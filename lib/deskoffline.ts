import "server-only";
import { env as cfEnv } from "cloudflare:workers";
import * as cfWorkers from "cloudflare:workers";
import { DeskUnavailable, deskDown } from "@/lib/db";

/**
 * Degraded desk. When the coordination database cannot answer (lib/db.ts throws DeskUnavailable: timeout, 5xx, breaker
 * open), the desk keeps handing out problems, chosen the usual way from cached data (solved list, pending proofs,
 * filters, live event), with an offline lease the database never saw: "offline-" and 32 hex digits. A proof never
 * needs a lease (the merger does not check it), so agents keep working and submitting. Teams and notes wait for the
 * database; nothing pretends to be stored: beats, notes and releases say degraded: true and stored: false.
 *
 * To spread agents without the database, recent offline handouts are counted per problem and the least handed out
 * candidates go first: in this data centre (Cache API, updated on every handout, free and unmetered) and worldwide (one
 * Workers KV key holding each data centre's counts, written at most once a minute per data centre that hands problems
 * out, so KV sees a few writes a minute however many agents ask). Each data centre writes its whole picture, never an
 * increment, so a write lost to a concurrent one is repaired by that data centre's next write.
 */

export const OFFLINE_LEASE = /^offline-[0-9a-f]{32}$/;
export const offlineLease = () => `offline-${crypto.randomUUID().replace(/-/g, "")}`;

/** True when an error means the database is down (timeout, 5xx, breaker open). A 4xx is the database answering. */
export function dbDown(e: unknown): boolean {
  if (!(e instanceof DeskUnavailable)) return false;
  return deskDown() || !/ 4\d\d: /.test(e.message);
}

const NOTES_HINT = "Teammates and team notes are unavailable until it is back: put what you learned in your pull request body.";

/** Added to a /api/desk/next answer that carries an offline lease. */
export const DEGRADED_NEXT = {
  degraded: true,
  hint: "The coordination database is down: this lease is offline (recorded nowhere) and the problem was chosen from " +
    `cached data. Work and submit normally: a proof never needs a lease. ${NOTES_HINT}`,
};

/** A heartbeat that could not reach the database (or has nothing to refresh): never a stop. */
export function degradedBeat(offline: boolean) {
  return {
    ok: true,
    degraded: true,
    stop: false,
    refreshed: false,
    team: [],
    notes: [],
    hint: (offline ? "Offline lease: nothing to refresh." : "The database is down: your lease could not be refreshed.") +
      " Keep working and submit normally: a proof never needs a lease.",
  };
}

/** A note, a release or a board write that was not stored: 200 for an offline lease, 202 for a real one while the database is down. */
export function notStored(offline: boolean, what: "note" | "release" | "board") {
  const hint = (offline ? "Offline lease: nothing was stored." : "The database is down: nothing was stored.") +
    (what === "release" && !offline ? " Your lease ends by itself once its heartbeats stop." : "") +
    (what === "board" ? " Keep the lemma in your files and send it to the board once the desk is back, or put it in your pull request body." : " Put any note in your pull request body instead.");
  return offline ? { ok: true, degraded: true, stored: false, hint } : { accepted: true, stored: false, degraded: true, hint };
}

// --- recent offline handouts per problem -------------------------------------------------------------------------

/** A handout counts as recent for 90 minutes, about one working session. */
const WINDOW = 90 * 60_000;
const FLUSH_EVERY = 60_000;
const MAX_IDS = 3000;
const KV_KEY = "desk-offline:v1";
const ORIGIN = (process.env.SITE_URL ?? process.env.NEXT_PUBLIC_SITE_URL ?? "https://lefttosolve.com").replace(/\/$/, "");
const COLO_URL = `${ORIGIN}/__desk_offline/v1`;

/** Problem id -> [handouts, last handout in ms]. */
type Counts = Record<string, [number, number]>;
/** This data centre: a random writer id (its slot in KV), when it last wrote KV, its counts. */
type Colo = { writer: string; flushed: number; counts: Counts };
/** Worldwide (KV): writer id -> that data centre's counts and when it wrote them. */
type World = Record<string, { at: number; counts: Counts }>;
type KV = { get(k: string, o: { type: "json"; cacheTtl?: number }): Promise<unknown>; put(k: string, v: string, o?: { expirationTtl?: number }): Promise<void> };

function kv(): KV | null {
  try {
    return (cfEnv as unknown as { DESK_KV?: KV }).DESK_KV ?? null;
  } catch {
    return null;
  }
}
function edgeCache(): Cache | null {
  try {
    return (globalThis as unknown as { caches?: { default?: Cache } }).caches?.default ?? null;
  } catch {
    return null;
  }
}
function waitUntilFn(): ((p: Promise<unknown>) => void) | null {
  try {
    const w = (cfWorkers as unknown as { waitUntil?: (p: Promise<unknown>) => void }).waitUntil;
    return typeof w === "function" ? w : null;
  } catch {
    return null;
  }
}

/** Keeps the recent entries only (the most recent MAX_IDS); ignores anything malformed. */
function prune(counts: unknown, now: number): Counts {
  const rows = Object.entries(counts && typeof counts === "object" ? (counts as Record<string, unknown>) : {})
    .filter((e): e is [string, [number, number]] => Array.isArray(e[1]) && Number.isFinite(e[1][0]) && Number.isFinite(e[1][1]) && now - e[1][1] < WINDOW);
  if (rows.length > MAX_IDS) rows.sort((a, b) => b[1][1] - a[1][1]).length = MAX_IDS;
  return Object.fromEntries(rows);
}

// Fallbacks for runtimes without the Cache API (local development), and the last KV read of this instance.
let memColo: Colo | null = null;
let memWorld: { at: number; world: World } | null = null;

async function readColo(now: number): Promise<Colo> {
  const cache = edgeCache();
  if (cache) {
    const hit = await cache.match(new Request(COLO_URL)).catch(() => undefined);
    const got = hit ? ((await hit.json().catch(() => null)) as Colo | null) : null;
    if (got && typeof got.writer === "string") return (memColo = { writer: got.writer, flushed: Number(got.flushed) || 0, counts: prune(got.counts, now) });
  }
  return memColo ?? (memColo = { writer: crypto.randomUUID().slice(0, 8), flushed: 0, counts: {} });
}

async function writeColo(colo: Colo): Promise<void> {
  memColo = colo;
  await edgeCache()
    ?.put(new Request(COLO_URL), new Response(JSON.stringify(colo), { headers: { "Content-Type": "application/json", "Cache-Control": `public, max-age=${WINDOW / 1000}` } }))
    .catch(() => undefined);
}

async function readWorld(now: number, maxAge = 20_000): Promise<World> {
  if (memWorld && now - memWorld.at < maxAge) return memWorld.world;
  const store = kv();
  const got = store ? await store.get(KV_KEY, { type: "json", cacheTtl: 30 }).catch(() => null) : null;
  const world: World = {};
  for (const [w, sub] of Object.entries(got && typeof got === "object" ? (got as Record<string, { at?: unknown; counts?: unknown }>) : {})) {
    const at = Number(sub?.at) || 0;
    if (now - at < WINDOW) world[w] = { at, counts: prune(sub?.counts, now) };
  }
  memWorld = { at: now, world };
  return world;
}

/**
 * The desk's crowding scores while degraded: the live map (the last value read before the outage) plus the recent
 * offline handouts of every data centre. Falls back to the live map alone if the counts cannot be read.
 */
export async function offlineScores(live: Map<string, number>): Promise<Map<string, number>> {
  try {
    const now = Date.now();
    const [colo, world] = await Promise.all([readColo(now), readWorld(now)]);
    const scores = new Map(live);
    const add = (counts: Counts) => { for (const [id, [n]] of Object.entries(counts)) scores.set(id, (scores.get(id) ?? 0) + n); };
    // this data centre's own counts come from its Cache API entry, fresher than its slot in KV
    for (const [w, sub] of Object.entries(world)) if (w !== colo.writer) add(sub.counts);
    add(colo.counts);
    return scores;
  } catch (e) {
    console.error("desk offline scores", e);
    return live;
  }
}

async function record(id: string): Promise<void> {
  const now = Date.now();
  const colo = await readColo(now);
  const prev = colo.counts[id];
  colo.counts[id] = [(prev ? prev[0] : 0) + 1, now];
  colo.counts = prune(colo.counts, now);
  const store = kv();
  const flush = store !== null && now - colo.flushed >= FLUSH_EVERY;
  // claimed before the KV write, so the other instances of this data centre skip theirs
  if (flush) colo.flushed = now;
  await writeColo(colo);
  if (!flush) return;
  const world = { ...(await readWorld(now, 0)) };
  world[colo.writer] = { at: now, counts: colo.counts };
  await store.put(KV_KEY, JSON.stringify(world), { expirationTtl: WINDOW / 1000 });
  memWorld = { at: now, world };
}

/** Counts one offline handout of `id`, after the response when the runtime allows it. Never throws. */
export async function countHandout(id: string): Promise<void> {
  const p = record(id).catch((e) => console.error("desk offline count", e));
  const later = waitUntilFn();
  if (later) later(p);
  else await p;
}
