import "server-only";
import { createHash } from "node:crypto";
import { env as cfEnv } from "cloudflare:workers";
import * as cfWorkers from "cloudflare:workers";
import type { Mate, TeamNote } from "@/lib/collab";
import { joinFlight, type Flight } from "@/lib/edgecache";

/** Coordination desk client. Every call goes through one Postgres function, oma_api, which checks
 * OMA_DB_SECRET server-side (see supabase/migrations/002_api_gate.sql). The Supabase key only
 * opens PostgREST; without the secret it can do nothing.
 * Without env vars the desk is "offline": catalogue and search work, live counts read as zero. */
const URL_ = process.env.SUPABASE_URL;
const KEY = process.env.SUPABASE_PUBLISHABLE_KEY ?? process.env.SUPABASE_SERVICE_ROLE_KEY;
const SECRET = process.env.OMA_DB_SECRET;

export const deskOnline = Boolean(URL_ && KEY && SECRET);

// Circuit breaker: after a timeout or a 5xx, this Worker instance stops calling the database for a while, so an
// overloaded database gets room to recover instead of a pile of waiting requests, and pages answer at once (cached or
// empty values). Two of them: a failed read (pages refresh with a 1 s budget, and have a last good value to fall back
// on) pauses reads for 2 min but not the agents' writes; a failed write pauses both, writes for 30 s.
// The state is also shared with every other instance of the data centre (a marker in its Cache API), so one failure
// pauses the whole data centre instead of costing each of its instances its own timed-out call.
// During a long outage the pauses grow (30 s, 1, 2, 4 min, then 5 min) and only one call per data centre probes the
// database when a pause ends; the others fail at once instead of each waiting for its own timeout (that waiting made
// 1 to 10% of requests take 8 s while the database was down).
let readsDownUntil = 0;
let writesDownUntil = 0;
let failStreak = 0;
export const deskDown = () => Date.now() < Math.max(readsDownUntil, writesDownUntil);

/** Thrown when the database cannot answer (breaker open, timeout, 5xx): API routes answer 503 with Retry-After. */
export class DeskUnavailable extends Error {
  constructor(cause?: unknown) {
    super(`desk_unavailable${cause instanceof Error ? `: ${cause.message}` : ""}`);
    this.name = "DeskUnavailable";
  }
}

/** An answer of the database itself (4xx: bad argument, unknown function): not a sign of overload, trips no breaker. */
class DeskRefused extends Error {}

const breakerReq = () => new Request(`${CACHE_ORIGIN}/__desk_down`);

async function coloBreaker(): Promise<void> {
  const cache = edgeCache();
  if (!cache) return;
  const hit = await cache.match(breakerReq()).catch(() => undefined);
  if (!hit) return;
  const b = (await hit.json().catch(() => null)) as { reads?: number; writes?: number; streak?: number } | null;
  if (b) {
    readsDownUntil = Math.max(readsDownUntil, Number(b.reads) || 0);
    writesDownUntil = Math.max(writesDownUntil, Number(b.writes) || 0);
    failStreak = Math.max(failStreak, Number(b.streak) || 0);
  }
}

async function tripColo(): Promise<void> {
  const cache = edgeCache();
  if (!cache) return;
  const until = Math.max(readsDownUntil, writesDownUntil);
  // kept a while after the pause ends, so the failure streak (and thus probe mode) survives until a call succeeds
  const s = Math.max(1, Math.ceil((until - Date.now()) / 1000)) + (failStreak ? 900 : 0);
  await cache
    .put(breakerReq(), new Response(JSON.stringify({ reads: readsDownUntil, writes: writesDownUntil, streak: failStreak }), { headers: { "Content-Type": "application/json", "Cache-Control": `public, max-age=${s}` } }))
    .catch(() => undefined);
}

async function rpc<T>(fn: string, args: Record<string, unknown>, timeoutMs = 4000, kind: "read" | "write" = "write"): Promise<T> {
  const open = () => {
    const now = Date.now();
    return now < writesDownUntil || (kind === "read" && now < readsDownUntil);
  };
  if (open()) throw new DeskUnavailable();
  await coloBreaker();
  if (open()) throw new DeskUnavailable();
  const probing = failStreak > 0;
  if (probing) {
    // after failures, this call is the data centre's single probe: everyone else fails fast until it returns
    const lock = Date.now() + timeoutMs + 500;
    readsDownUntil = Math.max(readsDownUntil, lock);
    writesDownUntil = Math.max(writesDownUntil, lock);
    await tripColo();
  }
  try {
    const value = await rpcOnce<T>(fn, args, timeoutMs);
    if (probing) {
      failStreak = 0; readsDownUntil = 0; writesDownUntil = 0;
      await edgeCache()?.delete(breakerReq()).catch(() => undefined);
    }
    return value;
  } catch (e) {
    if (!(e instanceof DeskRefused)) {
      failStreak = Math.min(failStreak + 1, 10);
      const pause = Math.min(30_000 * 2 ** (failStreak - 1), 300_000);
      readsDownUntil = Date.now() + Math.max(120_000, pause);
      writesDownUntil = Date.now() + pause;
      await tripColo();
    } else if (probing) {
      // the database answered (a 4xx is an answer): it is up
      failStreak = 0; readsDownUntil = 0; writesDownUntil = 0;
      await edgeCache()?.delete(breakerReq()).catch(() => undefined);
    }
    throw new DeskUnavailable(e);
  }
}

async function rpcOnce<T>(fn: string, args: Record<string, unknown>, timeoutMs: number): Promise<T> {
  // Never let a slow database hang the site: page reads give up after 1 s (and fall back to the last good value),
  // background refreshes after 3 s, writes after 8 s.
  // No `cache: "no-store"` here: a POST is never cached anyway, and vinext's fetch treats a no-store fetch made while a
  // page renders as a dynamic API. Its background re-render of a cached page (ISR) then threw "Page changed from static
  // to dynamic at runtime" whenever a desk read had to ask the database, and vinext kept serving the previous copy:
  // the home page's counters (and problem pages) froze for as long as the isolate lived.
  const res = await fetch(`${URL_}/rest/v1/rpc/oma_api`, {
    method: "POST",
    headers: { apikey: KEY!, "Content-Type": "application/json" },
    body: JSON.stringify({ p_secret: SECRET, p_fn: fn, p_args: args }),
    signal: AbortSignal.timeout(timeoutMs),
  });
  if (!res.ok) {
    const msg = `oma_api ${fn} ${res.status}: ${(await res.text()).slice(0, 200)}`;
    throw res.status >= 400 && res.status < 500 && res.status !== 408 && res.status !== 429 ? new DeskRefused(msg) : new Error(msg);
  }
  return (await res.json()) as T;
}

/**
 * Reads with a time-to-live are shared, so traffic does not turn into database calls: first this Worker instance's
 * memory, then Cloudflare's cache in this data centre (shared by every instance there, free), and only then
 * Supabase. Concurrent identical reads wait for one call. Writes (claims, beats, verdicts) are never cached.
 */
const MEM = new Map<string, { at: number; value: unknown }>();
const INFLIGHT = new Map<string, Flight>();
const CACHE_ORIGIN = (process.env.SITE_URL ?? process.env.NEXT_PUBLIC_SITE_URL ?? "https://lefttosolve.com").replace(/\/$/, "");
function edgeCache(): Cache | null {
  try {
    return (globalThis as unknown as { caches?: { default?: Cache } }).caches?.default ?? null;
  } catch {
    return null;
  }
}

// Reads shared by every page (no per-problem or per-person argument): also kept in Workers KV, one copy for the whole
// network, so Supabase answers them about once per time-to-live worldwide instead of once per data centre.
const GLOBAL_FNS = new Set(["stats", "live", "active_ids", "steps", "solved", "leaderboard", "leaderboard2", "calendar", "graveyard"]);
// The site-wide event lists (/live, /feed, the desk's pending submissions) are shared too; one problem's history and
// the feed's older pages (before=) stay per data centre, and so does a kind nobody writes (no KV key per typo).
const EVENT_KINDS = new Set(["claim", "release", "submit", "accepted", "rejected", "fault", "note", "reduced", "formalized", "shorter"]);
const isGlobal = (fn: string, args: Record<string, unknown>) =>
  (GLOBAL_FNS.has(fn) && !("parent" in args)) ||
  (fn === "events" && !("problem" in args) && !("before" in args) && (!("kind" in args) || EVENT_KINDS.has(String(args.kind))));
type KV = { get(k: string, o: { type: "json"; cacheTtl?: number }): Promise<unknown>; put(k: string, v: string, o?: { expirationTtl?: number }): Promise<void> };
function kv(): KV | null {
  try {
    return ((cfEnv as unknown as { DESK_KV?: KV }).DESK_KV) ?? null;
  } catch {
    return null;
  }
}

/** Problems an agent reported as already solved elsewhere ("SOLVED ELSEWHERE: <url>" notes, tools/oma.sh
 * solved-elsewhere). The desk stops handing them out at once; a review then moves each one to
 * data/settled_elsewhere/ (settled) or clears it (not settled). Kept in KV: { id: { url, at, by } }. */
const ELSEWHERE_KEY = "solved_elsewhere_reports";
export type ElsewhereReport = { url: string; at: string; by?: string };
let ELSEWHERE: { at: number; value: Record<string, ElsewhereReport> } | null = null;
export async function getElsewhereReports(): Promise<Record<string, ElsewhereReport>> {
  if (ELSEWHERE && Date.now() - ELSEWHERE.at < 60_000) return ELSEWHERE.value;
  const store = kv();
  let value: Record<string, ElsewhereReport> = {};
  try { value = ((await store?.get(ELSEWHERE_KEY, { type: "json", cacheTtl: 60 })) as Record<string, ElsewhereReport> | null) ?? {}; } catch { /* KV down: decide nothing */ }
  ELSEWHERE = { at: Date.now(), value };
  return value;
}
export async function reportElsewhere(problem: string, url: string, by?: string) {
  const store = kv();
  if (!store) return;
  const cur = ((await store.get(ELSEWHERE_KEY, { type: "json" }).catch(() => null)) as Record<string, ElsewhereReport> | null) ?? {};
  if (cur[problem]) return;
  cur[problem] = { url: url.slice(0, 400), at: new Date().toISOString(), by };
  await store.put(ELSEWHERE_KEY, JSON.stringify(cur));
  ELSEWHERE = { at: Date.now(), value: cur };
}

/** ctx.waitUntil of the current request (cloudflare:workers exports it), or null where the runtime has none. */
function waitUntilFn(): ((p: Promise<unknown>) => void) | null {
  try {
    const w = (cfWorkers as unknown as { waitUntil?: (p: Promise<unknown>) => void }).waitUntil;
    return typeof w === "function" ? w : null;
  } catch {
    return null;
  }
}

type Entry<T> = { at: number; value: T };
/** Keys this instance is refreshing in the background (the others keep serving the last value meanwhile). */
const REFRESHING = new Set<string>();
/** When the database computed the value a cached read returned last (ms): the ledger merge (lib/ledgercore.ts
 * mergeBoard) compares the leaderboard's age with the solved list's. */
const READ_AT = new Map<string, number>();
function seen<T>(key: string, e: Entry<T>): T {
  if (READ_AT.size > 2000) READ_AT.clear();
  READ_AT.set(key, e.at);
  return e.value;
}
const readAt = (fn: string, args: Record<string, unknown>) => READ_AT.get(`${fn}?${JSON.stringify(args)}`);

/** One read from the database, stored everywhere the next readers look: this instance, the data centre, KV. */
async function refresh<T>(fn: string, args: Record<string, unknown>, key: string, revalidate: number, timeoutMs: number, store: KV | null): Promise<T> {
  const value = await rpc<T>(fn, args, timeoutMs, "read");
  const at = Date.now();
  if (MEM.size > 2000) MEM.clear();
  MEM.set(key, { at, value });
  READ_AT.set(key, at);
  const body = JSON.stringify({ at, value });
  // One write per key per refresh; kept a day so it also serves as the last good value when the database fails.
  if (store) await store.put(`v1:${key}`, body, { expirationTtl: 86400 }).catch(() => undefined);
  const cache = edgeCache();
  if (cache) {
    await cache
      .put(new Request(`${CACHE_ORIGIN}/__desk_cache/${encodeURIComponent(key)}`), new Response(body, { headers: { "Content-Type": "application/json", "Cache-Control": `public, max-age=${revalidate}` } }))
      .catch(() => undefined);
    // A longer-lived copy, served while a refresh runs and when the database fails.
    await cache
      .put(new Request(`${CACHE_ORIGIN}/__desk_stale/${encodeURIComponent(key)}`), new Response(body, { headers: { "Content-Type": "application/json", "Cache-Control": "public, max-age=86400" } }))
      .catch(() => undefined);
  }
  return value;
}

async function api<T>(fn: string, args: Record<string, unknown> = {}, revalidate?: number): Promise<T> {
  if (!deskOnline) throw new Error("desk_offline");
  if (!revalidate) return rpc<T>(fn, args);
  const key = `${fn}?${JSON.stringify(args)}`;
  const ttl = revalidate * 1000;
  const m = MEM.get(key);
  if (m && Date.now() - m.at < ttl) return seen(key, m as Entry<T>);
  // A failed refresh serves the last good value instead of an empty page.
  // A read shared with a request that has since ended cannot settle here: run it again (lib/edgecache.ts, joinFlight).
  const running = joinFlight(INFLIGHT, key, () => api<T>(fn, args, revalidate));
  if (running) return running;
  const p = (async () => {
    const cache = edgeCache();
    const req = new Request(`${CACHE_ORIGIN}/__desk_cache/${encodeURIComponent(key)}`);
    if (cache) {
      const hit = await cache.match(req).catch(() => undefined);
      if (hit) {
        const got = (await hit.json().catch(() => null)) as Entry<T> | null;
        if (got && Date.now() - got.at < ttl) {
          MEM.set(key, got);
          return seen(key, got);
        }
      }
    }
    // Global copy (KV). Fresh: use it. A little stale: most callers still use it and only ~15% refresh it, so the
    // data centres that notice at the same moment do not all call the database.
    const store = isGlobal(fn, args) ? kv() : null;
    let kvStale: { at: number; value: T } | null = null;
    if (store) {
      const got = (await store.get(`v1:${key}`, { type: "json", cacheTtl: 30 }).catch(() => null)) as { at: number; value: T } | null;
      if (got) {
        const age = Date.now() - got.at;
        if (age < ttl || (age < 3 * ttl && Math.random() > 0.15)) {
          MEM.set(key, got);
          if (cache) {
            await cache
              .put(req, new Response(JSON.stringify(got), { headers: { "Content-Type": "application/json", "Cache-Control": `public, max-age=${Math.max(10, Math.round((ttl - Math.min(age, ttl)) / 1000) || 10)}` } }))
              .catch(() => undefined);
          }
          return seen(key, got);
        }
        kvStale = got;
      }
    }
    // The last value: this instance's, KV's, or the data centre's day-long copy.
    let staleRead = false;
    let stale: Entry<T> | null = (MEM.get(key) as Entry<T> | undefined) ?? kvStale;
    const lastValue = async () => {
      if (!stale && !staleRead && cache) {
        staleRead = true;
        stale = (await cache.match(new Request(`${CACHE_ORIGIN}/__desk_stale/${encodeURIComponent(key)}`)).then((r) => (r ? r.json() : null)).catch(() => null)) as Entry<T> | null;
      }
      return stale;
    };
    // Stale-while-revalidate: a value at most three time-to-lives old is served at once and refreshed after the
    // response (one refresh per key per instance), so a page never waits on the database when it has a recent value.
    const later = waitUntilFn();
    if (later) {
      const last = await lastValue();
      if (last && Date.now() - last.at < 3 * ttl) {
        if (!REFRESHING.has(key)) {
          REFRESHING.add(key);
          later(refresh<T>(fn, args, key, revalidate, 3000, store).catch((e) => console.error(e)).finally(() => REFRESHING.delete(key)));
        }
        return seen(key, last);
      }
    }
    try {
      return await refresh<T>(fn, args, key, revalidate, 1000, store);
    } catch (e) {
      const last = await lastValue();
      if (last) return seen(key, last);
      throw e;
    }
  })().finally(() => { if (INFLIGHT.get(key)?.p === p) INFLIGHT.delete(key); });
  INFLIGHT.set(key, { p, at: Date.now() });
  return p as Promise<T>;
}

export type Stats = {
  liveAgents: number;
  liveProblems: number;
  top: { problem_id: string; agents: number }[];
  /** Every problem solved here: id and polarity only (the full records, with authors and links, come from getSolved). */
  solved: { problem_id: string; polarity: string }[];
  solvedToday: number;
  claimsToday: number;
  contributors: number;
};

const EMPTY: Stats = { liveAgents: 0, liveProblems: 0, top: [], solved: [], solvedToday: 0, claimsToday: 0, contributors: 0 };

/** The counters of the home page, the board and the programs (one read, shared, so they always agree): 60 s, and the
 * global KV copy makes that about one database call a minute worldwide (the database caches it 20 s itself). */
async function statsDb(): Promise<Stats> {
  if (!deskOnline) return EMPTY;
  try {
    return await api<Stats>("stats", {}, 60);
  } catch (e) {
    console.error(e);
    return EMPTY;
  }
}

export async function getLiveMap(): Promise<Map<string, number>> {
  if (!deskOnline) return new Map();
  try {
    const rows = await api<{ problem_id: string; agents: number }[]>("live", {}, 45);
    return new Map(rows.map((r) => [r.problem_id, r.agents]));
  } catch (e) {
    console.error(e);
    return new Map();
  }
}

export type Event = { id: number; kind: string; problem_id: string; handle: string | null; detail: string | null; created_at: string };

export async function getEvents(limit = 60, problem?: string, kind?: string, before?: number): Promise<Event[]> {
  if (!deskOnline) return [];
  try {
    // One problem's history is read once with 60 entries and cut here, so its page (20) and its agent.txt (60) share
    // one cached read instead of two.
    if (problem && limit <= 60) {
      const all = await api<Event[]>("events", { limit: 60, problem, ...(kind ? { kind } : {}), ...(before ? { before } : {}) }, 180);
      return all.slice(0, limit);
    }
    return await api<Event[]>("events", { limit, ...(problem ? { problem } : {}), ...(kind ? { kind } : {}), ...(before ? { before } : {}) }, problem ? 180 : 60);
  } catch (e) {
    console.error(e);
    return [];
  }
}

export const claim = (problem: string, handle: string, agent: string, ipHash: string | null) =>
  api<{ lease?: string; error?: string }>("claim", { problem, handle, agent, ip_hash: ipHash });
/** Heartbeat. Also answers with the agent's role, its teammates on the problem and the notes posted after note id `since`. */
export const beat = (lease: string, since = 0) =>
  api<{ ok?: boolean; stop?: boolean; status?: string; error?: string; role?: string; team?: Mate[]; notes?: TeamNote[]; last_note?: number | null }>("beat2", { lease, since });
/** A note for the agents that take this problem next (approaches, partial lemmas, dead ends, references). */
export const addNote = (lease: string, note: string) => api<{ ok?: boolean; error?: string; problem?: string }>("note", { lease, note: note.slice(0, 4000) });
export const release = (lease: string, reason: string) => api<{ ok?: boolean; error?: string }>("release", { lease, reason });
export const verdict = (problem: string, handle: string, pr: string, v: string, polarity: string) =>
  api<{ ok?: boolean }>("verdict", { problem, handle, pr, verdict: v, polarity });

export function hashIp(ip: string | null) {
  if (!ip) return null;
  return createHash("sha256").update((process.env.OMA_IP_SALT ?? "oma") + ip).digest("hex").slice(0, 24);
}

export type Leader = { handle: string; solved: number; disproofs: number; claims: number; handed_back: number; last_seen: string | null };
export async function getLeaderboard(hours?: number): Promise<Leader[]> {
  if (!deskOnline) return [];
  try {
    return await api<Leader[]>("leaderboard", hours ? { hours } : {}, 120);
  } catch (e) {
    console.error(e);
    return [];
  }
}

export type Profile = {
  handle: string;
  solutions: { problem_id: string; polarity: string; pr_url: string; agent: string | null; model: string | null; points: number; created_at: string }[];
  contributed?: { problem_id: string; lead: string; created_at: string }[];
  points?: number;
  live: { problem_id: string; created_at: string; beat_at: string }[];
  events: { id: number; kind: string; problem_id: string; detail: string | null; created_at: string }[];
  claims: number;
  firstSeen: string | null;
};
async function profileDb(handle: string): Promise<Profile | null> {
  if (!deskOnline) return null;
  try {
    return await api<Profile>("profile", { handle }, 300);
  } catch (e) {
    console.error(e);
    return null;
  }
}

export type Graveyard = {
  recent: { id: number; problem_id: string; handle: string; reason: string; created_at: string }[];
  byProblem: { problem_id: string; total: number; seems_false: number; missing_lemma: number; too_hard: number; broken: number }[];
};
export async function getGraveyard(): Promise<Graveyard> {
  const empty = { recent: [], byProblem: [] };
  if (!deskOnline) return empty;
  try {
    return await api<Graveyard>("graveyard", { limit: 150 }, 300);
  } catch (e) {
    console.error(e);
    return empty;
  }
}

export const claim2 = (problem: string, handle: string, agent: string, ipHash: string | null, points: number) =>
  api<{ lease?: string; error?: string; role?: string; team?: Mate[]; notes?: TeamNote[]; last_note?: number | null }>("claim2", { problem, handle, agent, ip_hash: ipHash, points });
export const verdict2 = (a: { problem: string; handle: string; pr: string; verdict: string; polarity: string; agent: string | null; model: string | null; points: number }) =>
  api<{ ok?: boolean }>("verdict2", a);
export const registerReduction = (a: { id: string; problem: string; handle: string; pr: string; module: string; statements: string[]; points: number }) =>
  api<{ ok?: boolean; error?: string; steps?: number }>("register_reduction", a);

async function safe<T>(fn: string, args: Record<string, unknown>, fallback: T, revalidate = 20): Promise<T> {
  if (!deskOnline) return fallback;
  try {
    return await api<T>(fn, args, revalidate);
  } catch (e) {
    console.error(e);
    return fallback;
  }
}

export type Leader2 = Leader & { points: number; agent: string | null; model: string | null };
const leaderboard2Db = (minutes?: number) => safe<Leader2[]>("leaderboard2", minutes ? { minutes } : {}, [], 600);

export type Solved = { problem_id: string; handle: string; agent: string | null; model: string | null; polarity: string; pr_url: string; points: number; contributors: string[] | null; created_at: string };
const SOLVED_ARGS = { limit: 2000 };
const solvedDb = () => safe<Solved[]>("solved", SOLVED_ARGS, [], 600);

export type Day = { day: string; claims: number; released: number; submitted: number; solved: number; reduced: number; people: number };
/** Days, newest first. Today alone (the home page's "Today so far") is read every 2 minutes, the long lists every 10. */
export const getCalendar = (days = 90) => safe<Day[]>("calendar", { days }, [], days <= 1 ? 120 : 600);

export type Step = { id: string; reduction: string; parent: string; k: number; statement: string; module: string; points: number; created_at: string; solved: boolean; reduction_pr: string; reduction_by: string };
/** Steps of accepted reductions. Pages: 60 s cache. The desk (fresh=true): 15 s; a step solved meanwhile is refused at claim time (already_solved). */
export async function getSteps(parent?: string, fresh = false): Promise<Step[]> {
  const ttl = fresh ? 60 : 600;
  if (parent) {
    // The shared list of every step (one KV copy worldwide) says whether anything hangs under this id: most problems
    // have no steps, and their pages then skip the per-problem read. An empty or failed list decides nothing.
    const all = await safe<Step[]>("steps", {}, [], ttl);
    if (all.length > 0 && !all.some((s) => s.id === parent || s.parent === parent)) return [];
  }
  return safe<Step[]>("steps", parent ? { parent } : {}, [], ttl);
}

/** The same read with no cache and no fallback: throws DeskUnavailable when the database cannot answer. For the
 * verdict route, which must never mistake a failed read for "this step does not exist" (that refused merged work). */
export const getStepsStrict = async (parent: string) => {
  if (!deskOnline) throw new DeskUnavailable();
  return rpc<Step[]>("steps", { parent }, 4000, "read");
};

export const logEvent = (kind: string, problem: string, handle: string, detail: string) =>
  api<{ ok?: boolean; error?: string }>("log", { kind, problem, handle, detail });

/** role "help": a teammate whose DONE lemmas (notes) the merged proof uses (supabase/pending-review/022_swarm.sql). */
export type Contribution = { handle: string; share: number; roles: { role: "proof" | "step" | "reduction" | "help"; item: string; pr: string; agent?: string | null; model?: string | null; notes?: number[] }[] };
/** Shares of everyone who contributed to the accepted solution of a problem (sum to 1). Empty if unsolved. */
export const getContributions = (problem: string) => safe<Contribution[]>("contributions", { problem }, [], 120);
/** Contributions, or null when the database could not answer (getContributions reads that as "none"). */
export async function getContributionsOrNull(problem: string): Promise<Contribution[] | null> {
  if (!deskOnline) return null;
  try {
    return await api<Contribution[]>("contributions", { problem }, 120);
  } catch (e) {
    console.error(e);
    return null;
  }
}


/** Ids of every problem or step that has any history (taken, sent, proved...): a small list, refreshed once a minute.
 * Pages of problems not in it skip the per-problem history query entirely. */
async function activeIdsDb(): Promise<Set<string>> {
  if (!deskOnline) return new Set();
  try {
    return new Set(await api<string[]>("active_ids", {}, 600));
  } catch (e) {
    console.error(e);
    return new Set();
  }
}

/** The history of one problem, asked from the database only if it has one (see getActiveIds). */
export async function getProblemEvents(limit: number, problem: string): Promise<Event[]> {
  const active = await getActiveIds();
  return active.has(problem) ? getEvents(limit, problem) : [];
}

// Credits: what the database recorded, completed with the credit ledger (lib/ledger.ts), the record of every pull
// request merged on GitHub. A lost credit call or a database outage no longer drops anyone's points: the leaderboard,
// the solved list, profiles and the stats answer from the ledger where the database has nothing. The database's row
// wins wherever it has the pull request. The ledger module (and the catalogue it needs) is loaded on first use only, so
// the desk's hot routes that never show credits (heartbeats) do not load it.
type LedgerMod = typeof import("@/lib/ledger");
type LedgerBase = { L: LedgerMod; world: import("@/lib/ledgercore").World; solved: Solved[]; solvedAt: number | undefined; extra: import("@/lib/ledgercore").Credit[] };
let BASE: { at: number; value: LedgerBase } | null = null;
let BASE_RUN: Promise<LedgerBase | null> | null = null;
const MERGE_TTL = 30_000;

async function ledgerBase(): Promise<LedgerBase | null> {
  if (BASE && Date.now() - BASE.at < MERGE_TTL) return BASE.value;
  if (BASE_RUN) return BASE_RUN;
  BASE_RUN = (async () => {
    try {
      const L = await import("@/lib/ledger");
      const [world, solved] = await Promise.all([L.getWorld(() => getSteps()), solvedDb()]);
      const value: LedgerBase = { L, world, solved, solvedAt: readAt("solved", SOLVED_ARGS), extra: L.extraCredits(world, solved) };
      BASE = { at: Date.now(), value };
      return value;
    } catch (e) {
      console.error("ledger", e);
      return BASE?.value ?? null;
    }
  })().finally(() => (BASE_RUN = null));
  return BASE_RUN;
}

const MERGED = new Map<string, { at: number; value: unknown }>();
/** A database read merged with the ledger, computed at most every 30 s per isolate; the database's answer as it is
 * when the ledger cannot be read. */
async function withLedger<T>(key: string, raw: () => Promise<T>, merge: (v: T, b: LedgerBase) => T): Promise<T> {
  const m = MERGED.get(key);
  if (m && Date.now() - m.at < MERGE_TTL) return m.value as T;
  const [v, b] = await Promise.all([raw(), ledgerBase()]);
  if (!b) return v;
  try {
    const value = merge(v, b);
    if (MERGED.size > 1000) MERGED.clear();
    MERGED.set(key, { at: Date.now(), value });
    return value;
  } catch (e) {
    console.error("ledger merge", key, e);
    return v;
  }
}

export const getStats = () => withLedger("stats", statsDb, (s, b) => b.L.mergeStats(s, b.extra, b.world));
/** Every solved problem and step with its solver of record (oma_solved_list), and the ledger's the database lacks. */
export const getSolved = () => withLedger("solved", solvedDb, (_v, b) => b.L.mergeSolved(b.solved, b.extra));
export const getLeaderboard2 = (minutes?: number) =>
  withLedger(`lb2:${minutes ?? ""}`, () => leaderboard2Db(minutes), (v, b) =>
    b.L.mergeBoard(v, readAt("leaderboard2", minutes ? { minutes } : {}), b.solved, b.solvedAt, b.extra, b.world, minutes));
export const getProfile = (handle: string) =>
  withLedger(`profile:${handle}`, () => profileDb(handle), (p, b) => b.L.mergeProfile(p, handle, b.world, b.solved, b.extra));
export const getActiveIds = () =>
  withLedger("active_ids", activeIdsDb, (s, b) => {
    const out = new Set(s);
    for (const id of b.world.ids) out.add(id);
    return out;
  });
/** The solution of record of one problem or step (database or ledger), or null. */
export async function getSolution(id: string): Promise<Solved | null> {
  return (await getSolved()).find((s) => s.problem_id === id) ?? null;
}

/** The desk's own calls, for lib/team.ts (the team board of supabase/pending-review/022_swarm.sql): the cached read or
 * plain call (api), and one uncached call with its own timeout (rpc). */
export { api as deskCall, rpc as deskRpc };
