import "server-only";
import { env as cfEnv } from "cloudflare:workers";
import { getProblem } from "@/lib/catalog";
import { REPO } from "@/lib/site";
import { computeWorld, LEDGER_SHARD, sameEntry, upsertEntry, type LedgerEntry, type World } from "@/lib/ledgercore";

export * from "@/lib/ledgercore";

/**
 * The credit ledger in Workers KV (DESK_KV): one entry per merged pull request (lib/ledgercore.ts). Two families of
 * keys, sharded by pull request number (1000 per key, value {v, list}), each with a meta listing its shards and their
 * version, so a reader fetches again only the shards that changed:
 *  - live: "ledger:v1:s<k>" and "ledger:v1:meta", written only by this site (POST /api/ledger, from the merger);
 *  - backfill: "ledger:v1:b<k>" and "ledger:v1:bmeta", written only by a maintainer's import of
 *    tools/ledger_backfill.mjs (Cloudflare API), never by the site: the two never overwrite each other's writes
 *    (KV has no transactions, and an import racing the merger's posts on the same key lost entries).
 * The reader takes the union by pull request (upsertEntry: the earliest merge time seen).
 */
export const LEDGER_META = "ledger:v1:meta";
export const ledgerShardKey = (k: number) => `ledger:v1:s${k}`;
export const LEDGER_BACKFILL_META = "ledger:v1:bmeta";
const backfillShardKey = (k: number) => `ledger:v1:b${k}`;
export type LedgerMeta = { v: 1; shards: Record<string, { n: number; v: string }>; count: number; at: string };
type Shard = { v: string; list: LedgerEntry[] };
type KV = { get(k: string, o?: { type: "json"; cacheTtl?: number }): Promise<unknown>; put(k: string, v: string): Promise<void> };

function kv(): KV | null {
  try {
    return ((cfEnv as unknown as { DESK_KV?: KV }).DESK_KV) ?? null;
  } catch {
    return null;
  }
}

const SHARDS = new Map<string, Shard>();
/** Every shard up to the highest one listed: pull request numbers are dense, so shards 0..max all exist. */
const shardRange = (meta: LedgerMeta | null) => {
  const ks = Object.keys(meta?.shards ?? {}).map(Number).filter(Number.isInteger);
  return ks.length ? Array.from({ length: Math.min(Math.max(...ks), 9999) + 1 }, (_, i) => i) : [];
};
type Ledger = { at: number; list: LedgerEntry[]; version: string; meta: LedgerMeta | null };
let LEDGER: Ledger | null = null;
let READING: Promise<Ledger> | null = null;
const TTL = 60_000;

/** One family's shards, each fetched again only when its meta lists a new version (or does not list it). */
async function readFamily(store: KV, metaKey: string, key: (k: number) => string): Promise<{ list: LedgerEntry[]; version: string; meta: LedgerMeta | null }> {
  const meta = (await store.get(metaKey, { type: "json", cacheTtl: 60 })) as LedgerMeta | null;
  const keys = shardRange(meta);
  await Promise.all(keys.map(async (k) => {
    // A shard the meta does not list (two writes raced on it): read again every time until a write lists it.
    const want = meta?.shards?.[k]?.v;
    if (want && SHARDS.get(key(k))?.v === want) return;
    const got = (await store.get(key(k), { type: "json", cacheTtl: 60 })) as Shard | null;
    // A copy older than the meta (another data centre's cache): kept, and asked again at the next read.
    if (got && Array.isArray(got.list)) SHARDS.set(key(k), got);
  }));
  return {
    list: keys.flatMap((k) => SHARDS.get(key(k))?.list ?? []),
    version: keys.map((k) => `${k}:${SHARDS.get(key(k))?.v ?? "-"}`).join(","),
    meta,
  };
}

/** Every entry, backfill and live merged by pull request (cached a minute per isolate; a failed read keeps the last). */
export function readLedger(): Promise<Ledger> {
  if (LEDGER && Date.now() - LEDGER.at < TTL) return Promise.resolve(LEDGER);
  if (READING) return READING;
  const run = (async (): Promise<Ledger> => {
    await Promise.resolve(); // READING is set before this body runs on
    try {
      const store = kv();
      if (!store) return (LEDGER = { at: Date.now(), list: [], version: "none", meta: null });
      const [bf, live] = await Promise.all([readFamily(store, LEDGER_BACKFILL_META, backfillShardKey), readFamily(store, LEDGER_META, ledgerShardKey)]);
      const byPr = new Map<number, LedgerEntry>();
      for (const e of bf.list) byPr.set(e.pr, e);
      for (const e of live.list) byPr.set(e.pr, upsertEntry(byPr.get(e.pr), e));
      return (LEDGER = { at: Date.now(), list: [...byPr.values()], version: `b${bf.version}|s${live.version}`, meta: live.meta });
    } catch (e) {
      console.error("ledger read", e);
      if (LEDGER) return (LEDGER = { ...LEDGER, at: Date.now() - TTL / 2 });
      return { at: 0, list: [], version: "none", meta: null };
    } finally {
      READING = null;
    }
  })();
  READING = run;
  return run;
}

let WORLD: { key: string; at: number; world: World } | null = null;

/** Credits computed from the ledger (lib/ledgercore.ts computeWorld), recomputed when the ledger changes. The
 * database's steps (a cached shared read) give the points of the steps it registered. */
export async function getWorld(dbSteps: () => Promise<{ id: string; points: number; reduction: string }[]>): Promise<World> {
  const led = await readLedger();
  if (WORLD && WORLD.key === led.version && Date.now() - WORLD.at < 10 * TTL) return WORLD.world;
  const steps = new Map((await dbSteps().catch(() => [])).map((s) => [s.id, { points: s.points, reduction: s.reduction }]));
  const world = computeWorld(led.list, getProblem, steps, REPO);
  WORLD = { key: led.version, at: Date.now(), world };
  return world;
}

let WRITING: Promise<unknown> = Promise.resolve();

/** Upserts entries by pull request, one write per changed shard and one for the meta. Writes are serialised in this
 * isolate; the merger posts from one place every few minutes and posts its latest entries again, which repairs a
 * write lost to KV's eventual consistency. */
export function upsertLedger(entries: LedgerEntry[]): Promise<{ changed: number; total: number }> {
  const run = WRITING.then(() => write(entries));
  WRITING = run.catch(() => undefined);
  return run;
}

async function write(entries: LedgerEntry[]): Promise<{ changed: number; total: number }> {
  const store = kv();
  if (!store) throw new Error("kv_unavailable");
  const meta = ((await store.get(LEDGER_META, { type: "json" })) as LedgerMeta | null) ?? { v: 1, shards: {}, count: 0, at: "" };
  const groups = new Map<number, LedgerEntry[]>();
  for (const e of entries) {
    const k = Math.floor(e.pr / LEDGER_SHARD);
    groups.set(k, [...(groups.get(k) ?? []), e]);
  }
  let changed = 0;
  for (const [k, group] of groups) {
    const cur = (await store.get(ledgerShardKey(k), { type: "json" })) as Shard | null;
    const byPr = new Map((cur?.list ?? []).map((e) => [e.pr, e]));
    let n = 0;
    for (const e of group) {
      const old = byPr.get(e.pr);
      const next = upsertEntry(old, e);
      if (!old || !sameEntry(old, next)) { byPr.set(e.pr, next); n++; }
    }
    if (!n) continue;
    const v = `${Date.now().toString(36)}${Math.random().toString(36).slice(2, 6)}`;
    const list = [...byPr.values()].sort((a, b) => a.pr - b.pr);
    await store.put(ledgerShardKey(k), JSON.stringify({ v, list }));
    meta.shards[String(k)] = { n: list.length, v };
    SHARDS.set(ledgerShardKey(k), { v, list });
    changed += n;
  }
  if (changed) {
    // Repair a meta that lost a shard to a concurrent write: list every shard below the highest one again.
    for (const k of shardRange(meta)) {
      if (meta.shards[String(k)]) continue;
      const got = (await store.get(ledgerShardKey(k), { type: "json" })) as Shard | null;
      if (got && Array.isArray(got.list)) meta.shards[String(k)] = { n: got.list.length, v: got.v };
    }
    meta.count = Object.values(meta.shards).reduce((a, s) => a + s.n, 0);
    meta.at = new Date().toISOString();
    await store.put(LEDGER_META, JSON.stringify(meta));
    LEDGER = null;
  }
  return { changed, total: meta.count };
}
