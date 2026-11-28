/**
 * Caches a computed JSON value for `ttl` seconds: in this isolate's memory, then in the data centre's Cache API
 * (shared by every isolate there; not billed, unlike Workers Cache). Identical concurrent computations run once.
 * For public, read-only values only.
 */
const MEM = new Map<string, { at: number; value: unknown }>();
const INFLIGHT = new Map<string, Flight>();

/**
 * Identical concurrent computations are shared between requests, but on Workers a promise belongs to the request that
 * created it: once that request has ended (answered, or cancelled because its visitor left), another request awaiting
 * it is rejected with "This promise was created by a request that has since ended, so it can never settle", and the
 * entry was never removed (its finally never ran), so every later request of that isolate failed the same way: 503 on
 * /api/problems, empty live data on pages. A joiner whose computation died that way runs its own; an entry older
 * than FLIGHT_MAX_MS is not joined at all.
 */
export type Flight = { p: Promise<unknown>; at: number };
const FLIGHT_MAX_MS = 15_000;
export const crossRequest = (e: unknown) => e instanceof Error && /request that has since ended|different request context/i.test(e.message);
export function joinFlight<T>(flights: Map<string, Flight>, key: string, again: () => Promise<T>): Promise<T> | null {
  const f = flights.get(key);
  if (!f) return null;
  if (Date.now() - f.at > FLIGHT_MAX_MS) {
    flights.delete(key);
    return null;
  }
  return (f.p as Promise<T>).catch((e) => {
    if (!crossRequest(e)) throw e;
    if (flights.get(key) === f) flights.delete(key);
    return again();
  });
}
const ORIGIN = (process.env.SITE_URL ?? process.env.NEXT_PUBLIC_SITE_URL ?? "https://lefttosolve.com").replace(/\/$/, "");

function edgeCache(): Cache | null {
  try {
    return (globalThis as unknown as { caches?: { default?: Cache } }).caches?.default ?? null;
  } catch {
    return null;
  }
}

export async function cachedJSON<T>(key: string, ttl: number, compute: () => Promise<T>): Promise<T> {
  const m = MEM.get(key);
  if (m && Date.now() - m.at < ttl * 1000) return m.value as T;
  const running = joinFlight(INFLIGHT, key, () => cachedJSON(key, ttl, compute));
  if (running) return running;
  const p = (async () => {
    const cache = edgeCache();
    const req = new Request(`${ORIGIN}/__json_cache/${encodeURIComponent(key)}`);
    if (cache) {
      const hit = await cache.match(req).catch(() => undefined);
      if (hit) {
        const got = (await hit.json().catch(() => null)) as { at: number; value: T } | null;
        if (got && Date.now() - got.at < ttl * 1000) {
          MEM.set(key, got);
          return got.value;
        }
      }
    }
    const value = await compute();
    const at = Date.now();
    if (MEM.size > 500) MEM.clear();
    MEM.set(key, { at, value });
    if (cache) {
      await cache
        .put(req, new Response(JSON.stringify({ at, value }), { headers: { "Content-Type": "application/json", "Cache-Control": `public, max-age=${ttl}` } }))
        .catch(() => undefined);
    }
    return value;
  })().finally(() => { if (INFLIGHT.get(key)?.p === p) INFLIGHT.delete(key); });
  INFLIGHT.set(key, { p, at: Date.now() });
  return p as Promise<T>;
}
