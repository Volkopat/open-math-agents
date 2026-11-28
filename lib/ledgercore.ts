/**
 * The credit ledger, pure part (no I/O; lib/ledger.ts reads and writes it in Workers KV).
 *
 * GitHub is the record of who solved what: every pull request merged into main that adds one file under proofs/,
 * reductions/ or statements/ (or makes a proof shorter) is one ledger entry, appended by the merger at merge time and
 * backfilled from the history of main (tools/ledger_backfill.mjs). The database (Supabase) keeps the same credits and
 * more (claims, heartbeats), but a credit call can be lost, and the database can be down for hours. Credits are
 * computed here from the ledger exactly as the verdict route (app/api/verdict/route.ts) and the database
 * (supabase/migrations: oma_verdict2, oma_register_reduction, oma_leaderboard2_raw) compute them, then merged with
 * the database's answers: the database's row wins when it has the pull request, the ledger fills in what it lacks.
 */
import type { Kind } from "@/lib/catalog";
import type { Event, Leader2, Profile, Solved, Stats } from "@/lib/db";
import { pointsFor } from "@/lib/points";
import { REDUCTION_FILE_RE, STEP_RE } from "@/lib/steps";

export type LedgerKind = "proof" | "reduction" | "statement" | "shorter";
export type LedgerEntry = {
  pr: number;
  path: string;
  kind: LedgerKind;
  /** The file's name without .lean: problem or step id, reduction id (<target>.R<n>) or statement id. */
  id: string;
  /** Author of the pull request: the owner of the agent, credited as the solver. */
  handle: string;
  agent: string | null;
  model: string | null;
  merged_at: string;
  polarity: "proof" | "disproof";
  /** Number of hypotheses of a reduction (reductionHypotheses), null otherwise or when unknown. */
  hyps: number | null;
};

export const LEDGER_SHARD = 1000;
const PATH_RE = /^(proofs|reductions|statements)\/([A-Za-z0-9_.'\-]+)\.lean$/;
const HANDLE_RE = /^[A-Za-z0-9](?:[A-Za-z0-9-]{0,38})(?:\[bot\])?$/;
const EARLIEST = Date.parse("2026-01-01T00:00:00Z");
/** As creditLine in the verdict route: free text shown as credit, without markup. */
const clean = (v: unknown) => (typeof v === "string" ? v.replace(/[<>`*_\[\]]/g, "").trim().slice(0, 80) || null : null);

/** A ledger entry from untrusted JSON, checked and normalised (kind and id follow from the path); null if invalid. */
export function normalizeEntry(x: unknown): LedgerEntry | null {
  if (!x || typeof x !== "object") return null;
  const e = x as Record<string, unknown>;
  const pr = Number(e.pr);
  if (!Number.isInteger(pr) || pr <= 0 || pr > 99_999_999) return null;
  const path = typeof e.path === "string" && e.path.length <= 400 ? e.path : "";
  const m = path.match(PATH_RE);
  if (!m) return null;
  let kind: LedgerKind;
  if (m[1] === "reductions") {
    if (!REDUCTION_FILE_RE.test(path)) return null;
    kind = "reduction";
  } else kind = m[1] === "statements" ? "statement" : e.kind === "shorter" ? "shorter" : "proof";
  const handle = typeof e.handle === "string" ? e.handle : "";
  if (!HANDLE_RE.test(handle)) return null;
  const t = Date.parse(String(e.merged_at ?? ""));
  if (!Number.isFinite(t) || t < EARLIEST || t > Date.now() + 3600_000) return null;
  const h = Number(e.hyps);
  return {
    pr, path, kind, id: m[2], handle, agent: clean(e.agent), model: clean(e.model), merged_at: new Date(t).toISOString(),
    polarity: (kind === "proof" || kind === "shorter") && e.polarity === "disproof" ? "disproof" : "proof",
    hyps: kind === "reduction" && e.hyps !== null && e.hyps !== undefined && Number.isInteger(h) && h >= 0 && h <= 99 ? h : null,
  };
}

export const sameEntry = (a: LedgerEntry, b: LedgerEntry) =>
  a.pr === b.pr && a.path === b.path && a.kind === b.kind && a.handle === b.handle && a.agent === b.agent && a.model === b.model &&
  a.merged_at === b.merged_at && a.polarity === b.polarity && a.hyps === b.hyps;

/** Upsert by pull request: the newer entry replaces the older one, but the earliest merge time seen is kept (the
 * backfill has GitHub's merged_at; the merger's own clock reads it a few seconds later). */
export function upsertEntry(old: LedgerEntry | undefined, e: LedgerEntry): LedgerEntry {
  if (!old) return e;
  return { ...e, merged_at: old.merged_at < e.merged_at ? old.merged_at : e.merged_at };
}

/** A solution as the database lists it (oma_solved_list), plus whether it is the first solve of its problem. */
export type Credit = Solved & { first: boolean };
type LStep = { id: string; reduction: string; parent: string; k: number; points: number };
type LReduction = { id: string; target: string; handle: string; pr_url: string; steps: string[] };
/** An event for a profile; pr: the credit it stands for (accepted), to match the solutions it belongs to. */
type LEvent = Event & { handle: string; pr: string };

export type World = {
  /** Every credited solution, in merge order: first solves (points), later proofs (0 points), closures by reduction. */
  credits: Credit[];
  /** Problem or step id -> its first solve in the ledger (the solver of record). */
  firsts: Map<string, Credit>;
  /** Lower-cased handle -> that person's credits. */
  byHandle: Map<string, Credit[]>;
  /** Lower-cased handle -> events (accepted, reduced, formalized, shorter) for a profile the database cannot give. */
  events: Map<string, LEvent[]>;
  /** Every id with merged work: problems and steps proved, reduction targets, problems stated. */
  ids: Set<string>;
  handles: number;
  entries: number;
};

export type Lookup = (id: string) => { difficulty: number; kind: Kind } | undefined;

/**
 * Credits from the ledger alone, in merge order, as the verdict route and the database give them:
 *  - proofs/<id>.lean: a catalogue problem (a merged statement makes an unformalized problem provable) or a known step;
 *    pointsFor(difficulty, kind), or the step's points; the earliest merge is the first solve, a later proof gets no
 *    points; a closed step may close its parent (oma_verdict2): credited to the reduction's author, points
 *    max(1, sum of the steps' points / 10), the step solvers as contributors;
 *  - reductions/<target>.R<n>.lean: 2 to 4 hypotheses, at most 3 reductions per target (oma_register_reduction), each
 *    step worth max(1, the target's points / n), the database's figure when it has the step;
 *  - statements/<id>.lean and shorter proofs: no points, shown in the person's history.
 */
export function computeWorld(entries: LedgerEntry[], problem: Lookup, dbSteps: Map<string, { points: number; reduction: string }>, repo: string): World {
  const sorted = [...entries].sort((a, b) => (a.merged_at < b.merged_at ? -1 : a.merged_at > b.merged_at ? 1 : a.pr - b.pr));
  const url = (n: number) => `https://github.com/${repo}/pull/${n}`;
  const formalized = new Set<string>();
  const steps = new Map<string, LStep>();
  const reductions = new Map<string, LReduction>();
  const perTarget = new Map<string, number>();
  const firsts = new Map<string, Credit>();
  const credits: Credit[] = [];
  const byHandle = new Map<string, Credit[]>();
  const events = new Map<string, LEvent[]>();
  const ids = new Set<string>();
  let evId = 0;
  const event = (handle: string, kind: string, problem_id: string, detail: string, created_at: string, pr: string) => {
    const k = handle.toLowerCase();
    const list = events.get(k) ?? [];
    list.push({ id: -++evId, kind, problem_id, detail, created_at, handle, pr });
    events.set(k, list);
  };
  const credit = (c: Credit) => {
    credits.push(c);
    const k = c.handle.toLowerCase();
    const list = byHandle.get(k) ?? [];
    list.push(c);
    byHandle.set(k, list);
  };
  const kindOf = (id: string): Kind | null => {
    const p = problem(id);
    if (!p) return null;
    return p.kind === "unformalized" && formalized.has(id) ? "open" : p.kind;
  };
  const targetPoints = (id: string): number | null => {
    const p = problem(id);
    if (p) return pointsFor(p.difficulty, kindOf(id)!);
    return dbSteps.get(id)?.points ?? steps.get(id)?.points ?? null;
  };
  const dbHyps = (rid: string) => {
    let n = 0;
    for (const s of dbSteps.values()) if (s.reduction === rid) n++;
    return n;
  };

  for (const e of sorted) {
    const pr = url(e.pr);
    if (e.kind === "statement") {
      if (!problem(e.id)) continue; // unknown_problem
      formalized.add(e.id);
      ids.add(e.id);
      event(e.handle, "formalized", e.id, pr, e.merged_at, pr);
      continue;
    }
    if (e.kind === "shorter") {
      ids.add(e.id);
      event(e.handle, "shorter", e.id, pr, e.merged_at, pr);
      continue;
    }
    if (e.kind === "reduction") {
      const m = e.path.match(REDUCTION_FILE_RE);
      if (!m) continue;
      const target = m[1];
      const rid = `${target}.R${m[2]}`;
      const pts = targetPoints(target);
      if (pts === null || reductions.has(rid)) continue; // unknown_target
      const n = e.hyps ?? dbHyps(rid);
      if (n < 2 || n > 4) continue; // bad_reduction
      if ((perTarget.get(target) ?? 0) >= 3) continue; // too_many_reductions
      perTarget.set(target, (perTarget.get(target) ?? 0) + 1);
      const red: LReduction = { id: rid, target, handle: e.handle, pr_url: pr, steps: [] };
      for (let k = 1; k <= n; k++) {
        const id = `${rid}.H${k}`;
        steps.set(id, { id, reduction: rid, parent: target, k, points: dbSteps.get(id)?.points ?? Math.max(1, Math.floor(pts / n)) });
        red.steps.push(id);
      }
      reductions.set(rid, red);
      ids.add(target);
      event(e.handle, "reduced", target, `${rid} into ${n} steps`, e.merged_at, pr);
      continue;
    }
    // A proof (or a disproof).
    const id = e.id;
    let points: number;
    const kind = kindOf(id);
    if (kind) {
      if (kind === "unformalized") continue; // not_formalized_yet
      const p = problem(id)!;
      points = pointsFor(p.difficulty, kind);
    } else if (STEP_RE.test(id) && (dbSteps.has(id) || steps.has(id))) {
      points = dbSteps.get(id)?.points ?? steps.get(id)!.points;
    } else continue; // unknown_problem, unknown_step
    const first = !firsts.has(id);
    const c: Credit = {
      problem_id: id, handle: e.handle, agent: e.agent, model: e.model, polarity: e.polarity, pr_url: pr,
      points: first ? points : 0, contributors: null, created_at: e.merged_at, first,
    };
    credit(c);
    ids.add(id);
    event(e.handle, "accepted", id, pr, e.merged_at, pr);
    if (!first) continue;
    firsts.set(id, c);
    // Climb: a closed step may close its parent, which may itself be a step.
    let cur = id;
    for (let guard = 0; guard < 100; guard++) {
      const st = steps.get(cur);
      const red = st ? reductions.get(st.reduction) : undefined;
      if (!st || !red || !red.steps.every((s) => firsts.has(s)) || firsts.has(red.target)) break;
      const total = red.steps.reduce((a, s) => a + (steps.get(s)?.points ?? 0), 0);
      const cl: Credit = {
        problem_id: red.target, handle: red.handle, agent: "reduction", model: null, polarity: "proof", pr_url: `${red.pr_url}#closed`,
        points: Math.max(1, Math.floor(total / 10)), contributors: [...new Set(red.steps.map((s) => firsts.get(s)!.handle))].sort(),
        created_at: e.merged_at, first: true,
      };
      credit(cl);
      firsts.set(red.target, cl);
      ids.add(red.target);
      event(red.handle, "accepted", red.target, `closed by reduction ${red.id}`, e.merged_at, cl.pr_url);
      cur = red.target;
    }
  }
  const people = new Set<string>();
  for (const e of entries) people.add(e.handle.toLowerCase());
  return { credits, firsts, byHandle, events, ids, handles: people.size, entries: entries.length };
}

/** A pull request by its number ("#closed" kept for a closure by reduction), whatever owner its link names: the
 * database's links and the ledger's stay comparable after the repository is transferred or renamed. */
export const prKey = (url: string) => {
  const m = url.match(/\/pull\/(\d+)(#closed)?$/);
  return m ? m[1] + (m[2] ?? "") : url;
};

const strip = (c: Credit): Solved => ({
  problem_id: c.problem_id, handle: c.handle, agent: c.agent, model: c.model, polarity: c.polarity, pr_url: c.pr_url,
  points: c.points, contributors: c.contributors, created_at: c.created_at,
});

/** The first solves the database does not have: problems it lists no solution for (its row wins when it has one). */
export function extraCredits(world: World, dbSolved: Solved[]): Credit[] {
  const problems = new Set(dbSolved.map((s) => s.problem_id));
  const prs = new Set(dbSolved.map((s) => prKey(s.pr_url)));
  return [...world.firsts.values()].filter((c) => !problems.has(c.problem_id) && !prs.has(prKey(c.pr_url)));
}

/** Every solved problem: the database's list plus the ledger's first solves it lacks, newest first. */
export function mergeSolved(dbSolved: Solved[], extra: Credit[]): Solved[] {
  if (!extra.length) return dbSolved;
  return [...dbSolved, ...extra.map(strip)].sort((a, b) => (a.created_at < b.created_at ? 1 : a.created_at > b.created_at ? -1 : 0));
}

export function mergeStats(stats: Stats, extra: Credit[], world: World, now = Date.now()): Stats {
  const have = new Set(stats.solved.map((s) => s.problem_id));
  const add = extra.filter((c) => !have.has(c.problem_id));
  if (!add.length && stats.contributors >= world.handles) return stats;
  const day = now - 86400_000;
  return {
    ...stats,
    solved: [...stats.solved, ...add.map((c) => ({ problem_id: c.problem_id, polarity: c.polarity }))],
    solvedToday: stats.solvedToday + add.filter((c) => Date.parse(c.created_at) >= day).length,
    contributors: Math.max(stats.contributors, world.handles),
  };
}

const MAX_BOARD = 500;

/**
 * The leaderboard (oma_leaderboard2: points, distinct problems solved, refutations, latest agent and model, claims)
 * with the ledger's credits added. The database's rows count what it recorded; the ledger adds the first solves it has
 * no row for. People below the database's 200 rows get their recorded first solves from its solved list. If the
 * board was read after the solved list, a first solve merged in between may already be in the board: those are left
 * out until the solved list catches up, so nothing is ever counted twice. Without the database's solved list, points
 * and proofs come from the ledger alone (claims and last seen still from the database).
 */
export function mergeBoard(
  dbBoard: Leader2[], boardAt: number | undefined, dbSolved: Solved[], solvedAt: number | undefined, extra: Credit[], world: World,
  minutes?: number, now = Date.now(),
): Leader2[] {
  const since = minutes ? now - minutes * 60_000 : -Infinity;
  const rows = new Map<string, Leader2>();
  for (const r of dbBoard) rows.set(r.handle.toLowerCase(), { ...r });
  const inBoard = new Set(rows.keys());
  const add = (c: Solved) => {
    const k = c.handle.toLowerCase();
    let r = rows.get(k);
    if (!r) {
      r = { handle: c.handle, solved: 0, disproofs: 0, points: 0, agent: null, model: null, claims: 0, handed_back: 0, last_seen: null };
      rows.set(k, r);
    }
    r.solved += 1;
    if (c.polarity === "disproof") r.disproofs += 1;
    r.points += c.points;
    if (c.agent) r.agent = c.agent;
    if (c.model) r.model = c.model;
    if (!r.last_seen || Date.parse(c.created_at) > Date.parse(r.last_seen)) r.last_seen = c.created_at;
  };
  const chrono = <T extends { created_at: string }>(l: T[]) => [...l].sort((a, b) => (a.created_at < b.created_at ? -1 : a.created_at > b.created_at ? 1 : 0));
  if (!dbSolved.length) {
    // No recorded solutions to rely on: points and proofs from the ledger alone.
    for (const r of rows.values()) Object.assign(r, { solved: 0, disproofs: 0, points: 0, agent: null, model: null });
    for (const c of chrono([...world.firsts.values()])) if (Date.parse(c.created_at) >= since) add(c);
  } else {
    if (!extra.length && dbBoard.length < 200) return dbBoard;
    for (const s of chrono(dbSolved)) if (!inBoard.has(s.handle.toLowerCase()) && Date.parse(s.created_at) >= since) add(s);
    const gapFrom = boardAt && solvedAt && boardAt > solvedAt ? solvedAt - 60_000 : Infinity;
    for (const c of chrono(extra)) {
      const t = Date.parse(c.created_at);
      if (t < since) continue;
      if (inBoard.has(c.handle.toLowerCase()) && t > gapFrom && t <= boardAt!) continue;
      add(c);
    }
  }
  return [...rows.values()]
    .filter((r) => r.points > 0 || r.solved > 0 || r.claims > 0)
    .sort((a, b) => b.points - a.points || b.solved - a.solved || b.claims - a.claims || (a.handle < b.handle ? -1 : a.handle > b.handle ? 1 : 0))
    .slice(0, MAX_BOARD);
}

const asEvent = (e: LEvent) => ({ id: e.id, kind: e.kind, problem_id: e.problem_id, detail: e.detail, created_at: e.created_at });

/** One person's profile: the database's, with the ledger's solutions it lacks (union by pull request); built from the
 * ledger alone when the database has none to give. A proof the ledger has but that is not the first solve of its
 * problem shows with no points; a closure by reduction shows only where it is the solution of record. */
export function mergeProfile(p: Profile | null, handle: string, world: World, dbSolved: Solved[], extra: Credit[]): Profile | null {
  const k = handle.toLowerCase();
  const dbRow = new Map(dbSolved.map((s) => [prKey(s.pr_url), s]));
  const extraPr = new Set(extra.map((c) => prKey(c.pr_url)));
  const isRecord = (c: Credit) => dbRow.has(prKey(c.pr_url)) || extraPr.has(prKey(c.pr_url));
  const mine = (world.byHandle.get(k) ?? []).filter((c) => c.agent !== "reduction" || isRecord(c));
  const minePr = new Set(mine.map((c) => c.pr_url));
  const evs = (world.events.get(k) ?? []).filter((e) => e.kind !== "accepted" || minePr.has(e.pr));
  const known = new Set((p?.solutions ?? []).map((s) => prKey(s.pr_url)));
  const added = mine.filter((c) => !known.has(prKey(c.pr_url))).map((c) => {
    const d = dbRow.get(prKey(c.pr_url));
    return {
      problem_id: d?.problem_id ?? c.problem_id, polarity: d?.polarity ?? c.polarity, pr_url: c.pr_url, agent: d?.agent ?? c.agent,
      model: d?.model ?? c.model, points: d ? d.points : extraPr.has(prKey(c.pr_url)) ? c.points : 0, created_at: d?.created_at ?? c.created_at,
    };
  });
  const gained = added.reduce((a, s) => a + s.points, 0);
  const closures = [...world.firsts.values()].filter((c) =>
    c.agent === "reduction" && isRecord(c) && c.handle.toLowerCase() !== k && !!c.contributors?.some((h) => h.toLowerCase() === k));
  const byDate = <T extends { created_at: string }>(a: T, b: T) => (a.created_at < b.created_at ? 1 : a.created_at > b.created_at ? -1 : 0);
  if (!p) {
    if (!mine.length && !evs.length && !closures.length) return null;
    const events = [...evs].sort(byDate).map(asEvent);
    return {
      handle: mine[0]?.handle ?? evs[0]?.handle ?? handle,
      solutions: added.sort(byDate),
      contributed: closures.map((c) => ({ problem_id: c.problem_id, lead: c.handle, created_at: c.created_at })),
      points: gained, live: [], events, claims: 0,
      firstSeen: events.length ? events[events.length - 1].created_at : null,
    };
  }
  // The database's history is its latest 80 events: ledger events are added for the solutions it lacks, and for any
  // other merged work after its newest event (what it missed while it was down).
  const newest = p.events.reduce((a, e) => (e.created_at > a ? e.created_at : a), "");
  const details = new Set(p.events.map((e) => `${e.kind} ${e.problem_id} ${e.detail}`));
  const addedPr = new Set(added.map((s) => s.pr_url));
  const extraEvents = evs
    .filter((e) => (e.kind === "accepted" ? addedPr.has(e.pr) : e.created_at > newest && !details.has(`${e.kind} ${e.problem_id} ${e.detail}`)))
    .map(asEvent);
  const contributed = [...(p.contributed ?? [])];
  const haveContrib = new Set(contributed.map((c) => c.problem_id));
  for (const c of closures) if (!haveContrib.has(c.problem_id)) contributed.push({ problem_id: c.problem_id, lead: c.handle, created_at: c.created_at });
  if (!added.length && !extraEvents.length && contributed.length === (p.contributed?.length ?? 0)) return p;
  return {
    ...p,
    solutions: [...p.solutions, ...added].sort(byDate),
    contributed: contributed.sort(byDate),
    points: (p.points ?? p.solutions.reduce((a, s) => a + s.points, 0)) + gained,
    events: [...p.events, ...extraEvents].sort(byDate),
  };
}
