/**
 * Prestige badges of a contributor page (app/a/[handle]), computed from the leaderboard, the solver of record of every
 * problem and the person's own profile. Pure: no database, no catalogue import. The caller passes `info`, which says
 * for a problem or step id what it counts as (outcomeOf of lib/outcome.ts, so an open problem counts as solved only
 * once its statement is confirmed in content/open_review.json) and its fields. Unit tests: tests/badges.test.mjs.
 *
 * Ranks are competition ranks (ties share the better rank: 10, 10, 8 ranks #1, #1, #3) and only a value above zero
 * earns a badge. Tiers: #1 gold, top 3 silver, top 10 bronze, top 100 plain.
 */
import type { Outcome } from "@/lib/outcome";

export type Tier = "gold" | "silver" | "bronze" | "plain";
export type Badge = {
  id: "points" | "open" | "proofs" | "pioneer" | "marathon" | "refuter" | "polymath" | "first";
  /** Short title on the chip, e.g. "Most points", "Top 10 · Lean proofs". */
  title: string;
  /** Second line on the chip, e.g. "#4 of 412", "×38". */
  sub: string;
  tier: Tier;
  /** One line: why it was earned, and what it is computed from. */
  why: string;
  rank?: number;
  of?: number;
  value: number;
};

export type BadgeInput = {
  handle: string;
  /** The leaderboard (getLeaderboard2): points, checked proofs (solved) and disproofs of everyone. */
  board: { handle: string; points: number; solved: number; disproofs: number }[];
  /** The solver of record of every solved problem and step (getSolved): the first accepted proof of each. */
  records: { problem_id: string; handle: string; polarity: string; created_at: string; contributors?: string[] | null }[];
  /** The person's own checked proofs (Profile.solutions) and events (Profile.events). */
  solutions: { problem_id: string; polarity: string; created_at: string }[];
  events: { kind: string; problem_id: string; created_at: string }[];
  /** What an id counts as, and its fields (a step: its parent problem's fields). Null: unknown, counted as a step. */
  info: (id: string) => { outcome: Outcome; fields: string[] } | null;
};

/** Fewest distinct fields for Polymath: a handful of proofs always spans two or three. */
export const POLYMATH_MIN = 5;
const lc = (s: string) => s.toLowerCase();
const n = (x: number) => x.toLocaleString("en-US");
const plural = (k: number, one: string, many = one + "s") => `${n(k)} ${k === 1 ? one : many}`;

/** Competition rank of `mine` among `values` (higher is better), or null if mine is 0. */
export function rankOf(values: number[], mine: number): number | null {
  if (!(mine > 0)) return null;
  return 1 + values.filter((v) => v > mine).length;
}

export function tierOf(rank: number | null): Tier | null {
  if (rank === null) return null;
  return rank === 1 ? "gold" : rank <= 3 ? "silver" : rank <= 10 ? "bronze" : rank <= 100 ? "plain" : null;
}

/** "Most points" at #1, "Top 3 · points" etc. below. */
function ranked(id: Badge["id"], top: string, short: string, rank: number | null, of: number, value: number, why: (r: number) => string): Badge | null {
  const tier = tierOf(rank);
  if (!tier || rank === null) return null;
  const title = tier === "gold" ? top : `Top ${tier === "silver" ? 3 : tier === "bronze" ? 10 : 100} · ${short}`;
  return { id, title, sub: `#${rank} of ${n(of)}`, tier, why: why(rank), rank, of, value };
}

/** Sum of the time between each claim and the release or submission that ended it, in hours (one person). */
export function claimedHours(events: BadgeInput["events"]): number {
  const ev = [...events].sort((a, b) => a.created_at.localeCompare(b.created_at));
  const open = new Map<string, number>();
  let ms = 0;
  for (const e of ev) {
    const t = Date.parse(e.created_at);
    if (e.kind === "claim") { if (!open.has(e.problem_id)) open.set(e.problem_id, t); }
    else if ((e.kind === "release" || e.kind === "submit") && open.has(e.problem_id)) {
      ms += Math.max(0, t - open.get(e.problem_id)!);
      open.delete(e.problem_id);
    }
  }
  return ms / 3_600_000;
}

export function computeBadges(inp: BadgeInput): Badge[] {
  const me = lc(inp.handle);
  const out: (Badge | null)[] = [];
  const boardMe = inp.board.find((r) => lc(r.handle) === me);
  const of = inp.board.length;

  // Per handle, from the solver-of-record list: open problems solved (as solver or credited contributor), the first
  // checked proof, distinct UTC days with a checked proof, distinct primary fields.
  type Acc = { open: Set<string>; first: number; days: Set<string>; fields: Set<string>; firstSolves: number };
  const acc = new Map<string, Acc>();
  const get = (h: string) => {
    let a = acc.get(h);
    if (!a) { a = { open: new Set(), first: Infinity, days: new Set(), fields: new Set(), firstSolves: 0 }; acc.set(h, a); }
    return a;
  };
  for (const r of inp.records) {
    const i = inp.info(r.problem_id);
    const isOpen = i?.outcome === "open";
    const lead = get(lc(r.handle));
    const t = Date.parse(r.created_at);
    if (t < lead.first) lead.first = t;
    lead.days.add(r.created_at.slice(0, 10));
    if (i?.fields[0]) lead.fields.add(i.fields[0]);
    if (isOpen) { lead.open.add(r.problem_id); lead.firstSolves++; }
    if (isOpen) for (const c of r.contributors ?? []) if (lc(c) !== lc(r.handle)) get(lc(c)).open.add(r.problem_id);
  }
  // The person's own proofs complete their row (a later proof of a problem someone else solved first is not a record).
  const mine = get(me);
  for (const s of inp.solutions) {
    const t = Date.parse(s.created_at);
    if (t < mine.first) mine.first = t;
    mine.days.add(s.created_at.slice(0, 10));
    const f = inp.info(s.problem_id)?.fields[0];
    if (f) mine.fields.add(f);
  }
  const rows = [...acc.entries()];
  const all = (f: (a: Acc) => number) => rows.map(([, a]) => f(a));

  // 1. Points.
  const pts = boardMe?.points ?? 0;
  out.push(ranked("points", "Most points", "points", rankOf(inp.board.map((r) => r.points), pts), of, pts,
    (r) => `${r === 1 ? "More points than anyone" : `#${r} of ${n(of)} by points`} on the leaderboard: ${plural(pts, "point")}.`));

  // 2. Open problems solved (outcomeOf "open" only: statement confirmed by review).
  const op = mine.open.size;
  out.push(ranked("open", "Most open problems solved", "open problems", rankOf(all((a) => a.open.size), op), of, op,
    (r) => `${plural(op, "open problem")} solved (statement confirmed by review), as solver of record or credited contributor: #${r} on the site.`));

  // 3. Lean proofs.
  const pr = boardMe?.solved ?? inp.solutions.length;
  out.push(ranked("proofs", "Most Lean proofs", "Lean proofs", rankOf(inp.board.map((r) => r.solved), pr), of, pr,
    (r) => `${plural(pr, "proof")} checked by Lean, of any kind (open, known, warm-up, step): #${r} on the leaderboard.`));

  // 4. Pioneer: order of first checked proof.
  if (Number.isFinite(mine.first)) {
    const order = 1 + rows.filter(([h, a]) => h !== me && a.first < mine.first).length;
    const day = new Date(mine.first).toISOString().slice(0, 10);
    if (order <= 100) out.push({
      id: "pioneer", title: order <= 10 ? "Pioneer · first 10" : "Pioneer · first 100", sub: `#${order} to arrive`, tier: order === 1 ? "gold" : order <= 10 ? "silver" : "plain",
      why: `Contributor #${order} by first checked proof (${day} UTC). Ordered by first proof, the one date known for everyone.`, rank: order, of: rows.length, value: order,
    });
  }

  // 5. Marathon: distinct UTC days with a checked proof (the one measure known for everyone); claimed hours as context.
  const days = mine.days.size;
  const hours = claimedHours(inp.events);
  const mr = rankOf(all((a) => a.days.size), days);
  if (days >= 2) out.push(ranked("marathon", "Marathon", "active days", mr, rows.length, days,
    (r) => `Checked proofs on ${plural(days, "distinct UTC day")} (#${r}); ${Math.round(hours).toLocaleString("en-US")} h between claims and their release or submission. Ranked by days: durations are not known for everyone.`));

  // 6. Refuter: disproofs.
  const dp = boardMe?.disproofs ?? inp.solutions.filter((s) => s.polarity === "disproof").length;
  out.push(ranked("refuter", "Refuter", "disproofs", rankOf(inp.board.map((r) => r.disproofs), dp), of, dp,
    (r) => `${plural(dp, "statement")} refuted with a Lean disproof (counterexample or negation proved): #${r} on the site.`));

  // 7. Polymath: distinct primary fields.
  const fl = mine.fields.size;
  if (fl >= POLYMATH_MIN) out.push(ranked("polymath", "Polymath", "breadth", rankOf(all((a) => a.fields.size), fl), rows.length, fl,
    (r) => `Proofs in ${n(fl)} different fields (each problem's primary field): #${r} for breadth.`));

  // 8. First solver: open problems where this person's proof is the first accepted one, on record.
  const fs = mine.firstSolves;
  if (fs > 0) {
    const r = rankOf(all((a) => a.firstSolves), fs)!;
    out.push({
      id: "first", title: "First solver", sub: `×${n(fs)}`, tier: tierOf(r) ?? "plain",
      why: `First accepted proof on record for ${plural(fs, "open problem")} (statement confirmed by review).`, rank: r, of: rows.length, value: fs,
    });
  }

  const order: Tier[] = ["gold", "silver", "bronze", "plain"];
  return (out.filter(Boolean) as Badge[]).sort((a, b) => order.indexOf(a.tier) - order.indexOf(b.tier));
}
