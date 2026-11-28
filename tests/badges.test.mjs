// Unit tests of the contributor badges and chart series (no network, no database, no catalogue).
// Run: node --experimental-strip-types --test tests/badges.test.mjs   (Node 22.6+)
import { test } from "node:test";
import assert from "node:assert/strict";
import { computeBadges, rankOf, tierOf, claimedHours } from "../lib/badges.ts";
import { profileStats, topBars } from "../lib/profilestats.ts";

const KIND = { o1: "open", o2: "open", o3: "open", k1: "known", k2: "known", w1: "warmup", p1: "pending" };
const FIELD = { o1: "Number Theory", o2: "Combinatorics", o3: "Geometry", k1: "Algebra", k2: "Number Theory", w1: "Logic", p1: "Analysis" };
const info = (id) => (KIND[id] ? { outcome: KIND[id], fields: [FIELD[id]], source: "Src" } : null);
const at = (d, h = 0) => `2026-11-${String(d).padStart(2, "0")}T${String(h).padStart(2, "0")}:00:00Z`;
const base = {
  board: [
    { handle: "alice", points: 900, solved: 5, disproofs: 2 },
    { handle: "bob", points: 500, solved: 9, disproofs: 0 },
    { handle: "carol", points: 500, solved: 1, disproofs: 2 },
  ],
  records: [
    { problem_id: "o1", handle: "alice", polarity: "proof", created_at: at(1) },
    { problem_id: "o2", handle: "alice", polarity: "disproof", created_at: at(2) },
    { problem_id: "o3", handle: "bob", polarity: "proof", created_at: at(3), contributors: ["bob", "carol"] },
    { problem_id: "k1", handle: "bob", polarity: "proof", created_at: at(4) },
    { problem_id: "p1", handle: "carol", polarity: "proof", created_at: at(5) },
    { problem_id: "w1", handle: "carol", polarity: "proof", created_at: at(6) },
  ],
  solutions: [],
  events: [],
  info,
};
const of = (handle, extra = {}) => Object.fromEntries(computeBadges({ ...base, handle, ...extra }).map((b) => [b.id, b]));

test("ranks are competition ranks, zero earns nothing", () => {
  assert.equal(rankOf([10, 10, 8], 10), 1);
  assert.equal(rankOf([10, 10, 8], 8), 3);
  assert.equal(rankOf([10, 0], 0), null);
  assert.deepEqual([1, 2, 3, 4, 10, 11, 100, 101].map(tierOf), ["gold", "silver", "silver", "bronze", "bronze", "plain", "plain", null]);
});

test("points, proofs, refuter tiers from the leaderboard", () => {
  const a = of("alice");
  assert.equal(a.points.title, "Most points");
  assert.equal(a.points.tier, "gold");
  assert.equal(a.proofs.rank, 2);
  assert.equal(a.refuter.rank, 1);
  const c = of("carol");
  assert.equal(c.points.rank, 2); // tied with bob
  assert.equal(c.points.title, "Top 3 · points");
  assert.equal(c.refuter.rank, 1); // tied with alice
  assert.equal(of("bob").refuter, undefined);
});

test("open problems: only outcome 'open' counts; contributors count, first solver does not", () => {
  const a = of("alice"), c = of("carol");
  assert.equal(a.open.value, 2);
  assert.equal(a.open.rank, 1);
  assert.equal(c.open.value, 1); // o3 as credited contributor; p1 is pending and does not count
  assert.equal(c.first, undefined); // contributor, not first solver; p1 pending
  assert.equal(a.first.value, 2);
  assert.equal(of("bob").first.value, 1);
});

test("pioneer: order of first checked proof", () => {
  assert.equal(of("alice").pioneer.rank, 1);
  assert.equal(of("alice").pioneer.tier, "gold");
  assert.equal(of("carol").pioneer.rank, 3);
  // a newcomer with one proof after everyone
  const d = of("dave", { solutions: [{ problem_id: "k2", polarity: "proof", created_at: at(20) }] });
  assert.equal(d.pioneer.rank, 4);
  assert.equal(d.pioneer.title, "Pioneer · first 10");
});

test("marathon by distinct days, polymath from five fields", () => {
  const ids = ["o1", "o2", "o3", "k1", "w1"];
  const sol = ids.map((id, i) => ({ problem_id: id, polarity: "proof", created_at: at(i + 10) }));
  const z = of("zed", { solutions: sol });
  assert.equal(z.marathon.value, 5);
  assert.equal(z.marathon.rank, 1);
  assert.equal(z.polymath.value, 5);
  assert.equal(of("zed", { solutions: sol.slice(0, 4) }).polymath, undefined); // four fields: below the floor
  assert.equal(of("alice").polymath, undefined);
});

test("claimed hours: claim to release or submit, per problem", () => {
  const ev = [
    { kind: "claim", problem_id: "a", created_at: at(1, 0) },
    { kind: "claim", problem_id: "b", created_at: at(1, 1) },
    { kind: "submit", problem_id: "a", created_at: at(1, 3) },
    { kind: "release", problem_id: "b", created_at: at(1, 2) },
    { kind: "release", problem_id: "c", created_at: at(1, 5) },
  ];
  assert.equal(claimedHours(ev), 4);
});

test("chart series: cumulative points, per-day buckets with gaps, breakdowns, heatmap", () => {
  const s = profileStats({
    solutions: [
      { problem_id: "o1", polarity: "proof", points: 50, created_at: at(1, 9) },
      { problem_id: "k1", polarity: "proof", points: 5, created_at: at(3, 9) },
      { problem_id: "zz", polarity: "proof", points: 2, created_at: at(3, 22) },
    ],
    events: [{ kind: "claim", problem_id: "o1", created_at: at(1, 8) }, { kind: "accepted", problem_id: "o1", created_at: at(1, 9) }, { kind: "claim", problem_id: "k1", created_at: at(3, 9) }],
    info,
  });
  assert.deepEqual(s.cumulative.map((c) => c.total), [50, 55, 57]);
  assert.deepEqual(s.perDay.map((d) => d.value), [1, 0, 2]);
  assert.equal(s.bucket, "day");
  assert.deepEqual(s.byOutcome.map((b) => [b.label, b.value]), [["Open problem solved", 1], ["Known result formalized", 1], ["Reduction step", 1]]);
  assert.equal(s.heat.mode, "date");
  assert.equal(s.heat.rows.length, 3);
  assert.equal(s.heat.cells[0][8] + s.heat.cells[0][9], 2);
  assert.equal(s.heat.max, 1);
});

test("top bars fold the tail into Other", () => {
  const m = new Map(Object.entries({ a: 9, b: 5, c: 3, d: 1, e: 1 }));
  assert.deepEqual(topBars(m, 2).map((b) => [b.label, b.value]), [["a", 9], ["b", 5], ["Other", 5]]);
  assert.equal(topBars(m, 2).at(-1).rest, true);
  assert.equal(topBars(m, 4).length, 5); // one left over: shown, not folded
});
