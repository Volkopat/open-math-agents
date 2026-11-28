// Unit tests of the team board helpers (no network, no database): Lean snippet rules, PLAN parsing, which teammates'
// lemmas a merged proof uses (credit), and the action suggested to each role.
// Run: node --experimental-strip-types --test tests/team.test.mjs   (Node 22.6+)
import { test } from "node:test";
import assert from "node:assert/strict";
import { snippetProblems, declarations, planItems, usedNoteIds, usedNotes } from "../lib/snippet.ts";
import { suggestFor, teamFields, roleTask } from "../lib/collab.ts";

test("snippet: a plain lemma passes", () => {
  assert.deepEqual(snippetProblems("lemma foo (n : ℕ) : n + 0 = n := by simp"), []);
  assert.deepEqual(snippetProblems("-- helper\n@[simp] theorem bar : 1 + 1 = 2 := by\n  set_option maxHeartbeats 400000 in\n  norm_num"), []);
});

test("snippet: what the checker refuses is refused", () => {
  const bad = {
    "#eval IO.println 1\nlemma a : True := trivial": "forbidden",
    "lemma a : True := by sorry": "sorry",
    "lemma a : True := by native_decide": "native_decide",
    "import Mathlib\nlemma a : True := trivial": "import",
    'lemma a : "x" = "x" := rfl': "double-quote",
    "@[implemented_by foo] lemma a : True := trivial": "attribute",
    "set_option maxHeartbeats 0\nlemma a : True := trivial": "set_option",
    "macro_rules | `(tactic| foo) => `(tactic| rfl)\nlemma a : True := trivial": "macro",
    "lemma a : True := by\n  run_tac pure ()": "run_tac",
    "/- open comment\nlemma a : True := trivial": "unterminated",
    "def f : ℕ := 3": "declares no lemma",
  };
  for (const [code, why] of Object.entries(bad)) {
    const p = snippetProblems(code);
    assert.ok(p.some((x) => x.includes(why)), `${JSON.stringify(code)} -> ${JSON.stringify(p)}`);
  }
  // a banned word inside a comment is fine, as in tools/lint.py
  assert.deepEqual(snippetProblems("-- no sorry here\nlemma a : True := trivial"), []);
});

test("declarations: names and normalized heads", () => {
  const d = declarations("lemma foo (n : ℕ) :\n    n + 0 = n := by simp\n\n-- lemma commented : False := x\ntheorem OMA.solution : True := trivial\nprivate theorem bar\n  {a : ℕ} : a = a := rfl");
  assert.deepEqual(d, [{ name: "foo", head: "foo (n : ℕ) : n + 0 = n" }, { name: "bar", head: "bar {a : ℕ} : a = a" }]);
});

test("plan: lemma lines become items", () => {
  const items = planItems(`PLAN: induction on n.
- lemma step_bound (n : ℕ) : f (n + 1) ≤ 2 * f n   -- by the recurrence
- lemma base_case : f 0 = 1
theorem long_one (a b : ℕ)
    (h : a ≤ b) : g a ≤ g b := by sorry
lemma step_bound : duplicate
The lemma below is prose, not a subgoal.
* lemma bad name : x`);
  assert.deepEqual(items.map((x) => x.name), ["step_bound", "base_case", "long_one", "bad"]);
  assert.equal(items[0].statement, "(n : ℕ) : f (n + 1) ≤ 2 * f n");
  assert.equal(items[0].detail, "by the recurrence");
  assert.equal(items[2].statement, "(a b : ℕ) (h : a ≤ b) : g a ≤ g b");
  assert.deepEqual(planItems("DONE: lemma x : True"), []);
  assert.equal(planItems("PLAN:\n" + Array.from({ length: 12 }, (_, i) => `lemma l${i} : True`).join("\n")).length, 8);
});

test("credit: which notes a merged proof uses", () => {
  const src = `import X
-- uses note #11 · board #1 step_bound · by @bob
lemma step_bound (n : ℕ) : f (n + 1) ≤ 2 * f n := by
  omega
lemma renamed_base : f 0 = 1 := by rfl
theorem OMA.solution : type_of% @X.x := by
  exact foo`;
  const cands = [
    { id: 11, text: "DONE: board #1 step_bound\nlemma step_bound (n : ℕ) :\n  f (n + 1) ≤ 2 * f n := by\n  simp" }, // same head
    { id: 12, text: "DONE: lemma base_case : f 0 = 1 := by rfl" },                                  // not in the file
    { id: 13, text: "DONE: lemma renamed_base : f 0 = 1 := by decide" },                            // same head
    { id: 14, text: "DONE: lemma step_bound (n : ℕ) : f n ≤ f (n + 1) := by simp" },               // same name, other head, not named
    { id: 15, text: "DONE: the case n = 3 works by hand" },                                        // no Lean
    { id: 16, text: "DONE: lemma step_bound (m : ℕ) : f (m+1) ≤ 2 * f m := by simp" },             // named in the body, name declared
  ];
  assert.deepEqual(usedNotes(src, "Lease: x\nUses: #16, #15\n", cands), [11, 13, 16]);
  assert.deepEqual(usedNoteIds("Uses: #1 #2\nThanks #3", "-- uses note #4\n-- USES NOTE #5"), [1, 2, 4, 5]);
});

test("suggestions route each role", () => {
  const board = {
    complete: false,
    items: [
      { k: 1, name: "a", status: "done", done_by: "bob" },
      { k: 2, name: "b", status: "taken", owner: "carol" },
      { k: 3, name: "c", status: "open" },
    ],
    steps: [{ id: "P.R1.H1", status: "open", agents: 2 }, { id: "P.R1.H2", status: "open", agents: 0 }],
  };
  assert.equal(suggestFor("helper", board, "P").item, 3);
  assert.equal(suggestFor("checker", board, "P").action, "verify");
  assert.equal(suggestFor("helper", board, "P", "carol").item, 2);
  assert.equal(suggestFor("lead", board, "P"), null);
  const noItems = { complete: false, items: [{ k: 1, name: "a", status: "dead" }], steps: board.steps };
  assert.equal(suggestFor("scout", noItems, "P").step, "P.R1.H2");
  assert.equal(suggestFor("lead", noItems, "P").action, "plan");
  const done = { complete: true, items: [{ k: 1, name: "a", status: "done", done_by: "bob" }, { k: 2, name: "b", status: "dead" }], steps: [] };
  assert.match(suggestFor("lead", done, "P").text, /^ASSEMBLE NOW/);
  assert.equal(suggestFor("helper", done, "P").action, "assemble");
});

test("teamFields: unchanged without the board", () => {
  const r = { role: "checker", team: [{ handle: "m", role: "lead" }], notes: [], last_note: 3 };
  const f = teamFields(r);
  assert.deepEqual(Object.keys(f), ["role", "roleTask", "team", "teamNotes", "lastNote", "collaboration"]);
  assert.equal(f.roleTask, roleTask("checker"));
  const g = teamFields({ ...r, board: { complete: true, items: [{ k: 1, name: "a", status: "done" }], steps: [] } }, { boardOn: true, id: "P" });
  assert.equal(g.assemble, true);
  assert.equal(g.boardEnabled, true);
  const h = teamFields({ ...r, notes: [{ id: 5, handle: "x", at: "t", note: "DEAD END: a" }] }, { deadEnds: [{ id: 5, handle: "x", at: "t", note: "DEAD END: a" }, { id: 2, handle: "y", at: "t", note: "DEAD END: b" }] });
  assert.deepEqual(h.deadEnds.map((n) => n.id), [2]);
});
