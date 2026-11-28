import Mathlib

/-!
# OEIS A289076: a(n)/n -> m = 2.05..., and -1 < m - a(n)/n < 0

Source: https://oeis.org/A289076 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Jun 28 2017), offset 1: Positions of 1 in A289074; complement of A289075.
Conjecture: a(n)/n -> 2.05..., and if m denotes this number, then -1 < m - a(n)/n < 0 for n >= 1.
Data: 3, 5, 8, 12, 13, 16, 19, 20, 21, 25, 26, 29, ...
A289074 (Clark Kimberling, Jun 27 2017), offset 1: Fixed point of the mapping 00->0010, 01->011,
10->100, starting with 00. Data: 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 1, 0, ...
Its program: w[n_] := StringReplace[w[n - 1], {00 -> 0010, 01 -> 011, 10 -> 100}] with w[0] = 00,
and the word is read off w[11].

Formalization notes:
* `step` is one pass of StringReplace with the rules 00 -> 0010, 01 -> 011 and 10 -> 100 over a
  finite word: read from the left, where 00, 01 or 10 starts it is replaced by 0010, 011 or 100, and
  any other letter (a 1 before a 1, or a final letter) is copied. The three left sides are the three
  pairs other than 11, so the order in which the rules are tried does not matter.
* `iter n` is the n-th iterate, starting with 00 as in the entry. Each iterate is a prefix of the
  next (lemma `iter_prefix` of the proof: a lone final letter is copied and every rule image begins
  with the first letter of its pair, so a pass maps a prefix of a word to a prefix of its image) and
  iterate i + 1 has more than i letters (lemma `iter_length`), so `W i`, letter i of iterate i + 1,
  is letter i of the fixed point: `W` is A289074, indexed from 0.
* `a n` adds 1 to the 0-based index of the n-th 1 of `W`, so positions count from 1 as in the entry;
  `Nat.nth` counts its argument from 0.
* The entry gives the limit only as 2.05..., so `main` asks for a real number m with
  2.05 <= m < 2.06, the numbers whose decimal expansion starts 2.05, such that a(n)/n tends to m as
  a limit of real numbers and -1 < m - a(n)/n < 0 for every n >= 1, with a(n)/n a real quotient.
  This is the conjunction of both parts of the conjecture.
-/

namespace OMA.S_oeis_a289076

open Filter Topology

/-- One pass of StringReplace with the rules 00 -> 0010, 01 -> 011 and 10 -> 100 over a finite
word, read from the left: where 00, 01 or 10 starts it is replaced by 0010, 011 or 100, and any
other letter (a 1 before a 1, or a final letter) is copied. -/
def step : List ℕ → List ℕ
  | 0 :: 0 :: l => 0 :: 0 :: 1 :: 0 :: step l
  | 0 :: 1 :: l => 0 :: 1 :: 1 :: step l
  | 1 :: 0 :: l => 1 :: 0 :: 0 :: step l
  | x :: l => x :: step l
  | [] => []

/-- The iterates of the mapping, starting with 00. -/
def iter : ℕ → List ℕ
  | 0 => [0, 0]
  | n + 1 => step (iter n)

/-- A289074 (0-indexed): the fixed point of the mapping, the infinite word of which every iterate
is a prefix; its letter i is read off iterate i + 1, which has more than i letters. -/
def W (i : ℕ) : ℕ := (iter (i + 1)).getD i 0

/-- A289076(n): the position, counted from 1 as in the entry, of the n-th 1 of A289074. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => W i = 1) (n - 1) + 1

/-- Kimberling's conjecture: a(n)/n tends to a number m = 2.05..., and -1 < m - a(n)/n < 0
for n >= 1. -/
theorem main : ∃ m : ℝ, (2.05 ≤ m ∧ m < 2.06) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 0 := by
  sorry

end OMA.S_oeis_a289076
