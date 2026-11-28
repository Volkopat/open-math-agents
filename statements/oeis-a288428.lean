import Mathlib

/-!
# OEIS A288428: a(n)/n -> m = 2.07..., and -1 < m - a(n)/n < 1

Source: https://oeis.org/A288428 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Jun 11 2017), offset 1: Positions of 1 in A288426; complement of A288427.
Conjecture: a(n)/n->2.07..., and if m denotes this number, then -1 < m - a(n)/n < 1 for n >= 1.
Data: 2, 6, 8, 9, 12, 13, 17, 18, 22, 24, 25, 26, ...
A288426 (Clark Kimberling, Jun 10 2017), offset 1: Fixed point of the mapping 00->0101, 10->100,
starting with 00. Its iterates, starting with 00: 00, 0101, 01001, 010001, 010001011, ...
Its program: w[n_] := StringReplace[w[n - 1], {00 -> 0101, 10 -> 100}] with w[0] = 00.

Formalization notes:
* `step` is one pass of StringReplace with the rules 00 -> 0101 and 10 -> 100 over a finite word:
  read from the left, where 00 starts it is replaced by 0101, where 10 starts it is replaced by
  100, and any other letter is copied. The two left sides start with different letters, so the
  order in which the rules are tried does not matter.
* `iter n` is the n-th iterate, starting with 00 as in the entry. The iterates are not nested
  (0101 is not a prefix of 01001), but letter i is the same in every iterate from iterate i + 1
  on (lemmas `stable` and `W_eq` of the proof: iterate n + 1 is a word of more than n + 2 letters
  followed by 1, and that word begins every later iterate), so `W i`, letter i of iterate i + 1,
  is letter i of the limit of the iterates: `W` is the fixed point A288426, indexed from 0.
* `a n` adds 1 to the 0-based index of the n-th 1 of `W`, so positions count from 1 as in the
  entry; `Nat.nth` counts its argument from 0.
* The entry gives the limit only as 2.07..., so `main` asks for a real number m with
  2.07 <= m < 2.08, the numbers whose decimal expansion starts 2.07, such that a(n)/n tends to m
  as a limit of real numbers and -1 < m - a(n)/n < 1 for every n >= 1, with a(n)/n a real
  quotient. This is the conjunction of both parts of the conjecture. The proof takes
  m = 1 + lam^2/2 = 2.07394..., where lam is the root of x^3 - x^2 - 1 in [1.4655, 1.4656].
-/

namespace OMA.S_oeis_a288428

open Filter Topology

/-- One pass of StringReplace with the rules 00 -> 0101 and 10 -> 100 over a finite word, read
from the left: where 00 starts it is replaced by 0101, where 10 starts it is replaced by 100,
and any other letter is copied. -/
def step : List ℕ → List ℕ
  | 0 :: 0 :: l => 0 :: 1 :: 0 :: 1 :: step l
  | 1 :: 0 :: l => 1 :: 0 :: 0 :: step l
  | x :: l => x :: step l
  | [] => []

/-- The iterates of the mapping, starting with 00. -/
def iter : ℕ → List ℕ
  | 0 => [0, 0]
  | n + 1 => step (iter n)

/-- A288426 (0-indexed): the fixed point of the mapping, the limit of the iterates. Letter i is
the same in every iterate from iterate i + 1 on, and it is read off iterate i + 1. -/
def W (i : ℕ) : ℕ := (iter (i + 1)).getD i 0

/-- A288428(n): the position, counted from 1 as in the entry, of the n-th 1 of A288426. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => W i = 1) (n - 1) + 1

/-- Kimberling's conjecture: a(n)/n tends to a number m = 2.07..., and -1 < m - a(n)/n < 1
for n >= 1. -/
theorem main : ∃ m : ℝ, (2.07 ≤ m ∧ m < 2.08) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 1 := by
  sorry

end OMA.S_oeis_a288428
