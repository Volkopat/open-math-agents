import Mathlib

/-!
# OEIS A288427: a(n)/n -> m = 1.93..., and -1 < m - a(n)/n < 1

Source: https://oeis.org/A288427 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Jun 10 2017), offset 1: Positions of 0 in A288426; complement of A288428.
Conjecture: a(n)/n -> 1.93..., and if m denotes this number, then -1 < m - a(n)/n < 1 for n >= 1.
Data: 1, 3, 4, 5, 7, 10, 11, 14, 15, 16, 19, 20, ...
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
* `a n` adds 1 to the 0-based index of the n-th 0 of `W`, so positions count from 1 as in the
  entry; `Nat.nth` counts its argument from 0.
* The entry gives the limit only as 1.93..., so `main` asks for a real number m with
  1.93 <= m < 1.94, the numbers whose decimal expansion starts 1.93, such that a(n)/n tends to m
  as a limit of real numbers and -1 < m - a(n)/n < 1 for every n >= 1, with a(n)/n a real
  quotient. This is the conjunction of both parts of the conjecture. The proof takes
  m = 2 lam - 1 = 1.93114..., where lam is the root of x^3 - x^2 - 1 in [1.4655, 1.4656].
-/

namespace OMA.S_oeis_a288427

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

/-- A288427(n): the position, counted from 1 as in the entry, of the n-th 0 of A288426. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => W i = 0) (n - 1) + 1

/-- Kimberling's conjecture: a(n)/n tends to a number m = 1.93..., and -1 < m - a(n)/n < 1
for n >= 1. -/
theorem main : ∃ m : ℝ, (1.93 ≤ m ∧ m < 1.94) ∧
    Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 m) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < m - (a n : ℝ) / n ∧ m - (a n : ℝ) / n < 1 := by
  sorry

end OMA.S_oeis_a288427
