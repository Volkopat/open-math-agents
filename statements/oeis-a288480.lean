import Mathlib

/-!
# OEIS A288480: a(n)/n -> 1 + sqrt(1/2) and -1 < 1 + sqrt(1/2) - a(n)/n < 1

Source: https://oeis.org/A288480 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Jun 12 2017), offset 1: Positions of 1 in A288478; complement of A288479.
Conjecture: a(n)/n -> 1 + sqrt(1/2), and -1 < 1 + sqrt(1/2) - a(n)/n < 1 for n >= 1.
Data: 2, 3, 5, 6, 9, 10, 12, 13, ...
A288478 (Clark Kimberling, Jun 12 2017), offset 1: Fixed point of the mapping 00->0101, 1->110,
starting with 00. Its iterates, starting with 00: 00, 0101, 01100110, 011011001011101100, ...
Its program: w[n_] := StringReplace[w[n - 1], {00 -> 0101, 1 -> 110}] with w[0] = 00.

Formalization notes:
* `step` is one pass of StringReplace with the rules 00 -> 0101 and 1 -> 110 over a finite word:
  read from the left, where 00 starts it is replaced by 0101, a letter 1 is replaced by 110, and
  any other letter (a 0 not followed by 0) is copied. The two left sides start with different
  letters, so the order in which the rules are tried does not matter.
* `iter n` is the n-th iterate, starting with 00 as in the entry. The iterates are not nested
  (0101 is not a prefix of 01100110), but letter i is the same in every iterate from iterate
  i + 2 on (lemma `iter_stable` of the proof), so `W i`, letter i of iterate i + 2, is letter i of
  the limit of the iterates: `W` is the fixed point A288478, indexed from 0.
* `a n` adds 1 to the 0-based index of the n-th 1 of `W`, so positions count from 1 as in the
  entry; `Nat.nth` counts its argument from 0.
* `main` is the conjunction of both statements of the conjecture: a(n)/n tends to 1 + sqrt(1/2)
  as a limit of real numbers, and -1 < 1 + sqrt(1/2) - a(n)/n < 1 for every n >= 1, with a(n)/n a
  real quotient.
-/

namespace OMA.S_oeis_a288480

open Filter Topology

/-- One pass of StringReplace with the rules 00 -> 0101 and 1 -> 110 over a finite word, read
from the left: where 00 starts it is replaced by 0101, a letter 1 is replaced by 110, and any
other letter is copied. -/
def step : List ℕ → List ℕ
  | 0 :: 0 :: l => 0 :: 1 :: 0 :: 1 :: step l
  | 1 :: l => 1 :: 1 :: 0 :: step l
  | x :: l => x :: step l
  | [] => []

/-- The iterates of the mapping, starting with 00. -/
def iter : ℕ → List ℕ
  | 0 => [0, 0]
  | n + 1 => step (iter n)

/-- A288478 (0-indexed): the fixed point of the mapping, the limit of the iterates. Letter i is
the same in every iterate from iterate i + 2 on, and it is read off iterate i + 2. -/
def W (i : ℕ) : ℕ := (iter (i + 2)).getD i 0

/-- A288480(n): the position, counted from 1 as in the entry, of the n-th 1 of A288478. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => W i = 1) (n - 1) + 1

/-- Kimberling's conjecture: a(n)/n -> 1 + sqrt(1/2), and -1 < 1 + sqrt(1/2) - a(n)/n < 1 for
n >= 1. -/
theorem main : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (𝓝 (1 + Real.sqrt (1 / 2))) ∧
    ∀ n : ℕ, 1 ≤ n → -1 < 1 + Real.sqrt (1 / 2) - (a n : ℝ) / n ∧
      1 + Real.sqrt (1 / 2) - (a n : ℝ) / n < 1 := by
  sorry

end OMA.S_oeis_a288480
