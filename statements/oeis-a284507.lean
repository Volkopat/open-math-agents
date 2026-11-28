import Mathlib

/-!
# OEIS A284507: the n-th 1 of the fixed point of 0 -> 1, 1 -> 1100 stays near n sqrt 3

Source: https://oeis.org/A284507 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Apr 04 2017), offset 1: Positions of 1 in A284505; complement of
A284506. Comment: Conjecture: -2 < n*sqrt(3) - a(n) < 4 for n >= 1. A284505 is the fixed point
of the morphism 0->1, 1->1100.

Formalization notes:
* Words are lists of the digits 0 and 1 and `sigma` is the morphism.
* `iter k` is the k-th iterate of the morphism applied to the word 1. The fixed point starts
  with 1, whose image starts with 1 (the image of 0 does not start with 0), and each iterate
  extends the one before, so their limit is the fixed point.
* `A284505 i` is the i-th letter (i >= 1) of the word, read off `iter i`, which has more than
  i letters; any later iterate gives the same letter.
* `a n` is the n-th (n >= 1) position i >= 1 with A284505(i) = 1, counted from 1 as in the
  entry: `Nat.nth` of that set of positions at index n - 1.
* `main` states both strict inequalities in the reals, with `Real.sqrt`, for every n >= 1.
* Controls (proved in the proof file): a(1..8) = 1, 2, 5, 6, 9, 10, 11, 12, the entry's data.
-/

namespace OMA.S_oeis_a284507

/-- The morphism 0 -> 1, 1 -> 1100 (only the letters 0 and 1 occur). -/
def sigma : ℕ → List ℕ
  | 0 => [1]
  | _ => [1, 1, 0, 0]

/-- The k-th iterate of the morphism applied to the word 1. -/
def iter (k : ℕ) : List ℕ := (fun w : List ℕ => w.flatMap sigma)^[k] [1]

/-- A284505(i) for i >= 1: the i-th letter of the word, read off `iter i`. -/
def A284505 (i : ℕ) : ℕ := (iter i).getD (i - 1) 0

/-- A284507(n) for n >= 1: the position of the n-th 1 in A284505. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A284505 i = 1) (n - 1)

/-- Kimberling's conjecture. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    -2 < (n : ℝ) * Real.sqrt 3 - a n ∧ (n : ℝ) * Real.sqrt 3 - a n < 4 := by
  sorry

end OMA.S_oeis_a284507
