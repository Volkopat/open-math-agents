import Mathlib

/-!
# OEIS A284655: the n-th 1 of the 0-limiting word of 0 -> 1, 1 -> 0110 stays near n sqrt 3

Source: https://oeis.org/A284655 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Apr 07 2017), offset 1: Positions of 1 in A284653; complement of
A284654. Comment: Conjecture: -1 < n*sqrt(3) - a(n) < 2 for n >= 1. A284653 is the 0-limiting
word of the morphism 0 -> 1, 1 -> 0110.

Formalization notes:
* Words are lists of the digits 0 and 1 and `sigma` is the morphism.
* `iter k` applies the morphism 2k times to the word 0: the 0-limiting word is the limit of
  the iterates with an even number of iterations, as the entry A284653 describes, and each such
  iterate extends the one before.
* `A284653 i` is the i-th letter (i >= 1) of the word, read off `iter i`, which has more than
  i letters; any later iterate gives the same letter.
* `a n` is the n-th (n >= 1) position i >= 1 with A284653(i) = 1, counted from 1 as in the
  entry: `Nat.nth` of that set of positions at index n - 1.
* `main` states both strict inequalities in the reals, with `Real.sqrt`, for every n >= 1.
* Controls (proved in the proof file): a(1..8) = 2, 3, 5, 7, 8, 11, 12, 14, the entry's data.
-/

namespace OMA.S_oeis_a284655

/-- The morphism 0 -> 1, 1 -> 0110 (only the letters 0 and 1 occur). -/
def sigma : ℕ → List ℕ
  | 0 => [1]
  | _ => [0, 1, 1, 0]

/-- The (2k)-th iterate of the morphism applied to the word 0. -/
def iter (k : ℕ) : List ℕ :=
  (fun w : List ℕ => (w.flatMap sigma).flatMap sigma)^[k] [0]

/-- A284653(i) for i >= 1: the i-th letter of the word, read off `iter i`. -/
def A284653 (i : ℕ) : ℕ := (iter i).getD (i - 1) 0

/-- A284655(n) for n >= 1: the position of the n-th 1 in A284653. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A284653 i = 1) (n - 1)

/-- Kimberling's conjecture. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    -1 < (n : ℝ) * Real.sqrt 3 - a n ∧ (n : ℝ) * Real.sqrt 3 - a n < 2 := by
  sorry

end OMA.S_oeis_a284655
