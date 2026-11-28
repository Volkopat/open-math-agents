import Mathlib

/-!
# OEIS A284941: the n-th 1 of the fixed point of 0 -> 01, 1 -> 1101 stays near n sqrt 2

Source: https://oeis.org/A284941 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Apr 18 2017), offset 1: positions of 1 in A284939; complement of
A080580. Comment: Conjecture: -1 < n*sqrt(2) - a(n) < 2 for n >= 1. A284939 is the fixed point
of the morphism 0 -> 01, 1 -> 1101, starting with 0, with offset 1.

Formalization notes:
* Words are lists of the digits 0 and 1. `sigma` is the morphism and `iter k` is its k-th iterate
  applied to the word 0, so iter 1 = 01, iter 2 = 011101, and each iterate extends the one before.
* `A284939 i` is the i-th letter (i >= 1) of the fixed point, read off `iter i`, which has more
  than i letters; any later iterate gives the same letter.
* `a n` is the n-th (n >= 1) position i >= 1 with A284939(i) = 1, counted from 1 as in the entry:
  `Nat.nth` of that set of positions at index n - 1.
* `main` states both strict inequalities in the reals, with `Real.sqrt 2`, for every n >= 1.
* Controls (proved in the proof file): a(1..8) = 2, 3, 4, 6, 7, 8, 10, 11, the entry's data.
-/

namespace OMA.S_oeis_a284941

/-- The morphism 0 -> 01, 1 -> 1101 (only the letters 0 and 1 occur). -/
def sigma : ℕ → List ℕ
  | 0 => [0, 1]
  | _ => [1, 1, 0, 1]

/-- The k-th iterate of the morphism applied to the word 0. -/
def iter (k : ℕ) : List ℕ := (fun w : List ℕ => w.flatMap sigma)^[k] [0]

/-- A284939(i) for i >= 1: the i-th letter of the fixed point, read off the i-th iterate. -/
def A284939 (i : ℕ) : ℕ := (iter i).getD (i - 1) 0

/-- A284941(n) for n >= 1: the position of the n-th 1 in A284939. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A284939 i = 1) (n - 1)

/-- Kimberling's conjecture: -1 < n sqrt 2 - a(n) < 2 for n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    -1 < (n : ℝ) * Real.sqrt 2 - a n ∧ (n : ℝ) * Real.sqrt 2 - a n < 2 := by
  sorry

end OMA.S_oeis_a284941
