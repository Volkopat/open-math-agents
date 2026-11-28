import Mathlib

/-!
# OEIS A285276: the n-th 1 of the 0-limiting word of 0 -> 10, 1 -> 0111 stays near n sqrt 2

Source: https://oeis.org/A285276 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Apr 24 2017), offset 1: Positions of 1 in A285274; complement of
A285275. Comment: Conjecture: -2 < n*sqrt(2) - a(n) < 1 for n>=1. A285274 is the 0-limiting
word of the morphism 0->10, 1-> 0111.

Formalization notes:
* Words are lists of the digits 0 and 1 and `sigma` is the morphism.
* `iter k` applies the morphism 2k times to the word 0: the 0-limiting word is the limit of
  the iterates with an even number of iterations, as the entry A285274 describes, and each such
  iterate extends the one before.
* `A285274 i` is the i-th letter (i >= 1) of the word, read off `iter i`, which has more than
  i letters; any later iterate gives the same letter.
* `a n` is the n-th (n >= 1) position i >= 1 with A285274(i) = 1, counted from 1 as in the
  entry: `Nat.nth` of that set of positions at index n - 1.
* `main` states both strict inequalities in the reals, with `Real.sqrt`, for every n >= 1.
* Controls (proved in the proof file): a(1..8) = 2, 3, 4, 5, 7, 10, 11, 12, the entry's data.
-/

namespace OMA.S_oeis_a285276

/-- The morphism 0 -> 10, 1 -> 0111 (only the letters 0 and 1 occur). -/
def sigma : ℕ → List ℕ
  | 0 => [1, 0]
  | _ => [0, 1, 1, 1]

/-- The (2k)-th iterate of the morphism applied to the word 0. -/
def iter (k : ℕ) : List ℕ :=
  (fun w : List ℕ => (w.flatMap sigma).flatMap sigma)^[k] [0]

/-- A285274(i) for i >= 1: the i-th letter of the word, read off `iter i`. -/
def A285274 (i : ℕ) : ℕ := (iter i).getD (i - 1) 0

/-- A285276(n) for n >= 1: the position of the n-th 1 in A285274. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A285274 i = 1) (n - 1)

/-- Kimberling's conjecture. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    -2 < (n : ℝ) * Real.sqrt 2 - a n ∧ (n : ℝ) * Real.sqrt 2 - a n < 1 := by
  sorry

end OMA.S_oeis_a285276
