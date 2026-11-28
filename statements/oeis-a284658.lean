import Mathlib

/-!
# OEIS A284658: the n-th 1 of the 1-limiting word of 0 -> 1, 1 -> 0110 stays near n sqrt 3

Source: https://oeis.org/A284658 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Apr 08 2017), offset 1: Positions of 1 in A284656; complement of
A284657. Comment: Conjecture: -1 < n*sqrt(3) - a(n) < 2 for n >= 1. A284656 is the 1-limiting
word of the morphism 0 -> 1, 1 -> 0110.

Formalization notes:
* Words are lists of the digits 0 and 1 and `sigma` is the morphism.
* `iter k` applies the morphism 2k times to the word 1: the 1-limiting word is the limit of
  the iterates with an even number of iterations, as the entry A284656 describes, and each such
  iterate extends the one before.
* `A284656 i` is the i-th letter (i >= 1) of the word, read off `iter i`, which has more than
  i letters; any later iterate gives the same letter.
* `a n` is the n-th (n >= 1) position i >= 1 with A284656(i) = 1, counted from 1 as in the
  entry: `Nat.nth` of that set of positions at index n - 1.
* `main` states both strict inequalities in the reals, with `Real.sqrt`, for every n >= 1.
* Controls (proved in the proof file): a(1..8) = 1, 3, 4, 7, 8, 10, 12, 13, the entry's data.
-/

namespace OMA.S_oeis_a284658

/-- The morphism 0 -> 1, 1 -> 0110 (only the letters 0 and 1 occur). -/
def sigma : ℕ → List ℕ
  | 0 => [1]
  | _ => [0, 1, 1, 0]

/-- The (2k)-th iterate of the morphism applied to the word 1. -/
def iter (k : ℕ) : List ℕ :=
  (fun w : List ℕ => (w.flatMap sigma).flatMap sigma)^[k] [1]

/-- A284656(i) for i >= 1: the i-th letter of the word, read off `iter i`. -/
def A284656 (i : ℕ) : ℕ := (iter i).getD (i - 1) 0

/-- A284658(n) for n >= 1: the position of the n-th 1 in A284656. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A284656 i = 1) (n - 1)

/-- Kimberling's conjecture. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    -1 < (n : ℝ) * Real.sqrt 3 - a n ∧ (n : ℝ) * Real.sqrt 3 - a n < 2 := by
  sorry

end OMA.S_oeis_a284658
