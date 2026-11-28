import Mathlib

/-!
# OEIS A285346: the n-th 0 of the fixed point of 0 -> 10, 1 -> 1100 sits at 2n or 2n + 1

Source: https://oeis.org/A285346 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Apr 25 2017), offset 1: positions of 0 in A285345; complement of
A285347. Comment: Conjecture: 2n + 1 - a(n) is in {0,1} for n>=1; see A285351. A285345 is the
fixed point of the morphism 0 -> 10, 1 -> 1100, with offset 1.

Formalization notes:
* Words are lists of the digits 0 and 1. `sigma` is the morphism and `iter k` is its k-th iterate
  applied to the word 1. The fixed point starts with 1, whose image starts with 1 (the image of 0
  does not start with 0), and each iterate extends the one before, so their limit is the fixed
  point: iter 1 = 1100, iter 2 = 110011001010.
* `A285345 i` is the i-th letter (i >= 1) of the fixed point, read off `iter i`, which has more
  than i letters; any later iterate gives the same letter.
* `a n` is the n-th (n >= 1) position i >= 1 with A285345(i) = 0, counted from 1 as in the entry:
  `Nat.nth` of that set of positions at index n - 1.
* `main` states the conjecture in the integers: 2n + 1 - a(n) is 0 or 1 for every n >= 1. The
  pointer to A285351 (defined as 2n + 1 - A285346(n)) adds no condition.
* Controls (proved in the proof file): a(1..8) = 3, 4, 7, 8, 10, 12, 15, 16, the entry's data.
-/

namespace OMA.S_oeis_a285346

/-- The morphism 0 -> 10, 1 -> 1100 (only the letters 0 and 1 occur). -/
def sigma : ℕ → List ℕ
  | 0 => [1, 0]
  | _ => [1, 1, 0, 0]

/-- The k-th iterate of the morphism applied to the word 1. -/
def iter (k : ℕ) : List ℕ := (fun w : List ℕ => w.flatMap sigma)^[k] [1]

/-- A285345(i) for i >= 1: the i-th letter of the fixed point, read off the i-th iterate. -/
def A285345 (i : ℕ) : ℕ := (iter i).getD (i - 1) 0

/-- A285346(n) for n >= 1: the position of the n-th 0 in A285345. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A285345 i = 0) (n - 1)

/-- Kimberling's conjecture: 2n + 1 - a(n) is in {0, 1} for n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (2 * n : ℤ) + 1 - a n ∈ ({0, 1} : Set ℤ) := by
  sorry

end OMA.S_oeis_a285346
