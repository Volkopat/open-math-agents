import Mathlib

/-!
# OEIS A285353: the n-th 0 of A285351 sits at 3n - 3 or 3n - 2

Source: https://oeis.org/A285353 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Apr 25 2017), offset 1: positions of 0 in A285351; complement of
A285354. Comment: Conjecture: 3n - 2 - a(n) is in {0,1} for n>=1. A285351 (offset 1) is
a(n) = 2n + 1 - A285346(n), where A285346 lists the positions of 0 in A285345, the fixed point
of the morphism 0 -> 10, 1 -> 1100.

Formalization notes:
* Words are lists of the digits 0 and 1. `sigma` is the morphism and `iter k` is its k-th iterate
  applied to the word 1. The fixed point starts with 1, whose image starts with 1 (the image of 0
  does not start with 0), and each iterate extends the one before, so their limit is the fixed
  point. `A285345 i` is its i-th letter (i >= 1), read off `iter i`, which has more than i
  letters; any later iterate gives the same letter.
* `A285346 n` is the n-th (n >= 1) position i >= 1 with A285345(i) = 0 (`Nat.nth` at index
  n - 1), `A285351 n` is 2n + 1 - A285346(n) in the integers, and `a n` is the n-th (n >= 1)
  position i >= 1 with A285351(i) = 0, all counted from 1 as in the entries.
* `main` states the conjecture in the integers: 3n - 2 - a(n) is 0 or 1 for every n >= 1.
* Controls (proved in the proof file): a(1..8) = 1, 3, 7, 9, 13, 16, 19, 21, the entry's data.
-/

namespace OMA.S_oeis_a285353

/-- The morphism 0 -> 10, 1 -> 1100 (only the letters 0 and 1 occur). -/
def sigma : ℕ → List ℕ
  | 0 => [1, 0]
  | _ => [1, 1, 0, 0]

/-- The k-th iterate of the morphism applied to the word 1. -/
def iter (k : ℕ) : List ℕ := (fun w : List ℕ => w.flatMap sigma)^[k] [1]

/-- A285345(i) for i >= 1: the i-th letter of the fixed point, read off the i-th iterate. -/
def A285345 (i : ℕ) : ℕ := (iter i).getD (i - 1) 0

/-- A285346(n) for n >= 1: the position of the n-th 0 in A285345. -/
noncomputable def A285346 (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A285345 i = 0) (n - 1)

/-- A285351(n) = 2n + 1 - A285346(n). -/
noncomputable def A285351 (n : ℕ) : ℤ := 2 * n + 1 - A285346 n

/-- A285353(n) for n >= 1: the position of the n-th 0 in A285351. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A285351 i = 0) (n - 1)

/-- Kimberling's conjecture: 3n - 2 - a(n) is in {0, 1} for n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (3 * n : ℤ) - 2 - a n ∈ ({0, 1} : Set ℤ) := by
  sorry

end OMA.S_oeis_a285353
