import Mathlib

/-!
# OEIS A284937: the n-th 1 of the fixed point of 0 -> 01, 1 -> 1100 sits at 2n, 2n-1 or 2n-2

Source: https://oeis.org/A284937 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Clark Kimberling, Apr 18 2017), offset 1: positions of 1 in A284935; complement of
A284936. Comment: Conjecture: 2n - a(n) is in {0,1,2} for n >= 1. A284935 is the fixed point of
the morphism 0 -> 01, 1 -> 1100 (starting with 0), with offset 1.

Formalization notes:
* Words are lists of the digits 0 and 1. `sigma` is the morphism and `iter k` is its k-th iterate
  applied to the word 0, so iter 1 = 01, iter 2 = 011100, and each iterate extends the one before.
* `A284935 i` is the i-th letter (i >= 1) of the fixed point, read off `iter i`, which has more
  than i letters; any later iterate gives the same letter.
* `a n` is the n-th (n >= 1) position i >= 1 with A284935(i) = 1, counted from 1 as in the entry:
  `Nat.nth` of that set of positions at index n - 1.
* `main` states the conjecture in the integers: 2n - a(n) is 0, 1 or 2 for every n >= 1.
* Controls (proved in the proof file): a(1..8) = 2, 3, 4, 7, 8, 11, 12, 16, the entry's data.
-/

namespace OMA.S_oeis_a284937

/-- The morphism 0 -> 01, 1 -> 1100 (only the letters 0 and 1 occur). -/
def sigma : ℕ → List ℕ
  | 0 => [0, 1]
  | _ => [1, 1, 0, 0]

/-- The k-th iterate of the morphism applied to the word 0. -/
def iter (k : ℕ) : List ℕ := (fun w : List ℕ => w.flatMap sigma)^[k] [0]

/-- A284935(i) for i >= 1: the i-th letter of the fixed point, read off the i-th iterate. -/
def A284935 (i : ℕ) : ℕ := (iter i).getD (i - 1) 0

/-- A284937(n) for n >= 1: the position of the n-th 1 in A284935. -/
noncomputable def a (n : ℕ) : ℕ := Nat.nth (fun i => 1 ≤ i ∧ A284935 i = 1) (n - 1)

/-- Kimberling's conjecture: 2n - a(n) is in {0, 1, 2} for n >= 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n → (2 * n : ℤ) - a n ∈ ({0, 1, 2} : Set ℤ) := by
  sorry

end OMA.S_oeis_a284937
