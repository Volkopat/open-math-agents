import Mathlib

/-!
# A319053: Exponent of the largest power of 2 appearing in the entries of {{3,1},{1,-1}}^n.

Source: https://oeis.org/A319053
Credit: @bnb9001

The sequence has offset 1 (0, 1, 5, 3, 4, 8, ...). `a n` is the largest 2-adic valuation among the
four entries of `M ^ n`, where `M` is the integer matrix with rows `(3, 1)` and `(1, -1)` (a zero
entry has valuation 0 in Mathlib, which does not affect the maximum).

Conjecture: a(n) appears to equal n - 1 for n not a multiple of 3. Wolfdieter Lang notes that
the conjecture is true.
-/

namespace OMA.S_oeis_a319053

/-- The matrix with rows `(3, 1)` and `(1, -1)`. -/
def M : Matrix (Fin 2) (Fin 2) ℤ := !![3, 1; 1, -1]

/-- A319053: the largest 2-adic valuation of an entry of `M ^ n`. -/
def a (n : ℕ) : ℕ := Finset.univ.sup (fun ij : Fin 2 × Fin 2 => padicValInt 2 ((M ^ n) ij.1 ij.2))

/-- For every `n ≥ 1` not divisible by 3, `a n = n - 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ¬ 3 ∣ n → a n = n - 1 := by
  sorry

end OMA.S_oeis_a319053
