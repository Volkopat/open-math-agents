import Mathlib

/-!
# The prime-indicator determinant of OEIS A228616

Source: https://oeis.org/A228616
Credit: @hiattco
-/

namespace OMA.S_oeis_a228616

/-- Convert the zero-based matrix indices to the one-based indices of A228616. -/
def primeMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  fun i j => if Nat.Prime (2 * ((i.val + 1) + (j.val + 1)) - 1) then 1 else 0

theorem main : ∀ n : ℕ, 7 < n → (primeMatrix n).det ≠ 0 := by
  sorry

end OMA.S_oeis_a228616
