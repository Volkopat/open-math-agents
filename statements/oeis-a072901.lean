import Mathlib

/-!
# OEIS A072901

Every composite natural number `n` for which `ℚ(√n)` has field discriminant
`4n` is squarefree.

Source: https://oeis.org/A072901
Credit: @wtho704
-/

namespace OMA.S_oeis_a072901

open Polynomial

/-- The subfield of the reals generated over the rationals by `√n`. -/
noncomputable def sqrtField (n : ℕ) : IntermediateField ℚ ℝ :=
  IntermediateField.adjoin ℚ {Real.sqrt (n : ℝ)}

instance (n : ℕ) : NumberField (sqrtField n) where
  to_charZero := inferInstance
  to_finiteDimensional := by
    unfold sqrtField
    refine IntermediateField.adjoin.finiteDimensional ?_
    refine ⟨X ^ 2 - C (n : ℚ), monic_X_pow_sub_C _ (by decide), ?_⟩
    simp [Real.sq_sqrt (Nat.cast_nonneg n)]

theorem main : ∀ n : ℕ, 1 < n → ¬ n.Prime →
    NumberField.discr (sqrtField n) = 4 * (n : ℤ) → Squarefree n := by
  sorry

end OMA.S_oeis_a072901
