import OMAStatements.S_oeis_a298024
import Mathlib

/-!
# A298024: the recurrence of the expansion of `(x⁴+3x³+6x²+3x+1) / ((1-x)(1-x³))`

Multiplying `G` by `(1 - X)(1 - X³) = 1 - X - X³ + X⁴` gives back the numerator, a polynomial of
degree `4`.  Comparing the coefficients of `Xⁿ` for `n > 4` gives
`a n - a (n-1) - a (n-3) + a (n-4) = 0`.
-/

open OMA.S_oeis_a298024 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a298024.main := by
  have hG : G * ((1 - X) * (1 - X ^ 3)) = 1 + 3 * X + 6 * X ^ 2 + 3 * X ^ 3 + X ^ 4 := by
    unfold G
    rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by simp), mul_one]
  have el : ∀ S : PowerSeries ℚ, S * ((1 - X) * (1 - X ^ 3)) =
      S * X ^ 0 - S * X ^ 1 - S * X ^ 3 + S * X ^ 4 := by
    intro S
    ring
  have er : (1 + 3 * X + 6 * X ^ 2 + 3 * X ^ 3 + X ^ 4 : PowerSeries ℚ) =
      X ^ 0 * C 1 + X ^ 1 * C 3 + X ^ 2 * C 6 + X ^ 3 * C 3 + X ^ 4 * C 1 := by
    simp only [map_one, map_ofNat]
    ring
  rw [el, er] at hG
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have h := congrArg (coeff (k + 5)) hG
  simp only [map_add, map_sub, coeff_mul_C, coeff_mul_X_pow', coeff_X_pow] at h
  simp at h
  have e1 : k + 5 - 1 = k + 4 := rfl
  have e3 : k + 5 - 3 = k + 2 := rfl
  have e4 : k + 5 - 4 = k + 1 := rfl
  rw [e1, e3, e4]
  unfold a
  linarith
