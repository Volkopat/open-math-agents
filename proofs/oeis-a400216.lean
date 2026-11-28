import OMAStatements.S_oeis_a400216
import Mathlib

open OMA.S_oeis_a400216 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a400216.main := by
  have e (c : ℕ) [c.AtLeastTwo] : (OfNat.ofNat c : ℚ⟦X⟧) = C (OfNat.ofNat c) := (map_ofNat C c).symm
  rw [show mk a * ((3*X-1)^2*(9*X^2+4*X+1)) = 81*(X^4*mk a) - 18*(X^3*mk a) - 6*(X^2*mk a) - 2*(X^1*mk a) + mk a by ring]
  ext n
  obtain h | ⟨m, rfl⟩ : n < 8 ∨ ∃ m, n = m+8 := by
    by_cases h : n < 8
    · exact .inl h
    · exact .inr ⟨n-8, by omega⟩
  · interval_cases n <;> simp [e, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, coeff_X, a, V] <;> norm_num
  · simp [e, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, coeff_X, a, V]
    ring
