import OMAStatements.S_oeis_a144135
import Mathlib

/-!
Credit: @ivillar
Proof: write R(k) = (k+2)a(k+2) - 16(k+3)a(k+1) + (k+4)a(k), which vanishes by the three-term
recurrence. Then (m+4)*(a(m+4) - 32a(m+3) + 258a(m+2) - 32a(m+1) + a(m)) = R(m+2) - 16R(m+1) + R(m)
(this is the coefficient form of (g*D^2)' = D*(D*g' + 2*D'*g) with D = 1 - 16x + x^2), which gives
Barker's recurrence; with the first four terms it gives (Sum a(n) x^n) * D^2 = 1.
-/

namespace OMAA144135Helpers
open PowerSeries OMA.S_oeis_a144135

theorem rec3 (m j k : ℕ) (hj : j = m + 2) (hk : k = m + 1) :
    ((m : ℚ) + 2) * a j = 16 * ((m : ℚ) + 3) * a k - ((m : ℚ) + 4) * a m := by
  subst hj hk
  have h : a (m + 2) = (2 * 8 * ((m : ℚ) + 1 + 2) * a (m + 1) - ((m : ℚ) + 2 * 2) * a m) /
      ((m : ℚ) + 2) := rfl
  rw [h]
  have : (m : ℚ) + 2 ≠ 0 := by positivity
  field_simp
  ring

theorem rec4 (m : ℕ) : a (m + 4) = 32 * a (m + 3) - 258 * a (m + 2) + 32 * a (m + 1) - a m := by
  have r2 := rec3 (m + 2) (m + 4) (m + 3) (by omega) (by omega)
  have r1 := rec3 (m + 1) (m + 3) (m + 2) (by omega) (by omega)
  have r0 := rec3 m (m + 2) (m + 1) (by omega) (by omega)
  push_cast at r2 r1 r0
  have hm : (m : ℚ) + 4 ≠ 0 := by positivity
  apply mul_left_cancel₀ hm
  linear_combination r2 - 16 * r1 + r0

theorem coeff_mk_mul_X_pow (f : ℕ → ℚ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * X ^ k) = if k ≤ n then f (n - k) else 0 := by
  rw [coeff_mul_X_pow', coeff_mk]

theorem coeff_mk_mul_C_X_pow (f : ℕ → ℚ) (r : ℚ) (n k : ℕ) :
    coeff n (PowerSeries.mk f * (C r * X ^ k)) = r * (if k ≤ n then f (n - k) else 0) := by
  rw [mul_left_comm, coeff_C_mul, coeff_mk_mul_X_pow]

theorem coeff_at (f : ℕ → ℚ) (n k j : ℕ) (h : n = j + k) :
    coeff n (PowerSeries.mk f * X ^ k) = f j := by
  rw [coeff_mk_mul_X_pow, if_pos (by omega), show n - k = j by omega]

theorem coeff_at_C (f : ℕ → ℚ) (r : ℚ) (n k j : ℕ) (h : n = j + k) :
    coeff n (PowerSeries.mk f * (C r * X ^ k)) = r * f j := by
  rw [mul_left_comm, coeff_C_mul, coeff_at f n k j h]

theorem series : PowerSeries.mk a * (X ^ 2 - 16 * X + 1) ^ 2 = (1 : PowerSeries ℚ) := by
  ext n
  have hD : ((X ^ 2 - 16 * X + 1) ^ 2 : PowerSeries ℚ) =
      X ^ 4 - C 32 * X ^ 3 + C 258 * X ^ 2 - C 32 * X ^ 1 + X ^ 0 := by
    rw [map_ofNat C 32, map_ofNat C 258]
    ring
  rw [hD, coeff_one]
  have v0 : a 0 = 1 := rfl
  have v1 : a 1 = 32 := by norm_num [a, gegenbauer]
  have v2 : a 2 = 766 := by norm_num [a, gegenbauer]
  have v3 : a 3 = 16288 := by norm_num [a, gegenbauer]
  rcases Nat.lt_or_ge n 4 with h | h
  · simp only [mul_add, mul_sub, map_add, map_sub, coeff_mk_mul_C_X_pow, coeff_mk_mul_X_pow]
    interval_cases n
    · norm_num [v0]
    · norm_num [v0, v1]
    · norm_num [v0, v1, v2]
    · norm_num [v0, v1, v2, v3]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    simp only [mul_add, mul_sub, map_add, map_sub]
    rw [coeff_at a (m + 4) 4 m (by omega), coeff_at_C a 32 (m + 4) 3 (m + 1) (by omega),
      coeff_at_C a 258 (m + 4) 2 (m + 2) (by omega), coeff_at_C a 32 (m + 4) 1 (m + 3) (by omega),
      coeff_at a (m + 4) 0 (m + 4) (by omega), if_neg (by omega), rec4 m]
    ring

end OMAA144135Helpers

theorem OMA.solution : type_of% @OMA.S_oeis_a144135.main := by
  refine ⟨?_, ?_⟩
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 4 := ⟨n - 4, by omega⟩
    rw [show m + 4 - 1 = m + 3 by omega, show m + 4 - 2 = m + 2 by omega,
      show m + 4 - 3 = m + 1 by omega, show m + 4 - 4 = m by omega]
    exact OMAA144135Helpers.rec4 m
  · rw [mul_assoc, OMAA144135Helpers.series, mul_one]
