import OMAStatements.S_oeis_a309717
import Mathlib

namespace A309717Proof

open PowerSeries OMA.S_oeis_a309717

lemma series_mul (t : ℤ) : series t * (1 - C t * X - X ^ 2) = X := by
  have hD : (1 - C t * X - X ^ 2 : PowerSeries ℤ) = 1 - C t * X ^ 1 - X ^ 2 := by rw [pow_one]
  rw [hD]
  ext n
  simp only [series, mul_sub, mul_one, map_sub, ← mul_assoc, coeff_mul_X_pow', coeff_mul_C,
    coeff_mk, coeff_X]
  rcases n with _ | _ | m
  · simp [fibPoly]
  · simp [fibPoly]
  · have h1 : 1 ≤ m + 1 + 1 := by omega
    have h2 : 2 ≤ m + 1 + 1 := by omega
    have e1 : m + 1 + 1 - 1 = m + 1 := by omega
    have e2 : m + 1 + 1 - 2 = m := by omega
    have z : ¬ m + 1 + 1 = 1 := by omega
    rw [if_pos h1, if_pos h2, if_neg z, e1, e2]
    rw [show fibPoly t (m + 1 + 1) = t * fibPoly t (m + 1) + fibPoly t m by rw [fibPoly]]
    ring

lemma key : 2 * (series 1 * series 2 * series 3) = series 1 - 2 * series 2 + series 3 := by
  have h1 := series_mul 1
  have h2 := series_mul 2
  have h3 := series_mul 3
  rw [map_one] at h1
  rw [map_ofNat] at h2 h3
  have hP : ((1 - 1 * X - X ^ 2) * (1 - 2 * X - X ^ 2) * (1 - 3 * X - X ^ 2) : PowerSeries ℤ) ≠ 0 := by
    intro h
    have h0 := congrArg constantCoeff h
    simp at h0
  have hz : (2 * (series 1 * series 2 * series 3) - (series 1 - 2 * series 2 + series 3)) *
      ((1 - 1 * X - X ^ 2) * (1 - 2 * X - X ^ 2) * (1 - 3 * X - X ^ 2)) = 0 := by
    linear_combination
      (2 * (series 2 * (1 - 2 * X - X ^ 2)) * (series 3 * (1 - 3 * X - X ^ 2))
        - (1 - 2 * X - X ^ 2) * (1 - 3 * X - X ^ 2)) * h1
      + (2 * X * (series 3 * (1 - 3 * X - X ^ 2)) + 2 * (1 - 1 * X - X ^ 2) * (1 - 3 * X - X ^ 2)) * h2
      + (2 * X ^ 2 - (1 - 1 * X - X ^ 2) * (1 - 2 * X - X ^ 2)) * h3
  rcases mul_eq_zero.mp hz with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hP

lemma tri (n : ℕ) : triangle n 3 = fibPoly 1 n - 2 * fibPoly 2 n + fibPoly 3 n := by
  norm_num [triangle, Finset.sum_range_succ]
  ring

end A309717Proof

open PowerSeries OMA.S_oeis_a309717 in
theorem OMA.solution : type_of% @OMA.S_oeis_a309717.main := by
  intro n _
  have hk := A309717Proof.key
  rw [two_mul, two_mul] at hk
  have h := congrArg (PowerSeries.coeff n) hk
  rw [A309717Proof.tri]
  simp only [a]
  simp only [map_add, map_sub] at h
  have e1 : PowerSeries.coeff n (series 1) = fibPoly 1 n := by simp [series]
  have e2 : PowerSeries.coeff n (series 2) = fibPoly 2 n := by simp [series]
  have e3 : PowerSeries.coeff n (series 3) = fibPoly 3 n := by simp [series]
  rw [e1, e2, e3] at h
  linarith
