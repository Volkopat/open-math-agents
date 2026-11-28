import OMAStatements.S_oeis_a101602

namespace OMA.P_oeis_a101602

open OMA.S_oeis_a101602 PowerSeries

lemma X_mul_c_sq : (X : PowerSeries ℤ) * c ^ 2 = c - 1 := by
  ext n
  cases n with
  | zero => simp [c]
  | succ n =>
    rw [coeff_succ_X_mul, pow_two, coeff_mul]
    simp only [c, coeff_mk, map_sub, coeff_one, Nat.succ_ne_zero, if_false, sub_zero]
    rw [catalan_succ']
    push_cast
    rfl

lemma X_pow_three_mul_c_pow_four :
    (X : PowerSeries ℤ) ^ 3 * c ^ 4 = (c - 1) - 2 * X * c + X := by
  linear_combination (X * (X * c ^ 2 + c - 1) + 1) * X_mul_c_sq

lemma coeff_c_pow_four (n : ℕ) :
    coeff n (c ^ 4) = (catalan (n + 3) : ℤ) - 2 * catalan (n + 2) := by
  have h := congrArg (coeff (n + 3)) X_pow_three_mul_c_pow_four
  rw [coeff_X_pow_mul', if_pos (by omega), show n + 3 - 3 = n by omega] at h
  rw [h]
  have e1 : coeff (n + 3) (2 * X * c) = 2 * (catalan (n + 2) : ℤ) := by
    rw [mul_comm (2 : PowerSeries ℤ) X, mul_assoc, show n + 3 = (n + 2) + 1 from rfl,
      coeff_succ_X_mul]
    simp [c]
    rw [show (2 : PowerSeries ℤ) = C (2 : ℤ) from rfl, coeff_C_mul]
    simp
  rw [map_add, map_sub, map_sub, e1]
  simp [c, coeff_mk, coeff_one, coeff_X]

lemma a_eq (n : ℕ) : a n = 3 ^ n * ((catalan (n + 3) : ℤ) - 2 * catalan (n + 2)) := by
  rw [a, ← map_pow, coeff_rescale, coeff_c_pow_four]

lemma cat_rec (k : ℕ) : ((k : ℚ) + 2) * catalan (k + 1) = 2 * (2 * k + 1) * catalan k := by
  have h1 := succ_mul_catalan_eq_centralBinom (k + 1)
  have h2 := succ_mul_catalan_eq_centralBinom k
  have h3 := Nat.succ_mul_centralBinom_succ k
  have h4 : ((k + 1 : ℕ) : ℚ) * ((k + 1 + 1 : ℕ) * catalan (k + 1)) =
      ((k + 1 : ℕ) : ℚ) * (2 * (2 * k + 1) * catalan k) := by
    have : (k + 1) * ((k + 1 + 1) * catalan (k + 1)) =
        (k + 1) * (2 * (2 * k + 1) * catalan k) := by
      rw [h1, h3, ← h2]; ring
    exact_mod_cast this
  have hk : ((k + 1 : ℕ) : ℚ) ≠ 0 := by positivity
  have := mul_left_cancel₀ hk h4
  push_cast at this
  linarith

end OMA.P_oeis_a101602

theorem OMA.solution : type_of% @OMA.S_oeis_a101602.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  simp only [OMA.P_oeis_a101602.a_eq]
  have r3 := OMA.P_oeis_a101602.cat_rec (m + 2)
  have r4 := OMA.P_oeis_a101602.cat_rec (m + 3)
  have r5 := OMA.P_oeis_a101602.cat_rec (m + 4)
  have key : (((m + 2 : ℕ) : ℚ) + 4) * (3 ^ (m + 2) * ((catalan (m + 2 + 3) : ℚ) -
      2 * catalan (m + 2 + 2))) - 6 * (3 * ((m + 2 : ℕ) : ℚ) + 7) *
      (3 ^ (m + 1) * ((catalan (m + 1 + 3) : ℚ) - 2 * catalan (m + 1 + 2))) +
      36 * (2 * ((m + 2 : ℕ) : ℚ) + 1) * (3 ^ m * ((catalan (m + 3) : ℚ) -
      2 * catalan (m + 2))) = 0 := by
    push_cast at r3 r4 r5 ⊢
    have h3 : (catalan (m + 3) : ℚ) = 2 * (2 * (m + 2) + 1) * catalan (m + 2) / (m + 2 + 2) := by
      rw [eq_div_iff (by positivity)]; linarith
    have h4 : (catalan (m + 4) : ℚ) = 2 * (2 * (m + 3) + 1) * catalan (m + 3) / (m + 3 + 2) := by
      rw [eq_div_iff (by positivity)]; linarith
    have h5 : (catalan (m + 5) : ℚ) = 2 * (2 * (m + 4) + 1) * catalan (m + 4) / (m + 4 + 2) := by
      rw [eq_div_iff (by positivity)]; linarith
    rw [show m + 2 + 3 = m + 5 by omega, show m + 2 + 2 = m + 4 by omega,
      show m + 1 + 3 = m + 4 by omega, show m + 1 + 2 = m + 3 by omega]
    rw [h5, h4, h3]
    field_simp
    ring
  exact_mod_cast key
