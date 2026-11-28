import OMAStatements.S_oeis_a359643

namespace OMA.P359643

open PowerSeries OMA.S_oeis_a359643

lemma fact_ne (k : ℕ) : (k.factorial : ℚ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero k

/-- The coefficients binomial(4k,k) / k!. -/
def b (k : ℕ) : ℚ := ((4 * k).choose k : ℚ) / (k.factorial : ℚ)

lemma choose_eq (k : ℕ) : ((4 * k).choose k : ℚ)
    = ((4 * k).factorial : ℚ) / ((k.factorial : ℚ) * ((3 * k).factorial : ℚ)) := by
  have hk : k ≤ 4 * k := by omega
  have e : 4 * k - k = 3 * k := by omega
  rw [Nat.cast_choose ℚ hk, e]

lemma fact4 (k : ℕ) : ((4 * (k + 1)).factorial : ℚ)
    = (4 * (k : ℚ) + 4) * (4 * (k : ℚ) + 3) * (4 * (k : ℚ) + 2) * (4 * (k : ℚ) + 1)
      * ((4 * k).factorial : ℚ) := by
  have e : 4 * (k + 1) = 4 * k + 1 + 1 + 1 + 1 := by ring
  rw [e]
  simp only [Nat.factorial_succ]
  push_cast
  ring

lemma fact3 (k : ℕ) : ((3 * (k + 1)).factorial : ℚ)
    = (3 * (k : ℚ) + 3) * (3 * (k : ℚ) + 2) * (3 * (k : ℚ) + 1) * ((3 * k).factorial : ℚ) := by
  have e : 3 * (k + 1) = 3 * k + 1 + 1 + 1 := by ring
  rw [e]
  simp only [Nat.factorial_succ]
  push_cast
  ring

lemma b_succ (k : ℕ) :
    3 * (3 * (k : ℚ) + 1) * (3 * (k : ℚ) + 2) * ((k : ℚ) + 1) ^ 2 * b (k + 1)
      = 4 * (4 * (k : ℚ) + 1) * (4 * (k : ℚ) + 2) * (4 * (k : ℚ) + 3) * b k := by
  unfold b
  rw [choose_eq (k + 1), choose_eq k, fact4, fact3, Nat.factorial_succ]
  push_cast
  have h0 := fact_ne k
  have h3 := fact_ne (3 * k)
  have h4 := fact_ne (4 * k)
  have p1 : (k : ℚ) + 1 ≠ 0 := by positivity
  have p2 : 3 * (k : ℚ) + 3 ≠ 0 := by positivity
  have p3 : 3 * (k : ℚ) + 2 ≠ 0 := by positivity
  have p4 : 3 * (k : ℚ) + 1 ≠ 0 := by positivity
  field_simp

lemma coeff_theta (f : PowerSeries ℚ) (n : ℕ) :
    coeff n (X * d⁄dX ℚ f) = (n : ℚ) * coeff n f := by
  rcases n with _ | m
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

/-- The differential equation of the series with coefficients binomial(4k,k) / k!. -/
lemma odeB :
    C (27 : ℚ) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ (PowerSeries.mk b)))))
      + C (6 : ℚ) * (X * d⁄dX ℚ (X * d⁄dX ℚ (PowerSeries.mk b)))
      - (C (27 : ℚ) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ (PowerSeries.mk b))))
      + C (256 : ℚ) * (X * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ (PowerSeries.mk b)))))
      + C (384 : ℚ) * (X * (X * d⁄dX ℚ (X * d⁄dX ℚ (PowerSeries.mk b))))
      + C (176 : ℚ) * (X * (X * d⁄dX ℚ (PowerSeries.mk b)))
      + C (24 : ℚ) * (X * (PowerSeries.mk b))) = 0 := by
  ext n
  rcases n with _ | m
  · simp
  · have h := b_succ m
    simp only [map_add, map_sub, map_zero, coeff_C_mul, coeff_theta, coeff_succ_X_mul,
      coeff_derivative, coeff_mk]
    push_cast
    linear_combination h

/-- The differential equation of the product with the exponential series. -/
lemma odeA :
    C (27 : ℚ) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ (exp ℚ * PowerSeries.mk b)))))
      + C (6 : ℚ) * (X * d⁄dX ℚ (X * d⁄dX ℚ (exp ℚ * PowerSeries.mk b)))
      + C (930 : ℚ) * (X * (X * (X * d⁄dX ℚ (X * d⁄dX ℚ (exp ℚ * PowerSeries.mk b)))))
      + C (1779 : ℚ) * (X * (X * (X * d⁄dX ℚ (exp ℚ * PowerSeries.mk b))))
      + C (930 : ℚ) * (X * (X * (exp ℚ * PowerSeries.mk b)))
      + C (283 : ℚ) * (X * (X * (X * (X * (exp ℚ * PowerSeries.mk b)))))
      - (C (27 : ℚ) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ (exp ℚ * PowerSeries.mk b))))
      + C (364 : ℚ) * (X * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ (exp ℚ * PowerSeries.mk b)))))
      + C (465 : ℚ) * (X * (X * d⁄dX ℚ (X * d⁄dX ℚ (exp ℚ * PowerSeries.mk b))))
      + C (215 : ℚ) * (X * (X * d⁄dX ℚ (exp ℚ * PowerSeries.mk b)))
      + C (30 : ℚ) * (X * (exp ℚ * PowerSeries.mk b))
      + C (876 : ℚ) * (X * (X * (X * (X * d⁄dX ℚ (exp ℚ * PowerSeries.mk b)))))
      + C (1287 : ℚ) * (X * (X * (X * (exp ℚ * PowerSeries.mk b))))) = 0 := by
  have hB := odeB
  have hE : d⁄dX ℚ (exp ℚ) = exp ℚ := derivative_exp ℚ
  simp only [Derivation.leibniz, derivative_X, smul_eq_mul, hE, map_add, map_ofNat,
    Derivation.map_one_eq_zero, map_zero] at hB ⊢
  linear_combination exp ℚ * hB

/-- The coefficients of the product with the exponential series. -/
noncomputable def c (m : ℕ) : ℚ := coeff m (exp ℚ * PowerSeries.mk b)

lemma recD (m : ℕ) :
    (27 * (m : ℚ) ^ 4 + 405 * (m : ℚ) ^ 3 + 2274 * (m : ℚ) ^ 2 + 5664 * (m : ℚ) + 5280) * c (m + 4)
      + (-364 * (m : ℚ) ^ 3 - 3741 * (m : ℚ) ^ 2 - 12833 * (m : ℚ) - 14688) * c (m + 3)
      + (930 * (m : ℚ) ^ 2 + 5499 * (m : ℚ) + 8208) * c (m + 2)
      + (-876 * (m : ℚ) - 2163) * c (m + 1)
      + (283) * c m = 0 := by
  have hc := congrArg (coeff (m + 4)) odeA
  simp only [map_add, map_sub, map_zero, coeff_C_mul, coeff_succ_X_mul, coeff_derivative] at hc
  push_cast at hc
  unfold c
  linear_combination hc

lemma a_eq (n : ℕ) : ((a n : ℤ) : ℚ) = (n.factorial : ℚ) * c n := by
  unfold c a
  rw [mul_comm (exp ℚ), coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,
    Finset.mul_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro k hk
  have hk2 : k ≤ n := by
    have h := Finset.mem_range.mp hk
    omega
  have h1 := fact_ne k
  have h2 := fact_ne (n - k)
  have h3 := fact_ne n
  rw [coeff_mk, coeff_exp, Nat.cast_choose ℚ hk2]
  simp only [b, eq_ratCast, Rat.cast_div, Rat.cast_one, Rat.cast_natCast]
  field_simp

end OMA.P359643

open OMA.S_oeis_a359643 OMA.P359643 in
theorem OMA.solution : type_of% @OMA.S_oeis_a359643.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
  have e1 : m + 5 - 1 = m + 4 := by omega
  have e2 : m + 5 - 2 = m + 3 := by omega
  have e3 : m + 5 - 3 = m + 2 := by omega
  have e4 : m + 5 - 4 = m + 1 := by omega
  have e5 : m + 5 - 5 = m := by omega
  rw [e1, e2, e3, e4, e5]
  apply Int.cast_injective (α := ℚ)
  push_cast
  rw [a_eq, a_eq, a_eq, a_eq, a_eq, a_eq]
  have h1 := recD (m + 1)
  have h0 := recD m
  simp only [Nat.add_assoc, Nat.reduceAdd] at h1
  push_cast at h1
  simp only [Nat.factorial_succ]
  push_cast
  linear_combination
    (27 * (m.factorial : ℚ) * ((m : ℚ) + 1) * ((m : ℚ) + 2) * ((m : ℚ) + 3) * ((m : ℚ) + 4)) * h1
    + (391 * (m.factorial : ℚ) * ((m : ℚ) + 1) * ((m : ℚ) + 2) * ((m : ℚ) + 3)) * h0
