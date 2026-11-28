import OMAStatements.S_oeis_a098520

namespace OMA.P098520

open PowerSeries OMA.S_oeis_a098520

lemma xder (f : ℚ⟦X⟧) (n : ℕ) : coeff n (X * d⁄dX ℚ f) = (n : ℚ) * coeff n f := by
  rcases n with _ | m
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]
    push_cast
    ring

lemma b_even (k : ℕ) : b (2 * k) = 0 := by
  have h2 : ¬ Odd (2 * k) := by
    rw [Nat.not_odd_iff_even]
    exact even_two_mul k
  unfold b
  rw [if_neg h2]

lemma b_odd (k : ℕ) :
    b (2 * k + 1) = (4 : ℚ) ^ k / ((k.factorial : ℚ) * ((k + 1).factorial : ℚ)) := by
  have h1 : Odd (2 * k + 1) := odd_two_mul_add_one k
  have h3 : (2 * k + 1 - 1) / 2 = k := by omega
  have h5 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  unfold b
  rw [if_pos h1, h3, h5]

lemma fact_ne (k : ℕ) : (k.factorial : ℚ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero k

/-- The Bessel differential equation, written with the operator `x * d/dx`. -/
lemma odeB : X * d⁄dX ℚ (X * d⁄dX ℚ (PowerSeries.mk b))
    = C (16 : ℚ) * (X * (X * PowerSeries.mk b)) + PowerSeries.mk b := by
  ext n
  rw [xder, xder, map_add, coeff_C_mul, coeff_mk]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rw [b_even]
    rcases k with _ | j
    · simp
    · have e : 2 * (j + 1) = 2 * j + 1 + 1 := by ring
      rw [e, coeff_succ_X_mul, coeff_succ_X_mul, coeff_mk, b_even]
      simp
  · rcases k with _ | j
    · simp
    · have e : 2 * (j + 1) + 1 = 2 * j + 1 + 1 + 1 := by ring
      have e2 : 2 * j + 1 + 1 + 1 = 2 * (j + 1) + 1 := by ring
      rw [e, coeff_succ_X_mul, coeff_succ_X_mul, coeff_mk, e2, b_odd, b_odd]
      simp only [Nat.factorial_succ, pow_succ]
      push_cast
      have h0 := fact_ne j
      have p1 : (j : ℚ) + 1 ≠ 0 := by positivity
      have p2 : (j : ℚ) + 1 + 1 ≠ 0 := by positivity
      field_simp
      ring

/-- The differential equation of the exponential generating function. -/
lemma odeA : X * d⁄dX ℚ (X * d⁄dX ℚ (exp ℚ * PowerSeries.mk b))
    = C (2 : ℚ) * (X * (X * d⁄dX ℚ (exp ℚ * PowerSeries.mk b)))
      + exp ℚ * PowerSeries.mk b + X * (exp ℚ * PowerSeries.mk b)
      + C (15 : ℚ) * (X * (X * (exp ℚ * PowerSeries.mk b))) := by
  have hB := odeB
  have hE : d⁄dX ℚ (exp ℚ) = exp ℚ := derivative_exp ℚ
  simp only [Derivation.leibniz, derivative_X, smul_eq_mul, hE, map_add, map_ofNat] at hB ⊢
  linear_combination exp ℚ * hB

lemma recC (k : ℕ) :
    (((k : ℚ) + 2) ^ 2 - 1) * coeff (k + 2) (exp ℚ * PowerSeries.mk b)
      - (2 * (k : ℚ) + 3) * coeff (k + 1) (exp ℚ * PowerSeries.mk b)
      - 15 * coeff k (exp ℚ * PowerSeries.mk b) = 0 := by
  have hc := congrArg (coeff (k + 2)) odeA
  simp only [map_add, coeff_C_mul, coeff_succ_X_mul, coeff_derivative] at hc
  push_cast at hc
  linear_combination hc

end OMA.P098520

open OMA.S_oeis_a098520 OMA.P098520 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a098520.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  have hr := recC k
  have e1 : k + 2 - 1 = k + 1 := by omega
  have e2 : k + 2 - 2 = k := by omega
  unfold a
  rw [e1, e2]
  simp only [Nat.factorial_succ]
  push_cast
  linear_combination ((k.factorial : ℚ) * ((k : ℚ) + 2) * ((k : ℚ) + 1)) * hr
