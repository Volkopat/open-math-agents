import OMAStatements.S_oeis_a119975

namespace OMA.P119975

open PowerSeries OMA.S_oeis_a119975

/-- The coefficient of x^n in the sum of the two Bessel series. -/
def bb (n : ℕ) : ℚ := b0 n + b1 n

lemma mk_bb : PowerSeries.mk b0 + PowerSeries.mk b1 = PowerSeries.mk bb := by
  ext n
  simp [bb]

lemma bb_even (k : ℕ) : bb (2 * k) = (2 : ℚ) ^ k / ((k.factorial : ℚ) ^ 2) := by
  have h1 : Even (2 * k) := even_two_mul k
  have h2 : ¬ Odd (2 * k) := by
    rw [Nat.not_odd_iff_even]
    exact h1
  have h3 : 2 * k / 2 = k := by omega
  unfold bb b0 b1
  rw [if_pos h1, if_neg h2, h3, add_zero]

lemma bb_odd (k : ℕ) :
    bb (2 * k + 1) = (2 : ℚ) ^ k / ((k.factorial : ℚ) * ((k + 1).factorial : ℚ)) := by
  have h1 : Odd (2 * k + 1) := odd_two_mul_add_one k
  have h2 : ¬ Even (2 * k + 1) := by
    rw [Nat.not_even_iff_odd]
    exact h1
  have h3 : (2 * k + 1 - 1) / 2 = k := by omega
  have h5 : (2 * k + 1 + 1) / 2 = k + 1 := by omega
  unfold bb b0 b1
  rw [if_pos h1, if_neg h2, h3, h5, zero_add]

lemma fact_ne (k : ℕ) : (k.factorial : ℚ) ≠ 0 := by
  exact_mod_cast Nat.factorial_ne_zero k

/-- The coefficients of the differential expression for a general power series. -/
lemma coefB (s : ℕ → ℚ) (m : ℕ) :
    coeff (m + 3) (C (2 : ℚ) * (X * (X * d⁄dX ℚ (X * d⁄dX ℚ (PowerSeries.mk s))))
      + C (8 : ℚ) * (X * (X * PowerSeries.mk s)) + C (2 : ℚ) * (X * PowerSeries.mk s)
      - (X * d⁄dX ℚ (X * d⁄dX ℚ (PowerSeries.mk s)) + X * d⁄dX ℚ (PowerSeries.mk s)
        + C (16 : ℚ) * (X * (X * (X * PowerSeries.mk s)))))
    = 2 * ((m : ℚ) + 2) ^ 2 * s (m + 2) + 8 * s (m + 1) + 2 * s (m + 2)
      - ((m : ℚ) + 3) ^ 2 * s (m + 3) - ((m : ℚ) + 3) * s (m + 3) - 16 * s m := by
  simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_derivative, coeff_mk]
  push_cast
  ring

/-- The differential equation of the sum of the two Bessel series. -/
lemma odeB : C (2 : ℚ) * (X * (X * d⁄dX ℚ (X * d⁄dX ℚ (PowerSeries.mk bb))))
      + C (8 : ℚ) * (X * (X * PowerSeries.mk bb)) + C (2 : ℚ) * (X * PowerSeries.mk bb)
      - (X * d⁄dX ℚ (X * d⁄dX ℚ (PowerSeries.mk bb)) + X * d⁄dX ℚ (PowerSeries.mk bb)
        + C (16 : ℚ) * (X * (X * (X * PowerSeries.mk bb)))) = 0 := by
  have v0 : bb 0 = 1 := by
    have h := bb_even 0
    norm_num at h
    exact h
  have v1 : bb 1 = 1 := by
    have h := bb_odd 0
    norm_num at h
    exact h
  have v2 : bb 2 = 2 := by
    have h := bb_even 1
    norm_num at h
    exact h
  ext n
  rcases n with _ | _ | _ | m
  · simp
  · simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_zero_X_mul,
      coeff_derivative, coeff_mk]
    norm_num [v0, v1]
  · simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_zero_X_mul,
      coeff_derivative, coeff_mk]
    norm_num [v0, v1, v2]
  · rw [coefB, map_zero]
    have hk := fact_ne
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩
    · have e3 : 2 * k + 3 = 2 * (k + 1) + 1 := by ring
      have e2 : 2 * k + 2 = 2 * (k + 1) := by ring
      rw [e3, e2, bb_odd, bb_even, bb_odd, bb_even]
      simp only [Nat.factorial_succ, pow_succ]
      push_cast
      have h0 := hk k
      have p1 : (k : ℚ) + 1 ≠ 0 := by positivity
      have p2 : (k : ℚ) + 1 + 1 ≠ 0 := by positivity
      field_simp
      ring
    · have e3 : 2 * k + 1 + 3 = 2 * (k + 2) := by ring
      have e2 : 2 * k + 1 + 2 = 2 * (k + 1) + 1 := by ring
      have e1 : 2 * k + 1 + 1 = 2 * (k + 1) := by ring
      rw [e3, e2, e1, bb_odd, bb_even, bb_odd, bb_even]
      simp only [Nat.factorial_succ, pow_succ]
      push_cast
      have h0 := hk k
      have p1 : (k : ℚ) + 1 ≠ 0 := by positivity
      have p2 : (k : ℚ) + 1 + 1 ≠ 0 := by positivity
      field_simp
      ring

/-- The differential equation of the exponential generating function. -/
lemma odeA : C (2 : ℚ) * (X * (X * d⁄dX ℚ (X * d⁄dX ℚ (exp ℚ * PowerSeries.mk bb))))
      + C (2 : ℚ) * (X * (X * d⁄dX ℚ (exp ℚ * PowerSeries.mk bb)))
      + C (4 : ℚ) * (X * (exp ℚ * PowerSeries.mk bb))
      + C (5 : ℚ) * (X * (X * (exp ℚ * PowerSeries.mk bb)))
      - (X * d⁄dX ℚ (X * d⁄dX ℚ (exp ℚ * PowerSeries.mk bb))
        + X * d⁄dX ℚ (exp ℚ * PowerSeries.mk bb)
        + C (4 : ℚ) * (X * (X * (X * d⁄dX ℚ (exp ℚ * PowerSeries.mk bb))))
        + C (14 : ℚ) * (X * (X * (X * (exp ℚ * PowerSeries.mk bb))))) = 0 := by
  have hB := odeB
  have hE : d⁄dX ℚ (exp ℚ) = exp ℚ := derivative_exp ℚ
  simp only [Derivation.leibniz, derivative_X, smul_eq_mul, hE, map_add, map_ofNat] at hB ⊢
  linear_combination exp ℚ * hB

/-- The coefficients of the exponential generating function divided by n!. -/
noncomputable def c (m : ℕ) : ℚ := coeff m (exp ℚ * PowerSeries.mk bb)

lemma recC (k : ℕ) :
    -(((k : ℚ) + 3) * ((k : ℚ) + 4)) * c (k + 3)
      + (2 * ((k : ℚ) + 3) * ((k : ℚ) + 2) + 4) * c (k + 2)
      + (13 - 4 * ((k : ℚ) + 3)) * c (k + 1) - 14 * c k = 0 := by
  have hc := congrArg (coeff (k + 3)) odeA
  simp only [map_add, map_sub, map_zero, coeff_C_mul, coeff_succ_X_mul, coeff_derivative] at hc
  push_cast at hc
  unfold c
  linear_combination hc

lemma rec1 : c 1 = 2 * c 0 := by
  have hc := congrArg (coeff (0 + 1)) odeA
  simp only [map_add, map_sub, map_zero, coeff_C_mul, coeff_succ_X_mul, coeff_zero_X_mul,
    coeff_derivative] at hc
  norm_num at hc
  have e : coeff 0 (exp ℚ * PowerSeries.mk bb) = bb 0 := by norm_num
  unfold c
  rw [e]
  linear_combination (-1 / 2 : ℚ) * hc

lemma rec2 : 6 * c 2 = 8 * c 1 + 5 * c 0 := by
  have hc := congrArg (coeff (0 + 1 + 1)) odeA
  simp only [map_add, map_sub, map_zero, coeff_C_mul, coeff_succ_X_mul, coeff_zero_X_mul,
    coeff_derivative] at hc
  norm_num at hc
  have e : coeff 0 (exp ℚ * PowerSeries.mk bb) = bb 0 := by norm_num
  unfold c
  rw [e]
  linear_combination (-1 : ℚ) * hc

/-- The second order recurrence. -/
lemma recL (k : ℕ) :
    ((k : ℚ) + 2) * ((k : ℚ) + 3) * (2 * (k : ℚ) + 5) * c (k + 2)
      - 4 * (((k : ℚ) + 2) ^ 2 + ((k : ℚ) + 2) + 1) * c (k + 1)
      - 7 * (2 * (k : ℚ) + 7) * c k = 0 := by
  induction k with
  | zero =>
    have h1 := rec1
    have h2 := rec2
    norm_num
    linear_combination 5 * h2 + 12 * h1
  | succ k ih =>
    have hN := recC k
    have e2 : k + 1 + 2 = k + 3 := by omega
    have e1 : k + 1 + 1 = k + 2 := by omega
    rw [e2, e1]
    push_cast
    linear_combination 2 * ih - (2 * ((k : ℚ) + 3) + 1) * hN

end OMA.P119975

open OMA.S_oeis_a119975 OMA.P119975 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a119975.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  have hN := recC k
  have hL := recL k
  have e1 : k + 3 - 1 = k + 2 := by omega
  have e2 : k + 3 - 2 = k + 1 := by omega
  have e3 : k + 3 - 3 = k := by omega
  unfold a
  rw [e1, e2, e3, mk_bb]
  unfold c at hN hL
  simp only [Nat.factorial_succ]
  push_cast
  linear_combination ((k.factorial : ℚ) * ((k : ℚ) + 1)) * hL
    - ((k.factorial : ℚ) * ((k : ℚ) + 1) * ((k : ℚ) + 2)) * hN
