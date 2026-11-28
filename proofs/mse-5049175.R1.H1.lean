import OMAReductions.R_mse_5049175_R1

namespace OMA.Proof_mse_5049175_R1_H1

open Polynomial OMA.S_mse_5049175

private lemma nat_mul_C (a : ℕ) (b c : ℚ) (h : (a : ℚ) * b = c) :
    (a : ℚ[X]) * C b = C c := by
  rw [← C_eq_natCast, ← C_mul, h]

private lemma nat_mul_C_nat (a : ℕ) (b : ℚ) (c : ℕ) (h : (a : ℚ) * b = (c : ℚ)) :
    (a : ℚ[X]) * C b = (c : ℚ[X]) := by
  rw [← C_eq_natCast, ← C_mul, h, C_eq_natCast]

private lemma bernoulli_two_poly : Polynomial.bernoulli 2 = X ^ 2 - X + C (1 / 6 : ℚ) := by
  have h := Polynomial.bernoulli_eq_sub_sum 2
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
    Polynomial.bernoulli_zero, Polynomial.bernoulli_one] at h
  have hchoose0 : Nat.choose 3 0 = 1 := by decide
  have hchoose1 : Nat.choose 3 1 = 3 := by decide
  rw [hchoose0, hchoose1, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul] at h
  have h3 : (3 : ℚ[X]) * Polynomial.bernoulli 2 = (3 : ℚ[X]) * (X ^ 2 - X + C (1 / 6 : ℚ)) := by
    have h' : (3 : ℚ[X]) * Polynomial.bernoulli 2 =
        (3 : ℚ[X]) * X ^ 2 - ((1 : ℚ[X]) + (3 : ℚ[X]) * (X - C (2⁻¹ : ℚ))) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, show (2 : ℚ[X]) + 1 = 3 by norm_num,
        one_mul] using h
    rw [h']
    have hC1 : (3 : ℚ[X]) * C (1 / 6 : ℚ) = C (1 / 2 : ℚ) := nat_mul_C 3 (1 / 6) (1 / 2) (by norm_num)
    have hC2 : (3 : ℚ[X]) * C (2⁻¹ : ℚ) = C (3 / 2 : ℚ) := nat_mul_C 3 (2⁻¹) (3 / 2) (by norm_num)
    have hC3 : (1 : ℚ[X]) - C (3 / 2 : ℚ) = -C (1 / 2 : ℚ) := by
      rw [← map_one C, ← C_sub, ← C_neg]; norm_num
    linear_combination hC2 - hC1 - hC3
  exact mul_left_cancel₀ (by norm_num : (3 : ℚ[X]) ≠ 0) h3

private lemma bernoulli_three_poly :
    Polynomial.bernoulli 3 = X ^ 3 - C (3 / 2 : ℚ) * X ^ 2 + C (1 / 2 : ℚ) * X := by
  have h := Polynomial.bernoulli_eq_sub_sum 3
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
    zero_add, Polynomial.bernoulli_zero, Polynomial.bernoulli_one, bernoulli_two_poly] at h
  have hchoose0 : Nat.choose 4 0 = 1 := by decide
  have hchoose1 : Nat.choose 4 1 = 4 := by decide
  have hchoose2 : Nat.choose 4 2 = 6 := by decide
  rw [hchoose0, hchoose1, hchoose2, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul,
    nsmul_eq_mul] at h
  have h4 : (4 : ℚ[X]) * Polynomial.bernoulli 3 =
      (4 : ℚ[X]) * (X ^ 3 - C (3 / 2 : ℚ) * X ^ 2 + C (1 / 2 : ℚ) * X) := by
    have h' : (4 : ℚ[X]) * Polynomial.bernoulli 3 =
        (4 : ℚ[X]) * X ^ 3 - ((1 : ℚ[X]) + (4 : ℚ[X]) * (X - C (2⁻¹ : ℚ)) +
          (6 : ℚ[X]) * (X ^ 2 - X + C (1 / 6 : ℚ))) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, show (3 : ℚ[X]) + 1 = 4 by norm_num,
        one_mul] using h
    rw [h']
    have hC1 : (4 : ℚ[X]) * C (2⁻¹ : ℚ) = 2 := nat_mul_C_nat 4 (2⁻¹) 2 (by norm_num)
    have hC2 : (6 : ℚ[X]) * C (1 / 6 : ℚ) = 1 := nat_mul_C_nat 6 (1 / 6) 1 (by norm_num)
    have hC3 : (4 : ℚ[X]) * C (3 / 2 : ℚ) = 6 := nat_mul_C_nat 4 (3 / 2) 6 (by norm_num)
    have hC4 : (4 : ℚ[X]) * C (1 / 2 : ℚ) = 2 := nat_mul_C_nat 4 (1 / 2) 2 (by norm_num)
    linear_combination hC1 - hC2 + hC3 * X ^ 2 - hC4 * X
  exact mul_left_cancel₀ (by norm_num : (4 : ℚ[X]) ≠ 0) h4

private lemma bernoulli_four_poly :
    Polynomial.bernoulli 4 = X ^ 4 - 2 * X ^ 3 + X ^ 2 - C (1 / 30 : ℚ) := by
  have h := Polynomial.bernoulli_eq_sub_sum 4
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, Polynomial.bernoulli_zero, Polynomial.bernoulli_one,
    bernoulli_two_poly, bernoulli_three_poly] at h
  have hchoose0 : Nat.choose 5 0 = 1 := by decide
  have hchoose1 : Nat.choose 5 1 = 5 := by decide
  have hchoose2 : Nat.choose 5 2 = 10 := by decide
  have hchoose3 : Nat.choose 5 3 = 10 := by decide
  rw [hchoose0, hchoose1, hchoose2, hchoose3, nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul,
    nsmul_eq_mul, nsmul_eq_mul, nsmul_eq_mul] at h
  have h5 : (5 : ℚ[X]) * Polynomial.bernoulli 4 =
      (5 : ℚ[X]) * (X ^ 4 - 2 * X ^ 3 + X ^ 2 - C (1 / 30 : ℚ)) := by
    have h' : (5 : ℚ[X]) * Polynomial.bernoulli 4 =
        (5 : ℚ[X]) * X ^ 4 - ((1 : ℚ[X]) + (5 : ℚ[X]) * (X - C (2⁻¹ : ℚ)) +
          (10 : ℚ[X]) * (X ^ 2 - X + C (1 / 6 : ℚ)) +
          (10 : ℚ[X]) * (X ^ 3 - C (3 / 2 : ℚ) * X ^ 2 + C (1 / 2 : ℚ) * X)) := by
      simpa only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, show (4 : ℚ[X]) + 1 = 5 by norm_num,
        one_mul] using h
    rw [h']
    have hC1 : (5 : ℚ[X]) * C (2⁻¹ : ℚ) = C (5 / 2 : ℚ) := nat_mul_C 5 (2⁻¹) (5 / 2) (by norm_num)
    have hC2 : (10 : ℚ[X]) * C (1 / 6 : ℚ) = C (5 / 3 : ℚ) := nat_mul_C 10 (1 / 6) (5 / 3) (by norm_num)
    have hC3 : (10 : ℚ[X]) * C (3 / 2 : ℚ) = 15 := nat_mul_C_nat 10 (3 / 2) 15 (by norm_num)
    have hC4 : (10 : ℚ[X]) * C (1 / 2 : ℚ) = 5 := nat_mul_C_nat 10 (1 / 2) 5 (by norm_num)
    have hC5 : (5 : ℚ[X]) * C (1 / 30 : ℚ) = C (1 / 6 : ℚ) := nat_mul_C 5 (1 / 30) (1 / 6) (by norm_num)
    have hC6 : (1 : ℚ[X]) - C (5 / 2 : ℚ) + C (5 / 3 : ℚ) = C (1 / 6 : ℚ) := by
      rw [← map_one C, ← C_sub, ← C_add]; norm_num
    linear_combination hC1 - hC2 + hC3 * X ^ 2 - hC4 * X + hC5 - hC6
  exact mul_left_cancel₀ (by norm_num : (5 : ℚ[X]) ≠ 0) h5

private lemma f_one_eq : f 1 = C (1 / 2 : ℚ) * (X * (X + 1)) := by
  unfold f
  rw [bernoulli_two_poly]
  simp only [Nat.cast_one, show (1 : ℚ) + 1 = 2 by norm_num, smul_eq_C_mul]
  simp [sub_comp, add_comp, pow_comp, X_comp, C_comp, eval_add, eval_sub, eval_pow, eval_X, eval_C]
  ring

private lemma f_two_eq : f 2 = C (1 / 6 : ℚ) * (X * (X + 1) * (2 * X + 1)) := by
  have h6 : (6 : ℚ[X]) * f 2 = (6 : ℚ[X]) * (C (1 / 6 : ℚ) * (X * (X + 1) * (2 * X + 1))) := by
    unfold f
    rw [bernoulli_three_poly]
    simp only [Nat.cast_ofNat, show (2 : ℚ) + 1 = 3 by norm_num, smul_eq_C_mul]
    simp only [sub_comp, add_comp, mul_comp, pow_comp, X_comp, C_comp, eval_add, eval_sub, eval_mul,
      eval_pow, eval_X, eval_C]
    have h0 : (0 : ℚ) ^ 3 - 3 / 2 * 0 ^ 2 + 1 / 2 * 0 = 0 := by norm_num
    rw [h0, map_zero, sub_zero, ← mul_assoc, ← mul_assoc]
    have h63 : (6 : ℚ[X]) * C (1 / 3 : ℚ) = 2 := nat_mul_C_nat 6 (1 / 3) 2 (by norm_num)
    have h66 : (6 : ℚ[X]) * C (1 / 6 : ℚ) = 1 := nat_mul_C_nat 6 (1 / 6) 1 (by norm_num)
    have h23 : (2 : ℚ[X]) * C (3 / 2 : ℚ) = 3 := nat_mul_C_nat 2 (3 / 2) 3 (by norm_num)
    have h22 : (2 : ℚ[X]) * C (1 / 2 : ℚ) = 1 := nat_mul_C_nat 2 (1 / 2) 1 (by norm_num)
    rw [h63, h66, one_mul]
    linear_combination -(X + 1) ^ 2 * h23 + (X + 1) * h22
  exact mul_left_cancel₀ (by norm_num : (6 : ℚ[X]) ≠ 0) h6

private lemma f_three_eq : f 3 = C (1 / 4 : ℚ) * (X ^ 2 * (X + 1) ^ 2) := by
  unfold f
  rw [bernoulli_four_poly]
  simp only [Nat.cast_ofNat, show (3 : ℚ) + 1 = 4 by norm_num, smul_eq_C_mul]
  simp [sub_comp, add_comp, mul_comp, pow_comp, X_comp, C_comp, eval_add, eval_sub, eval_mul,
    eval_pow, eval_X, eval_C]
  ring

private lemma eval_zero_f {n : ℕ} (hn : 1 ≤ n) : (f n).eval 0 = 0 := by
  unfold f
  rw [eval_smul, eval_sub, eval_comp, eval_add, eval_X, eval_one, zero_add, eval_C,
    Polynomial.bernoulli_eval_one, Polynomial.bernoulli_eval_zero,
    bernoulli_eq_bernoulli'_of_ne_one (by omega), sub_self, smul_zero]

private lemma eval_neg_one_f (n : ℕ) : (f n).eval (-1) = 0 := by
  unfold f
  rw [eval_smul, eval_sub, eval_comp, eval_add, eval_X, eval_one, neg_add_cancel, eval_C,
    sub_self, smul_zero]

private lemma eval_neg_half_f {n : ℕ} (hn : 2 ≤ n) (heven : Even n) : (f n).eval (-1 / 2) = 0 := by
  unfold f
  rw [eval_smul, eval_sub, eval_comp, eval_add, eval_X, eval_one, eval_C]
  have hhalf : (-1 / 2 : ℚ) + 1 = 1 / 2 := by norm_num
  rw [hhalf]
  have hodd : Odd (n + 1) := heven.add_one
  have hsym := Polynomial.bernoulli_eval_one_sub (n + 1) (1 / 2 : ℚ)
  rw [show (1 : ℚ) - 1 / 2 = 1 / 2 by norm_num, hodd.neg_one_pow] at hsym
  have hval_half : (Polynomial.bernoulli (n + 1)).eval (1 / 2 : ℚ) = 0 := by linarith
  have hval_zero : (Polynomial.bernoulli (n + 1)).eval 0 = 0 := by
    rw [Polynomial.bernoulli_eval_zero]
    exact bernoulli_eq_zero_of_odd hodd (by omega)
  rw [hval_half, hval_zero, sub_self, smul_zero]

private lemma derivative_f (n : ℕ) :
    Polynomial.derivative (f n) = (Polynomial.bernoulli n).comp (X + 1) := by
  unfold f
  rw [derivative_smul, derivative_sub, derivative_C, sub_zero, derivative_comp,
    Polynomial.derivative_bernoulli_add_one, derivative_add, derivative_X, derivative_one,
    add_zero, one_mul, mul_comp]
  have hC : ((n : ℚ[X]) + 1).comp (X + 1) = C ((n : ℚ) + 1) := by
    rw [show (n : ℚ[X]) + 1 = C ((n : ℚ) + 1) by simp, C_comp]
  rw [hC, smul_eq_C_mul, ← mul_assoc, ← C_mul]
  have hne : (n : ℚ) + 1 ≠ 0 := by positivity
  rw [one_div_mul_cancel hne, map_one, one_mul]

private lemma sq_dvd_of_eval_and_deriv {p : ℚ[X]} {a : ℚ}
    (h0 : p.eval a = 0) (h1 : (Polynomial.derivative p).eval a = 0) :
    (X - C a) ^ 2 ∣ p := by
  have hd1 : X - C a ∣ p := Polynomial.dvd_iff_isRoot.mpr h0
  obtain ⟨q, rfl⟩ := hd1
  rw [derivative_mul, derivative_sub, derivative_X, derivative_C, sub_zero, one_mul,
    eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, zero_mul, add_zero] at h1
  have hd2 : X - C a ∣ q := Polynomial.dvd_iff_isRoot.mpr h1
  obtain ⟨r, rfl⟩ := hd2
  exact ⟨r, by ring⟩

private lemma C_mul_dvd_of_ne_zero {c : ℚ} (hc : c ≠ 0) {p q : ℚ[X]} (h : p ∣ q) :
    C c * p ∣ q := by
  obtain ⟨r, rfl⟩ := h
  refine ⟨C c⁻¹ * r, ?_⟩
  rw [show C c * p * (C c⁻¹ * r) = (C c * C c⁻¹) * (p * r) by ring, ← C_mul,
    mul_inv_cancel₀ hc, map_one, one_mul]

end OMA.Proof_mse_5049175_R1_H1

theorem OMA.solution : OMA.R_mse_5049175_R1.H1 := by
  open Polynomial OMA.S_mse_5049175 OMA.Proof_mse_5049175_R1_H1 in
  have hcop01 : IsCoprime (X : ℚ[X]) (X + 1) := ⟨-1, 1, by ring⟩
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    have hX : X ∣ f n := by
      simpa using Polynomial.dvd_iff_isRoot.mpr (eval_zero_f hn)
    have hX1 : X + 1 ∣ f n := by
      simpa [sub_neg_eq_add] using Polynomial.dvd_iff_isRoot.mpr (eval_neg_one_f n)
    rw [f_one_eq]
    exact C_mul_dvd_of_ne_zero (by norm_num) (hcop01.mul_dvd hX hX1)
  · intro n hn heven
    have hX : X ∣ f n := by
      simpa using Polynomial.dvd_iff_isRoot.mpr (eval_zero_f (by omega))
    have hX1 : X + 1 ∣ f n := by
      simpa [sub_neg_eq_add] using Polynomial.dvd_iff_isRoot.mpr (eval_neg_one_f n)
    have hX01 : X * (X + 1) ∣ f n := hcop01.mul_dvd hX hX1
    have h2X1 : 2 * X + 1 ∣ f n := by
      have hroot : X - C (-1 / 2 : ℚ) ∣ f n :=
        Polynomial.dvd_iff_isRoot.mpr (eval_neg_half_f hn heven)
      have heq : 2 * X + 1 = C (2 : ℚ) * (X - C (-1 / 2 : ℚ)) := by
        rw [mul_sub, ← C_mul, show (2 : ℚ) * (-1 / 2) = -1 by norm_num, map_neg, map_one,
          show C (2 : ℚ) = (2 : ℚ[X]) from map_ofNat C 2]
        ring
      rw [heq]
      exact C_mul_dvd_of_ne_zero (by norm_num) hroot
    have hcop2 : IsCoprime (X * (X + 1) : ℚ[X]) (2 * X + 1) := ⟨-4, 2 * X + 1, by ring⟩
    rw [f_two_eq]
    exact C_mul_dvd_of_ne_zero (by norm_num) (hcop2.mul_dvd hX01 h2X1)
  · intro n hn hodd
    have hderiv0 : (Polynomial.derivative (f n)).eval 0 = 0 := by
      rw [derivative_f, eval_comp, eval_add, eval_X, eval_one, zero_add,
        Polynomial.bernoulli_eval_one, ← bernoulli_eq_bernoulli'_of_ne_one (by omega)]
      exact bernoulli_eq_zero_of_odd hodd (by omega)
    have hderivm1 : (Polynomial.derivative (f n)).eval (-1) = 0 := by
      rw [derivative_f, eval_comp, eval_add, eval_X, eval_one, neg_add_cancel,
        Polynomial.bernoulli_eval_zero]
      exact bernoulli_eq_zero_of_odd hodd (by omega)
    have hX2 : X ^ 2 ∣ f n := by
      simpa using sq_dvd_of_eval_and_deriv (eval_zero_f (by omega)) hderiv0
    have hX12 : (X + 1) ^ 2 ∣ f n := by
      simpa [sub_neg_eq_add] using sq_dvd_of_eval_and_deriv (eval_neg_one_f n) hderivm1
    have hcop_sq : IsCoprime (X ^ 2 : ℚ[X]) ((X + 1) ^ 2) := hcop01.pow
    rw [f_three_eq]
    exact C_mul_dvd_of_ne_zero (by norm_num) (hcop_sq.mul_dvd hX2 hX12)
