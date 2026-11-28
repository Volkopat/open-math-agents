import OMAStatements.S_oeis_a228178
import Mathlib

open OMA.S_oeis_a228178
open PowerSeries

namespace Pa228178

theorem nC (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem cXd (F : PowerSeries ℚ) (k : ℕ) : coeff k (X * d⁄dX ℚ F) = coeff k F * k := by
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

theorem sq_step (S E : PowerSeries ℚ) (h : S ^ 2 = E) : 2 * E * d⁄dX ℚ S = d⁄dX ℚ E * S := by
  have h1 := congrArg (d⁄dX ℚ) h
  simp only [pow_two, Derivation.leibniz, smul_eq_mul] at h1
  linear_combination (-2 * d⁄dX ℚ S) * h + S * h1

theorem th_step (P B U V S : PowerSeries ℚ) (h : P * B = U + V * S) :
    d⁄dX ℚ P * B + P * d⁄dX ℚ B = d⁄dX ℚ U + d⁄dX ℚ V * S + V * d⁄dX ℚ S := by
  have h1 := congrArg (d⁄dX ℚ) h
  simp only [Derivation.leibniz, map_add, smul_eq_mul] at h1
  linear_combination h1

theorem ne_of_coeff (p : PowerSeries ℚ) (m : ℕ) (h : coeff m p ≠ 0) : p ≠ 0 := by
  intro h0; rw [h0, map_zero] at h; exact h rfl

set_option maxHeartbeats 2000000 in
theorem ode (S A : PowerSeries ℚ) (hS : S ^ 2 = 1 - 4 * X)
    (hL : (2 * X ^ 2 - 2 * X ^ 3) * A = (2 - 8 * X + 5 * X ^ 2) + (-2 + 4 * X - X ^ 2) * S) :
    (4 - 22 * X + 36 * X ^ 2 - 23 * X ^ 3 + 2 * X ^ 4) * (A) + (2 - 14 * X + 29 * X ^ 2 - 21 * X ^ 3 + 4 * X ^ 4) * (X * d⁄dX ℚ A) = 6 * X - 4 * X ^ 2 + 5 * X ^ 3 := by
  have hdD : d⁄dX ℚ (1 - 4 * X : PowerSeries ℚ) = -4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have hS1 := sq_step S _ hS
  rw [hdD] at hS1
  have L0 := hL
  have dP1 : d⁄dX ℚ (2 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ) = 4 * X - 6 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (2 - 8 * X + 5 * X ^ 2 : PowerSeries ℚ) = -8 + 10 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (-2 + 4 * X - X ^ 2 : PowerSeries ℚ) = 4 - 2 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (2 * X ^ 2 - 12 * X ^ 3 + 18 * X ^ 4 - 8 * X ^ 5) * (X * d⁄dX ℚ A) = (-4 + 30 * X - 72 * X ^ 2 + 69 * X ^ 3 - 20 * X ^ 4) + (4 - 22 * X + 36 * X ^ 2 - 23 * X ^ 3 + 2 * X ^ 4) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 10 * X ^ 2 + 8 * X ^ 3) * E1 + (-4 + 22 * X - 24 * X ^ 2) * L0 + (-2 * X + 6 * X ^ 2 - 5 * X ^ 3 + X ^ 4) * hS1
  have key : (-2 * X ^ 2 + 12 * X ^ 3 - 18 * X ^ 4 + 8 * X ^ 5) * (((4 - 22 * X + 36 * X ^ 2 - 23 * X ^ 3 + 2 * X ^ 4) * (A) + (2 - 14 * X + 29 * X ^ 2 - 21 * X ^ 3 + 4 * X ^ 4) * (X * d⁄dX ℚ A)) - (6 * X - 4 * X ^ 2 + 5 * X ^ 3)) = 0 := by
    linear_combination (-4 + 42 * X - 162 * X ^ 2 + 291 * X ^ 3 - 261 * X ^ 4 + 102 * X ^ 5 - 8 * X ^ 6) * L0 + (-2 + 14 * X - 29 * X ^ 2 + 21 * X ^ 3 - 4 * X ^ 4) * L1
  have hne : (-2 * X ^ 2 + 12 * X ^ 3 - 18 * X ^ 4 + 8 * X ^ 5 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 2
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

end Pa228178

theorem OMA.solution : type_of% @OMA.S_oeis_a228178.main := by
  intro T G hT hG n hn
  have h2 : X * T ^ 2 = T - 1 := by linear_combination -hT
  have h4 : X ^ 2 * T ^ 4 = (T - 1) ^ 2 := by
    rw [show X ^ 2 * T ^ 4 = (X * T ^ 2) ^ 2 by ring, h2]
  have hS : (1 - 2 * X * T) ^ 2 = 1 - 4 * X := by linear_combination (4 * X) * h2
  have hL' : (2 * X ^ 2 - 2 * X ^ 3) * G = (2 - 8 * X + 5 * X ^ 2) + (-2 + 4 * X - X ^ 2) * (1 - 2 * X * T) := by
    linear_combination (2 * X ^ 2) * hG + (4 * X ^ 2) * h4 + (4 * X) * h2
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have e := congrArg (coeff (k + 5)) (Pa228178.ode _ G hS hL')
  simp only [show k + 4 + 1 = k + 5 by omega, show k + 4 - 1 = k + 3 by omega,
    show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega]
  norm_num only at e ⊢
  simp only [Pa228178.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa228178.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
