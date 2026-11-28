import OMAStatements.S_oeis_a102880
import Mathlib

open OMA.S_oeis_a102880
open PowerSeries

namespace Pa102880

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

theorem cat_eq : c ^ 2 * X + 1 = c := by
  have := congrArg (map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
  simpa [c] using this

theorem catalan_subst (u : PowerSeries ℚ) (hu : constantCoeff u = 0) :
    c.subst u ^ 2 * u + 1 = c.subst u := by
  have ha := HasSubst.of_constantCoeff_zero' hu
  have hc := congrArg (substAlgHom ha) cat_eq
  rw [map_add, map_mul, map_pow, map_one, substAlgHom_X, coe_substAlgHom] at hc
  exact hc

theorem facts : ∃ T : PowerSeries ℚ, T ^ 2 = 1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4 ∧
    (2 * X + 2 * X ^ 3) * A = (1 - X ^ 4) + (-1 + X ^ 2) * T := by
  have hd : constantCoeff (1 + X ^ 2 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  set W : PowerSeries ℚ := (1 + X ^ 2)⁻¹ with hWdef
  have hW : (1 + X ^ 2) * W = 1 := PowerSeries.mul_inv_cancel _ hd
  set C : PowerSeries ℚ := c.subst (X * W) with hCdef
  have hC : C ^ 2 * (X * W) + 1 = C := catalan_subst _ (by simp)
  have hAe0 : A = (1 - X ^ 2) * W * C := rfl
  have hAe : A = (1 - X ^ 2) * W * C + (0) := by rw [hAe0]; ring
  have hWi : (W * (1 + X ^ 2)) ^ 1 = 1 := by rw [mul_comm, hW, one_pow]
  have hWb : (W * (1 + X ^ 2)) ^ 1 = 1 := by rw [mul_comm, hW, one_pow]
  have h1 : (A - (0)) * (1 + X ^ 2) ^ 1 = (1 - X ^ 2) * C := by
    rw [hAe]; linear_combination (1 - X ^ 2) * C * hWi
  have h2 : C ^ 2 * (X * (1)) + (1 + X ^ 2) ^ 1 = (1 + X ^ 2) ^ 1 * C := by
    linear_combination (1 + X ^ 2) ^ 1 * hC - C ^ 2 * X * (1) * hWb
  refine ⟨(1 + X ^ 2) ^ 1 - 2 * X * (1) * C, ?_, ?_⟩
  · linear_combination 4 * X * (1) * h2
  · linear_combination 2 * X * (1) * h1

set_option maxHeartbeats 2000000 in
theorem ode (S A : PowerSeries ℚ) (hS : S ^ 2 = 1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4)
    (hL : (2 * X + 2 * X ^ 3) * A = (1 - X ^ 4) + (-1 + X ^ 2) * S) :
    (-3 + 4 * X - 6 * X ^ 2 + 4 * X ^ 3 - 3 * X ^ 4) * (A) + (-2 + 6 * X - 6 * X ^ 3 + 2 * X ^ 4) * (X * d⁄dX ℚ A) + (1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = -3 + 3 * X ^ 4 := by
  have hdD : d⁄dX ℚ (1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4 : PowerSeries ℚ) = -4 + 4 * X - 12 * X ^ 2 + 4 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have hS1 := sq_step S _ hS
  rw [hdD] at hS1
  have L0 := hL
  have dP1 : d⁄dX ℚ (2 * X + 2 * X ^ 3 : PowerSeries ℚ) = 2 + 6 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (1 - X ^ 4 : PowerSeries ℚ) = -4 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (-1 + X ^ 2 : PowerSeries ℚ) = 2 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (2 * X - 8 * X ^ 2 + 6 * X ^ 3 - 16 * X ^ 4 + 6 * X ^ 5 - 8 * X ^ 6 + 2 * X ^ 7) * (X * d⁄dX ℚ A) = (-1 + 4 * X - 4 * X ^ 2 + 12 * X ^ 3 - 6 * X ^ 4 + 12 * X ^ 5 - 4 * X ^ 6 + 4 * X ^ 7 - X ^ 8) + (1 - 2 * X + 3 * X ^ 2 - 12 * X ^ 3 + 3 * X ^ 4 - 2 * X ^ 5 + X ^ 6) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 8 * X ^ 2 + 4 * X ^ 3 - 8 * X ^ 4 + 2 * X ^ 5) * E1 + (-2 + 8 * X - 8 * X ^ 2 + 24 * X ^ 3 - 6 * X ^ 4) * L0 + (-X + X ^ 3) * hS1
  have dP2 : d⁄dX ℚ (2 * X - 8 * X ^ 2 + 6 * X ^ 3 - 16 * X ^ 4 + 6 * X ^ 5 - 8 * X ^ 6 + 2 * X ^ 7 : PowerSeries ℚ) = 2 - 16 * X + 18 * X ^ 2 - 64 * X ^ 3 + 30 * X ^ 4 - 48 * X ^ 5 + 14 * X ^ 6 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU2 : d⁄dX ℚ (-1 + 4 * X - 4 * X ^ 2 + 12 * X ^ 3 - 6 * X ^ 4 + 12 * X ^ 5 - 4 * X ^ 6 + 4 * X ^ 7 - X ^ 8 : PowerSeries ℚ) = 4 - 8 * X + 36 * X ^ 2 - 24 * X ^ 3 + 60 * X ^ 4 - 24 * X ^ 5 + 28 * X ^ 6 - 8 * X ^ 7 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV2 : d⁄dX ℚ (1 - 2 * X + 3 * X ^ 2 - 12 * X ^ 3 + 3 * X ^ 4 - 2 * X ^ 5 + X ^ 6 : PowerSeries ℚ) = -2 + 6 * X - 36 * X ^ 2 + 12 * X ^ 3 - 10 * X ^ 4 + 6 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E2 := th_step _ _ _ _ _ L1
  simp only [dP2, dU2, dV2] at E2
  have L2 : (2 * X - 16 * X ^ 2 + 42 * X ^ 3 - 64 * X ^ 4 + 116 * X ^ 5 - 96 * X ^ 6 + 116 * X ^ 7 - 64 * X ^ 8 + 42 * X ^ 9 - 16 * X ^ 10 + 2 * X ^ 11) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = (1 - 8 * X + 20 * X ^ 2 - 24 * X ^ 3 + 37 * X ^ 4 - 16 * X ^ 5 + 16 * X ^ 7 - 37 * X ^ 8 + 24 * X ^ 9 - 20 * X ^ 10 + 8 * X ^ 11 - X ^ 12) + (-1 + 6 * X - 7 * X ^ 2 - 4 * X ^ 3 + 42 * X ^ 4 - 42 * X ^ 6 + 4 * X ^ 7 + 7 * X ^ 8 - 6 * X ^ 9 + X ^ 10) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 8 * X ^ 2 + 4 * X ^ 3 - 8 * X ^ 4 + 2 * X ^ 5) * E2 + (-2 + 16 * X - 16 * X ^ 2 + 48 * X ^ 3 - 14 * X ^ 4) * L1 + (X - 2 * X ^ 2 + 3 * X ^ 3 - 12 * X ^ 4 + 3 * X ^ 5 - 2 * X ^ 6 + X ^ 7) * hS1
  have key : (2 * X - 16 * X ^ 2 + 42 * X ^ 3 - 64 * X ^ 4 + 116 * X ^ 5 - 96 * X ^ 6 + 116 * X ^ 7 - 64 * X ^ 8 + 42 * X ^ 9 - 16 * X ^ 10 + 2 * X ^ 11) * (((-3 + 4 * X - 6 * X ^ 2 + 4 * X ^ 3 - 3 * X ^ 4) * (A) + (-2 + 6 * X - 6 * X ^ 3 + 2 * X ^ 4) * (X * d⁄dX ℚ A) + (1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ A))) - (-3 + 3 * X ^ 4)) = 0 := by
    linear_combination (-3 + 28 * X - 98 * X ^ 2 + 204 * X ^ 3 - 365 * X ^ 4 + 472 * X ^ 5 - 540 * X ^ 6 + 472 * X ^ 7 - 365 * X ^ 8 + 204 * X ^ 9 - 98 * X ^ 10 + 28 * X ^ 11 - 3 * X ^ 12) * L0 + (-2 + 14 * X - 28 * X ^ 2 + 14 * X ^ 3 - 14 * X ^ 5 + 28 * X ^ 6 - 14 * X ^ 7 + 2 * X ^ 8) * L1 + (1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4) * L2
  have hne : (2 * X - 16 * X ^ 2 + 42 * X ^ 3 - 64 * X ^ 4 + 116 * X ^ 5 - 96 * X ^ 6 + 116 * X ^ 7 - 64 * X ^ 8 + 42 * X ^ 9 - 16 * X ^ 10 + 2 * X ^ 11 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 1
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

end Pa102880

theorem OMA.solution : type_of% @OMA.S_oeis_a102880.main := by
  intro n hn
  obtain ⟨T, hT, hL⟩ := Pa102880.facts
  have e := congrArg (coeff n) (Pa102880.ode T A hT hL)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega, show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega]
  simp only [Pa102880.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa102880.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
