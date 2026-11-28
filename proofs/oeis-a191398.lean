import OMAStatements.S_oeis_a191398
import Mathlib

open OMA.S_oeis_a191398
open PowerSeries

namespace Pa191398

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
theorem ode (S A : PowerSeries ℚ) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hL : (2 - 6 * X + 4 * X ^ 2 + 2 * X ^ 4) * A = (1 - X - 2 * X ^ 3) + (-1 + X) * S) :
    (-8 * X + 16 * X ^ 2 - 4 * X ^ 3 + 4 * X ^ 4 + 4 * X ^ 5 + 16 * X ^ 6) * (A) + (5 - 9 * X - 14 * X ^ 2 + 24 * X ^ 3 - 3 * X ^ 4 + 16 * X ^ 6) * (X * d⁄dX ℚ A) + (-1 + 3 * X + 2 * X ^ 2 - 12 * X ^ 3 + 7 * X ^ 4 + 4 * X ^ 6) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = 6 * X ^ 2 - 8 * X ^ 3 - 4 * X ^ 4 - 4 * X ^ 5 := by
  have hdD : d⁄dX ℚ (1 - 4 * X ^ 2 : PowerSeries ℚ) = -8 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have hS1 := sq_step S _ hS
  rw [hdD] at hS1
  have L0 := hL
  have dP1 : d⁄dX ℚ (2 - 6 * X + 4 * X ^ 2 + 2 * X ^ 4 : PowerSeries ℚ) = -6 + 8 * X + 8 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (1 - X - 2 * X ^ 3 : PowerSeries ℚ) = -1 - 6 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (-1 + X : PowerSeries ℚ) = 1 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (2 - 12 * X + 18 * X ^ 2 + 24 * X ^ 3 - 92 * X ^ 4 + 84 * X ^ 5 - 40 * X ^ 6 + 48 * X ^ 7 - 30 * X ^ 8 - 8 * X ^ 10) * (X * d⁄dX ℚ A) = (2 * X - 4 * X ^ 2 - 12 * X ^ 3 + 24 * X ^ 4 + 15 * X ^ 5 - 32 * X ^ 6 + 6 * X ^ 7 - 8 * X ^ 9) + (-2 * X + 8 * X ^ 2 - 10 * X ^ 3 + 8 * X ^ 4 - 3 * X ^ 5 - 12 * X ^ 6 + 8 * X ^ 7) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 6 * X ^ 2 - 4 * X ^ 3 + 24 * X ^ 4 - 14 * X ^ 5 - 8 * X ^ 7) * E1 + (6 * X - 8 * X ^ 2 - 24 * X ^ 3 + 24 * X ^ 4 + 32 * X ^ 6) * L0 + (-X + 4 * X ^ 2 - 5 * X ^ 3 + 2 * X ^ 4 - X ^ 5 + X ^ 6) * hS1
  have dP2 : d⁄dX ℚ (2 - 12 * X + 18 * X ^ 2 + 24 * X ^ 3 - 92 * X ^ 4 + 84 * X ^ 5 - 40 * X ^ 6 + 48 * X ^ 7 - 30 * X ^ 8 - 8 * X ^ 10 : PowerSeries ℚ) = -12 + 36 * X + 72 * X ^ 2 - 368 * X ^ 3 + 420 * X ^ 4 - 240 * X ^ 5 + 336 * X ^ 6 - 240 * X ^ 7 - 80 * X ^ 9 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU2 : d⁄dX ℚ (2 * X - 4 * X ^ 2 - 12 * X ^ 3 + 24 * X ^ 4 + 15 * X ^ 5 - 32 * X ^ 6 + 6 * X ^ 7 - 8 * X ^ 9 : PowerSeries ℚ) = 2 - 8 * X - 36 * X ^ 2 + 96 * X ^ 3 + 75 * X ^ 4 - 192 * X ^ 5 + 42 * X ^ 6 - 72 * X ^ 8 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV2 : d⁄dX ℚ (-2 * X + 8 * X ^ 2 - 10 * X ^ 3 + 8 * X ^ 4 - 3 * X ^ 5 - 12 * X ^ 6 + 8 * X ^ 7 : PowerSeries ℚ) = -2 + 16 * X - 30 * X ^ 2 + 32 * X ^ 3 - 15 * X ^ 4 - 72 * X ^ 5 + 56 * X ^ 6 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E2 := th_step _ _ _ _ _ L1
  simp only [dP2, dU2, dV2] at E2
  have L2 : (-2 + 18 * X - 50 * X ^ 2 - 18 * X ^ 3 + 358 * X ^ 4 - 612 * X ^ 5 - 46 * X ^ 6 + 1224 * X ^ 7 - 1486 * X ^ 8 + 1170 * X ^ 9 - 1276 * X ^ 10 + 1008 * X ^ 11 - 386 * X ^ 12 + 288 * X ^ 13 - 176 * X ^ 14 - 32 * X ^ 16) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = (-2 * X + 2 * X ^ 2 + 40 * X ^ 3 - 76 * X ^ 4 - 165 * X ^ 5 + 479 * X ^ 6 - 120 * X ^ 7 - 634 * X ^ 8 + 1185 * X ^ 9 - 1024 * X ^ 10 - 390 * X ^ 11 + 992 * X ^ 12 - 256 * X ^ 13 + 32 * X ^ 15) + (2 * X - 10 * X ^ 2 + 18 * X ^ 3 - 46 * X ^ 4 + 109 * X ^ 5 - 3 * X ^ 6 - 164 * X ^ 7 - 256 * X ^ 8 + 807 * X ^ 9 - 664 * X ^ 10 + 184 * X ^ 11 + 144 * X ^ 12 - 64 * X ^ 13) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-2 * X + 6 * X ^ 2 + 4 * X ^ 3 - 24 * X ^ 4 + 14 * X ^ 5 + 8 * X ^ 7) * E2 + (-12 * X + 96 * X ^ 3 - 80 * X ^ 4 - 80 * X ^ 6) * L1 + (2 * X ^ 2 - 14 * X ^ 3 + 38 * X ^ 4 - 54 * X ^ 5 + 49 * X ^ 6 - 21 * X ^ 7 - 28 * X ^ 8 + 40 * X ^ 9 - 13 * X ^ 10 + 12 * X ^ 11 - 8 * X ^ 12) * hS1
  have key : (2 - 18 * X + 50 * X ^ 2 + 18 * X ^ 3 - 358 * X ^ 4 + 612 * X ^ 5 + 46 * X ^ 6 - 1224 * X ^ 7 + 1486 * X ^ 8 - 1170 * X ^ 9 + 1276 * X ^ 10 - 1008 * X ^ 11 + 386 * X ^ 12 - 288 * X ^ 13 + 176 * X ^ 14 + 32 * X ^ 16) * (((-8 * X + 16 * X ^ 2 - 4 * X ^ 3 + 4 * X ^ 4 + 4 * X ^ 5 + 16 * X ^ 6) * (A) + (5 - 9 * X - 14 * X ^ 2 + 24 * X ^ 3 - 3 * X ^ 4 + 16 * X ^ 6) * (X * d⁄dX ℚ A) + (-1 + 3 * X + 2 * X ^ 2 - 12 * X ^ 3 + 7 * X ^ 4 + 4 * X ^ 6) * (X * d⁄dX ℚ (X * d⁄dX ℚ A))) - (6 * X ^ 2 - 8 * X ^ 3 - 4 * X ^ 4 - 4 * X ^ 5)) = 0 := by
    linear_combination (-8 * X + 64 * X ^ 2 - 140 * X ^ 3 - 180 * X ^ 4 + 1192 * X ^ 5 - 1396 * X ^ 6 - 1012 * X ^ 7 + 3696 * X ^ 8 - 3256 * X ^ 9 + 1704 * X ^ 10 - 2260 * X ^ 11 + 3588 * X ^ 12 - 2780 * X ^ 13 + 1136 * X ^ 14 - 1376 * X ^ 15 + 960 * X ^ 16 + 64 * X ^ 17 + 256 * X ^ 18) * L0 + (5 - 24 * X + 3 * X ^ 2 + 144 * X ^ 3 - 190 * X ^ 4 - 144 * X ^ 5 + 388 * X ^ 6 - 216 * X ^ 7 + 45 * X ^ 8 + 96 * X ^ 9 - 100 * X ^ 10 - 64 * X ^ 12) * L1 + (1 - 3 * X - 2 * X ^ 2 + 12 * X ^ 3 - 7 * X ^ 4 - 4 * X ^ 6) * L2
  have hne : (2 - 18 * X + 50 * X ^ 2 + 18 * X ^ 3 - 358 * X ^ 4 + 612 * X ^ 5 + 46 * X ^ 6 - 1224 * X ^ 7 + 1486 * X ^ 8 - 1170 * X ^ 9 + 1276 * X ^ 10 - 1008 * X ^ 11 + 386 * X ^ 12 - 288 * X ^ 13 + 176 * X ^ 14 + 32 * X ^ 16 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 0
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

theorem S_sq : S ^ 2 = 1 - 4 * X ^ 2 := by
  have hB : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = (1 + X : PowerSeries ℚ) := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    norm_num
    simpa using binomialSeries_nat (A := ℚ) (R := ℚ) 1
  have h0 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow h0, hB, ← coe_substAlgHom h0, map_add, map_one,
    coe_substAlgHom, subst_X h0, R]
  ring

theorem gf_eq : (2 - 6 * X + 4 * X ^ 2 + 2 * X ^ 4) * ((1 - X - 2 * X ^ 3 + (-1 + X) * S) * (2 - 6 * X + 4 * X ^ 2 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹) = 1 - X - 2 * X ^ 3 + (-1 + X) * S := by
  have hd : constantCoeff (2 - 6 * X + 4 * X ^ 2 + 2 * X ^ 4 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (2 - 6 * X + 4 * X ^ 2 + 2 * X ^ 4 : PowerSeries ℚ) hd
  linear_combination (1 - X - 2 * X ^ 3 + (-1 + X) * S) * hinv

end Pa191398

theorem OMA.solution : type_of% @OMA.S_oeis_a191398.main := by
  intro n hn
  have hL := Pa191398.gf_eq
  have ha : ∀ m, a m = coeff (m + 2) ((1 - X - 2 * X ^ 3 + (-1 + X) * S) * (2 - 6 * X + 4 * X ^ 2 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((1 - X - 2 * X ^ 3 + (-1 + X) * S) * (2 - 6 * X + 4 * X ^ 2 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹) = A at hL ha
  have hL' : (2 - 6 * X + 4 * X ^ 2 + 2 * X ^ 4) * A = (1 - X - 2 * X ^ 3) + (-1 + X) * S := by
    linear_combination hL
  have e := congrArg (coeff (n + 2)) (Pa191398.ode S A Pa191398.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  simp only [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega, show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega, show k + 6 - 5 = k + 1 by omega, show k + 6 - 6 = k by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [Pa191398.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa191398.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
