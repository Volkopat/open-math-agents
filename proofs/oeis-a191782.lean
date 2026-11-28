import OMAStatements.S_oeis_a191782
import Mathlib

open OMA.S_oeis_a191782
open PowerSeries

namespace Pa191782

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
    (hL : (2 - 6 * X + 4 * X ^ 2) * A = (-X ^ 3 + X ^ 4 + 3 * X ^ 5 - 3 * X ^ 6 + 2 * X ^ 7) + (X ^ 3 - X ^ 4 - X ^ 5 + X ^ 6) * S) :
    (-159 + 206 * X + 573 * X ^ 2 - 1098 * X ^ 3 + 460 * X ^ 4) * (A) + (71 - 124 * X - 195 * X ^ 2 + 460 * X ^ 3 - 212 * X ^ 4) * (X * d⁄dX ℚ A) + (-6 + 12 * X + 18 * X ^ 2 - 48 * X ^ 3 + 24 * X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = 44 * X ^ 7 + X ^ 8 := by
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
  have dP1 : d⁄dX ℚ (2 - 6 * X + 4 * X ^ 2 : PowerSeries ℚ) = -6 + 8 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (-X ^ 3 + X ^ 4 + 3 * X ^ 5 - 3 * X ^ 6 + 2 * X ^ 7 : PowerSeries ℚ) = -3 * X ^ 2 + 4 * X ^ 3 + 15 * X ^ 4 - 18 * X ^ 5 + 14 * X ^ 6 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (X ^ 3 - X ^ 4 - X ^ 5 + X ^ 6 : PowerSeries ℚ) = 3 * X ^ 2 - 4 * X ^ 3 - 5 * X ^ 4 + 6 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (-2 + 8 * X - 2 * X ^ 2 - 28 * X ^ 3 + 40 * X ^ 4 - 16 * X ^ 5) * (X * d⁄dX ℚ A) = (3 * X ^ 3 - 4 * X ^ 4 - 24 * X ^ 5 + 42 * X ^ 6 + 23 * X ^ 7 - 94 * X ^ 8 + 100 * X ^ 9 - 40 * X ^ 10) + (-3 * X ^ 3 + 4 * X ^ 4 + 18 * X ^ 5 - 34 * X ^ 6 - 7 * X ^ 7 + 42 * X ^ 8 - 20 * X ^ 9) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-2 * X + 2 * X ^ 2 + 8 * X ^ 3 - 8 * X ^ 4) * E1 + (-6 * X - 4 * X ^ 2 + 16 * X ^ 3) * L0 + (-X ^ 4 + 2 * X ^ 5 - 2 * X ^ 7 + X ^ 8) * hS1
  have dP2 : d⁄dX ℚ (-2 + 8 * X - 2 * X ^ 2 - 28 * X ^ 3 + 40 * X ^ 4 - 16 * X ^ 5 : PowerSeries ℚ) = 8 - 4 * X - 84 * X ^ 2 + 160 * X ^ 3 - 80 * X ^ 4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU2 : d⁄dX ℚ (3 * X ^ 3 - 4 * X ^ 4 - 24 * X ^ 5 + 42 * X ^ 6 + 23 * X ^ 7 - 94 * X ^ 8 + 100 * X ^ 9 - 40 * X ^ 10 : PowerSeries ℚ) = 9 * X ^ 2 - 16 * X ^ 3 - 120 * X ^ 4 + 252 * X ^ 5 + 161 * X ^ 6 - 752 * X ^ 7 + 900 * X ^ 8 - 400 * X ^ 9 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV2 : d⁄dX ℚ (-3 * X ^ 3 + 4 * X ^ 4 + 18 * X ^ 5 - 34 * X ^ 6 - 7 * X ^ 7 + 42 * X ^ 8 - 20 * X ^ 9 : PowerSeries ℚ) = -9 * X ^ 2 + 16 * X ^ 3 + 90 * X ^ 4 - 204 * X ^ 5 - 49 * X ^ 6 + 336 * X ^ 7 - 180 * X ^ 8 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E2 := th_step _ _ _ _ _ L1
  simp only [dP2, dU2, dV2] at E2
  have L2 : (-2 + 10 * X - 2 * X ^ 2 - 66 * X ^ 3 + 108 * X ^ 4 + 48 * X ^ 5 - 256 * X ^ 6 + 224 * X ^ 7 - 64 * X ^ 8) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = (9 * X ^ 3 - 13 * X ^ 4 - 126 * X ^ 5 + 276 * X ^ 6 + 333 * X ^ 7 - 1409 * X ^ 8 + 1030 * X ^ 9 + 1352 * X ^ 10 - 3488 * X ^ 11 + 2800 * X ^ 12 - 800 * X ^ 13) + (-9 * X ^ 3 + 13 * X ^ 4 + 108 * X ^ 5 - 250 * X ^ 6 - 233 * X ^ 7 + 1041 * X ^ 8 - 466 * X ^ 9 - 1076 * X ^ 10 + 1272 * X ^ 11 - 400 * X ^ 12) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 2 * X ^ 2 - 8 * X ^ 3 + 8 * X ^ 4) * E2 + (8 * X + 20 * X ^ 2 - 40 * X ^ 3) * L1 + (-3 * X ^ 4 + 7 * X ^ 5 + 14 * X ^ 6 - 52 * X ^ 7 + 27 * X ^ 8 + 49 * X ^ 9 - 62 * X ^ 10 + 20 * X ^ 11) * hS1
  have key : (2 - 10 * X + 2 * X ^ 2 + 66 * X ^ 3 - 108 * X ^ 4 - 48 * X ^ 5 + 256 * X ^ 6 - 224 * X ^ 7 + 64 * X ^ 8) * (((-159 + 206 * X + 573 * X ^ 2 - 1098 * X ^ 3 + 460 * X ^ 4) * (A) + (71 - 124 * X - 195 * X ^ 2 + 460 * X ^ 3 - 212 * X ^ 4) * (X * d⁄dX ℚ A) + (-6 + 12 * X + 18 * X ^ 2 - 48 * X ^ 3 + 24 * X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ A))) - (44 * X ^ 7 + X ^ 8)) = 0 := by
    linear_combination (-159 + 524 * X + 1274 * X ^ 2 - 6230 * X ^ 3 + 669 * X ^ 4 + 22670 * X ^ 5 - 25340 * X ^ 6 - 16464 * X ^ 7 + 47984 * X ^ 8 - 32288 * X ^ 9 + 7360 * X ^ 10) * L0 + (-71 + 195 * X + 355 * X ^ 2 - 1435 * X ^ 3 + 388 * X ^ 4 + 2408 * X ^ 5 - 2688 * X ^ 6 + 848 * X ^ 7) * L1 + (6 - 12 * X - 18 * X ^ 2 + 48 * X ^ 3 - 24 * X ^ 4) * L2
  have hne : (2 - 10 * X + 2 * X ^ 2 + 66 * X ^ 3 - 108 * X ^ 4 - 48 * X ^ 5 + 256 * X ^ 6 - 224 * X ^ 7 + 64 * X ^ 8 : PowerSeries ℚ) ≠ 0 := by
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

theorem gf_eq : (2 - 6 * X + 4 * X ^ 2) * ((-X ^ 3 + X ^ 4 + 3 * X ^ 5 - 3 * X ^ 6 + 2 * X ^ 7 + (X ^ 3 - X ^ 4 - X ^ 5 + X ^ 6) * S) * (2 - 6 * X + 4 * X ^ 2 : PowerSeries ℚ)⁻¹) = -X ^ 3 + X ^ 4 + 3 * X ^ 5 - 3 * X ^ 6 + 2 * X ^ 7 + (X ^ 3 - X ^ 4 - X ^ 5 + X ^ 6) * S := by
  have hd : constantCoeff (2 - 6 * X + 4 * X ^ 2 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (2 - 6 * X + 4 * X ^ 2 : PowerSeries ℚ) hd
  linear_combination (-X ^ 3 + X ^ 4 + 3 * X ^ 5 - 3 * X ^ 6 + 2 * X ^ 7 + (X ^ 3 - X ^ 4 - X ^ 5 + X ^ 6) * S) * hinv

end Pa191782

theorem OMA.solution : type_of% @OMA.S_oeis_a191782.main := by
  intro n hn
  have hL := Pa191782.gf_eq
  have ha : ∀ m, a m = coeff ((m + 6)) ((-X ^ 3 + X ^ 4 + 3 * X ^ 5 - 3 * X ^ 6 + 2 * X ^ 7 + (X ^ 3 - X ^ 4 - X ^ 5 + X ^ 6) * S) * (2 - 6 * X + 4 * X ^ 2 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((-X ^ 3 + X ^ 4 + 3 * X ^ 5 - 3 * X ^ 6 + 2 * X ^ 7 + (X ^ 3 - X ^ 4 - X ^ 5 + X ^ 6) * S) * (2 - 6 * X + 4 * X ^ 2 : PowerSeries ℚ)⁻¹) = A at hL ha
  have hL' : (2 - 6 * X + 4 * X ^ 2) * A = (-X ^ 3 + X ^ 4 + 3 * X ^ 5 - 3 * X ^ 6 + 2 * X ^ 7) + (X ^ 3 - X ^ 4 - X ^ 5 + X ^ 6) * S := by
    linear_combination hL
  have e := congrArg (coeff ((n + 6))) (Pa191782.ode S A Pa191782.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega, show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [Pa191782.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa191782.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
