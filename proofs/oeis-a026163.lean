import OMAStatements.S_oeis_a026163
import Mathlib

open OMA.S_oeis_a026163
open PowerSeries

namespace Pa026163

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
theorem ode (S A : PowerSeries ℚ) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hL : (2) * A = (1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 4 + 2 * X ^ 5) + (-1 + 5 * X - 7 * X ^ 2 + X ^ 3 + 2 * X ^ 4) * S) :
    (294 * X + 412 * X ^ 2 - 2100 * X ^ 3 - 2430 * X ^ 4) * (A) + (52 - 69 * X - 586 * X ^ 2 + 662 * X ^ 3 + 1041 * X ^ 4) * (X * d⁄dX ℚ A) + (-3 - 3 * X + 64 * X ^ 2 - 47 * X ^ 3 - 111 * X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = 224 * X ^ 8 := by
  have hdD : d⁄dX ℚ (1 - 2 * X - 3 * X ^ 2 : PowerSeries ℚ) = -2 - 6 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have hS1 := sq_step S _ hS
  rw [hdD] at hS1
  have L0 := hL
  have dP1 : d⁄dX ℚ (2 : PowerSeries ℚ) = 0 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 4 + 2 * X ^ 5 : PowerSeries ℚ) = -6 + 20 * X - 36 * X ^ 3 + 10 * X ^ 4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (-1 + 5 * X - 7 * X ^ 2 + X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ) = 5 - 14 * X + 3 * X ^ 2 + 8 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (1 - 2 * X - 3 * X ^ 2) * (X * d⁄dX ℚ A) = (-3 * X + 16 * X ^ 2 - 11 * X ^ 3 - 48 * X ^ 4 + 41 * X ^ 5 + 44 * X ^ 6 - 15 * X ^ 7) + (3 * X - 13 * X ^ 2 + 4 * X ^ 3 + 32 * X ^ 4 - 15 * X ^ 5 - 15 * X ^ 6) * S := by
    have hg : (4 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 4 * X ^ 2 - 6 * X ^ 3) * E1 + (0) * L0 + (-X + 5 * X ^ 2 - 7 * X ^ 3 + X ^ 4 + 2 * X ^ 5) * hS1
  have dP2 : d⁄dX ℚ (1 - 2 * X - 3 * X ^ 2 : PowerSeries ℚ) = -2 - 6 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU2 : d⁄dX ℚ (-3 * X + 16 * X ^ 2 - 11 * X ^ 3 - 48 * X ^ 4 + 41 * X ^ 5 + 44 * X ^ 6 - 15 * X ^ 7 : PowerSeries ℚ) = -3 + 32 * X - 33 * X ^ 2 - 192 * X ^ 3 + 205 * X ^ 4 + 264 * X ^ 5 - 105 * X ^ 6 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV2 : d⁄dX ℚ (3 * X - 13 * X ^ 2 + 4 * X ^ 3 + 32 * X ^ 4 - 15 * X ^ 5 - 15 * X ^ 6 : PowerSeries ℚ) = 3 - 26 * X + 12 * X ^ 2 + 128 * X ^ 3 - 75 * X ^ 4 - 90 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E2 := th_step _ _ _ _ _ L1
  simp only [dP2, dU2, dV2] at E2
  have L2 : (-1 + 4 * X + 2 * X ^ 2 - 12 * X ^ 3 - 9 * X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = (3 * X - 32 * X ^ 2 + 74 * X ^ 3 + 148 * X ^ 4 - 526 * X ^ 5 - 224 * X ^ 6 + 914 * X ^ 7 + 348 * X ^ 8 - 225 * X ^ 9) + (-3 * X + 29 * X ^ 2 - 51 * X ^ 3 - 147 * X ^ 4 + 323 * X ^ 5 + 243 * X ^ 6 - 345 * X ^ 7 - 225 * X ^ 8) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-2 * X + 4 * X ^ 2 + 6 * X ^ 3) * E2 + (-4 * X - 12 * X ^ 2) * L1 + (-3 * X ^ 2 + 13 * X ^ 3 - 4 * X ^ 4 - 32 * X ^ 5 + 15 * X ^ 6 + 15 * X ^ 7) * hS1
  have key : (2 - 8 * X - 4 * X ^ 2 + 24 * X ^ 3 + 18 * X ^ 4) * (((294 * X + 412 * X ^ 2 - 2100 * X ^ 3 - 2430 * X ^ 4) * (A) + (52 - 69 * X - 586 * X ^ 2 + 662 * X ^ 3 + 1041 * X ^ 4) * (X * d⁄dX ℚ A) + (-3 - 3 * X + 64 * X ^ 2 - 47 * X ^ 3 - 111 * X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ A))) - (224 * X ^ 8)) = 0 := by
    linear_combination (294 * X - 764 * X ^ 2 - 4336 * X ^ 3 + 8674 * X ^ 4 + 21510 * X ^ 5 - 16632 * X ^ 6 - 48060 * X ^ 7 - 21870 * X ^ 8) * L0 + (104 - 346 * X - 1208 * X ^ 2 + 4082 * X ^ 3 + 2950 * X ^ 4 - 8136 * X ^ 5 - 6246 * X ^ 6) * L1 + (6 + 6 * X - 128 * X ^ 2 + 94 * X ^ 3 + 222 * X ^ 4) * L2
  have hne : (2 - 8 * X - 4 * X ^ 2 + 24 * X ^ 3 + 18 * X ^ 4 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 0
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

theorem S_sq : S ^ 2 = 1 - 2 * X - 3 * X ^ 2 := by
  have hB : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = (1 + X : PowerSeries ℚ) := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    norm_num
    simpa using binomialSeries_nat (A := ℚ) (R := ℚ) 1
  have h0 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow h0, hB, ← coe_substAlgHom h0, map_add, map_one,
    coe_substAlgHom, subst_X h0, R]
  ring

theorem gf_eq : (2) * ((1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 4 + 2 * X ^ 5 + (-1 + 5 * X - 7 * X ^ 2 + X ^ 3 + 2 * X ^ 4) * S) * (2 : PowerSeries ℚ)⁻¹) = 1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 4 + 2 * X ^ 5 + (-1 + 5 * X - 7 * X ^ 2 + X ^ 3 + 2 * X ^ 4) * S := by
  have hd : constantCoeff (2 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (2 : PowerSeries ℚ) hd
  linear_combination (1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 4 + 2 * X ^ 5 + (-1 + 5 * X - 7 * X ^ 2 + X ^ 3 + 2 * X ^ 4) * S) * hinv

end Pa026163

theorem OMA.solution : type_of% @OMA.S_oeis_a026163.main := by
  intro n hn
  have hL := Pa026163.gf_eq
  have ha : ∀ m, a m = coeff (m + 7) ((1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 4 + 2 * X ^ 5 + (-1 + 5 * X - 7 * X ^ 2 + X ^ 3 + 2 * X ^ 4) * S) * (2 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 4 + 2 * X ^ 5 + (-1 + 5 * X - 7 * X ^ 2 + X ^ 3 + 2 * X ^ 4) * S) * (2 : PowerSeries ℚ)⁻¹) = A at hL ha
  have hL' : (2) * A = (1 - 6 * X + 10 * X ^ 2 - 9 * X ^ 4 + 2 * X ^ 5) + (-1 + 5 * X - 7 * X ^ 2 + X ^ 3 + 2 * X ^ 4) * S := by
    linear_combination hL
  have e := congrArg (coeff (n + 7)) (Pa026163.ode S A Pa026163.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega, show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [Pa026163.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa026163.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
