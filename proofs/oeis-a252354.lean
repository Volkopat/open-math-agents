import OMAStatements.S_oeis_a252354
import Mathlib

open OMA.S_oeis_a252354
open PowerSeries

namespace Pa252354

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
    (hL : (2 - 8 * X + 4 * X ^ 2 + 12 * X ^ 3 - 8 * X ^ 4 + 2 * X ^ 5) * A = (2 - 6 * X + 9 * X ^ 3 - 3 * X ^ 4) + (-X ^ 3) * S) :
    (3 - 15 * X + 10 * X ^ 2 + 30 * X ^ 3 - 14 * X ^ 4 - 24 * X ^ 5 + 3 * X ^ 6 + 3 * X ^ 7) * (A) + (-1 + 6 * X - 7 * X ^ 2 - 14 * X ^ 3 + 22 * X ^ 4 + 9 * X ^ 5 - 10 * X ^ 6 + 3 * X ^ 7) * (X * d⁄dX ℚ A) = 3 - 13 * X + 3 * X ^ 2 + 27 * X ^ 3 - 3 * X ^ 4 - 15 * X ^ 5 := by
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
  have dP1 : d⁄dX ℚ (2 - 8 * X + 4 * X ^ 2 + 12 * X ^ 3 - 8 * X ^ 4 + 2 * X ^ 5 : PowerSeries ℚ) = -8 + 8 * X + 36 * X ^ 2 - 32 * X ^ 3 + 10 * X ^ 4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (2 - 6 * X + 9 * X ^ 3 - 3 * X ^ 4 : PowerSeries ℚ) = -6 + 27 * X ^ 2 - 12 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (-X ^ 3 : PowerSeries ℚ) = -3 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (2 - 20 * X + 66 * X ^ 2 - 40 * X ^ 3 - 208 * X ^ 4 + 348 * X ^ 5 + 104 * X ^ 6 - 484 * X ^ 7 + 160 * X ^ 8 + 136 * X ^ 9 - 134 * X ^ 10 + 44 * X ^ 11 - 6 * X ^ 12) * (X * d⁄dX ℚ A) = (2 * X - 12 * X ^ 2 + 13 * X ^ 3 + 38 * X ^ 4 - 77 * X ^ 5 + 8 * X ^ 6 + 78 * X ^ 7 - 90 * X ^ 8 - 15 * X ^ 9 + 48 * X ^ 10 - 9 * X ^ 11) + (-3 * X ^ 3 + 15 * X ^ 4 - 10 * X ^ 5 - 30 * X ^ 6 + 14 * X ^ 7 + 24 * X ^ 8 - 3 * X ^ 9 - 3 * X ^ 10) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 12 * X ^ 2 + 14 * X ^ 3 + 28 * X ^ 4 - 44 * X ^ 5 - 18 * X ^ 6 + 20 * X ^ 7 - 6 * X ^ 8) * E1 + (8 * X - 24 * X ^ 2 - 44 * X ^ 3 + 128 * X ^ 4 + 34 * X ^ 5 - 76 * X ^ 6 + 30 * X ^ 7) * L0 + (-X ^ 4 + 4 * X ^ 5 - 2 * X ^ 6 - 6 * X ^ 7 + 4 * X ^ 8 - X ^ 9) * hS1
  have key : (2 - 20 * X + 66 * X ^ 2 - 40 * X ^ 3 - 208 * X ^ 4 + 348 * X ^ 5 + 104 * X ^ 6 - 484 * X ^ 7 + 160 * X ^ 8 + 136 * X ^ 9 - 134 * X ^ 10 + 44 * X ^ 11 - 6 * X ^ 12) * (((3 - 15 * X + 10 * X ^ 2 + 30 * X ^ 3 - 14 * X ^ 4 - 24 * X ^ 5 + 3 * X ^ 6 + 3 * X ^ 7) * (A) + (-1 + 6 * X - 7 * X ^ 2 - 14 * X ^ 3 + 22 * X ^ 4 + 9 * X ^ 5 - 10 * X ^ 6 + 3 * X ^ 7) * (X * d⁄dX ℚ A)) - (3 - 13 * X + 3 * X ^ 2 + 27 * X ^ 3 - 3 * X ^ 4 - 15 * X ^ 5)) = 0 := by
    linear_combination (3 - 33 * X + 121 * X ^ 2 - 93 * X ^ 3 - 400 * X ^ 4 + 713 * X ^ 5 + 414 * X ^ 6 - 1288 * X ^ 7 - 150 * X ^ 8 + 987 * X ^ 9 - 38 * X ^ 10 - 291 * X ^ 11 + 75 * X ^ 12 + 21 * X ^ 13 - 9 * X ^ 14) * L0 + (-1 + 6 * X - 7 * X ^ 2 - 14 * X ^ 3 + 22 * X ^ 4 + 9 * X ^ 5 - 10 * X ^ 6 + 3 * X ^ 7) * L1
  have hne : (2 - 20 * X + 66 * X ^ 2 - 40 * X ^ 3 - 208 * X ^ 4 + 348 * X ^ 5 + 104 * X ^ 6 - 484 * X ^ 7 + 160 * X ^ 8 + 136 * X ^ 9 - 134 * X ^ 10 + 44 * X ^ 11 - 6 * X ^ 12 : PowerSeries ℚ) ≠ 0 := by
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

theorem gf_eq : (2 - 8 * X + 4 * X ^ 2 + 12 * X ^ 3 - 8 * X ^ 4 + 2 * X ^ 5) * ((2 - 6 * X + 9 * X ^ 3 - 3 * X ^ 4 + (-X ^ 3) * S) * (2 - 8 * X + 4 * X ^ 2 + 12 * X ^ 3 - 8 * X ^ 4 + 2 * X ^ 5 : PowerSeries ℚ)⁻¹) = 2 - 6 * X + 9 * X ^ 3 - 3 * X ^ 4 + (-X ^ 3) * S := by
  have hd : constantCoeff (2 - 8 * X + 4 * X ^ 2 + 12 * X ^ 3 - 8 * X ^ 4 + 2 * X ^ 5 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (2 - 8 * X + 4 * X ^ 2 + 12 * X ^ 3 - 8 * X ^ 4 + 2 * X ^ 5 : PowerSeries ℚ) hd
  linear_combination (2 - 6 * X + 9 * X ^ 3 - 3 * X ^ 4 + (-X ^ 3) * S) * hinv

end Pa252354

theorem OMA.solution : type_of% @OMA.S_oeis_a252354.main := by
  intro n hn
  have hL := Pa252354.gf_eq
  have ha : ∀ m, a m = coeff (m) ((2 - 6 * X + 9 * X ^ 3 - 3 * X ^ 4 + (-X ^ 3) * S) * (2 - 8 * X + 4 * X ^ 2 + 12 * X ^ 3 - 8 * X ^ 4 + 2 * X ^ 5 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((2 - 6 * X + 9 * X ^ 3 - 3 * X ^ 4 + (-X ^ 3) * S) * (2 - 8 * X + 4 * X ^ 2 + 12 * X ^ 3 - 8 * X ^ 4 + 2 * X ^ 5 : PowerSeries ℚ)⁻¹) = A at hL ha
  have hL' : (2 - 8 * X + 4 * X ^ 2 + 12 * X ^ 3 - 8 * X ^ 4 + 2 * X ^ 5) * A = (2 - 6 * X + 9 * X ^ 3 - 3 * X ^ 4) + (-X ^ 3) * S := by
    linear_combination hL
  have e := congrArg (coeff (n)) (Pa252354.ode S A Pa252354.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  simp only [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega, show k + 7 - 3 = k + 4 by omega, show k + 7 - 4 = k + 3 by omega, show k + 7 - 5 = k + 2 by omega, show k + 7 - 6 = k + 1 by omega, show k + 7 - 7 = k by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [Pa252354.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa252354.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
