import OMAStatements.S_oeis_a171853
import Mathlib

open OMA.S_oeis_a171853
open PowerSeries

namespace Pa171853

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
theorem ode (S A : PowerSeries ℚ) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hL : (2 - 6 * X + 4 * X ^ 3 + 4 * X ^ 4 - 6 * X ^ 6 + 2 * X ^ 7) * A = (-X + 2 * X ^ 2 + X ^ 3 + 2 * X ^ 4 - X ^ 5) + (X - X ^ 2 + X ^ 3) * S) :
    (1 - 2 * X + 5 * X ^ 2 - 7 * X ^ 3 - 5 * X ^ 4 - 7 * X ^ 5 + 6 * X ^ 6 - 5 * X ^ 7 + 2 * X ^ 8) * (A) + (-1 + 3 * X - X ^ 2 + X ^ 6 - 3 * X ^ 7 + X ^ 8) * (X * d⁄dX ℚ A) = -2 * X ^ 3 - 2 * X ^ 4 := by
  have hdD : d⁄dX ℚ (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 : PowerSeries ℚ) = -2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have hS1 := sq_step S _ hS
  rw [hdD] at hS1
  have L0 := hL
  have dP1 : d⁄dX ℚ (2 - 6 * X + 4 * X ^ 3 + 4 * X ^ 4 - 6 * X ^ 6 + 2 * X ^ 7 : PowerSeries ℚ) = -6 + 12 * X ^ 2 + 16 * X ^ 3 - 36 * X ^ 5 + 14 * X ^ 6 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (-X + 2 * X ^ 2 + X ^ 3 + 2 * X ^ 4 - X ^ 5 : PowerSeries ℚ) = -1 + 4 * X + 3 * X ^ 2 + 8 * X ^ 3 - 5 * X ^ 4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (X - X ^ 2 + X ^ 3 : PowerSeries ℚ) = 1 - 2 * X + 3 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (-2 + 10 * X - 8 * X ^ 2 - 16 * X ^ 3 + 24 * X ^ 5 + 28 * X ^ 6 - 28 * X ^ 7 - 24 * X ^ 8 + 16 * X ^ 10 + 8 * X ^ 11 - 10 * X ^ 12 + 2 * X ^ 13) * (X * d⁄dX ℚ A) = (X - 3 * X ^ 2 - 6 * X ^ 4 + 15 * X ^ 5 + 11 * X ^ 6 + 24 * X ^ 7 - 2 * X ^ 8 + X ^ 9 - 7 * X ^ 10 + 2 * X ^ 11) + (-X + 2 * X ^ 2 - 5 * X ^ 3 + 7 * X ^ 4 + 5 * X ^ 5 + 7 * X ^ 6 - 6 * X ^ 7 + 5 * X ^ 8 - 2 * X ^ 9) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-2 * X + 4 * X ^ 2 + 4 * X ^ 3 - 4 * X ^ 5 - 4 * X ^ 6 + 2 * X ^ 7) * E1 + (-6 * X - 6 * X ^ 2 + 6 * X ^ 3 + 22 * X ^ 4 + 22 * X ^ 5 - 14 * X ^ 6) * L0 + (-X ^ 2 + X ^ 3 - X ^ 5 + X ^ 6) * hS1
  have key : (-2 + 10 * X - 8 * X ^ 2 - 16 * X ^ 3 + 24 * X ^ 5 + 28 * X ^ 6 - 28 * X ^ 7 - 24 * X ^ 8 + 16 * X ^ 10 + 8 * X ^ 11 - 10 * X ^ 12 + 2 * X ^ 13) * (((1 - 2 * X + 5 * X ^ 2 - 7 * X ^ 3 - 5 * X ^ 4 - 7 * X ^ 5 + 6 * X ^ 6 - 5 * X ^ 7 + 2 * X ^ 8) * (A) + (-1 + 3 * X - X ^ 2 + X ^ 6 - 3 * X ^ 7 + X ^ 8) * (X * d⁄dX ℚ A)) - (-2 * X ^ 3 - 2 * X ^ 4)) = 0 := by
    linear_combination (-1 + 4 * X - 7 * X ^ 2 + 13 * X ^ 3 - X ^ 4 - 15 * X ^ 5 - 35 * X ^ 6 + 5 * X ^ 7 + 29 * X ^ 8 + 11 * X ^ 9 + X ^ 10 - 9 * X ^ 11 + 12 * X ^ 12 - 9 * X ^ 13 + 2 * X ^ 14) * L0 + (-1 + 3 * X - X ^ 2 + X ^ 6 - 3 * X ^ 7 + X ^ 8) * L1
  have hne : (-2 + 10 * X - 8 * X ^ 2 - 16 * X ^ 3 + 24 * X ^ 5 + 28 * X ^ 6 - 28 * X ^ 7 - 24 * X ^ 8 + 16 * X ^ 10 + 8 * X ^ 11 - 10 * X ^ 12 + 2 * X ^ 13 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 0
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

theorem S_sq : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 := by
  have hB : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = (1 + X : PowerSeries ℚ) := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    norm_num
    simpa using binomialSeries_nat (A := ℚ) (R := ℚ) 1
  have h0 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow h0, hB, ← coe_substAlgHom h0, map_add, map_one,
    coe_substAlgHom, subst_X h0, R]
  ring

theorem gf_eq : (2 - 6 * X + 4 * X ^ 3 + 4 * X ^ 4 - 6 * X ^ 6 + 2 * X ^ 7) * ((-X + 2 * X ^ 2 + X ^ 3 + 2 * X ^ 4 - X ^ 5 + (X - X ^ 2 + X ^ 3) * S) * (2 - 6 * X + 4 * X ^ 3 + 4 * X ^ 4 - 6 * X ^ 6 + 2 * X ^ 7 : PowerSeries ℚ)⁻¹) = -X + 2 * X ^ 2 + X ^ 3 + 2 * X ^ 4 - X ^ 5 + (X - X ^ 2 + X ^ 3) * S := by
  have hd : constantCoeff (2 - 6 * X + 4 * X ^ 3 + 4 * X ^ 4 - 6 * X ^ 6 + 2 * X ^ 7 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (2 - 6 * X + 4 * X ^ 3 + 4 * X ^ 4 - 6 * X ^ 6 + 2 * X ^ 7 : PowerSeries ℚ) hd
  linear_combination (-X + 2 * X ^ 2 + X ^ 3 + 2 * X ^ 4 - X ^ 5 + (X - X ^ 2 + X ^ 3) * S) * hinv

end Pa171853

theorem OMA.solution : type_of% @OMA.S_oeis_a171853.main := by
  intro n hn
  have hL := Pa171853.gf_eq
  have ha : ∀ m, a m = coeff (m) ((-X + 2 * X ^ 2 + X ^ 3 + 2 * X ^ 4 - X ^ 5 + (X - X ^ 2 + X ^ 3) * S) * (2 - 6 * X + 4 * X ^ 3 + 4 * X ^ 4 - 6 * X ^ 6 + 2 * X ^ 7 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((-X + 2 * X ^ 2 + X ^ 3 + 2 * X ^ 4 - X ^ 5 + (X - X ^ 2 + X ^ 3) * S) * (2 - 6 * X + 4 * X ^ 3 + 4 * X ^ 4 - 6 * X ^ 6 + 2 * X ^ 7 : PowerSeries ℚ)⁻¹) = A at hL ha
  have hL' : (2 - 6 * X + 4 * X ^ 3 + 4 * X ^ 4 - 6 * X ^ 6 + 2 * X ^ 7) * A = (-X + 2 * X ^ 2 + X ^ 3 + 2 * X ^ 4 - X ^ 5) + (X - X ^ 2 + X ^ 3) * S := by
    linear_combination hL
  have e := congrArg (coeff (n)) (Pa171853.ode S A Pa171853.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
  simp only [show k + 8 - 1 = k + 7 by omega, show k + 8 - 2 = k + 6 by omega, show k + 8 - 3 = k + 5 by omega, show k + 8 - 4 = k + 4 by omega, show k + 8 - 5 = k + 3 by omega, show k + 8 - 6 = k + 2 by omega, show k + 8 - 7 = k + 1 by omega, show k + 8 - 8 = k by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [Pa171853.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa171853.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
