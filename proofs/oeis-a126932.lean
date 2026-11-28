import OMAStatements.S_oeis_a126932
import Mathlib

open OMA.S_oeis_a126932
open PowerSeries

namespace P126932

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
    (hL : (4 - 26 * X + 42 * X ^ 2) * A = (3 - 9 * X) + (1) * S) :
    (-11 * X + 28 * X ^ 2 + 21 * X ^ 3) * (A) + (2 - 11 * X + 8 * X ^ 2 + 21 * X ^ 3) * (X * d⁄dX ℚ A) = -3 * X := by
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
  have dP1 : d⁄dX ℚ (4 - 26 * X + 42 * X ^ 2 : PowerSeries ℚ) = -26 + 84 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (3 - 9 * X : PowerSeries ℚ) = -9 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (1 : PowerSeries ℚ) = 0 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (-8 + 96 * X - 402 * X ^ 2 + 586 * X ^ 3 + 210 * X ^ 4 - 882 * X ^ 5) * (X * d⁄dX ℚ A) = (-21 * X + 105 * X ^ 2 - 63 * X ^ 3 - 189 * X ^ 4) + (-11 * X + 28 * X ^ 2 + 21 * X ^ 3) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-4 * X + 22 * X ^ 2 - 16 * X ^ 3 - 42 * X ^ 4) * E1 + (-26 * X + 58 * X ^ 2 + 84 * X ^ 3) * L0 + (-2 * X + 7 * X ^ 2) * hS1
  have key : (-8 + 96 * X - 402 * X ^ 2 + 586 * X ^ 3 + 210 * X ^ 4 - 882 * X ^ 5) * (((-11 * X + 28 * X ^ 2 + 21 * X ^ 3) * (A) + (2 - 11 * X + 8 * X ^ 2 + 21 * X ^ 3) * (X * d⁄dX ℚ A)) - (-3 * X)) = 0 := by
    linear_combination (22 * X - 177 * X ^ 2 + 354 * X ^ 3 + 238 * X ^ 4 - 756 * X ^ 5 - 441 * X ^ 6) * L0 + (2 - 11 * X + 8 * X ^ 2 + 21 * X ^ 3) * L1
  have hne : (-8 + 96 * X - 402 * X ^ 2 + 586 * X ^ 3 + 210 * X ^ 4 - 882 * X ^ 5 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 0
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

theorem B_sq : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = (1 + X : PowerSeries ℚ) := by
  rw [sq, ← PowerSeries.binomialSeries_add]
  norm_num
  simpa using binomialSeries_nat (A := ℚ) (R := ℚ) 1

theorem S_sq : root ^ 2 = 1 - 2 * X - 3 * X ^ 2 := by
  have h2 : (rescale (-3 : ℚ) (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ))) ^ 2 = 1 - 3 * X := by
    rw [← map_pow, B_sq, map_add, map_one, rescale_X]
    simp only [map_neg, map_ofNat]
    ring
  unfold root
  rw [mul_pow, B_sq, h2]
  ring

theorem gf_eq : (4 - 26 * X + 42 * X ^ 2) * generatingFunction = 3 - 9 * X + root := by
  have hd : constantCoeff (C 2 * (C 2 - C 13 * X + C 21 * X ^ 2) : PowerSeries ℚ) ≠ 0 := by
    simp
  have hinv := PowerSeries.mul_inv_cancel (C 2 * (C 2 - C 13 * X + C 21 * X ^ 2) : PowerSeries ℚ) hd
  unfold generatingFunction
  simp only [map_ofNat] at hinv ⊢
  linear_combination (root + 3 * (1 - 3 * X)) * hinv

end P126932

theorem OMA.solution : type_of% @OMA.S_oeis_a126932.main := by
  intro n hn
  have hL := P126932.gf_eq
  have ha : ∀ m, a m = coeff m generatingFunction := fun m => rfl
  generalize generatingFunction = A at hL ha
  have hL' : (4 - 26 * X + 42 * X ^ 2) * A = (3 - 9 * X) + (1) * root := by
    linear_combination hL
  have e := congrArg (coeff n) (P126932.ode root A P126932.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega, show k + 3 - 3 = k by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [P126932.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, P126932.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
