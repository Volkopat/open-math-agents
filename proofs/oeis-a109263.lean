import OMAStatements.S_oeis_a109263
import Mathlib

open OMA.S_oeis_a109263
open PowerSeries

namespace Pa109263

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


theorem facts : ∃ T : PowerSeries ℚ, T ^ 2 = 1 - 4 * X ∧
    (-4 + 16 * X + 4 * X ^ 2) * A = (2 - 6 * X - 4 * X ^ 2) + (-2 + 2 * X) * T := by
  have hc := cat_eq
  have hu : constantCoeff (X * c) = 0 := by simp
  have ha := HasSubst.of_constantCoeff_zero' hu
  have hq : constantCoeff (1 - X - X ^ 2 : PowerSeries ℚ) ≠ 0 := by simp
  have hG : G * (1 - X - X ^ 2) = X ^ 2 := by
    rw [G, mul_assoc, PowerSeries.inv_mul_cancel _ hq, mul_one]
  have h1 := congrArg (substAlgHom ha) hG
  rw [map_mul, map_sub, map_sub, map_pow, map_one, substAlgHom_X, coe_substAlgHom] at h1
  have hA : A * (1 - X * c - (X * c) ^ 2) = (X * c) ^ 2 := h1
  have hT : (1 - 2 * X * c) ^ 2 = 1 - 4 * X := by linear_combination 4 * X * hc
  have hRT : (2 * X + 2 * (1 - 2 * X * c)) * A = 1 - 2 * X - (1 - 2 * X * c) := by
    linear_combination 2 * hA + 2 * X * (A + 1) * hc
  refine ⟨(1 - 2 * X * c), by linear_combination hT, ?_⟩
  linear_combination ((2 * X) - (2) * (1 - 2 * X * c)) * hRT + ((2) ^ 2 * A - (-1) * (2)) * hT

set_option maxHeartbeats 2000000 in
theorem ode (S A : PowerSeries ℚ) (hS : S ^ 2 = 1 - 4 * X)
    (hL : (-4 + 16 * X + 4 * X ^ 2) * A = (2 - 6 * X - 4 * X ^ 2) + (-2 + 2 * X) * S) :
    (2 * X + 2 * X ^ 2 + 2 * X ^ 3) * (A) + (-3 + 14 * X - 9 * X ^ 2 + 6 * X ^ 3) * (X * d⁄dX ℚ A) + (1 - 8 * X + 15 * X ^ 2 + 4 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = -2 * X ^ 2 - 2 * X ^ 3 := by
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
  have dP1 : d⁄dX ℚ (-4 + 16 * X + 4 * X ^ 2 : PowerSeries ℚ) = 16 + 8 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (2 - 6 * X - 4 * X ^ 2 : PowerSeries ℚ) = -6 - 8 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (-2 + 2 * X : PowerSeries ℚ) = 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (2 - 24 * X + 92 * X ^ 2 - 96 * X ^ 3 - 62 * X ^ 4 - 8 * X ^ 5) * (X * d⁄dX ℚ A) = (-X + 6 * X ^ 2 - 13 * X ^ 3 + 20 * X ^ 4) + (X - 15 * X ^ 3 + 2 * X ^ 4) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-X + 8 * X ^ 2 - 15 * X ^ 3 - 4 * X ^ 4) * E1 + (-4 * X + 14 * X ^ 2 + 8 * X ^ 3) * L0 + (X - 5 * X ^ 2 + 3 * X ^ 3 + X ^ 4) * hS1
  have dP2 : d⁄dX ℚ (2 - 24 * X + 92 * X ^ 2 - 96 * X ^ 3 - 62 * X ^ 4 - 8 * X ^ 5 : PowerSeries ℚ) = -24 + 184 * X - 288 * X ^ 2 - 248 * X ^ 3 - 40 * X ^ 4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU2 : d⁄dX ℚ (-X + 6 * X ^ 2 - 13 * X ^ 3 + 20 * X ^ 4 : PowerSeries ℚ) = -1 + 12 * X - 39 * X ^ 2 + 80 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV2 : d⁄dX ℚ (X - 15 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ) = 1 - 45 * X ^ 2 + 8 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E2 := th_step _ _ _ _ _ L1
  simp only [dP2, dU2, dV2] at E2
  have L2 : (2 - 40 * X + 314 * X ^ 2 - 1184 * X ^ 3 + 1990 * X ^ 4 - 584 * X ^ 5 - 1250 * X ^ 6 - 368 * X ^ 7 - 32 * X ^ 8) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = (-X + 8 * X ^ 2 - 34 * X ^ 3 + 168 * X ^ 4 - 485 * X ^ 5 + 424 * X ^ 6 - 80 * X ^ 7) + (X + 2 * X ^ 2 - 66 * X ^ 3 + 204 * X ^ 4 - 179 * X ^ 5 + 138 * X ^ 6 - 4 * X ^ 7) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 16 * X ^ 2 + 30 * X ^ 3 + 8 * X ^ 4) * E2 + (24 * X - 88 * X ^ 2 - 40 * X ^ 3) * L1 + (X ^ 2 - 4 * X ^ 3 - 16 * X ^ 4 + 62 * X ^ 5 + 7 * X ^ 6 - 2 * X ^ 7) * hS1
  have key : (-4 + 80 * X - 628 * X ^ 2 + 2368 * X ^ 3 - 3980 * X ^ 4 + 1168 * X ^ 5 + 2500 * X ^ 6 + 736 * X ^ 7 + 64 * X ^ 8) * (((2 * X + 2 * X ^ 2 + 2 * X ^ 3) * (A) + (-3 + 14 * X - 9 * X ^ 2 + 6 * X ^ 3) * (X * d⁄dX ℚ A) + (1 - 8 * X + 15 * X ^ 2 + 4 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ A))) - (-2 * X ^ 2 - 2 * X ^ 3)) = 0 := by
    linear_combination (2 * X - 30 * X ^ 2 + 158 * X ^ 3 - 308 * X ^ 4 + 46 * X ^ 5 + 98 * X ^ 6 + 594 * X ^ 7 + 272 * X ^ 8 + 32 * X ^ 9) * L0 + (6 - 76 * X + 332 * X ^ 2 - 552 * X ^ 3 + 254 * X ^ 4 - 108 * X ^ 5 - 48 * X ^ 6) * L1 + (-2 + 16 * X - 30 * X ^ 2 - 8 * X ^ 3) * L2
  have hne : (-4 + 80 * X - 628 * X ^ 2 + 2368 * X ^ 3 - 3980 * X ^ 4 + 1168 * X ^ 5 + 2500 * X ^ 6 + 736 * X ^ 7 + 64 * X ^ 8 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 0
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

end Pa109263

theorem OMA.solution : type_of% @OMA.S_oeis_a109263.main := by
  intro n hn
  obtain ⟨T, hT, hL⟩ := Pa109263.facts
  have e := congrArg (coeff n) (Pa109263.ode T A hT hL)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega]
  simp only [Pa109263.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa109263.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
