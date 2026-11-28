import OMAStatements.S_oeis_a157125
import Mathlib

open OMA.S_oeis_a157125
open PowerSeries

namespace Pa157125

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

noncomputable def cat : PowerSeries ℚ := map (Nat.castRingHom ℚ) catalanSeries

theorem cat_eq' : cat ^ 2 * X + 1 = cat := by
  have := congrArg (map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
  simpa [cat] using this

theorem h4 : (4 : PowerSeries ℚ) * C (1 / 4) = 1 := by
  rw [nC, ← map_mul]; norm_num

theorem sqrt_exists (u : PowerSeries ℚ) (hu : constantCoeff u = 0) :
    ∃ S : PowerSeries ℚ, S ^ 2 = 1 - 4 * u ∧ constantCoeff S = 1 := by
  have ha := HasSubst.of_constantCoeff_zero' hu
  have hc := congrArg (substAlgHom ha) cat_eq'
  rw [map_add, map_mul, map_pow, map_one, substAlgHom_X] at hc
  refine ⟨1 - 2 * u * substAlgHom ha cat, ?_, ?_⟩
  · linear_combination (4 * u) * hc
  · simp [hu]

theorem exists_gf : ∃ S1 S2 A : PowerSeries ℚ, IsGF S1 S2 A := by
  obtain ⟨S2, hS2, hS20⟩ := sqrt_exists ((1 - (1 + X ^ 2)) * C (1 / 4)) (by simp)
  have hS2' : S2 ^ 2 = 1 + X ^ 2 := by linear_combination hS2 - (1 - (1 + X ^ 2)) * h4
  have hq : constantCoeff (1 + X ^ 2 : PowerSeries ℚ) ≠ 0 := by simp
  set W : PowerSeries ℚ := (1 + X ^ 2 : PowerSeries ℚ)⁻¹ with hWdef
  have hW : (1 + X ^ 2) * W = 1 := PowerSeries.mul_inv_cancel _ hq
  have hu : constantCoeff (-(X ^ 3 * W)) = 0 := by simp
  have ha := HasSubst.of_constantCoeff_zero' hu
  have hc := congrArg (substAlgHom ha) cat_eq'
  rw [map_add, map_mul, map_pow, map_one, substAlgHom_X] at hc
  set K := substAlgHom ha cat with hK
  refine ⟨S2 * (1 + 2 * X ^ 3 * W * K), S2, (1 - X) * W * K, ?_, ?_, hS2', hS20, ?_⟩
  · linear_combination (1 + 2 * X ^ 3 * W * K) ^ 2 * hS2' - 4 * X ^ 3 * W * (1 + X ^ 2) * hc +
      4 * X ^ 3 * hW
  · simp [hS20]
  · ring

theorem facts (S1 S2 A : PowerSeries ℚ) (h : IsGF S1 S2 A) : ∃ T : PowerSeries ℚ, T ^ 2 = 1 + 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4 + 4 * X ^ 5 ∧
    (4 * X ^ 6 + 8 * X ^ 8 + 4 * X ^ 10) * A = (-2 * X ^ 3 + 2 * X ^ 4 - 4 * X ^ 5 + 4 * X ^ 6 - 2 * X ^ 7 + 2 * X ^ 8) + (2 * X ^ 3 - 2 * X ^ 4 + 2 * X ^ 5 - 2 * X ^ 6) * T := by
  obtain ⟨h1, _, h2, _, hA⟩ := h
  have hT : (S1 * S2) ^ 2 = (1 + X ^ 2 + 4 * X ^ 3) * (1 + X ^ 2) := by
    linear_combination S2 ^ 2 * h1 + (1 + X ^ 2 + 4 * X ^ 3) * h2
  have hRT : (2 * X ^ 3 * (1 + X ^ 2)) * A = -(1 - X) * (1 + X ^ 2) + (1 - X) * (S1 * S2) := by
    linear_combination S2 * hA - (2 * X ^ 3 * A + 1 - X) * h2
  refine ⟨(S1 * S2), by linear_combination hT, ?_⟩
  linear_combination ((2 * X ^ 3 + 2 * X ^ 5) - (0) * (S1 * S2)) * hRT + ((0) ^ 2 * A - (1 - X) * (0)) * hT

set_option maxHeartbeats 2000000 in
theorem ode (S A : PowerSeries ℚ) (hS : S ^ 2 = 1 + 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4 + 4 * X ^ 5)
    (hL : (4 * X ^ 6 + 8 * X ^ 8 + 4 * X ^ 10) * A = (-2 * X ^ 3 + 2 * X ^ 4 - 4 * X ^ 5 + 4 * X ^ 6 - 2 * X ^ 7 + 2 * X ^ 8) + (2 * X ^ 3 - 2 * X ^ 4 + 2 * X ^ 5 - 2 * X ^ 6) * S) :
    (-6 - 4 * X - 4 * X ^ 2 - 2 * X ^ 3 + 24 * X ^ 5) * (A) + (1 + 6 * X ^ 2 + 10 * X ^ 3 + 5 * X ^ 4 + 22 * X ^ 5) * (X * d⁄dX ℚ A) + (1 + 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4 + 4 * X ^ 5) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = -6 - 2 * X ^ 3 := by
  have hdD : d⁄dX ℚ (1 + 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4 + 4 * X ^ 5 : PowerSeries ℚ) = 4 * X + 12 * X ^ 2 + 4 * X ^ 3 + 20 * X ^ 4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have hS1 := sq_step S _ hS
  rw [hdD] at hS1
  have L0 := hL
  have dP1 : d⁄dX ℚ (4 * X ^ 6 + 8 * X ^ 8 + 4 * X ^ 10 : PowerSeries ℚ) = 24 * X ^ 5 + 64 * X ^ 7 + 40 * X ^ 9 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (-2 * X ^ 3 + 2 * X ^ 4 - 4 * X ^ 5 + 4 * X ^ 6 - 2 * X ^ 7 + 2 * X ^ 8 : PowerSeries ℚ) = -6 * X ^ 2 + 8 * X ^ 3 - 20 * X ^ 4 + 24 * X ^ 5 - 14 * X ^ 6 + 16 * X ^ 7 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (2 * X ^ 3 - 2 * X ^ 4 + 2 * X ^ 5 - 2 * X ^ 6 : PowerSeries ℚ) = 6 * X ^ 2 - 8 * X ^ 3 + 10 * X ^ 4 - 12 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (2 * X ^ 3 + 6 * X ^ 5 + 8 * X ^ 6 + 6 * X ^ 7 + 16 * X ^ 8 + 2 * X ^ 9 + 8 * X ^ 10) * (X * d⁄dX ℚ A) = (3 - 2 * X + 9 * X ^ 2 + 6 * X ^ 3 + X ^ 4 + 18 * X ^ 5 - 13 * X ^ 6 + 10 * X ^ 7 - 8 * X ^ 8) + (-3 + 2 * X - 6 * X ^ 2 - 2 * X ^ 3 - X ^ 4 - 8 * X ^ 5 + 6 * X ^ 6) * S := by
    have hg : (2 * X ^ 3 + 2 * X ^ 5 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 3
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (X + 2 * X ^ 3 + 4 * X ^ 4 + X ^ 5 + 4 * X ^ 6) * E1 + (-6 - 16 * X ^ 2 - 24 * X ^ 3 - 10 * X ^ 4 - 40 * X ^ 5) * L0 + (X ^ 4 - X ^ 5 + X ^ 6 - X ^ 7) * hS1
  have dP2 : d⁄dX ℚ (2 * X ^ 3 + 6 * X ^ 5 + 8 * X ^ 6 + 6 * X ^ 7 + 16 * X ^ 8 + 2 * X ^ 9 + 8 * X ^ 10 : PowerSeries ℚ) = 6 * X ^ 2 + 30 * X ^ 4 + 48 * X ^ 5 + 42 * X ^ 6 + 128 * X ^ 7 + 18 * X ^ 8 + 80 * X ^ 9 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU2 : d⁄dX ℚ (3 - 2 * X + 9 * X ^ 2 + 6 * X ^ 3 + X ^ 4 + 18 * X ^ 5 - 13 * X ^ 6 + 10 * X ^ 7 - 8 * X ^ 8 : PowerSeries ℚ) = -2 + 18 * X + 18 * X ^ 2 + 4 * X ^ 3 + 90 * X ^ 4 - 78 * X ^ 5 + 70 * X ^ 6 - 64 * X ^ 7 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV2 : d⁄dX ℚ (-3 + 2 * X - 6 * X ^ 2 - 2 * X ^ 3 - X ^ 4 - 8 * X ^ 5 + 6 * X ^ 6 : PowerSeries ℚ) = 2 - 12 * X - 6 * X ^ 2 - 4 * X ^ 3 - 40 * X ^ 4 + 36 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E2 := th_step _ _ _ _ _ L1
  simp only [dP2, dU2, dV2] at E2
  have L2 : (2 * X ^ 3 + 10 * X ^ 5 + 16 * X ^ 6 + 20 * X ^ 7 + 64 * X ^ 8 + 52 * X ^ 9 + 96 * X ^ 10 + 106 * X ^ 11 + 64 * X ^ 12 + 98 * X ^ 13 + 16 * X ^ 14 + 32 * X ^ 15) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = (-9 + 4 * X - 45 * X ^ 2 - 52 * X ^ 3 - 58 * X ^ 4 - 248 * X ^ 5 - 106 * X ^ 6 - 328 * X ^ 7 - 285 * X ^ 8 - 76 * X ^ 9 - 313 * X ^ 10 + 124 * X ^ 11 - 112 * X ^ 12 + 64 * X ^ 13) + (9 - 4 * X + 36 * X ^ 2 + 38 * X ^ 3 + 28 * X ^ 4 + 130 * X ^ 5 + 10 * X ^ 6 + 142 * X ^ 7 + 35 * X ^ 8 + 66 * X ^ 9 + 74 * X ^ 10 - 36 * X ^ 11) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X + 4 * X ^ 3 + 8 * X ^ 4 + 2 * X ^ 5 + 8 * X ^ 6) * E2 + (-6 - 24 * X ^ 2 - 48 * X ^ 3 - 18 * X ^ 4 - 80 * X ^ 5) * L1 + (-3 * X + 2 * X ^ 2 - 6 * X ^ 3 - 2 * X ^ 4 - X ^ 5 - 8 * X ^ 6 + 6 * X ^ 7) * hS1
  have key : (4 * X ^ 6 + 20 * X ^ 8 + 32 * X ^ 9 + 40 * X ^ 10 + 128 * X ^ 11 + 104 * X ^ 12 + 192 * X ^ 13 + 212 * X ^ 14 + 128 * X ^ 15 + 196 * X ^ 16 + 32 * X ^ 17 + 64 * X ^ 18) * (((-6 - 4 * X - 4 * X ^ 2 - 2 * X ^ 3 + 24 * X ^ 5) * (A) + (1 + 6 * X ^ 2 + 10 * X ^ 3 + 5 * X ^ 4 + 22 * X ^ 5) * (X * d⁄dX ℚ A) + (1 + 2 * X ^ 2 + 4 * X ^ 3 + X ^ 4 + 4 * X ^ 5) * (X * d⁄dX ℚ (X * d⁄dX ℚ A))) - (-6 - 2 * X ^ 3)) = 0 := by
    linear_combination (-6 - 4 * X - 22 * X ^ 2 - 62 * X ^ 3 - 62 * X ^ 4 - 122 * X ^ 5 - 194 * X ^ 6 - 114 * X ^ 7 - 36 * X ^ 8 - 58 * X ^ 9 + 304 * X ^ 10 + 376 * X ^ 11 + 192 * X ^ 12 + 384 * X ^ 13) * L0 + (2 * X ^ 3 + 16 * X ^ 5 + 28 * X ^ 6 + 36 * X ^ 7 + 140 * X ^ 8 + 112 * X ^ 9 + 196 * X ^ 10 + 266 * X ^ 11 + 84 * X ^ 12 + 176 * X ^ 13) * L1 + (2 * X ^ 3 + 4 * X ^ 5 + 8 * X ^ 6 + 2 * X ^ 7 + 8 * X ^ 8) * L2
  have hne : (4 * X ^ 6 + 20 * X ^ 8 + 32 * X ^ 9 + 40 * X ^ 10 + 128 * X ^ 11 + 104 * X ^ 12 + 192 * X ^ 13 + 212 * X ^ 14 + 128 * X ^ 15 + 196 * X ^ 16 + 32 * X ^ 17 + 64 * X ^ 18 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 6
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

end Pa157125

theorem OMA.solution : type_of% @OMA.S_oeis_a157125.main := by
  refine ⟨Pa157125.exists_gf, fun S1 S2 A h n hn => ?_⟩
  obtain ⟨T, hT, hL⟩ := Pa157125.facts S1 S2 A h
  have e := congrArg (coeff n) (Pa157125.ode T A hT hL)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega, show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega, show k + 5 - 5 = k by omega]
  simp only [Pa157125.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa157125.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
