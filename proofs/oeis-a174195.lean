import OMAStatements.S_oeis_a174195
import Mathlib

open OMA.S_oeis_a174195
open PowerSeries

namespace Pa174195

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
    (hL : (2 - 16 * X + 32 * X ^ 2) * A = (X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4 + 49 * X ^ 5 - 72 * X ^ 6 + 16 * X ^ 7) + (-X ^ 2 + 5 * X ^ 3 + 6 * X ^ 4 - 45 * X ^ 5 + 24 * X ^ 6) * S) :
    (-461992 - 1306782 * X + 7128882 * X ^ 2) * (A) + (337152 + 911807 * X - 5028946 * X ^ 2) * (X * d⁄dX ℚ A) + (-61130 - 164259 * X + 1127840 * X ^ 2) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) + (4026 + 4026 * X - 80520 * X ^ 2) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) = 166200 * X ^ 4 + 168734 * X ^ 5 + 13998 * X ^ 6 + 57576 * X ^ 7 := by
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
  have dP1 : d⁄dX ℚ (2 - 16 * X + 32 * X ^ 2 : PowerSeries ℚ) = -16 + 64 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4 + 49 * X ^ 5 - 72 * X ^ 6 + 16 * X ^ 7 : PowerSeries ℚ) = 2 * X - 21 * X ^ 2 + 16 * X ^ 3 + 245 * X ^ 4 - 432 * X ^ 5 + 112 * X ^ 6 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (-X ^ 2 + 5 * X ^ 3 + 6 * X ^ 4 - 45 * X ^ 5 + 24 * X ^ 6 : PowerSeries ℚ) = -2 * X + 15 * X ^ 2 + 24 * X ^ 3 - 225 * X ^ 4 + 144 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (2 - 24 * X + 96 * X ^ 2 - 128 * X ^ 3) * (X * d⁄dX ℚ A) = (2 * X ^ 2 - 21 * X ^ 3 + 44 * X ^ 4 + 213 * X ^ 5 - 1020 * X ^ 6 + 1264 * X ^ 7 - 320 * X ^ 8) + (-2 * X ^ 2 + 17 * X ^ 3 - 6 * X ^ 4 - 285 * X ^ 5 + 774 * X ^ 6 - 432 * X ^ 7) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 8 * X ^ 2) * E1 + (16 * X) * L0 + (-X ^ 3 + 5 * X ^ 4 + 6 * X ^ 5 - 45 * X ^ 6 + 24 * X ^ 7) * hS1
  have dP2 : d⁄dX ℚ (2 - 24 * X + 96 * X ^ 2 - 128 * X ^ 3 : PowerSeries ℚ) = -24 + 192 * X - 384 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU2 : d⁄dX ℚ (2 * X ^ 2 - 21 * X ^ 3 + 44 * X ^ 4 + 213 * X ^ 5 - 1020 * X ^ 6 + 1264 * X ^ 7 - 320 * X ^ 8 : PowerSeries ℚ) = 4 * X - 63 * X ^ 2 + 176 * X ^ 3 + 1065 * X ^ 4 - 6120 * X ^ 5 + 8848 * X ^ 6 - 2560 * X ^ 7 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV2 : d⁄dX ℚ (-2 * X ^ 2 + 17 * X ^ 3 - 6 * X ^ 4 - 285 * X ^ 5 + 774 * X ^ 6 - 432 * X ^ 7 : PowerSeries ℚ) = -4 * X + 51 * X ^ 2 - 24 * X ^ 3 - 1425 * X ^ 4 + 4644 * X ^ 5 - 3024 * X ^ 6 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E2 := th_step _ _ _ _ _ L1
  simp only [dP2, dU2, dV2] at E2
  have L2 : (-2 + 32 * X - 192 * X ^ 2 + 512 * X ^ 3 - 512 * X ^ 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = (-4 * X ^ 2 + 55 * X ^ 3 - 176 * X ^ 4 - 889 * X ^ 5 + 7824 * X ^ 6 - 21088 * X ^ 7 + 22784 * X ^ 8 - 6400 * X ^ 9) + (4 * X ^ 2 - 47 * X ^ 3 + 58 * X ^ 4 + 1389 * X ^ 5 - 7494 * X ^ 6 + 13860 * X ^ 7 - 7776 * X ^ 8) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-2 * X + 8 * X ^ 2) * E2 + (-24 * X) * L1 + (2 * X ^ 3 - 17 * X ^ 4 + 6 * X ^ 5 + 285 * X ^ 6 - 774 * X ^ 7 + 432 * X ^ 8) * hS1
  have dP3 : d⁄dX ℚ (-2 + 32 * X - 192 * X ^ 2 + 512 * X ^ 3 - 512 * X ^ 4 : PowerSeries ℚ) = 32 - 384 * X + 1536 * X ^ 2 - 2048 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU3 : d⁄dX ℚ (-4 * X ^ 2 + 55 * X ^ 3 - 176 * X ^ 4 - 889 * X ^ 5 + 7824 * X ^ 6 - 21088 * X ^ 7 + 22784 * X ^ 8 - 6400 * X ^ 9 : PowerSeries ℚ) = -8 * X + 165 * X ^ 2 - 704 * X ^ 3 - 4445 * X ^ 4 + 46944 * X ^ 5 - 147616 * X ^ 6 + 182272 * X ^ 7 - 57600 * X ^ 8 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV3 : d⁄dX ℚ (4 * X ^ 2 - 47 * X ^ 3 + 58 * X ^ 4 + 1389 * X ^ 5 - 7494 * X ^ 6 + 13860 * X ^ 7 - 7776 * X ^ 8 : PowerSeries ℚ) = 8 * X - 141 * X ^ 2 + 232 * X ^ 3 + 6945 * X ^ 4 - 44964 * X ^ 5 + 97020 * X ^ 6 - 62208 * X ^ 7 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E3 := th_step _ _ _ _ _ L2
  simp only [dP3, dU3, dV3] at E3
  have L3 : (2 - 40 * X + 320 * X ^ 2 - 1280 * X ^ 3 + 2560 * X ^ 4 - 2048 * X ^ 5) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) = (8 * X ^ 2 - 133 * X ^ 3 + 484 * X ^ 4 + 4445 * X ^ 5 - 50500 * X ^ 6 + 210208 * X ^ 7 - 435328 * X ^ 8 + 422144 * X ^ 9 - 128000 * X ^ 10) + (-8 * X ^ 2 + 117 * X ^ 3 - 138 * X ^ 4 - 6829 * X ^ 5 + 53298 * X ^ 6 - 171960 * X ^ 7 + 256248 * X ^ 8 - 139968 * X ^ 9) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-2 * X + 8 * X ^ 2) * E3 + (-32 * X) * L2 + (-4 * X ^ 3 + 47 * X ^ 4 - 58 * X ^ 5 - 1389 * X ^ 6 + 7494 * X ^ 7 - 13860 * X ^ 8 + 7776 * X ^ 9) * hS1
  have key : (2 - 40 * X + 320 * X ^ 2 - 1280 * X ^ 3 + 2560 * X ^ 4 - 2048 * X ^ 5) * (((-461992 - 1306782 * X + 7128882 * X ^ 2) * (A) + (337152 + 911807 * X - 5028946 * X ^ 2) * (X * d⁄dX ℚ A) + (-61130 - 164259 * X + 1127840 * X ^ 2) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) + (4026 + 4026 * X - 80520 * X ^ 2) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A)))) - (166200 * X ^ 4 + 168734 * X ^ 5 + 13998 * X ^ 6 + 57576 * X ^ 7)) = 0 := by
    linear_combination (-461992 + 4237122 * X + 634650 * X ^ 2 - 118704632 * X ^ 3 + 425820384 * X ^ 4 - 456248448 * X ^ 5) * L0 + (337152 - 1785409 * X - 6928970 * X ^ 2 + 54820480 * X ^ 3 - 80463136 * X ^ 4) * L1 + (61130 - 80261 * X - 1784876 * X ^ 2 + 4511360 * X ^ 3) * L2 + (4026 + 4026 * X - 80520 * X ^ 2) * L3
  have hne : (2 - 40 * X + 320 * X ^ 2 - 1280 * X ^ 3 + 2560 * X ^ 4 - 2048 * X ^ 5 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 0
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

theorem S_sq : S ^ 2 = 1 - 4 * X := by
  have hB : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = (1 + X : PowerSeries ℚ) := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    norm_num
    simpa using binomialSeries_nat (A := ℚ) (R := ℚ) 1
  have h0 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow h0, hB, ← coe_substAlgHom h0, map_add, map_one,
    coe_substAlgHom, subst_X h0, R]
  ring

theorem gf_eq : (2 - 16 * X + 32 * X ^ 2) * ((X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4 + 49 * X ^ 5 - 72 * X ^ 6 + 16 * X ^ 7 + (-X ^ 2 + 5 * X ^ 3 + 6 * X ^ 4 - 45 * X ^ 5 + 24 * X ^ 6) * S) * (2 - 16 * X + 32 * X ^ 2 : PowerSeries ℚ)⁻¹) = X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4 + 49 * X ^ 5 - 72 * X ^ 6 + 16 * X ^ 7 + (-X ^ 2 + 5 * X ^ 3 + 6 * X ^ 4 - 45 * X ^ 5 + 24 * X ^ 6) * S := by
  have hd : constantCoeff (2 - 16 * X + 32 * X ^ 2 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (2 - 16 * X + 32 * X ^ 2 : PowerSeries ℚ) hd
  linear_combination (X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4 + 49 * X ^ 5 - 72 * X ^ 6 + 16 * X ^ 7 + (-X ^ 2 + 5 * X ^ 3 + 6 * X ^ 4 - 45 * X ^ 5 + 24 * X ^ 6) * S) * hinv

end Pa174195

theorem OMA.solution : type_of% @OMA.S_oeis_a174195.main := by
  intro n hn
  have hL := Pa174195.gf_eq
  have ha : ∀ m, a m = coeff (m + 4) ((X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4 + 49 * X ^ 5 - 72 * X ^ 6 + 16 * X ^ 7 + (-X ^ 2 + 5 * X ^ 3 + 6 * X ^ 4 - 45 * X ^ 5 + 24 * X ^ 6) * S) * (2 - 16 * X + 32 * X ^ 2 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4 + 49 * X ^ 5 - 72 * X ^ 6 + 16 * X ^ 7 + (-X ^ 2 + 5 * X ^ 3 + 6 * X ^ 4 - 45 * X ^ 5 + 24 * X ^ 6) * S) * (2 - 16 * X + 32 * X ^ 2 : PowerSeries ℚ)⁻¹) = A at hL ha
  have hL' : (2 - 16 * X + 32 * X ^ 2) * A = (X ^ 2 - 7 * X ^ 3 + 4 * X ^ 4 + 49 * X ^ 5 - 72 * X ^ 6 + 16 * X ^ 7) + (-X ^ 2 + 5 * X ^ 3 + 6 * X ^ 4 - 45 * X ^ 5 + 24 * X ^ 6) * S := by
    linear_combination hL
  have e := congrArg (coeff (n + 4)) (Pa174195.ode S A Pa174195.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [Pa174195.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa174195.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
