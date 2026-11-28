import OMAStatements.S_oeis_a118974
import Mathlib

open OMA.S_oeis_a118974
open PowerSeries

namespace Pa118974

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
    (hL : (8 - 6 * X ^ 2 - 2 * X ^ 3) * A = (2 * X - 3 * X ^ 2 - 4 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5) + (-2 * X - X ^ 2 - 2 * X ^ 3 - X ^ 4) * S) :
    (-516 + 1680 * X - 180 * X ^ 2 + 12 * X ^ 3) * (A) + (782 - 2442 * X + 363 * X ^ 2 - 26 * X ^ 3) * (X * d⁄dX ℚ A) + (-300 + 1095 * X - 246 * X ^ 2 - 90 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) + (34 - 153 * X + 51 * X ^ 2 + 68 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) = -24 * X ^ 4 - 144 * X ^ 5 := by
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
  have dP1 : d⁄dX ℚ (8 - 6 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ) = -12 * X - 6 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (2 * X - 3 * X ^ 2 - 4 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5 : PowerSeries ℚ) = 2 - 6 * X - 12 * X ^ 2 + 12 * X ^ 3 + 10 * X ^ 4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (-2 * X - X ^ 2 - 2 * X ^ 3 - X ^ 4 : PowerSeries ℚ) = -2 - 2 * X - 6 * X ^ 2 - 4 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (8 - 40 * X + 26 * X ^ 2 + 28 * X ^ 3 - 14 * X ^ 4 - 8 * X ^ 5) * (X * d⁄dX ℚ A) = (2 * X - 16 * X ^ 2 + 29 * X ^ 3 + 30 * X ^ 4 - 77 * X ^ 5 + 16 * X ^ 6 + 16 * X ^ 7) + (-2 * X + 12 * X ^ 2 - 9 * X ^ 3 + 32 * X ^ 4 - 9 * X ^ 5 - 6 * X ^ 6) * S := by
    have hg : (4 + 2 * X : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (4 * X - 18 * X ^ 2 + 6 * X ^ 3 + 8 * X ^ 4) * E1 + (6 * X ^ 2 - 24 * X ^ 3) * L0 + (-4 * X ^ 2 - X ^ 4 + X ^ 5 + 3 * X ^ 6 + X ^ 7) * hS1
  have dP2 : d⁄dX ℚ (8 - 40 * X + 26 * X ^ 2 + 28 * X ^ 3 - 14 * X ^ 4 - 8 * X ^ 5 : PowerSeries ℚ) = -40 + 52 * X + 84 * X ^ 2 - 56 * X ^ 3 - 40 * X ^ 4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU2 : d⁄dX ℚ (2 * X - 16 * X ^ 2 + 29 * X ^ 3 + 30 * X ^ 4 - 77 * X ^ 5 + 16 * X ^ 6 + 16 * X ^ 7 : PowerSeries ℚ) = 2 - 32 * X + 87 * X ^ 2 + 120 * X ^ 3 - 385 * X ^ 4 + 96 * X ^ 5 + 112 * X ^ 6 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV2 : d⁄dX ℚ (-2 * X + 12 * X ^ 2 - 9 * X ^ 3 + 32 * X ^ 4 - 9 * X ^ 5 - 6 * X ^ 6 : PowerSeries ℚ) = -2 + 24 * X - 27 * X ^ 2 + 128 * X ^ 3 - 45 * X ^ 4 - 36 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E2 := th_step _ _ _ _ _ L1
  simp only [dP2, dU2, dV2] at E2
  have L2 : (16 - 152 * X + 436 * X ^ 2 - 266 * X ^ 3 - 362 * X ^ 4 + 298 * X ^ 5 + 142 * X ^ 6 - 80 * X ^ 7 - 32 * X ^ 8) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = (4 * X - 62 * X ^ 2 + 292 * X ^ 3 - 253 * X ^ 4 - 1329 * X ^ 5 + 2775 * X ^ 6 - 1139 * X ^ 7 - 688 * X ^ 8 + 272 * X ^ 9 + 128 * X ^ 10) + (-4 * X + 54 * X ^ 2 - 192 * X ^ 3 + 473 * X ^ 4 - 1197 * X ^ 5 + 525 * X ^ 6 + 143 * X ^ 7 - 90 * X ^ 8 - 36 * X ^ 9) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (4 * X - 18 * X ^ 2 + 6 * X ^ 3 + 8 * X ^ 4) * E2 + (20 * X - 16 * X ^ 2 - 40 * X ^ 3) * L1 + (-4 * X ^ 2 + 26 * X ^ 3 - 28 * X ^ 4 + 61 * X ^ 5 - 41 * X ^ 6 - 35 * X ^ 7 + 15 * X ^ 8 + 6 * X ^ 9) * hS1
  have dP3 : d⁄dX ℚ (16 - 152 * X + 436 * X ^ 2 - 266 * X ^ 3 - 362 * X ^ 4 + 298 * X ^ 5 + 142 * X ^ 6 - 80 * X ^ 7 - 32 * X ^ 8 : PowerSeries ℚ) = -152 + 872 * X - 798 * X ^ 2 - 1448 * X ^ 3 + 1490 * X ^ 4 + 852 * X ^ 5 - 560 * X ^ 6 - 256 * X ^ 7 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU3 : d⁄dX ℚ (4 * X - 62 * X ^ 2 + 292 * X ^ 3 - 253 * X ^ 4 - 1329 * X ^ 5 + 2775 * X ^ 6 - 1139 * X ^ 7 - 688 * X ^ 8 + 272 * X ^ 9 + 128 * X ^ 10 : PowerSeries ℚ) = 4 - 124 * X + 876 * X ^ 2 - 1012 * X ^ 3 - 6645 * X ^ 4 + 16650 * X ^ 5 - 7973 * X ^ 6 - 5504 * X ^ 7 + 2448 * X ^ 8 + 1280 * X ^ 9 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV3 : d⁄dX ℚ (-4 * X + 54 * X ^ 2 - 192 * X ^ 3 + 473 * X ^ 4 - 1197 * X ^ 5 + 525 * X ^ 6 + 143 * X ^ 7 - 90 * X ^ 8 - 36 * X ^ 9 : PowerSeries ℚ) = -4 + 108 * X - 576 * X ^ 2 + 1892 * X ^ 3 - 5985 * X ^ 4 + 3150 * X ^ 5 + 1001 * X ^ 6 - 720 * X ^ 7 - 324 * X ^ 8 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E3 := th_step _ _ _ _ _ L2
  simp only [dP3, dU3, dV3] at E3
  have L3 : (32 - 448 * X + 2288 * X ^ 2 - 4848 * X ^ 3 + 2370 * X ^ 4 + 4800 * X ^ 5 - 4548 * X ^ 6 - 1992 * X ^ 7 + 2274 * X ^ 8 + 616 * X ^ 9 - 416 * X ^ 10 - 128 * X ^ 11) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) = (8 * X - 208 * X ^ 2 + 1646 * X ^ 3 - 3976 * X ^ 4 - 8961 * X ^ 5 + 62520 * X ^ 6 - 110352 * X ^ 7 + 66156 * X ^ 8 + 11187 * X ^ 9 - 16628 * X ^ 10 - 5552 * X ^ 11 + 3136 * X ^ 12 + 1024 * X ^ 13) + (-8 * X + 192 * X ^ 2 - 1278 * X ^ 3 + 5868 * X ^ 4 - 22515 * X ^ 5 + 45666 * X ^ 6 - 28686 * X ^ 7 + 6816 * X ^ 8 + 2619 * X ^ 9 + 1010 * X ^ 10 - 720 * X ^ 11 - 216 * X ^ 12) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (4 * X - 18 * X ^ 2 + 6 * X ^ 3 + 8 * X ^ 4) * E3 + (38 * X - 28 * X ^ 2 - 64 * X ^ 3) * L2 + (-8 * X ^ 2 + 112 * X ^ 3 - 434 * X ^ 4 + 1084 * X ^ 5 - 2675 * X ^ 6 + 1774 * X ^ 7 + 958 * X ^ 8 - 848 * X ^ 9 - 125 * X ^ 10 + 126 * X ^ 11 + 36 * X ^ 12) * hS1
  have key : (-32 + 448 * X - 2288 * X ^ 2 + 4848 * X ^ 3 - 2370 * X ^ 4 - 4800 * X ^ 5 + 4548 * X ^ 6 + 1992 * X ^ 7 - 2274 * X ^ 8 - 616 * X ^ 9 + 416 * X ^ 10 + 128 * X ^ 11) * (((-516 + 1680 * X - 180 * X ^ 2 + 12 * X ^ 3) * (A) + (782 - 2442 * X + 363 * X ^ 2 - 26 * X ^ 3) * (X * d⁄dX ℚ A) + (-300 + 1095 * X - 246 * X ^ 2 - 90 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) + (34 - 153 * X + 51 * X ^ 2 + 68 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A)))) - (-24 * X ^ 4 - 144 * X ^ 5)) = 0 := by
    linear_combination (2064 - 35616 * X + 243924 * X ^ 2 - 829500 * X ^ 3 + 1397136 * X ^ 4 - 861756 * X ^ 5 - 400272 * X ^ 6 + 634008 * X ^ 7 - 60180 * X ^ 8 - 100368 * X ^ 9 + 11328 * X ^ 10 - 768 * X ^ 11) * L0 + (-3128 + 37920 * X - 162090 * X ^ 2 + 269994 * X ^ 3 - 78225 * X ^ 4 - 156402 * X ^ 5 + 67977 * X ^ 6 + 28722 * X ^ 7 - 5184 * X ^ 8 + 416 * X ^ 9) * L1 + (600 - 4890 * X + 11247 * X ^ 2 - 4119 * X ^ 3 - 4452 * X ^ 4 + 1254 * X ^ 5 + 360 * X ^ 6) * L2 + (-34 + 153 * X - 51 * X ^ 2 - 68 * X ^ 3) * L3
  have hne : (-32 + 448 * X - 2288 * X ^ 2 + 4848 * X ^ 3 - 2370 * X ^ 4 - 4800 * X ^ 5 + 4548 * X ^ 6 + 1992 * X ^ 7 - 2274 * X ^ 8 - 616 * X ^ 9 + 416 * X ^ 10 + 128 * X ^ 11 : PowerSeries ℚ) ≠ 0 := by
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

theorem gf_eq : (8 - 6 * X ^ 2 - 2 * X ^ 3) * ((2 * X - 3 * X ^ 2 - 4 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5 + (-2 * X - X ^ 2 - 2 * X ^ 3 - X ^ 4) * S) * (8 - 6 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ)⁻¹) = 2 * X - 3 * X ^ 2 - 4 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5 + (-2 * X - X ^ 2 - 2 * X ^ 3 - X ^ 4) * S := by
  have hd : constantCoeff (8 - 6 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (8 - 6 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ) hd
  linear_combination (2 * X - 3 * X ^ 2 - 4 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5 + (-2 * X - X ^ 2 - 2 * X ^ 3 - X ^ 4) * S) * hinv

end Pa118974

theorem OMA.solution : type_of% @OMA.S_oeis_a118974.main := by
  intro n hn
  have hL := Pa118974.gf_eq
  have ha : ∀ m, a m = coeff ((m + 2)) ((2 * X - 3 * X ^ 2 - 4 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5 + (-2 * X - X ^ 2 - 2 * X ^ 3 - X ^ 4) * S) * (8 - 6 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((2 * X - 3 * X ^ 2 - 4 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5 + (-2 * X - X ^ 2 - 2 * X ^ 3 - X ^ 4) * S) * (8 - 6 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ)⁻¹) = A at hL ha
  have hL' : (8 - 6 * X ^ 2 - 2 * X ^ 3) * A = (2 * X - 3 * X ^ 2 - 4 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5) + (-2 * X - X ^ 2 - 2 * X ^ 3 - X ^ 4) * S := by
    linear_combination hL
  have e := congrArg (coeff ((n + 2))) (Pa118974.ode S A Pa118974.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [Pa118974.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa118974.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
