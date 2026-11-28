import OMAStatements.S_oeis_a161006
import Mathlib

open OMA.S_oeis_a161006
open PowerSeries

namespace Pa161006

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

theorem th_step2 (P B U V1 V2 V3 S1 S2 : PowerSeries ℚ)
    (h : P * B = U + V1 * S1 + V2 * S2 + V3 * (S1 * S2)) :
    d⁄dX ℚ P * B + P * d⁄dX ℚ B = d⁄dX ℚ U + d⁄dX ℚ V1 * S1 + V1 * d⁄dX ℚ S1 + d⁄dX ℚ V2 * S2 +
      V2 * d⁄dX ℚ S2 + d⁄dX ℚ V3 * (S1 * S2) + V3 * (d⁄dX ℚ S1 * S2 + S1 * d⁄dX ℚ S2) := by
  have h1 := congrArg (d⁄dX ℚ) h
  simp only [Derivation.leibniz, map_add, smul_eq_mul] at h1
  linear_combination h1

theorem cat_eq : c ^ 2 * X + 1 = c := by
  have := congrArg (map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
  simpa [c] using this

theorem catalan_subst (u : PowerSeries ℚ) (hu : constantCoeff u = 0) :
    c.subst u ^ 2 * u + 1 = c.subst u := by
  have ha := HasSubst.of_constantCoeff_zero' hu
  have hc := congrArg (substAlgHom ha) cat_eq
  rw [map_add, map_mul, map_pow, map_one, substAlgHom_X, coe_substAlgHom] at hc
  exact hc

theorem facts : ∃ S1 S2 : PowerSeries ℚ, S1 ^ 2 = 1 - 4 * X ∧ S2 ^ 2 = 1 - 4 * X ^ 2 ∧
    (4 * X ^ 3) * A = (1) + (-1) * S1 + (-1) * S2 +
      (1) * (S1 * S2) := by
  set C2 : PowerSeries ℚ := c.subst (X ^ 2) with hC2def
  have hC2 : C2 ^ 2 * X ^ 2 + 1 = C2 := catalan_subst _ (by simp)
  have hc := cat_eq
  have hA : A = c * C2 := rfl
  refine ⟨1 - 2 * X * c, 1 - 2 * X ^ 2 * C2, by linear_combination 4 * X * hc,
    by linear_combination 4 * X ^ 2 * hC2, ?_⟩
  rw [hA]; ring

set_option maxHeartbeats 4000000 in
theorem ode2 (S1 S2 A : PowerSeries ℚ) (h1 : S1 ^ 2 = 1 - 4 * X) (h2 : S2 ^ 2 = 1 - 4 * X ^ 2)
    (hL : (4 * X ^ 3) * A = (1) + (-1) * S1 + (-1) * S2 + (1) * (S1 * S2)) :
    (252 - 1524 * X + 10680 * X ^ 2 - 66840 * X ^ 3 + 146160 * X ^ 4 + 235104 * X ^ 5 - 1304448 * X ^ 6 + 1424640 * X ^ 7) * (A) + (180 - 1066 * X + 18200 * X ^ 2 - 147200 * X ^ 3 + 364352 * X ^ 4 + 236992 * X ^ 5 - 2252608 * X ^ 6 + 2546816 * X ^ 7) * (X * d⁄dX ℚ A) + (-265 + 3156 * X - 976 * X ^ 2 - 95144 * X ^ 3 + 327728 * X ^ 4 - 20768 * X ^ 5 - 1386432 * X ^ 6 + 1633024 * X ^ 7) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) + (-240 + 2734 * X - 7016 * X ^ 2 - 22960 * X ^ 3 + 121696 * X ^ 4 - 62368 * X ^ 5 - 359168 * X ^ 6 + 441856 * X ^ 7) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) + (-47 + 540 * X - 1688 * X ^ 2 - 1696 * X ^ 3 + 15760 * X ^ 4 - 12352 * X ^ 5 - 33024 * X ^ 6 + 41984 * X ^ 7) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A)))) = 252 - 1644 * X + 5160 * X ^ 2 - 480 * X ^ 3 - 12000 * X ^ 4 := by
  have hd1 : d⁄dX ℚ (1 - 4 * X : PowerSeries ℚ) = -4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have hd2 : d⁄dX ℚ (1 - 4 * X ^ 2 : PowerSeries ℚ) = -8 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have hS1 := sq_step S1 _ h1
  rw [hd1] at hS1
  have hS2 := sq_step S2 _ h2
  rw [hd2] at hS2
  have L0 := hL
  have dP1 : d⁄dX ℚ (4 * X ^ 3 : PowerSeries ℚ) = 12 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dW1_0 : d⁄dX ℚ (1 : PowerSeries ℚ) = 0 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dW1_1 : d⁄dX ℚ (-1 : PowerSeries ℚ) = 0 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dW1_2 : d⁄dX ℚ (-1 : PowerSeries ℚ) = 0 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dW1_3 : d⁄dX ℚ (1 : PowerSeries ℚ) = 0 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step2 _ _ _ _ _ _ _ _ L0
  simp only [dP1, dW1_0, dW1_1, dW1_2, dW1_3] at E1
  have L1 : (4 * X ^ 3 - 16 * X ^ 4 - 16 * X ^ 5 + 64 * X ^ 6) * (X * d⁄dX ℚ A) = (-3 + 12 * X + 12 * X ^ 2 - 48 * X ^ 3) + (3 - 10 * X - 12 * X ^ 2 + 40 * X ^ 3) * S1 + (3 - 12 * X - 8 * X ^ 2 + 32 * X ^ 3) * S2 + (-3 + 10 * X + 8 * X ^ 2 - 24 * X ^ 3) * (S1 * S2) := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 8 * X ^ 2 - 8 * X ^ 3 + 32 * X ^ 4) * E1 + (-6 + 24 * X + 24 * X ^ 2 - 96 * X ^ 3) * L0 +
      ((-X + 4 * X ^ 3) + (X - 4 * X ^ 3) * S2) * hS1 + ((-X + 4 * X ^ 2) + (X - 4 * X ^ 2) * S1) * hS2
  have dP2 : d⁄dX ℚ (4 * X ^ 3 - 16 * X ^ 4 - 16 * X ^ 5 + 64 * X ^ 6 : PowerSeries ℚ) = 12 * X ^ 2 - 64 * X ^ 3 - 80 * X ^ 4 + 384 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dW2_0 : d⁄dX ℚ (-3 + 12 * X + 12 * X ^ 2 - 48 * X ^ 3 : PowerSeries ℚ) = 12 + 24 * X - 144 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dW2_1 : d⁄dX ℚ (3 - 10 * X - 12 * X ^ 2 + 40 * X ^ 3 : PowerSeries ℚ) = -10 - 24 * X + 120 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dW2_2 : d⁄dX ℚ (3 - 12 * X - 8 * X ^ 2 + 32 * X ^ 3 : PowerSeries ℚ) = -12 - 16 * X + 96 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dW2_3 : d⁄dX ℚ (-3 + 10 * X + 8 * X ^ 2 - 24 * X ^ 3 : PowerSeries ℚ) = 10 + 16 * X - 72 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E2 := th_step2 _ _ _ _ _ _ _ _ L1
  simp only [dP2, dW2_0, dW2_1, dW2_2, dW2_3] at E2
  have L2 : (4 * X ^ 3 - 32 * X ^ 4 + 32 * X ^ 5 + 256 * X ^ 6 - 448 * X ^ 7 - 512 * X ^ 8 + 1024 * X ^ 9) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = (9 - 72 * X + 72 * X ^ 2 + 576 * X ^ 3 - 1008 * X ^ 4 - 1152 * X ^ 5 + 2304 * X ^ 6) + (-9 + 62 * X - 28 * X ^ 2 - 496 * X ^ 3 + 656 * X ^ 4 + 992 * X ^ 5 - 1600 * X ^ 6) * S1 + (-9 + 72 * X - 88 * X ^ 2 - 448 * X ^ 3 + 832 * X ^ 4 + 512 * X ^ 5 - 1024 * X ^ 6) * S2 + (9 - 62 * X + 44 * X ^ 2 + 384 * X ^ 3 - 544 * X ^ 4 - 416 * X ^ 5 + 576 * X ^ 6) * (S1 * S2) := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 8 * X ^ 2 - 8 * X ^ 3 + 32 * X ^ 4) * E2 + (-6 + 32 * X + 40 * X ^ 2 - 192 * X ^ 3) * L1 +
      ((3 * X - 10 * X ^ 2 - 24 * X ^ 3 + 80 * X ^ 4 + 48 * X ^ 5 - 160 * X ^ 6) + (-3 * X + 10 * X ^ 2 + 20 * X ^ 3 - 64 * X ^ 4 - 32 * X ^ 5 + 96 * X ^ 6) * S2) * hS1 + ((3 * X - 24 * X ^ 2 + 40 * X ^ 3 + 64 * X ^ 4 - 128 * X ^ 5) + (-3 * X + 22 * X ^ 2 - 32 * X ^ 3 - 56 * X ^ 4 + 96 * X ^ 5) * S1) * hS2
  have dP3 : d⁄dX ℚ (4 * X ^ 3 - 32 * X ^ 4 + 32 * X ^ 5 + 256 * X ^ 6 - 448 * X ^ 7 - 512 * X ^ 8 + 1024 * X ^ 9 : PowerSeries ℚ) = 12 * X ^ 2 - 128 * X ^ 3 + 160 * X ^ 4 + 1536 * X ^ 5 - 3136 * X ^ 6 - 4096 * X ^ 7 + 9216 * X ^ 8 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dW3_0 : d⁄dX ℚ (9 - 72 * X + 72 * X ^ 2 + 576 * X ^ 3 - 1008 * X ^ 4 - 1152 * X ^ 5 + 2304 * X ^ 6 : PowerSeries ℚ) = -72 + 144 * X + 1728 * X ^ 2 - 4032 * X ^ 3 - 5760 * X ^ 4 + 13824 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dW3_1 : d⁄dX ℚ (-9 + 62 * X - 28 * X ^ 2 - 496 * X ^ 3 + 656 * X ^ 4 + 992 * X ^ 5 - 1600 * X ^ 6 : PowerSeries ℚ) = 62 - 56 * X - 1488 * X ^ 2 + 2624 * X ^ 3 + 4960 * X ^ 4 - 9600 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dW3_2 : d⁄dX ℚ (-9 + 72 * X - 88 * X ^ 2 - 448 * X ^ 3 + 832 * X ^ 4 + 512 * X ^ 5 - 1024 * X ^ 6 : PowerSeries ℚ) = 72 - 176 * X - 1344 * X ^ 2 + 3328 * X ^ 3 + 2560 * X ^ 4 - 6144 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dW3_3 : d⁄dX ℚ (9 - 62 * X + 44 * X ^ 2 + 384 * X ^ 3 - 544 * X ^ 4 - 416 * X ^ 5 + 576 * X ^ 6 : PowerSeries ℚ) = -62 + 88 * X + 1152 * X ^ 2 - 2176 * X ^ 3 - 2080 * X ^ 4 + 3456 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E3 := th_step2 _ _ _ _ _ _ _ _ L2
  simp only [dP3, dW3_0, dW3_1, dW3_2, dW3_3] at E3
  have L3 : (4 * X ^ 3 - 48 * X ^ 4 + 144 * X ^ 5 + 320 * X ^ 6 - 2112 * X ^ 7 + 768 * X ^ 8 + 8960 * X ^ 9 - 9216 * X ^ 10 - 12288 * X ^ 11 + 16384 * X ^ 12) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) = (-27 + 324 * X - 972 * X ^ 2 - 2160 * X ^ 3 + 14256 * X ^ 4 - 5184 * X ^ 5 - 60480 * X ^ 6 + 62208 * X ^ 7 + 82944 * X ^ 8 - 110592 * X ^ 9) + (27 - 286 * X + 644 * X ^ 2 + 2432 * X ^ 3 - 10320 * X ^ 4 - 1728 * X ^ 5 + 44736 * X ^ 6 - 29696 * X ^ 7 - 61952 * X ^ 8 + 64000 * X ^ 9) * S1 + (27 - 324 * X + 1024 * X ^ 2 + 1536 * X ^ 3 - 12224 * X ^ 4 + 7424 * X ^ 5 + 39424 * X ^ 6 - 47104 * X ^ 7 - 24576 * X ^ 8 + 32768 * X ^ 9) * S2 + (-27 + 286 * X - 696 * X ^ 2 - 1880 * X ^ 3 + 8912 * X ^ 4 - 1184 * X ^ 5 - 29440 * X ^ 6 + 25344 * X ^ 7 + 16640 * X ^ 8 - 13824 * X ^ 9) * (S1 * S2) := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 8 * X ^ 2 - 8 * X ^ 3 + 32 * X ^ 4) * E3 + (-6 + 40 * X + 56 * X ^ 2 - 288 * X ^ 3) * L2 +
      ((-9 * X + 62 * X ^ 2 + 8 * X ^ 3 - 744 * X ^ 4 + 768 * X ^ 5 + 2976 * X ^ 6 - 4224 * X ^ 7 - 3968 * X ^ 8 + 6400 * X ^ 9) + (9 * X - 62 * X ^ 2 + 8 * X ^ 3 + 632 * X ^ 4 - 720 * X ^ 5 - 1952 * X ^ 6 + 2752 * X ^ 7 + 1664 * X ^ 8 - 2304 * X ^ 9) * S2) * hS1 + ((-9 * X + 108 * X ^ 2 - 376 * X ^ 3 - 96 * X ^ 4 + 2624 * X ^ 5 - 2816 * X ^ 6 - 3072 * X ^ 7 + 4096 * X ^ 8) + (9 * X - 98 * X ^ 2 + 292 * X ^ 3 + 208 * X ^ 4 - 2080 * X ^ 5 + 1760 * X ^ 6 + 2240 * X ^ 7 - 2304 * X ^ 8) * S1) * hS2
  have dP4 : d⁄dX ℚ (4 * X ^ 3 - 48 * X ^ 4 + 144 * X ^ 5 + 320 * X ^ 6 - 2112 * X ^ 7 + 768 * X ^ 8 + 8960 * X ^ 9 - 9216 * X ^ 10 - 12288 * X ^ 11 + 16384 * X ^ 12 : PowerSeries ℚ) = 12 * X ^ 2 - 192 * X ^ 3 + 720 * X ^ 4 + 1920 * X ^ 5 - 14784 * X ^ 6 + 6144 * X ^ 7 + 80640 * X ^ 8 - 92160 * X ^ 9 - 135168 * X ^ 10 + 196608 * X ^ 11 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dW4_0 : d⁄dX ℚ (-27 + 324 * X - 972 * X ^ 2 - 2160 * X ^ 3 + 14256 * X ^ 4 - 5184 * X ^ 5 - 60480 * X ^ 6 + 62208 * X ^ 7 + 82944 * X ^ 8 - 110592 * X ^ 9 : PowerSeries ℚ) = 324 - 1944 * X - 6480 * X ^ 2 + 57024 * X ^ 3 - 25920 * X ^ 4 - 362880 * X ^ 5 + 435456 * X ^ 6 + 663552 * X ^ 7 - 995328 * X ^ 8 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dW4_1 : d⁄dX ℚ (27 - 286 * X + 644 * X ^ 2 + 2432 * X ^ 3 - 10320 * X ^ 4 - 1728 * X ^ 5 + 44736 * X ^ 6 - 29696 * X ^ 7 - 61952 * X ^ 8 + 64000 * X ^ 9 : PowerSeries ℚ) = -286 + 1288 * X + 7296 * X ^ 2 - 41280 * X ^ 3 - 8640 * X ^ 4 + 268416 * X ^ 5 - 207872 * X ^ 6 - 495616 * X ^ 7 + 576000 * X ^ 8 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dW4_2 : d⁄dX ℚ (27 - 324 * X + 1024 * X ^ 2 + 1536 * X ^ 3 - 12224 * X ^ 4 + 7424 * X ^ 5 + 39424 * X ^ 6 - 47104 * X ^ 7 - 24576 * X ^ 8 + 32768 * X ^ 9 : PowerSeries ℚ) = -324 + 2048 * X + 4608 * X ^ 2 - 48896 * X ^ 3 + 37120 * X ^ 4 + 236544 * X ^ 5 - 329728 * X ^ 6 - 196608 * X ^ 7 + 294912 * X ^ 8 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dW4_3 : d⁄dX ℚ (-27 + 286 * X - 696 * X ^ 2 - 1880 * X ^ 3 + 8912 * X ^ 4 - 1184 * X ^ 5 - 29440 * X ^ 6 + 25344 * X ^ 7 + 16640 * X ^ 8 - 13824 * X ^ 9 : PowerSeries ℚ) = 286 - 1392 * X - 5640 * X ^ 2 + 35648 * X ^ 3 - 5920 * X ^ 4 - 176640 * X ^ 5 + 177408 * X ^ 6 + 133120 * X ^ 7 - 124416 * X ^ 8 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E4 := th_step2 _ _ _ _ _ _ _ _ L3
  simp only [dP4, dW4_0, dW4_1, dW4_2, dW4_3] at E4
  have L4 : (4 * X ^ 3 - 64 * X ^ 4 + 320 * X ^ 5 - 4736 * X ^ 7 + 10240 * X ^ 8 + 19456 * X ^ 9 - 81920 * X ^ 10 + 1024 * X ^ 11 + 245760 * X ^ 12 - 163840 * X ^ 13 - 262144 * X ^ 14 + 262144 * X ^ 15) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A)))) = (81 - 1296 * X + 6480 * X ^ 2 - 95904 * X ^ 4 + 207360 * X ^ 5 + 393984 * X ^ 6 - 1658880 * X ^ 7 + 20736 * X ^ 8 + 4976640 * X ^ 9 - 3317760 * X ^ 10 - 5308416 * X ^ 11 + 5308416 * X ^ 12) + (-81 + 1166 * X - 4820 * X ^ 2 - 5104 * X ^ 3 + 80080 * X ^ 4 - 104896 * X ^ 5 - 406400 * X ^ 6 + 1002496 * X ^ 7 + 584960 * X ^ 8 - 3170816 * X ^ 9 + 994304 * X ^ 10 + 3469312 * X ^ 11 - 2560000 * X ^ 12) * S1 + (-81 + 1296 * X - 6640 * X ^ 2 + 2560 * X ^ 3 + 82624 * X ^ 4 - 199680 * X ^ 5 - 244224 * X ^ 6 + 1269760 * X ^ 7 - 331776 * X ^ 8 - 2949120 * X ^ 9 + 2621440 * X ^ 10 + 1048576 * X ^ 11 - 1048576 * X ^ 12) * S2 + (81 - 1166 * X + 4980 * X ^ 2 + 2800 * X ^ 3 - 70064 * X ^ 4 + 108160 * X ^ 5 + 277504 * X ^ 6 - 780800 * X ^ 7 - 200192 * X ^ 8 + 1971712 * X ^ 9 - 1225728 * X ^ 10 - 610304 * X ^ 11 + 331776 * X ^ 12) * (S1 * S2) := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (2 * X - 8 * X ^ 2 - 8 * X ^ 3 + 32 * X ^ 4) * E4 + (-6 + 48 * X + 72 * X ^ 2 - 384 * X ^ 3) * L3 +
      ((27 * X - 286 * X ^ 2 + 536 * X ^ 3 + 3576 * X ^ 4 - 12896 * X ^ 5 - 11456 * X ^ 6 + 86016 * X ^ 7 - 22784 * X ^ 8 - 240896 * X ^ 9 + 182784 * X ^ 10 + 247808 * X ^ 11 - 256000 * X ^ 12) + (-27 * X + 286 * X ^ 2 - 588 * X ^ 3 - 3024 * X ^ 4 + 11696 * X ^ 5 + 6336 * X ^ 6 - 65088 * X ^ 7 + 30080 * X ^ 8 + 134400 * X ^ 9 - 115200 * X ^ 10 - 66560 * X ^ 11 + 55296 * X ^ 12) * S2) * hS1 + ((27 * X - 432 * X ^ 2 + 2320 * X ^ 3 - 2560 * X ^ 4 - 18368 * X ^ 5 + 56320 * X ^ 6 + 9728 * X ^ 7 - 204800 * X ^ 8 + 163840 * X ^ 9 + 131072 * X ^ 10 - 131072 * X ^ 11) + (-27 * X + 394 * X ^ 2 - 1840 * X ^ 3 + 904 * X ^ 4 + 16432 * X ^ 5 - 36832 * X ^ 6 - 24704 * X ^ 7 + 143104 * X ^ 8 - 84736 * X ^ 9 - 80384 * X ^ 10 + 55296 * X ^ 11) * S1) * hS2
  have key : (4 * X ^ 3 - 64 * X ^ 4 + 320 * X ^ 5 - 4736 * X ^ 7 + 10240 * X ^ 8 + 19456 * X ^ 9 - 81920 * X ^ 10 + 1024 * X ^ 11 + 245760 * X ^ 12 - 163840 * X ^ 13 - 262144 * X ^ 14 + 262144 * X ^ 15) * (((252 - 1524 * X + 10680 * X ^ 2 - 66840 * X ^ 3 + 146160 * X ^ 4 + 235104 * X ^ 5 - 1304448 * X ^ 6 + 1424640 * X ^ 7) * (A) + (180 - 1066 * X + 18200 * X ^ 2 - 147200 * X ^ 3 + 364352 * X ^ 4 + 236992 * X ^ 5 - 2252608 * X ^ 6 + 2546816 * X ^ 7) * (X * d⁄dX ℚ A) + (-265 + 3156 * X - 976 * X ^ 2 - 95144 * X ^ 3 + 327728 * X ^ 4 - 20768 * X ^ 5 - 1386432 * X ^ 6 + 1633024 * X ^ 7) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) + (-240 + 2734 * X - 7016 * X ^ 2 - 22960 * X ^ 3 + 121696 * X ^ 4 - 62368 * X ^ 5 - 359168 * X ^ 6 + 441856 * X ^ 7) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) + (-47 + 540 * X - 1688 * X ^ 2 - 1696 * X ^ 3 + 15760 * X ^ 4 - 12352 * X ^ 5 - 33024 * X ^ 6 + 41984 * X ^ 7) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))))) - (252 - 1644 * X + 5160 * X ^ 2 - 480 * X ^ 3 - 12000 * X ^ 4)) = 0 := by
    linear_combination (252 - 5556 * X + 55224 * X ^ 2 - 359640 * X ^ 3 + 1771632 * X ^ 4 - 5001120 * X ^ 5 - 8694144 * X ^ 6 + 135009792 * X ^ 7 - 388090368 * X ^ 8 - 318965760 * X ^ 9 + 4124915712 * X ^ 10 - 6190995456 * X ^ 11 - 11902980096 * X ^ 12 + 44622766080 * X ^ 13 - 15972139008 * X ^ 14 - 103369605120 * X ^ 15 + 135131037696 * X ^ 16 + 42542825472 * X ^ 17 - 178853511168 * X ^ 18 + 93365207040 * X ^ 19) * L0 + (180 - 3226 * X + 37472 * X ^ 2 - 389576 * X ^ 3 + 2605632 * X ^ 4 - 7381024 * X ^ 5 - 13166912 * X ^ 6 + 145671424 * X ^ 7 - 270665472 * X ^ 8 - 511348224 * X ^ 9 + 2533645312 * X ^ 10 - 1559078912 * X ^ 11 - 6825103360 * X ^ 12 + 11659223040 * X ^ 13 + 2022866944 * X ^ 14 - 17050501120 * X ^ 15 + 10431758336 * X ^ 16) * L1 + (-265 + 5276 * X - 28344 * X ^ 2 - 79048 * X ^ 3 + 1312736 * X ^ 4 - 3785760 * X ^ 5 - 5050176 * X ^ 6 + 45121920 * X ^ 7 - 50261760 * X ^ 8 - 139647488 * X ^ 9 + 346350592 * X ^ 10 - 10752000 * X ^ 11 - 563953664 * X ^ 12 + 418054144 * X ^ 13) * L2 + (-240 + 3694 * X - 16992 * X ^ 2 - 9672 * X ^ 3 + 285344 * X ^ 4 - 569568 * X ^ 5 - 963840 * X ^ 6 + 4075136 * X ^ 7 - 1328640 * X ^ 8 - 7514112 * X ^ 9 + 7069696 * X ^ 10) * L3 + (-47 + 540 * X - 1688 * X ^ 2 - 1696 * X ^ 3 + 15760 * X ^ 4 - 12352 * X ^ 5 - 33024 * X ^ 6 + 41984 * X ^ 7) * L4
  have hne : (4 * X ^ 3 - 64 * X ^ 4 + 320 * X ^ 5 - 4736 * X ^ 7 + 10240 * X ^ 8 + 19456 * X ^ 9 - 81920 * X ^ 10 + 1024 * X ^ 11 + 245760 * X ^ 12 - 163840 * X ^ 13 - 262144 * X ^ 14 + 262144 * X ^ 15 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 3
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

end Pa161006

theorem OMA.solution : type_of% @OMA.S_oeis_a161006.main := by
  intro n hn
  obtain ⟨S1, S2, h1, h2, hL⟩ := Pa161006.facts
  have e := congrArg (coeff n) (Pa161006.ode2 S1 S2 A h1 h2 hL)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  simp only [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega, show k + 7 - 3 = k + 4 by omega, show k + 7 - 4 = k + 3 by omega, show k + 7 - 5 = k + 2 by omega, show k + 7 - 6 = k + 1 by omega, show k + 7 - 7 = k by omega]
  simp only [Pa161006.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa161006.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
