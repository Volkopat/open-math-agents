import OMAStatements.S_oeis_a128734
import Mathlib

open OMA.S_oeis_a128734
open PowerSeries

namespace Pa128734

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
theorem ode (S A : PowerSeries ℚ) (hS : S ^ 2 = 1 - 6 * X + 5 * X ^ 2)
    (hL : (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3) * A = (-2 * X + 17 * X ^ 2 - 40 * X ^ 3 + 26 * X ^ 4 - 5 * X ^ 5) + (2 * X - 11 * X ^ 2 + 11 * X ^ 3 - 3 * X ^ 4) * S) :
    (-260 + 1440 * X - 1200 * X ^ 2 + 140 * X ^ 3) * (A) + (342 - 1580 * X + 1384 * X ^ 2 - 240 * X ^ 3) * (X * d⁄dX ℚ A) + (-88 + 479 * X - 488 * X ^ 2 + 115 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) + (6 - 39 * X + 48 * X ^ 2 - 15 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) = 0 := by
  have hdD : d⁄dX ℚ (1 - 6 * X + 5 * X ^ 2 : PowerSeries ℚ) = -6 + 10 * X := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have hS1 := sq_step S _ hS
  rw [hdD] at hS1
  have L0 := hL
  have dP1 : d⁄dX ℚ (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3 : PowerSeries ℚ) = -48 + 84 * X - 30 * X ^ 2 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU1 : d⁄dX ℚ (-2 * X + 17 * X ^ 2 - 40 * X ^ 3 + 26 * X ^ 4 - 5 * X ^ 5 : PowerSeries ℚ) = -2 + 34 * X - 120 * X ^ 2 + 104 * X ^ 3 - 25 * X ^ 4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV1 : d⁄dX ℚ (2 * X - 11 * X ^ 2 + 11 * X ^ 3 - 3 * X ^ 4 : PowerSeries ℚ) = 2 - 22 * X + 33 * X ^ 2 - 12 * X ^ 3 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E1 := th_step _ _ _ _ _ L0
  simp only [dP1, dU1, dV1] at E1
  have L1 : (-8 + 96 * X - 370 * X ^ 2 + 502 * X ^ 3 - 270 * X ^ 4 + 50 * X ^ 5) * (X * d⁄dX ℚ A) = (2 * X - 34 * X ^ 2 + 211 * X ^ 3 - 571 * X ^ 4 + 637 * X ^ 5 - 295 * X ^ 6 + 50 * X ^ 7) + (-2 * X + 28 * X ^ 2 - 131 * X ^ 3 + 222 * X ^ 4 - 145 * X ^ 5 + 30 * X ^ 6) * S := by
    have hg : (-4 + 2 * X : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (4 * X - 26 * X ^ 2 + 32 * X ^ 3 - 10 * X ^ 4) * E1 + (24 * X - 54 * X ^ 2 + 30 * X ^ 3) * L0 + (4 * X ^ 2 - 24 * X ^ 3 + 33 * X ^ 4 - 17 * X ^ 5 + 3 * X ^ 6) * hS1
  have dP2 : d⁄dX ℚ (-8 + 96 * X - 370 * X ^ 2 + 502 * X ^ 3 - 270 * X ^ 4 + 50 * X ^ 5 : PowerSeries ℚ) = 96 - 740 * X + 1506 * X ^ 2 - 1080 * X ^ 3 + 250 * X ^ 4 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU2 : d⁄dX ℚ (2 * X - 34 * X ^ 2 + 211 * X ^ 3 - 571 * X ^ 4 + 637 * X ^ 5 - 295 * X ^ 6 + 50 * X ^ 7 : PowerSeries ℚ) = 2 - 68 * X + 633 * X ^ 2 - 2284 * X ^ 3 + 3185 * X ^ 4 - 1770 * X ^ 5 + 350 * X ^ 6 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV2 : d⁄dX ℚ (-2 * X + 28 * X ^ 2 - 131 * X ^ 3 + 222 * X ^ 4 - 145 * X ^ 5 + 30 * X ^ 6 : PowerSeries ℚ) = -2 + 56 * X - 393 * X ^ 2 + 888 * X ^ 3 - 725 * X ^ 4 + 180 * X ^ 5 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E2 := th_step _ _ _ _ _ L1
  simp only [dP2, dU2, dV2] at E2
  have L2 : (16 - 296 * X + 2116 * X ^ 2 - 7390 * X ^ 3 + 13466 * X ^ 4 - 13492 * X ^ 5 + 7480 * X ^ 6 - 2150 * X ^ 7 + 250 * X ^ 8) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = (-4 * X + 114 * X ^ 2 - 1260 * X ^ 3 + 6979 * X ^ 4 - 20793 * X ^ 5 + 33828 * X ^ 6 - 30974 * X ^ 7 + 16035 * X ^ 8 - 4425 * X ^ 9 + 500 * X ^ 10) + (4 * X - 102 * X ^ 2 + 962 * X ^ 3 - 4273 * X ^ 4 + 9766 * X ^ 5 - 11848 * X ^ 6 + 7600 * X ^ 7 - 2405 * X ^ 8 + 300 * X ^ 9) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-4 * X + 26 * X ^ 2 - 32 * X ^ 3 + 10 * X ^ 4) * E2 + (-48 * X + 106 * X ^ 2 - 50 * X ^ 3) * L1 + (4 * X ^ 2 - 58 * X ^ 3 + 290 * X ^ 4 - 575 * X ^ 5 + 512 * X ^ 6 - 205 * X ^ 7 + 30 * X ^ 8) * hS1
  have dP3 : d⁄dX ℚ (16 - 296 * X + 2116 * X ^ 2 - 7390 * X ^ 3 + 13466 * X ^ 4 - 13492 * X ^ 5 + 7480 * X ^ 6 - 2150 * X ^ 7 + 250 * X ^ 8 : PowerSeries ℚ) = -296 + 4232 * X - 22170 * X ^ 2 + 53864 * X ^ 3 - 67460 * X ^ 4 + 44880 * X ^ 5 - 15050 * X ^ 6 + 2000 * X ^ 7 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dU3 : d⁄dX ℚ (-4 * X + 114 * X ^ 2 - 1260 * X ^ 3 + 6979 * X ^ 4 - 20793 * X ^ 5 + 33828 * X ^ 6 - 30974 * X ^ 7 + 16035 * X ^ 8 - 4425 * X ^ 9 + 500 * X ^ 10 : PowerSeries ℚ) = -4 + 228 * X - 3780 * X ^ 2 + 27916 * X ^ 3 - 103965 * X ^ 4 + 202968 * X ^ 5 - 216818 * X ^ 6 + 128280 * X ^ 7 - 39825 * X ^ 8 + 5000 * X ^ 9 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have dV3 : d⁄dX ℚ (4 * X - 102 * X ^ 2 + 962 * X ^ 3 - 4273 * X ^ 4 + 9766 * X ^ 5 - 11848 * X ^ 6 + 7600 * X ^ 7 - 2405 * X ^ 8 + 300 * X ^ 9 : PowerSeries ℚ) = 4 - 204 * X + 2886 * X ^ 2 - 17092 * X ^ 3 + 48830 * X ^ 4 - 71088 * X ^ 5 + 53200 * X ^ 6 - 19240 * X ^ 7 + 2700 * X ^ 8 := by
      simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
        add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one, map_zero,
        neg_zero]
      try simp only [map_ofNat]
      try push_cast
      try ring
  have E3 := th_step _ _ _ _ _ L2
  simp only [dP3, dU3, dV3] at E3
  have L3 : (-32 + 800 * X - 8336 * X ^ 2 + 47104 * X ^ 3 - 158338 * X ^ 4 + 330862 * X ^ 5 - 442762 * X ^ 6 + 384742 * X ^ 7 - 215590 * X ^ 8 + 75050 * X ^ 9 - 14750 * X ^ 10 + 1250 * X ^ 11) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) = (8 * X - 360 * X ^ 2 + 6030 * X ^ 3 - 52170 * X ^ 4 + 262575 * X ^ 5 - 810081 * X ^ 6 + 1577039 * X ^ 7 - 1989369 * X ^ 8 + 1652013 * X ^ 9 - 898635 * X ^ 10 + 307575 * X ^ 11 - 59625 * X ^ 12 + 5000 * X ^ 13) + (-8 * X + 336 * X ^ 2 - 5038 * X ^ 3 + 37680 * X ^ 4 - 161755 * X ^ 5 + 420796 * X ^ 6 - 677289 * X ^ 7 + 681172 * X ^ 8 - 425725 * X ^ 9 + 160480 * X ^ 10 - 33625 * X ^ 11 + 3000 * X ^ 12) * S := by
    have hg : (2 : PowerSeries ℚ) ≠ 0 := by
      apply ne_of_coeff _ 0
      simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
    apply mul_left_cancel₀ hg
    linear_combination (-4 * X + 26 * X ^ 2 - 32 * X ^ 3 + 10 * X ^ 4) * E3 + (-74 * X + 170 * X ^ 2 - 80 * X ^ 3) * L2 + (-8 * X ^ 2 + 208 * X ^ 3 - 2026 * X ^ 4 + 9508 * X ^ 5 - 23805 * X ^ 6 + 33462 * X ^ 7 - 27048 * X ^ 8 + 12410 * X ^ 9 - 3005 * X ^ 10 + 300 * X ^ 11) * hS1
  have key : (32 - 800 * X + 8336 * X ^ 2 - 47104 * X ^ 3 + 158338 * X ^ 4 - 330862 * X ^ 5 + 442762 * X ^ 6 - 384742 * X ^ 7 + 215590 * X ^ 8 - 75050 * X ^ 9 + 14750 * X ^ 10 - 1250 * X ^ 11) * (((-260 + 1440 * X - 1200 * X ^ 2 + 140 * X ^ 3) * (A) + (342 - 1580 * X + 1384 * X ^ 2 - 240 * X ^ 3) * (X * d⁄dX ℚ A) + (-88 + 479 * X - 488 * X ^ 2 + 115 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) + (6 - 39 * X + 48 * X ^ 2 - 15 * X ^ 3) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A)))) - (0)) = 0 := by
    linear_combination (-1040 + 25520 * X - 261140 * X ^ 2 + 1449800 * X ^ 3 - 4787420 * X ^ 4 + 9802940 * X ^ 5 - 12756100 * X ^ 6 + 10615180 * X ^ 7 - 5550340 * X ^ 8 + 1728100 * X ^ 9 - 283000 * X ^ 10 + 17500 * X ^ 11) * L0 + (-1368 + 24104 * X - 167382 * X ^ 2 + 590180 * X ^ 3 - 1155844 * X ^ 4 + 1323944 * X ^ 5 - 900214 * X ^ 6 + 353580 * X ^ 7 - 73000 * X ^ 8 + 6000 * X ^ 9) * L1 + (-176 + 2102 * X - 8611 * X ^ 2 + 14678 * X ^ 3 - 11698 * X ^ 4 + 4280 * X ^ 5 - 575 * X ^ 6) * L2 + (-6 + 39 * X - 48 * X ^ 2 + 15 * X ^ 3) * L3
  have hne : (32 - 800 * X + 8336 * X ^ 2 - 47104 * X ^ 3 + 158338 * X ^ 4 - 330862 * X ^ 5 + 442762 * X ^ 6 - 384742 * X ^ 7 + 215590 * X ^ 8 - 75050 * X ^ 9 + 14750 * X ^ 10 - 1250 * X ^ 11 : PowerSeries ℚ) ≠ 0 := by
    apply ne_of_coeff _ 0
    simp [nC, coeff_X_pow, coeff_X, coeff_one, coeff_C_mul]
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

theorem S_sq : S ^ 2 = 1 - 6 * X + 5 * X ^ 2 := by
  have hB : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = (1 + X : PowerSeries ℚ) := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    norm_num
    simpa using binomialSeries_nat (A := ℚ) (R := ℚ) 1
  have h0 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])
  unfold S
  rw [← subst_pow h0, hB, ← coe_substAlgHom h0, map_add, map_one,
    coe_substAlgHom, subst_X h0, R]
  ring

theorem gf_eq : (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3) * ((-2 * X + 17 * X ^ 2 - 40 * X ^ 3 + 26 * X ^ 4 - 5 * X ^ 5 + (2 * X - 11 * X ^ 2 + 11 * X ^ 3 - 3 * X ^ 4) * S) * (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3 : PowerSeries ℚ)⁻¹) = -2 * X + 17 * X ^ 2 - 40 * X ^ 3 + 26 * X ^ 4 - 5 * X ^ 5 + (2 * X - 11 * X ^ 2 + 11 * X ^ 3 - 3 * X ^ 4) * S := by
  have hd : constantCoeff (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero, constantCoeff_C]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3 : PowerSeries ℚ) hd
  linear_combination (-2 * X + 17 * X ^ 2 - 40 * X ^ 3 + 26 * X ^ 4 - 5 * X ^ 5 + (2 * X - 11 * X ^ 2 + 11 * X ^ 3 - 3 * X ^ 4) * S) * hinv

end Pa128734

theorem OMA.solution : type_of% @OMA.S_oeis_a128734.main := by
  intro n hn
  have hL := Pa128734.gf_eq
  have ha : ∀ m, a m = coeff ((m + 2)) ((-2 * X + 17 * X ^ 2 - 40 * X ^ 3 + 26 * X ^ 4 - 5 * X ^ 5 + (2 * X - 11 * X ^ 2 + 11 * X ^ 3 - 3 * X ^ 4) * S) * (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((-2 * X + 17 * X ^ 2 - 40 * X ^ 3 + 26 * X ^ 4 - 5 * X ^ 5 + (2 * X - 11 * X ^ 2 + 11 * X ^ 3 - 3 * X ^ 4) * S) * (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3 : PowerSeries ℚ)⁻¹) = A at hL ha
  have hL' : (8 - 48 * X + 42 * X ^ 2 - 10 * X ^ 3) * A = (-2 * X + 17 * X ^ 2 - 40 * X ^ 3 + 26 * X ^ 4 - 5 * X ^ 5) + (2 * X - 11 * X ^ 2 + 11 * X ^ 3 - 3 * X ^ 4) * S := by
    linear_combination hL
  have e := congrArg (coeff ((n + 2))) (Pa128734.ode S A Pa128734.S_sq hL')
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega, show k + 3 - 3 = k by omega]
  simp only [ha, add_assoc]
  norm_num only at e ⊢
  simp only [Pa128734.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa128734.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
