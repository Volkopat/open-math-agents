import OMAStatements.S_oeis_a220899
import Mathlib

open OMA.S_oeis_a220899
open PowerSeries

namespace P220899

theorem nC (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem cXd (F : PowerSeries ℚ) (k : ℕ) : coeff k (X * d⁄dX ℚ F) = coeff k F * k := by
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

theorem ne_of_cc (p : PowerSeries ℚ) (h : constantCoeff p ≠ 0) : p ≠ 0 := by
  intro h0; rw [h0, map_zero] at h; exact h rfl

set_option maxHeartbeats 4000000 in
theorem ode (G P U : PowerSeries ℚ) (hG : G = (1 - X) * P) (hP : P = U * (3 - U)) (hU : (1 + X) * U = (1 + X) + X * U ^ 3) (hU0 : constantCoeff U = 1) :
    (-48 * X ^ 4 - 90 * X ^ 3 - 18 * X ^ 2 + 2 * X + 2) * (G) + (23 * X ^ 5 + 44 * X ^ 4 - 8 * X ^ 3 - 50 * X ^ 2 - 15 * X + 6) * (X * d⁄dX ℚ G) + (-23 * X ^ 5 + 4 * X ^ 4 + 46 * X ^ 3 - 8 * X ^ 2 - 23 * X + 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) = -4 * X ^ 4 + 8 * X ^ 3 - 8 * X + 4 := by
  have hG1 := congrArg (d⁄dX ℚ) hG
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hG1
  try simp only [map_ofNat] at hG1
  try push_cast at hG1
  have hG2 := congrArg (d⁄dX ℚ) hG1
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hG2
  try simp only [map_ofNat] at hG2
  try push_cast at hG2
  have hP1 := congrArg (d⁄dX ℚ) hP
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hP1
  try simp only [map_ofNat] at hP1
  try push_cast at hP1
  have hP2 := congrArg (d⁄dX ℚ) hP1
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hP2
  try simp only [map_ofNat] at hP2
  try push_cast at hP2
  have hU1 := congrArg (d⁄dX ℚ) hU
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hU1
  try simp only [map_ofNat] at hU1
  try push_cast at hU1
  have hU2 := congrArg (d⁄dX ℚ) hU1
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hU2
  try simp only [map_ofNat] at hU2
  try push_cast at hU2
  have key : (X ^ 0 * (1)) ^ 6 * (X ^ 0 * (-3 * X * U ^ 2 + X + 1)) ^ 3 * (X ^ 1 * (-1)) ^ 6 * (-23 * X ^ 7 * (d⁄dX ℚ (d⁄dX ℚ G)) + 4 * X ^ 6 * (d⁄dX ℚ (d⁄dX ℚ G)) + 48 * X ^ 5 * (d⁄dX ℚ G) + 46 * X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ G)) - 48 * X ^ 4 * G + 38 * X ^ 4 * (d⁄dX ℚ G) - 8 * X ^ 4 * (d⁄dX ℚ (d⁄dX ℚ G)) + 4 * X ^ 4 - 90 * X ^ 3 * G - 58 * X ^ 3 * (d⁄dX ℚ G) - 23 * X ^ 3 * (d⁄dX ℚ (d⁄dX ℚ G)) - 8 * X ^ 3 - 18 * X ^ 2 * G - 38 * X ^ 2 * (d⁄dX ℚ G) + 4 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ G)) + 2 * X * G + 10 * X * (d⁄dX ℚ G) + 8 * X + 2 * G - 4) = 0 := by
    linear_combination (138 * X ^ 14 * U ^ 5 - 414 * X ^ 14 * U ^ 4 - 92 * X ^ 14 * U ^ 3 + 552 * X ^ 14 * U ^ 2 - 460 * X ^ 14 * U + 46 * X ^ 14 - 198 * X ^ 13 * U ^ 5 + 540 * X ^ 13 * U ^ 4 + 40 * X ^ 13 * U ^ 3 - 822 * X ^ 13 * U ^ 2 + 1042 * X ^ 13 * U - 186 * X ^ 13 - 324 * X ^ 12 * U ^ 5 + 1026 * X ^ 12 * U ^ 4 + 348 * X ^ 12 * U ^ 3 - 648 * X ^ 12 * U ^ 2 - 184 * X ^ 12 * U + 74 * X ^ 12 + 774 * X ^ 11 * U ^ 5 - 2214 * X ^ 11 * U ^ 4 - 300 * X ^ 11 * U ^ 3 + 1296 * X ^ 11 * U ^ 2 - 1074 * X ^ 11 * U + 342 * X ^ 11 - 468 * X ^ 10 * U ^ 5 + 1296 * X ^ 10 * U ^ 4 - 204 * X ^ 10 * U ^ 3 - 36 * X ^ 10 * U ^ 2 + 774 * X ^ 10 * U - 282 * X ^ 10 + 72 * X ^ 9 * U ^ 5 - 270 * X ^ 9 * U ^ 4 + 264 * X ^ 9 * U ^ 3 - 450 * X ^ 9 * U ^ 2 - 6 * X ^ 9 * U - 126 * X ^ 9 + 6 * X ^ 8 * U ^ 5 + 36 * X ^ 8 * U ^ 4 - 52 * X ^ 8 * U ^ 3 + 132 * X ^ 8 * U ^ 2 - 128 * X ^ 8 * U + 158 * X ^ 8 - 4 * X ^ 7 * U ^ 3 - 24 * X ^ 7 * U ^ 2 + 38 * X ^ 7 * U - 30 * X ^ 7 - 2 * X ^ 6 * U + 4 * X ^ 6) * hU + (-108 * X ^ 13 * U ^ 6 + 108 * X ^ 13 * U ^ 4 - 36 * X ^ 13 * U ^ 2 + 4 * X ^ 13 + 378 * X ^ 12 * U ^ 6 - 270 * X ^ 12 * U ^ 4 + 54 * X ^ 12 * U ^ 2 - 2 * X ^ 12 - 486 * X ^ 11 * U ^ 6 + 108 * X ^ 11 * U ^ 4 + 54 * X ^ 11 * U ^ 2 - 12 * X ^ 11 + 270 * X ^ 10 * U ^ 6 + 216 * X ^ 10 * U ^ 4 - 108 * X ^ 10 * U ^ 2 + 6 * X ^ 10 - 54 * X ^ 9 * U ^ 6 - 216 * X ^ 9 * U ^ 4 + 12 * X ^ 9 + 54 * X ^ 8 * U ^ 4 + 54 * X ^ 8 * U ^ 2 - 6 * X ^ 8 - 18 * X ^ 7 * U ^ 2 - 4 * X ^ 7 + 2 * X ^ 6) * hP + (1296 * X ^ 13 * U ^ 6 - 1296 * X ^ 13 * U ^ 4 + 432 * X ^ 13 * U ^ 2 - 48 * X ^ 13 + 2430 * X ^ 12 * U ^ 6 - 3726 * X ^ 12 * U ^ 4 + 1674 * X ^ 12 * U ^ 2 - 234 * X ^ 12 + 486 * X ^ 11 * U ^ 6 - 2916 * X ^ 11 * U ^ 4 + 2214 * X ^ 11 * U ^ 2 - 432 * X ^ 11 - 54 * X ^ 10 * U ^ 6 - 432 * X ^ 10 * U ^ 4 + 1116 * X ^ 10 * U ^ 2 - 370 * X ^ 10 - 54 * X ^ 9 * U ^ 6 + 108 * X ^ 9 * U ^ 4 + 108 * X ^ 9 * U ^ 2 - 136 * X ^ 9 + 54 * X ^ 8 * U ^ 4 - 54 * X ^ 8 * U ^ 2 - 6 * X ^ 8 - 18 * X ^ 7 * U ^ 2 + 8 * X ^ 7 + 2 * X ^ 6) * hG + (414 * X ^ 16 * U ^ 4 * (d⁄dX ℚ U) - 1242 * X ^ 16 * U ^ 3 * (d⁄dX ℚ U) + 414 * X ^ 16 * U * (d⁄dX ℚ U) - 46 * X ^ 16 * (d⁄dX ℚ U) - 138 * X ^ 15 * U ^ 5 - 486 * X ^ 15 * U ^ 4 * (d⁄dX ℚ U) + 414 * X ^ 15 * U ^ 4 + 1458 * X ^ 15 * U ^ 3 * (d⁄dX ℚ U) + 92 * X ^ 15 * U ^ 3 - 552 * X ^ 15 * U ^ 2 - 72 * X ^ 15 * U * (d⁄dX ℚ U) + 460 * X ^ 15 * U - 38 * X ^ 15 * (d⁄dX ℚ U) - 46 * X ^ 15 + 198 * X ^ 14 * U ^ 5 - 756 * X ^ 14 * U ^ 4 * (d⁄dX ℚ U) - 540 * X ^ 14 * U ^ 4 + 2268 * X ^ 14 * U ^ 3 * (d⁄dX ℚ U) + 98 * X ^ 14 * U ^ 3 + 270 * X ^ 14 * U ^ 2 - 1242 * X ^ 14 * U * (d⁄dX ℚ U) - 582 * X ^ 14 * U + 146 * X ^ 14 * (d⁄dX ℚ U) + 140 * X ^ 14 + 216 * X ^ 13 * U ^ 5 + 972 * X ^ 13 * U ^ 4 * (d⁄dX ℚ U) - 702 * X ^ 13 * U ^ 4 - 2916 * X ^ 13 * U ^ 3 * (d⁄dX ℚ U) - 438 * X ^ 13 * U ^ 3 + 1494 * X ^ 13 * U ^ 2 + 216 * X ^ 13 * U * (d⁄dX ℚ U) - 874 * X ^ 13 * U + 114 * X ^ 13 * (d⁄dX ℚ U) + 108 * X ^ 13 - 396 * X ^ 12 * U ^ 5 + 270 * X ^ 12 * U ^ 4 * (d⁄dX ℚ U) + 1080 * X ^ 12 * U ^ 4 - 810 * X ^ 12 * U ^ 3 * (d⁄dX ℚ U) - 132 * X ^ 12 * U ^ 3 - 648 * X ^ 12 * U ^ 2 + 1242 * X ^ 12 * U * (d⁄dX ℚ U) + 1260 * X ^ 12 * U - 162 * X ^ 12 * (d⁄dX ℚ U) - 420 * X ^ 12 - 18 * X ^ 11 * U ^ 5 - 486 * X ^ 11 * U ^ 4 * (d⁄dX ℚ U) + 162 * X ^ 11 * U ^ 4 + 1458 * X ^ 11 * U ^ 3 * (d⁄dX ℚ U) + 600 * X ^ 11 * U ^ 3 - 1332 * X ^ 11 * U ^ 2 - 216 * X ^ 11 * U * (d⁄dX ℚ U) + 348 * X ^ 11 * U - 114 * X ^ 11 * (d⁄dX ℚ U) - 48 * X ^ 11 + 198 * X ^ 10 * U ^ 5 + 72 * X ^ 10 * U ^ 4 * (d⁄dX ℚ U) - 540 * X ^ 10 * U ^ 4 - 216 * X ^ 10 * U ^ 3 * (d⁄dX ℚ U) - 30 * X ^ 10 * U ^ 3 + 486 * X ^ 10 * U ^ 2 - 414 * X ^ 10 * U * (d⁄dX ℚ U) - 774 * X ^ 10 * U + 70 * X ^ 10 * (d⁄dX ℚ U) + 420 * X ^ 10 - 60 * X ^ 9 * U ^ 5 + 126 * X ^ 9 * U ^ 4 - 254 * X ^ 9 * U ^ 3 + 390 * X ^ 9 * U ^ 2 + 72 * X ^ 9 * U * (d⁄dX ℚ U) + 86 * X ^ 9 * U + 38 * X ^ 9 * (d⁄dX ℚ U) - 44 * X ^ 9 + 64 * X ^ 8 * U ^ 3 - 108 * X ^ 8 * U ^ 2 + 96 * X ^ 8 * U - 8 * X ^ 8 * (d⁄dX ℚ U) - 140 * X ^ 8 - 20 * X ^ 7 * U + 30 * X ^ 7) * hU1 + (-414 * X ^ 16 * U ^ 5 + 621 * X ^ 16 * U ^ 4 + 276 * X ^ 16 * U ^ 3 - 414 * X ^ 16 * U ^ 2 - 46 * X ^ 16 * U + 69 * X ^ 16 + 486 * X ^ 15 * U ^ 5 - 729 * X ^ 15 * U ^ 4 - 48 * X ^ 15 * U ^ 3 + 72 * X ^ 15 * U ^ 2 - 38 * X ^ 15 * U + 57 * X ^ 15 + 756 * X ^ 14 * U ^ 5 - 1134 * X ^ 14 * U ^ 4 - 828 * X ^ 14 * U ^ 3 + 1242 * X ^ 14 * U ^ 2 + 146 * X ^ 14 * U - 219 * X ^ 14 - 972 * X ^ 13 * U ^ 5 + 1458 * X ^ 13 * U ^ 4 + 144 * X ^ 13 * U ^ 3 - 216 * X ^ 13 * U ^ 2 + 114 * X ^ 13 * U - 171 * X ^ 13 - 270 * X ^ 12 * U ^ 5 + 405 * X ^ 12 * U ^ 4 + 828 * X ^ 12 * U ^ 3 - 1242 * X ^ 12 * U ^ 2 - 162 * X ^ 12 * U + 243 * X ^ 12 + 486 * X ^ 11 * U ^ 5 - 729 * X ^ 11 * U ^ 4 - 144 * X ^ 11 * U ^ 3 + 216 * X ^ 11 * U ^ 2 - 114 * X ^ 11 * U + 171 * X ^ 11 - 72 * X ^ 10 * U ^ 5 + 108 * X ^ 10 * U ^ 4 - 276 * X ^ 10 * U ^ 3 + 414 * X ^ 10 * U ^ 2 + 70 * X ^ 10 * U - 105 * X ^ 10 + 48 * X ^ 9 * U ^ 3 - 72 * X ^ 9 * U ^ 2 + 38 * X ^ 9 * U - 57 * X ^ 9 - 8 * X ^ 8 * U + 12 * X ^ 8) * hU2 + (-1242 * X ^ 16 * U ^ 6 + 1242 * X ^ 16 * U ^ 4 - 414 * X ^ 16 * U ^ 2 + 46 * X ^ 16 + 1512 * X ^ 15 * U ^ 6 - 270 * X ^ 15 * U ^ 4 - 324 * X ^ 15 * U ^ 2 + 82 * X ^ 15 + 2214 * X ^ 14 * U ^ 6 - 3726 * X ^ 14 * U ^ 4 + 1332 * X ^ 14 * U ^ 2 - 112 * X ^ 14 - 3024 * X ^ 13 * U ^ 6 + 810 * X ^ 13 * U ^ 4 + 972 * X ^ 13 * U ^ 2 - 256 * X ^ 13 - 702 * X ^ 12 * U ^ 6 + 3726 * X ^ 12 * U ^ 4 - 1512 * X ^ 12 * U ^ 2 + 60 * X ^ 12 + 1512 * X ^ 11 * U ^ 6 - 810 * X ^ 11 * U ^ 4 - 972 * X ^ 11 * U ^ 2 + 276 * X ^ 11 - 270 * X ^ 10 * U ^ 6 - 1242 * X ^ 10 * U ^ 4 + 684 * X ^ 10 * U ^ 2 + 32 * X ^ 10 + 270 * X ^ 9 * U ^ 4 + 324 * X ^ 9 * U ^ 2 - 112 * X ^ 9 - 90 * X ^ 8 * U ^ 2 - 26 * X ^ 8 + 10 * X ^ 7) * hP1 + (-621 * X ^ 17 * U ^ 6 + 621 * X ^ 17 * U ^ 4 - 207 * X ^ 17 * U ^ 2 + 23 * X ^ 17 + 729 * X ^ 16 * U ^ 6 - 108 * X ^ 16 * U ^ 4 - 171 * X ^ 16 * U ^ 2 + 42 * X ^ 16 + 1134 * X ^ 15 * U ^ 6 - 1863 * X ^ 15 * U ^ 4 + 657 * X ^ 15 * U ^ 2 - 54 * X ^ 15 - 1458 * X ^ 14 * U ^ 6 + 324 * X ^ 14 * U ^ 4 + 513 * X ^ 14 * U ^ 2 - 130 * X ^ 14 - 405 * X ^ 13 * U ^ 6 + 1863 * X ^ 13 * U ^ 4 - 729 * X ^ 13 * U ^ 2 + 24 * X ^ 13 + 729 * X ^ 12 * U ^ 6 - 324 * X ^ 12 * U ^ 4 - 513 * X ^ 12 * U ^ 2 + 138 * X ^ 12 - 108 * X ^ 11 * U ^ 6 - 621 * X ^ 11 * U ^ 4 + 315 * X ^ 11 * U ^ 2 + 22 * X ^ 11 + 108 * X ^ 10 * U ^ 4 + 171 * X ^ 10 * U ^ 2 - 54 * X ^ 10 - 36 * X ^ 9 * U ^ 2 - 15 * X ^ 9 + 4 * X ^ 8) * hP2 + (-1296 * X ^ 14 * U ^ 6 + 1296 * X ^ 14 * U ^ 4 - 432 * X ^ 14 * U ^ 2 + 48 * X ^ 14 - 1026 * X ^ 13 * U ^ 6 + 2322 * X ^ 13 * U ^ 4 - 1206 * X ^ 13 * U ^ 2 + 182 * X ^ 13 + 1566 * X ^ 12 * U ^ 6 - 540 * X ^ 12 * U ^ 4 - 594 * X ^ 12 * U ^ 2 + 200 * X ^ 12 + 1026 * X ^ 11 * U ^ 6 - 2592 * X ^ 11 * U ^ 4 + 1044 * X ^ 11 * U ^ 2 - 50 * X ^ 11 - 270 * X ^ 10 * U ^ 6 - 756 * X ^ 10 * U ^ 4 + 1116 * X ^ 10 * U ^ 2 - 240 * X ^ 10 + 270 * X ^ 9 * U ^ 4 + 162 * X ^ 9 * U ^ 2 - 142 * X ^ 9 - 90 * X ^ 8 * U ^ 2 - 8 * X ^ 8 + 10 * X ^ 7) * hG1 + (621 * X ^ 16 * U ^ 6 - 621 * X ^ 16 * U ^ 4 + 207 * X ^ 16 * U ^ 2 - 23 * X ^ 16 - 108 * X ^ 15 * U ^ 6 - 513 * X ^ 15 * U ^ 4 + 378 * X ^ 15 * U ^ 2 - 65 * X ^ 15 - 1242 * X ^ 14 * U ^ 6 + 1350 * X ^ 14 * U ^ 4 - 279 * X ^ 14 * U ^ 2 - 11 * X ^ 14 + 216 * X ^ 13 * U ^ 6 + 1026 * X ^ 13 * U ^ 4 - 792 * X ^ 13 * U ^ 2 + 119 * X ^ 13 + 621 * X ^ 12 * U ^ 6 - 837 * X ^ 12 * U ^ 4 - 63 * X ^ 12 * U ^ 2 + 95 * X ^ 12 - 108 * X ^ 11 * U ^ 6 - 513 * X ^ 11 * U ^ 4 + 450 * X ^ 11 * U ^ 2 - 43 * X ^ 11 + 108 * X ^ 10 * U ^ 4 + 135 * X ^ 10 * U ^ 2 - 65 * X ^ 10 - 36 * X ^ 9 * U ^ 2 - 11 * X ^ 9 + 4 * X ^ 8) * hG2
  have hf0 : (X ^ 0 * (1) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C, hU0])
  have hf1 : (X ^ 0 * (-3 * X * U ^ 2 + X + 1) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C, hU0])
  have hf2 : (X ^ 1 * (-1) : PowerSeries ℚ) ≠ 0 := by simp [PowerSeries.X_ne_zero]
  have hE := (mul_eq_zero.mp key).resolve_left (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hf0) (pow_ne_zero _ hf1)) (pow_ne_zero _ hf2))
  have th2 : X * d⁄dX ℚ (X * d⁄dX ℚ G) = 1 * X ^ 1 * (d⁄dX ℚ G) + 1 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ G)) := by
    simp only [Derivation.leibniz, derivative_X, smul_eq_mul, map_add, map_mul, nC, derivative_C]
    try simp only [map_ofNat]
    ring
  rw [th2]
  linear_combination hE

lemma prep (Y T P : PowerSeries ℚ) (hY : Y * (1 + X) = X) (hT : T = 1 + X * T ^ 3)
    (hP : P = (T * (3 - T)).subst Y) :
    ∃ U : PowerSeries ℚ, P = U * (3 - U) ∧ (1 + X) * U = (1 + X) + X * U ^ 3 ∧ constantCoeff U = 1 := by
  have hY0 : constantCoeff Y = 0 := by
    have h := congrArg constantCoeff hY
    simpa using h
  have hs : HasSubst Y := HasSubst.of_constantCoeff_zero' hY0
  refine ⟨substAlgHom hs T, ?_, ?_, ?_⟩
  · rw [hP, ← coe_substAlgHom hs, map_mul, map_sub, map_ofNat]
  · have h := congrArg (substAlgHom hs) hT
    rw [map_add, map_one, map_mul, map_pow, substAlgHom_X] at h
    have h2 : (1 + X) * substAlgHom hs T = (1 + X) * (1 + Y * substAlgHom hs T ^ 3) := by rw [← h]
    rw [h2]
    linear_combination (substAlgHom hs T ^ 3) * hY
  · have h := congrArg (substAlgHom hs) hT
    rw [map_add, map_one, map_mul, map_pow, substAlgHom_X] at h
    have h3 := congrArg constantCoeff h
    rw [map_add, map_one, map_mul, hY0, zero_mul, add_zero] at h3
    exact h3

end P220899

theorem OMA.solution : type_of% @OMA.S_oeis_a220899.main := by
  intro Y T P G hY hT hP hG n hn
  obtain ⟨U, hPU, hU, hU0⟩ := P220899.prep Y T P hY hT hP
  have e := congrArg (coeff n) (P220899.ode G P U hG hPU hU hU0)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
  simp only [show k + 7 - 1 = k + 6 by omega, show k + 7 - 2 = k + 5 by omega,
    show k + 7 - 3 = k + 4 by omega, show k + 7 - 4 = k + 3 by omega,
    show k + 7 - 5 = k + 2 by omega]
  norm_num only at e ⊢
  simp only [P220899.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, P220899.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
