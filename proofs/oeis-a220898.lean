import OMAStatements.S_oeis_a220898
import Mathlib

open OMA.S_oeis_a220898
open PowerSeries

namespace P220898

theorem nC (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem cXd (F : PowerSeries ℚ) (k : ℕ) : coeff k (X * d⁄dX ℚ F) = coeff k F * k := by
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

theorem ne_of_cc (p : PowerSeries ℚ) (h : constantCoeff p ≠ 0) : p ≠ 0 := by
  intro h0; rw [h0, map_zero] at h; exact h rfl

set_option maxHeartbeats 4000000 in
theorem ode (G T : PowerSeries ℚ) (hG : G = T * (3 - T)) (hT : (1 + X) * T = (1 + X) + X * T ^ 3) (hT0 : constantCoeff T = 1) :
    (-4 * X + 2) * (G) + (-23 * X ^ 3 - 40 * X ^ 2 - 11 * X + 6) * (X * d⁄dX ℚ G) + (-23 * X ^ 3 - 42 * X ^ 2 - 15 * X + 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) = 4 * X + 4 := by
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
  have hT1 := congrArg (d⁄dX ℚ) hT
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hT1
  try simp only [map_ofNat] at hT1
  try push_cast at hT1
  have hT2 := congrArg (d⁄dX ℚ) hT1
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hT2
  try simp only [map_ofNat] at hT2
  try push_cast at hT2
  have key : (X ^ 0 * (1)) ^ 3 * (X ^ 0 * (-3 * X * T ^ 2 + X + 1)) ^ 3 * (X ^ 1 * (-1)) ^ 6 * (-23 * X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ G)) - 46 * X ^ 4 * (d⁄dX ℚ G) - 42 * X ^ 4 * (d⁄dX ℚ (d⁄dX ℚ G)) - 82 * X ^ 3 * (d⁄dX ℚ G) - 15 * X ^ 3 * (d⁄dX ℚ (d⁄dX ℚ G)) - 26 * X ^ 2 * (d⁄dX ℚ G) + 4 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ G)) - 4 * X * G + 10 * X * (d⁄dX ℚ G) - 4 * X + 2 * G - 4) = 0 := by
    linear_combination (-138 * X ^ 11 * T ^ 5 + 414 * X ^ 11 * T ^ 4 + 92 * X ^ 11 * T ^ 3 - 552 * X ^ 11 * T ^ 2 + 460 * X ^ 11 * T - 46 * X ^ 11 - 216 * X ^ 10 * T ^ 5 + 702 * X ^ 10 * T ^ 4 + 236 * X ^ 10 * T ^ 3 - 834 * X ^ 10 * T ^ 2 + 338 * X ^ 10 * T + 48 * X ^ 10 + 90 * X ^ 9 * T ^ 5 - 162 * X ^ 9 * T ^ 4 + 84 * X ^ 9 * T ^ 3 - 198 * X ^ 9 * T ^ 2 - 182 * X ^ 9 * T + 208 * X ^ 9 + 6 * X ^ 8 * T ^ 5 + 36 * X ^ 8 * T ^ 4 - 64 * X ^ 8 * T ^ 3 + 60 * X ^ 8 * T ^ 2 - 26 * X ^ 8 * T + 92 * X ^ 8 - 4 * X ^ 7 * T ^ 3 - 24 * X ^ 7 * T ^ 2 + 32 * X ^ 7 * T - 18 * X ^ 7 - 2 * X ^ 6 * T + 4 * X ^ 6) * hT + (108 * X ^ 10 * T ^ 6 - 108 * X ^ 10 * T ^ 4 + 36 * X ^ 10 * T ^ 2 - 4 * X ^ 10 - 54 * X ^ 9 * T ^ 6 - 54 * X ^ 9 * T ^ 4 + 54 * X ^ 9 * T ^ 2 - 10 * X ^ 9 + 54 * X ^ 8 * T ^ 4 - 6 * X ^ 8 - 18 * X ^ 7 * T ^ 2 + 2 * X ^ 7 + 2 * X ^ 6) * hG + (-414 * X ^ 13 * T ^ 4 * (d⁄dX ℚ T) + 1242 * X ^ 13 * T ^ 3 * (d⁄dX ℚ T) - 414 * X ^ 13 * T * (d⁄dX ℚ T) + 46 * X ^ 13 * (d⁄dX ℚ T) + 138 * X ^ 12 * T ^ 5 - 756 * X ^ 12 * T ^ 4 * (d⁄dX ℚ T) - 414 * X ^ 12 * T ^ 4 + 2268 * X ^ 12 * T ^ 3 * (d⁄dX ℚ T) - 92 * X ^ 12 * T ^ 3 + 552 * X ^ 12 * T ^ 2 - 1170 * X ^ 12 * T * (d⁄dX ℚ T) - 460 * X ^ 12 * T + 176 * X ^ 12 * (d⁄dX ℚ T) + 46 * X ^ 12 + 216 * X ^ 11 * T ^ 5 - 270 * X ^ 11 * T ^ 4 * (d⁄dX ℚ T) - 702 * X ^ 11 * T ^ 4 + 810 * X ^ 11 * T ^ 3 * (d⁄dX ℚ T) - 374 * X ^ 11 * T ^ 3 + 1386 * X ^ 11 * T ^ 2 - 1026 * X ^ 11 * T * (d⁄dX ℚ T) - 798 * X ^ 11 * T + 244 * X ^ 11 * (d⁄dX ℚ T) - 2 * X ^ 11 + 18 * X ^ 10 * T ^ 5 + 72 * X ^ 10 * T ^ 4 * (d⁄dX ℚ T) - 162 * X ^ 10 * T ^ 4 - 216 * X ^ 10 * T ^ 3 * (d⁄dX ℚ T) - 408 * X ^ 10 * T ^ 3 + 1008 * X ^ 10 * T ^ 2 - 198 * X ^ 10 * T * (d⁄dX ℚ T) - 140 * X ^ 10 * T + 136 * X ^ 10 * (d⁄dX ℚ T) - 252 * X ^ 10 - 60 * X ^ 9 * T ^ 5 + 126 * X ^ 9 * T ^ 4 - 62 * X ^ 9 * T ^ 3 + 66 * X ^ 9 * T ^ 2 + 72 * X ^ 9 * T * (d⁄dX ℚ T) + 254 * X ^ 9 * T + 14 * X ^ 9 * (d⁄dX ℚ T) - 284 * X ^ 9 + 64 * X ^ 8 * T ^ 3 - 108 * X ^ 8 * T ^ 2 + 36 * X ^ 8 * T - 8 * X ^ 8 * (d⁄dX ℚ T) - 50 * X ^ 8 - 20 * X ^ 7 * T + 30 * X ^ 7) * hT1 + (414 * X ^ 13 * T ^ 5 - 621 * X ^ 13 * T ^ 4 - 276 * X ^ 13 * T ^ 3 + 414 * X ^ 13 * T ^ 2 + 46 * X ^ 13 * T - 69 * X ^ 13 + 756 * X ^ 12 * T ^ 5 - 1134 * X ^ 12 * T ^ 4 - 780 * X ^ 12 * T ^ 3 + 1170 * X ^ 12 * T ^ 2 + 176 * X ^ 12 * T - 264 * X ^ 12 + 270 * X ^ 11 * T ^ 5 - 405 * X ^ 11 * T ^ 4 - 684 * X ^ 11 * T ^ 3 + 1026 * X ^ 11 * T ^ 2 + 244 * X ^ 11 * T - 366 * X ^ 11 - 72 * X ^ 10 * T ^ 5 + 108 * X ^ 10 * T ^ 4 - 132 * X ^ 10 * T ^ 3 + 198 * X ^ 10 * T ^ 2 + 136 * X ^ 10 * T - 204 * X ^ 10 + 48 * X ^ 9 * T ^ 3 - 72 * X ^ 9 * T ^ 2 + 14 * X ^ 9 * T - 21 * X ^ 9 - 8 * X ^ 8 * T + 12 * X ^ 8) * hT2 + (1242 * X ^ 13 * T ^ 6 - 1242 * X ^ 13 * T ^ 4 + 414 * X ^ 13 * T ^ 2 - 46 * X ^ 13 + 2214 * X ^ 12 * T ^ 6 - 3456 * X ^ 12 * T ^ 4 + 1566 * X ^ 12 * T ^ 2 - 220 * X ^ 12 + 702 * X ^ 11 * T ^ 6 - 2916 * X ^ 11 * T ^ 4 + 2124 * X ^ 11 * T ^ 2 - 410 * X ^ 11 - 270 * X ^ 10 * T ^ 6 - 432 * X ^ 10 * T ^ 4 + 1116 * X ^ 10 * T ^ 2 - 360 * X ^ 10 + 270 * X ^ 9 * T ^ 4 + 54 * X ^ 9 * T ^ 2 - 130 * X ^ 9 - 90 * X ^ 8 * T ^ 2 + 4 * X ^ 8 + 10 * X ^ 7) * hG1 + (621 * X ^ 14 * T ^ 6 - 621 * X ^ 14 * T ^ 4 + 207 * X ^ 14 * T ^ 2 - 23 * X ^ 14 + 1134 * X ^ 13 * T ^ 6 - 1755 * X ^ 13 * T ^ 4 + 792 * X ^ 13 * T ^ 2 - 111 * X ^ 13 + 405 * X ^ 12 * T ^ 6 - 1539 * X ^ 12 * T ^ 4 + 1098 * X ^ 12 * T ^ 2 - 210 * X ^ 12 - 108 * X ^ 11 * T ^ 6 - 297 * X ^ 11 * T ^ 4 + 612 * X ^ 11 * T ^ 2 - 190 * X ^ 11 + 108 * X ^ 10 * T ^ 4 + 63 * X ^ 10 * T ^ 2 - 75 * X ^ 10 - 36 * X ^ 9 * T ^ 2 - 3 * X ^ 9 + 4 * X ^ 8) * hG2
  have hf0 : (X ^ 0 * (1) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C, hT0])
  have hf1 : (X ^ 0 * (-3 * X * T ^ 2 + X + 1) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C, hT0])
  have hf2 : (X ^ 1 * (-1) : PowerSeries ℚ) ≠ 0 := by simp [PowerSeries.X_ne_zero]
  have hE := (mul_eq_zero.mp key).resolve_left (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hf0) (pow_ne_zero _ hf1)) (pow_ne_zero _ hf2))
  have th2 : X * d⁄dX ℚ (X * d⁄dX ℚ G) = 1 * X ^ 1 * (d⁄dX ℚ G) + 1 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ G)) := by
    simp only [Derivation.leibniz, derivative_X, smul_eq_mul, map_add, map_mul, nC, derivative_C]
    try simp only [map_ofNat]
    ring
  rw [th2]
  linear_combination hE

end P220898

theorem OMA.solution : type_of% @OMA.S_oeis_a220898.main := by
  intro T G hT hG hG0 n hn
  have hT0 : constantCoeff T = 1 := by
    have h := congrArg constantCoeff hT
    simp [map_ofNat] at h
    linear_combination h
  have e := congrArg (coeff n) (P220898.ode G T hG hT hT0)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  norm_num only at e ⊢
  simp only [P220898.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, P220898.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
