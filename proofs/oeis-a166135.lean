import OMAStatements.S_oeis_a166135
import Mathlib

open OMA.S_oeis_a166135
open PowerSeries

namespace P166135

theorem nC (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem cXd (F : PowerSeries ℚ) (k : ℕ) : coeff k (X * d⁄dX ℚ F) = coeff k F * k := by
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

theorem ne_of_cc (p : PowerSeries ℚ) (h : constantCoeff p ≠ 0) : p ≠ 0 := by
  intro h0; rw [h0, map_zero] at h; exact h rfl

set_option maxHeartbeats 4000000 in
theorem ode (G U T : PowerSeries ℚ) (hG : G * 2 = U - 1) (hU : X * U ^ 2 = 2 - 2 * T - 3 * X) (hT : T ^ 2 = 1 - 4 * X) (hT0 : constantCoeff T = 1) (hU0 : constantCoeff U = 1) :
    (-12 * X ^ 2 - 12 * X) * (G) + (-108 * X ^ 3 - 54 * X ^ 2 - 19 * X + 2) * (X * d⁄dX ℚ G) + (-216 * X ^ 3 - 78 * X ^ 2 + 17 * X + 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ G)) = 6 * X ^ 2 + 6 * X := by
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
  have key : (X ^ 0 * (2)) ^ 3 * (X ^ 1 * (2 * U)) ^ 3 * (X ^ 0 * (2 * T)) ^ 3 * (X ^ 1 * (1)) ^ 2 * (X ^ 0 * (1)) ^ 4 * (-216 * X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ G)) - 324 * X ^ 4 * (d⁄dX ℚ G) - 78 * X ^ 4 * (d⁄dX ℚ (d⁄dX ℚ G)) - 132 * X ^ 3 * (d⁄dX ℚ G) + 17 * X ^ 3 * (d⁄dX ℚ (d⁄dX ℚ G)) - 12 * X ^ 2 * G - 2 * X ^ 2 * (d⁄dX ℚ G) + 4 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ G)) - 6 * X ^ 2 - 12 * X * G + 6 * X * (d⁄dX ℚ G) - 6 * X) = 0 := by
    linear_combination (165888 * X ^ 8 - 82944 * X ^ 7 * T ^ 2 + 165888 * X ^ 7 * T - 9216 * X ^ 7 - 55296 * X ^ 6 * T ^ 2 + 101376 * X ^ 6 * T - 55296 * X ^ 6 - 4608 * X ^ 5 * T ^ 3 + 12288 * X ^ 5 * T - 8192 * X ^ 5 + 1792 * X ^ 4 * T ^ 3 - 2048 * X ^ 4 * T ^ 2) * hT + (-221184 * X ^ 8 + 41472 * X ^ 7 * T ^ 3 - 55296 * X ^ 7 * T ^ 2 - 79872 * X ^ 7 - 1152 * X ^ 6 * U ^ 2 * T ^ 3 + 24192 * X ^ 6 * T ^ 3 - 27648 * X ^ 6 * T ^ 2 + 17408 * X ^ 6 + 448 * X ^ 5 * U ^ 2 * T ^ 3 + 2304 * X ^ 5 * T ^ 4 + 3648 * X ^ 5 * T ^ 3 - 9728 * X ^ 5 * T ^ 2 + 4096 * X ^ 5 - 896 * X ^ 4 * T ^ 4 + 128 * X ^ 4 * T ^ 3 + 1024 * X ^ 4 * T ^ 2) * hU + (-3072 * X ^ 7 * U ^ 3 * T ^ 3 - 3072 * X ^ 6 * U ^ 3 * T ^ 3) * hG + (-27648 * X ^ 9 * U ^ 2 * T * (d⁄dX ℚ T) + 55296 * X ^ 9 * U ^ 2 + 13824 * X ^ 8 * U ^ 2 * T ^ 2 - 9984 * X ^ 8 * U ^ 2 * T * (d⁄dX ℚ T) + 19968 * X ^ 8 * U ^ 2 + 27648 * X ^ 8 * T ^ 2 * (d⁄dX ℚ T) + 82944 * X ^ 8 * T ^ 2 - 55296 * X ^ 8 * T + 6912 * X ^ 7 * U ^ 2 * T ^ 2 + 2176 * X ^ 7 * U ^ 2 * T * (d⁄dX ℚ T) - 4352 * X ^ 7 * U ^ 2 + 9984 * X ^ 7 * T ^ 2 * (d⁄dX ℚ T) + 29952 * X ^ 7 * T ^ 2 - 19968 * X ^ 7 * T + 2432 * X ^ 6 * U ^ 2 * T ^ 2 + 512 * X ^ 6 * U ^ 2 * T * (d⁄dX ℚ T) - 1024 * X ^ 6 * U ^ 2 - 2176 * X ^ 6 * T ^ 2 * (d⁄dX ℚ T) - 6528 * X ^ 6 * T ^ 2 + 4352 * X ^ 6 * T - 256 * X ^ 5 * U ^ 2 * T ^ 2 - 512 * X ^ 5 * T ^ 2 * (d⁄dX ℚ T) - 1536 * X ^ 5 * T ^ 2 + 1024 * X ^ 5 * T) * hT1 + (27648 * X ^ 9 * U ^ 2 * T ^ 2 + 9984 * X ^ 8 * U ^ 2 * T ^ 2 - 2176 * X ^ 7 * U ^ 2 * T ^ 2 - 512 * X ^ 6 * U ^ 2 * T ^ 2) * hT2 + (27648 * X ^ 9 * U * (d⁄dX ℚ U) * T ^ 3 + 9984 * X ^ 8 * U * (d⁄dX ℚ U) * T ^ 3 - 27648 * X ^ 8 * T ^ 3 * (d⁄dX ℚ T) - 41472 * X ^ 8 * T ^ 3 - 1920 * X ^ 7 * U ^ 2 * T ^ 3 - 2176 * X ^ 7 * U * (d⁄dX ℚ U) * T ^ 3 - 9984 * X ^ 7 * T ^ 3 * (d⁄dX ℚ T) - 14976 * X ^ 7 * T ^ 3 - 3520 * X ^ 6 * U ^ 2 * T ^ 3 - 512 * X ^ 6 * U * (d⁄dX ℚ U) * T ^ 3 + 2176 * X ^ 6 * T ^ 3 * (d⁄dX ℚ T) + 3264 * X ^ 6 * T ^ 3 + 512 * X ^ 5 * T ^ 3 * (d⁄dX ℚ T) + 768 * X ^ 5 * T ^ 3) * hU1 + (-27648 * X ^ 9 * U ^ 2 * T ^ 3 - 9984 * X ^ 8 * U ^ 2 * T ^ 3 + 2176 * X ^ 7 * U ^ 2 * T ^ 3 + 512 * X ^ 6 * U ^ 2 * T ^ 3) * hU2 + (-82944 * X ^ 9 * U ^ 3 * T ^ 3 - 33792 * X ^ 8 * U ^ 3 * T ^ 3 - 512 * X ^ 7 * U ^ 3 * T ^ 3 + 1536 * X ^ 6 * U ^ 3 * T ^ 3) * hG1 + (-55296 * X ^ 10 * U ^ 3 * T ^ 3 - 19968 * X ^ 9 * U ^ 3 * T ^ 3 + 4352 * X ^ 8 * U ^ 3 * T ^ 3 + 1024 * X ^ 7 * U ^ 3 * T ^ 3) * hG2
  have hf0 : (X ^ 0 * (2) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C, hT0, hU0])
  have hf1 : (X ^ 1 * (2 * U) : PowerSeries ℚ) ≠ 0 := mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (ne_of_cc _ (by simp [nC, constantCoeff_C, hT0, hU0]))
  have hf2 : (X ^ 0 * (2 * T) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C, hT0, hU0])
  have hf3 : (X ^ 1 * (1) : PowerSeries ℚ) ≠ 0 := by simp [PowerSeries.X_ne_zero]
  have hf4 : (X ^ 0 * (1) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C, hT0, hU0])
  have hE := (mul_eq_zero.mp key).resolve_left (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hf0) (pow_ne_zero _ hf1)) (pow_ne_zero _ hf2)) (pow_ne_zero _ hf3)) (pow_ne_zero _ hf4))
  have th2 : X * d⁄dX ℚ (X * d⁄dX ℚ G) = 1 * X ^ 1 * (d⁄dX ℚ G) + 1 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ G)) := by
    simp only [Derivation.leibniz, derivative_X, smul_eq_mul, map_add, map_mul, nC, derivative_C]
    try simp only [map_ofNat]
    ring
  rw [th2]
  linear_combination hE

end P166135

theorem OMA.solution : type_of% @OMA.S_oeis_a166135.main := by
  intro T U G hT hT0 hU hU0 hG hG0 n hn
  rw [coeff_zero_eq_constantCoeff_apply] at hT0 hU0
  have e := congrArg (coeff n) (P166135.ode G U T hG hU hT hT0 hU0)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega]
  norm_num only at e ⊢
  simp only [P166135.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, P166135.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
