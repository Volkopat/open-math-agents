import OMAStatements.S_oeis_a290265
import Mathlib

open OMA.S_oeis_a290265
open PowerSeries

namespace P290265

theorem nC (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem cXd (F : PowerSeries ℚ) (k : ℕ) : coeff k (X * d⁄dX ℚ F) = coeff k F * k := by
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

theorem ne_of_cc (p : PowerSeries ℚ) (h : constantCoeff p ≠ 0) : p ≠ 0 := by
  intro h0; rw [h0, map_zero] at h; exact h rfl

namespace M

set_option maxHeartbeats 4000000 in
theorem ode (m T : PowerSeries ℚ) (hm : 2 * X ^ 2 * m = 1 - X - T) (hT : T ^ 2 = 1 - 2 * X - 3 * X ^ 2) (hT0 : constantCoeff T = 1) :
    (-1836 * X ^ 8 - 6048 * X ^ 7 - 7134 * X ^ 6 - 3708 * X ^ 5 - 1362 * X ^ 4 - 1848 * X ^ 3 - 570 * X ^ 2 - 60 * X + 94) * (m) + (-3168 * X ^ 8 - 9690 * X ^ 7 - 10167 * X ^ 6 - 5124 * X ^ 5 - 2925 * X ^ 4 - 1918 * X ^ 3 - 73 * X ^ 2 + 268 * X + 109) * (X * d⁄dX ℚ m) + (-1539 * X ^ 8 - 4149 * X ^ 7 - 3888 * X ^ 6 - 2267 * X ^ 5 - 1316 * X ^ 4 - 123 * X ^ 3 + 384 * X ^ 2 + 131 * X - 1) * (X * d⁄dX ℚ (X * d⁄dX ℚ m)) + (-207 * X ^ 8 - 507 * X ^ 7 - 459 * X ^ 6 - 311 * X ^ 5 - 97 * X ^ 4 + 187 * X ^ 3 + 139 * X ^ 2 - 9 * X - 16) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ m))) = 594 * X ^ 5 + 930 * X ^ 4 - 192 * X ^ 3 + 120 * X ^ 2 + 126 * X + 94 := by
  have hm1 := congrArg (d⁄dX ℚ) hm
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hm1
  try simp only [map_ofNat] at hm1
  try push_cast at hm1
  have hm2 := congrArg (d⁄dX ℚ) hm1
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hm2
  try simp only [map_ofNat] at hm2
  try push_cast at hm2
  have hm3 := congrArg (d⁄dX ℚ) hm2
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hm3
  try simp only [map_ofNat] at hm3
  try push_cast at hm3
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
  have hT3 := congrArg (d⁄dX ℚ) hT2
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hT3
  try simp only [map_ofNat] at hT3
  try push_cast at hT3
  have key : (X ^ 2 * (2)) ^ 4 * (X ^ 0 * (2 * T)) ^ 5 * (X ^ 0 * (1)) ^ 3 * (-207 * X ^ 11 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ m))) - 2160 * X ^ 10 * (d⁄dX ℚ (d⁄dX ℚ m)) - 507 * X ^ 10 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ m))) - 4914 * X ^ 9 * (d⁄dX ℚ m) - 5670 * X ^ 9 * (d⁄dX ℚ (d⁄dX ℚ m)) - 459 * X ^ 9 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ m))) - 1836 * X ^ 8 * m - 14346 * X ^ 8 * (d⁄dX ℚ m) - 5265 * X ^ 8 * (d⁄dX ℚ (d⁄dX ℚ m)) - 311 * X ^ 8 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ m))) - 6048 * X ^ 7 * m - 14514 * X ^ 7 * (d⁄dX ℚ m) - 3200 * X ^ 7 * (d⁄dX ℚ (d⁄dX ℚ m)) - 97 * X ^ 7 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ m))) - 7134 * X ^ 6 * m - 7702 * X ^ 6 * (d⁄dX ℚ m) - 1607 * X ^ 6 * (d⁄dX ℚ (d⁄dX ℚ m)) + 187 * X ^ 6 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ m))) - 3708 * X ^ 5 * m - 4338 * X ^ 5 * (d⁄dX ℚ m) + 438 * X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ m)) + 139 * X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ m))) - 594 * X ^ 5 - 1362 * X ^ 4 * m - 1854 * X ^ 4 * (d⁄dX ℚ m) + 801 * X ^ 4 * (d⁄dX ℚ (d⁄dX ℚ m)) - 9 * X ^ 4 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ m))) - 930 * X ^ 4 - 1848 * X ^ 3 * m + 450 * X ^ 3 * (d⁄dX ℚ m) + 104 * X ^ 3 * (d⁄dX ℚ (d⁄dX ℚ m)) - 16 * X ^ 3 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ m))) + 192 * X ^ 3 - 570 * X ^ 2 * m + 390 * X ^ 2 * (d⁄dX ℚ m) - 49 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ m)) - 120 * X ^ 2 - 60 * X * m + 92 * X * (d⁄dX ℚ m) - 126 * X + 94 * m - 94) = 0 := by
    linear_combination (-1430784 * X ^ 18 - 3981312 * X ^ 17 - 705024 * X ^ 16 * T ^ 2 - 4976640 * X ^ 16 - 2018304 * X ^ 15 * T ^ 2 - 4552704 * X ^ 15 - 2029824 * X ^ 14 * T ^ 2 - 2631168 * X ^ 14 - 202752 * X ^ 13 * T ^ 4 - 1405440 * X ^ 13 * T ^ 2 + 24576 * X ^ 13 - 337920 * X ^ 12 * T ^ 4 - 1009408 * X ^ 12 * T ^ 2 + 1056768 * X ^ 12 + 10240 * X ^ 11 * T ^ 4 - 611328 * X ^ 11 * T ^ 2 + 608256 * X ^ 11 - 280320 * X ^ 10 * T ^ 2 + 142080 * X ^ 10 - 87552 * X ^ 9 * T ^ 2 + 12288 * X ^ 9 - 12032 * X ^ 8 * T ^ 2) * hT + (202752 * X ^ 13 * T ^ 5 + 337920 * X ^ 12 * T ^ 5 - 10240 * X ^ 11 * T ^ 5) * hm + (715392 * X ^ 19 - 238464 * X ^ 18 * T * (d⁄dX ℚ T) + 2229120 * X ^ 18 + 79488 * X ^ 17 * T ^ 2 * (d⁄dX ℚ T) ^ 2 + 590976 * X ^ 17 * T ^ 2 - 663552 * X ^ 17 * T * (d⁄dX ℚ T) + 2833920 * X ^ 17 - 117504 * X ^ 16 * T ^ 3 * (d⁄dX ℚ T) + 194688 * X ^ 16 * T ^ 2 * (d⁄dX ℚ T) ^ 2 + 1710720 * X ^ 16 * T ^ 2 - 723456 * X ^ 16 * T * (d⁄dX ℚ T) + 2327040 * X ^ 16 - 336384 * X ^ 15 * T ^ 3 * (d⁄dX ℚ T) + 176256 * X ^ 15 * T ^ 2 * (d⁄dX ℚ T) ^ 2 + 1829376 * X ^ 15 * T ^ 2 - 534528 * X ^ 15 * T * (d⁄dX ℚ T) + 1228032 * X ^ 15 + 101376 * X ^ 14 * T ^ 4 - 321408 * X ^ 14 * T ^ 3 * (d⁄dX ℚ T) + 119424 * X ^ 14 * T ^ 2 * (d⁄dX ℚ T) ^ 2 + 1191936 * X ^ 14 * T ^ 2 - 231168 * X ^ 14 * T * (d⁄dX ℚ T) - 303360 * X ^ 14 + 219648 * X ^ 13 * T ^ 4 - 170752 * X ^ 13 * T ^ 3 * (d⁄dX ℚ T) + 37248 * X ^ 13 * T ^ 2 * (d⁄dX ℚ T) ^ 2 + 676096 * X ^ 13 * T ^ 2 + 178176 * X ^ 13 * T * (d⁄dX ℚ T) - 873984 * X ^ 13 + 64000 * X ^ 12 * T ^ 4 - 131200 * X ^ 12 * T ^ 3 * (d⁄dX ℚ T) - 71808 * X ^ 12 * T ^ 2 * (d⁄dX ℚ T) ^ 2 + 178432 * X ^ 12 * T ^ 2 + 231936 * X ^ 12 * T * (d⁄dX ℚ T) - 360960 * X ^ 12 - 44032 * X ^ 11 * T ^ 4 - 87552 * X ^ 11 * T ^ 3 * (d⁄dX ℚ T) - 53376 * X ^ 11 * T ^ 2 * (d⁄dX ℚ T) ^ 2 - 59904 * X ^ 11 * T ^ 2 + 43008 * X ^ 11 * T * (d⁄dX ℚ T) + 22656 * X ^ 11 + 30720 * X ^ 10 * T ^ 4 - 4224 * X ^ 10 * T ^ 3 * (d⁄dX ℚ T) + 3456 * X ^ 10 * T ^ 2 * (d⁄dX ℚ T) ^ 2 - 46080 * X ^ 10 * T ^ 2 - 21888 * X ^ 10 * T * (d⁄dX ℚ T) + 40320 * X ^ 10 + 32256 * X ^ 9 * T ^ 4 + 20224 * X ^ 9 * T ^ 3 * (d⁄dX ℚ T) + 6144 * X ^ 9 * T ^ 2 * (d⁄dX ℚ T) ^ 2 - 19840 * X ^ 9 * T ^ 2 - 6144 * X ^ 9 * T * (d⁄dX ℚ T) + 6144 * X ^ 9 + 24064 * X ^ 8 * T ^ 4 + 6016 * X ^ 8 * T ^ 3 * (d⁄dX ℚ T) - 6016 * X ^ 8 * T ^ 2) * hT1 + (-79488 * X ^ 17 * T ^ 3 * (d⁄dX ℚ T) + 117504 * X ^ 16 * T ^ 4 - 194688 * X ^ 16 * T ^ 3 * (d⁄dX ℚ T) + 336384 * X ^ 15 * T ^ 4 - 176256 * X ^ 15 * T ^ 3 * (d⁄dX ℚ T) + 321408 * X ^ 14 * T ^ 4 - 119424 * X ^ 14 * T ^ 3 * (d⁄dX ℚ T) + 170752 * X ^ 13 * T ^ 4 - 37248 * X ^ 13 * T ^ 3 * (d⁄dX ℚ T) + 131200 * X ^ 12 * T ^ 4 + 71808 * X ^ 12 * T ^ 3 * (d⁄dX ℚ T) + 87552 * X ^ 11 * T ^ 4 + 53376 * X ^ 11 * T ^ 3 * (d⁄dX ℚ T) + 4224 * X ^ 10 * T ^ 4 - 3456 * X ^ 10 * T ^ 3 * (d⁄dX ℚ T) - 20224 * X ^ 9 * T ^ 4 - 6144 * X ^ 9 * T ^ 3 * (d⁄dX ℚ T) - 6016 * X ^ 8 * T ^ 4) * hT2 + (26496 * X ^ 17 * T ^ 4 + 64896 * X ^ 16 * T ^ 4 + 58752 * X ^ 15 * T ^ 4 + 39808 * X ^ 14 * T ^ 4 + 12416 * X ^ 13 * T ^ 4 - 23936 * X ^ 12 * T ^ 4 - 17792 * X ^ 11 * T ^ 4 + 1152 * X ^ 10 * T ^ 4 + 2048 * X ^ 9 * T ^ 4) * hT3 + (-202752 * X ^ 14 * T ^ 5 - 439296 * X ^ 13 * T ^ 5 - 128000 * X ^ 12 * T ^ 5 + 88064 * X ^ 11 * T ^ 5 - 61440 * X ^ 10 * T ^ 5 - 64512 * X ^ 9 * T ^ 5 - 48128 * X ^ 8 * T ^ 5) * hm1 + (-235008 * X ^ 16 * T ^ 5 - 672768 * X ^ 15 * T ^ 5 - 642816 * X ^ 14 * T ^ 5 - 341504 * X ^ 13 * T ^ 5 - 262400 * X ^ 12 * T ^ 5 - 175104 * X ^ 11 * T ^ 5 - 8448 * X ^ 10 * T ^ 5 + 40448 * X ^ 9 * T ^ 5 + 12032 * X ^ 8 * T ^ 5) * hm2 + (-52992 * X ^ 17 * T ^ 5 - 129792 * X ^ 16 * T ^ 5 - 117504 * X ^ 15 * T ^ 5 - 79616 * X ^ 14 * T ^ 5 - 24832 * X ^ 13 * T ^ 5 + 47872 * X ^ 12 * T ^ 5 + 35584 * X ^ 11 * T ^ 5 - 2304 * X ^ 10 * T ^ 5 - 4096 * X ^ 9 * T ^ 5) * hm3
  have hf0 : (X ^ 2 * (2) : PowerSeries ℚ) ≠ 0 := mul_ne_zero (pow_ne_zero _ PowerSeries.X_ne_zero) (ne_of_cc _ (by simp [nC, constantCoeff_C]))
  have hf1 : (X ^ 0 * (2 * T) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C, hT0])
  have hf2 : (X ^ 0 * (1) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C, hT0])
  have hE := (mul_eq_zero.mp key).resolve_left (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hf0) (pow_ne_zero _ hf1)) (pow_ne_zero _ hf2))
  have th2 : X * d⁄dX ℚ (X * d⁄dX ℚ m) = 1 * X ^ 1 * (d⁄dX ℚ m) + 1 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ m)) := by
    simp only [Derivation.leibniz, derivative_X, smul_eq_mul, map_add, map_mul, nC, derivative_C]
    try simp only [map_ofNat]
    ring
  have th3 : X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ m)) = 1 * X ^ 1 * (d⁄dX ℚ m) + 3 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ m)) + 1 * X ^ 3 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ m))) := by
    simp only [Derivation.leibniz, derivative_X, smul_eq_mul, th2, Derivation.map_one_eq_zero, map_add, map_mul, nC, derivative_C]
    try simp only [map_ofNat]
    ring
  rw [th3, th2]
  linear_combination hE

end M

namespace Bq

set_option maxHeartbeats 4000000 in
theorem ode (B T : PowerSeries ℚ) (hB : 2 * (1 - 3 * X) * B = 1 - 3 * X + T) (hT : T ^ 2 = 1 - 2 * X - 3 * X ^ 2) (hT0 : constantCoeff T = 1) :
    (2 * X) * (B) + (3 * X ^ 2 + 2 * X - 1) * (X * d⁄dX ℚ B) = X := by
  have hB1 := congrArg (d⁄dX ℚ) hB
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hB1
  try simp only [map_ofNat] at hB1
  try push_cast at hB1
  have hT1 := congrArg (d⁄dX ℚ) hT
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hT1
  try simp only [map_ofNat] at hT1
  try push_cast at hT1
  have key : (X ^ 0 * (-6 * X + 2)) ^ 2 * (X ^ 0 * (2 * T)) ^ 1 * (X ^ 0 * (1)) ^ 1 * (3 * X ^ 3 * (d⁄dX ℚ B) + 2 * X ^ 2 * (d⁄dX ℚ B) + 2 * X * B - X * (d⁄dX ℚ B) - X) = 0 := by
    linear_combination (36 * X ^ 3 - 4 * X) * hT + (36 * X ^ 3 * T - 4 * X * T) * hB + (-18 * X ^ 4 - 6 * X ^ 3 + 10 * X ^ 2 - 2 * X) * hT1 + (-36 * X ^ 4 * T - 12 * X ^ 3 * T + 20 * X ^ 2 * T - 4 * X * T) * hB1
  have hf0 : (X ^ 0 * (-6 * X + 2) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C, hT0])
  have hf1 : (X ^ 0 * (2 * T) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C, hT0])
  have hf2 : (X ^ 0 * (1) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C, hT0])
  have hE := (mul_eq_zero.mp key).resolve_left (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hf0) (pow_ne_zero _ hf1)) (pow_ne_zero _ hf2))
  linear_combination hE

end Bq

theorem recm (T m : PowerSeries ℚ) (hm : 2 * X ^ 2 * m = 1 - X - T) (hT : T ^ 2 = 1 - 2 * X - 3 * X ^ 2) (hT0 : constantCoeff T = 1) :
    ∀ n : ℕ, 8 ≤ n → (94 + 109 * (n : ℚ) - (n : ℚ) ^ 2 - 16 * (n : ℚ) ^ 3) * coeff n m + (-188 - 21 * (n : ℚ) + 158 * (n : ℚ) ^ 2 - 9 * (n : ℚ) ^ 3) * coeff (n - 1) m + (59 * (n : ℚ) - 450 * (n : ℚ) ^ 2 + 139 * (n : ℚ) ^ 3) * coeff (n - 2) m + (-2250 + 3869 * (n : ℚ) - 1806 * (n : ℚ) ^ 2 + 187 * (n : ℚ) ^ 3) * coeff (n - 3) m + (-4510 + 2947 * (n : ℚ) - 152 * (n : ℚ) ^ 2 - 97 * (n : ℚ) ^ 3) * coeff (n - 4) m + (4112 - 5779 * (n : ℚ) + 2398 * (n : ℚ) ^ 2 - 311 * (n : ℚ) ^ 3) * coeff (n - 5) m + (13044 - 13083 * (n : ℚ) + 4374 * (n : ℚ) ^ 2 - 459 * (n : ℚ) ^ 3) * coeff (n - 6) m + (32382 - 26133 * (n : ℚ) + 6498 * (n : ℚ) ^ 2 - 507 * (n : ℚ) ^ 3) * coeff (n - 7) m + (30996 - 18288 * (n : ℚ) + 3429 * (n : ℚ) ^ 2 - 207 * (n : ℚ) ^ 3) * coeff (n - 8) m = 0 := by
  intro n hn
  have e := congrArg (coeff n) (M.ode m T hm hT hT0)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
  simp only [show k + 8 - 1 = k + 7 by omega, show k + 8 - 2 = k + 6 by omega, show k + 8 - 3 = k + 5 by omega, show k + 8 - 4 = k + 4 by omega, show k + 8 - 5 = k + 3 by omega, show k + 8 - 6 = k + 2 by omega, show k + 8 - 7 = k + 1 by omega, show k + 8 - 8 = k by omega]
  norm_num only at e ⊢
  simp only [nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e

theorem recB (T B : PowerSeries ℚ) (hB : 2 * (1 - 3 * X) * B = 1 - 3 * X + T) (hT : T ^ 2 = 1 - 2 * X - 3 * X ^ 2) (hT0 : constantCoeff T = 1) :
    ∀ n : ℕ, 2 ≤ n → (-(n : ℚ)) * coeff n B + (2 * (n : ℚ)) * coeff (n - 1) B + (-6 + 3 * (n : ℚ)) * coeff (n - 2) B = 0 := by
  intro n hn
  have e := congrArg (coeff n) (Bq.ode B T hB hT hT0)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp only [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  norm_num only at e ⊢
  simp only [nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e

end P290265


theorem OMA.solution : type_of% @OMA.S_oeis_a290265.main := by
  intro T m B hT hT0 hm hB a ha n hn
  rw [coeff_zero_eq_constantCoeff_apply] at hT0
  obtain ⟨k, rfl | rfl⟩ : ∃ k, n = 2 * k + 8 ∨ n = 2 * k + 9 := ⟨(n - 8) / 2, by omega⟩
  · have hmm := P290265.recm T m hm hT hT0 (2 * k + 8) (by omega)
    simp only [show 2 * k + 8 - 1 = 2 * k + 7 by omega, show 2 * k + 8 - 2 = 2 * k + 6 by omega, show 2 * k + 8 - 3 = 2 * k + 5 by omega, show 2 * k + 8 - 4 = 2 * k + 4 by omega, show 2 * k + 8 - 5 = 2 * k + 3 by omega, show 2 * k + 8 - 6 = 2 * k + 2 by omega, show 2 * k + 8 - 7 = 2 * k + 1 by omega, show 2 * k + 8 - 8 = 2 * k + 0 by omega] at hmm ⊢
    simp only [ha, show 1 + (2 * k + 8) / 2 = k + 5 by omega, show 1 + (2 * k + 7) / 2 = k + 4 by omega, show 1 + (2 * k + 6) / 2 = k + 4 by omega, show 1 + (2 * k + 5) / 2 = k + 3 by omega, show 1 + (2 * k + 4) / 2 = k + 3 by omega, show 1 + (2 * k + 3) / 2 = k + 2 by omega, show 1 + (2 * k + 2) / 2 = k + 2 by omega, show 1 + (2 * k + 1) / 2 = k + 1 by omega, show 1 + (2 * k + 0) / 2 = k + 1 by omega]
    have hb0 := P290265.recB T B hB hT hT0 (k + 5) (by omega)
    simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega] at hb0
    have hb1 := P290265.recB T B hB hT hT0 (k + 4) (by omega)
    simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega] at hb1
    have hb2 := P290265.recB T B hB hT hT0 (k + 3) (by omega)
    simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega] at hb2
    push_cast at hmm hb0 hb1 hb2 ⊢
    linear_combination hmm - (1458 + 900 * (k : ℚ) + 128 * (k : ℚ) ^ 2) * hb0 - (-8352 - 5096 * (k : ℚ) - 784 * (k : ℚ) ^ 2) * hb1 - (-7410 - 7708 * (k : ℚ) - 1904 * (k : ℚ) ^ 2) * hb2
  · have hmm := P290265.recm T m hm hT hT0 (2 * k + 9) (by omega)
    simp only [show 2 * k + 9 - 1 = 2 * k + 8 by omega, show 2 * k + 9 - 2 = 2 * k + 7 by omega, show 2 * k + 9 - 3 = 2 * k + 6 by omega, show 2 * k + 9 - 4 = 2 * k + 5 by omega, show 2 * k + 9 - 5 = 2 * k + 4 by omega, show 2 * k + 9 - 6 = 2 * k + 3 by omega, show 2 * k + 9 - 7 = 2 * k + 2 by omega, show 2 * k + 9 - 8 = 2 * k + 1 by omega] at hmm ⊢
    simp only [ha, show 1 + (2 * k + 9) / 2 = k + 5 by omega, show 1 + (2 * k + 8) / 2 = k + 5 by omega, show 1 + (2 * k + 7) / 2 = k + 4 by omega, show 1 + (2 * k + 6) / 2 = k + 4 by omega, show 1 + (2 * k + 5) / 2 = k + 3 by omega, show 1 + (2 * k + 4) / 2 = k + 3 by omega, show 1 + (2 * k + 3) / 2 = k + 2 by omega, show 1 + (2 * k + 2) / 2 = k + 2 by omega, show 1 + (2 * k + 1) / 2 = k + 1 by omega]
    have hb0 := P290265.recB T B hB hT hT0 (k + 5) (by omega)
    simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega] at hb0
    have hb1 := P290265.recB T B hB hT hT0 (k + 4) (by omega)
    simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega] at hb1
    have hb2 := P290265.recB T B hB hT hT0 (k + 3) (by omega)
    simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega] at hb2
    push_cast at hmm hb0 hb1 hb2 ⊢
    linear_combination hmm - (962 + 1072 * (k : ℚ) + 200 * (k : ℚ) ^ 2) * hb0 - (-19600 - 13208 * (k : ℚ) - 2208 * (k : ℚ) ^ 2) * hb1 - (-2250 - 2328 * (k : ℚ) - 552 * (k : ℚ) ^ 2) * hb2
