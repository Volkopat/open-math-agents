import OMAStatements.S_oeis_a372018
import Mathlib

open OMA.S_oeis_a372018
open PowerSeries

namespace P372018

theorem nC (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem cXd (F : PowerSeries ℚ) (k : ℕ) : coeff k (X * d⁄dX ℚ F) = coeff k F * k := by
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

theorem ne_of_cc (p : PowerSeries ℚ) (h : constantCoeff p ≠ 0) : p ≠ 0 := by
  intro h0; rw [h0, map_zero] at h; exact h rfl

namespace Aq

set_option maxHeartbeats 4000000 in
theorem ode (A : PowerSeries ℚ) (hA : A ^ 2 * (1 - X * A) = 1 - X * A + 4 * X * A) (hA0 : constantCoeff A = 1) :
    (108 * X ^ 4 + 6 * X ^ 2 + 2) * (X * d⁄dX ℚ A) + (135 * X ^ 4 + 36 * X ^ 2 + 1) * (X * d⁄dX ℚ (X * d⁄dX ℚ A)) + (27 * X ^ 4 + 18 * X ^ 2 - 1) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A))) = 4 * X := by
  have hA1 := congrArg (d⁄dX ℚ) hA
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hA1
  try simp only [map_ofNat] at hA1
  try push_cast at hA1
  have hA2 := congrArg (d⁄dX ℚ) hA1
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hA2
  try simp only [map_ofNat] at hA2
  try push_cast at hA2
  have hA3 := congrArg (d⁄dX ℚ) hA2
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hA3
  try simp only [map_ofNat] at hA3
  try push_cast at hA3
  have key : (X ^ 0 * (-3 * X * A ^ 2 - 3 * X + 2 * A)) ^ 5 * (X ^ 1 * (-1)) ^ 9 * (27 * X ^ 7 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ A))) + 216 * X ^ 6 * (d⁄dX ℚ (d⁄dX ℚ A)) + 270 * X ^ 5 * (d⁄dX ℚ A) + 18 * X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ A))) + 90 * X ^ 4 * (d⁄dX ℚ (d⁄dX ℚ A)) + 60 * X ^ 3 * (d⁄dX ℚ A) - X ^ 3 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ A))) - 2 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ A)) + 2 * X * (d⁄dX ℚ A) - 4 * X) = 0 := by
    linear_combination (5346 * X ^ 17 * A ^ 8 + 28674 * X ^ 17 * A ^ 6 + 39366 * X ^ 17 * A ^ 4 + 4374 * X ^ 17 * A ^ 2 - 14256 * X ^ 16 * A ^ 7 - 68040 * X ^ 16 * A ^ 5 - 77760 * X ^ 16 * A ^ 3 - 5832 * X ^ 16 * A - 324 * X ^ 15 * A ^ 8 + 13608 * X ^ 15 * A ^ 6 + 56376 * X ^ 15 * A ^ 4 + 40824 * X ^ 15 * A ^ 2 + 972 * X ^ 15 + 864 * X ^ 14 * A ^ 7 - 4968 * X ^ 14 * A ^ 5 - 19440 * X ^ 14 * A ^ 3 - 3240 * X ^ 14 * A + 126 * X ^ 13 * A ^ 8 - 522 * X ^ 13 * A ^ 6 + 810 * X ^ 13 * A ^ 4 + 1890 * X ^ 13 * A ^ 2 - 336 * X ^ 12 * A ^ 7 - 288 * X ^ 12 * A ^ 5 - 720 * X ^ 12 * A ^ 3 + 240 * X ^ 11 * A ^ 6 + 240 * X ^ 11 * A ^ 4 - 32 * X ^ 10 * A ^ 5) * hA + (-21870 * X ^ 20 * A ^ 6 * (d⁄dX ℚ A) ^ 2 - 39366 * X ^ 20 * A ^ 4 * (d⁄dX ℚ A) ^ 2 - 13122 * X ^ 20 * A ^ 2 * (d⁄dX ℚ A) ^ 2 + 4374 * X ^ 20 * (d⁄dX ℚ A) ^ 2 + 16038 * X ^ 19 * A ^ 7 * (d⁄dX ℚ A) + 43740 * X ^ 19 * A ^ 5 * (d⁄dX ℚ A) ^ 2 + 53946 * X ^ 19 * A ^ 5 * (d⁄dX ℚ A) + 52488 * X ^ 19 * A ^ 3 * (d⁄dX ℚ A) ^ 2 + 42282 * X ^ 19 * A ^ 3 * (d⁄dX ℚ A) + 8748 * X ^ 19 * A * (d⁄dX ℚ A) ^ 2 + 4374 * X ^ 19 * A * (d⁄dX ℚ A) - 5346 * X ^ 18 * A ^ 8 - 14580 * X ^ 18 * A ^ 6 * (d⁄dX ℚ A) ^ 2 - 52002 * X ^ 18 * A ^ 6 * (d⁄dX ℚ A) - 28674 * X ^ 18 * A ^ 6 - 58320 * X ^ 18 * A ^ 4 * (d⁄dX ℚ A) ^ 2 - 116154 * X ^ 18 * A ^ 4 * (d⁄dX ℚ A) - 39366 * X ^ 18 * A ^ 4 - 32076 * X ^ 18 * A ^ 2 * (d⁄dX ℚ A) ^ 2 - 51030 * X ^ 18 * A ^ 2 * (d⁄dX ℚ A) - 4374 * X ^ 18 * A ^ 2 + 1458 * X ^ 18 * (d⁄dX ℚ A) + 1944 * X ^ 17 * A ^ 7 * (d⁄dX ℚ A) + 19602 * X ^ 17 * A ^ 7 + 29160 * X ^ 17 * A ^ 5 * (d⁄dX ℚ A) ^ 2 + 66420 * X ^ 17 * A ^ 5 * (d⁄dX ℚ A) + 75330 * X ^ 17 * A ^ 5 + 45360 * X ^ 17 * A ^ 3 * (d⁄dX ℚ A) ^ 2 + 73872 * X ^ 17 * A ^ 3 * (d⁄dX ℚ A) + 66582 * X ^ 17 * A ^ 3 + 9720 * X ^ 17 * A * (d⁄dX ℚ A) ^ 2 + 2916 * X ^ 17 * A * (d⁄dX ℚ A) + 4374 * X ^ 17 * A + 324 * X ^ 16 * A ^ 8 + 810 * X ^ 16 * A ^ 6 * (d⁄dX ℚ A) ^ 2 - 14256 * X ^ 16 * A ^ 6 * (d⁄dX ℚ A) - 27864 * X ^ 16 * A ^ 6 - 19926 * X ^ 16 * A ^ 4 * (d⁄dX ℚ A) ^ 2 - 58320 * X ^ 16 * A ^ 4 * (d⁄dX ℚ A) - 67392 * X ^ 16 * A ^ 4 - 16362 * X ^ 16 * A ^ 2 * (d⁄dX ℚ A) ^ 2 - 19440 * X ^ 16 * A ^ 2 * (d⁄dX ℚ A) - 17496 * X ^ 16 * A ^ 2 - 2106 * X ^ 16 * (d⁄dX ℚ A) ^ 2 + 3888 * X ^ 16 * (d⁄dX ℚ A) + 972 * X ^ 16 + 378 * X ^ 15 * A ^ 7 * (d⁄dX ℚ A) - 216 * X ^ 15 * A ^ 7 - 1620 * X ^ 15 * A ^ 5 * (d⁄dX ℚ A) ^ 2 + 21222 * X ^ 15 * A ^ 5 * (d⁄dX ℚ A) + 21816 * X ^ 15 * A ^ 5 + 4968 * X ^ 15 * A ^ 3 * (d⁄dX ℚ A) ^ 2 + 29430 * X ^ 15 * A ^ 3 * (d⁄dX ℚ A) + 21384 * X ^ 15 * A ^ 3 + 2268 * X ^ 15 * A * (d⁄dX ℚ A) ^ 2 + 810 * X ^ 15 * A * (d⁄dX ℚ A) - 8424 * X ^ 15 * A - 126 * X ^ 14 * A ^ 8 - 342 * X ^ 14 * A ^ 6 * (d⁄dX ℚ A) - 1854 * X ^ 14 * A ^ 6 + 1188 * X ^ 14 * A ^ 4 * (d⁄dX ℚ A) ^ 2 - 10494 * X ^ 14 * A ^ 4 * (d⁄dX ℚ A) - 12474 * X ^ 14 * A ^ 4 - 4914 * X ^ 14 * A ^ 2 * (d⁄dX ℚ A) - 810 * X ^ 14 * A ^ 2 + 108 * X ^ 14 * (d⁄dX ℚ A) ^ 2 - 378 * X ^ 14 * (d⁄dX ℚ A) + 462 * X ^ 13 * A ^ 7 - 156 * X ^ 13 * A ^ 5 * (d⁄dX ℚ A) + 3582 * X ^ 13 * A ^ 5 - 384 * X ^ 13 * A ^ 3 * (d⁄dX ℚ A) ^ 2 + 1368 * X ^ 13 * A ^ 3 * (d⁄dX ℚ A) + 5130 * X ^ 13 * A ^ 3 - 144 * X ^ 13 * A * (d⁄dX ℚ A) ^ 2 + 324 * X ^ 13 * A * (d⁄dX ℚ A) + 810 * X ^ 13 * A - 576 * X ^ 12 * A ^ 6 + 192 * X ^ 12 * A ^ 4 * (d⁄dX ℚ A) - 2064 * X ^ 12 * A ^ 4 + 48 * X ^ 12 * A ^ 2 * (d⁄dX ℚ A) ^ 2 - 720 * X ^ 12 * A ^ 2 + 272 * X ^ 11 * A ^ 5 - 32 * X ^ 11 * A ^ 3 * (d⁄dX ℚ A) + 240 * X ^ 11 * A ^ 3 - 32 * X ^ 10 * A ^ 4) * hA1 + (13122 * X ^ 20 * A ^ 7 * (d⁄dX ℚ A) + 39366 * X ^ 20 * A ^ 5 * (d⁄dX ℚ A) + 39366 * X ^ 20 * A ^ 3 * (d⁄dX ℚ A) + 13122 * X ^ 20 * A * (d⁄dX ℚ A) - 10935 * X ^ 19 * A ^ 8 - 30618 * X ^ 19 * A ^ 6 * (d⁄dX ℚ A) - 43740 * X ^ 19 * A ^ 6 - 65610 * X ^ 19 * A ^ 4 * (d⁄dX ℚ A) - 65610 * X ^ 19 * A ^ 4 - 39366 * X ^ 19 * A ^ 2 * (d⁄dX ℚ A) - 43740 * X ^ 19 * A ^ 2 - 4374 * X ^ 19 * (d⁄dX ℚ A) - 10935 * X ^ 19 + 8748 * X ^ 18 * A ^ 7 * (d⁄dX ℚ A) + 33534 * X ^ 18 * A ^ 7 + 52488 * X ^ 18 * A ^ 5 * (d⁄dX ℚ A) + 100602 * X ^ 18 * A ^ 5 + 61236 * X ^ 18 * A ^ 3 * (d⁄dX ℚ A) + 100602 * X ^ 18 * A ^ 3 + 17496 * X ^ 18 * A * (d⁄dX ℚ A) + 33534 * X ^ 18 * A - 2916 * X ^ 17 * A ^ 8 - 20412 * X ^ 17 * A ^ 6 * (d⁄dX ℚ A) - 49572 * X ^ 17 * A ^ 6 - 53460 * X ^ 17 * A ^ 4 * (d⁄dX ℚ A) - 93312 * X ^ 17 * A ^ 4 - 32076 * X ^ 17 * A ^ 2 * (d⁄dX ℚ A) - 49572 * X ^ 17 * A ^ 2 - 2916 * X ^ 17 * (d⁄dX ℚ A) - 2916 * X ^ 17 - 486 * X ^ 16 * A ^ 7 * (d⁄dX ℚ A) + 10692 * X ^ 16 * A ^ 7 + 16038 * X ^ 16 * A ^ 5 * (d⁄dX ℚ A) + 50868 * X ^ 16 * A ^ 5 + 23166 * X ^ 16 * A ^ 3 * (d⁄dX ℚ A) + 50868 * X ^ 16 * A ^ 3 + 5346 * X ^ 16 * A * (d⁄dX ℚ A) + 10692 * X ^ 16 * A - 81 * X ^ 15 * A ^ 8 + 1134 * X ^ 15 * A ^ 6 * (d⁄dX ℚ A) - 13932 * X ^ 15 * A ^ 6 - 4050 * X ^ 15 * A ^ 4 * (d⁄dX ℚ A) - 31158 * X ^ 15 * A ^ 4 - 2430 * X ^ 15 * A ^ 2 * (d⁄dX ℚ A) - 13932 * X ^ 15 * A ^ 2 + 162 * X ^ 15 * (d⁄dX ℚ A) - 81 * X ^ 15 + 54 * X ^ 14 * A ^ 7 - 972 * X ^ 14 * A ^ 5 * (d⁄dX ℚ A) + 7506 * X ^ 14 * A ^ 5 - 432 * X ^ 14 * A ^ 3 * (d⁄dX ℚ A) + 7506 * X ^ 14 * A ^ 3 - 324 * X ^ 14 * A * (d⁄dX ℚ A) + 54 * X ^ 14 * A + 108 * X ^ 13 * A ^ 6 + 360 * X ^ 13 * A ^ 4 * (d⁄dX ℚ A) - 1224 * X ^ 13 * A ^ 4 + 216 * X ^ 13 * A ^ 2 * (d⁄dX ℚ A) + 108 * X ^ 13 * A ^ 2 - 120 * X ^ 12 * A ^ 5 - 48 * X ^ 12 * A ^ 3 * (d⁄dX ℚ A) - 120 * X ^ 12 * A ^ 3 + 32 * X ^ 11 * A ^ 4) * hA2 + (-2187 * X ^ 20 * A ^ 8 - 8748 * X ^ 20 * A ^ 6 - 13122 * X ^ 20 * A ^ 4 - 8748 * X ^ 20 * A ^ 2 - 2187 * X ^ 20 + 5832 * X ^ 19 * A ^ 7 + 17496 * X ^ 19 * A ^ 5 + 17496 * X ^ 19 * A ^ 3 + 5832 * X ^ 19 * A - 1458 * X ^ 18 * A ^ 8 - 11664 * X ^ 18 * A ^ 6 - 20412 * X ^ 18 * A ^ 4 - 11664 * X ^ 18 * A ^ 2 - 1458 * X ^ 18 + 3888 * X ^ 17 * A ^ 7 + 14256 * X ^ 17 * A ^ 5 + 14256 * X ^ 17 * A ^ 3 + 3888 * X ^ 17 * A + 81 * X ^ 16 * A ^ 8 - 3564 * X ^ 16 * A ^ 6 - 7722 * X ^ 16 * A ^ 4 - 3564 * X ^ 16 * A ^ 2 + 81 * X ^ 16 - 216 * X ^ 15 * A ^ 7 + 1080 * X ^ 15 * A ^ 5 + 1080 * X ^ 15 * A ^ 3 - 216 * X ^ 15 * A + 216 * X ^ 14 * A ^ 6 + 144 * X ^ 14 * A ^ 4 + 216 * X ^ 14 * A ^ 2 - 96 * X ^ 13 * A ^ 5 - 96 * X ^ 13 * A ^ 3 + 16 * X ^ 12 * A ^ 4) * hA3
  have hf0 : (X ^ 0 * (-3 * X * A ^ 2 - 3 * X + 2 * A) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C, hA0] <;> norm_num)
  have hf1 : (X ^ 1 * (-1) : PowerSeries ℚ) ≠ 0 := by simp [PowerSeries.X_ne_zero]
  have hE := (mul_eq_zero.mp key).resolve_left (mul_ne_zero (pow_ne_zero _ hf0) (pow_ne_zero _ hf1))
  have th2 : X * d⁄dX ℚ (X * d⁄dX ℚ A) = 1 * X ^ 1 * (d⁄dX ℚ A) + 1 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ A)) := by
    simp only [Derivation.leibniz, derivative_X, smul_eq_mul, map_add, map_mul, nC, derivative_C]
    try simp only [map_ofNat]
    ring
  have th3 : X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ A)) = 1 * X ^ 1 * (d⁄dX ℚ A) + 3 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ A)) + 1 * X ^ 3 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ A))) := by
    simp only [Derivation.leibniz, derivative_X, smul_eq_mul, th2, Derivation.map_one_eq_zero, map_add, map_mul, nC, derivative_C]
    try simp only [map_ofNat]
    ring
  rw [th3, th2]
  linear_combination hE

end Aq

namespace Tq

set_option maxHeartbeats 4000000 in
theorem ode (T : PowerSeries ℚ) (hT : T * (1 - 4 * T) ^ 2 = X * (1 - 3 * T)) (hT0 : constantCoeff T = 0) :
    (6 * X) * (T) + (-81 * X ^ 2 - 12 * X - 3) * (X * d⁄dX ℚ T) + (108 * X ^ 2 - 36 * X + 8) * (X * d⁄dX ℚ (X * d⁄dX ℚ T)) + (108 * X ^ 2 + 72 * X - 4) * (X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ T))) = X := by
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
  have key : (X ^ 0 * (3 * X + 48 * T ^ 2 - 16 * T + 1)) ^ 5 * (X ^ 0 * (16)) ^ 9 * (108 * X ^ 5 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ T))) + 432 * X ^ 4 * (d⁄dX ℚ (d⁄dX ℚ T)) + 72 * X ^ 4 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ T))) + 135 * X ^ 3 * (d⁄dX ℚ T) + 180 * X ^ 3 * (d⁄dX ℚ (d⁄dX ℚ T)) - 4 * X ^ 3 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ T))) + 24 * X ^ 2 * (d⁄dX ℚ T) - 4 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ T)) + 6 * X * T + X * (d⁄dX ℚ T) - X) = 0 := by
    linear_combination (450868486864896 * X ^ 6 + 180347394745958400 * X ^ 5 * T ^ 2 - 82959801583140864 * X ^ 5 * T + 8366115256270848 * X ^ 5 - 577111663187066880 * X ^ 4 * T ^ 4 + 807956328461893632 * X ^ 4 * T ^ 3 - 251684808667693056 * X ^ 4 * T ^ 2 + 9618527719784448 * X ^ 4 * T + 2460294706102272 * X ^ 4 - 9233786610993070080 * X ^ 3 * T ^ 6 + 10772751046158581760 * X ^ 3 * T ^ 5 - 5065757932419809280 * X ^ 3 * T ^ 4 + 1449191509780856832 * X ^ 3 * T ^ 3 - 313492755311493120 * X ^ 3 * T ^ 2 + 45034896762077184 * X ^ 3 * T - 2811588671176704 * X ^ 3 - 820781032088272896 * X ^ 2 * T ^ 6 + 1299569967473098752 * X ^ 2 * T ^ 5 - 756657513956376576 * X ^ 2 * T ^ 4 + 214220049462853632 * X ^ 2 * T ^ 3 - 31091989810249728 * X ^ 2 * T ^ 2 + 2177033022996480 * X ^ 2 * T - 57930518888448 * X ^ 2 + 6566248256706183168 * X * T ^ 8 - 8754997675608244224 * X * T ^ 7 + 4947485665643200512 * X * T ^ 6 - 1538964435165511680 * X * T ^ 5 + 286735040337936384 * X * T ^ 4 - 32668689484480512 * X * T ^ 3 + 2224312022990848 * X * T ^ 2 - 83013127897088 * X * T + 1305670057984 * X) * hT + (-19237055439568896 * X ^ 8 * (d⁄dX ℚ T) ^ 2 + 923378661099307008 * X ^ 7 * T ^ 2 * (d⁄dX ℚ T) ^ 2 - 307792887033102336 * X ^ 7 * T * (d⁄dX ℚ T) ^ 2 + 115422332637413376 * X ^ 7 * T * (d⁄dX ℚ T) + 19237055439568896 * X ^ 7 * (d⁄dX ℚ T) ^ 2 - 22443231346163712 * X ^ 7 * (d⁄dX ℚ T) - 450868486864896 * X ^ 7 + 44322175732766736384 * X ^ 6 * T ^ 4 * (d⁄dX ℚ T) ^ 2 - 29548117155177824256 * X ^ 6 * T ^ 3 * (d⁄dX ℚ T) ^ 2 + 615585774066204672 * X ^ 6 * T ^ 3 * (d⁄dX ℚ T) + 7797419804838592512 * X ^ 6 * T ^ 2 * (d⁄dX ℚ T) ^ 2 - 102597629011034112 * X ^ 6 * T ^ 2 * (d⁄dX ℚ T) - 182752026675904512 * X ^ 6 * T ^ 2 - 957577870769651712 * X ^ 6 * T * (d⁄dX ℚ T) ^ 2 + 61986067527499776 * X ^ 6 * T * (d⁄dX ℚ T) + 83360573571465216 * X ^ 6 * T + 49873847435919360 * X ^ 6 * (d⁄dX ℚ T) ^ 2 - 11755978324180992 * X ^ 6 * (d⁄dX ℚ T) - 8349416423424000 * X ^ 6 + 393974895402370990080 * X ^ 5 * T ^ 6 * (d⁄dX ℚ T) ^ 2 - 393974895402370990080 * X ^ 5 * T ^ 5 * (d⁄dX ℚ T) ^ 2 - 39397489540237099008 * X ^ 5 * T ^ 5 * (d⁄dX ℚ T) + 188779637380302766080 * X ^ 5 * T ^ 4 * (d⁄dX ℚ T) ^ 2 + 36935146443972280320 * X ^ 5 * T ^ 4 * (d⁄dX ℚ T) - 384741108791377920 * X ^ 5 * T ^ 4 - 52894777623466475520 * X ^ 5 * T ^ 3 * (d⁄dX ℚ T) ^ 2 - 12003922594290991104 * X ^ 5 * T ^ 3 * (d⁄dX ℚ T) - 205195258022068224 * X ^ 5 * T ^ 3 + 8504203471359049728 * X ^ 5 * T ^ 2 * (d⁄dX ℚ T) ^ 2 + 1784058771136315392 * X ^ 5 * T ^ 2 * (d⁄dX ℚ T) + 129315761565990912 * X ^ 5 * T ^ 2 - 706783666520457216 * X ^ 5 * T * (d⁄dX ℚ T) ^ 2 - 151046509377355776 * X ^ 5 * T * (d⁄dX ℚ T) - 1781208836997120 * X ^ 5 * T + 22324484090363904 * X ^ 5 * (d⁄dX ℚ T) ^ 2 + 8312307905986560 * X ^ 5 * (d⁄dX ℚ T) - 2432463318024192 * X ^ 5 - 315179916321896792064 * X ^ 4 * T ^ 7 * (d⁄dX ℚ T) + 262649930268247326720 * X ^ 4 * T ^ 6 * (d⁄dX ℚ T) ^ 2 + 367709902375546257408 * X ^ 4 * T ^ 6 * (d⁄dX ℚ T) + 12311715481324093440 * X ^ 4 * T ^ 6 - 262649930268247326720 * X ^ 4 * T ^ 5 * (d⁄dX ℚ T) ^ 2 - 188779637380302766080 * X ^ 4 * T ^ 5 * (d⁄dX ℚ T) - 15594839609677185024 * X ^ 4 * T ^ 5 + 104512784752573415424 * X ^ 4 * T ^ 4 * (d⁄dX ℚ T) ^ 2 + 57910661708450365440 * X ^ 4 * T ^ 4 * (d⁄dX ℚ T) + 7233132845277904896 * X ^ 4 * T ^ 4 - 21036313859447586816 * X ^ 4 * T ^ 3 * (d⁄dX ℚ T) ^ 2 - 11851926106867236864 * X ^ 4 * T ^ 3 * (d⁄dX ℚ T) - 1789758639414706176 * X ^ 4 * T ^ 3 + 2234348365129187328 * X ^ 4 * T ^ 2 * (d⁄dX ℚ T) ^ 2 + 1586463337485434880 * X ^ 4 * T ^ 2 * (d⁄dX ℚ T) + 318955129078284288 * X ^ 4 * T ^ 2 - 116530640358211584 * X ^ 4 * T * (d⁄dX ℚ T) ^ 2 - 119855563520606208 * X ^ 4 * T * (d⁄dX ℚ T) - 43224001111130112 * X ^ 4 * T + 2295780278796288 * X ^ 4 * (d⁄dX ℚ T) ^ 2 + 3562417673994240 * X ^ 4 * (d⁄dX ℚ T) + 2830142929895424 * X ^ 4 + 49246861925296373760 * X ^ 3 * T ^ 8 - 131324965134123663360 * X ^ 3 * T ^ 7 * (d⁄dX ℚ T) - 65662482567061831680 * X ^ 3 * T ^ 7 - 14591662792680407040 * X ^ 3 * T ^ 6 * (d⁄dX ℚ T) ^ 2 + 153212459323144273920 * X ^ 3 * T ^ 6 * (d⁄dX ℚ T) + 39123895862874341376 * X ^ 3 * T ^ 6 + 14591662792680407040 * X ^ 3 * T ^ 5 * (d⁄dX ℚ T) ^ 2 - 74052688672853065728 * X ^ 3 * T ^ 5 * (d⁄dX ℚ T) - 14956454362497417216 * X ^ 3 * T ^ 5 - 5897463712041664512 * X ^ 3 * T ^ 4 * (d⁄dX ℚ T) ^ 2 + 18999560927969280000 * X ^ 3 * T ^ 4 * (d⁄dX ℚ T) + 4198902965081210880 * X ^ 3 * T ^ 4 + 1229482698272145408 * X ^ 3 * T ^ 3 * (d⁄dX ℚ T) ^ 2 - 2744803235393961984 * X ^ 3 * T ^ 3 * (d⁄dX ℚ T) - 823947625576267776 * X ^ 3 * T ^ 3 - 138907901006708736 * X ^ 3 * T ^ 2 * (d⁄dX ℚ T) ^ 2 + 216383888346316800 * X ^ 3 * T ^ 2 * (d⁄dX ℚ T) + 96660266221043712 * X ^ 3 * T ^ 2 + 8022036836253696 * X ^ 3 * T * (d⁄dX ℚ T) ^ 2 - 8074813394386944 * X ^ 3 * T * (d⁄dX ℚ T) - 5304044092391424 * X ^ 3 * T - 184717953466368 * X ^ 3 * (d⁄dX ℚ T) ^ 2 + 92358976733184 * X ^ 3 * (d⁄dX ℚ T) + 64115271794688 * X ^ 3 + 8754997675608244224 * X ^ 2 * T ^ 8 + 2918332558536081408 * X ^ 2 * T ^ 7 * (d⁄dX ℚ T) - 11673330234144325632 * X ^ 2 * T ^ 7 - 3404721318292094976 * X ^ 2 * T ^ 6 * (d⁄dX ℚ T) + 6657446149160435712 * X ^ 2 * T ^ 6 + 1641562064176545792 * X ^ 2 * T ^ 5 * (d⁄dX ℚ T) - 2087418427286224896 * X ^ 2 * T ^ 5 - 422212465065984000 * X ^ 2 * T ^ 4 * (d⁄dX ℚ T) + 383580024512446464 * X ^ 2 * T ^ 4 + 62346707341410304 * X ^ 2 * T ^ 3 * (d⁄dX ℚ T) - 40532396646334464 * X ^ 2 * T ^ 3 - 5277655813324800 * X ^ 2 * T ^ 2 * (d⁄dX ℚ T) + 2212217395085312 * X ^ 2 * T ^ 2 + 237494511599616 * X ^ 2 * T * (d⁄dX ℚ T) - 43980465111040 * X ^ 2 * T - 4398046511104 * X ^ 2 * (d⁄dX ℚ T) - 274877906944 * X ^ 2 + 364791569817010176 * X * T ^ 8 - 486388759756013568 * X * T ^ 7 + 273593677362757632 * X * T ^ 6 - 84442493013196800 * X * T ^ 5 + 15586676835352576 * X * T ^ 4 - 1759218604441600 * X * T ^ 3 + 118747255799808 * X * T ^ 2 - 4398046511104 * X * T + 68719476736 * X) * hT1 + (-57711166318706688 * X ^ 8 * T * (d⁄dX ℚ T) + 9618527719784448 * X ^ 8 * (d⁄dX ℚ T) + 601157982486528 * X ^ 8 - 2770135983297921024 * X ^ 7 * T ^ 3 * (d⁄dX ℚ T) + 1385067991648960512 * X ^ 7 * T ^ 2 * (d⁄dX ℚ T) + 67329694038491136 * X ^ 7 * T ^ 2 - 250081720714395648 * X ^ 7 * T * (d⁄dX ℚ T) - 22443231346163712 * X ^ 7 * T + 16030879532974080 * X ^ 7 * (d⁄dX ℚ T) + 1202315964973056 * X ^ 7 - 44322175732766736384 * X ^ 6 * T ^ 5 * (d⁄dX ℚ T) + 36935146443972280320 * X ^ 6 * T ^ 4 * (d⁄dX ℚ T) + 2308446652748267520 * X ^ 6 * T ^ 4 - 13542887029456502784 * X ^ 6 * T ^ 3 * (d⁄dX ℚ T) - 1538964435165511680 * X ^ 6 * T ^ 3 + 2667538354286886912 * X ^ 6 * T ^ 2 * (d⁄dX ℚ T) + 359091701538619392 * X ^ 6 * T ^ 2 - 260768973736378368 * X ^ 6 * T * (d⁄dX ℚ T) - 34199209670344704 * X ^ 6 * T + 9262285952385024 * X ^ 6 * (d⁄dX ℚ T) + 1180050854510592 * X ^ 6 - 236384937241422594048 * X ^ 5 * T ^ 7 * (d⁄dX ℚ T) + 275782426781659693056 * X ^ 5 * T ^ 6 * (d⁄dX ℚ T) + 32010460251442642944 * X ^ 5 * T ^ 6 - 162514644353478033408 * X ^ 5 * T ^ 5 * (d⁄dX ℚ T) - 32010460251442642944 * X ^ 5 * T ^ 5 + 58822640632992890880 * X ^ 5 * T ^ 4 * (d⁄dX ℚ T) + 13286392956928917504 * X ^ 5 * T ^ 4 - 12744905470481793024 * X ^ 5 * T ^ 3 * (d⁄dX ℚ T) - 2929732295092862976 * X ^ 5 * T ^ 3 + 1538964435165511680 * X ^ 5 * T ^ 2 * (d⁄dX ℚ T) + 359804185073418240 * X ^ 5 * T ^ 2 - 92622859523850240 * X ^ 5 * T * (d⁄dX ℚ T) - 23036967625162752 * X ^ 5 * T + 2137450604396544 * X ^ 5 * (d⁄dX ℚ T) + 593736278999040 * X ^ 5 + 157589958160948396032 * X ^ 4 * T ^ 8 - 157589958160948396032 * X ^ 4 * T ^ 7 * (d⁄dX ℚ T) - 210119944214597861376 * X ^ 4 * T ^ 7 + 183854951187773128704 * X ^ 4 * T ^ 6 * (d⁄dX ℚ T) + 129683403069947117568 * X ^ 4 * T ^ 6 - 87002789401356926976 * X ^ 4 * T ^ 5 * (d⁄dX ℚ T) - 47970091430936838144 * X ^ 4 * T ^ 5 + 21431504726749347840 * X ^ 4 * T ^ 4 * (d⁄dX ℚ T) + 11299038883863330816 * X ^ 4 * T ^ 4 - 2933532207278456832 * X ^ 4 * T ^ 3 * (d⁄dX ℚ T) - 1675761273846890496 * X ^ 4 * T ^ 3 + 220394906764443648 * X ^ 4 * T ^ 2 * (d⁄dX ℚ T) + 148671564261359616 * X ^ 4 * T ^ 2 - 8312307905986560 * X ^ 4 * T * (d⁄dX ℚ T) - 7124835347988480 * X ^ 4 * T + 118747255799808 * X ^ 4 * (d⁄dX ℚ T) + 141012366262272 * X ^ 4 + 65662482567061831680 * X ^ 3 * T ^ 8 + 8754997675608244224 * X ^ 3 * T ^ 7 * (d⁄dX ℚ T) - 87549976756082442240 * X ^ 3 * T ^ 7 - 10214163954876284928 * X ^ 3 * T ^ 6 * (d⁄dX ℚ T) + 49155664032842121216 * X ^ 3 * T ^ 6 + 4924686192529637376 * X ^ 3 * T ^ 5 * (d⁄dX ℚ T) - 15108450849921171456 * X ^ 3 * T ^ 5 - 1266637395197952000 * X ^ 3 * T ^ 4 * (d⁄dX ℚ T) + 2769502664600322048 * X ^ 3 * T ^ 4 + 187040122024230912 * X ^ 3 * T ^ 3 * (d⁄dX ℚ T) - 309481736893366272 * X ^ 3 * T ^ 3 - 15832967439974400 * X ^ 3 * T ^ 2 * (d⁄dX ℚ T) + 20622440090566656 * X ^ 3 * T ^ 2 + 712483534798848 * X ^ 3 * T * (d⁄dX ℚ T) - 752065953398784 * X ^ 3 * T - 13194139533312 * X ^ 3 * (d⁄dX ℚ T) + 11544872091648 * X ^ 3 - 1459166279268040704 * X ^ 2 * T ^ 8 + 1945555039024054272 * X ^ 2 * T ^ 7 - 1094374709451030528 * X ^ 2 * T ^ 6 + 337769972052787200 * X ^ 2 * T ^ 5 - 62346707341410304 * X ^ 2 * T ^ 4 + 7036874417766400 * X ^ 2 * T ^ 3 - 474989023199232 * X ^ 2 * T ^ 2 + 17592186044416 * X ^ 2 * T - 274877906944 * X ^ 2) * hT2 + (601157982486528 * X ^ 9 + 38474110879137792 * X ^ 8 * T ^ 2 - 12824703626379264 * X ^ 8 * T + 1202315964973056 * X ^ 8 + 923378661099307008 * X ^ 7 * T ^ 4 - 615585774066204672 * X ^ 7 * T ^ 3 + 166721147142930432 * X ^ 7 * T ^ 2 - 21374506043965440 * X ^ 7 * T + 912869528961024 * X ^ 7 + 9849372385059274752 * X ^ 6 * T ^ 6 - 9849372385059274752 * X ^ 6 * T ^ 5 + 4514295676485500928 * X ^ 6 * T ^ 4 - 1185572601905283072 * X ^ 6 * T ^ 3 + 173845982490918912 * X ^ 6 * T ^ 2 - 12349714603180032 * X ^ 6 * T + 326554953449472 * X ^ 6 + 39397489540237099008 * X ^ 5 * T ^ 8 - 52529986053649465344 * X ^ 5 * T ^ 7 + 36114365411884007424 * X ^ 5 * T ^ 6 - 15686037502131437568 * X ^ 5 * T ^ 5 + 4248301823493931008 * X ^ 5 * T ^ 4 - 683984193406894080 * X ^ 5 * T ^ 3 + 61748573015900160 * X ^ 5 * T ^ 2 - 2849934139195392 * X ^ 5 * T + 51951924412416 * X ^ 5 + 26264993026824732672 * X ^ 4 * T ^ 8 - 35019990702432976896 * X ^ 4 * T ^ 7 + 19333953200301539328 * X ^ 4 * T ^ 6 - 5715067927133159424 * X ^ 4 * T ^ 5 + 977844069092818944 * X ^ 4 * T ^ 4 - 97953291895308288 * X ^ 4 * T ^ 3 + 5541538603991040 * X ^ 4 * T ^ 2 - 158329674399744 * X ^ 4 * T + 1649267441664 * X ^ 4 - 1459166279268040704 * X ^ 3 * T ^ 8 + 1945555039024054272 * X ^ 3 * T ^ 7 - 1094374709451030528 * X ^ 3 * T ^ 6 + 337769972052787200 * X ^ 3 * T ^ 5 - 62346707341410304 * X ^ 3 * T ^ 4 + 7036874417766400 * X ^ 3 * T ^ 3 - 474989023199232 * X ^ 3 * T ^ 2 + 17592186044416 * X ^ 3 * T - 274877906944 * X ^ 3) * hT3
  have hf0 : (X ^ 0 * (3 * X + 48 * T ^ 2 - 16 * T + 1) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C, hT0] <;> norm_num)
  have hf1 : (X ^ 0 * (16) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C, hT0] <;> norm_num)
  have hE := (mul_eq_zero.mp key).resolve_left (mul_ne_zero (pow_ne_zero _ hf0) (pow_ne_zero _ hf1))
  have th2 : X * d⁄dX ℚ (X * d⁄dX ℚ T) = 1 * X ^ 1 * (d⁄dX ℚ T) + 1 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ T)) := by
    simp only [Derivation.leibniz, derivative_X, smul_eq_mul, map_add, map_mul, nC, derivative_C]
    try simp only [map_ofNat]
    ring
  have th3 : X * d⁄dX ℚ (X * d⁄dX ℚ (X * d⁄dX ℚ T)) = 1 * X ^ 1 * (d⁄dX ℚ T) + 3 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ T)) + 1 * X ^ 3 * (d⁄dX ℚ (d⁄dX ℚ (d⁄dX ℚ T))) := by
    simp only [Derivation.leibniz, derivative_X, smul_eq_mul, th2, Derivation.map_one_eq_zero, map_add, map_mul, nC, derivative_C]
    try simp only [map_ofNat]
    ring
  rw [th3, th2]
  linear_combination hE

end Tq

theorem recA (A : PowerSeries ℚ) (hA : A ^ 2 * (1 - X * A) = 1 - X * A + 4 * X * A) (hA0 : constantCoeff A = 1) :
    ∀ n : ℕ, 4 ≤ n → (2 * (n : ℚ) + (n : ℚ) ^ 2 - (n : ℚ) ^ 3) * coeff n A + (-12 + 78 * (n : ℚ) - 72 * (n : ℚ) ^ 2 + 18 * (n : ℚ) ^ 3) * coeff (n - 2) A + (324 * (n : ℚ) - 189 * (n : ℚ) ^ 2 + 27 * (n : ℚ) ^ 3) * coeff (n - 4) A = 0 := by
  intro n hn
  have e := congrArg (coeff n) (Aq.ode A hA hA0)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  norm_num only at e ⊢
  simp only [nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e

theorem recT (T : PowerSeries ℚ) (hT : T * (1 - 4 * T) ^ 2 = X * (1 - 3 * T)) (hT0 : constantCoeff T = 0) :
    ∀ n : ℕ, 2 ≤ n → (-3 * (n : ℚ) + 8 * (n : ℚ) ^ 2 - 4 * (n : ℚ) ^ 3) * coeff n T + (-90 + 276 * (n : ℚ) - 252 * (n : ℚ) ^ 2 + 72 * (n : ℚ) ^ 3) * coeff (n - 1) T + (-270 + 783 * (n : ℚ) - 540 * (n : ℚ) ^ 2 + 108 * (n : ℚ) ^ 3) * coeff (n - 2) T = 0 := by
  intro n hn
  have e := congrArg (coeff n) (Tq.ode T hT hT0)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp only [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  norm_num only at e ⊢
  simp only [nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e

theorem small (A T : PowerSeries ℚ) (hA0 : constantCoeff A = 1) (hA : A ^ 2 * (1 - X * A) = 1 - X * A + 4 * X * A)
    (hT0 : constantCoeff T = 0) (hT : T * (1 - 4 * T) ^ 2 = X * (1 - 3 * T)) :
    coeff 1 A = 2 * coeff 1 T ∧ coeff 3 A = 2 * coeff 2 T := by
  have hA' : A * A - X * (A * (A * A)) = 1 + X * (C (3 : ℚ) * A) := by
    rw [show (C (3 : ℚ)) = 3 from map_ofNat C 3]; linear_combination hA
  obtain ⟨U, rfl⟩ : X ∣ T := by rw [PowerSeries.X_dvd_iff]; exact hT0
  have hU : U * (1 - 4 * X * U) ^ 2 = 1 - 3 * X * U := by
    have : X * (U * (1 - 4 * X * U) ^ 2 - (1 - 3 * X * U)) = 0 := by linear_combination hT
    linear_combination (mul_eq_zero.mp this).resolve_left PowerSeries.X_ne_zero
  have hU' : U - X * (C (8 : ℚ) * (U * U) - C (16 : ℚ) * (X * (U * (U * U)))) = 1 - X * (C (3 : ℚ) * U) := by
    rw [show (C (3 : ℚ)) = 3 from map_ofNat C 3, show (C (8 : ℚ)) = 8 from map_ofNat C 8,
      show (C (16 : ℚ)) = 16 from map_ofNat C 16]
    linear_combination hU
  have a1 := congrArg (coeff 1) hA'
  have a2 := congrArg (coeff 2) hA'
  have a3 := congrArg (coeff 3) hA'
  have u0 := congrArg (coeff 0) hU'
  have u1 := congrArg (coeff 1) hU'
  simp only [map_sub, map_add, coeff_one, coeff_succ_X_mul, coeff_zero_X_mul, coeff_C_mul] at a1 a2 a3 u0 u1
  simp only [coeff_mul, Finset.Nat.antidiagonal_succ, Finset.Nat.antidiagonal_zero, Finset.sum_cons,
    Finset.sum_singleton, Finset.map_cons, Finset.map_singleton] at a1 a2 a3 u0 u1
  simp [coeff_zero_eq_constantCoeff_apply, hA0, Finset.Nat.sum_antidiagonal_succ] at a1 a2 a3 u0 u1
  have t1 : coeff 1 (X * U) = constantCoeff U := by
    rw [show (1 : ℕ) = 0 + 1 from rfl, coeff_succ_X_mul, coeff_zero_eq_constantCoeff_apply]
  have t2 : coeff 2 (X * U) = coeff 1 U := by
    rw [show (2 : ℕ) = 1 + 1 from rfl, coeff_succ_X_mul]
  rw [t1, t2]
  rw [u0] at u1
  have ha1 : coeff 1 A = 2 := by linarith
  rw [ha1] at a2 a3
  have ha2 : coeff 2 A = 4 := by linarith
  rw [ha2] at a3
  constructor
  · rw [ha1, u0]; norm_num
  · linarith

end P372018

theorem OMA.solution : type_of% @OMA.S_oeis_a372018.main := by
  intro A T hA0 hA hT0 hT
  rw [coeff_zero_eq_constantCoeff_apply] at hA0 hT0
  have key : ∀ k : ℕ, coeff (2 * k + 1) A = 2 * coeff (k + 1) T ∧ coeff (2 * k + 3) A = 2 * coeff (k + 2) T := by
    intro k
    induction k with
    | zero => simpa using P372018.small A T hA0 hA hT0 hT
    | succ k ih =>
      refine ⟨by rw [show 2 * (k + 1) + 1 = 2 * k + 3 by ring]; exact ih.2, ?_⟩
      have eA := P372018.recA A hA hA0 (2 * k + 5) (by omega)
      have eT := P372018.recT T hT hT0 (k + 3) (by omega)
      simp only [show 2 * k + 5 - 2 = 2 * k + 3 by omega, show 2 * k + 5 - 4 = 2 * k + 1 by omega] at eA
      simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega] at eT
      rw [show 2 * (k + 1) + 3 = 2 * k + 5 by ring, show k + 1 + 2 = k + 3 by ring]
      push_cast at eA eT
      have hL : -((2 * (2 * (k : ℚ) + 5) + (2 * (k : ℚ) + 5) ^ 2 - (2 * (k : ℚ) + 5) ^ 3)) ≠ 0 := by
        have : -((2 * (2 * (k : ℚ) + 5) + (2 * (k : ℚ) + 5) ^ 2 - (2 * (k : ℚ) + 5) ^ 3)) = (2 * (k : ℚ) + 5) * (2 * (k : ℚ) + 6) * (2 * (k : ℚ) + 3) := by ring
        rw [this]; positivity
      have h2 : -((2 * (2 * (k : ℚ) + 5) + (2 * (k : ℚ) + 5) ^ 2 - (2 * (k : ℚ) + 5) ^ 3)) * (coeff (2 * k + 5) A - 2 * coeff (k + 3) T) = 0 := by
        linear_combination -eA + 4 * eT + (-12 + 78 * (2 * (k : ℚ) + 5) - 72 * (2 * (k : ℚ) + 5) ^ 2 + 18 * (2 * (k : ℚ) + 5) ^ 3) * ih.2 + (324 * (2 * (k : ℚ) + 5) - 189 * (2 * (k : ℚ) + 5) ^ 2 + 27 * (2 * (k : ℚ) + 5) ^ 3) * ih.1
      have := (mul_eq_zero.mp h2).resolve_left hL
      linear_combination this
  intro n
  exact (key n).1
