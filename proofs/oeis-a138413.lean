import OMAStatements.S_oeis_a138413
import Mathlib

open OMA.S_oeis_a138413
open PowerSeries

namespace P138413

theorem nC (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem cXd (F : PowerSeries ℚ) (k : ℕ) : coeff k (X * d⁄dX ℚ F) = coeff k F * k := by
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

theorem ne_of_cc (p : PowerSeries ℚ) (h : constantCoeff p ≠ 0) : p ≠ 0 := by
  intro h0; rw [h0, map_zero] at h; exact h rfl

namespace Fq

set_option maxHeartbeats 4000000 in
theorem ode (F S : PowerSeries ℚ) (hF : F * (3 - S) = 1 - S) (hS : S ^ 2 = 1 - 4 * X) (hS0 : constantCoeff S = 1) :
    (5 * X) * (F) + (2 * X ^ 2 - 12 * X + 4) * (X * d⁄dX ℚ F) + (4 * X ^ 2 + 7 * X - 2) * (X * d⁄dX ℚ (X * d⁄dX ℚ F)) = 2 * X := by
  have hF1 := congrArg (d⁄dX ℚ) hF
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hF1
  try simp only [map_ofNat] at hF1
  try push_cast at hF1
  have hF2 := congrArg (d⁄dX ℚ) hF1
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hF2
  try simp only [map_ofNat] at hF2
  try push_cast at hF2
  have hS1 := congrArg (d⁄dX ℚ) hS
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hS1
  try simp only [map_ofNat] at hS1
  try push_cast at hS1
  have hS2 := congrArg (d⁄dX ℚ) hS1
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hS2
  try simp only [map_ofNat] at hS2
  try push_cast at hS2
  have key : (X ^ 0 * (-S + 3)) ^ 3 * (X ^ 0 * (2 * S)) ^ 3 * (X ^ 0 * (1)) ^ 5 * (4 * X ^ 4 * (d⁄dX ℚ (d⁄dX ℚ F)) + 6 * X ^ 3 * (d⁄dX ℚ F) + 7 * X ^ 3 * (d⁄dX ℚ (d⁄dX ℚ F)) - 5 * X ^ 2 * (d⁄dX ℚ F) - 2 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ F)) + 5 * X * F + 2 * X * (d⁄dX ℚ F) - 2 * X) = 0 := by
    linear_combination (-192 * X ^ 3 * S + 192 * X ^ 3 + 96 * X ^ 2 * S ^ 2 - 384 * X ^ 2 * S + 384 * X ^ 2 - 24 * X * S ^ 4 + 136 * X * S ^ 3 - 192 * X * S ^ 2) * hS + (384 * X ^ 4 * S - 384 * X ^ 4 + 96 * X ^ 3 * S ^ 3 - 288 * X ^ 3 * S ^ 2 + 672 * X ^ 3 * S - 672 * X ^ 3 - 80 * X ^ 2 * S ^ 3 + 240 * X ^ 2 * S ^ 2 - 192 * X ^ 2 * S + 192 * X ^ 2 + 40 * X * S ^ 5 - 240 * X * S ^ 4 + 392 * X * S ^ 3 - 96 * X * S ^ 2) * hF + (-48 * X ^ 4 * F * S ^ 3 * (d⁄dX ℚ S) + 192 * X ^ 4 * F * S ^ 2 * (d⁄dX ℚ S) + 96 * X ^ 4 * F * S ^ 2 - 144 * X ^ 4 * F * S * (d⁄dX ℚ S) - 384 * X ^ 4 * F * S + 288 * X ^ 4 * F + 48 * X ^ 4 * S ^ 3 * (d⁄dX ℚ S) - 192 * X ^ 4 * S ^ 2 * (d⁄dX ℚ S) - 96 * X ^ 4 * S ^ 2 + 144 * X ^ 4 * S * (d⁄dX ℚ S) + 384 * X ^ 4 * S - 288 * X ^ 4 + 24 * X ^ 3 * F * S ^ 4 - 84 * X ^ 3 * F * S ^ 3 * (d⁄dX ℚ S) - 144 * X ^ 3 * F * S ^ 3 + 336 * X ^ 3 * F * S ^ 2 * (d⁄dX ℚ S) + 384 * X ^ 3 * F * S ^ 2 - 252 * X ^ 3 * F * S * (d⁄dX ℚ S) - 672 * X ^ 3 * F * S + 504 * X ^ 3 * F - 24 * X ^ 3 * S ^ 4 + 84 * X ^ 3 * S ^ 3 * (d⁄dX ℚ S) + 144 * X ^ 3 * S ^ 3 - 336 * X ^ 3 * S ^ 2 * (d⁄dX ℚ S) - 384 * X ^ 3 * S ^ 2 + 252 * X ^ 3 * S * (d⁄dX ℚ S) + 672 * X ^ 3 * S - 504 * X ^ 3 - 20 * X ^ 2 * F * S ^ 4 + 24 * X ^ 2 * F * S ^ 3 * (d⁄dX ℚ S) + 120 * X ^ 2 * F * S ^ 3 - 96 * X ^ 2 * F * S ^ 2 * (d⁄dX ℚ S) - 228 * X ^ 2 * F * S ^ 2 + 72 * X ^ 2 * F * S * (d⁄dX ℚ S) + 192 * X ^ 2 * F * S - 144 * X ^ 2 * F + 20 * X ^ 2 * S ^ 4 - 24 * X ^ 2 * S ^ 3 * (d⁄dX ℚ S) - 120 * X ^ 2 * S ^ 3 + 96 * X ^ 2 * S ^ 2 * (d⁄dX ℚ S) + 228 * X ^ 2 * S ^ 2 - 72 * X ^ 2 * S * (d⁄dX ℚ S) - 192 * X ^ 2 * S + 144 * X ^ 2 + 8 * X * F * S ^ 4 - 48 * X * F * S ^ 3 + 72 * X * F * S ^ 2 - 8 * X * S ^ 4 + 48 * X * S ^ 3 - 72 * X * S ^ 2) * hS1 + (16 * X ^ 4 * F * S ^ 4 - 96 * X ^ 4 * F * S ^ 3 + 144 * X ^ 4 * F * S ^ 2 - 16 * X ^ 4 * S ^ 4 + 96 * X ^ 4 * S ^ 3 - 144 * X ^ 4 * S ^ 2 + 28 * X ^ 3 * F * S ^ 4 - 168 * X ^ 3 * F * S ^ 3 + 252 * X ^ 3 * F * S ^ 2 - 28 * X ^ 3 * S ^ 4 + 168 * X ^ 3 * S ^ 3 - 252 * X ^ 3 * S ^ 2 - 8 * X ^ 2 * F * S ^ 4 + 48 * X ^ 2 * F * S ^ 3 - 72 * X ^ 2 * F * S ^ 2 + 8 * X ^ 2 * S ^ 4 - 48 * X ^ 2 * S ^ 3 + 72 * X ^ 2 * S ^ 2) * hS2 + (-64 * X ^ 4 * S ^ 4 * (d⁄dX ℚ S) + 192 * X ^ 4 * S ^ 3 * (d⁄dX ℚ S) + 48 * X ^ 3 * S ^ 5 - 112 * X ^ 3 * S ^ 4 * (d⁄dX ℚ S) - 288 * X ^ 3 * S ^ 4 + 336 * X ^ 3 * S ^ 3 * (d⁄dX ℚ S) + 432 * X ^ 3 * S ^ 3 - 40 * X ^ 2 * S ^ 5 + 32 * X ^ 2 * S ^ 4 * (d⁄dX ℚ S) + 240 * X ^ 2 * S ^ 4 - 96 * X ^ 2 * S ^ 3 * (d⁄dX ℚ S) - 360 * X ^ 2 * S ^ 3 + 16 * X * S ^ 5 - 96 * X * S ^ 4 + 144 * X * S ^ 3) * hF1 + (32 * X ^ 4 * S ^ 5 - 192 * X ^ 4 * S ^ 4 + 288 * X ^ 4 * S ^ 3 + 56 * X ^ 3 * S ^ 5 - 336 * X ^ 3 * S ^ 4 + 504 * X ^ 3 * S ^ 3 - 16 * X ^ 2 * S ^ 5 + 96 * X ^ 2 * S ^ 4 - 144 * X ^ 2 * S ^ 3) * hF2
  have hf0 : (X ^ 0 * (-S + 3) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C, hS0] <;> norm_num)
  have hf1 : (X ^ 0 * (2 * S) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C, hS0] <;> norm_num)
  have hf2 : (X ^ 0 * (1) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C, hS0] <;> norm_num)
  have hE := (mul_eq_zero.mp key).resolve_left (mul_ne_zero (mul_ne_zero (pow_ne_zero _ hf0) (pow_ne_zero _ hf1)) (pow_ne_zero _ hf2))
  have th2 : X * d⁄dX ℚ (X * d⁄dX ℚ F) = 1 * X ^ 1 * (d⁄dX ℚ F) + 1 * X ^ 2 * (d⁄dX ℚ (d⁄dX ℚ F)) := by
    simp only [Derivation.leibniz, derivative_X, smul_eq_mul, map_add, map_mul, nC, derivative_C]
    try simp only [map_ofNat]
    ring
  rw [th2]
  linear_combination hE

end Fq

theorem recF (S F : PowerSeries ℚ) (hF : F * (3 - S) = 1 - S) (hS : S ^ 2 = 1 - 4 * X) (hS0 : constantCoeff S = 1) :
    ∀ n : ℕ, 2 ≤ n → (4 * (n : ℚ) - 2 * (n : ℚ) ^ 2) * coeff n F + (24 - 26 * (n : ℚ) + 7 * (n : ℚ) ^ 2) * coeff (n - 1) F + (12 - 14 * (n : ℚ) + 4 * (n : ℚ) ^ 2) * coeff (n - 2) F = 0 := by
  intro n hn
  have e := congrArg (coeff n) (Fq.ode F S hF hS hS0)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 2 := ⟨n - 2, by omega⟩
  simp only [show k + 2 - 1 = k + 1 by omega, show k + 2 - 2 = k by omega]
  norm_num only at e ⊢
  simp only [nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e

end P138413

theorem OMA.solution : type_of% @OMA.S_oeis_a138413.main := by
  intro S F hS hS0 hF n hn
  rw [coeff_zero_eq_constantCoeff_apply] at hS0
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show 2 * (k + 3) = 2 * k + 6 by ring, show 2 * (k + 2) = 2 * k + 4 by ring,
    show 2 * (k + 1) = 2 * k + 2 by ring]
  have h0 := P138413.recF S F hF hS hS0 (2 * k + 6) (by omega)
  simp only [show 2 * k + 6 - 1 = 2 * k + 5 by omega, show 2 * k + 6 - 2 = 2 * k + 4 by omega] at h0
  have h1 := P138413.recF S F hF hS hS0 (2 * k + 5) (by omega)
  simp only [show 2 * k + 5 - 1 = 2 * k + 4 by omega, show 2 * k + 5 - 2 = 2 * k + 3 by omega] at h1
  have h2 := P138413.recF S F hF hS hS0 (2 * k + 4) (by omega)
  simp only [show 2 * k + 4 - 1 = 2 * k + 3 by omega, show 2 * k + 4 - 2 = 2 * k + 2 by omega] at h2
  push_cast at h0 h1 h2 ⊢
  have key : (-12 + 26 * ((k : ℚ) + 3) - 18 * ((k : ℚ) + 3) ^ 2 + 4 * ((k : ℚ) + 3) ^ 3) * (4 * ((k : ℚ) + 3) * (2 * ((k : ℚ) + 3) - 1) * (7 * ((k : ℚ) + 3) - 13) * coeff (2 * k + 6) F +
        (-910 * ((k : ℚ) + 3) ^ 3 + 3489 * ((k : ℚ) + 3) ^ 2 - 4277 * ((k : ℚ) + 3) + 1680) * coeff (2 * k + 4) F +
        2 * (4 * ((k : ℚ) + 3) - 7) * (7 * ((k : ℚ) + 3) - 6) * (4 * ((k : ℚ) + 3) - 5) * coeff (2 * k + 2) F) = 0 := by
    linear_combination (-78 + 289 * ((k : ℚ) + 3) - 341 * ((k : ℚ) + 3) ^ 2 + 164 * ((k : ℚ) + 3) ^ 3 - 28 * ((k : ℚ) + 3) ^ 4) * h0 + (-312 + 1000 * ((k : ℚ) + 3) - 1150 * ((k : ℚ) + 3) ^ 2 + 560 * ((k : ℚ) + 3) ^ 3 - 98 * ((k : ℚ) + 3) ^ 4) * h1 + (90 - 327 * ((k : ℚ) + 3) + 439 * ((k : ℚ) + 3) ^ 2 - 258 * ((k : ℚ) + 3) ^ 3 + 56 * ((k : ℚ) + 3) ^ 4) * h2
  have hc : (-12 + 26 * ((k : ℚ) + 3) - 18 * ((k : ℚ) + 3) ^ 2 + 4 * ((k : ℚ) + 3) ^ 3) ≠ 0 := by
    have : (-12 + 26 * ((k : ℚ) + 3) - 18 * ((k : ℚ) + 3) ^ 2 + 4 * ((k : ℚ) + 3) ^ 3) = 2 * ((k : ℚ) + 2) * ((k : ℚ) + 1) * (2 * (k : ℚ) + 3) := by ring
    rw [this]; positivity
  have := (mul_eq_zero.mp key).resolve_left hc
  linear_combination this
