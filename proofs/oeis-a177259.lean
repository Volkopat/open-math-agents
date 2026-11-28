import OMAStatements.S_oeis_a177259
import Mathlib

open OMA.S_oeis_a177259
open PowerSeries

namespace P177259

theorem nC (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem cXd (F : PowerSeries ℚ) (k : ℕ) : coeff k (X * d⁄dX ℚ F) = coeff k F * k := by
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

theorem ne_of_cc (p : PowerSeries ℚ) (h : constantCoeff p ≠ 0) : p ≠ 0 := by
  intro h0; rw [h0, map_zero] at h; exact h rfl

set_option maxHeartbeats 4000000 in
theorem ode (G H Y : PowerSeries ℚ) (hG : G * (1 + X + X ^ 3) = H) (hH : Y ^ 2 * d⁄dX ℚ H + (Y - 1) * d⁄dX ℚ Y * H + d⁄dX ℚ Y = 0) (hY : Y * (1 + X + X ^ 3) = X) (hYne : Y ≠ 0) :
    (-2 * X ^ 6 - 3 * X ^ 4 - X ^ 3 - X ^ 2 + 1) * (G) + (-X ^ 4 - X ^ 2 - X) * (X * d⁄dX ℚ G) = -2 * X ^ 3 + 1 := by
  have hG1 := congrArg (d⁄dX ℚ) hG
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hG1
  try simp only [map_ofNat] at hG1
  try push_cast at hG1
  have hH1 := congrArg (d⁄dX ℚ) hH
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hH1
  try simp only [map_ofNat] at hH1
  try push_cast at hH1
  have hY1 := congrArg (d⁄dX ℚ) hY
  simp only [nC, Derivation.leibniz, Derivation.leibniz_pow, derivative_X, derivative_C, smul_eq_mul,
    nsmul_eq_mul, map_add, map_sub, map_neg, Derivation.map_one_eq_zero, mul_one, mul_zero, add_zero,
    zero_add, sub_zero, neg_zero, map_zero] at hY1
  try simp only [map_ofNat] at hY1
  try push_cast at hY1
  have key : (X ^ 0 * (X ^ 3 + X + 1)) ^ 5 * (X ^ 0 * (Y ^ 2)) ^ 1 * (-2 * X ^ 6 * G - X ^ 5 * (d⁄dX ℚ G) - 3 * X ^ 4 * G - X ^ 3 * G - X ^ 3 * (d⁄dX ℚ G) + 2 * X ^ 3 - X ^ 2 * G - X ^ 2 * (d⁄dX ℚ G) + G - 1) = 0 := by
    linear_combination (-2 * X ^ 15 * H * Y + 2 * X ^ 15 * Y - 9 * X ^ 13 * H * Y + X ^ 13 * H + 8 * X ^ 13 * Y - X ^ 13 - 7 * X ^ 12 * H * Y + 7 * X ^ 12 * Y - 16 * X ^ 11 * H * Y + 4 * X ^ 11 * H + 12 * X ^ 11 * Y - 4 * X ^ 11 - 24 * X ^ 10 * H * Y + 4 * X ^ 10 * H + 20 * X ^ 10 * Y - 4 * X ^ 10 - 22 * X ^ 9 * H * Y + 6 * X ^ 9 * H + 16 * X ^ 9 * Y - 6 * X ^ 9 - 30 * X ^ 8 * H * Y + 12 * X ^ 8 * H + 18 * X ^ 8 * Y - 12 * X ^ 8 - 24 * X ^ 7 * H * Y + 10 * X ^ 7 * H + 14 * X ^ 7 * Y - 10 * X ^ 7 - 18 * X ^ 6 * H * Y + 12 * X ^ 6 * H + 6 * X ^ 6 * Y - 12 * X ^ 6 - 13 * X ^ 5 * H * Y + 13 * X ^ 5 * H - 13 * X ^ 5 - 3 * X ^ 4 * H * Y + 8 * X ^ 4 * H - 5 * X ^ 4 * Y - 8 * X ^ 4 + 6 * X ^ 3 * H - 6 * X ^ 3 * Y - 6 * X ^ 3 + 2 * X ^ 2 * H * Y + 4 * X ^ 2 * H - 6 * X ^ 2 * Y - 4 * X ^ 2 + 3 * X * H * Y + X * H - 4 * X * Y - X + H * Y - Y) * hY + (-2 * X ^ 18 * Y ^ 2 - 8 * X ^ 16 * Y ^ 2 - 9 * X ^ 15 * Y ^ 2 - 12 * X ^ 14 * Y ^ 2 - 28 * X ^ 13 * Y ^ 2 - 23 * X ^ 12 * Y ^ 2 - 30 * X ^ 11 * Y ^ 2 - 34 * X ^ 10 * Y ^ 2 - 22 * X ^ 9 * Y ^ 2 - 18 * X ^ 8 * Y ^ 2 - 9 * X ^ 7 * Y ^ 2 + 6 * X ^ 5 * Y ^ 2 + 9 * X ^ 4 * Y ^ 2 + 7 * X ^ 3 * Y ^ 2 + 6 * X ^ 2 * Y ^ 2 + 4 * X * Y ^ 2 + Y ^ 2) * hG + (X ^ 14 * H * Y - X ^ 14 * H + X ^ 14 + 4 * X ^ 12 * H * Y - 4 * X ^ 12 * H + 4 * X ^ 12 + 4 * X ^ 11 * H * Y - 4 * X ^ 11 * H + 4 * X ^ 11 + 6 * X ^ 10 * H * Y - 6 * X ^ 10 * H + 6 * X ^ 10 + 12 * X ^ 9 * H * Y - 12 * X ^ 9 * H + 12 * X ^ 9 + 10 * X ^ 8 * H * Y - 10 * X ^ 8 * H + 10 * X ^ 8 + 12 * X ^ 7 * H * Y - 12 * X ^ 7 * H + 12 * X ^ 7 + 13 * X ^ 6 * H * Y - 13 * X ^ 6 * H + 13 * X ^ 6 + 8 * X ^ 5 * H * Y - 8 * X ^ 5 * H + 8 * X ^ 5 + 6 * X ^ 4 * H * Y - 6 * X ^ 4 * H + 6 * X ^ 4 + 4 * X ^ 3 * H * Y - 4 * X ^ 3 * H + 4 * X ^ 3 + X ^ 2 * H * Y - X ^ 2 * H + X ^ 2) * hY1 + (-X ^ 17 - 5 * X ^ 15 - 5 * X ^ 14 - 10 * X ^ 13 - 20 * X ^ 12 - 20 * X ^ 11 - 30 * X ^ 10 - 35 * X ^ 9 - 30 * X ^ 8 - 31 * X ^ 7 - 25 * X ^ 6 - 15 * X ^ 5 - 10 * X ^ 4 - 5 * X ^ 3 - X ^ 2) * hH + (-X ^ 17 * Y ^ 2 - 5 * X ^ 15 * Y ^ 2 - 5 * X ^ 14 * Y ^ 2 - 10 * X ^ 13 * Y ^ 2 - 20 * X ^ 12 * Y ^ 2 - 20 * X ^ 11 * Y ^ 2 - 30 * X ^ 10 * Y ^ 2 - 35 * X ^ 9 * Y ^ 2 - 30 * X ^ 8 * Y ^ 2 - 31 * X ^ 7 * Y ^ 2 - 25 * X ^ 6 * Y ^ 2 - 15 * X ^ 5 * Y ^ 2 - 10 * X ^ 4 * Y ^ 2 - 5 * X ^ 3 * Y ^ 2 - X ^ 2 * Y ^ 2) * hG1
  have hf0 : (X ^ 0 * (X ^ 3 + X + 1) : PowerSeries ℚ) ≠ 0 := ne_of_cc _ (by simp [nC, constantCoeff_C] <;> norm_num)
  have hf1 : (X ^ 0 * (Y ^ 2) : PowerSeries ℚ) ≠ 0 := by simpa using pow_ne_zero 2 hYne
  have hE := (mul_eq_zero.mp key).resolve_left (mul_ne_zero (pow_ne_zero _ hf0) (pow_ne_zero _ hf1))
  linear_combination hE

theorem hf : X ^ 2 * d⁄dX ℚ (PowerSeries.mk fun k : ℕ => (k.factorial : ℚ)) +
    (X - 1) * (PowerSeries.mk fun k : ℕ => (k.factorial : ℚ)) + 1 = 0 := by
  ext n
  rcases n with _ | _ | n
  · simp
  · simp [sub_mul, coeff_X_pow_mul', coeff_one]
  · simp only [map_add, map_sub, sub_mul, one_mul, coeff_X_pow_mul', coeff_succ_X_mul, coeff_one,
      coeff_derivative, coeff_mk, map_zero]
    simp only [show n + 2 - 2 = n by omega, show 2 ≤ n + 2 by omega, if_true,
      show n + 1 + 1 ≠ 0 by omega, if_false, Nat.factorial_succ]
    push_cast; ring

end P177259

theorem OMA.solution : type_of% @OMA.S_oeis_a177259.main := by
  intro Y G hY hG n hn
  have hY0 : constantCoeff Y = 0 := by
    have h := congrArg constantCoeff hY
    simpa using h
  have hS : HasSubst Y := HasSubst.of_constantCoeff_zero' hY0
  have h1 := congrArg (substAlgHom hS) P177259.hf
  simp only [map_add, map_mul, map_sub, map_one, map_pow, map_zero, coe_substAlgHom, subst_X hS] at h1
  have hH : Y ^ 2 * d⁄dX ℚ ((PowerSeries.mk fun k : ℕ => (k.factorial : ℚ)).subst Y) +
      (Y - 1) * d⁄dX ℚ Y * (PowerSeries.mk fun k : ℕ => (k.factorial : ℚ)).subst Y + d⁄dX ℚ Y = 0 := by
    rw [derivative_subst hS]
    linear_combination (d⁄dX ℚ Y) * h1
  have hYne : Y ≠ 0 := by
    intro h; rw [h, zero_mul] at hY; exact PowerSeries.X_ne_zero hY.symm
  generalize (PowerSeries.mk fun k : ℕ => (k.factorial : ℚ)).subst Y = H at hG hH
  have e := congrArg (coeff n) (P177259.ode G H Y hG hH hY hYne)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  simp only [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega, show k + 6 - 3 = k + 3 by omega, show k + 6 - 4 = k + 2 by omega, show k + 6 - 5 = k + 1 by omega, show k + 6 - 6 = k by omega]
  norm_num only at e ⊢
  simp only [P177259.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, P177259.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X, coeff_one] at e
  simp at e
  push_cast at e ⊢
  linear_combination e
