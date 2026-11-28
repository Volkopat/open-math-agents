import OMAStatements.S_oeis_a186341
import Mathlib

/-
A186341: the coefficients a(n) of A = (U + V S) / W, where S is the square root of
R = 1 - 4 * X - 4 * X ^ 2 + 26 * X ^ 3 - 4 * X ^ 4 - 40 * X ^ 5 + 9 * X ^ 6 + 16 * X ^ 7 with S(0) = 1, U = 1 - 2 * X - 2 * X ^ 2 + 3 * X ^ 3, V = -1, W = 2 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3,
satisfy the stated recurrence with polynomial coefficients.

- sqrt_sq: S^2 = R, because the binomial series with exponent 1/2 squares to 1 + X and
  substitution is a ring homomorphism.
- ode: differentiating S^2 = R and multiplying by S gives 2 R S' = R' S.
- odeA: with A W = U + V S this yields the first-order equation
  2 R V W A' + (2 R V W' - (2 R V' + V R') W) A = 2 R V U' - (2 R V' + V R') U.
- For the given polynomials this equation is written out, and comparing the coefficient of
  X^m on both sides gives the recurrence, up to a rational factor.
-/

namespace OMA.P186341

open PowerSeries

lemma sqrt_sq (R : PowerSeries ℚ) (hR : constantCoeff R = 1) :
    ((PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)) ^ 2 = R := by
  have ha : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [hR])
  have h1 : PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) ^ 2 = 1 + X := by
    have h := binomialSeries_add (A := ℚ) (1 / 2 : ℚ) (1 / 2 : ℚ)
    have h2 := binomialSeries_nat (R := ℚ) (A := ℚ) 1
    rw [pow_two, ← h, show (1 / 2 : ℚ) + 1 / 2 = ((1 : ℕ) : ℚ) by norm_num, h2, pow_one]
  rw [← subst_pow ha, h1, subst_add ha, subst_X ha, ← coe_substAlgHom ha, map_one]
  ring

lemma ode (R S : PowerSeries ℚ) (hS : S ^ 2 = R) :
    2 * R * d⁄dX ℚ S = d⁄dX ℚ R * S := by
  have h := congrArg (d⁄dX ℚ) hS
  rw [derivative_pow] at h
  have h' : 2 * S * d⁄dX ℚ S = d⁄dX ℚ R := by simpa using h
  calc 2 * R * d⁄dX ℚ S = S * (2 * S * d⁄dX ℚ S) := by
        rw [← hS]
        ring
    _ = S * d⁄dX ℚ R := by rw [h']
    _ = d⁄dX ℚ R * S := mul_comm _ _

lemma odeA (R S U V W A : PowerSeries ℚ) (hS : S ^ 2 = R) (hA : A * W = U + V * S) :
    2 * R * V * W * d⁄dX ℚ A +
        (2 * R * V * d⁄dX ℚ W - (2 * R * d⁄dX ℚ V + V * d⁄dX ℚ R) * W) * A =
      2 * R * V * d⁄dX ℚ U - (2 * R * d⁄dX ℚ V + V * d⁄dX ℚ R) * U := by
  have h1 := ode R S hS
  have h2 := congrArg (d⁄dX ℚ) hA
  rw [Derivation.leibniz, map_add, Derivation.leibniz] at h2
  simp only [smul_eq_mul] at h2
  linear_combination (2 * R * V) * h2 + V ^ 2 * h1 - (2 * R * d⁄dX ℚ V + V * d⁄dX ℚ R) * hA

lemma d_ofNat (n : ℕ) [n.AtLeastTwo] :
    d⁄dX ℚ (no_index (OfNat.ofNat n) : ℚ⟦X⟧) = 0 := by
  rw [← map_ofNat (C (R := ℚ)) n, derivative_C]


lemma main' (R S : PowerSeries ℚ) (hR : R = 1 - 4 * X - 4 * X ^ 2 + 26 * X ^ 3 - 4 * X ^ 4 - 40 * X ^ 5 + 9 * X ^ 6 + 16 * X ^ 7)
    (hSdef : S = (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1))
    (a : ℕ → ℚ)
    (ha : ∀ n, a n =
  coeff (n + 2)
    ((1 - 2 * X - 2 * X ^ 2 + 3 * X ^ 3 - S)
      * (2 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 : PowerSeries ℚ)⁻¹)) :
    ∀ n : ℕ, 9 ≤ n →
    ((n : ℚ) + 2) * a n + (-5 * (n : ℚ) - 5) * a (n - 1) + (-2 * (n : ℚ) + 6) * a (n - 2)
      + (38 * (n : ℚ) - 59) * a (n - 3) + (-22 * (n : ℚ) + 41) * a (n - 4)
      + (-88 * (n : ℚ) + 324) * a (n - 5) + (57 * (n : ℚ) - 237) * a (n - 6)
      + (87 * (n : ℚ) - 492) * a (n - 7) + (-34 * (n : ℚ) + 196) * a (n - 8)
      + (-32 * (n : ℚ) + 240) * a (n - 9) = 0 := by
  have hR1 : constantCoeff R = 1 := by
    rw [hR]
    simp [map_ofNat]
  have hS : S ^ 2 = R := by
    rw [hSdef]
    exact sqrt_sq R hR1
  obtain ⟨A, hAdef⟩ : ∃ A : PowerSeries ℚ, A = (1 - 2 * X - 2 * X ^ 2 + 3 * X ^ 3 - S) * (2 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 : PowerSeries ℚ)⁻¹ :=
    ⟨_, rfl⟩
  have ha' : ∀ n, a n = coeff (n + 2) A := fun n => by rw [ha, hAdef]
  have hW0 : constantCoeff (2 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 : PowerSeries ℚ) ≠ 0 := by simp [map_ofNat]
  have hA : A * (2 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3) = (1 - 2 * X - 2 * X ^ 2 + 3 * X ^ 3) + (-1) * S := by
    rw [hAdef, mul_assoc, PowerSeries.inv_mul_cancel _ hW0]
    ring
  have hode := odeA R S (1 - 2 * X - 2 * X ^ 2 + 3 * X ^ 3) (-1) (2 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3) A hS hA
  have dR : d⁄dX ℚ R = -4 - 8 * X + 78 * X ^ 2 - 16 * X ^ 3 - 200 * X ^ 4 + 54 * X ^ 5 + 112 * X ^ 6 := by
    rw [hR]
    simp [Derivation.leibniz, d_ofNat] <;> ring
  have dU : d⁄dX ℚ (1 - 2 * X - 2 * X ^ 2 + 3 * X ^ 3 : ℚ⟦X⟧) = -2 - 4 * X + 9 * X ^ 2 := by
    simp [Derivation.leibniz, d_ofNat] <;> ring
  have dV : d⁄dX ℚ (-1 : ℚ⟦X⟧) = 0 := by
    simp [Derivation.leibniz, d_ofNat] <;> ring
  have dW : d⁄dX ℚ (2 - 4 * X - 2 * X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) = -4 - 4 * X + 12 * X ^ 2 := by
    simp [Derivation.leibniz, d_ofNat] <;> ring
  rw [dR] at hode
  simp only [dU, dV, dW] at hode
  rw [hR] at hode
  have hg : (-1 + X : ℚ⟦X⟧) ≠ 0 := by
    intro hg0
    have h0 := congrArg constantCoeff hg0
    simp [map_ofNat] at h0
  have red : (-1 + X : ℚ⟦X⟧) * (C (4 : ℚ) * (d⁄dX ℚ A * X ^ 0) +
      C (-20 : ℚ) * (d⁄dX ℚ A * X ^ 1) +
      C (-8 : ℚ) * (d⁄dX ℚ A * X ^ 2) +
      C (152 : ℚ) * (d⁄dX ℚ A * X ^ 3) +
      C (-88 : ℚ) * (d⁄dX ℚ A * X ^ 4) +
      C (-352 : ℚ) * (d⁄dX ℚ A * X ^ 5) +
      C (228 : ℚ) * (d⁄dX ℚ A * X ^ 6) +
      C (348 : ℚ) * (d⁄dX ℚ A * X ^ 7) +
      C (-136 : ℚ) * (d⁄dX ℚ A * X ^ 8) +
      C (-128 : ℚ) * (d⁄dX ℚ A * X ^ 9) +
      C (24 : ℚ) * (A * X ^ 1) +
      C (-84 : ℚ) * (A * X ^ 2) +
      C (-12 : ℚ) * (A * X ^ 3) +
      C (240 : ℚ) * (A * X ^ 4) +
      C (-36 : ℚ) * (A * X ^ 5) +
      C (-228 : ℚ) * (A * X ^ 6) +
      C (-32 : ℚ) * (A * X ^ 7) +
      C (64 : ℚ) * (A * X ^ 8)) =
      (-1 + X : ℚ⟦X⟧) * (C (8 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 1) +
      C (-28 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 2) +
      C (-4 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 3) +
      C (80 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 4) +
      C (20 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 5) +
      C (-124 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 6) +
      C (-48 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 7) +
      C (48 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 8)) := by
    simp only [map_neg, map_ofNat, map_one, map_zero]
    linear_combination (1 : ℚ⟦X⟧) * hode
  have key := mul_left_cancel₀ hg red
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 9 := ⟨n - 9, by omega⟩
  have tp0 : coeff (k + 10) (C (4 : ℚ) * (d⁄dX ℚ A * X ^ 0)) =
      (4 : ℚ) * (coeff (k + 11) A * ((k : ℚ) + 11)) := by
    have e : k + 10 = k + 10 + 0 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 10 + 1 = k + 11 by omega]; push_cast; ring)
  have tp1 : coeff (k + 10) (C (-20 : ℚ) * (d⁄dX ℚ A * X ^ 1)) =
      (-20 : ℚ) * (coeff (k + 10) A * ((k : ℚ) + 10)) := by
    have e : k + 10 = k + 9 + 1 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 9 + 1 = k + 10 by omega]; push_cast; ring)
  have tp2 : coeff (k + 10) (C (-8 : ℚ) * (d⁄dX ℚ A * X ^ 2)) =
      (-8 : ℚ) * (coeff (k + 9) A * ((k : ℚ) + 9)) := by
    have e : k + 10 = k + 8 + 2 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 8 + 1 = k + 9 by omega]; push_cast; ring)
  have tp3 : coeff (k + 10) (C (152 : ℚ) * (d⁄dX ℚ A * X ^ 3)) =
      (152 : ℚ) * (coeff (k + 8) A * ((k : ℚ) + 8)) := by
    have e : k + 10 = k + 7 + 3 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 7 + 1 = k + 8 by omega]; push_cast; ring)
  have tp4 : coeff (k + 10) (C (-88 : ℚ) * (d⁄dX ℚ A * X ^ 4)) =
      (-88 : ℚ) * (coeff (k + 7) A * ((k : ℚ) + 7)) := by
    have e : k + 10 = k + 6 + 4 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 6 + 1 = k + 7 by omega]; push_cast; ring)
  have tp5 : coeff (k + 10) (C (-352 : ℚ) * (d⁄dX ℚ A * X ^ 5)) =
      (-352 : ℚ) * (coeff (k + 6) A * ((k : ℚ) + 6)) := by
    have e : k + 10 = k + 5 + 5 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 5 + 1 = k + 6 by omega]; push_cast; ring)
  have tp6 : coeff (k + 10) (C (228 : ℚ) * (d⁄dX ℚ A * X ^ 6)) =
      (228 : ℚ) * (coeff (k + 5) A * ((k : ℚ) + 5)) := by
    have e : k + 10 = k + 4 + 6 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 4 + 1 = k + 5 by omega]; push_cast; ring)
  have tp7 : coeff (k + 10) (C (348 : ℚ) * (d⁄dX ℚ A * X ^ 7)) =
      (348 : ℚ) * (coeff (k + 4) A * ((k : ℚ) + 4)) := by
    have e : k + 10 = k + 3 + 7 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 3 + 1 = k + 4 by omega]; push_cast; ring)
  have tp8 : coeff (k + 10) (C (-136 : ℚ) * (d⁄dX ℚ A * X ^ 8)) =
      (-136 : ℚ) * (coeff (k + 3) A * ((k : ℚ) + 3)) := by
    have e : k + 10 = k + 2 + 8 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 2 + 1 = k + 3 by omega]; push_cast; ring)
  have tp9 : coeff (k + 10) (C (-128 : ℚ) * (d⁄dX ℚ A * X ^ 9)) =
      (-128 : ℚ) * (coeff (k + 2) A * ((k : ℚ) + 2)) := by
    have e : k + 10 = k + 1 + 9 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 1 + 1 = k + 2 by omega]; push_cast; ring)
  have tq1 : coeff (k + 10) (C (24 : ℚ) * (A * X ^ 1)) = (24 : ℚ) * coeff (k + 9) A := by
    have e : k + 10 = k + 9 + 1 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq2 : coeff (k + 10) (C (-84 : ℚ) * (A * X ^ 2)) = (-84 : ℚ) * coeff (k + 8) A := by
    have e : k + 10 = k + 8 + 2 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq3 : coeff (k + 10) (C (-12 : ℚ) * (A * X ^ 3)) = (-12 : ℚ) * coeff (k + 7) A := by
    have e : k + 10 = k + 7 + 3 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq4 : coeff (k + 10) (C (240 : ℚ) * (A * X ^ 4)) = (240 : ℚ) * coeff (k + 6) A := by
    have e : k + 10 = k + 6 + 4 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq5 : coeff (k + 10) (C (-36 : ℚ) * (A * X ^ 5)) = (-36 : ℚ) * coeff (k + 5) A := by
    have e : k + 10 = k + 5 + 5 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq6 : coeff (k + 10) (C (-228 : ℚ) * (A * X ^ 6)) = (-228 : ℚ) * coeff (k + 4) A := by
    have e : k + 10 = k + 4 + 6 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq7 : coeff (k + 10) (C (-32 : ℚ) * (A * X ^ 7)) = (-32 : ℚ) * coeff (k + 3) A := by
    have e : k + 10 = k + 3 + 7 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq8 : coeff (k + 10) (C (64 : ℚ) * (A * X ^ 8)) = (64 : ℚ) * coeff (k + 2) A := by
    have e : k + 10 = k + 2 + 8 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have th1 : coeff (k + 10) (C (8 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 1)) = 0 := by
    have e : k + 10 = k + 9 + 1 := by omega
    rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
  have th2 : coeff (k + 10) (C (-28 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 2)) = 0 := by
    have e : k + 10 = k + 8 + 2 := by omega
    rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
  have th3 : coeff (k + 10) (C (-4 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 3)) = 0 := by
    have e : k + 10 = k + 7 + 3 := by omega
    rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
  have th4 : coeff (k + 10) (C (80 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 4)) = 0 := by
    have e : k + 10 = k + 6 + 4 := by omega
    rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
  have th5 : coeff (k + 10) (C (20 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 5)) = 0 := by
    have e : k + 10 = k + 5 + 5 := by omega
    rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
  have th6 : coeff (k + 10) (C (-124 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 6)) = 0 := by
    have e : k + 10 = k + 4 + 6 := by omega
    rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
  have th7 : coeff (k + 10) (C (-48 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 7)) = 0 := by
    have e : k + 10 = k + 3 + 7 := by omega
    rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
  have th8 : coeff (k + 10) (C (48 : ℚ) * ((1 : ℚ⟦X⟧) * X ^ 8)) = 0 := by
    have e : k + 10 = k + 2 + 8 := by omega
    rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_one, if_neg (by omega), mul_zero]
  have hc := congrArg (coeff (k + 10)) key
  simp only [map_add, map_zero, tp0, tp1, tp2, tp3, tp4, tp5, tp6, tp7, tp8, tp9, tq1, tq2, tq3, tq4, tq5, tq6, tq7, tq8, th1, th2, th3, th4, th5, th6, th7, th8] at hc
  have g0 : a (k + 9) = coeff (k + 11) A := by
    rw [ha', show k + 9 + 2 = k + 11 by omega]
  have g1 : a (k + 9 - 1) = coeff (k + 10) A := by
    rw [ha', show k + 9 - 1 + 2 = k + 10 by omega]
  have g2 : a (k + 9 - 2) = coeff (k + 9) A := by
    rw [ha', show k + 9 - 2 + 2 = k + 9 by omega]
  have g3 : a (k + 9 - 3) = coeff (k + 8) A := by
    rw [ha', show k + 9 - 3 + 2 = k + 8 by omega]
  have g4 : a (k + 9 - 4) = coeff (k + 7) A := by
    rw [ha', show k + 9 - 4 + 2 = k + 7 by omega]
  have g5 : a (k + 9 - 5) = coeff (k + 6) A := by
    rw [ha', show k + 9 - 5 + 2 = k + 6 by omega]
  have g6 : a (k + 9 - 6) = coeff (k + 5) A := by
    rw [ha', show k + 9 - 6 + 2 = k + 5 by omega]
  have g7 : a (k + 9 - 7) = coeff (k + 4) A := by
    rw [ha', show k + 9 - 7 + 2 = k + 4 by omega]
  have g8 : a (k + 9 - 8) = coeff (k + 3) A := by
    rw [ha', show k + 9 - 8 + 2 = k + 3 by omega]
  have g9 : a (k + 9 - 9) = coeff (k + 2) A := by
    rw [ha', show k + 9 - 9 + 2 = k + 2 by omega]
  rw [g0, g1, g2, g3, g4, g5, g6, g7, g8, g9]
  push_cast at hc ⊢
  linear_combination (1 / 4 : ℚ) * hc

end OMA.P186341

theorem OMA.solution : type_of% @OMA.S_oeis_a186341.main :=
  OMA.P186341.main' OMA.S_oeis_a186341.R OMA.S_oeis_a186341.S rfl rfl OMA.S_oeis_a186341.a (fun _ => rfl)
