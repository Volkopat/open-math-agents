import OMAStatements.S_oeis_a110198
import Mathlib

/-
A110198: the coefficients a(n) of A = (U + V S) / W, where S is the square root of
R = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 with S(0) = 1, U = 0, V = 1, W = 1 - 3 * X + X ^ 2 - X ^ 3 + 3 * X ^ 4 - X ^ 5,
satisfy the stated recurrence with polynomial coefficients.

- sqrt_sq: S^2 = R, because the binomial series with exponent 1/2 squares to 1 + X and
  substitution is a ring homomorphism.
- ode: differentiating S^2 = R and multiplying by S gives 2 R S' = R' S.
- odeA: with A W = U + V S this yields the first-order equation
  2 R V W A' + (2 R V W' - (2 R V' + V R') W) A = 2 R V U' - (2 R V' + V R') U.
- For the given polynomials this equation is written out, and comparing the coefficient of
  X^m on both sides gives the recurrence, up to a rational factor.
-/

namespace OMA.P110198

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


lemma main' (R S : PowerSeries ℚ) (hR : R = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hSdef : S = (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1))
    (a : ℕ → ℚ)
    (ha : ∀ n, a n =
  coeff n
    ((S)
      * (1 - 3 * X + X ^ 2 - X ^ 3 + 3 * X ^ 4 - X ^ 5 : PowerSeries ℚ)⁻¹)) :
    ∀ n : ℕ, 5 ≤ n →
    (n : ℚ) * a n + (-3 * (n : ℚ) + 1) * a (n - 1) + (n : ℚ) * a (n - 2)
      + (-(n : ℚ) + 2) * a (n - 3) + (3 * (n : ℚ) - 5) * a (n - 4)
      + (-(n : ℚ) + 2) * a (n - 5) = 0 := by
  have hR1 : constantCoeff R = 1 := by
    rw [hR]
    simp [map_ofNat]
  have hS : S ^ 2 = R := by
    rw [hSdef]
    exact sqrt_sq R hR1
  obtain ⟨A, hAdef⟩ : ∃ A : PowerSeries ℚ, A = (S) * (1 - 3 * X + X ^ 2 - X ^ 3 + 3 * X ^ 4 - X ^ 5 : PowerSeries ℚ)⁻¹ :=
    ⟨_, rfl⟩
  have ha' : ∀ n, a n = coeff n A := fun n => by rw [ha, hAdef]
  have hW0 : constantCoeff (1 - 3 * X + X ^ 2 - X ^ 3 + 3 * X ^ 4 - X ^ 5 : PowerSeries ℚ) ≠ 0 := by simp [map_ofNat]
  have hA : A * (1 - 3 * X + X ^ 2 - X ^ 3 + 3 * X ^ 4 - X ^ 5) = (0) + (1) * S := by
    rw [hAdef, mul_assoc, PowerSeries.inv_mul_cancel _ hW0]
    ring
  have hode := odeA R S (0) (1) (1 - 3 * X + X ^ 2 - X ^ 3 + 3 * X ^ 4 - X ^ 5) A hS hA
  have dR : d⁄dX ℚ R = -2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 := by
    rw [hR]
    simp [Derivation.leibniz, d_ofNat] <;> ring
  have dU : d⁄dX ℚ (0 : ℚ⟦X⟧) = 0 := by
    simp [Derivation.leibniz, d_ofNat] <;> ring
  have dV : d⁄dX ℚ (1 : ℚ⟦X⟧) = 0 := by
    simp [Derivation.leibniz, d_ofNat] <;> ring
  have dW : d⁄dX ℚ (1 - 3 * X + X ^ 2 - X ^ 3 + 3 * X ^ 4 - X ^ 5 : ℚ⟦X⟧) = -3 + 2 * X - 3 * X ^ 2 + 12 * X ^ 3 - 5 * X ^ 4 := by
    simp [Derivation.leibniz, d_ofNat] <;> ring
  rw [dR] at hode
  simp only [dU, dV, dW] at hode
  rw [hR] at hode
  have hg : (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
    intro hg0
    have h0 := congrArg constantCoeff hg0
    simp [map_ofNat] at h0
  have red : (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 : ℚ⟦X⟧) * (C (2 : ℚ) * (d⁄dX ℚ A * X ^ 0) +
      C (-6 : ℚ) * (d⁄dX ℚ A * X ^ 1) +
      C (2 : ℚ) * (d⁄dX ℚ A * X ^ 2) +
      C (-2 : ℚ) * (d⁄dX ℚ A * X ^ 3) +
      C (6 : ℚ) * (d⁄dX ℚ A * X ^ 4) +
      C (-2 : ℚ) * (d⁄dX ℚ A * X ^ 5) +
      C (-4 : ℚ) * (A * X ^ 0) +
      C (4 : ℚ) * (A * X ^ 1) +
      C (-2 : ℚ) * (A * X ^ 2) +
      C (14 : ℚ) * (A * X ^ 3) +
      C (-6 : ℚ) * (A * X ^ 4)) =
      (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4 : ℚ⟦X⟧) * (0) := by
    simp only [map_neg, map_ofNat, map_one, map_zero]
    linear_combination (1 : ℚ⟦X⟧) * hode
  have key := mul_left_cancel₀ hg red
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have tp0 : coeff (k + 4) (C (2 : ℚ) * (d⁄dX ℚ A * X ^ 0)) =
      (2 : ℚ) * (coeff (k + 5) A * ((k : ℚ) + 5)) := by
    have e : k + 4 = k + 4 + 0 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 4 + 1 = k + 5 by omega]; push_cast; ring)
  have tp1 : coeff (k + 4) (C (-6 : ℚ) * (d⁄dX ℚ A * X ^ 1)) =
      (-6 : ℚ) * (coeff (k + 4) A * ((k : ℚ) + 4)) := by
    have e : k + 4 = k + 3 + 1 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 3 + 1 = k + 4 by omega]; push_cast; ring)
  have tp2 : coeff (k + 4) (C (2 : ℚ) * (d⁄dX ℚ A * X ^ 2)) =
      (2 : ℚ) * (coeff (k + 3) A * ((k : ℚ) + 3)) := by
    have e : k + 4 = k + 2 + 2 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 2 + 1 = k + 3 by omega]; push_cast; ring)
  have tp3 : coeff (k + 4) (C (-2 : ℚ) * (d⁄dX ℚ A * X ^ 3)) =
      (-2 : ℚ) * (coeff (k + 2) A * ((k : ℚ) + 2)) := by
    have e : k + 4 = k + 1 + 3 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (rw [show k + 1 + 1 = k + 2 by omega]; push_cast; ring)
  have tp4 : coeff (k + 4) (C (6 : ℚ) * (d⁄dX ℚ A * X ^ 4)) =
      (6 : ℚ) * (coeff (k + 1) A * ((k : ℚ) + 1)) := by
    have e : k + 4 = k + 4 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
    all_goals (push_cast; ring)
  have tp5 : coeff (k + 4) (C (-2 : ℚ) * (d⁄dX ℚ A * X ^ 5)) =
      (-2 : ℚ) * (coeff k A * ((k : ℚ) + 0)) := by
    rcases k with _ | k'
    · simp [coeff_C_mul, coeff_mul_X_pow']
    · have e : k' + 1 + 4 = k' + 5 := by omega
      conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow, coeff_derivative]
      all_goals (push_cast; ring)
  have tq0 : coeff (k + 4) (C (-4 : ℚ) * (A * X ^ 0)) = (-4 : ℚ) * coeff (k + 4) A := by
    have e : k + 4 = k + 4 + 0 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq1 : coeff (k + 4) (C (4 : ℚ) * (A * X ^ 1)) = (4 : ℚ) * coeff (k + 3) A := by
    have e : k + 4 = k + 3 + 1 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq2 : coeff (k + 4) (C (-2 : ℚ) * (A * X ^ 2)) = (-2 : ℚ) * coeff (k + 2) A := by
    have e : k + 4 = k + 2 + 2 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq3 : coeff (k + 4) (C (14 : ℚ) * (A * X ^ 3)) = (14 : ℚ) * coeff (k + 1) A := by
    have e : k + 4 = k + 1 + 3 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have tq4 : coeff (k + 4) (C (-6 : ℚ) * (A * X ^ 4)) = (-6 : ℚ) * coeff (k) A := by
    have e : k + 4 = k + 4 := by omega
    conv_lhs => rw [e, coeff_C_mul, coeff_mul_X_pow]
  have hc := congrArg (coeff (k + 4)) key
  simp only [map_add, map_zero, tp0, tp1, tp2, tp3, tp4, tp5, tq0, tq1, tq2, tq3, tq4] at hc
  have g0 : a (k + 5) = coeff (k + 5) A := ha' _
  have g1 : a (k + 5 - 1) = coeff (k + 4) A := by
    rw [ha', show k + 5 - 1 = k + 4 by omega]
  have g2 : a (k + 5 - 2) = coeff (k + 3) A := by
    rw [ha', show k + 5 - 2 = k + 3 by omega]
  have g3 : a (k + 5 - 3) = coeff (k + 2) A := by
    rw [ha', show k + 5 - 3 = k + 2 by omega]
  have g4 : a (k + 5 - 4) = coeff (k + 1) A := by
    rw [ha', show k + 5 - 4 = k + 1 by omega]
  have g5 : a (k + 5 - 5) = coeff (k) A := by
    rw [ha', show k + 5 - 5 = k by omega]
  rw [g0, g1, g2, g3, g4, g5]
  push_cast at hc ⊢
  linear_combination (1 / 2 : ℚ) * hc

end OMA.P110198

theorem OMA.solution : type_of% @OMA.S_oeis_a110198.main :=
  OMA.P110198.main' OMA.S_oeis_a110198.R OMA.S_oeis_a110198.S rfl rfl OMA.S_oeis_a110198.a (fun _ => rfl)
