import OMAStatements.S_oeis_a141344
import Mathlib

-- Problem: A141344, R. J. Mathar's conjectured recurrence for the g.f. (2 - sqrt(1+4x))/(2 - x - sqrt(1+4x)).
-- Upstream: formal-conjectures statements/oeis-a141344.lean (declaration OMA.S_oeis_a141344.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: the rescaled binomial series equals S = sqrt(1 + 4x) (both square to 1 + 4x with constant
-- term 1), and (2 - S)/(2 - x - S) = (3 - 6x + x S)/(3 - 8x + x^2) using S^2 = 1 + 4x. With
-- 2 R S' = R' S the recurrence follows from an explicit polynomial certificate (and an induction
-- from exact initial values when needed).

namespace OMA.P_oeis_a141344

open OMA.S_oeis_a141344 PowerSeries

noncomputable def R : PowerSeries ℚ := 1 + 4 * X

noncomputable def S : PowerSeries ℚ := (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)).subst (R - 1)

theorem hR1 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' (by simp [R])

theorem S_sq : S ^ 2 = R := by
  have h : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = 1 + X := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    have h12 : (1 / 2 + 1 / 2 : ℚ) = ((1 : ℕ) : ℚ) := by norm_num
    rw [h12, PowerSeries.binomialSeries_nat, pow_one]
  unfold S
  rw [← coe_substAlgHom hR1, ← map_pow, h, map_add, map_one, substAlgHom_X]
  ring

theorem ode : 2 * R * d⁄dX ℚ S = d⁄dX ℚ R * S := by
  have h := congrArg (d⁄dX ℚ) S_sq
  rw [pow_two, Derivation.leibniz, smul_eq_mul] at h
  rw [← h, ← S_sq]
  ring

theorem hRC : R = C (1 : ℚ) + C (4 : ℚ) * X ^ 1 := by
  simp only [R, map_one, map_neg, map_ofNat]
  ring

theorem hDR : d⁄dX ℚ R = C (4 : ℚ) := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  push_cast
  ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (8 : ℚ) * X ^ 1 * d⁄dX ℚ S - (C (4 : ℚ) * S) = 0 := by
  have h := ode
  rw [hDR, hRC] at h
  simp only [map_one, map_neg, map_ofNat] at h ⊢
  linear_combination h

theorem cx (c : ℚ) (j n : ℕ) (f : ℚ⟦X⟧) (h : j ≤ n) :
    coeff n (C c * X ^ j * f) = c * coeff (n - j) f := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos h]

theorem cx0 (c : ℚ) (n : ℕ) (f : ℚ⟦X⟧) : coeff n (C c * f) = c * coeff n f := coeff_C_mul _ _ _

theorem cc (c : ℚ) (j n : ℕ) (h : n ≠ j) : coeff n (C c * X ^ j) = 0 := by
  rw [coeff_C_mul_X_pow, if_neg h]

theorem cc0 (c : ℚ) (n : ℕ) (h : n ≠ 0) : coeff n (C c : ℚ⟦X⟧) = 0 := by
  rw [coeff_C, if_neg h]

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 2) S * ((m : ℚ) + 2)) + (8 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((4 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 1)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 1 - 1 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := ((3 - 6 * X + X * S) * (3 - 8 * X + X ^ 2 : PowerSeries ℚ)⁻¹)

theorem S_const0 : constantCoeff S = 1 := by
  have h0 : constantCoeff (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) - 1) = 0 := by simp
  have hc : constantCoeff (R - 1) = 0 := by simp [R]
  have h1 := constantCoeff_subst_eq_zero (a := (R - 1 : ℚ⟦X⟧)) hc _ h0
  have h2 : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) - 1).subst (R - 1) = S - 1 := by
    unfold S
    rw [← coe_substAlgHom hR1, map_sub, map_one]
  rw [h2] at h1
  have h3 : constantCoeff (S - 1) = 0 := h1
  rw [map_sub, map_one, sub_eq_zero] at h3
  exact h3

theorem root_sq : rootSeries ^ 2 = R := by
  have h : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = 1 + X := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    have h12 : (1 / 2 + 1 / 2 : ℚ) = ((1 : ℕ) : ℚ) := by norm_num
    rw [h12, PowerSeries.binomialSeries_nat, pow_one]
  unfold rootSeries R
  rw [← map_pow, h, map_add, map_one, rescale_X]
  simp only [map_ofNat]

theorem root_const : constantCoeff rootSeries = 1 := by
  unfold rootSeries
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale]
  simp

theorem hroot : rootSeries = S := by
  have h : (rootSeries - S) * (rootSeries + S) = 0 := by
    linear_combination root_sq - S_sq
  rcases mul_eq_zero.mp h with h1 | h1
  · exact sub_eq_zero.mp h1
  · exfalso
    have h2 := congrArg constantCoeff h1
    rw [map_add, root_const, S_const0, map_zero] at h2
    norm_num at h2

theorem a_eq (n : ℕ) : a n = coeff n F := by
  unfold a generatingSeries F
  rw [hroot]
  congr 1
  have hb : (2 - X - S) * (2 - X - S)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by
    rw [show (2 - X - S : ℚ⟦X⟧) = C (2 : ℚ) - X - S from by simp only [map_ofNat], map_sub, map_sub,
      constantCoeff_C, constantCoeff_X, S_const0]
    norm_num)
  have hd : (3 - 8 * X + X ^ 2 : ℚ⟦X⟧) * (3 - 8 * X + X ^ 2 : ℚ⟦X⟧)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by
      rw [show (3 - 8 * X + X ^ 2 : ℚ⟦X⟧) = C (3 : ℚ) + C (-8 : ℚ) * X ^ 1 + C (1 : ℚ) * X ^ 2 from by
        simp only [map_one, map_neg, map_ofNat] <;> ring]
      simp)
  have hk : (2 - S) * (3 - 8 * X + X ^ 2) = (3 - 6 * X + X * S) * (2 - X - S) := by
    have hs := S_sq
    unfold R at hs
    linear_combination X * hs
  linear_combination ((2 - X - S)⁻¹ * (3 - 8 * X + X ^ 2 : ℚ⟦X⟧)⁻¹) * hk
    + ((3 - 6 * X + X * S) * (3 - 8 * X + X ^ 2 : ℚ⟦X⟧)⁻¹) * hb - ((2 - S) * (2 - X - S)⁻¹) * hd

theorem hF : F * (3 - 8 * X + X ^ 2 : ℚ⟦X⟧) = 3 - 6 * X + X * S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (3 - 8 * X + X ^ 2 : ℚ⟦X⟧) = C (3 : ℚ) + C (-8 : ℚ) * X ^ 1 + C (1 : ℚ) * X ^ 2 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (3 : ℚ) * F + C (-8 : ℚ) * X ^ 1 * F + C (1 : ℚ) * X ^ 2 * F - (C (1 : ℚ) * X ^ 1 * S) - (C (3 : ℚ) + C (-6 : ℚ) * X ^ 1) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (3 : ℚ) * coeff (m + 2) F + (-8 : ℚ) * coeff (m + 1) F + (1 : ℚ) * coeff (m) F - ((1 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 2)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega] at h
  linear_combination h

theorem mainQ : ∀ n : ℕ, 3 ≤ n → (3 * (n : ℚ) - 3) * a n + (4 * (n : ℚ) - 22) * a (n - 1) + (-31 * (n : ℚ) + 79) * a (n - 2)
      + (4 * (n : ℚ) - 10) * a (n - 3) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 from by omega, show k + 3 - 2 = k + 1 from by omega, show k + 3 - 3 = k from by omega]
  simp only [a_eq]
  have r1_49 := rel1 (k)
  have r1_50 := rel1 (k + 1)
  have r2_48 := rel2 (k)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_49 r1_50 r2_48 ⊢
  push_cast at r1_49 r1_50 r2_48 ⊢
  linear_combination ((-10 : ℚ) + (4 : ℚ) * ((k : ℚ) + 3) ^ 1) * r1_49 + ((-1 : ℚ) + (1 : ℚ) * ((k : ℚ) + 3) ^ 1) * r1_50 + ((1 / 2 : ℚ)) * r2_48

theorem main' : ∀ k : ℕ, let n : ℚ := (k : ℚ) + 3
    3 * (n - 1) * a (k + 3) + 2 * (2 * n - 11) * a (k + 2) +
    (79 - 31 * n) * a (k + 1) + 2 * (2 * n - 5) * a k = 0 := by
  intro k
  have h := mainQ (k + 3) (by omega)
  rw [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega, show k + 3 - 3 = k by omega] at h
  push_cast at h
  dsimp only
  linear_combination h

end OMA.P_oeis_a141344

theorem OMA.solution : type_of% @OMA.S_oeis_a141344.main := OMA.P_oeis_a141344.main'
