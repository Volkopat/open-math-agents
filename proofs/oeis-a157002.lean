import OMAStatements.S_oeis_a157002
import Mathlib

-- Problem: A157002, Mathar's conjectured recurrence for the sequence a(0) = 1, a(1) = 0,
-- a(n+2) = Sum_{k=0..n+1} a(k) a(n+1-k) + Sum_{k=0..n} a(k) a(n-k).
-- Upstream: formal-conjectures statements/oeis-a157002.lean (declaration OMA.S_oeis_a157002.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds).
-- Proof idea: the g.f. F satisfies (x + x^2) F^2 - F + 1 - x = 0 (quad), so T = 1 - 2 (x + x^2) F
-- satisfies T^2 = R = 1 - 4x + 4x^3 and T(0) = 1; hence T = S, the square root of R with constant
-- term 1 (T_eq). S satisfies 2 R S' = R' S (rel2), and T = S gives 2 f(m-1) + 2 f(m-2) + s(m) = 0
-- (rel1). The recurrence is an explicit polynomial combination of shifted instances of rel1, rel2.

namespace OMA.P_oeis_a157002

open OMA.S_oeis_a157002 PowerSeries

noncomputable def R : PowerSeries ℚ := 1 - 4 * X + 4 * X ^ 3

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

theorem hRC : R = C (1 : ℚ) + C (-4 : ℚ) * X ^ 1 + C (4 : ℚ) * X ^ 3 := by
  simp only [R, map_one, map_neg, map_ofNat]
  ring

theorem hDR : d⁄dX ℚ R = C (-4 : ℚ) + C (12 : ℚ) * X ^ 2 := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  push_cast
  ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (-8 : ℚ) * X ^ 1 * d⁄dX ℚ S + C (8 : ℚ) * X ^ 3 * d⁄dX ℚ S - (C (-4 : ℚ) * S + C (12 : ℚ) * X ^ 2 * S) = 0 := by
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

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 4) S * ((m : ℚ) + 4)) + (-8 : ℚ) * (coeff (m + 3) S * ((m : ℚ) + 3)) + (8 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((-4 : ℚ) * coeff (m + 3) S + (12 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 3)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 3 - 1 = m + 2 from by omega, show m + 3 - 2 = m + 1 from by omega, show m + 3 - 3 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := PowerSeries.mk (fun n => (a n : ℚ))

theorem a_eq (n : ℕ) : (a n : ℚ) = coeff n F := by simp [F]

theorem S_const : constantCoeff S = 1 := by
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

theorem quad : (X + X ^ 2) * F ^ 2 - F + 1 - X = 0 := by
  ext n
  rw [map_zero]
  rcases n with _ | _ | n
  · simp [F, a]
  · have e1 : coeff 1 (X * F ^ 2) = coeff 0 (F ^ 2) := coeff_succ_X_mul _ _
    have e2 : coeff 1 (X ^ 2 * F ^ 2) = 0 := by simp [coeff_X_pow_mul']
    have e0 : coeff 0 (F ^ 2) = 1 := by simp [F, a]
    have e3 : coeff 1 F = 0 := by simp [F, a]
    rw [map_sub, map_add, map_sub, add_mul, map_add, e1, e2, e0, e3]
    simp
  · have h1 : coeff (n + 1) (F ^ 2) = ∑ k ∈ Finset.range (n + 2), (a k : ℚ) * a (n + 1 - k) := by
      rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [F]
    have h2 : coeff n (F ^ 2) = ∑ k ∈ Finset.range (n + 1), (a k : ℚ) * a (n - k) := by
      rw [pow_two, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
      simp [F]
    have h3 : (a (n + 2) : ℚ) = (∑ k ∈ Finset.range (n + 2), (a k : ℚ) * a (n + 1 - k))
        + ∑ k ∈ Finset.range (n + 1), (a k : ℚ) * a (n - k) := by
      rw [a]
      push_cast
      rw [Fin.sum_univ_eq_sum_range (fun k => (a k : ℚ) * a (n + 1 - k)),
        Fin.sum_univ_eq_sum_range (fun k => (a k : ℚ) * a (n - k))]
    have e1 : coeff (n + 2) (X * F ^ 2) = coeff (n + 1) (F ^ 2) := coeff_succ_X_mul _ _
    have e2 : coeff (n + 2) (X ^ 2 * F ^ 2) = coeff n (F ^ 2) := by simp [coeff_X_pow_mul']
    have e3 : coeff (n + 2) F = (a (n + 2) : ℚ) := by simp [F]
    have e4 : coeff (n + 2) (1 : ℚ⟦X⟧) = 0 := by simp [coeff_one]
    have e5 : coeff (n + 2) (X : ℚ⟦X⟧) = 0 := by simp [coeff_X]
    rw [map_sub, map_add, map_sub, add_mul, map_add, e1, e2, e3, e4, e5, h1, h2, h3]
    ring

theorem T_sq : (1 - 2 * (X + X ^ 2) * F) ^ 2 = R := by
  unfold R
  linear_combination (4 * (X + X ^ 2)) * quad

theorem T_eq : 1 - 2 * (X + X ^ 2) * F = S := by
  have h : (1 - 2 * (X + X ^ 2) * F - S) * (1 - 2 * (X + X ^ 2) * F + S) = 0 := by
    linear_combination T_sq - S_sq
  rcases mul_eq_zero.mp h with h1 | h1
  · exact sub_eq_zero.mp h1
  · exfalso
    have h2 := congrArg constantCoeff h1
    norm_num [S_const] at h2

theorem E1 : C (2 : ℚ) * X ^ 1 * F + C (2 : ℚ) * X ^ 2 * F - (C (-1 : ℚ) * S) - (C (1 : ℚ)) = 0 := by
  simp only [map_one, map_neg, map_ofNat]
  linear_combination (-1 : ℚ⟦X⟧) * T_eq

theorem rel1 (m : ℕ) : (2 : ℚ) * coeff (m + 1) F + (2 : ℚ) * coeff (m) F - ((-1 : ℚ) * coeff (m + 2) S) = 0 := by
  have h := congrArg (coeff (m + 2)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega] at h
  linear_combination h

theorem mainQ : ∀ n : ℕ, 4 ≤ n → ((n : ℚ) + 1) * a n + 3 * (-(n : ℚ) + 1) * a (n - 1) + 2 * (-2 * (n : ℚ) + 1) * a (n - 2)
      + 2 * (2 * (n : ℚ) - 7) * a (n - 3) + 2 * (2 * (n : ℚ) - 7) * a (n - 4) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  rw [show k + 4 - 1 = k + 3 from by omega, show k + 4 - 2 = k + 2 from by omega, show k + 4 - 3 = k + 1 from by omega, show k + 4 - 4 = k from by omega]
  simp only [a_eq]
  have r1_48 := rel1 (k)
  have r1_50 := rel1 (k + 2)
  have r1_51 := rel1 (k + 3)
  have r2_50 := rel2 (k + 1)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_48 r1_50 r1_51 r2_50 ⊢
  push_cast at r1_48 r1_50 r1_51 r2_50 ⊢
  linear_combination ((-7 : ℚ) + (2 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_48 + ((1 : ℚ) + (-2 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_50 + ((1 / 2 : ℚ) + (1 / 2 : ℚ) * ((k : ℚ) + 4) ^ 1) * r1_51 + ((-1 / 4 : ℚ)) * r2_50

theorem main' : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 1) * a n + 3 * (-(n : ℤ) + 1) * a (n - 1) + 2 * (-2 * (n : ℤ) + 1) * a (n - 2)
      + 2 * (2 * (n : ℤ) - 7) * a (n - 3) + 2 * (2 * (n : ℤ) - 7) * a (n - 4) = 0 := by
  intro n hn
  have h := mainQ n hn
  exact_mod_cast h

end OMA.P_oeis_a157002

theorem OMA.solution : type_of% @OMA.S_oeis_a157002.main := OMA.P_oeis_a157002.main'
