import OMAStatements.S_oeis_a112243
import Mathlib

-- Problem: A112243, conjectured recurrence for a(n) = n! [x^n] exp((x + x^2)/(1 - 2x)).
-- Upstream: formal-conjectures statements/oeis-a112243.lean (declaration OMA.S_oeis_a112243.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the e.g.f. as defined).
-- Proof idea: W = exp(U) satisfies q^2 W' = (p'q - pq') W for U = p/q (rel2), and F = (B W + A)/C
-- satisfies C F = B W + A (rel1). Writing a(n-i) = (n-i)! f(n-i) and factoring out k!, the
-- recurrence is an explicit polynomial combination of shifted instances of rel1 and rel2.

namespace OMA.P_oeis_a112243

open OMA.S_oeis_a112243 PowerSeries

theorem hU : HasSubst f := HasSubst.of_constantCoeff_zero' (by simp [f])

theorem dexp : d⁄dX ℚ (PowerSeries.exp ℚ) = PowerSeries.exp ℚ := by
  ext n
  rw [coeff_derivative, coeff_exp, coeff_exp, Nat.factorial_succ]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  push_cast
  have h : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp

theorem dW : d⁄dX ℚ E = E * d⁄dX ℚ f := by
  unfold E
  rw [derivative_subst hU, dexp]

theorem hdp : d⁄dX ℚ (X + X ^ 2 : ℚ⟦X⟧) = 1 + 2 * X := by
  rw [show (X + X ^ 2 : ℚ⟦X⟧) = C (1 : ℚ) * X ^ 1 + C (1 : ℚ) * X ^ 2 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, zero_add, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  try push_cast
  try ring

theorem hdq : d⁄dX ℚ (1 - 2 * X : ℚ⟦X⟧) = -2 := by
  rw [show (1 - 2 * X : ℚ⟦X⟧) = C (1 : ℚ) + C (-2 : ℚ) * X ^ 1 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, zero_add, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  try push_cast
  try ring

theorem ode : (1 - 4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * d⁄dX ℚ E = (1 + 2 * X - 2 * X ^ 2) * E := by
  have hq : (1 - 2 * X : ℚ⟦X⟧) * (1 - 2 * X : ℚ⟦X⟧)⁻¹ = 1 := PowerSeries.mul_inv_cancel _ (by
    rw [show (1 - 2 * X : ℚ⟦X⟧) = C (1 : ℚ) + C (-2 : ℚ) * X ^ 1 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp)
  rw [dW]
  unfold f
  rw [Derivation.leibniz, derivative_inv', smul_eq_mul, smul_eq_mul, hdp, hdq]
  linear_combination (E * (-(X + X ^ 2) * (-2) * ((1 - 2 * X : ℚ⟦X⟧) * (1 - 2 * X : ℚ⟦X⟧)⁻¹ + 1) + (1 + 2 * X) * (1 - 2 * X))) * hq

theorem E2 : C (1 : ℚ) * d⁄dX ℚ E + C (-4 : ℚ) * X ^ 1 * d⁄dX ℚ E + C (4 : ℚ) * X ^ 2 * d⁄dX ℚ E - (C (1 : ℚ) * E + C (2 : ℚ) * X ^ 1 * E + C (-2 : ℚ) * X ^ 2 * E) = 0 := by
  have h := ode
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem cx (c : ℚ) (j n : ℕ) (f : ℚ⟦X⟧) (h : j ≤ n) :
    coeff n (C c * X ^ j * f) = c * coeff (n - j) f := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_pos h]

theorem cx0 (c : ℚ) (n : ℕ) (f : ℚ⟦X⟧) : coeff n (C c * f) = c * coeff n f := coeff_C_mul _ _ _

theorem cc (c : ℚ) (j n : ℕ) (h : n ≠ j) : coeff n (C c * X ^ j) = 0 := by
  rw [coeff_C_mul_X_pow, if_neg h]

theorem cc0 (c : ℚ) (n : ℕ) (h : n ≠ 0) : coeff n (C c : ℚ⟦X⟧) = 0 := by
  rw [coeff_C, if_neg h]

theorem rel2 (m : ℕ) : (1 : ℚ) * (coeff (m + 3) E * ((m : ℚ) + 3)) + (-4 : ℚ) * (coeff (m + 2) E * ((m : ℚ) + 2)) + (4 : ℚ) * (coeff (m + 1) E * ((m : ℚ) + 1)) - ((1 : ℚ) * coeff (m + 2) E + (2 : ℚ) * coeff (m + 1) E + (-2 : ℚ) * coeff (m) E) = 0 := by
  have h := congrArg (coeff (m + 2)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := E

theorem a_eq (n : ℕ) : a n = (n.factorial : ℚ) * coeff n F := rfl

theorem hF : F * (1 : ℚ⟦X⟧) = (1) * E + (0) := by
  unfold F
  ring

theorem E1 : C (1 : ℚ) * F - (C (1 : ℚ) * E) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (1 : ℚ) * coeff (m) F - ((1 : ℚ) * coeff (m) E) = 0 := by
  have h := congrArg (coeff (m)) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cc, cc0] at h
  try simp only [cx0, sub_zero, add_zero, zero_add] at h
  skip
  linear_combination h

theorem main' : ∀ n : ℕ, 3 ≤ n →
    a n + (-4 * (n : ℚ) + 3) * a (n - 1) + 2 * ((n : ℚ) - 1) * (2 * n - 5) * a (n - 2) +
      2 * ((n : ℚ) - 1) * ((n : ℚ) - 2) * a (n - 3) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  rw [show k + 3 - 1 = k + 2 from by omega, show k + 3 - 2 = k + 1 from by omega, show k + 3 - 3 = k from by omega]
  simp only [a_eq]
  have r1_47 := rel1 (k)
  have r1_48 := rel1 (k + 1)
  have r1_49 := rel1 (k + 2)
  have r1_50 := rel1 (k + 3)
  have r2_49 := rel2 (k)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_47 r1_48 r1_49 r1_50 r2_49 ⊢
  simp only [Nat.factorial_succ]
  push_cast at r1_47 r1_48 r1_49 r1_50 r2_49 ⊢
  linear_combination (k.factorial : ℚ) * (((4 : ℚ) + (-6 : ℚ) * ((k : ℚ) + 3) ^ 1 + (2 : ℚ) * ((k : ℚ) + 3) ^ 2) * r1_47 + ((-20 : ℚ) + (38 : ℚ) * ((k : ℚ) + 3) ^ 1 + (-22 : ℚ) * ((k : ℚ) + 3) ^ 2 + (4 : ℚ) * ((k : ℚ) + 3) ^ 3) * r1_48 + ((6 : ℚ) + (-17 : ℚ) * ((k : ℚ) + 3) ^ 1 + (15 : ℚ) * ((k : ℚ) + 3) ^ 2 + (-4 : ℚ) * ((k : ℚ) + 3) ^ 3) * r1_49 + ((2 : ℚ) * ((k : ℚ) + 3) ^ 1 + (-3 : ℚ) * ((k : ℚ) + 3) ^ 2 + (1 : ℚ) * ((k : ℚ) + 3) ^ 3) * r1_50 + ((2 : ℚ) + (-3 : ℚ) * ((k : ℚ) + 3) ^ 1 + (1 : ℚ) * ((k : ℚ) + 3) ^ 2) * r2_49)

end OMA.P_oeis_a112243

theorem OMA.solution : type_of% @OMA.S_oeis_a112243.main := OMA.P_oeis_a112243.main'
