import OMAStatements.S_oeis_a191786
import Mathlib

-- Problem: A191786: Number of length n left factors of Dyck paths having no triple-rises (triple-rise = three consecutive (1,1)-steps).
-- Upstream: formal-conjectures statements/oeis-a191786.lean (declaration OMA.S_oeis_a191786.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: S = sqrt(R) satisfies S^2 = R, so 2 R S' = R' S, a first-order linear recurrence with
-- linear coefficients for the coefficients of S (rel2). The series F = (A + B S) / C satisfies
-- C F = A + B S, a constant-coefficient relation between the coefficients of F and of S (rel1). The
-- conjectured recurrence is an explicit linear combination, with polynomial coefficients in n, of
-- shifted instances of rel1 and rel2 (the certificate was found by exact linear algebra).

namespace OMA.P_oeis_a191786

open OMA.S_oeis_a191786 PowerSeries

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

theorem hRC : R = C (1 : ℚ) + C (-2 : ℚ) * X ^ 2 + C (-3 : ℚ) * X ^ 4 := by
  simp only [R, map_one, map_neg, map_ofNat]
  ring

theorem hDR : d⁄dX ℚ R = C (-4 : ℚ) * X ^ 1 + C (-12 : ℚ) * X ^ 3 := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  push_cast
  ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (-4 : ℚ) * X ^ 2 * d⁄dX ℚ S + C (-6 : ℚ) * X ^ 4 * d⁄dX ℚ S - (C (-4 : ℚ) * X ^ 1 * S + C (-12 : ℚ) * X ^ 3 * S) = 0 := by
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

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 5) S * ((m : ℚ) + 5)) + (-4 : ℚ) * (coeff (m + 3) S * ((m : ℚ) + 3)) + (-6 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((-4 : ℚ) * coeff (m + 3) S + (-12 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 4)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 4 - 1 = m + 3 from by omega, show m + 4 - 2 = m + 2 from by omega, show m + 4 - 3 = m + 1 from by omega, show m + 4 - 4 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := ((-1 - X + 3 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5 + (1 + X + X ^ 2) * S) * (2 - 2 * X - 2 * X ^ 2 - 2 * X ^ 3 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = coeff (n + 3) F := rfl

theorem hF : F * (2 - 2 * X - 2 * X ^ 2 - 2 * X ^ 3 : ℚ⟦X⟧) = -1 - X + 3 * X ^ 3 + 3 * X ^ 4 + 2 * X ^ 5 + (1 + X + X ^ 2) * S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (2 - 2 * X - 2 * X ^ 2 - 2 * X ^ 3 : ℚ⟦X⟧) = C (2 : ℚ) + C (-2 : ℚ) * X ^ 1 + C (-2 : ℚ) * X ^ 2 + C (-2 : ℚ) * X ^ 3 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (2 : ℚ) * F + C (-2 : ℚ) * X ^ 1 * F + C (-2 : ℚ) * X ^ 2 * F + C (-2 : ℚ) * X ^ 3 * F - (C (1 : ℚ) * S + C (1 : ℚ) * X ^ 1 * S + C (1 : ℚ) * X ^ 2 * S) - (C (-1 : ℚ) + C (-1 : ℚ) * X ^ 1 + C (3 : ℚ) * X ^ 3 + C (3 : ℚ) * X ^ 4 + C (2 : ℚ) * X ^ 5) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (2 : ℚ) * coeff (m + 6) F + (-2 : ℚ) * coeff (m + 5) F + (-2 : ℚ) * coeff (m + 4) F + (-2 : ℚ) * coeff (m + 3) F - ((1 : ℚ) * coeff (m + 6) S + (1 : ℚ) * coeff (m + 5) S + (1 : ℚ) * coeff (m + 4) S) = 0 := by
  have h := congrArg (coeff (m + 6)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 6 - 1 = m + 5 from by omega, show m + 6 - 2 = m + 4 from by omega, show m + 6 - 3 = m + 3 from by omega] at h
  linear_combination h

theorem main' : ∀ n : ℕ, 8 ≤ n → (-13 * (n : ℚ) ^ 2 + 31 * (n : ℚ) + 210) * a n
      + (-13 * (n : ℚ) ^ 2 + 19 * (n : ℚ) - 102) * a (n - 1)
      + (65 * (n : ℚ) ^ 2 - 221 * (n : ℚ) - 516) * a (n - 2)
      + (65 * (n : ℚ) ^ 2 - 197 * (n : ℚ) + 288) * a (n - 3)
      + (-13 * (n : ℚ) ^ 2 + 19 * (n : ℚ) + 582) * a (n - 4)
      + (-39 * (n : ℚ) ^ 2 + 105 * (n : ℚ) - 210) * a (n - 5)
      + (-169 * (n : ℚ) ^ 2 + 1201 * (n : ℚ) - 2208) * a (n - 6)
      + (-117 * (n : ℚ) ^ 2 + 945 * (n : ℚ) - 1800) * a (n - 7)
      + (-78 * (n : ℚ) ^ 2 + 618 * (n : ℚ) - 900) * a (n - 8) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
  rw [show k + 8 - 1 = k + 7 from by omega, show k + 8 - 2 = k + 6 from by omega, show k + 8 - 3 = k + 5 from by omega, show k + 8 - 4 = k + 4 from by omega, show k + 8 - 5 = k + 3 from by omega, show k + 8 - 6 = k + 2 from by omega, show k + 8 - 7 = k + 1 from by omega, show k + 8 - 8 = k from by omega]
  simp only [a_eq]
  have r1_45 := rel1 (k)
  have r1_46 := rel1 (k + 1)
  have r1_47 := rel1 (k + 2)
  have r1_48 := rel1 (k + 3)
  have r1_49 := rel1 (k + 4)
  have r1_50 := rel1 (k + 5)
  have r2_46 := rel2 (k + 3)
  have r2_47 := rel2 (k + 4)
  have r2_48 := rel2 (k + 5)
  have r2_49 := rel2 (k + 6)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_45 r1_46 r1_47 r1_48 r1_49 r1_50 r2_46 r2_47 r2_48 r2_49 ⊢
  push_cast at r1_45 r1_46 r1_47 r1_48 r1_49 r1_50 r2_46 r2_47 r2_48 r2_49 ⊢
  linear_combination ((450 : ℚ) + (-309 : ℚ) * ((k : ℚ) + 8) ^ 1 + (39 : ℚ) * ((k : ℚ) + 8) ^ 2) * r1_45 + ((450 : ℚ) + (-327 / 2 : ℚ) * ((k : ℚ) + 8) ^ 1 + (39 / 2 : ℚ) * ((k : ℚ) + 8) ^ 2) * r1_46 + ((204 : ℚ) + (-128 : ℚ) * ((k : ℚ) + 8) ^ 1 + (26 : ℚ) * ((k : ℚ) + 8) ^ 2) * r1_47 + ((-99 : ℚ) + (-70 : ℚ) * ((k : ℚ) + 8) ^ 1 + (13 : ℚ) * ((k : ℚ) + 8) ^ 2) * r1_48 + ((54 : ℚ) + (25 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-13 : ℚ) * ((k : ℚ) + 8) ^ 2) * r1_49 + ((105 : ℚ) + (31 / 2 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-13 / 2 : ℚ) * ((k : ℚ) + 8) ^ 2) * r1_50 + ((25 / 2 : ℚ) + (-13 / 2 : ℚ) * ((k : ℚ) + 8) ^ 1) * r2_46 + ((30 : ℚ) + (-39 / 4 : ℚ) * ((k : ℚ) + 8) ^ 1) * r2_47 + ((159 / 4 : ℚ) + (-39 / 4 : ℚ) * ((k : ℚ) + 8) ^ 1) * r2_48 + ((35 / 2 : ℚ) + (-13 / 4 : ℚ) * ((k : ℚ) + 8) ^ 1) * r2_49

end OMA.P_oeis_a191786

theorem OMA.solution : type_of% @OMA.S_oeis_a191786.main := OMA.P_oeis_a191786.main'
