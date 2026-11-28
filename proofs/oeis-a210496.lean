import OMAStatements.S_oeis_a210496
import Mathlib

-- Problem: A210496: Number of set partitions of [n] avoiding the patterns {1123, 1211}.
-- Upstream: formal-conjectures statements/oeis-a210496.lean (declaration OMA.S_oeis_a210496.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: S = sqrt(R) satisfies S^2 = R, so 2 R S' = R' S, a first-order linear recurrence with
-- linear coefficients for the coefficients of S (rel2). The series F = (A + B S) / C satisfies
-- C F = A + B S, a constant-coefficient relation between the coefficients of F and of S (rel1). The
-- conjectured recurrence is an explicit linear combination, with polynomial coefficients in n, of
-- shifted instances of rel1 and rel2 (the certificate was found by exact linear algebra).

namespace OMA.P_oeis_a210496

open OMA.S_oeis_a210496 PowerSeries

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

theorem hRC : R = C (1 : ℚ) + C (-2 : ℚ) * X ^ 1 + C (-3 : ℚ) * X ^ 2 + C (4 : ℚ) * X ^ 3 := by
  simp only [R, map_one, map_neg, map_ofNat]
  ring

theorem hDR : d⁄dX ℚ R = C (-2 : ℚ) + C (-6 : ℚ) * X ^ 1 + C (12 : ℚ) * X ^ 2 := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  push_cast
  ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (-4 : ℚ) * X ^ 1 * d⁄dX ℚ S + C (-6 : ℚ) * X ^ 2 * d⁄dX ℚ S + C (8 : ℚ) * X ^ 3 * d⁄dX ℚ S - (C (-2 : ℚ) * S + C (-6 : ℚ) * X ^ 1 * S + C (12 : ℚ) * X ^ 2 * S) = 0 := by
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

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 4) S * ((m : ℚ) + 4)) + (-4 : ℚ) * (coeff (m + 3) S * ((m : ℚ) + 3)) + (-6 : ℚ) * (coeff (m + 2) S * ((m : ℚ) + 2)) + (8 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((-2 : ℚ) * coeff (m + 3) S + (-6 : ℚ) * coeff (m + 2) S + (12 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 3)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 3 - 1 = m + 2 from by omega, show m + 3 - 2 = m + 1 from by omega, show m + 3 - 3 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := ((-1 + 3 * X + 2 * X ^ 2 - 14 * X ^ 3 + 15 * X ^ 4 - 3 * X ^ 5 + (1 - 2 * X + 2 * X ^ 3 - X ^ 4) * S) * (2 - 10 * X + 16 * X ^ 2 - 10 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = coeff (n + 2) F := rfl

theorem hF : F * (2 - 10 * X + 16 * X ^ 2 - 10 * X ^ 3 + 2 * X ^ 4 : ℚ⟦X⟧) = -1 + 3 * X + 2 * X ^ 2 - 14 * X ^ 3 + 15 * X ^ 4 - 3 * X ^ 5 + (1 - 2 * X + 2 * X ^ 3 - X ^ 4) * S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (2 - 10 * X + 16 * X ^ 2 - 10 * X ^ 3 + 2 * X ^ 4 : ℚ⟦X⟧) = C (2 : ℚ) + C (-10 : ℚ) * X ^ 1 + C (16 : ℚ) * X ^ 2 + C (-10 : ℚ) * X ^ 3 + C (2 : ℚ) * X ^ 4 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (2 : ℚ) * F + C (-10 : ℚ) * X ^ 1 * F + C (16 : ℚ) * X ^ 2 * F + C (-10 : ℚ) * X ^ 3 * F + C (2 : ℚ) * X ^ 4 * F - (C (1 : ℚ) * S + C (-2 : ℚ) * X ^ 1 * S + C (2 : ℚ) * X ^ 3 * S + C (-1 : ℚ) * X ^ 4 * S) - (C (-1 : ℚ) + C (3 : ℚ) * X ^ 1 + C (2 : ℚ) * X ^ 2 + C (-14 : ℚ) * X ^ 3 + C (15 : ℚ) * X ^ 4 + C (-3 : ℚ) * X ^ 5) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (2 : ℚ) * coeff (m + 6) F + (-10 : ℚ) * coeff (m + 5) F + (16 : ℚ) * coeff (m + 4) F + (-10 : ℚ) * coeff (m + 3) F + (2 : ℚ) * coeff (m + 2) F - ((1 : ℚ) * coeff (m + 6) S + (-2 : ℚ) * coeff (m + 5) S + (2 : ℚ) * coeff (m + 3) S + (-1 : ℚ) * coeff (m + 2) S) = 0 := by
  have h := congrArg (coeff (m + 6)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 6 - 1 = m + 5 from by omega, show m + 6 - 2 = m + 4 from by omega, show m + 6 - 3 = m + 3 from by omega, show m + 6 - 4 = m + 2 from by omega] at h
  linear_combination h

theorem main' : ∀ n : ℕ, 8 ≤ n → ((n : ℚ) + 2) * a n + (-6 * (n : ℚ) - 8) * a (n - 1) + (8 * (n : ℚ) + 12) * a (n - 2)
      + (13 * (n : ℚ) - 40) * a (n - 3) + (-35 * (n : ℚ) + 90) * a (n - 4)
      + (12 * (n : ℚ) - 6) * a (n - 5) + (22 * (n : ℚ) - 154) * a (n - 6)
      + (-19 * (n : ℚ) + 134) * a (n - 7) + (4 * (n : ℚ) - 30) * a (n - 8) = 0 := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
  rw [show k + 8 - 1 = k + 7 from by omega, show k + 8 - 2 = k + 6 from by omega, show k + 8 - 3 = k + 5 from by omega, show k + 8 - 4 = k + 4 from by omega, show k + 8 - 5 = k + 3 from by omega, show k + 8 - 6 = k + 2 from by omega, show k + 8 - 7 = k + 1 from by omega, show k + 8 - 8 = k from by omega]
  simp only [a_eq]
  have r1_46 := rel1 (k)
  have r1_47 := rel1 (k + 1)
  have r1_48 := rel1 (k + 2)
  have r1_49 := rel1 (k + 3)
  have r1_50 := rel1 (k + 4)
  have r2_44 := rel2 (k + 1)
  have r2_45 := rel2 (k + 2)
  have r2_46 := rel2 (k + 3)
  have r2_47 := rel2 (k + 4)
  have r2_48 := rel2 (k + 5)
  have r2_49 := rel2 (k + 6)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_46 r1_47 r1_48 r1_49 r1_50 r2_44 r2_45 r2_46 r2_47 r2_48 r2_49 ⊢
  push_cast at r1_46 r1_47 r1_48 r1_49 r1_50 r2_44 r2_45 r2_46 r2_47 r2_48 r2_49 ⊢
  linear_combination ((-15 : ℚ) + (2 : ℚ) * ((k : ℚ) + 8) ^ 1) * r1_46 + ((-8 : ℚ) + (1 / 2 : ℚ) * ((k : ℚ) + 8) ^ 1) * r1_47 + ((3 : ℚ) + (-5 / 2 : ℚ) * ((k : ℚ) + 8) ^ 1) * r1_48 + ((1 : ℚ) + (-1 / 2 : ℚ) * ((k : ℚ) + 8) ^ 1) * r1_49 + ((1 : ℚ) + (1 / 2 : ℚ) * ((k : ℚ) + 8) ^ 1) * r1_50 + ((-1 / 4 : ℚ)) * r2_44 + ((1 / 4 : ℚ)) * r2_45 + ((1 / 2 : ℚ)) * r2_46 + ((-1 / 2 : ℚ)) * r2_47 + ((-1 / 4 : ℚ)) * r2_48 + ((1 / 4 : ℚ)) * r2_49

end OMA.P_oeis_a210496

theorem OMA.solution : type_of% @OMA.S_oeis_a210496.main := OMA.P_oeis_a210496.main'
