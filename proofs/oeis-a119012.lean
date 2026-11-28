import OMAStatements.S_oeis_a119012
import Mathlib

-- Problem: A119012: Number of valleys strictly above the x-axis in all hill-free Dyck paths of semilength n (a hill in a Dyck path is a peak at level 1).
-- Upstream: formal-conjectures statements/oeis-a119012.lean (declaration OMA.S_oeis_a119012.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: S = sqrt(R) satisfies S^2 = R, so 2 R S' = R' S (rel2). The series F = (A + B S) / C
-- satisfies C F = A + B S (rel1). Writing M(n) for the left side of the conjectured recurrence, an
-- explicit operator Q gives sum_i q_i(n) M(n + i) as a polynomial combination of shifted instances
-- of rel1 and rel2 (certQ, found by exact linear algebra), so M(n) = 0 follows by induction from the
-- first values, which are computed exactly from rel1 and rel2 (the leading q is nonzero there).

namespace OMA.P_oeis_a119012

open OMA.S_oeis_a119012 PowerSeries

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

theorem hRC : R = C (1 : ℚ) + C (-4 : ℚ) * X ^ 1 := by
  simp only [R, map_one, map_neg, map_ofNat]
  ring

theorem hDR : d⁄dX ℚ R = C (-4 : ℚ) := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  push_cast
  ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (-8 : ℚ) * X ^ 1 * d⁄dX ℚ S - (C (-4 : ℚ) * S) = 0 := by
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

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 2) S * ((m : ℚ) + 2)) + (-8 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((-4 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 1)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 1 - 1 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := ((-1 + 5 * X - 2 * X ^ 2 - 7 * X ^ 3 - 4 * X ^ 4 + (1 - 3 * X - 2 * X ^ 2 + X ^ 3) * S) * (8 - 24 * X - 30 * X ^ 2 - 8 * X ^ 3 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = coeff (n + 2) F := rfl

theorem hF : F * (8 - 24 * X - 30 * X ^ 2 - 8 * X ^ 3 : ℚ⟦X⟧) = -1 + 5 * X - 2 * X ^ 2 - 7 * X ^ 3 - 4 * X ^ 4 + (1 - 3 * X - 2 * X ^ 2 + X ^ 3) * S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (8 - 24 * X - 30 * X ^ 2 - 8 * X ^ 3 : ℚ⟦X⟧) = C (8 : ℚ) + C (-24 : ℚ) * X ^ 1 + C (-30 : ℚ) * X ^ 2 + C (-8 : ℚ) * X ^ 3 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (8 : ℚ) * F + C (-24 : ℚ) * X ^ 1 * F + C (-30 : ℚ) * X ^ 2 * F + C (-8 : ℚ) * X ^ 3 * F - (C (1 : ℚ) * S + C (-3 : ℚ) * X ^ 1 * S + C (-2 : ℚ) * X ^ 2 * S + C (1 : ℚ) * X ^ 3 * S) - (C (-1 : ℚ) + C (5 : ℚ) * X ^ 1 + C (-2 : ℚ) * X ^ 2 + C (-7 : ℚ) * X ^ 3 + C (-4 : ℚ) * X ^ 4) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (8 : ℚ) * coeff (m + 5) F + (-24 : ℚ) * coeff (m + 4) F + (-30 : ℚ) * coeff (m + 3) F + (-8 : ℚ) * coeff (m + 2) F - ((1 : ℚ) * coeff (m + 5) S + (-3 : ℚ) * coeff (m + 4) S + (-2 : ℚ) * coeff (m + 3) S + (1 : ℚ) * coeff (m + 2) S) = 0 := by
  have h := congrArg (coeff (m + 5)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 5 - 1 = m + 4 from by omega, show m + 5 - 2 = m + 3 from by omega, show m + 5 - 3 = m + 2 from by omega] at h
  linear_combination h

theorem cz (c : ℚ) (j n : ℕ) (f : ℚ⟦X⟧) (h : n < j) : coeff n (C c * X ^ j * f) = 0 := by
  rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', if_neg (by omega), mul_zero]

theorem ccj (c : ℚ) (j n : ℕ) (h : n = j) : coeff n (C c * X ^ j) = c := by
  rw [coeff_C_mul_X_pow, if_pos h]

theorem cc0' (c : ℚ) : coeff 0 (C c : ℚ⟦X⟧) = c := by rw [coeff_C, if_pos rfl]

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

theorem hs0 : coeff 0 S = 1 := by rw [coeff_zero_eq_constantCoeff_apply, S_const]

theorem hs1 : coeff 1 S = (-2 : ℚ) := by
  have h := congrArg (coeff 0) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0] at h ⊢ <;> linarith

theorem hs2 : coeff 2 S = (-2 : ℚ) := by
  have h := congrArg (coeff 1) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1] at h ⊢ <;> linarith

theorem hs3 : coeff 3 S = (-4 : ℚ) := by
  have h := congrArg (coeff 2) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2] at h ⊢ <;> linarith

theorem hs4 : coeff 4 S = (-10 : ℚ) := by
  have h := congrArg (coeff 3) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3] at h ⊢ <;> linarith

theorem hs5 : coeff 5 S = (-28 : ℚ) := by
  have h := congrArg (coeff 4) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4] at h ⊢ <;> linarith

theorem hs6 : coeff 6 S = (-84 : ℚ) := by
  have h := congrArg (coeff 5) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5] at h ⊢ <;> linarith

theorem hs7 : coeff 7 S = (-264 : ℚ) := by
  have h := congrArg (coeff 6) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6] at h ⊢ <;> linarith

theorem hs8 : coeff 8 S = (-858 : ℚ) := by
  have h := congrArg (coeff 7) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7] at h ⊢ <;> linarith

theorem hf0 : coeff 0 F = (0 : ℚ) := by
  have h := congrArg (coeff 0) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8] at h ⊢ <;> linarith

theorem hf0c : constantCoeff F = (0 : ℚ) := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf0

theorem hf1 : coeff 1 F = (0 : ℚ) := by
  have h := congrArg (coeff 1) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf0c] at h ⊢ <;> linarith

theorem hf2 : coeff 2 F = (0 : ℚ) := by
  have h := congrArg (coeff 2) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf0c] at h ⊢ <;> linarith

theorem hf3 : coeff 3 F = (0 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem hf4 : coeff 4 F = (0 : ℚ) := by
  have h := congrArg (coeff 4) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf2, hf3, hf0c] at h ⊢ <;> linarith

theorem hf5 : coeff 5 F = (1 : ℚ) := by
  have h := congrArg (coeff 5) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf2, hf3, hf4, hf0c] at h ⊢ <;> linarith

theorem hf6 : coeff 6 F = (5 : ℚ) := by
  have h := congrArg (coeff 6) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf2, hf3, hf4, hf5, hf0c] at h ⊢ <;> linarith

theorem hf7 : coeff 7 F = (23 : ℚ) := by
  have h := congrArg (coeff 7) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf0c] at h ⊢ <;> linarith

theorem hf8 : coeff 8 F = (98 : ℚ) := by
  have h := congrArg (coeff 8) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (0 : ℚ) := by rw [a_eq]; exact hf2

theorem ha1 : a 1 = (0 : ℚ) := by rw [a_eq]; exact hf3

theorem ha2 : a 2 = (0 : ℚ) := by rw [a_eq]; exact hf4

theorem ha3 : a 3 = (1 : ℚ) := by rw [a_eq]; exact hf5

theorem ha4 : a 4 = (5 : ℚ) := by rw [a_eq]; exact hf6

theorem ha5 : a 5 = (23 : ℚ) := by rw [a_eq]; exact hf7

theorem ha6 : a 6 = (98 : ℚ) := by rw [a_eq]; exact hf8

noncomputable def Mv (n : ℕ) : ℚ := (6 * (n : ℚ) ^ 3 - 10 * (n : ℚ) ^ 2 - 32 * (n : ℚ) + 24) * a n
      + (-21 * (n : ℚ) ^ 3 + 50 * (n : ℚ) ^ 2 - 13 * (n : ℚ) - 4) * a (n - 1)
      + (-12 * (n : ℚ) ^ 3 + 14 * (n : ℚ) ^ 2 - 2) * a (n - 2)

theorem base3 : Mv 3 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6]

theorem base4 : Mv 4 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6]

theorem base5 : Mv 5 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6]

theorem base6 : Mv 6 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6]

theorem certQ (k : ℕ) : ((-26144 / 87 : ℚ) + (-34134 / 203 : ℚ) * ((k : ℚ) + 3) ^ 1) * Mv (k + 3) + ((17522 / 87 : ℚ) + (-1800 / 7 : ℚ) * ((k : ℚ) + 3) ^ 1) * Mv (k + 4) + ((-15922 / 203 : ℚ) + (242019 / 1624 : ℚ) * ((k : ℚ) + 3) ^ 1) * Mv (k + 5) + ((-5465 / 1218 : ℚ) + (-15069 / 812 : ℚ) * ((k : ℚ) + 3) ^ 1) * Mv (k + 6) + ((8 / 3 : ℚ)) * Mv (k + 7) = 0 := by
  unfold Mv
  rw [show k + 3 - 1 = k + 2 from by omega, show k + 3 - 2 = k + 1 from by omega, show k + 4 - 1 = k + 3 from by omega, show k + 4 - 2 = k + 2 from by omega, show k + 5 - 1 = k + 4 from by omega, show k + 5 - 2 = k + 3 from by omega, show k + 6 - 1 = k + 5 from by omega, show k + 6 - 2 = k + 4 from by omega, show k + 7 - 1 = k + 6 from by omega, show k + 7 - 2 = k + 5 from by omega]
  simp only [a_eq]
  have r1_51 := rel1 (k + 1)
  have r1_52 := rel1 (k + 2)
  have r1_53 := rel1 (k + 3)
  have r1_54 := rel1 (k + 4)
  have r2_48 := rel2 (k + 2)
  have r2_49 := rel2 (k + 3)
  have r2_50 := rel2 (k + 4)
  have r2_51 := rel2 (k + 5)
  have r2_52 := rel2 (k + 6)
  have r2_53 := rel2 (k + 7)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_51 r1_52 r1_53 r1_54 r2_48 r2_49 r2_50 r2_51 r2_52 r2_53 ⊢
  push_cast at r1_51 r1_52 r1_53 r1_54 r2_48 r2_49 r2_50 r2_51 r2_52 r2_53 ⊢
  linear_combination ((-6536 / 87 : ℚ) + (-17067 / 406 : ℚ) * ((k : ℚ) + 3) ^ 1 + (45752 / 87 : ℚ) * ((k : ℚ) + 3) ^ 2 + (-313 / 2 : ℚ) * ((k : ℚ) + 3) ^ 3 + (-51201 / 203 : ℚ) * ((k : ℚ) + 3) ^ 4) * r1_51 + ((11438 / 87 : ℚ) + (-148495 / 696 : ℚ) * ((k : ℚ) + 3) ^ 1 + (-57193 / 812 : ℚ) * ((k : ℚ) + 3) ^ 2 + (720945 / 1624 : ℚ) * ((k : ℚ) + 3) ^ 3 + (24102 / 203 : ℚ) * ((k : ℚ) + 3) ^ 4) * r1_52 + ((-80 : ℚ) + (-48901 / 696 : ℚ) * ((k : ℚ) + 3) ^ 1 + (-624891 / 3248 : ℚ) * ((k : ℚ) + 3) ^ 2 + (-21606 / 203 : ℚ) * ((k : ℚ) + 3) ^ 3 + (-45207 / 3248 : ℚ) * ((k : ℚ) + 3) ^ 4) * r1_53 + ((40 : ℚ) + (176 / 3 : ℚ) * ((k : ℚ) + 3) ^ 1 + (62 / 3 : ℚ) * ((k : ℚ) + 3) ^ 2 + (2 : ℚ) * ((k : ℚ) + 3) ^ 3) * r1_54 + ((-1634 / 87 : ℚ) + (-234209 / 4872 : ℚ) * ((k : ℚ) + 3) ^ 1 + (28685 / 812 : ℚ) * ((k : ℚ) + 3) ^ 2 + (51201 / 1624 : ℚ) * ((k : ℚ) + 3) ^ 3) * r2_48 + ((-13889 / 174 : ℚ) + (3089567 / 19488 : ℚ) * ((k : ℚ) + 3) ^ 1 + (-139325 / 3248 : ℚ) * ((k : ℚ) + 3) ^ 2 + (-454815 / 6496 : ℚ) * ((k : ℚ) + 3) ^ 3) * r2_49 + ((-975 / 58 : ℚ) + (51329 / 4872 : ℚ) * ((k : ℚ) + 3) ^ 1 + (457531 / 3248 : ℚ) * ((k : ℚ) + 3) ^ 2 + (-261999 / 3248 : ℚ) * ((k : ℚ) + 3) ^ 3) * r2_50 + ((2935 / 348 : ℚ) + (-116245 / 2784 : ℚ) * ((k : ℚ) + 3) ^ 1 + (2341 / 812 : ℚ) * ((k : ℚ) + 3) ^ 2 + (340425 / 6496 : ℚ) * ((k : ℚ) + 3) ^ 3) * r2_51 + ((-8 : ℚ) + (-6625 / 1392 : ℚ) * ((k : ℚ) + 3) ^ 1 + (-113165 / 6496 : ℚ) * ((k : ℚ) + 3) ^ 2 + (-45207 / 6496 : ℚ) * ((k : ℚ) + 3) ^ 3) * r2_52 + ((10 / 3 : ℚ) + (13 / 3 : ℚ) * ((k : ℚ) + 3) ^ 1 + (1 : ℚ) * ((k : ℚ) + 3) ^ 2) * r2_53

theorem Mv_zero : ∀ n : ℕ, 3 ≤ n → Mv n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 7
    · interval_cases n
      · exact base3
      · exact base4
      · exact base5
      · exact base6
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 7 := ⟨n - 7, by omega⟩
      have hc := certQ k
      have h0 : Mv (k + 3) = 0 := ih _ (by omega) (by omega)
      have h1 : Mv (k + 4) = 0 := ih _ (by omega) (by omega)
      have h2 : Mv (k + 5) = 0 := ih _ (by omega) (by omega)
      have h3 : Mv (k + 6) = 0 := ih _ (by omega) (by omega)
      have hq : ((8 / 3 : ℚ)) ≠ 0 := by
        have e : ((8 / 3 : ℚ)) = (8 / 3 : ℚ) := by ring
        rw [e]
        positivity
      have hm : ((8 / 3 : ℚ)) * Mv (k + 7) = 0 := by linear_combination hc - ((-26144 / 87 : ℚ) + (-34134 / 203 : ℚ) * ((k : ℚ) + 3) ^ 1) * h0 - ((17522 / 87 : ℚ) + (-1800 / 7 : ℚ) * ((k : ℚ) + 3) ^ 1) * h1 - ((-15922 / 203 : ℚ) + (242019 / 1624 : ℚ) * ((k : ℚ) + 3) ^ 1) * h2 - ((-5465 / 1218 : ℚ) + (-15069 / 812 : ℚ) * ((k : ℚ) + 3) ^ 1) * h3
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem main' : ∀ n : ℕ, 3 ≤ n → (6 * (n : ℚ) ^ 3 - 10 * (n : ℚ) ^ 2 - 32 * (n : ℚ) + 24) * a n
      + (-21 * (n : ℚ) ^ 3 + 50 * (n : ℚ) ^ 2 - 13 * (n : ℚ) - 4) * a (n - 1)
      + (-12 * (n : ℚ) ^ 3 + 14 * (n : ℚ) ^ 2 - 2) * a (n - 2) = 0 := fun n hn => Mv_zero n hn

end OMA.P_oeis_a119012

theorem OMA.solution : type_of% @OMA.S_oeis_a119012.main := OMA.P_oeis_a119012.main'
