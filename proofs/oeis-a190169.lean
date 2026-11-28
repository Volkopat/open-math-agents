import OMAStatements.S_oeis_a190169
import Mathlib

-- Problem: A190169: Number of (1,0)-steps at levels 1,3,5,... in all peakless Motzkin paths of length n.
-- Upstream: formal-conjectures statements/oeis-a190169.lean (declaration OMA.S_oeis_a190169.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: S = sqrt(R) satisfies S^2 = R, so 2 R S' = R' S (rel2). The series F = (A + B S) / C
-- satisfies C F = A + B S (rel1). Writing M(n) for the left side of the conjectured recurrence, an
-- explicit operator Q gives sum_i q_i(n) M(n + i) as a polynomial combination of shifted instances
-- of rel1 and rel2 (certQ, found by exact linear algebra), so M(n) = 0 follows by induction from the
-- first values, which are computed exactly from rel1 and rel2 (the leading q is nonzero there).

namespace OMA.P_oeis_a190169

open OMA.S_oeis_a190169 PowerSeries

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

theorem hRC : R = C (1 : ℚ) + C (-2 : ℚ) * X ^ 1 + C (-1 : ℚ) * X ^ 2 + C (-2 : ℚ) * X ^ 3 + C (1 : ℚ) * X ^ 4 := by
  simp only [R, map_one, map_neg, map_ofNat]
  ring

theorem hDR : d⁄dX ℚ R = C (-2 : ℚ) + C (-2 : ℚ) * X ^ 1 + C (-6 : ℚ) * X ^ 2 + C (4 : ℚ) * X ^ 3 := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  push_cast
  ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (-4 : ℚ) * X ^ 1 * d⁄dX ℚ S + C (-2 : ℚ) * X ^ 2 * d⁄dX ℚ S + C (-4 : ℚ) * X ^ 3 * d⁄dX ℚ S + C (2 : ℚ) * X ^ 4 * d⁄dX ℚ S - (C (-2 : ℚ) * S + C (-2 : ℚ) * X ^ 1 * S + C (-6 : ℚ) * X ^ 2 * S + C (4 : ℚ) * X ^ 3 * S) = 0 := by
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

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 5) S * ((m : ℚ) + 5)) + (-4 : ℚ) * (coeff (m + 4) S * ((m : ℚ) + 4)) + (-2 : ℚ) * (coeff (m + 3) S * ((m : ℚ) + 3)) + (-4 : ℚ) * (coeff (m + 2) S * ((m : ℚ) + 2)) + (2 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((-2 : ℚ) * coeff (m + 4) S + (-2 : ℚ) * coeff (m + 3) S + (-6 : ℚ) * coeff (m + 2) S + (4 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 4)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 4 - 1 = m + 3 from by omega, show m + 4 - 2 = m + 2 from by omega, show m + 4 - 3 = m + 1 from by omega, show m + 4 - 4 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := ((-1 + 3 * X - 2 * X ^ 2 + 3 * X ^ 3 - 2 * X ^ 4 + 3 * X ^ 5 - X ^ 6 + (1 - 2 * X + X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) * (2 - 6 * X + 4 * X ^ 2 - 6 * X ^ 3 + 4 * X ^ 4 - 6 * X ^ 5 + 2 * X ^ 6 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = coeff (n + 1) F := rfl

theorem hF : F * (2 - 6 * X + 4 * X ^ 2 - 6 * X ^ 3 + 4 * X ^ 4 - 6 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) = -1 + 3 * X - 2 * X ^ 2 + 3 * X ^ 3 - 2 * X ^ 4 + 3 * X ^ 5 - X ^ 6 + (1 - 2 * X + X ^ 2 - 2 * X ^ 3 + X ^ 4) * S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (2 - 6 * X + 4 * X ^ 2 - 6 * X ^ 3 + 4 * X ^ 4 - 6 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) = C (2 : ℚ) + C (-6 : ℚ) * X ^ 1 + C (4 : ℚ) * X ^ 2 + C (-6 : ℚ) * X ^ 3 + C (4 : ℚ) * X ^ 4 + C (-6 : ℚ) * X ^ 5 + C (2 : ℚ) * X ^ 6 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (2 : ℚ) * F + C (-6 : ℚ) * X ^ 1 * F + C (4 : ℚ) * X ^ 2 * F + C (-6 : ℚ) * X ^ 3 * F + C (4 : ℚ) * X ^ 4 * F + C (-6 : ℚ) * X ^ 5 * F + C (2 : ℚ) * X ^ 6 * F - (C (1 : ℚ) * S + C (-2 : ℚ) * X ^ 1 * S + C (1 : ℚ) * X ^ 2 * S + C (-2 : ℚ) * X ^ 3 * S + C (1 : ℚ) * X ^ 4 * S) - (C (-1 : ℚ) + C (3 : ℚ) * X ^ 1 + C (-2 : ℚ) * X ^ 2 + C (3 : ℚ) * X ^ 3 + C (-2 : ℚ) * X ^ 4 + C (3 : ℚ) * X ^ 5 + C (-1 : ℚ) * X ^ 6) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (2 : ℚ) * coeff (m + 7) F + (-6 : ℚ) * coeff (m + 6) F + (4 : ℚ) * coeff (m + 5) F + (-6 : ℚ) * coeff (m + 4) F + (4 : ℚ) * coeff (m + 3) F + (-6 : ℚ) * coeff (m + 2) F + (2 : ℚ) * coeff (m + 1) F - ((1 : ℚ) * coeff (m + 7) S + (-2 : ℚ) * coeff (m + 6) S + (1 : ℚ) * coeff (m + 5) S + (-2 : ℚ) * coeff (m + 4) S + (1 : ℚ) * coeff (m + 3) S) = 0 := by
  have h := congrArg (coeff (m + 7)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 7 - 1 = m + 6 from by omega, show m + 7 - 2 = m + 5 from by omega, show m + 7 - 3 = m + 4 from by omega, show m + 7 - 4 = m + 3 from by omega, show m + 7 - 5 = m + 2 from by omega, show m + 7 - 6 = m + 1 from by omega] at h
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

theorem hs1 : coeff 1 S = (-1 : ℚ) := by
  have h := congrArg (coeff 0) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0] at h ⊢ <;> linarith

theorem hs2 : coeff 2 S = (-1 : ℚ) := by
  have h := congrArg (coeff 1) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1] at h ⊢ <;> linarith

theorem hs3 : coeff 3 S = (-2 : ℚ) := by
  have h := congrArg (coeff 2) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2] at h ⊢ <;> linarith

theorem hs4 : coeff 4 S = (-2 : ℚ) := by
  have h := congrArg (coeff 3) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3] at h ⊢ <;> linarith

theorem hs5 : coeff 5 S = (-4 : ℚ) := by
  have h := congrArg (coeff 4) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4] at h ⊢ <;> linarith

theorem hs6 : coeff 6 S = (-8 : ℚ) := by
  have h := congrArg (coeff 5) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5] at h ⊢ <;> linarith

theorem hs7 : coeff 7 S = (-16 : ℚ) := by
  have h := congrArg (coeff 6) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6] at h ⊢ <;> linarith

theorem hs8 : coeff 8 S = (-34 : ℚ) := by
  have h := congrArg (coeff 7) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7] at h ⊢ <;> linarith

theorem hs9 : coeff 9 S = (-74 : ℚ) := by
  have h := congrArg (coeff 8) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8] at h ⊢ <;> linarith

theorem hs10 : coeff 10 S = (-164 : ℚ) := by
  have h := congrArg (coeff 9) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9] at h ⊢ <;> linarith

theorem hs11 : coeff 11 S = (-370 : ℚ) := by
  have h := congrArg (coeff 10) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10] at h ⊢ <;> linarith

theorem hs12 : coeff 12 S = (-846 : ℚ) := by
  have h := congrArg (coeff 11) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11] at h ⊢ <;> linarith

theorem hf0 : coeff 0 F = (0 : ℚ) := by
  have h := congrArg (coeff 0) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12] at h ⊢ <;> linarith

theorem hf0c : constantCoeff F = (0 : ℚ) := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf0

theorem hf1 : coeff 1 F = (0 : ℚ) := by
  have h := congrArg (coeff 1) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hf0, hf0c] at h ⊢ <;> linarith

theorem hf2 : coeff 2 F = (0 : ℚ) := by
  have h := congrArg (coeff 2) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hf0, hf1, hf0c] at h ⊢ <;> linarith

theorem hf3 : coeff 3 F = (0 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem hf4 : coeff 4 F = (1 : ℚ) := by
  have h := congrArg (coeff 4) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hf0, hf1, hf2, hf3, hf0c] at h ⊢ <;> linarith

theorem hf5 : coeff 5 F = (4 : ℚ) := by
  have h := congrArg (coeff 5) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hf0, hf1, hf2, hf3, hf4, hf0c] at h ⊢ <;> linarith

theorem hf6 : coeff 6 F = (10 : ℚ) := by
  have h := congrArg (coeff 6) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hf0, hf1, hf2, hf3, hf4, hf5, hf0c] at h ⊢ <;> linarith

theorem hf7 : coeff 7 F = (24 : ℚ) := by
  have h := congrArg (coeff 7) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf0c] at h ⊢ <;> linarith

theorem hf8 : coeff 8 F = (60 : ℚ) := by
  have h := congrArg (coeff 8) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf0c] at h ⊢ <;> linarith

theorem hf9 : coeff 9 F = (152 : ℚ) := by
  have h := congrArg (coeff 9) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf0c] at h ⊢ <;> linarith

theorem hf10 : coeff 10 F = (386 : ℚ) := by
  have h := congrArg (coeff 10) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf0c] at h ⊢ <;> linarith

theorem hf11 : coeff 11 F = (980 : ℚ) := by
  have h := congrArg (coeff 11) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf0c] at h ⊢ <;> linarith

theorem hf12 : coeff 12 F = (2488 : ℚ) := by
  have h := congrArg (coeff 12) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (0 : ℚ) := by rw [a_eq]; exact hf1

theorem ha1 : a 1 = (0 : ℚ) := by rw [a_eq]; exact hf2

theorem ha2 : a 2 = (0 : ℚ) := by rw [a_eq]; exact hf3

theorem ha3 : a 3 = (1 : ℚ) := by rw [a_eq]; exact hf4

theorem ha4 : a 4 = (4 : ℚ) := by rw [a_eq]; exact hf5

theorem ha5 : a 5 = (10 : ℚ) := by rw [a_eq]; exact hf6

theorem ha6 : a 6 = (24 : ℚ) := by rw [a_eq]; exact hf7

theorem ha7 : a 7 = (60 : ℚ) := by rw [a_eq]; exact hf8

theorem ha8 : a 8 = (152 : ℚ) := by rw [a_eq]; exact hf9

theorem ha9 : a 9 = (386 : ℚ) := by rw [a_eq]; exact hf10

theorem ha10 : a 10 = (980 : ℚ) := by rw [a_eq]; exact hf11

theorem ha11 : a 11 = (2488 : ℚ) := by rw [a_eq]; exact hf12

noncomputable def Mv (n : ℕ) : ℚ := (-(n : ℚ) ^ 2 + 1) * a n + (-(n : ℚ) ^ 2 + 19 * (n : ℚ)) * a (n - 1)
      + (14 * (n : ℚ) ^ 2 - 94 * (n : ℚ) + 80) * a (n - 2)
      + (-17 * (n : ℚ) ^ 2 + 131 * (n : ℚ) - 194) * a (n - 3)
      + (18 * (n : ℚ) ^ 2 - 128 * (n : ℚ) + 238) * a (n - 4)
      + (-17 * (n : ℚ) ^ 2 + 153 * (n : ℚ) - 340) * a (n - 5)
      + (19 * (n : ℚ) ^ 2 - 154 * (n : ℚ) + 295) * a (n - 6)
      + (-16 * (n : ℚ) ^ 2 + 138 * (n : ℚ) - 252) * a (n - 7)
      + (4 * (n : ℚ) ^ 2 - 38 * (n : ℚ) + 70) * a (n - 8)

theorem base8 : Mv 8 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11]

theorem base9 : Mv 9 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11]

theorem base10 : Mv 10 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11]

theorem base11 : Mv 11 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11]

theorem certQ (k : ℕ) : ((-4020 / 217 : ℚ) + (15144 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-14332 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (3256 / 217 : ℚ) * ((k : ℚ) + 8) ^ 3 + (-4 : ℚ) * ((k : ℚ) + 8) ^ 4) * Mv (k + 8) + ((46080 / 217 : ℚ) + (-11136 / 31 : ℚ) * ((k : ℚ) + 8) ^ 1 + (40984 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (-8248 / 217 : ℚ) * ((k : ℚ) + 8) ^ 3 + (8 : ℚ) * ((k : ℚ) + 8) ^ 4) * Mv (k + 9) + ((-6780 / 217 : ℚ) + (2448 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (5108 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (-4992 / 217 : ℚ) * ((k : ℚ) + 8) ^ 3 + (4 : ℚ) * ((k : ℚ) + 8) ^ 4) * Mv (k + 10) + ((39264 / 217 : ℚ) + (-82080 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (7720 / 31 : ℚ) * ((k : ℚ) + 8) ^ 2 + (-11720 / 217 : ℚ) * ((k : ℚ) + 8) ^ 3 + (8 : ℚ) * ((k : ℚ) + 8) ^ 4) * Mv (k + 11) + ((-37620 / 217 : ℚ) + (57048 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-29308 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (6728 / 217 : ℚ) * ((k : ℚ) + 8) ^ 3 + (-4 : ℚ) * ((k : ℚ) + 8) ^ 4) * Mv (k + 12) = 0 := by
  unfold Mv
  rw [show k + 8 - 1 = k + 7 from by omega, show k + 8 - 2 = k + 6 from by omega, show k + 8 - 3 = k + 5 from by omega, show k + 8 - 4 = k + 4 from by omega, show k + 8 - 5 = k + 3 from by omega, show k + 8 - 6 = k + 2 from by omega, show k + 8 - 7 = k + 1 from by omega, show k + 8 - 8 = k from by omega, show k + 9 - 1 = k + 8 from by omega, show k + 9 - 2 = k + 7 from by omega, show k + 9 - 3 = k + 6 from by omega, show k + 9 - 4 = k + 5 from by omega, show k + 9 - 5 = k + 4 from by omega, show k + 9 - 6 = k + 3 from by omega, show k + 9 - 7 = k + 2 from by omega, show k + 9 - 8 = k + 1 from by omega, show k + 10 - 1 = k + 9 from by omega, show k + 10 - 2 = k + 8 from by omega, show k + 10 - 3 = k + 7 from by omega, show k + 10 - 4 = k + 6 from by omega, show k + 10 - 5 = k + 5 from by omega, show k + 10 - 6 = k + 4 from by omega, show k + 10 - 7 = k + 3 from by omega, show k + 10 - 8 = k + 2 from by omega, show k + 11 - 1 = k + 10 from by omega, show k + 11 - 2 = k + 9 from by omega, show k + 11 - 3 = k + 8 from by omega, show k + 11 - 4 = k + 7 from by omega, show k + 11 - 5 = k + 6 from by omega, show k + 11 - 6 = k + 5 from by omega, show k + 11 - 7 = k + 4 from by omega, show k + 11 - 8 = k + 3 from by omega, show k + 12 - 1 = k + 11 from by omega, show k + 12 - 2 = k + 10 from by omega, show k + 12 - 3 = k + 9 from by omega, show k + 12 - 4 = k + 8 from by omega, show k + 12 - 5 = k + 7 from by omega, show k + 12 - 6 = k + 6 from by omega, show k + 12 - 7 = k + 5 from by omega, show k + 12 - 8 = k + 4 from by omega]
  simp only [a_eq]
  have r1_48 := rel1 (k)
  have r1_49 := rel1 (k + 1)
  have r1_50 := rel1 (k + 2)
  have r1_51 := rel1 (k + 3)
  have r1_52 := rel1 (k + 4)
  have r1_53 := rel1 (k + 5)
  have r1_54 := rel1 (k + 6)
  have r2_47 := rel2 (k + 2)
  have r2_48 := rel2 (k + 3)
  have r2_49 := rel2 (k + 4)
  have r2_50 := rel2 (k + 5)
  have r2_51 := rel2 (k + 6)
  have r2_52 := rel2 (k + 7)
  have r2_53 := rel2 (k + 8)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_48 r1_49 r1_50 r1_51 r1_52 r1_53 r1_54 r2_47 r2_48 r2_49 r2_50 r2_51 r2_52 r2_53 ⊢
  push_cast at r1_48 r1_49 r1_50 r1_51 r1_52 r1_53 r1_54 r2_47 r2_48 r2_49 r2_50 r2_51 r2_52 r2_53 ⊢
  linear_combination ((-20100 / 31 : ℚ) + (606420 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-797396 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (59508 / 31 : ℚ) * ((k : ℚ) + 8) ^ 3 + (-120908 / 217 : ℚ) * ((k : ℚ) + 8) ^ 4 + (23004 / 217 : ℚ) * ((k : ℚ) + 8) ^ 5 + (-8 : ℚ) * ((k : ℚ) + 8) ^ 6) * r1_48 + ((913860 / 217 : ℚ) + (-2460600 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (2489892 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (-169968 / 31 : ℚ) * ((k : ℚ) + 8) ^ 3 + (322900 / 217 : ℚ) * ((k : ℚ) + 8) ^ 4 + (-59464 / 217 : ℚ) * ((k : ℚ) + 8) ^ 5 + (24 : ℚ) * ((k : ℚ) + 8) ^ 6) * r1_49 + ((-599070 / 217 : ℚ) + (1544580 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-1432784 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (82984 / 31 : ℚ) * ((k : ℚ) + 8) ^ 3 + (-112768 / 217 : ℚ) * ((k : ℚ) + 8) ^ 4 + (11828 / 217 : ℚ) * ((k : ℚ) + 8) ^ 5 + (-6 : ℚ) * ((k : ℚ) + 8) ^ 6) * r1_50 + ((301314 / 217 : ℚ) + (-662958 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (676082 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (-58646 / 31 : ℚ) * ((k : ℚ) + 8) ^ 3 + (118498 / 217 : ℚ) * ((k : ℚ) + 8) ^ 4 + (-13238 / 217 : ℚ) * ((k : ℚ) + 8) ^ 5 + (4 : ℚ) * ((k : ℚ) + 8) ^ 6) * r1_51 + ((424908 / 217 : ℚ) + (-893610 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (504162 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (81926 / 217 : ℚ) * ((k : ℚ) + 8) ^ 3 + (-128558 / 217 : ℚ) * ((k : ℚ) + 8) ^ 4 + (35486 / 217 : ℚ) * ((k : ℚ) + 8) ^ 5 + (-26 : ℚ) * ((k : ℚ) + 8) ^ 6) * r1_52 + ((-439206 / 217 : ℚ) + (882918 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-504934 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (52666 / 217 : ℚ) * ((k : ℚ) + 8) ^ 3 + (9570 / 217 : ℚ) * ((k : ℚ) + 8) ^ 4 + (-7162 / 217 : ℚ) * ((k : ℚ) + 8) ^ 5 + (4 : ℚ) * ((k : ℚ) + 8) ^ 6) * r1_53 + ((282150 / 217 : ℚ) + (-277380 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (10428 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (5464 / 31 : ℚ) * ((k : ℚ) + 8) ^ 3 + (-5748 / 217 : ℚ) * ((k : ℚ) + 8) ^ 4 + (108 / 217 : ℚ) * ((k : ℚ) + 8) ^ 5 + (2 : ℚ) * ((k : ℚ) + 8) ^ 6) * r1_54 + ((10050 / 217 : ℚ) + (-41880 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (7282 / 31 : ℚ) * ((k : ℚ) + 8) ^ 2 + (-22472 / 217 : ℚ) * ((k : ℚ) + 8) ^ 3 + (5426 / 217 : ℚ) * ((k : ℚ) + 8) ^ 4 + (-4 : ℚ) * ((k : ℚ) + 8) ^ 5) * r2_47 + ((-81180 / 217 : ℚ) + (212460 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-28224 / 31 : ℚ) * ((k : ℚ) + 8) ^ 2 + (77456 / 217 : ℚ) * ((k : ℚ) + 8) ^ 3 + (-16712 / 217 : ℚ) * ((k : ℚ) + 8) ^ 4 + (12 : ℚ) * ((k : ℚ) + 8) ^ 5) * r2_48 + ((118665 / 217 : ℚ) + (-43443 / 31 : ℚ) * ((k : ℚ) + 8) ^ 1 + (268725 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (-93679 / 217 : ℚ) * ((k : ℚ) + 8) ^ 3 + (16983 / 217 : ℚ) * ((k : ℚ) + 8) ^ 4 + (-11 : ℚ) * ((k : ℚ) + 8) ^ 5) * r2_49 + ((-177498 / 217 : ℚ) + (414576 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-343962 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (17002 / 31 : ℚ) * ((k : ℚ) + 8) ^ 3 + (-21160 / 217 : ℚ) * ((k : ℚ) + 8) ^ 4 + (10 : ℚ) * ((k : ℚ) + 8) ^ 5) * r2_50 + ((156285 / 217 : ℚ) + (-347763 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (41111 / 31 : ℚ) * ((k : ℚ) + 8) ^ 2 + (-15445 / 31 : ℚ) * ((k : ℚ) + 8) ^ 3 + (21757 / 217 : ℚ) * ((k : ℚ) + 8) ^ 4 + (-11 : ℚ) * ((k : ℚ) + 8) ^ 5) * r2_51 + ((-10866 / 31 : ℚ) + (154416 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-107510 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (31750 / 217 : ℚ) * ((k : ℚ) + 8) ^ 3 + (-5968 / 217 : ℚ) * ((k : ℚ) + 8) ^ 4 + (2 : ℚ) * ((k : ℚ) + 8) ^ 5) * r2_52 + ((28215 / 217 : ℚ) + (-33381 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (249 / 7 : ℚ) * ((k : ℚ) + 8) ^ 2 + (2281 / 217 : ℚ) * ((k : ℚ) + 8) ^ 3 + (-1031 / 217 : ℚ) * ((k : ℚ) + 8) ^ 4 + (1 : ℚ) * ((k : ℚ) + 8) ^ 5) * r2_53

theorem Mv_zero : ∀ n : ℕ, 8 ≤ n → Mv n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 12
    · interval_cases n
      · exact base8
      · exact base9
      · exact base10
      · exact base11
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 12 := ⟨n - 12, by omega⟩
      have hc := certQ k
      have h0 : Mv (k + 8) = 0 := ih _ (by omega) (by omega)
      have h1 : Mv (k + 9) = 0 := ih _ (by omega) (by omega)
      have h2 : Mv (k + 10) = 0 := ih _ (by omega) (by omega)
      have h3 : Mv (k + 11) = 0 := ih _ (by omega) (by omega)
      have hq : ((-37620 / 217 : ℚ) + (57048 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-29308 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (6728 / 217 : ℚ) * ((k : ℚ) + 8) ^ 3 + (-4 : ℚ) * ((k : ℚ) + 8) ^ 4) ≠ 0 := by
        have e : ((-37620 / 217 : ℚ) + (57048 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-29308 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (6728 / 217 : ℚ) * ((k : ℚ) + 8) ^ 3 + (-4 : ℚ) * ((k : ℚ) + 8) ^ 4) = -((1567540 / 217 : ℚ) + (897768 / 217 : ℚ) * (k : ℚ) ^ 1 + (201148 / 217 : ℚ) * (k : ℚ) ^ 2 + (21048 / 217 : ℚ) * (k : ℚ) ^ 3 + (4 : ℚ) * (k : ℚ) ^ 4) := by ring
        rw [e, neg_ne_zero]
        positivity
      have hm : ((-37620 / 217 : ℚ) + (57048 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-29308 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (6728 / 217 : ℚ) * ((k : ℚ) + 8) ^ 3 + (-4 : ℚ) * ((k : ℚ) + 8) ^ 4) * Mv (k + 12) = 0 := by linear_combination hc - ((-4020 / 217 : ℚ) + (15144 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-14332 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (3256 / 217 : ℚ) * ((k : ℚ) + 8) ^ 3 + (-4 : ℚ) * ((k : ℚ) + 8) ^ 4) * h0 - ((46080 / 217 : ℚ) + (-11136 / 31 : ℚ) * ((k : ℚ) + 8) ^ 1 + (40984 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (-8248 / 217 : ℚ) * ((k : ℚ) + 8) ^ 3 + (8 : ℚ) * ((k : ℚ) + 8) ^ 4) * h1 - ((-6780 / 217 : ℚ) + (2448 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (5108 / 217 : ℚ) * ((k : ℚ) + 8) ^ 2 + (-4992 / 217 : ℚ) * ((k : ℚ) + 8) ^ 3 + (4 : ℚ) * ((k : ℚ) + 8) ^ 4) * h2 - ((39264 / 217 : ℚ) + (-82080 / 217 : ℚ) * ((k : ℚ) + 8) ^ 1 + (7720 / 31 : ℚ) * ((k : ℚ) + 8) ^ 2 + (-11720 / 217 : ℚ) * ((k : ℚ) + 8) ^ 3 + (8 : ℚ) * ((k : ℚ) + 8) ^ 4) * h3
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem main' : ∀ n : ℕ, 8 ≤ n → (-(n : ℚ) ^ 2 + 1) * a n + (-(n : ℚ) ^ 2 + 19 * (n : ℚ)) * a (n - 1)
      + (14 * (n : ℚ) ^ 2 - 94 * (n : ℚ) + 80) * a (n - 2)
      + (-17 * (n : ℚ) ^ 2 + 131 * (n : ℚ) - 194) * a (n - 3)
      + (18 * (n : ℚ) ^ 2 - 128 * (n : ℚ) + 238) * a (n - 4)
      + (-17 * (n : ℚ) ^ 2 + 153 * (n : ℚ) - 340) * a (n - 5)
      + (19 * (n : ℚ) ^ 2 - 154 * (n : ℚ) + 295) * a (n - 6)
      + (-16 * (n : ℚ) ^ 2 + 138 * (n : ℚ) - 252) * a (n - 7)
      + (4 * (n : ℚ) ^ 2 - 38 * (n : ℚ) + 70) * a (n - 8) = 0 := fun n hn => Mv_zero n hn

end OMA.P_oeis_a190169

theorem OMA.solution : type_of% @OMA.S_oeis_a190169.main := OMA.P_oeis_a190169.main'
