import OMAStatements.S_oeis_a166290
import Mathlib

-- Problem: A166290: Number of UDUD's in all Dyck paths of semilength n with no UUU's and no DDD's (U=(1,1), D=(1,-1)).
-- Upstream: formal-conjectures statements/oeis-a166290.lean (declaration OMA.S_oeis_a166290.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: S = sqrt(R) satisfies S^2 = R, so 2 R S' = R' S (rel2). The series F = (A + B S) / C
-- satisfies C F = A + B S (rel1). Writing M(n) for the left side of the conjectured recurrence, an
-- explicit operator Q gives sum_i q_i(n) M(n + i) as a polynomial combination of shifted instances
-- of rel1 and rel2 (certQ, found by exact linear algebra), so M(n) = 0 follows by induction from the
-- first values, which are computed exactly from rel1 and rel2 (the leading q is nonzero there).

namespace OMA.P_oeis_a166290

open OMA.S_oeis_a166290 PowerSeries

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

noncomputable def F : ℚ⟦X⟧ := ((-2 + 5 * X + X ^ 2 + X ^ 3 - 5 * X ^ 4 - X ^ 5 + X ^ 6 + (2 - 3 * X - 2 * X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) * (2 - 4 * X - 2 * X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = coeff (n + 2) F := rfl

theorem hF : F * (2 - 4 * X - 2 * X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 : ℚ⟦X⟧) = -2 + 5 * X + X ^ 2 + X ^ 3 - 5 * X ^ 4 - X ^ 5 + X ^ 6 + (2 - 3 * X - 2 * X ^ 2 - 2 * X ^ 3 + X ^ 4) * S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (2 - 4 * X - 2 * X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 : ℚ⟦X⟧) = C (2 : ℚ) + C (-4 : ℚ) * X ^ 1 + C (-2 : ℚ) * X ^ 2 + C (-4 : ℚ) * X ^ 3 + C (2 : ℚ) * X ^ 4 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (2 : ℚ) * F + C (-4 : ℚ) * X ^ 1 * F + C (-2 : ℚ) * X ^ 2 * F + C (-4 : ℚ) * X ^ 3 * F + C (2 : ℚ) * X ^ 4 * F - (C (2 : ℚ) * S + C (-3 : ℚ) * X ^ 1 * S + C (-2 : ℚ) * X ^ 2 * S + C (-2 : ℚ) * X ^ 3 * S + C (1 : ℚ) * X ^ 4 * S) - (C (-2 : ℚ) + C (5 : ℚ) * X ^ 1 + C (1 : ℚ) * X ^ 2 + C (1 : ℚ) * X ^ 3 + C (-5 : ℚ) * X ^ 4 + C (-1 : ℚ) * X ^ 5 + C (1 : ℚ) * X ^ 6) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (2 : ℚ) * coeff (m + 7) F + (-4 : ℚ) * coeff (m + 6) F + (-2 : ℚ) * coeff (m + 5) F + (-4 : ℚ) * coeff (m + 4) F + (2 : ℚ) * coeff (m + 3) F - ((2 : ℚ) * coeff (m + 7) S + (-3 : ℚ) * coeff (m + 6) S + (-2 : ℚ) * coeff (m + 5) S + (-2 : ℚ) * coeff (m + 4) S + (1 : ℚ) * coeff (m + 3) S) = 0 := by
  have h := congrArg (coeff (m + 7)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 7 - 1 = m + 6 from by omega, show m + 7 - 2 = m + 5 from by omega, show m + 7 - 3 = m + 4 from by omega, show m + 7 - 4 = m + 3 from by omega] at h
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

theorem hs13 : coeff 13 S = (-1956 : ℚ) := by
  have h := congrArg (coeff 12) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12] at h ⊢ <;> linarith

theorem hs14 : coeff 14 S = (-4566 : ℚ) := by
  have h := congrArg (coeff 13) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13] at h ⊢ <;> linarith

theorem hs15 : coeff 15 S = (-10746 : ℚ) := by
  have h := congrArg (coeff 14) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14] at h ⊢ <;> linarith

theorem hs16 : coeff 16 S = (-25470 : ℚ) := by
  have h := congrArg (coeff 15) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15] at h ⊢ <;> linarith

theorem hs17 : coeff 17 S = (-60744 : ℚ) := by
  have h := congrArg (coeff 16) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16] at h ⊢ <;> linarith

theorem hs18 : coeff 18 S = (-145664 : ℚ) := by
  have h := congrArg (coeff 17) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17] at h ⊢ <;> linarith

theorem hs19 : coeff 19 S = (-351004 : ℚ) := by
  have h := congrArg (coeff 18) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18] at h ⊢ <;> linarith

theorem hs20 : coeff 20 S = (-849496 : ℚ) := by
  have h := congrArg (coeff 19) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19] at h ⊢ <;> linarith

theorem hs21 : coeff 21 S = (-2064008 : ℚ) := by
  have h := congrArg (coeff 20) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20] at h ⊢ <;> linarith

theorem hs22 : coeff 22 S = (-5032694 : ℚ) := by
  have h := congrArg (coeff 21) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21] at h ⊢ <;> linarith

theorem hs23 : coeff 23 S = (-12310882 : ℚ) := by
  have h := congrArg (coeff 22) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22] at h ⊢ <;> linarith

theorem hs24 : coeff 24 S = (-30203402 : ℚ) := by
  have h := congrArg (coeff 23) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23] at h ⊢ <;> linarith

theorem hs25 : coeff 25 S = (-74300944 : ℚ) := by
  have h := congrArg (coeff 24) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24] at h ⊢ <;> linarith

theorem hf0 : coeff 0 F = (0 : ℚ) := by
  have h := congrArg (coeff 0) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25] at h ⊢ <;> linarith

theorem hf0c : constantCoeff F = (0 : ℚ) := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf0

theorem hf1 : coeff 1 F = (0 : ℚ) := by
  have h := congrArg (coeff 1) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf0c] at h ⊢ <;> linarith

theorem hf2 : coeff 2 F = (0 : ℚ) := by
  have h := congrArg (coeff 2) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf0c] at h ⊢ <;> linarith

theorem hf3 : coeff 3 F = (0 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem hf4 : coeff 4 F = (1 : ℚ) := by
  have h := congrArg (coeff 4) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf0c] at h ⊢ <;> linarith

theorem hf5 : coeff 5 F = (3 : ℚ) := by
  have h := congrArg (coeff 5) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf0c] at h ⊢ <;> linarith

theorem hf6 : coeff 6 F = (9 : ℚ) := by
  have h := congrArg (coeff 6) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf0c] at h ⊢ <;> linarith

theorem hf7 : coeff 7 F = (24 : ℚ) := by
  have h := congrArg (coeff 7) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf0c] at h ⊢ <;> linarith

theorem hf8 : coeff 8 F = (63 : ℚ) := by
  have h := congrArg (coeff 8) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf0c] at h ⊢ <;> linarith

theorem hf9 : coeff 9 F = (164 : ℚ) := by
  have h := congrArg (coeff 9) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf0c] at h ⊢ <;> linarith

theorem hf10 : coeff 10 F = (423 : ℚ) := by
  have h := congrArg (coeff 10) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf0c] at h ⊢ <;> linarith

theorem hf11 : coeff 11 F = (1088 : ℚ) := by
  have h := congrArg (coeff 11) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf0c] at h ⊢ <;> linarith

theorem hf12 : coeff 12 F = (2794 : ℚ) := by
  have h := congrArg (coeff 12) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf0c] at h ⊢ <;> linarith

theorem hf13 : coeff 13 F = (7168 : ℚ) := by
  have h := congrArg (coeff 13) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf0c] at h ⊢ <;> linarith

theorem hf14 : coeff 14 F = (18385 : ℚ) := by
  have h := congrArg (coeff 14) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf0c] at h ⊢ <;> linarith

theorem hf15 : coeff 15 F = (47158 : ℚ) := by
  have h := congrArg (coeff 15) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf0c] at h ⊢ <;> linarith

theorem hf16 : coeff 16 F = (120991 : ℚ) := by
  have h := congrArg (coeff 16) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf0c] at h ⊢ <;> linarith

theorem hf17 : coeff 17 F = (310537 : ℚ) := by
  have h := congrArg (coeff 17) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16, hf0c] at h ⊢ <;> linarith

theorem hf18 : coeff 18 F = (797381 : ℚ) := by
  have h := congrArg (coeff 18) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16, hf17, hf0c] at h ⊢ <;> linarith

theorem hf19 : coeff 19 F = (2048456 : ℚ) := by
  have h := congrArg (coeff 19) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16, hf17, hf18, hf0c] at h ⊢ <;> linarith

theorem hf20 : coeff 20 F = (5265059 : ℚ) := by
  have h := congrArg (coeff 20) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16, hf17, hf18, hf19, hf0c] at h ⊢ <;> linarith

theorem hf21 : coeff 21 F = (13539331 : ℚ) := by
  have h := congrArg (coeff 21) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16, hf17, hf18, hf19, hf20, hf0c] at h ⊢ <;> linarith

theorem hf22 : coeff 22 F = (34834238 : ℚ) := by
  have h := congrArg (coeff 22) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16, hf17, hf18, hf19, hf20, hf21, hf0c] at h ⊢ <;> linarith

theorem hf23 : coeff 23 F = (89665630 : ℚ) := by
  have h := congrArg (coeff 23) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16, hf17, hf18, hf19, hf20, hf21, hf22, hf0c] at h ⊢ <;> linarith

theorem hf24 : coeff 24 F = (230913976 : ℚ) := by
  have h := congrArg (coeff 24) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16, hf17, hf18, hf19, hf20, hf21, hf22, hf23, hf0c] at h ⊢ <;> linarith

theorem hf25 : coeff 25 F = (594938458 : ℚ) := by
  have h := congrArg (coeff 25) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hs25, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16, hf17, hf18, hf19, hf20, hf21, hf22, hf23, hf24, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (0 : ℚ) := by rw [a_eq]; exact hf2

theorem ha1 : a 1 = (0 : ℚ) := by rw [a_eq]; exact hf3

theorem ha2 : a 2 = (1 : ℚ) := by rw [a_eq]; exact hf4

theorem ha3 : a 3 = (3 : ℚ) := by rw [a_eq]; exact hf5

theorem ha4 : a 4 = (9 : ℚ) := by rw [a_eq]; exact hf6

theorem ha5 : a 5 = (24 : ℚ) := by rw [a_eq]; exact hf7

theorem ha6 : a 6 = (63 : ℚ) := by rw [a_eq]; exact hf8

theorem ha7 : a 7 = (164 : ℚ) := by rw [a_eq]; exact hf9

theorem ha8 : a 8 = (423 : ℚ) := by rw [a_eq]; exact hf10

theorem ha9 : a 9 = (1088 : ℚ) := by rw [a_eq]; exact hf11

theorem ha10 : a 10 = (2794 : ℚ) := by rw [a_eq]; exact hf12

theorem ha11 : a 11 = (7168 : ℚ) := by rw [a_eq]; exact hf13

theorem ha12 : a 12 = (18385 : ℚ) := by rw [a_eq]; exact hf14

theorem ha13 : a 13 = (47158 : ℚ) := by rw [a_eq]; exact hf15

theorem ha14 : a 14 = (120991 : ℚ) := by rw [a_eq]; exact hf16

theorem ha15 : a 15 = (310537 : ℚ) := by rw [a_eq]; exact hf17

theorem ha16 : a 16 = (797381 : ℚ) := by rw [a_eq]; exact hf18

theorem ha17 : a 17 = (2048456 : ℚ) := by rw [a_eq]; exact hf19

theorem ha18 : a 18 = (5265059 : ℚ) := by rw [a_eq]; exact hf20

theorem ha19 : a 19 = (13539331 : ℚ) := by rw [a_eq]; exact hf21

theorem ha20 : a 20 = (34834238 : ℚ) := by rw [a_eq]; exact hf22

theorem ha21 : a 21 = (89665630 : ℚ) := by rw [a_eq]; exact hf23

theorem ha22 : a 22 = (230913976 : ℚ) := by rw [a_eq]; exact hf24

theorem ha23 : a 23 = (594938458 : ℚ) := by rw [a_eq]; exact hf25

noncomputable def Mv (n : ℕ) : ℚ := (-60283 * (n : ℚ) ^ 2 + 198489 * (n : ℚ) + 638110) * a n
      + (-60283 * (n : ℚ) ^ 2 - 13090 * (n : ℚ) + 236862) * a (n - 1)
      + (588710 * (n : ℚ) ^ 2 - 2858167 * (n : ℚ) + 437486) * a (n - 2)
      + (-32043 * (n : ℚ) ^ 2 + 2024290 * (n : ℚ) - 2826488) * a (n - 3)
      + (134686 * (n : ℚ) ^ 2 + 585099 * (n : ℚ) - 3417942) * a (n - 4)
      + (-514307 * (n : ℚ) ^ 2 + 4366464 * (n : ℚ) - 8945002) * a (n - 5)
      + (166729 * (n : ℚ) ^ 2 - 1863662 * (n : ℚ) + 5179728) * a (n - 6)

theorem base6 : Mv 6 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23]

theorem base7 : Mv 7 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23]

theorem base8 : Mv 8 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23]

theorem base9 : Mv 9 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23]

theorem base10 : Mv 10 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23]

theorem base11 : Mv 11 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23]

theorem base12 : Mv 12 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23]

theorem base13 : Mv 13 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23]

theorem base14 : Mv 14 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23]

theorem base15 : Mv 15 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23]

theorem base16 : Mv 16 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23]

theorem base17 : Mv 17 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23]

theorem base18 : Mv 18 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23]

theorem base19 : Mv 19 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23]

theorem base20 : Mv 20 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23]

theorem base21 : Mv 21 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23]

theorem base22 : Mv 22 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23]

theorem base23 : Mv 23 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23]

theorem certQ (k : ℕ) : ((-6756197072397230754360163 / 60055345667701483606574680 : ℚ) + (481534495482865755289976 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 1 + (-96215384081671794777748 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 2 + (1698562877636979525520 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 3 + (-2 / 60283 : ℚ) * ((k : ℚ) + 20) ^ 4) * Mv (k + 20) + ((6771540475103260573876517 / 30027672833850741803287340 : ℚ) + (-967658584698768599356719 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 1 + (197235423833376133858326 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 2 + (-3496748112601400425236 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 3 + (4 / 60283 : ℚ) * ((k : ℚ) + 20) ^ 4) * Mv (k + 21) + ((9763776750257673600830487 / 60055345667701483606574680 : ℚ) + (-637850599676346796529109 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 1 + (110022816231027496426678 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 2 + (-1798185234964420899716 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 3 + (2 / 60283 : ℚ) * ((k : ℚ) + 20) ^ 4) * Mv (k + 22) + ((1629643399658401298431417 / 6005534566770148360657468 : ℚ) + (-1193347922900006163935047 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 1 + (228836197203612506705146 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 2 + (-3695992827256283173628 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 3 + (4 / 60283 : ℚ) * ((k : ℚ) + 20) ^ 4) * Mv (k + 23) + ((-2289626214233111832681335 / 12011069133540296721314936 : ℚ) + (700439930384038451470232 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 1 + (-123188162606138108273488 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 2 + (1897807592291862273912 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 3 + (-2 / 60283 : ℚ) * ((k : ℚ) + 20) ^ 4) * Mv (k + 24) = 0 := by
  unfold Mv
  rw [show k + 20 - 1 = k + 19 from by omega, show k + 20 - 2 = k + 18 from by omega, show k + 20 - 3 = k + 17 from by omega, show k + 20 - 4 = k + 16 from by omega, show k + 20 - 5 = k + 15 from by omega, show k + 20 - 6 = k + 14 from by omega, show k + 21 - 1 = k + 20 from by omega, show k + 21 - 2 = k + 19 from by omega, show k + 21 - 3 = k + 18 from by omega, show k + 21 - 4 = k + 17 from by omega, show k + 21 - 5 = k + 16 from by omega, show k + 21 - 6 = k + 15 from by omega, show k + 22 - 1 = k + 21 from by omega, show k + 22 - 2 = k + 20 from by omega, show k + 22 - 3 = k + 19 from by omega, show k + 22 - 4 = k + 18 from by omega, show k + 22 - 5 = k + 17 from by omega, show k + 22 - 6 = k + 16 from by omega, show k + 23 - 1 = k + 22 from by omega, show k + 23 - 2 = k + 21 from by omega, show k + 23 - 3 = k + 20 from by omega, show k + 23 - 4 = k + 19 from by omega, show k + 23 - 5 = k + 18 from by omega, show k + 23 - 6 = k + 17 from by omega, show k + 24 - 1 = k + 23 from by omega, show k + 24 - 2 = k + 22 from by omega, show k + 24 - 3 = k + 21 from by omega, show k + 24 - 4 = k + 20 from by omega, show k + 24 - 5 = k + 19 from by omega, show k + 24 - 6 = k + 18 from by omega]
  simp only [a_eq]
  have r1_48 := rel1 (k + 13)
  have r1_49 := rel1 (k + 14)
  have r1_50 := rel1 (k + 15)
  have r1_51 := rel1 (k + 16)
  have r1_52 := rel1 (k + 17)
  have r1_53 := rel1 (k + 18)
  have r1_54 := rel1 (k + 19)
  have r2_47 := rel2 (k + 15)
  have r2_48 := rel2 (k + 16)
  have r2_49 := rel2 (k + 17)
  have r2_50 := rel2 (k + 18)
  have r2_51 := rel2 (k + 19)
  have r2_52 := rel2 (k + 20)
  have r2_53 := rel2 (k + 21)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_48 r1_49 r1_50 r1_51 r1_52 r1_53 r1_54 r2_47 r2_48 r2_49 r2_50 r2_51 r2_52 r2_53 ⊢
  push_cast at r1_48 r1_49 r1_50 r1_51 r1_52 r1_53 r1_54 r2_47 r2_48 r2_49 r2_50 r2_51 r2_52 r2_53 ⊢
  linear_combination ((-2187203946838372703801278648479 / 7506918208462685450821835 : ℚ) + (3254500942208575404546546454913 / 12011069133540296721314936 : ℚ) * ((k : ℚ) + 20) ^ 1 + (-2458550092143428763617994874815 / 24022138267080593442629872 : ℚ) * ((k : ℚ) + 20) ^ 2 + (30358918851106352833164309448 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 3 + (-16579836002526941244825582106 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 4 + (188015445438161491234428478 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 5 + (-166729 / 60283 : ℚ) * ((k : ℚ) + 20) ^ 6) * r1_48 + ((9402861161033492047840194513507 / 30027672833850741803287340 : ℚ) + (-11638554284239899157606822427691 / 30027672833850741803287340 : ℚ) * ((k : ℚ) + 20) ^ 1 + (4438889257550141265758403877465 / 24022138267080593442629872 : ℚ) * ((k : ℚ) + 20) ^ 2 + (-660606904146821274010478749699 / 15013836416925370901643670 : ℚ) * ((k : ℚ) + 20) ^ 3 + (41924825622027176493745702533 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 4 + (-537235780163349771110985614 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 5 + (514307 / 60283 : ℚ) * ((k : ℚ) + 20) ^ 6) * r1_49 + ((939979444586191963869009327753 / 7506918208462685450821835 : ℚ) + (-15552707621217597936978772219673 / 120110691335402967213149360 : ℚ) * ((k : ℚ) + 20) ^ 1 + (2415326232501378901680425963747 / 60055345667701483606574680 : ℚ) * ((k : ℚ) + 20) ^ 2 + (-5010652038732464700346754355 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 3 + (-115252813478963069145297058 / 326387748194029802209645 : ℚ) * ((k : ℚ) + 20) ^ 4 + (99110750613493220935093249 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 5 + (-134686 / 60283 : ℚ) * ((k : ℚ) + 20) ^ 6) * r1_50 + ((-12074995904834286064179611128281 / 60055345667701483606574680 : ℚ) + (2491807455395081108106950464521 / 60055345667701483606574680 : ℚ) * ((k : ℚ) + 20) ^ 1 + (2562800637631478591996164535133 / 120110691335402967213149360 : ℚ) * ((k : ℚ) + 20) ^ 2 + (-23318603778285543586245486411 / 3002767283385074180328734 : ℚ) * ((k : ℚ) + 20) ^ 3 + (7462183085772805225482457137 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 4 + (-64725825683922279714751500 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 5 + (32043 / 60283 : ℚ) * ((k : ℚ) + 20) ^ 6) * r1_51 + ((16895418682231027481401355446311 / 60055345667701483606574680 : ℚ) + (-23879714351600546479166755971527 / 120110691335402967213149360 : ℚ) * ((k : ℚ) + 20) ^ 1 + (862121842730183174399366396163 / 60055345667701483606574680 : ℚ) * ((k : ℚ) + 20) ^ 2 + (120383757277349808619902559894 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 3 + (-5959710156575460013947242350 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 4 + (524527200542010676093242059 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 5 + (-588710 / 60283 : ℚ) * ((k : ℚ) + 20) ^ 6) * r1_52 + ((948629206207523054426441593635 / 12011069133540296721314936 : ℚ) + (378025158027330854135606865819 / 12011069133540296721314936 : ℚ) * ((k : ℚ) + 20) ^ 1 + (-439527662705047990543995727687 / 24022138267080593442629872 : ℚ) * ((k : ℚ) + 20) ^ 2 + (27554861462298047320529260771 / 15013836416925370901643670 : ℚ) * ((k : ℚ) + 20) ^ 3 + (859638838062181656649379457 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 4 + (-41862916961785743930418468 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 5 + (1 : ℚ) * ((k : ℚ) + 20) ^ 6) * r1_53 + ((-535243630475060320014083001615 / 12011069133540296721314936 : ℚ) + (5868551668095147107783643828653 / 120110691335402967213149360 : ℚ) * ((k : ℚ) + 20) ^ 1 + (-1360772221943159480407836357727 / 120110691335402967213149360 : ℚ) * ((k : ℚ) + 20) ^ 2 + (-1415206824679692387784797588 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 3 + (2308478582311157142065832242 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 4 + (-50135183930416497738501073 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 5 + (1 : ℚ) * ((k : ℚ) + 20) ^ 6) * r1_54 + ((729067982279457567933759549493 / 30027672833850741803287340 : ℚ) + (-4452077593975015583665898025531 / 240221382670805934426298720 : ℚ) * ((k : ℚ) + 20) ^ 1 + (40836837847615251220958730982 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 2 + (-5843409880025105143658673773 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 3 + (81550270707945515958470576 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 4 + (-166729 / 120566 : ℚ) * ((k : ℚ) + 20) ^ 5) * r2_47 + ((-2755453810942047491088550362093 / 60055345667701483606574680 : ℚ) + (9777726935023290683414156467797 / 240221382670805934426298720 : ℚ) * ((k : ℚ) + 20) ^ 1 + (-81685278930492398812949505469 / 6005534566770148360657468 : ℚ) * ((k : ℚ) + 20) ^ 2 + (32230142805466054166963530763 / 15013836416925370901643670 : ℚ) * ((k : ℚ) + 20) ^ 3 + (-242823818755989756110725781 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 4 + (514307 / 120566 : ℚ) * ((k : ℚ) + 20) ^ 5) * r2_48 + ((-17365595813902352420223172709523 / 240221382670805934426298720 : ℚ) + (10366909692526566941242919221417 / 240221382670805934426298720 : ℚ) * ((k : ℚ) + 20) ^ 1 + (-68088039544120618549141257396 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 2 + (6145340598125822581779792481 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 3 + (-84657494864727462193237161 / 3002767283385074180328734 : ℚ) * ((k : ℚ) + 20) ^ 4 + (32043 / 120566 : ℚ) * ((k : ℚ) + 20) ^ 5) * r2_49 + ((-4460502940392559921799089035387 / 48044276534161186885259744 : ℚ) + (2550449189533723614418702181477 / 48044276534161186885259744 : ℚ) * ((k : ℚ) + 20) ^ 1 + (-161553581392945497169199092219 / 15013836416925370901643670 : ℚ) * ((k : ℚ) + 20) ^ 2 + (7580753784918317152468297551 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 3 + (-97095533524232197730280061 / 3002767283385074180328734 : ℚ) * ((k : ℚ) + 20) ^ 4 + (17923 / 120566 : ℚ) * ((k : ℚ) + 20) ^ 5) * r2_50 + ((17759213155314916754223342153531 / 240221382670805934426298720 : ℚ) + (-18001877067417001119511145959653 / 240221382670805934426298720 : ℚ) * ((k : ℚ) + 20) ^ 1 + (821868240981198268676497012759 / 30027672833850741803287340 : ℚ) * ((k : ℚ) + 20) ^ 2 + (-65630030931873074187515829289 / 15013836416925370901643670 : ℚ) * ((k : ℚ) + 20) ^ 3 + (965664510199869689068507511 / 3002767283385074180328734 : ℚ) * ((k : ℚ) + 20) ^ 4 + (-996571 / 120566 : ℚ) * ((k : ℚ) + 20) ^ 5) * r2_51 + ((189725841241504610885288318727 / 12011069133540296721314936 : ℚ) + (574782723651618199663246521163 / 240221382670805934426298720 : ℚ) * ((k : ℚ) + 20) ^ 1 + (-48041107747206265950303001299 / 15013836416925370901643670 : ℚ) * ((k : ℚ) + 20) ^ 2 + (4968406345045476838034476153 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 3 + (-82695037164765632246394858 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 4 + (3 / 2 : ℚ) * ((k : ℚ) + 20) ^ 5) * r2_52 + ((-178414543491686773338027667205 / 24022138267080593442629872 : ℚ) + (1126770730925596829078963694113 / 120110691335402967213149360 : ℚ) * ((k : ℚ) + 20) ^ 1 + (-5182381151809908978097500108 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 2 + (4082783155728308750450450492 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 3 + (-59143485780571720279487275 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 4 + (1 : ℚ) * ((k : ℚ) + 20) ^ 5) * r2_53

theorem Mv_zero : ∀ n : ℕ, 6 ≤ n → Mv n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 24
    · interval_cases n
      · exact base6
      · exact base7
      · exact base8
      · exact base9
      · exact base10
      · exact base11
      · exact base12
      · exact base13
      · exact base14
      · exact base15
      · exact base16
      · exact base17
      · exact base18
      · exact base19
      · exact base20
      · exact base21
      · exact base22
      · exact base23
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 24 := ⟨n - 24, by omega⟩
      have hc := certQ k
      have h0 : Mv (k + 20) = 0 := ih _ (by omega) (by omega)
      have h1 : Mv (k + 21) = 0 := ih _ (by omega) (by omega)
      have h2 : Mv (k + 22) = 0 := ih _ (by omega) (by omega)
      have h3 : Mv (k + 23) = 0 := ih _ (by omega) (by omega)
      have hq : ((-2289626214233111832681335 / 12011069133540296721314936 : ℚ) + (700439930384038451470232 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 1 + (-123188162606138108273488 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 2 + (1897807592291862273912 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 3 + (-2 / 60283 : ℚ) * ((k : ℚ) + 20) ^ 4) ≠ 0 := by
        have e : ((-2289626214233111832681335 / 12011069133540296721314936 : ℚ) + (700439930384038451470232 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 1 + (-123188162606138108273488 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 2 + (1897807592291862273912 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 3 + (-2 / 60283 : ℚ) * ((k : ℚ) + 20) ^ 4) = -((1014595292755564635738231 / 12011069133540296721314936 : ℚ) + (810029606305622171677288 / 7506918208462685450821835 : ℚ) * (k : ℚ) ^ 1 + (151580028883227671275888 / 7506918208462685450821835 : ℚ) * (k : ℚ) ^ 2 + (2087086700805792693928 / 1501383641692537090164367 : ℚ) * (k : ℚ) ^ 3 + (2 / 60283 : ℚ) * (k : ℚ) ^ 4) := by ring
        rw [e, neg_ne_zero]
        positivity
      have hm : ((-2289626214233111832681335 / 12011069133540296721314936 : ℚ) + (700439930384038451470232 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 1 + (-123188162606138108273488 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 2 + (1897807592291862273912 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 3 + (-2 / 60283 : ℚ) * ((k : ℚ) + 20) ^ 4) * Mv (k + 24) = 0 := by linear_combination hc - ((-6756197072397230754360163 / 60055345667701483606574680 : ℚ) + (481534495482865755289976 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 1 + (-96215384081671794777748 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 2 + (1698562877636979525520 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 3 + (-2 / 60283 : ℚ) * ((k : ℚ) + 20) ^ 4) * h0 - ((6771540475103260573876517 / 30027672833850741803287340 : ℚ) + (-967658584698768599356719 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 1 + (197235423833376133858326 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 2 + (-3496748112601400425236 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 3 + (4 / 60283 : ℚ) * ((k : ℚ) + 20) ^ 4) * h1 - ((9763776750257673600830487 / 60055345667701483606574680 : ℚ) + (-637850599676346796529109 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 1 + (110022816231027496426678 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 2 + (-1798185234964420899716 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 3 + (2 / 60283 : ℚ) * ((k : ℚ) + 20) ^ 4) * h2 - ((1629643399658401298431417 / 6005534566770148360657468 : ℚ) + (-1193347922900006163935047 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 1 + (228836197203612506705146 / 7506918208462685450821835 : ℚ) * ((k : ℚ) + 20) ^ 2 + (-3695992827256283173628 / 1501383641692537090164367 : ℚ) * ((k : ℚ) + 20) ^ 3 + (4 / 60283 : ℚ) * ((k : ℚ) + 20) ^ 4) * h3
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem main' : ∀ n : ℕ, 6 ≤ n → (-60283 * (n : ℚ) ^ 2 + 198489 * (n : ℚ) + 638110) * a n
      + (-60283 * (n : ℚ) ^ 2 - 13090 * (n : ℚ) + 236862) * a (n - 1)
      + (588710 * (n : ℚ) ^ 2 - 2858167 * (n : ℚ) + 437486) * a (n - 2)
      + (-32043 * (n : ℚ) ^ 2 + 2024290 * (n : ℚ) - 2826488) * a (n - 3)
      + (134686 * (n : ℚ) ^ 2 + 585099 * (n : ℚ) - 3417942) * a (n - 4)
      + (-514307 * (n : ℚ) ^ 2 + 4366464 * (n : ℚ) - 8945002) * a (n - 5)
      + (166729 * (n : ℚ) ^ 2 - 1863662 * (n : ℚ) + 5179728) * a (n - 6) = 0 := fun n hn => Mv_zero n hn

end OMA.P_oeis_a166290

theorem OMA.solution : type_of% @OMA.S_oeis_a166290.main := OMA.P_oeis_a166290.main'
