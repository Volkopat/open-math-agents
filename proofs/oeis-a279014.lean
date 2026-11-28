import OMAStatements.S_oeis_a279014
import Mathlib

-- Problem: A279014: a(n) = Sum_{k=0..n} fibonacci(k+1)*binomial(2*n-1,n-k).
-- Upstream: formal-conjectures statements/oeis-a279014.lean (declaration OMA.S_oeis_a279014.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: S = sqrt(R) satisfies S^2 = R, so 2 R S' = R' S (rel2). The series F = (A + B S) / C
-- satisfies C F = A + B S (rel1). Writing M(n) for the left side of the conjectured recurrence, an
-- explicit operator Q gives sum_i q_i(n) M(n + i) as a polynomial combination of shifted instances
-- of rel1 and rel2 (certQ, found by exact linear algebra), so M(n) = 0 follows by induction from the
-- first values, which are computed exactly from rel1 and rel2 (the leading q is nonzero there).

namespace OMA.P_oeis_a279014

open OMA.S_oeis_a279014 PowerSeries

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

noncomputable def F : ℚ⟦X⟧ := ((1 - 6 * X + 7 * X ^ 2 + 4 * X ^ 3 + (1 - 4 * X + X ^ 2) * S) * (2 - 16 * X + 30 * X ^ 2 + 8 * X ^ 3 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = coeff n F := rfl

theorem hF : F * (2 - 16 * X + 30 * X ^ 2 + 8 * X ^ 3 : ℚ⟦X⟧) = 1 - 6 * X + 7 * X ^ 2 + 4 * X ^ 3 + (1 - 4 * X + X ^ 2) * S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (2 - 16 * X + 30 * X ^ 2 + 8 * X ^ 3 : ℚ⟦X⟧) = C (2 : ℚ) + C (-16 : ℚ) * X ^ 1 + C (30 : ℚ) * X ^ 2 + C (8 : ℚ) * X ^ 3 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (2 : ℚ) * F + C (-16 : ℚ) * X ^ 1 * F + C (30 : ℚ) * X ^ 2 * F + C (8 : ℚ) * X ^ 3 * F - (C (1 : ℚ) * S + C (-4 : ℚ) * X ^ 1 * S + C (1 : ℚ) * X ^ 2 * S) - (C (1 : ℚ) + C (-6 : ℚ) * X ^ 1 + C (7 : ℚ) * X ^ 2 + C (4 : ℚ) * X ^ 3) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (2 : ℚ) * coeff (m + 4) F + (-16 : ℚ) * coeff (m + 3) F + (30 : ℚ) * coeff (m + 2) F + (8 : ℚ) * coeff (m + 1) F - ((1 : ℚ) * coeff (m + 4) S + (-4 : ℚ) * coeff (m + 3) S + (1 : ℚ) * coeff (m + 2) S) = 0 := by
  have h := congrArg (coeff (m + 4)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 4 - 1 = m + 3 from by omega, show m + 4 - 2 = m + 2 from by omega, show m + 4 - 3 = m + 1 from by omega] at h
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

theorem hs9 : coeff 9 S = (-2860 : ℚ) := by
  have h := congrArg (coeff 8) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8] at h ⊢ <;> linarith

theorem hs10 : coeff 10 S = (-9724 : ℚ) := by
  have h := congrArg (coeff 9) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9] at h ⊢ <;> linarith

theorem hs11 : coeff 11 S = (-33592 : ℚ) := by
  have h := congrArg (coeff 10) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10] at h ⊢ <;> linarith

theorem hs12 : coeff 12 S = (-117572 : ℚ) := by
  have h := congrArg (coeff 11) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11] at h ⊢ <;> linarith

theorem hs13 : coeff 13 S = (-416024 : ℚ) := by
  have h := congrArg (coeff 12) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12] at h ⊢ <;> linarith

theorem hs14 : coeff 14 S = (-1485800 : ℚ) := by
  have h := congrArg (coeff 13) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13] at h ⊢ <;> linarith

theorem hs15 : coeff 15 S = (-5348880 : ℚ) := by
  have h := congrArg (coeff 14) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14] at h ⊢ <;> linarith

theorem hs16 : coeff 16 S = (-19389690 : ℚ) := by
  have h := congrArg (coeff 15) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15] at h ⊢ <;> linarith

theorem hs17 : coeff 17 S = (-70715340 : ℚ) := by
  have h := congrArg (coeff 16) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16] at h ⊢ <;> linarith

theorem hs18 : coeff 18 S = (-259289580 : ℚ) := by
  have h := congrArg (coeff 17) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17] at h ⊢ <;> linarith

theorem hs19 : coeff 19 S = (-955277400 : ℚ) := by
  have h := congrArg (coeff 18) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18] at h ⊢ <;> linarith

theorem hs20 : coeff 20 S = (-3534526380 : ℚ) := by
  have h := congrArg (coeff 19) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19] at h ⊢ <;> linarith

theorem hs21 : coeff 21 S = (-13128240840 : ℚ) := by
  have h := congrArg (coeff 20) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20] at h ⊢ <;> linarith

theorem hs22 : coeff 22 S = (-48932534040 : ℚ) := by
  have h := congrArg (coeff 21) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21] at h ⊢ <;> linarith

theorem hs23 : coeff 23 S = (-182965127280 : ℚ) := by
  have h := congrArg (coeff 22) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22] at h ⊢ <;> linarith

theorem hs24 : coeff 24 S = (-686119227300 : ℚ) := by
  have h := congrArg (coeff 23) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23] at h ⊢ <;> linarith

theorem hf0 : coeff 0 F = (1 : ℚ) := by
  have h := congrArg (coeff 0) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24] at h ⊢ <;> linarith

theorem hf0c : constantCoeff F = (1 : ℚ) := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf0

theorem hf1 : coeff 1 F = (2 : ℚ) := by
  have h := congrArg (coeff 1) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf0c] at h ⊢ <;> linarith

theorem hf2 : coeff 2 F = (8 : ℚ) := by
  have h := congrArg (coeff 2) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf0c] at h ⊢ <;> linarith

theorem hf3 : coeff 3 F = (33 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem hf4 : coeff 4 F = (138 : ℚ) := by
  have h := congrArg (coeff 4) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf0c] at h ⊢ <;> linarith

theorem hf5 : coeff 5 F = (581 : ℚ) := by
  have h := congrArg (coeff 5) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf0c] at h ⊢ <;> linarith

theorem hf6 : coeff 6 F = (2455 : ℚ) := by
  have h := congrArg (coeff 6) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf5, hf0c] at h ⊢ <;> linarith

theorem hf7 : coeff 7 F = (10395 : ℚ) := by
  have h := congrArg (coeff 7) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf0c] at h ⊢ <;> linarith

theorem hf8 : coeff 8 F = (44068 : ℚ) := by
  have h := congrArg (coeff 8) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf0c] at h ⊢ <;> linarith

theorem hf9 : coeff 9 F = (186953 : ℚ) := by
  have h := congrArg (coeff 9) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf0c] at h ⊢ <;> linarith

theorem hf10 : coeff 10 F = (793453 : ℚ) := by
  have h := congrArg (coeff 10) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf0c] at h ⊢ <;> linarith

theorem hf11 : coeff 11 F = (3368279 : ℚ) := by
  have h := congrArg (coeff 11) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf0c] at h ⊢ <;> linarith

theorem hf12 : coeff 12 F = (14300161 : ℚ) := by
  have h := congrArg (coeff 12) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf0c] at h ⊢ <;> linarith

theorem hf13 : coeff 13 F = (60713627 : ℚ) := by
  have h := congrArg (coeff 13) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf0c] at h ⊢ <;> linarith

theorem hf14 : coeff 14 F = (257763847 : ℚ) := by
  have h := congrArg (coeff 14) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf0c] at h ⊢ <;> linarith

theorem hf15 : coeff 15 F = (1094294875 : ℚ) := by
  have h := congrArg (coeff 15) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf0c] at h ⊢ <;> linarith

theorem hf16 : coeff 16 F = (4645306802 : ℚ) := by
  have h := congrArg (coeff 16) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf0c] at h ⊢ <;> linarith

theorem hf17 : coeff 17 F = (19717723173 : ℚ) := by
  have h := congrArg (coeff 17) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16, hf0c] at h ⊢ <;> linarith

theorem hf18 : coeff 18 F = (83687094899 : ℚ) := by
  have h := congrArg (coeff 18) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16, hf17, hf0c] at h ⊢ <;> linarith

theorem hf19 : coeff 19 F = (355155267179 : ℚ) := by
  have h := congrArg (coeff 19) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16, hf17, hf18, hf0c] at h ⊢ <;> linarith

theorem hf20 : coeff 20 F = (1507078468075 : ℚ) := by
  have h := congrArg (coeff 20) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16, hf17, hf18, hf19, hf0c] at h ⊢ <;> linarith

theorem hf21 : coeff 21 F = (6394577650959 : ℚ) := by
  have h := congrArg (coeff 21) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16, hf17, hf18, hf19, hf20, hf0c] at h ⊢ <;> linarith

theorem hf22 : coeff 22 F = (27129846069301 : ℚ) := by
  have h := congrArg (coeff 22) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16, hf17, hf18, hf19, hf20, hf21, hf0c] at h ⊢ <;> linarith

theorem hf23 : coeff 23 F = (115091608301743 : ℚ) := by
  have h := congrArg (coeff 23) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16, hf17, hf18, hf19, hf20, hf21, hf22, hf0c] at h ⊢ <;> linarith

theorem hf24 : coeff 24 F = (488205269144483 : ℚ) := by
  have h := congrArg (coeff 24) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hs12, hs13, hs14, hs15, hs16, hs17, hs18, hs19, hs20, hs21, hs22, hs23, hs24, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf11, hf12, hf13, hf14, hf15, hf16, hf17, hf18, hf19, hf20, hf21, hf22, hf23, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (1 : ℚ) := by rw [a_eq]; exact hf0

theorem ha1 : a 1 = (2 : ℚ) := by rw [a_eq]; exact hf1

theorem ha2 : a 2 = (8 : ℚ) := by rw [a_eq]; exact hf2

theorem ha3 : a 3 = (33 : ℚ) := by rw [a_eq]; exact hf3

theorem ha4 : a 4 = (138 : ℚ) := by rw [a_eq]; exact hf4

theorem ha5 : a 5 = (581 : ℚ) := by rw [a_eq]; exact hf5

theorem ha6 : a 6 = (2455 : ℚ) := by rw [a_eq]; exact hf6

theorem ha7 : a 7 = (10395 : ℚ) := by rw [a_eq]; exact hf7

theorem ha8 : a 8 = (44068 : ℚ) := by rw [a_eq]; exact hf8

theorem ha9 : a 9 = (186953 : ℚ) := by rw [a_eq]; exact hf9

theorem ha10 : a 10 = (793453 : ℚ) := by rw [a_eq]; exact hf10

theorem ha11 : a 11 = (3368279 : ℚ) := by rw [a_eq]; exact hf11

theorem ha12 : a 12 = (14300161 : ℚ) := by rw [a_eq]; exact hf12

theorem ha13 : a 13 = (60713627 : ℚ) := by rw [a_eq]; exact hf13

theorem ha14 : a 14 = (257763847 : ℚ) := by rw [a_eq]; exact hf14

theorem ha15 : a 15 = (1094294875 : ℚ) := by rw [a_eq]; exact hf15

theorem ha16 : a 16 = (4645306802 : ℚ) := by rw [a_eq]; exact hf16

theorem ha17 : a 17 = (19717723173 : ℚ) := by rw [a_eq]; exact hf17

theorem ha18 : a 18 = (83687094899 : ℚ) := by rw [a_eq]; exact hf18

theorem ha19 : a 19 = (355155267179 : ℚ) := by rw [a_eq]; exact hf19

theorem ha20 : a 20 = (1507078468075 : ℚ) := by rw [a_eq]; exact hf20

theorem ha21 : a 21 = (6394577650959 : ℚ) := by rw [a_eq]; exact hf21

theorem ha22 : a 22 = (27129846069301 : ℚ) := by rw [a_eq]; exact hf22

theorem ha23 : a 23 = (115091608301743 : ℚ) := by rw [a_eq]; exact hf23

theorem ha24 : a 24 = (488205269144483 : ℚ) := by rw [a_eq]; exact hf24

noncomputable def Mv (n : ℕ) : ℚ := (3 * (n : ℚ) ^ 2 - 62 * (n : ℚ)) * a n + (3 * (n : ℚ) ^ 2 + 362 * (n : ℚ) - 247) * a (n - 1)
      + (-171 * (n : ℚ) ^ 2 + 220 * (n : ℚ) + 162) * a (n - 2)
      + (417 * (n : ℚ) ^ 2 - 2570 * (n : ℚ) + 3551) * a (n - 3)
      + (108 * (n : ℚ) ^ 2 - 614 * (n : ℚ) + 826) * a (n - 4)

theorem base5 : Mv 5 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem base6 : Mv 6 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem base7 : Mv 7 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem base8 : Mv 8 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem base9 : Mv 9 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem base10 : Mv 10 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem base11 : Mv 11 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem base12 : Mv 12 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem base13 : Mv 13 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem base14 : Mv 14 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem base15 : Mv 15 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem base16 : Mv 16 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem base17 : Mv 17 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem base18 : Mv 18 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem base19 : Mv 19 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem base20 : Mv 20 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem base21 : Mv 21 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem base22 : Mv 22 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem base23 : Mv 23 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem base24 : Mv 24 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10, ha11, ha12, ha13, ha14, ha15, ha16, ha17, ha18, ha19, ha20, ha21, ha22, ha23, ha24]

theorem certQ (k : ℕ) : ((13888 / 117 : ℚ) + (-16 / 3 : ℚ) * ((k : ℚ) + 24) ^ 1) * Mv (k + 24) + ((-3628 / 117 : ℚ) + (4 / 3 : ℚ) * ((k : ℚ) + 24) ^ 1) * Mv (k + 25) = 0 := by
  unfold Mv
  rw [show k + 24 - 1 = k + 23 from by omega, show k + 24 - 2 = k + 22 from by omega, show k + 24 - 3 = k + 21 from by omega, show k + 24 - 4 = k + 20 from by omega, show k + 25 - 1 = k + 24 from by omega, show k + 25 - 2 = k + 23 from by omega, show k + 25 - 3 = k + 22 from by omega, show k + 25 - 4 = k + 21 from by omega]
  simp only [a_eq]
  have r1_49 := rel1 (k + 19)
  have r1_50 := rel1 (k + 20)
  have r1_51 := rel1 (k + 21)
  have r2_47 := rel2 (k + 20)
  have r2_48 := rel2 (k + 21)
  have r2_49 := rel2 (k + 22)
  have r2_50 := rel2 (k + 23)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_49 r1_50 r1_51 r2_47 r2_48 r2_49 r2_50 ⊢
  push_cast at r1_49 r1_50 r1_51 r2_47 r2_48 r2_49 r2_50 ⊢
  linear_combination ((1433936 / 117 : ℚ) + (-1130332 / 117 : ℚ) * ((k : ℚ) + 24) ^ 1 + (78460 / 39 : ℚ) * ((k : ℚ) + 24) ^ 2 + (-72 : ℚ) * ((k : ℚ) + 24) ^ 3) * r1_49 + ((214052 / 39 : ℚ) + (-34780 / 13 : ℚ) * ((k : ℚ) + 24) ^ 1 + (-5014 / 39 : ℚ) * ((k : ℚ) + 24) ^ 2 + (10 : ℚ) * ((k : ℚ) + 24) ^ 3) * r1_50 + ((107026 / 117 : ℚ) + (96982 / 117 : ℚ) * ((k : ℚ) + 24) ^ 1 + (-1090 / 13 : ℚ) * ((k : ℚ) + 24) ^ 2 + (2 : ℚ) * ((k : ℚ) + 24) ^ 3) * r1_51 + ((51212 / 117 : ℚ) + (-8579 / 39 : ℚ) * ((k : ℚ) + 24) ^ 1 + (9 : ℚ) * ((k : ℚ) + 24) ^ 2) * r2_47 + ((-81479 / 39 : ℚ) + (34124 / 39 : ℚ) * ((k : ℚ) + 24) ^ 1 + (-35 : ℚ) * ((k : ℚ) + 24) ^ 2) * r2_48 + ((-14042 / 13 : ℚ) + (-2741 / 39 : ℚ) * ((k : ℚ) + 24) ^ 1 + (5 : ℚ) * ((k : ℚ) + 24) ^ 2) * r2_49 + ((53513 / 117 : ℚ) + (-558 / 13 : ℚ) * ((k : ℚ) + 24) ^ 1 + (1 : ℚ) * ((k : ℚ) + 24) ^ 2) * r2_50

theorem Mv_zero : ∀ n : ℕ, 5 ≤ n → Mv n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 25
    · interval_cases n
      · exact base5
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
      · exact base24
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 25 := ⟨n - 25, by omega⟩
      have hc := certQ k
      have h0 : Mv (k + 24) = 0 := ih _ (by omega) (by omega)
      have hq : ((-3628 / 117 : ℚ) + (4 / 3 : ℚ) * ((k : ℚ) + 24) ^ 1) ≠ 0 := by
        have e : ((-3628 / 117 : ℚ) + (4 / 3 : ℚ) * ((k : ℚ) + 24) ^ 1) = (116 / 117 : ℚ) + (4 / 3 : ℚ) * (k : ℚ) ^ 1 := by ring
        rw [e]
        positivity
      have hm : ((-3628 / 117 : ℚ) + (4 / 3 : ℚ) * ((k : ℚ) + 24) ^ 1) * Mv (k + 25) = 0 := by linear_combination hc - ((13888 / 117 : ℚ) + (-16 / 3 : ℚ) * ((k : ℚ) + 24) ^ 1) * h0
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem main' : ∀ n : ℕ, 5 ≤ n → (3 * (n : ℚ) ^ 2 - 62 * (n : ℚ)) * a n + (3 * (n : ℚ) ^ 2 + 362 * (n : ℚ) - 247) * a (n - 1)
      + (-171 * (n : ℚ) ^ 2 + 220 * (n : ℚ) + 162) * a (n - 2)
      + (417 * (n : ℚ) ^ 2 - 2570 * (n : ℚ) + 3551) * a (n - 3)
      + (108 * (n : ℚ) ^ 2 - 614 * (n : ℚ) + 826) * a (n - 4) = 0 := fun n hn => Mv_zero n hn

end OMA.P_oeis_a279014

theorem OMA.solution : type_of% @OMA.S_oeis_a279014.main := OMA.P_oeis_a279014.main'
