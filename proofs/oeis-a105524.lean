import OMAStatements.S_oeis_a105524
import Mathlib

-- Problem: A105524: Diagonal sums of number triangle A105522.
-- Upstream: formal-conjectures statements/oeis-a105524.lean (declaration OMA.S_oeis_a105524.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: S = sqrt(R) satisfies S^2 = R, so 2 R S' = R' S (rel2). The series F = (A + B S) / C
-- satisfies C F = A + B S (rel1). Writing M(n) for the left side of the conjectured recurrence, an
-- explicit operator Q gives sum_i q_i(n) M(n + i) as a polynomial combination of shifted instances
-- of rel1 and rel2 (certQ, found by exact linear algebra), so M(n) = 0 follows by induction from the
-- first values, which are computed exactly from rel1 and rel2 (the leading q is nonzero there).

namespace OMA.P_oeis_a105524

open OMA.S_oeis_a105524 PowerSeries

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

theorem hRC : R = C (1 : ℚ) + C (4 : ℚ) * X ^ 2 := by
  simp only [R, map_one, map_neg, map_ofNat] <;> ring

theorem hDR : d⁄dX ℚ R = C (8 : ℚ) * X ^ 1 := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  try push_cast
  try ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (8 : ℚ) * X ^ 2 * d⁄dX ℚ S - (C (8 : ℚ) * X ^ 1 * S) = 0 := by
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

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 3) S * ((m : ℚ) + 3)) + (8 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((8 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 2)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := ((2 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 - 10 * X ^ 5 - 4 * X ^ 6 + 4 * X ^ 7 + (-2 * X ^ 2 - 4 * X ^ 3 + 5 * X ^ 4 + 2 * X ^ 5 - 2 * X ^ 6) * S) * (8 - 8 * X ^ 2 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = coeff (n + 4) F := rfl

theorem hF : F * (8 - 8 * X ^ 2 + 2 * X ^ 4 : ℚ⟦X⟧) = 2 * X ^ 2 + 4 * X ^ 3 + 7 * X ^ 4 - 10 * X ^ 5 - 4 * X ^ 6 + 4 * X ^ 7 + (-2 * X ^ 2 - 4 * X ^ 3 + 5 * X ^ 4 + 2 * X ^ 5 - 2 * X ^ 6) * S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (8 - 8 * X ^ 2 + 2 * X ^ 4 : ℚ⟦X⟧) = C (8 : ℚ) + C (-8 : ℚ) * X ^ 2 + C (2 : ℚ) * X ^ 4 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (8 : ℚ) * F + C (-8 : ℚ) * X ^ 2 * F + C (2 : ℚ) * X ^ 4 * F - (C (-2 : ℚ) * X ^ 2 * S + C (-4 : ℚ) * X ^ 3 * S + C (5 : ℚ) * X ^ 4 * S + C (2 : ℚ) * X ^ 5 * S + C (-2 : ℚ) * X ^ 6 * S) - (C (2 : ℚ) * X ^ 2 + C (4 : ℚ) * X ^ 3 + C (7 : ℚ) * X ^ 4 + C (-10 : ℚ) * X ^ 5 + C (-4 : ℚ) * X ^ 6 + C (4 : ℚ) * X ^ 7) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (8 : ℚ) * coeff (m + 8) F + (-8 : ℚ) * coeff (m + 6) F + (2 : ℚ) * coeff (m + 4) F - ((-2 : ℚ) * coeff (m + 6) S + (-4 : ℚ) * coeff (m + 5) S + (5 : ℚ) * coeff (m + 4) S + (2 : ℚ) * coeff (m + 3) S + (-2 : ℚ) * coeff (m + 2) S) = 0 := by
  have h := congrArg (coeff (m + 8)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 8 - 2 = m + 6 from by omega, show m + 8 - 3 = m + 5 from by omega, show m + 8 - 4 = m + 4 from by omega, show m + 8 - 5 = m + 3 from by omega, show m + 8 - 6 = m + 2 from by omega] at h
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

theorem hs1 : coeff 1 S = (0 : ℚ) := by
  have h := congrArg (coeff 0) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0] at h ⊢ <;> linarith

theorem hs2 : coeff 2 S = (2 : ℚ) := by
  have h := congrArg (coeff 1) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1] at h ⊢ <;> linarith

theorem hs3 : coeff 3 S = (0 : ℚ) := by
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

theorem hs5 : coeff 5 S = (0 : ℚ) := by
  have h := congrArg (coeff 4) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4] at h ⊢ <;> linarith

theorem hs6 : coeff 6 S = (4 : ℚ) := by
  have h := congrArg (coeff 5) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5] at h ⊢ <;> linarith

theorem hs7 : coeff 7 S = (0 : ℚ) := by
  have h := congrArg (coeff 6) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6] at h ⊢ <;> linarith

theorem hs8 : coeff 8 S = (-10 : ℚ) := by
  have h := congrArg (coeff 7) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7] at h ⊢ <;> linarith

theorem hs9 : coeff 9 S = (0 : ℚ) := by
  have h := congrArg (coeff 8) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8] at h ⊢ <;> linarith

theorem hs10 : coeff 10 S = (28 : ℚ) := by
  have h := congrArg (coeff 9) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9] at h ⊢ <;> linarith

theorem hs11 : coeff 11 S = (0 : ℚ) := by
  have h := congrArg (coeff 10) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10] at h ⊢ <;> linarith

theorem hf0 : coeff 0 F = (0 : ℚ) := by
  have h := congrArg (coeff 0) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11] at h ⊢ <;> linarith

theorem hf0c : constantCoeff F = (0 : ℚ) := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf0

theorem hf1 : coeff 1 F = (0 : ℚ) := by
  have h := congrArg (coeff 1) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf0c] at h ⊢ <;> linarith

theorem hf2 : coeff 2 F = (0 : ℚ) := by
  have h := congrArg (coeff 2) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf0c] at h ⊢ <;> linarith

theorem hf3 : coeff 3 F = (0 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem hf4 : coeff 4 F = (1 : ℚ) := by
  have h := congrArg (coeff 4) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf2, hf3, hf0c] at h ⊢ <;> linarith

theorem hf5 : coeff 5 F = (-2 : ℚ) := by
  have h := congrArg (coeff 5) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf2, hf3, hf4, hf0c] at h ⊢ <;> linarith

theorem hf6 : coeff 6 F = (2 : ℚ) := by
  have h := congrArg (coeff 6) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf2, hf3, hf4, hf5, hf0c] at h ⊢ <;> linarith

theorem hf7 : coeff 7 F = (0 : ℚ) := by
  have h := congrArg (coeff 7) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf0c] at h ⊢ <;> linarith

theorem hf8 : coeff 8 F = (-1 : ℚ) := by
  have h := congrArg (coeff 8) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf0c] at h ⊢ <;> linarith

theorem hf9 : coeff 9 F = (-2 : ℚ) := by
  have h := congrArg (coeff 9) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf0c] at h ⊢ <;> linarith

theorem hf10 : coeff 10 F = (4 : ℚ) := by
  have h := congrArg (coeff 10) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf0c] at h ⊢ <;> linarith

theorem hf11 : coeff 11 F = (4 : ℚ) := by
  have h := congrArg (coeff 11) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hs11, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf10, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (1 : ℚ) := by rw [a_eq]; exact hf4

theorem ha1 : a 1 = (-2 : ℚ) := by rw [a_eq]; exact hf5

theorem ha2 : a 2 = (2 : ℚ) := by rw [a_eq]; exact hf6

theorem ha3 : a 3 = (0 : ℚ) := by rw [a_eq]; exact hf7

theorem ha4 : a 4 = (-1 : ℚ) := by rw [a_eq]; exact hf8

theorem ha5 : a 5 = (-2 : ℚ) := by rw [a_eq]; exact hf9

theorem ha6 : a 6 = (4 : ℚ) := by rw [a_eq]; exact hf10

theorem ha7 : a 7 = (4 : ℚ) := by rw [a_eq]; exact hf11

noncomputable def Mv (n : ℕ) : ℚ := (26 * (n : ℚ) ^ 3 - 18 * (n : ℚ) ^ 2 - 128 * (n : ℚ) + 24) * a n
      + (24 * (n : ℚ) - 192) * a (n - 1)
      + (91 * (n : ℚ) ^ 3 - 375 * (n : ℚ) ^ 2 + 152 * (n : ℚ) + 372) * a (n - 2)
      + (-12 * (n : ℚ) + 96) * a (n - 3)
      + (-52 * (n : ℚ) ^ 3 + 192 * (n : ℚ) ^ 2 - 44 * (n : ℚ) - 192) * a (n - 4)

theorem base4 : Mv 4 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7]

theorem base5 : Mv 5 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7]

theorem base6 : Mv 6 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7]

theorem base7 : Mv 7 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7]

theorem certQ (k : ℕ) : ((272306337300883 / 52211407693523 : ℚ) + (2461110211517098 / 469902669241707 : ℚ) * ((k : ℚ) + 4) ^ 1 + (14975281849504 / 12048786390813 : ℚ) * ((k : ℚ) + 4) ^ 2) * Mv (k + 4) + ((1459779095872208 / 156634223080569 : ℚ) + (5029112387755216 / 469902669241707 : ℚ) * ((k : ℚ) + 4) ^ 1 + (26430191781688 / 12048786390813 : ℚ) * ((k : ℚ) + 4) ^ 2) * Mv (k + 5) + ((4517421252002768 / 469902669241707 : ℚ) + (2086211482533676 / 469902669241707 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-29950563699008 / 12048786390813 : ℚ) * ((k : ℚ) + 4) ^ 2) * Mv (k + 6) + ((3593445802283936 / 469902669241707 : ℚ) + (2311104978319552 / 469902669241707 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-52860383563376 / 12048786390813 : ℚ) * ((k : ℚ) + 4) ^ 2) * Mv (k + 7) + ((-4 / 13 : ℚ)) * Mv (k + 8) = 0 := by
  unfold Mv
  rw [show k + 4 - 1 = k + 3 from by omega, show k + 4 - 2 = k + 2 from by omega, show k + 4 - 3 = k + 1 from by omega, show k + 4 - 4 = k from by omega, show k + 5 - 1 = k + 4 from by omega, show k + 5 - 2 = k + 3 from by omega, show k + 5 - 3 = k + 2 from by omega, show k + 5 - 4 = k + 1 from by omega, show k + 6 - 1 = k + 5 from by omega, show k + 6 - 2 = k + 4 from by omega, show k + 6 - 3 = k + 3 from by omega, show k + 6 - 4 = k + 2 from by omega, show k + 7 - 1 = k + 6 from by omega, show k + 7 - 2 = k + 5 from by omega, show k + 7 - 3 = k + 4 from by omega, show k + 7 - 4 = k + 3 from by omega, show k + 8 - 1 = k + 7 from by omega, show k + 8 - 2 = k + 6 from by omega, show k + 8 - 3 = k + 5 from by omega, show k + 8 - 4 = k + 4 from by omega]
  simp only [a_eq]
  have r1_50 := rel1 (k)
  have r1_51 := rel1 (k + 1)
  have r1_52 := rel1 (k + 2)
  have r1_53 := rel1 (k + 3)
  have r1_54 := rel1 (k + 4)
  have r2_45 := rel2 (k + 1)
  have r2_46 := rel2 (k + 2)
  have r2_47 := rel2 (k + 3)
  have r2_48 := rel2 (k + 4)
  have r2_49 := rel2 (k + 5)
  have r2_50 := rel2 (k + 6)
  have r2_51 := rel2 (k + 7)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_50 r1_51 r1_52 r1_53 r1_54 r2_45 r2_46 r2_47 r2_48 r2_49 r2_50 r2_51 ⊢
  push_cast at r1_50 r1_51 r1_52 r1_53 r1_54 r2_45 r2_46 r2_47 r2_48 r2_49 r2_50 r2_51 ⊢
  linear_combination ((-26141408380884768 / 52211407693523 : ℚ) + (-96727745030405414 / 156634223080569 : ℚ) * ((k : ℚ) + 4) ^ 1 + (125060795530043780 / 469902669241707 : ℚ) * ((k : ℚ) + 4) ^ 2 + (53232701850120118 / 156634223080569 : ℚ) * ((k : ℚ) + 4) ^ 3 + (-609339250377044 / 36146359172439 : ℚ) * ((k : ℚ) + 4) ^ 4 + (-389357328087104 / 12048786390813 : ℚ) * ((k : ℚ) + 4) ^ 5) * r1_50 + ((-10285761343512944 / 52211407693523 : ℚ) + (88310127929017354 / 156634223080569 : ℚ) * ((k : ℚ) + 4) ^ 1 + (505296158188428068 / 469902669241707 : ℚ) * ((k : ℚ) + 4) ^ 2 + (22662855220491424 / 156634223080569 : ℚ) * ((k : ℚ) + 4) ^ 3 + (-8630994419299280 / 36146359172439 : ℚ) * ((k : ℚ) + 4) ^ 4 + (-687184986323888 / 12048786390813 : ℚ) * ((k : ℚ) + 4) ^ 5) * r1_51 + ((-15410062435352850 / 52211407693523 : ℚ) + (-30787533777510704 / 469902669241707 : ℚ) * ((k : ℚ) + 4) ^ 1 + (21651383987926255 / 72292718344878 : ℚ) * ((k : ℚ) + 4) ^ 2 + (52033064949107731 / 939805338483414 : ℚ) * ((k : ℚ) + 4) ^ 3 + (-1028388800790245 / 36146359172439 : ℚ) * ((k : ℚ) + 4) ^ 4 + (-97339332021776 / 12048786390813 : ℚ) * ((k : ℚ) + 4) ^ 5) * r1_52 + ((9176395087962848 / 52211407693523 : ℚ) + (260884323685159924 / 469902669241707 : ℚ) * ((k : ℚ) + 4) ^ 1 + (185259915071917736 / 469902669241707 : ℚ) * ((k : ℚ) + 4) ^ 2 + (-46007043088048732 / 469902669241707 : ℚ) * ((k : ℚ) + 4) ^ 3 + (-3703914824053568 / 36146359172439 : ℚ) * ((k : ℚ) + 4) ^ 4 + (-171796246580972 / 12048786390813 : ℚ) * ((k : ℚ) + 4) ^ 5) * r1_53 + ((-444 / 13 : ℚ) + (-488 / 13 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-147 / 13 : ℚ) * ((k : ℚ) + 4) ^ 2 + (-1 : ℚ) * ((k : ℚ) + 4) ^ 3) * r1_54 + ((-2178450698407064 / 52211407693523 : ℚ) + (-4725736669665007 / 72292718344878 : ℚ) * ((k : ℚ) + 4) ^ 1 + (121757895486311 / 313268446161138 : ℚ) * ((k : ℚ) + 4) ^ 2 + (1028388800790245 / 36146359172439 : ℚ) * ((k : ℚ) + 4) ^ 3 + (97339332021776 / 12048786390813 : ℚ) * ((k : ℚ) + 4) ^ 4) * r2_45 + ((1981955879671478 / 52211407693523 : ℚ) + (8700889313145021 / 52211407693523 : ℚ) * ((k : ℚ) + 4) ^ 1 + (57788948160967087 / 313268446161138 : ℚ) * ((k : ℚ) + 4) ^ 2 + (817385093195245 / 12048786390813 : ℚ) * ((k : ℚ) + 4) ^ 3 + (24818971519732 / 4016262130271 : ℚ) * ((k : ℚ) + 4) ^ 4) * r2_46 + ((30114609930186007 / 104422815387046 : ℚ) + (952197092621162389 / 1879610676966828 : ℚ) * ((k : ℚ) + 4) ^ 1 + (81421884392107661 / 626536892322276 : ℚ) * ((k : ℚ) + 4) ^ 2 + (-7568038732433417 / 72292718344878 : ℚ) * ((k : ℚ) + 4) ^ 3 + (-415144576635412 / 12048786390813 : ℚ) * ((k : ℚ) + 4) ^ 4) * r2_47 + ((23746526818112320 / 52211407693523 : ℚ) + (200900364800207428 / 469902669241707 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-16330221855041468 / 156634223080569 : ℚ) * ((k : ℚ) + 4) ^ 2 + (-5089701886873528 / 36146359172439 : ℚ) * ((k : ℚ) + 4) ^ 3 + (-234811952408878 / 12048786390813 : ℚ) * ((k : ℚ) + 4) ^ 4) * r2_48 + ((-2741804869213576 / 52211407693523 : ℚ) + (-45919327972506998 / 156634223080569 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-33532904692183343 / 156634223080569 : ℚ) * ((k : ℚ) + 4) ^ 2 + (1048345515564247 / 12048786390813 : ℚ) * ((k : ℚ) + 4) ^ 3 + (146977275061240 / 4016262130271 : ℚ) * ((k : ℚ) + 4) ^ 4) * r2_49 + ((-1121990863256440 / 52211407693523 : ℚ) + (-43101511872710300 / 469902669241707 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-8768758240167358 / 156634223080569 : ℚ) * ((k : ℚ) + 4) ^ 2 + (1126971125338988 / 36146359172439 : ℚ) * ((k : ℚ) + 4) ^ 3 + (171796246580972 / 12048786390813 : ℚ) * ((k : ℚ) + 4) ^ 4) * r2_50 + ((74 / 13 : ℚ) + (69 / 13 : ℚ) * ((k : ℚ) + 4) ^ 1 + (1 : ℚ) * ((k : ℚ) + 4) ^ 2) * r2_51

theorem Mv_zero : ∀ n : ℕ, 4 ≤ n → Mv n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 8
    · interval_cases n
      · exact base4
      · exact base5
      · exact base6
      · exact base7
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 8 := ⟨n - 8, by omega⟩
      have hc := certQ k
      have h0 : Mv (k + 4) = 0 := ih _ (by omega) (by omega)
      have h1 : Mv (k + 5) = 0 := ih _ (by omega) (by omega)
      have h2 : Mv (k + 6) = 0 := ih _ (by omega) (by omega)
      have h3 : Mv (k + 7) = 0 := ih _ (by omega) (by omega)
      have hq : ((-4 / 13 : ℚ)) ≠ 0 := by
        have e : ((-4 / 13 : ℚ)) = -((4 / 13 : ℚ)) := by ring
        rw [e, neg_ne_zero]
        positivity
      have hm : ((-4 / 13 : ℚ)) * Mv (k + 8) = 0 := by linear_combination hc - ((272306337300883 / 52211407693523 : ℚ) + (2461110211517098 / 469902669241707 : ℚ) * ((k : ℚ) + 4) ^ 1 + (14975281849504 / 12048786390813 : ℚ) * ((k : ℚ) + 4) ^ 2) * h0 - ((1459779095872208 / 156634223080569 : ℚ) + (5029112387755216 / 469902669241707 : ℚ) * ((k : ℚ) + 4) ^ 1 + (26430191781688 / 12048786390813 : ℚ) * ((k : ℚ) + 4) ^ 2) * h1 - ((4517421252002768 / 469902669241707 : ℚ) + (2086211482533676 / 469902669241707 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-29950563699008 / 12048786390813 : ℚ) * ((k : ℚ) + 4) ^ 2) * h2 - ((3593445802283936 / 469902669241707 : ℚ) + (2311104978319552 / 469902669241707 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-52860383563376 / 12048786390813 : ℚ) * ((k : ℚ) + 4) ^ 2) * h3
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem main' : ∀ n : ℕ, 4 ≤ n → (26 * (n : ℚ) ^ 3 - 18 * (n : ℚ) ^ 2 - 128 * (n : ℚ) + 24) * a n
      + (24 * (n : ℚ) - 192) * a (n - 1)
      + (91 * (n : ℚ) ^ 3 - 375 * (n : ℚ) ^ 2 + 152 * (n : ℚ) + 372) * a (n - 2)
      + (-12 * (n : ℚ) + 96) * a (n - 3)
      + (-52 * (n : ℚ) ^ 3 + 192 * (n : ℚ) ^ 2 - 44 * (n : ℚ) - 192) * a (n - 4) = 0 := fun n hn => Mv_zero n hn

end OMA.P_oeis_a105524

theorem OMA.solution : type_of% @OMA.S_oeis_a105524.main := OMA.P_oeis_a105524.main'
