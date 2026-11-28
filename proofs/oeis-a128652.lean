import OMAStatements.S_oeis_a128652
import Mathlib

-- Problem: A128652: Number of square permutations of length n.
-- Upstream: formal-conjectures statements/oeis-a128652.lean (declaration OMA.S_oeis_a128652.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: false as stated at n = 3; proved here for the corrected recurrence (n >= 4).
-- Proof idea: S = sqrt(R) satisfies S^2 = R, so 2 R S' = R' S (rel2). The series F = (A + B S) / C
-- satisfies C F = A + B S (rel1). Writing M(n) for the left side of the conjectured recurrence, an
-- explicit operator Q gives sum_i q_i(n) M(n + i) as a polynomial combination of shifted instances
-- of rel1 and rel2 (certQ, found by exact linear algebra), so M(n) = 0 follows by induction from the
-- first values, which are computed exactly from rel1 and rel2 (the leading q is nonzero there).

namespace OMA.P_oeis_a128652

open OMA.S_oeis_a128652 PowerSeries

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

noncomputable def F : ℚ⟦X⟧ := ((X - 14 * X ^ 2 + 74 * X ^ 3 - 176 * X ^ 4 + 160 * X ^ 5 + (-4 * X ^ 3 + 32 * X ^ 4 - 64 * X ^ 5) * S) * (1 - 16 * X + 96 * X ^ 2 - 256 * X ^ 3 + 256 * X ^ 4 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = coeff n F := rfl

theorem hF : F * (1 - 16 * X + 96 * X ^ 2 - 256 * X ^ 3 + 256 * X ^ 4 : ℚ⟦X⟧) = X - 14 * X ^ 2 + 74 * X ^ 3 - 176 * X ^ 4 + 160 * X ^ 5 + (-4 * X ^ 3 + 32 * X ^ 4 - 64 * X ^ 5) * S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (1 - 16 * X + 96 * X ^ 2 - 256 * X ^ 3 + 256 * X ^ 4 : ℚ⟦X⟧) = C (1 : ℚ) + C (-16 : ℚ) * X ^ 1 + C (96 : ℚ) * X ^ 2 + C (-256 : ℚ) * X ^ 3 + C (256 : ℚ) * X ^ 4 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (1 : ℚ) * F + C (-16 : ℚ) * X ^ 1 * F + C (96 : ℚ) * X ^ 2 * F + C (-256 : ℚ) * X ^ 3 * F + C (256 : ℚ) * X ^ 4 * F - (C (-4 : ℚ) * X ^ 3 * S + C (32 : ℚ) * X ^ 4 * S + C (-64 : ℚ) * X ^ 5 * S) - (C (1 : ℚ) * X ^ 1 + C (-14 : ℚ) * X ^ 2 + C (74 : ℚ) * X ^ 3 + C (-176 : ℚ) * X ^ 4 + C (160 : ℚ) * X ^ 5) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (1 : ℚ) * coeff (m + 6) F + (-16 : ℚ) * coeff (m + 5) F + (96 : ℚ) * coeff (m + 4) F + (-256 : ℚ) * coeff (m + 3) F + (256 : ℚ) * coeff (m + 2) F - ((-4 : ℚ) * coeff (m + 3) S + (32 : ℚ) * coeff (m + 2) S + (-64 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 6)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 6 - 1 = m + 5 from by omega, show m + 6 - 2 = m + 4 from by omega, show m + 6 - 3 = m + 3 from by omega, show m + 6 - 4 = m + 2 from by omega, show m + 6 - 5 = m + 1 from by omega] at h
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

theorem hf0 : coeff 0 F = (0 : ℚ) := by
  have h := congrArg (coeff 0) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10] at h ⊢ <;> linarith

theorem hf0c : constantCoeff F = (0 : ℚ) := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf0

theorem hf1 : coeff 1 F = (1 : ℚ) := by
  have h := congrArg (coeff 1) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf0c] at h ⊢ <;> linarith

theorem hf2 : coeff 2 F = (2 : ℚ) := by
  have h := congrArg (coeff 2) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf0c] at h ⊢ <;> linarith

theorem hf3 : coeff 3 F = (6 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem hf4 : coeff 4 F = (24 : ℚ) := by
  have h := congrArg (coeff 4) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf0c] at h ⊢ <;> linarith

theorem hf5 : coeff 5 F = (104 : ℚ) := by
  have h := congrArg (coeff 5) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf0c] at h ⊢ <;> linarith

theorem hf6 : coeff 6 F = (464 : ℚ) := by
  have h := congrArg (coeff 6) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf0c] at h ⊢ <;> linarith

theorem hf7 : coeff 7 F = (2088 : ℚ) := by
  have h := congrArg (coeff 7) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf0c] at h ⊢ <;> linarith

theorem hf8 : coeff 8 F = (9392 : ℚ) := by
  have h := congrArg (coeff 8) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf0c] at h ⊢ <;> linarith

theorem hf9 : coeff 9 F = (42064 : ℚ) := by
  have h := congrArg (coeff 9) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf0c] at h ⊢ <;> linarith

theorem hf10 : coeff 10 F = (187296 : ℚ) := by
  have h := congrArg (coeff 10) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (0 : ℚ) := by rw [a_eq]; exact hf0

theorem ha1 : a 1 = (1 : ℚ) := by rw [a_eq]; exact hf1

theorem ha2 : a 2 = (2 : ℚ) := by rw [a_eq]; exact hf2

theorem ha3 : a 3 = (6 : ℚ) := by rw [a_eq]; exact hf3

theorem ha4 : a 4 = (24 : ℚ) := by rw [a_eq]; exact hf4

theorem ha5 : a 5 = (104 : ℚ) := by rw [a_eq]; exact hf5

theorem ha6 : a 6 = (464 : ℚ) := by rw [a_eq]; exact hf6

theorem ha7 : a 7 = (2088 : ℚ) := by rw [a_eq]; exact hf7

theorem ha8 : a 8 = (9392 : ℚ) := by rw [a_eq]; exact hf8

theorem ha9 : a 9 = (42064 : ℚ) := by rw [a_eq]; exact hf9

theorem ha10 : a 10 = (187296 : ℚ) := by rw [a_eq]; exact hf10

noncomputable def Mv (n : ℕ) : ℚ := ((n : ℚ) ^ 2 - 11 * (n : ℚ) + 24) * a n + (-8 * (n : ℚ) ^ 2 + 86 * (n : ℚ) - 192) * a (n - 1)
      + (16 * (n : ℚ) ^ 2 - 168 * (n : ℚ) + 392) * a (n - 2)

theorem base4 : Mv 4 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10]

theorem base5 : Mv 5 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10]

theorem base6 : Mv 6 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10]

theorem base7 : Mv 7 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10]

theorem base8 : Mv 8 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10]

theorem base9 : Mv 9 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10]

theorem base10 : Mv 10 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7, ha8, ha9, ha10]

theorem certQ (k : ℕ) : ((960 : ℚ) + (-352 : ℚ) * ((k : ℚ) + 8) ^ 1 + (32 : ℚ) * ((k : ℚ) + 8) ^ 2) * Mv (k + 8) + ((-800 : ℚ) + (280 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-24 : ℚ) * ((k : ℚ) + 8) ^ 2) * Mv (k + 9) + ((224 : ℚ) + (-74 : ℚ) * ((k : ℚ) + 8) ^ 1 + (6 : ℚ) * ((k : ℚ) + 8) ^ 2) * Mv (k + 10) + ((-21 : ℚ) + (13 / 2 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-1 / 2 : ℚ) * ((k : ℚ) + 8) ^ 2) * Mv (k + 11) = 0 := by
  unfold Mv
  rw [show k + 8 - 1 = k + 7 from by omega, show k + 8 - 2 = k + 6 from by omega, show k + 9 - 1 = k + 8 from by omega, show k + 9 - 2 = k + 7 from by omega, show k + 10 - 1 = k + 9 from by omega, show k + 10 - 2 = k + 8 from by omega, show k + 11 - 1 = k + 10 from by omega, show k + 11 - 2 = k + 9 from by omega]
  simp only [a_eq]
  have r1_52 := rel1 (k + 4)
  have r1_53 := rel1 (k + 5)
  have r2_47 := rel2 (k + 4)
  have r2_48 := rel2 (k + 5)
  have r2_49 := rel2 (k + 6)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_52 r1_53 r2_47 r2_48 r2_49 ⊢
  push_cast at r1_52 r1_53 r2_47 r2_48 r2_49 ⊢
  linear_combination ((1470 : ℚ) + (-1169 : ℚ) * ((k : ℚ) + 8) ^ 1 + (340 : ℚ) * ((k : ℚ) + 8) ^ 2 + (-43 : ℚ) * ((k : ℚ) + 8) ^ 3 + (2 : ℚ) * ((k : ℚ) + 8) ^ 4) * r1_52 + ((105 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-107 / 2 : ℚ) * ((k : ℚ) + 8) ^ 2 + (9 : ℚ) * ((k : ℚ) + 8) ^ 3 + (-1 / 2 : ℚ) * ((k : ℚ) + 8) ^ 4) * r1_53 + ((-3360 : ℚ) + (1712 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-288 : ℚ) * ((k : ℚ) + 8) ^ 2 + (16 : ℚ) * ((k : ℚ) + 8) ^ 3) * r2_47 + ((1680 : ℚ) + (-856 : ℚ) * ((k : ℚ) + 8) ^ 1 + (144 : ℚ) * ((k : ℚ) + 8) ^ 2 + (-8 : ℚ) * ((k : ℚ) + 8) ^ 3) * r2_48 + ((-210 : ℚ) + (107 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-18 : ℚ) * ((k : ℚ) + 8) ^ 2 + (1 : ℚ) * ((k : ℚ) + 8) ^ 3) * r2_49

theorem Mv_zero : ∀ n : ℕ, 4 ≤ n → Mv n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 11
    · interval_cases n
      · exact base4
      · exact base5
      · exact base6
      · exact base7
      · exact base8
      · exact base9
      · exact base10
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
      have hc := certQ k
      have h0 : Mv (k + 8) = 0 := ih _ (by omega) (by omega)
      have h1 : Mv (k + 9) = 0 := ih _ (by omega) (by omega)
      have h2 : Mv (k + 10) = 0 := ih _ (by omega) (by omega)
      have hq : ((-21 : ℚ) + (13 / 2 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-1 / 2 : ℚ) * ((k : ℚ) + 8) ^ 2) ≠ 0 := by
        have e : ((-21 : ℚ) + (13 / 2 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-1 / 2 : ℚ) * ((k : ℚ) + 8) ^ 2) = -((1 : ℚ) + (3 / 2 : ℚ) * (k : ℚ) ^ 1 + (1 / 2 : ℚ) * (k : ℚ) ^ 2) := by ring
        rw [e, neg_ne_zero]
        positivity
      have hm : ((-21 : ℚ) + (13 / 2 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-1 / 2 : ℚ) * ((k : ℚ) + 8) ^ 2) * Mv (k + 11) = 0 := by linear_combination hc - ((960 : ℚ) + (-352 : ℚ) * ((k : ℚ) + 8) ^ 1 + (32 : ℚ) * ((k : ℚ) + 8) ^ 2) * h0 - ((-800 : ℚ) + (280 : ℚ) * ((k : ℚ) + 8) ^ 1 + (-24 : ℚ) * ((k : ℚ) + 8) ^ 2) * h1 - ((224 : ℚ) + (-74 : ℚ) * ((k : ℚ) + 8) ^ 1 + (6 : ℚ) * ((k : ℚ) + 8) ^ 2) * h2
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem main' : ∀ n : ℕ, 4 ≤ n → ((n : ℚ) ^ 2 - 11 * (n : ℚ) + 24) * a n + (-8 * (n : ℚ) ^ 2 + 86 * (n : ℚ) - 192) * a (n - 1)
      + (16 * (n : ℚ) ^ 2 - 168 * (n : ℚ) + 392) * a (n - 2) = 0 := fun n hn => Mv_zero n hn

end OMA.P_oeis_a128652

theorem OMA.solution : type_of% @OMA.S_oeis_a128652.main := OMA.P_oeis_a128652.main'
