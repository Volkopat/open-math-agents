import OMAStatements.S_oeis_a273351
import Mathlib

-- Problem: A273351: Number of up steps in all bargraphs of semiperimeter n (n>=2).
-- Upstream: formal-conjectures statements/oeis-a273351.lean (declaration OMA.S_oeis_a273351.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: S = sqrt(R) satisfies S^2 = R, so 2 R S' = R' S (rel2). The series F = (A + B S) / C
-- satisfies C F = A + B S (rel1). Writing M(n) for the left side of the conjectured recurrence, an
-- explicit operator Q gives sum_i q_i(n) M(n + i) as a polynomial combination of shifted instances
-- of rel1 and rel2 (certQ, found by exact linear algebra), so M(n) = 0 follows by induction from the
-- first values, which are computed exactly from rel1 and rel2 (the leading q is nonzero there).

namespace OMA.P_oeis_a273351

open OMA.S_oeis_a273351 PowerSeries

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

theorem hRC : R = C (1 : ℚ) + C (-4 : ℚ) * X ^ 1 + C (2 : ℚ) * X ^ 2 + C (1 : ℚ) * X ^ 4 := by
  simp only [R, map_one, map_neg, map_ofNat]
  ring

theorem hDR : d⁄dX ℚ R = C (-4 : ℚ) + C (4 : ℚ) * X ^ 1 + C (4 : ℚ) * X ^ 3 := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  push_cast
  ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (-8 : ℚ) * X ^ 1 * d⁄dX ℚ S + C (4 : ℚ) * X ^ 2 * d⁄dX ℚ S + C (2 : ℚ) * X ^ 4 * d⁄dX ℚ S - (C (-4 : ℚ) * S + C (4 : ℚ) * X ^ 1 * S + C (4 : ℚ) * X ^ 3 * S) = 0 := by
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

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 5) S * ((m : ℚ) + 5)) + (-8 : ℚ) * (coeff (m + 4) S * ((m : ℚ) + 4)) + (4 : ℚ) * (coeff (m + 3) S * ((m : ℚ) + 3)) + (2 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((-4 : ℚ) * coeff (m + 4) S + (4 : ℚ) * coeff (m + 3) S + (4 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 4)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 4 - 1 = m + 3 from by omega, show m + 4 - 2 = m + 2 from by omega, show m + 4 - 3 = m + 1 from by omega, show m + 4 - 4 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := ((-1 + 3 * X + 2 * X ^ 2 - 2 * X ^ 3 - X ^ 4 - X ^ 5 + (1 - X - X ^ 2 - X ^ 3) * S) * (2 - 8 * X + 4 * X ^ 2 + 2 * X ^ 4 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = coeff n F := rfl

theorem hF : F * (2 - 8 * X + 4 * X ^ 2 + 2 * X ^ 4 : ℚ⟦X⟧) = -1 + 3 * X + 2 * X ^ 2 - 2 * X ^ 3 - X ^ 4 - X ^ 5 + (1 - X - X ^ 2 - X ^ 3) * S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (2 - 8 * X + 4 * X ^ 2 + 2 * X ^ 4 : ℚ⟦X⟧) = C (2 : ℚ) + C (-8 : ℚ) * X ^ 1 + C (4 : ℚ) * X ^ 2 + C (2 : ℚ) * X ^ 4 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (2 : ℚ) * F + C (-8 : ℚ) * X ^ 1 * F + C (4 : ℚ) * X ^ 2 * F + C (2 : ℚ) * X ^ 4 * F - (C (1 : ℚ) * S + C (-1 : ℚ) * X ^ 1 * S + C (-1 : ℚ) * X ^ 2 * S + C (-1 : ℚ) * X ^ 3 * S) - (C (-1 : ℚ) + C (3 : ℚ) * X ^ 1 + C (2 : ℚ) * X ^ 2 + C (-2 : ℚ) * X ^ 3 + C (-1 : ℚ) * X ^ 4 + C (-1 : ℚ) * X ^ 5) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (2 : ℚ) * coeff (m + 6) F + (-8 : ℚ) * coeff (m + 5) F + (4 : ℚ) * coeff (m + 4) F + (2 : ℚ) * coeff (m + 2) F - ((1 : ℚ) * coeff (m + 6) S + (-1 : ℚ) * coeff (m + 5) S + (-1 : ℚ) * coeff (m + 4) S + (-1 : ℚ) * coeff (m + 3) S) = 0 := by
  have h := congrArg (coeff (m + 6)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 6 - 1 = m + 5 from by omega, show m + 6 - 2 = m + 4 from by omega, show m + 6 - 3 = m + 3 from by omega, show m + 6 - 4 = m + 2 from by omega] at h
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

theorem hs4 : coeff 4 S = (-4 : ℚ) := by
  have h := congrArg (coeff 3) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3] at h ⊢ <;> linarith

theorem hs5 : coeff 5 S = (-10 : ℚ) := by
  have h := congrArg (coeff 4) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4] at h ⊢ <;> linarith

theorem hs6 : coeff 6 S = (-26 : ℚ) := by
  have h := congrArg (coeff 5) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5] at h ⊢ <;> linarith

theorem hs7 : coeff 7 S = (-70 : ℚ) := by
  have h := congrArg (coeff 6) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6] at h ⊢ <;> linarith

theorem hs8 : coeff 8 S = (-194 : ℚ) := by
  have h := congrArg (coeff 7) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7] at h ⊢ <;> linarith

theorem hs9 : coeff 9 S = (-550 : ℚ) := by
  have h := congrArg (coeff 8) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8] at h ⊢ <;> linarith

theorem hs10 : coeff 10 S = (-1588 : ℚ) := by
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

theorem hf1 : coeff 1 F = (0 : ℚ) := by
  have h := congrArg (coeff 1) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf0c] at h ⊢ <;> linarith

theorem hf2 : coeff 2 F = (1 : ℚ) := by
  have h := congrArg (coeff 2) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf0c] at h ⊢ <;> linarith

theorem hf3 : coeff 3 F = (3 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem hf4 : coeff 4 F = (10 : ℚ) := by
  have h := congrArg (coeff 4) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf0c] at h ⊢ <;> linarith

theorem hf5 : coeff 5 F = (32 : ℚ) := by
  have h := congrArg (coeff 5) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf0c] at h ⊢ <;> linarith

theorem hf6 : coeff 6 F = (102 : ℚ) := by
  have h := congrArg (coeff 6) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf0c] at h ⊢ <;> linarith

theorem hf7 : coeff 7 F = (326 : ℚ) := by
  have h := congrArg (coeff 7) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf0c] at h ⊢ <;> linarith

theorem hf8 : coeff 8 F = (1046 : ℚ) := by
  have h := congrArg (coeff 8) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf0c] at h ⊢ <;> linarith

theorem hf9 : coeff 9 F = (3370 : ℚ) := by
  have h := congrArg (coeff 9) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf0c] at h ⊢ <;> linarith

theorem hf10 : coeff 10 F = (10899 : ℚ) := by
  have h := congrArg (coeff 10) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hs8, hs9, hs10, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7, hf8, hf9, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (0 : ℚ) := by rw [a_eq]; exact hf0

theorem ha1 : a 1 = (0 : ℚ) := by rw [a_eq]; exact hf1

theorem ha2 : a 2 = (1 : ℚ) := by rw [a_eq]; exact hf2

theorem ha3 : a 3 = (3 : ℚ) := by rw [a_eq]; exact hf3

theorem ha4 : a 4 = (10 : ℚ) := by rw [a_eq]; exact hf4

theorem ha5 : a 5 = (32 : ℚ) := by rw [a_eq]; exact hf5

theorem ha6 : a 6 = (102 : ℚ) := by rw [a_eq]; exact hf6

theorem ha7 : a 7 = (326 : ℚ) := by rw [a_eq]; exact hf7

theorem ha8 : a 8 = (1046 : ℚ) := by rw [a_eq]; exact hf8

theorem ha9 : a 9 = (3370 : ℚ) := by rw [a_eq]; exact hf9

theorem ha10 : a 10 = (10899 : ℚ) := by rw [a_eq]; exact hf10

noncomputable def Mv (n : ℕ) : ℚ := (13 * (n : ℚ) ^ 2 - 40 * (n : ℚ)) * a n
      + (-55 * (n : ℚ) ^ 2 + 211 * (n : ℚ) - 129) * a (n - 1)
      + (38 * (n : ℚ) ^ 2 - 212 * (n : ℚ) + 255) * a (n - 2)
      + (-6 * (n : ℚ) ^ 2 + 56 * (n : ℚ) - 75) * a (n - 3)
      + (13 * (n : ℚ) ^ 2 - 66 * (n : ℚ) + 3) * a (n - 4)
      + (-3 * (n : ℚ) ^ 2 + 31 * (n : ℚ) - 78) * a (n - 5)

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

theorem certQ (k : ℕ) : ((77178 / 9841 : ℚ) + (767584 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 1 + (414208 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 2 + (111788 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 3 + (4 / 13 : ℚ) * ((k : ℚ) + 7) ^ 4) * Mv (k + 7) + ((541332 / 49205 : ℚ) + (721776 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 1 + (141372 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 2) * Mv (k + 8) + ((494748 / 49205 : ℚ) + (10404 / 757 : ℚ) * ((k : ℚ) + 7) ^ 1 + (297436 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 2 + (163016 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 3 + (8 / 13 : ℚ) * ((k : ℚ) + 7) ^ 4) * Mv (k + 9) + ((-691356 / 49205 : ℚ) + (-1536232 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-165980 / 9841 : ℚ) * ((k : ℚ) + 7) ^ 2 + (-265472 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 3 + (-16 / 13 : ℚ) * ((k : ℚ) + 7) ^ 4) * Mv (k + 10) + ((-64134 / 49205 : ℚ) + (213972 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 1 + (169684 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 2 + (51228 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 3 + (4 / 13 : ℚ) * ((k : ℚ) + 7) ^ 4) * Mv (k + 11) = 0 := by
  unfold Mv
  rw [show k + 7 - 1 = k + 6 from by omega, show k + 7 - 2 = k + 5 from by omega, show k + 7 - 3 = k + 4 from by omega, show k + 7 - 4 = k + 3 from by omega, show k + 7 - 5 = k + 2 from by omega, show k + 8 - 1 = k + 7 from by omega, show k + 8 - 2 = k + 6 from by omega, show k + 8 - 3 = k + 5 from by omega, show k + 8 - 4 = k + 4 from by omega, show k + 8 - 5 = k + 3 from by omega, show k + 9 - 1 = k + 8 from by omega, show k + 9 - 2 = k + 7 from by omega, show k + 9 - 3 = k + 6 from by omega, show k + 9 - 4 = k + 5 from by omega, show k + 9 - 5 = k + 4 from by omega, show k + 10 - 1 = k + 9 from by omega, show k + 10 - 2 = k + 8 from by omega, show k + 10 - 3 = k + 7 from by omega, show k + 10 - 4 = k + 6 from by omega, show k + 10 - 5 = k + 5 from by omega, show k + 11 - 1 = k + 10 from by omega, show k + 11 - 2 = k + 9 from by omega, show k + 11 - 3 = k + 8 from by omega, show k + 11 - 4 = k + 7 from by omega, show k + 11 - 5 = k + 6 from by omega]
  simp only [a_eq]
  have r1_49 := rel1 (k)
  have r1_50 := rel1 (k + 1)
  have r1_51 := rel1 (k + 2)
  have r1_52 := rel1 (k + 3)
  have r1_53 := rel1 (k + 4)
  have r1_54 := rel1 (k + 5)
  have r2_49 := rel2 (k + 2)
  have r2_50 := rel2 (k + 3)
  have r2_51 := rel2 (k + 4)
  have r2_52 := rel2 (k + 5)
  have r2_53 := rel2 (k + 6)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_49 r1_50 r1_51 r1_52 r1_53 r1_54 r2_49 r2_50 r2_51 r2_52 r2_53 ⊢
  push_cast at r1_49 r1_50 r1_51 r1_52 r1_53 r1_54 r2_49 r2_50 r2_51 r2_52 r2_53 ⊢
  linear_combination ((-231534 / 757 : ℚ) + (-23954481 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-967079 / 9841 : ℚ) * ((k : ℚ) + 7) ^ 2 + (69932 / 3785 : ℚ) * ((k : ℚ) + 7) ^ 3 + (520942 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 4 + (66988 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 5 + (-6 / 13 : ℚ) * ((k : ℚ) + 7) ^ 6) * r1_49 + ((-2590893 / 9841 : ℚ) + (-22860744 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-17524773 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 2 + (-1565480 / 9841 : ℚ) * ((k : ℚ) + 7) ^ 3 + (-237200 / 9841 : ℚ) * ((k : ℚ) + 7) ^ 4 + (227002 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 5 + (2 : ℚ) * ((k : ℚ) + 7) ^ 6) * r1_50 + ((-4831227 / 49205 : ℚ) + (-3709092 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 1 + (1539754 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 2 + (4677922 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 3 + (144254 / 3785 : ℚ) * ((k : ℚ) + 7) ^ 4 + (-2284 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 5 + (-12 / 13 : ℚ) * ((k : ℚ) + 7) ^ 6) * r1_51 + ((-6755247 / 49205 : ℚ) + (-3004476 / 9841 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-1992580 / 9841 : ℚ) * ((k : ℚ) + 7) ^ 2 + (-58502 / 9841 : ℚ) * ((k : ℚ) + 7) ^ 3 + (298302 / 9841 : ℚ) * ((k : ℚ) + 7) ^ 4 + (1185292 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 5 + (76 / 13 : ℚ) * ((k : ℚ) + 7) ^ 6) * r1_52 + ((34245 / 9841 : ℚ) + (-8808603 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-5432363 / 9841 : ℚ) * ((k : ℚ) + 7) ^ 2 + (-22694046 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 3 + (-9706036 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 4 + (-549732 / 9841 : ℚ) * ((k : ℚ) + 7) ^ 5 + (-110 / 13 : ℚ) * ((k : ℚ) + 7) ^ 6) * r1_53 + ((-1539216 / 49205 : ℚ) + (616608 / 9841 : ℚ) * ((k : ℚ) + 7) ^ 1 + (10502649 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 2 + (8050178 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 3 + (3105602 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 4 + (817462 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 5 + (2 : ℚ) * ((k : ℚ) + 7) ^ 6) * r1_54 + ((-38589 / 1514 : ℚ) + (-4410461 / 98410 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-770488 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 2 + (-10531 / 9841 : ℚ) * ((k : ℚ) + 7) ^ 3 + (34636 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 4 + (3 / 13 : ℚ) * ((k : ℚ) + 7) ^ 5) * r2_49 + ((-1120167 / 19682 : ℚ) + (-5241606 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-3284338 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 2 + (-1348696 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 3 + (-5173 / 757 : ℚ) * ((k : ℚ) + 7) ^ 4 + (-10 / 13 : ℚ) * ((k : ℚ) + 7) ^ 5) * r2_50 + ((-4446423 / 98410 : ℚ) + (-4190568 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-3597077 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 2 + (-1485576 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 3 + (-59679 / 9841 : ℚ) * ((k : ℚ) + 7) ^ 4 + (-10 / 13 : ℚ) * ((k : ℚ) + 7) ^ 5) * r2_51 + ((-712533 / 98410 : ℚ) + (-674786 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-1459638 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 2 + (-136204 / 9841 : ℚ) * ((k : ℚ) + 7) ^ 3 + (-261687 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 4 + (-16 / 13 : ℚ) * ((k : ℚ) + 7) ^ 5) * r2_52 + ((-192402 / 49205 : ℚ) + (866961 / 98410 : ℚ) * ((k : ℚ) + 7) ^ 1 + (1204461 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 2 + (705157 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 3 + (211911 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 4 + (1 : ℚ) * ((k : ℚ) + 7) ^ 5) * r2_53

theorem Mv_zero : ∀ n : ℕ, 7 ≤ n → Mv n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 11
    · interval_cases n
      · exact base7
      · exact base8
      · exact base9
      · exact base10
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 11 := ⟨n - 11, by omega⟩
      have hc := certQ k
      have h0 : Mv (k + 7) = 0 := ih _ (by omega) (by omega)
      have h1 : Mv (k + 8) = 0 := ih _ (by omega) (by omega)
      have h2 : Mv (k + 9) = 0 := ih _ (by omega) (by omega)
      have h3 : Mv (k + 10) = 0 := ih _ (by omega) (by omega)
      have hq : ((-64134 / 49205 : ℚ) + (213972 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 1 + (169684 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 2 + (51228 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 3 + (4 / 13 : ℚ) * ((k : ℚ) + 7) ^ 4) ≠ 0 := by
        have e : ((-64134 / 49205 : ℚ) + (213972 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 1 + (169684 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 2 + (51228 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 3 + (4 / 13 : ℚ) * ((k : ℚ) + 7) ^ 4) = (12734106 / 9841 : ℚ) + (30892144 / 49205 : ℚ) * (k : ℚ) ^ 1 + (5696632 / 49205 : ℚ) * (k : ℚ) ^ 2 + (475148 / 49205 : ℚ) * (k : ℚ) ^ 3 + (4 / 13 : ℚ) * (k : ℚ) ^ 4 := by ring
        rw [e]
        positivity
      have hm : ((-64134 / 49205 : ℚ) + (213972 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 1 + (169684 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 2 + (51228 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 3 + (4 / 13 : ℚ) * ((k : ℚ) + 7) ^ 4) * Mv (k + 11) = 0 := by linear_combination hc - ((77178 / 9841 : ℚ) + (767584 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 1 + (414208 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 2 + (111788 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 3 + (4 / 13 : ℚ) * ((k : ℚ) + 7) ^ 4) * h0 - ((541332 / 49205 : ℚ) + (721776 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 1 + (141372 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 2) * h1 - ((494748 / 49205 : ℚ) + (10404 / 757 : ℚ) * ((k : ℚ) + 7) ^ 1 + (297436 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 2 + (163016 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 3 + (8 / 13 : ℚ) * ((k : ℚ) + 7) ^ 4) * h2 - ((-691356 / 49205 : ℚ) + (-1536232 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 1 + (-165980 / 9841 : ℚ) * ((k : ℚ) + 7) ^ 2 + (-265472 / 49205 : ℚ) * ((k : ℚ) + 7) ^ 3 + (-16 / 13 : ℚ) * ((k : ℚ) + 7) ^ 4) * h3
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem main' : ∀ n : ℕ, 7 ≤ n → (13 * (n : ℚ) ^ 2 - 40 * (n : ℚ)) * a n
      + (-55 * (n : ℚ) ^ 2 + 211 * (n : ℚ) - 129) * a (n - 1)
      + (38 * (n : ℚ) ^ 2 - 212 * (n : ℚ) + 255) * a (n - 2)
      + (-6 * (n : ℚ) ^ 2 + 56 * (n : ℚ) - 75) * a (n - 3)
      + (13 * (n : ℚ) ^ 2 - 66 * (n : ℚ) + 3) * a (n - 4)
      + (-3 * (n : ℚ) ^ 2 + 31 * (n : ℚ) - 78) * a (n - 5) = 0 := fun n hn => Mv_zero n hn

end OMA.P_oeis_a273351

theorem OMA.solution : type_of% @OMA.S_oeis_a273351.main := OMA.P_oeis_a273351.main'
