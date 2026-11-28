import OMAStatements.S_oeis_a128726
import Mathlib

-- Problem: A128726: Number of LL's in all skew Dyck paths of semilength n.
-- Upstream: formal-conjectures statements/oeis-a128726.lean (declaration OMA.S_oeis_a128726.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: S = sqrt(R) satisfies S^2 = R, so 2 R S' = R' S (rel2). The series F = (A + B S) / C
-- satisfies C F = A + B S (rel1). Writing M(n) for the left side of the conjectured recurrence, an
-- explicit operator Q gives sum_i q_i(n) M(n + i) as a polynomial combination of shifted instances
-- of rel1 and rel2 (certQ, found by exact linear algebra), so M(n) = 0 follows by induction from the
-- first values, which are computed exactly from rel1 and rel2 (the leading q is nonzero there).

namespace OMA.P_oeis_a128726

open OMA.S_oeis_a128726 PowerSeries

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

theorem hRC : R = C (1 : ℚ) + C (-6 : ℚ) * X ^ 1 + C (5 : ℚ) * X ^ 2 := by
  simp only [R, map_one, map_neg, map_ofNat] <;> ring

theorem hDR : d⁄dX ℚ R = C (-6 : ℚ) + C (10 : ℚ) * X ^ 1 := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  try push_cast
  try ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (-12 : ℚ) * X ^ 1 * d⁄dX ℚ S + C (10 : ℚ) * X ^ 2 * d⁄dX ℚ S - (C (-6 : ℚ) * S + C (10 : ℚ) * X ^ 1 * S) = 0 := by
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

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 3) S * ((m : ℚ) + 3)) + (-12 : ℚ) * (coeff (m + 2) S * ((m : ℚ) + 2)) + (10 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((-6 : ℚ) * coeff (m + 2) S + (10 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 2)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 2 - 1 = m + 1 from by omega, show m + 2 - 2 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := ((-2 + 15 * X - 29 * X ^ 2 + 21 * X ^ 3 - 5 * X ^ 4 + (2 - 9 * X + 6 * X ^ 2 - X ^ 3) * S) * (8 - 56 * X + 90 * X ^ 2 - 52 * X ^ 3 + 10 * X ^ 4 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = coeff n F := rfl

theorem hF : F * (8 - 56 * X + 90 * X ^ 2 - 52 * X ^ 3 + 10 * X ^ 4 : ℚ⟦X⟧) = -2 + 15 * X - 29 * X ^ 2 + 21 * X ^ 3 - 5 * X ^ 4 + (2 - 9 * X + 6 * X ^ 2 - X ^ 3) * S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (8 - 56 * X + 90 * X ^ 2 - 52 * X ^ 3 + 10 * X ^ 4 : ℚ⟦X⟧) = C (8 : ℚ) + C (-56 : ℚ) * X ^ 1 + C (90 : ℚ) * X ^ 2 + C (-52 : ℚ) * X ^ 3 + C (10 : ℚ) * X ^ 4 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (8 : ℚ) * F + C (-56 : ℚ) * X ^ 1 * F + C (90 : ℚ) * X ^ 2 * F + C (-52 : ℚ) * X ^ 3 * F + C (10 : ℚ) * X ^ 4 * F - (C (2 : ℚ) * S + C (-9 : ℚ) * X ^ 1 * S + C (6 : ℚ) * X ^ 2 * S + C (-1 : ℚ) * X ^ 3 * S) - (C (-2 : ℚ) + C (15 : ℚ) * X ^ 1 + C (-29 : ℚ) * X ^ 2 + C (21 : ℚ) * X ^ 3 + C (-5 : ℚ) * X ^ 4) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (8 : ℚ) * coeff (m + 5) F + (-56 : ℚ) * coeff (m + 4) F + (90 : ℚ) * coeff (m + 3) F + (-52 : ℚ) * coeff (m + 2) F + (10 : ℚ) * coeff (m + 1) F - ((2 : ℚ) * coeff (m + 5) S + (-9 : ℚ) * coeff (m + 4) S + (6 : ℚ) * coeff (m + 3) S + (-1 : ℚ) * coeff (m + 2) S) = 0 := by
  have h := congrArg (coeff (m + 5)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 5 - 1 = m + 4 from by omega, show m + 5 - 2 = m + 3 from by omega, show m + 5 - 3 = m + 2 from by omega, show m + 5 - 4 = m + 1 from by omega] at h
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

theorem hs1 : coeff 1 S = (-3 : ℚ) := by
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

theorem hs3 : coeff 3 S = (-6 : ℚ) := by
  have h := congrArg (coeff 2) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2] at h ⊢ <;> linarith

theorem hs4 : coeff 4 S = (-20 : ℚ) := by
  have h := congrArg (coeff 3) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3] at h ⊢ <;> linarith

theorem hs5 : coeff 5 S = (-72 : ℚ) := by
  have h := congrArg (coeff 4) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4] at h ⊢ <;> linarith

theorem hs6 : coeff 6 S = (-274 : ℚ) := by
  have h := congrArg (coeff 5) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5] at h ⊢ <;> linarith

theorem hs7 : coeff 7 S = (-1086 : ℚ) := by
  have h := congrArg (coeff 6) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6] at h ⊢ <;> linarith

theorem hf0 : coeff 0 F = (0 : ℚ) := by
  have h := congrArg (coeff 0) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7] at h ⊢ <;> linarith

theorem hf0c : constantCoeff F = (0 : ℚ) := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf0

theorem hf1 : coeff 1 F = (0 : ℚ) := by
  have h := congrArg (coeff 1) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hf0, hf0c] at h ⊢ <;> linarith

theorem hf2 : coeff 2 F = (0 : ℚ) := by
  have h := congrArg (coeff 2) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hf0, hf1, hf0c] at h ⊢ <;> linarith

theorem hf3 : coeff 3 F = (1 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem hf4 : coeff 4 F = (7 : ℚ) := by
  have h := congrArg (coeff 4) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hf0, hf1, hf2, hf3, hf0c] at h ⊢ <;> linarith

theorem hf5 : coeff 5 F = (38 : ℚ) := by
  have h := congrArg (coeff 5) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hf0, hf1, hf2, hf3, hf4, hf0c] at h ⊢ <;> linarith

theorem hf6 : coeff 6 F = (192 : ℚ) := by
  have h := congrArg (coeff 6) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hf0, hf1, hf2, hf3, hf4, hf5, hf0c] at h ⊢ <;> linarith

theorem hf7 : coeff 7 F = (946 : ℚ) := by
  have h := congrArg (coeff 7) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hs6, hs7, hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (0 : ℚ) := by rw [a_eq]; exact hf0

theorem ha1 : a 1 = (0 : ℚ) := by rw [a_eq]; exact hf1

theorem ha2 : a 2 = (0 : ℚ) := by rw [a_eq]; exact hf2

theorem ha3 : a 3 = (1 : ℚ) := by rw [a_eq]; exact hf3

theorem ha4 : a 4 = (7 : ℚ) := by rw [a_eq]; exact hf4

theorem ha5 : a 5 = (38 : ℚ) := by rw [a_eq]; exact hf5

theorem ha6 : a 6 = (192 : ℚ) := by rw [a_eq]; exact hf6

theorem ha7 : a 7 = (946 : ℚ) := by rw [a_eq]; exact hf7

noncomputable def Mv (n : ℕ) : ℚ := (2 * (n : ℚ) ^ 3 - 12 * (n : ℚ) ^ 2 + 18 * (n : ℚ)) * a n
      + (-13 * (n : ℚ) ^ 3 + 84 * (n : ℚ) ^ 2 - 167 * (n : ℚ) + 100) * a (n - 1)
      + (16 * (n : ℚ) ^ 3 - 109 * (n : ℚ) ^ 2 + 239 * (n : ℚ) - 170) * a (n - 2)
      + (-5 * (n : ℚ) ^ 3 + 35 * (n : ℚ) ^ 2 - 80 * (n : ℚ) + 60) * a (n - 3)

theorem base3 : Mv 3 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5, ha6, ha7]

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

theorem certQ (k : ℕ) : ((1584534957600 / 309018266549 : ℚ) + (786305964970 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-7508257690140 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (4253333896570 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 3) * Mv (k + 4) + ((-16886615405280 / 309018266549 : ℚ) + (-25639079492906 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (56518714469516 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (-16700851134514 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 3) * Mv (k + 5) + ((-14268136704276 / 309018266549 : ℚ) + (84393753578442 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-89567390676192 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (20947252660650 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 3) * Mv (k + 6) + ((1265895566484 / 309018266549 : ℚ) + (-47804202508754 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (46054117442412 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (-9735808488902 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 3) * Mv (k + 7) + ((-4038300520512 / 309018266549 : ℚ) + (12140798600680 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-7358225515324 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (4 : ℚ) * ((k : ℚ) + 4) ^ 3) * Mv (k + 8) = 0 := by
  unfold Mv
  rw [show k + 4 - 1 = k + 3 from by omega, show k + 4 - 2 = k + 2 from by omega, show k + 4 - 3 = k + 1 from by omega, show k + 5 - 1 = k + 4 from by omega, show k + 5 - 2 = k + 3 from by omega, show k + 5 - 3 = k + 2 from by omega, show k + 6 - 1 = k + 5 from by omega, show k + 6 - 2 = k + 4 from by omega, show k + 6 - 3 = k + 3 from by omega, show k + 7 - 1 = k + 6 from by omega, show k + 7 - 2 = k + 5 from by omega, show k + 7 - 3 = k + 4 from by omega, show k + 8 - 1 = k + 7 from by omega, show k + 8 - 2 = k + 6 from by omega, show k + 8 - 3 = k + 5 from by omega]
  simp only [a_eq]
  have r1_51 := rel1 (k)
  have r1_52 := rel1 (k + 1)
  have r1_53 := rel1 (k + 2)
  have r1_54 := rel1 (k + 3)
  have r2_49 := rel2 (k + 1)
  have r2_50 := rel2 (k + 2)
  have r2_51 := rel2 (k + 3)
  have r2_52 := rel2 (k + 4)
  have r2_53 := rel2 (k + 5)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_51 r1_52 r1_53 r1_54 r2_49 r2_50 r2_51 r2_52 r2_53 ⊢
  push_cast at r1_51 r1_52 r1_53 r1_54 r2_49 r2_50 r2_51 r2_52 r2_53 ⊢
  linear_combination ((9507209745600 / 309018266549 : ℚ) + (-7958443870980 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-45794121509000 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (87545868299135 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 3 + (-60698726070535 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 4 + (18640797483065 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 5 + (-2126666948285 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 6) * r1_51 + ((181089709440 / 9968331179 : ℚ) + (-303265026652 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-22124587198256 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (-3383487558023 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 3 + (36728499449489 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 4 + (-23103464368685 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 5 + (4097091670687 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 6) * r1_52 + ((-3533512955448 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (5515169669690 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (-24268714979897 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 3 + (14151362939641 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 4 + (5146004403805 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 5 + (-2279442988951 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 6) * r1_53 + ((-4038300520512 / 309018266549 : ℚ) + (3054622429528 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (13901120555438 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (1881688427609 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 3 + (-5220974223875 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 4 + (14553220463 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 5 + (1 : ℚ) * ((k : ℚ) + 4) ^ 6) * r1_54 + ((316906991520 / 309018266549 : ℚ) + (-159645798526 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-1579685983142 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (4783267231181 / 618036533098 : ℚ) * ((k : ℚ) + 4) ^ 3 + (-1226079663821 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 4 + (425333389657 / 618036533098 : ℚ) * ((k : ℚ) + 4) ^ 5) * r2_49 + ((-2286257581680 / 309018266549 : ℚ) + (895415705536 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (11753785039843 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (-34911521007607 / 618036533098 : ℚ) * ((k : ℚ) + 4) ^ 3 + (8779710674940 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 4 + (-2861018604491 / 618036533098 : ℚ) * ((k : ℚ) + 4) ^ 5) * r2_50 + ((3816465626448 / 309018266549 : ℚ) + (-173386217346 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-21615983271966 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (63769167374715 / 618036533098 : ℚ) * ((k : ℚ) + 4) ^ 3 + (-537844110297 / 9968331179 : ℚ) * ((k : ℚ) + 4) ^ 4 + (5682110106207 / 618036533098 : ℚ) * ((k : ℚ) + 4) ^ 5) * r2_51 + ((1009575130128 / 309018266549 : ℚ) + (-3035199650170 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (136880010196 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (-12379339186795 / 618036533098 : ℚ) * ((k : ℚ) + 4) ^ 3 + (7834416602941 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 4 + (-3631831178255 / 618036533098 : ℚ) * ((k : ℚ) + 4) ^ 5) * r2_52 + ((-1009575130128 / 309018266549 : ℚ) + (1016049389914 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (3221267791381 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (-334894840943 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 3 + (-1221519845733 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 4 + (1 : ℚ) * ((k : ℚ) + 4) ^ 5) * r2_53

theorem Mv_zero : ∀ n : ℕ, 3 ≤ n → Mv n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 8
    · interval_cases n
      · exact base3
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
      have hq : ((-4038300520512 / 309018266549 : ℚ) + (12140798600680 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-7358225515324 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (4 : ℚ) * ((k : ℚ) + 4) ^ 3) ≠ 0 := by
        have e : ((-4038300520512 / 309018266549 : ℚ) + (12140798600680 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-7358225515324 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (4 : ℚ) * ((k : ℚ) + 4) ^ 3) = (5901961873568 / 309018266549 : ℚ) + (12606501655496 / 309018266549 : ℚ) * (k : ℚ) ^ 1 + (7474651279028 / 309018266549 : ℚ) * (k : ℚ) ^ 2 + (4 : ℚ) * (k : ℚ) ^ 3 := by ring
        rw [e]
        positivity
      have hm : ((-4038300520512 / 309018266549 : ℚ) + (12140798600680 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-7358225515324 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (4 : ℚ) * ((k : ℚ) + 4) ^ 3) * Mv (k + 8) = 0 := by linear_combination hc - ((1584534957600 / 309018266549 : ℚ) + (786305964970 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-7508257690140 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (4253333896570 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 3) * h0 - ((-16886615405280 / 309018266549 : ℚ) + (-25639079492906 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (56518714469516 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (-16700851134514 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 3) * h1 - ((-14268136704276 / 309018266549 : ℚ) + (84393753578442 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (-89567390676192 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (20947252660650 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 3) * h2 - ((1265895566484 / 309018266549 : ℚ) + (-47804202508754 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 1 + (46054117442412 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 2 + (-9735808488902 / 309018266549 : ℚ) * ((k : ℚ) + 4) ^ 3) * h3
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem main' : ∀ n : ℕ, 3 ≤ n → (2 * (n : ℚ) ^ 3 - 12 * (n : ℚ) ^ 2 + 18 * (n : ℚ)) * a n
      + (-13 * (n : ℚ) ^ 3 + 84 * (n : ℚ) ^ 2 - 167 * (n : ℚ) + 100) * a (n - 1)
      + (16 * (n : ℚ) ^ 3 - 109 * (n : ℚ) ^ 2 + 239 * (n : ℚ) - 170) * a (n - 2)
      + (-5 * (n : ℚ) ^ 3 + 35 * (n : ℚ) ^ 2 - 80 * (n : ℚ) + 60) * a (n - 3) = 0 := fun n hn => Mv_zero n hn

end OMA.P_oeis_a128726

theorem OMA.solution : type_of% @OMA.S_oeis_a128726.main := OMA.P_oeis_a128726.main'
