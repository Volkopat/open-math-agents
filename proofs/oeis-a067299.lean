import OMAStatements.S_oeis_a067299
import Mathlib

-- Problem: A067299: Second column of triangle A067298.
-- Upstream: formal-conjectures statements/oeis-a067299.lean (declaration OMA.S_oeis_a067299.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the conjectured recurrence holds for the series as defined).
-- Proof idea: S = sqrt(R) satisfies S^2 = R, so 2 R S' = R' S (rel2). The series F = (A + B S) / C
-- satisfies C F = A + B S (rel1). Writing M(n) for the left side of the conjectured recurrence, an
-- explicit operator Q gives sum_i q_i(n) M(n + i) as a polynomial combination of shifted instances
-- of rel1 and rel2 (certQ, found by exact linear algebra), so M(n) = 0 follows by induction from the
-- first values, which are computed exactly from rel1 and rel2 (the leading q is nonzero there).

namespace OMA.P_oeis_a067299

open OMA.S_oeis_a067299 PowerSeries

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

theorem hRC : R = C (1 : ℚ) + C (-16 : ℚ) * X ^ 1 := by
  simp only [R, map_one, map_neg, map_ofNat] <;> ring

theorem hDR : d⁄dX ℚ R = C (-16 : ℚ) := by
  rw [hRC]
  simp only [map_add, Derivation.leibniz, derivative_C, derivative_pow, derivative_X, smul_eq_mul,
    mul_zero, add_zero, Nat.reduceSub, pow_one, mul_one]
  simp only [map_one, map_neg, map_ofNat]
  try push_cast
  try ring

theorem E2 : C (2 : ℚ) * d⁄dX ℚ S + C (-32 : ℚ) * X ^ 1 * d⁄dX ℚ S - (C (-16 : ℚ) * S) = 0 := by
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

theorem rel2 (m : ℕ) : (2 : ℚ) * (coeff (m + 2) S * ((m : ℚ) + 2)) + (-32 : ℚ) * (coeff (m + 1) S * ((m : ℚ) + 1)) - ((-16 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 1)) E2
  simp (disch := omega) only [map_add, map_sub, map_zero, cx, cx0, coeff_derivative] at h
  rw [show m + 1 - 1 = m from by omega] at h
  try simp only [Nat.add_assoc, Nat.reduceAdd] at h
  try push_cast at h
  linear_combination h

noncomputable def F : ℚ⟦X⟧ := ((7 + 33 * X + 48 * X ^ 2 + 20 * X ^ 3 + (-3 - 15 * X - 24 * X ^ 2 - 12 * X ^ 3) * S) * (2 + 16 * X + 48 * X ^ 2 + 64 * X ^ 3 + 32 * X ^ 4 : PowerSeries ℚ)⁻¹)

theorem a_eq (n : ℕ) : a n = coeff n F := rfl

theorem hF : F * (2 + 16 * X + 48 * X ^ 2 + 64 * X ^ 3 + 32 * X ^ 4 : ℚ⟦X⟧) = 7 + 33 * X + 48 * X ^ 2 + 20 * X ^ 3 + (-3 - 15 * X - 24 * X ^ 2 - 12 * X ^ 3) * S := by
  unfold F
  rw [mul_assoc, PowerSeries.inv_mul_cancel _ (by
    rw [show (2 + 16 * X + 48 * X ^ 2 + 64 * X ^ 3 + 32 * X ^ 4 : ℚ⟦X⟧) = C (2 : ℚ) + C (16 : ℚ) * X ^ 1 + C (48 : ℚ) * X ^ 2 + C (64 : ℚ) * X ^ 3 + C (32 : ℚ) * X ^ 4 from by simp only [map_one, map_neg, map_ofNat] <;> ring]
    simp), mul_one]

theorem E1 : C (2 : ℚ) * F + C (16 : ℚ) * X ^ 1 * F + C (48 : ℚ) * X ^ 2 * F + C (64 : ℚ) * X ^ 3 * F + C (32 : ℚ) * X ^ 4 * F - (C (-3 : ℚ) * S + C (-15 : ℚ) * X ^ 1 * S + C (-24 : ℚ) * X ^ 2 * S + C (-12 : ℚ) * X ^ 3 * S) - (C (7 : ℚ) + C (33 : ℚ) * X ^ 1 + C (48 : ℚ) * X ^ 2 + C (20 : ℚ) * X ^ 3) = 0 := by
  have h := hF
  simp only [map_one, map_neg, map_ofNat]
  linear_combination h

theorem rel1 (m : ℕ) : (2 : ℚ) * coeff (m + 4) F + (16 : ℚ) * coeff (m + 3) F + (48 : ℚ) * coeff (m + 2) F + (64 : ℚ) * coeff (m + 1) F + (32 : ℚ) * coeff (m) F - ((-3 : ℚ) * coeff (m + 4) S + (-15 : ℚ) * coeff (m + 3) S + (-24 : ℚ) * coeff (m + 2) S + (-12 : ℚ) * coeff (m + 1) S) = 0 := by
  have h := congrArg (coeff (m + 4)) E1
  simp only [map_add, map_sub, map_zero] at h
  simp (disch := omega) only [cx, cc, cc0] at h
  simp only [cx0, sub_zero, add_zero, zero_add] at h
  rw [show m + 4 - 1 = m + 3 from by omega, show m + 4 - 2 = m + 2 from by omega, show m + 4 - 3 = m + 1 from by omega, show m + 4 - 4 = m from by omega] at h
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

theorem hs1 : coeff 1 S = (-8 : ℚ) := by
  have h := congrArg (coeff 0) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0] at h ⊢ <;> linarith

theorem hs2 : coeff 2 S = (-32 : ℚ) := by
  have h := congrArg (coeff 1) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1] at h ⊢ <;> linarith

theorem hs3 : coeff 3 S = (-256 : ℚ) := by
  have h := congrArg (coeff 2) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2] at h ⊢ <;> linarith

theorem hs4 : coeff 4 S = (-2560 : ℚ) := by
  have h := congrArg (coeff 3) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3] at h ⊢ <;> linarith

theorem hs5 : coeff 5 S = (-28672 : ℚ) := by
  have h := congrArg (coeff 4) E2
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz] at h
  try simp only [cx0, coeff_derivative] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4] at h ⊢ <;> linarith

theorem hf0 : coeff 0 F = (2 : ℚ) := by
  have h := congrArg (coeff 0) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5] at h ⊢ <;> linarith

theorem hf0c : constantCoeff F = (2 : ℚ) := by rw [← coeff_zero_eq_constantCoeff_apply]; exact hf0

theorem hf1 : coeff 1 F = (5 : ℚ) := by
  have h := congrArg (coeff 1) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hf0, hf0c] at h ⊢ <;> linarith

theorem hf2 : coeff 2 F = (32 : ℚ) := by
  have h := congrArg (coeff 2) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hf0, hf1, hf0c] at h ⊢ <;> linarith

theorem hf3 : coeff 3 F = (284 : ℚ) := by
  have h := congrArg (coeff 3) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hf0, hf1, hf2, hf0c] at h ⊢ <;> linarith

theorem hf4 : coeff 4 F = (2960 : ℚ) := by
  have h := congrArg (coeff 4) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hf0, hf1, hf2, hf3, hf0c] at h ⊢ <;> linarith

theorem hf5 : coeff 5 F = (33872 : ℚ) := by
  have h := congrArg (coeff 5) E1
  simp only [map_add, map_sub, map_zero] at h
  try simp (disch := omega) only [cx, cz, cc, ccj, cc0, cc0'] at h
  try simp only [cx0] at h
  norm_num [S_const, hs0, hs1, hs2, hs3, hs4, hs5, hf0, hf1, hf2, hf3, hf4, hf0c] at h ⊢ <;> linarith

theorem ha0 : a 0 = (2 : ℚ) := by rw [a_eq]; exact hf0

theorem ha1 : a 1 = (5 : ℚ) := by rw [a_eq]; exact hf1

theorem ha2 : a 2 = (32 : ℚ) := by rw [a_eq]; exact hf2

theorem ha3 : a 3 = (284 : ℚ) := by rw [a_eq]; exact hf3

theorem ha4 : a 4 = (2960 : ℚ) := by rw [a_eq]; exact hf4

theorem ha5 : a 5 = (33872 : ℚ) := by rw [a_eq]; exact hf5

noncomputable def Mv (n : ℕ) : ℚ := (17 * (n : ℚ) ^ 2 - 7 * (n : ℚ)) * a n
      + (-238 * (n : ℚ) ^ 2 + 540 * (n : ℚ) - 192) * a (n - 1)
      + (-544 * (n : ℚ) ^ 2 + 496 * (n : ℚ) + 480) * a (n - 2)

theorem base2 : Mv 2 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5]

theorem base3 : Mv 3 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5]

theorem base4 : Mv 4 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5]

theorem base5 : Mv 5 = 0 := by
  unfold Mv
  norm_num [ha0, ha1, ha2, ha3, ha4, ha5]

theorem certQ (k : ℕ) : ((-2132992 / 397953 : ℚ) + (-41920 / 7803 : ℚ) * ((k : ℚ) + 2) ^ 1 + (-64 / 51 : ℚ) * ((k : ℚ) + 2) ^ 2) * Mv (k + 2) + ((-2947328 / 397953 : ℚ) + (-74048 / 7803 : ℚ) * ((k : ℚ) + 2) ^ 1 + (-128 / 51 : ℚ) * ((k : ℚ) + 2) ^ 2) * Mv (k + 3) + ((-490400 / 132651 : ℚ) + (-16064 / 2601 : ℚ) * ((k : ℚ) + 2) ^ 1 + (-32 / 17 : ℚ) * ((k : ℚ) + 2) ^ 2) * Mv (k + 4) + ((-327200 / 397953 : ℚ) + (-13616 / 7803 : ℚ) * ((k : ℚ) + 2) ^ 1 + (-32 / 51 : ℚ) * ((k : ℚ) + 2) ^ 2) * Mv (k + 5) + ((-30904 / 397953 : ℚ) + (-1396 / 7803 : ℚ) * ((k : ℚ) + 2) ^ 1 + (-4 / 51 : ℚ) * ((k : ℚ) + 2) ^ 2) * Mv (k + 6) = 0 := by
  unfold Mv
  rw [show k + 2 - 1 = k + 1 from by omega, show k + 2 - 2 = k from by omega, show k + 3 - 1 = k + 2 from by omega, show k + 3 - 2 = k + 1 from by omega, show k + 4 - 1 = k + 3 from by omega, show k + 4 - 2 = k + 2 from by omega, show k + 5 - 1 = k + 4 from by omega, show k + 5 - 2 = k + 3 from by omega, show k + 6 - 1 = k + 5 from by omega, show k + 6 - 2 = k + 4 from by omega]
  simp only [a_eq]
  have r1_52 := rel1 (k)
  have r1_53 := rel1 (k + 1)
  have r1_54 := rel1 (k + 2)
  have r2_49 := rel2 (k)
  have r2_50 := rel2 (k + 1)
  have r2_51 := rel2 (k + 2)
  have r2_52 := rel2 (k + 3)
  have r2_53 := rel2 (k + 4)
  try simp only [Nat.add_assoc, Nat.reduceAdd] at r1_52 r1_53 r1_54 r2_49 r2_50 r2_51 r2_52 r2_53 ⊢
  push_cast at r1_52 r1_53 r1_54 r2_49 r2_50 r2_51 r2_52 r2_53 ⊢
  linear_combination ((-10664960 / 132651 : ℚ) + (-65130176 / 397953 : ℚ) * ((k : ℚ) + 2) ^ 1 + (-256928 / 23409 : ℚ) * ((k : ℚ) + 2) ^ 2 + (32992 / 459 : ℚ) * ((k : ℚ) + 2) ^ 3 + (64 / 3 : ℚ) * ((k : ℚ) + 2) ^ 4) * r1_52 + ((4110976 / 44217 : ℚ) + (110637152 / 397953 : ℚ) * ((k : ℚ) + 2) ^ 1 + (5764936 / 23409 : ℚ) * ((k : ℚ) + 2) ^ 2 + (37996 / 459 : ℚ) * ((k : ℚ) + 2) ^ 3 + (28 / 3 : ℚ) * ((k : ℚ) + 2) ^ 4) * r1_53 + ((-3770288 / 397953 : ℚ) + (-1186580 / 44217 : ℚ) * ((k : ℚ) + 2) ^ 1 + (-509570 / 23409 : ℚ) * ((k : ℚ) + 2) ^ 2 + (-3020 / 459 : ℚ) * ((k : ℚ) + 2) ^ 3 + (-2 / 3 : ℚ) * ((k : ℚ) + 2) ^ 4) * r1_54 + ((2666240 / 132651 : ℚ) + (423824 / 7803 : ℚ) * ((k : ℚ) + 2) ^ 1 + (5960 / 153 : ℚ) * ((k : ℚ) + 2) ^ 2 + (8 : ℚ) * ((k : ℚ) + 2) ^ 3) * r2_49 + ((2249248 / 44217 : ℚ) + (1062824 / 7803 : ℚ) * ((k : ℚ) + 2) ^ 1 + (14900 / 153 : ℚ) * ((k : ℚ) + 2) ^ 2 + (20 : ℚ) * ((k : ℚ) + 2) ^ 3) * r2_50 + ((8401888 / 132651 : ℚ) + (121528 / 867 : ℚ) * ((k : ℚ) + 2) ^ 1 + (1558 / 17 : ℚ) * ((k : ℚ) + 2) ^ 2 + (18 : ℚ) * ((k : ℚ) + 2) ^ 3) * r2_51 + ((3259256 / 132651 : ℚ) + (477334 / 7803 : ℚ) * ((k : ℚ) + 2) ^ 1 + (5827 / 153 : ℚ) * ((k : ℚ) + 2) ^ 2 + (7 : ℚ) * ((k : ℚ) + 2) ^ 3) * r2_52 + ((471286 / 132651 : ℚ) + (71593 / 7803 : ℚ) * ((k : ℚ) + 2) ^ 1 + (898 / 153 : ℚ) * ((k : ℚ) + 2) ^ 2 + (1 : ℚ) * ((k : ℚ) + 2) ^ 3) * r2_53

theorem Mv_zero : ∀ n : ℕ, 2 ≤ n → Mv n = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hlt : n < 6
    · interval_cases n
      · exact base2
      · exact base3
      · exact base4
      · exact base5
    · obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
      have hc := certQ k
      have h0 : Mv (k + 2) = 0 := ih _ (by omega) (by omega)
      have h1 : Mv (k + 3) = 0 := ih _ (by omega) (by omega)
      have h2 : Mv (k + 4) = 0 := ih _ (by omega) (by omega)
      have h3 : Mv (k + 5) = 0 := ih _ (by omega) (by omega)
      have hq : ((-30904 / 397953 : ℚ) + (-1396 / 7803 : ℚ) * ((k : ℚ) + 2) ^ 1 + (-4 / 51 : ℚ) * ((k : ℚ) + 2) ^ 2) ≠ 0 := by
        have e : ((-30904 / 397953 : ℚ) + (-1396 / 7803 : ℚ) * ((k : ℚ) + 2) ^ 1 + (-4 / 51 : ℚ) * ((k : ℚ) + 2) ^ 2) = -((298144 / 397953 : ℚ) + (3844 / 7803 : ℚ) * (k : ℚ) ^ 1 + (4 / 51 : ℚ) * (k : ℚ) ^ 2) := by ring
        rw [e, neg_ne_zero]
        positivity
      have hm : ((-30904 / 397953 : ℚ) + (-1396 / 7803 : ℚ) * ((k : ℚ) + 2) ^ 1 + (-4 / 51 : ℚ) * ((k : ℚ) + 2) ^ 2) * Mv (k + 6) = 0 := by linear_combination hc - ((-2132992 / 397953 : ℚ) + (-41920 / 7803 : ℚ) * ((k : ℚ) + 2) ^ 1 + (-64 / 51 : ℚ) * ((k : ℚ) + 2) ^ 2) * h0 - ((-2947328 / 397953 : ℚ) + (-74048 / 7803 : ℚ) * ((k : ℚ) + 2) ^ 1 + (-128 / 51 : ℚ) * ((k : ℚ) + 2) ^ 2) * h1 - ((-490400 / 132651 : ℚ) + (-16064 / 2601 : ℚ) * ((k : ℚ) + 2) ^ 1 + (-32 / 17 : ℚ) * ((k : ℚ) + 2) ^ 2) * h2 - ((-327200 / 397953 : ℚ) + (-13616 / 7803 : ℚ) * ((k : ℚ) + 2) ^ 1 + (-32 / 51 : ℚ) * ((k : ℚ) + 2) ^ 2) * h3
      exact (mul_eq_zero.mp hm).resolve_left hq

theorem main' : ∀ n : ℕ, 2 ≤ n → (17 * (n : ℚ) ^ 2 - 7 * (n : ℚ)) * a n
      + (-238 * (n : ℚ) ^ 2 + 540 * (n : ℚ) - 192) * a (n - 1)
      + (-544 * (n : ℚ) ^ 2 + 496 * (n : ℚ) + 480) * a (n - 2) = 0 := fun n hn => Mv_zero n hn

end OMA.P_oeis_a067299

theorem OMA.solution : type_of% @OMA.S_oeis_a067299.main := OMA.P_oeis_a067299.main'
