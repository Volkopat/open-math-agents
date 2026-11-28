import OMAStatements.S_oeis_a217333
import Mathlib

namespace OMA.A217333Proof

open PowerSeries OMA.S_oeis_a217333

lemma dnum (m : ℕ) [m.AtLeastTwo] : derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]; exact derivative_C

lemma cnum (m n : ℕ) [m.AtLeastTwo] (f : ℚ⟦X⟧) :
    coeff n ((no_index (OfNat.ofNat m : ℚ⟦X⟧)) * f) = (OfNat.ofNat m : ℚ) * coeff n f := by
  rw [← map_ofNat C m, coeff_C_mul]

lemma hasSubst : HasSubst (R - 1 : PowerSeries ℚ) := by
  apply HasSubst.of_constantCoeff_zero'
  simp [R]

lemma S_sq : S ^ 2 = R := by
  have h : PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) ^ 2 = 1 + X := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    have : (1 / 2 + 1 / 2 : ℚ) = ((1 : ℕ) : ℚ) := by norm_num
    rw [this, PowerSeries.binomialSeries_nat, pow_one]
  unfold S
  rw [← subst_pow hasSubst, h, ← coe_substAlgHom hasSubst, map_add, map_one,
    coe_substAlgHom hasSubst, subst_X hasSubst]
  ring

lemma ode_S : 2 * R * derivative ℚ S =
    S * (-4 + 8 * X - 12 * X ^ 2 + 16 * X ^ 3) := by
  have hsq := S_sq
  have hD : derivative ℚ (S ^ 2) = derivative ℚ R := congrArg _ hsq
  have hP : derivative ℚ R = -4 + 8 * X - 12 * X ^ 2 + 16 * X ^ 3 := by
    simp [R, dnum]
    ring
  rw [hP, sq, Derivation.leibniz, smul_eq_mul] at hD
  linear_combination (-2 * derivative ℚ S) * hsq + S * hD

lemma cx (f : ℚ⟦X⟧) (j k : ℕ) : coeff (k + j) (X ^ j * f) = coeff k f :=
  coeff_X_pow_mul f j k

lemma rec_S (k : ℕ) :
    ((k : ℚ) + 7) * coeff (k + 7) S - 4 * ((k : ℚ) + 6) * coeff (k + 6) S
      + 4 * ((k : ℚ) + 5) * coeff (k + 5) S - 4 * ((k : ℚ) + 4) * coeff (k + 4) S
      + 4 * ((k : ℚ) + 3) * coeff (k + 3) S =
    -2 * coeff (k + 6) S + 4 * coeff (k + 5) S - 6 * coeff (k + 4) S + 8 * coeff (k + 3) S := by
  have E := ode_S
  have E' : 2 * derivative ℚ S - 8 * (X ^ 1 * derivative ℚ S) + 8 * (X ^ 2 * derivative ℚ S)
      - 8 * (X ^ 3 * derivative ℚ S) + 8 * (X ^ 4 * derivative ℚ S) =
      8 * (X ^ 1 * S) - 12 * (X ^ 2 * S) + 16 * (X ^ 3 * S) - 4 * S := by
    unfold R at E
    linear_combination E
  have h := congrArg (coeff (k + 6)) E'
  simp only [map_add, map_sub, cnum] at h
  rw [cx _ 1 (k + 5), cx _ 2 (k + 4), cx _ 3 (k + 3), cx _ 4 (k + 2), cx _ 1 (k + 5),
    cx _ 2 (k + 4), cx _ 3 (k + 3)] at h
  simp only [coeff_derivative] at h
  push_cast at h
  linear_combination h / 2

lemma inv2 : ((2 : ℚ⟦X⟧))⁻¹ = C (1 / 2 : ℚ) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by rw [show (2 : ℚ⟦X⟧) = C 2 from (map_ofNat C 2).symm, constantCoeff_C]; norm_num)]
  rw [← map_ofNat C 2, ← map_mul]
  norm_num

lemma coeff_main (m : ℕ) (hm : 2 ≤ m) :
    coeff m ((1 - 2 * X - S) * (2 : ℚ⟦X⟧)⁻¹) = -(1 / 2 : ℚ) * coeff m S := by
  rw [inv2, mul_comm, coeff_C_mul]
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 2 := ⟨m - 2, by omega⟩
  simp only [map_sub, coeff_one, coeff_X, cnum]
  simp

end OMA.A217333Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a217333.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hr := OMA.A217333Proof.rec_S k
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  unfold OMA.S_oeis_a217333.a
  rw [show k + 4 + 3 = k + 7 by omega, show k + 3 + 3 = k + 6 by omega,
    show k + 2 + 3 = k + 5 by omega, show k + 1 + 3 = k + 4 by omega]
  rw [OMA.A217333Proof.coeff_main _ (by omega), OMA.A217333Proof.coeff_main _ (by omega),
    OMA.A217333Proof.coeff_main _ (by omega), OMA.A217333Proof.coeff_main _ (by omega),
    OMA.A217333Proof.coeff_main _ (by omega)]
  push_cast at hr ⊢
  linear_combination (-1 / 2 : ℚ) * hr
