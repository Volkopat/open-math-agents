import OMAStatements.S_oeis_a227081
import Mathlib

namespace OMA.A227081Proof

open PowerSeries OMA.S_oeis_a227081

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

lemma ode_S : 2 * R * derivative ℚ S = S * (-8 + 24 * X) := by
  have hsq := S_sq
  have hD : derivative ℚ (S ^ 2) = derivative ℚ R := congrArg _ hsq
  have hP : derivative ℚ R = -8 + 24 * X := by
    simp [R, dnum]
    ring
  rw [hP, sq, Derivation.leibniz, smul_eq_mul] at hD
  linear_combination (-2 * derivative ℚ S) * hsq + S * hD

noncomputable def H : ℚ⟦X⟧ :=
  (1 - 6 * X + (2) * S) * (3 - 20 * X + 12 * X ^ 2 : PowerSeries ℚ)⁻¹

lemma ode_H : (3 - 26 * X + 52 * X ^ 2 - 24 * X ^ 3) * derivative ℚ H =
    (8 - 20 * X + 24 * X ^ 2) * H - 2 := by
  have hU : (3 - 20 * X + 12 * X ^ 2 : ℚ⟦X⟧) * (3 - 20 * X + 12 * X ^ 2 : ℚ⟦X⟧)⁻¹ = 1 :=
    PowerSeries.mul_inv_cancel _ (by
      have h3 : constantCoeff (3 : ℚ⟦X⟧) = 3 := map_ofNat constantCoeff 3
      simp [h3])
  have h3 : (3 - 20 * X + 12 * X ^ 2 : ℚ⟦X⟧) * H = 1 - 6 * X + 2 * S := by
    unfold H
    linear_combination (1 - 6 * X + 2 * S) * hU
  have h4 : derivative ℚ ((3 - 20 * X + 12 * X ^ 2 : ℚ⟦X⟧) * H) =
      derivative ℚ (1 - 6 * X + 2 * S) := congrArg _ h3
  have hd1 : derivative ℚ (3 - 20 * X + 12 * X ^ 2 : ℚ⟦X⟧) = -20 + 24 * X := by
    simp [dnum]; ring
  have hd2 : derivative ℚ (1 - 6 * X + 2 * S) = -6 + 2 * derivative ℚ S := by
    simp [dnum]
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hd1, hd2] at h4
  have hR := ode_S
  unfold R at hR
  have key : (1 - 6 * X : ℚ⟦X⟧) * ((3 - 26 * X + 52 * X ^ 2 - 24 * X ^ 3) * derivative ℚ H -
      ((8 - 20 * X + 24 * X ^ 2) * H - 2)) = 0 := by
    linear_combination (1 - 8 * X + 12 * X ^ 2 : ℚ⟦X⟧) * h4 + hR - (-4 + 12 * X : ℚ⟦X⟧) * h3
  have hne : (1 - 6 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have := congrArg (constantCoeff) h
    simp at this
  have := (mul_eq_zero.mp key).resolve_left hne
  linear_combination this

lemma cx (f : ℚ⟦X⟧) (j k : ℕ) : coeff (k + j) (X ^ j * f) = coeff k f :=
  coeff_X_pow_mul f j k

lemma rec_H (k : ℕ) :
    3 * ((k : ℚ) + 4) * coeff (k + 4) H - 26 * ((k : ℚ) + 3) * coeff (k + 3) H
      + 52 * ((k : ℚ) + 2) * coeff (k + 2) H - 24 * ((k : ℚ) + 1) * coeff (k + 1) H =
    8 * coeff (k + 3) H - 20 * coeff (k + 2) H + 24 * coeff (k + 1) H := by
  have E := ode_H
  have E' : 3 * derivative ℚ H - 26 * (X ^ 1 * derivative ℚ H) + 52 * (X ^ 2 * derivative ℚ H)
      - 24 * (X ^ 3 * derivative ℚ H) =
      8 * H - 20 * (X ^ 1 * H) + 24 * (X ^ 2 * H) - 2 * 1 := by
    linear_combination E
  have h := congrArg (coeff (k + 3)) E'
  simp only [map_add, map_sub, cnum] at h
  rw [cx _ 1 (k + 2), cx _ 2 (k + 1), cx _ 3 k, cx _ 1 (k + 2), cx _ 2 (k + 1)] at h
  simp only [coeff_derivative, coeff_one] at h
  simp at h
  push_cast at h
  linear_combination h

lemma rec_H3 :
    3 * 3 * coeff 3 H - 26 * 2 * coeff 2 H + 52 * 1 * coeff 1 H =
    8 * coeff 2 H - 20 * coeff 1 H + 24 * coeff 0 H := by
  have E := ode_H
  have E' : 3 * derivative ℚ H - 26 * (X ^ 1 * derivative ℚ H) + 52 * (X ^ 2 * derivative ℚ H)
      - 24 * (X ^ 3 * derivative ℚ H) =
      8 * H - 20 * (X ^ 1 * H) + 24 * (X ^ 2 * H) - 2 * 1 := by
    linear_combination E
  have h := congrArg (coeff 2) E'
  simp only [map_add, map_sub, cnum] at h
  rw [cx _ 1 1, cx _ 2 0, cx _ 1 1, cx _ 2 0] at h
  simp only [coeff_derivative, coeff_one, coeff_X_pow_mul'] at h
  simp at h
  norm_num at h
  rw [coeff_zero_eq_constantCoeff_apply]
  linear_combination h

end OMA.A227081Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a227081.main := by
  intro n hn
  have hH : ∀ m, OMA.S_oeis_a227081.a m = PowerSeries.coeff m OMA.A227081Proof.H := fun m => rfl
  rcases Nat.eq_or_lt_of_le hn with rfl | hn'
  · have hr := OMA.A227081Proof.rec_H3
    simp only [hH]
    norm_num
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply] at hr
    linear_combination hr
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
    have hr := OMA.A227081Proof.rec_H k
    simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
      show k + 4 - 3 = k + 1 by omega, hH]
    push_cast at hr ⊢
    linear_combination hr
