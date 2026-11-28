import OMAStatements.S_oeis_a168505
import Mathlib

open OMA.S_oeis_a168505
open PowerSeries

namespace Pa168505

theorem nC (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem cXd (F : PowerSeries ℚ) (k : ℕ) : coeff k (X * d⁄dX ℚ F) = coeff k F * k := by
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_derivative]; push_cast; ring

theorem two_ne : (2 : PowerSeries ℚ) ≠ 0 := by
  intro h
  have := congrArg constantCoeff h
  rw [map_ofNat, map_zero] at this
  norm_num at this

noncomputable def cat : PowerSeries ℚ := map (Nat.castRingHom ℚ) catalanSeries

theorem cat_eq : cat ^ 2 * X + 1 = cat := by
  have := congrArg (map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
  simpa [cat] using this

theorem catalan_subst (u : PowerSeries ℚ) (hu : constantCoeff u = 0) :
    (catalanSeries.map (Nat.castRingHom ℚ)).subst u ^ 2 * u + 1 =
      (catalanSeries.map (Nat.castRingHom ℚ)).subst u := by
  have ha := HasSubst.of_constantCoeff_zero' hu
  have hc := congrArg (substAlgHom ha) cat_eq
  rw [map_add, map_mul, map_pow, map_one, substAlgHom_X, coe_substAlgHom] at hc
  exact hc

theorem nC' (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem h4 : (4 : PowerSeries ℚ) * C (1 / 4) = 1 := by
  rw [nC', ← map_mul]; norm_num

theorem sqrt_exists (u : PowerSeries ℚ) (hu : constantCoeff u = 0) :
    ∃ S : PowerSeries ℚ, S ^ 2 = 1 - 4 * u ∧ constantCoeff S = 1 := by
  have ha := HasSubst.of_constantCoeff_zero' hu
  have hc := congrArg (substAlgHom ha) cat_eq
  rw [map_add, map_mul, map_pow, map_one, substAlgHom_X] at hc
  refine ⟨1 - 2 * u * substAlgHom ha cat, ?_, ?_⟩
  · linear_combination (4 * u) * hc
  · simp [hu]

theorem exists_gf : ∃ A U V : PowerSeries ℚ, CF A U V := by
  obtain ⟨S, hS, hS0⟩ := sqrt_exists ((1 - (1 - 2 * X + X ^ 2 + 4 * X ^ 3)) * C (1 / 4)) (by simp)
  have hS' : S ^ 2 = 1 - 2 * X + X ^ 2 + 4 * X ^ 3 := by linear_combination hS - (1 - (1 - 2 * X + X ^ 2 + 4 * X ^ 3)) * h4
  have hd : X ∣ (S - (1 + X)) := by
    rw [X_dvd_iff]
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, hS0, map_zero]
    norm_num
  obtain ⟨B, hB⟩ := hd
  have hW : constantCoeff (2 * (-1 + X) : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (2 * (-1 + X) : PowerSeries ℚ) hW
  set A : PowerSeries ℚ := B * (2 * (-1 + X))⁻¹ with hAdef
  have h2a : 2 * (X * (-1 + X)) * A = S - (1 + X) := by
    rw [hAdef]; linear_combination (X * B) * hinv - hB
  have hq4 : (4 * (X * (-1 + X))) * ((X * (-1 + X)) * A ^ 2 + (1 + X) * A + (-1 - X)) = 0 := by
    linear_combination (2 * (X * (-1 + X)) * A + (1 + X) + S) * h2a + hS'
  have hne4 : (4 * (X * (-1 + X)) : PowerSeries ℚ) ≠ 0 := by
    rw [show (4 * (X * (-1 + X)) : PowerSeries ℚ) = X * (4 * (-1 + X)) by ring]
    refine mul_ne_zero X_ne_zero ?_
    intro h0
    have := congrArg constantCoeff h0
    revert this
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero]
    norm_num
  have hq := (mul_eq_zero.mp hq4).resolve_left hne4
  have hcv : constantCoeff (1 - X * A : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero]
    norm_num
  set V : PowerSeries ℚ := (1 - X * A)⁻¹ with hV
  have hv : V * (1 - X * A) = 1 := PowerSeries.inv_mul_cancel _ hcv
  have hcu : constantCoeff (1 + X * V : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero]
    norm_num
  set U : PowerSeries ℚ := (1 + X * V)⁻¹ with hU
  have hu : U * (1 + X * V) = 1 := PowerSeries.inv_mul_cancel _ hcu
  have hw : (1 - -1 * X - 1 * X * A) * (A * (1 - X * U) - 1) = 0 := by
    linear_combination hq - (1 * X * A * (1 - 1 * X * A)) * hu - (-1 * X ^ 2 * A * U) * hv
  have hwne : ((1 - -1 * X - 1 * X * A) : PowerSeries ℚ) ≠ 0 := by
    intro h0
    have := congrArg constantCoeff h0
    revert this
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat, map_zero]
    norm_num
  refine ⟨A, U, V, ?_, hu, hv⟩
  exact sub_eq_zero.mp ((mul_eq_zero.mp hw).resolve_left hwne)

theorem quad (A U V : PowerSeries ℚ) (h : CF A U V) : (X * (-1 + X)) * A ^ 2 + (1 + X) * A + (-1 - X) = 0 := by
  obtain ⟨hy, hu, hv⟩ := h
  linear_combination (1 - -1 * X - 1 * X * A) * hy + (1 * X * A * (1 - 1 * X * A)) * hu + (-1 * X ^ 2 * A * U) * hv

theorem ode (A U V : PowerSeries ℚ) (h : CF A U V) : (X - 3 * X ^ 2 + 3 * X ^ 3 + 3 * X ^ 4 - 4 * X ^ 5) * d⁄dX ℚ A + (1 - 3 * X + 3 * X ^ 2 - 3 * X ^ 3 - 2 * X ^ 4) * A = 1 - X - 3 * X ^ 2 - X ^ 3 := by
  set S : PowerSeries ℚ := 2 * (X * (-1 + X)) * A + (1 + X) with hSdef
  have hS : S ^ 2 = (1 + X) ^ 2 - 4 * (X * (-1 + X)) * (-1 - X) := by
    rw [hSdef]; linear_combination (4 * (X * (-1 + X))) * quad A U V h
  have hA : 2 * (X * (-1 + X)) * A = -(1 + X) + S := by rw [hSdef]; ring
  have hdD : d⁄dX ℚ ((1 + X) ^ 2 - 4 * (X * (-1 + X)) * (-1 - X)) = -2 + 2 * X + 12 * X ^ 2 := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    try simp only [map_ofNat]
    try push_cast
    try ring
  have hda : d⁄dX ℚ (2 * (X * (-1 + X))) = -2 + 4 * X := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    try simp only [map_ofNat]
    try push_cast
    try ring
  have hdb : d⁄dX ℚ (1 + X) = 1 := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    try simp only [map_ofNat]
    try push_cast
    try ring
  have h1 : 2 * S * d⁄dX ℚ S = -2 + 2 * X + 12 * X ^ 2 := by
    have := congrArg (d⁄dX ℚ) hS
    rw [derivative_pow, hdD] at this
    rw [← this]; push_cast; ring
  have E1 : (-2 + 4 * X) * A + 2 * (X * (-1 + X)) * d⁄dX ℚ A = -(1) + d⁄dX ℚ S := by
    have := congrArg (d⁄dX ℚ) hA
    rw [Derivation.leibniz, map_add, map_neg, hda, hdb, smul_eq_mul, smul_eq_mul] at this
    linear_combination this
  have E2 : 2 * ((1 + X) ^ 2 - 4 * (X * (-1 + X)) * (-1 - X)) * d⁄dX ℚ S = (-2 + 2 * X + 12 * X ^ 2) * S := by
    linear_combination (-2 * d⁄dX ℚ S) * hS + S * h1
  have key : (2 * ((1 + X) ^ 2 - 4 * (X * (-1 + X)) * (-1 - X)) * (2 * (X * (-1 + X)))) *
      ((X - 3 * X ^ 2 + 3 * X ^ 3 + 3 * X ^ 4 - 4 * X ^ 5) * d⁄dX ℚ A + (1 - 3 * X + 3 * X ^ 2 - 3 * X ^ 3 - 2 * X ^ 4) * A - (1 - X - 3 * X ^ 2 - X ^ 3)) = 0 := by
    linear_combination (2 * ((1 + X) ^ 2 - 4 * (X * (-1 + X)) * (-1 - X)) * (X - 3 * X ^ 2 + 3 * X ^ 3 + 3 * X ^ 4 - 4 * X ^ 5)) * E1 +
      (X - 3 * X ^ 2 + 3 * X ^ 3 + 3 * X ^ 4 - 4 * X ^ 5) * E2 - ((X - 3 * X ^ 2 + 3 * X ^ 3 + 3 * X ^ 4 - 4 * X ^ 5) * (-2 + 2 * X + 12 * X ^ 2)) * hA
  have hne : ((2 : PowerSeries ℚ) * ((1 + X) ^ 2 - 4 * (X * (-1 + X)) * (-1 - X)) * (2 * (X * (-1 + X)))) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero two_ne ?_) (mul_ne_zero two_ne ?_)
    · intro h0
      have := congrArg constantCoeff h0
      simp only [map_ofNat, map_mul, map_sub, map_add, map_neg, map_pow, constantCoeff_X,
        constantCoeff_one, map_one] at this
      norm_num at this
    · refine mul_ne_zero X_ne_zero ?_
      intro h0
      have := congrArg constantCoeff h0
      simp only [map_ofNat, map_mul, map_sub, map_add, map_neg, map_pow, constantCoeff_X,
        constantCoeff_one, map_one] at this
      norm_num at this
  exact sub_eq_zero.mp ((mul_eq_zero.mp key).resolve_left hne)

end Pa168505

theorem OMA.solution : type_of% @OMA.S_oeis_a168505.main := by
  refine ⟨Pa168505.exists_gf, fun A U V h n hn => ?_⟩
  have e := congrArg (coeff n) (Pa168505.ode A U V h)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  simp only [Pa168505.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa168505.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X,
    coeff_one] at e
  simp at e
  push_cast at e ⊢
  linarith
