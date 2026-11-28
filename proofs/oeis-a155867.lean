import OMAStatements.S_oeis_a155867
import Mathlib

open OMA.S_oeis_a155867
open PowerSeries

namespace Pa155867

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

theorem exists_gf : ∃ S A, IsGF S A := by
  obtain ⟨S, hS, hS0⟩ := sqrt_exists ((1 - (1 - 10 * X + 19 * X ^ 2 - 10 * X ^ 3 + X ^ 4)) * C (1 / 4)) (by simp)
  have hd : X ∣ (1 - 3 * X + X ^ 2 - S) := by
    rw [X_dvd_iff]
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one, hS0,
      map_ofNat]
    norm_num
  obtain ⟨B, hB⟩ := hd
  have hW : constantCoeff (2 * (1 - X) : PowerSeries ℚ) ≠ 0 := by
    simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
      map_ofNat]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (2 * (1 - X) : PowerSeries ℚ) hW
  refine ⟨S, B * (2 * (1 - X))⁻¹, ?_, hS0, ?_⟩
  · linear_combination hS - (1 - (1 - 10 * X + 19 * X ^ 2 - 10 * X ^ 3 + X ^ 4)) * h4
  · linear_combination (X * B) * hinv - hB

theorem quad (S0 A : PowerSeries ℚ) (h : IsGF S0 A) : (X * (1 - X)) * A ^ 2 + (-1 + 3 * X - X ^ 2) * A + (1 - X) = 0 := by
  obtain ⟨hS, _, hA⟩ := h
  have h2 : (2 * (2 * X * (1 - X))) * ((X * (1 - X)) * A ^ 2 + (-1 + 3 * X - X ^ 2) * A + (1 - X)) = 0 := by
    linear_combination hS + (2 * X * (1 - X) * A - (1 - 3 * X + X ^ 2) - S0) * hA
  have hne : (2 * (2 * X * (1 - X)) : PowerSeries ℚ) ≠ 0 := by
    refine mul_ne_zero two_ne ?_
    intro h0
    have h1 : (2 * X * (1 - X) : PowerSeries ℚ) = X * (2 * (1 - X)) := by ring
    rw [h1] at h0
    rcases mul_eq_zero.mp h0 with h0 | h0
    · exact X_ne_zero h0
    · have := congrArg constantCoeff h0
      simp only [map_add, map_sub, map_mul, map_pow, map_neg, constantCoeff_X, constantCoeff_one,
        map_ofNat, map_zero] at this
      norm_num at this
  exact (mul_eq_zero.mp h2).resolve_left hne

theorem ode (S0 A : PowerSeries ℚ) (h : IsGF S0 A) : (X - 11 * X ^ 2 + 29 * X ^ 3 - 29 * X ^ 4 + 11 * X ^ 5 - X ^ 6) * d⁄dX ℚ A + (1 - 7 * X + 15 * X ^ 2 - 14 * X ^ 3 + 4 * X ^ 4) * A = 1 - X + X ^ 3 - X ^ 4 := by
  set S : PowerSeries ℚ := 2 * (X * (1 - X)) * A + (-1 + 3 * X - X ^ 2) with hSdef
  have hS : S ^ 2 = (-1 + 3 * X - X ^ 2) ^ 2 - 4 * (X * (1 - X)) * (1 - X) := by
    rw [hSdef]; linear_combination (4 * (X * (1 - X))) * quad S0 A h
  have hA : 2 * (X * (1 - X)) * A = -(-1 + 3 * X - X ^ 2) + S := by rw [hSdef]; ring
  have hdD : d⁄dX ℚ ((-1 + 3 * X - X ^ 2) ^ 2 - 4 * (X * (1 - X)) * (1 - X)) = -10 + 38 * X - 30 * X ^ 2 + 4 * X ^ 3 := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    try simp only [map_ofNat]
    try push_cast
    try ring
  have hda : d⁄dX ℚ (2 * (X * (1 - X))) = 2 - 4 * X := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    try simp only [map_ofNat]
    try push_cast
    try ring
  have hdb : d⁄dX ℚ (-1 + 3 * X - X ^ 2) = 3 - 2 * X := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    try simp only [map_ofNat]
    try push_cast
    try ring
  have h1 : 2 * S * d⁄dX ℚ S = -10 + 38 * X - 30 * X ^ 2 + 4 * X ^ 3 := by
    have := congrArg (d⁄dX ℚ) hS
    rw [derivative_pow, hdD] at this
    rw [← this]; push_cast; ring
  have E1 : (2 - 4 * X) * A + 2 * (X * (1 - X)) * d⁄dX ℚ A = -(3 - 2 * X) + d⁄dX ℚ S := by
    have := congrArg (d⁄dX ℚ) hA
    rw [Derivation.leibniz, map_add, map_neg, hda, hdb, smul_eq_mul, smul_eq_mul] at this
    linear_combination this
  have E2 : 2 * ((-1 + 3 * X - X ^ 2) ^ 2 - 4 * (X * (1 - X)) * (1 - X)) * d⁄dX ℚ S = (-10 + 38 * X - 30 * X ^ 2 + 4 * X ^ 3) * S := by
    linear_combination (-2 * d⁄dX ℚ S) * hS + S * h1
  have key : (2 * ((-1 + 3 * X - X ^ 2) ^ 2 - 4 * (X * (1 - X)) * (1 - X)) * (2 * (X * (1 - X)))) *
      ((X - 11 * X ^ 2 + 29 * X ^ 3 - 29 * X ^ 4 + 11 * X ^ 5 - X ^ 6) * d⁄dX ℚ A + (1 - 7 * X + 15 * X ^ 2 - 14 * X ^ 3 + 4 * X ^ 4) * A - (1 - X + X ^ 3 - X ^ 4)) = 0 := by
    linear_combination (2 * ((-1 + 3 * X - X ^ 2) ^ 2 - 4 * (X * (1 - X)) * (1 - X)) * (X - 11 * X ^ 2 + 29 * X ^ 3 - 29 * X ^ 4 + 11 * X ^ 5 - X ^ 6)) * E1 +
      (X - 11 * X ^ 2 + 29 * X ^ 3 - 29 * X ^ 4 + 11 * X ^ 5 - X ^ 6) * E2 - ((X - 11 * X ^ 2 + 29 * X ^ 3 - 29 * X ^ 4 + 11 * X ^ 5 - X ^ 6) * (-10 + 38 * X - 30 * X ^ 2 + 4 * X ^ 3)) * hA
  have hne : ((2 : PowerSeries ℚ) * ((-1 + 3 * X - X ^ 2) ^ 2 - 4 * (X * (1 - X)) * (1 - X)) * (2 * (X * (1 - X)))) ≠ 0 := by
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

end Pa155867

theorem OMA.solution : type_of% @OMA.S_oeis_a155867.main := by
  refine ⟨Pa155867.exists_gf, fun S0 A h n hn => ?_⟩
  have e := congrArg (coeff n) (Pa155867.ode S0 A h)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega, show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega, show k + 5 - 5 = k by omega]
  simp only [Pa155867.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa155867.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X,
    coeff_one] at e
  simp at e
  push_cast at e ⊢
  linarith
