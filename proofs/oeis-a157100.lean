import OMAStatements.S_oeis_a157100
import Mathlib

open OMA.S_oeis_a157100
open PowerSeries

namespace Pa157100

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


theorem quad : (X * (1 - X ^ 2)) * A ^ 2 + (-(1 + X)) * A + ((1 + X) ^ 2) = 0 := by
  have hc := catalan_subst (X * (1 - X ^ 2)) (by simp)
  unfold A
  set c := (catalanSeries.map (Nat.castRingHom ℚ)).subst (X * (1 - X ^ 2) : PowerSeries ℚ)
  linear_combination (1 + X) ^ 2 * hc

theorem ode : (X - 5 * X ^ 2 + 4 * X ^ 3 + 4 * X ^ 4 - 4 * X ^ 5) * d⁄dX ℚ A + (1 - 4 * X + 6 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4) * A = 1 - 3 * X ^ 2 := by
  set S : PowerSeries ℚ := 2 * (X * (1 - X ^ 2)) * A + (-(1 + X)) with hSdef
  have hS : S ^ 2 = (-(1 + X)) ^ 2 - 4 * (X * (1 - X ^ 2)) * ((1 + X) ^ 2) := by
    rw [hSdef]; linear_combination (4 * (X * (1 - X ^ 2))) * quad
  have hA : 2 * (X * (1 - X ^ 2)) * A = -(-(1 + X)) + S := by rw [hSdef]; ring
  have hdD : d⁄dX ℚ ((-(1 + X)) ^ 2 - 4 * (X * (1 - X ^ 2)) * ((1 + X) ^ 2)) = -2 - 14 * X + 32 * X ^ 3 + 20 * X ^ 4 := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    try simp only [map_ofNat]
    try push_cast
    try ring
  have hda : d⁄dX ℚ (2 * (X * (1 - X ^ 2))) = 2 - 6 * X ^ 2 := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    try simp only [map_ofNat]
    try push_cast
    try ring
  have hdb : d⁄dX ℚ (-(1 + X)) = -1 := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    try simp only [map_ofNat]
    try push_cast
    try ring
  have h1 : 2 * S * d⁄dX ℚ S = -2 - 14 * X + 32 * X ^ 3 + 20 * X ^ 4 := by
    have := congrArg (d⁄dX ℚ) hS
    rw [derivative_pow, hdD] at this
    rw [← this]; push_cast; ring
  have E1 : (2 - 6 * X ^ 2) * A + 2 * (X * (1 - X ^ 2)) * d⁄dX ℚ A = -(-1) + d⁄dX ℚ S := by
    have := congrArg (d⁄dX ℚ) hA
    rw [Derivation.leibniz, map_add, map_neg, hda, hdb, smul_eq_mul, smul_eq_mul] at this
    linear_combination this
  have E2 : 2 * ((-(1 + X)) ^ 2 - 4 * (X * (1 - X ^ 2)) * ((1 + X) ^ 2)) * d⁄dX ℚ S = (-2 - 14 * X + 32 * X ^ 3 + 20 * X ^ 4) * S := by
    linear_combination (-2 * d⁄dX ℚ S) * hS + S * h1
  have key : (2 * ((-(1 + X)) ^ 2 - 4 * (X * (1 - X ^ 2)) * ((1 + X) ^ 2)) * (2 * (X * (1 - X ^ 2)))) *
      ((X - 5 * X ^ 2 + 4 * X ^ 3 + 4 * X ^ 4 - 4 * X ^ 5) * d⁄dX ℚ A + (1 - 4 * X + 6 * X ^ 2 - 2 * X ^ 3 - 2 * X ^ 4) * A - (1 - 3 * X ^ 2)) = 0 := by
    linear_combination (2 * ((-(1 + X)) ^ 2 - 4 * (X * (1 - X ^ 2)) * ((1 + X) ^ 2)) * (X - 5 * X ^ 2 + 4 * X ^ 3 + 4 * X ^ 4 - 4 * X ^ 5)) * E1 +
      (X - 5 * X ^ 2 + 4 * X ^ 3 + 4 * X ^ 4 - 4 * X ^ 5) * E2 - ((X - 5 * X ^ 2 + 4 * X ^ 3 + 4 * X ^ 4 - 4 * X ^ 5) * (-2 - 14 * X + 32 * X ^ 3 + 20 * X ^ 4)) * hA
  have hne : ((2 : PowerSeries ℚ) * ((-(1 + X)) ^ 2 - 4 * (X * (1 - X ^ 2)) * ((1 + X) ^ 2)) * (2 * (X * (1 - X ^ 2)))) ≠ 0 := by
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

end Pa157100

theorem OMA.solution : type_of% @OMA.S_oeis_a157100.main := by
  intro n hn
  have e := congrArg (coeff n) Pa157100.ode
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  simp only [Pa157100.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa157100.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X,
    coeff_one] at e
  simp at e
  push_cast at e ⊢
  linarith
