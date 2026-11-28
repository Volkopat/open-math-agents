import OMAStatements.S_oeis_a166228
import Mathlib

open OMA.S_oeis_a166228
open PowerSeries

namespace Pa166228

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

noncomputable def A : PowerSeries ℚ := PowerSeries.mk fun n => (a n : ℚ)

noncomputable def Sq : PowerSeries ℚ := map (Nat.castRingHom ℚ) largeSchroderSeries

theorem Sq_eq : Sq = 1 + X * Sq + X * Sq ^ 2 := by
  have := congrArg (map (Nat.castRingHom ℚ))
    largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq
  simpa [Sq] using this

theorem a_succ (n : ℕ) : (a (n + 1) : ℚ) + a n = Nat.largeSchroder (n + 1) := by
  unfold a
  rw [Finset.sum_range_succ, Nat.sub_self, pow_zero, one_mul]
  have h : ∀ k ∈ Finset.range (n + 1),
      ((-1 : ℤ) ^ (n + 1 - k) * (Nat.largeSchroder k : ℤ)) = -((-1) ^ (n - k) * Nat.largeSchroder k) := by
    intro k hk
    rw [Finset.mem_range] at hk
    rw [show n + 1 - k = (n - k) + 1 by omega, pow_succ]
    ring
  rw [Finset.sum_congr rfl h, Finset.sum_neg_distrib]
  push_cast
  ring

theorem shift : (1 + X) * A = Sq := by
  ext n
  rcases n with _ | n
  · simp [A, Sq, a]
  · rw [add_mul, one_mul, map_add, coeff_succ_X_mul]
    simp only [A, Sq, coeff_mk, coeff_map, coeff_largeSchroderSeries]
    rw [a_succ]
    simp

theorem quad : (X * (1 + X) ^ 2) * A ^ 2 + ((X - 1) * (1 + X)) * A + (1) = 0 := by
  have h1 := shift
  have h2 := Sq_eq
  linear_combination (X * ((1 + X) * A + Sq) + (X - 1)) * h1 - h2

theorem ode : (X - 5 * X ^ 2 - 5 * X ^ 3 + X ^ 4) * d⁄dX ℚ A + (1 - X - 9 * X ^ 2 + X ^ 3) * A = 1 + X := by
  set S : PowerSeries ℚ := 2 * (X * (1 + X) ^ 2) * A + ((X - 1) * (1 + X)) with hSdef
  have hS : S ^ 2 = ((X - 1) * (1 + X)) ^ 2 - 4 * (X * (1 + X) ^ 2) * (1) := by
    rw [hSdef]; linear_combination (4 * (X * (1 + X) ^ 2)) * quad
  have hA : 2 * (X * (1 + X) ^ 2) * A = -((X - 1) * (1 + X)) + S := by rw [hSdef]; ring
  have hdD : d⁄dX ℚ (((X - 1) * (1 + X)) ^ 2 - 4 * (X * (1 + X) ^ 2) * (1)) = -4 - 20 * X - 12 * X ^ 2 + 4 * X ^ 3 := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    try simp only [map_ofNat]
    try push_cast
    try ring
  have hda : d⁄dX ℚ (2 * (X * (1 + X) ^ 2)) = 2 + 8 * X + 6 * X ^ 2 := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    try simp only [map_ofNat]
    try push_cast
    try ring
  have hdb : d⁄dX ℚ ((X - 1) * (1 + X)) = 2 * X := by
    simp only [nC, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, map_sub, map_add, map_neg, derivative_pow, derivative_one]
    try simp only [map_ofNat]
    try push_cast
    try ring
  have h1 : 2 * S * d⁄dX ℚ S = -4 - 20 * X - 12 * X ^ 2 + 4 * X ^ 3 := by
    have := congrArg (d⁄dX ℚ) hS
    rw [derivative_pow, hdD] at this
    rw [← this]; push_cast; ring
  have E1 : (2 + 8 * X + 6 * X ^ 2) * A + 2 * (X * (1 + X) ^ 2) * d⁄dX ℚ A = -(2 * X) + d⁄dX ℚ S := by
    have := congrArg (d⁄dX ℚ) hA
    rw [Derivation.leibniz, map_add, map_neg, hda, hdb, smul_eq_mul, smul_eq_mul] at this
    linear_combination this
  have E2 : 2 * (((X - 1) * (1 + X)) ^ 2 - 4 * (X * (1 + X) ^ 2) * (1)) * d⁄dX ℚ S = (-4 - 20 * X - 12 * X ^ 2 + 4 * X ^ 3) * S := by
    linear_combination (-2 * d⁄dX ℚ S) * hS + S * h1
  have key : (2 * (((X - 1) * (1 + X)) ^ 2 - 4 * (X * (1 + X) ^ 2) * (1)) * (2 * (X * (1 + X) ^ 2))) *
      ((X - 5 * X ^ 2 - 5 * X ^ 3 + X ^ 4) * d⁄dX ℚ A + (1 - X - 9 * X ^ 2 + X ^ 3) * A - (1 + X)) = 0 := by
    linear_combination (2 * (((X - 1) * (1 + X)) ^ 2 - 4 * (X * (1 + X) ^ 2) * (1)) * (X - 5 * X ^ 2 - 5 * X ^ 3 + X ^ 4)) * E1 +
      (X - 5 * X ^ 2 - 5 * X ^ 3 + X ^ 4) * E2 - ((X - 5 * X ^ 2 - 5 * X ^ 3 + X ^ 4) * (-4 - 20 * X - 12 * X ^ 2 + 4 * X ^ 3)) * hA
  have hne : ((2 : PowerSeries ℚ) * (((X - 1) * (1 + X)) ^ 2 - 4 * (X * (1 + X) ^ 2) * (1)) * (2 * (X * (1 + X) ^ 2))) ≠ 0 := by
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

end Pa166228

theorem OMA.solution : type_of% @OMA.S_oeis_a166228.main := by
  intro n hn
  have e := congrArg (coeff n) Pa166228.ode
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega, show k + 3 - 3 = k by omega]
  simp only [Pa166228.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, Pa166228.cXd, coeff_succ_X_mul, coeff_derivative, coeff_X,
    coeff_one] at e
  simp at e
  simp only [Pa166228.A, coeff_mk] at e
  qify
  push_cast at e ⊢
  linarith
