import OMAStatements.S_oeis_a110322
import Mathlib

open OMA.S_oeis_a110322
open PowerSeries

namespace P110322

theorem nC (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem dexp : d⁄dX ℚ (exp ℚ) = exp ℚ := by
  ext n
  rw [coeff_derivative, coeff_exp, coeff_exp]
  simp only [Algebra.algebraMap_self, RingHom.id_apply, Nat.factorial_succ]
  push_cast
  field_simp

theorem gf_eq : (1 - X - 2 * X ^ 2 : PowerSeries ℚ) * (((1) * W + (0)) * (1 - X - 2 * X ^ 2 : PowerSeries ℚ)⁻¹)
    = exp ℚ := by
  have hd : constantCoeff (1 - X - 2 * X ^ 2 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_sub, map_mul, map_pow, constantCoeff_X, constantCoeff_one, map_ofNat]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (1 - X - 2 * X ^ 2 : PowerSeries ℚ) hd
  have hW : W = exp ℚ := by unfold W U; exact X_subst _
  rw [hW]
  linear_combination (exp ℚ) * hinv

theorem ode (G : PowerSeries ℚ) (h : (1 - X - 2 * X ^ 2 : PowerSeries ℚ) * G = exp ℚ) :
    (1 - X - 2 * X ^ 2 : PowerSeries ℚ) * d⁄dX ℚ G = (2 + 3 * X - 2 * X ^ 2) * G := by
  have h1 := congrArg (d⁄dX ℚ) h
  rw [dexp, Derivation.leibniz, smul_eq_mul, smul_eq_mul] at h1
  have hdD : d⁄dX ℚ (1 - X - 2 * X ^ 2 : PowerSeries ℚ) = -1 - 4 * X := by
    simp only [nC, map_sub, Derivation.leibniz, derivative_C, derivative_X, smul_eq_mul, mul_zero,
      add_zero, mul_one, derivative_pow, derivative_one, map_zero]
    simp only [map_ofNat]
    ring
  rw [hdD] at h1
  linear_combination h1 - h

theorem cXd (F : PowerSeries ℚ) (k : ℕ) : coeff k (d⁄dX ℚ F) = coeff (k + 1) F * (k + 1) := by
  rw [coeff_derivative]

end P110322

theorem OMA.solution : type_of% @OMA.S_oeis_a110322.main := by
  intro n hn
  have hL := P110322.gf_eq
  have ha : ∀ m, a m = (m.factorial : ℚ) * coeff m (((1) * W + (0)) * (1 - X - 2 * X ^ 2 : PowerSeries ℚ)⁻¹) :=
    fun m => rfl
  generalize (((1) * W + (0)) * (1 - X - 2 * X ^ 2 : PowerSeries ℚ)⁻¹) = G at hL ha
  have e := congrArg (coeff (n - 1)) (P110322.ode G hL)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 3 := ⟨n - 3, by omega⟩
  simp only [show k + 3 - 1 = k + 2 by omega, show k + 3 - 2 = k + 1 by omega,
    show k + 3 - 3 = k by omega, ha]
  simp only [P110322.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, P110322.cXd, coeff_succ_X_mul, coeff_X, coeff_one, coeff_derivative] at e
  simp at e
  rw [coeff_derivative, coeff_derivative] at e
  have f3 : ((k + 3).factorial : ℚ) = (k + 3) * (k + 2).factorial := by
    rw [show k + 3 = (k + 2) + 1 by omega, Nat.factorial_succ]; push_cast; ring
  have f2 : ((k + 2).factorial : ℚ) = (k + 2) * (k + 1).factorial := by
    rw [show k + 2 = (k + 1) + 1 by omega, Nat.factorial_succ]; push_cast; ring
  have f1 : ((k + 1).factorial : ℚ) = (k + 1) * k.factorial := by
    rw [Nat.factorial_succ]; push_cast; ring
  rw [f3, f2, f1] at *
  push_cast at e ⊢
  linear_combination ((k + 2) * (k + 1) * (k.factorial : ℚ)) * e
