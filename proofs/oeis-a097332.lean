import OMAStatements.S_oeis_a097332
import Mathlib

open PowerSeries

namespace OMA.A097332Proof

open OMA.S_oeis_a097332

/-- The square of `rootSeries` is `(1 + X) (1 - 3X)`. -/
lemma root_sq : rootSeries * rootSeries = (1 + X) * (1 - 3 * X) := by
  have hB : PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) * PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) = 1 + X := by
    rw [← PowerSeries.binomialSeries_add]
    have : (1 / 2 + 1 / 2 : ℚ) = ((1 : ℕ) : ℚ) := by norm_num
    rw [this, PowerSeries.binomialSeries_nat, pow_one]
  have hR : rescale (-3 : ℚ) (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) *
      rescale (-3 : ℚ) (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) = 1 - 3 * X := by
    rw [← map_mul, hB, map_add, map_one, rescale_X, map_neg]
    have : (C (3 : ℚ) : ℚ⟦X⟧) = 3 := map_ofNat C 3
    rw [this]; ring
  calc rootSeries * rootSeries
      = (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) * PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) *
        (rescale (-3 : ℚ) (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) *
          rescale (-3 : ℚ) (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ))) := by
        unfold rootSeries; ring
    _ = (1 + X) * (1 - 3 * X) := by rw [hB, hR]

lemma root_const : constantCoeff rootSeries = 1 := by
  have : constantCoeff (rescale (-3 : ℚ) (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ))) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale]; simp
  simp only [rootSeries, map_mul, this, binomialSeries_constantCoeff, mul_one]

/-- `rootSeries = 1 + X - 2 X (1 - X) a`. -/
lemma root_eq : rootSeries = 1 + X - 2 * X * (1 - X) * generatingSeries := by
  have hDc : constantCoeff (1 - X + rootSeries : ℚ⟦X⟧) ≠ 0 := by
    norm_num [root_const]
  have h1 := PowerSeries.mul_inv_cancel _ hDc
  have hEc : constantCoeff (1 - X : ℚ⟦X⟧) ≠ 0 := by simp
  have h2 := PowerSeries.mul_inv_cancel _ hEc
  have h3 := root_sq
  unfold generatingSeries
  linear_combination (1 - X - rootSeries) * h1 + (1 - X + rootSeries)⁻¹ * h3 +
    2 * X * (1 + 2 * X * (1 - X + rootSeries)⁻¹) * h2

lemma d_one : d⁄dX ℚ (1 : ℚ⟦X⟧) = 0 := (d⁄dX ℚ).map_one_eq_zero

lemma d_two : d⁄dX ℚ (2 : ℚ⟦X⟧) = 0 := by
  rw [show (2 : ℚ⟦X⟧) = ((2 : ℕ) : ℚ⟦X⟧) by norm_num]; exact (d⁄dX ℚ).map_natCast 2

lemma d_three : d⁄dX ℚ (3 : ℚ⟦X⟧) = 0 := by
  rw [show (3 : ℚ⟦X⟧) = ((3 : ℕ) : ℚ⟦X⟧) by norm_num]; exact (d⁄dX ℚ).map_natCast 3

lemma two_ne : (2 : ℚ⟦X⟧) ≠ 0 := by
  intro h
  have := congrArg (coeff 0) h
  rw [show (2 : ℚ⟦X⟧) = C (2 : ℚ) from (map_ofNat C 2).symm, coeff_C] at this
  norm_num at this

/-- The linear differential equation satisfied by `rootSeries`. -/
lemma root_ode : (1 + X) * (1 - 3 * X) * d⁄dX ℚ rootSeries + (1 + 3 * X) * rootSeries = 0 := by
  have h := congrArg (d⁄dX ℚ) root_sq
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_sub, derivative_X, d_one, d_three] at h
  have h2 : (2 : ℚ⟦X⟧) * ((1 + X) * (1 - 3 * X) * d⁄dX ℚ rootSeries + (1 + 3 * X) * rootSeries)
      = 0 := by
    linear_combination (-2 * d⁄dX ℚ rootSeries) * root_sq + rootSeries * h
  exact (mul_eq_zero.mp h2).resolve_left two_ne

/-- The differential equation satisfied by the generating function. -/
lemma gen_ode :
    generatingSeries - 3 * (X * generatingSeries) + 3 * (X ^ 2 * generatingSeries) +
      3 * (X ^ 3 * generatingSeries) + X * d⁄dX ℚ generatingSeries -
      3 * (X ^ 2 * d⁄dX ℚ generatingSeries) - X ^ 3 * d⁄dX ℚ generatingSeries +
      3 * (X ^ 4 * d⁄dX ℚ generatingSeries) = 1 + X := by
  have h := root_ode
  rw [root_eq] at h
  simp only [Derivation.leibniz, smul_eq_mul, map_add, map_sub, derivative_X, d_one, d_two] at h
  have h2 : (2 : ℚ⟦X⟧) * (generatingSeries - 3 * (X * generatingSeries) +
      3 * (X ^ 2 * generatingSeries) + 3 * (X ^ 3 * generatingSeries) +
      X * d⁄dX ℚ generatingSeries - 3 * (X ^ 2 * d⁄dX ℚ generatingSeries) -
      X ^ 3 * d⁄dX ℚ generatingSeries + 3 * (X ^ 4 * d⁄dX ℚ generatingSeries) - (1 + X)) = 0 := by
    linear_combination (-1 : ℚ⟦X⟧) * h
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left two_ne)

lemma coeff_three_mul (n : ℕ) (f : ℚ⟦X⟧) : coeff n ((3 : ℚ⟦X⟧) * f) = 3 * coeff n f := by
  rw [show (3 : ℚ⟦X⟧) = C (3 : ℚ) from (map_ofNat C 3).symm, coeff_C_mul]

end OMA.A097332Proof

open OMA.A097332Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a097332.main := by
  intro k
  have h := congrArg (coeff (k + 3)) OMA.A097332Proof.gen_ode
  simp only [map_add, map_sub, coeff_three_mul, coeff_X_pow_mul', coeff_derivative] at h
  rw [show (X : ℚ⟦X⟧) = X ^ 1 from (pow_one X).symm] at h
  simp only [coeff_X_pow_mul', coeff_one, coeff_X_pow, coeff_derivative] at h
  unfold OMA.S_oeis_a097332.a
  rcases k with _ | k
  · norm_num at h ⊢
    linear_combination h
  · simp only [show 1 ≤ k + 1 + 3 by omega, show 2 ≤ k + 1 + 3 by omega,
      show 3 ≤ k + 1 + 3 by omega, show 4 ≤ k + 1 + 3 by omega, if_true,
      show k + 1 + 3 - 1 = k + 3 by omega, show k + 1 + 3 - 2 = k + 2 by omega,
      show k + 1 + 3 - 3 = k + 1 by omega, show k + 1 + 3 - 4 = k by omega,
      show k + 1 + 3 ≠ 0 by omega, show k + 1 + 3 ≠ 1 by omega, if_false] at h
    simp only [show k + 3 + 1 = k + 1 + 3 by omega, show k + 2 + 1 = k + 1 + 2 by omega,
      show k + 1 + 1 = k + 1 + 1 from rfl] at h
    push_cast at h ⊢
    linear_combination h
