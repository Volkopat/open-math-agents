import OMAStatements.S_oeis_a054341
import Mathlib.Tactic

open PowerSeries OMA.S_oeis_a054341

namespace CentralConvolution

lemma catalan_equation :
    doubleCatalan^2 * (X : PowerSeries ℚ)^2 + 1 = doubleCatalan := by
  have h := congrArg (fun p : PowerSeries ℕ =>
    expand 2 (by decide) (map (Nat.castRingHom ℚ) p)) catalanSeries_sq_mul_X_add_one
  simpa [doubleCatalan] using h

lemma series_identity : (2-5*X)*series = 2-X*doubleCatalan := by
  let den : PowerSeries ℚ := 1 - 2*X*doubleCatalan
  have unit : constantCoeff den ≠ 0 := by simp [den]
  have hx : (2-5*X)*doubleCatalan = (2-X*doubleCatalan)*den := by
    dsimp [den]
    linear_combination -2*catalan_equation
  change (2-5*X)*(doubleCatalan*den⁻¹) = _
  rw [← mul_assoc, hx, mul_assoc, PowerSeries.mul_inv_cancel den unit, mul_one]

lemma difference (n : ℕ) : 2*a (n+1)-5*a n = -coeff n doubleCatalan := by
  have h : C (2:ℚ)*series - C (5:ℚ)*(series*X) =
      C (2:ℚ) - doubleCatalan*X := by
    simp only [map_ofNat]
    linear_combination series_identity
  have h' := congrArg (fun p : PowerSeries ℚ => coeff (n+1) p) h
  simpa [a, coeff_C_mul, coeff_C, coeff_succ_mul_X] using h'

lemma catalan_ratio (k : ℕ) : ((k:ℚ)+2)*catalan (k+1) =
    2*(2*(k:ℚ)+1)*catalan k := by
  have h := Nat.succ_mul_centralBinom_succ k
  rw [← succ_mul_catalan_eq_centralBinom (k+1), ← succ_mul_catalan_eq_centralBinom k] at h
  have hq := congrArg (fun z : ℕ => (z:ℚ)) h
  push_cast at hq
  apply (mul_left_cancel₀ (a := (k:ℚ)+1) (by positivity))
  linear_combination hq

lemma coeff_recurrence (t : ℕ) : ((t:ℚ)+4)*coeff (t+2) doubleCatalan =
    4*((t:ℚ)+1)*coeff t doubleCatalan := by
  obtain ⟨k, rfl | rfl⟩ : ∃ k, t=2*k ∨ t=2*k+1 := ⟨t/2, by omega⟩
  · rw [show 2*k+2 = 2*(k+1) by omega]
    simp only [doubleCatalan, coeff_expand_mul, coeff_map, catalanSeries_coeff,
      Nat.cast_mul, Nat.cast_ofNat]
    linear_combination 2*catalan_ratio k
  · have h₀ : ¬ 2 ∣ 2*k+1 := by omega
    have h₁ : ¬ 2 ∣ 2*k+1+2 := by omega
    simp [doubleCatalan, coeff_expand, h₀, h₁]

end CentralConvolution

open CentralConvolution

theorem OMA.solution : type_of% @OMA.S_oeis_a054341.main := by
  intro t
  linear_combination ((t:ℚ)+4)*difference (t+2) -
    4*((t:ℚ)+1)*difference t - coeff_recurrence t
