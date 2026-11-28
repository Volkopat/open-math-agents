import OMAStatements.S_oeis_a273722
import Mathlib

namespace OMA.S_oeis_a273722
open PowerSeries

lemma ode2 (T : ℚ⟦X⟧) (hT : T ^ 2 = 1 - 4 * X + 2 * X ^ 2 + X ^ 4) (h0 : coeff 0 T = 1) :
    (1 - 4 * X + 2 * X ^ 2 + X ^ 4) * d⁄dX ℚ T⁻¹ + (-2 + 2 * X + 2 * X ^ 3) * T⁻¹ = 0 := by
  have hTU : T * T⁻¹ = 1 := PowerSeries.mul_inv_cancel T (by
    rw [← coeff_zero_eq_constantCoeff_apply, h0]; norm_num)
  have hd : (2 : ℚ⟦X⟧) * (T * d⁄dX ℚ T) = 2 * (-2 + 2 * X + 2 * X ^ 3) := by
    have c4 : d⁄dX ℚ (4 : ℚ⟦X⟧) = 0 := by rw [← map_ofNat (C (R := ℚ)) 4]; simp
    have c2 : d⁄dX ℚ (2 : ℚ⟦X⟧) = 0 := by rw [← map_ofNat (C (R := ℚ)) 2]; simp
    have := congrArg (d⁄dX ℚ) hT
    simp [Derivation.leibniz_pow, c4, c2] at this
    linear_combination this
  have h2 : T * d⁄dX ℚ T = -2 + 2 * X + 2 * X ^ 3 := mul_left_cancel₀ (by intro h; have := congrArg (constantCoeff (R := ℚ)) h; rw [map_ofNat] at this; norm_num at this : (2 : ℚ⟦X⟧) ≠ 0) hd
  rw [derivative_inv', ← hT, ← h2]
  linear_combination (-(T * d⁄dX ℚ T * T⁻¹)) * hTU


lemma ode3 (T : ℚ⟦X⟧) (hT : T ^ 2 = 1 - 4 * X + 2 * X ^ 2 + X ^ 4) (h0 : coeff 0 T = 1) :
    d⁄dX ℚ T⁻¹ - C (4 : ℚ) * (X * d⁄dX ℚ T⁻¹) + C (2 : ℚ) * (X * (X * d⁄dX ℚ T⁻¹)) + X * (X * (X * (X * d⁄dX ℚ T⁻¹)))
      + (C (-2 : ℚ) * T⁻¹ + C (2 : ℚ) * (X * T⁻¹) + C (2 : ℚ) * (X * (X * (X * T⁻¹)))) = 0 := by
  have := ode2 T hT h0
  have c4 : (C (4 : ℚ) : ℚ⟦X⟧) = 4 := map_ofNat C 4
  have c2 : (C (2 : ℚ) : ℚ⟦X⟧) = 2 := map_ofNat C 2
  have c2' : (C (-2 : ℚ) : ℚ⟦X⟧) = -2 := by rw [map_neg, c2]
  rw [c4, c2, c2']
  linear_combination this

lemma Rw (T : ℚ⟦X⟧) (hT : T ^ 2 = 1 - 4 * X + 2 * X ^ 2 + X ^ 4) (h0 : coeff 0 T = 1) (j : ℕ) :
    ((j : ℚ) + 3) * coeff (j + 4) (X * T⁻¹) - (4 * (j : ℚ) + 10) * coeff (j + 3) (X * T⁻¹)
      + 2 * ((j : ℚ) + 2) * coeff (j + 2) (X * T⁻¹) + ((j : ℚ) + 1) * coeff j (X * T⁻¹) = 0 := by
  have h := ode3 T hT h0
  generalize T⁻¹ = U at h ⊢
  rcases j with _ | _ | j
  · have := congrArg (coeff 2) h
    simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_zero_X_mul, coeff_derivative, map_zero] at this ⊢
    norm_num at this ⊢
    linarith
  · have := congrArg (coeff 3) h
    simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_zero_X_mul, coeff_derivative, map_zero] at this ⊢
    norm_num at this ⊢
    linarith
  · have := congrArg (coeff (j + 4)) h
    simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_zero_X_mul, coeff_derivative, map_zero] at this ⊢
    push_cast at this ⊢
    linarith

lemma Gw (T G : ℚ⟦X⟧) (hT : T ^ 2 = 1 - 4 * X + 2 * X ^ 2 + X ^ 4) (h0 : coeff 0 T = 1)
    (hG : G * (2 * X * T) = 1 - 5 * X + 6 * X ^ 2 - X ^ 3 + X ^ 4 - (1 - 3 * X + X ^ 2) * T) (j : ℕ) :
    2 * coeff (j + 2) G = coeff (j + 4) (X * T⁻¹) - 5 * coeff (j + 3) (X * T⁻¹)
      + 6 * coeff (j + 2) (X * T⁻¹) - coeff (j + 1) (X * T⁻¹) + coeff j (X * T⁻¹) := by
  have hTU : T * T⁻¹ = 1 := PowerSeries.mul_inv_cancel T (by
    rw [← coeff_zero_eq_constantCoeff_apply, h0]; norm_num)
  have e : 2 * (X * G) = (1 - 5 * X + 6 * X ^ 2 - X ^ 3 + X ^ 4) * T⁻¹ - (1 - 3 * X + X ^ 2) := by
    linear_combination T⁻¹ * hG - (2 * X * G + (1 - 3 * X + X ^ 2)) * hTU
  have e2 : C (2 : ℚ) * (X * G) = T⁻¹ - C (5 : ℚ) * (X * T⁻¹) + C (6 : ℚ) * (X * (X * T⁻¹)) - X * (X * (X * T⁻¹))
      + X * (X * (X * (X * T⁻¹))) - (1 - C (3 : ℚ) * X + X * X) := by
    have c : (C (2 : ℚ) : ℚ⟦X⟧) = 2 := map_ofNat C 2
    have c5 : (C (5 : ℚ) : ℚ⟦X⟧) = 5 := map_ofNat C 5
    have c6 : (C (6 : ℚ) : ℚ⟦X⟧) = 6 := map_ofNat C 6
    have c3 : (C (3 : ℚ) : ℚ⟦X⟧) = 3 := map_ofNat C 3
    rw [c, c5, c6, c3]
    linear_combination e
  generalize T⁻¹ = U at e2 ⊢
  rcases j with _ | j
  · have := congrArg (coeff 3) e2
    simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_zero_X_mul, map_zero, coeff_one, coeff_X] at this ⊢
    norm_num at this ⊢
    linarith
  · have := congrArg (coeff (j + 4)) e2
    simp only [map_add, map_sub, coeff_C_mul, coeff_succ_X_mul, coeff_zero_X_mul, map_zero, coeff_one, coeff_X] at this ⊢
    have h1 : j + 4 ≠ 1 := by omega
    have h2 : j + 3 ≠ 1 := by omega
    simp [h1, h2] at this
    rw [show j + 1 + 2 = j + 3 from rfl]
    linarith

end OMA.S_oeis_a273722

theorem OMA.solution : type_of% @OMA.S_oeis_a273722.main := by
  intro T G hT h0 hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have G0 := OMA.S_oeis_a273722.Gw T G hT h0 hG (k + 4)
  have G1 := OMA.S_oeis_a273722.Gw T G hT h0 hG (k + 3)
  have G2 := OMA.S_oeis_a273722.Gw T G hT h0 hG (k + 2)
  have G3 := OMA.S_oeis_a273722.Gw T G hT h0 hG (k + 1)
  have G4 := OMA.S_oeis_a273722.Gw T G hT h0 hG k
  have R0 := OMA.S_oeis_a273722.Rw T hT h0 (k + 4)
  have R1 := OMA.S_oeis_a273722.Rw T hT h0 (k + 3)
  have R2 := OMA.S_oeis_a273722.Rw T hT h0 (k + 2)
  have R3 := OMA.S_oeis_a273722.Rw T hT h0 (k + 1)
  have R4 := OMA.S_oeis_a273722.Rw T hT h0 k
  simp only [Nat.add_assoc, Nat.reduceAdd] at G0 G1 G2 G3 G4 R0 R1 R2 R3 R4
  rw [show k + 6 - 1 = k + 5 by omega, show k + 6 - 2 = k + 4 by omega, show k + 6 - 3 = k + 3 by omega,
    show k + 6 - 4 = k + 2 by omega]
  push_cast at G0 G1 G2 G3 G4 R0 R1 R2 R3 R4 ⊢
  linear_combination (-2*(k:ℚ)^4 - 22*(k:ℚ)^3 - 127*(k:ℚ)^2/2 - 105*(k:ℚ)/2 : ℚ) * G0 + (8*(k:ℚ)^4 + 84*(k:ℚ)^3 + 294*(k:ℚ)^2 + 405*(k:ℚ) + 189 : ℚ) * G1 + (-4*(k:ℚ)^4 - 40*(k:ℚ)^3 - 145*(k:ℚ)^2 - 225*(k:ℚ) - 133 : ℚ) * G2 + (4*(k:ℚ)^2 + 22*(k:ℚ) + 28 : ℚ) * G3 + (-2*(k:ℚ)^4 - 18*(k:ℚ)^3 - 115*(k:ℚ)^2/2 - 153*(k:ℚ)/2 - 35 : ℚ) * G4 + (-2*(k:ℚ)^3 - 8*(k:ℚ)^2 - 15*(k:ℚ)/2 : ℚ) * R0 + (10*(k:ℚ)^3 + 50*(k:ℚ)^2 + 147*(k:ℚ)/2 + 63/2 : ℚ) * R1 + (-12*(k:ℚ)^3 - 72*(k:ℚ)^2 - 131*(k:ℚ) - 77 : ℚ) * R2 + (2*(k:ℚ)^3 + 14*(k:ℚ)^2 + 67*(k:ℚ)/2 + 63/2 : ℚ) * R3 + (-2*(k:ℚ)^3 - 16*(k:ℚ)^2 - 83*(k:ℚ)/2 - 35 : ℚ) * R4
