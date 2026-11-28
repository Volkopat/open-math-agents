import OMAStatements.S_oeis_a119967
import Mathlib

open OMA.S_oeis_a119967
open PowerSeries

namespace P119967

theorem hR0 : constantCoeff (R - 1 : PowerSeries ℚ) = 0 := by simp [R]

theorem S_sq : S ^ 2 = R := by
  have hB : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = (1 + X : PowerSeries ℚ) := by
    rw [sq, ← PowerSeries.binomialSeries_add]
    norm_num
    simpa using binomialSeries_nat (A := ℚ) (R := ℚ) 1
  have h0 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' hR0
  unfold S
  rw [← subst_pow h0, hB, ← coe_substAlgHom h0, map_add, map_one,
    coe_substAlgHom, subst_X h0]
  ring

theorem S0 : constantCoeff S = 1 := by
  have h0 : HasSubst (R - 1) := HasSubst.of_constantCoeff_zero' hR0
  have hz := constantCoeff_subst_eq_zero hR0 (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) - 1)
    (by simp [PowerSeries.binomialSeries_constantCoeff])
  have he : subst (R - 1) (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ) - 1) = S - 1 := by
    rw [← coe_substAlgHom h0, map_sub, map_one, coe_substAlgHom]; rfl
  rw [he] at hz
  have : constantCoeff (S - 1) = 0 := hz
  rw [map_sub, map_one, sub_eq_zero] at this
  exact this

theorem gf_eq : (2 - 4 * X - 2 * X ^ 2 : PowerSeries ℚ) *
    ((-X ^ 2 + 3 * X ^ 3 - X ^ 4 - X ^ 5 + (X ^ 2 - X ^ 3) * S)
      * (2 - 4 * X - 2 * X ^ 2 : PowerSeries ℚ)⁻¹) =
    -X ^ 2 + 3 * X ^ 3 - X ^ 4 - X ^ 5 + (X ^ 2 - X ^ 3) * S := by
  have hd : constantCoeff (2 - 4 * X - 2 * X ^ 2 : PowerSeries ℚ) ≠ 0 := by
    simp only [map_sub, map_mul, map_pow, constantCoeff_X, map_ofNat]
    norm_num
  have hinv := PowerSeries.mul_inv_cancel (2 - 4 * X - 2 * X ^ 2 : PowerSeries ℚ) hd
  linear_combination (-X ^ 2 + 3 * X ^ 3 - X ^ 4 - X ^ 5 + (X ^ 2 - X ^ 3) * S) * hinv

theorem nC (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : PowerSeries ℚ) = C (OfNat.ofNat n : ℚ) :=
  (map_ofNat C n).symm

theorem sq_coeff (k : ℕ) : coeff k (S ^ 2) = ∑ i ∈ Finset.range (k + 1), coeff i S * coeff (k - i) S := by
  rw [sq, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun i j => coeff i S * coeff j S)]

theorem Rc (k : ℕ) : coeff k R = if k = 0 then 1 else if k = 1 then -4 else if k = 2 then 6
    else if k = 3 then -4 else if k = 4 then -3 else 0 := by
  simp only [R, nC, map_add, map_sub, coeff_C_mul, coeff_X_pow, coeff_X, coeff_one]
  rcases k with _ | _ | _ | _ | _ | k <;> simp

theorem vals : coeff 4 S = -2 ∧ coeff 3 S = 0 ∧ coeff 2 S = 1 ∧ coeff 1 S = -2 ∧ coeff 0 S = 1 ∧
    coeff 5 S = -4 ∧ coeff 6 S = -6 := by
  have h0 : coeff 0 S = 1 := by rw [coeff_zero_eq_constantCoeff_apply, S0]
  have e := fun k => (sq_coeff k).symm.trans ((congrArg (coeff k) S_sq).trans (Rc k))
  have e1 := e 1; have e2 := e 2; have e3 := e 3; have e4 := e 4; have e5 := e 5; have e6 := e 6
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at e1 e2 e3 e4 e5 e6
  simp only [Nat.reduceSub, coeff_zero_eq_constantCoeff_apply, S0] at e1 e2 e3 e4 e5 e6
  norm_num at e1 e2 e3 e4 e5 e6
  have h1 : coeff 1 S = -2 := by linarith
  rw [h1] at e2 e3 e4 e5 e6
  have h2 : coeff 2 S = 1 := by linarith
  rw [h2] at e3 e4 e5 e6
  have h3 : coeff 3 S = 0 := by linarith
  rw [h3] at e4 e5 e6
  have h4 : coeff 4 S = -2 := by linarith
  rw [h4] at e5 e6
  have h5 : coeff 5 S = -4 := by linarith
  rw [h5] at e6
  have h6 : coeff 6 S = -6 := by linarith
  exact ⟨h4, h3, h2, h1, h0, h5, h6⟩

end P119967

theorem OMA.disproof : ¬ (type_of% @OMA.S_oeis_a119967.main) := by
  intro h
  have h4 := h 4 le_rfl
  have hL := P119967.gf_eq
  have ha : ∀ m, a m = coeff (m + 4) ((-X ^ 2 + 3 * X ^ 3 - X ^ 4 - X ^ 5 + (X ^ 2 - X ^ 3) * S)
      * (2 - 4 * X - 2 * X ^ 2 : PowerSeries ℚ)⁻¹) := fun m => rfl
  generalize ((-X ^ 2 + 3 * X ^ 3 - X ^ 4 - X ^ 5 + (X ^ 2 - X ^ 3) * S)
      * (2 - 4 * X - 2 * X ^ 2 : PowerSeries ℚ)⁻¹) = A at hL ha
  obtain ⟨s4, s3, s2, s1, s0, s5, s6⟩ := P119967.vals
  have c := fun k => congrArg (coeff k) hL
  have c0 := c 0; have c1 := c 1; have c2 := c 2; have c3 := c 3; have c4 := c 4
  have c5 := c 5; have c6 := c 6; have c7 := c 7; have c8 := c 8
  simp only [P119967.nC, sub_mul, add_mul, neg_mul, pow_succ, pow_zero, one_mul, mul_assoc, map_add,
    map_sub, map_neg, coeff_C_mul, coeff_succ_X_mul, coeff_zero_X_mul, coeff_X, coeff_one,
    coeff_zero_eq_constantCoeff_apply, map_mul, constantCoeff_X, zero_mul] at c0 c1 c2 c3 c4 c5 c6 c7 c8
  simp only [← coeff_zero_eq_constantCoeff_apply] at c0 c1 c2 c3 c4 c5 c6 c7 c8
  norm_num [s0, s1, s2, s3, s4, s5, s6] at c0 c1 c2 c3 c4 c5 c6 c7 c8
  simp only [ha] at h4
  norm_num at h4
  have g0 : coeff 0 A = 0 := by linarith
  have g1 : coeff 1 A = 0 := by linarith
  have g2 : coeff 2 A = 0 := by linarith
  have g3 : coeff 3 A = 0 := by linarith
  have g4 : coeff 4 A = 1 := by linarith
  have g5 : coeff 5 A = 1 := by linarith
  have g6 : coeff 6 A = 2 := by linarith
  have g7 : coeff 7 A = 4 := by linarith
  have g8 : coeff 8 A = 9 := by linarith
  rw [g4, g5, g6, g7, g8] at h4
  norm_num at h4
