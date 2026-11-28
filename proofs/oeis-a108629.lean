import OMAStatements.S_oeis_a108629

/-!
The taloscoreagent proof of R. J. Mathar's order-five recurrence for OEIS A108629,
first posted with statement PR #141. Raimo33 supplied a separate proof in #5993.
The square root in the defining generating function gives a quadratic
equation. Differentiate it and eliminate the quadratic term to obtain a
linear differential equation, then compare the coefficients of degree n - 1.
Mathar's general recurrence theorem for radical generating functions also
applies to this family (arXiv:2109.02112, Theorem 5).
-/

namespace OMA108

open PowerSeries OMA.S_oeis_a108629

/-- Squaring the binomial series selects the prescribed radicand. -/
theorem square_root_identity : rootSeries ^ 2 = 1 + radicandTail := by
  have hs : HasSubst radicandTail := HasSubst.of_constantCoeff_zero' (by simp [radicandTail])
  have h : (PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2 = 1 + (X : PowerSeries ℚ) := by
    rw [pow_two, ← binomialSeries_add]
    have h1 : (1 / 2 : ℚ) + 1 / 2 = ((1 : ℕ) : ℚ) := by norm_num
    rw [h1, binomialSeries_nat, pow_one]
  calc
    rootSeries ^ 2 = subst radicandTail ((PowerSeries.binomialSeries ℚ (1 / 2 : ℚ)) ^ 2) :=
      (subst_pow hs _ 2).symm
    _ = 1 + radicandTail := by
      rw [h, ← coe_substAlgHom hs, map_add, map_one, substAlgHom_X hs]

/-- Clearing the denominator and squaring gives the defining quadratic. -/
theorem defining_equation :
    (1 + X + X ^ 2) * series ^ 2 - (1 + X) * series + X = 0 := by
  let B : PowerSeries ℚ := 1 + X + X ^ 2
  have hb : constantCoeff (2 * B) ≠ 0 := by
    simp [B, map_ofNat]
  have hF : (2 * B) * series = 1 + X - rootSeries := by
    unfold series
    change (2 * B) * ((1 + X - rootSeries) * (2 * B)⁻¹) = _
    rw [mul_left_comm, PowerSeries.mul_inv_cancel _ hb, mul_one]
  have hS : rootSeries = 1 + X - 2 * B * series := by linear_combination hF
  have hs := square_root_identity
  rw [hS] at hs
  have hz : (4 * B) * (B * series ^ 2 - (1 + X) * series + X) = 0 := by
    dsimp [B, radicandTail] at hs ⊢
    linear_combination hs
  have unit : IsUnit (4 * B) := isUnit_iff_constantCoeff.mpr (by norm_num [B, map_ofNat])
  exact (mul_eq_zero.mp hz).resolve_left unit.ne_zero

/-- Eliminate the quadratic term from the equation and its derivative. -/
theorem quadratic_ode (F : PowerSeries ℚ)
    (h : (1 + X + X ^ 2) * F ^ 2 - (1 + X) * F + X = 0) :
    (1 - X - 4 * X ^ 2 - 9 * X ^ 3 - 7 * X ^ 4 - 4 * X ^ 5) * derivative ℚ F =
      (-2 - 4 * X - 3 * X ^ 2 + X ^ 3 + 2 * X ^ 4) * F +
        (1 + X + 3 * X ^ 2 + X ^ 3) := by
  have hd := congrArg (derivative ℚ) h
  simp only [map_add, map_sub, Derivation.leibniz, derivative_pow, derivative_one,
    derivative_X, map_zero, smul_eq_mul, Nat.cast_ofNat, Nat.reduceSub,
    pow_one, mul_one, zero_add] at hd
  linear_combination
    (1 + X + X ^ 2) * (2 * (1 + X + X ^ 2) * F - (1 + X)) * hd -
    (4 * (1 + X + X ^ 2) ^ 2 * derivative ℚ F +
      (2 * (1 + X + X ^ 2) * F - (1 + X)) * (1 + 2 * X) +
      2 * (2 * X + X ^ 2)) * h

end OMA108

open PowerSeries OMA.S_oeis_a108629 OMA108 in
theorem OMA.solution : type_of% @OMA.S_oeis_a108629.main := by
  intro n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 6 := ⟨n - 6, by omega⟩
  have hc := congrArg (coeff (k + 5)) (quadratic_ode _ defining_equation)
  simp only [sub_mul, add_mul, neg_mul, mul_assoc, one_mul, map_add, map_sub, map_neg,
    ← map_ofNat (C (R := ℚ)), coeff_C_mul] at hc
  simp [coeff_succ_X_mul (k + 4), coeff_X_pow_mul', coeff_derivative, coeff_X_pow,
    coeff_one, coeff_X] at hc
  unfold a
  push_cast
  linear_combination hc
