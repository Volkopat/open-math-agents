import OMAStatements.S_oeis_a126089

open PowerSeries OMA.S_oeis_a126089

private theorem derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]
  exact derivative_C

private noncomputable def euler (F : ℚ⟦X⟧) := X * derivative ℚ F

private theorem coeff_euler (n : ℕ) (F : ℚ⟦X⟧) :
    coeff n (euler F) = (n : ℚ) * coeff n F := by
  cases n with
  | zero => simp [euler]
  | succ n => rw [euler, coeff_succ_X_mul, coeff_derivative, mul_comm, Nat.cast_succ]

theorem OMA.solution : type_of% @OMA.S_oeis_a126089.main := by
  intro F hF _ n hn
  let d := derivative ℚ
  have hFactor : (2 * (1 - 2 * X) : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (constantCoeff (R := ℚ)) h
    simp only [map_mul, map_sub, map_one, constantCoeff_X, mul_zero, sub_zero,
      mul_one, map_zero] at hc
    rw [← map_ofNat C 2, constantCoeff_C] at hc
    norm_num at hc
  have hLinear : (1 - 2 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    exact hFactor (by rw [h, mul_zero])
  have hd := congrArg (fun f => d f) hF
  change derivative ℚ _ = derivative ℚ _ at hd
  simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
  have hFirst : (1 - 2 * X) * (1 - 4 * X) * d F = (-4 + 12 * X) * F := by
    apply mul_left_cancel₀ hFactor
    change _ * ((1 - 2 * X) * (1 - 4 * X) * derivative ℚ F) = _
    linear_combination F * hd - 2 * derivative ℚ F * hF
  have hSecond : (1 - 2 * X) * (1 - 4 * X) * d (d F) +
      (-2 + 4 * X) * d F - 12 * F = 0 := by
    have h := congrArg (fun f => d f) hFirst
    dsimp only [d] at h ⊢
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at h
    linear_combination h
  have hRec : 4 * euler F - euler (euler F) +
      X * (4 * euler (euler F) - 14 * euler F + 12 * F) = 0 := by
    apply mul_left_cancel₀ hLinear
    dsimp only [euler, d] at *
    simp only [Derivation.leibniz, smul_eq_mul, derivative_X, mul_one] at ⊢
    linear_combination X * (-X * hSecond + 3 * hFirst)
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  have hc := congrArg (coeff (k + 1)) hRec
  simp only [map_add, map_sub, ← map_ofNat C, coeff_C_mul, coeff_euler,
    coeff_succ_X_mul, map_zero] at hc
  simp only [a, Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul]
  push_cast at hc ⊢
  linear_combination (k.factorial : ℚ) * hc
