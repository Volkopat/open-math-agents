import OMAStatements.S_oeis_a071717

open PowerSeries

private theorem coeff_ofNat_mul (n k : ℕ) [k.AtLeastTwo] (f : ℚ⟦X⟧) :
    coeff n ((ofNat(k) : ℚ⟦X⟧) * f) = ofNat(k) * coeff n f := by
  rw [← map_ofNat (PowerSeries.C : ℚ →+* ℚ⟦X⟧), coeff_C_mul]

private theorem series_ofNat_ne_zero (k : ℕ) [k.AtLeastTwo] (hk : (ofNat(k) : ℚ) ≠ 0) :
    (ofNat(k) : ℚ⟦X⟧) ≠ 0 := by
  intro h
  have hz := congrArg (constantCoeff (R := ℚ)) h
  rw [map_ofNat, map_zero] at hz
  exact hk hz

private theorem derivative_numeral (m : ℕ) [m.AtLeastTwo] :
    derivative ℚ (no_index (OfNat.ofNat m : ℚ⟦X⟧)) = 0 := by
  rw [← map_ofNat C m]
  exact derivative_C

private theorem coeff_X_derivative (G : ℚ⟦X⟧) (k : ℕ) :
    coeff k (X * derivative ℚ G) = (k : ℚ) * coeff k G := by
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_succ_X_mul, coeff_derivative, mul_comm]
    simp only [Nat.cast_add, Nat.cast_one]

/-- The coefficients of `sqrt (1 - 4 x)` satisfy a first order recurrence. -/
private theorem sqrt_coeff_rec (S : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X) (m : ℕ) :
    ((m : ℚ) + 1) * coeff (m + 1) S = (4 * (m : ℚ) - 2) * coeff m S := by
  have hd : 2 * S * derivative ℚ S = -4 := by
    have h := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hS
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at h
    linear_combination h
  have hode : derivative ℚ S - 4 * (X * derivative ℚ S) = -(2 * S) := by
    apply mul_left_cancel₀ (series_ofNat_ne_zero 2 (by norm_num))
    linear_combination S * hd - 2 * derivative ℚ S * hS
  have h := congrArg (coeff m) hode
  simp only [map_sub, map_neg, coeff_ofNat_mul, coeff_X_derivative, coeff_derivative] at h
  linear_combination h

theorem OMA.solution : type_of% @OMA.S_oeis_a071717.main := by
  intro S c G hS _ hc hG n hn
  have hSc : S = 1 - 2 * X * c := by linear_combination hc
  have hcat : c = 1 + X * c ^ 2 := by
    apply mul_left_cancel₀ (a := (4 : ℚ⟦X⟧) * X)
      (mul_ne_zero (series_ofNat_ne_zero 4 (by norm_num)) X_ne_zero)
    have h := hS
    rw [hSc] at h
    linear_combination -h
  have h2 : X ^ 1 * c ^ 2 = (1 : ℚ⟦X⟧) * c - (1 : ℚ⟦X⟧) := by
    linear_combination -hcat
  have h3 : X ^ 2 * c ^ 3 = (1 - X : ℚ⟦X⟧) * c - (1 : ℚ⟦X⟧) := by
    linear_combination (X * c) * h2 - (1 : ℚ⟦X⟧) * hcat
  have hmain : 2 * (X ^ 2 * G) = (1 - X - 3 * X ^ 2 : ℚ⟦X⟧) - ((X ^ 0 * S) + (X ^ 1 * S) - (X ^ 2 * S)) := by
    rw [hSc, hG]
    linear_combination (2 * X) * h2 + (2 * X ^ 2) * h3
  have ha : ∀ m : ℕ, 1 ≤ m → 2 * coeff m G = -(coeff (m + 2) S + coeff (m + 1) S - coeff (m + 0) S) := by
    intro m hm
    have e0 : coeff (m + 2) (X ^ 0 * S) = coeff (m + 2) S := by
      rw [show m + 2 = (m + 2) + 0 by omega, coeff_X_pow_mul]
    have e1 : coeff (m + 2) (X ^ 1 * S) = coeff (m + 1) S := by
      rw [show m + 2 = (m + 1) + 1 by omega, coeff_X_pow_mul]
    have e2 : coeff (m + 2) (X ^ 2 * S) = coeff (m + 0) S := by
      rw [show m + 2 = (m + 0) + 2 by omega, coeff_X_pow_mul]
    have eG : coeff (m + 2) (X ^ 2 * G) = coeff m G := coeff_X_pow_mul _ _ _
    have h := congrArg (coeff (m + 2)) hmain
    have hP : coeff (m + 2) (1 - X - 3 * X ^ 2 : ℚ⟦X⟧) = 0 := by
      simp (disch := omega) only [map_add, map_sub, map_neg, coeff_ofNat_mul, coeff_one,
        coeff_X, coeff_X_pow, if_neg, mul_zero, add_zero, sub_zero, neg_zero]
    simp only [map_add, map_sub, map_neg, coeff_ofNat_mul, hP, eG, e0, e1, e2] at h
    linear_combination h
  have hs := sqrt_coeff_rec S hS
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have r1 : coeff (k + 2) S =
      (4 * ((k : ℚ) + 1) - 2) / ((k : ℚ) + 2) * coeff (k + 1) S := by
    have h := hs (k + 1)
    rw [show k + 1 + 1 = k + 2 by omega] at h
    push_cast at h
    have hne : (k : ℚ) + 2 ≠ 0 := by positivity
    rw [div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination h
  have r2 : coeff (k + 3) S =
      (4 * ((k : ℚ) + 2) - 2) / ((k : ℚ) + 3) * coeff (k + 2) S := by
    have h := hs (k + 2)
    rw [show k + 2 + 1 = k + 3 by omega] at h
    push_cast at h
    have hne : (k : ℚ) + 3 ≠ 0 := by positivity
    rw [div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination h
  have r3 : coeff (k + 4) S =
      (4 * ((k : ℚ) + 3) - 2) / ((k : ℚ) + 4) * coeff (k + 3) S := by
    have h := hs (k + 3)
    rw [show k + 3 + 1 = k + 4 by omega] at h
    push_cast at h
    have hne : (k : ℚ) + 4 ≠ 0 := by positivity
    rw [div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination h
  have r4 : coeff (k + 5) S =
      (4 * ((k : ℚ) + 4) - 2) / ((k : ℚ) + 5) * coeff (k + 4) S := by
    have h := hs (k + 4)
    rw [show k + 4 + 1 = k + 5 by omega] at h
    push_cast at h
    have hne : (k : ℚ) + 5 ≠ 0 := by positivity
    rw [div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination h
  have r5 : coeff (k + 6) S =
      (4 * ((k : ℚ) + 5) - 2) / ((k : ℚ) + 6) * coeff (k + 5) S := by
    have h := hs (k + 5)
    rw [show k + 5 + 1 = k + 6 by omega] at h
    push_cast at h
    have hne : (k : ℚ) + 6 ≠ 0 := by positivity
    rw [div_mul_eq_mul_div, eq_div_iff hne]
    linear_combination h
  have A4 : coeff (k + 4) G = -(coeff (k + 6) S + coeff (k + 5) S - coeff (k + 4) S) / 2 := by
    have h := ha (k + 4) (by omega)
    simp only [add_assoc, Nat.reduceAdd, Nat.add_zero] at h ⊢
    linear_combination h / 2
  have A3 : coeff (k + 3) G = -(coeff (k + 5) S + coeff (k + 4) S - coeff (k + 3) S) / 2 := by
    have h := ha (k + 3) (by omega)
    simp only [add_assoc, Nat.reduceAdd, Nat.add_zero] at h ⊢
    linear_combination h / 2
  have A2 : coeff (k + 2) G = -(coeff (k + 4) S + coeff (k + 3) S - coeff (k + 2) S) / 2 := by
    have h := ha (k + 2) (by omega)
    simp only [add_assoc, Nat.reduceAdd, Nat.add_zero] at h ⊢
    linear_combination h / 2
  have A1 : coeff (k + 1) G = -(coeff (k + 3) S + coeff (k + 2) S - coeff (k + 1) S) / 2 := by
    have h := ha (k + 1) (by omega)
    simp only [add_assoc, Nat.reduceAdd, Nat.add_zero] at h ⊢
    linear_combination h / 2
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega, show k + 4 - 3 = k + 1 by omega]
  rw [A4, A3, A2, A1]
  rw [r5, r4, r3, r2, r1]
  push_cast
  have d2 : (k : ℚ) + 2 ≠ 0 := by positivity
  have d3 : (k : ℚ) + 3 ≠ 0 := by positivity
  have d4 : (k : ℚ) + 4 ≠ 0 := by positivity
  have d5 : (k : ℚ) + 5 ≠ 0 := by positivity
  have d6 : (k : ℚ) + 6 ≠ 0 := by positivity
  field_simp
  ring
