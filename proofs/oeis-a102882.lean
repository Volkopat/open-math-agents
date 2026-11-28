import OMAStatements.S_oeis_a102882

open PowerSeries

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

private theorem first_order (S G : ℚ⟦X⟧)
    (hS : S ^ 2 = 1 + 4 * X + 2 * X ^ 2 - 12 * X ^ 3 - 15 * X ^ 4)
    (hS0 : coeff 0 S = 1) (hG : G * S = 1 + 2 * X) :
    (1 + 2 * X) * (1 + 4 * X + 2 * X ^ 2 - 12 * X ^ 3 - 15 * X ^ 4) * derivative ℚ G
      + (-2 * X - 18 * X ^ 2 - 42 * X ^ 3 - 30 * X ^ 4) * G = 0 := by
  have h2 : (2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    simp [map_ofNat] at hc
  have hS1 : S ≠ 0 := by
    intro h
    rw [h] at hS0
    simp at hS0
  have hSd : (1 + 4 * X + 2 * X ^ 2 - 12 * X ^ 3 - 15 * X ^ 4) * derivative ℚ S
      = (2 + 2 * X - 18 * X ^ 2 - 30 * X ^ 3) * S := by
    have hd : 2 * S * derivative ℚ S = 4 + 4 * X - 36 * X ^ 2 - 60 * X ^ 3 := by
      have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hS
      simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at hd
      linear_combination hd
    apply mul_left_cancel₀ (mul_ne_zero h2 hS1)
    linear_combination (1 + 4 * X + 2 * X ^ 2 - 12 * X ^ 3 - 15 * X ^ 4 : ℚ⟦X⟧) * hd
      - (2 * (2 + 2 * X - 18 * X ^ 2 - 30 * X ^ 3) : ℚ⟦X⟧) * hS
  have hGd : derivative ℚ G * S + G * derivative ℚ S = 2 := by
    have hd := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hG
    simp [derivative_numeral, Derivation.leibniz, smul_eq_mul] at hd
    linear_combination hd
  apply mul_left_cancel₀ hS1
  linear_combination ((1 + 2 * X) * (1 + 4 * X + 2 * X ^ 2 - 12 * X ^ 3 - 15 * X ^ 4) : ℚ⟦X⟧) * hGd
    - ((1 + 2 * X) * G) * hSd
    - (2 * (1 + 4 * X + 2 * X ^ 2 - 12 * X ^ 3 - 15 * X ^ 4) : ℚ⟦X⟧) * hG

theorem OMA.solution : type_of% @OMA.S_oeis_a102882.main := by
  intro S G hS hS0 hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 4 := ⟨n - 4, by omega⟩
  have hF := first_order S G hS hS0 hG
  have hF' := congrArg (fun f : ℚ⟦X⟧ => derivative ℚ f) hF
  simp [derivative_numeral, Derivation.leibniz, Derivation.leibniz_pow, smul_eq_mul] at hF'
  have htheta : X * derivative ℚ (X * derivative ℚ G)
      = X * derivative ℚ G + X ^ 2 * derivative ℚ (derivative ℚ G) := by
    simp [Derivation.leibniz, smul_eq_mul]
    ring
  have hK : (1 + 2 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have hc := congrArg (fun f : ℚ⟦X⟧ => constantCoeff f) h
    simp at hc
  have hop : X * derivative ℚ (X * derivative ℚ G) + X * derivative ℚ G
      + X ^ 1 * (C 4 * (X * derivative ℚ (X * derivative ℚ G))
          + C 10 * (X * derivative ℚ G))
      + X ^ 2 * (C 2 * (X * derivative ℚ (X * derivative ℚ G))
          + C 8 * (X * derivative ℚ G) - C 6 * G)
      + X ^ 3 * (-(C 12 * (X * derivative ℚ (X * derivative ℚ G)))
          - C 66 * (X * derivative ℚ G) - C 60 * G)
      + X ^ 4 * (-(C 15 * (X * derivative ℚ (X * derivative ℚ G)))
          - C 105 * (X * derivative ℚ G) - C 90 * G)
      = 0 := by
    rw [htheta]
    simp only [map_ofNat]
    apply mul_left_cancel₀ hK
    linear_combination X ^ 2 * hF' + 2 * X * hF
  have hc := congrArg (coeff (k + 4)) hop
  have e1 : ∀ f : ℚ⟦X⟧, coeff (k + 4) (X ^ 1 * f) = coeff (k + 3) f :=
    fun f => coeff_X_pow_mul f 1 (k + 3)
  have e2 : ∀ f : ℚ⟦X⟧, coeff (k + 4) (X ^ 2 * f) = coeff (k + 2) f :=
    fun f => coeff_X_pow_mul f 2 (k + 2)
  have e3 : ∀ f : ℚ⟦X⟧, coeff (k + 4) (X ^ 3 * f) = coeff (k + 1) f :=
    fun f => coeff_X_pow_mul f 3 (k + 1)
  have e4 : ∀ f : ℚ⟦X⟧, coeff (k + 4) (X ^ 4 * f) = coeff k f :=
    fun f => coeff_X_pow_mul f 4 k
  simp only [map_add, map_sub, map_neg, map_zero, e1, e2, e3, e4, coeff_C_mul,
    coeff_X_derivative] at hc
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 4 - 2 = k + 2 by omega,
    show k + 4 - 3 = k + 1 by omega, show k + 4 - 4 = k by omega]
  push_cast at hc ⊢
  linear_combination hc
