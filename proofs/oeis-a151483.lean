import OMAStatements.S_oeis_a151483

-- Problem: A151483: Number of walks within N^2 (the first quadrant of Z^2) starting at (0,0), ending on the vertical axis and consisting of n steps taken from {(-1, 0), (-1, 1), (0, -1), (0, 1), (1, -1), (1, 0)}.
-- Upstream: formal-conjectures statements/oeis-a151483.lean:0 (declaration OMA.S_oeis_a151483.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A151483Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 12 * X ^ 2)
    (hG : G * (32 * X ^ 3 + (0) * S) = -1 + 8 * X - 4 * X ^ 2 + (1 - 6 * X) * S) :
    (64 * X - 256 * X ^ 2 - 768 * X ^ 3) * derivative ℚ G + (192 - 256 * X - 768 * X ^ 2) * G = 192 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have hS2 : S * S = (1 - 4 * X - 12 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (32 * X ^ 3) * G = (-1 + 8 * X - 4 * X ^ 2 : ℚ⟦X⟧) + (1 - 6 * X) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 4 * X - 12 * (X * X) : ℚ⟦X⟧) = -4 - 24 * X := by
    simp [Derivation.leibniz, d4, d12]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 - 24 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((32 * (X * X * X) : ℚ⟦X⟧) * G) = (96 * X ^ 2) * G + (32 * X ^ 3) * derivative ℚ G := by
    simp [Derivation.leibniz, d32]
    ring
  have hR : derivative ℚ ((-1 + 8 * X - 4 * (X * X) : ℚ⟦X⟧) + (1 - 6 * X : ℚ⟦X⟧) * S) =
      8 - 8 * X + (-6) * S + (1 - 6 * X) * derivative ℚ S := by
    simp [Derivation.leibniz, d4, d6, d8]
    ring
  have hk2 : (32 * (X * X * X) : ℚ⟦X⟧) * G = (-1 + 8 * X - 4 * (X * X) : ℚ⟦X⟧) + (1 - 6 * X : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (96 * X ^ 2) * G + (32 * X ^ 3) * derivative ℚ G =
      8 - 8 * X + (-6) * S + (1 - 6 * X) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 2 * ((1 - 6 * X) * ((64 * X - 256 * X ^ 2 - 768 * X ^ 3) * derivative ℚ G + (192 - 256 * X - 768 * X ^ 2) * G - (192))) = 0 := by
    linear_combination (1 - 6 * X) ^ 2 * S * hdS - 2 * (1 - 6 * X) ^ 2 * derivative ℚ S * hS -
      (2 * (-6) * (1 - 4 * X - 12 * X ^ 2) + (1 - 6 * X) * (-4 - 24 * X)) * hk + 2 * (1 - 6 * X) * (1 - 4 * X - 12 * X ^ 2) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero 2 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 6 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 12 * X ^ 2)
    (hG : G * (32 * X ^ 3 + (0) * S) = -1 + 8 * X - 4 * X ^ 2 + (1 - 6 * X) * S) :
    derivative ℚ G * X * C 64 + derivative ℚ G * X * X * C (-256) +
      derivative ℚ G * X * X * X * C (-768) + G * C 192 +
      G * X * C (-256) + G * X * X * C (-768) =
      C 192 := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 12 * X ^ 2)
    (hG : G * (32 * X ^ 3 + (0) * S) = -1 + 8 * X - 4 * X ^ 2 + (1 - 6 * X) * S) (m : ℕ) :
    64 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-256) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-768) * ((m : ℚ) + 1) * coeff (m + 1) G + 192 * coeff (m + 1 + 1 + 1) G +
      (-256) * coeff (m + 1 + 1) G + (-768) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X - 12 * X ^ 2)
    (hG : G * (32 * X ^ 3 + (0) * S) = -1 + 8 * X - 4 * X ^ 2 + (1 - 6 * X) * S) :
    128 * coeff (0 + 1 + 1) G + (-256) * coeff (0 + 1) G +
      192 * coeff (0 + 1 + 1) G + (-256) * coeff (0 + 1) G +
      (-768) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A151483Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a151483.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  cases m with
  | zero =>
    have r := A151483Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination ((1 : ℚ) / 64) * r
  | succ m =>
    have r := A151483Aux.rel (S) G (by linear_combination hS)
        (by linear_combination hG) m
    push_cast
    linear_combination ((1 : ℚ) / 64) * r
