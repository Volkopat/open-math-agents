import OMAStatements.S_oeis_a166076

-- Problem: A166076: Expansion of (7+5x-sqrt(1-10x-7x^2))/(2(3+5x+2x^2)).
-- Upstream: formal-conjectures statements/oeis-a166076.lean:0 (declaration OMA.S_oeis_a166076.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A166076Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 10 * X - 7 * X ^ 2)
    (hG : G * (6 + 10 * X + 4 * X ^ 2 + (0) * S) = 7 + 5 * X + (-1) * S) :
    (-12 + 100 * X + 276 * X ^ 2 + 220 * X ^ 3 + 56 * X ^ 4) * derivative ℚ G + (-80 + 120 * X ^ 2 + 56 * X ^ 3) * G = -80 - 48 * X := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d5 : derivative ℚ (5 : ℚ⟦X⟧) = 0 := dnum 5
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d7 : derivative ℚ (7 : ℚ⟦X⟧) = 0 := dnum 7
  have d10 : derivative ℚ (10 : ℚ⟦X⟧) = 0 := dnum 10
  have hS2 : S * S = (1 - 10 * X - 7 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (6 + 10 * X + 4 * X ^ 2) * G = (7 + 5 * X : ℚ⟦X⟧) + (-1) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 10 * X - 7 * (X * X) : ℚ⟦X⟧) = -10 - 14 * X := by
    simp [Derivation.leibniz, d7, d10]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -10 - 14 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((6 + 10 * X + 4 * (X * X) : ℚ⟦X⟧) * G) = (10 + 8 * X) * G + (6 + 10 * X + 4 * X ^ 2) * derivative ℚ G := by
    simp [Derivation.leibniz, d4, d6, d10]
    ring
  have hR : derivative ℚ ((7 + 5 * X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * S) =
      5 + (0) * S + (-1) * derivative ℚ S := by
    simp [Derivation.leibniz, d5, d7]
  have hk2 : (6 + 10 * X + 4 * (X * X) : ℚ⟦X⟧) * G = (7 + 5 * X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (10 + 8 * X) * G + (6 + 10 * X + 4 * X ^ 2) * derivative ℚ G =
      5 + (0) * S + (-1) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  linear_combination (-1) ^ 2 * S * hdS - 2 * (-1) ^ 2 * derivative ℚ S * hS -
      (2 * (0) * (1 - 10 * X - 7 * X ^ 2) + (-1) * (-10 - 14 * X)) * hk + 2 * (-1) * (1 - 10 * X - 7 * X ^ 2) * hdk

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 10 * X - 7 * X ^ 2)
    (hG : G * (6 + 10 * X + 4 * X ^ 2 + (0) * S) = 7 + 5 * X + (-1) * S) :
    derivative ℚ G * C (-12) + derivative ℚ G * X * C 100 +
      derivative ℚ G * X * X * C 276 + derivative ℚ G * X * X * X * C 220 +
      derivative ℚ G * X * X * X * X * C 56 + G * C (-80) +
      G * X * X * C 120 + G * X * X * X * C 56 =
      C (-80) + C (-48) * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 10 * X - 7 * X ^ 2)
    (hG : G * (6 + 10 * X + 4 * X ^ 2 + (0) * S) = 7 + 5 * X + (-1) * S) (m : ℕ) :
    (-12) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 100 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      276 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 220 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      56 * ((m : ℚ) + 1) * coeff (m + 1) G + (-80) * coeff (m + 1 + 1 + 1 + 1) G +
      120 * coeff (m + 1 + 1) G + 56 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 10 * X - 7 * X ^ 2)
    (hG : G * (6 + 10 * X + 4 * X ^ 2 + (0) * S) = 7 + 5 * X + (-1) * S) :
    (-48) * coeff (0 + 1 + 1 + 1 + 1) G + 300 * coeff (0 + 1 + 1 + 1) G +
      552 * coeff (0 + 1 + 1) G + 220 * coeff (0 + 1) G +
      (-80) * coeff (0 + 1 + 1 + 1) G + 120 * coeff (0 + 1) G +
      56 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A166076Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a166076.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  cases m with
  | zero =>
    have r := A166076Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination ((-1 : ℚ) / 4) * r
  | succ m =>
    have r := A166076Aux.rel (S) G (by linear_combination hS)
        (by linear_combination hG) m
    push_cast
    linear_combination ((-1 : ℚ) / 4) * r
