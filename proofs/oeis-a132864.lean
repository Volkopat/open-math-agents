import OMAStatements.S_oeis_a132864

-- Problem: A132864: Expansion of 1/(1-4x*c(5x)), where c(x) is the g.f. of A000108.
-- Upstream: formal-conjectures statements/oeis-a132864.lean:0 (declaration OMA.S_oeis_a132864.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A132864Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 20 * X)
    (hG : G * (3 + (2) * S) = 5 + (0) * S) :
    (-100 + 400 * X + 32000 * X ^ 2) * derivative ℚ G + (-2600 + 16000 * X) * G = -3000 := by
  have d5 : derivative ℚ (5 : ℚ⟦X⟧) = 0 := dnum 5
  have d10 : derivative ℚ (10 : ℚ⟦X⟧) = 0 := dnum 10
  have d15 : derivative ℚ (15 : ℚ⟦X⟧) = 0 := dnum 15
  have d20 : derivative ℚ (20 : ℚ⟦X⟧) = 0 := dnum 20
  have d80 : derivative ℚ (80 : ℚ⟦X⟧) = 0 := dnum 80
  have hS2 : S * S = (1 - 20 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (5 + 80 * X) * G = (15 : ℚ⟦X⟧) + (-10) * S := by
    linear_combination (3 - (2) * S) * hG + (2) * ((2) * G - (0)) * hS
  have hPd : derivative ℚ (1 - 20 * X : ℚ⟦X⟧) = -20 := by
    simp [Derivation.leibniz, d20]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -20 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((5 + 80 * X : ℚ⟦X⟧) * G) = (80) * G + (5 + 80 * X) * derivative ℚ G := by
    simp [Derivation.leibniz, d5, d80]
    ring
  have hR : derivative ℚ ((15 : ℚ⟦X⟧) + (-10 : ℚ⟦X⟧) * S) =
      0 + (0) * S + (-10) * derivative ℚ S := by
    simp [Derivation.leibniz, d10, d15]
  have hk2 : (5 + 80 * X : ℚ⟦X⟧) * G = (15 : ℚ⟦X⟧) + (-10 : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (80) * G + (5 + 80 * X) * derivative ℚ G =
      0 + (0) * S + (-10) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  linear_combination (-10) ^ 2 * S * hdS - 2 * (-10) ^ 2 * derivative ℚ S * hS -
      (2 * (0) * (1 - 20 * X) + (-10) * (-20)) * hk + 2 * (-10) * (1 - 20 * X) * hdk

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 20 * X)
    (hG : G * (3 + (2) * S) = 5 + (0) * S) :
    derivative ℚ G * C (-100) + derivative ℚ G * X * C 400 +
      derivative ℚ G * X * X * C 32000 + G * C (-2600) +
      G * X * C 16000 =
      C (-3000) := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 20 * X)
    (hG : G * (3 + (2) * S) = 5 + (0) * S) (m : ℕ) :
    (-100) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 400 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      32000 * ((m : ℚ) + 1) * coeff (m + 1) G + (-2600) * coeff (m + 1 + 1) G +
      16000 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 20 * X)
    (hG : G * (3 + (2) * S) = 5 + (0) * S) :
    (-200) * coeff (0 + 1 + 1) G + 400 * coeff (0 + 1) G +
      (-2600) * coeff (0 + 1) G + 16000 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A132864Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a132864.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  cases m with
  | zero =>
    have r := A132864Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination 5 * hG + 2 * G * hc)
    push_cast
    linear_combination ((-1 : ℚ) / 100) * r
  | succ m =>
    have r := A132864Aux.rel (S) G (by linear_combination hS)
        (by linear_combination 5 * hG + 2 * G * hc) m
    push_cast
    linear_combination ((-1 : ℚ) / 100) * r
