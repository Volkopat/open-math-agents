import OMAStatements.S_oeis_a127275

-- Problem: A127275: Expansion of (sqrt(1-4x)-x)/(1-4x).
-- Upstream: formal-conjectures statements/oeis-a127275.lean:0 (declaration OMA.S_oeis_a127275.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A127275Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (1 - 4 * X + (0) * S) = -X + (1) * S) :
    (2 - 16 * X + 32 * X ^ 2) * derivative ℚ G + (-4 + 16 * X) * G = -2 + 4 * X := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (1 - 4 * X) * G = (-X : ℚ⟦X⟧) + (1) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((1 - 4 * X : ℚ⟦X⟧) * G) = (-4) * G + (1 - 4 * X) * derivative ℚ G := by
    simp [Derivation.leibniz, d4]
    ring
  have hR : derivative ℚ ((-1 * X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * S) =
      -1 + (0) * S + (1) * derivative ℚ S := by
    simp
  have hk2 : (1 - 4 * X : ℚ⟦X⟧) * G = (-1 * X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-4) * G + (1 - 4 * X) * derivative ℚ G =
      -1 + (0) * S + (1) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  linear_combination (1) ^ 2 * S * hdS - 2 * (1) ^ 2 * derivative ℚ S * hS -
      (2 * (0) * (1 - 4 * X) + (1) * (-4)) * hk + 2 * (1) * (1 - 4 * X) * hdk

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (1 - 4 * X + (0) * S) = -X + (1) * S) :
    derivative ℚ G * C 2 + derivative ℚ G * X * C (-16) +
      derivative ℚ G * X * X * C 32 + G * C (-4) +
      G * X * C 16 =
      C (-2) + C 4 * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (1 - 4 * X + (0) * S) = -X + (1) * S) (m : ℕ) :
    2 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-16) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      32 * ((m : ℚ) + 1) * coeff (m + 1) G + (-4) * coeff (m + 1 + 1) G +
      16 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

end A127275Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a127275.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  rw [e1, e2]
  have r := A127275Aux.rel (S) G (by linear_combination hS)
      (by linear_combination hG) m
  push_cast
  linear_combination ((1 : ℚ) / 2) * r
