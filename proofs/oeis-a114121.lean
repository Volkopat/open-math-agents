import OMAStatements.S_oeis_a114121

-- Problem: A114121: Expansion of (sqrt(1 - 4*x) + (1 - 2*x))/(2*(1 - 4*x)).
-- Upstream: formal-conjectures statements/oeis-a114121.lean:0 (declaration OMA.S_oeis_a114121.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A114121Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (2 - 8 * X + (0) * S) = 1 - 2 * X + (1) * S) :
    (4 - 32 * X + 64 * X ^ 2) * derivative ℚ G + (-8 + 32 * X) * G = 8 * X := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (2 - 8 * X) * G = (1 - 2 * X : ℚ⟦X⟧) + (1) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((2 - 8 * X : ℚ⟦X⟧) * G) = (-8) * G + (2 - 8 * X) * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d8]
    ring
  have hR : derivative ℚ ((1 - 2 * X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * S) =
      -2 + (0) * S + (1) * derivative ℚ S := by
    simp [Derivation.leibniz, d2]
  have hk2 : (2 - 8 * X : ℚ⟦X⟧) * G = (1 - 2 * X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-8) * G + (2 - 8 * X) * derivative ℚ G =
      -2 + (0) * S + (1) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  linear_combination (1) ^ 2 * S * hdS - 2 * (1) ^ 2 * derivative ℚ S * hS -
      (2 * (0) * (1 - 4 * X) + (1) * (-4)) * hk + 2 * (1) * (1 - 4 * X) * hdk

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (2 - 8 * X + (0) * S) = 1 - 2 * X + (1) * S) :
    derivative ℚ G * C 4 + derivative ℚ G * X * C (-32) +
      derivative ℚ G * X * X * C 64 + G * C (-8) +
      G * X * C 32 =
      C 8 * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (2 - 8 * X + (0) * S) = 1 - 2 * X + (1) * S) (m : ℕ) :
    4 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-32) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      64 * ((m : ℚ) + 1) * coeff (m + 1) G + (-8) * coeff (m + 1 + 1) G +
      32 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

end A114121Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a114121.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  rw [e1, e2]
  have r := A114121Aux.rel (S) G (by linear_combination hS)
      (by linear_combination hG) m
  push_cast
  linear_combination ((1 : ℚ) / 4) * r
