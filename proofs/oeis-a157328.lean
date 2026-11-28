import OMAStatements.S_oeis_a157328

-- Problem: A157328: Expansion of 1/(1-2x*c(4x)) with c(x) g.f. of Catalan numbers (A000108).
-- Upstream: formal-conjectures statements/oeis-a157328.lean:0 (declaration OMA.S_oeis_a157328.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A157328Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 16 * X)
    (hG : G * (3 + (1) * S) = 4 + (0) * S) :
    (-64 + 896 * X + 2048 * X ^ 2) * derivative ℚ G + (-640 + 1024 * X) * G = -768 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have hS2 : S * S = (1 - 16 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (8 + 16 * X) * G = (12 : ℚ⟦X⟧) + (-4) * S := by
    linear_combination (3 - (1) * S) * hG + (1) * ((1) * G - (0)) * hS
  have hPd : derivative ℚ (1 - 16 * X : ℚ⟦X⟧) = -16 := by
    simp [Derivation.leibniz, d16]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -16 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((8 + 16 * X : ℚ⟦X⟧) * G) = (16) * G + (8 + 16 * X) * derivative ℚ G := by
    simp [Derivation.leibniz, d8, d16]
    ring
  have hR : derivative ℚ ((12 : ℚ⟦X⟧) + (-4 : ℚ⟦X⟧) * S) =
      0 + (0) * S + (-4) * derivative ℚ S := by
    simp [Derivation.leibniz, d4, d12]
  have hk2 : (8 + 16 * X : ℚ⟦X⟧) * G = (12 : ℚ⟦X⟧) + (-4 : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (16) * G + (8 + 16 * X) * derivative ℚ G =
      0 + (0) * S + (-4) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  linear_combination (-4) ^ 2 * S * hdS - 2 * (-4) ^ 2 * derivative ℚ S * hS -
      (2 * (0) * (1 - 16 * X) + (-4) * (-16)) * hk + 2 * (-4) * (1 - 16 * X) * hdk

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 16 * X)
    (hG : G * (3 + (1) * S) = 4 + (0) * S) :
    derivative ℚ G * C (-64) + derivative ℚ G * X * C 896 +
      derivative ℚ G * X * X * C 2048 + G * C (-640) +
      G * X * C 1024 =
      C (-768) := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 16 * X)
    (hG : G * (3 + (1) * S) = 4 + (0) * S) (m : ℕ) :
    (-64) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 896 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      2048 * ((m : ℚ) + 1) * coeff (m + 1) G + (-640) * coeff (m + 1 + 1) G +
      1024 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 16 * X)
    (hG : G * (3 + (1) * S) = 4 + (0) * S) :
    (-128) * coeff (0 + 1 + 1) G + 896 * coeff (0 + 1) G +
      (-640) * coeff (0 + 1) G + 1024 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A157328Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a157328.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  cases m with
  | zero =>
    have r := A157328Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination 4 * hG + G * hc)
    push_cast
    linear_combination ((-1 : ℚ) / 64) * r
  | succ m =>
    have r := A157328Aux.rel (S) G (by linear_combination hS)
        (by linear_combination 4 * hG + G * hc) m
    push_cast
    linear_combination ((-1 : ℚ) / 64) * r
