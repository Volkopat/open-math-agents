import OMAStatements.S_oeis_a128057

-- Problem: A128057: Expansion of (1+x)/sqrt(1+4x^2).
-- Upstream: formal-conjectures statements/oeis-a128057.lean:0 (declaration OMA.S_oeis_a128057.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A128057Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 + 4 * X ^ 2)
    (hG : G * (0 + (1) * S) = 1 + X + (0) * S) :
    (2 + 2 * X + 8 * X ^ 2 + 8 * X ^ 3) * derivative ℚ G + (-2 + 8 * X) * G = 0 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have hS2 : S * S = (1 + 4 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-1 - 4 * X ^ 2) * G = (0 : ℚ⟦X⟧) + (-1 - X) * S := by
    linear_combination (0 - (1) * S) * hG + (1) * ((1) * G - (0)) * hS
  have hPd : derivative ℚ (1 + 4 * (X * X) : ℚ⟦X⟧) = 8 * X := by
    simp [Derivation.leibniz, d4]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = 8 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-1 - 4 * (X * X) : ℚ⟦X⟧) * G) = (-8 * X) * G + (-1 - 4 * X ^ 2) * derivative ℚ G := by
    simp [Derivation.leibniz, d4]
    ring
  have hR : derivative ℚ ((0 : ℚ⟦X⟧) + (-1 - 1 * X : ℚ⟦X⟧) * S) =
      0 + (-1) * S + (-1 - X) * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hk2 : (-1 - 4 * (X * X) : ℚ⟦X⟧) * G = (0 : ℚ⟦X⟧) + (-1 - 1 * X : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-8 * X) * G + (-1 - 4 * X ^ 2) * derivative ℚ G =
      0 + (-1) * S + (-1 - X) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 + 4 * X ^ 2) * ((2 + 2 * X + 8 * X ^ 2 + 8 * X ^ 3) * derivative ℚ G + (-2 + 8 * X) * G - (0)) = 0 := by
    linear_combination (-1 - X) ^ 2 * S * hdS - 2 * (-1 - X) ^ 2 * derivative ℚ S * hS -
      (2 * (-1) * (1 + 4 * X ^ 2) + (-1 - X) * (8 * X)) * hk + 2 * (-1 - X) * (1 + 4 * X ^ 2) * hdk
  have hg : (1 + 4 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 + 4 * X ^ 2)
    (hG : G * (0 + (1) * S) = 1 + X + (0) * S) :
    (5 * X ^ 2 + 20 * X ^ 4) * derivative ℚ (derivative ℚ G) + (-4 * X + 44 * X ^ 3) * derivative ℚ G + (4 * X) * G =
      0 := by
  have h := key S G hS hG
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have hL : derivative ℚ ((2 + 2 * X + 8 * (X * X) + 8 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-2 + 8 * X : ℚ⟦X⟧) * G) =
      (2 + 16 * X + 24 * X ^ 2) * derivative ℚ G + (2 + 2 * X + 8 * X ^ 2 + 8 * X ^ 3) * derivative ℚ (derivative ℚ G) + (8) * G + (-2 + 8 * X) * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d8]
    ring
  have hRd : derivative ℚ (0 : ℚ⟦X⟧) = 0 := by
    simp
  have h2 : (2 + 2 * X + 8 * (X * X) + 8 * (X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-2 + 8 * X : ℚ⟦X⟧) * G = (0 : ℚ⟦X⟧) := by linear_combination h
  have hd : (2 + 16 * X + 24 * X ^ 2) * derivative ℚ G + (2 + 2 * X + 8 * X ^ 2 + 8 * X ^ 3) * derivative ℚ (derivative ℚ G) + (8) * G + (-2 + 8 * X) * derivative ℚ G = 0 := by
    rw [← hL, h2, hRd]
  have hfull : (2 + 2 * X) * ((5 * X ^ 2 + 20 * X ^ 4) * derivative ℚ (derivative ℚ G) + (-4 * X + 44 * X ^ 3) * derivative ℚ G + (4 * X) * G - (0)) = 0 := by
    linear_combination (5 * X ^ 2) * hd + (-4 * X) * h
  have hg : (2 + 2 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 + 4 * X ^ 2)
    (hG : G * (0 + (1) * S) = 1 + X + (0) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C 5 + derivative ℚ (derivative ℚ G) * X * X * X * X * C 20 +
      derivative ℚ G * X * C (-4) + derivative ℚ G * X * X * X * C 44 +
      G * X * C 4 =
      0 := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 + 4 * X ^ 2)
    (hG : G * (0 + (1) * S) = 1 + X + (0) * S) (m : ℕ) :
    5 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + 20 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      (-4) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 44 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      4 * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 + 4 * X ^ 2)
    (hG : G * (0 + (1) * S) = 1 + X + (0) * S) :
    10 * coeff (0 + 1 + 1) G + (-8) * coeff (0 + 1 + 1) G +
      4 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 + 4 * X ^ 2)
    (hG : G * (0 + (1) * S) = 1 + X + (0) * S) :
    30 * coeff (0 + 1 + 1 + 1) G + (-12) * coeff (0 + 1 + 1 + 1) G +
      44 * coeff (0 + 1) G + 4 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A128057Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a128057.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  cases m with
  | zero =>
    have r := A128057Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A128057Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination hG)
      push_cast
      linear_combination r
    | succ m =>
      have r := A128057Aux.rel (S) G (by linear_combination hS)
          (by linear_combination hG) m
      push_cast
      linear_combination r
