import OMAStatements.S_oeis_a102879

-- Problem: A102879: A Chebyshev transform of the first kind of the central binomial numbers.
-- Upstream: formal-conjectures statements/oeis-a102879.lean:0 (declaration OMA.S_oeis_a102879.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A102879Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1) * S) = 1 - X ^ 2 + (0) * S) :
    (2 - 8 * X + 2 * X ^ 2 - 2 * X ^ 4 + 8 * X ^ 5 - 2 * X ^ 6) * derivative ℚ G + (-4 + 8 * X - 24 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4) * G = 0 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have hS2 : S * S = (1 - 4 * X + 2 * (X * X) - 4 * (X * X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-1 + 4 * X - 2 * X ^ 2 + 4 * X ^ 3 - X ^ 4) * G = (0 : ℚ⟦X⟧) + (-1 + X ^ 2) * S := by
    linear_combination (0 - (1) * S) * hG + (1) * ((1) * G - (0)) * hS
  have hPd : derivative ℚ (1 - 4 * X + 2 * (X * X) - 4 * (X * X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) = -4 + 4 * X - 12 * X ^ 2 + 4 * X ^ 3 := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 + 4 * X - 12 * X ^ 2 + 4 * X ^ 3 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-1 + 4 * X - 2 * (X * X) + 4 * (X * X * X) - 1 * (X * X * X * X) : ℚ⟦X⟧) * G) = (4 - 4 * X + 12 * X ^ 2 - 4 * X ^ 3) * G + (-1 + 4 * X - 2 * X ^ 2 + 4 * X ^ 3 - X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hR : derivative ℚ ((0 : ℚ⟦X⟧) + (-1 + 1 * (X * X) : ℚ⟦X⟧) * S) =
      0 + (2 * X) * S + (-1 + X ^ 2) * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hk2 : (-1 + 4 * X - 2 * (X * X) + 4 * (X * X * X) - 1 * (X * X * X * X) : ℚ⟦X⟧) * G = (0 : ℚ⟦X⟧) + (-1 + 1 * (X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (4 - 4 * X + 12 * X ^ 2 - 4 * X ^ 3) * G + (-1 + 4 * X - 2 * X ^ 2 + 4 * X ^ 3 - X ^ 4) * derivative ℚ G =
      0 + (2 * X) * S + (-1 + X ^ 2) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4) * ((2 - 8 * X + 2 * X ^ 2 - 2 * X ^ 4 + 8 * X ^ 5 - 2 * X ^ 6) * derivative ℚ G + (-4 + 8 * X - 24 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4) * G - (0)) = 0 := by
    linear_combination (-1 + X ^ 2) ^ 2 * S * hdS - 2 * (-1 + X ^ 2) ^ 2 * derivative ℚ S * hS -
      (2 * (2 * X) * (1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4) + (-1 + X ^ 2) * (-4 + 4 * X - 12 * X ^ 2 + 4 * X ^ 3)) * hk + 2 * (-1 + X ^ 2) * (1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4) * hdk
  have hg : (1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1) * S) = 1 - X ^ 2 + (0) * S) :
    (X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 - 4 * X ^ 5 + X ^ 6) * derivative ℚ (derivative ℚ G) + (-2 * X + 2 * X ^ 2 + 2 * X ^ 3 - 10 * X ^ 4 + 4 * X ^ 5) * derivative ℚ G + (4 * X - 4 * X ^ 2 + 4 * X ^ 3) * G =
      0 := by
  have h := key S G hS hG
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have hL : derivative ℚ ((2 - 8 * X + 2 * (X * X) - 2 * (X * X * X * X) + 8 * (X * X * X * X * X) - 2 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-4 + 8 * X - 24 * (X * X) + 8 * (X * X * X) - 4 * (X * X * X * X) : ℚ⟦X⟧) * G) =
      (-8 + 4 * X - 8 * X ^ 3 + 40 * X ^ 4 - 12 * X ^ 5) * derivative ℚ G + (2 - 8 * X + 2 * X ^ 2 - 2 * X ^ 4 + 8 * X ^ 5 - 2 * X ^ 6) * derivative ℚ (derivative ℚ G) + (8 - 48 * X + 24 * X ^ 2 - 16 * X ^ 3) * G + (-4 + 8 * X - 24 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d4, d8, d24]
    ring
  have hRd : derivative ℚ (0 : ℚ⟦X⟧) = 0 := by
    simp
  have h2 : (2 - 8 * X + 2 * (X * X) - 2 * (X * X * X * X) + 8 * (X * X * X * X * X) - 2 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-4 + 8 * X - 24 * (X * X) + 8 * (X * X * X) - 4 * (X * X * X * X) : ℚ⟦X⟧) * G = (0 : ℚ⟦X⟧) := by linear_combination h
  have hd : (-8 + 4 * X - 8 * X ^ 3 + 40 * X ^ 4 - 12 * X ^ 5) * derivative ℚ G + (2 - 8 * X + 2 * X ^ 2 - 2 * X ^ 4 + 8 * X ^ 5 - 2 * X ^ 6) * derivative ℚ (derivative ℚ G) + (8 - 48 * X + 24 * X ^ 2 - 16 * X ^ 3) * G + (-4 + 8 * X - 24 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4) * derivative ℚ G = 0 := by
    rw [← hL, h2, hRd]
  have hfull : (2 - 2 * X ^ 2) * ((X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4 - 4 * X ^ 5 + X ^ 6) * derivative ℚ (derivative ℚ G) + (-2 * X + 2 * X ^ 2 + 2 * X ^ 3 - 10 * X ^ 4 + 4 * X ^ 5) * derivative ℚ G + (4 * X - 4 * X ^ 2 + 4 * X ^ 3) * G - (0)) = 0 := by
    linear_combination (X ^ 2) * hd + (-2 * X) * h
  have hg : (2 - 2 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1) * S) = 1 - X ^ 2 + (0) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C 1 + derivative ℚ (derivative ℚ G) * X * X * X * C (-4) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 2 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-4) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 1 + derivative ℚ G * X * C (-2) +
      derivative ℚ G * X * X * C 2 + derivative ℚ G * X * X * X * C 2 +
      derivative ℚ G * X * X * X * X * C (-10) + derivative ℚ G * X * X * X * X * X * C 4 +
      G * X * C 4 + G * X * X * C (-4) +
      G * X * X * X * C 4 =
      0 := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1) * S) = 1 - X ^ 2 + (0) * S) (m : ℕ) :
    1 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-4) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      2 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      1 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + (-2) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      2 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 2 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-10) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 4 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      4 * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-4) * coeff (m + 1 + 1 + 1 + 1) G +
      4 * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1) * S) = 1 - X ^ 2 + (0) * S) :
    12 * coeff (0 + 1 + 1 + 1 + 1) G + (-24) * coeff (0 + 1 + 1 + 1) G +
      4 * coeff (0 + 1 + 1) G + (-8) * coeff (0 + 1 + 1 + 1 + 1) G +
      6 * coeff (0 + 1 + 1 + 1) G + 4 * coeff (0 + 1 + 1) G +
      (-10) * coeff (0 + 1) G + 4 * coeff (0 + 1 + 1 + 1) G +
      (-4) * coeff (0 + 1 + 1) G + 4 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X + 2 * X ^ 2 - 4 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1) * S) = 1 - X ^ 2 + (0) * S) :
    20 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-48) * coeff (0 + 1 + 1 + 1 + 1) G +
      12 * coeff (0 + 1 + 1 + 1) G + (-8) * coeff (0 + 1 + 1) G +
      (-10) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 8 * coeff (0 + 1 + 1 + 1 + 1) G +
      6 * coeff (0 + 1 + 1 + 1) G + (-20) * coeff (0 + 1 + 1) G +
      4 * coeff (0 + 1) G + 4 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-4) * coeff (0 + 1 + 1 + 1) G + 4 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A102879Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a102879.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  cases m with
  | zero =>
    have r := A102879Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A102879Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination hG)
      push_cast
      linear_combination r
    | succ m =>
      have r := A102879Aux.rel (S) G (by linear_combination hS)
          (by linear_combination hG) m
      push_cast
      linear_combination r
