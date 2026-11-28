import OMAStatements.S_oeis_a155051

-- Problem: A155051: Expansion of c(x^2)*(1+x)/(1-x), c(x) the g.f. of A000108.
-- Upstream: formal-conjectures statements/oeis-a155051.lean:0 (declaration OMA.S_oeis_a155051.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A155051Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (2 * X ^ 2 - 2 * X ^ 3 + (0) * S) = 1 + X + (-1 - X) * S) :
    (-4 * X + 20 * X ^ 3 - 16 * X ^ 5) * derivative ℚ G + (-8 + 8 * X + 24 * X ^ 2 - 32 * X ^ 3 - 16 * X ^ 4) * G = -8 - 16 * X - 8 * X ^ 2 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have hS2 : S * S = (1 - 4 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (2 * X ^ 2 - 2 * X ^ 3) * G = (1 + X : ℚ⟦X⟧) + (-1 - X) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 4 * (X * X) : ℚ⟦X⟧) = -8 * X := by
    simp [Derivation.leibniz, d4]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -8 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((2 * (X * X) - 2 * (X * X * X) : ℚ⟦X⟧) * G) = (4 * X - 6 * X ^ 2) * G + (2 * X ^ 2 - 2 * X ^ 3) * derivative ℚ G := by
    simp [Derivation.leibniz, d2]
    ring
  have hR : derivative ℚ ((1 + 1 * X : ℚ⟦X⟧) + (-1 - 1 * X : ℚ⟦X⟧) * S) =
      1 + (-1) * S + (-1 - X) * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hk2 : (2 * (X * X) - 2 * (X * X * X) : ℚ⟦X⟧) * G = (1 + 1 * X : ℚ⟦X⟧) + (-1 - 1 * X : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (4 * X - 6 * X ^ 2) * G + (2 * X ^ 2 - 2 * X ^ 3) * derivative ℚ G =
      1 + (-1) * S + (-1 - X) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 1 * ((-4 * X + 20 * X ^ 3 - 16 * X ^ 5) * derivative ℚ G + (-8 + 8 * X + 24 * X ^ 2 - 32 * X ^ 3 - 16 * X ^ 4) * G - (-8 - 16 * X - 8 * X ^ 2)) = 0 := by
    linear_combination (-1 - X) ^ 2 * S * hdS - 2 * (-1 - X) ^ 2 * derivative ℚ S * hS -
      (2 * (-1) * (1 - 4 * X ^ 2) + (-1 - X) * (-8 * X)) * hk + 2 * (-1 - X) * (1 - 4 * X ^ 2) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 1 ≠ 0 := pow_ne_zero 1 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  linear_combination h1

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (2 * X ^ 2 - 2 * X ^ 3 + (0) * S) = 1 + X + (-1 - X) * S) :
    (-X ^ 2 + X ^ 3 + 4 * X ^ 4 - 4 * X ^ 5) * derivative ℚ (derivative ℚ G) + (2 * X ^ 2 + 4 * X ^ 3 - 12 * X ^ 4) * derivative ℚ G + (6 - 10 * X + 4 * X ^ 2 - 4 * X ^ 3) * G =
      6 + 2 * X := by
  have h := key S G hS hG
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d20 : derivative ℚ (20 : ℚ⟦X⟧) = 0 := dnum 20
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have hL : derivative ℚ ((-4 * X + 20 * (X * X * X) - 16 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-8 + 8 * X + 24 * (X * X) - 32 * (X * X * X) - 16 * (X * X * X * X) : ℚ⟦X⟧) * G) =
      (-4 + 60 * X ^ 2 - 80 * X ^ 4) * derivative ℚ G + (-4 * X + 20 * X ^ 3 - 16 * X ^ 5) * derivative ℚ (derivative ℚ G) + (8 + 48 * X - 96 * X ^ 2 - 64 * X ^ 3) * G + (-8 + 8 * X + 24 * X ^ 2 - 32 * X ^ 3 - 16 * X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d4, d8, d16, d20, d24, d32]
    ring
  have hRd : derivative ℚ (-8 - 16 * X - 8 * (X * X) : ℚ⟦X⟧) = -16 - 16 * X := by
    simp [Derivation.leibniz, d8, d16]
    ring
  have h2 : (-4 * X + 20 * (X * X * X) - 16 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-8 + 8 * X + 24 * (X * X) - 32 * (X * X * X) - 16 * (X * X * X * X) : ℚ⟦X⟧) * G = (-8 - 16 * X - 8 * (X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (-4 + 60 * X ^ 2 - 80 * X ^ 4) * derivative ℚ G + (-4 * X + 20 * X ^ 3 - 16 * X ^ 5) * derivative ℚ (derivative ℚ G) + (8 + 48 * X - 96 * X ^ 2 - 64 * X ^ 3) * G + (-8 + 8 * X + 24 * X ^ 2 - 32 * X ^ 3 - 16 * X ^ 4) * derivative ℚ G = -16 - 16 * X := by
    rw [← hL, h2, hRd]
  have hfull : (4 + 4 * X) * ((-X ^ 2 + X ^ 3 + 4 * X ^ 4 - 4 * X ^ 5) * derivative ℚ (derivative ℚ G) + (2 * X ^ 2 + 4 * X ^ 3 - 12 * X ^ 4) * derivative ℚ G + (6 - 10 * X + 4 * X ^ 2 - 4 * X ^ 3) * G - (6 + 2 * X)) = 0 := by
    linear_combination (X) * hd + (-3) * h
  have hg : (4 + 4 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (4 : ℚ⟦X⟧) = 4 := cnum 4
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (2 * X ^ 2 - 2 * X ^ 3 + (0) * S) = 1 + X + (-1 - X) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C (-1) + derivative ℚ (derivative ℚ G) * X * X * X * C 1 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 4 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-4) +
      derivative ℚ G * X * X * C 2 + derivative ℚ G * X * X * X * C 4 +
      derivative ℚ G * X * X * X * X * C (-12) + G * C 6 +
      G * X * C (-10) + G * X * X * C 4 +
      G * X * X * X * C (-4) =
      C 6 + C 2 * X := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (2 * X ^ 2 - 2 * X ^ 3 + (0) * S) = 1 + X + (-1 - X) * S) (m : ℕ) :
    (-1) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 1 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      4 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + (-4) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      2 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 4 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      (-12) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + 6 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-10) * coeff (m + 1 + 1 + 1 + 1) G + 4 * coeff (m + 1 + 1 + 1) G +
      (-4) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (2 * X ^ 2 - 2 * X ^ 3 + (0) * S) = 1 + X + (-1 - X) * S) :
    (-6) * coeff (0 + 1 + 1 + 1) G + 2 * coeff (0 + 1 + 1) G +
      4 * coeff (0 + 1 + 1) G + 4 * coeff (0 + 1) G +
      6 * coeff (0 + 1 + 1 + 1) G + (-10) * coeff (0 + 1 + 1) G +
      4 * coeff (0 + 1) G + (-4) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (2 * X ^ 2 - 2 * X ^ 3 + (0) * S) = 1 + X + (-1 - X) * S) :
    (-12) * coeff (0 + 1 + 1 + 1 + 1) G + 6 * coeff (0 + 1 + 1 + 1) G +
      8 * coeff (0 + 1 + 1) G + 6 * coeff (0 + 1 + 1 + 1) G +
      8 * coeff (0 + 1 + 1) G + (-12) * coeff (0 + 1) G +
      6 * coeff (0 + 1 + 1 + 1 + 1) G + (-10) * coeff (0 + 1 + 1 + 1) G +
      4 * coeff (0 + 1 + 1) G + (-4) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A155051Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a155051.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  have e3 : m + 1 + 1 + 1 - 3 = m := rfl
  rw [e1, e2, e3]
  cases m with
  | zero =>
    have r := A155051Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A155051Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination hG)
      push_cast
      linear_combination r
    | succ m =>
      have r := A155051Aux.rel (S) G (by linear_combination hS)
          (by linear_combination hG) m
      push_cast
      linear_combination r
