import OMAStatements.S_oeis_a294159

-- Problem: A294159: Alternating row sums of triangle A291844.
-- Upstream: formal-conjectures statements/oeis-a294159.lean:0 (declaration OMA.S_oeis_a294159.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A294159Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (1 - 3 * X - X ^ 2 - X ^ 3 : ℚ⟦X⟧) * G + (-1 + 3 * X + X ^ 2 + X ^ 3 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    (X - 3 * X ^ 2 - 2 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6) * derivative ℚ G + (-2 * X + 2 * X ^ 2 - 4 * X ^ 3) * G =
      -X + X ^ 2 - 2 * X ^ 3 := by
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have hp0 : (1 * X : ℚ⟦X⟧) + (1 - 3 * X - 1 * (X * X) - 1 * (X * X * X) : ℚ⟦X⟧) * G + (-1 + 3 * X + 1 * (X * X) + 1 * (X * X * X) : ℚ⟦X⟧) * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 * X : ℚ⟦X⟧) + (1 - 3 * X - 1 * (X * X) - 1 * (X * X * X) : ℚ⟦X⟧) * G + (-1 + 3 * X + 1 * (X * X) + 1 * (X * X * X) : ℚ⟦X⟧) * G * G) =
      (1 : ℚ⟦X⟧) + (1 - 3 * X - X ^ 2 - X ^ 3 : ℚ⟦X⟧) * (derivative ℚ G) + (-3 - 2 * X - 3 * X ^ 2 : ℚ⟦X⟧) * G + (-2 + 6 * X + 2 * X ^ 2 + 2 * X ^ 3 : ℚ⟦X⟧) * G * (derivative ℚ G) + (3 + 2 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 := by
    simp [Derivation.leibniz, d3]
    ring
  have hd1 : (1 : ℚ⟦X⟧) + (1 - 3 * X - X ^ 2 - X ^ 3 : ℚ⟦X⟧) * (derivative ℚ G) + (-3 - 2 * X - 3 * X ^ 2 : ℚ⟦X⟧) * G + (-2 + 6 * X + 2 * X ^ 2 + 2 * X ^ 3 : ℚ⟦X⟧) * G * (derivative ℚ G) + (3 + 2 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 = 0 := by rw [← hL1, hp0, map_zero]
  have hfull : ((1 - 3 * X - X ^ 2 - X ^ 3 : ℚ⟦X⟧) + (-2 + 6 * X + 2 * X ^ 2 + 2 * X ^ 3 : ℚ⟦X⟧) * G) ^ 1 * ((X - 3 * X ^ 2 - 2 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6) * derivative ℚ G + (-2 * X + 2 * X ^ 2 - 4 * X ^ 3) * G - (-X + X ^ 2 - 2 * X ^ 3)) = 0 := by
    linear_combination ((-X + 6 * X ^ 2 - 8 * X ^ 3 - 2 * X ^ 4 - 3 * X ^ 5 : ℚ⟦X⟧)) * hP +
      ((X - 3 * X ^ 2 - 2 * X ^ 3 + 2 * X ^ 4 + X ^ 5 + X ^ 6 : ℚ⟦X⟧)) * hd1
  have k2 : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
  have hPG : (1 - 3 * X - X ^ 2 - X ^ 3 : ℚ⟦X⟧) + (-2 + 6 * X + 2 * X ^ 2 + 2 * X ^ 3 : ℚ⟦X⟧) * G ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k2] at h'
    norm_num at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 1 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (1 - 3 * X - X ^ 2 - X ^ 3 : ℚ⟦X⟧) * G + (-1 + 3 * X + X ^ 2 + X ^ 3 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    derivative ℚ G * X * C 1 + derivative ℚ G * X * X * C (-3) +
      derivative ℚ G * X * X * X * C (-2) + derivative ℚ G * X * X * X * X * C 2 +
      derivative ℚ G * X * X * X * X * X * C 1 + derivative ℚ G * X * X * X * X * X * X * C 1 +
      G * X * C (-2) + G * X * X * C 2 +
      G * X * X * X * C (-4) =
      C (-1) * X + C 1 * X * X +
      C (-2) * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (1 - 3 * X - X ^ 2 - X ^ 3 : ℚ⟦X⟧) * G + (-1 + 3 * X + X ^ 2 + X ^ 3 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) (m : ℕ) :
    1 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-3) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-2) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 2 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      1 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + 1 * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-2) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 2 * coeff (m + 1 + 1 + 1 + 1) G +
      (-4) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (1 - 3 * X - X ^ 2 - X ^ 3 : ℚ⟦X⟧) * G + (-1 + 3 * X + X ^ 2 + X ^ 3 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    5 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-12) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-6) * coeff (0 + 1 + 1 + 1) G + 4 * coeff (0 + 1 + 1) G +
      1 * coeff (0 + 1) G + (-2) * coeff (0 + 1 + 1 + 1 + 1) G +
      2 * coeff (0 + 1 + 1 + 1) G + (-4) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A294159Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a294159.main := by
  intro G h0 hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 - 5 = m := rfl
  rw [e1, e2, e3, e4, e5]
  have hP : (PowerSeries.X : PowerSeries ℚ) + (1 - 3 * PowerSeries.X - PowerSeries.X ^ 2 - PowerSeries.X ^ 3 : PowerSeries ℚ) * G + (-1 + 3 * PowerSeries.X + PowerSeries.X ^ 2 + PowerSeries.X ^ 3 : PowerSeries ℚ) * G ^ 2 = 0 := by
    linear_combination hG
  have h0c : PowerSeries.constantCoeff G = (1 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A294159Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    have r := A294159Aux.rel G hP h0c m
    push_cast
    linear_combination r
