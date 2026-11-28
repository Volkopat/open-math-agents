import OMAStatements.S_oeis_a190160

-- Problem: A190160: Number of peakless Motzkin paths of length n containing no subwords of  type uh^ju or dh^jd (j>=1), where u=(1,1), h=(1,0), and d=(1,-1) (can be easily expressed using RNA secondary structure terminology).
-- Upstream: formal-conjectures statements/oeis-a190160.lean:0 (declaration OMA.S_oeis_a190160.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A190160Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (1 - X : ℚ⟦X⟧) + (-1 + 2 * X - 2 * X ^ 2 + 3 * X ^ 3 - X ^ 4 : ℚ⟦X⟧) * G + (X ^ 2 - 3 * X ^ 3 + 3 * X ^ 4 - X ^ 5 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    (X - 5 * X ^ 2 + 8 * X ^ 3 - 2 * X ^ 4 - 8 * X ^ 5 + 6 * X ^ 6 + 9 * X ^ 7 - 15 * X ^ 8 + 7 * X ^ 9 - X ^ 10) * derivative ℚ G + (2 - 11 * X + 22 * X ^ 2 - 15 * X ^ 3 - 7 * X ^ 4 + 18 * X ^ 5 - 9 * X ^ 6 - 9 * X ^ 7 + 7 * X ^ 8 - X ^ 9) * G =
      2 - 8 * X + 10 * X ^ 2 + 4 * X ^ 3 - 14 * X ^ 4 + 8 * X ^ 5 - 2 * X ^ 6 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have hp0 : (1 - 1 * X : ℚ⟦X⟧) + (-1 + 2 * X - 2 * (X * X) + 3 * (X * X * X) - 1 * (X * X * X * X) : ℚ⟦X⟧) * G + (1 * (X * X) - 3 * (X * X * X) + 3 * (X * X * X * X) - 1 * (X * X * X * X * X) : ℚ⟦X⟧) * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 - 1 * X : ℚ⟦X⟧) + (-1 + 2 * X - 2 * (X * X) + 3 * (X * X * X) - 1 * (X * X * X * X) : ℚ⟦X⟧) * G + (1 * (X * X) - 3 * (X * X * X) + 3 * (X * X * X * X) - 1 * (X * X * X * X * X) : ℚ⟦X⟧) * G * G) =
      (-1 : ℚ⟦X⟧) + (-1 + 2 * X - 2 * X ^ 2 + 3 * X ^ 3 - X ^ 4 : ℚ⟦X⟧) * (derivative ℚ G) + (2 - 4 * X + 9 * X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) * G + (2 * X ^ 2 - 6 * X ^ 3 + 6 * X ^ 4 - 2 * X ^ 5 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X - 9 * X ^ 2 + 12 * X ^ 3 - 5 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have hd1 : (-1 : ℚ⟦X⟧) + (-1 + 2 * X - 2 * X ^ 2 + 3 * X ^ 3 - X ^ 4 : ℚ⟦X⟧) * (derivative ℚ G) + (2 - 4 * X + 9 * X ^ 2 - 4 * X ^ 3 : ℚ⟦X⟧) * G + (2 * X ^ 2 - 6 * X ^ 3 + 6 * X ^ 4 - 2 * X ^ 5 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X - 9 * X ^ 2 + 12 * X ^ 3 - 5 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 = 0 := by rw [← hL1, hp0, map_zero]
  have hfull : ((-1 + 2 * X - 2 * X ^ 2 + 3 * X ^ 3 - X ^ 4 : ℚ⟦X⟧) + (2 * X ^ 2 - 6 * X ^ 3 + 6 * X ^ 4 - 2 * X ^ 5 : ℚ⟦X⟧) * G) ^ 1 * ((X - 5 * X ^ 2 + 8 * X ^ 3 - 2 * X ^ 4 - 8 * X ^ 5 + 6 * X ^ 6 + 9 * X ^ 7 - 15 * X ^ 8 + 7 * X ^ 9 - X ^ 10) * derivative ℚ G + (2 - 11 * X + 22 * X ^ 2 - 15 * X ^ 3 - 7 * X ^ 4 + 18 * X ^ 5 - 9 * X ^ 6 - 9 * X ^ 7 + 7 * X ^ 8 - X ^ 9) * G - (2 - 8 * X + 10 * X ^ 2 + 4 * X ^ 3 - 14 * X ^ 4 + 8 * X ^ 5 - 2 * X ^ 6)) = 0 := by
    linear_combination ((2 - 9 * X + 16 * X ^ 2 - 14 * X ^ 3 + 8 * X ^ 4 + 6 * X ^ 5 - 36 * X ^ 6 + 39 * X ^ 7 - 18 * X ^ 8 + 3 * X ^ 9 : ℚ⟦X⟧)) * hP +
      ((X - 5 * X ^ 2 + 8 * X ^ 3 - 2 * X ^ 4 - 8 * X ^ 5 + 6 * X ^ 6 + 9 * X ^ 7 - 15 * X ^ 8 + 7 * X ^ 9 - X ^ 10 : ℚ⟦X⟧)) * hd1
  have hPG : (-1 + 2 * X - 2 * X ^ 2 + 3 * X ^ 3 - X ^ 4 : ℚ⟦X⟧) + (2 * X ^ 2 - 6 * X ^ 3 + 6 * X ^ 4 - 2 * X ^ 5 : ℚ⟦X⟧) * G ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 1 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (1 - X : ℚ⟦X⟧) + (-1 + 2 * X - 2 * X ^ 2 + 3 * X ^ 3 - X ^ 4 : ℚ⟦X⟧) * G + (X ^ 2 - 3 * X ^ 3 + 3 * X ^ 4 - X ^ 5 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    derivative ℚ G * X * C 1 + derivative ℚ G * X * X * C (-5) +
      derivative ℚ G * X * X * X * C 8 + derivative ℚ G * X * X * X * X * C (-2) +
      derivative ℚ G * X * X * X * X * X * C (-8) + derivative ℚ G * X * X * X * X * X * X * C 6 +
      derivative ℚ G * X * X * X * X * X * X * X * C 9 + derivative ℚ G * X * X * X * X * X * X * X * X * C (-15) +
      derivative ℚ G * X * X * X * X * X * X * X * X * X * C 7 + derivative ℚ G * X * X * X * X * X * X * X * X * X * X * C (-1) +
      G * C 2 + G * X * C (-11) +
      G * X * X * C 22 + G * X * X * X * C (-15) +
      G * X * X * X * X * C (-7) + G * X * X * X * X * X * C 18 +
      G * X * X * X * X * X * X * C (-9) + G * X * X * X * X * X * X * X * C (-9) +
      G * X * X * X * X * X * X * X * X * C 7 + G * X * X * X * X * X * X * X * X * X * C (-1) =
      C 2 + C (-8) * X +
      C 10 * X * X + C 4 * X * X * X +
      C (-14) * X * X * X * X + C 8 * X * X * X * X * X +
      C (-2) * X * X * X * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (1 - X : ℚ⟦X⟧) + (-1 + 2 * X - 2 * X ^ 2 + 3 * X ^ 3 - X ^ 4 : ℚ⟦X⟧) * G + (X ^ 2 - 3 * X ^ 3 + 3 * X ^ 4 - X ^ 5 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) (m : ℕ) :
    1 * ((m : ℚ) + 10) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-5) * ((m : ℚ) + 9) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      8 * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-2) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-8) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 6 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      9 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + (-15) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      7 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + (-1) * ((m : ℚ) + 1) * coeff (m + 1) G +
      2 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-11) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      22 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-15) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 18 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-9) * coeff (m + 1 + 1 + 1 + 1) G + (-9) * coeff (m + 1 + 1 + 1) G +
      7 * coeff (m + 1 + 1) G + (-1) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (1 - X : ℚ⟦X⟧) + (-1 + 2 * X - 2 * X ^ 2 + 3 * X ^ 3 - X ^ 4 : ℚ⟦X⟧) * G + (X ^ 2 - 3 * X ^ 3 + 3 * X ^ 4 - X ^ 5 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    9 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-40) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      56 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-12) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-40) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 24 * coeff (0 + 1 + 1 + 1 + 1) G +
      27 * coeff (0 + 1 + 1 + 1) G + (-30) * coeff (0 + 1 + 1) G +
      7 * coeff (0 + 1) G + 2 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-11) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 22 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-15) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-7) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      18 * coeff (0 + 1 + 1 + 1 + 1) G + (-9) * coeff (0 + 1 + 1 + 1) G +
      (-9) * coeff (0 + 1 + 1) G + 7 * coeff (0 + 1) G +
      (-1) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A190160Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a190160.main := by
  intro G hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 9, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 + 1 + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 + 1 + 1 := rfl
  have e7 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 = m + 1 + 1 := rfl
  have e8 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 8 = m + 1 := rfl
  have e9 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 9 = m := rfl
  rw [e1, e2, e3, e4, e5, e6, e7, e8, e9]
  have hP : (1 - PowerSeries.X : PowerSeries ℚ) + (-1 + 2 * PowerSeries.X - 2 * PowerSeries.X ^ 2 + 3 * PowerSeries.X ^ 3 - PowerSeries.X ^ 4 : PowerSeries ℚ) * G + (PowerSeries.X ^ 2 - 3 * PowerSeries.X ^ 3 + 3 * PowerSeries.X ^ 4 - PowerSeries.X ^ 5 : PowerSeries ℚ) * G ^ 2 = 0 := by
    linear_combination -hG
  have h0c : PowerSeries.constantCoeff G = (1 : ℚ) := by
    have h := congrArg PowerSeries.constantCoeff hG
    simpa using h
  cases m with
  | zero =>
    have r := A190160Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    have r := A190160Aux.rel G hP h0c m
    push_cast
    linear_combination r
