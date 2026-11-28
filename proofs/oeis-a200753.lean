import OMAStatements.S_oeis_a200753

-- Problem: A200753: G.f. satisfies: A(x) = 1 + (x-x^2)*A(x)^3.
-- Upstream: formal-conjectures statements/oeis-a200753.lean:0 (declaration OMA.S_oeis_a200753.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A200753Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (X - X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    (4 * X ^ 2 - 39 * X ^ 3 + 116 * X ^ 4 - 135 * X ^ 5 + 54 * X ^ 6) * derivative ℚ (derivative ℚ G) + (6 * X - 70 * X ^ 2 + 232 * X ^ 3 - 324 * X ^ 4 + 162 * X ^ 5) * derivative ℚ G + (-6 * X + 36 * X ^ 2 - 72 * X ^ 3 + 48 * X ^ 4) * G =
      0 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have hp0 : (1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (1 * X - 1 * (X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (1 * X - 1 * (X * X) : ℚ⟦X⟧) * G * G * G) =
      (-1 : ℚ⟦X⟧) * (derivative ℚ G) + (3 * X - 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (1 - 2 * X : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz]
    ring
  have hd1 : (-1 : ℚ⟦X⟧) * (derivative ℚ G) + (3 * X - 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (1 - 2 * X : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (-1 : ℚ⟦X⟧) * (derivative ℚ G) + (3 * X - 3 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (1 - 2 * X : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((-1 : ℚ⟦X⟧) * (derivative ℚ G) + (3 * X - 3 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (1 - 2 * X : ℚ⟦X⟧) * G * G * G) =
      (-1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (6 * X - 6 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (3 * X - 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (6 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have hd2 : (-1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (6 * X - 6 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (3 * X - 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (6 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((-1 : ℚ⟦X⟧) + (3 * X - 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2) ^ 3 * ((4 * X ^ 2 - 39 * X ^ 3 + 116 * X ^ 4 - 135 * X ^ 5 + 54 * X ^ 6) * derivative ℚ (derivative ℚ G) + (6 * X - 70 * X ^ 2 + 232 * X ^ 3 - 324 * X ^ 4 + 162 * X ^ 5) * derivative ℚ G + (-6 * X + 36 * X ^ 2 - 72 * X ^ 3 + 48 * X ^ 4) * G - (0)) = 0 := by
    linear_combination ((6 * X - 36 * X ^ 2 + 72 * X ^ 3 - 48 * X ^ 4 : ℚ⟦X⟧) * G + (6 * X - 36 * X ^ 2 + 72 * X ^ 3 - 48 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 + (-6 * X ^ 2 + 42 * X ^ 3 - 108 * X ^ 4 + 120 * X ^ 5 - 48 * X ^ 6 : ℚ⟦X⟧) * G ^ 4) * hP +
      ((6 * X - 70 * X ^ 2 + 232 * X ^ 3 - 324 * X ^ 4 + 162 * X ^ 5 : ℚ⟦X⟧) + (24 * X ^ 3 - 258 * X ^ 4 + 930 * X ^ 5 - 1506 * X ^ 6 + 1134 * X ^ 7 - 324 * X ^ 8 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-12 * X ^ 2 + 174 * X ^ 3 - 648 * X ^ 4 + 1134 * X ^ 5 - 972 * X ^ 6 + 324 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 + (-72 * X ^ 4 + 846 * X ^ 5 - 3564 * X ^ 6 + 7308 * X ^ 7 - 7920 * X ^ 8 + 4374 * X ^ 9 - 972 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (6 * X ^ 3 - 126 * X ^ 4 + 510 * X ^ 5 - 990 * X ^ 6 + 1086 * X ^ 7 - 648 * X ^ 8 + 162 * X ^ 9 : ℚ⟦X⟧) * G ^ 4) * hd1 +
      ((4 * X ^ 2 - 39 * X ^ 3 + 116 * X ^ 4 - 135 * X ^ 5 + 54 * X ^ 6 : ℚ⟦X⟧) + (-24 * X ^ 3 + 258 * X ^ 4 - 930 * X ^ 5 + 1506 * X ^ 6 - 1134 * X ^ 7 + 324 * X ^ 8 : ℚ⟦X⟧) * G ^ 2 + (36 * X ^ 4 - 423 * X ^ 5 + 1782 * X ^ 6 - 3654 * X ^ 7 + 3960 * X ^ 8 - 2187 * X ^ 9 + 486 * X ^ 10 : ℚ⟦X⟧) * G ^ 4) * hd2
  have hPG : (-1 : ℚ⟦X⟧) + (3 * X - 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (X - X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C 4 + derivative ℚ (derivative ℚ G) * X * X * X * C (-39) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 116 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-135) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 54 + derivative ℚ G * X * C 6 +
      derivative ℚ G * X * X * C (-70) + derivative ℚ G * X * X * X * C 232 +
      derivative ℚ G * X * X * X * X * C (-324) + derivative ℚ G * X * X * X * X * X * C 162 +
      G * X * C (-6) + G * X * X * C 36 +
      G * X * X * X * C (-72) + G * X * X * X * X * C 48 =
      0 := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (X - X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) (m : ℕ) :
    4 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-39) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      116 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-135) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      54 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + 6 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-70) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 232 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-324) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 162 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-6) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 36 * coeff (m + 1 + 1 + 1 + 1) G +
      (-72) * coeff (m + 1 + 1 + 1) G + 48 * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (X - X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    48 * coeff (0 + 1 + 1 + 1 + 1) G + (-234) * coeff (0 + 1 + 1 + 1) G +
      232 * coeff (0 + 1 + 1) G + 24 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-210) * coeff (0 + 1 + 1 + 1) G + 464 * coeff (0 + 1 + 1) G +
      (-324) * coeff (0 + 1) G + (-6) * coeff (0 + 1 + 1 + 1) G +
      36 * coeff (0 + 1 + 1) G + (-72) * coeff (0 + 1) G +
      48 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (X - X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    80 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-468) * coeff (0 + 1 + 1 + 1 + 1) G +
      696 * coeff (0 + 1 + 1 + 1) G + (-270) * coeff (0 + 1 + 1) G +
      30 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-280) * coeff (0 + 1 + 1 + 1 + 1) G +
      696 * coeff (0 + 1 + 1 + 1) G + (-648) * coeff (0 + 1 + 1) G +
      162 * coeff (0 + 1) G + (-6) * coeff (0 + 1 + 1 + 1 + 1) G +
      36 * coeff (0 + 1 + 1 + 1) G + (-72) * coeff (0 + 1 + 1) G +
      48 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A200753Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a200753.main := by
  intro G hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  have hP : (1 : PowerSeries ℚ) + (-1 : PowerSeries ℚ) * G + (PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 3 = 0 := by
    linear_combination -hG
  have h0c : PowerSeries.constantCoeff G = (1 : ℚ) := by
    have h := congrArg PowerSeries.constantCoeff hG
    simpa using h
  cases m with
  | zero =>
    have r := A200753Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A200753Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A200753Aux.rel G hP h0c m
      push_cast
      linear_combination r
