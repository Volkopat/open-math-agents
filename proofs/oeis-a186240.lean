import OMAStatements.S_oeis_a186240

-- Problem: A186240: G.f. A(x) defined by A(x) = 1 +x*A(x) +x^2*A(x)^2 +3*x^3*A(x)^3.
-- Upstream: formal-conjectures statements/oeis-a186240.lean:0 (declaration OMA.S_oeis_a186240.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A186240Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 + X : ℚ⟦X⟧) * G + (X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (3 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    (12 * X ^ 2 + 277 * X ^ 3 - 930 * X ^ 4 - 724 * X ^ 5 - 5304 * X ^ 6) * derivative ℚ (derivative ℚ G) + (42 * X + 640 * X ^ 2 - 2820 * X ^ 3 - 2840 * X ^ 4 - 21216 * X ^ 5) * derivative ℚ G + (18 - 76 * X - 816 * X ^ 2 - 1392 * X ^ 3 - 10608 * X ^ 4) * G =
      18 - 16 * X := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d9 : derivative ℚ (9 : ℚ⟦X⟧) = 0 := dnum 9
  have hp0 : (1 : ℚ⟦X⟧) + (-1 + 1 * X : ℚ⟦X⟧) * G + (1 * (X * X) : ℚ⟦X⟧) * G * G + (3 * (X * X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 : ℚ⟦X⟧) + (-1 + 1 * X : ℚ⟦X⟧) * G + (1 * (X * X) : ℚ⟦X⟧) * G * G + (3 * (X * X * X) : ℚ⟦X⟧) * G * G * G) =
      (-1 + X : ℚ⟦X⟧) * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G + (2 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G ^ 2 + (9 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (9 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d3]
    ring
  have hd1 : (-1 + X : ℚ⟦X⟧) * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G + (2 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G ^ 2 + (9 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (9 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (-1 + 1 * X : ℚ⟦X⟧) * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G + (2 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G * G + (9 * (X * X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (9 * (X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((-1 + 1 * X : ℚ⟦X⟧) * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G + (2 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G * G + (9 * (X * X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (9 * (X * X) : ℚ⟦X⟧) * G * G * G) =
      (-1 + X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (2 : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (18 * X ^ 3 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (2 : ℚ⟦X⟧) * G ^ 2 + (9 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (54 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (18 * X : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d2, d9]
    ring
  have hd2 : (-1 + X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (2 : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (18 * X ^ 3 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (2 : ℚ⟦X⟧) * G ^ 2 + (9 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (54 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (18 * X : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((-1 + X : ℚ⟦X⟧) + (2 * X ^ 2 : ℚ⟦X⟧) * G + (9 * X ^ 3 : ℚ⟦X⟧) * G ^ 2) ^ 3 * ((12 * X ^ 2 + 277 * X ^ 3 - 930 * X ^ 4 - 724 * X ^ 5 - 5304 * X ^ 6) * derivative ℚ (derivative ℚ G) + (42 * X + 640 * X ^ 2 - 2820 * X ^ 3 - 2840 * X ^ 4 - 21216 * X ^ 5) * derivative ℚ G + (18 - 76 * X - 816 * X ^ 2 - 1392 * X ^ 3 - 10608 * X ^ 4) * G - (18 - 16 * X)) = 0 := by
    linear_combination ((18 - 70 * X + 102 * X ^ 2 - 66 * X ^ 3 + 16 * X ^ 4 : ℚ⟦X⟧) + (18 * X ^ 2 + 2862 * X ^ 3 + 7560 * X ^ 4 - 10440 * X ^ 5 : ℚ⟦X⟧) * G + (162 * X ^ 3 + 12636 * X ^ 4 - 27216 * X ^ 5 + 1080 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (-17496 * X ^ 6 + 15552 * X ^ 7 : ℚ⟦X⟧) * G ^ 3 + (-39366 * X ^ 7 + 34992 * X ^ 8 : ℚ⟦X⟧) * G ^ 4) * hP +
      ((42 * X + 580 * X ^ 2 - 3528 * X ^ 3 + 1026 * X ^ 4 - 17944 * X ^ 5 + 30432 * X ^ 6 - 10608 * X ^ 7 : ℚ⟦X⟧) + (24 * X ^ 4 + 530 * X ^ 5 - 2414 * X ^ 6 + 412 * X ^ 7 - 9160 * X ^ 8 + 10608 * X ^ 9 : ℚ⟦X⟧) * (derivative ℚ G) + (-72 * X ^ 3 - 296 * X ^ 4 + 3630 * X ^ 5 + 3588 * X ^ 6 + 38312 * X ^ 7 - 31824 * X ^ 8 : ℚ⟦X⟧) * G + (216 * X ^ 5 + 4722 * X ^ 6 - 22834 * X ^ 7 + 7428 * X ^ 8 - 79544 * X ^ 9 + 116688 * X ^ 10 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-108 * X ^ 4 + 3570 * X ^ 5 - 3662 * X ^ 6 + 11364 * X ^ 7 + 80776 * X ^ 8 - 116688 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 + (-648 * X ^ 7 - 14958 * X ^ 8 + 50220 * X ^ 9 + 39096 * X ^ 10 + 286416 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-11862 * X ^ 7 + 15660 * X ^ 8 - 11016 * X ^ 9 - 95472 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 + (-1944 * X ^ 8 - 44874 * X ^ 9 + 150660 * X ^ 10 + 117288 * X ^ 11 + 859248 * X ^ 12 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-486 * X ^ 7 - 37908 * X ^ 8 + 72900 * X ^ 9 + 4536 * X ^ 10 : ℚ⟦X⟧) * G ^ 4) * hd1 +
      ((12 * X ^ 2 + 253 * X ^ 3 - 1472 * X ^ 4 + 1413 * X ^ 5 - 4786 * X ^ 6 + 9884 * X ^ 7 - 5304 * X ^ 8 : ℚ⟦X⟧) + (-48 * X ^ 4 - 1060 * X ^ 5 + 4828 * X ^ 6 - 824 * X ^ 7 + 18320 * X ^ 8 - 21216 * X ^ 9 : ℚ⟦X⟧) * G + (-216 * X ^ 5 - 4722 * X ^ 6 + 22834 * X ^ 7 - 7428 * X ^ 8 + 79544 * X ^ 9 - 116688 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 + (432 * X ^ 7 + 9972 * X ^ 8 - 33480 * X ^ 9 - 26064 * X ^ 10 - 190944 * X ^ 11 : ℚ⟦X⟧) * G ^ 3 + (972 * X ^ 8 + 22437 * X ^ 9 - 75330 * X ^ 10 - 58644 * X ^ 11 - 429624 * X ^ 12 : ℚ⟦X⟧) * G ^ 4) * hd2
  have hPG : (-1 + X : ℚ⟦X⟧) + (2 * X ^ 2 : ℚ⟦X⟧) * G + (9 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 + X : ℚ⟦X⟧) * G + (X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (3 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C 12 + derivative ℚ (derivative ℚ G) * X * X * X * C 277 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-930) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-724) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-5304) + derivative ℚ G * X * C 42 +
      derivative ℚ G * X * X * C 640 + derivative ℚ G * X * X * X * C (-2820) +
      derivative ℚ G * X * X * X * X * C (-2840) + derivative ℚ G * X * X * X * X * X * C (-21216) +
      G * C 18 + G * X * C (-76) +
      G * X * X * C (-816) + G * X * X * X * C (-1392) +
      G * X * X * X * X * C (-10608) =
      C 18 + C (-16) * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 + X : ℚ⟦X⟧) * G + (X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (3 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) (m : ℕ) :
    12 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 277 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-930) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-724) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-5304) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + 42 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      640 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-2820) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-2840) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-21216) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      18 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-76) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-816) * coeff (m + 1 + 1 + 1 + 1) G + (-1392) * coeff (m + 1 + 1 + 1) G +
      (-10608) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 + X : ℚ⟦X⟧) * G + (X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (3 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    144 * coeff (0 + 1 + 1 + 1 + 1) G + 1662 * coeff (0 + 1 + 1 + 1) G +
      (-1860) * coeff (0 + 1 + 1) G + 168 * coeff (0 + 1 + 1 + 1 + 1) G +
      1920 * coeff (0 + 1 + 1 + 1) G + (-5640) * coeff (0 + 1 + 1) G +
      (-2840) * coeff (0 + 1) G + 18 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-76) * coeff (0 + 1 + 1 + 1) G + (-816) * coeff (0 + 1 + 1) G +
      (-1392) * coeff (0 + 1) G + (-10608) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (-1 + X : ℚ⟦X⟧) * G + (X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (3 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    240 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 3324 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-5580) * coeff (0 + 1 + 1 + 1) G + (-1448) * coeff (0 + 1 + 1) G +
      210 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 2560 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-8460) * coeff (0 + 1 + 1 + 1) G + (-5680) * coeff (0 + 1 + 1) G +
      (-21216) * coeff (0 + 1) G + 18 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-76) * coeff (0 + 1 + 1 + 1 + 1) G + (-816) * coeff (0 + 1 + 1 + 1) G +
      (-1392) * coeff (0 + 1 + 1) G + (-10608) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A186240Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a186240.main := by
  intro G hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  have hP : (1 : PowerSeries ℚ) + (-1 + PowerSeries.X : PowerSeries ℚ) * G + (PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (3 * PowerSeries.X ^ 3 : PowerSeries ℚ) * G ^ 3 = 0 := by
    linear_combination -hG
  have h0c : PowerSeries.constantCoeff G = (1 : ℚ) := by
    have h := congrArg PowerSeries.constantCoeff hG
    simpa using h
  cases m with
  | zero =>
    have r := A186240Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A186240Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A186240Aux.rel G hP h0c m
      push_cast
      linear_combination r
