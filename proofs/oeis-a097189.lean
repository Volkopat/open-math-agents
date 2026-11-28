import OMAStatements.S_oeis_a097189

-- Problem: A097189: Row sums of triangle A097186, in which the n-th row polynomial R_n(y) is formed from the initial (n+1) terms of g.f. A057083(y)^(n+1), where R_n(1/3) = 3^n for all n >= 0.
-- Upstream: formal-conjectures statements/oeis-a097189.lean:0 (declaration OMA.S_oeis_a097189.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A097189Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (3 : ℚ⟦X⟧) + (-3 + 27 * X : ℚ⟦X⟧) * G + (1 - 18 * X + 81 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (-1 + 19 * X - 99 * X ^ 2 + 81 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    (X ^ 2 - 19 * X ^ 3 + 99 * X ^ 4 - 81 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-20 * X ^ 2 + 216 * X ^ 3 - 324 * X ^ 4) * derivative ℚ G + (36 * X ^ 2 - 180 * X ^ 3) * G =
      6 * X ^ 2 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d18 : derivative ℚ (18 : ℚ⟦X⟧) = 0 := dnum 18
  have d19 : derivative ℚ (19 : ℚ⟦X⟧) = 0 := dnum 19
  have d27 : derivative ℚ (27 : ℚ⟦X⟧) = 0 := dnum 27
  have d36 : derivative ℚ (36 : ℚ⟦X⟧) = 0 := dnum 36
  have d57 : derivative ℚ (57 : ℚ⟦X⟧) = 0 := dnum 57
  have d81 : derivative ℚ (81 : ℚ⟦X⟧) = 0 := dnum 81
  have d99 : derivative ℚ (99 : ℚ⟦X⟧) = 0 := dnum 99
  have d162 : derivative ℚ (162 : ℚ⟦X⟧) = 0 := dnum 162
  have d198 : derivative ℚ (198 : ℚ⟦X⟧) = 0 := dnum 198
  have d243 : derivative ℚ (243 : ℚ⟦X⟧) = 0 := dnum 243
  have d297 : derivative ℚ (297 : ℚ⟦X⟧) = 0 := dnum 297
  have hp0 : (3 : ℚ⟦X⟧) + (-3 + 27 * X : ℚ⟦X⟧) * G + (1 - 18 * X + 81 * (X * X) : ℚ⟦X⟧) * G * G + (-1 + 19 * X - 99 * (X * X) + 81 * (X * X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((3 : ℚ⟦X⟧) + (-3 + 27 * X : ℚ⟦X⟧) * G + (1 - 18 * X + 81 * (X * X) : ℚ⟦X⟧) * G * G + (-1 + 19 * X - 99 * (X * X) + 81 * (X * X * X) : ℚ⟦X⟧) * G * G * G) =
      (-3 + 27 * X : ℚ⟦X⟧) * (derivative ℚ G) + (27 : ℚ⟦X⟧) * G + (2 - 36 * X + 162 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-18 + 162 * X : ℚ⟦X⟧) * G ^ 2 + (-3 + 57 * X - 297 * X ^ 2 + 243 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (19 - 198 * X + 243 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d3, d18, d19, d27, d81, d99]
    ring
  have hd1 : (-3 + 27 * X : ℚ⟦X⟧) * (derivative ℚ G) + (27 : ℚ⟦X⟧) * G + (2 - 36 * X + 162 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-18 + 162 * X : ℚ⟦X⟧) * G ^ 2 + (-3 + 57 * X - 297 * X ^ 2 + 243 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (19 - 198 * X + 243 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (-3 + 27 * X : ℚ⟦X⟧) * (derivative ℚ G) + (27 : ℚ⟦X⟧) * G + (2 - 36 * X + 162 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (-18 + 162 * X : ℚ⟦X⟧) * G * G + (-3 + 57 * X - 297 * (X * X) + 243 * (X * X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (19 - 198 * X + 243 * (X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((-3 + 27 * X : ℚ⟦X⟧) * (derivative ℚ G) + (27 : ℚ⟦X⟧) * G + (2 - 36 * X + 162 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (-18 + 162 * X : ℚ⟦X⟧) * G * G + (-3 + 57 * X - 297 * (X * X) + 243 * (X * X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (19 - 198 * X + 243 * (X * X) : ℚ⟦X⟧) * G * G * G) =
      (-3 + 27 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (54 : ℚ⟦X⟧) * (derivative ℚ G) + (2 - 36 * X + 162 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 - 36 * X + 162 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-72 + 648 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 + 114 * X - 594 * X ^ 2 + 486 * X ^ 3 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (162 : ℚ⟦X⟧) * G ^ 2 + (-3 + 57 * X - 297 * X ^ 2 + 243 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (114 - 1188 * X + 1458 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-198 + 486 * X : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d2, d3, d18, d19, d27, d36, d57, d162, d198, d243, d297]
    ring
  have hd2 : (-3 + 27 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (54 : ℚ⟦X⟧) * (derivative ℚ G) + (2 - 36 * X + 162 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 - 36 * X + 162 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-72 + 648 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 + 114 * X - 594 * X ^ 2 + 486 * X ^ 3 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (162 : ℚ⟦X⟧) * G ^ 2 + (-3 + 57 * X - 297 * X ^ 2 + 243 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (114 - 1188 * X + 1458 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-198 + 486 * X : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((-3 + 27 * X : ℚ⟦X⟧) + (2 - 36 * X + 162 * X ^ 2 : ℚ⟦X⟧) * G + (-3 + 57 * X - 297 * X ^ 2 + 243 * X ^ 3 : ℚ⟦X⟧) * G ^ 2) ^ 3 * ((X ^ 2 - 19 * X ^ 3 + 99 * X ^ 4 - 81 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-20 * X ^ 2 + 216 * X ^ 3 - 324 * X ^ 4) * derivative ℚ G + (36 * X ^ 2 - 180 * X ^ 3) * G - (6 * X ^ 2)) = 0 := by
    linear_combination ((54 * X ^ 2 - 1458 * X ^ 3 + 13122 * X ^ 4 - 39366 * X ^ 5 : ℚ⟦X⟧) + (-216 * X ^ 2 + 6480 * X ^ 3 - 69984 * X ^ 4 + 314928 * X ^ 5 - 472392 * X ^ 6 : ℚ⟦X⟧) * G + (324 * X ^ 2 - 11988 * X ^ 3 + 169128 * X ^ 4 - 1102248 * X ^ 5 + 3070548 * X ^ 6 - 2125764 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 + (-136 * X ^ 2 + 6192 * X ^ 3 - 113400 * X ^ 4 + 1049760 * X ^ 5 - 4986360 * X ^ 6 + 10392624 * X ^ 7 - 4251528 * X ^ 8 : ℚ⟦X⟧) * G ^ 3 + (102 * X ^ 2 - 4746 * X ^ 3 + 89694 * X ^ 4 - 872370 * X ^ 5 + 4527090 * X ^ 6 - 11534238 * X ^ 7 + 10983114 * X ^ 8 - 3188646 * X ^ 9 : ℚ⟦X⟧) * G ^ 4) * hP +
      ((-18 * X ^ 2 + 648 * X ^ 3 - 8748 * X ^ 4 + 52488 * X ^ 5 - 118098 * X ^ 6 : ℚ⟦X⟧) + (6 * X ^ 2 - 276 * X ^ 3 + 5130 * X ^ 4 - 48600 * X ^ 5 + 240570 * X ^ 6 - 551124 * X ^ 7 + 354294 * X ^ 8 : ℚ⟦X⟧) * (derivative ℚ G) + (-30 * X ^ 2 + 918 * X ^ 3 - 8748 * X ^ 4 + 8748 * X ^ 5 + 275562 * X ^ 6 - 1062882 * X ^ 7 : ℚ⟦X⟧) * G + (-22 * X ^ 2 + 1066 * X ^ 3 - 21294 * X ^ 4 + 224370 * X ^ 5 - 1319490 * X ^ 6 + 4185918 * X ^ 7 - 6259194 * X ^ 8 + 3188646 * X ^ 9 : ℚ⟦X⟧) * G * (derivative ℚ G) + (10 * X ^ 2 - 396 * X ^ 3 + 5670 * X ^ 4 - 29160 * X ^ 5 - 65610 * X ^ 6 + 1180980 * X ^ 7 - 3188646 * X ^ 8 : ℚ⟦X⟧) * G ^ 2 + (18 * X ^ 2 - 1008 * X ^ 3 + 23832 * X ^ 4 - 307152 * X ^ 5 + 2318220 * X ^ 6 - 10182672 * X ^ 7 + 24091992 * X ^ 8 - 25509168 * X ^ 9 + 9565938 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-58 * X ^ 2 + 2614 * X ^ 3 - 47106 * X ^ 4 + 423630 * X ^ 5 - 1888110 * X ^ 6 + 3162402 * X ^ 7 + 1535274 * X ^ 8 - 3188646 * X ^ 9 : ℚ⟦X⟧) * G ^ 3 + (-18 * X ^ 2 + 1026 * X ^ 3 - 24840 * X ^ 4 + 330984 * X ^ 5 - 2625372 * X ^ 6 + 12500892 * X ^ 7 - 34274664 * X ^ 8 + 49601160 * X ^ 9 - 35075106 * X ^ 10 + 9565938 * X ^ 11 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (48 * X ^ 2 - 2256 * X ^ 3 + 43248 * X ^ 4 - 429840 * X ^ 5 + 2313360 * X ^ 6 - 6333552 * X ^ 7 + 7243344 * X ^ 8 - 2834352 * X ^ 9 : ℚ⟦X⟧) * G ^ 4) * hd1 +
      ((9 * X ^ 2 - 333 * X ^ 3 + 4698 * X ^ 4 - 30618 * X ^ 5 + 85293 * X ^ 6 - 59049 * X ^ 7 : ℚ⟦X⟧) + (-12 * X ^ 2 + 552 * X ^ 3 - 10260 * X ^ 4 + 97200 * X ^ 5 - 481140 * X ^ 6 + 1102248 * X ^ 7 - 708588 * X ^ 8 : ℚ⟦X⟧) * G + (22 * X ^ 2 - 1066 * X ^ 3 + 21294 * X ^ 4 - 224370 * X ^ 5 + 1319490 * X ^ 6 - 4185918 * X ^ 7 + 6259194 * X ^ 8 - 3188646 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 + (-12 * X ^ 2 + 672 * X ^ 3 - 15888 * X ^ 4 + 204768 * X ^ 5 - 1545480 * X ^ 6 + 6788448 * X ^ 7 - 16061328 * X ^ 8 + 17006112 * X ^ 9 - 6377292 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 + (9 * X ^ 2 - 513 * X ^ 3 + 12420 * X ^ 4 - 165492 * X ^ 5 + 1312686 * X ^ 6 - 6250446 * X ^ 7 + 17137332 * X ^ 8 - 24800580 * X ^ 9 + 17537553 * X ^ 10 - 4782969 * X ^ 11 : ℚ⟦X⟧) * G ^ 4) * hd2
  have k2 : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
  have k3 : constantCoeff (3 : ℚ⟦X⟧) = 3 := cnum 3
  have hPG : (-3 + 27 * X : ℚ⟦X⟧) + (2 - 36 * X + 162 * X ^ 2 : ℚ⟦X⟧) * G + (-3 + 57 * X - 297 * X ^ 2 + 243 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k2, k3] at h'
    norm_num at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (3 : ℚ⟦X⟧) + (-3 + 27 * X : ℚ⟦X⟧) * G + (1 - 18 * X + 81 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (-1 + 19 * X - 99 * X ^ 2 + 81 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C 1 + derivative ℚ (derivative ℚ G) * X * X * X * C (-19) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 99 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-81) +
      derivative ℚ G * X * X * C (-20) + derivative ℚ G * X * X * X * C 216 +
      derivative ℚ G * X * X * X * X * C (-324) + G * X * X * C 36 +
      G * X * X * X * C (-180) =
      C 6 * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (3 : ℚ⟦X⟧) + (-3 + 27 * X : ℚ⟦X⟧) * G + (1 - 18 * X + 81 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (-1 + 19 * X - 99 * X ^ 2 + 81 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) (m : ℕ) :
    1 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-19) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      99 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + (-81) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      (-20) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 216 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      (-324) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + 36 * coeff (m + 1 + 1 + 1) G +
      (-180) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (3 : ℚ⟦X⟧) + (-3 + 27 * X : ℚ⟦X⟧) * G + (1 - 18 * X + 81 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (-1 + 19 * X - 99 * X ^ 2 + 81 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    6 * coeff (0 + 1 + 1 + 1) G + (-38) * coeff (0 + 1 + 1) G +
      (-40) * coeff (0 + 1 + 1) G + 216 * coeff (0 + 1) G +
      36 * coeff (0 + 1) G + (-180) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (3 : ℚ⟦X⟧) + (-3 + 27 * X : ℚ⟦X⟧) * G + (1 - 18 * X + 81 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (-1 + 19 * X - 99 * X ^ 2 + 81 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    12 * coeff (0 + 1 + 1 + 1 + 1) G + (-114) * coeff (0 + 1 + 1 + 1) G +
      198 * coeff (0 + 1 + 1) G + (-60) * coeff (0 + 1 + 1 + 1) G +
      432 * coeff (0 + 1 + 1) G + (-324) * coeff (0 + 1) G +
      36 * coeff (0 + 1 + 1) G + (-180) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A097189Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a097189.main := by
  intro T G hT hT0 hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  have e3 : m + 1 + 1 + 1 - 3 = m := rfl
  rw [e1, e2, e3]
  have hT0c : PowerSeries.constantCoeff T = 1 := by simpa using hT0
  have kn2 : PowerSeries.constantCoeff (2 : PowerSeries ℚ) = 2 := A097189Aux.cnum 2
  have kn9 : PowerSeries.constantCoeff (9 : PowerSeries ℚ) = 9 := A097189Aux.cnum 9
  have hN1 : ((1) + (2) * T ^ 2 + (-9) * PowerSeries.X : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [hT0c, kn2, kn9] at h'
    norm_num at h'
  have hM : ((1) + (2) * T ^ 2 + (-9) * PowerSeries.X) ^ 3 * ((3 : PowerSeries ℚ) + (-3 + 27 * PowerSeries.X : PowerSeries ℚ) * G + (1 - 18 * PowerSeries.X + 81 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (-1 + 19 * PowerSeries.X - 99 * PowerSeries.X ^ 2 + 81 * PowerSeries.X ^ 3 : PowerSeries ℚ) * G ^ 3) = 0 := by
    linear_combination ((24) + (24) * T ^ 3 + (-216) * PowerSeries.X) * hT +
      ((-9) + (-6) * T ^ 2 + (-12) * T ^ 4 + (-2) * G + (-2) * G * T ^ 2 + (4) * G * T ^ 4 + (-1) * G ^ 2 + (-4) * G ^ 2 * T ^ 2 + (-4) * G ^ 2 * T ^ 4 + (171) * PowerSeries.X + (108) * PowerSeries.X * T ^ 2 + (108) * PowerSeries.X * T ^ 4 + (48) * PowerSeries.X * G + (6) * PowerSeries.X * G * T ^ 2 + (-72) * PowerSeries.X * G * T ^ 4 + (37) * PowerSeries.X * G ^ 2 + (112) * PowerSeries.X * G ^ 2 * T ^ 2 + (76) * PowerSeries.X * G ^ 2 * T ^ 4 + (-891) * PowerSeries.X ^ 2 + (-486) * PowerSeries.X ^ 2 * T ^ 2 + (-324) * PowerSeries.X ^ 2 * G + (378) * PowerSeries.X ^ 2 * G * T ^ 2 + (324) * PowerSeries.X ^ 2 * G * T ^ 4 + (-522) * PowerSeries.X ^ 2 * G ^ 2 + (-1080) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 2 + (-396) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 4 + (729) * PowerSeries.X ^ 3 + (-2430) * PowerSeries.X ^ 3 * G * T ^ 2 + (3402) * PowerSeries.X ^ 3 * G ^ 2 + (3888) * PowerSeries.X ^ 3 * G ^ 2 * T ^ 2 + (324) * PowerSeries.X ^ 3 * G ^ 2 * T ^ 4 + (4374) * PowerSeries.X ^ 4 * G + (-9477) * PowerSeries.X ^ 4 * G ^ 2 + (-2916) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 2 + (6561) * PowerSeries.X ^ 5 * G ^ 2) * hG
  have hP : (3 : PowerSeries ℚ) + (-3 + 27 * PowerSeries.X : PowerSeries ℚ) * G + (1 - 18 * PowerSeries.X + 81 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (-1 + 19 * PowerSeries.X - 99 * PowerSeries.X ^ 2 + 81 * PowerSeries.X ^ 3 : PowerSeries ℚ) * G ^ 3 = 0 := (mul_eq_zero.mp hM).resolve_left (pow_ne_zero 3 hN1)
  have h0c : PowerSeries.constantCoeff G = (1 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A097189Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A097189Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A097189Aux.rel G hP h0c m
      push_cast
      linear_combination r
