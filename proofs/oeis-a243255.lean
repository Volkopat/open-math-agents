import OMAStatements.S_oeis_a243255

-- Problem: A243255: Expansion of 1/2 - (1/2)*(sqrt((2*sqrt(-3*x^2 - 2*x + 1) + 3*x - 2)/x)).
-- Upstream: formal-conjectures statements/oeis-a243255.lean:0 (declaration OMA.S_oeis_a243255.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A243255Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + X : ℚ⟦X⟧) * G + (1 : ℚ⟦X⟧) * G ^ 2 + (-2 * X : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (4 * X ^ 2 - 65 * X ^ 3 + 291 * X ^ 4 - 207 * X ^ 5 - 567 * X ^ 6) * derivative ℚ (derivative ℚ G) + (6 * X - 76 * X ^ 2 + 336 * X ^ 3 - 216 * X ^ 4 - 1134 * X ^ 5) * derivative ℚ G + (12 * X - 48 * X ^ 2) * G =
      6 * X - 24 * X ^ 2 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have hp0 : (1 * X : ℚ⟦X⟧) + (-1 + 1 * X : ℚ⟦X⟧) * G + (1 : ℚ⟦X⟧) * G * G + (-2 * X : ℚ⟦X⟧) * G * G * G + (1 * X : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 * X : ℚ⟦X⟧) + (-1 + 1 * X : ℚ⟦X⟧) * G + (1 : ℚ⟦X⟧) * G * G + (-2 * X : ℚ⟦X⟧) * G * G * G + (1 * X : ℚ⟦X⟧) * G * G * G * G) =
      (1 : ℚ⟦X⟧) + (-1 + X : ℚ⟦X⟧) * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G + (2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G ^ 3 + (4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G ^ 4 := by
    simp [Derivation.leibniz, d2]
    ring
  have hd1 : (1 : ℚ⟦X⟧) + (-1 + X : ℚ⟦X⟧) * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G + (2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G ^ 3 + (4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G ^ 4 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (1 : ℚ⟦X⟧) + (-1 + 1 * X : ℚ⟦X⟧) * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G + (2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G * G * G + (4 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((1 : ℚ⟦X⟧) + (-1 + 1 * X : ℚ⟦X⟧) * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G + (2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G * G * G + (4 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G * G * G * G) =
      (-1 + X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (2 : ℚ⟦X⟧) * (derivative ℚ G) + (2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-12 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-6 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d2, d4, d6]
    ring
  have hd2 : (-1 + X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (2 : ℚ⟦X⟧) * (derivative ℚ G) + (2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-12 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-6 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((-1 + X : ℚ⟦X⟧) + (2 : ℚ⟦X⟧) * G + (-6 * X : ℚ⟦X⟧) * G ^ 2 + (4 * X : ℚ⟦X⟧) * G ^ 3) ^ 3 * ((4 * X ^ 2 - 65 * X ^ 3 + 291 * X ^ 4 - 207 * X ^ 5 - 567 * X ^ 6) * derivative ℚ (derivative ℚ G) + (6 * X - 76 * X ^ 2 + 336 * X ^ 3 - 216 * X ^ 4 - 1134 * X ^ 5) * derivative ℚ G + (12 * X - 48 * X ^ 2) * G - (6 * X - 24 * X ^ 2)) = 0 := by
    linear_combination ((30 * X - 136 * X ^ 2 - 408 * X ^ 3 + 1800 * X ^ 4 - 198 * X ^ 5 : ℚ⟦X⟧) + (-114 * X + 564 * X ^ 2 - 228 * X ^ 3 - 864 * X ^ 4 + 918 * X ^ 5 - 6804 * X ^ 6 : ℚ⟦X⟧) * G + (90 * X + 234 * X ^ 2 - 3186 * X ^ 3 + 2646 * X ^ 4 + 2376 * X ^ 5 : ℚ⟦X⟧) * G ^ 2 + (48 * X - 1580 * X ^ 2 + 6144 * X ^ 3 - 936 * X ^ 4 - 5904 * X ^ 5 + 6804 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 + (-24 * X + 750 * X ^ 2 - 1362 * X ^ 3 - 6102 * X ^ 4 + 1242 * X ^ 5 + 13608 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 + (48 * X ^ 2 - 2052 * X ^ 3 + 7884 * X ^ 4 + 2052 * X ^ 5 - 20412 * X ^ 6 : ℚ⟦X⟧) * G ^ 5 + (-16 * X ^ 2 + 684 * X ^ 3 - 2628 * X ^ 4 - 684 * X ^ 5 + 6804 * X ^ 6 : ℚ⟦X⟧) * G ^ 6) * hP +
      ((6 * X - 72 * X ^ 2 + 226 * X ^ 3 + 330 * X ^ 4 - 1776 * X ^ 5 + 198 * X ^ 6 : ℚ⟦X⟧) + (8 * X ^ 2 - 138 * X ^ 3 + 712 * X ^ 4 - 996 * X ^ 5 - 720 * X ^ 6 + 1134 * X ^ 7 : ℚ⟦X⟧) * (derivative ℚ G) + (-24 * X + 320 * X ^ 2 - 1566 * X ^ 3 + 2406 * X ^ 4 + 594 * X ^ 5 - 918 * X ^ 6 + 6804 * X ^ 7 : ℚ⟦X⟧) * G + (-16 * X ^ 2 + 212 * X ^ 3 - 336 * X ^ 4 - 3444 * X ^ 5 + 8244 * X ^ 6 + 4320 * X ^ 7 - 6804 * X ^ 8 : ℚ⟦X⟧) * G * (derivative ℚ G) + (24 * X - 280 * X ^ 2 + 1236 * X ^ 3 - 972 * X ^ 4 - 1692 * X ^ 5 - 9180 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (192 * X ^ 3 - 3168 * X ^ 4 + 14748 * X ^ 5 - 13428 * X ^ 6 - 24732 * X ^ 7 + 6804 * X ^ 8 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-80 * X ^ 2 + 644 * X ^ 3 - 2952 * X ^ 4 + 2640 * X ^ 5 + 19512 * X ^ 6 - 6804 * X ^ 7 : ℚ⟦X⟧) * G ^ 3 + (-128 * X ^ 3 + 1792 * X ^ 4 - 4632 * X ^ 5 - 14328 * X ^ 6 + 33048 * X ^ 7 + 40824 * X ^ 8 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (40 * X ^ 2 - 282 * X ^ 3 + 1686 * X ^ 4 - 2430 * X ^ 5 - 8046 * X ^ 6 - 13608 * X ^ 7 : ℚ⟦X⟧) * G ^ 4 + (480 * X ^ 4 - 7800 * X ^ 5 + 34920 * X ^ 6 - 24840 * X ^ 7 - 68040 * X ^ 8 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (-48 * X ^ 3 - 252 * X ^ 4 + 1332 * X ^ 5 - 2052 * X ^ 6 + 20412 * X ^ 7 : ℚ⟦X⟧) * G ^ 5 + (-192 * X ^ 4 + 3120 * X ^ 5 - 13968 * X ^ 6 + 9936 * X ^ 7 + 27216 * X ^ 8 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (16 * X ^ 3 + 84 * X ^ 4 - 444 * X ^ 5 + 684 * X ^ 6 - 6804 * X ^ 7 : ℚ⟦X⟧) * G ^ 6) * hd1 +
      ((4 * X ^ 2 - 73 * X ^ 3 + 425 * X ^ 4 - 854 * X ^ 5 + 138 * X ^ 6 + 927 * X ^ 7 - 567 * X ^ 8 : ℚ⟦X⟧) + (-16 * X ^ 2 + 276 * X ^ 3 - 1424 * X ^ 4 + 1992 * X ^ 5 + 1440 * X ^ 6 - 2268 * X ^ 7 : ℚ⟦X⟧) * G + (16 * X ^ 2 - 212 * X ^ 3 + 336 * X ^ 4 + 3444 * X ^ 5 - 8244 * X ^ 6 - 4320 * X ^ 7 + 6804 * X ^ 8 : ℚ⟦X⟧) * G ^ 2 + (-128 * X ^ 3 + 2112 * X ^ 4 - 9832 * X ^ 5 + 8952 * X ^ 6 + 16488 * X ^ 7 - 4536 * X ^ 8 : ℚ⟦X⟧) * G ^ 3 + (64 * X ^ 3 - 896 * X ^ 4 + 2316 * X ^ 5 + 7164 * X ^ 6 - 16524 * X ^ 7 - 20412 * X ^ 8 : ℚ⟦X⟧) * G ^ 4 + (-192 * X ^ 4 + 3120 * X ^ 5 - 13968 * X ^ 6 + 9936 * X ^ 7 + 27216 * X ^ 8 : ℚ⟦X⟧) * G ^ 5 + (64 * X ^ 4 - 1040 * X ^ 5 + 4656 * X ^ 6 - 3312 * X ^ 7 - 9072 * X ^ 8 : ℚ⟦X⟧) * G ^ 6) * hd2
  have k2 : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
  have hPG : (-1 + X : ℚ⟦X⟧) + (2 : ℚ⟦X⟧) * G + (-6 * X : ℚ⟦X⟧) * G ^ 2 + (4 * X : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k2] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + X : ℚ⟦X⟧) * G + (1 : ℚ⟦X⟧) * G ^ 2 + (-2 * X : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C 4 + derivative ℚ (derivative ℚ G) * X * X * X * C (-65) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 291 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-207) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-567) + derivative ℚ G * X * C 6 +
      derivative ℚ G * X * X * C (-76) + derivative ℚ G * X * X * X * C 336 +
      derivative ℚ G * X * X * X * X * C (-216) + derivative ℚ G * X * X * X * X * X * C (-1134) +
      G * X * C 12 + G * X * X * C (-48) =
      C 6 * X + C (-24) * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + X : ℚ⟦X⟧) * G + (1 : ℚ⟦X⟧) * G ^ 2 + (-2 * X : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    4 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-65) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      291 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-207) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-567) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + 6 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-76) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 336 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-216) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-1134) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      12 * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-48) * coeff (m + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + X : ℚ⟦X⟧) * G + (1 : ℚ⟦X⟧) * G ^ 2 + (-2 * X : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    48 * coeff (0 + 1 + 1 + 1 + 1) G + (-390) * coeff (0 + 1 + 1 + 1) G +
      582 * coeff (0 + 1 + 1) G + 24 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-228) * coeff (0 + 1 + 1 + 1) G + 672 * coeff (0 + 1 + 1) G +
      (-216) * coeff (0 + 1) G + 12 * coeff (0 + 1 + 1 + 1) G +
      (-48) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + X : ℚ⟦X⟧) * G + (1 : ℚ⟦X⟧) * G ^ 2 + (-2 * X : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    80 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-780) * coeff (0 + 1 + 1 + 1 + 1) G +
      1746 * coeff (0 + 1 + 1 + 1) G + (-414) * coeff (0 + 1 + 1) G +
      30 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-304) * coeff (0 + 1 + 1 + 1 + 1) G +
      1008 * coeff (0 + 1 + 1 + 1) G + (-432) * coeff (0 + 1 + 1) G +
      (-1134) * coeff (0 + 1) G + 12 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-48) * coeff (0 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A243255Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a243255.main := by
  intro T U G hT _ hU _ hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  have hM : ((16 : PowerSeries ℚ) * PowerSeries.X ^ 1) * ((PowerSeries.X : PowerSeries ℚ) + (-1 + PowerSeries.X : PowerSeries ℚ) * G + (1 : PowerSeries ℚ) * G ^ 2 + (-2 * PowerSeries.X : PowerSeries ℚ) * G ^ 3 + (PowerSeries.X : PowerSeries ℚ) * G ^ 4) = 0 := by
    linear_combination ((4)) * hT + ((2) + (2) * T + (-3) * PowerSeries.X + (1) * PowerSeries.X * U ^ 2) * hU + ((-4) * PowerSeries.X + (-4) * PowerSeries.X * U + (8) * PowerSeries.X * G + (5) * PowerSeries.X ^ 2 + (5) * PowerSeries.X ^ 2 * U + (-1) * PowerSeries.X ^ 2 * U ^ 2 + (-1) * PowerSeries.X ^ 2 * U ^ 3 + (-6) * PowerSeries.X ^ 2 * G + (4) * PowerSeries.X ^ 2 * G * U + (2) * PowerSeries.X ^ 2 * G * U ^ 2 + (-12) * PowerSeries.X ^ 2 * G ^ 2 + (-4) * PowerSeries.X ^ 2 * G ^ 2 * U + (8) * PowerSeries.X ^ 2 * G ^ 3) * hG
  have hc : (16 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    rw [A243255Aux.cnum, map_zero] at h'
    norm_num at h'
  have hMne : ((16 : PowerSeries ℚ) * PowerSeries.X ^ 1) ≠ 0 := mul_ne_zero hc (pow_ne_zero 1 PowerSeries.X_ne_zero)
  have hP : (PowerSeries.X : PowerSeries ℚ) + (-1 + PowerSeries.X : PowerSeries ℚ) * G + (1 : PowerSeries ℚ) * G ^ 2 + (-2 * PowerSeries.X : PowerSeries ℚ) * G ^ 3 + (PowerSeries.X : PowerSeries ℚ) * G ^ 4 = 0 := (mul_eq_zero.mp hM).resolve_left hMne
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A243255Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A243255Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A243255Aux.rel G hP h0c m
      push_cast
      linear_combination r
