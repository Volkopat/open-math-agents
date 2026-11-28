import OMAStatements.S_oeis_a190163

-- Problem: A190163: Number of subwords of type dh^ju (j>=1), where u=(1,1), h=(1,0), and d=(1,-1), in all peakless Motzkin paths of length n (can be easily expressed using RNA secondary structure terminology).
-- Upstream: formal-conjectures statements/oeis-a190163.lean:0 (declaration OMA.S_oeis_a190163.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A190163Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (-X ^ 7 : ℚ⟦X⟧) + (1 - 5 * X + 7 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - 7 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * G + (X - 4 * X ^ 2 + 4 * X ^ 3 - 2 * X ^ 4 + 4 * X ^ 5 - 4 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (-4 * X ^ 2 + 13 * X ^ 3 - 7 * X ^ 4 + 5 * X ^ 5 - 13 * X ^ 6 + 7 * X ^ 7 - X ^ 8) * derivative ℚ (derivative ℚ G) + (20 * X - 46 * X ^ 2 + 17 * X ^ 3 - 6 * X ^ 4 - 14 * X ^ 5 + 13 * X ^ 6 - 2 * X ^ 7) * derivative ℚ G + (28 - 44 * X + 35 * X ^ 2 - 11 * X ^ 3 + 7 * X ^ 4) * G =
      0 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d5 : derivative ℚ (5 : ℚ⟦X⟧) = 0 := dnum 5
  have d7 : derivative ℚ (7 : ℚ⟦X⟧) = 0 := dnum 7
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d9 : derivative ℚ (9 : ℚ⟦X⟧) = 0 := dnum 9
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d14 : derivative ℚ (14 : ℚ⟦X⟧) = 0 := dnum 14
  have d20 : derivative ℚ (20 : ℚ⟦X⟧) = 0 := dnum 20
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have d35 : derivative ℚ (35 : ℚ⟦X⟧) = 0 := dnum 35
  have hp0 : (-1 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (1 - 5 * X + 7 * (X * X) - 3 * (X * X * X) + 5 * (X * X * X * X) - 7 * (X * X * X * X * X) + 2 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G + (1 * X - 4 * (X * X) + 4 * (X * X * X) - 2 * (X * X * X * X) + 4 * (X * X * X * X * X) - 4 * (X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-1 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (1 - 5 * X + 7 * (X * X) - 3 * (X * X * X) + 5 * (X * X * X * X) - 7 * (X * X * X * X * X) + 2 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G + (1 * X - 4 * (X * X) + 4 * (X * X * X) - 2 * (X * X * X * X) + 4 * (X * X * X * X * X) - 4 * (X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * G) =
      (-7 * X ^ 6 : ℚ⟦X⟧) + (1 - 5 * X + 7 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - 7 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * (derivative ℚ G) + (-5 + 14 * X - 9 * X ^ 2 + 20 * X ^ 3 - 35 * X ^ 4 + 12 * X ^ 5 : ℚ⟦X⟧) * G + (2 * X - 8 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 8 * X ^ 6 + 2 * X ^ 7 : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 - 8 * X + 12 * X ^ 2 - 8 * X ^ 3 + 20 * X ^ 4 - 24 * X ^ 5 + 7 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 := by
    simp [Derivation.leibniz, d2, d3, d4, d5, d7]
    ring
  have hd1 : (-7 * X ^ 6 : ℚ⟦X⟧) + (1 - 5 * X + 7 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - 7 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * (derivative ℚ G) + (-5 + 14 * X - 9 * X ^ 2 + 20 * X ^ 3 - 35 * X ^ 4 + 12 * X ^ 5 : ℚ⟦X⟧) * G + (2 * X - 8 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 8 * X ^ 6 + 2 * X ^ 7 : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 - 8 * X + 12 * X ^ 2 - 8 * X ^ 3 + 20 * X ^ 4 - 24 * X ^ 5 + 7 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (-7 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (1 - 5 * X + 7 * (X * X) - 3 * (X * X * X) + 5 * (X * X * X * X) - 7 * (X * X * X * X * X) + 2 * (X * X * X * X * X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (-5 + 14 * X - 9 * (X * X) + 20 * (X * X * X) - 35 * (X * X * X * X) + 12 * (X * X * X * X * X) : ℚ⟦X⟧) * G + (2 * X - 8 * (X * X) + 8 * (X * X * X) - 4 * (X * X * X * X) + 8 * (X * X * X * X * X) - 8 * (X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 - 8 * X + 12 * (X * X) - 8 * (X * X * X) + 20 * (X * X * X * X) - 24 * (X * X * X * X * X) + 7 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((-7 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (1 - 5 * X + 7 * (X * X) - 3 * (X * X * X) + 5 * (X * X * X * X) - 7 * (X * X * X * X * X) + 2 * (X * X * X * X * X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (-5 + 14 * X - 9 * (X * X) + 20 * (X * X * X) - 35 * (X * X * X * X) + 12 * (X * X * X * X * X) : ℚ⟦X⟧) * G + (2 * X - 8 * (X * X) + 8 * (X * X * X) - 4 * (X * X * X * X) + 8 * (X * X * X * X * X) - 8 * (X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 - 8 * X + 12 * (X * X) - 8 * (X * X * X) + 20 * (X * X * X * X) - 24 * (X * X * X * X * X) + 7 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * G) =
      (-42 * X ^ 5 : ℚ⟦X⟧) + (1 - 5 * X + 7 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - 7 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-10 + 28 * X - 18 * X ^ 2 + 40 * X ^ 3 - 70 * X ^ 4 + 24 * X ^ 5 : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X - 8 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 8 * X ^ 6 + 2 * X ^ 7 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (14 - 18 * X + 60 * X ^ 2 - 140 * X ^ 3 + 60 * X ^ 4 : ℚ⟦X⟧) * G + (2 * X - 8 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 8 * X ^ 6 + 2 * X ^ 7 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (4 - 32 * X + 48 * X ^ 2 - 32 * X ^ 3 + 80 * X ^ 4 - 96 * X ^ 5 + 28 * X ^ 6 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-8 + 24 * X - 24 * X ^ 2 + 80 * X ^ 3 - 120 * X ^ 4 + 42 * X ^ 5 : ℚ⟦X⟧) * G ^ 2 := by
    simp [Derivation.leibniz, d2, d3, d4, d5, d7, d8, d9, d12, d14, d20, d24, d35]
    ring
  have hd2 : (-42 * X ^ 5 : ℚ⟦X⟧) + (1 - 5 * X + 7 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - 7 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-10 + 28 * X - 18 * X ^ 2 + 40 * X ^ 3 - 70 * X ^ 4 + 24 * X ^ 5 : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X - 8 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 8 * X ^ 6 + 2 * X ^ 7 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (14 - 18 * X + 60 * X ^ 2 - 140 * X ^ 3 + 60 * X ^ 4 : ℚ⟦X⟧) * G + (2 * X - 8 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 8 * X ^ 6 + 2 * X ^ 7 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (4 - 32 * X + 48 * X ^ 2 - 32 * X ^ 3 + 80 * X ^ 4 - 96 * X ^ 5 + 28 * X ^ 6 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-8 + 24 * X - 24 * X ^ 2 + 80 * X ^ 3 - 120 * X ^ 4 + 42 * X ^ 5 : ℚ⟦X⟧) * G ^ 2 = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((1 - 5 * X + 7 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - 7 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) + (2 * X - 8 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 8 * X ^ 6 + 2 * X ^ 7 : ℚ⟦X⟧) * G) ^ 3 * ((-4 * X ^ 2 + 13 * X ^ 3 - 7 * X ^ 4 + 5 * X ^ 5 - 13 * X ^ 6 + 7 * X ^ 7 - X ^ 8) * derivative ℚ (derivative ℚ G) + (20 * X - 46 * X ^ 2 + 17 * X ^ 3 - 6 * X ^ 4 - 14 * X ^ 5 + 13 * X ^ 6 - 2 * X ^ 7) * derivative ℚ G + (28 - 44 * X + 35 * X ^ 2 - 11 * X ^ 3 + 7 * X ^ 4) * G - (0)) = 0 := by
    linear_combination ((28 - 224 * X + 413 * X ^ 2 + 1190 * X ^ 3 - 6223 * X ^ 4 + 12467 * X ^ 5 - 21553 * X ^ 6 + 39179 * X ^ 7 - 54439 * X ^ 8 + 60865 * X ^ 9 - 73213 * X ^ 10 + 79555 * X ^ 11 - 66493 * X ^ 12 + 55979 * X ^ 13 - 47824 * X ^ 14 + 30485 * X ^ 15 - 16576 * X ^ 16 + 9926 * X ^ 17 - 4522 * X ^ 18 + 1078 * X ^ 19 - 98 * X ^ 20 : ℚ⟦X⟧) + (120 * X - 786 * X ^ 2 + 812 * X ^ 3 + 5302 * X ^ 4 - 19012 * X ^ 5 + 34390 * X ^ 6 - 60308 * X ^ 7 + 100484 * X ^ 8 - 125264 * X ^ 9 + 134996 * X ^ 10 - 151104 * X ^ 11 + 145972 * X ^ 12 - 111016 * X ^ 13 + 80734 * X ^ 14 - 57772 * X ^ 15 + 31046 * X ^ 16 - 10316 * X ^ 17 + 1862 * X ^ 18 - 140 * X ^ 19 : ℚ⟦X⟧) * G + (120 * X ^ 2 - 666 * X ^ 3 + 266 * X ^ 4 + 5022 * X ^ 5 - 14270 * X ^ 6 + 24862 * X ^ 7 - 44974 * X ^ 8 + 70844 * X ^ 9 - 84060 * X ^ 10 + 92140 * X ^ 11 - 101820 * X ^ 12 + 93436 * X ^ 13 - 70116 * X ^ 14 + 51518 * X ^ 15 - 35470 * X ^ 16 + 17878 * X ^ 17 - 5606 * X ^ 18 + 966 * X ^ 19 - 70 * X ^ 20 : ℚ⟦X⟧) * G ^ 2) * hP +
      ((20 * X - 286 * X ^ 2 + 1699 * X ^ 3 - 5486 * X ^ 4 + 10969 * X ^ 5 - 16451 * X ^ 6 + 24505 * X ^ 7 - 35831 * X ^ 8 + 41575 * X ^ 9 - 41341 * X ^ 10 + 43861 * X ^ 11 - 42319 * X ^ 12 + 31681 * X ^ 13 - 22829 * X ^ 14 + 17236 * X ^ 15 - 10049 * X ^ 16 + 4270 * X ^ 17 - 1754 * X ^ 18 + 670 * X ^ 19 - 154 * X ^ 20 + 14 * X ^ 21 : ℚ⟦X⟧) + (8 * X ^ 3 - 98 * X ^ 4 + 496 * X ^ 5 - 1366 * X ^ 6 + 2400 * X ^ 7 - 3450 * X ^ 8 + 5132 * X ^ 9 - 6956 * X ^ 10 + 7432 * X ^ 11 - 7284 * X ^ 12 + 7448 * X ^ 13 - 6556 * X ^ 14 + 4600 * X ^ 15 - 3138 * X ^ 16 + 2136 * X ^ 17 - 1094 * X ^ 18 + 344 * X ^ 19 - 58 * X ^ 20 + 4 * X ^ 21 : ℚ⟦X⟧) * (derivative ℚ G) + (96 * X ^ 2 - 1204 * X ^ 3 + 6254 * X ^ 4 - 17698 * X ^ 5 + 31788 * X ^ 6 - 45876 * X ^ 7 + 67974 * X ^ 8 - 93226 * X ^ 9 + 100994 * X ^ 10 - 98758 * X ^ 11 + 100990 * X ^ 12 - 90266 * X ^ 13 + 63970 * X ^ 14 - 43434 * X ^ 15 + 29784 * X ^ 16 - 15648 * X ^ 17 + 5086 * X ^ 18 - 890 * X ^ 19 + 64 * X ^ 20 : ℚ⟦X⟧) * G + (16 * X ^ 4 - 180 * X ^ 5 + 828 * X ^ 6 - 2068 * X ^ 7 + 3396 * X ^ 8 - 4908 * X ^ 9 + 7348 * X ^ 10 - 9480 * X ^ 11 + 9816 * X ^ 12 - 9800 * X ^ 13 + 9864 * X ^ 14 - 8280 * X ^ 15 + 5752 * X ^ 16 - 3972 * X ^ 17 + 2604 * X ^ 18 - 1252 * X ^ 19 + 372 * X ^ 20 - 60 * X ^ 21 + 4 * X ^ 22 : ℚ⟦X⟧) * G * (derivative ℚ G) + (104 * X ^ 3 - 1190 * X ^ 4 + 5590 * X ^ 5 - 14302 * X ^ 6 + 23946 * X ^ 7 - 34626 * X ^ 8 + 51722 * X ^ 9 - 67628 * X ^ 10 + 70828 * X ^ 11 - 70428 * X ^ 12 + 71108 * X ^ 13 - 60628 * X ^ 14 + 42412 * X ^ 15 - 29166 * X ^ 16 + 19326 * X ^ 17 - 9542 * X ^ 18 + 2930 * X ^ 19 - 490 * X ^ 20 + 34 * X ^ 21 : ℚ⟦X⟧) * G ^ 2) * hd1 +
      ((-4 * X ^ 2 + 53 * X ^ 3 - 293 * X ^ 4 + 886 * X ^ 5 - 1680 * X ^ 6 + 2445 * X ^ 7 - 3571 * X ^ 8 + 5039 * X ^ 9 - 5633 * X ^ 10 + 5441 * X ^ 11 - 5567 * X ^ 12 + 5159 * X ^ 13 - 3697 * X ^ 14 + 2472 * X ^ 15 - 1734 * X ^ 16 + 949 * X ^ 17 - 317 * X ^ 18 + 56 * X ^ 19 - 4 * X ^ 20 : ℚ⟦X⟧) + (-16 * X ^ 3 + 196 * X ^ 4 - 992 * X ^ 5 + 2732 * X ^ 6 - 4800 * X ^ 7 + 6900 * X ^ 8 - 10264 * X ^ 9 + 13912 * X ^ 10 - 14864 * X ^ 11 + 14568 * X ^ 12 - 14896 * X ^ 13 + 13112 * X ^ 14 - 9200 * X ^ 15 + 6276 * X ^ 16 - 4272 * X ^ 17 + 2188 * X ^ 18 - 688 * X ^ 19 + 116 * X ^ 20 - 8 * X ^ 21 : ℚ⟦X⟧) * G + (-16 * X ^ 4 + 180 * X ^ 5 - 828 * X ^ 6 + 2068 * X ^ 7 - 3396 * X ^ 8 + 4908 * X ^ 9 - 7348 * X ^ 10 + 9480 * X ^ 11 - 9816 * X ^ 12 + 9800 * X ^ 13 - 9864 * X ^ 14 + 8280 * X ^ 15 - 5752 * X ^ 16 + 3972 * X ^ 17 - 2604 * X ^ 18 + 1252 * X ^ 19 - 372 * X ^ 20 + 60 * X ^ 21 - 4 * X ^ 22 : ℚ⟦X⟧) * G ^ 2) * hd2
  have hPG : (1 - 5 * X + 7 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - 7 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) + (2 * X - 8 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 8 * X ^ 6 + 2 * X ^ 7 : ℚ⟦X⟧) * G ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (-X ^ 7 : ℚ⟦X⟧) + (1 - 5 * X + 7 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - 7 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * G + (X - 4 * X ^ 2 + 4 * X ^ 3 - 2 * X ^ 4 + 4 * X ^ 5 - 4 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C (-4) + derivative ℚ (derivative ℚ G) * X * X * X * C 13 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-7) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 5 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-13) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C 7 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * C (-1) + derivative ℚ G * X * C 20 +
      derivative ℚ G * X * X * C (-46) + derivative ℚ G * X * X * X * C 17 +
      derivative ℚ G * X * X * X * X * C (-6) + derivative ℚ G * X * X * X * X * X * C (-14) +
      derivative ℚ G * X * X * X * X * X * X * C 13 + derivative ℚ G * X * X * X * X * X * X * X * C (-2) +
      G * C 28 + G * X * C (-44) +
      G * X * X * C 35 + G * X * X * X * C (-11) +
      G * X * X * X * X * C 7 =
      0 := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (-X ^ 7 : ℚ⟦X⟧) + (1 - 5 * X + 7 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - 7 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * G + (X - 4 * X ^ 2 + 4 * X ^ 3 - 2 * X ^ 4 + 4 * X ^ 5 - 4 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    (-4) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 13 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 5 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-13) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + 7 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-1) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + 20 * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-46) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 17 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-14) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      13 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-2) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      28 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-44) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      35 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-11) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      7 * coeff (m + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (-X ^ 7 : ℚ⟦X⟧) + (1 - 5 * X + 7 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - 7 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * G + (X - 4 * X ^ 2 + 4 * X ^ 3 - 2 * X ^ 4 + 4 * X ^ 5 - 4 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (-120) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 260 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-84) * coeff (0 + 1 + 1 + 1 + 1) G + 30 * coeff (0 + 1 + 1 + 1) G +
      (-26) * coeff (0 + 1 + 1) G + 120 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-230) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 68 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-18) * coeff (0 + 1 + 1 + 1) G + (-28) * coeff (0 + 1 + 1) G +
      13 * coeff (0 + 1) G + 28 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-44) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 35 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-11) * coeff (0 + 1 + 1 + 1) G + 7 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (-X ^ 7 : ℚ⟦X⟧) + (1 - 5 * X + 7 * X ^ 2 - 3 * X ^ 3 + 5 * X ^ 4 - 7 * X ^ 5 + 2 * X ^ 6 : ℚ⟦X⟧) * G + (X - 4 * X ^ 2 + 4 * X ^ 3 - 2 * X ^ 4 + 4 * X ^ 5 - 4 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (-168) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 390 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-140) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 60 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-78) * coeff (0 + 1 + 1 + 1) G + 14 * coeff (0 + 1 + 1) G +
      140 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-276) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      85 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-24) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-42) * coeff (0 + 1 + 1 + 1) G + 26 * coeff (0 + 1 + 1) G +
      (-2) * coeff (0 + 1) G + 28 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-44) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 35 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-11) * coeff (0 + 1 + 1 + 1 + 1) G + 7 * coeff (0 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A190163Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a190163.main := by
  intro T G hT hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 6, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m := rfl
  rw [e1, e2, e3, e4, e5, e6]
  have hN1 : ((1) + (-1) * PowerSeries.X + (-1) * PowerSeries.X ^ 2 * T ^ 2 + (1) * PowerSeries.X ^ 3 * T ^ 2 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [] at h'
  have hM : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 14) * (((1) + (-1) * PowerSeries.X + (-1) * PowerSeries.X ^ 2 * T ^ 2 + (1) * PowerSeries.X ^ 3 * T ^ 2) ^ 2 * ((-PowerSeries.X ^ 7 : PowerSeries ℚ) + (1 - 5 * PowerSeries.X + 7 * PowerSeries.X ^ 2 - 3 * PowerSeries.X ^ 3 + 5 * PowerSeries.X ^ 4 - 7 * PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 6 : PowerSeries ℚ) * G + (PowerSeries.X - 4 * PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3 - 2 * PowerSeries.X ^ 4 + 4 * PowerSeries.X ^ 5 - 4 * PowerSeries.X ^ 6 + PowerSeries.X ^ 7 : PowerSeries ℚ) * G ^ 2)) = 0 := by
    linear_combination ((1) * PowerSeries.X ^ 19 * T ^ 2 + (-1) * PowerSeries.X ^ 19 * T ^ 3 + (-6) * PowerSeries.X ^ 20 * T ^ 2 + (5) * PowerSeries.X ^ 20 * T ^ 3 + (-1) * PowerSeries.X ^ 21 + (-1) * PowerSeries.X ^ 21 * T + (11) * PowerSeries.X ^ 21 * T ^ 2 + (-6) * PowerSeries.X ^ 21 * T ^ 3 + (-2) * PowerSeries.X ^ 21 * T ^ 4 + (1) * PowerSeries.X ^ 21 * T ^ 5 + (2) * PowerSeries.X ^ 22 + (3) * PowerSeries.X ^ 22 * T + (-6) * PowerSeries.X ^ 22 * T ^ 2 + (-3) * PowerSeries.X ^ 22 * T ^ 3 + (10) * PowerSeries.X ^ 22 * T ^ 4 + (-5) * PowerSeries.X ^ 22 * T ^ 5 + (-1) * PowerSeries.X ^ 23 + (-4) * PowerSeries.X ^ 23 * T + (3) * PowerSeries.X ^ 23 * T ^ 2 + (5) * PowerSeries.X ^ 23 * T ^ 3 + (-13) * PowerSeries.X ^ 23 * T ^ 4 + (5) * PowerSeries.X ^ 23 * T ^ 5 + (1) * PowerSeries.X ^ 23 * T ^ 6 + (3) * PowerSeries.X ^ 24 * T + (-8) * PowerSeries.X ^ 24 * T ^ 2 + (4) * PowerSeries.X ^ 24 * T ^ 3 + (6) * PowerSeries.X ^ 24 * T ^ 5 + (-4) * PowerSeries.X ^ 24 * T ^ 6 + (-1) * PowerSeries.X ^ 25 * T + (4) * PowerSeries.X ^ 25 * T ^ 2 + (1) * PowerSeries.X ^ 25 * T ^ 3 + (-6) * PowerSeries.X ^ 25 * T ^ 5 + (4) * PowerSeries.X ^ 25 * T ^ 6 + (2) * PowerSeries.X ^ 26 * T ^ 2 + (-9) * PowerSeries.X ^ 26 * T ^ 3 + (10) * PowerSeries.X ^ 26 * T ^ 4 + (-2) * PowerSeries.X ^ 26 * T ^ 5 + (-2) * PowerSeries.X ^ 26 * T ^ 6 + (-1) * PowerSeries.X ^ 27 * T ^ 2 + (2) * PowerSeries.X ^ 27 * T ^ 3 + (2) * PowerSeries.X ^ 27 * T ^ 4 + (-7) * PowerSeries.X ^ 27 * T ^ 5 + (4) * PowerSeries.X ^ 27 * T ^ 6 + (3) * PowerSeries.X ^ 28 * T ^ 3 + (-10) * PowerSeries.X ^ 28 * T ^ 4 + (11) * PowerSeries.X ^ 28 * T ^ 5 + (-4) * PowerSeries.X ^ 28 * T ^ 6 + (-1) * PowerSeries.X ^ 29 * T ^ 3 + (3) * PowerSeries.X ^ 29 * T ^ 4 + (-3) * PowerSeries.X ^ 29 * T ^ 5 + (1) * PowerSeries.X ^ 29 * T ^ 6) * hT +
      ((-1) * PowerSeries.X ^ 14 + (6) * PowerSeries.X ^ 15 + (-1) * PowerSeries.X ^ 15 * G + (-12) * PowerSeries.X ^ 16 + (1) * PowerSeries.X ^ 16 * T ^ 2 + (5) * PowerSeries.X ^ 16 * G + (10) * PowerSeries.X ^ 17 + (-6) * PowerSeries.X ^ 17 * T ^ 2 + (-8) * PowerSeries.X ^ 17 * G + (1) * PowerSeries.X ^ 17 * G * T ^ 2 + (-8) * PowerSeries.X ^ 18 + (12) * PowerSeries.X ^ 18 * T ^ 2 + (6) * PowerSeries.X ^ 18 * G + (-5) * PowerSeries.X ^ 18 * G * T ^ 2 + (12) * PowerSeries.X ^ 19 + (-10) * PowerSeries.X ^ 19 * T ^ 2 + (-6) * PowerSeries.X ^ 19 * G + (8) * PowerSeries.X ^ 19 * G * T ^ 2 + (-9) * PowerSeries.X ^ 20 + (7) * PowerSeries.X ^ 20 * T ^ 2 + (2) * PowerSeries.X ^ 20 * T ^ 3 + (-1) * PowerSeries.X ^ 20 * T ^ 4 + (8) * PowerSeries.X ^ 20 * G + (-6) * PowerSeries.X ^ 20 * G * T ^ 2 + (2) * PowerSeries.X ^ 21 + (-8) * PowerSeries.X ^ 21 * T ^ 2 + (-8) * PowerSeries.X ^ 21 * T ^ 3 + (4) * PowerSeries.X ^ 21 * T ^ 4 + (-5) * PowerSeries.X ^ 21 * G + (6) * PowerSeries.X ^ 21 * G * T ^ 2 + (5) * PowerSeries.X ^ 22 * T ^ 2 + (8) * PowerSeries.X ^ 22 * T ^ 3 + (-4) * PowerSeries.X ^ 22 * T ^ 4 + (1) * PowerSeries.X ^ 22 * G + (-8) * PowerSeries.X ^ 22 * G * T ^ 2 + (-4) * PowerSeries.X ^ 23 * T ^ 3 + (2) * PowerSeries.X ^ 23 * T ^ 4 + (5) * PowerSeries.X ^ 23 * G * T ^ 2 + (-4) * PowerSeries.X ^ 24 * T ^ 2 + (8) * PowerSeries.X ^ 24 * T ^ 3 + (-4) * PowerSeries.X ^ 24 * T ^ 4 + (-1) * PowerSeries.X ^ 24 * G * T ^ 2 + (4) * PowerSeries.X ^ 25 * T ^ 2 + (-8) * PowerSeries.X ^ 25 * T ^ 3 + (4) * PowerSeries.X ^ 25 * T ^ 4 + (-1) * PowerSeries.X ^ 26 * T ^ 2 + (2) * PowerSeries.X ^ 26 * T ^ 3 + (-1) * PowerSeries.X ^ 26 * T ^ 4) * hG
  have hLne : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 14) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero 14 PowerSeries.X_ne_zero)
  have hP : (-PowerSeries.X ^ 7 : PowerSeries ℚ) + (1 - 5 * PowerSeries.X + 7 * PowerSeries.X ^ 2 - 3 * PowerSeries.X ^ 3 + 5 * PowerSeries.X ^ 4 - 7 * PowerSeries.X ^ 5 + 2 * PowerSeries.X ^ 6 : PowerSeries ℚ) * G + (PowerSeries.X - 4 * PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3 - 2 * PowerSeries.X ^ 4 + 4 * PowerSeries.X ^ 5 - 4 * PowerSeries.X ^ 6 + PowerSeries.X ^ 7 : PowerSeries ℚ) * G ^ 2 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hM).resolve_left hLne)).resolve_left (pow_ne_zero 2 hN1)
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    have h := congrArg PowerSeries.constantCoeff hG
    simpa using h
  cases m with
  | zero =>
    have r := A190163Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A190163Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A190163Aux.rel G hP h0c m
      push_cast
      linear_combination r
