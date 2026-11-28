import OMAStatements.S_oeis_a006605

-- Problem: A006605: Number of modes of connections of 2n points.
-- Upstream: formal-conjectures statements/oeis-a006605.lean:0 (declaration OMA.S_oeis_a006605.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A006605Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-X : ℚ⟦X⟧) * G ^ 2 + (-X ^ 2 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    (27 * X ^ 3 - 275 * X ^ 4 + 556 * X ^ 5 + 720 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (108 * X ^ 2 - 1175 * X ^ 3 + 2142 * X ^ 4 + 4320 * X ^ 5) * derivative ℚ (derivative ℚ G) + (60 * X - 828 * X ^ 2 + 888 * X ^ 3 + 4860 * X ^ 4) * derivative ℚ G + (-60 * X - 120 * X ^ 2 + 540 * X ^ 3) * G =
      0 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have hp0 : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-1 * X : ℚ⟦X⟧) * G * G + (-1 * (X * X) : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-1 * X : ℚ⟦X⟧) * G * G + (-1 * (X * X) : ℚ⟦X⟧) * G * G * G * G) =
      (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-1 : ℚ⟦X⟧) * G ^ 2 + (-4 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-2 * X : ℚ⟦X⟧) * G ^ 4 := by
    simp [Derivation.leibniz]
    ring
  have hd1 : (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-1 : ℚ⟦X⟧) * G ^ 2 + (-4 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-2 * X : ℚ⟦X⟧) * G ^ 4 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-1 : ℚ⟦X⟧) * G * G + (-4 * (X * X) : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (-2 * X : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((1 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-1 : ℚ⟦X⟧) * G * G + (-4 * (X * X) : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (-2 * X : ℚ⟦X⟧) * G * G * G * G) =
      (1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-2 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-4 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-12 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (-4 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (-16 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G ^ 4 := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hd2 : (1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-2 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-4 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-12 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (-4 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (-16 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G ^ 4 = 0 := by rw [← hL2, hp1, map_zero]
  have hp2 : (1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-2 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (-2 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-4 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-12 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (-4 * (X * X) : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) + (-16 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hd2
  have hL3 : derivative ℚ ((1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-2 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (-2 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-4 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-12 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (-4 * (X * X) : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) + (-16 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G * G * G * G) =
      (1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-6 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-6 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-6 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-24 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (-36 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-72 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (-4 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-24 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d2, d4, d12, d16]
    ring
  have hd3 : (1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-6 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-6 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-6 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-24 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (-36 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-72 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (-4 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-24 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) = 0 := by rw [← hL3, hp2, map_zero]
  have hfull : ((1 : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * G + (-4 * X ^ 2 : ℚ⟦X⟧) * G ^ 3) ^ 5 * ((27 * X ^ 3 - 275 * X ^ 4 + 556 * X ^ 5 + 720 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (108 * X ^ 2 - 1175 * X ^ 3 + 2142 * X ^ 4 + 4320 * X ^ 5) * derivative ℚ (derivative ℚ G) + (60 * X - 828 * X ^ 2 + 888 * X ^ 3 + 4860 * X ^ 4) * derivative ℚ G + (-60 * X - 120 * X ^ 2 + 540 * X ^ 3) * G - (0)) = 0 := by
    linear_combination ((60 * X + 120 * X ^ 2 - 540 * X ^ 3 : ℚ⟦X⟧) * G + (348 * X ^ 2 - 2628 * X ^ 3 + 540 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 + (336 * X ^ 2 - 2272 * X ^ 3 + 4416 * X ^ 4 : ℚ⟦X⟧) * G ^ 3 + (312 * X ^ 3 - 3944 * X ^ 4 - 8568 * X ^ 5 : ℚ⟦X⟧) * G ^ 4 + (480 * X ^ 4 + 224 * X ^ 5 + 7680 * X ^ 6 : ℚ⟦X⟧) * G ^ 5 + (1008 * X ^ 4 - 12160 * X ^ 5 + 22080 * X ^ 6 : ℚ⟦X⟧) * G ^ 6 + (-1920 * X ^ 5 + 29312 * X ^ 6 - 15360 * X ^ 7 : ℚ⟦X⟧) * G ^ 7 + (-1728 * X ^ 6 + 23360 * X ^ 7 - 15360 * X ^ 8 : ℚ⟦X⟧) * G ^ 9 + (576 * X ^ 7 - 17856 * X ^ 8 : ℚ⟦X⟧) * G ^ 10 + (384 * X ^ 8 - 11904 * X ^ 9 : ℚ⟦X⟧) * G ^ 12) * hP +
      ((60 * X - 828 * X ^ 2 + 888 * X ^ 3 + 4860 * X ^ 4 : ℚ⟦X⟧) + (378 * X ^ 3 - 4000 * X ^ 4 + 7620 * X ^ 5 + 12960 * X ^ 6 : ℚ⟦X⟧) * (derivative ℚ G) + (324 * X ^ 5 - 3300 * X ^ 6 + 6672 * X ^ 7 + 8640 * X ^ 8 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-48 * X ^ 2 + 1924 * X ^ 3 + 1464 * X ^ 4 - 21600 * X ^ 5 : ℚ⟦X⟧) * G + (-1296 * X ^ 4 + 14100 * X ^ 5 - 25704 * X ^ 6 - 51840 * X ^ 7 : ℚ⟦X⟧) * G * (derivative ℚ G) + (648 * X ^ 5 - 7896 * X ^ 6 + 26544 * X ^ 7 - 9408 * X ^ 8 - 34560 * X ^ 9 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-126 * X ^ 3 - 2272 * X ^ 4 - 9132 * X ^ 5 + 43200 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (3240 * X ^ 4 - 32928 * X ^ 5 + 54036 * X ^ 6 + 121728 * X ^ 7 + 60480 * X ^ 8 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (1296 * X ^ 7 - 13200 * X ^ 8 + 26688 * X ^ 9 + 34560 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (1416 * X ^ 3 - 12020 * X ^ 4 + 36004 * X ^ 5 + 19200 * X ^ 6 - 43200 * X ^ 7 : ℚ⟦X⟧) * G ^ 3 + (-13608 * X ^ 5 + 146016 * X ^ 6 - 273352 * X ^ 7 - 495360 * X ^ 8 - 17280 * X ^ 9 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-10368 * X ^ 7 + 105600 * X ^ 8 - 213504 * X ^ 9 - 276480 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) ^ 2 + (-4176 * X ^ 4 + 31300 * X ^ 5 - 110412 * X ^ 6 + 13440 * X ^ 7 + 17280 * X ^ 8 : ℚ⟦X⟧) * G ^ 4 + (12312 * X ^ 6 - 143400 * X ^ 7 + 233856 * X ^ 8 + 673920 * X ^ 9 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (3888 * X ^ 7 - 24048 * X ^ 8 - 78336 * X ^ 9 + 423936 * X ^ 10 + 414720 * X ^ 11 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) ^ 2 + (3816 * X ^ 5 - 20024 * X ^ 6 + 120384 * X ^ 7 - 86400 * X ^ 8 : ℚ⟦X⟧) * G ^ 5 + (-14256 * X ^ 6 + 158592 * X ^ 7 - 293760 * X ^ 8 - 518400 * X ^ 9 - 207360 * X ^ 10 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-46656 * X ^ 8 + 475200 * X ^ 9 - 960768 * X ^ 10 - 1244160 * X ^ 11 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) ^ 2 + (-3960 * X ^ 5 + 31152 * X ^ 6 - 102320 * X ^ 7 - 80448 * X ^ 8 + 69120 * X ^ 9 : ℚ⟦X⟧) * G ^ 6 + (11664 * X ^ 7 - 169200 * X ^ 8 + 185088 * X ^ 9 + 1278720 * X ^ 10 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (82944 * X ^ 9 - 844800 * X ^ 10 + 1708032 * X ^ 11 + 2211840 * X ^ 12 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) ^ 2 + (5904 * X ^ 6 - 32048 * X ^ 7 + 194688 * X ^ 8 - 34560 * X ^ 9 : ℚ⟦X⟧) * G ^ 7 + (31104 * X ^ 8 - 259200 * X ^ 9 + 703488 * X ^ 10 - 276480 * X ^ 11 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (-62208 * X ^ 9 + 633600 * X ^ 10 - 1281024 * X ^ 11 - 1658880 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) ^ 2 + (-288 * X ^ 7 - 22752 * X ^ 8 - 76416 * X ^ 9 + 138240 * X ^ 10 : ℚ⟦X⟧) * G ^ 8 + (-18144 * X ^ 8 + 141600 * X ^ 9 - 420864 * X ^ 10 + 345600 * X ^ 11 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (186624 * X ^ 10 - 1900800 * X ^ 11 + 3843072 * X ^ 12 + 4976640 * X ^ 13 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) ^ 2 + (-2400 * X ^ 7 + 36768 * X ^ 8 - 7680 * X ^ 9 - 69120 * X ^ 10 : ℚ⟦X⟧) * G ^ 9 + (100224 * X ^ 9 - 924800 * X ^ 10 + 2168832 * X ^ 11 + 829440 * X ^ 12 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (9984 * X ^ 8 - 126336 * X ^ 9 + 122112 * X ^ 10 + 276480 * X ^ 11 : ℚ⟦X⟧) * G ^ 10 + (145152 * X ^ 11 - 1478400 * X ^ 12 + 2989056 * X ^ 13 + 3870720 * X ^ 14 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) ^ 2 + (93312 * X ^ 10 - 892800 * X ^ 11 + 1984512 * X ^ 12 + 1382400 * X ^ 13 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (13632 * X ^ 9 - 146368 * X ^ 10 + 244224 * X ^ 11 + 276480 * X ^ 12 : ℚ⟦X⟧) * G ^ 12) * hd1 +
      ((108 * X ^ 2 - 1175 * X ^ 3 + 2142 * X ^ 4 + 4320 * X ^ 5 : ℚ⟦X⟧) + (162 * X ^ 4 - 1650 * X ^ 5 + 3336 * X ^ 6 + 4320 * X ^ 7 : ℚ⟦X⟧) * (derivative ℚ G) + (-702 * X ^ 3 + 7750 * X ^ 4 - 13800 * X ^ 5 - 30240 * X ^ 6 : ℚ⟦X⟧) * G + (-972 * X ^ 5 + 9900 * X ^ 6 - 20016 * X ^ 7 - 25920 * X ^ 8 : ℚ⟦X⟧) * G * (derivative ℚ G) + (1620 * X ^ 4 - 18300 * X ^ 5 + 31392 * X ^ 6 + 77760 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 + (972 * X ^ 5 - 7956 * X ^ 6 + 216 * X ^ 7 + 65952 * X ^ 8 + 51840 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-1080 * X ^ 4 + 10688 * X ^ 5 - 3128 * X ^ 6 - 80352 * X ^ 7 - 86400 * X ^ 8 : ℚ⟦X⟧) * G ^ 3 + (-7776 * X ^ 6 + 77904 * X ^ 7 - 146928 * X ^ 8 - 234048 * X ^ 9 - 34560 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (4536 * X ^ 5 - 52968 * X ^ 6 + 79936 * X ^ 7 + 266784 * X ^ 8 + 34560 * X ^ 9 : ℚ⟦X⟧) * G ^ 4 + (19440 * X ^ 7 - 198000 * X ^ 8 + 400320 * X ^ 9 + 518400 * X ^ 10 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (-5184 * X ^ 6 + 67200 * X ^ 7 - 91008 * X ^ 8 - 414720 * X ^ 9 : ℚ⟦X⟧) * G ^ 5 + (-11664 * X ^ 7 + 103248 * X ^ 8 - 81792 * X ^ 9 - 631296 * X ^ 10 - 414720 * X ^ 11 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (2592 * X ^ 6 - 32736 * X ^ 7 + 27104 * X ^ 8 + 214656 * X ^ 9 + 207360 * X ^ 10 : ℚ⟦X⟧) * G ^ 6 + (54432 * X ^ 8 - 554400 * X ^ 9 + 1120896 * X ^ 10 + 1451520 * X ^ 11 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (-2592 * X ^ 7 + 55200 * X ^ 8 - 21888 * X ^ 9 - 622080 * X ^ 10 : ℚ⟦X⟧) * G ^ 7 + (-62208 * X ^ 9 + 633600 * X ^ 10 - 1281024 * X ^ 11 - 1658880 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (-5184 * X ^ 8 + 24000 * X ^ 9 - 138240 * X ^ 10 + 414720 * X ^ 11 : ℚ⟦X⟧) * G ^ 8 + (46656 * X ^ 9 - 475200 * X ^ 10 + 960768 * X ^ 11 + 1244160 * X ^ 12 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (3456 * X ^ 8 - 16000 * X ^ 9 + 92160 * X ^ 10 - 276480 * X ^ 11 : ℚ⟦X⟧) * G ^ 9 + (-103680 * X ^ 10 + 1056000 * X ^ 11 - 2135040 * X ^ 12 - 2764800 * X ^ 13 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (-17280 * X ^ 9 + 137600 * X ^ 10 - 397824 * X ^ 11 + 276480 * X ^ 12 : ℚ⟦X⟧) * G ^ 10 + (-62208 * X ^ 11 + 633600 * X ^ 12 - 1281024 * X ^ 13 - 1658880 * X ^ 14 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (-13824 * X ^ 10 + 121600 * X ^ 11 - 305664 * X ^ 12 : ℚ⟦X⟧) * G ^ 12) * hd2 +
      ((27 * X ^ 3 - 275 * X ^ 4 + 556 * X ^ 5 + 720 * X ^ 6 : ℚ⟦X⟧) + (-216 * X ^ 4 + 2200 * X ^ 5 - 4448 * X ^ 6 - 5760 * X ^ 7 : ℚ⟦X⟧) * G + (648 * X ^ 5 - 6600 * X ^ 6 + 13344 * X ^ 7 + 17280 * X ^ 8 : ℚ⟦X⟧) * G ^ 2 + (-432 * X ^ 5 + 3536 * X ^ 6 - 96 * X ^ 7 - 29312 * X ^ 8 - 23040 * X ^ 9 : ℚ⟦X⟧) * G ^ 3 + (2592 * X ^ 6 - 25968 * X ^ 7 + 48976 * X ^ 8 + 78016 * X ^ 9 + 11520 * X ^ 10 : ℚ⟦X⟧) * G ^ 4 + (-5184 * X ^ 7 + 52800 * X ^ 8 - 106752 * X ^ 9 - 138240 * X ^ 10 : ℚ⟦X⟧) * G ^ 5 + (2592 * X ^ 7 - 22944 * X ^ 8 + 18176 * X ^ 9 + 140288 * X ^ 10 + 92160 * X ^ 11 : ℚ⟦X⟧) * G ^ 6 + (-10368 * X ^ 8 + 105600 * X ^ 9 - 213504 * X ^ 10 - 276480 * X ^ 11 : ℚ⟦X⟧) * G ^ 7 + (10368 * X ^ 9 - 105600 * X ^ 10 + 213504 * X ^ 11 + 276480 * X ^ 12 : ℚ⟦X⟧) * G ^ 8 + (-6912 * X ^ 9 + 70400 * X ^ 10 - 142336 * X ^ 11 - 184320 * X ^ 12 : ℚ⟦X⟧) * G ^ 9 + (13824 * X ^ 10 - 140800 * X ^ 11 + 284672 * X ^ 12 + 368640 * X ^ 13 : ℚ⟦X⟧) * G ^ 10 + (6912 * X ^ 11 - 70400 * X ^ 12 + 142336 * X ^ 13 + 184320 * X ^ 14 : ℚ⟦X⟧) * G ^ 12) * hd3
  have hPG : (1 : ℚ⟦X⟧) + (-2 * X : ℚ⟦X⟧) * G + (-4 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 5 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-X : ℚ⟦X⟧) * G ^ 2 + (-X ^ 2 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 27 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-275) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C 556 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C 720 +
      derivative ℚ (derivative ℚ G) * X * X * C 108 + derivative ℚ (derivative ℚ G) * X * X * X * C (-1175) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 2142 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 4320 +
      derivative ℚ G * X * C 60 + derivative ℚ G * X * X * C (-828) +
      derivative ℚ G * X * X * X * C 888 + derivative ℚ G * X * X * X * X * C 4860 +
      G * X * C (-60) + G * X * X * C (-120) +
      G * X * X * X * C 540 =
      0 := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-X : ℚ⟦X⟧) * G ^ 2 + (-X ^ 2 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) (m : ℕ) :
    27 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-275) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      556 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G + 720 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G +
      108 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-1175) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      2142 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + 4320 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      60 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-828) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      888 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 4860 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      (-60) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-120) * coeff (m + 1 + 1 + 1 + 1) G +
      540 * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-X : ℚ⟦X⟧) * G ^ 2 + (-X ^ 2 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    162 * coeff (0 + 1 + 1 + 1) G + 648 * coeff (0 + 1 + 1 + 1) G +
      (-2350) * coeff (0 + 1 + 1) G + 180 * coeff (0 + 1 + 1 + 1) G +
      (-1656) * coeff (0 + 1 + 1) G + 888 * coeff (0 + 1) G +
      (-60) * coeff (0 + 1 + 1) G + (-120) * coeff (0 + 1) G +
      540 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-X : ℚ⟦X⟧) * G ^ 2 + (-X ^ 2 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    648 * coeff (0 + 1 + 1 + 1 + 1) G + (-1650) * coeff (0 + 1 + 1 + 1) G +
      1296 * coeff (0 + 1 + 1 + 1 + 1) G + (-7050) * coeff (0 + 1 + 1 + 1) G +
      4284 * coeff (0 + 1 + 1) G + 240 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-2484) * coeff (0 + 1 + 1 + 1) G + 1776 * coeff (0 + 1 + 1) G +
      4860 * coeff (0 + 1) G + (-60) * coeff (0 + 1 + 1 + 1) G +
      (-120) * coeff (0 + 1 + 1) G + 540 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE2 (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-X : ℚ⟦X⟧) * G ^ 2 + (-X ^ 2 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    1620 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-6600) * coeff (0 + 1 + 1 + 1 + 1) G +
      3336 * coeff (0 + 1 + 1 + 1) G + 2160 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-14100) * coeff (0 + 1 + 1 + 1 + 1) G + 12852 * coeff (0 + 1 + 1 + 1) G +
      8640 * coeff (0 + 1 + 1) G + 300 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-3312) * coeff (0 + 1 + 1 + 1 + 1) G + 2664 * coeff (0 + 1 + 1 + 1) G +
      9720 * coeff (0 + 1 + 1) G + (-60) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-120) * coeff (0 + 1 + 1 + 1) G + 540 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A006605Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a006605.main := by
  intro G hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  have e3 : m + 1 + 1 + 1 - 3 = m := rfl
  rw [e1, e2, e3]
  have hP : (-1 : PowerSeries ℚ) + (1 : PowerSeries ℚ) * G + (-PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (-PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 4 = 0 := by
    linear_combination hG
  have h0c : PowerSeries.constantCoeff G = (1 : ℚ) := by
    have h := congrArg PowerSeries.constantCoeff hG
    simpa using h
  cases m with
  | zero =>
    have r := A006605Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A006605Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A006605Aux.relE2 G hP h0c
        push_cast
        linear_combination r
      | succ m =>
        have r := A006605Aux.rel G hP h0c m
        push_cast
        linear_combination r
