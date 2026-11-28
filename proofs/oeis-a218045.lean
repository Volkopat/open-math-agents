import OMAStatements.S_oeis_a218045

-- Problem: A218045: Number of truth tables of bracketed formulas (case 3).
-- Upstream: formal-conjectures statements/oeis-a218045.lean:0 (declaration OMA.S_oeis_a218045.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A218045Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (X ^ 4 : ℚ⟦X⟧) + (-X ^ 2 : ℚ⟦X⟧) * G + (2 * X + 2 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (-1 : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0) :
    (2 * X ^ 3 - 22 * X ^ 4 - 24 * X ^ 5 + 512 * X ^ 6 + 512 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (X ^ 2 - 32 * X ^ 3 + 120 * X ^ 4 + 448 * X ^ 5 + 1024 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-2 * X ^ 2 - 48 * X ^ 3 + 96 * X ^ 4 - 128 * X ^ 5) * derivative ℚ G + (8 * X ^ 2 - 128 * X ^ 3 + 128 * X ^ 4) * G =
      2 * X ^ 2 - 32 * X ^ 3 + 32 * X ^ 4 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have hp0 : (1 * (X * X * X * X) : ℚ⟦X⟧) + (-1 * (X * X) : ℚ⟦X⟧) * G + (2 * X + 2 * (X * X) : ℚ⟦X⟧) * G * G + (-1 : ℚ⟦X⟧) * G * G * G + (1 : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 * (X * X * X * X) : ℚ⟦X⟧) + (-1 * (X * X) : ℚ⟦X⟧) * G + (2 * X + 2 * (X * X) : ℚ⟦X⟧) * G * G + (-1 : ℚ⟦X⟧) * G * G * G + (1 : ℚ⟦X⟧) * G * G * G * G) =
      (4 * X ^ 3 : ℚ⟦X⟧) + (-X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 * X : ℚ⟦X⟧) * G + (4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 + 4 * X : ℚ⟦X⟧) * G ^ 2 + (-3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d2]
    ring
  have hd1 : (4 * X ^ 3 : ℚ⟦X⟧) + (-X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 * X : ℚ⟦X⟧) * G + (4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 + 4 * X : ℚ⟦X⟧) * G ^ 2 + (-3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (4 * (X * X * X) : ℚ⟦X⟧) + (-1 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (-2 * X : ℚ⟦X⟧) * G + (4 * X + 4 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 + 4 * X : ℚ⟦X⟧) * G * G + (-3 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((4 * (X * X * X) : ℚ⟦X⟧) + (-1 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (-2 * X : ℚ⟦X⟧) * G + (4 * X + 4 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 + 4 * X : ℚ⟦X⟧) * G * G + (-3 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G)) =
      (12 * X ^ 2 : ℚ⟦X⟧) + (-X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 : ℚ⟦X⟧) * G + (4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 + 16 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 2 + (-3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d2, d3, d4]
    ring
  have hd2 : (12 * X ^ 2 : ℚ⟦X⟧) + (-X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 : ℚ⟦X⟧) * G + (4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 + 16 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 2 + (-3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) = 0 := by rw [← hL2, hp1, map_zero]
  have hp2 : (12 * (X * X) : ℚ⟦X⟧) + (-1 * (X * X) : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (4 * X + 4 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G + (4 * X + 4 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 + 16 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G + (-3 : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) = 0 := by linear_combination hd2
  have hL3 : derivative ℚ ((12 * (X * X) : ℚ⟦X⟧) + (-1 * (X * X) : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (4 * X + 4 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G + (4 * X + 4 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 + 16 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G + (-3 : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G))) =
      (24 * X : ℚ⟦X⟧) + (-X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-6 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-6 : ℚ⟦X⟧) * (derivative ℚ G) + (12 * X + 12 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (12 + 24 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-6 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (12 + 24 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-18 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (-3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) := by
    simp [Derivation.leibniz, d2, d3, d4, d6, d8, d12, d16]
    ring
  have hd3 : (24 * X : ℚ⟦X⟧) + (-X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-6 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-6 : ℚ⟦X⟧) * (derivative ℚ G) + (12 * X + 12 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (12 + 24 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-6 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (12 + 24 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-18 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (-3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) = 0 := by rw [← hL3, hp2, map_zero]
  have hfull : ((-X ^ 2 : ℚ⟦X⟧) + (4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G + (-3 : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3) ^ 5 * ((2 * X ^ 3 - 22 * X ^ 4 - 24 * X ^ 5 + 512 * X ^ 6 + 512 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (X ^ 2 - 32 * X ^ 3 + 120 * X ^ 4 + 448 * X ^ 5 + 1024 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-2 * X ^ 2 - 48 * X ^ 3 + 96 * X ^ 4 - 128 * X ^ 5) * derivative ℚ G + (8 * X ^ 2 - 128 * X ^ 3 + 128 * X ^ 4) * G - (2 * X ^ 2 - 32 * X ^ 3 + 32 * X ^ 4)) = 0 := by
    linear_combination ((-42 * X ^ 8 + 1080 * X ^ 9 - 10176 * X ^ 10 + 16896 * X ^ 11 + 341504 * X ^ 12 - 960512 * X ^ 13 - 4415488 * X ^ 14 - 4718592 * X ^ 15 - 1572864 * X ^ 16 : ℚ⟦X⟧) + (60 * X ^ 7 + 672 * X ^ 8 - 6528 * X ^ 9 - 127488 * X ^ 10 - 47104 * X ^ 11 + 5197824 * X ^ 12 + 8749056 * X ^ 13 + 3670016 * X ^ 14 : ℚ⟦X⟧) * G + (234 * X ^ 6 - 16392 * X ^ 7 + 161376 * X ^ 8 + 218112 * X ^ 9 - 2728960 * X ^ 10 - 8605696 * X ^ 11 - 15605760 * X ^ 12 - 16973824 * X ^ 13 - 7340032 * X ^ 14 : ℚ⟦X⟧) * G ^ 2 + (-696 * X ^ 5 + 31328 * X ^ 6 - 273152 * X ^ 7 - 510976 * X ^ 8 + 4552704 * X ^ 9 + 14262272 * X ^ 10 + 22773760 * X ^ 11 + 13500416 * X ^ 12 : ℚ⟦X⟧) * G ^ 3 + (714 * X ^ 4 - 16216 * X ^ 5 + 94944 * X ^ 6 + 695040 * X ^ 7 - 1000960 * X ^ 8 - 15202304 * X ^ 9 - 23617536 * X ^ 10 - 22118400 * X ^ 11 - 13500416 * X ^ 12 : ℚ⟦X⟧) * G ^ 4 + (-324 * X ^ 3 - 6112 * X ^ 4 + 33152 * X ^ 5 + 75264 * X ^ 6 - 1696768 * X ^ 7 + 806912 * X ^ 8 + 19218432 * X ^ 9 + 18087936 * X ^ 10 : ℚ⟦X⟧) * G ^ 5 + (54 * X ^ 2 + 5928 * X ^ 3 + 16160 * X ^ 4 - 289280 * X ^ 5 - 255488 * X ^ 6 + 83968 * X ^ 7 - 3375104 * X ^ 8 - 12419072 * X ^ 9 - 12058624 * X ^ 10 : ℚ⟦X⟧) * G ^ 6 + (-288 * X ^ 2 - 44288 * X ^ 3 + 178176 * X ^ 4 + 929792 * X ^ 5 + 1220608 * X ^ 6 + 6094848 * X ^ 7 + 9961472 * X ^ 8 : ℚ⟦X⟧) * G ^ 7 + (3936 * X ^ 2 + 88320 * X ^ 3 - 821248 * X ^ 4 - 1589248 * X ^ 5 - 1597440 * X ^ 6 - 2916352 * X ^ 7 - 4980736 * X ^ 8 : ℚ⟦X⟧) * G ^ 8 + (-16384 * X ^ 2 + 74752 * X ^ 3 + 901120 * X ^ 4 + 1294336 * X ^ 5 + 1310720 * X ^ 6 : ℚ⟦X⟧) * G ^ 9 + (29184 * X ^ 2 - 382976 * X ^ 3 - 24576 * X ^ 4 - 491520 * X ^ 5 - 524288 * X ^ 6 : ℚ⟦X⟧) * G ^ 10 + (-24576 * X ^ 2 + 393216 * X ^ 3 - 393216 * X ^ 4 : ℚ⟦X⟧) * G ^ 11 + (8192 * X ^ 2 - 131072 * X ^ 3 + 131072 * X ^ 4 : ℚ⟦X⟧) * G ^ 12) * hP +
      ((32 * X ^ 9 - 446 * X ^ 10 + 1904 * X ^ 11 + 576 * X ^ 12 - 82304 * X ^ 13 + 240128 * X ^ 14 + 1103872 * X ^ 15 + 1179648 * X ^ 16 + 393216 * X ^ 17 : ℚ⟦X⟧) + (-116 * X ^ 9 + 1436 * X ^ 10 - 80 * X ^ 11 - 39392 * X ^ 12 + 23168 * X ^ 13 + 257536 * X ^ 14 + 294912 * X ^ 15 + 98304 * X ^ 16 : ℚ⟦X⟧) * (derivative ℚ G) + (84 * X ^ 9 - 732 * X ^ 10 - 3024 * X ^ 11 + 18144 * X ^ 12 + 69504 * X ^ 13 + 73728 * X ^ 14 + 24576 * X ^ 15 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-192 * X ^ 8 + 80 * X ^ 9 + 17056 * X ^ 10 + 26880 * X ^ 11 - 215808 * X ^ 12 - 1900544 * X ^ 13 - 2777088 * X ^ 14 - 1114112 * X ^ 15 : ℚ⟦X⟧) * G + (1146 * X ^ 8 - 11952 * X ^ 9 - 17856 * X ^ 10 + 319488 * X ^ 11 + 204672 * X ^ 12 - 1227264 * X ^ 13 - 2291712 * X ^ 14 - 1572864 * X ^ 15 - 393216 * X ^ 16 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-912 * X ^ 8 + 7632 * X ^ 9 + 35040 * X ^ 10 - 180096 * X ^ 11 - 811776 * X ^ 12 - 1195008 * X ^ 13 - 786432 * X ^ 14 - 196608 * X ^ 15 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (636 * X ^ 7 + 6684 * X ^ 8 - 129520 * X ^ 9 - 135232 * X ^ 10 + 2044672 * X ^ 11 + 5675520 * X ^ 12 + 7430144 * X ^ 13 + 6012928 * X ^ 14 + 2228224 * X ^ 15 : ℚ⟦X⟧) * G ^ 2 + (-4644 * X ^ 7 + 39384 * X ^ 8 + 142032 * X ^ 9 - 1005312 * X ^ 10 - 2185728 * X ^ 11 - 250368 * X ^ 12 + 1609728 * X ^ 13 + 786432 * X ^ 14 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (3948 * X ^ 7 - 32676 * X ^ 8 - 154128 * X ^ 9 + 761088 * X ^ 10 + 3558912 * X ^ 11 + 5611008 * X ^ 12 + 4503552 * X ^ 13 + 1966080 * X ^ 14 + 393216 * X ^ 15 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (-1412 * X ^ 6 - 17248 * X ^ 7 + 289824 * X ^ 8 + 469504 * X ^ 9 - 4134400 * X ^ 10 - 12029952 * X ^ 11 - 13688832 * X ^ 12 - 5996544 * X ^ 13 : ℚ⟦X⟧) * G ^ 3 + (9914 * X ^ 6 - 64112 * X ^ 7 - 456688 * X ^ 8 + 1576192 * X ^ 9 + 7631360 * X ^ 10 + 9306112 * X ^ 11 + 2889728 * X ^ 12 - 1753088 * X ^ 13 - 1048576 * X ^ 14 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-8736 * X ^ 6 + 71712 * X ^ 7 + 348480 * X ^ 8 - 1682688 * X ^ 9 - 8082432 * X ^ 10 - 12423168 * X ^ 11 - 8650752 * X ^ 12 - 2359296 * X ^ 13 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) ^ 2 + (1848 * X ^ 5 + 17288 * X ^ 6 - 284752 * X ^ 7 - 840704 * X ^ 8 + 2269440 * X ^ 9 + 13600256 * X ^ 10 + 19984384 * X ^ 11 + 14934016 * X ^ 12 + 5996544 * X ^ 13 : ℚ⟦X⟧) * G ^ 4 + (-11628 * X ^ 5 + 47160 * X ^ 6 + 733200 * X ^ 7 - 1056768 * X ^ 8 - 12211968 * X ^ 9 - 20646912 * X ^ 10 - 12263424 * X ^ 11 - 1966080 * X ^ 12 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (10476 * X ^ 5 - 78948 * X ^ 6 - 479376 * X ^ 7 + 1773504 * X ^ 8 + 11130624 * X ^ 9 + 20505600 * X ^ 10 + 18616320 * X ^ 11 + 9437184 * X ^ 12 + 2359296 * X ^ 13 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) ^ 2 + (-1128 * X ^ 4 - 9632 * X ^ 5 + 133952 * X ^ 6 + 790144 * X ^ 7 + 1543168 * X ^ 8 - 5343232 * X ^ 9 - 16400384 * X ^ 10 - 10420224 * X ^ 11 : ℚ⟦X⟧) * G ^ 5 + (6894 * X ^ 4 + 3072 * X ^ 5 - 603216 * X ^ 6 - 534528 * X ^ 7 + 9435648 * X ^ 8 + 25580544 * X ^ 9 + 26505216 * X ^ 10 + 12091392 * X ^ 11 + 1572864 * X ^ 12 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-6480 * X ^ 4 + 30096 * X ^ 5 + 463968 * X ^ 6 - 466560 * X ^ 7 - 10994688 * X ^ 8 - 27205632 * X ^ 9 - 26542080 * X ^ 10 - 9437184 * X ^ 11 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) ^ 2 + (108 * X ^ 3 + 6628 * X ^ 4 - 43152 * X ^ 5 - 548480 * X ^ 6 - 2003456 * X ^ 7 - 1058816 * X ^ 8 + 5042176 * X ^ 9 + 11108352 * X ^ 10 + 6946816 * X ^ 11 : ℚ⟦X⟧) * G ^ 6 + (-1404 * X ^ 3 - 27768 * X ^ 4 + 222960 * X ^ 5 + 1462464 * X ^ 6 - 3174912 * X ^ 7 - 19663872 * X ^ 8 - 22708224 * X ^ 9 - 6881280 * X ^ 10 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (1620 * X ^ 3 + 13284 * X ^ 4 - 297840 * X ^ 5 - 610560 * X ^ 6 + 7096320 * X ^ 7 + 23420928 * X ^ 8 + 28606464 * X ^ 9 + 18874368 * X ^ 10 + 6291456 * X ^ 11 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) ^ 2 + (108 * X ^ 2 - 2832 * X ^ 3 + 17824 * X ^ 4 + 217088 * X ^ 5 + 1020928 * X ^ 6 + 2707456 * X ^ 7 - 2916352 * X ^ 8 - 5636096 * X ^ 9 : ℚ⟦X⟧) * G ^ 7 + (-162 * X ^ 2 + 11808 * X ^ 3 + 16368 * X ^ 4 - 792576 * X ^ 5 - 993024 * X ^ 6 + 5173248 * X ^ 7 + 14635008 * X ^ 8 + 14155776 * X ^ 9 + 3932160 * X ^ 10 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (-10368 * X ^ 3 + 63360 * X ^ 4 + 626688 * X ^ 5 - 1437696 * X ^ 6 - 14966784 * X ^ 7 - 27131904 * X ^ 8 - 14155776 * X ^ 9 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) ^ 2 + (-522 * X ^ 2 + 6368 * X ^ 3 - 127552 * X ^ 4 - 301952 * X ^ 5 - 400896 * X ^ 6 - 1693696 * X ^ 7 + 1097728 * X ^ 8 + 2818048 * X ^ 9 : ℚ⟦X⟧) * G ^ 8 + (972 * X ^ 2 - 40704 * X ^ 3 + 88032 * X ^ 4 + 1392768 * X ^ 5 + 597504 * X ^ 6 - 3858432 * X ^ 7 - 2064384 * X ^ 8 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (25056 * X ^ 3 - 247968 * X ^ 4 - 577152 * X ^ 5 + 5778432 * X ^ 6 + 13160448 * X ^ 7 + 14155776 * X ^ 8 + 7077888 * X ^ 9 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) ^ 2 + (1248 * X ^ 2 + 9856 * X ^ 3 + 142080 * X ^ 4 + 251904 * X ^ 5 - 253952 * X ^ 6 : ℚ⟦X⟧) * G ^ 9 + (-2160 * X ^ 2 + 73472 * X ^ 3 - 242048 * X ^ 4 - 1427968 * X ^ 5 - 2062336 * X ^ 6 + 1540096 * X ^ 7 + 917504 * X ^ 8 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (-26880 * X ^ 3 + 295680 * X ^ 4 + 322560 * X ^ 5 - 6881280 * X ^ 6 - 6881280 * X ^ 7 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) ^ 2 + (-1856 * X ^ 2 - 38144 * X ^ 3 + 7680 * X ^ 4 - 167936 * X ^ 5 + 114688 * X ^ 6 : ℚ⟦X⟧) * G ^ 10 + (2112 * X ^ 2 - 67584 * X ^ 3 + 253440 * X ^ 4 + 946176 * X ^ 5 + 2162688 * X ^ 6 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (10752 * X ^ 3 - 118272 * X ^ 4 - 129024 * X ^ 5 + 2752512 * X ^ 6 + 2752512 * X ^ 7 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) ^ 2 + (1536 * X ^ 2 + 36864 * X ^ 3 - 73728 * X ^ 4 + 98304 * X ^ 5 : ℚ⟦X⟧) * G ^ 11 + (-768 * X ^ 2 + 24576 * X ^ 3 - 92160 * X ^ 4 - 344064 * X ^ 5 - 786432 * X ^ 6 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (-512 * X ^ 2 - 12288 * X ^ 3 + 24576 * X ^ 4 - 32768 * X ^ 5 : ℚ⟦X⟧) * G ^ 12) * hd1 +
      ((-11 * X ^ 10 + 100 * X ^ 11 + 264 * X ^ 12 - 2624 * X ^ 13 - 2048 * X ^ 14 : ℚ⟦X⟧) + (24 * X ^ 10 - 240 * X ^ 11 - 552 * X ^ 12 + 5856 * X ^ 13 + 12288 * X ^ 14 + 6144 * X ^ 15 : ℚ⟦X⟧) * (derivative ℚ G) + (152 * X ^ 9 - 1160 * X ^ 10 - 5536 * X ^ 11 + 31616 * X ^ 12 + 68608 * X ^ 13 + 32768 * X ^ 14 : ℚ⟦X⟧) * G + (-324 * X ^ 9 + 2988 * X ^ 10 + 9936 * X ^ 11 - 72864 * X ^ 12 - 226944 * X ^ 13 - 221184 * X ^ 14 - 73728 * X ^ 15 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-864 * X ^ 8 + 5412 * X ^ 9 + 39600 * X ^ 10 - 143616 * X ^ 11 - 542976 * X ^ 12 - 571392 * X ^ 13 - 196608 * X ^ 14 : ℚ⟦X⟧) * G ^ 2 + (1800 * X ^ 8 - 15624 * X ^ 9 - 64080 * X ^ 10 + 373824 * X ^ 11 + 1475712 * X ^ 12 + 1939968 * X ^ 13 + 1179648 * X ^ 14 + 294912 * X ^ 15 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (2600 * X ^ 7 - 12776 * X ^ 8 - 138880 * X ^ 9 + 315904 * X ^ 10 + 1866240 * X ^ 11 + 2840576 * X ^ 12 + 1949696 * X ^ 13 + 524288 * X ^ 14 : ℚ⟦X⟧) * G ^ 3 + (-5316 * X ^ 7 + 44268 * X ^ 8 + 206256 * X ^ 9 - 1044480 * X ^ 10 - 4766208 * X ^ 11 - 7085568 * X ^ 12 - 5093376 * X ^ 13 - 1966080 * X ^ 14 - 393216 * X ^ 15 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-4430 * X ^ 6 + 14732 * X ^ 7 + 271264 * X ^ 8 - 322048 * X ^ 9 - 3331328 * X ^ 10 - 6120448 * X ^ 11 - 5175296 * X ^ 12 - 2375680 * X ^ 13 - 524288 * X ^ 14 : ℚ⟦X⟧) * G ^ 4 + (9000 * X ^ 6 - 71640 * X ^ 7 - 380160 * X ^ 8 + 1670400 * X ^ 9 + 8835840 * X ^ 10 + 14238720 * X ^ 11 + 10321920 * X ^ 12 + 2949120 * X ^ 13 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (4200 * X ^ 5 - 2760 * X ^ 6 - 307872 * X ^ 7 - 37248 * X ^ 8 + 3213312 * X ^ 9 + 7170048 * X ^ 10 + 6291456 * X ^ 11 + 1966080 * X ^ 12 : ℚ⟦X⟧) * G ^ 5 + (-8748 * X ^ 5 + 61092 * X ^ 6 + 444816 * X ^ 7 - 1332288 * X ^ 8 - 10379520 * X ^ 9 - 20505600 * X ^ 10 - 18911232 * X ^ 11 - 9437184 * X ^ 12 - 2359296 * X ^ 13 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-1944 * X ^ 4 - 12692 * X ^ 5 + 194032 * X ^ 6 + 524544 * X ^ 7 - 1357312 * X ^ 8 - 5426176 * X ^ 9 - 6942720 * X ^ 10 - 4653056 * X ^ 11 - 1310720 * X ^ 12 : ℚ⟦X⟧) * G ^ 6 + (4536 * X ^ 4 - 16632 * X ^ 5 - 363888 * X ^ 6 + 173376 * X ^ 7 + 8644608 * X ^ 8 + 22579200 * X ^ 9 + 22708224 * X ^ 10 + 8257536 * X ^ 11 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (216 * X ^ 3 + 13032 * X ^ 4 - 43968 * X ^ 5 - 600576 * X ^ 6 - 302592 * X ^ 7 + 2383872 * X ^ 8 + 4030464 * X ^ 9 + 1572864 * X ^ 10 : ℚ⟦X⟧) * G ^ 7 + (-972 * X ^ 3 - 10044 * X ^ 4 + 193680 * X ^ 5 + 470016 * X ^ 6 - 4617216 * X ^ 7 - 16459776 * X ^ 8 - 21012480 * X ^ 9 - 14155776 * X ^ 10 - 4718592 * X ^ 11 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (81 * X ^ 2 - 3456 * X ^ 3 - 24744 * X ^ 4 + 267840 * X ^ 5 + 838656 * X ^ 6 + 463872 * X ^ 7 - 884736 * X ^ 8 - 2064384 * X ^ 9 - 786432 * X ^ 10 : ℚ⟦X⟧) * G ^ 8 + (5832 * X ^ 3 - 33048 * X ^ 4 - 377568 * X ^ 5 + 739584 * X ^ 6 + 9040896 * X ^ 7 + 16809984 * X ^ 8 + 8847360 * X ^ 9 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (-432 * X ^ 2 + 14976 * X ^ 3 - 11008 * X ^ 4 - 514048 * X ^ 5 - 989184 * X ^ 6 - 655360 * X ^ 7 - 655360 * X ^ 8 : ℚ⟦X⟧) * G ^ 9 + (-12960 * X ^ 3 + 127200 * X ^ 4 + 309120 * X ^ 5 - 2964480 * X ^ 6 - 7065600 * X ^ 7 - 7864320 * X ^ 8 - 3932160 * X ^ 9 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (864 * X ^ 2 - 28160 * X ^ 3 + 85760 * X ^ 4 + 529408 * X ^ 5 + 1110016 * X ^ 6 + 327680 * X ^ 7 + 262144 * X ^ 8 : ℚ⟦X⟧) * G ^ 10 + (12672 * X ^ 3 - 139392 * X ^ 4 - 152064 * X ^ 5 + 3244032 * X ^ 6 + 3244032 * X ^ 7 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (-768 * X ^ 2 + 24576 * X ^ 3 - 92160 * X ^ 4 - 344064 * X ^ 5 - 786432 * X ^ 6 : ℚ⟦X⟧) * G ^ 11 + (-4608 * X ^ 3 + 50688 * X ^ 4 + 55296 * X ^ 5 - 1179648 * X ^ 6 - 1179648 * X ^ 7 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (256 * X ^ 2 - 8192 * X ^ 3 + 30720 * X ^ 4 + 114688 * X ^ 5 + 262144 * X ^ 6 : ℚ⟦X⟧) * G ^ 12) * hd2 +
      ((2 * X ^ 11 - 22 * X ^ 12 - 24 * X ^ 13 + 512 * X ^ 14 + 512 * X ^ 15 : ℚ⟦X⟧) + (-32 * X ^ 10 + 320 * X ^ 11 + 736 * X ^ 12 - 7808 * X ^ 13 - 16384 * X ^ 14 - 8192 * X ^ 15 : ℚ⟦X⟧) * G + (216 * X ^ 9 - 1992 * X ^ 10 - 6624 * X ^ 11 + 48576 * X ^ 12 + 151296 * X ^ 13 + 147456 * X ^ 14 + 49152 * X ^ 15 : ℚ⟦X⟧) * G ^ 2 + (-800 * X ^ 8 + 6944 * X ^ 9 + 28480 * X ^ 10 - 166144 * X ^ 11 - 655872 * X ^ 12 - 862208 * X ^ 13 - 524288 * X ^ 14 - 131072 * X ^ 15 : ℚ⟦X⟧) * G ^ 3 + (1772 * X ^ 7 - 14756 * X ^ 8 - 68752 * X ^ 9 + 348160 * X ^ 10 + 1588736 * X ^ 11 + 2361856 * X ^ 12 + 1697792 * X ^ 13 + 655360 * X ^ 14 + 131072 * X ^ 15 : ℚ⟦X⟧) * G ^ 4 + (-2400 * X ^ 6 + 19104 * X ^ 7 + 101376 * X ^ 8 - 445440 * X ^ 9 - 2356224 * X ^ 10 - 3796992 * X ^ 11 - 2752512 * X ^ 12 - 786432 * X ^ 13 : ℚ⟦X⟧) * G ^ 5 + (1944 * X ^ 5 - 13576 * X ^ 6 - 98848 * X ^ 7 + 296064 * X ^ 8 + 2306560 * X ^ 9 + 4556800 * X ^ 10 + 4202496 * X ^ 11 + 2097152 * X ^ 12 + 524288 * X ^ 13 : ℚ⟦X⟧) * G ^ 6 + (-864 * X ^ 4 + 3168 * X ^ 5 + 69312 * X ^ 6 - 33024 * X ^ 7 - 1646592 * X ^ 8 - 4300800 * X ^ 9 - 4325376 * X ^ 10 - 1572864 * X ^ 11 : ℚ⟦X⟧) * G ^ 7 + (162 * X ^ 3 + 1674 * X ^ 4 - 32280 * X ^ 5 - 78336 * X ^ 6 + 769536 * X ^ 7 + 2743296 * X ^ 8 + 3502080 * X ^ 9 + 2359296 * X ^ 10 + 786432 * X ^ 11 : ℚ⟦X⟧) * G ^ 8 + (-864 * X ^ 3 + 4896 * X ^ 4 + 55936 * X ^ 5 - 109568 * X ^ 6 - 1339392 * X ^ 7 - 2490368 * X ^ 8 - 1310720 * X ^ 9 : ℚ⟦X⟧) * G ^ 9 + (1728 * X ^ 3 - 16960 * X ^ 4 - 41216 * X ^ 5 + 395264 * X ^ 6 + 942080 * X ^ 7 + 1048576 * X ^ 8 + 524288 * X ^ 9 : ℚ⟦X⟧) * G ^ 10 + (-1536 * X ^ 3 + 16896 * X ^ 4 + 18432 * X ^ 5 - 393216 * X ^ 6 - 393216 * X ^ 7 : ℚ⟦X⟧) * G ^ 11 + (512 * X ^ 3 - 5632 * X ^ 4 - 6144 * X ^ 5 + 131072 * X ^ 6 + 131072 * X ^ 7 : ℚ⟦X⟧) * G ^ 12) * hd3
  have hres : ((9437184 * X ^ 3 + 6291456 * X ^ 4 : ℚ⟦X⟧) + (-1048576 * X - 30408704 * X ^ 2 - 37748736 * X ^ 3 - 8388608 * X ^ 4 : ℚ⟦X⟧) * G + (1048576 + 11534336 * X + 10485760 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (-1048576 - 12582912 * X - 8388608 * X ^ 2 : ℚ⟦X⟧) * G ^ 3) * ((-X ^ 2 : ℚ⟦X⟧) + (4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G + (-3 : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3) = (-8388608 * X ^ 5 + 58720256 * X ^ 6 + 67108864 * X ^ 7 : ℚ⟦X⟧) := by
    linear_combination (-((1048576 * X + 65011712 * X ^ 2 + 67108864 * X ^ 3 : ℚ⟦X⟧) + (-3145728 - 33554432 * X - 33554432 * X ^ 2 : ℚ⟦X⟧) * G + (4194304 + 50331648 * X + 33554432 * X ^ 2 : ℚ⟦X⟧) * G ^ 2)) * hP
  have hd0 : (-8388608 + 58720256 * X + 67108864 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    have kc : constantCoeff (8388608 : ℚ⟦X⟧) = 8388608 := cnum 8388608
    simp [kc] at h'
  have hdisc : (-8388608 * X ^ 5 + 58720256 * X ^ 6 + 67108864 * X ^ 7 : ℚ⟦X⟧) ≠ 0 := by
    have e : (-8388608 * X ^ 5 + 58720256 * X ^ 6 + 67108864 * X ^ 7 : ℚ⟦X⟧) = X ^ 5 * (-8388608 + 58720256 * X + 67108864 * X ^ 2 : ℚ⟦X⟧) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 5 X_ne_zero) hd0
  have hPG : (-X ^ 2 : ℚ⟦X⟧) + (4 * X + 4 * X ^ 2 : ℚ⟦X⟧) * G + (-3 : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hres
    exact hdisc hres.symm
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 5 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (X ^ 4 : ℚ⟦X⟧) + (-X ^ 2 : ℚ⟦X⟧) * G + (2 * X + 2 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (-1 : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 2 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-22) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C (-24) + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C 512 +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * C 512 + derivative ℚ (derivative ℚ G) * X * X * C 1 +
      derivative ℚ (derivative ℚ G) * X * X * X * C (-32) + derivative ℚ (derivative ℚ G) * X * X * X * X * C 120 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 448 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 1024 +
      derivative ℚ G * X * X * C (-2) + derivative ℚ G * X * X * X * C (-48) +
      derivative ℚ G * X * X * X * X * C 96 + derivative ℚ G * X * X * X * X * X * C (-128) +
      G * X * X * C 8 + G * X * X * X * C (-128) +
      G * X * X * X * X * C 128 =
      C 2 * X * X + C (-32) * X * X * X +
      C 32 * X * X * X * X := by
  have h := key G hP
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (X ^ 4 : ℚ⟦X⟧) + (-X ^ 2 : ℚ⟦X⟧) * G + (2 * X + 2 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (-1 : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0) (m : ℕ) :
    2 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-22) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-24) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 512 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      512 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + 1 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-32) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 120 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      448 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + 1024 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-2) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-48) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      96 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + (-128) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      8 * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-128) * coeff (m + 1 + 1 + 1 + 1) G +
      128 * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (X ^ 4 : ℚ⟦X⟧) + (-X ^ 2 : ℚ⟦X⟧) * G + (2 * X + 2 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (-1 : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0) :
    120 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-528) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-144) * coeff (0 + 1 + 1 + 1) G + 20 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-384) * coeff (0 + 1 + 1 + 1 + 1) G + 720 * coeff (0 + 1 + 1 + 1) G +
      896 * coeff (0 + 1 + 1) G + (-8) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-144) * coeff (0 + 1 + 1 + 1) G + 192 * coeff (0 + 1 + 1) G +
      (-128) * coeff (0 + 1) G + 8 * coeff (0 + 1 + 1 + 1) G +
      (-128) * coeff (0 + 1 + 1) G + 128 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (X ^ 4 : ℚ⟦X⟧) + (-X ^ 2 : ℚ⟦X⟧) * G + (2 * X + 2 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (-1 : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0) :
    240 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-1320) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-576) * coeff (0 + 1 + 1 + 1 + 1) G + 3072 * coeff (0 + 1 + 1 + 1) G +
      30 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-640) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      1440 * coeff (0 + 1 + 1 + 1 + 1) G + 2688 * coeff (0 + 1 + 1 + 1) G +
      2048 * coeff (0 + 1 + 1) G + (-10) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-192) * coeff (0 + 1 + 1 + 1 + 1) G + 288 * coeff (0 + 1 + 1 + 1) G +
      (-256) * coeff (0 + 1 + 1) G + 8 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-128) * coeff (0 + 1 + 1 + 1) G + 128 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A218045Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a218045.main := by
  intro T W G hT _ hW _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  rw [e1, e2, e3, e4]
  have kn8 : PowerSeries.constantCoeff (8 : PowerSeries ℚ) = 8 := A218045Aux.cnum 8
  have hN1 : ((8) : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [kn8] at h'
  have hM : ((8)) ^ 4 * ((PowerSeries.X ^ 4 : PowerSeries ℚ) + (-PowerSeries.X ^ 2 : PowerSeries ℚ) * G + (2 * PowerSeries.X + 2 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (-1 : PowerSeries ℚ) * G ^ 3 + (1 : PowerSeries ℚ) * G ^ 4) = 0 := by
    linear_combination ((92) + (-64) * W + (248) * T + (-144) * T * W + (224) * T ^ 2 + (-96) * T ^ 2 * W + (72) * T ^ 3 + (-16) * T ^ 3 * W + (4) * T ^ 4 + (128) * PowerSeries.X + (416) * PowerSeries.X * T + (-64) * PowerSeries.X * T * W + (320) * PowerSeries.X * T ^ 2 + (-64) * PowerSeries.X * T ^ 2 * W + (32) * PowerSeries.X * T ^ 3 + (192) * PowerSeries.X ^ 2 + (256) * PowerSeries.X ^ 2 * T + (64) * PowerSeries.X ^ 2 * T ^ 2 + (512) * PowerSeries.X ^ 3) * hT +
      ((-22) + (1) * W ^ 2 + (-38) * T + (-8) * T * W + (4) * T * W ^ 2 + (20) * T ^ 2 + (-24) * T ^ 2 * W + (6) * T ^ 2 * W ^ 2 + (68) * T ^ 3 + (-24) * T ^ 3 * W + (4) * T ^ 3 * W ^ 2 + (34) * T ^ 4 + (-8) * T ^ 4 * W + (1) * T ^ 4 * W ^ 2 + (2) * T ^ 5 + (136) * PowerSeries.X + (288) * PowerSeries.X * T + (176) * PowerSeries.X * T ^ 2 + (32) * PowerSeries.X * T ^ 3 + (8) * PowerSeries.X * T ^ 4 + (128) * PowerSeries.X ^ 2 + (256) * PowerSeries.X ^ 2 * T + (128) * PowerSeries.X ^ 2 * T ^ 2) * hW +
      ((-24) + (20) * W + (-2) * W ^ 2 + (-1) * W ^ 3 + (-40) * T + (28) * T * W + (2) * T * W ^ 2 + (-3) * T * W ^ 3 + (-8) * T ^ 2 + (-4) * T ^ 2 * W + (10) * T ^ 2 * W ^ 2 + (-3) * T ^ 2 * W ^ 3 + (8) * T ^ 3 + (-12) * T ^ 3 * W + (6) * T ^ 3 * W ^ 2 + (-1) * T ^ 3 * W ^ 3 + (-96) * G + (32) * G * W + (8) * G * W ^ 2 + (-64) * G * T + (16) * G * T * W ^ 2 + (32) * G * T ^ 2 + (-32) * G * T ^ 2 * W + (8) * G * T ^ 2 * W ^ 2 + (-384) * G ^ 2 + (-64) * G ^ 2 * W + (128) * G ^ 2 * T + (-64) * G ^ 2 * T * W + (512) * G ^ 3 + (256) * PowerSeries.X + (-128) * PowerSeries.X * W + (256) * PowerSeries.X * T + (-128) * PowerSeries.X * T * W + (1024) * PowerSeries.X * G + (-256) * PowerSeries.X ^ 2 + (-128) * PowerSeries.X ^ 2 * W + (256) * PowerSeries.X ^ 2 * T + (-128) * PowerSeries.X ^ 2 * T * W + (1024) * PowerSeries.X ^ 2 * G) * hG
  have hP : (PowerSeries.X ^ 4 : PowerSeries ℚ) + (-PowerSeries.X ^ 2 : PowerSeries ℚ) * G + (2 * PowerSeries.X + 2 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (-1 : PowerSeries ℚ) * G ^ 3 + (1 : PowerSeries ℚ) * G ^ 4 = 0 := (mul_eq_zero.mp hM).resolve_left (pow_ne_zero 4 hN1)
  cases m with
  | zero =>
    have r := A218045Aux.relE0 G hP
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A218045Aux.relE1 G hP
      push_cast
      linear_combination r
    | succ m =>
      have r := A218045Aux.rel G hP m
      push_cast
      linear_combination r
