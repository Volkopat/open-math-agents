import OMAStatements.S_oeis_a187259

-- Problem: A187259: Number of UH^jU's, DH^jD's, and DH^jU's for some j>0, in all peakless Motzkin paths of length n (here U=(1,1), D=(1,-1) and H=(1,0); can be easily expressed using RNA secondary structure terminology).
-- Upstream: formal-conjectures statements/oeis-a187259.lean:0 (declaration OMA.S_oeis_a187259.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A187259Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (-6 * X ^ 6 - 3 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧) + (3 - 15 * X + 23 * X ^ 2 - 17 * X ^ 3 + 23 * X ^ 4 - 25 * X ^ 5 + 14 * X ^ 6 - 8 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧) * G + (X - 4 * X ^ 2 + 4 * X ^ 3 - 2 * X ^ 4 + 4 * X ^ 5 - 4 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (-42968 * X ^ 2 - 33354 * X ^ 3 + 587317 * X ^ 4 - 549823 * X ^ 5 + 176865 * X ^ 6 - 587317 * X ^ 7 + 592791 * X ^ 8 - 143511 * X ^ 9) * derivative ℚ (derivative ℚ G) + (102055 * X + 788000 * X ^ 2 - 2659668 * X ^ 3 + 1872053 * X ^ 4 - 929642 * X ^ 5 - 14116 * X ^ 6 + 855950 * X ^ 7 - 384922 * X ^ 8) * derivative ℚ G + (187991 + 1042699 * X - 2694921 * X ^ 2 + 1193176 * X ^ 3 + 913280 * X ^ 4 - 456912 * X ^ 5 - 471028 * X ^ 6 + 384922 * X ^ 7) * G =
      -977438 * X ^ 6 - 384922 * X ^ 7 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d7 : derivative ℚ (7 : ℚ⟦X⟧) = 0 := dnum 7
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d14 : derivative ℚ (14 : ℚ⟦X⟧) = 0 := dnum 14
  have d15 : derivative ℚ (15 : ℚ⟦X⟧) = 0 := dnum 15
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d17 : derivative ℚ (17 : ℚ⟦X⟧) = 0 := dnum 17
  have d20 : derivative ℚ (20 : ℚ⟦X⟧) = 0 := dnum 20
  have d21 : derivative ℚ (21 : ℚ⟦X⟧) = 0 := dnum 21
  have d23 : derivative ℚ (23 : ℚ⟦X⟧) = 0 := dnum 23
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have d25 : derivative ℚ (25 : ℚ⟦X⟧) = 0 := dnum 25
  have d36 : derivative ℚ (36 : ℚ⟦X⟧) = 0 := dnum 36
  have d46 : derivative ℚ (46 : ℚ⟦X⟧) = 0 := dnum 46
  have d51 : derivative ℚ (51 : ℚ⟦X⟧) = 0 := dnum 51
  have d56 : derivative ℚ (56 : ℚ⟦X⟧) = 0 := dnum 56
  have d84 : derivative ℚ (84 : ℚ⟦X⟧) = 0 := dnum 84
  have d92 : derivative ℚ (92 : ℚ⟦X⟧) = 0 := dnum 92
  have d125 : derivative ℚ (125 : ℚ⟦X⟧) = 0 := dnum 125
  have hp0 : (-6 * (X * X * X * X * X * X) - 3 * (X * X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) + (3 - 15 * X + 23 * (X * X) - 17 * (X * X * X) + 23 * (X * X * X * X) - 25 * (X * X * X * X * X) + 14 * (X * X * X * X * X * X) - 8 * (X * X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (1 * X - 4 * (X * X) + 4 * (X * X * X) - 2 * (X * X * X * X) + 4 * (X * X * X * X * X) - 4 * (X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-6 * (X * X * X * X * X * X) - 3 * (X * X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) + (3 - 15 * X + 23 * (X * X) - 17 * (X * X * X) + 23 * (X * X * X * X) - 25 * (X * X * X * X * X) + 14 * (X * X * X * X * X * X) - 8 * (X * X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (1 * X - 4 * (X * X) + 4 * (X * X * X) - 2 * (X * X * X * X) + 4 * (X * X * X * X * X) - 4 * (X * X * X * X * X * X) + 1 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * G) =
      (-36 * X ^ 5 - 21 * X ^ 6 + 16 * X ^ 7 : ℚ⟦X⟧) + (3 - 15 * X + 23 * X ^ 2 - 17 * X ^ 3 + 23 * X ^ 4 - 25 * X ^ 5 + 14 * X ^ 6 - 8 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧) * (derivative ℚ G) + (-15 + 46 * X - 51 * X ^ 2 + 92 * X ^ 3 - 125 * X ^ 4 + 84 * X ^ 5 - 56 * X ^ 6 + 16 * X ^ 7 : ℚ⟦X⟧) * G + (2 * X - 8 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 8 * X ^ 6 + 2 * X ^ 7 : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 - 8 * X + 12 * X ^ 2 - 8 * X ^ 3 + 20 * X ^ 4 - 24 * X ^ 5 + 7 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 := by
    simp [Derivation.leibniz, d2, d3, d4, d6, d8, d14, d15, d17, d23, d25]
    ring
  have hd1 : (-36 * X ^ 5 - 21 * X ^ 6 + 16 * X ^ 7 : ℚ⟦X⟧) + (3 - 15 * X + 23 * X ^ 2 - 17 * X ^ 3 + 23 * X ^ 4 - 25 * X ^ 5 + 14 * X ^ 6 - 8 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧) * (derivative ℚ G) + (-15 + 46 * X - 51 * X ^ 2 + 92 * X ^ 3 - 125 * X ^ 4 + 84 * X ^ 5 - 56 * X ^ 6 + 16 * X ^ 7 : ℚ⟦X⟧) * G + (2 * X - 8 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 8 * X ^ 6 + 2 * X ^ 7 : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 - 8 * X + 12 * X ^ 2 - 8 * X ^ 3 + 20 * X ^ 4 - 24 * X ^ 5 + 7 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (-36 * (X * X * X * X * X) - 21 * (X * X * X * X * X * X) + 16 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (3 - 15 * X + 23 * (X * X) - 17 * (X * X * X) + 23 * (X * X * X * X) - 25 * (X * X * X * X * X) + 14 * (X * X * X * X * X * X) - 8 * (X * X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (-15 + 46 * X - 51 * (X * X) + 92 * (X * X * X) - 125 * (X * X * X * X) + 84 * (X * X * X * X * X) - 56 * (X * X * X * X * X * X) + 16 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (2 * X - 8 * (X * X) + 8 * (X * X * X) - 4 * (X * X * X * X) + 8 * (X * X * X * X * X) - 8 * (X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 - 8 * X + 12 * (X * X) - 8 * (X * X * X) + 20 * (X * X * X * X) - 24 * (X * X * X * X * X) + 7 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((-36 * (X * X * X * X * X) - 21 * (X * X * X * X * X * X) + 16 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (3 - 15 * X + 23 * (X * X) - 17 * (X * X * X) + 23 * (X * X * X * X) - 25 * (X * X * X * X * X) + 14 * (X * X * X * X * X * X) - 8 * (X * X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (-15 + 46 * X - 51 * (X * X) + 92 * (X * X * X) - 125 * (X * X * X * X) + 84 * (X * X * X * X * X) - 56 * (X * X * X * X * X * X) + 16 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (2 * X - 8 * (X * X) + 8 * (X * X * X) - 4 * (X * X * X * X) + 8 * (X * X * X * X * X) - 8 * (X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (1 - 8 * X + 12 * (X * X) - 8 * (X * X * X) + 20 * (X * X * X * X) - 24 * (X * X * X * X * X) + 7 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * G) =
      (-180 * X ^ 4 - 126 * X ^ 5 + 112 * X ^ 6 : ℚ⟦X⟧) + (3 - 15 * X + 23 * X ^ 2 - 17 * X ^ 3 + 23 * X ^ 4 - 25 * X ^ 5 + 14 * X ^ 6 - 8 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-30 + 92 * X - 102 * X ^ 2 + 184 * X ^ 3 - 250 * X ^ 4 + 168 * X ^ 5 - 112 * X ^ 6 + 32 * X ^ 7 : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X - 8 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 8 * X ^ 6 + 2 * X ^ 7 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (46 - 102 * X + 276 * X ^ 2 - 500 * X ^ 3 + 420 * X ^ 4 - 336 * X ^ 5 + 112 * X ^ 6 : ℚ⟦X⟧) * G + (2 * X - 8 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 8 * X ^ 6 + 2 * X ^ 7 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (4 - 32 * X + 48 * X ^ 2 - 32 * X ^ 3 + 80 * X ^ 4 - 96 * X ^ 5 + 28 * X ^ 6 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-8 + 24 * X - 24 * X ^ 2 + 80 * X ^ 3 - 120 * X ^ 4 + 42 * X ^ 5 : ℚ⟦X⟧) * G ^ 2 := by
    simp [Derivation.leibniz, d2, d3, d4, d7, d8, d12, d14, d15, d16, d17, d20, d21, d23, d24, d25, d36, d46, d51, d56, d84, d92, d125]
    ring
  have hd2 : (-180 * X ^ 4 - 126 * X ^ 5 + 112 * X ^ 6 : ℚ⟦X⟧) + (3 - 15 * X + 23 * X ^ 2 - 17 * X ^ 3 + 23 * X ^ 4 - 25 * X ^ 5 + 14 * X ^ 6 - 8 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-30 + 92 * X - 102 * X ^ 2 + 184 * X ^ 3 - 250 * X ^ 4 + 168 * X ^ 5 - 112 * X ^ 6 + 32 * X ^ 7 : ℚ⟦X⟧) * (derivative ℚ G) + (2 * X - 8 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 8 * X ^ 6 + 2 * X ^ 7 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (46 - 102 * X + 276 * X ^ 2 - 500 * X ^ 3 + 420 * X ^ 4 - 336 * X ^ 5 + 112 * X ^ 6 : ℚ⟦X⟧) * G + (2 * X - 8 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 8 * X ^ 6 + 2 * X ^ 7 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (4 - 32 * X + 48 * X ^ 2 - 32 * X ^ 3 + 80 * X ^ 4 - 96 * X ^ 5 + 28 * X ^ 6 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-8 + 24 * X - 24 * X ^ 2 + 80 * X ^ 3 - 120 * X ^ 4 + 42 * X ^ 5 : ℚ⟦X⟧) * G ^ 2 = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((3 - 15 * X + 23 * X ^ 2 - 17 * X ^ 3 + 23 * X ^ 4 - 25 * X ^ 5 + 14 * X ^ 6 - 8 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧) + (2 * X - 8 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 8 * X ^ 6 + 2 * X ^ 7 : ℚ⟦X⟧) * G) ^ 3 * ((-42968 * X ^ 2 - 33354 * X ^ 3 + 587317 * X ^ 4 - 549823 * X ^ 5 + 176865 * X ^ 6 - 587317 * X ^ 7 + 592791 * X ^ 8 - 143511 * X ^ 9) * derivative ℚ (derivative ℚ G) + (102055 * X + 788000 * X ^ 2 - 2659668 * X ^ 3 + 1872053 * X ^ 4 - 929642 * X ^ 5 - 14116 * X ^ 6 + 855950 * X ^ 7 - 384922 * X ^ 8) * derivative ℚ G + (187991 + 1042699 * X - 2694921 * X ^ 2 + 1193176 * X ^ 3 + 913280 * X ^ 4 - 456912 * X ^ 5 - 471028 * X ^ 6 + 384922 * X ^ 7) * G - (-977438 * X ^ 6 - 384922 * X ^ 7)) = 0 := by
    linear_combination ((1691919 - 2942424 * X - 64848447 * X ^ 2 + 263793723 * X ^ 3 + 139168947 * X ^ 4 - 2991865875 * X ^ 5 + 9321668897 * X ^ 6 - 19553519797 * X ^ 7 + 35466004485 * X ^ 8 - 55657168023 * X ^ 9 + 75654416311 * X ^ 10 - 93937335501 * X ^ 11 + 106502438190 * X ^ 12 - 108007685337 * X ^ 13 + 100527590960 * X ^ 14 - 86711954554 * X ^ 15 + 66951783886 * X ^ 16 - 45786247276 * X ^ 17 + 28342316374 * X ^ 18 - 15544994734 * X ^ 19 + 6814175630 * X ^ 20 - 2062786526 * X ^ 21 + 363773148 * X ^ 22 - 27473976 * X ^ 23 : ℚ⟦X⟧) + (2513700 * X - 693792 * X ^ 2 - 94858110 * X ^ 3 + 253604028 * X ^ 4 + 514402014 * X ^ 5 - 3651097624 * X ^ 6 + 9016679650 * X ^ 7 - 16498517024 * X ^ 8 + 26779085792 * X ^ 9 - 37162320580 * X ^ 10 + 44726136532 * X ^ 11 - 49504441464 * X ^ 12 + 49236324576 * X ^ 13 - 42845809032 * X ^ 14 + 33882809722 * X ^ 15 - 24343958740 * X ^ 16 + 14939429246 * X ^ 17 - 7544001440 * X ^ 18 + 3005607754 * X ^ 19 - 834947944 * X ^ 20 + 132503124 * X ^ 21 - 8450388 * X ^ 22 : ℚ⟦X⟧) * G + (837900 * X ^ 2 + 606636 * X ^ 3 - 30733434 * X ^ 4 + 54841354 * X ^ 5 + 217508750 * X ^ 6 - 1010532238 * X ^ 7 + 2093083018 * X ^ 8 - 3500205530 * X ^ 9 + 5356379708 * X ^ 10 - 6872183676 * X ^ 11 + 7647394860 * X ^ 12 - 7963027356 * X ^ 13 + 7307814944 * X ^ 14 - 5671466504 * X ^ 15 + 4052711710 * X ^ 16 - 2650645102 * X ^ 17 + 1310386982 * X ^ 18 - 404798390 * X ^ 19 + 66251562 * X ^ 20 - 4225194 * X ^ 21 : ℚ⟦X⟧) * G ^ 2) * hP +
      ((918495 * X - 5960070 * X ^ 2 - 29618139 * X ^ 3 + 436416603 * X ^ 4 - 1999120269 * X ^ 5 + 5250610513 * X ^ 6 - 9958087409 * X ^ 7 + 16611120301 * X ^ 8 - 25836507581 * X ^ 9 + 35262914523 * X ^ 10 - 42544925063 * X ^ 11 + 48072169033 * X ^ 12 - 50382207232 * X ^ 13 + 47603500523 * X ^ 14 - 41295018586 * X ^ 15 + 33153381672 * X ^ 16 - 24081020248 * X ^ 17 + 15651861682 * X ^ 18 - 9046291778 * X ^ 19 + 4512079778 * X ^ 20 - 1821141938 * X ^ 21 + 532955126 * X ^ 22 - 95674952 * X ^ 23 + 7645016 * X ^ 24 : ℚ⟦X⟧) + (257808 * X ^ 3 - 2120148 * X ^ 4 + 2838902 * X ^ 5 + 26312516 * X ^ 6 - 134680162 * X ^ 7 + 312072624 * X ^ 8 - 511874718 * X ^ 9 + 802963512 * X ^ 10 - 1200628504 * X ^ 11 + 1490553452 * X ^ 12 - 1616425852 * X ^ 13 + 1708024264 * X ^ 14 - 1667978372 * X ^ 15 + 1410100324 * X ^ 16 - 1083611538 * X ^ 17 + 779259876 * X ^ 18 - 496655442 * X ^ 19 + 268267768 * X ^ 20 - 117104606 * X ^ 21 + 36817768 * X ^ 22 - 6963516 * X ^ 23 + 574044 * X ^ 24 : ℚ⟦X⟧) * (derivative ℚ G) + (1740276 * X ^ 2 - 9157740 * X ^ 3 - 51616460 * X ^ 4 + 589542350 * X ^ 5 - 2257365102 * X ^ 6 + 4983608320 * X ^ 7 - 8201106640 * X ^ 8 + 12659578194 * X ^ 9 - 18475580822 * X ^ 10 + 22886046998 * X ^ 11 - 24941691186 * X ^ 12 + 26156083362 * X ^ 13 - 25382578386 * X ^ 14 + 21578621514 * X ^ 15 - 16676601454 * X ^ 16 + 11962838524 * X ^ 17 - 7628710296 * X ^ 18 + 4178933270 * X ^ 19 - 1866032714 * X ^ 20 + 598724616 * X ^ 21 - 114826216 * X ^ 22 + 9549592 * X ^ 23 : ℚ⟦X⟧) * G + (171872 * X ^ 4 - 1241560 * X ^ 5 + 708332 * X ^ 6 + 18008028 * X ^ 7 - 72612324 * X ^ 8 + 141077412 * X ^ 9 - 206729836 * X ^ 10 + 320639324 * X ^ 11 - 462577864 * X ^ 12 + 517386136 * X ^ 13 - 514402472 * X ^ 14 + 534185800 * X ^ 15 - 494437752 * X ^ 16 + 364118112 * X ^ 17 - 248489316 * X ^ 18 + 172565068 * X ^ 19 - 97075124 * X ^ 20 + 35095636 * X ^ 21 - 6963516 * X ^ 22 + 574044 * X ^ 23 : ℚ⟦X⟧) * G * (derivative ℚ G) + (666028 * X ^ 3 - 3007332 * X ^ 4 - 19607998 * X ^ 5 + 185538662 * X ^ 6 - 612965534 * X ^ 7 + 1160863938 * X ^ 8 - 1712020646 * X ^ 9 + 2582477886 * X ^ 10 - 3634156060 * X ^ 11 + 4070101036 * X ^ 12 - 4044054908 * X ^ 13 + 4133364532 * X ^ 14 - 3803556272 * X ^ 15 + 2812062728 * X ^ 16 - 1909676646 * X ^ 17 + 1313202542 * X ^ 18 - 739000614 * X ^ 19 + 269212234 * X ^ 20 - 53931350 * X ^ 21 + 4487774 * X ^ 22 : ℚ⟦X⟧) * G ^ 2) * hd1 +
      ((-386712 * X ^ 2 + 3566934 * X ^ 3 - 7309671 * X ^ 4 - 35883783 * X ^ 5 + 240114958 * X ^ 6 - 655508078 * X ^ 7 + 1209514549 * X ^ 8 - 1977307659 * X ^ 9 + 3056472975 * X ^ 10 - 4096080945 * X ^ 11 + 4803810205 * X ^ 12 - 5298685703 * X ^ 13 + 5434333951 * X ^ 14 - 5009201767 * X ^ 15 + 4222519148 * X ^ 16 - 3275283976 * X ^ 17 + 2301190677 * X ^ 18 - 1454048715 * X ^ 19 + 802326816 * X ^ 20 - 369136864 * X ^ 21 + 137134088 * X ^ 22 - 38539900 * X ^ 23 + 6963516 * X ^ 24 - 574044 * X ^ 25 : ℚ⟦X⟧) + (-515616 * X ^ 3 + 4240296 * X ^ 4 - 5677804 * X ^ 5 - 52625032 * X ^ 6 + 269360324 * X ^ 7 - 624145248 * X ^ 8 + 1023749436 * X ^ 9 - 1605927024 * X ^ 10 + 2401257008 * X ^ 11 - 2981106904 * X ^ 12 + 3232851704 * X ^ 13 - 3416048528 * X ^ 14 + 3335956744 * X ^ 15 - 2820200648 * X ^ 16 + 2167223076 * X ^ 17 - 1558519752 * X ^ 18 + 993310884 * X ^ 19 - 536535536 * X ^ 20 + 234209212 * X ^ 21 - 73635536 * X ^ 22 + 13927032 * X ^ 23 - 1148088 * X ^ 24 : ℚ⟦X⟧) * G + (-171872 * X ^ 4 + 1241560 * X ^ 5 - 708332 * X ^ 6 - 18008028 * X ^ 7 + 72612324 * X ^ 8 - 141077412 * X ^ 9 + 206729836 * X ^ 10 - 320639324 * X ^ 11 + 462577864 * X ^ 12 - 517386136 * X ^ 13 + 514402472 * X ^ 14 - 534185800 * X ^ 15 + 494437752 * X ^ 16 - 364118112 * X ^ 17 + 248489316 * X ^ 18 - 172565068 * X ^ 19 + 97075124 * X ^ 20 - 35095636 * X ^ 21 + 6963516 * X ^ 22 - 574044 * X ^ 23 : ℚ⟦X⟧) * G ^ 2) * hd2
  have k3 : constantCoeff (3 : ℚ⟦X⟧) = 3 := cnum 3
  have hPG : (3 - 15 * X + 23 * X ^ 2 - 17 * X ^ 3 + 23 * X ^ 4 - 25 * X ^ 5 + 14 * X ^ 6 - 8 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧) + (2 * X - 8 * X ^ 2 + 8 * X ^ 3 - 4 * X ^ 4 + 8 * X ^ 5 - 8 * X ^ 6 + 2 * X ^ 7 : ℚ⟦X⟧) * G ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k3] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (-6 * X ^ 6 - 3 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧) + (3 - 15 * X + 23 * X ^ 2 - 17 * X ^ 3 + 23 * X ^ 4 - 25 * X ^ 5 + 14 * X ^ 6 - 8 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧) * G + (X - 4 * X ^ 2 + 4 * X ^ 3 - 2 * X ^ 4 + 4 * X ^ 5 - 4 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C (-42968) + derivative ℚ (derivative ℚ G) * X * X * X * C (-33354) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 587317 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-549823) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 176865 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C (-587317) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * C 592791 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * X * C (-143511) +
      derivative ℚ G * X * C 102055 + derivative ℚ G * X * X * C 788000 +
      derivative ℚ G * X * X * X * C (-2659668) + derivative ℚ G * X * X * X * X * C 1872053 +
      derivative ℚ G * X * X * X * X * X * C (-929642) + derivative ℚ G * X * X * X * X * X * X * C (-14116) +
      derivative ℚ G * X * X * X * X * X * X * X * C 855950 + derivative ℚ G * X * X * X * X * X * X * X * X * C (-384922) +
      G * C 187991 + G * X * C 1042699 +
      G * X * X * C (-2694921) + G * X * X * X * C 1193176 +
      G * X * X * X * X * C 913280 + G * X * X * X * X * X * C (-456912) +
      G * X * X * X * X * X * X * C (-471028) + G * X * X * X * X * X * X * X * C 384922 =
      C (-977438) * X * X * X * X * X * X + C (-384922) * X * X * X * X * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (-6 * X ^ 6 - 3 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧) + (3 - 15 * X + 23 * X ^ 2 - 17 * X ^ 3 + 23 * X ^ 4 - 25 * X ^ 5 + 14 * X ^ 6 - 8 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧) * G + (X - 4 * X ^ 2 + 4 * X ^ 3 - 2 * X ^ 4 + 4 * X ^ 5 - 4 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    (-42968) * ((m : ℚ) + 9) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-33354) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      587317 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-549823) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      176865 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-587317) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      592791 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + (-143511) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      102055 * ((m : ℚ) + 9) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 788000 * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-2659668) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 1872053 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-929642) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-14116) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      855950 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-384922) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      187991 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 1042699 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-2694921) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 1193176 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      913280 * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-456912) * coeff (m + 1 + 1 + 1 + 1) G +
      (-471028) * coeff (m + 1 + 1 + 1) G + 384922 * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (-6 * X ^ 6 - 3 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧) + (3 - 15 * X + 23 * X ^ 2 - 17 * X ^ 3 + 23 * X ^ 4 - 25 * X ^ 5 + 14 * X ^ 6 - 8 * X ^ 7 + 2 * X ^ 8 : ℚ⟦X⟧) * G + (X - 4 * X ^ 2 + 4 * X ^ 3 - 2 * X ^ 4 + 4 * X ^ 5 - 4 * X ^ 6 + X ^ 7 : ℚ⟦X⟧) * G ^ 2 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (-2406208) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-1400868) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      17619510 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-10996460) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      2122380 * coeff (0 + 1 + 1 + 1 + 1) G + (-3523902) * coeff (0 + 1 + 1 + 1) G +
      1185582 * coeff (0 + 1 + 1) G + 816440 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      5516000 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-15958008) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      9360265 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-3718568) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-42348) * coeff (0 + 1 + 1 + 1) G + 1711900 * coeff (0 + 1 + 1) G +
      (-384922) * coeff (0 + 1) G + 187991 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      1042699 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-2694921) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      1193176 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 913280 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-456912) * coeff (0 + 1 + 1 + 1) G + (-471028) * coeff (0 + 1 + 1) G +
      384922 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A187259Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a187259.main := by
  intro T G hT hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 8, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 + 1 := rfl
  have e7 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 = m + 1 := rfl
  rw [e1, e2, e3, e4, e5, e6, e7]
  have hN1 : ((1) + (-1) * PowerSeries.X + (-1) * PowerSeries.X ^ 2 * T ^ 2 + (1) * PowerSeries.X ^ 3 * T ^ 2 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [] at h'
  have hM : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 14) * (((1) + (-1) * PowerSeries.X + (-1) * PowerSeries.X ^ 2 * T ^ 2 + (1) * PowerSeries.X ^ 3 * T ^ 2) ^ 2 * ((-6 * PowerSeries.X ^ 6 - 3 * PowerSeries.X ^ 7 + 2 * PowerSeries.X ^ 8 : PowerSeries ℚ) + (3 - 15 * PowerSeries.X + 23 * PowerSeries.X ^ 2 - 17 * PowerSeries.X ^ 3 + 23 * PowerSeries.X ^ 4 - 25 * PowerSeries.X ^ 5 + 14 * PowerSeries.X ^ 6 - 8 * PowerSeries.X ^ 7 + 2 * PowerSeries.X ^ 8 : PowerSeries ℚ) * G + (PowerSeries.X - 4 * PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3 - 2 * PowerSeries.X ^ 4 + 4 * PowerSeries.X ^ 5 - 4 * PowerSeries.X ^ 6 + PowerSeries.X ^ 7 : PowerSeries ℚ) * G ^ 2)) = 0 := by
    linear_combination ((3) * PowerSeries.X ^ 19 * T ^ 2 + (-9) * PowerSeries.X ^ 19 * T ^ 3 + (-6) * PowerSeries.X ^ 20 + (-6) * PowerSeries.X ^ 20 * T + (-24) * PowerSeries.X ^ 20 * T ^ 2 + (45) * PowerSeries.X ^ 20 * T ^ 3 + (9) * PowerSeries.X ^ 21 + (15) * PowerSeries.X ^ 21 * T + (59) * PowerSeries.X ^ 21 * T ^ 2 + (-66) * PowerSeries.X ^ 21 * T ^ 3 + (-12) * PowerSeries.X ^ 21 * T ^ 4 + (9) * PowerSeries.X ^ 21 * T ^ 5 + (2) * PowerSeries.X ^ 22 + (-13) * PowerSeries.X ^ 22 * T + (-56) * PowerSeries.X ^ 22 * T ^ 2 + (27) * PowerSeries.X ^ 22 * T ^ 3 + (60) * PowerSeries.X ^ 22 * T ^ 4 + (-45) * PowerSeries.X ^ 22 * T ^ 5 + (-7) * PowerSeries.X ^ 23 + (41) * PowerSeries.X ^ 23 * T ^ 2 + (-19) * PowerSeries.X ^ 23 * T ^ 3 + (-89) * PowerSeries.X ^ 23 * T ^ 4 + (57) * PowerSeries.X ^ 23 * T ^ 5 + (9) * PowerSeries.X ^ 23 * T ^ 6 + (2) * PowerSeries.X ^ 24 + (11) * PowerSeries.X ^ 24 * T + (-56) * PowerSeries.X ^ 24 * T ^ 2 + (52) * PowerSeries.X ^ 24 * T ^ 3 + (44) * PowerSeries.X ^ 24 * T ^ 4 + (6) * PowerSeries.X ^ 24 * T ^ 5 + (-36) * PowerSeries.X ^ 24 * T ^ 6 + (-9) * PowerSeries.X ^ 25 * T + (40) * PowerSeries.X ^ 25 * T ^ 2 + (-19) * PowerSeries.X ^ 25 * T ^ 3 + (-44) * PowerSeries.X ^ 25 * T ^ 4 + (-6) * PowerSeries.X ^ 25 * T ^ 5 + (36) * PowerSeries.X ^ 25 * T ^ 6 + (2) * PowerSeries.X ^ 26 * T + (-6) * PowerSeries.X ^ 26 * T ^ 2 + (-25) * PowerSeries.X ^ 26 * T ^ 3 + (82) * PowerSeries.X ^ 26 * T ^ 4 + (-42) * PowerSeries.X ^ 26 * T ^ 5 + (-18) * PowerSeries.X ^ 26 * T ^ 6 + (-1) * PowerSeries.X ^ 27 * T ^ 2 + (14) * PowerSeries.X ^ 27 * T ^ 3 + (-32) * PowerSeries.X ^ 27 * T ^ 4 + (-15) * PowerSeries.X ^ 27 * T ^ 5 + (36) * PowerSeries.X ^ 27 * T ^ 6 + (1) * PowerSeries.X ^ 28 * T ^ 3 + (-16) * PowerSeries.X ^ 28 * T ^ 4 + (51) * PowerSeries.X ^ 28 * T ^ 5 + (-36) * PowerSeries.X ^ 28 * T ^ 6 + (-1) * PowerSeries.X ^ 29 * T ^ 3 + (7) * PowerSeries.X ^ 29 * T ^ 4 + (-15) * PowerSeries.X ^ 29 * T ^ 5 + (9) * PowerSeries.X ^ 29 * T ^ 6) * hT +
      ((-3) * PowerSeries.X ^ 14 + (18) * PowerSeries.X ^ 15 + (-1) * PowerSeries.X ^ 15 * G + (-38) * PowerSeries.X ^ 16 + (3) * PowerSeries.X ^ 16 * T ^ 2 + (5) * PowerSeries.X ^ 16 * G + (40) * PowerSeries.X ^ 17 + (-18) * PowerSeries.X ^ 17 * T ^ 2 + (-8) * PowerSeries.X ^ 17 * G + (1) * PowerSeries.X ^ 17 * G * T ^ 2 + (-40) * PowerSeries.X ^ 18 + (38) * PowerSeries.X ^ 18 * T ^ 2 + (6) * PowerSeries.X ^ 18 * G + (-5) * PowerSeries.X ^ 18 * G * T ^ 2 + (48) * PowerSeries.X ^ 19 + (-40) * PowerSeries.X ^ 19 * T ^ 2 + (-6) * PowerSeries.X ^ 19 * G + (8) * PowerSeries.X ^ 19 * G * T ^ 2 + (-39) * PowerSeries.X ^ 20 + (39) * PowerSeries.X ^ 20 * T ^ 2 + (4) * PowerSeries.X ^ 20 * T ^ 3 + (-3) * PowerSeries.X ^ 20 * T ^ 4 + (8) * PowerSeries.X ^ 20 * G + (-6) * PowerSeries.X ^ 20 * G * T ^ 2 + (22) * PowerSeries.X ^ 21 + (-44) * PowerSeries.X ^ 21 * T ^ 2 + (-16) * PowerSeries.X ^ 21 * T ^ 3 + (12) * PowerSeries.X ^ 21 * T ^ 4 + (-5) * PowerSeries.X ^ 21 * G + (6) * PowerSeries.X ^ 21 * G * T ^ 2 + (-10) * PowerSeries.X ^ 22 + (35) * PowerSeries.X ^ 22 * T ^ 2 + (16) * PowerSeries.X ^ 22 * T ^ 3 + (-12) * PowerSeries.X ^ 22 * T ^ 4 + (1) * PowerSeries.X ^ 22 * G + (-8) * PowerSeries.X ^ 22 * G * T ^ 2 + (2) * PowerSeries.X ^ 23 + (-20) * PowerSeries.X ^ 23 * T ^ 2 + (-8) * PowerSeries.X ^ 23 * T ^ 3 + (6) * PowerSeries.X ^ 23 * T ^ 4 + (5) * PowerSeries.X ^ 23 * G * T ^ 2 + (6) * PowerSeries.X ^ 24 * T ^ 2 + (16) * PowerSeries.X ^ 24 * T ^ 3 + (-12) * PowerSeries.X ^ 24 * T ^ 4 + (-1) * PowerSeries.X ^ 24 * G * T ^ 2 + (2) * PowerSeries.X ^ 25 * T ^ 2 + (-16) * PowerSeries.X ^ 25 * T ^ 3 + (12) * PowerSeries.X ^ 25 * T ^ 4 + (-1) * PowerSeries.X ^ 26 * T ^ 2 + (4) * PowerSeries.X ^ 26 * T ^ 3 + (-3) * PowerSeries.X ^ 26 * T ^ 4) * hG
  have hLne : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 14) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero 14 PowerSeries.X_ne_zero)
  have hP : (-6 * PowerSeries.X ^ 6 - 3 * PowerSeries.X ^ 7 + 2 * PowerSeries.X ^ 8 : PowerSeries ℚ) + (3 - 15 * PowerSeries.X + 23 * PowerSeries.X ^ 2 - 17 * PowerSeries.X ^ 3 + 23 * PowerSeries.X ^ 4 - 25 * PowerSeries.X ^ 5 + 14 * PowerSeries.X ^ 6 - 8 * PowerSeries.X ^ 7 + 2 * PowerSeries.X ^ 8 : PowerSeries ℚ) * G + (PowerSeries.X - 4 * PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3 - 2 * PowerSeries.X ^ 4 + 4 * PowerSeries.X ^ 5 - 4 * PowerSeries.X ^ 6 + PowerSeries.X ^ 7 : PowerSeries ℚ) * G ^ 2 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hM).resolve_left hLne)).resolve_left (pow_ne_zero 2 hN1)
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    have h := congrArg PowerSeries.constantCoeff hG
    simpa using h
  cases m with
  | zero =>
    have r := A187259Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    have r := A187259Aux.rel G hP h0c m
    push_cast
    linear_combination r
