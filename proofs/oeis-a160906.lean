import OMAStatements.S_oeis_a160906

-- Problem: A160906: Row sums of A159841.
-- Upstream: formal-conjectures statements/oeis-a160906.lean:0 (declaration OMA.S_oeis_a160906.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A160906Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (5 : ℚ⟦X⟧) * G + (-8 + 54 * X : ℚ⟦X⟧) * G ^ 2 + (4 - 59 * X + 216 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    (20 * X ^ 3 - 295 * X ^ 4 + 1080 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (34 * X ^ 2 - 1319 * X ^ 3 + 7776 * X ^ 4) * derivative ℚ (derivative ℚ G) + (2 * X - 842 * X ^ 2 + 11328 * X ^ 3) * derivative ℚ G + (2 * X + 2112 * X ^ 2) * G =
      12 * X := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d5 : derivative ℚ (5 : ℚ⟦X⟧) = 0 := dnum 5
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have d54 : derivative ℚ (54 : ℚ⟦X⟧) = 0 := dnum 54
  have d59 : derivative ℚ (59 : ℚ⟦X⟧) = 0 := dnum 59
  have d108 : derivative ℚ (108 : ℚ⟦X⟧) = 0 := dnum 108
  have d177 : derivative ℚ (177 : ℚ⟦X⟧) = 0 := dnum 177
  have d216 : derivative ℚ (216 : ℚ⟦X⟧) = 0 := dnum 216
  have d354 : derivative ℚ (354 : ℚ⟦X⟧) = 0 := dnum 354
  have d432 : derivative ℚ (432 : ℚ⟦X⟧) = 0 := dnum 432
  have d648 : derivative ℚ (648 : ℚ⟦X⟧) = 0 := dnum 648
  have d1296 : derivative ℚ (1296 : ℚ⟦X⟧) = 0 := dnum 1296
  have d2592 : derivative ℚ (2592 : ℚ⟦X⟧) = 0 := dnum 2592
  have hp0 : (-1 : ℚ⟦X⟧) + (5 : ℚ⟦X⟧) * G + (-8 + 54 * X : ℚ⟦X⟧) * G * G + (4 - 59 * X + 216 * (X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-1 : ℚ⟦X⟧) + (5 : ℚ⟦X⟧) * G + (-8 + 54 * X : ℚ⟦X⟧) * G * G + (4 - 59 * X + 216 * (X * X) : ℚ⟦X⟧) * G * G * G) =
      (5 : ℚ⟦X⟧) * (derivative ℚ G) + (-16 + 108 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (54 : ℚ⟦X⟧) * G ^ 2 + (12 - 177 * X + 648 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-59 + 432 * X : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d4, d5, d8, d54, d59, d216]
    ring
  have hd1 : (5 : ℚ⟦X⟧) * (derivative ℚ G) + (-16 + 108 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (54 : ℚ⟦X⟧) * G ^ 2 + (12 - 177 * X + 648 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-59 + 432 * X : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (5 : ℚ⟦X⟧) * (derivative ℚ G) + (-16 + 108 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (54 : ℚ⟦X⟧) * G * G + (12 - 177 * X + 648 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-59 + 432 * X : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((5 : ℚ⟦X⟧) * (derivative ℚ G) + (-16 + 108 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (54 : ℚ⟦X⟧) * G * G + (12 - 177 * X + 648 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-59 + 432 * X : ℚ⟦X⟧) * G * G * G) =
      (5 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-16 + 108 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-16 + 108 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (216 : ℚ⟦X⟧) * G * (derivative ℚ G) + (24 - 354 * X + 1296 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (12 - 177 * X + 648 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-354 + 2592 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (432 : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d5, d12, d16, d54, d59, d108, d177, d432, d648]
    ring
  have hd2 : (5 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-16 + 108 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-16 + 108 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (216 : ℚ⟦X⟧) * G * (derivative ℚ G) + (24 - 354 * X + 1296 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (12 - 177 * X + 648 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-354 + 2592 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (432 : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL2, hp1, map_zero]
  have hp2 : (5 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-16 + 108 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (-16 + 108 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (216 : ℚ⟦X⟧) * G * (derivative ℚ G) + (24 - 354 * X + 1296 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (12 - 177 * X + 648 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (-354 + 2592 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (432 : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hd2
  have hL3 : derivative ℚ ((5 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-16 + 108 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (-16 + 108 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (216 : ℚ⟦X⟧) * G * (derivative ℚ G) + (24 - 354 * X + 1296 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (12 - 177 * X + 648 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (-354 + 2592 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (432 : ℚ⟦X⟧) * G * G * G) =
      (5 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-48 + 324 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (324 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (24 - 354 * X + 1296 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (-16 + 108 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (324 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (72 - 1062 * X + 3888 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-1062 + 7776 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (12 - 177 * X + 648 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-531 + 3888 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (3888 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d5, d12, d16, d24, d108, d177, d216, d354, d432, d648, d1296, d2592]
    ring
  have hd3 : (5 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-48 + 324 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (324 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (24 - 354 * X + 1296 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (-16 + 108 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (324 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (72 - 1062 * X + 3888 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-1062 + 7776 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (12 - 177 * X + 648 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-531 + 3888 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (3888 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) = 0 := by rw [← hL3, hp2, map_zero]
  have hfull : ((5 : ℚ⟦X⟧) + (-16 + 108 * X : ℚ⟦X⟧) * G + (12 - 177 * X + 648 * X ^ 2 : ℚ⟦X⟧) * G ^ 2) ^ 5 * ((20 * X ^ 3 - 295 * X ^ 4 + 1080 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (34 * X ^ 2 - 1319 * X ^ 3 + 7776 * X ^ 4) * derivative ℚ (derivative ℚ G) + (2 * X - 842 * X ^ 2 + 11328 * X ^ 3) * derivative ℚ G + (2 * X + 2112 * X ^ 2) * G - (12 * X)) = 0 := by
    linear_combination ((37500 * X : ℚ⟦X⟧) + (-418750 * X - 2550000 * X ^ 2 : ℚ⟦X⟧) * G + (2063750 * X + 7305000 * X ^ 2 - 131220000 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 + (-5882000 * X + 20251000 * X ^ 2 + 481938000 * X ^ 3 - 2337984000 * X ^ 4 : ℚ⟦X⟧) * G ^ 3 + (10621000 * X - 133415650 * X ^ 2 - 221826900 * X ^ 3 + 8057167200 * X ^ 4 - 25285219200 * X ^ 5 : ℚ⟦X⟧) * G ^ 4 + (-12437472 * X + 280200880 * X ^ 2 - 1604614230 * X ^ 3 - 5732357760 * X ^ 4 + 81032840640 * X ^ 5 - 199696264704 * X ^ 6 : ℚ⟦X⟧) * G ^ 5 + (9205920 * X - 299228160 * X ^ 2 + 3363646950 * X ^ 3 - 11014285800 * X ^ 4 - 62773315200 * X ^ 5 + 546922160640 * X ^ 6 - 1104717035520 * X ^ 7 : ℚ⟦X⟧) * G ^ 6 + (-3926016 * X + 164123136 * X ^ 2 - 2629501824 * X ^ 3 + 18547905120 * X ^ 4 - 27019215360 * X ^ 5 - 391751396352 * X ^ 6 + 2258532605952 * X ^ 7 - 3761479876608 * X ^ 8 : ℚ⟦X⟧) * G ^ 7 + (736128 * X - 36662112 * X ^ 2 + 739216296 * X ^ 3 - 7421984946 * X ^ 4 + 32887960560 * X ^ 5 + 32924563776 * X ^ 6 - 1011101958144 * X ^ 7 + 4093076385792 * X ^ 8 - 5642219814912 * X ^ 9 : ℚ⟦X⟧) * G ^ 8) * hP +
      ((1250 * X - 526250 * X ^ 2 + 7080000 * X ^ 3 : ℚ⟦X⟧) + (68000 * X ^ 2 - 3907000 * X ^ 3 + 45306000 * X ^ 4 - 148716000 * X ^ 5 : ℚ⟦X⟧) * (derivative ℚ G) + (324000 * X ^ 3 - 9078000 * X ^ 4 + 95162250 * X ^ 5 - 442422000 * X ^ 6 + 769824000 * X ^ 7 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-16000 * X + 5926000 * X ^ 2 - 100479000 * X ^ 3 + 401760000 * X ^ 4 : ℚ⟦X⟧) * G + (-754800 * X ^ 2 + 42254100 * X ^ 3 - 666730200 * X ^ 4 + 4157276400 * X ^ 5 - 9111916800 * X ^ 6 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-3033600 * X ^ 3 + 106896000 * X ^ 4 - 1504908000 * X ^ 5 + 10581435000 * X ^ 6 - 37161504000 * X ^ 7 + 52152076800 * X ^ 8 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (88800 * X - 29015700 * X ^ 2 + 614834850 * X ^ 3 - 4388295600 * X ^ 4 + 10336248000 * X ^ 5 : ℚ⟦X⟧) * G ^ 2 + (3557760 * X ^ 2 - 197428800 * X ^ 3 + 3781258200 * X ^ 4 - 33561928800 * X ^ 5 + 142181244000 * X ^ 6 - 233475022080 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (11736960 * X ^ 3 - 500314080 * X ^ 4 + 8877666600 * X ^ 5 - 83935546650 * X ^ 6 + 445984412400 * X ^ 7 - 1262722711680 * X ^ 8 + 1488374922240 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (-279040 * X + 80620800 * X ^ 2 - 2081005600 * X ^ 3 + 20890980000 * X ^ 4 - 93790224000 * X ^ 5 + 157791525120 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 + (-9229504 * X ^ 2 + 514571552 * X ^ 3 - 11209679340 * X ^ 4 + 125026228560 * X ^ 5 - 762498729360 * X ^ 6 + 2429092012032 * X ^ 7 - 3173325382656 * X ^ 8 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-24023040 * X ^ 3 + 1205514240 * X ^ 4 - 25901237760 * X ^ 5 + 308876716800 * X ^ 6 - 2207997824400 * X ^ 7 + 9461709429120 * X ^ 8 - 22505208376320 * X ^ 9 + 22921517998080 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) ^ 2 + (542912 * X - 138794848 * X ^ 2 + 4254474700 * X ^ 3 - 54990897060 * X ^ 4 + 360261393120 * X ^ 5 - 1185723795456 * X ^ 6 + 1562990183424 * X ^ 7 : ℚ⟦X⟧) * G ^ 4 + (14231040 * X ^ 2 - 804604800 * X ^ 3 + 19104404640 * X ^ 4 - 248048639400 * X ^ 5 + 1907942023800 * X ^ 6 - 8713534979520 * X ^ 7 + 21914453836800 * X ^ 8 - 23443945758720 * X ^ 9 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (27440640 * X ^ 3 - 1588584960 * X ^ 4 + 40196450880 * X ^ 5 - 580649986080 * X ^ 6 + 5237373374550 * X ^ 7 - 30205793715120 * X ^ 8 + 108780275652480 * X ^ 9 - 223656222090240 * X ^ 10 + 201004080906240 * X ^ 11 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) ^ 2 + (-669696 * X + 151174400 * X ^ 2 - 5388209536 * X ^ 3 + 85823678160 * X ^ 4 - 743336912520 * X ^ 5 + 3651308264448 * X ^ 6 - 9605656719360 * X ^ 7 + 10553040764928 * X ^ 8 : ℚ⟦X⟧) * G ^ 5 + (-13042944 * X ^ 2 + 751941696 * X ^ 3 - 18847226928 * X ^ 4 + 268251062988 * X ^ 5 - 2371072359780 * X ^ 6 + 13325509988352 * X ^ 7 - 46488542658048 * X ^ 8 + 92014040530944 * X ^ 9 - 79069441572864 * X ^ 10 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-16588800 * X ^ 3 + 1090713600 * X ^ 4 - 31844275200 * X ^ 5 + 541847750400 * X ^ 6 - 5921715664800 * X ^ 7 + 43106050373400 * X ^ 8 - 209002471084800 * X ^ 9 + 650871523353600 * X ^ 10 - 1181339773747200 * X ^ 11 + 952124593766400 * X ^ 12 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) ^ 2 + (511488 * X - 101311296 * X ^ 2 + 4129841760 * X ^ 3 - 79245861492 * X ^ 4 + 868474594290 * X ^ 5 - 5784986322144 * X ^ 6 + 23302944235008 * X ^ 7 - 52445942415360 * X ^ 8 + 50819160416256 * X ^ 9 : ℚ⟦X⟧) * G ^ 6 + (6580224 * X ^ 2 - 387698688 * X ^ 3 + 9975764736 * X ^ 4 - 146357546112 * X ^ 5 + 1338200850024 * X ^ 6 - 7797643238232 * X ^ 7 + 28184700129984 * X ^ 8 - 57191055810048 * X ^ 9 + 47194817826816 * X ^ 10 + 8463329722368 * X ^ 11 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (4147200 * X ^ 3 - 305856000 * X ^ 4 + 10142496000 * X ^ 5 - 199150488000 * X ^ 6 + 2564124417000 * X ^ 7 - 22619943922950 * X ^ 8 + 138462718518000 * X ^ 9 - 580722823008000 * X ^ 10 + 1597077990144000 * X ^ 11 - 2600710695936000 * X ^ 12 + 1904249187532800 * X ^ 13 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) ^ 2 + (-221184 * X + 37969920 * X ^ 2 - 1747774464 * X ^ 3 + 40044604416 * X ^ 4 - 545943560928 * X ^ 5 + 4743936411552 * X ^ 6 - 26700723282240 * X ^ 7 + 94727792742912 * X ^ 8 - 193304801783808 * X ^ 9 + 173498259308544 * X ^ 10 : ℚ⟦X⟧) * G ^ 7 + (-1410048 * X ^ 2 + 84879360 * X ^ 3 - 2179025280 * X ^ 4 + 30266913600 * X ^ 5 - 228028689540 * X ^ 6 + 581144628348 * X ^ 7 + 5225061777120 * X ^ 8 - 58858128437760 * X ^ 9 + 263771599564800 * X ^ 10 - 595959467950080 * X ^ 11 + 558579761676288 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (41472 * X - 6041088 * X ^ 2 + 311063616 * X ^ 3 - 8539791552 * X ^ 4 + 144886278474 * X ^ 5 - 1620735095610 * X ^ 6 + 12242492187984 * X ^ 7 - 62075992197888 * X ^ 8 + 203086898804736 * X ^ 9 - 388255251013632 * X ^ 10 + 330069859172352 * X ^ 11 : ℚ⟦X⟧) * G ^ 8) * hd1 +
      ((21250 * X ^ 2 - 824375 * X ^ 3 + 4860000 * X ^ 4 : ℚ⟦X⟧) + (120000 * X ^ 3 - 2580000 * X ^ 4 + 18427500 * X ^ 5 - 43740000 * X ^ 6 : ℚ⟦X⟧) * (derivative ℚ G) + (-272000 * X ^ 2 + 11578000 * X ^ 3 - 121486500 * X ^ 4 + 376164000 * X ^ 5 : ℚ⟦X⟧) * G + (-1332000 * X ^ 3 + 37854000 * X ^ 4 - 402689250 * X ^ 5 + 1900746000 * X ^ 6 - 3359232000 * X ^ 7 : ℚ⟦X⟧) * G * (derivative ℚ G) + (1509600 * X ^ 2 - 70094700 * X ^ 3 + 1019773275 * X ^ 4 - 6045175800 * X ^ 5 + 12765081600 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (6278400 * X ^ 3 - 222984000 * X ^ 4 + 3164022000 * X ^ 5 - 22422217500 * X ^ 6 + 79361856000 * X ^ 7 - 112240339200 * X ^ 8 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-4743680 * X ^ 2 + 239075200 * X ^ 3 - 4345567200 * X ^ 4 + 37241742600 * X ^ 5 - 153648122400 * X ^ 6 + 246928746240 * X ^ 7 : ℚ⟦X⟧) * G ^ 3 + (-16287360 * X ^ 3 + 697061280 * X ^ 4 - 12417780600 * X ^ 5 + 117866595150 * X ^ 6 - 628703888400 * X ^ 7 + 1786888874880 * X ^ 8 - 2114199843840 * X ^ 9 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (9229504 * X ^ 2 - 502710992 * X ^ 3 + 10788802740 * X ^ 4 - 119053003635 * X ^ 5 + 720113373360 * X ^ 6 - 2278706893632 * X ^ 7 + 2959879781376 * X ^ 8 : ℚ⟦X⟧) * G ^ 4 + (25113600 * X ^ 3 - 1262361600 * X ^ 4 + 27168278400 * X ^ 5 - 324530712000 * X ^ 6 + 2323787008500 * X ^ 7 - 9974509840800 * X ^ 8 + 23764340908800 * X ^ 9 - 24243913267200 * X ^ 10 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (-11384832 * X ^ 2 + 667621632 * X ^ 3 - 16333739328 * X ^ 4 + 217596129840 * X ^ 5 - 1712345023620 * X ^ 6 + 7984552872096 * X ^ 7 - 20472773918976 * X ^ 8 + 22304400205824 * X ^ 9 : ℚ⟦X⟧) * G ^ 5 + (-23016960 * X ^ 3 + 1333117440 * X ^ 4 - 33748384320 * X ^ 5 + 487741785120 * X ^ 6 - 4401514804950 * X ^ 7 + 25397715505680 * X ^ 8 - 91510909038720 * X ^ 9 + 188245415439360 * X ^ 10 - 169266594447360 * X ^ 11 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (8695296 * X ^ 2 - 547089984 * X ^ 3 + 14901352272 * X ^ 4 - 229865256972 * X ^ 5 + 2199189172545 * X ^ 6 - 13375852665768 * X ^ 7 + 50546877446592 * X ^ 8 - 108578719213056 * X ^ 9 + 101559956668416 * X ^ 10 : ℚ⟦X⟧) * G ^ 6 + (11612160 * X ^ 3 - 763499520 * X ^ 4 + 22290992640 * X ^ 5 - 379293425280 * X ^ 6 + 4145200965360 * X ^ 7 - 30174235261380 * X ^ 8 + 146301729759360 * X ^ 9 - 455610066347520 * X ^ 10 + 826937841623040 * X ^ 11 - 666487215636480 * X ^ 12 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (-3760128 * X ^ 2 + 253034496 * X ^ 3 - 7544005632 * X ^ 4 + 130806019584 * X ^ 5 - 1453808439648 * X ^ 6 + 10741917479904 * X ^ 7 - 52770855522528 * X ^ 8 + 166221956203776 * X ^ 9 - 304650483443712 * X ^ 10 + 247552394379264 * X ^ 11 : ℚ⟦X⟧) * G ^ 7 + (-2488320 * X ^ 3 + 183513600 * X ^ 4 - 6085497600 * X ^ 5 + 119490292800 * X ^ 6 - 1538474650200 * X ^ 7 + 13571966353770 * X ^ 8 - 83077631110800 * X ^ 9 + 348433693804800 * X ^ 10 - 958246794086400 * X ^ 11 + 1560426417561600 * X ^ 12 - 1142549512519680 * X ^ 13 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (705024 * X ^ 2 - 50595840 * X ^ 3 + 1630445760 * X ^ 4 - 31065495840 * X ^ 5 + 387520949250 * X ^ 6 - 3306564837234 * X ^ 7 + 19541504074320 * X ^ 8 - 78972529409280 * X ^ 9 + 208824171448320 * X ^ 10 - 326190833049600 * X ^ 11 + 228509902503936 * X ^ 12 : ℚ⟦X⟧) * G ^ 8) * hd2 +
      ((12500 * X ^ 3 - 184375 * X ^ 4 + 675000 * X ^ 5 : ℚ⟦X⟧) + (-160000 * X ^ 3 + 3440000 * X ^ 4 - 24570000 * X ^ 5 + 58320000 * X ^ 6 : ℚ⟦X⟧) * G + (888000 * X ^ 3 - 25236000 * X ^ 4 + 268459500 * X ^ 5 - 1267164000 * X ^ 6 + 2239488000 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 + (-2790400 * X ^ 3 + 99104000 * X ^ 4 - 1406232000 * X ^ 5 + 9965430000 * X ^ 6 - 35271936000 * X ^ 7 + 49884595200 * X ^ 8 : ℚ⟦X⟧) * G ^ 3 + (5429120 * X ^ 3 - 232353760 * X ^ 4 + 4139260200 * X ^ 5 - 39288865050 * X ^ 6 + 209567962800 * X ^ 7 - 595629624960 * X ^ 8 + 704733281280 * X ^ 9 : ℚ⟦X⟧) * G ^ 4 + (-6696960 * X ^ 3 + 336629760 * X ^ 4 - 7244874240 * X ^ 5 + 86541523200 * X ^ 6 - 619676535600 * X ^ 7 + 2659869290880 * X ^ 8 - 6337157575680 * X ^ 9 + 6465043537920 * X ^ 10 : ℚ⟦X⟧) * G ^ 5 + (5114880 * X ^ 3 - 296248320 * X ^ 4 + 7499640960 * X ^ 5 - 108387063360 * X ^ 6 + 978114401100 * X ^ 7 - 5643936779040 * X ^ 8 + 20335757564160 * X ^ 9 - 41832314542080 * X ^ 10 + 37614798766080 * X ^ 11 : ℚ⟦X⟧) * G ^ 6 + (-2211840 * X ^ 3 + 145428480 * X ^ 4 - 4245903360 * X ^ 5 + 72246366720 * X ^ 6 - 789562088640 * X ^ 7 + 5747473383120 * X ^ 8 - 27866996144640 * X ^ 9 + 86782869780480 * X ^ 10 - 157511969832960 * X ^ 11 + 126949945835520 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 + (414720 * X ^ 3 - 30585600 * X ^ 4 + 1014249600 * X ^ 5 - 19915048800 * X ^ 6 + 256412441700 * X ^ 7 - 2261994392295 * X ^ 8 + 13846271851800 * X ^ 9 - 58072282300800 * X ^ 10 + 159707799014400 * X ^ 11 - 260071069593600 * X ^ 12 + 190424918753280 * X ^ 13 : ℚ⟦X⟧) * G ^ 8) * hd3
  have k5 : constantCoeff (5 : ℚ⟦X⟧) = 5 := cnum 5
  have k12 : constantCoeff (12 : ℚ⟦X⟧) = 12 := cnum 12
  have k16 : constantCoeff (16 : ℚ⟦X⟧) = 16 := cnum 16
  have hPG : (5 : ℚ⟦X⟧) + (-16 + 108 * X : ℚ⟦X⟧) * G + (12 - 177 * X + 648 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k5, k12, k16] at h'
    norm_num at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 5 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (5 : ℚ⟦X⟧) * G + (-8 + 54 * X : ℚ⟦X⟧) * G ^ 2 + (4 - 59 * X + 216 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 20 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-295) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C 1080 + derivative ℚ (derivative ℚ G) * X * X * C 34 +
      derivative ℚ (derivative ℚ G) * X * X * X * C (-1319) + derivative ℚ (derivative ℚ G) * X * X * X * X * C 7776 +
      derivative ℚ G * X * C 2 + derivative ℚ G * X * X * C (-842) +
      derivative ℚ G * X * X * X * C 11328 + G * X * C 2 +
      G * X * X * C 2112 =
      C 12 * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (5 : ℚ⟦X⟧) * G + (-8 + 54 * X : ℚ⟦X⟧) * G ^ 2 + (4 - 59 * X + 216 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) (m : ℕ) :
    20 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-295) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      1080 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + 34 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-1319) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + 7776 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      2 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-842) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      11328 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 2 * coeff (m + 1 + 1 + 1 + 1) G +
      2112 * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (5 : ℚ⟦X⟧) * G + (-8 + 54 * X : ℚ⟦X⟧) * G ^ 2 + (4 - 59 * X + 216 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    68 * coeff (0 + 1 + 1) G + 4 * coeff (0 + 1 + 1) G +
      (-842) * coeff (0 + 1) G + 2 * coeff (0 + 1) G +
      2112 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (5 : ℚ⟦X⟧) * G + (-8 + 54 * X : ℚ⟦X⟧) * G ^ 2 + (4 - 59 * X + 216 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    120 * coeff (0 + 1 + 1 + 1) G + 204 * coeff (0 + 1 + 1 + 1) G +
      (-2638) * coeff (0 + 1 + 1) G + 6 * coeff (0 + 1 + 1 + 1) G +
      (-1684) * coeff (0 + 1 + 1) G + 11328 * coeff (0 + 1) G +
      2 * coeff (0 + 1 + 1) G + 2112 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE2 (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (5 : ℚ⟦X⟧) * G + (-8 + 54 * X : ℚ⟦X⟧) * G ^ 2 + (4 - 59 * X + 216 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    480 * coeff (0 + 1 + 1 + 1 + 1) G + (-1770) * coeff (0 + 1 + 1 + 1) G +
      408 * coeff (0 + 1 + 1 + 1 + 1) G + (-7914) * coeff (0 + 1 + 1 + 1) G +
      15552 * coeff (0 + 1 + 1) G + 8 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-2526) * coeff (0 + 1 + 1 + 1) G + 22656 * coeff (0 + 1 + 1) G +
      2 * coeff (0 + 1 + 1 + 1) G + 2112 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A160906Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a160906.main := by
  intro T G hT hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  have hT0c : PowerSeries.constantCoeff T = 1 := by
    have h := congrArg PowerSeries.constantCoeff hT
    simpa using h
  have kn2 : PowerSeries.constantCoeff (2 : PowerSeries ℚ) = 2 := A160906Aux.cnum 2
  have kn6 : PowerSeries.constantCoeff (6 : PowerSeries ℚ) = 6 := A160906Aux.cnum 6
  have kn7 : PowerSeries.constantCoeff (7 : PowerSeries ℚ) = 7 := A160906Aux.cnum 7
  have hN1 : ((6) + (-7) * T + (2) * T ^ 2 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [hT0c, kn2, kn6, kn7] at h'
    norm_num at h'
  have hM : ((1 : PowerSeries ℚ) * PowerSeries.X ^ 4) * (((6) + (-7) * T + (2) * T ^ 2) ^ 3 * ((-1 : PowerSeries ℚ) + (5 : PowerSeries ℚ) * G + (-8 + 54 * PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (4 - 59 * PowerSeries.X + 216 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 3)) = 0 := by
    linear_combination ((216) * PowerSeries.X ^ 4 + (-540) * PowerSeries.X ^ 4 * T + (378) * PowerSeries.X ^ 4 * T ^ 2 + (-49) * PowerSeries.X ^ 4 * T ^ 3 + (-216) * PowerSeries.X ^ 5 * T ^ 3) * hT +
      ((180) * PowerSeries.X ^ 4 + (-420) * PowerSeries.X ^ 4 * T + (317) * PowerSeries.X ^ 4 * T ^ 2 + (-84) * PowerSeries.X ^ 4 * T ^ 3 + (8) * PowerSeries.X ^ 4 * T ^ 4 + (-288) * PowerSeries.X ^ 4 * G + (672) * PowerSeries.X ^ 4 * G * T + (-560) * PowerSeries.X ^ 4 * G * T ^ 2 + (196) * PowerSeries.X ^ 4 * G * T ^ 3 + (-24) * PowerSeries.X ^ 4 * G * T ^ 4 + (144) * PowerSeries.X ^ 4 * G ^ 2 + (-336) * PowerSeries.X ^ 4 * G ^ 2 * T + (292) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 2 + (-112) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 3 + (16) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 4 + (324) * PowerSeries.X ^ 5 * T ^ 2 + (-378) * PowerSeries.X ^ 5 * T ^ 3 + (49) * PowerSeries.X ^ 5 * T ^ 4 + (1944) * PowerSeries.X ^ 5 * G + (-4536) * PowerSeries.X ^ 5 * G * T + (3588) * PowerSeries.X ^ 5 * G * T ^ 2 + (-1099) * PowerSeries.X ^ 5 * G * T ^ 3 + (98) * PowerSeries.X ^ 5 * G * T ^ 4 + (-2124) * PowerSeries.X ^ 5 * G ^ 2 + (4956) * PowerSeries.X ^ 5 * G ^ 2 * T + (-4307) * PowerSeries.X ^ 5 * G ^ 2 * T ^ 2 + (1652) * PowerSeries.X ^ 5 * G ^ 2 * T ^ 3 + (-236) * PowerSeries.X ^ 5 * G ^ 2 * T ^ 4 + (216) * PowerSeries.X ^ 6 * T ^ 4 + (1296) * PowerSeries.X ^ 6 * G * T ^ 2 + (-1512) * PowerSeries.X ^ 6 * G * T ^ 3 + (432) * PowerSeries.X ^ 6 * G * T ^ 4 + (7776) * PowerSeries.X ^ 6 * G ^ 2 + (-18144) * PowerSeries.X ^ 6 * G ^ 2 * T + (15768) * PowerSeries.X ^ 6 * G ^ 2 * T ^ 2 + (-6048) * PowerSeries.X ^ 6 * G ^ 2 * T ^ 3 + (864) * PowerSeries.X ^ 6 * G ^ 2 * T ^ 4) * hG
  have hLne : ((1 : PowerSeries ℚ) * PowerSeries.X ^ 4) ≠ 0 := mul_ne_zero one_ne_zero (pow_ne_zero 4 PowerSeries.X_ne_zero)
  have hP : (-1 : PowerSeries ℚ) + (5 : PowerSeries ℚ) * G + (-8 + 54 * PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (4 - 59 * PowerSeries.X + 216 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 3 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hM).resolve_left hLne)).resolve_left (pow_ne_zero 3 hN1)
  have h0c : PowerSeries.constantCoeff G = (1 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A160906Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A160906Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A160906Aux.relE2 G hP h0c
        push_cast
        linear_combination r
      | succ m =>
        have r := A160906Aux.rel G hP h0c m
        push_cast
        linear_combination r
