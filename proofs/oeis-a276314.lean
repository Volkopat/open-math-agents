import OMAStatements.S_oeis_a276314

-- Problem: A276314: G.f. A(x) satisfies: x = A(x)-A(x)^2-3*A(x)^3.
-- Upstream: formal-conjectures statements/oeis-a276314.lean:0 (declaration OMA.S_oeis_a276314.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A276314Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (-X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-1 : ℚ⟦X⟧) * G ^ 2 + (-3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (169 * X ^ 3 + 169 * X ^ 4 - 7277 * X ^ 5 - 17253 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (676 * X ^ 2 + 1183 * X ^ 3 - 52070 * X ^ 4 - 151389 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-1508 * X ^ 2 - 27334 * X ^ 3 - 114966 * X ^ 4) * derivative ℚ G + (1404 * X ^ 2 + 11070 * X ^ 3) * G =
      -156 * X ^ 2 - 1230 * X ^ 3 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d9 : derivative ℚ (9 : ℚ⟦X⟧) = 0 := dnum 9
  have d18 : derivative ℚ (18 : ℚ⟦X⟧) = 0 := dnum 18
  have hp0 : (-1 * X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-1 : ℚ⟦X⟧) * G * G + (-3 : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-1 * X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-1 : ℚ⟦X⟧) * G * G + (-3 : ℚ⟦X⟧) * G * G * G) =
      (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-9 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d3]
    ring
  have hd1 : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-9 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-9 : ℚ⟦X⟧) * G * G * (derivative ℚ G) = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-9 : ℚ⟦X⟧) * G * G * (derivative ℚ G)) =
      (1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-18 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-9 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d2, d9]
    ring
  have hd2 : (1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-18 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-9 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) = 0 := by rw [← hL2, hp1, map_zero]
  have hp2 : (1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-2 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-18 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (-9 : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) = 0 := by linear_combination hd2
  have hL3 : derivative ℚ ((1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-2 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (-2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-18 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (-9 : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G))) =
      (1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-6 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-18 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (-2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-54 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-9 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) := by
    simp [Derivation.leibniz, d2, d9, d18]
    ring
  have hd3 : (1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-6 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-18 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (-2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-54 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-9 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) = 0 := by rw [← hL3, hp2, map_zero]
  have hfull : ((1 : ℚ⟦X⟧) + (-2 : ℚ⟦X⟧) * G + (-9 : ℚ⟦X⟧) * G ^ 2) ^ 5 * ((169 * X ^ 3 + 169 * X ^ 4 - 7277 * X ^ 5 - 17253 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (676 * X ^ 2 + 1183 * X ^ 3 - 52070 * X ^ 4 - 151389 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-1508 * X ^ 2 - 27334 * X ^ 3 - 114966 * X ^ 4) * derivative ℚ G + (1404 * X ^ 2 + 11070 * X ^ 3) * G - (-156 * X ^ 2 - 1230 * X ^ 3)) = 0 := by
    linear_combination ((18668 * X ^ 2 + 214036 * X ^ 3 + 521088 * X ^ 4 + 517590 * X ^ 5 : ℚ⟦X⟧) + (-45656 * X ^ 2 + 91640 * X ^ 3 + 3341340 * X ^ 4 + 3105540 * X ^ 5 : ℚ⟦X⟧) * G + (-352144 * X ^ 2 - 3903230 * X ^ 3 - 6656580 * X ^ 4 + 13974930 * X ^ 5 : ℚ⟦X⟧) * G ^ 2 + (316368 * X ^ 2 + 219960 * X ^ 3 - 17933400 * X ^ 4 : ℚ⟦X⟧) * G ^ 3 + (1937520 * X ^ 2 + 28923480 * X ^ 3 + 99333540 * X ^ 4 : ℚ⟦X⟧) * G ^ 4 + (-227448 * X ^ 2 + 22771044 * X ^ 3 + 178800372 * X ^ 4 : ℚ⟦X⟧) * G ^ 5 + (2729376 * X ^ 2 + 21520080 * X ^ 3 : ℚ⟦X⟧) * G ^ 6 + (24564384 * X ^ 2 + 193680720 * X ^ 3 : ℚ⟦X⟧) * G ^ 7 + (27634932 * X ^ 2 + 217890810 * X ^ 3 : ℚ⟦X⟧) * G ^ 8) * hP +
      ((-156 * X ^ 2 - 19898 * X ^ 3 - 214036 * X ^ 4 - 521088 * X ^ 5 - 517590 * X ^ 6 : ℚ⟦X⟧) + (1352 * X ^ 2 + 7436 * X ^ 3 - 99070 * X ^ 4 - 521088 * X ^ 5 - 517590 * X ^ 6 : ℚ⟦X⟧) * (derivative ℚ G) + (5070 * X ^ 3 + 5070 * X ^ 4 - 218310 * X ^ 5 - 517590 * X ^ 6 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (18824 * X ^ 2 + 260922 * X ^ 3 + 429448 * X ^ 4 - 2823750 * X ^ 5 - 3105540 * X ^ 6 : ℚ⟦X⟧) * G + (4056 * X ^ 2 + 27378 * X ^ 3 - 292140 * X ^ 4 - 1781574 * X ^ 5 - 2070360 * X ^ 6 : ℚ⟦X⟧) * G * (derivative ℚ G) + (10140 * X ^ 3 + 10140 * X ^ 4 - 436620 * X ^ 5 - 1035180 * X ^ 6 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-49504 * X ^ 2 + 346598 * X ^ 3 + 6723482 * X ^ 4 + 9244530 * X ^ 5 - 13974930 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (-93288 * X ^ 2 - 132834 * X ^ 3 + 7216080 * X ^ 4 + 19581822 * X ^ 5 - 3105540 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-55770 * X ^ 3 - 55770 * X ^ 4 + 2401410 * X ^ 5 + 5693490 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (-399152 * X ^ 2 - 5242396 * X ^ 3 - 11781144 * X ^ 4 + 27250020 * X ^ 5 : ℚ⟦X⟧) * G ^ 3 + (-47320 * X ^ 2 - 630370 * X ^ 3 + 3097340 * X ^ 4 + 34174710 * X ^ 5 + 55899720 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-790920 * X ^ 3 - 790920 * X ^ 4 + 34056360 * X ^ 5 + 80744040 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) ^ 2 + (442000 * X ^ 2 - 955150 * X ^ 3 - 50224320 * X ^ 4 - 122625090 * X ^ 5 : ℚ⟦X⟧) * G ^ 4 + (1399320 * X ^ 2 + 1216800 * X ^ 3 - 109016910 * X ^ 4 - 260325900 * X ^ 5 + 125774370 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (-410670 * X ^ 3 - 410670 * X ^ 4 + 17683110 * X ^ 5 + 41924790 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) ^ 2 + (3482856 * X ^ 2 + 46989918 * X ^ 3 + 114465636 * X ^ 4 - 220725162 * X ^ 5 : ℚ⟦X⟧) * G ^ 5 + (985608 * X ^ 2 + 1724814 * X ^ 3 - 75918060 * X ^ 4 - 220725162 * X ^ 5 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (7392060 * X ^ 3 + 7392060 * X ^ 4 - 318295980 * X ^ 5 - 754646220 * X ^ 6 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) ^ 2 + (1465776 * X ^ 2 + 26568648 * X ^ 3 + 111746952 * X ^ 4 : ℚ⟦X⟧) * G ^ 6 + (-6899256 * X ^ 2 - 12073698 * X ^ 3 + 531426420 * X ^ 4 + 1545076134 * X ^ 5 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (11088090 * X ^ 3 + 11088090 * X ^ 4 - 477443970 * X ^ 5 - 1131969330 * X ^ 6 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) ^ 2 + (-8794656 * X ^ 2 - 159411888 * X ^ 3 - 670481712 * X ^ 4 : ℚ⟦X⟧) * G ^ 7 + (-8870472 * X ^ 2 - 15523326 * X ^ 3 + 683262540 * X ^ 4 + 1986526458 * X ^ 5 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (-9893988 * X ^ 2 - 179338374 * X ^ 3 - 754291926 * X ^ 4 : ℚ⟦X⟧) * G ^ 8) * hd1 +
      ((676 * X ^ 2 + 1183 * X ^ 3 - 52070 * X ^ 4 - 151389 * X ^ 5 : ℚ⟦X⟧) + (1014 * X ^ 3 + 1014 * X ^ 4 - 43662 * X ^ 5 - 103518 * X ^ 6 : ℚ⟦X⟧) * (derivative ℚ G) + (-5408 * X ^ 2 - 9464 * X ^ 3 + 416560 * X ^ 4 + 1211112 * X ^ 5 : ℚ⟦X⟧) * G + (3042 * X ^ 3 + 3042 * X ^ 4 - 130986 * X ^ 5 - 310554 * X ^ 6 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-8112 * X ^ 2 - 14196 * X ^ 3 + 624840 * X ^ 4 + 1816668 * X ^ 5 : ℚ⟦X⟧) * G ^ 2 + (-69966 * X ^ 3 - 69966 * X ^ 4 + 3012678 * X ^ 5 + 7142742 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (124384 * X ^ 2 + 217672 * X ^ 3 - 9580880 * X ^ 4 - 27855576 * X ^ 5 : ℚ⟦X⟧) * G ^ 3 + (-35490 * X ^ 3 - 35490 * X ^ 4 + 1528170 * X ^ 5 + 3623130 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (47320 * X ^ 2 + 82810 * X ^ 3 - 3644900 * X ^ 4 - 10597230 * X ^ 5 : ℚ⟦X⟧) * G ^ 4 + (1049490 * X ^ 3 + 1049490 * X ^ 4 - 45190170 * X ^ 5 - 107141130 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (-1119456 * X ^ 2 - 1959048 * X ^ 3 + 86227920 * X ^ 4 + 250700184 * X ^ 5 : ℚ⟦X⟧) * G ^ 5 + (739206 * X ^ 3 + 739206 * X ^ 4 - 31829598 * X ^ 5 - 75464622 * X ^ 6 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-657072 * X ^ 2 - 1149876 * X ^ 3 + 50612040 * X ^ 4 + 147150108 * X ^ 5 : ℚ⟦X⟧) * G ^ 6 + (-5174442 * X ^ 3 - 5174442 * X ^ 4 + 222807186 * X ^ 5 + 528252354 * X ^ 6 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (3942432 * X ^ 2 + 6899256 * X ^ 3 - 303672240 * X ^ 4 - 882900648 * X ^ 5 : ℚ⟦X⟧) * G ^ 7 + (-6652854 * X ^ 3 - 6652854 * X ^ 4 + 286466382 * X ^ 5 + 679181598 * X ^ 6 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (4435236 * X ^ 2 + 7761663 * X ^ 3 - 341631270 * X ^ 4 - 993263229 * X ^ 5 : ℚ⟦X⟧) * G ^ 8) * hd2 +
      ((169 * X ^ 3 + 169 * X ^ 4 - 7277 * X ^ 5 - 17253 * X ^ 6 : ℚ⟦X⟧) + (-1352 * X ^ 3 - 1352 * X ^ 4 + 58216 * X ^ 5 + 138024 * X ^ 6 : ℚ⟦X⟧) * G + (-2028 * X ^ 3 - 2028 * X ^ 4 + 87324 * X ^ 5 + 207036 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (31096 * X ^ 3 + 31096 * X ^ 4 - 1338968 * X ^ 5 - 3174552 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 + (11830 * X ^ 3 + 11830 * X ^ 4 - 509390 * X ^ 5 - 1207710 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 + (-279864 * X ^ 3 - 279864 * X ^ 4 + 12050712 * X ^ 5 + 28570968 * X ^ 6 : ℚ⟦X⟧) * G ^ 5 + (-164268 * X ^ 3 - 164268 * X ^ 4 + 7073244 * X ^ 5 + 16769916 * X ^ 6 : ℚ⟦X⟧) * G ^ 6 + (985608 * X ^ 3 + 985608 * X ^ 4 - 42439464 * X ^ 5 - 100619496 * X ^ 6 : ℚ⟦X⟧) * G ^ 7 + (1108809 * X ^ 3 + 1108809 * X ^ 4 - 47744397 * X ^ 5 - 113196933 * X ^ 6 : ℚ⟦X⟧) * G ^ 8) * hd3
  have k2 : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
  have k9 : constantCoeff (9 : ℚ⟦X⟧) = 9 := cnum 9
  have hPG : (1 : ℚ⟦X⟧) + (-2 : ℚ⟦X⟧) * G + (-9 : ℚ⟦X⟧) * G ^ 2 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k2, k9] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 5 hPG)
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (-X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-1 : ℚ⟦X⟧) * G ^ 2 + (-3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 169 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C 169 +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C (-7277) + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C (-17253) +
      derivative ℚ (derivative ℚ G) * X * X * C 676 + derivative ℚ (derivative ℚ G) * X * X * X * C 1183 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-52070) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-151389) +
      derivative ℚ G * X * X * C (-1508) + derivative ℚ G * X * X * X * C (-27334) +
      derivative ℚ G * X * X * X * X * C (-114966) + G * X * X * C 1404 +
      G * X * X * X * C 11070 =
      C (-156) * X * X + C (-1230) * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (-X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-1 : ℚ⟦X⟧) * G ^ 2 + (-3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    169 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 169 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-7277) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G + (-17253) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G +
      676 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 1183 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-52070) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-151389) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-1508) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-27334) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-114966) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 1404 * coeff (m + 1 + 1 + 1 + 1) G +
      11070 * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (-X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-1 : ℚ⟦X⟧) * G ^ 2 + (-3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    4056 * coeff (0 + 1 + 1 + 1 + 1) G + 1014 * coeff (0 + 1 + 1 + 1) G +
      8112 * coeff (0 + 1 + 1 + 1 + 1) G + 7098 * coeff (0 + 1 + 1 + 1) G +
      (-104140) * coeff (0 + 1 + 1) G + (-4524) * coeff (0 + 1 + 1 + 1) G +
      (-54668) * coeff (0 + 1 + 1) G + (-114966) * coeff (0 + 1) G +
      1404 * coeff (0 + 1 + 1) G + 11070 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (-X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-1 : ℚ⟦X⟧) * G ^ 2 + (-3 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    10140 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 4056 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-43662) * coeff (0 + 1 + 1 + 1) G + 13520 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      14196 * coeff (0 + 1 + 1 + 1 + 1) G + (-312420) * coeff (0 + 1 + 1 + 1) G +
      (-302778) * coeff (0 + 1 + 1) G + (-6032) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-82002) * coeff (0 + 1 + 1 + 1) G + (-229932) * coeff (0 + 1 + 1) G +
      1404 * coeff (0 + 1 + 1 + 1) G + 11070 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A276314Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a276314.main := by
  intro G h0 hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  rw [e1, e2, e3]
  have hP : (-PowerSeries.X : PowerSeries ℚ) + (1 : PowerSeries ℚ) * G + (-1 : PowerSeries ℚ) * G ^ 2 + (-3 : PowerSeries ℚ) * G ^ 3 = 0 := by
    linear_combination -hG
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A276314Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A276314Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A276314Aux.rel G hP h0c m
      push_cast
      linear_combination r
