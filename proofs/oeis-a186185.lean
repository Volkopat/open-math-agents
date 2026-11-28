import OMAStatements.S_oeis_a186185

-- Problem: A186185: Expansion of 1/(1 - x*A001764(x/(1-x))/(1-x)).
-- Upstream: formal-conjectures statements/oeis-a186185.lean:0 (declaration OMA.S_oeis_a186185.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A186185Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (-1 + 2 * X - X ^ 2 : ℚ⟦X⟧) + (3 - 6 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G + (-3 + 7 * X - 4 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 - 3 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0) :
    (4 * X ^ 2 + 9 * X ^ 3 - 570 * X ^ 4 + 2579 * X ^ 5 - 4899 * X ^ 6 + 4272 * X ^ 7 - 1395 * X ^ 8) * derivative ℚ (derivative ℚ G) + (-2 * X - 100 * X ^ 2 + 830 * X ^ 3 - 398 * X ^ 4 - 4506 * X ^ 5 + 6966 * X ^ 6 - 2790 * X ^ 7) * derivative ℚ G + (2 + 52 * X - 510 * X ^ 2 + 750 * X ^ 3 - 678 * X ^ 4) * G =
      2 + 52 * X - 540 * X ^ 2 + 900 * X ^ 3 - 414 * X ^ 4 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d7 : derivative ℚ (7 : ℚ⟦X⟧) = 0 := dnum 7
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d9 : derivative ℚ (9 : ℚ⟦X⟧) = 0 := dnum 9
  have d14 : derivative ℚ (14 : ℚ⟦X⟧) = 0 := dnum 14
  have hp0 : (-1 + 2 * X - 1 * (X * X) : ℚ⟦X⟧) + (3 - 6 * X + 3 * (X * X) : ℚ⟦X⟧) * G + (-3 + 7 * X - 4 * (X * X) : ℚ⟦X⟧) * G * G + (1 - 3 * X + 3 * (X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-1 + 2 * X - 1 * (X * X) : ℚ⟦X⟧) + (3 - 6 * X + 3 * (X * X) : ℚ⟦X⟧) * G + (-3 + 7 * X - 4 * (X * X) : ℚ⟦X⟧) * G * G + (1 - 3 * X + 3 * (X * X) : ℚ⟦X⟧) * G * G * G) =
      (2 - 2 * X : ℚ⟦X⟧) + (3 - 6 * X + 3 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) + (-6 + 6 * X : ℚ⟦X⟧) * G + (-6 + 14 * X - 8 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (7 - 8 * X : ℚ⟦X⟧) * G ^ 2 + (3 - 9 * X + 9 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-3 + 6 * X : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d2, d3, d4, d6, d7]
    ring
  have hd1 : (2 - 2 * X : ℚ⟦X⟧) + (3 - 6 * X + 3 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) + (-6 + 6 * X : ℚ⟦X⟧) * G + (-6 + 14 * X - 8 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (7 - 8 * X : ℚ⟦X⟧) * G ^ 2 + (3 - 9 * X + 9 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-3 + 6 * X : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (2 - 2 * X : ℚ⟦X⟧) + (3 - 6 * X + 3 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (-6 + 6 * X : ℚ⟦X⟧) * G + (-6 + 14 * X - 8 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (7 - 8 * X : ℚ⟦X⟧) * G * G + (3 - 9 * X + 9 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-3 + 6 * X : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((2 - 2 * X : ℚ⟦X⟧) + (3 - 6 * X + 3 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (-6 + 6 * X : ℚ⟦X⟧) * G + (-6 + 14 * X - 8 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (7 - 8 * X : ℚ⟦X⟧) * G * G + (3 - 9 * X + 9 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-3 + 6 * X : ℚ⟦X⟧) * G * G * G) =
      (-2 : ℚ⟦X⟧) + (3 - 6 * X + 3 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-12 + 12 * X : ℚ⟦X⟧) * (derivative ℚ G) + (-6 + 14 * X - 8 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (6 : ℚ⟦X⟧) * G + (-6 + 14 * X - 8 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (28 - 32 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 18 * X + 18 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-8 : ℚ⟦X⟧) * G ^ 2 + (3 - 9 * X + 9 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-18 + 36 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (6 : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d2, d3, d6, d7, d8, d9, d14]
    ring
  have hd2 : (-2 : ℚ⟦X⟧) + (3 - 6 * X + 3 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-12 + 12 * X : ℚ⟦X⟧) * (derivative ℚ G) + (-6 + 14 * X - 8 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (6 : ℚ⟦X⟧) * G + (-6 + 14 * X - 8 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (28 - 32 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 18 * X + 18 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-8 : ℚ⟦X⟧) * G ^ 2 + (3 - 9 * X + 9 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-18 + 36 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (6 : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((3 - 6 * X + 3 * X ^ 2 : ℚ⟦X⟧) + (-6 + 14 * X - 8 * X ^ 2 : ℚ⟦X⟧) * G + (3 - 9 * X + 9 * X ^ 2 : ℚ⟦X⟧) * G ^ 2) ^ 3 * ((4 * X ^ 2 + 9 * X ^ 3 - 570 * X ^ 4 + 2579 * X ^ 5 - 4899 * X ^ 6 + 4272 * X ^ 7 - 1395 * X ^ 8) * derivative ℚ (derivative ℚ G) + (-2 * X - 100 * X ^ 2 + 830 * X ^ 3 - 398 * X ^ 4 - 4506 * X ^ 5 + 6966 * X ^ 6 - 2790 * X ^ 7) * derivative ℚ G + (2 + 52 * X - 510 * X ^ 2 + 750 * X ^ 3 - 678 * X ^ 4) * G - (2 + 52 * X - 540 * X ^ 2 + 900 * X ^ 3 - 414 * X ^ 4)) = 0 := by
    linear_combination ((54 + 1152 * X - 21444 * X ^ 2 + 111122 * X ^ 3 - 276248 * X ^ 4 + 344448 * X ^ 5 - 140186 * X ^ 6 - 153886 * X ^ 7 + 224982 * X ^ 8 - 109524 * X ^ 9 + 19530 * X ^ 10 : ℚ⟦X⟧) + (-216 - 4500 * X + 87306 * X ^ 2 - 476658 * X ^ 3 + 1274400 * X ^ 4 - 1796784 * X ^ 5 + 1101546 * X ^ 6 + 272358 * X ^ 7 - 847908 * X ^ 8 + 490896 * X ^ 9 - 100440 * X ^ 10 : ℚ⟦X⟧) * G + (324 + 6570 * X - 133836 * X ^ 2 + 777216 * X ^ 3 - 2267694 * X ^ 4 + 3659958 * X ^ 5 - 3041496 * X ^ 6 + 640800 * X ^ 7 + 910266 * X ^ 8 - 702768 * X ^ 9 + 150660 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 + (-216 - 4248 * X + 91584 * X ^ 2 - 569376 * X ^ 3 + 1815840 * X ^ 4 - 3298176 * X ^ 5 + 3291768 * X ^ 6 - 1313424 * X ^ 7 - 471600 * X ^ 8 + 591768 * X ^ 9 - 133920 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 + (54 + 1026 * X - 23598 * X ^ 2 + 157788 * X ^ 3 - 550044 * X ^ 4 + 1119636 * X ^ 5 - 1312578 * X ^ 6 + 715284 * X ^ 7 + 83106 * X ^ 8 - 276372 * X ^ 9 + 75330 * X ^ 10 : ℚ⟦X⟧) * G ^ 4) * hP +
      ((-18 * X - 732 * X ^ 2 + 10906 * X ^ 3 - 52826 * X ^ 4 + 123328 * X ^ 5 - 156970 * X ^ 6 + 114704 * X ^ 7 - 53854 * X ^ 8 + 24258 * X ^ 9 - 11586 * X ^ 10 + 2790 * X ^ 11 : ℚ⟦X⟧) + (72 * X ^ 2 - 150 * X ^ 3 - 10458 * X ^ 4 + 91656 * X ^ 5 - 361878 * X ^ 6 + 835488 * X ^ 7 - 1221390 * X ^ 8 + 1149888 * X ^ 9 - 677826 * X ^ 10 + 228078 * X ^ 11 - 33480 * X ^ 12 : ℚ⟦X⟧) * (derivative ℚ G) + (72 * X + 2856 * X ^ 2 - 44604 * X ^ 3 + 231888 * X ^ 4 - 599580 * X ^ 5 + 888912 * X ^ 6 - 824376 * X ^ 7 + 528000 * X ^ 8 - 259956 * X ^ 9 + 93528 * X ^ 10 - 16740 * X ^ 11 : ℚ⟦X⟧) * G + (-216 * X ^ 2 + 546 * X ^ 3 + 31214 * X ^ 4 - 289030 * X ^ 5 + 1201970 * X ^ 6 - 2933000 * X ^ 7 + 4552588 * X ^ 8 - 4571630 * X ^ 9 + 2885514 * X ^ 10 - 1042566 * X ^ 11 + 164610 * X ^ 12 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-108 * X - 4164 * X ^ 2 + 68680 * X ^ 3 - 387450 * X ^ 4 + 1132250 * X ^ 5 - 1993690 * X ^ 6 + 2316900 * X ^ 7 - 1910390 * X ^ 8 + 1151094 * X ^ 9 - 462402 * X ^ 10 + 89280 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 + (216 * X ^ 2 - 666 * X ^ 3 - 30924 * X ^ 4 + 306558 * X ^ 5 - 1360620 * X ^ 6 + 3560472 * X ^ 7 - 5958900 * X ^ 8 + 6483294 * X ^ 9 - 4449492 * X ^ 10 + 1751382 * X ^ 11 - 301320 * X ^ 12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (72 * X + 2688 * X ^ 2 - 47196 * X ^ 3 + 290772 * X ^ 4 - 959814 * X ^ 5 + 1955916 * X ^ 6 - 2635578 * X ^ 7 + 2447202 * X ^ 8 - 1582596 * X ^ 9 + 662454 * X ^ 10 - 133920 * X ^ 11 : ℚ⟦X⟧) * G ^ 3 + (-72 * X ^ 2 + 270 * X ^ 3 + 10152 * X ^ 4 - 109116 * X ^ 5 + 522882 * X ^ 6 - 1488456 * X ^ 7 + 2737152 * X ^ 8 - 3309174 * X ^ 9 + 2554416 * X ^ 10 - 1144044 * X ^ 11 + 225990 * X ^ 12 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-18 * X - 648 * X ^ 2 + 12204 * X ^ 3 - 82422 * X ^ 4 + 306522 * X ^ 5 - 717480 * X ^ 6 + 1116450 * X ^ 7 - 1174716 * X ^ 8 + 823284 * X ^ 9 - 358506 * X ^ 10 + 75330 * X ^ 11 : ℚ⟦X⟧) * G ^ 4) * hd1 +
      ((36 * X ^ 2 - 63 * X ^ 3 - 5238 * X ^ 4 + 44073 * X ^ 5 - 168003 * X ^ 6 + 374679 * X ^ 7 - 528867 * X ^ 8 + 480483 * X ^ 9 - 273213 * X ^ 10 + 88668 * X ^ 11 - 12555 * X ^ 12 : ℚ⟦X⟧) + (-144 * X ^ 2 + 300 * X ^ 3 + 20916 * X ^ 4 - 183312 * X ^ 5 + 723756 * X ^ 6 - 1670976 * X ^ 7 + 2442780 * X ^ 8 - 2299776 * X ^ 9 + 1355652 * X ^ 10 - 456156 * X ^ 11 + 66960 * X ^ 12 : ℚ⟦X⟧) * G + (216 * X ^ 2 - 546 * X ^ 3 - 31214 * X ^ 4 + 289030 * X ^ 5 - 1201970 * X ^ 6 + 2933000 * X ^ 7 - 4552588 * X ^ 8 + 4571630 * X ^ 9 - 2885514 * X ^ 10 + 1042566 * X ^ 11 - 164610 * X ^ 12 : ℚ⟦X⟧) * G ^ 2 + (-144 * X ^ 2 + 444 * X ^ 3 + 20616 * X ^ 4 - 204372 * X ^ 5 + 907080 * X ^ 6 - 2373648 * X ^ 7 + 3972600 * X ^ 8 - 4322196 * X ^ 9 + 2966328 * X ^ 10 - 1167588 * X ^ 11 + 200880 * X ^ 12 : ℚ⟦X⟧) * G ^ 3 + (36 * X ^ 2 - 135 * X ^ 3 - 5076 * X ^ 4 + 54558 * X ^ 5 - 261441 * X ^ 6 + 744228 * X ^ 7 - 1368576 * X ^ 8 + 1654587 * X ^ 9 - 1277208 * X ^ 10 + 572022 * X ^ 11 - 112995 * X ^ 12 : ℚ⟦X⟧) * G ^ 4) * hd2
  have hres : ((-1458 + 9477 * X - 13851 * X ^ 2 + 5832 * X ^ 3 : ℚ⟦X⟧) + (2916 - 18225 * X + 27945 * X ^ 2 - 10449 * X ^ 3 : ℚ⟦X⟧) * G + (-1458 + 9720 * X - 20412 * X ^ 2 + 16038 * X ^ 3 : ℚ⟦X⟧) * G ^ 2) * ((3 - 6 * X + 3 * X ^ 2 : ℚ⟦X⟧) + (-6 + 14 * X - 8 * X ^ 2 : ℚ⟦X⟧) * G + (3 - 9 * X + 9 * X ^ 2 : ℚ⟦X⟧) * G ^ 2) = (-972 * X ^ 2 + 9477 * X ^ 3 - 16038 * X ^ 4 + 7533 * X ^ 5 : ℚ⟦X⟧) := by
    linear_combination (-((-4374 + 28431 * X - 40581 * X ^ 2 + 9963 * X ^ 3 : ℚ⟦X⟧) + (4374 - 29160 * X + 61236 * X ^ 2 - 48114 * X ^ 3 : ℚ⟦X⟧) * G)) * hP
  have hd0 : (-972 + 9477 * X - 16038 * X ^ 2 + 7533 * X ^ 3 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    have kc : constantCoeff (972 : ℚ⟦X⟧) = 972 := cnum 972
    simp [kc] at h'
  have hdisc : (-972 * X ^ 2 + 9477 * X ^ 3 - 16038 * X ^ 4 + 7533 * X ^ 5 : ℚ⟦X⟧) ≠ 0 := by
    have e : (-972 * X ^ 2 + 9477 * X ^ 3 - 16038 * X ^ 4 + 7533 * X ^ 5 : ℚ⟦X⟧) = X ^ 2 * (-972 + 9477 * X - 16038 * X ^ 2 + 7533 * X ^ 3 : ℚ⟦X⟧) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 2 X_ne_zero) hd0
  have hPG : (3 - 6 * X + 3 * X ^ 2 : ℚ⟦X⟧) + (-6 + 14 * X - 8 * X ^ 2 : ℚ⟦X⟧) * G + (3 - 9 * X + 9 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hres
    exact hdisc hres.symm
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (-1 + 2 * X - X ^ 2 : ℚ⟦X⟧) + (3 - 6 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G + (-3 + 7 * X - 4 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 - 3 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0) :
    derivative ℚ (derivative ℚ G) * X * X * C 4 + derivative ℚ (derivative ℚ G) * X * X * X * C 9 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-570) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 2579 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-4899) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C 4272 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * C (-1395) + derivative ℚ G * X * C (-2) +
      derivative ℚ G * X * X * C (-100) + derivative ℚ G * X * X * X * C 830 +
      derivative ℚ G * X * X * X * X * C (-398) + derivative ℚ G * X * X * X * X * X * C (-4506) +
      derivative ℚ G * X * X * X * X * X * X * C 6966 + derivative ℚ G * X * X * X * X * X * X * X * C (-2790) +
      G * C 2 + G * X * C 52 +
      G * X * X * C (-510) + G * X * X * X * C 750 +
      G * X * X * X * X * C (-678) =
      C 2 + C 52 * X +
      C (-540) * X * X + C 900 * X * X * X +
      C (-414) * X * X * X * X := by
  have h := key G hP
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (-1 + 2 * X - X ^ 2 : ℚ⟦X⟧) + (3 - 6 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G + (-3 + 7 * X - 4 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 - 3 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0) (m : ℕ) :
    4 * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 9 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-570) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 2579 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-4899) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + 4272 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-1395) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + (-2) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-100) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 830 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-398) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-4506) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      6966 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-2790) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      2 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 52 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-510) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 750 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-678) * coeff (m + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (-1 + 2 * X - X ^ 2 : ℚ⟦X⟧) + (3 - 6 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G + (-3 + 7 * X - 4 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 - 3 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0) :
    120 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 180 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-6840) * coeff (0 + 1 + 1 + 1 + 1) G + 15474 * coeff (0 + 1 + 1 + 1) G +
      (-9798) * coeff (0 + 1 + 1) G + (-12) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-500) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 3320 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-1194) * coeff (0 + 1 + 1 + 1) G + (-9012) * coeff (0 + 1 + 1) G +
      6966 * coeff (0 + 1) G + 2 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      52 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-510) * coeff (0 + 1 + 1 + 1 + 1) G +
      750 * coeff (0 + 1 + 1 + 1) G + (-678) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (-1 + 2 * X - X ^ 2 : ℚ⟦X⟧) + (3 - 6 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G + (-3 + 7 * X - 4 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 - 3 * X + 3 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0) :
    168 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 270 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-11400) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 30948 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-29394) * coeff (0 + 1 + 1 + 1) G + 8544 * coeff (0 + 1 + 1) G +
      (-14) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-600) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      4150 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-1592) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-13518) * coeff (0 + 1 + 1 + 1) G + 13932 * coeff (0 + 1 + 1) G +
      (-2790) * coeff (0 + 1) G + 2 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      52 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-510) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      750 * coeff (0 + 1 + 1 + 1 + 1) G + (-678) * coeff (0 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A186185Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a186185.main := by
  intro T G hT hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 6, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m := rfl
  rw [e1, e2, e3, e4, e5, e6]
  have hN1 : ((1) + (-1) * PowerSeries.X + (-1) * PowerSeries.X * T : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [] at h'
  have hM : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 1) * (((1) + (-1) * PowerSeries.X + (-1) * PowerSeries.X * T) ^ 3 * ((-1 + 2 * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries ℚ) + (3 - 6 * PowerSeries.X + 3 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G + (-3 + 7 * PowerSeries.X - 4 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (1 - 3 * PowerSeries.X + 3 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 3)) = 0 := by
    linear_combination ((1) * PowerSeries.X ^ 3 + (-2) * PowerSeries.X ^ 4 + (1) * PowerSeries.X ^ 5) * hT +
      ((-1) * PowerSeries.X + (2) * PowerSeries.X * G + (-1) * PowerSeries.X * G ^ 2 + (4) * PowerSeries.X ^ 2 + (3) * PowerSeries.X ^ 2 * T + (-8) * PowerSeries.X ^ 2 * G + (-5) * PowerSeries.X ^ 2 * G * T + (5) * PowerSeries.X ^ 2 * G ^ 2 + (2) * PowerSeries.X ^ 2 * G ^ 2 * T + (-7) * PowerSeries.X ^ 3 + (-8) * PowerSeries.X ^ 3 * T + (-3) * PowerSeries.X ^ 3 * T ^ 2 + (11) * PowerSeries.X ^ 3 * G + (16) * PowerSeries.X ^ 3 * G * T + (3) * PowerSeries.X ^ 3 * G * T ^ 2 + (-10) * PowerSeries.X ^ 3 * G ^ 2 + (-8) * PowerSeries.X ^ 3 * G ^ 2 * T + (-1) * PowerSeries.X ^ 3 * G ^ 2 * T ^ 2 + (6) * PowerSeries.X ^ 4 + (7) * PowerSeries.X ^ 4 * T + (6) * PowerSeries.X ^ 4 * T ^ 2 + (-6) * PowerSeries.X ^ 4 * G + (-16) * PowerSeries.X ^ 4 * G * T + (-7) * PowerSeries.X ^ 4 * G * T ^ 2 + (9) * PowerSeries.X ^ 4 * G ^ 2 + (12) * PowerSeries.X ^ 4 * G ^ 2 * T + (3) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 2 + (-2) * PowerSeries.X ^ 5 + (-2) * PowerSeries.X ^ 5 * T + (-3) * PowerSeries.X ^ 5 * T ^ 2 + (1) * PowerSeries.X ^ 5 * G + (5) * PowerSeries.X ^ 5 * G * T + (4) * PowerSeries.X ^ 5 * G * T ^ 2 + (-3) * PowerSeries.X ^ 5 * G ^ 2 + (-6) * PowerSeries.X ^ 5 * G ^ 2 * T + (-3) * PowerSeries.X ^ 5 * G ^ 2 * T ^ 2) * hG
  have hLne : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 1) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero 1 PowerSeries.X_ne_zero)
  have hP : (-1 + 2 * PowerSeries.X - PowerSeries.X ^ 2 : PowerSeries ℚ) + (3 - 6 * PowerSeries.X + 3 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G + (-3 + 7 * PowerSeries.X - 4 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (1 - 3 * PowerSeries.X + 3 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 3 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hM).resolve_left hLne)).resolve_left (pow_ne_zero 3 hN1)
  cases m with
  | zero =>
    have r := A186185Aux.relE0 G hP
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A186185Aux.relE1 G hP
      push_cast
      linear_combination r
    | succ m =>
      have r := A186185Aux.rel G hP m
      push_cast
      linear_combination r
