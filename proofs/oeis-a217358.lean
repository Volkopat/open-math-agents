import OMAStatements.S_oeis_a217358

-- Problem: A217358: Series reversion of x-x^3-x^4.
-- Upstream: formal-conjectures statements/oeis-a217358.lean:0 (declaration OMA.S_oeis_a217358.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A217358Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (-X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-1 : ℚ⟦X⟧) * G ^ 3 + (-1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (46 * X ^ 3 - 11 * X ^ 4 - 336 * X ^ 5 - 347 * X ^ 6 + 256 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (41 * X ^ 3 - 993 * X ^ 4 - 1974 * X ^ 5 + 896 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-298 * X ^ 3 - 1370 * X ^ 4 + 368 * X ^ 5) * derivative ℚ G + (88 * X ^ 3 - 8 * X ^ 4) * G =
      -22 * X ^ 3 + 2 * X ^ 4 := by
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have hp0 : (-1 * X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-1 : ℚ⟦X⟧) * G * G * G + (-1 : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-1 * X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-1 : ℚ⟦X⟧) * G * G * G + (-1 : ℚ⟦X⟧) * G * G * G * G) =
      (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) := by
    simp [Derivation.leibniz]
    ring
  have hd1 : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-3 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * (derivative ℚ G) + (-3 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G)) =
      (1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-6 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (-4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d3, d4]
    ring
  have hd2 : (1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-6 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (-4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) = 0 := by rw [← hL2, hp1, map_zero]
  have hp2 : (1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-6 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (-3 : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (-12 : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) = 0 := by linear_combination hd2
  have hL3 : derivative ℚ ((1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-6 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (-3 : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (-12 : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G))) =
      (1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-6 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (-18 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (-3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) := by
    simp [Derivation.leibniz, d3, d4, d6, d12]
    ring
  have hd3 : (1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-6 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (-18 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (-3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) = 0 := by rw [← hL3, hp2, map_zero]
  have hfull : ((1 : ℚ⟦X⟧) + (-3 : ℚ⟦X⟧) * G ^ 2 + (-4 : ℚ⟦X⟧) * G ^ 3) ^ 5 * ((46 * X ^ 3 - 11 * X ^ 4 - 336 * X ^ 5 - 347 * X ^ 6 + 256 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (41 * X ^ 3 - 993 * X ^ 4 - 1974 * X ^ 5 + 896 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-298 * X ^ 3 - 1370 * X ^ 4 + 368 * X ^ 5) * derivative ℚ G + (88 * X ^ 3 - 8 * X ^ 4) * G - (-22 * X ^ 3 + 2 * X ^ 4)) = 0 := by
    linear_combination ((1438 * X ^ 3 + 1648 * X ^ 4 + 2082 * X ^ 5 - 1536 * X ^ 6 : ℚ⟦X⟧) + (7878 * X ^ 3 + 21990 * X ^ 4 + 1416 * X ^ 5 - 6144 * X ^ 6 : ℚ⟦X⟧) * G + (18426 * X ^ 3 + 59760 * X ^ 4 + 14334 * X ^ 5 - 23040 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (3980 * X ^ 3 + 59972 * X ^ 4 + 127344 * X ^ 5 - 86016 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 + (-5130 * X ^ 3 - 20010 * X ^ 4 + 145776 * X ^ 5 - 86016 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 + (55014 * X ^ 3 - 5874 * X ^ 4 - 19200 * X ^ 5 : ℚ⟦X⟧) * G ^ 5 + (109890 * X ^ 3 + 340986 * X ^ 4 - 116736 * X ^ 5 : ℚ⟦X⟧) * G ^ 6 + (87456 * X ^ 3 + 527136 * X ^ 4 - 172032 * X ^ 5 : ℚ⟦X⟧) * G ^ 7 + (54816 * X ^ 3 + 262560 * X ^ 4 - 86016 * X ^ 5 : ℚ⟦X⟧) * G ^ 8 + (163328 * X ^ 3 - 14848 * X ^ 4 : ℚ⟦X⟧) * G ^ 9 + (321024 * X ^ 3 - 29184 * X ^ 4 : ℚ⟦X⟧) * G ^ 10 + (270336 * X ^ 3 - 24576 * X ^ 4 : ℚ⟦X⟧) * G ^ 11 + (90112 * X ^ 3 - 8192 * X ^ 4 : ℚ⟦X⟧) * G ^ 12) * hP +
      ((-22 * X ^ 3 - 1436 * X ^ 4 - 1648 * X ^ 5 - 2082 * X ^ 6 + 1536 * X ^ 7 : ℚ⟦X⟧) + (276 * X ^ 3 - 66 * X ^ 4 - 2016 * X ^ 5 - 2082 * X ^ 6 + 1536 * X ^ 7 : ℚ⟦X⟧) * (derivative ℚ G) + (276 * X ^ 3 - 66 * X ^ 4 - 2016 * X ^ 5 - 2082 * X ^ 6 + 1536 * X ^ 7 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (1350 * X ^ 3 - 6222 * X ^ 4 - 19908 * X ^ 5 - 2952 * X ^ 6 + 6144 * X ^ 7 : ℚ⟦X⟧) * G + (1350 * X ^ 3 - 6222 * X ^ 4 - 19908 * X ^ 5 - 2952 * X ^ 6 + 6144 * X ^ 7 : ℚ⟦X⟧) * G * (derivative ℚ G) + (1104 * X ^ 3 - 264 * X ^ 4 - 8064 * X ^ 5 - 8328 * X ^ 6 + 6144 * X ^ 7 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (8208 * X ^ 3 + 3534 * X ^ 4 - 58344 * X ^ 5 - 20478 * X ^ 6 + 23040 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 + (3804 * X ^ 3 - 12708 * X ^ 4 - 47880 * X ^ 5 - 14232 * X ^ 6 + 18432 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (2484 * X ^ 3 - 594 * X ^ 4 - 18144 * X ^ 5 - 18738 * X ^ 6 + 13824 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (18748 * X ^ 3 + 53972 * X ^ 4 - 47720 * X ^ 5 - 148848 * X ^ 6 + 86016 * X ^ 7 : ℚ⟦X⟧) * G ^ 3 + (8826 * X ^ 3 + 50982 * X ^ 4 + 25956 * X ^ 5 - 131664 * X ^ 6 + 61440 * X ^ 7 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (6624 * X ^ 3 - 1584 * X ^ 4 - 48384 * X ^ 5 - 49968 * X ^ 6 + 36864 * X ^ 7 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) ^ 2 + (-5556 * X ^ 3 + 41484 * X ^ 4 + 143856 * X ^ 5 - 224112 * X ^ 6 + 86016 * X ^ 7 : ℚ⟦X⟧) * G ^ 4 + (-8760 * X ^ 3 + 179070 * X ^ 4 + 365400 * X ^ 5 - 150870 * X ^ 6 - 7680 * X ^ 7 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (-15732 * X ^ 3 + 3762 * X ^ 4 + 114912 * X ^ 5 + 118674 * X ^ 6 - 87552 * X ^ 7 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) ^ 2 + (-44634 * X ^ 3 - 155574 * X ^ 4 + 135900 * X ^ 5 - 37632 * X ^ 6 : ℚ⟦X⟧) * G ^ 5 + (-62190 * X ^ 3 - 2826 * X ^ 4 + 424116 * X ^ 5 + 490824 * X ^ 6 - 350208 * X ^ 7 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-109296 * X ^ 3 + 26136 * X ^ 4 + 798336 * X ^ 5 + 824472 * X ^ 6 - 608256 * X ^ 7 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) ^ 2 + (13908 * X ^ 3 - 233796 * X ^ 4 - 501864 * X ^ 5 + 225792 * X ^ 6 : ℚ⟦X⟧) * G ^ 6 + (-77196 * X ^ 3 - 724836 * X ^ 4 - 702072 * X ^ 5 + 1493520 * X ^ 6 - 602112 * X ^ 7 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (-148212 * X ^ 3 + 35442 * X ^ 4 + 1082592 * X ^ 5 + 1118034 * X ^ 6 - 824832 * X ^ 7 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) ^ 2 + (144480 * X ^ 3 + 210528 * X ^ 4 - 916992 * X ^ 5 + 344064 * X ^ 6 : ℚ⟦X⟧) * G ^ 7 + (-21234 * X ^ 3 - 968286 * X ^ 4 - 1502676 * X ^ 5 + 1353408 * X ^ 6 - 344064 * X ^ 7 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (132480 * X ^ 3 - 31680 * X ^ 4 - 967680 * X ^ 5 - 999360 * X ^ 6 + 737280 * X ^ 7 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) ^ 2 + (155382 * X ^ 3 + 487494 * X ^ 4 - 561168 * X ^ 5 + 172032 * X ^ 6 : ℚ⟦X⟧) * G ^ 8 + (-16236 * X ^ 3 + 393228 * X ^ 4 + 781704 * X ^ 5 - 354816 * X ^ 6 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (576288 * X ^ 3 - 137808 * X ^ 4 - 4209408 * X ^ 5 - 4347216 * X ^ 6 + 3207168 * X ^ 7 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) ^ 2 + (-52448 * X ^ 3 - 241120 * X ^ 4 + 64768 * X ^ 5 : ℚ⟦X⟧) * G ^ 9 + (-88560 * X ^ 3 + 2144880 * X ^ 4 + 4263840 * X ^ 5 - 1935360 * X ^ 6 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (618240 * X ^ 3 - 147840 * X ^ 4 - 4515840 * X ^ 5 - 4663680 * X ^ 6 + 3440640 * X ^ 7 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) ^ 2 + (-257472 * X ^ 3 - 1183680 * X ^ 4 + 317952 * X ^ 5 : ℚ⟦X⟧) * G ^ 10 + (-86592 * X ^ 3 + 2097216 * X ^ 4 + 4169088 * X ^ 5 - 1892352 * X ^ 6 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (247296 * X ^ 3 - 59136 * X ^ 4 - 1806336 * X ^ 5 - 1865472 * X ^ 6 + 1376256 * X ^ 7 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) ^ 2 + (-228864 * X ^ 3 - 1052160 * X ^ 4 + 282624 * X ^ 5 : ℚ⟦X⟧) * G ^ 11 + (-31488 * X ^ 3 + 762624 * X ^ 4 + 1516032 * X ^ 5 - 688128 * X ^ 6 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (-76288 * X ^ 3 - 350720 * X ^ 4 + 94208 * X ^ 5 : ℚ⟦X⟧) * G ^ 12) * hd1 +
      ((41 * X ^ 3 - 993 * X ^ 4 - 1974 * X ^ 5 + 896 * X ^ 6 : ℚ⟦X⟧) + (828 * X ^ 3 - 198 * X ^ 4 - 6048 * X ^ 5 - 6246 * X ^ 6 + 4608 * X ^ 7 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-492 * X ^ 3 + 11916 * X ^ 4 + 23688 * X ^ 5 - 10752 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (1656 * X ^ 3 - 396 * X ^ 4 - 12096 * X ^ 5 - 12492 * X ^ 6 + 9216 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-656 * X ^ 3 + 15888 * X ^ 4 + 31584 * X ^ 5 - 14336 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 + (-7452 * X ^ 3 + 1782 * X ^ 4 + 54432 * X ^ 5 + 56214 * X ^ 6 - 41472 * X ^ 7 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (2214 * X ^ 3 - 53622 * X ^ 4 - 106596 * X ^ 5 + 48384 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 + (-24840 * X ^ 3 + 5940 * X ^ 4 + 181440 * X ^ 5 + 187380 * X ^ 6 - 138240 * X ^ 7 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (5904 * X ^ 3 - 142992 * X ^ 4 - 284256 * X ^ 5 + 129024 * X ^ 6 : ℚ⟦X⟧) * G ^ 5 + (2484 * X ^ 3 - 594 * X ^ 4 - 18144 * X ^ 5 - 18738 * X ^ 6 + 13824 * X ^ 7 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-492 * X ^ 3 + 11916 * X ^ 4 + 23688 * X ^ 5 - 10752 * X ^ 6 : ℚ⟦X⟧) * G ^ 6 + (104328 * X ^ 3 - 24948 * X ^ 4 - 762048 * X ^ 5 - 786996 * X ^ 6 + 580608 * X ^ 7 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (-17712 * X ^ 3 + 428976 * X ^ 4 + 852768 * X ^ 5 - 387072 * X ^ 6 : ℚ⟦X⟧) * G ^ 7 + (136620 * X ^ 3 - 32670 * X ^ 4 - 997920 * X ^ 5 - 1030590 * X ^ 6 + 760320 * X ^ 7 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (-20295 * X ^ 3 + 491535 * X ^ 4 + 977130 * X ^ 5 - 443520 * X ^ 6 : ℚ⟦X⟧) * G ^ 8 + (-54648 * X ^ 3 + 13068 * X ^ 4 + 399168 * X ^ 5 + 412236 * X ^ 6 - 304128 * X ^ 7 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (7216 * X ^ 3 - 174768 * X ^ 4 - 347424 * X ^ 5 + 157696 * X ^ 6 : ℚ⟦X⟧) * G ^ 9 + (-298080 * X ^ 3 + 71280 * X ^ 4 + 2177280 * X ^ 5 + 2248560 * X ^ 6 - 1658880 * X ^ 7 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (35424 * X ^ 3 - 857952 * X ^ 4 - 1705536 * X ^ 5 + 774144 * X ^ 6 : ℚ⟦X⟧) * G ^ 10 + (-291456 * X ^ 3 + 69696 * X ^ 4 + 2128896 * X ^ 5 + 2198592 * X ^ 6 - 1622016 * X ^ 7 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (31488 * X ^ 3 - 762624 * X ^ 4 - 1516032 * X ^ 5 + 688128 * X ^ 6 : ℚ⟦X⟧) * G ^ 11 + (-105984 * X ^ 3 + 25344 * X ^ 4 + 774144 * X ^ 5 + 799488 * X ^ 6 - 589824 * X ^ 7 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (10496 * X ^ 3 - 254208 * X ^ 4 - 505344 * X ^ 5 + 229376 * X ^ 6 : ℚ⟦X⟧) * G ^ 12) * hd2 +
      ((46 * X ^ 3 - 11 * X ^ 4 - 336 * X ^ 5 - 347 * X ^ 6 + 256 * X ^ 7 : ℚ⟦X⟧) + (-552 * X ^ 3 + 132 * X ^ 4 + 4032 * X ^ 5 + 4164 * X ^ 6 - 3072 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 + (-736 * X ^ 3 + 176 * X ^ 4 + 5376 * X ^ 5 + 5552 * X ^ 6 - 4096 * X ^ 7 : ℚ⟦X⟧) * G ^ 3 + (2484 * X ^ 3 - 594 * X ^ 4 - 18144 * X ^ 5 - 18738 * X ^ 6 + 13824 * X ^ 7 : ℚ⟦X⟧) * G ^ 4 + (6624 * X ^ 3 - 1584 * X ^ 4 - 48384 * X ^ 5 - 49968 * X ^ 6 + 36864 * X ^ 7 : ℚ⟦X⟧) * G ^ 5 + (-552 * X ^ 3 + 132 * X ^ 4 + 4032 * X ^ 5 + 4164 * X ^ 6 - 3072 * X ^ 7 : ℚ⟦X⟧) * G ^ 6 + (-19872 * X ^ 3 + 4752 * X ^ 4 + 145152 * X ^ 5 + 149904 * X ^ 6 - 110592 * X ^ 7 : ℚ⟦X⟧) * G ^ 7 + (-22770 * X ^ 3 + 5445 * X ^ 4 + 166320 * X ^ 5 + 171765 * X ^ 6 - 126720 * X ^ 7 : ℚ⟦X⟧) * G ^ 8 + (8096 * X ^ 3 - 1936 * X ^ 4 - 59136 * X ^ 5 - 61072 * X ^ 6 + 45056 * X ^ 7 : ℚ⟦X⟧) * G ^ 9 + (39744 * X ^ 3 - 9504 * X ^ 4 - 290304 * X ^ 5 - 299808 * X ^ 6 + 221184 * X ^ 7 : ℚ⟦X⟧) * G ^ 10 + (35328 * X ^ 3 - 8448 * X ^ 4 - 258048 * X ^ 5 - 266496 * X ^ 6 + 196608 * X ^ 7 : ℚ⟦X⟧) * G ^ 11 + (11776 * X ^ 3 - 2816 * X ^ 4 - 86016 * X ^ 5 - 88832 * X ^ 6 + 65536 * X ^ 7 : ℚ⟦X⟧) * G ^ 12) * hd3
  have k3 : constantCoeff (3 : ℚ⟦X⟧) = 3 := cnum 3
  have k4 : constantCoeff (4 : ℚ⟦X⟧) = 4 := cnum 4
  have hPG : (1 : ℚ⟦X⟧) + (-3 : ℚ⟦X⟧) * G ^ 2 + (-4 : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k3, k4] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 5 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (-X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-1 : ℚ⟦X⟧) * G ^ 3 + (-1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 46 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-11) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C (-336) + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C (-347) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * C 256 + derivative ℚ (derivative ℚ G) * X * X * X * C 41 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-993) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-1974) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 896 + derivative ℚ G * X * X * X * C (-298) +
      derivative ℚ G * X * X * X * X * C (-1370) + derivative ℚ G * X * X * X * X * X * C 368 +
      G * X * X * X * C 88 + G * X * X * X * X * C (-8) =
      C (-22) * X * X * X + C 2 * X * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (-X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-1 : ℚ⟦X⟧) * G ^ 3 + (-1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    46 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-11) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-336) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-347) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      256 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + 41 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-993) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-1974) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      896 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + (-298) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-1370) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 368 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      88 * coeff (m + 1 + 1 + 1 + 1) G + (-8) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (-X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-1 : ℚ⟦X⟧) * G ^ 3 + (-1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    2760 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-264) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-2016) * coeff (0 + 1 + 1 + 1) G + 492 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-5958) * coeff (0 + 1 + 1 + 1) G + (-3948) * coeff (0 + 1 + 1) G +
      (-894) * coeff (0 + 1 + 1 + 1) G + (-2740) * coeff (0 + 1 + 1) G +
      368 * coeff (0 + 1) G + 88 * coeff (0 + 1 + 1) G +
      (-8) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (-X : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * G + (-1 : ℚ⟦X⟧) * G ^ 3 + (-1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    5520 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-660) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-8064) * coeff (0 + 1 + 1 + 1 + 1) G + (-2082) * coeff (0 + 1 + 1 + 1) G +
      820 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-11916) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-11844) * coeff (0 + 1 + 1 + 1) G + 1792 * coeff (0 + 1 + 1) G +
      (-1192) * coeff (0 + 1 + 1 + 1 + 1) G + (-4110) * coeff (0 + 1 + 1 + 1) G +
      736 * coeff (0 + 1 + 1) G + 88 * coeff (0 + 1 + 1 + 1) G +
      (-8) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A217358Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a217358.main := by
  intro G h0 hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  rw [e1, e2, e3, e4]
  have hP : (-PowerSeries.X : PowerSeries ℚ) + (1 : PowerSeries ℚ) * G + (-1 : PowerSeries ℚ) * G ^ 3 + (-1 : PowerSeries ℚ) * G ^ 4 = 0 := by
    linear_combination hG
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A217358Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A217358Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A217358Aux.rel G hP h0c m
      push_cast
      linear_combination r
