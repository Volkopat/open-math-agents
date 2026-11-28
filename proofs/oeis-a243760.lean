import OMAStatements.S_oeis_a243760

-- Problem: A243760: Expansion of (sqrt(8*x+4*sqrt(1-4*x)-3)-1)/(2*sqrt(1-4*x)-2).
-- Upstream: formal-conjectures statements/oeis-a243760.lean:0 (declaration OMA.S_oeis_a243760.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A243760Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (1 + 4 * X : ℚ⟦X⟧) * G ^ 2 + (-2 : ℚ⟦X⟧) * G ^ 3 + (4 * X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (245 * X ^ 3 - 3920 * X ^ 4 + 23248 * X ^ 5 - 53888 * X ^ 6 - 19456 * X ^ 7 + 303104 * X ^ 8 - 393216 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (735 * X ^ 2 - 12180 * X ^ 3 + 66528 * X ^ 4 - 86016 * X ^ 5 - 448512 * X ^ 6 + 1769472 * X ^ 7 - 1966080 * X ^ 8) * derivative ℚ (derivative ℚ G) + (-840 * X ^ 2 - 6012 * X ^ 3 + 142080 * X ^ 4 - 708096 * X ^ 5 + 1529856 * X ^ 6 - 1474560 * X ^ 7) * derivative ℚ G + (420 * X ^ 2 - 4176 * X ^ 3 + 7296 * X ^ 4 + 6144 * X ^ 5) * G =
      630 * X ^ 2 - 8112 * X ^ 3 + 24576 * X ^ 4 - 12288 * X ^ 5 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have hp0 : (1 * X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (1 + 4 * X : ℚ⟦X⟧) * G * G + (-2 : ℚ⟦X⟧) * G * G * G + (4 * X : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 * X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (1 + 4 * X : ℚ⟦X⟧) * G * G + (-2 : ℚ⟦X⟧) * G * G * G + (4 * X : ℚ⟦X⟧) * G * G * G * G) =
      (1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * (derivative ℚ G) + (2 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 2 + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (16 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 4 := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hd1 : (1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * (derivative ℚ G) + (2 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 2 + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (16 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 4 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * (derivative ℚ G) + (2 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G + (-6 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (16 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((1 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * (derivative ℚ G) + (2 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G + (-6 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (16 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * G) =
      (-1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (2 + 8 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (16 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-12 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (48 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (16 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (32 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d2, d4, d6, d8, d16]
    ring
  have hd2 : (-1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (2 + 8 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (2 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (16 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-12 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (48 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (16 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (32 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) = 0 := by rw [← hL2, hp1, map_zero]
  have hp2 : (-1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (2 + 8 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (2 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (16 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-12 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (48 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (16 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) + (32 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) = 0 := by linear_combination hd2
  have hL3 : derivative ℚ ((-1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (2 + 8 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (2 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (16 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-12 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (48 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (16 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) + (32 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G)) =
      (-1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (6 + 24 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-12 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (2 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (24 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-36 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (96 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (144 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (144 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (16 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (48 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d2, d6, d8, d12, d16, d32, d48]
    ring
  have hd3 : (-1 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (6 + 24 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-12 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (2 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (24 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-36 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (96 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (-6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (144 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (144 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (16 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (48 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) = 0 := by rw [← hL3, hp2, map_zero]
  have hfull : ((-1 : ℚ⟦X⟧) + (2 + 8 * X : ℚ⟦X⟧) * G + (-6 : ℚ⟦X⟧) * G ^ 2 + (16 * X : ℚ⟦X⟧) * G ^ 3) ^ 5 * ((245 * X ^ 3 - 3920 * X ^ 4 + 23248 * X ^ 5 - 53888 * X ^ 6 - 19456 * X ^ 7 + 303104 * X ^ 8 - 393216 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (735 * X ^ 2 - 12180 * X ^ 3 + 66528 * X ^ 4 - 86016 * X ^ 5 - 448512 * X ^ 6 + 1769472 * X ^ 7 - 1966080 * X ^ 8) * derivative ℚ (derivative ℚ G) + (-840 * X ^ 2 - 6012 * X ^ 3 + 142080 * X ^ 4 - 708096 * X ^ 5 + 1529856 * X ^ 6 - 1474560 * X ^ 7) * derivative ℚ G + (420 * X ^ 2 - 4176 * X ^ 3 + 7296 * X ^ 4 + 6144 * X ^ 5) * G - (630 * X ^ 2 - 8112 * X ^ 3 + 24576 * X ^ 4 - 12288 * X ^ 5)) = 0 := by
    linear_combination ((10500 * X ^ 2 - 82560 * X ^ 3 + 106944 * X ^ 4 - 130560 * X ^ 5 + 2700288 * X ^ 6 - 5283840 * X ^ 7 - 196608 * X ^ 8 - 20447232 * X ^ 9 + 75497472 * X ^ 10 : ℚ⟦X⟧) + (-81480 * X ^ 2 + 468096 * X ^ 3 + 1160832 * X ^ 4 - 5428224 * X ^ 5 - 12509184 * X ^ 6 + 18677760 * X ^ 7 + 110100480 * X ^ 8 - 251658240 * X ^ 9 : ℚ⟦X⟧) * G + (432600 * X ^ 2 - 2788608 * X ^ 3 - 2301312 * X ^ 4 + 9345024 * X ^ 5 + 97566720 * X ^ 6 - 208011264 * X ^ 7 + 243793920 * X ^ 8 - 377487360 * X ^ 9 + 1006632960 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 + (-1464960 * X ^ 2 + 8558208 * X ^ 3 + 17875968 * X ^ 4 - 69298176 * X ^ 5 - 107200512 * X ^ 6 - 344064000 * X ^ 7 + 1525678080 * X ^ 8 - 2768240640 * X ^ 9 : ℚ⟦X⟧) * G ^ 3 + (3941280 * X ^ 2 - 24575616 * X ^ 3 - 17932032 * X ^ 4 - 55418880 * X ^ 5 + 1147736064 * X ^ 6 - 1513783296 * X ^ 7 + 3031695360 * X ^ 8 - 2799697920 * X ^ 9 + 5536481280 * X ^ 10 : ℚ⟦X⟧) * G ^ 4 + (-7654080 * X ^ 2 + 41352960 * X ^ 3 + 111873024 * X ^ 4 - 307126272 * X ^ 5 + 46202880 * X ^ 6 - 5166858240 * X ^ 7 + 8304721920 * X ^ 8 - 12079595520 * X ^ 9 : ℚ⟦X⟧) * G ^ 5 + (12559680 * X ^ 2 - 78253056 * X ^ 3 + 30163968 * X ^ 4 - 1067753472 * X ^ 5 + 5568331776 * X ^ 6 - 5547491328 * X ^ 7 + 14218690560 * X ^ 8 - 10569646080 * X ^ 9 + 16106127360 * X ^ 10 : ℚ⟦X⟧) * G ^ 6 + (-13977600 * X ^ 2 + 58917888 * X ^ 3 + 305221632 * X ^ 4 - 847724544 * X ^ 5 + 3607756800 * X ^ 6 - 21626880000 * X ^ 7 + 22020096000 * X ^ 8 - 26172456960 * X ^ 9 : ℚ⟦X⟧) * G ^ 7 + (14736960 * X ^ 2 - 107954688 * X ^ 3 + 468636672 * X ^ 4 - 3989544960 * X ^ 5 + 11965415424 * X ^ 6 - 12138184704 * X ^ 7 + 32102154240 * X ^ 8 - 21516779520 * X ^ 9 + 26172456960 * X ^ 10 : ℚ⟦X⟧) * G ^ 8 + (-6410880 * X ^ 2 - 11725824 * X ^ 3 + 479373312 * X ^ 4 - 2172076032 * X ^ 5 + 12013142016 * X ^ 6 - 37009489920 * X ^ 7 + 28437381120 * X ^ 8 - 28185722880 * X ^ 9 : ℚ⟦X⟧) * G ^ 9 + (7620480 * X ^ 2 - 102144000 * X ^ 3 + 857475072 * X ^ 4 - 4486004736 * X ^ 5 + 10199236608 * X ^ 6 - 14797504512 * X ^ 7 + 35257319424 * X ^ 8 - 22548578304 * X ^ 9 + 22548578304 * X ^ 10 : ℚ⟦X⟧) * G ^ 10 + (-22579200 * X ^ 3 + 330301440 * X ^ 4 - 2503507968 * X ^ 5 + 11279794176 * X ^ 6 - 22743613440 * X ^ 7 + 14344519680 * X ^ 8 - 12079595520 * X ^ 9 : ℚ⟦X⟧) * G ^ 11 + (15052800 * X ^ 4 - 220200960 * X ^ 5 + 1669005312 * X ^ 6 - 7519862784 * X ^ 7 + 15162408960 * X ^ 8 - 9563013120 * X ^ 9 + 8053063680 * X ^ 10 : ℚ⟦X⟧) * G ^ 12) * hP +
      ((630 * X ^ 2 - 18612 * X ^ 3 + 107136 * X ^ 4 - 119232 * X ^ 5 + 130560 * X ^ 6 - 2700288 * X ^ 7 + 5283840 * X ^ 8 + 196608 * X ^ 9 + 20447232 * X ^ 10 - 75497472 * X ^ 11 : ℚ⟦X⟧) + (1470 * X ^ 2 - 12600 * X ^ 3 - 34944 * X ^ 4 + 588864 * X ^ 5 - 1399296 * X ^ 6 - 1225728 * X ^ 7 + 5283840 * X ^ 8 + 196608 * X ^ 9 + 20447232 * X ^ 10 - 75497472 * X ^ 11 : ℚ⟦X⟧) * (derivative ℚ G) + (23520 * X ^ 4 - 329280 * X ^ 5 + 1479168 * X ^ 6 - 709632 * X ^ 7 - 12214272 * X ^ 8 + 25362432 * X ^ 9 + 20447232 * X ^ 10 - 75497472 * X ^ 11 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (3780 * X ^ 2 + 59016 * X ^ 3 - 289728 * X ^ 4 - 2157696 * X ^ 5 + 8620032 * X ^ 6 + 7225344 * X ^ 7 - 18874368 * X ^ 8 - 130547712 * X ^ 9 + 327155712 * X ^ 10 : ℚ⟦X⟧) * G + (-17640 * X ^ 2 + 192360 * X ^ 3 - 239232 * X ^ 4 - 2797824 * X ^ 5 + 3463680 * X ^ 6 + 29718528 * X ^ 7 - 35364864 * X ^ 8 - 173211648 * X ^ 9 + 284688384 * X ^ 10 - 12582912 * X ^ 11 + 603979776 * X ^ 12 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-29400 * X ^ 3 + 282240 * X ^ 4 - 343680 * X ^ 5 - 3108864 * X ^ 6 + 2199552 * X ^ 7 + 31309824 * X ^ 8 + 24772608 * X ^ 9 - 336592896 * X ^ 10 - 25165824 * X ^ 11 + 1207959552 * X ^ 12 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-46200 * X ^ 2 - 240696 * X ^ 3 + 3177792 * X ^ 4 - 781440 * X ^ 5 - 12512256 * X ^ 6 - 81469440 * X ^ 7 + 318308352 * X ^ 8 - 475004928 * X ^ 9 + 301989888 * X ^ 10 - 1006632960 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 + (97020 * X ^ 2 - 1037400 * X ^ 3 + 368256 * X ^ 4 + 24854784 * X ^ 5 - 58297344 * X ^ 6 - 105007104 * X ^ 7 + 339492864 * X ^ 8 + 25559040 * X ^ 9 + 732954624 * X ^ 10 - 3774873600 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (205800 * X ^ 3 - 1975680 * X ^ 4 + 1841280 * X ^ 5 + 28535808 * X ^ 6 - 29822976 * X ^ 7 - 357433344 * X ^ 8 + 653721600 * X ^ 9 + 1174929408 * X ^ 10 - 1950351360 * X ^ 11 - 1107296256 * X ^ 12 - 4831838208 * X ^ 13 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (288960 * X ^ 2 - 373248 * X ^ 3 - 6022656 * X ^ 4 - 16763904 * X ^ 5 + 137109504 * X ^ 6 - 191496192 * X ^ 7 + 541065216 * X ^ 8 - 1610612736 * X ^ 9 + 3623878656 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 + (-382200 * X ^ 2 + 4499040 * X ^ 3 - 7815360 * X ^ 4 - 57200640 * X ^ 5 + 100724736 * X ^ 6 + 539418624 * X ^ 7 - 660553728 * X ^ 8 - 4155899904 * X ^ 9 + 8546942976 * X ^ 10 - 679477248 * X ^ 11 + 6845104128 * X ^ 12 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-823200 * X ^ 3 + 7714560 * X ^ 4 - 2849280 * X ^ 5 - 162103296 * X ^ 6 + 411893760 * X ^ 7 + 349569024 * X ^ 8 - 500170752 * X ^ 9 - 4706009088 * X ^ 10 - 3019898880 * X ^ 11 + 28991029248 * X ^ 12 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) ^ 2 + (-1013040 * X ^ 2 + 2538720 * X ^ 3 + 20931840 * X ^ 4 - 45639936 * X ^ 5 + 144396288 * X ^ 6 - 1180078080 * X ^ 7 + 2857795584 * X ^ 8 - 5252579328 * X ^ 9 + 2095054848 * X ^ 10 - 5536481280 * X ^ 11 : ℚ⟦X⟧) * G ^ 4 + (970200 * X ^ 2 - 10726800 * X ^ 3 + 4945920 * X ^ 4 + 254027520 * X ^ 5 - 589019136 * X ^ 6 - 1292378112 * X ^ 7 + 5004656640 * X ^ 8 - 3795320832 * X ^ 9 + 9298771968 * X ^ 10 - 35634806784 * X ^ 11 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (2116800 * X ^ 3 - 20039040 * X ^ 4 + 21358080 * X ^ 5 + 205461504 * X ^ 6 + 356327424 * X ^ 7 - 5674106880 * X ^ 8 + 7863533568 * X ^ 9 + 19383975936 * X ^ 10 - 36389781504 * X ^ 11 + 1207959552 * X ^ 12 - 57982058496 * X ^ 13 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) ^ 2 + (2627520 * X ^ 2 - 11949888 * X ^ 3 + 2333184 * X ^ 4 - 158505984 * X ^ 5 + 899088384 * X ^ 6 - 2252341248 * X ^ 7 + 6741295104 * X ^ 8 - 9097445376 * X ^ 9 + 16307453952 * X ^ 10 : ℚ⟦X⟧) * G ^ 5 + (-1905120 * X ^ 2 + 21856800 * X ^ 3 - 29479296 * X ^ 4 - 298719744 * X ^ 5 + 303654912 * X ^ 6 + 2836168704 * X ^ 7 + 999751680 * X ^ 8 - 36234067968 * X ^ 9 + 61845012480 * X ^ 10 - 3523215360 * X ^ 11 + 33822867456 * X ^ 12 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-3175200 * X ^ 3 + 21450240 * X ^ 4 + 102873600 * X ^ 5 - 1183739904 * X ^ 6 + 2807119872 * X ^ 7 - 907149312 * X ^ 8 + 5766119424 * X ^ 9 - 22422749184 * X ^ 10 - 73685532672 * X ^ 11 + 231928233984 * X ^ 12 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) ^ 2 + (-4579680 * X ^ 2 + 20005824 * X ^ 3 + 41637888 * X ^ 4 - 310201344 * X ^ 5 + 1868881920 * X ^ 6 - 7447904256 * X ^ 7 + 12935233536 * X ^ 8 - 22259171328 * X ^ 9 + 8355053568 * X ^ 10 - 16106127360 * X ^ 11 : ℚ⟦X⟧) * G ^ 6 + (2222640 * X ^ 2 - 18886560 * X ^ 3 - 75038208 * X ^ 4 + 927327744 * X ^ 5 - 1037242368 * X ^ 6 - 7827308544 * X ^ 7 + 23226089472 * X ^ 8 - 27182235648 * X ^ 9 + 63493373952 * X ^ 10 - 153410863104 * X ^ 11 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (3175200 * X ^ 3 - 20321280 * X ^ 4 - 20835840 * X ^ 5 - 358920192 * X ^ 6 + 7406518272 * X ^ 7 - 28853403648 * X ^ 8 + 16559112192 * X ^ 9 + 105897787392 * X ^ 10 - 161866579968 * X ^ 11 + 83751862272 * X ^ 12 - 309237645312 * X ^ 13 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) ^ 2 + (6249600 * X ^ 2 - 39903744 * X ^ 3 + 130572288 * X ^ 4 - 875655168 * X ^ 5 + 3493429248 * X ^ 6 - 10051387392 * X ^ 7 + 26581401600 * X ^ 8 - 28387049472 * X ^ 9 + 37044092928 * X ^ 10 : ℚ⟦X⟧) * G ^ 7 + (-1905120 * X ^ 2 + 14918400 * X ^ 3 + 57625344 * X ^ 4 - 439486464 * X ^ 5 - 1125691392 * X ^ 6 + 5144739840 * X ^ 7 + 25365970944 * X ^ 8 - 133608505344 * X ^ 9 + 183987339264 * X ^ 10 - 29997662208 * X ^ 11 + 86973087744 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (-40642560 * X ^ 4 + 550932480 * X ^ 5 - 2700509184 * X ^ 6 + 6448545792 * X ^ 7 - 16057368576 * X ^ 8 + 52961476608 * X ^ 9 - 23253221376 * X ^ 10 - 376883380224 * X ^ 11 + 695784701952 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) ^ 2 + (-5110560 * X ^ 2 + 21467328 * X ^ 3 + 91370496 * X ^ 4 - 1070871552 * X ^ 5 + 6591406080 * X ^ 6 - 20487585792 * X ^ 7 + 31333416960 * X ^ 8 - 44534071296 * X ^ 9 + 19100860416 * X ^ 10 - 26172456960 * X ^ 11 : ℚ⟦X⟧) * G ^ 8 + (17357760 * X ^ 3 - 261058560 * X ^ 4 + 1043312640 * X ^ 5 + 826146816 * X ^ 6 - 14320680960 * X ^ 7 + 39904739328 * X ^ 8 - 88555388928 * X ^ 9 + 212525383680 * X ^ 10 - 300781928448 * X ^ 11 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (196439040 * X ^ 5 - 3034644480 * X ^ 6 + 17339498496 * X ^ 7 - 39859126272 * X ^ 8 + 1698693120 * X ^ 9 + 139066343424 * X ^ 10 - 215620780032 * X ^ 11 + 362387865600 * X ^ 12 - 695784701952 * X ^ 13 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) ^ 2 + (3810240 * X ^ 2 - 39016320 * X ^ 3 + 296064000 * X ^ 4 - 1799620608 * X ^ 5 + 6698532864 * X ^ 6 - 20072103936 * X ^ 7 + 45260734464 * X ^ 8 - 45474643968 * X ^ 9 + 42278584320 * X ^ 10 : ℚ⟦X⟧) * G ^ 9 + (-41771520 * X ^ 4 + 721889280 * X ^ 5 - 3322134528 * X ^ 6 - 2742386688 * X ^ 7 + 61670817792 * X ^ 8 - 182920937472 * X ^ 9 + 220377120768 * X ^ 10 - 98448703488 * X ^ 11 + 112742891520 * X ^ 12 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (-421478400 * X ^ 6 + 6743654400 * X ^ 7 - 39993999360 * X ^ 8 + 92704604160 * X ^ 9 + 33470545920 * X ^ 10 - 521435873280 * X ^ 11 + 676457349120 * X ^ 12 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) ^ 2 + (-18910080 * X ^ 3 + 263531520 * X ^ 4 - 1899350016 * X ^ 5 + 8547680256 * X ^ 6 - 21507735552 * X ^ 7 + 32076988416 * X ^ 8 - 41070624768 * X ^ 9 + 22951231488 * X ^ 10 - 22548578304 * X ^ 11 : ℚ⟦X⟧) * G ^ 10 + (1505280 * X ^ 5 - 137625600 * X ^ 6 - 726564864 * X ^ 7 + 20119289856 * X ^ 8 - 105589506048 * X ^ 9 + 234394484736 * X ^ 10 - 215016800256 * X ^ 11 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (337182720 * X ^ 7 - 5394923520 * X ^ 8 + 31995199488 * X ^ 9 - 74163683328 * X ^ 10 - 26776436736 * X ^ 11 + 417148698624 * X ^ 12 - 541165879296 * X ^ 13 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) ^ 2 + (30105600 * X ^ 4 - 440401920 * X ^ 5 + 3131572224 * X ^ 6 - 13152288768 * X ^ 7 + 28865200128 * X ^ 8 - 28588376064 * X ^ 9 + 19327352832 * X ^ 10 : ℚ⟦X⟧) * G ^ 11 + (60211200 * X ^ 6 - 880803840 * X ^ 7 + 6345719808 * X ^ 8 - 28116516864 * X ^ 9 + 71923924992 * X ^ 10 - 94623498240 * X ^ 11 + 57982058496 * X ^ 12 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (-15052800 * X ^ 5 + 220200960 * X ^ 6 - 1558904832 * X ^ 7 + 6425149440 * X ^ 8 - 13249806336 * X ^ 9 + 11173625856 * X ^ 10 - 8053063680 * X ^ 11 : ℚ⟦X⟧) * G ^ 12) * hd1 +
      ((735 * X ^ 2 - 12180 * X ^ 3 + 66528 * X ^ 4 - 86016 * X ^ 5 - 448512 * X ^ 6 + 1769472 * X ^ 7 - 1966080 * X ^ 8 : ℚ⟦X⟧) + (1470 * X ^ 3 - 17640 * X ^ 4 + 45408 * X ^ 5 + 234624 * X ^ 6 - 1410048 * X ^ 7 + 1351680 * X ^ 8 + 4915200 * X ^ 9 - 9437184 * X ^ 10 : ℚ⟦X⟧) * (derivative ℚ G) + (-5880 * X ^ 2 + 79800 * X ^ 3 - 236544 * X ^ 4 - 882816 * X ^ 5 + 5047296 * X ^ 6 - 270336 * X ^ 7 - 33619968 * X ^ 8 + 53477376 * X ^ 9 : ℚ⟦X⟧) * G + (-17640 * X ^ 3 + 211680 * X ^ 4 - 686016 * X ^ 5 - 557568 * X ^ 6 + 3529728 * X ^ 7 + 14819328 * X ^ 8 - 47775744 * X ^ 9 - 61341696 * X ^ 10 + 226492416 * X ^ 11 : ℚ⟦X⟧) * G * (derivative ℚ G) + (35280 * X ^ 2 - 478800 * X ^ 3 + 1560384 * X ^ 4 + 2877696 * X ^ 5 - 18127872 * X ^ 6 - 368640 * X ^ 7 + 40697856 * X ^ 8 + 184025088 * X ^ 9 - 528482304 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 + (97020 * X ^ 3 - 987840 * X ^ 4 + 1021248 * X ^ 5 + 19805184 * X ^ 6 - 69580800 * X ^ 7 - 3907584 * X ^ 8 + 227082240 * X ^ 9 + 51904512 * X ^ 10 + 37748736 * X ^ 11 - 1811939328 * X ^ 12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-129360 * X ^ 2 + 1579200 * X ^ 3 - 2811648 * X ^ 4 - 25830912 * X ^ 5 + 83890176 * X ^ 6 + 111747072 * X ^ 7 - 661192704 * X ^ 8 + 520617984 * X ^ 9 - 113246208 * X ^ 10 + 2214592512 * X ^ 11 : ℚ⟦X⟧) * G ^ 3 + (-382200 * X ^ 3 + 3951360 * X ^ 4 - 7290240 * X ^ 5 - 33954816 * X ^ 6 + 15814656 * X ^ 7 + 703070208 * X ^ 8 - 1238827008 * X ^ 9 - 2609381376 * X ^ 10 + 5574230016 * X ^ 11 + 1107296256 * X ^ 12 + 4831838208 * X ^ 13 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (382200 * X ^ 2 - 4710720 * X ^ 3 + 10214400 * X ^ 4 + 52167168 * X ^ 5 - 138117120 * X ^ 6 - 340623360 * X ^ 7 + 428408832 * X ^ 8 + 3829923840 * X ^ 9 - 7713325056 * X ^ 10 - 905969664 * X ^ 11 - 3221225472 * X ^ 12 : ℚ⟦X⟧) * G ^ 4 + (970200 * X ^ 3 - 8467200 * X ^ 4 - 6721920 * X ^ 5 + 252933120 * X ^ 6 - 651202560 * X ^ 7 - 321454080 * X ^ 8 + 1085276160 * X ^ 9 + 4341104640 * X ^ 10 + 5284823040 * X ^ 11 - 36238786560 * X ^ 12 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (-776160 * X ^ 2 + 8628480 * X ^ 3 - 4935168 * X ^ 4 - 193941504 * X ^ 5 + 420175872 * X ^ 6 + 1194098688 * X ^ 7 - 4192468992 * X ^ 8 + 2585788416 * X ^ 9 - 5586812928 * X ^ 10 + 26575110144 * X ^ 11 : ℚ⟦X⟧) * G ^ 5 + (-1905120 * X ^ 3 + 17216640 * X ^ 4 - 12561408 * X ^ 5 - 162330624 * X ^ 6 - 711548928 * X ^ 7 + 6387793920 * X ^ 8 - 7325614080 * X ^ 9 - 23083352064 * X ^ 10 + 40013660160 * X ^ 11 - 1207959552 * X ^ 12 + 57982058496 * X ^ 13 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (1270080 * X ^ 2 - 14414400 * X ^ 3 + 18461184 * X ^ 4 + 194958336 * X ^ 5 - 142049280 * X ^ 6 - 2034597888 * X ^ 7 - 828112896 * X ^ 8 + 24933040128 * X ^ 9 - 41020293120 * X ^ 10 + 1610612736 * X ^ 11 - 25769803776 * X ^ 12 : ℚ⟦X⟧) * G ^ 6 + (2222640 * X ^ 3 - 11854080 * X ^ 4 - 113105664 * X ^ 5 + 1002129408 * X ^ 6 - 2165022720 * X ^ 7 + 697761792 * X ^ 8 - 6440878080 * X ^ 9 + 20346568704 * X ^ 10 + 67645734912 * X ^ 11 - 202937204736 * X ^ 12 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (-1270080 * X ^ 2 + 10886400 * X ^ 3 + 39545856 * X ^ 4 - 503341056 * X ^ 5 + 584368128 * X ^ 6 + 3765436416 * X ^ 7 - 10456399872 * X ^ 8 + 14042529792 * X ^ 9 - 47714402304 * X ^ 10 + 106300440576 * X ^ 11 : ℚ⟦X⟧) * G ^ 7 + (-1905120 * X ^ 3 + 10160640 * X ^ 4 + 26952192 * X ^ 5 + 297086976 * X ^ 6 - 5508661248 * X ^ 7 + 20537671680 * X ^ 8 - 10579083264 * X ^ 9 - 75119984640 * X ^ 10 + 110528299008 * X ^ 11 - 62813896704 * X ^ 12 + 231928233984 * X ^ 13 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (952560 * X ^ 2 - 8164800 * X ^ 3 - 12160512 * X ^ 4 + 73009152 * X ^ 5 + 1151631360 * X ^ 6 - 3461677056 * X ^ 7 - 13306429440 * X ^ 8 + 69457674240 * X ^ 9 - 94824824832 * X ^ 10 + 31406948352 * X ^ 11 - 77309411328 * X ^ 12 : ℚ⟦X⟧) * G ^ 8 + (22861440 * X ^ 4 - 304819200 * X ^ 5 + 1464846336 * X ^ 6 - 3578757120 * X ^ 7 + 10485891072 * X ^ 8 - 36153851904 * X ^ 9 + 17213423616 * X ^ 10 + 237364051968 * X ^ 11 - 434865438720 * X ^ 12 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (-7620480 * X ^ 3 + 114186240 * X ^ 4 - 476510208 * X ^ 5 + 13910016 * X ^ 6 + 3859808256 * X ^ 7 - 11632902144 * X ^ 8 + 40944795648 * X ^ 9 - 127439732736 * X ^ 10 + 177167400960 * X ^ 11 : ℚ⟦X⟧) * G ^ 9 + (-101606400 * X ^ 5 + 1565491200 * X ^ 6 - 8918876160 * X ^ 7 + 20488519680 * X ^ 8 - 1541406720 * X ^ 9 - 67947724800 * X ^ 10 + 107709726720 * X ^ 11 - 201326592000 * X ^ 12 + 386547056640 * X ^ 13 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (20321280 * X ^ 4 - 342343680 * X ^ 5 + 1640349696 * X ^ 6 + 124256256 * X ^ 7 - 22454206464 * X ^ 8 + 69357010944 * X ^ 9 - 91603599360 * X ^ 10 + 77309411328 * X ^ 11 - 103079215104 * X ^ 12 : ℚ⟦X⟧) * G ^ 10 + (198696960 * X ^ 6 - 3179151360 * X ^ 7 + 18854313984 * X ^ 8 - 43703599104 * X ^ 9 - 15778971648 * X ^ 10 + 245819768832 * X ^ 11 - 318901321728 * X ^ 12 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (-18063360 * X ^ 5 + 330301440 * X ^ 6 - 1397882880 * X ^ 7 - 3463446528 * X ^ 8 + 39787167744 * X ^ 9 - 106904420352 * X ^ 10 + 106300440576 * X ^ 11 : ℚ⟦X⟧) * G ^ 11 + (-144506880 * X ^ 7 + 2312110080 * X ^ 8 - 13712228352 * X ^ 9 + 31784435712 * X ^ 10 + 11475615744 * X ^ 11 - 178778013696 * X ^ 12 + 231928233984 * X ^ 13 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (-27525120 * X ^ 7 - 210763776 * X ^ 8 + 4957667328 * X ^ 9 - 25568477184 * X ^ 10 + 56371445760 * X ^ 11 - 51539607552 * X ^ 12 : ℚ⟦X⟧) * G ^ 12) * hd2 +
      ((245 * X ^ 3 - 3920 * X ^ 4 + 23248 * X ^ 5 - 53888 * X ^ 6 - 19456 * X ^ 7 + 303104 * X ^ 8 - 393216 * X ^ 9 : ℚ⟦X⟧) + (-1960 * X ^ 3 + 23520 * X ^ 4 - 60544 * X ^ 5 - 312832 * X ^ 6 + 1880064 * X ^ 7 - 1802240 * X ^ 8 - 6553600 * X ^ 9 + 12582912 * X ^ 10 : ℚ⟦X⟧) * G + (11760 * X ^ 3 - 141120 * X ^ 4 + 457344 * X ^ 5 + 371712 * X ^ 6 - 2353152 * X ^ 7 - 9879552 * X ^ 8 + 31850496 * X ^ 9 + 40894464 * X ^ 10 - 150994944 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 + (-43120 * X ^ 3 + 439040 * X ^ 4 - 453888 * X ^ 5 - 8802304 * X ^ 6 + 30924800 * X ^ 7 + 1736704 * X ^ 8 - 100925440 * X ^ 9 - 23068672 * X ^ 10 - 16777216 * X ^ 11 + 805306368 * X ^ 12 : ℚ⟦X⟧) * G ^ 3 + (127400 * X ^ 3 - 1317120 * X ^ 4 + 2430080 * X ^ 5 + 11318272 * X ^ 6 - 5271552 * X ^ 7 - 234356736 * X ^ 8 + 412942336 * X ^ 9 + 869793792 * X ^ 10 - 1858076672 * X ^ 11 - 369098752 * X ^ 12 - 1610612736 * X ^ 13 : ℚ⟦X⟧) * G ^ 4 + (-258720 * X ^ 3 + 2257920 * X ^ 4 + 1792512 * X ^ 5 - 67448832 * X ^ 6 + 173654016 * X ^ 7 + 85721088 * X ^ 8 - 289406976 * X ^ 9 - 1157627904 * X ^ 10 - 1409286144 * X ^ 11 + 9663676416 * X ^ 12 : ℚ⟦X⟧) * G ^ 5 + (423360 * X ^ 3 - 3825920 * X ^ 4 + 2791424 * X ^ 5 + 36073472 * X ^ 6 + 158121984 * X ^ 7 - 1419509760 * X ^ 8 + 1627914240 * X ^ 9 + 5129633792 * X ^ 10 - 8891924480 * X ^ 11 + 268435456 * X ^ 12 - 12884901888 * X ^ 13 : ℚ⟦X⟧) * G ^ 6 + (-423360 * X ^ 3 + 2257920 * X ^ 4 + 21543936 * X ^ 5 - 190881792 * X ^ 6 + 412385280 * X ^ 7 - 132907008 * X ^ 8 + 1226833920 * X ^ 9 - 3875536896 * X ^ 10 - 12884901888 * X ^ 11 + 38654705664 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 + (317520 * X ^ 3 - 1693440 * X ^ 4 - 4492032 * X ^ 5 - 49514496 * X ^ 6 + 918110208 * X ^ 7 - 3422945280 * X ^ 8 + 1763180544 * X ^ 9 + 12519997440 * X ^ 10 - 18421383168 * X ^ 11 + 10468982784 * X ^ 12 - 38654705664 * X ^ 13 : ℚ⟦X⟧) * G ^ 8 + (-3386880 * X ^ 4 + 45158400 * X ^ 5 - 217014272 * X ^ 6 + 530186240 * X ^ 7 - 1553465344 * X ^ 8 + 5356126208 * X ^ 9 - 2550136832 * X ^ 10 - 35165044736 * X ^ 11 + 64424509440 * X ^ 12 : ℚ⟦X⟧) * G ^ 9 + (13547520 * X ^ 5 - 208732160 * X ^ 6 + 1189183488 * X ^ 7 - 2731802624 * X ^ 8 + 205520896 * X ^ 9 + 9059696640 * X ^ 10 - 14361296896 * X ^ 11 + 26843545600 * X ^ 12 - 51539607552 * X ^ 13 : ℚ⟦X⟧) * G ^ 10 + (-24084480 * X ^ 6 + 385351680 * X ^ 7 - 2285371392 * X ^ 8 + 5297405952 * X ^ 9 + 1912602624 * X ^ 10 - 29796335616 * X ^ 11 + 38654705664 * X ^ 12 : ℚ⟦X⟧) * G ^ 11 + (16056320 * X ^ 7 - 256901120 * X ^ 8 + 1523580928 * X ^ 9 - 3531603968 * X ^ 10 - 1275068416 * X ^ 11 + 19864223744 * X ^ 12 - 25769803776 * X ^ 13 : ℚ⟦X⟧) * G ^ 12) * hd3
  have k2 : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
  have k6 : constantCoeff (6 : ℚ⟦X⟧) = 6 := cnum 6
  have hPG : (-1 : ℚ⟦X⟧) + (2 + 8 * X : ℚ⟦X⟧) * G + (-6 : ℚ⟦X⟧) * G ^ 2 + (16 * X : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k2, k6] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 5 hPG)
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (1 + 4 * X : ℚ⟦X⟧) * G ^ 2 + (-2 : ℚ⟦X⟧) * G ^ 3 + (4 * X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 245 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-3920) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C 23248 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C (-53888) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * C (-19456) + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * X * C 303104 +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * X * X * C (-393216) + derivative ℚ (derivative ℚ G) * X * X * C 735 +
      derivative ℚ (derivative ℚ G) * X * X * X * C (-12180) + derivative ℚ (derivative ℚ G) * X * X * X * X * C 66528 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-86016) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-448512) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C 1769472 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * C (-1966080) +
      derivative ℚ G * X * X * C (-840) + derivative ℚ G * X * X * X * C (-6012) +
      derivative ℚ G * X * X * X * X * C 142080 + derivative ℚ G * X * X * X * X * X * C (-708096) +
      derivative ℚ G * X * X * X * X * X * X * C 1529856 + derivative ℚ G * X * X * X * X * X * X * X * C (-1474560) +
      G * X * X * C 420 + G * X * X * X * C (-4176) +
      G * X * X * X * X * C 7296 + G * X * X * X * X * X * C 6144 =
      C 630 * X * X + C (-8112) * X * X * X +
      C 24576 * X * X * X * X + C (-12288) * X * X * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (1 + 4 * X : ℚ⟦X⟧) * G ^ 2 + (-2 : ℚ⟦X⟧) * G ^ 3 + (4 * X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    245 * ((m : ℚ) + 9) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-3920) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      23248 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-53888) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-19456) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 303104 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-393216) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + 735 * ((m : ℚ) + 9) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-12180) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 66528 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-86016) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-448512) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      1769472 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-1966080) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-840) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-6012) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      142080 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-708096) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      1529856 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + (-1474560) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      420 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-4176) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      7296 * coeff (m + 1 + 1 + 1 + 1 + 1) G + 6144 * coeff (m + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (1 + 4 * X : ℚ⟦X⟧) * G ^ 2 + (-2 : ℚ⟦X⟧) * G ^ 3 + (4 * X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    29400 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-235200) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      557952 * coeff (0 + 1 + 1 + 1 + 1) G + (-323328) * coeff (0 + 1 + 1 + 1) G +
      22050 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-243600) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      798336 * coeff (0 + 1 + 1 + 1 + 1) G + (-516096) * coeff (0 + 1 + 1 + 1) G +
      (-897024) * coeff (0 + 1 + 1) G + (-4200) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-24048) * coeff (0 + 1 + 1 + 1 + 1) G + 426240 * coeff (0 + 1 + 1 + 1) G +
      (-1416192) * coeff (0 + 1 + 1) G + 1529856 * coeff (0 + 1) G +
      420 * coeff (0 + 1 + 1 + 1 + 1) G + (-4176) * coeff (0 + 1 + 1 + 1) G +
      7296 * coeff (0 + 1 + 1) G + 6144 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (1 + 4 * X : ℚ⟦X⟧) * G ^ 2 + (-2 : ℚ⟦X⟧) * G ^ 3 + (4 * X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    51450 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-470400) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      1394880 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-1293312) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-116736) * coeff (0 + 1 + 1 + 1) G + 30870 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-365400) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 1330560 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-1032192) * coeff (0 + 1 + 1 + 1 + 1) G + (-2691072) * coeff (0 + 1 + 1 + 1) G +
      3538944 * coeff (0 + 1 + 1) G + (-5040) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-30060) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 568320 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-2124288) * coeff (0 + 1 + 1 + 1) G + 3059712 * coeff (0 + 1 + 1) G +
      (-1474560) * coeff (0 + 1) G + 420 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-4176) * coeff (0 + 1 + 1 + 1 + 1) G + 7296 * coeff (0 + 1 + 1 + 1) G +
      6144 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE2 (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * G + (1 + 4 * X : ℚ⟦X⟧) * G ^ 2 + (-2 : ℚ⟦X⟧) * G ^ 3 + (4 * X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    82320 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-823200) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      2789760 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-3233280) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-466944) * coeff (0 + 1 + 1 + 1 + 1) G + 1818624 * coeff (0 + 1 + 1 + 1) G +
      41160 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-511560) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      1995840 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-1720320) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-5382144) * coeff (0 + 1 + 1 + 1 + 1) G + 10616832 * coeff (0 + 1 + 1 + 1) G +
      (-3932160) * coeff (0 + 1 + 1) G + (-5880) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-36072) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 710400 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-2832384) * coeff (0 + 1 + 1 + 1 + 1) G + 4589568 * coeff (0 + 1 + 1 + 1) G +
      (-2949120) * coeff (0 + 1 + 1) G + 420 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-4176) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 7296 * coeff (0 + 1 + 1 + 1 + 1) G +
      6144 * coeff (0 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A243760Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a243760.main := by
  intro T W G hT _ hW _ hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 6, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m := rfl
  rw [e1, e2, e3, e4, e5, e6]
  have hn : ((-2) + (2) * T) * ((-8) + (-8) * T + (8) * T ^ 2 + (8) * T ^ 3) = (256 * PowerSeries.X ^ 2 : PowerSeries ℚ) := by
    linear_combination ((-16) + (16) * T ^ 2 + (-64) * PowerSeries.X) * hT
  have hnu0 : (256 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    have kc : PowerSeries.constantCoeff (256 : PowerSeries ℚ) = 256 := A243760Aux.cnum 256
    simp [kc] at h'
  have hnu : (256 * PowerSeries.X ^ 2 : PowerSeries ℚ) ≠ 0 := by
    have e : (256 * PowerSeries.X ^ 2 : PowerSeries ℚ) = PowerSeries.X ^ 2 * (256 : PowerSeries ℚ) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 2 PowerSeries.X_ne_zero) hnu0
  have hN1 : ((-2) + (2) * T) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hn
    exact hnu hn.symm
  have hM : ((-2) + (2) * T) ^ 4 * ((PowerSeries.X : PowerSeries ℚ) + (-1 : PowerSeries ℚ) * G + (1 + 4 * PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (-2 : PowerSeries ℚ) * G ^ 3 + (4 * PowerSeries.X : PowerSeries ℚ) * G ^ 4) = 0 := by
    linear_combination ((-16) + (24) * T + (-8) * T * W + (48) * PowerSeries.X + (-32) * PowerSeries.X * W + (16) * PowerSeries.X * T ^ 2 + (64) * PowerSeries.X ^ 2) * hT +
      ((-8) + (4) * W + (4) * T + (-4) * T * W + (4) * T ^ 2 + (28) * PowerSeries.X + (-16) * PowerSeries.X * W + (4) * PowerSeries.X * W ^ 2 + (-16) * PowerSeries.X * T + (16) * PowerSeries.X * T ^ 2 + (32) * PowerSeries.X ^ 2) * hW +
      ((8) + (-4) * W + (4) * W ^ 2 + (-20) * T + (-4) * T * W ^ 2 + (20) * T ^ 2 + (4) * T ^ 2 * W + (-8) * T ^ 3 + (-8) * G * W + (8) * G * T + (16) * G * T * W + (-16) * G * T ^ 2 + (-8) * G * T ^ 2 * W + (8) * G * T ^ 3 + (16) * G ^ 2 + (-48) * G ^ 2 * T + (48) * G ^ 2 * T ^ 2 + (-16) * G ^ 2 * T ^ 3 + (-20) * PowerSeries.X + (28) * PowerSeries.X * W + (-12) * PowerSeries.X * W ^ 2 + (4) * PowerSeries.X * W ^ 3 + (32) * PowerSeries.X * T + (-32) * PowerSeries.X * T * W + (-16) * PowerSeries.X * T ^ 2 + (16) * PowerSeries.X * T ^ 2 * W + (-40) * PowerSeries.X * G + (16) * PowerSeries.X * G * W + (-8) * PowerSeries.X * G * W ^ 2 + (104) * PowerSeries.X * G * T + (-16) * PowerSeries.X * G * T * W + (8) * PowerSeries.X * G * T * W ^ 2 + (-96) * PowerSeries.X * G * T ^ 2 + (32) * PowerSeries.X * G * T ^ 3 + (-16) * PowerSeries.X * G ^ 2 + (16) * PowerSeries.X * G ^ 2 * W + (32) * PowerSeries.X * G ^ 2 * T + (-32) * PowerSeries.X * G ^ 2 * T * W + (-16) * PowerSeries.X * G ^ 2 * T ^ 2 + (16) * PowerSeries.X * G ^ 2 * T ^ 2 * W + (-32) * PowerSeries.X * G ^ 3 + (96) * PowerSeries.X * G ^ 3 * T + (-96) * PowerSeries.X * G ^ 3 * T ^ 2 + (32) * PowerSeries.X * G ^ 3 * T ^ 3) * hG
  have hP : (PowerSeries.X : PowerSeries ℚ) + (-1 : PowerSeries ℚ) * G + (1 + 4 * PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (-2 : PowerSeries ℚ) * G ^ 3 + (4 * PowerSeries.X : PowerSeries ℚ) * G ^ 4 = 0 := (mul_eq_zero.mp hM).resolve_left (pow_ne_zero 4 hN1)
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A243760Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A243760Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A243760Aux.relE2 G hP h0c
        push_cast
        linear_combination r
      | succ m =>
        have r := A243760Aux.rel G hP h0c m
        push_cast
        linear_combination r
