import OMAStatements.S_oeis_a390424

-- Problem: A390424: Expansion of 1/(2 - g^2)^2, where g = 1+x*g^3 is the g.f. of A001764.
-- Upstream: formal-conjectures statements/oeis-a390424.lean:0 (declaration OMA.S_oeis_a390424.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A390424Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (-X ^ 4 : ℚ⟦X⟧) + (2 * X ^ 2 - 8 * X ^ 3 + 12 * X ^ 4 : ℚ⟦X⟧) * G + (-1 + 12 * X - 44 * X ^ 2 + 64 * X ^ 3 - 48 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 + (1 - 16 * X + 80 * X ^ 2 - 128 * X ^ 3 + 64 * X ^ 4 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    (20 * X ^ 2 - 511 * X ^ 3 + 4922 * X ^ 4 - 21788 * X ^ 5 + 42416 * X ^ 6 - 26784 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-30 * X + 435 * X ^ 2 - 908 * X ^ 3 - 11084 * X ^ 4 + 56576 * X ^ 5 - 80352 * X ^ 6) * derivative ℚ G + (120 * X - 1720 * X ^ 2 + 6272 * X ^ 3 - 704 * X ^ 4 - 23808 * X ^ 5) * G =
      -20 * X ^ 2 + 208 * X ^ 3 + 320 * X ^ 4 - 5952 * X ^ 5 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have d44 : derivative ℚ (44 : ℚ⟦X⟧) = 0 := dnum 44
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d80 : derivative ℚ (80 : ℚ⟦X⟧) = 0 := dnum 80
  have d88 : derivative ℚ (88 : ℚ⟦X⟧) = 0 := dnum 88
  have d96 : derivative ℚ (96 : ℚ⟦X⟧) = 0 := dnum 96
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d160 : derivative ℚ (160 : ℚ⟦X⟧) = 0 := dnum 160
  have d192 : derivative ℚ (192 : ℚ⟦X⟧) = 0 := dnum 192
  have d240 : derivative ℚ (240 : ℚ⟦X⟧) = 0 := dnum 240
  have d256 : derivative ℚ (256 : ℚ⟦X⟧) = 0 := dnum 256
  have d384 : derivative ℚ (384 : ℚ⟦X⟧) = 0 := dnum 384
  have hp0 : (-1 * (X * X * X * X) : ℚ⟦X⟧) + (2 * (X * X) - 8 * (X * X * X) + 12 * (X * X * X * X) : ℚ⟦X⟧) * G + (-1 + 12 * X - 44 * (X * X) + 64 * (X * X * X) - 48 * (X * X * X * X) : ℚ⟦X⟧) * G * G + (1 - 16 * X + 80 * (X * X) - 128 * (X * X * X) + 64 * (X * X * X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-1 * (X * X * X * X) : ℚ⟦X⟧) + (2 * (X * X) - 8 * (X * X * X) + 12 * (X * X * X * X) : ℚ⟦X⟧) * G + (-1 + 12 * X - 44 * (X * X) + 64 * (X * X * X) - 48 * (X * X * X * X) : ℚ⟦X⟧) * G * G + (1 - 16 * X + 80 * (X * X) - 128 * (X * X * X) + 64 * (X * X * X * X) : ℚ⟦X⟧) * G * G * G) =
      (-4 * X ^ 3 : ℚ⟦X⟧) + (2 * X ^ 2 - 8 * X ^ 3 + 12 * X ^ 4 : ℚ⟦X⟧) * (derivative ℚ G) + (4 * X - 24 * X ^ 2 + 48 * X ^ 3 : ℚ⟦X⟧) * G + (-2 + 24 * X - 88 * X ^ 2 + 128 * X ^ 3 - 96 * X ^ 4 : ℚ⟦X⟧) * G * (derivative ℚ G) + (12 - 88 * X + 192 * X ^ 2 - 192 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 + (3 - 48 * X + 240 * X ^ 2 - 384 * X ^ 3 + 192 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-16 + 160 * X - 384 * X ^ 2 + 256 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d2, d8, d12, d16, d44, d48, d64, d80, d128]
    ring
  have hd1 : (-4 * X ^ 3 : ℚ⟦X⟧) + (2 * X ^ 2 - 8 * X ^ 3 + 12 * X ^ 4 : ℚ⟦X⟧) * (derivative ℚ G) + (4 * X - 24 * X ^ 2 + 48 * X ^ 3 : ℚ⟦X⟧) * G + (-2 + 24 * X - 88 * X ^ 2 + 128 * X ^ 3 - 96 * X ^ 4 : ℚ⟦X⟧) * G * (derivative ℚ G) + (12 - 88 * X + 192 * X ^ 2 - 192 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 + (3 - 48 * X + 240 * X ^ 2 - 384 * X ^ 3 + 192 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-16 + 160 * X - 384 * X ^ 2 + 256 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (-4 * (X * X * X) : ℚ⟦X⟧) + (2 * (X * X) - 8 * (X * X * X) + 12 * (X * X * X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (4 * X - 24 * (X * X) + 48 * (X * X * X) : ℚ⟦X⟧) * G + (-2 + 24 * X - 88 * (X * X) + 128 * (X * X * X) - 96 * (X * X * X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (12 - 88 * X + 192 * (X * X) - 192 * (X * X * X) : ℚ⟦X⟧) * G * G + (3 - 48 * X + 240 * (X * X) - 384 * (X * X * X) + 192 * (X * X * X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-16 + 160 * X - 384 * (X * X) + 256 * (X * X * X) : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((-4 * (X * X * X) : ℚ⟦X⟧) + (2 * (X * X) - 8 * (X * X * X) + 12 * (X * X * X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (4 * X - 24 * (X * X) + 48 * (X * X * X) : ℚ⟦X⟧) * G + (-2 + 24 * X - 88 * (X * X) + 128 * (X * X * X) - 96 * (X * X * X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (12 - 88 * X + 192 * (X * X) - 192 * (X * X * X) : ℚ⟦X⟧) * G * G + (3 - 48 * X + 240 * (X * X) - 384 * (X * X * X) + 192 * (X * X * X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-16 + 160 * X - 384 * (X * X) + 256 * (X * X * X) : ℚ⟦X⟧) * G * G * G) =
      (-12 * X ^ 2 : ℚ⟦X⟧) + (2 * X ^ 2 - 8 * X ^ 3 + 12 * X ^ 4 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (8 * X - 48 * X ^ 2 + 96 * X ^ 3 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 + 24 * X - 88 * X ^ 2 + 128 * X ^ 3 - 96 * X ^ 4 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (4 - 48 * X + 144 * X ^ 2 : ℚ⟦X⟧) * G + (-2 + 24 * X - 88 * X ^ 2 + 128 * X ^ 3 - 96 * X ^ 4 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (48 - 352 * X + 768 * X ^ 2 - 768 * X ^ 3 : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 96 * X + 480 * X ^ 2 - 768 * X ^ 3 + 384 * X ^ 4 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-88 + 384 * X - 576 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (3 - 48 * X + 240 * X ^ 2 - 384 * X ^ 3 + 192 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-96 + 960 * X - 2304 * X ^ 2 + 1536 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (160 - 768 * X + 768 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 := by
    simp [Derivation.leibniz, d2, d3, d4, d8, d12, d16, d24, d48, d88, d96, d128, d160, d192, d240, d256, d384]
    ring
  have hd2 : (-12 * X ^ 2 : ℚ⟦X⟧) + (2 * X ^ 2 - 8 * X ^ 3 + 12 * X ^ 4 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (8 * X - 48 * X ^ 2 + 96 * X ^ 3 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 + 24 * X - 88 * X ^ 2 + 128 * X ^ 3 - 96 * X ^ 4 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (4 - 48 * X + 144 * X ^ 2 : ℚ⟦X⟧) * G + (-2 + 24 * X - 88 * X ^ 2 + 128 * X ^ 3 - 96 * X ^ 4 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (48 - 352 * X + 768 * X ^ 2 - 768 * X ^ 3 : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 96 * X + 480 * X ^ 2 - 768 * X ^ 3 + 384 * X ^ 4 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-88 + 384 * X - 576 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (3 - 48 * X + 240 * X ^ 2 - 384 * X ^ 3 + 192 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-96 + 960 * X - 2304 * X ^ 2 + 1536 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (160 - 768 * X + 768 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((2 * X ^ 2 - 8 * X ^ 3 + 12 * X ^ 4 : ℚ⟦X⟧) + (-2 + 24 * X - 88 * X ^ 2 + 128 * X ^ 3 - 96 * X ^ 4 : ℚ⟦X⟧) * G + (3 - 48 * X + 240 * X ^ 2 - 384 * X ^ 3 + 192 * X ^ 4 : ℚ⟦X⟧) * G ^ 2) ^ 3 * ((20 * X ^ 2 - 511 * X ^ 3 + 4922 * X ^ 4 - 21788 * X ^ 5 + 42416 * X ^ 6 - 26784 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-30 * X + 435 * X ^ 2 - 908 * X ^ 3 - 11084 * X ^ 4 + 56576 * X ^ 5 - 80352 * X ^ 6) * derivative ℚ G + (120 * X - 1720 * X ^ 2 + 6272 * X ^ 3 - 704 * X ^ 4 - 23808 * X ^ 5) * G - (-20 * X ^ 2 + 208 * X ^ 3 + 320 * X ^ 4 - 5952 * X ^ 5)) = 0 := by
    linear_combination ((3520 * X ^ 5 - 89760 * X ^ 6 + 898816 * X ^ 7 - 4467328 * X ^ 8 + 11123328 * X ^ 9 - 10673024 * X ^ 10 - 4772864 * X ^ 11 + 11258880 * X ^ 12 : ℚ⟦X⟧) + (960 * X ^ 3 - 36160 * X ^ 4 + 584928 * X ^ 5 - 5244352 * X ^ 6 + 28441984 * X ^ 7 - 96976896 * X ^ 8 + 213521408 * X ^ 9 - 315430912 * X ^ 10 + 319881216 * X ^ 11 - 180142080 * X ^ 12 : ℚ⟦X⟧) * G + (-480 * X + 21920 * X ^ 2 - 447424 * X ^ 3 + 5353568 * X ^ 4 - 41526848 * X ^ 5 + 218664512 * X ^ 6 - 796852736 * X ^ 7 + 2012504576 * X ^ 8 - 3475845120 * X ^ 9 + 3993079808 * X ^ 10 - 2886696960 * X ^ 11 + 1080852480 * X ^ 12 : ℚ⟦X⟧) * G ^ 2 + (1440 * X - 70880 * X ^ 2 + 1547520 * X ^ 3 - 19625856 * X ^ 4 + 159424000 * X ^ 5 - 865320448 * X ^ 6 + 3189256192 * X ^ 7 - 7985262592 * X ^ 8 + 13418725376 * X ^ 9 - 14675247104 * X ^ 10 + 9619374080 * X ^ 11 - 2882273280 * X ^ 12 : ℚ⟦X⟧) * G ^ 3 + (-1080 * X + 57480 * X ^ 2 - 1360320 * X ^ 3 + 18758592 * X ^ 4 - 166115328 * X ^ 5 + 983012352 * X ^ 6 - 3928522752 * X ^ 7 + 10499383296 * X ^ 8 - 18231754752 * X ^ 9 + 19486900224 * X ^ 10 - 11540889600 * X ^ 11 + 2882273280 * X ^ 12 : ℚ⟦X⟧) * G ^ 4) * hP +
      ((-280 * X ^ 5 + 8068 * X ^ 6 - 99392 * X ^ 7 + 708672 * X ^ 8 - 3357856 * X ^ 9 + 11252336 * X ^ 10 - 26289856 * X ^ 11 + 39136064 * X ^ 12 - 31285248 * X ^ 13 + 8999424 * X ^ 14 : ℚ⟦X⟧) + (80 * X ^ 4 - 3324 * X ^ 5 + 60232 * X ^ 6 - 627432 * X ^ 7 + 4176688 * X ^ 8 - 18712384 * X ^ 9 + 57915840 * X ^ 10 - 124865792 * X ^ 11 + 185665280 * X ^ 12 - 183679488 * X ^ 13 + 110573568 * X ^ 14 - 30855168 * X ^ 15 : ℚ⟦X⟧) * (derivative ℚ G) + (400 * X ^ 3 - 16208 * X ^ 4 + 290240 * X ^ 5 - 3032424 * X ^ 6 + 20512976 * X ^ 7 - 94086368 * X ^ 8 + 297946240 * X ^ 9 - 652642048 * X ^ 10 + 977733632 * X ^ 11 - 969022464 * X ^ 12 + 575987712 * X ^ 13 - 143990784 * X ^ 14 : ℚ⟦X⟧) * G + (-80 * X ^ 2 + 3964 * X ^ 3 - 87544 * X ^ 4 + 1139524 * X ^ 5 - 9752168 * X ^ 6 + 58037736 * X ^ 7 - 248087120 * X ^ 8 + 776328672 * X ^ 9 - 1793748096 * X ^ 10 + 3048075520 * X ^ 11 - 3721991168 * X ^ 12 + 3095599104 * X ^ 13 - 1573724160 * X ^ 14 + 370262016 * X ^ 15 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-120 * X + 6060 * X ^ 2 - 138224 * X ^ 3 + 1883668 * X ^ 4 - 17083440 * X ^ 5 + 108681032 * X ^ 6 - 498387872 * X ^ 7 + 1669116320 * X ^ 8 - 4094026240 * X ^ 9 + 7291058432 * X ^ 10 - 9181874176 * X ^ 11 + 7737501696 * X ^ 12 - 3908468736 * X ^ 13 + 863944704 * X ^ 14 : ℚ⟦X⟧) * G ^ 2 + (360 * X ^ 2 - 19278 * X ^ 3 + 459900 * X ^ 4 - 6447600 * X ^ 5 + 59041584 * X ^ 6 - 371601792 * X ^ 7 + 1649611584 * X ^ 8 - 5226710400 * X ^ 9 + 11852241408 * X ^ 10 - 19125605376 * X ^ 11 + 21548593152 * X ^ 12 - 16181305344 * X ^ 13 + 7282262016 * X ^ 14 - 1481048064 * X ^ 15 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (360 * X - 19940 * X ^ 2 + 493368 * X ^ 3 - 7197664 * X ^ 4 + 68832896 * X ^ 5 - 453972800 * X ^ 6 + 2117220352 * X ^ 7 - 7055761152 * X ^ 8 + 16816539648 * X ^ 9 - 28438808576 * X ^ 10 + 33363787776 * X ^ 11 - 25734889472 * X ^ 12 + 11629363200 * X ^ 13 - 2303852544 * X ^ 14 : ℚ⟦X⟧) * G ^ 3 + (-360 * X ^ 2 + 20718 * X ^ 3 - 532692 * X ^ 4 + 8067384 * X ^ 5 - 79895520 * X ^ 6 + 543378240 * X ^ 7 - 2595469824 * X ^ 8 + 8763780096 * X ^ 9 - 20814999552 * X ^ 10 + 34252554240 * X ^ 11 - 37976555520 * X ^ 12 + 26951122944 * X ^ 13 - 11026169856 * X ^ 14 + 1974730752 * X ^ 15 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-270 * X + 16395 * X ^ 2 - 443724 * X ^ 3 + 7060404 * X ^ 4 - 73346304 * X ^ 5 + 522377760 * X ^ 6 - 2607118848 * X ^ 7 + 9167374848 * X ^ 8 - 22560522240 * X ^ 9 + 38206341120 * X ^ 10 - 43267571712 * X ^ 11 + 31138136064 * X ^ 12 - 12836143104 * X ^ 13 + 2303852544 * X ^ 14 : ℚ⟦X⟧) * G ^ 4) * hd1 +
      ((80 * X ^ 6 - 2684 * X ^ 7 + 38280 * X ^ 8 - 305728 * X ^ 9 + 1519136 * X ^ 10 - 4923312 * X ^ 11 + 10499744 * X ^ 12 - 14281152 * X ^ 13 + 11250432 * X ^ 14 - 3856896 * X ^ 15 : ℚ⟦X⟧) + (-160 * X ^ 4 + 6648 * X ^ 5 - 120464 * X ^ 6 + 1254864 * X ^ 7 - 8353376 * X ^ 8 + 37424768 * X ^ 9 - 115831680 * X ^ 10 + 249731584 * X ^ 11 - 371330560 * X ^ 12 + 367358976 * X ^ 13 - 221147136 * X ^ 14 + 61710336 * X ^ 15 : ℚ⟦X⟧) * G + (80 * X ^ 2 - 3964 * X ^ 3 + 87544 * X ^ 4 - 1139524 * X ^ 5 + 9752168 * X ^ 6 - 58037736 * X ^ 7 + 248087120 * X ^ 8 - 776328672 * X ^ 9 + 1793748096 * X ^ 10 - 3048075520 * X ^ 11 + 3721991168 * X ^ 12 - 3095599104 * X ^ 13 + 1573724160 * X ^ 14 - 370262016 * X ^ 15 : ℚ⟦X⟧) * G ^ 2 + (-240 * X ^ 2 + 12852 * X ^ 3 - 306600 * X ^ 4 + 4298400 * X ^ 5 - 39361056 * X ^ 6 + 247734528 * X ^ 7 - 1099741056 * X ^ 8 + 3484473600 * X ^ 9 - 7901494272 * X ^ 10 + 12750403584 * X ^ 11 - 14365728768 * X ^ 12 + 10787536896 * X ^ 13 - 4854841344 * X ^ 14 + 987365376 * X ^ 15 : ℚ⟦X⟧) * G ^ 3 + (180 * X ^ 2 - 10359 * X ^ 3 + 266346 * X ^ 4 - 4033692 * X ^ 5 + 39947760 * X ^ 6 - 271689120 * X ^ 7 + 1297734912 * X ^ 8 - 4381890048 * X ^ 9 + 10407499776 * X ^ 10 - 17126277120 * X ^ 11 + 18988277760 * X ^ 12 - 13475561472 * X ^ 13 + 5513084928 * X ^ 14 - 987365376 * X ^ 15 : ℚ⟦X⟧) * G ^ 4) * hd2
  have k2 : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
  have k3 : constantCoeff (3 : ℚ⟦X⟧) = 3 := cnum 3
  have hPG : (2 * X ^ 2 - 8 * X ^ 3 + 12 * X ^ 4 : ℚ⟦X⟧) + (-2 + 24 * X - 88 * X ^ 2 + 128 * X ^ 3 - 96 * X ^ 4 : ℚ⟦X⟧) * G + (3 - 48 * X + 240 * X ^ 2 - 384 * X ^ 3 + 192 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k2, k3] at h'
    norm_num at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (-X ^ 4 : ℚ⟦X⟧) + (2 * X ^ 2 - 8 * X ^ 3 + 12 * X ^ 4 : ℚ⟦X⟧) * G + (-1 + 12 * X - 44 * X ^ 2 + 64 * X ^ 3 - 48 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 + (1 - 16 * X + 80 * X ^ 2 - 128 * X ^ 3 + 64 * X ^ 4 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C 20 + derivative ℚ (derivative ℚ G) * X * X * X * C (-511) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 4922 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-21788) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 42416 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C (-26784) +
      derivative ℚ G * X * C (-30) + derivative ℚ G * X * X * C 435 +
      derivative ℚ G * X * X * X * C (-908) + derivative ℚ G * X * X * X * X * C (-11084) +
      derivative ℚ G * X * X * X * X * X * C 56576 + derivative ℚ G * X * X * X * X * X * X * C (-80352) +
      G * X * C 120 + G * X * X * C (-1720) +
      G * X * X * X * C 6272 + G * X * X * X * X * C (-704) +
      G * X * X * X * X * X * C (-23808) =
      C (-20) * X * X + C 208 * X * X * X +
      C 320 * X * X * X * X + C (-5952) * X * X * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (-X ^ 4 : ℚ⟦X⟧) + (2 * X ^ 2 - 8 * X ^ 3 + 12 * X ^ 4 : ℚ⟦X⟧) * G + (-1 + 12 * X - 44 * X ^ 2 + 64 * X ^ 3 - 48 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 + (1 - 16 * X + 80 * X ^ 2 - 128 * X ^ 3 + 64 * X ^ 4 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) (m : ℕ) :
    20 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-511) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      4922 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-21788) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      42416 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + (-26784) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      (-30) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 435 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-908) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-11084) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      56576 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-80352) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      120 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-1720) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      6272 * coeff (m + 1 + 1 + 1 + 1) G + (-704) * coeff (m + 1 + 1 + 1) G +
      (-23808) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (-X ^ 4 : ℚ⟦X⟧) + (2 * X ^ 2 - 8 * X ^ 3 + 12 * X ^ 4 : ℚ⟦X⟧) * G + (-1 + 12 * X - 44 * X ^ 2 + 64 * X ^ 3 - 48 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 + (1 - 16 * X + 80 * X ^ 2 - 128 * X ^ 3 + 64 * X ^ 4 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    600 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-10220) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      59064 * coeff (0 + 1 + 1 + 1 + 1) G + (-130728) * coeff (0 + 1 + 1 + 1) G +
      84832 * coeff (0 + 1 + 1) G + (-180) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      2175 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-3632) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-33252) * coeff (0 + 1 + 1 + 1) G + 113152 * coeff (0 + 1 + 1) G +
      (-80352) * coeff (0 + 1) G + 120 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-1720) * coeff (0 + 1 + 1 + 1 + 1) G + 6272 * coeff (0 + 1 + 1 + 1) G +
      (-704) * coeff (0 + 1 + 1) G + (-23808) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A390424Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a390424.main := by
  intro T G hT hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 6, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 := rfl
  rw [e1, e2, e3, e4, e5]
  have hT0c : PowerSeries.constantCoeff T = 1 := by
    have h := congrArg PowerSeries.constantCoeff hT
    simpa using h
  have kn4 : PowerSeries.constantCoeff (4 : PowerSeries ℚ) = 4 := A390424Aux.cnum 4
  have hN1 : ((4) + (-4) * T ^ 2 + (1) * T ^ 4) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [hT0c, kn4] at h'
  have hM : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 9) * (((4) + (-4) * T ^ 2 + (1) * T ^ 4) ^ 3 * ((-PowerSeries.X ^ 4 : PowerSeries ℚ) + (2 * PowerSeries.X ^ 2 - 8 * PowerSeries.X ^ 3 + 12 * PowerSeries.X ^ 4 : PowerSeries ℚ) * G + (-1 + 12 * PowerSeries.X - 44 * PowerSeries.X ^ 2 + 64 * PowerSeries.X ^ 3 - 48 * PowerSeries.X ^ 4 : PowerSeries ℚ) * G ^ 2 + (1 - 16 * PowerSeries.X + 80 * PowerSeries.X ^ 2 - 128 * PowerSeries.X ^ 3 + 64 * PowerSeries.X ^ 4 : PowerSeries ℚ) * G ^ 3)) = 0 := by
    linear_combination ((-3) * PowerSeries.X ^ 9 + (-3) * PowerSeries.X ^ 9 * T + (1) * PowerSeries.X ^ 9 * T ^ 2 + (1) * PowerSeries.X ^ 9 * T ^ 3 + (32) * PowerSeries.X ^ 10 + (32) * PowerSeries.X ^ 10 * T + (-16) * PowerSeries.X ^ 10 * T ^ 2 + (-13) * PowerSeries.X ^ 10 * T ^ 3 + (2) * PowerSeries.X ^ 10 * T ^ 4 + (1) * PowerSeries.X ^ 10 * T ^ 5 + (-64) * PowerSeries.X ^ 11 + (-64) * PowerSeries.X ^ 11 * T + (48) * PowerSeries.X ^ 11 * T ^ 2 + (16) * PowerSeries.X ^ 11 * T ^ 3 + (-12) * PowerSeries.X ^ 11 * T ^ 4 + (4) * PowerSeries.X ^ 11 * T ^ 5 + (1) * PowerSeries.X ^ 11 * T ^ 6 + (-1) * PowerSeries.X ^ 11 * T ^ 7 + (64) * PowerSeries.X ^ 12 * T ^ 3 + (-48) * PowerSeries.X ^ 12 * T ^ 5 + (12) * PowerSeries.X ^ 12 * T ^ 7 + (-1) * PowerSeries.X ^ 12 * T ^ 9) * hT +
      ((3) * PowerSeries.X ^ 9 + (-4) * PowerSeries.X ^ 9 * T ^ 2 + (1) * PowerSeries.X ^ 9 * T ^ 4 + (12) * PowerSeries.X ^ 9 * G + (-28) * PowerSeries.X ^ 9 * G * T ^ 2 + (23) * PowerSeries.X ^ 9 * G * T ^ 4 + (-8) * PowerSeries.X ^ 9 * G * T ^ 6 + (1) * PowerSeries.X ^ 9 * G * T ^ 8 + (-16) * PowerSeries.X ^ 9 * G ^ 2 + (32) * PowerSeries.X ^ 9 * G ^ 2 * T ^ 2 + (-24) * PowerSeries.X ^ 9 * G ^ 2 * T ^ 4 + (8) * PowerSeries.X ^ 9 * G ^ 2 * T ^ 6 + (-1) * PowerSeries.X ^ 9 * G ^ 2 * T ^ 8 + (-32) * PowerSeries.X ^ 10 + (48) * PowerSeries.X ^ 10 * T ^ 2 + (-12) * PowerSeries.X ^ 10 * T ^ 4 + (-128) * PowerSeries.X ^ 10 * G + (320) * PowerSeries.X ^ 10 * G * T ^ 2 + (-272) * PowerSeries.X ^ 10 * G * T ^ 4 + (96) * PowerSeries.X ^ 10 * G * T ^ 6 + (-12) * PowerSeries.X ^ 10 * G * T ^ 8 + (256) * PowerSeries.X ^ 10 * G ^ 2 + (-512) * PowerSeries.X ^ 10 * G ^ 2 * T ^ 2 + (384) * PowerSeries.X ^ 10 * G ^ 2 * T ^ 4 + (-128) * PowerSeries.X ^ 10 * G ^ 2 * T ^ 6 + (16) * PowerSeries.X ^ 10 * G ^ 2 * T ^ 8 + (64) * PowerSeries.X ^ 11 + (-112) * PowerSeries.X ^ 11 * T ^ 2 + (-4) * PowerSeries.X ^ 11 * T ^ 4 + (16) * PowerSeries.X ^ 11 * T ^ 6 + (-2) * PowerSeries.X ^ 11 * T ^ 8 + (384) * PowerSeries.X ^ 11 * G + (-1088) * PowerSeries.X ^ 11 * G * T ^ 2 + (976) * PowerSeries.X ^ 11 * G * T ^ 4 + (-352) * PowerSeries.X ^ 11 * G * T ^ 6 + (44) * PowerSeries.X ^ 11 * G * T ^ 8 + (-1280) * PowerSeries.X ^ 11 * G ^ 2 + (2560) * PowerSeries.X ^ 11 * G ^ 2 * T ^ 2 + (-1920) * PowerSeries.X ^ 11 * G ^ 2 * T ^ 4 + (640) * PowerSeries.X ^ 11 * G ^ 2 * T ^ 6 + (-80) * PowerSeries.X ^ 11 * G ^ 2 * T ^ 8 + (128) * PowerSeries.X ^ 12 * T ^ 4 + (-64) * PowerSeries.X ^ 12 * T ^ 6 + (8) * PowerSeries.X ^ 12 * T ^ 8 + (-512) * PowerSeries.X ^ 12 * G + (1536) * PowerSeries.X ^ 12 * G * T ^ 2 + (-1408) * PowerSeries.X ^ 12 * G * T ^ 4 + (512) * PowerSeries.X ^ 12 * G * T ^ 6 + (-64) * PowerSeries.X ^ 12 * G * T ^ 8 + (2048) * PowerSeries.X ^ 12 * G ^ 2 + (-4096) * PowerSeries.X ^ 12 * G ^ 2 * T ^ 2 + (3072) * PowerSeries.X ^ 12 * G ^ 2 * T ^ 4 + (-1024) * PowerSeries.X ^ 12 * G ^ 2 * T ^ 6 + (128) * PowerSeries.X ^ 12 * G ^ 2 * T ^ 8 + (-64) * PowerSeries.X ^ 13 + (192) * PowerSeries.X ^ 13 * T ^ 2 + (-240) * PowerSeries.X ^ 13 * T ^ 4 + (96) * PowerSeries.X ^ 13 * T ^ 6 + (-12) * PowerSeries.X ^ 13 * T ^ 8 + (512) * PowerSeries.X ^ 13 * G + (-1280) * PowerSeries.X ^ 13 * G * T ^ 2 + (1088) * PowerSeries.X ^ 13 * G * T ^ 4 + (-384) * PowerSeries.X ^ 13 * G * T ^ 6 + (48) * PowerSeries.X ^ 13 * G * T ^ 8 + (-1024) * PowerSeries.X ^ 13 * G ^ 2 + (2048) * PowerSeries.X ^ 13 * G ^ 2 * T ^ 2 + (-1536) * PowerSeries.X ^ 13 * G ^ 2 * T ^ 4 + (512) * PowerSeries.X ^ 13 * G ^ 2 * T ^ 6 + (-64) * PowerSeries.X ^ 13 * G ^ 2 * T ^ 8) * hG
  have hLne : ((-1 : PowerSeries ℚ) * PowerSeries.X ^ 9) ≠ 0 := mul_ne_zero (neg_ne_zero.mpr one_ne_zero) (pow_ne_zero 9 PowerSeries.X_ne_zero)
  have hP : (-PowerSeries.X ^ 4 : PowerSeries ℚ) + (2 * PowerSeries.X ^ 2 - 8 * PowerSeries.X ^ 3 + 12 * PowerSeries.X ^ 4 : PowerSeries ℚ) * G + (-1 + 12 * PowerSeries.X - 44 * PowerSeries.X ^ 2 + 64 * PowerSeries.X ^ 3 - 48 * PowerSeries.X ^ 4 : PowerSeries ℚ) * G ^ 2 + (1 - 16 * PowerSeries.X + 80 * PowerSeries.X ^ 2 - 128 * PowerSeries.X ^ 3 + 64 * PowerSeries.X ^ 4 : PowerSeries ℚ) * G ^ 3 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hM).resolve_left hLne)).resolve_left (pow_ne_zero 3 hN1)
  have h0c : PowerSeries.constantCoeff G = (1 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A390424Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    have r := A390424Aux.rel G hP h0c m
    push_cast
    linear_combination r
