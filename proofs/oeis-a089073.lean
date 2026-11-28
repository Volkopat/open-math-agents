import OMAStatements.S_oeis_a089073

-- Problem: A089073: Number of symmetric non-crossing connected graphs on n equidistant nodes on a circle.
-- Upstream: formal-conjectures statements/oeis-a089073.lean:0 (declaration OMA.S_oeis_a089073.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A089073Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem key (G T Y2 : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * T ^ 2 + (-4 * X ^ 2 : ℚ⟦X⟧) * T ^ 3 = 0)
    (hY2 : Y2 = T * T)
    (hG : (2) * G = (-1) + (1 + 2 * X) * T + (0) * Y2) :
    (23 * X ^ 4 - 2484 * X ^ 8) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (22 * X ^ 3 - 27216 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-312 * X ^ 2 + 324 * X ^ 3 - 648 * X ^ 4 + 1296 * X ^ 5 - 63192 * X ^ 6) * derivative ℚ (derivative ℚ G) + (180 * X + 408 * X ^ 2 - 2112 * X ^ 3 + 6816 * X ^ 4 - 10176 * X ^ 5) * derivative ℚ G + (-360 * X - 96 * X ^ 2 + 4416 * X ^ 3 - 3024 * X ^ 4) * G =
      180 * X - 216 * X ^ 2 - 3504 * X ^ 3 + 1512 * X ^ 4 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d512 : derivative ℚ (512 : ℚ⟦X⟧) = 0 := dnum 512
  have d768 : derivative ℚ (768 : ℚ⟦X⟧) = 0 := dnum 768
  have d1024 : derivative ℚ (1024 : ℚ⟦X⟧) = 0 := dnum 1024
  have d1536 : derivative ℚ (1536 : ℚ⟦X⟧) = 0 := dnum 1536
  have d2048 : derivative ℚ (2048 : ℚ⟦X⟧) = 0 := dnum 2048
  have d3840 : derivative ℚ (3840 : ℚ⟦X⟧) = 0 := dnum 3840
  have d4096 : derivative ℚ (4096 : ℚ⟦X⟧) = 0 := dnum 4096
  have d7168 : derivative ℚ (7168 : ℚ⟦X⟧) = 0 := dnum 7168
  have d9216 : derivative ℚ (9216 : ℚ⟦X⟧) = 0 := dnum 9216
  have d10752 : derivative ℚ (10752 : ℚ⟦X⟧) = 0 := dnum 10752
  have d12288 : derivative ℚ (12288 : ℚ⟦X⟧) = 0 := dnum 12288
  have d13824 : derivative ℚ (13824 : ℚ⟦X⟧) = 0 := dnum 13824
  have d14336 : derivative ℚ (14336 : ℚ⟦X⟧) = 0 := dnum 14336
  have d15360 : derivative ℚ (15360 : ℚ⟦X⟧) = 0 := dnum 15360
  have d28672 : derivative ℚ (28672 : ℚ⟦X⟧) = 0 := dnum 28672
  have d43008 : derivative ℚ (43008 : ℚ⟦X⟧) = 0 := dnum 43008
  have d55296 : derivative ℚ (55296 : ℚ⟦X⟧) = 0 := dnum 55296
  have d64512 : derivative ℚ (64512 : ℚ⟦X⟧) = 0 := dnum 64512
  have d73728 : derivative ℚ (73728 : ℚ⟦X⟧) = 0 := dnum 73728
  have d82944 : derivative ℚ (82944 : ℚ⟦X⟧) = 0 := dnum 82944
  have d86016 : derivative ℚ (86016 : ℚ⟦X⟧) = 0 := dnum 86016
  have d110592 : derivative ℚ (110592 : ℚ⟦X⟧) = 0 := dnum 110592
  have d138240 : derivative ℚ (138240 : ℚ⟦X⟧) = 0 := dnum 138240
  have d215040 : derivative ℚ (215040 : ℚ⟦X⟧) = 0 := dnum 215040
  have d322560 : derivative ℚ (322560 : ℚ⟦X⟧) = 0 := dnum 322560
  have d663552 : derivative ℚ (663552 : ℚ⟦X⟧) = 0 := dnum 663552
  have d811008 : derivative ℚ (811008 : ℚ⟦X⟧) = 0 := dnum 811008
  have d884736 : derivative ℚ (884736 : ℚ⟦X⟧) = 0 := dnum 884736
  have d1244160 : derivative ℚ (1244160 : ℚ⟦X⟧) = 0 := dnum 1244160
  have d4644864 : derivative ℚ (4644864 : ℚ⟦X⟧) = 0 := dnum 4644864
  have d7299072 : derivative ℚ (7299072 : ℚ⟦X⟧) = 0 := dnum 7299072
  have d8110080 : derivative ℚ (8110080 : ℚ⟦X⟧) = 0 := dnum 8110080
  have d9953280 : derivative ℚ (9953280 : ℚ⟦X⟧) = 0 := dnum 9953280
  have dp4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have hp0 : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * T * T + (-4 * (X * X) : ℚ⟦X⟧) * T * T * T = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * T * T + (-4 * (X * X) : ℚ⟦X⟧) * T * T * T) =
      (2 : ℚ⟦X⟧) * T * (derivative ℚ T) + (-12 * X ^ 2 : ℚ⟦X⟧) * T ^ 2 * (derivative ℚ T) + (-8 * X : ℚ⟦X⟧) * T ^ 3 := by
    simp [Derivation.leibniz, dp4]
    ring
  have hd1 : (2 : ℚ⟦X⟧) * T * (derivative ℚ T) + (-12 * X ^ 2 : ℚ⟦X⟧) * T ^ 2 * (derivative ℚ T) + (-8 * X : ℚ⟦X⟧) * T ^ 3 = 0 := by rw [← hL1, hp0, map_zero]
  have s1 : (-128 * X ^ 6 + 13824 * X ^ 10 : ℚ⟦X⟧) * derivative ℚ T =
      (-1536 * X ^ 7 : ℚ⟦X⟧) + (-9216 * X ^ 9 : ℚ⟦X⟧) * T + (1024 * X ^ 7 : ℚ⟦X⟧) * T ^ 2 := by
    linear_combination ((-384 * X ^ 8 : ℚ⟦X⟧) + (-64 * X ^ 6 + 4608 * X ^ 10 : ℚ⟦X⟧) * T + (256 * X ^ 8 : ℚ⟦X⟧) * T ^ 2) * hd1 +
      ((-1536 * X ^ 7 : ℚ⟦X⟧) + (128 * X ^ 6 - 13824 * X ^ 10 : ℚ⟦X⟧) * (derivative ℚ T) + (-9216 * X ^ 9 : ℚ⟦X⟧) * T + (-768 * X ^ 8 : ℚ⟦X⟧) * T * (derivative ℚ T) + (-512 * X ^ 7 : ℚ⟦X⟧) * T ^ 2) * hP
  have hdY2 : derivative ℚ Y2 = 2 * (T) * derivative ℚ T := by
    rw [hY2]
    simp [Derivation.leibniz]
    ring
  have r0_1 : (-128 * (X * X * X * X * X * X) + 13824 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ T =
      (-1536 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-9216 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * T + (1024 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * Y2 := by
    linear_combination s1 - (1024 * X ^ 7) * hY2
  have hLr0_2 : derivative ℚ ((-128 * (X * X * X * X * X * X) + 13824 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ T) =
      (-768 * X ^ 5 + 138240 * X ^ 9) * derivative ℚ T + (-128 * X ^ 6 + 13824 * X ^ 10) * derivative ℚ (derivative ℚ T) := by
    simp [Derivation.leibniz, d128, d13824]
    ring
  have hRr0_2 : derivative ℚ ((-1536 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-9216 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * T + (1024 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * Y2) =
      (-10752 * X ^ 6) + (-82944 * X ^ 8) * T + (-9216 * X ^ 9) * derivative ℚ T + (7168 * X ^ 6) * Y2 + (1024 * X ^ 7) * derivative ℚ Y2 := by
    simp [Derivation.leibniz, d1024, d1536, d9216]
    ring
  have r0_2 : (-768 * X ^ 5 + 138240 * X ^ 9) * derivative ℚ T + (-128 * X ^ 6 + 13824 * X ^ 10) * derivative ℚ (derivative ℚ T) =
      (-10752 * X ^ 6) + (-82944 * X ^ 8) * T + (-9216 * X ^ 9) * derivative ℚ T + (7168 * X ^ 6) * Y2 + (1024 * X ^ 7) * derivative ℚ Y2 := by
    rw [← hLr0_2, ← hRr0_2, r0_1]
  have r0_2p : (-768 * (X * X * X * X * X) + 138240 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ T + (-128 * (X * X * X * X * X * X) + 13824 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ T) =
      (-10752 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (-82944 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * T + (-9216 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ T + (7168 * (X * X * X * X * X * X) : ℚ⟦X⟧) * Y2 + (1024 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2 := by linear_combination r0_2
  have hLr0_3 : derivative ℚ ((-768 * (X * X * X * X * X) + 138240 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ T + (-128 * (X * X * X * X * X * X) + 13824 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ T)) =
      (-3840 * X ^ 4 + 1244160 * X ^ 8) * derivative ℚ T + 2 * (-768 * X ^ 5 + 138240 * X ^ 9) * derivative ℚ (derivative ℚ T) + (-128 * X ^ 6 + 13824 * X ^ 10) * derivative ℚ (derivative ℚ (derivative ℚ T)) := by
    simp [Derivation.leibniz, d128, d768, d13824, d138240]
    ring
  have hRr0_3 : derivative ℚ ((-10752 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (-82944 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * T + (-9216 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ T + (7168 * (X * X * X * X * X * X) : ℚ⟦X⟧) * Y2 + (1024 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2) =
      (-64512 * X ^ 5) + (-663552 * X ^ 7) * T + 2 * (-82944 * X ^ 8) * derivative ℚ T + (-9216 * X ^ 9) * derivative ℚ (derivative ℚ T) + (43008 * X ^ 5) * Y2 + 2 * (7168 * X ^ 6) * derivative ℚ Y2 + (1024 * X ^ 7) * derivative ℚ (derivative ℚ Y2) := by
    simp [Derivation.leibniz, d1024, d7168, d9216, d10752, d82944]
    ring
  have r0_3 : (-3840 * X ^ 4 + 1244160 * X ^ 8) * derivative ℚ T + 2 * (-768 * X ^ 5 + 138240 * X ^ 9) * derivative ℚ (derivative ℚ T) + (-128 * X ^ 6 + 13824 * X ^ 10) * derivative ℚ (derivative ℚ (derivative ℚ T)) =
      (-64512 * X ^ 5) + (-663552 * X ^ 7) * T + 2 * (-82944 * X ^ 8) * derivative ℚ T + (-9216 * X ^ 9) * derivative ℚ (derivative ℚ T) + (43008 * X ^ 5) * Y2 + 2 * (7168 * X ^ 6) * derivative ℚ Y2 + (1024 * X ^ 7) * derivative ℚ (derivative ℚ Y2) := by
    rw [← hLr0_3, ← hRr0_3, r0_2p]
  have r0_3p : (-3840 * (X * X * X * X) + 1244160 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ T + 2 * ((-768 * (X * X * X * X * X) + 138240 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ T)) + (-128 * (X * X * X * X * X * X) + 13824 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ T)) =
      (-64512 * (X * X * X * X * X) : ℚ⟦X⟧) + (-663552 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * T + 2 * ((-82944 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ T) + (-9216 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ T) + (43008 * (X * X * X * X * X) : ℚ⟦X⟧) * Y2 + 2 * ((7168 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2) + (1024 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ Y2) := by linear_combination r0_3
  have hLr0_4 : derivative ℚ ((-3840 * (X * X * X * X) + 1244160 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ T + 2 * ((-768 * (X * X * X * X * X) + 138240 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ T)) + (-128 * (X * X * X * X * X * X) + 13824 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ T))) =
      (-15360 * X ^ 3 + 9953280 * X ^ 7) * derivative ℚ T + 3 * (-3840 * X ^ 4 + 1244160 * X ^ 8) * derivative ℚ (derivative ℚ T) + 3 * (-768 * X ^ 5 + 138240 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ T)) + (-128 * X ^ 6 + 13824 * X ^ 10) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ T))) := by
    simp [Derivation.leibniz, d2, d128, d768, d3840, d13824, d138240, d1244160]
    ring
  have hRr0_4 : derivative ℚ ((-64512 * (X * X * X * X * X) : ℚ⟦X⟧) + (-663552 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * T + 2 * ((-82944 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ T) + (-9216 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ T) + (43008 * (X * X * X * X * X) : ℚ⟦X⟧) * Y2 + 2 * ((7168 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2) + (1024 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ Y2)) =
      (-322560 * X ^ 4) + (-4644864 * X ^ 6) * T + 3 * (-663552 * X ^ 7) * derivative ℚ T + 3 * (-82944 * X ^ 8) * derivative ℚ (derivative ℚ T) + (-9216 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ T)) + (215040 * X ^ 4) * Y2 + 3 * (43008 * X ^ 5) * derivative ℚ Y2 + 3 * (7168 * X ^ 6) * derivative ℚ (derivative ℚ Y2) + (1024 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ Y2)) := by
    simp [Derivation.leibniz, d2, d1024, d7168, d9216, d43008, d64512, d82944, d663552]
    ring
  have r0_4 : (-15360 * X ^ 3 + 9953280 * X ^ 7) * derivative ℚ T + 3 * (-3840 * X ^ 4 + 1244160 * X ^ 8) * derivative ℚ (derivative ℚ T) + 3 * (-768 * X ^ 5 + 138240 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ T)) + (-128 * X ^ 6 + 13824 * X ^ 10) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ T))) =
      (-322560 * X ^ 4) + (-4644864 * X ^ 6) * T + 3 * (-663552 * X ^ 7) * derivative ℚ T + 3 * (-82944 * X ^ 8) * derivative ℚ (derivative ℚ T) + (-9216 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ T)) + (215040 * X ^ 4) * Y2 + 3 * (43008 * X ^ 5) * derivative ℚ Y2 + 3 * (7168 * X ^ 6) * derivative ℚ (derivative ℚ Y2) + (1024 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ Y2)) := by
    rw [← hLr0_4, ← hRr0_4, r0_3p]
  have r1_1 : (512 * (X * X * X * X * X * X * X * X) - 55296 * (X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2 =
      (2048 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (12288 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * T + (-2048 * (X * X * X * X * X * X * X) + 73728 * (X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * Y2 := by
    linear_combination (512 * X ^ 8 - 55296 * X ^ 12) * hdY2 + ((-8 * X ^ 2 : ℚ⟦X⟧) * T) * s1 +
      ((2048 * X ^ 7 : ℚ⟦X⟧)) * hP - (-2048 * X ^ 7 + 73728 * X ^ 11) * hY2
  have hLr1_2 : derivative ℚ ((512 * (X * X * X * X * X * X * X * X) - 55296 * (X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2) =
      (4096 * X ^ 7 - 663552 * X ^ 11) * derivative ℚ Y2 + (512 * X ^ 8 - 55296 * X ^ 12) * derivative ℚ (derivative ℚ Y2) := by
    simp [Derivation.leibniz, d512, d55296]
    ring
  have hRr1_2 : derivative ℚ ((2048 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (12288 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * T + (-2048 * (X * X * X * X * X * X * X) + 73728 * (X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * Y2) =
      (14336 * X ^ 6) + (110592 * X ^ 8) * T + (12288 * X ^ 9) * derivative ℚ T + (-14336 * X ^ 6 + 811008 * X ^ 10) * Y2 + (-2048 * X ^ 7 + 73728 * X ^ 11) * derivative ℚ Y2 := by
    simp [Derivation.leibniz, d2048, d12288, d73728]
    ring
  have r1_2 : (4096 * X ^ 7 - 663552 * X ^ 11) * derivative ℚ Y2 + (512 * X ^ 8 - 55296 * X ^ 12) * derivative ℚ (derivative ℚ Y2) =
      (14336 * X ^ 6) + (110592 * X ^ 8) * T + (12288 * X ^ 9) * derivative ℚ T + (-14336 * X ^ 6 + 811008 * X ^ 10) * Y2 + (-2048 * X ^ 7 + 73728 * X ^ 11) * derivative ℚ Y2 := by
    rw [← hLr1_2, ← hRr1_2, r1_1]
  have r1_2p : (4096 * (X * X * X * X * X * X * X) - 663552 * (X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2 + (512 * (X * X * X * X * X * X * X * X) - 55296 * (X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ Y2) =
      (14336 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (110592 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * T + (12288 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ T + (-14336 * (X * X * X * X * X * X) + 811008 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * Y2 + (-2048 * (X * X * X * X * X * X * X) + 73728 * (X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2 := by linear_combination r1_2
  have hLr1_3 : derivative ℚ ((4096 * (X * X * X * X * X * X * X) - 663552 * (X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2 + (512 * (X * X * X * X * X * X * X * X) - 55296 * (X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ Y2)) =
      (28672 * X ^ 6 - 7299072 * X ^ 10) * derivative ℚ Y2 + 2 * (4096 * X ^ 7 - 663552 * X ^ 11) * derivative ℚ (derivative ℚ Y2) + (512 * X ^ 8 - 55296 * X ^ 12) * derivative ℚ (derivative ℚ (derivative ℚ Y2)) := by
    simp [Derivation.leibniz, d512, d4096, d55296, d663552]
    ring
  have hRr1_3 : derivative ℚ ((14336 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (110592 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * T + (12288 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ T + (-14336 * (X * X * X * X * X * X) + 811008 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * Y2 + (-2048 * (X * X * X * X * X * X * X) + 73728 * (X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2) =
      (86016 * X ^ 5) + (884736 * X ^ 7) * T + 2 * (110592 * X ^ 8) * derivative ℚ T + (12288 * X ^ 9) * derivative ℚ (derivative ℚ T) + (-86016 * X ^ 5 + 8110080 * X ^ 9) * Y2 + 2 * (-14336 * X ^ 6 + 811008 * X ^ 10) * derivative ℚ Y2 + (-2048 * X ^ 7 + 73728 * X ^ 11) * derivative ℚ (derivative ℚ Y2) := by
    simp [Derivation.leibniz, d2048, d12288, d14336, d73728, d110592, d811008]
    ring
  have r1_3 : (28672 * X ^ 6 - 7299072 * X ^ 10) * derivative ℚ Y2 + 2 * (4096 * X ^ 7 - 663552 * X ^ 11) * derivative ℚ (derivative ℚ Y2) + (512 * X ^ 8 - 55296 * X ^ 12) * derivative ℚ (derivative ℚ (derivative ℚ Y2)) =
      (86016 * X ^ 5) + (884736 * X ^ 7) * T + 2 * (110592 * X ^ 8) * derivative ℚ T + (12288 * X ^ 9) * derivative ℚ (derivative ℚ T) + (-86016 * X ^ 5 + 8110080 * X ^ 9) * Y2 + 2 * (-14336 * X ^ 6 + 811008 * X ^ 10) * derivative ℚ Y2 + (-2048 * X ^ 7 + 73728 * X ^ 11) * derivative ℚ (derivative ℚ Y2) := by
    rw [← hLr1_3, ← hRr1_3, r1_2p]
  have e0 : (2 : ℚ⟦X⟧) * G =
      (-1 : ℚ⟦X⟧) + (1 + 2 * X : ℚ⟦X⟧) * T + (0 : ℚ⟦X⟧) * Y2 := by linear_combination hG
  have hLe1 : derivative ℚ ((2 : ℚ⟦X⟧) * G) =
      (0) * G + (2) * derivative ℚ G := by
    simp [Derivation.leibniz, d2]
  have hRe1 : derivative ℚ ((-1 : ℚ⟦X⟧) + (1 + 2 * X : ℚ⟦X⟧) * T + (0 : ℚ⟦X⟧) * Y2) =
      (0) + (2) * T + (1 + 2 * X) * derivative ℚ T + (0) * Y2 + (0) * derivative ℚ Y2 := by
    simp [Derivation.leibniz, d2]
    ring
  have e1 : (0) * G + (2) * derivative ℚ G =
      (0) + (2) * T + (1 + 2 * X) * derivative ℚ T + (0) * Y2 + (0) * derivative ℚ Y2 := by
    rw [← hLe1, ← hRe1, e0]
  have e1p : (0 : ℚ⟦X⟧) * G + (2 : ℚ⟦X⟧) * derivative ℚ G =
      (0 : ℚ⟦X⟧) + (2 : ℚ⟦X⟧) * T + (1 + 2 * X : ℚ⟦X⟧) * derivative ℚ T + (0 : ℚ⟦X⟧) * Y2 + (0 : ℚ⟦X⟧) * derivative ℚ Y2 := by linear_combination e1
  have hLe2 : derivative ℚ ((0 : ℚ⟦X⟧) * G + (2 : ℚ⟦X⟧) * derivative ℚ G) =
      (0) * G + 2 * (0) * derivative ℚ G + (2) * derivative ℚ (derivative ℚ G) := by
    simp [Derivation.leibniz, d2]
  have hRe2 : derivative ℚ ((0 : ℚ⟦X⟧) + (2 : ℚ⟦X⟧) * T + (1 + 2 * X : ℚ⟦X⟧) * derivative ℚ T + (0 : ℚ⟦X⟧) * Y2 + (0 : ℚ⟦X⟧) * derivative ℚ Y2) =
      (0) + (0) * T + 2 * (2) * derivative ℚ T + (1 + 2 * X) * derivative ℚ (derivative ℚ T) + (0) * Y2 + 2 * (0) * derivative ℚ Y2 + (0) * derivative ℚ (derivative ℚ Y2) := by
    simp [Derivation.leibniz, d2]
    ring
  have e2 : (0) * G + 2 * (0) * derivative ℚ G + (2) * derivative ℚ (derivative ℚ G) =
      (0) + (0) * T + 2 * (2) * derivative ℚ T + (1 + 2 * X) * derivative ℚ (derivative ℚ T) + (0) * Y2 + 2 * (0) * derivative ℚ Y2 + (0) * derivative ℚ (derivative ℚ Y2) := by
    rw [← hLe2, ← hRe2, e1p]
  have e2p : (0 : ℚ⟦X⟧) * G + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ G) + (2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) =
      (0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * T + 2 * ((2 : ℚ⟦X⟧) * derivative ℚ T) + (1 + 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ T) + (0 : ℚ⟦X⟧) * Y2 + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ Y2) + (0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ Y2) := by linear_combination e2
  have hLe3 : derivative ℚ ((0 : ℚ⟦X⟧) * G + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ G) + (2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) =
      (0) * G + 3 * (0) * derivative ℚ G + 3 * (0) * derivative ℚ (derivative ℚ G) + (2) * derivative ℚ (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d2]
  have hRe3 : derivative ℚ ((0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * T + 2 * ((2 : ℚ⟦X⟧) * derivative ℚ T) + (1 + 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ T) + (0 : ℚ⟦X⟧) * Y2 + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ Y2) + (0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ Y2)) =
      (0) + (0) * T + 3 * (0) * derivative ℚ T + 3 * (2) * derivative ℚ (derivative ℚ T) + (1 + 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ T)) + (0) * Y2 + 3 * (0) * derivative ℚ Y2 + 3 * (0) * derivative ℚ (derivative ℚ Y2) + (0) * derivative ℚ (derivative ℚ (derivative ℚ Y2)) := by
    simp [Derivation.leibniz, d2]
    ring
  have e3 : (0) * G + 3 * (0) * derivative ℚ G + 3 * (0) * derivative ℚ (derivative ℚ G) + (2) * derivative ℚ (derivative ℚ (derivative ℚ G)) =
      (0) + (0) * T + 3 * (0) * derivative ℚ T + 3 * (2) * derivative ℚ (derivative ℚ T) + (1 + 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ T)) + (0) * Y2 + 3 * (0) * derivative ℚ Y2 + 3 * (0) * derivative ℚ (derivative ℚ Y2) + (0) * derivative ℚ (derivative ℚ (derivative ℚ Y2)) := by
    rw [← hLe3, ← hRe3, e2p]
  have e3p : (0 : ℚ⟦X⟧) * G + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ G) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + (2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G)) =
      (0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * T + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ T) + 3 * ((2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ T)) + (1 + 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ T)) + (0 : ℚ⟦X⟧) * Y2 + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ Y2) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ Y2)) + (0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ Y2)) := by linear_combination e3
  have hLe4 : derivative ℚ ((0 : ℚ⟦X⟧) * G + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ G) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + (2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G))) =
      (0) * G + 4 * (0) * derivative ℚ G + 6 * (0) * derivative ℚ (derivative ℚ G) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) := by
    simp [Derivation.leibniz, d2]
  have hRe4 : derivative ℚ ((0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * T + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ T) + 3 * ((2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ T)) + (1 + 2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ T)) + (0 : ℚ⟦X⟧) * Y2 + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ Y2) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ Y2)) + (0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ Y2))) =
      (0) + (0) * T + 4 * (0) * derivative ℚ T + 6 * (0) * derivative ℚ (derivative ℚ T) + 4 * (2) * derivative ℚ (derivative ℚ (derivative ℚ T)) + (1 + 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ T))) + (0) * Y2 + 4 * (0) * derivative ℚ Y2 + 6 * (0) * derivative ℚ (derivative ℚ Y2) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ Y2)) + (0) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ Y2))) := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have e4 : (0) * G + 4 * (0) * derivative ℚ G + 6 * (0) * derivative ℚ (derivative ℚ G) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) =
      (0) + (0) * T + 4 * (0) * derivative ℚ T + 6 * (0) * derivative ℚ (derivative ℚ T) + 4 * (2) * derivative ℚ (derivative ℚ (derivative ℚ T)) + (1 + 2 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ T))) + (0) * Y2 + 4 * (0) * derivative ℚ Y2 + 6 * (0) * derivative ℚ (derivative ℚ Y2) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ Y2)) + (0) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ Y2))) := by
    rw [← hLe4, ← hRe4, e3p]
  have hfull : (256 * X ^ 5 - 82944 * X ^ 9 + 8957952 * X ^ 13 - 322486272 * X ^ 17 : ℚ⟦X⟧) * ((23 * X ^ 4 - 2484 * X ^ 8) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (22 * X ^ 3 - 27216 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-312 * X ^ 2 + 324 * X ^ 3 - 648 * X ^ 4 + 1296 * X ^ 5 - 63192 * X ^ 6) * derivative ℚ (derivative ℚ G) + (180 * X + 408 * X ^ 2 - 2112 * X ^ 3 + 6816 * X ^ 4 - 10176 * X ^ 5) * derivative ℚ G + (-360 * X - 96 * X ^ 2 + 4416 * X ^ 3 - 3024 * X ^ 4) * G - (180 * X - 216 * X ^ 2 - 3504 * X ^ 3 + 1512 * X ^ 4)) = 0 := by
    linear_combination (2944 * X ^ 9 - 1271808 * X ^ 13 + 206032896 * X ^ 17 - 14834368512 * X ^ 21 + 400527949824 * X ^ 25) * e4 +
      (2816 * X ^ 8 - 4396032 * X ^ 12 + 1227239424 * X ^ 16 - 125447159808 * X ^ 20 + 4388393189376 * X ^ 24) * e3 +
      (-39936 * X ^ 7 + 41472 * X ^ 8 - 82944 * X ^ 9 + 165888 * X ^ 10 + 4850688 * X ^ 11 - 13436928 * X ^ 12 + 26873856 * X ^ 13 - 53747712 * X ^ 14 + 1223258112 * X ^ 15 + 1451188224 * X ^ 16 - 2902376448 * X ^ 17 + 5804752896 * X ^ 18 - 232727592960 * X ^ 19 - 52242776064 * X ^ 20 + 104485552128 * X ^ 21 - 208971104256 * X ^ 22 + 10189276250112 * X ^ 23) * e2 +
      (23040 * X ^ 6 + 52224 * X ^ 7 - 270336 * X ^ 8 + 872448 * X ^ 9 - 8767488 * X ^ 10 - 16920576 * X ^ 11 + 87588864 * X ^ 12 - 282673152 * X ^ 13 + 1228234752 * X ^ 14 + 1827422208 * X ^ 15 - 9459597312 * X ^ 16 + 30528700416 * X ^ 17 - 74601824256 * X ^ 18 - 65787199488 * X ^ 19 + 340545503232 * X ^ 20 - 1099033214976 * X ^ 21 + 1640810151936 * X ^ 22) * e1 +
      (-46080 * X ^ 6 - 12288 * X ^ 7 + 565248 * X ^ 8 - 387072 * X ^ 9 + 14929920 * X ^ 10 + 3981312 * X ^ 11 - 183140352 * X ^ 12 + 125411328 * X ^ 13 - 1612431360 * X ^ 14 - 429981696 * X ^ 15 + 19779158016 * X ^ 16 - 13544423424 * X ^ 17 + 58047528960 * X ^ 18 + 15479341056 * X ^ 19 - 712049688576 * X ^ 20 + 487599243264 * X ^ 21) * e0 +
      (-23 * X ^ 3 - 46 * X ^ 4 + 7452 * X ^ 7 + 14904 * X ^ 8 - 804816 * X ^ 11 - 1609632 * X ^ 12 + 28973376 * X ^ 15 + 57946752 * X ^ 16) * r0_4 +
      (392 * X ^ 2 + 600 * X ^ 3 - 133632 * X ^ 6 - 207648 * X ^ 7 + 15147648 * X ^ 10 + 23856768 * X ^ 11 - 571069440 * X ^ 14 - 910351872 * X ^ 15) * r0_3 +
      (-46 * X ^ 2 - 92 * X ^ 3 + 9936 * X ^ 6 + 19872 * X ^ 7 - 536544 * X ^ 10 - 1073088 * X ^ 11) * r1_3 +
      (-2322 * X - 2892 * X ^ 2 + 805608 * X ^ 5 + 990576 * X ^ 6 - 98483040 * X ^ 9 - 124213824 * X ^ 10 + 4164607872 * X ^ 13 + 5504101632 * X ^ 14) * r0_2 +
      (738 * X + 1108 * X ^ 2 - 199152 * X ^ 5 - 318816 * X ^ 6 + 12900384 * X ^ 9 + 21508416 * X ^ 10) * r1_2 +
      (4752 + 5352 * X - 1650240 * X ^ 4 - 1768608 * X ^ 5 + 204602112 * X ^ 8 + 200714112 * X ^ 9 - 11307174912 * X ^ 12 - 12734848512 * X ^ 13) * r0_1 +
      (-3168 - 3568 * X + 943488 * X ^ 4 + 1130112 * X ^ 5 - 82114560 * X ^ 8 - 114773760 * X ^ 9) * r1_1
  have hM0 : (256 - 82944 * X ^ 4 + 8957952 * X ^ 8 - 322486272 * X ^ 12 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    have kc : constantCoeff (256 : ℚ⟦X⟧) = 256 := cnum 256
    simp [kc] at h'
  have hM : (256 * X ^ 5 - 82944 * X ^ 9 + 8957952 * X ^ 13 - 322486272 * X ^ 17 : ℚ⟦X⟧) ≠ 0 := by
    have e : (256 * X ^ 5 - 82944 * X ^ 9 + 8957952 * X ^ 13 - 322486272 * X ^ 17 : ℚ⟦X⟧) = X ^ 5 * (256 - 82944 * X ^ 4 + 8957952 * X ^ 8 - 322486272 * X ^ 12 : ℚ⟦X⟧) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 5 X_ne_zero) hM0
  have h := (mul_eq_zero.mp hfull).resolve_left hM
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem keyC (G T Y2 : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * T ^ 2 + (-4 * X ^ 2 : ℚ⟦X⟧) * T ^ 3 = 0)
    (hY2 : Y2 = T * T)
    (hG : (2) * G = (-1) + (1 + 2 * X) * T + (0) * Y2) :
    derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) * X * X * X * X * C 23 + derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) * X * X * X * X * X * X * X * X * C (-2484) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 22 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * C (-27216) +
      derivative ℚ (derivative ℚ G) * X * X * C (-312) + derivative ℚ (derivative ℚ G) * X * X * X * C 324 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-648) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 1296 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-63192) + derivative ℚ G * X * C 180 +
      derivative ℚ G * X * X * C 408 + derivative ℚ G * X * X * X * C (-2112) +
      derivative ℚ G * X * X * X * X * C 6816 + derivative ℚ G * X * X * X * X * X * C (-10176) +
      G * X * C (-360) + G * X * X * C (-96) +
      G * X * X * X * C 4416 + G * X * X * X * X * C (-3024) =
      C 180 * X + C (-216) * X * X +
      C (-3504) * X * X * X + C 1512 * X * X * X * X := by
  have h := key G T Y2 hP hY2 hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem rel (G T Y2 : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * T ^ 2 + (-4 * X ^ 2 : ℚ⟦X⟧) * T ^ 3 = 0)
    (hY2 : Y2 = T * T)
    (hG : (2) * G = (-1) + (1 + 2 * X) * T + (0) * Y2) (m : ℕ) :
    23 * ((m : ℚ) + 8) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-2484) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1 + 1) G +
      22 * ((m : ℚ) + 8) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-27216) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-312) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 324 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-648) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 1296 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-63192) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + 180 * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      408 * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-2112) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      6816 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-10176) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-360) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-96) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      4416 * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-3024) * coeff (m + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G T Y2 hP hY2 hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem relE0 (G T Y2 : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * T ^ 2 + (-4 * X ^ 2 : ℚ⟦X⟧) * T ^ 3 = 0)
    (hY2 : Y2 = T * T)
    (hG : (2) * G = (-1) + (1 + 2 * X) * T + (0) * Y2) :
    2760 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 1320 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-6240) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 3888 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-3888) * coeff (0 + 1 + 1 + 1) G + 2592 * coeff (0 + 1 + 1) G +
      900 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 1632 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-6336) * coeff (0 + 1 + 1 + 1) G + 13632 * coeff (0 + 1 + 1) G +
      (-10176) * coeff (0 + 1) G + (-360) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-96) * coeff (0 + 1 + 1 + 1) G + 4416 * coeff (0 + 1 + 1) G +
      (-3024) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G T Y2 hP hY2 hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem relE1 (G T Y2 : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * T ^ 2 + (-4 * X ^ 2 : ℚ⟦X⟧) * T ^ 3 = 0)
    (hY2 : Y2 = T * T)
    (hG : (2) * G = (-1) + (1 + 2 * X) * T + (0) * Y2) :
    8280 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 2640 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-9360) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 6480 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-7776) * coeff (0 + 1 + 1 + 1 + 1) G + 7776 * coeff (0 + 1 + 1 + 1) G +
      (-126384) * coeff (0 + 1 + 1) G + 1080 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      2040 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-8448) * coeff (0 + 1 + 1 + 1 + 1) G +
      20448 * coeff (0 + 1 + 1 + 1) G + (-20352) * coeff (0 + 1 + 1) G +
      (-360) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-96) * coeff (0 + 1 + 1 + 1 + 1) G +
      4416 * coeff (0 + 1 + 1 + 1) G + (-3024) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G T Y2 hP hY2 hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem relE2 (G T Y2 : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * T ^ 2 + (-4 * X ^ 2 : ℚ⟦X⟧) * T ^ 3 = 0)
    (hY2 : Y2 = T * T)
    (hG : (2) * G = (-1) + (1 + 2 * X) * T + (0) * Y2) :
    19320 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 4620 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-163296) * coeff (0 + 1 + 1 + 1) G + (-13104) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      9720 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-12960) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      15552 * coeff (0 + 1 + 1 + 1 + 1) G + (-379152) * coeff (0 + 1 + 1 + 1) G +
      1260 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 2448 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-10560) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 27264 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-30528) * coeff (0 + 1 + 1 + 1) G + (-360) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-96) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 4416 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-3024) * coeff (0 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G T Y2 hP hY2 hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A089073Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 16000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a089073.main := by
  intro T G hT _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  rw [e1, e2, e3, e4]
  have hP : (-1 : PowerSeries ℚ) + (1 : PowerSeries ℚ) * T ^ 2 + (-4 * PowerSeries.X ^ 2 : PowerSeries ℚ) * T ^ 3 = 0 := by linear_combination hT
  have hGl : (2) * G = (-1) + (1 + 2 * PowerSeries.X) * T + (0) * (T * T) := by linear_combination hG
  cases m with
  | zero =>
    have r := A089073Aux.relE0 G T (T * T) hP rfl hGl
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A089073Aux.relE1 G T (T * T) hP rfl hGl
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A089073Aux.relE2 G T (T * T) hP rfl hGl
        push_cast
        linear_combination r
      | succ m =>
        have r := A089073Aux.rel G T (T * T) hP rfl hGl m
        push_cast
        linear_combination r
