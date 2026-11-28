import OMAStatements.S_oeis_a032123

-- Problem: A032123: Number of 2n-bead black-white reversible strings with n black beads.
-- Upstream: formal-conjectures statements/oeis-a032123.lean:0 (declaration OMA.S_oeis_a032123.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A032123Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (X ^ 2 - 2 * X ^ 3 + X ^ 4 : ℚ⟦X⟧) + (-1 + 6 * X - 2 * X ^ 2 - 32 * X ^ 3 + 24 * X ^ 4 + 32 * X ^ 5 : ℚ⟦X⟧) * G ^ 2 + (1 - 8 * X + 8 * X ^ 2 + 64 * X ^ 3 - 112 * X ^ 4 - 128 * X ^ 5 + 256 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    (X ^ 2 - 6 * X ^ 3 + 8 * X ^ 4 + 8 * X ^ 5 - 48 * X ^ 6 + 64 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-4 * X ^ 2 - 16 * X ^ 3 + 96 * X ^ 4 - 128 * X ^ 5 + 160 * X ^ 6) * derivative ℚ G + (-4 * X ^ 2 + 40 * X ^ 3 - 32 * X ^ 4 + 32 * X ^ 5) * G =
      0 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d96 : derivative ℚ (96 : ℚ⟦X⟧) = 0 := dnum 96
  have d112 : derivative ℚ (112 : ℚ⟦X⟧) = 0 := dnum 112
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d160 : derivative ℚ (160 : ℚ⟦X⟧) = 0 := dnum 160
  have d192 : derivative ℚ (192 : ℚ⟦X⟧) = 0 := dnum 192
  have d256 : derivative ℚ (256 : ℚ⟦X⟧) = 0 := dnum 256
  have d448 : derivative ℚ (448 : ℚ⟦X⟧) = 0 := dnum 448
  have d512 : derivative ℚ (512 : ℚ⟦X⟧) = 0 := dnum 512
  have d640 : derivative ℚ (640 : ℚ⟦X⟧) = 0 := dnum 640
  have d1024 : derivative ℚ (1024 : ℚ⟦X⟧) = 0 := dnum 1024
  have d1536 : derivative ℚ (1536 : ℚ⟦X⟧) = 0 := dnum 1536
  have hp0 : (1 * (X * X) - 2 * (X * X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) + (-1 + 6 * X - 2 * (X * X) - 32 * (X * X * X) + 24 * (X * X * X * X) + 32 * (X * X * X * X * X) : ℚ⟦X⟧) * G * G + (1 - 8 * X + 8 * (X * X) + 64 * (X * X * X) - 112 * (X * X * X * X) - 128 * (X * X * X * X * X) + 256 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 * (X * X) - 2 * (X * X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) + (-1 + 6 * X - 2 * (X * X) - 32 * (X * X * X) + 24 * (X * X * X * X) + 32 * (X * X * X * X * X) : ℚ⟦X⟧) * G * G + (1 - 8 * X + 8 * (X * X) + 64 * (X * X * X) - 112 * (X * X * X * X) - 128 * (X * X * X * X * X) + 256 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * G * G * G) =
      (2 * X - 6 * X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) + (-2 + 12 * X - 4 * X ^ 2 - 64 * X ^ 3 + 48 * X ^ 4 + 64 * X ^ 5 : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 4 * X - 96 * X ^ 2 + 96 * X ^ 3 + 160 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 + (4 - 32 * X + 32 * X ^ 2 + 256 * X ^ 3 - 448 * X ^ 4 - 512 * X ^ 5 + 1024 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-8 + 16 * X + 192 * X ^ 2 - 448 * X ^ 3 - 640 * X ^ 4 + 1536 * X ^ 5 : ℚ⟦X⟧) * G ^ 4 := by
    simp [Derivation.leibniz, d2, d6, d8, d24, d32, d64, d112, d128, d256]
    ring
  have hd1 : (2 * X - 6 * X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) + (-2 + 12 * X - 4 * X ^ 2 - 64 * X ^ 3 + 48 * X ^ 4 + 64 * X ^ 5 : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 4 * X - 96 * X ^ 2 + 96 * X ^ 3 + 160 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 + (4 - 32 * X + 32 * X ^ 2 + 256 * X ^ 3 - 448 * X ^ 4 - 512 * X ^ 5 + 1024 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-8 + 16 * X + 192 * X ^ 2 - 448 * X ^ 3 - 640 * X ^ 4 + 1536 * X ^ 5 : ℚ⟦X⟧) * G ^ 4 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (2 * X - 6 * (X * X) + 4 * (X * X * X) : ℚ⟦X⟧) + (-2 + 12 * X - 4 * (X * X) - 64 * (X * X * X) + 48 * (X * X * X * X) + 64 * (X * X * X * X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 4 * X - 96 * (X * X) + 96 * (X * X * X) + 160 * (X * X * X * X) : ℚ⟦X⟧) * G * G + (4 - 32 * X + 32 * (X * X) + 256 * (X * X * X) - 448 * (X * X * X * X) - 512 * (X * X * X * X * X) + 1024 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (-8 + 16 * X + 192 * (X * X) - 448 * (X * X * X) - 640 * (X * X * X * X) + 1536 * (X * X * X * X * X) : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((2 * X - 6 * (X * X) + 4 * (X * X * X) : ℚ⟦X⟧) + (-2 + 12 * X - 4 * (X * X) - 64 * (X * X * X) + 48 * (X * X * X * X) + 64 * (X * X * X * X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 4 * X - 96 * (X * X) + 96 * (X * X * X) + 160 * (X * X * X * X) : ℚ⟦X⟧) * G * G + (4 - 32 * X + 32 * (X * X) + 256 * (X * X * X) - 448 * (X * X * X * X) - 512 * (X * X * X * X * X) + 1024 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (-8 + 16 * X + 192 * (X * X) - 448 * (X * X * X) - 640 * (X * X * X * X) + 1536 * (X * X * X * X * X) : ℚ⟦X⟧) * G * G * G * G) =
      (2 - 12 * X + 12 * X ^ 2 : ℚ⟦X⟧) + (-2 + 12 * X - 4 * X ^ 2 - 64 * X ^ 3 + 48 * X ^ 4 + 64 * X ^ 5 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 + 12 * X - 4 * X ^ 2 - 64 * X ^ 3 + 48 * X ^ 4 + 64 * X ^ 5 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (24 - 16 * X - 384 * X ^ 2 + 384 * X ^ 3 + 640 * X ^ 4 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-4 - 192 * X + 288 * X ^ 2 + 640 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 + (12 - 96 * X + 96 * X ^ 2 + 768 * X ^ 3 - 1344 * X ^ 4 - 1536 * X ^ 5 + 3072 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 - 32 * X + 32 * X ^ 2 + 256 * X ^ 3 - 448 * X ^ 4 - 512 * X ^ 5 + 1024 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (-64 + 128 * X + 1536 * X ^ 2 - 3584 * X ^ 3 - 5120 * X ^ 4 + 12288 * X ^ 5 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (16 + 384 * X - 1344 * X ^ 2 - 2560 * X ^ 3 + 7680 * X ^ 4 : ℚ⟦X⟧) * G ^ 4 := by
    simp [Derivation.leibniz, d2, d4, d6, d8, d12, d16, d32, d48, d64, d96, d160, d192, d256, d448, d512, d640, d1024, d1536]
    ring
  have hd2 : (2 - 12 * X + 12 * X ^ 2 : ℚ⟦X⟧) + (-2 + 12 * X - 4 * X ^ 2 - 64 * X ^ 3 + 48 * X ^ 4 + 64 * X ^ 5 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 + 12 * X - 4 * X ^ 2 - 64 * X ^ 3 + 48 * X ^ 4 + 64 * X ^ 5 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (24 - 16 * X - 384 * X ^ 2 + 384 * X ^ 3 + 640 * X ^ 4 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-4 - 192 * X + 288 * X ^ 2 + 640 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 + (12 - 96 * X + 96 * X ^ 2 + 768 * X ^ 3 - 1344 * X ^ 4 - 1536 * X ^ 5 + 3072 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 - 32 * X + 32 * X ^ 2 + 256 * X ^ 3 - 448 * X ^ 4 - 512 * X ^ 5 + 1024 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (-64 + 128 * X + 1536 * X ^ 2 - 3584 * X ^ 3 - 5120 * X ^ 4 + 12288 * X ^ 5 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (16 + 384 * X - 1344 * X ^ 2 - 2560 * X ^ 3 + 7680 * X ^ 4 : ℚ⟦X⟧) * G ^ 4 = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((-2 + 12 * X - 4 * X ^ 2 - 64 * X ^ 3 + 48 * X ^ 4 + 64 * X ^ 5 : ℚ⟦X⟧) * G + (4 - 32 * X + 32 * X ^ 2 + 256 * X ^ 3 - 448 * X ^ 4 - 512 * X ^ 5 + 1024 * X ^ 6 : ℚ⟦X⟧) * G ^ 3) ^ 3 * ((X ^ 2 - 6 * X ^ 3 + 8 * X ^ 4 + 8 * X ^ 5 - 48 * X ^ 6 + 64 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-4 * X ^ 2 - 16 * X ^ 3 + 96 * X ^ 4 - 128 * X ^ 5 + 160 * X ^ 6) * derivative ℚ G + (-4 * X ^ 2 + 40 * X ^ 3 - 32 * X ^ 4 + 32 * X ^ 5) * G - (0)) = 0 := by
    linear_combination ((8 * X ^ 2 - 128 * X ^ 3 + 784 * X ^ 4 - 2016 * X ^ 5 - 256 * X ^ 6 + 14720 * X ^ 7 - 34816 * X ^ 8 + 15872 * X ^ 9 + 75776 * X ^ 10 - 153600 * X ^ 11 + 77824 * X ^ 12 + 65536 * X ^ 13 - 65536 * X ^ 14 : ℚ⟦X⟧) + (48 * X ^ 2 - 672 * X ^ 3 + 2688 * X ^ 4 + 3456 * X ^ 5 - 46080 * X ^ 6 + 35328 * X ^ 7 + 390144 * X ^ 8 - 798720 * X ^ 9 - 1167360 * X ^ 10 + 4571136 * X ^ 11 - 1327104 * X ^ 12 - 7569408 * X ^ 13 + 7864320 * X ^ 14 - 1572864 * X ^ 15 : ℚ⟦X⟧) * G ^ 2 + (-192 * X ^ 2 + 4224 * X ^ 3 - 32256 * X ^ 4 + 75264 * X ^ 5 + 251904 * X ^ 6 - 1529856 * X ^ 7 + 884736 * X ^ 8 + 8036352 * X ^ 9 - 13418496 * X ^ 10 - 13959168 * X ^ 11 + 42860544 * X ^ 12 - 4718592 * X ^ 13 - 44040192 * X ^ 14 + 25165824 * X ^ 15 : ℚ⟦X⟧) * G ^ 4 + (256 * X ^ 2 - 5632 * X ^ 3 + 45056 * X ^ 4 - 120832 * X ^ 5 - 335872 * X ^ 6 + 2637824 * X ^ 7 - 2686976 * X ^ 8 - 15138816 * X ^ 9 + 36765696 * X ^ 10 + 25296896 * X ^ 11 - 146800640 * X ^ 12 + 46661632 * X ^ 13 + 243269632 * X ^ 14 - 184549376 * X ^ 15 - 134217728 * X ^ 16 + 134217728 * X ^ 17 : ℚ⟦X⟧) * G ^ 6) * hP +
      ((-4 * X ^ 3 + 60 * X ^ 4 - 336 * X ^ 5 + 728 * X ^ 6 + 576 * X ^ 7 - 6336 * X ^ 8 + 12096 * X ^ 9 - 1152 * X ^ 10 - 32256 * X ^ 11 + 50176 * X ^ 12 - 15360 * X ^ 13 - 24576 * X ^ 14 + 16384 * X ^ 15 : ℚ⟦X⟧) + (-4 * X ^ 2 + 72 * X ^ 3 - 480 * X ^ 4 + 1152 * X ^ 5 + 1968 * X ^ 6 - 16800 * X ^ 7 + 26368 * X ^ 8 + 38016 * X ^ 9 - 179712 * X ^ 10 + 146944 * X ^ 11 + 294912 * X ^ 12 - 632832 * X ^ 13 + 61440 * X ^ 14 + 638976 * X ^ 15 - 196608 * X ^ 16 - 262144 * X ^ 17 : ℚ⟦X⟧) * G * (derivative ℚ G) + (20 * X ^ 2 - 304 * X ^ 3 + 1472 * X ^ 4 - 64 * X ^ 5 - 22432 * X ^ 6 + 61952 * X ^ 7 + 49536 * X ^ 8 - 497664 * X ^ 9 + 548352 * X ^ 10 + 1232896 * X ^ 11 - 3061760 * X ^ 12 + 114688 * X ^ 13 + 4587520 * X ^ 14 - 2883584 * X ^ 15 - 524288 * X ^ 16 : ℚ⟦X⟧) * G ^ 2 + (32 * X ^ 2 - 640 * X ^ 3 + 4800 * X ^ 4 - 13440 * X ^ 5 - 20736 * X ^ 6 + 227328 * X ^ 7 - 419840 * X ^ 8 - 634880 * X ^ 9 + 3538944 * X ^ 10 - 3276800 * X ^ 11 - 7749632 * X ^ 12 + 20152320 * X ^ 13 - 5308416 * X ^ 14 - 31457280 * X ^ 15 + 31457280 * X ^ 16 + 8388608 * X ^ 17 - 16777216 * X ^ 18 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-72 * X ^ 2 + 1280 * X ^ 3 - 7936 * X ^ 4 + 10688 * X ^ 5 + 99584 * X ^ 6 - 458752 * X ^ 7 + 195584 * X ^ 8 + 3115008 * X ^ 9 - 6764544 * X ^ 10 - 4571136 * X ^ 11 + 30687232 * X ^ 12 - 19152896 * X ^ 13 - 47513600 * X ^ 14 + 60030976 * X ^ 15 + 13631488 * X ^ 16 - 33554432 * X ^ 17 : ℚ⟦X⟧) * G ^ 4 + (-48 * X ^ 2 + 1056 * X ^ 3 - 8832 * X ^ 4 + 28800 * X ^ 5 + 34560 * X ^ 6 - 534528 * X ^ 7 + 1191936 * X ^ 8 + 1609728 * X ^ 9 - 11489280 * X ^ 10 + 12656640 * X ^ 11 + 30769152 * X ^ 12 - 94470144 * X ^ 13 + 33619968 * X ^ 14 + 200540160 * X ^ 15 - 283115520 * X ^ 16 - 50331648 * X ^ 17 + 352321536 * X ^ 18 - 201326592 * X ^ 19 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (96 * X ^ 2 - 1792 * X ^ 3 + 11392 * X ^ 4 - 11264 * X ^ 5 - 198656 * X ^ 6 + 876544 * X ^ 7 - 143360 * X ^ 8 - 7831552 * X ^ 9 + 17326080 * X ^ 10 + 15532032 * X ^ 11 - 107577344 * X ^ 12 + 86245376 * X ^ 13 + 226230272 * X ^ 14 - 432013312 * X ^ 15 - 16777216 * X ^ 16 + 536870912 * X ^ 17 - 335544320 * X ^ 18 : ℚ⟦X⟧) * G ^ 6) * hd1 +
      ((4 * X ^ 2 - 72 * X ^ 3 + 480 * X ^ 4 - 1152 * X ^ 5 - 1968 * X ^ 6 + 16800 * X ^ 7 - 26368 * X ^ 8 - 38016 * X ^ 9 + 179712 * X ^ 10 - 146944 * X ^ 11 - 294912 * X ^ 12 + 632832 * X ^ 13 - 61440 * X ^ 14 - 638976 * X ^ 15 + 196608 * X ^ 16 + 262144 * X ^ 17 : ℚ⟦X⟧) * G ^ 2 + (-16 * X ^ 2 + 320 * X ^ 3 - 2400 * X ^ 4 + 6720 * X ^ 5 + 10368 * X ^ 6 - 113664 * X ^ 7 + 209920 * X ^ 8 + 317440 * X ^ 9 - 1769472 * X ^ 10 + 1638400 * X ^ 11 + 3874816 * X ^ 12 - 10076160 * X ^ 13 + 2654208 * X ^ 14 + 15728640 * X ^ 15 - 15728640 * X ^ 16 - 4194304 * X ^ 17 + 8388608 * X ^ 18 : ℚ⟦X⟧) * G ^ 4 + (16 * X ^ 2 - 352 * X ^ 3 + 2944 * X ^ 4 - 9600 * X ^ 5 - 11520 * X ^ 6 + 178176 * X ^ 7 - 397312 * X ^ 8 - 536576 * X ^ 9 + 3829760 * X ^ 10 - 4218880 * X ^ 11 - 10256384 * X ^ 12 + 31490048 * X ^ 13 - 11206656 * X ^ 14 - 66846720 * X ^ 15 + 94371840 * X ^ 16 + 16777216 * X ^ 17 - 117440512 * X ^ 18 + 67108864 * X ^ 19 : ℚ⟦X⟧) * G ^ 6) * hd2
  have k2 : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
  have k4 : constantCoeff (4 : ℚ⟦X⟧) = 4 := cnum 4
  have hPG : (-2 + 12 * X - 4 * X ^ 2 - 64 * X ^ 3 + 48 * X ^ 4 + 64 * X ^ 5 : ℚ⟦X⟧) * G + (4 - 32 * X + 32 * X ^ 2 + 256 * X ^ 3 - 448 * X ^ 4 - 512 * X ^ 5 + 1024 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k2, k4] at h'
    norm_num at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (X ^ 2 - 2 * X ^ 3 + X ^ 4 : ℚ⟦X⟧) + (-1 + 6 * X - 2 * X ^ 2 - 32 * X ^ 3 + 24 * X ^ 4 + 32 * X ^ 5 : ℚ⟦X⟧) * G ^ 2 + (1 - 8 * X + 8 * X ^ 2 + 64 * X ^ 3 - 112 * X ^ 4 - 128 * X ^ 5 + 256 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C 1 + derivative ℚ (derivative ℚ G) * X * X * X * C (-6) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 8 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 8 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-48) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C 64 +
      derivative ℚ G * X * X * C (-4) + derivative ℚ G * X * X * X * C (-16) +
      derivative ℚ G * X * X * X * X * C 96 + derivative ℚ G * X * X * X * X * X * C (-128) +
      derivative ℚ G * X * X * X * X * X * X * C 160 + G * X * X * C (-4) +
      G * X * X * X * C 40 + G * X * X * X * X * C (-32) +
      G * X * X * X * X * X * C 32 =
      0 := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (X ^ 2 - 2 * X ^ 3 + X ^ 4 : ℚ⟦X⟧) + (-1 + 6 * X - 2 * X ^ 2 - 32 * X ^ 3 + 24 * X ^ 4 + 32 * X ^ 5 : ℚ⟦X⟧) * G ^ 2 + (1 - 8 * X + 8 * X ^ 2 + 64 * X ^ 3 - 112 * X ^ 4 - 128 * X ^ 5 + 256 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) (m : ℕ) :
    1 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-6) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      8 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 8 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      (-48) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + 64 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      (-4) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-16) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      96 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + (-128) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      160 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + (-4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      40 * coeff (m + 1 + 1 + 1 + 1) G + (-32) * coeff (m + 1 + 1 + 1) G +
      32 * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (X ^ 2 - 2 * X ^ 3 + X ^ 4 : ℚ⟦X⟧) + (-1 + 6 * X - 2 * X ^ 2 - 32 * X ^ 3 + 24 * X ^ 4 + 32 * X ^ 5 : ℚ⟦X⟧) * G ^ 2 + (1 - 8 * X + 8 * X ^ 2 + 64 * X ^ 3 - 112 * X ^ 4 - 128 * X ^ 5 + 256 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    20 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-72) * coeff (0 + 1 + 1 + 1 + 1) G +
      48 * coeff (0 + 1 + 1 + 1) G + 16 * coeff (0 + 1 + 1) G +
      (-16) * coeff (0 + 1 + 1 + 1 + 1) G + (-48) * coeff (0 + 1 + 1 + 1) G +
      192 * coeff (0 + 1 + 1) G + (-128) * coeff (0 + 1) G +
      (-4) * coeff (0 + 1 + 1 + 1) G + 40 * coeff (0 + 1 + 1) G +
      (-32) * coeff (0 + 1) G + 32 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (X ^ 2 - 2 * X ^ 3 + X ^ 4 : ℚ⟦X⟧) + (-1 + 6 * X - 2 * X ^ 2 - 32 * X ^ 3 + 24 * X ^ 4 + 32 * X ^ 5 : ℚ⟦X⟧) * G ^ 2 + (1 - 8 * X + 8 * X ^ 2 + 64 * X ^ 3 - 112 * X ^ 4 - 128 * X ^ 5 + 256 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    30 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-120) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      96 * coeff (0 + 1 + 1 + 1 + 1) G + 48 * coeff (0 + 1 + 1 + 1) G +
      (-96) * coeff (0 + 1 + 1) G + (-20) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-64) * coeff (0 + 1 + 1 + 1 + 1) G + 288 * coeff (0 + 1 + 1 + 1) G +
      (-256) * coeff (0 + 1 + 1) G + 160 * coeff (0 + 1) G +
      (-4) * coeff (0 + 1 + 1 + 1 + 1) G + 40 * coeff (0 + 1 + 1 + 1) G +
      (-32) * coeff (0 + 1 + 1) G + 32 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A032123Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a032123.main := by
  intro T W G hT _ hW _ hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 - 5 = m := rfl
  rw [e1, e2, e3, e4, e5]
  have hn : ((2) * T * W) * ((8) * T ^ 3 * W + (-32) * PowerSeries.X ^ 2 * T ^ 3 * W) = (16 - 128 * PowerSeries.X + 128 * PowerSeries.X ^ 2 + 1024 * PowerSeries.X ^ 3 - 1792 * PowerSeries.X ^ 4 - 2048 * PowerSeries.X ^ 5 + 4096 * PowerSeries.X ^ 6 : PowerSeries ℚ) := by
    linear_combination ((16) + (16) * T ^ 2 + (-64) * PowerSeries.X + (-128) * PowerSeries.X ^ 2 + (-128) * PowerSeries.X ^ 2 * T ^ 2 + (512) * PowerSeries.X ^ 3 + (256) * PowerSeries.X ^ 4 + (256) * PowerSeries.X ^ 4 * T ^ 2 + (-1024) * PowerSeries.X ^ 5) * hT + ((16) * T ^ 4 + (-64) * PowerSeries.X ^ 2 * T ^ 4) * hW
  have hnu0 : (16 - 128 * PowerSeries.X + 128 * PowerSeries.X ^ 2 + 1024 * PowerSeries.X ^ 3 - 1792 * PowerSeries.X ^ 4 - 2048 * PowerSeries.X ^ 5 + 4096 * PowerSeries.X ^ 6 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    have kc : PowerSeries.constantCoeff (16 : PowerSeries ℚ) = 16 := A032123Aux.cnum 16
    simp [kc] at h'
  have hnu : (16 - 128 * PowerSeries.X + 128 * PowerSeries.X ^ 2 + 1024 * PowerSeries.X ^ 3 - 1792 * PowerSeries.X ^ 4 - 2048 * PowerSeries.X ^ 5 + 4096 * PowerSeries.X ^ 6 : PowerSeries ℚ) ≠ 0 := by
    have e : (16 - 128 * PowerSeries.X + 128 * PowerSeries.X ^ 2 + 1024 * PowerSeries.X ^ 3 - 1792 * PowerSeries.X ^ 4 - 2048 * PowerSeries.X ^ 5 + 4096 * PowerSeries.X ^ 6 : PowerSeries ℚ) = PowerSeries.X ^ 0 * (16 - 128 * PowerSeries.X + 128 * PowerSeries.X ^ 2 + 1024 * PowerSeries.X ^ 3 - 1792 * PowerSeries.X ^ 4 - 2048 * PowerSeries.X ^ 5 + 4096 * PowerSeries.X ^ 6 : PowerSeries ℚ) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 0 PowerSeries.X_ne_zero) hnu0
  have hN1 : ((2) * T * W : PowerSeries ℚ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hn
    exact hnu hn.symm
  have hM : ((2) * T * W) ^ 4 * ((PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 : PowerSeries ℚ) + (-1 + 6 * PowerSeries.X - 2 * PowerSeries.X ^ 2 - 32 * PowerSeries.X ^ 3 + 24 * PowerSeries.X ^ 4 + 32 * PowerSeries.X ^ 5 : PowerSeries ℚ) * G ^ 2 + (1 - 8 * PowerSeries.X + 8 * PowerSeries.X ^ 2 + 64 * PowerSeries.X ^ 3 - 112 * PowerSeries.X ^ 4 - 128 * PowerSeries.X ^ 5 + 256 * PowerSeries.X ^ 6 : PowerSeries ℚ) * G ^ 4) = 0 := by
    linear_combination ((-1) + (-4) * T * W + (-3) * T ^ 2 + (4) * PowerSeries.X + (16) * PowerSeries.X * T * W + (16) * PowerSeries.X * T ^ 2 + (16) * PowerSeries.X ^ 2 + (48) * PowerSeries.X ^ 2 * T * W + (32) * PowerSeries.X ^ 2 * T ^ 2 + (-64) * PowerSeries.X ^ 3 + (-192) * PowerSeries.X ^ 3 * T * W + (-192) * PowerSeries.X ^ 3 * T ^ 2 + (-96) * PowerSeries.X ^ 4 + (-192) * PowerSeries.X ^ 4 * T * W + (-96) * PowerSeries.X ^ 4 * T ^ 2 + (384) * PowerSeries.X ^ 5 + (768) * PowerSeries.X ^ 5 * T * W + (768) * PowerSeries.X ^ 5 * T ^ 2 + (256) * PowerSeries.X ^ 6 + (256) * PowerSeries.X ^ 6 * T * W + (-1024) * PowerSeries.X ^ 7 + (-1024) * PowerSeries.X ^ 7 * T * W + (-1024) * PowerSeries.X ^ 7 * T ^ 2 + (-256) * PowerSeries.X ^ 8 + (256) * PowerSeries.X ^ 8 * T ^ 2 + (1024) * PowerSeries.X ^ 9) * hT +
      ((1) + (1) * W ^ 2 + (4) * T * W + (2) * T ^ 2 + (-4) * T ^ 2 * W ^ 2 + (-8) * T ^ 3 * W + (-4) * T ^ 4 + (-8) * PowerSeries.X + (-8) * PowerSeries.X * W ^ 2 + (-32) * PowerSeries.X * T * W + (-24) * PowerSeries.X * T ^ 2 + (24) * PowerSeries.X * T ^ 2 * W ^ 2 + (48) * PowerSeries.X * T ^ 3 * W + (24) * PowerSeries.X * T ^ 4 + (4) * PowerSeries.X ^ 2 + (8) * PowerSeries.X ^ 2 * W ^ 2 + (32) * PowerSeries.X ^ 2 * T * W + (56) * PowerSeries.X ^ 2 * T ^ 2 + (-8) * PowerSeries.X ^ 2 * T ^ 2 * W ^ 2 + (-16) * PowerSeries.X ^ 2 * T ^ 3 * W + (8) * PowerSeries.X ^ 2 * T ^ 4 + (16) * PowerSeries.X ^ 2 * T ^ 4 * W ^ 2 + (96) * PowerSeries.X ^ 3 + (64) * PowerSeries.X ^ 3 * W ^ 2 + (256) * PowerSeries.X ^ 3 * T * W + (160) * PowerSeries.X ^ 3 * T ^ 2 + (-128) * PowerSeries.X ^ 3 * T ^ 2 * W ^ 2 + (-256) * PowerSeries.X ^ 3 * T ^ 3 * W + (-160) * PowerSeries.X ^ 3 * T ^ 4 + (-32) * PowerSeries.X ^ 3 * T ^ 4 * W ^ 2 + (-144) * PowerSeries.X ^ 4 + (-112) * PowerSeries.X ^ 4 * W ^ 2 + (-448) * PowerSeries.X ^ 4 * T * W + (-544) * PowerSeries.X ^ 4 * T ^ 2 + (96) * PowerSeries.X ^ 4 * T ^ 2 * W ^ 2 + (192) * PowerSeries.X ^ 4 * T ^ 3 * W + (48) * PowerSeries.X ^ 4 * T ^ 4 + (16) * PowerSeries.X ^ 4 * T ^ 4 * W ^ 2 + (-384) * PowerSeries.X ^ 5 + (-128) * PowerSeries.X ^ 5 * W ^ 2 + (-512) * PowerSeries.X ^ 5 * T * W + (-128) * PowerSeries.X ^ 5 * T ^ 2 + (128) * PowerSeries.X ^ 5 * T ^ 2 * W ^ 2 + (256) * PowerSeries.X ^ 5 * T ^ 3 * W + (256) * PowerSeries.X ^ 5 * T ^ 4 + (704) * PowerSeries.X ^ 6 + (256) * PowerSeries.X ^ 6 * W ^ 2 + (1024) * PowerSeries.X ^ 6 * T * W + (1152) * PowerSeries.X ^ 6 * T ^ 2 + (-64) * PowerSeries.X ^ 6 * T ^ 4 + (512) * PowerSeries.X ^ 7 + (-512) * PowerSeries.X ^ 7 * T ^ 2 + (-1024) * PowerSeries.X ^ 8) * hW +
      ((1) * W ^ 3 + (3) * T * W ^ 2 + (3) * T ^ 2 * W + (-4) * T ^ 2 * W ^ 3 + (1) * T ^ 3 + (-4) * T ^ 3 * W ^ 2 + (2) * G * T * W ^ 3 + (4) * G * T ^ 2 * W ^ 2 + (2) * G * T ^ 3 * W + (-8) * G * T ^ 3 * W ^ 3 + (4) * G ^ 2 * T ^ 2 * W ^ 3 + (4) * G ^ 2 * T ^ 3 * W ^ 2 + (8) * G ^ 3 * T ^ 3 * W ^ 3 + (-8) * PowerSeries.X * W ^ 3 + (-24) * PowerSeries.X * T * W ^ 2 + (-24) * PowerSeries.X * T ^ 2 * W + (24) * PowerSeries.X * T ^ 2 * W ^ 3 + (-8) * PowerSeries.X * T ^ 3 + (24) * PowerSeries.X * T ^ 3 * W ^ 2 + (-16) * PowerSeries.X * G * T * W ^ 3 + (-32) * PowerSeries.X * G * T ^ 2 * W ^ 2 + (-16) * PowerSeries.X * G * T ^ 3 * W + (48) * PowerSeries.X * G * T ^ 3 * W ^ 3 + (-32) * PowerSeries.X * G ^ 2 * T ^ 2 * W ^ 3 + (-32) * PowerSeries.X * G ^ 2 * T ^ 3 * W ^ 2 + (-64) * PowerSeries.X * G ^ 3 * T ^ 3 * W ^ 3 + (8) * PowerSeries.X ^ 2 * W ^ 3 + (24) * PowerSeries.X ^ 2 * T * W ^ 2 + (24) * PowerSeries.X ^ 2 * T ^ 2 * W + (-8) * PowerSeries.X ^ 2 * T ^ 2 * W ^ 3 + (8) * PowerSeries.X ^ 2 * T ^ 3 + (-8) * PowerSeries.X ^ 2 * T ^ 3 * W ^ 2 + (16) * PowerSeries.X ^ 2 * G * T * W ^ 3 + (32) * PowerSeries.X ^ 2 * G * T ^ 2 * W ^ 2 + (16) * PowerSeries.X ^ 2 * G * T ^ 3 * W + (-16) * PowerSeries.X ^ 2 * G * T ^ 3 * W ^ 3 + (32) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 2 * W ^ 3 + (32) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 3 * W ^ 2 + (64) * PowerSeries.X ^ 2 * G ^ 3 * T ^ 3 * W ^ 3 + (64) * PowerSeries.X ^ 3 * W ^ 3 + (192) * PowerSeries.X ^ 3 * T * W ^ 2 + (192) * PowerSeries.X ^ 3 * T ^ 2 * W + (-128) * PowerSeries.X ^ 3 * T ^ 2 * W ^ 3 + (64) * PowerSeries.X ^ 3 * T ^ 3 + (-128) * PowerSeries.X ^ 3 * T ^ 3 * W ^ 2 + (128) * PowerSeries.X ^ 3 * G * T * W ^ 3 + (256) * PowerSeries.X ^ 3 * G * T ^ 2 * W ^ 2 + (128) * PowerSeries.X ^ 3 * G * T ^ 3 * W + (-256) * PowerSeries.X ^ 3 * G * T ^ 3 * W ^ 3 + (256) * PowerSeries.X ^ 3 * G ^ 2 * T ^ 2 * W ^ 3 + (256) * PowerSeries.X ^ 3 * G ^ 2 * T ^ 3 * W ^ 2 + (512) * PowerSeries.X ^ 3 * G ^ 3 * T ^ 3 * W ^ 3 + (-112) * PowerSeries.X ^ 4 * W ^ 3 + (-336) * PowerSeries.X ^ 4 * T * W ^ 2 + (-336) * PowerSeries.X ^ 4 * T ^ 2 * W + (96) * PowerSeries.X ^ 4 * T ^ 2 * W ^ 3 + (-112) * PowerSeries.X ^ 4 * T ^ 3 + (96) * PowerSeries.X ^ 4 * T ^ 3 * W ^ 2 + (-224) * PowerSeries.X ^ 4 * G * T * W ^ 3 + (-448) * PowerSeries.X ^ 4 * G * T ^ 2 * W ^ 2 + (-224) * PowerSeries.X ^ 4 * G * T ^ 3 * W + (192) * PowerSeries.X ^ 4 * G * T ^ 3 * W ^ 3 + (-448) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 2 * W ^ 3 + (-448) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 3 * W ^ 2 + (-896) * PowerSeries.X ^ 4 * G ^ 3 * T ^ 3 * W ^ 3 + (-128) * PowerSeries.X ^ 5 * W ^ 3 + (-384) * PowerSeries.X ^ 5 * T * W ^ 2 + (-384) * PowerSeries.X ^ 5 * T ^ 2 * W + (128) * PowerSeries.X ^ 5 * T ^ 2 * W ^ 3 + (-128) * PowerSeries.X ^ 5 * T ^ 3 + (128) * PowerSeries.X ^ 5 * T ^ 3 * W ^ 2 + (-256) * PowerSeries.X ^ 5 * G * T * W ^ 3 + (-512) * PowerSeries.X ^ 5 * G * T ^ 2 * W ^ 2 + (-256) * PowerSeries.X ^ 5 * G * T ^ 3 * W + (256) * PowerSeries.X ^ 5 * G * T ^ 3 * W ^ 3 + (-512) * PowerSeries.X ^ 5 * G ^ 2 * T ^ 2 * W ^ 3 + (-512) * PowerSeries.X ^ 5 * G ^ 2 * T ^ 3 * W ^ 2 + (-1024) * PowerSeries.X ^ 5 * G ^ 3 * T ^ 3 * W ^ 3 + (256) * PowerSeries.X ^ 6 * W ^ 3 + (768) * PowerSeries.X ^ 6 * T * W ^ 2 + (768) * PowerSeries.X ^ 6 * T ^ 2 * W + (256) * PowerSeries.X ^ 6 * T ^ 3 + (512) * PowerSeries.X ^ 6 * G * T * W ^ 3 + (1024) * PowerSeries.X ^ 6 * G * T ^ 2 * W ^ 2 + (512) * PowerSeries.X ^ 6 * G * T ^ 3 * W + (1024) * PowerSeries.X ^ 6 * G ^ 2 * T ^ 2 * W ^ 3 + (1024) * PowerSeries.X ^ 6 * G ^ 2 * T ^ 3 * W ^ 2 + (2048) * PowerSeries.X ^ 6 * G ^ 3 * T ^ 3 * W ^ 3) * hG
  have hP : (PowerSeries.X ^ 2 - 2 * PowerSeries.X ^ 3 + PowerSeries.X ^ 4 : PowerSeries ℚ) + (-1 + 6 * PowerSeries.X - 2 * PowerSeries.X ^ 2 - 32 * PowerSeries.X ^ 3 + 24 * PowerSeries.X ^ 4 + 32 * PowerSeries.X ^ 5 : PowerSeries ℚ) * G ^ 2 + (1 - 8 * PowerSeries.X + 8 * PowerSeries.X ^ 2 + 64 * PowerSeries.X ^ 3 - 112 * PowerSeries.X ^ 4 - 128 * PowerSeries.X ^ 5 + 256 * PowerSeries.X ^ 6 : PowerSeries ℚ) * G ^ 4 = 0 := (mul_eq_zero.mp hM).resolve_left (pow_ne_zero 4 hN1)
  have h0c : PowerSeries.constantCoeff G = (1 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A032123Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A032123Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A032123Aux.rel G hP h0c m
      push_cast
      linear_combination r
