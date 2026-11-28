import OMAStatements.S_oeis_a045743

-- Problem: A045743: Number of noncrossing connected graphs on n nodes on a circle having no triangular faces.
-- Upstream: formal-conjectures statements/oeis-a045743.lean:0 (declaration OMA.S_oeis_a045743.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! F satisfies the quartic equation Phi(x, F) = x F^4 + F^3 - 4 F^2 + 4 F - 1 = 0. Differentiating it
and using the resultant of Phi and its derivative in F gives a first order linear system with
polynomial coefficients for F, F^2, F^3. Differentiating that system and eliminating the derivatives
shows that the differential operator read off the recurrence (for the coefficients of F) maps F to
a polynomial; the recurrence is the coefficient of a power of x in the resulting equation. -/

namespace A045743Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem key (G Y2 Y3 : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (4 : ℚ⟦X⟧) * G + (-4 : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (hY2 : Y2 = G * G)
    (hY3 : Y3 = G * G * G) :
    (6769090 * X ^ 4 + 35782496 * X ^ 5 - 741408768 * X ^ 6 + 425485824 * X ^ 7 + 386031616 * X ^ 8) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (29125315 * X ^ 3 + 283783056 * X ^ 4 - 6638757376 * X ^ 5 + 888428032 * X ^ 6 + 3454566400 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (6146865 * X ^ 2 + 446760480 * X ^ 3 - 13631578848 * X ^ 4 - 5256777696 * X ^ 5 + 7221742080 * X ^ 6) * derivative ℚ (derivative ℚ G) + (49602528 * X ^ 2 - 5365534512 * X ^ 3 - 6069672768 * X ^ 4 + 3049528320 * X ^ 5) * derivative ℚ G + (-141110640 * X ^ 2 - 218701272 * X ^ 3 + 52437120 * X ^ 4) * G =
      -54626922 * X ^ 2 + 4061664 * X ^ 3 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d5 : derivative ℚ (5 : ℚ⟦X⟧) = 0 := dnum 5
  have d10 : derivative ℚ (10 : ℚ⟦X⟧) = 0 := dnum 10
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d15 : derivative ℚ (15 : ℚ⟦X⟧) = 0 := dnum 15
  have d20 : derivative ℚ (20 : ℚ⟦X⟧) = 0 := dnum 20
  have d23 : derivative ℚ (23 : ℚ⟦X⟧) = 0 := dnum 23
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have d25 : derivative ℚ (25 : ℚ⟦X⟧) = 0 := dnum 25
  have d28 : derivative ℚ (28 : ℚ⟦X⟧) = 0 := dnum 28
  have d30 : derivative ℚ (30 : ℚ⟦X⟧) = 0 := dnum 30
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d40 : derivative ℚ (40 : ℚ⟦X⟧) = 0 := dnum 40
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d50 : derivative ℚ (50 : ℚ⟦X⟧) = 0 := dnum 50
  have d56 : derivative ℚ (56 : ℚ⟦X⟧) = 0 := dnum 56
  have d60 : derivative ℚ (60 : ℚ⟦X⟧) = 0 := dnum 60
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d75 : derivative ℚ (75 : ℚ⟦X⟧) = 0 := dnum 75
  have d92 : derivative ℚ (92 : ℚ⟦X⟧) = 0 := dnum 92
  have d100 : derivative ℚ (100 : ℚ⟦X⟧) = 0 := dnum 100
  have d112 : derivative ℚ (112 : ℚ⟦X⟧) = 0 := dnum 112
  have d120 : derivative ℚ (120 : ℚ⟦X⟧) = 0 := dnum 120
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d140 : derivative ℚ (140 : ℚ⟦X⟧) = 0 := dnum 140
  have d144 : derivative ℚ (144 : ℚ⟦X⟧) = 0 := dnum 144
  have d150 : derivative ℚ (150 : ℚ⟦X⟧) = 0 := dnum 150
  have d160 : derivative ℚ (160 : ℚ⟦X⟧) = 0 := dnum 160
  have d192 : derivative ℚ (192 : ℚ⟦X⟧) = 0 := dnum 192
  have d200 : derivative ℚ (200 : ℚ⟦X⟧) = 0 := dnum 200
  have d224 : derivative ℚ (224 : ℚ⟦X⟧) = 0 := dnum 224
  have d240 : derivative ℚ (240 : ℚ⟦X⟧) = 0 := dnum 240
  have d256 : derivative ℚ (256 : ℚ⟦X⟧) = 0 := dnum 256
  have d276 : derivative ℚ (276 : ℚ⟦X⟧) = 0 := dnum 276
  have d280 : derivative ℚ (280 : ℚ⟦X⟧) = 0 := dnum 280
  have d288 : derivative ℚ (288 : ℚ⟦X⟧) = 0 := dnum 288
  have d300 : derivative ℚ (300 : ℚ⟦X⟧) = 0 := dnum 300
  have d336 : derivative ℚ (336 : ℚ⟦X⟧) = 0 := dnum 336
  have d352 : derivative ℚ (352 : ℚ⟦X⟧) = 0 := dnum 352
  have d384 : derivative ℚ (384 : ℚ⟦X⟧) = 0 := dnum 384
  have d480 : derivative ℚ (480 : ℚ⟦X⟧) = 0 := dnum 480
  have d512 : derivative ℚ (512 : ℚ⟦X⟧) = 0 := dnum 512
  have d552 : derivative ℚ (552 : ℚ⟦X⟧) = 0 := dnum 552
  have d560 : derivative ℚ (560 : ℚ⟦X⟧) = 0 := dnum 560
  have d576 : derivative ℚ (576 : ℚ⟦X⟧) = 0 := dnum 576
  have d640 : derivative ℚ (640 : ℚ⟦X⟧) = 0 := dnum 640
  have d660 : derivative ℚ (660 : ℚ⟦X⟧) = 0 := dnum 660
  have d720 : derivative ℚ (720 : ℚ⟦X⟧) = 0 := dnum 720
  have d768 : derivative ℚ (768 : ℚ⟦X⟧) = 0 := dnum 768
  have d876 : derivative ℚ (876 : ℚ⟦X⟧) = 0 := dnum 876
  have d896 : derivative ℚ (896 : ℚ⟦X⟧) = 0 := dnum 896
  have d960 : derivative ℚ (960 : ℚ⟦X⟧) = 0 := dnum 960
  have d1000 : derivative ℚ (1000 : ℚ⟦X⟧) = 0 := dnum 1000
  have d1120 : derivative ℚ (1120 : ℚ⟦X⟧) = 0 := dnum 1120
  have d1152 : derivative ℚ (1152 : ℚ⟦X⟧) = 0 := dnum 1152
  have d1200 : derivative ℚ (1200 : ℚ⟦X⟧) = 0 := dnum 1200
  have d1344 : derivative ℚ (1344 : ℚ⟦X⟧) = 0 := dnum 1344
  have d1440 : derivative ℚ (1440 : ℚ⟦X⟧) = 0 := dnum 1440
  have d1536 : derivative ℚ (1536 : ℚ⟦X⟧) = 0 := dnum 1536
  have d1680 : derivative ℚ (1680 : ℚ⟦X⟧) = 0 := dnum 1680
  have d1728 : derivative ℚ (1728 : ℚ⟦X⟧) = 0 := dnum 1728
  have d1760 : derivative ℚ (1760 : ℚ⟦X⟧) = 0 := dnum 1760
  have d1792 : derivative ℚ (1792 : ℚ⟦X⟧) = 0 := dnum 1792
  have d1920 : derivative ℚ (1920 : ℚ⟦X⟧) = 0 := dnum 1920
  have d2048 : derivative ℚ (2048 : ℚ⟦X⟧) = 0 := dnum 2048
  have d2240 : derivative ℚ (2240 : ℚ⟦X⟧) = 0 := dnum 2240
  have d2304 : derivative ℚ (2304 : ℚ⟦X⟧) = 0 := dnum 2304
  have d2352 : derivative ℚ (2352 : ℚ⟦X⟧) = 0 := dnum 2352
  have d2880 : derivative ℚ (2880 : ℚ⟦X⟧) = 0 := dnum 2880
  have d3072 : derivative ℚ (3072 : ℚ⟦X⟧) = 0 := dnum 3072
  have d3360 : derivative ℚ (3360 : ℚ⟦X⟧) = 0 := dnum 3360
  have d3584 : derivative ℚ (3584 : ℚ⟦X⟧) = 0 := dnum 3584
  have d3840 : derivative ℚ (3840 : ℚ⟦X⟧) = 0 := dnum 3840
  have d3960 : derivative ℚ (3960 : ℚ⟦X⟧) = 0 := dnum 3960
  have d4000 : derivative ℚ (4000 : ℚ⟦X⟧) = 0 := dnum 4000
  have d4032 : derivative ℚ (4032 : ℚ⟦X⟧) = 0 := dnum 4032
  have d4096 : derivative ℚ (4096 : ℚ⟦X⟧) = 0 := dnum 4096
  have d4800 : derivative ℚ (4800 : ℚ⟦X⟧) = 0 := dnum 4800
  have d5256 : derivative ℚ (5256 : ℚ⟦X⟧) = 0 := dnum 5256
  have d5376 : derivative ℚ (5376 : ℚ⟦X⟧) = 0 := dnum 5376
  have d5760 : derivative ℚ (5760 : ℚ⟦X⟧) = 0 := dnum 5760
  have d6720 : derivative ℚ (6720 : ℚ⟦X⟧) = 0 := dnum 6720
  have d7040 : derivative ℚ (7040 : ℚ⟦X⟧) = 0 := dnum 7040
  have d7200 : derivative ℚ (7200 : ℚ⟦X⟧) = 0 := dnum 7200
  have d7680 : derivative ℚ (7680 : ℚ⟦X⟧) = 0 := dnum 7680
  have d8064 : derivative ℚ (8064 : ℚ⟦X⟧) = 0 := dnum 8064
  have d8640 : derivative ℚ (8640 : ℚ⟦X⟧) = 0 := dnum 8640
  have d10752 : derivative ℚ (10752 : ℚ⟦X⟧) = 0 := dnum 10752
  have d14112 : derivative ℚ (14112 : ℚ⟦X⟧) = 0 := dnum 14112
  have d14336 : derivative ℚ (14336 : ℚ⟦X⟧) = 0 := dnum 14336
  have d15360 : derivative ℚ (15360 : ℚ⟦X⟧) = 0 := dnum 15360
  have d18432 : derivative ℚ (18432 : ℚ⟦X⟧) = 0 := dnum 18432
  have d19800 : derivative ℚ (19800 : ℚ⟦X⟧) = 0 := dnum 19800
  have d20160 : derivative ℚ (20160 : ℚ⟦X⟧) = 0 := dnum 20160
  have d21120 : derivative ℚ (21120 : ℚ⟦X⟧) = 0 := dnum 21120
  have d21504 : derivative ℚ (21504 : ℚ⟦X⟧) = 0 := dnum 21504
  have d24192 : derivative ℚ (24192 : ℚ⟦X⟧) = 0 := dnum 24192
  have d26280 : derivative ℚ (26280 : ℚ⟦X⟧) = 0 := dnum 26280
  have d28672 : derivative ℚ (28672 : ℚ⟦X⟧) = 0 := dnum 28672
  have d53760 : derivative ℚ (53760 : ℚ⟦X⟧) = 0 := dnum 53760
  have d61440 : derivative ℚ (61440 : ℚ⟦X⟧) = 0 := dnum 61440
  have dp4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have hp0 : (-1 : ℚ⟦X⟧) + (4 : ℚ⟦X⟧) * G + (-4 : ℚ⟦X⟧) * G * G + (1 : ℚ⟦X⟧) * G * G * G + (1 * X : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-1 : ℚ⟦X⟧) + (4 : ℚ⟦X⟧) * G + (-4 : ℚ⟦X⟧) * G * G + (1 : ℚ⟦X⟧) * G * G * G + (1 * X : ℚ⟦X⟧) * G * G * G * G) =
      (4 : ℚ⟦X⟧) * (derivative ℚ G) + (-8 : ℚ⟦X⟧) * G * (derivative ℚ G) + (3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G ^ 4 := by
    simp [Derivation.leibniz, dp4]
    ring
  have hd1 : (4 : ℚ⟦X⟧) * (derivative ℚ G) + (-8 : ℚ⟦X⟧) * G * (derivative ℚ G) + (3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G ^ 4 = 0 := by rw [← hL1, hp0, map_zero]
  have s1 : (5 * X ^ 4 + 32 * X ^ 5 - 512 * X ^ 6 - 256 * X ^ 7 : ℚ⟦X⟧) * derivative ℚ G =
      (-12 * X ^ 4 - 112 * X ^ 5 : ℚ⟦X⟧) + (40 * X ^ 4 + 352 * X ^ 5 + 64 * X ^ 6 : ℚ⟦X⟧) * G + (-23 * X ^ 4 - 144 * X ^ 5 - 64 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (-28 * X ^ 5 - 64 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 := by
    linear_combination ((12 * X ^ 4 + 92 * X ^ 5 - 976 * X ^ 6 : ℚ⟦X⟧) + (-25 * X ^ 4 - 216 * X ^ 5 + 1696 * X ^ 6 - 64 * X ^ 7 : ℚ⟦X⟧) * G + (8 * X ^ 4 + 83 * X ^ 5 - 368 * X ^ 6 - 192 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 + (8 * X ^ 5 + 76 * X ^ 6 - 448 * X ^ 7 : ℚ⟦X⟧) * G ^ 3) * hd1 +
      ((-12 * X ^ 4 - 112 * X ^ 5 : ℚ⟦X⟧) + (43 * X ^ 4 + 336 * X ^ 5 - 3392 * X ^ 6 + 256 * X ^ 7 : ℚ⟦X⟧) * (derivative ℚ G) + (-8 * X ^ 4 - 96 * X ^ 5 + 64 * X ^ 6 : ℚ⟦X⟧) * G + (-24 * X ^ 4 - 256 * X ^ 5 + 1024 * X ^ 6 + 768 * X ^ 7 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-7 * X ^ 4 - 80 * X ^ 5 + 192 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (-32 * X ^ 5 - 304 * X ^ 6 + 1792 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-8 * X ^ 4 - 76 * X ^ 5 + 448 * X ^ 6 : ℚ⟦X⟧) * G ^ 3) * hP
  have hdY2 : derivative ℚ Y2 = 2 * (G) * derivative ℚ G := by
    rw [hY2]
    simp [Derivation.leibniz]
    ring
  have hdY3 : derivative ℚ Y3 = 3 * (G * G) * derivative ℚ G := by
    rw [hY3]
    simp [Derivation.leibniz]
    ring
  -- G itself is the first basis element
  have r0_1 : (5 * (X * X * X * X) + 32 * (X * X * X * X * X) - 512 * (X * X * X * X * X * X) - 256 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G =
      (-12 * (X * X * X * X) - 112 * (X * X * X * X * X) : ℚ⟦X⟧) + (40 * (X * X * X * X) + 352 * (X * X * X * X * X) + 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G + (-23 * (X * X * X * X) - 144 * (X * X * X * X * X) - 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * Y2 + (-28 * (X * X * X * X * X) - 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * Y3 := by
    linear_combination s1 - (-23 * X ^ 4 - 144 * X ^ 5 - 64 * X ^ 6) * hY2 - (-28 * X ^ 5 - 64 * X ^ 6) * hY3
  have hLr0_2 : derivative ℚ ((5 * (X * X * X * X) + 32 * (X * X * X * X * X) - 512 * (X * X * X * X * X * X) - 256 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G) =
      (20 * X ^ 3 + 160 * X ^ 4 - 3072 * X ^ 5 - 1792 * X ^ 6) * derivative ℚ G + (5 * X ^ 4 + 32 * X ^ 5 - 512 * X ^ 6 - 256 * X ^ 7) * derivative ℚ (derivative ℚ G) := by
    simp [Derivation.leibniz, d5, d32, d256, d512]
    ring
  have hRr0_2 : derivative ℚ ((-12 * (X * X * X * X) - 112 * (X * X * X * X * X) : ℚ⟦X⟧) + (40 * (X * X * X * X) + 352 * (X * X * X * X * X) + 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G + (-23 * (X * X * X * X) - 144 * (X * X * X * X * X) - 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * Y2 + (-28 * (X * X * X * X * X) - 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * Y3) =
      (-48 * X ^ 3 - 560 * X ^ 4) + (160 * X ^ 3 + 1760 * X ^ 4 + 384 * X ^ 5) * G + (40 * X ^ 4 + 352 * X ^ 5 + 64 * X ^ 6) * derivative ℚ G + (-92 * X ^ 3 - 720 * X ^ 4 - 384 * X ^ 5) * Y2 + (-23 * X ^ 4 - 144 * X ^ 5 - 64 * X ^ 6) * derivative ℚ Y2 + (-140 * X ^ 4 - 384 * X ^ 5) * Y3 + (-28 * X ^ 5 - 64 * X ^ 6) * derivative ℚ Y3 := by
    simp [Derivation.leibniz, d12, d23, d28, d40, d64, d112, d144, d352]
    ring
  have r0_2 : (20 * X ^ 3 + 160 * X ^ 4 - 3072 * X ^ 5 - 1792 * X ^ 6) * derivative ℚ G + (5 * X ^ 4 + 32 * X ^ 5 - 512 * X ^ 6 - 256 * X ^ 7) * derivative ℚ (derivative ℚ G) =
      (-48 * X ^ 3 - 560 * X ^ 4) + (160 * X ^ 3 + 1760 * X ^ 4 + 384 * X ^ 5) * G + (40 * X ^ 4 + 352 * X ^ 5 + 64 * X ^ 6) * derivative ℚ G + (-92 * X ^ 3 - 720 * X ^ 4 - 384 * X ^ 5) * Y2 + (-23 * X ^ 4 - 144 * X ^ 5 - 64 * X ^ 6) * derivative ℚ Y2 + (-140 * X ^ 4 - 384 * X ^ 5) * Y3 + (-28 * X ^ 5 - 64 * X ^ 6) * derivative ℚ Y3 := by
    rw [← hLr0_2, ← hRr0_2, r0_1]
  have r0_2p : (20 * (X * X * X) + 160 * (X * X * X * X) - 3072 * (X * X * X * X * X) - 1792 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (5 * (X * X * X * X) + 32 * (X * X * X * X * X) - 512 * (X * X * X * X * X * X) - 256 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) =
      (-48 * (X * X * X) - 560 * (X * X * X * X) : ℚ⟦X⟧) + (160 * (X * X * X) + 1760 * (X * X * X * X) + 384 * (X * X * X * X * X) : ℚ⟦X⟧) * G + (40 * (X * X * X * X) + 352 * (X * X * X * X * X) + 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-92 * (X * X * X) - 720 * (X * X * X * X) - 384 * (X * X * X * X * X) : ℚ⟦X⟧) * Y2 + (-23 * (X * X * X * X) - 144 * (X * X * X * X * X) - 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2 + (-140 * (X * X * X * X) - 384 * (X * X * X * X * X) : ℚ⟦X⟧) * Y3 + (-28 * (X * X * X * X * X) - 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y3 := by linear_combination r0_2
  have hLr0_3 : derivative ℚ ((20 * (X * X * X) + 160 * (X * X * X * X) - 3072 * (X * X * X * X * X) - 1792 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (5 * (X * X * X * X) + 32 * (X * X * X * X * X) - 512 * (X * X * X * X * X * X) - 256 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) =
      (60 * X ^ 2 + 640 * X ^ 3 - 15360 * X ^ 4 - 10752 * X ^ 5) * derivative ℚ G + 2 * (20 * X ^ 3 + 160 * X ^ 4 - 3072 * X ^ 5 - 1792 * X ^ 6) * derivative ℚ (derivative ℚ G) + (5 * X ^ 4 + 32 * X ^ 5 - 512 * X ^ 6 - 256 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d5, d20, d32, d160, d256, d512, d1792, d3072]
    ring
  have hRr0_3 : derivative ℚ ((-48 * (X * X * X) - 560 * (X * X * X * X) : ℚ⟦X⟧) + (160 * (X * X * X) + 1760 * (X * X * X * X) + 384 * (X * X * X * X * X) : ℚ⟦X⟧) * G + (40 * (X * X * X * X) + 352 * (X * X * X * X * X) + 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-92 * (X * X * X) - 720 * (X * X * X * X) - 384 * (X * X * X * X * X) : ℚ⟦X⟧) * Y2 + (-23 * (X * X * X * X) - 144 * (X * X * X * X * X) - 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2 + (-140 * (X * X * X * X) - 384 * (X * X * X * X * X) : ℚ⟦X⟧) * Y3 + (-28 * (X * X * X * X * X) - 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y3) =
      (-144 * X ^ 2 - 2240 * X ^ 3) + (480 * X ^ 2 + 7040 * X ^ 3 + 1920 * X ^ 4) * G + 2 * (160 * X ^ 3 + 1760 * X ^ 4 + 384 * X ^ 5) * derivative ℚ G + (40 * X ^ 4 + 352 * X ^ 5 + 64 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-276 * X ^ 2 - 2880 * X ^ 3 - 1920 * X ^ 4) * Y2 + 2 * (-92 * X ^ 3 - 720 * X ^ 4 - 384 * X ^ 5) * derivative ℚ Y2 + (-23 * X ^ 4 - 144 * X ^ 5 - 64 * X ^ 6) * derivative ℚ (derivative ℚ Y2) + (-560 * X ^ 3 - 1920 * X ^ 4) * Y3 + 2 * (-140 * X ^ 4 - 384 * X ^ 5) * derivative ℚ Y3 + (-28 * X ^ 5 - 64 * X ^ 6) * derivative ℚ (derivative ℚ Y3) := by
    simp [Derivation.leibniz, d23, d28, d40, d48, d64, d92, d140, d144, d160, d352, d384, d560, d720, d1760]
    ring
  have r0_3 : (60 * X ^ 2 + 640 * X ^ 3 - 15360 * X ^ 4 - 10752 * X ^ 5) * derivative ℚ G + 2 * (20 * X ^ 3 + 160 * X ^ 4 - 3072 * X ^ 5 - 1792 * X ^ 6) * derivative ℚ (derivative ℚ G) + (5 * X ^ 4 + 32 * X ^ 5 - 512 * X ^ 6 - 256 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) =
      (-144 * X ^ 2 - 2240 * X ^ 3) + (480 * X ^ 2 + 7040 * X ^ 3 + 1920 * X ^ 4) * G + 2 * (160 * X ^ 3 + 1760 * X ^ 4 + 384 * X ^ 5) * derivative ℚ G + (40 * X ^ 4 + 352 * X ^ 5 + 64 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-276 * X ^ 2 - 2880 * X ^ 3 - 1920 * X ^ 4) * Y2 + 2 * (-92 * X ^ 3 - 720 * X ^ 4 - 384 * X ^ 5) * derivative ℚ Y2 + (-23 * X ^ 4 - 144 * X ^ 5 - 64 * X ^ 6) * derivative ℚ (derivative ℚ Y2) + (-560 * X ^ 3 - 1920 * X ^ 4) * Y3 + 2 * (-140 * X ^ 4 - 384 * X ^ 5) * derivative ℚ Y3 + (-28 * X ^ 5 - 64 * X ^ 6) * derivative ℚ (derivative ℚ Y3) := by
    rw [← hLr0_3, ← hRr0_3, r0_2p]
  have r0_3p : (60 * (X * X) + 640 * (X * X * X) - 15360 * (X * X * X * X) - 10752 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + 2 * ((20 * (X * X * X) + 160 * (X * X * X * X) - 3072 * (X * X * X * X * X) - 1792 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + (5 * (X * X * X * X) + 32 * (X * X * X * X * X) - 512 * (X * X * X * X * X * X) - 256 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G)) =
      (-144 * (X * X) - 2240 * (X * X * X) : ℚ⟦X⟧) + (480 * (X * X) + 7040 * (X * X * X) + 1920 * (X * X * X * X) : ℚ⟦X⟧) * G + 2 * ((160 * (X * X * X) + 1760 * (X * X * X * X) + 384 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G) + (40 * (X * X * X * X) + 352 * (X * X * X * X * X) + 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-276 * (X * X) - 2880 * (X * X * X) - 1920 * (X * X * X * X) : ℚ⟦X⟧) * Y2 + 2 * ((-92 * (X * X * X) - 720 * (X * X * X * X) - 384 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2) + (-23 * (X * X * X * X) - 144 * (X * X * X * X * X) - 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ Y2) + (-560 * (X * X * X) - 1920 * (X * X * X * X) : ℚ⟦X⟧) * Y3 + 2 * ((-140 * (X * X * X * X) - 384 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y3) + (-28 * (X * X * X * X * X) - 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ Y3) := by linear_combination r0_3
  have hLr0_4 : derivative ℚ ((60 * (X * X) + 640 * (X * X * X) - 15360 * (X * X * X * X) - 10752 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + 2 * ((20 * (X * X * X) + 160 * (X * X * X * X) - 3072 * (X * X * X * X * X) - 1792 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + (5 * (X * X * X * X) + 32 * (X * X * X * X * X) - 512 * (X * X * X * X * X * X) - 256 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G))) =
      (120 * X + 1920 * X ^ 2 - 61440 * X ^ 3 - 53760 * X ^ 4) * derivative ℚ G + 3 * (60 * X ^ 2 + 640 * X ^ 3 - 15360 * X ^ 4 - 10752 * X ^ 5) * derivative ℚ (derivative ℚ G) + 3 * (20 * X ^ 3 + 160 * X ^ 4 - 3072 * X ^ 5 - 1792 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (5 * X ^ 4 + 32 * X ^ 5 - 512 * X ^ 6 - 256 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) := by
    simp [Derivation.leibniz, d2, d5, d20, d32, d60, d160, d256, d512, d640, d1792, d3072, d10752, d15360]
    ring
  have hRr0_4 : derivative ℚ ((-144 * (X * X) - 2240 * (X * X * X) : ℚ⟦X⟧) + (480 * (X * X) + 7040 * (X * X * X) + 1920 * (X * X * X * X) : ℚ⟦X⟧) * G + 2 * ((160 * (X * X * X) + 1760 * (X * X * X * X) + 384 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G) + (40 * (X * X * X * X) + 352 * (X * X * X * X * X) + 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-276 * (X * X) - 2880 * (X * X * X) - 1920 * (X * X * X * X) : ℚ⟦X⟧) * Y2 + 2 * ((-92 * (X * X * X) - 720 * (X * X * X * X) - 384 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2) + (-23 * (X * X * X * X) - 144 * (X * X * X * X * X) - 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ Y2) + (-560 * (X * X * X) - 1920 * (X * X * X * X) : ℚ⟦X⟧) * Y3 + 2 * ((-140 * (X * X * X * X) - 384 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y3) + (-28 * (X * X * X * X * X) - 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ Y3)) =
      (-288 * X - 6720 * X ^ 2) + (960 * X + 21120 * X ^ 2 + 7680 * X ^ 3) * G + 3 * (480 * X ^ 2 + 7040 * X ^ 3 + 1920 * X ^ 4) * derivative ℚ G + 3 * (160 * X ^ 3 + 1760 * X ^ 4 + 384 * X ^ 5) * derivative ℚ (derivative ℚ G) + (40 * X ^ 4 + 352 * X ^ 5 + 64 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-552 * X - 8640 * X ^ 2 - 7680 * X ^ 3) * Y2 + 3 * (-276 * X ^ 2 - 2880 * X ^ 3 - 1920 * X ^ 4) * derivative ℚ Y2 + 3 * (-92 * X ^ 3 - 720 * X ^ 4 - 384 * X ^ 5) * derivative ℚ (derivative ℚ Y2) + (-23 * X ^ 4 - 144 * X ^ 5 - 64 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ Y2)) + (-1680 * X ^ 2 - 7680 * X ^ 3) * Y3 + 3 * (-560 * X ^ 3 - 1920 * X ^ 4) * derivative ℚ Y3 + 3 * (-140 * X ^ 4 - 384 * X ^ 5) * derivative ℚ (derivative ℚ Y3) + (-28 * X ^ 5 - 64 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ Y3)) := by
    simp [Derivation.leibniz, d2, d23, d28, d40, d64, d92, d140, d144, d160, d276, d352, d384, d480, d560, d720, d1760, d1920, d2240, d2880, d7040]
    ring
  have r0_4 : (120 * X + 1920 * X ^ 2 - 61440 * X ^ 3 - 53760 * X ^ 4) * derivative ℚ G + 3 * (60 * X ^ 2 + 640 * X ^ 3 - 15360 * X ^ 4 - 10752 * X ^ 5) * derivative ℚ (derivative ℚ G) + 3 * (20 * X ^ 3 + 160 * X ^ 4 - 3072 * X ^ 5 - 1792 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (5 * X ^ 4 + 32 * X ^ 5 - 512 * X ^ 6 - 256 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) =
      (-288 * X - 6720 * X ^ 2) + (960 * X + 21120 * X ^ 2 + 7680 * X ^ 3) * G + 3 * (480 * X ^ 2 + 7040 * X ^ 3 + 1920 * X ^ 4) * derivative ℚ G + 3 * (160 * X ^ 3 + 1760 * X ^ 4 + 384 * X ^ 5) * derivative ℚ (derivative ℚ G) + (40 * X ^ 4 + 352 * X ^ 5 + 64 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-552 * X - 8640 * X ^ 2 - 7680 * X ^ 3) * Y2 + 3 * (-276 * X ^ 2 - 2880 * X ^ 3 - 1920 * X ^ 4) * derivative ℚ Y2 + 3 * (-92 * X ^ 3 - 720 * X ^ 4 - 384 * X ^ 5) * derivative ℚ (derivative ℚ Y2) + (-23 * X ^ 4 - 144 * X ^ 5 - 64 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ Y2)) + (-1680 * X ^ 2 - 7680 * X ^ 3) * Y3 + 3 * (-560 * X ^ 3 - 1920 * X ^ 4) * derivative ℚ Y3 + 3 * (-140 * X ^ 4 - 384 * X ^ 5) * derivative ℚ (derivative ℚ Y3) + (-28 * X ^ 5 - 64 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ Y3)) := by
    rw [← hLr0_4, ← hRr0_4, r0_3p]
  have r1_1 : (5 * (X * X * X * X * X) + 32 * (X * X * X * X * X * X) - 512 * (X * X * X * X * X * X * X) - 256 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2 =
      (-56 * (X * X * X * X * X) - 128 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (200 * (X * X * X * X * X) + 288 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G + (-144 * (X * X * X * X * X) + 192 * (X * X * X * X * X * X) + 128 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * Y2 + (10 * (X * X * X * X * X) - 160 * (X * X * X * X * X * X) - 128 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * Y3 := by
    linear_combination (5 * X ^ 5 + 32 * X ^ 6 - 512 * X ^ 7 - 256 * X ^ 8) * hdY2 + ((2 * X : ℚ⟦X⟧) * G) * s1 +
      ((-56 * X ^ 5 - 128 * X ^ 6 : ℚ⟦X⟧)) * hP - (-144 * X ^ 5 + 192 * X ^ 6 + 128 * X ^ 7) * hY2 - (10 * X ^ 5 - 160 * X ^ 6 - 128 * X ^ 7) * hY3
  have hLr1_2 : derivative ℚ ((5 * (X * X * X * X * X) + 32 * (X * X * X * X * X * X) - 512 * (X * X * X * X * X * X * X) - 256 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2) =
      (25 * X ^ 4 + 192 * X ^ 5 - 3584 * X ^ 6 - 2048 * X ^ 7) * derivative ℚ Y2 + (5 * X ^ 5 + 32 * X ^ 6 - 512 * X ^ 7 - 256 * X ^ 8) * derivative ℚ (derivative ℚ Y2) := by
    simp [Derivation.leibniz, d5, d32, d256, d512]
    ring
  have hRr1_2 : derivative ℚ ((-56 * (X * X * X * X * X) - 128 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (200 * (X * X * X * X * X) + 288 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G + (-144 * (X * X * X * X * X) + 192 * (X * X * X * X * X * X) + 128 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * Y2 + (10 * (X * X * X * X * X) - 160 * (X * X * X * X * X * X) - 128 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * Y3) =
      (-280 * X ^ 4 - 768 * X ^ 5) + (1000 * X ^ 4 + 1728 * X ^ 5) * G + (200 * X ^ 5 + 288 * X ^ 6) * derivative ℚ G + (-720 * X ^ 4 + 1152 * X ^ 5 + 896 * X ^ 6) * Y2 + (-144 * X ^ 5 + 192 * X ^ 6 + 128 * X ^ 7) * derivative ℚ Y2 + (50 * X ^ 4 - 960 * X ^ 5 - 896 * X ^ 6) * Y3 + (10 * X ^ 5 - 160 * X ^ 6 - 128 * X ^ 7) * derivative ℚ Y3 := by
    simp [Derivation.leibniz, d10, d56, d128, d144, d160, d192, d200, d288]
    ring
  have r1_2 : (25 * X ^ 4 + 192 * X ^ 5 - 3584 * X ^ 6 - 2048 * X ^ 7) * derivative ℚ Y2 + (5 * X ^ 5 + 32 * X ^ 6 - 512 * X ^ 7 - 256 * X ^ 8) * derivative ℚ (derivative ℚ Y2) =
      (-280 * X ^ 4 - 768 * X ^ 5) + (1000 * X ^ 4 + 1728 * X ^ 5) * G + (200 * X ^ 5 + 288 * X ^ 6) * derivative ℚ G + (-720 * X ^ 4 + 1152 * X ^ 5 + 896 * X ^ 6) * Y2 + (-144 * X ^ 5 + 192 * X ^ 6 + 128 * X ^ 7) * derivative ℚ Y2 + (50 * X ^ 4 - 960 * X ^ 5 - 896 * X ^ 6) * Y3 + (10 * X ^ 5 - 160 * X ^ 6 - 128 * X ^ 7) * derivative ℚ Y3 := by
    rw [← hLr1_2, ← hRr1_2, r1_1]
  have r1_2p : (25 * (X * X * X * X) + 192 * (X * X * X * X * X) - 3584 * (X * X * X * X * X * X) - 2048 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2 + (5 * (X * X * X * X * X) + 32 * (X * X * X * X * X * X) - 512 * (X * X * X * X * X * X * X) - 256 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ Y2) =
      (-280 * (X * X * X * X) - 768 * (X * X * X * X * X) : ℚ⟦X⟧) + (1000 * (X * X * X * X) + 1728 * (X * X * X * X * X) : ℚ⟦X⟧) * G + (200 * (X * X * X * X * X) + 288 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-720 * (X * X * X * X) + 1152 * (X * X * X * X * X) + 896 * (X * X * X * X * X * X) : ℚ⟦X⟧) * Y2 + (-144 * (X * X * X * X * X) + 192 * (X * X * X * X * X * X) + 128 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2 + (50 * (X * X * X * X) - 960 * (X * X * X * X * X) - 896 * (X * X * X * X * X * X) : ℚ⟦X⟧) * Y3 + (10 * (X * X * X * X * X) - 160 * (X * X * X * X * X * X) - 128 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y3 := by linear_combination r1_2
  have hLr1_3 : derivative ℚ ((25 * (X * X * X * X) + 192 * (X * X * X * X * X) - 3584 * (X * X * X * X * X * X) - 2048 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2 + (5 * (X * X * X * X * X) + 32 * (X * X * X * X * X * X) - 512 * (X * X * X * X * X * X * X) - 256 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ Y2)) =
      (100 * X ^ 3 + 960 * X ^ 4 - 21504 * X ^ 5 - 14336 * X ^ 6) * derivative ℚ Y2 + 2 * (25 * X ^ 4 + 192 * X ^ 5 - 3584 * X ^ 6 - 2048 * X ^ 7) * derivative ℚ (derivative ℚ Y2) + (5 * X ^ 5 + 32 * X ^ 6 - 512 * X ^ 7 - 256 * X ^ 8) * derivative ℚ (derivative ℚ (derivative ℚ Y2)) := by
    simp [Derivation.leibniz, d5, d25, d32, d192, d256, d512, d2048, d3584]
    ring
  have hRr1_3 : derivative ℚ ((-280 * (X * X * X * X) - 768 * (X * X * X * X * X) : ℚ⟦X⟧) + (1000 * (X * X * X * X) + 1728 * (X * X * X * X * X) : ℚ⟦X⟧) * G + (200 * (X * X * X * X * X) + 288 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-720 * (X * X * X * X) + 1152 * (X * X * X * X * X) + 896 * (X * X * X * X * X * X) : ℚ⟦X⟧) * Y2 + (-144 * (X * X * X * X * X) + 192 * (X * X * X * X * X * X) + 128 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2 + (50 * (X * X * X * X) - 960 * (X * X * X * X * X) - 896 * (X * X * X * X * X * X) : ℚ⟦X⟧) * Y3 + (10 * (X * X * X * X * X) - 160 * (X * X * X * X * X * X) - 128 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y3) =
      (-1120 * X ^ 3 - 3840 * X ^ 4) + (4000 * X ^ 3 + 8640 * X ^ 4) * G + 2 * (1000 * X ^ 4 + 1728 * X ^ 5) * derivative ℚ G + (200 * X ^ 5 + 288 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-2880 * X ^ 3 + 5760 * X ^ 4 + 5376 * X ^ 5) * Y2 + 2 * (-720 * X ^ 4 + 1152 * X ^ 5 + 896 * X ^ 6) * derivative ℚ Y2 + (-144 * X ^ 5 + 192 * X ^ 6 + 128 * X ^ 7) * derivative ℚ (derivative ℚ Y2) + (200 * X ^ 3 - 4800 * X ^ 4 - 5376 * X ^ 5) * Y3 + 2 * (50 * X ^ 4 - 960 * X ^ 5 - 896 * X ^ 6) * derivative ℚ Y3 + (10 * X ^ 5 - 160 * X ^ 6 - 128 * X ^ 7) * derivative ℚ (derivative ℚ Y3) := by
    simp [Derivation.leibniz, d10, d50, d128, d144, d160, d192, d200, d280, d288, d720, d768, d896, d960, d1000, d1152, d1728]
    ring
  have r1_3 : (100 * X ^ 3 + 960 * X ^ 4 - 21504 * X ^ 5 - 14336 * X ^ 6) * derivative ℚ Y2 + 2 * (25 * X ^ 4 + 192 * X ^ 5 - 3584 * X ^ 6 - 2048 * X ^ 7) * derivative ℚ (derivative ℚ Y2) + (5 * X ^ 5 + 32 * X ^ 6 - 512 * X ^ 7 - 256 * X ^ 8) * derivative ℚ (derivative ℚ (derivative ℚ Y2)) =
      (-1120 * X ^ 3 - 3840 * X ^ 4) + (4000 * X ^ 3 + 8640 * X ^ 4) * G + 2 * (1000 * X ^ 4 + 1728 * X ^ 5) * derivative ℚ G + (200 * X ^ 5 + 288 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-2880 * X ^ 3 + 5760 * X ^ 4 + 5376 * X ^ 5) * Y2 + 2 * (-720 * X ^ 4 + 1152 * X ^ 5 + 896 * X ^ 6) * derivative ℚ Y2 + (-144 * X ^ 5 + 192 * X ^ 6 + 128 * X ^ 7) * derivative ℚ (derivative ℚ Y2) + (200 * X ^ 3 - 4800 * X ^ 4 - 5376 * X ^ 5) * Y3 + 2 * (50 * X ^ 4 - 960 * X ^ 5 - 896 * X ^ 6) * derivative ℚ Y3 + (10 * X ^ 5 - 160 * X ^ 6 - 128 * X ^ 7) * derivative ℚ (derivative ℚ Y3) := by
    rw [← hLr1_3, ← hRr1_3, r1_2p]
  have r2_1 : (5 * (X * X * X * X * X * X) + 32 * (X * X * X * X * X * X * X) - 512 * (X * X * X * X * X * X * X * X) - 256 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y3 =
      (15 * (X * X * X * X * X) - 240 * (X * X * X * X * X * X) - 192 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-60 * (X * X * X * X * X) + 876 * (X * X * X * X * X * X) + 576 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (60 * (X * X * X * X * X) - 660 * (X * X * X * X * X * X) - 336 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * Y2 + (-15 * (X * X * X * X * X) + 24 * (X * X * X * X * X * X) + 480 * (X * X * X * X * X * X * X) + 192 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * Y3 := by
    linear_combination (5 * X ^ 6 + 32 * X ^ 7 - 512 * X ^ 8 - 256 * X ^ 9) * hdY3 + ((3 * X ^ 2 : ℚ⟦X⟧) * G ^ 2) * s1 +
      ((15 * X ^ 5 - 240 * X ^ 6 - 192 * X ^ 7 : ℚ⟦X⟧) + (-84 * X ^ 6 - 192 * X ^ 7 : ℚ⟦X⟧) * G) * hP - (60 * X ^ 5 - 660 * X ^ 6 - 336 * X ^ 7) * hY2 - (-15 * X ^ 5 + 24 * X ^ 6 + 480 * X ^ 7 + 192 * X ^ 8) * hY3
  have hLr2_2 : derivative ℚ ((5 * (X * X * X * X * X * X) + 32 * (X * X * X * X * X * X * X) - 512 * (X * X * X * X * X * X * X * X) - 256 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y3) =
      (30 * X ^ 5 + 224 * X ^ 6 - 4096 * X ^ 7 - 2304 * X ^ 8) * derivative ℚ Y3 + (5 * X ^ 6 + 32 * X ^ 7 - 512 * X ^ 8 - 256 * X ^ 9) * derivative ℚ (derivative ℚ Y3) := by
    simp [Derivation.leibniz, d5, d32, d256, d512]
    ring
  have hRr2_2 : derivative ℚ ((15 * (X * X * X * X * X) - 240 * (X * X * X * X * X * X) - 192 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-60 * (X * X * X * X * X) + 876 * (X * X * X * X * X * X) + 576 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (60 * (X * X * X * X * X) - 660 * (X * X * X * X * X * X) - 336 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * Y2 + (-15 * (X * X * X * X * X) + 24 * (X * X * X * X * X * X) + 480 * (X * X * X * X * X * X * X) + 192 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * Y3) =
      (75 * X ^ 4 - 1440 * X ^ 5 - 1344 * X ^ 6) + (-300 * X ^ 4 + 5256 * X ^ 5 + 4032 * X ^ 6) * G + (-60 * X ^ 5 + 876 * X ^ 6 + 576 * X ^ 7) * derivative ℚ G + (300 * X ^ 4 - 3960 * X ^ 5 - 2352 * X ^ 6) * Y2 + (60 * X ^ 5 - 660 * X ^ 6 - 336 * X ^ 7) * derivative ℚ Y2 + (-75 * X ^ 4 + 144 * X ^ 5 + 3360 * X ^ 6 + 1536 * X ^ 7) * Y3 + (-15 * X ^ 5 + 24 * X ^ 6 + 480 * X ^ 7 + 192 * X ^ 8) * derivative ℚ Y3 := by
    simp [Derivation.leibniz, d15, d24, d60, d192, d240, d336, d480, d576, d660, d876]
    ring
  have r2_2 : (30 * X ^ 5 + 224 * X ^ 6 - 4096 * X ^ 7 - 2304 * X ^ 8) * derivative ℚ Y3 + (5 * X ^ 6 + 32 * X ^ 7 - 512 * X ^ 8 - 256 * X ^ 9) * derivative ℚ (derivative ℚ Y3) =
      (75 * X ^ 4 - 1440 * X ^ 5 - 1344 * X ^ 6) + (-300 * X ^ 4 + 5256 * X ^ 5 + 4032 * X ^ 6) * G + (-60 * X ^ 5 + 876 * X ^ 6 + 576 * X ^ 7) * derivative ℚ G + (300 * X ^ 4 - 3960 * X ^ 5 - 2352 * X ^ 6) * Y2 + (60 * X ^ 5 - 660 * X ^ 6 - 336 * X ^ 7) * derivative ℚ Y2 + (-75 * X ^ 4 + 144 * X ^ 5 + 3360 * X ^ 6 + 1536 * X ^ 7) * Y3 + (-15 * X ^ 5 + 24 * X ^ 6 + 480 * X ^ 7 + 192 * X ^ 8) * derivative ℚ Y3 := by
    rw [← hLr2_2, ← hRr2_2, r2_1]
  have r2_2p : (30 * (X * X * X * X * X) + 224 * (X * X * X * X * X * X) - 4096 * (X * X * X * X * X * X * X) - 2304 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y3 + (5 * (X * X * X * X * X * X) + 32 * (X * X * X * X * X * X * X) - 512 * (X * X * X * X * X * X * X * X) - 256 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ Y3) =
      (75 * (X * X * X * X) - 1440 * (X * X * X * X * X) - 1344 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (-300 * (X * X * X * X) + 5256 * (X * X * X * X * X) + 4032 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G + (-60 * (X * X * X * X * X) + 876 * (X * X * X * X * X * X) + 576 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (300 * (X * X * X * X) - 3960 * (X * X * X * X * X) - 2352 * (X * X * X * X * X * X) : ℚ⟦X⟧) * Y2 + (60 * (X * X * X * X * X) - 660 * (X * X * X * X * X * X) - 336 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2 + (-75 * (X * X * X * X) + 144 * (X * X * X * X * X) + 3360 * (X * X * X * X * X * X) + 1536 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * Y3 + (-15 * (X * X * X * X * X) + 24 * (X * X * X * X * X * X) + 480 * (X * X * X * X * X * X * X) + 192 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y3 := by linear_combination r2_2
  have hLr2_3 : derivative ℚ ((30 * (X * X * X * X * X) + 224 * (X * X * X * X * X * X) - 4096 * (X * X * X * X * X * X * X) - 2304 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y3 + (5 * (X * X * X * X * X * X) + 32 * (X * X * X * X * X * X * X) - 512 * (X * X * X * X * X * X * X * X) - 256 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ Y3)) =
      (150 * X ^ 4 + 1344 * X ^ 5 - 28672 * X ^ 6 - 18432 * X ^ 7) * derivative ℚ Y3 + 2 * (30 * X ^ 5 + 224 * X ^ 6 - 4096 * X ^ 7 - 2304 * X ^ 8) * derivative ℚ (derivative ℚ Y3) + (5 * X ^ 6 + 32 * X ^ 7 - 512 * X ^ 8 - 256 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ Y3)) := by
    simp [Derivation.leibniz, d5, d30, d32, d224, d256, d512, d2304, d4096]
    ring
  have hRr2_3 : derivative ℚ ((75 * (X * X * X * X) - 1440 * (X * X * X * X * X) - 1344 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (-300 * (X * X * X * X) + 5256 * (X * X * X * X * X) + 4032 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G + (-60 * (X * X * X * X * X) + 876 * (X * X * X * X * X * X) + 576 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (300 * (X * X * X * X) - 3960 * (X * X * X * X * X) - 2352 * (X * X * X * X * X * X) : ℚ⟦X⟧) * Y2 + (60 * (X * X * X * X * X) - 660 * (X * X * X * X * X * X) - 336 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y2 + (-75 * (X * X * X * X) + 144 * (X * X * X * X * X) + 3360 * (X * X * X * X * X * X) + 1536 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * Y3 + (-15 * (X * X * X * X * X) + 24 * (X * X * X * X * X * X) + 480 * (X * X * X * X * X * X * X) + 192 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ Y3) =
      (300 * X ^ 3 - 7200 * X ^ 4 - 8064 * X ^ 5) + (-1200 * X ^ 3 + 26280 * X ^ 4 + 24192 * X ^ 5) * G + 2 * (-300 * X ^ 4 + 5256 * X ^ 5 + 4032 * X ^ 6) * derivative ℚ G + (-60 * X ^ 5 + 876 * X ^ 6 + 576 * X ^ 7) * derivative ℚ (derivative ℚ G) + (1200 * X ^ 3 - 19800 * X ^ 4 - 14112 * X ^ 5) * Y2 + 2 * (300 * X ^ 4 - 3960 * X ^ 5 - 2352 * X ^ 6) * derivative ℚ Y2 + (60 * X ^ 5 - 660 * X ^ 6 - 336 * X ^ 7) * derivative ℚ (derivative ℚ Y2) + (-300 * X ^ 3 + 720 * X ^ 4 + 20160 * X ^ 5 + 10752 * X ^ 6) * Y3 + 2 * (-75 * X ^ 4 + 144 * X ^ 5 + 3360 * X ^ 6 + 1536 * X ^ 7) * derivative ℚ Y3 + (-15 * X ^ 5 + 24 * X ^ 6 + 480 * X ^ 7 + 192 * X ^ 8) * derivative ℚ (derivative ℚ Y3) := by
    simp [Derivation.leibniz, d15, d24, d60, d75, d144, d192, d300, d336, d480, d576, d660, d876, d1344, d1440, d1536, d2352, d3360, d3960, d4032, d5256]
    ring
  have r2_3 : (150 * X ^ 4 + 1344 * X ^ 5 - 28672 * X ^ 6 - 18432 * X ^ 7) * derivative ℚ Y3 + 2 * (30 * X ^ 5 + 224 * X ^ 6 - 4096 * X ^ 7 - 2304 * X ^ 8) * derivative ℚ (derivative ℚ Y3) + (5 * X ^ 6 + 32 * X ^ 7 - 512 * X ^ 8 - 256 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ Y3)) =
      (300 * X ^ 3 - 7200 * X ^ 4 - 8064 * X ^ 5) + (-1200 * X ^ 3 + 26280 * X ^ 4 + 24192 * X ^ 5) * G + 2 * (-300 * X ^ 4 + 5256 * X ^ 5 + 4032 * X ^ 6) * derivative ℚ G + (-60 * X ^ 5 + 876 * X ^ 6 + 576 * X ^ 7) * derivative ℚ (derivative ℚ G) + (1200 * X ^ 3 - 19800 * X ^ 4 - 14112 * X ^ 5) * Y2 + 2 * (300 * X ^ 4 - 3960 * X ^ 5 - 2352 * X ^ 6) * derivative ℚ Y2 + (60 * X ^ 5 - 660 * X ^ 6 - 336 * X ^ 7) * derivative ℚ (derivative ℚ Y2) + (-300 * X ^ 3 + 720 * X ^ 4 + 20160 * X ^ 5 + 10752 * X ^ 6) * Y3 + 2 * (-75 * X ^ 4 + 144 * X ^ 5 + 3360 * X ^ 6 + 1536 * X ^ 7) * derivative ℚ Y3 + (-15 * X ^ 5 + 24 * X ^ 6 + 480 * X ^ 7 + 192 * X ^ 8) * derivative ℚ (derivative ℚ Y3) := by
    rw [← hLr2_3, ← hRr2_3, r2_2p]
  have hfull : (-125 * X ^ 3 - 2400 * X ^ 4 + 23040 * X ^ 5 + 477952 * X ^ 6 - 2113536 * X ^ 7 - 28311552 * X ^ 8 + 108068864 * X ^ 9 + 195035136 * X ^ 10 + 100663296 * X ^ 11 + 16777216 * X ^ 12 : ℚ⟦X⟧) * ((6769090 * X ^ 4 + 35782496 * X ^ 5 - 741408768 * X ^ 6 + 425485824 * X ^ 7 + 386031616 * X ^ 8) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (29125315 * X ^ 3 + 283783056 * X ^ 4 - 6638757376 * X ^ 5 + 888428032 * X ^ 6 + 3454566400 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (6146865 * X ^ 2 + 446760480 * X ^ 3 - 13631578848 * X ^ 4 - 5256777696 * X ^ 5 + 7221742080 * X ^ 6) * derivative ℚ (derivative ℚ G) + (49602528 * X ^ 2 - 5365534512 * X ^ 3 - 6069672768 * X ^ 4 + 3049528320 * X ^ 5) * derivative ℚ G + (-141110640 * X ^ 2 - 218701272 * X ^ 3 + 52437120 * X ^ 4) * G - (-54626922 * X ^ 2 + 4061664 * X ^ 3)) = 0 := by
    linear_combination (-169227250 * X ^ 3 - 3060671200 * X ^ 4 + 34811013120 * X ^ 5 + 612317175296 * X ^ 6 - 3582064107520 * X ^ 7 - 35141611683840 * X ^ 8 + 188997581799424 * X ^ 9 + 101081147244544 * X ^ 10 - 157820720775168 * X ^ 11 - 129080510906368 * X ^ 12 - 25298967986176 * X ^ 13) * r0_4 +
      (1302594125 * X ^ 2 + 22208722400 * X ^ 3 - 317014023360 * X ^ 4 - 4826273499264 * X ^ 5 + 35659455174656 * X ^ 6 + 290823969538048 * X ^ 7 - 1891061774548992 * X ^ 8 - 465003047026688 * X ^ 9 + 2328372189331456 * X ^ 10 + 1649485771964416 * X ^ 11 + 311204606115840 * X ^ 12) * r0_3 +
      (778445350 * X ^ 2 + 13970782080 * X ^ 3 - 79517422464 * X ^ 4 - 1800663602176 * X ^ 5 + 2494146314240 * X ^ 6 + 52555418894336 * X ^ 7 + 15391886016512 * X ^ 8 - 47423888031744 * X ^ 9 - 33851313225728 * X ^ 10 - 6324741996544 * X ^ 11) * r1_3 +
      (947672600 * X ^ 2 + 13240762880 * X ^ 3 - 143464290304 * X ^ 4 - 1552010735616 * X ^ 5 + 8141951598592 * X ^ 6 + 24263684784128 * X ^ 7 - 9588517109760 * X ^ 8 - 22387718356992 * X ^ 9 - 6324741996544 * X ^ 10) * r2_3 +
      (-4482243625 * X - 77126587000 * X ^ 2 + 1083791888080 * X ^ 3 + 16396126888320 * X ^ 4 - 137423128782848 * X ^ 5 - 1028084170334208 * X ^ 6 + 8116138171105280 * X ^ 7 - 561841912152064 * X ^ 8 - 13487117979090944 * X ^ 9 - 8742358543761408 * X ^ 10 - 1606434403909632 * X ^ 11) * r0_2 +
      (-4435042275 * X - 79774919600 * X ^ 2 + 797550810144 * X ^ 3 + 13506414011392 * X ^ 4 - 45262036230144 * X ^ 5 - 437726601822208 * X ^ 6 + 65809651400704 * X ^ 7 + 639716320870400 * X ^ 8 + 388555392155648 * X ^ 9 + 68314038534144 * X ^ 10) * r1_2 +
      (-5737636400 * X - 84177604800 * X ^ 2 + 1270026077184 * X ^ 3 + 12494146318336 * X ^ 4 - 94309822267392 * X ^ 5 - 172374285090816 * X ^ 6 + 176697559220224 * X ^ 7 + 278418088263680 * X ^ 8 + 79382337028096 * X ^ 9) * r2_2 +
      (6359299000 + 113971850200 * X - 1466875768200 * X ^ 2 - 24171472803232 * X ^ 3 + 184649042056704 * X ^ 4 + 1511124877017088 * X ^ 5 - 14085154571763712 * X ^ 6 + 5832773050040320 * X ^ 7 + 30230603756994560 * X ^ 8 + 18438708057341952 * X ^ 9 + 3324598321938432 * X ^ 10) * r0_1 +
      (7313193850 + 132619326840 * X - 1567895554768 * X ^ 2 - 26621699317248 * X ^ 3 + 167710875287552 * X ^ 4 + 1073003201626112 * X ^ 5 - 781862426968064 * X ^ 6 - 2380601178456064 * X ^ 7 - 1311060119257088 * X ^ 8 - 219432144076800 * X ^ 9) * r1_1 +
      (10492843350 + 157069625440 * X - 2609363099648 * X ^ 2 - 28130681240576 * X ^ 3 + 299883851579392 * X ^ 4 + 333652065779712 * X ^ 5 - 782028635766784 * X ^ 6 - 988710126485504 * X ^ 7 - 290037195341824 * X ^ 8) * r2_1
  have hM0 : (-125 - 2400 * X + 23040 * X ^ 2 + 477952 * X ^ 3 - 2113536 * X ^ 4 - 28311552 * X ^ 5 + 108068864 * X ^ 6 + 195035136 * X ^ 7 + 100663296 * X ^ 8 + 16777216 * X ^ 9 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    have kc : constantCoeff (125 : ℚ⟦X⟧) = 125 := cnum 125
    simp [kc] at h'
  have hM : (-125 * X ^ 3 - 2400 * X ^ 4 + 23040 * X ^ 5 + 477952 * X ^ 6 - 2113536 * X ^ 7 - 28311552 * X ^ 8 + 108068864 * X ^ 9 + 195035136 * X ^ 10 + 100663296 * X ^ 11 + 16777216 * X ^ 12 : ℚ⟦X⟧) ≠ 0 := by
    have e : (-125 * X ^ 3 - 2400 * X ^ 4 + 23040 * X ^ 5 + 477952 * X ^ 6 - 2113536 * X ^ 7 - 28311552 * X ^ 8 + 108068864 * X ^ 9 + 195035136 * X ^ 10 + 100663296 * X ^ 11 + 16777216 * X ^ 12 : ℚ⟦X⟧) = X ^ 3 * (-125 - 2400 * X + 23040 * X ^ 2 + 477952 * X ^ 3 - 2113536 * X ^ 4 - 28311552 * X ^ 5 + 108068864 * X ^ 6 + 195035136 * X ^ 7 + 100663296 * X ^ 8 + 16777216 * X ^ 9 : ℚ⟦X⟧) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 3 X_ne_zero) hM0
  have h := (mul_eq_zero.mp hfull).resolve_left hM
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem keyC (G Y2 Y3 : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (4 : ℚ⟦X⟧) * G + (-4 : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (hY2 : Y2 = G * G)
    (hY3 : Y3 = G * G * G) :
    derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) * X * X * X * X * C 6769090 + derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) * X * X * X * X * X * C 35782496 +
      derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) * X * X * X * X * X * X * C (-741408768) + derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) * X * X * X * X * X * X * X * C 425485824 +
      derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) * X * X * X * X * X * X * X * X * C 386031616 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 29125315 +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C 283783056 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C (-6638757376) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C 888428032 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * C 3454566400 +
      derivative ℚ (derivative ℚ G) * X * X * C 6146865 + derivative ℚ (derivative ℚ G) * X * X * X * C 446760480 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-13631578848) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-5256777696) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 7221742080 + derivative ℚ G * X * X * C 49602528 +
      derivative ℚ G * X * X * X * C (-5365534512) + derivative ℚ G * X * X * X * X * C (-6069672768) +
      derivative ℚ G * X * X * X * X * X * C 3049528320 + G * X * X * C (-141110640) +
      G * X * X * X * C (-218701272) + G * X * X * X * X * C 52437120 =
      C (-54626922) * X * X + C 4061664 * X * X * X := by
  have h := key G Y2 Y3 hP hY2 hY3
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem rel (G Y2 Y3 : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (4 : ℚ⟦X⟧) * G + (-4 : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (hY2 : Y2 = G * G)
    (hY3 : Y3 = G * G * G) (m : ℕ) :
    6769090 * ((m : ℚ) + 8) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 35782496 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-741408768) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 425485824 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      386031616 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1 + 1) G + 29125315 * ((m : ℚ) + 8) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      283783056 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-6638757376) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      888428032 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 3454566400 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      6146865 * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 446760480 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-13631578848) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-5256777696) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      7221742080 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + 49602528 * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-5365534512) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-6069672768) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      3049528320 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + (-141110640) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-218701272) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 52437120 * coeff (m + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G Y2 Y3 hP hY2 hY3)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem relE0 (G Y2 Y3 : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (4 : ℚ⟦X⟧) * G + (-4 : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (hY2 : Y2 = G * G)
    (hY3 : Y3 = G * G * G) :
    162458160 * coeff (0 + 1 + 1 + 1 + 1) G + 699007560 * coeff (0 + 1 + 1 + 1 + 1) G +
      1702698336 * coeff (0 + 1 + 1 + 1) G + 73762380 * coeff (0 + 1 + 1 + 1 + 1) G +
      2680562880 * coeff (0 + 1 + 1 + 1) G + (-27263157696) * coeff (0 + 1 + 1) G +
      148807584 * coeff (0 + 1 + 1 + 1) G + (-10731069024) * coeff (0 + 1 + 1) G +
      (-6069672768) * coeff (0 + 1) G + (-141110640) * coeff (0 + 1 + 1) G +
      (-218701272) * coeff (0 + 1) G + 52437120 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G Y2 Y3 hP hY2 hY3)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem relE1 (G Y2 Y3 : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (4 : ℚ⟦X⟧) * G + (-4 : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (hY2 : Y2 = G * G)
    (hY3 : Y3 = G * G * G) :
    812290800 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 858779904 * coeff (0 + 1 + 1 + 1 + 1) G +
      1747518900 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 6810793344 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-39832544256) * coeff (0 + 1 + 1 + 1) G + 122937300 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      5361125760 * coeff (0 + 1 + 1 + 1 + 1) G + (-81789473088) * coeff (0 + 1 + 1 + 1) G +
      (-10513555392) * coeff (0 + 1 + 1) G + 198410112 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-16096603536) * coeff (0 + 1 + 1 + 1) G + (-12139345536) * coeff (0 + 1 + 1) G +
      3049528320 * coeff (0 + 1) G + (-141110640) * coeff (0 + 1 + 1 + 1) G +
      (-218701272) * coeff (0 + 1 + 1) G + 52437120 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G Y2 Y3 hP hY2 hY3)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem relE2 (G Y2 Y3 : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (4 : ℚ⟦X⟧) * G + (-4 : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (hY2 : Y2 = G * G)
    (hY3 : Y3 = G * G * G) :
    2436872400 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 4293899520 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-17793810432) * coeff (0 + 1 + 1 + 1 + 1) G + 3495037800 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      17026983360 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-159330177024) * coeff (0 + 1 + 1 + 1 + 1) G +
      5330568192 * coeff (0 + 1 + 1 + 1) G + 184405950 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      8935209600 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-163578946176) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-31540666176) * coeff (0 + 1 + 1 + 1) G + 14443484160 * coeff (0 + 1 + 1) G +
      248012640 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-21462138048) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-18209018304) * coeff (0 + 1 + 1 + 1) G + 6099056640 * coeff (0 + 1 + 1) G +
      (-141110640) * coeff (0 + 1 + 1 + 1 + 1) G + (-218701272) * coeff (0 + 1 + 1 + 1) G +
      52437120 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G Y2 Y3 hP hY2 hY3)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem relE3 (G Y2 Y3 : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (4 : ℚ⟦X⟧) * G + (-4 : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (hY2 : Y2 = G * G)
    (hY3 : Y3 = G * G * G) :
    5686035600 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 12881698560 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-88969052160) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 10211659776 * coeff (0 + 1 + 1 + 1 + 1) G +
      6116316150 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 34053966720 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-398325442560) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 21322272768 * coeff (0 + 1 + 1 + 1 + 1) G +
      20727398400 * coeff (0 + 1 + 1 + 1) G + 258168330 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      13402814400 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-272631576960) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-63081332352) * coeff (0 + 1 + 1 + 1 + 1) G + 43330452480 * coeff (0 + 1 + 1 + 1) G +
      297615168 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-26827672560) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-24278691072) * coeff (0 + 1 + 1 + 1 + 1) G + 9148584960 * coeff (0 + 1 + 1 + 1) G +
      (-141110640) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-218701272) * coeff (0 + 1 + 1 + 1 + 1) G +
      52437120 * coeff (0 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G Y2 Y3 hP hY2 hY3)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h


set_option maxRecDepth 20000 in
set_option maxHeartbeats 32000000 in
theorem gen : ∀ G : ℚ⟦X⟧, coeff 0 G = 1 →
    X * G ^ 4 + G ^ 3 - 4 * G ^ 2 + 4 * G - 1 = 0 →
    ∀ n : ℕ, 4 ≤ n →
      (11489225 * (n : ℚ) - 6769090 * (n : ℚ) ^ 2 - 11489225 * (n : ℚ) ^ 3 + 6769090 * (n : ℚ) ^ 4) * coeff n G + (41809904 * (n : ℚ) - 3550496 * (n : ℚ) ^ 2 - 74041904 * (n : ℚ) ^ 3 + 35782496 * (n : ℚ) ^ 4) * coeff (n - 1) G +
        (-838389840 + 4361618224 * (n : ℚ) - 6522784992 * (n : ℚ) ^ 2 + 3740965376 * (n : ℚ) ^ 3 - 741408768 * (n : ℚ) ^ 4) * coeff (n - 2) G + (54778199400 - 73032263200 * (n : ℚ) + 34714898976 * (n : ℚ) ^ 2 - 6770316800 * (n : ℚ) ^ 3 + 425485824 * (n : ℚ) ^ 4) * coeff (n - 3) G +
        (42007754880 - 52596407808 * (n : ℚ) + 24502905344 * (n : ℚ) ^ 2 - 5038129152 * (n : ℚ) ^ 3 + 386031616 * (n : ℚ) ^ 4) * coeff (n - 4) G = 0 := by
  intro G _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  have hP : (-1 : PowerSeries ℚ) + (4 : PowerSeries ℚ) * G + (-4 : PowerSeries ℚ) * G ^ 2 + (1 : PowerSeries ℚ) * G ^ 3 + (PowerSeries.X : PowerSeries ℚ) * G ^ 4 = 0 := by linear_combination hG
  cases m with
  | zero =>
    have r := A045743Aux.relE0 G (G * G) (G * G * G) hP rfl rfl
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A045743Aux.relE1 G (G * G) (G * G * G) hP rfl rfl
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A045743Aux.relE2 G (G * G) (G * G * G) hP rfl rfl
        push_cast
        linear_combination r
      | succ m =>
        cases m with
        | zero =>
          have r := A045743Aux.relE3 G (G * G) (G * G * G) hP rfl rfl
          push_cast
          linear_combination r
        | succ m =>
          have r := A045743Aux.rel G (G * G) (G * G * G) hP rfl rfl m
          push_cast
          linear_combination r

end A045743Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a045743.main := by
  intro F h0 hF n hn
  have hP : PowerSeries.X * F ^ 4 + F ^ 3 - 4 * F ^ 2 + 4 * F - 1 = 0 := by linear_combination hF
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  have key := A045743Aux.gen F h0 hP (m + 5) (by omega)
  have e1 : m + 5 - 1 = m + 4 := rfl
  have e2 : m + 5 - 2 = m + 3 := rfl
  have e3 : m + 5 - 3 = m + 2 := rfl
  have e4 : m + 5 - 4 = m + 1 := rfl
  have f1 : m + 6 - 1 = m + 5 := rfl
  have f2 : m + 6 - 2 = m + 4 := rfl
  have f3 : m + 6 - 3 = m + 3 := rfl
  have f4 : m + 6 - 4 = m + 2 := rfl
  have f5 : m + 6 - 5 = m + 1 := rfl
  rw [e1, e2, e3, e4] at key
  rw [f1, f2, f3, f4, f5]
  push_cast at key ⊢
  linear_combination key
