import OMAStatements.S_oeis_a217539

-- Problem: A217539: Number of Dyck paths of semilength n which satisfy the condition: number of returns + number of hills < number of peaks.
-- Upstream: formal-conjectures statements/oeis-a217539.lean:0 (declaration OMA.S_oeis_a217539.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The g.f. of a is G = c - 1 - x^2 (x m)' - x m. Differentiating the equations for T and m shows that
G * (4 x T) = 2 (1 - 3x - 2x^2 - S T), so G is algebraic: it satisfies a polynomial equation
Phi(x, G) = 0. Differentiating that equation repeatedly expresses the derivatives of G through G;
substituting into the differential operator read off the recurrence and reducing modulo Phi gives a
polynomial identity, and the recurrence is the coefficient of a power of x in the resulting equation. -/

namespace A217539Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (X ^ 6 : ℚ⟦X⟧) + (-1 + 8 * X - 14 * X ^ 2 - 20 * X ^ 3 + 37 * X ^ 4 + 40 * X ^ 5 + 6 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (X ^ 2 - 4 * X ^ 3 - 2 * X ^ 4 + 12 * X ^ 5 + 9 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 = 0) :
    (2 * X ^ 2 - 15 * X ^ 3 + 28 * X ^ 4 + 9 * X ^ 5 - 36 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-2 * X + 8 * X ^ 2 - 17 * X ^ 3 + 69 * X ^ 4 - 54 * X ^ 5) * derivative ℚ G + (-6 + 26 * X - 37 * X ^ 2 + 21 * X ^ 3) * G =
      0 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d9 : derivative ℚ (9 : ℚ⟦X⟧) = 0 := dnum 9
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d14 : derivative ℚ (14 : ℚ⟦X⟧) = 0 := dnum 14
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d20 : derivative ℚ (20 : ℚ⟦X⟧) = 0 := dnum 20
  have d28 : derivative ℚ (28 : ℚ⟦X⟧) = 0 := dnum 28
  have d36 : derivative ℚ (36 : ℚ⟦X⟧) = 0 := dnum 36
  have d37 : derivative ℚ (37 : ℚ⟦X⟧) = 0 := dnum 37
  have d40 : derivative ℚ (40 : ℚ⟦X⟧) = 0 := dnum 40
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d54 : derivative ℚ (54 : ℚ⟦X⟧) = 0 := dnum 54
  have d60 : derivative ℚ (60 : ℚ⟦X⟧) = 0 := dnum 60
  have d74 : derivative ℚ (74 : ℚ⟦X⟧) = 0 := dnum 74
  have d80 : derivative ℚ (80 : ℚ⟦X⟧) = 0 := dnum 80
  have d148 : derivative ℚ (148 : ℚ⟦X⟧) = 0 := dnum 148
  have d200 : derivative ℚ (200 : ℚ⟦X⟧) = 0 := dnum 200
  have hp0 : (1 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (-1 + 8 * X - 14 * (X * X) - 20 * (X * X * X) + 37 * (X * X * X * X) + 40 * (X * X * X * X * X) + 6 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * G + (1 * (X * X) - 4 * (X * X * X) - 2 * (X * X * X * X) + 12 * (X * X * X * X * X) + 9 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 * (X * X * X * X * X * X) : ℚ⟦X⟧) + (-1 + 8 * X - 14 * (X * X) - 20 * (X * X * X) + 37 * (X * X * X * X) + 40 * (X * X * X * X * X) + 6 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * G + (1 * (X * X) - 4 * (X * X * X) - 2 * (X * X * X * X) + 12 * (X * X * X * X * X) + 9 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * G * G * G) =
      (6 * X ^ 5 : ℚ⟦X⟧) + (-2 + 16 * X - 28 * X ^ 2 - 40 * X ^ 3 + 74 * X ^ 4 + 80 * X ^ 5 + 12 * X ^ 6 : ℚ⟦X⟧) * G * (derivative ℚ G) + (8 - 28 * X - 60 * X ^ 2 + 148 * X ^ 3 + 200 * X ^ 4 + 36 * X ^ 5 : ℚ⟦X⟧) * G ^ 2 + (4 * X ^ 2 - 16 * X ^ 3 - 8 * X ^ 4 + 48 * X ^ 5 + 36 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (2 * X - 12 * X ^ 2 - 8 * X ^ 3 + 60 * X ^ 4 + 54 * X ^ 5 : ℚ⟦X⟧) * G ^ 4 := by
    simp [Derivation.leibniz, d2, d4, d6, d8, d9, d12, d14, d20, d37, d40]
    ring
  have hd1 : (6 * X ^ 5 : ℚ⟦X⟧) + (-2 + 16 * X - 28 * X ^ 2 - 40 * X ^ 3 + 74 * X ^ 4 + 80 * X ^ 5 + 12 * X ^ 6 : ℚ⟦X⟧) * G * (derivative ℚ G) + (8 - 28 * X - 60 * X ^ 2 + 148 * X ^ 3 + 200 * X ^ 4 + 36 * X ^ 5 : ℚ⟦X⟧) * G ^ 2 + (4 * X ^ 2 - 16 * X ^ 3 - 8 * X ^ 4 + 48 * X ^ 5 + 36 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (2 * X - 12 * X ^ 2 - 8 * X ^ 3 + 60 * X ^ 4 + 54 * X ^ 5 : ℚ⟦X⟧) * G ^ 4 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (6 * (X * X * X * X * X) : ℚ⟦X⟧) + (-2 + 16 * X - 28 * (X * X) - 40 * (X * X * X) + 74 * (X * X * X * X) + 80 * (X * X * X * X * X) + 12 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (8 - 28 * X - 60 * (X * X) + 148 * (X * X * X) + 200 * (X * X * X * X) + 36 * (X * X * X * X * X) : ℚ⟦X⟧) * G * G + (4 * (X * X) - 16 * (X * X * X) - 8 * (X * X * X * X) + 48 * (X * X * X * X * X) + 36 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (2 * X - 12 * (X * X) - 8 * (X * X * X) + 60 * (X * X * X * X) + 54 * (X * X * X * X * X) : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((6 * (X * X * X * X * X) : ℚ⟦X⟧) + (-2 + 16 * X - 28 * (X * X) - 40 * (X * X * X) + 74 * (X * X * X * X) + 80 * (X * X * X * X * X) + 12 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (8 - 28 * X - 60 * (X * X) + 148 * (X * X * X) + 200 * (X * X * X * X) + 36 * (X * X * X * X * X) : ℚ⟦X⟧) * G * G + (4 * (X * X) - 16 * (X * X * X) - 8 * (X * X * X * X) + 48 * (X * X * X * X * X) + 36 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (2 * X - 12 * (X * X) - 8 * (X * X * X) + 60 * (X * X * X * X) + 54 * (X * X * X * X * X) : ℚ⟦X⟧) * G * G * G * G) =
      (30 * X ^ 4 : ℚ⟦X⟧) + (-2 + 16 * X - 28 * X ^ 2 - 40 * X ^ 3 + 74 * X ^ 4 + 80 * X ^ 5 + 12 * X ^ 6 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 + 16 * X - 28 * X ^ 2 - 40 * X ^ 3 + 74 * X ^ 4 + 80 * X ^ 5 + 12 * X ^ 6 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (32 - 112 * X - 240 * X ^ 2 + 592 * X ^ 3 + 800 * X ^ 4 + 144 * X ^ 5 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-28 - 120 * X + 444 * X ^ 2 + 800 * X ^ 3 + 180 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 + (12 * X ^ 2 - 48 * X ^ 3 - 24 * X ^ 4 + 144 * X ^ 5 + 108 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 * X ^ 2 - 16 * X ^ 3 - 8 * X ^ 4 + 48 * X ^ 5 + 36 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (16 * X - 96 * X ^ 2 - 64 * X ^ 3 + 480 * X ^ 4 + 432 * X ^ 5 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (2 - 24 * X - 24 * X ^ 2 + 240 * X ^ 3 + 270 * X ^ 4 : ℚ⟦X⟧) * G ^ 4 := by
    simp [Derivation.leibniz, d2, d4, d6, d8, d12, d16, d28, d36, d40, d48, d54, d60, d74, d80, d148, d200]
    ring
  have hd2 : (30 * X ^ 4 : ℚ⟦X⟧) + (-2 + 16 * X - 28 * X ^ 2 - 40 * X ^ 3 + 74 * X ^ 4 + 80 * X ^ 5 + 12 * X ^ 6 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 + 16 * X - 28 * X ^ 2 - 40 * X ^ 3 + 74 * X ^ 4 + 80 * X ^ 5 + 12 * X ^ 6 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (32 - 112 * X - 240 * X ^ 2 + 592 * X ^ 3 + 800 * X ^ 4 + 144 * X ^ 5 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-28 - 120 * X + 444 * X ^ 2 + 800 * X ^ 3 + 180 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 + (12 * X ^ 2 - 48 * X ^ 3 - 24 * X ^ 4 + 144 * X ^ 5 + 108 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 * X ^ 2 - 16 * X ^ 3 - 8 * X ^ 4 + 48 * X ^ 5 + 36 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (16 * X - 96 * X ^ 2 - 64 * X ^ 3 + 480 * X ^ 4 + 432 * X ^ 5 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (2 - 24 * X - 24 * X ^ 2 + 240 * X ^ 3 + 270 * X ^ 4 : ℚ⟦X⟧) * G ^ 4 = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((-2 + 16 * X - 28 * X ^ 2 - 40 * X ^ 3 + 74 * X ^ 4 + 80 * X ^ 5 + 12 * X ^ 6 : ℚ⟦X⟧) * G + (4 * X ^ 2 - 16 * X ^ 3 - 8 * X ^ 4 + 48 * X ^ 5 + 36 * X ^ 6 : ℚ⟦X⟧) * G ^ 3) ^ 3 * ((2 * X ^ 2 - 15 * X ^ 3 + 28 * X ^ 4 + 9 * X ^ 5 - 36 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-2 * X + 8 * X ^ 2 - 17 * X ^ 3 + 69 * X ^ 4 - 54 * X ^ 5) * derivative ℚ G + (-6 + 26 * X - 37 * X ^ 2 + 21 * X ^ 3) * G - (0)) = 0 := by
    linear_combination ((144 * X ^ 6 - 2232 * X ^ 7 + 12672 * X ^ 8 - 27720 * X ^ 9 - 6480 * X ^ 10 + 104328 * X ^ 11 - 55584 * X ^ 12 - 149976 * X ^ 13 + 57888 * X ^ 14 + 99792 * X ^ 15 + 15552 * X ^ 16 : ℚ⟦X⟧) + (-48 + 912 * X - 6504 * X ^ 2 + 18552 * X ^ 3 + 3120 * X ^ 4 - 111744 * X ^ 5 + 42960 * X ^ 6 + 511440 * X ^ 7 - 150096 * X ^ 8 - 1777152 * X ^ 9 + 18744 * X ^ 10 + 3692616 * X ^ 11 + 1528464 * X ^ 12 - 3285648 * X ^ 13 - 3156192 * X ^ 14 - 706320 * X ^ 15 + 62208 * X ^ 16 : ℚ⟦X⟧) * G ^ 2 + (240 * X ^ 2 - 3240 * X ^ 3 + 14592 * X ^ 4 - 13800 * X ^ 5 - 68160 * X ^ 6 + 107040 * X ^ 7 + 297408 * X ^ 8 - 472656 * X ^ 9 - 939024 * X ^ 10 + 1173144 * X ^ 11 + 1969920 * X ^ 12 - 1025352 * X ^ 13 - 2407968 * X ^ 14 - 944784 * X ^ 15 - 46656 * X ^ 16 : ℚ⟦X⟧) * G ^ 4 + (-224 * X ^ 4 + 2224 * X ^ 5 - 5664 * X ^ 6 - 8048 * X ^ 7 + 39616 * X ^ 8 + 36576 * X ^ 9 - 170304 * X ^ 10 - 165600 * X ^ 11 + 434592 * X ^ 12 + 506736 * X ^ 13 - 427680 * X ^ 14 - 781488 * X ^ 15 - 279936 * X ^ 16 : ℚ⟦X⟧) * G ^ 6) * hP +
      ((-24 * X ^ 7 + 372 * X ^ 8 - 2112 * X ^ 9 + 4620 * X ^ 10 + 1080 * X ^ 11 - 17388 * X ^ 12 + 9264 * X ^ 13 + 24996 * X ^ 14 - 9648 * X ^ 15 - 16632 * X ^ 16 - 2592 * X ^ 17 : ℚ⟦X⟧) + (-8 * X ^ 2 + 188 * X ^ 3 - 1808 * X ^ 4 + 8748 * X ^ 5 - 19040 * X ^ 6 - 5464 * X ^ 7 + 106432 * X ^ 8 - 119880 * X ^ 9 - 213256 * X ^ 10 + 389404 * X ^ 11 + 280528 * X ^ 12 - 532052 * X ^ 13 - 355792 * X ^ 14 + 266496 * X ^ 15 + 273024 * X ^ 16 + 67824 * X ^ 17 + 5184 * X ^ 18 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-8 * X + 256 * X ^ 2 - 3140 * X ^ 3 + 18716 * X ^ 4 - 50304 * X ^ 5 - 1680 * X ^ 6 + 319968 * X ^ 7 - 453488 * X ^ 8 - 733440 * X ^ 9 + 1662336 * X ^ 10 + 1129652 * X ^ 11 - 2671220 * X ^ 12 - 1795544 * X ^ 13 + 1636560 * X ^ 14 + 1748304 * X ^ 15 + 439560 * X ^ 16 + 15552 * X ^ 17 : ℚ⟦X⟧) * G ^ 2 + (64 * X ^ 4 - 1248 * X ^ 5 + 9472 * X ^ 6 - 32096 * X ^ 7 + 23808 * X ^ 8 + 141184 * X ^ 9 - 301568 * X ^ 10 - 206016 * X ^ 11 + 872256 * X ^ 12 + 195616 * X ^ 13 - 1244160 * X ^ 14 - 407520 * X ^ 15 + 749952 * X ^ 16 + 482112 * X ^ 17 + 62208 * X ^ 18 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (88 * X ^ 3 - 1780 * X ^ 4 + 14088 * X ^ 5 - 50236 * X ^ 6 + 41872 * X ^ 7 + 233008 * X ^ 8 - 549872 * X ^ 9 - 326584 * X ^ 10 + 1719832 * X ^ 11 + 235308 * X ^ 12 - 2720760 * X ^ 13 - 718092 * X ^ 14 + 1928448 * X ^ 15 + 1225368 * X ^ 16 + 163296 * X ^ 17 : ℚ⟦X⟧) * G ^ 4 + (-96 * X ^ 6 + 1488 * X ^ 7 - 8256 * X ^ 8 + 15120 * X ^ 9 + 24960 * X ^ 10 - 114528 * X ^ 11 + 6144 * X ^ 12 + 319392 * X ^ 13 - 73440 * X ^ 14 - 486000 * X ^ 15 - 15552 * X ^ 16 + 338256 * X ^ 17 + 139968 * X ^ 18 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-112 * X ^ 5 + 1784 * X ^ 6 - 10240 * X ^ 7 + 19576 * X ^ 8 + 33248 * X ^ 9 - 162832 * X ^ 10 + 17984 * X ^ 11 + 494256 * X ^ 12 - 154224 * X ^ 13 - 830952 * X ^ 14 + 25920 * X ^ 15 + 670680 * X ^ 16 + 279936 * X ^ 17 : ℚ⟦X⟧) * G ^ 6) * hd1 +
      ((8 * X ^ 2 - 188 * X ^ 3 + 1808 * X ^ 4 - 8748 * X ^ 5 + 19040 * X ^ 6 + 5464 * X ^ 7 - 106432 * X ^ 8 + 119880 * X ^ 9 + 213256 * X ^ 10 - 389404 * X ^ 11 - 280528 * X ^ 12 + 532052 * X ^ 13 + 355792 * X ^ 14 - 266496 * X ^ 15 - 273024 * X ^ 16 - 67824 * X ^ 17 - 5184 * X ^ 18 : ℚ⟦X⟧) * G ^ 2 + (-32 * X ^ 4 + 624 * X ^ 5 - 4736 * X ^ 6 + 16048 * X ^ 7 - 11904 * X ^ 8 - 70592 * X ^ 9 + 150784 * X ^ 10 + 103008 * X ^ 11 - 436128 * X ^ 12 - 97808 * X ^ 13 + 622080 * X ^ 14 + 203760 * X ^ 15 - 374976 * X ^ 16 - 241056 * X ^ 17 - 31104 * X ^ 18 : ℚ⟦X⟧) * G ^ 4 + (32 * X ^ 6 - 496 * X ^ 7 + 2752 * X ^ 8 - 5040 * X ^ 9 - 8320 * X ^ 10 + 38176 * X ^ 11 - 2048 * X ^ 12 - 106464 * X ^ 13 + 24480 * X ^ 14 + 162000 * X ^ 15 + 5184 * X ^ 16 - 112752 * X ^ 17 - 46656 * X ^ 18 : ℚ⟦X⟧) * G ^ 6) * hd2
  have hres : ((-5832 + 69984 * X - 268272 * X ^ 2 + 209952 * X ^ 3 + 670680 * X ^ 4 - 559872 * X ^ 5 - 956448 * X ^ 6 - 279936 * X ^ 7 - 11664 * X ^ 8 : ℚ⟦X⟧) * G + (5832 * X ^ 2 - 46656 * X ^ 3 + 81648 * X ^ 4 + 116640 * X ^ 5 - 215784 * X ^ 6 - 233280 * X ^ 7 - 34992 * X ^ 8 : ℚ⟦X⟧) * G ^ 3) * ((-2 + 16 * X - 28 * X ^ 2 - 40 * X ^ 3 + 74 * X ^ 4 + 80 * X ^ 5 + 12 * X ^ 6 : ℚ⟦X⟧) * G + (4 * X ^ 2 - 16 * X ^ 3 - 8 * X ^ 4 + 48 * X ^ 5 + 36 * X ^ 6 : ℚ⟦X⟧) * G ^ 3) = (11664 * X ^ 6 - 139968 * X ^ 7 + 536544 * X ^ 8 - 419904 * X ^ 9 - 1341360 * X ^ 10 + 1119744 * X ^ 11 + 1912896 * X ^ 12 + 559872 * X ^ 13 : ℚ⟦X⟧) := by
    linear_combination (-((11664 - 139968 * X + 536544 * X ^ 2 - 419904 * X ^ 3 - 1341360 * X ^ 4 + 1119744 * X ^ 5 + 1912896 * X ^ 6 + 559872 * X ^ 7 : ℚ⟦X⟧) + (-23328 * X ^ 2 + 186624 * X ^ 3 - 326592 * X ^ 4 - 466560 * X ^ 5 + 863136 * X ^ 6 + 933120 * X ^ 7 + 139968 * X ^ 8 : ℚ⟦X⟧) * G ^ 2)) * hP
  have hd0 : (11664 - 139968 * X + 536544 * X ^ 2 - 419904 * X ^ 3 - 1341360 * X ^ 4 + 1119744 * X ^ 5 + 1912896 * X ^ 6 + 559872 * X ^ 7 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    have kc : constantCoeff (11664 : ℚ⟦X⟧) = 11664 := cnum 11664
    simp [kc] at h'
  have hdisc : (11664 * X ^ 6 - 139968 * X ^ 7 + 536544 * X ^ 8 - 419904 * X ^ 9 - 1341360 * X ^ 10 + 1119744 * X ^ 11 + 1912896 * X ^ 12 + 559872 * X ^ 13 : ℚ⟦X⟧) ≠ 0 := by
    have e : (11664 * X ^ 6 - 139968 * X ^ 7 + 536544 * X ^ 8 - 419904 * X ^ 9 - 1341360 * X ^ 10 + 1119744 * X ^ 11 + 1912896 * X ^ 12 + 559872 * X ^ 13 : ℚ⟦X⟧) = X ^ 6 * (11664 - 139968 * X + 536544 * X ^ 2 - 419904 * X ^ 3 - 1341360 * X ^ 4 + 1119744 * X ^ 5 + 1912896 * X ^ 6 + 559872 * X ^ 7 : ℚ⟦X⟧) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 6 X_ne_zero) hd0
  have hPG : (-2 + 16 * X - 28 * X ^ 2 - 40 * X ^ 3 + 74 * X ^ 4 + 80 * X ^ 5 + 12 * X ^ 6 : ℚ⟦X⟧) * G + (4 * X ^ 2 - 16 * X ^ 3 - 8 * X ^ 4 + 48 * X ^ 5 + 36 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hres
    exact hdisc hres.symm
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (X ^ 6 : ℚ⟦X⟧) + (-1 + 8 * X - 14 * X ^ 2 - 20 * X ^ 3 + 37 * X ^ 4 + 40 * X ^ 5 + 6 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (X ^ 2 - 4 * X ^ 3 - 2 * X ^ 4 + 12 * X ^ 5 + 9 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 = 0) :
    derivative ℚ (derivative ℚ G) * X * X * C 2 + derivative ℚ (derivative ℚ G) * X * X * X * C (-15) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 28 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 9 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-36) + derivative ℚ G * X * C (-2) +
      derivative ℚ G * X * X * C 8 + derivative ℚ G * X * X * X * C (-17) +
      derivative ℚ G * X * X * X * X * C 69 + derivative ℚ G * X * X * X * X * X * C (-54) +
      G * C (-6) + G * X * C 26 +
      G * X * X * C (-37) + G * X * X * X * C 21 =
      0 := by
  have h := key G hP
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (X ^ 6 : ℚ⟦X⟧) + (-1 + 8 * X - 14 * X ^ 2 - 20 * X ^ 3 + 37 * X ^ 4 + 40 * X ^ 5 + 6 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (X ^ 2 - 4 * X ^ 3 - 2 * X ^ 4 + 12 * X ^ 5 + 9 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 = 0) (m : ℕ) :
    2 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-15) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      28 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + 9 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-36) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + (-2) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      8 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-17) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      69 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-54) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 26 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-37) * coeff (m + 1 + 1 + 1 + 1) G + 21 * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (X ^ 6 : ℚ⟦X⟧) + (-1 + 8 * X - 14 * X ^ 2 - 20 * X ^ 3 + 37 * X ^ 4 + 40 * X ^ 5 + 6 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (X ^ 2 - 4 * X ^ 3 - 2 * X ^ 4 + 12 * X ^ 5 + 9 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 = 0) :
    24 * coeff (0 + 1 + 1 + 1 + 1) G + (-90) * coeff (0 + 1 + 1 + 1) G +
      56 * coeff (0 + 1 + 1) G + (-8) * coeff (0 + 1 + 1 + 1 + 1) G +
      24 * coeff (0 + 1 + 1 + 1) G + (-34) * coeff (0 + 1 + 1) G +
      69 * coeff (0 + 1) G + (-6) * coeff (0 + 1 + 1 + 1 + 1) G +
      26 * coeff (0 + 1 + 1 + 1) G + (-37) * coeff (0 + 1 + 1) G +
      21 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (X ^ 6 : ℚ⟦X⟧) + (-1 + 8 * X - 14 * X ^ 2 - 20 * X ^ 3 + 37 * X ^ 4 + 40 * X ^ 5 + 6 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (X ^ 2 - 4 * X ^ 3 - 2 * X ^ 4 + 12 * X ^ 5 + 9 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 = 0) :
    40 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-180) * coeff (0 + 1 + 1 + 1 + 1) G +
      168 * coeff (0 + 1 + 1 + 1) G + 18 * coeff (0 + 1 + 1) G +
      (-10) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 32 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-51) * coeff (0 + 1 + 1 + 1) G + 138 * coeff (0 + 1 + 1) G +
      (-54) * coeff (0 + 1) G + (-6) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      26 * coeff (0 + 1 + 1 + 1 + 1) G + (-37) * coeff (0 + 1 + 1 + 1) G +
      21 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h


set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem gen : ∀ T W G : ℚ⟦X⟧, T ^ 2 = 1 - 2 * X - 3 * X ^ 2 →
    coeff 0 T = 1 →
    W ^ 2 = 1 - 4 * X →
    coeff 0 W = 1 →
    G * (4 * X * T) = 2 * (1 - 3 * X - 2 * X ^ 2 - W * T) →
    coeff 0 G = 0 →
    ∀ n : ℕ, 4 ≤ n →
      (-6 - 4 * (n : ℚ) + 2 * (n : ℚ) ^ 2) * coeff n G + (-12 + 53 * (n : ℚ) - 15 * (n : ℚ) ^ 2) * coeff (n - 1) G +
        (165 - 157 * (n : ℚ) + 28 * (n : ℚ) ^ 2) * coeff (n - 2) G + (-78 + 6 * (n : ℚ) + 9 * (n : ℚ) ^ 2) * coeff (n - 3) G +
        (-504 + 270 * (n : ℚ) - 36 * (n : ℚ) ^ 2) * coeff (n - 4) G = 0 := by
  intro T W G hT _ hW _ hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  have hn : ((4) * PowerSeries.X * T) * ((64) * PowerSeries.X ^ 3 * T ^ 3) = (256 * PowerSeries.X ^ 4 - 1024 * PowerSeries.X ^ 5 - 512 * PowerSeries.X ^ 6 + 3072 * PowerSeries.X ^ 7 + 2304 * PowerSeries.X ^ 8 : PowerSeries ℚ) := by
    linear_combination ((256) * PowerSeries.X ^ 4 + (256) * PowerSeries.X ^ 4 * T ^ 2 + (-512) * PowerSeries.X ^ 5 + (-768) * PowerSeries.X ^ 6) * hT
  have hnu0 : (256 - 1024 * PowerSeries.X - 512 * PowerSeries.X ^ 2 + 3072 * PowerSeries.X ^ 3 + 2304 * PowerSeries.X ^ 4 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    have kc : PowerSeries.constantCoeff (256 : PowerSeries ℚ) = 256 := A217539Aux.cnum 256
    simp [kc] at h'
  have hnu : (256 * PowerSeries.X ^ 4 - 1024 * PowerSeries.X ^ 5 - 512 * PowerSeries.X ^ 6 + 3072 * PowerSeries.X ^ 7 + 2304 * PowerSeries.X ^ 8 : PowerSeries ℚ) ≠ 0 := by
    have e : (256 * PowerSeries.X ^ 4 - 1024 * PowerSeries.X ^ 5 - 512 * PowerSeries.X ^ 6 + 3072 * PowerSeries.X ^ 7 + 2304 * PowerSeries.X ^ 8 : PowerSeries ℚ) = PowerSeries.X ^ 4 * (256 - 1024 * PowerSeries.X - 512 * PowerSeries.X ^ 2 + 3072 * PowerSeries.X ^ 3 + 2304 * PowerSeries.X ^ 4 : PowerSeries ℚ) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 4 PowerSeries.X_ne_zero) hnu0
  have hN1 : ((4) * PowerSeries.X * T : PowerSeries ℚ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hn
    exact hnu hn.symm
  have hM : ((4) * PowerSeries.X * T) ^ 4 * ((PowerSeries.X ^ 6 : PowerSeries ℚ) + (-1 + 8 * PowerSeries.X - 14 * PowerSeries.X ^ 2 - 20 * PowerSeries.X ^ 3 + 37 * PowerSeries.X ^ 4 + 40 * PowerSeries.X ^ 5 + 6 * PowerSeries.X ^ 6 : PowerSeries ℚ) * G ^ 2 + (PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 - 2 * PowerSeries.X ^ 4 + 12 * PowerSeries.X ^ 5 + 9 * PowerSeries.X ^ 6 : PowerSeries ℚ) * G ^ 4) = 0 := by
    linear_combination ((-16) * PowerSeries.X ^ 2 + (64) * PowerSeries.X ^ 2 * T * W + (-48) * PowerSeries.X ^ 2 * T ^ 2 + (224) * PowerSeries.X ^ 3 + (-704) * PowerSeries.X ^ 3 * T * W + (576) * PowerSeries.X ^ 3 * T ^ 2 + (-1072) * PowerSeries.X ^ 4 + (2304) * PowerSeries.X ^ 4 * T * W + (-2208) * PowerSeries.X ^ 4 * T ^ 2 + (1472) * PowerSeries.X ^ 5 + (-384) * PowerSeries.X ^ 5 * T * W + (1728) * PowerSeries.X ^ 5 * T ^ 2 + (2832) * PowerSeries.X ^ 6 + (-7872) * PowerSeries.X ^ 6 * T * W + (5584) * PowerSeries.X ^ 6 * T ^ 2 + (-6432) * PowerSeries.X ^ 7 + (1344) * PowerSeries.X ^ 7 * T * W + (-4992) * PowerSeries.X ^ 7 * T ^ 2 + (-5968) * PowerSeries.X ^ 8 + (12160) * PowerSeries.X ^ 8 * T * W + (-7552) * PowerSeries.X ^ 8 * T ^ 2 + (7808) * PowerSeries.X ^ 9 + (7936) * PowerSeries.X ^ 9 * T * W + (-1536) * PowerSeries.X ^ 9 * T ^ 2 + (11648) * PowerSeries.X ^ 10 + (1536) * PowerSeries.X ^ 10 * T * W + (256) * PowerSeries.X ^ 10 * T ^ 2 + (5120) * PowerSeries.X ^ 11 + (768) * PowerSeries.X ^ 12) * hT +
      ((96) * PowerSeries.X ^ 2 * T ^ 2 + (-64) * PowerSeries.X ^ 2 * T ^ 3 * W + (-48) * PowerSeries.X ^ 2 * T ^ 4 + (16) * PowerSeries.X ^ 2 * T ^ 4 * W ^ 2 + (-960) * PowerSeries.X ^ 3 * T ^ 2 + (448) * PowerSeries.X ^ 3 * T ^ 3 * W + (384) * PowerSeries.X ^ 3 * T ^ 4 + (-64) * PowerSeries.X ^ 3 * T ^ 4 * W ^ 2 + (2592) * PowerSeries.X ^ 4 * T ^ 2 + (-512) * PowerSeries.X ^ 4 * T ^ 3 * W + (-672) * PowerSeries.X ^ 4 * T ^ 4 + (-32) * PowerSeries.X ^ 4 * T ^ 4 * W ^ 2 + (1536) * PowerSeries.X ^ 5 * T ^ 2 + (-1664) * PowerSeries.X ^ 5 * T ^ 3 * W + (-960) * PowerSeries.X ^ 5 * T ^ 4 + (192) * PowerSeries.X ^ 5 * T ^ 4 * W ^ 2 + (-11232) * PowerSeries.X ^ 6 * T ^ 2 + (1472) * PowerSeries.X ^ 6 * T ^ 3 * W + (1744) * PowerSeries.X ^ 6 * T ^ 4 + (144) * PowerSeries.X ^ 6 * T ^ 4 * W ^ 2 + (-3264) * PowerSeries.X ^ 7 * T ^ 2 + (3264) * PowerSeries.X ^ 7 * T ^ 3 * W + (1984) * PowerSeries.X ^ 7 * T ^ 4 + (17376) * PowerSeries.X ^ 8 * T ^ 2 + (1152) * PowerSeries.X ^ 8 * T ^ 3 * W + (384) * PowerSeries.X ^ 8 * T ^ 4 + (14976) * PowerSeries.X ^ 9 * T ^ 2 + (3456) * PowerSeries.X ^ 10 * T ^ 2) * hW +
      ((8) * PowerSeries.X ^ 2 + (-24) * PowerSeries.X ^ 2 * T * W + (-32) * PowerSeries.X ^ 2 * T ^ 2 + (24) * PowerSeries.X ^ 2 * T ^ 2 * W ^ 2 + (32) * PowerSeries.X ^ 2 * T ^ 3 * W + (-8) * PowerSeries.X ^ 2 * T ^ 3 * W ^ 3 + (-104) * PowerSeries.X ^ 3 + (240) * PowerSeries.X ^ 3 * T * W + (352) * PowerSeries.X ^ 3 * T ^ 2 + (-168) * PowerSeries.X ^ 3 * T ^ 2 * W ^ 2 + (-256) * PowerSeries.X ^ 3 * T ^ 3 * W + (32) * PowerSeries.X ^ 3 * T ^ 3 * W ^ 3 + (16) * PowerSeries.X ^ 3 * G * T + (-32) * PowerSeries.X ^ 3 * G * T ^ 2 * W + (-64) * PowerSeries.X ^ 3 * G * T ^ 3 + (16) * PowerSeries.X ^ 3 * G * T ^ 3 * W ^ 2 + (440) * PowerSeries.X ^ 4 + (-648) * PowerSeries.X ^ 4 * T * W + (-1152) * PowerSeries.X ^ 4 * T ^ 2 + (192) * PowerSeries.X ^ 4 * T ^ 2 * W ^ 2 + (448) * PowerSeries.X ^ 4 * T ^ 3 * W + (16) * PowerSeries.X ^ 4 * T ^ 3 * W ^ 3 + (-160) * PowerSeries.X ^ 4 * G * T + (224) * PowerSeries.X ^ 4 * G * T ^ 2 * W + (512) * PowerSeries.X ^ 4 * G * T ^ 3 + (-64) * PowerSeries.X ^ 4 * G * T ^ 3 * W ^ 2 + (32) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 2 + (-32) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 3 * W + (-360) * PowerSeries.X ^ 5 + (-384) * PowerSeries.X ^ 5 * T * W + (192) * PowerSeries.X ^ 5 * T ^ 2 + (624) * PowerSeries.X ^ 5 * T ^ 2 * W ^ 2 + (640) * PowerSeries.X ^ 5 * T ^ 3 * W + (-96) * PowerSeries.X ^ 5 * T ^ 3 * W ^ 3 + (432) * PowerSeries.X ^ 5 * G * T + (-256) * PowerSeries.X ^ 5 * G * T ^ 2 * W + (-896) * PowerSeries.X ^ 5 * G * T ^ 3 + (-32) * PowerSeries.X ^ 5 * G * T ^ 3 * W ^ 2 + (-224) * PowerSeries.X ^ 5 * G ^ 2 * T ^ 2 + (128) * PowerSeries.X ^ 5 * G ^ 2 * T ^ 3 * W + (64) * PowerSeries.X ^ 5 * G ^ 3 * T ^ 3 + (-1752) * PowerSeries.X ^ 6 + (2808) * PowerSeries.X ^ 6 * T * W + (4000) * PowerSeries.X ^ 6 * T ^ 2 + (-552) * PowerSeries.X ^ 6 * T ^ 2 * W ^ 2 + (-1184) * PowerSeries.X ^ 6 * T ^ 3 * W + (-72) * PowerSeries.X ^ 6 * T ^ 3 * W ^ 3 + (256) * PowerSeries.X ^ 6 * G * T + (-832) * PowerSeries.X ^ 6 * G * T ^ 2 * W + (-1280) * PowerSeries.X ^ 6 * G * T ^ 3 + (192) * PowerSeries.X ^ 6 * G * T ^ 3 * W ^ 2 + (256) * PowerSeries.X ^ 6 * G ^ 2 * T ^ 2 + (64) * PowerSeries.X ^ 6 * G ^ 2 * T ^ 3 * W + (-256) * PowerSeries.X ^ 6 * G ^ 3 * T ^ 3 + (2280) * PowerSeries.X ^ 7 + (816) * PowerSeries.X ^ 7 * T * W + (-992) * PowerSeries.X ^ 7 * T ^ 2 + (-1224) * PowerSeries.X ^ 7 * T ^ 2 * W ^ 2 + (-1280) * PowerSeries.X ^ 7 * T ^ 3 * W + (-1872) * PowerSeries.X ^ 7 * G * T + (736) * PowerSeries.X ^ 7 * G * T ^ 2 * W + (2368) * PowerSeries.X ^ 7 * G * T ^ 3 + (144) * PowerSeries.X ^ 7 * G * T ^ 3 * W ^ 2 + (832) * PowerSeries.X ^ 7 * G ^ 2 * T ^ 2 + (-384) * PowerSeries.X ^ 7 * G ^ 2 * T ^ 3 * W + (-128) * PowerSeries.X ^ 7 * G ^ 3 * T ^ 3 + (4136) * PowerSeries.X ^ 8 + (-4344) * PowerSeries.X ^ 8 * T * W + (-6016) * PowerSeries.X ^ 8 * T ^ 2 + (-432) * PowerSeries.X ^ 8 * T ^ 2 * W ^ 2 + (-192) * PowerSeries.X ^ 8 * T ^ 3 * W + (-544) * PowerSeries.X ^ 8 * G * T + (1632) * PowerSeries.X ^ 8 * G * T ^ 2 * W + (2560) * PowerSeries.X ^ 8 * G * T ^ 3 + (-736) * PowerSeries.X ^ 8 * G ^ 2 * T ^ 2 + (-288) * PowerSeries.X ^ 8 * G ^ 2 * T ^ 3 * W + (768) * PowerSeries.X ^ 8 * G ^ 3 * T ^ 3 + (-2552) * PowerSeries.X ^ 9 + (-3744) * PowerSeries.X ^ 9 * T * W + (-3136) * PowerSeries.X ^ 9 * T ^ 2 + (2896) * PowerSeries.X ^ 9 * G * T + (576) * PowerSeries.X ^ 9 * G * T ^ 2 * W + (384) * PowerSeries.X ^ 9 * G * T ^ 3 + (-1632) * PowerSeries.X ^ 9 * G ^ 2 * T ^ 2 + (576) * PowerSeries.X ^ 9 * G ^ 3 * T ^ 3 + (-6352) * PowerSeries.X ^ 10 + (-864) * PowerSeries.X ^ 10 * T * W + (-384) * PowerSeries.X ^ 10 * T ^ 2 + (2496) * PowerSeries.X ^ 10 * G * T + (-576) * PowerSeries.X ^ 10 * G ^ 2 * T ^ 2 + (-3360) * PowerSeries.X ^ 11 + (576) * PowerSeries.X ^ 11 * G * T + (-576) * PowerSeries.X ^ 12) * hG
  have hP : (PowerSeries.X ^ 6 : PowerSeries ℚ) + (-1 + 8 * PowerSeries.X - 14 * PowerSeries.X ^ 2 - 20 * PowerSeries.X ^ 3 + 37 * PowerSeries.X ^ 4 + 40 * PowerSeries.X ^ 5 + 6 * PowerSeries.X ^ 6 : PowerSeries ℚ) * G ^ 2 + (PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3 - 2 * PowerSeries.X ^ 4 + 12 * PowerSeries.X ^ 5 + 9 * PowerSeries.X ^ 6 : PowerSeries ℚ) * G ^ 4 = 0 := (mul_eq_zero.mp hM).resolve_left (pow_ne_zero 4 hN1)
  cases m with
  | zero =>
    have r := A217539Aux.relE0 G hP
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A217539Aux.relE1 G hP
      push_cast
      linear_combination r
    | succ m =>
      have r := A217539Aux.rel G hP m
      push_cast
      linear_combination r

set_option maxHeartbeats 4000000 in
theorem wrap (S T c m : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X) (hS0 : coeff 0 S = 1)
    (hT : T ^ 2 = 1 - 2 * X - 3 * X ^ 2) (_hT0 : coeff 0 T = 1)
    (hc : 2 * X * c = 1 - S) (hm : 2 * X ^ 2 * m = 1 - X - T)
    (a : ℕ → ℚ) (a0 : a 0 = 0)
    (ha : ∀ n : ℕ, 1 ≤ n → a n = coeff n c - ((n : ℚ) - 1) * coeff (n - 2) m - coeff (n - 1) m) :
    ∃ G : ℚ⟦X⟧, (∀ k, coeff k G = a k) ∧
      G * (4 * X * T) = 2 * (1 - 3 * X - 2 * X ^ 2 - S * T) := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have hS0c : constantCoeff S = 1 := by simpa using hS0
  -- constant term of the Catalan series
  have h1 : X * (2 * (c * (1 + S))) = X * 4 := by linear_combination (1 + S) * hc - hS
  have h2 : 2 * (c * (1 + S)) = 4 := mul_left_cancel₀ X_ne_zero h1
  have h3 := congrArg constantCoeff h2
  have k2 : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
  have k4 : constantCoeff (4 : ℚ⟦X⟧) = 4 := cnum 4
  simp only [map_mul, map_add, map_one, hS0c, k2, k4] at h3
  have hc0 : constantCoeff c = 1 := by linarith
  -- derivative facts
  have hT2 : T * T = (1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) := by linear_combination hT
  have hPd : derivative ℚ (1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) = -2 - 6 * X := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have hTTd : derivative ℚ (T * T) = 2 * T * derivative ℚ T := by
    simp [Derivation.leibniz]
    ring
  have hdT : 2 * T * derivative ℚ T = -2 - 6 * X := by rw [← hTTd, hT2, hPd]
  have hm2 : 2 * (X * X * m) = (1 - X - T : ℚ⟦X⟧) := by linear_combination hm
  have hLd : derivative ℚ (2 * (X * X * m)) = 4 * X * m + 2 * X ^ 2 * derivative ℚ m := by
    simp [Derivation.leibniz, d2]
    ring
  have hRd : derivative ℚ (1 - X - T : ℚ⟦X⟧) = -1 - derivative ℚ T := by
    simp
  have hdm : 4 * X * m + 2 * X ^ 2 * derivative ℚ m = -1 - derivative ℚ T := by
    rw [← hLd, hm2, hRd]
  have hdXm : derivative ℚ (X * m) = m + X * derivative ℚ m := by
    simp [Derivation.leibniz]
    ring
  refine ⟨c - 1 - X ^ 2 * derivative ℚ (X * m) - X * m, ?_, ?_⟩
  · intro k
    rcases k with _ | _ | j
    · simp [hc0, a0]
    · have h := ha 1 le_rfl
      simp only [map_sub, coeff_one, coeff_X_pow_mul', coeff_succ_X_mul]
      rw [h]
      norm_num
    · have h := ha (j + 2) (by omega)
      have e1 : j + 2 - 2 = j := rfl
      have e2 : j + 2 - 1 = j + 1 := rfl
      rw [e1, e2] at h
      simp only [map_sub, coeff_one, coeff_X_pow_mul', coeff_succ_X_mul, coeff_derivative]
      rw [h]
      have e3 : j + 1 + 1 - 2 = j := rfl
      simp only [e3]
      push_cast
      norm_num
      ring
  · rw [hdXm]
    linear_combination 2 * T * hc + 2 * (X - 1) * T * hm - 2 * X ^ 2 * T * hdm + X ^ 2 * hdT +
      2 * (1 - X) * hT

end A217539Aux

theorem OMA.solution : type_of% @OMA.S_oeis_a217539.main := by
  intro S T c m hS hS0 hT hT0 hc hm a a0 ha n hn
  obtain ⟨G, hG, hG2⟩ := A217539Aux.wrap S T c m hS hS0 hT hT0 hc hm a a0 ha
  have hG0 : PowerSeries.coeff 0 G = 0 := by rw [hG, a0]
  have key := A217539Aux.gen T S G hT hT0 hS hS0 hG2 hG0 n hn
  simp only [hG] at key
  exact key
