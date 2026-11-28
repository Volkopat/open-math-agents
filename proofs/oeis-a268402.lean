import OMAStatements.S_oeis_a268402

-- Problem: A268402: Number of North-East lattice paths from (0,0) to (n,n) that bounce off the diagonal y = x to the right exactly four times.
-- Upstream: formal-conjectures statements/oeis-a268402.lean:0 (declaration OMA.S_oeis_a268402.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its first two derivatives, divided by a common
polynomial factor, is a third order equation with polynomial coefficients and polynomial right
side rho; the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A268402Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (32 - 640 * X + 5120 * X ^ 2 - 20640 * X ^ 3 + 43040 * X ^ 4 - 41920 * X ^ 5 + 13760 * X ^ 6 - 800 * X ^ 7 + (-32 + 576 * X - 4032 * X ^ 2 + 13600 * X ^ 3 - 21920 * X ^ 4 + 13952 * X ^ 5 - 2176 * X ^ 6 + 32 * X ^ 7) * S) = -32 * X ^ 3 + 224 * X ^ 4 - 448 * X ^ 5 + 224 * X ^ 6 + (32 * X ^ 3 - 160 * X ^ 4 + 192 * X ^ 5 - 32 * X ^ 6) * S) :
    (16777216 * X - 218103808 * X ^ 2 + 956301312 * X ^ 3 - 1493172224 * X ^ 4 + 1191182336 * X ^ 5 - 6559891456 * X ^ 6 + 12398362624 * X ^ 7 + 754974720 * X ^ 8 - 603979776 * X ^ 9) * derivative ℚ G + (-50331648 + 436207616 * X - 1056964608 * X ^ 2 + 1207959552 * X ^ 3 - 8573157376 * X ^ 4 + 31440502784 * X ^ 5 - 39879442432 * X ^ 6 + 16307453952 * X ^ 7 - 905969664 * X ^ 8) * G = 33554432 * X ^ 5 - 301989888 * X ^ 6 + 301989888 * X ^ 7 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d2048 : derivative ℚ (2048 : ℚ⟦X⟧) = 0 := dnum 2048
  have d4096 : derivative ℚ (4096 : ℚ⟦X⟧) = 0 := dnum 4096
  have d10240 : derivative ℚ (10240 : ℚ⟦X⟧) = 0 := dnum 10240
  have d14336 : derivative ℚ (14336 : ℚ⟦X⟧) = 0 := dnum 14336
  have d16384 : derivative ℚ (16384 : ℚ⟦X⟧) = 0 := dnum 16384
  have d18432 : derivative ℚ (18432 : ℚ⟦X⟧) = 0 := dnum 18432
  have d53248 : derivative ℚ (53248 : ℚ⟦X⟧) = 0 := dnum 53248
  have d81920 : derivative ℚ (81920 : ℚ⟦X⟧) = 0 := dnum 81920
  have d92160 : derivative ℚ (92160 : ℚ⟦X⟧) = 0 := dnum 92160
  have d112640 : derivative ℚ (112640 : ℚ⟦X⟧) = 0 := dnum 112640
  have d124928 : derivative ℚ (124928 : ℚ⟦X⟧) = 0 := dnum 124928
  have d557056 : derivative ℚ (557056 : ℚ⟦X⟧) = 0 := dnum 557056
  have d634880 : derivative ℚ (634880 : ℚ⟦X⟧) = 0 := dnum 634880
  have d2293760 : derivative ℚ (2293760 : ℚ⟦X⟧) = 0 := dnum 2293760
  have d3317760 : derivative ℚ (3317760 : ℚ⟦X⟧) = 0 := dnum 3317760
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-4096 * X ^ 5 + 81920 * X ^ 6 - 634880 * X ^ 7 + 2293760 * X ^ 8 - 3317760 * X ^ 9 - 557056 * X ^ 10 + 3317760 * X ^ 11 + 2293760 * X ^ 12 + 634880 * X ^ 13 + 81920 * X ^ 14 + 4096 * X ^ 15) * G = (2048 * X ^ 8 - 14336 * X ^ 9 + 16384 * X ^ 10 + 53248 * X ^ 11 - 112640 * X ^ 12 + 124928 * X ^ 13 - 4096 * X ^ 14 : ℚ⟦X⟧) + (-2048 * X ^ 8 + 10240 * X ^ 9 - 4096 * X ^ 10 + 4096 * X ^ 11 - 92160 * X ^ 12 + 18432 * X ^ 13) * S := by
    linear_combination (32 - 640 * X + 5120 * X ^ 2 - 20640 * X ^ 3 + 43040 * X ^ 4 - 41920 * X ^ 5 + 13760 * X ^ 6 - 800 * X ^ 7 - (-32 + 576 * X - 4032 * X ^ 2 + 13600 * X ^ 3 - 21920 * X ^ 4 + 13952 * X ^ 5 - 2176 * X ^ 6 + 32 * X ^ 7) * S) * hG + (-32 + 576 * X - 4032 * X ^ 2 + 13600 * X ^ 3 - 21920 * X ^ 4 + 13952 * X ^ 5 - 2176 * X ^ 6 + 32 * X ^ 7) * ((-32 + 576 * X - 4032 * X ^ 2 + 13600 * X ^ 3 - 21920 * X ^ 4 + 13952 * X ^ 5 - 2176 * X ^ 6 + 32 * X ^ 7) * G - (32 * X ^ 3 - 160 * X ^ 4 + 192 * X ^ 5 - 32 * X ^ 6)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-4096 * (X * X * X * X * X) + 81920 * (X * X * X * X * X * X) - 634880 * (X * X * X * X * X * X * X) + 2293760 * (X * X * X * X * X * X * X * X) - 3317760 * (X * X * X * X * X * X * X * X * X) - 557056 * (X * X * X * X * X * X * X * X * X * X) + 3317760 * (X * X * X * X * X * X * X * X * X * X * X) + 2293760 * (X * X * X * X * X * X * X * X * X * X * X * X) + 634880 * (X * X * X * X * X * X * X * X * X * X * X * X * X) + 81920 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 4096 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-20480 * X ^ 4 + 491520 * X ^ 5 - 4444160 * X ^ 6 + 18350080 * X ^ 7 - 29859840 * X ^ 8 - 5570560 * X ^ 9 + 36495360 * X ^ 10 + 27525120 * X ^ 11 + 8253440 * X ^ 12 + 1146880 * X ^ 13 + 61440 * X ^ 14) * G + (-4096 * X ^ 5 + 81920 * X ^ 6 - 634880 * X ^ 7 + 2293760 * X ^ 8 - 3317760 * X ^ 9 - 557056 * X ^ 10 + 3317760 * X ^ 11 + 2293760 * X ^ 12 + 634880 * X ^ 13 + 81920 * X ^ 14 + 4096 * X ^ 15) * derivative ℚ G := by
    simp [Derivation.leibniz, d4096, d81920, d557056, d634880, d2293760, d3317760]
    ring
  have hR : derivative ℚ ((2048 * (X * X * X * X * X * X * X * X) - 14336 * (X * X * X * X * X * X * X * X * X) + 16384 * (X * X * X * X * X * X * X * X * X * X) + 53248 * (X * X * X * X * X * X * X * X * X * X * X) - 112640 * (X * X * X * X * X * X * X * X * X * X * X * X) + 124928 * (X * X * X * X * X * X * X * X * X * X * X * X * X) - 4096 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-2048 * (X * X * X * X * X * X * X * X) + 10240 * (X * X * X * X * X * X * X * X * X) - 4096 * (X * X * X * X * X * X * X * X * X * X) + 4096 * (X * X * X * X * X * X * X * X * X * X * X) - 92160 * (X * X * X * X * X * X * X * X * X * X * X * X) + 18432 * (X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S) =
      16384 * X ^ 7 - 129024 * X ^ 8 + 163840 * X ^ 9 + 585728 * X ^ 10 - 1351680 * X ^ 11 + 1624064 * X ^ 12 - 57344 * X ^ 13 + (-16384 * X ^ 7 + 92160 * X ^ 8 - 40960 * X ^ 9 + 45056 * X ^ 10 - 1105920 * X ^ 11 + 239616 * X ^ 12) * S + (-2048 * X ^ 8 + 10240 * X ^ 9 - 4096 * X ^ 10 + 4096 * X ^ 11 - 92160 * X ^ 12 + 18432 * X ^ 13) * derivative ℚ S := by
    simp [Derivation.leibniz, d2048, d4096, d10240, d14336, d16384, d18432, d53248, d92160, d112640, d124928]
    ring
  have hk2 : (-4096 * (X * X * X * X * X) + 81920 * (X * X * X * X * X * X) - 634880 * (X * X * X * X * X * X * X) + 2293760 * (X * X * X * X * X * X * X * X) - 3317760 * (X * X * X * X * X * X * X * X * X) - 557056 * (X * X * X * X * X * X * X * X * X * X) + 3317760 * (X * X * X * X * X * X * X * X * X * X * X) + 2293760 * (X * X * X * X * X * X * X * X * X * X * X * X) + 634880 * (X * X * X * X * X * X * X * X * X * X * X * X * X) + 81920 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 4096 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (2048 * (X * X * X * X * X * X * X * X) - 14336 * (X * X * X * X * X * X * X * X * X) + 16384 * (X * X * X * X * X * X * X * X * X * X) + 53248 * (X * X * X * X * X * X * X * X * X * X * X) - 112640 * (X * X * X * X * X * X * X * X * X * X * X * X) + 124928 * (X * X * X * X * X * X * X * X * X * X * X * X * X) - 4096 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-2048 * (X * X * X * X * X * X * X * X) + 10240 * (X * X * X * X * X * X * X * X * X) - 4096 * (X * X * X * X * X * X * X * X * X * X) + 4096 * (X * X * X * X * X * X * X * X * X * X * X) - 92160 * (X * X * X * X * X * X * X * X * X * X * X * X) + 18432 * (X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-20480 * X ^ 4 + 491520 * X ^ 5 - 4444160 * X ^ 6 + 18350080 * X ^ 7 - 29859840 * X ^ 8 - 5570560 * X ^ 9 + 36495360 * X ^ 10 + 27525120 * X ^ 11 + 8253440 * X ^ 12 + 1146880 * X ^ 13 + 61440 * X ^ 14) * G + (-4096 * X ^ 5 + 81920 * X ^ 6 - 634880 * X ^ 7 + 2293760 * X ^ 8 - 3317760 * X ^ 9 - 557056 * X ^ 10 + 3317760 * X ^ 11 + 2293760 * X ^ 12 + 634880 * X ^ 13 + 81920 * X ^ 14 + 4096 * X ^ 15) * derivative ℚ G =
      16384 * X ^ 7 - 129024 * X ^ 8 + 163840 * X ^ 9 + 585728 * X ^ 10 - 1351680 * X ^ 11 + 1624064 * X ^ 12 - 57344 * X ^ 13 + (-16384 * X ^ 7 + 92160 * X ^ 8 - 40960 * X ^ 9 + 45056 * X ^ 10 - 1105920 * X ^ 11 + 239616 * X ^ 12) * S + (-2048 * X ^ 8 + 10240 * X ^ 9 - 4096 * X ^ 10 + 4096 * X ^ 11 - 92160 * X ^ 12 + 18432 * X ^ 13) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 12 * ((1 - 16 * X + 92 * X ^ 2 - 208 * X ^ 3 + 70 * X ^ 4 + 208 * X ^ 5 + 92 * X ^ 6 + 16 * X ^ 7 + X ^ 8) * ((16777216 * X - 218103808 * X ^ 2 + 956301312 * X ^ 3 - 1493172224 * X ^ 4 + 1191182336 * X ^ 5 - 6559891456 * X ^ 6 + 12398362624 * X ^ 7 + 754974720 * X ^ 8 - 603979776 * X ^ 9) * derivative ℚ G + (-50331648 + 436207616 * X - 1056964608 * X ^ 2 + 1207959552 * X ^ 3 - 8573157376 * X ^ 4 + 31440502784 * X ^ 5 - 39879442432 * X ^ 6 + 16307453952 * X ^ 7 - 905969664 * X ^ 8) * G - (33554432 * X ^ 5 - 301989888 * X ^ 6 + 301989888 * X ^ 7))) = 0 := by
    linear_combination (-2048 * X ^ 8 + 10240 * X ^ 9 - 4096 * X ^ 10 + 4096 * X ^ 11 - 92160 * X ^ 12 + 18432 * X ^ 13) ^ 2 * S * hdS - 2 * (-2048 * X ^ 8 + 10240 * X ^ 9 - 4096 * X ^ 10 + 4096 * X ^ 11 - 92160 * X ^ 12 + 18432 * X ^ 13) ^ 2 * derivative ℚ S * hS -
      (2 * (-16384 * X ^ 7 + 92160 * X ^ 8 - 40960 * X ^ 9 + 45056 * X ^ 10 - 1105920 * X ^ 11 + 239616 * X ^ 12) * (1 - 4 * X) + (-2048 * X ^ 8 + 10240 * X ^ 9 - 4096 * X ^ 10 + 4096 * X ^ 11 - 92160 * X ^ 12 + 18432 * X ^ 13) * (-4)) * hk + 2 * (-2048 * X ^ 8 + 10240 * X ^ 9 - 4096 * X ^ 10 + 4096 * X ^ 11 - 92160 * X ^ 12 + 18432 * X ^ 13) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 12 ≠ 0 := pow_ne_zero 12 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 16 * X + 92 * X ^ 2 - 208 * X ^ 3 + 70 * X ^ 4 + 208 * X ^ 5 + 92 * X ^ 6 + 16 * X ^ 7 + X ^ 8 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (32 - 640 * X + 5120 * X ^ 2 - 20640 * X ^ 3 + 43040 * X ^ 4 - 41920 * X ^ 5 + 13760 * X ^ 6 - 800 * X ^ 7 + (-32 + 576 * X - 4032 * X ^ 2 + 13600 * X ^ 3 - 21920 * X ^ 4 + 13952 * X ^ 5 - 2176 * X ^ 6 + 32 * X ^ 7) * S) = -32 * X ^ 3 + 224 * X ^ 4 - 448 * X ^ 5 + 224 * X ^ 6 + (32 * X ^ 3 - 160 * X ^ 4 + 192 * X ^ 5 - 32 * X ^ 6) * S) :
    (-55 * X ^ 3 - 55 * X ^ 4 + 3135 * X ^ 5 - 7645 * X ^ 6 - 1980 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (893 * X ^ 2 - 1170 * X ^ 3 - 9317 * X ^ 4 + 1332 * X ^ 5 - 14274 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-4766 * X + 4064 * X ^ 2 + 10720 * X ^ 3 + 24654 * X ^ 4 - 21744 * X ^ 5) * derivative ℚ G + (9270 + 332 * X - 11032 * X ^ 2 - 9336 * X ^ 3 - 5076 * X ^ 4) * G =
      0 := by
  have h := key S G hS hG
  have d16777216 : derivative ℚ (16777216 : ℚ⟦X⟧) = 0 := dnum 16777216
  have d33554432 : derivative ℚ (33554432 : ℚ⟦X⟧) = 0 := dnum 33554432
  have d50331648 : derivative ℚ (50331648 : ℚ⟦X⟧) = 0 := dnum 50331648
  have d167772160 : derivative ℚ (167772160 : ℚ⟦X⟧) = 0 := dnum 167772160
  have d218103808 : derivative ℚ (218103808 : ℚ⟦X⟧) = 0 := dnum 218103808
  have d301989888 : derivative ℚ (301989888 : ℚ⟦X⟧) = 0 := dnum 301989888
  have d436207616 : derivative ℚ (436207616 : ℚ⟦X⟧) = 0 := dnum 436207616
  have d603979776 : derivative ℚ (603979776 : ℚ⟦X⟧) = 0 := dnum 603979776
  have d754974720 : derivative ℚ (754974720 : ℚ⟦X⟧) = 0 := dnum 754974720
  have d905969664 : derivative ℚ (905969664 : ℚ⟦X⟧) = 0 := dnum 905969664
  have d956301312 : derivative ℚ (956301312 : ℚ⟦X⟧) = 0 := dnum 956301312
  have d1056964608 : derivative ℚ (1056964608 : ℚ⟦X⟧) = 0 := dnum 1056964608
  have d1191182336 : derivative ℚ (1191182336 : ℚ⟦X⟧) = 0 := dnum 1191182336
  have d1207959552 : derivative ℚ (1207959552 : ℚ⟦X⟧) = 0 := dnum 1207959552
  have d1493172224 : derivative ℚ (1493172224 : ℚ⟦X⟧) = 0 := dnum 1493172224
  have d1811939328 : derivative ℚ (1811939328 : ℚ⟦X⟧) = 0 := dnum 1811939328
  have d2113929216 : derivative ℚ (2113929216 : ℚ⟦X⟧) = 0 := dnum 2113929216
  have d2868903936 : derivative ℚ (2868903936 : ℚ⟦X⟧) = 0 := dnum 2868903936
  have d3623878656 : derivative ℚ (3623878656 : ℚ⟦X⟧) = 0 := dnum 3623878656
  have d5435817984 : derivative ℚ (5435817984 : ℚ⟦X⟧) = 0 := dnum 5435817984
  have d5955911680 : derivative ℚ (5955911680 : ℚ⟦X⟧) = 0 := dnum 5955911680
  have d5972688896 : derivative ℚ (5972688896 : ℚ⟦X⟧) = 0 := dnum 5972688896
  have d6039797760 : derivative ℚ (6039797760 : ℚ⟦X⟧) = 0 := dnum 6039797760
  have d6559891456 : derivative ℚ (6559891456 : ℚ⟦X⟧) = 0 := dnum 6559891456
  have d7247757312 : derivative ℚ (7247757312 : ℚ⟦X⟧) = 0 := dnum 7247757312
  have d8573157376 : derivative ℚ (8573157376 : ℚ⟦X⟧) = 0 := dnum 8573157376
  have d12398362624 : derivative ℚ (12398362624 : ℚ⟦X⟧) = 0 := dnum 12398362624
  have d16307453952 : derivative ℚ (16307453952 : ℚ⟦X⟧) = 0 := dnum 16307453952
  have d31440502784 : derivative ℚ (31440502784 : ℚ⟦X⟧) = 0 := dnum 31440502784
  have d34292629504 : derivative ℚ (34292629504 : ℚ⟦X⟧) = 0 := dnum 34292629504
  have d39359348736 : derivative ℚ (39359348736 : ℚ⟦X⟧) = 0 := dnum 39359348736
  have d39879442432 : derivative ℚ (39879442432 : ℚ⟦X⟧) = 0 := dnum 39879442432
  have d86788538368 : derivative ℚ (86788538368 : ℚ⟦X⟧) = 0 := dnum 86788538368
  have d114152177664 : derivative ℚ (114152177664 : ℚ⟦X⟧) = 0 := dnum 114152177664
  have d157202513920 : derivative ℚ (157202513920 : ℚ⟦X⟧) = 0 := dnum 157202513920
  have d239276654592 : derivative ℚ (239276654592 : ℚ⟦X⟧) = 0 := dnum 239276654592
  have hL : derivative ℚ ((16777216 * X - 218103808 * (X * X) + 956301312 * (X * X * X) - 1493172224 * (X * X * X * X) + 1191182336 * (X * X * X * X * X) - 6559891456 * (X * X * X * X * X * X) + 12398362624 * (X * X * X * X * X * X * X) + 754974720 * (X * X * X * X * X * X * X * X) - 603979776 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-50331648 + 436207616 * X - 1056964608 * (X * X) + 1207959552 * (X * X * X) - 8573157376 * (X * X * X * X) + 31440502784 * (X * X * X * X * X) - 39879442432 * (X * X * X * X * X * X) + 16307453952 * (X * X * X * X * X * X * X) - 905969664 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) =
      (16777216 - 436207616 * X + 2868903936 * X ^ 2 - 5972688896 * X ^ 3 + 5955911680 * X ^ 4 - 39359348736 * X ^ 5 + 86788538368 * X ^ 6 + 6039797760 * X ^ 7 - 5435817984 * X ^ 8) * derivative ℚ G + (16777216 * X - 218103808 * X ^ 2 + 956301312 * X ^ 3 - 1493172224 * X ^ 4 + 1191182336 * X ^ 5 - 6559891456 * X ^ 6 + 12398362624 * X ^ 7 + 754974720 * X ^ 8 - 603979776 * X ^ 9) * derivative ℚ (derivative ℚ G) + (436207616 - 2113929216 * X + 3623878656 * X ^ 2 - 34292629504 * X ^ 3 + 157202513920 * X ^ 4 - 239276654592 * X ^ 5 + 114152177664 * X ^ 6 - 7247757312 * X ^ 7) * G + (-50331648 + 436207616 * X - 1056964608 * X ^ 2 + 1207959552 * X ^ 3 - 8573157376 * X ^ 4 + 31440502784 * X ^ 5 - 39879442432 * X ^ 6 + 16307453952 * X ^ 7 - 905969664 * X ^ 8) * derivative ℚ G := by
    simp [Derivation.leibniz, d16777216, d50331648, d218103808, d436207616, d603979776, d754974720, d905969664, d956301312, d1056964608, d1191182336, d1207959552, d1493172224, d6559891456, d8573157376, d12398362624, d16307453952, d31440502784, d39879442432]
    ring
  have hRd : derivative ℚ (33554432 * (X * X * X * X * X) - 301989888 * (X * X * X * X * X * X) + 301989888 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) = 167772160 * X ^ 4 - 1811939328 * X ^ 5 + 2113929216 * X ^ 6 := by
    simp [Derivation.leibniz, d33554432, d301989888]
    ring
  have h2 : (16777216 * X - 218103808 * (X * X) + 956301312 * (X * X * X) - 1493172224 * (X * X * X * X) + 1191182336 * (X * X * X * X * X) - 6559891456 * (X * X * X * X * X * X) + 12398362624 * (X * X * X * X * X * X * X) + 754974720 * (X * X * X * X * X * X * X * X) - 603979776 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-50331648 + 436207616 * X - 1056964608 * (X * X) + 1207959552 * (X * X * X) - 8573157376 * (X * X * X * X) + 31440502784 * (X * X * X * X * X) - 39879442432 * (X * X * X * X * X * X) + 16307453952 * (X * X * X * X * X * X * X) - 905969664 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (33554432 * (X * X * X * X * X) - 301989888 * (X * X * X * X * X * X) + 301989888 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (16777216 - 436207616 * X + 2868903936 * X ^ 2 - 5972688896 * X ^ 3 + 5955911680 * X ^ 4 - 39359348736 * X ^ 5 + 86788538368 * X ^ 6 + 6039797760 * X ^ 7 - 5435817984 * X ^ 8) * derivative ℚ G + (16777216 * X - 218103808 * X ^ 2 + 956301312 * X ^ 3 - 1493172224 * X ^ 4 + 1191182336 * X ^ 5 - 6559891456 * X ^ 6 + 12398362624 * X ^ 7 + 754974720 * X ^ 8 - 603979776 * X ^ 9) * derivative ℚ (derivative ℚ G) + (436207616 - 2113929216 * X + 3623878656 * X ^ 2 - 34292629504 * X ^ 3 + 157202513920 * X ^ 4 - 239276654592 * X ^ 5 + 114152177664 * X ^ 6 - 7247757312 * X ^ 7) * G + (-50331648 + 436207616 * X - 1056964608 * X ^ 2 + 1207959552 * X ^ 3 - 8573157376 * X ^ 4 + 31440502784 * X ^ 5 - 39879442432 * X ^ 6 + 16307453952 * X ^ 7 - 905969664 * X ^ 8) * derivative ℚ G = 167772160 * X ^ 4 - 1811939328 * X ^ 5 + 2113929216 * X ^ 6 := by
    rw [← hL, h2, hRd]
  have hL2 : derivative ℚ ((16777216 - 436207616 * X + 2868903936 * (X * X) - 5972688896 * (X * X * X) + 5955911680 * (X * X * X * X) - 39359348736 * (X * X * X * X * X) + 86788538368 * (X * X * X * X * X * X) + 6039797760 * (X * X * X * X * X * X * X) - 5435817984 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (16777216 * X - 218103808 * (X * X) + 956301312 * (X * X * X) - 1493172224 * (X * X * X * X) + 1191182336 * (X * X * X * X * X) - 6559891456 * (X * X * X * X * X * X) + 12398362624 * (X * X * X * X * X * X * X) + 754974720 * (X * X * X * X * X * X * X * X) - 603979776 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (436207616 - 2113929216 * X + 3623878656 * (X * X) - 34292629504 * (X * X * X) + 157202513920 * (X * X * X * X) - 239276654592 * (X * X * X * X * X) + 114152177664 * (X * X * X * X * X * X) - 7247757312 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (-50331648 + 436207616 * X - 1056964608 * (X * X) + 1207959552 * (X * X * X) - 8573157376 * (X * X * X * X) + 31440502784 * (X * X * X * X * X) - 39879442432 * (X * X * X * X * X * X) + 16307453952 * (X * X * X * X * X * X * X) - 905969664 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G) =
      (436207616 + 1509949440 * X - 10670309376 * X ^ 2 - 44761612288 * X ^ 3 + 117608284160 * X ^ 4 + 42177921024 * X ^ 5 + 270582939648 * X ^ 6 - 57982058496 * X ^ 7) * derivative ℚ G + (-16777216 - 436207616 * X + 4680843264 * X ^ 2 - 10737418240 * X ^ 3 + 3338665984 * X ^ 4 - 47278194688 * X ^ 5 + 133697634304 * X ^ 6 + 28387049472 * X ^ 7 - 11777605632 * X ^ 8) * derivative ℚ (derivative ℚ G) + (16777216 * X - 218103808 * X ^ 2 + 956301312 * X ^ 3 - 1493172224 * X ^ 4 + 1191182336 * X ^ 5 - 6559891456 * X ^ 6 + 12398362624 * X ^ 7 + 754974720 * X ^ 8 - 603979776 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-2113929216 + 7247757312 * X - 102877888512 * X ^ 2 + 628810055680 * X ^ 3 - 1196383272960 * X ^ 4 + 684913065984 * X ^ 5 - 50734301184 * X ^ 6) * G := by
    simp [Derivation.leibniz, d16777216, d50331648, d218103808, d436207616, d603979776, d754974720, d905969664, d956301312, d1056964608, d1191182336, d1207959552, d1493172224, d2113929216, d2868903936, d3623878656, d5435817984, d5955911680, d5972688896, d6039797760, d6559891456, d7247757312, d8573157376, d12398362624, d16307453952, d31440502784, d34292629504, d39359348736, d39879442432, d86788538368, d114152177664, d157202513920, d239276654592]
    ring
  have hRd2 : derivative ℚ (167772160 * (X * X * X * X) - 1811939328 * (X * X * X * X * X) + 2113929216 * (X * X * X * X * X * X) : ℚ⟦X⟧) = 671088640 * X ^ 3 - 9059696640 * X ^ 4 + 12683575296 * X ^ 5 := by
    simp [Derivation.leibniz, d167772160, d1811939328, d2113929216]
    ring
  have hdp : (16777216 - 436207616 * X + 2868903936 * (X * X) - 5972688896 * (X * X * X) + 5955911680 * (X * X * X * X) - 39359348736 * (X * X * X * X * X) + 86788538368 * (X * X * X * X * X * X) + 6039797760 * (X * X * X * X * X * X * X) - 5435817984 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (16777216 * X - 218103808 * (X * X) + 956301312 * (X * X * X) - 1493172224 * (X * X * X * X) + 1191182336 * (X * X * X * X * X) - 6559891456 * (X * X * X * X * X * X) + 12398362624 * (X * X * X * X * X * X * X) + 754974720 * (X * X * X * X * X * X * X * X) - 603979776 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (436207616 - 2113929216 * X + 3623878656 * (X * X) - 34292629504 * (X * X * X) + 157202513920 * (X * X * X * X) - 239276654592 * (X * X * X * X * X) + 114152177664 * (X * X * X * X * X * X) - 7247757312 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G + (-50331648 + 436207616 * X - 1056964608 * (X * X) + 1207959552 * (X * X * X) - 8573157376 * (X * X * X * X) + 31440502784 * (X * X * X * X * X) - 39879442432 * (X * X * X * X * X * X) + 16307453952 * (X * X * X * X * X * X * X) - 905969664 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G = (167772160 * (X * X * X * X) - 1811939328 * (X * X * X * X * X) + 2113929216 * (X * X * X * X * X * X) : ℚ⟦X⟧) := by linear_combination hd
  have hd2 : (436207616 + 1509949440 * X - 10670309376 * X ^ 2 - 44761612288 * X ^ 3 + 117608284160 * X ^ 4 + 42177921024 * X ^ 5 + 270582939648 * X ^ 6 - 57982058496 * X ^ 7) * derivative ℚ G + (-16777216 - 436207616 * X + 4680843264 * X ^ 2 - 10737418240 * X ^ 3 + 3338665984 * X ^ 4 - 47278194688 * X ^ 5 + 133697634304 * X ^ 6 + 28387049472 * X ^ 7 - 11777605632 * X ^ 8) * derivative ℚ (derivative ℚ G) + (16777216 * X - 218103808 * X ^ 2 + 956301312 * X ^ 3 - 1493172224 * X ^ 4 + 1191182336 * X ^ 5 - 6559891456 * X ^ 6 + 12398362624 * X ^ 7 + 754974720 * X ^ 8 - 603979776 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-2113929216 + 7247757312 * X - 102877888512 * X ^ 2 + 628810055680 * X ^ 3 - 1196383272960 * X ^ 4 + 684913065984 * X ^ 5 - 50734301184 * X ^ 6) * G = 671088640 * X ^ 3 - 9059696640 * X ^ 4 + 12683575296 * X ^ 5 := by
    rw [← hL2, hdp, hRd2]
  have hfull : (16777216 - 167772160 * X + 486539264 * X ^ 2 - 402653184 * X ^ 3 + 1912602624 * X ^ 4 - 7985954816 * X ^ 5 + 4596957184 * X ^ 6 - 3623878656 * X ^ 7 + 34577842176 * X ^ 8 - 13589544960 * X ^ 9 + 1358954496 * X ^ 10) * ((-55 * X ^ 3 - 55 * X ^ 4 + 3135 * X ^ 5 - 7645 * X ^ 6 - 1980 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (893 * X ^ 2 - 1170 * X ^ 3 - 9317 * X ^ 4 + 1332 * X ^ 5 - 14274 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-4766 * X + 4064 * X ^ 2 + 10720 * X ^ 3 + 24654 * X ^ 4 - 21744 * X ^ 5) * derivative ℚ G + (9270 + 332 * X - 11032 * X ^ 2 - 9336 * X ^ 3 - 5076 * X ^ 4) * G - (0)) = 0 := by
    linear_combination (-55 * X ^ 2 - 220 * X ^ 3 + 2365 * X ^ 4 - 880 * X ^ 5 - 1485 * X ^ 6 - 21780 * X ^ 7 + 4455 * X ^ 8) * hd2 + (838 * X - 856 * X ^ 2 - 18624 * X ^ 3 + 7192 * X ^ 4 + 37422 * X ^ 5 + 241488 * X ^ 6 - 54756 * X ^ 7) * hd + (-3090 + 11272 * X + 37450 * X ^ 2 - 12816 * X ^ 3 - 179694 * X ^ 4 - 774360 * X ^ 5 + 196182 * X ^ 6) * h
  have hg : (16777216 - 167772160 * X + 486539264 * X ^ 2 - 402653184 * X ^ 3 + 1912602624 * X ^ 4 - 7985954816 * X ^ 5 + 4596957184 * X ^ 6 - 3623878656 * X ^ 7 + 34577842176 * X ^ 8 - 13589544960 * X ^ 9 + 1358954496 * X ^ 10 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (16777216 : ℚ⟦X⟧) = 16777216 := cnum 16777216
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (32 - 640 * X + 5120 * X ^ 2 - 20640 * X ^ 3 + 43040 * X ^ 4 - 41920 * X ^ 5 + 13760 * X ^ 6 - 800 * X ^ 7 + (-32 + 576 * X - 4032 * X ^ 2 + 13600 * X ^ 3 - 21920 * X ^ 4 + 13952 * X ^ 5 - 2176 * X ^ 6 + 32 * X ^ 7) * S) = -32 * X ^ 3 + 224 * X ^ 4 - 448 * X ^ 5 + 224 * X ^ 6 + (32 * X ^ 3 - 160 * X ^ 4 + 192 * X ^ 5 - 32 * X ^ 6) * S) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C (-55) + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-55) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C 3135 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C (-7645) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * C (-1980) + derivative ℚ (derivative ℚ G) * X * X * C 893 +
      derivative ℚ (derivative ℚ G) * X * X * X * C (-1170) + derivative ℚ (derivative ℚ G) * X * X * X * X * C (-9317) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 1332 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-14274) +
      derivative ℚ G * X * C (-4766) + derivative ℚ G * X * X * C 4064 +
      derivative ℚ G * X * X * X * C 10720 + derivative ℚ G * X * X * X * X * C 24654 +
      derivative ℚ G * X * X * X * X * X * C (-21744) + G * C 9270 +
      G * X * C 332 + G * X * X * C (-11032) +
      G * X * X * X * C (-9336) + G * X * X * X * X * C (-5076) =
      0 := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (32 - 640 * X + 5120 * X ^ 2 - 20640 * X ^ 3 + 43040 * X ^ 4 - 41920 * X ^ 5 + 13760 * X ^ 6 - 800 * X ^ 7 + (-32 + 576 * X - 4032 * X ^ 2 + 13600 * X ^ 3 - 21920 * X ^ 4 + 13952 * X ^ 5 - 2176 * X ^ 6 + 32 * X ^ 7) * S) = -32 * X ^ 3 + 224 * X ^ 4 - 448 * X ^ 5 + 224 * X ^ 6 + (32 * X ^ 3 - 160 * X ^ 4 + 192 * X ^ 5 - 32 * X ^ 6) * S) (m : ℕ) :
    (-55) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-55) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      3135 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-7645) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-1980) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + 893 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-1170) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-9317) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      1332 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-14274) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-4766) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 4064 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      10720 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 24654 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-21744) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 9270 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      332 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-11032) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-9336) * coeff (m + 1 + 1 + 1 + 1) G + (-5076) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (32 - 640 * X + 5120 * X ^ 2 - 20640 * X ^ 3 + 43040 * X ^ 4 - 41920 * X ^ 5 + 13760 * X ^ 6 - 800 * X ^ 7 + (-32 + 576 * X - 4032 * X ^ 2 + 13600 * X ^ 3 - 21920 * X ^ 4 + 13952 * X ^ 5 - 2176 * X ^ 6 + 32 * X ^ 7) * S) = -32 * X ^ 3 + 224 * X ^ 4 - 448 * X ^ 5 + 224 * X ^ 6 + (32 * X ^ 3 - 160 * X ^ 4 + 192 * X ^ 5 - 32 * X ^ 6) * S) :
    (-1320) * coeff (0 + 1 + 1 + 1 + 1) G + (-330) * coeff (0 + 1 + 1 + 1) G +
      10716 * coeff (0 + 1 + 1 + 1 + 1) G + (-7020) * coeff (0 + 1 + 1 + 1) G +
      (-18634) * coeff (0 + 1 + 1) G + (-19064) * coeff (0 + 1 + 1 + 1 + 1) G +
      12192 * coeff (0 + 1 + 1 + 1) G + 21440 * coeff (0 + 1 + 1) G +
      24654 * coeff (0 + 1) G + 9270 * coeff (0 + 1 + 1 + 1 + 1) G +
      332 * coeff (0 + 1 + 1 + 1) G + (-11032) * coeff (0 + 1 + 1) G +
      (-9336) * coeff (0 + 1) G + (-5076) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (32 - 640 * X + 5120 * X ^ 2 - 20640 * X ^ 3 + 43040 * X ^ 4 - 41920 * X ^ 5 + 13760 * X ^ 6 - 800 * X ^ 7 + (-32 + 576 * X - 4032 * X ^ 2 + 13600 * X ^ 3 - 21920 * X ^ 4 + 13952 * X ^ 5 - 2176 * X ^ 6 + 32 * X ^ 7) * S) = -32 * X ^ 3 + 224 * X ^ 4 - 448 * X ^ 5 + 224 * X ^ 6 + (32 * X ^ 3 - 160 * X ^ 4 + 192 * X ^ 5 - 32 * X ^ 6) * S) :
    (-3300) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-1320) * coeff (0 + 1 + 1 + 1 + 1) G +
      18810 * coeff (0 + 1 + 1 + 1) G + 17860 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-14040) * coeff (0 + 1 + 1 + 1 + 1) G + (-55902) * coeff (0 + 1 + 1 + 1) G +
      2664 * coeff (0 + 1 + 1) G + (-23830) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      16256 * coeff (0 + 1 + 1 + 1 + 1) G + 32160 * coeff (0 + 1 + 1 + 1) G +
      49308 * coeff (0 + 1 + 1) G + (-21744) * coeff (0 + 1) G +
      9270 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 332 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-11032) * coeff (0 + 1 + 1 + 1) G + (-9336) * coeff (0 + 1 + 1) G +
      (-5076) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (32 - 640 * X + 5120 * X ^ 2 - 20640 * X ^ 3 + 43040 * X ^ 4 - 41920 * X ^ 5 + 13760 * X ^ 6 - 800 * X ^ 7 + (-32 + 576 * X - 4032 * X ^ 2 + 13600 * X ^ 3 - 21920 * X ^ 4 + 13952 * X ^ 5 - 2176 * X ^ 6 + 32 * X ^ 7) * S) = -32 * X ^ 3 + 224 * X ^ 4 - 448 * X ^ 5 + 224 * X ^ 6 + (32 * X ^ 3 - 160 * X ^ 4 + 192 * X ^ 5 - 32 * X ^ 6) * S) :
    (-6600) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-3300) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      75240 * coeff (0 + 1 + 1 + 1 + 1) G + (-45870) * coeff (0 + 1 + 1 + 1) G +
      26790 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-23400) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-111804) * coeff (0 + 1 + 1 + 1 + 1) G + 7992 * coeff (0 + 1 + 1 + 1) G +
      (-28548) * coeff (0 + 1 + 1) G + (-28596) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      20320 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 42880 * coeff (0 + 1 + 1 + 1 + 1) G +
      73962 * coeff (0 + 1 + 1 + 1) G + (-43488) * coeff (0 + 1 + 1) G +
      9270 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 332 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-11032) * coeff (0 + 1 + 1 + 1 + 1) G + (-9336) * coeff (0 + 1 + 1 + 1) G +
      (-5076) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A268402Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a268402.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  cases m with
  | zero =>
    have r := A268402Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG - (G * ((30) + (-22) * S + (10) * S ^ 2 + (-2) * S ^ 3 + (-470) * PowerSeries.X + (278) * PowerSeries.X * S + (-90) * PowerSeries.X * S ^ 2 + (10) * PowerSeries.X * S ^ 3 + (2740) * PowerSeries.X ^ 2 + (-1220) * PowerSeries.X ^ 2 * S + (260) * PowerSeries.X ^ 2 * S ^ 2 + (-20) * PowerSeries.X ^ 2 * S ^ 3 + (-7180) * PowerSeries.X ^ 3 + (2220) * PowerSeries.X ^ 3 * S + (-340) * PowerSeries.X ^ 3 * S ^ 2 + (20) * PowerSeries.X ^ 3 * S ^ 3 + (8070) * PowerSeries.X ^ 4 + (-1790) * PowerSeries.X ^ 4 * S + (210) * PowerSeries.X ^ 4 * S ^ 2 + (-10) * PowerSeries.X ^ 4 * S ^ 3 + (-3390) * PowerSeries.X ^ 5 + (542) * PowerSeries.X ^ 5 * S + (-50) * PowerSeries.X ^ 5 * S ^ 2 + (2) * PowerSeries.X ^ 5 * S ^ 3 + (200) * PowerSeries.X ^ 6 + (-8) * PowerSeries.X ^ 6 * S) - ((-31) * PowerSeries.X ^ 3 + (26) * PowerSeries.X ^ 3 * S + (-16) * PowerSeries.X ^ 3 * S ^ 2 + (6) * PowerSeries.X ^ 3 * S ^ 3 + (-1) * PowerSeries.X ^ 3 * S ^ 4 + (98) * PowerSeries.X ^ 4 + (-46) * PowerSeries.X ^ 4 * S + (14) * PowerSeries.X ^ 4 * S ^ 2 + (-2) * PowerSeries.X ^ 4 * S ^ 3 + (-56) * PowerSeries.X ^ 5 + (8) * PowerSeries.X ^ 5 * S)) * hS)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A268402Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination hG - (G * ((30) + (-22) * S + (10) * S ^ 2 + (-2) * S ^ 3 + (-470) * PowerSeries.X + (278) * PowerSeries.X * S + (-90) * PowerSeries.X * S ^ 2 + (10) * PowerSeries.X * S ^ 3 + (2740) * PowerSeries.X ^ 2 + (-1220) * PowerSeries.X ^ 2 * S + (260) * PowerSeries.X ^ 2 * S ^ 2 + (-20) * PowerSeries.X ^ 2 * S ^ 3 + (-7180) * PowerSeries.X ^ 3 + (2220) * PowerSeries.X ^ 3 * S + (-340) * PowerSeries.X ^ 3 * S ^ 2 + (20) * PowerSeries.X ^ 3 * S ^ 3 + (8070) * PowerSeries.X ^ 4 + (-1790) * PowerSeries.X ^ 4 * S + (210) * PowerSeries.X ^ 4 * S ^ 2 + (-10) * PowerSeries.X ^ 4 * S ^ 3 + (-3390) * PowerSeries.X ^ 5 + (542) * PowerSeries.X ^ 5 * S + (-50) * PowerSeries.X ^ 5 * S ^ 2 + (2) * PowerSeries.X ^ 5 * S ^ 3 + (200) * PowerSeries.X ^ 6 + (-8) * PowerSeries.X ^ 6 * S) - ((-31) * PowerSeries.X ^ 3 + (26) * PowerSeries.X ^ 3 * S + (-16) * PowerSeries.X ^ 3 * S ^ 2 + (6) * PowerSeries.X ^ 3 * S ^ 3 + (-1) * PowerSeries.X ^ 3 * S ^ 4 + (98) * PowerSeries.X ^ 4 + (-46) * PowerSeries.X ^ 4 * S + (14) * PowerSeries.X ^ 4 * S ^ 2 + (-2) * PowerSeries.X ^ 4 * S ^ 3 + (-56) * PowerSeries.X ^ 5 + (8) * PowerSeries.X ^ 5 * S)) * hS)
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A268402Aux.relE2 (S) G (by linear_combination hS)
            (by linear_combination hG - (G * ((30) + (-22) * S + (10) * S ^ 2 + (-2) * S ^ 3 + (-470) * PowerSeries.X + (278) * PowerSeries.X * S + (-90) * PowerSeries.X * S ^ 2 + (10) * PowerSeries.X * S ^ 3 + (2740) * PowerSeries.X ^ 2 + (-1220) * PowerSeries.X ^ 2 * S + (260) * PowerSeries.X ^ 2 * S ^ 2 + (-20) * PowerSeries.X ^ 2 * S ^ 3 + (-7180) * PowerSeries.X ^ 3 + (2220) * PowerSeries.X ^ 3 * S + (-340) * PowerSeries.X ^ 3 * S ^ 2 + (20) * PowerSeries.X ^ 3 * S ^ 3 + (8070) * PowerSeries.X ^ 4 + (-1790) * PowerSeries.X ^ 4 * S + (210) * PowerSeries.X ^ 4 * S ^ 2 + (-10) * PowerSeries.X ^ 4 * S ^ 3 + (-3390) * PowerSeries.X ^ 5 + (542) * PowerSeries.X ^ 5 * S + (-50) * PowerSeries.X ^ 5 * S ^ 2 + (2) * PowerSeries.X ^ 5 * S ^ 3 + (200) * PowerSeries.X ^ 6 + (-8) * PowerSeries.X ^ 6 * S) - ((-31) * PowerSeries.X ^ 3 + (26) * PowerSeries.X ^ 3 * S + (-16) * PowerSeries.X ^ 3 * S ^ 2 + (6) * PowerSeries.X ^ 3 * S ^ 3 + (-1) * PowerSeries.X ^ 3 * S ^ 4 + (98) * PowerSeries.X ^ 4 + (-46) * PowerSeries.X ^ 4 * S + (14) * PowerSeries.X ^ 4 * S ^ 2 + (-2) * PowerSeries.X ^ 4 * S ^ 3 + (-56) * PowerSeries.X ^ 5 + (8) * PowerSeries.X ^ 5 * S)) * hS)
        push_cast
        linear_combination r
      | succ m =>
        have r := A268402Aux.rel (S) G (by linear_combination hS)
            (by linear_combination hG - (G * ((30) + (-22) * S + (10) * S ^ 2 + (-2) * S ^ 3 + (-470) * PowerSeries.X + (278) * PowerSeries.X * S + (-90) * PowerSeries.X * S ^ 2 + (10) * PowerSeries.X * S ^ 3 + (2740) * PowerSeries.X ^ 2 + (-1220) * PowerSeries.X ^ 2 * S + (260) * PowerSeries.X ^ 2 * S ^ 2 + (-20) * PowerSeries.X ^ 2 * S ^ 3 + (-7180) * PowerSeries.X ^ 3 + (2220) * PowerSeries.X ^ 3 * S + (-340) * PowerSeries.X ^ 3 * S ^ 2 + (20) * PowerSeries.X ^ 3 * S ^ 3 + (8070) * PowerSeries.X ^ 4 + (-1790) * PowerSeries.X ^ 4 * S + (210) * PowerSeries.X ^ 4 * S ^ 2 + (-10) * PowerSeries.X ^ 4 * S ^ 3 + (-3390) * PowerSeries.X ^ 5 + (542) * PowerSeries.X ^ 5 * S + (-50) * PowerSeries.X ^ 5 * S ^ 2 + (2) * PowerSeries.X ^ 5 * S ^ 3 + (200) * PowerSeries.X ^ 6 + (-8) * PowerSeries.X ^ 6 * S) - ((-31) * PowerSeries.X ^ 3 + (26) * PowerSeries.X ^ 3 * S + (-16) * PowerSeries.X ^ 3 * S ^ 2 + (6) * PowerSeries.X ^ 3 * S ^ 3 + (-1) * PowerSeries.X ^ 3 * S ^ 4 + (98) * PowerSeries.X ^ 4 + (-46) * PowerSeries.X ^ 4 * S + (14) * PowerSeries.X ^ 4 * S ^ 2 + (-2) * PowerSeries.X ^ 4 * S ^ 3 + (-56) * PowerSeries.X ^ 5 + (8) * PowerSeries.X ^ 5 * S)) * hS) m
        push_cast
        linear_combination r
