import OMAStatements.S_oeis_a071264

-- Problem: A071264: Expansion of (1+x*C^4)*C^3, where C = (1-(1-4*x)^(1/2))/(2*x) is g.f. for Catalan numbers, A000108.
-- Upstream: formal-conjectures statements/oeis-a071264.lean:0 (declaration OMA.S_oeis_a071264.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its first two derivatives, divided by a common
polynomial factor, is a third order equation with polynomial coefficients and polynomial right
side rho; the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A071264Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (128 * X ^ 7 + (0) * S) = 64 * X - 448 * X ^ 2 + 896 * X ^ 3 - 384 * X ^ 4 - 192 * X ^ 5 + (-64 * X + 320 * X ^ 2 - 384 * X ^ 3 + 64 * X ^ 5) * S) :
    (-16384 * X + 147456 * X ^ 2 - 425984 * X ^ 3 + 393216 * X ^ 4 + 16384 * X ^ 5 - 65536 * X ^ 6) * derivative ℚ G + (-98304 + 770048 * X - 1867776 * X ^ 2 + 1376256 * X ^ 3 + 32768 * X ^ 4 - 98304 * X ^ 5) * G = -98304 + 311296 * X - 294912 * X ^ 2 - 49152 * X ^ 3 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d192 : derivative ℚ (192 : ℚ⟦X⟧) = 0 := dnum 192
  have d320 : derivative ℚ (320 : ℚ⟦X⟧) = 0 := dnum 320
  have d384 : derivative ℚ (384 : ℚ⟦X⟧) = 0 := dnum 384
  have d448 : derivative ℚ (448 : ℚ⟦X⟧) = 0 := dnum 448
  have d896 : derivative ℚ (896 : ℚ⟦X⟧) = 0 := dnum 896
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (128 * X ^ 7) * G = (64 * X - 448 * X ^ 2 + 896 * X ^ 3 - 384 * X ^ 4 - 192 * X ^ 5 : ℚ⟦X⟧) + (-64 * X + 320 * X ^ 2 - 384 * X ^ 3 + 64 * X ^ 5) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((128 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (896 * X ^ 6) * G + (128 * X ^ 7) * derivative ℚ G := by
    simp [Derivation.leibniz, d128]
    ring
  have hR : derivative ℚ ((64 * X - 448 * (X * X) + 896 * (X * X * X) - 384 * (X * X * X * X) - 192 * (X * X * X * X * X) : ℚ⟦X⟧) + (-64 * X + 320 * (X * X) - 384 * (X * X * X) + 64 * (X * X * X * X * X) : ℚ⟦X⟧) * S) =
      64 - 896 * X + 2688 * X ^ 2 - 1536 * X ^ 3 - 960 * X ^ 4 + (-64 + 640 * X - 1152 * X ^ 2 + 320 * X ^ 4) * S + (-64 * X + 320 * X ^ 2 - 384 * X ^ 3 + 64 * X ^ 5) * derivative ℚ S := by
    simp [Derivation.leibniz, d64, d192, d320, d384, d448, d896]
    ring
  have hk2 : (128 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (64 * X - 448 * (X * X) + 896 * (X * X * X) - 384 * (X * X * X * X) - 192 * (X * X * X * X * X) : ℚ⟦X⟧) + (-64 * X + 320 * (X * X) - 384 * (X * X * X) + 64 * (X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (896 * X ^ 6) * G + (128 * X ^ 7) * derivative ℚ G =
      64 - 896 * X + 2688 * X ^ 2 - 1536 * X ^ 3 - 960 * X ^ 4 + (-64 + 640 * X - 1152 * X ^ 2 + 320 * X ^ 4) * S + (-64 * X + 320 * X ^ 2 - 384 * X ^ 3 + 64 * X ^ 5) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 7 * ((-16384 * X + 147456 * X ^ 2 - 425984 * X ^ 3 + 393216 * X ^ 4 + 16384 * X ^ 5 - 65536 * X ^ 6) * derivative ℚ G + (-98304 + 770048 * X - 1867776 * X ^ 2 + 1376256 * X ^ 3 + 32768 * X ^ 4 - 98304 * X ^ 5) * G - (-98304 + 311296 * X - 294912 * X ^ 2 - 49152 * X ^ 3)) = 0 := by
    linear_combination (-64 * X + 320 * X ^ 2 - 384 * X ^ 3 + 64 * X ^ 5) ^ 2 * S * hdS - 2 * (-64 * X + 320 * X ^ 2 - 384 * X ^ 3 + 64 * X ^ 5) ^ 2 * derivative ℚ S * hS -
      (2 * (-64 + 640 * X - 1152 * X ^ 2 + 320 * X ^ 4) * (1 - 4 * X) + (-64 * X + 320 * X ^ 2 - 384 * X ^ 3 + 64 * X ^ 5) * (-4)) * hk + 2 * (-64 * X + 320 * X ^ 2 - 384 * X ^ 3 + 64 * X ^ 5) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 7 ≠ 0 := pow_ne_zero 7 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  linear_combination h1

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (128 * X ^ 7 + (0) * S) = 64 * X - 448 * X ^ 2 + 896 * X ^ 3 - 384 * X ^ 4 - 192 * X ^ 5 + (-64 * X + 320 * X ^ 2 - 384 * X ^ 3 + 64 * X ^ 5) * S) :
    (8587 * X ^ 3 + 8587 * X ^ 4 - 171740 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (140241 * X ^ 2 - 326438 * X ^ 3 - 1401802 * X ^ 4) * derivative ℚ (derivative ℚ G) + (562482 * X - 3342738 * X ^ 2 - 2079428 * X ^ 3) * derivative ℚ G + (370002 - 3729936 * X - 116472 * X ^ 2) * G =
      370002 := by
  have h := key S G hS hG
  have d16384 : derivative ℚ (16384 : ℚ⟦X⟧) = 0 := dnum 16384
  have d32768 : derivative ℚ (32768 : ℚ⟦X⟧) = 0 := dnum 32768
  have d49152 : derivative ℚ (49152 : ℚ⟦X⟧) = 0 := dnum 49152
  have d65536 : derivative ℚ (65536 : ℚ⟦X⟧) = 0 := dnum 65536
  have d81920 : derivative ℚ (81920 : ℚ⟦X⟧) = 0 := dnum 81920
  have d98304 : derivative ℚ (98304 : ℚ⟦X⟧) = 0 := dnum 98304
  have d131072 : derivative ℚ (131072 : ℚ⟦X⟧) = 0 := dnum 131072
  have d147456 : derivative ℚ (147456 : ℚ⟦X⟧) = 0 := dnum 147456
  have d294912 : derivative ℚ (294912 : ℚ⟦X⟧) = 0 := dnum 294912
  have d311296 : derivative ℚ (311296 : ℚ⟦X⟧) = 0 := dnum 311296
  have d393216 : derivative ℚ (393216 : ℚ⟦X⟧) = 0 := dnum 393216
  have d425984 : derivative ℚ (425984 : ℚ⟦X⟧) = 0 := dnum 425984
  have d491520 : derivative ℚ (491520 : ℚ⟦X⟧) = 0 := dnum 491520
  have d589824 : derivative ℚ (589824 : ℚ⟦X⟧) = 0 := dnum 589824
  have d770048 : derivative ℚ (770048 : ℚ⟦X⟧) = 0 := dnum 770048
  have d1277952 : derivative ℚ (1277952 : ℚ⟦X⟧) = 0 := dnum 1277952
  have d1376256 : derivative ℚ (1376256 : ℚ⟦X⟧) = 0 := dnum 1376256
  have d1572864 : derivative ℚ (1572864 : ℚ⟦X⟧) = 0 := dnum 1572864
  have d1867776 : derivative ℚ (1867776 : ℚ⟦X⟧) = 0 := dnum 1867776
  have d3735552 : derivative ℚ (3735552 : ℚ⟦X⟧) = 0 := dnum 3735552
  have d4128768 : derivative ℚ (4128768 : ℚ⟦X⟧) = 0 := dnum 4128768
  have hL : derivative ℚ ((-16384 * X + 147456 * (X * X) - 425984 * (X * X * X) + 393216 * (X * X * X * X) + 16384 * (X * X * X * X * X) - 65536 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-98304 + 770048 * X - 1867776 * (X * X) + 1376256 * (X * X * X) + 32768 * (X * X * X * X) - 98304 * (X * X * X * X * X) : ℚ⟦X⟧) * G) =
      (-16384 + 294912 * X - 1277952 * X ^ 2 + 1572864 * X ^ 3 + 81920 * X ^ 4 - 393216 * X ^ 5) * derivative ℚ G + (-16384 * X + 147456 * X ^ 2 - 425984 * X ^ 3 + 393216 * X ^ 4 + 16384 * X ^ 5 - 65536 * X ^ 6) * derivative ℚ (derivative ℚ G) + (770048 - 3735552 * X + 4128768 * X ^ 2 + 131072 * X ^ 3 - 491520 * X ^ 4) * G + (-98304 + 770048 * X - 1867776 * X ^ 2 + 1376256 * X ^ 3 + 32768 * X ^ 4 - 98304 * X ^ 5) * derivative ℚ G := by
    simp [Derivation.leibniz, d16384, d32768, d65536, d98304, d147456, d393216, d425984, d770048, d1376256, d1867776]
    ring
  have hRd : derivative ℚ (-98304 + 311296 * X - 294912 * (X * X) - 49152 * (X * X * X) : ℚ⟦X⟧) = 311296 - 589824 * X - 147456 * X ^ 2 := by
    simp [Derivation.leibniz, d49152, d98304, d294912, d311296]
    ring
  have h2 : (-16384 * X + 147456 * (X * X) - 425984 * (X * X * X) + 393216 * (X * X * X * X) + 16384 * (X * X * X * X * X) - 65536 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-98304 + 770048 * X - 1867776 * (X * X) + 1376256 * (X * X * X) + 32768 * (X * X * X * X) - 98304 * (X * X * X * X * X) : ℚ⟦X⟧) * G = (-98304 + 311296 * X - 294912 * (X * X) - 49152 * (X * X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (-16384 + 294912 * X - 1277952 * X ^ 2 + 1572864 * X ^ 3 + 81920 * X ^ 4 - 393216 * X ^ 5) * derivative ℚ G + (-16384 * X + 147456 * X ^ 2 - 425984 * X ^ 3 + 393216 * X ^ 4 + 16384 * X ^ 5 - 65536 * X ^ 6) * derivative ℚ (derivative ℚ G) + (770048 - 3735552 * X + 4128768 * X ^ 2 + 131072 * X ^ 3 - 491520 * X ^ 4) * G + (-98304 + 770048 * X - 1867776 * X ^ 2 + 1376256 * X ^ 3 + 32768 * X ^ 4 - 98304 * X ^ 5) * derivative ℚ G = 311296 - 589824 * X - 147456 * X ^ 2 := by
    rw [← hL, h2, hRd]
  have hL2 : derivative ℚ ((-16384 + 294912 * X - 1277952 * (X * X) + 1572864 * (X * X * X) + 81920 * (X * X * X * X) - 393216 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-16384 * X + 147456 * (X * X) - 425984 * (X * X * X) + 393216 * (X * X * X * X) + 16384 * (X * X * X * X * X) - 65536 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (770048 - 3735552 * X + 4128768 * (X * X) + 131072 * (X * X * X) - 491520 * (X * X * X * X) : ℚ⟦X⟧) * G + (-98304 + 770048 * X - 1867776 * (X * X) + 1376256 * (X * X * X) + 32768 * (X * X * X * X) - 98304 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G) =
      (1835008 - 10027008 * X + 12976128 * X ^ 2 + 589824 * X ^ 3 - 2949120 * X ^ 4) * derivative ℚ G + (-131072 + 1359872 * X - 4423680 * X ^ 2 + 4521984 * X ^ 3 + 196608 * X ^ 4 - 884736 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-16384 * X + 147456 * X ^ 2 - 425984 * X ^ 3 + 393216 * X ^ 4 + 16384 * X ^ 5 - 65536 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-3735552 + 8257536 * X + 393216 * X ^ 2 - 1966080 * X ^ 3) * G := by
    simp [Derivation.leibniz, d16384, d32768, d65536, d81920, d98304, d131072, d147456, d294912, d393216, d425984, d491520, d770048, d1277952, d1376256, d1572864, d1867776, d3735552, d4128768]
    ring
  have hRd2 : derivative ℚ (311296 - 589824 * X - 147456 * (X * X) : ℚ⟦X⟧) = -589824 - 294912 * X := by
    simp [Derivation.leibniz, d147456, d311296, d589824]
    ring
  have hdp : (-16384 + 294912 * X - 1277952 * (X * X) + 1572864 * (X * X * X) + 81920 * (X * X * X * X) - 393216 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-16384 * X + 147456 * (X * X) - 425984 * (X * X * X) + 393216 * (X * X * X * X) + 16384 * (X * X * X * X * X) - 65536 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (770048 - 3735552 * X + 4128768 * (X * X) + 131072 * (X * X * X) - 491520 * (X * X * X * X) : ℚ⟦X⟧) * G + (-98304 + 770048 * X - 1867776 * (X * X) + 1376256 * (X * X * X) + 32768 * (X * X * X * X) - 98304 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G = (311296 - 589824 * X - 147456 * (X * X) : ℚ⟦X⟧) := by linear_combination hd
  have hd2 : (1835008 - 10027008 * X + 12976128 * X ^ 2 + 589824 * X ^ 3 - 2949120 * X ^ 4) * derivative ℚ G + (-131072 + 1359872 * X - 4423680 * X ^ 2 + 4521984 * X ^ 3 + 196608 * X ^ 4 - 884736 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-16384 * X + 147456 * X ^ 2 - 425984 * X ^ 3 + 393216 * X ^ 4 + 16384 * X ^ 5 - 65536 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-3735552 + 8257536 * X + 393216 * X ^ 2 - 1966080 * X ^ 3) * G = -589824 - 294912 * X := by
    rw [← hL2, hdp, hRd2]
  have hfull : (16384 - 163840 * X + 606208 * X ^ 2 - 983040 * X ^ 3 + 557056 * X ^ 4 + 163840 * X ^ 5 - 196608 * X ^ 6 + 16384 * X ^ 8) * ((8587 * X ^ 3 + 8587 * X ^ 4 - 171740 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (140241 * X ^ 2 - 326438 * X ^ 3 - 1401802 * X ^ 4) * derivative ℚ (derivative ℚ G) + (562482 * X - 3342738 * X ^ 2 - 2079428 * X ^ 3) * derivative ℚ G + (370002 - 3729936 * X - 116472 * X ^ 2) * G - (370002)) = 0 := by
    linear_combination (-8587 * X ^ 2 + 163153 * X ^ 4 - 257610 * X ^ 5 + 8587 * X ^ 6 + 42935 * X ^ 7) * hd2 + (-71545 * X + 372222 * X ^ 2 - 828061 * X ^ 3 + 859812 * X ^ 4 + 37197 * X ^ 5 - 229172 * X ^ 6) * hd + (-61667 + 194832 * X + 179785 * X ^ 2 - 1006770 * X ^ 3 + 232299 * X ^ 4 + 306572 * X ^ 5) * h
  have hg : (16384 - 163840 * X + 606208 * X ^ 2 - 983040 * X ^ 3 + 557056 * X ^ 4 + 163840 * X ^ 5 - 196608 * X ^ 6 + 16384 * X ^ 8 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (16384 : ℚ⟦X⟧) = 16384 := cnum 16384
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (128 * X ^ 7 + (0) * S) = 64 * X - 448 * X ^ 2 + 896 * X ^ 3 - 384 * X ^ 4 - 192 * X ^ 5 + (-64 * X + 320 * X ^ 2 - 384 * X ^ 3 + 64 * X ^ 5) * S) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 8587 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C 8587 +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C (-171740) + derivative ℚ (derivative ℚ G) * X * X * C 140241 +
      derivative ℚ (derivative ℚ G) * X * X * X * C (-326438) + derivative ℚ (derivative ℚ G) * X * X * X * X * C (-1401802) +
      derivative ℚ G * X * C 562482 + derivative ℚ G * X * X * C (-3342738) +
      derivative ℚ G * X * X * X * C (-2079428) + G * C 370002 +
      G * X * C (-3729936) + G * X * X * C (-116472) =
      C 370002 := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (128 * X ^ 7 + (0) * S) = 64 * X - 448 * X ^ 2 + 896 * X ^ 3 - 384 * X ^ 4 - 192 * X ^ 5 + (-64 * X + 320 * X ^ 2 - 384 * X ^ 3 + 64 * X ^ 5) * S) (m : ℕ) :
    8587 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 8587 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-171740) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + 140241 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-326438) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-1401802) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      562482 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-3342738) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-2079428) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 370002 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-3729936) * coeff (m + 1 + 1 + 1 + 1) G + (-116472) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (128 * X ^ 7 + (0) * S) = 64 * X - 448 * X ^ 2 + 896 * X ^ 3 - 384 * X ^ 4 - 192 * X ^ 5 + (-64 * X + 320 * X ^ 2 - 384 * X ^ 3 + 64 * X ^ 5) * S) :
    280482 * coeff (0 + 1 + 1) G + 1124964 * coeff (0 + 1 + 1) G +
      (-3342738) * coeff (0 + 1) G + 370002 * coeff (0 + 1 + 1) G +
      (-3729936) * coeff (0 + 1) G + (-116472) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (128 * X ^ 7 + (0) * S) = 64 * X - 448 * X ^ 2 + 896 * X ^ 3 - 384 * X ^ 4 - 192 * X ^ 5 + (-64 * X + 320 * X ^ 2 - 384 * X ^ 3 + 64 * X ^ 5) * S) :
    51522 * coeff (0 + 1 + 1 + 1) G + 841446 * coeff (0 + 1 + 1 + 1) G +
      (-652876) * coeff (0 + 1 + 1) G + 1687446 * coeff (0 + 1 + 1 + 1) G +
      (-6685476) * coeff (0 + 1 + 1) G + (-2079428) * coeff (0 + 1) G +
      370002 * coeff (0 + 1 + 1 + 1) G + (-3729936) * coeff (0 + 1 + 1) G +
      (-116472) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (128 * X ^ 7 + (0) * S) = 64 * X - 448 * X ^ 2 + 896 * X ^ 3 - 384 * X ^ 4 - 192 * X ^ 5 + (-64 * X + 320 * X ^ 2 - 384 * X ^ 3 + 64 * X ^ 5) * S) :
    206088 * coeff (0 + 1 + 1 + 1 + 1) G + 51522 * coeff (0 + 1 + 1 + 1) G +
      1682892 * coeff (0 + 1 + 1 + 1 + 1) G + (-1958628) * coeff (0 + 1 + 1 + 1) G +
      (-2803604) * coeff (0 + 1 + 1) G + 2249928 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-10028214) * coeff (0 + 1 + 1 + 1) G + (-4158856) * coeff (0 + 1 + 1) G +
      370002 * coeff (0 + 1 + 1 + 1 + 1) G + (-3729936) * coeff (0 + 1 + 1 + 1) G +
      (-116472) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A071264Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a071264.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  cases m with
  | zero =>
    have r := A071264Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (128 * PowerSeries.X ^ 7) * hG - ((-PowerSeries.X - 16 * PowerSeries.X ^ 4) + (6 * PowerSeries.X + 32 * PowerSeries.X ^ 4) * S + (-15 * PowerSeries.X - 16 * PowerSeries.X ^ 4) * S ^ 2 + (20 * PowerSeries.X) * S ^ 3 + (-15 * PowerSeries.X) * S ^ 4 + (6 * PowerSeries.X) * S ^ 5 + (-PowerSeries.X) * S ^ 6 + (-2 * PowerSeries.X ^ 2 - 32 * PowerSeries.X ^ 5) * c + (10 * PowerSeries.X ^ 2 + 32 * PowerSeries.X ^ 5) * c * S + (-20 * PowerSeries.X ^ 2) * c * S ^ 2 + (20 * PowerSeries.X ^ 2) * c * S ^ 3 + (-10 * PowerSeries.X ^ 2) * c * S ^ 4 + (2 * PowerSeries.X ^ 2) * c * S ^ 5 + (-4 * PowerSeries.X ^ 3 - 64 * PowerSeries.X ^ 6) * c ^ 2 + (16 * PowerSeries.X ^ 3) * c ^ 2 * S + (-24 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 2 + (16 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 3 + (-4 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 4 + (-8 * PowerSeries.X ^ 4) * c ^ 3 + (24 * PowerSeries.X ^ 4) * c ^ 3 * S + (-24 * PowerSeries.X ^ 4) * c ^ 3 * S ^ 2 + (8 * PowerSeries.X ^ 4) * c ^ 3 * S ^ 3 + (-16 * PowerSeries.X ^ 5) * c ^ 4 + (32 * PowerSeries.X ^ 5) * c ^ 4 * S + (-16 * PowerSeries.X ^ 5) * c ^ 4 * S ^ 2 + (-32 * PowerSeries.X ^ 6) * c ^ 5 + (32 * PowerSeries.X ^ 6) * c ^ 5 * S + (-64 * PowerSeries.X ^ 7) * c ^ 6) * hc - ((-63 * PowerSeries.X + 196 * PowerSeries.X ^ 2 - 112 * PowerSeries.X ^ 3 - 48 * PowerSeries.X ^ 4) + (57 * PowerSeries.X - 92 * PowerSeries.X ^ 2 + 16 * PowerSeries.X ^ 3 + 16 * PowerSeries.X ^ 4) * S + (-42 * PowerSeries.X + 28 * PowerSeries.X ^ 2) * S ^ 2 + (22 * PowerSeries.X - 4 * PowerSeries.X ^ 2) * S ^ 3 + (-7 * PowerSeries.X) * S ^ 4 + (PowerSeries.X) * S ^ 5) * hS)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A071264Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination (128 * PowerSeries.X ^ 7) * hG - ((-PowerSeries.X - 16 * PowerSeries.X ^ 4) + (6 * PowerSeries.X + 32 * PowerSeries.X ^ 4) * S + (-15 * PowerSeries.X - 16 * PowerSeries.X ^ 4) * S ^ 2 + (20 * PowerSeries.X) * S ^ 3 + (-15 * PowerSeries.X) * S ^ 4 + (6 * PowerSeries.X) * S ^ 5 + (-PowerSeries.X) * S ^ 6 + (-2 * PowerSeries.X ^ 2 - 32 * PowerSeries.X ^ 5) * c + (10 * PowerSeries.X ^ 2 + 32 * PowerSeries.X ^ 5) * c * S + (-20 * PowerSeries.X ^ 2) * c * S ^ 2 + (20 * PowerSeries.X ^ 2) * c * S ^ 3 + (-10 * PowerSeries.X ^ 2) * c * S ^ 4 + (2 * PowerSeries.X ^ 2) * c * S ^ 5 + (-4 * PowerSeries.X ^ 3 - 64 * PowerSeries.X ^ 6) * c ^ 2 + (16 * PowerSeries.X ^ 3) * c ^ 2 * S + (-24 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 2 + (16 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 3 + (-4 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 4 + (-8 * PowerSeries.X ^ 4) * c ^ 3 + (24 * PowerSeries.X ^ 4) * c ^ 3 * S + (-24 * PowerSeries.X ^ 4) * c ^ 3 * S ^ 2 + (8 * PowerSeries.X ^ 4) * c ^ 3 * S ^ 3 + (-16 * PowerSeries.X ^ 5) * c ^ 4 + (32 * PowerSeries.X ^ 5) * c ^ 4 * S + (-16 * PowerSeries.X ^ 5) * c ^ 4 * S ^ 2 + (-32 * PowerSeries.X ^ 6) * c ^ 5 + (32 * PowerSeries.X ^ 6) * c ^ 5 * S + (-64 * PowerSeries.X ^ 7) * c ^ 6) * hc - ((-63 * PowerSeries.X + 196 * PowerSeries.X ^ 2 - 112 * PowerSeries.X ^ 3 - 48 * PowerSeries.X ^ 4) + (57 * PowerSeries.X - 92 * PowerSeries.X ^ 2 + 16 * PowerSeries.X ^ 3 + 16 * PowerSeries.X ^ 4) * S + (-42 * PowerSeries.X + 28 * PowerSeries.X ^ 2) * S ^ 2 + (22 * PowerSeries.X - 4 * PowerSeries.X ^ 2) * S ^ 3 + (-7 * PowerSeries.X) * S ^ 4 + (PowerSeries.X) * S ^ 5) * hS)
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A071264Aux.relE2 (S) G (by linear_combination hS)
            (by linear_combination (128 * PowerSeries.X ^ 7) * hG - ((-PowerSeries.X - 16 * PowerSeries.X ^ 4) + (6 * PowerSeries.X + 32 * PowerSeries.X ^ 4) * S + (-15 * PowerSeries.X - 16 * PowerSeries.X ^ 4) * S ^ 2 + (20 * PowerSeries.X) * S ^ 3 + (-15 * PowerSeries.X) * S ^ 4 + (6 * PowerSeries.X) * S ^ 5 + (-PowerSeries.X) * S ^ 6 + (-2 * PowerSeries.X ^ 2 - 32 * PowerSeries.X ^ 5) * c + (10 * PowerSeries.X ^ 2 + 32 * PowerSeries.X ^ 5) * c * S + (-20 * PowerSeries.X ^ 2) * c * S ^ 2 + (20 * PowerSeries.X ^ 2) * c * S ^ 3 + (-10 * PowerSeries.X ^ 2) * c * S ^ 4 + (2 * PowerSeries.X ^ 2) * c * S ^ 5 + (-4 * PowerSeries.X ^ 3 - 64 * PowerSeries.X ^ 6) * c ^ 2 + (16 * PowerSeries.X ^ 3) * c ^ 2 * S + (-24 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 2 + (16 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 3 + (-4 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 4 + (-8 * PowerSeries.X ^ 4) * c ^ 3 + (24 * PowerSeries.X ^ 4) * c ^ 3 * S + (-24 * PowerSeries.X ^ 4) * c ^ 3 * S ^ 2 + (8 * PowerSeries.X ^ 4) * c ^ 3 * S ^ 3 + (-16 * PowerSeries.X ^ 5) * c ^ 4 + (32 * PowerSeries.X ^ 5) * c ^ 4 * S + (-16 * PowerSeries.X ^ 5) * c ^ 4 * S ^ 2 + (-32 * PowerSeries.X ^ 6) * c ^ 5 + (32 * PowerSeries.X ^ 6) * c ^ 5 * S + (-64 * PowerSeries.X ^ 7) * c ^ 6) * hc - ((-63 * PowerSeries.X + 196 * PowerSeries.X ^ 2 - 112 * PowerSeries.X ^ 3 - 48 * PowerSeries.X ^ 4) + (57 * PowerSeries.X - 92 * PowerSeries.X ^ 2 + 16 * PowerSeries.X ^ 3 + 16 * PowerSeries.X ^ 4) * S + (-42 * PowerSeries.X + 28 * PowerSeries.X ^ 2) * S ^ 2 + (22 * PowerSeries.X - 4 * PowerSeries.X ^ 2) * S ^ 3 + (-7 * PowerSeries.X) * S ^ 4 + (PowerSeries.X) * S ^ 5) * hS)
        push_cast
        linear_combination r
      | succ m =>
        have r := A071264Aux.rel (S) G (by linear_combination hS)
            (by linear_combination (128 * PowerSeries.X ^ 7) * hG - ((-PowerSeries.X - 16 * PowerSeries.X ^ 4) + (6 * PowerSeries.X + 32 * PowerSeries.X ^ 4) * S + (-15 * PowerSeries.X - 16 * PowerSeries.X ^ 4) * S ^ 2 + (20 * PowerSeries.X) * S ^ 3 + (-15 * PowerSeries.X) * S ^ 4 + (6 * PowerSeries.X) * S ^ 5 + (-PowerSeries.X) * S ^ 6 + (-2 * PowerSeries.X ^ 2 - 32 * PowerSeries.X ^ 5) * c + (10 * PowerSeries.X ^ 2 + 32 * PowerSeries.X ^ 5) * c * S + (-20 * PowerSeries.X ^ 2) * c * S ^ 2 + (20 * PowerSeries.X ^ 2) * c * S ^ 3 + (-10 * PowerSeries.X ^ 2) * c * S ^ 4 + (2 * PowerSeries.X ^ 2) * c * S ^ 5 + (-4 * PowerSeries.X ^ 3 - 64 * PowerSeries.X ^ 6) * c ^ 2 + (16 * PowerSeries.X ^ 3) * c ^ 2 * S + (-24 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 2 + (16 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 3 + (-4 * PowerSeries.X ^ 3) * c ^ 2 * S ^ 4 + (-8 * PowerSeries.X ^ 4) * c ^ 3 + (24 * PowerSeries.X ^ 4) * c ^ 3 * S + (-24 * PowerSeries.X ^ 4) * c ^ 3 * S ^ 2 + (8 * PowerSeries.X ^ 4) * c ^ 3 * S ^ 3 + (-16 * PowerSeries.X ^ 5) * c ^ 4 + (32 * PowerSeries.X ^ 5) * c ^ 4 * S + (-16 * PowerSeries.X ^ 5) * c ^ 4 * S ^ 2 + (-32 * PowerSeries.X ^ 6) * c ^ 5 + (32 * PowerSeries.X ^ 6) * c ^ 5 * S + (-64 * PowerSeries.X ^ 7) * c ^ 6) * hc - ((-63 * PowerSeries.X + 196 * PowerSeries.X ^ 2 - 112 * PowerSeries.X ^ 3 - 48 * PowerSeries.X ^ 4) + (57 * PowerSeries.X - 92 * PowerSeries.X ^ 2 + 16 * PowerSeries.X ^ 3 + 16 * PowerSeries.X ^ 4) * S + (-42 * PowerSeries.X + 28 * PowerSeries.X ^ 2) * S ^ 2 + (22 * PowerSeries.X - 4 * PowerSeries.X ^ 2) * S ^ 3 + (-7 * PowerSeries.X) * S ^ 4 + (PowerSeries.X) * S ^ 5) * hS) m
        push_cast
        linear_combination r
