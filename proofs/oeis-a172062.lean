import OMAStatements.S_oeis_a172062

-- Problem: A172062: Expansion of (2/(3*sqrt(1-4*z)-1+4*z))*((1-sqrt(1-4*z))/(2*z))^k with k=5.
-- Upstream: formal-conjectures statements/oeis-a172062.lean:0 (declaration OMA.S_oeis_a172062.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its first two derivatives, divided by a common
polynomial factor, is a third order equation with polynomial coefficients and polynomial right
side rho; the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A172062Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-32 * X ^ 5 + 128 * X ^ 6 + (96 * X ^ 5) * S) = 32 - 160 * X + 160 * X ^ 2 + (-32 + 96 * X - 32 * X ^ 2) * S) :
    (33554432 * X - 251658240 * X ^ 2 + 436207616 * X ^ 3 + 218103808 * X ^ 4 - 301989888 * X ^ 5 - 134217728 * X ^ 6) * derivative ℚ G + (167772160 - 1174405120 * X + 1744830464 * X ^ 2 + 1207959552 * X ^ 3 - 872415232 * X ^ 4 - 469762048 * X ^ 5) * G = 167772160 + 33554432 * X := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d2048 : derivative ℚ (2048 : ℚ⟦X⟧) = 0 := dnum 2048
  have d4096 : derivative ℚ (4096 : ℚ⟦X⟧) = 0 := dnum 4096
  have d8192 : derivative ℚ (8192 : ℚ⟦X⟧) = 0 := dnum 8192
  have d12288 : derivative ℚ (12288 : ℚ⟦X⟧) = 0 := dnum 12288
  have d14336 : derivative ℚ (14336 : ℚ⟦X⟧) = 0 := dnum 14336
  have d16384 : derivative ℚ (16384 : ℚ⟦X⟧) = 0 := dnum 16384
  have d28672 : derivative ℚ (28672 : ℚ⟦X⟧) = 0 := dnum 28672
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-8192 * X ^ 10 + 28672 * X ^ 11 + 16384 * X ^ 12) * G = (2048 * X ^ 5 - 12288 * X ^ 6 + 14336 * X ^ 7 + 8192 * X ^ 8 : ℚ⟦X⟧) + (-2048 * X ^ 5 + 8192 * X ^ 6 - 2048 * X ^ 7 - 4096 * X ^ 8) * S := by
    linear_combination (-32 * X ^ 5 + 128 * X ^ 6 - (96 * X ^ 5) * S) * hG + (96 * X ^ 5) * ((96 * X ^ 5) * G - (-32 + 96 * X - 32 * X ^ 2)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-8192 * (X * X * X * X * X * X * X * X * X * X) + 28672 * (X * X * X * X * X * X * X * X * X * X * X) + 16384 * (X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-81920 * X ^ 9 + 315392 * X ^ 10 + 196608 * X ^ 11) * G + (-8192 * X ^ 10 + 28672 * X ^ 11 + 16384 * X ^ 12) * derivative ℚ G := by
    simp [Derivation.leibniz, d8192, d16384, d28672]
    ring
  have hR : derivative ℚ ((2048 * (X * X * X * X * X) - 12288 * (X * X * X * X * X * X) + 14336 * (X * X * X * X * X * X * X) + 8192 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-2048 * (X * X * X * X * X) + 8192 * (X * X * X * X * X * X) - 2048 * (X * X * X * X * X * X * X) - 4096 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S) =
      10240 * X ^ 4 - 73728 * X ^ 5 + 100352 * X ^ 6 + 65536 * X ^ 7 + (-10240 * X ^ 4 + 49152 * X ^ 5 - 14336 * X ^ 6 - 32768 * X ^ 7) * S + (-2048 * X ^ 5 + 8192 * X ^ 6 - 2048 * X ^ 7 - 4096 * X ^ 8) * derivative ℚ S := by
    simp [Derivation.leibniz, d2048, d4096, d8192, d12288, d14336]
    ring
  have hk2 : (-8192 * (X * X * X * X * X * X * X * X * X * X) + 28672 * (X * X * X * X * X * X * X * X * X * X * X) + 16384 * (X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (2048 * (X * X * X * X * X) - 12288 * (X * X * X * X * X * X) + 14336 * (X * X * X * X * X * X * X) + 8192 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-2048 * (X * X * X * X * X) + 8192 * (X * X * X * X * X * X) - 2048 * (X * X * X * X * X * X * X) - 4096 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-81920 * X ^ 9 + 315392 * X ^ 10 + 196608 * X ^ 11) * G + (-8192 * X ^ 10 + 28672 * X ^ 11 + 16384 * X ^ 12) * derivative ℚ G =
      10240 * X ^ 4 - 73728 * X ^ 5 + 100352 * X ^ 6 + 65536 * X ^ 7 + (-10240 * X ^ 4 + 49152 * X ^ 5 - 14336 * X ^ 6 - 32768 * X ^ 7) * S + (-2048 * X ^ 5 + 8192 * X ^ 6 - 2048 * X ^ 7 - 4096 * X ^ 8) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 14 * ((1 - 4 * X) * ((33554432 * X - 251658240 * X ^ 2 + 436207616 * X ^ 3 + 218103808 * X ^ 4 - 301989888 * X ^ 5 - 134217728 * X ^ 6) * derivative ℚ G + (167772160 - 1174405120 * X + 1744830464 * X ^ 2 + 1207959552 * X ^ 3 - 872415232 * X ^ 4 - 469762048 * X ^ 5) * G - (167772160 + 33554432 * X))) = 0 := by
    linear_combination (-2048 * X ^ 5 + 8192 * X ^ 6 - 2048 * X ^ 7 - 4096 * X ^ 8) ^ 2 * S * hdS - 2 * (-2048 * X ^ 5 + 8192 * X ^ 6 - 2048 * X ^ 7 - 4096 * X ^ 8) ^ 2 * derivative ℚ S * hS -
      (2 * (-10240 * X ^ 4 + 49152 * X ^ 5 - 14336 * X ^ 6 - 32768 * X ^ 7) * (1 - 4 * X) + (-2048 * X ^ 5 + 8192 * X ^ 6 - 2048 * X ^ 7 - 4096 * X ^ 8) * (-4)) * hk + 2 * (-2048 * X ^ 5 + 8192 * X ^ 6 - 2048 * X ^ 7 - 4096 * X ^ 8) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 14 ≠ 0 := pow_ne_zero 14 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 4 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-32 * X ^ 5 + 128 * X ^ 6 + (96 * X ^ 5) * S) = 32 - 160 * X + 160 * X ^ 2 + (-32 + 96 * X - 32 * X ^ 2) * S) :
    (6 * X ^ 3 - 21 * X ^ 4 - 12 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (62 * X ^ 2 - 268 * X ^ 3 - 190 * X ^ 4) * derivative ℚ (derivative ℚ G) + (120 * X - 890 * X ^ 2 - 814 * X ^ 3) * derivative ℚ G + (-720 * X - 896 * X ^ 2) * G =
      0 := by
  have h := key S G hS hG
  have d33554432 : derivative ℚ (33554432 : ℚ⟦X⟧) = 0 := dnum 33554432
  have d134217728 : derivative ℚ (134217728 : ℚ⟦X⟧) = 0 := dnum 134217728
  have d167772160 : derivative ℚ (167772160 : ℚ⟦X⟧) = 0 := dnum 167772160
  have d218103808 : derivative ℚ (218103808 : ℚ⟦X⟧) = 0 := dnum 218103808
  have d251658240 : derivative ℚ (251658240 : ℚ⟦X⟧) = 0 := dnum 251658240
  have d301989888 : derivative ℚ (301989888 : ℚ⟦X⟧) = 0 := dnum 301989888
  have d436207616 : derivative ℚ (436207616 : ℚ⟦X⟧) = 0 := dnum 436207616
  have d469762048 : derivative ℚ (469762048 : ℚ⟦X⟧) = 0 := dnum 469762048
  have d503316480 : derivative ℚ (503316480 : ℚ⟦X⟧) = 0 := dnum 503316480
  have d805306368 : derivative ℚ (805306368 : ℚ⟦X⟧) = 0 := dnum 805306368
  have d872415232 : derivative ℚ (872415232 : ℚ⟦X⟧) = 0 := dnum 872415232
  have d1174405120 : derivative ℚ (1174405120 : ℚ⟦X⟧) = 0 := dnum 1174405120
  have d1207959552 : derivative ℚ (1207959552 : ℚ⟦X⟧) = 0 := dnum 1207959552
  have d1308622848 : derivative ℚ (1308622848 : ℚ⟦X⟧) = 0 := dnum 1308622848
  have d1509949440 : derivative ℚ (1509949440 : ℚ⟦X⟧) = 0 := dnum 1509949440
  have d1744830464 : derivative ℚ (1744830464 : ℚ⟦X⟧) = 0 := dnum 1744830464
  have d2348810240 : derivative ℚ (2348810240 : ℚ⟦X⟧) = 0 := dnum 2348810240
  have d3489660928 : derivative ℚ (3489660928 : ℚ⟦X⟧) = 0 := dnum 3489660928
  have d3623878656 : derivative ℚ (3623878656 : ℚ⟦X⟧) = 0 := dnum 3623878656
  have hL : derivative ℚ ((33554432 * X - 251658240 * (X * X) + 436207616 * (X * X * X) + 218103808 * (X * X * X * X) - 301989888 * (X * X * X * X * X) - 134217728 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (167772160 - 1174405120 * X + 1744830464 * (X * X) + 1207959552 * (X * X * X) - 872415232 * (X * X * X * X) - 469762048 * (X * X * X * X * X) : ℚ⟦X⟧) * G) =
      (33554432 - 503316480 * X + 1308622848 * X ^ 2 + 872415232 * X ^ 3 - 1509949440 * X ^ 4 - 805306368 * X ^ 5) * derivative ℚ G + (33554432 * X - 251658240 * X ^ 2 + 436207616 * X ^ 3 + 218103808 * X ^ 4 - 301989888 * X ^ 5 - 134217728 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-1174405120 + 3489660928 * X + 3623878656 * X ^ 2 - 3489660928 * X ^ 3 - 2348810240 * X ^ 4) * G + (167772160 - 1174405120 * X + 1744830464 * X ^ 2 + 1207959552 * X ^ 3 - 872415232 * X ^ 4 - 469762048 * X ^ 5) * derivative ℚ G := by
    simp [Derivation.leibniz, d33554432, d134217728, d167772160, d218103808, d251658240, d301989888, d436207616, d469762048, d872415232, d1174405120, d1207959552, d1744830464]
    ring
  have hRd : derivative ℚ (167772160 + 33554432 * X : ℚ⟦X⟧) = 33554432 := by
    simp [Derivation.leibniz, d33554432, d167772160]
  have h2 : (33554432 * X - 251658240 * (X * X) + 436207616 * (X * X * X) + 218103808 * (X * X * X * X) - 301989888 * (X * X * X * X * X) - 134217728 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (167772160 - 1174405120 * X + 1744830464 * (X * X) + 1207959552 * (X * X * X) - 872415232 * (X * X * X * X) - 469762048 * (X * X * X * X * X) : ℚ⟦X⟧) * G = (167772160 + 33554432 * X : ℚ⟦X⟧) := by linear_combination h
  have hd : (33554432 - 503316480 * X + 1308622848 * X ^ 2 + 872415232 * X ^ 3 - 1509949440 * X ^ 4 - 805306368 * X ^ 5) * derivative ℚ G + (33554432 * X - 251658240 * X ^ 2 + 436207616 * X ^ 3 + 218103808 * X ^ 4 - 301989888 * X ^ 5 - 134217728 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-1174405120 + 3489660928 * X + 3623878656 * X ^ 2 - 3489660928 * X ^ 3 - 2348810240 * X ^ 4) * G + (167772160 - 1174405120 * X + 1744830464 * X ^ 2 + 1207959552 * X ^ 3 - 872415232 * X ^ 4 - 469762048 * X ^ 5) * derivative ℚ G = 33554432 := by
    rw [← hL, h2, hRd]
  have hL2 : derivative ℚ ((33554432 - 503316480 * X + 1308622848 * (X * X) + 872415232 * (X * X * X) - 1509949440 * (X * X * X * X) - 805306368 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (33554432 * X - 251658240 * (X * X) + 436207616 * (X * X * X) + 218103808 * (X * X * X * X) - 301989888 * (X * X * X * X * X) - 134217728 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-1174405120 + 3489660928 * X + 3623878656 * (X * X) - 3489660928 * (X * X * X) - 2348810240 * (X * X * X * X) : ℚ⟦X⟧) * G + (167772160 - 1174405120 * X + 1744830464 * (X * X) + 1207959552 * (X * X * X) - 872415232 * (X * X * X * X) - 469762048 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G) =
      (-2852126720 + 9596567552 * X + 9865003008 * X ^ 2 - 13019119616 * X ^ 3 - 8724152320 * X ^ 4) * derivative ℚ G + (234881024 - 2181038080 * X + 4362076160 * X ^ 2 + 2952790016 * X ^ 3 - 3892314112 * X ^ 4 - 2080374784 * X ^ 5) * derivative ℚ (derivative ℚ G) + (33554432 * X - 251658240 * X ^ 2 + 436207616 * X ^ 3 + 218103808 * X ^ 4 - 301989888 * X ^ 5 - 134217728 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (3489660928 + 7247757312 * X - 10468982784 * X ^ 2 - 9395240960 * X ^ 3) * G := by
    simp [Derivation.leibniz, d33554432, d134217728, d167772160, d218103808, d251658240, d301989888, d436207616, d469762048, d503316480, d805306368, d872415232, d1174405120, d1207959552, d1308622848, d1509949440, d1744830464, d2348810240, d3489660928, d3623878656]
    ring
  have hRd2 : derivative ℚ (33554432 : ℚ⟦X⟧) = 0 := by
    simp [d33554432]
  have hdp : (33554432 - 503316480 * X + 1308622848 * (X * X) + 872415232 * (X * X * X) - 1509949440 * (X * X * X * X) - 805306368 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (33554432 * X - 251658240 * (X * X) + 436207616 * (X * X * X) + 218103808 * (X * X * X * X) - 301989888 * (X * X * X * X * X) - 134217728 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-1174405120 + 3489660928 * X + 3623878656 * (X * X) - 3489660928 * (X * X * X) - 2348810240 * (X * X * X * X) : ℚ⟦X⟧) * G + (167772160 - 1174405120 * X + 1744830464 * (X * X) + 1207959552 * (X * X * X) - 872415232 * (X * X * X * X) - 469762048 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G = (33554432 : ℚ⟦X⟧) := by linear_combination hd
  have hd2 : (-2852126720 + 9596567552 * X + 9865003008 * X ^ 2 - 13019119616 * X ^ 3 - 8724152320 * X ^ 4) * derivative ℚ G + (234881024 - 2181038080 * X + 4362076160 * X ^ 2 + 2952790016 * X ^ 3 - 3892314112 * X ^ 4 - 2080374784 * X ^ 5) * derivative ℚ (derivative ℚ G) + (33554432 * X - 251658240 * X ^ 2 + 436207616 * X ^ 3 + 218103808 * X ^ 4 - 301989888 * X ^ 5 - 134217728 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (3489660928 + 7247757312 * X - 10468982784 * X ^ 2 - 9395240960 * X ^ 3) * G = 0 := by
    rw [← hL2, hdp, hRd2]
  have hfull : (16777216 - 134217728 * X + 301989888 * X ^ 2 - 67108864 * X ^ 3 - 251658240 * X ^ 4 + 67108864 * X ^ 5 + 67108864 * X ^ 6) * ((6 * X ^ 3 - 21 * X ^ 4 - 12 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (62 * X ^ 2 - 268 * X ^ 3 - 190 * X ^ 4) * derivative ℚ (derivative ℚ G) + (120 * X - 890 * X ^ 2 - 814 * X ^ 3) * derivative ℚ G + (-720 * X - 896 * X ^ 2) * G - (0)) = 0 := by
    linear_combination (3 * X ^ 2 - 12 * X ^ 3 + 3 * X ^ 4 + 6 * X ^ 5) * hd2 + (10 * X - 28 * X ^ 2 + 4 * X ^ 3 + 2 * X ^ 4) * hd + (-2 * X + 6 * X ^ 2 - 2 * X ^ 3) * h
  have hg : (16777216 - 134217728 * X + 301989888 * X ^ 2 - 67108864 * X ^ 3 - 251658240 * X ^ 4 + 67108864 * X ^ 5 + 67108864 * X ^ 6 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (16777216 : ℚ⟦X⟧) = 16777216 := cnum 16777216
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-32 * X ^ 5 + 128 * X ^ 6 + (96 * X ^ 5) * S) = 32 - 160 * X + 160 * X ^ 2 + (-32 + 96 * X - 32 * X ^ 2) * S) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 6 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-21) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C (-12) + derivative ℚ (derivative ℚ G) * X * X * C 62 +
      derivative ℚ (derivative ℚ G) * X * X * X * C (-268) + derivative ℚ (derivative ℚ G) * X * X * X * X * C (-190) +
      derivative ℚ G * X * C 120 + derivative ℚ G * X * X * C (-890) +
      derivative ℚ G * X * X * X * C (-814) + G * X * C (-720) +
      G * X * X * C (-896) =
      0 := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-32 * X ^ 5 + 128 * X ^ 6 + (96 * X ^ 5) * S) = 32 - 160 * X + 160 * X ^ 2 + (-32 + 96 * X - 32 * X ^ 2) * S) (m : ℕ) :
    6 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-21) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-12) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + 62 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-268) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-190) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      120 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-890) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-814) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-720) * coeff (m + 1 + 1 + 1 + 1) G +
      (-896) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-32 * X ^ 5 + 128 * X ^ 6 + (96 * X ^ 5) * S) = 32 - 160 * X + 160 * X ^ 2 + (-32 + 96 * X - 32 * X ^ 2) * S) :
    124 * coeff (0 + 1 + 1) G + 240 * coeff (0 + 1 + 1) G +
      (-890) * coeff (0 + 1) G + (-720) * coeff (0 + 1) G +
      (-896) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-32 * X ^ 5 + 128 * X ^ 6 + (96 * X ^ 5) * S) = 32 - 160 * X + 160 * X ^ 2 + (-32 + 96 * X - 32 * X ^ 2) * S) :
    36 * coeff (0 + 1 + 1 + 1) G + 372 * coeff (0 + 1 + 1 + 1) G +
      (-536) * coeff (0 + 1 + 1) G + 360 * coeff (0 + 1 + 1 + 1) G +
      (-1780) * coeff (0 + 1 + 1) G + (-814) * coeff (0 + 1) G +
      (-720) * coeff (0 + 1 + 1) G + (-896) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-32 * X ^ 5 + 128 * X ^ 6 + (96 * X ^ 5) * S) = 32 - 160 * X + 160 * X ^ 2 + (-32 + 96 * X - 32 * X ^ 2) * S) :
    144 * coeff (0 + 1 + 1 + 1 + 1) G + (-126) * coeff (0 + 1 + 1 + 1) G +
      744 * coeff (0 + 1 + 1 + 1 + 1) G + (-1608) * coeff (0 + 1 + 1 + 1) G +
      (-380) * coeff (0 + 1 + 1) G + 480 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-2670) * coeff (0 + 1 + 1 + 1) G + (-1628) * coeff (0 + 1 + 1) G +
      (-720) * coeff (0 + 1 + 1 + 1) G + (-896) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A172062Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a172062.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  cases m with
  | zero =>
    have r := A172062Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (32 * PowerSeries.X ^ 5) * hG - ((-2) + (8) * S + (-12) * S ^ 2 + (8) * S ^ 3 + (-2) * S ^ 4 + (-4 * PowerSeries.X) * c + (12 * PowerSeries.X) * c * S + (-12 * PowerSeries.X) * c * S ^ 2 + (4 * PowerSeries.X) * c * S ^ 3 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (16 * PowerSeries.X ^ 2) * c ^ 2 * S + (-8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (16 * PowerSeries.X ^ 3) * c ^ 3 * S + (-32 * PowerSeries.X ^ 4) * c ^ 4) * hc - ((-30 + 40 * PowerSeries.X) + (22 - 8 * PowerSeries.X) * S + (-10) * S ^ 2 + (2) * S ^ 3) * hS)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A172062Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination (32 * PowerSeries.X ^ 5) * hG - ((-2) + (8) * S + (-12) * S ^ 2 + (8) * S ^ 3 + (-2) * S ^ 4 + (-4 * PowerSeries.X) * c + (12 * PowerSeries.X) * c * S + (-12 * PowerSeries.X) * c * S ^ 2 + (4 * PowerSeries.X) * c * S ^ 3 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (16 * PowerSeries.X ^ 2) * c ^ 2 * S + (-8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (16 * PowerSeries.X ^ 3) * c ^ 3 * S + (-32 * PowerSeries.X ^ 4) * c ^ 4) * hc - ((-30 + 40 * PowerSeries.X) + (22 - 8 * PowerSeries.X) * S + (-10) * S ^ 2 + (2) * S ^ 3) * hS)
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A172062Aux.relE2 (S) G (by linear_combination hS)
            (by linear_combination (32 * PowerSeries.X ^ 5) * hG - ((-2) + (8) * S + (-12) * S ^ 2 + (8) * S ^ 3 + (-2) * S ^ 4 + (-4 * PowerSeries.X) * c + (12 * PowerSeries.X) * c * S + (-12 * PowerSeries.X) * c * S ^ 2 + (4 * PowerSeries.X) * c * S ^ 3 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (16 * PowerSeries.X ^ 2) * c ^ 2 * S + (-8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (16 * PowerSeries.X ^ 3) * c ^ 3 * S + (-32 * PowerSeries.X ^ 4) * c ^ 4) * hc - ((-30 + 40 * PowerSeries.X) + (22 - 8 * PowerSeries.X) * S + (-10) * S ^ 2 + (2) * S ^ 3) * hS)
        push_cast
        linear_combination r
      | succ m =>
        have r := A172062Aux.rel (S) G (by linear_combination hS)
            (by linear_combination (32 * PowerSeries.X ^ 5) * hG - ((-2) + (8) * S + (-12) * S ^ 2 + (8) * S ^ 3 + (-2) * S ^ 4 + (-4 * PowerSeries.X) * c + (12 * PowerSeries.X) * c * S + (-12 * PowerSeries.X) * c * S ^ 2 + (4 * PowerSeries.X) * c * S ^ 3 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (16 * PowerSeries.X ^ 2) * c ^ 2 * S + (-8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (16 * PowerSeries.X ^ 3) * c ^ 3 * S + (-32 * PowerSeries.X ^ 4) * c ^ 4) * hc - ((-30 + 40 * PowerSeries.X) + (22 - 8 * PowerSeries.X) * S + (-10) * S ^ 2 + (2) * S ^ 3) * hS) m
        push_cast
        linear_combination r
