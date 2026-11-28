import OMAStatements.S_oeis_a172067

-- Problem: A172067: Expansion of (2/(3*sqrt(1-4*z)-1+4*z))*((1-sqrt(1-4*z))/(2*z))^k with k=10.
-- Upstream: formal-conjectures statements/oeis-a172067.lean:0 (declaration OMA.S_oeis_a172067.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its first two derivatives, divided by a common
polynomial factor, is a third order equation with polynomial coefficients and polynomial right
side rho; the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A172067Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-1024 * X ^ 10 + 4096 * X ^ 11 + (3072 * X ^ 10) * S) = 1024 - 10240 * X + 35840 * X ^ 2 - 51200 * X ^ 3 + 25600 * X ^ 4 - 2048 * X ^ 5 + (-1024 + 8192 * X - 21504 * X ^ 2 + 20480 * X ^ 3 - 5120 * X ^ 4) * S) :
    (35184372088832 * X - 439804651110400 * X ^ 2 + 1952732650930176 * X ^ 3 - 3377699720527872 * X ^ 4 + 826832744087552 * X ^ 5 + 2480498232262656 * X ^ 6 - 510173395288064 * X ^ 7 - 492581209243648 * X ^ 8) * derivative ℚ G + (351843720888320 - 4134163720437760 * X + 16958867346817024 * X ^ 2 - 26001250973646848 * X ^ 3 + 2603643534573568 * X ^ 4 + 18946784369836032 * X ^ 5 - 2040693581152256 * X ^ 6 - 3201777860083712 * X ^ 7) * G = 351843720888320 + 123145302310912 * X := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d2097152 : derivative ℚ (2097152 : ℚ⟦X⟧) = 0 := dnum 2097152
  have d8388608 : derivative ℚ (8388608 : ℚ⟦X⟧) = 0 := dnum 8388608
  have d10485760 : derivative ℚ (10485760 : ℚ⟦X⟧) = 0 := dnum 10485760
  have d14680064 : derivative ℚ (14680064 : ℚ⟦X⟧) = 0 := dnum 14680064
  have d16777216 : derivative ℚ (16777216 : ℚ⟦X⟧) = 0 := dnum 16777216
  have d18874368 : derivative ℚ (18874368 : ℚ⟦X⟧) = 0 := dnum 18874368
  have d23068672 : derivative ℚ (23068672 : ℚ⟦X⟧) = 0 := dnum 23068672
  have d29360128 : derivative ℚ (29360128 : ℚ⟦X⟧) = 0 := dnum 29360128
  have d31457280 : derivative ℚ (31457280 : ℚ⟦X⟧) = 0 := dnum 31457280
  have d44040192 : derivative ℚ (44040192 : ℚ⟦X⟧) = 0 := dnum 44040192
  have d48234496 : derivative ℚ (48234496 : ℚ⟦X⟧) = 0 := dnum 48234496
  have d54525952 : derivative ℚ (54525952 : ℚ⟦X⟧) = 0 := dnum 54525952
  have d88080384 : derivative ℚ (88080384 : ℚ⟦X⟧) = 0 := dnum 88080384
  have d127926272 : derivative ℚ (127926272 : ℚ⟦X⟧) = 0 := dnum 127926272
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-8388608 * X ^ 20 + 29360128 * X ^ 21 + 16777216 * X ^ 22) * G = (2097152 * X ^ 10 - 23068672 * X ^ 11 + 88080384 * X ^ 12 - 127926272 * X ^ 13 + 31457280 * X ^ 14 + 44040192 * X ^ 15 - 8388608 * X ^ 16 : ℚ⟦X⟧) + (-2097152 * X ^ 10 + 18874368 * X ^ 11 - 54525952 * X ^ 12 + 48234496 * X ^ 13 + 10485760 * X ^ 14 - 14680064 * X ^ 15) * S := by
    linear_combination (-1024 * X ^ 10 + 4096 * X ^ 11 - (3072 * X ^ 10) * S) * hG + (3072 * X ^ 10) * ((3072 * X ^ 10) * G - (-1024 + 8192 * X - 21504 * X ^ 2 + 20480 * X ^ 3 - 5120 * X ^ 4)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-8388608 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 29360128 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 16777216 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-167772160 * X ^ 19 + 616562688 * X ^ 20 + 369098752 * X ^ 21) * G + (-8388608 * X ^ 20 + 29360128 * X ^ 21 + 16777216 * X ^ 22) * derivative ℚ G := by
    simp [Derivation.leibniz, d8388608, d16777216, d29360128]
    ring
  have hR : derivative ℚ ((2097152 * (X * X * X * X * X * X * X * X * X * X) - 23068672 * (X * X * X * X * X * X * X * X * X * X * X) + 88080384 * (X * X * X * X * X * X * X * X * X * X * X * X) - 127926272 * (X * X * X * X * X * X * X * X * X * X * X * X * X) + 31457280 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 44040192 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) - 8388608 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-2097152 * (X * X * X * X * X * X * X * X * X * X) + 18874368 * (X * X * X * X * X * X * X * X * X * X * X) - 54525952 * (X * X * X * X * X * X * X * X * X * X * X * X) + 48234496 * (X * X * X * X * X * X * X * X * X * X * X * X * X) + 10485760 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X) - 14680064 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S) =
      20971520 * X ^ 9 - 253755392 * X ^ 10 + 1056964608 * X ^ 11 - 1663041536 * X ^ 12 + 440401920 * X ^ 13 + 660602880 * X ^ 14 - 134217728 * X ^ 15 + (-20971520 * X ^ 9 + 207618048 * X ^ 10 - 654311424 * X ^ 11 + 627048448 * X ^ 12 + 146800640 * X ^ 13 - 220200960 * X ^ 14) * S + (-2097152 * X ^ 10 + 18874368 * X ^ 11 - 54525952 * X ^ 12 + 48234496 * X ^ 13 + 10485760 * X ^ 14 - 14680064 * X ^ 15) * derivative ℚ S := by
    simp [Derivation.leibniz, d2097152, d8388608, d10485760, d14680064, d18874368, d23068672, d31457280, d44040192, d48234496, d54525952, d88080384, d127926272]
    ring
  have hk2 : (-8388608 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 29360128 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 16777216 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (2097152 * (X * X * X * X * X * X * X * X * X * X) - 23068672 * (X * X * X * X * X * X * X * X * X * X * X) + 88080384 * (X * X * X * X * X * X * X * X * X * X * X * X) - 127926272 * (X * X * X * X * X * X * X * X * X * X * X * X * X) + 31457280 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X) + 44040192 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) - 8388608 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-2097152 * (X * X * X * X * X * X * X * X * X * X) + 18874368 * (X * X * X * X * X * X * X * X * X * X * X) - 54525952 * (X * X * X * X * X * X * X * X * X * X * X * X) + 48234496 * (X * X * X * X * X * X * X * X * X * X * X * X * X) + 10485760 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X) - 14680064 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-167772160 * X ^ 19 + 616562688 * X ^ 20 + 369098752 * X ^ 21) * G + (-8388608 * X ^ 20 + 29360128 * X ^ 21 + 16777216 * X ^ 22) * derivative ℚ G =
      20971520 * X ^ 9 - 253755392 * X ^ 10 + 1056964608 * X ^ 11 - 1663041536 * X ^ 12 + 440401920 * X ^ 13 + 660602880 * X ^ 14 - 134217728 * X ^ 15 + (-20971520 * X ^ 9 + 207618048 * X ^ 10 - 654311424 * X ^ 11 + 627048448 * X ^ 12 + 146800640 * X ^ 13 - 220200960 * X ^ 14) * S + (-2097152 * X ^ 10 + 18874368 * X ^ 11 - 54525952 * X ^ 12 + 48234496 * X ^ 13 + 10485760 * X ^ 14 - 14680064 * X ^ 15) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 29 * ((1 - 4 * X) * ((35184372088832 * X - 439804651110400 * X ^ 2 + 1952732650930176 * X ^ 3 - 3377699720527872 * X ^ 4 + 826832744087552 * X ^ 5 + 2480498232262656 * X ^ 6 - 510173395288064 * X ^ 7 - 492581209243648 * X ^ 8) * derivative ℚ G + (351843720888320 - 4134163720437760 * X + 16958867346817024 * X ^ 2 - 26001250973646848 * X ^ 3 + 2603643534573568 * X ^ 4 + 18946784369836032 * X ^ 5 - 2040693581152256 * X ^ 6 - 3201777860083712 * X ^ 7) * G - (351843720888320 + 123145302310912 * X))) = 0 := by
    linear_combination (-2097152 * X ^ 10 + 18874368 * X ^ 11 - 54525952 * X ^ 12 + 48234496 * X ^ 13 + 10485760 * X ^ 14 - 14680064 * X ^ 15) ^ 2 * S * hdS - 2 * (-2097152 * X ^ 10 + 18874368 * X ^ 11 - 54525952 * X ^ 12 + 48234496 * X ^ 13 + 10485760 * X ^ 14 - 14680064 * X ^ 15) ^ 2 * derivative ℚ S * hS -
      (2 * (-20971520 * X ^ 9 + 207618048 * X ^ 10 - 654311424 * X ^ 11 + 627048448 * X ^ 12 + 146800640 * X ^ 13 - 220200960 * X ^ 14) * (1 - 4 * X) + (-2097152 * X ^ 10 + 18874368 * X ^ 11 - 54525952 * X ^ 12 + 48234496 * X ^ 13 + 10485760 * X ^ 14 - 14680064 * X ^ 15) * (-4)) * hk + 2 * (-2097152 * X ^ 10 + 18874368 * X ^ 11 - 54525952 * X ^ 12 + 48234496 * X ^ 13 + 10485760 * X ^ 14 - 14680064 * X ^ 15) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 29 ≠ 0 := pow_ne_zero 29 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 4 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-1024 * X ^ 10 + 4096 * X ^ 11 + (3072 * X ^ 10) * S) = 1024 - 10240 * X + 35840 * X ^ 2 - 51200 * X ^ 3 + 25600 * X ^ 4 - 2048 * X ^ 5 + (-1024 + 8192 * X - 21504 * X ^ 2 + 20480 * X ^ 3 - 5120 * X ^ 4) * S) :
    (6 * X ^ 3 - 21 * X ^ 4 - 12 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (112 * X ^ 2 - 443 * X ^ 3 - 290 * X ^ 4) * derivative ℚ (derivative ℚ G) + (440 * X - 2720 * X ^ 2 - 2034 * X ^ 3) * derivative ℚ G + (-4840 * X - 4056 * X ^ 2) * G =
      0 := by
  have h := key S G hS hG
  have d35184372088832 : derivative ℚ (35184372088832 : ℚ⟦X⟧) = 0 := dnum 35184372088832
  have d123145302310912 : derivative ℚ (123145302310912 : ℚ⟦X⟧) = 0 := dnum 123145302310912
  have d351843720888320 : derivative ℚ (351843720888320 : ℚ⟦X⟧) = 0 := dnum 351843720888320
  have d439804651110400 : derivative ℚ (439804651110400 : ℚ⟦X⟧) = 0 := dnum 439804651110400
  have d492581209243648 : derivative ℚ (492581209243648 : ℚ⟦X⟧) = 0 := dnum 492581209243648
  have d510173395288064 : derivative ℚ (510173395288064 : ℚ⟦X⟧) = 0 := dnum 510173395288064
  have d826832744087552 : derivative ℚ (826832744087552 : ℚ⟦X⟧) = 0 := dnum 826832744087552
  have d879609302220800 : derivative ℚ (879609302220800 : ℚ⟦X⟧) = 0 := dnum 879609302220800
  have d1952732650930176 : derivative ℚ (1952732650930176 : ℚ⟦X⟧) = 0 := dnum 1952732650930176
  have d2040693581152256 : derivative ℚ (2040693581152256 : ℚ⟦X⟧) = 0 := dnum 2040693581152256
  have d2480498232262656 : derivative ℚ (2480498232262656 : ℚ⟦X⟧) = 0 := dnum 2480498232262656
  have d2603643534573568 : derivative ℚ (2603643534573568 : ℚ⟦X⟧) = 0 := dnum 2603643534573568
  have d3201777860083712 : derivative ℚ (3201777860083712 : ℚ⟦X⟧) = 0 := dnum 3201777860083712
  have d3377699720527872 : derivative ℚ (3377699720527872 : ℚ⟦X⟧) = 0 := dnum 3377699720527872
  have d3571213767016448 : derivative ℚ (3571213767016448 : ℚ⟦X⟧) = 0 := dnum 3571213767016448
  have d3940649673949184 : derivative ℚ (3940649673949184 : ℚ⟦X⟧) = 0 := dnum 3940649673949184
  have d4134163720437760 : derivative ℚ (4134163720437760 : ℚ⟦X⟧) = 0 := dnum 4134163720437760
  have d5858197952790528 : derivative ℚ (5858197952790528 : ℚ⟦X⟧) = 0 := dnum 5858197952790528
  have d10414574138294272 : derivative ℚ (10414574138294272 : ℚ⟦X⟧) = 0 := dnum 10414574138294272
  have d12244161486913536 : derivative ℚ (12244161486913536 : ℚ⟦X⟧) = 0 := dnum 12244161486913536
  have d13510798882111488 : derivative ℚ (13510798882111488 : ℚ⟦X⟧) = 0 := dnum 13510798882111488
  have d14882989393575936 : derivative ℚ (14882989393575936 : ℚ⟦X⟧) = 0 := dnum 14882989393575936
  have d16958867346817024 : derivative ℚ (16958867346817024 : ℚ⟦X⟧) = 0 := dnum 16958867346817024
  have d18946784369836032 : derivative ℚ (18946784369836032 : ℚ⟦X⟧) = 0 := dnum 18946784369836032
  have d22412445020585984 : derivative ℚ (22412445020585984 : ℚ⟦X⟧) = 0 := dnum 22412445020585984
  have d26001250973646848 : derivative ℚ (26001250973646848 : ℚ⟦X⟧) = 0 := dnum 26001250973646848
  have d33917734693634048 : derivative ℚ (33917734693634048 : ℚ⟦X⟧) = 0 := dnum 33917734693634048
  have d78003752920940544 : derivative ℚ (78003752920940544 : ℚ⟦X⟧) = 0 := dnum 78003752920940544
  have d94733921849180160 : derivative ℚ (94733921849180160 : ℚ⟦X⟧) = 0 := dnum 94733921849180160
  have hL : derivative ℚ ((35184372088832 * X - 439804651110400 * (X * X) + 1952732650930176 * (X * X * X) - 3377699720527872 * (X * X * X * X) + 826832744087552 * (X * X * X * X * X) + 2480498232262656 * (X * X * X * X * X * X) - 510173395288064 * (X * X * X * X * X * X * X) - 492581209243648 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (351843720888320 - 4134163720437760 * X + 16958867346817024 * (X * X) - 26001250973646848 * (X * X * X) + 2603643534573568 * (X * X * X * X) + 18946784369836032 * (X * X * X * X * X) - 2040693581152256 * (X * X * X * X * X * X) - 3201777860083712 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) =
      (35184372088832 - 879609302220800 * X + 5858197952790528 * X ^ 2 - 13510798882111488 * X ^ 3 + 4134163720437760 * X ^ 4 + 14882989393575936 * X ^ 5 - 3571213767016448 * X ^ 6 - 3940649673949184 * X ^ 7) * derivative ℚ G + (35184372088832 * X - 439804651110400 * X ^ 2 + 1952732650930176 * X ^ 3 - 3377699720527872 * X ^ 4 + 826832744087552 * X ^ 5 + 2480498232262656 * X ^ 6 - 510173395288064 * X ^ 7 - 492581209243648 * X ^ 8) * derivative ℚ (derivative ℚ G) + (-4134163720437760 + 33917734693634048 * X - 78003752920940544 * X ^ 2 + 10414574138294272 * X ^ 3 + 94733921849180160 * X ^ 4 - 12244161486913536 * X ^ 5 - 22412445020585984 * X ^ 6) * G + (351843720888320 - 4134163720437760 * X + 16958867346817024 * X ^ 2 - 26001250973646848 * X ^ 3 + 2603643534573568 * X ^ 4 + 18946784369836032 * X ^ 5 - 2040693581152256 * X ^ 6 - 3201777860083712 * X ^ 7) * derivative ℚ G := by
    simp [Derivation.leibniz, d35184372088832, d351843720888320, d439804651110400, d492581209243648, d510173395288064, d826832744087552, d1952732650930176, d2040693581152256, d2480498232262656, d2603643534573568, d3201777860083712, d3377699720527872, d4134163720437760, d16958867346817024, d18946784369836032, d26001250973646848]
    ring
  have hRd : derivative ℚ (351843720888320 + 123145302310912 * X : ℚ⟦X⟧) = 123145302310912 := by
    simp [Derivation.leibniz, d123145302310912, d351843720888320]
  have h2 : (35184372088832 * X - 439804651110400 * (X * X) + 1952732650930176 * (X * X * X) - 3377699720527872 * (X * X * X * X) + 826832744087552 * (X * X * X * X * X) + 2480498232262656 * (X * X * X * X * X * X) - 510173395288064 * (X * X * X * X * X * X * X) - 492581209243648 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (351843720888320 - 4134163720437760 * X + 16958867346817024 * (X * X) - 26001250973646848 * (X * X * X) + 2603643534573568 * (X * X * X * X) + 18946784369836032 * (X * X * X * X * X) - 2040693581152256 * (X * X * X * X * X * X) - 3201777860083712 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (351843720888320 + 123145302310912 * X : ℚ⟦X⟧) := by linear_combination h
  have hd : (35184372088832 - 879609302220800 * X + 5858197952790528 * X ^ 2 - 13510798882111488 * X ^ 3 + 4134163720437760 * X ^ 4 + 14882989393575936 * X ^ 5 - 3571213767016448 * X ^ 6 - 3940649673949184 * X ^ 7) * derivative ℚ G + (35184372088832 * X - 439804651110400 * X ^ 2 + 1952732650930176 * X ^ 3 - 3377699720527872 * X ^ 4 + 826832744087552 * X ^ 5 + 2480498232262656 * X ^ 6 - 510173395288064 * X ^ 7 - 492581209243648 * X ^ 8) * derivative ℚ (derivative ℚ G) + (-4134163720437760 + 33917734693634048 * X - 78003752920940544 * X ^ 2 + 10414574138294272 * X ^ 3 + 94733921849180160 * X ^ 4 - 12244161486913536 * X ^ 5 - 22412445020585984 * X ^ 6) * G + (351843720888320 - 4134163720437760 * X + 16958867346817024 * X ^ 2 - 26001250973646848 * X ^ 3 + 2603643534573568 * X ^ 4 + 18946784369836032 * X ^ 5 - 2040693581152256 * X ^ 6 - 3201777860083712 * X ^ 7) * derivative ℚ G = 123145302310912 := by
    rw [← hL, h2, hRd]
  have hL2 : derivative ℚ ((35184372088832 - 879609302220800 * X + 5858197952790528 * (X * X) - 13510798882111488 * (X * X * X) + 4134163720437760 * (X * X * X * X) + 14882989393575936 * (X * X * X * X * X) - 3571213767016448 * (X * X * X * X * X * X) - 3940649673949184 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (35184372088832 * X - 439804651110400 * (X * X) + 1952732650930176 * (X * X * X) - 3377699720527872 * (X * X * X * X) + 826832744087552 * (X * X * X * X * X) + 2480498232262656 * (X * X * X * X * X * X) - 510173395288064 * (X * X * X * X * X * X * X) - 492581209243648 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-4134163720437760 + 33917734693634048 * X - 78003752920940544 * (X * X) + 10414574138294272 * (X * X * X) + 94733921849180160 * (X * X * X * X) - 12244161486913536 * (X * X * X * X * X) - 22412445020585984 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G + (351843720888320 - 4134163720437760 * X + 16958867346817024 * (X * X) - 26001250973646848 * (X * X * X) + 2603643534573568 * (X * X * X * X) + 18946784369836032 * (X * X * X * X * X) - 2040693581152256 * (X * X * X * X * X * X) - 3201777860083712 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G) =
      (-9147936743096320 + 79551865292849152 * X - 196539902488215552 * X ^ 2 + 37365803158339584 * X ^ 3 + 263882790666240000 * X ^ 4 - 45915605575925760 * X ^ 5 - 72409437758816256 * X ^ 6) * derivative ℚ G + (422212465065984 - 5893382324879360 * X + 28675263252398080 * X ^ 2 - 53022848737869824 * X ^ 3 + 10871970975449088 * X ^ 4 + 48712763156987904 * X ^ 5 - 9183121115185152 * X ^ 6 - 11083077207982080 * X ^ 7) * derivative ℚ (derivative ℚ G) + (35184372088832 * X - 439804651110400 * X ^ 2 + 1952732650930176 * X ^ 3 - 3377699720527872 * X ^ 4 + 826832744087552 * X ^ 5 + 2480498232262656 * X ^ 6 - 510173395288064 * X ^ 7 - 492581209243648 * X ^ 8) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (33917734693634048 - 156007505841881088 * X + 31243722414882816 * X ^ 2 + 378935687396720640 * X ^ 3 - 61220807434567680 * X ^ 4 - 134474670123515904 * X ^ 5) * G := by
    simp [Derivation.leibniz, d35184372088832, d351843720888320, d439804651110400, d492581209243648, d510173395288064, d826832744087552, d879609302220800, d1952732650930176, d2040693581152256, d2480498232262656, d2603643534573568, d3201777860083712, d3377699720527872, d3571213767016448, d3940649673949184, d4134163720437760, d5858197952790528, d10414574138294272, d12244161486913536, d13510798882111488, d14882989393575936, d16958867346817024, d18946784369836032, d22412445020585984, d26001250973646848, d33917734693634048, d78003752920940544, d94733921849180160]
    ring
  have hRd2 : derivative ℚ (123145302310912 : ℚ⟦X⟧) = 0 := by
    simp [d123145302310912]
  have hdp : (35184372088832 - 879609302220800 * X + 5858197952790528 * (X * X) - 13510798882111488 * (X * X * X) + 4134163720437760 * (X * X * X * X) + 14882989393575936 * (X * X * X * X * X) - 3571213767016448 * (X * X * X * X * X * X) - 3940649673949184 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (35184372088832 * X - 439804651110400 * (X * X) + 1952732650930176 * (X * X * X) - 3377699720527872 * (X * X * X * X) + 826832744087552 * (X * X * X * X * X) + 2480498232262656 * (X * X * X * X * X * X) - 510173395288064 * (X * X * X * X * X * X * X) - 492581209243648 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-4134163720437760 + 33917734693634048 * X - 78003752920940544 * (X * X) + 10414574138294272 * (X * X * X) + 94733921849180160 * (X * X * X * X) - 12244161486913536 * (X * X * X * X * X) - 22412445020585984 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G + (351843720888320 - 4134163720437760 * X + 16958867346817024 * (X * X) - 26001250973646848 * (X * X * X) + 2603643534573568 * (X * X * X * X) + 18946784369836032 * (X * X * X * X * X) - 2040693581152256 * (X * X * X * X * X * X) - 3201777860083712 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G = (123145302310912 : ℚ⟦X⟧) := by linear_combination hd
  have hd2 : (-9147936743096320 + 79551865292849152 * X - 196539902488215552 * X ^ 2 + 37365803158339584 * X ^ 3 + 263882790666240000 * X ^ 4 - 45915605575925760 * X ^ 5 - 72409437758816256 * X ^ 6) * derivative ℚ G + (422212465065984 - 5893382324879360 * X + 28675263252398080 * X ^ 2 - 53022848737869824 * X ^ 3 + 10871970975449088 * X ^ 4 + 48712763156987904 * X ^ 5 - 9183121115185152 * X ^ 6 - 11083077207982080 * X ^ 7) * derivative ℚ (derivative ℚ G) + (35184372088832 * X - 439804651110400 * X ^ 2 + 1952732650930176 * X ^ 3 - 3377699720527872 * X ^ 4 + 826832744087552 * X ^ 5 + 2480498232262656 * X ^ 6 - 510173395288064 * X ^ 7 - 492581209243648 * X ^ 8) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (33917734693634048 - 156007505841881088 * X + 31243722414882816 * X ^ 2 + 378935687396720640 * X ^ 3 - 61220807434567680 * X ^ 4 - 134474670123515904 * X ^ 5) * G = 0 := by
    rw [← hL2, hdp, hRd2]
  have hfull : (17592186044416 - 316659348799488 * X + 2339760743907328 * X ^ 2 - 9042383626829824 * X ^ 3 + 18999560927969280 * X ^ 4 - 19210667160502272 * X ^ 5 + 2515682604351488 * X ^ 6 + 10449758510383104 * X ^ 7 - 5224879255191552 * X ^ 8 - 1231453023109120 * X ^ 9 + 862017116176384 * X ^ 10) * ((6 * X ^ 3 - 21 * X ^ 4 - 12 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (112 * X ^ 2 - 443 * X ^ 3 - 290 * X ^ 4) * derivative ℚ (derivative ℚ G) + (440 * X - 2720 * X ^ 2 - 2034 * X ^ 3) * derivative ℚ G + (-4840 * X - 4056 * X ^ 2) * G - (0)) = 0 := by
    linear_combination (3 * X ^ 2 - 27 * X ^ 3 + 78 * X ^ 4 - 69 * X ^ 5 - 15 * X ^ 6 + 21 * X ^ 7) * hd2 + (20 * X - 153 * X ^ 2 + 364 * X ^ 3 - 253 * X ^ 4 - 40 * X ^ 5 + 35 * X ^ 6) * hd + (-7 * X + 56 * X ^ 2 - 147 * X ^ 3 + 140 * X ^ 4 - 35 * X ^ 5) * h
  have hg : (17592186044416 - 316659348799488 * X + 2339760743907328 * X ^ 2 - 9042383626829824 * X ^ 3 + 18999560927969280 * X ^ 4 - 19210667160502272 * X ^ 5 + 2515682604351488 * X ^ 6 + 10449758510383104 * X ^ 7 - 5224879255191552 * X ^ 8 - 1231453023109120 * X ^ 9 + 862017116176384 * X ^ 10 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (17592186044416 : ℚ⟦X⟧) = 17592186044416 := cnum 17592186044416
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-1024 * X ^ 10 + 4096 * X ^ 11 + (3072 * X ^ 10) * S) = 1024 - 10240 * X + 35840 * X ^ 2 - 51200 * X ^ 3 + 25600 * X ^ 4 - 2048 * X ^ 5 + (-1024 + 8192 * X - 21504 * X ^ 2 + 20480 * X ^ 3 - 5120 * X ^ 4) * S) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 6 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-21) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C (-12) + derivative ℚ (derivative ℚ G) * X * X * C 112 +
      derivative ℚ (derivative ℚ G) * X * X * X * C (-443) + derivative ℚ (derivative ℚ G) * X * X * X * X * C (-290) +
      derivative ℚ G * X * C 440 + derivative ℚ G * X * X * C (-2720) +
      derivative ℚ G * X * X * X * C (-2034) + G * X * C (-4840) +
      G * X * X * C (-4056) =
      0 := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-1024 * X ^ 10 + 4096 * X ^ 11 + (3072 * X ^ 10) * S) = 1024 - 10240 * X + 35840 * X ^ 2 - 51200 * X ^ 3 + 25600 * X ^ 4 - 2048 * X ^ 5 + (-1024 + 8192 * X - 21504 * X ^ 2 + 20480 * X ^ 3 - 5120 * X ^ 4) * S) (m : ℕ) :
    6 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-21) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-12) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + 112 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-443) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-290) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      440 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-2720) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-2034) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-4840) * coeff (m + 1 + 1 + 1 + 1) G +
      (-4056) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-1024 * X ^ 10 + 4096 * X ^ 11 + (3072 * X ^ 10) * S) = 1024 - 10240 * X + 35840 * X ^ 2 - 51200 * X ^ 3 + 25600 * X ^ 4 - 2048 * X ^ 5 + (-1024 + 8192 * X - 21504 * X ^ 2 + 20480 * X ^ 3 - 5120 * X ^ 4) * S) :
    224 * coeff (0 + 1 + 1) G + 880 * coeff (0 + 1 + 1) G +
      (-2720) * coeff (0 + 1) G + (-4840) * coeff (0 + 1) G +
      (-4056) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-1024 * X ^ 10 + 4096 * X ^ 11 + (3072 * X ^ 10) * S) = 1024 - 10240 * X + 35840 * X ^ 2 - 51200 * X ^ 3 + 25600 * X ^ 4 - 2048 * X ^ 5 + (-1024 + 8192 * X - 21504 * X ^ 2 + 20480 * X ^ 3 - 5120 * X ^ 4) * S) :
    36 * coeff (0 + 1 + 1 + 1) G + 672 * coeff (0 + 1 + 1 + 1) G +
      (-886) * coeff (0 + 1 + 1) G + 1320 * coeff (0 + 1 + 1 + 1) G +
      (-5440) * coeff (0 + 1 + 1) G + (-2034) * coeff (0 + 1) G +
      (-4840) * coeff (0 + 1 + 1) G + (-4056) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-1024 * X ^ 10 + 4096 * X ^ 11 + (3072 * X ^ 10) * S) = 1024 - 10240 * X + 35840 * X ^ 2 - 51200 * X ^ 3 + 25600 * X ^ 4 - 2048 * X ^ 5 + (-1024 + 8192 * X - 21504 * X ^ 2 + 20480 * X ^ 3 - 5120 * X ^ 4) * S) :
    144 * coeff (0 + 1 + 1 + 1 + 1) G + (-126) * coeff (0 + 1 + 1 + 1) G +
      1344 * coeff (0 + 1 + 1 + 1 + 1) G + (-2658) * coeff (0 + 1 + 1 + 1) G +
      (-580) * coeff (0 + 1 + 1) G + 1760 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-8160) * coeff (0 + 1 + 1 + 1) G + (-4068) * coeff (0 + 1 + 1) G +
      (-4840) * coeff (0 + 1 + 1 + 1) G + (-4056) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A172067Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a172067.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  cases m with
  | zero =>
    have r := A172067Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (1024 * PowerSeries.X ^ 10) * hG - ((-2) + (18) * S + (-72) * S ^ 2 + (168) * S ^ 3 + (-252) * S ^ 4 + (252) * S ^ 5 + (-168) * S ^ 6 + (72) * S ^ 7 + (-18) * S ^ 8 + (2) * S ^ 9 + (-4 * PowerSeries.X) * c + (32 * PowerSeries.X) * c * S + (-112 * PowerSeries.X) * c * S ^ 2 + (224 * PowerSeries.X) * c * S ^ 3 + (-280 * PowerSeries.X) * c * S ^ 4 + (224 * PowerSeries.X) * c * S ^ 5 + (-112 * PowerSeries.X) * c * S ^ 6 + (32 * PowerSeries.X) * c * S ^ 7 + (-4 * PowerSeries.X) * c * S ^ 8 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (56 * PowerSeries.X ^ 2) * c ^ 2 * S + (-168 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (280 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-280 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 4 + (168 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 5 + (-56 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 6 + (8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 7 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (96 * PowerSeries.X ^ 3) * c ^ 3 * S + (-240 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (320 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 3 + (-240 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 4 + (96 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 5 + (-16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 6 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (160 * PowerSeries.X ^ 4) * c ^ 4 * S + (-320 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 2 + (320 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 3 + (-160 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 4 + (32 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 5 + (-64 * PowerSeries.X ^ 5) * c ^ 5 + (256 * PowerSeries.X ^ 5) * c ^ 5 * S + (-384 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 2 + (256 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 3 + (-64 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 4 + (-128 * PowerSeries.X ^ 6) * c ^ 6 + (384 * PowerSeries.X ^ 6) * c ^ 6 * S + (-384 * PowerSeries.X ^ 6) * c ^ 6 * S ^ 2 + (128 * PowerSeries.X ^ 6) * c ^ 6 * S ^ 3 + (-256 * PowerSeries.X ^ 7) * c ^ 7 + (512 * PowerSeries.X ^ 7) * c ^ 7 * S + (-256 * PowerSeries.X ^ 7) * c ^ 7 * S ^ 2 + (-512 * PowerSeries.X ^ 8) * c ^ 8 + (512 * PowerSeries.X ^ 8) * c ^ 8 * S + (-1024 * PowerSeries.X ^ 9) * c ^ 9) * hc - ((-1022 + 6152 * PowerSeries.X - 11232 * PowerSeries.X ^ 2 + 6272 * PowerSeries.X ^ 3 - 512 * PowerSeries.X ^ 4) + (1004 - 4176 * PowerSeries.X + 4800 * PowerSeries.X ^ 2 - 1280 * PowerSeries.X ^ 3) * S + (-932 + 2424 * PowerSeries.X - 1536 * PowerSeries.X ^ 2 + 128 * PowerSeries.X ^ 3) * S ^ 2 + (764 - 1120 * PowerSeries.X + 320 * PowerSeries.X ^ 2) * S ^ 3 + (-512 + 376 * PowerSeries.X - 32 * PowerSeries.X ^ 2) * S ^ 4 + (260 - 80 * PowerSeries.X) * S ^ 5 + (-92 + 8 * PowerSeries.X) * S ^ 6 + (20) * S ^ 7 + (-2) * S ^ 8) * hS)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A172067Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination (1024 * PowerSeries.X ^ 10) * hG - ((-2) + (18) * S + (-72) * S ^ 2 + (168) * S ^ 3 + (-252) * S ^ 4 + (252) * S ^ 5 + (-168) * S ^ 6 + (72) * S ^ 7 + (-18) * S ^ 8 + (2) * S ^ 9 + (-4 * PowerSeries.X) * c + (32 * PowerSeries.X) * c * S + (-112 * PowerSeries.X) * c * S ^ 2 + (224 * PowerSeries.X) * c * S ^ 3 + (-280 * PowerSeries.X) * c * S ^ 4 + (224 * PowerSeries.X) * c * S ^ 5 + (-112 * PowerSeries.X) * c * S ^ 6 + (32 * PowerSeries.X) * c * S ^ 7 + (-4 * PowerSeries.X) * c * S ^ 8 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (56 * PowerSeries.X ^ 2) * c ^ 2 * S + (-168 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (280 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-280 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 4 + (168 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 5 + (-56 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 6 + (8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 7 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (96 * PowerSeries.X ^ 3) * c ^ 3 * S + (-240 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (320 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 3 + (-240 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 4 + (96 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 5 + (-16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 6 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (160 * PowerSeries.X ^ 4) * c ^ 4 * S + (-320 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 2 + (320 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 3 + (-160 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 4 + (32 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 5 + (-64 * PowerSeries.X ^ 5) * c ^ 5 + (256 * PowerSeries.X ^ 5) * c ^ 5 * S + (-384 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 2 + (256 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 3 + (-64 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 4 + (-128 * PowerSeries.X ^ 6) * c ^ 6 + (384 * PowerSeries.X ^ 6) * c ^ 6 * S + (-384 * PowerSeries.X ^ 6) * c ^ 6 * S ^ 2 + (128 * PowerSeries.X ^ 6) * c ^ 6 * S ^ 3 + (-256 * PowerSeries.X ^ 7) * c ^ 7 + (512 * PowerSeries.X ^ 7) * c ^ 7 * S + (-256 * PowerSeries.X ^ 7) * c ^ 7 * S ^ 2 + (-512 * PowerSeries.X ^ 8) * c ^ 8 + (512 * PowerSeries.X ^ 8) * c ^ 8 * S + (-1024 * PowerSeries.X ^ 9) * c ^ 9) * hc - ((-1022 + 6152 * PowerSeries.X - 11232 * PowerSeries.X ^ 2 + 6272 * PowerSeries.X ^ 3 - 512 * PowerSeries.X ^ 4) + (1004 - 4176 * PowerSeries.X + 4800 * PowerSeries.X ^ 2 - 1280 * PowerSeries.X ^ 3) * S + (-932 + 2424 * PowerSeries.X - 1536 * PowerSeries.X ^ 2 + 128 * PowerSeries.X ^ 3) * S ^ 2 + (764 - 1120 * PowerSeries.X + 320 * PowerSeries.X ^ 2) * S ^ 3 + (-512 + 376 * PowerSeries.X - 32 * PowerSeries.X ^ 2) * S ^ 4 + (260 - 80 * PowerSeries.X) * S ^ 5 + (-92 + 8 * PowerSeries.X) * S ^ 6 + (20) * S ^ 7 + (-2) * S ^ 8) * hS)
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A172067Aux.relE2 (S) G (by linear_combination hS)
            (by linear_combination (1024 * PowerSeries.X ^ 10) * hG - ((-2) + (18) * S + (-72) * S ^ 2 + (168) * S ^ 3 + (-252) * S ^ 4 + (252) * S ^ 5 + (-168) * S ^ 6 + (72) * S ^ 7 + (-18) * S ^ 8 + (2) * S ^ 9 + (-4 * PowerSeries.X) * c + (32 * PowerSeries.X) * c * S + (-112 * PowerSeries.X) * c * S ^ 2 + (224 * PowerSeries.X) * c * S ^ 3 + (-280 * PowerSeries.X) * c * S ^ 4 + (224 * PowerSeries.X) * c * S ^ 5 + (-112 * PowerSeries.X) * c * S ^ 6 + (32 * PowerSeries.X) * c * S ^ 7 + (-4 * PowerSeries.X) * c * S ^ 8 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (56 * PowerSeries.X ^ 2) * c ^ 2 * S + (-168 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (280 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-280 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 4 + (168 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 5 + (-56 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 6 + (8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 7 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (96 * PowerSeries.X ^ 3) * c ^ 3 * S + (-240 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (320 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 3 + (-240 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 4 + (96 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 5 + (-16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 6 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (160 * PowerSeries.X ^ 4) * c ^ 4 * S + (-320 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 2 + (320 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 3 + (-160 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 4 + (32 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 5 + (-64 * PowerSeries.X ^ 5) * c ^ 5 + (256 * PowerSeries.X ^ 5) * c ^ 5 * S + (-384 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 2 + (256 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 3 + (-64 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 4 + (-128 * PowerSeries.X ^ 6) * c ^ 6 + (384 * PowerSeries.X ^ 6) * c ^ 6 * S + (-384 * PowerSeries.X ^ 6) * c ^ 6 * S ^ 2 + (128 * PowerSeries.X ^ 6) * c ^ 6 * S ^ 3 + (-256 * PowerSeries.X ^ 7) * c ^ 7 + (512 * PowerSeries.X ^ 7) * c ^ 7 * S + (-256 * PowerSeries.X ^ 7) * c ^ 7 * S ^ 2 + (-512 * PowerSeries.X ^ 8) * c ^ 8 + (512 * PowerSeries.X ^ 8) * c ^ 8 * S + (-1024 * PowerSeries.X ^ 9) * c ^ 9) * hc - ((-1022 + 6152 * PowerSeries.X - 11232 * PowerSeries.X ^ 2 + 6272 * PowerSeries.X ^ 3 - 512 * PowerSeries.X ^ 4) + (1004 - 4176 * PowerSeries.X + 4800 * PowerSeries.X ^ 2 - 1280 * PowerSeries.X ^ 3) * S + (-932 + 2424 * PowerSeries.X - 1536 * PowerSeries.X ^ 2 + 128 * PowerSeries.X ^ 3) * S ^ 2 + (764 - 1120 * PowerSeries.X + 320 * PowerSeries.X ^ 2) * S ^ 3 + (-512 + 376 * PowerSeries.X - 32 * PowerSeries.X ^ 2) * S ^ 4 + (260 - 80 * PowerSeries.X) * S ^ 5 + (-92 + 8 * PowerSeries.X) * S ^ 6 + (20) * S ^ 7 + (-2) * S ^ 8) * hS)
        push_cast
        linear_combination r
      | succ m =>
        have r := A172067Aux.rel (S) G (by linear_combination hS)
            (by linear_combination (1024 * PowerSeries.X ^ 10) * hG - ((-2) + (18) * S + (-72) * S ^ 2 + (168) * S ^ 3 + (-252) * S ^ 4 + (252) * S ^ 5 + (-168) * S ^ 6 + (72) * S ^ 7 + (-18) * S ^ 8 + (2) * S ^ 9 + (-4 * PowerSeries.X) * c + (32 * PowerSeries.X) * c * S + (-112 * PowerSeries.X) * c * S ^ 2 + (224 * PowerSeries.X) * c * S ^ 3 + (-280 * PowerSeries.X) * c * S ^ 4 + (224 * PowerSeries.X) * c * S ^ 5 + (-112 * PowerSeries.X) * c * S ^ 6 + (32 * PowerSeries.X) * c * S ^ 7 + (-4 * PowerSeries.X) * c * S ^ 8 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (56 * PowerSeries.X ^ 2) * c ^ 2 * S + (-168 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (280 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-280 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 4 + (168 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 5 + (-56 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 6 + (8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 7 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (96 * PowerSeries.X ^ 3) * c ^ 3 * S + (-240 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (320 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 3 + (-240 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 4 + (96 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 5 + (-16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 6 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (160 * PowerSeries.X ^ 4) * c ^ 4 * S + (-320 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 2 + (320 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 3 + (-160 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 4 + (32 * PowerSeries.X ^ 4) * c ^ 4 * S ^ 5 + (-64 * PowerSeries.X ^ 5) * c ^ 5 + (256 * PowerSeries.X ^ 5) * c ^ 5 * S + (-384 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 2 + (256 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 3 + (-64 * PowerSeries.X ^ 5) * c ^ 5 * S ^ 4 + (-128 * PowerSeries.X ^ 6) * c ^ 6 + (384 * PowerSeries.X ^ 6) * c ^ 6 * S + (-384 * PowerSeries.X ^ 6) * c ^ 6 * S ^ 2 + (128 * PowerSeries.X ^ 6) * c ^ 6 * S ^ 3 + (-256 * PowerSeries.X ^ 7) * c ^ 7 + (512 * PowerSeries.X ^ 7) * c ^ 7 * S + (-256 * PowerSeries.X ^ 7) * c ^ 7 * S ^ 2 + (-512 * PowerSeries.X ^ 8) * c ^ 8 + (512 * PowerSeries.X ^ 8) * c ^ 8 * S + (-1024 * PowerSeries.X ^ 9) * c ^ 9) * hc - ((-1022 + 6152 * PowerSeries.X - 11232 * PowerSeries.X ^ 2 + 6272 * PowerSeries.X ^ 3 - 512 * PowerSeries.X ^ 4) + (1004 - 4176 * PowerSeries.X + 4800 * PowerSeries.X ^ 2 - 1280 * PowerSeries.X ^ 3) * S + (-932 + 2424 * PowerSeries.X - 1536 * PowerSeries.X ^ 2 + 128 * PowerSeries.X ^ 3) * S ^ 2 + (764 - 1120 * PowerSeries.X + 320 * PowerSeries.X ^ 2) * S ^ 3 + (-512 + 376 * PowerSeries.X - 32 * PowerSeries.X ^ 2) * S ^ 4 + (260 - 80 * PowerSeries.X) * S ^ 5 + (-92 + 8 * PowerSeries.X) * S ^ 6 + (20) * S ^ 7 + (-2) * S ^ 8) * hS) m
        push_cast
        linear_combination r
