import OMAStatements.S_oeis_a172063

-- Problem: A172063: Expansion of (2/(3*sqrt(1-4*z)-1+4*z))*((1-sqrt(1-4*z))/(2*z))^k with k=6.
-- Upstream: formal-conjectures statements/oeis-a172063.lean:0 (declaration OMA.S_oeis_a172063.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its first two derivatives, divided by a common
polynomial factor, is a third order equation with polynomial coefficients and polynomial right
side rho; the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A172063Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-64 * X ^ 6 + 256 * X ^ 7 + (192 * X ^ 6) * S) = 64 - 384 * X + 576 * X ^ 2 - 128 * X ^ 3 + (-64 + 256 * X - 192 * X ^ 2) * S) :
    (536870912 * X - 4563402752 * X ^ 2 + 10468982784 * X ^ 3 - 536870912 * X ^ 4 - 9932111872 * X ^ 5 - 3221225472 * X ^ 6) * derivative ℚ G + (3221225472 - 25501368320 * X + 51539607552 * X ^ 2 + 6442450944 * X ^ 3 - 42949672960 * X ^ 4 - 14495514624 * X ^ 5) * G = 3221225472 + 805306368 * X := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8192 : derivative ℚ (8192 : ℚ⟦X⟧) = 0 := dnum 8192
  have d24576 : derivative ℚ (24576 : ℚ⟦X⟧) = 0 := dnum 24576
  have d32768 : derivative ℚ (32768 : ℚ⟦X⟧) = 0 := dnum 32768
  have d40960 : derivative ℚ (40960 : ℚ⟦X⟧) = 0 := dnum 40960
  have d57344 : derivative ℚ (57344 : ℚ⟦X⟧) = 0 := dnum 57344
  have d65536 : derivative ℚ (65536 : ℚ⟦X⟧) = 0 := dnum 65536
  have d98304 : derivative ℚ (98304 : ℚ⟦X⟧) = 0 := dnum 98304
  have d114688 : derivative ℚ (114688 : ℚ⟦X⟧) = 0 := dnum 114688
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-32768 * X ^ 12 + 114688 * X ^ 13 + 65536 * X ^ 14) * G = (8192 * X ^ 6 - 57344 * X ^ 7 + 98304 * X ^ 8 + 8192 * X ^ 9 - 32768 * X ^ 10 : ℚ⟦X⟧) + (-8192 * X ^ 6 + 40960 * X ^ 7 - 32768 * X ^ 8 - 24576 * X ^ 9) * S := by
    linear_combination (-64 * X ^ 6 + 256 * X ^ 7 - (192 * X ^ 6) * S) * hG + (192 * X ^ 6) * ((192 * X ^ 6) * G - (-64 + 256 * X - 192 * X ^ 2)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-32768 * (X * X * X * X * X * X * X * X * X * X * X * X) + 114688 * (X * X * X * X * X * X * X * X * X * X * X * X * X) + 65536 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-393216 * X ^ 11 + 1490944 * X ^ 12 + 917504 * X ^ 13) * G + (-32768 * X ^ 12 + 114688 * X ^ 13 + 65536 * X ^ 14) * derivative ℚ G := by
    simp [Derivation.leibniz, d32768, d65536, d114688]
    ring
  have hR : derivative ℚ ((8192 * (X * X * X * X * X * X) - 57344 * (X * X * X * X * X * X * X) + 98304 * (X * X * X * X * X * X * X * X) + 8192 * (X * X * X * X * X * X * X * X * X) - 32768 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-8192 * (X * X * X * X * X * X) + 40960 * (X * X * X * X * X * X * X) - 32768 * (X * X * X * X * X * X * X * X) - 24576 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S) =
      49152 * X ^ 5 - 401408 * X ^ 6 + 786432 * X ^ 7 + 73728 * X ^ 8 - 327680 * X ^ 9 + (-49152 * X ^ 5 + 286720 * X ^ 6 - 262144 * X ^ 7 - 221184 * X ^ 8) * S + (-8192 * X ^ 6 + 40960 * X ^ 7 - 32768 * X ^ 8 - 24576 * X ^ 9) * derivative ℚ S := by
    simp [Derivation.leibniz, d8192, d24576, d32768, d40960, d57344, d98304]
    ring
  have hk2 : (-32768 * (X * X * X * X * X * X * X * X * X * X * X * X) + 114688 * (X * X * X * X * X * X * X * X * X * X * X * X * X) + 65536 * (X * X * X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (8192 * (X * X * X * X * X * X) - 57344 * (X * X * X * X * X * X * X) + 98304 * (X * X * X * X * X * X * X * X) + 8192 * (X * X * X * X * X * X * X * X * X) - 32768 * (X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) + (-8192 * (X * X * X * X * X * X) + 40960 * (X * X * X * X * X * X * X) - 32768 * (X * X * X * X * X * X * X * X) - 24576 * (X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-393216 * X ^ 11 + 1490944 * X ^ 12 + 917504 * X ^ 13) * G + (-32768 * X ^ 12 + 114688 * X ^ 13 + 65536 * X ^ 14) * derivative ℚ G =
      49152 * X ^ 5 - 401408 * X ^ 6 + 786432 * X ^ 7 + 73728 * X ^ 8 - 327680 * X ^ 9 + (-49152 * X ^ 5 + 286720 * X ^ 6 - 262144 * X ^ 7 - 221184 * X ^ 8) * S + (-8192 * X ^ 6 + 40960 * X ^ 7 - 32768 * X ^ 8 - 24576 * X ^ 9) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 17 * ((1 - 4 * X) * ((536870912 * X - 4563402752 * X ^ 2 + 10468982784 * X ^ 3 - 536870912 * X ^ 4 - 9932111872 * X ^ 5 - 3221225472 * X ^ 6) * derivative ℚ G + (3221225472 - 25501368320 * X + 51539607552 * X ^ 2 + 6442450944 * X ^ 3 - 42949672960 * X ^ 4 - 14495514624 * X ^ 5) * G - (3221225472 + 805306368 * X))) = 0 := by
    linear_combination (-8192 * X ^ 6 + 40960 * X ^ 7 - 32768 * X ^ 8 - 24576 * X ^ 9) ^ 2 * S * hdS - 2 * (-8192 * X ^ 6 + 40960 * X ^ 7 - 32768 * X ^ 8 - 24576 * X ^ 9) ^ 2 * derivative ℚ S * hS -
      (2 * (-49152 * X ^ 5 + 286720 * X ^ 6 - 262144 * X ^ 7 - 221184 * X ^ 8) * (1 - 4 * X) + (-8192 * X ^ 6 + 40960 * X ^ 7 - 32768 * X ^ 8 - 24576 * X ^ 9) * (-4)) * hk + 2 * (-8192 * X ^ 6 + 40960 * X ^ 7 - 32768 * X ^ 8 - 24576 * X ^ 9) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 17 ≠ 0 := pow_ne_zero 17 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 4 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-64 * X ^ 6 + 256 * X ^ 7 + (192 * X ^ 6) * S) = 64 - 384 * X + 576 * X ^ 2 - 128 * X ^ 3 + (-64 + 256 * X - 192 * X ^ 2) * S) :
    (2 * X ^ 3 - 7 * X ^ 4 - 4 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (24 * X ^ 2 - 101 * X ^ 3 - 70 * X ^ 4) * derivative ℚ (derivative ℚ G) + (56 * X - 392 * X ^ 2 - 338 * X ^ 3) * derivative ℚ G + (-392 * X - 432 * X ^ 2) * G =
      0 := by
  have h := key S G hS hG
  have d536870912 : derivative ℚ (536870912 : ℚ⟦X⟧) = 0 := dnum 536870912
  have d805306368 : derivative ℚ (805306368 : ℚ⟦X⟧) = 0 := dnum 805306368
  have d2147483648 : derivative ℚ (2147483648 : ℚ⟦X⟧) = 0 := dnum 2147483648
  have d3221225472 : derivative ℚ (3221225472 : ℚ⟦X⟧) = 0 := dnum 3221225472
  have d4563402752 : derivative ℚ (4563402752 : ℚ⟦X⟧) = 0 := dnum 4563402752
  have d6442450944 : derivative ℚ (6442450944 : ℚ⟦X⟧) = 0 := dnum 6442450944
  have d9126805504 : derivative ℚ (9126805504 : ℚ⟦X⟧) = 0 := dnum 9126805504
  have d9932111872 : derivative ℚ (9932111872 : ℚ⟦X⟧) = 0 := dnum 9932111872
  have d10468982784 : derivative ℚ (10468982784 : ℚ⟦X⟧) = 0 := dnum 10468982784
  have d14495514624 : derivative ℚ (14495514624 : ℚ⟦X⟧) = 0 := dnum 14495514624
  have d19327352832 : derivative ℚ (19327352832 : ℚ⟦X⟧) = 0 := dnum 19327352832
  have d25501368320 : derivative ℚ (25501368320 : ℚ⟦X⟧) = 0 := dnum 25501368320
  have d31406948352 : derivative ℚ (31406948352 : ℚ⟦X⟧) = 0 := dnum 31406948352
  have d42949672960 : derivative ℚ (42949672960 : ℚ⟦X⟧) = 0 := dnum 42949672960
  have d49660559360 : derivative ℚ (49660559360 : ℚ⟦X⟧) = 0 := dnum 49660559360
  have d51539607552 : derivative ℚ (51539607552 : ℚ⟦X⟧) = 0 := dnum 51539607552
  have d72477573120 : derivative ℚ (72477573120 : ℚ⟦X⟧) = 0 := dnum 72477573120
  have d103079215104 : derivative ℚ (103079215104 : ℚ⟦X⟧) = 0 := dnum 103079215104
  have d171798691840 : derivative ℚ (171798691840 : ℚ⟦X⟧) = 0 := dnum 171798691840
  have hL : derivative ℚ ((536870912 * X - 4563402752 * (X * X) + 10468982784 * (X * X * X) - 536870912 * (X * X * X * X) - 9932111872 * (X * X * X * X * X) - 3221225472 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (3221225472 - 25501368320 * X + 51539607552 * (X * X) + 6442450944 * (X * X * X) - 42949672960 * (X * X * X * X) - 14495514624 * (X * X * X * X * X) : ℚ⟦X⟧) * G) =
      (536870912 - 9126805504 * X + 31406948352 * X ^ 2 - 2147483648 * X ^ 3 - 49660559360 * X ^ 4 - 19327352832 * X ^ 5) * derivative ℚ G + (536870912 * X - 4563402752 * X ^ 2 + 10468982784 * X ^ 3 - 536870912 * X ^ 4 - 9932111872 * X ^ 5 - 3221225472 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-25501368320 + 103079215104 * X + 19327352832 * X ^ 2 - 171798691840 * X ^ 3 - 72477573120 * X ^ 4) * G + (3221225472 - 25501368320 * X + 51539607552 * X ^ 2 + 6442450944 * X ^ 3 - 42949672960 * X ^ 4 - 14495514624 * X ^ 5) * derivative ℚ G := by
    simp [Derivation.leibniz, d536870912, d3221225472, d4563402752, d6442450944, d9932111872, d10468982784, d14495514624, d25501368320, d42949672960, d51539607552]
    ring
  have hRd : derivative ℚ (3221225472 + 805306368 * X : ℚ⟦X⟧) = 805306368 := by
    simp [Derivation.leibniz, d805306368, d3221225472]
  have h2 : (536870912 * X - 4563402752 * (X * X) + 10468982784 * (X * X * X) - 536870912 * (X * X * X * X) - 9932111872 * (X * X * X * X * X) - 3221225472 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (3221225472 - 25501368320 * X + 51539607552 * (X * X) + 6442450944 * (X * X * X) - 42949672960 * (X * X * X * X) - 14495514624 * (X * X * X * X * X) : ℚ⟦X⟧) * G = (3221225472 + 805306368 * X : ℚ⟦X⟧) := by linear_combination h
  have hd : (536870912 - 9126805504 * X + 31406948352 * X ^ 2 - 2147483648 * X ^ 3 - 49660559360 * X ^ 4 - 19327352832 * X ^ 5) * derivative ℚ G + (536870912 * X - 4563402752 * X ^ 2 + 10468982784 * X ^ 3 - 536870912 * X ^ 4 - 9932111872 * X ^ 5 - 3221225472 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-25501368320 + 103079215104 * X + 19327352832 * X ^ 2 - 171798691840 * X ^ 3 - 72477573120 * X ^ 4) * G + (3221225472 - 25501368320 * X + 51539607552 * X ^ 2 + 6442450944 * X ^ 3 - 42949672960 * X ^ 4 - 14495514624 * X ^ 5) * derivative ℚ G = 805306368 := by
    rw [← hL, h2, hRd]
  have hL2 : derivative ℚ ((536870912 - 9126805504 * X + 31406948352 * (X * X) - 2147483648 * (X * X * X) - 49660559360 * (X * X * X * X) - 19327352832 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (536870912 * X - 4563402752 * (X * X) + 10468982784 * (X * X * X) - 536870912 * (X * X * X * X) - 9932111872 * (X * X * X * X * X) - 3221225472 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-25501368320 + 103079215104 * X + 19327352832 * (X * X) - 171798691840 * (X * X * X) - 72477573120 * (X * X * X * X) : ℚ⟦X⟧) * G + (3221225472 - 25501368320 * X + 51539607552 * (X * X) + 6442450944 * (X * X * X) - 42949672960 * (X * X * X * X) - 14495514624 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G) =
      (-60129542144 + 268972326912 * X + 32212254720 * X ^ 2 - 542239621120 * X ^ 3 - 241591910400 * X ^ 4) * derivative ℚ G + (4294967296 - 43754979328 * X + 114353504256 * X ^ 2 + 2147483648 * X ^ 3 - 142270791680 * X ^ 4 - 53150220288 * X ^ 5) * derivative ℚ (derivative ℚ G) + (536870912 * X - 4563402752 * X ^ 2 + 10468982784 * X ^ 3 - 536870912 * X ^ 4 - 9932111872 * X ^ 5 - 3221225472 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (103079215104 + 38654705664 * X - 515396075520 * X ^ 2 - 289910292480 * X ^ 3) * G := by
    simp [Derivation.leibniz, d536870912, d2147483648, d3221225472, d4563402752, d6442450944, d9126805504, d9932111872, d10468982784, d14495514624, d19327352832, d25501368320, d31406948352, d42949672960, d49660559360, d51539607552, d72477573120, d103079215104, d171798691840]
    ring
  have hRd2 : derivative ℚ (805306368 : ℚ⟦X⟧) = 0 := by
    simp [d805306368]
  have hdp : (536870912 - 9126805504 * X + 31406948352 * (X * X) - 2147483648 * (X * X * X) - 49660559360 * (X * X * X * X) - 19327352832 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (536870912 * X - 4563402752 * (X * X) + 10468982784 * (X * X * X) - 536870912 * (X * X * X * X) - 9932111872 * (X * X * X * X * X) - 3221225472 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-25501368320 + 103079215104 * X + 19327352832 * (X * X) - 171798691840 * (X * X * X) - 72477573120 * (X * X * X * X) : ℚ⟦X⟧) * G + (3221225472 - 25501368320 * X + 51539607552 * (X * X) + 6442450944 * (X * X * X) - 42949672960 * (X * X * X * X) - 14495514624 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G = (805306368 : ℚ⟦X⟧) := by linear_combination hd
  have hd2 : (-60129542144 + 268972326912 * X + 32212254720 * X ^ 2 - 542239621120 * X ^ 3 - 241591910400 * X ^ 4) * derivative ℚ G + (4294967296 - 43754979328 * X + 114353504256 * X ^ 2 + 2147483648 * X ^ 3 - 142270791680 * X ^ 4 - 53150220288 * X ^ 5) * derivative ℚ (derivative ℚ G) + (536870912 * X - 4563402752 * X ^ 2 + 10468982784 * X ^ 3 - 536870912 * X ^ 4 - 9932111872 * X ^ 5 - 3221225472 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (103079215104 + 38654705664 * X - 515396075520 * X ^ 2 - 289910292480 * X ^ 3) * G = 0 := by
    rw [← hL2, hdp, hRd2]
  have hfull : (268435456 - 2684354560 * X + 8858370048 * X ^ 2 - 9126805504 * X ^ 3 - 3758096384 * X ^ 4 + 6442450944 * X ^ 5 + 2415919104 * X ^ 6) * ((2 * X ^ 3 - 7 * X ^ 4 - 4 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (24 * X ^ 2 - 101 * X ^ 3 - 70 * X ^ 4) * derivative ℚ (derivative ℚ G) + (56 * X - 392 * X ^ 2 - 338 * X ^ 3) * derivative ℚ G + (-392 * X - 432 * X ^ 2) * G - (0)) = 0 := by
    linear_combination (X ^ 2 - 5 * X ^ 3 + 4 * X ^ 4 + 3 * X ^ 5) * hd2 + (4 * X - 15 * X ^ 2 + 8 * X ^ 3 + 3 * X ^ 4) * hd + (-X + 4 * X ^ 2 - 3 * X ^ 3) * h
  have hg : (268435456 - 2684354560 * X + 8858370048 * X ^ 2 - 9126805504 * X ^ 3 - 3758096384 * X ^ 4 + 6442450944 * X ^ 5 + 2415919104 * X ^ 6 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (268435456 : ℚ⟦X⟧) = 268435456 := cnum 268435456
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-64 * X ^ 6 + 256 * X ^ 7 + (192 * X ^ 6) * S) = 64 - 384 * X + 576 * X ^ 2 - 128 * X ^ 3 + (-64 + 256 * X - 192 * X ^ 2) * S) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 2 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-7) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C (-4) + derivative ℚ (derivative ℚ G) * X * X * C 24 +
      derivative ℚ (derivative ℚ G) * X * X * X * C (-101) + derivative ℚ (derivative ℚ G) * X * X * X * X * C (-70) +
      derivative ℚ G * X * C 56 + derivative ℚ G * X * X * C (-392) +
      derivative ℚ G * X * X * X * C (-338) + G * X * C (-392) +
      G * X * X * C (-432) =
      0 := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-64 * X ^ 6 + 256 * X ^ 7 + (192 * X ^ 6) * S) = 64 - 384 * X + 576 * X ^ 2 - 128 * X ^ 3 + (-64 + 256 * X - 192 * X ^ 2) * S) (m : ℕ) :
    2 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-7) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + 24 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-101) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-70) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      56 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-392) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-338) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-392) * coeff (m + 1 + 1 + 1 + 1) G +
      (-432) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-64 * X ^ 6 + 256 * X ^ 7 + (192 * X ^ 6) * S) = 64 - 384 * X + 576 * X ^ 2 - 128 * X ^ 3 + (-64 + 256 * X - 192 * X ^ 2) * S) :
    48 * coeff (0 + 1 + 1) G + 112 * coeff (0 + 1 + 1) G +
      (-392) * coeff (0 + 1) G + (-392) * coeff (0 + 1) G +
      (-432) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-64 * X ^ 6 + 256 * X ^ 7 + (192 * X ^ 6) * S) = 64 - 384 * X + 576 * X ^ 2 - 128 * X ^ 3 + (-64 + 256 * X - 192 * X ^ 2) * S) :
    12 * coeff (0 + 1 + 1 + 1) G + 144 * coeff (0 + 1 + 1 + 1) G +
      (-202) * coeff (0 + 1 + 1) G + 168 * coeff (0 + 1 + 1 + 1) G +
      (-784) * coeff (0 + 1 + 1) G + (-338) * coeff (0 + 1) G +
      (-392) * coeff (0 + 1 + 1) G + (-432) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-64 * X ^ 6 + 256 * X ^ 7 + (192 * X ^ 6) * S) = 64 - 384 * X + 576 * X ^ 2 - 128 * X ^ 3 + (-64 + 256 * X - 192 * X ^ 2) * S) :
    48 * coeff (0 + 1 + 1 + 1 + 1) G + (-42) * coeff (0 + 1 + 1 + 1) G +
      288 * coeff (0 + 1 + 1 + 1 + 1) G + (-606) * coeff (0 + 1 + 1 + 1) G +
      (-140) * coeff (0 + 1 + 1) G + 224 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-1176) * coeff (0 + 1 + 1 + 1) G + (-676) * coeff (0 + 1 + 1) G +
      (-392) * coeff (0 + 1 + 1 + 1) G + (-432) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A172063Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a172063.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  cases m with
  | zero =>
    have r := A172063Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (64 * PowerSeries.X ^ 6) * hG - ((-2) + (10) * S + (-20) * S ^ 2 + (20) * S ^ 3 + (-10) * S ^ 4 + (2) * S ^ 5 + (-4 * PowerSeries.X) * c + (16 * PowerSeries.X) * c * S + (-24 * PowerSeries.X) * c * S ^ 2 + (16 * PowerSeries.X) * c * S ^ 3 + (-4 * PowerSeries.X) * c * S ^ 4 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (24 * PowerSeries.X ^ 2) * c ^ 2 * S + (-24 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (32 * PowerSeries.X ^ 3) * c ^ 3 * S + (-16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (32 * PowerSeries.X ^ 4) * c ^ 4 * S + (-64 * PowerSeries.X ^ 5) * c ^ 5) * hc - ((-62 + 136 * PowerSeries.X - 32 * PowerSeries.X ^ 2) + (52 - 48 * PowerSeries.X) * S + (-32 + 8 * PowerSeries.X) * S ^ 2 + (12) * S ^ 3 + (-2) * S ^ 4) * hS)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A172063Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination (64 * PowerSeries.X ^ 6) * hG - ((-2) + (10) * S + (-20) * S ^ 2 + (20) * S ^ 3 + (-10) * S ^ 4 + (2) * S ^ 5 + (-4 * PowerSeries.X) * c + (16 * PowerSeries.X) * c * S + (-24 * PowerSeries.X) * c * S ^ 2 + (16 * PowerSeries.X) * c * S ^ 3 + (-4 * PowerSeries.X) * c * S ^ 4 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (24 * PowerSeries.X ^ 2) * c ^ 2 * S + (-24 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (32 * PowerSeries.X ^ 3) * c ^ 3 * S + (-16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (32 * PowerSeries.X ^ 4) * c ^ 4 * S + (-64 * PowerSeries.X ^ 5) * c ^ 5) * hc - ((-62 + 136 * PowerSeries.X - 32 * PowerSeries.X ^ 2) + (52 - 48 * PowerSeries.X) * S + (-32 + 8 * PowerSeries.X) * S ^ 2 + (12) * S ^ 3 + (-2) * S ^ 4) * hS)
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A172063Aux.relE2 (S) G (by linear_combination hS)
            (by linear_combination (64 * PowerSeries.X ^ 6) * hG - ((-2) + (10) * S + (-20) * S ^ 2 + (20) * S ^ 3 + (-10) * S ^ 4 + (2) * S ^ 5 + (-4 * PowerSeries.X) * c + (16 * PowerSeries.X) * c * S + (-24 * PowerSeries.X) * c * S ^ 2 + (16 * PowerSeries.X) * c * S ^ 3 + (-4 * PowerSeries.X) * c * S ^ 4 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (24 * PowerSeries.X ^ 2) * c ^ 2 * S + (-24 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (32 * PowerSeries.X ^ 3) * c ^ 3 * S + (-16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (32 * PowerSeries.X ^ 4) * c ^ 4 * S + (-64 * PowerSeries.X ^ 5) * c ^ 5) * hc - ((-62 + 136 * PowerSeries.X - 32 * PowerSeries.X ^ 2) + (52 - 48 * PowerSeries.X) * S + (-32 + 8 * PowerSeries.X) * S ^ 2 + (12) * S ^ 3 + (-2) * S ^ 4) * hS)
        push_cast
        linear_combination r
      | succ m =>
        have r := A172063Aux.rel (S) G (by linear_combination hS)
            (by linear_combination (64 * PowerSeries.X ^ 6) * hG - ((-2) + (10) * S + (-20) * S ^ 2 + (20) * S ^ 3 + (-10) * S ^ 4 + (2) * S ^ 5 + (-4 * PowerSeries.X) * c + (16 * PowerSeries.X) * c * S + (-24 * PowerSeries.X) * c * S ^ 2 + (16 * PowerSeries.X) * c * S ^ 3 + (-4 * PowerSeries.X) * c * S ^ 4 + (-8 * PowerSeries.X ^ 2) * c ^ 2 + (24 * PowerSeries.X ^ 2) * c ^ 2 * S + (-24 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 2 + (8 * PowerSeries.X ^ 2) * c ^ 2 * S ^ 3 + (-16 * PowerSeries.X ^ 3) * c ^ 3 + (32 * PowerSeries.X ^ 3) * c ^ 3 * S + (-16 * PowerSeries.X ^ 3) * c ^ 3 * S ^ 2 + (-32 * PowerSeries.X ^ 4) * c ^ 4 + (32 * PowerSeries.X ^ 4) * c ^ 4 * S + (-64 * PowerSeries.X ^ 5) * c ^ 5) * hc - ((-62 + 136 * PowerSeries.X - 32 * PowerSeries.X ^ 2) + (52 - 48 * PowerSeries.X) * S + (-32 + 8 * PowerSeries.X) * S ^ 2 + (12) * S ^ 3 + (-2) * S ^ 4) * hS) m
        push_cast
        linear_combination r
