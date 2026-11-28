import OMAStatements.S_oeis_a118447

-- Problem: A118447: Number of rooted n-edge one-vertex maps on the Klein bottle (dually: one-face maps).
-- Upstream: formal-conjectures statements/oeis-a118447.lean:0 (declaration OMA.S_oeis_a118447.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its first two derivatives, divided by a common
polynomial factor, is a third order equation with polynomial coefficients and polynomial right
side rho; the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A118447Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (0 + (8 - 64 * X + 128 * X ^ 2) * S) = 8 * X + 16 * X ^ 2 + (-8 * X) * S) :
    (8192 * X - 81920 * X ^ 2 + 196608 * X ^ 3 + 262144 * X ^ 4 - 1048576 * X ^ 5) * derivative ℚ G + (-8192 - 16384 * X + 491520 * X ^ 2 - 1048576 * X ^ 3 - 524288 * X ^ 4) * G = 32768 * X ^ 2 - 32768 * X ^ 3 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d384 : derivative ℚ (384 : ℚ⟦X⟧) = 0 := dnum 384
  have d768 : derivative ℚ (768 : ℚ⟦X⟧) = 0 := dnum 768
  have d1280 : derivative ℚ (1280 : ℚ⟦X⟧) = 0 := dnum 1280
  have d2048 : derivative ℚ (2048 : ℚ⟦X⟧) = 0 := dnum 2048
  have d3072 : derivative ℚ (3072 : ℚ⟦X⟧) = 0 := dnum 3072
  have d4096 : derivative ℚ (4096 : ℚ⟦X⟧) = 0 := dnum 4096
  have d10240 : derivative ℚ (10240 : ℚ⟦X⟧) = 0 := dnum 10240
  have d40960 : derivative ℚ (40960 : ℚ⟦X⟧) = 0 := dnum 40960
  have d65536 : derivative ℚ (65536 : ℚ⟦X⟧) = 0 := dnum 65536
  have d81920 : derivative ℚ (81920 : ℚ⟦X⟧) = 0 := dnum 81920
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-64 + 1280 * X - 10240 * X ^ 2 + 40960 * X ^ 3 - 81920 * X ^ 4 + 65536 * X ^ 5) * G = (64 * X - 768 * X ^ 2 + 3072 * X ^ 3 - 4096 * X ^ 4 : ℚ⟦X⟧) + (-64 * X + 384 * X ^ 2 - 2048 * X ^ 4) * S := by
    linear_combination (0 - (8 - 64 * X + 128 * X ^ 2) * S) * hG + (8 - 64 * X + 128 * X ^ 2) * ((8 - 64 * X + 128 * X ^ 2) * G - (-8 * X)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-64 + 1280 * X - 10240 * (X * X) + 40960 * (X * X * X) - 81920 * (X * X * X * X) + 65536 * (X * X * X * X * X) : ℚ⟦X⟧) * G) = (1280 - 20480 * X + 122880 * X ^ 2 - 327680 * X ^ 3 + 327680 * X ^ 4) * G + (-64 + 1280 * X - 10240 * X ^ 2 + 40960 * X ^ 3 - 81920 * X ^ 4 + 65536 * X ^ 5) * derivative ℚ G := by
    simp [Derivation.leibniz, d64, d1280, d10240, d40960, d65536, d81920]
    ring
  have hR : derivative ℚ ((64 * X - 768 * (X * X) + 3072 * (X * X * X) - 4096 * (X * X * X * X) : ℚ⟦X⟧) + (-64 * X + 384 * (X * X) - 2048 * (X * X * X * X) : ℚ⟦X⟧) * S) =
      64 - 1536 * X + 9216 * X ^ 2 - 16384 * X ^ 3 + (-64 + 768 * X - 8192 * X ^ 3) * S + (-64 * X + 384 * X ^ 2 - 2048 * X ^ 4) * derivative ℚ S := by
    simp [Derivation.leibniz, d64, d384, d768, d2048, d3072, d4096]
    ring
  have hk2 : (-64 + 1280 * X - 10240 * (X * X) + 40960 * (X * X * X) - 81920 * (X * X * X * X) + 65536 * (X * X * X * X * X) : ℚ⟦X⟧) * G = (64 * X - 768 * (X * X) + 3072 * (X * X * X) - 4096 * (X * X * X * X) : ℚ⟦X⟧) + (-64 * X + 384 * (X * X) - 2048 * (X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (1280 - 20480 * X + 122880 * X ^ 2 - 327680 * X ^ 3 + 327680 * X ^ 4) * G + (-64 + 1280 * X - 10240 * X ^ 2 + 40960 * X ^ 3 - 81920 * X ^ 4 + 65536 * X ^ 5) * derivative ℚ G =
      64 - 1536 * X + 9216 * X ^ 2 - 16384 * X ^ 3 + (-64 + 768 * X - 8192 * X ^ 3) * S + (-64 * X + 384 * X ^ 2 - 2048 * X ^ 4) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 - 20 * X + 160 * X ^ 2 - 640 * X ^ 3 + 1280 * X ^ 4 - 1024 * X ^ 5) * ((8192 * X - 81920 * X ^ 2 + 196608 * X ^ 3 + 262144 * X ^ 4 - 1048576 * X ^ 5) * derivative ℚ G + (-8192 - 16384 * X + 491520 * X ^ 2 - 1048576 * X ^ 3 - 524288 * X ^ 4) * G - (32768 * X ^ 2 - 32768 * X ^ 3)) = 0 := by
    linear_combination (-64 * X + 384 * X ^ 2 - 2048 * X ^ 4) ^ 2 * S * hdS - 2 * (-64 * X + 384 * X ^ 2 - 2048 * X ^ 4) ^ 2 * derivative ℚ S * hS -
      (2 * (-64 + 768 * X - 8192 * X ^ 3) * (1 - 4 * X) + (-64 * X + 384 * X ^ 2 - 2048 * X ^ 4) * (-4)) * hk + 2 * (-64 * X + 384 * X ^ 2 - 2048 * X ^ 4) * (1 - 4 * X) * hdk
  have hg : (1 - 20 * X + 160 * X ^ 2 - 640 * X ^ 3 + 1280 * X ^ 4 - 1024 * X ^ 5 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (0 + (8 - 64 * X + 128 * X ^ 2) * S) = 8 * X + 16 * X ^ 2 + (-8 * X) * S) :
    (-X ^ 3 + 8 * X ^ 4 - 16 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (X ^ 2 + 22 * X ^ 3 - 104 * X ^ 4) * derivative ℚ (derivative ℚ G) + (-2 * X - 2 * X ^ 2 - 128 * X ^ 3) * derivative ℚ G + (2 + 2 * X - 16 * X ^ 2) * G =
      0 := by
  have h := key S G hS hG
  have d8192 : derivative ℚ (8192 : ℚ⟦X⟧) = 0 := dnum 8192
  have d16384 : derivative ℚ (16384 : ℚ⟦X⟧) = 0 := dnum 16384
  have d32768 : derivative ℚ (32768 : ℚ⟦X⟧) = 0 := dnum 32768
  have d65536 : derivative ℚ (65536 : ℚ⟦X⟧) = 0 := dnum 65536
  have d81920 : derivative ℚ (81920 : ℚ⟦X⟧) = 0 := dnum 81920
  have d98304 : derivative ℚ (98304 : ℚ⟦X⟧) = 0 := dnum 98304
  have d163840 : derivative ℚ (163840 : ℚ⟦X⟧) = 0 := dnum 163840
  have d196608 : derivative ℚ (196608 : ℚ⟦X⟧) = 0 := dnum 196608
  have d262144 : derivative ℚ (262144 : ℚ⟦X⟧) = 0 := dnum 262144
  have d491520 : derivative ℚ (491520 : ℚ⟦X⟧) = 0 := dnum 491520
  have d524288 : derivative ℚ (524288 : ℚ⟦X⟧) = 0 := dnum 524288
  have d589824 : derivative ℚ (589824 : ℚ⟦X⟧) = 0 := dnum 589824
  have d983040 : derivative ℚ (983040 : ℚ⟦X⟧) = 0 := dnum 983040
  have d1048576 : derivative ℚ (1048576 : ℚ⟦X⟧) = 0 := dnum 1048576
  have d2097152 : derivative ℚ (2097152 : ℚ⟦X⟧) = 0 := dnum 2097152
  have d3145728 : derivative ℚ (3145728 : ℚ⟦X⟧) = 0 := dnum 3145728
  have d5242880 : derivative ℚ (5242880 : ℚ⟦X⟧) = 0 := dnum 5242880
  have hL : derivative ℚ ((8192 * X - 81920 * (X * X) + 196608 * (X * X * X) + 262144 * (X * X * X * X) - 1048576 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-8192 - 16384 * X + 491520 * (X * X) - 1048576 * (X * X * X) - 524288 * (X * X * X * X) : ℚ⟦X⟧) * G) =
      (8192 - 163840 * X + 589824 * X ^ 2 + 1048576 * X ^ 3 - 5242880 * X ^ 4) * derivative ℚ G + (8192 * X - 81920 * X ^ 2 + 196608 * X ^ 3 + 262144 * X ^ 4 - 1048576 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-16384 + 983040 * X - 3145728 * X ^ 2 - 2097152 * X ^ 3) * G + (-8192 - 16384 * X + 491520 * X ^ 2 - 1048576 * X ^ 3 - 524288 * X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d8192, d16384, d81920, d196608, d262144, d491520, d524288, d1048576]
    ring
  have hRd : derivative ℚ (32768 * (X * X) - 32768 * (X * X * X) : ℚ⟦X⟧) = 65536 * X - 98304 * X ^ 2 := by
    simp [Derivation.leibniz, d32768]
    ring
  have h2 : (8192 * X - 81920 * (X * X) + 196608 * (X * X * X) + 262144 * (X * X * X * X) - 1048576 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-8192 - 16384 * X + 491520 * (X * X) - 1048576 * (X * X * X) - 524288 * (X * X * X * X) : ℚ⟦X⟧) * G = (32768 * (X * X) - 32768 * (X * X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (8192 - 163840 * X + 589824 * X ^ 2 + 1048576 * X ^ 3 - 5242880 * X ^ 4) * derivative ℚ G + (8192 * X - 81920 * X ^ 2 + 196608 * X ^ 3 + 262144 * X ^ 4 - 1048576 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-16384 + 983040 * X - 3145728 * X ^ 2 - 2097152 * X ^ 3) * G + (-8192 - 16384 * X + 491520 * X ^ 2 - 1048576 * X ^ 3 - 524288 * X ^ 4) * derivative ℚ G = 65536 * X - 98304 * X ^ 2 := by
    rw [← hL, h2, hRd]
  have hL2 : derivative ℚ ((8192 - 163840 * X + 589824 * (X * X) + 1048576 * (X * X * X) - 5242880 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (8192 * X - 81920 * (X * X) + 196608 * (X * X * X) + 262144 * (X * X * X * X) - 1048576 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-16384 + 983040 * X - 3145728 * (X * X) - 2097152 * (X * X * X) : ℚ⟦X⟧) * G + (-8192 - 16384 * X + 491520 * (X * X) - 1048576 * (X * X * X) - 524288 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G) =
      (-196608 + 3145728 * X - 3145728 * X ^ 2 - 25165824 * X ^ 3) * derivative ℚ G + (8192 - 344064 * X + 1671168 * X ^ 2 + 1048576 * X ^ 3 - 11010048 * X ^ 4) * derivative ℚ (derivative ℚ G) + (8192 * X - 81920 * X ^ 2 + 196608 * X ^ 3 + 262144 * X ^ 4 - 1048576 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (983040 - 6291456 * X - 6291456 * X ^ 2) * G := by
    simp [Derivation.leibniz, d8192, d16384, d81920, d163840, d196608, d262144, d491520, d524288, d589824, d983040, d1048576, d2097152, d3145728, d5242880]
    ring
  have hRd2 : derivative ℚ (65536 * X - 98304 * (X * X) : ℚ⟦X⟧) = 65536 - 196608 * X := by
    simp [Derivation.leibniz, d65536, d98304]
    ring
  have hdp : (8192 - 163840 * X + 589824 * (X * X) + 1048576 * (X * X * X) - 5242880 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (8192 * X - 81920 * (X * X) + 196608 * (X * X * X) + 262144 * (X * X * X * X) - 1048576 * (X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) + (-16384 + 983040 * X - 3145728 * (X * X) - 2097152 * (X * X * X) : ℚ⟦X⟧) * G + (-8192 - 16384 * X + 491520 * (X * X) - 1048576 * (X * X * X) - 524288 * (X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G = (65536 * X - 98304 * (X * X) : ℚ⟦X⟧) := by linear_combination hd
  have hd2 : (-196608 + 3145728 * X - 3145728 * X ^ 2 - 25165824 * X ^ 3) * derivative ℚ G + (8192 - 344064 * X + 1671168 * X ^ 2 + 1048576 * X ^ 3 - 11010048 * X ^ 4) * derivative ℚ (derivative ℚ G) + (8192 * X - 81920 * X ^ 2 + 196608 * X ^ 3 + 262144 * X ^ 4 - 1048576 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (983040 - 6291456 * X - 6291456 * X ^ 2) * G = 65536 - 196608 * X := by
    rw [← hL2, hdp, hRd2]
  have hfull : (8192 - 32768 * X - 98304 * X ^ 2 + 262144 * X ^ 3 + 524288 * X ^ 4) * ((-X ^ 3 + 8 * X ^ 4 - 16 * X ^ 5) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (X ^ 2 + 22 * X ^ 3 - 104 * X ^ 4) * derivative ℚ (derivative ℚ G) + (-2 * X - 2 * X ^ 2 - 128 * X ^ 3) * derivative ℚ G + (2 + 2 * X - 16 * X ^ 2) * G - (0)) = 0 := by
    linear_combination (-X ^ 2 + 2 * X ^ 3 + 8 * X ^ 4) * hd2 + (2 * X - 6 * X ^ 2 - 32 * X ^ 3) * hd + (-2 + 6 * X + 48 * X ^ 2) * h
  have hg : (8192 - 32768 * X - 98304 * X ^ 2 + 262144 * X ^ 3 + 524288 * X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (8192 : ℚ⟦X⟧) = 8192 := cnum 8192
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (0 + (8 - 64 * X + 128 * X ^ 2) * S) = 8 * X + 16 * X ^ 2 + (-8 * X) * S) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C (-1) + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C 8 +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C (-16) + derivative ℚ (derivative ℚ G) * X * X * C 1 +
      derivative ℚ (derivative ℚ G) * X * X * X * C 22 + derivative ℚ (derivative ℚ G) * X * X * X * X * C (-104) +
      derivative ℚ G * X * C (-2) + derivative ℚ G * X * X * C (-2) +
      derivative ℚ G * X * X * X * C (-128) + G * C 2 +
      G * X * C 2 + G * X * X * C (-16) =
      0 := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (0 + (8 - 64 * X + 128 * X ^ 2) * S) = 8 * X + 16 * X ^ 2 + (-8 * X) * S) (m : ℕ) :
    (-1) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 8 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-16) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + 1 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      22 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-104) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-2) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-2) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-128) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 2 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      2 * coeff (m + 1 + 1 + 1 + 1) G + (-16) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (0 + (8 - 64 * X + 128 * X ^ 2) * S) = 8 * X + 16 * X ^ 2 + (-8 * X) * S) :
    2 * coeff (0 + 1 + 1) G + (-4) * coeff (0 + 1 + 1) G +
      (-2) * coeff (0 + 1) G + 2 * coeff (0 + 1 + 1) G +
      2 * coeff (0 + 1) G + (-16) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (0 + (8 - 64 * X + 128 * X ^ 2) * S) = 8 * X + 16 * X ^ 2 + (-8 * X) * S) :
    (-6) * coeff (0 + 1 + 1 + 1) G + 6 * coeff (0 + 1 + 1 + 1) G +
      44 * coeff (0 + 1 + 1) G + (-6) * coeff (0 + 1 + 1 + 1) G +
      (-4) * coeff (0 + 1 + 1) G + (-128) * coeff (0 + 1) G +
      2 * coeff (0 + 1 + 1 + 1) G + 2 * coeff (0 + 1 + 1) G +
      (-16) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (0 + (8 - 64 * X + 128 * X ^ 2) * S) = 8 * X + 16 * X ^ 2 + (-8 * X) * S) :
    (-24) * coeff (0 + 1 + 1 + 1 + 1) G + 48 * coeff (0 + 1 + 1 + 1) G +
      12 * coeff (0 + 1 + 1 + 1 + 1) G + 132 * coeff (0 + 1 + 1 + 1) G +
      (-208) * coeff (0 + 1 + 1) G + (-8) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-6) * coeff (0 + 1 + 1 + 1) G + (-256) * coeff (0 + 1 + 1) G +
      2 * coeff (0 + 1 + 1 + 1 + 1) G + 2 * coeff (0 + 1 + 1 + 1) G +
      (-16) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A118447Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a118447.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  cases m with
  | zero =>
    have r := A118447Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG - (8 * G * S * (S ^ 2 + (1 - 4 * PowerSeries.X)) - (S ^ 2 + (1 - 4 * PowerSeries.X) + 2 * S - 4)) * hS)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A118447Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination hG - (8 * G * S * (S ^ 2 + (1 - 4 * PowerSeries.X)) - (S ^ 2 + (1 - 4 * PowerSeries.X) + 2 * S - 4)) * hS)
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A118447Aux.relE2 (S) G (by linear_combination hS)
            (by linear_combination hG - (8 * G * S * (S ^ 2 + (1 - 4 * PowerSeries.X)) - (S ^ 2 + (1 - 4 * PowerSeries.X) + 2 * S - 4)) * hS)
        push_cast
        linear_combination r
      | succ m =>
        have r := A118447Aux.rel (S) G (by linear_combination hS)
            (by linear_combination hG - (8 * G * S * (S ^ 2 + (1 - 4 * PowerSeries.X)) - (S ^ 2 + (1 - 4 * PowerSeries.X) + 2 * S - 4)) * hS) m
        push_cast
        linear_combination r
