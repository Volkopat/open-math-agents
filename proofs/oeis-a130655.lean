import OMAStatements.S_oeis_a130655

-- Problem: A130655: Catalan transform of Catalan numbers C(n+1).
-- Upstream: formal-conjectures statements/oeis-a130655.lean:0 (declaration OMA.S_oeis_a130655.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A130655Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (2 * X : ℚ⟦X⟧) * G ^ 2 + (-1 + 4 * X : ℚ⟦X⟧) * G ^ 3 + (X ^ 2 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    (3 * X ^ 3 - 40 * X ^ 4 + 176 * X ^ 5 - 256 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (9 * X ^ 2 - 156 * X ^ 3 + 832 * X ^ 4 - 1408 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-9 * X + 496 * X ^ 3 - 1392 * X ^ 4) * derivative ℚ G + (12 * X - 16 * X ^ 2 - 120 * X ^ 3) * G =
      -6 * X + 8 * X ^ 2 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have hp0 : (1 : ℚ⟦X⟧) + (2 * X : ℚ⟦X⟧) * G * G + (-1 + 4 * X : ℚ⟦X⟧) * G * G * G + (1 * (X * X) : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 : ℚ⟦X⟧) + (2 * X : ℚ⟦X⟧) * G * G + (-1 + 4 * X : ℚ⟦X⟧) * G * G * G + (1 * (X * X) : ℚ⟦X⟧) * G * G * G * G) =
      (4 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G ^ 2 + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 3 + (4 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G ^ 4 := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hd1 : (4 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G ^ 2 + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 3 + (4 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G ^ 4 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (4 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G * G + (-3 + 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G + (4 * (X * X) : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((4 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G * G + (-3 + 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G + (4 * (X * X) : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (2 * X : ℚ⟦X⟧) * G * G * G * G) =
      (4 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (4 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 + 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (12 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (16 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G ^ 4 := by
    simp [Derivation.leibniz, d2, d3, d4, d12]
    ring
  have hd2 : (4 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (4 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 + 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (12 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (16 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G ^ 4 = 0 := by rw [← hL2, hp1, map_zero]
  have hp2 : (4 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (4 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 + 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (-3 + 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (12 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (4 * (X * X) : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) + (16 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hd2
  have hL3 : derivative ℚ ((4 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (4 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 + 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (-3 + 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (12 * (X * X) : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (4 * (X * X) : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) + (16 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G * G * G * G) =
      (12 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-6 + 24 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (4 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (12 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-18 + 72 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (72 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (24 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (36 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (72 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (24 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d2, d3, d4, d6, d8, d12, d16, d24]
    ring
  have hd3 : (12 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-6 + 24 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (4 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (12 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-18 + 72 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (72 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (24 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (36 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (72 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (24 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) = 0 := by rw [← hL3, hp2, map_zero]
  have hfull : ((4 * X : ℚ⟦X⟧) * G + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 + (4 * X ^ 2 : ℚ⟦X⟧) * G ^ 3) ^ 5 * ((3 * X ^ 3 - 40 * X ^ 4 + 176 * X ^ 5 - 256 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (9 * X ^ 2 - 156 * X ^ 3 + 832 * X ^ 4 - 1408 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-9 * X + 496 * X ^ 3 - 1392 * X ^ 4) * derivative ℚ G + (12 * X - 16 * X ^ 2 - 120 * X ^ 3) * G - (-6 * X + 8 * X ^ 2)) = 0 := by
    linear_combination ((6144 * X ^ 6 - 8192 * X ^ 7 : ℚ⟦X⟧) * G ^ 5 + (-17280 * X ^ 5 + 92160 * X ^ 6 - 92160 * X ^ 7 : ℚ⟦X⟧) * G ^ 6 + (11520 * X ^ 4 - 107520 * X ^ 5 + 307200 * X ^ 6 - 233472 * X ^ 7 - 16384 * X ^ 8 : ℚ⟦X⟧) * G ^ 7 + (-2160 * X ^ 3 + 28800 * X ^ 4 - 138240 * X ^ 5 + 302976 * X ^ 6 - 325632 * X ^ 7 + 141312 * X ^ 8 : ℚ⟦X⟧) * G ^ 8 + (-40320 * X ^ 5 + 376320 * X ^ 6 - 1075200 * X ^ 7 + 866304 * X ^ 8 - 8192 * X ^ 9 : ℚ⟦X⟧) * G ^ 9 + (11664 * X ^ 4 - 155520 * X ^ 5 + 746496 * X ^ 6 - 1461888 * X ^ 7 + 829440 * X ^ 8 + 165888 * X ^ 9 : ℚ⟦X⟧) * G ^ 10 + (-17280 * X ^ 6 + 161280 * X ^ 7 - 460800 * X ^ 8 + 368640 * X ^ 9 : ℚ⟦X⟧) * G ^ 11 + (5760 * X ^ 8 - 30720 * X ^ 9 + 30720 * X ^ 10 : ℚ⟦X⟧) * G ^ 12) * hP +
      ((2304 * X ^ 7 - 30720 * X ^ 8 + 135168 * X ^ 9 - 196608 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (1152 * X ^ 6 - 6144 * X ^ 7 - 10240 * X ^ 8 + 65536 * X ^ 9 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-9216 * X ^ 6 + 159744 * X ^ 7 - 1032192 * X ^ 8 + 2949120 * X ^ 9 - 3145728 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) ^ 2 + (-2880 * X ^ 5 + 21504 * X ^ 6 - 23552 * X ^ 7 - 61440 * X ^ 8 : ℚ⟦X⟧) * G ^ 4 + (-3168 * X ^ 5 + 24960 * X ^ 6 + 13824 * X ^ 7 - 497664 * X ^ 8 + 983040 * X ^ 9 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (14256 * X ^ 5 - 304128 * X ^ 6 + 2585088 * X ^ 7 - 10934784 * X ^ 8 + 22929408 * X ^ 9 - 18653184 * X ^ 10 - 1179648 * X ^ 11 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) ^ 2 + (11520 * X ^ 4 - 124800 * X ^ 5 + 387072 * X ^ 6 - 88064 * X ^ 7 - 802816 * X ^ 8 : ℚ⟦X⟧) * G ^ 5 + (-432 * X ^ 4 + 32256 * X ^ 5 - 436224 * X ^ 6 + 2421504 * X ^ 7 - 6119424 * X ^ 8 + 5738496 * X ^ 9 + 393216 * X ^ 10 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-9720 * X ^ 4 + 246240 * X ^ 5 - 2592000 * X ^ 6 + 14470272 * X ^ 7 - 44840448 * X ^ 8 + 71276544 * X ^ 9 - 38707200 * X ^ 10 - 15335424 * X ^ 11 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) ^ 2 + (-11880 * X ^ 3 + 169920 * X ^ 4 - 833280 * X ^ 5 + 1286400 * X ^ 6 + 1416192 * X ^ 7 - 4227072 * X ^ 8 - 81920 * X ^ 9 : ℚ⟦X⟧) * G ^ 6 + (3564 * X ^ 3 - 91152 * X ^ 4 + 944640 * X ^ 5 - 5099616 * X ^ 6 + 15108480 * X ^ 7 - 22927872 * X ^ 8 + 12429312 * X ^ 9 + 3342336 * X ^ 10 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (2430 * X ^ 3 - 71280 * X ^ 4 + 894240 * X ^ 5 - 6174144 * X ^ 6 + 24924672 * X ^ 7 - 56236032 * X ^ 8 + 53784576 * X ^ 9 + 22069248 * X ^ 10 - 61538304 * X ^ 11 - 3145728 * X ^ 12 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) ^ 2 + (4860 * X ^ 2 - 86400 * X ^ 3 + 576000 * X ^ 4 - 1557312 * X ^ 5 + 35712 * X ^ 6 + 7670784 * X ^ 7 - 10283008 * X ^ 8 - 770048 * X ^ 9 : ℚ⟦X⟧) * G ^ 7 + (-1458 * X ^ 2 + 40176 * X ^ 3 - 465696 * X ^ 4 + 2932848 * X ^ 5 - 10721664 * X ^ 6 + 22084608 * X ^ 7 - 21192192 * X ^ 8 + 577536 * X ^ 9 + 9658368 * X ^ 10 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (-15552 * X ^ 5 + 393984 * X ^ 6 - 4147200 * X ^ 7 + 23148288 * X ^ 8 - 71672832 * X ^ 9 + 113577984 * X ^ 10 - 60604416 * X ^ 11 - 25952256 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) ^ 2 + (-729 * X + 15552 * X ^ 2 - 131760 * X ^ 3 + 497520 * X ^ 4 - 267840 * X ^ 5 - 4212480 * X ^ 6 + 13022592 * X ^ 7 - 11056128 * X ^ 8 - 2746368 * X ^ 9 - 73728 * X ^ 10 : ℚ⟦X⟧) * G ^ 8 + (4536 * X ^ 4 - 108000 * X ^ 5 + 1031040 * X ^ 6 - 5046048 * X ^ 7 + 13290624 * X ^ 8 - 17776128 * X ^ 9 + 9811968 * X ^ 10 - 1376256 * X ^ 11 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (37584 * X ^ 7 - 801792 * X ^ 8 + 6815232 * X ^ 9 - 28823040 * X ^ 10 + 60383232 * X ^ 11 - 48881664 * X ^ 12 - 3538944 * X ^ 13 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) ^ 2 + (7776 * X ^ 3 - 151200 * X ^ 4 + 1163520 * X ^ 5 - 4348608 * X ^ 6 + 7396992 * X ^ 7 - 2595840 * X ^ 8 - 4413440 * X ^ 9 - 507904 * X ^ 10 : ℚ⟦X⟧) * G ^ 9 + (3456 * X ^ 6 - 61056 * X ^ 7 + 476160 * X ^ 8 - 2034432 * X ^ 9 + 4558848 * X ^ 10 - 3837952 * X ^ 11 - 917504 * X ^ 12 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (-40320 * X ^ 9 + 698880 * X ^ 10 - 4515840 * X ^ 11 + 12902400 * X ^ 12 - 13762560 * X ^ 13 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) ^ 2 + (-14472 * X ^ 5 + 226944 * X ^ 6 - 1310208 * X ^ 7 + 3223296 * X ^ 8 - 2472960 * X ^ 9 - 1064960 * X ^ 10 - 147456 * X ^ 11 : ℚ⟦X⟧) * G ^ 10 + (-18720 * X ^ 8 + 280704 * X ^ 9 - 1580544 * X ^ 10 + 3962880 * X ^ 11 - 3735552 * X ^ 12 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (16128 * X ^ 11 - 215040 * X ^ 12 + 946176 * X ^ 13 - 1376256 * X ^ 14 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) ^ 2 + (8064 * X ^ 7 - 90240 * X ^ 8 + 294912 * X ^ 9 - 116736 * X ^ 10 - 540672 * X ^ 11 : ℚ⟦X⟧) * G ^ 11 + (12672 * X ^ 10 - 141312 * X ^ 11 + 509952 * X ^ 12 - 589824 * X ^ 13 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (-576 * X ^ 9 + 33792 * X ^ 11 - 94208 * X ^ 12 : ℚ⟦X⟧) * G ^ 12) * hd1 +
      ((-2304 * X ^ 7 + 30720 * X ^ 8 - 135168 * X ^ 9 + 196608 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-9216 * X ^ 7 + 77824 * X ^ 8 - 163840 * X ^ 9 : ℚ⟦X⟧) * G ^ 4 + (8640 * X ^ 6 - 149760 * X ^ 7 + 967680 * X ^ 8 - 2764800 * X ^ 9 + 2949120 * X ^ 10 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (-1728 * X ^ 5 + 50688 * X ^ 6 - 445440 * X ^ 7 + 1572864 * X ^ 8 - 1966080 * X ^ 9 : ℚ⟦X⟧) * G ^ 5 + (-11664 * X ^ 5 + 248832 * X ^ 6 - 2115072 * X ^ 7 + 8944128 * X ^ 8 - 18726912 * X ^ 9 + 15114240 * X ^ 10 + 1179648 * X ^ 11 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (3888 * X ^ 4 - 98496 * X ^ 5 + 946944 * X ^ 6 - 4398336 * X ^ 7 + 9947136 * X ^ 8 - 8671232 * X ^ 9 - 458752 * X ^ 10 : ℚ⟦X⟧) * G ^ 6 + (6804 * X ^ 4 - 172368 * X ^ 5 + 1814400 * X ^ 6 - 10124352 * X ^ 7 + 31304448 * X ^ 8 - 49351680 * X ^ 9 + 25546752 * X ^ 10 + 12386304 * X ^ 11 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (-2916 * X ^ 3 + 77760 * X ^ 4 - 846720 * X ^ 5 + 4838400 * X ^ 6 - 15282432 * X ^ 7 + 24901632 * X ^ 8 - 14635008 * X ^ 9 - 4128768 * X ^ 10 : ℚ⟦X⟧) * G ^ 7 + (-1458 * X ^ 3 + 42768 * X ^ 4 - 536544 * X ^ 5 + 3701376 * X ^ 6 - 14888448 * X ^ 7 + 33177600 * X ^ 8 - 29887488 * X ^ 9 - 18210816 * X ^ 10 + 40845312 * X ^ 11 + 2359296 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (729 * X ^ 2 - 21384 * X ^ 3 + 265680 * X ^ 4 - 1810512 * X ^ 5 + 7247232 * X ^ 6 - 16561152 * X ^ 7 + 17743104 * X ^ 8 + 368640 * X ^ 9 - 12324864 * X ^ 10 - 393216 * X ^ 11 : ℚ⟦X⟧) * G ^ 8 + (8748 * X ^ 5 - 221616 * X ^ 6 + 2332800 * X ^ 7 - 13017024 * X ^ 8 + 40248576 * X ^ 9 - 63452160 * X ^ 10 + 32845824 * X ^ 11 + 15925248 * X ^ 12 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (-1944 * X ^ 4 + 53136 * X ^ 5 - 587520 * X ^ 6 + 3392064 * X ^ 7 - 10810368 * X ^ 8 + 17851392 * X ^ 9 - 10985472 * X ^ 10 - 2359296 * X ^ 11 : ℚ⟦X⟧) * G ^ 9 + (-19440 * X ^ 7 + 414720 * X ^ 8 - 3525120 * X ^ 9 + 14906880 * X ^ 10 - 31211520 * X ^ 11 + 25190400 * X ^ 12 + 1966080 * X ^ 13 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (-15552 * X ^ 7 + 241920 * X ^ 8 - 1416960 * X ^ 9 + 3704832 * X ^ 10 - 3633152 * X ^ 11 - 65536 * X ^ 12 : ℚ⟦X⟧) * G ^ 10 + (19008 * X ^ 9 - 329472 * X ^ 10 + 2128896 * X ^ 11 - 6082560 * X ^ 12 + 6488064 * X ^ 13 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (3456 * X ^ 8 - 39168 * X ^ 9 + 135168 * X ^ 10 - 86016 * X ^ 11 - 196608 * X ^ 12 : ℚ⟦X⟧) * G ^ 11 + (-6912 * X ^ 11 + 92160 * X ^ 12 - 405504 * X ^ 13 + 589824 * X ^ 14 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (-2304 * X ^ 10 + 21504 * X ^ 11 - 57344 * X ^ 12 + 32768 * X ^ 13 : ℚ⟦X⟧) * G ^ 12) * hd2 +
      ((768 * X ^ 7 - 10240 * X ^ 8 + 45056 * X ^ 9 - 65536 * X ^ 10 : ℚ⟦X⟧) * G ^ 4 + (-2304 * X ^ 6 + 39936 * X ^ 7 - 258048 * X ^ 8 + 737280 * X ^ 9 - 786432 * X ^ 10 : ℚ⟦X⟧) * G ^ 5 + (2592 * X ^ 5 - 55296 * X ^ 6 + 470016 * X ^ 7 - 1987584 * X ^ 8 + 4161536 * X ^ 9 - 3358720 * X ^ 10 - 262144 * X ^ 11 : ℚ⟦X⟧) * G ^ 6 + (-1296 * X ^ 4 + 32832 * X ^ 5 - 345600 * X ^ 6 + 1928448 * X ^ 7 - 5962752 * X ^ 8 + 9400320 * X ^ 9 - 4866048 * X ^ 10 - 2359296 * X ^ 11 : ℚ⟦X⟧) * G ^ 7 + (243 * X ^ 3 - 7128 * X ^ 4 + 89424 * X ^ 5 - 616896 * X ^ 6 + 2481408 * X ^ 7 - 5529600 * X ^ 8 + 4981248 * X ^ 9 + 3035136 * X ^ 10 - 6807552 * X ^ 11 - 393216 * X ^ 12 : ℚ⟦X⟧) * G ^ 8 + (-1296 * X ^ 5 + 32832 * X ^ 6 - 345600 * X ^ 7 + 1928448 * X ^ 8 - 5962752 * X ^ 9 + 9400320 * X ^ 10 - 4866048 * X ^ 11 - 2359296 * X ^ 12 : ℚ⟦X⟧) * G ^ 9 + (2592 * X ^ 7 - 55296 * X ^ 8 + 470016 * X ^ 9 - 1987584 * X ^ 10 + 4161536 * X ^ 11 - 3358720 * X ^ 12 - 262144 * X ^ 13 : ℚ⟦X⟧) * G ^ 10 + (-2304 * X ^ 9 + 39936 * X ^ 10 - 258048 * X ^ 11 + 737280 * X ^ 12 - 786432 * X ^ 13 : ℚ⟦X⟧) * G ^ 11 + (768 * X ^ 11 - 10240 * X ^ 12 + 45056 * X ^ 13 - 65536 * X ^ 14 : ℚ⟦X⟧) * G ^ 12) * hd3
  have k3 : constantCoeff (3 : ℚ⟦X⟧) = 3 := cnum 3
  have hPG : (4 * X : ℚ⟦X⟧) * G + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 + (4 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k3] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 5 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (2 * X : ℚ⟦X⟧) * G ^ 2 + (-1 + 4 * X : ℚ⟦X⟧) * G ^ 3 + (X ^ 2 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 3 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-40) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C 176 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C (-256) +
      derivative ℚ (derivative ℚ G) * X * X * C 9 + derivative ℚ (derivative ℚ G) * X * X * X * C (-156) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 832 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-1408) +
      derivative ℚ G * X * C (-9) + derivative ℚ G * X * X * X * C 496 +
      derivative ℚ G * X * X * X * X * C (-1392) + G * X * C 12 +
      G * X * X * C (-16) + G * X * X * X * C (-120) =
      C (-6) * X + C 8 * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (2 * X : ℚ⟦X⟧) * G ^ 2 + (-1 + 4 * X : ℚ⟦X⟧) * G ^ 3 + (X ^ 2 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) (m : ℕ) :
    3 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-40) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      176 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G + (-256) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G +
      9 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-156) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      832 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-1408) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-9) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 496 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-1392) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 12 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-16) * coeff (m + 1 + 1 + 1 + 1) G + (-120) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (2 * X : ℚ⟦X⟧) * G ^ 2 + (-1 + 4 * X : ℚ⟦X⟧) * G ^ 3 + (X ^ 2 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    18 * coeff (0 + 1 + 1 + 1) G + 54 * coeff (0 + 1 + 1 + 1) G +
      (-312) * coeff (0 + 1 + 1) G + (-27) * coeff (0 + 1 + 1 + 1) G +
      496 * coeff (0 + 1) G + 12 * coeff (0 + 1 + 1) G +
      (-16) * coeff (0 + 1) G + (-120) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (2 * X : ℚ⟦X⟧) * G ^ 2 + (-1 + 4 * X : ℚ⟦X⟧) * G ^ 3 + (X ^ 2 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    72 * coeff (0 + 1 + 1 + 1 + 1) G + (-240) * coeff (0 + 1 + 1 + 1) G +
      108 * coeff (0 + 1 + 1 + 1 + 1) G + (-936) * coeff (0 + 1 + 1 + 1) G +
      1664 * coeff (0 + 1 + 1) G + (-36) * coeff (0 + 1 + 1 + 1 + 1) G +
      992 * coeff (0 + 1 + 1) G + (-1392) * coeff (0 + 1) G +
      12 * coeff (0 + 1 + 1 + 1) G + (-16) * coeff (0 + 1 + 1) G +
      (-120) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE2 (G : ℚ⟦X⟧)
    (hP : (1 : ℚ⟦X⟧) + (2 * X : ℚ⟦X⟧) * G ^ 2 + (-1 + 4 * X : ℚ⟦X⟧) * G ^ 3 + (X ^ 2 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    180 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-960) * coeff (0 + 1 + 1 + 1 + 1) G +
      1056 * coeff (0 + 1 + 1 + 1) G + 180 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-1872) * coeff (0 + 1 + 1 + 1 + 1) G + 4992 * coeff (0 + 1 + 1 + 1) G +
      (-2816) * coeff (0 + 1 + 1) G + (-45) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      1488 * coeff (0 + 1 + 1 + 1) G + (-2784) * coeff (0 + 1 + 1) G +
      12 * coeff (0 + 1 + 1 + 1 + 1) G + (-16) * coeff (0 + 1 + 1 + 1) G +
      (-120) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A130655Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a130655.main := by
  intro T U V G hT _ hU hV _ hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  have e3 : m + 1 + 1 + 1 - 3 = m := rfl
  rw [e1, e2, e3]
  have hV2 : V ^ 2 = 2 * T - 1 := by linear_combination hV - 2 * hU
  have hG2 : G * (1 - T) ^ 2 = 2 * (T - V) := by linear_combination 2 * hG - (G * (1 - T + 2 * PowerSeries.X * U) + 2) * hU
  have hn : ((1) + (-2) * T + (1) * T ^ 2) * ((1) + (2) * T + (-1) * T ^ 2 + (-4) * T ^ 3 + (-1) * T ^ 4 + (2) * T ^ 5 + (1) * T ^ 6) = (256 * PowerSeries.X ^ 4 : PowerSeries ℚ) := by
    linear_combination ((-1) + (3) * T ^ 2 + (-3) * T ^ 4 + (1) * T ^ 6 + (-4) * PowerSeries.X + (8) * PowerSeries.X * T ^ 2 + (-4) * PowerSeries.X * T ^ 4 + (-16) * PowerSeries.X ^ 2 + (16) * PowerSeries.X ^ 2 * T ^ 2 + (-64) * PowerSeries.X ^ 3) * hT
  have hnu0 : (256 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    have kc : PowerSeries.constantCoeff (256 : PowerSeries ℚ) = 256 := A130655Aux.cnum 256
    simp [kc] at h'
  have hnu : (256 * PowerSeries.X ^ 4 : PowerSeries ℚ) ≠ 0 := by
    have e : (256 * PowerSeries.X ^ 4 : PowerSeries ℚ) = PowerSeries.X ^ 4 * (256 : PowerSeries ℚ) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 4 PowerSeries.X_ne_zero) hnu0
  have hN1 : ((1) + (-2) * T + (1) * T ^ 2 : PowerSeries ℚ) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hn
    exact hnu hn.symm
  have hM : ((1) + (-2) * T + (1) * T ^ 2) ^ 4 * ((1 : PowerSeries ℚ) + (2 * PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (-1 + 4 * PowerSeries.X : PowerSeries ℚ) * G ^ 3 + (PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 4) = 0 := by
    linear_combination ((-1) + (8) * V + (-16) * T + (-32) * T * V + (67) * T ^ 2 + (24) * T ^ 2 * V + (-72) * T ^ 3 + (29) * T ^ 4 + (-8) * T ^ 5 + (1) * T ^ 6 + (4) * PowerSeries.X + (-16) * PowerSeries.X * T + (16) * PowerSeries.X * T * V + (-8) * PowerSeries.X * T ^ 2 + (-32) * PowerSeries.X * T ^ 2 * V + (48) * PowerSeries.X * T ^ 3 + (-16) * PowerSeries.X * T ^ 3 * V + (4) * PowerSeries.X * T ^ 4) * hT +
      ((8) * V + (-24) * T + (-16) * T * V + (48) * T ^ 2 + (8) * T ^ 2 * V + (-24) * T ^ 3 + (8) * PowerSeries.X + (-32) * PowerSeries.X * V + (64) * PowerSeries.X * T + (64) * PowerSeries.X * T * V + (-144) * PowerSeries.X * T ^ 2 + (-32) * PowerSeries.X * T ^ 2 * V + (64) * PowerSeries.X * T ^ 3 + (8) * PowerSeries.X * T ^ 4 + (-16) * PowerSeries.X ^ 2 + (16) * PowerSeries.X ^ 2 * V ^ 2 + (32) * PowerSeries.X ^ 2 * T + (-64) * PowerSeries.X ^ 2 * T * V + (96) * PowerSeries.X ^ 2 * T ^ 2) * hV2 +
      ((-4) * V ^ 2 + (8) * T * V + (8) * T * V ^ 2 + (-4) * T ^ 2 + (-16) * T ^ 2 * V + (-4) * T ^ 2 * V ^ 2 + (8) * T ^ 3 + (8) * T ^ 3 * V + (-4) * T ^ 4 + (2) * G * V + (-2) * G * T + (-8) * G * T * V + (8) * G * T ^ 2 + (12) * G * T ^ 2 * V + (-12) * G * T ^ 3 + (-8) * G * T ^ 3 * V + (8) * G * T ^ 4 + (2) * G * T ^ 4 * V + (-2) * G * T ^ 5 + (-1) * G ^ 2 + (6) * G ^ 2 * T + (-15) * G ^ 2 * T ^ 2 + (20) * G ^ 2 * T ^ 3 + (-15) * G ^ 2 * T ^ 4 + (6) * G ^ 2 * T ^ 5 + (-1) * G ^ 2 * T ^ 6 + (-4) * PowerSeries.X * V + (16) * PowerSeries.X * V ^ 2 + (4) * PowerSeries.X * T + (-16) * PowerSeries.X * T * V + (-32) * PowerSeries.X * T * V ^ 2 + (40) * PowerSeries.X * T ^ 2 * V + (16) * PowerSeries.X * T ^ 2 * V ^ 2 + (-8) * PowerSeries.X * T ^ 3 + (-16) * PowerSeries.X * T ^ 3 * V + (-4) * PowerSeries.X * T ^ 4 * V + (4) * PowerSeries.X * T ^ 5 + (2) * PowerSeries.X * G + (-8) * PowerSeries.X * G * V + (-4) * PowerSeries.X * G * T + (32) * PowerSeries.X * G * T * V + (-2) * PowerSeries.X * G * T ^ 2 + (-48) * PowerSeries.X * G * T ^ 2 * V + (8) * PowerSeries.X * G * T ^ 3 + (32) * PowerSeries.X * G * T ^ 3 * V + (-2) * PowerSeries.X * G * T ^ 4 + (-8) * PowerSeries.X * G * T ^ 4 * V + (-4) * PowerSeries.X * G * T ^ 5 + (2) * PowerSeries.X * G * T ^ 6 + (4) * PowerSeries.X * G ^ 2 + (-24) * PowerSeries.X * G ^ 2 * T + (60) * PowerSeries.X * G ^ 2 * T ^ 2 + (-80) * PowerSeries.X * G ^ 2 * T ^ 3 + (60) * PowerSeries.X * G ^ 2 * T ^ 4 + (-24) * PowerSeries.X * G ^ 2 * T ^ 5 + (4) * PowerSeries.X * G ^ 2 * T ^ 6 + (-8) * PowerSeries.X ^ 2 * V ^ 3 + (24) * PowerSeries.X ^ 2 * T * V ^ 2 + (-24) * PowerSeries.X ^ 2 * T ^ 2 * V + (8) * PowerSeries.X ^ 2 * T ^ 3 + (4) * PowerSeries.X ^ 2 * G * V ^ 2 + (-8) * PowerSeries.X ^ 2 * G * T * V + (-8) * PowerSeries.X ^ 2 * G * T * V ^ 2 + (4) * PowerSeries.X ^ 2 * G * T ^ 2 + (16) * PowerSeries.X ^ 2 * G * T ^ 2 * V + (4) * PowerSeries.X ^ 2 * G * T ^ 2 * V ^ 2 + (-8) * PowerSeries.X ^ 2 * G * T ^ 3 + (-8) * PowerSeries.X ^ 2 * G * T ^ 3 * V + (4) * PowerSeries.X ^ 2 * G * T ^ 4 + (-2) * PowerSeries.X ^ 2 * G ^ 2 * V + (2) * PowerSeries.X ^ 2 * G ^ 2 * T + (8) * PowerSeries.X ^ 2 * G ^ 2 * T * V + (-8) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 2 + (-12) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 2 * V + (12) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 3 + (8) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 3 * V + (-8) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 4 + (-2) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 4 * V + (2) * PowerSeries.X ^ 2 * G ^ 2 * T ^ 5 + (1) * PowerSeries.X ^ 2 * G ^ 3 + (-6) * PowerSeries.X ^ 2 * G ^ 3 * T + (15) * PowerSeries.X ^ 2 * G ^ 3 * T ^ 2 + (-20) * PowerSeries.X ^ 2 * G ^ 3 * T ^ 3 + (15) * PowerSeries.X ^ 2 * G ^ 3 * T ^ 4 + (-6) * PowerSeries.X ^ 2 * G ^ 3 * T ^ 5 + (1) * PowerSeries.X ^ 2 * G ^ 3 * T ^ 6) * hG2
  have hP : (1 : PowerSeries ℚ) + (2 * PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (-1 + 4 * PowerSeries.X : PowerSeries ℚ) * G ^ 3 + (PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 4 = 0 := (mul_eq_zero.mp hM).resolve_left (pow_ne_zero 4 hN1)
  have h0c : PowerSeries.constantCoeff G = (1 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A130655Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A130655Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A130655Aux.relE2 G hP h0c
        push_cast
        linear_combination r
      | succ m =>
        have r := A130655Aux.rel G hP h0c m
        push_cast
        linear_combination r
