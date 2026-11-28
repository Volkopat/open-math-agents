import OMAStatements.S_oeis_a243814

-- Problem: A243814: Expansion of -(x*(1-sqrt((2*(1-sqrt(4*x^2+1)))/x+1)))/(1-sqrt(4*x^2+1)) - 1.
-- Upstream: formal-conjectures statements/oeis-a243814.lean:0 (declaration OMA.S_oeis_a243814.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A243814Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-2 + 5 * X : ℚ⟦X⟧) * G ^ 2 + (-1 + 4 * X : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (4 * X ^ 3 - 47 * X ^ 4 + 152 * X ^ 5 - 376 * X ^ 6 + 1024 * X ^ 7 - 752 * X ^ 8 + 1920 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (14 * X ^ 2 - 155 * X ^ 3 + 624 * X ^ 4 - 1616 * X ^ 5 + 5152 * X ^ 6 - 3984 * X ^ 7 + 11520 * X ^ 8) * derivative ℚ (derivative ℚ G) + (4 * X - 34 * X ^ 2 + 332 * X ^ 3 - 1188 * X ^ 4 + 4560 * X ^ 5 - 3456 * X ^ 6 + 11520 * X ^ 7) * derivative ℚ G + (-6 * X - 12 * X ^ 2 - 132 * X ^ 3) * G =
      4 * X + 32 * X ^ 2 + 32 * X ^ 3 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d5 : derivative ℚ (5 : ℚ⟦X⟧) = 0 := dnum 5
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d10 : derivative ℚ (10 : ℚ⟦X⟧) = 0 := dnum 10
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d20 : derivative ℚ (20 : ℚ⟦X⟧) = 0 := dnum 20
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have hp0 : (1 * X : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-2 + 5 * X : ℚ⟦X⟧) * G * G + (-1 + 4 * X : ℚ⟦X⟧) * G * G * G + (1 * X : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 * X : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-2 + 5 * X : ℚ⟦X⟧) * G * G + (-1 + 4 * X : ℚ⟦X⟧) * G * G * G + (1 * X : ℚ⟦X⟧) * G * G * G * G) =
      (1 : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G + (-4 + 10 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (5 : ℚ⟦X⟧) * G ^ 2 + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 3 + (4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G ^ 4 := by
    simp [Derivation.leibniz, d2, d4, d5]
    ring
  have hd1 : (1 : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G + (-4 + 10 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (5 : ℚ⟦X⟧) * G ^ 2 + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G ^ 3 + (4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G ^ 4 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (1 : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G + (-4 + 10 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (5 : ℚ⟦X⟧) * G * G + (-3 + 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G + (4 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((1 : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G + (-4 + 10 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (5 : ℚ⟦X⟧) * G * G + (-3 + 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G + (4 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G * G * G * G) =
      (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * (derivative ℚ G) + (-4 + 10 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-4 + 10 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (20 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 + 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d3, d4, d5, d10, d12]
    ring
  have hd2 : (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * (derivative ℚ G) + (-4 + 10 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-4 + 10 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (20 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 + 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) = 0 := by rw [← hL2, hp1, map_zero]
  have hp2 : (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * (derivative ℚ G) + (-4 + 10 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (-4 + 10 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (20 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 + 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (-3 + 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (4 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) = 0 := by linear_combination hd2
  have hL3 : derivative ℚ ((-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * (derivative ℚ G) + (-4 + 10 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (-4 + 10 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (20 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 + 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (-3 + 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (4 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G)) =
      (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (12 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-12 + 30 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (30 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-6 + 24 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (-4 + 10 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (30 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-18 + 72 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (72 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (36 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (12 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d3, d4, d6, d8, d10, d12, d20, d24]
    ring
  have hd3 : (-1 + 4 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (12 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-12 + 30 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (30 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-6 + 24 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (-4 + 10 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (30 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-18 + 72 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (72 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (36 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (12 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) = 0 := by rw [← hL3, hp2, map_zero]
  have hfull : ((-1 + 4 * X : ℚ⟦X⟧) + (-4 + 10 * X : ℚ⟦X⟧) * G + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 + (4 * X : ℚ⟦X⟧) * G ^ 3) ^ 5 * ((4 * X ^ 3 - 47 * X ^ 4 + 152 * X ^ 5 - 376 * X ^ 6 + 1024 * X ^ 7 - 752 * X ^ 8 + 1920 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (14 * X ^ 2 - 155 * X ^ 3 + 624 * X ^ 4 - 1616 * X ^ 5 + 5152 * X ^ 6 - 3984 * X ^ 7 + 11520 * X ^ 8) * derivative ℚ (derivative ℚ G) + (4 * X - 34 * X ^ 2 + 332 * X ^ 3 - 1188 * X ^ 4 + 4560 * X ^ 5 - 3456 * X ^ 6 + 11520 * X ^ 7) * derivative ℚ G + (-6 * X - 12 * X ^ 2 - 132 * X ^ 3) * G - (4 * X + 32 * X ^ 2 + 32 * X ^ 3)) = 0 := by
    linear_combination ((-6 * X + 52 * X ^ 2 + 666 * X ^ 3 - 12296 * X ^ 4 + 74164 * X ^ 5 - 226272 * X ^ 6 + 469952 * X ^ 7 - 809600 * X ^ 8 + 760128 * X ^ 9 - 391680 * X ^ 10 : ℚ⟦X⟧) + (-100 * X + 936 * X ^ 2 + 6256 * X ^ 3 - 136188 * X ^ 4 + 837712 * X ^ 5 - 2702368 * X ^ 6 + 5955712 * X ^ 7 - 10144960 * X ^ 8 + 10149120 * X ^ 9 - 5253120 * X ^ 10 : ℚ⟦X⟧) * G + (-700 * X + 7484 * X ^ 2 + 12178 * X ^ 3 - 604816 * X ^ 4 + 4040304 * X ^ 5 - 13850752 * X ^ 6 + 32225696 * X ^ 7 - 54920960 * X ^ 8 + 57504768 * X ^ 9 - 30827520 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 + (-2656 * X + 34416 * X ^ 2 - 71488 * X ^ 3 - 1333848 * X ^ 4 + 10892832 * X ^ 5 - 40513728 * X ^ 6 + 100376832 * X ^ 7 - 173566336 * X ^ 8 + 187912704 * X ^ 9 - 105984000 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 + (-5856 * X + 98800 * X ^ 2 - 455090 * X ^ 3 - 1266360 * X ^ 4 + 17897076 * X ^ 5 - 75796192 * X ^ 6 + 203496960 * X ^ 7 - 362916736 * X ^ 8 + 404801856 * X ^ 9 - 241989120 * X ^ 10 : ℚ⟦X⟧) * G ^ 4 + (-7376 * X + 181260 * X ^ 2 - 1166608 * X ^ 3 + 670060 * X ^ 4 + 17952752 * X ^ 5 - 94995360 * X ^ 6 + 285194112 * X ^ 7 - 533645376 * X ^ 8 + 614947584 * X ^ 9 - 393062400 * X ^ 10 : ℚ⟦X⟧) * G ^ 5 + (-4596 * X + 211296 * X ^ 2 - 1727674 * X ^ 3 + 3471808 * X ^ 4 + 9503744 * X ^ 5 - 79874752 * X ^ 6 + 282781280 * X ^ 7 - 567189504 * X ^ 8 + 678037248 * X ^ 9 - 470062080 * X ^ 10 : ℚ⟦X⟧) * G ^ 6 + (-432 * X + 152128 * X ^ 2 - 1599904 * X ^ 3 + 4668720 * X ^ 4 - 51008 * X ^ 5 - 42785152 * X ^ 6 + 197330432 * X ^ 7 - 438094592 * X ^ 8 + 545074176 * X ^ 9 - 418406400 * X ^ 10 : ℚ⟦X⟧) * G ^ 7 + (918 * X + 63336 * X ^ 2 - 922762 * X ^ 3 + 3492264 * X ^ 4 - 3759756 * X ^ 5 - 12005792 * X ^ 6 + 93269632 * X ^ 7 - 242286976 * X ^ 8 + 313724736 * X ^ 9 - 275120640 * X ^ 10 : ℚ⟦X⟧) * G ^ 8 + (324 * X + 13140 * X ^ 2 - 308720 * X ^ 3 + 1562820 * X ^ 4 - 2560240 * X ^ 5 + 11424 * X ^ 6 + 27100800 * X ^ 7 - 92624576 * X ^ 8 + 123066624 * X ^ 9 - 129669120 * X ^ 10 : ℚ⟦X⟧) * G ^ 9 + (864 * X ^ 2 - 49074 * X ^ 3 + 396688 * X ^ 4 - 807600 * X ^ 5 + 921984 * X ^ 6 + 3618912 * X ^ 7 - 23242496 * X ^ 8 + 29902848 * X ^ 9 - 41103360 * X ^ 10 : ℚ⟦X⟧) * G ^ 10 + (-1728 * X ^ 3 + 46512 * X ^ 4 - 137280 * X ^ 5 + 147840 * X ^ 6 - 161280 * X ^ 7 - 3525888 * X ^ 8 + 3750912 * X ^ 9 - 7741440 * X ^ 10 : ℚ⟦X⟧) * G ^ 11 + (576 * X ^ 4 - 13200 * X ^ 5 - 7040 * X ^ 6 - 77440 * X ^ 7 - 256000 * X ^ 8 + 151296 * X ^ 9 - 645120 * X ^ 10 : ℚ⟦X⟧) * G ^ 12) * hP +
      ((4 * X - 42 * X ^ 2 - 20 * X ^ 3 + 1254 * X ^ 4 + 2056 * X ^ 5 - 57780 * X ^ 6 + 234464 * X ^ 7 - 502720 * X ^ 8 + 809600 * X ^ 9 - 760128 * X ^ 10 + 391680 * X ^ 11 : ℚ⟦X⟧) + (-56 * X ^ 2 + 1144 * X ^ 3 - 9302 * X ^ 4 + 42064 * X ^ 5 - 142228 * X ^ 6 + 442416 * X ^ 7 - 1106240 * X ^ 8 + 2027904 * X ^ 9 - 3121984 * X ^ 10 + 3432192 * X ^ 11 - 1566720 * X ^ 12 : ℚ⟦X⟧) * (derivative ℚ G) + (168 * X ^ 3 - 4086 * X ^ 4 + 40848 * X ^ 5 - 228228 * X ^ 6 + 842304 * X ^ 7 - 2347584 * X ^ 8 + 5212416 * X ^ 9 - 8871744 * X ^ 10 + 11510784 * X ^ 11 - 11486208 * X ^ 12 + 6266880 * X ^ 13 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (64 * X - 604 * X ^ 2 + 134 * X ^ 3 + 4728 * X ^ 4 + 113712 * X ^ 5 - 999984 * X ^ 6 + 3460064 * X ^ 7 - 7179008 * X ^ 8 + 10905088 * X ^ 9 - 10540800 * X ^ 10 + 5253120 * X ^ 11 : ℚ⟦X⟧) * G + (-756 * X ^ 2 + 15090 * X ^ 3 - 122784 * X ^ 4 + 577644 * X ^ 5 - 2038560 * X ^ 6 + 6220200 * X ^ 7 - 15083328 * X ^ 8 + 27318144 * X ^ 9 - 40046592 * X ^ 10 + 42855552 * X ^ 11 - 18662400 * X ^ 12 : ℚ⟦X⟧) * G * (derivative ℚ G) + (1824 * X ^ 3 - 43176 * X ^ 4 + 420996 * X ^ 5 - 2315568 * X ^ 6 + 8506224 * X ^ 7 - 23676864 * X ^ 8 + 52387008 * X ^ 9 - 89320704 * X ^ 10 + 116237568 * X ^ 11 - 115596288 * X ^ 12 + 65249280 * X ^ 13 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (432 * X - 3664 * X ^ 2 + 1864 * X ^ 3 - 18054 * X ^ 4 + 967160 * X ^ 5 - 6575568 * X ^ 6 + 21135744 * X ^ 7 - 43161952 * X ^ 8 + 63549824 * X ^ 9 - 61974528 * X ^ 10 + 30827520 * X ^ 11 : ℚ⟦X⟧) * G ^ 2 + (-4200 * X ^ 2 + 83184 * X ^ 3 - 680910 * X ^ 4 + 3262992 * X ^ 5 - 11626056 * X ^ 6 + 35032608 * X ^ 7 - 83733024 * X ^ 8 + 149961216 * X ^ 9 - 215932800 * X ^ 10 + 226859520 * X ^ 11 - 98058240 * X ^ 12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (7896 * X ^ 3 - 186858 * X ^ 4 + 1828272 * X ^ 5 - 10131312 * X ^ 6 + 37511232 * X ^ 7 - 104945520 * X ^ 8 + 233437056 * X ^ 9 - 401096832 * X ^ 10 + 524888064 * X ^ 11 - 525827328 * X ^ 12 + 305326080 * X ^ 13 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (1600 * X - 12148 * X ^ 2 + 1410 * X ^ 3 - 109016 * X ^ 4 + 3668504 * X ^ 5 - 23060832 * X ^ 6 + 72386144 * X ^ 7 - 147079296 * X ^ 8 + 213813376 * X ^ 9 - 209800704 * X ^ 10 + 105984000 * X ^ 11 : ℚ⟦X⟧) * G ^ 3 + (-12404 * X ^ 2 + 248914 * X ^ 3 - 2073272 * X ^ 4 + 10079344 * X ^ 5 - 36076048 * X ^ 6 + 108430056 * X ^ 7 - 258924224 * X ^ 8 + 462902976 * X ^ 9 - 664244992 * X ^ 10 + 698087040 * X ^ 11 - 305003520 * X ^ 12 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (17472 * X ^ 3 - 428496 * X ^ 4 + 4352136 * X ^ 5 - 24901152 * X ^ 6 + 94246848 * X ^ 7 - 267340800 * X ^ 8 + 603182208 * X ^ 9 - 1053166080 * X ^ 10 + 1393391616 * X ^ 11 - 1419190272 * X ^ 12 + 858193920 * X ^ 13 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) ^ 2 + (3544 * X - 23804 * X ^ 2 - 32512 * X ^ 3 - 94158 * X ^ 4 + 7675952 * X ^ 5 - 49443892 * X ^ 6 + 157327648 * X ^ 7 - 322123648 * X ^ 8 + 468815104 * X ^ 9 - 466226496 * X ^ 10 + 241989120 * X ^ 11 : ℚ⟦X⟧) * G ^ 4 + (-21000 * X ^ 2 + 439608 * X ^ 3 - 3802896 * X ^ 4 + 18924216 * X ^ 5 - 68297496 * X ^ 6 + 207132384 * X ^ 7 - 501566400 * X ^ 8 + 905296512 * X ^ 9 - 1309569408 * X ^ 10 + 1405678080 * X ^ 11 - 632217600 * X ^ 12 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (20952 * X ^ 3 - 558954 * X ^ 4 + 6149232 * X ^ 5 - 37471068 * X ^ 6 + 147689280 * X ^ 7 - 429178752 * X ^ 8 + 991938816 * X ^ 9 - 1777910976 * X ^ 10 + 2393809920 * X ^ 11 - 2499840000 * X ^ 12 + 1603584000 * X ^ 13 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) ^ 2 + (4800 * X - 27720 * X ^ 2 - 135084 * X ^ 3 + 404088 * X ^ 4 + 9290436 * X ^ 5 - 68809200 * X ^ 6 + 230116512 * X ^ 7 - 482681088 * X ^ 8 + 711673152 * X ^ 9 - 726322944 * X ^ 10 + 393062400 * X ^ 11 : ℚ⟦X⟧) * G ^ 5 + (-20412 * X ^ 2 + 465990 * X ^ 3 - 4322928 * X ^ 4 + 22450116 * X ^ 5 - 82402080 * X ^ 6 + 255216984 * X ^ 7 - 638622144 * X ^ 8 + 1178637696 * X ^ 9 - 1738116096 * X ^ 10 + 1948593024 * X ^ 11 - 922475520 * X ^ 12 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (12960 * X ^ 3 - 409608 * X ^ 4 + 5193972 * X ^ 5 - 35215056 * X ^ 6 + 148496256 * X ^ 7 - 447887232 * X ^ 8 + 1071508032 * X ^ 9 - 1997634816 * X ^ 10 + 2757312000 * X ^ 11 - 2973247488 * X ^ 12 + 2072494080 * X ^ 13 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) ^ 2 + (3888 * X - 17936 * X ^ 2 - 244960 * X ^ 3 + 1235618 * X ^ 4 + 5881336 * X ^ 5 - 62877120 * X ^ 6 + 231764992 * X ^ 7 - 508268128 * X ^ 8 + 768433536 * X ^ 9 - 816415488 * X ^ 10 + 470062080 * X ^ 11 : ℚ⟦X⟧) * G ^ 6 + (-10584 * X ^ 2 + 286320 * X ^ 3 - 3000282 * X ^ 4 + 16767408 * X ^ 5 - 63461412 * X ^ 6 + 203195376 * X ^ 7 - 538745856 * X ^ 8 + 1035107712 * X ^ 9 - 1571313216 * X ^ 10 + 1889121024 * X ^ 11 - 969615360 * X ^ 12 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (3240 * X ^ 3 - 152118 * X ^ 4 + 2492688 * X ^ 5 - 20178768 * X ^ 6 + 95017728 * X ^ 7 - 303065184 * X ^ 8 + 757812480 * X ^ 9 - 1494882816 * X ^ 10 + 2135629824 * X ^ 11 - 2382987264 * X ^ 12 + 1863843840 * X ^ 13 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) ^ 2 + (1728 * X - 4740 * X ^ 2 - 239350 * X ^ 3 + 1562032 * X ^ 4 + 588724 * X ^ 5 - 36326688 * X ^ 6 + 160043776 * X ^ 7 - 377230336 * X ^ 8 + 591873344 * X ^ 9 - 665273856 * X ^ 10 + 418406400 * X ^ 11 : ℚ⟦X⟧) * G ^ 7 + (-2268 * X ^ 2 + 91062 * X ^ 3 - 1191624 * X ^ 4 + 7543056 * X ^ 5 - 30051840 * X ^ 6 + 100771536 * X ^ 7 - 293104128 * X ^ 8 + 604131456 * X ^ 9 - 950830080 * X ^ 10 + 1263624960 * X ^ 11 - 734238720 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (-20736 * X ^ 4 + 593856 * X ^ 5 - 6566400 * X ^ 6 + 37180800 * X ^ 7 - 129378816 * X ^ 8 + 340273152 * X ^ 9 - 725151744 * X ^ 10 + 1089533952 * X ^ 11 - 1245487104 * X ^ 12 + 1141309440 * X ^ 13 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) ^ 2 + (324 * X + 774 * X ^ 2 - 127460 * X ^ 3 + 1057694 * X ^ 4 - 1828504 * X ^ 5 - 11643348 * X ^ 6 + 73164896 * X ^ 7 - 194050880 * X ^ 8 + 319038592 * X ^ 9 - 385701696 * X ^ 10 + 275120640 * X ^ 11 : ℚ⟦X⟧) * G ^ 8 + (10800 * X ^ 3 - 232098 * X ^ 4 + 1844088 * X ^ 5 - 7963200 * X ^ 6 + 28395264 * X ^ 7 - 95747616 * X ^ 8 + 223916928 * X ^ 9 - 368030976 * X ^ 10 + 556600320 * X ^ 11 - 390389760 * X ^ 12 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (50112 * X ^ 5 - 1045008 * X ^ 6 + 8204544 * X ^ 7 - 33091200 * X ^ 8 + 91431936 * X ^ 9 - 214569216 * X ^ 10 + 350466048 * X ^ 11 - 395698176 * X ^ 12 + 451215360 * X ^ 13 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) ^ 2 + (540 * X ^ 2 - 32838 * X ^ 3 + 378528 * X ^ 4 - 1273780 * X ^ 5 - 1110160 * X ^ 6 + 20407744 * X ^ 7 - 66614144 * X ^ 8 + 115630784 * X ^ 9 - 151267584 * X ^ 10 + 129669120 * X ^ 11 : ℚ⟦X⟧) * G ^ 9 + (-14976 * X ^ 4 + 195896 * X ^ 5 - 931072 * X ^ 6 + 3577568 * X ^ 7 - 16049408 * X ^ 8 + 47876736 * X ^ 9 - 84588544 * X ^ 10 + 146803200 * X ^ 11 - 137318400 * X ^ 12 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (-53760 * X ^ 6 + 846720 * X ^ 7 - 4569600 * X ^ 8 + 13224960 * X ^ 9 - 33976320 * X ^ 10 + 65157120 * X ^ 11 - 66232320 * X ^ 12 + 103219200 * X ^ 13 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) ^ 2 + (-2592 * X ^ 3 + 59874 * X ^ 4 - 346288 * X ^ 5 + 388400 * X ^ 6 + 2907520 * X ^ 7 - 14224736 * X ^ 8 + 26690816 * X ^ 9 - 36354048 * X ^ 10 + 41103360 * X ^ 11 : ℚ⟦X⟧) * G ^ 10 + (4416 * X ^ 5 - 6480 * X ^ 6 - 15936 * X ^ 7 - 862848 * X ^ 8 + 4594176 * X ^ 9 - 10444032 * X ^ 10 + 18914304 * X ^ 11 - 28385280 * X ^ 12 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (21504 * X ^ 7 - 252672 * X ^ 8 + 817152 * X ^ 9 - 2021376 * X ^ 10 + 5505024 * X ^ 11 - 4042752 * X ^ 12 + 10321920 * X ^ 13 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) ^ 2 + (2304 * X ^ 4 - 36672 * X ^ 5 + 104640 * X ^ 6 + 113664 * X ^ 7 - 1614336 * X ^ 8 + 3677184 * X ^ 9 - 4396032 * X ^ 10 + 7741440 * X ^ 11 : ℚ⟦X⟧) * G ^ 11 + (2304 * X ^ 6 - 34368 * X ^ 7 + 16896 * X ^ 8 + 13824 * X ^ 9 - 614400 * X ^ 10 + 605184 * X ^ 11 - 2580480 * X ^ 12 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (-576 * X ^ 5 + 7056 * X ^ 6 - 5248 * X ^ 7 - 57728 * X ^ 8 + 256000 * X ^ 9 - 151296 * X ^ 10 + 645120 * X ^ 11 : ℚ⟦X⟧) * G ^ 12) * hd1 +
      ((14 * X ^ 2 - 331 * X ^ 3 + 3308 * X ^ 4 - 19168 * X ^ 5 + 77632 * X ^ 6 - 250896 * X ^ 7 + 653504 * X ^ 8 - 1289472 * X ^ 9 + 1948672 * X ^ 10 - 2285568 * X ^ 11 + 1474560 * X ^ 12 : ℚ⟦X⟧) + (-48 * X ^ 3 + 1260 * X ^ 4 - 13746 * X ^ 5 + 83784 * X ^ 6 - 331440 * X ^ 7 + 964992 * X ^ 8 - 2234400 * X ^ 9 + 4020864 * X ^ 10 - 5423616 * X ^ 11 + 5683200 * X ^ 12 - 3686400 * X ^ 13 : ℚ⟦X⟧) * (derivative ℚ G) + (224 * X ^ 2 - 5032 * X ^ 3 + 47750 * X ^ 4 - 264352 * X ^ 5 + 1036240 * X ^ 6 - 3259776 * X ^ 7 + 8187488 * X ^ 8 - 15536640 * X ^ 9 + 22855168 * X ^ 10 - 25620480 * X ^ 11 + 14745600 * X ^ 12 : ℚ⟦X⟧) * G + (-648 * X ^ 3 + 16254 * X ^ 4 - 168912 * X ^ 5 + 985068 * X ^ 6 - 3775680 * X ^ 7 + 10793088 * X ^ 8 - 24544512 * X ^ 9 + 43222464 * X ^ 10 - 57535488 * X ^ 11 + 59083776 * X ^ 12 - 36495360 * X ^ 13 : ℚ⟦X⟧) * G * (derivative ℚ G) + (1512 * X ^ 2 - 32580 * X ^ 3 + 296856 * X ^ 4 - 1589004 * X ^ 5 + 6091344 * X ^ 6 - 18804960 * X ^ 7 + 46047744 * X ^ 8 - 85348800 * X ^ 9 + 123588864 * X ^ 10 - 133871616 * X ^ 11 + 72990720 * X ^ 12 : ℚ⟦X⟧) * G ^ 2 + (-3600 * X ^ 3 + 87732 * X ^ 4 - 885762 * X ^ 5 + 5046840 * X ^ 6 - 19064520 * X ^ 7 + 54025632 * X ^ 8 - 121738464 * X ^ 9 + 212416128 * X ^ 10 - 280957824 * X ^ 11 + 285792768 * X ^ 12 - 173076480 * X ^ 13 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (5600 * X ^ 2 - 117528 * X ^ 3 + 1045330 * X ^ 4 - 5493088 * X ^ 5 + 20826296 * X ^ 6 - 63662784 * X ^ 7 + 153897056 * X ^ 8 - 282426368 * X ^ 9 + 405527168 * X ^ 10 - 432571392 * X ^ 11 + 230768640 * X ^ 12 : ℚ⟦X⟧) * G ^ 3 + (-10632 * X ^ 3 + 258174 * X ^ 4 - 2601552 * X ^ 5 + 14826720 * X ^ 6 - 56065344 * X ^ 7 + 158966832 * X ^ 8 - 358447488 * X ^ 9 + 626144640 * X ^ 10 - 828831744 * X ^ 11 + 843926784 * X ^ 12 - 513239040 * X ^ 13 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (12404 * X ^ 2 - 259474 * X ^ 3 + 2303816 * X ^ 4 - 12102328 * X ^ 5 + 45904480 * X ^ 6 - 140327040 * X ^ 7 + 339500288 * X ^ 8 - 623678976 * X ^ 9 + 896108032 * X ^ 10 - 957606912 * X ^ 11 + 513239040 * X ^ 12 : ℚ⟦X⟧) * G ^ 4 + (-18000 * X ^ 3 + 451620 * X ^ 4 - 4702050 * X ^ 5 + 27519480 * X ^ 6 - 105882840 * X ^ 7 + 303400800 * X ^ 8 - 691463520 * X ^ 9 + 1221886080 * X ^ 10 - 1630016640 * X ^ 11 + 1678763520 * X ^ 12 - 1047859200 * X ^ 13 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (16800 * X ^ 2 - 362088 * X ^ 3 + 3303966 * X ^ 4 - 17725152 * X ^ 5 + 68095320 * X ^ 6 - 210598848 * X ^ 7 + 517134624 * X ^ 8 - 961926144 * X ^ 9 + 1395738240 * X ^ 10 - 1519838208 * X ^ 11 + 838287360 * X ^ 12 : ℚ⟦X⟧) * G ^ 5 + (-17496 * X ^ 3 + 478026 * X ^ 4 - 5378544 * X ^ 5 + 33394068 * X ^ 6 - 133357248 * X ^ 7 + 390543552 * X ^ 8 - 909105408 * X ^ 9 + 1643807808 * X ^ 10 - 2226207744 * X ^ 11 + 2341380096 * X ^ 12 - 1535016960 * X ^ 13 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (13608 * X ^ 2 - 317156 * X ^ 3 + 3091256 * X ^ 4 - 17397180 * X ^ 5 + 68747344 * X ^ 6 - 217906272 * X ^ 7 + 551725056 * X ^ 8 - 1052853440 * X ^ 9 + 1557135616 * X ^ 10 - 1757140992 * X ^ 11 + 1023344640 * X ^ 12 : ℚ⟦X⟧) * G ^ 6 + (-9072 * X ^ 3 + 295596 * X ^ 4 - 3833550 * X ^ 5 + 26414136 * X ^ 6 - 112563360 * X ^ 7 + 341498304 * X ^ 8 - 820909152 * X ^ 9 + 1539780480 * X ^ 10 - 2134008576 * X ^ 11 + 2309981184 * X ^ 12 - 1633443840 * X ^ 13 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (6048 * X ^ 2 - 165960 * X ^ 3 + 1830390 * X ^ 4 - 11219040 * X ^ 5 + 46628352 * X ^ 6 - 153696000 * X ^ 7 + 408915168 * X ^ 8 - 814158336 * X ^ 9 + 1238552832 * X ^ 10 - 1473030144 * X ^ 11 + 933396480 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 + (-1944 * X ^ 3 + 95418 * X ^ 4 - 1599408 * X ^ 5 + 13131216 * X ^ 6 - 62348544 * X ^ 7 + 199682208 * X ^ 8 - 500758272 * X ^ 9 + 991586304 * X ^ 10 - 1420296192 * X ^ 11 + 1587400704 * X ^ 12 - 1251901440 * X ^ 13 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (1134 * X ^ 2 - 45819 * X ^ 3 + 636924 * X ^ 4 - 4518000 * X ^ 5 + 20459520 * X ^ 6 - 71446416 * X ^ 7 + 204224448 * X ^ 8 - 434793984 * X ^ 9 + 686505984 * X ^ 10 - 873455616 * X ^ 11 + 625950720 * X ^ 12 : ℚ⟦X⟧) * G ^ 8 + (11664 * X ^ 4 - 339228 * X ^ 5 + 3789936 * X ^ 6 - 21586176 * X ^ 7 + 75299328 * X ^ 8 - 198293184 * X ^ 9 + 423463680 * X ^ 10 - 637051392 * X ^ 11 + 728635392 * X ^ 12 - 670187520 * X ^ 13 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (-4752 * X ^ 3 + 111636 * X ^ 4 - 1032896 * X ^ 5 + 5416384 * X ^ 6 - 20638208 * X ^ 7 + 64937024 * X ^ 8 - 153412608 * X ^ 9 + 254695936 * X ^ 10 - 348327936 * X ^ 11 + 297861120 * X ^ 12 : ℚ⟦X⟧) * G ^ 9 + (-25920 * X ^ 5 + 542640 * X ^ 6 - 4273920 * X ^ 7 + 17258880 * X ^ 8 - 47692800 * X ^ 9 + 112024320 * X ^ 10 - 183029760 * X ^ 11 + 206684160 * X ^ 12 - 235929600 * X ^ 13 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (6912 * X ^ 4 - 112688 * X ^ 5 + 765760 * X ^ 6 - 3376256 * X ^ 7 + 11987456 * X ^ 8 - 33064704 * X ^ 9 + 59732992 * X ^ 10 - 85450752 * X ^ 11 + 94371840 * X ^ 12 : ℚ⟦X⟧) * G ^ 10 + (25344 * X ^ 6 - 399168 * X ^ 7 + 2154240 * X ^ 8 - 6234624 * X ^ 9 + 16017408 * X ^ 10 - 30716928 * X ^ 11 + 31223808 * X ^ 12 - 48660480 * X ^ 13 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (-3840 * X ^ 5 + 43968 * X ^ 6 - 259584 * X ^ 7 + 1107456 * X ^ 8 - 3686400 * X ^ 9 + 8150016 * X ^ 10 - 10838016 * X ^ 11 + 17694720 * X ^ 12 : ℚ⟦X⟧) * G ^ 11 + (-9216 * X ^ 7 + 108288 * X ^ 8 - 350208 * X ^ 9 + 866304 * X ^ 10 - 2359296 * X ^ 11 + 1732608 * X ^ 12 - 4423680 * X ^ 13 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (512 * X ^ 6 - 3584 * X ^ 7 + 43008 * X ^ 8 - 124928 * X ^ 9 + 532480 * X ^ 10 - 442368 * X ^ 11 + 1474560 * X ^ 12 : ℚ⟦X⟧) * G ^ 12) * hd2 +
      ((4 * X ^ 3 - 111 * X ^ 4 + 1288 * X ^ 5 - 8344 * X ^ 6 + 34688 * X ^ 7 - 104176 * X ^ 8 + 247424 * X ^ 9 - 461312 * X ^ 10 + 638976 * X ^ 11 - 684032 * X ^ 12 + 491520 * X ^ 13 : ℚ⟦X⟧) + (64 * X ^ 3 - 1680 * X ^ 4 + 18328 * X ^ 5 - 111712 * X ^ 6 + 441920 * X ^ 7 - 1286656 * X ^ 8 + 2979200 * X ^ 9 - 5361152 * X ^ 10 + 7231488 * X ^ 11 - 7577600 * X ^ 12 + 4915200 * X ^ 13 : ℚ⟦X⟧) * G + (432 * X ^ 3 - 10836 * X ^ 4 + 112608 * X ^ 5 - 656712 * X ^ 6 + 2517120 * X ^ 7 - 7195392 * X ^ 8 + 16363008 * X ^ 9 - 28814976 * X ^ 10 + 38356992 * X ^ 11 - 39389184 * X ^ 12 + 24330240 * X ^ 13 : ℚ⟦X⟧) * G ^ 2 + (1600 * X ^ 3 - 38992 * X ^ 4 + 393672 * X ^ 5 - 2243040 * X ^ 6 + 8473120 * X ^ 7 - 24011392 * X ^ 8 + 54105984 * X ^ 9 - 94407168 * X ^ 10 + 124870144 * X ^ 11 - 127019008 * X ^ 12 + 76922880 * X ^ 13 : ℚ⟦X⟧) * G ^ 3 + (3544 * X ^ 3 - 86058 * X ^ 4 + 867184 * X ^ 5 - 4942240 * X ^ 6 + 18688448 * X ^ 7 - 52988944 * X ^ 8 + 119482496 * X ^ 9 - 208714880 * X ^ 10 + 276277248 * X ^ 11 - 281308928 * X ^ 12 + 171079680 * X ^ 13 : ℚ⟦X⟧) * G ^ 4 + (4800 * X ^ 3 - 120432 * X ^ 4 + 1253880 * X ^ 5 - 7338528 * X ^ 6 + 28235424 * X ^ 7 - 80906880 * X ^ 8 + 184390272 * X ^ 9 - 325836288 * X ^ 10 + 434671104 * X ^ 11 - 447670272 * X ^ 12 + 279429120 * X ^ 13 : ℚ⟦X⟧) * G ^ 5 + (3888 * X ^ 3 - 106228 * X ^ 4 + 1195232 * X ^ 5 - 7420904 * X ^ 6 + 29634944 * X ^ 7 - 86787456 * X ^ 8 + 202023424 * X ^ 9 - 365290624 * X ^ 10 + 494712832 * X ^ 11 - 520306688 * X ^ 12 + 341114880 * X ^ 13 : ℚ⟦X⟧) * G ^ 6 + (1728 * X ^ 3 - 56304 * X ^ 4 + 730200 * X ^ 5 - 5031264 * X ^ 6 + 21440640 * X ^ 7 - 65047296 * X ^ 8 + 156363648 * X ^ 9 - 293291520 * X ^ 10 + 406477824 * X ^ 11 - 439996416 * X ^ 12 + 311132160 * X ^ 13 : ℚ⟦X⟧) * G ^ 7 + (324 * X ^ 3 - 15903 * X ^ 4 + 266568 * X ^ 5 - 2188536 * X ^ 6 + 10391424 * X ^ 7 - 33280368 * X ^ 8 + 83459712 * X ^ 9 - 165264384 * X ^ 10 + 236716032 * X ^ 11 - 264566784 * X ^ 12 + 208650240 * X ^ 13 : ℚ⟦X⟧) * G ^ 8 + (-1728 * X ^ 4 + 50256 * X ^ 5 - 561472 * X ^ 6 + 3197952 * X ^ 7 - 11155456 * X ^ 8 + 29376768 * X ^ 9 - 62735360 * X ^ 10 + 94377984 * X ^ 11 - 107945984 * X ^ 12 + 99287040 * X ^ 13 : ℚ⟦X⟧) * G ^ 9 + (3456 * X ^ 5 - 72352 * X ^ 6 + 569856 * X ^ 7 - 2301184 * X ^ 8 + 6359040 * X ^ 9 - 14936576 * X ^ 10 + 24403968 * X ^ 11 - 27557888 * X ^ 12 + 31457280 * X ^ 13 : ℚ⟦X⟧) * G ^ 10 + (-3072 * X ^ 6 + 48384 * X ^ 7 - 261120 * X ^ 8 + 755712 * X ^ 9 - 1941504 * X ^ 10 + 3723264 * X ^ 11 - 3784704 * X ^ 12 + 5898240 * X ^ 13 : ℚ⟦X⟧) * G ^ 11 + (1024 * X ^ 7 - 12032 * X ^ 8 + 38912 * X ^ 9 - 96256 * X ^ 10 + 262144 * X ^ 11 - 192512 * X ^ 12 + 491520 * X ^ 13 : ℚ⟦X⟧) * G ^ 12) * hd3
  have k3 : constantCoeff (3 : ℚ⟦X⟧) = 3 := cnum 3
  have k4 : constantCoeff (4 : ℚ⟦X⟧) = 4 := cnum 4
  have hPG : (-1 + 4 * X : ℚ⟦X⟧) + (-4 + 10 * X : ℚ⟦X⟧) * G + (-3 + 12 * X : ℚ⟦X⟧) * G ^ 2 + (4 * X : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k3, k4] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 5 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-2 + 5 * X : ℚ⟦X⟧) * G ^ 2 + (-1 + 4 * X : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 4 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-47) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C 152 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C (-376) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * C 1024 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * X * C (-752) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * X * X * C 1920 + derivative ℚ (derivative ℚ G) * X * X * C 14 +
      derivative ℚ (derivative ℚ G) * X * X * X * C (-155) + derivative ℚ (derivative ℚ G) * X * X * X * X * C 624 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-1616) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 5152 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C (-3984) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * C 11520 +
      derivative ℚ G * X * C 4 + derivative ℚ G * X * X * C (-34) +
      derivative ℚ G * X * X * X * C 332 + derivative ℚ G * X * X * X * X * C (-1188) +
      derivative ℚ G * X * X * X * X * X * C 4560 + derivative ℚ G * X * X * X * X * X * X * C (-3456) +
      derivative ℚ G * X * X * X * X * X * X * X * C 11520 + G * X * C (-6) +
      G * X * X * C (-12) + G * X * X * X * C (-132) =
      C 4 * X + C 32 * X * X +
      C 32 * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-2 + 5 * X : ℚ⟦X⟧) * G ^ 2 + (-1 + 4 * X : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    4 * ((m : ℚ) + 9) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-47) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      152 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-376) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      1024 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-752) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      1920 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + 14 * ((m : ℚ) + 9) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-155) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 624 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-1616) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 5152 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-3984) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + 11520 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      4 * ((m : ℚ) + 9) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-34) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      332 * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-1188) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      4560 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-3456) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      11520 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-12) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-132) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-2 + 5 * X : ℚ⟦X⟧) * G ^ 2 + (-1 + 4 * X : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    480 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-2820) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      3648 * coeff (0 + 1 + 1 + 1 + 1) G + (-2256) * coeff (0 + 1 + 1 + 1) G +
      420 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-3100) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      7488 * coeff (0 + 1 + 1 + 1 + 1) G + (-9696) * coeff (0 + 1 + 1 + 1) G +
      10304 * coeff (0 + 1 + 1) G + 24 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-170) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 1328 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-3564) * coeff (0 + 1 + 1 + 1) G + 9120 * coeff (0 + 1 + 1) G +
      (-3456) * coeff (0 + 1) G + (-6) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-12) * coeff (0 + 1 + 1 + 1 + 1) G + (-132) * coeff (0 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-2 + 5 * X : ℚ⟦X⟧) * G ^ 2 + (-1 + 4 * X : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    840 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-5640) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      9120 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-9024) * coeff (0 + 1 + 1 + 1 + 1) G +
      6144 * coeff (0 + 1 + 1 + 1) G + 588 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-4650) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 12480 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-19392) * coeff (0 + 1 + 1 + 1 + 1) G + 30912 * coeff (0 + 1 + 1 + 1) G +
      (-7968) * coeff (0 + 1 + 1) G + 28 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-204) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 1660 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-4752) * coeff (0 + 1 + 1 + 1 + 1) G + 13680 * coeff (0 + 1 + 1 + 1) G +
      (-6912) * coeff (0 + 1 + 1) G + 11520 * coeff (0 + 1) G +
      (-6) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-12) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-132) * coeff (0 + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE2 (G : ℚ⟦X⟧)
    (hP : (X : ℚ⟦X⟧) + (-1 + 4 * X : ℚ⟦X⟧) * G + (-2 + 5 * X : ℚ⟦X⟧) * G ^ 2 + (-1 + 4 * X : ℚ⟦X⟧) * G ^ 3 + (X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    1344 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-9870) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      18240 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-22560) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      24576 * coeff (0 + 1 + 1 + 1 + 1) G + (-4512) * coeff (0 + 1 + 1 + 1) G +
      784 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-6510) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      18720 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-32320) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      61824 * coeff (0 + 1 + 1 + 1 + 1) G + (-23904) * coeff (0 + 1 + 1 + 1) G +
      23040 * coeff (0 + 1 + 1) G + 32 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-238) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 1992 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-5940) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 18240 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-10368) * coeff (0 + 1 + 1 + 1) G + 23040 * coeff (0 + 1 + 1) G +
      (-6) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-12) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-132) * coeff (0 + 1 + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A243814Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a243814.main := by
  intro T U G hT _ hU _ hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 6, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m := rfl
  rw [e1, e2, e3, e4, e5, e6]
  have hn : ((1) + (-1) * T) * ((1) + (1) * T + (-1) * T ^ 2 + (-1) * T ^ 3) = (16 * PowerSeries.X ^ 4 : PowerSeries ℚ) := by
    linear_combination ((-1) + (1) * T ^ 2 + (4) * PowerSeries.X ^ 2) * hT
  have hnu0 : (16 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    have kc : PowerSeries.constantCoeff (16 : PowerSeries ℚ) = 16 := A243814Aux.cnum 16
    simp [kc] at h'
  have hnu : (16 * PowerSeries.X ^ 4 : PowerSeries ℚ) ≠ 0 := by
    have e : (16 * PowerSeries.X ^ 4 : PowerSeries ℚ) = PowerSeries.X ^ 4 * (16 : PowerSeries ℚ) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 4 PowerSeries.X_ne_zero) hnu0
  have hN1 : ((1) + (-1) * T) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hn
    exact hnu hn.symm
  have hM : ((1 : PowerSeries ℚ) * PowerSeries.X ^ 3) * (((1) + (-1) * T) ^ 4 * ((PowerSeries.X : PowerSeries ℚ) + (-1 + 4 * PowerSeries.X : PowerSeries ℚ) * G + (-2 + 5 * PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (-1 + 4 * PowerSeries.X : PowerSeries ℚ) * G ^ 3 + (PowerSeries.X : PowerSeries ℚ) * G ^ 4)) = 0 := by
    linear_combination ((-1) * PowerSeries.X ^ 4 + (2) * PowerSeries.X ^ 4 * T + (-1) * PowerSeries.X ^ 4 * T ^ 2 + (-4) * PowerSeries.X ^ 5 + (2) * PowerSeries.X ^ 5 * U + (4) * PowerSeries.X ^ 5 * T + (-2) * PowerSeries.X ^ 5 * T * U + (-2) * PowerSeries.X ^ 6 + (2) * PowerSeries.X ^ 6 * U) * hT +
      ((1) * PowerSeries.X ^ 4 + (-2) * PowerSeries.X ^ 4 * T + (1) * PowerSeries.X ^ 4 * T ^ 2 + (2) * PowerSeries.X ^ 5 + (-1) * PowerSeries.X ^ 5 * U + (-1) * PowerSeries.X ^ 5 * T + (1) * PowerSeries.X ^ 5 * T * U + (-1) * PowerSeries.X ^ 5 * T ^ 2 + (2) * PowerSeries.X ^ 6 + (-2) * PowerSeries.X ^ 6 * T + (7) * PowerSeries.X ^ 7 + (-4) * PowerSeries.X ^ 7 * U + (1) * PowerSeries.X ^ 7 * U ^ 2) * hU +
      ((-1) * PowerSeries.X ^ 3 * G + (3) * PowerSeries.X ^ 3 * G * T + (-3) * PowerSeries.X ^ 3 * G * T ^ 2 + (1) * PowerSeries.X ^ 3 * G * T ^ 3 + (-1) * PowerSeries.X ^ 3 * G ^ 2 + (3) * PowerSeries.X ^ 3 * G ^ 2 * T + (-3) * PowerSeries.X ^ 3 * G ^ 2 * T ^ 2 + (1) * PowerSeries.X ^ 3 * G ^ 2 * T ^ 3 + (2) * PowerSeries.X ^ 4 + (-6) * PowerSeries.X ^ 4 * T + (6) * PowerSeries.X ^ 4 * T ^ 2 + (-2) * PowerSeries.X ^ 4 * T ^ 3 + (3) * PowerSeries.X ^ 4 * G + (-1) * PowerSeries.X ^ 4 * G * U + (-8) * PowerSeries.X ^ 4 * G * T + (2) * PowerSeries.X ^ 4 * G * T * U + (7) * PowerSeries.X ^ 4 * G * T ^ 2 + (-1) * PowerSeries.X ^ 4 * G * T ^ 2 * U + (-2) * PowerSeries.X ^ 4 * G * T ^ 3 + (3) * PowerSeries.X ^ 4 * G ^ 2 + (-9) * PowerSeries.X ^ 4 * G ^ 2 * T + (9) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 2 + (-3) * PowerSeries.X ^ 4 * G ^ 2 * T ^ 3 + (1) * PowerSeries.X ^ 4 * G ^ 3 + (-3) * PowerSeries.X ^ 4 * G ^ 3 * T + (3) * PowerSeries.X ^ 4 * G ^ 3 * T ^ 2 + (-1) * PowerSeries.X ^ 4 * G ^ 3 * T ^ 3 + (-1) * PowerSeries.X ^ 5 + (2) * PowerSeries.X ^ 5 * U + (-1) * PowerSeries.X ^ 5 * U ^ 2 + (1) * PowerSeries.X ^ 5 * T + (-2) * PowerSeries.X ^ 5 * T * U + (1) * PowerSeries.X ^ 5 * T * U ^ 2 + (-2) * PowerSeries.X ^ 5 * G + (2) * PowerSeries.X ^ 5 * G * U + (4) * PowerSeries.X ^ 5 * G * T + (-4) * PowerSeries.X ^ 5 * G * T * U + (-2) * PowerSeries.X ^ 5 * G * T ^ 2 + (2) * PowerSeries.X ^ 5 * G * T ^ 2 * U + (-1) * PowerSeries.X ^ 5 * G ^ 2 + (1) * PowerSeries.X ^ 5 * G ^ 2 * U + (2) * PowerSeries.X ^ 5 * G ^ 2 * T + (-2) * PowerSeries.X ^ 5 * G ^ 2 * T * U + (-1) * PowerSeries.X ^ 5 * G ^ 2 * T ^ 2 + (1) * PowerSeries.X ^ 5 * G ^ 2 * T ^ 2 * U + (1) * PowerSeries.X ^ 6 + (-2) * PowerSeries.X ^ 6 * U + (1) * PowerSeries.X ^ 6 * U ^ 2 + (-1) * PowerSeries.X ^ 6 * T + (2) * PowerSeries.X ^ 6 * T * U + (-1) * PowerSeries.X ^ 6 * T * U ^ 2 + (1) * PowerSeries.X ^ 6 * G + (-2) * PowerSeries.X ^ 6 * G * U + (1) * PowerSeries.X ^ 6 * G * U ^ 2 + (-1) * PowerSeries.X ^ 6 * G * T + (2) * PowerSeries.X ^ 6 * G * T * U + (-1) * PowerSeries.X ^ 6 * G * T * U ^ 2 + (-1) * PowerSeries.X ^ 7 + (3) * PowerSeries.X ^ 7 * U + (-3) * PowerSeries.X ^ 7 * U ^ 2 + (1) * PowerSeries.X ^ 7 * U ^ 3) * hG
  have hLne : ((1 : PowerSeries ℚ) * PowerSeries.X ^ 3) ≠ 0 := mul_ne_zero one_ne_zero (pow_ne_zero 3 PowerSeries.X_ne_zero)
  have hP : (PowerSeries.X : PowerSeries ℚ) + (-1 + 4 * PowerSeries.X : PowerSeries ℚ) * G + (-2 + 5 * PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (-1 + 4 * PowerSeries.X : PowerSeries ℚ) * G ^ 3 + (PowerSeries.X : PowerSeries ℚ) * G ^ 4 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hM).resolve_left hLne)).resolve_left (pow_ne_zero 4 hN1)
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A243814Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A243814Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A243814Aux.relE2 G hP h0c
        push_cast
        linear_combination r
      | succ m =>
        have r := A243814Aux.rel G hP h0c m
        push_cast
        linear_combination r
