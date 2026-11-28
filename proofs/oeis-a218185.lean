import OMAStatements.S_oeis_a218185

-- Problem: A218185: Number of rows with the value true in the truth tables of all bracketed formulas with n distinct propositions p_1, ..., p_n connected by the binary connective of m-implication (case 3).
-- Upstream: formal-conjectures statements/oeis-a218185.lean:0 (declaration OMA.S_oeis_a218185.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A218185Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (X ^ 4 : ℚ⟦X⟧) + (-X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) * G + (2 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 - 4 * X : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0) :
    (X ^ 3 - 24 * X ^ 4 + 208 * X ^ 5 - 768 * X ^ 6 + 1024 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-12 * X ^ 3 + 208 * X ^ 4 - 1152 * X ^ 5 + 2048 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-12 * X ^ 3 + 96 * X ^ 4 - 256 * X ^ 5) * derivative ℚ G + (-48 * X ^ 3 + 256 * X ^ 4) * G =
      -16 * X ^ 4 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have hp0 : (1 * (X * X * X * X) : ℚ⟦X⟧) + (-1 * (X * X) + 4 * (X * X * X) : ℚ⟦X⟧) * G + (2 * (X * X) : ℚ⟦X⟧) * G * G + (1 - 4 * X : ℚ⟦X⟧) * G * G * G + (1 : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((1 * (X * X * X * X) : ℚ⟦X⟧) + (-1 * (X * X) + 4 * (X * X * X) : ℚ⟦X⟧) * G + (2 * (X * X) : ℚ⟦X⟧) * G * G + (1 - 4 * X : ℚ⟦X⟧) * G * G * G + (1 : ℚ⟦X⟧) * G * G * G * G) =
      (4 * X ^ 3 : ℚ⟦X⟧) + (-X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 * X + 12 * X ^ 2 : ℚ⟦X⟧) * G + (4 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (4 * X : ℚ⟦X⟧) * G ^ 2 + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G ^ 3 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hd1 : (4 * X ^ 3 : ℚ⟦X⟧) + (-X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) * (derivative ℚ G) + (-2 * X + 12 * X ^ 2 : ℚ⟦X⟧) * G + (4 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (4 * X : ℚ⟦X⟧) * G ^ 2 + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G ^ 3 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (4 * (X * X * X) : ℚ⟦X⟧) + (-1 * (X * X) + 4 * (X * X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (-2 * X + 12 * (X * X) : ℚ⟦X⟧) * G + (4 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (4 * X : ℚ⟦X⟧) * G * G + (3 - 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G * G * G + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((4 * (X * X * X) : ℚ⟦X⟧) + (-1 * (X * X) + 4 * (X * X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (-2 * X + 12 * (X * X) : ℚ⟦X⟧) * G + (4 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (4 * X : ℚ⟦X⟧) * G * G + (3 - 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G * G * G + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G)) =
      (12 * X ^ 2 : ℚ⟦X⟧) + (-X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-4 * X + 24 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) + (4 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 + 24 * X : ℚ⟦X⟧) * G + (4 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (16 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 2 + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d2, d3, d4, d12]
    ring
  have hd2 : (12 * X ^ 2 : ℚ⟦X⟧) + (-X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-4 * X + 24 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) + (4 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-2 + 24 * X : ℚ⟦X⟧) * G + (4 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (16 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 2 + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) = 0 := by rw [← hL2, hp1, map_zero]
  have hp2 : (12 * (X * X) : ℚ⟦X⟧) + (-1 * (X * X) + 4 * (X * X * X) : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-4 * X + 24 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (4 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (-2 + 24 * X : ℚ⟦X⟧) * G + (4 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (16 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G + (3 - 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (12 : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) = 0 := by linear_combination hd2
  have hL3 : derivative ℚ ((12 * (X * X) : ℚ⟦X⟧) + (-1 * (X * X) + 4 * (X * X * X) : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-4 * X + 24 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (4 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (-2 + 24 * X : ℚ⟦X⟧) * G + (4 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (16 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G + (3 - 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (12 : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G))) =
      (24 * X : ℚ⟦X⟧) + (-X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-6 * X + 36 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-6 + 72 * X : ℚ⟦X⟧) * (derivative ℚ G) + (12 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (24 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (6 - 24 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (24 : ℚ⟦X⟧) * G + (4 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (24 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G * (derivative ℚ G) + (18 - 72 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-72 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (24 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) := by
    simp [Derivation.leibniz, d2, d3, d4, d6, d12, d16, d24]
    ring
  have hd3 : (24 * X : ℚ⟦X⟧) + (-X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-6 * X + 36 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-6 + 72 * X : ℚ⟦X⟧) * (derivative ℚ G) + (12 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (24 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (6 - 24 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (24 : ℚ⟦X⟧) * G + (4 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (24 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (24 : ℚ⟦X⟧) * G * (derivative ℚ G) + (18 - 72 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-72 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (24 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) = 0 := by rw [← hL3, hp2, map_zero]
  have hfull : ((-X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) + (4 * X ^ 2 : ℚ⟦X⟧) * G + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3) ^ 5 * ((X ^ 3 - 24 * X ^ 4 + 208 * X ^ 5 - 768 * X ^ 6 + 1024 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-12 * X ^ 3 + 208 * X ^ 4 - 1152 * X ^ 5 + 2048 * X ^ 6) * derivative ℚ (derivative ℚ G) + (-12 * X ^ 3 + 96 * X ^ 4 - 256 * X ^ 5) * derivative ℚ G + (-48 * X ^ 3 + 256 * X ^ 4) * G - (-16 * X ^ 4)) = 0 := by
    linear_combination ((-24 * X ^ 8 + 960 * X ^ 9 - 16800 * X ^ 10 + 168128 * X ^ 11 - 1046528 * X ^ 12 + 4114432 * X ^ 13 - 9936896 * X ^ 14 + 13549568 * X ^ 15 - 8126464 * X ^ 16 : ℚ⟦X⟧) + (1320 * X ^ 8 - 48576 * X ^ 9 + 747520 * X ^ 10 - 6206464 * X ^ 11 + 29890560 * X ^ 12 - 83165184 * X ^ 13 + 123207680 * X ^ 14 - 74448896 * X ^ 15 : ℚ⟦X⟧) * G + (-360 * X ^ 6 + 16128 * X ^ 7 - 317472 * X ^ 8 + 3548544 * X ^ 9 - 24371200 * X ^ 10 + 104372224 * X ^ 11 - 270491648 * X ^ 12 + 386334720 * X ^ 13 - 232259584 * X ^ 14 : ℚ⟦X⟧) * G ^ 2 + (4560 * X ^ 6 - 172416 * X ^ 7 + 2684160 * X ^ 8 - 22228992 * X ^ 9 + 105234432 * X ^ 10 - 282411008 * X ^ 11 + 391446528 * X ^ 12 - 208666624 * X ^ 13 : ℚ⟦X⟧) * G ^ 3 + (864 * X ^ 5 - 23136 * X ^ 6 + 178944 * X ^ 7 + 503808 * X ^ 8 - 15585280 * X ^ 9 + 94191616 * X ^ 10 - 246038528 * X ^ 11 + 243007488 * X ^ 12 : ℚ⟦X⟧) * G ^ 4 + (-3672 * X ^ 4 + 138816 * X ^ 5 - 2188800 * X ^ 6 + 18819072 * X ^ 7 - 95924224 * X ^ 8 + 290521088 * X ^ 9 - 482869248 * X ^ 10 + 337641472 * X ^ 11 : ℚ⟦X⟧) * G ^ 5 + (-2592 * X ^ 3 + 80928 * X ^ 4 - 954240 * X ^ 5 + 5013504 * X ^ 6 - 7188480 * X ^ 7 - 41238528 * X ^ 8 + 191234048 * X ^ 9 - 240123904 * X ^ 10 : ℚ⟦X⟧) * G ^ 6 + (-13824 * X ^ 3 + 441600 * X ^ 4 - 5517312 * X ^ 5 + 34652160 * X ^ 6 - 116162560 * X ^ 7 + 199622656 * X ^ 8 - 140509184 * X ^ 9 : ℚ⟦X⟧) * G ^ 7 + (-36288 * X ^ 3 + 1026048 * X ^ 4 - 11532288 * X ^ 5 + 63856640 * X ^ 6 - 173260800 * X ^ 7 + 184287232 * X ^ 8 : ℚ⟦X⟧) * G ^ 8 + (-119808 * X ^ 3 + 2365440 * X ^ 4 - 17825792 * X ^ 5 + 60817408 * X ^ 6 - 78643200 * X ^ 7 : ℚ⟦X⟧) * G ^ 9 + (-190464 * X ^ 3 + 2662400 * X ^ 4 - 12386304 * X ^ 5 + 19398656 * X ^ 6 : ℚ⟦X⟧) * G ^ 10 + (-147456 * X ^ 3 + 1376256 * X ^ 4 - 3145728 * X ^ 5 : ℚ⟦X⟧) * G ^ 11 + (-49152 * X ^ 3 + 262144 * X ^ 4 : ℚ⟦X⟧) * G ^ 12) * hP +
      ((18 * X ^ 9 - 720 * X ^ 10 + 12548 * X ^ 11 - 124512 * X ^ 12 + 767872 * X ^ 13 - 3004416 * X ^ 14 + 7271424 * X ^ 15 - 9969664 * X ^ 16 + 5963776 * X ^ 17 : ℚ⟦X⟧) + (-24 * X ^ 10 + 960 * X ^ 11 - 16064 * X ^ 12 + 145152 * X ^ 13 - 762880 * X ^ 14 + 2330624 * X ^ 15 - 3833856 * X ^ 16 + 2621440 * X ^ 17 : ℚ⟦X⟧) * (derivative ℚ G) + (6 * X ^ 9 - 240 * X ^ 10 + 4176 * X ^ 11 - 41472 * X ^ 12 + 258048 * X ^ 13 - 1032192 * X ^ 14 + 2592768 * X ^ 15 - 3735552 * X ^ 16 + 2359296 * X ^ 17 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-528 * X ^ 9 + 19104 * X ^ 10 - 289984 * X ^ 11 + 2391040 * X ^ 12 - 11549696 * X ^ 13 + 32636928 * X ^ 14 - 49872896 * X ^ 15 + 31719424 * X ^ 16 : ℚ⟦X⟧) * G + (-120 * X ^ 8 + 4896 * X ^ 9 - 85248 * X ^ 10 + 825216 * X ^ 11 - 4842240 * X ^ 12 + 17565696 * X ^ 13 - 38252544 * X ^ 14 + 45318144 * X ^ 15 - 22020096 * X ^ 16 : ℚ⟦X⟧) * G * (derivative ℚ G) + (96 * X ^ 9 - 3456 * X ^ 10 + 51840 * X ^ 11 - 419328 * X ^ 12 + 1972224 * X ^ 13 - 5382144 * X ^ 14 + 7864320 * X ^ 15 - 4718592 * X ^ 16 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (114 * X ^ 7 - 4944 * X ^ 8 + 93264 * X ^ 9 - 992640 * X ^ 10 + 6480512 * X ^ 11 - 26459136 * X ^ 12 + 65832960 * X ^ 13 - 91275264 * X ^ 14 + 54132736 * X ^ 15 : ℚ⟦X⟧) * G ^ 2 + (1368 * X ^ 8 - 49344 * X ^ 9 + 746496 * X ^ 10 - 6135552 * X ^ 11 + 29571072 * X ^ 12 - 83521536 * X ^ 13 + 127893504 * X ^ 14 - 81788928 * X ^ 15 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (54 * X ^ 7 - 2160 * X ^ 8 + 36000 * X ^ 9 - 322560 * X ^ 10 + 1664256 * X ^ 11 - 4847616 * X ^ 12 + 6868992 * X ^ 13 - 1769472 * X ^ 14 - 3932160 * X ^ 15 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (-1440 * X ^ 7 + 51360 * X ^ 8 - 753024 * X ^ 9 + 5840384 * X ^ 10 - 25604096 * X ^ 11 + 62169088 * X ^ 12 - 73859072 * X ^ 13 + 28573696 * X ^ 14 : ℚ⟦X⟧) * G ^ 3 + (504 * X ^ 6 - 20544 * X ^ 7 + 357888 * X ^ 8 - 3475200 * X ^ 9 + 20550144 * X ^ 10 - 75703296 * X ^ 11 + 169398272 * X ^ 12 - 209879040 * X ^ 13 + 109576192 * X ^ 14 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-1152 * X ^ 7 + 41472 * X ^ 8 - 625152 * X ^ 9 + 5117952 * X ^ 10 - 24600576 * X ^ 11 + 69500928 * X ^ 12 - 106954752 * X ^ 13 + 69206016 * X ^ 14 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) ^ 2 + (-18 * X ^ 5 + 240 * X ^ 6 + 2136 * X ^ 7 - 52800 * X ^ 8 + 219904 * X ^ 9 + 1263616 * X ^ 10 - 13628416 * X ^ 11 + 41984000 * X ^ 12 - 44498944 * X ^ 13 : ℚ⟦X⟧) * G ^ 4 + (-2856 * X ^ 6 + 100416 * X ^ 7 - 1499520 * X ^ 8 + 12390912 * X ^ 9 - 61501440 * X ^ 10 + 184098816 * X ^ 11 - 308477952 * X ^ 12 + 223346688 * X ^ 13 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (-486 * X ^ 5 + 19440 * X ^ 6 - 333504 * X ^ 7 + 3207168 * X ^ 8 - 18920448 * X ^ 9 + 70115328 * X ^ 10 - 159178752 * X ^ 11 + 201719808 * X ^ 12 - 108527616 * X ^ 13 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) ^ 2 + (2064 * X ^ 5 - 69792 * X ^ 6 + 983040 * X ^ 7 - 7515648 * X ^ 8 + 34025472 * X ^ 9 - 92340224 * X ^ 10 + 140771328 * X ^ 11 - 93847552 * X ^ 12 : ℚ⟦X⟧) * G ^ 5 + (-432 * X ^ 4 + 17856 * X ^ 5 - 331392 * X ^ 6 + 3601920 * X ^ 7 - 24926208 * X ^ 8 + 111544320 * X ^ 9 - 312729600 * X ^ 10 + 499187712 * X ^ 11 - 346030080 * X ^ 12 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (864 * X ^ 5 - 31104 * X ^ 6 + 481536 * X ^ 7 - 4193280 * X ^ 8 + 22302720 * X ^ 9 - 72400896 * X ^ 10 + 132120576 * X ^ 11 - 103809024 * X ^ 12 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) ^ 2 + (-162 * X ^ 3 + 7920 * X ^ 4 - 150576 * X ^ 5 + 1475712 * X ^ 6 - 8046336 * X ^ 7 + 23515136 * X ^ 8 - 27299840 * X ^ 9 - 20086784 * X ^ 10 + 58458112 * X ^ 11 : ℚ⟦X⟧) * G ^ 6 + (360 * X ^ 4 - 11328 * X ^ 5 + 150528 * X ^ 6 - 1104384 * X ^ 7 + 4872192 * X ^ 8 - 13000704 * X ^ 9 + 19464192 * X ^ 10 - 12582912 * X ^ 11 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (810 * X ^ 3 - 32400 * X ^ 4 + 568800 * X ^ 5 - 5760000 * X ^ 6 + 36945408 * X ^ 7 - 153833472 * X ^ 8 + 405479424 * X ^ 9 - 616955904 * X ^ 10 + 413663232 * X ^ 11 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) ^ 2 + (-864 * X ^ 3 + 36192 * X ^ 4 - 606336 * X ^ 5 + 5270016 * X ^ 6 - 25659392 * X ^ 7 + 70008832 * X ^ 8 - 99352576 * X ^ 9 + 57147392 * X ^ 10 : ℚ⟦X⟧) * G ^ 7 + (-864 * X ^ 3 + 44160 * X ^ 4 - 860928 * X ^ 5 + 8719872 * X ^ 6 - 50823168 * X ^ 7 + 172793856 * X ^ 8 - 319488000 * X ^ 9 + 248512512 * X ^ 10 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (5184 * X ^ 3 - 186624 * X ^ 4 + 2843136 * X ^ 5 - 23869440 * X ^ 6 + 119808000 * X ^ 7 - 360677376 * X ^ 8 + 603979776 * X ^ 9 - 434110464 * X ^ 10 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) ^ 2 + (-3132 * X ^ 3 + 95136 * X ^ 4 - 1280640 * X ^ 5 + 9523200 * X ^ 6 - 40236032 * X ^ 7 + 90120192 * X ^ 8 - 83034112 * X ^ 9 : ℚ⟦X⟧) * G ^ 8 + (-2304 * X ^ 3 + 118848 * X ^ 4 - 2066688 * X ^ 5 + 17126400 * X ^ 6 - 74428416 * X ^ 7 + 164462592 * X ^ 8 - 146276352 * X ^ 9 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (12528 * X ^ 3 - 400896 * X ^ 4 + 5225472 * X ^ 5 - 35610624 * X ^ 6 + 134369280 * X ^ 7 - 267190272 * X ^ 8 + 219414528 * X ^ 9 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) ^ 2 + (-16704 * X ^ 3 + 391680 * X ^ 4 - 3765248 * X ^ 5 + 18612224 * X ^ 6 - 47382528 * X ^ 7 + 49545216 * X ^ 8 : ℚ⟦X⟧) * G ^ 9 + (4224 * X ^ 3 - 42240 * X ^ 4 - 233472 * X ^ 5 + 4100096 * X ^ 6 - 16023552 * X ^ 7 + 19922944 * X ^ 8 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (13440 * X ^ 3 - 376320 * X ^ 4 + 4085760 * X ^ 5 - 21504000 * X ^ 6 + 55050240 * X ^ 7 - 55050240 * X ^ 8 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) ^ 2 + (-29568 * X ^ 3 + 568320 * X ^ 4 - 4126720 * X ^ 5 + 13320192 * X ^ 6 - 16121856 * X ^ 7 : ℚ⟦X⟧) * G ^ 10 + (14592 * X ^ 3 - 282624 * X ^ 4 + 1953792 * X ^ 5 - 5799936 * X ^ 6 + 6291456 * X ^ 7 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (5376 * X ^ 3 - 129024 * X ^ 4 + 1118208 * X ^ 5 - 4128768 * X ^ 6 + 5505024 * X ^ 7 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) ^ 2 + (-18432 * X ^ 3 + 270336 * X ^ 4 - 1376256 * X ^ 5 + 2359296 * X ^ 6 : ℚ⟦X⟧) * G ^ 11 + (9216 * X ^ 3 - 159744 * X ^ 4 + 884736 * X ^ 5 - 1572864 * X ^ 6 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (-3072 * X ^ 3 + 24576 * X ^ 4 - 65536 * X ^ 5 : ℚ⟦X⟧) * G ^ 12) * hd1 +
      ((-6 * X ^ 10 + 240 * X ^ 11 - 4160 * X ^ 12 + 40832 * X ^ 13 - 248320 * X ^ 14 + 958464 * X ^ 15 - 2293760 * X ^ 16 + 3112960 * X ^ 17 - 1835008 * X ^ 18 : ℚ⟦X⟧) + (12 * X ^ 11 - 432 * X ^ 12 + 6528 * X ^ 13 - 53760 * X ^ 14 + 261120 * X ^ 15 - 749568 * X ^ 16 + 1179648 * X ^ 17 - 786432 * X ^ 18 : ℚ⟦X⟧) * (derivative ℚ G) + (96 * X ^ 10 - 3408 * X ^ 11 + 51200 * X ^ 12 - 422400 * X ^ 13 + 2068480 * X ^ 14 - 6017024 * X ^ 15 + 9633792 * X ^ 16 - 6553600 * X ^ 17 : ℚ⟦X⟧) * G + (18 * X ^ 9 - 720 * X ^ 10 + 12240 * X ^ 11 - 115200 * X ^ 12 + 654336 * X ^ 13 - 2285568 * X ^ 14 + 4755456 * X ^ 15 - 5308416 * X ^ 16 + 2359296 * X ^ 17 : ℚ⟦X⟧) * G * (derivative ℚ G) + (54 * X ^ 8 - 2160 * X ^ 9 + 36960 * X ^ 10 - 352320 * X ^ 11 + 2039040 * X ^ 12 - 7302144 * X ^ 13 + 15691776 * X ^ 14 - 18284544 * X ^ 15 + 8650752 * X ^ 16 : ℚ⟦X⟧) * G ^ 2 + (-288 * X ^ 9 + 10368 * X ^ 10 - 156096 * X ^ 11 + 1274112 * X ^ 12 - 6091776 * X ^ 13 + 17068032 * X ^ 14 - 25952256 * X ^ 15 + 16515072 * X ^ 16 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-576 * X ^ 8 + 20352 * X ^ 9 - 303616 * X ^ 10 + 2478336 * X ^ 11 - 11950080 * X ^ 12 + 34033664 * X ^ 13 - 53018624 * X ^ 14 + 34865152 * X ^ 15 : ℚ⟦X⟧) * G ^ 3 + (-162 * X ^ 7 + 6480 * X ^ 8 - 110304 * X ^ 9 + 1041408 * X ^ 10 - 5949696 * X ^ 11 + 20994048 * X ^ 12 - 44470272 * X ^ 13 + 51314688 * X ^ 14 - 24379392 * X ^ 15 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-162 * X ^ 6 + 6480 * X ^ 7 - 111456 * X ^ 8 + 1073664 * X ^ 9 - 6316032 * X ^ 10 + 23159808 * X ^ 11 - 51507200 * X ^ 12 + 63209472 * X ^ 13 - 32505856 * X ^ 14 : ℚ⟦X⟧) * G ^ 4 + (1080 * X ^ 7 - 38880 * X ^ 8 + 587520 * X ^ 9 - 4838400 * X ^ 10 + 23500800 * X ^ 11 - 67461120 * X ^ 12 + 106168320 * X ^ 13 - 70778880 * X ^ 14 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (864 * X ^ 6 - 30240 * X ^ 7 + 451584 * X ^ 8 - 3732480 * X ^ 9 + 18432000 * X ^ 10 - 54337536 * X ^ 11 + 88473600 * X ^ 12 - 61341696 * X ^ 13 : ℚ⟦X⟧) * G ^ 5 + (486 * X ^ 5 - 19440 * X ^ 6 + 335232 * X ^ 7 - 3262464 * X ^ 8 + 19639296 * X ^ 9 - 74981376 * X ^ 10 + 177315840 * X ^ 11 - 237109248 * X ^ 12 + 136839168 * X ^ 13 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (162 * X ^ 4 - 6480 * X ^ 5 + 115488 * X ^ 6 - 1192320 * X ^ 7 + 7742976 * X ^ 8 - 32151552 * X ^ 9 + 82862080 * X ^ 10 - 120717312 * X ^ 11 + 76021760 * X ^ 12 : ℚ⟦X⟧) * G ^ 6 + (-8064 * X ^ 7 + 225792 * X ^ 8 - 2451456 * X ^ 9 + 12902400 * X ^ 10 - 33030144 * X ^ 11 + 33030144 * X ^ 12 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (-4608 * X ^ 6 + 115200 * X ^ 7 - 1118208 * X ^ 8 + 5283840 * X ^ 9 - 12189696 * X ^ 10 + 11010048 * X ^ 11 : ℚ⟦X⟧) * G ^ 7 + (-486 * X ^ 3 + 19440 * X ^ 4 - 341280 * X ^ 5 + 3456000 * X ^ 6 - 22169088 * X ^ 7 + 92344320 * X ^ 8 - 243671040 * X ^ 9 + 371589120 * X ^ 10 - 250085376 * X ^ 11 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (-4320 * X ^ 4 + 120960 * X ^ 5 - 1396224 * X ^ 6 + 8570880 * X ^ 7 - 29614080 * X ^ 8 + 54558720 * X ^ 9 - 41680896 * X ^ 10 : ℚ⟦X⟧) * G ^ 8 + (-2916 * X ^ 3 + 104976 * X ^ 4 - 1600128 * X ^ 5 + 13450752 * X ^ 6 - 67654656 * X ^ 7 + 204263424 * X ^ 8 - 343277568 * X ^ 9 + 247726080 * X ^ 10 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (-1296 * X ^ 3 + 24576 * X ^ 4 - 139776 * X ^ 5 - 4096 * X ^ 6 + 2682880 * X ^ 7 - 8978432 * X ^ 8 + 9175040 * X ^ 9 : ℚ⟦X⟧) * G ^ 9 + (-6480 * X ^ 3 + 207360 * X ^ 4 - 2703360 * X ^ 5 + 18432000 * X ^ 6 - 69611520 * X ^ 7 + 138608640 * X ^ 8 - 114032640 * X ^ 9 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (-5184 * X ^ 3 + 115968 * X ^ 4 - 998400 * X ^ 5 + 4206592 * X ^ 6 - 8847360 * X ^ 7 + 7602176 * X ^ 8 : ℚ⟦X⟧) * G ^ 10 + (-6336 * X ^ 3 + 177408 * X ^ 4 - 1926144 * X ^ 5 + 10137600 * X ^ 6 - 25952256 * X ^ 7 + 25952256 * X ^ 8 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (-6912 * X ^ 3 + 141312 * X ^ 4 - 1044480 * X ^ 5 + 3342336 * X ^ 6 - 3932160 * X ^ 7 : ℚ⟦X⟧) * G ^ 11 + (-2304 * X ^ 3 + 55296 * X ^ 4 - 479232 * X ^ 5 + 1769472 * X ^ 6 - 2359296 * X ^ 7 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (-3072 * X ^ 3 + 53248 * X ^ 4 - 294912 * X ^ 5 + 524288 * X ^ 6 : ℚ⟦X⟧) * G ^ 12) * hd2 +
      ((X ^ 11 - 40 * X ^ 12 + 688 * X ^ 13 - 6656 * X ^ 14 + 39680 * X ^ 15 - 149504 * X ^ 16 + 348160 * X ^ 17 - 458752 * X ^ 18 + 262144 * X ^ 19 : ℚ⟦X⟧) + (-16 * X ^ 11 + 576 * X ^ 12 - 8704 * X ^ 13 + 71680 * X ^ 14 - 348160 * X ^ 15 + 999424 * X ^ 16 - 1572864 * X ^ 17 + 1048576 * X ^ 18 : ℚ⟦X⟧) * G + (-12 * X ^ 9 + 480 * X ^ 10 - 8160 * X ^ 11 + 76800 * X ^ 12 - 436224 * X ^ 13 + 1523712 * X ^ 14 - 3170304 * X ^ 15 + 3538944 * X ^ 16 - 1572864 * X ^ 17 : ℚ⟦X⟧) * G ^ 2 + (128 * X ^ 9 - 4608 * X ^ 10 + 69376 * X ^ 11 - 566272 * X ^ 12 + 2707456 * X ^ 13 - 7585792 * X ^ 14 + 11534336 * X ^ 15 - 7340032 * X ^ 16 : ℚ⟦X⟧) * G ^ 3 + (54 * X ^ 7 - 2160 * X ^ 8 + 36768 * X ^ 9 - 347136 * X ^ 10 + 1983232 * X ^ 11 - 6998016 * X ^ 12 + 14823424 * X ^ 13 - 17104896 * X ^ 14 + 8126464 * X ^ 15 : ℚ⟦X⟧) * G ^ 4 + (-288 * X ^ 7 + 10368 * X ^ 8 - 156672 * X ^ 9 + 1290240 * X ^ 10 - 6266880 * X ^ 11 + 17989632 * X ^ 12 - 28311552 * X ^ 13 + 18874368 * X ^ 14 : ℚ⟦X⟧) * G ^ 5 + (-108 * X ^ 5 + 4320 * X ^ 6 - 74496 * X ^ 7 + 724992 * X ^ 8 - 4364288 * X ^ 9 + 16662528 * X ^ 10 - 39403520 * X ^ 11 + 52690944 * X ^ 12 - 30408704 * X ^ 13 : ℚ⟦X⟧) * G ^ 6 + (1536 * X ^ 7 - 43008 * X ^ 8 + 466944 * X ^ 9 - 2457600 * X ^ 10 + 6291456 * X ^ 11 - 6291456 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 + (81 * X ^ 3 - 3240 * X ^ 4 + 56880 * X ^ 5 - 576000 * X ^ 6 + 3694848 * X ^ 7 - 15390720 * X ^ 8 + 40611840 * X ^ 9 - 61931520 * X ^ 10 + 41680896 * X ^ 11 : ℚ⟦X⟧) * G ^ 8 + (432 * X ^ 3 - 15552 * X ^ 4 + 237056 * X ^ 5 - 1992704 * X ^ 6 + 10022912 * X ^ 7 - 30261248 * X ^ 8 + 50855936 * X ^ 9 - 36700160 * X ^ 10 : ℚ⟦X⟧) * G ^ 9 + (864 * X ^ 3 - 27648 * X ^ 4 + 360448 * X ^ 5 - 2457600 * X ^ 6 + 9281536 * X ^ 7 - 18481152 * X ^ 8 + 15204352 * X ^ 9 : ℚ⟦X⟧) * G ^ 10 + (768 * X ^ 3 - 21504 * X ^ 4 + 233472 * X ^ 5 - 1228800 * X ^ 6 + 3145728 * X ^ 7 - 3145728 * X ^ 8 : ℚ⟦X⟧) * G ^ 11 + (256 * X ^ 3 - 6144 * X ^ 4 + 53248 * X ^ 5 - 196608 * X ^ 6 + 262144 * X ^ 7 : ℚ⟦X⟧) * G ^ 12) * hd3
  have hres : ((-33554432 * X ^ 2 + 268435456 * X ^ 3 - 469762048 * X ^ 4 : ℚ⟦X⟧) + (184549376 * X ^ 2 - 738197504 * X ^ 3 : ℚ⟦X⟧) * G + (50331648 - 402653184 * X + 872415232 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (50331648 - 201326592 * X : ℚ⟦X⟧) * G ^ 3) * ((-X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) + (4 * X ^ 2 : ℚ⟦X⟧) * G + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3) = (33554432 * X ^ 4 - 402653184 * X ^ 5 + 1073741824 * X ^ 6 : ℚ⟦X⟧) := by
    linear_combination (-((-469762048 * X ^ 2 + 1879048192 * X ^ 3 : ℚ⟦X⟧) + (-150994944 + 1207959552 * X - 2684354560 * X ^ 2 : ℚ⟦X⟧) * G + (-201326592 + 805306368 * X : ℚ⟦X⟧) * G ^ 2)) * hP
  have hd0 : (33554432 - 402653184 * X + 1073741824 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    have kc : constantCoeff (33554432 : ℚ⟦X⟧) = 33554432 := cnum 33554432
    simp [kc] at h'
  have hdisc : (33554432 * X ^ 4 - 402653184 * X ^ 5 + 1073741824 * X ^ 6 : ℚ⟦X⟧) ≠ 0 := by
    have e : (33554432 * X ^ 4 - 402653184 * X ^ 5 + 1073741824 * X ^ 6 : ℚ⟦X⟧) = X ^ 4 * (33554432 - 402653184 * X + 1073741824 * X ^ 2 : ℚ⟦X⟧) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 4 X_ne_zero) hd0
  have hPG : (-X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) + (4 * X ^ 2 : ℚ⟦X⟧) * G + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hres
    exact hdisc hres.symm
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 5 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (X ^ 4 : ℚ⟦X⟧) + (-X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) * G + (2 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 - 4 * X : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 1 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-24) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C 208 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C (-768) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * C 1024 + derivative ℚ (derivative ℚ G) * X * X * X * C (-12) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 208 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-1152) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 2048 + derivative ℚ G * X * X * X * C (-12) +
      derivative ℚ G * X * X * X * X * C 96 + derivative ℚ G * X * X * X * X * X * C (-256) +
      G * X * X * X * C (-48) + G * X * X * X * X * C 256 =
      C (-16) * X * X * X * X := by
  have h := key G hP
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (X ^ 4 : ℚ⟦X⟧) + (-X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) * G + (2 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 - 4 * X : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0) (m : ℕ) :
    1 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-24) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      208 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-768) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      1024 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + (-12) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      208 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-1152) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      2048 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + (-12) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      96 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + (-256) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      (-48) * coeff (m + 1 + 1 + 1 + 1) G + 256 * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (X ^ 4 : ℚ⟦X⟧) + (-X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) * G + (2 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 - 4 * X : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0) :
    60 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-576) * coeff (0 + 1 + 1 + 1 + 1) G +
      1248 * coeff (0 + 1 + 1 + 1) G + (-144) * coeff (0 + 1 + 1 + 1 + 1) G +
      1248 * coeff (0 + 1 + 1 + 1) G + (-2304) * coeff (0 + 1 + 1) G +
      (-36) * coeff (0 + 1 + 1 + 1) G + 192 * coeff (0 + 1 + 1) G +
      (-256) * coeff (0 + 1) G + (-48) * coeff (0 + 1 + 1) G +
      256 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (X ^ 4 : ℚ⟦X⟧) + (-X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) * G + (2 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 - 4 * X : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0) :
    120 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-1440) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      4992 * coeff (0 + 1 + 1 + 1 + 1) G + (-4608) * coeff (0 + 1 + 1 + 1) G +
      (-240) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 2496 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-6912) * coeff (0 + 1 + 1 + 1) G + 4096 * coeff (0 + 1 + 1) G +
      (-48) * coeff (0 + 1 + 1 + 1 + 1) G + 288 * coeff (0 + 1 + 1 + 1) G +
      (-512) * coeff (0 + 1 + 1) G + (-48) * coeff (0 + 1 + 1 + 1) G +
      256 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A218185Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a218185.main := by
  intro T W G hT _ hW _ hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  rw [e1, e2, e3, e4]
  have kn4 : PowerSeries.constantCoeff (4 : PowerSeries ℚ) = 4 := A218185Aux.cnum 4
  have hN1 : ((4) : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [kn4] at h'
  have hM : ((4)) ^ 4 * ((PowerSeries.X ^ 4 : PowerSeries ℚ) + (-PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3 : PowerSeries ℚ) * G + (2 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (1 - 4 * PowerSeries.X : PowerSeries ℚ) * G ^ 3 + (1 : PowerSeries ℚ) * G ^ 4) = 0 := by
    linear_combination ((8) + (-8) * W + (16) * T + (-16) * T * W + (8) * T ^ 2 + (-8) * T ^ 2 * W + (-48) * PowerSeries.X + (32) * PowerSeries.X * W + (-80) * PowerSeries.X * T + (48) * PowerSeries.X * T * W + (-32) * PowerSeries.X * T ^ 2 + (16) * PowerSeries.X * T ^ 2 * W + (48) * PowerSeries.X ^ 2 + (64) * PowerSeries.X ^ 2 * T + (16) * PowerSeries.X ^ 2 * T ^ 2 + (128) * PowerSeries.X ^ 3) * hT +
      ((-5) + (1) * W ^ 2 + (-8) * T + (-4) * T * W + (4) * T * W ^ 2 + (6) * T ^ 2 + (-12) * T ^ 2 * W + (6) * T ^ 2 * W ^ 2 + (16) * T ^ 3 + (-12) * T ^ 3 * W + (4) * T ^ 3 * W ^ 2 + (7) * T ^ 4 + (-4) * T ^ 4 * W + (1) * T ^ 4 * W ^ 2 + (44) * PowerSeries.X + (80) * PowerSeries.X * T + (24) * PowerSeries.X * T ^ 2 + (-16) * PowerSeries.X * T ^ 3 + (-4) * PowerSeries.X * T ^ 4 + (-64) * PowerSeries.X ^ 2 + (-128) * PowerSeries.X ^ 2 * T + (-64) * PowerSeries.X ^ 2 * T ^ 2) * hW +
      ((3) + (-5) * W + (1) * W ^ 2 + (1) * W ^ 3 + (5) * T + (-7) * T * W + (-1) * T * W ^ 2 + (3) * T * W ^ 3 + (1) * T ^ 2 + (1) * T ^ 2 * W + (-5) * T ^ 2 * W ^ 2 + (3) * T ^ 2 * W ^ 3 + (-1) * T ^ 3 + (3) * T ^ 3 * W + (-3) * T ^ 3 * W ^ 2 + (1) * T ^ 3 * W ^ 3 + (-12) * G + (8) * G * W + (4) * G * W ^ 2 + (-8) * G * T + (8) * G * T * W ^ 2 + (4) * G * T ^ 2 + (-8) * G * T ^ 2 * W + (4) * G * T ^ 2 * W ^ 2 + (48) * G ^ 2 + (16) * G ^ 2 * W + (-16) * G ^ 2 * T + (16) * G ^ 2 * T * W + (64) * G ^ 3 + (-36) * PowerSeries.X + (40) * PowerSeries.X * W + (-4) * PowerSeries.X * W ^ 2 + (-40) * PowerSeries.X * T + (48) * PowerSeries.X * T * W + (-8) * PowerSeries.X * T * W ^ 2 + (-4) * PowerSeries.X * T ^ 2 + (8) * PowerSeries.X * T ^ 2 * W + (-4) * PowerSeries.X * T ^ 2 * W ^ 2 + (96) * PowerSeries.X * G + (-32) * PowerSeries.X * G * W + (32) * PowerSeries.X * G * T + (-32) * PowerSeries.X * G * T * W + (-192) * PowerSeries.X * G ^ 2 + (48) * PowerSeries.X ^ 2 + (-48) * PowerSeries.X ^ 2 * W + (48) * PowerSeries.X ^ 2 * T + (-48) * PowerSeries.X ^ 2 * T * W + (-64) * PowerSeries.X ^ 2 * G + (192) * PowerSeries.X ^ 3) * hG
  have hP : (PowerSeries.X ^ 4 : PowerSeries ℚ) + (-PowerSeries.X ^ 2 + 4 * PowerSeries.X ^ 3 : PowerSeries ℚ) * G + (2 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (1 - 4 * PowerSeries.X : PowerSeries ℚ) * G ^ 3 + (1 : PowerSeries ℚ) * G ^ 4 = 0 := (mul_eq_zero.mp hM).resolve_left (pow_ne_zero 4 hN1)
  cases m with
  | zero =>
    have r := A218185Aux.relE0 G hP
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A218185Aux.relE1 G hP
      push_cast
      linear_combination r
    | succ m =>
      have r := A218185Aux.rel G hP m
      push_cast
      linear_combination r
