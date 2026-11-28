import OMAStatements.S_oeis_a243642

-- Problem: A243642: Expansion of -(4*x)/((1-sqrt(1-4*x))/2-sqrt(-3*(1-sqrt(1-4*x))+(1-sqrt(1-4*x))^2/4+1)+1).
-- Upstream: formal-conjectures statements/oeis-a243642.lean:0 (declaration OMA.S_oeis_a243642.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A243642Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 3 : ℚ⟦X⟧) + (6 * X ^ 2 : ℚ⟦X⟧) * G + (4 * X + X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 + 2 * X : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (-1 : ℚ)) :
    (16 * X ^ 3 - 172 * X ^ 4 + 104 * X ^ 5 + 3479 * X ^ 6 - 9266 * X ^ 7 + 2368 * X ^ 8 + 96 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-300 * X ^ 3 + 2118 * X ^ 4 - 966 * X ^ 5 - 10950 * X ^ 6 + 456 * X ^ 7 + 192 * X ^ 8) * derivative ℚ (derivative ℚ G) + (228 * X ^ 3 - 486 * X ^ 4 - 516 * X ^ 5 + 1428 * X ^ 6 - 24 * X ^ 7) * derivative ℚ G + (-360 * X ^ 3 + 204 * X ^ 4 - 1488 * X ^ 5 + 24 * X ^ 6) * G =
      -24 * X ^ 3 + 372 * X ^ 4 + 528 * X ^ 5 + 24 * X ^ 6 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have hp0 : (4 * (X * X * X) : ℚ⟦X⟧) + (6 * (X * X) : ℚ⟦X⟧) * G + (4 * X + 1 * (X * X) : ℚ⟦X⟧) * G * G + (1 + 2 * X : ℚ⟦X⟧) * G * G * G + (1 : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((4 * (X * X * X) : ℚ⟦X⟧) + (6 * (X * X) : ℚ⟦X⟧) * G + (4 * X + 1 * (X * X) : ℚ⟦X⟧) * G * G + (1 + 2 * X : ℚ⟦X⟧) * G * G * G + (1 : ℚ⟦X⟧) * G * G * G * G) =
      (12 * X ^ 2 : ℚ⟦X⟧) + (6 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) + (12 * X : ℚ⟦X⟧) * G + (8 * X + 2 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (4 + 2 * X : ℚ⟦X⟧) * G ^ 2 + (3 + 6 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G ^ 3 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d2, d4, d6]
    ring
  have hd1 : (12 * X ^ 2 : ℚ⟦X⟧) + (6 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) + (12 * X : ℚ⟦X⟧) * G + (8 * X + 2 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ G) + (4 + 2 * X : ℚ⟦X⟧) * G ^ 2 + (3 + 6 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G ^ 3 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (12 * (X * X) : ℚ⟦X⟧) + (6 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (12 * X : ℚ⟦X⟧) * G + (8 * X + 2 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (4 + 2 * X : ℚ⟦X⟧) * G * G + (3 + 6 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G * G * G + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((12 * (X * X) : ℚ⟦X⟧) + (6 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) + (12 * X : ℚ⟦X⟧) * G + (8 * X + 2 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ G) + (4 + 2 * X : ℚ⟦X⟧) * G * G + (3 + 6 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G * G * G + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G)) =
      (24 * X : ℚ⟦X⟧) + (6 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (24 * X : ℚ⟦X⟧) * (derivative ℚ G) + (8 * X + 2 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (12 : ℚ⟦X⟧) * G + (8 * X + 2 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (16 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 + 12 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (2 : ℚ⟦X⟧) * G ^ 2 + (3 + 6 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d2, d3, d4, d6, d8, d12]
    ring
  have hd2 : (24 * X : ℚ⟦X⟧) + (6 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (24 * X : ℚ⟦X⟧) * (derivative ℚ G) + (8 * X + 2 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (12 : ℚ⟦X⟧) * G + (8 * X + 2 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (16 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 + 12 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (2 : ℚ⟦X⟧) * G ^ 2 + (3 + 6 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) = 0 := by rw [← hL2, hp1, map_zero]
  have hp2 : (24 * X : ℚ⟦X⟧) + (6 * (X * X) : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (24 * X : ℚ⟦X⟧) * (derivative ℚ G) + (8 * X + 2 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (12 : ℚ⟦X⟧) * G + (8 * X + 2 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (16 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 + 12 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G * G + (3 + 6 * X : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (12 : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) = 0 := by linear_combination hd2
  have hL3 : derivative ℚ ((24 * X : ℚ⟦X⟧) + (6 * (X * X) : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (24 * X : ℚ⟦X⟧) * (derivative ℚ G) + (8 * X + 2 * (X * X) : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (12 : ℚ⟦X⟧) * G + (8 * X + 2 * (X * X) : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (16 + 8 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 + 12 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (2 : ℚ⟦X⟧) * G * G + (3 + 6 * X : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (12 : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G))) =
      (24 : ℚ⟦X⟧) + (6 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (36 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (36 : ℚ⟦X⟧) * (derivative ℚ G) + (24 * X + 6 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (24 + 12 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (6 + 12 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (8 * X + 2 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (24 + 12 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G * (derivative ℚ G) + (18 + 36 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (36 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (24 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (3 + 6 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (18 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) := by
    simp [Derivation.leibniz, d2, d3, d4, d6, d8, d12, d16, d24]
    ring
  have hd3 : (24 : ℚ⟦X⟧) + (6 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (36 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (36 : ℚ⟦X⟧) * (derivative ℚ G) + (24 * X + 6 * X ^ 2 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (24 + 12 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (6 + 12 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (8 * X + 2 * X ^ 2 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (24 + 12 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (12 : ℚ⟦X⟧) * G * (derivative ℚ G) + (18 + 36 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (36 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (24 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (3 + 6 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (18 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) = 0 := by rw [← hL3, hp2, map_zero]
  have hfull : ((6 * X ^ 2 : ℚ⟦X⟧) + (8 * X + 2 * X ^ 2 : ℚ⟦X⟧) * G + (3 + 6 * X : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3) ^ 5 * ((16 * X ^ 3 - 172 * X ^ 4 + 104 * X ^ 5 + 3479 * X ^ 6 - 9266 * X ^ 7 + 2368 * X ^ 8 + 96 * X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-300 * X ^ 3 + 2118 * X ^ 4 - 966 * X ^ 5 - 10950 * X ^ 6 + 456 * X ^ 7 + 192 * X ^ 8) * derivative ℚ (derivative ℚ G) + (228 * X ^ 3 - 486 * X ^ 4 - 516 * X ^ 5 + 1428 * X ^ 6 - 24 * X ^ 7) * derivative ℚ G + (-360 * X ^ 3 + 204 * X ^ 4 - 1488 * X ^ 5 + 24 * X ^ 6) * G - (-24 * X ^ 3 + 372 * X ^ 4 + 528 * X ^ 5 + 24 * X ^ 6)) = 0 := by
    linear_combination ((-82944 * X ^ 8 + 1752192 * X ^ 9 - 7065792 * X ^ 10 - 18423936 * X ^ 11 + 97396992 * X ^ 12 - 56744064 * X ^ 13 + 58226688 * X ^ 14 - 12275712 * X ^ 15 - 497664 * X ^ 16 : ℚ⟦X⟧) + (-207360 * X ^ 7 + 5080320 * X ^ 8 - 20217600 * X ^ 9 - 66329280 * X ^ 10 + 241092288 * X ^ 11 - 11363328 * X ^ 12 + 455943168 * X ^ 13 - 121181184 * X ^ 14 - 5059584 * X ^ 15 : ℚ⟦X⟧) * G + (-207360 * X ^ 6 + 6143040 * X ^ 7 - 20429280 * X ^ 8 - 127163520 * X ^ 9 + 207112032 * X ^ 10 + 226348128 * X ^ 11 + 1628525952 * X ^ 12 - 437045760 * X ^ 13 - 18620928 * X ^ 14 - 13824 * X ^ 15 : ℚ⟦X⟧) * G ^ 2 + (-115200 * X ^ 5 + 4158720 * X ^ 6 - 6088320 * X ^ 7 - 159399360 * X ^ 8 + 29533248 * X ^ 9 + 259839360 * X ^ 10 + 3086627328 * X ^ 11 - 787364352 * X ^ 12 - 33984000 * X ^ 13 - 221184 * X ^ 14 : ℚ⟦X⟧) * G ^ 3 + (-38400 * X ^ 4 + 1614240 * X ^ 5 + 5146320 * X ^ 6 - 124511520 * X ^ 7 - 153979200 * X ^ 8 + 111964896 * X ^ 9 + 3334930944 * X ^ 10 - 766761984 * X ^ 11 - 50376576 * X ^ 12 - 2078592 * X ^ 13 - 4608 * X ^ 14 : ℚ⟦X⟧) * G ^ 4 + (-5760 * X ^ 3 + 283968 * X ^ 4 + 5366784 * X ^ 5 - 54263952 * X ^ 6 - 221948976 * X ^ 7 - 591744 * X ^ 8 + 2163053952 * X ^ 9 - 361675392 * X ^ 10 - 98348928 * X ^ 11 - 6992640 * X ^ 12 + 43008 * X ^ 13 : ℚ⟦X⟧) * G ^ 5 + (7440 * X ^ 3 + 1671720 * X ^ 4 - 9887520 * X ^ 5 - 149137224 * X ^ 6 - 71314632 * X ^ 7 + 834559392 * X ^ 8 - 16870272 * X ^ 9 - 178340736 * X ^ 10 - 13082496 * X ^ 11 + 304128 * X ^ 12 : ℚ⟦X⟧) * G ^ 6 + (142080 * X ^ 3 + 301440 * X ^ 4 - 53646336 * X ^ 5 - 74282496 * X ^ 6 + 148041600 * X ^ 7 + 29380608 * X ^ 8 - 226695168 * X ^ 9 - 19986432 * X ^ 10 + 743424 * X ^ 11 : ℚ⟦X⟧) * G ^ 7 + (153120 * X ^ 3 - 9812784 * X ^ 4 - 40177248 * X ^ 5 - 9642912 * X ^ 6 - 32028288 * X ^ 7 - 193473024 * X ^ 8 - 28970496 * X ^ 9 + 978432 * X ^ 10 : ℚ⟦X⟧) * G ^ 8 + (-783360 * X ^ 3 - 12069888 * X ^ 4 - 12712704 * X ^ 5 - 29117184 * X ^ 6 - 104990208 * X ^ 7 - 32403456 * X ^ 8 + 798720 * X ^ 9 : ℚ⟦X⟧) * G ^ 9 + (-1536000 * X ^ 3 - 5809152 * X ^ 4 - 7045632 * X ^ 5 - 31326720 * X ^ 6 - 23003136 * X ^ 7 + 430080 * X ^ 8 : ℚ⟦X⟧) * G ^ 10 + (-1105920 * X ^ 3 - 1585152 * X ^ 4 - 3317760 * X ^ 5 - 9068544 * X ^ 6 + 147456 * X ^ 7 : ℚ⟦X⟧) * G ^ 11 + (-368640 * X ^ 3 + 208896 * X ^ 4 - 1523712 * X ^ 5 + 24576 * X ^ 6 : ℚ⟦X⟧) * G ^ 12) * hP +
      ((235008 * X ^ 9 - 2035584 * X ^ 10 - 1771200 * X ^ 11 + 53491968 * X ^ 12 - 124512768 * X ^ 13 + 48406464 * X ^ 14 - 18662400 * X ^ 15 + 4091904 * X ^ 16 + 165888 * X ^ 17 : ℚ⟦X⟧) + (235008 * X ^ 9 - 1952640 * X ^ 10 - 2611008 * X ^ 11 + 52361856 * X ^ 12 - 104826528 * X ^ 13 + 3694464 * X ^ 14 + 17070912 * X ^ 15 - 1797120 * X ^ 16 - 82944 * X ^ 17 : ℚ⟦X⟧) * (derivative ℚ G) + (89856 * X ^ 9 - 952128 * X ^ 10 + 442368 * X ^ 11 + 19553616 * X ^ 12 - 48987072 * X ^ 13 + 6795792 * X ^ 14 - 1417824 * X ^ 15 + 1105920 * X ^ 16 + 41472 * X ^ 17 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (940032 * X ^ 8 - 7164288 * X ^ 9 - 14893632 * X ^ 10 + 216549504 * X ^ 11 - 394529184 * X ^ 12 + 10485504 * X ^ 13 - 119615616 * X ^ 14 + 43435008 * X ^ 15 + 1769472 * X ^ 16 : ℚ⟦X⟧) * G + (1004544 * X ^ 8 - 7631424 * X ^ 9 - 16716384 * X ^ 10 + 219292704 * X ^ 11 - 334232352 * X ^ 12 - 217795392 * X ^ 13 + 165806208 * X ^ 14 - 8781120 * X ^ 15 - 1345536 * X ^ 16 - 27648 * X ^ 17 : ℚ⟦X⟧) * G * (derivative ℚ G) + (377856 * X ^ 8 - 3737088 * X ^ 9 - 939456 * X ^ 10 + 83236032 * X ^ 11 - 147608784 * X ^ 12 - 111143232 * X ^ 13 - 4691808 * X ^ 14 + 13602240 * X ^ 15 + 1262592 * X ^ 16 + 27648 * X ^ 17 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (1601280 * X ^ 7 - 9612864 * X ^ 8 - 44898048 * X ^ 9 + 361970064 * X ^ 10 - 348232320 * X ^ 11 - 479317680 * X ^ 12 - 464906304 * X ^ 13 + 189475776 * X ^ 14 + 7916544 * X ^ 15 + 18432 * X ^ 16 : ℚ⟦X⟧) * G ^ 2 + (1806336 * X ^ 7 - 11389824 * X ^ 8 - 47611296 * X ^ 9 + 372242736 * X ^ 10 - 207869328 * X ^ 11 - 1128112272 * X ^ 12 + 458105616 * X ^ 13 + 40237056 * X ^ 14 - 6691968 * X ^ 15 - 262656 * X ^ 16 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (670080 * X ^ 7 - 5776416 * X ^ 8 - 10315968 * X ^ 9 + 147860520 * X ^ 10 - 74171664 * X ^ 11 - 581493024 * X ^ 12 - 157039680 * X ^ 13 + 68476752 * X ^ 14 + 13566624 * X ^ 15 + 519168 * X ^ 16 + 4608 * X ^ 17 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (1479168 * X ^ 6 - 4936320 * X ^ 7 - 67872960 * X ^ 8 + 294743232 * X ^ 9 + 226872000 * X ^ 10 - 1047714912 * X ^ 11 - 1252612800 * X ^ 12 + 453279168 * X ^ 13 + 26143488 * X ^ 14 + 354816 * X ^ 15 : ℚ⟦X⟧) * G ^ 3 + (1746432 * X ^ 6 - 6942048 * X ^ 7 - 74097360 * X ^ 8 + 299621808 * X ^ 9 + 495087744 * X ^ 10 - 2104666416 * X ^ 11 + 169693200 * X ^ 12 + 304655856 * X ^ 13 - 3054528 * X ^ 14 - 282240 * X ^ 15 + 10752 * X ^ 16 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (642048 * X ^ 6 - 4090368 * X ^ 7 - 23683392 * X ^ 8 + 132858816 * X ^ 9 + 250216848 * X ^ 10 - 1015545888 * X ^ 11 - 856089024 * X ^ 12 + 115674240 * X ^ 13 + 72110592 * X ^ 14 + 4454400 * X ^ 15 + 73728 * X ^ 16 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) ^ 2 + (774528 * X ^ 5 + 1214496 * X ^ 6 - 55712928 * X ^ 7 + 77141064 * X ^ 8 + 674822784 * X ^ 9 - 741727008 * X ^ 10 - 2168365200 * X ^ 11 + 591997152 * X ^ 12 + 82665312 * X ^ 13 + 2624448 * X ^ 14 + 8832 * X ^ 15 : ℚ⟦X⟧) * G ^ 4 + (956544 * X ^ 5 + 434016 * X ^ 6 - 64669488 * X ^ 7 + 63779328 * X ^ 8 + 967024824 * X ^ 9 - 1579315128 * X ^ 10 - 1199018376 * X ^ 11 + 602209488 * X ^ 12 + 69056832 * X ^ 13 + 5632896 * X ^ 14 + 152064 * X ^ 15 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (350784 * X ^ 5 - 758448 * X ^ 6 - 25433280 * X ^ 7 + 47198988 * X ^ 8 + 465605280 * X ^ 9 - 667890468 * X ^ 10 - 1918303128 * X ^ 11 - 172768176 * X ^ 12 + 208825056 * X ^ 13 + 21947904 * X ^ 14 + 511488 * X ^ 15 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) ^ 2 + (215808 * X ^ 4 + 2658912 * X ^ 5 - 22256016 * X ^ 6 - 60725328 * X ^ 7 + 508064952 * X ^ 8 + 183302352 * X ^ 9 - 2207699040 * X ^ 10 + 263630832 * X ^ 11 + 195432576 * X ^ 12 + 9250176 * X ^ 13 + 39936 * X ^ 14 : ℚ⟦X⟧) * G ^ 5 + (281088 * X ^ 4 + 2855184 * X ^ 5 - 28475208 * X ^ 6 - 84739032 * X ^ 7 + 656226168 * X ^ 8 + 40229544 * X ^ 9 - 2102657376 * X ^ 10 + 261580128 * X ^ 11 + 226008384 * X ^ 12 + 32209536 * X ^ 13 + 797184 * X ^ 14 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (103680 * X ^ 4 + 720000 * X ^ 5 - 13675824 * X ^ 6 - 20040912 * X ^ 7 + 339303132 * X ^ 8 + 138454848 * X ^ 9 - 2132794944 * X ^ 10 - 997528320 * X ^ 11 + 321853248 * X ^ 12 + 67843584 * X ^ 13 + 1963008 * X ^ 14 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) ^ 2 + (24768 * X ^ 3 + 1161456 * X ^ 4 - 1069536 * X ^ 5 - 56776764 * X ^ 6 + 128970744 * X ^ 7 + 546998436 * X ^ 8 - 1105652424 * X ^ 9 - 297566352 * X ^ 10 + 284467104 * X ^ 11 + 19133952 * X ^ 12 + 43776 * X ^ 13 : ℚ⟦X⟧) * G ^ 6 + (34560 * X ^ 3 + 1418784 * X ^ 4 - 2695416 * X ^ 5 - 74395116 * X ^ 6 + 130045788 * X ^ 7 + 774326832 * X ^ 8 - 1196995440 * X ^ 9 - 572564544 * X ^ 10 + 283044672 * X ^ 11 + 84445824 * X ^ 12 + 2105856 * X ^ 13 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (12960 * X ^ 3 + 462024 * X ^ 4 - 2780592 * X ^ 5 - 27898746 * X ^ 6 + 103644156 * X ^ 7 + 454706448 * X ^ 8 - 1105591200 * X ^ 9 - 1656933024 * X ^ 10 + 187254720 * X ^ 11 + 136040448 * X ^ 12 + 4525056 * X ^ 13 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) ^ 2 + (171552 * X ^ 3 + 2088192 * X ^ 4 - 14744712 * X ^ 5 - 26891760 * X ^ 6 + 261450024 * X ^ 7 - 67832640 * X ^ 8 - 422760000 * X ^ 9 + 239702976 * X ^ 10 + 26329728 * X ^ 11 - 107520 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 + (232344 * X ^ 3 + 2340900 * X ^ 4 - 20613780 * X ^ 5 - 63878832 * X ^ 6 + 400830048 * X ^ 7 + 83885760 * X ^ 8 - 763527744 * X ^ 9 + 93299328 * X ^ 10 + 127072512 * X ^ 11 + 3032064 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (82944 * X ^ 3 + 417024 * X ^ 4 - 10487808 * X ^ 5 - 5083200 * X ^ 6 + 244795392 * X ^ 7 - 77371776 * X ^ 8 - 1334647296 * X ^ 9 - 161155584 * X ^ 10 + 176467968 * X ^ 11 + 6414336 * X ^ 12 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) ^ 2 + (480132 * X ^ 3 + 824106 * X ^ 4 - 18523380 * X ^ 5 + 20769084 * X ^ 6 + 144103032 * X ^ 7 - 137056608 * X ^ 8 + 116030016 * X ^ 9 + 25325376 * X ^ 10 - 405888 * X ^ 11 : ℚ⟦X⟧) * G ^ 8 + (639888 * X ^ 3 + 587064 * X ^ 4 - 35232360 * X ^ 5 + 25952016 * X ^ 6 + 322705824 * X ^ 7 - 237146304 * X ^ 8 - 106554240 * X ^ 9 + 112506624 * X ^ 10 + 2239488 * X ^ 11 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (200448 * X ^ 3 - 910656 * X ^ 4 - 11159424 * X ^ 5 + 41863824 * X ^ 6 + 160373088 * X ^ 7 - 492471360 * X ^ 8 - 343046016 * X ^ 9 + 142497792 * X ^ 10 + 5474304 * X ^ 11 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) ^ 2 + (684000 * X ^ 3 - 916464 * X ^ 4 - 12119472 * X ^ 5 + 30117024 * X ^ 6 + 29548224 * X ^ 7 + 40535424 * X ^ 8 + 16627968 * X ^ 9 - 559104 * X ^ 10 : ℚ⟦X⟧) * G ^ 9 + (932160 * X ^ 3 - 3099168 * X ^ 4 - 26560224 * X ^ 5 + 80336448 * X ^ 6 + 82209408 * X ^ 7 - 89068032 * X ^ 8 + 54099456 * X ^ 9 + 509952 * X ^ 10 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (215040 * X ^ 3 - 1881600 * X ^ 4 - 3225600 * X ^ 5 + 49553280 * X ^ 6 - 31019520 * X ^ 7 - 217244160 * X ^ 8 + 64942080 * X ^ 9 + 2580480 * X ^ 10 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) ^ 2 + (580224 * X ^ 3 - 1324224 * X ^ 4 - 5259264 * X ^ 5 + 15766656 * X ^ 6 + 16988160 * X ^ 7 + 7094784 * X ^ 8 - 377856 * X ^ 9 : ℚ⟦X⟧) * G ^ 10 + (719616 * X ^ 3 - 4130688 * X ^ 4 - 6347136 * X ^ 5 + 45909888 * X ^ 6 - 4524288 * X ^ 7 + 10398720 * X ^ 8 - 294912 * X ^ 9 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (86016 * X ^ 3 - 924672 * X ^ 4 + 559104 * X ^ 5 + 18703104 * X ^ 6 - 49814016 * X ^ 7 + 12730368 * X ^ 8 + 516096 * X ^ 9 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) ^ 2 + (290304 * X ^ 3 - 836352 * X ^ 4 - 771840 * X ^ 5 + 4508928 * X ^ 6 + 1999872 * X ^ 7 - 110592 * X ^ 8 : ℚ⟦X⟧) * G ^ 11 + (230400 * X ^ 3 - 1626624 * X ^ 4 + 741888 * X ^ 5 + 8409600 * X ^ 6 - 350208 * X ^ 7 - 147456 * X ^ 8 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (58368 * X ^ 3 - 124416 * X ^ 4 - 132096 * X ^ 5 + 365568 * X ^ 6 - 6144 * X ^ 7 : ℚ⟦X⟧) * G ^ 12) * hd1 +
      ((-124416 * X ^ 10 + 948672 * X ^ 11 + 1936224 * X ^ 12 - 28304640 * X ^ 13 + 57861216 * X ^ 14 - 17822592 * X ^ 15 - 497664 * X ^ 16 : ℚ⟦X⟧) + (-82944 * X ^ 10 + 870912 * X ^ 11 - 316224 * X ^ 12 - 18169920 * X ^ 13 + 43526160 * X ^ 14 - 266976 * X ^ 15 - 3566592 * X ^ 16 - 124416 * X ^ 17 : ℚ⟦X⟧) * (derivative ℚ G) + (-580608 * X ^ 9 + 4002048 * X ^ 10 + 12130560 * X ^ 11 - 130341312 * X ^ 12 + 222818688 * X ^ 13 - 5629824 * X ^ 14 - 25920000 * X ^ 15 - 663552 * X ^ 16 : ℚ⟦X⟧) * G + (-393984 * X ^ 9 + 3945024 * X ^ 10 + 539136 * X ^ 11 - 87330960 * X ^ 12 + 164908224 * X ^ 13 + 105303888 * X ^ 14 - 33320160 * X ^ 15 - 4810752 * X ^ 16 - 124416 * X ^ 17 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-1181952 * X ^ 8 + 6765120 * X ^ 9 + 34297344 * X ^ 10 - 253211184 * X ^ 11 + 273418416 * X ^ 12 + 269663904 * X ^ 13 - 110227392 * X ^ 14 - 15655680 * X ^ 15 - 331776 * X ^ 16 : ℚ⟦X⟧) * G ^ 2 + (-815616 * X ^ 8 + 7471872 * X ^ 9 + 8360928 * X ^ 10 - 182878560 * X ^ 11 + 188866728 * X ^ 12 + 571175712 * X ^ 13 - 42091056 * X ^ 14 - 43669152 * X ^ 15 - 2640384 * X ^ 16 - 41472 * X ^ 17 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-1359360 * X ^ 7 + 5224320 * X ^ 8 + 55584576 * X ^ 9 - 253564704 * X ^ 10 - 47306160 * X ^ 11 + 772324848 * X ^ 12 - 92928096 * X ^ 13 - 89744256 * X ^ 14 - 4976640 * X ^ 15 - 73728 * X ^ 16 : ℚ⟦X⟧) * G ^ 3 + (-953472 * X ^ 7 + 7357536 * X ^ 8 + 23576640 * X ^ 9 - 212048376 * X ^ 10 - 84255696 * X ^ 11 + 1246713408 * X ^ 12 + 308730432 * X ^ 13 - 157416912 * X ^ 14 - 21556896 * X ^ 15 - 685056 * X ^ 16 - 4608 * X ^ 17 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-953472 * X ^ 6 + 675264 * X ^ 7 + 54685872 * X ^ 8 - 109539336 * X ^ 9 - 463156248 * X ^ 10 + 848656944 * X ^ 11 + 296556240 * X ^ 12 - 215733792 * X ^ 13 - 29635488 * X ^ 14 - 839040 * X ^ 15 - 6144 * X ^ 16 : ℚ⟦X⟧) * G ^ 4 + (-679680 * X ^ 6 + 3553920 * X ^ 7 + 32570640 * X ^ 8 - 136666800 * X ^ 9 - 438511860 * X ^ 10 + 1340451720 * X ^ 11 + 1267896600 * X ^ 12 - 217609920 * X ^ 13 - 91018080 * X ^ 14 - 4849920 * X ^ 15 - 69120 * X ^ 16 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (-407808 * X ^ 5 - 2016576 * X ^ 6 + 31499136 * X ^ 7 + 31985712 * X ^ 8 - 500387472 * X ^ 9 + 230189040 * X ^ 10 + 768645936 * X ^ 11 - 211756464 * X ^ 12 - 91255968 * X ^ 13 - 4396032 * X ^ 14 - 59904 * X ^ 15 : ℚ⟦X⟧) * G ^ 5 + (-295488 * X ^ 5 + 191664 * X ^ 6 + 25167168 * X ^ 7 - 31452588 * X ^ 8 - 493885728 * X ^ 9 + 588614796 * X ^ 10 + 2115960840 * X ^ 11 + 119342736 * X ^ 12 - 216754848 * X ^ 13 - 19819008 * X ^ 14 - 428544 * X ^ 15 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-98496 * X ^ 4 - 1664784 * X ^ 5 + 8325984 * X ^ 6 + 66434748 * X ^ 7 - 219742476 * X ^ 8 - 356623632 * X ^ 9 + 669676248 * X ^ 10 + 30389472 * X ^ 11 - 156505440 * X ^ 12 - 13714944 * X ^ 13 - 238080 * X ^ 14 : ℚ⟦X⟧) * G ^ 6 + (-72576 * X ^ 4 - 665280 * X ^ 5 + 10506888 * X ^ 6 + 21160440 * X ^ 7 - 273285306 * X ^ 8 - 180042912 * X ^ 9 + 1841095872 * X ^ 10 + 818947584 * X ^ 11 - 284685408 * X ^ 12 - 51916032 * X ^ 13 - 1451520 * X ^ 14 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (-10368 * X ^ 3 - 560736 * X ^ 4 - 914544 * X ^ 5 + 33861672 * X ^ 6 - 868428 * X ^ 7 - 369061380 * X ^ 8 + 124643016 * X ^ 9 + 234576432 * X ^ 10 - 145289376 * X ^ 11 - 27330048 * X ^ 12 - 483840 * X ^ 13 : ℚ⟦X⟧) * G ^ 7 + (-7776 * X ^ 3 - 310392 * X ^ 4 + 1666512 * X ^ 5 + 19953558 * X ^ 6 - 67214052 * X ^ 7 - 333881424 * X ^ 8 + 773618976 * X ^ 9 + 1177597152 * X ^ 10 - 153762624 * X ^ 11 - 90169344 * X ^ 12 - 2958336 * X ^ 13 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (-73548 * X ^ 3 - 1159794 * X ^ 4 + 6117354 * X ^ 5 + 38258352 * X ^ 6 - 121254840 * X ^ 7 - 181314144 * X ^ 8 + 156242016 * X ^ 9 - 57667968 * X ^ 10 - 34860672 * X ^ 11 - 493056 * X ^ 12 : ℚ⟦X⟧) * G ^ 8 + (-46656 * X ^ 3 - 276048 * X ^ 4 + 6210432 * X ^ 5 + 4017924 * X ^ 6 - 147368160 * X ^ 7 + 38097216 * X ^ 8 + 818149248 * X ^ 9 + 82461888 * X ^ 10 - 103140864 * X ^ 11 - 3732480 * X ^ 12 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (-216000 * X ^ 3 - 726336 * X ^ 4 + 13345632 * X ^ 5 + 3555576 * X ^ 6 - 123435504 * X ^ 7 - 9680544 * X ^ 8 + 4974912 * X ^ 9 - 27242496 * X ^ 10 - 138240 * X ^ 11 : ℚ⟦X⟧) * G ^ 9 + (-103680 * X ^ 3 + 454080 * X ^ 4 + 5950080 * X ^ 5 - 21718320 * X ^ 6 - 86664480 * X ^ 7 + 263620800 * X ^ 8 + 177383040 * X ^ 9 - 74434560 * X ^ 10 - 2856960 * X ^ 11 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (-325248 * X ^ 3 + 793536 * X ^ 4 + 10226880 * X ^ 5 - 21353760 * X ^ 6 - 46164864 * X ^ 7 + 4602240 * X ^ 8 - 11624448 * X ^ 9 + 190464 * X ^ 10 : ℚ⟦X⟧) * G ^ 10 + (-101376 * X ^ 3 + 887040 * X ^ 4 + 1520640 * X ^ 5 - 23360832 * X ^ 6 + 14623488 * X ^ 7 + 102415104 * X ^ 8 - 30615552 * X ^ 9 - 1216512 * X ^ 10 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (-248832 * X ^ 3 + 1363968 * X ^ 4 + 2391552 * X ^ 5 - 13901184 * X ^ 6 - 5794560 * X ^ 7 - 1880064 * X ^ 8 + 184320 * X ^ 9 : ℚ⟦X⟧) * G ^ 11 + (-36864 * X ^ 3 + 396288 * X ^ 4 - 239616 * X ^ 5 - 8015616 * X ^ 6 + 21348864 * X ^ 7 - 5455872 * X ^ 8 - 221184 * X ^ 9 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (-76800 * X ^ 3 + 542208 * X ^ 4 - 247296 * X ^ 5 - 2803200 * X ^ 6 + 116736 * X ^ 7 + 49152 * X ^ 8 : ℚ⟦X⟧) * G ^ 12) * hd2 +
      ((20736 * X ^ 11 - 222912 * X ^ 12 + 134784 * X ^ 13 + 4508784 * X ^ 14 - 12008736 * X ^ 15 + 3068928 * X ^ 16 + 124416 * X ^ 17 : ℚ⟦X⟧) + (110592 * X ^ 10 - 1161216 * X ^ 11 + 421632 * X ^ 12 + 24226560 * X ^ 13 - 58034880 * X ^ 14 + 355968 * X ^ 15 + 4755456 * X ^ 16 + 165888 * X ^ 17 : ℚ⟦X⟧) * G + (262656 * X ^ 9 - 2630016 * X ^ 10 - 359424 * X ^ 11 + 58220640 * X ^ 12 - 109938816 * X ^ 13 - 70202592 * X ^ 14 + 22213440 * X ^ 15 + 3207168 * X ^ 16 + 82944 * X ^ 17 : ℚ⟦X⟧) * G ^ 2 + (362496 * X ^ 8 - 3320832 * X ^ 9 - 3715968 * X ^ 10 + 81279360 * X ^ 11 - 83940768 * X ^ 12 - 253855872 * X ^ 13 + 18707136 * X ^ 14 + 19408512 * X ^ 15 + 1173504 * X ^ 16 + 18432 * X ^ 17 : ℚ⟦X⟧) * G ^ 3 + (317824 * X ^ 7 - 2452512 * X ^ 8 - 7858880 * X ^ 9 + 70682792 * X ^ 10 + 28085232 * X ^ 11 - 415571136 * X ^ 12 - 102910144 * X ^ 13 + 52472304 * X ^ 14 + 7185632 * X ^ 15 + 228352 * X ^ 16 + 1536 * X ^ 17 : ℚ⟦X⟧) * G ^ 4 + (181248 * X ^ 6 - 947712 * X ^ 7 - 8685504 * X ^ 8 + 36444480 * X ^ 9 + 116936496 * X ^ 10 - 357453792 * X ^ 11 - 338105760 * X ^ 12 + 58029312 * X ^ 13 + 24271488 * X ^ 14 + 1293312 * X ^ 15 + 18432 * X ^ 16 : ℚ⟦X⟧) * G ^ 5 + (65664 * X ^ 5 - 42592 * X ^ 6 - 5592704 * X ^ 7 + 6989464 * X ^ 8 + 109752384 * X ^ 9 - 130803288 * X ^ 10 - 470213520 * X ^ 11 - 26520608 * X ^ 12 + 48167744 * X ^ 13 + 4404224 * X ^ 14 + 95232 * X ^ 15 : ℚ⟦X⟧) * G ^ 6 + (13824 * X ^ 4 + 126720 * X ^ 5 - 2001312 * X ^ 6 - 4030560 * X ^ 7 + 52054344 * X ^ 8 + 34293888 * X ^ 9 - 350684928 * X ^ 10 - 155990016 * X ^ 11 + 54225792 * X ^ 12 + 9888768 * X ^ 13 + 276480 * X ^ 14 : ℚ⟦X⟧) * G ^ 7 + (1296 * X ^ 3 + 51732 * X ^ 4 - 277752 * X ^ 5 - 3325593 * X ^ 6 + 11202342 * X ^ 7 + 55646904 * X ^ 8 - 128936496 * X ^ 9 - 196266192 * X ^ 10 + 25627104 * X ^ 11 + 15028224 * X ^ 12 + 493056 * X ^ 13 : ℚ⟦X⟧) * G ^ 8 + (6912 * X ^ 3 + 40896 * X ^ 4 - 920064 * X ^ 5 - 595248 * X ^ 6 + 21832320 * X ^ 7 - 5644032 * X ^ 8 - 121207296 * X ^ 9 - 12216576 * X ^ 10 + 15280128 * X ^ 11 + 552960 * X ^ 12 : ℚ⟦X⟧) * G ^ 9 + (13824 * X ^ 3 - 60544 * X ^ 4 - 793344 * X ^ 5 + 2895776 * X ^ 6 + 11555264 * X ^ 7 - 35149440 * X ^ 8 - 23651072 * X ^ 9 + 9924608 * X ^ 10 + 380928 * X ^ 11 : ℚ⟦X⟧) * G ^ 10 + (12288 * X ^ 3 - 107520 * X ^ 4 - 184320 * X ^ 5 + 2831616 * X ^ 6 - 1772544 * X ^ 7 - 12413952 * X ^ 8 + 3710976 * X ^ 9 + 147456 * X ^ 10 : ℚ⟦X⟧) * G ^ 11 + (4096 * X ^ 3 - 44032 * X ^ 4 + 26624 * X ^ 5 + 890624 * X ^ 6 - 2372096 * X ^ 7 + 606208 * X ^ 8 + 24576 * X ^ 9 : ℚ⟦X⟧) * G ^ 12) * hd3
  have k3 : constantCoeff (3 : ℚ⟦X⟧) = 3 := cnum 3
  have k4 : constantCoeff (4 : ℚ⟦X⟧) = 4 := cnum 4
  have hPG : (6 * X ^ 2 : ℚ⟦X⟧) + (8 * X + 2 * X ^ 2 : ℚ⟦X⟧) * G + (3 + 6 * X : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k3, k4] at h'
    norm_num at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 5 hPG)
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 3 : ℚ⟦X⟧) + (6 * X ^ 2 : ℚ⟦X⟧) * G + (4 * X + X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 + 2 * X : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (-1 : ℚ)) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 16 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-172) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C 104 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C 3479 +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * C (-9266) + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * X * C 2368 +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * X * X * C 96 + derivative ℚ (derivative ℚ G) * X * X * X * C (-300) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 2118 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-966) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-10950) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C 456 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * X * C 192 + derivative ℚ G * X * X * X * C 228 +
      derivative ℚ G * X * X * X * X * C (-486) + derivative ℚ G * X * X * X * X * X * C (-516) +
      derivative ℚ G * X * X * X * X * X * X * C 1428 + derivative ℚ G * X * X * X * X * X * X * X * C (-24) +
      G * X * X * X * C (-360) + G * X * X * X * X * C 204 +
      G * X * X * X * X * X * C (-1488) + G * X * X * X * X * X * X * C 24 =
      C (-24) * X * X * X + C 372 * X * X * X * X +
      C 528 * X * X * X * X * X + C 24 * X * X * X * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 3 : ℚ⟦X⟧) + (6 * X ^ 2 : ℚ⟦X⟧) * G + (4 * X + X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 + 2 * X : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (-1 : ℚ)) (m : ℕ) :
    16 * ((m : ℚ) + 9) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-172) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      104 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 3479 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-9266) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 2368 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      96 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + (-300) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      2118 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-966) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-10950) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 456 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      192 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + 228 * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-486) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-516) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      1428 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + (-24) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      (-360) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 204 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-1488) * coeff (m + 1 + 1 + 1 + 1) G + 24 * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 3 : ℚ⟦X⟧) + (6 * X ^ 2 : ℚ⟦X⟧) * G + (4 * X + X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 + 2 * X : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (-1 : ℚ)) :
    3360 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-20640) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      6240 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 83496 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-55596) * coeff (0 + 1 + 1 + 1) G + (-9000) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      42360 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-11592) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-65700) * coeff (0 + 1 + 1 + 1) G + 912 * coeff (0 + 1 + 1) G +
      1140 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-1944) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-1548) * coeff (0 + 1 + 1 + 1) G + 2856 * coeff (0 + 1 + 1) G +
      (-24) * coeff (0 + 1) G + (-360) * coeff (0 + 1 + 1 + 1 + 1) G +
      204 * coeff (0 + 1 + 1 + 1) G + (-1488) * coeff (0 + 1 + 1) G +
      24 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (4 * X ^ 3 : ℚ⟦X⟧) + (6 * X ^ 2 : ℚ⟦X⟧) * G + (4 * X + X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (1 + 2 * X : ℚ⟦X⟧) * G ^ 3 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (-1 : ℚ)) :
    5376 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-36120) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      12480 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 208740 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-222384) * coeff (0 + 1 + 1 + 1 + 1) G + 14208 * coeff (0 + 1 + 1 + 1) G +
      (-12600) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 63540 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-19320) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-131400) * coeff (0 + 1 + 1 + 1 + 1) G +
      2736 * coeff (0 + 1 + 1 + 1) G + 384 * coeff (0 + 1 + 1) G +
      1368 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-2430) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-2064) * coeff (0 + 1 + 1 + 1 + 1) G + 4284 * coeff (0 + 1 + 1 + 1) G +
      (-48) * coeff (0 + 1 + 1) G + (-360) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      204 * coeff (0 + 1 + 1 + 1 + 1) G + (-1488) * coeff (0 + 1 + 1 + 1) G +
      24 * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A243642Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a243642.main := by
  intro T V G hT _ hV _ hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 7, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 := rfl
  rw [e1, e2, e3, e4, e5, e6]
  have hn : ((3) + (-2) * V + (-1) * T) * ((768) + (512) * V + (512) * T + (512) * T * V + (-256) * T ^ 2) = (16384 * PowerSeries.X : PowerSeries ℚ) := by
    linear_combination ((-4096)) * hT + ((-256) + (-256) * T) * hV
  have hnu0 : (16384 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    have kc : PowerSeries.constantCoeff (16384 : PowerSeries ℚ) = 16384 := A243642Aux.cnum 16384
    simp [kc] at h'
  have hnu : (16384 * PowerSeries.X : PowerSeries ℚ) ≠ 0 := by
    have e : (16384 * PowerSeries.X : PowerSeries ℚ) = PowerSeries.X ^ 1 * (16384 : PowerSeries ℚ) := by ring
    rw [e]
    exact mul_ne_zero (pow_ne_zero 1 PowerSeries.X_ne_zero) hnu0
  have hN1 : ((3) + (-2) * V + (-1) * T) ≠ 0 := by
    intro h
    rw [h, zero_mul] at hn
    exact hnu hn.symm
  have hM : ((64 : PowerSeries ℚ) * PowerSeries.X ^ 0) * (((3) + (-2) * V + (-1) * T) ^ 4 * ((4 * PowerSeries.X ^ 3 : PowerSeries ℚ) + (6 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G + (4 * PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (1 + 2 * PowerSeries.X : PowerSeries ℚ) * G ^ 3 + (1 : PowerSeries ℚ) * G ^ 4)) = 0 := by
    linear_combination ((18432) * PowerSeries.X ^ 3 + (20480) * PowerSeries.X ^ 3 * V + (20480) * PowerSeries.X ^ 3 * T + (4096) * PowerSeries.X ^ 3 * T * V + (2048) * PowerSeries.X ^ 3 * T ^ 2) * hT +
      ((768) * PowerSeries.X ^ 3 + (1024) * PowerSeries.X ^ 3 * V ^ 2 + (2560) * PowerSeries.X ^ 3 * T + (2048) * PowerSeries.X ^ 3 * T * V + (1792) * PowerSeries.X ^ 3 * T ^ 2 + (4096) * PowerSeries.X ^ 4) * hV +
      ((1728) * G ^ 2 + (-3456) * G ^ 2 * V + (2304) * G ^ 2 * V ^ 2 + (-512) * G ^ 2 * V ^ 3 + (-1728) * G ^ 2 * T + (2304) * G ^ 2 * T * V + (-768) * G ^ 2 * T * V ^ 2 + (576) * G ^ 2 * T ^ 2 + (-384) * G ^ 2 * T ^ 2 * V + (-64) * G ^ 2 * T ^ 3 + (1728) * G ^ 3 + (-3456) * G ^ 3 * V + (2304) * G ^ 3 * V ^ 2 + (-512) * G ^ 3 * V ^ 3 + (-1728) * G ^ 3 * T + (2304) * G ^ 3 * T * V + (-768) * G ^ 3 * T * V ^ 2 + (576) * G ^ 3 * T ^ 2 + (-384) * G ^ 3 * T ^ 2 * V + (-64) * G ^ 3 * T ^ 3 + (2304) * PowerSeries.X * G + (-7680) * PowerSeries.X * G * V + (7168) * PowerSeries.X * G * V ^ 2 + (-2048) * PowerSeries.X * G * V ^ 3 + (-3840) * PowerSeries.X * G * T + (7168) * PowerSeries.X * G * T * V + (-3072) * PowerSeries.X * G * T * V ^ 2 + (1792) * PowerSeries.X * G * T ^ 2 + (-1536) * PowerSeries.X * G * T ^ 2 * V + (-256) * PowerSeries.X * G * T ^ 3 + (-1152) * PowerSeries.X * G ^ 2 + (-768) * PowerSeries.X * G ^ 2 * V + (2560) * PowerSeries.X * G ^ 2 * V ^ 2 + (-1024) * PowerSeries.X * G ^ 2 * V ^ 3 + (-384) * PowerSeries.X * G ^ 2 * T + (2560) * PowerSeries.X * G ^ 2 * T * V + (-1536) * PowerSeries.X * G ^ 2 * T * V ^ 2 + (640) * PowerSeries.X * G ^ 2 * T ^ 2 + (-768) * PowerSeries.X * G ^ 2 * T ^ 2 * V + (-128) * PowerSeries.X * G ^ 2 * T ^ 3 + (4224) * PowerSeries.X ^ 2 + (-4352) * PowerSeries.X ^ 2 * V + (5632) * PowerSeries.X ^ 2 * V ^ 2 + (-3072) * PowerSeries.X ^ 2 * V ^ 3 + (-2176) * PowerSeries.X ^ 2 * T + (5632) * PowerSeries.X ^ 2 * T * V + (-4608) * PowerSeries.X ^ 2 * T * V ^ 2 + (1408) * PowerSeries.X ^ 2 * T ^ 2 + (-2304) * PowerSeries.X ^ 2 * T ^ 2 * V + (-384) * PowerSeries.X ^ 2 * T ^ 3 + (4800) * PowerSeries.X ^ 2 * G + (640) * PowerSeries.X ^ 2 * G * V + (-1792) * PowerSeries.X ^ 2 * G * V ^ 2 + (-512) * PowerSeries.X ^ 2 * G * V ^ 3 + (320) * PowerSeries.X ^ 2 * G * T + (-1792) * PowerSeries.X ^ 2 * G * T * V + (-768) * PowerSeries.X ^ 2 * G * T * V ^ 2 + (-448) * PowerSeries.X ^ 2 * G * T ^ 2 + (-384) * PowerSeries.X ^ 2 * G * T ^ 2 * V + (-64) * PowerSeries.X ^ 2 * G * T ^ 3 + (-12800) * PowerSeries.X ^ 3 + (-10240) * PowerSeries.X ^ 3 * V + (-2048) * PowerSeries.X ^ 3 * V ^ 2 + (-5120) * PowerSeries.X ^ 3 * T + (-2048) * PowerSeries.X ^ 3 * T * V + (-512) * PowerSeries.X ^ 3 * T ^ 2) * hG
  have hc : (64 : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    rw [A243642Aux.cnum, map_zero] at h'
    norm_num at h'
  have hLne : ((64 : PowerSeries ℚ) * PowerSeries.X ^ 0) ≠ 0 := mul_ne_zero hc (pow_ne_zero 0 PowerSeries.X_ne_zero)
  have hP : (4 * PowerSeries.X ^ 3 : PowerSeries ℚ) + (6 * PowerSeries.X ^ 2 : PowerSeries ℚ) * G + (4 * PowerSeries.X + PowerSeries.X ^ 2 : PowerSeries ℚ) * G ^ 2 + (1 + 2 * PowerSeries.X : PowerSeries ℚ) * G ^ 3 + (1 : PowerSeries ℚ) * G ^ 4 = 0 :=
    (mul_eq_zero.mp ((mul_eq_zero.mp hM).resolve_left hLne)).resolve_left (pow_ne_zero 4 hN1)
  have h0c : PowerSeries.constantCoeff G = (-1 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A243642Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A243642Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A243642Aux.rel G hP h0c m
      push_cast
      linear_combination r
