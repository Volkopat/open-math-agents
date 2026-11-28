import OMAStatements.S_oeis_a101478

-- Problem: A101478: G.f. satisfies A(x) = x*(1+A(x))^4/(1+A(x)^2).
-- Upstream: formal-conjectures statements/oeis-a101478.lean:0 (declaration OMA.S_oeis_a101478.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A101478Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (-X : ℚ⟦X⟧) + (1 - 4 * X : ℚ⟦X⟧) * G + (-6 * X : ℚ⟦X⟧) * G ^ 2 + (1 - 4 * X : ℚ⟦X⟧) * G ^ 3 + (-X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (X ^ 3 - 24 * X ^ 4 + 192 * X ^ 5 - 512 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (3 * X ^ 2 - 84 * X ^ 3 + 768 * X ^ 4 - 2304 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-24 * X ^ 2 + 396 * X ^ 3 - 1632 * X ^ 4) * derivative ℚ G + (12 * X ^ 2 - 48 * X ^ 3) * G =
      48 * X ^ 3 := by
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have hp0 : (-1 * X : ℚ⟦X⟧) + (1 - 4 * X : ℚ⟦X⟧) * G + (-6 * X : ℚ⟦X⟧) * G * G + (1 - 4 * X : ℚ⟦X⟧) * G * G * G + (-1 * X : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-1 * X : ℚ⟦X⟧) + (1 - 4 * X : ℚ⟦X⟧) * G + (-6 * X : ℚ⟦X⟧) * G * G + (1 - 4 * X : ℚ⟦X⟧) * G * G * G + (-1 * X : ℚ⟦X⟧) * G * G * G * G) =
      (-1 : ℚ⟦X⟧) + (1 - 4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G + (-12 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G ^ 2 + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G ^ 3 + (-4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-1 : ℚ⟦X⟧) * G ^ 4 := by
    simp [Derivation.leibniz, d4, d6]
    ring
  have hd1 : (-1 : ℚ⟦X⟧) + (1 - 4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G + (-12 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G ^ 2 + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G ^ 3 + (-4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-1 : ℚ⟦X⟧) * G ^ 4 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (-1 : ℚ⟦X⟧) + (1 - 4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G + (-12 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G * G + (3 - 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G * G * G + (-4 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (-1 : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((-1 : ℚ⟦X⟧) + (1 - 4 * X : ℚ⟦X⟧) * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G + (-12 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-6 : ℚ⟦X⟧) * G * G + (3 - 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-4 : ℚ⟦X⟧) * G * G * G + (-4 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (-1 : ℚ⟦X⟧) * G * G * G * G) =
      (1 - 4 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-8 : ℚ⟦X⟧) * (derivative ℚ G) + (-12 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-12 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (-4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (-8 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d3, d4, d6, d12]
    ring
  have hd2 : (1 - 4 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-8 : ℚ⟦X⟧) * (derivative ℚ G) + (-12 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-12 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (-4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (-8 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) = 0 := by rw [← hL2, hp1, map_zero]
  have hp2 : (1 - 4 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-8 : ℚ⟦X⟧) * (derivative ℚ G) + (-12 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (-12 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (3 - 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (-4 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) + (-8 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) = 0 := by linear_combination hd2
  have hL3 : derivative ℚ ((1 - 4 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-8 : ℚ⟦X⟧) * (derivative ℚ G) + (-12 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (-12 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G * (derivative ℚ G) + (6 - 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (3 - 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (-24 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (-12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (-4 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) + (-8 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G)) =
      (1 - 4 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-12 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-36 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-36 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (6 - 24 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (-12 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-36 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (18 - 72 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-72 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-36 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (-4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-12 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d3, d4, d6, d8, d12, d24]
    ring
  have hd3 : (1 - 4 * X : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-12 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-36 * X : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-36 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (6 - 24 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (-12 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-36 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (18 - 72 * X : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-72 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (-36 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (-4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-12 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) = 0 := by rw [← hL3, hp2, map_zero]
  have hfull : ((1 - 4 * X : ℚ⟦X⟧) + (-12 * X : ℚ⟦X⟧) * G + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 + (-4 * X : ℚ⟦X⟧) * G ^ 3) ^ 5 * ((X ^ 3 - 24 * X ^ 4 + 192 * X ^ 5 - 512 * X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (3 * X ^ 2 - 84 * X ^ 3 + 768 * X ^ 4 - 2304 * X ^ 5) * derivative ℚ (derivative ℚ G) + (-24 * X ^ 2 + 396 * X ^ 3 - 1632 * X ^ 4) * derivative ℚ G + (12 * X ^ 2 - 48 * X ^ 3) * G - (48 * X ^ 3)) = 0 := by
    linear_combination ((66 * X ^ 2 - 1152 * X ^ 3 + 6768 * X ^ 4 - 15744 * X ^ 5 + 18432 * X ^ 6 : ℚ⟦X⟧) + (144 * X ^ 2 - 4560 * X ^ 3 + 43200 * X ^ 4 - 164352 * X ^ 5 + 221184 * X ^ 6 : ℚ⟦X⟧) * G + (606 * X ^ 2 - 15168 * X ^ 3 + 165984 * X ^ 4 - 768768 * X ^ 5 + 1216512 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (960 * X ^ 2 - 37776 * X ^ 3 + 430272 * X ^ 4 - 2191872 * X ^ 5 + 4055040 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 + (2292 * X ^ 2 - 61440 * X ^ 3 + 798480 * X ^ 4 - 4389504 * X ^ 5 + 9123840 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 + (2016 * X ^ 2 - 95136 * X ^ 3 + 1164672 * X ^ 4 - 6693888 * X ^ 5 + 14598144 * X ^ 6 : ℚ⟦X⟧) * G ^ 5 + (4572 * X ^ 2 - 109440 * X ^ 3 + 1406784 * X ^ 4 - 8010240 * X ^ 5 + 17031168 * X ^ 6 : ℚ⟦X⟧) * G ^ 6 + (1728 * X ^ 2 - 108960 * X ^ 3 + 1381248 * X ^ 4 - 7394304 * X ^ 5 + 14598144 * X ^ 6 : ℚ⟦X⟧) * G ^ 7 + (4266 * X ^ 2 - 95616 * X ^ 3 + 1023888 * X ^ 4 - 5016192 * X ^ 5 + 9123840 * X ^ 6 : ℚ⟦X⟧) * G ^ 8 + (1296 * X ^ 2 - 47760 * X ^ 3 + 506304 * X ^ 4 - 2333184 * X ^ 5 + 4055040 * X ^ 6 : ℚ⟦X⟧) * G ^ 9 + (486 * X ^ 2 - 12096 * X ^ 3 + 136800 * X ^ 4 - 670464 * X ^ 5 + 1216512 * X ^ 6 : ℚ⟦X⟧) * G ^ 10 + (-720 * X ^ 3 + 13248 * X ^ 4 - 96768 * X ^ 5 + 221184 * X ^ 6 : ℚ⟦X⟧) * G ^ 11 + (240 * X ^ 4 - 3456 * X ^ 5 + 18432 * X ^ 6 : ℚ⟦X⟧) * G ^ 12) * hP +
      ((-18 * X ^ 3 + 192 * X ^ 4 + 912 * X ^ 5 - 14976 * X ^ 6 + 43008 * X ^ 7 - 49152 * X ^ 8 : ℚ⟦X⟧) + (66 * X ^ 3 - 2088 * X ^ 4 + 25488 * X ^ 5 - 149184 * X ^ 6 + 419328 * X ^ 7 - 479232 * X ^ 8 + 98304 * X ^ 9 : ℚ⟦X⟧) * (derivative ℚ G) + (-6 * X ^ 3 + 240 * X ^ 4 - 3600 * X ^ 5 + 23040 * X ^ 6 - 25344 * X ^ 7 - 423936 * X ^ 8 + 2015232 * X ^ 9 - 2752512 * X ^ 10 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (54 * X ^ 2 - 1200 * X ^ 3 + 9408 * X ^ 4 - 28224 * X ^ 5 - 16896 * X ^ 6 + 344064 * X ^ 7 - 589824 * X ^ 8 : ℚ⟦X⟧) * G + (-18 * X ^ 2 + 624 * X ^ 3 - 9912 * X ^ 4 + 98304 * X ^ 5 - 631488 * X ^ 6 + 2305536 * X ^ 7 - 3624960 * X ^ 8 + 1081344 * X ^ 9 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-192 * X ^ 4 + 6912 * X ^ 5 - 111744 * X ^ 6 + 1064448 * X ^ 7 - 6230016 * X ^ 8 + 20348928 * X ^ 9 - 27525120 * X ^ 10 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-72 * X ^ 2 + 210 * X ^ 3 + 15936 * X ^ 4 - 136800 * X ^ 5 + 148224 * X ^ 6 + 1314816 * X ^ 7 - 3244032 * X ^ 8 : ℚ⟦X⟧) * G ^ 2 + (756 * X ^ 3 - 25392 * X ^ 4 + 333168 * X ^ 5 - 2190144 * X ^ 6 + 7678464 * X ^ 7 - 13283328 * X ^ 8 + 5406720 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (54 * X ^ 3 - 2160 * X ^ 4 + 46656 * X ^ 5 - 663552 * X ^ 6 + 5992704 * X ^ 7 - 32348160 * X ^ 8 + 95993856 * X ^ 9 - 123863040 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (456 * X ^ 2 - 10080 * X ^ 3 + 86208 * X ^ 4 - 376896 * X ^ 5 + 529920 * X ^ 6 + 3440640 * X ^ 7 - 10813440 * X ^ 8 : ℚ⟦X⟧) * G ^ 3 + (-162 * X ^ 2 + 6096 * X ^ 3 - 98160 * X ^ 4 + 921216 * X ^ 5 - 5515584 * X ^ 6 + 19665408 * X ^ 7 - 33239040 * X ^ 8 + 16220160 * X ^ 9 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-4032 * X ^ 4 + 145152 * X ^ 5 - 2225664 * X ^ 6 + 18966528 * X ^ 7 - 95993856 * X ^ 8 + 272498688 * X ^ 9 - 330301440 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) ^ 2 + (-504 * X ^ 2 + 4332 * X ^ 3 + 54144 * X ^ 4 - 623376 * X ^ 5 + 838272 * X ^ 6 + 7280640 * X ^ 7 - 24330240 * X ^ 8 : ℚ⟦X⟧) * G ^ 4 + (3288 * X ^ 3 - 118656 * X ^ 4 + 1639968 * X ^ 5 - 11073408 * X ^ 6 + 38476800 * X ^ 7 - 64561152 * X ^ 8 + 32440320 * X ^ 9 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (486 * X ^ 3 - 19440 * X ^ 4 + 381600 * X ^ 5 - 4746240 * X ^ 6 + 38177280 * X ^ 7 - 187527168 * X ^ 8 + 505774080 * X ^ 9 - 578027520 * X ^ 10 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) ^ 2 + (1332 * X ^ 2 - 26688 * X ^ 3 + 196992 * X ^ 4 - 747648 * X ^ 5 + 605184 * X ^ 6 + 12681216 * X ^ 7 - 38928384 * X ^ 8 : ℚ⟦X⟧) * G ^ 5 + (-486 * X ^ 2 + 18864 * X ^ 3 - 308064 * X ^ 4 + 2861184 * X ^ 5 - 16652160 * X ^ 6 + 57928704 * X ^ 7 - 97198080 * X ^ 8 + 45416448 * X ^ 9 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-12096 * X ^ 4 + 435456 * X ^ 5 - 6531840 * X ^ 6 + 52835328 * X ^ 7 - 246177792 * X ^ 8 + 631701504 * X ^ 9 - 693633024 * X ^ 10 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) ^ 2 + (-1080 * X ^ 2 + 11844 * X ^ 3 + 51840 * X ^ 4 - 758592 * X ^ 5 - 308736 * X ^ 6 + 17031168 * X ^ 7 - 45416448 * X ^ 8 : ℚ⟦X⟧) * G ^ 6 + (5580 * X ^ 3 - 200400 * X ^ 4 + 2776416 * X ^ 5 - 18870912 * X ^ 6 + 65713152 * X ^ 7 - 107175936 * X ^ 8 + 45416448 * X ^ 9 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (810 * X ^ 3 - 32400 * X ^ 4 + 595008 * X ^ 5 - 6598656 * X ^ 6 + 47135232 * X ^ 7 - 210530304 * X ^ 8 + 530546688 * X ^ 9 - 578027520 * X ^ 10 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) ^ 2 + (1512 * X ^ 2 - 29856 * X ^ 3 + 201600 * X ^ 4 - 521856 * X ^ 5 - 1090560 * X ^ 6 + 16515072 * X ^ 7 - 38928384 * X ^ 8 : ℚ⟦X⟧) * G ^ 7 + (-486 * X ^ 2 + 18576 * X ^ 3 - 300048 * X ^ 4 + 2739072 * X ^ 5 - 15451776 * X ^ 6 + 51446784 * X ^ 7 - 81420288 * X ^ 8 + 32440320 * X ^ 9 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (-5184 * X ^ 4 + 186624 * X ^ 5 - 2815488 * X ^ 6 + 23095296 * X ^ 7 - 110149632 * X ^ 8 + 291373056 * X ^ 9 - 330301440 * X ^ 10 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) ^ 2 + (-648 * X ^ 2 + 7878 * X ^ 3 + 13248 * X ^ 4 - 297360 * X ^ 5 - 839040 * X ^ 6 + 10967040 * X ^ 7 - 24330240 * X ^ 8 : ℚ⟦X⟧) * G ^ 8 + (2214 * X ^ 3 - 77400 * X ^ 4 + 1049424 * X ^ 5 - 7022016 * X ^ 6 + 24288768 * X ^ 7 - 39751680 * X ^ 8 + 16220160 * X ^ 9 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (12528 * X ^ 5 - 400896 * X ^ 6 + 5052672 * X ^ 7 - 31463424 * X ^ 8 + 97763328 * X ^ 9 - 123863040 * X ^ 10 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) ^ 2 + (486 * X ^ 2 - 10512 * X ^ 3 + 82368 * X ^ 4 - 274752 * X ^ 5 - 96768 * X ^ 6 + 4669440 * X ^ 7 - 10813440 * X ^ 8 : ℚ⟦X⟧) * G ^ 9 + (-2664 * X ^ 4 + 89472 * X ^ 5 - 1071552 * X ^ 6 + 5506560 * X ^ 7 - 11046912 * X ^ 8 + 5406720 * X ^ 9 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (-13440 * X ^ 6 + 376320 * X ^ 7 - 3870720 * X ^ 8 + 17203200 * X ^ 9 - 27525120 * X ^ 10 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) ^ 2 + (-1206 * X ^ 3 + 24384 * X ^ 4 - 150624 * X ^ 5 + 172800 * X ^ 6 + 1118208 * X ^ 7 - 3244032 * X ^ 8 : ℚ⟦X⟧) * G ^ 10 + (48 * X ^ 5 - 15936 * X ^ 6 + 262656 * X ^ 7 - 1241088 * X ^ 8 + 1081344 * X ^ 9 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (5376 * X ^ 7 - 129024 * X ^ 8 + 1032192 * X ^ 9 - 2752512 * X ^ 10 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) ^ 2 + (960 * X ^ 4 - 16704 * X ^ 5 + 69120 * X ^ 6 + 98304 * X ^ 7 - 589824 * X ^ 8 : ℚ⟦X⟧) * G ^ 11 + (960 * X ^ 6 - 13824 * X ^ 7 + 36864 * X ^ 8 + 98304 * X ^ 9 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (-240 * X ^ 5 + 3456 * X ^ 6 - 6144 * X ^ 7 - 49152 * X ^ 8 : ℚ⟦X⟧) * G ^ 12) * hd1 +
      ((3 * X ^ 2 - 120 * X ^ 3 + 1968 * X ^ 4 - 17088 * X ^ 5 + 84480 * X ^ 6 - 236544 * X ^ 7 + 344064 * X ^ 8 - 196608 * X ^ 9 : ℚ⟦X⟧) + (36 * X ^ 4 - 1296 * X ^ 5 + 19008 * X ^ 6 - 145152 * X ^ 7 + 608256 * X ^ 8 - 1327104 * X ^ 9 + 1179648 * X ^ 10 : ℚ⟦X⟧) * (derivative ℚ G) + (-108 * X ^ 3 + 4032 * X ^ 4 - 59328 * X ^ 5 + 437760 * X ^ 6 - 1695744 * X ^ 7 + 3244032 * X ^ 8 - 2359296 * X ^ 9 : ℚ⟦X⟧) * G + (-18 * X ^ 3 + 720 * X ^ 4 - 13392 * X ^ 5 + 152064 * X ^ 6 - 1112832 * X ^ 7 + 5031936 * X ^ 8 - 12533760 * X ^ 9 + 12976128 * X ^ 10 : ℚ⟦X⟧) * G * (derivative ℚ G) + (36 * X ^ 2 - 1440 * X ^ 3 + 24912 * X ^ 4 - 251712 * X ^ 5 + 1635840 * X ^ 6 - 6653952 * X ^ 7 + 14745600 * X ^ 8 - 12976128 * X ^ 9 : ℚ⟦X⟧) * G ^ 2 + (1008 * X ^ 4 - 36288 * X ^ 5 + 547776 * X ^ 6 - 4499712 * X ^ 7 + 21510144 * X ^ 8 - 57065472 * X ^ 9 + 64880640 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (-1008 * X ^ 3 + 37632 * X ^ 4 - 558912 * X ^ 5 + 4293120 * X ^ 6 - 18481152 * X ^ 7 + 43548672 * X ^ 8 - 43253760 * X ^ 9 : ℚ⟦X⟧) * G ^ 3 + (-162 * X ^ 3 + 6480 * X ^ 4 - 126144 * X ^ 5 + 1548288 * X ^ 6 - 12324096 * X ^ 7 + 60438528 * X ^ 8 - 165003264 * X ^ 9 + 194641920 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (162 * X ^ 2 - 6480 * X ^ 3 + 114912 * X ^ 4 - 1233792 * X ^ 5 + 8709120 * X ^ 6 - 38458368 * X ^ 7 + 93339648 * X ^ 8 - 97320960 * X ^ 9 : ℚ⟦X⟧) * G ^ 4 + (5400 * X ^ 4 - 194400 * X ^ 5 + 2954880 * X ^ 6 - 24675840 * X ^ 7 + 121098240 * X ^ 8 - 331776000 * X ^ 9 + 389283840 * X ^ 10 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (-3240 * X ^ 3 + 120960 * X ^ 4 - 1800576 * X ^ 5 + 13962240 * X ^ 6 - 61489152 * X ^ 7 + 150405120 * X ^ 8 - 155713536 * X ^ 9 : ℚ⟦X⟧) * G ^ 5 + (-486 * X ^ 3 + 19440 * X ^ 4 - 377568 * X ^ 5 + 4617216 * X ^ 6 - 36564480 * X ^ 7 + 177721344 * X ^ 8 - 476872704 * X ^ 9 + 544997376 * X ^ 10 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (324 * X ^ 2 - 12960 * X ^ 3 + 229536 * X ^ 4 - 2457216 * X ^ 5 + 17280000 * X ^ 6 - 75902976 * X ^ 7 + 181665792 * X ^ 8 - 181665792 * X ^ 9 : ℚ⟦X⟧) * G ^ 6 + (9072 * X ^ 4 - 326592 * X ^ 5 + 4910976 * X ^ 6 - 39965184 * X ^ 7 + 188116992 * X ^ 8 - 489259008 * X ^ 9 + 544997376 * X ^ 10 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (-3888 * X ^ 3 + 145152 * X ^ 4 - 2153088 * X ^ 5 + 16450560 * X ^ 6 - 69894144 * X ^ 7 + 161021952 * X ^ 8 - 155713536 * X ^ 9 : ℚ⟦X⟧) * G ^ 7 + (-486 * X ^ 3 + 19440 * X ^ 4 - 361152 * X ^ 5 + 4091904 * X ^ 6 - 29956608 * X ^ 7 + 136802304 * X ^ 8 - 351240192 * X ^ 9 + 389283840 * X ^ 10 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (243 * X ^ 2 - 9720 * X ^ 3 + 168048 * X ^ 4 - 1695168 * X ^ 5 + 10990080 * X ^ 6 - 44762112 * X ^ 7 + 101302272 * X ^ 8 - 97320960 * X ^ 9 : ℚ⟦X⟧) * G ^ 8 + (2916 * X ^ 4 - 104976 * X ^ 5 + 1588032 * X ^ 6 - 13112064 * X ^ 7 + 63203328 * X ^ 8 - 169426944 * X ^ 9 + 194641920 * X ^ 10 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (-972 * X ^ 3 + 36288 * X ^ 4 - 539328 * X ^ 5 + 4154880 * X ^ 6 - 18014208 * X ^ 7 + 42958848 * X ^ 8 - 43253760 * X ^ 9 : ℚ⟦X⟧) * G ^ 9 + (-6480 * X ^ 5 + 207360 * X ^ 6 - 2615040 * X ^ 7 + 16312320 * X ^ 8 - 50872320 * X ^ 9 + 64880640 * X ^ 10 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (1296 * X ^ 4 - 46656 * X ^ 5 + 622080 * X ^ 6 - 3852288 * X ^ 7 + 11206656 * X ^ 8 - 12976128 * X ^ 9 : ℚ⟦X⟧) * G ^ 10 + (6336 * X ^ 6 - 177408 * X ^ 7 + 1824768 * X ^ 8 - 8110080 * X ^ 9 + 12976128 * X ^ 10 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (-576 * X ^ 5 + 23040 * X ^ 6 - 294912 * X ^ 7 + 1474560 * X ^ 8 - 2359296 * X ^ 9 : ℚ⟦X⟧) * G ^ 11 + (-2304 * X ^ 7 + 55296 * X ^ 8 - 442368 * X ^ 9 + 1179648 * X ^ 10 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (-3072 * X ^ 7 + 49152 * X ^ 8 - 196608 * X ^ 9 : ℚ⟦X⟧) * G ^ 12) * hd2 +
      ((X ^ 3 - 40 * X ^ 4 + 672 * X ^ 5 - 6144 * X ^ 6 + 33024 * X ^ 7 - 104448 * X ^ 8 + 180224 * X ^ 9 - 131072 * X ^ 10 : ℚ⟦X⟧) + (-48 * X ^ 4 + 1728 * X ^ 5 - 25344 * X ^ 6 + 193536 * X ^ 7 - 811008 * X ^ 8 + 1769472 * X ^ 9 - 1572864 * X ^ 10 : ℚ⟦X⟧) * G + (12 * X ^ 3 - 480 * X ^ 4 + 8928 * X ^ 5 - 101376 * X ^ 6 + 741888 * X ^ 7 - 3354624 * X ^ 8 + 8355840 * X ^ 9 - 8650752 * X ^ 10 : ℚ⟦X⟧) * G ^ 2 + (-448 * X ^ 4 + 16128 * X ^ 5 - 243456 * X ^ 6 + 1999872 * X ^ 7 - 9560064 * X ^ 8 + 25362432 * X ^ 9 - 28835840 * X ^ 10 : ℚ⟦X⟧) * G ^ 3 + (54 * X ^ 3 - 2160 * X ^ 4 + 42048 * X ^ 5 - 516096 * X ^ 6 + 4108032 * X ^ 7 - 20146176 * X ^ 8 + 55001088 * X ^ 9 - 64880640 * X ^ 10 : ℚ⟦X⟧) * G ^ 4 + (-1440 * X ^ 4 + 51840 * X ^ 5 - 787968 * X ^ 6 + 6580224 * X ^ 7 - 32292864 * X ^ 8 + 88473600 * X ^ 9 - 103809024 * X ^ 10 : ℚ⟦X⟧) * G ^ 5 + (108 * X ^ 3 - 4320 * X ^ 4 + 83904 * X ^ 5 - 1026048 * X ^ 6 + 8125440 * X ^ 7 - 39493632 * X ^ 8 + 105971712 * X ^ 9 - 121110528 * X ^ 10 : ℚ⟦X⟧) * G ^ 6 + (-1728 * X ^ 4 + 62208 * X ^ 5 - 935424 * X ^ 6 + 7612416 * X ^ 7 - 35831808 * X ^ 8 + 93192192 * X ^ 9 - 103809024 * X ^ 10 : ℚ⟦X⟧) * G ^ 7 + (81 * X ^ 3 - 3240 * X ^ 4 + 60192 * X ^ 5 - 681984 * X ^ 6 + 4992768 * X ^ 7 - 22800384 * X ^ 8 + 58540032 * X ^ 9 - 64880640 * X ^ 10 : ℚ⟦X⟧) * G ^ 8 + (-432 * X ^ 4 + 15552 * X ^ 5 - 235264 * X ^ 6 + 1942528 * X ^ 7 - 9363456 * X ^ 8 + 25100288 * X ^ 9 - 28835840 * X ^ 10 : ℚ⟦X⟧) * G ^ 9 + (864 * X ^ 5 - 27648 * X ^ 6 + 348672 * X ^ 7 - 2174976 * X ^ 8 + 6782976 * X ^ 9 - 8650752 * X ^ 10 : ℚ⟦X⟧) * G ^ 10 + (-768 * X ^ 6 + 21504 * X ^ 7 - 221184 * X ^ 8 + 983040 * X ^ 9 - 1572864 * X ^ 10 : ℚ⟦X⟧) * G ^ 11 + (256 * X ^ 7 - 6144 * X ^ 8 + 49152 * X ^ 9 - 131072 * X ^ 10 : ℚ⟦X⟧) * G ^ 12) * hd3
  have k3 : constantCoeff (3 : ℚ⟦X⟧) = 3 := cnum 3
  have hPG : (1 - 4 * X : ℚ⟦X⟧) + (-12 * X : ℚ⟦X⟧) * G + (3 - 12 * X : ℚ⟦X⟧) * G ^ 2 + (-4 * X : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k3] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 5 hPG)
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (-X : ℚ⟦X⟧) + (1 - 4 * X : ℚ⟦X⟧) * G + (-6 * X : ℚ⟦X⟧) * G ^ 2 + (1 - 4 * X : ℚ⟦X⟧) * G ^ 3 + (-X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 1 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-24) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C 192 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C (-512) +
      derivative ℚ (derivative ℚ G) * X * X * C 3 + derivative ℚ (derivative ℚ G) * X * X * X * C (-84) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 768 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-2304) +
      derivative ℚ G * X * X * C (-24) + derivative ℚ G * X * X * X * C 396 +
      derivative ℚ G * X * X * X * X * C (-1632) + G * X * X * C 12 +
      G * X * X * X * C (-48) =
      C 48 * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (-X : ℚ⟦X⟧) + (1 - 4 * X : ℚ⟦X⟧) * G + (-6 * X : ℚ⟦X⟧) * G ^ 2 + (1 - 4 * X : ℚ⟦X⟧) * G ^ 3 + (-X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    1 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-24) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      192 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G + (-512) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G +
      3 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-84) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      768 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-2304) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-24) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 396 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-1632) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 12 * coeff (m + 1 + 1 + 1 + 1) G +
      (-48) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (-X : ℚ⟦X⟧) + (1 - 4 * X : ℚ⟦X⟧) * G + (-6 * X : ℚ⟦X⟧) * G ^ 2 + (1 - 4 * X : ℚ⟦X⟧) * G ^ 3 + (-X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    24 * coeff (0 + 1 + 1 + 1 + 1) G + (-144) * coeff (0 + 1 + 1 + 1) G +
      36 * coeff (0 + 1 + 1 + 1 + 1) G + (-504) * coeff (0 + 1 + 1 + 1) G +
      1536 * coeff (0 + 1 + 1) G + (-72) * coeff (0 + 1 + 1 + 1) G +
      792 * coeff (0 + 1 + 1) G + (-1632) * coeff (0 + 1) G +
      12 * coeff (0 + 1 + 1) G + (-48) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (-X : ℚ⟦X⟧) + (1 - 4 * X : ℚ⟦X⟧) * G + (-6 * X : ℚ⟦X⟧) * G ^ 2 + (1 - 4 * X : ℚ⟦X⟧) * G ^ 3 + (-X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    60 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-576) * coeff (0 + 1 + 1 + 1 + 1) G +
      1152 * coeff (0 + 1 + 1 + 1) G + 60 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-1008) * coeff (0 + 1 + 1 + 1 + 1) G + 4608 * coeff (0 + 1 + 1 + 1) G +
      (-4608) * coeff (0 + 1 + 1) G + (-96) * coeff (0 + 1 + 1 + 1 + 1) G +
      1188 * coeff (0 + 1 + 1 + 1) G + (-3264) * coeff (0 + 1 + 1) G +
      12 * coeff (0 + 1 + 1 + 1) G + (-48) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A101478Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a101478.main := by
  intro G h0 hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  rw [e1, e2, e3]
  have hP : (-PowerSeries.X : PowerSeries ℚ) + (1 - 4 * PowerSeries.X : PowerSeries ℚ) * G + (-6 * PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (1 - 4 * PowerSeries.X : PowerSeries ℚ) * G ^ 3 + (-PowerSeries.X : PowerSeries ℚ) * G ^ 4 = 0 := by
    linear_combination hG
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A101478Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A101478Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A101478Aux.rel G hP h0c m
      push_cast
      linear_combination r
