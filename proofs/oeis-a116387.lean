import OMAStatements.S_oeis_a116387

-- Problem: A116387: Expansion of 1/(sqrt(1-2*x-3*x^2)*(2-M(x))), where M(x) is the g.f. of the Motzkin numbers A001006.
-- Upstream: formal-conjectures statements/oeis-a116387.lean:0 (declaration OMA.S_oeis_a116387.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A116387Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (1 - 2 * X - 3 * X ^ 2 + (-1 + X + 4 * X ^ 2) * S) = 2 * X ^ 2 + (0) * S) :
    (16 - 80 * X - 48 * X ^ 2 + 528 * X ^ 3 + 160 * X ^ 4 - 1088 * X ^ 5 - 768 * X ^ 6) * derivative ℚ G + (-32 + 32 * X + 224 * X ^ 2 + 224 * X ^ 3 - 640 * X ^ 4 - 768 * X ^ 5) * G = 32 * X - 96 * X ^ 2 - 96 * X ^ 3 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d56 : derivative ℚ (56 : ℚ⟦X⟧) = 0 := dnum 56
  have hS2 : S * S = (1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (4 * X ^ 2 - 16 * X ^ 3 - 12 * X ^ 4 + 56 * X ^ 5 + 48 * X ^ 6) * G = (2 * X ^ 2 - 4 * X ^ 3 - 6 * X ^ 4 : ℚ⟦X⟧) + (2 * X ^ 2 - 2 * X ^ 3 - 8 * X ^ 4) * S := by
    linear_combination (1 - 2 * X - 3 * X ^ 2 - (-1 + X + 4 * X ^ 2) * S) * hG + (-1 + X + 4 * X ^ 2) * ((-1 + X + 4 * X ^ 2) * G - (0)) * hS
  have hPd : derivative ℚ (1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) = -2 - 6 * X := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -2 - 6 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((4 * (X * X) - 16 * (X * X * X) - 12 * (X * X * X * X) + 56 * (X * X * X * X * X) + 48 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (8 * X - 48 * X ^ 2 - 48 * X ^ 3 + 280 * X ^ 4 + 288 * X ^ 5) * G + (4 * X ^ 2 - 16 * X ^ 3 - 12 * X ^ 4 + 56 * X ^ 5 + 48 * X ^ 6) * derivative ℚ G := by
    simp [Derivation.leibniz, d4, d12, d16, d48, d56]
    ring
  have hR : derivative ℚ ((2 * (X * X) - 4 * (X * X * X) - 6 * (X * X * X * X) : ℚ⟦X⟧) + (2 * (X * X) - 2 * (X * X * X) - 8 * (X * X * X * X) : ℚ⟦X⟧) * S) =
      4 * X - 12 * X ^ 2 - 24 * X ^ 3 + (4 * X - 6 * X ^ 2 - 32 * X ^ 3) * S + (2 * X ^ 2 - 2 * X ^ 3 - 8 * X ^ 4) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d4, d6, d8]
    ring
  have hk2 : (4 * (X * X) - 16 * (X * X * X) - 12 * (X * X * X * X) + 56 * (X * X * X * X * X) + 48 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G = (2 * (X * X) - 4 * (X * X * X) - 6 * (X * X * X * X) : ℚ⟦X⟧) + (2 * (X * X) - 2 * (X * X * X) - 8 * (X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (8 * X - 48 * X ^ 2 - 48 * X ^ 3 + 280 * X ^ 4 + 288 * X ^ 5) * G + (4 * X ^ 2 - 16 * X ^ 3 - 12 * X ^ 4 + 56 * X ^ 5 + 48 * X ^ 6) * derivative ℚ G =
      4 * X - 12 * X ^ 2 - 24 * X ^ 3 + (4 * X - 6 * X ^ 2 - 32 * X ^ 3) * S + (2 * X ^ 2 - 2 * X ^ 3 - 8 * X ^ 4) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 4 * ((1 - 2 * X - 3 * X ^ 2) * ((16 - 80 * X - 48 * X ^ 2 + 528 * X ^ 3 + 160 * X ^ 4 - 1088 * X ^ 5 - 768 * X ^ 6) * derivative ℚ G + (-32 + 32 * X + 224 * X ^ 2 + 224 * X ^ 3 - 640 * X ^ 4 - 768 * X ^ 5) * G - (32 * X - 96 * X ^ 2 - 96 * X ^ 3))) = 0 := by
    linear_combination (2 * X ^ 2 - 2 * X ^ 3 - 8 * X ^ 4) ^ 2 * S * hdS - 2 * (2 * X ^ 2 - 2 * X ^ 3 - 8 * X ^ 4) ^ 2 * derivative ℚ S * hS -
      (2 * (4 * X - 6 * X ^ 2 - 32 * X ^ 3) * (1 - 2 * X - 3 * X ^ 2) + (2 * X ^ 2 - 2 * X ^ 3 - 8 * X ^ 4) * (-2 - 6 * X)) * hk + 2 * (2 * X ^ 2 - 2 * X ^ 3 - 8 * X ^ 4) * (1 - 2 * X - 3 * X ^ 2) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 4 ≠ 0 := pow_ne_zero 4 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 2 * X - 3 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (1 - 2 * X - 3 * X ^ 2 + (-1 + X + 4 * X ^ 2) * S) = 2 * X ^ 2 + (0) * S) :
    (17 * X ^ 2 + 17 * X ^ 3 - 391 * X ^ 4 - 17 * X ^ 5 + 1394 * X ^ 6 + 1020 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-125 * X + 146 * X ^ 2 + 533 * X ^ 3 - 722 * X ^ 4 + 2928 * X ^ 5 + 4320 * X ^ 6) * derivative ℚ G + (250 * X + 504 * X ^ 2 - 70 * X ^ 3 + 2280 * X ^ 5) * G =
      -216 * X ^ 2 + 30 * X ^ 3 := by
  have h := key S G hS hG
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d80 : derivative ℚ (80 : ℚ⟦X⟧) = 0 := dnum 80
  have d96 : derivative ℚ (96 : ℚ⟦X⟧) = 0 := dnum 96
  have d160 : derivative ℚ (160 : ℚ⟦X⟧) = 0 := dnum 160
  have d224 : derivative ℚ (224 : ℚ⟦X⟧) = 0 := dnum 224
  have d528 : derivative ℚ (528 : ℚ⟦X⟧) = 0 := dnum 528
  have d640 : derivative ℚ (640 : ℚ⟦X⟧) = 0 := dnum 640
  have d768 : derivative ℚ (768 : ℚ⟦X⟧) = 0 := dnum 768
  have d1088 : derivative ℚ (1088 : ℚ⟦X⟧) = 0 := dnum 1088
  have hL : derivative ℚ ((16 - 80 * X - 48 * (X * X) + 528 * (X * X * X) + 160 * (X * X * X * X) - 1088 * (X * X * X * X * X) - 768 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-32 + 32 * X + 224 * (X * X) + 224 * (X * X * X) - 640 * (X * X * X * X) - 768 * (X * X * X * X * X) : ℚ⟦X⟧) * G) =
      (-80 - 96 * X + 1584 * X ^ 2 + 640 * X ^ 3 - 5440 * X ^ 4 - 4608 * X ^ 5) * derivative ℚ G + (16 - 80 * X - 48 * X ^ 2 + 528 * X ^ 3 + 160 * X ^ 4 - 1088 * X ^ 5 - 768 * X ^ 6) * derivative ℚ (derivative ℚ G) + (32 + 448 * X + 672 * X ^ 2 - 2560 * X ^ 3 - 3840 * X ^ 4) * G + (-32 + 32 * X + 224 * X ^ 2 + 224 * X ^ 3 - 640 * X ^ 4 - 768 * X ^ 5) * derivative ℚ G := by
    simp [Derivation.leibniz, d16, d32, d48, d80, d160, d224, d528, d640, d768, d1088]
    ring
  have hRd : derivative ℚ (32 * X - 96 * (X * X) - 96 * (X * X * X) : ℚ⟦X⟧) = 32 - 192 * X - 288 * X ^ 2 := by
    simp [Derivation.leibniz, d32, d96]
    ring
  have h2 : (16 - 80 * X - 48 * (X * X) + 528 * (X * X * X) + 160 * (X * X * X * X) - 1088 * (X * X * X * X * X) - 768 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-32 + 32 * X + 224 * (X * X) + 224 * (X * X * X) - 640 * (X * X * X * X) - 768 * (X * X * X * X * X) : ℚ⟦X⟧) * G = (32 * X - 96 * (X * X) - 96 * (X * X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (-80 - 96 * X + 1584 * X ^ 2 + 640 * X ^ 3 - 5440 * X ^ 4 - 4608 * X ^ 5) * derivative ℚ G + (16 - 80 * X - 48 * X ^ 2 + 528 * X ^ 3 + 160 * X ^ 4 - 1088 * X ^ 5 - 768 * X ^ 6) * derivative ℚ (derivative ℚ G) + (32 + 448 * X + 672 * X ^ 2 - 2560 * X ^ 3 - 3840 * X ^ 4) * G + (-32 + 32 * X + 224 * X ^ 2 + 224 * X ^ 3 - 640 * X ^ 4 - 768 * X ^ 5) * derivative ℚ G = 32 - 192 * X - 288 * X ^ 2 := by
    rw [← hL, h2, hRd]
  have hfull : (16 - 16 * X - 64 * X ^ 2) * ((17 * X ^ 2 + 17 * X ^ 3 - 391 * X ^ 4 - 17 * X ^ 5 + 1394 * X ^ 6 + 1020 * X ^ 7) * derivative ℚ (derivative ℚ G) + (-125 * X + 146 * X ^ 2 + 533 * X ^ 3 - 722 * X ^ 4 + 2928 * X ^ 5 + 4320 * X ^ 6) * derivative ℚ G + (250 * X + 504 * X ^ 2 - 70 * X ^ 3 + 2280 * X ^ 5) * G - (-216 * X ^ 2 + 30 * X ^ 3)) = 0 := by
    linear_combination (17 * X ^ 2 + 85 * X ^ 3) * hd + (-125 * X - 235 * X ^ 2) * h
  have hg : (16 - 16 * X - 64 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (16 : ℚ⟦X⟧) = 16 := cnum 16
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (1 - 2 * X - 3 * X ^ 2 + (-1 + X + 4 * X ^ 2) * S) = 2 * X ^ 2 + (0) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C 17 + derivative ℚ (derivative ℚ G) * X * X * X * C 17 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-391) + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-17) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 1394 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C 1020 +
      derivative ℚ G * X * C (-125) + derivative ℚ G * X * X * C 146 +
      derivative ℚ G * X * X * X * C 533 + derivative ℚ G * X * X * X * X * C (-722) +
      derivative ℚ G * X * X * X * X * X * C 2928 + derivative ℚ G * X * X * X * X * X * X * C 4320 +
      G * X * C 250 + G * X * X * C 504 +
      G * X * X * X * C (-70) + G * X * X * X * X * X * C 2280 =
      C (-216) * X * X + C 30 * X * X * X := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (1 - 2 * X - 3 * X ^ 2 + (-1 + X + 4 * X ^ 2) * S) = 2 * X ^ 2 + (0) * S) (m : ℕ) :
    17 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 17 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-391) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-17) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      1394 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + 1020 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      (-125) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 146 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      533 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-722) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      2928 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 4320 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      250 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 504 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-70) * coeff (m + 1 + 1 + 1 + 1) G + 2280 * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (1 - 2 * X - 3 * X ^ 2 + (-1 + X + 4 * X ^ 2) * S) = 2 * X ^ 2 + (0) * S) :
    340 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 204 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-2346) * coeff (0 + 1 + 1 + 1) G + (-34) * coeff (0 + 1 + 1) G +
      (-625) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 584 * coeff (0 + 1 + 1 + 1 + 1) G +
      1599 * coeff (0 + 1 + 1 + 1) G + (-1444) * coeff (0 + 1 + 1) G +
      2928 * coeff (0 + 1) G + 250 * coeff (0 + 1 + 1 + 1 + 1) G +
      504 * coeff (0 + 1 + 1 + 1) G + (-70) * coeff (0 + 1 + 1) G +
      2280 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (1 - 2 * X - 3 * X ^ 2 + (-1 + X + 4 * X ^ 2) * S) = 2 * X ^ 2 + (0) * S) :
    510 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 340 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-4692) * coeff (0 + 1 + 1 + 1 + 1) G + (-102) * coeff (0 + 1 + 1 + 1) G +
      2788 * coeff (0 + 1 + 1) G + (-750) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      730 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 2132 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-2166) * coeff (0 + 1 + 1 + 1) G + 5856 * coeff (0 + 1 + 1) G +
      4320 * coeff (0 + 1) G + 250 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      504 * coeff (0 + 1 + 1 + 1 + 1) G + (-70) * coeff (0 + 1 + 1 + 1) G +
      2280 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A116387Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a116387.main := by
  intro S M G hS _ hM hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 - 5 = m := rfl
  rw [e1, e2, e3, e4, e5]
  cases m with
  | zero =>
    have r := A116387Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination 2 * PowerSeries.X ^ 2 * hG + G * S * hM - G * hS)
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A116387Aux.relE1 (S) G (by linear_combination hS)
          (by linear_combination 2 * PowerSeries.X ^ 2 * hG + G * S * hM - G * hS)
      push_cast
      linear_combination r
    | succ m =>
      have r := A116387Aux.rel (S) G (by linear_combination hS)
          (by linear_combination 2 * PowerSeries.X ^ 2 * hG + G * S * hM - G * hS) m
      push_cast
      linear_combination r
