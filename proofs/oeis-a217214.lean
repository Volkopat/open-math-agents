import OMAStatements.S_oeis_a217214

-- Problem: A217214: G.f.: (P-Q*(sqrt(1-4*x)))/(x*(1-4*x)^3) where P=(1-4*x)^3*(1-x-x^2), Q=1-11*x+39*x^2-40*x^3-22*x^4.
-- Upstream: formal-conjectures statements/oeis-a217214.lean:0 (declaration OMA.S_oeis_a217214.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
A polynomial combination of this equation and its derivative, divided by a common polynomial
factor, is a second order equation f2 G'' + f1 G' + f0 G = rho with polynomial f2, f1, f0, rho;
the recurrence is the coefficient of a power of x in it, beyond the degree of rho. -/

namespace A217214Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (X - 12 * X ^ 2 + 48 * X ^ 3 - 64 * X ^ 4 + (0) * S) = 1 - 13 * X + 59 * X ^ 2 - 100 * X ^ 3 + 16 * X ^ 4 + 64 * X ^ 5 + (-1 + 11 * X - 39 * X ^ 2 + 40 * X ^ 3 + 22 * X ^ 4) * S) :
    (-2 * X + 30 * X ^ 2 - 166 * X ^ 3 + 392 * X ^ 4 - 276 * X ^ 5 - 176 * X ^ 6) * derivative ℚ G + (-2 + 28 * X - 142 * X ^ 2 + 308 * X ^ 3 - 292 * X ^ 4 + 88 * X ^ 5) * G = -16 * X ^ 3 - 144 * X ^ 4 + 480 * X ^ 5 + 88 * X ^ 6 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d11 : derivative ℚ (11 : ℚ⟦X⟧) = 0 := dnum 11
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d13 : derivative ℚ (13 : ℚ⟦X⟧) = 0 := dnum 13
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d22 : derivative ℚ (22 : ℚ⟦X⟧) = 0 := dnum 22
  have d39 : derivative ℚ (39 : ℚ⟦X⟧) = 0 := dnum 39
  have d40 : derivative ℚ (40 : ℚ⟦X⟧) = 0 := dnum 40
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d59 : derivative ℚ (59 : ℚ⟦X⟧) = 0 := dnum 59
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d100 : derivative ℚ (100 : ℚ⟦X⟧) = 0 := dnum 100
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (X - 12 * X ^ 2 + 48 * X ^ 3 - 64 * X ^ 4) * G = (1 - 13 * X + 59 * X ^ 2 - 100 * X ^ 3 + 16 * X ^ 4 + 64 * X ^ 5 : ℚ⟦X⟧) + (-1 + 11 * X - 39 * X ^ 2 + 40 * X ^ 3 + 22 * X ^ 4) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((1 * X - 12 * (X * X) + 48 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * G) = (1 - 24 * X + 144 * X ^ 2 - 256 * X ^ 3) * G + (X - 12 * X ^ 2 + 48 * X ^ 3 - 64 * X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d12, d48, d64]
    ring
  have hR : derivative ℚ ((1 - 13 * X + 59 * (X * X) - 100 * (X * X * X) + 16 * (X * X * X * X) + 64 * (X * X * X * X * X) : ℚ⟦X⟧) + (-1 + 11 * X - 39 * (X * X) + 40 * (X * X * X) + 22 * (X * X * X * X) : ℚ⟦X⟧) * S) =
      -13 + 118 * X - 300 * X ^ 2 + 64 * X ^ 3 + 320 * X ^ 4 + (11 - 78 * X + 120 * X ^ 2 + 88 * X ^ 3) * S + (-1 + 11 * X - 39 * X ^ 2 + 40 * X ^ 3 + 22 * X ^ 4) * derivative ℚ S := by
    simp [Derivation.leibniz, d11, d13, d16, d22, d39, d40, d59, d64, d100]
    ring
  have hk2 : (1 * X - 12 * (X * X) + 48 * (X * X * X) - 64 * (X * X * X * X) : ℚ⟦X⟧) * G = (1 - 13 * X + 59 * (X * X) - 100 * (X * X * X) + 16 * (X * X * X * X) + 64 * (X * X * X * X * X) : ℚ⟦X⟧) + (-1 + 11 * X - 39 * (X * X) + 40 * (X * X * X) + 22 * (X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (1 - 24 * X + 144 * X ^ 2 - 256 * X ^ 3) * G + (X - 12 * X ^ 2 + 48 * X ^ 3 - 64 * X ^ 4) * derivative ℚ G =
      -13 + 118 * X - 300 * X ^ 2 + 64 * X ^ 3 + 320 * X ^ 4 + (11 - 78 * X + 120 * X ^ 2 + 88 * X ^ 3) * S + (-1 + 11 * X - 39 * X ^ 2 + 40 * X ^ 3 + 22 * X ^ 4) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 - 12 * X + 48 * X ^ 2 - 64 * X ^ 3) * ((-2 * X + 30 * X ^ 2 - 166 * X ^ 3 + 392 * X ^ 4 - 276 * X ^ 5 - 176 * X ^ 6) * derivative ℚ G + (-2 + 28 * X - 142 * X ^ 2 + 308 * X ^ 3 - 292 * X ^ 4 + 88 * X ^ 5) * G - (-16 * X ^ 3 - 144 * X ^ 4 + 480 * X ^ 5 + 88 * X ^ 6)) = 0 := by
    linear_combination (-1 + 11 * X - 39 * X ^ 2 + 40 * X ^ 3 + 22 * X ^ 4) ^ 2 * S * hdS - 2 * (-1 + 11 * X - 39 * X ^ 2 + 40 * X ^ 3 + 22 * X ^ 4) ^ 2 * derivative ℚ S * hS -
      (2 * (11 - 78 * X + 120 * X ^ 2 + 88 * X ^ 3) * (1 - 4 * X) + (-1 + 11 * X - 39 * X ^ 2 + 40 * X ^ 3 + 22 * X ^ 4) * (-4)) * hk + 2 * (-1 + 11 * X - 39 * X ^ 2 + 40 * X ^ 3 + 22 * X ^ 4) * (1 - 4 * X) * hdk
  have hg : (1 - 12 * X + 48 * X ^ 2 - 64 * X ^ 3 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem key2 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (X - 12 * X ^ 2 + 48 * X ^ 3 - 64 * X ^ 4 + (0) * S) = 1 - 13 * X + 59 * X ^ 2 - 100 * X ^ 3 + 16 * X ^ 4 + 64 * X ^ 5 + (-1 + 11 * X - 39 * X ^ 2 + 40 * X ^ 3 + 22 * X ^ 4) * S) :
    (-423 * X ^ 2 - 423 * X ^ 3 + 17801 * X ^ 4 - 37364 * X ^ 5) * derivative ℚ (derivative ℚ G) + (872 * X + 3510 * X ^ 2 + 4478 * X ^ 3 - 47462 * X ^ 4) * derivative ℚ G + (1718 + 6074 * X - 22460 * X ^ 2 + 14390 * X ^ 3) * G =
      3592 * X ^ 3 + 33072 * X ^ 4 := by
  have h := key S G hS hG
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d28 : derivative ℚ (28 : ℚ⟦X⟧) = 0 := dnum 28
  have d30 : derivative ℚ (30 : ℚ⟦X⟧) = 0 := dnum 30
  have d88 : derivative ℚ (88 : ℚ⟦X⟧) = 0 := dnum 88
  have d142 : derivative ℚ (142 : ℚ⟦X⟧) = 0 := dnum 142
  have d144 : derivative ℚ (144 : ℚ⟦X⟧) = 0 := dnum 144
  have d166 : derivative ℚ (166 : ℚ⟦X⟧) = 0 := dnum 166
  have d176 : derivative ℚ (176 : ℚ⟦X⟧) = 0 := dnum 176
  have d276 : derivative ℚ (276 : ℚ⟦X⟧) = 0 := dnum 276
  have d292 : derivative ℚ (292 : ℚ⟦X⟧) = 0 := dnum 292
  have d308 : derivative ℚ (308 : ℚ⟦X⟧) = 0 := dnum 308
  have d392 : derivative ℚ (392 : ℚ⟦X⟧) = 0 := dnum 392
  have d480 : derivative ℚ (480 : ℚ⟦X⟧) = 0 := dnum 480
  have hL : derivative ℚ ((-2 * X + 30 * (X * X) - 166 * (X * X * X) + 392 * (X * X * X * X) - 276 * (X * X * X * X * X) - 176 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-2 + 28 * X - 142 * (X * X) + 308 * (X * X * X) - 292 * (X * X * X * X) + 88 * (X * X * X * X * X) : ℚ⟦X⟧) * G) =
      (-2 + 60 * X - 498 * X ^ 2 + 1568 * X ^ 3 - 1380 * X ^ 4 - 1056 * X ^ 5) * derivative ℚ G + (-2 * X + 30 * X ^ 2 - 166 * X ^ 3 + 392 * X ^ 4 - 276 * X ^ 5 - 176 * X ^ 6) * derivative ℚ (derivative ℚ G) + (28 - 284 * X + 924 * X ^ 2 - 1168 * X ^ 3 + 440 * X ^ 4) * G + (-2 + 28 * X - 142 * X ^ 2 + 308 * X ^ 3 - 292 * X ^ 4 + 88 * X ^ 5) * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d28, d30, d88, d142, d166, d176, d276, d292, d308, d392]
    ring
  have hRd : derivative ℚ (-16 * (X * X * X) - 144 * (X * X * X * X) + 480 * (X * X * X * X * X) + 88 * (X * X * X * X * X * X) : ℚ⟦X⟧) = -48 * X ^ 2 - 576 * X ^ 3 + 2400 * X ^ 4 + 528 * X ^ 5 := by
    simp [Derivation.leibniz, d16, d88, d144, d480]
    ring
  have h2 : (-2 * X + 30 * (X * X) - 166 * (X * X * X) + 392 * (X * X * X * X) - 276 * (X * X * X * X * X) - 176 * (X * X * X * X * X * X) : ℚ⟦X⟧) * derivative ℚ G + (-2 + 28 * X - 142 * (X * X) + 308 * (X * X * X) - 292 * (X * X * X * X) + 88 * (X * X * X * X * X) : ℚ⟦X⟧) * G = (-16 * (X * X * X) - 144 * (X * X * X * X) + 480 * (X * X * X * X * X) + 88 * (X * X * X * X * X * X) : ℚ⟦X⟧) := by linear_combination h
  have hd : (-2 + 60 * X - 498 * X ^ 2 + 1568 * X ^ 3 - 1380 * X ^ 4 - 1056 * X ^ 5) * derivative ℚ G + (-2 * X + 30 * X ^ 2 - 166 * X ^ 3 + 392 * X ^ 4 - 276 * X ^ 5 - 176 * X ^ 6) * derivative ℚ (derivative ℚ G) + (28 - 284 * X + 924 * X ^ 2 - 1168 * X ^ 3 + 440 * X ^ 4) * G + (-2 + 28 * X - 142 * X ^ 2 + 308 * X ^ 3 - 292 * X ^ 4 + 88 * X ^ 5) * derivative ℚ G = -48 * X ^ 2 - 576 * X ^ 3 + 2400 * X ^ 4 + 528 * X ^ 5 := by
    rw [← hL, h2, hRd]
  have hfull : (2 - 22 * X + 78 * X ^ 2 - 80 * X ^ 3 - 44 * X ^ 4) * ((-423 * X ^ 2 - 423 * X ^ 3 + 17801 * X ^ 4 - 37364 * X ^ 5) * derivative ℚ (derivative ℚ G) + (872 * X + 3510 * X ^ 2 + 4478 * X ^ 3 - 47462 * X ^ 4) * derivative ℚ G + (1718 + 6074 * X - 22460 * X ^ 2 + 14390 * X ^ 3) * G - (3592 * X ^ 3 + 33072 * X ^ 4)) = 0 := by
    linear_combination (423 * X + 2115 * X ^ 2 - 9341 * X ^ 3) * hd + (-1718 - 5306 * X + 39510 * X ^ 2) * h
  have hg : (2 - 22 * X + 78 * X ^ 2 - 80 * X ^ 3 - 44 * X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    have kc : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
    simp [kc] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (X - 12 * X ^ 2 + 48 * X ^ 3 - 64 * X ^ 4 + (0) * S) = 1 - 13 * X + 59 * X ^ 2 - 100 * X ^ 3 + 16 * X ^ 4 + 64 * X ^ 5 + (-1 + 11 * X - 39 * X ^ 2 + 40 * X ^ 3 + 22 * X ^ 4) * S) :
    derivative ℚ (derivative ℚ G) * X * X * C (-423) + derivative ℚ (derivative ℚ G) * X * X * X * C (-423) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 17801 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-37364) +
      derivative ℚ G * X * C 872 + derivative ℚ G * X * X * C 3510 +
      derivative ℚ G * X * X * X * C 4478 + derivative ℚ G * X * X * X * X * C (-47462) +
      G * C 1718 + G * X * C 6074 +
      G * X * X * C (-22460) + G * X * X * X * C 14390 =
      C 3592 * X * X * X + C 33072 * X * X * X * X := by
  have h := key2 S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (X - 12 * X ^ 2 + 48 * X ^ 3 - 64 * X ^ 4 + (0) * S) = 1 - 13 * X + 59 * X ^ 2 - 100 * X ^ 3 + 16 * X ^ 4 + 64 * X ^ 5 + (-1 + 11 * X - 39 * X ^ 2 + 40 * X ^ 3 + 22 * X ^ 4) * S) (m : ℕ) :
    (-423) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-423) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      17801 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + (-37364) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      872 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 3510 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      4478 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-47462) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      1718 * coeff (m + 1 + 1 + 1 + 1 + 1) G + 6074 * coeff (m + 1 + 1 + 1 + 1) G +
      (-22460) * coeff (m + 1 + 1 + 1) G + 14390 * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

end A217214Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a217214.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  rw [e1, e2, e3]
  have r := A217214Aux.rel (S) G (by linear_combination hS)
      (by linear_combination hG) m
  push_cast
  linear_combination r
