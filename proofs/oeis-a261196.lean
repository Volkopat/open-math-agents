import OMAStatements.S_oeis_a261196

-- Problem: A261196: Expansion of sqrt(8*x + sqrt(1 + 64*x^2)).
-- Upstream: formal-conjectures statements/oeis-a261196.lean:0 (declaration OMA.S_oeis_a261196.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A261196Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (-16 * X : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    (X ^ 2 + X ^ 3 + 64 * X ^ 4 + 64 * X ^ 5) * derivative ℚ (derivative ℚ G) + (64 * X ^ 3 + 64 * X ^ 4) * derivative ℚ G + (-16 * X ^ 2 - 16 * X ^ 3) * G =
      0 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have hp0 : (-1 : ℚ⟦X⟧) + (-16 * X : ℚ⟦X⟧) * G * G + (1 : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-1 : ℚ⟦X⟧) + (-16 * X : ℚ⟦X⟧) * G * G + (1 : ℚ⟦X⟧) * G * G * G * G) =
      (-32 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-16 : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d16]
    ring
  have hd1 : (-32 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-16 : ℚ⟦X⟧) * G ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (-32 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-16 : ℚ⟦X⟧) * G * G + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((-32 * X : ℚ⟦X⟧) * G * (derivative ℚ G) + (-16 : ℚ⟦X⟧) * G * G + (4 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G)) =
      (-32 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-32 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-64 : ℚ⟦X⟧) * G * (derivative ℚ G) + (12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d4, d16, d32]
    ring
  have hd2 : (-32 * X : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-32 * X : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-64 : ℚ⟦X⟧) * G * (derivative ℚ G) + (12 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((-32 * X : ℚ⟦X⟧) * G + (4 : ℚ⟦X⟧) * G ^ 3) ^ 3 * ((X ^ 2 + X ^ 3 + 64 * X ^ 4 + 64 * X ^ 5) * derivative ℚ (derivative ℚ G) + (64 * X ^ 3 + 64 * X ^ 4) * derivative ℚ G + (-16 * X ^ 2 - 16 * X ^ 3) * G - (0)) = 0 := by
    linear_combination ((24576 * X ^ 3 + 24576 * X ^ 4 : ℚ⟦X⟧) * G ^ 4 + (-1024 * X ^ 2 - 1024 * X ^ 3 : ℚ⟦X⟧) * G ^ 6) * hP +
      ((-1024 * X ^ 4 - 1024 * X ^ 5 - 65536 * X ^ 6 - 65536 * X ^ 7 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-1536 * X ^ 3 - 1536 * X ^ 4 - 32768 * X ^ 5 - 32768 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (512 * X ^ 3 + 512 * X ^ 4 + 32768 * X ^ 5 + 32768 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (64 * X ^ 2 + 64 * X ^ 3 - 12288 * X ^ 4 - 12288 * X ^ 5 : ℚ⟦X⟧) * G ^ 4 + (-48 * X ^ 2 - 48 * X ^ 3 - 3072 * X ^ 4 - 3072 * X ^ 5 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (1024 * X ^ 3 + 1024 * X ^ 4 : ℚ⟦X⟧) * G ^ 6) * hd1 +
      ((1024 * X ^ 4 + 1024 * X ^ 5 + 65536 * X ^ 6 + 65536 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 + (-256 * X ^ 3 - 256 * X ^ 4 - 16384 * X ^ 5 - 16384 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 + (16 * X ^ 2 + 16 * X ^ 3 + 1024 * X ^ 4 + 1024 * X ^ 5 : ℚ⟦X⟧) * G ^ 6) * hd2
  have k4 : constantCoeff (4 : ℚ⟦X⟧) = 4 := cnum 4
  have hPG : (-32 * X : ℚ⟦X⟧) * G + (4 : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k4] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (-16 * X : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C 1 + derivative ℚ (derivative ℚ G) * X * X * X * C 1 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 64 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 64 +
      derivative ℚ G * X * X * X * C 64 + derivative ℚ G * X * X * X * X * C 64 +
      G * X * X * C (-16) + G * X * X * X * C (-16) =
      0 := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (-16 * X : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) (m : ℕ) :
    1 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 1 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      64 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + 64 * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      64 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 64 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-16) * coeff (m + 1 + 1 + 1) G + (-16) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (-16 * X : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    6 * coeff (0 + 1 + 1 + 1) G + 2 * coeff (0 + 1 + 1) G +
      64 * coeff (0 + 1) G + (-16) * coeff (0 + 1) G +
      (-16) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (-1 : ℚ⟦X⟧) + (-16 * X : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    12 * coeff (0 + 1 + 1 + 1 + 1) G + 6 * coeff (0 + 1 + 1 + 1) G +
      128 * coeff (0 + 1 + 1) G + 128 * coeff (0 + 1 + 1) G +
      64 * coeff (0 + 1) G + (-16) * coeff (0 + 1 + 1) G +
      (-16) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A261196Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a261196.main := by
  intro T G hT _ hG h0 n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  have e3 : m + 1 + 1 + 1 - 3 = m := rfl
  rw [e1, e2, e3]
  have hP : (-1 : PowerSeries ℚ) + (-16 * PowerSeries.X : PowerSeries ℚ) * G ^ 2 + (1 : PowerSeries ℚ) * G ^ 4 = 0 := by
    linear_combination (G ^ 2 - 8 * PowerSeries.X + T) * hG + hT
  have h0c : PowerSeries.constantCoeff G = (1 : ℚ) := by
    simpa using h0
  cases m with
  | zero =>
    have r := A261196Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A261196Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      have r := A261196Aux.rel G hP h0c m
      push_cast
      linear_combination r
