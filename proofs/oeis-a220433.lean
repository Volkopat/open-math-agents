import OMAStatements.S_oeis_a220433

-- Problem: A220433: Expansion of e.g.f. for operads for alia algebras.
-- Upstream: formal-conjectures statements/oeis-a220433.lean:0 (declaration OMA.S_oeis_a220433.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A220433Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (-6 * X : ℚ⟦X⟧) + (6 : ℚ⟦X⟧) * G + (-6 : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    (4 * X ^ 2 - 12 * X ^ 3 - 9 * X ^ 4) * derivative ℚ (derivative ℚ G) + (-6 * X ^ 2 - 9 * X ^ 3) * derivative ℚ G + (X ^ 2) * G =
      2 * X ^ 2 := by
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have hp0 : (-6 * X : ℚ⟦X⟧) + (6 : ℚ⟦X⟧) * G + (-6 : ℚ⟦X⟧) * G * G + (1 : ℚ⟦X⟧) * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((-6 * X : ℚ⟦X⟧) + (6 : ℚ⟦X⟧) * G + (-6 : ℚ⟦X⟧) * G * G + (1 : ℚ⟦X⟧) * G * G * G) =
      (-6 : ℚ⟦X⟧) + (6 : ℚ⟦X⟧) * (derivative ℚ G) + (-12 : ℚ⟦X⟧) * G * (derivative ℚ G) + (3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d6]
    ring
  have hd1 : (-6 : ℚ⟦X⟧) + (6 : ℚ⟦X⟧) * (derivative ℚ G) + (-12 : ℚ⟦X⟧) * G * (derivative ℚ G) + (3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (-6 : ℚ⟦X⟧) + (6 : ℚ⟦X⟧) * (derivative ℚ G) + (-12 : ℚ⟦X⟧) * G * (derivative ℚ G) + (3 : ℚ⟦X⟧) * G * G * (derivative ℚ G) = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((-6 : ℚ⟦X⟧) + (6 : ℚ⟦X⟧) * (derivative ℚ G) + (-12 : ℚ⟦X⟧) * G * (derivative ℚ G) + (3 : ℚ⟦X⟧) * G * G * (derivative ℚ G)) =
      (6 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-12 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-12 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (6 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d3, d6, d12]
    ring
  have hd2 : (6 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (-12 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-12 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (6 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (3 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) = 0 := by rw [← hL2, hp1, map_zero]
  have hfull : ((6 : ℚ⟦X⟧) + (-12 : ℚ⟦X⟧) * G + (3 : ℚ⟦X⟧) * G ^ 2) ^ 3 * ((4 * X ^ 2 - 12 * X ^ 3 - 9 * X ^ 4) * derivative ℚ (derivative ℚ G) + (-6 * X ^ 2 - 9 * X ^ 3) * derivative ℚ G + (X ^ 2) * G - (2 * X ^ 2)) = 0 := by
    linear_combination ((1188 * X ^ 2 + 648 * X ^ 3 : ℚ⟦X⟧) + (-1080 * X ^ 2 - 324 * X ^ 3 : ℚ⟦X⟧) * G + (648 * X ^ 2 : ℚ⟦X⟧) * G ^ 2 + (-216 * X ^ 2 : ℚ⟦X⟧) * G ^ 3 + (27 * X ^ 2 : ℚ⟦X⟧) * G ^ 4) * hP +
      ((72 * X ^ 2 - 1188 * X ^ 3 - 648 * X ^ 4 : ℚ⟦X⟧) + (288 * X ^ 2 - 864 * X ^ 3 - 648 * X ^ 4 : ℚ⟦X⟧) * (derivative ℚ G) + (720 * X ^ 2 + 1728 * X ^ 3 + 324 * X ^ 4 : ℚ⟦X⟧) * G + (-720 * X ^ 2 + 2160 * X ^ 3 + 1620 * X ^ 4 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-1080 * X ^ 2 - 1620 * X ^ 3 : ℚ⟦X⟧) * G ^ 2 + (432 * X ^ 2 - 1296 * X ^ 3 - 972 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (432 * X ^ 2 + 648 * X ^ 3 : ℚ⟦X⟧) * G ^ 3 + (-72 * X ^ 2 + 216 * X ^ 3 + 162 * X ^ 4 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-54 * X ^ 2 - 81 * X ^ 3 : ℚ⟦X⟧) * G ^ 4) * hd1 +
      ((144 * X ^ 2 - 432 * X ^ 3 - 324 * X ^ 4 : ℚ⟦X⟧) + (-576 * X ^ 2 + 1728 * X ^ 3 + 1296 * X ^ 4 : ℚ⟦X⟧) * G + (720 * X ^ 2 - 2160 * X ^ 3 - 1620 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 + (-288 * X ^ 2 + 864 * X ^ 3 + 648 * X ^ 4 : ℚ⟦X⟧) * G ^ 3 + (36 * X ^ 2 - 108 * X ^ 3 - 81 * X ^ 4 : ℚ⟦X⟧) * G ^ 4) * hd2
  have k3 : constantCoeff (3 : ℚ⟦X⟧) = 3 := cnum 3
  have k6 : constantCoeff (6 : ℚ⟦X⟧) = 6 := cnum 6
  have k12 : constantCoeff (12 : ℚ⟦X⟧) = 12 := cnum 12
  have hPG : (6 : ℚ⟦X⟧) + (-12 : ℚ⟦X⟧) * G + (3 : ℚ⟦X⟧) * G ^ 2 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k3, k6, k12] at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 3 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (-6 * X : ℚ⟦X⟧) + (6 : ℚ⟦X⟧) * G + (-6 : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    derivative ℚ (derivative ℚ G) * X * X * C 4 + derivative ℚ (derivative ℚ G) * X * X * X * C (-12) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-9) + derivative ℚ G * X * X * C (-6) +
      derivative ℚ G * X * X * X * C (-9) + G * X * X * C 1 =
      C 2 * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (-6 * X : ℚ⟦X⟧) + (6 : ℚ⟦X⟧) * G + (-6 : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) (m : ℕ) :
    4 * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + (-12) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G +
      (-9) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G + (-6) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      (-9) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + 1 * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (-6 * X : ℚ⟦X⟧) + (6 : ℚ⟦X⟧) * G + (-6 : ℚ⟦X⟧) * G ^ 2 + (1 : ℚ⟦X⟧) * G ^ 3 = 0)
    (h0 : constantCoeff G = (0 : ℚ)) :
    24 * coeff (0 + 1 + 1 + 1) G + (-24) * coeff (0 + 1 + 1) G +
      (-12) * coeff (0 + 1 + 1) G + (-9) * coeff (0 + 1) G +
      1 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A220433Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a220433.main := by
  intro G h0 hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  rw [e1, e2]
  have hP : (-6 * PowerSeries.X : PowerSeries ℚ) + (6 : PowerSeries ℚ) * G + (-6 : PowerSeries ℚ) * G ^ 2 + (1 : PowerSeries ℚ) * G ^ 3 = 0 := by
    linear_combination -hG
  have h0c : PowerSeries.constantCoeff G = (0 : ℚ) := by
    simpa using h0
  unfold OMA.S_oeis_a220433.a
  cases m with
  | zero =>
    have r := A220433Aux.relE0 G hP h0c
    simp only [Nat.factorial_succ, Nat.factorial_zero]
    push_cast
    linear_combination (1 : ℚ) * r
  | succ m =>
    have r := A220433Aux.rel G hP h0c m
    simp only [Nat.factorial_succ]
    push_cast
    linear_combination (((m : ℚ) + 1) * ((m : ℚ) + 2) * (m.factorial : ℚ)) * r
