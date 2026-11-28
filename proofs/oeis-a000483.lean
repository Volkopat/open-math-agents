import OMAStatements.S_oeis_a000483

-- Problem: A000483: Associated Stirling numbers: second-order reciprocal Stirling numbers (Fekete) a(n) = [[n, 3]]. The number of 3-orbit permutations of an n-set with at least 2 elements in each orbit.
-- Upstream: formal-conjectures statements/oeis-a000483.lean:0 (declaration OMA.S_oeis_a000483.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Put U = x + L, so that (1 - x) DU = -x and 6 F + U^3 = 0, where D is the derivative.
Differentiating the second relation three times and eliminating DU with the first one expresses
(1-x) DF, (1-x)^2 D^2 F and (1-x)^3 D^3 F as polynomials in x and U; a linear combination of these is
the differential equation x^3 (1-x)^3 D^3 F - 3 x^2 (1-x)^2 D^2 F + x (1-x) (3-2x) DF = x^6. The
recurrence for the coefficients of F is the coefficient of a power of x in this equation, and
multiplying by factorials gives the recurrence for a(n) = n! [x^n] F. -/

namespace A000483Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G U : ℚ⟦X⟧)
    (hU : (1 - X) * derivative ℚ U = -X)
    (hG : 6 * G + U ^ 3 = 0) :
    (X ^ 3 - 3 * X ^ 4 + 3 * X ^ 5 - X ^ 6) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-3 * X ^ 2 + 6 * X ^ 3 - 3 * X ^ 4) * derivative ℚ (derivative ℚ G) + (3 * X - 5 * X ^ 2 + 2 * X ^ 3) * derivative ℚ G =
      X ^ 6 := by
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have hL1 : derivative ℚ (6 * G + U * U * U) =
      6 * derivative ℚ G + 3 * U ^ 2 * derivative ℚ U := by
    simp [Derivation.leibniz, d6]
    ring
  have hGp : 6 * G + U * U * U = 0 := by linear_combination hG
  have hE1 : 6 * derivative ℚ G + 3 * U ^ 2 * derivative ℚ U = 0 := by
    rw [← hL1, hGp, map_zero]
  have A1 : 6 * ((1 - X) * derivative ℚ G) = 3 * X * (U * U) := by
    linear_combination (1 - X) * hE1 - 3 * U ^ 2 * hU
  have hL2 : derivative ℚ (6 * ((1 - X) * derivative ℚ G)) =
      6 * (1 - X) * derivative ℚ (derivative ℚ G) - 6 * derivative ℚ G := by
    simp [Derivation.leibniz, d6]
    ring
  have hR2 : derivative ℚ (3 * X * (U * U)) = 3 * U ^ 2 + 6 * X * U * derivative ℚ U := by
    simp [Derivation.leibniz, d3]
    ring
  have hD2 : 6 * (1 - X) * derivative ℚ (derivative ℚ G) - 6 * derivative ℚ G =
      3 * U ^ 2 + 6 * X * U * derivative ℚ U := by
    rw [← hL2, ← hR2, A1]
  have A2 : 6 * ((1 - X) * (1 - X) * derivative ℚ (derivative ℚ G)) - 6 * ((1 - X) * derivative ℚ G) =
      3 * ((1 - X) * (U * U)) - 6 * (X * X * U) := by
    linear_combination (1 - X) * hD2 + 6 * X * U * hU
  have hL3 : derivative ℚ (6 * ((1 - X) * (1 - X) * derivative ℚ (derivative ℚ G)) -
      6 * ((1 - X) * derivative ℚ G)) =
      6 * (1 - X) ^ 2 * derivative ℚ (derivative ℚ (derivative ℚ G)) -
        18 * (1 - X) * derivative ℚ (derivative ℚ G) + 6 * derivative ℚ G := by
    simp [Derivation.leibniz, d6]
    ring
  have hR3 : derivative ℚ (3 * ((1 - X) * (U * U)) - 6 * (X * X * U)) =
      -3 * U ^ 2 + 6 * (1 - X) * U * derivative ℚ U - 12 * X * U - 6 * X ^ 2 * derivative ℚ U := by
    simp [Derivation.leibniz, d3, d6]
    ring
  have hD3 : 6 * (1 - X) ^ 2 * derivative ℚ (derivative ℚ (derivative ℚ G)) -
        18 * (1 - X) * derivative ℚ (derivative ℚ G) + 6 * derivative ℚ G =
      -3 * U ^ 2 + 6 * (1 - X) * U * derivative ℚ U - 12 * X * U - 6 * X ^ 2 * derivative ℚ U := by
    rw [← hL3, ← hR3, A2]
  have A3 : 6 * (1 - X) ^ 3 * derivative ℚ (derivative ℚ (derivative ℚ G)) -
      18 * (1 - X) ^ 2 * derivative ℚ (derivative ℚ G) + 6 * (1 - X) * derivative ℚ G +
      3 * (1 - X) * U ^ 2 + 18 * X * (1 - X) * U - 6 * X ^ 3 = 0 := by
    linear_combination (1 - X) * hD3 + (6 * (1 - X) * U - 6 * X ^ 2) * hU
  have hc : (6 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    rw [cnum, map_zero] at h'
    norm_num at h'
  have hfull : (6 : ℚ⟦X⟧) * ((X ^ 3 - 3 * X ^ 4 + 3 * X ^ 5 - X ^ 6) *
      derivative ℚ (derivative ℚ (derivative ℚ G)) +
      (-3 * X ^ 2 + 6 * X ^ 3 - 3 * X ^ 4) * derivative ℚ (derivative ℚ G) +
      (3 * X - 5 * X ^ 2 + 2 * X ^ 3) * derivative ℚ G - X ^ 6) = 0 := by
    linear_combination X ^ 3 * A3 - 3 * X ^ 2 * (1 - X) * A2 + X * (1 - X) * (3 - 2 * X) * A1
  have h := (mul_eq_zero.mp hfull).resolve_left hc
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G U : ℚ⟦X⟧)
    (hU : (1 - X) * derivative ℚ U = -X)
    (hG : 6 * G + U ^ 3 = 0) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 1 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-3) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C 3 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C (-1) +
      derivative ℚ (derivative ℚ G) * X * X * C (-3) + derivative ℚ (derivative ℚ G) * X * X * X * C 6 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C (-3) + derivative ℚ G * X * C 3 +
      derivative ℚ G * X * X * C (-5) + derivative ℚ G * X * X * X * C 2 =
      C 1 * X * X * X * X * X * X := by
  have h := key G U hU hG
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G U : ℚ⟦X⟧)
    (hU : (1 - X) * derivative ℚ U = -X)
    (hG : 6 * G + U ^ 3 = 0) (m : ℕ) :
    1 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-3) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      3 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-1) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-3) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 6 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-3) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 3 * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-5) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 2 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G U hU hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h


set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem gen : ∀ U G : ℚ⟦X⟧, (1 - X) * derivative ℚ U = -X →
    6 * G + U ^ 3 = 0 →
    ∀ n : ℕ, 7 ≤ n →
      (8 * (n : ℚ) - 6 * (n : ℚ) ^ 2 + (n : ℚ) ^ 3) * coeff n G + (35 - 56 * (n : ℚ) + 24 * (n : ℚ) ^ 2 - 3 * (n : ℚ) ^ 3) * coeff (n - 1) G +
        (-94 + 95 * (n : ℚ) - 30 * (n : ℚ) ^ 2 + 3 * (n : ℚ) ^ 3) * coeff (n - 2) G + (60 - 47 * (n : ℚ) + 12 * (n : ℚ) ^ 2 - (n : ℚ) ^ 3) * coeff (n - 3) G = 0 := by
  intro U G hU hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 7, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 := rfl
  rw [e1, e2, e3]
  have r := A000483Aux.rel G U hU hG m
  push_cast
  linear_combination r

end A000483Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a000483.main := by
  intro L F _ hL hF n hn
  have hd : PowerSeries.derivative ℚ (PowerSeries.X + L) = 1 + PowerSeries.derivative ℚ L := by
    simp
  have hU : (1 - PowerSeries.X) * PowerSeries.derivative ℚ (PowerSeries.X + L) = -PowerSeries.X := by
    rw [hd]
    linear_combination hL
  have hG : 6 * F + (PowerSeries.X + L) ^ 3 = 0 := by linear_combination hF
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 7, by omega⟩
  have key := A000483Aux.gen (PowerSeries.X + L) F hU hG (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) (by omega)
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 := rfl
  rw [e1, e2, e3] at key ⊢
  unfold OMA.S_oeis_a000483.a
  simp only [Nat.factorial_succ]
  push_cast at key ⊢
  linear_combination ((m : ℚ) + 6) * ((m : ℚ) + 5) * (((m : ℚ) + 4) * ((m : ℚ) + 3) *
    ((m : ℚ) + 2) * ((m : ℚ) + 1) * (m.factorial : ℚ)) * key
