import OMAStatements.S_oeis_a025577

-- Problem: A025577: Expansion of (x/(1-x))*sqrt((1+x)/(1-3*x)).
-- Upstream: formal-conjectures statements/oeis-a025577.lean:0 (declaration OMA.S_oeis_a025577.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A025577Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (1 - 4 * X + 3 * X ^ 2 + (0) * S) = 0 + (X) * S) :
    (2 * X - 6 * X ^ 2 - 2 * X ^ 3 + 6 * X ^ 4) * derivative ℚ G + (-2 + 10 * X ^ 2) * G = 0 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have hS2 : S * S = (1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (1 - 4 * X + 3 * X ^ 2) * G = (0 : ℚ⟦X⟧) + (X) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) = -2 - 6 * X := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -2 - 6 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((1 - 4 * X + 3 * (X * X) : ℚ⟦X⟧) * G) = (-4 + 6 * X) * G + (1 - 4 * X + 3 * X ^ 2) * derivative ℚ G := by
    simp [Derivation.leibniz, d3, d4]
    ring
  have hR : derivative ℚ ((0 : ℚ⟦X⟧) + (1 * X : ℚ⟦X⟧) * S) =
      0 + (1) * S + (X) * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hk2 : (1 - 4 * X + 3 * (X * X) : ℚ⟦X⟧) * G = (0 : ℚ⟦X⟧) + (1 * X : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-4 + 6 * X) * G + (1 - 4 * X + 3 * X ^ 2) * derivative ℚ G =
      0 + (1) * S + (X) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 - 3 * X) * ((2 * X - 6 * X ^ 2 - 2 * X ^ 3 + 6 * X ^ 4) * derivative ℚ G + (-2 + 10 * X ^ 2) * G - (0)) = 0 := by
    linear_combination (X) ^ 2 * S * hdS - 2 * (X) ^ 2 * derivative ℚ S * hS -
      (2 * (1) * (1 - 2 * X - 3 * X ^ 2) + (X) * (-2 - 6 * X)) * hk + 2 * (X) * (1 - 2 * X - 3 * X ^ 2) * hdk
  have hg : (1 - 3 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (1 - 4 * X + 3 * X ^ 2 + (0) * S) = 0 + (X) * S) :
    derivative ℚ G * X * C 2 + derivative ℚ G * X * X * C (-6) +
      derivative ℚ G * X * X * X * C (-2) + derivative ℚ G * X * X * X * X * C 6 +
      G * C (-2) + G * X * X * C 10 =
      0 := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (1 - 4 * X + 3 * X ^ 2 + (0) * S) = 0 + (X) * S) (m : ℕ) :
    2 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + (-6) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      (-2) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + 6 * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-2) * coeff (m + 1 + 1 + 1 + 1) G + 10 * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (1 - 4 * X + 3 * X ^ 2 + (0) * S) = 0 + (X) * S) :
    6 * coeff (0 + 1 + 1 + 1) G + (-12) * coeff (0 + 1 + 1) G +
      (-2) * coeff (0 + 1) G + (-2) * coeff (0 + 1 + 1 + 1) G +
      10 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A025577Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a025577.main := by
  intro T G hT _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  have e3 : m + 1 + 1 + 1 - 3 = m := rfl
  rw [e1, e2, e3]
  cases m with
  | zero =>
    have r := A025577Aux.relE0 ((1 - 3 * PowerSeries.X) * T) G (by linear_combination (1 - 3 * PowerSeries.X) * hT)
        (by linear_combination (1 - 3 * PowerSeries.X) * hG)
    push_cast
    linear_combination ((-1 : ℚ) / 2) * r
  | succ m =>
    have r := A025577Aux.rel ((1 - 3 * PowerSeries.X) * T) G (by linear_combination (1 - 3 * PowerSeries.X) * hT)
        (by linear_combination (1 - 3 * PowerSeries.X) * hG) m
    push_cast
    linear_combination ((-1 : ℚ) / 2) * r
