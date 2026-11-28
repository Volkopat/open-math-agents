import OMAStatements.S_oeis_a154623

-- Problem: A154623: Expansion of 1+(x/(1-5*x))*c(x/(1-5*x)) where c(x) is the g.f. of A000108.
-- Upstream: formal-conjectures statements/oeis-a154623.lean:0 (declaration OMA.S_oeis_a154623.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A154623Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 14 * X + 45 * X ^ 2)
    (hG : G * (2 - 10 * X + (0) * S) = 3 - 15 * X + (-1) * S) :
    (-4 + 56 * X - 180 * X ^ 2) * derivative ℚ G + (-8) * G = -12 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d10 : derivative ℚ (10 : ℚ⟦X⟧) = 0 := dnum 10
  have d14 : derivative ℚ (14 : ℚ⟦X⟧) = 0 := dnum 14
  have d15 : derivative ℚ (15 : ℚ⟦X⟧) = 0 := dnum 15
  have d45 : derivative ℚ (45 : ℚ⟦X⟧) = 0 := dnum 45
  have hS2 : S * S = (1 - 14 * X + 45 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (2 - 10 * X) * G = (3 - 15 * X : ℚ⟦X⟧) + (-1) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 14 * X + 45 * (X * X) : ℚ⟦X⟧) = -14 + 90 * X := by
    simp [Derivation.leibniz, d14, d45]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -14 + 90 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((2 - 10 * X : ℚ⟦X⟧) * G) = (-10) * G + (2 - 10 * X) * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d10]
    ring
  have hR : derivative ℚ ((3 - 15 * X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * S) =
      -15 + (0) * S + (-1) * derivative ℚ S := by
    simp [Derivation.leibniz, d3, d15]
  have hk2 : (2 - 10 * X : ℚ⟦X⟧) * G = (3 - 15 * X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-10) * G + (2 - 10 * X) * derivative ℚ G =
      -15 + (0) * S + (-1) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 - 5 * X) * ((-4 + 56 * X - 180 * X ^ 2) * derivative ℚ G + (-8) * G - (-12)) = 0 := by
    linear_combination (-1) ^ 2 * S * hdS - 2 * (-1) ^ 2 * derivative ℚ S * hS -
      (2 * (0) * (1 - 14 * X + 45 * X ^ 2) + (-1) * (-14 + 90 * X)) * hk + 2 * (-1) * (1 - 14 * X + 45 * X ^ 2) * hdk
  have hg : (1 - 5 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 14 * X + 45 * X ^ 2)
    (hG : G * (2 - 10 * X + (0) * S) = 3 - 15 * X + (-1) * S) :
    derivative ℚ G * C (-4) + derivative ℚ G * X * C 56 +
      derivative ℚ G * X * X * C (-180) + G * C (-8) =
      C (-12) := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 14 * X + 45 * X ^ 2)
    (hG : G * (2 - 10 * X + (0) * S) = 3 - 15 * X + (-1) * S) (m : ℕ) :
    (-4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 56 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-180) * ((m : ℚ) + 1) * coeff (m + 1) G + (-8) * coeff (m + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 14 * X + 45 * X ^ 2)
    (hG : G * (2 - 10 * X + (0) * S) = 3 - 15 * X + (-1) * S) :
    (-8) * coeff (0 + 1 + 1) G + 56 * coeff (0 + 1) G +
      (-8) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A154623Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a154623.main := by
  intro T G hT _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  cases m with
  | zero =>
    have r := A154623Aux.relE0 ((1 - 5 * PowerSeries.X) * T) G (by linear_combination (1 - 5 * PowerSeries.X) * hT)
        (by linear_combination (1 - 5 * PowerSeries.X) * hG)
    push_cast
    linear_combination ((-1 : ℚ) / 4) * r
  | succ m =>
    have r := A154623Aux.rel ((1 - 5 * PowerSeries.X) * T) G (by linear_combination (1 - 5 * PowerSeries.X) * hT)
        (by linear_combination (1 - 5 * PowerSeries.X) * hG) m
    push_cast
    linear_combination ((-1 : ℚ) / 4) * r
