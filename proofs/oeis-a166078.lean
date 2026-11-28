import OMAStatements.S_oeis_a166078

-- Problem: A166078: Expansion of (3(1-x)-sqrt(1+6x-7x^2))/(2(1-x)(1-2x)).
-- Upstream: formal-conjectures statements/oeis-a166078.lean:0 (declaration OMA.S_oeis_a166078.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A166078Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 + 6 * X - 7 * X ^ 2)
    (hG : G * (2 - 6 * X + 4 * X ^ 2 + (0) * S) = 3 - 3 * X + (-1) * S) :
    (-4 - 16 * X + 76 * X ^ 2 - 56 * X ^ 3) * derivative ℚ G + (24 + 16 * X - 56 * X ^ 2) * G = 24 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d7 : derivative ℚ (7 : ℚ⟦X⟧) = 0 := dnum 7
  have hS2 : S * S = (1 + 6 * X - 7 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (2 - 6 * X + 4 * X ^ 2) * G = (3 - 3 * X : ℚ⟦X⟧) + (-1) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 + 6 * X - 7 * (X * X) : ℚ⟦X⟧) = 6 - 14 * X := by
    simp [Derivation.leibniz, d6, d7]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = 6 - 14 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((2 - 6 * X + 4 * (X * X) : ℚ⟦X⟧) * G) = (-6 + 8 * X) * G + (2 - 6 * X + 4 * X ^ 2) * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d4, d6]
    ring
  have hR : derivative ℚ ((3 - 3 * X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * S) =
      -3 + (0) * S + (-1) * derivative ℚ S := by
    simp [Derivation.leibniz, d3]
  have hk2 : (2 - 6 * X + 4 * (X * X) : ℚ⟦X⟧) * G = (3 - 3 * X : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-6 + 8 * X) * G + (2 - 6 * X + 4 * X ^ 2) * derivative ℚ G =
      -3 + (0) * S + (-1) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 - X) * ((-4 - 16 * X + 76 * X ^ 2 - 56 * X ^ 3) * derivative ℚ G + (24 + 16 * X - 56 * X ^ 2) * G - (24)) = 0 := by
    linear_combination (-1) ^ 2 * S * hdS - 2 * (-1) ^ 2 * derivative ℚ S * hS -
      (2 * (0) * (1 + 6 * X - 7 * X ^ 2) + (-1) * (6 - 14 * X)) * hk + 2 * (-1) * (1 + 6 * X - 7 * X ^ 2) * hdk
  have hg : (1 - X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 + 6 * X - 7 * X ^ 2)
    (hG : G * (2 - 6 * X + 4 * X ^ 2 + (0) * S) = 3 - 3 * X + (-1) * S) :
    derivative ℚ G * C (-4) + derivative ℚ G * X * C (-16) +
      derivative ℚ G * X * X * C 76 + derivative ℚ G * X * X * X * C (-56) +
      G * C 24 + G * X * C 16 +
      G * X * X * C (-56) =
      C 24 := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 + 6 * X - 7 * X ^ 2)
    (hG : G * (2 - 6 * X + 4 * X ^ 2 + (0) * S) = 3 - 3 * X + (-1) * S) (m : ℕ) :
    (-4) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + (-16) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      76 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + (-56) * ((m : ℚ) + 1) * coeff (m + 1) G +
      24 * coeff (m + 1 + 1 + 1) G + 16 * coeff (m + 1 + 1) G +
      (-56) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 + 6 * X - 7 * X ^ 2)
    (hG : G * (2 - 6 * X + 4 * X ^ 2 + (0) * S) = 3 - 3 * X + (-1) * S) :
    (-12) * coeff (0 + 1 + 1 + 1) G + (-32) * coeff (0 + 1 + 1) G +
      76 * coeff (0 + 1) G + 24 * coeff (0 + 1 + 1) G +
      16 * coeff (0 + 1) G + (-56) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A166078Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a166078.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  have e3 : m + 1 + 1 + 1 - 3 = m := rfl
  rw [e1, e2, e3]
  cases m with
  | zero =>
    have r := A166078Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination ((-1 : ℚ) / 4) * r
  | succ m =>
    have r := A166078Aux.rel (S) G (by linear_combination hS)
        (by linear_combination hG) m
    push_cast
    linear_combination ((-1 : ℚ) / 4) * r
