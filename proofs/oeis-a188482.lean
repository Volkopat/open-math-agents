import OMAStatements.S_oeis_a188482

-- Problem: A188482: Diagonal sums of the Riordan matrix (1/(1-4x),(1-sqrt(1-4x))/(2*sqrt(1-4x))) (A188481).
-- Upstream: formal-conjectures statements/oeis-a188482.lean:0 (declaration OMA.S_oeis_a188482.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A188482Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (2 - 14 * X + 16 * X ^ 2 + 30 * X ^ 3 + 8 * X ^ 4 + (0) * S) = 2 - 7 * X - 4 * X ^ 2 + (X) * S) :
    (4 * X - 28 * X ^ 2 + 32 * X ^ 3 + 60 * X ^ 4 + 16 * X ^ 5) * derivative ℚ G + (-4 + 8 * X + 8 * X ^ 2 + 88 * X ^ 3 + 40 * X ^ 4) * G = -4 + 8 * X - 4 * X ^ 2 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d7 : derivative ℚ (7 : ℚ⟦X⟧) = 0 := dnum 7
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d14 : derivative ℚ (14 : ℚ⟦X⟧) = 0 := dnum 14
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d30 : derivative ℚ (30 : ℚ⟦X⟧) = 0 := dnum 30
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (2 - 14 * X + 16 * X ^ 2 + 30 * X ^ 3 + 8 * X ^ 4) * G = (2 - 7 * X - 4 * X ^ 2 : ℚ⟦X⟧) + (X) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((2 - 14 * X + 16 * (X * X) + 30 * (X * X * X) + 8 * (X * X * X * X) : ℚ⟦X⟧) * G) = (-14 + 32 * X + 90 * X ^ 2 + 32 * X ^ 3) * G + (2 - 14 * X + 16 * X ^ 2 + 30 * X ^ 3 + 8 * X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d8, d14, d16, d30]
    ring
  have hR : derivative ℚ ((2 - 7 * X - 4 * (X * X) : ℚ⟦X⟧) + (1 * X : ℚ⟦X⟧) * S) =
      -7 - 8 * X + (1) * S + (X) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d4, d7]
    ring
  have hk2 : (2 - 14 * X + 16 * (X * X) + 30 * (X * X * X) + 8 * (X * X * X * X) : ℚ⟦X⟧) * G = (2 - 7 * X - 4 * (X * X) : ℚ⟦X⟧) + (1 * X : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-14 + 32 * X + 90 * X ^ 2 + 32 * X ^ 3) * G + (2 - 14 * X + 16 * X ^ 2 + 30 * X ^ 3 + 8 * X ^ 4) * derivative ℚ G =
      -7 - 8 * X + (1) * S + (X) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 - 4 * X) * ((4 * X - 28 * X ^ 2 + 32 * X ^ 3 + 60 * X ^ 4 + 16 * X ^ 5) * derivative ℚ G + (-4 + 8 * X + 8 * X ^ 2 + 88 * X ^ 3 + 40 * X ^ 4) * G - (-4 + 8 * X - 4 * X ^ 2)) = 0 := by
    linear_combination (X) ^ 2 * S * hdS - 2 * (X) ^ 2 * derivative ℚ S * hS -
      (2 * (1) * (1 - 4 * X) + (X) * (-4)) * hk + 2 * (X) * (1 - 4 * X) * hdk
  have hg : (1 - 4 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (2 - 14 * X + 16 * X ^ 2 + 30 * X ^ 3 + 8 * X ^ 4 + (0) * S) = 2 - 7 * X - 4 * X ^ 2 + (X) * S) :
    derivative ℚ G * X * C 4 + derivative ℚ G * X * X * C (-28) +
      derivative ℚ G * X * X * X * C 32 + derivative ℚ G * X * X * X * X * C 60 +
      derivative ℚ G * X * X * X * X * X * C 16 + G * C (-4) +
      G * X * C 8 + G * X * X * C 8 +
      G * X * X * X * C 88 + G * X * X * X * X * C 40 =
      C (-4) + C 8 * X +
      C (-4) * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (2 - 14 * X + 16 * X ^ 2 + 30 * X ^ 3 + 8 * X ^ 4 + (0) * S) = 2 - 7 * X - 4 * X ^ 2 + (X) * S) (m : ℕ) :
    4 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-28) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      32 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 60 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      16 * ((m : ℚ) + 1) * coeff (m + 1) G + (-4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      8 * coeff (m + 1 + 1 + 1 + 1) G + 8 * coeff (m + 1 + 1 + 1) G +
      88 * coeff (m + 1 + 1) G + 40 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (2 - 14 * X + 16 * X ^ 2 + 30 * X ^ 3 + 8 * X ^ 4 + (0) * S) = 2 - 7 * X - 4 * X ^ 2 + (X) * S) :
    16 * coeff (0 + 1 + 1 + 1 + 1) G + (-84) * coeff (0 + 1 + 1 + 1) G +
      64 * coeff (0 + 1 + 1) G + 60 * coeff (0 + 1) G +
      (-4) * coeff (0 + 1 + 1 + 1 + 1) G + 8 * coeff (0 + 1 + 1 + 1) G +
      8 * coeff (0 + 1 + 1) G + 88 * coeff (0 + 1) G +
      40 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A188482Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a188482.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  cases m with
  | zero =>
    have r := A188482Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination ((-1 : ℚ) / 4) * r
  | succ m =>
    have r := A188482Aux.rel (S) G (by linear_combination hS)
        (by linear_combination hG) m
    push_cast
    linear_combination ((-1 : ℚ) / 4) * r
