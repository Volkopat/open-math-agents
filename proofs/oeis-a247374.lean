import OMAStatements.S_oeis_a247374

-- Problem: A247374: Number of button presses required to try every combination of a binary combination lock with n number buttons.
-- Upstream: formal-conjectures statements/oeis-a247374.lean:0 (declaration OMA.S_oeis_a247374.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A247374Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (2 * X - 6 * X ^ 2 - 4 * X ^ 3 + 24 * X ^ 4 - 16 * X ^ 5 + (0) * S) = X + X ^ 2 - 4 * X ^ 3 - 4 * X ^ 4 + (X - X ^ 2) * S) :
    (4 - 16 * X + 4 * X ^ 2 + 56 * X ^ 3 - 80 * X ^ 4 + 32 * X ^ 5) * derivative ℚ G + (-8 + 88 * X ^ 2 - 144 * X ^ 3 + 64 * X ^ 4) * G = 4 - 8 * X - 16 * X ^ 2 + 8 * X ^ 3 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have hS2 : S * S = (1 - 4 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (2 * X - 6 * X ^ 2 - 4 * X ^ 3 + 24 * X ^ 4 - 16 * X ^ 5) * G = (X + X ^ 2 - 4 * X ^ 3 - 4 * X ^ 4 : ℚ⟦X⟧) + (X - X ^ 2) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 4 * (X * X) : ℚ⟦X⟧) = -8 * X := by
    simp [Derivation.leibniz, d4]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -8 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((2 * X - 6 * (X * X) - 4 * (X * X * X) + 24 * (X * X * X * X) - 16 * (X * X * X * X * X) : ℚ⟦X⟧) * G) = (2 - 12 * X - 12 * X ^ 2 + 96 * X ^ 3 - 80 * X ^ 4) * G + (2 * X - 6 * X ^ 2 - 4 * X ^ 3 + 24 * X ^ 4 - 16 * X ^ 5) * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d4, d6, d16, d24]
    ring
  have hR : derivative ℚ ((1 * X + 1 * (X * X) - 4 * (X * X * X) - 4 * (X * X * X * X) : ℚ⟦X⟧) + (1 * X - 1 * (X * X) : ℚ⟦X⟧) * S) =
      1 + 2 * X - 12 * X ^ 2 - 16 * X ^ 3 + (1 - 2 * X) * S + (X - X ^ 2) * derivative ℚ S := by
    simp [Derivation.leibniz, d4]
    ring
  have hk2 : (2 * X - 6 * (X * X) - 4 * (X * X * X) + 24 * (X * X * X * X) - 16 * (X * X * X * X * X) : ℚ⟦X⟧) * G = (1 * X + 1 * (X * X) - 4 * (X * X * X) - 4 * (X * X * X * X) : ℚ⟦X⟧) + (1 * X - 1 * (X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (2 - 12 * X - 12 * X ^ 2 + 96 * X ^ 3 - 80 * X ^ 4) * G + (2 * X - 6 * X ^ 2 - 4 * X ^ 3 + 24 * X ^ 4 - 16 * X ^ 5) * derivative ℚ G =
      1 + 2 * X - 12 * X ^ 2 - 16 * X ^ 3 + (1 - 2 * X) * S + (X - X ^ 2) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 2 * ((1 - 4 * X ^ 2) * ((4 - 16 * X + 4 * X ^ 2 + 56 * X ^ 3 - 80 * X ^ 4 + 32 * X ^ 5) * derivative ℚ G + (-8 + 88 * X ^ 2 - 144 * X ^ 3 + 64 * X ^ 4) * G - (4 - 8 * X - 16 * X ^ 2 + 8 * X ^ 3))) = 0 := by
    linear_combination (X - X ^ 2) ^ 2 * S * hdS - 2 * (X - X ^ 2) ^ 2 * derivative ℚ S * hS -
      (2 * (1 - 2 * X) * (1 - 4 * X ^ 2) + (X - X ^ 2) * (-8 * X)) * hk + 2 * (X - X ^ 2) * (1 - 4 * X ^ 2) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero 2 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 4 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (2 * X - 6 * X ^ 2 - 4 * X ^ 3 + 24 * X ^ 4 - 16 * X ^ 5 + (0) * S) = X + X ^ 2 - 4 * X ^ 3 - 4 * X ^ 4 + (X - X ^ 2) * S) :
    derivative ℚ G * C 4 + derivative ℚ G * X * C (-16) +
      derivative ℚ G * X * X * C 4 + derivative ℚ G * X * X * X * C 56 +
      derivative ℚ G * X * X * X * X * C (-80) + derivative ℚ G * X * X * X * X * X * C 32 +
      G * C (-8) + G * X * X * C 88 +
      G * X * X * X * C (-144) + G * X * X * X * X * C 64 =
      C 4 + C (-8) * X +
      C (-16) * X * X + C 8 * X * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (2 * X - 6 * X ^ 2 - 4 * X ^ 3 + 24 * X ^ 4 - 16 * X ^ 5 + (0) * S) = X + X ^ 2 - 4 * X ^ 3 - 4 * X ^ 4 + (X - X ^ 2) * S) (m : ℕ) :
    4 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + (-16) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      4 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 56 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      (-80) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + 32 * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-8) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 88 * coeff (m + 1 + 1 + 1) G +
      (-144) * coeff (m + 1 + 1) G + 64 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (2 * X - 6 * X ^ 2 - 4 * X ^ 3 + 24 * X ^ 4 - 16 * X ^ 5 + (0) * S) = X + X ^ 2 - 4 * X ^ 3 - 4 * X ^ 4 + (X - X ^ 2) * S) :
    20 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-64) * coeff (0 + 1 + 1 + 1 + 1) G +
      12 * coeff (0 + 1 + 1 + 1) G + 112 * coeff (0 + 1 + 1) G +
      (-80) * coeff (0 + 1) G + (-8) * coeff (0 + 1 + 1 + 1 + 1) G +
      88 * coeff (0 + 1 + 1) G + (-144) * coeff (0 + 1) G +
      64 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A247374Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a247374.main := by
  intro S A B G hS _ hA hB hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 - 5 = m := rfl
  rw [e1, e2, e3, e4, e5]
  cases m with
  | zero =>
    have r := A247374Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination ((2) * PowerSeries.X + (-2) * PowerSeries.X ^ 2 + (-8) * PowerSeries.X ^ 3 + (8) * PowerSeries.X ^ 4) * hG + ((1) + (-4) * PowerSeries.X ^ 2) * hA + ((1) * S + (-1) * PowerSeries.X * S) * hB + ((1) + (-1) * S + (-2) * PowerSeries.X + (-2) * PowerSeries.X * B + (1) * PowerSeries.X * S + (1) * PowerSeries.X ^ 2 + (6) * PowerSeries.X ^ 2 * B + (-4) * PowerSeries.X ^ 3 * B) * hS)
    push_cast
    linear_combination ((1 : ℚ) / 4) * r
  | succ m =>
    have r := A247374Aux.rel (S) G (by linear_combination hS)
        (by linear_combination ((2) * PowerSeries.X + (-2) * PowerSeries.X ^ 2 + (-8) * PowerSeries.X ^ 3 + (8) * PowerSeries.X ^ 4) * hG + ((1) + (-4) * PowerSeries.X ^ 2) * hA + ((1) * S + (-1) * PowerSeries.X * S) * hB + ((1) + (-1) * S + (-2) * PowerSeries.X + (-2) * PowerSeries.X * B + (1) * PowerSeries.X * S + (1) * PowerSeries.X ^ 2 + (6) * PowerSeries.X ^ 2 * B + (-4) * PowerSeries.X ^ 3 * B) * hS) m
    push_cast
    linear_combination ((1 : ℚ) / 4) * r
