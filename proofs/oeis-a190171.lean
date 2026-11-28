import OMAStatements.S_oeis_a190171

-- Problem: A190171: Number of peakless Motzkin paths of length n having no UHD's starting at level 0; here U=(1,1), H=(1,0), and D=(1,-1).
-- Upstream: formal-conjectures statements/oeis-a190171.lean:0 (declaration OMA.S_oeis_a190171.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A190171Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (1 - X + X ^ 2 + 2 * X ^ 3 + (1) * S) = 2 + (0) * S) :
    (-16 * X + 16 * X ^ 2 + 64 * X ^ 3 + 16 * X ^ 5 + 64 * X ^ 7 + 16 * X ^ 8 - 16 * X ^ 9) * derivative ℚ G + (-32 + 160 * X ^ 2 - 144 * X ^ 3 + 48 * X ^ 4 + 144 * X ^ 5 + 224 * X ^ 6 + 96 * X ^ 7 - 64 * X ^ 8) * G = -32 - 48 * X + 112 * X ^ 2 + 32 * X ^ 3 + 48 * X ^ 4 - 16 * X ^ 5 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have hS2 : S * S = (1 - 2 * X - 1 * (X * X) - 2 * (X * X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (4 * X ^ 2 + 4 * X ^ 3 - 4 * X ^ 4 + 4 * X ^ 5 + 4 * X ^ 6) * G = (2 - 2 * X + 2 * X ^ 2 + 4 * X ^ 3 : ℚ⟦X⟧) + (-2) * S := by
    linear_combination (1 - X + X ^ 2 + 2 * X ^ 3 - (1) * S) * hG + (1) * ((1) * G - (0)) * hS
  have hPd : derivative ℚ (1 - 2 * X - 1 * (X * X) - 2 * (X * X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) = -2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 := by
    simp [Derivation.leibniz, d2]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((4 * (X * X) + 4 * (X * X * X) - 4 * (X * X * X * X) + 4 * (X * X * X * X * X) + 4 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (8 * X + 12 * X ^ 2 - 16 * X ^ 3 + 20 * X ^ 4 + 24 * X ^ 5) * G + (4 * X ^ 2 + 4 * X ^ 3 - 4 * X ^ 4 + 4 * X ^ 5 + 4 * X ^ 6) * derivative ℚ G := by
    simp [Derivation.leibniz, d4]
    ring
  have hR : derivative ℚ ((2 - 2 * X + 2 * (X * X) + 4 * (X * X * X) : ℚ⟦X⟧) + (-2 : ℚ⟦X⟧) * S) =
      -2 + 4 * X + 12 * X ^ 2 + (0) * S + (-2) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hk2 : (4 * (X * X) + 4 * (X * X * X) - 4 * (X * X * X * X) + 4 * (X * X * X * X * X) + 4 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G = (2 - 2 * X + 2 * (X * X) + 4 * (X * X * X) : ℚ⟦X⟧) + (-2 : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (8 * X + 12 * X ^ 2 - 16 * X ^ 3 + 20 * X ^ 4 + 24 * X ^ 5) * G + (4 * X ^ 2 + 4 * X ^ 3 - 4 * X ^ 4 + 4 * X ^ 5 + 4 * X ^ 6) * derivative ℚ G =
      -2 + 4 * X + 12 * X ^ 2 + (0) * S + (-2) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 1 * ((-16 * X + 16 * X ^ 2 + 64 * X ^ 3 + 16 * X ^ 5 + 64 * X ^ 7 + 16 * X ^ 8 - 16 * X ^ 9) * derivative ℚ G + (-32 + 160 * X ^ 2 - 144 * X ^ 3 + 48 * X ^ 4 + 144 * X ^ 5 + 224 * X ^ 6 + 96 * X ^ 7 - 64 * X ^ 8) * G - (-32 - 48 * X + 112 * X ^ 2 + 32 * X ^ 3 + 48 * X ^ 4 - 16 * X ^ 5)) = 0 := by
    linear_combination (-2) ^ 2 * S * hdS - 2 * (-2) ^ 2 * derivative ℚ S * hS -
      (2 * (0) * (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) + (-2) * (-2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3)) * hk + 2 * (-2) * (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 1 ≠ 0 := pow_ne_zero 1 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  linear_combination h1

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (1 - X + X ^ 2 + 2 * X ^ 3 + (1) * S) = 2 + (0) * S) :
    derivative ℚ G * X * C (-16) + derivative ℚ G * X * X * C 16 +
      derivative ℚ G * X * X * X * C 64 + derivative ℚ G * X * X * X * X * X * C 16 +
      derivative ℚ G * X * X * X * X * X * X * X * C 64 + derivative ℚ G * X * X * X * X * X * X * X * X * C 16 +
      derivative ℚ G * X * X * X * X * X * X * X * X * X * C (-16) + G * C (-32) +
      G * X * X * C 160 + G * X * X * X * C (-144) +
      G * X * X * X * X * C 48 + G * X * X * X * X * X * C 144 +
      G * X * X * X * X * X * X * C 224 + G * X * X * X * X * X * X * X * C 96 +
      G * X * X * X * X * X * X * X * X * C (-64) =
      C (-32) + C (-48) * X +
      C 112 * X * X + C 32 * X * X * X +
      C 48 * X * X * X * X + C (-16) * X * X * X * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (1 - X + X ^ 2 + 2 * X ^ 3 + (1) * S) = 2 + (0) * S) (m : ℕ) :
    (-16) * ((m : ℚ) + 9) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 16 * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      64 * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 16 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      64 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 16 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-16) * ((m : ℚ) + 1) * coeff (m + 1) G + (-32) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      160 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-144) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      48 * coeff (m + 1 + 1 + 1 + 1 + 1) G + 144 * coeff (m + 1 + 1 + 1 + 1) G +
      224 * coeff (m + 1 + 1 + 1) G + 96 * coeff (m + 1 + 1) G +
      (-64) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (1 - X + X ^ 2 + 2 * X ^ 3 + (1) * S) = 2 + (0) * S) :
    (-128) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 112 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      384 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 64 * coeff (0 + 1 + 1 + 1 + 1) G +
      128 * coeff (0 + 1 + 1) G + 16 * coeff (0 + 1) G +
      (-32) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 160 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-144) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 48 * coeff (0 + 1 + 1 + 1 + 1) G +
      144 * coeff (0 + 1 + 1 + 1) G + 224 * coeff (0 + 1 + 1) G +
      96 * coeff (0 + 1) G + (-64) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A190171Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a190171.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 8, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 + 1 := rfl
  have e7 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 = m + 1 := rfl
  have e8 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 8 = m := rfl
  rw [e1, e2, e3, e4, e5, e6, e7, e8]
  cases m with
  | zero =>
    have r := A190171Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination ((-1 : ℚ) / 16) * r
  | succ m =>
    have r := A190171Aux.rel (S) G (by linear_combination hS)
        (by linear_combination hG) m
    push_cast
    linear_combination ((-1 : ℚ) / 16) * r
