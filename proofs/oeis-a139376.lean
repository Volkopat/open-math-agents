import OMAStatements.S_oeis_a139376

-- Problem: A139376: Expansion of 1/((1-x^2*c(x))(1-x-x^2)) where c(x) is the g.f. of A000108.
-- Upstream: formal-conjectures statements/oeis-a139376.lean:0 (declaration OMA.S_oeis_a139376.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A139376Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (2 - 3 * X - X ^ 2 + X ^ 3 + (X - X ^ 2 - X ^ 3) * S) = 2 + (0) * S) :
    (-16 * X + 96 * X ^ 2 - 128 * X ^ 3 - 32 * X ^ 4 + 144 * X ^ 5 - 48 * X ^ 6 - 64 * X ^ 7) * derivative ℚ G + (16 - 96 * X + 64 * X ^ 2 - 64 * X ^ 3 + 240 * X ^ 4 - 96 * X ^ 5 - 224 * X ^ 6) * G = 16 - 96 * X + 16 * X ^ 2 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (4 - 12 * X + 4 * X ^ 2 + 16 * X ^ 3 - 12 * X ^ 4 - 8 * X ^ 5 + 8 * X ^ 6 + 4 * X ^ 7) * G = (4 - 6 * X - 2 * X ^ 2 + 2 * X ^ 3 : ℚ⟦X⟧) + (-2 * X + 2 * X ^ 2 + 2 * X ^ 3) * S := by
    linear_combination (2 - 3 * X - X ^ 2 + X ^ 3 - (X - X ^ 2 - X ^ 3) * S) * hG + (X - X ^ 2 - X ^ 3) * ((X - X ^ 2 - X ^ 3) * G - (0)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((4 - 12 * X + 4 * (X * X) + 16 * (X * X * X) - 12 * (X * X * X * X) - 8 * (X * X * X * X * X) + 8 * (X * X * X * X * X * X) + 4 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-12 + 8 * X + 48 * X ^ 2 - 48 * X ^ 3 - 40 * X ^ 4 + 48 * X ^ 5 + 28 * X ^ 6) * G + (4 - 12 * X + 4 * X ^ 2 + 16 * X ^ 3 - 12 * X ^ 4 - 8 * X ^ 5 + 8 * X ^ 6 + 4 * X ^ 7) * derivative ℚ G := by
    simp [Derivation.leibniz, d4, d8, d12, d16]
    ring
  have hR : derivative ℚ ((4 - 6 * X - 2 * (X * X) + 2 * (X * X * X) : ℚ⟦X⟧) + (-2 * X + 2 * (X * X) + 2 * (X * X * X) : ℚ⟦X⟧) * S) =
      -6 - 4 * X + 6 * X ^ 2 + (-2 + 4 * X + 6 * X ^ 2) * S + (-2 * X + 2 * X ^ 2 + 2 * X ^ 3) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d4, d6]
    ring
  have hk2 : (4 - 12 * X + 4 * (X * X) + 16 * (X * X * X) - 12 * (X * X * X * X) - 8 * (X * X * X * X * X) + 8 * (X * X * X * X * X * X) + 4 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (4 - 6 * X - 2 * (X * X) + 2 * (X * X * X) : ℚ⟦X⟧) + (-2 * X + 2 * (X * X) + 2 * (X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-12 + 8 * X + 48 * X ^ 2 - 48 * X ^ 3 - 40 * X ^ 4 + 48 * X ^ 5 + 28 * X ^ 6) * G + (4 - 12 * X + 4 * X ^ 2 + 16 * X ^ 3 - 12 * X ^ 4 - 8 * X ^ 5 + 8 * X ^ 6 + 4 * X ^ 7) * derivative ℚ G =
      -6 - 4 * X + 6 * X ^ 2 + (-2 + 4 * X + 6 * X ^ 2) * S + (-2 * X + 2 * X ^ 2 + 2 * X ^ 3) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 - 2 * X - X ^ 2 + 2 * X ^ 3 + X ^ 4) * ((-16 * X + 96 * X ^ 2 - 128 * X ^ 3 - 32 * X ^ 4 + 144 * X ^ 5 - 48 * X ^ 6 - 64 * X ^ 7) * derivative ℚ G + (16 - 96 * X + 64 * X ^ 2 - 64 * X ^ 3 + 240 * X ^ 4 - 96 * X ^ 5 - 224 * X ^ 6) * G - (16 - 96 * X + 16 * X ^ 2)) = 0 := by
    linear_combination (-2 * X + 2 * X ^ 2 + 2 * X ^ 3) ^ 2 * S * hdS - 2 * (-2 * X + 2 * X ^ 2 + 2 * X ^ 3) ^ 2 * derivative ℚ S * hS -
      (2 * (-2 + 4 * X + 6 * X ^ 2) * (1 - 4 * X) + (-2 * X + 2 * X ^ 2 + 2 * X ^ 3) * (-4)) * hk + 2 * (-2 * X + 2 * X ^ 2 + 2 * X ^ 3) * (1 - 4 * X) * hdk
  have hg : (1 - 2 * X - X ^ 2 + 2 * X ^ 3 + X ^ 4 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (2 - 3 * X - X ^ 2 + X ^ 3 + (X - X ^ 2 - X ^ 3) * S) = 2 + (0) * S) :
    derivative ℚ G * X * C (-16) + derivative ℚ G * X * X * C 96 +
      derivative ℚ G * X * X * X * C (-128) + derivative ℚ G * X * X * X * X * C (-32) +
      derivative ℚ G * X * X * X * X * X * C 144 + derivative ℚ G * X * X * X * X * X * X * C (-48) +
      derivative ℚ G * X * X * X * X * X * X * X * C (-64) + G * C 16 +
      G * X * C (-96) + G * X * X * C 64 +
      G * X * X * X * C (-64) + G * X * X * X * X * C 240 +
      G * X * X * X * X * X * C (-96) + G * X * X * X * X * X * X * C (-224) =
      C 16 + C (-96) * X +
      C 16 * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (2 - 3 * X - X ^ 2 + X ^ 3 + (X - X ^ 2 - X ^ 3) * S) = 2 + (0) * S) (m : ℕ) :
    (-16) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 96 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-128) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-32) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      144 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-48) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-64) * ((m : ℚ) + 1) * coeff (m + 1) G + 16 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-96) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 64 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-64) * coeff (m + 1 + 1 + 1 + 1) G + 240 * coeff (m + 1 + 1 + 1) G +
      (-96) * coeff (m + 1 + 1) G + (-224) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (2 - 3 * X - X ^ 2 + X ^ 3 + (X - X ^ 2 - X ^ 3) * S) = 2 + (0) * S) :
    (-96) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 480 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-512) * coeff (0 + 1 + 1 + 1 + 1) G + (-96) * coeff (0 + 1 + 1 + 1) G +
      288 * coeff (0 + 1 + 1) G + (-48) * coeff (0 + 1) G +
      16 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-96) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      64 * coeff (0 + 1 + 1 + 1 + 1) G + (-64) * coeff (0 + 1 + 1 + 1) G +
      240 * coeff (0 + 1 + 1) G + (-96) * coeff (0 + 1) G +
      (-224) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A139376Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a139376.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 6, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m := rfl
  rw [e1, e2, e3, e4, e5, e6]
  cases m with
  | zero =>
    have r := A139376Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination 2 * hG + G * (1 - PowerSeries.X - PowerSeries.X ^ 2) * PowerSeries.X * hc)
    push_cast
    linear_combination ((1 : ℚ) / 16) * r
  | succ m =>
    have r := A139376Aux.rel (S) G (by linear_combination hS)
        (by linear_combination 2 * hG + G * (1 - PowerSeries.X - PowerSeries.X ^ 2) * PowerSeries.X * hc) m
    push_cast
    linear_combination ((1 : ℚ) / 16) * r
