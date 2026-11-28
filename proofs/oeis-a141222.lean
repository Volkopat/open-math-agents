import OMAStatements.S_oeis_a141222

-- Problem: A141222: Expansion of -1/(2*x) + (2*x-1)^2/(2*x*(1-4x)^(3/2)).
-- Upstream: formal-conjectures statements/oeis-a141222.lean:0 (declaration OMA.S_oeis_a141222.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A141222Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (0 + (2 * X - 8 * X ^ 2) * S) = 1 - 4 * X + 4 * X ^ 2 + (-1 + 4 * X) * S) :
    (16 * X - 96 * X ^ 2 + 128 * X ^ 3) * derivative ℚ G + (16 - 128 * X + 64 * X ^ 2) * G = 16 + 32 * X := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d40 : derivative ℚ (40 : ℚ⟦X⟧) = 0 := dnum 40
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d96 : derivative ℚ (96 : ℚ⟦X⟧) = 0 := dnum 96
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d192 : derivative ℚ (192 : ℚ⟦X⟧) = 0 := dnum 192
  have d256 : derivative ℚ (256 : ℚ⟦X⟧) = 0 := dnum 256
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-4 * X ^ 2 + 48 * X ^ 3 - 192 * X ^ 4 + 256 * X ^ 5) * G = (2 * X - 24 * X ^ 2 + 96 * X ^ 3 - 128 * X ^ 4 : ℚ⟦X⟧) + (-2 * X + 16 * X ^ 2 - 40 * X ^ 3 + 32 * X ^ 4) * S := by
    linear_combination (0 - (2 * X - 8 * X ^ 2) * S) * hG + (2 * X - 8 * X ^ 2) * ((2 * X - 8 * X ^ 2) * G - (-1 + 4 * X)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-4 * (X * X) + 48 * (X * X * X) - 192 * (X * X * X * X) + 256 * (X * X * X * X * X) : ℚ⟦X⟧) * G) = (-8 * X + 144 * X ^ 2 - 768 * X ^ 3 + 1280 * X ^ 4) * G + (-4 * X ^ 2 + 48 * X ^ 3 - 192 * X ^ 4 + 256 * X ^ 5) * derivative ℚ G := by
    simp [Derivation.leibniz, d4, d48, d192, d256]
    ring
  have hR : derivative ℚ ((2 * X - 24 * (X * X) + 96 * (X * X * X) - 128 * (X * X * X * X) : ℚ⟦X⟧) + (-2 * X + 16 * (X * X) - 40 * (X * X * X) + 32 * (X * X * X * X) : ℚ⟦X⟧) * S) =
      2 - 48 * X + 288 * X ^ 2 - 512 * X ^ 3 + (-2 + 32 * X - 120 * X ^ 2 + 128 * X ^ 3) * S + (-2 * X + 16 * X ^ 2 - 40 * X ^ 3 + 32 * X ^ 4) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d16, d24, d32, d40, d96, d128]
    ring
  have hk2 : (-4 * (X * X) + 48 * (X * X * X) - 192 * (X * X * X * X) + 256 * (X * X * X * X * X) : ℚ⟦X⟧) * G = (2 * X - 24 * (X * X) + 96 * (X * X * X) - 128 * (X * X * X * X) : ℚ⟦X⟧) + (-2 * X + 16 * (X * X) - 40 * (X * X * X) + 32 * (X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-8 * X + 144 * X ^ 2 - 768 * X ^ 3 + 1280 * X ^ 4) * G + (-4 * X ^ 2 + 48 * X ^ 3 - 192 * X ^ 4 + 256 * X ^ 5) * derivative ℚ G =
      2 - 48 * X + 288 * X ^ 2 - 512 * X ^ 3 + (-2 + 32 * X - 120 * X ^ 2 + 128 * X ^ 3) * S + (-2 * X + 16 * X ^ 2 - 40 * X ^ 3 + 32 * X ^ 4) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 2 * ((1 - 18 * X + 128 * X ^ 2 - 448 * X ^ 3 + 768 * X ^ 4 - 512 * X ^ 5) * ((16 * X - 96 * X ^ 2 + 128 * X ^ 3) * derivative ℚ G + (16 - 128 * X + 64 * X ^ 2) * G - (16 + 32 * X))) = 0 := by
    linear_combination (-2 * X + 16 * X ^ 2 - 40 * X ^ 3 + 32 * X ^ 4) ^ 2 * S * hdS - 2 * (-2 * X + 16 * X ^ 2 - 40 * X ^ 3 + 32 * X ^ 4) ^ 2 * derivative ℚ S * hS -
      (2 * (-2 + 32 * X - 120 * X ^ 2 + 128 * X ^ 3) * (1 - 4 * X) + (-2 * X + 16 * X ^ 2 - 40 * X ^ 3 + 32 * X ^ 4) * (-4)) * hk + 2 * (-2 * X + 16 * X ^ 2 - 40 * X ^ 3 + 32 * X ^ 4) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero 2 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 18 * X + 128 * X ^ 2 - 448 * X ^ 3 + 768 * X ^ 4 - 512 * X ^ 5 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (0 + (2 * X - 8 * X ^ 2) * S) = 1 - 4 * X + 4 * X ^ 2 + (-1 + 4 * X) * S) :
    derivative ℚ G * X * C 16 + derivative ℚ G * X * X * C (-96) +
      derivative ℚ G * X * X * X * C 128 + G * C 16 +
      G * X * C (-128) + G * X * X * C 64 =
      C 16 + C 32 * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (0 + (2 * X - 8 * X ^ 2) * S) = 1 - 4 * X + 4 * X ^ 2 + (-1 + 4 * X) * S) (m : ℕ) :
    16 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-96) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      128 * ((m : ℚ) + 1) * coeff (m + 1) G + 16 * coeff (m + 1 + 1 + 1) G +
      (-128) * coeff (m + 1 + 1) G + 64 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (0 + (2 * X - 8 * X ^ 2) * S) = 1 - 4 * X + 4 * X ^ 2 + (-1 + 4 * X) * S) :
    32 * coeff (0 + 1 + 1) G + (-96) * coeff (0 + 1) G +
      16 * coeff (0 + 1 + 1) G + (-128) * coeff (0 + 1) G +
      64 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A141222Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a141222.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  cases m with
  | zero =>
    have r := A141222Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination ((1 : ℚ) / 16) * r
  | succ m =>
    have r := A141222Aux.rel (S) G (by linear_combination hS)
        (by linear_combination hG) m
    push_cast
    linear_combination ((1 : ℚ) / 16) * r
