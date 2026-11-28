import OMAStatements.S_oeis_a116388

-- Problem: A116388: Expansion of 1/((1+x*(1-M(x)))*sqrt(1-2*x-3*x^2)), M(x) the g.f. of A001006.
-- Upstream: formal-conjectures statements/oeis-a116388.lean:0 (declaration OMA.S_oeis_a116388.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A116388Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (1 - 2 * X - 3 * X ^ 2 + (-1 + 3 * X + 2 * X ^ 2) * S) = 2 * X + (0) * S) :
    (16 - 112 * X + 128 * X ^ 2 + 400 * X ^ 3 - 288 * X ^ 4 - 832 * X ^ 5 - 496 * X ^ 6 - 96 * X ^ 7) * derivative ℚ G + (-32 * X + 272 * X ^ 2 - 112 * X ^ 3 - 976 * X ^ 4 - 816 * X ^ 5 - 192 * X ^ 6) * G = 16 - 16 * X - 48 * X ^ 2 - 48 * X ^ 3 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d44 : derivative ℚ (44 : ℚ⟦X⟧) = 0 := dnum 44
  have hS2 : S * S = (1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (4 * X - 16 * X ^ 2 - 8 * X ^ 3 + 44 * X ^ 4 + 44 * X ^ 5 + 12 * X ^ 6) * G = (2 * X - 4 * X ^ 2 - 6 * X ^ 3 : ℚ⟦X⟧) + (2 * X - 6 * X ^ 2 - 4 * X ^ 3) * S := by
    linear_combination (1 - 2 * X - 3 * X ^ 2 - (-1 + 3 * X + 2 * X ^ 2) * S) * hG + (-1 + 3 * X + 2 * X ^ 2) * ((-1 + 3 * X + 2 * X ^ 2) * G - (0)) * hS
  have hPd : derivative ℚ (1 - 2 * X - 3 * (X * X) : ℚ⟦X⟧) = -2 - 6 * X := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -2 - 6 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((4 * X - 16 * (X * X) - 8 * (X * X * X) + 44 * (X * X * X * X) + 44 * (X * X * X * X * X) + 12 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (4 - 32 * X - 24 * X ^ 2 + 176 * X ^ 3 + 220 * X ^ 4 + 72 * X ^ 5) * G + (4 * X - 16 * X ^ 2 - 8 * X ^ 3 + 44 * X ^ 4 + 44 * X ^ 5 + 12 * X ^ 6) * derivative ℚ G := by
    simp [Derivation.leibniz, d4, d8, d12, d16, d44]
    ring
  have hR : derivative ℚ ((2 * X - 4 * (X * X) - 6 * (X * X * X) : ℚ⟦X⟧) + (2 * X - 6 * (X * X) - 4 * (X * X * X) : ℚ⟦X⟧) * S) =
      2 - 8 * X - 18 * X ^ 2 + (2 - 12 * X - 12 * X ^ 2) * S + (2 * X - 6 * X ^ 2 - 4 * X ^ 3) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d4, d6]
    ring
  have hk2 : (4 * X - 16 * (X * X) - 8 * (X * X * X) + 44 * (X * X * X * X) + 44 * (X * X * X * X * X) + 12 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G = (2 * X - 4 * (X * X) - 6 * (X * X * X) : ℚ⟦X⟧) + (2 * X - 6 * (X * X) - 4 * (X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (4 - 32 * X - 24 * X ^ 2 + 176 * X ^ 3 + 220 * X ^ 4 + 72 * X ^ 5) * G + (4 * X - 16 * X ^ 2 - 8 * X ^ 3 + 44 * X ^ 4 + 44 * X ^ 5 + 12 * X ^ 6) * derivative ℚ G =
      2 - 8 * X - 18 * X ^ 2 + (2 - 12 * X - 12 * X ^ 2) * S + (2 * X - 6 * X ^ 2 - 4 * X ^ 3) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 2 * ((1 - 2 * X - 3 * X ^ 2) * ((16 - 112 * X + 128 * X ^ 2 + 400 * X ^ 3 - 288 * X ^ 4 - 832 * X ^ 5 - 496 * X ^ 6 - 96 * X ^ 7) * derivative ℚ G + (-32 * X + 272 * X ^ 2 - 112 * X ^ 3 - 976 * X ^ 4 - 816 * X ^ 5 - 192 * X ^ 6) * G - (16 - 16 * X - 48 * X ^ 2 - 48 * X ^ 3))) = 0 := by
    linear_combination (2 * X - 6 * X ^ 2 - 4 * X ^ 3) ^ 2 * S * hdS - 2 * (2 * X - 6 * X ^ 2 - 4 * X ^ 3) ^ 2 * derivative ℚ S * hS -
      (2 * (2 - 12 * X - 12 * X ^ 2) * (1 - 2 * X - 3 * X ^ 2) + (2 * X - 6 * X ^ 2 - 4 * X ^ 3) * (-2 - 6 * X)) * hk + 2 * (2 * X - 6 * X ^ 2 - 4 * X ^ 3) * (1 - 2 * X - 3 * X ^ 2) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero 2 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 2 * X - 3 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (1 - 2 * X - 3 * X ^ 2 + (-1 + 3 * X + 2 * X ^ 2) * S) = 2 * X + (0) * S) :
    derivative ℚ G * C 16 + derivative ℚ G * X * C (-112) +
      derivative ℚ G * X * X * C 128 + derivative ℚ G * X * X * X * C 400 +
      derivative ℚ G * X * X * X * X * C (-288) + derivative ℚ G * X * X * X * X * X * C (-832) +
      derivative ℚ G * X * X * X * X * X * X * C (-496) + derivative ℚ G * X * X * X * X * X * X * X * C (-96) +
      G * X * C (-32) + G * X * X * C 272 +
      G * X * X * X * C (-112) + G * X * X * X * X * C (-976) +
      G * X * X * X * X * X * C (-816) + G * X * X * X * X * X * X * C (-192) =
      C 16 + C (-16) * X +
      C (-48) * X * X + C (-48) * X * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (1 - 2 * X - 3 * X ^ 2 + (-1 + 3 * X + 2 * X ^ 2) * S) = 2 * X + (0) * S) (m : ℕ) :
    16 * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-112) * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      128 * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 400 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-288) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + (-832) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      (-496) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + (-96) * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-32) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 272 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-112) * coeff (m + 1 + 1 + 1 + 1) G + (-976) * coeff (m + 1 + 1 + 1) G +
      (-816) * coeff (m + 1 + 1) G + (-192) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - 3 * X ^ 2)
    (hG : G * (1 - 2 * X - 3 * X ^ 2 + (-1 + 3 * X + 2 * X ^ 2) * S) = 2 * X + (0) * S) :
    112 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-672) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      640 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 1600 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-864) * coeff (0 + 1 + 1 + 1) G + (-1664) * coeff (0 + 1 + 1) G +
      (-496) * coeff (0 + 1) G + (-32) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      272 * coeff (0 + 1 + 1 + 1 + 1) G + (-112) * coeff (0 + 1 + 1 + 1) G +
      (-976) * coeff (0 + 1 + 1) G + (-816) * coeff (0 + 1) G +
      (-192) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A116388Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a116388.main := by
  intro S M G hS _ hM hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 + 1 + 1 := ⟨n - 7, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 + 1 + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 5 = m + 1 + 1 := rfl
  have e6 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 6 = m + 1 := rfl
  have e7 : m + 1 + 1 + 1 + 1 + 1 + 1 + 1 - 7 = m := rfl
  rw [e1, e2, e3, e4, e5, e6, e7]
  cases m with
  | zero =>
    have r := A116388Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination 2 * PowerSeries.X * hG + G * S * hM - G * hS)
    push_cast
    linear_combination ((1 : ℚ) / 16) * r
  | succ m =>
    have r := A116388Aux.rel (S) G (by linear_combination hS)
        (by linear_combination 2 * PowerSeries.X * hG + G * S * hM - G * hS) m
    push_cast
    linear_combination ((1 : ℚ) / 16) * r
