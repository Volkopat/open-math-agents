import OMAStatements.S_oeis_a337499

-- Problem: A337499: a(n) is the number of ballot sequences of length n tied or won by at most 2 votes.
-- Upstream: formal-conjectures statements/oeis-a337499.lean:0 (declaration OMA.S_oeis_a337499.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A337499Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (2 - 8 * X ^ 2 + (2 - 4 * X ^ 2) * S) = 2 + 4 * X + 4 * X ^ 2 + (2 + 4 * X) * S) :
    (512 * X + 512 * X ^ 2 - 2560 * X ^ 3 - 2048 * X ^ 4 + 2048 * X ^ 5) * derivative ℚ G + (1024 + 512 * X - 6144 * X ^ 2 - 4096 * X ^ 3 + 2048 * X ^ 4) * G = 1024 + 3584 * X + 4096 * X ^ 2 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have hS2 : S * S = (1 - 4 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-16 * X ^ 4 + 64 * X ^ 6) * G = (16 * X ^ 2 + 16 * X ^ 3 - 64 * X ^ 4 - 64 * X ^ 5 : ℚ⟦X⟧) + (-16 * X ^ 2 - 16 * X ^ 3 + 16 * X ^ 4) * S := by
    linear_combination (2 - 8 * X ^ 2 - (2 - 4 * X ^ 2) * S) * hG + (2 - 4 * X ^ 2) * ((2 - 4 * X ^ 2) * G - (2 + 4 * X)) * hS
  have hPd : derivative ℚ (1 - 4 * (X * X) : ℚ⟦X⟧) = -8 * X := by
    simp [Derivation.leibniz, d4]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -8 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-16 * (X * X * X * X) + 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-64 * X ^ 3 + 384 * X ^ 5) * G + (-16 * X ^ 4 + 64 * X ^ 6) * derivative ℚ G := by
    simp [Derivation.leibniz, d16, d64]
    ring
  have hR : derivative ℚ ((16 * (X * X) + 16 * (X * X * X) - 64 * (X * X * X * X) - 64 * (X * X * X * X * X) : ℚ⟦X⟧) + (-16 * (X * X) - 16 * (X * X * X) + 16 * (X * X * X * X) : ℚ⟦X⟧) * S) =
      32 * X + 48 * X ^ 2 - 256 * X ^ 3 - 320 * X ^ 4 + (-32 * X - 48 * X ^ 2 + 64 * X ^ 3) * S + (-16 * X ^ 2 - 16 * X ^ 3 + 16 * X ^ 4) * derivative ℚ S := by
    simp [Derivation.leibniz, d16, d64]
    ring
  have hk2 : (-16 * (X * X * X * X) + 64 * (X * X * X * X * X * X) : ℚ⟦X⟧) * G = (16 * (X * X) + 16 * (X * X * X) - 64 * (X * X * X * X) - 64 * (X * X * X * X * X) : ℚ⟦X⟧) + (-16 * (X * X) - 16 * (X * X * X) + 16 * (X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-64 * X ^ 3 + 384 * X ^ 5) * G + (-16 * X ^ 4 + 64 * X ^ 6) * derivative ℚ G =
      32 * X + 48 * X ^ 2 - 256 * X ^ 3 - 320 * X ^ 4 + (-32 * X - 48 * X ^ 2 + 64 * X ^ 3) * S + (-16 * X ^ 2 - 16 * X ^ 3 + 16 * X ^ 4) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 5 * ((1 - 4 * X ^ 2) * ((512 * X + 512 * X ^ 2 - 2560 * X ^ 3 - 2048 * X ^ 4 + 2048 * X ^ 5) * derivative ℚ G + (1024 + 512 * X - 6144 * X ^ 2 - 4096 * X ^ 3 + 2048 * X ^ 4) * G - (1024 + 3584 * X + 4096 * X ^ 2))) = 0 := by
    linear_combination (-16 * X ^ 2 - 16 * X ^ 3 + 16 * X ^ 4) ^ 2 * S * hdS - 2 * (-16 * X ^ 2 - 16 * X ^ 3 + 16 * X ^ 4) ^ 2 * derivative ℚ S * hS -
      (2 * (-32 * X - 48 * X ^ 2 + 64 * X ^ 3) * (1 - 4 * X ^ 2) + (-16 * X ^ 2 - 16 * X ^ 3 + 16 * X ^ 4) * (-8 * X)) * hk + 2 * (-16 * X ^ 2 - 16 * X ^ 3 + 16 * X ^ 4) * (1 - 4 * X ^ 2) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 5 ≠ 0 := pow_ne_zero 5 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 4 * X ^ 2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (2 - 8 * X ^ 2 + (2 - 4 * X ^ 2) * S) = 2 + 4 * X + 4 * X ^ 2 + (2 + 4 * X) * S) :
    derivative ℚ G * X * C 512 + derivative ℚ G * X * X * C 512 +
      derivative ℚ G * X * X * X * C (-2560) + derivative ℚ G * X * X * X * X * C (-2048) +
      derivative ℚ G * X * X * X * X * X * C 2048 + G * C 1024 +
      G * X * C 512 + G * X * X * C (-6144) +
      G * X * X * X * C (-4096) + G * X * X * X * X * C 2048 =
      C 1024 + C 3584 * X +
      C 4096 * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (2 - 8 * X ^ 2 + (2 - 4 * X ^ 2) * S) = 2 + 4 * X + 4 * X ^ 2 + (2 + 4 * X) * S) (m : ℕ) :
    512 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 512 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-2560) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-2048) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      2048 * ((m : ℚ) + 1) * coeff (m + 1) G + 1024 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      512 * coeff (m + 1 + 1 + 1 + 1) G + (-6144) * coeff (m + 1 + 1 + 1) G +
      (-4096) * coeff (m + 1 + 1) G + 2048 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X ^ 2)
    (hG : G * (2 - 8 * X ^ 2 + (2 - 4 * X ^ 2) * S) = 2 + 4 * X + 4 * X ^ 2 + (2 + 4 * X) * S) :
    2048 * coeff (0 + 1 + 1 + 1 + 1) G + 1536 * coeff (0 + 1 + 1 + 1) G +
      (-5120) * coeff (0 + 1 + 1) G + (-2048) * coeff (0 + 1) G +
      1024 * coeff (0 + 1 + 1 + 1 + 1) G + 512 * coeff (0 + 1 + 1 + 1) G +
      (-6144) * coeff (0 + 1 + 1) G + (-4096) * coeff (0 + 1) G +
      2048 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A337499Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a337499.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  cases m with
  | zero =>
    have r := A337499Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG - (G * (2 + S)) * hS)
    push_cast
    linear_combination ((1 : ℚ) / 512) * r
  | succ m =>
    have r := A337499Aux.rel (S) G (by linear_combination hS)
        (by linear_combination hG - (G * (2 + S)) * hS) m
    push_cast
    linear_combination ((1 : ℚ) / 512) * r
