import OMAStatements.S_oeis_a101596

-- Problem: A101596: Expansion of g.f. c(2*x)^4, where c(x) is the g.f. of A000108.
-- Upstream: formal-conjectures statements/oeis-a101596.lean:0 (declaration OMA.S_oeis_a101596.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A101596Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X)
    (hG : G * (256 * X ^ 4 + (0) * S) = 8 - 64 * X + 64 * X ^ 2 + (-8 + 32 * X) * S) :
    (-4096 * X + 49152 * X ^ 2 - 131072 * X ^ 3) * derivative ℚ G + (-16384 + 163840 * X - 327680 * X ^ 2) * G = -16384 := by
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have d64 : derivative ℚ (64 : ℚ⟦X⟧) = 0 := dnum 64
  have d256 : derivative ℚ (256 : ℚ⟦X⟧) = 0 := dnum 256
  have hS2 : S * S = (1 - 8 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (256 * X ^ 4) * G = (8 - 64 * X + 64 * X ^ 2 : ℚ⟦X⟧) + (-8 + 32 * X) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 8 * X : ℚ⟦X⟧) = -8 := by
    simp [Derivation.leibniz, d8]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -8 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((256 * (X * X * X * X) : ℚ⟦X⟧) * G) = (1024 * X ^ 3) * G + (256 * X ^ 4) * derivative ℚ G := by
    simp [Derivation.leibniz, d256]
    ring
  have hR : derivative ℚ ((8 - 64 * X + 64 * (X * X) : ℚ⟦X⟧) + (-8 + 32 * X : ℚ⟦X⟧) * S) =
      -64 + 128 * X + (32) * S + (-8 + 32 * X) * derivative ℚ S := by
    simp [Derivation.leibniz, d8, d32, d64]
    ring
  have hk2 : (256 * (X * X * X * X) : ℚ⟦X⟧) * G = (8 - 64 * X + 64 * (X * X) : ℚ⟦X⟧) + (-8 + 32 * X : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (1024 * X ^ 3) * G + (256 * X ^ 4) * derivative ℚ G =
      -64 + 128 * X + (32) * S + (-8 + 32 * X) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 3 * ((-4096 * X + 49152 * X ^ 2 - 131072 * X ^ 3) * derivative ℚ G + (-16384 + 163840 * X - 327680 * X ^ 2) * G - (-16384)) = 0 := by
    linear_combination (-8 + 32 * X) ^ 2 * S * hdS - 2 * (-8 + 32 * X) ^ 2 * derivative ℚ S * hS -
      (2 * (32) * (1 - 8 * X) + (-8 + 32 * X) * (-8)) * hk + 2 * (-8 + 32 * X) * (1 - 8 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 3 ≠ 0 := pow_ne_zero 3 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  linear_combination h1

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X)
    (hG : G * (256 * X ^ 4 + (0) * S) = 8 - 64 * X + 64 * X ^ 2 + (-8 + 32 * X) * S) :
    derivative ℚ G * X * C (-4096) + derivative ℚ G * X * X * C 49152 +
      derivative ℚ G * X * X * X * C (-131072) + G * C (-16384) +
      G * X * C 163840 + G * X * X * C (-327680) =
      C (-16384) := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X)
    (hG : G * (256 * X ^ 4 + (0) * S) = 8 - 64 * X + 64 * X ^ 2 + (-8 + 32 * X) * S) (m : ℕ) :
    (-4096) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 49152 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-131072) * ((m : ℚ) + 1) * coeff (m + 1) G + (-16384) * coeff (m + 1 + 1 + 1) G +
      163840 * coeff (m + 1 + 1) G + (-327680) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X)
    (hG : G * (256 * X ^ 4 + (0) * S) = 8 - 64 * X + 64 * X ^ 2 + (-8 + 32 * X) * S) :
    (-8192) * coeff (0 + 1 + 1) G + 49152 * coeff (0 + 1) G +
      (-16384) * coeff (0 + 1 + 1) G + 163840 * coeff (0 + 1) G +
      (-327680) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A101596Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a101596.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  cases m with
  | zero =>
    have r := A101596Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (256 * PowerSeries.X ^ 4) * hG - ((-1) + (3) * S + (-3) * S ^ 2 + (1) * S ^ 3 + (-4 * PowerSeries.X) * c + (8 * PowerSeries.X) * c * S + (-4 * PowerSeries.X) * c * S ^ 2 + (-16 * PowerSeries.X ^ 2) * c ^ 2 + (16 * PowerSeries.X ^ 2) * c ^ 2 * S + (-64 * PowerSeries.X ^ 3) * c ^ 3) * hc - ((-7 + 8 * PowerSeries.X) + (4) * S + (-1) * S ^ 2) * hS)
    push_cast
    linear_combination ((-1 : ℚ) / 4096) * r
  | succ m =>
    have r := A101596Aux.rel (S) G (by linear_combination hS)
        (by linear_combination (256 * PowerSeries.X ^ 4) * hG - ((-1) + (3) * S + (-3) * S ^ 2 + (1) * S ^ 3 + (-4 * PowerSeries.X) * c + (8 * PowerSeries.X) * c * S + (-4 * PowerSeries.X) * c * S ^ 2 + (-16 * PowerSeries.X ^ 2) * c ^ 2 + (16 * PowerSeries.X ^ 2) * c ^ 2 * S + (-64 * PowerSeries.X ^ 3) * c ^ 3) * hc - ((-7 + 8 * PowerSeries.X) + (4) * S + (-1) * S ^ 2) * hS) m
    push_cast
    linear_combination ((-1 : ℚ) / 4096) * r
