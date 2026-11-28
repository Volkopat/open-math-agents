import OMAStatements.S_oeis_a226316

-- Problem: A226316: Expansion of g.f. 1/2 + 1/(1+sqrt(1-8*x+8*x^2)).
-- Upstream: formal-conjectures statements/oeis-a226316.lean:0 (declaration OMA.S_oeis_a226316.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A226316Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X + 8 * X ^ 2)
    (hG : G * (2 + (2) * S) = 3 + (1) * S) :
    (-256 * X + 2304 * X ^ 2 - 4096 * X ^ 3 + 2048 * X ^ 4) * derivative ℚ G + (-256 + 1536 * X - 3072 * X ^ 2 + 2048 * X ^ 3) * G = -256 + 1024 * X - 1536 * X ^ 2 + 1024 * X ^ 3 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have hS2 : S * S = (1 - 8 * X + 8 * (X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (32 * X - 32 * X ^ 2) * G = (4 + 16 * X - 16 * X ^ 2 : ℚ⟦X⟧) + (-4) * S := by
    linear_combination (2 - (2) * S) * hG + (2) * ((2) * G - (1)) * hS
  have hPd : derivative ℚ (1 - 8 * X + 8 * (X * X) : ℚ⟦X⟧) = -8 + 16 * X := by
    simp [Derivation.leibniz, d8]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -8 + 16 * X := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((32 * X - 32 * (X * X) : ℚ⟦X⟧) * G) = (32 - 64 * X) * G + (32 * X - 32 * X ^ 2) * derivative ℚ G := by
    simp [Derivation.leibniz, d32]
    ring
  have hR : derivative ℚ ((4 + 16 * X - 16 * (X * X) : ℚ⟦X⟧) + (-4 : ℚ⟦X⟧) * S) =
      16 - 32 * X + (0) * S + (-4) * derivative ℚ S := by
    simp [Derivation.leibniz, d4, d16]
    ring
  have hk2 : (32 * X - 32 * (X * X) : ℚ⟦X⟧) * G = (4 + 16 * X - 16 * (X * X) : ℚ⟦X⟧) + (-4 : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (32 - 64 * X) * G + (32 * X - 32 * X ^ 2) * derivative ℚ G =
      16 - 32 * X + (0) * S + (-4) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  linear_combination (-4) ^ 2 * S * hdS - 2 * (-4) ^ 2 * derivative ℚ S * hS -
      (2 * (0) * (1 - 8 * X + 8 * X ^ 2) + (-4) * (-8 + 16 * X)) * hk + 2 * (-4) * (1 - 8 * X + 8 * X ^ 2) * hdk

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X + 8 * X ^ 2)
    (hG : G * (2 + (2) * S) = 3 + (1) * S) :
    derivative ℚ G * X * C (-256) + derivative ℚ G * X * X * C 2304 +
      derivative ℚ G * X * X * X * C (-4096) + derivative ℚ G * X * X * X * X * C 2048 +
      G * C (-256) + G * X * C 1536 +
      G * X * X * C (-3072) + G * X * X * X * C 2048 =
      C (-256) + C 1024 * X +
      C (-1536) * X * X + C 1024 * X * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X + 8 * X ^ 2)
    (hG : G * (2 + (2) * S) = 3 + (1) * S) (m : ℕ) :
    (-256) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 2304 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      (-4096) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + 2048 * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-256) * coeff (m + 1 + 1 + 1 + 1) G + 1536 * coeff (m + 1 + 1 + 1) G +
      (-3072) * coeff (m + 1 + 1) G + 2048 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

end A226316Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a226316.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  rw [e1, e2, e3]
  have r := A226316Aux.rel (S) G (by linear_combination hS)
      (by linear_combination hG) m
  push_cast
  linear_combination ((-1 : ℚ) / 256) * r
