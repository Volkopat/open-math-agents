import OMAStatements.S_oeis_a114194

-- Problem: A114194: Expansion of 1/(1+x*(2-x)*c(-2*x)), c(x) the g.f. of A000108.
-- Upstream: formal-conjectures statements/oeis-a114194.lean:0 (declaration OMA.S_oeis_a114194.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A114194Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 + 8 * X)
    (hG : G * (2 + X + (2 - X) * S) = 4 + (0) * S) :
    (384 * X + 2368 * X ^ 2 - 5248 * X ^ 3 + 3008 * X ^ 4 - 512 * X ^ 5) * derivative ℚ G + (384 + 512 * X - 4736 * X ^ 2 + 3456 * X ^ 3 - 768 * X ^ 4) * G = 384 - 1024 * X - 128 * X ^ 2 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d24 : derivative ℚ (24 : ℚ⟦X⟧) = 0 := dnum 24
  have d32 : derivative ℚ (32 : ℚ⟦X⟧) = 0 := dnum 32
  have hS2 : S * S = (1 + 8 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-24 * X + 32 * X ^ 2 - 8 * X ^ 3) * G = (8 + 4 * X : ℚ⟦X⟧) + (-8 + 4 * X) * S := by
    linear_combination (2 + X - (2 - X) * S) * hG + (2 - X) * ((2 - X) * G - (0)) * hS
  have hPd : derivative ℚ (1 + 8 * X : ℚ⟦X⟧) = 8 := by
    simp [Derivation.leibniz, d8]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = 8 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-24 * X + 32 * (X * X) - 8 * (X * X * X) : ℚ⟦X⟧) * G) = (-24 + 64 * X - 24 * X ^ 2) * G + (-24 * X + 32 * X ^ 2 - 8 * X ^ 3) * derivative ℚ G := by
    simp [Derivation.leibniz, d8, d24, d32]
    ring
  have hR : derivative ℚ ((8 + 4 * X : ℚ⟦X⟧) + (-8 + 4 * X : ℚ⟦X⟧) * S) =
      4 + (4) * S + (-8 + 4 * X) * derivative ℚ S := by
    simp [Derivation.leibniz, d4, d8]
    ring
  have hk2 : (-24 * X + 32 * (X * X) - 8 * (X * X * X) : ℚ⟦X⟧) * G = (8 + 4 * X : ℚ⟦X⟧) + (-8 + 4 * X : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-24 + 64 * X - 24 * X ^ 2) * G + (-24 * X + 32 * X ^ 2 - 8 * X ^ 3) * derivative ℚ G =
      4 + (4) * S + (-8 + 4 * X) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  linear_combination (-8 + 4 * X) ^ 2 * S * hdS - 2 * (-8 + 4 * X) ^ 2 * derivative ℚ S * hS -
      (2 * (4) * (1 + 8 * X) + (-8 + 4 * X) * (8)) * hk + 2 * (-8 + 4 * X) * (1 + 8 * X) * hdk

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 + 8 * X)
    (hG : G * (2 + X + (2 - X) * S) = 4 + (0) * S) :
    derivative ℚ G * X * C 384 + derivative ℚ G * X * X * C 2368 +
      derivative ℚ G * X * X * X * C (-5248) + derivative ℚ G * X * X * X * X * C 3008 +
      derivative ℚ G * X * X * X * X * X * C (-512) + G * C 384 +
      G * X * C 512 + G * X * X * C (-4736) +
      G * X * X * X * C 3456 + G * X * X * X * X * C (-768) =
      C 384 + C (-1024) * X +
      C (-128) * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 + 8 * X)
    (hG : G * (2 + X + (2 - X) * S) = 4 + (0) * S) (m : ℕ) :
    384 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + 2368 * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-5248) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + 3008 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      (-512) * ((m : ℚ) + 1) * coeff (m + 1) G + 384 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      512 * coeff (m + 1 + 1 + 1 + 1) G + (-4736) * coeff (m + 1 + 1 + 1) G +
      3456 * coeff (m + 1 + 1) G + (-768) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 + 8 * X)
    (hG : G * (2 + X + (2 - X) * S) = 4 + (0) * S) :
    1536 * coeff (0 + 1 + 1 + 1 + 1) G + 7104 * coeff (0 + 1 + 1 + 1) G +
      (-10496) * coeff (0 + 1 + 1) G + 3008 * coeff (0 + 1) G +
      384 * coeff (0 + 1 + 1 + 1 + 1) G + 512 * coeff (0 + 1 + 1 + 1) G +
      (-4736) * coeff (0 + 1 + 1) G + 3456 * coeff (0 + 1) G +
      (-768) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A114194Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a114194.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  cases m with
  | zero =>
    have r := A114194Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination 4 * hG + G * (2 - PowerSeries.X) * hc)
    push_cast
    linear_combination ((1 : ℚ) / 64) * r
  | succ m =>
    have r := A114194Aux.rel (S) G (by linear_combination hS)
        (by linear_combination 4 * hG + G * (2 - PowerSeries.X) * hc) m
    push_cast
    linear_combination ((1 : ℚ) / 64) * r
