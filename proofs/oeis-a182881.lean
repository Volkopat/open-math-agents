import OMAStatements.S_oeis_a182881

-- Problem: A182881: Number of (1,1)-steps in all weighted lattice paths in L_n.
-- Upstream: formal-conjectures statements/oeis-a182881.lean:0 (declaration OMA.S_oeis_a182881.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A182881Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) = 2 * X ^ 3 + (0) * S) :
    (4 * X - 8 * X ^ 2 - 4 * X ^ 3 - 8 * X ^ 4 + 4 * X ^ 5) * derivative ℚ G + (-12 + 12 * X - 12 * X ^ 3 + 12 * X ^ 4) * G = 0 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d7 : derivative ℚ (7 : ℚ⟦X⟧) = 0 := dnum 7
  have d9 : derivative ℚ (9 : ℚ⟦X⟧) = 0 := dnum 9
  have d18 : derivative ℚ (18 : ℚ⟦X⟧) = 0 := dnum 18
  have d30 : derivative ℚ (30 : ℚ⟦X⟧) = 0 := dnum 30
  have hS2 : S * S = (1 - 2 * X - 1 * (X * X) - 2 * (X * X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-1 + 6 * X - 9 * X ^ 2 + 2 * X ^ 3 - 18 * X ^ 4 + 30 * X ^ 5 + 7 * X ^ 6 + 30 * X ^ 7 - 18 * X ^ 8 + 2 * X ^ 9 - 9 * X ^ 10 + 6 * X ^ 11 - X ^ 12) * G = (0 : ℚ⟦X⟧) + (-2 * X ^ 3 + 4 * X ^ 4 + 2 * X ^ 5 + 4 * X ^ 6 - 2 * X ^ 7) * S := by
    linear_combination (0 - (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) * hG + (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * ((1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * G - (0)) * hS
  have hPd : derivative ℚ (1 - 2 * X - 1 * (X * X) - 2 * (X * X * X) + 1 * (X * X * X * X) : ℚ⟦X⟧) = -2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 := by
    simp [Derivation.leibniz, d2]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-1 + 6 * X - 9 * (X * X) + 2 * (X * X * X) - 18 * (X * X * X * X) + 30 * (X * X * X * X * X) + 7 * (X * X * X * X * X * X) + 30 * (X * X * X * X * X * X * X) - 18 * (X * X * X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X * X * X) - 9 * (X * X * X * X * X * X * X * X * X * X) + 6 * (X * X * X * X * X * X * X * X * X * X * X) - 1 * (X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (6 - 18 * X + 6 * X ^ 2 - 72 * X ^ 3 + 150 * X ^ 4 + 42 * X ^ 5 + 210 * X ^ 6 - 144 * X ^ 7 + 18 * X ^ 8 - 90 * X ^ 9 + 66 * X ^ 10 - 12 * X ^ 11) * G + (-1 + 6 * X - 9 * X ^ 2 + 2 * X ^ 3 - 18 * X ^ 4 + 30 * X ^ 5 + 7 * X ^ 6 + 30 * X ^ 7 - 18 * X ^ 8 + 2 * X ^ 9 - 9 * X ^ 10 + 6 * X ^ 11 - X ^ 12) * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d6, d7, d9, d18, d30]
    ring
  have hR : derivative ℚ ((0 : ℚ⟦X⟧) + (-2 * (X * X * X) + 4 * (X * X * X * X) + 2 * (X * X * X * X * X) + 4 * (X * X * X * X * X * X) - 2 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * S) =
      0 + (-6 * X ^ 2 + 16 * X ^ 3 + 10 * X ^ 4 + 24 * X ^ 5 - 14 * X ^ 6) * S + (-2 * X ^ 3 + 4 * X ^ 4 + 2 * X ^ 5 + 4 * X ^ 6 - 2 * X ^ 7) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hk2 : (-1 + 6 * X - 9 * (X * X) + 2 * (X * X * X) - 18 * (X * X * X * X) + 30 * (X * X * X * X * X) + 7 * (X * X * X * X * X * X) + 30 * (X * X * X * X * X * X * X) - 18 * (X * X * X * X * X * X * X * X) + 2 * (X * X * X * X * X * X * X * X * X) - 9 * (X * X * X * X * X * X * X * X * X * X) + 6 * (X * X * X * X * X * X * X * X * X * X * X) - 1 * (X * X * X * X * X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (0 : ℚ⟦X⟧) + (-2 * (X * X * X) + 4 * (X * X * X * X) + 2 * (X * X * X * X * X) + 4 * (X * X * X * X * X * X) - 2 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (6 - 18 * X + 6 * X ^ 2 - 72 * X ^ 3 + 150 * X ^ 4 + 42 * X ^ 5 + 210 * X ^ 6 - 144 * X ^ 7 + 18 * X ^ 8 - 90 * X ^ 9 + 66 * X ^ 10 - 12 * X ^ 11) * G + (-1 + 6 * X - 9 * X ^ 2 + 2 * X ^ 3 - 18 * X ^ 4 + 30 * X ^ 5 + 7 * X ^ 6 + 30 * X ^ 7 - 18 * X ^ 8 + 2 * X ^ 9 - 9 * X ^ 10 + 6 * X ^ 11 - X ^ 12) * derivative ℚ G =
      0 + (-6 * X ^ 2 + 16 * X ^ 3 + 10 * X ^ 4 + 24 * X ^ 5 - 14 * X ^ 6) * S + (-2 * X ^ 3 + 4 * X ^ 4 + 2 * X ^ 5 + 4 * X ^ 6 - 2 * X ^ 7) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 2 * ((1 - 8 * X + 20 * X ^ 2 - 16 * X ^ 3 + 26 * X ^ 4 - 88 * X ^ 5 + 48 * X ^ 6 - 24 * X ^ 7 + 163 * X ^ 8 - 24 * X ^ 9 + 48 * X ^ 10 - 88 * X ^ 11 + 26 * X ^ 12 - 16 * X ^ 13 + 20 * X ^ 14 - 8 * X ^ 15 + X ^ 16) * ((4 * X - 8 * X ^ 2 - 4 * X ^ 3 - 8 * X ^ 4 + 4 * X ^ 5) * derivative ℚ G + (-12 + 12 * X - 12 * X ^ 3 + 12 * X ^ 4) * G - (0))) = 0 := by
    linear_combination (-2 * X ^ 3 + 4 * X ^ 4 + 2 * X ^ 5 + 4 * X ^ 6 - 2 * X ^ 7) ^ 2 * S * hdS - 2 * (-2 * X ^ 3 + 4 * X ^ 4 + 2 * X ^ 5 + 4 * X ^ 6 - 2 * X ^ 7) ^ 2 * derivative ℚ S * hS -
      (2 * (-6 * X ^ 2 + 16 * X ^ 3 + 10 * X ^ 4 + 24 * X ^ 5 - 14 * X ^ 6) * (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) + (-2 * X ^ 3 + 4 * X ^ 4 + 2 * X ^ 5 + 4 * X ^ 6 - 2 * X ^ 7) * (-2 - 2 * X - 6 * X ^ 2 + 4 * X ^ 3)) * hk + 2 * (-2 * X ^ 3 + 4 * X ^ 4 + 2 * X ^ 5 + 4 * X ^ 6 - 2 * X ^ 7) * (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 2 ≠ 0 := pow_ne_zero 2 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  have hg : (1 - 8 * X + 20 * X ^ 2 - 16 * X ^ 3 + 26 * X ^ 4 - 88 * X ^ 5 + 48 * X ^ 6 - 24 * X ^ 7 + 163 * X ^ 8 - 24 * X ^ 9 + 48 * X ^ 10 - 88 * X ^ 11 + 26 * X ^ 12 - 16 * X ^ 13 + 20 * X ^ 14 - 8 * X ^ 15 + X ^ 16 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp h1).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) = 2 * X ^ 3 + (0) * S) :
    derivative ℚ G * X * C 4 + derivative ℚ G * X * X * C (-8) +
      derivative ℚ G * X * X * X * C (-4) + derivative ℚ G * X * X * X * X * C (-8) +
      derivative ℚ G * X * X * X * X * X * C 4 + G * C (-12) +
      G * X * C 12 + G * X * X * X * C (-12) +
      G * X * X * X * X * C 12 =
      0 := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) = 2 * X ^ 3 + (0) * S) (m : ℕ) :
    4 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-8) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G +
      (-4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G + (-8) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G +
      4 * ((m : ℚ) + 1) * coeff (m + 1) G + (-12) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      12 * coeff (m + 1 + 1 + 1 + 1) G + (-12) * coeff (m + 1 + 1) G +
      12 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4)
    (hG : G * (0 + (1 - 2 * X - X ^ 2 - 2 * X ^ 3 + X ^ 4) * S) = 2 * X ^ 3 + (0) * S) :
    16 * coeff (0 + 1 + 1 + 1 + 1) G + (-24) * coeff (0 + 1 + 1 + 1) G +
      (-8) * coeff (0 + 1 + 1) G + (-8) * coeff (0 + 1) G +
      (-12) * coeff (0 + 1 + 1 + 1 + 1) G + 12 * coeff (0 + 1 + 1 + 1) G +
      (-12) * coeff (0 + 1) G + 12 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A182881Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a182881.main := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  cases m with
  | zero =>
    have r := A182881Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination ((-1 : ℚ) / 4) * r
  | succ m =>
    have r := A182881Aux.rel (S) G (by linear_combination hS)
        (by linear_combination hG) m
    push_cast
    linear_combination ((-1 : ℚ) / 4) * r
