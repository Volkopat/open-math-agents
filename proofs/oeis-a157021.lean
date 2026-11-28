import OMAStatements.S_oeis_a157021

-- Problem: A157021: a(n)=sum{k=0..floor(n/2), C(n,2k)*A000108(floor(k/2))}. Inverse binomial transform is aeration of doubled Catalan numbers.
-- Upstream: formal-conjectures statements/oeis-a157021.lean:0 (declaration OMA.S_oeis_a157021.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A157021Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X + 6 * X ^ 2 - 4 * X ^ 3 - 3 * X ^ 4)
    (hG : G * (2 * X ^ 4 - 2 * X ^ 5 + (0) * S) = 1 - 4 * X + 7 * X ^ 2 - 6 * X ^ 3 + 2 * X ^ 4 + (-1 + 2 * X - 2 * X ^ 2) * S) :
    (-4 * X + 28 * X ^ 2 - 88 * X ^ 3 + 160 * X ^ 4 - 164 * X ^ 5 + 76 * X ^ 6 + 16 * X ^ 7 - 24 * X ^ 8) * derivative ℚ G + (-16 + 100 * X - 272 * X ^ 2 + 416 * X ^ 3 - 352 * X ^ 4 + 132 * X ^ 5 - 24 * X ^ 7) * G = -16 + 80 * X - 192 * X ^ 2 + 256 * X ^ 3 - 192 * X ^ 4 + 64 * X ^ 5 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have d7 : derivative ℚ (7 : ℚ⟦X⟧) = 0 := dnum 7
  have hS2 : S * S = (1 - 4 * X + 6 * (X * X) - 4 * (X * X * X) - 3 * (X * X * X * X) : ℚ⟦X⟧) := by linear_combination hS
  have hk : (2 * X ^ 4 - 2 * X ^ 5) * G = (1 - 4 * X + 7 * X ^ 2 - 6 * X ^ 3 + 2 * X ^ 4 : ℚ⟦X⟧) + (-1 + 2 * X - 2 * X ^ 2) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 4 * X + 6 * (X * X) - 4 * (X * X * X) - 3 * (X * X * X * X) : ℚ⟦X⟧) = -4 + 12 * X - 12 * X ^ 2 - 12 * X ^ 3 := by
    simp [Derivation.leibniz, d3, d4, d6]
    ring
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 + 12 * X - 12 * X ^ 2 - 12 * X ^ 3 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((2 * (X * X * X * X) - 2 * (X * X * X * X * X) : ℚ⟦X⟧) * G) = (8 * X ^ 3 - 10 * X ^ 4) * G + (2 * X ^ 4 - 2 * X ^ 5) * derivative ℚ G := by
    simp [Derivation.leibniz, d2]
    ring
  have hR : derivative ℚ ((1 - 4 * X + 7 * (X * X) - 6 * (X * X * X) + 2 * (X * X * X * X) : ℚ⟦X⟧) + (-1 + 2 * X - 2 * (X * X) : ℚ⟦X⟧) * S) =
      -4 + 14 * X - 18 * X ^ 2 + 8 * X ^ 3 + (2 - 4 * X) * S + (-1 + 2 * X - 2 * X ^ 2) * derivative ℚ S := by
    simp [Derivation.leibniz, d2, d4, d6, d7]
    ring
  have hk2 : (2 * (X * X * X * X) - 2 * (X * X * X * X * X) : ℚ⟦X⟧) * G = (1 - 4 * X + 7 * (X * X) - 6 * (X * X * X) + 2 * (X * X * X * X) : ℚ⟦X⟧) + (-1 + 2 * X - 2 * (X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (8 * X ^ 3 - 10 * X ^ 4) * G + (2 * X ^ 4 - 2 * X ^ 5) * derivative ℚ G =
      -4 + 14 * X - 18 * X ^ 2 + 8 * X ^ 3 + (2 - 4 * X) * S + (-1 + 2 * X - 2 * X ^ 2) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 3 * ((-4 * X + 28 * X ^ 2 - 88 * X ^ 3 + 160 * X ^ 4 - 164 * X ^ 5 + 76 * X ^ 6 + 16 * X ^ 7 - 24 * X ^ 8) * derivative ℚ G + (-16 + 100 * X - 272 * X ^ 2 + 416 * X ^ 3 - 352 * X ^ 4 + 132 * X ^ 5 - 24 * X ^ 7) * G - (-16 + 80 * X - 192 * X ^ 2 + 256 * X ^ 3 - 192 * X ^ 4 + 64 * X ^ 5)) = 0 := by
    linear_combination (-1 + 2 * X - 2 * X ^ 2) ^ 2 * S * hdS - 2 * (-1 + 2 * X - 2 * X ^ 2) ^ 2 * derivative ℚ S * hS -
      (2 * (2 - 4 * X) * (1 - 4 * X + 6 * X ^ 2 - 4 * X ^ 3 - 3 * X ^ 4) + (-1 + 2 * X - 2 * X ^ 2) * (-4 + 12 * X - 12 * X ^ 2 - 12 * X ^ 3)) * hk + 2 * (-1 + 2 * X - 2 * X ^ 2) * (1 - 4 * X + 6 * X ^ 2 - 4 * X ^ 3 - 3 * X ^ 4) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 3 ≠ 0 := pow_ne_zero 3 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  linear_combination h1

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X + 6 * X ^ 2 - 4 * X ^ 3 - 3 * X ^ 4)
    (hG : G * (2 * X ^ 4 - 2 * X ^ 5 + (0) * S) = 1 - 4 * X + 7 * X ^ 2 - 6 * X ^ 3 + 2 * X ^ 4 + (-1 + 2 * X - 2 * X ^ 2) * S) :
    derivative ℚ G * X * C (-4) + derivative ℚ G * X * X * C 28 +
      derivative ℚ G * X * X * X * C (-88) + derivative ℚ G * X * X * X * X * C 160 +
      derivative ℚ G * X * X * X * X * X * C (-164) + derivative ℚ G * X * X * X * X * X * X * C 76 +
      derivative ℚ G * X * X * X * X * X * X * X * C 16 + derivative ℚ G * X * X * X * X * X * X * X * X * C (-24) +
      G * C (-16) + G * X * C 100 +
      G * X * X * C (-272) + G * X * X * X * C 416 +
      G * X * X * X * X * C (-352) + G * X * X * X * X * X * C 132 +
      G * X * X * X * X * X * X * X * C (-24) =
      C (-16) + C 80 * X +
      C (-192) * X * X + C 256 * X * X * X +
      C (-192) * X * X * X * X + C 64 * X * X * X * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X + 6 * X ^ 2 - 4 * X ^ 3 - 3 * X ^ 4)
    (hG : G * (2 * X ^ 4 - 2 * X ^ 5 + (0) * S) = 1 - 4 * X + 7 * X ^ 2 - 6 * X ^ 3 + 2 * X ^ 4 + (-1 + 2 * X - 2 * X ^ 2) * S) (m : ℕ) :
    (-4) * ((m : ℚ) + 8) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 28 * ((m : ℚ) + 7) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-88) * ((m : ℚ) + 6) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 160 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-164) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 76 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      16 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + (-24) * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-16) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 100 * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-272) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 416 * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-352) * coeff (m + 1 + 1 + 1 + 1) G + 132 * coeff (m + 1 + 1 + 1) G +
      (-24) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X + 6 * X ^ 2 - 4 * X ^ 3 - 3 * X ^ 4)
    (hG : G * (2 * X ^ 4 - 2 * X ^ 5 + (0) * S) = 1 - 4 * X + 7 * X ^ 2 - 6 * X ^ 3 + 2 * X ^ 4 + (-1 + 2 * X - 2 * X ^ 2) * S) :
    (-28) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 168 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-440) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 640 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-492) * coeff (0 + 1 + 1 + 1) G + 152 * coeff (0 + 1 + 1) G +
      16 * coeff (0 + 1) G + (-16) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      100 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-272) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      416 * coeff (0 + 1 + 1 + 1 + 1) G + (-352) * coeff (0 + 1 + 1 + 1) G +
      132 * coeff (0 + 1 + 1) G + (-24) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A157021Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a157021.main := by
  intro S G hS _ hG n hn
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
    have r := A157021Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination ((-1 : ℚ) / 4) * r
  | succ m =>
    have r := A157021Aux.rel (S) G (by linear_combination hS)
        (by linear_combination hG) m
    push_cast
    linear_combination ((-1 : ℚ) / 4) * r
