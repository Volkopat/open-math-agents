import OMAStatements.S_oeis_a158196

-- Problem: A158196: Expansion of (1-x^2*c(x)^4)/(1-3*x*c(x)^2), c(x) the g.f. of A000108.
-- Upstream: formal-conjectures statements/oeis-a158196.lean:0 (declaration OMA.S_oeis_a158196.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A158196Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-24 * X ^ 3 + 64 * X ^ 4 + (24 * X ^ 3) * S) = -8 * X ^ 2 + 32 * X ^ 3 + (8 * X ^ 2 - 16 * X ^ 3) * S) :
    (-196608 * X + 3407872 * X ^ 2 - 18874368 * X ^ 3 + 33554432 * X ^ 4) * derivative ℚ G + (-196608 + 2490368 * X - 11534336 * X ^ 2 + 16777216 * X ^ 3) * G = -196608 + 1310720 * X - 2097152 * X ^ 2 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d512 : derivative ℚ (512 : ℚ⟦X⟧) = 0 := dnum 512
  have d768 : derivative ℚ (768 : ℚ⟦X⟧) = 0 := dnum 768
  have d1024 : derivative ℚ (1024 : ℚ⟦X⟧) = 0 := dnum 1024
  have d4096 : derivative ℚ (4096 : ℚ⟦X⟧) = 0 := dnum 4096
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-768 * X ^ 7 + 4096 * X ^ 8) * G = (-128 * X ^ 6 + 512 * X ^ 7 : ℚ⟦X⟧) + (128 * X ^ 6 - 1024 * X ^ 7) * S := by
    linear_combination (-24 * X ^ 3 + 64 * X ^ 4 - (24 * X ^ 3) * S) * hG + (24 * X ^ 3) * ((24 * X ^ 3) * G - (8 * X ^ 2 - 16 * X ^ 3)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-768 * (X * X * X * X * X * X * X) + 4096 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-5376 * X ^ 6 + 32768 * X ^ 7) * G + (-768 * X ^ 7 + 4096 * X ^ 8) * derivative ℚ G := by
    simp [Derivation.leibniz, d768, d4096]
    ring
  have hR : derivative ℚ ((-128 * (X * X * X * X * X * X) + 512 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (128 * (X * X * X * X * X * X) - 1024 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * S) =
      -768 * X ^ 5 + 3584 * X ^ 6 + (768 * X ^ 5 - 7168 * X ^ 6) * S + (128 * X ^ 6 - 1024 * X ^ 7) * derivative ℚ S := by
    simp [Derivation.leibniz, d128, d512, d1024]
    ring
  have hk2 : (-768 * (X * X * X * X * X * X * X) + 4096 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (-128 * (X * X * X * X * X * X) + 512 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (128 * (X * X * X * X * X * X) - 1024 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-5376 * X ^ 6 + 32768 * X ^ 7) * G + (-768 * X ^ 7 + 4096 * X ^ 8) * derivative ℚ G =
      -768 * X ^ 5 + 3584 * X ^ 6 + (768 * X ^ 5 - 7168 * X ^ 6) * S + (128 * X ^ 6 - 1024 * X ^ 7) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 12 * ((-196608 * X + 3407872 * X ^ 2 - 18874368 * X ^ 3 + 33554432 * X ^ 4) * derivative ℚ G + (-196608 + 2490368 * X - 11534336 * X ^ 2 + 16777216 * X ^ 3) * G - (-196608 + 1310720 * X - 2097152 * X ^ 2)) = 0 := by
    linear_combination (128 * X ^ 6 - 1024 * X ^ 7) ^ 2 * S * hdS - 2 * (128 * X ^ 6 - 1024 * X ^ 7) ^ 2 * derivative ℚ S * hS -
      (2 * (768 * X ^ 5 - 7168 * X ^ 6) * (1 - 4 * X) + (128 * X ^ 6 - 1024 * X ^ 7) * (-4)) * hk + 2 * (128 * X ^ 6 - 1024 * X ^ 7) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 12 ≠ 0 := pow_ne_zero 12 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  linear_combination h1

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-24 * X ^ 3 + 64 * X ^ 4 + (24 * X ^ 3) * S) = -8 * X ^ 2 + 32 * X ^ 3 + (8 * X ^ 2 - 16 * X ^ 3) * S) :
    derivative ℚ G * X * C (-196608) + derivative ℚ G * X * X * C 3407872 +
      derivative ℚ G * X * X * X * C (-18874368) + derivative ℚ G * X * X * X * X * C 33554432 +
      G * C (-196608) + G * X * C 2490368 +
      G * X * X * C (-11534336) + G * X * X * X * C 16777216 =
      C (-196608) + C 1310720 * X +
      C (-2097152) * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-24 * X ^ 3 + 64 * X ^ 4 + (24 * X ^ 3) * S) = -8 * X ^ 2 + 32 * X ^ 3 + (8 * X ^ 2 - 16 * X ^ 3) * S) (m : ℕ) :
    (-196608) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 3407872 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      (-18874368) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + 33554432 * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-196608) * coeff (m + 1 + 1 + 1 + 1) G + 2490368 * coeff (m + 1 + 1 + 1) G +
      (-11534336) * coeff (m + 1 + 1) G + 16777216 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-24 * X ^ 3 + 64 * X ^ 4 + (24 * X ^ 3) * S) = -8 * X ^ 2 + 32 * X ^ 3 + (8 * X ^ 2 - 16 * X ^ 3) * S) :
    (-589824) * coeff (0 + 1 + 1 + 1) G + 6815744 * coeff (0 + 1 + 1) G +
      (-18874368) * coeff (0 + 1) G + (-196608) * coeff (0 + 1 + 1 + 1) G +
      2490368 * coeff (0 + 1 + 1) G + (-11534336) * coeff (0 + 1) G +
      16777216 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A158196Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a158196.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  have e3 : m + 1 + 1 + 1 - 3 = m := rfl
  rw [e1, e2, e3]
  cases m with
  | zero =>
    have r := A158196Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (16 * PowerSeries.X ^ 4) * hG - ((PowerSeries.X ^ 2) + (-12 * PowerSeries.X ^ 3) * G + (-3 * PowerSeries.X ^ 2) * S + (12 * PowerSeries.X ^ 3) * S * G + (3 * PowerSeries.X ^ 2) * S ^ 2 + (-PowerSeries.X ^ 2) * S ^ 3 + (2 * PowerSeries.X ^ 3) * c + (-24 * PowerSeries.X ^ 4) * c * G + (-4 * PowerSeries.X ^ 3) * c * S + (2 * PowerSeries.X ^ 3) * c * S ^ 2 + (4 * PowerSeries.X ^ 4) * c ^ 2 + (-4 * PowerSeries.X ^ 4) * c ^ 2 * S + (8 * PowerSeries.X ^ 5) * c ^ 3) * hc - ((7 * PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3) + (-12 * PowerSeries.X ^ 3) * G + (-4 * PowerSeries.X ^ 2) * S + (PowerSeries.X ^ 2) * S ^ 2) * hS)
    push_cast
    linear_combination ((-1 : ℚ) / 65536) * r
  | succ m =>
    have r := A158196Aux.rel (S) G (by linear_combination hS)
        (by linear_combination (16 * PowerSeries.X ^ 4) * hG - ((PowerSeries.X ^ 2) + (-12 * PowerSeries.X ^ 3) * G + (-3 * PowerSeries.X ^ 2) * S + (12 * PowerSeries.X ^ 3) * S * G + (3 * PowerSeries.X ^ 2) * S ^ 2 + (-PowerSeries.X ^ 2) * S ^ 3 + (2 * PowerSeries.X ^ 3) * c + (-24 * PowerSeries.X ^ 4) * c * G + (-4 * PowerSeries.X ^ 3) * c * S + (2 * PowerSeries.X ^ 3) * c * S ^ 2 + (4 * PowerSeries.X ^ 4) * c ^ 2 + (-4 * PowerSeries.X ^ 4) * c ^ 2 * S + (8 * PowerSeries.X ^ 5) * c ^ 3) * hc - ((7 * PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3) + (-12 * PowerSeries.X ^ 3) * G + (-4 * PowerSeries.X ^ 2) * S + (PowerSeries.X ^ 2) * S ^ 2) * hS) m
    push_cast
    linear_combination ((-1 : ℚ) / 65536) * r
