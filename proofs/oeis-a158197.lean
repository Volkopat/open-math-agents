import OMAStatements.S_oeis_a158197

-- Problem: A158197: Expansion of (1-x^2*c(x)^4)/(1-4*x*c(x)^2), c(x) the g.f. of A000108.
-- Upstream: formal-conjectures statements/oeis-a158197.lean:0 (declaration OMA.S_oeis_a158197.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Write the generating function as D G = A + B S with polynomials D, A, B and S^2 = P.
Differentiating S^2 = P and D G = A + B S and eliminating S and its derivative gives a first
order linear differential equation c1 G' + c0 G = r with polynomial c1, c0, r.
The recurrence is the coefficient of a power of x in this equation, beyond the degree of r. -/

namespace A158197Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-32 * X ^ 3 + 80 * X ^ 4 + (32 * X ^ 3) * S) = -8 * X ^ 2 + 32 * X ^ 3 + (8 * X ^ 2 - 16 * X ^ 3) * S) :
    (-262144 * X + 5308416 * X ^ 2 - 33423360 * X ^ 3 + 65536000 * X ^ 4) * derivative ℚ G + (-262144 + 3801088 * X - 20971520 * X ^ 2 + 32768000 * X ^ 3) * G = -262144 + 1703936 * X - 2621440 * X ^ 2 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d128 : derivative ℚ (128 : ℚ⟦X⟧) = 0 := dnum 128
  have d512 : derivative ℚ (512 : ℚ⟦X⟧) = 0 := dnum 512
  have d1024 : derivative ℚ (1024 : ℚ⟦X⟧) = 0 := dnum 1024
  have d1280 : derivative ℚ (1280 : ℚ⟦X⟧) = 0 := dnum 1280
  have d6400 : derivative ℚ (6400 : ℚ⟦X⟧) = 0 := dnum 6400
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-1024 * X ^ 7 + 6400 * X ^ 8) * G = (-128 * X ^ 6 + 512 * X ^ 7 : ℚ⟦X⟧) + (128 * X ^ 6 - 1280 * X ^ 7) * S := by
    linear_combination (-32 * X ^ 3 + 80 * X ^ 4 - (32 * X ^ 3) * S) * hG + (32 * X ^ 3) * ((32 * X ^ 3) * G - (8 * X ^ 2 - 16 * X ^ 3)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-1024 * (X * X * X * X * X * X * X) + 6400 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G) = (-7168 * X ^ 6 + 51200 * X ^ 7) * G + (-1024 * X ^ 7 + 6400 * X ^ 8) * derivative ℚ G := by
    simp [Derivation.leibniz, d1024, d6400]
    ring
  have hR : derivative ℚ ((-128 * (X * X * X * X * X * X) + 512 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (128 * (X * X * X * X * X * X) - 1280 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * S) =
      -768 * X ^ 5 + 3584 * X ^ 6 + (768 * X ^ 5 - 8960 * X ^ 6) * S + (128 * X ^ 6 - 1280 * X ^ 7) * derivative ℚ S := by
    simp [Derivation.leibniz, d128, d512, d1280]
    ring
  have hk2 : (-1024 * (X * X * X * X * X * X * X) + 6400 * (X * X * X * X * X * X * X * X) : ℚ⟦X⟧) * G = (-128 * (X * X * X * X * X * X) + 512 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) + (128 * (X * X * X * X * X * X) - 1280 * (X * X * X * X * X * X * X) : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (-7168 * X ^ 6 + 51200 * X ^ 7) * G + (-1024 * X ^ 7 + 6400 * X ^ 8) * derivative ℚ G =
      -768 * X ^ 5 + 3584 * X ^ 6 + (768 * X ^ 5 - 8960 * X ^ 6) * S + (128 * X ^ 6 - 1280 * X ^ 7) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (X : ℚ⟦X⟧) ^ 12 * ((-262144 * X + 5308416 * X ^ 2 - 33423360 * X ^ 3 + 65536000 * X ^ 4) * derivative ℚ G + (-262144 + 3801088 * X - 20971520 * X ^ 2 + 32768000 * X ^ 3) * G - (-262144 + 1703936 * X - 2621440 * X ^ 2)) = 0 := by
    linear_combination (128 * X ^ 6 - 1280 * X ^ 7) ^ 2 * S * hdS - 2 * (128 * X ^ 6 - 1280 * X ^ 7) ^ 2 * derivative ℚ S * hS -
      (2 * (768 * X ^ 5 - 8960 * X ^ 6) * (1 - 4 * X) + (128 * X ^ 6 - 1280 * X ^ 7) * (-4)) * hk + 2 * (128 * X ^ 6 - 1280 * X ^ 7) * (1 - 4 * X) * hdk
  have hX : (X : ℚ⟦X⟧) ^ 12 ≠ 0 := pow_ne_zero 12 X_ne_zero
  have h1 := (mul_eq_zero.mp hfull).resolve_left hX
  linear_combination h1

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-32 * X ^ 3 + 80 * X ^ 4 + (32 * X ^ 3) * S) = -8 * X ^ 2 + 32 * X ^ 3 + (8 * X ^ 2 - 16 * X ^ 3) * S) :
    derivative ℚ G * X * C (-262144) + derivative ℚ G * X * X * C 5308416 +
      derivative ℚ G * X * X * X * C (-33423360) + derivative ℚ G * X * X * X * X * C 65536000 +
      G * C (-262144) + G * X * C 3801088 +
      G * X * X * C (-20971520) + G * X * X * X * C 32768000 =
      C (-262144) + C 1703936 * X +
      C (-2621440) * X * X := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-32 * X ^ 3 + 80 * X ^ 4 + (32 * X ^ 3) * S) = -8 * X ^ 2 + 32 * X ^ 3 + (8 * X ^ 2 - 16 * X ^ 3) * S) (m : ℕ) :
    (-262144) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + 5308416 * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      (-33423360) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + 65536000 * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-262144) * coeff (m + 1 + 1 + 1 + 1) G + 3801088 * coeff (m + 1 + 1 + 1) G +
      (-20971520) * coeff (m + 1 + 1) G + 32768000 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (-32 * X ^ 3 + 80 * X ^ 4 + (32 * X ^ 3) * S) = -8 * X ^ 2 + 32 * X ^ 3 + (8 * X ^ 2 - 16 * X ^ 3) * S) :
    (-786432) * coeff (0 + 1 + 1 + 1) G + 10616832 * coeff (0 + 1 + 1) G +
      (-33423360) * coeff (0 + 1) G + (-262144) * coeff (0 + 1 + 1 + 1) G +
      3801088 * coeff (0 + 1 + 1) G + (-20971520) * coeff (0 + 1) G +
      32768000 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A158197Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a158197.main := by
  intro S c G hS _ hc hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 := ⟨n - 3, by omega⟩
  have e1 : m + 1 + 1 + 1 - 1 = m + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 - 2 = m + 1 := rfl
  have e3 : m + 1 + 1 + 1 - 3 = m := rfl
  rw [e1, e2, e3]
  cases m with
  | zero =>
    have r := A158197Aux.relE0 (S) G (by linear_combination hS)
        (by linear_combination (16 * PowerSeries.X ^ 4) * hG - ((PowerSeries.X ^ 2) + (-16 * PowerSeries.X ^ 3) * G + (-3 * PowerSeries.X ^ 2) * S + (16 * PowerSeries.X ^ 3) * S * G + (3 * PowerSeries.X ^ 2) * S ^ 2 + (-PowerSeries.X ^ 2) * S ^ 3 + (2 * PowerSeries.X ^ 3) * c + (-32 * PowerSeries.X ^ 4) * c * G + (-4 * PowerSeries.X ^ 3) * c * S + (2 * PowerSeries.X ^ 3) * c * S ^ 2 + (4 * PowerSeries.X ^ 4) * c ^ 2 + (-4 * PowerSeries.X ^ 4) * c ^ 2 * S + (8 * PowerSeries.X ^ 5) * c ^ 3) * hc - ((7 * PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3) + (-16 * PowerSeries.X ^ 3) * G + (-4 * PowerSeries.X ^ 2) * S + (PowerSeries.X ^ 2) * S ^ 2) * hS)
    push_cast
    linear_combination ((-1 : ℚ) / 65536) * r
  | succ m =>
    have r := A158197Aux.rel (S) G (by linear_combination hS)
        (by linear_combination (16 * PowerSeries.X ^ 4) * hG - ((PowerSeries.X ^ 2) + (-16 * PowerSeries.X ^ 3) * G + (-3 * PowerSeries.X ^ 2) * S + (16 * PowerSeries.X ^ 3) * S * G + (3 * PowerSeries.X ^ 2) * S ^ 2 + (-PowerSeries.X ^ 2) * S ^ 3 + (2 * PowerSeries.X ^ 3) * c + (-32 * PowerSeries.X ^ 4) * c * G + (-4 * PowerSeries.X ^ 3) * c * S + (2 * PowerSeries.X ^ 3) * c * S ^ 2 + (4 * PowerSeries.X ^ 4) * c ^ 2 + (-4 * PowerSeries.X ^ 4) * c ^ 2 * S + (8 * PowerSeries.X ^ 5) * c ^ 3) * hc - ((7 * PowerSeries.X ^ 2 - 4 * PowerSeries.X ^ 3) + (-16 * PowerSeries.X ^ 3) * G + (-4 * PowerSeries.X ^ 2) * S + (PowerSeries.X ^ 2) * S ^ 2) * hS) m
    push_cast
    linear_combination ((-1 : ℚ) / 65536) * r
