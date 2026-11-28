import OMAStatements.S_oeis_a258490

-- Problem: A258490: Number of words of length 2n such that all letters of the ternary alphabet occur at least once and are introduced in ascending order and which can be built by repeatedly inserting doublets into the initially empty word.
-- Upstream: formal-conjectures statements/oeis-a258490.lean:0 (declaration OMA.S_oeis_a258490.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! Let C = 1/W. The coefficients t(m) of T and c(m) of C satisfy first order recurrences. Multiplying the
defining relation by (1 - 3*T)*C gives 48*(1 - 9*x)*(1 - x)*G as a combination of T and C with polynomial
coefficients, so u(m) = a(m) - 10*a(m-1) + 9*a(m-2) is a combination of t(m), t(m-1), c(m), c(m-1), c(m-2).
The left side of the recurrence is a combination of u(n), ..., u(n-3) with polynomial coefficients, and it
reduces to zero with the recurrences of t and c. -/

namespace A258490AuxT

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X)
    (hG : G * (1 + (0) * S) = 0 + (1) * S) :
    (2 - 16 * X) * derivative ℚ G + (8) * G = 0 := by
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have hS2 : S * S = (1 - 8 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (1) * G = (0 : ℚ⟦X⟧) + (1) * S := by
    linear_combination hG
  have hPd : derivative ℚ (1 - 8 * X : ℚ⟦X⟧) = -8 := by
    simp [Derivation.leibniz, d8]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -8 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((1 : ℚ⟦X⟧) * G) = (0) * G + (1) * derivative ℚ G := by
    simp [Derivation.leibniz]
  have hR : derivative ℚ ((0 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * S) =
      0 + (0) * S + (1) * derivative ℚ S := by
    simp [Derivation.leibniz]
  have hk2 : (1 : ℚ⟦X⟧) * G = (0 : ℚ⟦X⟧) + (1 : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (0) * G + (1) * derivative ℚ G =
      0 + (0) * S + (1) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  linear_combination (1) ^ 2 * S * hdS - 2 * (1) ^ 2 * derivative ℚ S * hS -
      (2 * (0) * (1 - 8 * X) + (1) * (-8)) * hk + 2 * (1) * (1 - 8 * X) * hdk

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X)
    (hG : G * (1 + (0) * S) = 0 + (1) * S) :
    derivative ℚ G * C 2 + derivative ℚ G * X * C (-16) +
      G * C 8 =
      0 := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X)
    (hG : G * (1 + (0) * S) = 0 + (1) * S) (m : ℕ) :
    2 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + (-16) * ((m : ℚ) + 1) * coeff (m + 1) G +
      8 * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 8 * X)
    (hG : G * (1 + (0) * S) = 0 + (1) * S) :
    2 * coeff (0 + 1) G + 8 * coeff (0) G = 0 := by
  have h := congrArg (coeff (0)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h


theorem hrecT : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 8 * X →
    coeff 0 S = 1 →
    G = S →
    ∀ n : ℕ, 1 ≤ n →
      ((n : ℚ)) * coeff n G + (12 - 8 * (n : ℚ)) * coeff (n - 1) G = 0 := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e1 : m + 1 - 1 = m := rfl
  rw [e1]
  cases m with
  | zero =>
    have r := relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination ((1 : ℚ) / 2) * r
  | succ m =>
    have r := rel (S) G (by linear_combination hS)
        (by linear_combination hG) m
    push_cast
    linear_combination ((1 : ℚ) / 2) * r

end A258490AuxT

namespace A258490AuxC

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxHeartbeats 4000000 in
theorem key (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (0 + (1) * S) = 1 + (0) * S) :
    (2 - 8 * X) * derivative ℚ G + (-4) * G = 0 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hk : (-1 + 4 * X) * G = (0 : ℚ⟦X⟧) + (-1) * S := by
    linear_combination (0 - (1) * S) * hG + (1) * ((1) * G - (0)) * hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have hSSd : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdS : 2 * S * derivative ℚ S = -4 := by rw [← hSSd, hS2, hPd]
  have hL : derivative ℚ ((-1 + 4 * X : ℚ⟦X⟧) * G) = (4) * G + (-1 + 4 * X) * derivative ℚ G := by
    simp [Derivation.leibniz, d4]
    ring
  have hR : derivative ℚ ((0 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * S) =
      0 + (0) * S + (-1) * derivative ℚ S := by
    simp [Derivation.leibniz]
  have hk2 : (-1 + 4 * X : ℚ⟦X⟧) * G = (0 : ℚ⟦X⟧) + (-1 : ℚ⟦X⟧) * S := by linear_combination hk
  have hdk : (4) * G + (-1 + 4 * X) * derivative ℚ G =
      0 + (0) * S + (-1) * derivative ℚ S := by
    rw [← hL, ← hR, hk2]
  have hfull : (1 - 4 * X) * ((2 - 8 * X) * derivative ℚ G + (-4) * G - (0)) = 0 := by
    linear_combination (-1) ^ 2 * S * hdS - 2 * (-1) ^ 2 * derivative ℚ S * hS -
      (2 * (0) * (1 - 4 * X) + (-1) * (-4)) * hk + 2 * (-1) * (1 - 4 * X) * hdk
  have hg : (1 - 4 * X : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg (coeff 0) h
    simp at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left hg
  linear_combination h2

set_option maxHeartbeats 4000000 in
theorem keyC (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (0 + (1) * S) = 1 + (0) * S) :
    derivative ℚ G * C 2 + derivative ℚ G * X * C (-8) +
      G * C (-4) =
      0 := by
  have h := key S G hS hG
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem rel (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (0 + (1) * S) = 1 + (0) * S) (m : ℕ) :
    2 * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + (-8) * ((m : ℚ) + 1) * coeff (m + 1) G +
      (-4) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem relE0 (S G : ℚ⟦X⟧) (hS : S ^ 2 = 1 - 4 * X)
    (hG : G * (0 + (1) * S) = 1 + (0) * S) :
    2 * coeff (0 + 1) G + (-4) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0)) (keyC S G hS hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h


theorem hrecC : ∀ S G : ℚ⟦X⟧, S ^ 2 = 1 - 4 * X →
    coeff 0 S = 1 →
    G * S = 1 →
    ∀ n : ℕ, 1 ≤ n →
      ((n : ℚ)) * coeff n G + (2 - 4 * (n : ℚ)) * coeff (n - 1) G = 0 := by
  intro S G hS _ hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have e1 : m + 1 - 1 = m := rfl
  rw [e1]
  cases m with
  | zero =>
    have r := relE0 (S) G (by linear_combination hS)
        (by linear_combination hG)
    push_cast
    linear_combination ((1 : ℚ) / 2) * r
  | succ m =>
    have r := rel (S) G (by linear_combination hS)
        (by linear_combination hG) m
    push_cast
    linear_combination ((1 : ℚ) / 2) * r

end A258490AuxC

namespace A258490Aux

open PowerSeries

set_option maxHeartbeats 4000000 in
theorem relC (T W Cc G : ℚ⟦X⟧) (hT : T ^ 2 = 1 - 8 * X)
    (hG : 6 * (1 + 3 * T) * W * (1 - X) * G = 4 * W * (1 - X) - 3 * (1 + 3 * T) * (1 - X) + 3 * (1 + 3 * T) * W - (1 + 3 * T) * W * (1 - X))
    (hC : Cc * W = 1) :
    G * C 48 + G * X * C (-480) + G * X * X * C 432 =
      T * C 12 + T * X * C (-12) + Cc * C (-24) + Cc * X * C 240 + Cc * X * X * C (-216) +
        (C 12 + C (-132) * X + C (-72) * X * X) := by
  have h : 48 * (1 - 9 * X) * (1 - X) * G =
      -4 * (1 - X) * (1 - 3 * T) - 24 * (1 - 9 * X) * (1 - X) * Cc + 24 * (1 - 9 * X) -
        8 * (1 - 9 * X) * (1 - X) := by
    linear_combination (-(1 - 3 * T) * Cc) * hG +
      (18 - 27 * Cc - 54 * G + 9 * X + 27 * X * Cc + 54 * X * G) * hT +
      (-6 + 12 * T + 18 * T ^ 2 + 6 * G - 54 * G * T ^ 2 + 3 * X - 12 * X * T + 9 * X * T ^ 2 - 6 * X * G +
        54 * X * G * T ^ 2) * hC
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxHeartbeats 4000000 in
theorem uform (T W Cc G : ℚ⟦X⟧) (hT : T ^ 2 = 1 - 8 * X)
    (hG : 6 * (1 + 3 * T) * W * (1 - X) * G = 4 * W * (1 - X) - 3 * (1 + 3 * T) * (1 - X) + 3 * (1 + 3 * T) * W - (1 + 3 * T) * W * (1 - X))
    (hC : Cc * W = 1) (k : ℕ) :
    48 * coeff (k + 1 + 1 + 1) G + (-480) * coeff (k + 1 + 1) G + 432 * coeff (k + 1) G =
      12 * coeff (k + 1 + 1 + 1) T + (-12) * coeff (k + 1 + 1) T + (-24) * coeff (k + 1 + 1 + 1) Cc +
        240 * coeff (k + 1 + 1) Cc + (-216) * coeff (k + 1) Cc := by
  have h := congrArg (coeff (k + 1 + 1 + 1)) (relC T W Cc G hT hG hC)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C,
    Nat.add_one_ne_zero, ↓reduceIte] at h
  linear_combination h

end A258490Aux

set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a258490.main := by
  intro T W G hT hT0 hW hW0 hG n hn
  have hc : PowerSeries.constantCoeff W ≠ 0 := by
    have h : PowerSeries.constantCoeff W = 1 := by simpa using hW0
    rw [h]
    exact one_ne_zero
  obtain ⟨Cc, hC⟩ : ∃ Cc : PowerSeries ℚ, Cc * W = 1 := ⟨W⁻¹, PowerSeries.inv_mul_cancel W hc⟩
  have hrt := A258490AuxT.hrecT T T hT hT0 rfl
  have hrc := A258490AuxC.hrecC W Cc hW hW0 hC
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 8 := ⟨n - 8, by omega⟩
  rw [show j + 8 - 1 = j + 7 from rfl, show j + 8 - 2 = j + 6 from rfl, show j + 8 - 3 = j + 5 from rfl,
    show j + 8 - 4 = j + 4 from rfl, show j + 8 - 5 = j + 3 from rfl]
  have u0 := A258490Aux.uform T W Cc G hT hG hC (j + 5)
  have u1 := A258490Aux.uform T W Cc G hT hG hC (j + 4)
  have u2 := A258490Aux.uform T W Cc G hT hG hC (j + 3)
  have u3 := A258490Aux.uform T W Cc G hT hG hC (j + 2)
  have t0 := hrt (j + 8) (by omega)
  have t1 := hrt (j + 7) (by omega)
  have t2 := hrt (j + 6) (by omega)
  have t3 := hrt (j + 5) (by omega)
  have c0 := hrc (j + 8) (by omega)
  have c1 := hrc (j + 7) (by omega)
  have c2 := hrc (j + 6) (by omega)
  have c3 := hrc (j + 5) (by omega)
  have c4 := hrc (j + 4) (by omega)
  rw [show j + 8 - 1 = j + 7 from rfl] at t0
  rw [show j + 7 - 1 = j + 6 from rfl] at t1
  rw [show j + 6 - 1 = j + 5 from rfl] at t2
  rw [show j + 5 - 1 = j + 4 from rfl] at t3
  rw [show j + 8 - 1 = j + 7 from rfl] at c0
  rw [show j + 7 - 1 = j + 6 from rfl] at c1
  rw [show j + 6 - 1 = j + 5 from rfl] at c2
  rw [show j + 5 - 1 = j + 4 from rfl] at c3
  rw [show j + 4 - 1 = j + 3 from rfl] at c4
  simp only [Nat.add_assoc, Nat.reduceAdd] at u0 u1 u2 u3
  push_cast at t0 t1 t2 t3 c0 c1 c2 c3 c4 ⊢
  linear_combination (644812 * ((j : ℚ) + 8) - 832128 * ((j : ℚ) + 8) ^ 2 + 187316 * ((j : ℚ) + 8) ^ 3) / 48 * u0 +
    (19821114 - 35806753 * ((j : ℚ) + 8) + 18978150 * ((j : ℚ) + 8) ^ 2 - 2992511 * ((j : ℚ) + 8) ^ 3) / 48 * u1 +
    (-306501132 + 343866518 * ((j : ℚ) + 8) - 125484666 * ((j : ℚ) + 8) ^ 2 + 14930740 * ((j : ℚ) + 8) ^ 3) / 48 * u2 +
    (958545504 - 862218632 * ((j : ℚ) + 8) + 251508096 * ((j : ℚ) + 8) ^ 2 - 23831008 * ((j : ℚ) + 8) ^ 3) / 48 * u3 +
    (644812 - 832128 * ((j : ℚ) + 8) + 187316 * ((j : ℚ) + 8) ^ 2) / 4 * t0 + (-12083370 + 9224163 * ((j : ℚ) + 8) - 1681299 * ((j : ℚ) + 8) ^ 2) / 4 * t1 +
    (42327423 - 28097814 * ((j : ℚ) + 8) + 4472859 * ((j : ℚ) + 8) ^ 2) / 4 * t2 + (-26626264 + 18033570 * ((j : ℚ) + 8) - 2978876 * ((j : ℚ) + 8) ^ 2) / 4 * t3 +
    (-(644812 - 832128 * ((j : ℚ) + 8) + 187316 * ((j : ℚ) + 8) ^ 2)) / 2 * c0 + (-(-18531490 + 19479879 * ((j : ℚ) + 8) - 4116407 * ((j : ℚ) + 8) ^ 2)) / 2 * c1 +
    (-(196761666 - 159985228 * ((j : ℚ) + 8) + 30076066 * ((j : ℚ) + 8) ^ 2)) / 2 * c2 + (-(-744776730 + 497156305 * ((j : ℚ) + 8) - 79766743 * ((j : ℚ) + 8) ^ 2)) / 2 * c3 +
    (-(479272752 - 324604260 * ((j : ℚ) + 8) + 53619768 * ((j : ℚ) + 8) ^ 2)) / 2 * c4
