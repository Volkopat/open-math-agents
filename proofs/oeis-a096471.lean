import OMAStatements.S_oeis_a096471

-- Problem: A096471: Number of degree-n permutations with exactly one even cycle.
-- Upstream: formal-conjectures statements/oeis-a096471.lean:0 (declaration OMA.S_oeis_a096471.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A096471Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G U S L : ℚ⟦X⟧)
    (hS : S ^ 2 * (1 - X) = 1 + X)
    (hS0 : constantCoeff S = 1)
    (hL : (1 - X ^ 2) * derivative ℚ L = -(2 * X))
    (hU : U = S * L)
    (hG : 2 * G = -U) :
    (X ^ 5 - 2 * X ^ 7 + X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) + (-3 * X ^ 5 - 14 * X ^ 6 + 4 * X ^ 7 + 14 * X ^ 8 - X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-13 * X ^ 5 + 21 * X ^ 6 + 50 * X ^ 7 - 9 * X ^ 8) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (15 * X ^ 5 + 45 * X ^ 6 - 18 * X ^ 7) * derivative ℚ (derivative ℚ G) + (6 * X ^ 5 - 6 * X ^ 6) * derivative ℚ G =
      0 := by
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d3 : derivative ℚ (3 : ℚ⟦X⟧) = 0 := dnum 3
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d6 : derivative ℚ (6 : ℚ⟦X⟧) = 0 := dnum 6
  have hSS : S * S * (1 - X) = (1 + X : ℚ⟦X⟧) := by linear_combination hS
  have hLS : derivative ℚ (S * S * (1 - X)) = 2 * S * derivative ℚ S * (1 - X) - S * S := by
    simp [Derivation.leibniz]
    ring
  have hRS : derivative ℚ (1 + X : ℚ⟦X⟧) = 1 := by
    simp
  have hdS : 2 * S * derivative ℚ S * (1 - X) - S * S = 1 := by rw [← hLS, hSS, hRS]
  have hSne : S ≠ 0 := by
    intro h
    rw [h, map_zero] at hS0
    norm_num at hS0
  have h2 : (2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    rw [cnum, map_zero] at h'
    norm_num at h'
  have hdU : derivative ℚ U = derivative ℚ S * L + S * derivative ℚ L := by
    rw [hU]
    simp [Derivation.leibniz]
    ring
  have r0_1 : (1 - 1 * (X * X) : ℚ⟦X⟧) * derivative ℚ S =
      (1 : ℚ⟦X⟧) * S := by
    have hSr : 2 * S * ((1 - X ^ 2) * derivative ℚ S - S) = 0 := by
      linear_combination (1 + X) * hdS - hS
    have h := (mul_eq_zero.mp hSr).resolve_left (mul_ne_zero h2 hSne)
    linear_combination h
  have hLr0_2 : derivative ℚ ((1 - 1 * (X * X) : ℚ⟦X⟧) * derivative ℚ S) =
      (-2 * X) * derivative ℚ S + (1 - X ^ 2) * derivative ℚ (derivative ℚ S) := by
    simp [Derivation.leibniz]
    ring
  have hRr0_2 : derivative ℚ ((1 : ℚ⟦X⟧) * S) =
      (0) * S + (1) * derivative ℚ S := by
    simp
  have r0_2 : (-2 * X) * derivative ℚ S + (1 - X ^ 2) * derivative ℚ (derivative ℚ S) =
      (0) * S + (1) * derivative ℚ S := by
    rw [← hLr0_2, ← hRr0_2, r0_1]
  have r0_2p : (-2 * X : ℚ⟦X⟧) * derivative ℚ S + (1 - 1 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S) =
      (0 : ℚ⟦X⟧) * S + (1 : ℚ⟦X⟧) * derivative ℚ S := by linear_combination r0_2
  have hLr0_3 : derivative ℚ ((-2 * X : ℚ⟦X⟧) * derivative ℚ S + (1 - 1 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S)) =
      (-2) * derivative ℚ S + 2 * (-2 * X) * derivative ℚ (derivative ℚ S) + (1 - X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ S)) := by
    simp [Derivation.leibniz, d2]
    ring
  have hRr0_3 : derivative ℚ ((0 : ℚ⟦X⟧) * S + (1 : ℚ⟦X⟧) * derivative ℚ S) =
      (0) * S + 2 * (0) * derivative ℚ S + (1) * derivative ℚ (derivative ℚ S) := by
    simp
  have r0_3 : (-2) * derivative ℚ S + 2 * (-2 * X) * derivative ℚ (derivative ℚ S) + (1 - X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ S)) =
      (0) * S + 2 * (0) * derivative ℚ S + (1) * derivative ℚ (derivative ℚ S) := by
    rw [← hLr0_3, ← hRr0_3, r0_2p]
  have r0_3p : (-2 : ℚ⟦X⟧) * derivative ℚ S + 2 * ((-2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S)) + (1 - 1 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ S)) =
      (0 : ℚ⟦X⟧) * S + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ S) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S) := by linear_combination r0_3
  have hLr0_4 : derivative ℚ ((-2 : ℚ⟦X⟧) * derivative ℚ S + 2 * ((-2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S)) + (1 - 1 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ S))) =
      (0) * derivative ℚ S + 3 * (-2) * derivative ℚ (derivative ℚ S) + 3 * (-2 * X) * derivative ℚ (derivative ℚ (derivative ℚ S)) + (1 - X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S))) := by
    simp [Derivation.leibniz, d2]
    ring
  have hRr0_4 : derivative ℚ ((0 : ℚ⟦X⟧) * S + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ S) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S)) =
      (0) * S + 3 * (0) * derivative ℚ S + 3 * (0) * derivative ℚ (derivative ℚ S) + (1) * derivative ℚ (derivative ℚ (derivative ℚ S)) := by
    simp
  have r0_4 : (0) * derivative ℚ S + 3 * (-2) * derivative ℚ (derivative ℚ S) + 3 * (-2 * X) * derivative ℚ (derivative ℚ (derivative ℚ S)) + (1 - X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S))) =
      (0) * S + 3 * (0) * derivative ℚ S + 3 * (0) * derivative ℚ (derivative ℚ S) + (1) * derivative ℚ (derivative ℚ (derivative ℚ S)) := by
    rw [← hLr0_4, ← hRr0_4, r0_3p]
  have r0_4p : (0 : ℚ⟦X⟧) * derivative ℚ S + 3 * ((-2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S)) + 3 * ((-2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ S))) + (1 - 1 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S))) =
      (0 : ℚ⟦X⟧) * S + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ S) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S)) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ S)) := by linear_combination r0_4
  have hLr0_5 : derivative ℚ ((0 : ℚ⟦X⟧) * derivative ℚ S + 3 * ((-2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S)) + 3 * ((-2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ S))) + (1 - 1 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S)))) =
      (0) * derivative ℚ S + 4 * (0) * derivative ℚ (derivative ℚ S) + 6 * (-2) * derivative ℚ (derivative ℚ (derivative ℚ S)) + 4 * (-2 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S))) + (1 - X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S)))) := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have hRr0_5 : derivative ℚ ((0 : ℚ⟦X⟧) * S + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ S) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S)) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ S))) =
      (0) * S + 4 * (0) * derivative ℚ S + 6 * (0) * derivative ℚ (derivative ℚ S) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ S)) + (1) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S))) := by
    simp
  have r0_5 : (0) * derivative ℚ S + 4 * (0) * derivative ℚ (derivative ℚ S) + 6 * (-2) * derivative ℚ (derivative ℚ (derivative ℚ S)) + 4 * (-2 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S))) + (1 - X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S)))) =
      (0) * S + 4 * (0) * derivative ℚ S + 6 * (0) * derivative ℚ (derivative ℚ S) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ S)) + (1) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S))) := by
    rw [← hLr0_5, ← hRr0_5, r0_4p]
  have r1_1 : (1 - 1 * (X * X) : ℚ⟦X⟧) * derivative ℚ U =
      (-2 * X : ℚ⟦X⟧) * S + (1 : ℚ⟦X⟧) * U := by
    linear_combination (1 - X ^ 2) * hdU + L * r0_1 + S * hL - hU
  have hLr1_2 : derivative ℚ ((1 - 1 * (X * X) : ℚ⟦X⟧) * derivative ℚ U) =
      (-2 * X) * derivative ℚ U + (1 - X ^ 2) * derivative ℚ (derivative ℚ U) := by
    simp [Derivation.leibniz]
    ring
  have hRr1_2 : derivative ℚ ((-2 * X : ℚ⟦X⟧) * S + (1 : ℚ⟦X⟧) * U) =
      (-2) * S + (-2 * X) * derivative ℚ S + (0) * U + (1) * derivative ℚ U := by
    simp [Derivation.leibniz, d2]
    ring
  have r1_2 : (-2 * X) * derivative ℚ U + (1 - X ^ 2) * derivative ℚ (derivative ℚ U) =
      (-2) * S + (-2 * X) * derivative ℚ S + (0) * U + (1) * derivative ℚ U := by
    rw [← hLr1_2, ← hRr1_2, r1_1]
  have r1_2p : (-2 * X : ℚ⟦X⟧) * derivative ℚ U + (1 - 1 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ U) =
      (-2 : ℚ⟦X⟧) * S + (-2 * X : ℚ⟦X⟧) * derivative ℚ S + (0 : ℚ⟦X⟧) * U + (1 : ℚ⟦X⟧) * derivative ℚ U := by linear_combination r1_2
  have hLr1_3 : derivative ℚ ((-2 * X : ℚ⟦X⟧) * derivative ℚ U + (1 - 1 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ U)) =
      (-2) * derivative ℚ U + 2 * (-2 * X) * derivative ℚ (derivative ℚ U) + (1 - X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ U)) := by
    simp [Derivation.leibniz, d2]
    ring
  have hRr1_3 : derivative ℚ ((-2 : ℚ⟦X⟧) * S + (-2 * X : ℚ⟦X⟧) * derivative ℚ S + (0 : ℚ⟦X⟧) * U + (1 : ℚ⟦X⟧) * derivative ℚ U) =
      (0) * S + 2 * (-2) * derivative ℚ S + (-2 * X) * derivative ℚ (derivative ℚ S) + (0) * U + 2 * (0) * derivative ℚ U + (1) * derivative ℚ (derivative ℚ U) := by
    simp [Derivation.leibniz, d2]
    ring
  have r1_3 : (-2) * derivative ℚ U + 2 * (-2 * X) * derivative ℚ (derivative ℚ U) + (1 - X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ U)) =
      (0) * S + 2 * (-2) * derivative ℚ S + (-2 * X) * derivative ℚ (derivative ℚ S) + (0) * U + 2 * (0) * derivative ℚ U + (1) * derivative ℚ (derivative ℚ U) := by
    rw [← hLr1_3, ← hRr1_3, r1_2p]
  have r1_3p : (-2 : ℚ⟦X⟧) * derivative ℚ U + 2 * ((-2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ U)) + (1 - 1 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ U)) =
      (0 : ℚ⟦X⟧) * S + 2 * ((-2 : ℚ⟦X⟧) * derivative ℚ S) + (-2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S) + (0 : ℚ⟦X⟧) * U + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ U) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ U) := by linear_combination r1_3
  have hLr1_4 : derivative ℚ ((-2 : ℚ⟦X⟧) * derivative ℚ U + 2 * ((-2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ U)) + (1 - 1 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ U))) =
      (0) * derivative ℚ U + 3 * (-2) * derivative ℚ (derivative ℚ U) + 3 * (-2 * X) * derivative ℚ (derivative ℚ (derivative ℚ U)) + (1 - X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ U))) := by
    simp [Derivation.leibniz, d2]
    ring
  have hRr1_4 : derivative ℚ ((0 : ℚ⟦X⟧) * S + 2 * ((-2 : ℚ⟦X⟧) * derivative ℚ S) + (-2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S) + (0 : ℚ⟦X⟧) * U + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ U) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ U)) =
      (0) * S + 3 * (0) * derivative ℚ S + 3 * (-2) * derivative ℚ (derivative ℚ S) + (-2 * X) * derivative ℚ (derivative ℚ (derivative ℚ S)) + (0) * U + 3 * (0) * derivative ℚ U + 3 * (0) * derivative ℚ (derivative ℚ U) + (1) * derivative ℚ (derivative ℚ (derivative ℚ U)) := by
    simp [Derivation.leibniz, d2]
    ring
  have r1_4 : (0) * derivative ℚ U + 3 * (-2) * derivative ℚ (derivative ℚ U) + 3 * (-2 * X) * derivative ℚ (derivative ℚ (derivative ℚ U)) + (1 - X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ U))) =
      (0) * S + 3 * (0) * derivative ℚ S + 3 * (-2) * derivative ℚ (derivative ℚ S) + (-2 * X) * derivative ℚ (derivative ℚ (derivative ℚ S)) + (0) * U + 3 * (0) * derivative ℚ U + 3 * (0) * derivative ℚ (derivative ℚ U) + (1) * derivative ℚ (derivative ℚ (derivative ℚ U)) := by
    rw [← hLr1_4, ← hRr1_4, r1_3p]
  have r1_4p : (0 : ℚ⟦X⟧) * derivative ℚ U + 3 * ((-2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ U)) + 3 * ((-2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ U))) + (1 - 1 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ U))) =
      (0 : ℚ⟦X⟧) * S + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ S) + 3 * ((-2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S)) + (-2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ S)) + (0 : ℚ⟦X⟧) * U + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ U) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ U)) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ U)) := by linear_combination r1_4
  have hLr1_5 : derivative ℚ ((0 : ℚ⟦X⟧) * derivative ℚ U + 3 * ((-2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ U)) + 3 * ((-2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ U))) + (1 - 1 * (X * X) : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ U)))) =
      (0) * derivative ℚ U + 4 * (0) * derivative ℚ (derivative ℚ U) + 6 * (-2) * derivative ℚ (derivative ℚ (derivative ℚ U)) + 4 * (-2 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ U))) + (1 - X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ U)))) := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have hRr1_5 : derivative ℚ ((0 : ℚ⟦X⟧) * S + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ S) + 3 * ((-2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S)) + (-2 * X : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ S)) + (0 : ℚ⟦X⟧) * U + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ U) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ U)) + (1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ U))) =
      (0) * S + 4 * (0) * derivative ℚ S + 6 * (0) * derivative ℚ (derivative ℚ S) + 4 * (-2) * derivative ℚ (derivative ℚ (derivative ℚ S)) + (-2 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S))) + (0) * U + 4 * (0) * derivative ℚ U + 6 * (0) * derivative ℚ (derivative ℚ U) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ U)) + (1) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ U))) := by
    simp [Derivation.leibniz, d2, d3]
    ring
  have r1_5 : (0) * derivative ℚ U + 4 * (0) * derivative ℚ (derivative ℚ U) + 6 * (-2) * derivative ℚ (derivative ℚ (derivative ℚ U)) + 4 * (-2 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ U))) + (1 - X ^ 2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ U)))) =
      (0) * S + 4 * (0) * derivative ℚ S + 6 * (0) * derivative ℚ (derivative ℚ S) + 4 * (-2) * derivative ℚ (derivative ℚ (derivative ℚ S)) + (-2 * X) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S))) + (0) * U + 4 * (0) * derivative ℚ U + 6 * (0) * derivative ℚ (derivative ℚ U) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ U)) + (1) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ U))) := by
    rw [← hLr1_5, ← hRr1_5, r1_4p]
  have e0 : (2 : ℚ⟦X⟧) * G =
      (0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * S + (-1 : ℚ⟦X⟧) * U := by linear_combination hG
  have hLe1 : derivative ℚ ((2 : ℚ⟦X⟧) * G) =
      (0) * G + (2) * derivative ℚ G := by
    simp [Derivation.leibniz, d2]
  have hRe1 : derivative ℚ ((0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * S + (-1 : ℚ⟦X⟧) * U) =
      (0) + (0) * S + (0) * derivative ℚ S + (0) * U + (-1) * derivative ℚ U := by
    simp
  have e1 : (0) * G + (2) * derivative ℚ G =
      (0) + (0) * S + (0) * derivative ℚ S + (0) * U + (-1) * derivative ℚ U := by
    rw [← hLe1, ← hRe1, e0]
  have e1p : (0 : ℚ⟦X⟧) * G + (2 : ℚ⟦X⟧) * derivative ℚ G =
      (0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * S + (0 : ℚ⟦X⟧) * derivative ℚ S + (0 : ℚ⟦X⟧) * U + (-1 : ℚ⟦X⟧) * derivative ℚ U := by linear_combination e1
  have hLe2 : derivative ℚ ((0 : ℚ⟦X⟧) * G + (2 : ℚ⟦X⟧) * derivative ℚ G) =
      (0) * G + 2 * (0) * derivative ℚ G + (2) * derivative ℚ (derivative ℚ G) := by
    simp [Derivation.leibniz, d2]
  have hRe2 : derivative ℚ ((0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * S + (0 : ℚ⟦X⟧) * derivative ℚ S + (0 : ℚ⟦X⟧) * U + (-1 : ℚ⟦X⟧) * derivative ℚ U) =
      (0) + (0) * S + 2 * (0) * derivative ℚ S + (0) * derivative ℚ (derivative ℚ S) + (0) * U + 2 * (0) * derivative ℚ U + (-1) * derivative ℚ (derivative ℚ U) := by
    simp
  have e2 : (0) * G + 2 * (0) * derivative ℚ G + (2) * derivative ℚ (derivative ℚ G) =
      (0) + (0) * S + 2 * (0) * derivative ℚ S + (0) * derivative ℚ (derivative ℚ S) + (0) * U + 2 * (0) * derivative ℚ U + (-1) * derivative ℚ (derivative ℚ U) := by
    rw [← hLe2, ← hRe2, e1p]
  have e2p : (0 : ℚ⟦X⟧) * G + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ G) + (2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G) =
      (0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * S + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ S) + (0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S) + (0 : ℚ⟦X⟧) * U + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ U) + (-1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ U) := by linear_combination e2
  have hLe3 : derivative ℚ ((0 : ℚ⟦X⟧) * G + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ G) + (2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) =
      (0) * G + 3 * (0) * derivative ℚ G + 3 * (0) * derivative ℚ (derivative ℚ G) + (2) * derivative ℚ (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d2]
  have hRe3 : derivative ℚ ((0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * S + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ S) + (0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S) + (0 : ℚ⟦X⟧) * U + 2 * ((0 : ℚ⟦X⟧) * derivative ℚ U) + (-1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ U)) =
      (0) + (0) * S + 3 * (0) * derivative ℚ S + 3 * (0) * derivative ℚ (derivative ℚ S) + (0) * derivative ℚ (derivative ℚ (derivative ℚ S)) + (0) * U + 3 * (0) * derivative ℚ U + 3 * (0) * derivative ℚ (derivative ℚ U) + (-1) * derivative ℚ (derivative ℚ (derivative ℚ U)) := by
    simp
  have e3 : (0) * G + 3 * (0) * derivative ℚ G + 3 * (0) * derivative ℚ (derivative ℚ G) + (2) * derivative ℚ (derivative ℚ (derivative ℚ G)) =
      (0) + (0) * S + 3 * (0) * derivative ℚ S + 3 * (0) * derivative ℚ (derivative ℚ S) + (0) * derivative ℚ (derivative ℚ (derivative ℚ S)) + (0) * U + 3 * (0) * derivative ℚ U + 3 * (0) * derivative ℚ (derivative ℚ U) + (-1) * derivative ℚ (derivative ℚ (derivative ℚ U)) := by
    rw [← hLe3, ← hRe3, e2p]
  have e3p : (0 : ℚ⟦X⟧) * G + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ G) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + (2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G)) =
      (0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * S + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ S) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S)) + (0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ S)) + (0 : ℚ⟦X⟧) * U + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ U) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ U)) + (-1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ U)) := by linear_combination e3
  have hLe4 : derivative ℚ ((0 : ℚ⟦X⟧) * G + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ G) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + (2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G))) =
      (0) * G + 4 * (0) * derivative ℚ G + 6 * (0) * derivative ℚ (derivative ℚ G) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) := by
    simp [Derivation.leibniz, d2]
  have hRe4 : derivative ℚ ((0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * S + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ S) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S)) + (0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ S)) + (0 : ℚ⟦X⟧) * U + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ U) + 3 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ U)) + (-1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ U))) =
      (0) + (0) * S + 4 * (0) * derivative ℚ S + 6 * (0) * derivative ℚ (derivative ℚ S) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ S)) + (0) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S))) + (0) * U + 4 * (0) * derivative ℚ U + 6 * (0) * derivative ℚ (derivative ℚ U) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ U)) + (-1) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ U))) := by
    simp
  have e4 : (0) * G + 4 * (0) * derivative ℚ G + 6 * (0) * derivative ℚ (derivative ℚ G) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) =
      (0) + (0) * S + 4 * (0) * derivative ℚ S + 6 * (0) * derivative ℚ (derivative ℚ S) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ S)) + (0) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S))) + (0) * U + 4 * (0) * derivative ℚ U + 6 * (0) * derivative ℚ (derivative ℚ U) + 4 * (0) * derivative ℚ (derivative ℚ (derivative ℚ U)) + (-1) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ U))) := by
    rw [← hLe4, ← hRe4, e3p]
  have e4p : (0 : ℚ⟦X⟧) * G + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ G) + 6 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G))) + (2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) =
      (0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * S + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ S) + 6 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S)) + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ S))) + (0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S))) + (0 : ℚ⟦X⟧) * U + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ U) + 6 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ U)) + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ U))) + (-1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ U))) := by linear_combination e4
  have hLe5 : derivative ℚ ((0 : ℚ⟦X⟧) * G + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ G) + 6 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ G)) + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ G))) + (2 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) =
      (0) * G + 5 * (0) * derivative ℚ G + 10 * (0) * derivative ℚ (derivative ℚ G) + 10 * (0) * derivative ℚ (derivative ℚ (derivative ℚ G)) + 5 * (0) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) := by
    simp [Derivation.leibniz, d2]
  have hRe5 : derivative ℚ ((0 : ℚ⟦X⟧) + (0 : ℚ⟦X⟧) * S + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ S) + 6 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ S)) + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ S))) + (0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S))) + (0 : ℚ⟦X⟧) * U + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ U) + 6 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ U)) + 4 * ((0 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ U))) + (-1 : ℚ⟦X⟧) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ U)))) =
      (0) + (0) * S + 5 * (0) * derivative ℚ S + 10 * (0) * derivative ℚ (derivative ℚ S) + 10 * (0) * derivative ℚ (derivative ℚ (derivative ℚ S)) + 5 * (0) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S))) + (0) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S)))) + (0) * U + 5 * (0) * derivative ℚ U + 10 * (0) * derivative ℚ (derivative ℚ U) + 10 * (0) * derivative ℚ (derivative ℚ (derivative ℚ U)) + 5 * (0) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ U))) + (-1) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ U)))) := by
    simp
  have e5 : (0) * G + 5 * (0) * derivative ℚ G + 10 * (0) * derivative ℚ (derivative ℚ G) + 10 * (0) * derivative ℚ (derivative ℚ (derivative ℚ G)) + 5 * (0) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (2) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) =
      (0) + (0) * S + 5 * (0) * derivative ℚ S + 10 * (0) * derivative ℚ (derivative ℚ S) + 10 * (0) * derivative ℚ (derivative ℚ (derivative ℚ S)) + 5 * (0) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S))) + (0) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ S)))) + (0) * U + 5 * (0) * derivative ℚ U + 10 * (0) * derivative ℚ (derivative ℚ U) + 10 * (0) * derivative ℚ (derivative ℚ (derivative ℚ U)) + 5 * (0) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ U))) + (-1) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ U)))) := by
    rw [← hLe5, ← hRe5, e4p]
  have hfull : (2 : ℚ⟦X⟧) * ((X ^ 5 - 2 * X ^ 7 + X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) + (-3 * X ^ 5 - 14 * X ^ 6 + 4 * X ^ 7 + 14 * X ^ 8 - X ^ 9) * derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-13 * X ^ 5 + 21 * X ^ 6 + 50 * X ^ 7 - 9 * X ^ 8) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (15 * X ^ 5 + 45 * X ^ 6 - 18 * X ^ 7) * derivative ℚ (derivative ℚ G) + (6 * X ^ 5 - 6 * X ^ 6) * derivative ℚ G - (0)) = 0 := by
    linear_combination (X ^ 5 - 2 * X ^ 7 + X ^ 9) * e5 +
      (-3 * X ^ 5 - 14 * X ^ 6 + 4 * X ^ 7 + 14 * X ^ 8 - X ^ 9) * e4 +
      (-13 * X ^ 5 + 21 * X ^ 6 + 50 * X ^ 7 - 9 * X ^ 8) * e3 +
      (15 * X ^ 5 + 45 * X ^ 6 - 18 * X ^ 7) * e2 +
      (6 * X ^ 5 - 6 * X ^ 6) * e1 +
      (-X ^ 5 + X ^ 7) * r1_5 +
      (2 * X ^ 6) * r0_4 +
      (2 * X ^ 5 + 6 * X ^ 6 - X ^ 7) * r1_4 +
      (8 * X ^ 5 - 2 * X ^ 6) * r0_3 +
      (3 * X ^ 5 - 3 * X ^ 6) * r1_3 +
      (-4 * X ^ 5) * r0_2
  have hM0 : (2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    have kc : constantCoeff (2 : ℚ⟦X⟧) = 2 := cnum 2
    simp [kc] at h'
  have h := (mul_eq_zero.mp hfull).resolve_left hM0
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G U S L : ℚ⟦X⟧)
    (hS : S ^ 2 * (1 - X) = 1 + X)
    (hS0 : constantCoeff S = 1)
    (hL : (1 - X ^ 2) * derivative ℚ L = -(2 * X))
    (hU : U = S * L)
    (hG : 2 * G = -U) :
    derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) * X * X * X * X * X * C 1 + derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) * X * X * X * X * X * X * X * C (-2) +
      derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G)))) * X * X * X * X * X * X * X * X * X * C 1 + derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) * X * X * X * X * X * C (-3) +
      derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) * X * X * X * X * X * X * C (-14) + derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) * X * X * X * X * X * X * X * C 4 +
      derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) * X * X * X * X * X * X * X * X * C 14 + derivative ℚ (derivative ℚ (derivative ℚ (derivative ℚ G))) * X * X * X * X * X * X * X * X * X * C (-1) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C (-13) + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C 21 +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * C 50 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * X * C (-9) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * C 15 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C 45 +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * X * C (-18) + derivative ℚ G * X * X * X * X * X * C 6 +
      derivative ℚ G * X * X * X * X * X * X * C (-6) =
      0 := by
  have h := key G U S L hS hS0 hL hU hG
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G U S L : ℚ⟦X⟧)
    (hS : S ^ 2 * (1 - X) = 1 + X)
    (hS0 : constantCoeff S = 1)
    (hL : (1 - X ^ 2) * derivative ℚ L = -(2 * X))
    (hU : U = S * L)
    (hG : 2 * G = -U) (m : ℕ) :
    1 * ((m : ℚ) + 9) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-2) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      1 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-3) * ((m : ℚ) + 8) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-14) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 4 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      14 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-1) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1 + 1) G +
      (-13) * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + 21 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      50 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-9) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      15 * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G + 45 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-18) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G + 6 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-6) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G U S L hS hS0 hL hU hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G U S L : ℚ⟦X⟧)
    (hS : S ^ 2 * (1 - X) = 1 + X)
    (hS0 : constantCoeff S = 1)
    (hL : (1 - X ^ 2) * derivative ℚ L = -(2 * X))
    (hU : U = S * L)
    (hG : 2 * G = -U) :
    120 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-72) * coeff (0 + 1 + 1 + 1 + 1) G +
      (-78) * coeff (0 + 1 + 1 + 1) G + 30 * coeff (0 + 1 + 1) G +
      6 * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G U S L hS hS0 hL hU hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G U S L : ℚ⟦X⟧)
    (hS : S ^ 2 * (1 - X) = 1 + X)
    (hS0 : constantCoeff S = 1)
    (hL : (1 - X ^ 2) * derivative ℚ L = -(2 * X))
    (hU : U = S * L)
    (hG : 2 * G = -U) :
    720 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-360) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-336) * coeff (0 + 1 + 1 + 1 + 1) G + (-312) * coeff (0 + 1 + 1 + 1 + 1) G +
      126 * coeff (0 + 1 + 1 + 1) G + 90 * coeff (0 + 1 + 1 + 1) G +
      90 * coeff (0 + 1 + 1) G + 12 * coeff (0 + 1 + 1) G +
      (-6) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G U S L hS hS0 hL hU hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE2 (G U S L : ℚ⟦X⟧)
    (hS : S ^ 2 * (1 - X) = 1 + X)
    (hS0 : constantCoeff S = 1)
    (hL : (1 - X ^ 2) * derivative ℚ L = -(2 * X))
    (hU : U = S * L)
    (hG : 2 * G = -U) :
    2520 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-240) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      (-1080) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-1680) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      96 * coeff (0 + 1 + 1 + 1 + 1) G + (-780) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      504 * coeff (0 + 1 + 1 + 1 + 1) G + 300 * coeff (0 + 1 + 1 + 1) G +
      180 * coeff (0 + 1 + 1 + 1 + 1) G + 270 * coeff (0 + 1 + 1 + 1) G +
      (-36) * coeff (0 + 1 + 1) G + 18 * coeff (0 + 1 + 1 + 1) G +
      (-12) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G U S L hS hS0 hL hU hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE3 (G U S L : ℚ⟦X⟧)
    (hS : S ^ 2 * (1 - X) = 1 + X)
    (hS0 : constantCoeff S = 1)
    (hL : (1 - X ^ 2) * derivative ℚ L = -(2 * X))
    (hU : U = S * L)
    (hG : 2 * G = -U) :
    6720 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-1440) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      (-2520) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-5040) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G +
      480 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 336 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-1560) * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + 1260 * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      1200 * coeff (0 + 1 + 1 + 1 + 1) G + (-54) * coeff (0 + 1 + 1 + 1) G +
      300 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 540 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-108) * coeff (0 + 1 + 1 + 1) G + 24 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-18) * coeff (0 + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G U S L hS hS0 hL hU hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A096471Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a096471.main := by
  intro S L G hS hS0 _ hL hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 + 1 := ⟨n - 5, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 + 1 - 3 = m + 1 + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 + 1 - 4 = m + 1 := rfl
  have e5 : m + 1 + 1 + 1 + 1 + 1 - 5 = m := rfl
  rw [e1, e2, e3, e4, e5]
  have hS0c : PowerSeries.constantCoeff S = 1 := by simpa using hS0
  unfold OMA.S_oeis_a096471.a
  cases m with
  | zero =>
    have r := A096471Aux.relE0 G (S * L) S L hS hS0c hL rfl hG
    simp only [Nat.factorial_succ, Nat.factorial_zero]
    push_cast
    linear_combination (1 : ℚ) * r
  | succ m =>
    cases m with
    | zero =>
      have r := A096471Aux.relE1 G (S * L) S L hS hS0c hL rfl hG
      simp only [Nat.factorial_succ, Nat.factorial_zero]
      push_cast
      linear_combination (1 : ℚ) * r
    | succ m =>
      cases m with
      | zero =>
        have r := A096471Aux.relE2 G (S * L) S L hS hS0c hL rfl hG
        simp only [Nat.factorial_succ, Nat.factorial_zero]
        push_cast
        linear_combination (2 : ℚ) * r
      | succ m =>
        cases m with
        | zero =>
          have r := A096471Aux.relE3 G (S * L) S L hS hS0c hL rfl hG
          simp only [Nat.factorial_succ, Nat.factorial_zero]
          push_cast
          linear_combination (6 : ℚ) * r
        | succ m =>
          have r := A096471Aux.rel G (S * L) S L hS hS0c hL rfl hG m
          simp only [Nat.factorial_succ]
          push_cast
          linear_combination (((m : ℚ) + 1) * ((m : ℚ) + 2) * ((m : ℚ) + 3) * ((m : ℚ) + 4) * (m.factorial : ℚ)) * r
