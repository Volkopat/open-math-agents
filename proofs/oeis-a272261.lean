import OMAStatements.S_oeis_a272261

-- Problem: A272261: Number of one-to-one functions f from [n] to [2n] where f(x) may not be equal to x or to 2n+1-x.
-- Upstream: formal-conjectures statements/oeis-a272261.lean:0 (declaration OMA.S_oeis_a272261.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A272261Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G S : ℚ⟦X⟧)
    (hS : S ^ 2 = 1 - 4 * X)
    (hS0 : constantCoeff S = 1)
    (hG : G * S = (PowerSeries.exp ℚ).subst (S - 1)) :
    (X ^ 2 - 4 * X ^ 3) * derivative ℚ (derivative ℚ G) + (-6 * X ^ 2) * derivative ℚ G + (-4 * X ^ 2) * G =
      0 := by
  have hS0' : constantCoeff (S - 1) = 0 := by simp [hS0]
  have hsub : HasSubst (S - 1) := HasSubst.of_constantCoeff_zero' hS0'
  have hE0 : derivative ℚ ((PowerSeries.exp ℚ).subst (S - 1)) =
      (PowerSeries.exp ℚ).subst (S - 1) * derivative ℚ (S - 1) := by
    rw [derivative_subst hsub, derivative_exp]
  have hd1 : derivative ℚ (S - 1) = derivative ℚ S := by simp
  rw [hd1] at hE0
  have d2 : derivative ℚ (2 : ℚ⟦X⟧) = 0 := dnum 2
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have hSS : derivative ℚ (S * S) = 2 * S * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hS2 : S * S = (1 - 4 * X : ℚ⟦X⟧) := by linear_combination hS
  have hPd : derivative ℚ (1 - 4 * X : ℚ⟦X⟧) = -4 := by
    simp [Derivation.leibniz, d4]
  have h2 : 2 * S * derivative ℚ S = -4 := by rw [← hSS, hS2, hPd]
  have hLg : derivative ℚ (G * S) = derivative ℚ G * S + G * derivative ℚ S := by
    simp [Derivation.leibniz]
    ring
  have hdG : derivative ℚ G * S + G * derivative ℚ S =
      derivative ℚ ((PowerSeries.exp ℚ).subst (S - 1)) := by
    rw [← hLg, hG]
  have hB2 : 2 * derivative ℚ ((PowerSeries.exp ℚ).subst (S - 1)) = -4 * G := by
    linear_combination 2 * hE0 + (-2 * derivative ℚ S) * hG + G * h2
  have hA2 : 2 * ((1 - 4 * X) * derivative ℚ G) =
      4 * G - 4 * (PowerSeries.exp ℚ).subst (S - 1) := by
    linear_combination 2 * S * hdG - 2 * derivative ℚ G * hS - G * h2 + S * hB2 - 4 * hG
  have hL : derivative ℚ (2 * ((1 - 4 * X) * derivative ℚ G)) =
      2 * (1 - 4 * X) * derivative ℚ (derivative ℚ G) - 8 * derivative ℚ G := by
    simp [Derivation.leibniz, d2, d4]
    ring
  have hR : derivative ℚ (4 * G - 4 * (PowerSeries.exp ℚ).subst (S - 1)) =
      4 * derivative ℚ G - 4 * derivative ℚ ((PowerSeries.exp ℚ).subst (S - 1)) := by
    simp [Derivation.leibniz, d4]
  have hdd : 2 * (1 - 4 * X) * derivative ℚ (derivative ℚ G) - 8 * derivative ℚ G =
      4 * derivative ℚ G - 4 * derivative ℚ ((PowerSeries.exp ℚ).subst (S - 1)) := by
    rw [← hL, ← hR, hA2]
  have hc : (2 : ℚ⟦X⟧) ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    rw [cnum, map_zero] at h'
    norm_num at h'
  have hfull : (2 : ℚ⟦X⟧) * ((X ^ 2 - 4 * X ^ 3) * derivative ℚ (derivative ℚ G) +
      (-6 * X ^ 2) * derivative ℚ G + (-4 * X ^ 2) * G) = 0 := by
    linear_combination X ^ 2 * hdd - 2 * X ^ 2 * hB2
  exact (mul_eq_zero.mp hfull).resolve_left hc


set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G S : ℚ⟦X⟧)
    (hS : S ^ 2 = 1 - 4 * X)
    (hS0 : constantCoeff S = 1)
    (hG : G * S = (PowerSeries.exp ℚ).subst (S - 1)) :
    derivative ℚ (derivative ℚ G) * X * X * C 1 + derivative ℚ (derivative ℚ G) * X * X * X * C (-4) +
      derivative ℚ G * X * X * C (-6) + G * X * X * C (-4) =
      0 := by
  have h := key G S hS hS0 hG
  simp only [map_ofNat, map_neg, map_one]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G S : ℚ⟦X⟧)
    (hS : S ^ 2 = 1 - 4 * X)
    (hS0 : constantCoeff S = 1)
    (hG : G * S = (PowerSeries.exp ℚ).subst (S - 1)) (m : ℕ) :
    1 * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + (-4) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1) G +
      (-6) * ((m : ℚ) + 2) * coeff (m + 1 + 1) G + (-4) * coeff (m + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1)) (keyC G S hS hS0 hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G S : ℚ⟦X⟧)
    (hS : S ^ 2 = 1 - 4 * X)
    (hS0 : constantCoeff S = 1)
    (hG : G * S = (PowerSeries.exp ℚ).subst (S - 1)) :
    2 * coeff (0 + 1 + 1) G + (-6) * coeff (0 + 1) G +
      (-4) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1)) (keyC G S hS hS0 hG)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    map_zero, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A272261Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a272261.main := by
  intro S G hS hS0 hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 := ⟨n - 2, by omega⟩
  have e1 : m + 1 + 1 - 1 = m + 1 := rfl
  have e2 : m + 1 + 1 - 2 = m := rfl
  rw [e1, e2]
  have hS0c : PowerSeries.constantCoeff S = 1 := by simpa using hS0
  unfold OMA.S_oeis_a272261.a
  cases m with
  | zero =>
    have r := A272261Aux.relE0 G S hS hS0c hG
    simp only [Nat.factorial_succ, Nat.factorial_zero]
    push_cast
    linear_combination (1 : ℚ) * r
  | succ m =>
    have r := A272261Aux.rel G S hS hS0c hG m
    simp only [Nat.factorial_succ]
    push_cast
    linear_combination (((m : ℚ) + 1) * (m.factorial : ℚ)) * r
