import OMAStatements.S_oeis_a099363
import Mathlib

open PowerSeries

theorem OMA.solution : type_of% @OMA.S_oeis_a099363.main := by
  have hs : HasSubst ((X : ℚ⟦X⟧) ^ 2) := HasSubst.X_pow two_ne_zero
  set c : ℚ⟦X⟧ := catalanSeries.map (Nat.castRingHom ℚ) with hcdef
  have hc : c ^ 2 * X + 1 = c := by
    have h := congrArg (PowerSeries.map (Nat.castRingHom ℚ)) catalanSeries_sq_mul_X_add_one
    simpa [hcdef, map_add, map_mul, map_pow] using h
  set C2 : ℚ⟦X⟧ := OMA.S_oeis_a099363.c2 with hC2def
  have hC2 : C2 = c.subst ((X : ℚ⟦X⟧) ^ 2) := rfl
  have hC2eq : C2 ^ 2 * X ^ 2 + 1 = C2 := by
    have h := congrArg (fun f : ℚ⟦X⟧ => f.subst ((X : ℚ⟦X⟧) ^ 2)) hc
    simp only [subst_add hs, subst_mul hs, subst_pow hs, subst_X hs] at h
    have h1 : (1 : ℚ⟦X⟧).subst ((X : ℚ⟦X⟧) ^ 2) = 1 := by
      rw [← coe_substAlgHom hs, map_one]
    rw [h1, ← hC2] at h
    exact h
  set P : ℚ⟦X⟧ := 1 - X * (X * (C2 + C2)) with hPdef
  have hP2 : P ^ 2 = 1 - 4 * X ^ 2 := by
    rw [hPdef]; linear_combination (4 * X ^ 2) * hC2eq
  set dP := d⁄dX ℚ P with hdP
  have hd : (P + P) * dP = -(8 * X) := by
    have h := congrArg (d⁄dX ℚ) hP2
    have h4 : d⁄dX ℚ (4 : ℚ⟦X⟧) = 0 := by
      rw [show (4 : ℚ⟦X⟧) = C (4 : ℚ) from (map_ofNat C 4).symm]; exact derivative_C
    simp only [Derivation.leibniz_pow, map_sub, Derivation.leibniz, derivative_X,
      smul_eq_mul, derivative_one, h4, nsmul_eq_mul] at h
    norm_num at h
    rw [hdP]; linear_combination h
  have key : dP + dP - 8 * (X * (X * dP)) + 8 * (X * P) = 0 := by
    linear_combination (-2 * dP) * hP2 + P * hd
  have cdP : ∀ k, coeff k dP = coeff (k + 1) P * ((k : ℚ) + 1) := by
    intro k; rw [hdP, coeff_derivative]
  have hrec : ∀ k : ℕ, ((k : ℚ) + 3) * coeff (k + 3) P = 4 * (k : ℚ) * coeff (k + 1) P := by
    intro k
    have h := congrArg (coeff (k + 2)) key
    have e8 : ∀ f : ℚ⟦X⟧, coeff (k + 2) (8 * f) = 8 * coeff (k + 2) f := by
      intro f; rw [show (8 : ℚ⟦X⟧) = C (8 : ℚ) from (map_ofNat C 8).symm, coeff_C_mul]
    rw [map_add, map_sub, e8, e8, map_add, coeff_succ_X_mul, coeff_succ_X_mul,
      coeff_succ_X_mul, cdP, cdP, map_zero] at h
    push_cast at h
    linarith
  have hF : X * (X * ((1 - (1 - X) * C2) + (1 - (1 - X) * C2))) =
      X * (X * (1 + 1)) - ((1 - P) - X * (1 - P)) := by
    rw [hPdef]; ring
  have rel : ∀ n : ℕ, 2 * OMA.S_oeis_a099363.a n = coeff (n + 3) P - coeff (n + 2) P := by
    intro n
    have h := congrArg (coeff (n + 3)) hF
    have e1 : coeff (n + 1) (1 : ℚ⟦X⟧) = 0 := by rw [coeff_one]; simp
    have e2 : coeff (n + 2) (1 : ℚ⟦X⟧) = 0 := by rw [coeff_one]; simp
    have e3 : coeff (n + 3) (1 : ℚ⟦X⟧) = 0 := by rw [coeff_one]; simp
    simp only [OMA.S_oeis_a099363.a, ← hC2def]
    simp only [coeff_succ_X_mul, map_sub, map_add] at h ⊢
    simp only [e1, e2, e3] at h ⊢
    linarith
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [show m + 3 - 1 = m + 2 by omega, show m + 3 - 2 = m + 1 by omega,
    show m + 3 - 3 = m by omega]
  have r0 := rel m
  have r1 := rel (m + 1)
  have r2 := rel (m + 2)
  have r3 := rel (m + 3)
  have q0 := hrec m
  have q1 := hrec (m + 1)
  have q2 := hrec (m + 2)
  have q3 := hrec (m + 3)
  simp only [show m + 1 + 3 = m + 4 by ring, show m + 1 + 2 = m + 3 by ring,
    show m + 2 + 3 = m + 5 by ring, show m + 2 + 2 = m + 4 by ring,
    show m + 3 + 3 = m + 6 by ring, show m + 3 + 2 = m + 5 by ring,
    show m + 1 + 1 = m + 2 by ring, show m + 2 + 1 = m + 3 by ring,
    show m + 3 + 1 = m + 4 by ring] at r1 r2 r3 q1 q2 q3
  push_cast at q1 q2 q3 ⊢
  linear_combination ((m : ℚ) + 6) / 2 * r3 - ((m : ℚ) + 4) / 2 * r2 - 4 * ((m : ℚ) + 3) / 2 * r1
    + 4 * ((m : ℚ) + 1) / 2 * r0 + (1 / 2 : ℚ) * q3 - q2 + (1 / 2 : ℚ) * q1
