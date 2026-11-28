import OMAStatements.S_oeis_a080243
import Mathlib

open PowerSeries

/-- Large Schröder numbers satisfy (n+3) S(n+2) = 3(2n+3) S(n+1) - n S(n). -/
theorem OMA.a080243_large (n : ℕ) :
    ((n : ℤ) + 3) * (Nat.largeSchroder (n + 2) : ℤ) =
      3 * (2 * (n : ℤ) + 3) * (Nat.largeSchroder (n + 1) : ℤ) - (n : ℤ) * (Nat.largeSchroder n : ℤ) := by
  set G : ℤ⟦X⟧ := PowerSeries.map (Nat.castRingHom ℤ) largeSchroderSeries with hGdef
  have hG : G = 1 + X * G + X * G ^ 2 := by
    have h := congrArg (PowerSeries.map (Nat.castRingHom ℤ))
      largeSchroderSeries_eq_one_add_X_mul_largeSchroderSeries_add_X_mul_largeSchroderSeries_sq
    simpa [hGdef, map_add, map_mul, map_pow] using h
  have cG : ∀ k, coeff k G = (Nat.largeSchroder k : ℤ) := by
    intro k; simp [hGdef, coeff_map, coeff_largeSchroderSeries]
  set Q : ℤ⟦X⟧ := 1 - X - X * (G + G) with hQdef
  have hQ2 : Q ^ 2 = 1 - 6 * X + X ^ 2 := by
    rw [hQdef]; linear_combination (-4 * X) * hG
  set dQ := d⁄dX ℤ Q with hdQ
  have hd : (Q + Q) * dQ = 2 * X - 6 := by
    have h := congrArg (d⁄dX ℤ) hQ2
    have h6 : d⁄dX ℤ (6 : ℤ⟦X⟧) = 0 := by
      rw [show (6 : ℤ⟦X⟧) = C (6 : ℤ) by simp]; exact derivative_C
    simp only [Derivation.leibniz_pow, map_add, map_sub, Derivation.leibniz, derivative_X,
      smul_eq_mul, derivative_one, h6, nsmul_eq_mul] at h
    norm_num at h
    rw [hdQ]; linear_combination h
  have key : dQ + dQ - 12 * (X * dQ) + X * (X * (dQ + dQ)) = X * (Q + Q) - 6 * Q := by
    linear_combination (-2 * dQ) * hQ2 + Q * hd
  have cQ : ∀ k, coeff (k + 1) Q = -(if k = 0 then 1 else 0) - 2 * (Nat.largeSchroder k : ℤ) := by
    intro k
    rw [hQdef, map_sub, map_sub, coeff_succ_X_mul, map_add, cG, coeff_one, coeff_X]
    by_cases hk : k = 0
    · subst hk; simp
    · have hk1 : k + 1 ≠ 1 := by omega
      simp only [Nat.add_one_ne_zero, hk, hk1, if_false]
      ring
  have cdQ : ∀ k, coeff k dQ = coeff (k + 1) Q * ((k : ℤ) + 1) := by
    intro k; rw [hdQ, coeff_derivative]
  have h := congrArg (coeff (n + 2)) key
  simp only [map_add, map_sub, coeff_succ_X_mul] at h
  have e12 : coeff (n + 2) (12 * (X * dQ)) = 12 * coeff (n + 1) dQ := by
    rw [show (12 : ℤ⟦X⟧) = C (12 : ℤ) by simp, coeff_C_mul, coeff_succ_X_mul]
  have e6 : coeff (n + 2) (6 * Q) = 6 * coeff (n + 2) Q := by
    rw [show (6 : ℤ⟦X⟧) = C (6 : ℤ) by simp, coeff_C_mul]
  rw [e12, e6, cdQ, cdQ, cdQ, cQ, cQ, cQ] at h
  try simp only [show n + 1 + 1 = n + 2 by ring, show n + 2 + 1 = n + 3 by ring] at h
  have e2 : ¬ (n + 2 = 0) := by omega
  have e1 : ¬ (n + 1 = 0) := by omega
  rw [if_neg e2, if_neg e1] at h
  by_cases hn : n = 0
  · subst hn; simp at h ⊢
  · rw [if_neg hn] at h; push_cast at h ⊢; linarith

theorem OMA.solution : type_of% @OMA.S_oeis_a080243.main := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega]
  simp only [OMA.S_oeis_a080243.a]
  have h3 : (2 * Nat.smallSchroder (m + 2 + 1) : ℤ) = Nat.largeSchroder (m + 2) := by
    exact_mod_cast Nat.two_mul_smallSchroder_succ (by omega)
  have h2 : (2 * Nat.smallSchroder (m + 1 + 1) : ℤ) = Nat.largeSchroder (m + 1) := by
    exact_mod_cast Nat.two_mul_smallSchroder_succ (by omega)
  have hL := OMA.a080243_large m
  have h1 : (m : ℤ) * (2 * (Nat.smallSchroder (m + 1) : ℤ)) = (m : ℤ) * Nat.largeSchroder m := by
    rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp
    · congr 1; exact_mod_cast Nat.two_mul_smallSchroder_succ (by omega)
  have h2E : 2 * (((m : ℤ) + 3) * (Nat.smallSchroder (m + 2 + 1) : ℤ)
      - 3 * (2 * (m : ℤ) + 3) * (Nat.smallSchroder (m + 1 + 1) : ℤ)
      + (m : ℤ) * (Nat.smallSchroder (m + 1) : ℤ)) = 0 := by
    linear_combination ((m : ℤ) + 3) * h3 - 3 * (2 * (m : ℤ) + 3) * h2 + h1 + hL
  have hE : ((m : ℤ) + 3) * (Nat.smallSchroder (m + 2 + 1) : ℤ)
      - 3 * (2 * (m : ℤ) + 3) * (Nat.smallSchroder (m + 1 + 1) : ℤ)
      + (m : ℤ) * (Nat.smallSchroder (m + 1) : ℤ) = 0 := by linarith
  push_cast
  rw [pow_succ, pow_succ]
  linear_combination (-1 : ℤ) ^ m * hE
