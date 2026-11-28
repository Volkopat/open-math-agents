import OMAStatements.S_oeis_a187252
import Mathlib

open OMA.S_oeis_a187252 PowerSeries

theorem Estep (G : ℚ⟦X⟧)
    (hG : (4 : ℚ) • (G * (1 - X)) = -((2 : ℚ) • X - 1 + rescale (2 : ℚ) (exp ℚ) + (4 : ℚ) • logOneSub))
    (k : ℕ) : a G (k + 2) - ((k : ℚ) + 2) * a G (k + 1) - ((k + 1).factorial : ℚ) +
      2 ^ (k + 2) / 4 = 0 := by
  have h := congrArg (coeff (k + 2)) hG
  simp [mul_sub, coeff_rescale, coeff_exp, logOneSub, coeff_X, coeff_one] at h
  unfold a
  rw [Nat.factorial_succ (k + 1)] at h ⊢
  push_cast at h ⊢
  have hk : (k : ℚ) + 2 ≠ 0 := by positivity
  have hF : ((k + 1).factorial : ℚ) ≠ 0 := by positivity
  have e1 : ((k : ℚ) + 2) * ((k : ℚ) + 2)⁻¹ = 1 := mul_inv_cancel₀ hk
  have e2 : ((k : ℚ) + 1 + 1) * ((k + 1).factorial : ℚ) *
      (((k : ℚ) + 1 + 1) * ((k + 1).factorial : ℚ))⁻¹ = 1 :=
    mul_inv_cancel₀ (mul_ne_zero (by positivity) hF)
  linear_combination (((k : ℚ) + 2) * ((k + 1).factorial : ℚ) / 4) * h +
    ((k + 1).factorial : ℚ) * e1 - (2 ^ (k + 2) / 4 : ℚ) * e2

theorem OMA.solution : type_of% @OMA.S_oeis_a187252.main := by
  intro G hG n hn
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  have E0 := Estep G hG (k + 3)
  have E1 := Estep G hG (k + 2)
  have E2 := Estep G hG (k + 1)
  have E3 := Estep G hG k
  simp only [show k + 5 - 1 = k + 4 by omega, show k + 5 - 2 = k + 3 by omega,
    show k + 5 - 3 = k + 2 by omega, show k + 5 - 4 = k + 1 by omega,
    show k + 3 + 2 = k + 5 by omega, show k + 3 + 1 = k + 4 by omega,
    show k + 2 + 2 = k + 4 by omega, show k + 2 + 1 = k + 3 by omega,
    show k + 1 + 2 = k + 3 by omega, show k + 1 + 1 = k + 2 by omega] at E0 E1 E2 E3 ⊢
  rw [Nat.factorial_succ (k + 3), Nat.factorial_succ (k + 2), Nat.factorial_succ (k + 1)] at E0
  rw [Nat.factorial_succ (k + 2), Nat.factorial_succ (k + 1)] at E1
  rw [Nat.factorial_succ (k + 1)] at E2
  rw [pow_succ, pow_succ, pow_succ] at E0
  rw [pow_succ, pow_succ] at E1
  rw [pow_succ] at E2
  push_cast at E0 E1 E2 E3 ⊢
  linear_combination E0 + (-3 - ((k : ℚ) + 5)) * E1 + (4 * ((k : ℚ) + 5) - 4) * E2 +
    (12 - 4 * ((k : ℚ) + 5)) * E3
