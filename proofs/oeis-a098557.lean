import OMAStatements.S_oeis_a098557
import Mathlib

/-!
Credit: @ivillar
Proof: the coefficient of x^m (m <= n) of Sum_{k<=n} x^(2k+1)/(2k+1) is c(m) = 1/m for odd m
and 0 for even m, so the coefficient of x^n of the truncated polynomial is c(n) + c(n-1).
Hence a(2j+1) = (2j+1)!/(2j+1) = (2j)! and a(2j+2) = (2j+2)!/(2j+1) = (2j+2)(2j)!, and the
recurrence -a(n) + a(n-1) + (n-1)(n-3) a(n-2) = 0 is checked separately for odd and even n.
-/

namespace OMAA098557Helpers
open OMA.S_oeis_a098557

/-- c(m) = 1/m for odd m, 0 for even m. -/
noncomputable def cc (m : ℕ) : ℚ := if m % 2 = 1 then ((m : ℚ))⁻¹ else 0

theorem cS (n m : ℕ) (hm : m ≤ n) :
    (∑ k ∈ Finset.range (n + 1),
      (((2 * k + 1 : ℚ)⁻¹) • (Polynomial.X ^ (2 * k + 1)))).coeff m = cc m := by
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_smul, Polynomial.coeff_X_pow, smul_eq_mul, mul_ite, mul_one,
    mul_zero]
  unfold cc
  split_ifs with h
  · obtain ⟨j, rfl⟩ : ∃ j, m = 2 * j + 1 := ⟨m / 2, by omega⟩
    rw [Finset.sum_eq_single j]
    · rw [if_pos rfl]
      push_cast
      ring
    · intro k _ hk
      rw [if_neg (by omega)]
    · intro hj
      exfalso
      simp only [Finset.mem_range] at hj
      omega
  · apply Finset.sum_eq_zero
    intro k _
    rw [if_neg (by omega)]

theorem cP (n : ℕ) : (polyTrunc (n + 1)).coeff (n + 1) = cc (n + 1) + cc n := by
  unfold polyTrunc
  rw [add_mul, one_mul, Polynomial.coeff_add, Polynomial.coeff_X_mul, cS _ _ le_rfl,
    cS _ _ (by omega)]

theorem ao (j : ℕ) : a (2 * j + 1) = ((2 * j).factorial : ℚ) := by
  unfold a
  rw [cP, cc, cc, if_pos (by omega), if_neg (by omega), add_zero, Nat.factorial_succ]
  push_cast
  field_simp

theorem ae (j : ℕ) : a (2 * j + 2) = (2 * (j : ℚ) + 2) * ((2 * j).factorial : ℚ) := by
  unfold a
  rw [show 2 * j + 2 = (2 * j + 1) + 1 by ring, cP, cc, cc, if_neg (by omega),
    if_pos (by omega), zero_add, Nat.factorial_succ, Nat.factorial_succ]
  push_cast
  field_simp
  ring

end OMAA098557Helpers

open OMAA098557Helpers in
theorem OMA.solution : type_of% @OMA.S_oeis_a098557.main := by
  intro n hn
  obtain ⟨m, rfl | rfl⟩ : ∃ m, n = 2 * m + 3 ∨ n = 2 * m + 4 := ⟨(n - 3) / 2, by omega⟩
  · rw [show 2 * m + 3 - 1 = 2 * m + 2 by omega, show 2 * m + 3 - 2 = 2 * m + 1 by omega]
    have h1 : OMA.S_oeis_a098557.a (2 * m + 3) = ((2 * m + 2).factorial : ℚ) := by
      have := ao (m + 1)
      rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring, show 2 * (m + 1) = 2 * m + 2 by ring] at this
      exact this
    rw [h1, ae, ao, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
  · rw [show 2 * m + 4 - 1 = 2 * m + 3 by omega, show 2 * m + 4 - 2 = 2 * m + 2 by omega]
    have h1 : OMA.S_oeis_a098557.a (2 * m + 3) = ((2 * m + 2).factorial : ℚ) := by
      have := ao (m + 1)
      rw [show 2 * (m + 1) + 1 = 2 * m + 3 by ring, show 2 * (m + 1) = 2 * m + 2 by ring] at this
      exact this
    have h2 : OMA.S_oeis_a098557.a (2 * m + 4) =
        (2 * (m : ℚ) + 4) * ((2 * m + 2).factorial : ℚ) := by
      have := ae (m + 1)
      rw [show 2 * (m + 1) + 2 = 2 * m + 4 by ring, show 2 * (m + 1) = 2 * m + 2 by ring] at this
      rw [this]
      push_cast
      ring
    rw [h1, h2, ae, Nat.factorial_succ, Nat.factorial_succ]
    push_cast
    ring
