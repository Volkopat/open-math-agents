import OMAStatements.S_oeis_a081567
import Mathlib

-- Problem: A081567, a(n) = 2 a(n-1) + b(n) where a(n) = Sum_k C(n,k) 2^(n-k) F(k+1) and
-- b(n) = Sum_k C(n-1,k) F(2k+2).
-- Upstream: formal-conjectures statements/oeis-a081567.lean (declaration OMA.S_oeis_a081567.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)
-- Status: proved here (the stated identity holds).
-- Proof: by Binet's formula and the binomial theorem, sqrt5 a(n) = phi (phi+2)^n - psi (psi+2)^n and
-- sqrt5 b(m+1) = phi^2 (phi^2+1)^m - psi^2 (psi^2+1)^m; since phi^2 + 1 = phi + 2 (and likewise for
-- psi), both sides of the identity agree.

namespace OMA.P_oeis_a081567

open OMA.S_oeis_a081567

theorem A_closed (n : ℕ) : (a n : ℝ) = (Real.goldenRatio * (Real.goldenRatio + 2) ^ n
    - Real.goldenConj * (Real.goldenConj + 2) ^ n) / √5 := by
  unfold a
  push_cast
  simp only [Real.coe_fib_eq]
  rw [add_pow, add_pow, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  generalize Real.goldenRatio = p
  generalize Real.goldenConj = q
  generalize √5 = r
  ring

theorem B_closed (m : ℕ) : (b (m + 1) : ℝ) = (Real.goldenRatio ^ 2 * (Real.goldenRatio ^ 2 + 1) ^ m
    - Real.goldenConj ^ 2 * (Real.goldenConj ^ 2 + 1) ^ m) / √5 := by
  unfold b
  push_cast
  simp only [Real.coe_fib_eq, Nat.add_sub_cancel]
  rw [add_pow, add_pow, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  generalize Real.goldenRatio = p
  generalize Real.goldenConj = q
  generalize √5 = r
  rw [show p ^ (2 * k + 2) = (p ^ 2) ^ k * p ^ 2 by ring, show q ^ (2 * k + 2) = (q ^ 2) ^ k * q ^ 2 by ring]
  ring

theorem main' : ∀ n : ℕ, 1 ≤ n → a n = 2 * a (n - 1) + b n := by
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel]
  apply Nat.cast_injective (R := ℝ)
  push_cast
  rw [A_closed, A_closed, B_closed]
  have hp := Real.goldenRatio_sq
  have hq := Real.goldenConj_sq
  generalize Real.goldenRatio = p at hp ⊢
  generalize Real.goldenConj = q at hq ⊢
  generalize √5 = r
  rw [show p ^ 2 + 1 = p + 2 by linear_combination hp, show q ^ 2 + 1 = q + 2 by linear_combination hq]
  ring

end OMA.P_oeis_a081567

theorem OMA.solution : type_of% @OMA.S_oeis_a081567.main := OMA.P_oeis_a081567.main'
