import Mathlib

/-!
# Erdős Problem 451
Source: https://www.erdosproblems.com/451 (accessed 2026-11-27).
Credit: @jaredwilder; adapted from the September statement archive.
Erdős conjectures that the least integer n_k > 2k with no prime factor
in (k,2k) in the product of n_k-i for 1 ≤ i ≤ k is subexponential in k
and exceeds every fixed power of k. The latter is now implied by a cited
2026 lower bound; the subexponential upper bound is the remaining question.
The real-exponent formulation below makes both asymptotic claims explicit.
-/
namespace OMA.S_erdos_451

open Filter

def good (k n : ℕ) : Prop :=
  2*k < n ∧ ∀ p : ℕ, p.Prime → k < p → p < 2*k →
    ¬ p ∣ ∏ i ∈ Finset.Icc 1 k, (n-i)

def leastGood (k n : ℕ) : Prop := IsLeast {m | good k m} n

theorem main : ∃ f : ℕ → ℕ,
    (∀ k ≥ 1, leastGood k (f k)) ∧
    (∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in atTop, (f k : ℝ) < Real.exp (ε*k)) ∧
    (∀ d : ℝ, 0 < d → ∀ᶠ k : ℕ in atTop, (k : ℝ)^d < f k) := by
  sorry

end OMA.S_erdos_451
