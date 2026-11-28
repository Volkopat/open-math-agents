import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.Ring.Periodic
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Real.Basic

namespace OMA.S_mo_60684

/-- A partial sum with periodic integer weights has a numerator with a
prime divisor above any prescribed multiple of the summation length. -/
theorem main :
    ∀ weights : ℕ → ℤ, (∃ period : ℕ, 0 < period ∧ Function.Periodic weights period) →
      ∀ c : ℝ, ∃ n p : ℕ, 2 ≤ n ∧ p.Prime ∧ c * (n : ℝ) < (p : ℝ) ∧
        (p : ℤ) ∣ (∑ i ∈ Finset.Icc 1 n, (weights i : ℚ) / (i : ℚ)).num := by
  sorry

end OMA.S_mo_60684
