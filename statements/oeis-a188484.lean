import Mathlib.NumberTheory.Divisors

namespace OMA.S_oeis_a188484

/-- The abundance of a positive integer `n`: `σ(n) - 2n`, where `σ(n)` is the sum of
positive divisors of `n`. -/
def abundance (n : ℕ) : ℤ :=
  (∑ d ∈ n.divisors, d : ℤ) - 2 * (n : ℤ)

/-- Conjecture (Sidney Kravitz; OEIS A188484 / A188486): No positive integer `n` has
abundance `σ(n) - 2n` equal to an odd perfect square. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → ¬ ∃ k : ℕ, abundance n = ((2 * k + 1 : ℕ) : ℤ) ^ 2 := by
  sorry

end OMA.S_oeis_a188484
