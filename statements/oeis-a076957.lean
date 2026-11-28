import Mathlib

/-!
# OEIS A076957: exactly n primes between consecutive squares

Source: https://oeis.org/A076957
`a n` is the smallest `k` such that there are exactly `n` primes strictly between `k²` and
`(k+1)²`. Conjecturally, `a(n)` is undefined for `n = 1` and defined for all `n ≥ 2`.

Conventions. `k ≥ 1`. "Undefined for `n = 1`" means that no interval `(k², (k+1)²)` contains
exactly one prime.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a076957

/-- Number of primes strictly between `k²` and `(k+1)²`. -/
def c (k : ℕ) : ℕ := ((Finset.Ioo (k ^ 2) ((k + 1) ^ 2)).filter Nat.Prime).card

theorem main :
    (¬ ∃ k : ℕ, 1 ≤ k ∧ c k = 1) ∧ ∀ n : ℕ, 2 ≤ n → ∃ k : ℕ, 1 ≤ k ∧ c k = n := by
  sorry

end OMA.S_oeis_a076957
