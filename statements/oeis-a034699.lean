import Mathlib

/-!
# OEIS A034699 (largest prime power factor): distinct values between consecutive primes

Source: https://oeis.org/A034699
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (first of the entry's conjectures): for all `n` strictly between two consecutive
primes, the values `a(n)` are pairwise different, where `a(n)` is the largest prime power
dividing `n` (`a(1) = 1`).
-/

namespace OMA.S_oeis_a034699

/-- Largest prime power factor of `n` (`1` for `n = 1`). -/
def a (n : ℕ) : ℕ := (n.divisors.filter fun d => IsPrimePow d).sup id ⊔ 1

/-- Distinctness between consecutive primes. -/
theorem main :
    ∀ p q : ℕ, p.Prime → q.Prime → p < q → (∀ r, p < r → r < q → ¬ r.Prime) →
      ∀ m n, p < m → m < q → p < n → n < q → a m = a n → m = n := by
  sorry

end OMA.S_oeis_a034699
