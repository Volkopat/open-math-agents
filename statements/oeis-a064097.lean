import Mathlib

/-!
# OEIS A064097: bounds for a quasi-logarithm

Source: https://oeis.org/A064097
`a` is defined by `a(1) = 0`, `a(p) = 1 + a(p - 1)` for primes `p`, and `a(nm) = a(n) + a(m)`
for `n, m > 1`. Conjecture (Wilson v, 2013): for `n > 1`, `⌊log₂ n⌋ ≤ a(n) < (5/2) log n`.

Conventions. `a` is completely additive on `n ≥ 1`, so it is given by
`a n = ∑_{p} v_p(n) (1 + a(p - 1))`; `main` quantifies over every function satisfying the
defining rules (they determine it uniquely by strong induction).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a064097

open Real

theorem main :
    ∀ a : ℕ → ℕ, a 1 = 0 → (∀ p : ℕ, p.Prime → a p = 1 + a (p - 1)) →
      (∀ n m : ℕ, 1 < n → 1 < m → a (n * m) = a n + a m) →
      ∀ n : ℕ, 1 < n → Nat.log 2 n ≤ a n ∧ (a n : ℝ) < 5 / 2 * log n := by
  sorry

end OMA.S_oeis_a064097
