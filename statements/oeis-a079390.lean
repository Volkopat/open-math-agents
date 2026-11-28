import Mathlib

/-!
# OEIS A079390: records of lpf(n) lpf(n+1) lpf(n+2) and twin primes

Source: https://oeis.org/A079390
`a(n) = lpf(n) · lpf(n+1) · lpf(n+2)` with `lpf` the least prime factor. Conjecture: for
`n > 2`, `a(n)` is a record value iff `(n, n+2)` is a twin prime pair.

Conventions. A record value is one exceeding all earlier values `a(m)`, `1 ≤ m < n`
(`lpf(1) = 1`, Mathlib's `Nat.minFac 1 = 1`).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a079390

/-- A079390. -/
def a (n : ℕ) : ℕ := n.minFac * (n + 1).minFac * (n + 2).minFac

theorem main :
    ∀ n : ℕ, 2 < n → ((∀ m, 1 ≤ m → m < n → a m < a n) ↔ n.Prime ∧ (n + 2).Prime) := by
  sorry

end OMA.S_oeis_a079390
