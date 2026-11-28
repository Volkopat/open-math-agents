import Mathlib

/-!
# Infinitely many primes adjacent to a highly composite number?

Source: https://math.stackexchange.com/questions/4877902

A highly composite number is a positive integer with more divisors than every smaller positive
integer (`1, 2, 4, 6, 12, 24, 36, 48, 60, 120, …`). Many of them are next to a prime, e.g.
`60 ± 1` are both prime. Are there infinitely many primes that are a highly composite number
plus or minus `1`?

Formalization notes:
* `main` states the question in its "yes" reading: infinitely many primes `p` have `p - 1` or
  `p + 1` highly composite (natural subtraction is harmless since `p ≥ 2`). This is equivalent
  to infinitely many highly composite `n` having `n - 1` or `n + 1` prime, the body's phrasing.
* The divisor count is `n.divisors.card`.
-/

namespace OMA.S_mse_4877902

/-- `n` is highly composite: `n > 0` and every smaller positive integer has fewer divisors. -/
def IsHighlyComposite (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n → m.divisors.card < n.divisors.card

/-- Are there infinitely many primes `p` with `p - 1` or `p + 1` highly composite? -/
theorem main :
    Set.Infinite {p : ℕ | p.Prime ∧ (IsHighlyComposite (p - 1) ∨ IsHighlyComposite (p + 1))} := by
  sorry

end OMA.S_mse_4877902
