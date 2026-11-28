import Mathlib

/-!
# A278741: Odd numbers k such that tau(k - 1) is prime

Source: https://oeis.org/A278741

Conjecture (OEIS A278741):
Every prime term of A278741 belongs to OEIS A249759 (primes `p` such that `σ(p - 1)`
is prime).

Conventions:
- Offset: `1`; first terms of A278741: `3, 5, 17, 65, 1025, 4097, 65537, 262145, ...`.
- Known prime terms: `3, 5, 17, 65537, ...`, matching the known terms of A249759.
- `tau n = n.divisors.card` is the divisor count function `τ(n)` (A000005), and
  `sigma n = ∑ d ∈ n.divisors, d` is the sum-of-divisors function `σ(n)` (A000203).
-/

namespace OMA.S_oeis_a278741

/-- Number of positive divisors `τ(n)` of `n : ℕ`. -/
def tau (n : ℕ) : ℕ :=
  n.divisors.card

/-- Sum of positive divisors `σ(n)` of `n : ℕ`. -/
def sigma (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

/-- Conjecture: every odd prime `p` such that `τ(p - 1)` is prime also satisfies that
`σ(p - 1)` is prime. -/
theorem main :
    ∀ p : ℕ, Nat.Prime p → Odd p → Nat.Prime (tau (p - 1)) → Nat.Prime (sigma (p - 1)) := by
  sorry

end OMA.S_oeis_a278741
