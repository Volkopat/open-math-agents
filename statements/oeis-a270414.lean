import Mathlib

/-!
# A270414: Numbers m such that sigma(m - 1) and sigma(phi(m)) are both prime

Source: https://oeis.org/A270414

Conjecture (OEIS A270414):
The sequence consists precisely of `10` together with the terms of OEIS A249759
(primes `p` such that `σ(p - 1)` is prime: `3, 5, 17, 65537, ...`).

Conventions:
- Offset: `1`; known terms: `3, 5, 10, 17, 65537, ...`.
- For `m = 10`, `σ(9) = 13` and `σ(φ(10)) = σ(4) = 7` are both prime.
- For every prime `p`, `φ(p) = p - 1`, so `A249759 ⊆ A270414` automatically; the
  conjecture asserts that `10` is the unique nonprime term.
-/

namespace OMA.S_oeis_a270414

/-- Sum of positive divisors `σ(n)` of `n : ℕ`. -/
def sigma (n : ℕ) : ℕ :=
  ∑ d ∈ n.divisors, d

/-- Conjecture: for `m ≥ 2`, `σ(m - 1)` and `σ(φ(m))` are both prime if and only if
`m = 10` or `m` is a prime with `σ(m - 1)` prime (OEIS A249759). -/
theorem main :
    ∀ m : ℕ, 2 ≤ m →
      (Nat.Prime (sigma (m - 1)) ∧ Nat.Prime (sigma (Nat.totient m))) ↔
        (m = 10 ∨ (Nat.Prime m ∧ Nat.Prime (sigma (m - 1)))) := by
  sorry

end OMA.S_oeis_a270414
