import Mathlib

/-!
# Infinitely Many Primes p Such That p + 2 Has at Most 20 Prime Factors

Source: https://math.stackexchange.com/questions/511808/using-the-brun-sieve-to-show-very-weak-approximation-to-twin-prime-conjecture
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

## Problem Statement
Show that there are infinitely many primes `p` such that `p + 2` is the product
of at most 20 primes (counted with multiplicity).

## Formalization Notes
`Nat.primeFactorsList n` is the list of prime factors of `n` with multiplicity,
so `(p + 2).primeFactorsList.length ≤ 20` expresses that `p + 2` is a product
of at most 20 primes.
-/

namespace OMA.S_mse_511808

theorem main :
    {p : ℕ | p.Prime ∧ (p + 2).primeFactorsList.length ≤ 20}.Infinite := by
  sorry

end OMA.S_mse_511808
