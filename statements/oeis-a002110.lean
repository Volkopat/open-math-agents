import Mathlib

/-!
# A002110: primorials and successive primes with common prime divisors

Source: https://oeis.org/A002110
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Alon Kellner, in A002110): `a(n) = A270592(2n+2) - A270592(2n+1)` for all `n`, where
`a(n)` is the product of the first `n` primes and `A270592` lists, for `n = 0, 1, 2, …`, the
smallest pair of successive primes `p < q` such that `p + 1` and `q + 1` have `n` distinct prime
divisors in common.

Conventions:
* Reading the formula with the listed terms (`2, 3, 3, 5, 23, 29, …`, verified by the source for
  `n ≤ 4`), `A270592(2n+1)` and `A270592(2n+2)` are the two members `p < q` of the `n`-th pair, so
  the conjecture says `q - p = p₁ p₂ ⋯ p_n` for that pair.
* "Have `n` distinct prime divisors in common": exactly `n` primes divide both `p + 1` and `q + 1`.
  "Smallest pair": the one with least `p`. The statement also asserts that the pair exists.
-/

namespace OMA.S_oeis_a002110

/-- The product of the first `n` primes. -/
noncomputable def primorialFirst (n : ℕ) : ℕ := ∏ i ∈ Finset.range n, Nat.nth Nat.Prime i

/-- `p < q` are successive primes and `p + 1`, `q + 1` have exactly `n` common prime divisors. -/
def GoodPair (n p q : ℕ) : Prop :=
  p.Prime ∧ q.Prime ∧ p < q ∧ (∀ r, p < r → r < q → ¬ r.Prime) ∧
    ((p + 1).primeFactors ∩ (q + 1).primeFactors).card = n

theorem main :
    ∀ n : ℕ, ∃ p q : ℕ, GoodPair n p q ∧ (∀ p' q', GoodPair n p' q' → p ≤ p') ∧
      q - p = primorialFirst n := by
  sorry

end OMA.S_oeis_a002110
