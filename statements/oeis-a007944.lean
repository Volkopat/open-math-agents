import Mathlib

/-!
# A007944: Largest even k such that 6, 8, ..., k are sums of 2 of the first n odd primes

Source: https://oeis.org/A007944
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
Let a(n) be the largest even integer k such that every even integer in [6, k] is a sum of
two of the first n odd primes. On the Goldbach conjecture,
  a(n) >= prime(n + 1) + 3
for all n >= 1, where prime(n + 1) is the n-th odd prime (3, 5, 7, ...).
-/

namespace OMA.S_oeis_a007944

/-- The first n odd primes: {prime(2), ..., prime(n+1)} = {3, 5, ..., Nat.nth Prime n}. -/
noncomputable def firstNOddPrimes (n : ℕ) : Finset ℕ :=
  (Finset.range n).image (fun i => Nat.nth Nat.Prime (i + 1))

/-- Predicate that m is a sum of two of the first n odd primes. -/
def IsSumOfTwoFirstOddPrimes (n m : ℕ) : Prop :=
  ∃ p ∈ firstNOddPrimes n, ∃ q ∈ firstNOddPrimes n, p + q = m

/-- Largest even k such that every even m with 6 <= m <= k is a sum of 2 of the first n odd primes. -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {k : ℕ | Even k ∧ ∀ m : ℕ, 6 ≤ m → m ≤ k → Even m → IsSumOfTwoFirstOddPrimes n m}

/-- Conjectured lower bound (implied by Goldbach's conjecture): a(n) >= prime(n + 1) + 3. -/
theorem main : ∀ n : ℕ, 1 ≤ n → Nat.nth Nat.Prime n + 3 ≤ a n := by
  sorry

end OMA.S_oeis_a007944
