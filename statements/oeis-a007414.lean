import Mathlib

/-!
# A007414: Largest number not a sum of distinct primes >= prime(n)

Source: https://oeis.org/A007414
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture (Kløve):
Let a(n) be the largest natural number that cannot be expressed as a sum of distinct primes
each >= prime(n), where prime(n) is the n-th prime. Then a(n) ~ 3 * prime(n) as n -> ∞.
-/

namespace OMA.S_oeis_a007414

open Filter

/-- The n-th prime (1-indexed: nthPrime 1 = 2, nthPrime 2 = 3, ...). -/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- Predicate that m is a sum of distinct primes each >= p. -/
def IsSumOfDistinctPrimesGe (p m : ℕ) : Prop :=
  ∃ s : Finset ℕ, (∀ q ∈ s, Nat.Prime q ∧ p ≤ q) ∧ s.sum id = m

/-- Largest natural number not expressible as a sum of distinct primes >= nthPrime(n). -/
noncomputable def a (n : ℕ) : ℕ :=
  sSup {m : ℕ | ¬ IsSumOfDistinctPrimesGe (nthPrime n) m}

/-- Kløve's conjecture: a(n) / (3 * prime(n)) -> 1 as n -> ∞. -/
theorem main :
    Tendsto
      (fun n : ℕ => (a (n + 1) : ℝ) / (3 * (nthPrime (n + 1) : ℝ)))
      atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a007414
