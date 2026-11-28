import Mathlib

/-!
# A087942: Partitions of n into as many primes as n has prime factors

Source: https://oeis.org/A087942
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) is the number of partitions of n into Omega(n) primes, where Omega(n) is
the number of prime factors of n counted with multiplicity.
Conjecture: For m > 1, a(m) = 0 if and only if m is an odd semiprime such that
m - 2 is not prime.
-/

namespace OMA.S_oeis_a087942

/-- `HasPrimePartition m` holds if `m` can be written as a sum of `Ω(m)` primes. -/
def HasPrimePartition (m : ℕ) : Prop :=
  ∃ s : Multiset ℕ, (∀ p ∈ s, p.Prime) ∧ s.card = m.primeFactorsList.length ∧ s.sum = m

theorem main :
    ∀ m : ℕ, 1 < m →
      (¬ HasPrimePartition m ↔ Odd m ∧ m.primeFactorsList.length = 2 ∧ ¬ (m - 2).Prime) := by
  sorry

end OMA.S_oeis_a087942
