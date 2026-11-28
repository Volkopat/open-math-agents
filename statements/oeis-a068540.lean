import Mathlib

/-!
# OEIS A068540: Largest k Satisfying phi(k) = bigomega(k) * tau(k)^2

Source: https://oeis.org/A068540
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Consider positive integers $k \ge 1$ such that $\phi(k) = \Omega(k) \cdot \tau(k)^2$,
where $\phi(k)$ is Euler's totient function, $\Omega(k)$ is the number of prime factors
of $k$ counted with multiplicity, and $\tau(k)$ is the number of positive divisors of $k$.

Conjecture: $14137200$ is the largest term of this sequence; that is, no integer
$k > 14137200$ satisfies $\phi(k) = \Omega(k) \cdot \tau(k)^2$.
-/

namespace OMA.S_oeis_a068540

/-- Number of prime factors counted with multiplicity (`Ω`). -/
def bigOmega (k : ℕ) : ℕ :=
  k.primeFactorsList.length

/-- Number of positive divisors (`τ`). -/
def tau (k : ℕ) : ℕ :=
  k.divisors.card

theorem main :
    ∀ k : ℕ, 14137200 < k → Nat.totient k ≠ bigOmega k * tau k ^ 2 := by
  sorry

end OMA.S_oeis_a068540
