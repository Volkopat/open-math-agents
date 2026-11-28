import FormalConjectures.ErdosProblems.«913»

-- Credit: @PetrouilFan
-- Reduction of Erdős 913.  Upstream proves `variants.conditional`: infinitely many primes p
-- with 8p^2 - 1 prime implies the target.  That core is the genuinely open, strictly easier
-- problem (difficulty 47 vs 59), and the transfer is already proved.  Both hypotheses are
-- self-contained; no upstream theorem is referenced by a hypothesis.

namespace OMA.R_Erdos913_erdos_913_R1

-- Genuinely open core: infinitely many primes p with 8p^2 - 1 also prime.
def H1 : Prop := { p : ℕ | p.Prime ∧ (8 * p ^ 2 - 1).Prime }.Infinite

-- Upstream-proved transfer: the core suffices for the target.
def H2 : Prop :=
  ({ p : ℕ | p.Prime ∧ (8 * p ^ 2 - 1).Prime }.Infinite →
    { n | Set.InjOn (n * (n + 1)).factorization (n * (n + 1)).primeFactors }.Infinite)

theorem main : H1 → H2 → type_of% @Erdos913.erdos_913 := by
  intro h1 h2
  exact h2 h1

end OMA.R_Erdos913_erdos_913_R1
