import FormalConjectures.Wikipedia.PrimorialPrime

-- Reduction PrimorialPrime.infinitely_many_primorial_primes.R1
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_PrimorialPrime_infinitely_many_primorial_primes_R1

/-- Infinitely many prime Kummer numbers p_n# - 1 (the negative-sign case). -/
def H1 : Prop := {q : ℕ | PrimorialPrime.IsKummerPrimorialPrime q}.Infinite

/-- Infinitely many prime Euclid numbers p_n# + 1 (the positive-sign case). -/
def H2 : Prop := {n : ℕ | (EuclidNumbers.Euclid n).Prime}.Infinite

theorem main : H1 → H2 → type_of% @PrimorialPrime.infinitely_many_primorial_primes := by
  intro h1 _h2
  exact (PrimorialPrime.isPrimorialPrime_prime_and_infinite_imp).2.2 h1

end OMA.R_PrimorialPrime_infinitely_many_primorial_primes_R1
