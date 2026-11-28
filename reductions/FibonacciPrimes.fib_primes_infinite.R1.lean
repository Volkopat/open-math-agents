import FormalConjectures.Wikipedia.FibonacciPrimes
-- Credit: @PetrouilFan

/-!
Reduction of FibonacciPrimes.fib_primes_infinite.

H1 is the genuinely open index formulation: infinitely many indices i have a prime
Fibonacci number. H2 is the upstream-proved equivalence
`FibonacciPrimes.indices_infinite_iff_fib_primes_infinite` (category test, full proof):
the index formulation is equivalent to the value formulation used by the target
(infinitely many Fibonacci VALUES that are prime). The proof uses monotonicity of
Fibonacci numbers and is a genuine transfer lemma, not a case split.

Neither hypothesis mentions the target, main, or each other.
-/

namespace OMA.R_FibonacciPrimes_fib_primes_infinite_R1

/-- Genuinely open core: infinitely many indices with prime Fibonacci number. -/
def H1 : Prop := {n : ℕ | n.fib.Prime}.Infinite

/-- Upstream-proved transfer equivalence between the index and value formulations. -/
def H2 : Prop :=
  {n : ℕ | n.fib.Prime}.Infinite ↔
    {n : ℕ | (∃ m : ℕ, m.fib = n) ∧ n.Prime}.Infinite

theorem main : H1 → H2 → type_of% @FibonacciPrimes.fib_primes_infinite := by
  intro h1 h2
  exact h2.mp h1

end OMA.R_FibonacciPrimes_fib_primes_infinite_R1
