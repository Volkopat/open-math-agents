import FormalConjectures.Wikipedia.FibonacciPrimes

-- Reduction FibonacciPrimes.fib_primes_infinite.variant.R1
-- Credit: @PetrouilFan
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

namespace OMA.R_FibonacciPrimes_fib_primes_infinite_variant_R1

/-- The "values" phrasing of the conjecture: infinitely many Fibonacci numbers are prime. -/
def H1 : Prop := {n : ℕ | (∃ m : ℕ, m.fib = n) ∧ n.Prime}.Infinite

/-- Growth bound on Fibonacci indices: every index is at most its Fibonacci value plus one. -/
def H2 : Prop := ∀ b : ℕ, b ≤ b.fib + 1

theorem main : H1 → H2 → type_of% @FibonacciPrimes.fib_primes_infinite.variant := by
  intro h1 _h2
  exact (FibonacciPrimes.indices_infinite_iff_fib_primes_infinite).2 h1

end OMA.R_FibonacciPrimes_fib_primes_infinite_variant_R1
