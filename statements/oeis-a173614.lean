import Mathlib

/-!
# A173614: a(n) = lcm_{p is prime and divisor of n} p-1

Source: https://oeis.org/A173614
Credit: @ivillar

The sequence (offset 2, José María Grau Ribas) is a(n) = lcm{p - 1 : p prime, p | n}.

Conjecture (Velin Yanev, Feb 06 2021): a(n) = A002322(A007947(n)), where A002322 is the
Carmichael function λ (reduced totient: the exponent of the unit group of ℤ/nℤ) and A007947 is
the squarefree kernel rad(n). Mathlib provides both: `ArithmeticFunction.carmichael` and
`UniqueFactorizationMonoid.radical`.
-/

namespace OMA.S_oeis_a173614

/-- a(n) = lcm of p - 1 over the primes p dividing n. -/
def a (n : ℕ) : ℕ := n.primeFactors.lcm (fun p => p - 1)

/-- Yanev's conjecture: a(n) = λ(rad(n)) for every n ≥ 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    a n = ArithmeticFunction.carmichael (UniqueFactorizationMonoid.radical n) := by
  sorry

end OMA.S_oeis_a173614
