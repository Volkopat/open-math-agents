import Mathlib

/-!
# A350072: sigma(n^2) / gcd(sigma(n^2), A003961(n^2)) is never 1 after n = 1

Source: https://oeis.org/A350072

A350072 (Antti Karttunen), offset 1: a(n) = sigma(n^2) / gcd(sigma(n^2), A003961(n^2)), where
A003961 shifts the prime factorization one step towards larger primes and sigma is the sum of
divisors. Conjecture (in the entry): there are no 1's after the initial term.

Conventions:
* `nextPrime p` is the least prime greater than p.
* A003961 is completely multiplicative with A003961(p) = nextPrime(p) for primes p, i.e.
  A003961(m) = ∏_{p^e ∥ m} nextPrime(p)^e (and A003961(1) = 1).
* sigma is Mathlib's `ArithmeticFunction.sigma 1`; `/` is exact division here.
-/

namespace OMA.S_oeis_a350072

/-- The least prime greater than `p`. -/
def nextPrime (p : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (p + 1))

/-- A003961: replace each prime `p` in the factorization by the next prime. -/
def shift (m : ℕ) : ℕ := ∏ p ∈ m.primeFactors, nextPrime p ^ m.factorization p

/-- A350072. -/
def a (n : ℕ) : ℕ :=
  ArithmeticFunction.sigma 1 (n ^ 2) / Nat.gcd (ArithmeticFunction.sigma 1 (n ^ 2)) (shift (n ^ 2))

/-- No term after the first equals `1`. -/
theorem main : ∀ n : ℕ, 1 < n → a n ≠ 1 := by
  sorry

end OMA.S_oeis_a350072
