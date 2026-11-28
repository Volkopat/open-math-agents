import Mathlib

/-!
OEIS A193679: Sequence related to discriminant of cyclotomic polynomials A004124.

a(n) = n^phi(n)/abs(discriminant(Phi(n,x))); OEIS gives the equivalent closed form
a(n) = Product_{p prime, p | n} p^(phi(n)/(p-1)) for n >= 2, a(1) = 1, which we use as the definition.

Conjecture (Benedict W. J. Irwin, 2018): the Dirichlet g.f. of log(a(n)) is
-zeta(s-1)*zeta'(s)/zeta(s)^2, i.e. a(n) = exp(Sum_{d|n} Lambda(d)*phi(n/d)), equivalently
a(n) = Product_{d|n} A014963(d)^phi(n/d), where A014963(d) = p if d is a power of a prime p
(d > 1) and 1 otherwise.
-/

namespace OMA.S_oeis_a193679

/-- A193679 via its product formula. -/
def a (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p ^ (Nat.totient n / (p - 1))

/-- A014963: exp(Lambda(d)). -/
def expMangoldt (d : ℕ) : ℕ := if IsPrimePow d then d.minFac else 1

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      a n = ∏ d ∈ n.divisors, expMangoldt d ^ Nat.totient (n / d) := by
  sorry

end OMA.S_oeis_a193679
