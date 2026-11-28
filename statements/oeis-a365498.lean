import Mathlib

/-!
OEIS A365498: Dirichlet g.f.: zeta(s) * Product_{p prime} (1 + 1/p^s - 1/p^(3*s)).

The Euler product Product_{p prime} (1 + p^(-s) - p^(-3s)) is the Dirichlet series of the
multiplicative function g with g(p) = 1, g(p^3) = -1 and g(p^e) = 0 for e = 2 or e >= 4,
so a(n) = Sum_{d|n} g(d).

Conjecture (Sequence Machine, reported by Vaclav Kotesovec, 2025): a(n) = A056671(n) * A368885(n),
where A056671 is multiplicative with a(p) = 2 and a(p^e) = 1 for e > 1, and A368885 is
multiplicative with a(p^2) = 2 and a(p^e) = 1 otherwise.
-/

namespace OMA.S_oeis_a365498

/-- Value of g at p^e. -/
def c (e : ℕ) : ℤ := if e = 0 then 1 else if e = 1 then 1 else if e = 3 then -1 else 0

/-- The multiplicative function with Dirichlet series Product_p (1 + p^(-s) - p^(-3s)). -/
def g (n : ℕ) : ℤ := ∏ p ∈ n.primeFactors, c (n.factorization p)

/-- A365498. -/
def a (n : ℕ) : ℤ := ∑ d ∈ n.divisors, g d

/-- A056671. -/
def a056671 (n : ℕ) : ℤ := ∏ p ∈ n.primeFactors, if n.factorization p = 1 then 2 else 1

/-- A368885. -/
def a368885 (n : ℕ) : ℤ := ∏ p ∈ n.primeFactors, if n.factorization p = 2 then 2 else 1

theorem main :
    ∀ n : ℕ, 1 ≤ n → a n = a056671 n * a368885 n := by
  sorry

end OMA.S_oeis_a365498
