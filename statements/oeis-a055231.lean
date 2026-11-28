import Mathlib

/-!
# A055231: Powerfree part of n: product of primes that divide n only once.

Source: https://oeis.org/A055231
Credit: @ShoQo

Conjecture (Velin Yanev, Feb 06 2019): a(n*m) = a(n)*a(m)/(gcd(n,a(m))*gcd(m,a(n))) for all n
and m > 0. (N. J. A. Sloane notes in the entry that this follows from a(n) being multiplicative
with a(p) = p and a(p^e) = 1 for e > 1.)

Formalization notes:
* "Primes that divide n only once" are the primes `p` with `v_p(n) = 1`, i.e.
  `n.factorization p = 1`; `a(n)` is their product (so `a(1) = 1`).
* The division is natural-number division; the identity asserts it is the stated value.
-/

namespace OMA.S_oeis_a055231

/-- a(n): the product of the primes that divide `n` exactly once. -/
def a (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors.filter (fun p => n.factorization p = 1), p

theorem main : ∀ n m : ℕ, 0 < n → 0 < m →
    a (n * m) = a n * a m / (Nat.gcd n (a m) * Nat.gcd m (a n)) := by
  sorry

end OMA.S_oeis_a055231
