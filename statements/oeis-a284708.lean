import Mathlib

/-!
# OEIS A284708: a(n) > n# for n ≥ 4

Source: https://oeis.org/A284708 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (Arkadiusz Wesolowski, Jan 09 2018), offset 1: Smallest initial prime p for at least n
primes in increasing arithmetic progression with a common difference less than p. Comment:
Conjecture: a(n) > A034386(n) for every n >= 4. A034386(n) = n#, the product of the primes <= n.
Data: 2, 2, 3, 11, 37, 107, 409, 409, 409, 25471, ...

Formalization notes:
* IsAP n p d says that p is prime, 0 < d < p, and p + i*d is prime for every i < n: n primes in
  increasing arithmetic progression with first term p and common difference d < p.
* A034386(n) is Mathlib's primorial n, the product of the primes up to n.
* main says: for every n ≥ 4, every such first term p exceeds n#. Since a(n) is the least such p,
  this is equivalent to a(n) > n# whenever a(n) exists, and it does not presuppose that a(n)
  exists for every n.
* Control proved in the proof file: IsAP 4 11 6 (the progression 11, 17, 23, 29 of a(4) = 11)
  and primorial 4 = 6.
-/

namespace OMA.S_oeis_a284708

/-- `p, p + d, ..., p + (n-1) d` are `n` primes in increasing arithmetic progression with common
difference `d < p`. -/
def IsAP (n p d : ℕ) : Prop := p.Prime ∧ 0 < d ∧ d < p ∧ ∀ i < n, (p + i * d).Prime

/-- Wesolowski's conjecture: a(n) > A034386(n) for every n >= 4. -/
theorem main : ∀ n : ℕ, 4 ≤ n → ∀ p d : ℕ, IsAP n p d → primorial n < p := by
  sorry

end OMA.S_oeis_a284708
