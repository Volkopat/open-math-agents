import Mathlib

/-!
# A026741: lcm and gcd via the reduced value a(n, p)

Source: https://oeis.org/A026741 (OEIS Foundation, CC BY-SA 4.0).

From Timothy Hopper (Feb 26 2017): for a prime p, let a(n, p) = n/p if
n mod p = 0, and a(n, p) = n otherwise (for p = 2 this is A026741).
Conjecture: lcm(n, p) = p * a(n, p) and gcd(n, p) = n / a(n, p).
The quotient n / a(n, p) only makes sense for positive n, so n ranges over
the positive integers.
-/

namespace OMA.S_oeis_a026741

/-- `a n p` is `n / p` when `p` divides `n`, and `n` otherwise. -/
def a (n p : ℕ) : ℕ := if n % p = 0 then n / p else n

theorem main : ∀ p n : ℕ, p.Prime → 0 < n →
    Nat.lcm n p = p * a n p ∧ Nat.gcd n p = n / a n p := by
  sorry

end OMA.S_oeis_a026741
