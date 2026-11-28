import Mathlib

/-!
# A238643: Number of primes p <= n such that 2*pi(p) - (-1)^n and p*n +((-1)^n - 3)/2 are both prime, where pi(x) is the number of primes not exceeding x.

Source: https://oeis.org/A238643
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A238643 (Zhi-Wei Sun, Mar 01 2014),
part (i): a(n) > 0 for all n > 2.

Conventions:
* The sequence has offset 1 (data 0, 0, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, ...). `a n` is the number
  of primes p <= n such that 2*pi(p) - (-1)^n and p*n + ((-1)^n - 3)/2 are both prime.
* pi(x) is `Nat.primeCounting x`, the number of primes not exceeding x.
* The signs are rendered over the natural numbers: 2*pi(p) - (-1)^n is
  2*pi(p) + 2*(n mod 2) - 1 (that is 2*pi(p) - 1 for even n and 2*pi(p) + 1 for odd n), and
  p*n + ((-1)^n - 3)/2 is p*n - (1 + n mod 2) (that is p*n - 1 for even n and p*n - 2 for odd
  n). Both natural subtractions are exact for a prime p <= n (pi(p) >= 1 and p*n >= 4).
* Only part (i) of the conjecture is formalized; part (ii) is a different statement.
-/

namespace OMA.S_oeis_a238643

/-- A238643: number of primes p <= n with 2*pi(p) - (-1)^n and p*n + ((-1)^n - 3)/2
both prime. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {p : ℕ | p.Prime ∧ p ≤ n ∧ (2 * Nat.primeCounting p + 2 * (n % 2) - 1).Prime ∧
    (p * n - (1 + n % 2)).Prime}

/-- The conjecture of Sun, part (i): a(n) > 0 for all n > 2. -/
theorem main : ∀ n : ℕ, 2 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a238643
