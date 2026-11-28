import Mathlib

/-!
# A277201: Primes of the form (p^4 + 1)/2, where p is prime

Source: https://oeis.org/A277201
Credit: @xor2k

Formalizes the OEIS A277201 conjecture: the sequence consists of the numbers k such that
tau(2k) = 4 and tau(2k-1) = 5.

Conventions:
- The terms of the sequence are the primes `q` with `q = (p^4 + 1)/2` for some prime `p`
  (the sequence is the increasing enumeration of this set, so it consists of exactly these numbers).
- `tau n` is the number of divisors, `(Nat.divisors n).card`.
- `k` ranges over all natural numbers; `2 * k - 1` is natural subtraction (for `k = 0` it is `0`,
  which has no divisors in Mathlib, so `k = 0` is not in the left-hand set; this matches OEIS,
  where `k` is positive).
- `/` is natural division; for prime `p = 2` it gives `17 / 2 = 8`, not prime, so this case adds
  no term (and OEIS likewise has no term for `p = 2`).
- The claim is stated as an equality of sets.
-/

namespace OMA.S_oeis_a277201

/-- The set of numbers `k` with `tau(2k) = 4` and `tau(2k - 1) = 5` equals the set of terms of
A277201, i.e. of primes of the form `(p^4 + 1)/2` with `p` prime. -/
theorem main :
    {k : ℕ | (2 * k).divisors.card = 4 ∧ (2 * k - 1).divisors.card = 5} =
      {q : ℕ | q.Prime ∧ ∃ p : ℕ, p.Prime ∧ q = (p ^ 4 + 1) / 2} := by
  sorry

end OMA.S_oeis_a277201
