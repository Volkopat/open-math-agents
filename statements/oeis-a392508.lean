import Mathlib

/-!
# A392508: iterating prime(x) -> gpf(2*prime(x) + prime(x+1)) always reaches 5

Source: https://oeis.org/A392508
Credit: @gblacher2

A392508 (Alain Rocchelli), offset 1: a(n) is the number of iterations
prime(x) -> gpf(2*prime(x)+prime(x+1)) starting at prime(n) until the value prime(3) = 5 is
reached, where gpf(x) is the greatest prime factor of x; a(n) = -1 if the value 5 is not reached.
Conjecture (in the entry): a(n) is never equal to -1.

Conventions:
* prime(n) is the n-th prime with OEIS indexing, prime(1) = 2, written `Nat.nth Nat.Prime (n - 1)`
  (Mathlib's `Nat.nth Nat.Prime` is 0-indexed).
* For a prime p = prime(x), the next prime prime(x+1) is the least prime q with q ≥ p + 1,
  written `nextPrime p`.
* gpf(m) is the greatest prime factor of m, written `m.primeFactors.sup id`; along the iteration
  the argument `2 * p + nextPrime p` is at least 7, so this is a genuine prime and every iterate
  is again a prime.
* a(n) ≠ -1 means that some iterate `f^[k] (prime n)` (k ≥ 0) equals 5; n ranges over n ≥ 1.
  The case k = 0 covers a(3) = 0.
-/

namespace OMA.S_oeis_a392508

/-- The greatest prime factor of `m` (for `m ≥ 2`). -/
def gpf (m : ℕ) : ℕ := m.primeFactors.sup id

/-- The least prime `q` with `q ≥ p + 1`; for `p = prime(x)` this is `prime(x+1)`. -/
noncomputable def nextPrime (p : ℕ) : ℕ := Nat.find (Nat.exists_infinite_primes (p + 1))

/-- The map `prime(x) ↦ gpf(2 * prime(x) + prime(x+1))`. -/
noncomputable def f (p : ℕ) : ℕ := gpf (2 * p + nextPrime p)

/-- For every `n ≥ 1`, iterating `f` from `prime(n)` reaches `5 = prime(3)`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → ∃ k : ℕ, f^[k] (Nat.nth Nat.Prime (n - 1)) = 5 := by
  sorry

end OMA.S_oeis_a392508
