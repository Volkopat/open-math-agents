import Mathlib

/-!
# A088987: Triples of primes between two consecutive prime-indexed primes.

Source: https://oeis.org/A088987
Credit: @bnb9001

The prime-indexed primes are prime(prime(k)) for k >= 1, where prime(n) is the n-th prime
(1-indexed: prime(1) = 2). In increasing order they are 3, 5, 11, 17, 31, ..., so the k-th and
(k+1)-th of them are consecutive. Example from the entry: prime(prime(4)) = 17,
prime(prime(5)) = 31, and 19, 23, 29 are the only three primes between 17 and 31.

Conjecture: There cannot be an even number total of primes between two consecutive prime-indexed
primes. The conjecture is true except for the first two prime-indexed primes (3 and 5), which have
zero primes between them.

Formalized as: the first two prime-indexed primes are 3 and 5 with zero primes strictly between
them, and for every later consecutive pair (k >= 2) the number of primes strictly between them is
odd. `prime n` is Mathlib's 0-indexed `Nat.nth Nat.Prime` shifted to the 1-indexed convention.
-/

namespace OMA.S_oeis_a088987

/-- The `n`-th prime, 1-indexed: `prime 1 = 2`, `prime 2 = 3`, `prime 3 = 5`, ... -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- The `k`-th prime-indexed prime `prime (prime k)`, for `k >= 1`. -/
noncomputable def ppi (k : ℕ) : ℕ := prime (prime k)

/-- The number of primes strictly between the consecutive prime-indexed primes
`ppi k` and `ppi (k + 1)`. -/
noncomputable def between (k : ℕ) : ℕ :=
  {p : ℕ | p.Prime ∧ ppi k < p ∧ p < ppi (k + 1)}.ncard

theorem main : ppi 1 = 3 ∧ ppi 2 = 5 ∧ between 1 = 0 ∧
    ∀ k : ℕ, 2 ≤ k → Odd (between k) := by
  sorry

end OMA.S_oeis_a088987
