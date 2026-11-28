import Mathlib

/-!
# A071681: Number of ways to represent the n-th prime as arithmetic mean of two other primes.

Source: https://oeis.org/A071681
Credit: @divmxnd0x

Conjecture (stated in A071681): `a(n) > 0` for `n > 2`.

Formalization notes:
* `prime n` is the `n`-th prime (`prime 1 = 2`). A representation of `p` as the arithmetic mean of
  two other primes is an unordered pair `q < p < r` of primes with `q + r = 2p`; it is counted by
  its smaller element `q < p` (data `0, 0, 1, 1, 2, 2, 3, 1, ...`).
-/

namespace OMA.S_oeis_a071681

/-- The `n`-th prime, `prime 1 = 2`. -/
noncomputable def prime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- A071681(n): the number of primes `q < p` with `2p - q` prime, `p = prime n`. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.range (prime n)).filter fun q => q.Prime ∧ (2 * prime n - q).Prime).card

/-- Every prime `prime n` with `n > 2` is the arithmetic mean of two other primes. -/
theorem main : ∀ n : ℕ, 2 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a071681
