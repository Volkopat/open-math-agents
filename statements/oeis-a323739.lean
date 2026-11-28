import Mathlib

/-!
# A323739: a(n) is the number of residues modulo (4*primorial(n)) of the squares of primes
greater than or equal to prime(n+1).

Source: https://oeis.org/A323739
Credit: @bnb9001

Here primorial(n) = A002110(n) is the product of the first n primes (offset 0: 2, 1, 1, 2, 6, 30,
180, ...). With Mathlib's 0-indexed `Nat.nth Nat.Prime`, prime(n+1) is `Nat.nth Nat.Prime n` and
prime(j) is `Nat.nth Nat.Prime (j - 1)`.

Conjecture: a(n) = 2^(1-n) * Product_{j=1..n} (prime(j) - 1) for n >= 0. Charlie Neder notes that
the conjecture is true. It is stated below without division, multiplied through by 2^n.
-/

namespace OMA.S_oeis_a323739

open Finset

/-- The product of the first `k` primes (A002110). -/
noncomputable def firstPrimesProd (k : ℕ) : ℕ := ∏ i ∈ range k, Nat.nth Nat.Prime i

/-- A323739: the number of values of `p^2 mod (4 * primorial(n))` over primes `p >= prime(n+1)`. -/
noncomputable def a (n : ℕ) : ℕ :=
  Set.ncard {r : ℕ | ∃ p : ℕ, p.Prime ∧ Nat.nth Nat.Prime n ≤ p ∧
    r = p ^ 2 % (4 * firstPrimesProd n)}

/-- The conjecture, proved: `2^n * a(n) = 2 * Product_{j=1..n} (prime(j) - 1)`. -/
theorem main : ∀ n : ℕ, 2 ^ n * a n = 2 * ∏ j ∈ range n, (Nat.nth Nat.Prime j - 1) := by
  sorry

end OMA.S_oeis_a323739
