import Mathlib

/-!
# A122707: Smallest prime equal to the sum of squares of 8 consecutive primes divided by 2^n, or 1 if such a prime does not exist.

Source: https://oeis.org/A122707
Credit: @grzegorzfrskiba-hub

Formalizes the conjecture recorded in OEIS A122707 (Alexander Adamchuk, Sep 23 2006):
a(n) > 1 exists for all n > 2. Since a(n) = 1 exactly when no such prime exists, this says:
for every n > 2 there are 8 consecutive primes whose sum of squares, divided by 2^n, is a prime.

Conventions:
* `Nat.nth Nat.Prime i` is the i-th prime counted from 0, so `Nat.nth Nat.Prime 0 = 2`. The block
  `Nat.nth Nat.Prime k, …, Nat.nth Nat.Prime (k + 7)` is the OEIS block prime(k+1), …, prime(k+8);
  `k` ranges over all natural numbers, so every block of 8 consecutive primes occurs.
* "The sum S divided by 2^n is a prime p" is stated without division as S = 2^n * p with p prime.
* The bound n > 2 is the one in the conjecture: for n ≤ 2 the entry explains why no such prime exists
  (a(0) = a(1) = a(2) = 1).
* Check against the entry's example a(4) = 97: for k = 1 the primes are 3, 5, 7, 11, 13, 17, 19, 23,
  and 9 + 25 + 49 + 121 + 169 + 289 + 361 + 529 = 1552 = 2^4 * 97.
-/

namespace OMA.S_oeis_a122707

/-- The sum of the squares of the 8 consecutive primes starting at the k-th prime (counted from 0). -/
noncomputable def blockSum (k : ℕ) : ℕ :=
  ∑ i ∈ Finset.range 8, (Nat.nth Nat.Prime (k + i)) ^ 2

/-- The conjecture recorded in A122707: a(n) > 1 exists for all n > 2. -/
theorem main : ∀ n : ℕ, 2 < n → ∃ k p : ℕ, p.Prime ∧ blockSum k = 2 ^ n * p := by
  sorry

end OMA.S_oeis_a122707
