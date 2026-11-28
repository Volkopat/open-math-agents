import Mathlib

/-!
# A072190: Indices of primes with primitive root 2

Source: https://oeis.org/A072190

Conjecture (Artin's Primitive Root Conjecture for base 2):
There are infinitely many primes `p` for which `2` is a primitive root modulo `p`,
i.e., the multiplicative order of `2` in `ZMod p` equals `p - 1`.

Conventions:
- Offset: `1`; first terms: `2, 3, 5, 6, 8, 10, 12, 16, 17, 18, ...`, corresponding to
  the primes `3, 5, 11, 13, 19, 29, 37, 53, 59, 61, ...` (A001122).
- `nthPrime n` denotes the `n`-th prime (1-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`).
- For `p = 2`, `orderOf (2 : ZMod 2) = orderOf 0 = 0 ≠ 1`, so `p = 2` is excluded.
-/

namespace OMA.S_oeis_a072190

/-- The `n`-th prime number (1-indexed: `nthPrime 1 = 2`, `nthPrime 2 = 3`, ...). -/
noncomputable def nthPrime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n - 1)

/-- The set of 1-based prime indices `n` such that `2` is a primitive root modulo `prime(n)`
(OEIS A072190). -/
def S : Set ℕ :=
  {n : ℕ | 1 ≤ n ∧ orderOf (2 : ZMod (nthPrime n)) = nthPrime n - 1}

/-- Artin's Conjecture for base 2: OEIS A072190 is infinite. -/
theorem main : Set.Infinite S := by
  sorry

end OMA.S_oeis_a072190
