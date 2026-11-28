import Mathlib

/-!
# A083144: a multiple of the n-th prime that is an n-digit palindrome

Source: https://oeis.org/A083144
Credit: @R-Dson

`a(n)` is the smallest `k` such that `k * prime(n)` is an n-digit palindrome, or `0` if no such
number exists. Conjecture: no entry is zero.

Conventions.
- `prime(n)` is the n-th prime (`A000040(n)`, 1-indexed), here `nthPrime n`.
- A palindrome is a number whose decimal digits read the same backwards, and an n-digit number is
  one with exactly n decimal digits.
- `a(n)` is the infimum in `ℕ` of the set of positive such `k`, so it is `0` exactly when the set
  is empty.
- The offset of the entry is `1`.
- First terms of the entry: 1, 11, 101, 143, 991, 7777 (so `1 * 2 = 2`, `11 * 3 = 33`,
  `101 * 5 = 505`, `143 * 7 = 1001`).
-/

namespace OMA.S_oeis_a083144

/-- The n-th prime, 1-indexed. -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- Smallest `k` such that `k * nthPrime n` has exactly `n` decimal digits and is a palindrome,
or `0`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {k : ℕ | 0 < k ∧ (Nat.digits 10 (k * nthPrime n)).length = n ∧
    (Nat.digits 10 (k * nthPrime n)).Palindrome}

theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a083144
