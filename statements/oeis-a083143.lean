import Mathlib

/-!
# A083143: an n-digit palindromic multiple of the n-th prime

Source: https://oeis.org/A083143
Credit: @R-Dson

`a(n)` is the smallest n-digit palindromic multiple of `prime(n)`, or `0` if no such number
exists. Conjecture: no entry is zero.

Conventions.
- `prime(n)` is the n-th prime (`A000040(n)`, 1-indexed), here `nthPrime n`.
- An n-digit number is a positive number with exactly n decimal digits, and a palindrome is a
  number whose decimal digits read the same backwards.
- `a(n)` is the infimum in `ℕ` of the set of such multiples, so it is `0` exactly when the set is
  empty.
- The offset of the entry is `1`.
- First terms of the entry: 2, 33, 505, 1001, 10901, 101101.
-/

namespace OMA.S_oeis_a083143

/-- The n-th prime, 1-indexed. -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- Smallest n-digit palindromic multiple of `nthPrime n`, or `0`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {m : ℕ | 0 < m ∧ (Nat.digits 10 m).length = n ∧ (Nat.digits 10 m).Palindrome ∧
    nthPrime n ∣ m}

theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a083143
