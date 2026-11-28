import Mathlib

/-!
# A083184: a palindromic prime whose digit sum is the n-th prime

Source: https://oeis.org/A083184
Credit: @R-Dson

`a(n)` is the smallest palindromic prime having a sum of digits equal to `prime(n)`, or `0` if no
such number exists. Conjecture: no entry is zero.

Conventions.
- A palindrome is a number whose decimal digits read the same backwards:
  `(Nat.digits 10 m).Palindrome`.
- `prime(n)` is the n-th prime (`A000040(n)`, 1-indexed), here `nthPrime n`.
- `a(n)` is the infimum in `ℕ` of the set of such primes, so it is `0` exactly when the set is
  empty.
- The offset of the entry is `1`.
- First terms of the entry: 2, 3, 5, 7, 191, 373, 13931, ...
-/

namespace OMA.S_oeis_a083184

/-- The decimal digits of `m` read the same backwards. -/
def IsPal (m : ℕ) : Prop := (Nat.digits 10 m).Palindrome

/-- The n-th prime, 1-indexed. -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- Smallest palindromic prime having a sum of digits equal to `nthPrime n`, or `0`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ IsPal p ∧ (Nat.digits 10 p).sum = nthPrime n}

theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a083184
