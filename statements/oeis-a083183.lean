import Mathlib

/-!
# A083183: a palindromic prime with prime digits and a prime digit sum

Source: https://oeis.org/A083183
Credit: @R-Dson

`a(n)` is the smallest palindromic prime using only the prime digits `2, 3, 5, 7` and having a
sum of digits equal to `prime(n)`, or `0` if no such number exists. Conjecture: no entry is
zero.

Conventions.
- `prime(n)` is the n-th prime (`A000040(n)`, 1-indexed), here `nthPrime n`.
- A palindrome is a number whose decimal digits read the same backwards.
- `a(n)` is the infimum in `ℕ` of the set of such primes, so it is `0` exactly when the set is
  empty.
- The offset of the entry is `1`.
- First terms of the entry: 2, 3, 5, 7, 353, 373, 33533, 757, 35753, 75557.
-/

namespace OMA.S_oeis_a083183

/-- The n-th prime, 1-indexed. -/
noncomputable def nthPrime (n : ℕ) : ℕ := Nat.nth Nat.Prime (n - 1)

/-- Smallest palindromic prime whose decimal digits are all `2, 3, 5` or `7` and whose sum of
digits is `nthPrime n`, or `0`. -/
noncomputable def a (n : ℕ) : ℕ :=
  sInf {p : ℕ | p.Prime ∧ (Nat.digits 10 p).Palindrome ∧
    (∀ d ∈ Nat.digits 10 p, d ∈ ({2, 3, 5, 7} : Finset ℕ)) ∧ (Nat.digits 10 p).sum = nthPrime n}

theorem main : ∀ n : ℕ, 0 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a083183
