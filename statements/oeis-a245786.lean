import Mathlib

/-!
# A245786: Numbers n such that k(n) = (n/tau(n) + sigma(n)/n) is an integer.

Source: https://oeis.org/A245786
Credit: @agchua

Comment of A245786 (unsigned; the entry is by Jaroslav Krizek, Aug 15 2014):
  Conjecture: Subsequence of A216793.
Offset of A245786: 1 (data 1, 672, 4680, 30240, 23569920, 45532800, 275890944, ...).

A216793 (offset 1) is, by its name line: Numbers n such that gcd(sigma(n), n) > gcd(sigma(m), m)
for all m < n (data 1, 6, 24, 28, 120, 496, 672, ...).
Here tau(n) is the number of divisors of n and sigma(n) the sum of the divisors of n. Both
sequences consist of positive integers, so n >= 1 and m ranges over 1 <= m < n. The quotients
are computed in the rationals. Both sequences are listed in increasing order, so being a
subsequence means: every term of A245786 is a term of A216793.
-/

namespace OMA.S_oeis_a245786

/-- sigma(n): the sum of the divisors of n. -/
def sigma (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

/-- tau(n): the number of divisors of n. -/
def tau (n : ℕ) : ℕ := n.divisors.card

/-- n is a term of A245786: n >= 1 and n/tau(n) + sigma(n)/n is an integer. -/
def InA245786 (n : ℕ) : Prop :=
  1 ≤ n ∧ ∃ z : ℤ, (n : ℚ) / (tau n : ℚ) + (sigma n : ℚ) / (n : ℚ) = (z : ℚ)

/-- n is a term of A216793: n >= 1 and gcd(sigma(n), n) > gcd(sigma(m), m) for all 1 <= m < n. -/
def InA216793 (n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ m : ℕ, 1 ≤ m → m < n → Nat.gcd (sigma m) m < Nat.gcd (sigma n) n

/-- The comment's conjecture: A245786 is a subsequence of A216793. -/
theorem main : ∀ n : ℕ, InA245786 n → InA216793 n := by
  sorry

end OMA.S_oeis_a245786
