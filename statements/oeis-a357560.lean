import Mathlib

/-!
# A357560: a(n) = the numerator of ( Sum_{k = 1..n} (-1)^(n+k)*(1/k)*binomial(n,k)* binomial(n+k,k)^2 )

Source: https://oeis.org/A357560

`a(n)` is the numerator (in lowest terms) of the rational number
`s(n) = Sum_{k = 1..n} (-1)^(n+k) * (1/k) * binomial(n,k) * binomial(n+k,k)^2`; offset 0. The
first terms are `0, 4, 0, 94, 500, 19262, 50421, 2929583, 25197642, 2007045752, ...`.

The formula section of the entry (Peter Bala, Oct 04 2022) makes one conjectural statement, stated
here:

  Conjecture: `a(p-1) == 0 (mod p^4)` for all primes `p >= 7` (checked up to `p = 499`).

Not part of the target: the note that the Apery numbers `B(n) = A005258(n)` satisfy
`B(p-1) == 1 (mod p^3)` for primes `p >= 5` is quoted as a known fact (Straub, Example 3.4), and
the example line `a(19 - 1) == 0 (mod 19^4)` is an instance of the conjecture. The comment section
of the entry also lists two conjectures about the whole family `S_m(n)` (numerators of the same sum
with `1/k^m` in place of `1/k`); the conjecture stated here is exactly the case `m = 1` of the
second of them (`p > m + 4` means `p >= 7`), and the other members of the family (`m >= 2`) are a
different statement, not covered by this file.

Formalized: `s n` is the rational sum exactly as in the name line, with `k` running over
`Finset.Icc 1 n`, that is `1 <= k <= n`, the sign `(-1)^(n+k)` and the factor `1/k` taken in the
rationals, and `Nat.choose` for the binomial coefficients. `a n` is the integer `(s n).num`, the
numerator of `s n` in lowest terms with positive denominator (`Rat.num`), which is what Maple
`numer` (the program of the entry) returns. For `n = 0` the sum is empty, `s 0 = 0` and
`(0 : ℚ).num = 0`, as in the data. The sums `s(n)` are nonnegative in the range of the data, so
the sign convention of the numerator does not matter there, and it never matters for divisibility.
The index `p - 1` is a natural-number subtraction, harmless because a prime is at least 2. The
congruence `a(p-1) == 0 (mod p^4)` is written as divisibility of `a (p - 1)` by `p ^ 4` in the
integers. The range is every prime `p` with `7 <= p`; the claim is false for `p = 5`
(`a(4) = 500 = 2^2 * 5^3`) and for `p = 2` (`a(1) = 4`), and holds trivially for `p = 3`
(`a(2) = 0`), which is outside the stated range.
-/

namespace OMA.S_oeis_a357560

/-- The rational sum `s(n) = Sum_{k=1..n} (-1)^(n+k) * (1/k) * C(n,k) * C(n+k,k)^2`. -/
def s (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n,
    (-1 : ℚ) ^ (n + k) * (1 / (k : ℚ)) * (n.choose k : ℚ) * ((n + k).choose k : ℚ) ^ 2

/-- A357560: `a(n)` is the numerator of `s(n)` in lowest terms. -/
def a (n : ℕ) : ℤ := (s n).num

/-- Bala's conjecture: `a(p-1) == 0 (mod p^4)` for every prime `p >= 7`. -/
theorem main : ∀ p : ℕ, p.Prime → 7 ≤ p → ((p : ℤ) ^ 4) ∣ a (p - 1) := by
  sorry

end OMA.S_oeis_a357560
