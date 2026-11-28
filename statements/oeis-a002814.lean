import Mathlib

/-!
# A002814: For n > 1: a(n) = a(n-1)^3 + 3*a(n-1)^2 - 3; a(0) = 1, a(1) = 2.

Source: https://oeis.org/A002814
Credit: @maaaakks

The source (Peter Bala, Dec 08 2022) states:

  Conjecture: The sequence {a(n) - 2: n >= 1} is a strong divisibility sequence, that is,
  gcd(a(n) - 2, a(m) - 2) = a(gcd(n, m)) - 2 for n, m >= 1.
  [added Jul 26 2026: This is correct - see the Bala link. More generally, for k >= 1, the
  sequence {a(n+k) - a(k) : n >= 1} is a strong divisibility sequence.]

## Indexing

Read with the OEIS offset 0 (a(0) = 1, a(1) = 2, a(2) = 17, a(3) = 5777), the displayed formula
is false: a(1) - 2 = 0, so for n = 2, m = 3 the left side is gcd(15, 5775) = 15 while the right
side is a(gcd(2, 3)) - 2 = a(1) - 2 = 0. (It fails for every pair with gcd(n, m) = 1, since the
left side is never 0 for n, m >= 2.)

The intended statement is the case k = 1 of the general remark: the sequence
c(n) := a(n + 1) - a(1) = a(n + 1) - 2, for n >= 1 (that is 15, 5775, 192900153615, ...),
is a strong divisibility sequence, gcd(c(n), c(m)) = c(gcd(n, m)). This is the reading formalized
below. It agrees with the source's general remark and has been checked numerically for
1 <= n, m <= 6.

`a` takes values in `ℤ` so that the differences are not truncated.
-/

namespace OMA.S_oeis_a002814

/-- A002814, offset 0: a(0) = 1, a(1) = 2, a(n) = a(n-1)^3 + 3 a(n-1)^2 - 3 for n > 1. -/
def a : ℕ → ℤ
  | 0 => 1
  | 1 => 2
  | n + 2 => a (n + 1) ^ 3 + 3 * a (n + 1) ^ 2 - 3

/-- The sequence c(n) = a(n + 1) - 2 (n >= 1) is a strong divisibility sequence:
gcd(c(n), c(m)) = c(gcd(n, m)) for all n, m >= 1. -/
theorem main : ∀ n m : ℕ, 1 ≤ n → 1 ≤ m →
    (Int.gcd (a (n + 1) - a 1) (a (m + 1) - a 1) : ℤ) = a (Nat.gcd n m + 1) - a 1 := by
  sorry

end OMA.S_oeis_a002814
