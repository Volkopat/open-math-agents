import Mathlib

/-!
# A242429: Length of longest chain of nonempty proper subsemigroups of the monoid of partial injective order-preserving functions of a chain with n elements.

Source: https://oeis.org/A242429
Credit: @agchua

R. J. Mathar (Oct 20 2015), in the formula section of A242429:
  Conjecture: n*(131*n-376)*a(n) +2*(-563*n^2+1993*n-1185)*a(n-1) +3*(1099*n^2-4678*n+4684)*a(n-2)
  +2*(-1987*n^2+9803*n-12021)*a(n-3) +4*(209*n-387)*(2*n-7)*a(n-4)=0.
The sequence is taken by the explicit formula of the same section,
  a(n) = binomial(2*n,n)/2 + 3*2^(n-1) - n - 2. - Gheorghe Coserea, May 16 2016,
which agrees with the PARI program of the entry and with all listed terms (binomial(2n,n) is
even for n ≥ 1, so the quotient is exact). The offset is 1 and the recurrence uses a(n-4), so
the conjecture is stated for n ≥ 5. Terms are taken in ℤ.
-/

namespace OMA.S_oeis_a242429

/-- a(n) = binomial(2*n,n)/2 + 3*2^(n-1) - n - 2. -/
def a (n : ℕ) : ℤ := (((2 * n).choose n / 2 : ℕ) : ℤ) + 3 * 2 ^ (n - 1) - n - 2

/-- Mathar's conjectured recurrence, for n ≥ 5. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (n : ℤ) * (131 * n - 376) * a n + 2 * (-563 * (n : ℤ) ^ 2 + 1993 * n - 1185) * a (n - 1)
      + 3 * (1099 * (n : ℤ) ^ 2 - 4678 * n + 4684) * a (n - 2)
      + 2 * (-1987 * (n : ℤ) ^ 2 + 9803 * n - 12021) * a (n - 3)
      + 4 * (209 * (n : ℤ) - 387) * (2 * n - 7) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a242429
