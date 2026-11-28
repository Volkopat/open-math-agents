import Mathlib

/-!
# A274039: Expansion of (x^4 + x^10) / (1 - 2*x + x^2).

Source: https://oeis.org/A274039
Credit: @agchua

Comment line of A274039 (offset 0; entry by Sean A. Irvine, Jun 07 2016), verbatim:
  This g.f. was incorrectly conjectured by Plouffe in his 1992 disseration to be the g.f. for A005377.
(A005377 records the same: G.f.: z^4 * (z^2+1) * (z^4-z^2+1) / (z-1)^2; [Conjectured by
Simon Plouffe in his 1992 dissertation, but is incorrect.] Note z^4 (z^2+1)(z^4-z^2+1) = z^4 + z^10.)
This file states the comment's assertion, that (x^4 + x^10)/(1 - 2x + x^2) is NOT the g.f. of
A005377, as a non-identity of formal power series over Q:
  (sum over n >= 0 of A005377(n+1) X^n) * (1 - 2X + X^2) is not X^4 + X^10.
Since 1 - 2X + X^2 has constant coefficient 1, it is a unit of Q[[X]], so the identity would say
exactly that the g.f. expands to the sum of A005377(n+1) X^n, i.e. A274039(n) = A005377(n+1) for
all n >= 0. The shift by one is the alignment of the two entries (A274039 has offset 0, A005377
has offset 1; both begin 0, 0, 0, 0, 1, 2, 3, ...), under which the two agree for n <= 29.
A005377 (offset 1): Number of low discrepancy sequences in base 4. Its definition is the formula
of the entry (Sean A. Irvine, Jun 07 2016, from the Niederreiter paper), verbatim:
  Let N(b,n) = (1/n) * Sum_{d|n} mobius(n/d) * b^d. Let M(b,n) = Sum_{k=1..n} N(b,k) with
  M(b,0) = 0. Let r = r(b,n) be the largest value r such that M(b,r) <= n. Then
  a(n) = r * (n - M(4, r)) + Sum_{h=1..r} (h-1) * N(4, h) [From Niederreiter paper].
The set of r with M(4,r) <= n contains 0 and is finite (M(4,r) >= r), so rmax below, its sSup, is
its largest element. The definition gives the listed terms 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 8, 10, ...
(all 61 listed terms checked by exact computation).
-/

namespace OMA.S_oeis_a274039

/-- N(b, n) = (1/n) * sum over the divisors d of n of mobius(n/d) * b^d. -/
noncomputable def N (b n : ℕ) : ℚ :=
  (1 / (n : ℚ)) * ∑ d ∈ n.divisors, ((ArithmeticFunction.moebius (n / d) : ℤ) : ℚ) * (b : ℚ) ^ d

/-- M(b, n) = sum of N(b, k) over k = 1..n; in particular M(b, 0) = 0. -/
noncomputable def M (b n : ℕ) : ℚ := ∑ k ∈ Finset.Icc 1 n, N b k

/-- r(b, n): the largest value r such that M(b, r) <= n. -/
noncomputable def rmax (b n : ℕ) : ℕ := sSup {x : ℕ | M b x ≤ (n : ℚ)}

/-- A005377(n) = r * (n - M(4, r)) + sum of (h - 1) * N(4, h) over h = 1..r, with r = r(4, n). -/
noncomputable def A005377 (n : ℕ) : ℚ :=
  (rmax 4 n : ℚ) * ((n : ℚ) - M 4 (rmax 4 n)) +
    ∑ h ∈ Finset.Icc 1 (rmax 4 n), ((h : ℚ) - 1) * N 4 h

/-- The comment of A274039: its g.f. (x^4 + x^10)/(1 - 2x + x^2) is not the g.f. of A005377. -/
theorem main : PowerSeries.mk (fun n => A005377 (n + 1)) *
      (1 - 2 * PowerSeries.X + PowerSeries.X ^ 2) ≠
    PowerSeries.X ^ 4 + PowerSeries.X ^ 10 := by
  sorry

end OMA.S_oeis_a274039
