import Mathlib

/-!
# A190154: Diagonal sums of the triangle A190152.

Source: https://oeis.org/A190154
Credit: @JeremyDevs

Formalizes the conjecture recorded in the FORMULA section of OEIS A190154 (R. J. Mathar,
Mar 15 2013): Conjecture: G.f. ( -1+x+x^3-x^4+2*x^2 ) / ( (x^3-3*x^2+4*x-1)*(x^3+3*x^2+2*x+1) ).

Conventions:
* A190152 is the triangle of binomial coefficients T(n,k) = binomial(3*n-k, 3*n-3*k) for
  0 <= k <= n; `T n k` below, with `Nat.choose` and natural-number subtraction (exact for
  k <= n).
* The diagonal sums of a triangle are a(n) = Sum_{k=0..floor(n/2)} T(n-k,k) (offset 0), which is
  the formula a(n) = Sum_{k=0..floor(n/2)} binomial(3*n-4*k, 3*n-6*k) given in the entry; data
  1, 1, 2, 11, 30, 91, 303, 936, ... The sum runs over `Finset.range (n / 2 + 1)`, and for these
  k one has k <= n - k, so every subtraction is exact.
* The ordinary generating function of the offset-0 sequence is the formal power series
  `PowerSeries.mk a` in `PowerSeries ℤ`. G.f. = N(x)/D(x) is stated without division, as
  `G.f. * D(x) = N(x)` with N(x) = -1+x+x^3-x^4+2*x^2 and
  D(x) = (x^3-3*x^2+4*x-1)*(x^3+3*x^2+2*x+1), which is the same assertion (D has constant
  term -1, so it is invertible as a power series).
-/

namespace OMA.S_oeis_a190154

/-- A190152: T(n,k) = binomial(3n-k, 3n-3k). -/
def T (n k : ℕ) : ℕ := Nat.choose (3 * n - k) (3 * n - 3 * k)

/-- A190154 (offset 0): the diagonal sums a(n) = Sum_{k=0..floor(n/2)} T(n-k,k). -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n / 2 + 1), (T (n - k) k : ℤ)

/-- The generating function of A190154 is
(-1+x+x^3-x^4+2x^2) / ((x^3-3x^2+4x-1)(x^3+3x^2+2x+1)). -/
theorem main :
    PowerSeries.mk a
        * ((PowerSeries.X ^ 3 - 3 * PowerSeries.X ^ 2 + 4 * PowerSeries.X - 1)
          * (PowerSeries.X ^ 3 + 3 * PowerSeries.X ^ 2 + 2 * PowerSeries.X + 1))
      = (-1 + PowerSeries.X + PowerSeries.X ^ 3 - PowerSeries.X ^ 4 + 2 * PowerSeries.X ^ 2
          : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a190154
