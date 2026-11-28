import Mathlib

/-!
# A116637: G.f. satisfies: A(x) = x/series_reversion(x/G(x)) where A(x) + A(-x) = 2*G(x^2) and G(x) is the g.f. of A046646.

Source: https://oeis.org/A116637
Credit: @agchua

R. J. Mathar (Jun 22 2016), in the formula section of A116637:
  Conjecture: 4*n*(n+1)*(3*n-1)*a(n) -36*n*a(n-1) -3*(3*n-5)*(3*n+2)*(3*n-4)*a(n-2)=0.
The terms are given explicitly in the formula section of the entry:
  a(2*n+1) = 2*(3*n+1)!/((n+1)!*(2*n+1)!) = 2*A006013(n), with a(0)=1 and
  a(2*n+2) = 2*(3*n+3)!/((n+1)!*(2*n+3)!) = 2*A001764(n+1).
The definition below is this formula: for odd n = 2k+1 we have n/2 = k, and for even n = 2k+2
we have n/2 = k+1, so that (3*(n/2))! = (3k+3)!, (n/2)! = (k+1)! and (2*(n/2)+1)! = (2k+3)!.
It reproduces the listed data. Values are taken in the rationals (they are integers).
The sequence has offset 0. The recurrence uses a(n-2). At n = 2 the left side equals 48, not 0,
because of the exceptional value a(0) = 1; the recurrence holds from n = 3 on, so the conjecture
is stated for n >= 3.
-/

namespace OMA.S_oeis_a116637

/-- A116637(n): a(0) = 1, a(2k+1) = 2 (3k+1)! / ((k+1)! (2k+1)!),
a(2k+2) = 2 (3k+3)! / ((k+1)! (2k+3)!). -/
def a (n : ℕ) : ℚ :=
  if n = 0 then 1
  else if n % 2 = 1 then
    2 * ((3 * (n / 2) + 1).factorial : ℚ)
      / (((n / 2 + 1).factorial : ℚ) * ((2 * (n / 2) + 1).factorial : ℚ))
  else
    2 * ((3 * (n / 2)).factorial : ℚ)
      / (((n / 2).factorial : ℚ) * ((2 * (n / 2) + 1).factorial : ℚ))

/-- Mathar's conjecture, for n >= 3:
4n(n+1)(3n-1) a(n) - 36n a(n-1) - 3(3n-5)(3n+2)(3n-4) a(n-2) = 0. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    4 * (n : ℚ) * ((n : ℚ) + 1) * (3 * (n : ℚ) - 1) * a n - 36 * (n : ℚ) * a (n - 1)
      - 3 * (3 * (n : ℚ) - 5) * (3 * (n : ℚ) + 2) * (3 * (n : ℚ) - 4) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a116637
