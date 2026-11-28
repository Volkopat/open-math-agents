import Mathlib

/-!
# OEIS A240434: binomial transform of the sum of the first even squares

Source: https://oeis.org/A240434
Conjectured formulas: Colin Barker, April 6, 2014.
Credit: @caa1982
-/

open scoped BigOperators

namespace OMA.S_oeis_a240434

/-- The first `k` positive even squares, summed in the rationals. -/
def evenSquareSum (k : ℕ) : ℚ := ∑ i ∈ Finset.range k, (2 * ((i : ℚ) + 1)) ^ 2

/-- The ordinary binomial transform of A002492. -/
def a (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * evenSquareSum k

/-- The closed coefficient formula and ordinary generating function. The
denominator in the generating function has constant coefficient one, so the
formal-series equation below is equivalent to the displayed fraction in OEIS. -/
theorem main :
    (∀ n : ℕ, a n = (2 : ℚ) ^ (n - 1) * n * (5 + 6 * (n : ℚ) + (n : ℚ) ^ 2) / 3) ∧
    PowerSeries.mk a * ((1 : PowerSeries ℚ) - PowerSeries.C 2 * PowerSeries.X) ^ 4 =
      (4 : PowerSeries ℚ) * PowerSeries.X * (1 - PowerSeries.X) := by
  sorry

end OMA.S_oeis_a240434
