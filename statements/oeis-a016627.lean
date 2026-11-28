import Mathlib

/-!
# A016627: Decimal expansion of log(4).

Source: https://oeis.org/A016627
Credit: @luciusacarr

The entry (data 1, 3, 8, 6, 2, 9, 4, ...) records in its formula section the claim
(Mats Granvik, Jun 19 2011): log(4) = Sum_{k >= 1} A191907(4, k)/k, (conjecture).

Reading of the source:
* A191907 is the square array T(n, k) = -(n - 1) if n divides k, else 1 (n, k >= 1).
  So the row n = 4 is 1, 1, 1, -3, 1, 1, 1, -3, ...
* The series Sum_{k >= 1} T(4, k)/k = 1 + 1/2 + 1/3 - 3/4 + 1/5 + ... is not absolutely
  convergent, so the sum is read in the usual sense of an infinite series: the partial sums
  Sum_{k = 1..N} T(4, k)/k tend to log(4) (natural logarithm) as N tends to infinity.
-/

namespace OMA.S_oeis_a016627

/-- The square array A191907: `T n k = -(n - 1)` if `n ∣ k`, else `1`. -/
def T (n k : ℕ) : ℤ := if n ∣ k then -((n : ℤ) - 1) else 1

theorem main :
    Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, (T 4 k : ℝ) / k) Filter.atTop
      (nhds (Real.log 4)) := by
  sorry

end OMA.S_oeis_a016627
