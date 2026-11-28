import Mathlib

/-!
# A002391: Decimal expansion of natural logarithm of 3.

Source: https://oeis.org/A002391
Credit: @luciusacarr

The entry records the conjecture (Mats Granvik, Jun 19 2011):
log(3) = Sum_{k>=1} A191907(3,k)/k.

Reading of the source:
* A191907 is the square array `T(n,k) = -(n-1)` if `n` divides `k`, else `1` (n, k ≥ 1).
  So `T(3,k) = -2` when `3 ∣ k` and `1` otherwise, and the series is
  1 + 1/2 - 2/3 + 1/4 + 1/5 - 2/6 + ... .
* This series is not absolutely convergent, so `Sum_{k>=1}` is read in the usual sense of the
  limit of the partial sums `Sum_{k=1..N} T(3,k)/k` as `N → ∞`.
* The claim: these partial sums tend to the natural logarithm `Real.log 3`.
-/

namespace OMA.S_oeis_a002391

/-- A191907: `T(n, k) = -(n-1)` if `n` divides `k`, else `1`. -/
def T (n k : ℕ) : ℤ := if n ∣ k then -((n : ℤ) - 1) else 1

theorem main :
    Filter.Tendsto (fun N : ℕ => ∑ k ∈ Finset.Icc 1 N, (T 3 k : ℝ) / k)
      Filter.atTop (nhds (Real.log 3)) := by
  sorry

end OMA.S_oeis_a002391
