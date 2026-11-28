import Mathlib

/-!
# A325350: partitions whose augmented differences are weakly decreasing

Source: https://oeis.org/A325350

`a(n)` (offset 0) is the number of integer partitions of `n` whose augmented differences are
weakly decreasing. For a partition `y = (y_1, ..., y_k)` with `y_1 ≥ y_2 ≥ ... ≥ y_k > 0` the
augmented differences are `aug(y)_i = y_i - y_(i+1) + 1` for `i < k` and `aug(y)_k = y_k`.
The entry records the conjecture (Ilya Gutkovskiy, 2019)

  G.f.: `Sum_{k>=0} x^k / Product_{j=1..k} (1 - x^(j*(j+1)/2))`.

## Encoding

* A partition of `n` is a `Nat.Partition n`; its parts listed in weakly decreasing order are
  `p.parts.sort (· ≥ ·)`, and `augDiff` computes the augmented differences of that list.
  Since the parts are weakly decreasing, the truncated subtraction `y_i - y_(i+1)` is exact.
* `a 0 = 1` counts the empty partition (the term `k = 0` of the series is `1`).
* The generating function `Sum_{n≥0} a(n) x^n` is a formal power series over `ℚ`.
  `1 / (1 - x^d)` is the inverse `(1 - X^d)⁻¹` in `ℚ⟦X⟧` (its constant coefficient is `1`), and
  the infinite sum over `k ≥ 0` is the limit of its partial sums `k < N` in the coefficientwise
  topology on formal power series.
-/

open Filter
open scoped Topology PowerSeries.WithPiTopology

namespace OMA.S_oeis_a325350

/-- The augmented differences of a list `(y_1, ..., y_k)`: `y_i - y_(i+1) + 1` for `i < k`,
and `y_k` for the last entry. -/
def augDiff : List ℕ → List ℕ
  | [] => []
  | [y] => [y]
  | y :: z :: t => (y - z + 1) :: augDiff (z :: t)

/-- `a n` is the number of integer partitions of `n` whose augmented differences (computed on
the parts in weakly decreasing order) are weakly decreasing (A325350). -/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Nat.Partition n)).filter
    (fun p => (augDiff (p.parts.sort (· ≥ ·))).Pairwise (· ≥ ·))).card

/-- **Gutkovskiy's conjecture for A325350**: the generating function `Sum_{n≥0} a(n) x^n` equals
`Sum_{k>=0} x^k / Product_{j=1..k} (1 - x^(j*(j+1)/2))`. -/
theorem main :
    Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range N,
        (PowerSeries.X : PowerSeries ℚ) ^ k *
          ∏ j ∈ Finset.Icc 1 k, (1 - (PowerSeries.X : PowerSeries ℚ) ^ (j * (j + 1) / 2))⁻¹)
      atTop
      (𝓝 (PowerSeries.mk (fun n : ℕ => (a n : ℚ)))) := by
  sorry

end OMA.S_oeis_a325350
