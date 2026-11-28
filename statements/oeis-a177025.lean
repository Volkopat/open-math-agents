import Mathlib

/-!
# A177025: the generating function of the number of polygonal representations

Source: https://oeis.org/A177025

`a(n)` (offset 3) is the number of ways to represent `n` as a polygonal number: the number of
pairs `(s, m)` with `s ≥ 3` and `m ≥ 1` such that the `m`-th `s`-gonal number
`P(s, m) = ((s - 2) m^2 - (s - 4) m) / 2` equals `n`. The entry records the conjecture
(Ilya Gutkovskiy, 2020)

  G.f.: `x * Sum_{k>=2} x^k / (1 - x^(k*(k + 1)/2))`.

## Encoding

* `P(s, m)` is written `m + (s - 2) * (m * (m - 1) / 2)`, which equals
  `((s - 2) m^2 - (s - 4) m) / 2` for `s ≥ 3`, `m ≥ 1`.
* For `n ≥ 3` a representation has `m ≥ 2` (as `P(s, 1) = 1`), hence `s = P(s, 2) ≤ n`, and
  `m ≤ P(s, m) = n`; so the pairs are searched in `[3, n] × [1, n]` without losing any.
  This agrees with the PARI program `sum(i=3, n, ispolygonal(n, i))` of the entry, since for each
  `s` there is at most one `m`.
* The generating function `Sum_{n≥3} a(n) x^n` is a formal power series over `ℚ`; its
  coefficients below degree 3 are `0`, as the sequence starts at `n = 3`.
* `1 / (1 - x^d)` is the inverse `(1 - X^d)⁻¹` in `ℚ⟦X⟧` (the constant coefficient is `1`), and the
  infinite sum over `k ≥ 2` is the limit of its partial sums `k < N` in the coefficientwise
  topology on formal power series.
-/

open Filter
open scoped Topology PowerSeries.WithPiTopology

namespace OMA.S_oeis_a177025

/-- The `m`-th `s`-gonal number `P(s, m) = m + (s - 2) * m * (m - 1) / 2`. -/
def polygonal (s m : ℕ) : ℕ := m + (s - 2) * (m * (m - 1) / 2)

/-- `a n` is the number of ways to represent `n` as a polygonal number: the number of pairs
`(s, m)` with `s ≥ 3`, `m ≥ 1` and `P(s, m) = n` (A177025, offset 3). -/
def a (n : ℕ) : ℕ :=
  ((Finset.Icc 3 n ×ˢ Finset.Icc 1 n).filter (fun p => polygonal p.1 p.2 = n)).card

/-- **Gutkovskiy's conjecture for A177025**: the generating function `Sum_{n≥3} a(n) x^n` equals
`x * Sum_{k>=2} x^k / (1 - x^(k*(k + 1)/2))`. -/
theorem main :
    Tendsto
      (fun N : ℕ => (PowerSeries.X : PowerSeries ℚ) *
        ∑ k ∈ Finset.Ico 2 N,
          (PowerSeries.X : PowerSeries ℚ) ^ k * (1 - PowerSeries.X ^ (k * (k + 1) / 2))⁻¹)
      atTop
      (𝓝 (PowerSeries.mk (fun n : ℕ => if 3 ≤ n then (a n : ℚ) else 0))) := by
  sorry

end OMA.S_oeis_a177025
