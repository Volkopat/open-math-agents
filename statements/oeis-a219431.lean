import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Combinatorics.Enumerative.Partition.Basic

namespace OMA.S_oeis_a219431

/-- Number of overpartitions of `N` (OEIS A015128): for each integer partition `p` of `N`,
each distinct part size in `p` may independently be overlined or not. -/
noncomputable def overpartitionCount (N : ℕ) : ℕ :=
  ∑ p : Nat.Partition N, 2 ^ p.parts.toFinset.card

/-- Generating function of `A219430(n) = overpartitionCount (n^2)`. -/
noncomputable def Fseries : PowerSeries ℤ :=
  PowerSeries.mk fun n => (overpartitionCount (n ^ 2) : ℤ)

/-- OEIS A219431: Logarithmic derivative `A(x) = x * F'(x) / F(x)` of the g.f. `F(x)`
of the overpartitions of `n^2` (`A219430`), satisfying `F(x) * A(x) = x * F'(x)`.
Conjecture: `a(2*n + 1) ≡ 2 (mod 4)` and `a(2*n) ≡ 0 (mod 4)` for all `n ≥ 0`. -/
theorem main :
    ∀ (A : PowerSeries ℤ),
      Fseries * A = PowerSeries.X * PowerSeries.derivative ℤ Fseries →
      ∀ n : ℕ,
        PowerSeries.coeff (2 * n + 1) A % 4 = 2 ∧
        PowerSeries.coeff (2 * n) A % 4 = 0 := by
  sorry

end OMA.S_oeis_a219431
