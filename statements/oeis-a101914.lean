import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Rat.Init
import Mathlib.RingTheory.PowerSeries.Basic

open scoped BigOperators

namespace OMA.S_oeis_a101914

/-- OEIS A101914: `a(0) = 1` and `a(n) = -∑_{k=0}^{⌊(n-1)/4⌋} a(k) * a(n - 4k - 1)` for `n ≥ 1`,
whose ordinary generating function satisfies `A(x) = 1 / (1 + x * A(x^4))`. -/
def a101914 : ℕ → ℤ
  | 0 => 1
  | n + 1 => -∑ k : Fin (n / 4 + 1), a101914 k.val * a101914 (n - 4 * k.val)
termination_by n => n
decreasing_by
  · have := k.isLt; omega
  · omega

/-- Conjecture (Ralf Stephan, May 17 2007; OEIS A101914): The sequence `a101914` has a
rational ordinary generating function over `ℚ`, i.e., there exist polynomials `P, Q ∈ ℚ[X]`
with `P ≠ 0` such that `P(X) * (∑_{n ≥ 0} a101914(n) * X^n) = Q(X)` in `ℚ⟦X⟧`. -/
theorem main :
    ∃ P Q : Polynomial ℚ, P ≠ 0 ∧
      (P : PowerSeries ℚ) * PowerSeries.mk (fun n => (a101914 n : ℚ)) = (Q : PowerSeries ℚ) := by
  sorry

end OMA.S_oeis_a101914
