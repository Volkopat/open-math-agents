import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Int.Basic

/-!
# OEIS A054116

Mathar's recurrence for the diagonal of A054115, with the range
`n ≥ 4` specified by Eiver Rodríguez in the OEIS entry.
The sequence uses Robert G. Wilson's factorial-sum formula.

Source: https://oeis.org/A054116
-/

namespace OMA.S_oeis_a054116

/-- The sequence has offset one. At indices at least two it is a sum of factorials. -/
def a (n : ℕ) : ℤ :=
  if n = 1 then 1 else ∑ k ∈ Finset.Icc 2 n, (k.factorial : ℤ)

theorem main : ∀ n : ℕ, 4 ≤ n →
    a n - ((n : ℤ) + 1) * a (n - 1) + (n : ℤ) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a054116
