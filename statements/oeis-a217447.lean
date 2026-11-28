import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A217447: Number of n x n permutation matrices that disconnect their zeros.

Source: https://oeis.org/A217447
Credit: @LDJAI

The OEIS entry gives an explicit factorial-sum formula for the sequence;
we use that published formula, not the conjectured recurrence, as its
definition. The formula is attributed to the solution of Problem 1877
by D. Edelman and A. Edelman, Mathematics Magazine 85 (2012), 297–298.
The offset is 2, so the five-lag recurrence is asserted for n ≥ 7.
All calculations are in ℤ so negative coefficients and empty sums have
their usual meanings.
-/

namespace OMA.S_oeis_a217447

open scoped BigOperators

def a (n : ℕ) : ℤ :=
  4 * (∑ i ∈ Finset.range (n - 2), ((i+1).factorial : ℤ))
    - 2 * ((n : ℤ) - 2) * (∑ i ∈ Finset.range (n - 3), (i.factorial : ℤ))
    + 2 * (∑ i ∈ Finset.range (n - 3), ((i+1).factorial : ℤ)) + 2

theorem main : ∀ n : ℕ, 7 ≤ n →
    2*a n + 2*(-(n : ℤ)-1)*a (n-1) + (6*(n : ℤ)-11)*a (n-2) +
    (-5*(n : ℤ)+14)*a (n-3) + 3*a (n-4) + ((n : ℤ)-6)*a (n-5) = 0 := by
  sorry

end OMA.S_oeis_a217447
