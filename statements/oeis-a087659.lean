import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic

namespace OMA.S_oeis_a087659

/-- OEIS A087659 conjecture (Bill Gosper, Feb 04 2004):
For all `n : ℕ` and `0 ≤ i ≤ n`, the summand
`2 * C(n, i) * (n + 2*i + 3)! / ((i + 1)! * (i + 2)! * (n + 3)!)`
of `A087659(n)` is always an integer, i.e.
`(i + 1)! * (i + 2)! * (n + 3)!` divides `2 * C(n, i) * (n + 2*i + 3)!`. -/
theorem main :
    ∀ n i : ℕ, i ≤ n →
      ((i + 1).factorial * (i + 2).factorial * (n + 3).factorial) ∣
        (2 * Nat.choose n i * (n + 2 * i + 3).factorial) := by
  sorry

end OMA.S_oeis_a087659
