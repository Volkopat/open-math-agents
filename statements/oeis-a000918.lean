import Mathlib
import Mathlib.Combinatorics.Enumerative.Catalan.Basic

/-!
# A000918: a(n) = 2^n - 2.

Source: https://oeis.org/A000918
Credit: @rabdelaal

OEIS A000918 records the conjecture (L. Edson Jeffery) that for `n > 0`, `a(n) = 2 ^ n - 2`
is the least `m` such that the 2-adic valuation of the `m`-th Catalan number equals `n - 1`.
The valuation of `catalan m` is read as the exponent of `2` in `catalan m`,
`Nat.factorization (catalan m) 2`.
-/

namespace OMA.S_oeis_a000918

open Nat

/-- The conjecture recorded in OEIS A000918: `2 ^ n - 2` is the least `m` with
`catalan m` having 2-adic valuation `n - 1`. -/
theorem main : ∀ n > 0,
    (2 ^ n - 2) = sInf { m | (catalan m).factorization 2 = n - 1 } := by
  sorry

end OMA.S_oeis_a000918
