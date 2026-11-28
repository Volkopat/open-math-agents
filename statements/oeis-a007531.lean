import Mathlib

/-!
# A007531: a(n) = n*(n-1)*(n-2) (or n!/(n-3)!).

Source: https://oeis.org/A007531
Credit: @Sathy-21

The OEIS entry records the comment:

  Ed Pegg Jr conjectures that n^3 - n = k! has a solution if and only if n is 2, 3, 5 or 9
  (when k is 3, 4, 5 and 6).

This file states that conjecture in Pegg's own form, `n ^ 3 - n = k !`, for natural numbers
`n` and `k` (the sequence is indexed by natural numbers, as in the OEIS entry).
-/

namespace OMA.S_oeis_a007531

open Nat

/-- **Pegg's conjecture** (OEIS A007531): `n ^ 3 - n = k !` has a solution `k` if and only if
`n` is `2`, `3`, `5` or `9` (with `k = 3, 4, 5, 6` respectively).

Natural-number subtraction is safe here: `n ≤ n ^ 3` for every `n : ℕ` (both sides vanish at
`n = 0`, and `n ^ 3 = n * n * n ≥ n` for `n ≥ 1`), so `n ^ 3 - n` is the true integer value
`n ^ 3 - n = (n - 1) * n * (n + 1)` and never truncates to `0` spuriously. For `n = 0` and `n = 1`
it equals `0`, which is not a factorial, matching the conjecture's exclusion of those values. -/
theorem main :
    ∀ n : ℕ, (∃ k : ℕ, n ^ 3 - n = k !) ↔ n ∈ ({2, 3, 5, 9} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a007531
