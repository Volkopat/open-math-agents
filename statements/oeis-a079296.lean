import Mathlib

/-!
# OEIS A079296: is `√p(n+1) - √p(n)` a zero sequence?

Source: https://oeis.org/A079296
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The entry notes that the sequence only makes sense if `n ↦ √p(n+1) - √p(n)` is a zero sequence
(tends to `0`), "a hard unsolved problem". Statement: `√p(n+1) - √p(n) → 0`, with `p(n)` the
`n`-th prime (`Nat.nth Nat.Prime`, 0-indexed; indexing does not affect the limit).
-/

namespace OMA.S_oeis_a079296

open Filter

/-- Consecutive prime square-root gaps tend to zero. -/
theorem main :
    Tendsto (fun n : ℕ => Real.sqrt (Nat.nth Nat.Prime (n + 1)) - Real.sqrt (Nat.nth Nat.Prime n))
      atTop (nhds 0) := by
  sorry

end OMA.S_oeis_a079296
