import Mathlib

/-!
# OEIS A308190: iterating A111234 from any n ≥ 5 reaches 5

Source: https://oeis.org/A308190
Credit: Sudharsan Rajendiran

A308190(n) is the number of steps to reach 5 when iterating `x ↦ A111234(x)` from `x = n`, where
A111234(1) = 2 and A111234(n) = (largest proper divisor of n) + (smallest prime divisor of n).
Ali Sada conjectured that every `n ≥ 5` eventually reaches 5; the entry records that this is easy
to show (composite `n > 5` map to smaller numbers, primes `> 5` drop in two steps, and nothing
`≥ 5` maps below 5). We state this proved result.

Conventions: for `n ≥ 2` the largest proper divisor of `n` is `n / minFac n`, so
`f n = n / minFac n + minFac n`; `f 1 = 2` (the value at `0` is irrelevant). `f^[k]` is the
`k`-fold iterate.
-/

namespace OMA.S_oeis_a308190

/-- OEIS A111234: `f 1 = 2`, and for `n ≥ 2`, `f n` = (largest proper divisor of `n`) +
(smallest prime divisor of `n`) `= n / minFac n + minFac n`. -/
def f (n : ℕ) : ℕ := if n = 1 then 2 else n / n.minFac + n.minFac

theorem main : ∀ n : ℕ, 5 ≤ n → ∃ k : ℕ, f^[k] n = 5 := by
  sorry

end OMA.S_oeis_a308190
