import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Prime.Basic

/-!
# Prime values of the decimal digit-square sum

A187553 lists the least prime with a given sum of squared decimal digits,
using zero when no prime realizes that sum. Michel Lagneau's conjecture
concerns the positive indices for which a prime exists.
See [OEIS A187553](https://oeis.org/A187553).
-/

namespace OMA.S_oeis_a187553

/-- Sum of the squares of the decimal digits of a natural number. -/
def digitSquareSum (p : ℕ) : ℕ := ((Nat.digits 10 p).map (fun d => d ^ 2)).sum

theorem main :
    ∀ n : ℕ, 0 < n →
      ((∃ p : ℕ, p.Prime ∧ digitSquareSum p = n) ↔ n ≠ 1 ∧ n ≠ 3) := by
  sorry

end OMA.S_oeis_a187553
