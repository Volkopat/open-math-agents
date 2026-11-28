import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Finite.Basic

/-!
# Finiteness of squares with decimal digit average above 8.3

Source: M. F. Hasler, OEIS A362264, https://oeis.org/A362264 (CC BY-SA 4.0).
Credit: @jatin6

The conjecture in the comments concerns every natural number whose square has
digit average strictly above 8.3. The inequality below clears the denominator.
For zero the two sides are zero, so the strict inequality excludes it.
-/

namespace OMA.S_oeis_a362264

theorem main : Set.Finite {n : ℕ |
    83 * (Nat.digits 10 (n ^ 2)).length < 10 * (Nat.digits 10 (n ^ 2)).sum} := by
  sorry

end OMA.S_oeis_a362264
