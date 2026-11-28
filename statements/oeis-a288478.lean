import Mathlib.Logic.Function.Iterate
import Mathlib.Data.Int.Basic

/-!
# Kimberling's iterate-length conjecture for A288478

The seed 00 has iteration index zero. Each pass reads the old word from left
to right, replaces disjoint occurrences of 00 by 0101 and each 1 by 110,
and copies an unmatched zero. Kimberling conjectured that the successive
lengths are A182780. We use that entry's integer recurrence and initial values.

Sources: https://oeis.org/A288478 and https://oeis.org/A182780.
Formalization: @Liungang, with OpenAI Codex.
-/

namespace OMA.S_oeis_a288478

/-- One replacement pass, with false denoting zero. -/
def rewriteWord : List Bool → List Bool
  | [] => []
  | [false] => [false]
  | false :: false :: xs => false :: true :: false :: true :: rewriteWord xs
  | false :: true :: xs => false :: true :: true :: false :: rewriteWord xs
  | true :: xs => true :: true :: false :: rewriteWord xs

/-- The n-th word starting from 00. -/
def word (n : ℕ) : List Bool := (rewriteWord^[n]) [false, false]

/-- A182780, using the recurrence given in the OEIS entry. -/
def a : ℕ → ℤ
  | 0 => 2
  | 1 => 4
  | 2 => 8
  | n + 3 => 3 * a (n + 2) - a (n + 1) - a n

theorem main : ∀ n : ℕ, ((word n).length : ℤ) = a n := by
  sorry

end OMA.S_oeis_a288478
