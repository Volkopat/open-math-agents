import Mathlib.Data.Nat.Basic

/-!
# The decimal remainder conjecture for A284814

Max Alekseyev conjectured that no positive integer with at least 15 digits
has successive remainders modulo 2, 3, ..., n+1 equal to its decimal digits
from left to right. Here n is the number of digits of the candidate k, as in
the worked example, the reference program and the companion entry A266181.

Source: https://oeis.org/A284814 and https://oeis.org/A266181.
OEIS text, CC BY-SA 4.0. Formalization by @pmaster with Codex.
-/

namespace OMA.S_oeis_a284814

def MatchesDigits (n k : ℕ) : Prop :=
  10^(n-1) ≤ k ∧ k < 10^n ∧ ∀ j, j < n → k / 10^j % 10 = k % (n+1-j)

theorem main : ∀ n k : ℕ, 15 ≤ n → ¬ MatchesDigits n k := by
  sorry

end OMA.S_oeis_a284814

