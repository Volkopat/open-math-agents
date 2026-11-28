import Mathlib

/-!
# A004977: Sum of digits of n-th term in Look and Say sequence A005150

Source: https://oeis.org/A004977
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture:
In the Look-and-Say sequence A005150 (1, 11, 21, 1211, 111221, ...), the ratio of the
sum of digits A004977(n) to the number of digits A005341(n) tends to a finite constant
as n -> ∞.
-/

namespace OMA.S_oeis_a004977

open Filter

/-- Run-length encoding helper for Look-and-Say. -/
def rleAux : List ℕ → ℕ → ℕ → List ℕ
  | [], d, c => [c, d]
  | x :: xs, d, c =>
    if x = d then rleAux xs d (c + 1)
    else c :: d :: rleAux xs x 1

/-- One step of the Look-and-Say sequence. -/
def nextLookAndSay : List ℕ → List ℕ
  | [] => []
  | x :: xs => rleAux xs x 1

/-- The n-th term of the Look-and-Say sequence A005150 (0-indexed: [1], [1,1], [2,1], ...). -/
def lookAndSay : ℕ → List ℕ
  | 0 => [1]
  | n + 1 => nextLookAndSay (lookAndSay n)

/-- Conjecture: The mean digit value (sum of digits / number of digits) of lookAndSay(n) converges. -/
theorem main :
    ∃ L : ℝ,
      Tendsto
        (fun n : ℕ => ((lookAndSay n).sum : ℝ) / ((lookAndSay n).length : ℝ))
        atTop (nhds L) := by
  sorry

end OMA.S_oeis_a004977
