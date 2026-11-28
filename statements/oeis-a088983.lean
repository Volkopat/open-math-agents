import Mathlib

/-!
# A088983: Six consecutive integers each having exactly two distinct prime factors

Source: https://oeis.org/A088983
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Numbers k such that each of the 6 consecutive numbers k through k+5 has exactly
two distinct prime factors.
Eggleton and MacDougall conjecture that A007774 contains no runs of 9 consecutive
integers, has only two runs of size 8 (at 141 and 212), two maximal runs of size 7
(at 323 and 2302), and one maximal run of size 6 (at 91), so A088983 is complete:
{91, 141, 142, 143, 212, 213, 214, 323, 324, 2302, 2303}.
-/

namespace OMA.S_oeis_a088983

theorem main :
    ∀ k : ℕ,
      (∀ i < 6, (k + i).primeFactors.card = 2) ↔
      k ∈ ({91, 141, 142, 143, 212, 213, 214, 323, 324, 2302, 2303} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a088983
