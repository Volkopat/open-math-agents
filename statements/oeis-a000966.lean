import Mathlib

/-!
# A000966: Irrationality of the generating function of impossible trailing-zero counts of n!

Source: https://oeis.org/A000966
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Title: A000966: n! never ends in this many 0's.

Statement:
The g.f. conjectured by Simon Plouffe in 1992 dissertation is not correct; the first
discrepancy is a(31) = 155, his g.f. gives 160. In fact, the g.f. for this sequence is not
rational; the first differences are bounded but not periodic.

Conventions:
- The number of trailing zeros of `n!` in base 10 equals `padicValNat 5 n.factorial`.
- `a(k)` is the `k`-th natural number (0-indexed) that never occurs as `padicValNat 5 n.factorial`.
- Non-rationality of the ordinary generating function is stated in `PowerSeries ℚ`.
-/

namespace OMA.S_oeis_a000966

/-- Number of trailing base-10 zeros of `n!`. -/
noncomputable def trailingZeros (n : ℕ) : ℕ :=
  padicValNat 5 n.factorial

/-- `m` never occurs as the number of trailing zeros of `n!`. -/
def IsSkippedZeroCount (m : ℕ) : Prop :=
  ∀ n : ℕ, trailingZeros n ≠ m

/-- The `k`-th term of OEIS A000966 (0-indexed). -/
noncomputable def a (k : ℕ) : ℕ :=
  Nat.nth IsSkippedZeroCount k

theorem main :
    ¬ ∃ P Q : Polynomial ℚ,
      Q ≠ 0 ∧ (PowerSeries.mk (fun k => (a k : ℚ))) * (Q : PowerSeries ℚ) = (P : PowerSeries ℚ) := by
  sorry

end OMA.S_oeis_a000966
