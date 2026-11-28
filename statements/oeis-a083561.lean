import Mathlib

/-!
# A083561: a(1) = 1 and for n>1: a(n) = n + Max{a(k): k<n, gcd(n,a(k))=1}.

Source: https://oeis.org/A083561
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: a(n) ~ n^2/3 as n -> infinity.
-/

namespace OMA.S_oeis_a083561

def seqRev : ℕ → List ℕ
  | 0 => [1]
  | n + 1 =>
    let prev := seqRev n
    let cands := prev.filter (fun v => Nat.Coprime (n + 2) v)
    let next := (n + 2) + cands.foldl max 0
    next :: prev

def a : ℕ → ℕ
  | 0 => 0
  | n + 1 => (seqRev n).headD 1

theorem main :
    Filter.Tendsto
      (fun n : ℕ => (a n : ℝ) / ((n : ℝ) ^ 2 / 3))
      Filter.atTop (nhds (1 : ℝ)) := by
  sorry

end OMA.S_oeis_a083561
