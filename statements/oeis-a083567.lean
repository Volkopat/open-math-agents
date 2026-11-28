import Mathlib

/-!
# A083567: Let B(k) be the number of binary digits in k equal to 1. This is the sequence of positive integers k such that 2B(k)=B(k^2).

Source: https://oeis.org/A083567
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture: The counting function p(n) satisfies p(n)=c n/log n + o(n/log n).
-/

namespace OMA.S_oeis_a083567

def popcount (k : ℕ) : ℕ :=
  (Nat.digits 2 k).sum

def countFunc (n : ℕ) : ℕ :=
  ((Finset.Icc 1 n).filter (fun k => 2 * popcount k = popcount (k ^ 2))).card

theorem main :
    ∃ c : ℝ, 0 < c ∧
      Filter.Tendsto
        (fun n : ℕ => (countFunc n : ℝ) / ((n : ℝ) / Real.log (n : ℝ)))
        Filter.atTop (nhds c) := by
  sorry

end OMA.S_oeis_a083567
