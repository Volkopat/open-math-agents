import Mathlib

/-!
A086398: a(1)=1; a(n)=a(n-1)+2 if n is in the sequence; a(n)=a(n-1)+2 if n and (n-1) are not in the sequence; a(n)=a(n-1)+4 if n is not in the sequence and (n-1) is in the sequence.

Source: https://oeis.org/A086398
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: -1 < n*(1 + sqrt(3)) - a(n) < 4 for n >= 1.
-/

namespace OMA.S_oeis_a086398

noncomputable def a : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | n + 2 =>
    let prev := a (n + 1)
    let nIn := ∃ k : Fin (n + 1), a (k.val + 1) = n + 2
    let prevIn := ∃ k : Fin (n + 1), a (k.val + 1) = n + 1
    if ¬ nIn ∧ prevIn then prev + 4 else prev + 2

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (-1 : ℝ) < (n : ℝ) * (1 + Real.sqrt 3) - (a n : ℝ) ∧
      (n : ℝ) * (1 + Real.sqrt 3) - (a n : ℝ) < 4 := by
  sorry

end OMA.S_oeis_a086398
