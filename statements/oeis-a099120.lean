import Mathlib

/-!
# A099120: Tutescu's conjecture for the Kempner function

Source: https://oeis.org/A099120
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) is the least m such that n = S(k) = S(k+m) for some k, where S is the Kempner function
A002034 (the smallest positive integer m such that k divides m!).
Tutescu's conjecture: The equation S(k) = S(k+1) has no solutions for k >= 1
(equivalently, a(n) > 1 for all n).
-/

namespace OMA.S_oeis_a099120

noncomputable def kempner (k : ℕ) : ℕ :=
  sInf {m : ℕ | 1 ≤ m ∧ k ∣ m.factorial}

theorem main :
    ∀ k : ℕ, 1 ≤ k → kempner k ≠ kempner (k + 1) := by
  sorry

end OMA.S_oeis_a099120
