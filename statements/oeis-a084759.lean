import Mathlib

/-!
# A084759: Composite numbers in ascending order such that the difference of successive terms is unique.

Source: https://oeis.org/A084759
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

The sequence of first differences is 2, 3, 1, 4, 6, 5, 7, 8, 9, 11, 10, ...
Conjecture: every number is a term of this sequence. For every number r there
exists some k such that a(k) - a(k-1) = r.
-/

namespace OMA.S_oeis_a084759

def IsComposite (n : ℕ) : Prop := 1 < n ∧ ¬ n.Prime

noncomputable def a : ℕ → ℕ
  | 0 => 4
  | n + 1 =>
    sInf {m : ℕ | IsComposite m ∧ a n < m ∧ ∀ i < n, m - a n ≠ a (i + 1) - a i}

theorem main : ∀ r : ℕ, 1 ≤ r → ∃ k : ℕ, 1 ≤ k ∧ a k - a (k - 1) = r := by
  sorry

end OMA.S_oeis_a084759
