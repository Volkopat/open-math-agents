import Mathlib

/-!
# A090940: a(n) = least odd prime distinct from earlier elements such that average of first n elements is prime.

Source: https://oeis.org/A090940
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjectured to include all odd prime numbers.
-/

namespace OMA.S_oeis_a090940

noncomputable def nextTerm (l : List ℕ) : ℕ :=
  sInf {p : ℕ | Nat.Prime p ∧ p ≠ 2 ∧ p ∉ l ∧
    (l.length + 1) ∣ (l.sum + p) ∧ Nat.Prime ((l.sum + p) / (l.length + 1))}

noncomputable def prefSeq : ℕ → List ℕ
  | 0 => []
  | n + 1 => prefSeq n ++ [nextTerm (prefSeq n)]

noncomputable def a (n : ℕ) : ℕ :=
  nextTerm (prefSeq n)

theorem main :
    ∀ p : ℕ, Nat.Prime p → p ≠ 2 → ∃ n : ℕ, a n = p := by
  sorry

end OMA.S_oeis_a090940
