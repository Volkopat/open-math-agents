import OMAStatements.S_oeis_a001013
import Mathlib

/-! Appending (k-1)! to a factorial product for k gives a decomposition of k!.
A prime k cannot occur on the decomposition side, since no smaller factorial
contains k. Only the reverse implication for composite indices remains. -/
namespace OMA.R_oeis_a001013_R1
open OMA.S_oeis_a001013

def H1 : Prop := ∀ k : ℕ, 3 ≤ k →
  (IsJordanPolya k → FactorialOfSmaller k) ∧ (FactorialOfSmaller k → ¬ k.Prime)

def H2 : Prop := ∀ k : ℕ, 3 ≤ k → ¬ k.Prime → k ≠ 9 → k ≠ 10 →
  FactorialOfSmaller k → IsJordanPolya k

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a001013.main := by
  intro structural reverse k positive outside
  by_cases one : k = 1
  · subst k
    constructor
    · intro _
      exact ⟨0, by simp, by simp⟩
    · intro _
      exact ⟨0, by simp, by simp⟩
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at outside
    have large : 3 ≤ k := by omega
    obtain ⟨forward, composite⟩ := structural k large
    exact ⟨forward, fun h => reverse k large (composite h) outside.2.1 outside.2.2 h⟩

end OMA.R_oeis_a001013_R1
