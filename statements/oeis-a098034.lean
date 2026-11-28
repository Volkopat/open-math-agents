import Mathlib

/-!
# A098034: Insolite numbers (divisible by both the sum and product of squares of their digits)

Source: https://oeis.org/A098034
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Numbers that are divisible both by the sum and by the product of the squares of their digits.
Conjecture (De Koninck and Doyon): 1111111111131111131111111111175 is the smallest insolite
number containing the digit 5.
-/

namespace OMA.S_oeis_a098034

def sumSqDigits (n : ℕ) : ℕ :=
  ((Nat.digits 10 n).map (fun d => d ^ 2)).sum

def prodSqDigits (n : ℕ) : ℕ :=
  ((Nat.digits 10 n).map (fun d => d ^ 2)).prod

def IsInsolite (n : ℕ) : Prop :=
  0 < n ∧ sumSqDigits n ∣ n ∧ prodSqDigits n ∣ n

theorem main :
    IsLeast {n : ℕ | IsInsolite n ∧ 5 ∈ Nat.digits 10 n} 1111111111131111131111111111175 := by
  sorry

end OMA.S_oeis_a098034
