import Mathlib

/-!
# A090072: Numbers with eleven palindromes in their Reverse and Add! trajectory

Source: https://oeis.org/A090072
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Only two numbers are known whose Reverse and Add! trajectory contains twelve
palindromes: 10000 and 10001. It is conjectured that these are the only such
numbers and that no Reverse and Add! trajectory contains more than twelve
palindromes.
-/

namespace OMA.S_oeis_a090072

/-- Base-10 digit reversal of a natural number. -/
def revNum (n : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 n).reverse

/-- One step of the Reverse and Add! process. -/
def revAdd (n : ℕ) : ℕ :=
  n + revNum n

/-- Predicate that a natural number is a base-10 palindrome. -/
def isPalindrome (n : ℕ) : Prop :=
  (Nat.digits 10 n).reverse = Nat.digits 10 n

/-- Set of step indices at which the Reverse and Add! trajectory of n is a palindrome. -/
def palindromeSteps (n : ℕ) : Set ℕ :=
  {k : ℕ | isPalindrome (revAdd^[k] n)}

theorem main :
    (∀ n : ℕ, 1 ≤ n → (palindromeSteps n).Finite ∧ (palindromeSteps n).ncard ≤ 12) ∧
    (∀ n : ℕ, 1 ≤ n → ((palindromeSteps n).ncard = 12 ↔ n = 10000 ∨ n = 10001)) := by
  sorry

end OMA.S_oeis_a090072
