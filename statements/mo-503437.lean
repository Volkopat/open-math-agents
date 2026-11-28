import Mathlib

/-!
# Minimizing an expression with sum of digits

John C's boxed conjecture concerns positive integers, as in the author's numerical
test starting at 1. AfterMath gives a counterexample in the answers to the question.
Source: https://mathoverflow.net/questions/503437/minimizing-an-expression-with-sum-of-digits
Credit: @vubui
-/

namespace OMA.S_mo_503437

def digitSum (base n : ℕ) : ℤ := (Nat.digits base n).sum

def score (n : ℕ) : ℤ := 10 * digitSum 5 n + 12 * digitSum 2 n - 5 * digitSum 3 n

theorem main : ∀ n : ℕ, 0 < n → 0 ≤ score n ∧ (score n = 0 ↔ n = 19925000) := by
  sorry

end OMA.S_mo_503437
