import Mathlib

/-!
# A069748: Classification of multi-digit palindromes whose cubes are palindromes

Source: https://oeis.org/A069748
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A069748: Numbers k such that k and k^3 are both palindromes.

Statement:
For n >= 5 (i.e., terms k >= 10), there are no terms with digit sum 5. Conjecture: all terms
k >= 10 belong to one of 3 disjoint classes of the following forms:
10^m + 1, 10^(2*t) + 10^t + 1 (t > 0), and (10^u + 1)*(10^v + 1) (u, v > 0),
with digit sums 2, 3 and 4 correspondingly.
-/

namespace OMA.S_oeis_a069748

/-- `m` is a base-10 palindrome. -/
def IsPalindrome10 (m : ℕ) : Prop :=
  (Nat.digits 10 m).reverse = Nat.digits 10 m

theorem main :
    ∀ k : ℕ, 10 ≤ k → IsPalindrome10 k → IsPalindrome10 (k ^ 3) →
      (∃ m : ℕ, 1 ≤ m ∧ k = 10 ^ m + 1) ∨
      (∃ t : ℕ, 1 ≤ t ∧ k = 10 ^ (2 * t) + 10 ^ t + 1) ∨
      (∃ u v : ℕ, 1 ≤ u ∧ 1 ≤ v ∧ k = (10 ^ u + 1) * (10 ^ v + 1)) := by
  sorry

end OMA.S_oeis_a069748
