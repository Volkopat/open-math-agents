import Mathlib

/-!
# A088113: Digit reversal of 11^n divided by 11

Source: https://oeis.org/A088113
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

a(n) = (digit reversal of 11^n in base 10) / 11 for n >= 1.
Conjecture: There are only finitely many palindromic terms in this sequence.
-/

namespace OMA.S_oeis_a088113

/-- `a(n)` is the base-10 digit reversal of `11^n`, divided by `11`. -/
def a (n : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 (11 ^ n)).reverse / 11

/-- `m` is a base-10 palindrome. -/
def IsPalindrome10 (m : ℕ) : Prop :=
  (Nat.digits 10 m).reverse = Nat.digits 10 m

theorem main :
    Set.Finite {n : ℕ | 1 ≤ n ∧ IsPalindrome10 (a n)} := by
  sorry

end OMA.S_oeis_a088113
