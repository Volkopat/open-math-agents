import Mathlib

/-!
# OEIS A032594: consecutive prime palindromes

Source: https://oeis.org/A032594
`a n` is the greater of two consecutive palindromes both of which are prime
(3, 191, 383, 797, …). Conjecture: the sequence is finite.

Conventions. A palindrome is a natural number whose decimal digit list is a palindrome.
Two palindromes `p < q` are consecutive when no palindrome lies strictly between them.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a032594

/-- `n` is a decimal palindrome. -/
def IsPal (n : ℕ) : Prop := (Nat.digits 10 n).reverse = Nat.digits 10 n

theorem main :
    {q : ℕ | ∃ p < q, IsPal p ∧ IsPal q ∧ p.Prime ∧ q.Prime ∧
      ∀ r, p < r → r < q → ¬ IsPal r}.Finite := by
  sorry

end OMA.S_oeis_a032594
