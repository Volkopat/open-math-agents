import Mathlib

/-!
# A083834: Palindromes of the form 5p + 1 where p is also a palindrome

Source: https://oeis.org/A083834
Credit: @gaudinfrederic

Conjecture (Michael S. Branicky, in the comments of A083834): every term of the
sequence contains only the digits {0, 1, 5, 6}; equivalently, if `p` is a decimal
palindrome and `5 * p + 1` is also a decimal palindrome, then every decimal digit
of `5 * p + 1` belongs to {0, 1, 5, 6}.

## Encoding

* "Term of the sequence" means a value `q = 5 * p + 1` where `p` and `q` are both
  decimal palindromes (`List.Palindrome (Nat.digits 10 _)`). Every element of
  `Nat.digits 10 q` must lie in `{0, 1, 5, 6}` — including the one-digit cases
  `q ∈ {1, 6}`, whose single digits already satisfy the claim.
-/

namespace OMA.S_oeis_a083834

/-- The conjecture on A083834: every decimal digit of `5 * p + 1`, when both `p`
and `5 * p + 1` are palindromes, is one of `0, 1, 5, 6`. -/
theorem main : ∀ p : ℕ, List.Palindrome (Nat.digits 10 p) →
    List.Palindrome (Nat.digits 10 (5 * p + 1)) →
    ∀ d ∈ Nat.digits 10 (5 * p + 1), d ∈ ({0, 1, 5, 6} : Finset ℕ) := by
  sorry

end OMA.S_oeis_a083834
