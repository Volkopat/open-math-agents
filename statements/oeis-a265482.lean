import Mathlib

/-!
# A265482: Numbers k such that 16^k - 4^k - 1 is prime.

Source: https://oeis.org/A265482
Credit: @prasledi

Conjecture (in the COMMENTS of A265482): the odd terms are not of the form 8*k+7.

Formalization notes:
* k is a term when 16^k - 4^k - 1 is prime. For k >= 1, 16^k >= 4^k + 1, so the natural
  subtraction is exact; for k = 0 the true value is -1 (not prime) and the truncated value 0 is not
  prime either. The definition reproduces the first terms 1, 2, 5 (#eval for k = 0..5).
* "The odd terms are not of the form 8*k+7": every odd term k satisfies k mod 8 ≠ 7.
  (The other comments, terms not of the form 5k+6, 9k+8, 7k+3(-1)^k, are proved facts and are
  not part of the conjecture.)
-/

namespace OMA.S_oeis_a265482

/-- The conjecture of A265482: no odd term is congruent to 7 modulo 8. -/
theorem main : ∀ k : ℕ, (16 ^ k - 4 ^ k - 1).Prime → Odd k → k % 8 ≠ 7 := by
  sorry

end OMA.S_oeis_a265482
