import Mathlib

/-!
# OEIS A069942: Picture-perfect numbers

Source: https://oeis.org/A069942
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

A positive integer `n` is called a picture-perfect number if the base-10 reversal
of `n` equals the sum of the base-10 reversals of the proper divisors of `n`.

Conjecture (OEIS entry): Every picture-perfect number is divisible by 3.
-/

namespace OMA.S_oeis_a069942

def rev10 (n : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 n).reverse

def IsPicturePerfect (n : ℕ) : Prop :=
  0 < n ∧ rev10 n = ∑ d ∈ n.properDivisors, rev10 d

theorem main :
    ∀ n : ℕ, IsPicturePerfect n → 3 ∣ n := by
  sorry

end OMA.S_oeis_a069942
