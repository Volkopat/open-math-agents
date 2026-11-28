import Mathlib

/-!
# A069917: Base-10 digit sum conjecture for base-6 picture-perfect numbers

Source: https://oeis.org/A069917
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Title: A069917: In base 6, the reversal of n equals the sum of the reversals of the proper
divisors of n.

Statement:
A number n is called picture-perfect (in base 6) if the reversal of n in base 6 equals the
sum of the reversals in base 6 of the proper divisors of n. Conjecture: the digital sum of
the base-10 representation of every base-6 picture-perfect number equals 10.
-/

namespace OMA.S_oeis_a069917

/-- Reversal of `n` in base `b`. -/
def revBase (b n : ℕ) : ℕ :=
  Nat.ofDigits b (Nat.digits b n).reverse

/-- `n` is base-6 picture-perfect. -/
def IsBase6PicturePerfect (n : ℕ) : Prop :=
  0 < n ∧ revBase 6 n = ∑ d ∈ n.properDivisors, revBase 6 d

theorem main :
    ∀ n : ℕ, IsBase6PicturePerfect n → (Nat.digits 10 n).sum = 10 := by
  sorry

end OMA.S_oeis_a069917
