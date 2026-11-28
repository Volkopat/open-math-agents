import Mathlib

/-!
# A077402: Reverse and Add! carried out in base 3; number of steps needed to reach a palindrome, or -1 if no palindrome is ever reached.

Source: https://oeis.org/A077402
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Base-3 analog of A066057 (base 2), A075685 (base 4) and A033665 (base 10).
a(103) = -1 is a conjecture (cf. A066450, A077408).
-/

namespace OMA.S_oeis_a077402

/-- One Reverse-and-Add step in base 3. -/
def revAdd3 (n : ℕ) : ℕ :=
  n + Nat.ofDigits 3 (Nat.digits 3 n).reverse

/-- Predicate that `n` is a palindrome in base 3. -/
def isPalBase3 (n : ℕ) : Prop :=
  (Nat.digits 3 n).reverse = Nat.digits 3 n

theorem main :
    ∀ k : ℕ, ¬ isPalBase3 (Nat.iterate revAdd3 k 103) := by sorry

end OMA.S_oeis_a077402
