import Mathlib

/-!
# A085298: a(n) is the smallest exponent x such that prime(n)^x when reversed is a prime.

Source: https://oeis.org/A085298
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

It is conjectured that for every n such exponent exists.
-/

namespace OMA.S_oeis_a085298

def rev10 (n : ℕ) : ℕ :=
  Nat.ofDigits 10 (Nat.digits 10 n).reverse

theorem main : ∀ p : ℕ, p.Prime → ∃ x : ℕ, 1 ≤ x ∧ (rev10 (p ^ x)).Prime := by
  sorry

end OMA.S_oeis_a085298
