import Mathlib

/-!
# A090534: Least n-digit prime in which every two-digit substring is prime

Source: https://oeis.org/A090534
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Least n-digit prime in which every two-digit string is also a prime, or 0 if no
such number exists.
Conjecture: sequence is infinite (i.e., there are infinitely many n >= 2 for
which such an n-digit prime exists).
-/

namespace OMA.S_oeis_a090534

/-- Predicate that p is an n-digit prime whose every contiguous 2-digit base-10
substring forms a prime number. -/
def isTwoDigitPrimeString (n p : ℕ) : Prop :=
  let d := (Nat.digits 10 p).reverse
  Nat.Prime p ∧
  d.length = n ∧
  ∀ i : ℕ, i + 1 < n → Nat.Prime (10 * d.getD i 0 + d.getD (i + 1) 0)

theorem main :
    Set.Infinite {n : ℕ | 2 ≤ n ∧ ∃ p : ℕ, isTwoDigitPrimeString n p} := by
  sorry

end OMA.S_oeis_a090534
