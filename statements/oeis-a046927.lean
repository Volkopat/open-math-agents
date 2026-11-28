import Mathlib

/-!
# A046927: Number of ways to express 2n+1 as p+2q where p and q are primes

Source: https://oeis.org/A046927
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjectures:
1. Lemoine's conjecture (also known as Levy's conjecture):
   Any odd integer greater than 5 can be written as p + 2*q where p and q are primes.
2. Second conjecture in the entry (after an observation on the SeqFan list):
   1, 3, 5, 59, and 151 are the only odd integers n such that n + 2*p and n + 2*q are
   both composite for all primes p, q with n = p + 2*q.
-/

namespace OMA.S_oeis_a046927

/-- Lemoine's conjecture and the second conjecture of the entry on representations n = p + 2*q. -/
theorem main :
    (∀ n : ℕ, 5 < n → Odd n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + 2 * q) ∧
    ({n : ℕ | Odd n ∧ ∀ p q : ℕ, Nat.Prime p → Nat.Prime q → n = p + 2 * q →
        ¬ Nat.Prime (n + 2 * p) ∧ ¬ Nat.Prime (n + 2 * q)} = ({1, 3, 5, 59, 151} : Set ℕ)) := by
  sorry

end OMA.S_oeis_a046927
