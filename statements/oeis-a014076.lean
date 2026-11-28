import Mathlib

/-!
# A014076: Odd nonprimes

Source: https://oeis.org/A014076
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
There exist infinitely many odd nonprimes `m` such that `m + 6` is also an odd nonprime,
`3 ∣ m`, and `m / 3` and `(m + 6) / 3` are twin primes.

Conventions:
- An odd nonprime is a natural number `m` satisfying `Odd m ∧ ¬ Nat.Prime m`.
-/

namespace OMA.S_oeis_a014076

def IsOddNonPrime (m : ℕ) : Prop :=
  Odd m ∧ ¬ Nat.Prime m

theorem main :
    Set.Infinite
      {m : ℕ | IsOddNonPrime m ∧ IsOddNonPrime (m + 6) ∧
        3 ∣ m ∧ Nat.Prime (m / 3) ∧ Nat.Prime ((m + 6) / 3)} := by
  sorry

end OMA.S_oeis_a014076
