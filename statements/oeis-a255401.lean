import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Set.Finite.Basic
import Mathlib.NumberTheory.Divisors

/-!
# A255401: Divisor ranks equal the number of binary ones

Source: https://oeis.org/A255401
Credit: @Alienchisel

For each positive divisor d of m, the number of divisors at most d is
its one-based rank. The sequence consists of positive m for which the
number of ones in each divisor's binary expansion is that divisor's rank.
The two conjectures assert infinitude and a maximum divisor count of eight.
-/

namespace OMA.S_oeis_a255401

/-- Each divisor's binary weight equals its position in increasing divisor order. -/
def HasDivisorDigitProperty (m : ℕ) : Prop :=
  0 < m ∧ ∀ d ∈ m.divisors,
    (Nat.digits 2 d).count 1 = (m.divisors.filter fun e => e ≤ d).card

theorem main :
    Set.Infinite {m : ℕ | HasDivisorDigitProperty m} ∧
    IsGreatest {k : ℕ | ∃ m : ℕ, HasDivisorDigitProperty m ∧ m.divisors.card = k} 8 := by
  sorry

end OMA.S_oeis_a255401
