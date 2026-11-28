import Mathlib

/-!
# OEIS A376114 and A181795

Both sequences list their positive terms in increasing order, starting at
index 1. A376114 conjectures that each term is half its counterpart in A181795.

Sources: https://oeis.org/A376114 and https://oeis.org/A181795
(OEIS Foundation, CC BY-SA 4.0).
Credit: @Solitude1312
-/

namespace OMA.S_oeis_a376114

/-- The positive integers that are twice a square and divisible by their divisor count. -/
def inA376114 (m : ℕ) : Prop :=
  0 < m ∧ (∃ t : ℕ, m = 2 * t ^ 2) ∧ m.divisors.card ∣ m

/-- The odd and even divisor counts must themselves be odd and even divisors. -/
def inA181795 (k : ℕ) : Prop :=
  let o := (k.divisors.filter Odd).card
  let e := (k.divisors.filter Even).card
  0 < k ∧ Odd o ∧ o ∣ k ∧ Even e ∧ e ∣ k

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      Nat.nth inA376114 (n - 1) = Nat.nth inA181795 (n - 1) / 2 := by
  sorry

end OMA.S_oeis_a376114
