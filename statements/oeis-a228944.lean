import Mathlib

/-!
# OEIS A228944: Differences of highly abundant numbers

Source: https://oeis.org/A228944
Credit: @gblacher2

Jaycob Coleman conjectured that every highly composite number `n` is the
difference of two highly abundant numbers, each at most `2 * n`.
-/

namespace OMA.S_oeis_a228944

/-- A positive integer whose divisor count exceeds that of every smaller
positive integer, as in OEIS A002182. -/
def IsHighlyComposite (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n → m.divisors.card < n.divisors.card

/-- A positive integer whose divisor sum exceeds that of every smaller
positive integer, as in OEIS A002093. -/
def IsHighlyAbundant (n : ℕ) : Prop :=
  0 < n ∧ ∀ m : ℕ, 0 < m → m < n →
    ArithmeticFunction.sigma 1 m < ArithmeticFunction.sigma 1 n

theorem main : ∀ n : ℕ, IsHighlyComposite n →
    ∃ a b : ℕ, IsHighlyAbundant a ∧ IsHighlyAbundant b ∧
      a ≤ 2 * n ∧ b ≤ 2 * n ∧ a = b + n := by
  sorry

end OMA.S_oeis_a228944
