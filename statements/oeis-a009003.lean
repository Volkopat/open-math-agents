import Mathlib

/-!
# A009003: Hypotenuse numbers (squares are sums of 2 nonzero squares)

Source: https://oeis.org/A009003
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

## Problem Statement
A positive integer `m` is a hypotenuse number (A009003) if `m^2` can be written as the sum
of two nonzero squares (`m^2 = a^2 + b^2` with `a, b > 0`).

Conjecture (from A009003): A positive integer `m` is a hypotenuse number if and only if
`∑_{k | m} μ(k) * i^k = 0`, where `μ` is the Möbius function (A008683) and `i` is the
imaginary unit.
-/

namespace OMA.S_oeis_a009003

/-- A positive integer `m` is a hypotenuse number if `m^2 = a^2 + b^2` for some `a, b > 0`. -/
def isHypotenuse (m : ℕ) : Prop :=
  0 < m ∧ ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ a ^ 2 + b ^ 2 = m ^ 2

theorem main :
    ∀ m : ℕ, 0 < m →
      (isHypotenuse m ↔
        (∑ k ∈ m.divisors, (ArithmeticFunction.moebius k : ℂ) * Complex.I ^ k) = 0) := by
  sorry

end OMA.S_oeis_a009003
