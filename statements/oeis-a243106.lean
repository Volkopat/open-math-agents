import Mathlib

/-!
# Digits of signed sums of consecutive powers (OEIS A243106)

Source: https://oeis.org/A243106 (OEIS Foundation, CC BY-SA 4.0).
R. J. Cano's conjecture uses arbitrary choices of signs and excludes exponent
zero. We take the general-base reading from the preceding OEIS comment and
from *OEIS Open*, Appendix A (https://arxiv.org/abs/2608.11941).
The convention `Nat.digits b 0 = []` agrees with the digit condition at zero,
since zero is an allowed digit.
-/

namespace OMA.S_oeis_a243106

/-- The sign at index `i` multiplies the power with exponent `i + 1`. -/
def signedSum (b n : ℕ) (signs : ℕ → ℤ) : ℤ :=
  ∑ i ∈ Finset.range n, signs i * (b : ℤ) ^ (i + 1)

/-- The four allowed base-`b` digits. -/
def AllowedDigit (b d : ℕ) : Prop :=
  d = 0 ∨ d = 1 ∨ d = b - 2 ∨ d = b - 1

theorem main : ∀ (b n : ℕ), 5 ≤ b → ∀ signs : ℕ → ℤ,
    (∀ i < n, signs i = -1 ∨ signs i = 1) →
    ∀ d ∈ Nat.digits b (signedSum b n signs).natAbs, AllowedDigit b d := by
  sorry

end OMA.S_oeis_a243106
