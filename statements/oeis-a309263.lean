import Mathlib

/-! OEIS A309263, referring to A140110.
Source: https://oeis.org/A309263 and https://oeis.org/A140110
Credit: @etaubman

A pair of positive integers has consecutive numerator and denominator after
cancellation precisely when the pair can be written as `(g*t, g*(t+1))`.
-/

namespace OMA.S_oeis_a309263

def ConsecutiveRatios (N : ℕ) : Prop :=
  ∀ a b : ℕ, a ∣ N → b ∣ N → a < b →
    (∀ c : ℕ, c ∣ N → a < c → c < b → False) →
    ∃ g t : ℕ, a = g * t ∧ b = g * (t + 1)

/-- Every number 4·5ⁿ belongs to A309263. -/
theorem main : ∀ n : ℕ, ¬6 ∣ 4 * 5 ^ n ∧ ConsecutiveRatios (4 * 5 ^ n) := by
  sorry

end OMA.S_oeis_a309263
