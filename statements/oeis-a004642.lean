import Mathlib

/-!
# A004642: Powers of 2 written in base 3.

Source: https://oeis.org/A004642
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a004642


/-- Conjecture (Sloane, 1973; open, see A102483): for n > 15, the base-3 expansion of 2^n contains
a digit 0. Since 2^n is not divisible by 3, its first and last base-3 digits are nonzero, so any
digit 0 is automatically strictly between the most and least significant digits. -/
theorem main : ∀ n : ℕ, 15 < n → 0 ∈ Nat.digits 3 (2 ^ n) := by
  sorry

end OMA.S_oeis_a004642
