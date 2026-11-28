import Mathlib

/-!
# A060464: Numbers that are not congruent to 4 or 5 mod 9.

Source: https://oeis.org/A060464
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a060464


/-- Conjecture (A060464): a nonnegative integer `n` is a sum of three (integer, possibly negative)
cubes if and only if `n` is not congruent to 4 or 5 modulo 9. The "only if" direction is a mod 9
obstruction; the "if" direction is open (for example for n = 114). -/
theorem main : ∀ n : ℕ,
    (∃ x y z : ℤ, (n : ℤ) = x ^ 3 + y ^ 3 + z ^ 3) ↔ (n % 9 ≠ 4 ∧ n % 9 ≠ 5) := by
  sorry

end OMA.S_oeis_a060464
