import Mathlib

/-!
# A088703: Numbers of form x^5 + y^5, x,y > 0 and x <> y.

Source: https://oeis.org/A088703
Credit: @divmxnd0x

Conjecture (stated in A088703): no number can be expressed as the sum of two 5th powers in more
than one way.

Formalization notes:
* A representation is an unordered pair of positive integers `{x, y}`, written with `x ≤ y`;
  "at most one way" means that two such representations of the same number coincide.
-/

namespace OMA.S_oeis_a088703

/-- No number is a sum of two positive fifth powers in two different ways. -/
theorem main : ∀ a b c d : ℕ, 0 < a → a ≤ b → 0 < c → c ≤ d →
    a ^ 5 + b ^ 5 = c ^ 5 + d ^ 5 → a = c ∧ b = d := by
  sorry

end OMA.S_oeis_a088703
