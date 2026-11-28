import Mathlib

/-!
# OEIS A230563: sums of three positive `n`-th powers in two ways

Source: https://oeis.org/A230563
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the smallest number that is the sum of three positive `n`-th powers in at least two
ways. The entry notes that if the Lander–Parkin–Selfridge conjecture is true then `a(n)` does not
exist for `n ≥ 7`; `main` states this non-existence: for `n ≥ 7` no number is a sum of three
positive `n`-th powers in two different ways.

Conventions:
* A way is a multiset `{x, y, z}` of positive integers, i.e. a triple `x ≤ y ≤ z`.
-/

namespace OMA.S_oeis_a230563

/-- For `n ≥ 7`, sums of three positive `n`-th powers are unique up to order. -/
theorem main : ∀ n : ℕ, 7 ≤ n → ∀ x y z u v w : ℕ,
    0 < x → x ≤ y → y ≤ z → 0 < u → u ≤ v → v ≤ w →
    x ^ n + y ^ n + z ^ n = u ^ n + v ^ n + w ^ n → (x, y, z) = (u, v, w) := by
  sorry

end OMA.S_oeis_a230563
