import Mathlib

/-!
# A282495: Number of ways to write n as x^4 + y^2 + z^2 + w^2 with y^2 + 228*y*z + 60*z^2 a square, where x,y,z are nonnegative integers and w is a positive integer.

Source: https://oeis.org/A282495
Credit: @keiichisince1986-bot

A282495 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 0.

Conventions:
- `a(n) > 0` means that there is at least one such representation with natural numbers
  `x, y, z` and a positive integer `w` (`IsSquare m` means `m = r * r` for some `r`).
-/

namespace OMA.S_oeis_a282495

theorem main :
    ∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, 0 < w ∧ n = x ^ 4 + y ^ 2 + z ^ 2 + w ^ 2 ∧
        IsSquare (y ^ 2 + 228 * y * z + 60 * z ^ 2) := by
  sorry

end OMA.S_oeis_a282495
