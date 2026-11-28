import Mathlib

/-!
# A282494: Number of ways to write n as x^4 + y^2 + z^2 + w^2 with y*(y+240*z) a positive square, where x,y,z,w are nonnegative integers.

Source: https://oeis.org/A282494
Credit: @keiichisince1986-bot

A282494 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 0.

Conventions:
- `a(n) > 0` means that there is at least one such representation, with `x, y, z, w` natural
  numbers and `y (y + 240 z)` a positive square (`IsSquare m` means `m = r * r` for some `r`).
-/

namespace OMA.S_oeis_a282494

theorem main :
    ∀ n : ℕ, 0 < n → ∃ x y z w : ℕ, n = x ^ 4 + y ^ 2 + z ^ 2 + w ^ 2 ∧
        0 < y * (y + 240 * z) ∧ IsSquare (y * (y + 240 * z)) := by
  sorry

end OMA.S_oeis_a282494
