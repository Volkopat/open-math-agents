import Mathlib

/-!
# A343897: Number of ways to write n as 2*x + y + z with x,y,z positive integers such that 16*x^2*y^2 + 19*y^2*z^2 + 29*z^2*x^2 is a square.

Source: https://oeis.org/A343897
Credit: @keiichisince1986-bot

A343897 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 3. (Verified for all n = 4..10000.)

Conventions:
- `a(n) > 0` means that there is at least one such representation with positive integers
  `x, y, z` (`IsSquare m` means `m = r * r` for some `r`).
-/

namespace OMA.S_oeis_a343897

theorem main :
    ∀ n : ℕ, 3 < n → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ n = 2 * x + y + z ∧
        IsSquare (16 * x ^ 2 * y ^ 2 + 19 * y ^ 2 * z ^ 2 + 29 * z ^ 2 * x ^ 2) := by
  sorry

end OMA.S_oeis_a343897
