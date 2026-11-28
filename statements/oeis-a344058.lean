import Mathlib

/-!
# A344058: Number of ways to write n as x + y + z with x*y + 2*y*z + 3*z*x a square, where x,y,z are positive integers with x or y a power of two (including 2^0 = 1).

Source: https://oeis.org/A344058
Credit: @keiichisince1986-bot

A344058 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 3.

Conventions:
- `a(n) > 0` means that there is at least one such representation with positive integers
  `x, y, z`, where `x` or `y` is `2^k` for some `k : ℕ` (`IsSquare m` means `m = r * r` for some
  `r`).
-/

namespace OMA.S_oeis_a344058

theorem main :
    ∀ n : ℕ, 3 < n → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ n = x + y + z ∧
        IsSquare (x * y + 2 * y * z + 3 * z * x) ∧ ((∃ k : ℕ, x = 2 ^ k) ∨ ∃ k : ℕ, y = 2 ^ k) := by
  sorry

end OMA.S_oeis_a344058
