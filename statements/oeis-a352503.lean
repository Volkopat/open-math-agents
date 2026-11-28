import Mathlib

/-!
# A352503: Number of ways to write n as w^3 + 2*x^3 + 4*y^3 + 5*z^3 + t^6, where w is a positive integer, and x,y,z,t are nonnegative integers.

Source: https://oeis.org/A352503
Credit: @keiichisince1986-bot

A352503 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 0.

Conventions:
- `a(n) > 0` means that there is at least one such representation, with `w ≥ 1` and
  `x, y, z, t` natural numbers.
-/

namespace OMA.S_oeis_a352503

theorem main :
    ∀ n : ℕ, 0 < n → ∃ w x y z t : ℕ, 0 < w ∧
        n = w ^ 3 + 2 * x ^ 3 + 4 * y ^ 3 + 5 * z ^ 3 + t ^ 6 := by
  sorry

end OMA.S_oeis_a352503
