import Mathlib

/-!
# A231168: Number of ways to write n = x + y + z (x, y, z > 0) such that x^2 + y^2 + z^2 + z is a square, and 6*x + 1, 6*y - 1, 6*z -1 are all prime.

Source: https://oeis.org/A231168
Credit: @keiichisince1986-bot

A231168 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 5.

Conventions:
- `a(n) > 0` means that there is at least one such representation with positive integers
  `x, y, z` (`IsSquare m` means `m = r * r` for some `r`; since `y, z ≥ 1`, `6y - 1` and `6z - 1`
  are not truncated).
-/

namespace OMA.S_oeis_a231168

theorem main :
    ∀ n : ℕ, 5 < n → ∃ x y z : ℕ, 0 < x ∧ 0 < y ∧ 0 < z ∧ n = x + y + z ∧
        IsSquare (x ^ 2 + y ^ 2 + z ^ 2 + z) ∧ (6 * x + 1).Prime ∧ (6 * y - 1).Prime ∧
        (6 * z - 1).Prime := by
  sorry

end OMA.S_oeis_a231168
