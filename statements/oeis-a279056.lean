import Mathlib

/-!
# A279056: Number of ways to write n as w^2 + x^2 + y^2 + z^2 with w a positive integer and x,y,z nonnegative integers such that x^3 + 4*y*z*(y-z) is a square.

Source: https://oeis.org/A279056
Credit: @keiichisince1986-bot

A279056 is the sequence `a(n)` named in the title. The entry states:
Conjecture: (i) a(n) > 0 for all n > 0. [Only the first claim of part (i), a(n) > 0, is formalized here; the list of n with a(n) = 1
and the other parts are not.]

Conventions:
- All variables are natural numbers (nonnegative integers) unless stated otherwise; `(…).IsSquare` is
  Mathlib's `IsSquare`. The representation is ordered, which does not matter for existence.
- The expression may be negative, so it is computed in `ℤ`; a negative integer is never a square.
-/

namespace OMA.S_oeis_a279056

theorem main :
    ∀ n : ℕ, 0 < n → ∃ w x y z : ℕ, 0 < w ∧ n = w ^ 2 + x ^ 2 + y ^ 2 + z ^ 2 ∧
      IsSquare (x ^ 3 + 4 * y * z * (y - z) : ℤ) := by
  sorry

end OMA.S_oeis_a279056
