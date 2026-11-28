import Mathlib

/-!
# A228431: Number of ordered ways to write n = x + y (x, y > 0) with p(3, x) + p(6, y) prime, where p(3, k) denotes the triangular number k*(k+1)/2 and p(6, k) denotes the hexagonal number k*(2*k-1) = p(3, 2*k-1).

Source: https://oeis.org/A228431
Credit: @keiichisince1986-bot

A228431 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 1.

Conventions:
- `p(3, x) = x (x + 1) / 2` (exact in `ℕ`, as `x (x + 1)` is even) and `p(6, y) = y (2 y - 1)`
  (with `y ≥ 1`, so `2 y - 1` is not truncated).
- `a(n) > 0` means that there are positive integers `x, y` with `n = x + y` and
  `p(3, x) + p(6, y)` prime.
-/

namespace OMA.S_oeis_a228431

theorem main :
    ∀ n : ℕ, 1 < n → ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ n = x + y ∧
        (x * (x + 1) / 2 + y * (2 * y - 1)).Prime := by
  sorry

end OMA.S_oeis_a228431
