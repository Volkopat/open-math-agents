import Mathlib

/-!
# A228428: Number of ways to write n = x + y (x, y > 0) with p(99, x) + p(100, y) prime, where p(m, k) denotes the m-gonal number (m-2)*k*(k-1)/2 + k.

Source: https://oeis.org/A228428
Credit: @keiichisince1986-bot

A228428 is the sequence `a(n)` named in the title. The entry states:
Conjecture: a(n) > 0 for all n > 1.

Conventions:
- `polygonal m k` is the `m`-gonal number `(m - 2) k (k - 1) / 2 + k`; `k (k - 1)` is even, so the
  division in `ℕ` is exact.
- `a(n) > 0` means that there are positive integers `x, y` with `n = x + y` and
  `p(99, x) + p(100, y)` prime.
-/

namespace OMA.S_oeis_a228428

/-- The `m`-gonal number `p(m, k) = (m - 2) k (k - 1) / 2 + k`. -/
def polygonal (m k : ℕ) : ℕ :=
  (m - 2) * k * (k - 1) / 2 + k

theorem main :
    ∀ n : ℕ, 1 < n → ∃ x y : ℕ, 0 < x ∧ 0 < y ∧ n = x + y ∧
        (polygonal 99 x + polygonal 100 y).Prime := by
  sorry

end OMA.S_oeis_a228428
