import Mathlib

/-!
# A370394: Number of steps to reach 0 by applying the map f(x) = 5x + 1 if x is odd and floor(x/3) if x is even, or -1 if 0 is never reached.

Source: https://oeis.org/A370394
Credit: @keiichisince1986-bot

A370394 is the sequence `a(n)` named in the title. The entry states:
Conjecture: for all n, a(n) != -1.

Conventions:
- `floor(x/3)` is natural-number division `x / 3`. The offset is `0`.
-/

namespace OMA.S_oeis_a370394

/-- `f(x) = 5x + 1` for odd `x`, `⌊x/3⌋` for even `x`. -/
def f (x : ℕ) : ℕ := if x % 2 = 1 then 5 * x + 1 else x / 3

theorem main :
    ∀ n : ℕ, ∃ k : ℕ, f^[k] n = 0 := by
  sorry

end OMA.S_oeis_a370394
