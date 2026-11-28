import Mathlib

/-!
# A193101: Minimal number of numbers of the form (m^3+5m)/6 (see A004006) needed to sum to n.

Source: https://oeis.org/A193101
Credit: @keiichisince1986-bot

A193101 is the sequence `a(n)` named in the title. The entry states:
It is conjectured that a(n) <= 5 for all n.

Conventions:
- `f m = (m^3 + 5m)/6` (A004006, `m ≥ 0`); `6` divides `m (m^2 + 5)` for every `m`, so the division is exact.
- Since `f 0 = 0`, `a(n) ≤ 5` is the same as: `n` is a sum of exactly five values of `f` (unused summands
  are `f 0`). The offset is `1`; for `n = 0` the claim holds trivially.
-/

namespace OMA.S_oeis_a193101

/-- A004006: `(m^3 + 5m)/6`. -/
def f (m : ℕ) : ℕ := (m ^ 3 + 5 * m) / 6

theorem main :
    ∀ n : ℕ, ∃ a b c d e : ℕ, n = f a + f b + f c + f d + f e := by
  sorry

end OMA.S_oeis_a193101
