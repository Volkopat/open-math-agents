import Mathlib

/-!
# A282172: Number of ways to write n as an ordered sum of 5 tetrahedral numbers

Source: https://oeis.org/A282172
Author: Sir Frederick Pollock (1850)

Conjecture (Pollock's Tetrahedral Numbers Conjecture, OEIS A282172):
Every natural number `n` is the sum of at most `5` tetrahedral numbers
`k * (k + 1) * (k + 2) / 6` (equivalently, `a(n) > 0` for all `n ≥ 0`, allowing `k = 0`).

Conventions:
- Offset: `0`; first terms: `1, 5, 10, 10, 10, 21, 30, 20, 15, 30, 35, ...`.
- `tet 0 = 0`, `tet 1 = 1`, `tet 2 = 4`, `tet 3 = 10`, `tet 4 = 20`, ...
-/

namespace OMA.S_oeis_a282172

/-- The `k`-th tetrahedral number `k * (k + 1) * (k + 2) / 6` (OEIS A000292). -/
def tet (k : ℕ) : ℕ :=
  k * (k + 1) * (k + 2) / 6

/-- Conjecture (Pollock's Conjecture): every natural number is a sum of 5 tetrahedral numbers. -/
theorem main :
    ∀ n : ℕ, ∃ a b c d e : ℕ, n = tet a + tet b + tet c + tet d + tet e := by
  sorry

end OMA.S_oeis_a282172
