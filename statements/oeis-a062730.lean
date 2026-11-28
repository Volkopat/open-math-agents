import Mathlib

/-!
# A062730: Rows of Pascal's triangle which contain 3 terms in arithmetic progression

Source: https://oeis.org/A062730
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-- Draft from an earlier generic agent run; audited against the source and checked by this agent.

Conjecture: Let `a(n)` (1-indexed, `n ≥ 1`) be the `n`-th row `r` of Pascal's triangle
containing three distinct terms `C(r, i) < C(r, j) < C(r, k)` in arithmetic progression
(`2 * C(r, j) = C(r, i) + C(r, k)`). Then for `n > 4`:
- `a(n) = (n^2 + 8*n + 8) / 4` when `n` is even,
- `a(n) = (n^2 + 10*n + 9) / 4` when `n` is odd.

Conventions:
- `a(n)` for `n ≥ 1` is realized via `Nat.nth HasThreeTermAP (n - 1)`, matching the
  1-indexed sequence `a(1) = 7, a(2) = 12, a(3) = 14, a(4) = 19, a(5) = 21, a(6) = 23, ...`.
-/

namespace OMA.S_oeis_a062730

/-- Row `r` of Pascal's triangle contains three strictly increasing terms in arithmetic progression. -/
def HasThreeTermAP (r : ℕ) : Prop :=
  ∃ i j k : ℕ, i < j ∧ j < k ∧ k ≤ r ∧
    Nat.choose r i < Nat.choose r j ∧
    Nat.choose r j < Nat.choose r k ∧
    2 * Nat.choose r j = Nat.choose r i + Nat.choose r k

/-- The 1-indexed sequence A062730 (`n ≥ 1`). -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.nth HasThreeTermAP (n - 1)

theorem main :
    ∀ n : ℕ, 4 < n →
      a n = if Even n then (n ^ 2 + 8 * n + 8) / 4 else (n ^ 2 + 10 * n + 9) / 4 := by
  sorry

end OMA.S_oeis_a062730
