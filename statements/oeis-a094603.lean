import Mathlib

/-!
# OEIS A094603: rightmost black runs in Rule 30

Source: https://oeis.org/A094603
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

`a(n)` is the length of the maximal run of rightmost black cells in the `n`-th row of Rule 30
started from a single black cell (offset 1: row `1` is the initial row). Conjecture (OEIS entry):
`a(n) = A094604(A007814(n))`, where `A007814(n)` is the `2`-adic valuation of `n` and
`A094604(k) = a(2^k)`.

Conventions:
* Rows are `ℤ → Bool` (`true` = black), `row 0` has a single black cell at `0`, and Rule 30 is
  `new(x) = old(x-1) xor (old(x) or old(x+1))`. Row `t` (the `(t+1)`-st row) is black at `x = t`
  and white beyond, so its rightmost run has length the least `j` with `row t (t - j)` white.
* So `a(n) = run (n - 1)`, and `main` reads `run (n - 1) = run (2^(v₂ n) - 1)` for `n ≥ 1`.
-/

namespace OMA.S_oeis_a094603

/-- The rows of Rule 30 from a single black cell. -/
def row : ℕ → ℤ → Bool
  | 0, x => decide (x = 0)
  | t + 1, x => xor (row t (x - 1)) (row t x || row t (x + 1))

/-- Length of the run of black cells ending at position `t` in row `t`. -/
noncomputable def run (t : ℕ) : ℕ := sInf {j : ℕ | row t ((t : ℤ) - j) = false}

/-- `a(n) = a(2^(v₂ n))` for `n ≥ 1`. -/
theorem main : ∀ n : ℕ, 1 ≤ n → run (n - 1) = run (2 ^ padicValNat 2 n - 1) := by
  sorry

end OMA.S_oeis_a094603
