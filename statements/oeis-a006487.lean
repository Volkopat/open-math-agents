import Mathlib

/-!
# A006487: Denominators of greedy Egyptian fraction for square root of 2

Source: https://oeis.org/A006487
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

## Problem Statement
Let `a(n)` be the `n`-th denominator in the greedy Egyptian fraction expansion of `√2`:
starting with `r(0) = √2`, set `a(n) = ⌈1 / r(n)⌉` and `r(n + 1) = r(n) - 1 / a(n)`
(giving `a(0) = 1, a(1) = 3, a(2) = 13, a(3) = 253, a(4) = 218201, ...`).

Conjecture: Writing `a(n) = 2^(2^(n + b(n)))`, i.e., `b(n) = log₂(log₂(a(n))) - n`,
the sequence `b(n)` converges to a finite real constant as `n → ∞`.
-/

namespace OMA.S_oeis_a006487

/-- Remainder at step `n` of the greedy Egyptian fraction expansion of `√2`. -/
noncomputable def remainder : ℕ → ℝ
  | 0 => Real.sqrt 2
  | n + 1 =>
    let r := remainder n
    r - (1 : ℝ) / (Nat.ceil (1 / r) : ℝ)

/-- The `n`-th denominator `a(n)` of the greedy Egyptian fraction for `√2`. -/
noncomputable def greedyDenom (n : ℕ) : ℕ :=
  Nat.ceil (1 / remainder n)

theorem main :
    ∃ L : ℝ,
      Filter.Tendsto
        (fun n : ℕ => Real.logb 2 (Real.logb 2 (greedyDenom n : ℝ)) - (n : ℝ))
        Filter.atTop (nhds L) := by
  sorry

end OMA.S_oeis_a006487
