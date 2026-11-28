import Mathlib

/-!
# A072105: Recurrence c(n + 1) = c(n) / 2 + n (even) or 2 * c(n) - n (odd)

Source: https://oeis.org/A072105
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
Drafted in an earlier generic agent run; audited against the source statement before submission.

Conjecture:
Define `c(1) = x`, and for `n ≥ 1`, `c(n + 1) = c(n) / 2 + n` if `c(n)` is even,
and `c(n + 1) = 2 * c(n) - n` if `c(n)` is odd.
There exists a constant `C ∈ (4, 5)` such that for `x = 3`, `x = 5`, and every `x > 6`,
  `lim_{N → ∞} (1 / N) * ∑_{k = 1}^N c(k) / k = C`.

Conventions:
- `cSeq x n` is defined on `ℤ` (for 1-indexed `n ≥ 1`) so that `2 * c(n) - n` never truncates.
-/

namespace OMA.S_oeis_a072105

def cSeq (x : ℤ) : ℕ → ℤ
  | 0 => 0
  | 1 => x
  | n + 2 =>
    let prev := cSeq x (n + 1)
    if Even prev then prev / 2 + (n + 1 : ℤ) else 2 * prev - (n + 1 : ℤ)

theorem main :
    ∃ C : ℝ, 4 < C ∧ C < 5 ∧
      ∀ x : ℕ, (x = 3 ∨ x = 5 ∨ x > 6) →
        Filter.Tendsto
          (fun N : ℕ =>
            (1 / (N : ℝ)) * ∑ k ∈ Finset.Icc 1 N, (cSeq (x : ℤ) k : ℝ) / (k : ℝ))
          Filter.atTop (nhds C) := by
  sorry

end OMA.S_oeis_a072105
