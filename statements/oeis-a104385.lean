import Mathlib

/-!
# OEIS A104385: partitions of triangular numbers into three distinct parts

Source: https://oeis.org/A104385
`a n` is the number of partitions of the triangular number `n(n+1)/2` into `3` distinct parts,
`n ≥ 1`. Conjecture (Stephan, 2010): `a(n) = round((3n⁴ + 6n³ - 33n² - 36n + 110)/144)`.

Conventions. Parts are positive integers `x < y < z`; `round` is Mathlib's `round` on `ℝ`
(the argument is never a half-integer here, so the rounding convention is immaterial).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a104385

/-- Partitions of `m` into three distinct positive parts. -/
def p3 (m : ℕ) : ℕ :=
  ((Finset.range (m + 1) ×ˢ Finset.range (m + 1) ×ˢ Finset.range (m + 1)).filter fun t =>
    0 < t.1 ∧ t.1 < t.2.1 ∧ t.2.1 < t.2.2 ∧ t.1 + t.2.1 + t.2.2 = m).card

theorem main :
    ∀ n : ℕ, 1 ≤ n →
      (p3 (n * (n + 1) / 2) : ℤ) =
        round ((3 * (n : ℝ) ^ 4 + 6 * n ^ 3 - 33 * n ^ 2 - 36 * n + 110) / 144) := by
  sorry

end OMA.S_oeis_a104385
