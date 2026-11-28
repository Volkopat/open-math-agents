import Mathlib

/-!
# A083863: First integer reached by the approximate-squaring recurrence from n/3

Source: https://oeis.org/A083863

Conjecture (J. C. Lagarias and N. J. A. Sloane):
Consider the recurrence `b(0) = n / 3`, `b(k + 1) = b(k) * floor(b(k))`.
An integer is always eventually reached whenever the initial value `n / 3` is at least `2`
(i.e., `n ≥ 6`).

Conventions:
- Offset: `6` (corresponding to `n / 3 ≥ 2`).
- We work in `ℚ` and express integrality of `b n k` as `∃ m : ℤ, b n k = (m : ℚ)`.
-/

namespace OMA.S_oeis_a083863

/-- The rational sequence `b n k` defined by `b n 0 = n / 3` and
`b n (k + 1) = b n k * ⌊b n k⌋`. -/
def b (n : ℕ) : ℕ → ℚ
  | 0 => (n : ℚ) / 3
  | k + 1 => b n k * (Int.floor (b n k) : ℚ)

/-- Conjecture (Lagarias–Sloane): for every `n ≥ 6`, the recurrence `b n` eventually
reaches an integer. -/
theorem main :
    ∀ n : ℕ, 6 ≤ n → ∃ k : ℕ, ∃ m : ℤ, b n k = (m : ℚ) := by
  sorry

end OMA.S_oeis_a083863
