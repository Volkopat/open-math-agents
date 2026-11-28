import Mathlib

/-!
# A087664: Steps to reach an integer in the approximate-squaring recurrence from n/4

Source: https://oeis.org/A087664

Conjecture (J. C. Lagarias and N. J. A. Sloane):
Consider the recurrence `b(0) = n / 4`, `b(k + 1) = b(k) * floor(b(k))`.
An integer is always eventually reached whenever the initial value `n / 4` is at least `2`
(i.e., `n ≥ 8`).

Conventions:
- Offset: `8` (corresponding to `n / 4 ≥ 2`).
- We work in `ℚ` and express integrality of `b n k` as `∃ m : ℤ, b n k = (m : ℚ)`.
-/

namespace OMA.S_oeis_a087664

/-- The rational sequence `b n k` defined by `b n 0 = n / 4` and
`b n (k + 1) = b n k * ⌊b n k⌋`. -/
def b (n : ℕ) : ℕ → ℚ
  | 0 => (n : ℚ) / 4
  | k + 1 => b n k * (Int.floor (b n k) : ℚ)

/-- Conjecture (Lagarias–Sloane): for every `n ≥ 8`, the recurrence `b n` eventually
reaches an integer. -/
theorem main :
    ∀ n : ℕ, 8 ≤ n → ∃ k : ℕ, ∃ m : ℤ, b n k = (m : ℚ) := by
  sorry

end OMA.S_oeis_a087664
