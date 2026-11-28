import Mathlib

/-!
# A211995: a(n) = floor(7^n / 2^n) mod 2^n

Source: https://oeis.org/A211995

Conjecture (OEIS A211995):
For every `n > 2`, `a(n) > 0`, where `a(n) = ⌊7^n / 2^n⌋ mod 2^n`.

Conventions:
- Offset: `1`; first terms: `a(1) = 1`, `a(2) = 0`, `a(3) = 2`, `a(4) = 6`, `a(5) = 13`,
  `a(6) = 46`, `a(7) = 33`, `a(8) = 246`, `a(9) = 479`, `a(10) = 398`, ...
- On `ℕ`, integer division `7 ^ n / 2 ^ n` is exact floor division `⌊7^n / 2^n⌋`.
-/

namespace OMA.S_oeis_a211995

/-- The sequence `a(n) = ⌊7^n / 2^n⌋ mod 2^n` (OEIS A211995). -/
def a (n : ℕ) : ℕ :=
  (7 ^ n / 2 ^ n) % (2 ^ n)

/-- Conjecture: `a(n) > 0` for all `n > 2`. -/
theorem main :
    ∀ n : ℕ, 2 < n → 0 < a n := by
  sorry

end OMA.S_oeis_a211995
