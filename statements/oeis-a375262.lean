import Mathlib.Data.Nat.Totient
import Mathlib.Data.Rat.Defs
import Mathlib.NumberTheory.Divisors

/-!
# The range of the ratio of the divisor sum to Euler's totient

Zhi-Wei Sun conjectures that every rational number at least one occurs as
`σ(m) / φ(m)` for a positive integer `m`. OEIS A375262 records the least
such integer for each half-integer `n + 1/2` with `n ≥ 1`.

Source: https://oeis.org/A375262
Original question: https://mathoverflow.net/questions/476578
Credit: @studer
-/

namespace OMA.S_oeis_a375262

theorem main : ∀ r : ℚ, 1 ≤ r → ∃ m : ℕ, 0 < m ∧
    r = (↑(∑ d ∈ m.divisors, d) : ℚ) / (m.totient : ℚ) := by
  sorry

end OMA.S_oeis_a375262
