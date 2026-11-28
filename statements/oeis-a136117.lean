import Mathlib

/-!
# OEIS A136117: every integer greater than 33066 is a sum of three pentagonal numbers

Source: https://oeis.org/A136117
Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

The comment of A136117 (Jonathan Vos Post, Dec 18 2007) records the conjecture that every
integer greater than 33066 can be represented as the sum of three pentagonal numbers.

Conventions: the pentagonal numbers are A000326, `P(m) = m (3m - 1)/2` for `m ≥ 0`, so `0` is
pentagonal. This is the convention of the companion sequence A003679 (numbers that are not the
sum of 3 pentagonal numbers, conjectured largest term 33066), which starts `4, 8, 9, …` and
therefore counts `1 = 1 + 0 + 0` and `2 = 1 + 1 + 0` as representable. The three summands need
not be distinct. Integers greater than 33066 are positive, so `N : ℕ` loses nothing.
-/

namespace OMA.S_oeis_a136117

/-- The pentagonal number `P(m) = m (3m - 1)/2` (A000326, offset 0); the division is exact. -/
def pentagonal (m : ℕ) : ℕ := m * (3 * m - 1) / 2

/-- Every integer `N > 33066` is `P(a) + P(b) + P(c)` for some `a, b, c ≥ 0`. -/
theorem main : ∀ N : ℕ, 33066 < N → ∃ a b c : ℕ, N = pentagonal a + pentagonal b + pentagonal c := by
  sorry

end OMA.S_oeis_a136117
