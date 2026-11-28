import Mathlib

/-!
# Catalan–Dickson conjecture on aliquot sequences

Source: https://en.wikipedia.org/wiki/Aliquot_sequence#Catalan-Dickson_conjecture
Credit: @mwhuss

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.

The source: the aliquot sequence of n starts at n and iterates s(m) = σ(m) − m, the sum of the
proper divisors of m. The Catalan–Dickson conjecture says "no aliquot sequences are infinite
but non-repeating" — every aliquot sequence is eventually periodic (it reaches 1, a perfect
number, or an amicable/cyclic pair).
-/

namespace OMA.S_wp_catalan_dickson_conjecture_on_aliquot_sequences

/-- The aliquot successor: the sum of the proper divisors of n. -/
def aliquot (n : ℕ) : ℕ := (∑ d ∈ n.divisors.erase n, d)

/--
Catalan–Dickson: every aliquot sequence is eventually periodic — iterating the aliquot
successor from any starting value n, two terms repeat.
-/
theorem main :
    ∀ n : ℕ, ∃ k m : ℕ, 0 < m ∧ aliquot^[k + m] n = aliquot^[k] n := by
  sorry

end OMA.S_wp_catalan_dickson_conjecture_on_aliquot_sequences
