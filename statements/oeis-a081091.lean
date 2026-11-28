import Mathlib

/-!
# A081091: Primes of the form 2^i + 2^j + 1, i > j > 0.

Source: https://oeis.org/A081091
Credit: @eitanteperman

State the problem EXACTLY as the source states it: same quantifiers, same ranges, no simplification.
Do not prove it here: the theorem body stays `sorry`. A person reviews the translation before merging.
-/

namespace OMA.S_oeis_a081091

/-- The set of terms of A081091: primes of the form `2^i + 2^j + 1` with `i > j > 0`
(7, 11, 13, 19, 37, 41, 67, 73, 97, 131, ...). -/
def S : Set ℕ := {p | p.Prime ∧ ∃ i j : ℕ, 0 < j ∧ j < i ∧ p = 2 ^ i + 2 ^ j + 1}

/-- Conjecture (Sam Wagstaff, recorded in A081091): there are infinitely many primes with exactly three
bits set in their binary expansion, i.e. the set of terms is infinite. -/
theorem main : S.Infinite := by
  sorry

end OMA.S_oeis_a081091
