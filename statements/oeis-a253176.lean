import Mathlib

/-!
# A253176: Least k>=0 such that both 3n*2^k+1 and 3n*2^k-1 are primes, or -1 if no such k exists.

Source: https://oeis.org/A253176
Credit: @azmiozgen

Conjecture (from the entry): if n < 79, then a(n) >= 0.

Formalization notes:
* a(n) ≥ 0 means some k ≥ 0 makes 3n*2^k + 1 and 3n*2^k - 1 both prime. Stated for 1 ≤ n < 79.
* Controls (computed, k < 60): such k exists for all 1 ≤ n < 79 except n = 37, 41, 51, 53, 57, 61, 63,
  73, 74, 75, for which the entry also lists a(n) as unknown or not yet found (e.g. 37, 41, 51, 53, 57).
-/

namespace OMA.S_oeis_a253176



/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 1 ≤ n → n < 79 → ∃ k : ℕ, (3 * n * 2 ^ k + 1).Prime ∧ (3 * n * 2 ^ k - 1).Prime := by
  sorry

end OMA.S_oeis_a253176
