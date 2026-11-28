import Mathlib

/-!
# A263722: Integers k > 0 such that k^2 + p^2 is composite for all primes p.

Source: https://oeis.org/A263722
Credit: @azmiozgen

Conjecture (from the entry, checked for all k <= 12*10^7): all terms are odd.

Formalization notes:
* "k^2 + p^2 is composite" is stated as "not prime" (k^2 + p^2 ≥ 5 for k ≥ 1 and p ≥ 2, so the
  two readings agree).
* Stated as: for every k > 0, if k^2 + p^2 is not prime for every prime p, then k is odd.
* Controls (computed, primes p < 3000): the terms below 50 are 9, 11, 19, 21, 23, 25, 29, 31, 39,
  41, 43, 49, as in the entry.
-/

namespace OMA.S_oeis_a263722

/-- Every term of A263722 is odd. -/
theorem main : ∀ k : ℕ, 0 < k → (∀ p : ℕ, p.Prime → ¬ (k ^ 2 + p ^ 2).Prime) → Odd k := by
  sorry

end OMA.S_oeis_a263722
