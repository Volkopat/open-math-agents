import Mathlib

/-!
# A242441: Numbers n such that there are no integer k < sqrt(n) and prime p < n with k^2*p == 1 (mod n).

Source: https://oeis.org/A242441
Credit: @azmiozgen

Conjecture (Zhi-Wei Sun, from the entry; checked in A242425 for n up to 10^7): the sequence only
has 61 terms as listed.

Formalization notes:
* k ranges over positive integers with k^2 < n (i.e. k < sqrt(n)); p over primes p < n.
* Stated as equality of the set of terms (n ≥ 1) with the 61 listed values.
* Controls (computed): the terms below 4000 are exactly the 61 listed values, the last being 1848.
-/

namespace OMA.S_oeis_a242441

/-- The sequence has exactly the 61 listed terms. -/
theorem main :
    {n : ℕ | 0 < n ∧ ¬ ∃ k p : ℕ, 0 < k ∧ k ^ 2 < n ∧ p.Prime ∧ p < n ∧ k ^ 2 * p ≡ 1 [MOD n]} =
      ({1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 16, 18, 20, 21, 24, 28, 30, 32, 39, 40, 48, 50, 56, 60, 63,
        70, 72, 80, 88, 102, 110, 112, 120, 126, 156, 168, 204, 213, 220, 232, 240, 252, 272, 273, 280,
        312, 372, 378, 408, 520, 527, 546, 760, 765, 780, 813, 840, 968, 1320, 1715, 1848} : Set ℕ) := by
  sorry

end OMA.S_oeis_a242441
