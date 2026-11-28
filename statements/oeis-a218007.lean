import Mathlib

/-!
# A218007: Number of partitions of n into at most three primes (including 1).

Source: https://oeis.org/A218007
Credit: @azmiozgen

Conjecture (strong Goldbach form, from the entry): any positive integer is the sum of at most three distinct terms from {1} union primes.

Formalization notes:
* The terms are 1 and the primes; "at most three distinct terms" is stated as a sum over a finite set
  S of such terms with 1 ≤ |S| ≤ 3.
* Controls (computed): every n with 1 ≤ n < 3000 is such a sum.
-/

namespace OMA.S_oeis_a218007



/-- The conjecture of the entry. -/
theorem main :
    ∀ n : ℕ, 0 < n → ∃ S : Finset ℕ, 0 < S.card ∧ S.card ≤ 3 ∧ (∀ t ∈ S, t = 1 ∨ t.Prime) ∧
      ∑ t ∈ S, t = n := by
  sorry

end OMA.S_oeis_a218007
