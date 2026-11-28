import Mathlib

/-!
# Practical numbers in the representation n = p + q/2

Zhi-Wei Sun, OEIS A214841, March 8, 2013. The sequence counts ordered pairs of
practical numbers p and q strictly below n satisfying n = p + q/2. The claim
that this count is positive is equivalent to the existence of such a pair.
Clearing the denominator expresses the exact equality over the natural numbers.

Source: https://oeis.org/A214841 (OEIS Foundation, CC BY-SA 4.0).
See also Sun, arXiv:1211.1588v26, Remark 4.26(a), p. 21.
-/

namespace OMA.S_oeis_a214841

/-- Every positive integer up to a practical number is a sum of distinct divisors. -/
def practical (n : ℕ) : Prop :=
  0 < n ∧ ∀ m, m ≤ n → ∃ s : Finset ℕ, s ⊆ n.divisors ∧ m = ∑ i ∈ s, i

theorem main : ∀ n : ℕ, 4 < n →
    ∃ p q : ℕ, p < n ∧ q < n ∧ practical p ∧ practical q ∧ 2 * n = 2 * p + q := by
  sorry

end OMA.S_oeis_a214841
