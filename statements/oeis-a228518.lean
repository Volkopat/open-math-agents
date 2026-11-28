import Mathlib

/-!
# A228518: a(n) is the least r > 1 for which the interval (r*n, r*(n+1)) contains no terms of A050376 or a(n) = 0 if no such r exists.

Source: https://oeis.org/A228518
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A228518 (Vladimir Shevelev and Peter J. C. Moses, Aug
24 2013): a(n) = 0 iff n = 1, 2, 3, 4, 5, 6, 9, 12, 14, 24, 56.

Conventions:
* The sequence has offset 1 (data 0, 0, 0, 0, 0, 0, 2, 4, 0, 2, 3, 0, ...).
* A050376 is the sequence of numbers of the form p^(2^k) with p prime and k >= 0 (2, 3, 4, 5, 7,
  9, 11, 13, 16, ...).
* a(n) = 0 means that no integer r > 1 exists for which the open interval (r*n, r*(n+1)) contains
  no terms of A050376, i.e. that for every integer r > 1 the interval contains one. The conjecture
  is stated for n >= 1 (the offset of the sequence) as the equivalence between this property and
  membership of n in the list.
-/

namespace OMA.S_oeis_a228518

/-- The conjecture recorded in A228518. -/
theorem main : ∀ n : ℕ, 0 < n →
    ((∀ r : ℕ, 1 < r → ∃ q : ℕ, (∃ p k : ℕ, p.Prime ∧ q = p ^ (2 ^ k)) ∧
        r * n < q ∧ q < r * (n + 1)) ↔
      n ∈ ({1, 2, 3, 4, 5, 6, 9, 12, 14, 24, 56} : Finset ℕ)) := by
  sorry

end OMA.S_oeis_a228518
