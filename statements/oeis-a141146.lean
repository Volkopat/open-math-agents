import Mathlib

/-!
# A141146: Number of linear arrangements of n blue, n red and n green items such that first and last elements are blue but there are no adjacent items of the same color.

Source: https://oeis.org/A141146
Credit: @JeremyDevs

Formalizes the conjecture recorded in the FORMULA section of OEIS A141146 (R. J. Mathar,
Jul 23 2014):
-(n+1)*(n-2)*a(n) +(7*n^2-13*n+4)*a(n-1) +8*(n-2)^2*a(n-2)=0.

Conventions:
* The sequence has offset 1 (data 0, 2, 14, 96, 664, 4660, 33144, ...). The number of
  arrangements is rendered through the explicit formula of the FORMULA section of the entry:
  a(n) = Sum[k=0..[n/2]] binomial(n-1,2k) * binomial(2k,k) * binomial(n-1+k,k+1) * 2^(n-1-2k).
  Binomial coefficients are `Nat.choose`, [n/2] is the natural number division `n / 2`, the
  sum over k = 0..[n/2] is `Finset.range (n / 2 + 1)`, and the terms are cast to `ℤ`. The
  subtractions n-1 and n-1-2k are natural number subtractions; for n ≥ 1 the only term in which
  n-1-2k is truncated (n even, k = n/2) has binomial(n-1,2k) = 0, so nothing is changed.
* The source gives no range for n. The recurrence is asserted for every `n ≥ 3`, which is
  exactly the range in which the indices n, n-1, n-2 are all at least the offset 1.
* The identity is stated in `ℤ`, with the natural number `n` cast to `ℤ`, so the subtractions
  in the polynomial coefficients are exact.
-/

namespace OMA.S_oeis_a141146

/-- A141146 (offset 1): a(n) = Sum_{k=0..[n/2]} binomial(n-1,2k) * binomial(2k,k)
* binomial(n-1+k,k+1) * 2^(n-1-2k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    ((n - 1).choose (2 * k) : ℤ) * ((2 * k).choose k : ℤ) * ((n - 1 + k).choose (k + 1) : ℤ)
      * 2 ^ (n - 1 - 2 * k)

/-- For every `n ≥ 3`, -(n+1)*(n-2)*a(n) + (7*n^2-13*n+4)*a(n-1) + 8*(n-2)^2*a(n-2) = 0. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    -((n : ℤ) + 1) * ((n : ℤ) - 2) * a n
      + (7 * (n : ℤ) ^ 2 - 13 * (n : ℤ) + 4) * a (n - 1)
      + 8 * ((n : ℤ) - 2) ^ 2 * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a141146
