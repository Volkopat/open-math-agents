import Mathlib

/-!
# A278618: a(n) = Sum_{j=0..n/2} binomial(n-j-1,n-2*j)*binomial(2*n+1,j).

Source: https://oeis.org/A278618
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 0, 5, 7, 45, 121, 533, 1800, 7157, ...
It is defined by the formula in the name of the entry, which is used here verbatim (the definition
below reproduces the data of the entry).

The conjecture (R. J. Mathar, Dec 02 2016) reads
  Conjecture: 2*n*(5*n-8)*(2*n-1)*(n+1)*a(n) -n*(115*n^3-344*n^2+299*n-82)*a(n-1)
  -4*(2*n-1)*(5*n^3+27*n^2-74*n+30)*a(n-2) +36*(n-2)*(5*n-3)*(2*n-1)*(2*n-3)*a(n-3)=0
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a278618

/-- A278618: a(n) = Sum_{j=0..n/2} binomial(n-j-1,n-2*j)*binomial(2*n+1,j). -/
def a (n : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (n / 2 + 1), ((n - j - 1).choose (n - 2 * j) : ℤ) * ((2 * n + 1).choose j : ℤ)

/-- The conjectured recurrence for A278618. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (20 * (n : ℤ) ^ 4 - 22 * (n : ℤ) ^ 3 - 26 * (n : ℤ) ^ 2 + 16 * (n : ℤ)) * a n
      + (-115 * (n : ℤ) ^ 4 + 344 * (n : ℤ) ^ 3 - 299 * (n : ℤ) ^ 2 + 82 * (n : ℤ)) * a (n - 1)
      + (-40 * (n : ℤ) ^ 4 - 196 * (n : ℤ) ^ 3 + 700 * (n : ℤ) ^ 2 - 536 * (n : ℤ) + 120) * a (n - 2)
      + (720 * (n : ℤ) ^ 4 - 3312 * (n : ℤ) ^ 3 + 5148 * (n : ℤ) ^ 2 - 3132 * (n : ℤ) + 648) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a278618
