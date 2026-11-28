import Mathlib

/-!
# A212696: Central coefficient of the triangle A097609.

Source: https://oeis.org/A212696
Credit: @JeremyDevs

Formalizes the conjecture recorded in the FORMULA section of OEIS A212696 (R. J. Mathar,
Oct 08 2016):
2*n*(n-1)*(2*n+1)*(5*n-8)*a(n) -(n-1)*(115*n^3-344*n^2+299*n-82) *a(n-1)
-4*(2*n-3)*(5*n^3+27*n^2-74*n+30)*a(n-2) +36*(n-1)*(5*n-3)*(2*n-3)*(2*n-5) *a(n-3)=0.

Conventions:
* The sequence has offset 0 (data 1, 0, 3, 4, 25, 66, 287, 960, 3789, 13810, ...). The central
  coefficient is rendered through the first explicit formula of the FORMULA section of the
  entry: a(n) = ((n+1)*Sum_{j=0..n} C(n+2*j, n+j)*(-1)^(n-j)*C(2*n+1, n+j+1)) / (2*n+1).
  Binomial coefficients are `Nat.choose`, the sum over j = 0..n is `Finset.range (n + 1)`
  (so the exponent n-j is an exact natural number subtraction), and the value is computed
  in `ℚ`, where the division by 2*n+1 is the ordinary field division (the quotient is in
  fact an integer).
* The source gives no range for n. The recurrence is asserted for every `n ≥ 3`, which is
  exactly the range in which the indices n, n-1, n-2, n-3 are all at least the offset 0.
* The identity is stated in `ℚ`, with the natural number `n` cast to `ℚ`, so the subtractions
  in the polynomial coefficients are exact.
-/

namespace OMA.S_oeis_a212696

/-- A212696 (offset 0):
a(n) = ((n+1)*Sum_{j=0..n} C(n+2*j, n+j)*(-1)^(n-j)*C(2*n+1, n+j+1)) / (2*n+1). -/
def a (n : ℕ) : ℚ :=
  ((n : ℚ) + 1)
    * (∑ j ∈ Finset.range (n + 1),
        ((n + 2 * j).choose (n + j) : ℚ) * (-1) ^ (n - j) * ((2 * n + 1).choose (n + j + 1) : ℚ))
    / (2 * (n : ℚ) + 1)

/-- For every `n ≥ 3`,
2*n*(n-1)*(2*n+1)*(5*n-8)*a(n) - (n-1)*(115*n^3-344*n^2+299*n-82)*a(n-1)
- 4*(2*n-3)*(5*n^3+27*n^2-74*n+30)*a(n-2) + 36*(n-1)*(5*n-3)*(2*n-3)*(2*n-5)*a(n-3) = 0. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    2 * (n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) + 1) * (5 * (n : ℚ) - 8) * a n
      - ((n : ℚ) - 1) * (115 * (n : ℚ) ^ 3 - 344 * (n : ℚ) ^ 2 + 299 * (n : ℚ) - 82) * a (n - 1)
      - 4 * (2 * (n : ℚ) - 3) * (5 * (n : ℚ) ^ 3 + 27 * (n : ℚ) ^ 2 - 74 * (n : ℚ) + 30)
        * a (n - 2)
      + 36 * ((n : ℚ) - 1) * (5 * (n : ℚ) - 3) * (2 * (n : ℚ) - 3) * (2 * (n : ℚ) - 5)
        * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a212696
