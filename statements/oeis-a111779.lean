import Mathlib

/-!
# A111779: Sixth column (m=5) of unsigned triangle A111595.

Source: https://oeis.org/A111779
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A111779 (R. J. Mathar, Jun 08 2016):
+(-n+5)*a(n) +5*n*a(n-1) +n*(n-1)^2*a(n-2)=0.

Conventions:
* The sequence has offset 5 (data 1, 30, 651, 12600, 235494, 4396140, ...).
* The column is given by the explicit formula of the entry:
  a(n)=(n!/5!)*sum(binomial(2*k, k)*binomial(n-2*k-1, 4)/(4^k), k=0..floor((n-5)/2)), n>=5.
  The sum over k = 0..floor((n-5)/2) is `Finset.range ((n - 5) / 2 + 1)`; for n >= 5 and k in
  this range 2k + 5 <= n, so the natural number subtractions n - 5 and n - 2k - 1 are exact.
  Only `n ≥ 5` is used.
* The division by 4^k and by 5! is the division of `ℚ`, so a(n) is defined as a rational
  number (it is an integer).
* The source gives no range for n. The recurrence is asserted for every `n ≥ 7`, which is
  exactly the range in which all the indices n, n-1, n-2 are at least the offset 5.
* The identity is stated in `ℚ`, with the natural number `n` cast to `ℚ`, so the subtractions
  in the polynomial coefficients are exact.
-/

namespace OMA.S_oeis_a111779

/-- A111779 (offset 5):
a(n) = (n!/5!) * Sum_{k=0..floor((n-5)/2)} binomial(2k,k)*binomial(n-2k-1,4)/4^k. -/
def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) / (Nat.factorial 5 : ℚ)
    * ∑ k ∈ Finset.range ((n - 5) / 2 + 1),
        ((2 * k).choose k : ℚ) * ((n - 2 * k - 1).choose 4 : ℚ) / (4 : ℚ) ^ k

/-- For every `n ≥ 7`, (-n+5)*a(n) + 5*n*a(n-1) + n*(n-1)^2*a(n-2) = 0. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    (-(n : ℚ) + 5) * a n + 5 * (n : ℚ) * a (n - 1)
      + (n : ℚ) * ((n : ℚ) - 1) ^ 2 * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a111779
