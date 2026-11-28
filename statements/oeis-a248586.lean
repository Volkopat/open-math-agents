import Mathlib

/-!
# A248586: a(n) = Sum_{i=0..n} C(n,i)*C(2i,i)^2.

Source: https://oeis.org/A248586
Credit: @JeremyDevs

Formalizes the conjecture recorded in the FORMULA section of OEIS A248586:
n^2*a(n) +(-19*n^2+19*n-5)*a(n-1) +35*(n-1)^2*a(n-2) -17*(n-1)*(n-2)*a(n-3)=0.

Conventions:
* The sequence has offset 0 (data 1, 5, 45, 521, 6733, 92385, ...) and
  a(n) = Sum_{i=0..n} C(n,i)*C(2i,i)^2, with C the binomial coefficient (`Nat.choose`); the sum
  over i = 0..n is `Finset.range (n + 1)`. The terms are cast to `ℤ`.
* The source gives no range for n. The recurrence is asserted for every `n ≥ 3`, which is
  exactly the range in which all the indices n, n-1, n-2, n-3 are at least the offset 0.
* The identity is stated in `ℤ`, with the natural number `n` cast to `ℤ`, so the subtractions
  in the polynomial coefficients are exact.
-/

namespace OMA.S_oeis_a248586

/-- A248586 (offset 0): a(n) = Sum_{i=0..n} C(n,i)*C(2i,i)^2. -/
def a (n : ℕ) : ℤ :=
  ∑ i ∈ Finset.range (n + 1), (n.choose i : ℤ) * ((2 * i).choose i : ℤ) ^ 2

/-- For every `n ≥ 3`,
n^2*a(n) + (-19*n^2+19*n-5)*a(n-1) + 35*(n-1)^2*a(n-2) - 17*(n-1)*(n-2)*a(n-3) = 0. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (n : ℤ) ^ 2 * a n + (-19 * (n : ℤ) ^ 2 + 19 * (n : ℤ) - 5) * a (n - 1)
      + 35 * ((n : ℤ) - 1) ^ 2 * a (n - 2)
      - 17 * ((n : ℤ) - 1) * ((n : ℤ) - 2) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a248586
