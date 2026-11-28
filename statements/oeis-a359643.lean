import Mathlib

/-!
# A359643: a(n) = Sum_{k=0..n} binomial(n,k) * binomial(4*k,k).

Source: https://oeis.org/A359643
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A359643 (R. J. Mathar, Jan 09 2023):
Conjecture D-finite with recurrence +81*n*(3*n-1)*(3*n-2)*a(n)
+3*(243*n^3-8433*n^2+14984*n-7064)*a(n-1) +2*(-58607*n^3+297306*n^2-491401*n+269124)*a(n-2)
+6*(n-2)*(56663*n^2-237722*n+252221)*a(n-3) -3*(n-2)*(n-3)*(111625*n-286402)*a(n-4)
+110653*(n-2)*(n-3)*(n-4)*a(n-5)=0.

Conventions:
* The sequence has offset 0 (data 1, 5, 37, 317, 2885, 27105, ...) and
  a(n) = Sum_{k=0..n} binomial(n,k) * binomial(4*k,k), with the binomial coefficient
  `Nat.choose`; the sum over k = 0..n is `Finset.range (n + 1)`. The terms are cast to `ℤ`.
* The source gives no range for n. The recurrence is asserted for every `n ≥ 5`, which is
  exactly the range in which all the indices n, n-1, ..., n-5 are at least the offset 0.
* The identity is stated in `ℤ`, with the natural number `n` cast to `ℤ`, so the subtractions
  in the polynomial coefficients are exact.
-/

namespace OMA.S_oeis_a359643

/-- A359643 (offset 0): a(n) = Sum_{k=0..n} binomial(n,k) * binomial(4*k,k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k : ℤ) * ((4 * k).choose k : ℤ)

/-- The conjectured recurrence, for every `n ≥ 5`. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    (81 * (n : ℤ) * (3 * (n : ℤ) - 1) * (3 * (n : ℤ) - 2)) * a n
      + (3 * (243 * (n : ℤ) ^ 3 - 8433 * (n : ℤ) ^ 2 + 14984 * (n : ℤ) - 7064)) * a (n - 1)
      + (2 * (-58607 * (n : ℤ) ^ 3 + 297306 * (n : ℤ) ^ 2 - 491401 * (n : ℤ) + 269124)) * a (n - 2)
      + (6 * ((n : ℤ) - 2) * (56663 * (n : ℤ) ^ 2 - 237722 * (n : ℤ) + 252221)) * a (n - 3)
      + (-3 * ((n : ℤ) - 2) * ((n : ℤ) - 3) * (111625 * (n : ℤ) - 286402)) * a (n - 4)
      + (110653 * ((n : ℤ) - 2) * ((n : ℤ) - 3) * ((n : ℤ) - 4)) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a359643
