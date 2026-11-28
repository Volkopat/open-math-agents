import Mathlib

/-!
# A168452: Self-convolution of A005568, where A005568(n) is the product of two successive Catalan numbers C(n)*C(n+1).

Source: https://oeis.org/A168452
Credit: @JeremyDevs

Formalizes the conjecture recorded in OEIS A168452 (R. J. Mathar, Nov 22 2024):
Conjecture D-finite with recurrence 3*(n+4)*(n+3)*(n+2)*(n+1)^2*a(n)
-4*n*(n+1) *(32*n^3+164*n^2+233*n+75)*a(n-1)
+96*(16*n^5+24*n^4-14*n^3-28*n^2-16*n+3) *a(n-2) +1536*(-8*n^4+22*n^3-32*n+15)*a(n-3)
-16384*(2*n-5)*(n-1)*(n-2)*(n-3)*(2*n-3)*a(n-4)=0.

Conventions:
* The sequence has offset 0 (data 1, 4, 24, 180, 1556, 14840, 152092, ...).
* C(n) is the n-th Catalan number A000108(n) (`catalan n` in Mathlib), and
  `c n` = A005568(n) = C(n)*C(n+1), as the name says.
* The self-convolution of a sequence c with offset 0 is a(n) = Sum_{k=0..n} c(k)*c(n-k); the sum
  over k = 0..n is a sum over `Finset.range (n + 1)`.
* The source gives no range for n. The recurrence is asserted for every `n ≥ 4`, which is
  exactly the range in which all the indices n, n-1, n-2, n-3, n-4 are at least the offset 0.
* The identity is stated in `ℤ`, with the natural number `n` cast to `ℤ`, so the subtractions
  and negative coefficients are exact.
-/

namespace OMA.S_oeis_a168452

/-- A005568(n) = C(n)*C(n+1), the product of two successive Catalan numbers. -/
def c (n : ℕ) : ℤ := (catalan n : ℤ) * (catalan (n + 1) : ℤ)

/-- A168452 (offset 0): the self-convolution a(n) = Sum_{k=0..n} c(k)*c(n-k). -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), c k * c (n - k)

/-- For every `n ≥ 4`, 3*(n+4)*(n+3)*(n+2)*(n+1)^2*a(n)
- 4*n*(n+1)*(32*n^3+164*n^2+233*n+75)*a(n-1)
+ 96*(16*n^5+24*n^4-14*n^3-28*n^2-16*n+3)*a(n-2) + 1536*(-8*n^4+22*n^3-32*n+15)*a(n-3)
- 16384*(2*n-5)*(n-1)*(n-2)*(n-3)*(2*n-3)*a(n-4) = 0. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    3 * ((n : ℤ) + 4) * ((n : ℤ) + 3) * ((n : ℤ) + 2) * ((n : ℤ) + 1) ^ 2 * a n
      - 4 * (n : ℤ) * ((n : ℤ) + 1)
        * (32 * (n : ℤ) ^ 3 + 164 * (n : ℤ) ^ 2 + 233 * (n : ℤ) + 75) * a (n - 1)
      + 96 * (16 * (n : ℤ) ^ 5 + 24 * (n : ℤ) ^ 4 - 14 * (n : ℤ) ^ 3 - 28 * (n : ℤ) ^ 2
          - 16 * (n : ℤ) + 3) * a (n - 2)
      + 1536 * (-8 * (n : ℤ) ^ 4 + 22 * (n : ℤ) ^ 3 - 32 * (n : ℤ) + 15) * a (n - 3)
      - 16384 * (2 * (n : ℤ) - 5) * ((n : ℤ) - 1) * ((n : ℤ) - 2) * ((n : ℤ) - 3)
        * (2 * (n : ℤ) - 3) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a168452
