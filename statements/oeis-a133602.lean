import Mathlib

/-!
# A133602: The matrix-vector product A133080 * A000108.

Source: https://oeis.org/A133602
Credit: @agchua

Formula line of A133602 (the entry is by Gary W. Adamson):
  Conjecture: n*(n-1)*(n-3)*(3*n-4)*a(n) -8*(n-1)*(2*n-5)*a(n-1)
  -4*(n-2)*(3*n-1)*(2*n-5)*(2*n-7)*a(n-2)=0. - R. J. Mathar, Jun 20 2015
A133080 is the lower triangular matrix with rows and columns numbered from 1, with T(n,n) = 1,
T(n,n-1) = 1 for even n and 0 otherwise (R. J. Mathar's formula and Maple program in A133080).
A000108 is the Catalan numbers, Mathlib's catalan, numbered from 0. The n-th entry of the product
(n >= 1, the row index of A133080) is Sum_{k=1..n} T(n,k) * A000108(k-1); A133602 lists these
entries with offset 0, so A133602(n) is the entry of row n + 1, which is the definition of a below
(it gives the data 1, 2, 2, 7, 14, 56, 132, 561, ...).
Mathar's recurrence is written in the row index of A133080: with the offset 0 of A133602 it fails
for every n >= 2 (n = 2 gives 8), while with the row index, that is with A133602(n-1), A133602(n-2),
A133602(n-3) in the places of a(n), a(n-1), a(n-2), it holds for all n >= 3 (checked to n = 80).
The statement is that reading, for n >= 3, where all three indices are rows of A133080.
-/

namespace OMA.S_oeis_a133602

/-- A133080(n, k) for rows and columns n, k >= 1: T(n,n) = 1, T(n,n-1) = 1 if n is even,
and 0 otherwise. -/
def T (n k : ℕ) : ℕ := if k = n then 1 else if k + 1 = n then (if n % 2 = 0 then 1 else 0) else 0

/-- A133602(n) = Sum_{k=0..n} A133080(n+1, k+1) * A000108(k), the entry of row n + 1. -/
def a (n : ℕ) : ℕ := ∑ k ∈ Finset.range (n + 1), T (n + 1) (k + 1) * catalan k

/-- Mathar's conjecture in the row index of A133080: for n >= 3,
n(n-1)(n-3)(3n-4) A133602(n-1) - 8(n-1)(2n-5) A133602(n-2)
- 4(n-2)(3n-1)(2n-5)(2n-7) A133602(n-3) = 0. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (n : ℤ) * (n - 1) * (n - 3) * (3 * n - 4) * (a (n - 1) : ℤ)
      - 8 * (n - 1) * (2 * n - 5) * (a (n - 2) : ℤ)
      - 4 * (n - 2) * (3 * n - 1) * (2 * n - 5) * (2 * n - 7) * (a (n - 3) : ℤ) = 0 := by
  sorry

end OMA.S_oeis_a133602
