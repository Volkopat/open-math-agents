import Mathlib

/-!
# A106391: A "cosh transform" of binomial(2n,n-1).

Source: https://oeis.org/A106391
Credit: @JeremyDevs

Formalizes the two conjectures recorded in OEIS A106391 (R. J. Mathar, Feb 20 2015):
-(n+1)*(n-2)*a(n) +4*n*(3*n-7)*a(n-1) +(-49*n^2+193*n-148)*a(n-2) +8*(9*n-19)*(n-4)*a(n-3)
+(5*n^2+115*n-418)*a(n-4) -12*(7*n-19)*(n-4)*a(n-5) +45*(n-4)*(n-5)*a(n-6)=0
and
-(n-2)*(n+1)*(4*n^2-16*n+19)*a(n) +8*n*(n-2)*(4*n^2-14*n+13)*a(n-1)
+2*(-28*n^4+168*n^3-375*n^2+401*n-180)*a(n-2) -8*(n-2)*(4*n^3-18*n^2+27*n-10)*a(n-3)
+15*(n-2)*(n-3)*(4*n^2-8*n+7)*a(n-4)=0.

Conventions:
* The sequence has offset 0 (data 0, 1, 4, 18, 80, 365, 1692, 7945, ...).
* The cosh transform is the one given by the formula of the entry (and by its Maple program):
  a(n) = Sum_{k=0..floor(n/2)} binomial(n,2k)*binomial(2(n-2k),n-2k+1). Here
  binomial(2m,m+1) = binomial(2m,m-1) for m >= 1 and both are 0 for m = 0, so this is the
  transform of binomial(2n,n-1) of the title. The sum over k = 0..floor(n/2) is
  `Finset.range (n / 2 + 1)`; in it 2k <= n, so the natural number subtraction n - 2k is exact.
* The source gives no range for n. The first recurrence is asserted for every `n ≥ 6` and the
  second for every `n ≥ 4`, which are exactly the ranges in which all the indices that occur
  (down to n-6, respectively n-4) are at least the offset 0.
* The statement is the conjunction of the two conjectured recurrences.
* The identities are stated in `ℤ`, with the natural number `n` cast to `ℤ`, so the
  subtractions in the polynomial coefficients are exact.
-/

namespace OMA.S_oeis_a106391

/-- A106391 (offset 0):
a(n) = Sum_{k=0..floor(n/2)} binomial(n,2k)*binomial(2(n-2k),n-2k+1). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n / 2 + 1),
    (n.choose (2 * k) : ℤ) * ((2 * (n - 2 * k)).choose (n - 2 * k + 1) : ℤ)

/-- The two conjectured recurrences: the first for every `n ≥ 6`, the second for every
`n ≥ 4`. -/
theorem main :
    (∀ n : ℕ, 6 ≤ n →
      (-((n : ℤ) + 1) * ((n : ℤ) - 2)) * a n
        + (4 * (n : ℤ) * (3 * (n : ℤ) - 7)) * a (n - 1)
        + ((-49 * (n : ℤ) ^ 2 + 193 * (n : ℤ) - 148)) * a (n - 2)
        + (8 * (9 * (n : ℤ) - 19) * ((n : ℤ) - 4)) * a (n - 3)
        + ((5 * (n : ℤ) ^ 2 + 115 * (n : ℤ) - 418)) * a (n - 4)
        + (-12 * (7 * (n : ℤ) - 19) * ((n : ℤ) - 4)) * a (n - 5)
        + (45 * ((n : ℤ) - 4) * ((n : ℤ) - 5)) * a (n - 6) = 0) ∧
    (∀ n : ℕ, 4 ≤ n →
      (-((n : ℤ) - 2) * ((n : ℤ) + 1) * (4 * (n : ℤ) ^ 2 - 16 * (n : ℤ) + 19)) * a n
        + (8 * (n : ℤ) * ((n : ℤ) - 2) * (4 * (n : ℤ) ^ 2 - 14 * (n : ℤ) + 13)) * a (n - 1)
        + (2 * (-28 * (n : ℤ) ^ 4 + 168 * (n : ℤ) ^ 3 - 375 * (n : ℤ) ^ 2 + 401 * (n : ℤ) - 180)) * a (n - 2)
        + (-8 * ((n : ℤ) - 2) * (4 * (n : ℤ) ^ 3 - 18 * (n : ℤ) ^ 2 + 27 * (n : ℤ) - 10)) * a (n - 3)
        + (15 * ((n : ℤ) - 2) * ((n : ℤ) - 3) * (4 * (n : ℤ) ^ 2 - 8 * (n : ℤ) + 7)) * a (n - 4) = 0) := by
  sorry

end OMA.S_oeis_a106391
