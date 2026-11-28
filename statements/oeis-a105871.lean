import Mathlib

/-!
# A105871: a(n) = sum{k=0..floor(n/2), C(2*n-3*k, n)*C(n-k, k)}.

Source: https://oeis.org/A105871
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 2, 6, 22, 85, 336, 1350, 5492, 22554, ...
It is defined by the formula in the name of the entry, which is used here verbatim (the definition
below reproduces the data of the entry).

The conjecture (R. J. Mathar, Feb 20 2015) reads
  Conjecture: 5*n*(n-1)*(3*n-10)*a(n) -3*(n-1)*(21*n^2-63*n-20)*a(n-1)
  +3*(-3*n^3+107*n^2-446*n+444)*a(n-2) +(3*n^3-259*n^2+1279*n-1575)*a(n-3)
  +3*(-21*n^3+210*n^2-673*n+694)*a(n-4) -3*(n-3)*(3*n^2-8*n-7)*a(n-5)
  -2*(n-4)*(3*n-7)*(2*n-9)*a(n-6)=0
It involves a(n-6) and the offset is 0, so it is stated for n >= 6.
-/

namespace OMA.S_oeis_a105871

/-- A105871: a(n) = sum{k=0..floor(n/2), C(2*n-3*k, n)*C(n-k, k)}. -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n / 2 + 1), ((2 * n - 3 * k).choose n : ℤ) * ((n - k).choose k : ℤ)

/-- The conjectured recurrence for A105871. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (15 * (n : ℤ) ^ 3 - 65 * (n : ℤ) ^ 2 + 50 * (n : ℤ)) * a n
      + (-63 * (n : ℤ) ^ 3 + 252 * (n : ℤ) ^ 2 - 129 * (n : ℤ) - 60) * a (n - 1)
      + (-9 * (n : ℤ) ^ 3 + 321 * (n : ℤ) ^ 2 - 1338 * (n : ℤ) + 1332) * a (n - 2)
      + (3 * (n : ℤ) ^ 3 - 259 * (n : ℤ) ^ 2 + 1279 * (n : ℤ) - 1575) * a (n - 3)
      + (-63 * (n : ℤ) ^ 3 + 630 * (n : ℤ) ^ 2 - 2019 * (n : ℤ) + 2082) * a (n - 4)
      + (-9 * (n : ℤ) ^ 3 + 51 * (n : ℤ) ^ 2 - 51 * (n : ℤ) - 63) * a (n - 5)
      + (-12 * (n : ℤ) ^ 3 + 130 * (n : ℤ) ^ 2 - 454 * (n : ℤ) + 504) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a105871
