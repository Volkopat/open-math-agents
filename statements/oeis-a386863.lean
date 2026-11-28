import Mathlib

/-!
# A386863: a(n) = Sum_{k=0..n} 2^(n-k) * binomial(3*n+1,k) * binomial(3*n-k-1,n-k).

Source: https://oeis.org/A386863
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 8, 117, 1948, 34283, 622272, 11519692, 216193460, 4098365799, ...
It is defined by the formula in the name of the entry, which is used here verbatim (the definition
below reproduces the data of the entry).

The conjecture (R. J. Mathar, Nov 02 2026) reads
  Conjecture D-finite with recurrence 256*n*(2*n-1)*a(n) +224*(-90*n^2+197*n-120)*a(n-1)
  +8*(22946*n^2-84680*n+71325)*a(n-2) +18*(16798*n^2-128101*n+228655)*a(n-3)
  -9639*(3*n-8)*(3*n-10)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a386863

/-- A386863: a(n) = Sum_{k=0..n} 2^(n-k) * binomial(3*n+1,k) * binomial(3*n-k-1,n-k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (2 : ℤ) ^ (n - k) * ((3 * n + 1).choose k : ℤ) * ((3 * n - k - 1).choose (n - k) : ℤ)

/-- The conjectured recurrence for A386863. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (512 * (n : ℤ) ^ 2 - 256 * (n : ℤ)) * a n
      + (-20160 * (n : ℤ) ^ 2 + 44128 * (n : ℤ) - 26880) * a (n - 1)
      + (183568 * (n : ℤ) ^ 2 - 677440 * (n : ℤ) + 570600) * a (n - 2)
      + (302364 * (n : ℤ) ^ 2 - 2305818 * (n : ℤ) + 4115790) * a (n - 3)
      + (-86751 * (n : ℤ) ^ 2 + 520506 * (n : ℤ) - 771120) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a386863
