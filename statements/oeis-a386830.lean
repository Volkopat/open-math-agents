import Mathlib

/-!
# A386830: a(n) = Sum_{k=0..n} 3^k * 2^(n-k) * binomial(3*n+1,k) * binomial(3*n-k,n-k).

Source: https://oeis.org/A386830
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 18, 459, 12942, 382671, 11632248, 360048924, 11287595862, 357239123631, ...
It is defined by the formula in the name of the entry, which is used here verbatim (the definition
below reproduces the data of the entry).

The conjecture (R. J. Mathar, Aug 19 2025) reads
  Conjecture D-finite with recurrence +8*n*(2*n-3)*a(n) +6*(-108*n^2+207*n-80)*a(n-1)
  +405*(3*n-2)*(3*n-4)*a(n-2)=0
It involves a(n-2) and the offset is 0, so it is stated for n >= 2.
-/

namespace OMA.S_oeis_a386830

/-- A386830: a(n) = Sum_{k=0..n} 3^k * 2^(n-k) * binomial(3*n+1,k) * binomial(3*n-k,n-k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (3 : ℤ) ^ k * (2 : ℤ) ^ (n - k) * ((3 * n + 1).choose k : ℤ) * ((3 * n - k).choose (n - k) : ℤ)

/-- The conjectured recurrence for A386830. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    (16 * (n : ℤ) ^ 2 - 24 * (n : ℤ)) * a n
      + (-648 * (n : ℤ) ^ 2 + 1242 * (n : ℤ) - 480) * a (n - 1)
      + (3645 * (n : ℤ) ^ 2 - 7290 * (n : ℤ) + 3240) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a386830
