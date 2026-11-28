import Mathlib

/-!
# A386833: a(n) = Sum_{k=0..n} binomial(3*n+1,k) * binomial(3*n-k-1,n-k).

Source: https://oeis.org/A386833
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 6, 59, 656, 7701, 93210, 1150495, 14395428, 181936169, ...
It is defined by the formula in the name of the entry, which is used here verbatim (the definition
below reproduces the data of the entry).

The conjecture (R. J. Mathar, Nov 02 2026) reads
  Conjecture D-finite with recurrence n*(2*n-1)*a(n) +(-59*n^2+131*n-78)*a(n-1)
  +3*(90*n^2-149*n-124)*a(n-2) +3*(793*n^2-5995*n+10510)*a(n-3) +288*-(3*n-8)*(3*n-10)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a386833

/-- A386833: a(n) = Sum_{k=0..n} binomial(3*n+1,k) * binomial(3*n-k-1,n-k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ((3 * n + 1).choose k : ℤ) * ((3 * n - k - 1).choose (n - k) : ℤ)

/-- The conjectured recurrence for A386833. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (2 * (n : ℤ) ^ 2 - (n : ℤ)) * a n + (-59 * (n : ℤ) ^ 2 + 131 * (n : ℤ) - 78) * a (n - 1)
      + (270 * (n : ℤ) ^ 2 - 447 * (n : ℤ) - 372) * a (n - 2)
      + (2379 * (n : ℤ) ^ 2 - 17985 * (n : ℤ) + 31530) * a (n - 3)
      + (-2592 * (n : ℤ) ^ 2 + 15552 * (n : ℤ) - 23040) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a386833
