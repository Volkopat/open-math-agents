import Mathlib

/-!
# A386862: a(n) = Sum_{k=0..n} 2^(n-k) * binomial(2*n+1,k) * binomial(2*n-k-1,n-k).

Source: https://oeis.org/A386862
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 5, 42, 409, 4238, 45414, 496996, 5517929, 61909878, ...
It is defined by the formula in the name of the entry, which is used here verbatim (the definition
below reproduces the data of the entry).

The conjecture (R. J. Mathar, Nov 02 2026) reads
  Conjecture D-finite with recurrence +8*n*a(n) +2*(-19*n-28)*a(n-1) +3*(-223*n+523)*a(n-2)
  +162*(-2*n+3)*a(n-3)=0
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a386862

/-- A386862: a(n) = Sum_{k=0..n} 2^(n-k) * binomial(2*n+1,k) * binomial(2*n-k-1,n-k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (2 : ℤ) ^ (n - k) * ((2 * n + 1).choose k : ℤ) * ((2 * n - k - 1).choose (n - k) : ℤ)

/-- The conjectured recurrence for A386862. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (8 * (n : ℤ)) * a n + (-38 * (n : ℤ) - 56) * a (n - 1) + (-669 * (n : ℤ) + 1569) * a (n - 2)
      + (-324 * (n : ℤ) + 486) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a386862
