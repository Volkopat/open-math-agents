import Mathlib

/-!
# A236407: a(n) = 2*Sum_{k=0..n-1} C(n-1,k)*C(n+k,k) + n.

Source: https://oeis.org/A236407
Credit: @vivanpoddar

The sequence (offset 0) begins 0, 3, 10, 41, 196, 1007, 5342, 28821, 157192, ...
It is defined by the formula in the name of the entry, which is used here verbatim (the definition
below reproduces the data of the entry).

The conjecture (R. J. Mathar, Feb 01 2014) reads
  Conjecture: n*(n-3)*a(n) -4*(2*n-1)*(n-3)*a(n-1) +2*(7*n^2-28*n+20)*a(n-2)
  -4*(n-1)*(2*n-7)*a(n-3) +(n-1)*(n-4)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a236407

/-- A236407: a(n) = 2*Sum_{k=0..n-1} C(n-1,k)*C(n+k,k) + n. -/
def a (n : ℕ) : ℤ :=
  2 * ∑ k ∈ Finset.range n, ((n - 1).choose k : ℤ) * ((n + k).choose k : ℤ) + (n : ℤ)

/-- The conjectured recurrence for A236407. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) ^ 2 - 3 * (n : ℤ)) * a n + (-8 * (n : ℤ) ^ 2 + 28 * (n : ℤ) - 12) * a (n - 1)
      + (14 * (n : ℤ) ^ 2 - 56 * (n : ℤ) + 40) * a (n - 2)
      + (-8 * (n : ℤ) ^ 2 + 36 * (n : ℤ) - 28) * a (n - 3)
      + ((n : ℤ) ^ 2 - 5 * (n : ℤ) + 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a236407
