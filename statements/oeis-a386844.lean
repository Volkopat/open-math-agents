import Mathlib

/-!
# A386844: a(n) = Sum_{k=0..n} binomial(3*n+2,k) * binomial(3*n-k,n-k).

Source: https://oeis.org/A386844
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 8, 83, 942, 11177, 136164, 1688031, 21187546, 268409813, ...
It is defined by the formula in the name of the entry, which is used here verbatim (the definition
below reproduces the data of the entry).

The conjecture (R. J. Mathar, Nov 02 2026) reads
  Conjecture D-finite with recurrence 3*n*(2*n-1)*a(n) +(-353*n^2+1009*n-672)*a(n-1)
  +(3938*n^2-15029*n+13872)*a(n-2) -399*(3*n-4)*(3*n-5)*a(n-3)=0
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a386844

/-- A386844: a(n) = Sum_{k=0..n} binomial(3*n+2,k) * binomial(3*n-k,n-k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ((3 * n + 2).choose k : ℤ) * ((3 * n - k).choose (n - k) : ℤ)

/-- The conjectured recurrence for A386844. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (6 * (n : ℤ) ^ 2 - 3 * (n : ℤ)) * a n
      + (-353 * (n : ℤ) ^ 2 + 1009 * (n : ℤ) - 672) * a (n - 1)
      + (3938 * (n : ℤ) ^ 2 - 15029 * (n : ℤ) + 13872) * a (n - 2)
      + (-3591 * (n : ℤ) ^ 2 + 10773 * (n : ℤ) - 7980) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a386844
