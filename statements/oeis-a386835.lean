import Mathlib

/-!
# A386835: a(n) = Sum_{k=0..n} binomial(2*n+2,k) * binomial(2*n-k-1,n-k).

Source: https://oeis.org/A386835
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 5, 30, 198, 1375, 9843, 71876, 532220, 3981645, ...
It is defined by the formula in the name of the entry, which is used here verbatim (the definition
below reproduces the data of the entry).

The conjecture (R. J. Mathar, Nov 02 2026) reads
  Conjecture D-finite with recurrence n*a(n) +(13*n-34)*a(n-1) +12*(-13*n+35)*a(n-2)
  +8*(-13*n-24)*a(n-3) +32*(2*n-5)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a386835

/-- A386835: a(n) = Sum_{k=0..n} binomial(2*n+2,k) * binomial(2*n-k-1,n-k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ((2 * n + 2).choose k : ℤ) * ((2 * n - k - 1).choose (n - k) : ℤ)

/-- The conjectured recurrence for A386835. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (n : ℤ) * a n + (13 * (n : ℤ) - 34) * a (n - 1) + (-156 * (n : ℤ) + 420) * a (n - 2)
      + (-104 * (n : ℤ) - 192) * a (n - 3) + (64 * (n : ℤ) - 160) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a386835
