import Mathlib

/-!
# A386836: a(n) = Sum_{k=0..n} binomial(3*n+2,k) * binomial(3*n-k-1,n-k).

Source: https://oeis.org/A386836
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 7, 70, 782, 9199, 111465, 1376764, 17234600, 217891693, ...
It is defined by the formula in the name of the entry, which is used here verbatim (the definition
below reproduces the data of the entry).

The conjecture (R. J. Mathar, Nov 02 2026) reads
  Conjecture D-finite with recurrence n*(2*n-1)*a(n) +(-41*n^2+66*n-24)*a(n-1)
  +(-509*n^2+3976*n-6392)*a(n-2) +(10133*n^2-69966*n+116776)*a(n-3) -1065*(3*n-7)*(3*n-8)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a386836

/-- A386836: a(n) = Sum_{k=0..n} binomial(3*n+2,k) * binomial(3*n-k-1,n-k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ((3 * n + 2).choose k : ℤ) * ((3 * n - k - 1).choose (n - k) : ℤ)

/-- The conjectured recurrence for A386836. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (2 * (n : ℤ) ^ 2 - (n : ℤ)) * a n + (-41 * (n : ℤ) ^ 2 + 66 * (n : ℤ) - 24) * a (n - 1)
      + (-509 * (n : ℤ) ^ 2 + 3976 * (n : ℤ) - 6392) * a (n - 2)
      + (10133 * (n : ℤ) ^ 2 - 69966 * (n : ℤ) + 116776) * a (n - 3)
      + (-9585 * (n : ℤ) ^ 2 + 47925 * (n : ℤ) - 59640) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a386836
