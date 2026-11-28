import Mathlib

/-!
# A270490: a(n) = Sum_{i=0..(n+1)/2} binomial(2*i+1,i)*binomial(2*n-2*i,n)/(2*i+1).

Source: https://oeis.org/A270490
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 2, 7, 24, 87, 320, 1195, 4504, 17102, ...
It is defined by the formula in the name of the entry, which is used here verbatim (the definition
below reproduces the data of the entry).

The conjecture (R. J. Mathar, Jun 07 2016) reads
  Conjecture: 3*n*(n-2)*(n+2)*a(n) -4*(n+1)*(8*n^2-23*n+12)*a(n-1) +16*n *(3*n-4)*(2*n-5)*a(n-2)
  +8*(2*n-3)*(4*n-7)*a(n-3) -64*(2*n-5)*(n-3)*(2*n-3)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a270490

/-- A270490: a(n) = Sum_{i=0..(n+1)/2} binomial(2*i+1,i)*binomial(2*n-2*i,n)/(2*i+1). -/
def a (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range ((n + 1) / 2 + 1),
    ((2 * i + 1).choose i : ℚ) * ((2 * n - 2 * i).choose n : ℚ) / (2 * (i : ℚ) + 1)

/-- The conjectured recurrence for A270490. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (3 * (n : ℚ) ^ 3 - 12 * (n : ℚ)) * a n
      + (-32 * (n : ℚ) ^ 3 + 60 * (n : ℚ) ^ 2 + 44 * (n : ℚ) - 48) * a (n - 1)
      + (96 * (n : ℚ) ^ 3 - 368 * (n : ℚ) ^ 2 + 320 * (n : ℚ)) * a (n - 2)
      + (64 * (n : ℚ) ^ 2 - 208 * (n : ℚ) + 168) * a (n - 3)
      + (-256 * (n : ℚ) ^ 3 + 1792 * (n : ℚ) ^ 2 - 4032 * (n : ℚ) + 2880) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a270490
