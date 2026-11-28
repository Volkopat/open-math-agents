import Mathlib

/-!
# A386831: a(n) = Sum_{k=0..n} 3^k * 2^(n-k) * binomial(4*n+1,k) * binomial(4*n-k,n-k).

Source: https://oeis.org/A386831
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 23, 814, 32102, 1330436, 56734023, 2464566064, 108464237352, 4819668737436, ...
It is defined by the formula in the name of the entry, which is used here verbatim (the definition
below reproduces the data of the entry).

The conjecture (R. J. Mathar, Nov 02 2026) reads
  Conjecture D-finite with recurrence 18744*n*(3*n-1)*(3*n-2)*a(n) +(203878391*n^3
  -1040550807*n^2+1658851582*n -822702720) *a(n-1) +27*(-252935041*n^3 +1277608165*n^2
  -1931547954*n +777640080)*a(n-2) +3645*(-38797609*n^3 +259381745*n^2 -614869982*n
  +523823440)*a(n-3) -16309333800*(2*n-7) *(4*n-13) *(4*n-11)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a386831

/-- A386831: a(n) = Sum_{k=0..n} 3^k * 2^(n-k) * binomial(4*n+1,k) * binomial(4*n-k,n-k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (3 : ℤ) ^ k * (2 : ℤ) ^ (n - k) * ((4 * n + 1).choose k : ℤ) * ((4 * n - k).choose (n - k) : ℤ)

/-- The conjectured recurrence for A386831. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (168696 * (n : ℤ) ^ 3 - 168696 * (n : ℤ) ^ 2 + 37488 * (n : ℤ)) * a n
      + (203878391 * (n : ℤ) ^ 3 - 1040550807 * (n : ℤ) ^ 2 + 1658851582 * (n : ℤ) - 822702720) * a (n - 1)
      + (-6829246107 * (n : ℤ) ^ 3 + 34495420455 * (n : ℤ) ^ 2 - 52151794758 * (n : ℤ) + 20996282160) * a (n - 2)
      + (-141417284805 * (n : ℤ) ^ 3 + 945446460525 * (n : ℤ) ^ 2 - 2241201084390 * (n : ℤ) + 1909336438800) * a (n - 3)
      + (-521898681600 * (n : ℤ) ^ 3 + 4958037475200 * (n : ℤ) ^ 2 - 15624341780400 * (n : ℤ) + 16325643133800) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a386831
