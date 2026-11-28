import Mathlib

/-!
# A386845: a(n) = Sum_{k=0..n} binomial(4*n+2,k) * binomial(4*n-k,n-k).

Source: https://oeis.org/A386845
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 10, 143, 2264, 37601, 642086, 11165395, 196658228, 3496849349, ...
It is defined by the formula in the name of the entry, which is used here verbatim (the definition
below reproduces the data of the entry).

The conjecture (R. J. Mathar, Nov 02 2026) reads
  Conjecture D-finite with recurrence 357*n*(3*n-1)*(3*n-2)*a(n) +(209315*n^3 -1243758*n^2
  +2143003*n -1111620)*a(n-1) +2*(-927859*n^3 -102078*n^2 +14674297*n -21847920)*a(n-2)
  +20*(-2949299*n^3 +26977560*n^2 -83822227*n +87003534)*a(n-3)
  -1778880*(2*n-5)*(4*n-13)*(4*n-11)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a386845

/-- A386845: a(n) = Sum_{k=0..n} binomial(4*n+2,k) * binomial(4*n-k,n-k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ((4 * n + 2).choose k : ℤ) * ((4 * n - k).choose (n - k) : ℤ)

/-- The conjectured recurrence for A386845. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (3213 * (n : ℤ) ^ 3 - 3213 * (n : ℤ) ^ 2 + 714 * (n : ℤ)) * a n
      + (209315 * (n : ℤ) ^ 3 - 1243758 * (n : ℤ) ^ 2 + 2143003 * (n : ℤ) - 1111620) * a (n - 1)
      + (-1855718 * (n : ℤ) ^ 3 - 204156 * (n : ℤ) ^ 2 + 29348594 * (n : ℤ) - 43695840) * a (n - 2)
      + (-58985980 * (n : ℤ) ^ 3 + 539551200 * (n : ℤ) ^ 2 - 1676444540 * (n : ℤ) + 1740070680) * a (n - 3)
      + (-56924160 * (n : ℤ) ^ 3 + 483855360 * (n : ℤ) ^ 2 - 1362622080 * (n : ℤ) + 1271899200) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a386845
