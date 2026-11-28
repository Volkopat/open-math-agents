import Mathlib

/-!
# A386834: a(n) = Sum_{k=0..n} binomial(4*n+1,k) * binomial(4*n-k-1,n-k).

Source: https://oeis.org/A386834
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 8, 111, 1738, 28701, 488412, 8473387, 148994510, 2645999673, ...
It is defined by the formula in the name of the entry, which is used here verbatim (the definition
below reproduces the data of the entry).

The conjecture (R. J. Mathar, Aug 19 2025) reads
  Conjecture D-finite with recurrence +3*n*(16543753*n -26995933)*(3*n-1)*(3*n-2)*a(n)
  +(-1669899251*n^4 -26931977989*n^3 +131963667975*n^2 -188283072995*n +85757456660)*a(n-1)
  +2*(-61301926003*n^4 +515926265010*n^3 -1655392333929*n^2 +2311146075302*n
  -1165379619540)*a(n-2) -96*(39221117*n -50949760)*(4*n-9)*(2*n-5)*(4*n-7)*a(n-3)=0
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a386834

/-- A386834: a(n) = Sum_{k=0..n} binomial(4*n+1,k) * binomial(4*n-k-1,n-k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ((4 * n + 1).choose k : ℤ) * ((4 * n - k - 1).choose (n - k) : ℤ)

/-- The conjectured recurrence for A386834. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (446681331 * (n : ℤ) ^ 4 - 1175571522 * (n : ℤ) ^ 3 + 828152709 * (n : ℤ) ^ 2 - 161975598 * (n : ℤ)) * a n
      + (-1669899251 * (n : ℤ) ^ 4 - 26931977989 * (n : ℤ) ^ 3 + 131963667975 * (n : ℤ) ^ 2 - 188283072995 * (n : ℤ) + 85757456660) * a (n - 1)
      + (-122603852006 * (n : ℤ) ^ 4 + 1031852530020 * (n : ℤ) ^ 3 - 3310784667858 * (n : ℤ) ^ 2 + 4622292150604 * (n : ℤ) - 2330759239080) * a (n - 2)
      + (-120487271424 * (n : ℤ) ^ 4 + 939684926976 * (n : ℤ) ^ 3 - 2696656153152 * (n : ℤ) ^ 2 + 3367511502240 * (n : ℤ) - 1540720742400) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a386834
