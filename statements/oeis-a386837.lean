import Mathlib

/-!
# A386837: a(n) = Sum_{k=0..n} binomial(4*n+2,k) * binomial(4*n-k-1,n-k).

Source: https://oeis.org/A386837
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 9, 126, 1978, 32703, 556887, 9665476, 170006256, 3019802253, ...
It is defined by the formula in the name of the entry, which is used here verbatim (the definition
below reproduces the data of the entry).

The conjecture (R. J. Mathar, Nov 02 2026) reads
  Conjecture D-finite with recurrence 3*n*(21719*n-23881)*(3*n-1)*(3*n-2)*a(n) +(15946643*n^4
  -186214804*n^3 +598016755*n^2 -732654974*n +305230680)*a(n-1) +2*(-243392909*n^4 +2086940959*n^3
  -6606906993*n^2 +8833336089*n -4155831354)*a(n-2) -32*(490377*n-550022)*(4*n-9)*(2*n-3)
  *(4*n-7)*a(n-3)=0
It involves a(n-3) and the offset is 0, so it is stated for n >= 3.
-/

namespace OMA.S_oeis_a386837

/-- A386837: a(n) = Sum_{k=0..n} binomial(4*n+2,k) * binomial(4*n-k-1,n-k). -/
def a (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), ((4 * n + 2).choose k : ℤ) * ((4 * n - k - 1).choose (n - k) : ℤ)

/-- The conjectured recurrence for A386837. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    (586413 * (n : ℤ) ^ 4 - 1231200 * (n : ℤ) ^ 3 + 775101 * (n : ℤ) ^ 2 - 143286 * (n : ℤ)) * a n
      + (15946643 * (n : ℤ) ^ 4 - 186214804 * (n : ℤ) ^ 3 + 598016755 * (n : ℤ) ^ 2 - 732654974 * (n : ℤ) + 305230680) * a (n - 1)
      + (-486785818 * (n : ℤ) ^ 4 + 4173881918 * (n : ℤ) ^ 3 - 13213813986 * (n : ℤ) ^ 2 + 17666672178 * (n : ℤ) - 8311662708) * a (n - 2)
      + (-502146048 * (n : ℤ) ^ 4 + 3325025792 * (n : ℤ) ^ 3 - 8087800256 * (n : ℤ) ^ 2 + 8562823968 * (n : ℤ) - 3326533056) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a386837
