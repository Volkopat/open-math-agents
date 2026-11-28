import Mathlib

/-!
# A241193: a(n) = Sum_{k=1..n} ((3*n-k-1)/(2*n-k))*(3*n-k-2)!/((n-1)!*(n-1)!*(n-k)!).

Source: https://oeis.org/A241193
Credit: @vivanpoddar

The sequence (offset 1) begins 1, 11, 181, 3499, 73501, 1623467, 37081045, 867484331, 20661914989, ...
It is defined by the formula in the name of the entry, which is used here verbatim (the definition
below reproduces the data of the entry).

The conjecture (R. J. Mathar, Aug 26 2014) reads
  Conjecture: -(2*n-1)*(n-1)^2*a(n) +2*(32*n^3-131*n^2+187*n-94)*a(n-1)
  +3*(-86*n^3+721*n^2-1896*n+1617)*a(n-2) -18*(2*n-5)*(3*n-8)*(3*n-7)*a(n-3)=0
It involves a(n-3) and the offset is 1, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a241193

/-- A241193: a(n) = Sum_{k=1..n} ((3*n-k-1)/(2*n-k))*(3*n-k-2)!/((n-1)!*(n-1)!*(n-k)!). -/
def a (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.Icc 1 n, ((3 * (n : ℚ) - k - 1) / (2 * (n : ℚ) - k)) * ((3 * n - k - 2).factorial : ℚ)
    / (((n - 1).factorial : ℚ) * ((n - 1).factorial : ℚ) * ((n - k).factorial : ℚ))

/-- The conjectured recurrence for A241193. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (-2 * (n : ℚ) ^ 3 + 5 * (n : ℚ) ^ 2 - 4 * (n : ℚ) + 1) * a n
      + (64 * (n : ℚ) ^ 3 - 262 * (n : ℚ) ^ 2 + 374 * (n : ℚ) - 188) * a (n - 1)
      + (-258 * (n : ℚ) ^ 3 + 2163 * (n : ℚ) ^ 2 - 5688 * (n : ℚ) + 4851) * a (n - 2)
      + (-324 * (n : ℚ) ^ 3 + 2430 * (n : ℚ) ^ 2 - 6066 * (n : ℚ) + 5040) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a241193
