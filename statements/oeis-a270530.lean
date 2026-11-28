import Mathlib

/-!
# A270530: a(n) = Sum_{k=0..n}((binomial(2*k,k)/(k+1)*binomial(2*n+2,n-k))).

Source: https://oeis.org/A270530
Credit: @vivanpoddar

The sequence (offset 0) begins 1, 5, 23, 105, 484, 2267, 10821, 52705, 262010, ...
It is defined by the formula in the name of the entry, which is used here verbatim (the definition
below reproduces the data of the entry).

The conjecture (R. J. Mathar, Jun 07 2016) reads
  Conjecture: 2*n*(2*n+3)*(n+1)*a(n) -n*(77*n^2+27*n-4)*a(n-1) +(549*n^3-987*n^2+686*n-168)*a(n-2)
  -20*(2*n-3)*(43*n^2-104*n+70)*a(n-3) +500*(2*n-5)*(n-2)*(2*n-3)*a(n-4)=0
It involves a(n-4) and the offset is 0, so it is stated for n >= 4.
-/

namespace OMA.S_oeis_a270530

/-- A270530: a(n) = Sum_{k=0..n}((binomial(2*k,k)/(k+1)*binomial(2*n+2,n-k))). -/
def a (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range (n + 1), ((2 * k).choose k : ℚ) / ((k : ℚ) + 1) * ((2 * n + 2).choose (n - k) : ℚ)

/-- The conjectured recurrence for A270530. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    (4 * (n : ℚ) ^ 3 + 10 * (n : ℚ) ^ 2 + 6 * (n : ℚ)) * a n
      + (-77 * (n : ℚ) ^ 3 - 27 * (n : ℚ) ^ 2 + 4 * (n : ℚ)) * a (n - 1)
      + (549 * (n : ℚ) ^ 3 - 987 * (n : ℚ) ^ 2 + 686 * (n : ℚ) - 168) * a (n - 2)
      + (-1720 * (n : ℚ) ^ 3 + 6740 * (n : ℚ) ^ 2 - 9040 * (n : ℚ) + 4200) * a (n - 3)
      + (2000 * (n : ℚ) ^ 3 - 12000 * (n : ℚ) ^ 2 + 23500 * (n : ℚ) - 15000) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a270530
