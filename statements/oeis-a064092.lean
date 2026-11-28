import Mathlib

/-!
# A064092: Generalized Catalan numbers C(9; n).

Source: https://oeis.org/A064092
Credit: @vivanpoddar

The sequence (offset 0) is 1, 1, 10, 181, 4078, 102826, 2777212, ... The OEIS entry gives the formula
a(n) = Sum_{m=0..n-1} (n-m)*binomial(n-1+m, m)*(9^m)/n for n >= 1, with a(0) = 1,
which is used here as the definition (the sum is divisible by n; the value is taken in the rationals).

The conjecture (R. J. Mathar, Jun 07 2013) reads
8*n*a(n) + (-287*n+432)*a(n-1) + 18*(-2*n+3)*a(n-2) = 0.
It involves a(n-2), so it is stated for n >= 2.
-/

namespace OMA.S_oeis_a064092

/-- A064092 (offset 0): a(0) = 1 and a(n) = (Sum_{m=0..n-1} (n-m)*binomial(n-1+m, m)*9^m)/n. -/
def a (n : ℕ) : ℚ :=
  if n = 0 then 1
  else (∑ m ∈ Finset.range n, ((n : ℚ) - m) * ((n - 1 + m).choose m : ℚ) * 9 ^ m) / n

/-- Mathar's conjectured recurrence for A064092. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    8 * (n : ℚ) * a n + (-287 * (n : ℚ) + 432) * a (n - 1)
      + 18 * (-2 * (n : ℚ) + 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a064092
