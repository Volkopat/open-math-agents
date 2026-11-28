import Mathlib

/-!
# A064088: Generalized Catalan numbers C(5; n).

Source: https://oeis.org/A064088
Credit: @vivanpoddar

The sequence (offset 0) is 1, 1, 6, 61, 766, 10746, 161376, ... The OEIS entry gives the formula
a(n) = Sum_{m=0..n-1} (n-m)*binomial(n-1+m, m)*(5^m)/n for n >= 1, with a(0) = 1,
which is used here as the definition (the sum is divisible by n; the value is taken in the rationals).

The conjecture (R. J. Mathar, Jun 07 2013) reads
4*n*a(n) + (-79*n+120)*a(n-1) + 10*(-2*n+3)*a(n-2) = 0.
It involves a(n-2), so it is stated for n >= 2.
-/

namespace OMA.S_oeis_a064088

/-- A064088 (offset 0): a(0) = 1 and a(n) = (Sum_{m=0..n-1} (n-m)*binomial(n-1+m, m)*5^m)/n. -/
def a (n : ℕ) : ℚ :=
  if n = 0 then 1
  else (∑ m ∈ Finset.range n, ((n : ℚ) - m) * ((n - 1 + m).choose m : ℚ) * 5 ^ m) / n

/-- Mathar's conjectured recurrence for A064088. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    4 * (n : ℚ) * a n + (-79 * (n : ℚ) + 120) * a (n - 1)
      + 10 * (-2 * (n : ℚ) + 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a064088
