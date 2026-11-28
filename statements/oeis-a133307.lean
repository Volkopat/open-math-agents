import Mathlib

/-!
# A133307: a(n) = (1/n)*Sum_{i=0..n-1} C(n,i)*C(n,i+1)*6^i*7^(n-i), a(0) = 1.

Source: https://oeis.org/A133307
Credit: @vivanpoddar

The sequence (offset 0) is 1, 7, 91, 1477, 26845, 522739, ... The defining formula of the entry is used as the
definition (the sum is divisible by n; the value is taken in the rationals).

The conjecture (R. J. Mathar) reads
(n+1)*a(n) + 13*(-2*n+1)*a(n-1) + (n-2)*a(n-2) = 0.
It involves a(n-2), so it is stated for n >= 2.
-/

namespace OMA.S_oeis_a133307

/-- A133307 (offset 0): a(0) = 1 and a(n) = (1/n)*Sum_{i=0..n-1} C(n,i)*C(n,i+1)*6^i*7^(n-i). -/
def a (n : ℕ) : ℚ :=
  if n = 0 then 1
  else (∑ i ∈ Finset.range n, (n.choose i : ℚ) * (n.choose (i + 1) : ℚ) * 6 ^ i * 7 ^ (n - i)) / n

/-- Mathar's conjectured recurrence for A133307. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    ((n : ℚ) + 1) * a n + 13 * (-2 * (n : ℚ) + 1) * a (n - 1) + ((n : ℚ) - 2) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a133307
