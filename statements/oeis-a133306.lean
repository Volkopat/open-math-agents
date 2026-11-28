import Mathlib

/-!
# A133306: a(n) = (1/n)*Sum_{i=0..n-1} C(n,i)*C(n,i+1)*5^i*6^(n-i), a(0) = 1.

Source: https://oeis.org/A133306
Credit: @vivanpoddar

The sequence (offset 0) is 1, 6, 66, 906, 13926, 229326, ... The defining formula of the entry is used as the
definition (the sum is divisible by n; the value is taken in the rationals).

The conjecture (R. J. Mathar) reads
(n+1)*a(n) + 11*(-2*n+1)*a(n-1) + (n-2)*a(n-2) = 0.
It involves a(n-2), so it is stated for n >= 2.
-/

namespace OMA.S_oeis_a133306

/-- A133306 (offset 0): a(0) = 1 and a(n) = (1/n)*Sum_{i=0..n-1} C(n,i)*C(n,i+1)*5^i*6^(n-i). -/
def a (n : ℕ) : ℚ :=
  if n = 0 then 1
  else (∑ i ∈ Finset.range n, (n.choose i : ℚ) * (n.choose (i + 1) : ℚ) * 5 ^ i * 6 ^ (n - i)) / n

/-- Mathar's conjectured recurrence for A133306. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    ((n : ℚ) + 1) * a n + 11 * (-2 * (n : ℚ) + 1) * a (n - 1) + ((n : ℚ) - 2) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a133306
