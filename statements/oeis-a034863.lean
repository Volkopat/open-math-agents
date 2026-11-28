import Mathlib

/-!
# A034863: a(n) = n!*(4*n^3 - 30*n^2 + 40*n + 3)/24.

Source: https://oeis.org/A034863
Credit: @vivanpoddar

The sequence (offset 4) begins -61, -235, 810, 38850, 757680, 12836880, 212133600, 3554258400, 61372080000, ...
It is defined by the formula in the name of the entry, which is used here verbatim (the definition
below reproduces the data of the entry).

The conjecture (R. J. Mathar, Apr 03 2017) reads
  Conjecture: (-96*n + 27161)*a(n) + (96*n^2 - 99580*n + 199917)*a(n-1) +(72707*n -
  61983)*(n-1)*a(n-2) = 0
It involves a(n-2) and the offset is 4, so it is stated for n >= 6.
-/

namespace OMA.S_oeis_a034863

/-- A034863: a(n) = n!*(4*n^3 - 30*n^2 + 40*n + 3)/24. -/
def a (n : ℕ) : ℚ :=
  (n.factorial : ℚ) * (4 * (n : ℚ) ^ 3 - 30 * (n : ℚ) ^ 2 + 40 * (n : ℚ) + 3) / 24

/-- The conjectured recurrence for A034863. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (-96 * (n : ℚ) + 27161) * a n + (96 * (n : ℚ) ^ 2 - 99580 * (n : ℚ) + 199917) * a (n - 1)
      + (72707 * (n : ℚ) ^ 2 - 134690 * (n : ℚ) + 61983) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a034863
