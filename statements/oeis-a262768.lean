import Mathlib

/-!
# A262768: Mathar's recurrence

Source: https://oeis.org/A262768
Credit: @ivillar

Vladimir Kruchinin's sequence a(n) = binomial(2n+2, n) - 2*binomial(2n, n) + binomial(2n-2, n)
(offset 0; data 0, 0, 4, 20, 85, 344, ...). R. J. Mathar conjectured (Jun 07 2016) the recurrence
-2*(n+2)*(49*n-95)*a(n) + 325*(n-1)*(n+1)*a(n-1) + 2*(67*n-38)*(2*n-5)*a(n-2) = 0.

Status: the recurrence fails at n = 2 (the left side is -96 there); `main` is the corrected
recurrence (n ≥ 3).

Formalization notes:
* The terms are computed in ℤ. At n = 0 the entry's programs take binomial(-2, 0) = 1; the
  truncated `2 * n - 2 = 0` in ℕ gives the same value, and for n ≥ 1 no truncation occurs.
* The recurrence is stated for n ≥ 3, where all three terms are defined by the formula; at n = 2
  the left side equals -96 (with a(0) = a(1) = 0, a(2) = 4).
-/

namespace OMA.S_oeis_a262768

/-- A262768: `binomial(2n+2, n) - 2*binomial(2n, n) + binomial(2n-2, n)`. -/
def a (n : ℕ) : ℤ :=
  ((2 * n + 2).choose n : ℤ) - 2 * ((2 * n).choose n : ℤ) + ((2 * n - 2).choose n : ℤ)

/-- Mathar's conjectured recurrence for A262768, for every `n ≥ 3`. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    -2 * ((n : ℤ) + 2) * (49 * n - 95) * a n + 325 * ((n : ℤ) - 1) * (n + 1) * a (n - 1) +
      2 * (67 * (n : ℤ) - 38) * (2 * n - 5) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a262768
