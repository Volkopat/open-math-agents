import Mathlib

/-!
# A026021: a(n) = T(n, [n/2]), where T is the array defined in A026009

Source: https://oeis.org/A026021
Triangle: https://oeis.org/A026009
Credit: @xor2k
Sibling of OEIS A026008 (same conjecture wording); statement modelled on the accepted one for that entry.

Formalizes the OEIS A026021 conjecture (R. J. Mathar, 2013, offset 0):
-(n+7)*(5*n-34)*a(n) + 8*(-n-14)*a(n-1) + (27*n^2-83*n-428)*a(n-2) + 8*(4*n+5)*a(n-3)
44*(n-3)*(7*n-27)*a(n-4) = 0.

Conventions.
- The array T of A026009 is given by the formula recorded there (D. Marinov),
  T(n, k) = binomial(n, k) - binomial(n, k-3), where binomial(n, k-3) = 0 for k < 3.
  The entry A026021 records the same formula, a(n) = binomial(n, [n/2]) - binomial(n, [n/2]-3).
  This reproduces the tabulated rows of A026009 and the data of A026021. Values are taken in the
  rationals, as in the template entry.
- The printed formula has no operator between a(n-3) and 44*(n-3)*(7*n-27)*a(n-4). Neither
  +44 nor -44 makes the identity true (both already fail at n = 4), while the coefficient -4
  makes it hold for every n with four predecessors. We read the garbled 44 as - 4.
- The recurrence uses a(n-4), so it is stated for all n >= 4 (the first index with four
  predecessors in offset 0); index subtractions are then exact.
-/

namespace OMA.S_oeis_a026021

/-- The array of A026009: `T(n, k) = binomial(n, k) - binomial(n, k-3)`, the second term being
zero when `k < 3`. -/
def T (n k : ℕ) : ℚ :=
  (n.choose k : ℚ) - if 3 ≤ k then (n.choose (k - 3) : ℚ) else 0

/-- A026021: `a(n) = T(n, [n/2])`. -/
def a (n : ℕ) : ℚ := T n (n / 2)

/-- Mathar's recurrence for A026021, with the last coefficient read as `-4`. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    -((n : ℚ) + 7) * (5 * (n : ℚ) - 34) * a n + 8 * (-(n : ℚ) - 14) * a (n - 1)
      + (27 * (n : ℚ) ^ 2 - 83 * (n : ℚ) - 428) * a (n - 2)
      + 8 * (4 * (n : ℚ) + 5) * a (n - 3)
      - 4 * ((n : ℚ) - 3) * (7 * (n : ℚ) - 27) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026021
