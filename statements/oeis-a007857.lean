import Mathlib

/-!
# A007857: Mathar's recurrence

Source: https://oeis.org/A007857
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there. It follows
from the closed form recorded in the entry, which is used as the definition here.

A007857 (offset 1): number of independent sets in rooted plane trees on n nodes;
data 1, 2, 8, 37, 184, 959, 5172, 28641, 162008, 932503, 5445934, 32197334, 192357788, ...

Conjecture (R. J. Mathar, Nov 26 2012): 2*n*(n - 1)*(2*n - 3)*(44*n - 69)*a(n)
+ (n - 1)*(176*n^3 - 9591*n^2 + 38703*n - 40640)*a(n-1)
+ (-17479*n^4 + 218005*n^3 - 959616*n^2 + 1797890*n - 1221920)*a(n-2)
+ 6*(3*n - 10)*(2*n - 7)*(3*n - 11)*(517*n - 1198)*a(n-3) = 0 for n >= 4.

Formalization: the entry records a(n+1) = (2/(n+1))*C(3*n, n) - (1/(n+1))*C(2*n, n) (Paul Barry,
Nov 05 2006), that is a(n) = (2*C(3(n-1), n-1) - C(2(n-1), n-1))/n for n ≥ 1; this formula, read in ℚ,
is the definition of a(n) used here (the value at n = 0 lies outside the offset and is not used).
The recurrence is stated for n ≥ 4, as in the entry; for example at n = 4:
(12840)*(37) + (-84060)*(8) + (93480)*(2) + (10440)*(1) = 0.
-/

namespace OMA.S_oeis_a007857

/-- a(n) = (2 C(3(n-1), n-1) - C(2(n-1), n-1))/n, the closed form recorded in the entry. -/
def a (n : ℕ) : ℚ :=
  (2 * ((3 * (n - 1)).choose (n - 1) : ℚ) - ((2 * (n - 1)).choose (n - 1) : ℚ)) / (n : ℚ)

/-- Mathar's conjectured recurrence for A007857, for n ≥ 4. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    2 * (n : ℚ) * ((n : ℚ) - 1) * (2 * (n : ℚ) - 3) * (44 * (n : ℚ) - 69) * a n +
      ((n : ℚ) - 1) * (176 * (n : ℚ) ^ 3 - 9591 * (n : ℚ) ^ 2 + 38703 * (n : ℚ) - 40640) * a (n - 1) +
      (-17479 * (n : ℚ) ^ 4 + 218005 * (n : ℚ) ^ 3 - 959616 * (n : ℚ) ^ 2 + 1797890 * (n : ℚ) - 1221920) * a (n - 2) +
      6 * (3 * (n : ℚ) - 10) * (2 * (n : ℚ) - 7) * (3 * (n : ℚ) - 11) * (517 * (n : ℚ) - 1198) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a007857
