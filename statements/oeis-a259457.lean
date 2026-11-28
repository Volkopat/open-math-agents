import Mathlib

/-!
# A259457: Mathar's recurrence

Source: https://oeis.org/A259457
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there. It follows
from the closed form recorded in the entry, which is used as the definition here.

A259457 (offset 0): from higher-order arithmetic progressions;
data 3, 66, 1050, 15300, 220500, 3245760, 49533120, 789264000, 13172544000, ...

Conjecture (R. J. Mathar, Jul 15 2015):
3*n*a(n) +(-3*n^2-19*n-44)*a(n-1) -2*(n+2)^2*a(n-2) = 0.

Formalization: the entry records the closed form a(n) = (n+3)!*(n+2)*(n+1)*(n+3)*(3*n+8)/96 (Georg
Fischer, Dec 06 2024), and this formula, read in ℚ, is the definition of a(n) used here. The recurrence
involves a(n-2), so it is stated for n ≥ 2; it is checked by the data, for example at n = 2:
(6)*(1050) + (-94)*(66) + (-32)*(3) = 0.
-/

namespace OMA.S_oeis_a259457

/-- a(n) = (n+3)! (n+2) (n+1) (n+3) (3n+8) / 96, the closed form recorded in the entry. -/
def a (n : ℕ) : ℚ :=
  ((n + 3).factorial : ℚ) * ((n : ℚ) + 2) * ((n : ℚ) + 1) * ((n : ℚ) + 3) * (3 * (n : ℚ) + 8) / 96

/-- Mathar's conjectured recurrence for A259457, for n ≥ 2. -/
theorem main : ∀ n : ℕ, 2 ≤ n →
    3 * (n : ℚ) * a n + (-3 * (n : ℚ) ^ 2 - 19 * (n : ℚ) - 44) * a (n - 1) -
      2 * ((n : ℚ) + 2) ^ 2 * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a259457
