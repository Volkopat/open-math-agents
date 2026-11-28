import Mathlib

/-!
# A268554: Mathar's recurrence

Source: https://oeis.org/A268554
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there. It follows
from the closed form recorded in the entry, which is used as the definition here.

A268554 (offset 0): diagonal of the rational function 1/((1 - w - u v) * (1 - x y - x z - y z));
data 1, 36, 6300, 1552320, 445945500, 139815211536, 46384755633216, ...

Conjecture (R. J. Mathar, Mar 10 2016):
n^3*(2*n-1)*a(n) -6*(4*n-1)*(3*n-1)*(3*n-2)*(4*n-3)*a(n-1) = 0.

Formalization: the entry records the closed form a(n) = (4*n)! * (3*n)! / ((n!)^3 * (2*n)!^2) (Vaclav
Kotesovec, Jul 01 2016), and this formula, read in ℚ, is the definition of a(n) used here. The
recurrence involves a(n-1), so it is stated for n ≥ 1; it is checked by the data, for example at
n = 1: (1)*(36) - (36)*(1) = 0.
-/

namespace OMA.S_oeis_a268554

/-- a(n) = (4n)! (3n)! / ((n!)^3 ((2n)!)^2), the closed form recorded in the entry. -/
def a (n : ℕ) : ℚ :=
  ((4 * n).factorial : ℚ) * ((3 * n).factorial : ℚ) / ((n.factorial : ℚ) ^ 3 * ((2 * n).factorial : ℚ) ^ 2)

/-- Mathar's conjectured recurrence for A268554, for n ≥ 1. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (n : ℚ) ^ 3 * (2 * (n : ℚ) - 1) * a n -
      6 * (4 * (n : ℚ) - 1) * (3 * (n : ℚ) - 1) * (3 * (n : ℚ) - 2) * (4 * (n : ℚ) - 3) * a (n - 1) = 0 := by
  sorry

end OMA.S_oeis_a268554
