import Mathlib

/-!
# A121580: Mathar's recurrence

Source: https://oeis.org/A121580
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there. It follows
from the first-order recurrence with factorials recorded in the entry, which is used as the
definition here.

A121580 (offset 1): number of cells in column 1 of all deco polyominoes of height n. A deco polyomino is a directed column-convex polyomino in which the height, measured along the diagonal, is attained only in the last column;
data 1, 3, 11, 53, 317, 2237, 18077, 164237, 1656077, 18348557, 221561357, ...

Conjecture (R. J. Mathar, Jul 26 2022): D-finite with recurrence
a(n) +(-n-4)*a(n-1) +3*(n+1)*a(n-2) +2*(-2*n+3)*a(n-3) +2*(n-3)*a(n-4) = 0.

Formalization: the entry records a(1) = 1, a(n) = a(n-1) + (n-1)!*(1 + n*(n-1)/2) for n ≥ 2, and this
recurrence, read in ℚ, is the definition of a(n) used here (the value a(0) = 0 is a placeholder and is
not used). The sequence has offset 1 and the recurrence involves a(n-4), so it is stated for n ≥ 5;
it is checked by the data, for example at n = 5: (1)*(317) + (-9)*(53) + (18)*(11) + (-14)*(3) + (4)*(1) = 0.
-/

namespace OMA.S_oeis_a121580

/-- a(1) = 1, a(n) = a(n-1) + (n-1)!*(1 + n*(n-1)/2) for n ≥ 2 (a(0) = 0 is a placeholder). -/
def a : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | (n + 2) => a (n + 1) + ((n + 1).factorial : ℚ) * (1 + ((n : ℚ) + 2) * ((n : ℚ) + 1) / 2)

/-- Mathar's conjectured recurrence for A121580, for n ≥ 5. -/
theorem main : ∀ n : ℕ, 5 ≤ n →
    a n + (-(n : ℚ) - 4) * a (n - 1) + 3 * ((n : ℚ) + 1) * a (n - 2) +
      2 * (-2 * (n : ℚ) + 3) * a (n - 3) + 2 * ((n : ℚ) - 3) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a121580
