import Mathlib

/-!
# A121751: Mathar's recurrence

Source: https://oeis.org/A121751
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there. It follows
from the recurrence with floor functions recorded in the entry, which is used as the definition here.

A121751 (offset 1): number of deco polyominoes of height n in which all columns end at an even level;
data 0, 1, 2, 4, 14, 44, 194, 812, 4362, 22716, 144282, 897636, 6587454, ...

Conjecture (R. J. Mathar, Jul 26 2022): D-finite with recurrence
+256*a(n) -384*a(n-1) +16*(-8*n^2+40*n-67)*a(n-2) +16*(8*n^2-54*n+87)*a(n-3)
+4*(4*n^4-56*n^3+242*n^2-304*n-21)*a(n-4) +4*(-2*n^4+38*n^3-249*n^2+647*n-554)*a(n-5)
+(n-4)*(n-8)*(n^2-12*n+31)*a(n-6) = 0.

Formalization: the entry records a(1)=0, a(2)=1 and
a(n) = 2*floor((n-1)/2)*a(n-1) - [floor((n-1)/2)*floor((n-2)/2) - 1]*a(n-2) for n ≥ 3, and this
recurrence is the definition of a(n) used here (with values in ℤ; the floors are natural number
divisions by 2, and the value a(0) = 0 is a placeholder that is not used). The sequence has offset 1
and the recurrence involves a(n-6), so it is stated for n ≥ 7; on the data the left side vanishes at
n = 7, 8, 9.
-/

namespace OMA.S_oeis_a121751

/-- a(1)=0, a(2)=1, a(n) = 2*floor((n-1)/2)*a(n-1) - (floor((n-1)/2)*floor((n-2)/2) - 1)*a(n-2) for
n ≥ 3 (a(0) = 0 is a placeholder). -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | (n + 3) => 2 * (((n + 2) / 2 : ℕ) : ℤ) * a (n + 2) -
      ((((n + 2) / 2 : ℕ) : ℤ) * (((n + 1) / 2 : ℕ) : ℤ) - 1) * a (n + 1)

/-- Mathar's conjectured recurrence for A121751, for n ≥ 7. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    (256) * a n + (-384) * a (n - 1) +
      (-1072 + 640 * (n : ℤ) - 128 * (n : ℤ) ^ 2) * a (n - 2) + (1392 - 864 * (n : ℤ) + 128 * (n : ℤ) ^ 2) * a (n - 3) +
      (-84 - 1216 * (n : ℤ) + 968 * (n : ℤ) ^ 2 - 224 * (n : ℤ) ^ 3 + 16 * (n : ℤ) ^ 4) * a (n - 4) + (-2216 + 2588 * (n : ℤ) - 996 * (n : ℤ) ^ 2 + 152 * (n : ℤ) ^ 3 - 8 * (n : ℤ) ^ 4) * a (n - 5) +
      (992 - 756 * (n : ℤ) + 207 * (n : ℤ) ^ 2 - 24 * (n : ℤ) ^ 3 + (n : ℤ) ^ 4) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a121751
