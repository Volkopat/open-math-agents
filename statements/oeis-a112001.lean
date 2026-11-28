import Mathlib

/-!
# A112001: One fourth of fourth column (k=3) of triangle A111999.

Source: https://oeis.org/A112001
Credit: @agchua

R. J. Mathar (Jul 09 2017), in the formula section of A112001:
  Conjecture: +n*(20*n^2+75*n+67)*a(n) +(2*n+5)*(n+2)*(20*n^2+115*n+162)*a(n-1)=0.
The offset is 0 (data 6, -231, 6608, -176330, 4714710, ...). As the name says, a(n) is one
fourth of the column k = 3 of A111999: a(n) = A111999(n+4, 3)/4, n >= 0. This reproduces all
listed terms. (The formula section writes a(n)=A112492(n+4, 3)/4; A112492 is a different
triangle with positive entries, so that A-number is a slip for A111999, which the name line,
the comments of A111999 and the data all point to.)

The triangle A111999 (rows n >= 1, 0 <= k <= n - 1; data -1; 3, 2; -15, -20, -6; ...) is taken
from the recurrence in its formula section (also its Mathematica program):
a(m, k) = 0 if m < k+1; a(1, 0) = -1; a(m, -1) := 0;
a(m, k) = -(2*m-k-1)*(a(m-1, k) + a(m-1, k-1)) else.
Below, `T m k` is a(m, k) for m, k >= 0: row 0 and the entries with m < k + 1 are 0, and the
case k = 0 uses a(m-1, -1) = 0. Values are integers, taken in the integers; the column of
A112001 is divided by 4 in the rationals.
The recurrence uses a(n-1), so the conjecture is stated for n >= 1.
-/

namespace OMA.S_oeis_a112001

/-- The triangle A111999 by its recurrence: `T m k` = a(m, k). -/
def T : ℕ → ℕ → ℤ
  | 0, _ => 0
  | 1, 0 => -1
  | 1, _ + 1 => 0
  | m + 2, 0 => -(2 * ((m : ℤ) + 2) - 1) * T (m + 1) 0
  | m + 2, k + 1 =>
      if m + 2 < k + 2 then 0
      else -(2 * ((m : ℤ) + 2) - ((k : ℤ) + 1) - 1) * (T (m + 1) (k + 1) + T (m + 1) k)

/-- A112001(n) = A111999(n+4, 3)/4. -/
def a (n : ℕ) : ℚ := (T (n + 4) 3 : ℚ) / 4

/-- Mathar's conjecture: for n >= 1,
n(20n^2+75n+67) a(n) + (2n+5)(n+2)(20n^2+115n+162) a(n-1) = 0. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (n : ℚ) * (20 * (n : ℚ) ^ 2 + 75 * (n : ℚ) + 67) * a n
      + (2 * (n : ℚ) + 5) * ((n : ℚ) + 2) * (20 * (n : ℚ) ^ 2 + 115 * (n : ℚ) + 162)
        * a (n - 1) = 0 := by
  sorry

end OMA.S_oeis_a112001
