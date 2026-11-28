import Mathlib

/-!
# A112000: One half of third column (k=2) of triangle A111999.

Source: https://oeis.org/A112000
Credit: @agchua

R. J. Mathar (Jul 09 2017), in the formula section of A112000:
  Conjecture: +n*(4*n+5)*a(n) +(2*n+3)*(n+2)*(4*n+9)*a(n-1)=0.
The formula section also says a(n) = A111999(n+3, 2)/2, n >= 0, and the offset is 0
(data -3, 65, -1190, 22050, -433125, ...).

The triangle A111999 (rows n >= 1, 0 <= k <= n - 1; data -1; 3, 2; -15, -20, -6; ...) is taken
from the recurrence in its formula section (also its Mathematica program):
a(m, k) = 0 if m < k+1; a(1, 0) = -1; a(m, -1) := 0;
a(m, k) = -(2*m-k-1)*(a(m-1, k) + a(m-1, k-1)) else.
Below, `T m k` is a(m, k) for m, k >= 0: row 0 and the entries with m < k + 1 are 0, and the
case k = 0 uses a(m-1, -1) = 0. Values are integers, taken in the integers; the column of
A112000 is halved in the rationals.
The recurrence uses a(n-1), so the conjecture is stated for n >= 1.
-/

namespace OMA.S_oeis_a112000

/-- The triangle A111999 by its recurrence: `T m k` = a(m, k). -/
def T : ℕ → ℕ → ℤ
  | 0, _ => 0
  | 1, 0 => -1
  | 1, _ + 1 => 0
  | m + 2, 0 => -(2 * ((m : ℤ) + 2) - 1) * T (m + 1) 0
  | m + 2, k + 1 =>
      if m + 2 < k + 2 then 0
      else -(2 * ((m : ℤ) + 2) - ((k : ℤ) + 1) - 1) * (T (m + 1) (k + 1) + T (m + 1) k)

/-- A112000(n) = A111999(n+3, 2)/2. -/
def a (n : ℕ) : ℚ := (T (n + 3) 2 : ℚ) / 2

/-- Mathar's conjecture: for n >= 1, n(4n+5) a(n) + (2n+3)(n+2)(4n+9) a(n-1) = 0. -/
theorem main : ∀ n : ℕ, 1 ≤ n →
    (n : ℚ) * (4 * (n : ℚ) + 5) * a n
      + (2 * (n : ℚ) + 3) * ((n : ℚ) + 2) * (4 * (n : ℚ) + 9) * a (n - 1) = 0 := by
  sorry

end OMA.S_oeis_a112000
