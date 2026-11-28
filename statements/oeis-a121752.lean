import Mathlib

/-!
# A121752: Mathar's recurrence

Source: https://oeis.org/A121752
Credit: @ivillar

Status: open conjecture (R. J. Mathar, Jul 26 2022); the entry records it as a conjecture and notes no proof or
verification of it. It follows from the recurrence with factorials recorded in the entry, which is used as
the definition here.

A121752 (offset 1): number of columns ending at an odd level in all deco polyominoes of height n;
data 1, 2, 7, 39, 235, 1746, 14166, 132408, 1341432, 15148080, 183764880, 2435607360, ...

Conjecture (R. J. Mathar, Jul 26 2022): D-finite with recurrence
(-460*n+1223)*a(n) +(460*n^2+460*n-5569)*a(n-1) +(460*n^3-3826*n^2+7853*n+1313)*a(n-2)
+(-460*n^4+1840*n^3+5501*n^2-31045*n+31726)*a(n-3)
+(1223*n^4-13205*n^3+45787*n^2-51389*n+558)*a(n-4) -2*(426*n-1111)*(n-6)*(n-4)^2*a(n-5) = 0.

Formalization: the entry records the recurrence relation
a(n) = (2n-3)*a(n-1) - (n-1)*(n-3)*a(n-2) + (n-2)!*(n*floor(n/2) - (n-2)*floor((n-1)/2) - 1), a(1)=1, a(2)=2,
and this recurrence, read in ℚ, is the definition of a(n) used here (the value a(0) = 0 is a
placeholder and is not used). The sequence has offset 1 and the recurrence involves a(n-5), so it
is stated for n ≥ 6, where every index is at least the offset; it is checked by the data, for example at
n = 6: (-1537)*(1746) + (13751)*(235) + (10055)*(39) + (-155228)*(7) + (73284)*(2) + (0)*(1) = 0.
-/

namespace OMA.S_oeis_a121752

/-- a(1)=1, a(2)=2, a(n) = (2n-3) a(n-1) - (n-1)(n-3) a(n-2) + (n-2)! (n floor(n/2) - (n-2) floor((n-1)/2) - 1) for n ≥ 3
(a(0) = 0 is a placeholder). -/
def a : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | (n + 3) => (2 * ((n : ℚ) + 3) - 3) * a (n + 2) - ((n : ℚ) + 3 - 1) * ((n : ℚ) + 3 - 3) * a (n + 1) +
      ((n + 1).factorial : ℚ) * (((n : ℚ) + 3) * (((n + 3) / 2 : ℕ) : ℚ) -
        ((n : ℚ) + 3 - 2) * (((n + 2) / 2 : ℕ) : ℚ) - 1)

/-- Mathar's conjectured recurrence for A121752, for n ≥ 6. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (1223 - 460 * (n : ℚ)) * a n + (-5569 + 460 * (n : ℚ) + 460 * (n : ℚ) ^ 2) * a (n - 1) +
      (1313 + 7853 * (n : ℚ) - 3826 * (n : ℚ) ^ 2 + 460 * (n : ℚ) ^ 3) * a (n - 2) + (31726 - 31045 * (n : ℚ) + 5501 * (n : ℚ) ^ 2 + 1840 * (n : ℚ) ^ 3 - 460 * (n : ℚ) ^ 4) * a (n - 3) +
      (558 - 51389 * (n : ℚ) + 45787 * (n : ℚ) ^ 2 - 13205 * (n : ℚ) ^ 3 + 1223 * (n : ℚ) ^ 4) * a (n - 4) + (-213312 + 224000 * (n : ℚ) - 85636 * (n : ℚ) ^ 2 + 14150 * (n : ℚ) ^ 3 - 852 * (n : ℚ) ^ 4) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a121752
