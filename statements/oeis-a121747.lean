import Mathlib

/-!
# A121747: Mathar's recurrence

Source: https://oeis.org/A121747
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there. It follows
from the recurrence relation recorded in the entry, which is used as the definition here.

A121747 (offset 1): number of columns of odd length in all deco polyominoes of height n;
data 1, 2, 8, 44, 262, 1938, 15600, 145086, 1461888, 16438446, 198598860, 2623055166, ...

Conjecture (R. J. Mathar, Jul 26 2022): D-finite with recurrence
(-9*n+38)*a(n) +3*(3*n^2-19*n+27)*a(n-1) +(9*n^3-37*n^2-24*n+127)*a(n-2)
+(-9*n^4+102*n^3-392*n^2+525*n-85)*a(n-3) -(n-3)*(28*n^3-223*n^2+510*n-237)*a(n-4)
-(19*n-15)*(n-3)*(n-4)^2*a(n-5) = 0.

Formalization: the entry records a(n) = n*a(n-1) - d(n-1) + (n-1)!*floor(n/2) for n ≥ 2, a(1) = 1,
where d(1)=1, d(2)=0, d(2n) = 3!+5!+...+(2n-1)!, d(2n+1) = -d(2n). Here d is defined by d(1) = 1,
d(n+2) = d(n) + (n+1)! for even n and d(n+2) = -d(n+1) for odd n, with the auxiliary value d(0) = -1;
this gives d(2) = 0, d(2n) = 3!+...+(2n-1)! and d(2n+1) = -d(2n) for n ≥ 1, as in the entry, and d(0) is
not used in the definition of a(n). The recurrence of the entry is the definition of a(n) used here
(with values in ℤ; the floor is a natural number division, and a(0) = 0 is a placeholder that is not
used). The sequence has offset 1 and the recurrence involves a(n-5), so it is stated for n ≥ 6;
on the data the left side vanishes at n = 6, 7, 8.
-/

namespace OMA.S_oeis_a121747

/-- d(1)=1, d(2)=0, d(2n) = 3!+5!+...+(2n-1)!, d(2n+1) = -d(2n) (d(0) = -1 is an auxiliary value). -/
def d : ℕ → ℤ
  | 0 => -1
  | 1 => 1
  | (n + 2) => if n % 2 = 0 then d n + ((n + 1).factorial : ℤ) else -(d (n + 1))

/-- a(1) = 1, a(n) = n*a(n-1) - d(n-1) + (n-1)!*floor(n/2) for n ≥ 2 (a(0) = 0 is a placeholder). -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | (n + 2) => ((n : ℤ) + 2) * a (n + 1) - d (n + 1) + ((n + 1).factorial : ℤ) * (((n + 2) / 2 : ℕ) : ℤ)

/-- Mathar's conjectured recurrence for A121747, for n ≥ 6. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (38 - 9 * (n : ℤ)) * a n + (81 - 57 * (n : ℤ) + 9 * (n : ℤ) ^ 2) * a (n - 1) +
      (127 - 24 * (n : ℤ) - 37 * (n : ℤ) ^ 2 + 9 * (n : ℤ) ^ 3) * a (n - 2) + (-85 + 525 * (n : ℤ) - 392 * (n : ℤ) ^ 2 + 102 * (n : ℤ) ^ 3 - 9 * (n : ℤ) ^ 4) * a (n - 3) +
      (-711 + 1767 * (n : ℤ) - 1179 * (n : ℤ) ^ 2 + 307 * (n : ℤ) ^ 3 - 28 * (n : ℤ) ^ 4) * a (n - 4) + (-720 + 1512 * (n : ℤ) - 925 * (n : ℤ) ^ 2 + 224 * (n : ℤ) ^ 3 - 19 * (n : ℤ) ^ 4) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a121747
