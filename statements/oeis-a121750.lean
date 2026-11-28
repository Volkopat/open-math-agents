import Mathlib

/-!
# A121750: Mathar's recurrence

Source: https://oeis.org/A121750
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there. It follows
from the recurrence relation recorded in the entry, which is used as the definition here.

A121750 (offset 1): number of columns of even length in all deco polyominoes of height n;
data 0, 1, 5, 26, 184, 1338, 11652, 108210, 1140336, 12849714, 159858900, 2117522754, ...

Conjecture (R. J. Mathar, Jul 26 2022): D-finite with recurrence
a(n) +(-n-2)*a(n-1) +(-n^2+4*n-2)*a(n-2) +(n^3-3*n^2-4*n+11)*a(n-3) -(n-1)*(n^2-11*n+26)*a(n-4)
+(-n^3+5*n^2+7*n-43)*a(n-5) +(n-3)*(n-5)^2*a(n-6) = 0.

Formalization: the entry records a(n) = n*a(n-1) + d(n-1) + (n-1)!*floor((n-1)/2) for n ≥ 2, a(1) = 0,
where d(1)=1, d(2)=0, d(2n) = 3!+5!+...+(2n-1)!, d(2n+1) = -d(2n). Here d is defined by d(1) = 1,
d(n+2) = d(n) + (n+1)! for even n and d(n+2) = -d(n+1) for odd n, with the auxiliary value d(0) = -1;
this gives d(2) = 0, d(2n) = 3!+...+(2n-1)! and d(2n+1) = -d(2n) for n ≥ 1, as in the entry, and d(0) is
not used in the definition of a(n). The recurrence of the entry is the definition of a(n) used here
(with values in ℤ; the floor is a natural number division, and a(0) = 0 is a placeholder that is not
used). The sequence has offset 1 and the recurrence involves a(n-6), so it is stated for n ≥ 7;
on the data the left side vanishes at n = 7, 8, 9.
-/

namespace OMA.S_oeis_a121750

/-- d(1)=1, d(2)=0, d(2n) = 3!+5!+...+(2n-1)!, d(2n+1) = -d(2n) (d(0) = -1 is an auxiliary value). -/
def d : ℕ → ℤ
  | 0 => -1
  | 1 => 1
  | (n + 2) => if n % 2 = 0 then d n + ((n + 1).factorial : ℤ) else -(d (n + 1))

/-- a(1) = 0, a(n) = n*a(n-1) + d(n-1) + (n-1)!*floor((n-1)/2) for n ≥ 2 (a(0) = 0 is a placeholder). -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 0
  | (n + 2) => ((n : ℤ) + 2) * a (n + 1) + d (n + 1) + ((n + 1).factorial : ℤ) * (((n + 1) / 2 : ℕ) : ℤ)

/-- Mathar's conjectured recurrence for A121750, for n ≥ 7. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    (1) * a n + (-2 - (n : ℤ)) * a (n - 1) +
      (-2 + 4 * (n : ℤ) - (n : ℤ) ^ 2) * a (n - 2) + (11 - 4 * (n : ℤ) - 3 * (n : ℤ) ^ 2 + (n : ℤ) ^ 3) * a (n - 3) +
      (26 - 37 * (n : ℤ) + 12 * (n : ℤ) ^ 2 - (n : ℤ) ^ 3) * a (n - 4) + (-43 + 7 * (n : ℤ) + 5 * (n : ℤ) ^ 2 - (n : ℤ) ^ 3) * a (n - 5) +
      (-75 + 55 * (n : ℤ) - 13 * (n : ℤ) ^ 2 + (n : ℤ) ^ 3) * a (n - 6) = 0 := by
  sorry

end OMA.S_oeis_a121750
