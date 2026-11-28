import Mathlib

/-!
# A121584: Mathar's recurrence

Source: https://oeis.org/A121584
Credit: @ivillar

Status: recorded in the entry as a conjecture; no proof or verification is noted there. It follows
from the recurrence with factorials recorded in the entry, which is used as the definition here.

A121584 (offset 1): number of cells in columns 1 and 2 of all deco polyominoes of height n;
data 1, 4, 18, 93, 569, 4074, 33336, 306035, 3111771, 34708944, 421407314, 5533007841, ...

Conjecture (R. J. Mathar, Jul 26 2022): D-finite with recurrence
14*(-n+1)*a(n) +(14*n^2+1731*n-6995)*a(n-1) +3*(-577*n^2+480*n+7243)*a(n-2)
+2*(2781*n^2-11952*n+6004)*a(n-3) +(-5987*n^2+36181*n-54220)*a(n-4) +2*(1071*n-3433)*(n-4)*a(n-5)
= 0.

Formalization: the entry records
a(1)=1, a(2)=4, a(n) = [(2n-3)*a(n-1) - (n-1)*a(n-2)]/(n-2) + (1/2)*(2n^3-9n^2+17n-16)*(n-1)!/(n-2) for n ≥ 3,
and this recurrence, read in ℚ, is the definition of a(n) used here (the value a(0) = 0 is a
placeholder and is not used). The sequence has offset 1 and the recurrence involves a(n-5), so it
is stated for n ≥ 6; on the data the left side vanishes at n = 6, 7, 8.
-/

namespace OMA.S_oeis_a121584

/-- a(1)=1, a(2)=4, a(n) = ((2n-3) a(n-1) - (n-1) a(n-2))/(n-2) + (1/2)(2n^3-9n^2+17n-16)(n-1)!/(n-2) for n ≥ 3
(a(0) = 0 is a placeholder). -/
def a : ℕ → ℚ
  | 0 => 0
  | 1 => 1
  | 2 => 4
  | (n + 3) => ((2 * ((n : ℚ) + 3) - 3) * a (n + 2) - ((n : ℚ) + 3 - 1) * a (n + 1)) / ((n : ℚ) + 3 - 2) +
      (1 / 2) * (2 * ((n : ℚ) + 3) ^ 3 - 9 * ((n : ℚ) + 3) ^ 2 + 17 * ((n : ℚ) + 3) - 16) * ((n + 2).factorial : ℚ) /
        ((n : ℚ) + 3 - 2)

/-- Mathar's conjectured recurrence for A121584, for n ≥ 6. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (14 - 14 * (n : ℚ)) * a n + (-6995 + 1731 * (n : ℚ) + 14 * (n : ℚ) ^ 2) * a (n - 1) +
      (21729 + 1440 * (n : ℚ) - 1731 * (n : ℚ) ^ 2) * a (n - 2) + (12008 - 23904 * (n : ℚ) + 5562 * (n : ℚ) ^ 2) * a (n - 3) +
      (-54220 + 36181 * (n : ℚ) - 5987 * (n : ℚ) ^ 2) * a (n - 4) + (27464 - 15434 * (n : ℚ) + 2142 * (n : ℚ) ^ 2) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a121584
