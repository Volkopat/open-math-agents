import Mathlib

/-!
# A121754: Mathar's recurrence

Source: https://oeis.org/A121754
Credit: @ivillar

Status: open conjecture (R. J. Mathar, Jul 26 2022); the entry records it as a conjecture and notes no proof or
verification of it. It follows from the recurrence with factorials recorded in the entry, which is used as
the definition here.

A121754 (offset 1): number of columns ending at an even level in all deco polyominoes of height n;
data 0, 1, 6, 31, 211, 1530, 13086, 120888, 1260792, 14140080, 174692880, 2304970560, ...

Conjecture (R. J. Mathar, Jul 26 2022): D-finite with recurrence
16*(n+1)*a(n) +(-16*n^2-178*n+531)*a(n-1) +(-16*n^3+178*n^2-393*n-510)*a(n-2)
+(16*n^4+98*n^3-1439*n^2+4222*n-3623)*a(n-3) +(-146*n^4+1479*n^3-4483*n^2+3054*n+2841)*a(n-4)
+(130*n-311)*(n-6)*(-4+n)^2*a(n-5) = 0.

Formalization: the entry records the recurrence relation
a(1)=0, a(2)=1, a(n) = (2n-3)*a(n-1) - (n-1)*(n-3)*a(n-2) + (n-2)!*[n-2 + (1/2)*(1+(-1)^(n-1))*(n-1)] for n ≥ 3,
and this recurrence, read in ℚ, is the definition of a(n) used here (the value a(0) = 0 is a
placeholder and is not used). The sequence has offset 1 and the recurrence involves a(n-5), so it
is stated for n ≥ 6, where every index is at least the offset; it is checked by the data, for example at
n = 6: (112)*(1530) + (-1113)*(211) + (84)*(31) + (11809)*(6) + (-9975)*(1) + (0)*(0) = 0.
-/

namespace OMA.S_oeis_a121754

/-- a(1)=0, a(2)=1, a(n) = (2n-3) a(n-1) - (n-1)(n-3) a(n-2) + (n-2)! (n-2 + (1/2)(1+(-1)^(n-1))(n-1)) for n ≥ 3
(a(0) = 0 is a placeholder). -/
def a : ℕ → ℚ
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | (n + 3) => (2 * ((n : ℚ) + 3) - 3) * a (n + 2) - ((n : ℚ) + 3 - 1) * ((n : ℚ) + 3 - 3) * a (n + 1) +
      ((n + 1).factorial : ℚ) * ((n : ℚ) + 3 - 2 + (1 / 2) * (1 + (-1 : ℚ) ^ (n + 2)) * ((n : ℚ) + 3 - 1))

/-- Mathar's conjectured recurrence for A121754, for n ≥ 6. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    (16 + 16 * (n : ℚ)) * a n + (531 - 178 * (n : ℚ) - 16 * (n : ℚ) ^ 2) * a (n - 1) +
      (-510 - 393 * (n : ℚ) + 178 * (n : ℚ) ^ 2 - 16 * (n : ℚ) ^ 3) * a (n - 2) + (-3623 + 4222 * (n : ℚ) - 1439 * (n : ℚ) ^ 2 + 98 * (n : ℚ) ^ 3 + 16 * (n : ℚ) ^ 4) * a (n - 3) +
      (2841 + 3054 * (n : ℚ) - 4483 * (n : ℚ) ^ 2 + 1479 * (n : ℚ) ^ 3 - 146 * (n : ℚ) ^ 4) * a (n - 4) + (29856 - 32384 * (n : ℚ) + 12674 * (n : ℚ) ^ 2 - 2131 * (n : ℚ) ^ 3 + 130 * (n : ℚ) ^ 4) * a (n - 5) = 0 := by
  sorry

end OMA.S_oeis_a121754
