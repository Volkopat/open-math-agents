import Mathlib

/-!
# A004138: Plouffe's conjectured generating function

Source: https://oeis.org/A004138
Credit: @ivillar

Status: known result. The entry records the g.f. as conjectured (correctly) by Simon Plouffe in his
1992 dissertation; it follows from the recurrence recorded in the entry, which is used as the
definition here.

A004138 (offset 1): from a counter moving problem;
data 1, 2, 3, 8, 13, 24, 37, 66, 107, 186, 303, 516, 849, 1436, 2377, 3998, 6639, 11134, ...

Conjecture (Simon Plouffe, 1992): G.f. = -(-1+z^2-4*z^3+2*z^4)/((z-1)*(2*z^4-z^3+z^2+z-1)).

Formalization: the entry records a(n) = a(n-1) + a(n-2) - a(n-3) + 2*a(n-4) + 2 for n ≥ 5 [Rawlins];
with the first terms a(1) = 1, a(2) = 2, a(3) = 3, a(4) = 8 this recurrence is the definition of a(n)
used here (with values in ℤ; the value a(0) = 0 is a placeholder and is not used). The stated g.f.
has constant term 1 = a(1), so it is the series Sum_{k>=0} a(k+1) z^k, and the conjecture is stated
as the identity
(Sum_k a(k+1) z^k) * (z-1)*(2*z^4-z^3+z^2+z-1) = -(-1+z^2-4*z^3+2*z^4)
of formal power series over ℚ.
-/

namespace OMA.S_oeis_a004138

open PowerSeries

/-- a(1) = 1, a(2) = 2, a(3) = 3, a(4) = 8, a(n) = a(n-1) + a(n-2) - a(n-3) + 2 a(n-4) + 2 for n ≥ 5
(a(0) = 0 is a placeholder). -/
def a : ℕ → ℤ
  | 0 => 0
  | 1 => 1
  | 2 => 2
  | 3 => 3
  | 4 => 8
  | (n + 5) => a (n + 4) + a (n + 3) - a (n + 2) + 2 * a (n + 1) + 2

/-- Plouffe's generating function for A004138. -/
theorem main : PowerSeries.mk (fun k => (a (k + 1) : ℚ)) *
    ((X - 1) * (2 * X ^ 4 - X ^ 3 + X ^ 2 + X - 1)) = -(-1 + X ^ 2 - 4 * X ^ 3 + 2 * X ^ 4) := by
  sorry

end OMA.S_oeis_a004138
