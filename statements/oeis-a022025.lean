import Mathlib

/-!
# A022025: Define the sequence S(a(0),a(1)) by a(n+2) is the least integer such that a(n+2)/a(n+1) > a(n+1)/a(n) for n >= 0. This is S(6,102).

Source: https://oeis.org/A022025
Credit: @agchua

The formula section of A022025 says:
  The conjectured g.f. (6-5*x^2)/(1-17*x-x^2+14*x^3) yields the same initial terms a(0..271)
  but from a(272) on a different sequence. - Bruno Berselli and M. F. Hasler, Feb 11 2016
This file states the conjectured g.f. literally, as an identity of formal power series over ℚ:
(∑ a(n) X^n) * (1 - 17X - X^2 + 14X^3) = 6 - 5X^2 (offset 0). The entry's line says that it is false;
the statement is the conjecture itself, so that a disproof can be checked.
Definition: a(0) = 6, a(1) = 102. All terms are positive, and for positive a(n), a(n+1) the condition
k/a(n+1) > a(n+1)/a(n) says k > a(n+1)^2/a(n), whose least integer solution is
floor(a(n+1)^2/a(n)) + 1. This is the formula a(n+1) = floor(a(n)^2/a(n-1))+1 of M. F. Hasler
(Feb 10 2016) in the same entry and the rule of the entry's Maple, Mathematica and PARI programs; it
is used as the definition below, with the quotient taken in ℚ and Int.floor.
-/

namespace OMA.S_oeis_a022025

/-- A022025: a(0) = 6, a(1) = 102, a(n+2) = floor(a(n+1)^2/a(n)) + 1. -/
def a : ℕ → ℤ
  | 0 => 6
  | 1 => 102
  | (n + 2) => ⌊((a (n + 1) : ℚ) ^ 2 / (a n : ℚ))⌋ + 1

/-- The conjectured g.f. (6-5x^2)/(1-17x-x^2+14x^3). -/
theorem main : PowerSeries.mk (fun n => (a n : ℚ)) *
    (1 - 17 * PowerSeries.X - PowerSeries.X ^ 2 + 14 * PowerSeries.X ^ 3) =
      6 - 5 * PowerSeries.X ^ 2 := by
  sorry

end OMA.S_oeis_a022025
