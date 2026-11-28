import Mathlib

/-!
# A006172: a(n) = 1 + F(2*n+1) + (-1)^n*L(n).

Source: https://oeis.org/A006172
Credit: @agchua

In the comment section of A006172:
  The g.f. -(-2 -3*x + 19*x^2 - 17*x^3 + 4*x^4)/((x-1)*(x^2 - x - 1)*(x^2 - 3*x + 1)) conjectured
  by Simon Plouffe in his 1992 dissertation is probably wrong. [The correct g.f. is
  (4 - 10*x - x^2 + 9*x^3 - 3*x^4)/((x - 1)*(x^2 - x - 1)*(x^2 - 3*x + 1)). From Bruno Berselli,
  Mar 09 2015]
This file states both parts, as identities of formal power series over ℚ with the common
denominator D = (X - 1)(X^2 - X - 1)(X^2 - 3X + 1), whose constant term is 1: Plouffe's g.f. is not
the g.f. of the sequence, (∑ a(n) X^n) * D ≠ -(-2 - 3X + 19X^2 - 17X^3 + 4X^4), and Berselli's is,
(∑ a(n) X^n) * D = 4 - 10X - X^2 + 9X^3 - 3X^4.
The sequence has offset 0. F = Nat.fib is the Fibonacci sequence (F(0) = 0, F(1) = 1) and L is the
Lucas sequence A000032 (L(0) = 2, L(1) = 1, L(n+2) = L(n+1) + L(n)), as in the name of the entry;
the values are 4, 2, 9, 10, 42, 79, ... as listed.
-/

namespace OMA.S_oeis_a006172

/-- The Lucas numbers L(0) = 2, L(1) = 1, L(n+2) = L(n+1) + L(n) (A000032). -/
def L : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | (n + 2) => L (n + 1) + L n

/-- A006172(n) = 1 + F(2n+1) + (-1)^n L(n). -/
def a (n : ℕ) : ℤ := 1 + (Nat.fib (2 * n + 1) : ℤ) + (-1) ^ n * L n

/-- Plouffe's g.f. is not the g.f. of A006172, and Berselli's g.f.
(4 - 10x - x^2 + 9x^3 - 3x^4)/((x - 1)(x^2 - x - 1)(x^2 - 3x + 1)) is. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℚ)) * ((PowerSeries.X - 1) *
        (PowerSeries.X ^ 2 - PowerSeries.X - 1) * (PowerSeries.X ^ 2 - 3 * PowerSeries.X + 1)) ≠
      -(-2 - 3 * PowerSeries.X + 19 * PowerSeries.X ^ 2 - 17 * PowerSeries.X ^ 3 +
        4 * PowerSeries.X ^ 4) ∧
    PowerSeries.mk (fun n => (a n : ℚ)) * ((PowerSeries.X - 1) *
        (PowerSeries.X ^ 2 - PowerSeries.X - 1) * (PowerSeries.X ^ 2 - 3 * PowerSeries.X + 1)) =
      4 - 10 * PowerSeries.X - PowerSeries.X ^ 2 + 9 * PowerSeries.X ^ 3 -
        3 * PowerSeries.X ^ 4 := by
  sorry

end OMA.S_oeis_a006172
