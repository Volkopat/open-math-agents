import Mathlib

/-!
# A005522: Plouffe's generating function

Source: https://oeis.org/A005522
Credit: @ivillar

Status: known result. The entry records the g.f. conjectured by Simon Plouffe in his 1992
dissertation, and Comment VI of Russell Jay Hendel (Mar 02 2015) settles it: the g.f. A(x) of a(n)
is 1/(1-x) + (1-2x)/(1-3x+x^2) + (2-x)/(1-x-x^2), and Plouffe's P(x) equals (A(x) - 4)/x.

A005522 (offset 0): a(n) = 1 + L(n) + F(2*n-1) with L(n) the Lucas numbers (A000032) and F(2*n-1)
the bisected Fibonacci numbers (A001519);
data 4, 3, 6, 10, 21, 46, 108, 263, 658, 1674, 4305, 11146, 28980, 75547, 197262, 515594, ...

Conjectured g.f. (Simon Plouffe, as recorded in the Maple section of the entry):
-(-3+9*z-z**2-10*z**3+4*z**4)/(z-1)/(z**2-3*z+1)/(z**2+z-1).
Its expansion starts 3 + 6z + 10z^2 + 21z^3 + ..., so it is the g.f. of a(n+1), n ≥ 0 (the entry:
P(x) = (A(x) - 4)/x).

Formalization: L is defined by L(0) = 2, L(1) = 1, L(n) = L(n-1) + L(n-2), and
a(n) = 1 + L(n) + F(2n-1) for n ≥ 1 with a(0) = 4 (the name formula with F(-1) = 1). The statement
is the identity of formal power series over ℚ with the denominator cleared:
(Sum_{n ≥ 0} a(n+1) z^n) * (z-1) * (z^2-3z+1) * (z^2+z-1) = -(-3 + 9z - z^2 - 10z^3 + 4z^4).
-/

namespace OMA.S_oeis_a005522

open PowerSeries

/-- The Lucas numbers A000032. -/
def lucas : ℕ → ℤ
  | 0 => 2
  | 1 => 1
  | (n + 2) => lucas (n + 1) + lucas n

/-- a(0) = 4 and a(n) = 1 + L(n) + F(2n-1) for n ≥ 1. -/
def a (n : ℕ) : ℤ :=
  if n = 0 then 4 else 1 + lucas n + (Nat.fib (2 * n - 1) : ℤ)

/-- Plouffe's g.f. for A005522 (the g.f. of a(n+1)), with the denominator cleared. -/
theorem main :
    PowerSeries.mk (fun n => (a (n + 1) : ℚ)) * ((X - 1) * (X ^ 2 - 3 * X + 1) * (X ^ 2 + X - 1)) =
      -(-3 + 9 * X - X ^ 2 - 10 * X ^ 3 + 4 * X ^ 4) := by
  sorry

end OMA.S_oeis_a005522
