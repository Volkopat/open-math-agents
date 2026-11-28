import Mathlib

/-!
# A296516: Barker's generating function and recurrence

Source: https://oeis.org/A296516
Credit: @ivillar

Status: recorded in the entry as conjectures (Colin Barker, Mar 28 2018). The entry also records the
closed form a(n) = (F(2*n+1) + F(n+2) - n^2 + n - 2) / 2 (Luc Rousseau, Mar 30 2018) and notes that
it is proved in the linked paper on unions and Minkowski sums (Andrei Zabolotskii, Jul 19 2026). Both
conjectures follow from that closed form, which is used as the definition here.

A296516 (offset 0): a(n) is the number of terms in expanded form of bivariate polynomial Q_n, where
(P_n, Q_n) is defined by: P_0 = x, Q_0 = y, P_(n+1) = P_n + Q_n, Q_(n+1) = P_n * Q_n;
data 1, 1, 2, 5, 14, 40, 111, 300, 797, 2098, 5499, 14389, 37634, 98435, 257516, 673827, ...

Conjectures from Colin Barker, Mar 28 2018:
(1) G.f.: 1 + x*(1 - 5*x + 9*x^2 - 5*x^3 - 2*x^4 + x^5) / ((1 - x)^3*(1 - 3*x + x^2)*(1 - x - x^2)).
(2) a(n) = 7*a(n-1) - 18*a(n-2) + 20*a(n-3) - 6*a(n-4) - 6*a(n-5) + 5*a(n-6) - a(n-7) for n > 7.

Formalization: a(0) = 1 and, for n > 0, a(n) = (F(2n+1) + F(n+2) - n^2 + n - 2)/2 with F the
Fibonacci numbers, read in ℚ (the closed form gives 0 at n = 0, and the entry states it for n > 0).
(1) is stated with the denominator cleared, as an identity of formal power series over ℚ:
A(x) * D(x) = D(x) + x * (1 - 5x + 9x^2 - 5x^3 - 2x^4 + x^5) with
D(x) = (1 - x)^3 (1 - 3x + x^2) (1 - x - x^2). (2) is stated for n ≥ 8. `main` is the conjunction.
-/

namespace OMA.S_oeis_a296516

open PowerSeries

/-- a(0) = 1 and a(n) = (F(2n+1) + F(n+2) - n^2 + n - 2)/2 for n > 0, as recorded in the entry. -/
def a (n : ℕ) : ℚ :=
  if n = 0 then 1
  else ((Nat.fib (2 * n + 1) : ℚ) + (Nat.fib (n + 2) : ℚ) - (n : ℚ) ^ 2 + (n : ℚ) - 2) / 2

/-- The two conjectures of Colin Barker for A296516. -/
theorem main :
    (PowerSeries.mk a * ((1 - X) ^ 3 * (1 - 3 * X + X ^ 2) * (1 - X - X ^ 2)) =
      (1 - X) ^ 3 * (1 - 3 * X + X ^ 2) * (1 - X - X ^ 2) +
        X * (1 - 5 * X + 9 * X ^ 2 - 5 * X ^ 3 - 2 * X ^ 4 + X ^ 5)) ∧
    (∀ n : ℕ, 8 ≤ n → a n = 7 * a (n - 1) - 18 * a (n - 2) + 20 * a (n - 3) - 6 * a (n - 4) - 6 * a (n - 5) + 5 * a (n - 6) - a (n - 7)) := by
  sorry

end OMA.S_oeis_a296516
