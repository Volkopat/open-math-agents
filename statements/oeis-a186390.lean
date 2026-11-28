import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# A186390: adjusted joint rank sequence of f(i) = 6i and g(j) = j(j+1)/2

Source: https://oeis.org/A186390
Credit: @SPatel2133

Conjectures of Chai Wah Wu, 12 May 2026:
a(n) = 2*a(n-1) - 2*a(n-2) + 3*a(n-3) - 3*a(n-4) + 2*a(n-5) - 2*a(n-6) + a(n-7) for n > 7, and
G.f.: x*(x^6 - x^2 - 1)/((x - 1)^3*(x^2 + 1)*(x^2 + x + 1)).

Jointly rank the numbers f(i) = 6i (i ≥ 1) and g(j) = j(j+1)/2 (j ≥ 1), with f(i) placed
after g(j) when f(i) = g(j). Then a(n) is the rank of g(n): it is n plus the number of i ≥ 1
with f(i) < g(n). The sequence has offset one; this definition gives a(0) = 0, the constant
coefficient of the conjectured generating function. The generating function is stated with
its denominator cleared.
-/

namespace OMA.S_oeis_a186390

open PowerSeries

def f (i : ℕ) : ℕ := 6 * i

def g (j : ℕ) : ℕ := j * (j + 1) / 2

def a (n : ℕ) : ℤ := n + ((Finset.Icc 1 (g n)).filter fun i => f i < g n).card

theorem main :
    (∀ n : ℕ, 7 < n →
      a n = 2 * a (n - 1) - 2 * a (n - 2) + 3 * a (n - 3) - 3 * a (n - 4) + 2 * a (n - 5) -
        2 * a (n - 6) + a (n - 7)) ∧
    ((X - 1) ^ 3 * (X ^ 2 + 1) * (X ^ 2 + X + 1) * PowerSeries.mk a =
      (X * (X ^ 6 - X ^ 2 - 1) : PowerSeries ℤ)) := by
  sorry

end OMA.S_oeis_a186390
