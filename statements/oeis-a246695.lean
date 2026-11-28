import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Row sums of the triangular array A246694 (OEIS A246695)

Source: https://oeis.org/A246695 and https://oeis.org/A246694
(OEIS Foundation, CC BY-SA 4.0).
Formalization: @thomasfredrickson.

A246694 is the triangle T(n,k), 0 <= k <= n, defined in its name by
T(0,0) = 1, T(1,0) = 1, T(1,1) = 2, and for n > 1:
T(n,k) = T(n,k-2) + 1 for 2 <= k <= n;
if n is odd, T(n,0) = T(n-1,n-2) + 1 and T(n,1) = T(n-1,n-1) + 1;
if n is even, T(n,0) = T(n-1,n-1) + 1 and T(n,1) = T(n-1,n-2) + 1.
A246695 is a(n) = Sum_{k=0..n} T(n,k), with offset 0: 1, 3, 9, 18, 35, 57, 91, ...

The formula section of A246695 lists three conjectures, stated together here:

* the linear recurrence
  a(n) = 2*a(n-1) + a(n-2) - 4*a(n-3) + a(n-4) + 2*a(n-5) - a(n-6)
  with a(0), ..., a(6) = 1, 3, 9, 18, 35, 57, 91 (stated for every n >= 6;
  at n = 6 it is consistent with the seven listed values);
* the generating function (1 + x + 2*x^2 + x^3 + x^4)/((x - 1)^4*(x + 1)^2),
  stated as an identity of formal power series over the integers with the
  denominator cleared;
* a(n) = (1/8)*(n + 1)*((-1)^n + 2*n^2 + 4*n + 7), stated with the division
  by 8 cleared.

`T` below also returns values for k > n; they are never used by `a`.
-/

namespace OMA.S_oeis_a246695

/-- The triangle A246694. Only the entries with `k ≤ n` are meaningful. -/
def T : ℕ → ℕ → ℤ
  | 0, _ => 1
  | 1, 0 => 1
  | 1, _ + 1 => 2
  | n + 2, 0 => if n % 2 = 1 then T (n + 1) n + 1 else T (n + 1) (n + 1) + 1
  | n + 2, 1 => if n % 2 = 1 then T (n + 1) (n + 1) + 1 else T (n + 1) n + 1
  | n + 2, k + 2 => T (n + 2) k + 1
termination_by n k => (n, k)

/-- A246695: the row sums of the triangle. -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (n + 1), T n k

theorem main :
    (a 0 = 1 ∧ a 1 = 3 ∧ a 2 = 9 ∧ a 3 = 18 ∧ a 4 = 35 ∧ a 5 = 57 ∧ a 6 = 91 ∧
      ∀ n : ℕ, 6 ≤ n →
        a n = 2 * a (n - 1) + a (n - 2) - 4 * a (n - 3) + a (n - 4)
          + 2 * a (n - 5) - a (n - 6)) ∧
    (PowerSeries.mk a * ((PowerSeries.X - 1) ^ 4 * (PowerSeries.X + 1) ^ 2) =
      (1 + PowerSeries.X + 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ 3
        + PowerSeries.X ^ 4 : PowerSeries ℤ)) ∧
    (∀ n : ℕ, 8 * a n = ((n : ℤ) + 1) * ((-1) ^ n + 2 * (n : ℤ) ^ 2 + 4 * n + 7)) := by
  sorry

end OMA.S_oeis_a246695
