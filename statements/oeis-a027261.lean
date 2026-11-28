import Mathlib

/-!
# A027261: closed form, recurrence and generating function

Source: https://oeis.org/A027261
Credit: @ivillar

A025177 is the triangular array T(n,k), 0 ≤ k ≤ 2n, with rows [1], [1, 0, 1] and
T(n,k) = T(n-1,k-2) + T(n-1,k-1) + T(n-1,k) for n ≥ 2 (first differences of the trinomial array;
rows 1; 1,0,1; 1,1,2,1,1; 1,2,4,4,4,2,1; ...).
A027261 (offset 0) is a(n) = Sum_{k=0..2n} (k+1) * T(n,k); data 1, 4, 18, 72, 270, 972, ...

Conjectures recorded in A027261:
* a(n) = 2*(n+1)*3^(n-1) for n > 1 (Ralf Stephan, Feb 02 2004);
* a(n) = 6*a(n-1) - 9*a(n-2) for n > 3, and the g.f. is (1-2*x+3*x^2)/(1-3*x)^2
  (Colin Barker, Jul 28 2012).

Formalization: entries of T outside 0 ≤ k ≤ 2n are 0, and terms with a negative column index are
dropped from the recurrence. The values a(n) are integers. The generating function is a formal
power series over ℤ and its identity is stated with the denominator cleared.
-/

namespace OMA.S_oeis_a027261

open PowerSeries

/-- The array A025177: rows [1] and [1, 0, 1], then
T(n,k) = T(n-1,k-2) + T(n-1,k-1) + T(n-1,k). -/
def T : ℕ → ℕ → ℤ
  | 0, k => if k = 0 then 1 else 0
  | 1, k => if k = 0 ∨ k = 2 then 1 else 0
  | (n + 2), k =>
    (if 2 ≤ k then T (n + 1) (k - 2) else 0) + (if 1 ≤ k then T (n + 1) (k - 1) else 0) +
      T (n + 1) k

/-- A027261: a(n) = ∑_{k=0}^{2n} (k+1) T(n,k). -/
def a (n : ℕ) : ℤ := ∑ k ∈ Finset.range (2 * n + 1), ((k : ℤ) + 1) * T n k

/-- Stephan's closed form, Barker's recurrence and Barker's generating function. -/
theorem main :
    (∀ n : ℕ, 1 < n → a n = 2 * ((n : ℤ) + 1) * 3 ^ (n - 1)) ∧
    (∀ n : ℕ, 3 < n → a n = 6 * a (n - 1) - 9 * a (n - 2)) ∧
    PowerSeries.mk a * (1 - 3 * X) ^ 2 = 1 - 2 * X + 3 * X ^ 2 := by
  sorry

end OMA.S_oeis_a027261
