import Mathlib

/-!
# A267186: column 3 of the square array A267181

Source: https://oeis.org/A267186 (conjectures by Colin Barker, Jan 30 2016)

Entry (offset 0): Column 3 of the square array in A267181. A267181 is the array T(i,j)
(i >= 0, j >= 0) giving the number of steps to reach either the top row or the main diagonal
using the steps (i,j) -> (j,i) (when i > j) or (i,j) -> (i,j-i) (when j > i). Its formula section
gives the recurrence used here: T(0,k) = T(k,k) = 0; if i > j then T(i,j) = T(j,i)+1;
if j > i then T(i,j) = T(i,j-i)+1. Column 3 is a(n) = T(n,3).
Formula section, Conjectures from Colin Barker, Jan 30 2016:
a(n) = a(n-1)+a(n-3)-a(n-4) for n>4.
G.f.: x*(2+x-3*x^2+3*x^3-x^5-x^6) / ((1-x)^2*(1+x+x^2)).

Formalization notes:
* `T` is defined by the recurrence above (well-founded recursion; the measure
  `2*(i+j) + [j < i]` decreases at every step).
* The recurrence is stated in the integers. Since the denominator of the generating function
  has constant term 1, the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as
  A * D = N in the formal power series ring over the integers.
* The recurrence is stated with the range n > 4 given in the entry.
* Controls from the entry: a(0..8) = 0, 2, 3, 0, 5, 6, 2, 6, 7.
-/

namespace OMA.S_oeis_a267186

open PowerSeries

/-- The array A267181: steps to reach the top row (i = 0) or the main diagonal (i = j). -/
def T (i j : ℕ) : ℕ :=
  if h0 : i = 0 ∨ i = j then 0 else if h1 : j < i then T j i + 1 else T i (j - i) + 1
termination_by 2 * (i + j) + (if j < i then 1 else 0)
decreasing_by
  all_goals (split_ifs <;> omega)

/-- A267186(n) = T(n, 3). -/
def a (n : ℕ) : ℕ := T n 3

/-- Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 4 < n → (a n : ℤ) = a (n - 1) + a (n - 3) - a (n - 4)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X + X ^ 2)) =
      (X * (2 + X - 3 * X ^ 2 + 3 * X ^ 3 - X ^ 5 - X ^ 6) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a267186
