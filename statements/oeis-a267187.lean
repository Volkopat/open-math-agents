import Mathlib

/-!
# A267187: column 4 of the square array A267181

Source: https://oeis.org/A267187 (conjectures by Colin Barker, Jan 29 2016)

Entry (offset 0): Column 4 of the square array in A267181. A267181 is the array T(i,j)
(i >= 0, j >= 0) giving the number of steps to reach either the top row or the main diagonal
using the steps (i,j) -> (j,i) (when i > j) or (i,j) -> (i,j-i) (when j > i). Its formula section
gives the recurrence used here: T(0,k) = T(k,k) = 0; if i > j then T(i,j) = T(j,i)+1;
if j > i then T(i,j) = T(i,j-i)+1. Column 4 is a(n) = T(n,4).
Formula section, Conjectures from Colin Barker, Jan 29 2016:
a(n) = a(n-1)+a(n-4)-a(n-5) for n>5.
G.f.: x*(3-2*x+3*x^2-4*x^3+3*x^4-x^7-x^8) / ((1-x)^2*(1+x)*(1+x^2)).

Formalization notes:
* `T` is defined by the recurrence above (well-founded recursion; the measure
  `2*(i+j) + [j < i]` decreases at every step).
* The recurrence is stated in the integers. Since the denominator of the generating function
  has constant term 1, the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as
  A * D = N in the formal power series ring over the integers.
* The recurrence is stated with the range n > 5 given in the entry.
* Controls from the entry: a(0..9) = 0, 3, 1, 4, 0, 6, 4, 7, 2, 7.
-/

namespace OMA.S_oeis_a267187

open PowerSeries

/-- The array A267181: steps to reach the top row (i = 0) or the main diagonal (i = j). -/
def T (i j : ℕ) : ℕ :=
  if h0 : i = 0 ∨ i = j then 0 else if h1 : j < i then T j i + 1 else T i (j - i) + 1
termination_by 2 * (i + j) + (if j < i then 1 else 0)
decreasing_by
  all_goals (split_ifs <;> omega)

/-- A267187(n) = T(n, 4). -/
def a (n : ℕ) : ℕ := T n 4

/-- Barker's recurrence and generating function. -/
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = a (n - 1) + a (n - 4) - a (n - 5)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2)) =
      (X * (3 - 2 * X + 3 * X ^ 2 - 4 * X ^ 3 + 3 * X ^ 4 - X ^ 7 - X ^ 8) : PowerSeries ℤ) := by
  sorry

end OMA.S_oeis_a267187
