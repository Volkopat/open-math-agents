import Mathlib

/-!
# A267184: row 4 of the square array A267181

Source: https://oeis.org/A267184 (conjectures by Colin Barker, Jan 29 2016, and Stefano Spezia, Nov 29 2024)

Entry (offset 0): Row 4 of the square array in A267181. A267181 is the array T(i,j)
(i >= 0, j >= 0) giving the number of steps to reach either the top row or the main diagonal
using the steps (i,j) -> (j,i) (when i > j) or (i,j) -> (i,j-i) (when j > i). Its formula section
gives the recurrence used here: T(0,k) = T(k,k) = 0; if i > j then T(i,j) = T(j,i)+1;
if j > i then T(i,j) = T(i,j-i)+1. Row 4 is a(n) = T(4,n).
Formula section, Conjectures from Colin Barker, Jan 29 2016:
a(n) = a(n-1)+a(n-4)-a(n-5) for n>5.
G.f.: (1+3*x-2*x^2+3*x^3-6*x^4+2*x^5) / ((1-x)^2*(1+x)*(1+x^2)).
Conjectured e.g.f. (Stefano Spezia, Nov 29 2024):
(8 - 5*cos(x) + (1 + x)*cosh(x) - sin(x) + (16 + x)*sinh(x))/4.

Formalization notes:
* `T` is defined by the recurrence above (well-founded recursion; the measure
  `2*(i+j) + [j < i]` decreases at every step).
* The recurrence is stated in the integers. Since the denominator of the generating function
  has constant term 1, the identity A(x) = N/D for A(x) = Sum_(n >= 0) a(n) x^n is stated as
  A * D = N in the formal power series ring over the integers.
* The e.g.f. identity is stated in `ℚ⟦X⟧`, multiplied by 4: `Sum_(n >= 0) a(n) x^n / n!` times 4
  equals the right-hand side, where `cos` and `sin` are Mathlib `PowerSeries.cos` and
  `PowerSeries.sin`, and `cosh`, `sinh` are their hyperbolic analogues, the series
  `Sum_(n even) x^n/n!` and `Sum_(n odd) x^n/n!`.
* Controls from the entry: a(0..9) = 1, 4, 2, 5, 0, 5, 3, 6, 1, 6.
-/

namespace OMA.S_oeis_a267184

open PowerSeries

/-- The array A267181: steps to reach the top row (i = 0) or the main diagonal (i = j). -/
def T (i j : ℕ) : ℕ :=
  if h0 : i = 0 ∨ i = j then 0 else if h1 : j < i then T j i + 1 else T i (j - i) + 1
termination_by 2 * (i + j) + (if j < i then 1 else 0)
decreasing_by
  all_goals (split_ifs <;> omega)

/-- A267184(n) = T(4, n). -/
def a (n : ℕ) : ℕ := T 4 n

/-- The power series of `cosh x`. -/
noncomputable def cosh : PowerSeries ℚ := mk fun n => if Even n then 1 / (n.factorial : ℚ) else 0

/-- The power series of `sinh x`. -/
noncomputable def sinh : PowerSeries ℚ := mk fun n => if Even n then 0 else 1 / (n.factorial : ℚ)

/-- Barker's recurrence and generating function, and Spezia's exponential generating function. -/
theorem main :
    (∀ n : ℕ, 5 < n → (a n : ℤ) = a (n - 1) + a (n - 4) - a (n - 5)) ∧
    mk (fun n => (a n : ℤ)) * ((1 - X) ^ 2 * (1 + X) * (1 + X ^ 2)) =
      (1 + 3 * X - 2 * X ^ 2 + 3 * X ^ 3 - 6 * X ^ 4 + 2 * X ^ 5 : PowerSeries ℤ) ∧
    4 * mk (fun n => (a n : ℚ) / (n.factorial : ℚ)) =
      8 - 5 * cos ℚ + (1 + X) * cosh - sin ℚ + (16 + X) * sinh := by
  sorry

end OMA.S_oeis_a267184
