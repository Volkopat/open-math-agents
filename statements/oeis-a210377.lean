import Mathlib

/-!
# A210377: number of 2 X 2 matrices with all terms in {0,1,...,n} and (sum of terms) = n + 5

Source: https://oeis.org/A210377 (conjectures by Colin Barker, Dec 07 2017)

Entry (offset 0): Number of 2 X 2 matrices with all terms in {0,1,...,n} and (sum of terms) = n + 5.
Formula section, Conjectures from Colin Barker, Dec 07 2017:
G.f.: x^2*(4 + 15*x - 20*x^2 - 4*x^3 + 6*x^5) / (1 - x)^4.
a(n) = (-504 + 146*n + 21*n^2 + n^3) / 6 for n>3.
a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>5.

Formalization notes:
* The matrices are `Matrix (Fin 2) (Fin 2) (Fin (n + 1))`, i.e. entries in {0,...,n}.
* The closed form is stated after multiplying both sides by 6; it and the recurrence are stated
  in the integers, with the ranges given in the entry.
* Since `(1 - x)^4` has constant term 1, the identity A(x) = N/D for
  A(x) = Sum_(n >= 0) a(n) x^n is stated as A * D = N in the formal power series ring over the
  integers.
* Controls from the entry: a(0..) = 0, 0, 4, 31, 80, 146, 224, 315.
-/

namespace OMA.S_oeis_a210377

open PowerSeries

/-- A210377(n): the number of 2 X 2 matrices with entries in {0,...,n} whose entries sum to n + 5. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun M : Matrix (Fin 2) (Fin 2) (Fin (n + 1)) =>
    ∑ i, ∑ j, (M i j : ℕ) = n + 5).card

/-- Barker's generating function, closed form and recurrence. -/
theorem main :
    mk (fun n => (a n : ℤ)) * (1 - X) ^ 4 = (X ^ 2 * (4 + 15 * X - 20 * X ^ 2 - 4 * X ^ 3 + 6 * X ^ 5) : PowerSeries ℤ) ∧
    (∀ n : ℕ, 3 < n → 6 * (a n : ℤ) = -504 + 146 * n + 21 * n ^ 2 + n ^ 3) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) := by
  sorry

end OMA.S_oeis_a210377
