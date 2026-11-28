import Mathlib

/-!
# A210376: number of 2 X 2 matrices with all terms in {0,1,...,n} and (sum of terms) = n + 4

Source: https://oeis.org/A210376 (conjectures by Colin Barker, Dec 07 2017)

Entry (offset 0): Number of 2 X 2 matrices with all terms in {0,1,...,n} and (sum of terms) = n + 4.
Formula section, Conjectures from Colin Barker, Dec 07 2017:
G.f.: x^2*(10 - 15*x^2 + 6*x^4) / (1 - x)^4.
a(n) = (-270 + 107*n + 18*n^2 + n^3) / 6 for n>2.
a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>4.

Formalization notes:
* The matrices are `Matrix (Fin 2) (Fin 2) (Fin (n + 1))`, i.e. entries in {0,...,n}.
* The closed form is stated after multiplying both sides by 6; it and the recurrence are stated
  in the integers, with the ranges given in the entry.
* Since `(1 - x)^4` has constant term 1, the identity A(x) = N/D for
  A(x) = Sum_(n >= 0) a(n) x^n is stated as A * D = N in the formal power series ring over the
  integers.
* Controls from the entry: a(0..) = 0, 0, 10, 40, 85, 140, 206.
-/

namespace OMA.S_oeis_a210376

open PowerSeries

/-- A210376(n): the number of 2 X 2 matrices with entries in {0,...,n} whose entries sum to n + 4. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter fun M : Matrix (Fin 2) (Fin 2) (Fin (n + 1)) =>
    ∑ i, ∑ j, (M i j : ℕ) = n + 4).card

/-- Barker's generating function, closed form and recurrence. -/
theorem main :
    mk (fun n => (a n : ℤ)) * (1 - X) ^ 4 = (X ^ 2 * (10 - 15 * X ^ 2 + 6 * X ^ 4) : PowerSeries ℤ) ∧
    (∀ n : ℕ, 2 < n → 6 * (a n : ℤ) = -270 + 107 * n + 18 * n ^ 2 + n ^ 3) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) := by
  sorry

end OMA.S_oeis_a210376
