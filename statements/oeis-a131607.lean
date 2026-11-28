import Mathlib

/-!
# A131607: Barker's g.f. and recurrence for the Pell companion numbers without last digit

Source: https://oeis.org/A131607
Credit: @ivillar

A131607 (offset 4): the Pell companion numbers A001333 without their last digit, that is
a(n) = floor(A001333(n)/10) (Andrew Howroyd); data 1, 4, 9, 23, 57, 139, 336, 811, 1960, ...
Conjectures (Colin Barker, Jan 03 2020):
G.f.: x^4*(1 + x - 2*x^2 + x^3 + x^4) / ((1 - x)*(1 + x^2)*(1 - 2*x - x^2)*(1 - x^2 + x^4));
a(n) = 3*a(n-1) - a(n-2) - a(n-3) - a(n-6) + 3*a(n-7) - a(n-8) - a(n-9) for n > 12.

Formalization notes.
* A001333 is given by A001333(0) = A001333(1) = 1 and A001333(n) = 2*A001333(n-1) + A001333(n-2);
  a(n) = A001333(n) / 10 (natural number division) for every n. The OEIS entry starts at
  offset 4; for n = 0, 1, 2, 3 this formula gives 0 (A001333(n) = 1, 1, 3, 7), matching the
  factor x^4 of the g.f., so the g.f. is stated for the sequence indexed from 0.
* The g.f. identity is stated over ℤ⟦X⟧, cross-multiplied by the denominator, whose constant
  coefficient is 1. The recurrence is stated in ℤ for n > 12.
-/

namespace OMA.S_oeis_a131607

open PowerSeries

/-- A001333: A001333(0) = A001333(1) = 1, A001333(n) = 2*A001333(n-1) + A001333(n-2). -/
def P : ℕ → ℕ
  | 0 => 1
  | 1 => 1
  | n + 2 => 2 * P (n + 1) + P n

/-- A131607: A001333(n) without its last decimal digit. -/
def a (n : ℕ) : ℕ := P n / 10

/-- Barker's conjectures: the g.f. (cross-multiplied) and the recurrence for n > 12. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) *
        ((1 - X) * (1 + X ^ 2) * (1 - 2 * X - X ^ 2) * (1 - X ^ 2 + X ^ 4) : PowerSeries ℤ) =
      X ^ 4 * (1 + X - 2 * X ^ 2 + X ^ 3 + X ^ 4) ∧
    (∀ n : ℕ, 12 < n → (a n : ℤ) = 3 * a (n - 1) - a (n - 2) - a (n - 3) - a (n - 6) +
      3 * a (n - 7) - a (n - 8) - a (n - 9)) := by
  sorry

end OMA.S_oeis_a131607
