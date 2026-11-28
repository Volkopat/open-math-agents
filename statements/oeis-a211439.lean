import Mathlib

/-!
# A211439: Barker's g.f. and recurrence for the triples with w + 3x + 3y = 0

Source: https://oeis.org/A211439
Credit: @ivillar

A211439 (offset 0): a(n) is the number of ordered triples (w,x,y) with all terms in
{-n,...,0,...,n} and w + 3x + 3y = 0; data 1, 3, 5, 19, 25, 31, 59, ...
Conjectures (Colin Barker, May 15 2017):
G.f.: (1 + 2*x + 2*x^2 + 12*x^3 + 2*x^4 + 2*x^5 + x^6) / ((1 - x)^3*(1 + x + x^2)^2);
a(n) = a(n-1) + 2*a(n-3) - 2*a(n-4) - a(n-6) + a(n-7) for n > 6.

Formalization notes.
* a(n) is the cardinality of the set of integer triples in [-n, n]^3 with w + 3x + 3y = 0.
* The g.f. identity is stated over ℤ⟦X⟧, cross-multiplied by the denominator
  (1-x)^3*(1+x+x^2)^2, whose constant coefficient is 1. The recurrence is stated in ℤ for n > 6.
-/

namespace OMA.S_oeis_a211439

open PowerSeries

/-- A211439: the number of (w,x,y) in [-n,n]^3 with w + 3x + 3y = 0. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun t : ℤ × ℤ × ℤ => t.1 + 3 * t.2.1 + 3 * t.2.2 = 0)).card

/-- Barker's conjectures: the g.f. (cross-multiplied) and the recurrence for n > 6. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) *
        ((1 - X) ^ 3 * (1 + X + X ^ 2) ^ 2 : PowerSeries ℤ) =
      1 + 2 * X + 2 * X ^ 2 + 12 * X ^ 3 + 2 * X ^ 4 + 2 * X ^ 5 + X ^ 6 ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = a (n - 1) + 2 * a (n - 3) - 2 * a (n - 4) - a (n - 6) +
      a (n - 7)) := by
  sorry

end OMA.S_oeis_a211439
