import Mathlib

/-!
# A211435: Barker's g.f. and recurrence for the triples with w + 4x + 5y = 0

Source: https://oeis.org/A211435
Credit: @ivillar

A211435 (offset 0): a(n) is the number of ordered triples (w,x,y) with all terms in
{-n,...,0,...,n} and w + 4x + 5y = 0; data 1, 3, 5, 11, 17, 25, 35, 45, 59, ...
Conjectures (Colin Barker, May 15 2017):
G.f.: (1 + x + 4*x^3 + x^5 + x^6) / ((1 - x)^3*(1 + x + x^2 + x^3 + x^4));
a(n) = 2*a(n-1) - a(n-2) + a(n-5) - 2*a(n-6) + a(n-7) for n > 6.
(The separate asymptotic conjecture a(n) ~ 4*n^2/5 is not part of this statement.)

Formalization notes.
* a(n) is the cardinality of the set of integer triples in [-n, n]^3 with w + 4x + 5y = 0.
* The g.f. identity is stated over ℤ⟦X⟧, cross-multiplied by the denominator
  (1-x)^3*(1+x+x^2+x^3+x^4), whose constant coefficient is 1. The recurrence is stated in ℤ for
  n > 6.
-/

namespace OMA.S_oeis_a211435

open PowerSeries

/-- A211435: the number of (w,x,y) in [-n,n]^3 with w + 4x + 5y = 0. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun t : ℤ × ℤ × ℤ => t.1 + 4 * t.2.1 + 5 * t.2.2 = 0)).card

/-- Barker's conjectures: the g.f. (cross-multiplied) and the recurrence for n > 6. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) *
        ((1 - X) ^ 3 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) : PowerSeries ℤ) =
      1 + X + 4 * X ^ 3 + X ^ 5 + X ^ 6 ∧
    (∀ n : ℕ, 6 < n → (a n : ℤ) = 2 * a (n - 1) - a (n - 2) + a (n - 5) - 2 * a (n - 6) +
      a (n - 7)) := by
  sorry

end OMA.S_oeis_a211435
