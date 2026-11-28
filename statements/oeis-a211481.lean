import Mathlib

/-!
# A211481: Barker's recurrence and g.f. for the triples with w + 2x + 3y = n

Source: https://oeis.org/A211481
Credit: @ivillar

Status: open conjecture in the OEIS entry (Colin Barker's conjectured recurrence and empirical
g.f., Nov 08 2014); both are stated here.

A211481 (offset 0): a(n) is the number of ordered triples (w,x,y) with all terms in
{-n,...,0,...,n} and w + 2x + 3y = n; data 1, 3, 8, 16, 26, 38, 54, 71, 91, 114, ...
Conjecture (Colin Barker, Nov 08 2014): a(n) = a(n-1)+a(n-2)-a(n-4)-a(n-5)+a(n-6) for n > 5.
Empirical g.f. (Colin Barker): -(3*x^4+5*x^3+4*x^2+2*x+1) / ((x-1)^3*(x+1)*(x^2+x+1)).

Formalization notes.
* a(n) is the cardinality of the set of integer triples in [-n, n]^3 with w + 2x + 3y = n.
* The g.f. identity is stated over ℤ⟦X⟧, cross-multiplied by the denominator
  (x-1)^3*(x+1)*(x^2+x+1); the recurrence is stated in ℤ for n > 5.
-/

namespace OMA.S_oeis_a211481

open PowerSeries

/-- A211481: the number of (w,x,y) in [-n,n]^3 with w + 2x + 3y = n. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun t : ℤ × ℤ × ℤ => t.1 + 2 * t.2.1 + 3 * t.2.2 = n)).card

/-- Barker's conjectures: the empirical g.f. (cross-multiplied) and the recurrence for n > 5. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) *
        ((X - 1) ^ 3 * (X + 1) * (X ^ 2 + X + 1) : PowerSeries ℤ) =
      -(3 * X ^ 4 + 5 * X ^ 3 + 4 * X ^ 2 + 2 * X + 1) ∧
    (∀ n : ℕ, 5 < n → (a n : ℤ) = a (n - 1) + a (n - 2) - a (n - 4) - a (n - 5) +
      a (n - 6)) := by
  sorry

end OMA.S_oeis_a211481
