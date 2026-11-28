import Mathlib

/-!
# A211434: Number of ordered triples (w,x,y) with all terms in {-n,...,0,...,n} and w+2x+5y=0.

Source: https://oeis.org/A211434
Credit: @rickmanelius

Conjectures from Colin Barker, May 15 2017:
G.f.: (1 - x + 4*x^2 + 4*x^4 - x^5 + x^6) / ((1 - x)^3*(1 + x + x^2 + x^3 + x^4)).
a(n) = 2*a(n-1) - a(n-2) + a(n-5) - 2*a(n-6) + a(n-7) for n>6.
(Pontus von Brömssen, Jan 17 2020, in a comment of the entry: this proves the conjecture.)

Formalization notes:
* Offset 0. `a n` is the number of ordered triples (w, x, y) of integers, each in
  `Finset.Icc (-n) n` (the set {-n, ..., 0, ..., n}), with w + 2x + 5y = 0: the cardinality of
  a filtered triple product. The data begin 1, 1, 5, 9, 17, 25, 33, 45, 57, ..., matching the
  entry (all 49 terms of the data were checked by brute force).
* `a n` is a natural number. The statement casts it to ℤ, since the recurrence and the g.f.
  have negative coefficients. The definition is marked noncomputable only because, under
  `import Mathlib`, `Finset.Icc` on ℤ picks up its order through a noncomputable instance; the
  value is still the plain cardinality of a finite set.
* The recurrence is stated for every n > 6, as in the entry. Then n - 7 ≥ 0, so the
  natural-number subtractions n - 1, ..., n - 7 are exact.
* The g.f. is the series Sum_{n ≥ 0} a(n) x^n (offset 0), written as `PowerSeries.mk` of
  n ↦ a(n). The identity is stated over ℤ⟦X⟧ with the denominator cleared. The denominator
  (1 - x)^3 (1 + x + x^2 + x^3 + x^4) has constant coefficient 1, a unit, so this is
  equivalent to the quotient form of the entry.
-/

namespace OMA.S_oeis_a211434

open PowerSeries

/-- A211434: the number of ordered triples (w, x, y) with all terms in {-n, ..., 0, ..., n}
and w + 2x + 5y = 0. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun t : ℤ × ℤ × ℤ => t.1 + 2 * t.2.1 + 5 * t.2.2 = 0)).card

/-- Barker's conjectures on A211434: the g.f.
(1 - x + 4x^2 + 4x^4 - x^5 + x^6)/((1 - x)^3 (1 + x + x^2 + x^3 + x^4)) of a(0), a(1), ...,
with the denominator cleared, and the linear recurrence of order 7 for n > 6. -/
theorem main :
    PowerSeries.mk (fun n => (a n : ℤ)) *
        ((1 - X) ^ 3 * (1 + X + X ^ 2 + X ^ 3 + X ^ 4) : PowerSeries ℤ) =
      1 - X + 4 * X ^ 2 + 4 * X ^ 4 - X ^ 5 + X ^ 6 ∧
    ∀ n : ℕ, 6 < n →
      (a n : ℤ) = 2 * a (n - 1) - a (n - 2) + a (n - 5) - 2 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a211434
