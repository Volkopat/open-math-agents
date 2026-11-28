import Mathlib

/-!
# A211438: Number of ordered triples (w,x,y) with all terms in {-n,...,0,...,n} and w+2x+2y=0.

Source: https://oeis.org/A211438
Credit: @rickmanelius

Conjecture from Colin Barker, Apr 18 2012: a(n) = (5+3*(-1)^n+2*(7+3*(-1)^n)*n+14*n^2)/8.
G.f.: (1+2*x+8*x^2+2*x^3+x^4)/((1-x)^3*(1+x)^2).

Formalization notes:
* Offset 0. `a n` is the number of ordered triples (w, x, y) of integers, each in
  `Finset.Icc (-n) n` (the set {-n, ..., 0, ..., n}), with w + 2x + 2y = 0: the cardinality of
  a filtered triple product. The data begin 1, 3, 13, 19, 39, 49, 79, 93, 133, ..., matching
  the entry (all 46 terms of the data were checked by brute force).
* The closed form is stated in ℚ, so the division by 8 is exact division. It is stated for
  every n ≥ 0, the indices of the sequence (offset 0; at n = 0 the formula gives 1 = a(0)).
* The g.f. is the series Sum_{n ≥ 0} a(n) x^n (offset 0), written as `PowerSeries.mk` of
  n ↦ a(n). The identity is stated over ℤ⟦X⟧ with the denominator cleared. The denominator
  (1 - x)^3 (1 + x)^2 has constant coefficient 1, a unit, so this is equivalent to the quotient
  form of the entry.
* `a n` is a natural number, cast to ℚ and ℤ in the statement. The definition is marked
  noncomputable only because, under `import Mathlib`, `Finset.Icc` on ℤ picks up its order
  through a noncomputable instance; the value is still the plain cardinality of a finite set.
-/

namespace OMA.S_oeis_a211438

open PowerSeries

/-- A211438: the number of ordered triples (w, x, y) with all terms in {-n, ..., 0, ..., n}
and w + 2x + 2y = 0. -/
noncomputable def a (n : ℕ) : ℕ :=
  ((Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n ×ˢ Finset.Icc (-(n : ℤ)) n).filter
    (fun t : ℤ × ℤ × ℤ => t.1 + 2 * t.2.1 + 2 * t.2.2 = 0)).card

/-- Barker's conjectures on A211438: the closed form for every n ≥ 0, and the g.f.
(1 + 2x + 8x^2 + 2x^3 + x^4)/((1 - x)^3 (1 + x)^2) of a(0), a(1), ..., with the denominator
cleared. -/
theorem main :
    (∀ n : ℕ, (a n : ℚ) =
      (5 + 3 * (-1) ^ n + 2 * (7 + 3 * (-1) ^ n) * (n : ℚ) + 14 * (n : ℚ) ^ 2) / 8) ∧
    PowerSeries.mk (fun n => (a n : ℤ)) * ((1 - X) ^ 3 * (1 + X) ^ 2 : PowerSeries ℤ) =
      1 + 2 * X + 8 * X ^ 2 + 2 * X ^ 3 + X ^ 4 := by
  sorry

end OMA.S_oeis_a211438
