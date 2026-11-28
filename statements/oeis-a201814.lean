import Mathlib

/-!
# OEIS A201814: Barker's generating function and recurrence

Source: https://oeis.org/A201814 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 05 2011), offset 1: Number of arrays of 6 integers in -n..n with sum zero
and equal numbers of elements greater than zero and less than zero. Data: 141, 1001, 4621, 15681,
42821, 99961, 207621, 394241, 697501, 1165641, ... The formula section states: Empirical: a(n) =
11*n^5 + 65*n^3 + 64*n + 1. Conjectures from Colin Barker, May 25 2018: (Start) G.f.: x*(141 +
155*x + 730*x^2 + 150*x^3 + 145*x^4 - x^5) / (1 - x)^6. a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) -
15*a(n-4) + 6*a(n-5) - a(n-6) for n>6. (End)

Formalization notes:
* An array is a function x : Fin 6 → ℤ, the array x(0..5). `arrays n` is the set of arrays with
  every entry in -n..n (a `Fintype.piFinset` of `Finset.Icc (-n) n`), zero sum, and as many entries
  greater than zero as entries less than zero (the two `Finset.filter` cardinalities); `a n` is its
  cardinality.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^6 = N(x) in Z[[x]],
  which is equivalent because 1 - x is a unit. The recurrence is stated in the integers, for n > 6
  as in the entry.
* `main` is the conjunction of Barker's two conjectures, in the entry's order.
* Controls proved in the proof file: a(1..26), all the entry's listed terms.
-/

namespace OMA.S_oeis_a201814

open PowerSeries

/-- The arrays x(0..5) of 6 integers in -n..n with sum zero and as many entries greater than
zero as entries less than zero. -/
noncomputable def arrays (n : ℕ) : Finset (Fin 6 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 6 => Finset.Icc (-(n : ℤ)) n).filter fun x =>
    ∑ i, x i = 0 ∧
      (Finset.univ.filter (fun i => 0 < x i)).card = (Finset.univ.filter (fun i => x i < 0)).card

/-- A201814(n): the number of such arrays. -/
noncomputable def a (n : ℕ) : ℕ := (arrays n).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (141 + 155 * X + 730 * X ^ 2 + 150 * X ^ 3 + 145 * X ^ 4 - X ^ 5) ∧
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) := by
  sorry

end OMA.S_oeis_a201814
