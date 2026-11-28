import Mathlib

/-!
# OEIS A201813: Barker's generating function and recurrence

Source: https://oeis.org/A201813 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 05 2011), offset 1: Number of arrays of 5 integers in -n..n with sum zero
and equal numbers of elements greater than zero and less than zero. Data: 51, 221, 631, 1401, 2651,
4501, 7071, 10481, 14851, 20301, ... The formula section states: Empirical: a(n) = 20*n^3 + 30*n +
1. Conjectures from Colin Barker, May 25 2018: (Start) G.f.: x*(51 + 17*x + 53*x^2 - x^3) / (1 -
x)^4. a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>4. (End)

Formalization notes:
* An array is a function x : Fin 5 → ℤ, the array x(0..4). `arrays n` is the set of arrays with
  every entry in -n..n (a `Fintype.piFinset` of `Finset.Icc (-n) n`), zero sum, and as many entries
  greater than zero as entries less than zero (the two `Finset.filter` cardinalities); `a n` is its
  cardinality.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^4 = N(x) in Z[[x]],
  which is equivalent because 1 - x is a unit. The recurrence is stated in the integers, for n > 4
  as in the entry.
* `main` is the conjunction of Barker's two conjectures, in the entry's order.
* Controls proved in the proof file: a(1..33), all the entry's listed terms.
-/

namespace OMA.S_oeis_a201813

open PowerSeries

/-- The arrays x(0..4) of 5 integers in -n..n with sum zero and as many entries greater than
zero as entries less than zero. -/
noncomputable def arrays (n : ℕ) : Finset (Fin 5 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 5 => Finset.Icc (-(n : ℤ)) n).filter fun x =>
    ∑ i, x i = 0 ∧
      (Finset.univ.filter (fun i => 0 < x i)).card = (Finset.univ.filter (fun i => x i < 0)).card

/-- A201813(n): the number of such arrays. -/
noncomputable def a (n : ℕ) : ℕ := (arrays n).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 4 =
      X * (51 + 17 * X + 53 * X ^ 2 - X ^ 3) ∧
    (∀ n : ℕ, 4 < n →
      (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4)) := by
  sorry

end OMA.S_oeis_a201813
