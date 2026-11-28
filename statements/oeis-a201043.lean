import Mathlib

/-!
# OEIS A201043: Barker's generating function and recurrence

Source: https://oeis.org/A201043 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 26 2011), offset 1: Number of -n..n arrays of 4 elements with adjacent
element differences also in -n..n. Data: 41, 295, 1111, 3011, 6691, 13021, 23045, 37981, 59221,
88331, ... The formula section states: Empirical: a(n) = (29/4)*n^4 + (29/2)*n^3 + (51/4)*n^2 +
(11/2)*n + 1. Conjectures from Colin Barker, May 21 2018: (Start) G.f.: x*(41 + 90*x + 46*x^2 -
4*x^3 + x^4) / (1 - x)^5. a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5. (End)

Formalization notes:
* An array is a function x : Fin 4 → ℤ, the array x(0..3). `arrays n` is the set of arrays with
  every entry in -n..n (a `Fintype.piFinset` of `Finset.Icc (-n) n`) and every adjacent difference
  x(i+1) - x(i) in -n..n; `a n` is its cardinality.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^5 = N(x) in Z[[x]],
  which is equivalent because 1 - x is a unit. The recurrence is stated in the integers, for n > 5
  as in the entry.
* `main` is the conjunction of Barker's two conjectures, in the entry's order.
* Controls proved in the proof file: a(1..30), all the entry's listed terms.
-/

namespace OMA.S_oeis_a201043

open PowerSeries

/-- The -n..n arrays x(0..3) of 4 elements with adjacent element differences x(i+1) - x(i)
also in -n..n. -/
noncomputable def arrays (n : ℕ) : Finset (Fin 4 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 4 => Finset.Icc (-(n : ℤ)) n).filter fun x =>
    ∀ i : Fin 3, -(n : ℤ) ≤ x i.succ - x i.castSucc ∧ x i.succ - x i.castSucc ≤ n

/-- A201043(n): the number of -n..n arrays of 4 elements with adjacent element differences
also in -n..n. -/
noncomputable def a (n : ℕ) : ℕ := (arrays n).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 5 =
      X * (41 + 90 * X + 46 * X ^ 2 - 4 * X ^ 3 + X ^ 4) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) := by
  sorry

end OMA.S_oeis_a201043
