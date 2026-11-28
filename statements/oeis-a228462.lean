import Mathlib

/-!
# OEIS A228462: Barker's recurrence and generating function

Source: https://oeis.org/A228462 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Aug 22 2013), offset 1: Number of arrays of maxima of three adjacent elements
of some length 7 0..n array. Data: 17, 91, 310, 821, 1847, 3703, 6812, 11721, 19117, 29843, ... The
formula section states: Empirical: a(n) = (2/15)*n^5 + (7/6)*n^4 + (25/6)*n^3 + (19/3)*n^2 +
(21/5)*n + 1. Conjectures from Colin Barker, Sep 11 2018: (Start) G.f.: x*(17 - 11*x + 19*x^2 -
14*x^3 + 6*x^4 - x^5) / (1 - x)^6. a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) -
a(n-6) for n>6. (End)

Formalization notes:
* An array is a function from Fin m to Fin (n + 1), entries in 0..n. `maxima x` is the array y(0..4)
  with y(i) = max(x(i), x(i+1), x(i+2)) for x = x(0..6), and `a n` counts the arrays y : Fin 5 → Fin
  (n + 1) for which some x : Fin 7 → Fin (n + 1) has maxima x = y: the number of distinct arrays of
  maxima of three adjacent elements, which is how the name is read (it reproduces the entry's data).
* The proof characterizes these arrays (y is a maxima array iff it is the maxima array of the array
  whose entry j is the minimum of the y(i) over the windows containing j); the characterization is a
  lemma of the proof file, not part of the definition.
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^6 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..32), all the entry's listed terms.
-/

namespace OMA.S_oeis_a228462

open PowerSeries

/-- The maxima of the three adjacent elements x(i), x(i+1), x(i+2) of x(0..6), for
i = 0..4. -/
def maxima {n : ℕ} (x : Fin 7 → Fin (n + 1)) : Fin 5 → Fin (n + 1) :=
  fun i => max (x ⟨i, by have := i.isLt; omega⟩)
    (max (x ⟨i + 1, by have := i.isLt; omega⟩) (x ⟨i + 2, by have := i.isLt; omega⟩))

/-- A228462(n): the number of arrays y(0..4) that are the array of maxima of three adjacent
elements of some 0..n array x(0..6). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun y : Fin 5 → Fin (n + 1) =>
    ∃ x : Fin 7 → Fin (n + 1), maxima x = y)).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (17 - 11 * X + 19 * X ^ 2 - 14 * X ^ 3 + 6 * X ^ 4 - X ^ 5) := by
  sorry

end OMA.S_oeis_a228462
