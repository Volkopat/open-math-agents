import Mathlib

/-!
# OEIS A228463: Barker's recurrence and generating function

Source: https://oeis.org/A228463 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Aug 22 2013), offset 1: Number of arrays of maxima of three adjacent elements
of some length 8 0..n array. Data: 27, 183, 736, 2227, 5615, 12453, 25096, 46941, 82699, 138699, ...
The formula section states: Empirical: a(n) = (2/45)*n^6 + (8/15)*n^5 + (115/36)*n^4 + 8*n^3 +
(1667/180)*n^2 + (149/30)*n + 1. Conjectures from Colin Barker, Sep 11 2018: (Start) G.f.: x*(27 -
6*x + 22*x^2 - 27*x^3 + 22*x^4 - 7*x^5 + x^6) / (1 - x)^7. a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) -
35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7. (End)

Formalization notes:
* An array is a function from Fin m to Fin (n + 1), entries in 0..n. `maxima x` is the array y(0..5)
  with y(i) = max(x(i), x(i+1), x(i+2)) for x = x(0..7), and `a n` counts the arrays y : Fin 6 → Fin
  (n + 1) for which some x : Fin 8 → Fin (n + 1) has maxima x = y: the number of distinct arrays of
  maxima of three adjacent elements, which is how the name is read (it reproduces the entry's data).
* The proof characterizes these arrays (y is a maxima array iff it is the maxima array of the array
  whose entry j is the minimum of the y(i) over the windows containing j); the characterization is a
  lemma of the proof file, not part of the definition.
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^7 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..29), all the entry's listed terms.
-/

namespace OMA.S_oeis_a228463

open PowerSeries

/-- The maxima of the three adjacent elements x(i), x(i+1), x(i+2) of x(0..7), for
i = 0..5. -/
def maxima {n : ℕ} (x : Fin 8 → Fin (n + 1)) : Fin 6 → Fin (n + 1) :=
  fun i => max (x ⟨i, by have := i.isLt; omega⟩)
    (max (x ⟨i + 1, by have := i.isLt; omega⟩) (x ⟨i + 2, by have := i.isLt; omega⟩))

/-- A228463(n): the number of arrays y(0..5) that are the array of maxima of three adjacent
elements of some 0..n array x(0..7). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun y : Fin 6 → Fin (n + 1) =>
    ∃ x : Fin 8 → Fin (n + 1), maxima x = y)).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      X * (27 - 6 * X + 22 * X ^ 2 - 27 * X ^ 3 + 22 * X ^ 4 - 7 * X ^ 5 + X ^ 6) := by
  sorry

end OMA.S_oeis_a228463
