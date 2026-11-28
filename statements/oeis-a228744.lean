import Mathlib

/-!
# OEIS A228744: Barker's generating function and recurrence

Source: https://oeis.org/A228744 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Sep 01 2013), offset 1: Number of arrays of the median of three adjacent
elements of some length 9 0..n array. Data: 88, 1071, 6130, 23627, 71278, 181885, 410828, 845517,
1617004, 2913955, ... The formula section states: Empirical: a(n) = (5/126)*n^7 + (4/3)*n^6 +
(829/90)*n^5 + (93/4)*n^4 + (509/18)*n^3 + (221/12)*n^2 + (453/70)*n + 1. Conjectures from Colin
Barker, Mar 16 2018: (Start) G.f.: x*(88 + 367*x + 26*x^2 - 353*x^3 + 86*x^4 - 21*x^5 + 8*x^6 -
x^7) / (1 - x)^8. a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) +
8*a(n-7) - a(n-8) for n>8. (End)

Formalization notes:
* An array is a function from Fin m to Fin (n + 1), entries in 0..n. `med u v w` is the median of u,
  v, w (the middle value after sorting), written as max (min u v) (min (max u v) w). `medians x` is
  the array y(0..6) with y(i) the median of x(i), x(i+1), x(i+2) for x = x(0..8), and `a n` counts
  the arrays y : Fin 7 → Fin (n + 1) for which some x : Fin 9 → Fin (n + 1) has medians x = y: the
  number of distinct arrays of medians of three adjacent elements, which is how the name is read (it
  reproduces the entry's data, and the row of the table A228740).
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^8 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures, the g.f. first, as the entry states them.
* Controls proved in the proof file: a(1..26), all the entry's listed terms.
-/

namespace OMA.S_oeis_a228744

open PowerSeries

/-- The median of three elements of a linear order. -/
def med {α : Type*} [LinearOrder α] (u v w : α) : α := max (min u v) (min (max u v) w)

/-- The medians of the three adjacent elements x(i), x(i+1), x(i+2) of x(0..8), for
i = 0..6. -/
def medians {n : ℕ} (x : Fin 9 → Fin (n + 1)) : Fin 7 → Fin (n + 1) :=
  fun i => med (x ⟨i, by have := i.isLt; omega⟩) (x ⟨i + 1, by have := i.isLt; omega⟩)
    (x ⟨i + 2, by have := i.isLt; omega⟩)

/-- A228744(n): the number of arrays y(0..6) that are the array of medians of three adjacent
elements of some 0..n array x(0..8). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun y : Fin 7 → Fin (n + 1) =>
    ∃ x : Fin 9 → Fin (n + 1), medians x = y)).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      X * (88 + 367 * X + 26 * X ^ 2 - 353 * X ^ 3 + 86 * X ^ 4 - 21 * X ^ 5 + 8 * X ^ 6 - X ^ 7) ∧
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) := by
  sorry

end OMA.S_oeis_a228744
