import Mathlib

/-!
# OEIS A228464: Barker's recurrence and generating function

Source: https://oeis.org/A228464 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Aug 22 2013), offset 1: Number of arrays of maxima of three adjacent elements
of some 0..n array of length 9. Data: 44, 383, 1821, 6254, 17487, 42386, 92430, 185727, 349558,
623513, ... The formula section states: Empirical: a(n) = (4/315)*n^7 + (1/5)*n^6 + (91/45)*n^5 +
(63/8)*n^4 + (2557/180)*n^3 + (517/40)*n^2 + (2419/420)*n + 1 = (n+1) *(n+2) *(32*n^5 + 408*n^4 +
3808*n^3 + 7605*n^2 + 5367*n + 1260)/2520. Conjectures from Colin Barker, Mar 16 2018: (Start) G.f.:
x*(44 + 31*x - 11*x^2 - 54*x^3 + 75*x^4 - 28*x^5 + 8*x^6 - x^7) / (1 - x)^8. a(n) = 8*a(n-1) -
28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>8. (End)

Formalization notes:
* An array is a function from Fin m to Fin (n + 1), entries in 0..n. `maxima x` is the array y(0..6)
  with y(i) = max(x(i), x(i+1), x(i+2)) for x = x(0..8), and `a n` counts the arrays y : Fin 7 → Fin
  (n + 1) for which some x : Fin 9 → Fin (n + 1) has maxima x = y: the number of distinct arrays of
  maxima of three adjacent elements, which is how the name is read (it reproduces the entry's data).
* The proof characterizes these arrays (y is a maxima array iff it is the maxima array of the array
  whose entry j is the minimum of the y(i) over the windows containing j); the characterization is a
  lemma of the proof file, not part of the definition.
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^8 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..27), all the entry's listed terms.
-/

namespace OMA.S_oeis_a228464

open PowerSeries

/-- The maxima of the three adjacent elements x(i), x(i+1), x(i+2) of x(0..8), for
i = 0..6. -/
def maxima {n : ℕ} (x : Fin 9 → Fin (n + 1)) : Fin 7 → Fin (n + 1) :=
  fun i => max (x ⟨i, by have := i.isLt; omega⟩)
    (max (x ⟨i + 1, by have := i.isLt; omega⟩) (x ⟨i + 2, by have := i.isLt; omega⟩))

/-- A228464(n): the number of arrays y(0..6) that are the array of maxima of three adjacent
elements of some 0..n array x(0..8). -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun y : Fin 7 → Fin (n + 1) =>
    ∃ x : Fin 9 → Fin (n + 1), maxima x = y)).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      X * (44 + 31 * X - 11 * X ^ 2 - 54 * X ^ 3 + 75 * X ^ 4 - 28 * X ^ 5 + 8 * X ^ 6 - X ^ 7) := by
  sorry

end OMA.S_oeis_a228464
