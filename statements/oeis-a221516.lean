import Mathlib

/-!
# OEIS A221516: Barker's generating function and recurrence

Source: https://oeis.org/A221516 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 18 2013), offset 1: Number of 0..n arrays of length 5 with each element
differing from at least one neighbor by 2 or more, starting with 0. Data: 0, 3, 30, 130, 381, ...
The formula section states: Empirical: a(n) = 1*n^4 - 1*n^3 - 10*n^2 + 33*n - 34 for n>3.
Conjectures from Colin Barker, Aug 06 2018: (Start) G.f.: x^2*(3 + 15*x + 10*x^2 + x^3 - 6*x^4 +
2*x^5 - x^6) / (1 - x)^5. a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>8.
(End)

Formalization notes:
* An array of length 5 is a function `Fin 5 → ℕ`, x i being the element at position i, counted from
  0, and a 0..n array starting with 0 has every element in 0..n and x 0 = 0. The neighbors of the
  element at position i are the elements at the adjacent positions i - 1 and i + 1 that exist. Two
  elements differ by 2 or more when one is at least the other plus 2, stated as x i + 2 ≤ x j ∨ x j
  + 2 ≤ x i; `good x` says that every element has a neighbor from which it differs by 2 or more.
* `a n` is `Set.ncard` of the set of good arrays with elements in 0..n, starting with 0. The set is
  finite: the proof identifies it with a finite set of tuples.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - x)^5 = x^2(3 + 15x + 10x^2 + x^3 - 6x^4 +
  2x^5 - x^6) in Z[[x]], which is equivalent because (1 - x)^5 has constant term 1. The recurrence
  is stated in the integers for n > 8.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..34), all the entry's listed terms.
-/

namespace OMA.S_oeis_a221516

open PowerSeries

/-- Every element of the array x of length 5 differs from at least one of its neighbors (the
elements at the adjacent positions) by 2 or more. -/
def good (x : Fin 5 → ℕ) : Prop :=
  ∀ i : Fin 5, ∃ j : Fin 5, (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧
    (x i + 2 ≤ x j ∨ x j + 2 ≤ x i)

/-- A221516(n): the number of arrays of length 5 with elements in 0..n, starting with 0, in which
every element differs from at least one of its neighbors by 2 or more. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin 5 → ℕ | x 0 = 0 ∧ (∀ i, x i ≤ n) ∧ good x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 5 =
      X ^ 2 * (3 + 15 * X + 10 * X ^ 2 + X ^ 3 - 6 * X ^ 4 + 2 * X ^ 5 - X ^ 6) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) +
      a (n - 5) := by
  sorry

end OMA.S_oeis_a221516
