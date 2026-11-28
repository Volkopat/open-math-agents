import Mathlib

/-!
# OEIS A221575: Barker's generating function and recurrence

Source: https://oeis.org/A221575 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 20 2013), offset 1: Number of 0..n arrays of length 5 with each element
differing from at least one neighbor by something other than 1. Data: 6, 57, 342, 1293, 3734, ...
The formula section states: Empirical: a(n) = 1*n^5 + 1*n^4 - 2*n^3 + 12*n^2 - 15*n + 9 for n>2.
Conjectures from Colin Barker, Aug 08 2018: (Start) G.f.: x*(6 + 21*x + 90*x^2 - 24*x^3 + 56*x^4 -
39*x^5 + 12*x^6 - 2*x^7) / (1 - x)^6. a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) +
6*a(n-5) - a(n-6) for n>8. (End)

Formalization notes:
* An array of length 5 is a function `Fin 5 → ℕ`, x i being the element at position i, counted from
  0, and a 0..n array has every element in 0..n. The neighbors of the element at position i are the
  elements at the adjacent positions i - 1 and i + 1 that exist. Two elements differ by something
  other than 1 when neither is the other plus 1, stated as x i ≠ x j + 1 ∧ x j ≠ x i + 1 (this
  includes equal elements, as in the entry's examples); `good x` says that every element has a
  neighbor from which it differs by something other than 1.
* `a n` is `Set.ncard` of the set of good arrays with elements in 0..n. The set is finite: the
  proof identifies it with a finite set of tuples.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - x)^6 = x(6 + 21x + 90x^2 - 24x^3 + 56x^4 -
  39x^5 + 12x^6 - 2x^7) in Z[[x]], which is equivalent because (1 - x)^6 has constant term 1. The
  recurrence is stated in the integers for n > 8.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..30), all the entry's listed terms.
-/

namespace OMA.S_oeis_a221575

open PowerSeries

/-- Every element of the array x of length 5 differs from at least one of its neighbors (the
elements at the adjacent positions) by something other than 1. -/
def good (x : Fin 5 → ℕ) : Prop :=
  ∀ i : Fin 5, ∃ j : Fin 5, (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧
    x i ≠ x j + 1 ∧ x j ≠ x i + 1

/-- A221575(n): the number of arrays of length 5 with elements in 0..n in which every element
differs from at least one of its neighbors by something other than 1. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin 5 → ℕ | (∀ i, x i ≤ n) ∧ good x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (6 + 21 * X + 90 * X ^ 2 - 24 * X ^ 3 + 56 * X ^ 4 - 39 * X ^ 5 + 12 * X ^ 6 -
        2 * X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
      6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a221575
