import Mathlib

/-!
# OEIS A221543: Barker's generating function and recurrence

Source: https://oeis.org/A221543 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 19 2013), offset 1: Number of 0..n arrays of length 5 with each element
differing from at least one neighbor by something other than 1, starting with 0. Data: 3, 22, 103,
303, 716, ... The formula section states: Empirical: a(n) = 1*n^4 + 1*n^3 - 3*n^2 + 10*n - 9 for
n>3. Conjectures from Colin Barker, Aug 08 2018: (Start) G.f.: x*(3 + 7*x + 23*x^2 - 22*x^3 +
26*x^4 - 18*x^5 + 6*x^6 - x^7) / (1 - x)^5. a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) +
a(n-5) for n>8. (End)

Formalization notes:
* An array of length 5 is a function `Fin 5 → ℕ`, x i being the element at position i, counted from
  0, and a 0..n array starting with 0 has every element in 0..n and x 0 = 0. The neighbors of the
  element at position i are the elements at the adjacent positions i - 1 and i + 1 that exist. Two
  elements differ by something other than 1 when neither is the other plus 1, stated as x i ≠ x j +
  1 ∧ x j ≠ x i + 1 (this includes equal elements, as in the entry's examples); `good x` says that
  every element has a neighbor from which it differs by something other than 1.
* `a n` is `Set.ncard` of the set of good arrays with elements in 0..n, starting with 0. The set is
  finite: the proof identifies it with a finite set of tuples.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - x)^5 = x(3 + 7x + 23x^2 - 22x^3 + 26x^4 -
  18x^5 + 6x^6 - x^7) in Z[[x]], which is equivalent because (1 - x)^5 has constant term 1. The
  recurrence is stated in the integers for n > 8.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..33), all the entry's listed terms.
-/

namespace OMA.S_oeis_a221543

open PowerSeries

/-- Every element of the array x of length 5 differs from at least one of its neighbors (the
elements at the adjacent positions) by something other than 1. -/
def good (x : Fin 5 → ℕ) : Prop :=
  ∀ i : Fin 5, ∃ j : Fin 5, (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧
    x i ≠ x j + 1 ∧ x j ≠ x i + 1

/-- A221543(n): the number of arrays of length 5 with elements in 0..n, starting with 0, in which
every element differs from at least one of its neighbors by something other than 1. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin 5 → ℕ | x 0 = 0 ∧ (∀ i, x i ≤ n) ∧ good x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 5 =
      X * (3 + 7 * X + 23 * X ^ 2 - 22 * X ^ 3 + 26 * X ^ 4 - 18 * X ^ 5 + 6 * X ^ 6 - X ^ 7) ∧
    ∀ n : ℕ, 8 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) +
      a (n - 5) := by
  sorry

end OMA.S_oeis_a221543
