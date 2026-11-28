import Mathlib

/-!
# OEIS A221685: Barker's generating function and recurrence

Source: https://oeis.org/A221685 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 22 2013), offset 1: Number of 0..n arrays of length 6 with each element
differing from at least one neighbor by 1 or less, starting with 0. Data: 32, 113, 241, 418, 636,
... The formula section states: Empirical: a(n) = 18*n^2 + 57*n - 99 for n>4. Conjectures from
Colin Barker, Aug 10 2018: (Start) G.f.: x*(32 + 17*x - 2*x^2 + 2*x^3 - 8*x^4 - 4*x^5 - x^6) / (1 -
x)^3. a(n) = 3*a(n-1) - 3*a(n-2) + a(n-3) for n>7. (End)

Formalization notes:
* An array of length 6 is a function `Fin 6 → ℕ`, x i being the element at position i, counted from
  0, and a 0..n array starting with 0 has every element in 0..n and x 0 = 0. The neighbors of the
  element at position i are the elements at the adjacent positions i - 1 and i + 1 that exist. Two
  elements differ by 1 or less when each is at most the other plus 1, stated as x i ≤ x j + 1 ∧ x j
  ≤ x i + 1 (this includes equal elements); `good x` says that every element has a neighbor from
  which it differs by 1 or less.
* `a n` is `Set.ncard` of the set of good arrays with elements in 0..n, starting with 0. The set is
  finite: the proof identifies it with a finite set of tuples.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - x)^3 = x(32 + 17x - 2x^2 + 2x^3 - 8x^4 - 4x^5
  - x^6) in Z[[x]], which is equivalent because (1 - x)^3 has constant term 1. The recurrence is
  stated in the integers for n > 7.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..40), all the entry's listed terms.
-/

namespace OMA.S_oeis_a221685

open PowerSeries

/-- Every element of the array x of length 6 differs from at least one of its neighbors (the
elements at the adjacent positions) by 1 or less. -/
def good (x : Fin 6 → ℕ) : Prop :=
  ∀ i : Fin 6, ∃ j : Fin 6, (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧
    (x i ≤ x j + 1 ∧ x j ≤ x i + 1)

/-- A221685(n): the number of arrays of length 6 with elements in 0..n, starting with 0, in which
every element differs from at least one of its neighbors by 1 or less. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin 6 → ℕ | x 0 = 0 ∧ (∀ i, x i ≤ n) ∧ good x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 3 =
      X * (32 + 17 * X - 2 * X ^ 2 + 2 * X ^ 3 - 8 * X ^ 4 - 4 * X ^ 5 - X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  sorry

end OMA.S_oeis_a221685
