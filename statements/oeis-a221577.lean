import Mathlib

/-!
# OEIS A221577: Barker's generating function and recurrence

Source: https://oeis.org/A221577 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 20 2013), offset 1: Number of 0..n arrays of length 7 with each element
differing from at least one neighbor by something other than 1. Data: 16, 345, 4240, 26911,
117104, ... The formula section states: Empirical: a(n) = 1*n^7 + 3*n^6 - 7*n^5 + 29*n^4 -
41*n^3 + 45*n^2 - 33*n + 19 for n>2. Conjectures from Colin Barker, Aug 08 2018: (Start) G.f.:
x*(16 + 217*x + 1928*x^2 + 1755*x^3 + 2336*x^4 - 1869*x^5 + 1096*x^6 - 579*x^7 + 160*x^8 -
20*x^9) / (1 - x)^8. a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) -
28*a(n-6) + 8*a(n-7) - a(n-8) for n>10. (End)

Formalization notes:
* An array of length 7 is a function `Fin 7 → ℕ`, x i being the element at position i, counted
  from 0, and a 0..n array has every element in 0..n. The neighbors of the element at position i
  are the elements at the adjacent positions i - 1 and i + 1 that exist. Two elements differ by
  something other than 1 when neither is the other plus 1, stated as x i ≠ x j + 1 ∧
  x j ≠ x i + 1 (this includes equal elements, as in the entry's examples); `good x` says that
  every element has a neighbor from which it differs by something other than 1.
* `a n` is `Set.ncard` of the set of good arrays with elements in 0..n. The set is finite: the
  proof identifies it with a finite set of tuples.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - x)^8 = x (16 + 217x + 1928x^2 + 1755x^3 +
  2336x^4 - 1869x^5 + 1096x^6 - 579x^7 + 160x^8 - 20x^9) in Z[[x]], which is equivalent because
  (1 - x)^8 has constant term 1. The recurrence is stated in the integers for n > 10.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..23), all the entry's listed terms.
-/

namespace OMA.S_oeis_a221577

open PowerSeries

/-- Every element of the array x of length 7 differs from at least one of its neighbors (the
elements at the adjacent positions) by something other than 1. -/
def good (x : Fin 7 → ℕ) : Prop :=
  ∀ i : Fin 7, ∃ j : Fin 7, (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ x i ≠ x j + 1 ∧ x j ≠ x i + 1

/-- A221577(n): the number of arrays of length 7 with elements in 0..n in which every element
differs from at least one of its neighbors by something other than 1. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin 7 → ℕ | (∀ i, x i ≤ n) ∧ good x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      X * (16 + 217 * X + 1928 * X ^ 2 + 1755 * X ^ 3 + 2336 * X ^ 4 - 1869 * X ^ 5 +
        1096 * X ^ 6 - 579 * X ^ 7 + 160 * X ^ 8 - 20 * X ^ 9) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) -
      70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  sorry

end OMA.S_oeis_a221577
