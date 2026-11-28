import Mathlib

/-!
# OEIS A221518: Barker's generating function and recurrence

Source: https://oeis.org/A221518 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 18 2013), offset 1: Number of 0..n arrays of length 7 with each element
differing from at least one neighbor by 2 or more, starting with 0. Data: 0, 8, 248, 2088, 9940,
... The formula section states: Empirical: a(n) = 1*n^6 + 1*n^5 - 29*n^4 + 104*n^3 - 173*n^2 +
136*n - 40 for n>3. Conjectures from Colin Barker, Aug 06 2018: (Start) G.f.: 2*x^2*(4 + 96*x +
260*x^2 + 126*x^3 - 136*x^4 + 43*x^5 - 49*x^6 + 19*x^7 - 3*x^8) / (1 - x)^7. a(n) = 7*a(n-1) -
21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>10. (End)

Formalization notes:
* An array of length 7 is a function `Fin 7 → ℕ`, x i being the element at position i, counted
  from 0, and a 0..n array starting with 0 has every element in 0..n and x 0 = 0. The neighbors of
  the element at position i are the elements at the adjacent positions i - 1 and i + 1 that exist.
  Two elements differ by 2 or more when one is at least the other plus 2, stated as
  x i + 2 ≤ x j ∨ x j + 2 ≤ x i; `good x` says that every element has a neighbor from which it
  differs by 2 or more.
* `a n` is `Set.ncard` of the set of good arrays with elements in 0..n starting with 0. The set is
  finite: the proof identifies it with a finite set of tuples.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - x)^7 = 2x^2 (4 + 96x + 260x^2 + 126x^3 -
  136x^4 + 43x^5 - 49x^6 + 19x^7 - 3x^8) in Z[[x]], which is equivalent because (1 - x)^7 has
  constant term 1. The recurrence is stated in the integers for n > 10.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..27), all the entry's listed terms.
-/

namespace OMA.S_oeis_a221518

open PowerSeries

/-- Every element of the array x of length 7 differs from at least one of its neighbors (the
elements at the adjacent positions) by 2 or more. -/
def good (x : Fin 7 → ℕ) : Prop :=
  ∀ i : Fin 7, ∃ j : Fin 7, (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ (x i + 2 ≤ x j ∨ x j + 2 ≤ x i)

/-- A221518(n): the number of arrays of length 7 with elements in 0..n, starting with 0, in which
every element differs from at least one of its neighbors by 2 or more. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin 7 → ℕ | x 0 = 0 ∧ (∀ i, x i ≤ n) ∧ good x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      2 * X ^ 2 * (4 + 96 * X + 260 * X ^ 2 + 126 * X ^ 3 - 136 * X ^ 4 + 43 * X ^ 5 -
        49 * X ^ 6 + 19 * X ^ 7 - 3 * X ^ 8) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) -
      35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a221518
