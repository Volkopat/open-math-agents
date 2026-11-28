import Mathlib

/-!
# OEIS A221544: Barker's generating function and recurrence

Source: https://oeis.org/A221544 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 19 2013), offset 1: Number of 0..n arrays of length 6 with each element
differing from at least one neighbor by something other than 1, starting with 0. Data: 5, 54, 364,
1386, 4018, ... The formula section states: Empirical: a(n) = 1*n^5 + 2*n^4 - 6*n^3 + 21*n^2 - 31*n
+ 23 for n>4. Conjectures from Colin Barker, Aug 08 2018: (Start) G.f.: x*(5 + 24*x + 115*x^2 -
88*x^3 + 157*x^4 - 153*x^5 + 87*x^6 - 34*x^7 + 8*x^8 - x^9) / (1 - x)^6. a(n) = 6*a(n-1) -
15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>10. (End)

Formalization notes:
* An array of length 6 is a function `Fin 6 → ℕ`, x i being the element at position i, counted from
  0, and a 0..n array starting with 0 has every element in 0..n and x 0 = 0. The neighbors of the
  element at position i are the elements at the adjacent positions i - 1 and i + 1 that exist. Two
  elements differ by something other than 1 when neither is the other plus 1, stated as x i ≠ x j +
  1 ∧ x j ≠ x i + 1 (this includes equal elements, as in the entry's examples); `good x` says that
  every element has a neighbor from which it differs by something other than 1.
* `a n` is `Set.ncard` of the set of good arrays with elements in 0..n, starting with 0. The set is
  finite: the proof identifies it with a finite set of tuples.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - x)^6 = x(5 + 24x + 115x^2 - 88x^3 + 157x^4 -
  153x^5 + 87x^6 - 34x^7 + 8x^8 - x^9) in Z[[x]], which is equivalent because (1 - x)^6 has
  constant term 1. The recurrence is stated in the integers for n > 10.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..30), all the entry's listed terms.
-/

namespace OMA.S_oeis_a221544

open PowerSeries

/-- Every element of the array x of length 6 differs from at least one of its neighbors (the
elements at the adjacent positions) by something other than 1. -/
def good (x : Fin 6 → ℕ) : Prop :=
  ∀ i : Fin 6, ∃ j : Fin 6, (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧
    x i ≠ x j + 1 ∧ x j ≠ x i + 1

/-- A221544(n): the number of arrays of length 6 with elements in 0..n, starting with 0, in which
every element differs from at least one of its neighbors by something other than 1. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin 6 → ℕ | x 0 = 0 ∧ (∀ i, x i ≤ n) ∧ good x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (5 + 24 * X + 115 * X ^ 2 - 88 * X ^ 3 + 157 * X ^ 4 - 153 * X ^ 5 + 87 * X ^ 6 -
        34 * X ^ 7 + 8 * X ^ 8 - X ^ 9) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) +
      6 * a (n - 5) - a (n - 6) := by
  sorry

end OMA.S_oeis_a221544
