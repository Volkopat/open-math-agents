import Mathlib

/-!
# OEIS A221598: Barker's generating function and recurrence

Source: https://oeis.org/A221598 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 20 2013), offset 1: Number of 0..n arrays of length 6 with each element
differing from at least one neighbor by 1 or less. Data: 64, 393, 1210, 2715, 5082, ... The formula
section states: Empirical: a(n) = 27*n^3 + 108*n^2 - 252*n + 267 for n>3. Conjectures from Colin
Barker, Aug 09 2018: (Start) G.f.: x*(64 + 137*x + 22*x^2 - 23*x^3 - 26*x^4 - 10*x^5 - 2*x^6) / (1
- x)^4. a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>7. (End)

Formalization notes:
* An array of length 6 is a function `Fin 6 → ℕ`, x i being the element at position i, counted from
  0, and a 0..n array has every element in 0..n. The neighbors of the element at position i are the
  elements at the adjacent positions i - 1 and i + 1 that exist. Two elements differ by 1 or less
  when each is at most the other plus 1, stated as x i ≤ x j + 1 ∧ x j ≤ x i + 1 (this includes
  equal elements); `good x` says that every element has a neighbor from which it differs by 1 or
  less.
* `a n` is `Set.ncard` of the set of good arrays with elements in 0..n. The set is finite: the
  proof identifies it with a finite set of tuples.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - x)^4 = x(64 + 137x + 22x^2 - 23x^3 - 26x^4 -
  10x^5 - 2x^6) in Z[[x]], which is equivalent because (1 - x)^4 has constant term 1. The
  recurrence is stated in the integers for n > 7.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..33), all the entry's listed terms.
-/

namespace OMA.S_oeis_a221598

open PowerSeries

/-- Every element of the array x of length 6 differs from at least one of its neighbors (the
elements at the adjacent positions) by 1 or less. -/
def good (x : Fin 6 → ℕ) : Prop :=
  ∀ i : Fin 6, ∃ j : Fin 6, (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧
    (x i ≤ x j + 1 ∧ x j ≤ x i + 1)

/-- A221598(n): the number of arrays of length 6 with elements in 0..n in which every element
differs from at least one of its neighbors by 1 or less. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin 6 → ℕ | (∀ i, x i ≤ n) ∧ good x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 4 =
      X * (64 + 137 * X + 22 * X ^ 2 - 23 * X ^ 3 - 26 * X ^ 4 - 10 * X ^ 5 - 2 * X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a221598
