import Mathlib

/-!
# OEIS A221599: Barker's generating function and recurrence

Source: https://oeis.org/A221599 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 20 2013), offset 1: Number of 0..n arrays of length 7 with each element
differing from at least one neighbor by 1 or less. Data: 128, 1113, 4240, 11011, 22912, ... The
formula section states: Empirical: a(n) = 243*n^3 - 351*n^2 + 237*n + 127 for n>2. Conjectures from
Colin Barker, Aug 09 2018: (Start) G.f.: x*(128 + 601*x + 556*x^2 + 217*x^3 - 16*x^4 - 28*x^5) / (1
- x)^4. a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>6. (End)

Formalization notes:
* An array of length 7 is a function `Fin 7 → ℕ`, x i being the element at position i, counted from
  0, and a 0..n array has every element in 0..n. The neighbors of the element at position i are the
  elements at the adjacent positions i - 1 and i + 1 that exist. Two elements differ by 1 or less
  when each is at most the other plus 1, stated as x i ≤ x j + 1 ∧ x j ≤ x i + 1 (this includes
  equal elements); `good x` says that every element has a neighbor from which it differs by 1 or
  less.
* `a n` is `Set.ncard` of the set of good arrays with elements in 0..n. The set is finite: the
  proof identifies it with a finite set of tuples.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - x)^4 = x(128 + 601x + 556x^2 + 217x^3 - 16x^4
  - 28x^5) in Z[[x]], which is equivalent because (1 - x)^4 has constant term 1. The recurrence is
  stated in the integers for n > 6.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..29), all the entry's listed terms.
-/

namespace OMA.S_oeis_a221599

open PowerSeries

/-- Every element of the array x of length 7 differs from at least one of its neighbors (the
elements at the adjacent positions) by 1 or less. -/
def good (x : Fin 7 → ℕ) : Prop :=
  ∀ i : Fin 7, ∃ j : Fin 7, (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧
    (x i ≤ x j + 1 ∧ x j ≤ x i + 1)

/-- A221599(n): the number of arrays of length 7 with elements in 0..n in which every element
differs from at least one of its neighbors by 1 or less. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin 7 → ℕ | (∀ i, x i ≤ n) ∧ good x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 4 =
      X * (128 + 601 * X + 556 * X ^ 2 + 217 * X ^ 3 - 16 * X ^ 4 - 28 * X ^ 5) ∧
    ∀ n : ℕ, 6 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a221599
