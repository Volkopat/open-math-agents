import Mathlib

/-!
# OEIS A221597: Barker's generating function and recurrence

Source: https://oeis.org/A221597 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 20 2013), offset 1: Number of 0..n arrays of length 5 with each element
differing from at least one neighbor by 1 or less. Data: 32, 139, 342, 651, 1068, ... The formula
section states: Empirical: a(n) = 54*n^2 - 69*n + 63 for n>2. Conjectures from Colin Barker, Aug 09
2018: (Start) G.f.: x*(32 + 43*x + 21*x^2 + 10*x^3 + 2*x^4) / (1 - x)^3. a(n) = 3*a(n-1) - 3*a(n-2)
+ a(n-3) for n>5. (End)

Formalization notes:
* An array of length 5 is a function `Fin 5 → ℕ`, x i being the element at position i, counted from
  0, and a 0..n array has every element in 0..n. The neighbors of the element at position i are the
  elements at the adjacent positions i - 1 and i + 1 that exist. Two elements differ by 1 or less
  when each is at most the other plus 1, stated as x i ≤ x j + 1 ∧ x j ≤ x i + 1 (this includes
  equal elements); `good x` says that every element has a neighbor from which it differs by 1 or
  less.
* `a n` is `Set.ncard` of the set of good arrays with elements in 0..n. The set is finite: the
  proof identifies it with a finite set of tuples.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - x)^3 = x(32 + 43x + 21x^2 + 10x^3 + 2x^4) in
  Z[[x]], which is equivalent because (1 - x)^3 has constant term 1. The recurrence is stated in
  the integers for n > 5.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..39), all the entry's listed terms.
-/

namespace OMA.S_oeis_a221597

open PowerSeries

/-- Every element of the array x of length 5 differs from at least one of its neighbors (the
elements at the adjacent positions) by 1 or less. -/
def good (x : Fin 5 → ℕ) : Prop :=
  ∀ i : Fin 5, ∃ j : Fin 5, (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧
    (x i ≤ x j + 1 ∧ x j ≤ x i + 1)

/-- A221597(n): the number of arrays of length 5 with elements in 0..n in which every element
differs from at least one of its neighbors by 1 or less. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin 5 → ℕ | (∀ i, x i ≤ n) ∧ good x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 3 =
      X * (32 + 43 * X + 21 * X ^ 2 + 10 * X ^ 3 + 2 * X ^ 4) ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 3 * a (n - 1) - 3 * a (n - 2) + a (n - 3) := by
  sorry

end OMA.S_oeis_a221597
