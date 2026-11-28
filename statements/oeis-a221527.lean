import Mathlib

/-!
# OEIS A221527: Barker's generating function and recurrence

Source: https://oeis.org/A221527 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 19 2013), offset 1: Number of 0..n arrays of length 7 with each element
differing from at least one neighbor by 2 or more. Data: 0, 16, 768, 8544, 50400, ... The formula
section states: Empirical: a(n) = 1*n^7 + 1*n^6 - 29*n^5 + 109*n^4 - 204*n^3 + 202*n^2 - 80*n for
n>2. Conjectures from Colin Barker, Aug 06 2018: (Start) G.f.: 8*x^2*(2 + 80*x + 356*x^2 + 332*x^3
- 97*x^4 - 22*x^5 - 28*x^6 + 8*x^7 - x^8) / (1 - x)^8. a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) -
70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>10. (End)

Formalization notes:
* An array of length 7 is a function `Fin 7 → ℕ`, x i being the element at position i, counted from
  0, and a 0..n array has every element in 0..n. The neighbors of the element at position i are the
  elements at the adjacent positions i - 1 and i + 1 that exist. Two elements differ by 2 or more
  when one is at least the other plus 2, stated as x i + 2 ≤ x j ∨ x j + 2 ≤ x i; `good x` says
  that every element has a neighbor from which it differs by 2 or more.
* `a n` is `Set.ncard` of the set of good arrays with elements in 0..n. The set is finite: the
  proof identifies it with a finite set of tuples.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - x)^8 = 8x^2(2 + 80x + 356x^2 + 332x^3 - 97x^4
  - 22x^5 - 28x^6 + 8x^7 - x^8) in Z[[x]], which is equivalent because (1 - x)^8 has constant term
  1. The recurrence is stated in the integers for n > 10.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..24), all the entry's listed terms.
-/

namespace OMA.S_oeis_a221527

open PowerSeries

/-- Every element of the array x of length 7 differs from at least one of its neighbors (the
elements at the adjacent positions) by 2 or more. -/
def good (x : Fin 7 → ℕ) : Prop :=
  ∀ i : Fin 7, ∃ j : Fin 7, (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧
    (x i + 2 ≤ x j ∨ x j + 2 ≤ x i)

/-- A221527(n): the number of arrays of length 7 with elements in 0..n in which every element
differs from at least one of its neighbors by 2 or more. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin 7 → ℕ | (∀ i, x i ≤ n) ∧ good x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      8 * X ^ 2 * (2 + 80 * X + 356 * X ^ 2 + 332 * X ^ 3 - 97 * X ^ 4 - 22 * X ^ 5 - 28 * X ^ 6 +
        8 * X ^ 7 - X ^ 8) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) +
      56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8) := by
  sorry

end OMA.S_oeis_a221527
