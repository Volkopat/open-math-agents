import Mathlib

/-!
# OEIS A221576: Barker's generating function and recurrence

Source: https://oeis.org/A221576 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 20 2013), offset 1: Number of 0..n arrays of length 6 with each element
differing from at least one neighbor by something other than 1. Data: 10, 141, 1210, 5913, 20944,
... The formula section states: Empirical: a(n) = 1*n^6 + 2*n^5 - 5*n^4 + 24*n^3 - 41*n^2 +
50*n - 31 for n>3. Conjectures from Colin Barker, Aug 08 2018: (Start) G.f.: x*(10 + 71*x +
433*x^2 + 54*x^3 + 378*x^4 - 355*x^5 + 193*x^6 - 80*x^7 + 18*x^8 - 2*x^9) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>10.
(End)

Formalization notes:
* An array of length 6 is a function `Fin 6 → ℕ`, x i being the element at position i, counted
  from 0, and a 0..n array has every element in 0..n. The neighbors of the element at position i
  are the elements at the adjacent positions i - 1 and i + 1 that exist. Two elements differ by
  something other than 1 when neither is the other plus 1, stated as x i ≠ x j + 1 ∧
  x j ≠ x i + 1 (this includes equal elements, as in the entry's examples); `good x` says that
  every element has a neighbor from which it differs by something other than 1.
* `a n` is `Set.ncard` of the set of good arrays with elements in 0..n. The set is finite: the
  proof identifies it with a finite set of tuples.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1; the count for n = 0 is not a term of the
  sequence and is replaced by 0), stated as A(x) (1 - x)^7 = x (10 + 71x + 433x^2 + 54x^3 +
  378x^4 - 355x^5 + 193x^6 - 80x^7 + 18x^8 - 2x^9) in Z[[x]], which is equivalent because
  (1 - x)^7 has constant term 1. The recurrence is stated in the integers for n > 10.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..26), all the entry's listed terms.
-/

namespace OMA.S_oeis_a221576

open PowerSeries

/-- Every element of the array x of length 6 differs from at least one of its neighbors (the
elements at the adjacent positions) by something other than 1. -/
def good (x : Fin 6 → ℕ) : Prop :=
  ∀ i : Fin 6, ∃ j : Fin 6, (i.val + 1 = j.val ∨ j.val + 1 = i.val) ∧ x i ≠ x j + 1 ∧ x j ≠ x i + 1

/-- A221576(n): the number of arrays of length 6 with elements in 0..n in which every element
differs from at least one of its neighbors by something other than 1. -/
noncomputable def a (n : ℕ) : ℕ := Set.ncard {x : Fin 6 → ℕ | (∀ i, x i ≤ n) ∧ good x}

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      X * (10 + 71 * X + 433 * X ^ 2 + 54 * X ^ 3 + 378 * X ^ 4 - 355 * X ^ 5 + 193 * X ^ 6 -
        80 * X ^ 7 + 18 * X ^ 8 - 2 * X ^ 9) ∧
    ∀ n : ℕ, 10 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) -
      35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a221576
