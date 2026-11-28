import Mathlib

/-!
# OEIS A199532: Barker's generating function and recurrence

Source: https://oeis.org/A199532 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 07 2011), offset 1: Number of -n..n arrays x(0..4) of 5 elements with zero
sum and no two consecutive zero elements. Data: 32, 320, 1324, 3734, 8470, 16682, 29750, 49284,
77124, 115340, ... The formula section states: Empirical: a(n) = (115/12)*n^4 + (115/6)*n^3 +
(41/12)*n^2 - (1/6)*n. Conjectures from Colin Barker, May 15 2018: (Start) G.f.: 2*x*(16 + 80*x +
22*x^2 - 3*x^3) / (1 - x)^5. a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.
(End)

Formalization notes:
* An array is a function x : Fin 5 → ℤ, the array x(0..4). `arrays n` is the set of arrays with
  every entry in -n..n (a `Fintype.piFinset` of `Finset.Icc (-n) n`), zero sum, and no two
  consecutive zero elements: no i with x(i) = x(i+1) = 0; `a n` is its cardinality.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^5 = N(x) in Z[[x]],
  which is equivalent because 1 - x is a unit. The recurrence is stated in the integers, for n > 5
  as in the entry.
* `main` is the conjunction of Barker's two conjectures, in the entry's order.
* Controls proved in the proof file: a(1..30), all the entry's listed terms.
-/

namespace OMA.S_oeis_a199532

open PowerSeries

/-- The -n..n arrays x(0..4) of 5 elements with zero sum and, for every i, no two consecutive zero
elements: no i with x(i) = x(i+1) = 0. -/
noncomputable def arrays (n : ℕ) : Finset (Fin 5 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 5 => Finset.Icc (-(n : ℤ)) n).filter fun x =>
    ∑ i, x i = 0 ∧ ∀ i : Fin 4, ¬ (x i.castSucc = 0 ∧ x i.succ = 0)

/-- A199532(n): the number of such arrays. -/
noncomputable def a (n : ℕ) : ℕ := (arrays n).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 5 =
      2 * X * (16 + 80 * X + 22 * X ^ 2 - 3 * X ^ 3) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) := by
  sorry

end OMA.S_oeis_a199532
