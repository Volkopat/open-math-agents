import Mathlib

/-!
# OEIS A199533: Barker's generating function and recurrence

Source: https://oeis.org/A199533 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 07 2011), offset 1: Number of -n..n arrays x(0..5) of 6 elements with zero
sum and no two consecutive zero elements. Data: 80, 1414, 8342, 30484, 84852, 197962, 407946,
766664, 1341816, 2219054, ... The formula section states: Empirical: a(n) = (88/5)*n^5 + 44*n^4 +
(58/3)*n^3 - 3*n^2 + (31/15)*n. Conjectures from Colin Barker, May 15 2018: (Start) G.f.: 2*x*(40 +
467*x + 529*x^2 + 21*x^3 - x^4) / (1 - x)^6. a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) +
6*a(n-5) - a(n-6) for n>6. (End)

Formalization notes:
* An array is a function x : Fin 6 → ℤ, the array x(0..5). `arrays n` is the set of arrays with
  every entry in -n..n (a `Fintype.piFinset` of `Finset.Icc (-n) n`), zero sum, and no two
  consecutive zero elements: no i with x(i) = x(i+1) = 0; `a n` is its cardinality.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^6 = N(x) in Z[[x]],
  which is equivalent because 1 - x is a unit. The recurrence is stated in the integers, for n > 6
  as in the entry.
* `main` is the conjunction of Barker's two conjectures, in the entry's order.
* Controls proved in the proof file: a(1..26), all the entry's listed terms.
-/

namespace OMA.S_oeis_a199533

open PowerSeries

/-- The -n..n arrays x(0..5) of 6 elements with zero sum and, for every i, no two consecutive zero
elements: no i with x(i) = x(i+1) = 0. -/
noncomputable def arrays (n : ℕ) : Finset (Fin 6 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 6 => Finset.Icc (-(n : ℤ)) n).filter fun x =>
    ∑ i, x i = 0 ∧ ∀ i : Fin 5, ¬ (x i.castSucc = 0 ∧ x i.succ = 0)

/-- A199533(n): the number of such arrays. -/
noncomputable def a (n : ℕ) : ℕ := (arrays n).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      2 * X * (40 + 467 * X + 529 * X ^ 2 + 21 * X ^ 3 - X ^ 4) ∧
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) := by
  sorry

end OMA.S_oeis_a199533
