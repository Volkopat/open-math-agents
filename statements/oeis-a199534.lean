import Mathlib

/-!
# OEIS A199534: Barker's generating function and recurrence

Source: https://oeis.org/A199534 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 07 2011), offset 1: Number of -n..n arrays x(0..6) of 7 elements with zero
sum and no two consecutive zero elements. Data: 200, 6346, 53302, 252154, 860854, 2378412, 5662636,
12071420, 23627580, 43207238, ... The formula section states: Empirical: a(n) = (5887/180)*n^6 +
(5887/60)*n^5 + (620/9)*n^4 + (11/12)*n^3 + (433/180)*n^2 - (91/30)*n. Conjectures from Colin
Barker, May 16 2018: (Start) G.f.: 2*x*(100 + 2473*x + 6540*x^2 + 2653*x^3 + 4*x^4 + 4*x^5) / (1 -
x)^7. a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
(End)

Formalization notes:
* An array is a function x : Fin 7 → ℤ, the array x(0..6). `arrays n` is the set of arrays with
  every entry in -n..n (a `Fintype.piFinset` of `Finset.Icc (-n) n`), zero sum, and no two
  consecutive zero elements: no i with x(i) = x(i+1) = 0; `a n` is its cardinality.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^7 = N(x) in Z[[x]],
  which is equivalent because 1 - x is a unit. The recurrence is stated in the integers, for n > 7
  as in the entry.
* `main` is the conjunction of Barker's two conjectures, in the entry's order.
* Controls proved in the proof file: a(1..23), all the entry's listed terms.
-/

namespace OMA.S_oeis_a199534

open PowerSeries

/-- The -n..n arrays x(0..6) of 7 elements with zero sum and, for every i, no two consecutive zero
elements: no i with x(i) = x(i+1) = 0. -/
noncomputable def arrays (n : ℕ) : Finset (Fin 7 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 7 => Finset.Icc (-(n : ℤ)) n).filter fun x =>
    ∑ i, x i = 0 ∧ ∀ i : Fin 6, ¬ (x i.castSucc = 0 ∧ x i.succ = 0)

/-- A199534(n): the number of such arrays. -/
noncomputable def a (n : ℕ) : ℕ := (arrays n).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      2 * X * (100 + 2473 * X + 6540 * X ^ 2 + 2653 * X ^ 3 + 4 * X ^ 4 + 4 * X ^ 5) ∧
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a199534
