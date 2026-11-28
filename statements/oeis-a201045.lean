import Mathlib

/-!
# OEIS A201045: Barker's generating function and recurrence

Source: https://oeis.org/A201045 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 26 2011), offset 1: Number of -n..n arrays of 6 elements with adjacent
element differences also in -n..n. Data: 239, 4569, 33305, 148433, 491429, 1333683, 3139529,
6641881, 12930475, 23552717, ... The formula section states: Empirical: a(n) = (2101/120)*n^6 +
(2101/40)*n^5 + (1753/24)*n^4 + (1405/24)*n^3 + (569/20)*n^2 + (119/15)*n + 1. Conjectures from
Colin Barker, May 22 2018: (Start) G.f.: x*(239 + 2896*x + 6341*x^2 + 2882*x^3 + 253*x^4 - 6*x^5 +
x^6) / (1 - x)^7. a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) +
a(n-7) for n>7. (End)

Formalization notes:
* An array is a function x : Fin 6 → ℤ, the array x(0..5). `arrays n` is the set of arrays with
  every entry in -n..n (a `Fintype.piFinset` of `Finset.Icc (-n) n`) and every adjacent difference
  x(i+1) - x(i) in -n..n; `a n` is its cardinality.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^7 = N(x) in Z[[x]],
  which is equivalent because 1 - x is a unit. The recurrence is stated in the integers, for n > 7
  as in the entry.
* `main` is the conjunction of Barker's two conjectures, in the entry's order.
* Controls proved in the proof file: a(1..23), all the entry's listed terms.
-/

namespace OMA.S_oeis_a201045

open PowerSeries

/-- The -n..n arrays x(0..5) of 6 elements with adjacent element differences x(i+1) - x(i)
also in -n..n. -/
noncomputable def arrays (n : ℕ) : Finset (Fin 6 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 6 => Finset.Icc (-(n : ℤ)) n).filter fun x =>
    ∀ i : Fin 5, -(n : ℤ) ≤ x i.succ - x i.castSucc ∧ x i.succ - x i.castSucc ≤ n

/-- A201045(n): the number of -n..n arrays of 6 elements with adjacent element differences
also in -n..n. -/
noncomputable def a (n : ℕ) : ℕ := (arrays n).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      X * (239 + 2896 * X + 6341 * X ^ 2 + 2882 * X ^ 3 + 253 * X ^ 4 - 6 * X ^ 5 + X ^ 6) ∧
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a201045
