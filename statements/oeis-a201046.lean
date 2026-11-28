import Mathlib

/-!
# OEIS A201046: Barker's generating function and recurrence

Source: https://oeis.org/A201046 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 26 2011), offset 1: Number of -n..n arrays of 7 elements with adjacent
element differences also in -n..n. Data: 577, 17981, 182349, 1042167, 4211559, 13497523, 36644243,
87831605, 191065045, 384593857, ... The formula section states: Empirical: a(n) = (17141/630)*n^7 +
(17141/180)*n^6 + (28177/180)*n^5 + (2759/18)*n^4 + (17299/180)*n^3 + (6929/180)*n^2 +
(1921/210)*n + 1. Conjectures from Colin Barker, May 22 2018: (Start) G.f.: x*(577 + 13365*x +
54657*x^2 + 54531*x^3 + 13449*x^4 + 541*x^5 + 9*x^6 - x^7) / (1 - x)^8. a(n) = 8*a(n-1) -
28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>8. (End)

Formalization notes:
* An array is a function x : Fin 7 → ℤ, the array x(0..6). `arrays n` is the set of arrays with
  every entry in -n..n (a `Fintype.piFinset` of `Finset.Icc (-n) n`) and every adjacent difference
  x(i+1) - x(i) in -n..n; `a n` is its cardinality.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^8 = N(x) in Z[[x]],
  which is equivalent because 1 - x is a unit. The recurrence is stated in the integers, for n > 8
  as in the entry.
* `main` is the conjunction of Barker's two conjectures, in the entry's order.
* Controls proved in the proof file: a(1..21), all the entry's listed terms.
-/

namespace OMA.S_oeis_a201046

open PowerSeries

/-- The -n..n arrays x(0..6) of 7 elements with adjacent element differences x(i+1) - x(i)
also in -n..n. -/
noncomputable def arrays (n : ℕ) : Finset (Fin 7 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 7 => Finset.Icc (-(n : ℤ)) n).filter fun x =>
    ∀ i : Fin 6, -(n : ℤ) ≤ x i.succ - x i.castSucc ∧ x i.succ - x i.castSucc ≤ n

/-- A201046(n): the number of -n..n arrays of 7 elements with adjacent element differences
also in -n..n. -/
noncomputable def a (n : ℕ) : ℕ := (arrays n).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      X * (577 + 13365 * X + 54657 * X ^ 2 + 54531 * X ^ 3 + 13449 * X ^ 4 + 541 * X ^ 5 + 9 * X ^ 6 - X ^ 7) ∧
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) := by
  sorry

end OMA.S_oeis_a201046
