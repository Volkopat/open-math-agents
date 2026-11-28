import Mathlib

/-!
# OEIS A199901: Barker's generating function and recurrence

Source: https://oeis.org/A199901 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 11 2011), offset 1: Number of -n..n arrays x(0..5) of 6 elements with zero
sum, and adjacent elements not both strictly positive and not both strictly negative. Data: 75, 533,
2035, 5725, 13363, 27457, 51395, 89577, 147547, 232125, ... The formula section states: Empirical:
a(n) = (11/10)*n^5 + (55/6)*n^4 + (55/2)*n^3 + (173/6)*n^2 + (37/5)*n + 1. Conjectures from Colin
Barker, May 16 2018: (Start) G.f.: x*(75 + 83*x - 38*x^2 + 10*x^3 + 3*x^4 - x^5) / (1 - x)^6. a(n) =
6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6. (End)

Formalization notes:
* An array is a function x : Fin 6 → ℤ, the array x(0..5). `arrays n` is the set of arrays with
  every entry in -n..n (a `Fintype.piFinset` of `Finset.Icc (-n) n`), zero sum, and adjacent
  elements x(i), x(i+1) not both strictly positive and not both strictly negative; `a n` is its
  cardinality.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^6 = N(x) in Z[[x]],
  which is equivalent because 1 - x is a unit. The recurrence is stated in the integers, for n > 6
  as in the entry.
* `main` is the conjunction of Barker's two conjectures, in the entry's order.
* Controls proved in the proof file: a(1..29), all the entry's listed terms.
-/

namespace OMA.S_oeis_a199901

open PowerSeries

/-- The -n..n arrays x(0..5) of 6 elements with zero sum and, for every i, adjacent elements x(i),
x(i+1) not both strictly positive and not both strictly negative. -/
noncomputable def arrays (n : ℕ) : Finset (Fin 6 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 6 => Finset.Icc (-(n : ℤ)) n).filter fun x =>
    ∑ i, x i = 0 ∧ ∀ i : Fin 5, ¬ (0 < x i.castSucc ∧ 0 < x i.succ) ∧
      ¬ (x i.castSucc < 0 ∧ x i.succ < 0)

/-- A199901(n): the number of such arrays. -/
noncomputable def a (n : ℕ) : ℕ := (arrays n).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (75 + 83 * X - 38 * X ^ 2 + 10 * X ^ 3 + 3 * X ^ 4 - X ^ 5) ∧
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) := by
  sorry

end OMA.S_oeis_a199901
