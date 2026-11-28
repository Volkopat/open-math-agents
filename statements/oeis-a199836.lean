import Mathlib

/-!
# OEIS A199836: Barker's generating function and recurrence

Source: https://oeis.org/A199836 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 11 2011), offset 1: Number of -n..n arrays x(0..6) of 7 elements with zero
sum and no two neighbors summing to zero. Data: 22, 1650, 20240, 118280, 462234, 1402934, 3579520,
8046928, 16426926, 31082698, ... The formula section states: Empirical: a(n) = (5887/180)*n^6 -
(1013/60)*n^5 + (245/36)*n^4 - (35/12)*n^3 + (157/45)*n^2 - (6/5)*n. Conjectures from Colin Barker,
May 16 2018: (Start) G.f.: 2*x*(11 + 748*x + 4576*x^2 + 5240*x^3 + 1167*x^4 + 32*x^5) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7. (End)

Formalization notes:
* An array is a function x : Fin 7 → ℤ, the array x(0..6). `arrays n` is the set of arrays with
  every entry in -n..n (a `Fintype.piFinset` of `Finset.Icc (-n) n`), zero sum, and x(i) + x(i+1) ≠
  0 for every i; `a n` is its cardinality.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^7 = N(x) in Z[[x]],
  which is equivalent because 1 - x is a unit. The recurrence is stated in the integers, for n > 7
  as in the entry.
* `main` is the conjunction of Barker's two conjectures, in the entry's order.
* Controls proved in the proof file: a(1..23), all the entry's listed terms.
-/

namespace OMA.S_oeis_a199836

open PowerSeries

/-- The -n..n arrays x(0..6) of 7 elements with zero sum and no two neighbors summing to
zero. -/
noncomputable def arrays (n : ℕ) : Finset (Fin 7 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 7 => Finset.Icc (-(n : ℤ)) n).filter fun x =>
    ∑ i, x i = 0 ∧ ∀ i : Fin 6, x i.castSucc + x i.succ ≠ 0

/-- A199836(n): the number of such arrays. -/
noncomputable def a (n : ℕ) : ℕ := (arrays n).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      2 * X * (11 + 748 * X + 4576 * X ^ 2 + 5240 * X ^ 3 + 1167 * X ^ 4 + 32 * X ^ 5) ∧
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a199836
