import Mathlib

/-!
# OEIS A199837: Barker's generating function and recurrence

Source: https://oeis.org/A199837 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 11 2011), offset 1: Number of -n..n arrays x(0..7) of 8 elements with zero
sum and no two neighbors summing to zero. Data: 34, 6126, 113884, 888420, 4340094, 15805218,
47040968, 120843752, 277500282, 583380598, ... The formula section states: Empirical: a(n) =
(19328/315)*n^7 - (1424/45)*n^6 + (704/45)*n^5 - (112/9)*n^4 - (124/45)*n^3 + (229/45)*n^2 -
(131/105)*n. Conjectures from Colin Barker, May 16 2018: (Start) G.f.: 2*x*(17 + 2927*x +
32914*x^2 + 73486*x^3 + 40405*x^4 + 4819*x^5 + 56*x^6) / (1 - x)^8. a(n) = 8*a(n-1) - 28*a(n-2) +
56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>8. (End)

Formalization notes:
* An array is a function x : Fin 8 → ℤ, the array x(0..7). `arrays n` is the set of arrays with
  every entry in -n..n (a `Fintype.piFinset` of `Finset.Icc (-n) n`), zero sum, and x(i) + x(i+1) ≠
  0 for every i; `a n` is its cardinality.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^8 = N(x) in Z[[x]],
  which is equivalent because 1 - x is a unit. The recurrence is stated in the integers, for n > 8
  as in the entry.
* `main` is the conjunction of Barker's two conjectures, in the entry's order.
* Controls proved in the proof file: a(1..20), all the entry's listed terms.
-/

namespace OMA.S_oeis_a199837

open PowerSeries

/-- The -n..n arrays x(0..7) of 8 elements with zero sum and no two neighbors summing to
zero. -/
noncomputable def arrays (n : ℕ) : Finset (Fin 8 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 8 => Finset.Icc (-(n : ℤ)) n).filter fun x =>
    ∑ i, x i = 0 ∧ ∀ i : Fin 7, x i.castSucc + x i.succ ≠ 0

/-- A199837(n): the number of such arrays. -/
noncomputable def a (n : ℕ) : ℕ := (arrays n).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      2 * X * (17 + 2927 * X + 32914 * X ^ 2 + 73486 * X ^ 3 + 40405 * X ^ 4 + 4819 * X ^ 5 + 56 * X ^ 6) ∧
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) := by
  sorry

end OMA.S_oeis_a199837
