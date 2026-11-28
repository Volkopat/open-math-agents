import Mathlib

/-!
# OEIS A199838: Barker's generating function and recurrence

Source: https://oeis.org/A199838 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 11 2011), offset 1: Number of -n..n arrays x(0..8) of 9 elements with zero
sum and no two neighbors summing to zero. Data: 66, 23206, 645780, 6715618, 41008804, 179213048,
622300326, 1827026482, 4719970500, 11025201168, ... The formula section states: Empirical: a(n) =
(259723/2240)*n^8 - (299869/5040)*n^7 + (39757/1440)*n^6 - (8303/360)*n^5 + (31829/2880)*n^4 -
(8083/720)*n^3 + (32213/5040)*n^2 - (509/420)*n. Conjectures from Colin Barker, Mar 02 2018: (Start)
G.f.: 2*x*(33 + 11306*x + 219651*x^2 + 866735*x^3 + 937667*x^4 + 283090*x^5 + 18897*x^6 + 128*x^7) /
(1 - x)^9. a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) +
36*a(n-7) - 9*a(n-8) + a(n-9) for n>9. (End)

Formalization notes:
* An array is a function x : Fin 9 → ℤ, the array x(0..8). `arrays n` is the set of arrays with
  every entry in -n..n (a `Fintype.piFinset` of `Finset.Icc (-n) n`), zero sum, and x(i) + x(i+1) ≠
  0 for every i; `a n` is its cardinality.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^9 = N(x) in Z[[x]],
  which is equivalent because 1 - x is a unit. The recurrence is stated in the integers, for n > 9
  as in the entry.
* `main` is the conjunction of Barker's two conjectures, in the entry's order.
* Controls proved in the proof file: a(1..19), all the entry's listed terms.
-/

namespace OMA.S_oeis_a199838

open PowerSeries

/-- The -n..n arrays x(0..8) of 9 elements with zero sum and no two neighbors summing to
zero. -/
noncomputable def arrays (n : ℕ) : Finset (Fin 9 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 9 => Finset.Icc (-(n : ℤ)) n).filter fun x =>
    ∑ i, x i = 0 ∧ ∀ i : Fin 8, x i.castSucc + x i.succ ≠ 0

/-- A199838(n): the number of such arrays. -/
noncomputable def a (n : ℕ) : ℕ := (arrays n).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 9 =
      2 * X * (33 + 11306 * X + 219651 * X ^ 2 + 866735 * X ^ 3 + 937667 * X ^ 4 + 283090 * X ^ 5 + 18897 * X ^ 6 + 128 * X ^ 7) ∧
    (∀ n : ℕ, 9 < n →
      (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) := by
  sorry

end OMA.S_oeis_a199838
