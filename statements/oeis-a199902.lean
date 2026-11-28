import Mathlib

/-!
# OEIS A199902: Barker's generating function and recurrence

Source: https://oeis.org/A199902 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 11 2011), offset 1: Number of -n..n arrays x(0..6) of 7 elements with zero
sum, and adjacent elements not both strictly positive and not both strictly negative. Data: 171,
1783, 8823, 30199, 82555, 193689, 406575, 783989, 1413739, 2414499, ... The formula section states:
Empirical: a(n) = (151/180)*n^6 + (163/15)*n^5 + (377/9)*n^4 + (395/6)*n^3 + (7429/180)*n^2 +
(93/10)*n + 1. Conjectures from Colin Barker, May 17 2018: (Start) G.f.: x*(171 + 586*x - 67*x^2 -
104*x^3 + 25*x^4 - 8*x^5 + x^6) / (1 - x)^7. a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) +
21*a(n-5) - 7*a(n-6) + a(n-7) for n>7. (End)

Formalization notes:
* An array is a function x : Fin 7 → ℤ, the array x(0..6). `arrays n` is the set of arrays with
  every entry in -n..n (a `Fintype.piFinset` of `Finset.Icc (-n) n`), zero sum, and adjacent
  elements x(i), x(i+1) not both strictly positive and not both strictly negative; `a n` is its
  cardinality.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^7 = N(x) in Z[[x]],
  which is equivalent because 1 - x is a unit. The recurrence is stated in the integers, for n > 7
  as in the entry.
* `main` is the conjunction of Barker's two conjectures, in the entry's order.
* Controls proved in the proof file: a(1..26), all the entry's listed terms.
-/

namespace OMA.S_oeis_a199902

open PowerSeries

/-- The -n..n arrays x(0..6) of 7 elements with zero sum and, for every i, adjacent elements x(i),
x(i+1) not both strictly positive and not both strictly negative. -/
noncomputable def arrays (n : ℕ) : Finset (Fin 7 → ℤ) :=
  (Fintype.piFinset fun _ : Fin 7 => Finset.Icc (-(n : ℤ)) n).filter fun x =>
    ∑ i, x i = 0 ∧ ∀ i : Fin 6, ¬ (0 < x i.castSucc ∧ 0 < x i.succ) ∧
      ¬ (x i.castSucc < 0 ∧ x i.succ < 0)

/-- A199902(n): the number of such arrays. -/
noncomputable def a (n : ℕ) : ℕ := (arrays n).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      X * (171 + 586 * X - 67 * X ^ 2 - 104 * X ^ 3 + 25 * X ^ 4 - 8 * X ^ 5 + X ^ 6) ∧
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) := by
  sorry

end OMA.S_oeis_a199902
