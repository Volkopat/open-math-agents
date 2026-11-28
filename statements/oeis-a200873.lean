import Mathlib

/-!
# OEIS A200873: Barker's recurrence and generating function

Source: https://oeis.org/A200873 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 23 2011), offset 1: Number of 0..n arrays x(0..4) of 5 elements without any
interior element greater than both neighbors or less than both neighbors. Data: 16, 77, 236, 567,
1168, 2163, 3704, 5973, 9184, 13585, ... The formula section states: Empirical: a(n) = (1/60)*n^5 +
(3/4)*n^4 + (15/4)*n^3 + (25/4)*n^2 + (127/30)*n + 1. Conjectures from Colin Barker, Oct 16 2017:
(Start) G.f.: x*(16 - 19*x + 14*x^2 - 14*x^3 + 6*x^4 - x^5) / (1 - x)^6. a(n) = 6*a(n-1) -
15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6. (End)

Formalization notes:
* An array is a function x : Fin 5 → Fin (n + 1), the array x(0..4) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`. The instance only makes `good` decidable, so
  that `a n` is a computable count.
* `good x` says that no interior element, x 1 to x 3, is greater than both of its neighbors or less
  than both of them (strict comparisons).
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^6 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..33), all the entry's listed terms.
-/

namespace OMA.S_oeis_a200873

open PowerSeries

/-- No interior element of x(0..4) is greater than both neighbors or less than both neighbors
(strict comparisons). -/
def good (x : Fin 5 → ℕ) : Prop :=
  ¬ (x 0 < x 1 ∧ x 2 < x 1) ∧ ¬ (x 1 < x 0 ∧ x 1 < x 2) ∧
    ¬ (x 1 < x 2 ∧ x 3 < x 2) ∧ ¬ (x 2 < x 1 ∧ x 2 < x 3) ∧
    ¬ (x 2 < x 3 ∧ x 4 < x 3) ∧ ¬ (x 3 < x 2 ∧ x 3 < x 4)

instance : DecidablePred good := fun x => by unfold good; infer_instance

/-- A200873(n): the number of 0..n arrays x(0..4) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 5 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (16 - 19 * X + 14 * X ^ 2 - 14 * X ^ 3 + 6 * X ^ 4 - X ^ 5) := by
  sorry

end OMA.S_oeis_a200873
