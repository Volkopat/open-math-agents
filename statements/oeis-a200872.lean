import Mathlib

/-!
# OEIS A200872: Barker's recurrence and generating function

Source: https://oeis.org/A200872 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 23 2011), offset 1: Number of 0..n arrays x(0..3) of 4 elements without any
interior element greater than both neighbors or less than both neighbors. Data: 10, 37, 94, 195,
356, 595, 932, 1389, 1990, 2761, ... The formula section states: Empirical: a(n) = (1/12)*n^4 +
(3/2)*n^3 + (47/12)*n^2 + (7/2)*n + 1. Conjectures from Colin Barker, Oct 16 2017: (Start) G.f.:
x*(10 - 13*x + 9*x^2 - 5*x^3 + x^4) / (1 - x)^5. a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) -
5*a(n-4) + a(n-5) for n>5. (End)

Formalization notes:
* An array is a function x : Fin 4 → Fin (n + 1), the array x(0..3) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`. The instance only makes `good` decidable, so
  that `a n` is a computable count.
* `good x` says that neither interior element, x 1 or x 2, is greater than both of its neighbors or
  less than both of them (strict comparisons).
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^5 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..38), all the entry's listed terms.
-/

namespace OMA.S_oeis_a200872

open PowerSeries

/-- No interior element of x(0..3) is greater than both neighbors or less than both neighbors
(strict comparisons). -/
def good (x : Fin 4 → ℕ) : Prop :=
  ¬ (x 0 < x 1 ∧ x 2 < x 1) ∧ ¬ (x 1 < x 0 ∧ x 1 < x 2) ∧
    ¬ (x 1 < x 2 ∧ x 3 < x 2) ∧ ¬ (x 2 < x 1 ∧ x 2 < x 3)

instance : DecidablePred good := fun x => by unfold good; infer_instance

/-- A200872(n): the number of 0..n arrays x(0..3) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 4 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 5 =
      X * (10 - 13 * X + 9 * X ^ 2 - 5 * X ^ 3 + X ^ 4) := by
  sorry

end OMA.S_oeis_a200872
