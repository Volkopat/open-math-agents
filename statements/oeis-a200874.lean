import Mathlib

/-!
# OEIS A200874: Barker's recurrence and generating function

Source: https://oeis.org/A200874 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 23 2011), offset 1: Number of 0..n arrays x(0..5) of 6 elements without any
interior element greater than both neighbors or less than both neighbors. Data: 26, 163, 602, 1673,
3886, 7973, 14932, 26073, 43066, 67991, ... The formula section states: Empirical: a(n) =
(1/360)*n^6 + (7/24)*n^5 + (197/72)*n^4 + (185/24)*n^3 + (1667/180)*n^2 + 5*n + 1. Conjectures from
Colin Barker, Oct 16 2017: (Start) G.f.: x*(26 - 19*x + 7*x^2 - 28*x^3 + 22*x^4 - 7*x^5 + x^6) /
(1 - x)^7. a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for
n>7. (End)

Formalization notes:
* An array is a function x : Fin 6 → Fin (n + 1), the array x(0..5) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`. The instance only makes `good` decidable, so
  that `a n` is a computable count.
* `good x` says that no interior element, x 1 to x 4, is greater than both of its neighbors or less
  than both of them (strict comparisons).
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^7 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..30), all the entry's listed terms.
-/

namespace OMA.S_oeis_a200874

open PowerSeries

/-- No interior element of x(0..5) is greater than both neighbors or less than both neighbors
(strict comparisons). -/
def good (x : Fin 6 → ℕ) : Prop :=
  ¬ (x 0 < x 1 ∧ x 2 < x 1) ∧ ¬ (x 1 < x 0 ∧ x 1 < x 2) ∧
    ¬ (x 1 < x 2 ∧ x 3 < x 2) ∧ ¬ (x 2 < x 1 ∧ x 2 < x 3) ∧
    ¬ (x 2 < x 3 ∧ x 4 < x 3) ∧ ¬ (x 3 < x 2 ∧ x 3 < x 4) ∧
    ¬ (x 3 < x 4 ∧ x 5 < x 4) ∧ ¬ (x 4 < x 3 ∧ x 4 < x 5)

instance : DecidablePred good := fun x => by unfold good; infer_instance

/-- A200874(n): the number of 0..n arrays x(0..5) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 6 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      X * (26 - 19 * X + 7 * X ^ 2 - 28 * X ^ 3 + 22 * X ^ 4 - 7 * X ^ 5 + X ^ 6) := by
  sorry

end OMA.S_oeis_a200874
