import Mathlib

/-!
# OEIS A250143: Barker's recurrence and generating function

Source: https://oeis.org/A250143 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 13 2014), offset 1: Number of length 4+2 0..n arrays with the medians of
every three consecutive terms nondecreasing. Data: 41, 391, 1959, 6902, 19446, 46914, 100962,
199023, 365959, 635921, ... The formula section states: Empirical: a(n) = (13/45)*n^6 + (5/2)*n^5 +
(595/72)*n^4 + (53/4)*n^3 + (3941/360)*n^2 + (19/4)*n + 1. Conjectures from Colin Barker, Nov 11
2018: (Start) G.f.: x*(41 + 104*x + 83*x^2 - 35*x^3 + 21*x^4 - 7*x^5 + x^6) / (1 - x)^7. a(n) =
7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7. (End)

Formalization notes:
* An array is a function x : Fin 6 → Fin (n + 1), the array x(0..5) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`. The instance only makes `good` decidable, so
  that `a n` is a computable count.
* `med a b c` is the median of a, b, c (the middle value after sorting), written as max (min a b)
  (min (max a b) c); `good x` says that the medians of the consecutive triples x(i), x(i+1), x(i+2)
  are nondecreasing in i, i = 0..3.
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^7 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..26), all the entry's listed terms.
-/

namespace OMA.S_oeis_a250143

open PowerSeries

/-- The median of three numbers. -/
def med (a b c : ℕ) : ℕ := max (min a b) (min (max a b) c)

/-- The medians of the consecutive triples of x(0..5) are nondecreasing. -/
def good (x : Fin 6 → ℕ) : Prop :=
  med (x 0) (x 1) (x 2) ≤ med (x 1) (x 2) (x 3) ∧
    med (x 1) (x 2) (x 3) ≤ med (x 2) (x 3) (x 4) ∧
    med (x 2) (x 3) (x 4) ≤ med (x 3) (x 4) (x 5)

instance : DecidablePred good := fun x => by unfold good; infer_instance

/-- A250143(n): the number of 0..n arrays x(0..5) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 6 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      X * (41 + 104 * X + 83 * X ^ 2 - 35 * X ^ 3 + 21 * X ^ 4 - 7 * X ^ 5 + X ^ 6) := by
  sorry

end OMA.S_oeis_a250143
