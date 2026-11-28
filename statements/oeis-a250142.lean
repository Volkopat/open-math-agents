import Mathlib

/-!
# OEIS A250142: Barker's recurrence and generating function

Source: https://oeis.org/A250142 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 13 2014), offset 1: Number of length 3+2 0..n arrays with the medians of
every three consecutive terms nondecreasing. Data: 24, 162, 632, 1827, 4368, 9156, 17424, 30789,
51304, 81510, ... The formula section states: Empirical: a(n) = (13/30)*n^5 + 3*n^4 + (22/3)*n^3 +
8*n^2 + (127/30)*n + 1. Conjectures from Colin Barker, Nov 11 2018: (Start) G.f.: x*(24 + 18*x +
20*x^2 - 15*x^3 + 6*x^4 - x^5) / (1 - x)^6. a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) +
6*a(n-5) - a(n-6) for n>6. (End)

Formalization notes:
* An array is a function x : Fin 5 → Fin (n + 1), the array x(0..4) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`. The instance only makes `good` decidable, so
  that `a n` is a computable count.
* `med a b c` is the median of a, b, c (the middle value after sorting), written as max (min a b)
  (min (max a b) c); `good x` says that the medians of the consecutive triples x(i), x(i+1), x(i+2)
  are nondecreasing in i, i = 0..2.
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^6 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..30), all the entry's listed terms.
-/

namespace OMA.S_oeis_a250142

open PowerSeries

/-- The median of three numbers. -/
def med (a b c : ℕ) : ℕ := max (min a b) (min (max a b) c)

/-- The medians of the consecutive triples of x(0..4) are nondecreasing. -/
def good (x : Fin 5 → ℕ) : Prop :=
  med (x 0) (x 1) (x 2) ≤ med (x 1) (x 2) (x 3) ∧
    med (x 1) (x 2) (x 3) ≤ med (x 2) (x 3) (x 4)

instance : DecidablePred good := fun x => by unfold good; infer_instance

/-- A250142(n): the number of 0..n arrays x(0..4) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 5 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (24 + 18 * X + 20 * X ^ 2 - 15 * X ^ 3 + 6 * X ^ 4 - X ^ 5) := by
  sorry

end OMA.S_oeis_a250142
