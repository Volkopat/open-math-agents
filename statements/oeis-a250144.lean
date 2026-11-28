import Mathlib

/-!
# OEIS A250144: Barker's recurrence and generating function

Source: https://oeis.org/A250144 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 13 2014), offset 1: Number of length 5+2 0..n arrays with the medians of
every three consecutive terms nondecreasing. Data: 68, 900, 5696, 24125, 79200, 217856, 526032,
1149057, 2318140, 4383764, ... The formula section states: Empirical: a(n) = (10/63)*n^7 +
(163/90)*n^6 + (1421/180)*n^5 + (625/36)*n^4 + (751/36)*n^3 + (2489/180)*n^2 + (178/35)*n + 1.
Conjectures from Colin Barker, Nov 11 2018: (Start) G.f.: x*(68 + 356*x + 400*x^2 - 51*x^3 +
48*x^4 - 28*x^5 + 8*x^6 - x^7) / (1 - x)^8. a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) +
56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>8. (End)

Formalization notes:
* An array is a function x : Fin 7 → Fin (n + 1), the array x(0..6) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`. The instance only makes `good` decidable, so
  that `a n` is a computable count.
* `med a b c` is the median of a, b, c (the middle value after sorting), written as max (min a b)
  (min (max a b) c); `good x` says that the medians of the consecutive triples x(i), x(i+1), x(i+2)
  are nondecreasing in i, i = 0..4.
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^8 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..25), all the entry's listed terms.
-/

namespace OMA.S_oeis_a250144

open PowerSeries

/-- The median of three numbers. -/
def med (a b c : ℕ) : ℕ := max (min a b) (min (max a b) c)

/-- The medians of the consecutive triples of x(0..6) are nondecreasing. -/
def good (x : Fin 7 → ℕ) : Prop :=
  med (x 0) (x 1) (x 2) ≤ med (x 1) (x 2) (x 3) ∧
    med (x 1) (x 2) (x 3) ≤ med (x 2) (x 3) (x 4) ∧
    med (x 2) (x 3) (x 4) ≤ med (x 3) (x 4) (x 5) ∧
    med (x 3) (x 4) (x 5) ≤ med (x 4) (x 5) (x 6)

instance : DecidablePred good := fun x => by unfold good; infer_instance

/-- A250144(n): the number of 0..n arrays x(0..6) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 7 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      X * (68 + 356 * X + 400 * X ^ 2 - 51 * X ^ 3 + 48 * X ^ 4 - 28 * X ^ 5 + 8 * X ^ 6 - X ^ 7) := by
  sorry

end OMA.S_oeis_a250144
