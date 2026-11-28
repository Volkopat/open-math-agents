import Mathlib

/-!
# OEIS A251936: Barker's generating function and recurrence

Source: https://oeis.org/A251936 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Dec 11 2014), offset 1: Number of length 2+2 0..n arrays with the sum of the
maximum minus the median of adjacent triples multiplied by some arrangement of +-1 equal to zero.
Data: 10, 43, 120, 265, 506, 875, 1408, 2145, 3130, 4411, ... The formula section states: Empirical:
a(n) = (1/6)*n^4 + (7/3)*n^3 + (23/6)*n^2 + (8/3)*n + 1. Conjectures from Colin Barker, Dec 01 2018:
(Start) G.f.: x*(10 - 7*x + 5*x^2 - 5*x^3 + x^4) / (1 - x)^5. a(n) = 5*a(n-1) - 10*a(n-2) +
10*a(n-3) - 5*a(n-4) + a(n-5) for n>5. (End)

Formalization notes:
* An array is a function x : Fin 4 → Fin (n + 1), the length 2+2 array x(0..3) with entries in 0..n;
  `a n` counts those whose values `(x i : ℕ)` satisfy `good`.
* The adjacent triples are (x 0, x 1, x 2) and (x 1, x 2, x 3). `med` is the median of three numbers
  (max (min a b) (min (max a b) c)) and `topgap` the maximum minus the median; `good x` says that
  s * topgap (x 0) (x 1) (x 2) + t * topgap (x 1) (x 2) (x 3) = 0 in the integers for some
  arrangement of signs s, t in {1, -1}.
* The g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1), stated as A(x) (1 - x)^5 = N(x) in Z[[x]],
  which is equivalent because 1 - x is a unit. The recurrence is stated in the integers, for n > 5
  as in the entry.
* `main` is the conjunction of Barker's two conjectures, in the entry's order.
* Controls proved in the proof file: a(1..36), all the entry's listed terms.
-/

namespace OMA.S_oeis_a251936

open PowerSeries

/-- The median of three numbers. -/
def med (a b c : ℕ) : ℕ := max (min a b) (min (max a b) c)

/-- The maximum minus the median of three numbers. -/
def topgap (a b c : ℕ) : ℕ := max (max a b) c - med a b c

/-- The sum of (maximum - median) over the adjacent triples of x(0..3), each multiplied by +1 or
-1 (some arrangement of signs), is zero. -/
def good (x : Fin 4 → ℕ) : Prop :=
  ∃ s ∈ ({1, -1} : Finset ℤ), ∃ t ∈ ({1, -1} : Finset ℤ),
    s * (topgap (x 0) (x 1) (x 2) : ℤ) + t * (topgap (x 1) (x 2) (x 3) : ℤ) = 0

instance : DecidablePred good := fun x => by unfold good; infer_instance

/-- A251936(n): the number of 0..n arrays x(0..3) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 4 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the g.f. and the recurrence. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 5 =
      X * (10 - 7 * X + 5 * X ^ 2 - 5 * X ^ 3 + X ^ 4) ∧
    (∀ n : ℕ, 5 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5)) := by
  sorry

end OMA.S_oeis_a251936
