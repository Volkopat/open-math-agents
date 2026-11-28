import Mathlib

/-!
# OEIS A254700: Barker's recurrence and generating function

Source: https://oeis.org/A254700 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Feb 05 2015), offset 1: Number of length 2+4 0..n arrays with every five
consecutive terms having the maximum of some two terms equal to the minimum of the remaining three
terms. Data: 34, 267, 1116, 3341, 8142, 17255, 33048, 58617, 97882, 155683, ... The formula section
states: Empirical: a(n) = (4/5)*n^5 + (19/3)*n^4 + (34/3)*n^3 + (29/3)*n^2 + (73/15)*n + 1.
Conjectures from Colin Barker, Dec 17 2018: (Start) G.f.: x*(34 + 63*x + 24*x^2 - 30*x^3 + 6*x^4 -
x^5) / (1 - x)^6. a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) + 6*a(n-5) - a(n-6) for n>6.
(End)

Formalization notes:
* An array is a function x : Fin 6 → Fin (n + 1), the array x(0..5) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`. The instance only makes `good` decidable, so
  that `a n` is a computable count.
* `split5` says that the maximum of some 2 of its 5 arguments equals the minimum of the other 3,
  written as one disjunct for each of the 10 choices of the 2 terms; `good x` requires it for each
  of the 2 windows of 5 consecutive terms, x(s..s+4) for s = 0..1.
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^6 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..32), all the entry's listed terms.
-/

namespace OMA.S_oeis_a254700

open PowerSeries

/-- The maximum of some two of the five terms a, b, c, d, e equals the minimum of the other three:
one disjunct for each of the 10 choices of the two terms. -/
def split5 (a b c d e : ℕ) : Prop :=
  max a b = min (min c d) e ∨ max a c = min (min b d) e ∨ max a d = min (min b c) e ∨ max a e = min
    (min b c) d ∨ max b c = min (min a d) e ∨ max b d = min (min a c) e ∨ max b e = min (min a c) d ∨
    max c d = min (min a b) e ∨ max c e = min (min a b) d ∨ max d e = min (min a b) c

/-- Each of the windows x(0..4) and x(1..5) has two terms whose maximum equals the minimum of the
remaining three. -/
def good (x : Fin 6 → ℕ) : Prop :=
  split5 (x 0) (x 1) (x 2) (x 3) (x 4) ∧
    split5 (x 1) (x 2) (x 3) (x 4) (x 5)

instance : DecidablePred good := fun x => by unfold good split5; infer_instance

/-- A254700(n): the number of 0..n arrays x(0..5) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 6 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (34 + 63 * X + 24 * X ^ 2 - 30 * X ^ 3 + 6 * X ^ 4 - X ^ 5) := by
  sorry

end OMA.S_oeis_a254700
