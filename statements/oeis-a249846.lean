import Mathlib

/-!
# OEIS A249846: Barker's recurrence and generating function

Source: https://oeis.org/A249846 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 07 2014), offset 1: Number of length 2+4 0..n arrays with no five
consecutive terms having the maximum of any two terms equal to the minimum of the remaining three
terms. Data: 10, 198, 1500, 6916, 23526, 65226, 156184, 335016, 659682, 1213102, ... The formula
section states: Empirical: a(n) = n^6 + (9/5)*n^5 + 3*n^4 + 3*n^3 + n^2 + (1/5)*n. Conjectures from
Colin Barker, Aug 18 2017: (Start) G.f.: 2*x*(5 + 64*x + 162*x^2 + 112*x^3 + 17*x^4) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7. (End)

Formalization notes:
* An array is a function x : Fin 6 → Fin (n + 1), the array x(0..5) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`. The instance only makes `good` decidable, so
  that `a n` is a computable count.
* `split5` says that the maximum of some 2 of its 5 arguments equals the minimum of the other 3,
  written as one disjunct for each of the 10 choices of the 2 terms; `good x` forbids it for each of
  the 2 windows of 5 consecutive terms, x(s..s+4) for s = 0..1.
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^7 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..26), all the entry's listed terms.
-/

namespace OMA.S_oeis_a249846

open PowerSeries

/-- The maximum of some two of the five terms a, b, c, d, e equals the minimum of the other three:
one disjunct for each of the 10 choices of the two terms. -/
def split5 (a b c d e : ℕ) : Prop :=
  max a b = min (min c d) e ∨ max a c = min (min b d) e ∨ max a d = min (min b c) e ∨ max a e = min
    (min b c) d ∨ max b c = min (min a d) e ∨ max b d = min (min a c) e ∨ max b e = min (min a c) d ∨
    max c d = min (min a b) e ∨ max c e = min (min a b) d ∨ max d e = min (min a b) c

/-- Neither window x(0..4) nor x(1..5) has two terms whose maximum equals the minimum of the
remaining three. -/
def good (x : Fin 6 → ℕ) : Prop :=
  ¬ split5 (x 0) (x 1) (x 2) (x 3) (x 4) ∧
    ¬ split5 (x 1) (x 2) (x 3) (x 4) (x 5)

instance : DecidablePred good := fun x => by unfold good split5; infer_instance

/-- A249846(n): the number of 0..n arrays x(0..5) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 6 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      2 * X * (5 + 64 * X + 162 * X ^ 2 + 112 * X ^ 3 + 17 * X ^ 4) := by
  sorry

end OMA.S_oeis_a249846
