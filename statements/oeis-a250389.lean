import Mathlib

/-!
# OEIS A250389: Barker's recurrence and generating function

Source: https://oeis.org/A250389 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 20 2014), offset 1: Number of length 3+3 0..n arrays with no four
consecutive terms having the maximum of any two terms equal to the minimum of the remaining two
terms. Data: 6, 146, 1208, 5848, 20518, 58114, 141344, 306816, 609846, 1129986, ... The formula
section states: Empirical: a(n) = n^6 + (16/15)*n^5 + (13/6)*n^4 + (5/3)*n^3 - (1/6)*n^2 + (4/15)*n.
Conjectures from Colin Barker, Aug 21 2017: (Start) G.f.: 2*x*(3 + 52*x + 156*x^2 + 124*x^3 +
25*x^4) / (1 - x)^7. a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) +
a(n-7) for n>7. (End)

Formalization notes:
* An array is a function x : Fin 6 → Fin (n + 1), the array x(0..5) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`. The instance only makes `good` decidable, so
  that `a n` is a computable count.
* `split4` says that the maximum of some 2 of its 4 arguments equals the minimum of the other 2,
  written as one disjunct for each of the 6 choices of the 2 terms; `good x` forbids it for each of
  the 3 windows of 4 consecutive terms, x(s..s+3) for s = 0..2.
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^7 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..26), all the entry's listed terms.
-/

namespace OMA.S_oeis_a250389

open PowerSeries

/-- The maximum of some two of the four terms a, b, c, d equals the minimum of the other two: one
disjunct for each of the 6 choices of the two terms. -/
def split4 (a b c d : ℕ) : Prop :=
  max a b = min c d ∨ max a c = min b d ∨ max a d = min b c ∨ max b c = min a d ∨ max b d = min a c ∨
    max c d = min a b

/-- None of the windows x(0..3), x(1..4) and x(2..5) has two terms whose maximum equals the minimum
of the remaining two. -/
def good (x : Fin 6 → ℕ) : Prop :=
  ¬ split4 (x 0) (x 1) (x 2) (x 3) ∧
    ¬ split4 (x 1) (x 2) (x 3) (x 4) ∧
    ¬ split4 (x 2) (x 3) (x 4) (x 5)

instance : DecidablePred good := fun x => by unfold good split4; infer_instance

/-- A250389(n): the number of 0..n arrays x(0..5) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 6 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      2 * X * (3 + 52 * X + 156 * X ^ 2 + 124 * X ^ 3 + 25 * X ^ 4) := by
  sorry

end OMA.S_oeis_a250389
