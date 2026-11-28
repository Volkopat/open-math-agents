import Mathlib

/-!
# OEIS A268264: Barker's recurrence and generating function

Source: https://oeis.org/A268264 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 29 2016), offset 1: Number of length-(5+1) 0..n arrays with new repeated
values introduced in sequential order starting with zero. Data: 33, 273, 1616, 6877, 22710, 62249,
148468, 318261, 627242, 1155265, ... The formula section states: Empirical: a(n) = n^6 + n^5 +
5*n^4 + 4*n^3 + 12*n^2 + 6*n + 5 for n>1. Conjectures from Colin Barker, Jan 13 2019: (Start) G.f.:
x*(33 + 42*x + 398*x^2 + 143*x^3 + 107*x^4 - 2*x^5 - 2*x^6 + x^7) / (1 - x)^7. a(n) = 7*a(n-1) -
21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>8. (End)

Formalization notes:
* An array is a function x : Fin 6 → Fin (n + 1), the array x(0..5) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`.
* A repeated value is an entry equal to the entry before it; `repsL` lists them in order. New
  repeated values are introduced in sequential order starting with zero when the first repeated
  value is 0 and each repeated value not seen before is the number of distinct repeated values
  before it, that is, each repeated value is at most the number of values introduced before it
  (`rgsB 0`). This reading reproduces the entry's data and the examples by brute force.
* The recurrence is stated in the integers, for n > 8 as in the entry; the g.f. is A(x) = Sum_{n >=
  1} a(n) x^n (offset 1), stated as A(x) (1 - x)^7 = N(x) in Z[[x]], which is equivalent because 1 -
  x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..12), the entry's first terms.
-/

namespace OMA.S_oeis_a268264

open PowerSeries

/-- The repeated values of a list: every entry equal to the entry before it, in order. -/
def repsL {α : Type*} [DecidableEq α] : List α → List α
  | a :: b :: t => if a = b then b :: repsL (b :: t) else repsL (b :: t)
  | _ => []

/-- rgsB m l: reading l in order, new values are introduced in sequential order after the m
values 0, ..., m - 1: each value is at most the number of values introduced before it. -/
def rgsB : ℕ → List ℕ → Bool
  | _, [] => true
  | m, v :: t => decide (v ≤ m) && rgsB (max m (v + 1)) t

/-- The new repeated values of x(0..5) are introduced in sequential order starting with
zero. -/
def good (x : Fin 6 → ℕ) : Prop := rgsB 0 (repsL (List.ofFn x)) = true

instance : DecidablePred good := fun x => by unfold good; infer_instance

/-- A268264(n): the number of 0..n arrays x(0..5) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 6 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      X * (33 + 42 * X + 398 * X ^ 2 + 143 * X ^ 3 + 107 * X ^ 4 - 2 * X ^ 5 - 2 * X ^ 6 + X ^ 7) := by
  sorry

end OMA.S_oeis_a268264
