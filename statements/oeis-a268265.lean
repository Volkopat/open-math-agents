import Mathlib

/-!
# OEIS A268265: Barker's recurrence and generating function

Source: https://oeis.org/A268265 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 29 2016), offset 1: Number of length-(6+1) 0..n arrays with new repeated
values introduced in sequential order starting with zero. Data: 65, 717, 5492, 29461, 118530,
384605, 1061632, 2587557, 5717246, 11671405, ... The formula section states: Empirical: a(n) = n^7 +
n^6 + 6*n^5 + 5*n^4 + 20*n^3 + 12*n^2 + 20*n + 5 for n>1. Conjectures from Colin Barker, Jan 13
2019: (Start) G.f.: x*(65 + 197*x + 1576*x^2 + 1961*x^3 + 1016*x^4 + 271*x^5 - 76*x^6 + 35*x^7 -
5*x^8) / (1 - x)^8. a(n) = 8*a(n-1) - 28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) +
8*a(n-7) - a(n-8) for n>9. (End)

Formalization notes:
* An array is a function x : Fin 7 → Fin (n + 1), the array x(0..6) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`.
* A repeated value is an entry equal to the entry before it; `repsL` lists them in order. New
  repeated values are introduced in sequential order starting with zero when the first repeated
  value is 0 and each repeated value not seen before is the number of distinct repeated values
  before it, that is, each repeated value is at most the number of values introduced before it
  (`rgsB 0`). This reading reproduces the entry's data and the examples by brute force.
* The recurrence is stated in the integers, for n > 9 as in the entry; the g.f. is A(x) = Sum_{n >=
  1} a(n) x^n (offset 1), stated as A(x) (1 - x)^8 = N(x) in Z[[x]], which is equivalent because 1 -
  x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..12), the entry's first terms.
-/

namespace OMA.S_oeis_a268265

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

/-- The new repeated values of x(0..6) are introduced in sequential order starting with
zero. -/
def good (x : Fin 7 → ℕ) : Prop := rgsB 0 (repsL (List.ofFn x)) = true

instance : DecidablePred good := fun x => by unfold good; infer_instance

/-- A268265(n): the number of 0..n arrays x(0..6) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 7 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 9 < n →
      (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      X * (65 + 197 * X + 1576 * X ^ 2 + 1961 * X ^ 3 + 1016 * X ^ 4 + 271 * X ^ 5 - 76 * X ^ 6 + 35 * X ^ 7 - 5 * X ^ 8) := by
  sorry

end OMA.S_oeis_a268265
