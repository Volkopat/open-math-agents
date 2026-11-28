import Mathlib

/-!
# OEIS A268263: Barker's recurrence and generating function

Source: https://oeis.org/A268263 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Jan 29 2016), offset 1: Number of length-(4+1) 0..n arrays with new repeated
values introduced in sequential order starting with zero. Data: 17, 106, 479, 1610, 4357, 10082,
20771, 39154, 68825, 114362, ... The formula section states: Empirical: a(n) = n^5 + n^4 + 4*n^3 +
3*n^2 + 6*n + 2. Conjectures from Colin Barker, Jan 13 2019: (Start) G.f.: x*(17 + 4*x + 98*x^2 -
14*x^3 + 17*x^4 - 2*x^5) / (1 - x)^6. a(n) = 6*a(n-1) - 15*a(n-2) + 20*a(n-3) - 15*a(n-4) +
6*a(n-5) - a(n-6) for n>6. (End)

Formalization notes:
* An array is a function x : Fin 5 → Fin (n + 1), the array x(0..4) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`.
* A repeated value is an entry equal to the entry before it; `repsL` lists them in order. New
  repeated values are introduced in sequential order starting with zero when the first repeated
  value is 0 and each repeated value not seen before is the number of distinct repeated values
  before it, that is, each repeated value is at most the number of values introduced before it
  (`rgsB 0`). This reading reproduces the entry's data and the examples by brute force.
* The recurrence is stated in the integers, for n > 6 as in the entry; the g.f. is A(x) = Sum_{n >=
  1} a(n) x^n (offset 1), stated as A(x) (1 - x)^6 = N(x) in Z[[x]], which is equivalent because 1 -
  x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..12), the entry's first terms.
-/

namespace OMA.S_oeis_a268263

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

/-- The new repeated values of x(0..4) are introduced in sequential order starting with
zero. -/
def good (x : Fin 5 → ℕ) : Prop := rgsB 0 (repsL (List.ofFn x)) = true

instance : DecidablePred good := fun x => by unfold good; infer_instance

/-- A268263(n): the number of 0..n arrays x(0..4) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 5 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 6 < n →
      (a n : ℤ) = 6 * a (n - 1) - 15 * a (n - 2) + 20 * a (n - 3) - 15 * a (n - 4) + 6 * a (n - 5) - a (n - 6)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 6 =
      X * (17 + 4 * X + 98 * X ^ 2 - 14 * X ^ 3 + 17 * X ^ 4 - 2 * X ^ 5) := by
  sorry

end OMA.S_oeis_a268263
