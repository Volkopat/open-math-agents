import Mathlib

/-!
# OEIS A269412: Barker's recurrence and generating function

Source: https://oeis.org/A269412 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Feb 25 2016), offset 1: Number of length-6 0..n arrays with no repeated value
greater than or equal to the previous repeated value. Data: 16, 394, 2872, 12380, 39560, 104006,
238224, 492312, 939360, 1681570, ... The formula section states: Empirical: a(n) = n^6 + 6*n^5 +
8*n^4 + (5/3)*n^3 - n^2 + (1/3)*n. Conjectures from Colin Barker, Jan 21 2019: (Start) G.f.:
2*x*(8 + 141*x + 225*x^2 - 5*x^3 - 9*x^4) / (1 - x)^7. a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) -
35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7. (End)

Formalization notes:
* An array is a function x : Fin 6 → Fin (n + 1), the array x(0..5) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`. The instance only makes `good` decidable, so
  that `a n` is a computable count.
* A repeated value is an entry equal to the entry before it; `repsL` lists them in order (a run of
  three equal entries gives the value twice). `good x` says that each repeated value is strictly
  smaller than the previous one, that is, no repeated value is greater than or equal to the previous
  repeated value. This reading reproduces the entry's data and the rows of the table A269409 by
  brute force.
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^7 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..26), all the entry's listed terms.
-/

namespace OMA.S_oeis_a269412

open PowerSeries

/-- The repeated values of a list: every entry equal to the entry before it, in order. -/
def repsL {α : Type*} [DecidableEq α] : List α → List α
  | a :: b :: t => if a = b then b :: repsL (b :: t) else repsL (b :: t)
  | _ => []

/-- No repeated value of x(0..5) is greater than or equal to the previous repeated value:
the repeated values strictly decrease. -/
def good (x : Fin 6 → ℕ) : Prop := (repsL (List.ofFn x)).IsChain (· > ·)

instance : DecidablePred good := fun x => by unfold good; infer_instance

/-- A269412(n): the number of 0..n arrays x(0..5) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 6 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 7 =
      2 * X * (8 + 141 * X + 225 * X ^ 2 - 5 * X ^ 3 - 9 * X ^ 4) := by
  sorry

end OMA.S_oeis_a269412
