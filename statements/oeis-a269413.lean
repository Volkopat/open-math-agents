import Mathlib

/-!
# OEIS A269413: Barker's recurrence and generating function

Source: https://oeis.org/A269413 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Feb 25 2016), offset 1: Number of length-7 0..n arrays with no repeated value
greater than or equal to the previous repeated value. Data: 20, 957, 10132, 56890, 223320, 695135,
1837752, 4302612, 9168780, 18124865, ... The formula section states: Empirical: a(n) = n^7 + 7*n^6 +
11*n^5 + (8/3)*n^4 - (11/6)*n^3 + (1/3)*n^2 - (1/6)*n. Conjectures from Colin Barker, Jan 21 2019:
(Start) G.f.: x*(20 + 797*x + 3036*x^2 + 1510*x^3 - 296*x^4 - 27*x^5) / (1 - x)^8. a(n) = 8*a(n-1) -
28*a(n-2) + 56*a(n-3) - 70*a(n-4) + 56*a(n-5) - 28*a(n-6) + 8*a(n-7) - a(n-8) for n>8. (End)

Formalization notes:
* An array is a function x : Fin 7 → Fin (n + 1), the array x(0..6) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`. The instance only makes `good` decidable, so
  that `a n` is a computable count.
* A repeated value is an entry equal to the entry before it; `repsL` lists them in order (a run of
  three equal entries gives the value twice). `good x` says that each repeated value is strictly
  smaller than the previous one, that is, no repeated value is greater than or equal to the previous
  repeated value. This reading reproduces the entry's data and the rows of the table A269409 by
  brute force.
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^8 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..23), all the entry's listed terms.
-/

namespace OMA.S_oeis_a269413

open PowerSeries

/-- The repeated values of a list: every entry equal to the entry before it, in order. -/
def repsL {α : Type*} [DecidableEq α] : List α → List α
  | a :: b :: t => if a = b then b :: repsL (b :: t) else repsL (b :: t)
  | _ => []

/-- No repeated value of x(0..6) is greater than or equal to the previous repeated value:
the repeated values strictly decrease. -/
def good (x : Fin 7 → ℕ) : Prop := (repsL (List.ofFn x)).IsChain (· > ·)

instance : DecidablePred good := fun x => by unfold good; infer_instance

/-- A269413(n): the number of 0..n arrays x(0..6) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 7 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 8 < n →
      (a n : ℤ) = 8 * a (n - 1) - 28 * a (n - 2) + 56 * a (n - 3) - 70 * a (n - 4) + 56 * a (n - 5) - 28 * a (n - 6) + 8 * a (n - 7) - a (n - 8)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 8 =
      X * (20 + 797 * X + 3036 * X ^ 2 + 1510 * X ^ 3 - 296 * X ^ 4 - 27 * X ^ 5) := by
  sorry

end OMA.S_oeis_a269413
