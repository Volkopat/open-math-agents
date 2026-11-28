import Mathlib

/-!
# OEIS A250145: Barker's recurrence and generating function

Source: https://oeis.org/A250145 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry (R. H. Hardin, Nov 13 2014), offset 1: Number of length 6+2 0..n arrays with the medians of
every three consecutive terms nondecreasing. Data: 111, 2026, 16104, 81664, 311498, 974944, 2637228,
6376143, 14100493, 28998090, ... The formula section states: Empirical: a(n) = (1/12)*n^8 +
(1487/1260)*n^7 + (4757/720)*n^6 + (13757/720)*n^5 + (4519/144)*n^4 + (21611/720)*n^3 +
(2957/180)*n^2 + (2183/420)*n + 1. Conjectures from Colin Barker, Nov 11 2018: (Start) G.f.:
x*(111 + 1027*x + 1866*x^2 + 340*x^3 + 68*x^4 - 80*x^5 + 36*x^6 - 9*x^7 + x^8) / (1 - x)^9. a(n) =
9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) +
a(n-9) for n>10. (End)

Formalization notes:
* An array is a function x : Fin 8 → Fin (n + 1), the array x(0..7) with entries in 0..n; `a n`
  counts those whose values `(x i : ℕ)` satisfy `good`. The instance only makes `good` decidable, so
  that `a n` is a computable count.
* `med a b c` is the median of a, b, c (the middle value after sorting), written as max (min a b)
  (min (max a b) c); `good x` says that the medians of the consecutive triples x(i), x(i+1), x(i+2)
  are nondecreasing in i, i = 0..5.
* The recurrence is stated in the integers; the g.f. is A(x) = Sum_{n >= 1} a(n) x^n (offset 1),
  stated as A(x) (1 - x)^9 = N(x) in Z[[x]], which is equivalent because 1 - x is a unit.
* `main` is the conjunction of Barker's two conjectures.
* Controls proved in the proof file: a(1..23), all the entry's listed terms.
-/

namespace OMA.S_oeis_a250145

open PowerSeries

/-- The median of three numbers. -/
def med (a b c : ℕ) : ℕ := max (min a b) (min (max a b) c)

/-- The medians of the consecutive triples of x(0..7) are nondecreasing. -/
def good (x : Fin 8 → ℕ) : Prop :=
  med (x 0) (x 1) (x 2) ≤ med (x 1) (x 2) (x 3) ∧
    med (x 1) (x 2) (x 3) ≤ med (x 2) (x 3) (x 4) ∧
    med (x 2) (x 3) (x 4) ≤ med (x 3) (x 4) (x 5) ∧
    med (x 3) (x 4) (x 5) ≤ med (x 4) (x 5) (x 6) ∧
    med (x 4) (x 5) (x 6) ≤ med (x 5) (x 6) (x 7)

instance : DecidablePred good := fun x => by unfold good; infer_instance

/-- A250145(n): the number of 0..n arrays x(0..7) with property `good`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin 8 → Fin (n + 1) => good (fun i => (x i : ℕ)))).card

/-- Barker's conjectures: the recurrence and the g.f. -/
theorem main :
    (∀ n : ℕ, 10 < n →
      (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9)) ∧
    PowerSeries.mk (fun n => if n = 0 then (0 : ℤ) else a n) * (1 - X) ^ 9 =
      X * (111 + 1027 * X + 1866 * X ^ 2 + 340 * X ^ 3 + 68 * X ^ 4 - 80 * X ^ 5 + 36 * X ^ 6 - 9 * X ^ 7 + X ^ 8) := by
  sorry

end OMA.S_oeis_a250145
