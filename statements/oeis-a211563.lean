import Mathlib

/-!
# OEIS A211563: Barker's g.f. and recurrence for restricted growth arrays of length n+3

Source: https://oeis.org/A211563 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @ceejcake.

Entry (R. H. Hardin, Apr 15 2012), offset 1: Number of nonnegative integer arrays of length n+3
with new values 0 upwards introduced in order, and containing the value n-1. The formula section
states: Conjectures from Colin Barker, Jul 19 2018: (Start) G.f.: x*(15 - 54*x + 129*x^2 -
139*x^3 + 92*x^4 - 33*x^5 + 5*x^6) / (1 - x)^7. a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) -
35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7. (End)

Formalization notes:
* An array `x` of length `L` introduces new values 0 upwards in order when every value smaller
  than an entry `x i` already occurs at some position before `i`. Equivalently `x 0 = 0` and each
  entry is at most one more than the largest earlier entry.
* Such an array has `x i ≤ i`, so all its entries are below `L`. The arrays of length `n + 3` are
  therefore taken as functions `Fin (n + 3) → Fin (n + 3)`, which loses none of them.
* `main` is the conjunction of both conjectures. The g.f. is the series Sum_{n >= 1} a(n) x^n; the
  identity A(x) = N(x)/D(x) is stated as A(x)*D(x) = N(x) in Q[[x]], which is equivalent because
  D has constant term 1.
* Controls: the definitions give a(1..3) = 15, 51, 171, as in the entry.
-/

namespace OMA.S_oeis_a211563

/-- The array `x` introduces new values 0 upwards in order: every value smaller than an entry
`x i` occurs at some earlier position `j < i`. -/
def NewValuesInOrder {L : ℕ} (x : Fin L → ℕ) : Prop :=
  ∀ i : Fin L, ∀ v < x i, ∃ j < i, x j = v

instance {L : ℕ} (x : Fin L → ℕ) : Decidable (NewValuesInOrder x) := by
  unfold NewValuesInOrder; infer_instance

/-- A211563 (offset 1): the number of arrays of length `n + 3` that introduce new values
0 upwards in order and contain the value `n - 1`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin (n + 3) → Fin (n + 3) =>
    NewValuesInOrder (fun i => (x i : ℕ)) ∧ ∃ i, (x i : ℕ) = n - 1)).card

open PowerSeries in
/-- Barker's conjectures: the g.f., and the order-7 linear recurrence for n > 7. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (15 - 54 * X + 129 * X ^ 2 - 139 * X ^ 3 + 92 * X ^ 4 - 33 * X ^ 5 + 5 * X ^ 6) ∧
    ∀ n : ℕ, 7 < n →
      (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) +
        21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a211563
