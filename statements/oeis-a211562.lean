import Mathlib

/-!
# OEIS A211562: Barker's g.f. and recurrence for restricted growth arrays of length n+2

Source: https://oeis.org/A211562 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @ceejcake.

Entry (R. H. Hardin, Apr 15 2012), offset 1: Number of nonnegative integer arrays of length n+2
with new values 0 upwards introduced in order, and containing the value n-1. The formula section
states: Conjectures from Colin Barker, Jul 19 2018: (Start) G.f.: x*(5 - 11*x + 16*x^2 - 9*x^3 +
2*x^4) / (1 - x)^5. a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5. (End)

Formalization notes:
* An array `x` of length `L` introduces new values 0 upwards in order when every value smaller
  than an entry `x i` already occurs at some position before `i`. Equivalently `x 0 = 0` and each
  entry is at most one more than the largest earlier entry.
* Such an array has `x i ≤ i`, so all its entries are below `L`. The arrays of length `n + 2` are
  therefore taken as functions `Fin (n + 2) → Fin (n + 2)`, which loses none of them.
* `main` is the conjunction of both conjectures. The g.f. is the series Sum_{n >= 1} a(n) x^n; the
  identity A(x) = N(x)/D(x) is stated as A(x)*D(x) = N(x) in Q[[x]], which is equivalent because
  D has constant term 1.
* Controls: the definitions give a(1..4) = 5, 14, 36, 81, as in the entry.
-/

namespace OMA.S_oeis_a211562

/-- The array `x` introduces new values 0 upwards in order: every value smaller than an entry
`x i` occurs at some earlier position `j < i`. -/
def NewValuesInOrder {L : ℕ} (x : Fin L → ℕ) : Prop :=
  ∀ i : Fin L, ∀ v < x i, ∃ j < i, x j = v

instance {L : ℕ} (x : Fin L → ℕ) : Decidable (NewValuesInOrder x) := by
  unfold NewValuesInOrder; infer_instance

/-- A211562 (offset 1): the number of arrays of length `n + 2` that introduce new values
0 upwards in order and contain the value `n - 1`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin (n + 2) → Fin (n + 2) =>
    NewValuesInOrder (fun i => (x i : ℕ)) ∧ ∃ i, (x i : ℕ) = n - 1)).card

open PowerSeries in
/-- Barker's conjectures: the g.f., and the order-5 linear recurrence for n > 5. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (5 - 11 * X + 16 * X ^ 2 - 9 * X ^ 3 + 2 * X ^ 4) ∧
    ∀ n : ℕ, 5 < n →
      (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a211562
