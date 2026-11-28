import Mathlib

/-!
# OEIS A211564: Barker's g.f. and recurrence for restricted growth arrays of length n+4

Source: https://oeis.org/A211564 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @ceejcake.

Entry (R. H. Hardin, Apr 15 2012), offset 1: Number of nonnegative integer arrays of length n+4
with new values 0 upwards introduced in order, and containing the value n-1. The formula section
states: Conjectures from Colin Barker, Jul 19 2018: (Start) G.f.: x*(52 - 266*x + 867*x^2 -
1367*x^3 + 1534*x^4 - 1097*x^5 + 497*x^6 - 130*x^7 + 15*x^8) / (1 - x)^9. a(n) = 9*a(n-1) -
36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9)
for n>9. (End)

Formalization notes:
* An array `x` of length `L` introduces new values 0 upwards in order when every value smaller
  than an entry `x i` already occurs at some position before `i`. Equivalently `x 0 = 0` and each
  entry is at most one more than the largest earlier entry.
* Such an array has `x i ≤ i`, so all its entries are below `L`. The arrays of length `n + 4` are
  therefore taken as functions `Fin (n + 4) → Fin (n + 4)`, which loses none of them.
* `main` is the conjunction of both conjectures. The g.f. is the series Sum_{n >= 1} a(n) x^n; the
  identity A(x) = N(x)/D(x) is stated as A(x)*D(x) = N(x) in Q[[x]], which is equivalent because
  D has constant term 1.
* Controls: the definitions give a(1..3) = 52, 202, 813, as in the entry.
-/

namespace OMA.S_oeis_a211564

/-- The array `x` introduces new values 0 upwards in order: every value smaller than an entry
`x i` occurs at some earlier position `j < i`. -/
def NewValuesInOrder {L : ℕ} (x : Fin L → ℕ) : Prop :=
  ∀ i : Fin L, ∀ v < x i, ∃ j < i, x j = v

instance {L : ℕ} (x : Fin L → ℕ) : Decidable (NewValuesInOrder x) := by
  unfold NewValuesInOrder; infer_instance

/-- A211564 (offset 1): the number of arrays of length `n + 4` that introduce new values
0 upwards in order and contain the value `n - 1`. -/
def a (n : ℕ) : ℕ :=
  (Finset.univ.filter (fun x : Fin (n + 4) → Fin (n + 4) =>
    NewValuesInOrder (fun i => (x i : ℕ)) ∧ ∃ i, (x i : ℕ) = n - 1)).card

open PowerSeries in
/-- Barker's conjectures: the g.f., and the order-9 linear recurrence for n > 9. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (52 - 266 * X + 867 * X ^ 2 - 1367 * X ^ 3 + 1534 * X ^ 4 - 1097 * X ^ 5 +
        497 * X ^ 6 - 130 * X ^ 7 + 15 * X ^ 8) ∧
    ∀ n : ℕ, 9 < n →
      (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) +
        126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a211564
