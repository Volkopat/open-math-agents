import Mathlib

/-!
# OEIS A211837: Barker's conjectures for nonnegative integer arrays of length n+4 with new values 0 upwards introduced in order, no three adjacent elements equal, and containing the value n+1

Source: https://oeis.org/A211837 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A211837 (R. H. Hardin, Apr 21 2012), offset 1: Number of nonnegative integer arrays of length n+4 with new values 0 upwards introduced in order, no three adjacent elements equal, and containing the value n+1.
Formula section:
Empirical: a(n) = (1/8)*n^4 + (17/12)*n^3 + (51/8)*n^2 + (157/12)*n + 12.
Conjectures from Colin Barker, Jul 20 2018: (Start)
G.f.: x*(33 - 88*x + 102*x^2 - 56*x^3 + 12*x^4) / (1 - x)^5.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.
(End)

Formalization notes:
* An array of length n+4 is a map x : Fin (n + 4) -> ℕ. It introduces its new values 0 upwards in
  order when every entry is 0 or at most one more than an earlier entry (`newInOrder`); such an
  array has entries below its length, so x is a map Fin (n + 4) -> Fin (n + 4) without loss.
* No three adjacent elements are equal: there is no i with x(i) = x(i+1) = x(i+2) (`noThree`). The
  array contains the value n+1 when some entry equals n+1.
* This reading reproduces every listed term of the table A211836 (of which the entry is row 3)
  with length at most 11, checked by direct enumeration.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^5 = (the entry's numerator) in the formal power series ring over the
  rationals; and the recurrence, for every n > 5, as an identity of integers.
* The definition reproduces the entry's data (33, 77, 157, 289, 492, 788, ... from n = 1, checked
  by direct enumeration for n <= 5 and against every listed term through the formula of the
  proof).
-/

namespace OMA.S_oeis_a211837

open PowerSeries Finset

/-- Every entry of x is 0 or at most one more than an earlier entry, so the new values of x appear
in the order 0, 1, 2, ... -/
def newInOrder {L N : ℕ} (x : Fin L → Fin N) : Prop :=
  ∀ i : Fin L, (x i : ℕ) = 0 ∨ ∃ j : Fin L, j < i ∧ (x i : ℕ) ≤ x j + 1

/-- No three adjacent entries of x are equal. -/
def noThree {L N : ℕ} (x : Fin L → Fin N) : Prop :=
  ∀ i : Fin L, ∀ h : (i : ℕ) + 2 < L,
    ¬ (x i = x ⟨i + 1, by omega⟩ ∧ x ⟨i + 1, by omega⟩ = x ⟨i + 2, h⟩)

/-- x introduces its values in order, has no three adjacent equal entries, and contains n + 1. -/
def good {n : ℕ} (x : Fin (n + 4) → Fin (n + 4)) : Prop :=
  newInOrder x ∧ noThree x ∧ ∃ i, (x i : ℕ) = n + 1

instance {n : ℕ} : DecidablePred (@good n) := fun x => by
  unfold good newInOrder noThree; infer_instance

/-- A211837: number of nonnegative integer arrays of length n+4 with new values 0 upwards introduced in order, no three adjacent elements equal, and containing the value n+1. The entries of
such an array are below its length, so it is a map Fin (n + 4) → Fin (n + 4). -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin (n + 4) → Fin (n + 4))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (33 - 88 * X + 102 * X ^ 2 - 56 * X ^ 3 + 12 * X ^ 4) ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a211837
