import Mathlib

/-!
# OEIS A211850: Barker's conjectures for nonnegative integer arrays of length 2n+5 with new values 0 upwards introduced in order, no three adjacent elements all unequal, and containing the value n+1

Source: https://oeis.org/A211850 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A211850 (R. H. Hardin, Apr 22 2012), offset 1: Number of nonnegative integer arrays of length 2n+5 with new values 0 upwards introduced in order, no three adjacent elements all unequal, and containing the value n+1.
Formula section:
Empirical: a(n) = (7/3)*n^3 + (27/2)*n^2 + (163/6)*n + 20.
Conjectures from Colin Barker, Jul 20 2018: (Start)
G.f.: x*(63 - 105*x + 76*x^2 - 20*x^3) / (1 - x)^4.
a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>4.
(End)

Formalization notes:
* An array of length 2n+5 is a map x : Fin (2 * n + 5) -> ℕ. It introduces its new values 0
  upwards in order when every entry is 0 or at most one more than an earlier entry (`newInOrder`);
  such an array has entries below its length, so x is a map Fin (2 * n + 5) -> Fin (2 * n + 5)
  without loss.
* No three adjacent elements are all unequal: there is no i with x(i), x(i+1), x(i+2) pairwise
  different (`noAllDiff`). The array contains the value n+1 when some entry equals n+1.
* This reading reproduces every listed term of the table A211849 (of which the entry is row 4)
  with length at most 11, checked by direct enumeration.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem, Barker's conjectures:
  the g.f., as the identity A(x) (1 - x)^4 = (the entry's numerator) in the formal power series
  ring over the rationals; and the recurrence, for every n > 4, as an identity of integers.
* The definition reproduces the entry's data (63, 147, 286, 494, 785, 1173, ... from n = 1),
  checked by direct enumeration through the prefix recursion, itself checked against all arrays of
  length at most 10. Controls proved in the proof file: all 38 listed terms, a(1) to a(38).
-/

namespace OMA.S_oeis_a211850

open PowerSeries Finset

/-- Every entry of x is 0 or at most one more than an earlier entry, so the new values of x appear
in the order 0, 1, 2, ... -/
def newInOrder {L N : ℕ} (x : Fin L → Fin N) : Prop :=
  ∀ i : Fin L, (x i : ℕ) = 0 ∨ ∃ j : Fin L, j < i ∧ (x i : ℕ) ≤ x j + 1

/-- No three adjacent entries of x are all different. -/
def noAllDiff {L N : ℕ} (x : Fin L → Fin N) : Prop :=
  ∀ i : Fin L, ∀ h : (i : ℕ) + 2 < L,
    ¬ (x i ≠ x ⟨i + 1, by omega⟩ ∧ x ⟨i + 1, by omega⟩ ≠ x ⟨i + 2, h⟩ ∧ x i ≠ x ⟨i + 2, h⟩)

/-- x introduces its values in order, has no three adjacent entries all different, and contains
n + 1. -/
def good {n : ℕ} (x : Fin (2 * n + 5) → Fin (2 * n + 5)) : Prop :=
  newInOrder x ∧ noAllDiff x ∧ ∃ i, (x i : ℕ) = n + 1

instance {n : ℕ} : DecidablePred (@good n) := fun x => by
  unfold good newInOrder noAllDiff; infer_instance

/-- A211850: number of nonnegative integer arrays of length 2n+5 with new values 0 upwards introduced in order, no three adjacent elements all unequal, and containing the value n+1. The entries of
such an array are below its length, so it is a map Fin (2 * n + 5) → Fin (2 * n + 5). -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin (2 * n + 5) → Fin (2 * n + 5))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 4 =
      X * (63 - 105 * X + 76 * X ^ 2 - 20 * X ^ 3) ∧
    ∀ n : ℕ, 4 < n → (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a211850
