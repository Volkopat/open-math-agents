import Mathlib

/-!
# OEIS A211851: Barker's conjectures for nonnegative integer arrays of length 2n+6 with new values 0 upwards introduced in order, no three adjacent elements all unequal, and containing the value n+1

Source: https://oeis.org/A211851 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A211851 (R. H. Hardin, Apr 22 2012), offset 1: Number of nonnegative integer arrays of length 2n+6 with new values 0 upwards introduced in order, no three adjacent elements all unequal, and containing the value n+1.
Formula section:
Empirical: a(n) = (43/24)*n^4 + (185/12)*n^3 + (1217/24)*n^2 + (937/12)*n + 50.
Conjectures from Colin Barker, Jul 20 2018: (Start)
G.f.: x*(196 - 419*x + 457*x^2 - 241*x^3 + 50*x^4) / (1 - x)^5.
a(n) = 5*a(n-1) - 10*a(n-2) + 10*a(n-3) - 5*a(n-4) + a(n-5) for n>5.
(End)

Formalization notes:
* An array of length 2n+6 is a map x : Fin (2 * n + 6) -> ℕ. It introduces its new values 0
  upwards in order when every entry is 0 or at most one more than an earlier entry (`newInOrder`);
  such an array has entries below its length, so x is a map Fin (2 * n + 6) -> Fin (2 * n + 6)
  without loss.
* No three adjacent elements are all unequal: there is no i with x(i), x(i+1), x(i+2) pairwise
  different (`noAllDiff`). The array contains the value n+1 when some entry equals n+1.
* This reading reproduces every listed term of the table A211849 (of which the entry is row 5)
  with length at most 11, checked by direct enumeration.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem, Barker's conjectures:
  the g.f., as the identity A(x) (1 - x)^5 = (the entry's numerator) in the formal power series
  ring over the rationals; and the recurrence, for every n > 5, as an identity of integers.
* The definition reproduces the entry's data (196, 561, 1302, 2619, 4755, 7996, ... from n = 1),
  checked by direct enumeration through the prefix recursion, itself checked against all arrays of
  length at most 10. Controls proved in the proof file: all 32 listed terms, a(1) to a(32).
-/

namespace OMA.S_oeis_a211851

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
def good {n : ℕ} (x : Fin (2 * n + 6) → Fin (2 * n + 6)) : Prop :=
  newInOrder x ∧ noAllDiff x ∧ ∃ i, (x i : ℕ) = n + 1

instance {n : ℕ} : DecidablePred (@good n) := fun x => by
  unfold good newInOrder noAllDiff; infer_instance

/-- A211851: number of nonnegative integer arrays of length 2n+6 with new values 0 upwards introduced in order, no three adjacent elements all unequal, and containing the value n+1. The entries of
such an array are below its length, so it is a map Fin (2 * n + 6) → Fin (2 * n + 6). -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin (2 * n + 6) → Fin (2 * n + 6))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 5 =
      X * (196 - 419 * X + 457 * X ^ 2 - 241 * X ^ 3 + 50 * X ^ 4) ∧
    ∀ n : ℕ, 5 < n → (a n : ℤ) = 5 * a (n - 1) - 10 * a (n - 2) + 10 * a (n - 3) - 5 * a (n - 4) + a (n - 5) := by
  sorry

end OMA.S_oeis_a211851
