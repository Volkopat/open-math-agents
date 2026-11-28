import Mathlib

/-!
# OEIS A211853: Barker's conjectures for nonnegative integer arrays of length 2n+8 with new values 0 upwards introduced in order, no three adjacent elements all unequal, and containing the value n+1

Source: https://oeis.org/A211853 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A211853 (R. H. Hardin, Apr 22 2012), offset 1: Number of nonnegative integer arrays of length 2n+8 with new values 0 upwards introduced in order, no three adjacent elements all unequal, and containing the value n+1.
Formula section:
Empirical: a(n) = (499/720)*n^6 + (2587/240)*n^5 + (10031/144)*n^4 + (11681/48)*n^3 + (179153/360)*n^2 + (8788/15)*n + 323.
Conjectures from Colin Barker, Jul 20 2018: (Start)
G.f.: x*(1731 - 5181*x + 9696*x^2 - 10295*x^3 + 6435*x^4 - 2210*x^5 + 323*x^6) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
(End)

Formalization notes:
* An array of length 2n+8 is a map x : Fin (2 * n + 8) -> ℕ. It introduces its new values 0
  upwards in order when every entry is 0 or at most one more than an earlier entry (`newInOrder`);
  such an array has entries below its length, so x is a map Fin (2 * n + 8) -> Fin (2 * n + 8)
  without loss.
* No three adjacent elements are all unequal: there is no i with x(i), x(i+1), x(i+2) pairwise
  different (`noAllDiff`). The array contains the value n+1 when some entry equals n+1.
* This reading reproduces every listed term of the table A211849 (of which the entry is row 7)
  with length at most 11, checked by direct enumeration.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^7 = (the entry's numerator) in the formal power series ring over the
  rationals; and the recurrence, for every n > 7, as an identity of integers.
* The definition reproduces the entry's data (1731, 6936, 21897, 57913, 134164, 280751, ... from
  n = 1), checked by direct enumeration through the prefix recursion, itself checked against all
  arrays of length at most 10. Controls proved in the proof file: all 25 listed terms, a(1) to
  a(25).
-/

namespace OMA.S_oeis_a211853

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
def good {n : ℕ} (x : Fin (2 * n + 8) → Fin (2 * n + 8)) : Prop :=
  newInOrder x ∧ noAllDiff x ∧ ∃ i, (x i : ℕ) = n + 1

instance {n : ℕ} : DecidablePred (@good n) := fun x => by
  unfold good newInOrder noAllDiff; infer_instance

/-- A211853: number of nonnegative integer arrays of length 2n+8 with new values 0 upwards introduced in order, no three adjacent elements all unequal, and containing the value n+1. The entries of
such an array are below its length, so it is a map Fin (2 * n + 8) → Fin (2 * n + 8). -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin (2 * n + 8) → Fin (2 * n + 8))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (1731 - 5181 * X + 9696 * X ^ 2 - 10295 * X ^ 3 + 6435 * X ^ 4 - 2210 * X ^ 5 + 323 * X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a211853
