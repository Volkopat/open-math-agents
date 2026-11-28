import Mathlib

/-!
# OEIS A211838: Barker's conjectures for nonnegative integer arrays of length n+5 with new values 0 upwards introduced in order, no three adjacent elements equal, and containing the value n+1

Source: https://oeis.org/A211838 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A211838 (R. H. Hardin, Apr 21 2012), offset 1: Number of nonnegative integer arrays of length n+5 with new values 0 upwards introduced in order, no three adjacent elements equal, and containing the value n+1.
Formula section:
Empirical: a(n) = (1/48)*n^6 + (19/48)*n^5 + (51/16)*n^4 + (661/48)*n^3 + (835/24)*n^2 + (317/6)*n + 41.
Conjectures from Colin Barker, Jul 20 2018: (Start)
G.f.: x*(146 - 561*x + 1093*x^2 - 1210*x^3 + 781*x^4 - 275*x^5 + 41*x^6) / (1 - x)^7.
a(n) = 7*a(n-1) - 21*a(n-2) + 35*a(n-3) - 35*a(n-4) + 21*a(n-5) - 7*a(n-6) + a(n-7) for n>7.
(End)

Formalization notes:
* An array of length n+5 is a map x : Fin (n + 5) -> ℕ. It introduces its new values 0 upwards in
  order when every entry is 0 or at most one more than an earlier entry (`newInOrder`); such an
  array has entries below its length, so x is a map Fin (n + 5) -> Fin (n + 5) without loss.
* No three adjacent elements are equal: there is no i with x(i) = x(i+1) = x(i+2) (`noThree`). The
  array contains the value n+1 when some entry equals n+1.
* This reading reproduces every listed term of the table A211836 (of which the entry is row 4)
  with length at most 11, checked by direct enumeration.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^7 = (the entry's numerator) in the formal power series ring over the
  rationals; and the recurrence, for every n > 7, as an identity of integers.
* The definition reproduces the entry's data (146, 461, 1254, 2997, 6451, 12766, ... from n = 1,
  checked by direct enumeration for n <= 5 and against every listed term through the formula of
  the proof).
-/

namespace OMA.S_oeis_a211838

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
def good {n : ℕ} (x : Fin (n + 5) → Fin (n + 5)) : Prop :=
  newInOrder x ∧ noThree x ∧ ∃ i, (x i : ℕ) = n + 1

instance {n : ℕ} : DecidablePred (@good n) := fun x => by
  unfold good newInOrder noThree; infer_instance

/-- A211838: number of nonnegative integer arrays of length n+5 with new values 0 upwards introduced in order, no three adjacent elements equal, and containing the value n+1. The entries of
such an array are below its length, so it is a map Fin (n + 5) → Fin (n + 5). -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin (n + 5) → Fin (n + 5))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 7 =
      X * (146 - 561 * X + 1093 * X ^ 2 - 1210 * X ^ 3 + 781 * X ^ 4 - 275 * X ^ 5 + 41 * X ^ 6) ∧
    ∀ n : ℕ, 7 < n → (a n : ℤ) = 7 * a (n - 1) - 21 * a (n - 2) + 35 * a (n - 3) - 35 * a (n - 4) + 21 * a (n - 5) - 7 * a (n - 6) + a (n - 7) := by
  sorry

end OMA.S_oeis_a211838
