import Mathlib

/-!
# OEIS A211839: Barker's conjectures for nonnegative integer arrays of length n+6 with new values 0 upwards introduced in order, no three adjacent elements equal, and containing the value n+1

Source: https://oeis.org/A211839 (OEIS Foundation, CC BY-SA 4.0).
Formalization: AI-generated with Claude Code (model claude-opus-5-5), submitted by @jleguina.

Entry A211839 (R. H. Hardin, Apr 21 2012), offset 1: Number of nonnegative integer arrays of length n+6 with new values 0 upwards introduced in order, no three adjacent elements equal, and containing the value n+1.
Formula section:
Empirical: a(n) = (1/384)*n^8 + (7/96)*n^7 + (515/576)*n^6 + (499/80)*n^5 + (31603/1152)*n^4 + (7763/96)*n^3 + (47569/288)*n^2 + (8973/40)*n + 159.
Conjectures from Colin Barker, Jul 20 2018: (Start)
G.f.: x*(664 - 3355*x + 9383*x^2 - 15720*x^3 + 16980*x^4 - 11983*x^5 + 5367*x^6 - 1390*x^7 + 159*x^8) / (1 - x)^9.
a(n) = 9*a(n-1) - 36*a(n-2) + 84*a(n-3) - 126*a(n-4) + 126*a(n-5) - 84*a(n-6) + 36*a(n-7) - 9*a(n-8) + a(n-9) for n>9.
(End)

Formalization notes:
* An array of length n+6 is a map x : Fin (n + 6) -> ℕ. It introduces its new values 0 upwards in
  order when every entry is 0 or at most one more than an earlier entry (`newInOrder`); such an
  array has entries below its length, so x is a map Fin (n + 6) -> Fin (n + 6) without loss.
* No three adjacent elements are equal: there is no i with x(i) = x(i+1) = x(i+2) (`noThree`). The
  array contains the value n+1 when some entry equals n+1.
* This reading reproduces every listed term of the table A211836 (of which the entry is row 5)
  with length at most 11, checked by direct enumeration.
* a(n) is defined for every n; the entry starts at n = 1, so the g.f. is stated with
  A(x) = Sum_{n >= 1} a(n) x^n.
* The statement is the conjunction of the two parts of the site's problem: the g.f., as the
  identity A(x) (1 - x)^9 = (the entry's numerator) in the formal power series ring over the
  rationals; and the recurrence, for every n > 9, as an identity of integers.
* The definition reproduces the entry's data (664, 2621, 9068, 27312, 72840, 175475, ... from
  n = 1, checked by direct enumeration for n <= 5 and against every listed term through the
  formula of the proof).
-/

namespace OMA.S_oeis_a211839

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
def good {n : ℕ} (x : Fin (n + 6) → Fin (n + 6)) : Prop :=
  newInOrder x ∧ noThree x ∧ ∃ i, (x i : ℕ) = n + 1

instance {n : ℕ} : DecidablePred (@good n) := fun x => by
  unfold good newInOrder noThree; infer_instance

/-- A211839: number of nonnegative integer arrays of length n+6 with new values 0 upwards introduced in order, no three adjacent elements equal, and containing the value n+1. The entries of
such an array are below its length, so it is a map Fin (n + 6) → Fin (n + 6). -/
def a (n : ℕ) : ℕ := ((univ : Finset (Fin (n + 6) → Fin (n + 6))).filter good).card

/-- Barker's conjectures. -/
theorem main :
    PowerSeries.mk (fun n => if n = 0 then (0 : ℚ) else (a n : ℚ)) * (1 - X) ^ 9 =
      X * (664 - 3355 * X + 9383 * X ^ 2 - 15720 * X ^ 3 + 16980 * X ^ 4 - 11983 * X ^ 5 + 5367 * X ^ 6 - 1390 * X ^ 7 + 159 * X ^ 8) ∧
    ∀ n : ℕ, 9 < n → (a n : ℤ) = 9 * a (n - 1) - 36 * a (n - 2) + 84 * a (n - 3) - 126 * a (n - 4) + 126 * a (n - 5) - 84 * a (n - 6) + 36 * a (n - 7) - 9 * a (n - 8) + a (n - 9) := by
  sorry

end OMA.S_oeis_a211839
