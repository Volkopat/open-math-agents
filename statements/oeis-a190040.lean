import Mathlib

/-!
# A190040: Number of nondecreasing arrangements of n+2 numbers in 0..8 with the last equal to 8 and each after the second equal to the sum of one or two of the preceding three.

Source: https://oeis.org/A190040
Credit: @ivillar

Status: corrected recurrence (n >= 11): fails as stated at n = 8. The entry records, as
conjectures of Colin Barker (May 04 2018):
* G.f.: x*(13 - 28*x + 22*x^2 - 3*x^3 + 2*x^4 - 2*x^5 - 6*x^7 + x^8 + 3*x^9) / (1 - x)^4.
* a(n) = 4*a(n-1) - 6*a(n-2) + 4*a(n-3) - a(n-4) for n>6.
With the listed terms a(4..8) = 65, 105, 164, 246, 349 the recurrence gives
4*246 - 6*164 + 4*105 - 65 = 355 for a(8), not 349; it also fails at n = 9 (471, not 472) and
n = 10 (614, not 617), and holds at n = 7. The g.f., whose numerator has degree 9, is equivalent
to the recurrence for n >= 11 together with the first ten terms. This file states the corrected
recurrence, for every n >= 11.

Formalization notes:
* Offset 1, as in the entry (data: 13, 24, 40, 65, 105, 164, 246, 349, ...).
* An arrangement of n+2 numbers in 0..8 is a map `x : Fin (n + 2) → Fin 9` (positions
  0, ..., n+1); nondecreasing means `Monotone x`, and the last term is `x (Fin.last (n + 1)) = 8`.
* "Each after the second equal to the sum of one or two of the preceding three": for every
  position `i ≥ 2`, the term `x i` equals one term `x j`, or the sum `x j + x k` of two terms
  (`j < k`, two different positions), taken among the at most three positions just before `i`
  (`j < i ≤ j + 3`). This reading reproduces the data: exhaustive enumeration gives
  13, 24, 40, 65, 105, 164, 246, 349, 472, 617, ... for n = 1, 2, 3, ...
* The recurrence is stated in `ℤ`, for n > 10.
-/

namespace OMA.S_oeis_a190040

/-- Each term after the second is one of, or the sum of two of, the (at most three) terms just
before it. -/
def Rule {L : ℕ} (x : Fin L → Fin 9) : Prop :=
  ∀ i : Fin L, 2 ≤ (i : ℕ) →
    (∃ j : Fin L, j < i ∧ (i : ℕ) ≤ j + 3 ∧ x j = x i) ∨
    (∃ j k : Fin L, j < k ∧ k < i ∧ (i : ℕ) ≤ j + 3 ∧ (x j : ℕ) + x k = x i)

/-- A190040(n): the number of nondecreasing arrangements of n+2 numbers in 0..8 ending with 8
in which each term after the second is the sum of one or two of the preceding three. -/
noncomputable def a (n : ℕ) : ℕ := by
  classical
  exact Fintype.card
    {x : Fin (n + 2) → Fin 9 // Monotone x ∧ x (Fin.last (n + 1)) = 8 ∧ Rule x}

/-- The corrected recurrence (n >= 11): `a(n) = 4a(n-1) - 6a(n-2) + 4a(n-3) - a(n-4)` for
`n > 10` (Barker states it for `n > 6`, but it fails at `n = 8, 9, 10`). -/
theorem main : ∀ n : ℕ, 10 < n →
    (a n : ℤ) = 4 * a (n - 1) - 6 * a (n - 2) + 4 * a (n - 3) - a (n - 4) := by
  sorry

end OMA.S_oeis_a190040
