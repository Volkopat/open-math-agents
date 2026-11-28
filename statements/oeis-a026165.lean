import Mathlib

/-!
# A recurrence for OEIS A026165

Source: https://oeis.org/A026165
Credit: @hermitokatt

The sequence (offset 0): a(n) is the number of sequences `(s(0), s(1), …, s(n))` of nonnegative integers with `s(0) = 2`, `|s(1) - s(0)| = 1` and `|s(i) - s(i-1)| ≤ 1` for `i ≥ 2` (no condition on `s(n)`).
Data: 1, 2, 6, 17, 49, 141, 407, ….

The conjecture (R. J. Mathar, Jun 23 2013):
`(n+3) a(n) + (-5n-9) a(n-1) + (5n+1) a(n-2) + 5(n-1) a(n-3) + 6(-n+3) a(n-4) = 0`.

Reading.
* The recurrence is stated for every `n` for which all its terms are defined, i.e. `n ≥ 4`
  (the offset is 0); checked numerically against a direct count for `4 ≤ n ≤ 39`, and the
  count reproduces the listed data.
* A sequence `(s(0), …)` is a function on `Fin` positions; the set of admissible ones is finite
  (each value is within distance `i` of `s(0)`), so `Set.ncard` is its number of elements.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a026165

/-- Sequences `(s(0), …, s(n))` of naturals: start `2`, first step `±1`, later steps in `{-1, 0, 1}`. -/
def walks (n : ℕ) : Set (Fin (n + 1) → ℕ) :=
  {s | (∀ i : Fin (n + 1), i.val = 0 → s i = 2) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → j.val ≤ 1 → |(s j : ℤ) - (s i : ℤ)| = 1) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → 1 < j.val → |(s j : ℤ) - (s i : ℤ)| ≤ 1)}

/-- A026165: the number of admissible sequences. -/
noncomputable def a (n : ℕ) : ℤ := ((walks n).ncard : ℤ)

/-- Mathar's conjectured recurrence, for all `n ≥ 4`. -/
theorem main : ∀ n : ℕ, 4 ≤ n →
    ((n : ℤ) + 3) * a n + (-5 * (n : ℤ) - 9) * a (n - 1) + (5 * (n : ℤ) + 1) * a (n - 2) +
      5 * ((n : ℤ) - 1) * a (n - 3) + 6 * (-(n : ℤ) + 3) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026165
