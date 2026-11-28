import Mathlib

/-!
# A recurrence for OEIS A026125

Source: https://oeis.org/A026125
Credit: @hermitokatt

The sequence (offset 3): a(n) is the number of sequences `(s(0), …, s(n))` of nonnegative integers with `s(0) = 1`, `s(n) = 4`, `|s(1) - s(0)| = 1`, and `|s(i) - s(i-1)| ≤ 1` for `i ≥ 2`.
Data: 1, 3, 11, 35, 110, 336, ….

The conjecture (R. J. Mathar, Jun 23 2013):
`-(n+7)(n-3) a(n) + (4n+17)(n-3) a(n-1) + (-2n^2+13n+27) a(n-2) - (4n+5)(n-3) a(n-3) + 3(n-3)(n-4) a(n-4) = 0`.

Reading.
* Each recurrence is stated for every `n` for which all its terms are defined: `n ≥ 7` (the offset is 3);
  checked numerically against a direct count for `n ≤ 39`, and the count reproduces the
  listed data.
* A sequence `(s(0), …, s(n))` is a function `Fin (n + 1) → ℕ`; the set of admissible ones is
  finite (each `s(i)` is within distance `i` of `s(0)`), so `Set.ncard` is its number of elements.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a026125

/-- The admissible sequences `(s(0), …, s(n))`. -/
def walks (n : ℕ) : Set (Fin (n + 1) → ℕ) :=
  {s | (∀ i : Fin (n + 1), i.val = 0 → s i = 1) ∧
       (∀ i : Fin (n + 1), i.val = n → s i = 4) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → j.val ≤ 1 → |(s j : ℤ) - (s i : ℤ)| = 1) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → 1 < j.val → |(s j : ℤ) - (s i : ℤ)| ≤ 1)}

/-- A026125: the number of admissible sequences. -/
noncomputable def a (n : ℕ) : ℤ := ((walks n).ncard : ℤ)

/-- Mathar's conjectured recurrence, for all `n ≥ 7`. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    -((n : ℤ) + 7) * ((n : ℤ) - 3) * a n + (4 * (n : ℤ) + 17) * ((n : ℤ) - 3) * a (n - 1) +
      (-2 * (n : ℤ) ^ 2 + 13 * (n : ℤ) + 27) * a (n - 2) - (4 * (n : ℤ) + 5) * ((n : ℤ) - 3) * a (n - 3) +
      3 * ((n : ℤ) - 3) * ((n : ℤ) - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026125
