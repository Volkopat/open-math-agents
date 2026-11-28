import Mathlib

/-!
# A recurrence for OEIS A026110

Source: https://oeis.org/A026110
Credit: @hermitokatt

The sequence (offset 4): a(n) is the number of sequences `(s(0), …, s(n))` of nonnegative integers with `s(0) = 0`, `s(1) = 1`, `s(n) = 4`, and `|s(i) - s(i-1)| ≤ 1` for `i ≥ 2`.
Data: 1, 4, 15, 50, 160, 496, ….

The conjecture (R. J. Mathar, Jun 23 2013):
`-(n+6)(n-4) a(n) + (4n^2-n-51) a(n-1) + (-2n^2+11n+18) a(n-2) - (4n-1)(n-3) a(n-3) + 3(n-3)(n-4) a(n-4) = 0`.

Reading.
* Each recurrence is stated for every `n` for which all its terms are defined: `n ≥ 8` (the offset is 4);
  checked numerically against a direct count for `n ≤ 39`, and the count reproduces the
  listed data.
* A sequence `(s(0), …, s(n))` is a function `Fin (n + 1) → ℕ`; the set of admissible ones is
  finite (each `s(i)` is within distance `i` of `s(0)`), so `Set.ncard` is its number of elements.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a026110

/-- The admissible sequences `(s(0), …, s(n))`. -/
def walks (n : ℕ) : Set (Fin (n + 1) → ℕ) :=
  {s | (∀ i : Fin (n + 1), i.val = 0 → s i = 0) ∧
       (∀ i : Fin (n + 1), i.val = n → s i = 4) ∧
       (∀ i : Fin (n + 1), i.val = 1 → s i = 1) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → 1 < j.val → |(s j : ℤ) - (s i : ℤ)| ≤ 1)}

/-- A026110: the number of admissible sequences. -/
noncomputable def a (n : ℕ) : ℤ := ((walks n).ncard : ℤ)

/-- Mathar's conjectured recurrence, for all `n ≥ 8`. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    -((n : ℤ) + 6) * ((n : ℤ) - 4) * a n + (4 * (n : ℤ) ^ 2 - (n : ℤ) - 51) * a (n - 1) +
      (-2 * (n : ℤ) ^ 2 + 11 * (n : ℤ) + 18) * a (n - 2) - (4 * (n : ℤ) - 1) * ((n : ℤ) - 3) * a (n - 3) +
      3 * ((n : ℤ) - 3) * ((n : ℤ) - 4) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026110
