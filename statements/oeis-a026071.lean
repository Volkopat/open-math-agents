import Mathlib

/-!
# A recurrence for OEIS A026071

Source: https://oeis.org/A026071
Credit: @hermitokatt

The sequence (offset 4): a(n) is the number of sequences `(s(0), …, s(n))` of integers with `s(0) = 0`, `|s(i) - s(i-1)| = 1` for `i = 1, 2`, `|s(i) - s(i-1)| ≤ 1` for `i ≥ 3`, and `s(n) = 4`.
Data: 1, 3, 12, 40, 133, 427, ….

The conjecture (R. J. Mathar, Jun 22 2013):
`-(n-4)(n+4) a(n) + (4n+7)(n-4) a(n-1) + (-2n^2+23n-12) a(n-2) - (4n+3)(n-4) a(n-3) + 3(n-4)(n-5) a(n-4) = 0`.

Reading.
* The values `s(i)` are arbitrary integers (no nonnegativity condition), as in the source.
* Each recurrence is stated for every `n` for which all its terms are defined: `n ≥ 8` (the offset is 4);
  checked numerically against a direct count for `n ≤ 39`, and the count reproduces the
  listed data.
* A sequence `(s(0), …, s(n))` is a function `Fin (n + 1) → ℤ`; the set of admissible ones is
  finite (each `s(i)` is within distance `i` of `s(0)`), so `Set.ncard` is its number of elements.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a026071

/-- The admissible sequences `(s(0), …, s(n))`. -/
def walks (n : ℕ) : Set (Fin (n + 1) → ℤ) :=
  {s | (∀ i : Fin (n + 1), i.val = 0 → s i = 0) ∧
       (∀ i : Fin (n + 1), i.val = n → s i = 4) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → j.val ≤ 2 → |s j - s i| = 1) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → 2 < j.val → |s j - s i| ≤ 1)}

/-- A026071: the number of admissible sequences. -/
noncomputable def a (n : ℕ) : ℤ := ((walks n).ncard : ℤ)

/-- Mathar's conjectured recurrence, for all `n ≥ 8`. -/
theorem main : ∀ n : ℕ, 8 ≤ n →
    -((n : ℤ) - 4) * ((n : ℤ) + 4) * a n + (4 * (n : ℤ) + 7) * ((n : ℤ) - 4) * a (n - 1) +
      (-2 * (n : ℤ) ^ 2 + 23 * (n : ℤ) - 12) * a (n - 2) - (4 * (n : ℤ) + 3) * ((n : ℤ) - 4) * a (n - 3) +
      3 * ((n : ℤ) - 4) * ((n : ℤ) - 5) * a (n - 4) = 0 := by
  sorry

end OMA.S_oeis_a026071
