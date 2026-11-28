import Mathlib

/-!
# A recurrence for OEIS A026018

Source: https://oeis.org/A026018
Credit: @hermitokatt

The sequence (offset 3): a(n) is the number of sequences `(s(0), s(1), …, s(2n-1))` of nonnegative
integers with `|s(i) - s(i-1)| = 1`, `s(0) = 2` and `s(2n-1) = 7`. Data: 1, 7, 36, 164, 702, ….

The conjecture (R. J. Mathar, Jun 20 2013):
`-(n+5)(3n-37) a(n) + 3(-n^2-84n-173) a(n-1) + 2(32n^2+295n+254) a(n-2) - 8(n+25)(2n-5) a(n-3) = 0`.

Reading.
* The OEIS name says the step condition holds "for i = 1,2,...,n". This is read as
  `i = 1, …, 2n-1`, i.e. every consecutive pair: with only the first `n` steps constrained the
  count would be infinite, and this reading reproduces the listed data (checked for n = 3..44).
* The recurrence is stated for every `n` for which all four terms are defined, i.e. `n ≥ 6`
  (the offset is 3, and `a(n-3)` appears).
* The terms and coefficients are viewed in `ℤ` so that the negative coefficients are exact.
* A sequence `(s(0), …, s(2n-1))` is a function `Fin (2n) → ℕ`; the set of admissible ones is
  finite (all values are at most `2n + 1`), so `Set.ncard` is its number of elements.
-/

namespace OMA.S_oeis_a026018

/-- The admissible sequences of length `2n`: start at `2`, end at `7`, steps of `±1`. -/
def walks (n : ℕ) : Set (Fin (2 * n) → ℕ) :=
  {s | (∀ i : Fin (2 * n), i.val = 0 → s i = 2) ∧
       (∀ i : Fin (2 * n), i.val = 2 * n - 1 → s i = 7) ∧
       (∀ i j : Fin (2 * n), j.val = i.val + 1 → |(s j : ℤ) - (s i : ℤ)| = 1)}

/-- A026018: the number of admissible sequences. -/
noncomputable def a (n : ℕ) : ℤ := ((walks n).ncard : ℤ)

/-- Mathar's conjectured recurrence, for all `n ≥ 6`. -/
theorem main : ∀ n : ℕ, 6 ≤ n →
    -((n : ℤ) + 5) * (3 * (n : ℤ) - 37) * a n +
      3 * (-(n : ℤ) ^ 2 - 84 * (n : ℤ) - 173) * a (n - 1) +
      2 * (32 * (n : ℤ) ^ 2 + 295 * (n : ℤ) + 254) * a (n - 2) -
      8 * ((n : ℤ) + 25) * (2 * (n : ℤ) - 5) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a026018
