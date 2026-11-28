import Mathlib

/-!
# A recurrence for OEIS A026013

Source: https://oeis.org/A026013
Credit: @hermitokatt

The sequence (offset 1): a(n) is the number of sequences `(s(0), s(1), …, s(2n))` of nonnegative integers with `|s(i) - s(i-1)| = 1`, `s(0) = 2` and `s(2n) = 4`.
Data: 1, 4, 15, 55, 200, 726, ….

The conjecture (R. J. Mathar, Nov 13 2012):
`(n+4)(n+1) a(n) - 4(n^2+4n+6) a(n-1) + 4(2n-3) a(n-2) = 0`.

Reading.
* The OEIS name says the step condition holds "for i = 1,2,...,n". This is read as every step
  `i = 1, …, 2n`: with only the first `n` steps constrained the count would be infinite, and this
  reading reproduces the listed data.
* The recurrence is stated for every `n` for which all its terms are defined, i.e. `n ≥ 3`
  (the offset is 1); checked numerically against a direct count for `3 ≤ n ≤ 39`, and the
  count reproduces the listed data.
* A sequence `(s(0), …)` is a function on `Fin` positions; the set of admissible ones is finite
  (each value is within distance `i` of `s(0)`), so `Set.ncard` is its number of elements.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a026013

/-- Sequences `(s(0), …, s(2n))` of naturals: start `2`, end `4`, steps `±1`. -/
def walks (n : ℕ) : Set (Fin (2 * n + 1) → ℕ) :=
  {s | (∀ i : Fin (2 * n + 1), i.val = 0 → s i = 2) ∧
       (∀ i : Fin (2 * n + 1), i.val = 2 * n → s i = 4) ∧
       (∀ i j : Fin (2 * n + 1), j.val = i.val + 1 → |(s j : ℤ) - (s i : ℤ)| = 1)}

/-- A026013: the number of admissible sequences. -/
noncomputable def a (n : ℕ) : ℤ := ((walks n).ncard : ℤ)

/-- Mathar's conjectured recurrence, for all `n ≥ 3`. -/
theorem main : ∀ n : ℕ, 3 ≤ n →
    ((n : ℤ) + 4) * ((n : ℤ) + 1) * a n - 4 * ((n : ℤ) ^ 2 + 4 * (n : ℤ) + 6) * a (n - 1) +
      4 * (2 * (n : ℤ) - 3) * a (n - 2) = 0 := by
  sorry

end OMA.S_oeis_a026013
