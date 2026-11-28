import Mathlib

/-!
# A recurrence for OEIS A026084

Source: https://oeis.org/A026084
Credit: @hermitokatt

The sequence (offset 4): a(n) is the number of sequences `(s(0), s(1), …, s(n))` of integers with `s(0) = 0`, `|s(i) - s(i-1)| = 1` for `i = 1, 2, 3`, `|s(i) - s(i-1)| ≤ 1` for `i ≥ 4`, and `s(n) = 1`.
Data: 3, 13, 33, 98, 278, 804, ….

The conjecture (R. J. Mathar, Jun 23 2013):
`(n+1) a(n) + 3(-n+1) a(n-1) + (-n-9) a(n-2) + 3(n-5) a(n-3) = 0`.

Reading.
* The values `s(i)` are arbitrary integers (no nonnegativity condition), as in the source.
* The recurrence is stated for every `n` for which all its terms are defined, i.e. `n ≥ 7`
  (the offset is 4); checked numerically against a direct count for `7 ≤ n ≤ 39`, and the
  count reproduces the listed data.
* A sequence `(s(0), …)` is a function on `Fin` positions; the set of admissible ones is finite
  (each value is within distance `i` of `s(0)`), so `Set.ncard` is its number of elements.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a026084

/-- Integer sequences `(s(0), …, s(n))`: start `0`, end `1`, first three steps `±1`, later steps in `{-1, 0, 1}`. -/
def walks (n : ℕ) : Set (Fin (n + 1) → ℤ) :=
  {s | (∀ i : Fin (n + 1), i.val = 0 → s i = 0) ∧
       (∀ i : Fin (n + 1), i.val = n → s i = 1) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → j.val ≤ 3 → |s j - s i| = 1) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → 3 < j.val → |s j - s i| ≤ 1)}

/-- A026084: the number of admissible sequences. -/
noncomputable def a (n : ℕ) : ℤ := ((walks n).ncard : ℤ)

/-- Mathar's conjectured recurrence, for all `n ≥ 7`. -/
theorem main : ∀ n : ℕ, 7 ≤ n →
    ((n : ℤ) + 1) * a n + 3 * (-(n : ℤ) + 1) * a (n - 1) + (-(n : ℤ) - 9) * a (n - 2) +
      3 * ((n : ℤ) - 5) * a (n - 3) = 0 := by
  sorry

end OMA.S_oeis_a026084
