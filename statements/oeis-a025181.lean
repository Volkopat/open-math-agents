import Mathlib

/-!
# Two recurrences for OEIS A025181

Source: https://oeis.org/A025181
Credit: @hermitokatt

The sequence (offset 3): a(n) is the number of sequences `(s(0), …, s(n))` of integers with `s(0) = 0`, `|s(1)| = 1`, `|s(i) - s(i-1)| ≤ 1` for `i ≥ 2`, and `s(n) = 3`.
Data: 1, 3, 11, 35, 111, 343, ….

The entry records two conjectures (R. J. Mathar, Feb 25 2015):
1. `(n+3) a(n) + (-5n-7) a(n-1) + (3n-7) a(n-2) + (11n-7) a(n-3) + 4(-n+6) a(n-4) + 6(-n+5) a(n-5) = 0`;
2. `-(n+3)(n-3)(4n^2-12n+17) a(n) + (n-1)(8n^3-20n^2+30n-81) a(n-1) + 3(n-1)(n-2)(4n^2-4n+9) a(n-2) = 0`.
`main` states both.

Reading.
* The values `s(i)` are arbitrary integers (no nonnegativity condition), as in the source.
* `|s(1)| = 1` is `|s(1) - s(0)| = 1`, since `s(0) = 0`.
* Each recurrence is stated for every `n` for which all its terms are defined: `n ≥ 8` for the first and `n ≥ 5` for the second (the offset is 3);
  checked numerically against a direct count for `n ≤ 39`, and the count reproduces the
  listed data.
* A sequence `(s(0), …, s(n))` is a function `Fin (n + 1) → ℤ`; the set of admissible ones is
  finite (each `s(i)` is within distance `i` of `s(0)`), so `Set.ncard` is its number of elements.
* Terms and coefficients are in `ℤ`.
-/

namespace OMA.S_oeis_a025181

/-- The admissible sequences `(s(0), …, s(n))`. -/
def walks (n : ℕ) : Set (Fin (n + 1) → ℤ) :=
  {s | (∀ i : Fin (n + 1), i.val = 0 → s i = 0) ∧
       (∀ i : Fin (n + 1), i.val = n → s i = 3) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → j.val ≤ 1 → |s j - s i| = 1) ∧
       (∀ i j : Fin (n + 1), j.val = i.val + 1 → 1 < j.val → |s j - s i| ≤ 1)}

/-- A025181: the number of admissible sequences. -/
noncomputable def a (n : ℕ) : ℤ := ((walks n).ncard : ℤ)

/-- Both of Mathar's conjectured recurrences. -/
theorem main :
    (∀ n : ℕ, 8 ≤ n →
      ((n : ℤ) + 3) * a n + (-5 * (n : ℤ) - 7) * a (n - 1) + (3 * (n : ℤ) - 7) * a (n - 2) +
        (11 * (n : ℤ) - 7) * a (n - 3) + 4 * (-(n : ℤ) + 6) * a (n - 4) + 6 * (-(n : ℤ) + 5) * a (n - 5) = 0) ∧
    (∀ n : ℕ, 5 ≤ n →
      -((n : ℤ) + 3) * ((n : ℤ) - 3) * (4 * (n : ℤ) ^ 2 - 12 * (n : ℤ) + 17) * a n +
        ((n : ℤ) - 1) * (8 * (n : ℤ) ^ 3 - 20 * (n : ℤ) ^ 2 + 30 * (n : ℤ) - 81) * a (n - 1) +
        3 * ((n : ℤ) - 1) * ((n : ℤ) - 2) * (4 * (n : ℤ) ^ 2 - 4 * (n : ℤ) + 9) * a (n - 2) = 0) := by
  sorry

end OMA.S_oeis_a025181
