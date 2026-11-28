import Mathlib

/-!
# Numerical radius of an entrywise positive matrix

Source: https://mathoverflow.net/questions/219012
Asked by MathOverflow user dineshdileep.

Let `A` be a (real, square) matrix all of whose entries are positive, and let
`W(A) = {x^H A x : x^H x = 1}` be its numerical range, where `x` runs over complex vectors.
The question asks whether
`max_{x^H x = 1} |x^H A x| = max_{u^T u = 1, u > 0} u^T A u`,
where `u > 0` means that all entries of the real vector `u` are positive.

Translation choices.
* `A : Matrix (Fin n) (Fin n) ℝ` with `0 < A i j` for all `i, j`; a complex unit vector is
  `x : Fin n → ℂ` with `∑ i, ‖x i‖ ^ 2 = 1`, and `x^H A x = ∑ i, ∑ j, conj (x i) * A i j * x j`.
* The two maxima are written as suprema (`sSup`) of the corresponding sets of real numbers;
  `main` states that these suprema are equal. (Both are in fact attained, but attainment is
  not part of the statement.) For `n = 0` both sets are empty.
-/

namespace OMA.S_mo_219012

theorem main :
    ∀ n : ℕ, ∀ A : Matrix (Fin n) (Fin n) ℝ, (∀ i j, 0 < A i j) →
      sSup {r : ℝ | ∃ x : Fin n → ℂ, ∑ i, ‖x i‖ ^ 2 = 1 ∧
          r = ‖∑ i, ∑ j, star (x i) * (A i j : ℂ) * x j‖} =
        sSup {r : ℝ | ∃ u : Fin n → ℝ, ∑ i, u i ^ 2 = 1 ∧ (∀ i, 0 < u i) ∧
          r = ∑ i, ∑ j, u i * A i j * u j} := by
  sorry

end OMA.S_mo_219012
