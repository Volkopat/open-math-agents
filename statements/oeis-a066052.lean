import Mathlib

/-!
# OEIS A066052: permutations of order at least 3, two conjectured recurrences

Source: https://oeis.org/A066052
`a n` is the number of permutations in `S_n` with order `≥ 3`. Conjectures (Mathar, 2017):
1. `(-n+3) a(n) + (n² - 2n - 1) a(n-1) + (-n+1) a(n-2) - (n-1)(n-2)² a(n-3) = 0`;
2. `a(n) + (-n-3) a(n-1) + (2n-1) a(n-2) + n(n-2) a(n-3) - 2(n-2)(n-3) a(n-4) = 0`.
`main` is their conjunction, for `n ≥ 3` and `n ≥ 4` respectively (all indices nonnegative).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a066052

/-- Permutations of `Fin n` of order at least `3`. -/
noncomputable def a (n : ℕ) : ℕ := (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => 3 ≤ orderOf σ).card

theorem main :
    (∀ n : ℕ, 3 ≤ n →
      (-(n : ℤ) + 3) * a n + ((n : ℤ) ^ 2 - 2 * n - 1) * a (n - 1) + (-(n : ℤ) + 1) * a (n - 2) -
        ((n : ℤ) - 1) * ((n : ℤ) - 2) ^ 2 * a (n - 3) = 0) ∧
    (∀ n : ℕ, 4 ≤ n →
      (a n : ℤ) + (-(n : ℤ) - 3) * a (n - 1) + (2 * n - 1) * a (n - 2) +
        n * ((n : ℤ) - 2) * a (n - 3) - 2 * ((n : ℤ) - 2) * ((n : ℤ) - 3) * a (n - 4) = 0) := by
  sorry

end OMA.S_oeis_a066052
