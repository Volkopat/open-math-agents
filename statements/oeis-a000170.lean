import Mathlib

/-!
# OEIS A000170: number of ways to place `n` nonattacking queens on an `n × n` board

Source: https://oeis.org/A000170
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

Conjecture (Benoit Cloitre, "strong conjecture" in the OEIS entry): there is a constant `c`
(around `2.54`) such that `a(n) ~ n! / c^n`. Stated as: there is `c > 0` with
`a(n) / (n! / c^n) → 1`.

`a(n)` counts permutations `σ` of `Fin n` (queen in row `i` at column `σ i`) with no two
queens on a common diagonal: `|σ i - σ j| ≠ |i - j|` for `i ≠ j`.
-/

namespace OMA.S_oeis_a000170

open Filter

/-- Placements of `n` nonattacking queens. -/
noncomputable def a (n : ℕ) : ℕ :=
  Nat.card {σ : Equiv.Perm (Fin n) //
    ∀ i j : Fin n, i ≠ j → |((σ i : ℕ) : ℤ) - (σ j : ℕ)| ≠ |((i : ℕ) : ℤ) - (j : ℕ)|}

/-- Cloitre's strong conjecture. -/
theorem main :
    ∃ c : ℝ, 0 < c ∧
      Tendsto (fun n : ℕ => (a n : ℝ) / ((n.factorial : ℝ) / c ^ n)) atTop (nhds 1) := by
  sorry

end OMA.S_oeis_a000170
