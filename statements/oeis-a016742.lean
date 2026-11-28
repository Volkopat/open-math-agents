import Mathlib

/-!
# OEIS A016742: regular Hadamard matrices exist exactly in even-square orders

Source: https://oeis.org/A016742
`A016742` lists the even squares `4m²`. Comment on the entry: it is conjectured that a regular
Hadamard matrix of order `n` exists iff `n` is an even square (cf. Seberry–Yamada,
Th. 10.11). A Hadamard matrix is regular if all its row and column sums are equal.

Conventions. A Hadamard matrix of order `n ≥ 1` is an `n × n` matrix with entries `±1` and
`H Hᵀ = n I`. The trivial order `1` (the matrix `(1)`, which is regular) is excluded, so `n ≥ 2`.

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_oeis_a016742

open Matrix

/-- `H` is a regular Hadamard matrix. -/
def IsRegularHadamard {n : ℕ} (H : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  (∀ i j, H i j = 1 ∨ H i j = -1) ∧ H * Hᵀ = (n : ℤ) • (1 : Matrix (Fin n) (Fin n) ℤ) ∧
    ∃ s : ℤ, (∀ i, ∑ j, H i j = s) ∧ ∀ j, ∑ i, H i j = s

theorem main :
    ∀ n : ℕ, 2 ≤ n →
      ((∃ H : Matrix (Fin n) (Fin n) ℤ, IsRegularHadamard H) ↔ ∃ m : ℕ, n = (2 * m) ^ 2) := by
  sorry

end OMA.S_oeis_a016742
