import Mathlib

/-!
# Conjugation of irreducible {0,1}-matrices by an orthogonal matrix

Source: https://mathoverflow.net/questions/336842
Credit: @ivillar

Let $A_1$ and $A_2$ be irreducible matrices with entries in $\{0,1\}$. Let $S$ be an orthogonal
matrix such that $A_1 = S A_2 S^T$. Is it necessarily the case that $S$ is a permutation matrix?

Formalization notes:
* Matrices are real `n × n` matrices indexed by `Fin n`.
* A nonnegative square matrix is irreducible when for all `i, j` some positive power of it has a
  positive `(i, j)` entry (equivalently, its directed graph is strongly connected).
* `S` is orthogonal: `S * Sᵀ = 1`.
* `S` is a permutation matrix when `S i j = if σ i = j then 1 else 0` for a permutation `σ`.
* `main` is the affirmative answer to the question.
-/

namespace OMA.S_mo_336842

/-- Irreducibility of a nonnegative square matrix: every entry is positive in some positive
power. -/
def IsIrreducible {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∀ i j, ∃ k : ℕ, 0 < k ∧ 0 < (A ^ k) i j

/-- `S` is the permutation matrix of some permutation. -/
def IsPermMatrix {n : ℕ} (S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin n), ∀ i j, S i j = if σ i = j then 1 else 0

theorem main : ∀ (n : ℕ) (A₁ A₂ S : Matrix (Fin n) (Fin n) ℝ),
    (∀ i j, A₁ i j = 0 ∨ A₁ i j = 1) → (∀ i j, A₂ i j = 0 ∨ A₂ i j = 1) →
    IsIrreducible A₁ → IsIrreducible A₂ →
    S * S.transpose = 1 → A₁ = S * A₂ * S.transpose → IsPermMatrix S := by
  sorry

end OMA.S_mo_336842
