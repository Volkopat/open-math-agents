import Mathlib

/-!
# Williamson conjecture

Source: https://en.wikipedia.org/wiki/Williamson_conjecture
Credit: @AkiRA-COM-FP

Formalizes the Williamson conjecture: for every positive integer `n`, there exist four
symmetric circulant `n x n` matrices `A, B, C, D` with entries in `{-1, 1}` satisfying
`A^2 + B^2 + C^2 + D^2 = 4n I_n`.
-/

namespace OMA.S_wp_williamson_conjecture

abbrev SqMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℤ

/-- A symmetric circulant matrix with entries in {-1, 1}. -/
def IsWilliamsonMatrix {n : ℕ} (M : SqMatrix n) : Prop :=
  (∀ i j, M i j = 1 ∨ M i j = -1) ∧
  Matrix.IsSymm M ∧
  (∃ v : Fin n → ℤ, M = Matrix.circulant v)

/-- Four such matrices satisfying the Williamson equation. -/
def HasWilliamson (n : ℕ) : Prop :=
  ∃ A B C D : SqMatrix n,
    IsWilliamsonMatrix A ∧
    IsWilliamsonMatrix B ∧
    IsWilliamsonMatrix C ∧
    IsWilliamsonMatrix D ∧
    A * A + B * B + C * C + D * D =
      (4 * (n : ℤ)) • (1 : SqMatrix n)

/-- The original Williamson conjecture: Williamson matrices exist for every positive order `n`. -/
theorem main : ∀ n : ℕ, 0 < n → HasWilliamson n := by sorry

end OMA.S_wp_williamson_conjecture
