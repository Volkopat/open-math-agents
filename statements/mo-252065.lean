import Mathlib

/-!
# Dimensions of subspaces with a prescribed orthogonality pattern

Source: https://mathoverflow.net/questions/252065
Asked by MathOverflow user P_sharmit.

Let `S_1, ..., S_m` and `T_1, ..., T_n` be subspaces of `ℝ^k` of dimension at least one,
and let a binary `m × n` matrix `M` record their relative orthogonality: `M(i, j) = 0`
means `S_i ⟂ T_j`, and `M(i, j) = 1` means that `S_i` and `T_j` are not orthogonal.
For `k = 3` and
`M = [[1, 0, 0, 1], [1, 0, 1, 0], [0, 1, 0, 1], [0, 1, 1, 0]]`
the asker is pretty sure that `dim S_i = dim T_j = 1` for all `i, j`, but cannot prove it,
and asks for a proof (equivalently, whether `dim S_i ≤ k - 2` and `dim T_j ≤ k - 2`).

Translation choices.
* `ℝ^3` is `EuclideanSpace ℝ (Fin 3)`; indices run over `Fin 4`, row `i` of `M` belonging
  to `S i` and column `j` to `T j`.
* Orthogonality of subspaces is `Submodule.IsOrtho`.
* `main` states that under these hypotheses every `S i` and every `T j` has dimension one.
-/

namespace OMA.S_mo_252065

/-- The orthogonality pattern of the question. -/
def M : Matrix (Fin 4) (Fin 4) ℕ :=
  !![1, 0, 0, 1; 1, 0, 1, 0; 0, 1, 0, 1; 0, 1, 1, 0]

theorem main :
    ∀ S T : Fin 4 → Submodule ℝ (EuclideanSpace ℝ (Fin 3)),
      (∀ i, 1 ≤ Module.finrank ℝ (S i)) → (∀ j, 1 ≤ Module.finrank ℝ (T j)) →
      (∀ i j, M i j = 0 ↔ (S i).IsOrtho (T j)) →
      (∀ i, Module.finrank ℝ (S i) = 1) ∧ (∀ j, Module.finrank ℝ (T j) = 1) := by
  sorry

end OMA.S_mo_252065
