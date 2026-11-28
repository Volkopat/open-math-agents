import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Set.Card

/-!
# Exponential Euclidean kissing numbers for lattices

Bennett, Golovnev and Stephens-Davidowitz ask whether an infinite family of
lattices has Euclidean kissing number exponential in the ambient dimension.
Their lattice is the integer span of real-linearly independent generators.
Its kissing number counts all shortest nonzero vectors, including both signs.

Source: https://arxiv.org/abs/2410.16660
Credit: @jacklarmer
-/

namespace OMA.S_arxiv_2410_16660

noncomputable def kissingNumber {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) : ℕ :=
  {v : EuclideanSpace ℝ (Fin n) | v ∈ L ∧ v ≠ 0 ∧
    ∀ w ∈ L, w ≠ 0 → ‖v‖ ≤ ‖w‖}.ncard

theorem main :
    ∃ b : ℝ, 1 < b ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧
      ∃ (k : ℕ) (B : Fin k → EuclideanSpace ℝ (Fin n)),
        LinearIndependent ℝ B ∧
          b ^ n ≤ (kissingNumber (Submodule.span ℤ (Set.range B)) : ℝ) := by
  sorry

end OMA.S_arxiv_2410_16660
