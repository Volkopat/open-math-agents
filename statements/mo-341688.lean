import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # The squared-square converse
Source: Aaron Meyerowitz, https://mathoverflow.net/q/341688 (September 16, 2019).
Formalization by @LDJAI with OpenAI Codex. A finite family enumerates the
multiset of tile sizes, allowing repetitions as in the original question. -/
namespace OMA.S_mo_341688

/-- Each edge of the complete bipartite graph belongs to exactly one Cartesian
product of a row set and a column set of the prescribed cardinalities. -/
def HasBicliqueDecomposition {ι : Type} (n : ℕ) (s : ι → ℕ) : Prop :=
  ∃ R C : ι → Finset (Fin n),
    (∀ i, (R i).card = s i ∧ (C i).card = s i) ∧
    (∀ a b : Fin n, ∃! i, a ∈ R i ∧ b ∈ C i)

/-- A squared square with the stated side lengths: closed axis-parallel squares
contained in the board, with disjoint interiors, whose union covers the board. -/
def HasSquareTiling {ι : Type} (n : ℕ) (s : ι → ℕ) : Prop :=
  ∃ x y : ι → ℝ,
    (∀ i, 0 ≤ x i ∧ x i + s i ≤ n ∧ 0 ≤ y i ∧ y i + s i ≤ n) ∧
    (∀ i j, i ≠ j → x i + s i ≤ x j ∨ x j + s j ≤ x i ∨
                     y i + s i ≤ y j ∨ y j + s j ≤ y i) ∧
    (∀ a b : ℝ, 0 ≤ a → a ≤ n → 0 ≤ b → b ≤ n →
      ∃ i, x i ≤ a ∧ a ≤ x i + s i ∧ y i ≤ b ∧ b ≤ y i + s i)

/-- Universal converse: every square-area partition realized by a balanced
biclique decomposition can also be realized as a squared square. -/
theorem main : ∀ (n : ℕ) (ι : Type) [Fintype ι] (s : ι → ℕ),
    0 < n → (∀ i, 0 < s i ∧ s i < n) → (∑ i, (s i)^2) = n^2 →
    HasBicliqueDecomposition n s → HasSquareTiling n s := by
  sorry

end OMA.S_mo_341688
