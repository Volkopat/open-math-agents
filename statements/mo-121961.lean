import Mathlib

namespace OMA.S_mo_121961

/-- Every subset one smaller than a block is contained in a block. -/
def IsCover (n : ℕ) (blocks : Finset (Finset (Fin n))) : Prop :=
  (∀ B ∈ blocks, B.card = n / 2) ∧
    ∀ A : Finset (Fin n), A.card = n / 2 - 1 →
      ∃ B ∈ blocks, A ⊆ B

def IsMinimumCoverSize (n size : ℕ) : Prop :=
  (∃ blocks : Finset (Finset (Fin n)), IsCover n blocks ∧ blocks.card = size) ∧
    ∀ blocks : Finset (Finset (Fin n)), IsCover n blocks → size ≤ blocks.card

/-- The proposed Erdős–Hanani covering asymptotic when the block size is
half the ground-set size, rounded down. -/
theorem main :
    ∃ κ : ℕ → ℕ,
      (∀ n : ℕ, 2 ≤ n → IsMinimumCoverSize n (κ n)) ∧
      Filter.Tendsto
        (fun n : ℕ => (κ n : ℝ) * ((n / 2 : ℕ) : ℝ) / (n.choose (n / 2) : ℝ))
        Filter.atTop (nhds 1) := by
  sorry

end OMA.S_mo_121961
