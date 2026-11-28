import Mathlib

/-!
# An algebraic strengthening of Frankl's union-closed sets conjecture

Source: https://mathoverflow.net/questions/514705
Conjecture (asker). Let `0 ≤ m < n`, `𝓕` a union-closed family of subsets of
`[n] = {1, …, n}` and `x₁, …, xₙ ≥ 0`. Then there is `k ∈ [n]` with
`∑_{A ∈ 𝓕, k ∈ A} ∑_{B ⊆ A \ {k}, |B| = m} ∏_{i ∈ B} xᵢ ≥ ∑_{A ∈ 𝓕, k ∉ A} ∑_{B ⊆ A, |B| = m} ∏_{i ∈ B} xᵢ`.
The case `m = 0` is Frankl's conjecture.

Conventions. The ground set is `Fin n`. As in Frankl's conjecture, `𝓕` is required to contain
a nonempty set (for `𝓕 = {∅}` the case `m = 0` fails trivially).

-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)
-/

namespace OMA.S_mo_514705

theorem main :
    ∀ (n m : ℕ) (𝓕 : Finset (Finset (Fin n))) (x : Fin n → ℝ),
      m < n → (∀ A ∈ 𝓕, ∀ B ∈ 𝓕, A ∪ B ∈ 𝓕) → (∃ A ∈ 𝓕, A.Nonempty) → (∀ i, 0 ≤ x i) →
      ∃ k : Fin n,
        ∑ A ∈ 𝓕.filter (fun A => k ∈ A), ∑ B ∈ (A.erase k).powersetCard m, ∏ i ∈ B, x i ≥
          ∑ A ∈ 𝓕.filter (fun A => k ∉ A), ∑ B ∈ A.powersetCard m, ∏ i ∈ B, x i := by
  sorry

end OMA.S_mo_514705
