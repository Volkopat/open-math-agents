import Mathlib

/-!
# Frankl-like conjecture for `k`-union-closed families of sets

Source: https://mathoverflow.net/questions/511338
-- Credit: @Dugongue (agent: Claude Code, model claude-opus-5-5)

A family `𝓕` of subsets of `[n]` is `k`-union-closed if for every `A ⊆ [n]` with `|A| ≥ k`,
`⋃ {S ∈ 𝓕 | S ⊆ A} ∈ 𝓕`. Conjecture (asker): if `𝓕` is `k`-union-closed with `⋃ 𝓕 = [n]`, then
for all reals `x₁, …, xₙ ≥ 2^(k-1) - 1` there is `i ∈ [n]` with
`∑_{S ∈ 𝓕, i ∈ S} ∏_{j ∈ S} xⱼ ≥ xᵢ ∑_{S ∈ 𝓕, i ∉ S} ∏_{j ∈ S} xⱼ`.

Conventions:
* `[n]` is `Fin n`, families are `Finset (Finset (Fin n))`; `k ≥ 1` and `n ≥ 1` (for `n = 0`
  there is no `i`). The union over the empty subfamily is `∅`.
-/

namespace OMA.S_mo_511338

/-- `𝓕` is `k`-union-closed. -/
def KUnionClosed {n : ℕ} (k : ℕ) (F : Finset (Finset (Fin n))) : Prop :=
  ∀ A : Finset (Fin n), k ≤ A.card → (F.filter fun S => S ⊆ A).sup id ∈ F

/-- The conjectured weighted Frankl-type inequality. -/
theorem main : ∀ (n k : ℕ) (F : Finset (Finset (Fin n))), 1 ≤ n → 1 ≤ k →
    KUnionClosed k F → F.sup id = Finset.univ →
    ∀ x : Fin n → ℝ, (∀ j, (2 : ℝ) ^ (k - 1) - 1 ≤ x j) →
    ∃ i : Fin n, x i * ∑ S ∈ F.filter (fun S => i ∉ S), ∏ j ∈ S, x j ≤
      ∑ S ∈ F.filter (fun S => i ∈ S), ∏ j ∈ S, x j := by
  sorry

end OMA.S_mo_511338
