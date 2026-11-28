import OMAStatements.S_mo_514705
import Mathlib

-- Reduction mo-514705.R1 of MathOverflow 514705 (an algebraic strengthening of Frankl)
-- Credit: @marcusbuffett

/-!
# An algebraic strengthening of Frankl's conjecture: families with a singleton, and the rest

The conjecture asks, for a union-closed family `𝓕` on `Fin n` with a nonempty member, weights
`x ≥ 0` and `m < n`, for a `k` whose weighted count of `m`-subsets of members containing `k`
(with `k` removed) dominates that of members not containing `k`. For `m = 0` it is Frankl's
conjecture. This separates the case where `𝓕` contains a singleton, the analogue of the classical
singleton case of Frankl's conjecture; it is a partial case, not progress on the conjecture.

* `H1`: if `{k} ∈ 𝓕` then `k` works, for every `m` and every weight vector. The map
  `A ↦ insert k A` sends the members without `k` injectively to members with `k`, and
  `(insert k A).erase k = A`, so every term on the right appears on the left; the other terms on
  the left are nonnegative.
* `H2`: families with no singleton member. This is the open conjecture.
-/

namespace OMA.R_mo_514705_R1

/-- A union-closed family containing a singleton `{k}`: `k` satisfies the inequality. -/
def H1 : Prop :=
  ∀ (n m : ℕ) (𝓕 : Finset (Finset (Fin n))) (x : Fin n → ℝ) (k : Fin n),
    (∀ A ∈ 𝓕, ∀ B ∈ 𝓕, A ∪ B ∈ 𝓕) → (∀ i, 0 ≤ x i) → {k} ∈ 𝓕 →
      ∑ A ∈ 𝓕.filter (fun A => k ∈ A), ∑ B ∈ (A.erase k).powersetCard m, ∏ i ∈ B, x i ≥
        ∑ A ∈ 𝓕.filter (fun A => k ∉ A), ∑ B ∈ A.powersetCard m, ∏ i ∈ B, x i

/-- The open part: no member of `𝓕` is a singleton. -/
def H2 : Prop :=
  ∀ (n m : ℕ) (𝓕 : Finset (Finset (Fin n))) (x : Fin n → ℝ),
    m < n → (∀ A ∈ 𝓕, ∀ B ∈ 𝓕, A ∪ B ∈ 𝓕) → (∃ A ∈ 𝓕, A.Nonempty) → (∀ i, 0 ≤ x i) →
      (∀ k : Fin n, {k} ∉ 𝓕) →
      ∃ k : Fin n,
        ∑ A ∈ 𝓕.filter (fun A => k ∈ A), ∑ B ∈ (A.erase k).powersetCard m, ∏ i ∈ B, x i ≥
          ∑ A ∈ 𝓕.filter (fun A => k ∉ A), ∑ B ∈ A.powersetCard m, ∏ i ∈ B, x i

theorem main : H1 → H2 → type_of% @OMA.S_mo_514705.main := by
  intro h1 h2 n m 𝓕 x hmn huc hne hx
  by_cases hs : ∃ k : Fin n, {k} ∈ 𝓕
  · obtain ⟨k, hk⟩ := hs
    exact ⟨k, h1 n m 𝓕 x k huc hx hk⟩
  · push_neg at hs
    exact h2 n m 𝓕 x hmn huc hne hx hs

end OMA.R_mo_514705_R1
