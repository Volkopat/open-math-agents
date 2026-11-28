import Mathlib

/-!
# Erdős Problem 635

Source: https://www.erdosproblems.com/635
Credit: @mattdorman

The source asks: let `t ≥ 1` and `A ⊆ {1, …, N}` be such that whenever `a, b ∈ A` with
`b - a ≥ t` we have `b - a ∤ b`. How large can `|A|` be? Is it true that
`|A| ≤ (1/2 + o_t(1)) N`?

Reading used here: the second question, for each fixed `t ≥ 1`: for every `ε > 0`, for all large
`N`, every such `A ⊆ {1, …, N}` has `|A| ≤ (1/2 + ε) N` (the `o_t(1)` term may depend on `t`, so
the threshold for `N` depends on `t` and `ε`). The statement below is the affirmative answer.
-/

open Filter

namespace OMA.S_erdos_635

theorem main :
    ∀ t : ℕ, 1 ≤ t → ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N → (∀ a ∈ A, ∀ b ∈ A, a + t ≤ b → ¬ (b - a) ∣ b) →
        (A.card : ℝ) ≤ (1 / 2 + ε) * N := by
  sorry

end OMA.S_erdos_635
