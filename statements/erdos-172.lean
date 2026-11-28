import Mathlib

/-!
# Erdős Problem 172

Source: https://www.erdosproblems.com/172
Credit: @mattdorman

The source asks (first asked by Hindman): is it true that in any finite colouring of `ℕ` there
exist arbitrarily large finite `A` such that all sums and products of distinct elements in `A` are
the same colour?

Reading used here: `ℕ` is the positive integers, so `A` consists of positive integers. A finite
colouring is a map `c : ℕ → Fin r`. The sums and products of distinct elements of `A` are
`∑ B` and `∏ B` for nonempty `B ⊆ A`, single elements included (the source counts `|A| = 2`, i.e.
`{x, y, x + y, xy}`, as the first non-trivial case). Arbitrarily large means: for every `k` there
is such an `A` with at least `k` elements. The statement below is the affirmative answer.
-/

namespace OMA.S_erdos_172

theorem main :
    ∀ (r : ℕ) (c : ℕ → Fin r) (k : ℕ), ∃ A : Finset ℕ, k ≤ A.card ∧ (∀ a ∈ A, 0 < a) ∧
      ∃ col : Fin r, ∀ B ⊆ A, B.Nonempty → c (∑ b ∈ B, b) = col ∧ c (∏ b ∈ B, b) = col := by
  sorry

end OMA.S_erdos_172
