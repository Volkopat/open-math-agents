import Mathlib

/-!
# On sum-intersecting families of positive integers

Source: https://arxiv.org/abs/2304.14167, Conjecture 1.2.
Credit: @jagraj28

Definition 1.1 of the paper: a collection `𝓕` of subsets of `{1, 2, …, n}` is sum-intersecting
if for every `A, B ∈ 𝓕`, `A ∩ B` contains a sum, i.e. there exist `x, y, z ∈ A ∩ B` (not
necessarily distinct) with `x + y = z`. Conjecture 1.2: every sum-intersecting family of subsets
of `{1, …, n}` has at most `2 ^ n / 4` members. The family of all sets containing `{1, 2}` shows
the bound would be tight; the paper proves the bound `0.32 · 2 ^ n`.

Formalization notes:
* A family is a `Finset (Finset ℕ)` whose members are subsets of `Finset.Icc 1 n`.
* "For every `A, B ∈ 𝓕`" includes `A = B`, as in the definition.
* The bound `|𝓕| ≤ 2 ^ n / 4` is stated without division as `4 * |𝓕| ≤ 2 ^ n`.
* An exhaustive search gives the largest sum-intersecting families for `n = 1, …, 5`: sizes
  `0, 1, 2, 4, 8`, equal to `⌊2 ^ n / 4⌋`.
-/

namespace OMA.S_arxiv_2304_14167

/-- `𝓕` is sum-intersecting: for all `A, B ∈ 𝓕` there are `x, y, z ∈ A ∩ B` with
`x + y = z`. -/
def SumIntersecting (𝓕 : Finset (Finset ℕ)) : Prop :=
  ∀ A ∈ 𝓕, ∀ B ∈ 𝓕, ∃ x ∈ A ∩ B, ∃ y ∈ A ∩ B, ∃ z ∈ A ∩ B, x + y = z

/-- Conjecture 1.2: a sum-intersecting family of subsets of `{1, …, n}` has at most
`2 ^ n / 4` members. -/
theorem main :
    ∀ (n : ℕ) (𝓕 : Finset (Finset ℕ)), (∀ A ∈ 𝓕, A ⊆ Finset.Icc 1 n) → SumIntersecting 𝓕 →
      4 * 𝓕.card ≤ 2 ^ n := by
  sorry

end OMA.S_arxiv_2304_14167
