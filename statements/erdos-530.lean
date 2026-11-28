import Mathlib

/-!
# Erdős Problem 530

Source: https://www.erdosproblems.com/530
Credit: @mattdorman

The source asks (originally Riddell): let `ℓ(N)` be maximal such that every finite set `A ⊂ ℝ`
of size `N` contains a Sidon subset `S` of size `ℓ(N)` (the only solutions to `a + b = c + d` in
`S` are the trivial ones). Determine the order of `ℓ(N)`. In particular, is it true that
`ℓ(N) ∼ N^{1/2}`?

Reading used here: the second question. `ℓ(N) ∼ √N` means `ℓ(N) / √N → 1`, which is stated
directly from the definition of `ℓ(N)`: for every `ε > 0` and all large `N`, every `N`-element
`A ⊂ ℝ` has a Sidon subset of size at least `(1 - ε) √N`, and some `N`-element `A ⊂ ℝ` has no
Sidon subset larger than `(1 + ε) √N`. (The source records that the second half is known, from
`A = {1, …, N}`.) Trivial solutions of `a + b = c + d` are those with `{a, b} = {c, d}`.
-/

open Filter

namespace OMA.S_erdos_530

/-- `S` is a Sidon set: `a + b = c + d` in `S` only when `{a, b} = {c, d}`. -/
def IsSidonFinset (S : Finset ℝ) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ c ∈ S, ∀ d ∈ S, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

theorem main :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N : ℕ in atTop,
      (∀ A : Finset ℝ, A.card = N →
        ∃ S ⊆ A, IsSidonFinset S ∧ (1 - ε) * Real.sqrt N ≤ S.card) ∧
      (∃ A : Finset ℝ, A.card = N ∧
        ∀ S ⊆ A, IsSidonFinset S → (S.card : ℝ) ≤ (1 + ε) * Real.sqrt N) := by
  sorry

end OMA.S_erdos_530
