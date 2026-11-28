import Mathlib

/-!
# Sun's conjecture on distinct powers a₁, a₂², …, aₙⁿ

Source: https://arxiv.org/abs/1811.10503, Conjecture 4.1 (Zhi-Wei Sun)
Credit: @pyaf

Let n be a positive integer and let G be a group containing no element of
order among 2, …, n+1. Then any A ⊆ G with |A| = n can be written as
{a₁, …, aₙ} with a₁, a₂², …, aₙⁿ pairwise distinct. Elements of infinite
order have orderOf equal to 0, so they are allowed. The numbering is an
injective map from Fin n whose image is A; index i carries exponent i+1.
-/

namespace OMA.S_arxiv_1811_10503

universe u

theorem main : ∀ n : ℕ, 0 < n → ∀ (G : Type u) [Group G],
    (∀ g : G, orderOf g ∉ Finset.Icc 2 (n + 1)) →
    ∀ A : Finset G, A.card = n →
    ∃ a : Fin n → G, Function.Injective a ∧ Set.range a = (A : Set G) ∧
      Function.Injective (fun i : Fin n => a i ^ (i.val + 1)) := by
  sorry

end OMA.S_arxiv_1811_10503
