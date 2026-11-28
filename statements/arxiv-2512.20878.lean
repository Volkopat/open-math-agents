import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.ZMod.Basic

/-!
# Total chromatic numbers of circulant graphs C_n(1, 3)

Source: https://arxiv.org/abs/2512.20878 ("Total colouring of circulant graphs C_n(1, 3)")

For every integer `n ≥ 7`, the 4-regular circulant graph `C_n(1, 3)` on `ZMod n`
(connecting `u` and `v` when `u ≠ v` and `u - v ∈ {1, -1, 3, -3}`) has total chromatic
number `6` if `n ∈ {7, 8, 12, 13, 17}`, and `5` otherwise.
-/

namespace OMA.S_arxiv_2512_20878

def circulant13 (n : ℕ) : SimpleGraph (ZMod n) where
  Adj u v := u ≠ v ∧ (v - u = 1 ∨ u - v = 1 ∨ v - u = 3 ∨ u - v = 3)
  symm := ⟨by
    intro u v ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h | h | h | h
    · exact Or.inr (Or.inl h)
    · exact Or.inl h
    · exact Or.inr (Or.inr (Or.inr h))
    · exact Or.inr (Or.inr (Or.inl h))⟩
  loopless := ⟨by
    intro u ⟨hne, _⟩
    exact hne rfl⟩

def IsTotalColoring {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (cv : V → Fin k) (ce : G.edgeSet → Fin k) : Prop :=
  (∀ u v, G.Adj u v → cv u ≠ cv v) ∧
  (∀ u (e : G.edgeSet), u ∈ e.val → cv u ≠ ce e) ∧
  (∀ e₁ e₂ : G.edgeSet, e₁ ≠ e₂ → (∃ u, u ∈ e₁.val ∧ u ∈ e₂.val) → ce e₁ ≠ ce e₂)

def HasTotalColoring {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ cv ce, IsTotalColoring G k cv ce

theorem main :
    ∀ n : ℕ, 7 ≤ n →
      let χ := if n = 7 ∨ n = 8 ∨ n = 12 ∨ n = 13 ∨ n = 17 then 6 else 5
      HasTotalColoring (circulant13 n) χ ∧ ∀ k < χ, ¬ HasTotalColoring (circulant13 n) k := by
  sorry

end OMA.S_arxiv_2512_20878
