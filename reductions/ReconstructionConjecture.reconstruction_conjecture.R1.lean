import FormalConjectures.Wikipedia.ReconstructionConjecture

-- Reduction ReconstructionConjecture.reconstruction_conjecture.R1
-- of the graph reconstruction conjecture.
-- Credit: @lawrencerowland

/-!
Complementing a graph complements every vertex-deleted card. We prove
this directly and transport isomorphisms in both directions.

H1 is the published interval-graph theorem of Heinrich, Kiyomi, Otachi
and Schweitzer (Theorem 1, https://arxiv.org/abs/2504.02353).
The comparison graph is unrestricted, as in their theorem.
H2 is the remaining conjecture for two graphs for which neither graph
and neither complement has an interval representation.
-/

namespace OMA.R_ReconstructionConjecture_reconstruction_conjecture_R1

open SimpleGraph ReconstructionConjecture

private theorem complement_iso {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G ≃g H) : Nonempty (Gᶜ ≃g Hᶜ) := by
  refine ⟨⟨f.toEquiv, ?_⟩⟩
  intro a b
  change (f a ≠ f b ∧ ¬ H.Adj (f a) (f b)) ↔ (a ≠ b ∧ ¬ G.Adj a b)
  exact and_congr (not_congr f.injective.eq_iff) (not_congr f.map_rel_iff)

private theorem induce_complement {V : Type*} (G : SimpleGraph V) (S : Set V) :
    (Gᶜ).induce S = (G.induce S)ᶜ := by
  ext a b
  change ((a : V) ≠ (b : V) ∧ ¬ G.Adj a b) ↔ (a ≠ b ∧ ¬ G.Adj a b)
  exact and_congr (not_congr Subtype.val_injective.eq_iff) Iff.rfl

/-- The deck-matching bijection works also for the complements. -/
theorem complement_hypomorphic {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : Hypomorphic G H) : Hypomorphic Gᶜ Hᶜ := by
  obtain ⟨σ, cards⟩ := h
  refine ⟨σ, fun v => ?_⟩
  obtain ⟨f⟩ := cards v
  rw [induce_complement, induce_complement]
  exact complement_iso f

private theorem swap_decks {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (h : Hypomorphic G H) : Hypomorphic H G := by
  obtain ⟨σ, cards⟩ := h
  refine ⟨σ.symm, fun w => ?_⟩
  generalize hx : σ.symm w = v
  have hv : σ v = w := (congrArg σ hx.symm).trans (σ.apply_symm_apply w)
  rw [← hv]
  obtain ⟨f⟩ := cards v
  exact ⟨f.symm⟩

/-- Theorem 1 of Heinrich–Kiyomi–Otachi–Schweitzer. An interval model uses
nonempty closed intervals, and adjacency excludes loops. -/
def H1 : Prop :=
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V → ∀ (G : SimpleGraph V) (H : SimpleGraph W),
      (∃ left right : V → ℝ, (∀ v, left v ≤ right v) ∧
        ∀ x y, G.Adj x y ↔ x ≠ y ∧ left x ≤ right y ∧ left y ≤ right x) →
      Hypomorphic G H → Nonempty (G ≃g H)

/-- Remaining pairs after exploiting deck symmetry and complementation. -/
def H2 : Prop :=
  let interval {X : Type} (K : SimpleGraph X) : Prop :=
    ∃ left right : X → ℝ, (∀ v, left v ≤ right v) ∧
      ∀ x y, K.Adj x y ↔ x ≠ y ∧ left x ≤ right y ∧ left y ≤ right x
  ∀ {V W : Type} [Fintype V] [Fintype W],
    3 ≤ Fintype.card V → ∀ (G : SimpleGraph V) (H : SimpleGraph W),
      ¬ interval G → ¬ interval Gᶜ → ¬ interval H → ¬ interval Hᶜ →
      Hypomorphic G H → Nonempty (G ≃g H)

theorem main : H1 → H2 → type_of% @ReconstructionConjecture.reconstruction_conjecture := by
  intro known remaining V W _ _ n G H h
  let interval {X : Type} (K : SimpleGraph X) : Prop :=
    ∃ left right : X → ℝ, (∀ v, left v ≤ right v) ∧
      ∀ x y, K.Adj x y ↔ x ≠ y ∧ left x ≤ right y ∧ left y ≤ right x
  by_cases g : interval G
  · exact known n G H g h
  by_cases gc : interval Gᶜ
  · obtain ⟨f⟩ := known n Gᶜ Hᶜ gc (complement_hypomorphic h)
    simpa only [compl_compl] using complement_iso f
  have n' : 3 ≤ Fintype.card W := h.card_eq ▸ n
  have back := swap_decks h
  by_cases k : interval H
  · obtain ⟨f⟩ := known n' H G k back
    exact ⟨f.symm⟩
  by_cases kc : interval Hᶜ
  · obtain ⟨f⟩ := known n' Hᶜ Gᶜ kc (complement_hypomorphic back)
    simpa only [compl_compl] using complement_iso f.symm
  exact remaining n G H g gc k kc h

end OMA.R_ReconstructionConjecture_reconstruction_conjecture_R1
