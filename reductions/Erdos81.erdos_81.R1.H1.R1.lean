import OMAReductions.R_Erdos81_erdos_81_R1
import Mathlib

/-!
Dirac's two-simplicial-vertices theorem via minimal separators.
The two remaining ingredients concern minimal separators: their clique property
in chordal graphs, and their existence with a separation into two sides in any
finite graph. The induction and the lifting of simplicial vertices are proved here.
Reference: G. A. Dirac, On rigid circuit graphs (1961), pp. 71–76.
Credit: @rgoldman73-dev.
-/

namespace OMA.R_Erdos81_erdos_81_R1_H1_R1
open Finset SimpleGraph

/-- Given the induction conclusion, a clique cannot contain both nonadjacent witnesses. -/
private lemma simplicial_outside_clique {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (T C : Finset (Fin n)) (hC : G.IsClique (C : Set (Fin n)))
    (hout : ∃ x ∈ T, x ∉ C)
    (ih : (∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧ ¬ G.Adj u v) →
      ∃ u ∈ T, ∃ v ∈ T, u ≠ v ∧ ¬ G.Adj u v ∧
        G.IsClique ((T.filter (G.Adj u)) : Set (Fin n)) ∧
        G.IsClique ((T.filter (G.Adj v)) : Set (Fin n))) :
    ∃ x ∈ T, x ∉ C ∧ G.IsClique ((T.filter (G.Adj x)) : Set (Fin n)) := by
  classical
  by_cases hT : G.IsClique (T : Set (Fin n))
  · obtain ⟨x, hx, hxC⟩ := hout
    exact ⟨x, hx, hxC, fun _ hy _ hz hne => hT (mem_filter.mp hy).1 (mem_filter.mp hz).1 hne⟩
  · obtain ⟨u, v, huv, hna⟩ := (G.not_isClique_iff).mp hT
    obtain ⟨x, hx, y, hy, hxy, hna, hsx, hsy⟩ := ih
      ⟨u, u.property, v, v.property, fun h => huv (Subtype.ext h), hna⟩
    by_cases hxC : x ∈ C
    · exact ⟨y, hy, fun hyC => hna (hC hxC hyC hxy), hsy⟩
    · exact ⟨x, hx, hxC, hsx⟩

/-- The chordal-graph ingredient: every inclusion-minimal separator is a clique. -/
def H1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), G.IsChordal →
    ∀ (S C : Finset (Fin n)) (a b : Fin n), a ∈ S → b ∈ S → a ≠ b →
      let separates : Finset (Fin n) → Prop := fun D =>
        D ⊆ S ∧ a ∉ D ∧ b ∉ D ∧
          ∀ w : G.Walk a b, (∀ x ∈ w.support, x ∈ S) → ∃ x ∈ w.support, x ∈ D
      (separates C ∧ ∀ D : Finset (Fin n), D ⊆ C → separates D → C ⊆ D) →
        G.IsClique (C : Set (Fin n))

/-- Any two nonadjacent vertices admit a minimal separator and two anticomplete sides. -/
def H2 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (S : Finset (Fin n)) (a b : Fin n),
    a ∈ S → b ∈ S → a ≠ b → ¬ G.Adj a b →
    let separates : Finset (Fin n) → Prop := fun D =>
      D ⊆ S ∧ a ∉ D ∧ b ∉ D ∧
        ∀ w : G.Walk a b, (∀ x ∈ w.support, x ∈ S) → ∃ x ∈ w.support, x ∈ D
    ∃ L R C : Finset (Fin n), S = L ∪ R ∪ C ∧
      Disjoint L R ∧ Disjoint L C ∧ Disjoint R C ∧ a ∈ L ∧ b ∈ R ∧
      (∀ x ∈ L, ∀ y ∈ R, ¬ G.Adj x y) ∧
      separates C ∧ ∀ D : Finset (Fin n), D ⊆ C → separates D → C ⊆ D

theorem main : H1 → H2 → OMA.R_Erdos81_erdos_81_R1.H1 := by
  classical
  intro hclique hsplit n G _ hch S
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro hnon
    obtain ⟨a, ha, b, hb, hab, hnab⟩ := hnon
    obtain ⟨L, R, C, hS, hLR, hLC, hRC, haL, hbR, hcross, hsep⟩ :=
      hsplit n G S a b ha hb hab hnab
    have hC := hclique n G hch S C a b ha hb hab hsep
    have haC : a ∉ C := fun h => Finset.disjoint_left.mp hLC haL h
    have hbC : b ∉ C := fun h => Finset.disjoint_left.mp hRC hbR h
    have hleft : L ∪ C ⊂ S := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [hS]
        simp only [mem_union] at hx ⊢
        tauto
      · intro he
        have hb' : b ∈ L ∪ C := he.symm ▸ hb
        rcases mem_union.mp hb' with hbL | hbC'
        · exact Finset.disjoint_left.mp hLR hbL hbR
        · exact hbC hbC'
    have hright : R ∪ C ⊂ S := by
      apply Finset.ssubset_iff_subset_ne.mpr
      refine ⟨?_, ?_⟩
      · intro x hx
        rw [hS]
        simp only [mem_union] at hx ⊢
        tauto
      · intro he
        have ha' : a ∈ R ∪ C := he.symm ▸ ha
        rcases mem_union.mp ha' with haR | haC'
        · exact Finset.disjoint_left.mp hLR haL haR
        · exact haC haC'
    obtain ⟨u, hu, huC, hus⟩ := simplicial_outside_clique G (L ∪ C) C hC
      ⟨a, mem_union_left C haL, haC⟩ (ih (L ∪ C) hleft)
    obtain ⟨v, hv, hvC, hvs⟩ := simplicial_outside_clique G (R ∪ C) C hC
      ⟨b, mem_union_left C hbR, hbC⟩ (ih (R ∪ C) hright)
    have huL : u ∈ L := (mem_union.mp hu).resolve_right huC
    have hvR : v ∈ R := (mem_union.mp hv).resolve_right hvC
    refine ⟨u, hleft.subset hu, v, hright.subset hv, ?_, hcross u huL v hvR, ?_, ?_⟩
    · intro huv
      exact Finset.disjoint_left.mp hLR huL (huv.symm ▸ hvR)
    · apply Set.Pairwise.mono _ hus
      intro x hx
      obtain ⟨hxS, hux⟩ := mem_filter.mp hx
      rw [hS] at hxS
      rcases mem_union.mp hxS with hxLR | hxC
      · rcases mem_union.mp hxLR with hxL | hxR
        · exact mem_filter.mpr ⟨mem_union_left C hxL, hux⟩
        · exact (hcross u huL x hxR hux).elim
      · exact mem_filter.mpr ⟨mem_union_right L hxC, hux⟩
    · apply Set.Pairwise.mono _ hvs
      intro x hx
      obtain ⟨hxS, hvx⟩ := mem_filter.mp hx
      rw [hS] at hxS
      rcases mem_union.mp hxS with hxLR | hxC
      · rcases mem_union.mp hxLR with hxL | hxR
        · exact (hcross x hxL v hvR hvx.symm).elim
        · exact mem_filter.mpr ⟨mem_union_left C hxR, hvx⟩
      · exact mem_filter.mpr ⟨mem_union_right R hxC, hvx⟩

end OMA.R_Erdos81_erdos_81_R1_H1_R1
