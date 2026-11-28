import OMAReductions.R_UnionClosed_union_closed_variants_univ_card_R1
import Mathlib

/-! # The 4-element minimum case of the twelve-element union-closed theorem, split by local configuration
Vučković and Živković, The 12-Element Case of Frankl's Conjecture (2017), Table I: the rows that consist
of sets with at least four elements are 7, 8, 12, 16, 26, 27, 28, 29, 30, 31 and 32. A family with a
4-set and no smaller nonempty member is treated by the first of these rows whose configuration it
contains. H2, H3 and H4 are rows 30, 31 and 32, each with the earlier exclusions its weight certificate
needs (found by an exhaustive fiber search); H1 collects the families containing one of the earlier
configurations (rows 7, 8, 12, 16, 26, 27, 28, 29). The main theorem is the case split. -/

namespace OMA.R_UnionClosed_union_closed_variants_univ_card_R1_H2_R1
open Finset UnionClosed
open scoped Classical

-- Rows 7, 8, 12, 16, 26, 27, 28, 29: the family contains one of the richer configurations of 4-sets and 5-sets.
def H1 : Prop := ∀ F : Finset (Finset (Fin 12)), IsUnionClosed F → ∅ ∈ F → univ ∈ F →
    (∀ S ∈ F, S.Nonempty → 4 ≤ S.card) →
    ((∃ P Q : Finset (Fin 12), P.card = 2 ∧ Q.card = 4 ∧ Disjoint P Q ∧ ∀ T, T ⊆ Q → T.card = 2 → P ∪ T ∈ F) ∨
     (∃ T : Finset (Fin 12), T.card = 3 ∧ ∃ G : Finset (Finset (Fin 12)), G ⊆ F ∧ G.card = 4 ∧ ∀ A ∈ G, A.card = 4 ∧ T ⊆ A) ∨
     (∃ T : Finset (Fin 12), T.card = 3 ∧ ∃ G : Finset (Finset (Fin 12)), G ⊆ F ∧ G.card = 3 ∧ ∀ A ∈ G, A.card = 4 ∧ T ⊆ A) ∨
     (∃ V : Finset (Fin 12), V.card = 5 ∧ ∃ G : Finset (Finset (Fin 12)), G ⊆ F ∧ G.card = 3 ∧ ∀ A ∈ G, A.card = 4 ∧ A ⊆ V) ∨
     (∃ A ∈ F, ∃ B ∈ F, ∃ C ∈ F, A.card = 4 ∧ B.card = 4 ∧ (A ∩ B).card = 3 ∧ C.card = 5 ∧ A ⊆ C ∧ C ≠ A ∪ B) ∨
     (∃ A ∈ F, ∃ B ∈ F, ∃ C ∈ F, A.card = 4 ∧ B.card = 5 ∧ C.card = 5 ∧ A ⊆ B ∧ A ⊆ C ∧ B ≠ C) ∨
     (∃ A ∈ F, ∃ B ∈ F, A.card = 4 ∧ B.card = 4 ∧ (A ∩ B).card = 3) ∨
     (∃ A ∈ F, ∃ B ∈ F, A.card = 5 ∧ B.card = 5 ∧ (A ∩ B).card = 4)) →
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧
      F.card * (∑ i, w i) ≤ 2 * (∑ S ∈ F, ∑ i ∈ S, w i)

-- Row 30: a 4-set inside a 5-set; weights 3,3,3,3,3 | 1.
def H2 : Prop := ∀ F : Finset (Finset (Fin 12)), IsUnionClosed F → ∅ ∈ F → univ ∈ F →
    (∀ S ∈ F, S.Nonempty → 4 ≤ S.card) →
    (∃ A ∈ F, ∃ B ∈ F, A.card = 4 ∧ B.card = 5 ∧ A ⊆ B) →
    ¬ (∃ A ∈ F, ∃ B ∈ F, A.card = 4 ∧ B.card = 4 ∧ (A ∩ B).card = 3) →
    ¬ (∃ A ∈ F, ∃ B ∈ F, A.card = 5 ∧ B.card = 5 ∧ (A ∩ B).card = 4) →
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧
      F.card * (∑ i, w i) ≤ 2 * (∑ S ∈ F, ∑ i ∈ S, w i)

-- Row 31: two 4-sets meeting in two points; weights 3,3,3,3,3,3 | 1.
def H3 : Prop := ∀ F : Finset (Finset (Fin 12)), IsUnionClosed F → ∅ ∈ F → univ ∈ F →
    (∀ S ∈ F, S.Nonempty → 4 ≤ S.card) →
    (∃ A ∈ F, ∃ B ∈ F, A.card = 4 ∧ B.card = 4 ∧ (A ∩ B).card = 2) →
    ¬ (∃ A ∈ F, ∃ B ∈ F, A.card = 4 ∧ B.card = 5 ∧ A ⊆ B) →
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧
      F.card * (∑ i, w i) ≤ 2 * (∑ S ∈ F, ∑ i ∈ S, w i)

-- Row 32: a single 4-set; weights 5,5,5,5 | 2.
def H4 : Prop := ∀ F : Finset (Finset (Fin 12)), IsUnionClosed F → ∅ ∈ F → univ ∈ F →
    (∀ S ∈ F, S.Nonempty → 4 ≤ S.card) →
    (∃ S ∈ F, S.card = 4) →
    ¬ (∃ A ∈ F, ∃ B ∈ F, A.card = 4 ∧ B.card = 5 ∧ A ⊆ B) →
    ¬ (∃ A ∈ F, ∃ B ∈ F, A.card = 4 ∧ B.card = 4 ∧ (A ∩ B).card = 2) →
    ∃ w : Fin 12 → ℕ, 0 < ∑ i, w i ∧
      F.card * (∑ i, w i) ≤ 2 * (∑ S ∈ F, ∑ i ∈ S, w i)

theorem main : H1 → H2 → H3 → H4 →
    OMA.R_UnionClosed_union_closed_variants_univ_card_R1.H2 := by
  intro h1 h2 h3 h4 F closed empty full four low
  by_cases early : ((∃ P Q : Finset (Fin 12), P.card = 2 ∧ Q.card = 4 ∧ Disjoint P Q ∧ ∀ T, T ⊆ Q → T.card = 2 → P ∪ T ∈ F) ∨
     (∃ T : Finset (Fin 12), T.card = 3 ∧ ∃ G : Finset (Finset (Fin 12)), G ⊆ F ∧ G.card = 4 ∧ ∀ A ∈ G, A.card = 4 ∧ T ⊆ A) ∨
     (∃ T : Finset (Fin 12), T.card = 3 ∧ ∃ G : Finset (Finset (Fin 12)), G ⊆ F ∧ G.card = 3 ∧ ∀ A ∈ G, A.card = 4 ∧ T ⊆ A) ∨
     (∃ V : Finset (Fin 12), V.card = 5 ∧ ∃ G : Finset (Finset (Fin 12)), G ⊆ F ∧ G.card = 3 ∧ ∀ A ∈ G, A.card = 4 ∧ A ⊆ V) ∨
     (∃ A ∈ F, ∃ B ∈ F, ∃ C ∈ F, A.card = 4 ∧ B.card = 4 ∧ (A ∩ B).card = 3 ∧ C.card = 5 ∧ A ⊆ C ∧ C ≠ A ∪ B) ∨
     (∃ A ∈ F, ∃ B ∈ F, ∃ C ∈ F, A.card = 4 ∧ B.card = 5 ∧ C.card = 5 ∧ A ⊆ B ∧ A ⊆ C ∧ B ≠ C) ∨
     (∃ A ∈ F, ∃ B ∈ F, A.card = 4 ∧ B.card = 4 ∧ (A ∩ B).card = 3) ∨
     (∃ A ∈ F, ∃ B ∈ F, A.card = 5 ∧ B.card = 5 ∧ (A ∩ B).card = 4))
  · exact h1 F closed empty full low early
  have p28 : ¬ (∃ A ∈ F, ∃ B ∈ F, A.card = 4 ∧ B.card = 4 ∧ (A ∩ B).card = 3) :=
    fun h => early (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
  have p29 : ¬ (∃ A ∈ F, ∃ B ∈ F, A.card = 5 ∧ B.card = 5 ∧ (A ∩ B).card = 4) :=
    fun h => early (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
  by_cases p30 : (∃ A ∈ F, ∃ B ∈ F, A.card = 4 ∧ B.card = 5 ∧ A ⊆ B)
  · exact h2 F closed empty full low p30 p28 p29
  by_cases p31 : (∃ A ∈ F, ∃ B ∈ F, A.card = 4 ∧ B.card = 4 ∧ (A ∩ B).card = 2)
  · exact h3 F closed empty full low p31 p30
  exact h4 F closed empty full low four p30 p31

end OMA.R_UnionClosed_union_closed_variants_univ_card_R1_H2_R1
