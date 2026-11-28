import OMAReductions.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1_H3_R1

/-!
# Removing degree-three vertices in the Henning–Yeo transversal bound

Choose a vertex of degree three and discard its three incident edges. Keep just
the vertices used by surviving edges. If all remaining degree-three vertices
lose an edge, the original degree-three vertices lie in one three-edge star.
Otherwise induction applies. Deleting two vertices saves at least 19 units of
weight. Deleting one saves 14, enough to pay for a transversal vertex when the
original weight is congruent to any of 0 through 13 modulo 17.

The transversal bound is due to Henning and Yeo, DOI 10.1007/s00373-021-02285-x.
Reduction by @AlfredMelson.
-/

namespace OMA.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1_H3_R1_H2_R1

open Finset
open scoped Classical

/-- All degree-three vertices lie in a single three-edge star. -/
def H1 : Prop :=
  ∀ (A : Finset ℝ) (E : Finset (Finset ℝ)), (∀ e ∈ E, e ⊆ A ∧ e.card = 3) →
    (∀ e ∈ E, ∀ f ∈ E, e ≠ f → (e ∩ f).card ≤ 1) →
    (¬ ∃ f : Fin 7 ↪ ℝ, {f 0,f 1,f 2} ∈ E ∧ {f 0,f 3,f 4} ∈ E ∧
        {f 0,f 5,f 6} ∈ E ∧ {f 1,f 3,f 5} ∈ E ∧ {f 2,f 4,f 6} ∈ E) →
    (∀ v ∈ A, (E.filter fun e => v ∈ e).card ≤ 3) →
    (∃ v ∈ A, (E.filter fun e => v ∈ e).card = 3) →
    (∃ x ∈ A, (E.filter fun e => x ∈ e).card = 3 ∧
      ∀ z ∈ A, (E.filter fun e => z ∈ e).card = 3 →
        z = x ∨ ∃ e ∈ E, x ∈ e ∧ z ∈ e) →
    ∃ T ⊆ A, (∀ e ∈ E, (e ∩ T).Nonempty) ∧ 17*T.card ≤ 5*A.card+3*E.card

/-- Only the three tight residue classes remain, and deleting a degree-three
vertex never isolates another vertex. -/
def H2 : Prop :=
  ∀ (A : Finset ℝ) (E : Finset (Finset ℝ)), (∀ e ∈ E, e ⊆ A ∧ e.card = 3) →
    (∀ e ∈ E, ∀ f ∈ E, e ≠ f → (e ∩ f).card ≤ 1) →
    (¬ ∃ f : Fin 7 ↪ ℝ, {f 0,f 1,f 2} ∈ E ∧ {f 0,f 3,f 4} ∈ E ∧
        {f 0,f 5,f 6} ∈ E ∧ {f 1,f 3,f 5} ∈ E ∧ {f 2,f 4,f 6} ∈ E) →
    (∀ v ∈ A, (E.filter fun e => v ∈ e).card ≤ 3) →
    (∃ v ∈ A, (E.filter fun e => v ∈ e).card = 3) →
    (¬ ∃ x ∈ A, (E.filter fun e => x ∈ e).card = 3 ∧
      ∀ z ∈ A, (E.filter fun e => z ∈ e).card = 3 →
        z = x ∨ ∃ e ∈ E, x ∈ e ∧ z ∈ e) →
    14 ≤ (5*A.card + 3*E.card) % 17 →
    (∀ x ∈ A, (E.filter fun e => x ∈ e).card = 3 → ∀ y ∈ A, y ≠ x →
      ∃ e ∈ E, y ∈ e ∧ x ∉ e) →
    ∃ T ⊆ A, (∀ e ∈ E, (e ∩ T).Nonempty) ∧ 17*T.card ≤ 5*A.card+3*E.card

lemma oma_survives_star {E : Finset (Finset ℝ)} {x z : ℝ}
    (hz : (E.filter fun e => z ∈ e).card = 3)
    (hn : ¬ ∃ e ∈ E, x ∈ e ∧ z ∈ e) :
    ((E.filter fun e => x ∉ e).filter fun e => z ∈ e).card = 3 := by
  have sets : ((E.filter fun e => x ∉ e).filter fun e => z ∈ e) =
      (E.filter fun e => z ∈ e) := by
    ext e
    simp only [mem_filter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · exact fun h => ⟨⟨h.1, fun hx => hn ⟨e, h.1, hx, h.2⟩⟩, h.2⟩
  rwa [sets]

lemma oma_lift_degree_three {A D T : Finset ℝ} {E : Finset (Finset ℝ)} {x : ℝ}
    (hx : x ∈ A) (hT : T ⊆ D) (hD : D ⊆ A)
    (degree : (E.filter fun e => x ∈ e).card = 3)
    (hit : ∀ e ∈ E.filter (fun e => x ∉ e), (e ∩ T).Nonempty)
    (bound : 17*T.card ≤ 5*D.card + 3*(E.filter fun e => x ∉ e).card)
    (paid : 17 + 5*D.card + 3*(E.filter fun e => x ∉ e).card ≤ 5*A.card + 3*E.card ∨
      (D.card + 1 = A.card ∧ (5*A.card + 3*E.card)%17 < 14)) :
    ∃ S ⊆ A, (∀ e ∈ E, (e ∩ S).Nonempty) ∧ 17*S.card ≤ 5*A.card + 3*E.card := by
  refine ⟨insert x T, insert_subset hx (hT.trans hD), ?_, ?_⟩
  · intro e he
    by_cases hxe : x ∈ e
    · exact ⟨x, mem_inter.mpr ⟨hxe, mem_insert_self _ _⟩⟩
    · obtain ⟨z, hz⟩ := hit e (mem_filter.mpr ⟨he, hxe⟩)
      exact ⟨z, mem_inter.mpr ⟨(mem_inter.mp hz).1, mem_insert_of_mem (mem_inter.mp hz).2⟩⟩
  · have splitCard := card_filter_add_card_filter_not (s := E) (fun e => x ∈ e)
    have size := card_insert_le x T
    rcases paid with h | ⟨h, hmod⟩
    · omega
    · have division := Nat.mod_add_div (5*A.card + 3*E.card) 17
      have smaller : T.card < (5*A.card + 3*E.card)/17 := by omega
      omega

theorem main : H1 → H2 → OMA.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1_H3_R1.H2 := by
  classical
  intro localized tight A
  induction A using Finset.strongInductionOn
  rename_i A ih
  intro E three linear free max3 exists3
  let deg (v : ℝ) := (E.filter fun e => v ∈ e).card
  by_cases loc : ∃ x ∈ A, deg x = 3 ∧
      ∀ z ∈ A, deg z = 3 → z = x ∨ ∃ e ∈ E, x ∈ e ∧ z ∈ e
  · exact localized A E three linear free max3 exists3 loc
  let W := 5*A.card + 3*E.card
  by_cases core : 14 ≤ W % 17 ∧ ∀ x ∈ A, deg x = 3 → ∀ y ∈ A, y ≠ x →
      ∃ e ∈ E, y ∈ e ∧ x ∉ e
  · exact tight A E three linear free max3 exists3 loc core.1 core.2
  obtain ⟨x, hx, dx, reason⟩ : ∃ x ∈ A, deg x = 3 ∧
      (W % 17 < 14 ∨ ∃ y ∈ A, y ≠ x ∧ ∀ e ∈ E, y ∈ e → x ∈ e) := by
    by_cases loose : W % 17 < 14
    · obtain ⟨x,hx,dx⟩ := exists3
      exact ⟨x,hx,dx,Or.inl loose⟩
    · have missing := mt (And.intro (Nat.le_of_not_gt loose)) core
      push Not at missing
      obtain ⟨x,hx,dx,y,hy,hne,hyx⟩ := missing
      exact ⟨x,hx,dx,Or.inr ⟨y,hy,hne,hyx⟩⟩
  let F := E.filter fun e => x ∉ e
  let D := F.biUnion id
  have subF : F ⊆ E := filter_subset _ _
  have inside (e) (he : e ∈ F) : e ⊆ D := by
    intro y hy
    exact mem_biUnion.mpr ⟨e,he,hy⟩
  have subD : D ⊆ A.erase x := by
    intro v hv
    obtain ⟨e,he,hv⟩ := mem_biUnion.mp hv
    have he' := mem_filter.mp he
    exact mem_erase.mpr ⟨fun eq => he'.2 (eq ▸ hv), (three e he'.1).1 hv⟩
  have subA : D ⊆ A := subD.trans (erase_subset _ _)
  have surviving : ∃ z ∈ D, (F.filter fun e => z ∈ e).card = 3 := by
    have outside : ¬ ∀ z ∈ A, deg z = 3 → z = x ∨ ∃ e ∈ E, x ∈ e ∧ z ∈ e :=
      fun h => loc ⟨x,hx,dx,h⟩
    push Not at outside
    obtain ⟨z,_,dz,_,apart⟩ := outside
    have hn : ¬ ∃ e ∈ E, x ∈ e ∧ z ∈ e := by
      rintro ⟨e,he,hx',hz⟩
      exact apart e he hx' hz
    have d' : (F.filter fun e => z ∈ e).card = 3 :=
      oma_survives_star dz hn
    have hp : 0 < (F.filter fun e => z ∈ e).card := by omega
    obtain ⟨e,he⟩ := card_pos.mp hp
    have h := mem_filter.mp he
    exact ⟨z, inside e h.1 h.2, d'⟩
  obtain ⟨T,hT,hit,bound⟩ := ih D (lt_of_le_of_lt subD (erase_ssubset hx)) F
    (fun e he => ⟨inside e he, (three e (subF he)).2⟩)
    (fun e he f hf h => linear e (subF he) f (subF hf) h)
    (fun ⟨f,h₁,h₂,h₃,h₄,h₅⟩ => free ⟨f,subF h₁,subF h₂,subF h₃,subF h₄,subF h₅⟩)
    (fun z hz => le_trans (card_le_card (filter_subset_filter _ subF)) (max3 z (subA hz)))
    surviving
  have sx := card_erase_add_one hx
  have sd := card_le_card subD
  have se : (E.filter fun e => x ∈ e).card + F.card = E.card :=
    card_filter_add_card_filter_not (s := E) (fun e => x ∈ e)
  change (E.filter fun e => x ∈ e).card = 3 at dx
  have price : 17 + 5*D.card + 3*F.card ≤ 5*A.card+3*E.card ∨
      (D.card + 1 = A.card ∧ (5*A.card+3*E.card)%17 < 14) := by
    rcases reason with loose | ⟨y,hy,hne,dom⟩
    · dsimp [W] at loose
      omega
    · have yn : y ∉ D := by
        intro h
        obtain ⟨e,he,hy'⟩ := mem_biUnion.mp h
        have he' := mem_filter.mp he
        exact he'.2 (dom e he'.1 hy')
      have strict : D ⊂ A.erase x := Finset.ssubset_iff_subset_ne.mpr ⟨subD,fun eq =>
        yn (eq ▸ (mem_erase.mpr ⟨hne,hy⟩))⟩
      have sd' := card_lt_card strict
      exact Or.inl (by omega)
  exact oma_lift_degree_three hx hT subA dx hit bound price

end OMA.R_Erdos757_erdos_757_variants_lowerBound_R1_H1_R1_H3_R1_H2_R1
