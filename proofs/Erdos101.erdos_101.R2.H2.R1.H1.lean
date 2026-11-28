import OMAReductions.R_Erdos101_erdos_101_R2_H2_R1
import Mathlib

-- Extracted from @ubuwaits's accepted proof of Erdős 101 R2.H2 (PR #23304).

section DoubleTriangleRemoval

/-! Two applications of triangle removal give common anchors for a positive-density family of triples. -/

namespace TriangleAnchors

open Finset Fintype SimpleGraph TripartiteFromTriangles

variable {P : Type*}

/-- Three projected pair edges, possibly supplied by different records. -/
def shadowAt (T : Finset (P × P × P)) (x y z : P) : Prop :=
  (∃ w, (x,y,w) ∈ T) ∧ (∃ w, (x,w,z) ∈ T) ∧ (∃ w, (w,y,z) ∈ T)

theorem shadow_mono {T U : Finset (P × P × P)} (h : T ⊆ U) {x y z : P}
    (hT : shadowAt T x y z) : shadowAt U x y z := by
  obtain ⟨⟨u,hu⟩,⟨v,hv⟩,⟨w,hw⟩⟩ := hT
  exact ⟨⟨u,h hu⟩,⟨v,h hv⟩,⟨w,h hw⟩⟩

noncomputable def shadows [Fintype P] (T : Finset (P × P × P)) : Finset (P × P × P) := by
  classical
  exact univ.filter fun t => shadowAt T t.1 t.2.1 t.2.2

theorem many_shadows [Fintype P] (T : Finset (P × P × P)) [ExplicitDisjoint T]
    (δ : ℝ) (hδ : 0 < δ) (hT : δ * (Fintype.card P : ℝ)^2 ≤ T.card) :
    triangleRemovalBound (δ / 9) * (Fintype.card P : ℝ)^3 ≤ (shadows T).card := by
  classical
  have hfar : (graph T).FarFromTriangleFree (δ/9) := by
    apply farFromTriangleFree
    push_cast
    nlinarith only [hT]
  have hsz := hfar.le_card_cliqueFinset
  have hsub : (graph T).cliqueFinset 3 ⊆ (shadows T).map toTriangle := by
    intro s hs
    obtain ⟨u,v,w, huv,huw,hvw,rfl⟩ := SimpleGraph.is3Clique_iff.mp (mem_cliqueFinset_iff.mp hs)
    obtain ⟨x,y,z,he,hxy,hxz,hyz⟩ := graph_triple huv huw hvw
    apply mem_map.mpr
    refine ⟨(x,y,z),?_,he⟩
    apply mem_filter.mpr
    exact ⟨mem_univ _,Graph.in₀₁_iff.mp hxy,Graph.in₀₂_iff.mp hxz,Graph.in₁₂_iff.mp hyz⟩
  have hsize : ((graph T).cliqueFinset 3).card ≤ (shadows T).card := by
    simpa using card_le_card hsub
  have hh : (Fintype.card P : ℝ)^3 ≤ (Fintype.card (P ⊕ P ⊕ P) : ℝ)^3 := by
    simp only [Fintype.card_sum, Nat.cast_add]
    apply pow_le_pow_left₀ (by positivity)
    linarith [(Nat.cast_nonneg (Fintype.card P) : (0:ℝ) ≤ Fintype.card P)]
  exact ((mul_le_mul_of_nonneg_left hh (triangleRemovalBound_pos (by positivity)).le).trans hsz).trans
    (by exact_mod_cast hsize)


private theorem max_fiber [Fintype P] [Nonempty P] {E : Type*}
    (Q : Finset E) (pick : E → P) (sz : P → ℕ) [DecidableEq P]
    (hb : ∀ p : P, (Q.filter (fun e => pick e = p)).card ≤ sz p) :
    ∃ p, Q.card ≤ Fintype.card P * sz p := by
  classical
  obtain ⟨p, _, hm⟩ := (univ : Finset P).exists_max_image sz univ_nonempty
  refine ⟨p, ?_⟩
  calc
    Q.card = ∑ z : P, (Q.filter fun e => pick e = z).card :=
      Finset.card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
    _ ≤ ∑ _z : P, sz p := Finset.sum_le_sum fun z hz => (hb z).trans (hm z hz)
    _ = _ := by simp

/-- The first anchor is adjacent to the two endpoint roles of many genuine records. -/
theorem y_anchor [Fintype P] [Nonempty P] (T : Finset (P × P × P)) :
    ∃ (y : P) (U : Finset (P × P × P)), U ⊆ T ∧
      (shadows T).card ≤ Fintype.card P * U.card ∧ ∀ t ∈ U, shadowAt T t.1 y t.2.2 := by
  classical
  let F (y : P) := T.filter fun t => shadowAt T t.1 y t.2.2
  obtain ⟨y,hy⟩ := max_fiber (shadows T) (fun t => t.2.1) (fun y => (F y).card) (by
    intro y
    have hs : ((shadows T).filter fun t => t.2.1 = y) ⊆
        (F y).image (fun t => (t.1,y,t.2.2)) := by
      rintro ⟨x,b,z⟩ h
      obtain ⟨hs,hb⟩ := mem_filter.mp h
      change b = y at hb
      subst b
      have ht : shadowAt T x y z := (mem_filter.mp hs).2
      obtain ⟨w,hw⟩ := ht.2.1
      exact mem_image.mpr ⟨(x,w,z),mem_filter.mpr ⟨hw,ht⟩,rfl⟩
    exact (card_le_card hs).trans card_image_le)
  exact ⟨y,F y,filter_subset _ _,hy,fun _ h => (mem_filter.mp h).2⟩

/-- The second anchor is adjacent to the first two roles of many genuine records. -/
theorem z_anchor [Fintype P] [Nonempty P] (T : Finset (P × P × P)) :
    ∃ (z : P) (U : Finset (P × P × P)), U ⊆ T ∧
      (shadows T).card ≤ Fintype.card P * U.card ∧ ∀ t ∈ U, shadowAt T t.1 t.2.1 z := by
  classical
  let F (z : P) := T.filter fun t => shadowAt T t.1 t.2.1 z
  obtain ⟨z,hz⟩ := max_fiber (shadows T) (fun t => t.2.2) (fun z => (F z).card) (by
    intro z
    have hs : ((shadows T).filter fun t => t.2.2 = z) ⊆
        (F z).image (fun t => (t.1,t.2.1,z)) := by
      rintro ⟨x,y,b⟩ h
      obtain ⟨hs,hb⟩ := mem_filter.mp h
      change b = z at hb
      subst b
      have ht : shadowAt T x y z := (mem_filter.mp hs).2
      obtain ⟨w,hw⟩ := ht.1
      exact mem_image.mpr ⟨(x,y,w),mem_filter.mpr ⟨hw,ht⟩,rfl⟩
    exact (card_le_card hs).trans card_image_le)
  exact ⟨z,F z,filter_subset _ _,hz,fun _ h => (mem_filter.mp h).2⟩


private theorem pass_density [Fintype P] [Nonempty P] {γ : ℝ}
    {T U : Finset (P × P × P)} (ht : γ * (Fintype.card P : ℝ)^3 ≤ (shadows T).card)
    (hu : (shadows T).card ≤ Fintype.card P * U.card) :
    γ * (Fintype.card P : ℝ)^2 ≤ U.card := by
  have hz : (0:ℝ) < Fintype.card P := by exact_mod_cast Fintype.card_pos
  have he : ((shadows T).card : ℝ) ≤ (Fintype.card P : ℝ) * U.card := by exact_mod_cast hu
  apply (le_of_mul_le_mul_left ?_ hz)
  nlinarith only [ht,he]

/-- Two applications of Mathlib's triangle removal lemma find a positive-density
subfamily on which all three anchored triangles exist in the original graph. -/
theorem two_anchors [Fintype P] [Nonempty P] (δ : ℝ) (hδ : 0 < δ)
    (T : Finset (P × P × P)) [ExplicitDisjoint T]
    (hd : δ * (Fintype.card P : ℝ)^2 ≤ T.card) :
    ∃ (y z : P) (U : Finset (P × P × P)), U ⊆ T ∧
      triangleRemovalBound (triangleRemovalBound (δ/9)/9) * (Fintype.card P : ℝ)^2 ≤ U.card ∧
      ∀ t ∈ U, shadowAt T t.1 y t.2.2 ∧ shadowAt T t.1 t.2.1 z ∧ shadowAt T t.1 y z := by
  classical
  obtain ⟨y,U,hUT,hUy,hy⟩ := y_anchor T
  have : ExplicitDisjoint U := {
    inj₀ := fun {_ _ _ _} h h' => ExplicitDisjoint.inj₀ (hUT h) (hUT h')
    inj₁ := fun {_ _ _ _} h h' => ExplicitDisjoint.inj₁ (hUT h) (hUT h')
    inj₂ := fun {_ _ _ _} h h' => ExplicitDisjoint.inj₂ (hUT h) (hUT h') }
  have hdU := pass_density (many_shadows T δ hδ hd) hUy
  obtain ⟨z,V,hVU,hVz,hz⟩ := z_anchor U
  have hdV := pass_density (many_shadows U _ (triangleRemovalBound_pos (by positivity)) hdU) hVz
  refine ⟨y,z,V,hVU.trans hUT,hdV,?_⟩
  intro t ht
  have h₁ := hy t (hVU ht)
  have h₂ := hz t ht
  have h₃ := shadow_mono hUT h₂
  obtain ⟨w,hw⟩ := h₂.2.1
  have hcross := hy (t.1,w,z) hw
  exact ⟨h₁,h₃,h₁.1,h₃.2.1,hcross.2.2⟩

end TriangleAnchors

open EuclideanGeometry SimpleGraph SimpleGraph.TripartiteFromTriangles

theorem OMA.boundedRatioTwoAnchors : OMA.R_Erdos101_erdos_101_R2_H2_R1.H1 := by
  intro δ hδ
  refine ⟨triangleRemovalBound (triangleRemovalBound (δ/9)/9),
    triangleRemovalBound_pos (div_pos (triangleRemovalBound_pos (by positivity)) (by norm_num)),?_⟩
  intro S hS T ht hd
  obtain ⟨p,hp⟩ := hS
  have : Nonempty S := ⟨⟨p,hp⟩⟩
  have : ExplicitDisjoint T := ht
  simpa [TriangleAnchors.shadowAt] using
    TriangleAnchors.two_anchors δ hδ T (by simpa using hd)

end DoubleTriangleRemoval

theorem OMA.solution : OMA.R_Erdos101_erdos_101_R2_H2_R1.H1 := by
  exact OMA.boundedRatioTwoAnchors
