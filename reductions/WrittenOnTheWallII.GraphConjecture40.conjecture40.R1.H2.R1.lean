import OMAReductions.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1
import Mathlib

/-!
# Reduction of the non-bipartite step `H2` of Written on the Wall II - Conjecture 40

Let `B` be a largest induced bipartite subgraph of a non-bipartite graph `G` and `O` its
complement (a minimum odd cycle transversal). Every vertex `o` of `O` has two neighbours in `B`
of different colours (otherwise `B` plus `o` would be a larger induced bipartite subgraph), and
`B` has an edge. If `G[O]` is covered by at most two paths, link one end of each of these paths
to such a neighbour, chosen so that the (at most two) linked vertices of `B` get different colours.
If `B` has a path cover in which both linked vertices are path ends and whose size is at most
`2 f(B) - |B| - 1`, the links merge every path of `O` into a path of `B`, so `G` has a path cover
of the same size, which gives `p(G) + b(G) + 1 ≤ 2 f(G)`.

The first residual `H1` is this two-endpoint statement for connected bipartite graphs (two
prescribed ends of different colours); the form needed for the possibly disconnected `B` is
derived from it component by component. The second residual `H2` is the step `H2`
of the reduction `R1` restricted to graphs in which every minimum odd cycle transversal needs
at least three paths to cover it.
-/

namespace OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H2_R1

open SimpleGraph

/-- `S2`: in a connected bipartite graph (with proper 2-colouring `c`), for any two vertices
`x`, `y` of different colours there is a path cover with at most `2 f - n - 1` paths in which
`x` and `y` are ends of their paths. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (H : SimpleGraph V) (c : V → Fin 2),
    (∀ u v, H.Adj u v → c u ≠ c v) → H.Connected → ∀ x y : V, c x ≠ c y →
    ∃ P : Finset (Finset V), H.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (q : H.Walk u v), q.IsPath ∧ s = q.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card V + 1 ≤ 2 * H.largestInducedForestSize

/-- The class of the step `H2` of `R1` (2-connected non-bipartite graphs above the scattering
bound and above the path cover number of every maximum induced bipartite subgraph), restricted
to graphs in which the complement of every maximum induced bipartite subgraph has path cover
number at least three. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    3 ≤ Fintype.card V →
    G.Connected →
    (∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected) →
    ¬ G.IsBipartite →
    (∀ S : Finset V,
      Nat.card (G.induce (S : Set V)ᶜ).ConnectedComponent < G.pathCoverNumber + S.card) →
    (∀ B : Finset V,
      (G.induce (B : Set V)).IsBipartite →
      B.card = G.largestInducedBipartiteSubgraphSize →
      (G.induce (B : Set V)).pathCoverNumber < G.pathCoverNumber) →
    (∀ B : Finset V,
      (G.induce (B : Set V)).IsBipartite →
      B.card = G.largestInducedBipartiteSubgraphSize →
      2 < (G.induce ((Bᶜ : Finset V) : Set V)).pathCoverNumber) →
    G.pathCoverNumber + G.largestInducedBipartiteSubgraphSize + 1 ≤ 2 * G.largestInducedForestSize

section

variable {V : Type} [Fintype V] [DecidableEq V]

lemma nb0_fin2 (a b d : Fin 2) (h1 : a ≠ b) (h2 : a ≠ d) (h3 : b ≠ d) : False := by
  revert a b d; decide

lemma nb0_rb_refl (G : SimpleGraph V) (B : Finset V) {x : V} (hx : x ∈ B) : (∃ (hx₀ : (x : V) ∈ (B : Finset V)) (hy₀ : (x : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(x : V), hx₀⟩ ⟨(x : V), hy₀⟩) :=
  ⟨hx, hx, Reachable.refl _⟩

lemma nb0_rb_symm {G : SimpleGraph V} {B : Finset V} {x y : V} (h : (∃ (hx₀ : (x : V) ∈ (B : Finset V)) (hy₀ : (y : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(x : V), hx₀⟩ ⟨(y : V), hy₀⟩)) : (∃ (hx₀ : (y : V) ∈ (B : Finset V)) (hy₀ : (x : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(y : V), hx₀⟩ ⟨(x : V), hy₀⟩) := by
  obtain ⟨hx, hy, h⟩ := h
  exact ⟨hy, hx, h.symm⟩

lemma nb0_rb_trans {G : SimpleGraph V} {B : Finset V} {x y z : V} (h1 : (∃ (hx₀ : (x : V) ∈ (B : Finset V)) (hy₀ : (y : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(x : V), hx₀⟩ ⟨(y : V), hy₀⟩))
    (h2 : (∃ (hx₀ : (y : V) ∈ (B : Finset V)) (hy₀ : (z : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(y : V), hx₀⟩ ⟨(z : V), hy₀⟩)) : (∃ (hx₀ : (x : V) ∈ (B : Finset V)) (hy₀ : (z : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(x : V), hx₀⟩ ⟨(z : V), hy₀⟩) := by
  obtain ⟨hx, hy, h1⟩ := h1
  obtain ⟨hy', hz, h2⟩ := h2
  exact ⟨hx, hz, h1.trans h2⟩

lemma nb0_rb_adj {G : SimpleGraph V} {B : Finset V} {x y : V} (hx : x ∈ B) (hy : y ∈ B)
    (h : G.Adj x y) : (∃ (hx₀ : (x : V) ∈ (B : Finset V)) (hy₀ : (y : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(x : V), hx₀⟩ ⟨(y : V), hy₀⟩) :=
  ⟨hx, hy, Adj.reachable (G := G.induce (B : Set V)) (u := ⟨x, hx⟩) (v := ⟨y, hy⟩) h⟩

lemma nb0_rb_mono {G : SimpleGraph V} {B B' : Finset V} (hBB : B ⊆ B') {x y : V}
    (h : (∃ (hx₀ : (x : V) ∈ (B : Finset V)) (hy₀ : (y : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(x : V), hx₀⟩ ⟨(y : V), hy₀⟩)) : (∃ (hx₀ : (x : V) ∈ (B' : Finset V)) (hy₀ : (y : V) ∈ (B' : Finset V)), (G.induce ((B' : Finset V) : Set V)).Reachable ⟨(x : V), hx₀⟩ ⟨(y : V), hy₀⟩) := by
  obtain ⟨hx, hy, h⟩ := h
  have hs : (B : Set V) ⊆ (B' : Set V) := Finset.coe_subset.mpr hBB
  exact ⟨hBB hx, hBB hy, h.map (G.induceHomOfLE hs).toHom⟩

lemma nb0_rb_ne_adj {G : SimpleGraph V} {B : Finset V} {x y : V} (h : (∃ (hx₀ : (x : V) ∈ (B : Finset V)) (hy₀ : (y : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(x : V), hx₀⟩ ⟨(y : V), hy₀⟩)) (hne : x ≠ y) :
    ∃ a ∈ B, ∃ b ∈ B, G.Adj a b := by
  obtain ⟨hx, hy, ⟨p⟩⟩ := h
  cases p with
  | nil => exact (hne rfl).elim
  | @cons _ w _ h _ => exact ⟨x, hx, w.1, w.2, h⟩

lemma nb0_card_le_bip (G : SimpleGraph V) (T : Finset V) (hT : (G.induce (T : Set V)).IsBipartite) :
    T.card ≤ G.largestInducedBipartiteSubgraphSize := by
  unfold SimpleGraph.largestInducedBipartiteSubgraphSize
  apply le_csSup
  · exact ⟨Fintype.card V, fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  · exact ⟨T, hT, rfl⟩

lemma nb0_card_le_forest (G : SimpleGraph V) (F : Finset V) (hF : (G.induce (F : Set V)).IsAcyclic) :
    F.card ≤ G.largestInducedForestSize := by
  unfold SimpleGraph.largestInducedForestSize
  apply le_csSup
  · exact ⟨Fintype.card V, fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  · exact ⟨F, hF, rfl⟩

lemma nb0_exists_bip (G : SimpleGraph V) :
    ∃ B : Finset V, (G.induce (B : Set V)).IsBipartite ∧
      B.card = G.largestInducedBipartiteSubgraphSize := by
  have hne : { n | ∃ s : Finset V, (G.induce (s : Set V)).IsBipartite ∧ s.card = n }.Nonempty := by
    refine ⟨0, ∅, ?_, rfl⟩
    rw [SimpleGraph.induce_isBipartite_iff_exists_coloring]
    exact ⟨fun _ => 0, by simp⟩
  have hbdd : BddAbove { n | ∃ s : Finset V, (G.induce (s : Set V)).IsBipartite ∧ s.card = n } :=
    ⟨Fintype.card V, fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  exact Nat.sSup_mem hne hbdd

/-- Forest number of an induced subgraph, realised by a subset. -/
lemma nb0_exists_forest_sub (G : SimpleGraph V) (S : Finset V) :
    ∃ F : Finset V, F ⊆ S ∧ (G.induce (F : Set V)).IsAcyclic ∧
      F.card = (G.induce (S : Set V)).largestInducedForestSize := by
  have hne : { n | ∃ s : Finset (S : Set V), ((G.induce (S : Set V)).induce (s : Set (S : Set V))).IsAcyclic ∧ s.card = n }.Nonempty := by
    refine ⟨0, ∅, ?_, rfl⟩
    intro u
    exact False.elim (Finset.notMem_empty u.1 u.2)
  have hbdd : BddAbove { n | ∃ s : Finset (S : Set V), ((G.induce (S : Set V)).induce (s : Set (S : Set V))).IsAcyclic ∧ s.card = n } :=
    ⟨Fintype.card (S : Set V), fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  obtain ⟨F', hF'ac, hF'card⟩ := Nat.sSup_mem hne hbdd
  let F : Finset V := F'.image Subtype.val
  have hFS : F ⊆ S := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨⟨y, hy⟩, _, rfl⟩
    exact hy
  have hcard : F.card = F'.card := Finset.card_image_of_injective F' Subtype.val_injective
  refine ⟨F, hFS, ?_, hcard.trans hF'card⟩
  intro u c hc
  have hmemF' : ∀ x : (F : Set V), (⟨x.1, hFS x.2⟩ : (S : Set V)) ∈ F' := by
    intro x
    rcases Finset.mem_image.mp x.2 with ⟨⟨y, hy⟩, hyF', hyx⟩
    have heq : (⟨x.1, hFS x.2⟩ : (S : Set V)) = ⟨y, hy⟩ := Subtype.ext hyx.symm
    exact heq ▸ hyF'
  let f : G.induce (F : Set V) →g (G.induce (S : Set V)).induce (F' : Set (S : Set V)) :=
    { toFun := fun x => ⟨⟨x.1, hFS x.2⟩, hmemF' x⟩
      map_rel' := fun hadj => hadj }
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z => z.1.1) hab
  exact hF'ac (c.map f) (hc.map hfinj)

/-- An acyclic induced subgraph `F ⊆ S` gives a lower bound for the forest number of `G[S]`. -/
lemma nb0_card_le_induce_forest (G : SimpleGraph V) (S F : Finset V) (hFS : F ⊆ S)
    (hF : (G.induce (F : Set V)).IsAcyclic) :
    F.card ≤ (G.induce (S : Set V)).largestInducedForestSize := by
  let F' : Finset (S : Set V) := Finset.univ.filter (fun x : (S : Set V) => x.1 ∈ F)
  have hcard : F'.card = F.card := by
    have himg : F'.image Subtype.val = F := by
      ext x
      simp only [F', Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨⟨y, _⟩, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨⟨x, hFS hx⟩, hx, rfl⟩
    rw [← himg, Finset.card_image_of_injective _ Subtype.val_injective]
  rw [← hcard]
  apply nb0_card_le_forest
  intro u c hc
  let f : ((G.induce (S : Set V)).induce (F' : Set (S : Set V))) →g G.induce (F : Set V) :=
    { toFun := fun x => ⟨x.1.1, (Finset.mem_filter.mp x.2).2⟩
      map_rel' := fun hadj => hadj }
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z => z.1) hab
  exact hF (c.map f) (hc.map hfinj)

lemma nb0_mem_support_map {S : Set V} {G : SimpleGraph V} {a b : S} (p : (G.induce S).Walk a b)
    {x : V} (hx : x ∈ (p.map (Embedding.induce (G := G) S).toHom).support) :
    ∃ y ∈ p.support, y.1 = x := by
  rw [Walk.support_map, List.mem_map] at hx
  exact hx

lemma nb0_support_map_eq {S : Set V} {G : SimpleGraph V} {a b : S} (p : (G.induce S).Walk a b) :
    (p.map (Embedding.induce (G := G) S).toHom).support.toFinset =
      p.support.toFinset.image Subtype.val := by
  rw [Walk.support_map]
  ext x
  rw [List.mem_toFinset, List.mem_map, Finset.mem_image]
  simp only [List.mem_toFinset]
  rfl

/-- A walk with all vertices in `F1 ∪ F2`, starting in `F1`, with no edge between `F1` and `F2`,
stays in `F1`. -/
lemma nb0_walk_stays (G : SimpleGraph V) (F1 F2 : Finset V)
    (hno : ∀ a ∈ F1, ∀ b ∈ F2, ¬ G.Adj a b) {a b : V} (w : G.Walk a b)
    (hw : ∀ x ∈ w.support, x ∈ F1 ∪ F2) (ha : a ∈ F1) : ∀ x ∈ w.support, x ∈ F1 := by
  induction w with
  | nil =>
    intro x hx
    rw [Walk.support_nil, List.mem_singleton] at hx
    exact hx ▸ ha
  | @cons u v w' h p ih =>
    have hv : v ∈ F1 := by
      have hv' : v ∈ F1 ∪ F2 := hw v (by simp)
      rcases Finset.mem_union.mp hv' with h1 | h2
      · exact h1
      · exact (hno u ha v h2 h).elim
    intro x hx
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact ha
    · exact ih (fun y hy => hw y (by simp [hy])) hv x hx

lemma nb0_acyclic_union (G : SimpleGraph V) (F1 F2 : Finset V)
    (h1 : (G.induce (F1 : Set V)).IsAcyclic) (h2 : (G.induce (F2 : Set V)).IsAcyclic)
    (hno : ∀ a ∈ F1, ∀ b ∈ F2, ¬ G.Adj a b) :
    (G.induce ((F1 ∪ F2 : Finset V) : Set V)).IsAcyclic := by
  intro u c hc
  let w : G.Walk u.1 u.1 := c.map (Embedding.induce (G := G) _).toHom
  have hwc : w.IsCycle := hc.map (Embedding.induce (G := G) _).injective
  have hw : ∀ x ∈ w.support, x ∈ F1 ∪ F2 := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := nb0_mem_support_map c hx
    exact y.2
  have hu : u.1 ∈ F1 ∪ F2 := u.2
  rcases Finset.mem_union.mp hu with hu1 | hu2
  · have hs := nb0_walk_stays G F1 F2 hno w hw hu1
    have hcyc : (w.induce (F1 : Set V) (fun x hx => Finset.mem_coe.mpr (hs x hx))).IsCycle := by
      rw [← Walk.isCycle_map_iff_of_injective (f := (Embedding.induce (G := G) (F1 : Set V)).toHom)
        (Embedding.induce (G := G) (F1 : Set V)).injective, Walk.map_induce]
      exact hwc
    exact h1 _ hcyc
  · have hno' : ∀ a ∈ F2, ∀ b ∈ F1, ¬ G.Adj a b := fun a ha b hb hab => hno b hb a ha hab.symm
    have hw' : ∀ x ∈ w.support, x ∈ F2 ∪ F1 := fun x hx => by
      rw [Finset.union_comm]; exact hw x hx
    have hs := nb0_walk_stays G F2 F1 hno' w hw' hu2
    have hcyc : (w.induce (F2 : Set V) (fun x hx => Finset.mem_coe.mpr (hs x hx))).IsCycle := by
      rw [← Walk.isCycle_map_iff_of_injective (f := (Embedding.induce (G := G) (F2 : Set V)).toHom)
        (Embedding.induce (G := G) (F2 : Set V)).injective, Walk.map_induce]
      exact hwc
    exact h2 _ hcyc

lemma nb0_forest_superadd (G : SimpleGraph V) (K R : Finset V) (hKR : Disjoint K R)
    (hno : ∀ a ∈ K, ∀ b ∈ R, ¬ G.Adj a b) :
    (G.induce (K : Set V)).largestInducedForestSize + (G.induce (R : Set V)).largestInducedForestSize
      ≤ (G.induce ((K ∪ R : Finset V) : Set V)).largestInducedForestSize := by
  obtain ⟨F1, hF1K, hF1, hF1c⟩ := nb0_exists_forest_sub G K
  obtain ⟨F2, hF2R, hF2, hF2c⟩ := nb0_exists_forest_sub G R
  have hd : Disjoint F1 F2 := Finset.disjoint_of_subset_left hF1K (Finset.disjoint_of_subset_right hF2R hKR)
  have hac := nb0_acyclic_union G F1 F2 hF1 hF2 (fun a ha b hb => hno a (hF1K ha) b (hF2R hb))
  have := nb0_card_le_induce_forest G (K ∪ R) (F1 ∪ F2) (Finset.union_subset_union hF1K hF2R) hac
  rw [Finset.card_union_of_disjoint hd, hF1c, hF2c] at this
  exact this

lemma nb0_forest_le_G (G : SimpleGraph V) (S : Finset V) :
    (G.induce (S : Set V)).largestInducedForestSize ≤ G.largestInducedForestSize := by
  obtain ⟨F, _, hF, hFc⟩ := nb0_exists_forest_sub G S
  rw [← hFc]
  exact nb0_card_le_forest G F hF

lemma nb0_forest_singleton (G : SimpleGraph V) (v : V) :
    1 ≤ (G.induce (({v} : Finset V) : Set V)).largestInducedForestSize := by
  have hac : (G.induce (({v} : Finset V) : Set V)).IsAcyclic := by
    intro u c hc
    cases c with
    | nil => exact hc.ne_nil rfl
    | @cons _ w _ h _ =>
      apply h.ne
      apply Subtype.ext
      have h1 := Finset.mem_singleton.mp (Finset.mem_coe.mp u.2)
      have h2 := Finset.mem_singleton.mp (Finset.mem_coe.mp w.2)
      rw [h1, h2]
  have := nb0_card_le_induce_forest G {v} {v} (Finset.Subset.refl _) hac
  simpa using this

/- Path covers on vertex sets -/

lemma nb0_cover_univ (G : SimpleGraph V) (P : Finset (Finset V)) (Z : Finset V)
    (h : ((∀ t₁ ∈ (P : Finset (Finset V)), ∀ t₂ ∈ (P : Finset (Finset V)), t₁ ≠ t₂ → Disjoint t₁ t₂) ∧ (P : Finset (Finset V)).biUnion id = (Finset.univ : Finset V) ∧ (∀ t ∈ (P : Finset (Finset V)), ∃ (u₀ v₀ : V) (q₀ : G.Walk u₀ v₀), q₀.IsPath ∧ t = q₀.support.toFinset ∧ ∀ z₀ ∈ (Z : Finset V), z₀ ∈ t → z₀ = u₀ ∨ z₀ = v₀))) : G.pathCoverNumber ≤ P.card := by
  unfold SimpleGraph.pathCoverNumber
  apply Nat.sInf_le
  refine ⟨P, rfl, h.1, ?_, ?_⟩
  · rw [h.2.1]
  · intro s hs
    obtain ⟨u, v, q, hq, hs, _⟩ := h.2.2 s hs
    exact ⟨u, v, q, hq, hs⟩

lemma nb0_cover_sub {G : SimpleGraph V} {S : Finset V} {P : Finset (Finset V)} {Z : Finset V}
    (h : ((∀ t₁ ∈ (P : Finset (Finset V)), ∀ t₂ ∈ (P : Finset (Finset V)), t₁ ≠ t₂ → Disjoint t₁ t₂) ∧ (P : Finset (Finset V)).biUnion id = (S : Finset V) ∧ (∀ t ∈ (P : Finset (Finset V)), ∃ (u₀ v₀ : V) (q₀ : G.Walk u₀ v₀), q₀.IsPath ∧ t = q₀.support.toFinset ∧ ∀ z₀ ∈ (Z : Finset V), z₀ ∈ t → z₀ = u₀ ∨ z₀ = v₀))) {s : Finset V} (hs : s ∈ P) : s ⊆ S := by
  rw [← h.2.1]
  exact Finset.subset_biUnion_of_mem id hs

lemma nb0_cover_singleton (G : SimpleGraph V) (v : V) (Z : Finset V) :
    ((∀ t₁ ∈ ({{v}} : Finset (Finset V)), ∀ t₂ ∈ ({{v}} : Finset (Finset V)), t₁ ≠ t₂ → Disjoint t₁ t₂) ∧ ({{v}} : Finset (Finset V)).biUnion id = ({v} : Finset V) ∧ (∀ t ∈ ({{v}} : Finset (Finset V)), ∃ (u₀ v₀ : V) (q₀ : G.Walk u₀ v₀), q₀.IsPath ∧ t = q₀.support.toFinset ∧ ∀ z₀ ∈ (Z : Finset V), z₀ ∈ t → z₀ = u₀ ∨ z₀ = v₀)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s1 hs1 s2 hs2 hne
    rw [Finset.mem_singleton] at hs1 hs2
    exact (hne (hs1.trans hs2.symm)).elim
  · simp
  · intro s hs
    rw [Finset.mem_singleton] at hs
    subst hs
    refine ⟨v, v, Walk.nil, Walk.IsPath.nil, by simp, ?_⟩
    intro z _ hz
    exact Or.inl (Finset.mem_singleton.mp hz)

lemma nb0_cover_union {G : SimpleGraph V} {S1 S2 : Finset V} {P1 P2 : Finset (Finset V)}
    {Z : Finset V} (h1 : ((∀ t₁ ∈ (P1 : Finset (Finset V)), ∀ t₂ ∈ (P1 : Finset (Finset V)), t₁ ≠ t₂ → Disjoint t₁ t₂) ∧ (P1 : Finset (Finset V)).biUnion id = (S1 : Finset V) ∧ (∀ t ∈ (P1 : Finset (Finset V)), ∃ (u₀ v₀ : V) (q₀ : G.Walk u₀ v₀), q₀.IsPath ∧ t = q₀.support.toFinset ∧ ∀ z₀ ∈ (Z : Finset V), z₀ ∈ t → z₀ = u₀ ∨ z₀ = v₀))) (h2 : ((∀ t₁ ∈ (P2 : Finset (Finset V)), ∀ t₂ ∈ (P2 : Finset (Finset V)), t₁ ≠ t₂ → Disjoint t₁ t₂) ∧ (P2 : Finset (Finset V)).biUnion id = (S2 : Finset V) ∧ (∀ t ∈ (P2 : Finset (Finset V)), ∃ (u₀ v₀ : V) (q₀ : G.Walk u₀ v₀), q₀.IsPath ∧ t = q₀.support.toFinset ∧ ∀ z₀ ∈ (Z : Finset V), z₀ ∈ t → z₀ = u₀ ∨ z₀ = v₀))) (hd : Disjoint S1 S2) :
    ((∀ t₁ ∈ ((P1 ∪ P2) : Finset (Finset V)), ∀ t₂ ∈ ((P1 ∪ P2) : Finset (Finset V)), t₁ ≠ t₂ → Disjoint t₁ t₂) ∧ ((P1 ∪ P2) : Finset (Finset V)).biUnion id = ((S1 ∪ S2) : Finset V) ∧ (∀ t ∈ ((P1 ∪ P2) : Finset (Finset V)), ∃ (u₀ v₀ : V) (q₀ : G.Walk u₀ v₀), q₀.IsPath ∧ t = q₀.support.toFinset ∧ ∀ z₀ ∈ (Z : Finset V), z₀ ∈ t → z₀ = u₀ ∨ z₀ = v₀)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s1 hs1 s2 hs2 hne
    rcases Finset.mem_union.mp hs1 with hs1 | hs1 <;> rcases Finset.mem_union.mp hs2 with hs2 | hs2
    · exact h1.1 s1 hs1 s2 hs2 hne
    · exact Finset.disjoint_of_subset_left (nb0_cover_sub h1 hs1)
        (Finset.disjoint_of_subset_right (nb0_cover_sub h2 hs2) hd)
    · exact Finset.disjoint_of_subset_left (nb0_cover_sub h2 hs1)
        (Finset.disjoint_of_subset_right (nb0_cover_sub h1 hs2) hd.symm)
    · exact h2.1 s1 hs1 s2 hs2 hne
  · rw [Finset.union_biUnion, h1.2.1, h2.2.1]
  · intro s hs
    rcases Finset.mem_union.mp hs with hs | hs
    · exact h1.2.2 s hs
    · exact h2.2.2 s hs

/-- Attach a new vertex `o` to the capped end `w` of its path. -/
lemma nb0_cover_extend {G : SimpleGraph V} {S : Finset V} {P : Finset (Finset V)} {Z : Finset V}
    (h : ((∀ t₁ ∈ (P : Finset (Finset V)), ∀ t₂ ∈ (P : Finset (Finset V)), t₁ ≠ t₂ → Disjoint t₁ t₂) ∧ (P : Finset (Finset V)).biUnion id = (S : Finset V) ∧ (∀ t ∈ (P : Finset (Finset V)), ∃ (u₀ v₀ : V) (q₀ : G.Walk u₀ v₀), q₀.IsPath ∧ t = q₀.support.toFinset ∧ ∀ z₀ ∈ (Z : Finset V), z₀ ∈ t → z₀ = u₀ ∨ z₀ = v₀))) {o w : V} (ho : o ∉ S) (hwZ : w ∈ Z) (hwS : w ∈ S) (hadj : G.Adj o w) :
    ∃ P' : Finset (Finset V), ((∀ t₁ ∈ (P' : Finset (Finset V)), ∀ t₂ ∈ (P' : Finset (Finset V)), t₁ ≠ t₂ → Disjoint t₁ t₂) ∧ (P' : Finset (Finset V)).biUnion id = ((insert o S) : Finset V) ∧ (∀ t ∈ (P' : Finset (Finset V)), ∃ (u₀ v₀ : V) (q₀ : G.Walk u₀ v₀), q₀.IsPath ∧ t = q₀.support.toFinset ∧ ∀ z₀ ∈ ((Z.erase w) : Finset V), z₀ ∈ t → z₀ = u₀ ∨ z₀ = v₀)) ∧ P'.card = P.card := by
  have hwU : w ∈ P.biUnion id := by rw [h.2.1]; exact hwS
  obtain ⟨s0, hs0, hws0⟩ := Finset.mem_biUnion.mp hwU
  have hs0S : s0 ⊆ S := nb0_cover_sub h hs0
  obtain ⟨u, v, q, hq, hs0q, hcap⟩ := h.2.2 s0 hs0
  have hq' : ∃ (b : V) (q' : G.Walk w b), q'.IsPath ∧ s0 = q'.support.toFinset ∧
      ∀ z ∈ Z, z ∈ s0 → z = w ∨ z = b := by
    rcases hcap w hwZ hws0 with rfl | rfl
    · exact ⟨v, q, hq, hs0q, hcap⟩
    · refine ⟨u, q.reverse, hq.reverse, ?_, ?_⟩
      · rw [Walk.support_reverse, List.toFinset_reverse]; exact hs0q
      · intro z hz hzs
        rcases hcap z hz hzs with h' | h'
        · exact Or.inr h'
        · exact Or.inl h'
  obtain ⟨b, q', hq'p, hs0q', hcap'⟩ := hq'
  have hoq : o ∉ q'.support := by
    intro hmem
    apply ho
    apply hs0S
    rw [hs0q']
    exact List.mem_toFinset.mpr hmem
  have hnew : (Walk.cons hadj q').IsPath := (Walk.cons_isPath_iff hadj q').mpr ⟨hq'p, hoq⟩
  have hnotin : ∀ s ∈ P, o ∉ s := fun s hs hos => ho (nb0_cover_sub h hs hos)
  have hins : insert o s0 ∉ P.erase s0 := by
    intro hmem
    exact hnotin _ (Finset.mem_of_mem_erase hmem) (Finset.mem_insert_self o s0)
  refine ⟨insert (insert o s0) (P.erase s0), ⟨?_, ?_, ?_⟩, ?_⟩
  · intro s1 hs1 s2 hs2 hne
    rcases Finset.mem_insert.mp hs1 with rfl | hs1 <;> rcases Finset.mem_insert.mp hs2 with rfl | hs2
    · exact (hne rfl).elim
    · rw [Finset.disjoint_insert_left]
      refine ⟨hnotin s2 (Finset.mem_of_mem_erase hs2), ?_⟩
      exact h.1 s0 hs0 s2 (Finset.mem_of_mem_erase hs2) (Finset.ne_of_mem_erase hs2).symm
    · rw [Finset.disjoint_insert_right]
      refine ⟨hnotin s1 (Finset.mem_of_mem_erase hs1), ?_⟩
      exact h.1 s1 (Finset.mem_of_mem_erase hs1) s0 hs0 (Finset.ne_of_mem_erase hs1)
    · exact h.1 s1 (Finset.mem_of_mem_erase hs1) s2 (Finset.mem_of_mem_erase hs2) hne
  · have hP : P = insert s0 (P.erase s0) := (Finset.insert_erase hs0).symm
    have hS : S = s0 ∪ (P.erase s0).biUnion id := by
      rw [← h.2.1]
      conv_lhs => rw [hP]
      rw [Finset.biUnion_insert]
      rfl
    rw [Finset.biUnion_insert, hS]
    simp only [id]
    rw [Finset.insert_union]
  · intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · refine ⟨o, b, Walk.cons hadj q', hnew, ?_, ?_⟩
      · rw [Walk.support_cons, List.toFinset_cons, hs0q']
      · intro z hz hzs
        rcases Finset.mem_insert.mp hzs with rfl | hzs
        · exact Or.inl rfl
        · rcases hcap' z (Finset.mem_of_mem_erase hz) hzs with h' | h'
          · exact ((Finset.ne_of_mem_erase hz) h').elim
          · exact Or.inr h'
    · obtain ⟨u1, v1, q1, hq1, hs1, hcap1⟩ := h.2.2 s (Finset.mem_of_mem_erase hs)
      exact ⟨u1, v1, q1, hq1, hs1, fun z hz hzs => hcap1 z (Finset.mem_of_mem_erase hz) hzs⟩
  · rw [Finset.card_insert_of_notMem hins, Finset.card_erase_of_mem hs0]
    have : 1 ≤ P.card := Finset.card_pos.mpr ⟨s0, hs0⟩
    omega

/-- Lift a path cover of `G[K]` (with two capped vertices) to a cover of the vertex set `K`. -/
lemma nb0_cover_lift (G : SimpleGraph V) (K : Finset V) (x y : (K : Set V))
    (P' : Finset (Finset (K : Set V))) (hP' : (G.induce (K : Set V)).IsPathCover P')
    (hcap : ∀ s ∈ P', ∃ (u v : (K : Set V)) (q : (G.induce (K : Set V)).Walk u v), q.IsPath ∧
      s = q.support.toFinset ∧ (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v))
    (Z : Finset V) (hZ : ∀ z ∈ Z, z ∈ K → z = x.1 ∨ z = y.1) :
    ∃ P : Finset (Finset V), ((∀ t₁ ∈ (P : Finset (Finset V)), ∀ t₂ ∈ (P : Finset (Finset V)), t₁ ≠ t₂ → Disjoint t₁ t₂) ∧ (P : Finset (Finset V)).biUnion id = (K : Finset V) ∧ (∀ t ∈ (P : Finset (Finset V)), ∃ (u₀ v₀ : V) (q₀ : G.Walk u₀ v₀), q₀.IsPath ∧ t = q₀.support.toFinset ∧ ∀ z₀ ∈ (Z : Finset V), z₀ ∈ t → z₀ = u₀ ∨ z₀ = v₀)) ∧ P.card ≤ P'.card := by
  refine ⟨P'.image (fun s => s.image Subtype.val), ⟨?_, ?_, ?_⟩, Finset.card_image_le⟩
  · intro s1 hs1 s2 hs2 hne
    rcases Finset.mem_image.mp hs1 with ⟨s1', hs1', rfl⟩
    rcases Finset.mem_image.mp hs2 with ⟨s2', hs2', rfl⟩
    have hne' : s1' ≠ s2' := fun h => hne (by rw [h])
    have hd := hP'.1 s1' hs1' s2' hs2' hne'
    rw [Finset.disjoint_left] at hd ⊢
    intro a ha1 ha2
    rcases Finset.mem_image.mp ha1 with ⟨a1, ha1', rfl⟩
    rcases Finset.mem_image.mp ha2 with ⟨a2, ha2', hab⟩
    have : a1 = a2 := Subtype.ext hab.symm
    exact hd ha1' (this ▸ ha2')
  · ext a
    simp only [Finset.mem_biUnion, Finset.mem_image, id_eq]
    constructor
    · rintro ⟨_, ⟨s', _, rfl⟩, hb⟩
      obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hb
      exact b.2
    · intro ha
      have hmem : (⟨a, ha⟩ : (K : Set V)) ∈ P'.biUnion id := hP'.2.1 (Finset.mem_univ _)
      rcases Finset.mem_biUnion.mp hmem with ⟨s', hs', has'⟩
      exact ⟨_, ⟨s', hs', rfl⟩, Finset.mem_image.mpr ⟨⟨a, ha⟩, has', rfl⟩⟩
  · intro s hs
    rcases Finset.mem_image.mp hs with ⟨s', hs', rfl⟩
    obtain ⟨u, v, q, hq, hsq, hx, hy⟩ := hcap s' hs'
    refine ⟨_, _, q.map (Embedding.induce (G := G) (K : Set V)).toHom,
      hq.map (Embedding.induce (G := G) (K : Set V)).injective, ?_, ?_⟩
    · rw [hsq, nb0_support_map_eq]
    · intro z hz hzs
      rcases Finset.mem_image.mp hzs with ⟨a, has, rfl⟩
      rcases hZ a.1 hz a.2 with h | h
      · have : a = x := Subtype.ext h
        subst this
        rcases hx has with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl
      · have : a = y := Subtype.ext h
        subst this
        rcases hy has with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl

/- One component -/

lemma nb0_exists_nbr (G : SimpleGraph V) (K : Finset V) (hK : (G.induce (K : Set V)).Connected)
    {z a : V} (hz : z ∈ K) (ha : a ∈ K) (hne : a ≠ z) : ∃ y ∈ K, G.Adj z y := by
  obtain ⟨p⟩ := hK.preconnected (⟨z, hz⟩ : (K : Set V)) ⟨a, ha⟩
  cases p with
  | nil => exact (hne rfl).elim
  | @cons _ w _ h _ => exact ⟨w.1, w.2, h⟩

lemma nb0_pick (G : SimpleGraph V) (K : Finset V) (hK : (G.induce (K : Set V)).Connected)
    (hK2 : 2 ≤ K.card) (c : V → Fin 2) (hc : ∀ a ∈ K, ∀ b ∈ K, G.Adj a b → c a ≠ c b)
    (Z : Finset V) (hZ : ∀ z1 ∈ Z, ∀ z2 ∈ Z, z1 ∈ K → z2 ∈ K → z1 ≠ z2 → c z1 ≠ c z2) :
    ∃ x ∈ K, ∃ y ∈ K, c x ≠ c y ∧ ∀ z ∈ Z, z ∈ K → z = x ∨ z = y := by
  have hother : ∀ z ∈ K, ∃ a ∈ K, a ≠ z := by
    intro z hz
    by_contra hcon
    push_neg at hcon
    have : K ⊆ {z} := fun a ha => Finset.mem_singleton.mpr (hcon a ha)
    have := Finset.card_le_card this
    rw [Finset.card_singleton] at this
    omega
  by_cases hz0 : ∃ z ∈ Z, z ∈ K
  · obtain ⟨z, hzZ, hzK⟩ := hz0
    by_cases hz1 : ∃ z' ∈ Z, z' ∈ K ∧ z' ≠ z
    · obtain ⟨z', hz'Z, hz'K, hne⟩ := hz1
      refine ⟨z, hzK, z', hz'K, hZ z hzZ z' hz'Z hzK hz'K hne.symm, ?_⟩
      intro t htZ htK
      by_contra hcon
      push_neg at hcon
      exact nb0_fin2 (c t) (c z) (c z') (hZ t htZ z hzZ htK hzK hcon.1)
        (hZ t htZ z' hz'Z htK hz'K hcon.2) (hZ z hzZ z' hz'Z hzK hz'K hne.symm)
    · push_neg at hz1
      obtain ⟨a, haK, hane⟩ := hother z hzK
      obtain ⟨y, hyK, hzy⟩ := nb0_exists_nbr G K hK hzK haK hane
      exact ⟨z, hzK, y, hyK, hc z hzK y hyK hzy, fun t htZ htK => Or.inl (hz1 t htZ htK)⟩
  · push_neg at hz0
    obtain ⟨z, hzK⟩ : ∃ z, z ∈ K := Finset.card_pos.mp (by omega)
    obtain ⟨a, haK, hane⟩ := hother z hzK
    obtain ⟨y, hyK, hzy⟩ := nb0_exists_nbr G K hK hzK haK hane
    exact ⟨z, hzK, y, hyK, hc z hzK y hyK hzy, fun t htZ htK => (hz0 t htZ htK).elim⟩

/-- `S2` on one connected bipartite vertex set `K` with admissible caps `Z`. -/
lemma nb0_comp_one (hS2 : H1) (G : SimpleGraph V) (K : Finset V)
    (hK : (G.induce (K : Set V)).Connected) (c : V → Fin 2)
    (hc : ∀ a ∈ K, ∀ b ∈ K, G.Adj a b → c a ≠ c b)
    (Z : Finset V) (hZ : ∀ z1 ∈ Z, ∀ z2 ∈ Z, z1 ∈ K → z2 ∈ K → z1 ≠ z2 → c z1 ≠ c z2) :
    ∃ P : Finset (Finset V), ((∀ t₁ ∈ (P : Finset (Finset V)), ∀ t₂ ∈ (P : Finset (Finset V)), t₁ ≠ t₂ → Disjoint t₁ t₂) ∧ (P : Finset (Finset V)).biUnion id = (K : Finset V) ∧ (∀ t ∈ (P : Finset (Finset V)), ∃ (u₀ v₀ : V) (q₀ : G.Walk u₀ v₀), q₀.IsPath ∧ t = q₀.support.toFinset ∧ ∀ z₀ ∈ (Z : Finset V), z₀ ∈ t → z₀ = u₀ ∨ z₀ = v₀)) ∧
      P.card + K.card ≤ 2 * (G.induce (K : Set V)).largestInducedForestSize ∧
      (2 ≤ K.card → P.card + K.card + 1 ≤ 2 * (G.induce (K : Set V)).largestInducedForestSize) := by
  obtain ⟨v0, hv0⟩ : ∃ v, v ∈ K := by
    obtain ⟨⟨v, hv⟩⟩ := hK.nonempty
    exact ⟨v, hv⟩
  by_cases hK2 : 2 ≤ K.card
  · obtain ⟨x, hxK, y, hyK, hxy, hZxy⟩ := nb0_pick G K hK hK2 c hc Z hZ
    obtain ⟨P', hP', hcap, hcard⟩ := hS2 (K : Set V) (G.induce (K : Set V)) (fun a => c a.1)
      (fun a b hab => hc a.1 a.2 b.1 b.2 hab) hK ⟨x, hxK⟩ ⟨y, hyK⟩ hxy
    obtain ⟨P, hP, hPc⟩ := nb0_cover_lift G K ⟨x, hxK⟩ ⟨y, hyK⟩ P' hP' hcap Z hZxy
    have hcardK : Fintype.card (K : Set V) = K.card := by simp
    rw [hcardK] at hcard
    refine ⟨P, hP, by omega, fun _ => by omega⟩
  · have hK1 : K = {v0} := by
      apply Finset.eq_singleton_iff_unique_mem.mpr
      refine ⟨hv0, fun a ha => ?_⟩
      by_contra hne
      have : ({a, v0} : Finset V) ⊆ K := by
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact ha
        · rw [Finset.mem_singleton.mp ht]; exact hv0
      have := Finset.card_le_card this
      rw [Finset.card_pair hne] at this
      omega
    subst hK1
    refine ⟨{{v0}}, nb0_cover_singleton G v0 Z, ?_, fun h => (hK2 h).elim⟩
    have := nb0_forest_singleton G v0
    simp only [Finset.card_singleton]
    omega

/- All components (Lemma C) -/

lemma nb0_comp_connected (G : SimpleGraph V) (B K : Finset V) {v : V} (hv : v ∈ B)
    (hK : ∀ x, x ∈ K ↔ x ∈ B ∧ (∃ (hx₀ : (v : V) ∈ (B : Finset V)) (hy₀ : (x : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(v : V), hx₀⟩ ⟨(x : V), hy₀⟩)) :
    (G.induce (K : Set V)).Connected := by
  have hvK : v ∈ K := (hK v).mpr ⟨hv, nb0_rb_refl G B hv⟩
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨v, hvK⟩, ?_⟩
  rintro ⟨x, hxK⟩
  obtain ⟨hv', hx', ⟨p⟩⟩ := ((hK x).mp hxK).2
  let q : G.Walk v x := p.map (Embedding.induce (G := G) (B : Set V)).toHom
  have hq : ∀ y ∈ q.support, y ∈ (K : Set V) := by
    intro y hy
    obtain ⟨y', hy', rfl⟩ := nb0_mem_support_map p hy
    refine Finset.mem_coe.mpr ((hK y'.1).mpr ⟨y'.2, ?_⟩)
    exact ⟨hv', y'.2, (p.takeUntil y' hy').reachable⟩
  exact ⟨q.induce (K : Set V) hq⟩

lemma nb0_lemmaC (hS2 : H1) (G : SimpleGraph V) (c : V → Fin 2) :
    ∀ (m : ℕ) (B : Finset V), B.card = m → (∀ a ∈ B, ∀ b ∈ B, G.Adj a b → c a ≠ c b) →
    ∀ Z : Finset V, (∀ z1 ∈ Z, ∀ z2 ∈ Z, z1 ≠ z2 → (∃ (hx₀ : (z1 : V) ∈ (B : Finset V)) (hy₀ : (z2 : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(z1 : V), hx₀⟩ ⟨(z2 : V), hy₀⟩) → c z1 ≠ c z2) →
    ∃ P : Finset (Finset V), ((∀ t₁ ∈ (P : Finset (Finset V)), ∀ t₂ ∈ (P : Finset (Finset V)), t₁ ≠ t₂ → Disjoint t₁ t₂) ∧ (P : Finset (Finset V)).biUnion id = (B : Finset V) ∧ (∀ t ∈ (P : Finset (Finset V)), ∃ (u₀ v₀ : V) (q₀ : G.Walk u₀ v₀), q₀.IsPath ∧ t = q₀.support.toFinset ∧ ∀ z₀ ∈ (Z : Finset V), z₀ ∈ t → z₀ = u₀ ∨ z₀ = v₀)) ∧
      P.card + B.card ≤ 2 * (G.induce (B : Set V)).largestInducedForestSize ∧
      ((∃ a ∈ B, ∃ b ∈ B, G.Adj a b) →
        P.card + B.card + 1 ≤ 2 * (G.induce (B : Set V)).largestInducedForestSize) := by
  classical
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro B hBm hc Z hZ
  by_cases hB : B = ∅
  · subst hB
    refine ⟨∅, ⟨by simp, by simp, by simp⟩, by simp, ?_⟩
    rintro ⟨a, ha, _⟩
    exact (Finset.notMem_empty a ha).elim
  obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr hB
  set K := B.filter (fun x => (∃ (hx₀ : (v : V) ∈ (B : Finset V)) (hy₀ : (x : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(v : V), hx₀⟩ ⟨(x : V), hy₀⟩)) with hKdef
  set R := B.filter (fun x => ¬ (∃ (hx₀ : (v : V) ∈ (B : Finset V)) (hy₀ : (x : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(v : V), hx₀⟩ ⟨(x : V), hy₀⟩)) with hRdef
  have hvK : v ∈ K := Finset.mem_filter.mpr ⟨hv, nb0_rb_refl G B hv⟩
  have hKB : K ⊆ B := Finset.filter_subset _ _
  have hRB : R ⊆ B := Finset.filter_subset _ _
  have hKR : Disjoint K R := Finset.disjoint_filter_filter_not B B _
  have hBKR : K ∪ R = B := Finset.filter_union_filter_not_eq _ B
  have hcardB : K.card + R.card = B.card := by
    rw [← Finset.card_union_of_disjoint hKR, hBKR]
  have hK1 : 1 ≤ K.card := Finset.card_pos.mpr ⟨v, hvK⟩
  have hno : ∀ a ∈ K, ∀ b ∈ R, ¬ G.Adj a b := by
    intro a ha b hb hab
    have hra := (Finset.mem_filter.mp ha).2
    have hb' := Finset.mem_filter.mp hb
    exact hb'.2 (nb0_rb_trans hra (nb0_rb_adj (hKB ha) hb'.1 hab))
  -- the rest
  obtain ⟨PR, hPR, hPRc, hPRe⟩ := ih R.card (by omega) R rfl
    (fun a ha b hb hab => hc a (hRB ha) b (hRB hb) hab) Z
    (fun z1 h1 z2 h2 hne hr => hZ z1 h1 z2 h2 hne (nb0_rb_mono hRB hr))
  -- the component of v
  have hKconn := nb0_comp_connected G B K hv (fun x => Finset.mem_filter)
  obtain ⟨PK, hPK, hPKc, hPKe⟩ := nb0_comp_one hS2 G K hKconn c
    (fun a ha b hb hab => hc a (hKB ha) b (hKB hb) hab) Z
    (fun z1 h1 z2 h2 hz1 hz2 hne => hZ z1 h1 z2 h2 hne
      (nb0_rb_trans (nb0_rb_symm (Finset.mem_filter.mp hz1).2) (Finset.mem_filter.mp hz2).2))
  have hU := nb0_cover_union hPK hPR hKR
  rw [hBKR] at hU
  have hf := nb0_forest_superadd G K R hKR hno
  rw [hBKR] at hf
  have hPc : (PK ∪ PR).card ≤ PK.card + PR.card := Finset.card_union_le _ _
  refine ⟨PK ∪ PR, hU, by omega, ?_⟩
  rintro ⟨a, ha, b, hb, hab⟩
  by_cases haK : a ∈ K
  · have hbK : b ∈ K := by
      by_contra hbK
      have hbR : b ∈ R := by
        rw [← hBKR] at hb
        rcases Finset.mem_union.mp hb with h | h
        · exact (hbK h).elim
        · exact h
      exact hno a haK b hbR hab
    have hab' : a ≠ b := hab.ne
    have h2 : 2 ≤ K.card := by
      have : ({a, b} : Finset V) ⊆ K := by
        intro t ht
        rcases Finset.mem_insert.mp ht with rfl | ht
        · exact haK
        · rw [Finset.mem_singleton.mp ht]; exact hbK
      have := Finset.card_le_card this
      rwa [Finset.card_pair hab'] at this
    have := hPKe h2
    omega
  · have haR : a ∈ R := by
      rw [← hBKR] at ha
      rcases Finset.mem_union.mp ha with h | h
      · exact (haK h).elim
      · exact h
    have hbR : b ∈ R := by
      by_contra hbR
      have hbK : b ∈ K := by
        rw [← hBKR] at hb
        rcases Finset.mem_union.mp hb with h | h
        · exact h
        · exact (hbR h).elim
      exact hno b hbK a haR hab.symm
    have := hPRe ⟨a, haR, b, hbR, hab⟩
    omega

/- Lemma L (an odd pair at every vertex outside a maximum bipartite set) -/

lemma nb0_lemmaL (G : SimpleGraph V) (B : Finset V) (c : V → Fin 2)
    (hc : ∀ a ∈ B, ∀ b ∈ B, G.Adj a b → c a ≠ c b)
    (hmax : G.largestInducedBipartiteSubgraphSize ≤ B.card) {o : V} (ho : o ∉ B) :
    ∃ x ∈ B, ∃ y ∈ B, G.Adj o x ∧ G.Adj o y ∧ (∃ (hx₀ : (x : V) ∈ (B : Finset V)) (hy₀ : (y : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(x : V), hx₀⟩ ⟨(y : V), hy₀⟩) ∧ c x ≠ c y := by
  classical
  by_contra hcon
  push_neg at hcon
  -- hcon : ∀ x ∈ B, ∀ y ∈ B, G.Adj o x → G.Adj o y → (∃ (hx₀ : (x : V) ∈ (B : Finset V)) (hy₀ : (y : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(x : V), hx₀⟩ ⟨(y : V), hy₀⟩) → c x = c y
  let N : V → Prop := fun v => ∃ x ∈ B, G.Adj o x ∧ (∃ (hx₀ : (v : V) ∈ (B : Finset V)) (hy₀ : (x : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(v : V), hx₀⟩ ⟨(x : V), hy₀⟩)
  let d : V → Fin 2 := fun v =>
    if v = o then 0 else if N v then (if ∃ x ∈ B, G.Adj o x ∧ (∃ (hx₀ : (v : V) ∈ (B : Finset V)) (hy₀ : (x : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(v : V), hx₀⟩ ⟨(x : V), hy₀⟩) ∧ c x = c v then 1 else 0)
    else c v
  have hkey : ∀ u ∈ B, ∀ x0 ∈ B, G.Adj o x0 → (∃ (hx₀ : (u : V) ∈ (B : Finset V)) (hy₀ : (x0 : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(u : V), hx₀⟩ ⟨(x0 : V), hy₀⟩) →
      ((∃ x ∈ B, G.Adj o x ∧ (∃ (hx₀ : (u : V) ∈ (B : Finset V)) (hy₀ : (x : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(u : V), hx₀⟩ ⟨(x : V), hy₀⟩) ∧ c x = c u) ↔ c x0 = c u) := by
    intro u hu x0 hx0 hox0 hux0
    constructor
    · rintro ⟨x, hx, hox, hux, hxu⟩
      rw [← hxu]
      exact (hcon x hx x0 hx0 hox hox0 (nb0_rb_trans (nb0_rb_symm hux) hux0)).symm
    · intro h
      exact ⟨x0, hx0, hox0, hux0, h⟩
  have hd : ∀ u ∈ insert o B, ∀ v ∈ insert o B, G.Adj u v → d u ≠ d v := by
    have hside : ∀ v ∈ B, G.Adj o v → d v = 1 := by
      intro v hv hov
      have hvo : v ≠ o := fun h => ho (h ▸ hv)
      have hN : N v := ⟨v, hv, hov, nb0_rb_refl G B hv⟩
      simp only [d, if_neg hvo, if_pos hN]
      rw [if_pos ⟨v, hv, hov, nb0_rb_refl G B hv, rfl⟩]
    intro u hu v hv huv
    by_cases huo : u = o
    · subst huo
      have hvB : v ∈ B := by
        rcases Finset.mem_insert.mp hv with h | h
        · exact (huv.ne h.symm).elim
        · exact h
      rw [hside v hvB huv]
      simp [d]
    by_cases hvo : v = o
    · subst hvo
      have huB : u ∈ B := by
        rcases Finset.mem_insert.mp hu with h | h
        · exact (huo h).elim
        · exact h
      rw [hside u huB huv.symm]
      simp [d]
    have hu : u ∈ B := (Finset.mem_insert.mp hu).resolve_left huo
    have hv : v ∈ B := (Finset.mem_insert.mp hv).resolve_left hvo
    have hcuv := hc u hu v hv huv
    have hruv : (∃ (hx₀ : (u : V) ∈ (B : Finset V)) (hy₀ : (v : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(u : V), hx₀⟩ ⟨(v : V), hy₀⟩) := nb0_rb_adj hu hv huv
    by_cases hNu : N u
    · obtain ⟨x0, hx0, hox0, hux0⟩ := hNu
      have hvx0 : (∃ (hx₀ : (v : V) ∈ (B : Finset V)) (hy₀ : (x0 : V) ∈ (B : Finset V)), (G.induce ((B : Finset V) : Set V)).Reachable ⟨(v : V), hx₀⟩ ⟨(x0 : V), hy₀⟩) := nb0_rb_trans (nb0_rb_symm hruv) hux0
      have hNu' : N u := ⟨x0, hx0, hox0, hux0⟩
      have hNv : N v := ⟨x0, hx0, hox0, hvx0⟩
      simp only [d, if_neg huo, if_neg hvo, if_pos hNu', if_pos hNv]
      by_cases h1 : c x0 = c u
      · have h2 : ¬ c x0 = c v := fun h2 => hcuv (h1.symm.trans h2)
        rw [if_pos ((hkey u hu x0 hx0 hox0 hux0).mpr h1),
          if_neg (fun h => h2 ((hkey v hv x0 hx0 hox0 hvx0).mp h))]
        decide
      · have h2 : c x0 = c v := by
          by_contra h2
          exact nb0_fin2 (c x0) (c u) (c v) h1 h2 hcuv
        rw [if_neg (fun h => h1 ((hkey u hu x0 hx0 hox0 hux0).mp h)),
          if_pos ((hkey v hv x0 hx0 hox0 hvx0).mpr h2)]
        decide
    · have hNv : ¬ N v := by
        rintro ⟨x0, hx0, hox0, hvx0⟩
        exact hNu ⟨x0, hx0, hox0, nb0_rb_trans hruv hvx0⟩
      simp only [d, if_neg huo, if_neg hvo, if_neg hNu, if_neg hNv]
      exact hcuv
  have hbip : (G.induce ((insert o B : Finset V) : Set V)).IsBipartite :=
    (SimpleGraph.induce_isBipartite_iff_exists_coloring G (insert o B)).mpr ⟨d, hd⟩
  have h1 := nb0_card_le_bip G (insert o B) hbip
  rw [Finset.card_insert_of_notMem ho] at h1
  omega

lemma nb0_rb_univ_reachable {G : SimpleGraph V} {x y : V} (h : (∃ (hx₀ : (x : V) ∈ (Finset.univ : Finset V)) (hy₀ : (y : V) ∈ (Finset.univ : Finset V)), (G.induce ((Finset.univ : Finset V) : Set V)).Reachable ⟨(x : V), hx₀⟩ ⟨(y : V), hy₀⟩)) :
    G.Reachable x y := by
  obtain ⟨_, _, h⟩ := h
  exact h.map (Embedding.induce (G := G) _).toHom

/-- Lemma C: connected `S2` implies its component form. -/
theorem nb0_S2comp_of_S2 (hS2 : H1) : (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : G.Coloring (Fin 2))
    (x y : V),
    (G.Reachable x y → c x ≠ c y) →
    (∃ u v : V, G.Adj u v) →
    ∃ P : Finset (Finset V), G.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ s = p.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card V + 1 ≤ 2 * G.largestInducedForestSize) := by
  intro V _ _ G c x y hxy hedge
  obtain ⟨P, hP, _, hPe⟩ := nb0_lemmaC hS2 G (fun v => c v) Finset.univ.card Finset.univ rfl
    (fun a _ b _ hab => c.valid hab) {x, y}
    (by
      intro z1 h1 z2 h2 hne hr
      have h1' : z1 = x ∨ z1 = y := by simpa using h1
      have h2' : z2 = x ∨ z2 = y := by simpa using h2
      have hr' := nb0_rb_univ_reachable hr
      rcases h1' with rfl | rfl <;> rcases h2' with rfl | rfl
      · exact (hne rfl).elim
      · exact hxy hr'
      · exact fun h => hxy hr'.symm h.symm
      · exact (hne rfl).elim)
  obtain ⟨a, b, hab⟩ := hedge
  have h1 := hPe ⟨a, Finset.mem_univ a, b, Finset.mem_univ b, hab⟩
  have hf := nb0_forest_le_G G Finset.univ
  refine ⟨P, ⟨hP.1, by rw [hP.2.1], fun s hs => ?_⟩, fun s hs => ?_, ?_⟩
  · obtain ⟨u, v, q, hq, hsq, _⟩ := hP.2.2 s hs
    exact ⟨u, v, q, hq, hsq⟩
  · obtain ⟨u, v, q, hq, hsq, hcap⟩ := hP.2.2 s hs
    exact ⟨u, v, q, hq, hsq, hcap x (by simp), hcap y (by simp)⟩
  · rw [Finset.card_univ] at h1
    omega

end

section

variable {V : Type} [Fintype V] [DecidableEq V]

lemma exists_pathCover_card_eq {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) :
    ∃ P : Finset (Finset α), P.card = G.pathCoverNumber ∧ G.IsPathCover P := by
  have hne : { k | ∃ P : Finset (Finset α), P.card = k ∧ G.IsPathCover P }.Nonempty := by
    refine ⟨(Finset.univ.image (fun x : α => ({x} : Finset α))).card,
      Finset.univ.image (fun x : α => ({x} : Finset α)), rfl, ?_, ?_, ?_⟩
    · intro s1 hs1 s2 hs2 hne_s
      rcases Finset.mem_image.mp hs1 with ⟨x1, _, rfl⟩
      rcases Finset.mem_image.mp hs2 with ⟨x2, _, rfl⟩
      rw [Finset.disjoint_singleton]
      intro hx
      exact hne_s (by rw [hx])
    · intro x _
      rw [Finset.mem_biUnion]
      exact ⟨{x}, Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩, Finset.mem_singleton_self x⟩
    · intro s hs
      rcases Finset.mem_image.mp hs with ⟨x, _, rfl⟩
      exact ⟨x, x, Walk.nil, Walk.IsPath.nil, by simp⟩
  exact Nat.sInf_mem hne

lemma exists_acyclic_card_eq {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) :
    ∃ F : Finset α, (G.induce (F : Set α)).IsAcyclic ∧
      F.card = G.largestInducedForestSize := by
  have hne : { n | ∃ s : Finset α, (G.induce (s : Set α)).IsAcyclic ∧ s.card = n }.Nonempty := by
    refine ⟨0, ∅, ?_, rfl⟩
    intro u
    exact False.elim (Finset.notMem_empty u.1 u.2)
  have hbdd : BddAbove { n | ∃ s : Finset α, (G.induce (s : Set α)).IsAcyclic ∧ s.card = n } :=
    ⟨Fintype.card α, fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  exact Nat.sSup_mem hne hbdd

lemma card_le_largestInducedForestSize {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (F : Finset α) (hF : (G.induce (F : Set α)).IsAcyclic) :
    F.card ≤ G.largestInducedForestSize := by
  unfold SimpleGraph.largestInducedForestSize
  apply le_csSup
  · exact ⟨Fintype.card α, fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  · exact ⟨F, hF, rfl⟩

lemma card_le_largestInducedBipartiteSubgraphSize (G : SimpleGraph V) (T : Finset V)
    (hT : (G.induce (T : Set V)).IsBipartite) :
    T.card ≤ G.largestInducedBipartiteSubgraphSize := by
  unfold SimpleGraph.largestInducedBipartiteSubgraphSize
  apply le_csSup
  · exact ⟨Fintype.card V, fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  · exact ⟨T, hT, rfl⟩

/-- The forest number of an induced subgraph is at most that of the graph. -/
lemma forest_induce_le (G : SimpleGraph V) (S : Finset V) :
    (G.induce (S : Set V)).largestInducedForestSize ≤ G.largestInducedForestSize := by
  obtain ⟨F', hF'ac, hF'card⟩ := exists_acyclic_card_eq (G.induce (S : Set V))
  let F : Finset V := F'.image Subtype.val
  have hFS : F ⊆ S := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨⟨y, hy⟩, _, rfl⟩
    exact hy
  have hcard : F.card = F'.card := Finset.card_image_of_injective F' Subtype.val_injective
  rw [← hF'card, ← hcard]
  apply card_le_largestInducedForestSize
  intro u c hc
  have hmemF' : ∀ x : (F : Set V), (⟨x.1, hFS x.2⟩ : (S : Set V)) ∈ F' := by
    intro x
    rcases Finset.mem_image.mp x.2 with ⟨⟨y, hy⟩, hyF', hyx⟩
    have heq : (⟨x.1, hFS x.2⟩ : (S : Set V)) = ⟨y, hy⟩ := Subtype.ext hyx.symm
    exact heq ▸ hyF'
  let f : G.induce (F : Set V) →g (G.induce (S : Set V)).induce (F' : Set (S : Set V)) :=
    { toFun := fun x => ⟨⟨x.1, hFS x.2⟩, hmemF' x⟩
      map_rel' := fun hadj => hadj }
  have hfinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z => z.1.1) hab
  exact hF'ac (c.map f) (hc.map hfinj)

/-- A vertex outside a largest induced bipartite subgraph has two neighbours in it with
different colours. -/
lemma two_colours_at (G : SimpleGraph V) (B : Finset V) (c0 : V → Fin 2)
    (hc0 : ∀ u ∈ B, ∀ v ∈ B, G.Adj u v → c0 u ≠ c0 v)
    (hmax : G.largestInducedBipartiteSubgraphSize ≤ B.card) (o : V) (ho : o ∉ B) :
    ∃ x ∈ B, ∃ y ∈ B, G.Adj o x ∧ G.Adj o y ∧ c0 x ≠ c0 y := by
  by_contra h
  push Not at h
  have hflip : ∀ t : Fin 2, t ≠ (if t = 0 then 1 else 0) := by decide
  obtain ⟨k, hk⟩ : ∃ k : Fin 2, ∀ z ∈ B, G.Adj o z → c0 z ≠ k := by
    by_cases hz : ∃ z ∈ B, G.Adj o z
    · obtain ⟨z, hzB, hoz⟩ := hz
      refine ⟨if c0 z = 0 then 1 else 0, fun z' hz'B hoz' => ?_⟩
      rw [h z' hz'B z hzB hoz' hoz]
      exact hflip (c0 z)
    · push Not at hz
      exact ⟨0, fun z hzB hoz => absurd hoz (hz z hzB)⟩
  have hbip : (G.induce ((insert o B : Finset V) : Set V)).IsBipartite := by
    rw [SimpleGraph.induce_isBipartite_iff_exists_coloring]
    refine ⟨fun v => if v = o then k else c0 v, ?_⟩
    intro u hu v hv huv
    have hu' := Finset.mem_insert.mp hu
    have hv' := Finset.mem_insert.mp hv
    by_cases huo : u = o
    · have hvo : v ≠ o := fun h' => (G.ne_of_adj huv) (huo.trans h'.symm)
      have hvB : v ∈ B := hv'.resolve_left hvo
      simp only [if_pos huo, if_neg hvo]
      exact (hk v hvB (huo ▸ huv)).symm
    · have huB : u ∈ B := hu'.resolve_left huo
      by_cases hvo : v = o
      · simp only [if_neg huo, if_pos hvo]
        exact hk u huB (hvo ▸ huv.symm)
      · have hvB : v ∈ B := hv'.resolve_left hvo
        simp only [if_neg huo, if_neg hvo]
        exact hc0 u huB v hvB huv
  have h1 := card_le_largestInducedBipartiteSubgraphSize G _ hbip
  rw [Finset.card_insert_of_notMem ho] at h1
  omega

/-- A largest induced bipartite subgraph of a non-bipartite graph has an edge. -/
lemma exists_edge_in (G : SimpleGraph V) (B : Finset V)
    (hmax : G.largestInducedBipartiteSubgraphSize ≤ B.card) (o : V) (ho : o ∉ B) :
    ∃ u ∈ B, ∃ v ∈ B, G.Adj u v := by
  by_contra h
  push Not at h
  have hbip : (G.induce ((insert o B : Finset V) : Set V)).IsBipartite := by
    rw [SimpleGraph.induce_isBipartite_iff_exists_coloring]
    refine ⟨fun v => if v = o then 0 else 1, ?_⟩
    intro u hu v hv huv
    have hu' := Finset.mem_insert.mp hu
    have hv' := Finset.mem_insert.mp hv
    by_cases huo : u = o
    · have hvo : v ≠ o := fun h' => (G.ne_of_adj huv) (huo.trans h'.symm)
      simp [huo, hvo]
    · have huB : u ∈ B := hu'.resolve_left huo
      by_cases hvo : v = o
      · simp [huo, hvo]
      · have hvB : v ∈ B := hv'.resolve_left hvo
        exact absurd huv (h u huB v hvB)
  have h1 := card_le_largestInducedBipartiteSubgraphSize G _ hbip
  rw [Finset.card_insert_of_notMem ho] at h1
  omega

/-- A path of an induced subgraph is a path of the graph. -/
lemma lift_walk (G : SimpleGraph V) (S : Finset V) {u v : (S : Set V)}
    (p : (G.induce (S : Set V)).Walk u v) (hp : p.IsPath) :
    ∃ q : G.Walk u.1 v.1, q.IsPath ∧
      q.support.toFinset = p.support.toFinset.map (Function.Embedding.subtype _) := by
  have key : ∀ z : V, z ∈ (p.map (Embedding.induce (G := G) (S : Set V)).toHom).support ↔
      ∃ a ∈ p.support, a.1 = z := by
    intro z
    rw [Walk.support_map, List.mem_map]
    rfl
  refine ⟨p.map (Embedding.induce (G := G) (S : Set V)).toHom,
    (Walk.isPath_map_iff_of_injective (Embedding.induce (G := G) (S : Set V)).injective).mpr hp, ?_⟩
  ext z
  rw [List.mem_toFinset, Finset.mem_map]
  refine (key z).trans ?_
  simp only [List.mem_toFinset, Function.Embedding.coe_subtype]

/-- Lifting a path cover of an induced subgraph to a family of paths of the graph. -/
lemma lift_cover (G : SimpleGraph V) (S : Finset V) (P : Finset (Finset (S : Set V)))
    (hP : (G.induce (S : Set V)).IsPathCover P) :
    (∀ t ∈ P.image (fun s => s.map (Function.Embedding.subtype _)), t ⊆ S) ∧
    (∀ t₁ ∈ P.image (fun s => s.map (Function.Embedding.subtype _)),
      ∀ t₂ ∈ P.image (fun s => s.map (Function.Embedding.subtype _)),
        t₁ ≠ t₂ → Disjoint t₁ t₂) ∧
    (S ⊆ (P.image (fun s => s.map (Function.Embedding.subtype _))).biUnion id) ∧
    (∀ t ∈ P.image (fun s => s.map (Function.Embedding.subtype _)),
      ∃ (u v : V) (q : G.Walk u v), q.IsPath ∧ t = q.support.toFinset) ∧
    (P.image (fun s : Finset (S : Set V) => s.map (Function.Embedding.subtype _))).card =
      P.card := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht z hz
    rcases Finset.mem_image.mp ht with ⟨s, _, rfl⟩
    rcases Finset.mem_map.mp hz with ⟨a, _, rfl⟩
    exact a.2
  · intro t₁ ht₁ t₂ ht₂ hne
    rcases Finset.mem_image.mp ht₁ with ⟨s₁, hs₁, rfl⟩
    rcases Finset.mem_image.mp ht₂ with ⟨s₂, hs₂, rfl⟩
    have hsne : s₁ ≠ s₂ := fun h => hne (by rw [h])
    exact Finset.disjoint_map _ |>.mpr (hP.1 s₁ hs₁ s₂ hs₂ hsne)
  · intro z hz
    have hmem : (⟨z, hz⟩ : (S : Set V)) ∈ P.biUnion id := hP.2.1 (Finset.mem_univ _)
    rcases Finset.mem_biUnion.mp hmem with ⟨s, hsP, hzs⟩
    refine Finset.mem_biUnion.mpr ⟨s.map (Function.Embedding.subtype _),
      Finset.mem_image_of_mem _ hsP, ?_⟩
    exact Finset.mem_map.mpr ⟨⟨z, hz⟩, hzs, rfl⟩
  · intro t ht
    rcases Finset.mem_image.mp ht with ⟨s, hsP, rfl⟩
    obtain ⟨u, v, p, hp, hs⟩ := hP.2.2 s hsP
    obtain ⟨q, hq, hqs⟩ := lift_walk G S p hp
    exact ⟨u.1, v.1, q, hq, by rw [hqs, hs]⟩
  · exact Finset.card_image_of_injective _ (fun _ _ h => Finset.map_injective _ h)

/-- The union of path families covering two complementary vertex sets is a path cover. -/
lemma union_cover (G : SimpleGraph V) (O B : Finset V) (hOB : ∀ v, v ∈ O ∨ v ∈ B)
    (hdOB : Disjoint O B) (Q₁ Q₂ : Finset (Finset V))
    (h₁s : ∀ t ∈ Q₁, t ⊆ O) (h₁d : ∀ t₁ ∈ Q₁, ∀ t₂ ∈ Q₁, t₁ ≠ t₂ → Disjoint t₁ t₂)
    (h₁c : O ⊆ Q₁.biUnion id)
    (h₁p : ∀ t ∈ Q₁, ∃ (u v : V) (q : G.Walk u v), q.IsPath ∧ t = q.support.toFinset)
    (h₂s : ∀ t ∈ Q₂, t ⊆ B) (h₂d : ∀ t₁ ∈ Q₂, ∀ t₂ ∈ Q₂, t₁ ≠ t₂ → Disjoint t₁ t₂)
    (h₂c : B ⊆ Q₂.biUnion id)
    (h₂p : ∀ t ∈ Q₂, ∃ (u v : V) (q : G.Walk u v), q.IsPath ∧ t = q.support.toFinset) :
    G.IsPathCover (Q₁ ∪ Q₂) ∧ (Q₁ ∪ Q₂).card = Q₁.card + Q₂.card := by
  have hne : ∀ t ∈ Q₁ ∪ Q₂, t.Nonempty := by
    intro t ht
    rcases Finset.mem_union.mp ht with h | h
    · obtain ⟨u, v, q, _, rfl⟩ := h₁p t h
      exact ⟨u, List.mem_toFinset.mpr q.start_mem_support⟩
    · obtain ⟨u, v, q, _, rfl⟩ := h₂p t h
      exact ⟨u, List.mem_toFinset.mpr q.start_mem_support⟩
  have hcross : ∀ t₁ ∈ Q₁, ∀ t₂ ∈ Q₂, Disjoint t₁ t₂ :=
    fun t₁ ht₁ t₂ ht₂ => Finset.disjoint_of_subset_left (h₁s t₁ ht₁)
      (Finset.disjoint_of_subset_right (h₂s t₂ ht₂) hdOB)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro t₁ ht₁ t₂ ht₂ hne'
    rcases Finset.mem_union.mp ht₁ with a | a <;> rcases Finset.mem_union.mp ht₂ with b | b
    · exact h₁d t₁ a t₂ b hne'
    · exact hcross t₁ a t₂ b
    · exact (hcross t₂ b t₁ a).symm
    · exact h₂d t₁ a t₂ b hne'
  · intro v _
    rcases hOB v with h | h
    · rcases Finset.mem_biUnion.mp (h₁c h) with ⟨t, ht, hvt⟩
      exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_union_left _ ht, hvt⟩
    · rcases Finset.mem_biUnion.mp (h₂c h) with ⟨t, ht, hvt⟩
      exact Finset.mem_biUnion.mpr ⟨t, Finset.mem_union_right _ ht, hvt⟩
  · intro t ht
    rcases Finset.mem_union.mp ht with h | h
    · exact h₁p t h
    · exact h₂p t h
  · have hinter : Q₁ ∩ Q₂ = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro t ht
      rcases Finset.mem_inter.mp ht with ⟨a, b⟩
      obtain ⟨z, hz⟩ := hne t (Finset.mem_union_left _ a)
      exact Finset.disjoint_left.mp (hcross t a t b) hz hz
    have := Finset.card_union_add_card_inter Q₁ Q₂
    rw [hinter, Finset.card_empty] at this
    omega

/-- Merging two paths of a path cover along an edge joining an end of each. -/
lemma merge (G : SimpleGraph V) (C : Finset (Finset V)) (hC : G.IsPathCover C)
    {a₁ a w w₂ : V} (p : G.Walk a₁ a) (q : G.Walk w w₂) (hp : p.IsPath) (hq : q.IsPath)
    (hs : p.support.toFinset ∈ C) (ht : q.support.toFinset ∈ C)
    (hst : p.support.toFinset ≠ q.support.toFinset) (had : G.Adj a w) :
    ∃ (r : G.Walk a₁ w₂) (C' : Finset (Finset V)), r.IsPath ∧
      r.support.toFinset = p.support.toFinset ∪ q.support.toFinset ∧
      r.support.toFinset ∈ C' ∧ G.IsPathCover C' ∧ C'.card + 1 = C.card ∧
      (∀ x ∈ C, x ≠ p.support.toFinset → x ≠ q.support.toFinset → x ∈ C') := by
  have hdisj : Disjoint p.support.toFinset q.support.toFinset := hC.1 _ hs _ ht hst
  let r : G.Walk a₁ w₂ := p.append (Walk.cons had q)
  have hrs : r.support = p.support ++ q.support := by
    simp [r, Walk.support_append]
  have hr : r.IsPath := by
    rw [Walk.isPath_def, hrs, List.nodup_append]
    refine ⟨(Walk.isPath_def p).mp hp, (Walk.isPath_def q).mp hq, ?_⟩
    intro x hx y hy hxy
    subst hxy
    exact Finset.disjoint_left.mp hdisj (List.mem_toFinset.mpr hx) (List.mem_toFinset.mpr hy)
  have hrt : r.support.toFinset = p.support.toFinset ∪ q.support.toFinset := by
    rw [hrs, List.toFinset_append]
  have ha₁ : a₁ ∈ p.support.toFinset := List.mem_toFinset.mpr p.start_mem_support
  have hR : ∀ x ∈ (C.erase p.support.toFinset).erase q.support.toFinset,
      x ∈ C ∧ x ≠ p.support.toFinset ∧ x ≠ q.support.toFinset := by
    intro x hx
    obtain ⟨hxt, hx'⟩ := Finset.mem_erase.mp hx
    obtain ⟨hxs, hxC⟩ := Finset.mem_erase.mp hx'
    exact ⟨hxC, hxs, hxt⟩
  have hU : ∀ x ∈ (C.erase p.support.toFinset).erase q.support.toFinset,
      Disjoint (p.support.toFinset ∪ q.support.toFinset) x := by
    intro x hx
    obtain ⟨hxC, hxs, hxt⟩ := hR x hx
    exact Finset.disjoint_union_left.mpr
      ⟨hC.1 _ hs x hxC (Ne.symm hxs), hC.1 _ ht x hxC (Ne.symm hxt)⟩
  refine ⟨r, insert (p.support.toFinset ∪ q.support.toFinset)
    ((C.erase p.support.toFinset).erase q.support.toFinset), hr, hrt, ?_, ?_, ?_, ?_⟩
  · rw [hrt]
    exact Finset.mem_insert_self _ _
  · refine ⟨?_, ?_, ?_⟩
    · intro x₁ hx₁ x₂ hx₂ hne
      rcases Finset.mem_insert.mp hx₁ with h₁ | h₁ <;>
        rcases Finset.mem_insert.mp hx₂ with h₂ | h₂
      · exact absurd (h₁.trans h₂.symm) hne
      · rw [h₁]
        exact hU x₂ h₂
      · rw [h₂]
        exact (hU x₁ h₁).symm
      · exact hC.1 x₁ (hR x₁ h₁).1 x₂ (hR x₂ h₂).1 hne
    · intro v _
      obtain ⟨x, hxC, hvx⟩ : ∃ x ∈ C, v ∈ x := by
        simpa using hC.2.1 (Finset.mem_univ v)
      rw [Finset.mem_biUnion]
      by_cases hxs : x = p.support.toFinset
      · exact ⟨_, Finset.mem_insert_self _ _, Finset.mem_union_left _ (hxs ▸ hvx)⟩
      · by_cases hxt : x = q.support.toFinset
        · exact ⟨_, Finset.mem_insert_self _ _, Finset.mem_union_right _ (hxt ▸ hvx)⟩
        · exact ⟨x, Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨hxt, Finset.mem_erase.mpr ⟨hxs, hxC⟩⟩), hvx⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with h | h
      · exact ⟨a₁, w₂, r, hr, h.trans hrt.symm⟩
      · exact hC.2.2 x (hR x h).1
  · have hnot : p.support.toFinset ∪ q.support.toFinset ∉
        (C.erase p.support.toFinset).erase q.support.toFinset := by
      intro hmem
      obtain ⟨hxC, hxs, _⟩ := hR _ hmem
      have hd := hC.1 _ hs _ hxC (Ne.symm hxs)
      exact Finset.disjoint_left.mp hd ha₁ (Finset.mem_union_left _ ha₁)
    rw [Finset.card_insert_of_notMem hnot,
      Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hst, ht⟩),
      Finset.card_erase_of_mem hs]
    have h2 : 2 ≤ C.card := by
      have hsub : ({p.support.toFinset, q.support.toFinset} : Finset (Finset V)) ⊆ C := by
        intro x hx
        rcases Finset.mem_insert.mp hx with h | h
        · exact h ▸ hs
        · exact (Finset.mem_singleton.mp h) ▸ ht
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hst] at this
      exact this
    omega
  · intro x hxC hxs hxt
    exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hxt, Finset.mem_erase.mpr ⟨hxs, hxC⟩⟩)

/-- In a two-endpoint path cover, the path through the first root starts at it, and if it also
contains the second root, it ends there. -/
lemma orient {W : Type} [Fintype W] [DecidableEq W] (H : SimpleGraph W)
    (P : Finset (Finset W)) (hP : H.IsPathCover P) (x y : W) (hxy : x ≠ y)
    (hend : ∀ s ∈ P, ∃ (u v : W) (p : H.Walk u v), p.IsPath ∧ s = p.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) :
    ∃ s ∈ P, x ∈ s ∧ ∃ (x₂ : W) (q : H.Walk x x₂), q.IsPath ∧ q.support.toFinset = s ∧
      (y ∈ s → y = x₂) := by
  obtain ⟨s, hsP, hxs⟩ : ∃ s ∈ P, x ∈ s := by
    simpa using hP.2.1 (Finset.mem_univ x)
  obtain ⟨u, v, p, hp, hs, hx, hy⟩ := hend s hsP
  refine ⟨s, hsP, hxs, ?_⟩
  rcases hx hxs with h | h
  · subst h
    exact ⟨v, p, hp, hs.symm, fun hys => (hy hys).resolve_left (Ne.symm hxy)⟩
  · subst h
    refine ⟨u, p.reverse, hp.reverse, ?_, fun hys => (hy hys).resolve_right (Ne.symm hxy)⟩
    rw [Walk.support_reverse, List.toFinset_reverse]
    exact hs.symm


/-- Applying `H1` to a largest induced bipartite subgraph with two roots of different colours,
and lifting the resulting path cover to the graph. -/
lemma bip_part (h1 : (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : G.Coloring (Fin 2))
    (x y : V),
    (G.Reachable x y → c x ≠ c y) →
    (∃ u v : V, G.Adj u v) →
    ∃ P : Finset (Finset V), G.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ s = p.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card V + 1 ≤ 2 * G.largestInducedForestSize)) (G : SimpleGraph V) (B : Finset V) (c0 : V → Fin 2)
    (hc0 : ∀ u ∈ B, ∀ v ∈ B, G.Adj u v → c0 u ≠ c0 v)
    (hedge : ∃ u ∈ B, ∃ v ∈ B, G.Adj u v) (w u : V) (hw : w ∈ B) (hu : u ∈ B)
    (hwu : c0 w ≠ c0 u) :
    ∃ QB : Finset (Finset V), (∀ t ∈ QB, t ⊆ B) ∧
      (∀ t₁ ∈ QB, ∀ t₂ ∈ QB, t₁ ≠ t₂ → Disjoint t₁ t₂) ∧ (B ⊆ QB.biUnion id) ∧
      (∀ t ∈ QB, ∃ (u v : V) (q : G.Walk u v), q.IsPath ∧ t = q.support.toFinset) ∧
      QB.card + B.card + 1 ≤ 2 * G.largestInducedForestSize ∧
      (∃ tw ∈ QB, w ∈ tw ∧ ∃ (w₂ : V) (q : G.Walk w w₂), q.IsPath ∧ q.support.toFinset = tw ∧
        (u ∈ tw → u = w₂)) ∧
      (∃ tu ∈ QB, u ∈ tu ∧ ∃ (u₂ : V) (q : G.Walk u u₂), q.IsPath ∧ q.support.toFinset = tu ∧
        (w ∈ tu → w = u₂)) := by
  let cB : (G.induce (B : Set V)).Coloring (Fin 2) :=
    Coloring.mk (fun v => c0 v.1) (fun {a b} hab => hc0 a.1 a.2 b.1 b.2 hab)
  obtain ⟨e₁, he₁, e₂, he₂, he⟩ := hedge
  have hne : (⟨w, hw⟩ : (B : Set V)) ≠ ⟨u, hu⟩ := fun h => hwu (congrArg c0 (congrArg Subtype.val h))
  obtain ⟨PB, hPB, hend, hcount⟩ := h1 _ (G.induce (B : Set V)) cB ⟨w, hw⟩ ⟨u, hu⟩
    (fun _ => hwu) ⟨⟨e₁, he₁⟩, ⟨e₂, he₂⟩, he⟩
  obtain ⟨hBs, hBd, hBc, hBp, hBcard⟩ := lift_cover G B PB hPB
  have hend' : ∀ s ∈ PB, ∃ (a b : (B : Set V)) (p : (G.induce (B : Set V)).Walk a b),
      p.IsPath ∧ s = p.support.toFinset ∧ (⟨u, hu⟩ ∈ s → ⟨u, hu⟩ = a ∨ ⟨u, hu⟩ = b) ∧
        (⟨w, hw⟩ ∈ s → ⟨w, hw⟩ = a ∨ ⟨w, hw⟩ = b) := by
    intro s hs
    obtain ⟨a, b, p, hp, hsp, hx, hy⟩ := hend s hs
    exact ⟨a, b, p, hp, hsp, hy, hx⟩
  have hcardB : Fintype.card (B : Set V) = B.card := by simp
  have hf := forest_induce_le G B
  have hroot : ∀ (x y : V) (hx : x ∈ B) (hy : y ∈ B),
      (∃ s ∈ PB, (⟨x, hx⟩ : (B : Set V)) ∈ s ∧ ∃ (x₂ : (B : Set V))
        (q : (G.induce (B : Set V)).Walk ⟨x, hx⟩ x₂), q.IsPath ∧ q.support.toFinset = s ∧
          (⟨y, hy⟩ ∈ s → ⟨y, hy⟩ = x₂)) →
      ∃ tx ∈ PB.image (fun s => s.map (Function.Embedding.subtype _)), x ∈ tx ∧
        ∃ (x₂ : V) (q : G.Walk x x₂), q.IsPath ∧ q.support.toFinset = tx ∧ (y ∈ tx → y = x₂) := by
    intro x y hx hy ⟨s, hsP, hxs, x₂, q, hq, hqs, hys⟩
    obtain ⟨q', hq', hq's⟩ := lift_walk G B q hq
    refine ⟨s.map (Function.Embedding.subtype _), Finset.mem_image_of_mem _ hsP,
      Finset.mem_map.mpr ⟨⟨x, hx⟩, hxs, rfl⟩, x₂.1, q', hq', by rw [hq's, hqs], ?_⟩
    intro hyt
    obtain ⟨a, has, hay⟩ := Finset.mem_map.mp hyt
    have ha : a = ⟨y, hy⟩ := Subtype.ext hay
    rw [ha] at has
    exact congrArg Subtype.val (hys has)
  refine ⟨_, hBs, hBd, hBc, hBp, ?_, hroot w u hw hu
    (orient _ PB hPB ⟨w, hw⟩ ⟨u, hu⟩ hne hend),
    hroot u w hu hw (orient _ PB hPB ⟨u, hu⟩ ⟨w, hw⟩ (Ne.symm hne) hend')⟩
  rw [hBcard]
  omega

lemma key (h1 : (∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) (c : G.Coloring (Fin 2))
    (x y : V),
    (G.Reachable x y → c x ≠ c y) →
    (∃ u v : V, G.Adj u v) →
    ∃ P : Finset (Finset V), G.IsPathCover P ∧
      (∀ s ∈ P, ∃ (u v : V) (p : G.Walk u v), p.IsPath ∧ s = p.support.toFinset ∧
        (x ∈ s → x = u ∨ x = v) ∧ (y ∈ s → y = u ∨ y = v)) ∧
      P.card + Fintype.card V + 1 ≤ 2 * G.largestInducedForestSize)) (G : SimpleGraph V) (hnb : ¬ G.IsBipartite) (B : Finset V)
    (hB : (G.induce (B : Set V)).IsBipartite)
    (hBcard : B.card = G.largestInducedBipartiteSubgraphSize)
    (hp2 : (G.induce ((Bᶜ : Finset V) : Set V)).pathCoverNumber ≤ 2) :
    G.pathCoverNumber + G.largestInducedBipartiteSubgraphSize + 1 ≤
      2 * G.largestInducedForestSize := by
  obtain ⟨c0, hc0⟩ := (SimpleGraph.induce_isBipartite_iff_exists_coloring G B).mp hB
  have hmax : G.largestInducedBipartiteSubgraphSize ≤ B.card := hBcard.ge
  obtain ⟨o0, ho0⟩ : ∃ o, o ∉ B := by
    by_contra h
    push Not at h
    exact hnb ⟨Coloring.mk c0 (fun {u v} huv => hc0 u (h u) v (h v) huv)⟩
  have hedge := exists_edge_in G B hmax o0 ho0
  obtain ⟨PO, hPOcard, hPO⟩ := exists_pathCover_card_eq (G.induce ((Bᶜ : Finset V) : Set V))
  obtain ⟨hOs, hOd, hOc, hOp, hOcard⟩ := lift_cover G Bᶜ PO hPO
  set QO : Finset (Finset V) := PO.image (fun s => s.map (Function.Embedding.subtype _))
    with hQO
  have hOB : ∀ v, v ∈ Bᶜ ∨ v ∈ B := fun v => by
    by_cases h : v ∈ B
    · exact Or.inr h
    · exact Or.inl (Finset.mem_compl.mpr h)
  have hdOB : Disjoint Bᶜ B := disjoint_compl_left
  have hOend : ∀ s ∈ PO, ∃ (a₁ a : V) (p : G.Walk a₁ a), p.IsPath ∧
      p.support.toFinset = s.map (Function.Embedding.subtype _) ∧ a ∉ B := by
    intro s hs
    obtain ⟨u, v, p, hp, hsp⟩ := hPO.2.2 s hs
    obtain ⟨q, hq, hqs⟩ := lift_walk G Bᶜ p hp
    exact ⟨u.1, v.1, q, hq, by rw [hqs, hsp], Finset.mem_compl.mp v.2⟩
  have hpc : ∀ C : Finset (Finset V), G.IsPathCover C → G.pathCoverNumber ≤ C.card :=
    fun C hC => Nat.sInf_le ⟨C, rfl, hC⟩
  have hPOpos : 0 < PO.card := by
    rw [Finset.card_pos]
    obtain ⟨s, hs, _⟩ : ∃ s ∈ PO,
        (⟨o0, Finset.mem_compl.mpr ho0⟩ : ((Bᶜ : Finset V) : Set V)) ∈ s := by
      simpa using hPO.2.1 (Finset.mem_univ _)
    exact ⟨s, hs⟩
  have hnotin : ∀ s ∈ PO, ∀ z ∈ B, z ∉ s.map (Function.Embedding.subtype _) := by
    intro s hs z hz hzs
    exact Finset.mem_compl.mp (hOs _ (Finset.mem_image_of_mem _ hs) hzs) hz
  rcases (show PO.card = 1 ∨ PO.card = 2 by omega) with h1c | h2c
  · obtain ⟨s₁, rfl⟩ := Finset.card_eq_one.mp h1c
    obtain ⟨a₁, a, p, hp, hps, haB⟩ := hOend s₁ (Finset.mem_singleton_self _)
    obtain ⟨x, hx, y, hy, hax, hay, hxy⟩ := two_colours_at G B c0 hc0 hmax a haB
    obtain ⟨QB, hBs, hBd, hBc, hBp, hcount, ⟨tw, htw, hwt, w₂, qw, hqw, hqwt, _⟩, _⟩ :=
      bip_part h1 G B c0 hc0 hedge x y hx hy hxy
    obtain ⟨hC, hCcard⟩ := union_cover G Bᶜ B hOB hdOB _ QB hOs hOd hOc hOp hBs hBd hBc hBp
    have hs : p.support.toFinset ∈ QO ∪ QB := by
      rw [hps]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_singleton_self _))
    have ht : qw.support.toFinset ∈ QO ∪ QB := by
      rw [hqwt]
      exact Finset.mem_union_right _ htw
    have hst : p.support.toFinset ≠ qw.support.toFinset := by
      intro h
      have : x ∈ p.support.toFinset := by rw [h, hqwt]; exact hwt
      rw [hps] at this
      exact hnotin s₁ (Finset.mem_singleton_self _) x hx this
    obtain ⟨r, C', _, _, _, hC', hC'card, _⟩ := merge G _ hC p qw hp hqw hs ht hst hax
    have := hpc C' hC'
    rw [hOcard, h1c] at hCcard
    omega
  · obtain ⟨s₁, s₂, hs12, rfl⟩ := Finset.card_eq_two.mp h2c
    have hs₁ : s₁ ∈ ({s₁, s₂} : Finset _) := Finset.mem_insert_self _ _
    have hs₂ : s₂ ∈ ({s₁, s₂} : Finset _) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    obtain ⟨a₁, a, p₁, hp₁, hps₁, haB⟩ := hOend s₁ hs₁
    obtain ⟨c₁, c, p₂, hp₂, hps₂, hcB⟩ := hOend s₂ hs₂
    obtain ⟨w, hw, y, hy, haw, hay, hwy⟩ := two_colours_at G B c0 hc0 hmax a haB
    obtain ⟨u, hu, hcu, hwu⟩ : ∃ u ∈ B, G.Adj c u ∧ c0 w ≠ c0 u := by
      obtain ⟨x', hx', y', hy', hcx', hcy', hxy'⟩ := two_colours_at G B c0 hc0 hmax c hcB
      by_cases heq : c0 x' = c0 w
      · exact ⟨y', hy', hcy', fun h => hxy' (heq.trans h)⟩
      · exact ⟨x', hx', hcx', fun h => heq h.symm⟩
    obtain ⟨QB, hBs, hBd, hBc, hBp, hcount, ⟨tw, htw, hwt, w₂, qw, hqw, hqwt, huw⟩,
      ⟨tu, htu, hut, u₂, qu, hqu, hqut, _⟩⟩ := bip_part h1 G B c0 hc0 hedge w u hw hu hwu
    obtain ⟨hC, hCcard⟩ := union_cover G Bᶜ B hOB hdOB _ QB hOs hOd hOc hOp hBs hBd hBc hBp
    have hm₁ : p₁.support.toFinset ∈ QO ∪ QB := by
      rw [hps₁]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hs₁)
    have hm₂ : p₂.support.toFinset ∈ QO ∪ QB := by
      rw [hps₂]
      exact Finset.mem_union_left _ (Finset.mem_image_of_mem _ hs₂)
    have hmw : qw.support.toFinset ∈ QO ∪ QB := by
      rw [hqwt]
      exact Finset.mem_union_right _ htw
    have hmu : qu.support.toFinset ∈ QO ∪ QB := by
      rw [hqut]
      exact Finset.mem_union_right _ htu
    have hn₁ : ∀ z ∈ B, z ∉ p₁.support.toFinset := by
      intro z hz
      rw [hps₁]
      exact hnotin s₁ hs₁ z hz
    have hn₂ : ∀ z ∈ B, z ∉ p₂.support.toFinset := by
      intro z hz
      rw [hps₂]
      exact hnotin s₂ hs₂ z hz
    have hwq : w ∈ qw.support.toFinset := by rw [hqwt]; exact hwt
    have huq : u ∈ qu.support.toFinset := by rw [hqut]; exact hut
    have h1w : p₁.support.toFinset ≠ qw.support.toFinset :=
      fun h => hn₁ w hw (h ▸ hwq)
    have h12 : p₂.support.toFinset ≠ p₁.support.toFinset := by
      rw [hps₁, hps₂]
      intro h
      exact hs12 (Finset.map_injective _ h).symm
    have h2w : p₂.support.toFinset ≠ qw.support.toFinset :=
      fun h => hn₂ w hw (h ▸ hwq)
    obtain ⟨r₁, C₁, hr₁, hr₁s, hr₁C, hC₁, hC₁card, hkeep₁⟩ :=
      merge G _ hC p₁ qw hp₁ hqw hm₁ hmw h1w haw
    have hm₂' : p₂.support.toFinset ∈ C₁ := hkeep₁ _ hm₂ h12 h2w
    by_cases hutw : u ∈ tw
    · have hu₂ : u = w₂ := huw hutw
      subst hu₂
      have hrev : r₁.reverse.support.toFinset = r₁.support.toFinset := by
        rw [Walk.support_reverse, List.toFinset_reverse]
      have hst : p₂.support.toFinset ≠ r₁.reverse.support.toFinset := by
        rw [hrev, hr₁s]
        intro h
        exact hn₂ w hw (h ▸ Finset.mem_union_right _ hwq)
      obtain ⟨r₂, C₂, _, _, _, hC₂, hC₂card, _⟩ :=
        merge G C₁ hC₁ p₂ r₁.reverse hp₂ hr₁.reverse hm₂' (hrev ▸ hr₁C) hst hcu
      have := hpc C₂ hC₂
      rw [hOcard, Finset.card_pair hs12] at hCcard
      omega
    · have hmu' : qu.support.toFinset ∈ C₁ := by
        refine hkeep₁ _ hmu ?_ ?_
        · intro h
          exact hn₁ u hu (h ▸ huq)
        · intro h
          exact hutw (hqwt ▸ h ▸ huq)
      have hst : p₂.support.toFinset ≠ qu.support.toFinset :=
        fun h => hn₂ u hu (h ▸ huq)
      obtain ⟨r₂, C₂, _, _, _, hC₂, hC₂card, _⟩ :=
        merge G C₁ hC₁ p₂ qu hp₂ hqu hm₂' hmu' hst hcu
      have := hpc C₂ hC₂
      rw [hOcard, Finset.card_pair hs12] at hCcard
      omega

end

theorem main : H1 → H2 → OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1.H2 := by
  intro h1 h2
  unfold OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1.H2
  intro V _ _ G hcard hconn h2c hnb hsc hsub
  by_cases hex : ∃ B : Finset V, (G.induce (B : Set V)).IsBipartite ∧
      B.card = G.largestInducedBipartiteSubgraphSize ∧
      (G.induce ((Bᶜ : Finset V) : Set V)).pathCoverNumber ≤ 2
  · obtain ⟨B, hB, hBc, hp⟩ := hex
    exact key (nb0_S2comp_of_S2 h1) G hnb B hB hBc hp
  · push Not at hex
    exact h2 V G hcard hconn h2c hnb hsc hsub (fun B hB hBc => hex B hB hBc)

end OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H2_R1
