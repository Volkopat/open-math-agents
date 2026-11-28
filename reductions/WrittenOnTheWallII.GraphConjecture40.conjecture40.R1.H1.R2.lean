import OMAReductions.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1
import Mathlib

/-!
# Reduction of the bipartite residual step `R1.H1` of Written on the Wall II - Conjecture 40

The step `R1.H1` (2-connected bipartite graphs above the scattering bound) is PROVED here for
every graph having a maximum induced forest `U` whose outside neighbourhoods are in the block
class: for every `x ∈ U`, the components of `H - x` contain at most two outside neighbours of `x`,
where `H` is the graph of the edges between `U` and its complement. Stated without components:
for any three distinct outside neighbours of `x` there is a split of the outside vertices, such
that outside vertices on different sides have no common neighbour in `U` other than `x`, which
does not put all three on the same side. This holds in particular when every vertex of `U` has
at most two neighbours outside `U`. The proof gives `p + n + 1 ≤ 2 f` for every connected
bipartite graph on at least two vertices with such a forest (`k2_forest_class`).

The remaining graphs (no maximum induced forest is in the block class) are split by the number
of outside neighbours: some maximum induced forest has all its vertices with at most three
outside neighbours (`H1`), or every maximum induced forest has a vertex with four distinct
outside neighbours (`H2`).

Proof (Theorem BL and Corollary BLG of the written note `s200_K_1_separators_blocks_lp.md`):

- the outside vertices of colour `i` and their neighbourhoods in `U` form a set family satisfying
  the Hall-type condition `HP` (`p1_hp`, exchange argument: vertices with at most one neighbour
  in `U - S` can be added to `U - S`);
- Theorem BL (`theorem_BL`, `BL_R3form`): a family with `HP` in the block class has, for every
  prescribed point `v`, 2-subsets of the sets forming a linear forest in which `v` has degree at
  most one. Induction on the number of sets: a point in three sets is a cut point of the
  incidence graph; deleting it, at most one side loses `HP` (`lemma_SEP`), and the solutions of
  the sides are glued (`theorem_CE`, `glue`). If every point lies in at most two sets, Theorem GL
  (`theorem_GL`): `HP` gives the Lovász condition (`lc_of_hp`), `v` can be kept in one set only
  keeping it (`theorem_RF1`, using `lemma_LT`), and the Lovász condition gives a rainbow forest by
  deleting points from sets of size at least three (`shrink_step`, `lovasz_pairs`);
- the two one-sided linear forests, which are vertex-disjoint, and one edge of `U` form a linear
  forest with `2 (n - f) + 1` edges, hence a path cover with `2 f - n - 1` paths
  (`k2_bipartite_core`, `p1_linear_forest_cover`, graph lemmas of the merged reduction `R1` and
  of an unmerged local reduction of the problem).
-/

namespace OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H1_R2

open SimpleGraph

/-- 2-connected bipartite graphs above the scattering bound in which no maximum induced forest `U`
is in the block class (some `x ∈ U` has three outside neighbours that no split at `x` separates),
while some maximum induced forest has no vertex with four distinct neighbours outside it. -/
def H1 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    4 ≤ Fintype.card V →
    G.Connected →
    (∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected) →
    G.IsBipartite →
    (∀ S : Finset V,
      Nat.card (G.induce (S : Set V)ᶜ).ConnectedComponent < G.pathCoverNumber + S.card) →
    (∀ U : Finset V, (G.induce (U : Set V)).IsAcyclic → U.card = G.largestInducedForestSize →
      ∃ x ∈ U, ∃ t1 t2 t3 : V, t1 ∉ U ∧ t2 ∉ U ∧ t3 ∉ U ∧ t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3 ∧
        G.Adj x t1 ∧ G.Adj x t2 ∧ G.Adj x t3 ∧ ∀ p : V → Prop,
          (∀ s s', s ∉ U → s' ∉ U → p s → ¬ p s' → ∀ z ∈ U, G.Adj s z → G.Adj s' z → z = x) →
          (p t1 ↔ p t2) ∧ (p t1 ↔ p t3)) →
    (∃ U : Finset V, (G.induce (U : Set V)).IsAcyclic ∧ U.card = G.largestInducedForestSize ∧
      ∀ x ∈ U, ∀ t1 t2 t3 t4 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t4 ∉ U →
        G.Adj x t1 → G.Adj x t2 → G.Adj x t3 → G.Adj x t4 →
        t1 = t2 ∨ t1 = t3 ∨ t1 = t4 ∨ t2 = t3 ∨ t2 = t4 ∨ t3 = t4) →
    G.pathCoverNumber + Fintype.card V + 1 ≤ 2 * G.largestInducedForestSize

/-- 2-connected bipartite graphs above the scattering bound in which no maximum induced forest is
in the block class and every maximum induced forest `U` contains a vertex with four distinct
neighbours outside `U`. -/
def H2 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V),
    4 ≤ Fintype.card V →
    G.Connected →
    (∀ v : V, (G.induce ({v}ᶜ : Set V)).Connected) →
    G.IsBipartite →
    (∀ S : Finset V,
      Nat.card (G.induce (S : Set V)ᶜ).ConnectedComponent < G.pathCoverNumber + S.card) →
    (∀ U : Finset V, (G.induce (U : Set V)).IsAcyclic → U.card = G.largestInducedForestSize →
      ∃ x ∈ U, ∃ t1 t2 t3 : V, t1 ∉ U ∧ t2 ∉ U ∧ t3 ∉ U ∧ t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3 ∧
        G.Adj x t1 ∧ G.Adj x t2 ∧ G.Adj x t3 ∧ ∀ p : V → Prop,
          (∀ s s', s ∉ U → s' ∉ U → p s → ¬ p s' → ∀ z ∈ U, G.Adj s z → G.Adj s' z → z = x) →
          (p t1 ↔ p t2) ∧ (p t1 ↔ p t3)) →
    (∀ U : Finset V, (G.induce (U : Set V)).IsAcyclic → U.card = G.largestInducedForestSize →
      ∃ x ∈ U, ∃ t1 t2 t3 t4 : V, t1 ∉ U ∧ t2 ∉ U ∧ t3 ∉ U ∧ t4 ∉ U ∧
        G.Adj x t1 ∧ G.Adj x t2 ∧ G.Adj x t3 ∧ G.Adj x t4 ∧
        t1 ≠ t2 ∧ t1 ≠ t3 ∧ t1 ≠ t4 ∧ t2 ≠ t3 ∧ t2 ≠ t4 ∧ t3 ≠ t4) →
    G.pathCoverNumber + Fintype.card V + 1 ≤ 2 * G.largestInducedForestSize

section

private lemma isAcyclic_of_all_adj_eq {W : Type*} (H : SimpleGraph W) (r : W)
    (hstar : ∀ a b : W, H.Adj a b → a = r ∨ b = r) : H.IsAcyclic := by
  intro u c hc
  have hlen := hc.three_le_length
  cases c with
  | nil => simp at hlen
  | @cons _ x _ h1 c1 =>
    cases c1 with
    | nil => simp at hlen
    | @cons _ y _ h2 c2 =>
      cases c2 with
      | nil => simp at hlen
      | @cons _ z _ h3 c3 =>
        have hnd : (x :: y :: c3.support).Nodup := hc.support_nodup
        rw [List.nodup_cons] at hnd
        have hx_not : x ∉ y :: c3.support := hnd.1
        have hy_nd : (y :: c3.support).Nodup := hnd.2
        rw [List.nodup_cons] at hy_nd
        have hy_not : y ∉ c3.support := hy_nd.1
        have hz_mem : z ∈ c3.support := c3.start_mem_support
        have hu_mem : u ∈ c3.support := c3.end_mem_support
        rcases hstar u x h1 with rfl | rfl
        · rcases hstar x y h2 with hxr | rfl
          · exact H.ne_of_adj h1 hxr.symm
          · exact hy_not hu_mem
        · rcases hstar y z h3 with hyx | rfl
          · exact H.ne_of_adj h2 hyx.symm
          · exact hx_not (List.mem_cons_of_mem _ hz_mem)

private lemma indep_add_one_le_forest {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) (hconn : H.Connected) (hn : 1 < Fintype.card W)
    (I : Finset W) (hind : ∀ x ∈ I, ∀ y ∈ I, ¬ H.Adj x y) :
    I.card + 1 ≤ H.largestInducedForestSize := by
  obtain ⟨w, hw⟩ : ∃ w : W, w ∉ I := by
    by_contra hall
    push Not at hall
    obtain ⟨x, y, hxy⟩ := Fintype.one_lt_card_iff.mp hn
    obtain ⟨p⟩ := hconn.preconnected x y
    cases p with
    | nil => exact hxy rfl
    | @cons _ z _ hxz _ => exact hind x (hall x) z (hall z) hxz
  let T : Finset W := insert w I
  have hTcard : T.card = I.card + 1 := Finset.card_insert_of_notMem hw
  have hTacyc : (H.induce (T : Set W)).IsAcyclic := by
    apply isAcyclic_of_all_adj_eq (H.induce (T : Set W)) ⟨w, Finset.mem_insert_self w I⟩
    intro a b hadj
    have ha : a.val = w ∨ a.val ∈ I := Finset.mem_insert.mp a.prop
    have hb : b.val = w ∨ b.val ∈ I := Finset.mem_insert.mp b.prop
    rcases ha with haw | haI
    · exact Or.inl (Subtype.ext haw)
    · rcases hb with hbw | hbI
      · exact Or.inr (Subtype.ext hbw)
      · exact (hind a.val haI b.val hbI hadj).elim
  unfold SimpleGraph.largestInducedForestSize
  apply le_csSup
  · exact ⟨Fintype.card W, fun n ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  · exact ⟨T, hTacyc, hTcard⟩

private lemma ncvr_exists_acyclic_card_eq {α : Type*} [Fintype α] [DecidableEq α]
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

private lemma ncvr_card_le_largestInducedForestSize {α : Type*} [Fintype α] [DecidableEq α]
    (G : SimpleGraph α) (F : Finset α) (hF : (G.induce (F : Set α)).IsAcyclic) :
    F.card ≤ G.largestInducedForestSize := by
  unfold SimpleGraph.largestInducedForestSize
  apply le_csSup
  · exact ⟨Fintype.card α, fun _ ⟨t, _, ht⟩ => ht ▸ t.card_le_univ⟩
  · exact ⟨F, hF, rfl⟩

private lemma r2_isPathCover_mono {V : Type*} [Fintype V] [DecidableEq V]
    {G K : SimpleGraph V} (hle : K ≤ G) {P : Finset (Finset V)} (hP : K.IsPathCover P) :
    G.IsPathCover P := by
  rcases hP with ⟨hdisj, hcov, hpaths⟩
  refine ⟨hdisj, hcov, ?_⟩
  intro s hs
  rcases hpaths s hs with ⟨u, w, p, hp, rfl⟩
  refine ⟨u, w, p.mapLe hle, hp.mapLe hle, ?_⟩
  rw [Walk.support_mapLe_eq_support]

end

section


variable {T B : Type} [Fintype T] [DecidableEq T] [DecidableEq B]



theorem lc_of_hp (A : T → Finset B) (h : (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)) : (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion A).card) := by
  intro X hX
  by_contra hlt
  push Not at hlt
  -- choose S of size |A(X)| - 1 with every A t \ S of size ≤ 1 for t ∈ X
  have key : ∃ S : Finset B, S.card + 1 ≤ X.card ∧ ∀ t ∈ X, (A t \ S).card ≤ 1 := by
    rcases (X.biUnion A).eq_empty_or_nonempty with he | ⟨x, hx⟩
    · refine ⟨∅, by simpa using hX.card_pos, fun t ht => ?_⟩
      have : A t = ∅ := by
        have hs : A t ⊆ X.biUnion A := Finset.subset_biUnion_of_mem A ht
        rw [he] at hs; exact Finset.subset_empty.mp hs
      simp [this]
    · refine ⟨(X.biUnion A).erase x, ?_, fun t ht => ?_⟩
      · have := Finset.card_pos.mpr ⟨x, hx⟩
        rw [Finset.card_erase_of_mem hx]; omega
      · have hsub : A t \ (X.biUnion A).erase x ⊆ {x} := by
          intro z hz
          rw [Finset.mem_sdiff, Finset.mem_erase] at hz
          have : z ∈ X.biUnion A := Finset.mem_biUnion.mpr ⟨t, ht, hz.1⟩
          simp only [Finset.mem_singleton]
          by_contra hzx
          exact hz.2 ⟨hzx, this⟩
        simpa using Finset.card_le_card hsub
  obtain ⟨S, hS, hS2⟩ := key
  have hXsub : X ⊆ Finset.univ.filter (fun t : T => (A t \ S).card ≤ 1) := by
    intro t ht; simp [hS2 t ht]
  have := Finset.card_le_card hXsub
  have := h S
  omega

lemma biUnion_update_of_mem (A : T → Finset B) (t : T) (s : Finset B) (X : Finset T)
    (ht : t ∈ X) : X.biUnion (Function.update A t s) = (X.erase t).biUnion A ∪ s := by
  ext z
  simp only [Finset.mem_biUnion, Finset.mem_union, Finset.mem_erase]
  constructor
  · rintro ⟨u, hu, hz⟩
    by_cases hut : u = t
    · subst hut; right; simpa using hz
    · left; exact ⟨u, ⟨hut, hu⟩, by simpa [Function.update_of_ne hut] using hz⟩
  · rintro (⟨u, ⟨hut, hu⟩, hz⟩ | hz)
    · exact ⟨u, hu, by simpa [Function.update_of_ne hut] using hz⟩
    · exact ⟨t, ht, by simpa using hz⟩

lemma biUnion_update_of_not_mem (A : T → Finset B) (t : T) (s : Finset B) (X : Finset T)
    (ht : t ∉ X) : X.biUnion (Function.update A t s) = X.biUnion A := by
  apply Finset.biUnion_congr rfl
  intro u hu
  have : u ≠ t := fun h => ht (h ▸ hu)
  simp [Function.update_of_ne this]

/-- If removing `x` from `A t` breaks LC, there is a witness `P ⊆ T - t` with
`|A(P) ∪ (A t - x)| ≤ |P| + 1`. -/
lemma witness_of_not_lc (A : T → Finset B) (hA : (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion A).card)) (t : T) (x : B)
    (h : ¬ (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion (Function.update A t ((A t).erase x))).card)) :
    ∃ P : Finset T, t ∉ P ∧ (P.biUnion A ∪ (A t).erase x).card ≤ P.card + 1 := by
  beta_reduce at h
  push Not at h
  obtain ⟨X, hX, hlt⟩ := h
  by_cases ht : t ∈ X
  · refine ⟨X.erase t, Finset.notMem_erase t X, ?_⟩
    rw [biUnion_update_of_mem A t _ X ht] at hlt
    have := Finset.card_erase_add_one ht
    omega
  · rw [biUnion_update_of_not_mem A t _ X ht] at hlt
    have := hA X hX
    omega

/-- One shrinking step: if `|A t| ≥ 3` and `x ≠ y` in `A t`, removing `x` or removing `y`
keeps LC. -/
theorem shrink_step (A : T → Finset B) (hA : (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion A).card)) (t : T) (x y : B) (hx : x ∈ A t)
    (hy : y ∈ A t) (hxy : x ≠ y) (h3 : 3 ≤ (A t).card) :
    (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion (Function.update A t ((A t).erase x))).card) ∨ (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion (Function.update A t ((A t).erase y))).card) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨P, hPt, hP⟩ := witness_of_not_lc A hA t x hcon.1
  obtain ⟨Q, hQt, hQ⟩ := witness_of_not_lc A hA t y hcon.2
  set U := P.biUnion A ∪ (A t).erase x
  set W := Q.biUnion A ∪ (A t).erase y
  have hsum := Finset.card_union_add_card_inter U W
  -- the union contains A(insert t (P ∪ Q))
  have hun : (insert t (P ∪ Q)).biUnion A ⊆ U ∪ W := by
    intro z hz
    rw [Finset.biUnion_insert, Finset.mem_union] at hz
    rcases hz with hz | hz
    · by_cases hzx : z = x
      · subst hzx
        exact Finset.mem_union_right _ (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hxy, hz⟩))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hzx, hz⟩))
    · obtain ⟨u, hu, hzu⟩ := Finset.mem_biUnion.mp hz
      rcases Finset.mem_union.mp hu with hu | hu
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨u, hu, hzu⟩))
      · exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨u, hu, hzu⟩))
  have hint : (P ∩ Q).biUnion A ∪ ((A t).erase x).erase y ⊆ U ∩ W := by
    intro z hz
    rw [Finset.mem_union] at hz
    rcases hz with hz | hz
    · obtain ⟨u, hu, hzu⟩ := Finset.mem_biUnion.mp hz
      rw [Finset.mem_inter] at hu
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨u, hu.1, hzu⟩),
        Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨u, hu.2, hzu⟩)⟩
    · have h1 := Finset.mem_of_mem_erase hz
      have hzy := Finset.ne_of_mem_erase hz
      have hzx := Finset.ne_of_mem_erase h1
      have hzt := Finset.mem_of_mem_erase h1
      exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hzx, hzt⟩),
        Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hzy, hzt⟩)⟩
  have c1 := Finset.card_le_card hun
  have c2 := Finset.card_le_card hint
  have htPQ : t ∉ P ∪ Q := by simp [hPt, hQt]
  have l1 := hA (insert t (P ∪ Q)) (Finset.insert_nonempty _ _)
  rw [Finset.card_insert_of_notMem htPQ] at l1
  have l2 : (P ∩ Q).card + 1 ≤ ((P ∩ Q).biUnion A ∪ ((A t).erase x).erase y).card := by
    rcases (P ∩ Q).eq_empty_or_nonempty with he | hne
    · rw [he]
      have : ((A t).erase x).erase y ⊆ (P ∩ Q).biUnion A ∪ ((A t).erase x).erase y :=
        Finset.subset_union_right
      have e1 := Finset.card_erase_of_mem hx
      have e2 := Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hxy.symm, hy⟩)
      simp only [Finset.card_empty, Finset.biUnion_empty, Finset.empty_union]
      omega
    · have := hA _ hne
      have := Finset.card_le_card
        (Finset.subset_union_left (s₁ := (P ∩ Q).biUnion A) (s₂ := ((A t).erase x).erase y))
      omega
  have := Finset.card_union_add_card_inter P Q
  omega

/-- Lovász (pair form): LC ⟹ every set contains a 2-subset and the chosen 2-subsets satisfy LC. -/
theorem lovasz_pairs : ∀ (n : ℕ) (A : T → Finset B), (∑ t, (A t).card) ≤ n → (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion A).card) →
    ∃ e : T → B × B, (∀ t, (e t).1 ∈ A t ∧ (e t).2 ∈ A t ∧ (e t).1 ≠ (e t).2) ∧
      (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion (fun t => ({(e t).1, (e t).2} : Finset B))).card) := by
  intro n
  induction n with
  | zero =>
    intro A hs hA
    -- every set is empty; then T is empty by LC
    have hT : IsEmpty T := by
      by_contra hne
      rw [not_isEmpty_iff] at hne
      obtain ⟨t⟩ := hne
      have h1 := hA {t} (Finset.singleton_nonempty t)
      have : (A t).card = 0 := by
        have := Finset.single_le_sum (f := fun t => (A t).card) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ t)
        omega
      simp_all
    exact ⟨fun t => isEmptyElim t, fun t => isEmptyElim t, fun X hX => by
      obtain ⟨t, _⟩ := hX; exact isEmptyElim t⟩
  | succ n ih =>
    intro A hs hA
    by_cases hbig : ∃ t, 3 ≤ (A t).card
    · obtain ⟨t, ht⟩ := hbig
      obtain ⟨x, hx, y, hy, hxy⟩ : ∃ x ∈ A t, ∃ y ∈ A t, x ≠ y :=
        Finset.one_lt_card.mp (by omega)
      have step : ∀ z ∈ A t, (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion (Function.update A t ((A t).erase z))).card) →
          ∃ e : T → B × B, (∀ t, (e t).1 ∈ A t ∧ (e t).2 ∈ A t ∧ (e t).1 ≠ (e t).2) ∧
            (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion (fun t => ({(e t).1, (e t).2} : Finset B))).card) := by
        intro z hz hLC
        have hsum : (∑ u, (Function.update A t ((A t).erase z) u).card) ≤ n := by
          have key : (∑ u, (Function.update A t ((A t).erase z) u).card) + 1 =
              ∑ u, (A u).card := by
            rw [← Finset.add_sum_erase _ _ (Finset.mem_univ t), ← Finset.add_sum_erase _ _ (Finset.mem_univ t)]
            have hrest : ∑ u ∈ Finset.univ.erase t, (Function.update A t ((A t).erase z) u).card
                = ∑ u ∈ Finset.univ.erase t, (A u).card := by
              apply Finset.sum_congr rfl
              intro u hu
              rw [Function.update_of_ne (Finset.ne_of_mem_erase hu)]
            rw [hrest, Function.update_self, Finset.card_erase_of_mem hz]
            have : 1 ≤ (A t).card := by omega
            omega
          omega
        obtain ⟨e, he1, he2⟩ := ih _ hsum hLC
        refine ⟨e, fun u => ?_, he2⟩
        obtain ⟨a1, a2, a3⟩ := he1 u
        by_cases hu : u = t
        · subst hu
          simp only [Function.update_self] at a1 a2
          exact ⟨Finset.mem_of_mem_erase a1, Finset.mem_of_mem_erase a2, a3⟩
        · simp only [Function.update_of_ne hu] at a1 a2
          exact ⟨a1, a2, a3⟩
      rcases shrink_step A hA t x y hx hy hxy ht with h | h
      · exact step x hx h
      · exact step y hy h
    · push Not at hbig
      -- every set has exactly two elements
      have h2 : ∀ t, (A t).card = 2 := by
        intro t
        have := hA {t} (Finset.singleton_nonempty t)
        simp only [Finset.card_singleton, Finset.singleton_biUnion] at this
        have := hbig t
        omega
      have hex : ∀ t, ∃ p : B × B, A t = {p.1, p.2} ∧ p.1 ≠ p.2 := by
        intro t
        obtain ⟨a, b, hab, he⟩ := Finset.card_eq_two.mp (h2 t)
        exact ⟨(a, b), he, hab⟩
      choose e he using hex
      refine ⟨e, fun t => ?_, ?_⟩
      · rw [(he t).1]; exact ⟨by simp, by simp, (he t).2⟩
      · have : (fun t => ({(e t).1, (e t).2} : Finset B)) = A := by
          funext t; exact ((he t).1).symm
        rw [this]; exact hA



lemma biUnion_union_eq (A : T → Finset B) (X Y : Finset T) :
    (X ∪ Y).biUnion A = X.biUnion A ∪ Y.biUnion A := by
  ext z; simp only [Finset.mem_biUnion, Finset.mem_union]
  constructor
  · rintro ⟨u, hu | hu, hz⟩
    · exact Or.inl ⟨u, hu, hz⟩
    · exact Or.inr ⟨u, hu, hz⟩
  · rintro (⟨u, hu, hz⟩ | ⟨u, hu, hz⟩)
    · exact ⟨u, Or.inl hu, hz⟩
    · exact ⟨u, Or.inr hu, hz⟩

lemma biUnion_inter_sub (A : T → Finset B) (X Y : Finset T) :
    (X ∩ Y).biUnion A ⊆ X.biUnion A ∩ Y.biUnion A := by
  intro z hz
  obtain ⟨u, hu, hzu⟩ := Finset.mem_biUnion.mp hz
  rw [Finset.mem_inter] at hu
  exact Finset.mem_inter.mpr ⟨Finset.mem_biUnion.mpr ⟨u, hu.1, hzu⟩,
    Finset.mem_biUnion.mpr ⟨u, hu.2, hzu⟩⟩

/-- Lemma LT: under HP, disjoint L-tight sets have disjoint neighbourhoods. -/
theorem lemma_LT (A : T → Finset B) (h : (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)) (P Q : Finset T) (hP : (P.Nonempty ∧ (P.biUnion A).card = P.card + 1))
    (hQ : (Q.Nonempty ∧ (Q.biUnion A).card = Q.card + 1)) (hPQ : Disjoint P Q) : Disjoint (P.biUnion A) (Q.biUnion A) := by
  rw [Finset.disjoint_iff_ne]
  rintro x hxP _ hxQ rfl
  have hLC := lc_of_hp A h
  have hP2 := hP.2
  have hQ2 := hQ.2
  have hu := hLC (P ∪ Q) (hP.1.mono Finset.subset_union_left)
  rw [Finset.card_union_of_disjoint hPQ, biUnion_union_eq] at hu
  have hsum := Finset.card_union_add_card_inter (P.biUnion A) (Q.biUnion A)
  have hint1 : (P.biUnion A ∩ Q.biUnion A).card ≤ 1 := by omega
  have hint : P.biUnion A ∩ Q.biUnion A = {x} := by
    have hxm : x ∈ P.biUnion A ∩ Q.biUnion A := Finset.mem_inter.mpr ⟨hxP, hxQ⟩
    exact Finset.eq_singleton_iff_unique_mem.mpr ⟨hxm, fun z hz =>
      Finset.card_le_one.mp hint1 z hz x hxm⟩
  obtain ⟨y1, hy1, hy1x⟩ : ∃ y1 ∈ P.biUnion A, y1 ≠ x := by
    have : 1 < (P.biUnion A).card := by have := hP.1.card_pos; omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp this
    by_cases hax : a = x
    · exact ⟨b, hb, fun hbx => hab (hax.trans hbx.symm)⟩
    · exact ⟨a, ha, hax⟩
  obtain ⟨y2, hy2, hy2x⟩ : ∃ y2 ∈ Q.biUnion A, y2 ≠ x := by
    have : 1 < (Q.biUnion A).card := by have := hQ.1.card_pos; omega
    obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp this
    by_cases hax : a = x
    · exact ⟨b, hb, fun hbx => hab (hax.trans hbx.symm)⟩
    · exact ⟨a, ha, hax⟩
  have notin : ∀ z, z ∈ P.biUnion A → z ∈ Q.biUnion A → z = x := by
    intro z h1 h2
    have : z ∈ P.biUnion A ∩ Q.biUnion A := Finset.mem_inter.mpr ⟨h1, h2⟩
    rw [hint] at this; simpa using this
  have hy12 : y1 ≠ y2 := by
    rintro rfl; exact hy1x (notin y1 hy1 hy2)
  set S := (P.biUnion A ∪ Q.biUnion A).erase y1 |>.erase y2 with hS
  have hScard : S.card + 1 = P.card + Q.card := by
    have m1 : y1 ∈ P.biUnion A ∪ Q.biUnion A := Finset.mem_union_left _ hy1
    have m2 : y2 ∈ (P.biUnion A ∪ Q.biUnion A).erase y1 :=
      Finset.mem_erase.mpr ⟨hy12.symm, Finset.mem_union_right _ hy2⟩
    rw [hS, Finset.card_erase_of_mem m2, Finset.card_erase_of_mem m1]
    rw [hint, Finset.card_singleton] at hsum
    have : 2 ≤ (P.biUnion A ∪ Q.biUnion A).card := by
      have := Finset.card_le_card (Finset.subset_union_left (s₁ := P.biUnion A)
        (s₂ := Q.biUnion A))
      have := hP.1.card_pos
      omega
    omega
  have hsub : P ∪ Q ⊆ Finset.univ.filter (fun t : T => (A t \ S).card ≤ 1) := by
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases Finset.mem_union.mp ht with ht | ht
    · have : A t \ S ⊆ {y1} := by
        intro z hz
        rw [Finset.mem_sdiff] at hz
        have hzP : z ∈ P.biUnion A := Finset.mem_biUnion.mpr ⟨t, ht, hz.1⟩
        rw [Finset.mem_singleton]
        by_contra hzy1
        apply hz.2
        rw [hS, Finset.mem_erase, Finset.mem_erase]
        refine ⟨?_, hzy1, Finset.mem_union_left _ hzP⟩
        rintro rfl; exact hy2x (notin _ hzP hy2)
      simpa using Finset.card_le_card this
    · have : A t \ S ⊆ {y2} := by
        intro z hz
        rw [Finset.mem_sdiff] at hz
        have hzQ : z ∈ Q.biUnion A := Finset.mem_biUnion.mpr ⟨t, ht, hz.1⟩
        rw [Finset.mem_singleton]
        by_contra hzy2
        apply hz.2
        rw [hS, Finset.mem_erase, Finset.mem_erase]
        refine ⟨hzy2, ?_, Finset.mem_union_right _ hzQ⟩
        rintro rfl; exact hy1x (notin _ hy1 hzQ)
      simpa using Finset.card_le_card this
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hPQ] at this
  have := h S
  omega

/-- Closure: two L-tight sets whose neighbourhoods share `v` meet in an L-tight set whose
neighbourhood still contains `v`. -/
theorem tight_inter (A : T → Finset B) (h : (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)) (X Y : Finset T) (hX : (X.Nonempty ∧ (X.biUnion A).card = X.card + 1))
    (hY : (Y.Nonempty ∧ (Y.biUnion A).card = Y.card + 1)) (v : B) (hvX : v ∈ X.biUnion A) (hvY : v ∈ Y.biUnion A) :
    ((X ∩ Y).Nonempty ∧ ((X ∩ Y).biUnion A).card = (X ∩ Y).card + 1) ∧ v ∈ (X ∩ Y).biUnion A := by
  have hLC := lc_of_hp A h
  have hne : (X ∩ Y).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have hd : Disjoint X Y := Finset.disjoint_iff_inter_eq_empty.mpr he
    have := lemma_LT A h X Y hX hY hd
    exact Finset.disjoint_left.mp this hvX hvY
  have h1 := hLC (X ∪ Y) (hX.1.mono Finset.subset_union_left)
  have h2 := hLC (X ∩ Y) hne
  rw [biUnion_union_eq] at h1
  have hsubm := Finset.card_union_add_card_inter (X.biUnion A) (Y.biUnion A)
  have hsub := biUnion_inter_sub A X Y
  have hc := Finset.card_le_card hsub
  have hXY := Finset.card_union_add_card_inter X Y
  have hXt := hX.2
  have hYt := hY.2
  refine ⟨⟨hne, by omega⟩, ?_⟩
  have heq : (X ∩ Y).biUnion A = X.biUnion A ∩ Y.biUnion A :=
    Finset.eq_of_subset_of_card_le hsub (by omega)
  rw [heq]; exact Finset.mem_inter.mpr ⟨hvX, hvY⟩


lemma biUnion_sub_insert (A : T → Finset B) (v : B) (t0 : T) (X : Finset T) :
    X.biUnion A ⊆ insert v (X.biUnion ((fun kpt => if kpt = t0 then A kpt else (A kpt).erase v))) := by
  intro z hz
  obtain ⟨u, hu, hzu⟩ := Finset.mem_biUnion.mp hz
  by_cases hzv : z = v
  · exact hzv ▸ Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    refine Finset.mem_biUnion.mpr ⟨u, hu, ?_⟩
    beta_reduce
    split_ifs
    · exact hzu
    · exact Finset.mem_erase.mpr ⟨hzv, hzu⟩

lemma biUnion_sub_keep (A : T → Finset B) (v : B) (t0 : T) (X : Finset T) (hv : v ∈ A t0)
    (hc : t0 ∈ X ∨ v ∉ X.biUnion A) :
    X.biUnion A ⊆ X.biUnion ((fun kpt => if kpt = t0 then A kpt else (A kpt).erase v)) := by
  intro z hz
  obtain ⟨u, hu, hzu⟩ := Finset.mem_biUnion.mp hz
  by_cases hzv : z = v
  · subst hzv
    rcases hc with hc | hc
    · exact Finset.mem_biUnion.mpr ⟨t0, hc, by simp [hv]⟩
    · exact absurd hz hc
  · refine Finset.mem_biUnion.mpr ⟨u, hu, ?_⟩
    beta_reduce
    split_ifs
    · exact hzu
    · exact Finset.mem_erase.mpr ⟨hzv, hzu⟩

/-- Theorem RF1: under HP, for every element `v` lying in some set there is a set `A t0 ∋ v`
such that deleting `v` from all the other sets keeps LC. -/
theorem theorem_RF1 (A : T → Finset B) (h : (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)) (v : B) (hv : ∃ t, v ∈ A t) :
    ∃ t0, v ∈ A t0 ∧ (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion ((fun kpt => if kpt = t0 then A kpt else (A kpt).erase v))).card) := by
  classical
  have hLC := lc_of_hp A h
  by_contra hcon
  push Not at hcon
  -- witnesses
  have wit : ∀ t0, v ∈ A t0 → ∃ X : Finset T, (X.Nonempty ∧ (X.biUnion A).card = X.card + 1) ∧ t0 ∉ X ∧ v ∈ X.biUnion A := by
    intro t0 ht0
    have hn := hcon t0 ht0
    obtain ⟨X, hX, hlt⟩ := hn
    have hge := hLC X hX
    have hins := Finset.card_le_card (biUnion_sub_insert A v t0 X)
    have hins2 := Finset.card_insert_le v (X.biUnion ((fun kpt => if kpt = t0 then A kpt else (A kpt).erase v)))
    have hnot : ¬ (t0 ∈ X ∨ v ∉ X.biUnion A) := by
      intro hc
      have := Finset.card_le_card (biUnion_sub_keep A v t0 X ht0 hc)
      omega
    push Not at hnot
    exact ⟨X, ⟨hX, by omega⟩, hnot.1, hnot.2⟩
  choose! W hW using wit
  obtain ⟨t1, ht1⟩ := hv
  set C := (Finset.univ : Finset (Finset T)).filter (fun X => (X.Nonempty ∧ (X.biUnion A).card = X.card + 1) ∧ v ∈ X.biUnion A)
  have hCne : C.Nonempty :=
    ⟨W t1, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hW t1 ht1).1, (hW t1 ht1).2.2⟩⟩
  obtain ⟨I, hIC, hImin⟩ := Finset.exists_min_image C Finset.card hCne
  simp only [C, Finset.mem_filter, Finset.mem_univ, true_and] at hIC hImin
  have hIsub : ∀ t0, v ∈ A t0 → I ⊆ W t0 := by
    intro t0 ht0
    obtain ⟨hWt, _, hWv⟩ := hW t0 ht0
    obtain ⟨hT, hv'⟩ := tight_inter A h I (W t0) hIC.1 hWt v hIC.2 hWv
    have hle := hImin (I ∩ W t0) ⟨hT, hv'⟩
    have heq : I ∩ W t0 = I := Finset.eq_of_subset_of_card_le Finset.inter_subset_left hle
    rw [← heq]; exact Finset.inter_subset_right
  obtain ⟨s, hs, hvs⟩ := Finset.mem_biUnion.mp hIC.2
  exact (hW s hvs).2.1 (hIsub s hvs hs)

/-- Rainbow forest with a prescribed leaf (pair form of RF1 + Lovász). -/
theorem rainbow_leaf (A : T → Finset B) (h : (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)) (v : B) (hv : ∃ t, v ∈ A t) :
    ∃ t0, v ∈ A t0 ∧ ∃ e : T → B × B,
      (∀ t, (e t).1 ∈ (fun kpt => if kpt = t0 then A kpt else (A kpt).erase v) t ∧ (e t).2 ∈ (fun kpt => if kpt = t0 then A kpt else (A kpt).erase v) t ∧ (e t).1 ≠ (e t).2) ∧
      (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion (fun t => ({(e t).1, (e t).2} : Finset B))).card) := by
  obtain ⟨t0, ht0, hL⟩ := theorem_RF1 A h v hv
  exact ⟨t0, ht0, lovasz_pairs _ _ le_rfl hL⟩



omit [Fintype T] [DecidableEq T] in
lemma pg_adj (e : T → B × B) (x a : B) (h : ((SimpleGraph.fromRel (fun pgx pgy => ∃ pgt, e pgt = (pgx, pgy)))).Adj x a) :
    x ≠ a ∧ ∃ t, x ∈ ({(e t).1, (e t).2} : Finset B) ∧ a ∈ ({(e t).1, (e t).2} : Finset B) ∧ s((e t).1, (e t).2) = s(x, a) := by
  beta_reduce at h
  rw [SimpleGraph.fromRel_adj] at h
  obtain ⟨hne, ⟨t, ht⟩ | ⟨t, ht⟩⟩ := h
  · exact ⟨hne, t, by simp [ht], by simp [ht], by simp [ht]⟩
  · exact ⟨hne, t, by simp [ht], by simp [ht], by rw [ht]; exact Sym2.eq_swap⟩

omit [Fintype T] [DecidableEq T] in
/-- Distinct neighbours of `x` come from distinct pairs. -/
lemma pair_ne (e : T → B × B) (x a b : B) (ta tb : T) (hxa : x ≠ a) (hxb : x ≠ b) (hab : a ≠ b)
    (ha : x ∈ ({(e ta).1, (e ta).2} : Finset B) ∧ a ∈ ({(e ta).1, (e ta).2} : Finset B)) (hb : x ∈ ({(e tb).1, (e tb).2} : Finset B) ∧ b ∈ ({(e tb).1, (e tb).2} : Finset B)) : ta ≠ tb := by
  rintro rfl
  have hsub : ({x, a, b} : Finset B) ⊆ ({(e ta).1, (e ta).2} : Finset B) := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact ha.1
    · exact ha.2
    · exact hb.2
  have h3 : ({x, a, b} : Finset B).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair hab]
    simp [hxa, hxb]
  have h2 : (({(e ta).1, (e ta).2} : Finset B)).card ≤ 2 := Finset.card_le_two
  have := Finset.card_le_card hsub
  omega

/-- Bridge: pairs satisfying LC with element-degree bounds give the R3-style conclusion. -/
theorem bridge (e : T → B × B) (_hne : ∀ t, (e t).1 ≠ (e t).2) (hL : (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion ((fun prt => ({(e prt).1, (e prt).2} : Finset B)))).card))
    (hd2 : ∀ x, (Finset.univ.filter (fun t => x ∈ ({(e t).1, (e t).2} : Finset B))).card ≤ 2) (v : B)
    (hd1 : (Finset.univ.filter (fun t => v ∈ ({(e t).1, (e t).2} : Finset B))).card ≤ 1) :
    Function.Injective (fun t : T => s((e t).1, (e t).2)) ∧
      ((SimpleGraph.fromRel (fun pgx pgy => ∃ pgt, e pgt = (pgx, pgy)))).IsAcyclic ∧
      (∀ x a b c : B, ((SimpleGraph.fromRel (fun pgx pgy => ∃ pgt, e pgt = (pgx, pgy)))).Adj x a → ((SimpleGraph.fromRel (fun pgx pgy => ∃ pgt, e pgt = (pgx, pgy)))).Adj x b → ((SimpleGraph.fromRel (fun pgx pgy => ∃ pgt, e pgt = (pgx, pgy)))).Adj x c →
        a = b ∨ a = c ∨ b = c) ∧
      (∀ a b : B, ((SimpleGraph.fromRel (fun pgx pgy => ∃ pgt, e pgt = (pgx, pgy)))).Adj v a → ((SimpleGraph.fromRel (fun pgx pgy => ∃ pgt, e pgt = (pgx, pgy)))).Adj v b → a = b) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- injectivity
    intro t1 t2 h12
    by_contra hne12
    have hX := hL {t1, t2} (Finset.insert_nonempty _ _)
    rw [Finset.card_pair hne12] at hX
    have hpr : ({(e t2).1, (e t2).2} : Finset B) = ({(e t1).1, (e t1).2} : Finset B) := by
      simp only at h12
      rcases Sym2.eq_iff.mp h12 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp [h1, h2]
      · simp [h1, h2, Finset.pair_comm]
    have hU : ({t1, t2} : Finset T).biUnion ((fun prt => ({(e prt).1, (e prt).2} : Finset B))) = ({(e t1).1, (e t1).2} : Finset B) := by
      rw [Finset.biUnion_insert, Finset.singleton_biUnion, hpr, Finset.union_self]
    rw [hU] at hX
    have : (({(e t1).1, (e t1).2} : Finset B)).card ≤ 2 := Finset.card_le_two
    omega
  · -- acyclicity
    intro u c hc
    set X := Finset.univ.filter (fun t => s((e t).1, (e t).2) ∈ c.edges)
    have hcov : c.edges.toFinset ⊆ X.image (fun t => s((e t).1, (e t).2)) := by
      intro d hd
      rw [List.mem_toFinset] at hd
      have hdE := c.edges_subset_edgeSet hd
      induction d using Sym2.ind with
      | h x y =>
        rw [SimpleGraph.mem_edgeSet] at hdE
        obtain ⟨_, t, _, _, ht⟩ := pg_adj e x y hdE
        exact Finset.mem_image.mpr ⟨t, by simp [X, ht, hd], ht⟩
    have hlen : c.length ≤ X.card := by
      have h1 := List.toFinset_card_of_nodup hc.edges_nodup
      rw [SimpleGraph.Walk.length_edges] at h1
      have h2 := Finset.card_le_card hcov
      have h3 := Finset.card_image_le (s := X) (f := fun t => s((e t).1, (e t).2))
      omega
    have hsupp : X.biUnion ((fun prt => ({(e prt).1, (e prt).2} : Finset B))) ⊆ c.support.toFinset := by
      intro z hz
      obtain ⟨t, ht, hzt⟩ := Finset.mem_biUnion.mp hz
      simp only [X, Finset.mem_filter, Finset.mem_univ, true_and] at ht
      rw [List.mem_toFinset]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hzt
      rcases hzt with rfl | rfl
      · exact c.fst_mem_support_of_mem_edges ht
      · exact c.snd_mem_support_of_mem_edges ht
    have hsc : c.support.toFinset.card ≤ c.length := by
      have hmem := SimpleGraph.Walk.end_mem_tail_support hc.not_nil
      rw [← c.cons_tail_support, List.toFinset_cons, Finset.insert_eq_of_mem
        (List.mem_toFinset.mpr hmem)]
      have h1 := List.toFinset_card_le c.support.tail
      have h2 := c.length_support
      rw [← c.cons_tail_support] at h2
      simp only [List.length_cons] at h2
      omega
    have hXne : X.Nonempty := by
      rw [← Finset.card_pos]
      have : 0 < c.length := by
        rcases c with _ | ⟨_, _⟩
        · exact absurd SimpleGraph.Walk.Nil.nil hc.not_nil
        · simp
      omega
    have := hL X hXne
    have := Finset.card_le_card hsupp
    omega
  · -- degree at most two
    intro x a b c ha hb hc
    by_contra hcon
    push Not at hcon
    obtain ⟨hab, hac, hbc⟩ := hcon
    obtain ⟨hxa, ta, ha1, ha2, _⟩ := pg_adj e x a ha
    obtain ⟨hxb, tb, hb1, hb2, _⟩ := pg_adj e x b hb
    obtain ⟨hxc, tc, hc1, hc2, _⟩ := pg_adj e x c hc
    have n1 := pair_ne e x a b ta tb hxa hxb hab ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    have n2 := pair_ne e x a c ta tc hxa hxc hac ⟨ha1, ha2⟩ ⟨hc1, hc2⟩
    have n3 := pair_ne e x b c tb tc hxb hxc hbc ⟨hb1, hb2⟩ ⟨hc1, hc2⟩
    have hsub : ({ta, tb, tc} : Finset T) ⊆ Finset.univ.filter (fun t => x ∈ ({(e t).1, (e t).2} : Finset B)) := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and] <;> assumption
    have h3 : ({ta, tb, tc} : Finset T).card = 3 := by
      rw [Finset.card_insert_of_notMem, Finset.card_pair n3]
      simp [n1, n2]
    have := Finset.card_le_card hsub
    have := hd2 x
    omega
  · -- degree of v at most one
    intro a b ha hb
    by_contra hab
    obtain ⟨hva, ta, ha1, ha2, _⟩ := pg_adj e v a ha
    obtain ⟨hvb, tb, hb1, hb2, _⟩ := pg_adj e v b hb
    have n1 := pair_ne e v a b ta tb hva hvb hab ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    have hsub : ({ta, tb} : Finset T) ⊆ Finset.univ.filter (fun t => v ∈ ({(e t).1, (e t).2} : Finset B)) := by
      intro t ht
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl <;> simp only [Finset.mem_filter, Finset.mem_univ, true_and] <;> assumption
    have := Finset.card_le_card hsub
    rw [Finset.card_pair n1] at this
    omega

/-- Theorem GL (pure form): HP and every element in at most two sets ⟹ P1. -/
theorem theorem_GL (A : T → Finset B) (h : (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card))
    (hdeg : ∀ b, (Finset.univ.filter (fun t => b ∈ A t)).card ≤ 2) (v : B) :
    ∃ e : T → B × B, (∀ t, (e t).1 ∈ A t ∧ (e t).2 ∈ A t ∧ (e t).1 ≠ (e t).2) ∧
      (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion ((fun prt => ({(e prt).1, (e prt).2} : Finset B)))).card) ∧ (∀ x, (Finset.univ.filter (fun t => x ∈ ({(e t).1, (e t).2} : Finset B))).card ≤ 2) ∧
      (Finset.univ.filter (fun t => v ∈ ({(e t).1, (e t).2} : Finset B))).card ≤ 1 := by
  have hpA : ∀ e : T → B × B, (∀ t, (e t).1 ∈ A t ∧ (e t).2 ∈ A t) →
      ∀ x, (Finset.univ.filter (fun t => x ∈ ({(e t).1, (e t).2} : Finset B))).card ≤ 2 := by
    intro e he x
    refine le_trans (Finset.card_le_card ?_) (hdeg x)
    intro t ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton] at ht ⊢
    rcases ht with rfl | rfl
    · exact (he t).1
    · exact (he t).2
  by_cases hv : ∃ t, v ∈ A t
  · obtain ⟨t0, _, e, he, hL⟩ := rainbow_leaf A h v hv
    have heA : ∀ t, (e t).1 ∈ A t ∧ (e t).2 ∈ A t ∧ (e t).1 ≠ (e t).2 := by
      intro t
      obtain ⟨h1, h2, h3⟩ := he t
      beta_reduce at h1 h2
      split_ifs at h1 h2
      · exact ⟨h1, h2, h3⟩
      · exact ⟨Finset.mem_of_mem_erase h1, Finset.mem_of_mem_erase h2, h3⟩
    refine ⟨e, heA, hL, hpA e (fun t => ⟨(heA t).1, (heA t).2.1⟩), ?_⟩
    have : Finset.univ.filter (fun t => v ∈ ({(e t).1, (e t).2} : Finset B)) ⊆ {t0} := by
      intro t ht
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton] at ht ⊢
      by_contra htt
      obtain ⟨h1, h2, _⟩ := he t
      simp only [htt, if_false] at h1 h2
      rcases ht with ht | ht
      · rw [← ht] at h1; exact Finset.notMem_erase _ _ h1
      · rw [← ht] at h2; exact Finset.notMem_erase _ _ h2
    simpa using Finset.card_le_card this
  · push Not at hv
    obtain ⟨e, he, hL⟩ := lovasz_pairs _ A le_rfl (lc_of_hp A h)
    refine ⟨e, he, hL, hpA e (fun t => ⟨(he t).1, (he t).2.1⟩), ?_⟩
    have : Finset.univ.filter (fun t => v ∈ ({(e t).1, (e t).2} : Finset B)) = ∅ := by
      apply Finset.filter_false_of_mem
      intro t _ hvt
      simp only [Finset.mem_insert, Finset.mem_singleton] at hvt
      rcases hvt with hvt | hvt
      · exact hv t (hvt ▸ (he t).1)
      · exact hv t (hvt ▸ (he t).2.1)
    rw [this]
    simp

/-- Theorem GL in the graph form of the R3 statement `H1` (restricted to families in which every
element lies in at most two sets; no criticality needed). -/
theorem GL_R3form (A : T → Finset B) (h : (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card))
    (hdeg : ∀ b, (Finset.univ.filter (fun t => b ∈ A t)).card ≤ 2) (v : B) :
    ∃ e : T → B × B,
      (∀ t : T, (e t).1 ∈ A t ∧ (e t).2 ∈ A t ∧ (e t).1 ≠ (e t).2) ∧
      Function.Injective (fun t : T => s((e t).1, (e t).2)) ∧
      (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).IsAcyclic ∧
      (∀ x a b c : B,
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj x a →
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj x b →
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj x c →
        a = b ∨ a = c ∨ b = c) ∧
      (∀ a b : B,
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj v a →
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj v b → a = b) := by
  obtain ⟨e, he, hL, hd2, hd1⟩ := theorem_GL A h hdeg v
  obtain ⟨b1, b2, b3, b4⟩ := bridge e (fun t => (he t).2.2) hL hd2 v hd1
  exact ⟨e, he, b1, b2, b3, b4⟩



/-- HP is inherited by subfamilies. -/
theorem hp_sub {T' : Type} [Fintype T'] (A : T → Finset B) (h : (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)) (f : T' → T)
    (hf : Function.Injective f) : (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => ((fun t => A (f t)) hpt \ hpS).card ≤ 1)).card ≤ hpS.card) := by
  intro S
  have hsub : (Finset.univ.filter (fun t : T' => (A (f t) \ S).card ≤ 1)).map ⟨f, hf⟩ ⊆
      Finset.univ.filter (fun t : T => (A t \ S).card ≤ 1) := by
    intro t ht
    obtain ⟨t', ht', rfl⟩ := Finset.mem_map.mp ht
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht' ⊢
    exact ht'
  have := Finset.card_le_card hsub
  rw [Finset.card_map] at this
  exact this.trans (h S)

/-- Lemma SEP (case `Z = {b}`, two parts): deleting `b` from all sets, at most one of two
complementary subfamilies violates HP. -/
theorem lemma_SEP (A : T → Finset B) (h : (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)) (b : B) (p : T → Prop) [DecidablePred p] :
    (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => ((fun t : {t // p t} => (A t.1).erase b) hpt \ hpS).card ≤ 1)).card ≤ hpS.card) ∨ (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => ((fun t : {t // ¬ p t} => (A t.1).erase b) hpt \ hpS).card ≤ 1)).card ≤ hpS.card) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  obtain ⟨S1, hS1⟩ := h1
  obtain ⟨S2, hS2⟩ := h2
  set S := insert b (S1 ∪ S2)
  have hS : S.card ≤ S1.card + S2.card + 1 := by
    show (insert b (S1 ∪ S2)).card ≤ _
    have := Finset.card_insert_le b (S1 ∪ S2)
    have := Finset.card_union_le S1 S2
    omega
  have key : ∀ (t : T) (S' : Finset B), S' ⊆ S → ((A t).erase b \ S').card ≤ 1 →
      (A t \ S).card ≤ 1 := by
    intro t S' hS' h'
    refine le_trans (Finset.card_le_card ?_) h'
    intro z hz
    rw [Finset.mem_sdiff] at hz ⊢
    refine ⟨Finset.mem_erase.mpr ⟨?_, hz.1⟩, fun hz' => hz.2 (hS' hz')⟩
    rintro rfl; exact hz.2 (Finset.mem_insert_self _ _)
  have hsub : (Finset.univ.filter (fun t : {t // p t} => ((A t.1).erase b \ S1).card ≤ 1)).map
        (Function.Embedding.subtype p) ∪
      (Finset.univ.filter (fun t : {t // ¬ p t} => ((A t.1).erase b \ S2).card ≤ 1)).map
        (Function.Embedding.subtype _) ⊆
      Finset.univ.filter (fun t : T => (A t \ S).card ≤ 1) := by
    intro t ht
    simp only [Finset.mem_union, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Function.Embedding.subtype_apply] at ht ⊢
    rcases ht with ⟨t', ht', rfl⟩ | ⟨t', ht', rfl⟩
    · exact key _ S1 (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_left _ hz)) ht'
    · exact key _ S2 (fun z hz => Finset.mem_insert_of_mem (Finset.mem_union_right _ hz)) ht'
  have hdisj : Disjoint
      ((Finset.univ.filter (fun t : {t // p t} => ((A t.1).erase b \ S1).card ≤ 1)).map
        (Function.Embedding.subtype p))
      ((Finset.univ.filter (fun t : {t // ¬ p t} => ((A t.1).erase b \ S2).card ≤ 1)).map
        (Function.Embedding.subtype _)) := by
    rw [Finset.disjoint_left]
    intro t ht1 ht2
    obtain ⟨t1, _, rfl⟩ := Finset.mem_map.mp ht1
    obtain ⟨t2, _, ht⟩ := Finset.mem_map.mp ht2
    simp only [Function.Embedding.subtype_apply] at ht
    exact t2.2 (ht ▸ t1.2)
  have := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_map, Finset.card_map] at this
  have := h S
  omega

omit [DecidableEq T] in
lemma card_split (p : T → Prop) [DecidablePred p] (q : T → Prop) [DecidablePred q] :
    (Finset.univ.filter q).card =
      (Finset.univ.filter (fun t : {t // p t} => q t.1)).card +
      (Finset.univ.filter (fun t : {t // ¬ p t} => q t.1)).card := by
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter]
  exact (Fintype.sum_subtype_add_sum_subtype p (fun t => if q t then 1 else 0)).symm

/-- Gluing two pair systems on disjoint ground sets. -/
theorem glue (A : T → Finset B) (p : T → Prop) [DecidablePred p]
    (A1 : {t // p t} → Finset B) (A2 : {t // ¬ p t} → Finset B)
    (hA1 : ∀ t, A1 t ⊆ A t.1) (hA2 : ∀ t, A2 t ⊆ A t.1) (C1 C2 : Finset B)
    (hC : Disjoint C1 C2) (hC1 : ∀ t, A1 t ⊆ C1) (hC2 : ∀ t, A2 t ⊆ C2) (v : B)
    (E1 : (∃ p1e : _ → _ × _, (∀ p1t, (p1e p1t).1 ∈ A1 p1t ∧ (p1e p1t).2 ∈ A1 p1t ∧ (p1e p1t).1 ≠ (p1e p1t).2) ∧ (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion ((fun prt => ({(p1e prt).1, (p1e prt).2} : Finset B)))).card) ∧ (∀ p1x, (Finset.univ.filter (fun p1t => p1x ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 2) ∧ (Finset.univ.filter (fun p1t => v ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 1)) (E2 : (∃ p1e : _ → _ × _, (∀ p1t, (p1e p1t).1 ∈ A2 p1t ∧ (p1e p1t).2 ∈ A2 p1t ∧ (p1e p1t).1 ≠ (p1e p1t).2) ∧ (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion ((fun prt => ({(p1e prt).1, (p1e prt).2} : Finset B)))).card) ∧ (∀ p1x, (Finset.univ.filter (fun p1t => p1x ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 2) ∧ (Finset.univ.filter (fun p1t => v ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 1)) : (∃ p1e : _ → _ × _, (∀ p1t, (p1e p1t).1 ∈ A p1t ∧ (p1e p1t).2 ∈ A p1t ∧ (p1e p1t).1 ≠ (p1e p1t).2) ∧ (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion ((fun prt => ({(p1e prt).1, (p1e prt).2} : Finset B)))).card) ∧ (∀ p1x, (Finset.univ.filter (fun p1t => p1x ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 2) ∧ (Finset.univ.filter (fun p1t => v ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 1) := by
  obtain ⟨e1, m1, L1, d1, v1⟩ := E1
  obtain ⟨e2, m2, L2, d2, v2⟩ := E2
  set e : T → B × B := fun t => if h : p t then e1 ⟨t, h⟩ else e2 ⟨t, h⟩ with he
  have pe1 : ∀ t (h : p t), ({(e t).1, (e t).2} : Finset B) = ({(e1 (⟨t, h⟩)).1, (e1 (⟨t, h⟩)).2} : Finset B) := by
    intro t h; simp [he, h]
  have pe2 : ∀ t (h : ¬ p t), ({(e t).1, (e t).2} : Finset B) = ({(e2 (⟨t, h⟩)).1, (e2 (⟨t, h⟩)).2} : Finset B) := by
    intro t h; simp [he, h]
  have s1 : ∀ t, ({(e1 t).1, (e1 t).2} : Finset B) ⊆ C1 := by
    intro t z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hC1 t (m1 t).1
    · exact hC1 t (m1 t).2.1
  have s2 : ∀ t, ({(e2 t).1, (e2 t).2} : Finset B) ⊆ C2 := by
    intro t z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hC2 t (m2 t).1
    · exact hC2 t (m2 t).2.1
  have cnt : ∀ x, (Finset.univ.filter (fun t => x ∈ ({(e t).1, (e t).2} : Finset B))).card =
      (Finset.univ.filter (fun t => x ∈ ({(e1 t).1, (e1 t).2} : Finset B))).card +
      (Finset.univ.filter (fun t => x ∈ ({(e2 t).1, (e2 t).2} : Finset B))).card := by
    intro x
    rw [card_split p]
    congr 1
    · congr 1; ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [pe1 t.1 t.2]
    · congr 1; ext t; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; rw [pe2 t.1 t.2]
  have zero1 : ∀ x, x ∉ C1 → (Finset.univ.filter (fun t => x ∈ ({(e1 t).1, (e1 t).2} : Finset B))).card = 0 := by
    intro x hx
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun t _ ht => hx (s1 t ht)
  have zero2 : ∀ x, x ∉ C2 → (Finset.univ.filter (fun t => x ∈ ({(e2 t).1, (e2 t).2} : Finset B))).card = 0 := by
    intro x hx
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    exact fun t _ ht => hx (s2 t ht)
  refine ⟨e, fun t => ?_, ?_, fun x => ?_, ?_⟩
  · by_cases h : p t
    · simp only [he, h, dif_pos]
      exact ⟨hA1 _ (m1 _).1, hA1 _ (m1 _).2.1, (m1 _).2.2⟩
    · simp only [he, h, dif_neg, not_false_eq_true]
      exact ⟨hA2 _ (m2 _).1, hA2 _ (m2 _).2.1, (m2 _).2.2⟩
  · intro X hX
    set X1 := X.subtype p
    set X2 := X.subtype (fun t => ¬ p t)
    have hU : X.biUnion ((fun prt => ({(e prt).1, (e prt).2} : Finset B))) = X1.biUnion ((fun prt => ({(e1 prt).1, (e1 prt).2} : Finset B))) ∪ X2.biUnion ((fun prt => ({(e2 prt).1, (e2 prt).2} : Finset B))) := by
      ext z
      simp only [Finset.mem_biUnion, Finset.mem_union, X1, X2, Finset.mem_subtype]
      constructor
      · rintro ⟨t, ht, hz⟩
        by_cases h : p t
        · exact Or.inl ⟨⟨t, h⟩, ht, by rw [← pe1 t h]; exact hz⟩
        · exact Or.inr ⟨⟨t, h⟩, ht, by rw [← pe2 t h]; exact hz⟩
      · rintro (⟨t, ht, hz⟩ | ⟨t, ht, hz⟩)
        · exact ⟨t.1, ht, by rw [pe1 t.1 t.2]; exact hz⟩
        · exact ⟨t.1, ht, by rw [pe2 t.1 t.2]; exact hz⟩
    have hdisj : Disjoint (X1.biUnion ((fun prt => ({(e1 prt).1, (e1 prt).2} : Finset B)))) (X2.biUnion ((fun prt => ({(e2 prt).1, (e2 prt).2} : Finset B)))) := by
      rw [Finset.disjoint_left]
      intro z hz1 hz2
      obtain ⟨t, _, hz1⟩ := Finset.mem_biUnion.mp hz1
      obtain ⟨t', _, hz2⟩ := Finset.mem_biUnion.mp hz2
      exact Finset.disjoint_left.mp hC (s1 t hz1) (s2 t' hz2)
    have hXc : X.card = X1.card + X2.card := by
      rw [Finset.card_subtype, Finset.card_subtype]
      exact (Finset.card_filter_add_card_filter_not (s := X) p).symm
    rw [hU, Finset.card_union_of_disjoint hdisj, hXc]
    rcases X1.eq_empty_or_nonempty with h1 | h1
    · rcases X2.eq_empty_or_nonempty with h2 | h2
      · exfalso
        have : X.card = 0 := by rw [hXc, h1, h2]; rfl
        exact hX.ne_empty (Finset.card_eq_zero.mp this)
      · have := L2 X2 h2
        rw [h1]; simp only [Finset.card_empty, Finset.biUnion_empty]
        omega
    · rcases X2.eq_empty_or_nonempty with h2 | h2
      · have := L1 X1 h1
        rw [h2]; simp only [Finset.card_empty, Finset.biUnion_empty]
        omega
      · exact le_trans (by omega) (Nat.add_le_add (L1 X1 h1) (L2 X2 h2))
  · rw [cnt x]
    by_cases hx : x ∈ C1
    · have hx2 : x ∉ C2 := Finset.disjoint_left.mp hC hx
      have hd := d1 x
      rw [zero2 x hx2]; omega
    · have hd := d2 x
      rw [zero1 x hx]; omega
  · rw [cnt v]
    by_cases hx : v ∈ C1
    · have hx2 : v ∉ C2 := Finset.disjoint_left.mp hC hx
      rw [zero2 v hx2]; omega
    · rw [zero1 v hx]; omega

/-- Theorem CE (cut element, two sides): if the sets split into two sides meeting only in `b`,
P1 for the family follows from P1 for the side families `F_i^+` (the sets of side `i`) and those
of the families `F_i^-` (side `i` with `b` deleted) that satisfy HP. -/
theorem theorem_CE (A : T → Finset B) (h : (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)) (b : B) (p : T → Prop) [DecidablePred p]
    (hsep : ∀ s s', p s → ¬ p s' → A s ∩ A s' ⊆ {b})
    (P1m1 : (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => ((fun t : {t // p t} => (A t.1).erase b) hpt \ hpS).card ≤ 1)).card ≤ hpS.card) →
      (∀ p1w, (∃ p1e : _ → _ × _, (∀ p1t, (p1e p1t).1 ∈ (fun t : {t // p t} => (A t.1).erase b) p1t ∧ (p1e p1t).2 ∈ (fun t : {t // p t} => (A t.1).erase b) p1t ∧ (p1e p1t).1 ≠ (p1e p1t).2) ∧ (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion ((fun prt => ({(p1e prt).1, (p1e prt).2} : Finset B)))).card) ∧ (∀ p1x, (Finset.univ.filter (fun p1t => p1x ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 2) ∧ (Finset.univ.filter (fun p1t => p1w ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 1)))
    (P1p1 : (∀ p1w, (∃ p1e : _ → _ × _, (∀ p1t, (p1e p1t).1 ∈ (fun t : {t // p t} => A t.1) p1t ∧ (p1e p1t).2 ∈ (fun t : {t // p t} => A t.1) p1t ∧ (p1e p1t).1 ≠ (p1e p1t).2) ∧ (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion ((fun prt => ({(p1e prt).1, (p1e prt).2} : Finset B)))).card) ∧ (∀ p1x, (Finset.univ.filter (fun p1t => p1x ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 2) ∧ (Finset.univ.filter (fun p1t => p1w ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 1)))
    (P1m2 : (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => ((fun t : {t // ¬ p t} => (A t.1).erase b) hpt \ hpS).card ≤ 1)).card ≤ hpS.card) →
      (∀ p1w, (∃ p1e : _ → _ × _, (∀ p1t, (p1e p1t).1 ∈ (fun t : {t // ¬ p t} => (A t.1).erase b) p1t ∧ (p1e p1t).2 ∈ (fun t : {t // ¬ p t} => (A t.1).erase b) p1t ∧ (p1e p1t).1 ≠ (p1e p1t).2) ∧ (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion ((fun prt => ({(p1e prt).1, (p1e prt).2} : Finset B)))).card) ∧ (∀ p1x, (Finset.univ.filter (fun p1t => p1x ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 2) ∧ (Finset.univ.filter (fun p1t => p1w ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 1)))
    (P1p2 : (∀ p1w, (∃ p1e : _ → _ × _, (∀ p1t, (p1e p1t).1 ∈ (fun t : {t // ¬ p t} => A t.1) p1t ∧ (p1e p1t).2 ∈ (fun t : {t // ¬ p t} => A t.1) p1t ∧ (p1e p1t).1 ≠ (p1e p1t).2) ∧ (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion ((fun prt => ({(p1e prt).1, (p1e prt).2} : Finset B)))).card) ∧ (∀ p1x, (Finset.univ.filter (fun p1t => p1x ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 2) ∧ (Finset.univ.filter (fun p1t => p1w ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 1))) : (∀ p1w, (∃ p1e : _ → _ × _, (∀ p1t, (p1e p1t).1 ∈ A p1t ∧ (p1e p1t).2 ∈ A p1t ∧ (p1e p1t).1 ≠ (p1e p1t).2) ∧ (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion ((fun prt => ({(p1e prt).1, (p1e prt).2} : Finset B)))).card) ∧ (∀ p1x, (Finset.univ.filter (fun p1t => p1x ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 2) ∧ (Finset.univ.filter (fun p1t => p1w ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 1)) := by
  intro v
  set D1 := (Finset.univ.filter p).biUnion A
  set D2 := (Finset.univ.filter (fun t => ¬ p t)).biUnion A
  have hD : ∀ z, z ∈ D1 → z ∈ D2 → z = b := by
    intro z h1 h2
    obtain ⟨s, hs, hz1⟩ := Finset.mem_biUnion.mp h1
    obtain ⟨s', hs', hz2⟩ := Finset.mem_biUnion.mp h2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs hs'
    have := hsep s s' hs hs' (Finset.mem_inter.mpr ⟨hz1, hz2⟩)
    simpa using this
  have in1 : ∀ t : {t // p t}, A t.1 ⊆ D1 := fun t =>
    Finset.subset_biUnion_of_mem A (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.2⟩)
  have in2 : ∀ t : {t // ¬ p t}, A t.1 ⊆ D2 := fun t =>
    Finset.subset_biUnion_of_mem A (Finset.mem_filter.mpr ⟨Finset.mem_univ _, t.2⟩)
  rcases lemma_SEP A h b p with hm | hm
  · refine glue A p _ _ (fun t => Finset.erase_subset _ _) (fun t => subset_rfl)
      (D1.erase b) D2 ?_ (fun t => Finset.erase_subset_erase _ (in1 t)) in2 v (P1m1 hm v) (P1p2 v)
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    exact Finset.ne_of_mem_erase hz1 (hD z (Finset.mem_of_mem_erase hz1) hz2)
  · refine glue A p _ _ (fun t => subset_rfl) (fun t => Finset.erase_subset _ _)
      D1 (D2.erase b) ?_ in1 (fun t => Finset.erase_subset_erase _ (in2 t)) v (P1p1 v) (P1m2 hm v)
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    exact Finset.ne_of_mem_erase hz2 (hD z hz1 (Finset.mem_of_mem_erase hz2))


omit [Fintype T] [DecidableEq T] in
/-- BLpure is inherited by subfamilies with smaller sets. -/
theorem blpure_mono {T' : Type} (A : T → Finset B) (h : (∀ (blb : _) (blt1 blt2 blt3 : _), blt1 ≠ blt2 → blt1 ≠ blt3 → blt2 ≠ blt3 → blb ∈ A blt1 → blb ∈ A blt2 → blb ∈ A blt3 → ∃ blp : _ → Prop, (∀ bls bls2, blp bls → ¬ blp bls2 → A bls ∩ A bls2 ⊆ {blb}) ∧ ¬ ((blp blt1 ↔ blp blt2) ∧ (blp blt1 ↔ blp blt3)))) (f : T' → T)
    (hf : Function.Injective f) (A' : T' → Finset B) (hA' : ∀ t, A' t ⊆ A (f t)) :
    (∀ (blb : _) (blt1 blt2 blt3 : _), blt1 ≠ blt2 → blt1 ≠ blt3 → blt2 ≠ blt3 → blb ∈ A' blt1 → blb ∈ A' blt2 → blb ∈ A' blt3 → ∃ blp : _ → Prop, (∀ bls bls2, blp bls → ¬ blp bls2 → A' bls ∩ A' bls2 ⊆ {blb}) ∧ ¬ ((blp blt1 ↔ blp blt2) ∧ (blp blt1 ↔ blp blt3))) := by
  intro b t1 t2 t3 h12 h13 h23 hb1 hb2 hb3
  obtain ⟨p, hsep, hns⟩ := h b (f t1) (f t2) (f t3) (fun e => h12 (hf e)) (fun e => h13 (hf e))
    (fun e => h23 (hf e)) (hA' _ hb1) (hA' _ hb2) (hA' _ hb3)
  refine ⟨fun s => p (f s), fun s s' hs hs' => ?_, hns⟩
  exact (Finset.inter_subset_inter (hA' s) (hA' s')).trans (hsep _ _ hs hs')

/-- Theorem BL (set-system form): HP and the block-class condition imply P1. -/
theorem theorem_BL : ∀ (n : ℕ) (T : Type) [Fintype T] [DecidableEq T] (A : T → Finset B),
    Fintype.card T = n → (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card) → (∀ (blb : _) (blt1 blt2 blt3 : _), blt1 ≠ blt2 → blt1 ≠ blt3 → blt2 ≠ blt3 → blb ∈ A blt1 → blb ∈ A blt2 → blb ∈ A blt3 → ∃ blp : _ → Prop, (∀ bls bls2, blp bls → ¬ blp bls2 → A bls ∩ A bls2 ⊆ {blb}) ∧ ¬ ((blp blt1 ↔ blp blt2) ∧ (blp blt1 ↔ blp blt3))) → (∀ p1w, (∃ p1e : _ → _ × _, (∀ p1t, (p1e p1t).1 ∈ A p1t ∧ (p1e p1t).2 ∈ A p1t ∧ (p1e p1t).1 ≠ (p1e p1t).2) ∧ (∀ lcX : Finset _, lcX.Nonempty → lcX.card + 1 ≤ (lcX.biUnion ((fun prt => ({(p1e prt).1, (p1e prt).2} : Finset B)))).card) ∧ (∀ p1x, (Finset.univ.filter (fun p1t => p1x ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 2) ∧ (Finset.univ.filter (fun p1t => p1w ∈ ({(p1e p1t).1, (p1e p1t).2} : Finset B))).card ≤ 1)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
  intro T _ _ A hn hHP hBL
  classical
  by_cases hthree : ∃ b, 2 < (Finset.univ.filter (fun t => b ∈ A t)).card
  · obtain ⟨b, hb⟩ := hthree
    obtain ⟨t1, ht1, t2, ht2, t3, ht3, h12, h13, h23⟩ := Finset.two_lt_card.mp hb
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ht1 ht2 ht3
    obtain ⟨p, hsep, hns⟩ := hBL b t1 t2 t3 h12 h13 h23 ht1 ht2 ht3
    have hboth : (∃ s, p s) ∧ (∃ s, ¬ p s) := by
      by_cases hp1 : p t1
      · by_cases hp2 : p t2
        · by_cases hp3 : p t3
          · exact absurd ⟨iff_of_true hp1 hp2, iff_of_true hp1 hp3⟩ hns
          · exact ⟨⟨t1, hp1⟩, ⟨t3, hp3⟩⟩
        · exact ⟨⟨t1, hp1⟩, ⟨t2, hp2⟩⟩
      · by_cases hp2 : p t2
        · exact ⟨⟨t2, hp2⟩, ⟨t1, hp1⟩⟩
        · by_cases hp3 : p t3
          · exact ⟨⟨t3, hp3⟩, ⟨t1, hp1⟩⟩
          · exact absurd ⟨iff_of_false hp1 hp2, iff_of_false hp1 hp3⟩ hns
    obtain ⟨⟨s1, hs1⟩, ⟨s2, hs2⟩⟩ := hboth
    have c1 : Fintype.card {t // p t} < n := hn ▸ Fintype.card_subtype_lt hs2
    have c2 : Fintype.card {t // ¬ p t} < n := hn ▸ Fintype.card_subtype_lt (not_not.mpr hs1)
    have v1 := Subtype.val_injective (p := p)
    have v2 := Subtype.val_injective (p := fun t => ¬ p t)
    exact theorem_CE A hHP b p hsep
      (fun hm => ih _ c1 {t // p t} _ rfl hm
        (blpure_mono A hBL Subtype.val v1 _ (fun t => Finset.erase_subset _ _)))
      (ih _ c1 {t // p t} _ rfl (hp_sub A hHP Subtype.val v1)
        (blpure_mono A hBL Subtype.val v1 _ (fun t => subset_rfl)))
      (fun hm => ih _ c2 {t // ¬ p t} _ rfl hm
        (blpure_mono A hBL Subtype.val v2 _ (fun t => Finset.erase_subset _ _)))
      (ih _ c2 {t // ¬ p t} _ rfl (hp_sub A hHP Subtype.val v2)
        (blpure_mono A hBL Subtype.val v2 _ (fun t => subset_rfl)))
  · push Not at hthree
    intro v
    obtain ⟨e, he, hL, hd2, hd1⟩ := theorem_GL A hHP hthree v
    exact ⟨e, he, hL, hd2, hd1⟩

/-- Theorem BL in the graph form of the R3 statement `H1`. -/
theorem BL_R3form (A : T → Finset B) (h : (∀ hpS : Finset B, (Finset.univ.filter (fun hpt => (A hpt \ hpS).card ≤ 1)).card ≤ hpS.card)) (hBL : (∀ (blb : _) (blt1 blt2 blt3 : _), blt1 ≠ blt2 → blt1 ≠ blt3 → blt2 ≠ blt3 → blb ∈ A blt1 → blb ∈ A blt2 → blb ∈ A blt3 → ∃ blp : _ → Prop, (∀ bls bls2, blp bls → ¬ blp bls2 → A bls ∩ A bls2 ⊆ {blb}) ∧ ¬ ((blp blt1 ↔ blp blt2) ∧ (blp blt1 ↔ blp blt3)))) (v : B) :
    ∃ e : T → B × B,
      (∀ t : T, (e t).1 ∈ A t ∧ (e t).2 ∈ A t ∧ (e t).1 ≠ (e t).2) ∧
      Function.Injective (fun t : T => s((e t).1, (e t).2)) ∧
      (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).IsAcyclic ∧
      (∀ x a b c : B,
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj x a →
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj x b →
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj x c →
        a = b ∨ a = c ∨ b = c) ∧
      (∀ a b : B,
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj v a →
        (SimpleGraph.fromRel (fun x y : B => ∃ t : T, e t = (x, y))).Adj v b → a = b) := by
  obtain ⟨e, he, hL, hd2, hd1⟩ := theorem_BL _ T A rfl h hBL v
  obtain ⟨b1, b2, b3, b4⟩ := bridge e (fun t => (he t).2.2) hL hd2 v hd1
  exact ⟨e, he, b1, b2, b3, b4⟩


end

section

private lemma p1_reach_map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (ψ : V → W)
    (hψ : ∀ u w, G.Adj u w → ψ u = ψ w ∨ H.Adj (ψ u) (ψ w)) {u w : V}
    (h : G.Reachable u w) : H.Reachable (ψ u) (ψ w) := by
  obtain ⟨p⟩ := h
  induction p with
  | nil => exact Reachable.refl _
  | cons hadj _ ih =>
    rcases hψ _ _ hadj with heq | hadj'
    · rw [heq]; exact ih
    · exact hadj'.reachable.trans ih

private lemma p1_path_interior {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v)
    (hp : p.IsPath) (x : V) (hx : x ∈ p.support) :
    x = u ∨ x = v ∨ ∃ a b, a ≠ b ∧ G.Adj x a ∧ G.Adj x b := by
  induction p with
  | nil =>
    left
    simpa using hx
  | @cons u w v h q ih =>
    rw [Walk.cons_isPath_iff] at hp
    rw [Walk.support_cons, List.mem_cons] at hx
    rcases hx with hxu | hx
    · exact Or.inl hxu
    · rcases ih hp.1 hx with hxw | hxv | h3
      · subst hxw
        cases q with
        | nil => exact Or.inr (Or.inl rfl)
        | @cons _ w' _ h' q' =>
          refine Or.inr (Or.inr ⟨u, w', ?_, h.symm, h'⟩)
          intro huw
          apply hp.2
          rw [Walk.support_cons, List.mem_cons]
          right
          rw [huw]
          exact q'.start_mem_support
      · exact Or.inr (Or.inl hxv)
      · exact Or.inr (Or.inr h3)

private lemma p1_reachable_of_mem_support {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) {x y : V} (hx : x ∈ p.support) (hy : y ∈ p.support) : G.Reachable x y :=
  (Walk.reachable (p.takeUntil x hx)).symm.trans (Walk.reachable (p.takeUntil y hy))

/-- A path whose vertex set contains a vertex `x` without two distinct neighbours can be
re-oriented to end at `x`. -/
private lemma p1_path_to_end {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) (hp : p.IsPath) (x : V) (hx : x ∈ p.support)
    (hdeg : ∀ a b, G.Adj x a → G.Adj x b → a = b) :
    ∃ (z : V) (q : G.Walk z x), q.IsPath ∧ q.support.toFinset = p.support.toFinset := by
  rcases p1_path_interior p hp x hx with rfl | rfl | ⟨a, b, hab, ha, hb⟩
  · refine ⟨v, p.reverse, hp.reverse, ?_⟩
    rw [Walk.support_reverse, List.toFinset_reverse]
  · exact ⟨u, p, hp, rfl⟩
  · exact (hab (hdeg a b ha hb)).elim

/-- Path cover from a linear forest given by a finite edge set: every edge is a bridge and no
vertex lies on three edges. -/
private lemma p1_linear_forest_cover {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (hdiag : ∀ x y, s(x, y) ∈ E → x ≠ y)
    (hdeg : ∀ x a b c, s(x, a) ∈ E → s(x, b) ∈ E → s(x, c) ∈ E → a = b ∨ a = c ∨ b = c)
    (hbr : ∀ x y, s(x, y) ∈ E →
      ¬ (fromEdgeSet ((E.erase s(x, y) : Finset (Sym2 V)) : Set (Sym2 V))).Reachable x y) :
    ∃ P : Finset (Finset V),
      (fromEdgeSet (E : Set (Sym2 V))).IsPathCover P ∧ P.card + E.card = Fintype.card V := by
  suffices hmain : ∀ E' : Finset (Sym2 V), E' ⊆ E → ∃ P : Finset (Finset V),
      (fromEdgeSet (E' : Set (Sym2 V))).IsPathCover P ∧ P.card + E'.card = Fintype.card V from
    hmain E (Finset.Subset.refl E)
  intro E'
  induction E' using Finset.induction_on with
  | empty =>
    intro _
    refine ⟨Finset.univ.image (fun x : V => ({x} : Finset V)), ⟨?_, ?_, ?_⟩, ?_⟩
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
    · rw [Finset.card_image_of_injective _ Finset.singleton_injective, Finset.card_empty,
        Finset.card_univ, Nat.add_zero]
  | @insert e E0 he ih =>
    intro hsub
    have hE0 : E0 ⊆ E := fun z hz => hsub (Finset.mem_insert_of_mem hz)
    have heE : e ∈ E := hsub (Finset.mem_insert_self e E0)
    obtain ⟨P0, hP0, hcard0⟩ := ih hE0
    obtain ⟨hdisj, hcov, hpaths⟩ := hP0
    induction e using Sym2.ind with
    | _ x y =>
    have hxy : x ≠ y := hdiag x y heE
    have hle : fromEdgeSet (E0 : Set (Sym2 V)) ≤
        fromEdgeSet ((insert s(x, y) E0 : Finset (Sym2 V)) : Set (Sym2 V)) := by
      apply fromEdgeSet_mono
      intro z hz
      exact Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp hz))
    have hadj : (fromEdgeSet ((insert s(x, y) E0 : Finset (Sym2 V)) : Set (Sym2 V))).Adj x y := by
      rw [fromEdgeSet_adj]
      exact ⟨Finset.mem_coe.mpr (Finset.mem_insert_self _ _), hxy⟩
    have hnr : ¬ (fromEdgeSet (E0 : Set (Sym2 V))).Reachable x y := by
      intro hr
      apply hbr x y heE
      refine hr.mono (fromEdgeSet_mono ?_)
      intro z hz
      rw [Finset.mem_coe, Finset.mem_erase]
      refine ⟨?_, hE0 (Finset.mem_coe.mp hz)⟩
      rintro rfl
      exact he (Finset.mem_coe.mp hz)
    have hdx : ∀ a b, (fromEdgeSet (E0 : Set (Sym2 V))).Adj x a →
        (fromEdgeSet (E0 : Set (Sym2 V))).Adj x b → a = b := by
      intro a b ha hb
      rw [fromEdgeSet_adj] at ha hb
      have ha' : s(x, a) ∈ E0 := Finset.mem_coe.mp ha.1
      have hb' : s(x, b) ∈ E0 := Finset.mem_coe.mp hb.1
      rcases hdeg x a b y (hE0 ha') (hE0 hb') heE with h | h | h
      · exact h
      · exact (he (h ▸ ha')).elim
      · exact (he (h ▸ hb')).elim
    have hdy : ∀ a b, (fromEdgeSet (E0 : Set (Sym2 V))).Adj y a →
        (fromEdgeSet (E0 : Set (Sym2 V))).Adj y b → a = b := by
      intro a b ha hb
      rw [fromEdgeSet_adj] at ha hb
      have ha' : s(y, a) ∈ E0 := Finset.mem_coe.mp ha.1
      have hb' : s(y, b) ∈ E0 := Finset.mem_coe.mp hb.1
      have heE' : s(y, x) ∈ E := Sym2.eq_swap ▸ heE
      have he' : s(y, x) ∉ E0 := Sym2.eq_swap ▸ he
      rcases hdeg y a b x (hE0 ha') (hE0 hb') heE' with h | h | h
      · exact h
      · exact (he' (h ▸ ha')).elim
      · exact (he' (h ▸ hb')).elim
    obtain ⟨s1, hs1P, hxs1⟩ : ∃ s ∈ P0, x ∈ s := by
      have := hcov (Finset.mem_univ x)
      rw [Finset.mem_biUnion] at this
      exact this
    obtain ⟨s2, hs2P, hys2⟩ : ∃ s ∈ P0, y ∈ s := by
      have := hcov (Finset.mem_univ y)
      rw [Finset.mem_biUnion] at this
      exact this
    obtain ⟨u1, v1, p1, hp1, hs1eq⟩ := hpaths s1 hs1P
    obtain ⟨u2, v2, p2, hp2, hs2eq⟩ := hpaths s2 hs2P
    have hx1 : x ∈ p1.support := by
      rw [hs1eq] at hxs1
      exact List.mem_toFinset.mp hxs1
    have hy2 : y ∈ p2.support := by
      rw [hs2eq] at hys2
      exact List.mem_toFinset.mp hys2
    have hs12 : s1 ≠ s2 := by
      intro h
      apply hnr
      have hy1 : y ∈ p1.support := by
        rw [← h, hs1eq] at hys2
        exact List.mem_toFinset.mp hys2
      exact p1_reachable_of_mem_support p1 hx1 hy1
    have hd12 : Disjoint s1 s2 := hdisj s1 hs1P s2 hs2P hs12
    obtain ⟨z1, q1, hq1, hq1s⟩ := p1_path_to_end p1 hp1 x hx1 hdx
    obtain ⟨z2, q2, hq2, hq2s⟩ := p1_path_to_end p2 hp2 y hy2 hdy
    rw [← hs1eq] at hq1s
    rw [← hs2eq] at hq2s
    let w := (q1.mapLe hle).append (Walk.cons hadj (q2.mapLe hle).reverse)
    have hwsupp : w.support = q1.support ++ q2.support.reverse := by
      simp only [w, Walk.support_append, Walk.support_cons, List.tail_cons, Walk.support_reverse,
        Walk.support_mapLe_eq_support]
    have hwpath : w.IsPath := by
      rw [Walk.isPath_def, hwsupp, List.nodup_append]
      refine ⟨hq1.support_nodup, List.nodup_reverse.mpr hq2.support_nodup, ?_⟩
      intro a ha b hb hab
      subst hab
      have h1 : a ∈ s1 := by
        rw [← hq1s]
        exact List.mem_toFinset.mpr ha
      have h2 : a ∈ s2 := by
        rw [← hq2s]
        exact List.mem_toFinset.mpr (List.mem_reverse.mp hb)
      exact Finset.disjoint_left.mp hd12 h1 h2
    have hwfin : s1 ∪ s2 = w.support.toFinset := by
      rw [hwsupp, List.toFinset_append, List.toFinset_reverse, hq1s, hq2s]
    have hs2P' : s2 ∈ P0.erase s1 := Finset.mem_erase.mpr ⟨fun h => hs12 h.symm, hs2P⟩
    have hnew : s1 ∪ s2 ∉ (P0.erase s1).erase s2 := by
      intro h
      have h3 := Finset.mem_erase.mp h
      have h4 := Finset.mem_erase.mp h3.2
      have hd := hdisj (s1 ∪ s2) h4.2 s1 hs1P h4.1
      exact Finset.disjoint_left.mp hd (Finset.mem_union_left _ hxs1) hxs1
    refine ⟨insert (s1 ∪ s2) ((P0.erase s1).erase s2), ⟨?_, ?_, ?_⟩, ?_⟩
    · have hkey : ∀ t ∈ (P0.erase s1).erase s2, Disjoint (s1 ∪ s2) t := by
        intro t ht
        have h3 := Finset.mem_erase.mp ht
        have h4 := Finset.mem_erase.mp h3.2
        rw [Finset.disjoint_union_left]
        exact ⟨hdisj s1 hs1P t h4.2 (Ne.symm h4.1), hdisj s2 hs2P t h4.2 (Ne.symm h3.1)⟩
      intro t1 ht1 t2 ht2 hne
      rcases Finset.mem_insert.mp ht1 with rfl | ht1'
      · rcases Finset.mem_insert.mp ht2 with rfl | ht2'
        · exact (hne rfl).elim
        · exact hkey t2 ht2'
      · rcases Finset.mem_insert.mp ht2 with rfl | ht2'
        · exact (hkey t1 ht1').symm
        · exact hdisj t1 (Finset.mem_erase.mp (Finset.mem_erase.mp ht1').2).2 t2
            (Finset.mem_erase.mp (Finset.mem_erase.mp ht2').2).2 hne
    · intro a _
      have := hcov (Finset.mem_univ a)
      rw [Finset.mem_biUnion] at this ⊢
      obtain ⟨t, htP, hat⟩ := this
      by_cases ht1 : t = s1
      · exact ⟨s1 ∪ s2, Finset.mem_insert_self _ _, Finset.mem_union_left _ (ht1 ▸ hat)⟩
      · by_cases ht2 : t = s2
        · exact ⟨s1 ∪ s2, Finset.mem_insert_self _ _, Finset.mem_union_right _ (ht2 ▸ hat)⟩
        · exact ⟨t, Finset.mem_insert_of_mem
            (Finset.mem_erase.mpr ⟨ht2, Finset.mem_erase.mpr ⟨ht1, htP⟩⟩), hat⟩
    · intro t ht
      rcases Finset.mem_insert.mp ht with rfl | ht'
      · exact ⟨z1, z2, w, hwpath, hwfin⟩
      · obtain ⟨a, b, p, hp, hpe⟩ := hpaths t (Finset.mem_erase.mp (Finset.mem_erase.mp ht').2).2
        refine ⟨a, b, p.mapLe hle, hp.mapLe hle, ?_⟩
        rw [Walk.support_mapLe_eq_support]
        exact hpe
    · rw [Finset.card_insert_of_notMem hnew, Finset.card_erase_of_mem hs2P',
        Finset.card_erase_of_mem hs1P, Finset.card_insert_of_notMem he]
      have h1 : 0 < P0.card := Finset.card_pos.mpr ⟨s1, hs1P⟩
      have h2 : 0 < (P0.erase s1).card := Finset.card_pos.mpr ⟨s2, hs2P'⟩
      rw [Finset.card_erase_of_mem hs1P] at h2
      omega

/-- Exchange: adding to a subforest an independent set of vertices each having at most one
neighbour in it keeps the induced graph acyclic. -/
private lemma p1_exchange_acyclic {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (U R D : Finset V) (hU : (G.induce (U : Set V)).IsAcyclic) (hRU : R ⊆ U)
    (hDU : ∀ d ∈ D, d ∉ U)
    (hDind : ∀ d ∈ D, ∀ d' ∈ D, ¬ G.Adj d d')
    (hD1 : ∀ d ∈ D, ∀ a ∈ R, ∀ b ∈ R, G.Adj d a → G.Adj d b → a = b) :
    (G.induce ((R ∪ D : Finset V) : Set V)).IsAcyclic := by
  rw [isAcyclic_iff_forall_adj_isBridge]
  have hleaf : ∀ u w : ((R ∪ D : Finset V) : Set V), u.1 ∈ D →
      (G.induce ((R ∪ D : Finset V) : Set V)).Adj u w →
      ¬ ((G.induce ((R ∪ D : Finset V) : Set V)).deleteEdges {s(u, w)}).Reachable u w := by
    intro u w hu hadj hreach
    have hGw : G.Adj u.1 w.1 := hadj
    have hwR : w.1 ∈ R := by
      rcases Finset.mem_union.mp (Finset.mem_coe.mp w.2) with h | h
      · exact h
      · exact (hDind u.1 hu w.1 h hGw).elim
    obtain ⟨p⟩ := hreach
    cases p with
    | nil => exact hGw.ne rfl
    | @cons _ z _ h _ =>
      rw [deleteEdges_adj] at h
      have hGz : G.Adj u.1 z.1 := h.1
      have hzR : z.1 ∈ R := by
        rcases Finset.mem_union.mp (Finset.mem_coe.mp z.2) with h' | h'
        · exact h'
        · exact (hDind u.1 hu z.1 h' hGz).elim
      have hzw : z.1 = w.1 := hD1 u.1 hu z.1 hzR w.1 hwR hGz hGw
      apply h.2
      rw [Set.mem_singleton_iff, Subtype.ext hzw]
  intro u w hadj
  rw [isBridge_iff]
  by_cases hu : u.1 ∈ D
  · exact hleaf u w hu hadj
  by_cases hw : w.1 ∈ D
  · intro hreach
    apply hleaf w u hw hadj.symm
    rw [Sym2.eq_swap]
    exact hreach.symm
  have huR : u.1 ∈ R := (Finset.mem_union.mp (Finset.mem_coe.mp u.2)).resolve_right hu
  have hwR : w.1 ∈ R := (Finset.mem_union.mp (Finset.mem_coe.mp w.2)).resolve_right hw
  have huU : u.1 ∈ U := hRU huR
  have hwU : w.1 ∈ U := hRU hwR
  intro hreach
  classical
  let ψ : ((R ∪ D : Finset V) : Set V) → ((U : Set V)) := fun z =>
    if hz : z.1 ∈ U then ⟨z.1, hz⟩ else
      if hex : ∃ a, a ∈ R ∧ G.Adj z.1 a then ⟨hex.choose, hRU hex.choose_spec.1⟩
      else ⟨u.1, huU⟩
  have hψU : ∀ (z : ((R ∪ D : Finset V) : Set V)) (hz : z.1 ∈ U), ψ z = ⟨z.1, hz⟩ :=
    fun z hz => dif_pos hz
  have hbridge := (isAcyclic_iff_forall_adj_isBridge.mp hU)
    (show (G.induce (U : Set V)).Adj ⟨u.1, huU⟩ ⟨w.1, hwU⟩ from hadj)
  rw [isBridge_iff] at hbridge
  apply hbridge
  have key : ∀ y y' : ((R ∪ D : Finset V) : Set V), G.Adj y.1 y'.1 → y.1 ∉ U → y'.1 ∈ U →
      ψ y = ψ y' := by
    intro y y' hyy hy hy'
    have hyD : y.1 ∈ D := (Finset.mem_union.mp (Finset.mem_coe.mp y.2)).resolve_left
      (fun h => hy (hRU h))
    have hy'R : y'.1 ∈ R := (Finset.mem_union.mp (Finset.mem_coe.mp y'.2)).resolve_right
      (fun h => hDU _ h hy')
    have hex : ∃ a, a ∈ R ∧ G.Adj y.1 a := ⟨y'.1, hy'R, hyy⟩
    rw [hψU y' hy']
    have h1 : ψ y = ⟨hex.choose, hRU hex.choose_spec.1⟩ := by
      dsimp only [ψ]
      rw [dif_neg hy, dif_pos hex]
    rw [h1]
    exact Subtype.ext (hD1 y.1 hyD _ hex.choose_spec.1 _ hy'R hex.choose_spec.2 hyy)
  have hmap := p1_reach_map
    (H := (G.induce (U : Set V)).deleteEdges {s(⟨u.1, huU⟩, ⟨w.1, hwU⟩)}) ψ ?_ hreach
  · rwa [hψU u huU, hψU w hwU] at hmap
  intro z z' hzz
  rw [deleteEdges_adj] at hzz
  obtain ⟨hG, hne⟩ := hzz
  have hG' : G.Adj z.1 z'.1 := hG
  by_cases hz : z.1 ∈ U
  · by_cases hz' : z'.1 ∈ U
    · right
      rw [hψU z hz, hψU z' hz', deleteEdges_adj]
      refine ⟨hG', ?_⟩
      intro hmem
      apply hne
      rw [Set.mem_singleton_iff, Sym2.eq_iff] at hmem ⊢
      rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl ⟨Subtype.ext (Subtype.mk.inj h1), Subtype.ext (Subtype.mk.inj h2)⟩
      · exact Or.inr ⟨Subtype.ext (Subtype.mk.inj h1), Subtype.ext (Subtype.mk.inj h2)⟩
    · left
      exact (key z' z hG'.symm hz' hz).symm
  · by_cases hz' : z'.1 ∈ U
    · left
      exact key z z' hG' hz hz'
    · exfalso
      have hzD : z.1 ∈ D := (Finset.mem_union.mp (Finset.mem_coe.mp z.2)).resolve_left
        (fun h => hz (hRU h))
      have hz'D : z'.1 ∈ D := (Finset.mem_union.mp (Finset.mem_coe.mp z'.2)).resolve_left
        (fun h => hz' (hRU h))
      exact hDind _ hzD _ hz'D hG'

/-- The all-but-one Hall condition HP for the neighbourhoods, inside a maximum induced forest
`U`, of the outside vertices of one colour. -/
private lemma p1_hp {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {κ : Type*} [DecidableEq κ] (c : V → κ)
    (hc : ∀ u w, G.Adj u w → c u ≠ c w)
    (U : Finset V) (hU : (G.induce (U : Set V)).IsAcyclic)
    (hmax : ∀ W : Finset V, (G.induce (W : Set V)).IsAcyclic → W.card ≤ U.card) (i : κ)
    (S : Finset V) :
    (Finset.univ.filter (fun t : {t : V // t ∉ U ∧ c t = i} =>
      ((U.filter (fun x => G.Adj t.1 x)) \ S).card ≤ 1)).card ≤ S.card := by
  obtain ⟨D, hD⟩ : ∃ D : Finset V, D = (Finset.univ.filter
      (fun t : {t : V // t ∉ U ∧ c t = i} =>
        ((U.filter (fun x => G.Adj t.1 x)) \ S).card ≤ 1)).image Subtype.val := ⟨_, rfl⟩
  have hDcard : D.card = (Finset.univ.filter (fun t : {t : V // t ∉ U ∧ c t = i} =>
      ((U.filter (fun x => G.Adj t.1 x)) \ S).card ≤ 1)).card := by
    rw [hD]
    exact Finset.card_image_of_injective _ Subtype.val_injective
  have hmem : ∀ d ∈ D, d ∉ U ∧ c d = i ∧ ((U.filter (fun x => G.Adj d x)) \ S).card ≤ 1 := by
    intro d hd
    rw [hD, Finset.mem_image] at hd
    obtain ⟨t, ht, rfl⟩ := hd
    exact ⟨t.2.1, t.2.2, (Finset.mem_filter.mp ht).2⟩
  have hac := p1_exchange_acyclic G U (U \ S) D hU Finset.sdiff_subset
    (fun d hd => (hmem d hd).1)
    (fun d hd d' hd' hadj => hc d d' hadj ((hmem d hd).2.1.trans (hmem d' hd').2.1.symm))
    (fun d hd a ha b hb hda hdb => Finset.card_le_one.mp (hmem d hd).2.2 a
      (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp ha).1, hda⟩,
        (Finset.mem_sdiff.mp ha).2⟩) b
      (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨(Finset.mem_sdiff.mp hb).1, hdb⟩,
        (Finset.mem_sdiff.mp hb).2⟩))
  have h1 := hmax _ hac
  have hdisj : Disjoint (U \ S) D :=
    Finset.disjoint_left.mpr (fun x hx hxD => (hmem x hxD).1 (Finset.mem_sdiff.mp hx).1)
  rw [Finset.card_union_of_disjoint hdisj] at h1
  have h2 : U.card ≤ (U \ S).card + S.card := by
    rw [Finset.card_sdiff_add_card]
    exact Finset.card_le_card Finset.subset_union_left
  rw [← hDcard]
  omega

/-- One colour side: from Theorem BL, a set of edges between the outside vertices of colour `i` and
the maximum induced forest `U` forming a linear forest with degree two at every such outside
vertex and degree at most one at the prescribed forest vertex `v`. -/
private lemma p1_side {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (c : V → Fin 2) (hc : ∀ u w, G.Adj u w → c u ≠ c w)
    (U : Finset V) (hU : (G.induce (U : Set V)).IsAcyclic)
    (hmax : ∀ W : Finset V, (G.induce (W : Set V)).IsAcyclic → W.card ≤ U.card)
    (i : Fin 2)
    (hBLG : ∀ x ∈ U, ∀ t1 t2 t3 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t1 ≠ t2 → t1 ≠ t3 → t2 ≠ t3 →
      G.Adj x t1 → G.Adj x t2 → G.Adj x t3 → ∃ p : V → Prop,
        (∀ s s', s ∉ U → s' ∉ U → p s → ¬ p s' → ∀ z ∈ U, G.Adj s z → G.Adj s' z → z = x) ∧
        ¬ ((p t1 ↔ p t2) ∧ (p t1 ↔ p t3)))
    (v : V) (hvU : v ∈ U) :
    ∃ E : Finset (Sym2 V),
      (∀ p q, s(p, q) ∈ E →
        G.Adj p q ∧ ((p ∉ U ∧ c p = i ∧ q ∈ U) ∨ (q ∉ U ∧ c q = i ∧ p ∈ U))) ∧
      E.card = 2 * (Finset.univ.filter (fun z : V => z ∉ U ∧ c z = i)).card ∧
      (∀ x p q r, s(x, p) ∈ E → s(x, q) ∈ E → s(x, r) ∈ E → p = q ∨ p = r ∨ q = r) ∧
      (∀ p q, s(v, p) ∈ E → s(v, q) ∈ E → p = q) ∧
      (∀ x y, s(x, y) ∈ E →
        ¬ (fromEdgeSet ((E.erase s(x, y) : Finset (Sym2 V)) : Set (Sym2 V))).Reachable x y) := by
  classical
  obtain ⟨e, he1, hinj, hacyc, hdeg, hv⟩ := BL_R3form
    (fun t : {t : V // t ∉ U ∧ c t = i} => U.filter (fun x => G.Adj t.1 x))
    (p1_hp G c hc U hU hmax i) (by
      intro b t1 t2 t3 h12 h13 h23 hb1 hb2 hb3
      have m1 : b ∈ U ∧ G.Adj t1.1 b := Finset.mem_filter.mp hb1
      have m2 : b ∈ U ∧ G.Adj t2.1 b := Finset.mem_filter.mp hb2
      have m3 : b ∈ U ∧ G.Adj t3.1 b := Finset.mem_filter.mp hb3
      obtain ⟨p, hsep, hns⟩ := hBLG b m1.1 t1.1 t2.1 t3.1 t1.2.1 t2.2.1 t3.2.1
        (fun h => h12 (Subtype.ext h)) (fun h => h13 (Subtype.ext h)) (fun h => h23 (Subtype.ext h))
        m1.2.symm m2.2.symm m3.2.symm
      refine ⟨fun s => p s.1, fun s s' hs hs' => ?_, hns⟩
      intro z hz
      have z1 : z ∈ U ∧ G.Adj s.1 z := Finset.mem_filter.mp (Finset.mem_inter.mp hz).1
      have z2 : z ∈ U ∧ G.Adj s'.1 z := Finset.mem_filter.mp (Finset.mem_inter.mp hz).2
      exact Finset.mem_singleton.mpr (hsep s.1 s'.1 s.2.1 s'.2.1 hs hs' z z1.1 z1.2 z2.2)) v
  obtain ⟨Pg, hPg⟩ : ∃ Pg : SimpleGraph V, Pg = SimpleGraph.fromRel
      (fun x y : V => ∃ t : {t : V // t ∉ U ∧ c t = i}, e t = (x, y)) := ⟨_, rfl⟩
  rw [← hPg] at hacyc hdeg hv
  let X : {t : V // t ∉ U ∧ c t = i} → Bool → V := fun t k => cond k (e t).1 (e t).2
  have hXU : ∀ t k, X t k ∈ U := by
    intro t k
    cases k
    · exact (Finset.mem_filter.mp (he1 t).2.1).1
    · exact (Finset.mem_filter.mp (he1 t).1).1
  have hXadj : ∀ t k, G.Adj t.1 (X t k) := by
    intro t k
    cases k
    · exact (Finset.mem_filter.mp (he1 t).2.1).2
    · exact (Finset.mem_filter.mp (he1 t).1).2
  have hXne : ∀ t k, X t k ≠ X t (!k) := by
    intro t k
    cases k
    · exact (he1 t).2.2.symm
    · exact (he1 t).2.2
  have hXP : ∀ t k, Pg.Adj (X t k) (X t (!k)) := by
    intro t k
    rw [hPg, SimpleGraph.fromRel_adj]
    refine ⟨hXne t k, ?_⟩
    cases k
    · exact Or.inr ⟨t, rfl⟩
    · exact Or.inl ⟨t, rfl⟩
  have hXs : ∀ t k, s(X t k, X t (!k)) = s((e t).1, (e t).2) := by
    intro t k
    cases k
    · exact Sym2.eq_swap
    · rfl
  have hfin : ∀ t k t' k', X t k = X t' k' → X t (!k) = X t' (!k') → t = t' := by
    intro t k t' k' h1 h2
    apply hinj
    show s((e t).1, (e t).2) = s((e t').1, (e t').2)
    rw [← hXs t k, ← hXs t' k', h1, h2]
  obtain ⟨E, hEdef⟩ : ∃ E : Finset (Sym2 V), E = (Finset.univ :
      Finset ({t : V // t ∉ U ∧ c t = i} × Bool)).image
        (fun tk => s(tk.1.1, X tk.1 tk.2)) := ⟨_, rfl⟩
  have hE : ∀ p q, s(p, q) ∈ E → ∃ t k, (p = t.1 ∧ q = X t k) ∨ (q = t.1 ∧ p = X t k) := by
    intro p q h
    rw [hEdef] at h
    obtain ⟨⟨t, k⟩, _, htk⟩ := Finset.mem_image.mp h
    rw [Sym2.eq_iff] at htk
    rcases htk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨t, k, Or.inl ⟨h1.symm, h2.symm⟩⟩
    · exact ⟨t, k, Or.inr ⟨h1.symm, h2.symm⟩⟩
  have hEU : ∀ x p, x ∈ U → s(x, p) ∈ E → ∃ t k, p = t.1 ∧ x = X t k := by
    intro x p hx h
    obtain ⟨t, k, h' | h'⟩ := hE x p h
    · exact (t.2.1 (h'.1 ▸ hx)).elim
    · exact ⟨t, k, h'⟩
  have hEN : ∀ x p, x ∉ U → s(x, p) ∈ E → ∃ t k, x = t.1 ∧ p = X t k := by
    intro x p hx h
    obtain ⟨t, k, h' | h'⟩ := hE x p h
    · exact ⟨t, k, h'⟩
    · exact (hx (h'.2 ▸ hXU t k)).elim
  have hbool : ∀ k k' : Bool, k ≠ k' → k' = !k := by decide
  refine ⟨E, ?_, ?_, ?_, ?_, ?_⟩
  · intro p q h
    obtain ⟨t, k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hE p q h
    · exact ⟨hXadj t k, Or.inl ⟨t.2.1, t.2.2, hXU t k⟩⟩
    · exact ⟨(hXadj t k).symm, Or.inr ⟨t.2.1, t.2.2, hXU t k⟩⟩
  · rw [hEdef, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_prod,
      Fintype.card_bool, Fintype.card_subtype, Nat.mul_comm]
    rintro ⟨t, k⟩ ⟨t', k'⟩ h
    simp only at h
    rw [Sym2.eq_iff] at h
    rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have htt : t = t' := Subtype.ext h1
      subst htt
      have hkk : k = k' := by
        by_contra hne
        have hk' : k' = !k := hbool k k' hne
        rw [hk'] at h2
        exact hXne t k h2
      rw [hkk]
    · exact (t.2.1 (h1 ▸ hXU t' k')).elim
  · intro x p q r hp hq hr
    by_cases hx : x ∈ U
    · obtain ⟨tp, kp, hp1, hp2⟩ := hEU x p hx hp
      obtain ⟨tq, kq, hq1, hq2⟩ := hEU x q hx hq
      obtain ⟨tr, kr, hr1, hr2⟩ := hEU x r hx hr
      have hap : Pg.Adj x (X tp (!kp)) := by
        rw [hp2]
        exact hXP tp kp
      have haq : Pg.Adj x (X tq (!kq)) := by
        rw [hq2]
        exact hXP tq kq
      have har : Pg.Adj x (X tr (!kr)) := by
        rw [hr2]
        exact hXP tr kr
      rcases hdeg x _ _ _ hap haq har with h | h | h
      · left
        rw [hp1, hq1, hfin tp kp tq kq (hp2.symm.trans hq2) h]
      · right
        left
        rw [hp1, hr1, hfin tp kp tr kr (hp2.symm.trans hr2) h]
      · right
        right
        rw [hq1, hr1, hfin tq kq tr kr (hq2.symm.trans hr2) h]
    · obtain ⟨tp, kp, hp1, hp2⟩ := hEN x p hx hp
      obtain ⟨tq, kq, hq1, hq2⟩ := hEN x q hx hq
      obtain ⟨tr, kr, hr1, hr2⟩ := hEN x r hx hr
      have e1 : tq = tp := Subtype.ext (hq1.symm.trans hp1)
      have e2 : tr = tp := Subtype.ext (hr1.symm.trans hp1)
      rw [e1] at hq2
      rw [e2] at hr2
      rw [hp2, hq2, hr2]
      cases kp <;> cases kq <;> cases kr <;> simp
  · intro p q hp hq
    obtain ⟨tp, kp, hp1, hp2⟩ := hEU v p hvU hp
    obtain ⟨tq, kq, hq1, hq2⟩ := hEU v q hvU hq
    have hap : Pg.Adj v (X tp (!kp)) := by
      rw [hp2]
      exact hXP tp kp
    have haq : Pg.Adj v (X tq (!kq)) := by
      rw [hq2]
      exact hXP tq kq
    rw [hp1, hq1, hfin tp kp tq kq (hp2.symm.trans hq2) (hv _ _ hap haq)]
  · have hbr0 : ∀ (t0 : {t : V // t ∉ U ∧ c t = i}) (k0 : Bool),
        ¬ (fromEdgeSet ((E.erase s(t0.1, X t0 k0) : Finset (Sym2 V)) :
          Set (Sym2 V))).Reachable t0.1 (X t0 k0) := by
      intro t0 k0 hreach
      have hbP := (isAcyclic_iff_forall_adj_isBridge.mp hacyc) (hXP t0 k0)
      rw [isBridge_iff] at hbP
      apply hbP
      let ψ : V → V := fun z =>
        if h : z ∉ U ∧ c z = i then (if z = t0.1 then X t0 (!k0) else X ⟨z, h⟩ true) else z
      have hψT : ∀ t : {t : V // t ∉ U ∧ c t = i},
          ψ t.1 = if t.1 = t0.1 then X t0 (!k0) else X t true := fun t => dif_pos t.2
      have hψU : ∀ z, z ∈ U → ψ z = z := fun z hz => dif_neg (fun h => h.1 hz)
      have hkey : ∀ t k, (t, k) ≠ (t0, k0) →
          (ψ t.1 = ψ (X t k) ∨
            (Pg.deleteEdges {s(X t0 k0, X t0 (!k0))}).Adj (ψ t.1) (ψ (X t k))) := by
        intro t k hne
        rw [hψT t, hψU _ (hXU t k)]
        by_cases ht : t = t0
        · subst ht
          rw [if_pos rfl]
          left
          have hk : k = !k0 := hbool k0 k (fun h => hne (by rw [h]))
          rw [hk]
        · rw [if_neg (fun h => ht (Subtype.ext h))]
          cases k
          · right
            rw [deleteEdges_adj]
            refine ⟨hXP t true, ?_⟩
            intro hmem
            rw [Set.mem_singleton_iff] at hmem
            apply ht
            apply hinj
            show s((e t).1, (e t).2) = s((e t0).1, (e t0).2)
            rw [← hXs t0 k0]
            exact hmem
          · left
            rfl
      have hmap := p1_reach_map (H := Pg.deleteEdges {s(X t0 k0, X t0 (!k0))}) ψ ?_ hreach
      · rw [hψT t0, if_pos rfl, hψU _ (hXU t0 k0)] at hmap
        exact hmap.symm
      intro p q hpq
      rw [fromEdgeSet_adj] at hpq
      obtain ⟨hmem, _⟩ := hpq
      rw [Finset.mem_coe, Finset.mem_erase] at hmem
      obtain ⟨hne2, hin⟩ := hmem
      obtain ⟨t, k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hE p q hin
      · apply hkey t k
        intro h
        apply hne2
        rw [(Prod.mk.inj h).1, (Prod.mk.inj h).2]
      · have h3 := hkey t k (by
          intro h
          apply hne2
          rw [(Prod.mk.inj h).1, (Prod.mk.inj h).2, Sym2.eq_swap])
        rcases h3 with h3 | h3
        · exact Or.inl h3.symm
        · exact Or.inr h3.symm
    intro x y hxy
    obtain ⟨t, k, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := hE x y hxy
    · exact hbr0 t k
    · intro h
      rw [Sym2.eq_swap] at h
      exact hbr0 t k h.symm

/-- The two one-sided linear forests and one edge of the maximum induced forest `U` form a linear
forest with `2 (n - f) + 1` edges, hence a path cover with `2 f - n - 1` paths, as soon as the
outside neighbourhoods of `U` are in the block class. -/
private lemma k2_bipartite_core {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (hn : 1 < Fintype.card V) (c : V → Fin 2)
    (hc : ∀ u w, G.Adj u w → c u ≠ c w) (U : Finset V) (hU : (G.induce (U : Set V)).IsAcyclic)
    (hUcard : U.card = G.largestInducedForestSize)
    (hBLG : ∀ x ∈ U, ∀ t1 t2 t3 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t1 ≠ t2 → t1 ≠ t3 → t2 ≠ t3 →
      G.Adj x t1 → G.Adj x t2 → G.Adj x t3 → ∃ p : V → Prop,
        (∀ s s', s ∉ U → s' ∉ U → p s → ¬ p s' → ∀ z ∈ U, G.Adj s z → G.Adj s' z → z = x) ∧
        ¬ ((p t1 ↔ p t2) ∧ (p t1 ↔ p t3))) :
    G.pathCoverNumber + Fintype.card V + 1 ≤ 2 * G.largestInducedForestSize := by
  classical
  have hmax : ∀ W : Finset V, (G.induce (W : Set V)).IsAcyclic → W.card ≤ U.card := by
    intro W hW
    rw [hUcard]
    exact ncvr_card_le_largestInducedForestSize G W hW
  obtain ⟨a, haU, b, hbU, hab⟩ : ∃ a ∈ U, ∃ b ∈ U, G.Adj a b := by
    by_contra hno
    push Not at hno
    have := indep_add_one_le_forest G hconn hn U hno
    omega
  have hcab : c a ≠ c b := hc a b hab
  have hfin2 : ∀ x y z : Fin 2, y ≠ z → x = y ∨ x = z := by decide
  have hpig : ∀ z, c z = c a ∨ c z = c b := fun z => hfin2 (c z) (c a) (c b) hcab
  obtain ⟨E0, h0form, h0card, h0deg, h0v, h0br⟩ := p1_side G c hc U hU hmax (c b) hBLG a haU
  obtain ⟨E1, h1form, h1card, h1deg, h1v, h1br⟩ := p1_side G c hc U hU hmax (c a) hBLG b hbU
  obtain ⟨s0, hs0⟩ : ∃ s0 : V → Prop, s0 = fun z => (z ∈ U ↔ c z = c a) := ⟨_, rfl⟩
  have hs0a : s0 a := by
    rw [hs0]
    exact ⟨fun _ => rfl, fun _ => haU⟩
  have hs0b : ¬ s0 b := by
    rw [hs0]
    intro h
    exact hcab (h.mp hbU).symm
  have h0side : ∀ p q, s(p, q) ∈ E0 → s0 p ∧ s0 q := by
    have key : ∀ p q, G.Adj p q → p ∉ U → c p = c b → q ∈ U → s0 p ∧ s0 q := by
      intro p q hadj hp hcp hq
      rw [hs0]
      refine ⟨⟨fun h => (hp h).elim, fun h => (hcab (h.symm.trans hcp)).elim⟩,
        ⟨fun _ => ?_, fun _ => hq⟩⟩
      rcases hpig q with h | h
      · exact h
      · exact (hc p q hadj (hcp.trans h.symm)).elim
    intro p q h
    obtain ⟨hadj, ⟨hp, hcp, hq⟩ | ⟨hq, hcq, hp⟩⟩ := h0form p q h
    · exact key p q hadj hp hcp hq
    · exact (key q p hadj.symm hq hcq hp).symm
  have h1side : ∀ p q, s(p, q) ∈ E1 → ¬ s0 p ∧ ¬ s0 q := by
    have key : ∀ p q, G.Adj p q → p ∉ U → c p = c a → q ∈ U → ¬ s0 p ∧ ¬ s0 q := by
      intro p q hadj hp hcp hq
      rw [hs0]
      refine ⟨fun h => hp (h.mpr hcp), fun h => ?_⟩
      exact hc p q hadj (hcp.trans (h.mp hq).symm)
    intro p q h
    obtain ⟨hadj, ⟨hp, hcp, hq⟩ | ⟨hq, hcq, hp⟩⟩ := h1form p q h
    · exact key p q hadj hp hcp hq
    · exact (key q p hadj.symm hq hcq hp).symm
  obtain ⟨E, hEdef⟩ : ∃ E : Finset (Sym2 V), E = insert s(a, b) (E0 ∪ E1) := ⟨_, rfl⟩
  have hEcases : ∀ p q, s(p, q) ∈ E → s(p, q) = s(a, b) ∨ s(p, q) ∈ E0 ∨ s(p, q) ∈ E1 := by
    intro p q h
    rw [hEdef, Finset.mem_insert, Finset.mem_union] at h
    exact h
  have hab_cases : ∀ p q, s(p, q) = s(a, b) → (p = a ∧ q = b) ∨ (p = b ∧ q = a) := by
    intro p q h
    exact Sym2.eq_iff.mp h
  have hEadj : ∀ p q, s(p, q) ∈ E → G.Adj p q := by
    intro p q h
    rcases hEcases p q h with h | h | h
    · rcases hab_cases p q h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hab
      · exact hab.symm
    · exact (h0form p q h).1
    · exact (h1form p q h).1
  have hnab : s(a, b) ∉ E0 ∪ E1 := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hs0b (h0side a b h).2
    · exact (h1side a b h).1 hs0a
  have hdisj01 : Disjoint E0 E1 := by
    rw [Finset.disjoint_left]
    intro z
    induction z using Sym2.ind with
    | _ p q =>
      intro h0 h1
      exact (h1side p q h1).1 (h0side p q h0).1
  have hEcard : E.card = 1 + E0.card + E1.card := by
    rw [hEdef, Finset.card_insert_of_notMem hnab, Finset.card_union_of_disjoint hdisj01]
    omega
  have hcount : (Finset.univ.filter (fun z : V => z ∉ U ∧ c z = c b)).card +
      (Finset.univ.filter (fun z : V => z ∉ U ∧ c z = c a)).card = Fintype.card V - U.card := by
    rw [← Finset.card_compl, ← Finset.card_union_of_disjoint]
    · congr 1
      ext z
      simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        Finset.mem_compl]
      constructor
      · rintro (h | h)
        · exact h.1
        · exact h.1
      · intro h
        rcases hpig z with h' | h'
        · exact Or.inr ⟨h, h'⟩
        · exact Or.inl ⟨h, h'⟩
    · rw [Finset.disjoint_left]
      intro z h1 h2
      exact hcab ((Finset.mem_filter.mp h2).2.2.symm.trans (Finset.mem_filter.mp h1).2.2)
  have hdegE : ∀ x p q r, s(x, p) ∈ E → s(x, q) ∈ E → s(x, r) ∈ E → p = q ∨ p = r ∨ q = r := by
    have hgen : ∀ (E' : Finset (Sym2 V)) (x : V),
        (∀ p q r, s(x, p) ∈ E' → s(x, q) ∈ E' → s(x, r) ∈ E' → p = q ∨ p = r ∨ q = r) →
        (∀ p, s(x, p) = s(a, b) → ∀ q r, s(x, q) ∈ E' → s(x, r) ∈ E' → q = r) →
        ∀ p q r, (s(x, p) = s(a, b) ∨ s(x, p) ∈ E') → (s(x, q) = s(a, b) ∨ s(x, q) ∈ E') →
          (s(x, r) = s(a, b) ∨ s(x, r) ∈ E') → p = q ∨ p = r ∨ q = r := by
      intro E' x hd hv' p q r hp hq hr
      rcases hp with hp | hp <;> rcases hq with hq | hq <;> rcases hr with hr | hr
      · exact Or.inl (Sym2.congr_right.mp (hp.trans hq.symm))
      · exact Or.inl (Sym2.congr_right.mp (hp.trans hq.symm))
      · exact Or.inr (Or.inl (Sym2.congr_right.mp (hp.trans hr.symm)))
      · exact Or.inr (Or.inr (hv' p hp q r hq hr))
      · exact Or.inr (Or.inr (Sym2.congr_right.mp (hq.trans hr.symm)))
      · exact Or.inr (Or.inl (hv' q hq p r hp hr))
      · exact Or.inl (hv' r hr p q hp hq)
      · exact hd p q r hp hq hr
    intro x p q r hp hq hr
    by_cases hx : s0 x
    · have hconv : ∀ p, s(x, p) ∈ E → s(x, p) = s(a, b) ∨ s(x, p) ∈ E0 := by
        intro p h
        rcases hEcases x p h with h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact ((h1side x p h).1 hx).elim
      refine hgen E0 x (h0deg x) ?_ p q r (hconv p hp) (hconv q hq) (hconv r hr)
      intro p' hp' q' r' hq' hr'
      have hxa : x = a := by
        rcases hab_cases x p' hp' with ⟨h, _⟩ | ⟨h, _⟩
        · exact h
        · exact (hs0b (h ▸ hx)).elim
      rw [hxa] at hq' hr'
      exact h0v q' r' hq' hr'
    · have hconv : ∀ p, s(x, p) ∈ E → s(x, p) = s(a, b) ∨ s(x, p) ∈ E1 := by
        intro p h
        rcases hEcases x p h with h | h | h
        · exact Or.inl h
        · exact (hx (h0side x p h).1).elim
        · exact Or.inr h
      refine hgen E1 x (h1deg x) ?_ p q r (hconv p hp) (hconv q hq) (hconv r hr)
      intro p' hp' q' r' hq' hr'
      have hxb : x = b := by
        rcases hab_cases x p' hp' with ⟨h, _⟩ | ⟨h, _⟩
        · exact (hx (h ▸ hs0a)).elim
        · exact h
      rw [hxb] at hq' hr'
      exact h1v q' r' hq' hr'
  have hbrE : ∀ x y, s(x, y) ∈ E →
      ¬ (fromEdgeSet ((E.erase s(x, y) : Finset (Sym2 V)) : Set (Sym2 V))).Reachable x y := by
    intro x y hxy hreach
    have hedge : ∀ p q, (fromEdgeSet ((E.erase s(x, y) : Finset (Sym2 V)) :
        Set (Sym2 V))).Adj p q →
        s(p, q) ≠ s(x, y) ∧ p ≠ q ∧ (s(p, q) = s(a, b) ∨ s(p, q) ∈ E0 ∨ s(p, q) ∈ E1) := by
      intro p q hpq
      rw [fromEdgeSet_adj, Finset.mem_coe, Finset.mem_erase] at hpq
      exact ⟨hpq.1.1, hpq.2, hEcases p q hpq.1.2⟩
    rcases hEcases x y hxy with h | h | h
    · have hmap := p1_reach_map (H := (⊥ : SimpleGraph Prop)) s0 ?_ hreach
      · rw [reachable_bot] at hmap
        rcases hab_cases x y h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hs0b (hmap ▸ hs0a)
        · exact hs0b (hmap.symm ▸ hs0a)
      intro p q hpq
      left
      obtain ⟨hne, _, h' | h' | h'⟩ := hedge p q hpq
      · exact (hne (h'.trans h.symm)).elim
      · exact propext ⟨fun _ => (h0side p q h').2, fun _ => (h0side p q h').1⟩
      · exact propext ⟨fun hp => ((h1side p q h').1 hp).elim, fun hq => ((h1side p q h').2 hq).elim⟩
    · apply h0br x y h
      have hmap := p1_reach_map
        (H := fromEdgeSet ((E0.erase s(x, y) : Finset (Sym2 V)) : Set (Sym2 V)))
        (fun z => if s0 z then z else a) ?_ hreach
      · simp only [if_pos (h0side x y h).1, if_pos (h0side x y h).2] at hmap
        exact hmap
      intro p q hpq
      obtain ⟨hne, hpq', h' | h' | h'⟩ := hedge p q hpq
      · left
        rcases hab_cases p q h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [if_pos hs0a, if_neg hs0b]
        · simp only [if_pos hs0a, if_neg hs0b]
      · right
        simp only [if_pos (h0side p q h').1, if_pos (h0side p q h').2]
        rw [fromEdgeSet_adj, Finset.mem_coe, Finset.mem_erase]
        exact ⟨⟨hne, h'⟩, hpq'⟩
      · left
        simp only [if_neg (h1side p q h').1, if_neg (h1side p q h').2]
    · apply h1br x y h
      have hmap := p1_reach_map
        (H := fromEdgeSet ((E1.erase s(x, y) : Finset (Sym2 V)) : Set (Sym2 V)))
        (fun z => if s0 z then b else z) ?_ hreach
      · simp only [if_neg (h1side x y h).1, if_neg (h1side x y h).2] at hmap
        exact hmap
      intro p q hpq
      obtain ⟨hne, hpq', h' | h' | h'⟩ := hedge p q hpq
      · left
        rcases hab_cases p q h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · simp only [if_pos hs0a, if_neg hs0b]
        · simp only [if_pos hs0a, if_neg hs0b]
      · left
        simp only [if_pos (h0side p q h').1, if_pos (h0side p q h').2]
      · right
        simp only [if_neg (h1side p q h').1, if_neg (h1side p q h').2]
        rw [fromEdgeSet_adj, Finset.mem_coe, Finset.mem_erase]
        exact ⟨⟨hne, h'⟩, hpq'⟩
  obtain ⟨P, hP, hPcard⟩ := p1_linear_forest_cover E
    (fun x y h => (hEadj x y h).ne) hdegE hbrE
  have hle : fromEdgeSet (E : Set (Sym2 V)) ≤ G := by
    intro p q h
    rw [fromEdgeSet_adj] at h
    exact hEadj p q (Finset.mem_coe.mp h.1)
  have hpc : G.pathCoverNumber ≤ P.card := by
    unfold SimpleGraph.pathCoverNumber
    exact Nat.sInf_le ⟨P, rfl, r2_isPathCover_mono hle hP⟩
  have hUle : U.card ≤ Fintype.card V := Finset.card_le_univ U
  omega


/-- Corollary BLG: `p + n + 1 ≤ 2 f` for every connected bipartite graph on at least two vertices
having a maximum induced forest whose outside neighbourhoods are in the block class. -/
private lemma k2_forest_class {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (hconn : G.Connected) (hn : 1 < Fintype.card V) (hbip : G.IsBipartite)
    (U : Finset V) (hU : (G.induce (U : Set V)).IsAcyclic)
    (hUc : U.card = G.largestInducedForestSize)
    (hBLG : ∀ x ∈ U, ∀ t1 t2 t3 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t1 ≠ t2 → t1 ≠ t3 → t2 ≠ t3 →
        G.Adj x t1 → G.Adj x t2 → G.Adj x t3 → ∃ p : V → Prop,
          (∀ s s', s ∉ U → s' ∉ U → p s → ¬ p s' → ∀ z ∈ U, G.Adj s z → G.Adj s' z → z = x) ∧
          ¬ ((p t1 ↔ p t2) ∧ (p t1 ↔ p t3))) :
    G.pathCoverNumber + Fintype.card V + 1 ≤ 2 * G.largestInducedForestSize := by
  classical
  obtain ⟨col⟩ := hbip
  exact k2_bipartite_core G hconn hn (fun z => col z) (fun u w h => col.valid h) U hU hUc hBLG

end

theorem main : H1 → H2 → OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1.H1 := by
  intro h1 h2 V _ _ G hn hconn h2c hbip hscat
  by_cases hA : ∃ U : Finset V, (G.induce (U : Set V)).IsAcyclic ∧
      U.card = G.largestInducedForestSize ∧
      ∀ x ∈ U, ∀ t1 t2 t3 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t1 ≠ t2 → t1 ≠ t3 → t2 ≠ t3 →
        G.Adj x t1 → G.Adj x t2 → G.Adj x t3 → ∃ p : V → Prop,
          (∀ s s', s ∉ U → s' ∉ U → p s → ¬ p s' → ∀ z ∈ U, G.Adj s z → G.Adj s' z → z = x) ∧
          ¬ ((p t1 ↔ p t2) ∧ (p t1 ↔ p t3))
  · obtain ⟨U, hU, hUc, hBLG⟩ := hA
    exact k2_forest_class G hconn (by omega) hbip U hU hUc hBLG
  have h3 : ∀ U : Finset V, (G.induce (U : Set V)).IsAcyclic →
      U.card = G.largestInducedForestSize →
      ∃ x ∈ U, ∃ t1 t2 t3 : V, t1 ∉ U ∧ t2 ∉ U ∧ t3 ∉ U ∧ t1 ≠ t2 ∧ t1 ≠ t3 ∧ t2 ≠ t3 ∧
        G.Adj x t1 ∧ G.Adj x t2 ∧ G.Adj x t3 ∧ ∀ p : V → Prop,
          (∀ s s', s ∉ U → s' ∉ U → p s → ¬ p s' → ∀ z ∈ U, G.Adj s z → G.Adj s' z → z = x) →
          (p t1 ↔ p t2) ∧ (p t1 ↔ p t3) := by
    intro U hU hUc
    by_contra hno
    apply hA
    refine ⟨U, hU, hUc, ?_⟩
    intro x hx t1 t2 t3 n1 n2 n3 d12 d13 d23 a1 a2 a3
    by_contra hp
    apply hno
    refine ⟨x, hx, t1, t2, t3, n1, n2, n3, d12, d13, d23, a1, a2, a3, ?_⟩
    intro p hsep
    by_contra hsame
    exact hp ⟨p, hsep, hsame⟩
  by_cases hB : ∃ U : Finset V, (G.induce (U : Set V)).IsAcyclic ∧
      U.card = G.largestInducedForestSize ∧
      ∀ x ∈ U, ∀ t1 t2 t3 t4 : V, t1 ∉ U → t2 ∉ U → t3 ∉ U → t4 ∉ U →
        G.Adj x t1 → G.Adj x t2 → G.Adj x t3 → G.Adj x t4 →
        t1 = t2 ∨ t1 = t3 ∨ t1 = t4 ∨ t2 = t3 ∨ t2 = t4 ∨ t3 = t4
  · exact h1 V G hn hconn h2c hbip hscat h3 hB
  · apply h2 V G hn hconn h2c hbip hscat h3
    intro U hU hUc
    by_contra hno
    apply hB
    refine ⟨U, hU, hUc, ?_⟩
    intro x hx t1 t2 t3 t4 n1 n2 n3 n4 a1 a2 a3 a4
    by_contra hne
    simp only [not_or] at hne
    exact hno ⟨x, hx, t1, t2, t3, t4, n1, n2, n3, n4, a1, a2, a3, a4, hne.1, hne.2.1,
      hne.2.2.1, hne.2.2.2.1, hne.2.2.2.2.1, hne.2.2.2.2.2⟩

end OMA.R_WrittenOnTheWallII_GraphConjecture40_conjecture40_R1_H1_R2
