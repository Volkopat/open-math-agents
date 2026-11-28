import FormalConjectures.ErdosProblems.«159»

/-!
# Reduction of R(C4,K_n) << n^(2-c) to the triangle-free case

In a four-cycle-free graph every edge lies in at most one triangle. Choose one vertex
in each triangle and keep only its two incident edges in that triangle. The result is a
triangle-free spanning subgraph. A counting argument over all choices shows some choice
keeps the independence number below 8*n*d with d = log_3 m + 1. Since m <= 2n^2, the
logarithmic loss is absorbed by n^(eps/4). So a power saving for triangle-free,
four-cycle-free graphs with no independent n-set gives the Erdos bound with exponent
saving eps/2. The triangle-packing case of the earlier reduction R1 is not needed.

The triangle-free statement is split by maximum degree: H1 covers graphs whose degrees
are all at most n/2, H2 covers graphs with a vertex of degree above n/2.
-/

namespace OMA.R_Erdos159_erdos_159_R2

open scoped BigOperators Classical
open Finset SimpleGraph

section General
variable {V : Type*} [DecidableEq V]

/-- Delete one representative of each forbidden set that lies in the sample. -/
private lemma avoid_family (S : Finset V) (F : Finset (Finset V))
    (hne : ∀ B ∈ F, B.Nonempty) :
    ∃ U ⊆ S, (∀ B ∈ F, ¬ B ⊆ U) ∧
      S.card ≤ U.card + (F.filter (· ⊆ S)).card := by
  classical
  let Q := F.filter (· ⊆ S)
  let pick : Q → V := fun B => (hne B.1 (Finset.mem_filter.mp B.2).1).choose
  let R := Q.attach.image (fun B => pick B)
  let U := S \ R
  refine ⟨U, Finset.sdiff_subset, ?_, ?_⟩
  · intro B hB hBU
    have hBS : B ⊆ S := hBU.trans Finset.sdiff_subset
    let b : Q := ⟨B, Finset.mem_filter.mpr ⟨hB, hBS⟩⟩
    have hpB : pick b ∈ B := (hne b.1 (Finset.mem_filter.mp b.2).1).choose_spec
    have hpR : pick b ∈ R := Finset.mem_image_of_mem _ (Finset.mem_attach _ _)
    exact (Finset.mem_sdiff.mp (hBU hpB)).2 hpR
  · have hR : R.card ≤ Q.card := Finset.card_image_le.trans_eq Finset.card_attach
    exact Finset.card_le_card_sdiff_add_card.trans (Nat.add_le_add_left hR _)


private lemma indep_budget_after_neighborhood (G : SimpleGraph V) {r : ℕ} {S : Finset V}
    {x : V} (hx : x ∈ S)
    (hind : ∀ I ⊆ S, G.IsIndepSet (I : Set V) → I.card ≤ r + 1)
    (I : Finset V) (hIR : I ⊆ S \ insert x (S.filter (G.Adj x)))
    (hI : G.IsIndepSet (I : Set V)) : I.card ≤ r := by
  classical
  have hRsub : S \ insert x (S.filter (G.Adj x)) ⊆ S := Finset.sdiff_subset
  have hxN : x ∈ insert x (S.filter (G.Adj x)) := Finset.mem_insert_self _ _
  have hxI : x ∉ I := fun h => (Finset.mem_sdiff.mp (hIR h)).2 hxN
  have hi : G.IsIndepSet (↑(insert x I) : Set V) := by
    rw [Finset.coe_insert, isIndepSet_iff, Set.pairwise_insert_of_notMem hxI]
    refine ⟨hI, ?_⟩
    intro y hy
    have hyR := Finset.mem_sdiff.mp (hIR hy)
    have hxy : ¬ G.Adj x y := fun h =>
      hyR.2 (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hyR.1, h⟩))
    exact ⟨hxy, fun hyx => hxy hyx.symm⟩
  have hiBound := hind (insert x I) (Finset.insert_subset hx (hIR.trans hRsub)) hi
  rw [Finset.card_insert_of_notMem hxI] at hiBound
  omega

/-- A low-degree vertex and its neighbours cost at most `d` vertices and one
unit of the independence budget. -/
private lemma minimum_degree_core (G : SimpleGraph V) (d r : ℕ) (S : Finset V)
    (hind : ∀ I ⊆ S, G.IsIndepSet (I : Set V) → I.card ≤ r) :
    ∃ U ⊆ S, S.card ≤ U.card + r * d ∧
      ∀ x ∈ U, d ≤ (U.filter (G.Adj x)).card := by
  classical
  induction r generalizing S with
  | zero =>
    have hempty : S = ∅ := by
      apply Finset.not_nonempty_iff_eq_empty.mp
      intro hs
      obtain ⟨x, hx⟩ := hs
      have hc := hind {x} (Finset.singleton_subset_iff.mpr hx) (by simp)
      simp at hc
    subst S
    exact ⟨∅, by simp, by simp, by simp⟩
  | succ r ih =>
    by_cases hmin : ∀ x ∈ S, d ≤ (S.filter (G.Adj x)).card
    · exact ⟨S, le_rfl, Nat.le_add_right _ _, hmin⟩
    push Not at hmin
    obtain ⟨x, hx, hdeg⟩ := hmin
    let N := insert x (S.filter (G.Adj x))
    let R := S \ N
    have hRsub : R ⊆ S := Finset.sdiff_subset
    have hR : ∀ I ⊆ R, G.IsIndepSet (I : Set V) → I.card ≤ r :=
      indep_budget_after_neighborhood G hx hind
    obtain ⟨U, hUR, hcard, hU⟩ := ih R hR
    have hN : N.card ≤ d := (Finset.card_insert_le _ _).trans (by omega)
    have hS : S.card ≤ R.card + N.card := Finset.card_le_card_sdiff_add_card
    refine ⟨U, hUR.trans hRsub, ?_, hU⟩
    rw [Nat.succ_mul]
    omega

/-- The two common neighbors of a pair must coincide in a four-cycle-free graph. -/
lemma common_neighbor_unique (G : SimpleGraph V) (hG : ¬ (cycleGraph 4).IsContained G)
    {x y a b : V} (hxy : x ≠ y) (hxa : G.Adj x a) (hya : G.Adj y a)
    (hxb : G.Adj x b) (hyb : G.Adj y b) : a = b := by
  by_contra hab
  let f : Fin 4 → V := ![x, a, y, b]
  have hf : Function.Injective f := by
    have h₁ := hxa.ne
    have h₂ := hya.ne
    have h₃ := hxb.ne
    have h₄ := hyb.ne
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp [f] at hij ⊢ <;> grind
  apply hG
  refine ⟨⟨⟨f, ?_⟩, hf⟩⟩
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first
    | exact hxa
    | exact hya
    | exact hxb
    | exact hyb
    | exact hxa.symm
    | exact hya.symm
    | exact hxb.symm
    | exact hyb.symm
    | exact (show ¬ (cycleGraph 4).Adj _ _ by decide) hij |>.elim

private lemma triangle_third_vertex (G : SimpleGraph V)
    {T : Finset V} (hT : G.IsNClique 3 T) {a b : V}
    (ha : a ∈ T) (hb : b ∈ T) (hab : a ≠ b) :
    ∃ c ∈ T, c ≠ a ∧ c ≠ b := by
  have hdel : ((T.erase a).erase b).card = 1 := by
    rw [Finset.card_erase_of_mem (mem_erase.mpr ⟨hab.symm, hb⟩),
      Finset.card_erase_of_mem ha, hT.card_eq]
  obtain ⟨c, hc⟩ := card_pos.mp (show 0 < ((T.erase a).erase b).card by omega)
  simp only [mem_erase] at hc
  exact ⟨c, hc.2.2, hc.2.1, hc.1⟩

/-- An outside vertex has at most one neighbor in any triangle. -/
lemma triangle_neighbor_unique (G : SimpleGraph V) (hG : ¬ (cycleGraph 4).IsContained G)
    {T : Finset V} (hT : G.IsNClique 3 T) {x a b : V} (hx : x ∉ T)
    (ha : a ∈ T) (hb : b ∈ T) (hxa : G.Adj x a) (hxb : G.Adj x b) : a = b := by
  by_contra hab
  obtain ⟨c, hc, hca, hcb⟩ := triangle_third_vertex G hT ha hb hab
  have hxc : x ≠ c := by
    rintro rfl
    exact hx hc
  exact hab (common_neighbor_unique G hG hxc
    hxa (hT.isClique hc ha hca) hxb (hT.isClique hc hb hcb))

/-- Two disjoint triangles have at most one edge between them. -/
lemma triangle_cross_edge_unique (G : SimpleGraph V) (hG : ¬ (cycleGraph 4).IsContained G)
    {T U : Finset V} (hT : G.IsNClique 3 T) (hU : G.IsNClique 3 U)
    (hTU : Disjoint T U) {a c b d : V}
    (ha : a ∈ T) (hc : c ∈ T) (hb : b ∈ U) (hd : d ∈ U)
    (hab : G.Adj a b) (hcd : G.Adj c d) : a = c ∧ b = d := by
  have hdT : d ∉ T := fun h => disjoint_left.mp hTU h hd
  have haU : a ∉ U := disjoint_left.mp hTU ha
  have hcU : c ∉ U := disjoint_left.mp hTU hc
  by_cases hac : a = c
  · subst c
    exact ⟨rfl, triangle_neighbor_unique G hG hU haU hb hd hab hcd⟩
  have hbd : b ≠ d := fun h => hac
    (triangle_neighbor_unique G hG hT hdT ha hc (h ▸ hab.symm) hcd.symm)
  have hcb := hU.isClique hd hb hbd.symm
  have hca := hT.isClique ha hc hac
  have had : a ≠ d := by
    rintro rfl
    exact haU hd
  have heq := common_neighbor_unique G hG had hca hcd.symm hab hcb
  exact (hcU (heq.symm ▸ hb)).elim

/-- In a four-cycle-free graph, an edge belongs to at most one triangle. -/
lemma triangle_eq_of_shared_edge (G : SimpleGraph V)
    (hG : ¬ (cycleGraph 4).IsContained G) {T U : Finset V}
    (hT : G.IsNClique 3 T) (hU : G.IsNClique 3 U) {x y : V} (hxy : x ≠ y)
    (hxT : x ∈ T) (hyT : y ∈ T) (hxU : x ∈ U) (hyU : y ∈ U) :
    T = U := by
  obtain ⟨a, ha, hax, hay⟩ := triangle_third_vertex G hT hxT hyT hxy
  obtain ⟨b, hb, hbx, hby⟩ := triangle_third_vertex G hU hxU hyU hxy
  have hab := common_neighbor_unique G hG hxy
    (hT.isClique hxT ha hax.symm) (hT.isClique hyT ha hay.symm)
    (hU.isClique hxU hb hbx.symm) (hU.isClique hyU hb hby.symm)
  subst b
  let C : Finset V := {x, y, a}
  have hC : C.card = 3 := by simp [C, hxy, hax.symm, hay.symm]
  have hCT : C ⊆ T := insert_subset hxT (insert_subset hyT (singleton_subset_iff.mpr ha))
  have hCU : C ⊆ U := insert_subset hxU (insert_subset hyU (singleton_subset_iff.mpr hb))
  have heqT := eq_of_subset_of_card_le hCT (hT.card_eq.trans hC.symm).le
  have heqU := eq_of_subset_of_card_le hCU (hU.card_eq.trans hC.symm).le
  exact heqT.symm.trans heqU


end General

private lemma indep_card_le {m n : ℕ} {G : SimpleGraph (Fin m)}
    (hbad : (¬ (cycleGraph 4).IsContained G ∧ ¬ (completeGraph (Fin n)).IsContained Gᶜ)) (I : Finset (Fin m)) (hI : G.IsIndepSet (I : Set (Fin m))) :
    I.card ≤ n - 1 := by
  classical
  have hlt : I.card < n := by
    by_contra! hge
    obtain ⟨J, hJI, hJ⟩ := Finset.exists_subset_card_eq hge
    apply hbad.2
    apply ((Gᶜ).not_cliqueFree_iff_top_isContained n).mp
    intro hfree
    have hclique : Gᶜ.IsClique (I : Set (Fin m)) := by
      simpa only [isClique_compl] using hI
    exact hfree J ⟨hclique.subset hJI, hJ⟩
  omega

/-- The triangles at a vertex use disjoint pairs of its neighbors. Removing one
vertex from each pair leaves an independent set inside the neighborhood. -/
lemma neighborhood_triangle_bounds {n m : ℕ} {G : SimpleGraph (Fin m)}
    (hbad : (¬ (cycleGraph 4).IsContained G ∧ ¬ (completeGraph (Fin n)).IsContained Gᶜ)) (S : Finset (Fin m)) {x : Fin m} (hxS : x ∈ S) :
    2 * ((S.powersetCard 3).filter (fun B => G.IsNClique 3 B ∧ x ∈ B)).card ≤ (S.filter (G.Adj x)).card ∧
      (S.filter (G.Adj x)).card ≤ (n - 1) + ((S.powersetCard 3).filter (fun B => G.IsNClique 3 B ∧ x ∈ B)).card := by
  classical
  let N := S.filter (G.Adj x)
  let F := (S.powersetCard 3).filter fun T => G.IsNClique 3 T ∧ x ∈ T
  let edges := F.image fun T => T.erase x
  have hF (T : Finset (Fin m)) (hT : T ∈ F) :
      T ⊆ S ∧ G.IsNClique 3 T ∧ x ∈ T := by
    obtain ⟨hsub, hclique, hx⟩ := mem_filter.mp hT
    exact ⟨(mem_powersetCard.mp hsub).1, hclique, hx⟩
  have hN (T : Finset (Fin m)) (hT : T ∈ F) : T.erase x ⊆ N := by
    intro y hy
    obtain ⟨hyx, hyT⟩ := mem_erase.mp hy
    obtain ⟨hTS, htri, hxT⟩ := hF T hT
    exact mem_filter.mpr ⟨hTS hyT, htri.isClique hxT hyT hyx.symm⟩
  have hpair_card (T : Finset (Fin m)) (hT : T ∈ F) : (T.erase x).card = 2 := by
    rw [card_erase_of_mem (hF T hT).2.2, (hF T hT).2.1.card_eq]
  have hdisj : (↑F : Set (Finset (Fin m))).PairwiseDisjoint (fun T => T.erase x) := by
    intro T hT U hU hne
    apply Finset.disjoint_left.mpr
    intro y hyT hyU
    obtain ⟨hyx, hyT⟩ := mem_erase.mp hyT
    have hT' := hF T hT
    have hU' := hF U hU
    exact hne (triangle_eq_of_shared_edge G hbad.1 hT'.2.1 hU'.2.1 hyx.symm
      hT'.2.2 hyT hU'.2.2 (mem_of_mem_erase hyU))
  have hbi : (F.biUnion fun T => T.erase x).card = 2 * F.card := by
    rw [card_biUnion hdisj]
    calc
      _ = ∑ _ ∈ F, 2 := sum_congr rfl hpair_card
      _ = _ := by simp [Nat.mul_comm]
  have hsub : F.biUnion (fun T => T.erase x) ⊆ N := by
    intro y hy
    obtain ⟨T, hT, hyT⟩ := mem_biUnion.mp hy
    exact hN T hT hyT
  constructor
  · change 2 * F.card ≤ N.card
    exact hbi ▸ card_le_card hsub
  have hne (E : Finset (Fin m)) (hE : E ∈ edges) : E.Nonempty := by
    obtain ⟨T, hT, rfl⟩ := mem_image.mp hE
    exact card_pos.mp (by rw [hpair_card T hT]; decide)
  obtain ⟨I, hIN, havoid, hsize⟩ := avoid_family N edges hne
  have hI : G.IsIndepSet (I : Set (Fin m)) := by
    intro y hy z hz hyz hyz_adj
    have hyI : y ∈ I := hy
    have hzI : z ∈ I := hz
    obtain ⟨hyS, hxy⟩ := mem_filter.mp (hIN hyI)
    obtain ⟨hzS, hxz⟩ := mem_filter.mp (hIN hzI)
    let T : Finset (Fin m) := {x, y, z}
    have hT : G.IsNClique 3 T := is3Clique_triple_iff.mpr ⟨hxy, hxz, hyz_adj⟩
    have hTF : T ∈ F := mem_filter.mpr ⟨mem_powersetCard.mpr
      ⟨insert_subset hxS (insert_subset hyS (singleton_subset_iff.mpr hzS)), hT.card_eq⟩,
      hT, mem_insert_self _ _⟩
    have hpair : T.erase x ⊆ I := by
      intro w hw
      have hw' := mem_erase.mp hw
      rcases mem_insert.mp hw'.2 with h | h
      · exact (hw'.1 h).elim
      rcases mem_insert.mp h with rfl | h
      · exact hyI
      simpa only [mem_singleton.mp h] using hzI
    exact havoid _ (mem_image_of_mem _ hTF) hpair
  have hcount : (edges.filter (· ⊆ N)).card ≤ F.card :=
    (card_filter_le _ _).trans card_image_le
  exact hsize.trans (Nat.add_le_add (indep_card_le hbad I hI) hcount)




private lemma triangleDeletion_le {G : SimpleGraph (Fin m)} (f : (∀ T : ↥(G.cliqueFinset 3), ↥(T : Finset (Fin m)))) :
    ({ Adj := fun x y => G.Adj x y ∧ ∀ T : ↥(G.cliqueFinset 3), x ∈ T.val → y ∈ T.val → (f T).val = x ∨ (f T).val = y, symm := ⟨fun _ _ h => ⟨h.1.symm, fun T hy hx => (h.2 T hx hy).symm⟩⟩, loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩ } : SimpleGraph (Fin m)) ≤ G := fun _ _ h => h.1

private lemma triangleDeletion_free {G : SimpleGraph (Fin m)} (f : (∀ T : ↥(G.cliqueFinset 3), ↥(T : Finset (Fin m)))) :
    (({ Adj := fun x y => G.Adj x y ∧ ∀ T : ↥(G.cliqueFinset 3), x ∈ T.val → y ∈ T.val → (f T).val = x ∨ (f T).val = y, symm := ⟨fun _ _ h => ⟨h.1.symm, fun T hy hx => (h.2 T hx hy).symm⟩⟩, loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩ } : SimpleGraph (Fin m))).CliqueFree 3 := by
  intro T hT
  have hTG : G.IsNClique 3 T :=
    ⟨hT.isClique.mono (triangleDeletion_le f), hT.card_eq⟩
  let Q : ↥(G.cliqueFinset 3) := ⟨T, mem_cliqueFinset_iff.mpr hTG⟩
  have hcard : (T.erase (f Q).val).card = 2 := by
    rw [card_erase_of_mem (f Q).property, hT.card_eq]
  obtain ⟨a, ha, b, hb, hab⟩ := one_lt_card.mp (show 1 < (T.erase (f Q).val).card by omega)
  obtain ⟨ha', ha⟩ := mem_erase.mp ha
  obtain ⟨hb', hb⟩ := mem_erase.mp hb
  rcases (hT.isClique ha hb hab).2 Q ha hb with h | h
  · exact ha' h.symm
  · exact hb' h.symm

private lemma choice_outside_of_independent {G : SimpleGraph (Fin m)}
    (hG : ¬ (cycleGraph 4).IsContained G) {f : (∀ T : ↥(G.cliqueFinset 3), ↥(T : Finset (Fin m)))} {W : Finset (Fin m)}
    (hW : (({ Adj := fun x y => G.Adj x y ∧ ∀ T : ↥(G.cliqueFinset 3), x ∈ T.val → y ∈ T.val → (f T).val = x ∨ (f T).val = y, symm := ⟨fun _ _ h => ⟨h.1.symm, fun T hy hx => (h.2 T hx hy).symm⟩⟩, loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩ } : SimpleGraph (Fin m))).IsIndepSet (W : Set (Fin m)))
    (T : ↥(G.cliqueFinset 3)) (hlarge : 2 ≤ (T.val ∩ W).card) :
    (f T).val ∉ W := by
  intro hmem
  have hcent : (f T).val ∈ T.val ∩ W := mem_inter.mpr ⟨(f T).property, hmem⟩
  have hne : ((T.val ∩ W).erase (f T).val).Nonempty := by
    apply card_pos.mp
    rw [card_erase_of_mem hcent]
    omega
  obtain ⟨y, hy⟩ := hne
  obtain ⟨hyne, hy⟩ := mem_erase.mp hy
  obtain ⟨hyT, hyW⟩ := mem_inter.mp hy
  have hxy : (f T).val ≠ y := hyne.symm
  have htri := mem_cliqueFinset_iff.mp T.property
  apply hW hmem hyW hxy
  refine ⟨htri.isClique (f T).property hyT hxy, ?_⟩
  intro U hxU hyU
  have hTU : T = U := Subtype.ext (triangle_eq_of_shared_edge G hG htri
    (mem_cliqueFinset_iff.mp U.property) hxy (f T).property hyT hxU hyU)
  subst U
  exact Or.inl rfl

private lemma intersect_card_le_two {G : SimpleGraph (Fin m)} {W : Finset (Fin m)}
    {T : ↥(G.cliqueFinset 3)} {a : ↥(T : Finset (Fin m))} (ha : a.val ∉ W) :
    (T.val ∩ W).card ≤ 2 := by
  have hs : T.val ∩ W ⊆ T.val.erase a.val := by
    intro x hx
    obtain ⟨hxT, hxW⟩ := mem_inter.mp hx
    exact mem_erase.mpr ⟨fun he => ha (he ▸ hxW), hxT⟩
  have h := card_le_card hs
  rwa [card_erase_of_mem a.property, (mem_cliqueFinset_iff.mp T.property).card_eq] at h


/-- A large independent set after deletion forces choices in many triangle coordinates. -/
private lemma constrainedTriangles_card {n m d : ℕ} {G : SimpleGraph (Fin m)}
    (hbad : (¬ (cycleGraph 4).IsContained G ∧ ¬ (completeGraph (Fin n)).IsContained Gᶜ)) {f : (∀ T : ↥(G.cliqueFinset 3), ↥(T : Finset (Fin m)))} {W : Finset (Fin m)}
    (hW : (({ Adj := fun x y => G.Adj x y ∧ ∀ T : ↥(G.cliqueFinset 3), x ∈ T.val → y ∈ T.val → (f T).val = x ∨ (f T).val = y, symm := ⟨fun _ _ h => ⟨h.1.symm, fun T hy hx => (h.2 T hx hy).symm⟩⟩, loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩ } : SimpleGraph (Fin m))).IsIndepSet (W : Set (Fin m)))
    (hlarge : 8 * n * d ≤ W.card) :
    W.card * d ≤ ((univ.filter fun T : ↥(G.cliqueFinset 3) => 2 ≤ (T.val ∩ W).card)).card := by
  classical
  obtain ⟨U, hUW, hcard, hdeg⟩ := minimum_degree_core G (4 * d) (n - 1) W
    (fun I _ => indep_card_le hbad I)
  have hbudget : 2 * ((n - 1) * (4 * d)) ≤ 8 * n * d := by
    calc
      _ = 8 * (n - 1) * d := by ring
      _ ≤ _ := by gcongr; omega
  have hhalf : W.card ≤ 2 * U.card := by omega
  let R := (univ.filter fun T : ↥(G.cliqueFinset 3) => 2 ≤ (T.val ∩ W).card)
  let row (x : Fin m) := (U.filter (G.Adj x)).image (fun y => (x, y))
  let arcs := U.biUnion row
  have hrows : (↑U : Set (Fin m)).PairwiseDisjoint row := by
    intro x _ y _ hxy
    apply Finset.disjoint_left.mpr
    intro p hx hy
    obtain ⟨a, _, ha⟩ := mem_image.mp hx
    obtain ⟨b, _, hb⟩ := mem_image.mp hy
    exact hxy (congrArg Prod.fst (ha.trans hb.symm))
  have harcs_lower : U.card * (4 * d) ≤ arcs.card := by
    rw [show arcs.card = ∑ x ∈ U, (row x).card from card_biUnion hrows]
    calc
      U.card * (4 * d) = ∑ _ ∈ U, 4 * d := by simp
      _ ≤ _ := by
        apply sum_le_sum
        intro x hx
        rw [show (row x).card = (U.filter (G.Adj x)).card from
          card_image_of_injective _ (fun _ _ h => congrArg Prod.snd h)]
        exact hdeg x hx

  let pairs (T : ↥(G.cliqueFinset 3)) := (T.val ∩ W).offDiag
  have harcs_sub : arcs ⊆ R.biUnion pairs := by
    intro p hp
    obtain ⟨x, hx, hp⟩ := mem_biUnion.mp hp
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hp
    obtain ⟨hy, hxy⟩ := mem_filter.mp hy
    have hxW := hUW hx
    have hyW := hUW hy
    have hnot := hW hxW hyW hxy.ne
    have hfail : ¬ ∀ T : ↥(G.cliqueFinset 3), x ∈ T.val → y ∈ T.val →
        (f T).val = x ∨ (f T).val = y := fun h => hnot ⟨hxy, h⟩
    push Not at hfail
    obtain ⟨T, hxT, hyT, _, _⟩ := hfail
    have hxl := mem_inter.mpr ⟨hxT, hxW⟩
    have hyl := mem_inter.mpr ⟨hyT, hyW⟩
    have hR : T ∈ R := mem_filter.mpr ⟨mem_univ _, one_lt_card.mpr ⟨x, hxl, y, hyl, hxy.ne⟩⟩
    exact mem_biUnion.mpr ⟨T, hR, mem_offDiag.mpr ⟨hxl, hyl, hxy.ne⟩⟩
  have hpair_card (T : ↥(G.cliqueFinset 3)) (hT : T ∈ R) : (pairs T).card ≤ 2 := by
    have hT' := (mem_filter.mp hT).2
    have hout := choice_outside_of_independent hbad.1 hW T hT'
    have hcap := intersect_card_le_two hout
    have heq : (T.val ∩ W).card = 2 := by omega
    simp [pairs, offDiag_card, heq]
  have harcs_upper : arcs.card ≤ R.card * 2 := by
    calc
      _ ≤ (R.biUnion pairs).card := card_le_card harcs_sub
      _ ≤ ∑ T ∈ R, (pairs T).card := card_biUnion_le
      _ ≤ ∑ _ ∈ R, 2 := sum_le_sum hpair_card
      _ = _ := by simp
  have hmul := Nat.mul_le_mul_right d hhalf
  have haux : 2 * (W.card * d) ≤ R.card * 2 := by
    calc
      _ ≤ 2 * ((2 * U.card) * d) := Nat.mul_le_mul_left 2 hmul
      _ = U.card * (4 * d) := by ring
      _ ≤ _ := harcs_lower.trans harcs_upper
  change W.card * d ≤ R.card
  omega

private lemma outside_choice_unique {G : SimpleGraph (Fin m)} {W : Finset (Fin m)}
    {T : ↥(G.cliqueFinset 3)} {a b : ↥(T : Finset (Fin m))}
    (hlarge : 2 ≤ (T.val ∩ W).card) (ha : a.val ∉ W) (hb : b.val ∉ W) : a = b := by
  apply Subtype.ext
  by_contra hne
  have hb' : b.val ∈ T.val.erase a.val := mem_erase.mpr ⟨fun h => hne h.symm, b.property⟩
  have hsub : T.val ∩ W ⊆ (T.val.erase a.val).erase b.val := by
    intro x hx
    obtain ⟨hxT, hxW⟩ := mem_inter.mp hx
    exact mem_erase.mpr ⟨fun h => hb (h ▸ hxW),
      mem_erase.mpr ⟨fun h => ha (h ▸ hxW), hxT⟩⟩
  have hc := card_le_card hsub
  rw [card_erase_of_mem hb', card_erase_of_mem a.property,
    (mem_cliqueFinset_iff.mp T.property).card_eq] at hc
  omega

private lemma triangle_choice_space_card {G : SimpleGraph (Fin m)} :
    Fintype.card ((∀ T : ↥(G.cliqueFinset 3), ↥(T : Finset (Fin m)))) = 3 ^ Fintype.card (↥(G.cliqueFinset 3)) := by
  classical
  rw [Fintype.card_pi]
  have h (T : ↥(G.cliqueFinset 3)) : Fintype.card ↥(T : Finset (Fin m)) = 3 := by
    simpa using (mem_cliqueFinset_iff.mp T.property).card_eq
  simp only [h, Finset.prod_const, Finset.card_univ]


private lemma badTriangleChoices_card {n m d : ℕ} {G : SimpleGraph (Fin m)}
    (hbad : (¬ (cycleGraph 4).IsContained G ∧ ¬ (completeGraph (Fin n)).IsContained Gᶜ)) (W : Finset (Fin m)) (hlarge : 8 * n * d ≤ W.card) :
    ((univ.filter (fun f : (∀ T : ↥(G.cliqueFinset 3), ↥(T : Finset (Fin m))) => (({ Adj := fun x y => G.Adj x y ∧ ∀ T : ↥(G.cliqueFinset 3), x ∈ T.val → y ∈ T.val → (f T).val = x ∨ (f T).val = y, symm := ⟨fun _ _ h => ⟨h.1.symm, fun T hy hx => (h.2 T hx hy).symm⟩⟩, loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩ } : SimpleGraph (Fin m))).IsIndepSet (W : Set (Fin m))))).card * 3 ^ (W.card * d) ≤ 3 ^ Fintype.card (↥(G.cliqueFinset 3)) := by
  classical
  by_cases hnon : ((univ.filter (fun f : (∀ T : ↥(G.cliqueFinset 3), ↥(T : Finset (Fin m))) => (({ Adj := fun x y => G.Adj x y ∧ ∀ T : ↥(G.cliqueFinset 3), x ∈ T.val → y ∈ T.val → (f T).val = x ∨ (f T).val = y, symm := ⟨fun _ _ h => ⟨h.1.symm, fun T hy hx => (h.2 T hx hy).symm⟩⟩, loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩ } : SimpleGraph (Fin m))).IsIndepSet (W : Set (Fin m))))).Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty.mp hnon, card_empty, zero_mul]
    exact Nat.zero_le _
  obtain ⟨g, hg⟩ := hnon
  have hgW := (mem_filter.mp hg).2
  let R := (univ.filter fun T : ↥(G.cliqueFinset 3) => 2 ≤ (T.val ∩ W).card)
  let allowed (T : ↥(G.cliqueFinset 3)) : Finset ↥(T : Finset (Fin m)) :=
    if T ∈ R then {g T} else univ
  have hsub : (univ.filter (fun f : (∀ T : ↥(G.cliqueFinset 3), ↥(T : Finset (Fin m))) => (({ Adj := fun x y => G.Adj x y ∧ ∀ T : ↥(G.cliqueFinset 3), x ∈ T.val → y ∈ T.val → (f T).val = x ∨ (f T).val = y, symm := ⟨fun _ _ h => ⟨h.1.symm, fun T hy hx => (h.2 T hx hy).symm⟩⟩, loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩ } : SimpleGraph (Fin m))).IsIndepSet (W : Set (Fin m)))) ⊆ Fintype.piFinset allowed := by
    intro f hf
    have hfW := (mem_filter.mp hf).2
    apply Fintype.mem_piFinset.mpr
    intro T
    by_cases hT : T ∈ R
    · have hT' := (mem_filter.mp hT).2
      have eq := outside_choice_unique hT'
        (choice_outside_of_independent hbad.1 hfW T hT')
        (choice_outside_of_independent hbad.1 hgW T hT')
      simp [allowed, hT, eq]
    · simp [allowed, hT]
  have hallowed : (Fintype.piFinset allowed).card = 3 ^ (Fintype.card (↥(G.cliqueFinset 3)) - R.card) := by
    have h (T : ↥(G.cliqueFinset 3)) : Fintype.card ↥(T : Finset (Fin m)) = 3 := by
      simpa using (mem_cliqueFinset_iff.mp T.property).card_eq
    rw [Fintype.card_piFinset]
    simp only [allowed, apply_ite card, card_singleton, card_univ, h]
    rw [Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const]
    congr 1
    rw [← Finset.card_univ]
    simpa [Finset.sdiff_eq_filter] using
      (Finset.card_sdiff_of_subset (Finset.subset_univ R))
  have hR : W.card * d ≤ R.card := constrainedTriangles_card hbad hgW hlarge
  have hR' : R.card ≤ Fintype.card (↥(G.cliqueFinset 3)) := card_le_univ _
  calc
    _ ≤ 3 ^ (Fintype.card (↥(G.cliqueFinset 3)) - R.card) * 3 ^ R.card := by
      exact Nat.mul_le_mul ((card_le_card hsub).trans_eq hallowed)
        (Nat.pow_le_pow_right (by decide) hR)
    _ = _ := by rw [← pow_add, Nat.sub_add_cancel hR']

/-- Deleting one edge from every triangle can preserve the independence bound
up to a logarithmic factor in the number of vertices. -/
lemma exists_triangle_free_spanning_subgraph {n m : ℕ} {G : SimpleGraph (Fin m)}
    (hbad : (¬ (cycleGraph 4).IsContained G ∧ ¬ (completeGraph (Fin n)).IsContained Gᶜ)) {d : ℕ} (hd : 0 < d) (hm : m < 3 ^ d) (hn : 0 < n) :
    ∃ H : SimpleGraph (Fin m), H ≤ G ∧ H.CliqueFree 3 ∧ (¬ (cycleGraph 4).IsContained H ∧ ¬ (completeGraph (Fin (8 * n * d))).IsContained Hᶜ) := by
  classical
  let k := 8 * n * d
  let P := (univ : Finset (Fin m)).powersetCard k
  have hk : 0 < k := by dsimp [k]; positivity
  have hlt : P.card < 3 ^ (k * d) := by
    dsimp only [P]
    rw [card_powersetCard, card_univ, Fintype.card_fin, mul_comm k d, pow_mul]
    exact (Nat.choose_le_pow m k).trans_lt (Nat.pow_lt_pow_left hm (by omega))
  suffices hgood : ∃ f : (∀ T : ↥(G.cliqueFinset 3), ↥(T : Finset (Fin m))), ∀ W ∈ P,
      ¬ (({ Adj := fun x y => G.Adj x y ∧ ∀ T : ↥(G.cliqueFinset 3), x ∈ T.val → y ∈ T.val → (f T).val = x ∨ (f T).val = y, symm := ⟨fun _ _ h => ⟨h.1.symm, fun T hy hx => (h.2 T hx hy).symm⟩⟩, loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩ } : SimpleGraph (Fin m))).IsIndepSet (W : Set (Fin m)) by
    obtain ⟨f, hf⟩ := hgood
    refine ⟨({ Adj := fun x y => G.Adj x y ∧ ∀ T : ↥(G.cliqueFinset 3), x ∈ T.val → y ∈ T.val → (f T).val = x ∨ (f T).val = y, symm := ⟨fun _ _ h => ⟨h.1.symm, fun T hy hx => (h.2 T hx hy).symm⟩⟩, loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩ } : SimpleGraph (Fin m)), triangleDeletion_le f, triangleDeletion_free f,
      fun h => hbad.1 (h.mono_right (triangleDeletion_le f)), ?_⟩
    intro hcontain
    have hnot := ((({ Adj := fun x y => G.Adj x y ∧ ∀ T : ↥(G.cliqueFinset 3), x ∈ T.val → y ∈ T.val → (f T).val = x ∨ (f T).val = y, symm := ⟨fun _ _ h => ⟨h.1.symm, fun T hy hx => (h.2 T hx hy).symm⟩⟩, loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩ } : SimpleGraph (Fin m)))ᶜ.not_cliqueFree_iff_top_isContained k).mpr hcontain
    apply hnot
    intro W hW
    apply hf W (mem_powersetCard.mpr ⟨subset_univ _, hW.card_eq⟩)
    simpa only [isClique_compl] using hW.isClique
  by_contra! hall
  have hcover : (univ : Finset ((∀ T : ↥(G.cliqueFinset 3), ↥(T : Finset (Fin m))))) ⊆
      P.biUnion (fun W => (univ.filter (fun f : (∀ T : ↥(G.cliqueFinset 3), ↥(T : Finset (Fin m))) => (({ Adj := fun x y => G.Adj x y ∧ ∀ T : ↥(G.cliqueFinset 3), x ∈ T.val → y ∈ T.val → (f T).val = x ∨ (f T).val = y, symm := ⟨fun _ _ h => ⟨h.1.symm, fun T hy hx => (h.2 T hx hy).symm⟩⟩, loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩ } : SimpleGraph (Fin m))).IsIndepSet (W : Set (Fin m))))) := by
    intro f _
    obtain ⟨W, hW, hI⟩ := hall f
    exact mem_biUnion.mpr ⟨W, hW, mem_filter.mpr ⟨mem_univ _, hI⟩⟩
  let M := 3 ^ Fintype.card (↥(G.cliqueFinset 3))
  have htotal : M ≤ ∑ W ∈ P, ((univ.filter (fun f : (∀ T : ↥(G.cliqueFinset 3), ↥(T : Finset (Fin m))) => (({ Adj := fun x y => G.Adj x y ∧ ∀ T : ↥(G.cliqueFinset 3), x ∈ T.val → y ∈ T.val → (f T).val = x ∨ (f T).val = y, symm := ⟨fun _ _ h => ⟨h.1.symm, fun T hy hx => (h.2 T hx hy).symm⟩⟩, loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩ } : SimpleGraph (Fin m))).IsIndepSet (W : Set (Fin m))))).card := by
    dsimp only [M]
    rw [← triangle_choice_space_card (G := G), ← card_univ]
    exact (card_le_card hcover).trans card_biUnion_le
  have hsum : (∑ W ∈ P, ((univ.filter (fun f : (∀ T : ↥(G.cliqueFinset 3), ↥(T : Finset (Fin m))) => (({ Adj := fun x y => G.Adj x y ∧ ∀ T : ↥(G.cliqueFinset 3), x ∈ T.val → y ∈ T.val → (f T).val = x ∨ (f T).val = y, symm := ⟨fun _ _ h => ⟨h.1.symm, fun T hy hx => (h.2 T hx hy).symm⟩⟩, loopless := ⟨fun _ h => G.ne_of_adj h.1 rfl⟩ } : SimpleGraph (Fin m))).IsIndepSet (W : Set (Fin m))))).card) * 3 ^ (k * d) ≤ P.card * M := by
    rw [Finset.sum_mul]
    calc
      _ ≤ ∑ _ ∈ P, M := by
        apply sum_le_sum
        intro W hW
        have hcard := (mem_powersetCard.mp hW).2
        have h := badTriangleChoices_card hbad W (by rw [hcard])
        rw [hcard] at h
        exact h
      _ = _ := by simp
  have hpos : 0 < M := by dsimp [M]; positivity
  have hc := (Nat.mul_le_mul_right (3 ^ (k * d)) htotal).trans hsum
  rw [Nat.mul_comm M] at hc
  exact (Nat.not_lt_of_ge (Nat.le_of_mul_le_mul_right hc hpos)) hlt


private lemma bad_card_le_quadratic {n m : ℕ} {G : SimpleGraph (Fin m)}
    (hbad : (¬ (cycleGraph 4).IsContained G ∧ ¬ (completeGraph (Fin n)).IsContained Gᶜ)) (hn : 1 ≤ n) : m ≤ 2 * n ^ 2 := by
  classical
  let S : Finset (Fin m) := univ
  let d := 2 * (n - 1) + 1
  obtain ⟨U, hUS, hcard, hmin⟩ := minimum_degree_core G d (n - 1) S
    (fun I _ => indep_card_le hbad I)
  have hU : U = ∅ := by
    apply not_nonempty_iff_eq_empty.mp
    rintro ⟨x, hx⟩
    obtain ⟨htri, hdeg⟩ := neighborhood_triangle_bounds hbad U hx
    have hlow := hmin x hx
    dsimp only [d] at hlow
    omega
  rw [hU, card_empty, zero_add] at hcard
  calc
    m = S.card := by simp [S]
    _ ≤ (n - 1) * d := hcard
    _ ≤ n * (2 * n) := by dsimp only [d]; gcongr <;> omega
    _ = _ := by ring

/-- A power bound for triangle-free, four-cycle-free graphs without independent
`n`-sets suffices for the four-cycle versus clique Ramsey problem. -/
theorem ramsey_of_triangle_free_bound {ε A : ℝ}
    (hε : 0 < ε) (hεone : ε ≤ 1) (hA : 1 ≤ A)
    (hfree : ∀ (n m : ℕ) (G : SimpleGraph (Fin m)), 1 ≤ n →
      ¬ (cycleGraph 4).IsContained G → G.CliqueFree 3 →
      ¬ (completeGraph (Fin n)).IsContained Gᶜ → (m : ℝ) ≤ A * (n : ℝ) ^ (2 - ε)) :
    ∃ C : ℝ, ∀ n : ℕ, 1 ≤ n →
      (graphRamsey (cycleGraph 4) (completeGraph (Fin n)) : ℝ) ≤
        C * (n : ℝ) ^ (2 - ε / 2) := by
  let p := ε / 4
  let K : ℝ := 1 + (Real.log 2 + 2 / p) / Real.log 3
  let C : ℝ := A * (8 * K) ^ (2 - ε)
  have hp : 0 < p := by dsimp only [p]; positivity
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg (by linarith) (Real.rpow_nonneg (by positivity) _)
  have hcard (n m : ℕ) (hn : 1 ≤ n) (G : SimpleGraph (Fin m))
      (hbad : ¬ (cycleGraph 4).IsContained G ∧ ¬ (completeGraph (Fin n)).IsContained Gᶜ) : (m : ℝ) ≤ C * (n : ℝ) ^ (2 - ε / 2) := by
    by_cases hm : m = 0
    · subst m; simpa using mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg n) (2 - ε / 2))
    let d := Nat.log 3 m + 1
    have hd : 0 < d := by dsimp only [d]; omega
    have hnm : m < 3 ^ d := Nat.lt_pow_succ_log_self (by decide) m
    obtain ⟨H, _, hHfree, hHbad⟩ :=
      exists_triangle_free_spanning_subgraph hbad hd hnm hn
    let k := 8 * n * d
    have hk : 1 ≤ k := by
      change 0 < 8 * n * d
      positivity
    have hH := hfree k m H hk hHbad.1 hHfree hHbad.2
    have hmreal : 0 < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hnpos : 0 < (n : ℝ) := by linarith
    have hpow : 1 ≤ (n : ℝ) ^ p := Real.one_le_rpow hnreal hp.le
    have hlogm : (Nat.log 3 m : ℝ) * Real.log 3 ≤ Real.log (m : ℝ) := by
      have hpowlog : (3 : ℝ) ^ Nat.log 3 m ≤ (m : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 3 hm
      simpa only [Real.log_pow] using Real.log_le_log (by positivity) hpowlog
    have hquadratic : (m : ℝ) ≤ 2 * (n : ℝ) ^ 2 := by
      exact_mod_cast bad_card_le_quadratic hbad hn
    have hlogn : Real.log (m : ℝ) ≤ Real.log 2 + 2 * Real.log (n : ℝ) := by
      calc
        _ ≤ Real.log (2 * (n : ℝ) ^ 2) := Real.log_le_log hmreal hquadratic
        _ = _ := by rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]; norm_num
    have hlogbound : Real.log (n : ℝ) ≤ (n : ℝ) ^ p / p :=
      Real.log_le_rpow_div (Nat.cast_nonneg n) hp
    have hd_upper : (d : ℝ) ≤ K * (n : ℝ) ^ p := by
      rw [← le_div_iff₀ hlog3] at hlogm
      have hd' : (d : ℝ) = (Nat.log 3 m : ℝ) + 1 := by simp [d]
      rw [hd']
      calc
        _ ≤ Real.log (m : ℝ) / Real.log 3 + 1 := add_le_add_left hlogm 1
        _ ≤ (Real.log 2 + 2 * Real.log (n : ℝ)) / Real.log 3 + 1 := by gcongr
        _ ≤ ((Real.log 2 + 2 / p) * (n : ℝ) ^ p) / Real.log 3 + (n : ℝ) ^ p := by
          gcongr
          nlinarith only [hlogbound, mul_nonneg hlog2 (sub_nonneg.mpr hpow),
            show 2 * ((n : ℝ) ^ p / p) = (2 / p) * (n : ℝ) ^ p by ring]
        _ = _ := by dsimp only [K]; ring
    have hk_upper : (k : ℝ) ≤ (8 * K) * (n : ℝ) ^ (1 + p) := by
      have hk' : (k : ℝ) = 8 * (n : ℝ) * (d : ℝ) := by simp [k]
      rw [hk', Real.rpow_add hnpos, Real.rpow_one]
      calc
        _ ≤ 8 * (n : ℝ) * (K * (n : ℝ) ^ p) := by gcongr
        _ = _ := by ring
    have hexp : (1 + p) * (2 - ε) ≤ 2 - ε / 2 := by
      dsimp only [p]
      nlinarith only [sq_nonneg ε]
    have hpow_k : (k : ℝ) ^ (2 - ε) ≤ (8 * K) ^ (2 - ε) * (n : ℝ) ^ (2 - ε / 2) := by
      calc
        _ ≤ ((8 * K) * (n : ℝ) ^ (1 + p)) ^ (2 - ε) :=
          Real.rpow_le_rpow (Nat.cast_nonneg k) hk_upper (by linarith)
        _ = (8 * K) ^ (2 - ε) * (n : ℝ) ^ ((1 + p) * (2 - ε)) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hnpos.le]
        _ ≤ _ := by gcongr
    calc
      _ ≤ A * (k : ℝ) ^ (2 - ε) := hH
      _ ≤ A * ((8 * K) ^ (2 - ε) * (n : ℝ) ^ (2 - ε / 2)) :=
        mul_le_mul_of_nonneg_left hpow_k (by linarith)
      _ = _ := by dsimp only [C]; ring
  refine ⟨C + 1, fun n hn => ?_⟩
  let X := (n : ℝ) ^ (2 - ε / 2)
  have hX : 1 ≤ X := Real.one_le_rpow (by exact_mod_cast hn) (by linarith)
  let N := ⌊C * X⌋₊ + 1
  have hN : C * X < (N : ℝ) := by simpa [N] using Nat.lt_floor_add_one (C * X)
  have hit (G : SimpleGraph (Fin N)) :
      (cycleGraph 4).IsContained G ∨ (completeGraph (Fin n)).IsContained Gᶜ := by
    by_contra h
    exact hN.not_ge (hcard n N hn G (not_or.mp h))
  have hRamsey : graphRamsey (cycleGraph 4) (completeGraph (Fin n)) ≤ N := Nat.sInf_le hit
  calc
    _ ≤ (N : ℝ) := by exact_mod_cast hRamsey
    _ ≤ C * X + 1 := by
      simpa [N] using add_le_add_right (Nat.floor_le (by positivity : 0 ≤ C * X)) (1 : ℝ)
    _ ≤ (C + 1) * X := by linarith only [hX]

/-- Triangle-free, four-cycle-free graphs with no independent `n`-set and all
degrees at most `n / 2` have at most `A * n ^ (2 - ε)` vertices. -/
def H1 : Prop :=
  ∃ ε A : ℝ, 0 < ε ∧ 1 ≤ A ∧
    ∀ (n m : ℕ) (G : SimpleGraph (Fin m)), 1 ≤ n →
      ¬ (cycleGraph 4).IsContained G → G.CliqueFree 3 →
      ¬ (completeGraph (Fin n)).IsContained Gᶜ →
      (∀ v : Fin m, 2 * (Finset.univ.filter (G.Adj v)).card ≤ n) →
      (m : ℝ) ≤ A * (n : ℝ) ^ (2 - ε)

/-- The same bound for such graphs having a vertex of degree above `n / 2`. -/
def H2 : Prop :=
  ∃ ε A : ℝ, 0 < ε ∧ 1 ≤ A ∧
    ∀ (n m : ℕ) (G : SimpleGraph (Fin m)), 1 ≤ n →
      ¬ (cycleGraph 4).IsContained G → G.CliqueFree 3 →
      ¬ (completeGraph (Fin n)).IsContained Gᶜ →
      (∃ v : Fin m, n < 2 * (Finset.univ.filter (G.Adj v)).card) →
      (m : ℝ) ≤ A * (n : ℝ) ^ (2 - ε)

theorem main : H1 → H2 → type_of% @Erdos159.erdos_159 := by
  rintro ⟨ε₁, A₁, hε₁, hA₁, h₁⟩ ⟨ε₂, A₂, hε₂, hA₂, h₂⟩
  have hε : 0 < min (min ε₁ ε₂) 1 := lt_min (lt_min hε₁ hε₂) one_pos
  have hεone : min (min ε₁ ε₂) 1 ≤ 1 := min_le_right _ _
  have hA : 1 ≤ max A₁ A₂ := hA₁.trans (le_max_left _ _)
  have hmono : ∀ n : ℕ, 1 ≤ n → ∀ e B : ℝ, 0 ≤ B → B ≤ max A₁ A₂ →
      min (min ε₁ ε₂) 1 ≤ e →
      B * (n : ℝ) ^ (2 - e) ≤ max A₁ A₂ * (n : ℝ) ^ (2 - min (min ε₁ ε₂) 1) := by
    intro n hn e B hB hBA he
    have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
    calc
      B * (n : ℝ) ^ (2 - e) ≤ max A₁ A₂ * (n : ℝ) ^ (2 - e) :=
        mul_le_mul_of_nonneg_right hBA (Real.rpow_nonneg (Nat.cast_nonneg n) _)
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hnr (by linarith)) (by linarith)
  have hfree : ∀ (n m : ℕ) (G : SimpleGraph (Fin m)), 1 ≤ n →
      ¬ (cycleGraph 4).IsContained G → G.CliqueFree 3 →
      ¬ (completeGraph (Fin n)).IsContained Gᶜ →
      (m : ℝ) ≤ max A₁ A₂ * (n : ℝ) ^ (2 - min (min ε₁ ε₂) 1) := by
    intro n m G hn hc hf hi
    by_cases hd : ∀ v : Fin m, 2 * (Finset.univ.filter (G.Adj v)).card ≤ n
    · exact (h₁ n m G hn hc hf hi hd).trans (hmono n hn ε₁ A₁ (by linarith)
        (le_max_left _ _) ((min_le_left _ _).trans (min_le_left _ _)))
    · push Not at hd
      exact (h₂ n m G hn hc hf hi hd).trans (hmono n hn ε₂ A₂ (by linarith)
        (le_max_right _ _) ((min_le_left _ _).trans (min_le_right _ _)))
  obtain ⟨C, hC⟩ := ramsey_of_triangle_free_bound hε hεone hA hfree
  exact ⟨min (min ε₁ ε₂) 1 / 2, by positivity, C, hC⟩

end OMA.R_Erdos159_erdos_159_R2
