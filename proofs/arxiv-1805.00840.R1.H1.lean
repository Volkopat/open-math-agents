import OMAReductions.R_arxiv_1805_00840_R1

-- Credit: @ryansolves
-- The residual cubic case uses deletion or a six-vertex cut.

namespace BridgePort
open SimpleGraph OMA.S_arxiv_1805_00840
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem extend_matching (W : Set V) {x y : V} (edge : G.Adj x y) (hx : x ∈ W) (hy : y ∈ W)
    (M : G.Subgraph) (hm : IsUniquelyRestricted M) (covered : M.verts ⊆ W)
    (outX : x ∉ M.verts) (outY : y ∉ M.verts) (noOther : ∀ z ∈ M.verts, ¬G.Adj x z) :
    ∃ T : G.Subgraph, IsUniquelyRestricted T ∧ T.verts ⊆ W ∧
      T.edgeSet.ncard = M.edgeSet.ncard + 1 := by
  let E := G.subgraphOfAdj edge
  have dis : Disjoint M.verts E.verts := by
    apply Set.disjoint_left.mpr
    intro z hz he
    rcases (show z = x ∨ z = y from he) with rfl | rfl <;> contradiction
  refine ⟨M ⊔ E,OMA.R_arxiv_1805_00840_R1.uniquelyRestricted_add_forced hm edge outX outY noOther,?_,?_⟩
  · intro z hz
    rcases hz with old | h
    · exact covered old
    · rcases (show z=x ∨ z=y from h) with rfl | rfl <;> assumption
  · rw [BridgePortHelpers.sup_size _ _ dis,edgeSet_subgraphOfAdj,Set.ncard_singleton]

end BridgePort

namespace BridgePort
open SimpleGraph OMA.S_arxiv_1805_00840
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem small_biclique (hd : ∀ x, G.degree x ≤ 3)
    (noK : ∀ x y : V, x ≠ y → (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 2)
    (A B : Finset V) (ha : A.Nonempty) (hb : B.Nonempty)
    (edges : ∀ x ∈ A, ∀ y ∈ B, G.Adj x y) : A.card + B.card ≤ 4 := by
  classical
  have side (L R : Finset V) (ne : L.Nonempty) (allE : ∀ x ∈ L, ∀ y ∈ R, G.Adj x y) :
      R.card ≤ 3 ∧ (1 < L.card → R.card ≤ 2) := by
    obtain ⟨x,hx⟩ := ne
    have inc : (R : Set V) ⊆ G.neighborSet x := fun y hy => allE x hx y hy
    have n := Set.ncard_le_ncard inc
    rw [Set.ncard_coe_finset,← Set.fintypeCard_eq_ncard,card_neighborSet_eq_degree] at n
    refine ⟨n.trans (hd x),?_⟩
    intro two
    obtain ⟨p,q,hp,hq,pq⟩ := Finset.one_lt_card_iff.mp two
    have inc' : (R : Set V) ⊆ G.neighborSet p ∩ G.neighborSet q :=
      fun y hy => ⟨allE p hp y hy,allE q hq y hy⟩
    simpa using (Set.ncard_le_ncard inc').trans (noK p q pq)
  obtain ⟨b,ab⟩ := side A B ha edges
  obtain ⟨a,ba⟩ := side B A hb (fun y hy x hx => (edges x hx y hy).symm)
  omega

/-- Greedily peel the neighbors of a minimum-degree vertex and the vertices
with exactly its neighborhood. Each step pays at most four vertices per edge. -/
theorem greedy_region (hd : ∀ x, G.degree x ≤ 3)
    (noK : ∀ x y : V, x ≠ y → (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 2)
    (W : Finset V) (noIso : ∀ x ∈ W, ∃ y ∈ W, G.Adj x y) :
    ∃ M : G.Subgraph, IsUniquelyRestricted M ∧ M.verts ⊆ (W : Set V) ∧ W.card ≤ 4*M.edgeSet.ncard := by
  classical
  by_cases ne : W.Nonempty
  · let N (x : V) := (G.neighborFinset x).filter (· ∈ W)
    have memN (x y : V) : y ∈ N x ↔ G.Adj x y ∧ y ∈ W := by simp [N]
    obtain ⟨p,hp,hmin⟩ := Finset.exists_min_image W (fun x => (N x).card) ne
    obtain ⟨u,hu,pu⟩ := noIso p hp
    let L := W.filter (fun x => N x = N p)
    have pl : p ∈ L := Finset.mem_filter.mpr ⟨hp,rfl⟩
    have cross (x : V) (hx : x ∈ L) (y : V) (hy : y ∈ N p) : G.Adj x y := by
      exact ((memN x y).mp (((Finset.mem_filter.mp hx).2).symm ▸ hy)).1
    have unb : u ∈ N p := (memN p u).mpr ⟨pu,hu⟩
    have bound := small_biclique hd noK L (N p) ⟨p,pl⟩ ⟨u,unb⟩ cross
    let D := L ∪ N p
    let R := W \ D
    have good (x : V) (hx : x ∈ R) : ∃ y ∈ R, G.Adj x y := by
      obtain ⟨inW,notD⟩ := Finset.mem_sdiff.mp hx
      have notL : x ∉ L := fun h => notD (Finset.mem_union_left _ h)
      have notN : x ∉ N p := fun h => notD (Finset.mem_union_right _ h)
      have ns : ¬N x ⊆ N p := by
        intro sub
        exact notL (Finset.mem_filter.mpr ⟨inW,Finset.eq_of_subset_of_card_le sub (hmin x inW)⟩)
      obtain ⟨y,hy,miss⟩ := Finset.not_subset.mp ns
      have edge := (memN x y).mp hy
      refine ⟨y,Finset.mem_sdiff.mpr ⟨edge.2,?_⟩,edge.1⟩
      intro inside
      rcases Finset.mem_union.mp inside with hl | hn
      · have hxy := (memN y x).mpr ⟨edge.1.symm,inW⟩
        exact notN ((Finset.mem_filter.mp hl).2 ▸ hxy)
      · exact miss hn
    have rp : p ∉ R := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_union_left _ pl)
    have ru : u ∉ R := fun h => (Finset.mem_sdiff.mp h).2 (Finset.mem_union_right _ unb)
    have smaller : R.card < W.card := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.sdiff_subset,fun eq => rp ((congrArg (fun s : Finset V => p ∈ s) eq).mpr hp)⟩)
    obtain ⟨M,hm,sub,sz⟩ := greedy_region hd noK R good
    have rW : R ⊆ W := Finset.sdiff_subset
    obtain ⟨T,ht,cover,total⟩ := extend_matching (W : Set V) pu hp hu M hm
      (fun z hz => rW (sub hz)) (fun h => rp (sub h)) (fun h => ru (sub h))
      (fun z hz adj => (Finset.mem_sdiff.mp (sub hz)).2
        (Finset.mem_union_right _ ((memN p z).mpr ⟨adj,rW (sub hz)⟩)))
    have pay := Finset.card_sdiff_add_card_inter W D
    have boundD := Finset.card_union_le L (N p)
    have cap := Finset.card_le_card (Finset.inter_subset_right (s₁ := W) (s₂ := D))
    change R.card + (W ∩ D).card = W.card at pay
    change D.card ≤ _ at boundD
    exact ⟨T,ht,cover,by omega⟩
  · refine ⟨⊥,OMA.R_arxiv_1805_00840_R1.empty_ur,by simp,?_⟩
    simp [Finset.not_nonempty_iff_eq_empty.mp ne]
termination_by W.card
decreasing_by
  exact smaller

theorem unweighted_without_biclique (hd : ∀ x, G.degree x = 3)
    (noK : ∀ x y : V, x ≠ y → (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 2) :
    ∃ M : G.Subgraph, IsUniquelyRestricted M ∧ G.edgeFinset.card ≤ 6*M.edgeSet.ncard := by
  classical
  obtain ⟨M,hm,_,sz⟩ := greedy_region (fun x => (hd x).le) noK Finset.univ (by
    intro x _
    have pos : 0 < (G.neighborFinset x).card := by rw [card_neighborFinset_eq_degree,hd]; decide
    obtain ⟨y,hy⟩ := Finset.card_pos.mp pos
    exact ⟨y,Finset.mem_univ _,(G.mem_neighborFinset ..).mp hy⟩)
  have edges := G.sum_degrees_eq_twice_card_edges
  simp only [hd,Finset.sum_const,Finset.card_univ,smul_eq_mul] at edges
  rw [Finset.card_univ] at sz
  exact ⟨M,hm,by omega⟩

end BridgePort

namespace BridgePort
open SimpleGraph
variable {V : Type} [Fintype V]
abbrev Incoming (G : SimpleGraph V) (W : Set V) := Σ v : ↥(Wᶜ), {y : G.neighborSet v // (y : V) ∈ W}
end BridgePort

namespace BridgePort
open SimpleGraph BridgePortHelpers BridgeMatching OMA.S_arxiv_1805_00840
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure SixRegion (G : SimpleGraph V) where
  D : Set V
  p : V
  a : V
  b : V
  z : V
  w : V
  card : D.ncard = 6
  cut : Nat.card (Incoming G Dᶜ) ≤ 5
  pin : p ∈ D
  ain : a ∈ D
  bin : b ∈ D
  zin : z ∈ D
  pb : G.Adj p b
  az : G.Adj a z
  pa : p ≠ a
  pz : p ≠ z
  ba : b ≠ a
  bz : b ≠ z
  noBA : ¬G.Adj b a
  noBZ : ¬G.Adj b z
  pN : G.neighborSet p ⊆ D
  aN : G.neighborSet a ⊆ D
  bN : ∀ y, G.Adj b y → y ∈ D ∨ y = w

theorem use_six_region (hc : G.Connected) (hd : ∀ x, G.degree x = 3)
    (hb : ∀ e ∈ G.edgeSet, ¬G.IsBridge e) (modulo : Fintype.card V % 4 = 2) (C : SixRegion G) :
    ∃ M : G.Subgraph, IsUniquelyRestricted M ∧ G.edgeFinset.card ≤ 6*M.edgeSet.ncard := by
  classical
  let W := C.Dᶜ
  have total := Set.ncard_add_ncard_compl C.D
  rw [C.card,Nat.card_eq_fintype_card] at total
  change 6 + W.ncard = Fintype.card V at total
  have even : Even W.ncard := by rw [Nat.even_iff]; omega
  obtain ⟨P,hP⟩ := perfect_small_cut W even (fun x => hd x) hb C.cut
  let A := P.map (Embedding.induce W).toHom
  have ha : A.IsMatching := hP.1.map _ (Embedding.induce (G := G) W).injective
  obtain ⟨L,R,hL,hR,dis,eq⟩ := BridgeCubic.split_proper hc (fun x => (hd x).le) A ha
    ⟨C.p,fun h => lift_in_side P h C.pin⟩
  have pe := matching_size P hP.1
  rw [hP.2.verts_eq_univ,Set.ncard_univ,Nat.card_coe_set_eq] at pe
  have sizes := BridgePortHelpers.sup_size L R dis
  rw [eq,lift_size] at sizes
  have cover (M : G.Subgraph) (h : M ≤ A) : M.verts ⊆ W := fun x hx => lift_in_side P (h.1 hx)
  have lc := cover L (eq ▸ le_sup_left)
  have rc := cover R (eq ▸ le_sup_right)
  have edges := G.sum_degrees_eq_twice_card_edges
  simp only [hd,Finset.sum_const,Finset.card_univ,smul_eq_mul] at edges
  have addOne (M : G.Subgraph) (hm : IsUniquelyRestricted M) (sub : M.verts ⊆ W)
      (large : G.edgeFinset.card ≤ 6*(M.edgeSet.ncard + 1)) :
      ∃ T : G.Subgraph, IsUniquelyRestricted T ∧ G.edgeFinset.card ≤ 6*T.edgeSet.ncard := by
    obtain ⟨T,ht,_,sz⟩ := extend_matching Set.univ C.pb (Set.mem_univ _) (Set.mem_univ _)
      M hm (Set.subset_univ _) (fun h => sub h C.pin) (fun h => sub h C.bin)
      (fun x hx h => sub hx (C.pN h))
    exact ⟨T,ht,by omega⟩
  have addTwo (M : G.Subgraph) (hm : IsUniquelyRestricted M) (sub : M.verts ⊆ W)
      (free : C.w ∉ M.verts) (large : G.edgeFinset.card ≤ 6*(M.edgeSet.ncard + 2)) :
      ∃ T : G.Subgraph, IsUniquelyRestricted T ∧ G.edgeFinset.card ≤ 6*T.edgeSet.ncard := by
    let S : Set V := M.verts ∪ {C.a,C.z}
    obtain ⟨J,hJ,jS,sz⟩ := extend_matching S C.az (Or.inr (Or.inl rfl)) (Or.inr (Or.inr rfl))
      M hm Set.subset_union_left (fun h => sub h C.ain) (fun h => sub h C.zin)
      (fun x hx h => sub hx (C.aN h))
    have bout : C.b ∉ J.verts := fun h => (jS h).elim (fun hb => sub hb C.bin) (fun hb => hb.elim C.ba C.bz)
    have pout : C.p ∉ J.verts := fun h => (jS h).elim (fun hp => sub hp C.pin) (fun hp => hp.elim C.pa C.pz)
    have safe (x : V) (hx : x ∈ J.verts) (h : G.Adj C.b x) : False := by
      rcases jS hx with old | pair
      · exact (C.bN x h).elim (sub old) (fun e => free (e ▸ old))
      · rcases (show x=C.a ∨ x=C.z from pair) with rfl | rfl
        · exact C.noBA h
        · exact C.noBZ h
    obtain ⟨T,ht,_,ts⟩ := extend_matching Set.univ C.pb.symm (Set.mem_univ _) (Set.mem_univ _)
      J hJ (Set.subset_univ _) bout pout safe
    exact ⟨T,ht,by omega⟩
  by_cases same : L.edgeSet.ncard = R.edgeSet.ncard
  · by_cases used : C.w ∈ L.verts
    · exact addTwo R hR rc (fun h => Set.disjoint_left.mp dis used h) (by omega)
    · exact addTwo L hL lc used (by omega)
  · by_cases larger : L.edgeSet.ncard ≥ R.edgeSet.ncard
    · exact addOne L hL lc (by omega)
    · exact addOne R hR rc (by omega)

end BridgePort

namespace BridgePort
open SimpleGraph
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem third_neighbor {p q x : V} (pq : p ≠ q) (px : G.Adj p x) (qx : G.Adj q x)
    (deg : G.degree x = 3) : ∃ z, G.Adj x z ∧ z ≠ p ∧ z ≠ q ∧
      ∀ y, G.Adj x y → y = p ∨ y = q ∨ y = z := by
  classical
  let N := G.neighborFinset x
  have card : N.card = 3 := (G.card_neighborFinset_eq_degree x).trans deg
  have small : ¬N ⊆ {p,q} := by
    intro sub
    have := Finset.card_le_card sub
    simp [pq] at this
    omega
  obtain ⟨z,hz,out⟩ := Finset.not_subset.mp small
  have znp : z ≠ p := fun h => out (Finset.mem_insert.mpr (Or.inl h))
  have znq : z ≠ q := fun h => out (Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr h)))
  have eq : ({p,q,z} : Finset V) = N := by
    apply Finset.eq_of_subset_of_card_le
    · intro y hy
      simp only [Finset.mem_insert,Finset.mem_singleton] at hy
      rcases hy with rfl | rfl | rfl
      · exact (G.mem_neighborFinset ..).mpr px.symm
      · exact (G.mem_neighborFinset ..).mpr qx.symm
      · exact hz
    · simp [pq,znp.symm,znq.symm,card]
  refine ⟨z,(G.mem_neighborFinset ..).mp hz,znp,znq,fun y hy => ?_⟩
  have h : y ∈ N := (G.mem_neighborFinset ..).mpr hy
  simpa only [← eq,Finset.mem_insert,Finset.mem_singleton] using h

theorem two_stars_edges {X : Type} [Fintype X] (B : SimpleGraph X) [DecidableRel B.Adj]
    (p q a z : X) (pq : p ≠ q) (noEdge : ¬B.Adj p q) (az : B.Adj a z)
    (pa : p ≠ a) (pz : p ≠ z) (qa : q ≠ a) (qz : q ≠ z) :
    B.degree p + B.degree q < B.edgeFinset.card := by
  classical
  have dis : Disjoint (B.incidenceFinset p) (B.incidenceFinset q) := by
    apply Finset.disjoint_left.mpr
    rintro e hp hq
    obtain ⟨x,y⟩ := e
    rw [mem_incidenceFinset,mk'_mem_incidenceSet_iff] at hp hq
    rcases hp.2 with rfl | rfl <;> rcases hq.2 with eq | eq <;> grind [B.adj_comm]
  have miss : s(a,z) ∉ B.incidenceFinset p ∪ B.incidenceFinset q := by
    simp only [Finset.mem_union,mem_incidenceFinset,mk'_mem_incidenceSet_iff]
    tauto
  have strict := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
    ⟨Finset.union_subset (B.incidenceFinset_subset p) (B.incidenceFinset_subset q),
      fun eq => miss ((congrArg (fun F : Finset (Sym2 X) => s(a,z) ∈ F) eq).mpr (B.mem_edgeFinset.mpr az))⟩)
  rwa [Finset.card_union_of_disjoint dis,card_incidenceFinset_eq_degree,card_incidenceFinset_eq_degree] at strict

theorem bounded_twin_cut (hd : ∀ x, G.degree x = 3) (D : Set V) (dsize : D.ncard = 6)
    {p q a z : V} (pin : p ∈ D) (qin : q ∈ D) (ain : a ∈ D) (zin : z ∈ D)
    (pn : G.neighborSet p ⊆ D) (qn : G.neighborSet q ⊆ D) (pq : p ≠ q)
    (noEdge : ¬G.Adj p q) (az : G.Adj a z) (pa : p ≠ a) (pz : p ≠ z) (qa : q ≠ a) (qz : q ≠ z) :
    Nat.card (Incoming G Dᶜ) ≤ 5 := by
  classical
  let B := G.induce D
  let P : D := ⟨p,pin⟩
  let Q : D := ⟨q,qin⟩
  have strict := two_stars_edges B P Q ⟨a,ain⟩ ⟨z,zin⟩ (fun e => pq (congrArg Subtype.val e))
    noEdge az (fun e => pa (congrArg Subtype.val e)) (fun e => pz (congrArg Subtype.val e))
    (fun e => qa (congrArg Subtype.val e)) (fun e => qz (congrArg Subtype.val e))
  have dp : B.degree P = G.degree p := degree_induce_of_neighborSet_subset (v := P) pn
  have dq : B.degree Q = G.degree q := degree_induce_of_neighborSet_subset (v := Q) qn
  rw [dp,dq,hd,hd,edgeFinset_card,Set.fintypeCard_eq_ncard] at strict
  have cap := cut_cap (fun x => (hd x).le) D
  change Nat.card (Incoming G Dᶜ) + 2 * (G.induce D).edgeSet.ncard ≤ 3 * D.ncard at cap
  change 3 + 3 < (G.induce D).edgeSet.ncard at strict
  omega

end BridgePort

namespace BridgePort
open SimpleGraph
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

/-- At the minimum possible order, a triangle-free regular graph containing a
vertex is the balanced complete bipartite graph. -/
theorem balanced_of_order_twice (p : V) (d : ℕ) (hd : ∀ x, G.degree x = d)
    (triangleFree : ∀ x y z, G.Adj x y → G.Adj x z → ¬G.Adj y z)
    (order : Fintype.card V = 2*d) :
    Nonempty (G ≃g completeBipartiteGraph (Fin d) (Fin d)) := by
  classical
  let L := G.neighborSet p
  let R := Lᶜ
  have sizeL : L.ncard = d := by
    change (G.neighborSet p).ncard = d
    rw [← Set.fintypeCard_eq_ncard,card_neighborSet_eq_degree,hd]
  have sizeR : R.ncard = d := by
    change Lᶜ.ncard = d
    rw [Set.ncard_compl,Nat.card_eq_fintype_card,order,sizeL]
    omega
  have regular (x : V) : (G.neighborSet x).ncard = d := by
    rw [← Set.fintypeCard_eq_ncard,card_neighborSet_eq_degree,hd]
  have toR (x : L) : G.neighborSet x.1 = R := by
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · exact fun y hxy hy => triangleFree p x y x.2 hy hxy
    · rw [sizeR,regular]
  have toL (x : R) : G.neighborSet x.1 = L := by
    symm
    refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
    · intro y hy
      have xy : x.1 ∈ G.neighborSet y := (toR ⟨y,hy⟩).symm ▸ x.2
      exact G.adj_symm xy
    · rw [regular,sizeL]
  let l : L ≃ Fin d := Fintype.equivFinOfCardEq (by rwa [Set.fintypeCard_eq_ncard])
  let r : R ≃ Fin d := Fintype.equivFinOfCardEq (by rwa [Set.fintypeCard_eq_ncard])
  let f : Fin d ⊕ Fin d ≃ V := (Equiv.sumCongr l.symm r.symm).trans (Equiv.Set.sumCompl L)
  suffices h : Nonempty (completeBipartiteGraph (Fin d) (Fin d) ≃g G) from
    h.map (fun iso => iso.symm)
  refine ⟨{ toEquiv := f, map_rel_iff' := ?_ }⟩
  rintro (x|x) (y|y) <;> simp [completeBipartiteGraph]
  · change (l.symm y).1 ∉ G.neighborSet (l.symm x).1
    rw [toR]
    exact fun h => h (l.symm y).2
  · change (r.symm y).1 ∈ G.neighborSet (l.symm x).1
    rw [toR]
    exact (r.symm y).2
  · change (l.symm y).1 ∈ G.neighborSet (r.symm x).1
    rw [toL]
    exact (l.symm y).2
  · change (r.symm y).1 ∉ G.neighborSet (r.symm x).1
    rw [toL]
    exact (r.symm y).2


theorem residual_order (hc : G.Connected) (hd : ∀ x, G.degree x = 3)
    (triangleFree : ∀ x y z, G.Adj x y → G.Adj x z → ¬G.Adj y z)
    (modulo : Fintype.card V % 4 = 2)
    (hk : IsEmpty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3))) : 10 ≤ Fintype.card V := by
  obtain ⟨p⟩ := hc.nonempty
  have low := G.degree_lt_card_verts p
  rw [hd] at low
  by_contra! small
  have order : Fintype.card V = 2*3 := by omega
  obtain ⟨iso⟩ := balanced_of_order_twice p 3 hd triangleFree order
  exact hk.false iso

end BridgePort

namespace BridgePort
open SimpleGraph OMA.S_arxiv_1805_00840
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem region_from_twins (hc : G.Connected) (hd : ∀ x, G.degree x = 3)
    (triangle : ∀ a b c, G.Adj a b → G.Adj a c → ¬G.Adj b c) (big : 6 < Fintype.card V)
    {p q : V} (pq : p ≠ q) (same : G.neighborSet q = G.neighborSet p) : Nonempty (SixRegion G) := by
  classical
  let S := G.neighborSet p
  let D (z : V) : Set V := insert p (insert q (insert z S))
  have member (z x : V) : x ∈ D z ↔ x=p ∨ x=q ∨ x=z ∨ x∈S := Iff.rfl
  have regular (x : V) : (G.neighborSet x).ncard = 3 := by
    rw [← Set.fintypeCard_eq_ncard,card_neighborSet_eq_degree,hd]
  have ns : S.ncard = 3 := regular p
  have noPS : p ∉ S := G.irrefl
  have noQS : q ∉ S := fun h => G.irrefl ((show q ∈ G.neighborSet q from same.symm ▸ h))
  have qe (x : S) : G.Adj q x := (congrArg (fun s : Set V => x.1 ∈ s) same).mpr x.2
  choose f edge notP notQ nh using fun x : S => third_neighbor pq x.2 (qe x) (hd x)
  have f_out (x : S) : f x ∉ S := fun h => triangle p x (f x) x.2 h (edge x)
  have six (x : S) : (D (f x)).ncard = 6 := by
    change (insert p (insert q (insert (f x) S))).ncard = 6
    rw [Set.ncard_insert_of_notMem,Set.ncard_insert_of_notMem,Set.ncard_insert_of_notMem,ns]
    · exact f_out x
    · simpa only [Set.mem_insert_iff,not_or] using And.intro (notQ x).symm noQS
    · simp only [Set.mem_insert_iff,not_or]
      exact ⟨pq,(notP x).symm,noPS⟩
  have two : ∃ a b : S, f a ≠ f b := by
    by_contra! single
    obtain ⟨u,hu⟩ := Set.nonempty_of_ncard_ne_zero (s := S) (by omega)
    let a : S := ⟨u,hu⟩
    let z := f a
    have zeq : S = G.neighborSet z := by
      refine Set.eq_of_subset_of_ncard_le ?_ ?_ (Set.toFinite _)
      · intro y hy
        have h := (edge ⟨y,hy⟩).symm
        exact (congrArg (fun v : V => G.Adj v y) (single ⟨y,hy⟩ a)).mp h
      · rw [regular,ns]
    have closed {x y : V} (hx : x ∈ D z) (adj : G.Adj x y) : y ∈ D z := by
      rcases (member z x).mp hx with rfl | rfl | rfl | port
      · exact (member z y).mpr (Or.inr (Or.inr (Or.inr adj)))
      · exact (member z y).mpr (Or.inr (Or.inr (Or.inr ((congrArg (fun s : Set V => y ∈ s) same).mp adj))))
      · exact (member z y).mpr (Or.inr (Or.inr (Or.inr (zeq.symm ▸ (show y ∈ G.neighborSet z from adj)))))
      · rcases nh ⟨x,port⟩ y adj with e | e | e
        · exact (member z y).mpr (Or.inl e)
        · exact (member z y).mpr (Or.inr (Or.inl e))
        · exact (member z y).mpr (Or.inr (Or.inr (Or.inl (e.trans (single _ a)))))
    have allmem (x : V) : x ∈ D z := by
      have path := (G.reachable_iff_reflTransGen p x).mp (hc.preconnected p x)
      induction path with
      | refl => exact (member _ _).mpr (Or.inl rfl)
      | tail _ adj ih => exact closed ih adj
    have eq := Set.eq_univ_of_forall allmem
    have n := six a
    change (D z).ncard = 6 at n
    rw [eq,Set.ncard_univ,Nat.card_eq_fintype_card] at n
    omega
  obtain ⟨a,b,ab⟩ := two
  let z := f a
  have pin : p ∈ D z := (member _ _).mpr (Or.inl rfl)
  have qin : q ∈ D z := (member _ _).mpr (Or.inr (Or.inl rfl))
  have zin : z ∈ D z := (member _ _).mpr (Or.inr (Or.inr (Or.inl rfl)))
  have incl : S ⊆ D z := fun x hx => (member _ _).mpr (Or.inr (Or.inr (Or.inr hx)))
  have qn : G.neighborSet q ⊆ D z := same.symm ▸ incl
  have pa : p ≠ (a : V) := (show G.Adj p a from a.2).ne
  have qa := (qe a).ne
  refine ⟨{ D := D z, p := p, a := a, b := b, z := z, w := f b, card := six a
            cut := bounded_twin_cut hd (D z) (six a) pin qin (incl a.2) zin incl qn pq noQS (edge a)
              pa (notP a).symm qa (notQ a).symm
            pin := pin, ain := incl a.2, bin := incl b.2, zin := zin, pb := b.2, az := edge a,
            pa := pa, pz := (notP a).symm, ba := fun h => ab (congrArg f (Subtype.ext h.symm))
            bz := fun h => f_out a ((congrArg (fun v : V => v ∈ S) h).mp b.2), noBA := triangle p b a b.2 a.2,
            noBZ := fun h => (nh b z h).elim (notP a) (fun h' => h'.elim (notQ a) ab)
            pN := incl, aN := ?_, bN := ?_ }⟩
  · intro y e
    rcases nh a y e with rfl | rfl | rfl <;> assumption
  · intro y e
    rcases nh b y e with rfl | rfl | rfl
    · exact Or.inl pin
    · exact Or.inl qin
    · exact Or.inr rfl

theorem residual_bound (hc : G.Connected) (hb : ∀ e ∈ G.edgeSet, ¬G.IsBridge e)
    (hd : ∀ x, G.degree x = 3) (hk : IsEmpty (G ≃g completeBipartiteGraph (Fin 3) (Fin 3)))
    (modulo : Fintype.card V % 4 = 2) (triangle : ∀ a b c, G.Adj a b → G.Adj a c → ¬G.Adj b c) :
    ∃ M : G.Subgraph, IsUniquelyRestricted M ∧ G.edgeFinset.card ≤ 6*M.edgeSet.ncard := by
  classical
  by_cases noK : ∀ x y : V, x ≠ y → (G.neighborSet x ∩ G.neighborSet y).ncard ≤ 2
  · exact unweighted_without_biclique hd noK
  push Not at noK
  obtain ⟨p,q,pq,three⟩ := noK
  have regular (x : V) : (G.neighborSet x).ncard = 3 := by
    rw [← Set.fintypeCard_eq_ncard,card_neighborSet_eq_degree,hd]
  have left := Set.eq_of_subset_of_ncard_le (show G.neighborSet p ∩ G.neighborSet q ⊆ G.neighborSet p from Set.inter_subset_left)
    (by rw [regular]; omega) (Set.toFinite _)
  have right := Set.eq_of_subset_of_ncard_le (show G.neighborSet p ∩ G.neighborSet q ⊆ G.neighborSet q from Set.inter_subset_right)
    (by rw [regular]; omega) (Set.toFinite _)
  have big := residual_order hc hd triangle modulo hk
  obtain ⟨C⟩ := region_from_twins hc hd triangle (by omega) pq (right.symm.trans left)
  exact use_six_region hc hd hb modulo C

end BridgePort

theorem OMA.solution : OMA.R_arxiv_1805_00840_R1.H1 := by
  intro V _ G _ hc hb hd hk modulo triangle
  exact BridgePort.residual_bound hc hb hd hk modulo triangle
