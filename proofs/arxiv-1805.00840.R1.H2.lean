import OMAReductions.R_arxiv_1805_00840_R1

-- Credit: @ryansolves

-- The two components of a bridge admit six compatible matchings.

namespace OMA.S_arxiv_1805_00840
open SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {A N : G.Subgraph} {u v : V}

/-- Restricting a matching to a set closed under taking partners preserves matching. -/
theorem matching_induce_closed (hN : N.IsMatching) {s : Set V} (hs : s ⊆ N.verts)
    (hc : ∀ {x y}, x ∈ s → N.Adj x y → y ∈ s) : (N.induce s).IsMatching := by
  intro x hx
  obtain ⟨y, hy, _⟩ := hN (hs hx)
  exact ⟨y, ⟨hx, hc hx hy, hy⟩, fun z hz => hN.eq_of_adj_left hz.2.2 hy⟩

/-- A matching already covering every vertex of a larger matching is maximal inside it. -/
theorem matching_eq_of_le_verts (hA : A.IsMatching) (hN : N.IsMatching)
    (hle : A ≤ N) (hv : N.verts = A.verts) : N = A := by
  apply le_antisymm _ hle
  refine ⟨hv.le, ?_⟩
  intro x y hxy
  obtain ⟨z, hz, _⟩ := hA (hv ▸ hxy.fst_mem)
  rwa [hN.eq_of_adj_left hxy (hle.2 hz)]

/-- If u cannot reach an old covered vertex, its new partner v is forced. -/
theorem uniquelyRestricted_add_forced (hA : IsUniquelyRestricted A) (e : G.Adj u v)
    (hu : u ∉ A.verts) (hv : v ∉ A.verts)
    (hfree : ∀ x ∈ A.verts, ¬G.Adj u x) :
    IsUniquelyRestricted (A ⊔ G.subgraphOfAdj e) := by
  have hd : Disjoint A.support (G.subgraphOfAdj e).support := by
    apply Set.disjoint_left.mpr
    intro x hx he
    have hxa := A.support_subset_verts hx
    have hxe := (G.subgraphOfAdj e).support_subset_verts he
    simp only [subgraphOfAdj_verts, Set.mem_insert_iff, Set.mem_singleton_iff] at hxe
    rcases hxe with rfl | rfl
    · exact hu hxa
    · exact hv hxa
  have hsup := hA.1.sup (Subgraph.IsMatching.subgraphOfAdj e) hd
  refine ⟨hsup, ?_⟩
  intro N hN hverts
  have memN (x : V) : x ∈ N.verts ↔ x ∈ A.verts ∨ x = u ∨ x = v := by
    rw [hverts]
    change x ∈ A.verts ∪ {u, v} ↔ _
    simp only [Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  obtain ⟨w, hw, _⟩ := hN ((memN u).2 (.inr (.inl rfl)))
  have forced : N.Adj u v := by
    rcases (memN w).1 hw.snd_mem with ha | rfl | rfl
    · exact (hfree w ha (N.adj_sub hw)).elim
    · exact (G.loopless.irrefl _ (N.adj_sub hw)).elim
    · exact hw
  have closed {x y : V} (hx : x ∈ A.verts) (hxy : N.Adj x y) : y ∈ A.verts := by
    rcases (memN y).1 hxy.snd_mem with h | rfl | rfl
    · exact h
    · exact (hv (hN.eq_of_adj_left hxy.symm forced ▸ hx)).elim
    · exact (hu (hN.eq_of_adj_left hxy.symm forced.symm ▸ hx)).elim
  have hres := matching_induce_closed hN (fun x hx => (memN x).2 (.inl hx)) @closed
  have heq := hA.2 (N.induce A.verts) hres rfl
  apply matching_eq_of_le_verts hsup hN _ hverts
  apply sup_le
  · refine ⟨fun x hx => (memN x).2 (.inl hx), ?_⟩
    intro x y ha
    have h : (N.induce A.verts).Adj x y := heq ▸ ha
    exact h.2.2
  · exact (subgraphOfAdj_le_iff e N).2 forced

end OMA.S_arxiv_1805_00840

namespace OMA.S_arxiv_1805_00840
open SimpleGraph
open scoped symmDiff

variable {V : Type*} {G : SimpleGraph V} {M N : G.Subgraph}

/-- The edges on which equal-support matchings disagree form a graph of cycles. -/
theorem equal_support_difference_cycles (hm : M.IsMatching) (hn : N.IsMatching)
    (hv : M.verts = N.verts) : (M.spanningCoe ∆ N.spanningCoe).IsCycles := by
  intro v
  by_cases h : v ∈ M.verts
  · obtain ⟨w, hw⟩ := hm h
    obtain ⟨z, hz⟩ := hn (hv ▸ h)
    simp only [symmDiff_def, Set.ncard_eq_two, ne_eq, imp_iff_not_or, Set.not_nonempty_iff_eq_empty,
      Set.eq_empty_iff_forall_notMem, mem_neighborSet, sup_adj, sdiff_adj,
      Subgraph.spanningCoe_adj, not_or, not_and, not_not]
    by_cases heq : w = z
    · simp_all [← imp_iff_not_or]
    · right
      exact ⟨w, z, heq, by ext y; simp; aesop⟩
  · rintro ⟨w, hw⟩
    change (M.spanningCoe ∆ N.spanningCoe).Adj v w at hw
    rcases hw with hw | hw
    · exact (h (M.edge_vert hw.1)).elim
    · exact (h (hv.symm ▸ N.edge_vert hw.1)).elim

/-- Membership of every bridge is forced by the set of vertices covered. -/
theorem matchings_agree_on_bridge [Finite V] (hm : M.IsMatching) (hn : N.IsMatching)
    (hv : M.verts = N.verts) {x y : V} (hb : G.IsBridge s(x,y)) : M.Adj x y ↔ N.Adj x y := by
  have hcyc := equal_support_difference_cycles hm hn hv
  have hsub : M.spanningCoe ∆ N.spanningCoe ≤ G :=
    symmDiff_le_sup.trans (sup_le M.spanningCoe_le N.spanningCoe_le)
  have hb' := hb.anti hsub
  have hnedge : ¬ (M.spanningCoe ∆ N.spanningCoe).Adj x y :=
    fun h => (isBridge_iff.mp hb') (hcyc.reachable_deleteEdges h)
  change ¬ ((M.Adj x y ∧ ¬N.Adj x y) ∨ (N.Adj x y ∧ ¬M.Adj x y)) at hnedge
  tauto

/-- Given internal uniquely restricted pieces covering all non-bridge matching edges,
    it suffices to check that edges leaving a piece either cross a bridge or reach
    a vertex already matched across a bridge. -/
theorem uniquelyRestricted_of_bridge_pieces [Finite V] {I : Type*} (P : I → G.Subgraph)
    (hm : M.IsMatching) (hp : ∀ i, IsUniquelyRestricted (P i)) (hle : ∀ i, P i ≤ M)
    (cover : ∀ {x y}, M.Adj x y → G.IsBridge s(x,y) ∨ ∃ i, (P i).Adj x y)
    (boundary : ∀ i, ∀ x ∈ (P i).verts, ∀ y ∈ M.verts, y ∉ (P i).verts → G.Adj x y →
      G.IsBridge s(x,y) ∨ ∃ z, M.Adj y z ∧ G.IsBridge s(y,z)) : IsUniquelyRestricted M := by
  classical
  refine ⟨hm, ?_⟩
  intro N hn hv
  have agree := @matchings_agree_on_bridge _ _ M N _ hm hn hv.symm
  have part (i : I) : P i ≤ N := by
    have sub : (P i).verts ⊆ N.verts := (hle i).1.trans hv.symm.le
    have closed {x y : V} (hx : x ∈ (P i).verts) (hxy : N.Adj x y) : y ∈ (P i).verts := by
      by_contra hy
      have bm := boundary i x hx y (hv ▸ hxy.snd_mem) hy (N.adj_sub hxy)
      have em : M.Adj x y := by
        rcases bm with hb | ⟨z, ez, hz⟩
        · exact (agree hb).2 hxy
        · have exz := hn.eq_of_adj_left hxy.symm ((agree hz).1 ez)
          exact exz ▸ ez.symm
      obtain ⟨z, ez, _⟩ := (hp i).1 hx
      exact hy (hm.eq_of_adj_left ((hle i).2 ez) em ▸ ez.snd_mem)
    have heq := (hp i).2 (N.induce (P i).verts) (matching_induce_closed hn sub @closed) rfl
    refine ⟨sub, fun x y h => ?_⟩
    have hh : (N.induce (P i).verts).Adj x y := heq ▸ h
    exact hh.2.2
  apply matching_eq_of_le_verts hm hn _ hv
  refine ⟨hv.symm.le, fun x y h => ?_⟩
  rcases cover h with hb | ⟨i, hi⟩
  · exact (agree hb).1 h
  · exact (part i).2 hi

end OMA.S_arxiv_1805_00840

namespace BridgeJoin
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {a b : V}

abbrev side (G : SimpleGraph V) (a b : V) : Set V :=
  ((G.deleteEdges {s(a,b)}).connectedComponentMk a).supp

structure CutSides (G : SimpleGraph V) (a b : V) where
  left : Set V
  right : Set V
  left_port : a ∈ left
  right_port : b ∈ right
  partition : ∀ x, x ∈ right ↔ x ∉ left
  cross : ∀ {x y}, x ∈ left → y ∈ right → G.Adj x y → x = a ∧ y = b

def CutSides.flip (C : CutSides G a b) : CutSides G b a where
  left := C.right
  right := C.left
  left_port := C.right_port
  right_port := C.left_port
  partition x := by
    classical
    rw [C.partition x]
    simp
  cross hx hy ed := ⟨(C.cross hy hx ed.symm).2,(C.cross hy hx ed.symm).1⟩

theorem complementary_sides (hc : G.Connected) (hb : G.IsBridge s(a,b)) :
    ∀ x, x ∈ side G b a ↔ x ∉ side G a b := by
  classical
  let H := G.deleteEdges {s(a,b)}
  have noPath : ¬ H.Reachable a b := isBridge_iff.mp hb
  have either (v : V) : H.Reachable a v ∨ H.Reachable b v := by
    have path := (G.reachable_iff_reflTransGen a v).1 (hc.preconnected a v)
    induction path with
    | refl => exact .inl (.refl _)
    | @tail x y _ ed ih =>
      by_cases h : s(x,y) = s(a,b)
      · rcases Sym2.eq_iff.mp h with ⟨_,rfl⟩ | ⟨_,rfl⟩
        · exact .inr (.refl _)
        · exact .inl (.refl _)
      · have step : H.Adj x y := deleteEdges_adj.mpr ⟨ed,h⟩
        exact ih.imp (fun p => p.trans step.reachable) (fun p => p.trans step.reachable)
  intro x
  rw [side, side, show s(b,a) = s(a,b) from Sym2.eq_swap]
  change H.connectedComponentMk x = H.connectedComponentMk b ↔
    ¬H.connectedComponentMk x = H.connectedComponentMk a
  rw [ConnectedComponent.eq, ConnectedComponent.eq]
  constructor
  · intro hxb hxa
    exact noPath (hxa.symm.trans hxb)
  · intro hn
    exact ((either x).resolve_left (fun h => hn h.symm)).symm

def cutAt (hc : G.Connected) (hb : G.IsBridge s(a,b)) : CutSides G a b where
  left := side G a b
  right := side G b a
  left_port := rfl
  right_port := rfl
  partition := complementary_sides hc hb
  cross := by
    intro x y hx hy ed
    by_contra hn
    have dne : s(x,y) ≠ s(a,b) := by
      intro h
      rcases Sym2.eq_iff.mp h with hp | ⟨rfl,rfl⟩
      · exact hn hp
      · exact ((complementary_sides hc hb _) |>.mp (show _ ∈ side G _ _ from rfl)) hx
    have hadj : (G.deleteEdges {s(a,b)}).Adj x y := deleteEdges_adj.mpr ⟨ed,dne⟩
    exact ((complementary_sides hc hb y).mp hy)
      (((G.deleteEdges {s(a,b)}).connectedComponentMk a).mem_supp_of_adj_mem_supp hx hadj)

theorem side_connected (x y : V) : (G.induce (side G x y)).Connected := by
  let H := G.deleteEdges {s(x,y)}
  let c := H.connectedComponentMk x
  apply c.connected_toSimpleGraph.mono
  intro v w h
  exact (deleteEdges_le _ : H ≤ G) h

theorem side_smaller [Fintype V] (C : CutSides G a b) [Fintype C.left] :
    Fintype.card C.left < Fintype.card V := Fintype.card_subtype_lt ((C.partition b).mp C.right_port)

end BridgeJoin

namespace BridgeJoin
open SimpleGraph OMA.S_arxiv_1805_00840
variable {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

theorem ur_map (f : G ↪g H) (M : G.Subgraph) (hM : IsUniquelyRestricted M) :
    IsUniquelyRestricted (M.map f.toHom) := by
  classical
  have match' := hM.1.map f.toHom f.injective
  refine ⟨match', ?_⟩
  intro N hn hv
  have pullV : (N.comap f.toHom).verts = M.verts := by
    change (⇑f) ⁻¹' N.verts = M.verts
    rw [hv]
    exact Set.preimage_image_eq _ f.injective
  have pullM : (N.comap f.toHom).IsMatching := by
    intro v hv'
    obtain ⟨y,hy,_⟩ := hn hv'
    obtain ⟨w,_,hw⟩ := hv.le hy.snd_mem
    have e : N.Adj (f v) (f w) := hw ▸ hy
    exact ⟨w,⟨f.map_rel_iff.mp (N.adj_sub e),e⟩,
      fun z hz => f.injective (hn.eq_of_adj_left hz.2 e)⟩
  have eq := hM.2 _ pullM pullV
  exact matching_eq_of_le_verts match' hn ((Subgraph.map_le_iff_le_comap ..).mpr eq.ge) hv

theorem ur_sup_separated [Finite W] {A B : H.Subgraph}
    (ha : IsUniquelyRestricted A) (hb : IsUniquelyRestricted B) (hd : Disjoint A.verts B.verts)
    (cross : ∀ x ∈ A.verts, ∀ y ∈ B.verts, H.Adj x y → H.IsBridge s(x,y)) :
    IsUniquelyRestricted (A ⊔ B) := by
  let pieces (i : Bool) := if i then B else A
  apply uniquelyRestricted_of_bridge_pieces pieces
    (ha.1.sup hb.1 (hd.mono A.support_subset_verts B.support_subset_verts))
  · rintro (_|_) <;> simp [pieces,ha,hb]
  · rintro (_|_) <;> simp [pieces]
  · intro x y h
    rcases h with h | h
    · exact .inr ⟨false,h⟩
    · exact .inr ⟨true,h⟩
  · intro i x hx y hy hout he
    left
    cases i with
    | false => exact cross x hx y (hy.resolve_left hout) he
    | true =>
      rw [Sym2.eq_swap]
      exact cross y (hy.resolve_right hout) x hx he.symm

theorem ur_insert_bridge [Finite W] (M : H.Subgraph) (hm : IsUniquelyRestricted M)
    {a b : W} (e : H.Adj a b) (hb : H.IsBridge s(a,b))
    (ha : a ∉ M.verts) (hy : b ∉ M.verts) : IsUniquelyRestricted (M ⊔ H.subgraphOfAdj e) := by
  let E := H.subgraphOfAdj e
  have d : Disjoint M.verts E.verts := by
    apply Set.disjoint_left.mpr
    intro z h hz
    rcases (show z = a ∨ z = b from hz) with rfl | rfl <;> contradiction
  have hmatch := hm.1.sup (Subgraph.IsMatching.subgraphOfAdj e)
    (d.mono M.support_subset_verts E.support_subset_verts)
  apply uniquelyRestricted_of_bridge_pieces (fun _ : Unit => M) hmatch (fun _ => hm) (fun _ => le_sup_left)
  · intro x y h
    rcases h with h | h
    · exact .inr ⟨(),h⟩
    · exact .inl ((show s(a,b) = s(x,y) from h) ▸ hb)
  · intro _ x hx y hv hout _
    right
    rcases (show y = a ∨ y = b from hv.resolve_left hout) with rfl | rfl
    · exact ⟨b,.inr (subgraphOfAdj_adj_self e),hb⟩
    · exact ⟨a,.inr (subgraphOfAdj_adj_self e).symm,Sym2.eq_swap ▸ hb⟩

end BridgeJoin

namespace BridgeJoin
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {a b : V}

theorem bridge_induce (S : Set V) (x y : S) (hb : G.IsBridge s(x.1,y.1)) :
    (G.induce S).IsBridge s(x,y) := by
  let lift' : (G.induce S).deleteEdges {s(x,y)} →g G.deleteEdges {s(x.1,y.1)} :=
    { toFun := Subtype.val
      map_rel' := by
        intro u v e
        obtain ⟨edge,avoid⟩ := deleteEdges_adj.mp e
        apply deleteEdges_adj.mpr
        refine ⟨edge,fun eq => avoid ?_⟩
        exact Set.mem_singleton_iff.mpr
          (Sym2.map.injective Subtype.val_injective (Set.mem_singleton_iff.mp eq)) }
  exact isBridge_iff.mpr (fun path => isBridge_iff.mp hb (path.map lift'))

def counted {W : Type*} (K : SimpleGraph W) (bridgesOnly : Bool) : Set (Sym2 W) :=
  { e ∈ K.edgeSet | bridgesOnly = true → K.IsBridge e }

theorem count_sides [Finite V] (C : CutSides G a b) (k : Bool) :
    (counted G k).ncard ≤ (counted (G.induce C.left) k).ncard +
      (counted (G.induce C.right) k).ncard + 1 := by
  classical
  let inside (s : Set V) := Sym2.map (Subtype.val : s → V) '' counted (G.induce s) k
  have same {x y : V} (S : Set V) (hx : x ∈ S) (hy : y ∈ S) (h : s(x,y) ∈ counted G k) :
      s(x,y) ∈ inside S := by
    let u : S := ⟨x,hx⟩
    let v : S := ⟨y,hy⟩
    exact ⟨s(u,v),⟨h.1,fun eq => bridge_induce S u v (h.2 eq)⟩,rfl⟩
  have sub : counted G k ⊆ insert s(a,b) (inside C.left ∪ inside C.right) := by
    rintro e he
    induction e using Sym2.inductionOn with
    | _ x y =>
      by_cases hx : x ∈ C.left <;> by_cases hy : y ∈ C.left
      · exact .inr (.inl (same _ hx hy he))
      · obtain ⟨rfl,rfl⟩ := C.cross hx ((C.partition y).2 hy) he.1
        exact .inl rfl
      · obtain ⟨rfl,rfl⟩ := C.cross hy ((C.partition x).2 hx) (show G.Adj x y from he.1).symm
        exact .inl Sym2.eq_swap
      · exact .inr (.inr (same _ ((C.partition x).2 hx) ((C.partition y).2 hy) he))
  have h₁ := Set.ncard_le_ncard sub
  have h₂ := Set.ncard_insert_le s(a,b) (inside C.left ∪ inside C.right)
  have h₃ := Set.ncard_union_le (inside C.left) (inside C.right)
  have h₄ (s : Set V) : (inside s).ncard ≤ (counted (G.induce s) k).ncard := Set.ncard_image_le
  have := h₄ C.left
  have := h₄ C.right
  omega

theorem total_cost [Fintype V] [DecidableRel G.Adj] (C : CutSides G a b)
    [Fintype C.left] [Fintype C.right] :
    G.edgeFinset.card + {e ∈ G.edgeSet | G.IsBridge e}.ncard ≤
      ((G.induce C.left).edgeFinset.card +
        {e ∈ (G.induce C.left).edgeSet | (G.induce C.left).IsBridge e}.ncard) +
      ((G.induce C.right).edgeFinset.card +
        {e ∈ (G.induce C.right).edgeSet | (G.induce C.right).IsBridge e}.ncard) + 2 := by
  classical
  have e := count_sides C false
  have b := count_sides C true
  simp only [counted,Bool.false_eq_true,false_implies,and_true,Set.setOf_mem_eq] at e
  simp only [counted,forall_const] at b
  simp only [edgeFinset_card,Set.fintypeCard_eq_ncard]
  omega

end BridgeJoin

namespace BridgeJoin
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V} (C : CutSides G a b) [Fintype C.left]

theorem side_degree (e : G.Adj a b) (x : C.left) :
    (G.induce C.left).degree x + (if x.1 = a then 1 else 0) ≤ G.degree x.1 := by
  classical
  let inc (y : (G.induce C.left).neighborSet x) : G.neighborSet x.1 := ⟨y.1.1,y.2⟩
  have inj : Function.Injective inc := fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun y : G.neighborSet x.1 => y.1) h))
  rw [← card_neighborSet_eq_degree, ← card_neighborSet_eq_degree]
  split
  · rename_i hx
    let z : G.neighborSet x.1 := ⟨b,by change G.Adj x.1 b; rw [hx]; exact e⟩
    have miss : z ∉ Set.range inc := by
      rintro ⟨y,hy⟩
      have eq : y.1.1 = b := congrArg Subtype.val hy
      apply (C.partition b).mp C.right_port
      exact (congrArg (fun v => v ∈ C.left) eq).mp y.1.2
    exact Fintype.card_lt_of_injective_of_notMem inc inj miss
  · simpa using Fintype.card_le_of_injective inc inj

theorem side_not_K33 (e : G.Adj a b) (hd : ∀ x, G.degree x ≤ 3) :
    IsEmpty ((G.induce C.left) ≃g completeBipartiteGraph (Fin 3) (Fin 3)) := by
  constructor
  intro f
  letI : DecidableRel (completeBipartiteGraph (Fin 3) (Fin 3)).Adj := fun u v => by
    unfold completeBipartiteGraph
    infer_instance
  let x : C.left := ⟨a,C.left_port⟩
  have strict := side_degree C e x
  have d := hd a
  have h3 : ∀ z, (completeBipartiteGraph (Fin 3) (Fin 3)).degree z = 3 := by decide
  have eq := (f.degree_eq x).symm.trans (h3 (f x))
  change (G.induce C.left).degree x + (if a = a then 1 else 0) ≤ G.degree a at strict
  rw [if_pos rfl] at strict
  exact (by omega : False)

end BridgeJoin

namespace BridgeJoin
open SimpleGraph OMA.S_arxiv_1805_00840
variable {V : Type*} [Finite V] {G : SimpleGraph V} {a b : V}

abbrev liftSide {s : Set V} (M : (G.induce s).Subgraph) : G.Subgraph :=
  M.map (Embedding.induce s).toHom

theorem lift_in_side {s : Set V} (M : (G.induce s).Subgraph) : (liftSide M).verts ⊆ s := by
  rintro x ⟨y,_,rfl⟩
  exact y.2

theorem lift_mem {s : Set V} (M : (G.induce s).Subgraph) (x : s) :
    x.1 ∈ (liftSide M).verts ↔ x ∈ M.verts := by
  constructor
  · rintro ⟨y,hy,he⟩
    exact (Subtype.ext he : y = x) ▸ hy
  · intro h
    exact ⟨x,h,rfl⟩

theorem lift_size {s : Set V} (M : (G.induce s).Subgraph) :
    (liftSide M).edgeSet.ncard = M.edgeSet.ncard := by
  rw [Subgraph.edgeSet_map]
  exact Set.ncard_image_of_injective _ (Sym2.map.injective (Embedding.induce (G := G) s).injective)

theorem sup_size (A B : G.Subgraph) (hd : Disjoint A.verts B.verts) :
    (A ⊔ B).edgeSet.ncard = A.edgeSet.ncard + B.edgeSet.ncard := by
  rw [Subgraph.edgeSet_sup]
  refine Set.ncard_union_eq ?_ (Set.toFinite _) (Set.toFinite _)
  apply Set.disjoint_left.mpr
  intro e ea eb
  obtain ⟨x,y⟩ := e
  exact Set.disjoint_left.mp hd (A.edge_vert ea) (B.edge_vert eb)

def joinSlot (e : G.Adj a b) (A B : G.Subgraph) (mark : Prop) [Decidable mark] :=
  if mark then (A ⊔ B) ⊔ G.subgraphOfAdj e else A ⊔ B

theorem join_slot_result (C : CutSides G a b) (e : G.Adj a b) (hb : G.IsBridge s(a,b))
    (A : (G.induce C.left).Subgraph) (B : (G.induce C.right).Subgraph)
    (ha : IsUniquelyRestricted A) (hy : IsUniquelyRestricted B)
    (mark : Prop) [Decidable mark]
    (hfree : mark → ⟨a,C.left_port⟩ ∉ A.verts ∧ ⟨b,C.right_port⟩ ∉ B.verts) :
    let M := joinSlot e (liftSide A) (liftSide B) mark
    IsUniquelyRestricted M ∧ M.edgeSet.ncard = A.edgeSet.ncard + B.edgeSet.ncard + (if mark then 1 else 0) := by
  classical
  let X := liftSide A
  let Y := liftSide B
  have dx : Disjoint X.verts Y.verts := Set.disjoint_left.mpr
    (fun x hx hy => (C.partition x).mp (lift_in_side B hy) (lift_in_side A hx))
  have base : IsUniquelyRestricted (X ⊔ Y) := by
    apply ur_sup_separated (ur_map _ _ ha) (ur_map _ _ hy) dx
    intro x hx y hy' h
    obtain ⟨rfl,rfl⟩ := C.cross (lift_in_side A hx) (lift_in_side B hy') h
    exact hb
  have size : (X ⊔ Y).edgeSet.ncard = A.edgeSet.ncard + B.edgeSet.ncard := by
    rw [sup_size X Y dx, lift_size, lift_size]
  by_cases flag : mark
  · obtain ⟨fa,fb⟩ := hfree flag
    have aout : a ∉ (X ⊔ Y).verts := by
      rintro (ha'|hy')
      · exact fa ((lift_mem A ⟨a,C.left_port⟩).1 ha')
      · exact (C.partition a).mp (lift_in_side B hy') C.left_port
    have bout : b ∉ (X ⊔ Y).verts := by
      rintro (ha'|hy')
      · exact (C.partition b).mp C.right_port (lift_in_side A ha')
      · exact fb ((lift_mem B ⟨b,C.right_port⟩).1 hy')
    have dis : Disjoint (X ⊔ Y).verts (G.subgraphOfAdj e).verts := by
      apply Set.disjoint_left.mpr
      intro z h hz
      rcases (show z = a ∨ z = b from hz) with rfl | rfl <;> contradiction
    simp only [joinSlot,if_pos flag]
    refine ⟨ur_insert_bridge _ base e hb aout bout, ?_⟩
    rw [sup_size _ _ dis, size, edgeSet_subgraphOfAdj, Set.ncard_singleton]
  · simpa only [joinSlot,if_neg flag,add_zero] using And.intro base size

theorem free_left (C : CutSides G a b) (e : G.Adj a b)
    (A : (G.induce C.left).Subgraph) (B : (G.induce C.right).Subgraph)
    (mark : Prop) [Decidable mark] (x : C.left) (free : x ∉ A.verts) (h : x.1 ≠ a ∨ ¬mark) :
    x.1 ∉ (joinSlot e (liftSide A) (liftSide B) mark).verts := by
  have base : x.1 ∉ (liftSide A ⊔ liftSide B).verts :=
    fun hx => hx.elim (fun ha => free ((lift_mem A x).1 ha)) (fun hb => (C.partition _).mp (lift_in_side B hb) x.2)
  by_cases hm : mark
  · simp only [joinSlot,if_pos hm]
    rintro (hx|he)
    · exact base hx
    · rcases (show x.1 = a ∨ x.1 = b from he) with eq | eq
      · exact (h.resolve_right (not_not.mpr hm)) eq
      · exact ((C.partition b).mp C.right_port) ((congrArg (fun z => z ∈ C.left) eq).mp x.2)
  · simpa only [joinSlot,if_neg hm] using base

theorem free_right (C : CutSides G a b) (e : G.Adj a b)
    (A : (G.induce C.left).Subgraph) (B : (G.induce C.right).Subgraph)
    (mark : Prop) [Decidable mark] (x : C.right) (free : x ∉ B.verts) (h : x.1 ≠ b ∨ ¬mark) :
    x.1 ∉ (joinSlot e (liftSide A) (liftSide B) mark).verts := by
  have hf := free_left C.flip e.symm B A mark x free h
  change x.1 ∉ (joinSlot e.symm (liftSide B) (liftSide A) mark).verts at hf
  simpa only [joinSlot, subgraphOfAdj_symm e, sup_comm (liftSide B) (liftSide A)] using hf

end BridgeJoin

namespace BridgeJoin

theorem marks_for (L R : Set (Fin 6)) (hl : 2 ≤ L.ncard) (hr : 2 ≤ R.ncard) :
    ∃ (K : Finset (Fin 6)) (σ : Equiv.Perm (Fin 6)), K.card = 2 ∧
      ∀ j ∈ K, j ∈ L ∧ σ j ∈ R := by
  classical
  obtain ⟨A,ha,na⟩ := Set.exists_subset_card_eq hl
  obtain ⟨B,hb,nb⟩ := Set.exists_subset_card_eq hr
  rw [Set.ncard_eq_toFinset_card'] at na nb
  obtain ⟨σ,hσ⟩ := Equiv.Perm.exists_map_finset_eq A.toFinset B.toFinset (na.trans nb.symm)
  refine ⟨A.toFinset,σ,na,fun j hj => ⟨ha (Set.mem_toFinset.mp hj),hb ?_⟩⟩
  apply Set.mem_toFinset.mp
  rw [← hσ]
  exact Finset.mem_map.mpr ⟨j,hj,rfl⟩

theorem slot_budget (F F' : Set (Fin 6)) (K : Finset (Fin 6)) (port : Prop) [Decidable port]
    (d : ℕ) (hk : K.card = 2) (before : 2 * (d + if port then 1 else 0) ≤ F.ncard)
    (keep : ∀ j ∈ F, (¬port ∨ j ∉ K) → j ∈ F') : 2*d ≤ F'.ncard := by
  classical
  by_cases hp : port
  · have sub : F ⊆ F' ∪ (K : Set (Fin 6)) := by
      intro j hj
      by_cases hm : j ∈ K
      · exact Or.inr hm
      · exact Or.inl (keep j hj (Or.inr hm))
    have bound := (Set.ncard_le_ncard sub).trans (Set.ncard_union_le _ _)
    rw [Set.ncard_coe_finset,hk] at bound
    rw [if_pos hp] at before
    omega
  · have sub : F ⊆ F' := fun j hj => keep j hj (Or.inl hp)
    simpa [hp] using before.trans (Set.ncard_le_ncard sub)

theorem reindex_size (σ : Equiv.Perm (Fin 6)) (F : Set (Fin 6)) :
    (σ ⁻¹' F).ncard = F.ncard :=
  Set.ncard_preimage_of_injective_subset_range σ.injective (by simp [σ.surjective.range_eq])

theorem sum_marks (K : Finset (Fin 6)) : (∑ j : Fin 6, if j ∈ K then 1 else 0) = K.card := by
  classical
  rw [← Finset.sum_filter]
  simp

end BridgeJoin

namespace BridgeJoin
open SimpleGraph OMA.S_arxiv_1805_00840
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

def Certificate (G : SimpleGraph V) [DecidableRel G.Adj] (t : V → ℕ) : Prop :=
  ∃ M : Fin 6 → G.Subgraph, (∀ j, IsUniquelyRestricted (M j)) ∧
    G.edgeFinset.card + {f ∈ G.edgeSet | G.IsBridge f}.ncard ≤ ∑ j, (M j).edgeSet.ncard ∧
    ∀ x, 2 * t x ≤ {j : Fin 6 | x ∉ (M j).verts}.ncard

theorem glue {a b : V} [DecidableEq V] (C : CutSides G a b) (e : G.Adj a b)
    (hb : G.IsBridge s(a,b)) [Fintype C.left] [Fintype C.right] (t : V → ℕ)
    (hl : Certificate (G.induce C.left) (fun x => t x.1 + if x.1 = a then 1 else 0))
    (hr : Certificate (G.induce C.right) (fun x => t x.1 + if x.1 = b then 1 else 0)) :
    Certificate G t := by
  classical
  obtain ⟨L,hL,nL,fL⟩ := hl
  obtain ⟨R,hR,nR,fR⟩ := hr
  let u : C.left := ⟨a,C.left_port⟩
  let v : C.right := ⟨b,C.right_port⟩
  have atL := fL u
  have atR := fR v
  simp only [u,v,ite_true] at atL atR
  obtain ⟨K,σ,nK,hK⟩ := marks_for {j | u ∉ (L j).verts} {j | v ∉ (R j).verts}
    (by dsimp [u] at *; omega) (by dsimp [v] at *; omega)
  let M (j : Fin 6) := joinSlot e (liftSide (L j)) (liftSide (R (σ j))) (j ∈ K)
  have each (j : Fin 6) := join_slot_result C e hb (L j) (R (σ j)) (hL j) (hR (σ j))
    (j ∈ K) (hK j)
  refine ⟨M,fun j => (each j).1,?_,?_⟩
  · calc
      _ ≤ _ := total_cost C
      _ ≤ (∑ j, (L j).edgeSet.ncard) + (∑ j, (R j).edgeSet.ncard) + 2 := by omega
      _ = ∑ j, (M j).edgeSet.ncard := by
        simp_rw [show ∀ j, (M j).edgeSet.ncard = _ from fun j => (each j).2]
        rw [Finset.sum_add_distrib,Finset.sum_add_distrib,sum_marks,nK]
        rw [Equiv.sum_comp σ (fun j => (R j).edgeSet.ncard)]
  · intro x
    by_cases inside : x ∈ C.left
    · let w : C.left := ⟨x,inside⟩
      exact slot_budget {j | w ∉ (L j).verts} _ K (x = a) (t x) nK (fL w)
        (fun j hj h => free_left C e (L j) (R (σ j)) (j ∈ K) w hj h)
    · let w : C.right := ⟨x,(C.partition x).mpr inside⟩
      let F : Set (Fin 6) := {j | w ∉ (R j).verts}
      apply slot_budget (σ ⁻¹' F) _ K (x = b) (t x) nK
      · rw [reindex_size]
        exact fR w
      · exact fun j hj h => free_right C e (L j) (R (σ j)) (j ∈ K) w hj h

end BridgeJoin

namespace BridgeJoin
open SimpleGraph OMA.S_arxiv_1805_00840
variable {V : Type} [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj]

def ComponentOracle (G : SimpleGraph V) (e : Sym2 V) : Prop :=
  ∀ c : (G.deleteEdges {e}).ConnectedComponent,
    let B := G.induce c.supp
    ∀ [Fintype c.supp] [DecidableRel B.Adj], Fintype.card c.supp < Fintype.card V →
    B.Connected → (∀ x, B.degree x ≤ 3) →
    IsEmpty (B ≃g completeBipartiteGraph (Fin 3) (Fin 3)) →
    ∀ t : c.supp → ℕ, (∀ x, B.degree x + t x ≤ 3) → Certificate B t

theorem local_certificate {a b : V} [DecidableEq V] (hc : G.Connected) (hd : ∀ x, G.degree x ≤ 3)
    (e : G.Adj a b) (hb : G.IsBridge s(a,b)) (oracle : ComponentOracle G s(a,b))
    [Fintype (side G a b)] (t : V → ℕ) (ht : ∀ x, G.degree x + t x ≤ 3) :
    Certificate (G.induce (side G a b)) (fun x => t x.1 + if x.1 = a then 1 else 0) := by
  let C := cutAt hc hb
  let c := (G.deleteEdges {s(a,b)}).connectedComponentMk a
  letI : Fintype C.left := ‹Fintype (side G a b)›
  letI : Fintype c.supp := ‹Fintype (side G a b)›
  have deg := side_degree C e
  have fit (x : C.left) : (G.induce C.left).degree x + (t x.1 + if x.1 = a then 1 else 0) ≤ 3 := by
    have h := deg x
    have d := ht x.1
    omega
  have bound (x : C.left) : (G.induce C.left).degree x ≤ 3 := by
    have h := deg x
    have d := hd x.1
    omega
  exact oracle c (side_smaller C) (side_connected a b) bound (side_not_K33 C e hd) _ fit

set_option maxHeartbeats 1600000 in
theorem gluing_step : OMA.R_arxiv_1805_00840_R1.H2 := by
  intro V _ G _ hc hd _ pair
  induction pair using Sym2.inductionOn with
  | _ a b =>
    intro e hb oracle t ht
    classical
    have rev : s(b,a) = s(a,b) := Sym2.eq_swap
    have rb : G.IsBridge s(b,a) := rev.symm ▸ hb
    have ro : ComponentOracle G s(b,a) := (congrArg (ComponentOracle G) rev).mpr oracle
    change ComponentOracle G s(a,b) at oracle
    change Certificate G t
    let C := cutAt hc hb
    letI : Fintype (side G a b) := Fintype.ofFinite _
    letI : Fintype (side G b a) := Fintype.ofFinite _
    letI : Fintype C.left := ‹Fintype (side G a b)›
    letI : Fintype C.right := ‹Fintype (side G b a)›
    apply glue C e hb t
    · exact local_certificate hc hd e hb oracle t ht
    · exact local_certificate hc hd e.symm rb ro t ht

end BridgeJoin

theorem OMA.solution : OMA.R_arxiv_1805_00840_R1.H2 := BridgeJoin.gluing_step
