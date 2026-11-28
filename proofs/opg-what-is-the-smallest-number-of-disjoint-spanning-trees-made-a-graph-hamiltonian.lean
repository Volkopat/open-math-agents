import OMAStatements.S_opg_what_is_the_smallest_number_of_disjoint_spanning_trees_made_a_graph_hamiltonian
import Mathlib

namespace SpanningPacking

open OMA.S_opg_what_is_the_smallest_number_of_disjoint_spanning_trees_made_a_graph_hamiltonian

open SimpleGraph Finset
open scoped BigOperators

private abbrev PackingVertex (k : ℕ) := (Fin k × Bool) ⊕ (Fin k × Bool × Bool)

private def leftVertex {k : ℕ} (i : Fin k) (a : Bool) : PackingVertex k := Sum.inl (i,a)

private def rightVertex {k : ℕ} (i : Fin k) (b c : Bool) : PackingVertex k := Sum.inr (i,b,c)

private def onRightSide {k : ℕ} : PackingVertex k → Bool
  | .inl _ => false
  | .inr _ => true

private def packingParent {k : ℕ} (i : Fin k) : PackingVertex k → PackingVertex k
  | .inl (j,a) =>
      if j = i then
        if a then rightVertex i false false else leftVertex i false
      else rightVertex i (!a) false
  | .inr (j,b,_) => if j = i then leftVertex i false else leftVertex i b

private def packingDepth {k : ℕ} (i : Fin k) : PackingVertex k → ℕ
  | .inl (j,a) => if j = i ∧ a = false then 0 else 2
  | .inr (j,_,_) => if j = i then 1 else 3

private theorem parent_depth_lt {k : ℕ} (i : Fin k) {v : PackingVertex k}
    (hv : v ≠ leftVertex i false) : packingDepth i (packingParent i v) < packingDepth i v := by
  rcases v with ⟨j,a⟩ | ⟨j,b,c⟩
  · by_cases h : j = i
    · subst j
      cases a
      · exact (hv rfl).elim
      · simp [packingDepth,packingParent,rightVertex]
    · simp [packingDepth,packingParent,rightVertex,h]
  · by_cases h : j = i
    · subst j
      simp [packingDepth,packingParent,leftVertex]
    · cases b <;> simp [packingDepth,packingParent,leftVertex,h]

private def packingTree {k : ℕ} (i : Fin k) : SimpleGraph (PackingVertex k) :=
  SimpleGraph.fromRel (fun v w => v ≠ leftVertex i false ∧ packingParent i v = w)

private theorem parent_adjacent {k : ℕ} (i : Fin k) {v : PackingVertex k}
    (hv : v ≠ leftVertex i false) :
    (packingTree i).Adj v (packingParent i v) := by
  refine ⟨?_,Or.inl ⟨hv,rfl⟩⟩
  intro he
  have h := parent_depth_lt i hv
  rw [←he] at h
  exact (lt_irrefl _) h

private theorem packing_tree_connected {k : ℕ} (i : Fin k) : (packingTree i).Connected := by
  have reach (v : PackingVertex k) : (packingTree i).Reachable v (leftVertex i false) := by
    induction hD : packingDepth i v using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hv : v = leftVertex i false
      · subst v
        exact SimpleGraph.Reachable.refl _
      · have hLT := parent_depth_lt i hv
        rw [hD] at hLT
        exact (parent_adjacent i hv).reachable.trans (ih _ hLT _ rfl)
  let _ : Nonempty (PackingVertex k) := ⟨leftVertex i false⟩
  exact ⟨fun a b => (reach a).trans (reach b).symm⟩

private theorem parent_edge_iff {k : ℕ} (i : Fin k) (e : Sym2 (PackingVertex k)) :
    e ∈ (packingTree i).edgeSet ↔
      ∃ v, v ≠ leftVertex i false ∧ s(v,packingParent i v) = e := by
  induction e using Sym2.ind with
  | _ a b =>
    constructor
    · intro h
      have hAdj : (packingTree i).Adj a b := h
      rcases hAdj.2 with h | h
      · exact ⟨a,h.1,by rw [h.2]⟩
      · exact ⟨b,h.1,by rw [h.2,Sym2.eq_swap]⟩
    · rintro ⟨v,hv,hEq⟩
      rw [←hEq]
      exact parent_adjacent i hv

private theorem parent_edge_injective {k : ℕ} (i : Fin k) :
    Function.Injective (fun v : {v : PackingVertex k // v ≠ leftVertex i false} =>
      s(v.val,packingParent i v.val)) := by
  intro a b he
  apply Subtype.ext
  rcases Sym2.eq_iff.mp he with he | he
  · exact he.1
  · have hA := parent_depth_lt i a.property
    have hB := parent_depth_lt i b.property
    rw [←he.1,←he.2] at hB
    exact False.elim ((lt_asymm hA) hB)

private theorem parent_tree_card {k : ℕ} (i : Fin k) :
    Nat.card (packingTree i).edgeSet + 1 = Nat.card (PackingVertex k) := by
  classical
  let makeEdge (v : {v : PackingVertex k // v ≠ leftVertex i false}) : (packingTree i).edgeSet :=
    ⟨s(v.val,packingParent i v.val),(parent_edge_iff i _).mpr ⟨v.val,v.property,rfl⟩⟩
  have he : Function.Bijective makeEdge := by
    constructor
    · intro v w h
      exact parent_edge_injective i (congrArg Subtype.val h)
    · intro e
      obtain ⟨v,hv,heq⟩ := (parent_edge_iff i e.val).mp e.property
      exact ⟨⟨v,hv⟩,Subtype.ext heq⟩
  rw [←Nat.card_congr (Equiv.ofBijective makeEdge he), Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card]
  have hx : Fintype.card {v : PackingVertex k // v ≠ leftVertex i false} =
      Fintype.card (PackingVertex k) - 1 := by
    simp [Fintype.card_subtype_compl]
  rw [hx]
  have hPos : 0 < Fintype.card (PackingVertex k) := Fintype.card_pos_iff.mpr ⟨leftVertex i false⟩
  omega

private theorem packing_tree_isTree {k : ℕ} (i : Fin k) : (packingTree i).IsTree :=
  SimpleGraph.isTree_iff_connected_and_card.mpr ⟨packing_tree_connected i,parent_tree_card i⟩

private def crossEdgeOwner {k : ℕ} (a : Fin k × Bool) (b : Fin k × Bool × Bool) : Fin k :=
  if a.1 = b.1 then a.1 else if a.2 = b.2.1 then a.1 else b.1

private def edgeOwner {k : ℕ} : PackingVertex k → PackingVertex k → Option (Fin k)
  | .inl a,.inr b => some (crossEdgeOwner a b)
  | .inr b,.inl a => some (crossEdgeOwner a b)
  | _,_ => none

private theorem owner_symmetric {k : ℕ} (a b : PackingVertex k) : edgeOwner a b = edgeOwner b a := by
  cases a <;> cases b <;> rfl

private theorem parent_owner {k : ℕ} (i : Fin k) {v : PackingVertex k}
    (hv : v ≠ leftVertex i false) : edgeOwner v (packingParent i v) = some i := by
  rcases v with ⟨j,a⟩ | ⟨j,b,c⟩
  · by_cases h : j = i
    · subst j
      cases a
      · exact (hv rfl).elim
      · simp [edgeOwner,packingParent,rightVertex,crossEdgeOwner]
    · cases a <;> simp [edgeOwner,packingParent,rightVertex,crossEdgeOwner,h]
  · by_cases h : j = i
    · subst j
      simp [edgeOwner,packingParent,leftVertex,crossEdgeOwner]
    · simp [edgeOwner,packingParent,leftVertex,crossEdgeOwner,h,Ne.symm h]

private theorem packing_edge_owner {k : ℕ} {i : Fin k} {a b : PackingVertex k}
    (h : (packingTree i).Adj a b) : edgeOwner a b = some i := by
  rcases h.2 with h | h
  · rw [←h.2]
    exact parent_owner i h.1
  · rw [owner_symmetric,←h.2]
    exact parent_owner i h.1

private theorem packing_trees_disjoint {k : ℕ} {i j : Fin k} (hne : i ≠ j) :
    Disjoint (packingTree i) (packingTree j) := by
  apply SimpleGraph.disjoint_left.mpr
  intro a b hi hj
  exact hne (Option.some.inj ((packing_edge_owner hi).symm.trans (packing_edge_owner hj)))

private theorem tree_edges_cross {k : ℕ} {i : Fin k} {a b : PackingVertex k}
    (h : (packingTree i).Adj a b) : onRightSide a ≠ onRightSide b := by
  have hO := packing_edge_owner h
  cases a <;> cases b <;> simp [edgeOwner,onRightSide] at hO ⊢

private def cutWeights {V : Type} (side : V → Bool) : Sym2 V → ℝ :=
  Sym2.lift ⟨fun a b => if side a = side b then 2 else 1,by
    intro a b
    by_cases h : side a = side b
    · simp only [if_pos h,if_pos h.symm]
    · simp only [if_neg h,if_neg (Ne.symm h)]⟩

private theorem cost_bounded_below {V : Type} [Fintype V] (side : V → Bool)
    (G : SimpleGraph V) : (Nat.card G.edgeSet : ℝ) ≤ treeCost (cutWeights side) G := by
  classical
  rw [treeCost,Nat.card_eq_fintype_card,←SimpleGraph.edgeFinset_card]
  calc
    _ = ∑ e ∈ G.edgeFinset, (1 : ℝ) := by simp
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro e _
      refine Sym2.ind (fun a b => ?_) e
      unfold cutWeights
      rw [Sym2.lift_mk]
      change (1 : ℝ) ≤ if side a = side b then 2 else 1
      split <;> norm_num

private theorem cost_of_cross_edges {V : Type} [Fintype V] (side : V → Bool)
    (G : SimpleGraph V) (hSide : ∀ a b, G.Adj a b → side a ≠ side b) :
    treeCost (cutWeights side) G = Nat.card G.edgeSet := by
  classical
  rw [treeCost,Nat.card_eq_fintype_card,←SimpleGraph.edgeFinset_card]
  calc
    _ = ∑ e ∈ G.edgeFinset, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro e
      refine Sym2.ind (fun a b => ?_) e
      intro he
      have hAdj : G.Adj a b := SimpleGraph.mem_edgeFinset.mp he
      simp [cutWeights,Sym2.lift_mk,hSide a b hAdj]
    _ = _ := by simp

private theorem minimum_of_all_crossing {V : Type} [Fintype V] {k : ℕ}
    (side : V → Bool) (eligible : SimpleGraph V → Prop) (trees : Fin k → SimpleGraph V)
    (m : ℕ) (hCard : ∀ G, eligible G → Nat.card G.edgeSet = m)
    (hValid : ∀ i, eligible (trees i)) (hSeparate : ∀ i j, i ≠ j → Disjoint (trees i) (trees j))
    (hCross : ∀ i a b, (trees i).Adj a b → side a ≠ side b) :
    successiveMinimum (cutWeights side) eligible trees := by
  intro i
  refine ⟨hValid i,fun j hj => hSeparate i j hj.ne',?_⟩
  intro G hG _
  have hLower := cost_bounded_below side G
  rw [cost_of_cross_edges side (trees i) (hCross i),hCard _ (hValid i)]
  rw [hCard _ hG] at hLower
  exact hLower

private theorem all_tree_cards {V : Type} [Fintype V] (G : SimpleGraph V) (h : G.IsTree) :
    Nat.card G.edgeSet = Fintype.card V - 1 := by
  classical
  have hN := h.card_edgeFinset
  rw [SimpleGraph.edgeFinset_card,←Nat.card_eq_fintype_card] at hN
  omega

private theorem one_tree_cards {V : Type} [Fintype V] (root : V)
    (G : SimpleGraph V) (h : isOneTree root G) :
    Nat.card G.edgeSet = Fintype.card V := by
  classical
  have hN := h.1.card_edgeFinset
  rw [SimpleGraph.card_edgeFinset_induce_compl_singleton,
    SimpleGraph.card_edgeFinset_deleteIncidenceSet,h.2] at hN
  have hComplement : Fintype.card ↥({root}ᶜ : Set V) = Fintype.card V - 1 := by
    let e : ↥({root}ᶜ : Set V) ≃ {v : V // v ≠ root} :=
      Equiv.subtypeEquivRight (fun v => by simp)
    rw [Fintype.card_congr e]
    simp [Fintype.card_subtype_compl]
  rw [hComplement] at hN
  have hGe := G.degree_le_card_edgeFinset (v := root)
  rw [h.2] at hGe
  rw [Nat.card_eq_fintype_card,←SimpleGraph.edgeFinset_card]
  omega

private theorem alternating_walk_count {V : Type} {G : SimpleGraph V} (side : V → Bool)
    (hCross : ∀ a b, G.Adj a b → side a ≠ side b) {a b : V} (p : G.Walk a b) :
    p.support.countP side ≤ p.support.countP (fun v => !(side v)) +
      (if side a then 1 else 0) := by
  induction p with
  | nil =>
    cases ha : side _ <;> simp [Walk.support,ha]
  | @cons a b c hEdge tail ih =>
    have hNe := hCross a b hEdge
    cases ha : side a <;> cases hb : side b <;>
      simp [Walk.support,ha,hb] at hNe ih ⊢ <;> omega

private theorem hamiltonian_support_count {V : Type} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {a b : V} {p : G.Walk a b} (hp : walkSpanningPath p) (side : V → Bool) :
    p.support.countP side = (Finset.univ.filter (fun v => side v)).card := by
  rw [List.countP_eq_length_filter]
  rw [←List.toFinset_card_of_nodup (hp.1.support_nodup.filter _)]
  congr 1
  ext v
  simp [hp.2 v]

private theorem unbalanced_bipartition_no_path {V : Type} [Fintype V] (G : SimpleGraph V)
    (side : V → Bool) (hCross : ∀ a b, G.Adj a b → side a ≠ side b)
    (hTooMany : (Finset.univ.filter (fun v => !(side v))).card + 1 <
      (Finset.univ.filter (fun v => side v)).card) :
    ¬ hasHamiltonianPath G := by
  classical
  rintro ⟨a,b,p,hP⟩
  have h := alternating_walk_count side hCross p
  rw [hamiltonian_support_count hP side,
    hamiltonian_support_count hP (fun v => !(side v))] at h
  cases ha : side a <;> simp only [ha,Bool.false_eq_true,if_false,if_true] at h <;> omega

private theorem count_right_vertices (k : ℕ) :
    (Finset.univ.filter (fun v : PackingVertex k => onRightSide v)).card = 4*k := by
  classical
  let emb : (Fin k × Bool × Bool) ↪ PackingVertex k := ⟨Sum.inr,Sum.inr_injective⟩
  have h : Finset.univ.filter (fun v : PackingVertex k => onRightSide v) =
      (Finset.univ : Finset (Fin k × Bool × Bool)).map emb := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map]
    cases v <;> simp [onRightSide,emb,Function.Embedding.coeFn_mk]
  rw [h,Finset.card_map,Finset.card_univ,Fintype.card_prod,Fintype.card_prod,Fintype.card_fin,
    Fintype.card_bool]
  omega

private theorem count_left_vertices (k : ℕ) :
    (Finset.univ.filter (fun v : PackingVertex k => !(onRightSide v))).card = 2*k := by
  classical
  let emb : (Fin k × Bool) ↪ PackingVertex k := ⟨Sum.inl,Sum.inl_injective⟩
  have h : Finset.univ.filter (fun v : PackingVertex k => !(onRightSide v)) =
      (Finset.univ : Finset (Fin k × Bool)).map emb := by
    ext v
    cases v <;> simp [onRightSide,emb,Finset.mem_map]
  rw [h,Finset.card_map,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]
  omega


private def rootNeighbor {k : ℕ} (i : Fin k) (v : PackingVertex k) : Prop :=
  v = leftVertex i false ∨ v = leftVertex i true

private def oneTreeAdj {k : ℕ} (i : Fin k) : Option (PackingVertex k) → Option (PackingVertex k) → Prop
  | none,none => False
  | none,some v => rootNeighbor i v
  | some v,none => rootNeighbor i v
  | some a,some b => (packingTree i).Adj a b

private def packingOneTree {k : ℕ} (i : Fin k) : SimpleGraph (Option (PackingVertex k)) where
  Adj := oneTreeAdj i
  symm := by
    constructor
    intro a b h
    cases a <;> cases b
    · exact h
    · exact h
    · exact h
    · exact (packingTree i).adj_symm h
  loopless := by
    constructor
    intro a h
    cases a
    · exact h
    · exact (packingTree i).irrefl h

private theorem one_tree_induce {k : ℕ} (i : Fin k) :
    ((packingOneTree i).induce {none}ᶜ).IsTree := by
  let into : PackingVertex k → ↥({none}ᶜ : Set (Option (PackingVertex k))) :=
    fun v => ⟨some v,by simp⟩
  have hBijective : Function.Bijective into := by
    constructor
    · intro u v h
      exact Option.some.inj (congrArg Subtype.val h)
    · intro v
      cases hv : v.val with
      | none => exact (v.property (Set.mem_singleton_iff.mpr hv)).elim
      | some u => exact ⟨u,Subtype.ext hv.symm⟩
  let e : packingTree i ≃g (packingOneTree i).induce {none}ᶜ :=
    { Equiv.ofBijective into hBijective with map_rel_iff' := fun {_ _} => Iff.rfl }
  exact e.isTree_iff.mp (packing_tree_isTree i)

private theorem one_tree_is_eligible {k : ℕ} (i : Fin k) :
    isOneTree none (packingOneTree i) := by
  classical
  refine ⟨one_tree_induce i,?_⟩
  have h : (packingOneTree i).neighborFinset none =
      {some (leftVertex i false),some (leftVertex i true)} := by
    ext v
    rw [SimpleGraph.mem_neighborFinset]
    cases v <;> simp [packingOneTree,oneTreeAdj,rootNeighbor]
  rw [←SimpleGraph.card_neighborFinset_eq_degree,h]
  simp [leftVertex]

private theorem shared_root_neighbor {k : ℕ} {i j : Fin k} {v : PackingVertex k}
    (h : rootNeighbor i v) (h' : rootNeighbor j v) : i = j := by
  rcases h with h | h <;> rcases h' with h' | h' <;>
    exact congrArg Prod.fst (Sum.inl.inj (h.symm.trans h'))

private theorem one_trees_disjoint {k : ℕ} {i j : Fin k} (hne : i ≠ j) :
    Disjoint (packingOneTree i) (packingOneTree j) := by
  apply SimpleGraph.disjoint_left.mpr
  intro a b h h'
  cases a <;> cases b
  · exact h
  · exact hne (shared_root_neighbor h h')
  · exact hne (shared_root_neighbor h h')
  · exact SimpleGraph.disjoint_left.mp (packing_trees_disjoint hne) _ _ h h'

private def oneTreeSide {k : ℕ} : Option (PackingVertex k) → Bool
  | none => true
  | some v => onRightSide v

private theorem one_tree_edges_cross {k : ℕ} {i : Fin k} {a b : Option (PackingVertex k)}
    (h : (packingOneTree i).Adj a b) : oneTreeSide a ≠ oneTreeSide b := by
  cases a with
  | none =>
    cases b with
    | none => exact h.elim
    | some v =>
      change rootNeighbor i v at h
      rcases h with rfl | rfl <;> simp [oneTreeSide,onRightSide,leftVertex]
  | some u =>
    cases b with
    | none =>
      change rootNeighbor i u at h
      rcases h with rfl | rfl <;> simp [oneTreeSide,onRightSide,leftVertex]
    | some v => exact tree_edges_cross h

private theorem count_one_tree_sides (k : ℕ) :
    (Finset.univ.filter (fun v : Option (PackingVertex k) => !(oneTreeSide v))).card = 2*k ∧
    (Finset.univ.filter (fun v : Option (PackingVertex k) => oneTreeSide v)).card = 4*k+1 := by
  classical
  let emb : PackingVertex k ↪ Option (PackingVertex k) := ⟨some,fun _ _ => Option.some.inj⟩
  have hNone (p : PackingVertex k → Bool) : none ∉ (Finset.univ.filter (fun v => p v)).map emb := by
    rw [Finset.mem_map]
    rintro ⟨v,_,he⟩
    have he' : some v = none := he
    contradiction
  have hSome (p : PackingVertex k → Bool) (v : PackingVertex k) :
      some v ∈ (Finset.univ.filter (fun u => p u)).map emb ↔ p v = true := by
    rw [Finset.mem_map]
    constructor
    · rintro ⟨u,hu,he⟩
      have he' : some u = some v := he
      have heq := Option.some.inj he'
      subst u
      exact (Finset.mem_filter.mp hu).2
    · intro hv
      exact ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hv⟩,rfl⟩
  have hLeft : Finset.univ.filter (fun v : Option (PackingVertex k) => !(oneTreeSide v)) =
      (Finset.univ.filter (fun v : PackingVertex k => !(onRightSide v))).map emb := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    cases v with
    | none => simp [oneTreeSide]
    | some v => exact (hSome (fun u => !(onRightSide u)) v).symm
  have hRight : Finset.univ.filter (fun v : Option (PackingVertex k) => oneTreeSide v) =
      insert none ((Finset.univ.filter (fun v : PackingVertex k => onRightSide v)).map emb) := by
    ext v
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert]
    cases v with
    | none => simp [oneTreeSide]
    | some v => simpa only [Option.some_ne_none,false_or,oneTreeSide] using (hSome onRightSide v).symm
  have hMissing : none ∉ (Finset.univ.filter (fun v : PackingVertex k => onRightSide v)).map emb :=
    hNone onRightSide
  rw [hLeft,hRight,Finset.card_map,Finset.card_insert_of_notMem hMissing,Finset.card_map,
    count_left_vertices,count_right_vertices]
  exact ⟨rfl,rfl⟩

theorem packing_no_uniform_bound :
    noUniformSpanningTreePackingBound ∧ noUniformOneTreePackingBound := by
  classical
  constructor
  · intro k hk
    let G := ⨆ i : Fin k, packingTree i
    have hNo : ¬ hasHamiltonianPath G := by
      apply unbalanced_bipartition_no_path G onRightSide
      · intro a b h
        obtain ⟨i,hi⟩ := SimpleGraph.iSup_adj.mp h
        exact tree_edges_cross hi
      · rw [count_left_vertices,count_right_vertices]
        omega
    have hCost := minimum_of_all_crossing (k := k) onRightSide SimpleGraph.IsTree packingTree _
      all_tree_cards packing_tree_isTree (fun _ _ => packing_trees_disjoint)
      (fun _ _ _ => tree_edges_cross)
    refine ⟨PackingVertex k,inferInstance,cutWeights onRightSide,packingTree,hCost,hNo,?_⟩
    rintro ⟨a,b,p,hp,_⟩
    exact hNo ⟨a,b,p,hp⟩
  · intro k hk
    let G := ⨆ i : Fin k, packingOneTree i
    have hNo : ¬ hasHamiltonianPath G := by
      apply unbalanced_bipartition_no_path G oneTreeSide
      · intro a b h
        obtain ⟨i,hi⟩ := SimpleGraph.iSup_adj.mp h
        exact one_tree_edges_cross hi
      · obtain ⟨hL,hR⟩ := count_one_tree_sides k
        rw [hL,hR]
        omega
    have hNoCycle : ¬ hasHamiltonianCycle G := by
      rintro ⟨a,p,hp⟩
      exact hNo ⟨_,_,p.tail,hp.2⟩
    have hCost := minimum_of_all_crossing (k := k) oneTreeSide (isOneTree none) packingOneTree _
      (one_tree_cards none) one_tree_is_eligible (fun _ _ => one_trees_disjoint)
      (fun _ _ _ => one_tree_edges_cross)
    refine ⟨Option (PackingVertex k),inferInstance,none,cutWeights oneTreeSide,packingOneTree,hCost,hNoCycle,?_⟩
    rintro ⟨a,p,hp,_⟩
    exact hNoCycle ⟨a,p,hp⟩

end SpanningPacking

theorem OMA.solution : type_of% @OMA.S_opg_what_is_the_smallest_number_of_disjoint_spanning_trees_made_a_graph_hamiltonian.main := by
  exact SpanningPacking.packing_no_uniform_bound
