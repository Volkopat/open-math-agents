import OMAStatements.S_opg_every_prism_over_a_3_connected_planar_graph_is_hamiltonian
import Mathlib

/-!
An explicit disproof of prism Hamiltonicity for 3-connected planar graphs.
The graph is Špacapan's construction in Theorem 2.6 of
*A counterexample to prism-hamiltonicity of 3-connected planar graphs*
(arXiv:1906.06683, doi:10.1016/j.jctb.2020.09.012).
The connectivity routes, straight-line drawing and finite obstruction
certificates are checked by the Lean kernel.
-/


namespace PrismCounterexample

open SimpleGraph

abbrev Local := Fin 39
abbrev Line := Fin 989
abbrev Vertex := Fin 2 ⊕ Line
abbrev PairVertex := Fin 77

def hub (h : Fin 2) : Vertex := .inl h

def block (i : Fin 26) (j : Local) : Line :=
  ⟨38 * i.val + j.val, by omega⟩

def atBlock (i : Fin 26) (j : Local) : Vertex := .inr (block i j)

def jSide : List (Local × Local) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0),
   (3, 5), (5, 6), (6, 7), (7, 8), (8, 3),
   (4, 17), (7, 17), (8, 17)]

def upJ (j : Local) : Local :=
  if 1 ≤ j.val ∧ j.val ≤ 8 then j + 8 else j

def reflectJ (j : Local) : Local := 34 - j

def jEdges : List (Local × Local) :=
  jSide ++ jSide.map fun (u, v) => (upJ u, upJ v)

def localEdges : List (Local × Local) :=
  jEdges ++ (jEdges.map fun (u, v) => (reflectJ u, reflectJ v)) ++
    [(34, 35), (35, 38), (38, 37), (37, 36), (36, 34)]

def upper : List Local := [0, 9, 10, 11, 13, 14, 15, 17, 19, 20, 21, 23, 24, 25, 34, 35, 38]

def lower : List Local := [0, 1, 2, 3, 5, 6, 7, 17, 27, 28, 29, 31, 32, 33, 34, 36, 37, 38]

def graphOfEdges {V : Type} (edges : List (V × V)) : SimpleGraph V where
  Adj u v := u ≠ v ∧ ((u, v) ∈ edges ∨ (v, u) ∈ edges)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance graphOfEdgesDecidable {V : Type} [DecidableEq V] (edges : List (V × V)) :
    DecidableRel (graphOfEdges edges).Adj := fun u v =>
  inferInstanceAs (Decidable (u ≠ v ∧ ((u, v) ∈ edges ∨ (v, u) ∈ edges)))

def localG : SimpleGraph Local := graphOfEdges localEdges

instance : DecidableRel localG.Adj := graphOfEdgesDecidable _

def edgesAt (i : Fin 26) : List (Vertex × Vertex) :=
  (localEdges.map fun (u, v) => (atBlock i u, atBlock i v)) ++
  (upper.map fun j => (hub 0, atBlock i j)) ++
  (lower.map fun j => (hub 1, atBlock i j))

def allEdges : List (Vertex × Vertex) := (List.finRange 26).flatMap edgesAt

def G : SimpleGraph Vertex := graphOfEdges allEdges

instance : DecidableRel G.Adj := graphOfEdgesDecidable _

def pairEdges : List (PairVertex × PairVertex) :=
  (localEdges.map fun (u, v) => (⟨u.val, by omega⟩, ⟨v.val, by omega⟩)) ++
  (localEdges.map fun (u, v) => (⟨38 + u.val, by omega⟩, ⟨38 + v.val, by omega⟩))

def pairG : SimpleGraph PairVertex := graphOfEdges pairEdges

instance : DecidableRel pairG.Adj := graphOfEdgesDecidable _

abbrev pairPrism : SimpleGraph (PairVertex × Fin 2) := pairG □ (⊤ : SimpleGraph (Fin 2))

abbrev prism : SimpleGraph (Vertex × Fin 2) := G □ (⊤ : SimpleGraph (Fin 2))

theorem edge_at {i : Fin 26} {u v : Vertex} (h : (u, v) ∈ edgesAt i) :
    (u, v) ∈ allEdges :=
  List.mem_flatMap.mpr ⟨i, by simp, h⟩

theorem atBlock_ne_hub (i : Fin 26) (j : Local) (h : Fin 2) :
    atBlock i j ≠ hub h := by simp [atBlock, hub]

theorem atBlock_injective (i : Fin 26) : Function.Injective (atBlock i) := by
  intro j k h
  have h' : (block i j).val = (block i k).val :=
    congrArg Fin.val (Sum.inr.inj h)
  exact Fin.ext (by simpa [block] using h')

theorem adj_of_local {i : Fin 26} {u v : Local} (h : localG.Adj u v) :
    G.Adj (atBlock i u) (atBlock i v) := by
  have lift (a b : Local) (hab : (a, b) ∈ localEdges) :
      (atBlock i a, atBlock i b) ∈ allEdges := by
    apply edge_at (i := i)
    have member : (atBlock i a, atBlock i b) ∈
        localEdges.map (fun (u, v) => (atBlock i u, atBlock i v)) :=
      List.mem_map.mpr ⟨(a, b), hab, rfl⟩
    simp only [edgesAt, List.mem_append]
    tauto
  exact ⟨fun hv => h.1 (atBlock_injective i hv), h.2.imp (lift u v) (lift v u)⟩

theorem hub_upper_adj {i : Fin 26} {j : Local} (h : j ∈ upper) :
    G.Adj (hub 0) (atBlock i j) := by
  refine ⟨(atBlock_ne_hub i j 0).symm, Or.inl (edge_at (i := i) ?_)⟩
  have member : (hub 0, atBlock i j) ∈ upper.map (fun j => (hub 0, atBlock i j)) :=
    List.mem_map.mpr ⟨j, h, rfl⟩
  simp only [edgesAt, List.mem_append]
  tauto

theorem hub_lower_adj {i : Fin 26} {j : Local} (h : j ∈ lower) :
    G.Adj (hub 1) (atBlock i j) := by
  refine ⟨(atBlock_ne_hub i j 1).symm, Or.inl (edge_at (i := i) ?_)⟩
  have member : (hub 1, atBlock i j) ∈ lower.map (fun j => (hub 1, atBlock i j)) :=
    List.mem_map.mpr ⟨j, h, rfl⟩
  simp only [edgesAt, List.mem_append]
  tauto

end PrismCounterexample

namespace PrismCounterexample

open SimpleGraph

private theorem not_mem_of_card_lt {V : Type*} [DecidableEq V]
    {S T : Finset V} (h : S.card < T.card) : ∃ x ∈ T, x ∉ S := by
  by_contra! hs
  exact (not_le_of_gt h) (Finset.card_le_card hs)

private theorem connectCover {W V : Type*} [Fintype W] [DecidableEq V]
    (H : SimpleGraph W) (G : SimpleGraph V) (n : ℕ) (hn : 0 < n)
    (e : Fin n → W ↪ V)
    (edge : ∀ i, ∀ ⦃u v⦄, H.Adj u v → G.Adj (e i u) (e i v))
    (cover : ∀ x : V, ∃ i w, e i w = x)
    (overlap : ∀ k (hk : k+1<n), ∃ T : Finset V, 2 < T.card ∧
      ∀ x ∈ T, (∃ w, e ⟨k, by omega⟩ w = x) ∧ (∃ w, e ⟨k+1,hk⟩ w = x))
    (hH : ∀ S : Finset W, S.card ≤ 2 → (H.induce ((S : Set W)ᶜ)).Connected)
    (S : Finset V) (hS : S.card ≤ 2) : (G.induce ((S : Set V)ᶜ)).Connected := by
  classical
  let R := fun (i : Fin n) => Finset.univ.filter (fun w => e i w ∈ S)
  have rmem (i : Fin n) (w : W) : w ∈ R i ↔ e i w ∈ S := by simp [R]
  have rcard (i : Fin n) : (R i).card ≤ 2 := by
    have hsub : (R i).map (e i) ⊆ S := by
      intro x hx
      obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hx
      exact (rmem i w).mp hw
    have := Finset.card_le_card hsub
    simpa using this.trans hS
  let mapR (i : Fin n) : (H.induce ((R i : Set W)ᶜ)) →g (G.induce ((S : Set V)ᶜ)) :=
    ⟨fun w => ⟨e i w, fun h => w.property ((rmem i w).mpr h)⟩,
      fun h => edge i h⟩
  let Z := (S : Set V)ᶜ
  have inside (i : Fin n) (x y : Z)
      (hx : ∃ w, e i w = x.val) (hy : ∃ w, e i w = y.val) :
      (G.induce Z).Reachable x y := by
    obtain ⟨u,hu⟩ := hx
    obtain ⟨v,hv⟩ := hy
    let u' : ↥((R i : Set W)ᶜ) := ⟨u, fun h => x.property (hu ▸ (rmem i u).mp h)⟩
    let v' : ↥((R i : Set W)ᶜ) := ⟨v, fun h => y.property (hv ▸ (rmem i v).mp h)⟩
    have eqx : mapR i u' = x := Subtype.ext hu
    have eqy : mapR i v' = y := Subtype.ext hv
    simpa only [eqx, eqy] using ((hH (R i) (rcard i)) u' v').map (mapR i)
  have nz : Nonempty ↥((R ⟨0,hn⟩ : Set W)ᶜ) := (hH _ (rcard _)).nonempty
  let startR := Classical.choice nz
  let start : Z := mapR ⟨0,hn⟩ startR
  rw [connected_iff_exists_forall_reachable]
  refine ⟨start, ?_⟩
  have along : ∀ (k : ℕ) (hk : k < n) (x : Z), (∃ w, e ⟨k,hk⟩ w = x.val) →
      (G.induce Z).Reachable start x := by
    intro k
    induction k with
    | zero =>
        intro hk x hx
        exact inside ⟨0,hk⟩ start x ⟨startR.val,rfl⟩ hx
    | succ k ih =>
        intro hk x hx
        obtain ⟨T,hT,hboth⟩ := overlap k hk
        obtain ⟨z,hz,hzs⟩ := not_mem_of_card_lt (hS.trans_lt hT)
        exact (ih (by omega) ⟨z,hzs⟩ (hboth z hz).1).trans
          (inside ⟨k+1,hk⟩ ⟨z,hzs⟩ x (hboth z hz).2 hx)
  intro x
  obtain ⟨i,w,hw⟩ := cover x
  exact along i i.isLt x ⟨w,hw⟩

private abbrev LocalHub := Fin 41

private def insertLocal (j : Local) : LocalHub := ⟨j.val, by omega⟩

private def hubEdges : List (LocalHub × LocalHub) :=
  (localEdges.map fun (u,v) => (insertLocal u, insertLocal v)) ++
  (upper.map fun u => (39, insertLocal u)) ++ (lower.map fun u => (40, insertLocal u))

private def hubGraph : SimpleGraph LocalHub := graphOfEdges hubEdges

private instance : DecidableRel hubGraph.Adj := graphOfEdgesDecidable _

private def routes (v : LocalHub) : List LocalHub × List LocalHub × List LocalHub :=
  match v.val with
  | 1 => ([0], [2, 3, 4, 17, 39], [40])
  | 2 => ([1, 0], [3, 4, 17, 39], [40])
  | 3 => ([4, 0], [8, 17, 39], [40])
  | 4 => ([0], [17, 39], [3, 40])
  | 5 => ([3, 4, 0], [6, 7, 17, 39], [40])
  | 6 => ([5, 3, 4, 0], [7, 17, 39], [40])
  | 7 => ([8, 3, 4, 0], [17, 39], [40])
  | 8 => ([3, 4, 0], [17, 39], [7, 40])
  | 9 => ([0], [39], [10, 11, 12, 17, 40])
  | 10 => ([9, 0], [39], [11, 12, 17, 40])
  | 11 => ([12, 0], [39], [16, 17, 40])
  | 12 => ([0], [11, 39], [17, 40])
  | 13 => ([11, 12, 0], [39], [14, 15, 17, 40])
  | 14 => ([13, 11, 12, 0], [39], [15, 17, 40])
  | 15 => ([16, 11, 12, 0], [39], [17, 40])
  | 16 => ([11, 12, 0], [15, 39], [17, 40])
  | 17 => ([4, 0], [39], [40])
  | 18 => ([17, 4, 0], [19, 39], [23, 22, 34, 40])
  | 19 => ([17, 4, 0], [39], [18, 23, 22, 34, 40])
  | 20 => ([19, 17, 4, 0], [39], [21, 23, 22, 34, 40])
  | 21 => ([20, 19, 17, 4, 0], [39], [23, 22, 34, 40])
  | 22 => ([17, 4, 0], [23, 39], [34, 40])
  | 23 => ([18, 17, 4, 0], [39], [22, 34, 40])
  | 24 => ([23, 22, 17, 4, 0], [39], [25, 34, 40])
  | 25 => ([24, 23, 22, 17, 4, 0], [39], [34, 40])
  | 26 => ([17, 4, 0], [31, 30, 34, 39], [27, 40])
  | 27 => ([17, 4, 0], [26, 31, 30, 34, 39], [40])
  | 28 => ([27, 17, 4, 0], [29, 31, 30, 34, 39], [40])
  | 29 => ([28, 27, 17, 4, 0], [31, 30, 34, 39], [40])
  | 30 => ([17, 4, 0], [34, 39], [31, 40])
  | 31 => ([26, 17, 4, 0], [30, 34, 39], [40])
  | 32 => ([31, 30, 17, 4, 0], [33, 34, 39], [40])
  | 33 => ([32, 31, 30, 17, 4, 0], [34, 39], [40])
  | 34 => ([30, 17, 4, 0], [39], [40])
  | 35 => ([34, 30, 17, 4, 0], [39], [38, 40])
  | 36 => ([34, 30, 17, 4, 0], [37, 38, 39], [40])
  | 37 => ([36, 34, 30, 17, 4, 0], [38, 39], [40])
  | 38 => ([35, 34, 30, 17, 4, 0], [39], [40])
  | _ => ([], [], [])

private def RouteTo (v r : LocalHub) (l : List LocalHub) : Prop :=
  l.getLastD v = r ∧ (v :: l).IsChain hubGraph.Adj

private instance (v r : LocalHub) (l : List LocalHub) : Decidable (RouteTo v r l) :=
  inferInstanceAs (Decidable (_ ∧ _))

private lemma routeCertificate (v : LocalHub) :
    v ∈ ({0,39,40} : Finset LocalHub) ∨
      (let a := (routes v).1
       let b := (routes v).2.1
       let c := (routes v).2.2
       RouteTo v 0 a ∧ RouteTo v 39 b ∧ RouteTo v 40 c ∧
       Disjoint a.toFinset b.toFinset ∧ Disjoint a.toFinset c.toFinset ∧
       Disjoint b.toFinset c.toFinset) := by
  fin_cases v <;> decide

private theorem someRouteSurvives {V : Type*} [DecidableEq V] {S A B C : Finset V}
    (hs : S.card ≤ 2) (ab : Disjoint A B) (ac : Disjoint A C) (bc : Disjoint B C) :
    Disjoint S A ∨ Disjoint S B ∨ Disjoint S C := by
  by_contra! h
  obtain ⟨a, ha, ha'⟩ := Finset.not_disjoint_iff.mp h.1
  obtain ⟨b, hb, hb'⟩ := Finset.not_disjoint_iff.mp h.2.1
  obtain ⟨c, hc, hc'⟩ := Finset.not_disjoint_iff.mp h.2.2
  have h₁ : a ≠ b := fun e => (Finset.disjoint_left.mp ab) ha' (e ▸ hb')
  have h₂ : a ≠ c := fun e => (Finset.disjoint_left.mp ac) ha' (e ▸ hc')
  have h₃ : b ≠ c := fun e => (Finset.disjoint_left.mp bc) hb' (e ▸ hc')
  have hsub : ({a,b,c} : Finset V) ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hc' := Finset.card_le_card hsub
  simp [h₁,h₂,h₃] at hc'
  omega

private theorem followRoute {V : Type*} [DecidableEq V] (H : SimpleGraph V)
    (S : Finset V) (v : ↥((S : Set V)ᶜ)) (l : List V)
    (h : (v.val :: l).IsChain H.Adj) (hl : ∀ q ∈ l, q ∉ S) :
    ∃ w : ↥((S : Set V)ᶜ), w.val = l.getLastD v.val ∧ (H.induce ((S : Set V)ᶜ)).Reachable v w := by
  induction l generalizing v with
  | nil => exact ⟨v,rfl,SimpleGraph.Reachable.refl _⟩
  | cons u l ih =>
      obtain ⟨hvu, ht⟩ := List.isChain_cons_cons.mp h
      let u' : ↥((S : Set V)ᶜ) := ⟨u, hl u (by simp)⟩
      obtain ⟨w, hw, huw⟩ := ih u' ht (fun q hq => hl q (by simp [hq]))
      exact ⟨w, by simpa only [List.getLastD_cons] using hw,
        (SimpleGraph.Adj.reachable (G := H.induce ((S : Set V)ᶜ)) (u := v) (v := u') hvu).trans huw⟩

private theorem localHubConnected (S : Finset LocalHub) (hS : S.card ≤ 2) :
    (hubGraph.induce ((S : Set LocalHub)ᶜ)).Connected := by
  let Z := (S : Set LocalHub)ᶜ
  let K := hubGraph.induce Z
  let anchors : Finset LocalHub := {0,39,40}
  have anc : ∀ v : Z, ∃ r : Z, r.val ∈ anchors ∧ K.Reachable v r := by
    intro v
    rcases routeCertificate v.val with hv | cert
    · exact ⟨v,hv,SimpleGraph.Reachable.refl _⟩
    · rcases cert with ⟨ha,hb,hc,ab,ac,bc⟩
      have follow {r : LocalHub} {l : List LocalHub}
          (hr : r ∈ anchors) (hroute : RouteTo v.val r l) (hsafe : Disjoint S l.toFinset) :
          ∃ w : Z, w.val ∈ anchors ∧ K.Reachable v w := by
        obtain ⟨w,hw,hvw⟩ := followRoute hubGraph S v l hroute.2
          (fun q hq hs => (Finset.disjoint_left.mp hsafe) hs (by simpa using hq))
        exact ⟨w, by rw [hw, hroute.1]; exact hr, hvw⟩
      rcases someRouteSurvives hS ab ac bc with ha' | hb' | hc'
      · exact follow (by decide) ha ha'
      · exact follow (by decide) hb hb'
      · exact follow (by decide) hc hc'
  have hubsJoined (u v : Z) (h₁ : u.val = 39) (h₂ : v.val = 40) : K.Reachable u v := by
    have hcard : S.card < ({0,17,34} : Finset LocalHub).card := hS.trans_lt (by decide)
    obtain ⟨w,hw,hwS⟩ := not_mem_of_card_lt hcard
    let w' : Z := ⟨w,hwS⟩
    have h₃ : hubGraph.Adj 39 w ∧ hubGraph.Adj w 40 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with h | h | h <;> subst w <;> decide
    have hu' : K.Adj u w' := by change hubGraph.Adj u.val w; rw [h₁]; exact h₃.1
    have hv' : K.Adj w' v := by change hubGraph.Adj w v.val; rw [h₂]; exact h₃.2
    exact hu'.reachable.trans hv'.reachable
  have anchorsJoined (u v : Z) (hu : u.val ∈ anchors) (hv : v.val ∈ anchors) :
      K.Reachable u v := by
    have eqReach (h : u.val = v.val) : K.Reachable u v := by
      have e : u = v := Subtype.ext h
      subst v
      exact SimpleGraph.Reachable.refl _
    have edgeReach {p q : LocalHub} (h : hubGraph.Adj p q) (hu : u.val = p) (hv : v.val = q) :
        K.Reachable u v := by
      apply SimpleGraph.Adj.reachable
      change hubGraph.Adj u.val v.val
      rwa [hu,hv]
    simp only [anchors, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with hu | hu | hu <;> rcases hv with hv | hv | hv
    · exact eqReach (hu.trans hv.symm)
    · exact edgeReach (by decide) hu hv
    · exact edgeReach (by decide) hu hv
    · exact edgeReach (by decide) hu hv
    · exact eqReach (hu.trans hv.symm)
    · exact hubsJoined u v hu hv
    · exact edgeReach (by decide) hu hv
    · exact (hubsJoined v u hv hu).symm
    · exact eqReach (hu.trans hv.symm)
  have hcard : S.card < anchors.card := hS.trans_lt (by decide)
  obtain ⟨r, hr, hrS⟩ := not_mem_of_card_lt hcard
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨r,hrS⟩,fun v => ?_⟩
  obtain ⟨w,hw,hvw⟩ := anc v
  exact (anchorsJoined ⟨r,hrS⟩ w hr hw).trans hvw.symm
private def connEmbedFun (i : Fin 26) (j : LocalHub) : Vertex :=
  if h : j.val < 39 then atBlock i ⟨j.val,h⟩ else hub ⟨j.val-39,by omega⟩

private def connEmbedding (i : Fin 26) : LocalHub ↪ Vertex where
  toFun := connEmbedFun i
  inj' := by
    intro u v h
    unfold connEmbedFun at h
    split at h <;> split at h
    · have h' := congrArg Fin.val (atBlock_injective i h)
      exact Fin.ext h'
    · exact ((atBlock_ne_hub _ _ _) h).elim
    · exact ((atBlock_ne_hub _ _ _) h.symm).elim
    · have h' := congrArg Fin.val (Sum.inl.inj h)
      apply Fin.ext
      change u.val - 39 = v.val - 39 at h'
      omega

private theorem embedLocal (i : Fin 26) (j : Local) :
    connEmbedding i (insertLocal j) = atBlock i j := by
  change connEmbedFun i (insertLocal j) = _
  simp [connEmbedFun, insertLocal, j.isLt]

private theorem embedTop (i : Fin 26) : connEmbedding i 39 = hub 0 := rfl

private theorem embedBottom (i : Fin 26) : connEmbedding i 40 = hub 1 := rfl

private theorem connEdge (i : Fin 26) {u v : LocalHub} (h : hubGraph.Adj u v) :
    G.Adj (connEmbedding i u) (connEmbedding i v) := by
  have heq : hubEdges.map (fun (u,v) => (connEmbedding i u,connEmbedding i v)) = edgesAt i := by
    simp [hubEdges, edgesAt, List.map_append, List.map_map, Function.comp_def,
      embedLocal, embedTop, embedBottom]
  have edgeMap {a b : LocalHub} (h : (a,b) ∈ hubEdges) :
      (connEmbedding i a, connEmbedding i b) ∈ allEdges := by
    apply edge_at (i := i)
    rw [← heq]
    exact List.mem_map.mpr ⟨(a,b),h,rfl⟩
  refine ⟨fun h' => h.1 ((connEmbedding i).injective h'), ?_⟩
  exact h.2.imp edgeMap edgeMap

private theorem connCover : ∀ v : Vertex, ∃ i w, connEmbedding i w = v := by
  intro v
  rcases v with h | x
  · fin_cases h
    · exact ⟨0,39,embedTop 0⟩
    · exact ⟨0,40,embedBottom 0⟩
  · let i : Fin 26 := ⟨(x.val - 1) / 38, by omega⟩
    let j : Local := ⟨x.val - 38 * i.val, by dsimp [i]; omega⟩
    refine ⟨i,insertLocal j,?_⟩
    rw [embedLocal]
    apply congrArg Sum.inr
    apply Fin.ext
    dsimp [block, i, j]
    omega

private theorem connOverlap (k : ℕ) (hk : k+1 < 26) : ∃ T : Finset Vertex, 2 < T.card ∧
    ∀ x ∈ T, (∃ w, connEmbedding ⟨k, by omega⟩ w = x) ∧
      (∃ w, connEmbedding ⟨k+1,hk⟩ w = x) := by
  let i : Fin 26 := ⟨k, by omega⟩
  let j : Fin 26 := ⟨k+1,hk⟩
  have h : atBlock i 38 = atBlock j 0 := by
    apply congrArg Sum.inr
    apply Fin.ext
    simp [block, i, j]
    omega
  refine ⟨{hub 0,hub 1,atBlock i 38},?_,?_⟩
  · have diff : hub 0 ≠ hub 1 := by decide
    simp [diff, Ne.symm (atBlock_ne_hub _ _ _)]
  · intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact ⟨⟨39, embedTop _⟩, ⟨39, embedTop _⟩⟩
    · exact ⟨⟨40, embedBottom _⟩, ⟨40, embedBottom _⟩⟩
    · exact ⟨⟨insertLocal 38, embedLocal _ _⟩, ⟨insertLocal 0, (embedLocal _ _).trans h.symm⟩⟩

/-- Deleting any two vertices of the chain of gadgets leaves a connected graph. -/
theorem counterexampleConnected (S : Finset Vertex) (hs : S.card ≤ 2) :
    (G.induce ((S : Set Vertex)ᶜ)).Connected :=
  connectCover hubGraph G 26 (by decide) connEmbedding connEdge connCover connOverlap
    localHubConnected S hs

end PrismCounterexample

/-!
The two fans in Špacapan's construction can be drawn with rational coordinates.
Start with copies of the 39-vertex gadget inside adjacent vertical strips.
The upper half-plane is projected by `(x,y) ↦ (x/(1+y),y/(1+y))` and the lower
half-plane by reflection. Vertical rays therefore become spokes to `(0,1)` and
`(0,-1)`. The finite orientation checks verify the drawing inside one gadget.
-/

namespace PrismCounterexample

open Set SimpleGraph

noncomputable section

private abbrev Point := ℤ × ℤ

private abbrev Plane := EuclideanSpace ℝ (Fin 2)

private def actual (x y : ℝ) : Plane := WithLp.toLp 2 ![x, y]

private def euclid (p : Point) : Plane := actual p.1 p.2

@[simp] private theorem actual_x (x y : ℝ) : actual x y 0 = x := rfl
@[simp] private theorem actual_y (x y : ℝ) : actual x y 1 = y := rfl

private theorem plane_ext {u v : Plane} (h₀ : u 0 = v 0) (h₁ : u 1 = v 1) : u = v := by
  ext i
  fin_cases i
  · exact h₀
  · exact h₁

private theorem euclid_injective : Function.Injective euclid := by
  intro p q h
  have hx := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 0) h
  have hy := congrArg (fun v : EuclideanSpace ℝ (Fin 2) => v 1) h
  change (p.1 : ℝ) = (q.1 : ℝ) at hx
  change (p.2 : ℝ) = (q.2 : ℝ) at hy
  exact Prod.ext (Int.cast_injective hx) (Int.cast_injective hy)

private theorem point_on_segment_real {p q z : Plane} (hz : z ∈ segment ℝ p q) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      z 0 = p 0 + t * (q 0 - p 0) ∧
      z 1 = p 1 + t * (q 1 - p 1) := by
  obtain ⟨a, b, ha, hb, hab, hz⟩ := hz
  refine ⟨b, hb, by linarith, ?_, ?_⟩
  · have h := congrArg (fun v : Plane => v 0) hz
    change a * p 0 + b * q 0 = z 0 at h
    rw [show a = 1 - b by linarith] at h
    linarith
  · have h := congrArg (fun v : Plane => v 1) hz
    change a * p 1 + b * q 1 = z 1 at h
    rw [show a = 1 - b by linarith] at h
    linarith

private theorem point_on_segment {p q : Point} {z : Plane}
    (hz : z ∈ segment ℝ (euclid p) (euclid q)) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      z 0 = (p.1 : ℝ) + t * ((q.1 : ℝ) - p.1) ∧
      z 1 = (p.2 : ℝ) + t * ((q.2 : ℝ) - p.2) := by
  simpa [euclid] using point_on_segment_real hz

private theorem segment_of_weights {p q z : Plane} (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1)
    (hx : z 0 = a * p 0 + b * q 0) (hy : z 1 = a * p 1 + b * q 1) :
    z ∈ segment ℝ p q := by
  refine ⟨a, b, ha, hb, hab, plane_ext ?_ ?_⟩
  · exact hx.symm
  · exact hy.symm

private def orient (a b c : Point) : ℤ :=
  (b.1 - a.1) * (c.2 - a.2) - (b.2 - a.2) * (c.1 - a.1)

private def sameSide (a b c d : Point) : Prop :=
  0 < orient a b c * orient a b d

private def apart (a b d : Point) : Prop :=
  orient a b d ≠ 0 ∨ (b.1 - a.1) * (d.1 - a.1) < 0 ∨
    (b.2 - a.2) * (d.2 - a.2) < 0

private theorem apart_meet {a b d : Point} {z : EuclideanSpace ℝ (Fin 2)}
    (hgood : apart a b d)
    (h₁ : z ∈ segment ℝ (euclid a) (euclid b))
    (h₂ : z ∈ segment ℝ (euclid a) (euclid d)) : z = euclid a := by
  obtain ⟨s, hs, _, sx, sy⟩ := point_on_segment h₁
  obtain ⟨t, ht, _, tx, ty⟩ := point_on_segment h₂
  have hX : s * ((b.1 : ℝ) - a.1) = t * ((d.1 : ℝ) - a.1) := by linarith
  have hY : s * ((b.2 : ℝ) - a.2) = t * ((d.2 : ℝ) - a.2) := by linarith
  have hz : s = 0 := by
    rcases hgood with h | h | h
    · have hne : ((b.1 : ℝ) - a.1) * ((d.2 : ℝ) - a.2) -
          ((b.2 : ℝ) - a.2) * ((d.1 : ℝ) - a.1) ≠ 0 := by
        unfold orient at h
        exact_mod_cast h
      apply (mul_eq_zero.mp ?_).resolve_right hne
      calc
        _ = (s * ((b.1 : ℝ) - a.1)) * ((d.2 : ℝ) - a.2) -
            (s * ((b.2 : ℝ) - a.2)) * ((d.1 : ℝ) - a.1) := by ring
        _ = 0 := by rw [hX, hY]; ring
    · have hlt : ((b.1 : ℝ) - a.1) * ((d.1 : ℝ) - a.1) < 0 := by exact_mod_cast h
      by_contra hne
      have hneg := mul_neg_of_pos_of_neg (lt_of_le_of_ne hs (Ne.symm hne)) hlt
      have hpos := mul_nonneg ht (sq_nonneg ((d.1 : ℝ) - a.1))
      have hid := congrArg (fun r : ℝ => r * ((d.1 : ℝ) - a.1)) hX
      apply (not_lt_of_ge hpos)
      calc
        _ = _ := by nlinarith [hid]
        _ < 0 := hneg
    · have hlt : ((b.2 : ℝ) - a.2) * ((d.2 : ℝ) - a.2) < 0 := by exact_mod_cast h
      by_contra hne
      have hneg := mul_neg_of_pos_of_neg (lt_of_le_of_ne hs (Ne.symm hne)) hlt
      have hpos := mul_nonneg ht (sq_nonneg ((d.2 : ℝ) - a.2))
      have hid := congrArg (fun r : ℝ => r * ((d.2 : ℝ) - a.2)) hY
      apply (not_lt_of_ge hpos)
      calc
        _ = _ := by nlinarith [hid]
        _ < 0 := hneg
  ext i
  fin_cases i
  · simpa [euclid, hz] using sx
  · simpa [euclid, hz] using sy

private theorem sameSide_separate {a b c d : Point} {z : EuclideanSpace ℝ (Fin 2)}
    (hgood : sameSide a b c d) (h₁ : z ∈ segment ℝ (euclid a) (euclid b))
    (h₂ : z ∈ segment ℝ (euclid c) (euclid d)) : False := by
  obtain ⟨s, _, _, sx, sy⟩ := point_on_segment h₁
  obtain ⟨t, ht, ht', tx, ty⟩ := point_on_segment h₂
  set C : ℝ := (orient a b c : ℝ)
  set D : ℝ := (orient a b d : ℝ)
  have hcases : 0 < C * D := by
    dsimp [C, D]
    unfold sameSide at hgood
    exact_mod_cast hgood
  have hzero : (1 - t) * C + t * D = 0 := by
    calc
      _ = ((b.1 : ℝ) - a.1) * (z 1 - a.2) - ((b.2 : ℝ) - a.2) * (z 0 - a.1) := by
        rw [tx, ty]
        simp only [C, D, orient, Int.cast_sub, Int.cast_mul]
        ring
      _ = 0 := by rw [sx, sy]; ring
  rcases mul_pos_iff.mp hcases with ⟨hc, hd⟩ | ⟨hc, hd⟩
  · rcases eq_or_lt_of_le ht with h | h
    · simp [← h, ne_of_gt hc] at hzero
    · have h1 := mul_nonneg (sub_nonneg.mpr ht') (le_of_lt hc)
      have h2 := mul_pos h hd
      linarith
  · rcases eq_or_lt_of_le ht with h | h
    · simp [← h, ne_of_lt hc] at hzero
    · have h1 := mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr ht') (le_of_lt hc)
      have h2 := mul_neg_of_pos_of_neg h hd
      linarith

private def warp (s : ℝ) (p : Point) : Plane :=
  actual ((p.1 : ℝ) / (1 + s * p.2)) ((p.2 : ℝ) / (1 + s * p.2))

private def unwarp (s : ℝ) (z : Plane) : Plane :=
  actual (z 0 / (1 - s * z 1)) (z 1 / (1 - s * z 1))

private theorem unwarp_segment {s : ℝ} {p q : Point} {z : Plane}
    (hp : 0 < 1 + s * (p.2 : ℝ)) (hq : 0 < 1 + s * (q.2 : ℝ))
    (hz : z ∈ segment ℝ (warp s p) (warp s q)) :
    0 < 1 - s * z 1 ∧ unwarp s z ∈ segment ℝ (euclid p) (euclid q) := by
  obtain ⟨a, b, ha, hb, hab, hz⟩ := hz
  have hx := congrArg (fun v : Plane => v 0) hz
  have hy := congrArg (fun v : Plane => v 1) hz
  change a * ((p.1 : ℝ) / (1 + s * p.2)) +
    b * ((q.1 : ℝ) / (1 + s * q.2)) = z 0 at hx
  change a * ((p.2 : ℝ) / (1 + s * p.2)) +
    b * ((q.2 : ℝ) / (1 + s * q.2)) = z 1 at hy
  let U : ℝ := 1 + s * (p.2 : ℝ)
  let V : ℝ := 1 + s * (q.2 : ℝ)
  let D : ℝ := 1 - s * z 1
  change 0 < U at hp
  change 0 < V at hq
  have hD : D = a / U + b / V := by
    unfold D
    rw [← hy]
    change 1 - s * (a * ((p.2 : ℝ) / U) + b * ((q.2 : ℝ) / V)) = _
    have hU : 1 - s * ((p.2 : ℝ) / U) = 1 / U := by
      field_simp [hp.ne']
      dsimp [U]
      ring
    have hV : 1 - s * ((q.2 : ℝ) / V) = 1 / V := by
      field_simp [hq.ne']
      dsimp [V]
      ring
    calc
      _ = a * (1 - s * ((p.2 : ℝ) / U)) + b * (1 - s * ((q.2 : ℝ) / V)) := by
        linarith [hab]
      _ = _ := by rw [hU, hV]; simp [div_eq_mul_inv]
  have hd : 0 < D := by
    rw [hD]
    by_cases hap : 0 < a
    · exact add_pos_of_pos_of_nonneg (div_pos hap hp) (div_nonneg hb hq.le)
    · exact add_pos_of_nonneg_of_pos (div_nonneg ha hp.le) (div_pos (by linarith) hq)
  refine ⟨hd, segment_of_weights (a / U / D) (b / V / D)
    (div_nonneg (div_nonneg ha hp.le) hd.le) (div_nonneg (div_nonneg hb hq.le) hd.le) ?_ ?_ ?_⟩
  · rw [← add_div, ← hD, div_self hd.ne']
  · change z 0 / D = (a / U / D) * (p.1 : ℝ) + (b / V / D) * q.1
    change a * ((p.1 : ℝ) / U) + b * ((q.1 : ℝ) / V) = z 0 at hx
    rw [← hx]
    ring
  · change z 1 / D = (a / U / D) * (p.2 : ℝ) + (b / V / D) * q.2
    change a * ((p.2 : ℝ) / U) + b * ((q.2 : ℝ) / V) = z 1 at hy
    rw [← hy]
    ring

private theorem warp_of_unwarp_eq {s : ℝ} {p : Point} {z : Plane}
    (hz : 1 - s * z 1 ≠ 0) (h : unwarp s z = euclid p) : z = warp s p := by
  have hx := congrArg (fun v : Plane => v 0) h
  have hy := congrArg (fun v : Plane => v 1) h
  change z 0 / (1 - s * z 1) = (p.1 : ℝ) at hx
  change z 1 / (1 - s * z 1) = (p.2 : ℝ) at hy
  rw [div_eq_iff hz] at hx hy
  have hd : (1 - s * z 1) * (1 + s * (p.2 : ℝ)) = 1 := by nlinarith [congrArg (s * ·) hy]
  have hd' : 1 + s * (p.2 : ℝ) ≠ 0 := by
    intro he
    rw [he, mul_zero] at hd
    norm_num at hd
  apply plane_ext
  · simp only [warp, actual_x]
    apply (eq_div_iff hd').mpr
    rw [hx, mul_assoc, hd, mul_one]
  · simp only [warp, actual_y]
    apply (eq_div_iff hd').mpr
    rw [hy, mul_assoc, hd, mul_one]

private theorem unwarp_on_axis {s t : ℝ} {z : Plane} (hz : z 1 = 0) :
    unwarp s z = unwarp t z := by simp [unwarp, hz]

private def localPoint (j : Local) : Point :=
  ![(0,0),(1,-2),(2,-2),(4,-2),(2,-1),(5,-2),(6,-2),(9,-2),(7,-1),
    (1,2),(2,2),(4,2),(2,1),(5,2),(6,2),(9,2),(7,1),(10,0),
    (13,1),(11,2),(14,2),(15,2),(18,1),(16,2),(18,2),(19,2),
    (13,-1),(11,-2),(14,-2),(15,-2),(18,-1),(16,-2),(18,-2),(19,-2),
    (20,0),(22,2),(21,-2),(23,-2),(24,0)] j

private def xShift (h : ℤ) (p : Point) : Point := (h + p.1, p.2)

private def basePoint (i : Fin 26) (j : Local) : Point :=
  xShift (24 * (i.val : ℤ)) (localPoint j)

private def linePoint (v : Line) : Point :=
  if h : v.val < 988 then
    basePoint ⟨v.val / 38, by omega⟩ ⟨v.val % 38, by omega⟩
  else (624, 0)

private theorem linePoint_block (i : Fin 26) (j : Local) :
    linePoint (block i j) = basePoint i j := by
  have hi := i.isLt
  have hj := j.isLt
  by_cases hj' : j.val < 38
  · have hb : (block i j).val < 988 := by simp only [block]; omega
    rw [linePoint, dif_pos hb]
    congr 1
    · apply Fin.ext
      simp only [block]
      omega
    · apply Fin.ext
      simp only [block]
      omega
  · have hj38 : j = 38 := by apply Fin.ext; simpa using (show j.val = 38 by omega)
    subst j
    by_cases hi' : i.val < 25
    · have hb : (block i 38).val < 988 := by simp only [block]; omega
      have hdiv : (block i 38).val / 38 = i.val + 1 := by simp only [block]; omega
      have hmod : (block i 38).val % 38 = 0 := by simp only [block]; omega
      rw [linePoint, dif_pos hb]
      apply Prod.ext
      · simp only [basePoint, xShift, hdiv]
        have e : (⟨(block i 38).val % 38, by omega⟩ : Local) = 0 := Fin.ext hmod
        rw [e]
        change 24 * ((i.val + 1 : ℕ) : ℤ) + 0 = 24 * (i.val : ℤ) + 24
        push_cast
        ring
      · change (localPoint ⟨(block i 38).val % 38, by omega⟩).2 = (localPoint 38).2
        have e : (⟨(block i 38).val % 38, by omega⟩ : Local) = 0 := Fin.ext hmod
        rw [e]
        rfl
    · have hb : ¬ (block i 38).val < 988 := by simp only [block]; omega
      have hi25 : i = 25 := by apply Fin.ext; simpa using (show i.val = 25 by omega)
      subst i
      rfl

private def coord (k : Fin 2) (p : Point) : ℤ := if k = 0 then p.1 else p.2

private theorem coordinate_bounds {p q : Point} {z : Plane} (k : Fin 2)
    (hz : z ∈ segment ℝ (euclid p) (euclid q)) :
    ((min (coord k p) (coord k q) : ℤ) : ℝ) ≤ z k ∧ z k ≤ ((max (coord k p) (coord k q) : ℤ) : ℝ) := by
  obtain ⟨a, b, ha, hb, hab, hz⟩ := hz
  have h := congrArg (fun v : Plane => v k) hz
  have hc (u : Point) : euclid u k = (coord k u : ℝ) := by fin_cases k <;> rfl
  change a * (euclid p k) + b * (euclid q k) = z k at h
  rw [hc, hc] at h
  have hp : ((min (coord k p) (coord k q) : ℤ) : ℝ) ≤ coord k p := Int.cast_le.mpr (min_le_left _ _)
  have hq : ((min (coord k p) (coord k q) : ℤ) : ℝ) ≤ coord k q := Int.cast_le.mpr (min_le_right _ _)
  have gp : (coord k p : ℝ) ≤ ((max (coord k p) (coord k q) : ℤ) : ℝ) := Int.cast_le.mpr (le_max_left _ _)
  have gq : (coord k q : ℝ) ≤ ((max (coord k p) (coord k q) : ℤ) : ℝ) := Int.cast_le.mpr (le_max_right _ _)
  constructor
  · linarith [mul_le_mul_of_nonneg_left hp ha, mul_le_mul_of_nonneg_left hq hb,
      congrArg (fun v : ℝ => v * ((min (coord k p) (coord k q) : ℤ) : ℝ)) hab]
  · linarith [mul_le_mul_of_nonneg_left gp ha, mul_le_mul_of_nonneg_left gq hb,
      congrArg (fun v : ℝ => v * ((max (coord k p) (coord k q) : ℤ) : ℝ)) hab]

private def strictAxis (a b c d : Point) : Prop :=
  ∃ k : Fin 2, max (coord k a) (coord k b) < min (coord k c) (coord k d)

private theorem strictAxis_separate {a b c d : Point} {z : Plane}
    (hgood : strictAxis a b c d)
    (h₁ : z ∈ segment ℝ (euclid a) (euclid b))
    (h₂ : z ∈ segment ℝ (euclid c) (euclid d)) : False := by
  obtain ⟨k, hk⟩ := hgood
  exact (not_le_of_gt (Int.cast_lt.mpr hk))
    ((coordinate_bounds k h₂).1.trans (coordinate_bounds k h₁).2)

private def edgeCertificate (a b c d : Point) : Prop :=
  (a = c ∧ b = d) ∨ (a = d ∧ b = c) ∨
  (a = c ∧ apart a b d) ∨ (a = d ∧ apart a b c) ∨
  (b = c ∧ apart b a d) ∨ (b = d ∧ apart b a c) ∨
  sameSide a b c d ∨ sameSide c d a b ∨
  strictAxis a b c d ∨ strictAxis c d a b

private instance (a b c d : Point) : Decidable (edgeCertificate a b c d) := by
  unfold edgeCertificate apart sameSide strictAxis
  infer_instance

private def shareEndpoint (z : Plane) (a b c d : Point) : Prop :=
  ∃ p : Point, (p = a ∨ p = b) ∧ (p = c ∨ p = d) ∧ z = euclid p

private theorem certify_edges {a b c d : Point} {z : Plane}
    (hc : edgeCertificate a b c d) (hne : ¬ (a = c ∧ b = d) ∧ ¬ (a = d ∧ b = c))
    (h₁ : z ∈ segment ℝ (euclid a) (euclid b))
    (h₂ : z ∈ segment ℝ (euclid c) (euclid d)) : shareEndpoint z a b c d := by
  rcases hc with hc | hc | ⟨rfl, hc⟩ | ⟨rfl, hc⟩ | ⟨rfl, hc⟩ | ⟨rfl, hc⟩ |
    hc | hc | hc | hc
  · exact (hne.1 hc).elim
  · exact (hne.2 hc).elim
  · exact ⟨a, Or.inl rfl, Or.inl rfl, apart_meet hc h₁ h₂⟩
  · rw [segment_symm] at h₂
    exact ⟨a, Or.inl rfl, Or.inr rfl, apart_meet hc h₁ h₂⟩
  · rw [segment_symm] at h₁
    exact ⟨b, Or.inr rfl, Or.inl rfl, apart_meet hc h₁ h₂⟩
  · rw [segment_symm] at h₁ h₂
    exact ⟨b, Or.inr rfl, Or.inr rfl, apart_meet hc h₁ h₂⟩
  · exact (sameSide_separate hc h₁ h₂).elim
  · exact (sameSide_separate hc h₂ h₁).elim
  · exact (strictAxis_separate hc h₁ h₂).elim
  · exact (strictAxis_separate hc h₂ h₁).elim

private theorem local_pair_certificate :
    ∀ e ∈ localEdges, ∀ f ∈ localEdges,
      edgeCertificate (localPoint e.1) (localPoint e.2) (localPoint f.1) (localPoint f.2) := by
  have h : localEdges.all (fun e => localEdges.all (fun f =>
    decide (edgeCertificate (localPoint e.1) (localPoint e.2) (localPoint f.1) (localPoint f.2)))) = true := by
    decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

private theorem point_x_interval (j : Local) :
    0 ≤ (localPoint j).1 ∧ (localPoint j).1 ≤ 24 := by
  have h : ∀ j : Local, 0 ≤ (localPoint j).1 ∧ (localPoint j).1 ≤ 24 := by decide
  exact h j

private theorem point_y_interval (j : Local) :
    -2 ≤ (localPoint j).2 ∧ (localPoint j).2 ≤ 2 := by
  have h : ∀ j : Local, -2 ≤ (localPoint j).2 ∧ (localPoint j).2 ≤ 2 := by decide
  exact h j

private theorem left_coordinate (j : Local) : (localPoint j).1 = 0 ↔ j = 0 := by
  have h : ∀ j : Local, (localPoint j).1 = 0 ↔ j = 0 := by decide
  exact h j

private theorem right_coordinate (j : Local) : (localPoint j).1 = 24 ↔ j = 38 := by
  have h : ∀ j : Local, (localPoint j).1 = 24 ↔ j = 38 := by decide
  exact h j

private theorem local_injective : Function.Injective localPoint := by
  have h : ∀ i j : Local, localPoint i = localPoint j → i = j := by decide +kernel
  exact h

private theorem local_edge_dx :
    ∀ e ∈ localEdges, (localPoint e.1).1 ≠ (localPoint e.2).1 := by
  have h : localEdges.all (fun e => decide ((localPoint e.1).1 ≠ (localPoint e.2).1)) = true := by decide
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

private theorem local_edge_y :
    ∀ e ∈ localEdges, (0 ≤ (localPoint e.1).2 ∧ 0 ≤ (localPoint e.2).2) ∨
      ((localPoint e.1).2 ≤ 0 ∧ (localPoint e.2).2 ≤ 0) := by
  have h : localEdges.all (fun e => decide (
    (0 ≤ (localPoint e.1).2 ∧ 0 ≤ (localPoint e.2).2) ∨
    ((localPoint e.1).2 ≤ 0 ∧ (localPoint e.2).2 ≤ 0))) = true := by decide
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

private def pointCert (a b p : Point) : Prop :=
  p = a ∨ p = b ∨ orient a b p ≠ 0 ∨
    ∃ k : Fin 2, coord k p < min (coord k a) (coord k b) ∨
      max (coord k a) (coord k b) < coord k p

private instance (a b p : Point) : Decidable (pointCert a b p) := by
  unfold pointCert
  infer_instance

private theorem local_point_cert :
    ∀ e ∈ localEdges, ∀ p : Local, pointCert (localPoint e.1) (localPoint e.2) (localPoint p) := by
  have h : localEdges.all (fun e => (List.finRange 39).all (fun p =>
    decide (pointCert (localPoint e.1) (localPoint e.2) (localPoint p)))) = true := by
    decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq, List.mem_finRange, forall_true_left] using h

private theorem certify_point {a b p : Point} (h : pointCert a b p)
    (hm : euclid p ∈ segment ℝ (euclid a) (euclid b)) : p = a ∨ p = b := by
  rcases h with h | h | h | ⟨k, hk⟩
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    apply h
    obtain ⟨t, _, _, hx, hy⟩ := point_on_segment hm
    change (p.1 : ℝ) = (a.1 : ℝ) + t * ((b.1 : ℝ) - a.1) at hx
    change (p.2 : ℝ) = (a.2 : ℝ) + t * ((b.2 : ℝ) - a.2) at hy
    have hdet : (orient a b p : ℝ) = 0 := by
      simp only [orient, Int.cast_sub, Int.cast_mul]
      rw [hx, hy]
      ring
    exact_mod_cast hdet
  · obtain ⟨hl, hu⟩ := coordinate_bounds k hm
    have hcoord : euclid p k = (coord k p : ℝ) := by fin_cases k <;> rfl
    rw [hcoord] at hl hu
    rcases hk with hk | hk
    · exact (not_le_of_gt (Int.cast_lt.mpr hk) hl).elim
    · exact (not_le_of_gt (Int.cast_lt.mpr hk) hu).elim

private theorem point_of_x_eq {p q : Point} {z : Plane}
    (hneq : p.1 ≠ q.1) (hz : z ∈ segment ℝ (euclid p) (euclid q))
    (hx : z 0 = (p.1 : ℝ)) : z = euclid p := by
  obtain ⟨t, _, _, htx, hty⟩ := point_on_segment hz
  have hmul : t * ((q.1 : ℝ) - p.1) = 0 := by rw [hx] at htx; linarith
  have hd : (q.1 : ℝ) - p.1 ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hneq.symm)
  have ht := (mul_eq_zero.mp hmul).resolve_right hd
  exact plane_ext hx (by simpa [euclid, ht] using hty)

private theorem local_x_bounds (i : Fin 26) {a b : Local} {z : Plane}
    (h : z ∈ segment ℝ (euclid (basePoint i a)) (euclid (basePoint i b))) :
    24 * (i.val : ℝ) ≤ z 0 ∧ z 0 ≤ 24 * (i.val : ℝ) + 24 := by
  have ⟨h₁, h₂⟩ := coordinate_bounds 0 h
  have ha := point_x_interval a
  have hb := point_x_interval b
  change ((min (24 * (i.val : ℤ) + (localPoint a).1)
    (24 * (i.val : ℤ) + (localPoint b).1) : ℤ) : ℝ) ≤ z 0 at h₁
  change z 0 ≤ ((max (24 * (i.val : ℤ) + (localPoint a).1)
    (24 * (i.val : ℤ) + (localPoint b).1) : ℤ) : ℝ) at h₂
  constructor
  · apply le_trans ?_ h₁
    have hlow : 24 * (i.val : ℤ) ≤ min (24 * (i.val : ℤ) + (localPoint a).1)
        (24 * (i.val : ℤ) + (localPoint b).1) := by omega
    simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using
      (Int.cast_le.mpr hlow : (_ : ℝ) ≤ _)
  · apply h₂.trans
    have hupp : max (24 * (i.val : ℤ) + (localPoint a).1)
        (24 * (i.val : ℤ) + (localPoint b).1) ≤ 24 * (i.val : ℤ) + 24 := by omega
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using
      (Int.cast_le.mpr hupp : (_ : ℝ) ≤ _)

private theorem basePoint_dx (i : Fin 26) {a b : Local}
    (h : (a,b) ∈ localEdges) : (basePoint i a).1 ≠ (basePoint i b).1 := by
  have hh := local_edge_dx (a,b) h
  change (localPoint a).1 ≠ (localPoint b).1 at hh
  simp [basePoint, xShift, hh]

private theorem local_left_touch (i : Fin 26) {a b : Local} {z : Plane}
    (he : (a,b) ∈ localEdges)
    (hz : z ∈ segment ℝ (euclid (basePoint i a)) (euclid (basePoint i b)))
    (hx : z 0 = 24 * (i.val : ℝ)) :
    (a = 0 ∨ b = 0) ∧ z = euclid (basePoint i 0) := by
  have hl := (coordinate_bounds 0 hz).1
  change ((min (24 * (i.val : ℤ) + (localPoint a).1)
    (24 * (i.val : ℤ) + (localPoint b).1) : ℤ) : ℝ) ≤ z 0 at hl
  rw [hx] at hl
  have hl' : min (24 * (i.val : ℤ) + (localPoint a).1)
    (24 * (i.val : ℤ) + (localPoint b).1) ≤ 24 * (i.val : ℤ) := by
    apply (Int.cast_le (R := ℝ)).mp
    simpa only [Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using hl
  have ha := point_x_interval a
  have hb := point_x_interval b
  have heither : (localPoint a).1 = 0 ∨ (localPoint b).1 = 0 := by omega
  have ha' := (left_coordinate a).mp
  have hb' := (left_coordinate b).mp
  refine ⟨heither.imp ha' hb', ?_⟩
  rcases heither with ha0 | hb0
  · have hpt : z 0 = ((basePoint i a).1 : ℝ) := by
      change z 0 = ((24 * (i.val : ℤ) + (localPoint a).1 : ℤ) : ℝ)
      rw [ha0]; simpa using hx
    rw [← ha' ha0]
    exact point_of_x_eq (basePoint_dx i he) hz hpt
  · have hpt : z 0 = ((basePoint i b).1 : ℝ) := by
      change z 0 = ((24 * (i.val : ℤ) + (localPoint b).1 : ℤ) : ℝ)
      rw [hb0]; simpa using hx
    rw [segment_symm] at hz
    rw [← hb' hb0]
    exact point_of_x_eq (basePoint_dx i he).symm hz hpt

private theorem local_right_touch (i : Fin 26) {a b : Local} {z : Plane}
    (he : (a,b) ∈ localEdges)
    (hz : z ∈ segment ℝ (euclid (basePoint i a)) (euclid (basePoint i b)))
    (hx : z 0 = 24 * (i.val : ℝ) + 24) :
    (a = 38 ∨ b = 38) ∧ z = euclid (basePoint i 38) := by
  have hu := (coordinate_bounds 0 hz).2
  change z 0 ≤ ((max (24 * (i.val : ℤ) + (localPoint a).1)
    (24 * (i.val : ℤ) + (localPoint b).1) : ℤ) : ℝ) at hu
  rw [hx] at hu
  have hu' : 24 * (i.val : ℤ) + 24 ≤ max (24 * (i.val : ℤ) + (localPoint a).1)
    (24 * (i.val : ℤ) + (localPoint b).1) := by
    apply (Int.cast_le (R := ℝ)).mp
    simpa only [Int.cast_add, Int.cast_mul, Int.cast_ofNat, Int.cast_natCast] using hu
  have ha := point_x_interval a
  have hb := point_x_interval b
  have heither : (localPoint a).1 = 24 ∨ (localPoint b).1 = 24 := by omega
  have ha' := (right_coordinate a).mp
  have hb' := (right_coordinate b).mp
  refine ⟨heither.imp ha' hb', ?_⟩
  rcases heither with ha24 | hb24
  · have hpt : z 0 = ((basePoint i a).1 : ℝ) := by
      change z 0 = ((24 * (i.val : ℤ) + (localPoint a).1 : ℤ) : ℝ)
      rw [ha24]; simpa using hx
    rw [← ha' ha24]
    exact point_of_x_eq (basePoint_dx i he) hz hpt
  · have hpt : z 0 = ((basePoint i b).1 : ℝ) := by
      change z 0 = ((24 * (i.val : ℤ) + (localPoint b).1 : ℤ) : ℝ)
      rw [hb24]; simpa using hx
    rw [segment_symm] at hz
    rw [← hb' hb24]
    exact point_of_x_eq (basePoint_dx i he).symm hz hpt

private theorem basePoint_euclid (i : Fin 26) (j : Local) :
    euclid (basePoint i j) = actual (24 * (i.val : ℝ)) 0 + euclid (localPoint j) := by
  apply plane_ext
  · change ((24 * (i.val : ℤ) + (localPoint j).1 : ℤ) : ℝ) =
      24 * (i.val : ℝ) + (localPoint j).1
    push_cast
    norm_num
  · change ((localPoint j).2 : ℝ) = 0 + (localPoint j).2
    ring

private theorem unshift_segment (i : Fin 26) {a b : Local} {z : Plane}
    (h : z ∈ segment ℝ (euclid (basePoint i a)) (euclid (basePoint i b))) :
    z - actual (24 * (i.val : ℝ)) 0 ∈ segment ℝ (euclid (localPoint a)) (euclid (localPoint b)) := by
  rw [basePoint_euclid, basePoint_euclid] at h
  apply (mem_segment_translate ℝ (actual (24 * (i.val : ℝ)) 0)).mp
  rwa [show actual (24 * (i.val : ℝ)) 0 + (z - actual (24 * (i.val : ℝ)) 0) = z by abel]

private theorem basePoint_bounds (i : Fin 26) (a : Local) :
    24 * (i.val : ℤ) ≤ (basePoint i a).1 ∧ (basePoint i a).1 ≤ 24 * (i.val : ℤ) + 24 := by
  have h := point_x_interval a
  change 24 * (i.val : ℤ) ≤ 24 * (i.val : ℤ) + (localPoint a).1 ∧ _
  change _ ∧ 24 * (i.val : ℤ) + (localPoint a).1 ≤ 24 * (i.val : ℤ) + 24
  omega

private theorem adjacent_block_endpoint (i j : Fin 26) (h : j.val = i.val + 1) :
    atBlock i 38 = atBlock j 0 := by
  apply congrArg Sum.inr
  apply Fin.ext
  change 38 * i.val + 38 = 38 * j.val + 0
  omega

private theorem basePoint_inj {i j : Fin 26} {a b : Local}
    (h : basePoint i a = basePoint j b) : atBlock i a = atBlock j b := by
  have hx := congrArg Prod.fst h
  have ⟨hal, har⟩ := basePoint_bounds i a
  have ⟨hbl, hbr⟩ := basePoint_bounds j b
  change 24 * (i.val : ℤ) ≤ 24 * (i.val : ℤ) + (localPoint a).1 at hal
  change 24 * (i.val : ℤ) + (localPoint a).1 ≤ 24 * (i.val : ℤ) + 24 at har
  change 24 * (j.val : ℤ) ≤ 24 * (j.val : ℤ) + (localPoint b).1 at hbl
  change 24 * (j.val : ℤ) + (localPoint b).1 ≤ 24 * (j.val : ℤ) + 24 at hbr
  change 24 * (i.val : ℤ) + (localPoint a).1 =
    24 * (j.val : ℤ) + (localPoint b).1 at hx
  by_cases hij : i = j
  · subst j
    have hp : localPoint a = localPoint b := by
      apply Prod.ext
      · change 24 * (i.val : ℤ) + (localPoint a).1 =
          24 * (i.val : ℤ) + (localPoint b).1 at hx
        omega
      · have hy := congrArg Prod.snd h
        exact hy
    rw [local_injective hp]
  · have hval : i.val ≠ j.val := fun he => hij (Fin.ext he)
    rcases lt_or_gt_of_ne hval with hlt | hgt
    · have hj : j.val = i.val + 1 := by omega
      have ha : (localPoint a).1 = 24 := by
        change 24 * (i.val : ℤ) + (localPoint a).1 =
          24 * (j.val : ℤ) + (localPoint b).1 at hx
        have hb := point_x_interval b
        omega
      have hb : (localPoint b).1 = 0 := by
        change 24 * (i.val : ℤ) + (localPoint a).1 =
          24 * (j.val : ℤ) + (localPoint b).1 at hx
        omega
      rw [(right_coordinate a).mp ha, (left_coordinate b).mp hb]
      exact adjacent_block_endpoint i j hj
    · have hi : i.val = j.val + 1 := by omega
      have hb : (localPoint b).1 = 24 := by
        change 24 * (i.val : ℤ) + (localPoint a).1 =
          24 * (j.val : ℤ) + (localPoint b).1 at hx
        have ha := point_x_interval a
        omega
      have ha : (localPoint a).1 = 0 := by
        change 24 * (i.val : ℤ) + (localPoint a).1 =
          24 * (j.val : ℤ) + (localPoint b).1 at hx
        omega
      rw [(left_coordinate a).mp ha, (right_coordinate b).mp hb]
      exact (adjacent_block_endpoint j i hi).symm

private theorem every_line_point (v : Line) : ∃ i j, block i j = v := by
  by_cases hv : v.val < 988
  · refine ⟨⟨v.val / 38, by omega⟩, ⟨v.val % 38, by omega⟩, ?_⟩
    exact Fin.ext (by change 38 * (v.val / 38) + v.val % 38 = v.val; omega)
  · exact ⟨25, 38, Fin.ext (by change 988 = v.val; have := v.isLt; omega)⟩

private theorem local_intersection_ordered {i j : Fin 26} {a b c d : Local} {z : Plane}
    (hij : i.val < j.val) (he : (a,b) ∈ localEdges) (hf : (c,d) ∈ localEdges)
    (ha : z ∈ segment ℝ (euclid (basePoint i a)) (euclid (basePoint i b)))
    (hb : z ∈ segment ℝ (euclid (basePoint j c)) (euclid (basePoint j d))) :
    (a = 38 ∨ b = 38) ∧ (c = 0 ∨ d = 0) ∧ i.val + 1 = j.val ∧ z = euclid (basePoint i 38) := by
  have h₁ := (local_x_bounds i ha).2
  have h₂ := (local_x_bounds j hb).1
  have hn : i.val + 1 ≤ j.val := by omega
  have hn' : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hn
  have hxi : z 0 = 24 * (i.val : ℝ) + 24 := by linarith
  have hxj : z 0 = 24 * (j.val : ℝ) := by linarith
  have hc : (i.val : ℝ) + 1 = (j.val : ℝ) := by linarith
  have hval : i.val + 1 = j.val := by exact_mod_cast hc
  have hui := local_right_touch i he ha hxi
  have huj := local_left_touch j hf hb hxj
  exact ⟨hui.1, huj.1, hval, hui.2⟩

private theorem local_point_on_edge {i j : Fin 26} {a b c : Local}
    (he : (a,b) ∈ localEdges)
    (h : euclid (basePoint j c) ∈ segment ℝ (euclid (basePoint i a)) (euclid (basePoint i b))) :
    atBlock j c = atBlock i a ∨ atBlock j c = atBlock i b := by
  by_cases hij : i = j
  · subst j
    have ht := unshift_segment i h
    rw [basePoint_euclid] at ht
    rw [add_sub_cancel_left] at ht
    rcases certify_point (local_point_cert (a,b) he c) ht with hold | hold
    · exact Or.inl (congrArg (atBlock i) (local_injective hold))
    · exact Or.inr (congrArg (atBlock i) (local_injective hold))
  · have hn : i.val ≠ j.val := fun hs => hij (Fin.ext hs)
    have ⟨ha, hb⟩ := local_x_bounds i h
    have ⟨hc, hd⟩ := basePoint_bounds j c
    have hc' : 24 * (j.val : ℝ) ≤ ((basePoint j c).1 : ℝ) := by exact_mod_cast hc
    have hd' : ((basePoint j c).1 : ℝ) ≤ 24 * (j.val : ℝ) + 24 := by exact_mod_cast hd
    change 24 * (i.val : ℝ) ≤ ((basePoint j c).1 : ℝ) at ha
    change ((basePoint j c).1 : ℝ) ≤ 24 * (i.val : ℝ) + 24 at hb
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · have ht : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by
        exact_mod_cast (show i.val + 1 ≤ j.val by omega)
      have hxe : (euclid (basePoint j c)) 0 = 24 * (i.val : ℝ) + 24 := by
        change ((basePoint j c).1 : ℝ) = _
        linarith
      obtain ⟨ha', hb'⟩ := local_right_touch i he h hxe
      have hbase := basePoint_inj (euclid_injective hb')
      rcases ha' with ha' | hb'
      · exact Or.inl (by rw [ha']; exact hbase)
      · exact Or.inr (by rw [hb']; exact hbase)
    · have ht : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by
        exact_mod_cast (show j.val + 1 ≤ i.val by omega)
      have hxe : (euclid (basePoint j c)) 0 = 24 * (i.val : ℝ) := by
        change ((basePoint j c).1 : ℝ) = _
        linarith
      obtain ⟨ha', hb'⟩ := local_left_touch i he h hxe
      have hbase := basePoint_inj (euclid_injective hb')
      rcases ha' with ha' | hb'
      · exact Or.inl (by rw [ha']; exact hbase)
      · exact Or.inr (by rw [hb']; exact hbase)

private theorem local_intersection {i j : Fin 26} {a b c d : Local} {z : Plane}
    (he : (a,b) ∈ localEdges) (hf : (c,d) ∈ localEdges)
    (hne : s(atBlock i a, atBlock i b) ≠ s(atBlock j c, atBlock j d))
    (ha : z ∈ segment ℝ (euclid (basePoint i a)) (euclid (basePoint i b)))
    (hb : z ∈ segment ℝ (euclid (basePoint j c)) (euclid (basePoint j d))) :
    ∃ p : Local, (p = a ∨ p = b) ∧ (atBlock i p = atBlock j c ∨ atBlock i p = atBlock j d) ∧
      z = euclid (basePoint i p) := by
  by_cases hij : i = j
  · subst j
    have h₀ : ¬ (localPoint a = localPoint c ∧ localPoint b = localPoint d) := by
      intro ⟨h₁,h₂⟩
      exact hne (by rw [local_injective h₁, local_injective h₂])
    have h₁ : ¬ (localPoint a = localPoint d ∧ localPoint b = localPoint c) := by
      intro ⟨h₁,h₂⟩
      exact hne (by rw [local_injective h₁, local_injective h₂, Sym2.eq_swap])
    obtain ⟨p, hpab, hpcd, hEq⟩ :=
      certify_edges (local_pair_certificate (a,b) he (c,d) hf) ⟨h₀,h₁⟩
        (unshift_segment i ha) (unshift_segment i hb)
    have solve (u : Local) (hu : p = localPoint u) :
        (atBlock i u = atBlock i c ∨ atBlock i u = atBlock i d) ∧
          z = euclid (basePoint i u) := by
      rw [hu] at hpcd hEq
      refine ⟨hpcd.imp (fun h => congrArg (atBlock i) (local_injective h))
        (fun h => congrArg (atBlock i) (local_injective h)), ?_⟩
      rw [basePoint_euclid, ← hEq]
      abel
    rcases hpab with hp | hp
    · exact ⟨a, Or.inl rfl, (solve a hp).1, (solve a hp).2⟩
    · exact ⟨b, Or.inr rfl, (solve b hp).1, (solve b hp).2⟩
  · have hn : i.val ≠ j.val := fun hs => hij (Fin.ext hs)
    rcases lt_or_gt_of_ne hn with hlt | hgt
    · obtain ⟨hs, ht, hi, hz⟩ := local_intersection_ordered hlt he hf ha hb
      have hh := adjacent_block_endpoint i j hi.symm
      refine ⟨38, hs.imp Eq.symm Eq.symm, ?_, hz⟩
      rcases ht with ht | ht
      · exact Or.inl (by rw [ht]; exact hh)
      · exact Or.inr (by rw [ht]; exact hh)
    · obtain ⟨hs, ht, hi, hz⟩ := local_intersection_ordered hgt hf he hb ha
      have hh := adjacent_block_endpoint j i hi.symm
      refine ⟨0, ht.imp Eq.symm Eq.symm, ?_, ?_⟩
      · rcases hs with hs | hs
        · exact Or.inl (by rw [hs]; exact hh.symm)
        · exact Or.inr (by rw [hs]; exact hh.symm)
      · rw [hz, ← linePoint_block, ← linePoint_block]
        exact congrArg (euclid ∘ linePoint) (Sum.inr.inj hh)

private theorem upper_point (j : Local) (hj : j ∈ upper) :
    (localPoint j).2 = 0 ∨ (localPoint j).2 = 2 := by
  have h : ∀ j ∈ upper, (localPoint j).2 = 0 ∨ (localPoint j).2 = 2 := by decide
  exact h j hj

private theorem lower_point (j : Local) (hj : j ∈ lower) :
    (localPoint j).2 = 0 ∨ (localPoint j).2 = -2 := by
  have h : ∀ j ∈ lower, (localPoint j).2 = 0 ∨ (localPoint j).2 = -2 := by decide
  exact h j hj

private theorem upper_unique :
    ∀ a ∈ upper, ∀ b ∈ upper, (localPoint a).1 = (localPoint b).1 → a = b := by decide +kernel

private theorem lower_unique :
    ∀ a ∈ lower, ∀ b ∈ lower, (localPoint a).1 = (localPoint b).1 → a = b := by decide +kernel

private theorem local_cut :
    ∀ p : Local, (localPoint p).2 = 0 → ∀ e ∈ localEdges,
      (localPoint p).1 ≤ min (localPoint e.1).1 (localPoint e.2).1 ∨
      max (localPoint e.1).1 (localPoint e.2).1 ≤ (localPoint p).1 := by
  have h : (List.finRange 39).all (fun p => localEdges.all (fun e => decide (
      (localPoint p).2 = 0 →
      (localPoint p).1 ≤ min (localPoint e.1).1 (localPoint e.2).1 ∨
      max (localPoint e.1).1 (localPoint e.2).1 ≤ (localPoint p).1))) = true := by
    decide +kernel
  have hh := h
  simp only [List.all_eq_true, decide_eq_true_eq, List.mem_finRange, forall_true_left] at hh
  exact fun p hp e he => hh p e he hp

private theorem local_y_bounds (i : Fin 26) {a b : Local} {z : Plane}
    (h : z ∈ segment ℝ (euclid (basePoint i a)) (euclid (basePoint i b))) :
    -2 ≤ z 1 ∧ z 1 ≤ 2 := by
  obtain ⟨hl, hu⟩ := coordinate_bounds 1 h
  have ha := point_y_interval a
  have hb := point_y_interval b
  change ((min (localPoint a).2 (localPoint b).2 : ℤ) : ℝ) ≤ z 1 at hl
  change z 1 ≤ ((max (localPoint a).2 (localPoint b).2 : ℤ) : ℝ) at hu
  have hlo : (-2 : ℤ) ≤ min (localPoint a).2 (localPoint b).2 := by omega
  have hhi : max (localPoint a).2 (localPoint b).2 ≤ 2 := by omega
  exact ⟨le_trans (by simpa only [Int.cast_neg, Int.cast_ofNat] using
    (Int.cast_le.mpr hlo : (_ : ℝ) ≤ _)) hl,
    hu.trans (by simpa only [Int.cast_ofNat] using (Int.cast_le.mpr hhi : (_ : ℝ) ≤ _))⟩

private theorem cut_x_bounds {i j : Fin 26} {a b c : Local}
    (he : (a,b) ∈ localEdges) (hc : (localPoint c).2 = 0) :
    (basePoint j c).1 ≤ min (basePoint i a).1 (basePoint i b).1 ∨
      max (basePoint i a).1 (basePoint i b).1 ≤ (basePoint j c).1 := by
  by_cases h : i = j
  · subst j
    have hh := local_cut c hc (a,b) he
    unfold basePoint xShift
    dsimp at *
    omega
  · have hn : i.val ≠ j.val := fun hs => h (Fin.ext hs)
    have ⟨hal, har⟩ := basePoint_bounds i a
    have ⟨hbl, hbr⟩ := basePoint_bounds i b
    have ⟨hcl, hcr⟩ := basePoint_bounds j c
    omega

private theorem old_cut_touch {i j : Fin 26} {a b c : Local} {z : Plane}
    (he : (a,b) ∈ localEdges) (hc : (localPoint c).2 = 0)
    (hz : z ∈ segment ℝ (euclid (basePoint i a)) (euclid (basePoint i b)))
    (hx : z 0 = ((basePoint j c).1 : ℝ)) :
    ∃ p : Local, (p = a ∨ p = b) ∧ z = euclid (basePoint i p) := by
  have hh := cut_x_bounds (i := i) (j := j) he hc
  have ⟨hl, hu⟩ := coordinate_bounds 0 hz
  change ((min (basePoint i a).1 (basePoint i b).1 : ℤ) : ℝ) ≤ z 0 at hl
  change z 0 ≤ ((max (basePoint i a).1 (basePoint i b).1 : ℤ) : ℝ) at hu
  rw [hx] at hl hu
  have hl' : min (basePoint i a).1 (basePoint i b).1 ≤ (basePoint j c).1 := Int.cast_le.mp hl
  have hu' : (basePoint j c).1 ≤ max (basePoint i a).1 (basePoint i b).1 := Int.cast_le.mp hu
  have heither : (basePoint j c).1 = (basePoint i a).1 ∨
      (basePoint j c).1 = (basePoint i b).1 := by omega
  rcases heither with hal | hbl
  · rw [hal] at hx
    exact ⟨a, Or.inl rfl, point_of_x_eq (basePoint_dx i he) hz hx⟩
  · rw [hbl] at hx
    rw [segment_symm] at hz
    exact ⟨b, Or.inr rfl, point_of_x_eq (basePoint_dx i he).symm hz hx⟩

private def IsSign (s : ℝ) : Prop := s = 1 ∨ s = -1

private theorem sign_sq {s : ℝ} (hs : IsSign s) : s * s = 1 := by
  rcases hs with rfl | rfl <;> norm_num

private def projected (p : Point) : Plane :=
  if p.2 < 0 then warp (-1) p else warp 1 p

private theorem projection_sign {s : ℝ} {p : Point} (hs : IsSign s)
    (hp : 0 ≤ s * (p.2 : ℝ)) : projected p = warp s p := by
  rcases hs with rfl | rfl
  · have h : ¬ p.2 < 0 := by
      have h' : (0 : ℝ) ≤ p.2 := by simpa using hp
      exact not_lt_of_ge (by exact_mod_cast h')
    simp [projected, h]
  · have hh : (p.2 : ℝ) ≤ 0 := by linarith
    have h : p.2 ≤ 0 := by exact_mod_cast hh
    rcases lt_or_eq_of_le h with h | h
    · simp [projected, h]
    · simp [projected, warp, h]

private theorem project_unwarp (p : Point) {s : ℝ} (hp : 0 < 1 + s * (p.2 : ℝ)) :
    unwarp s (warp s p) = euclid p := by
  have hpos : 1 - s * ((p.2 : ℝ) / (1 + s * p.2)) = 1 / (1 + s * p.2) := by
    field_simp [hp.ne']
    ring
  apply plane_ext <;> simp only [unwarp, warp, euclid, actual_x, actual_y, hpos] <;>
    rw [div_div_eq_mul_div] <;> simp [hp.ne']

private def place : Vertex → Plane
  | .inl h => actual 0 (if h = 0 then 1 else -1)
  | .inr v => projected (linePoint v)

private theorem place_atBlock (i : Fin 26) (j : Local) :
    place (atBlock i j) = projected (basePoint i j) := by
  simp [place, atBlock, linePoint_block]

private theorem segment_half_plane {p q z : Plane} {s : ℝ}
    (hp : 0 ≤ s * p 1) (hq : 0 ≤ s * q 1)
    (hz : z ∈ segment ℝ p q) : 0 ≤ s * z 1 := by
  obtain ⟨a,b,ha,hb,_,he⟩ := hz
  have hy := congrArg (fun v : Plane => v 1) he
  change a * p 1 + b * q 1 = z 1 at hy
  rw [← hy]
  calc
    0 ≤ a * (s * p 1) + b * (s * q 1) :=
      add_nonneg (mul_nonneg ha hp) (mul_nonneg hb hq)
    _ = _ := by ring

private theorem warp_sign {s : ℝ} {p : Point} (hp : 0 ≤ s * (p.2 : ℝ)) :
    0 ≤ s * warp s p 1 := by
  change 0 ≤ s * ((p.2 : ℝ) / (1 + s * p.2))
  rw [← mul_div_assoc]
  exact div_nonneg hp (by linarith)

private theorem warp_lt_hub {s : ℝ} {p : Point} (hp : 0 ≤ s * (p.2 : ℝ)) :
    s * warp s p 1 < 1 := by
  change s * ((p.2 : ℝ) / (1 + s * p.2)) < 1
  rw [← mul_div_assoc]
  exact (div_lt_iff₀ (by linarith)).mpr (by linarith)

private theorem projected_local_edge {i : Fin 26} {a b : Local} {z : Plane}
    (he : (a,b) ∈ localEdges) (hz : z ∈ segment ℝ (place (atBlock i a)) (place (atBlock i b))) :
    ∃ s : ℝ, IsSign s ∧ 0 ≤ s * z 1 ∧ 0 < 1 - s * z 1 ∧
      unwarp s z ∈ segment ℝ (euclid (basePoint i a)) (euclid (basePoint i b)) := by
  have choose (s : ℝ) (hs : IsSign s) (ha : 0 ≤ s * ((basePoint i a).2 : ℝ))
      (hb : 0 ≤ s * ((basePoint i b).2 : ℝ)) :
      IsSign s ∧ 0 ≤ s * z 1 ∧ 0 < 1 - s * z 1 ∧
        unwarp s z ∈ segment ℝ (euclid (basePoint i a)) (euclid (basePoint i b)) := by
    rw [place_atBlock, place_atBlock, projection_sign hs ha, projection_sign hs hb] at hz
    have hs' := segment_half_plane (warp_sign ha) (warp_sign hb) hz
    exact ⟨hs, hs', unwarp_segment (by linarith) (by linarith) hz⟩
  rcases local_edge_y (a,b) he with ⟨ha,hb⟩ | ⟨ha,hb⟩
  · exact ⟨1, choose 1 (Or.inl rfl) (by simpa [basePoint, xShift] using (show (0 : ℝ) ≤ (localPoint a).2 by exact_mod_cast ha))
      (by simpa [basePoint, xShift] using (show (0 : ℝ) ≤ (localPoint b).2 by exact_mod_cast hb))⟩
  · exact ⟨-1, choose (-1) (Or.inr rfl)
      (by simpa [basePoint, xShift] using neg_nonneg.mpr (show ((localPoint a).2 : ℝ) ≤ 0 from by exact_mod_cast ha))
      (by simpa [basePoint, xShift] using neg_nonneg.mpr (show ((localPoint b).2 : ℝ) ≤ 0 from by exact_mod_cast hb))⟩

private theorem normalize_compatible {s t : ℝ} {z : Plane} (hs : IsSign s) (ht : IsSign t)
    (h₁ : 0 ≤ s * z 1) (h₂ : 0 ≤ t * z 1) :
    unwarp s z = unwarp t z := by
  by_cases hh : s = t
  · rw [hh]
  · apply unwarp_on_axis
    rcases hs with hs | hs <;> rcases ht with ht | ht
    · exact (hh (hs.trans ht.symm)).elim
    · rw [hs, one_mul] at h₁
      rw [ht, neg_one_mul] at h₂
      linarith
    · rw [hs, neg_one_mul] at h₁
      rw [ht, one_mul] at h₂
      linarith
    · exact (hh (hs.trans ht.symm)).elim

private theorem projected_eq_of_unwarp {s : ℝ} {p : Point} {z : Plane}
    (hs : IsSign s) (hz : 0 < 1 - s * z 1) (hside : 0 ≤ s * z 1)
    (he : unwarp s z = euclid p) : z = projected p := by
  have h := congrArg (fun v : Plane => v 1) he
  change z 1 / (1 - s * z 1) = (p.2 : ℝ) at h
  have hnonneg : 0 ≤ s * (p.2 : ℝ) := by
    rw [← h, ← mul_div_assoc]
    exact div_nonneg hside hz.le
  rw [projection_sign hs hnonneg]
  exact warp_of_unwarp_eq hz.ne' he

private theorem projected_local_intersection {i j : Fin 26} {a b c d : Local} {z : Plane}
    (he : (a,b) ∈ localEdges) (hf : (c,d) ∈ localEdges)
    (hne : s(atBlock i a, atBlock i b) ≠ s(atBlock j c, atBlock j d))
    (ha : z ∈ segment ℝ (place (atBlock i a)) (place (atBlock i b)))
    (hb : z ∈ segment ℝ (place (atBlock j c)) (place (atBlock j d))) :
    ∃ p : Vertex, (p = atBlock i a ∨ p = atBlock i b) ∧
      (p = atBlock j c ∨ p = atBlock j d) ∧ z = place p := by
  obtain ⟨s, hs, hside, hd, h₁⟩ := projected_local_edge he ha
  obtain ⟨t, ht, hside', _, h₂⟩ := projected_local_edge hf hb
  rw [← normalize_compatible hs ht hside hside'] at h₂
  obtain ⟨p, hpab, hpcd, hp⟩ := local_intersection he hf hne h₁ h₂
  refine ⟨atBlock i p, hpab.imp (congrArg (atBlock i)) (congrArg (atBlock i)), hpcd, ?_⟩
  rw [place_atBlock]
  exact projected_eq_of_unwarp hs hd hside hp

private theorem cut_x_unique :
    ∀ a b : Local, (localPoint a).2 = 0 → (localPoint a).1 = (localPoint b).1 → a = b := by
  have h : (List.finRange 39).all (fun a => (List.finRange 39).all (fun b =>
    decide ((localPoint a).2 = 0 → (localPoint a).1 = (localPoint b).1 → a = b))) = true := by
    decide +kernel
  simpa only [List.all_eq_true, decide_eq_true_eq, List.mem_finRange, forall_true_left] using h

private theorem base_x_eq_of_local_x_eq {i j : Fin 26} {a b : Local}
    (h : (basePoint i a).1 = (basePoint j b).1)
    (hlocal : (localPoint a).1 = (localPoint b).1 → a = b) :
    atBlock i a = atBlock j b := by
  by_cases hh : i = j
  · subst j
    apply congrArg (atBlock i)
    apply hlocal
    change 24 * (i.val : ℤ) + (localPoint a).1 = 24 * (i.val : ℤ) + (localPoint b).1 at h
    omega
  · apply basePoint_inj
    refine Prod.ext h ?_
    have ⟨hal, har⟩ := basePoint_bounds i a
    have ⟨hbl, hbr⟩ := basePoint_bounds j b
    have hn : i.val ≠ j.val := fun e => hh (Fin.ext e)
    have ha := point_x_interval a
    have hb := point_x_interval b
    change 24 * (i.val : ℤ) + (localPoint a).1 = 24 * (j.val : ℤ) + (localPoint b).1 at h
    change 24 * (i.val : ℤ) ≤ 24 * (i.val : ℤ) + (localPoint a).1 at hal
    change 24 * (i.val : ℤ) + (localPoint a).1 ≤ 24 * (i.val : ℤ) + 24 at har
    change 24 * (j.val : ℤ) ≤ 24 * (j.val : ℤ) + (localPoint b).1 at hbl
    change 24 * (j.val : ℤ) + (localPoint b).1 ≤ 24 * (j.val : ℤ) + 24 at hbr
    change (localPoint a).2 = (localPoint b).2
    rcases lt_or_gt_of_ne hn with hn | hn
    · rw [(right_coordinate a).mp (by omega), (left_coordinate b).mp (by omega)]
      rfl
    · rw [(left_coordinate a).mp (by omega), (right_coordinate b).mp (by omega)]
      rfl

private def hubSide (h : Fin 2) : ℝ := if h = 0 then 1 else -1

private def onBoundary (h : Fin 2) (j : Local) : Prop :=
  if h = 0 then j ∈ upper else j ∈ lower

private theorem hub_sign (h : Fin 2) : IsSign (hubSide h) := by
  fin_cases h <;> simp [hubSide, IsSign]

private theorem place_hub (h : Fin 2) : place (hub h) = actual 0 (hubSide h) := rfl

private theorem boundary_pos {h : Fin 2} {n : Fin 26} {j : Local}
    (hb : onBoundary h j) : 0 ≤ hubSide h * ((basePoint n j).2 : ℝ) := by
  fin_cases h
  · have hb' : j ∈ upper := by simpa [onBoundary] using hb
    rcases upper_point j hb' with h | h <;> simp [hubSide, basePoint, xShift, h]
  · have hb' : j ∈ lower := by simpa [onBoundary] using hb
    rcases lower_point j hb' with h | h <;> simp [hubSide, basePoint, xShift, h]

private theorem boundary_height {h : Fin 2} {n : Fin 26} {j : Local}
    (hb : onBoundary h j) : (localPoint j).2 = 0 ∨ hubSide h * ((basePoint n j).2 : ℝ) = 2 := by
  fin_cases h
  · have hb' : j ∈ upper := by simpa [onBoundary] using hb
    exact (upper_point j hb').imp id (fun h => by simp [hubSide, basePoint, xShift, h])
  · have hb' : j ∈ lower := by simpa [onBoundary] using hb
    exact (lower_point j hb').imp id (fun h => by simp [hubSide, basePoint, xShift, h])

private theorem boundary_x_eq {h : Fin 2} {i j : Fin 26} {a b : Local}
    (ha : onBoundary h a) (hb : onBoundary h b) (hx : (basePoint i a).1 = (basePoint j b).1) :
    atBlock i a = atBlock j b := by
  apply base_x_eq_of_local_x_eq hx
  fin_cases h
  · exact upper_unique a (by simpa [onBoundary] using ha) b (by simpa [onBoundary] using hb)
  · exact lower_unique a (by simpa [onBoundary] using ha) b (by simpa [onBoundary] using hb)

private theorem ray_half_plane {s : ℝ} {p : Point} {z : Plane}
    (hs : IsSign s) (hp : 0 ≤ s * (p.2 : ℝ))
    (hz : z ∈ segment ℝ (warp s p) (actual 0 s)) : 0 ≤ s * z 1 := by
  refine segment_half_plane (warp_sign hp) ?_ hz
  change 0 ≤ s * s
  rw [sign_sq hs]
  exact zero_le_one

private theorem ray_coordinates {s : ℝ} {p : Point} {z : Plane}
    (hs : IsSign s) (hp : 0 ≤ s * (p.2 : ℝ))
    (hz : z ∈ segment ℝ (warp s p) (actual 0 s)) :
    z = actual 0 s ∨
      (0 < 1 - s * z 1 ∧ (unwarp s z) 0 = p.1 ∧ s * (p.2 : ℝ) ≤ s * (unwarp s z) 1) := by
  obtain ⟨a,b,ha,hb,hab,he⟩ := hz
  have hx := congrArg (fun v : Plane => v 0) he
  have hy := congrArg (fun v : Plane => v 1) he
  change a * ((p.1 : ℝ) / (1 + s * p.2)) + b * 0 = z 0 at hx
  change a * ((p.2 : ℝ) / (1 + s * p.2)) + b * s = z 1 at hy
  by_cases h0 : a = 0
  · have h1 : b = 1 := by linarith
    exact Or.inl (plane_ext (by simpa [h0] using hx.symm) (by simpa [h0,h1] using hy.symm))
  · let U : ℝ := 1 + s * (p.2 : ℝ)
    let D : ℝ := 1 - s * z 1
    have hu : 0 < U := by dsimp [U]; linarith
    have hnorm : 1 - s * ((p.2 : ℝ) / U) = 1 / U := by
      field_simp [hu.ne']
      dsimp [U]
      ring
    have hd : D = a / U := by
      change 1 - s * z 1 = _
      rw [← hy]
      change 1 - s * (a * ((p.2 : ℝ) / U) + b * s) = _
      calc
        _ = a * (1 - s * ((p.2 : ℝ) / U)) := by
          nlinarith [congrArg (b * ·) (sign_sq hs)]
        _ = _ := by rw [hnorm]; ring
    have hD : 0 < D := by
      rw [hd]
      exact div_pos (lt_of_le_of_ne ha (Ne.symm h0)) hu
    right
    refine ⟨hD, ?_, ?_⟩
    · change z 0 / D = _
      apply (div_eq_iff hD.ne').mpr
      rw [hd, ← hx]
      change a * ((p.1 : ℝ) / U) + b * 0 = _
      ring
    · change _ ≤ s * (z 1 / D)
      rw [← mul_div_assoc]
      apply (le_div_iff₀ hD).mpr
      calc
        s * (p.2 : ℝ) * D = s * (a * ((p.2 : ℝ) / U)) := by rw [hd]; ring
        _ ≤ s * (a * ((p.2 : ℝ) / U)) + b := by linarith
        _ = s * z 1 := by
          rw [← hy]
          change _ = s * (a * ((p.2 : ℝ) / U) + b * s)
          nlinarith [congrArg (b * ·) (sign_sq hs)]

private theorem boundary_ray {h : Fin 2} {i : Fin 26} {j : Local} {z : Plane}
    (hj : onBoundary h j)
    (hz : z ∈ segment ℝ (place (hub h)) (place (atBlock i j))) :
    0 ≤ hubSide h * z 1 ∧
    (z = place (hub h) ∨ (0 < 1 - hubSide h * z 1 ∧
      (unwarp (hubSide h) z) 0 = (basePoint i j).1 ∧
      hubSide h * ((basePoint i j).2 : ℝ) ≤ hubSide h * (unwarp (hubSide h) z) 1)) := by
  have hp := boundary_pos (n := i) hj
  rw [segment_symm, place_hub, place_atBlock, projection_sign (hub_sign h) hp] at hz
  exact ⟨ray_half_plane (hub_sign h) hp hz, ray_coordinates (hub_sign h) hp hz⟩

private theorem cast_x_eq {a b : Point} (h : (a.1 : ℝ) = (b.1 : ℝ)) : a.1 = b.1 :=
  Int.cast_injective h

private theorem local_ray_intersection {i j : Fin 26} {a b c : Local} {h : Fin 2} {z : Plane}
    (he : (a,b) ∈ localEdges) (hc : onBoundary h c)
    (h₁ : z ∈ segment ℝ (place (atBlock i a)) (place (atBlock i b)))
    (h₂ : z ∈ segment ℝ (place (hub h)) (place (atBlock j c))) :
    ∃ p : Vertex, (p = atBlock i a ∨ p = atBlock i b) ∧
      (p = hub h ∨ p = atBlock j c) ∧ z = place p := by
  obtain ⟨s, hs, hside, hden, hOld⟩ := projected_local_edge he h₁
  obtain ⟨hside', hhub | ⟨hd, hx, hy⟩⟩ := boundary_ray hc h₂
  · rw [hhub, place_hub] at hside hden
    change 0 ≤ s * hubSide h at hside
    change 0 < 1 - s * hubSide h at hden
    have hh := hub_sign h
    rcases hs with rfl | rfl <;> rcases hh with hh | hh <;>
      rw [hh] at hside hden
    all_goals norm_num at hside
    all_goals norm_num at hden
  · rw [normalize_compatible hs (hub_sign h) hside hside'] at hOld
    have hEq : unwarp (hubSide h) z = euclid (basePoint j c) := by
      rcases boundary_height (n := j) hc with hcut | houter
      · obtain ⟨u, _, hu⟩ := old_cut_touch he hcut hOld hx
        have heqX : ((basePoint j c).1 : ℝ) = ((basePoint i u).1 : ℝ) := by
          rw [← hx, hu]
          rfl
        have hpt : atBlock j c = atBlock i u :=
          base_x_eq_of_local_x_eq (cast_x_eq heqX) (cut_x_unique c u hcut)
        have heq : basePoint j c = basePoint i u := by
          rw [← linePoint_block, ← linePoint_block]
          exact congrArg linePoint (Sum.inr.inj hpt)
        rw [hu, heq]
      · rw [houter] at hy
        have ⟨hmin, hmax⟩ := local_y_bounds i hOld
        have hyEq : (unwarp (hubSide h) z) 1 = ((basePoint j c).2 : ℝ) := by
          rcases hub_sign h with hsgn | hsgn <;> rw [hsgn] at houter hy hmin hmax ⊢ <;> linarith
        exact plane_ext hx hyEq
    rw [hEq] at hOld
    refine ⟨atBlock j c, local_point_on_edge he hOld, Or.inr rfl, ?_⟩
    rw [place_atBlock]
    exact projected_eq_of_unwarp (hub_sign h) hd hside' hEq

private theorem ray_intersection {i j : Fin 26} {a b : Local} {h k : Fin 2} {z : Plane}
    (ha : onBoundary h a) (hb : onBoundary k b)
    (hne : s(hub h, atBlock i a) ≠ s(hub k, atBlock j b))
    (h₁ : z ∈ segment ℝ (place (hub h)) (place (atBlock i a)))
    (h₂ : z ∈ segment ℝ (place (hub k)) (place (atBlock j b))) :
    ∃ p : Vertex, (p = hub h ∨ p = atBlock i a) ∧
      (p = hub k ∨ p = atBlock j b) ∧ z = place p := by
  obtain ⟨hs, ha'⟩ := boundary_ray ha h₁
  obtain ⟨ht, hb'⟩ := boundary_ray hb h₂
  by_cases he : h = k
  · subst k
    rcases ha' with ha' | ⟨_, hax, _⟩
    · exact ⟨hub h, Or.inl rfl, Or.inl rfl, ha'⟩
    rcases hb' with hb' | ⟨_, hbx, _⟩
    · exact ⟨hub h, Or.inl rfl, Or.inl rfl, hb'⟩
    have hEq := boundary_x_eq ha hb (cast_x_eq (hax.symm.trans hbx))
    exact (hne (by rw [hEq])).elim
  · have haxis : z 1 = 0 := by
      fin_cases h <;> fin_cases k <;> simp [hubSide] at hs ht he <;> linarith
    have hnot (t : Fin 2) : z ≠ place (hub t) := by
      intro hh
      have ht' := congrArg (fun v : Plane => v 1) hh
      change z 1 = hubSide t at ht'
      rw [haxis] at ht'
      rcases hub_sign t with h | h <;> rw [h] at ht' <;> norm_num at ht'
    obtain ⟨hd, hx, hy⟩ := ha'.resolve_left (hnot h)
    obtain ⟨hd', hx', hy'⟩ := hb'.resolve_left (hnot k)
    have hu (t : Fin 2) : (unwarp (hubSide t) z) 1 = 0 := by simp [unwarp,haxis]
    rw [hu h, mul_zero] at hy
    rw [hu k, mul_zero] at hy'
    have hzeroa : (unwarp (hubSide h) z) 1 = ((basePoint i a).2 : ℝ) := by
      rw [hu]
      have haP := boundary_pos (n := i) ha
      rcases hub_sign h with h | h <;> rw [h] at hy haP <;> linarith
    have hzerob : (unwarp (hubSide k) z) 1 = ((basePoint j b).2 : ℝ) := by
      rw [hu]
      have hbP := boundary_pos (n := j) hb
      rcases hub_sign k with k | k <;> rw [k] at hy' hbP <;> linarith
    have haBase : unwarp (hubSide h) z = euclid (basePoint i a) := plane_ext hx hzeroa
    have hbBase : unwarp (hubSide k) z = euclid (basePoint j b) := plane_ext hx' hzerob
    have hEq : basePoint i a = basePoint j b :=
      euclid_injective (haBase.symm.trans ((unwarp_on_axis haxis).trans hbBase))
    refine ⟨atBlock i a, Or.inr rfl, Or.inr (basePoint_inj hEq), ?_⟩
    rw [place_atBlock]
    exact projected_eq_of_unwarp (hub_sign h) hd hs haBase

private theorem point_sign (p : Point) :
    ∃ s : ℝ, IsSign s ∧ 0 ≤ s * (p.2 : ℝ) ∧ projected p = warp s p := by
  by_cases hp : p.2 < 0
  · have hp0 : (p.2 : ℝ) ≤ 0 := by exact_mod_cast hp.le
    have hs : 0 ≤ (-1 : ℝ) * p.2 := by linarith
    exact ⟨-1, Or.inr rfl, hs, projection_sign (Or.inr rfl) hs⟩
  · have hs : 0 ≤ (1 : ℝ) * p.2 := by
      rw [one_mul]
      exact_mod_cast not_lt.mp hp
    exact ⟨1, Or.inl rfl, hs, projection_sign (Or.inl rfl) hs⟩

private theorem place_injective : Function.Injective place := by
  have noTouch (h : Fin 2) (i : Fin 26) (j : Local) :
      place (hub h) ≠ place (atBlock i j) := by
    intro he
    obtain ⟨s, hs, hside, hpr⟩ := point_sign (basePoint i j)
    rw [place_hub, place_atBlock, hpr] at he
    have hy := congrArg (fun v : Plane => v 1) he
    change hubSide h = (warp s (basePoint i j)) 1 at hy
    have hn := warp_sign hside
    have hp := warp_lt_hub hside
    rw [← hy] at hn hp
    rcases hub_sign h with hh | hh <;> rcases hs with rfl | rfl <;>
      rw [hh] at hn hp
    all_goals norm_num at hn
    all_goals norm_num at hp
  intro u v he
  rcases u with h | u <;> rcases v with k | v
  · have hy := congrArg (fun w : Plane => w 1) he
    change hubSide h = hubSide k at hy
    congr 1
    fin_cases h <;> fin_cases k <;> simp [hubSide] at hy ⊢ <;> linarith
  · obtain ⟨i,j,rfl⟩ := every_line_point v
    exact (noTouch h i j he).elim
  · obtain ⟨i,j,rfl⟩ := every_line_point u
    exact (noTouch k i j he.symm).elim
  · obtain ⟨i,a,rfl⟩ := every_line_point u
    obtain ⟨j,b,rfl⟩ := every_line_point v
    change place (atBlock i a) = place (atBlock j b) at he
    rw [place_atBlock, place_atBlock] at he
    obtain ⟨s, hs, hside, hpr⟩ := point_sign (basePoint i a)
    obtain ⟨t, ht, hside', hpr'⟩ := point_sign (basePoint j b)
    rw [hpr,hpr'] at he
    have hh := normalize_compatible hs ht (warp_sign hside) (he ▸ warp_sign hside')
    have heq : euclid (basePoint i a) = euclid (basePoint j b) := by
      rw [project_unwarp _ (by linarith)] at hh
      rw [he, project_unwarp _ (by linarith)] at hh
      exact hh
    exact basePoint_inj (euclid_injective heq)

private inductive GraphSegment : Vertex → Vertex → Prop
  | localEdge (i : Fin 26) (a b : Local) (he : (a,b) ∈ localEdges) :
      GraphSegment (atBlock i a) (atBlock i b)
  | ray (h : Fin 2) (i : Fin 26) (a : Local) (he : onBoundary h a) :
      GraphSegment (hub h) (atBlock i a)

private theorem graph_segment {u v : Vertex} (h : (u,v) ∈ allEdges) : GraphSegment u v := by
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp h
  simp only [edgesAt, List.mem_append, List.mem_map] at hi
  rcases hi with (⟨⟨a,b⟩, ha, hp⟩ | ⟨a, ha, hp⟩) | ⟨a, ha, hp⟩
  · injection hp with hu hv
    subst u v
    exact .localEdge i a b ha
  · injection hp with hu hv
    subst u v
    exact .ray 0 i a (by simpa [onBoundary] using ha)
  · injection hp with hu hv
    subst u v
    exact .ray 1 i a (by simpa [onBoundary] using ha)

private theorem graph_segments_meet {a b c d : Vertex} {z : Plane}
    (h₁ : GraphSegment a b) (h₂ : GraphSegment c d)
    (hne : s(a,b) ≠ s(c,d))
    (ha : z ∈ segment ℝ (place a) (place b)) (hb : z ∈ segment ℝ (place c) (place d)) :
    ∃ p : Vertex, (p = a ∨ p = b) ∧ (p = c ∨ p = d) ∧ z = place p := by
  cases h₁ with
  | localEdge i a b he =>
    cases h₂ with
    | localEdge j c d hf => exact projected_local_intersection he hf hne ha hb
    | ray h j c hf => exact local_ray_intersection he hf ha hb
  | ray h i a he =>
    cases h₂ with
    | localEdge j c d hf =>
      obtain ⟨p,hp,hq,hz⟩ := local_ray_intersection hf he hb ha
      exact ⟨p,hq,hp,hz⟩
    | ray k j c hf => exact ray_intersection he hf hne ha hb

/-- A straight-line realization of the chain and its two fans, by projecting the two half-planes
so their vertical rays converge to their respective hubs. -/
theorem rational_planarity :
    ∃ pos : Vertex → EuclideanSpace ℝ (Fin 2), Function.Injective pos ∧
      ∀ u v x y : Vertex, G.Adj u v → G.Adj x y → s(u,v) ≠ s(x,y) →
        segment ℝ (pos u) (pos v) ∩ segment ℝ (pos x) (pos y) ⊆
          pos '' (({u,v} : Set Vertex) ∩ {x,y}) := by
  refine ⟨place, place_injective, ?_⟩
  intro u v x y huv hxy hne z ⟨hz₁,hz₂⟩
  have build (a b c d : Vertex) (ha : (a,b) ∈ allEdges) (hb : (c,d) ∈ allEdges)
      (hn : s(a,b) ≠ s(c,d))
      (h₁ : z ∈ segment ℝ (place a) (place b)) (h₂ : z ∈ segment ℝ (place c) (place d)) :
      z ∈ place '' (({a,b} : Set Vertex) ∩ {c,d}) := by
    obtain ⟨p,hp,hq,he⟩ := graph_segments_meet (graph_segment ha) (graph_segment hb) hn h₁ h₂
    exact ⟨p, by simpa only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_singleton_iff]
      using And.intro hp hq, he.symm⟩
  rcases huv.2 with ha | ha <;> rcases hxy.2 with hb | hb
  · exact build u v x y ha hb hne hz₁ hz₂
  · rw [segment_symm] at hz₂
    have hh := build u v y x ha hb (by rwa [(Sym2.eq_swap : s(y,x) = s(x,y))]) hz₁ hz₂
    simpa only [Set.pair_comm y x] using hh
  · rw [segment_symm] at hz₁
    have hh := build v u x y ha hb (by rwa [(Sym2.eq_swap : s(v,u) = s(u,v))]) hz₁ hz₂
    simpa only [Set.pair_comm v u] using hh
  · rw [segment_symm] at hz₁ hz₂
    have hh := build v u y x ha hb (by rwa [(Sym2.eq_swap : s(v,u) = s(u,v)), (Sym2.eq_swap : s(y,x) = s(x,y))]) hz₁ hz₂
    simpa only [Set.pair_comm v u, Set.pair_comm y x] using hh

end

end PrismCounterexample

namespace PrismCounterexample

open SimpleGraph

section

variable {V W : Type*} [Fintype V] [Fintype W]
variable (C : SimpleGraph V) [DecidableRel C.Adj] (e : W ↪ V)

private theorem comapNeighbors_subset (v : W) :
    ((C.comap e).neighborFinset v).map e ⊆ C.neighborFinset (e v) := by
  intro w hw
  obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hw
  exact (C.mem_neighborFinset (e v) (e z)).mpr ((C.comap e).mem_neighborFinset v z |>.mp hz)

/-- An induced restriction cannot increase any degree. -/
theorem comapDegree_le (v : W) : (C.comap e).degree v ≤ C.degree (e v) := by
  simpa only [Finset.card_map, card_neighborFinset_eq_degree] using
    Finset.card_le_card (comapNeighbors_subset C e v)

/-- A vertex of an induced restriction preserves its degree when all its neighbors are retained. -/
theorem comapDegree_eq_of_range (v : W)
    (hv : ∀ z, C.Adj (e v) z → z ∈ Set.range e) :
    (C.comap e).degree v = C.degree (e v) := by
  have hrev : C.neighborFinset (e v) ⊆ ((C.comap e).neighborFinset v).map e := by
    intro z hz
    have hadj := (C.mem_neighborFinset (e v) z).mp hz
    obtain ⟨w,rfl⟩ := hv z hadj
    exact Finset.mem_map.mpr ⟨w, ((C.comap e).mem_neighborFinset v w).mpr hadj, rfl⟩
  simpa only [Finset.card_map, card_neighborFinset_eq_degree] using
    congrArg Finset.card (Finset.Subset.antisymm (comapNeighbors_subset C e v) hrev)

omit [Fintype V] [DecidableRel C.Adj] in
private theorem stays {T : Finset V} {u v : V} (w : C.Walk u v)
    (closed : ∀ x ∈ T, ∀ y, C.Adj x y → y ∈ T) : u ∈ T → v ∈ T := by
  induction w with
  | nil => exact id
  | cons h _ ih => exact fun hu => ih (closed _ hu _ h)

/-- In a proper induced restriction of a connected 2-regular graph, a nonempty set closed
under restricted adjacency contains a vertex of restricted degree less than two. -/
theorem comapDegree_lt_two_of_closed (hC : C.Connected) (degC : ∀ x, C.degree x = 2)
    (out : V) (hout : out ∉ Set.range e) (S : Finset W) (hS : S.Nonempty)
    (closed : ∀ v ∈ S, ∀ w, (C.comap e).Adj v w → w ∈ S) :
    ∃ v ∈ S, (C.comap e).degree v < 2 := by
  by_contra! hdeg
  have edgeImage (v : W) (hv : v ∈ S) :
      ((C.comap e).neighborFinset v).map e = C.neighborFinset (e v) := by
    apply Finset.eq_of_subset_of_card_le (comapNeighbors_subset C e v)
    simpa only [Finset.card_map, card_neighborFinset_eq_degree, degC] using hdeg v hv
  have imageClosed : ∀ x ∈ S.map e, ∀ y, C.Adj x y → y ∈ S.map e := by
    intro x hx y hadj
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hx
    have h : y ∈ ((C.comap e).neighborFinset v).map e := by
      rw [edgeImage v hv]
      exact (C.mem_neighborFinset (e v) y).mpr hadj
    obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp h
    exact Finset.mem_map.mpr ⟨w,closed v hv w (((C.comap e).mem_neighborFinset v w).mp hw),rfl⟩
  obtain ⟨v,hv⟩ := hS
  obtain ⟨walk⟩ := hC (e v) out
  have hout' := stays C walk imageClosed (Finset.mem_map.mpr ⟨v,hv,rfl⟩)
  obtain ⟨w,_,hw⟩ := Finset.mem_map.mp hout'
  exact hout ⟨w,hw⟩

end

end PrismCounterexample

namespace PrismCounterexample

open SimpleGraph Finset


abbrev PrismVertex := Vertex × Fin 2
abbrev PairPrismVertex := PairVertex × Fin 2

theorem cycleSubgraph (h : prism.IsHamiltonian) :
    ∃ C : SimpleGraph PrismVertex, C ≤ prism ∧ C.Connected ∧
      ∀ v, (C.neighborSet v).ncard = 2 := by
  have size : Fintype.card PrismVertex ≠ 1 := by simp [Fintype.card_prod, Fintype.card_sum]
  obtain ⟨v, p, hp⟩ := h size
  have spanning : p.toSubgraph.IsSpanning := fun w =>
    p.mem_verts_toSubgraph.mpr (hp.mem_support w)
  use p.toSubgraph.spanningCoe
  exact ⟨p.toSubgraph.spanningCoe_le,
    (p.toSubgraph.spanningCoeEquivCoeOfSpanning spanning).symm.connected_iff.mp
      p.toSubgraph_connected,
    fun w => hp.isCycle.ncard_neighborSet_toSubgraph_eq_two (hp.mem_support w)⟩

def pairLine (i : Fin 9) (v : PairVertex) : Line :=
  ⟨114 * i.val + v.val, by omega⟩

def pairBase (i : Fin 9) (v : PairVertex) : Vertex := .inr (pairLine i v)

def embedPair (i : Fin 9) (v : PairPrismVertex) : PrismVertex :=
  (pairBase i v.1, v.2)

theorem pair_base_injective (i : Fin 9) : Function.Injective (pairBase i) := by
  intro v w eq
  have ev := congrArg Fin.val (Sum.inr.inj eq)
  exact Fin.ext (by simpa [pairLine] using ev)

theorem pair_injective (i : Fin 9) : Function.Injective (embedPair i) := by
  intro v w eq
  exact Prod.ext (pair_base_injective i (congrArg Prod.fst eq)) (congrArg (Prod.snd : PrismVertex → Fin 2) eq)

theorem pair_disjoint {i j : Fin 9} {v w : PairPrismVertex}
    (h : embedPair i v = embedPair j w) : i = j := by
  have h' := congrArg Fin.val (Sum.inr.inj (congrArg Prod.fst h))
  change 114 * i.val + v.1.val = 114 * j.val + w.1.val at h'
  exact Fin.ext (by omega)

def hubSet : Finset PrismVertex :=
  Finset.univ.image (fun v : Fin 2 × Fin 2 => (hub v.1, v.2))

theorem hubSet_card : hubSet.card = 4 := by decide

theorem hub_mem (a b : Fin 2) : (hub a, b) ∈ hubSet :=
  Finset.mem_image.mpr ⟨(a, b), Finset.mem_univ _, rfl⟩

theorem no_adj_to_four {V W : Type*} [Fintype V] [DecidableEq V]
    (C : SimpleGraph V) [DecidableRel C.Adj] (two : ∀ v, C.degree v = 2)
    (H : Finset V) (four : H.card = 4) (embed : Fin 9 → W → V)
    (separate : ∀ {i j v w}, embed i v = embed j w → i = j) :
    ∃ i : Fin 9, ∀ v : W, ∀ z ∈ H, ¬ C.Adj (embed i v) z := by
  classical
  let used := H.biUnion (fun v => C.neighborFinset v)
  have usedSize : used.card ≤ 8 := by
    calc
      used.card ≤ ∑ v ∈ H, (C.neighborFinset v).card := Finset.card_biUnion_le
      _ = 8 := by simp [two, four]
  by_contra! hit
  choose v z hz edge using hit
  let f : Fin 9 → V := fun i => embed i (v i)
  have hf : Function.Injective f := fun _ _ e => separate e
  have member (i : Fin 9) : f i ∈ used := by
    change f i ∈ H.biUnion (fun v => C.neighborFinset v)
    rw [Finset.mem_biUnion]
    use z i
    exact ⟨hz i, (C.mem_neighborFinset (z i) (f i)).mpr (edge i).symm⟩
  have subset : Finset.univ.image f ⊆ used := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact member i
  have tooMany := Finset.card_le_card subset
  rw [Finset.card_image_of_injective _ hf] at tooMany
  simp only [Finset.card_univ, Fintype.card_fin] at tooMany
  omega

set_option maxRecDepth 6000 in
theorem hub_free_pair (C : SimpleGraph PrismVertex) [DecidableRel C.Adj]
    (two : ∀ v, C.degree v = 2) :
    ∃ i : Fin 9, ∀ v : PairPrismVertex, ∀ a b : Fin 2,
      ¬ C.Adj (embedPair i v) (hub a, b) := by
  obtain ⟨i, hi⟩ := no_adj_to_four C two hubSet hubSet_card embedPair (fun e => pair_disjoint e)
  exact ⟨i, fun v a b => hi v (hub a, b) (hub_mem a b)⟩

theorem line_edge {r s : Line} (h : (.inr r, .inr s) ∈ allEdges) :
    ∃ (i : Fin 26) (u v : Local), r = block i u ∧ s = block i v ∧ (u, v) ∈ localEdges := by
  obtain ⟨i, _, hi⟩ := List.mem_flatMap.mp h
  simp only [edgesAt, List.mem_append] at hi
  rcases hi with (hi | hi) | hi
  · obtain ⟨⟨u, v⟩, huv, eq⟩ := List.mem_map.mp hi
    exact ⟨i, u, v, (Sum.inr.inj (congrArg Prod.fst eq)).symm,
      (Sum.inr.inj (congrArg Prod.snd eq)).symm, huv⟩
  · obtain ⟨u, _, eq⟩ := List.mem_map.mp hi
    have neq : hub 0 ≠ Sum.inr r := by simp [hub]
    exact (neq (congrArg Prod.fst eq)).elim
  · obtain ⟨u, _, eq⟩ := List.mem_map.mp hi
    have neq : hub 1 ≠ Sum.inr r := by simp [hub]
    exact (neq (congrArg Prod.fst eq)).elim

theorem line_adj {r s : Line} (h : G.Adj (.inr r) (.inr s)) :
    ∃ (i : Fin 26) (u v : Local), r = block i u ∧ s = block i v ∧ localG.Adj u v := by
  rcases h.2 with h0 | h0
  · obtain ⟨i, u, v, hr, hs, huv⟩ := line_edge h0
    refine ⟨i, u, v, hr, hs, ?_, Or.inl huv⟩
    rintro rfl
    exact h.1 (congrArg Sum.inr (hr.trans hs.symm))
  · obtain ⟨i, u, v, hs, hr, huv⟩ := line_edge h0
    refine ⟨i, v, u, hr, hs, ?_, Or.inr huv⟩
    rintro rfl
    exact h.1 (congrArg Sum.inr (hr.trans hs.symm))

def pairLocal (side : Fin 2) (j : Local) : PairVertex :=
  ⟨38 * side.val + j.val, by omega⟩

theorem pair_adj_of_local (side : Fin 2) {u v : Local} (h : localG.Adj u v) :
    pairG.Adj (pairLocal side u) (pairLocal side v) := by
  have member (a b : Local) (hab : (a, b) ∈ localEdges) :
      (pairLocal side a, pairLocal side b) ∈ pairEdges := by
    fin_cases side
    · exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨(a, b), hab, by simp [pairLocal]⟩))
    · exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨(a, b), hab, by simp [pairLocal]⟩))
  have ne : pairLocal side u ≠ pairLocal side v := by
    intro e
    apply h.1
    have e' := congrArg Fin.val e
    exact Fin.ext (by simpa [pairLocal] using e')
  exact ⟨ne, h.2.imp (member u v) (member v u)⟩

theorem pair_adj_in {i : Fin 9} {u v : PairVertex}
    (h : G.Adj (pairBase i u) (pairBase i v)) : pairG.Adj u v := by
  obtain ⟨t, a, b, ht, hw, hab⟩ := line_adj h
  have ht' := congrArg Fin.val ht
  have hw' := congrArg Fin.val hw
  change 114 * i.val + u.val = 38 * t.val + a.val at ht'
  change 114 * i.val + v.val = 38 * t.val + b.val at hw'
  have uv : u.val ≠ v.val := fun e => h.1 (congrArg (pairBase i) (Fin.ext e))
  have htlo : 3 * i.val ≤ t.val := by omega
  have hthi : t.val ≤ 3 * i.val + 1 := by omega
  let side : Fin 2 := ⟨t.val - 3 * i.val, by omega⟩
  have ueq : u = pairLocal side a := Fin.ext (by change u.val = 38 * (t.val - 3 * i.val) + a.val; omega)
  have veq : v = pairLocal side b := Fin.ext (by change v.val = 38 * (t.val - 3 * i.val) + b.val; omega)
  rw [ueq, veq]
  exact pair_adj_of_local side hab

theorem pair_interior_neighbor {i : Fin 9} {u : PairVertex} {v : Line}
    (h0 : u ≠ 0) (h76 : u ≠ 76) (h : G.Adj (pairBase i u) (.inr v)) :
    ∃ w : PairVertex, .inr v = pairBase i w := by
  obtain ⟨t, a, b, ht, hv, _⟩ := line_adj h
  have ht' := congrArg Fin.val ht
  have hv' := congrArg Fin.val hv
  change 114 * i.val + u.val = 38 * t.val + a.val at ht'
  change v.val = 38 * t.val + b.val at hv'
  have h0' : u.val ≠ 0 := fun e => h0 (Fin.ext e)
  have h76' : u.val ≠ 76 := fun e => h76 (Fin.ext e)
  have htlo : 3 * i.val ≤ t.val := by omega
  have hthi : t.val ≤ 3 * i.val + 1 := by omega
  let side : Fin 2 := ⟨t.val - 3 * i.val, by omega⟩
  use pairLocal side b
  apply congrArg Sum.inr
  apply Fin.ext
  change v.val = 114 * i.val + (38 * (t.val - 3 * i.val) + b.val)
  omega

theorem pair_prism_adj_in {i : Fin 9} {u v : PairPrismVertex}
    (h : prism.Adj (embedPair i u) (embedPair i v)) : pairPrism.Adj u v := by
  rw [boxProd_adj] at h ⊢
  rcases h with ⟨hadj, e⟩ | ⟨hadj, e⟩
  · exact Or.inl ⟨pair_adj_in hadj, e⟩
  · exact Or.inr ⟨hadj, pair_base_injective i e⟩


theorem covered_prism_neighbor (C : SimpleGraph PrismVertex) (hC : C ≤ prism)
    {i : Fin 9} (safe : ∀ v : PairPrismVertex, ∀ a b : Fin 2,
      ¬ C.Adj (embedPair i v) (hub a, b))
    (v : PairPrismVertex) (h0 : v.1 ≠ 0) (h76 : v.1 ≠ 76) :
    ∀ w, C.Adj (embedPair i v) w → w ∈ Set.range (embedPair i) := by
  rintro ⟨a, b⟩ edge
  cases a with
  | inl a => exact (safe v a b edge).elim
  | inr a =>
    have hadj := hC edge
    rw [boxProd_adj] at hadj
    rcases hadj with ⟨hab, _⟩ | ⟨_, hab⟩
    · obtain ⟨w, hw⟩ := pair_interior_neighbor h0 h76 hab
      exact ⟨(w, b), Prod.ext hw.symm rfl⟩
    · exact ⟨(v.1, b), Prod.ext hab rfl⟩

def localObstruction : Prop :=
    ∀ (A : SimpleGraph PairPrismVertex) [DecidableRel A.Adj],
      A ≤ pairPrism →
      (∀ v, A.degree v ≤ 2) →
      (∀ v, v.1 ≠ 0 → v.1 ≠ 76 → A.degree v = 2) →
      (∀ S : Finset PairPrismVertex, S.Nonempty →
        (∀ v ∈ S, ∀ w, A.Adj v w → w ∈ S) → ∃ v ∈ S, A.degree v < 2) →
      False

set_option maxRecDepth 6000 in
theorem counterexample_not_hamiltonian (impossible : localObstruction) :
    ¬ prism.IsHamiltonian := by
  classical
  intro hypothetical
  obtain ⟨C, sub, connected, degree⟩ := cycleSubgraph hypothetical
  have degC (v) : C.degree v = 2 := by
    rw [← C.card_neighborFinset_eq_degree, ← Set.ncard_coe_finset, C.coe_neighborFinset]
    exact degree v
  obtain ⟨i, safe⟩ := hub_free_pair C degC
  let e : PairPrismVertex ↪ PrismVertex := ⟨embedPair i, pair_injective i⟩
  have out : (hub 0, 0) ∉ Set.range e := by
    rintro ⟨w, hw⟩
    have h' := congrArg Prod.fst hw
    simp [e, embedPair, pairBase, hub] at h'
  apply impossible (C.comap e)
  · intro u v edge
    exact pair_prism_adj_in (sub edge)
  · intro v
    simpa [degC] using comapDegree_le C e v
  · intro v h0 h76
    rw [comapDegree_eq_of_range C e v (covered_prism_neighbor C sub safe v h0 h76)]
    exact degC (e v)
  · intro S hS hClosed
    exact comapDegree_lt_two_of_closed C e connected degC (hub 0, 0) out S hS hClosed

end PrismCounterexample

namespace PrismCounterexample

theorem exact_disproof_of (impossible : localObstruction) :
    ¬ (type_of% @OMA.S_opg_every_prism_over_a_3_connected_planar_graph_is_hamiltonian.main) := by
  intro assertion
  apply counterexample_not_hamiltonian impossible
  exact assertion Vertex G ⟨by simp [Fintype.card_sum], counterexampleConnected⟩ rational_planarity

end PrismCounterexample

namespace PrismCounterexample.Gadget

/-- Merge two label classes by replacing every occurrence of `b` by `a`. -/
def labelUnion (ds : Array ℕ) (a b : ℕ) : Array ℕ :=
  if a = b then ds else ds.map (fun t => if t = b then a else t)

def mergeLabelEdge (ds : Array ℕ) (e : ℕ × ℕ) : Array ℕ :=
  labelUnion ds ds[e.1]! ds[e.2]!

/-- Labels obtained by processing the selected edges in order. -/
def labels (n : ℕ) (es : List (ℕ × ℕ)) : Array ℕ :=
  es.foldl mergeLabelEdge (Array.range n)

@[simp] theorem labelUnion_size (ds : Array ℕ) (a b : ℕ) :
    (labelUnion ds a b).size = ds.size := by
  unfold labelUnion
  split <;> simp

@[simp] theorem mergeLabelEdge_size (ds : Array ℕ) (e : ℕ × ℕ) :
    (mergeLabelEdge ds e).size = ds.size := labelUnion_size _ _ _

theorem labelUnion_at (ds : Array ℕ) (a b i : ℕ) (hi : i < ds.size) :
    (labelUnion ds a b)[i]! = if ds[i]! = b then a else ds[i]! := by
  unfold labelUnion
  split
  · rename_i h
    simp [h]
  · have hi' : i < (ds.map fun t => if t = b then a else t).size := by simpa using hi
    rw [getElem!_pos (ds.map (fun t : ℕ => if t = b then a else t)) i hi',
      getElem!_pos ds i hi, Array.getElem_map]

theorem labelUnion_preserves (ds : Array ℕ) (a b i j : ℕ)
    (hi : i < ds.size) (hj : j < ds.size) (h : ds[i]! = ds[j]!) :
    (labelUnion ds a b)[i]! = (labelUnion ds a b)[j]! := by
  rw [labelUnion_at _ _ _ _ hi, labelUnion_at _ _ _ _ hj, h]

theorem mergeLabelEdge_identifies (ds : Array ℕ) (e : ℕ × ℕ)
    (hi : e.1 < ds.size) (hj : e.2 < ds.size) :
    (mergeLabelEdge ds e)[e.1]! = (mergeLabelEdge ds e)[e.2]! := by
  unfold mergeLabelEdge
  rw [labelUnion_at _ _ _ _ hi, labelUnion_at _ _ _ _ hj]
  split <;> simp

private theorem foldLabel_size (ds : Array ℕ) (es : List (ℕ × ℕ)) :
    (es.foldl mergeLabelEdge ds).size = ds.size := by
  induction es generalizing ds with
  | nil => rfl
  | cons e es ih => simp [List.foldl_cons, ih]

@[simp] theorem labels_size (n : ℕ) (es : List (ℕ × ℕ)) : (labels n es).size = n := by
  simp [labels, foldLabel_size]

private theorem foldLabel_preserves (ds : Array ℕ) (es : List (ℕ × ℕ)) (i j : ℕ)
    (hi : i < ds.size) (hj : j < ds.size) (h : ds[i]! = ds[j]!) :
    (es.foldl mergeLabelEdge ds)[i]! = (es.foldl mergeLabelEdge ds)[j]! := by
  induction es generalizing ds with
  | nil => exact h
  | cons e es ih =>
    rw [List.foldl_cons]
    exact ih (mergeLabelEdge ds e) (by simpa using hi) (by simpa using hj)
      (labelUnion_preserves _ _ _ _ _ hi hj h)

private theorem foldLabel_compatible (ds : Array ℕ) (es : List (ℕ × ℕ))
    (hbound : ∀ e ∈ es, e.1 < ds.size ∧ e.2 < ds.size) (e : ℕ × ℕ) (he : e ∈ es) :
    (es.foldl mergeLabelEdge ds)[e.1]! = (es.foldl mergeLabelEdge ds)[e.2]! := by
  induction es generalizing ds with
  | nil => exact (List.not_mem_nil he).elim
  | cons a as ih =>
    have htail (f : ℕ × ℕ) (hf : f ∈ as) :
        f.1 < (mergeLabelEdge ds a).size ∧ f.2 < (mergeLabelEdge ds a).size := by
      simpa using hbound f (List.mem_cons_of_mem _ hf)
    rw [List.foldl_cons]
    rcases List.mem_cons.mp he with rfl | he'
    · obtain ⟨h₁,h₂⟩ := hbound e (List.mem_cons_self)
      exact foldLabel_preserves _ _ _ _ (by simpa using h₁) (by simpa using h₂)
        (mergeLabelEdge_identifies _ _ h₁ h₂)
    · exact ih (mergeLabelEdge ds a) htail he'

/-- Every checked edge has endpoints in the same label class. -/
theorem labels_eq_of_mem (n : ℕ) (es : List (ℕ × ℕ))
    (hbound : ∀ e ∈ es, e.1 < n ∧ e.2 < n) (e : ℕ × ℕ) (he : e ∈ es) :
    (labels n es)[e.1]! = (labels n es)[e.2]! :=
  foldLabel_compatible _ _ (by simpa using hbound) _ he

end PrismCounterexample.Gadget

/-!
Local transfer certificates for the prism obstruction in Špacapan,
*A counterexample to prism-hamiltonicity of 3-connected planar graphs*,
arXiv:1906.06683, Figure 1 and Theorem 2.6.

An elementary piece has four ports, two at either end.  The two sides of a
large block are treated independently, with no vertical edge at their ports.
-/

namespace PrismCounterexample.Gadget

abbrev Edge := ℕ × ℕ

def incidence (v : ℕ) (e : Edge) : Bool := e.1 == v || e.2 == v

def deg (es : List Edge) (v : ℕ) : ℕ := es.countP (incidence v)

def row (allowed : List Edge) (v : ℕ) : List Edge :=
  allowed.filter fun e => e.1 == v

def kept (allowed : List Edge) (f : Edge → Bool) (i : ℕ) : ℕ → List Edge
  | 0 => []
  | n + 1 => ((row allowed i).filter f) ++ kept allowed f (i + 1) n

def degreeOK (port : ℕ → Bool) (v : ℕ) (es : List Edge) : Bool :=
  if port v then deg es v ≤ 2 else deg es v = 2

def enumerate (allowed : List Edge) (port : ℕ → Bool) (i : ℕ)
    (prior : List Edge) : ℕ → List (List Edge)
  | 0 => [prior]
  | n + 1 =>
    (row allowed i).sublists.flatMap fun selected =>
      let next := prior ++ selected
      if degreeOK port i next then enumerate allowed port (i+1) next n else []

private theorem kept_mem {allowed : List Edge} {f : Edge → Bool}
    {i n : ℕ} {e : Edge} (he : e ∈ kept allowed f i n) :
    e ∈ allowed ∧ i ≤ e.1 := by
  induction n generalizing i with
  | zero => simp [kept] at he
  | succ n ih =>
    rw [kept] at he
    rcases List.mem_append.mp he with h | h
    · have hh := List.mem_filter.mp (List.mem_filter.mp h).1
      exact ⟨hh.1, by simpa using (eq_of_beq hh.2).ge⟩
    · obtain ⟨he, hle⟩ := ih h
      exact ⟨he, by omega⟩

theorem kept_mem_iff {allowed : List Edge} {f : Edge → Bool}
    {i n : ℕ} {e : Edge} :
    e ∈ kept allowed f i n ↔ e ∈ allowed ∧ f e = true ∧ i ≤ e.1 ∧ e.1 < i+n := by
  induction n generalizing i with
  | zero =>
    simp only [kept, List.not_mem_nil, add_zero, false_iff]
    exact fun h => Nat.not_lt_of_ge h.2.2.1 h.2.2.2
  | succ n ih =>
    rw [kept, List.mem_append, List.mem_filter, row, List.mem_filter, ih]
    simp only [beq_iff_eq]
    constructor
    · rintro (⟨⟨he, hf⟩, hb⟩ | ⟨he, hb, hlo, hhi⟩)
      · exact ⟨he, hb, by omega, by omega⟩
      · exact ⟨he, hb, by omega, by omega⟩
    · rintro ⟨he, hb, hlo, hhi⟩
      by_cases hf : e.1 = i
      · exact Or.inl ⟨⟨he, hf⟩, hb⟩
      · exact Or.inr ⟨he, hb, by omega, by omega⟩

theorem kept_nodup {allowed : List Edge} (h : allowed.Nodup) (f : Edge → Bool) (i n : ℕ) :
    (kept allowed f i n).Nodup := by
  induction n generalizing i with
  | zero => simp [kept]
  | succ n ih =>
    rw [kept, List.nodup_append]
    refine ⟨(h.filter _).filter _, ih _, ?_⟩
    intro e he e' he' h
    subst e'
    have hrow := (List.mem_filter.mp (List.mem_filter.mp he).1).2
    have hf := (kept_mem_iff.mp he').2.2.1
    have hEq := eq_of_beq hrow
    omega

private theorem deg_late_zero {allowed : List Edge} {f : Edge → Bool}
    (horder : ∀ e ∈ allowed, e.1 < e.2) (i n : ℕ) :
    deg (kept allowed f (i+1) n) i = 0 := by
  unfold deg
  rw [List.countP_eq_length_filter]
  apply List.length_eq_zero_iff.mpr
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro e h
  obtain ⟨hm, hp⟩ := kept_mem (List.mem_filter.mp h).1
  have hq := horder e hm
  simp [incidence, show e.1 ≠ i by omega, show e.2 ≠ i by omega] at h

private theorem enumerate_complete (allowed : List Edge) (port : ℕ → Bool)
    (horder : ∀ e ∈ allowed, e.1 < e.2) (f : Edge → Bool) (n i : ℕ)
    (prior : List Edge)
    (hdeg : ∀ v, i ≤ v → v < i+n →
      degreeOK port v (prior ++ kept allowed f i n) = true) :
    prior ++ kept allowed f i n ∈ enumerate allowed port i prior n := by
  induction n generalizing i prior with
  | zero => simp [kept, enumerate]
  | succ n ih =>
    rw [enumerate, List.mem_flatMap]
    let q := (row allowed i).filter f
    refine ⟨q, List.mem_sublists.mpr List.filter_sublist, ?_⟩
    have hz := deg_late_zero (f := f) horder i n
    have hd := hdeg i le_rfl (by omega)
    have he : prior ++ kept allowed f i (n+1) =
        (prior ++ q) ++ kept allowed f (i+1) n := by
      simp only [kept, List.append_assoc, q]
    have hcopy : deg ((prior ++ q) ++ kept allowed f (i+1) n) i =
        deg (prior ++ q) i := by
      simp only [deg] at *
      simp only [List.countP_append, hz, add_zero]
    rw [he] at hd
    unfold degreeOK at hd
    rw [hcopy] at hd
    change degreeOK port i (prior ++ q) = true at hd
    change _ ∈ (if degreeOK port i (prior ++ q) then _ else [])
    rw [if_pos hd]
    rw [he]
    exact ih (i+1) (prior ++ q) (fun v hv hw => by
      rw [← he]
      exact hdeg v (by omega) (by omega))

private def prismEdges (n : ℕ) (base : List Edge) : List Edge :=
  (base.flatMap fun e =>
    let lo := min e.1 e.2
    let hi := max e.1 e.2
    [(2*lo,2*hi), (2*lo+1,2*hi+1)]) ++
  ((List.range' 1 (n-2)).map fun k => (2*k,2*k+1))

def sideEdges : List Edge :=
  prismEdges 10 [(0,1),(1,2),(2,3),(3,4),(4,0),(3,5),(5,6),(6,7),(7,8),
    (8,3),(4,9),(7,9),(8,9)]

def cycleEdges : List Edge :=
  prismEdges 5 [(0,1),(1,4),(4,3),(3,2),(2,0)]

def ports (n : ℕ) : List ℕ := [0,1,n-2,n-1]

def isPort (n : ℕ) (v : ℕ) : Bool := (ports n).contains v

abbrev Signature := List ℕ × List ℕ

def status (n : ℕ) (es : List Edge) : Signature × Bool :=
  let ds := labels n es
  let d := (ports n).map (deg es)
  let c := (ports n).map fun v => ds[v]!
  let free := ((ports n).filter fun p => deg es p < 2).map fun p => ds[p]!
  let valid := ds.toList.all free.contains
  ((d,c),valid)

def normalized (p : Signature) : Signature :=
  (p.1, p.2.map fun x => p.2.idxOf x)

/-- Fused traversal, retaining one branch at a time. -/
def check (allowed : List Edge) (port : ℕ → Bool) (test : List Edge → Bool)
    (i : ℕ) (prior : List Edge) : ℕ → Bool
  | 0 => test prior
  | n + 1 =>
    (row allowed i).sublists.all fun selected =>
      let next := prior ++ selected
      if degreeOK port i next then check allowed port test (i+1) next n else true

theorem check_sound (allowed : List Edge) (port : ℕ → Bool) (test : List Edge → Bool)
    (n i : ℕ) (prior actual : List Edge)
    (hcheck : check allowed port test i prior n = true)
    (hmem : actual ∈ enumerate allowed port i prior n) : test actual = true := by
  induction n generalizing i prior with
  | zero =>
    have : actual = prior := by simpa [enumerate] using hmem
    simpa [check, this] using hcheck
  | succ n ih =>
    rw [enumerate, List.mem_flatMap] at hmem
    obtain ⟨selected, hselected, hmem⟩ := hmem
    rw [check, List.all_eq_true] at hcheck
    specialize hcheck selected hselected
    by_cases h : degreeOK port i (prior ++ selected) = true
    · exact ih (i+1) (prior ++ selected) (by simpa only [if_pos h] using hcheck)
        (by simpa only [if_pos h] using hmem)
    · simp only [if_neg h, List.not_mem_nil] at hmem

theorem exhaustive (allowed : List Edge) (horder : ∀ e ∈ allowed, e.1 < e.2)
    (port : ℕ → Bool) (test : List Edge → Bool) (n : ℕ) (f : Edge → Bool)
    (hcheck : check allowed port test 0 [] n = true)
    (hdeg : ∀ v, v < n → degreeOK port v (kept allowed f 0 n) = true) :
    test (kept allowed f 0 n) = true := by
  apply check_sound _ _ _ n 0 [] _ hcheck
  simpa using enumerate_complete allowed port horder f n 0 [] (by simpa using hdeg)

def sideStates : List Signature := [
  ([0, 0, 1, 1], [0, 1, 2, 2]),
  ([0, 1, 0, 1], [0, 1, 2, 1]),
  ([0, 1, 1, 0], [0, 1, 1, 3]),
  ([0, 1, 1, 2], [0, 1, 1, 1]),
  ([0, 1, 2, 1], [0, 1, 1, 1]),
  ([0, 2, 1, 1], [0, 1, 1, 1]),
  ([1, 0, 0, 1], [0, 1, 2, 0]),
  ([1, 0, 1, 0], [0, 1, 0, 3]),
  ([1, 0, 1, 2], [0, 1, 0, 0]),
  ([1, 0, 2, 1], [0, 1, 0, 0]),
  ([1, 1, 0, 2], [0, 0, 2, 0]),
  ([1, 1, 1, 1], [0, 0, 2, 2]),
  ([1, 1, 1, 1], [0, 1, 0, 1]),
  ([1, 1, 1, 1], [0, 1, 1, 0]),
  ([1, 1, 2, 0], [0, 0, 0, 3]),
  ([1, 1, 2, 2], [0, 0, 0, 0]),
  ([1, 2, 0, 1], [0, 0, 2, 0]),
  ([1, 2, 1, 0], [0, 0, 0, 3]),
  ([1, 2, 1, 2], [0, 0, 0, 0]),
  ([1, 2, 2, 1], [0, 0, 0, 0]),
  ([2, 0, 1, 1], [0, 1, 0, 0]),
  ([2, 1, 0, 1], [0, 0, 2, 0]),
  ([2, 1, 1, 0], [0, 0, 0, 3]),
  ([2, 1, 1, 2], [0, 0, 0, 0]),
  ([2, 1, 2, 1], [0, 0, 0, 0]),
  ([2, 2, 1, 1], [0, 0, 0, 0])]

def cycleStates : List Signature := [
  ([0, 1, 1, 2], [0, 1, 1, 1]),
  ([0, 1, 2, 1], [0, 1, 1, 1]),
  ([0, 2, 1, 1], [0, 1, 1, 1]),
  ([1, 0, 1, 2], [0, 1, 0, 0]),
  ([1, 0, 2, 1], [0, 1, 0, 0]),
  ([1, 1, 0, 2], [0, 0, 2, 0]),
  ([1, 1, 1, 1], [0, 0, 2, 2]),
  ([1, 1, 2, 0], [0, 0, 0, 3]),
  ([1, 1, 2, 2], [0, 0, 0, 0]),
  ([1, 2, 0, 1], [0, 0, 2, 0]),
  ([1, 2, 1, 0], [0, 0, 0, 3]),
  ([1, 2, 2, 1], [0, 0, 0, 0]),
  ([2, 0, 1, 1], [0, 1, 0, 0]),
  ([2, 1, 0, 1], [0, 0, 2, 0]),
  ([2, 1, 1, 0], [0, 0, 0, 3]),
  ([2, 1, 1, 2], [0, 0, 0, 0]),
  ([2, 2, 1, 1], [0, 0, 0, 0])]

def stateTest (n : ℕ) (table : List Signature) (es : List Edge) : Bool :=
  let value := status n es
  !value.2 || table.contains (normalized value.1)

theorem status_good {n : ℕ} {es : List Edge}
    (h : ∀ v, v < n → ∃ p ∈ ports n, deg es p < 2 ∧ (labels n es)[v]! = (labels n es)[p]!) :
    (status n es).2 = true := by
  simp only [status, List.all_eq_true]
  intro x hx
  obtain ⟨i, hi, he⟩ := Array.mem_iff_getElem.mp (Array.mem_toList_iff.mp hx)
  obtain ⟨p, hp, hdegree, hsame⟩ := h i (by simpa only [labels_size] using hi)
  apply List.contains_iff_mem.mpr
  refine List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, by simpa using hdegree⟩, ?_⟩
  rw [getElem!_pos (labels n es) i hi] at hsame
  rw [← he]
  exact hsame.symm

theorem state_mem {n : ℕ} {table : List Signature} {es : List Edge}
    (hcheck : stateTest n table es = true) (hgood : (status n es).2 = true) :
    normalized (status n es).1 ∈ table := by
  simpa [stateTest, hgood, List.contains_iff_mem] using hcheck

theorem side_order : ∀ e ∈ sideEdges, e.1 < e.2 := by decide +kernel
theorem cycle_order : ∀ e ∈ cycleEdges, e.1 < e.2 := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem cycle_certificate :
    check cycleEdges (isPort 10) (stateTest 10 cycleStates) 0 [] 10 = true := by
  decide +kernel

theorem check_append (allowed : List Edge) (port : ℕ → Bool) (test : List Edge → Bool)
    (a b i : ℕ) (prior : List Edge) :
    check allowed port test i prior (a+b) =
      (enumerate allowed port i prior a).all
        (fun next => check allowed port test (i+a) next b) := by
  induction a generalizing i prior with
  | zero => simp [enumerate]
  | succ a ih =>
    rw [Nat.succ_add, check, enumerate, List.all_flatMap]
    refine List.all_congr rfl fun selected => ?_
    dsimp only
    by_cases h : degreeOK port i (prior ++ selected) = true
    · rw [if_pos h, if_pos h, ih]
      congr 1
      funext p
      congr 1
      omega
    · simp [if_neg h]

end PrismCounterexample.Gadget

namespace PrismCounterexample

open SimpleGraph

abbrev Piece := Fin 10
abbrev PairPoint := PairVertex × Fin 2

def pieceSize (p : Piece) : ℕ :=
  if p.val % 5 = 4 then 10 else 20

abbrev PiecePoint (p : Piece) := Fin (pieceSize p)

def pieceBaseLabel (p : Piece) (v : ℕ) : ℕ :=
  let a := v / 2
  let side := if a = 9 then 17 else a
  let up := if 1 ≤ side ∧ side ≤ 8 then side + 8 else side
  let base := match p.val % 5 with
    | 0 => side
    | 1 => up
    | 2 => 34 - side
    | 3 => 34 - up
    | _ => 34 + a
  38 * (p.val / 5) + base

def pieceMap (p : Piece) (v : PiecePoint p) : PairPoint :=
  (⟨pieceBaseLabel p v.val % 77, Nat.mod_lt _ (by decide)⟩,
    ⟨v.val % 2, Nat.mod_lt _ (by decide)⟩)

def piecePort (p : Piece) (i : Fin 4) : PiecePoint p :=
  ⟨if i.val < 2 then i.val else pieceSize p - 4 + i.val, by
    have hp : 10 ≤ pieceSize p := by unfold pieceSize; split <;> decide
    split <;> omega⟩

def pieceIsPort (p : Piece) (v : PiecePoint p) : Prop :=
  v.val < 2 ∨ pieceSize p - 2 ≤ v.val

instance (p : Piece) : DecidablePred (pieceIsPort p) :=
  fun v => inferInstanceAs (Decidable (v.val < 2 ∨ pieceSize p - 2 ≤ v.val))

theorem piecePort_isPort (p : Piece) (q : Fin 4) : pieceIsPort p (piecePort p q) := by
  unfold pieceIsPort piecePort
  have hp : 10 ≤ pieceSize p := by unfold pieceSize; split <;> decide
  simp only
  split <;> omega

theorem piecePort_exists (p : Piece) (v : PiecePoint p) (h : pieceIsPort p v) :
    ∃ q : Fin 4, piecePort p q = v := by
  have hp : 10 ≤ pieceSize p := by unfold pieceSize; split <;> decide
  rcases h with h | h
  · use ⟨v.val, by omega⟩
    apply Fin.ext
    simp [piecePort, h]
  · have hi := v.isLt
    use ⟨v.val + 4 - pieceSize p, by omega⟩
    apply Fin.ext
    have hge : ¬ v.val + 4 - pieceSize p < 2 := by omega
    simp only [piecePort, hge, if_false]
    omega

def rawPiecePoint (p : Piece) (v : ℕ) : PiecePoint p :=
  ⟨v % pieceSize p, Nat.mod_lt _ (by unfold pieceSize; split <;> decide)⟩

private theorem piece_injective_table :
    ∀ (p : Piece) (u v : PiecePoint p), pieceMap p u = pieceMap p v → u = v := by
  decide +kernel

def pieceEmbed (p : Piece) : PiecePoint p ↪ PairPoint where
  toFun := pieceMap p
  inj' := fun u v => piece_injective_table p u v

set_option maxRecDepth 20000 in
theorem piece_cover (w : PairPoint) : ∃ (p : Piece) (v : PiecePoint p), pieceEmbed p v = w := by
  have h : ∀ w : PairPoint, ∃ (p : Piece) (v : PiecePoint p), pieceMap p v = w := by
    decide +kernel
  exact h w

set_option maxRecDepth 20000 in
set_option maxHeartbeats 0 in
private theorem piece_overlap_table :
    ∀ (p q : Piece), p ≠ q → ∀ (v : PiecePoint p) (w : PiecePoint q),
      pieceMap p v = pieceMap q w → pieceIsPort p v ∧ pieceIsPort q w := by
  decide +kernel

theorem piece_overlap {p q : Piece} (hpq : p ≠ q) {v : PiecePoint p} {w : PiecePoint q}
    (h : pieceEmbed p v = pieceEmbed q w) :
    ∃ (a b : Fin 4), piecePort p a = v ∧ piecePort q b = w := by
  obtain ⟨hv, hw⟩ := piece_overlap_table p q hpq v w h
  obtain ⟨a, ha⟩ := piecePort_exists p v hv
  obtain ⟨b, hb⟩ := piecePort_exists q w hw
  exact ⟨a, b, ha, hb⟩

def jointPositions : List PairVertex := [0,17,34,38,55,72,76]

def jointRungs : List (PairPoint × PairPoint) :=
  jointPositions.map fun p => ((p,0), (p,1))

end PrismCounterexample

namespace PrismCounterexample

open SimpleGraph

/-- The degree of a vertex is the count of incident pairs in a duplicate-free
edge list whose orientation follows a fixed linear order. -/
theorem degree_graphOfEdges {V : Type} [Fintype V] [LinearOrder V]
    (edges : List (V × V)) (hn : edges.Nodup) (ho : ∀ e ∈ edges, e.1 < e.2) (v : V) :
    (graphOfEdges edges).degree v = edges.countP (fun e => e.1 == v || e.2 == v) := by
  let incident : V × V → Bool := fun e => e.1 == v || e.2 == v
  let picked := edges.filter incident
  let f : V → V × V := fun w => if v < w then (v,w) else (w,v)
  let g : V × V → V := fun e => if e.1 = v then e.2 else e.1
  rw [← card_neighborFinset_eq_degree, List.countP_eq_length_filter]
  change ((graphOfEdges edges).neighborFinset v).card = picked.length
  rw [← List.toFinset_card_of_nodup (hn.filter incident)]
  have picked_iff (e : V × V) : e ∈ picked.toFinset ↔ e ∈ edges ∧ (e.1 = v ∨ e.2 = v) := by
    simp [picked, incident]
  have neigh (w : V) : w ∈ (graphOfEdges edges).neighborFinset v ↔
      v ≠ w ∧ ((v,w) ∈ edges ∨ (w,v) ∈ edges) :=
    (graphOfEdges edges).mem_neighborFinset v w
  refine Finset.card_nbij' f g ?_ ?_ ?_ ?_
  · intro w hw
    obtain ⟨hne,hmem⟩ := (neigh w).mp hw
    apply (picked_iff (f w)).mpr
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · have hab : (v,w) ∈ edges := hmem.resolve_right (fun h => asymm hlt (ho (w,v) h))
      simpa [f,hlt] using hab
    · have hab : (w,v) ∈ edges := hmem.resolve_left (fun h => asymm hlt (ho (v,w) h))
      simpa [f,not_lt_of_gt hlt] using hab
  · rintro ⟨a,b⟩ hb
    obtain ⟨hmem,ha | hb'⟩ := (picked_iff (a,b)).mp hb
    · change a = v at ha
      subst a
      have hlt : v < b := ho (v,b) hmem
      exact (neigh (g (v,b))).mpr (by simp [g,hlt.ne,hmem])
    · change b = v at hb'
      subst b
      have hlt : a < v := ho (a,v) hmem
      exact (neigh (g (a,v))).mpr (by simp [g,hlt.ne,hlt.ne.symm,hmem])
  · intro w hw
    obtain ⟨hne,_⟩ := (neigh w).mp hw
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · simp [f,g,hlt]
    · simp [f,g,not_lt_of_gt hlt,hlt.ne]
  · rintro ⟨a,b⟩ hb
    obtain ⟨hmem,ha | hb'⟩ := (picked_iff (a,b)).mp hb
    · change a = v at ha
      subst a
      have hlt : v < b := ho (v,b) hmem
      simp [f,g,hlt]
    · change b = v at hb'
      subst b
      have hlt : a < v := ho (a,v) hmem
      simp [f,g,hlt.ne,not_lt_of_gt hlt]

end PrismCounterexample

namespace PrismCounterexample

open SimpleGraph

abbrev Index := Fin 154
abbrev IndexEdge := Index × Index
abbrev NumericEdge := ℕ × ℕ

def indexOf (w : PairPoint) : Index := ⟨2 * w.1.val + w.2.val, by omega⟩

def pointOf (i : Index) : PairPoint :=
  (⟨i.val / 2, by omega⟩, ⟨i.val % 2, Nat.mod_lt _ (by decide)⟩)

theorem point_index (v : PairPoint) : pointOf (indexOf v) = v := by
  apply Prod.ext
  · exact Fin.ext (by change (2 * v.1.val + v.2.val) / 2 = v.1.val; omega)
  · exact Fin.ext (by change (2 * v.1.val + v.2.val) % 2 = v.2.val; omega)

theorem index_point (i : Index) : indexOf (pointOf i) = i := by
  exact Fin.ext (by change 2 * (i.val / 2) + i.val % 2 = i.val; omega)

def indexEquiv : PairPoint ≃ Index where
  toFun := indexOf
  invFun := pointOf
  left_inv := point_index
  right_inv := index_point

def oriented (u v : Index) : IndexEdge :=
  if u < v then (u, v) else (v, u)

theorem oriented_comm (u v : Index) : oriented u v = oriented v u := by
  rcases lt_trichotomy u v with h | rfl | h
  · simp [oriented, h, not_lt_of_ge h.le]
  · rfl
  · simp [oriented, h, not_lt_of_ge h.le]

theorem oriented_mem_rel {V : Type*} (A : SimpleGraph V) (f : Index → V) (u v : Index) :
    A.Adj (f (oriented u v).1) (f (oriented u v).2) ↔ A.Adj (f u) (f v) := by
  unfold oriented
  split
  · rfl
  · exact A.adj_comm _ _

def indexRung (u : PairVertex) : IndexEdge :=
  (indexOf (u, 0), indexOf (u, 1))

def allIndexEdges : List IndexEdge :=
  (pairEdges.flatMap fun (u, v) =>
    (List.finRange 2).map fun j => oriented (indexOf (u, j)) (indexOf (v, j))) ++
  (List.finRange 77).map indexRung

theorem adjacent_index_edge {u v : PairPoint} (h : pairPrism.Adj u v) :
    oriented (indexOf u) (indexOf v) ∈ allIndexEdges := by
  obtain ⟨u, j⟩ := u
  obtain ⟨v, k⟩ := v
  rw [boxProd_adj] at h
  rcases h with ⟨edge, rfl⟩ | ⟨edge, eq⟩
  · apply List.mem_append.mpr
    left
    rcases edge.2 with last | first
    · exact List.mem_flatMap.mpr ⟨(u,v), last, List.mem_map.mpr ⟨j, by simp, rfl⟩⟩
    · exact List.mem_flatMap.mpr ⟨(v,u), first,
        List.mem_map.mpr ⟨j, by simp, oriented_comm _ _⟩⟩
  · change u = v at eq
    subst v
    apply List.mem_append.mpr
    right
    refine List.mem_map.mpr ⟨u, by simp, ?_⟩
    have ne : j ≠ k := edge.ne
    fin_cases j <;> fin_cases k
    · exact (ne rfl).elim
    · change (indexOf (u,0), indexOf (u,1)) = oriented (indexOf (u,0)) (indexOf (u,1))
      have lt : indexOf (u, 0) < indexOf (u, 1) := by
        change 2 * u.val + 0 < 2 * u.val + 1
        omega
      simp [oriented, lt]
    · rw [oriented_comm]
      have lt : indexOf (u, 0) < indexOf (u, 1) := by
        change 2 * u.val + 0 < 2 * u.val + 1
        omega
      simp [oriented, indexRung, lt]
    · exact (ne rfl).elim

def indexPieceEdge (p : Piece) (e : NumericEdge) : IndexEdge :=
  oriented (indexOf (pieceEmbed p (rawPiecePoint p e.1)))
    (indexOf (pieceEmbed p (rawPiecePoint p e.2)))

def pieceIndexEdges (es : Piece → List NumericEdge) (p : Piece) : List IndexEdge :=
  (es p).map (indexPieceEdge p)

def jointIndexEdges : List IndexEdge := jointPositions.map indexRung

def combinedIndexEdges (es : Piece → List NumericEdge) : List IndexEdge :=
  ((List.finRange 10).flatMap (pieceIndexEdges es)) ++ jointIndexEdges

end PrismCounterexample

namespace PrismCounterexample

open SimpleGraph

def pickIndex (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (e : IndexEdge) : Bool :=
  decide (A.Adj (pointOf e.1) (pointOf e.2))

def keptIndexEdges (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (es : Piece → List NumericEdge) : List IndexEdge :=
  (combinedIndexEdges es).filter (pickIndex A)

theorem represented_edges (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (sub : A ≤ pairPrism)
    (es : Piece → List NumericEdge) (cover : ∀ e ∈ allIndexEdges, e ∈ combinedIndexEdges es) :
    graphOfEdges (keptIndexEdges A es) = A.comap pointOf := by
  ext u v
  constructor
  · rintro ⟨_, h | h⟩
    · exact of_decide_eq_true (List.mem_filter.mp h).2
    · exact (of_decide_eq_true (List.mem_filter.mp h).2 : A.Adj (pointOf v) (pointOf u)).symm
  · intro hadj
    have h : A.Adj (pointOf u) (pointOf v) := hadj
    have ne : u ≠ v := fun eq => h.ne (congrArg pointOf eq)
    have both : oriented u v ∈ keptIndexEdges A es := by
      apply List.mem_filter.mpr
      refine ⟨cover _ ?_, decide_eq_true ((oriented_mem_rel A pointOf u v).mpr h)⟩
      simpa only [index_point] using adjacent_index_edge (sub h)
    refine ⟨ne, ?_⟩
    by_cases huv : u < v
    · exact Or.inl (by simpa [oriented, huv] using both)
    · exact Or.inr (by simpa [oriented, huv] using both)

def occursAt (v : Index) (e : IndexEdge) : Bool := e.1 == v || e.2 == v

theorem represented_degree (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (sub : A ≤ pairPrism)
    (es : Piece → List NumericEdge) (cover : ∀ e ∈ allIndexEdges, e ∈ combinedIndexEdges es)
    (unique : (combinedIndexEdges es).Nodup)
    (ordered : ∀ e ∈ combinedIndexEdges es, e.1 < e.2) (w : PairPoint) :
    A.degree w = (keptIndexEdges A es).countP (occursAt (indexOf w)) := by
  let emb : Index ↪ PairPoint := indexEquiv.symm.toEmbedding
  have hr : ∀ z, A.Adj (emb (indexOf w)) z → z ∈ Set.range emb :=
    fun z _ => ⟨indexOf z, point_index z⟩
  have degree := comapDegree_eq_of_range A emb (indexOf w) hr
  change (A.comap pointOf).degree (indexOf w) = A.degree (pointOf (indexOf w)) at degree
  rw [point_index] at degree
  rw [← degree]
  have hd := degree_graphOfEdges (keptIndexEdges A es) (List.Nodup.filter _ unique)
    (fun e he => ordered e (List.mem_filter.mp he).1) (indexOf w)
  have sets := congrArg (fun C : SimpleGraph Index => C.neighborSet (indexOf w))
    (represented_edges A sub es cover)
  have fins : (graphOfEdges (keptIndexEdges A es)).neighborFinset (indexOf w) =
      (A.comap pointOf).neighborFinset (indexOf w) :=
    Finset.coe_injective (by simpa only [coe_neighborFinset] using sets)
  exact (congrArg Finset.card fins.symm).trans hd

def pickedPiece (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (es : Piece → List NumericEdge) (p : Piece) : List NumericEdge :=
  (es p).filter (fun e => pickIndex A (indexPieceEdge p e))

def degreeContribution (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (es : Piece → List NumericEdge) (p : Piece) (w : PairPoint) : ℕ :=
  (pickedPiece A es p).countP (fun e => occursAt (indexOf w) (indexPieceEdge p e))

theorem degree_decompose (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism) (es : Piece → List NumericEdge)
    (cover : ∀ e ∈ allIndexEdges, e ∈ combinedIndexEdges es)
    (unique : (combinedIndexEdges es).Nodup)
    (ordered : ∀ e ∈ combinedIndexEdges es, e.1 < e.2) (w : PairPoint) :
    A.degree w =
      ((List.finRange 10).map (fun p => degreeContribution A es p w)).sum +
        (jointIndexEdges.filter (pickIndex A)).countP (occursAt (indexOf w)) := by
  rw [represented_degree A sub es cover unique ordered]
  simp only [keptIndexEdges, combinedIndexEdges, List.filter_append, List.countP_append,
    List.filter_flatMap, List.countP_flatMap, Function.comp_def, add_left_inj]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  simp only [pieceIndexEdges, List.filter_map, List.countP_map, degreeContribution,
    pickedPiece, Function.comp_def]

end PrismCounterexample

namespace PrismCounterexample

open SimpleGraph

def exactEdges (p : Piece) : List NumericEdge :=
  if p.val % 5 = 4 then Gadget.cycleEdges else Gadget.sideEdges

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem exact_cover : ∀ e ∈ allIndexEdges, e ∈ combinedIndexEdges exactEdges := by
  have certificate : allIndexEdges.all (combinedIndexEdges exactEdges).contains = true := by
    decide +kernel
  intro e he
  exact List.contains_iff_mem.mp (List.all_eq_true.mp certificate _ he)

set_option maxRecDepth 30000 in
set_option maxHeartbeats 0 in
theorem exact_unique : (combinedIndexEdges exactEdges).Nodup := by decide +kernel

set_option maxRecDepth 30000 in
theorem exact_ordered : ∀ e ∈ combinedIndexEdges exactEdges, e.1 < e.2 := by
  have certificate : (combinedIndexEdges exactEdges).all (fun e => decide (e.1 < e.2)) = true := by
    decide +kernel
  intro e he
  exact of_decide_eq_true (List.all_eq_true.mp certificate _ he)

set_option maxRecDepth 30000 in
theorem raw_bounds (p : Piece) (e : NumericEdge) (he : e ∈ exactEdges p) :
    e.1 < e.2 ∧ e.2 < pieceSize p := by
  have certificate : ∀ q : Piece,
      (exactEdges q).all (fun e => decide (e.1 < e.2 ∧ e.2 < pieceSize q)) = true := by
    decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp (certificate p) e he)

theorem raw_nodup (p : Piece) : (exactEdges p).Nodup := by
  have h : ∀ q : Piece, (exactEdges q).Nodup := by decide +kernel
  exact h p

def pointPair (p : Piece) (e : NumericEdge) : PiecePoint p × PiecePoint p :=
  (rawPiecePoint p e.1, rawPiecePoint p e.2)

theorem point_index_inj (p : Piece) : Function.Injective (fun v => indexOf (pieceEmbed p v)) :=
  indexEquiv.injective.comp (pieceEmbed p).injective

theorem rawPoint_val (p : Piece) {i : ℕ} (h : i < pieceSize p) : (rawPiecePoint p i).val = i :=
  Nat.mod_eq_of_lt h

theorem pointPair_inj_on (p : Piece) {e f : NumericEdge}
    (he : e ∈ exactEdges p) (hf : f ∈ exactEdges p) (eq : pointPair p e = pointPair p f) :
    e = f := by
  have be := raw_bounds p e he
  have bf := raw_bounds p f hf
  apply Prod.ext
  · have hv := congrArg (fun x : PiecePoint p × PiecePoint p => x.1.val) eq
    simpa only [pointPair, rawPoint_val p (be.1.trans be.2), rawPoint_val p (bf.1.trans bf.2)] using hv
  · have hv := congrArg (fun x : PiecePoint p × PiecePoint p => x.2.val) eq
    simpa only [pointPair, rawPoint_val p be.2, rawPoint_val p bf.2] using hv

theorem indexed_occurrence (p : Piece) (e : NumericEdge) (he : e ∈ exactEdges p) (v : PiecePoint p) :
    occursAt (indexOf (pieceEmbed p v)) (indexPieceEdge p e) = Gadget.incidence v.val e := by
  have bounds := raw_bounds p e he
  have hleft :
      indexOf (pieceEmbed p (rawPiecePoint p e.1)) = indexOf (pieceEmbed p v) ↔ e.1 = v.val := by
    rw [(point_index_inj p).eq_iff]
    constructor
    · intro h
      simpa only [rawPoint_val p (bounds.1.trans bounds.2)] using congrArg Fin.val h
    · intro h
      exact Fin.ext ((rawPoint_val p (bounds.1.trans bounds.2)).trans h)
  have hright :
      indexOf (pieceEmbed p (rawPiecePoint p e.2)) = indexOf (pieceEmbed p v) ↔ e.2 = v.val := by
    rw [(point_index_inj p).eq_iff]
    constructor
    · intro h
      simpa only [rawPoint_val p bounds.2] using congrArg Fin.val h
    · intro h
      exact Fin.ext ((rawPoint_val p bounds.2).trans h)
  apply Bool.eq_iff_iff.mpr
  unfold occursAt indexPieceEdge oriented Gadget.incidence
  split <;> simp only [Bool.or_eq_true, beq_iff_eq, hleft, hright, or_comm]

theorem indexed_no_occurrence (p : Piece) (e : NumericEdge) (w : PairPoint)
    (hw : w ∉ Set.range (pieceEmbed p)) :
    occursAt (indexOf w) (indexPieceEdge p e) = false := by
  have left : indexOf (pieceEmbed p (rawPiecePoint p e.1)) ≠ indexOf w := by
    intro h
    exact hw ⟨_, indexEquiv.injective h⟩
  have right : indexOf (pieceEmbed p (rawPiecePoint p e.2)) ≠ indexOf w := by
    intro h
    exact hw ⟨_, indexEquiv.injective h⟩
  unfold occursAt indexPieceEdge oriented
  split <;> simp [left, right]

def pickRaw (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (p : Piece) (e : NumericEdge) : Bool :=
  pickIndex A (indexPieceEdge p e)

def rawSelected (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (p : Piece) : List NumericEdge :=
  Gadget.kept (exactEdges p) (pickRaw A p) 0 (pieceSize p)


theorem rawSelected_mem (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (p : Piece) (e : NumericEdge) :
    e ∈ rawSelected A p ↔ e ∈ exactEdges p ∧ pickRaw A p e = true := by
  rw [rawSelected, Gadget.kept_mem_iff]
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · intro h
    refine ⟨h.1, h.2, Nat.zero_le _, ?_⟩
    simpa only [Nat.zero_add] using (raw_bounds p e h.1).1.trans (raw_bounds p e h.1).2

theorem rawSelected_picked (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (p : Piece) :
    (rawSelected A p).Perm (pickedPiece A exactEdges p) := by
  apply (List.perm_ext_iff_of_nodup (Gadget.kept_nodup (raw_nodup p) _ _ _)
    ((raw_nodup p).filter _)).mpr
  intro e
  change e ∈ rawSelected A p ↔ e ∈ pickedPiece A exactEdges p
  rw [rawSelected_mem, pickedPiece, List.mem_filter]
  rfl

theorem contribution_at (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (p : Piece)
    (v : PiecePoint p) :
    degreeContribution A exactEdges p (pieceEmbed p v) = Gadget.deg (rawSelected A p) v.val := by
  unfold degreeContribution Gadget.deg
  rw [(rawSelected_picked A p).countP_eq]
  apply List.countP_congr
  intro e he
  have h := indexed_occurrence p e (List.mem_filter.mp he).1 v
  rw [h]

theorem contribution_absent (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (p : Piece)
    (v : PairPoint) (h : v ∉ Set.range (pieceEmbed p)) :
    degreeContribution A exactEdges p v = 0 := by
  apply List.countP_eq_zero.mpr
  intro e _
  rw [indexed_no_occurrence p e v h]
  decide

def rawPieceGraph (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (p : Piece) :
    SimpleGraph (PiecePoint p) :=
  graphOfEdges ((rawSelected A p).map (pointPair p))

instance (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (p : Piece) :
    DecidableRel (rawPieceGraph A p).Adj := graphOfEdgesDecidable _

theorem rawPieceGraph_le (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (p : Piece) :
    rawPieceGraph A p ≤ A.comap (pieceEmbed p) := by
  intro u v h
  change u ≠ v ∧ ((u,v) ∈ (rawSelected A p).map (pointPair p) ∨
    (v,u) ∈ (rawSelected A p).map (pointPair p)) at h
  have lift {x y : PiecePoint p} (he : (x,y) ∈ (rawSelected A p).map (pointPair p)) :
      A.Adj (pieceEmbed p x) (pieceEmbed p y) := by
    obtain ⟨e, he, hxy⟩ := List.mem_map.mp he
    change (rawPiecePoint p e.1, rawPiecePoint p e.2) = (x,y) at hxy
    have hx : rawPiecePoint p e.1 = x := congrArg Prod.fst hxy
    have hy : rawPiecePoint p e.2 = y := congrArg Prod.snd hxy
    rw [← hx, ← hy]
    have chosen := (rawSelected_mem A p e).mp he
    have hsort : A.Adj (pointOf (indexPieceEdge p e).1) (pointOf (indexPieceEdge p e).2) :=
      of_decide_eq_true chosen.2
    have map := (oriented_mem_rel A pointOf
      (indexOf (pieceEmbed p (rawPiecePoint p e.1)))
      (indexOf (pieceEmbed p (rawPiecePoint p e.2)))).mp hsort
    simpa only [point_index] using map
  rcases h.2 with h | h
  · exact lift h
  · exact (lift h).symm

theorem rawPieceGraph_degree (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (p : Piece)
    (v : PiecePoint p) :
    (rawPieceGraph A p).degree v = Gadget.deg (rawSelected A p) v.val := by
  unfold rawPieceGraph
  have nodup : ((rawSelected A p).map (pointPair p)).Nodup := by
    apply List.Nodup.map_on _ (Gadget.kept_nodup (raw_nodup p) _ _ _)
    intro a ha b hb eq
    exact pointPair_inj_on p ((rawSelected_mem A p a).mp ha).1 ((rawSelected_mem A p b).mp hb).1 eq
  have sorted : ∀ e ∈ (rawSelected A p).map (pointPair p), e.1 < e.2 := by
    intro e he
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp he
    have b := raw_bounds p r ((rawSelected_mem A p r).mp hr).1
    change (rawPiecePoint p r.1).val < (rawPiecePoint p r.2).val
    rw [rawPoint_val p (b.1.trans b.2), rawPoint_val p b.2]
    exact b.1
  rw [degree_graphOfEdges _ nodup sorted]
  simp only [List.countP_map, Gadget.deg]
  apply List.countP_congr
  intro e he
  have b := raw_bounds p e ((rawSelected_mem A p e).mp he).1
  simp only [Function.comp_def, pointPair, Gadget.incidence, Bool.or_eq_true, beq_iff_eq,
    Fin.ext_iff, rawPoint_val p (b.1.trans b.2), rawPoint_val p b.2]


theorem finRange_sum (f : Piece → ℕ) :
    ((List.finRange 10).map f).sum = ∑ p : Piece, f p := by
  rw [← List.sum_toFinset _ (List.nodup_finRange 10), List.toFinset_finRange]

set_option maxRecDepth 20000 in
theorem joint_is_port (p : Piece) (v : PiecePoint p)
    (h : (pieceEmbed p v).1 ∈ jointPositions) : pieceIsPort p v := by
  have table : ∀ (p : Piece) (v : PiecePoint p), (pieceMap p v).1 ∈ jointPositions →
      pieceIsPort p v := by decide +kernel
  exact table p v h

theorem occurs_rung (w : PairPoint) (u : PairVertex) :
    occursAt (indexOf w) (indexRung u) = decide (u = w.1) := by
  obtain ⟨v,l⟩ := w
  have h0 : indexOf (u, 0) = indexOf (v, l) ↔ u = v ∧ 0 = l := by
    constructor
    · intro h
      have e : (u,(0 : Fin 2)) = (v,l) := indexEquiv.injective h
      exact ⟨congrArg (Prod.fst : PairPoint → PairVertex) e, congrArg (Prod.snd : PairPoint → Fin 2) e⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  have h1 : indexOf (u, 1) = indexOf (v, l) ↔ u = v ∧ 1 = l := by
    constructor
    · intro h
      have e : (u,(1 : Fin 2)) = (v,l) := indexEquiv.injective h
      exact ⟨congrArg (Prod.fst : PairPoint → PairVertex) e, congrArg (Prod.snd : PairPoint → Fin 2) e⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  apply Bool.eq_iff_iff.mpr
  unfold occursAt indexRung
  simp only [Bool.or_eq_true, beq_iff_eq, h0, h1, decide_eq_true_eq]
  fin_cases l <;> simp

theorem no_joint_contribution (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (w : PairPoint) (h : w.1 ∉ jointPositions) :
    (jointIndexEdges.filter (pickIndex A)).countP (occursAt (indexOf w)) = 0 := by
  apply List.countP_eq_zero.mpr
  intro e he
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (List.mem_filter.mp he).1
  rw [occurs_rung]
  intro hu'
  exact h ((of_decide_eq_true hu' : u = w.1) ▸ hu)

theorem degree_piece_interior (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (sub : A ≤ pairPrism)
    (p : Piece) (v : PiecePoint p) (interior : ¬ pieceIsPort p v) :
    A.degree (pieceEmbed p v) = (rawPieceGraph A p).degree v := by
  rw [degree_decompose A sub exactEdges exact_cover exact_unique exact_ordered, finRange_sum,
    no_joint_contribution A _ (fun h => interior (joint_is_port p v h)), add_zero,
    rawPieceGraph_degree]
  rw [Finset.sum_eq_single p]
  · exact contribution_at A p v
  · intro q _ hqp
    apply contribution_absent
    rintro ⟨w, hw⟩
    obtain ⟨_, b, _, hp⟩ := piece_overlap hqp hw
    rw [← hp] at interior
    exact interior (piecePort_isPort p b)
  · simp


theorem ordered_pair_eq_of_oriented {u v x y : Index} (h : oriented u v = oriented x y) :
    (u = x ∧ v = y) ∨ (u = y ∧ v = x) := by
  unfold oriented at h
  split at h <;> split at h <;> simp only [Prod.mk.injEq] at h <;> tauto

theorem index_rung_ordered (p : PairVertex) :
    indexOf (p, 0) < indexOf (p, 1) := by
  change 2 * p.val + 0 < 2 * p.val + 1
  omega

theorem chosen_edge_source (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism) {u v : PairPoint} (edge : A.Adj u v) :
    (∃ (p : Piece) (x y : PiecePoint p),
      pieceEmbed p x = u ∧ pieceEmbed p y = v ∧ (rawPieceGraph A p).Adj x y) ∨
    (∃ p ∈ jointPositions, (u = (p,0) ∧ v = (p,1)) ∨ (u = (p,1) ∧ v = (p,0))) := by
  have member := exact_cover _ (adjacent_index_edge (sub edge))
  unfold combinedIndexEdges at member
  rcases List.mem_append.mp member with part | vertical
  · obtain ⟨p, _, hp⟩ := List.mem_flatMap.mp part
    obtain ⟨r, hr, eq⟩ := List.mem_map.mp hp
    let x := rawPiecePoint p r.1
    let y := rawPiecePoint p r.2
    have pairEq : oriented (indexOf (pieceEmbed p x)) (indexOf (pieceEmbed p y)) =
        oriented (indexOf u) (indexOf v) := eq
    have he : A.Adj (pieceEmbed p x) (pieceEmbed p y) := by
      have left := oriented_mem_rel A pointOf (indexOf (pieceEmbed p x)) (indexOf (pieceEmbed p y))
      have right := oriented_mem_rel A pointOf (indexOf u) (indexOf v)
      rw [pairEq] at left
      simpa only [point_index] using left.mp (right.mpr (by simpa only [point_index] using edge))
    have selected : r ∈ rawSelected A p := by
      apply (rawSelected_mem A p r).mpr
      refine ⟨hr, ?_⟩
      exact decide_eq_true ((oriented_mem_rel A pointOf _ _).mpr (by simpa only [point_index] using he))
    have localEdge : (rawPieceGraph A p).Adj x y :=
      ⟨fun eq => he.ne (congrArg (pieceEmbed p) eq),
        Or.inl (List.mem_map.mpr ⟨r, selected, rfl⟩)⟩
    left
    rcases ordered_pair_eq_of_oriented pairEq with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact ⟨p, x, y, indexEquiv.injective hx, indexEquiv.injective hy, localEdge⟩
    · exact ⟨p, y, x, indexEquiv.injective hy, indexEquiv.injective hx, localEdge.symm⟩
  · obtain ⟨p, hp, eq⟩ := List.mem_map.mp vertical
    have pairEq : oriented (indexOf (p,0)) (indexOf (p,1)) = oriented (indexOf u) (indexOf v) := by
      simpa only [indexRung, oriented, index_rung_ordered p, if_true] using eq
    right
    refine ⟨p, hp, ?_⟩
    rcases ordered_pair_eq_of_oriented pairEq with ⟨hx, hy⟩ | ⟨hx, hy⟩
    · exact Or.inl ⟨(indexEquiv.injective hx).symm, (indexEquiv.injective hy).symm⟩
    · exact Or.inr ⟨(indexEquiv.injective hy).symm, (indexEquiv.injective hx).symm⟩

end PrismCounterexample

namespace PrismCounterexample

open SimpleGraph

section

variable {V W : Type*} [Fintype V] [Fintype W]
variable (C : SimpleGraph V) [DecidableRel C.Adj] (e : W ↪ V)
variable (A : SimpleGraph W) [DecidableRel A.Adj]

private theorem smallNeighbors_subset (hA : A ≤ C.comap e) (v : W) :
    (A.neighborFinset v).map e ⊆ C.neighborFinset (e v) := by
  intro w hw
  obtain ⟨z,hz,rfl⟩ := Finset.mem_map.mp hw
  exact (C.mem_neighborFinset (e v) (e z)).mpr (hA ((A.mem_neighborFinset v z).mp hz))

private theorem degree_lt_two_transfer (hA : A ≤ C.comap e)
    (degC : ∀ x, C.degree x ≤ 2)
    (openInRange : ∀ T : Finset V, T.Nonempty → (T : Set V) ⊆ Set.range e →
      (∀ x ∈ T, ∀ y, C.Adj x y → y ∈ T) → ∃ x ∈ T, C.degree x < 2)
    (S : Finset W) (hS : S.Nonempty)
    (closed : ∀ v ∈ S, ∀ w, A.Adj v w → w ∈ S) : ∃ v ∈ S, A.degree v < 2 := by
  by_contra! hdeg
  have edgeImage (v : W) (hv : v ∈ S) :
      (A.neighborFinset v).map e = C.neighborFinset (e v) := by
    apply Finset.eq_of_subset_of_card_le (smallNeighbors_subset C e A hA v)
    simpa only [Finset.card_map, card_neighborFinset_eq_degree] using (degC (e v)).trans (hdeg v hv)
  have imageClosed : ∀ x ∈ S.map e, ∀ y, C.Adj x y → y ∈ S.map e := by
    intro x hx y hadj
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hx
    have h : y ∈ (A.neighborFinset v).map e := by
      rw [edgeImage v hv]
      exact (C.mem_neighborFinset (e v) y).mpr hadj
    obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp h
    exact Finset.mem_map.mpr ⟨w,closed v hv w ((A.mem_neighborFinset v w).mp hw),rfl⟩
  have within : (S.map e : Set V) ⊆ Set.range e := by
    intro x hx
    obtain ⟨w,_,rfl⟩ := Finset.mem_map.mp (Finset.mem_coe.mp hx)
    exact ⟨w,rfl⟩
  obtain ⟨x,hx,hlt⟩ := openInRange (S.map e) hS.map within imageClosed
  obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hx
  have hcard := congrArg Finset.card (edgeImage w hw)
  simp only [Finset.card_map, card_neighborFinset_eq_degree] at hcard
  have := hdeg w hw
  omega

/-- A proper restriction of a connected cycle has a deficient vertex in every closed part. -/
theorem degree_lt_two_of_closed (hA : A ≤ C.comap e)
    (hC : C.Connected) (degC : ∀ x, C.degree x = 2)
    (out : V) (hout : out ∉ Set.range e) (S : Finset W) (hS : S.Nonempty)
    (closed : ∀ v ∈ S, ∀ w, A.Adj v w → w ∈ S) : ∃ v ∈ S, A.degree v < 2 := by
  apply degree_lt_two_transfer C e A hA (fun v => (degC v).le) ?_ S hS closed
  intro T hT within step
  obtain ⟨v,hv⟩ := hT
  obtain ⟨walk⟩ := hC v out
  have carry {x y : V} (p : C.Walk x y) : x ∈ T → y ∈ T := by
    induction p with
    | nil => exact id
    | cons h _ ih => exact fun hw => ih (step _ hw _ h)
  exact (hout (within (carry walk hv))).elim

private theorem color_has_open_port_aux {T : Type*} [DecidableEq T]
    (openColor : ∀ S : Finset W, S.Nonempty →
      (∀ u ∈ S, ∀ v, A.Adj u v → v ∈ S) → ∃ v ∈ S, A.degree v < 2)
    (ports : Finset W) (degreeInterior : ∀ v, v ∉ ports → A.degree v = 2)
    (color : W → T) (colorAdj : ∀ ⦃u v⦄, A.Adj u v → color u = color v) (v : W) :
    ∃ p ∈ ports, color p = color v ∧ A.degree p < 2 := by
  let S := Finset.univ.filter (fun w => color w = color v)
  have hs (w : W) : w ∈ S ↔ color w = color v := by simp [S]
  have closed (u : W) (hu : u ∈ S) (w : W) (huw : A.Adj u w) : w ∈ S :=
    (hs w).mpr ((colorAdj huw).symm.trans ((hs u).mp hu))
  obtain ⟨p,hp,hdeg⟩ := openColor S ⟨v,(hs v).mpr rfl⟩ closed
  have hport : p ∈ ports := by
    by_contra h
    rw [degreeInterior p h] at hdeg
    omega
  exact ⟨p,hport,(hs p).mp hp,hdeg⟩

/-- Every color represented by an actual vertex must occur at a deficient port. -/
theorem color_has_open_port {T : Type*} [DecidableEq T]
    (hA : A ≤ C.comap e) (hC : C.Connected) (degC : ∀ x, C.degree x = 2)
    (out : V) (hout : out ∉ Set.range e) (ports : Finset W)
    (degreeInterior : ∀ v, v ∉ ports → A.degree v = 2)
    (color : W → T) (colorAdj : ∀ ⦃u v⦄, A.Adj u v → color u = color v) (v : W) :
    ∃ p ∈ ports, color p = color v ∧ A.degree p < 2 :=
  color_has_open_port_aux A (degree_lt_two_of_closed C e A hA hC degC out hout)
    ports degreeInterior color colorAdj v

/-- The same property holds across a restriction when the ambient graph already has a
low-degree vertex in every nonempty closed set. -/
theorem color_has_open_port_of_no_full_closed {T : Type*} [DecidableEq T]
    (hA : A ≤ C.comap e) (degC : ∀ x, C.degree x ≤ 2)
    (openAmbient : ∀ S : Finset V, S.Nonempty →
      (∀ u ∈ S, ∀ v, C.Adj u v → v ∈ S) → ∃ v ∈ S, C.degree v < 2)
    (ports : Finset W) (degreeInterior : ∀ v, v ∉ ports → A.degree v = 2)
    (color : W → T) (colorAdj : ∀ ⦃u v⦄, A.Adj u v → color u = color v) (v : W) :
    ∃ p ∈ ports, color p = color v ∧ A.degree p < 2 :=
  color_has_open_port_aux A
    (degree_lt_two_transfer C e A hA degC (fun S hs _ => openAmbient S hs))
    ports degreeInterior color colorAdj v

end
/-- Local colors together with the tags assigned to their ports after gluing. -/
structure ColorPatch (W : Type*) where
  Local : Type
  embed : Local ↪ W
  color : Local → ℕ
  port : Fin 4 → Local
  tag : Fin 4 → ℕ
  representative : ∀ v, ∃ p, color v = color (port p)
  tag_compatible : ∀ p q, color (port p) = color (port q) → tag p = tag q

/-- A family of colored patches gives one coloring when their tags agree at shared ports. -/
theorem gluePortColors {W I : Type*} (patch : I → ColorPatch W)
    (cover : ∀ x, ∃ (i : I) (v : (patch i).Local), (patch i).embed v = x)
    (overlap : ∀ (i j : I), i ≠ j → ∀ (u : (patch i).Local) (v : (patch j).Local),
      (patch i).embed u = (patch j).embed v →
      ∃ p q, u = (patch i).port p ∧ v = (patch j).port q ∧ (patch i).tag p = (patch j).tag q) :
    ∃ color : W → ℕ,
      (∀ (i : I) (u v : (patch i).Local), (patch i).color u = (patch i).color v →
        color ((patch i).embed u) = color ((patch i).embed v)) ∧
      ∀ (i : I) (p : Fin 4), color ((patch i).embed ((patch i).port p)) = (patch i).tag p := by
  classical
  let rep (i : I) (v : (patch i).Local) : Fin 4 :=
    Classical.choose ((patch i).representative v)
  let ext (i : I) (v : (patch i).Local) : ℕ := (patch i).tag (rep i v)
  have repSpec (i : I) (v : (patch i).Local) :
      (patch i).color v = (patch i).color ((patch i).port (rep i v)) :=
    Classical.choose_spec ((patch i).representative v)
  have extColor (i : I) (u v : (patch i).Local) (h : (patch i).color u = (patch i).color v) :
      ext i u = ext i v :=
    (patch i).tag_compatible _ _ ((repSpec i u).symm.trans (h.trans (repSpec i v)))
  have extPort (i : I) (p : Fin 4) : ext i ((patch i).port p) = (patch i).tag p :=
    (patch i).tag_compatible _ _ (repSpec i ((patch i).port p)).symm
  have extOverlap (i j : I) (u : (patch i).Local) (v : (patch j).Local)
      (h : (patch i).embed u = (patch j).embed v) : ext i u = ext j v := by
    by_cases e : i = j
    · subst j
      rw [(patch i).embed.injective h]
    · obtain ⟨p,q,hu,hv,htag⟩ := overlap i j e u v h
      rw [hu,hv,extPort,extPort]
      exact htag
  let piece (x : W) : I := Classical.choose (cover x)
  let lift (x : W) : (patch (piece x)).Local := Classical.choose (Classical.choose_spec (cover x))
  let color (x : W) : ℕ := ext (piece x) (lift x)
  have chooseSpec (x : W) : (patch (piece x)).embed (lift x) = x :=
    Classical.choose_spec (Classical.choose_spec (cover x))
  have colorAt (i : I) (v : (patch i).Local) : color ((patch i).embed v) = ext i v :=
    extOverlap _ _ _ _ (chooseSpec ((patch i).embed v))
  refine ⟨color, ?_, ?_⟩
  · intro i u v h
    rw [colorAt, colorAt, extColor i u v h]
  · intro i p
    rw [colorAt, extPort]

end PrismCounterexample

namespace PrismCounterexample

open SimpleGraph

def physicalPorts (p : Piece) : Finset (PiecePoint p) :=
  Finset.univ.image (piecePort p)

theorem physicalPorts_spec (p : Piece) (v : PiecePoint p) :
    v ∈ physicalPorts p ↔ pieceIsPort p v := by
  constructor
  · intro h
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.mp h
    exact piecePort_isPort p q
  · intro h
    obtain ⟨q, rfl⟩ := piecePort_exists p v h
    exact Finset.mem_image.mpr ⟨q, Finset.mem_univ _, rfl⟩

theorem physicalPort_values (p : Piece) :
    (List.finRange 4).map (fun i => (piecePort p i).val) = Gadget.ports (pieceSize p) := by
  fin_cases p <;> decide

theorem gadgetPort_index (p : Piece) (q : Fin 4) :
    (Gadget.ports (pieceSize p))[q.val]! = (piecePort p q).val := by
  fin_cases p <;> fin_cases q <;> decide

theorem gadgetPort_pred (p : Piece) (v : PiecePoint p) :
    Gadget.isPort (pieceSize p) v.val = true ↔ pieceIsPort p v := by
  constructor
  · intro hv
    obtain ⟨q, _, h⟩ := List.mem_map.mp (by
      rw [physicalPort_values]
      exact List.contains_iff_mem.mp hv)
    have eq : piecePort p q = v := Fin.ext h
    exact eq ▸ piecePort_isPort p q
  · intro hv
    obtain ⟨q, rfl⟩ := piecePort_exists p v hv
    apply List.contains_iff_mem.mpr
    rw [← physicalPort_values]
    exact List.mem_map.mpr ⟨q, by simp, rfl⟩

theorem local_full_degree (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism) (full : ∀ v, v.1 ≠ 0 → v.1 ≠ 76 → A.degree v = 2)
    (p : Piece) (v : PiecePoint p) (hv : ¬ pieceIsPort p v) :
    (rawPieceGraph A p).degree v = 2 := by
  rw [← degree_piece_interior A sub p v hv]
  apply full
  · intro hz
    exact hv (joint_is_port p v (hz.symm ▸ (by decide : (0 : PairVertex) ∈ jointPositions)))
  · intro hz
    exact hv (joint_is_port p v (hz.symm ▸ (by decide : (76 : PairVertex) ∈ jointPositions)))

theorem local_degree_bound (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (degree : ∀ v, A.degree v ≤ 2) (p : Piece) (v : PiecePoint p) :
    (rawPieceGraph A p).degree v ≤ 2 := by
  have hb : (rawPieceGraph A p).degree v ≤ (A.comap (pieceEmbed p)).degree v :=
    (rawPieceGraph A p).degree_le_of_le (rawPieceGraph_le A p)
  exact hb.trans ((comapDegree_le A (pieceEmbed p) v).trans (degree _))

def actualSignature (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (p : Piece) :
    Gadget.Signature :=
  Gadget.normalized (Gadget.status (pieceSize p) (rawSelected A p)).1

theorem actualSig_degree (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (p : Piece) (q : Fin 4) :
    (actualSignature A p).1[q.val]! = Gadget.deg (rawSelected A p) (piecePort p q).val := by
  have h : q.val < (Gadget.ports (pieceSize p)).length := by simp [Gadget.ports]
  change ((Gadget.ports (pieceSize p)).map (Gadget.deg (rawSelected A p)))[q.val]! = _
  rw [getElem!_pos _ _ (by simpa only [List.length_map] using h), List.getElem_map,
    ← getElem!_pos (Gadget.ports (pieceSize p)) q.val h, gadgetPort_index]

def letterTable (p : Piece) : List Gadget.Signature :=
  if p.val % 5 = 4 then Gadget.cycleStates else Gadget.sideStates

end PrismCounterexample

namespace PrismCounterexample

def jointVertex (i : Fin 7) (l : Fin 2) : PairPoint :=
  (![0, 17, 34, 38, 55, 72, 76] i, l)

def lookupPiece (p : Piece) (w : PairPoint) : Option (PiecePoint p) :=
  (List.finRange (pieceSize p)).find? fun v => decide (pieceMap p v = w)

@[simp] theorem lookupPiece_eq_some {p : Piece} {w : PairPoint} {v : PiecePoint p} :
    lookupPiece p w = some v ↔ pieceEmbed p v = w := by
  constructor
  · intro h
    have h' := List.find?_some (p := fun x : PiecePoint p => decide (pieceMap p x = w)) h
    exact of_decide_eq_true h'
  · intro h
    cases he : lookupPiece p w with
    | none =>
      have hno := List.find?_eq_none.mp he v (List.mem_finRange v)
      exact (hno (decide_eq_true h)).elim
    | some u =>
      have hu : pieceEmbed p u = w := by
        have h' := List.find?_some (p := fun x : PiecePoint p => decide (pieceMap p x = w)) he
        exact of_decide_eq_true h'
      exact congrArg some ((pieceEmbed p).injective (hu.trans h.symm))

@[simp] theorem lookupPiece_eq_none {p : Piece} {w : PairPoint} :
    lookupPiece p w = none ↔ w ∉ Set.range (pieceEmbed p) := by
  constructor
  · rintro h ⟨v, hv⟩
    rw [lookupPiece_eq_some.mpr hv] at h
    cases h
  · intro h
    cases he : lookupPiece p w with
    | none => rfl
    | some v => exact (h ⟨v, lookupPiece_eq_some.mp he⟩).elim

/-- For each joint, record the incident pieces and the offset of the port for layer zero. -/
def jointPortTable (i : Fin 7) : List (Piece × ℕ) :=
  ![[(0,0),(1,0)],
    [(0,18),(1,18),(2,18),(3,18)],
    [(2,0),(3,0),(4,0)],
    [(4,8),(5,0),(6,0)],
    [(5,18),(6,18),(7,18),(8,18)],
    [(7,0),(8,0),(9,0)],
    [(9,8)]] i

private def incidences (ps : List Piece) (w : PairPoint) :
    List (Σ p : Piece, PiecePoint p) :=
  ps.filterMap fun p => (lookupPiece p w).map fun v => ⟨p, v⟩

private theorem joint_incidences (i : Fin 7) (l : Fin 2) :
    incidences (List.finRange 10) (jointVertex i l) =
      (jointPortTable i).map (fun e => ⟨e.1, rawPiecePoint e.1 (e.2 + l.val)⟩) := by
  fin_cases i <;> fin_cases l <;> rfl

private theorem incidences_sum (f : (p : Piece) → PiecePoint p → ℕ)
    (ps : List Piece) (w : PairPoint) :
    (ps.map fun p => ((lookupPiece p w).map (f p)).getD 0).sum =
      ((incidences ps w).map fun e => f e.1 e.2).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    simp only [incidences] at ih
    cases he : lookupPiece p w <;> simp [incidences, he, ih]

theorem joint_contribution_sum (f : (p : Piece) → PiecePoint p → ℕ)
    (i : Fin 7) (l : Fin 2) :
    ((List.finRange 10).map (fun p => ((lookupPiece p (jointVertex i l)).map (f p)).getD 0)).sum =
      ((jointPortTable i).map (fun e => f e.1 (rawPiecePoint e.1 (e.2 + l.val)))).sum := by
  rw [incidences_sum, joint_incidences]
  simp [List.map_map, Function.comp_def]

theorem contribution_via_lookup
    (d : Piece → PairPoint → ℕ) (f : (p : Piece) → PiecePoint p → ℕ)
    (at_piece : ∀ p v, d p (pieceEmbed p v) = f p v)
    (absent : ∀ p w, w ∉ Set.range (pieceEmbed p) → d p w = 0)
    (p : Piece) (w : PairPoint) :
    d p w = ((lookupPiece p w).map (f p)).getD 0 := by
  cases he : lookupPiece p w with
  | none => exact absent p w (lookupPiece_eq_none.mp he)
  | some v => rw [← lookupPiece_eq_some.mp he]; exact at_piece p v

theorem joint_contribution_of
    (d : Piece → PairPoint → ℕ) (f : (p : Piece) → PiecePoint p → ℕ)
    (at_piece : ∀ p v, d p (pieceEmbed p v) = f p v)
    (absent : ∀ p w, w ∉ Set.range (pieceEmbed p) → d p w = 0)
    (i : Fin 7) (l : Fin 2) :
    ((List.finRange 10).map (fun p => d p (jointVertex i l))).sum =
      ((jointPortTable i).map (fun e => f e.1 (rawPiecePoint e.1 (e.2 + l.val)))).sum := by
  simp only [contribution_via_lookup d f at_piece absent]
  exact joint_contribution_sum f i l

theorem single_piece_contribution_of
    (d : Piece → PairPoint → ℕ) (f : (p : Piece) → PiecePoint p → ℕ)
    (at_piece : ∀ p v, d p (pieceEmbed p v) = f p v)
    (absent : ∀ p w, w ∉ Set.range (pieceEmbed p) → d p w = 0)
    (p : Piece) (v : PiecePoint p) (h : ¬ pieceIsPort p v) :
    ((List.finRange 10).map (fun q => d q (pieceEmbed p v))).sum = f p v := by
  have only_p (q : Piece) (hne : q ≠ p) : d q (pieceEmbed p v) = 0 := by
    apply absent
    rintro ⟨w, hw⟩
    obtain ⟨a, _, ha, _⟩ := piece_overlap hne.symm hw.symm
    exact h (ha ▸ piecePort_isPort p a)
  rw [List.sum_map_eq_nsmul_single p _ (fun q hne _ => only_p q hne)]
  rw [List.count_eq_one_of_mem (List.nodup_finRange 10) (List.mem_finRange p),
    one_nsmul, at_piece]

private theorem piece_joint_port_check :
    ∀ (i : Fin 7) (l : Fin 2) (p : Piece) (v : PiecePoint p),
      pieceMap p v = jointVertex i l → pieceIsPort p v := by
  decide +kernel

theorem piece_joint_isPort (i : Fin 7) (l : Fin 2) (p : Piece) (v : PiecePoint p)
    (h : pieceEmbed p v = jointVertex i l) : pieceIsPort p v :=
  piece_joint_port_check i l p v h

/-- Exactly one of the seven possible joining rungs can be incident at a fixed joint. -/
theorem joint_positions_count (i : Fin 7) (f : PairVertex → Bool) :
    jointPositions.countP (fun x => (x == (jointVertex i 0).1) && f x) =
      (f (jointVertex i 0).1).toNat := by
  fin_cases i <;> simp [jointPositions, jointVertex, List.countP_cons, Bool.toNat]

theorem joint_rung_count {V : Type} [DecidableEq V] (encode : PairPoint ↪ V)
    (pick : (V × V) → Bool) (i : Fin 7) (l : Fin 2) :
    (((jointRungs.map fun e => (encode e.1, encode e.2)).filter pick).countP (fun e =>
      e.1 == encode (jointVertex i l) || e.2 == encode (jointVertex i l))) =
        (pick (encode (jointVertex i 0), encode (jointVertex i 1))).toNat := by
  rw [List.countP_filter, List.countP_map, jointRungs, List.countP_map]
  change _ = (pick (encode ((jointVertex i 0).1, 0), encode ((jointVertex i 0).1, 1))).toNat
  rw [← joint_positions_count i (fun x => pick (encode (x, 0), encode (x, 1)))]
  apply List.countP_congr
  intro x _
  simp only [Function.comp_apply]
  have h : (encode (x, 0) == encode (jointVertex i l) ||
      encode (x, 1) == encode (jointVertex i l)) = (x == (jointVertex i 0).1) := by
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, beq_iff_eq, encode.injective.eq_iff]
    fin_cases l <;> simp [jointVertex, Prod.ext_iff]
  rw [h]

end PrismCounterexample

namespace PrismCounterexample

open SimpleGraph

def jointRungSelected (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (i : Fin 7) : Bool :=
  decide (A.Adj (jointVertex i 0) (jointVertex i 1))

@[simp] theorem jointRungSelected_eq_true (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (i : Fin 7) : jointRungSelected A i = true ↔ A.Adj (jointVertex i 0) (jointVertex i 1) := by
  simp [jointRungSelected]

private theorem joint_port_bound (i : Fin 7) (l : Fin 2) :
    ∀ e ∈ jointPortTable i, e.2 + l.val < pieceSize e.1 := by
  have h : (jointPortTable i).all (fun e => decide (e.2 + l.val < pieceSize e.1)) = true := by
    fin_cases i <;> fin_cases l <;> rfl
  simpa only [List.all_eq_true, decide_eq_true_eq] using h

theorem joint_index_rung_count (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (i : Fin 7) (l : Fin 2) :
    (jointIndexEdges.filter (pickIndex A)).countP (occursAt (indexOf (jointVertex i l))) =
      (jointRungSelected A i).toNat := by
  change ((jointPositions.map fun x => (indexOf (x,0), indexOf (x,1))).filter
    (pickIndex A)).countP (fun e => e.1 == indexOf (jointVertex i l) ||
      e.2 == indexOf (jointVertex i l)) = (jointRungSelected A i).toNat
  have h := joint_rung_count indexEquiv.toEmbedding (pickIndex A) i l
  simpa only [jointRungs, List.map_map, Function.comp_def, Equiv.coe_toEmbedding, indexEquiv,
    Equiv.coe_fn_mk, pickIndex, point_index, jointRungSelected] using h

theorem joint_degree_eq (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism) (i : Fin 7) (l : Fin 2) :
    A.degree (jointVertex i l) =
      ((jointPortTable i).map (fun e =>
        Gadget.deg (rawSelected A e.1) (e.2 + l.val))).sum + (jointRungSelected A i).toNat := by
  rw [degree_decompose A sub exactEdges exact_cover exact_unique exact_ordered]
  rw [joint_contribution_of _ _ (contribution_at A) (contribution_absent A) i l]
  congr 1
  · apply congrArg List.sum
    apply List.map_congr_left
    intro e he
    rw [rawPoint_val _ (joint_port_bound i l e he)]
  · exact joint_index_rung_count A i l

theorem degree_joint0 (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism) (l : Fin 2) :
    A.degree (jointVertex 0 l) =
      Gadget.deg (rawSelected A 0) l.val +
      Gadget.deg (rawSelected A 1) l.val +
      (jointRungSelected A 0).toNat := by
  simpa [jointPortTable, add_assoc] using joint_degree_eq A sub 0 l

theorem degree_joint1 (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism) (l : Fin 2) :
    A.degree (jointVertex 1 l) =
      Gadget.deg (rawSelected A 0) (18 + l.val) +
      Gadget.deg (rawSelected A 1) (18 + l.val) +
      Gadget.deg (rawSelected A 2) (18 + l.val) +
      Gadget.deg (rawSelected A 3) (18 + l.val) +
      (jointRungSelected A 1).toNat := by
  simpa [jointPortTable, add_assoc] using joint_degree_eq A sub 1 l

theorem degree_joint2 (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism) (l : Fin 2) :
    A.degree (jointVertex 2 l) =
      Gadget.deg (rawSelected A 2) l.val +
      Gadget.deg (rawSelected A 3) l.val +
      Gadget.deg (rawSelected A 4) l.val +
      (jointRungSelected A 2).toNat := by
  simpa [jointPortTable, add_assoc] using joint_degree_eq A sub 2 l

theorem degree_joint3 (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism) (l : Fin 2) :
    A.degree (jointVertex 3 l) =
      Gadget.deg (rawSelected A 4) (8 + l.val) +
      Gadget.deg (rawSelected A 5) l.val +
      Gadget.deg (rawSelected A 6) l.val +
      (jointRungSelected A 3).toNat := by
  simpa [jointPortTable, add_assoc] using joint_degree_eq A sub 3 l

theorem degree_joint4 (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism) (l : Fin 2) :
    A.degree (jointVertex 4 l) =
      Gadget.deg (rawSelected A 5) (18 + l.val) +
      Gadget.deg (rawSelected A 6) (18 + l.val) +
      Gadget.deg (rawSelected A 7) (18 + l.val) +
      Gadget.deg (rawSelected A 8) (18 + l.val) +
      (jointRungSelected A 4).toNat := by
  simpa [jointPortTable, add_assoc] using joint_degree_eq A sub 4 l

theorem degree_joint5 (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism) (l : Fin 2) :
    A.degree (jointVertex 5 l) =
      Gadget.deg (rawSelected A 7) l.val +
      Gadget.deg (rawSelected A 8) l.val +
      Gadget.deg (rawSelected A 9) l.val +
      (jointRungSelected A 5).toNat := by
  simpa [jointPortTable, add_assoc] using joint_degree_eq A sub 5 l

theorem degree_joint6 (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism) (l : Fin 2) :
    A.degree (jointVertex 6 l) =
      Gadget.deg (rawSelected A 9) (8 + l.val) +
      (jointRungSelected A 6).toNat := by
  simpa [jointPortTable] using joint_degree_eq A sub 6 l

end PrismCounterexample

namespace PrismCounterexample.Gadget

def sameLabelEdges (offset : ℕ) (tagList : List ℕ) : List Edge :=
  (List.range 4).flatMap fun i =>
    ((List.range 4).filter fun j => i < j && tagList[i]! == tagList[j]!).map fun j => (offset+i, offset+j)

def projected (d : List ℕ) (tagArray : Array ℕ) (outer : List ℕ) : Option Signature :=
  let tags := outer.map fun o => tagArray[o]!
  let free := (d.zip tags).filterMap fun (v,a) => if v < 2 then some a else none
  if tagArray.toList.all free.contains then some (normalized (d,tags)) else none

def parallelTags (s t : Signature) : Array ℕ :=
  labels 4 (sameLabelEdges 0 s.2 ++ sameLabelEdges 0 t.2)

def parallel (s t : Signature) : Option Signature :=
  let d := (List.range 4).map fun i => s.1[i]! + t.1[i]!
  if d.all (· ≤ 2) then projected d (parallelTags s t) [0,1,2,3] else none

def serialTags (s t : Signature) (rung : Bool) : Array ℕ :=
  labels 6 (sameLabelEdges 0 s.2 ++ sameLabelEdges 2 t.2 ++ if rung then [(2,3)] else [])

def serial (s t : Signature) (rung : Bool) : Option Signature :=
  let r := if rung then 1 else 0
  if s.1[2]! + t.1[0]! + r = 2 ∧ s.1[3]! + t.1[1]! + r = 2 then
    projected [s.1[0]!,s.1[1]!,t.1[2]!,t.1[3]!] (serialTags s t rung) [0,1,4,5]
  else none

def swapSides (s : Signature) : Signature :=
  normalized (s.1.drop 2 ++ s.1.take 2, s.2.drop 2 ++ s.2.take 2)

def parallelStates : List Signature :=
  (sideStates.flatMap fun s => sideStates.filterMap (parallel s)).eraseDups

def mirroredStates : List Signature := parallelStates.map swapSides

def advance (left right : List Signature) : List Signature :=
  (left.flatMap fun s => right.flatMap fun t =>
    [false,true].filterMap (serial s t)).eraseDups

def firstTwoStates : List Signature := advance parallelStates mirroredStates
def firstBlockStates : List Signature := advance firstTwoStates cycleStates
def firstFourStates : List Signature := advance firstBlockStates parallelStates
def firstFiveStates : List Signature := advance firstFourStates mirroredStates
def allStates : List Signature := advance firstFiveStates cycleStates

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
theorem all_states_empty : allStates = [] := by
  decide +kernel

end PrismCounterexample.Gadget

namespace PrismCounterexample.Gadget

/-- Numbering of the two copies of all seven articulation or endpoint vertices. -/
def portSlot (p : Fin 10) (q : Fin 4) : Fin 14 :=
  ![![0,1,2,3], ![0,1,2,3], ![4,5,2,3], ![4,5,2,3], ![4,5,6,7],
    ![6,7,8,9], ![6,7,8,9], ![10,11,8,9], ![10,11,8,9], ![10,11,12,13]] p q

def rungLeft (i : Fin 5) : Fin 14 := ⟨2*(i.val+1), by omega⟩

def rungRight (i : Fin 5) : Fin 14 := ⟨2*(i.val+1)+1, by omega⟩

def outerPort (i : Fin 4) : Fin 14 := ![0,1,12,13] i

private def slotEdge (p : Fin 10) (e : Edge) : Edge :=
  ((portSlot p ⟨e.1 % 4, by omega⟩).val, (portSlot p ⟨e.2 % 4, by omega⟩).val)

def wholeTagEdges (states : Fin 10 → Signature) (rungs : Fin 5 → Bool) : List Edge :=
  ((List.finRange 10).flatMap fun p => ((sameLabelEdges 0 (states p).2).map (slotEdge p))) ++
    (((List.finRange 5).filter rungs).map fun i => ((rungLeft i).val, (rungRight i).val))

/-- The label array of the entire two-block restriction on its fourteen physical slots. -/
def wholeTags (states : Fin 10 → Signature) (rungs : Fin 5 → Bool) : Array ℕ :=
  labels 14 (wholeTagEdges states rungs)

@[simp] theorem wholeTags_size (states : Fin 10 → Signature) (rungs : Fin 5 → Bool) :
    (wholeTags states rungs).size = 14 := by simp [wholeTags]

theorem principalTagEdge (states : Fin 10 → Signature) (rungs : Fin 5 → Bool)
    (p : Fin 10) (i j : Fin 4) (h : (i : ℕ) < j.val)
    (hc : (states p).2[i.val]! = (states p).2[j.val]!) :
    ((portSlot p i).val, (portSlot p j).val) ∈ wholeTagEdges states rungs := by
  apply List.mem_append.mpr
  left
  apply List.mem_flatMap.mpr
  refine ⟨p, by simp, ?_⟩
  apply List.mem_map.mpr
  refine ⟨(i.val,j.val), ?_, ?_⟩
  · simp only [sameLabelEdges, List.mem_flatMap, List.mem_range, List.mem_map, List.mem_filter,
      Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Prod.mk.injEq, zero_add]
    exact ⟨i.val,i.isLt,j.val,⟨j.isLt,h,hc⟩,rfl,rfl⟩
  · simp [slotEdge, Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt]

private theorem wholeEdgeBounds (states : Fin 10 → Signature) (rungs : Fin 5 → Bool)
    (e : Edge) (he : e ∈ wholeTagEdges states rungs) : e.1 < 14 ∧ e.2 < 14 := by
  rcases List.mem_append.mp he with he | he
  · obtain ⟨p,_,hp⟩ := List.mem_flatMap.mp he
    obtain ⟨q,_,rfl⟩ := List.mem_map.mp hp
    exact ⟨(portSlot p _).isLt,(portSlot p _).isLt⟩
  · obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
    exact ⟨(rungLeft i).isLt,(rungRight i).isLt⟩

theorem wholeTags_port_eq (states : Fin 10 → Signature) (rungs : Fin 5 → Bool)
    (p : Fin 10) (i j : Fin 4) (hc : (states p).2[i.val]! = (states p).2[j.val]!) :
    (wholeTags states rungs)[(portSlot p i).val]! = (wholeTags states rungs)[(portSlot p j).val]! := by
  rcases lt_trichotomy i.val j.val with hi | eq | hj
  · exact labels_eq_of_mem 14 _ (wholeEdgeBounds states rungs) _
      (principalTagEdge states rungs p i j hi hc)
  · rw [Fin.ext eq]
  · exact (labels_eq_of_mem 14 _ (wholeEdgeBounds states rungs) _
      (principalTagEdge states rungs p j i hj hc.symm)).symm

theorem wholeTags_rung_eq (states : Fin 10 → Signature) (rungs : Fin 5 → Bool)
    (i : Fin 5) (h : rungs i = true) :
    (wholeTags states rungs)[(rungLeft i).val]! = (wholeTags states rungs)[(rungRight i).val]! := by
  apply labels_eq_of_mem 14 _ (wholeEdgeBounds states rungs) ((rungLeft i).val,(rungRight i).val)
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨i, by simp [h], rfl⟩

end PrismCounterexample.Gadget

namespace PrismCounterexample.Gadget

theorem mem_sameLabelEdges_iff (offset : ℕ) (cs : List ℕ) (a b : ℕ) :
    (a,b) ∈ sameLabelEdges offset cs ↔
      ∃ (i j : ℕ), i < 4 ∧ j < 4 ∧ i < j ∧ cs[i]! = cs[j]! ∧
        a = offset + i ∧ b = offset + j := by
  simp only [sameLabelEdges, List.mem_flatMap, List.mem_range, List.mem_map,
    List.mem_filter, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, Prod.mk.injEq]
  constructor
  · rintro ⟨i,hi,j,⟨hj,hh,he⟩,ha,hb⟩
    exact ⟨i,j,hi,hj,hh,he,ha.symm,hb.symm⟩
  · rintro ⟨i,j,hi,hj,hh,he,ha,hb⟩
    exact ⟨i,hi,j,⟨hj,hh,he⟩,ha.symm,hb.symm⟩

private theorem sameLabelEdges_bounds (offset : ℕ) (cs : List ℕ) {n : ℕ}
    (h : offset + 4 ≤ n) (e : Edge) (he : e ∈ sameLabelEdges offset cs) :
    e.1 < n ∧ e.2 < n := by
  obtain ⟨i,j,hi,hj,_,_,h₁,h₂⟩ := (mem_sameLabelEdges_iff offset cs e.1 e.2).mp he
  omega

private theorem tags_identify (n off : ℕ) (cs : List ℕ) (es : List Edge)
    (contained : ∀ e ∈ sameLabelEdges off cs, e ∈ es)
    (bounds : ∀ e ∈ es, e.1 < n ∧ e.2 < n)
    (i j : Fin 4) (h : cs[i.val]! = cs[j.val]!) :
    (labels n es)[off + i.val]! = (labels n es)[off + j.val]! := by
  rcases lt_trichotomy i.val j.val with hlt | heq | hlt
  · have ht := (mem_sameLabelEdges_iff off cs (off+i.val) (off+j.val)).mpr
      ⟨i.val,j.val,i.isLt,j.isLt,hlt,h,rfl,rfl⟩
    exact labels_eq_of_mem n es bounds _ (contained _ ht)
  · rw [heq]
  · have ht := (mem_sameLabelEdges_iff off cs (off+j.val) (off+i.val)).mpr
      ⟨j.val,i.val,j.isLt,i.isLt,hlt,h.symm,rfl,rfl⟩
    exact (labels_eq_of_mem n es bounds _ (contained _ ht)).symm

private theorem parallelEdgeBounds (s t : Signature) (e : Edge)
    (h : e ∈ sameLabelEdges 0 s.2 ++ sameLabelEdges 0 t.2) : e.1 < 4 ∧ e.2 < 4 := by
  rcases List.mem_append.mp h with h | h
  · exact sameLabelEdges_bounds 0 s.2 (by decide) _ h
  · exact sameLabelEdges_bounds 0 t.2 (by decide) _ h

theorem parallelTags_left (s t : Signature) (i j : Fin 4) (h : s.2[i.val]! = s.2[j.val]!) :
    (parallelTags s t)[i.val]! = (parallelTags s t)[j.val]! := by
  simpa [parallelTags] using tags_identify 4 0 s.2 _
    (fun e he => List.mem_append.mpr (Or.inl he)) (parallelEdgeBounds s t) i j h

theorem parallelTags_right (s t : Signature) (i j : Fin 4) (h : t.2[i.val]! = t.2[j.val]!) :
    (parallelTags s t)[i.val]! = (parallelTags s t)[j.val]! := by
  simpa [parallelTags] using tags_identify 4 0 t.2 _
    (fun e he => List.mem_append.mpr (Or.inr he)) (parallelEdgeBounds s t) i j h

private theorem serialEdgeBounds (s t : Signature) (rung : Bool) (e : Edge)
    (h : e ∈ sameLabelEdges 0 s.2 ++ sameLabelEdges 2 t.2 ++ if rung then [(2,3)] else []) :
    e.1 < 6 ∧ e.2 < 6 := by
  rcases List.mem_append.mp h with h | h
  · rcases List.mem_append.mp h with h | h
    · exact sameLabelEdges_bounds 0 s.2 (by decide) _ h
    · exact sameLabelEdges_bounds 2 t.2 (by decide) _ h
  · cases rung <;> simp_all

theorem serialTags_left (s t : Signature) (rung : Bool) (i j : Fin 4)
    (h : s.2[i.val]! = s.2[j.val]!) :
    (serialTags s t rung)[i.val]! = (serialTags s t rung)[j.val]! := by
  simpa [serialTags] using tags_identify 6 0 s.2 _
    (fun e he => by simp [he]) (serialEdgeBounds s t rung) i j h

theorem serialTags_right (s t : Signature) (rung : Bool) (i j : Fin 4)
    (h : t.2[i.val]! = t.2[j.val]!) :
    (serialTags s t rung)[2+i.val]! = (serialTags s t rung)[2+j.val]! := by
  exact tags_identify 6 2 t.2 _ (fun e he => by simp [he]) (serialEdgeBounds s t rung) i j h

theorem serialTags_rung (s t : Signature) :
    (serialTags s t true)[2]! = (serialTags s t true)[3]! := by
  apply labels_eq_of_mem 6 _ (serialEdgeBounds s t true) (2,3)
  simp

/-- Normalization preserves the equality relation of any two in-range labels. -/
theorem normalized_eq_iff (d cs : List ℕ) (i j : Fin cs.length) :
    (normalized (d,cs)).2[i.val]! = (normalized (d,cs)).2[j.val]! ↔ cs[i.val]! = cs[j.val]! := by
  let m := cs.map fun x => cs.idxOf x
  have hi : i.val < m.length := by simp [m, i.isLt]
  have hj : j.val < m.length := by simp [m, j.isLt]
  change m[i.val]! = m[j.val]! ↔ _
  rw [getElem!_pos m _ hi, getElem!_pos m _ hj,
    getElem!_pos cs _ i.isLt, getElem!_pos cs _ j.isLt]
  simp only [m, List.getElem_map]
  exact List.idxOf_inj (List.getElem_mem i.isLt)

/-- The projection succeeds whenever every input tag occurs at an outer port with degree below two. -/
theorem projected_of_open (d : List ℕ) (cs : Array ℕ) (outer : List ℕ)
    (length : d.length = outer.length)
    (h : ∀ i : Fin cs.size, ∃ j : Fin outer.length,
      d[j.val]! < 2 ∧ cs[outer[j.val]!]! = cs[i.val]!) :
    projected d cs outer = some (normalized (d, outer.map fun o => cs[o]!)) := by
  let tags := outer.map fun o => cs[o]!
  let free := (d.zip tags).filterMap fun (v,a) => if v < 2 then some a else none
  have hfree : cs.toList.all free.contains = true := by
    rw [List.all_eq_true]
    intro x hx
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hx
    have hi' : i < cs.size := by simpa using hi
    obtain ⟨j,hj,hj'⟩ := h ⟨i,hi'⟩
    have hjd : j.val < d.length := by simp [length, j.isLt]
    have hjt : j.val < tags.length := by simp [tags, j.isLt]
    have hjz : j.val < (d.zip tags).length := by simp [List.length_zip,hjd,hjt]
    apply List.elem_iff.mpr
    apply List.mem_filterMap.mpr
    refine ⟨(d.zip tags)[j.val], List.getElem_mem hjz, ?_⟩
    rw [List.getElem_zip, ← getElem!_pos d _ hjd, ← getElem!_pos tags _ hjt]
    simp only [hj, if_true, Option.some.injEq]
    rw [getElem!_pos tags _ hjt]
    simp only [tags, List.getElem_map]
    rw [← getElem!_pos outer _ j.isLt, hj', getElem!_pos cs _ hi']
    exact he
  change (if cs.toList.all free.contains then some (normalized (d,tags)) else none) = _
  rw [if_pos hfree]

/-- A glued edge-invariant coloring of the actual restricted graph certifies its projected state. -/
theorem projected_from_coloring {V W : Type*} [Fintype V] [Fintype W] [DecidableEq W]
    (C : SimpleGraph V) [DecidableRel C.Adj] (e : W ↪ V)
    (A : SimpleGraph W) [DecidableRel A.Adj] (hA : A ≤ C.comap e)
    (degC : ∀ x, C.degree x ≤ 2)
    (openAmbient : ∀ S : Finset V, S.Nonempty →
       (∀ u ∈ S, ∀ v, C.Adj u v → v ∈ S) → ∃ v ∈ S, C.degree v < 2)
    (d : List ℕ) (tags : Array ℕ) (outer : List ℕ) (length : d.length = outer.length)
    (site : Fin tags.size → W) (pick : Fin outer.length → W)
    (degreeInterior : ∀ v, (∀ j, v ≠ pick j) → A.degree v = 2)
    (color : W → ℕ) (colorAdj : ∀ ⦃u v⦄, A.Adj u v → color u = color v)
    (matchSite : ∀ i, color (site i) = tags[i.val]!)
    (matchPick : ∀ j, color (pick j) = tags[outer[j.val]!]! ∧ A.degree (pick j) = d[j.val]!) :
    projected d tags outer = some (normalized (d, outer.map fun o => tags[o]!)) := by
  apply projected_of_open _ _ _ length
  intro i
  let ports : Finset W := Finset.univ.image pick
  have hInterior (v : W) (hv : v ∉ ports) : A.degree v = 2 := by
    apply degreeInterior v
    intro j h
    exact hv (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, h.symm⟩)
  obtain ⟨p,hp,hcolor,hdeg⟩ := color_has_open_port_of_no_full_closed C e A hA degC
    openAmbient ports hInterior color colorAdj (site i)
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hp
  rw [(matchPick j).1, matchSite i] at hcolor
  rw [(matchPick j).2] at hdeg
  exact ⟨j,hdeg,hcolor⟩

/-- A patch cover with numbered port sites gives a coloring of the glued graph. -/
theorem glueColorFromTags {W I : Type*} (A : SimpleGraph W) (tags : Array ℕ)
    (site : Fin tags.size → W) (siteInj : Function.Injective site)
    (patch : I → ColorPatch W) (slot : I → Fin 4 → Fin tags.size)
    (portSite : ∀ i p, (patch i).embed ((patch i).port p) = site (slot i p))
    (portTag : ∀ i p, (patch i).tag p = tags[(slot i p).val]!)
    (siteCover : ∀ j, ∃ i p, slot i p = j)
    (cover : ∀ x, ∃ (i : I) (v : (patch i).Local), (patch i).embed v = x)
    (overlap : ∀ (i j : I), i ≠ j → ∀ (u : (patch i).Local) (v : (patch j).Local),
      (patch i).embed u = (patch j).embed v → ∃ p q, u = (patch i).port p ∧ v = (patch j).port q)
    (edgeSource : ∀ u v, A.Adj u v →
      (∃ (i : I) (a b : (patch i).Local), (patch i).embed a = u ∧ (patch i).embed b = v ∧
        (patch i).color a = (patch i).color b) ∨
      (∃ a b : Fin tags.size, site a = u ∧ site b = v ∧ tags[a.val]! = tags[b.val]!)) :
    ∃ color : W → ℕ, (∀ ⦃u v⦄, A.Adj u v → color u = color v) ∧
      ∀ j, color (site j) = tags[j.val]! := by
  have inter (i j : I) (hij : i ≠ j) (u : (patch i).Local) (v : (patch j).Local)
      (h : (patch i).embed u = (patch j).embed v) :
      ∃ p q, u = (patch i).port p ∧ v = (patch j).port q ∧ (patch i).tag p = (patch j).tag q := by
    obtain ⟨p,q,rfl,rfl⟩ := overlap i j hij u v h
    have eqSlot : slot i p = slot j q := siteInj ((portSite i p).symm.trans (h.trans (portSite j q)))
    exact ⟨p,q,rfl,rfl,by rw [portTag,portTag,eqSlot]⟩
  obtain ⟨color,sourceColor,colorPort⟩ := gluePortColors patch cover inter
  have siteColor (j : Fin tags.size) : color (site j) = tags[j.val]! := by
    obtain ⟨i,p,rfl⟩ := siteCover j
    rw [← portSite, colorPort, portTag]
  exact ⟨color, fun u v h => by
    rcases edgeSource u v h with ⟨i,a,b,rfl,rfl,e⟩ | ⟨a,b,rfl,rfl,e⟩
    · exact sourceColor i a b e
    · rw [siteColor, siteColor, e], siteColor⟩

/-- A projected state's normalized port list records the equality relation of its outer tags. -/
theorem projected_outerTags_eq_iff (d : List ℕ) (tagArray : Array ℕ) (outer : List ℕ)
    (i j : Fin outer.length) :
    (normalized (d, outer.map fun o => tagArray[o]!)).2[i.val]! =
      (normalized (d, outer.map fun o => tagArray[o]!)).2[j.val]! ↔
      tagArray[outer[i.val]!]! = tagArray[outer[j.val]!]! := by
  let tags := outer.map fun o => tagArray[o]!
  have hi : i.val < tags.length := by simp [tags, i.isLt]
  have hj : j.val < tags.length := by simp [tags, j.isLt]
  change (normalized (d,tags)).2[i.val]! = (normalized (d,tags)).2[j.val]! ↔ _
  rw [normalized_eq_iff d tags ⟨i.val,hi⟩ ⟨j.val,hj⟩]
  change tags[i.val]! = tags[j.val]! ↔ _
  rw [getElem!_pos tags i.val hi, getElem!_pos tags j.val hj,
    getElem!_pos outer i.val i.isLt, getElem!_pos outer j.val j.isLt]
  simp only [tags, List.getElem_map]

end PrismCounterexample.Gadget

namespace PrismCounterexample.Gadget

def rawParallelDegrees (s t : Signature) : List ℕ :=
  (List.range 4).map fun i => s.1[i]! + t.1[i]!

def rawParallel (s t : Signature) : Signature :=
  normalized (rawParallelDegrees s t, (List.range 4).map fun i => (parallelTags s t)[i]!)

def rawStates : List Signature := [
  ([0, 0, 2, 2], [0, 1, 2, 2]),
  ([0, 1, 1, 2], [0, 1, 1, 1]),
  ([0, 1, 2, 1], [0, 1, 1, 1]),
  ([0, 2, 0, 2], [0, 1, 2, 1]),
  ([0, 2, 1, 1], [0, 1, 1, 1]),
  ([0, 2, 2, 0], [0, 1, 1, 3]),
  ([0, 2, 2, 2], [0, 1, 1, 1]),
  ([1, 0, 1, 2], [0, 1, 0, 0]),
  ([1, 0, 2, 1], [0, 1, 0, 0]),
  ([1, 1, 0, 2], [0, 0, 2, 0]),
  ([1, 1, 1, 1], [0, 1, 0, 1]),
  ([1, 1, 1, 1], [0, 1, 1, 0]),
  ([1, 1, 2, 0], [0, 0, 0, 3]),
  ([1, 1, 2, 2], [0, 0, 0, 0]),
  ([1, 1, 2, 2], [0, 0, 2, 2]),
  ([1, 2, 1, 2], [0, 0, 0, 0]),
  ([1, 2, 1, 2], [0, 1, 0, 1]),
  ([1, 2, 2, 1], [0, 0, 0, 0]),
  ([1, 2, 2, 1], [0, 1, 1, 0]),
  ([2, 0, 0, 2], [0, 1, 2, 0]),
  ([2, 0, 1, 1], [0, 1, 0, 0]),
  ([2, 0, 2, 0], [0, 1, 0, 3]),
  ([2, 0, 2, 2], [0, 1, 0, 0]),
  ([2, 1, 1, 2], [0, 0, 0, 0]),
  ([2, 1, 1, 2], [0, 1, 1, 0]),
  ([2, 1, 2, 1], [0, 0, 0, 0]),
  ([2, 1, 2, 1], [0, 1, 0, 1]),
  ([2, 2, 0, 2], [0, 0, 2, 0]),
  ([2, 2, 1, 1], [0, 0, 0, 0]),
  ([2, 2, 2, 0], [0, 0, 0, 3]),
  ([2, 2, 2, 2], [0, 0, 0, 0]),
  ([2, 2, 2, 2], [0, 0, 2, 2]),
  ([2, 2, 2, 2], [0, 1, 0, 1]),
  ([2, 2, 2, 2], [0, 1, 1, 0])]

def mirroredRawStates : List Signature := rawStates.map swapSides

def outerSlots : List ℕ := [0,1,12,13]

def lineEdges (blocks : List Signature) (rungs : List Bool) : List Edge :=
  ((List.range 6).flatMap fun i => sameLabelEdges (2*i) (blocks[i]!.2)) ++
    (((List.range 5).filter fun i => rungs[i]!).map fun i => (2*i+2,2*i+3))

def lineTags (blocks : List Signature) (rungs : List Bool) : Array ℕ :=
  labels 14 (lineEdges blocks rungs)

def outerDegrees (blocks : List Signature) : List ℕ :=
  [blocks[0]!.1[0]!, blocks[0]!.1[1]!, blocks[5]!.1[2]!, blocks[5]!.1[3]!]

def jointOK (a b : Signature) (rung : Bool) : Bool :=
  let r := if rung then 1 else 0
  decide (a.1[2]! + b.1[0]! + r = 2 ∧ a.1[3]! + b.1[1]! + r = 2)

def allowedNext (previous : Signature) (possible : List Signature) : List (Signature × Bool) :=
  possible.flatMap fun s =>
    [false,true].filterMap fun r => if jointOK previous s r then some (s,r) else none

theorem allowedNext_mem {previous state : Signature} {possible : List Signature} {rung : Bool}
    (hs : state ∈ possible) (hr : jointOK previous state rung = true) :
    (state,rung) ∈ allowedNext previous possible := by
  refine List.mem_flatMap.mpr ⟨state, hs, List.mem_filterMap.mpr ⟨rung, by cases rung <;> simp, ?_⟩⟩
  rw [if_pos hr]

def rejectLine (blocks : List Signature) (rungs : List Bool) : Bool :=
  (projected (outerDegrees blocks) (lineTags blocks rungs) outerSlots).isNone

def checkLine (j₁ : Signature) : Bool :=
  (allowedNext j₁ mirroredRawStates).all fun (l₁,a) =>
  (allowedNext l₁ cycleStates).all fun (r₁,b) =>
  (allowedNext r₁ rawStates).all fun (j₂,c) =>
  (allowedNext j₂ mirroredRawStates).all fun (l₂,d) =>
  (allowedNext l₂ cycleStates).all fun (r₂,e) =>
    rejectLine [j₁,l₁,r₁,j₂,l₂,r₂] [a,b,c,d,e]

end PrismCounterexample.Gadget

namespace PrismCounterexample.Gadget

open SimpleGraph

/-- The physical vertex indicated by each of the fourteen numbered port slots. -/
def physicalSite (j : Fin 14) : PairPoint :=
  jointVertex ⟨j.val / 2, by omega⟩ ⟨j.val % 2, by omega⟩

private theorem physicalSite_table :
    ∀ i j : Fin 14, physicalSite i = physicalSite j → i = j := by decide +kernel

private theorem siteCover_table : ∀ j : Fin 14, ∃ p : Piece, ∃ q : Fin 4,
    portSlot p q = j := by decide +kernel

theorem port_is_physical (p : Piece) (q : Fin 4) :
    pieceEmbed p (piecePort p q) = physicalSite (portSlot p q) := by
  have h : ∀ (p : Piece) (q : Fin 4), pieceMap p (piecePort p q) = physicalSite (portSlot p q) := by
    decide +kernel
  exact h p q

@[simp] theorem physical_rung_left (i : Fin 5) :
    physicalSite (rungLeft i) = jointVertex ⟨i.val+1,by omega⟩ 0 := by
  fin_cases i <;> rfl

@[simp] theorem physical_rung_right (i : Fin 5) :
    physicalSite (rungRight i) = jointVertex ⟨i.val+1,by omega⟩ 1 := by
  fin_cases i <;> rfl

private theorem outerPort_index (i : Fin 4) : outerSlots[i.val]! = (outerPort i).val := by
  fin_cases i <;> rfl

/-- An actual graph with no closed 2-regular component gives an accepting physical-port state. -/
theorem projectedPhysical_some (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (degA : ∀ x, A.degree x ≤ 2)
    (openA : ∀ S : Finset PairPoint, S.Nonempty →
      (∀ u ∈ S, ∀ v, A.Adj u v → v ∈ S) → ∃ v ∈ S, A.degree v < 2)
    (tags : Array ℕ) (tagSize : tags.size = 14)
    (localColor : ∀ p : Piece, PiecePoint p → ℕ)
    (representative : ∀ p v, ∃ q, localColor p v = localColor p (piecePort p q))
    (tagEq : ∀ p q q', localColor p (piecePort p q) = localColor p (piecePort p q') →
      tags[(portSlot p q).val]! = tags[(portSlot p q').val]!)
    (rungs : Fin 5 → Bool)
    (tagRung : ∀ i, rungs i = true → tags[(rungLeft i).val]! = tags[(rungRight i).val]!)
    (edgeSource : ∀ u v, A.Adj u v →
      (∃ (p : Piece) (a b : PiecePoint p), pieceEmbed p a = u ∧ pieceEmbed p b = v ∧
        localColor p a = localColor p b) ∨
      (∃ i, rungs i = true ∧
        ((physicalSite (rungLeft i) = u ∧ physicalSite (rungRight i) = v) ∨
        (physicalSite (rungRight i) = u ∧ physicalSite (rungLeft i) = v))))
    (d : List ℕ) (dLength : d.length = 4)
    (dSpec : ∀ i : Fin 4, A.degree (physicalSite (outerPort i)) = d[i.val]!)
    (interior : ∀ v : PairPoint, v.1 ≠ 0 → v.1 ≠ 76 → A.degree v = 2) :
    projected d tags outerSlots = some (normalized (d, outerSlots.map fun o => tags[o]!)) := by
  let site (i : Fin tags.size) : PairPoint := physicalSite (i.cast tagSize)
  have siteInj : Function.Injective site := by
    intro i j hij
    have h := physicalSite_table (i.cast tagSize) (j.cast tagSize) hij
    exact Fin.ext (congrArg (fun a : Fin 14 => a.val) h)
  let patch (p : Piece) : ColorPatch PairPoint :=
    ⟨PiecePoint p, pieceEmbed p, localColor p, piecePort p,
      fun q => tags[(portSlot p q).val]!, representative p, tagEq p⟩
  let slot (p : Piece) (q : Fin 4) : Fin tags.size := (portSlot p q).cast tagSize.symm
  have hSiteCover (j : Fin tags.size) : ∃ p q, slot p q = j := by
    obtain ⟨p,q,h⟩ := siteCover_table (j.cast tagSize)
    exact ⟨p,q,Fin.ext (congrArg (fun a : Fin 14 => a.val) h)⟩
  have hEdges (u v : PairPoint) (h : A.Adj u v) :
      (∃ (p : Piece) (a b : (patch p).Local), (patch p).embed a = u ∧ (patch p).embed b = v ∧
        (patch p).color a = (patch p).color b) ∨
      (∃ a b : Fin tags.size, site a = u ∧ site b = v ∧ tags[a.val]! = tags[b.val]!) := by
    rcases edgeSource u v h with he | ⟨i,hi,he | he⟩
    · exact Or.inl he
    · exact Or.inr ⟨(rungLeft i).cast tagSize.symm,(rungRight i).cast tagSize.symm,
        he.1,he.2,tagRung i hi⟩
    · exact Or.inr ⟨(rungRight i).cast tagSize.symm,(rungLeft i).cast tagSize.symm,
        he.1,he.2,(tagRung i hi).symm⟩
  obtain ⟨color,colorAdj,matchSite⟩ := glueColorFromTags A tags site siteInj patch slot
    (fun p q => port_is_physical p q) (fun _ _ => rfl) hSiteCover piece_cover
    (fun _ _ hij _ _ h => by
      obtain ⟨p,q,hp,hq⟩ := piece_overlap hij h
      exact ⟨p,q,hp.symm,hq.symm⟩) hEdges
  let pick (i : Fin outerSlots.length) : PairPoint := physicalSite (outerPort i)
  have dEq : d.length = outerSlots.length := dLength
  have hInterior (v : PairPoint) (avoid : ∀ j, v ≠ pick j) : A.degree v = 2 := by
    apply interior
    · intro h
      obtain ⟨p,k⟩ := v
      change p = 0 at h
      subst p
      fin_cases k
      · exact avoid ⟨0,by decide⟩ rfl
      · exact avoid ⟨1,by decide⟩ rfl
    · intro h
      obtain ⟨p,k⟩ := v
      change p = 76 at h
      subst p
      fin_cases k
      · exact avoid ⟨2,by decide⟩ rfl
      · exact avoid ⟨3,by decide⟩ rfl
  have hPick (i : Fin outerSlots.length) :
      color (pick i) = tags[outerSlots[i.val]!]! ∧ A.degree (pick i) = d[i.val]! := by
    refine ⟨?_,dSpec i⟩
    rw [outerPort_index i]
    exact matchSite ((outerPort i).cast tagSize.symm)
  exact projected_from_coloring A (Function.Embedding.refl _) A (fun _ _ h => h)
    degA openA d tags outerSlots dEq site pick hInterior color colorAdj matchSite hPick

end PrismCounterexample.Gadget

namespace PrismCounterexample.Gadget

def blocksFrom (states : Fin 10 → Signature) : List Signature :=
  [rawParallel (states 0) (states 1), swapSides (rawParallel (states 2) (states 3)), states 4,
   rawParallel (states 5) (states 6), swapSides (rawParallel (states 7) (states 8)), states 9]

private def pieceBlock (p : Fin 10) : Fin 6 := ![0,0,1,1,2,3,3,4,4,5] p

private def withinBlock (p : Fin 10) (q : Fin 4) : Fin 4 :=
  if p.val = 2 ∨ p.val = 3 ∨ p.val = 7 ∨ p.val = 8 then q + 2 else q

private theorem slot_value (p : Fin 10) (i : Fin 4) :
    (portSlot p i).val = 2*(pieceBlock p).val + (withinBlock p i).val := by
  have h : ∀ (p : Fin 10) (i : Fin 4),
      (portSlot p i).val = 2*(pieceBlock p).val + (withinBlock p i).val := by decide +kernel
  exact h p i

private theorem range4_map_at (f : ℕ → ℕ) (i : Fin 4) :
    ((List.range 4).map f)[i.val]! = f i.val := by fin_cases i <;> rfl

theorem rawParallel_degree_at (s t : Signature) (i : Fin 4) :
    (rawParallel s t).1[i.val]! = s.1[i.val]! + t.1[i.val]! :=
  range4_map_at (fun k => s.1[k]! + t.1[k]!) i

private theorem rawParallel_label_eq_iff (s t : Signature) (i j : Fin 4) :
    (rawParallel s t).2[i.val]! = (rawParallel s t).2[j.val]! ↔
      (parallelTags s t)[i.val]! = (parallelTags s t)[j.val]! := by
  let tags := (List.range 4).map fun k => (parallelTags s t)[k]!
  have hlen : tags.length = 4 := by simp [tags]
  change (normalized (rawParallelDegrees s t,tags)).2[i.val]! =
    (normalized (rawParallelDegrees s t,tags)).2[j.val]! ↔ _
  rw [normalized_eq_iff _ tags ⟨i.val,by rw [hlen]; exact i.isLt⟩
    ⟨j.val,by rw [hlen]; exact j.isLt⟩]
  exact iff_of_eq (congrArg₂ Eq (range4_map_at _ i) (range4_map_at _ j))

private theorem rawParallel_left (s t : Signature) (i j : Fin 4)
    (h : s.2[i.val]! = s.2[j.val]!) :
    (rawParallel s t).2[i.val]! = (rawParallel s t).2[j.val]! :=
  (rawParallel_label_eq_iff s t i j).mpr (parallelTags_left s t i j h)

private theorem rawParallel_right (s t : Signature) (i j : Fin 4)
    (h : t.2[i.val]! = t.2[j.val]!) :
    (rawParallel s t).2[i.val]! = (rawParallel s t).2[j.val]! :=
  (rawParallel_label_eq_iff s t i j).mpr (parallelTags_right s t i j h)

private theorem rotate_at (cs : List ℕ) (h : cs.length = 4) (i : Fin 4) :
    (cs.drop 2 ++ cs.take 2)[(i+2 : Fin 4).val]! = cs[i.val]! := by
  rcases cs with _ | ⟨a, cs⟩
  · simp at h
  rcases cs with _ | ⟨b, cs⟩
  · simp at h
  rcases cs with _ | ⟨cc, cs⟩
  · simp at h
  rcases cs with _ | ⟨d, cs⟩
  · simp at h
  cases cs with
  | nil => fin_cases i <;> rfl
  | cons e cs => simp at h

private theorem rawParallel_degs_len (s t : Signature) : (rawParallel s t).1.length = 4 := by
  simp [rawParallel, normalized, rawParallelDegrees]

private theorem rawParallel_labs_len (s t : Signature) : (rawParallel s t).2.length = 4 := by
  simp [rawParallel, normalized]

theorem mirror_degree_at (s t : Signature) (i : Fin 4) :
    (swapSides (rawParallel s t)).1[(i+2 : Fin 4).val]! = s.1[i.val]! + t.1[i.val]! := by
  rw [show (swapSides (rawParallel s t)).1 =
    ((rawParallel s t).1.drop 2 ++ (rawParallel s t).1.take 2) from rfl,
    rotate_at _ (rawParallel_degs_len _ _), rawParallel_degree_at]

private theorem mirror_label_eq (s t : Signature) (i j : Fin 4)
    (h : (rawParallel s t).2[i.val]! = (rawParallel s t).2[j.val]!) :
    (swapSides (rawParallel s t)).2[(i+2 : Fin 4).val]! =
      (swapSides (rawParallel s t)).2[(j+2 : Fin 4).val]! := by
  let src := (rawParallel s t).2
  let dst := src.drop 2 ++ src.take 2
  have hsrc : src.length = 4 := rawParallel_labs_len _ _
  have hdst : dst.length = 4 := by simp [dst, hsrc]
  change (normalized ((rawParallel s t).1.drop 2 ++ (rawParallel s t).1.take 2, dst)).2[
    (i+2 : Fin 4).val]! = _
  apply (normalized_eq_iff _ dst
    ⟨(i+2 : Fin 4).val,by rw [hdst]; exact Fin.isLt _⟩
    ⟨(j+2 : Fin 4).val,by rw [hdst]; exact Fin.isLt _⟩).mpr
  rw [rotate_at _ hsrc,rotate_at _ hsrc]
  exact h

private theorem grouped_tag_eq (states : Fin 10 → Signature) (p : Fin 10) (i j : Fin 4)
    (h : (states p).2[i.val]! = (states p).2[j.val]!) :
    (blocksFrom states)[(pieceBlock p).val]!.2[(withinBlock p i).val]! =
      (blocksFrom states)[(pieceBlock p).val]!.2[(withinBlock p j).val]! := by
  fin_cases p
  · exact rawParallel_left _ _ i j h
  · exact rawParallel_right _ _ i j h
  · exact mirror_label_eq _ _ i j (rawParallel_left _ _ i j h)
  · exact mirror_label_eq _ _ i j (rawParallel_right _ _ i j h)
  · exact h
  · exact rawParallel_left _ _ i j h
  · exact rawParallel_right _ _ i j h
  · exact mirror_label_eq _ _ i j (rawParallel_left _ _ i j h)
  · exact mirror_label_eq _ _ i j (rawParallel_right _ _ i j h)
  · exact h

private theorem lineBounds (blocks : List Signature) (rungs : List Bool) (e : Edge)
    (he : e ∈ lineEdges blocks rungs) : e.1 < 14 ∧ e.2 < 14 := by
  rcases List.mem_append.mp he with he | he
  · obtain ⟨p,hp,hm⟩ := List.mem_flatMap.mp he
    have hp' : p < 6 := List.mem_range.mp hp
    obtain ⟨i,j,hi,hj,_,_,ha,hb⟩ := (mem_sameLabelEdges_iff (2*p) (blocks[p]!.2) e.1 e.2).mp hm
    omega
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
    have hi' := List.mem_range.mp (List.mem_filter.mp hi).1
    simp only
    omega

private theorem lineTags_block_eq (blocks : List Signature) (rungs : List Bool)
    (p : Fin 6) (i j : Fin 4) (h : blocks[p.val]!.2[i.val]! = blocks[p.val]!.2[j.val]!) :
    (lineTags blocks rungs)[2*p.val+i.val]! = (lineTags blocks rungs)[2*p.val+j.val]! := by
  have step (u v : Fin 4) (hlt : u.val < v.val)
      (eq : blocks[p.val]!.2[u.val]! = blocks[p.val]!.2[v.val]!) :
      (lineTags blocks rungs)[2*p.val+u.val]! = (lineTags blocks rungs)[2*p.val+v.val]! := by
    have hEdge : (2*p.val+u.val,2*p.val+v.val) ∈ sameLabelEdges (2*p.val) (blocks[p.val]!.2) :=
      (mem_sameLabelEdges_iff _ _ _ _).mpr ⟨u.val,v.val,u.isLt,v.isLt,hlt,eq,rfl,rfl⟩
    apply labels_eq_of_mem 14 _ (lineBounds blocks rungs) (2*p.val+u.val,2*p.val+v.val)
    apply List.mem_append.mpr
    exact Or.inl (List.mem_flatMap.mpr ⟨p.val,List.mem_range.mpr p.isLt,hEdge⟩)
  rcases lt_trichotomy i.val j.val with hlt | heq | hlt
  · exact step _ _ hlt h
  · rw [heq]
  · exact (step _ _ hlt h.symm).symm

@[simp] theorem lineTags_size (blocks : List Signature) (rungs : List Bool) :
    (lineTags blocks rungs).size = 14 := by simp [lineTags]

theorem lineTags_piece_eq (states : Fin 10 → Signature) (rungs : List Bool)
    (p : Fin 10) (i j : Fin 4) (h : (states p).2[i.val]! = (states p).2[j.val]!) :
    (lineTags (blocksFrom states) rungs)[(portSlot p i).val]! =
      (lineTags (blocksFrom states) rungs)[(portSlot p j).val]! := by
  rw [slot_value p i,slot_value p j]
  exact lineTags_block_eq _ _ (pieceBlock p) _ _ (grouped_tag_eq states p i j h)

theorem lineTags_rung_eq (blocks : List Signature) (rungs : List Bool) (i : Fin 5)
    (h : rungs[i.val]! = true) :
    (lineTags blocks rungs)[(rungLeft i).val]! = (lineTags blocks rungs)[(rungRight i).val]! := by
  have h₁ : (rungLeft i).val = 2*i.val+2 := by simp [rungLeft]; omega
  have h₂ : (rungRight i).val = 2*i.val+3 := by simp [rungRight]; omega
  rw [h₁,h₂]
  apply labels_eq_of_mem 14 _ (lineBounds blocks rungs) (2*i.val+2,2*i.val+3)
  apply List.mem_append.mpr
  right
  exact List.mem_map.mpr ⟨i.val,List.mem_filter.mpr ⟨List.mem_range.mpr i.isLt,h⟩,rfl⟩

end PrismCounterexample.Gadget

namespace PrismCounterexample

open SimpleGraph


private abbrev TrimPoint := PairVertex × Fin 2

def extremeRung (v w : TrimPoint) : Prop :=
  v.1 = w.1 ∧ (v.1 = 0 ∨ v.1 = 76)

theorem extremeRung_symm {v w : TrimPoint} : extremeRung v w → extremeRung w v := by
  rintro ⟨h, hw⟩
  exact ⟨h.symm, h ▸ hw⟩

def trimOuterRungs (A : SimpleGraph TrimPoint) : SimpleGraph TrimPoint where
  Adj v w := A.Adj v w ∧ ¬ extremeRung v w
  symm := ⟨fun _ _ h => ⟨h.1.symm, fun bad => h.2 (extremeRung_symm bad)⟩⟩
  loopless := ⟨fun _ h => A.irrefl h.1⟩

instance (A : SimpleGraph TrimPoint) [DecidableRel A.Adj] :
    DecidableRel (trimOuterRungs A).Adj := fun v w =>
  inferInstanceAs (Decidable (A.Adj v w ∧ ¬ (v.1 = w.1 ∧ (v.1 = 0 ∨ v.1 = 76))))

theorem trimOuterRungs_le (A : SimpleGraph TrimPoint) : trimOuterRungs A ≤ A :=
  fun _ _ h => h.1

set_option maxRecDepth 60000 in
theorem trimOuterRungs_degree_le (A : SimpleGraph TrimPoint) [DecidableRel A.Adj] (v : TrimPoint) :
    (trimOuterRungs A).degree v ≤ A.degree v := by
  exact Finset.card_le_card (fun w h => (A.mem_neighborFinset v w).mpr
    (((trimOuterRungs A).mem_neighborFinset v w).mp h).1)

set_option maxRecDepth 60000 in
theorem trimOuterRungs_degree_of_interior (A : SimpleGraph TrimPoint) [DecidableRel A.Adj]
    (v : TrimPoint) (h0 : v.1 ≠ 0) (h76 : v.1 ≠ 76) :
    (trimOuterRungs A).degree v = A.degree v := by
  have neighbors : (trimOuterRungs A).neighborFinset v = A.neighborFinset v := by
    ext w
    rw [SimpleGraph.mem_neighborFinset, SimpleGraph.mem_neighborFinset]
    exact ⟨And.left, fun h => ⟨h, fun hr => hr.2.elim h0 h76⟩⟩
  exact congrArg Finset.card neighbors

set_option maxRecDepth 60000 in
theorem trimOuterRungs_not_closed_full
    (A : SimpleGraph TrimPoint) [DecidableRel A.Adj]
    (degree : ∀ v, A.degree v ≤ 2)
    (base : ∀ S : Finset TrimPoint, S.Nonempty →
      (∀ v ∈ S, ∀ w, A.Adj v w → w ∈ S) → ∃ v ∈ S, A.degree v < 2)
    (S : Finset TrimPoint) (hn : S.Nonempty)
    (closed : ∀ v ∈ S, ∀ w, (trimOuterRungs A).Adj v w → w ∈ S) :
    ∃ v ∈ S, (trimOuterRungs A).degree v < 2 := by
  by_contra! h
  have forced (v : TrimPoint) (hv : v ∈ S) :
      (trimOuterRungs A).neighborFinset v = A.neighborFinset v := by
    apply Finset.eq_of_subset_of_card_le
    · exact fun w h => (A.mem_neighborFinset v w).mpr (((trimOuterRungs A).mem_neighborFinset v w).mp h).1
    · exact (degree v).trans (h v hv)
  have closedA : ∀ v ∈ S, ∀ w, A.Adj v w → w ∈ S := by
    intro v hv w h
    have mem : w ∈ (trimOuterRungs A).neighborFinset v := forced v hv ▸ (A.mem_neighborFinset v w).mpr h
    exact closed v hv w (((trimOuterRungs A).mem_neighborFinset v w).mp mem)
  obtain ⟨v, hv, hdeg⟩ := base S hn closedA
  exact (Nat.not_lt_of_ge ((h v hv).trans (trimOuterRungs_degree_le A v))) hdeg

end PrismCounterexample

namespace PrismCounterexample

open SimpleGraph Gadget

def internalJoint (i : Fin 5) : Fin 7 := ⟨i.val + 1, by omega⟩

def actualRung (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (i : Fin 5) : Bool :=
  jointRungSelected A (internalJoint i)

def rungList (A : SimpleGraph PairPoint) [DecidableRel A.Adj] : List Bool :=
  [actualRung A 0,actualRung A 1,actualRung A 2,actualRung A 3,actualRung A 4]

theorem rungList_value (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (i : Fin 5) :
    (rungList A)[i.val]! = actualRung A i := by
  fin_cases i <;> rfl

theorem rungSite_left (i : Fin 5) :
    physicalSite (rungLeft i) = jointVertex (internalJoint i) 0 := by
  fin_cases i <;> rfl

theorem rungSite_right (i : Fin 5) :
    physicalSite (rungRight i) = jointVertex (internalJoint i) 1 := by
  fin_cases i <;> rfl

theorem internal_rung_pos (p : PairVertex) (h : p ∈ jointPositions) :
    p = 0 ∨ p = 76 ∨ ∃ i : Fin 5, (jointVertex (internalJoint i) 0).1 = p := by
  have table : ∀ p : PairVertex, p ∈ jointPositions →
    p = 0 ∨ p = 76 ∨ ∃ i : Fin 5, (jointVertex (internalJoint i) 0).1 = p := by decide +kernel
  exact table p h

theorem two_port_degrees_le (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism) {p q : Piece} (hne : p ≠ q)
    {v : PiecePoint p} {w : PiecePoint q} (h : pieceEmbed p v = pieceEmbed q w) :
    Gadget.deg (rawSelected A p) v.val + Gadget.deg (rawSelected A q) w.val ≤
      A.degree (pieceEmbed p v) := by
  rw [← contribution_at A p v, ← contribution_at A q w, ← h,
    degree_decompose A sub exactEdges exact_cover exact_unique exact_ordered, finRange_sum]
  apply le_trans ?_ (Nat.le_add_right _ _)
  let f (r : Piece) := degreeContribution A exactEdges r (pieceEmbed p v)
  have sum := Finset.sum_le_sum_of_subset (f := f) (Finset.subset_univ ({p,q} : Finset Piece))
  rw [Finset.sum_pair hne] at sum
  exact sum

end PrismCounterexample

namespace PrismCounterexample.Gadget

/-- Six bits per vertex store a small label and leave one guard bit. -/
def packedRead (code i : ℕ) : ℕ := (code >>> (6*i)) &&& 31

def repeatedBits (n : ℕ) : ℕ := ((1 : ℕ) <<< (6*n)) / 63

def packedMerge (lanes code : ℕ) (e : Edge) : ℕ :=
  let a := packedRead code e.1
  let b := packedRead code e.2
  let highBits := lanes <<< 5
  let difference := code ^^^ (lanes * b)
  let nonMatches := ((difference ||| highBits) - lanes) &&& highBits
  let matchingLanes := (highBits ^^^ nonMatches) >>> 5
  code ^^^ (matchingLanes * (a ^^^ b))

def packedLabels (n : ℕ) (es : List Edge) : ℕ :=
  let init := (List.range n).foldl (fun acc i => acc + (i <<< (6*i))) 0
  es.foldl (packedMerge (repeatedBits n)) init

def packedStatus (n : ℕ) (es : List Edge) : Signature × Bool :=
  let code := packedLabels n es
  let read := packedRead code
  let d := (ports n).map (deg es)
  let tagList := (ports n).map read
  let free := ((ports n).filter fun p => deg es p < 2).map read
  ((d,tagList), (List.range n).all fun i => free.contains (read i))

def packedStateTest (n : ℕ) (table : List Signature) (es : List Edge) : Bool :=
  let code := packedLabels n es
  let value := packedStatus n es
  (es.all fun e => packedRead code e.1 == packedRead code e.2) &&
    (!value.2 || table.contains (normalized value.1))

theorem packed_labels_eq_of_mem {n : ℕ} {table : List Signature} {es : List Edge}
    (hcheck : packedStateTest n table es = true) (e : Edge) (he : e ∈ es) :
    packedRead (packedLabels n es) e.1 = packedRead (packedLabels n es) e.2 := by
  unfold packedStateTest at hcheck
  exact eq_of_beq (List.all_eq_true.mp (Bool.and_eq_true_iff.mp hcheck).1 e he)

theorem packed_status_good {n : ℕ} {es : List Edge}
    (h : ∀ v, v < n → ∃ p ∈ ports n, deg es p < 2 ∧
      packedRead (packedLabels n es) v = packedRead (packedLabels n es) p) :
    (packedStatus n es).2 = true := by
  simp only [packedStatus, List.all_eq_true]
  intro v hv
  obtain ⟨p, hp, hdegree, hsame⟩ := h v (List.mem_range.mp hv)
  apply List.contains_iff_mem.mpr
  exact List.mem_map.mpr ⟨p, List.mem_filter.mpr ⟨hp, by simpa using hdegree⟩, hsame.symm⟩

theorem packed_state_mem {n : ℕ} {table : List Signature} {es : List Edge}
    (hcheck : packedStateTest n table es = true) (hgood : (packedStatus n es).2 = true) :
    normalized (packedStatus n es).1 ∈ table := by
  unfold packedStateTest at hcheck
  simpa [hgood, List.contains_iff_mem] using (Bool.and_eq_true_iff.mp hcheck).2

end PrismCounterexample.Gadget

namespace PrismCounterexample

open SimpleGraph Gadget

abbrev PackedSideCertificate : Prop :=
  check sideEdges (isPort 20) (packedStateTest 20 sideStates) 0 [] 20 = true

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem packed_cycle_certificate :
    check cycleEdges (isPort 10) (packedStateTest 10 cycleStates) 0 [] 10 = true := by
  decide +kernel

/-- An independently checked small integer label assigned to each local vertex. -/
def packedLocalColor (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (p : Piece) (v : PiecePoint p) : ℕ :=
  packedRead (packedLabels (pieceSize p) (rawSelected A p)) v.val

theorem packedLocal_check (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (p : Piece) (degree : ∀ v, (rawPieceGraph A p).degree v ≤ 2)
    (interior : ∀ v, ¬ pieceIsPort p v → (rawPieceGraph A p).degree v = 2)
    (sideCert : PackedSideCertificate) :
    packedStateTest (pieceSize p) (letterTable p) (rawSelected A p) = true := by
  have degrees (v : ℕ) (hv : v < pieceSize p) :
      degreeOK (isPort (pieceSize p)) v (rawSelected A p) = true := by
    let w : PiecePoint p := ⟨v,hv⟩
    have bound := degree w
    rw [rawPieceGraph_degree] at bound
    by_cases h : pieceIsPort p w
    · have yes : isPort (pieceSize p) v = true := (gadgetPort_pred p w).mpr h
      rw [degreeOK, if_pos yes]
      exact decide_eq_true bound
    · have no : isPort (pieceSize p) v = false := Bool.eq_false_iff.mpr
        (fun yes => h ((gadgetPort_pred p w).mp yes))
      have exactDegree := interior w h
      rw [rawPieceGraph_degree] at exactDegree
      simpa only [degreeOK, no, Bool.false_eq_true, if_false, decide_eq_true_eq] using exactDegree
  have cert : check (exactEdges p) (isPort (pieceSize p))
      (packedStateTest (pieceSize p) (letterTable p)) 0 [] (pieceSize p) = true := by
    by_cases hp : p.val % 5 = 4
    · simpa only [letterTable, pieceSize, exactEdges, if_pos hp] using packed_cycle_certificate
    · simpa only [letterTable, pieceSize, exactEdges, if_neg hp] using sideCert
  exact exhaustive (exactEdges p) (fun e mem => (raw_bounds p e mem).1)
    (isPort (pieceSize p)) (packedStateTest (pieceSize p) (letterTable p))
    (pieceSize p) (pickRaw A p) cert degrees

theorem packedLocal_edge (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (p : Piece)
    (cert : packedStateTest (pieceSize p) (letterTable p) (rawSelected A p) = true)
    {u v : PiecePoint p} (h : (rawPieceGraph A p).Adj u v) :
    packedLocalColor A p u = packedLocalColor A p v := by
  have carry {a b : PiecePoint p} (he : (a,b) ∈ (rawSelected A p).map (pointPair p)) :
      packedLocalColor A p a = packedLocalColor A p b := by
    obtain ⟨r, hr, heq⟩ := List.mem_map.mp he
    have rb := raw_bounds p r ((rawSelected_mem A p r).mp hr).1
    have hl := packed_labels_eq_of_mem cert r hr
    change (rawPiecePoint p r.1, rawPiecePoint p r.2) = (a,b) at heq
    simp only [Prod.mk.injEq] at heq
    rw [← heq.1, ← heq.2]
    simpa only [packedLocalColor, rawPoint_val p (rb.1.trans rb.2), rawPoint_val p rb.2] using hl
  rcases h.2 with h | h
  · exact carry h
  · exact (carry h).symm

theorem packedLocal_open (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism) (degree : ∀ v, A.degree v ≤ 2)
    (full : ∀ v, v.1 ≠ 0 → v.1 ≠ 76 → A.degree v = 2)
    (closed : ∀ S : Finset PairPoint, S.Nonempty →
       (∀ u ∈ S, ∀ v, A.Adj u v → v ∈ S) → ∃ v ∈ S, A.degree v < 2)
    (p : Piece) (cert : packedStateTest (pieceSize p) (letterTable p) (rawSelected A p) = true)
    (v : PiecePoint p) :
    ∃ q : Fin 4, packedLocalColor A p v = packedLocalColor A p (piecePort p q) ∧
      deg (rawSelected A p) (piecePort p q).val < 2 := by
  obtain ⟨w, hw, color, deg⟩ := color_has_open_port_of_no_full_closed A (pieceEmbed p)
    (rawPieceGraph A p) (rawPieceGraph_le A p) degree closed (physicalPorts p)
    (fun w hw => local_full_degree A sub full p w (fun h => hw ((physicalPorts_spec p w).mpr h)))
    (packedLocalColor A p) (by intro u v h; exact packedLocal_edge A p cert h) v
  obtain ⟨q, rfl⟩ := piecePort_exists p w ((physicalPorts_spec p w).mp hw)
  rw [rawPieceGraph_degree] at deg
  exact ⟨q, color.symm, deg⟩

def packedActualSignature (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (p : Piece) :
    Signature := normalized (packedStatus (pieceSize p) (rawSelected A p)).1

theorem packedActual_degree (A : SimpleGraph PairPoint) [DecidableRel A.Adj] (p : Piece) :
    (packedActualSignature A p).1 = (actualSignature A p).1 := rfl

theorem packedActual_tag_eq (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (p : Piece) (i j : Fin 4)
    (h : packedLocalColor A p (piecePort p i) = packedLocalColor A p (piecePort p j)) :
    (packedActualSignature A p).2[i.val]! = (packedActualSignature A p).2[j.val]! := by
  let code := packedLabels (pieceSize p) (rawSelected A p)
  let tagList := (ports (pieceSize p)).map (packedRead code)
  have hi : i.val < tagList.length := by simp [tagList, ports]
  have hj : j.val < tagList.length := by simp [tagList, ports]
  change (normalized ((packedStatus (pieceSize p) (rawSelected A p)).1.1,tagList)).2[i.val]! = _
  apply (normalized_eq_iff _ tagList ⟨i.val,hi⟩ ⟨j.val,hj⟩).mpr
  have hit : i.val < (ports (pieceSize p)).length := by simp [ports]
  have hjt : j.val < (ports (pieceSize p)).length := by simp [ports]
  change tagList[i.val]! = tagList[j.val]!
  rw [getElem!_pos tagList i.val hi, getElem!_pos tagList j.val hj]
  simp only [tagList,List.getElem_map]
  rw [← getElem!_pos (ports (pieceSize p)) i.val hit,
    ← getElem!_pos (ports (pieceSize p)) j.val hjt, gadgetPort_index, gadgetPort_index]
  exact h

theorem packedActual_mem (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism) (degree : ∀ v, A.degree v ≤ 2)
    (full : ∀ v, v.1 ≠ 0 → v.1 ≠ 76 → A.degree v = 2)
    (closed : ∀ S : Finset PairPoint, S.Nonempty →
       (∀ u ∈ S, ∀ v, A.Adj u v → v ∈ S) → ∃ v ∈ S, A.degree v < 2)
    (p : Piece) (cert : packedStateTest (pieceSize p) (letterTable p) (rawSelected A p) = true) :
    packedActualSignature A p ∈ letterTable p := by
  apply packed_state_mem cert
  apply packed_status_good
  intro i hi
  obtain ⟨q,hcolor,hdeg⟩ := packedLocal_open A sub degree full closed p cert ⟨i,hi⟩
  refine ⟨(piecePort p q).val, ?_, hdeg, hcolor⟩
  rw [← physicalPort_values]
  exact List.mem_map.mpr ⟨q,by simp,rfl⟩

end PrismCounterexample

namespace PrismCounterexample

open SimpleGraph Gadget

theorem packed_trimmed_edge_sources (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism)
    (cert : ∀ p : Piece, packedStateTest (pieceSize p) (letterTable p) (rawSelected A p) = true)
    (noOuter : ∀ u v, A.Adj u v → ¬ extremeRung u v) (u v : PairPoint) (h : A.Adj u v) :
      (∃ (p : Piece) (a b : PiecePoint p), pieceEmbed p a = u ∧ pieceEmbed p b = v ∧
        packedLocalColor A p a = packedLocalColor A p b) ∨
      (∃ i, actualRung A i = true ∧
        ((physicalSite (rungLeft i) = u ∧ physicalSite (rungRight i) = v) ∨
        (physicalSite (rungRight i) = u ∧ physicalSite (rungLeft i) = v))) := by
  rcases chosen_edge_source A sub h with ⟨p,a,b,ha,hb,he⟩ | ⟨w,hw,hends⟩
  · exact Or.inl ⟨p, a, b, ha, hb, packedLocal_edge A p (cert p) he⟩
  · rcases internal_rung_pos w hw with rfl | rfl | ⟨i,hi⟩
    · rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
        exact (noOuter _ _ h ⟨rfl, Or.inl rfl⟩).elim
    · rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;>
        exact (noOuter _ _ h ⟨rfl, Or.inr rfl⟩).elim
    · have h0 : physicalSite (rungLeft i) = (w,0) := by
        rw [rungSite_left]
        exact Prod.ext hi rfl
      have h1 : physicalSite (rungRight i) = (w,1) := by
        rw [rungSite_right]
        exact Prod.ext hi rfl
      have hselected : A.Adj (w,0) (w,1) := by
        rcases hends with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
        · exact h
        · exact h.symm
      have hr : actualRung A i = true := by
        apply (jointRungSelected_eq_true A (internalJoint i)).mpr
        rw [← rungSite_left, ← rungSite_right, h0, h1]
        exact hselected
      exact Or.inr ⟨i, hr, hends.imp (fun h => ⟨h0.trans h.1.symm,h1.trans h.2.symm⟩)
        (fun h => ⟨h1.trans h.1.symm,h0.trans h.2.symm⟩)⟩

theorem packed_projected_some (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism) (bound : ∀ v, A.degree v ≤ 2)
    (full : ∀ v, v.1 ≠ 0 → v.1 ≠ 76 → A.degree v = 2)
    (closed : ∀ S : Finset PairPoint, S.Nonempty →
      (∀ u ∈ S, ∀ v, A.Adj u v → v ∈ S) → ∃ v ∈ S, A.degree v < 2)
    (noOuter : ∀ u v, A.Adj u v → ¬ extremeRung u v)
    (dSpec : ∀ i : Fin 4, A.degree (physicalSite (outerPort i)) =
      (outerDegrees (blocksFrom (packedActualSignature A)))[i.val]!)
    (cert : ∀ p : Piece, packedStateTest (pieceSize p) (letterTable p) (rawSelected A p) = true) :
    (Gadget.projected (outerDegrees (blocksFrom (packedActualSignature A)))
      (lineTags (blocksFrom (packedActualSignature A)) (rungList A)) outerSlots).isSome = true := by
  have h := projectedPhysical_some A bound closed
    (lineTags (blocksFrom (packedActualSignature A)) (rungList A)) (lineTags_size _ _)
    (packedLocalColor A)
    (fun p v => by
      obtain ⟨q, eq, _⟩ := packedLocal_open A sub bound full closed p (cert p) v
      exact ⟨q, eq⟩)
    (fun p i j eq => lineTags_piece_eq _ _ p i j (packedActual_tag_eq A p i j eq))
    (actualRung A)
    (fun i hr => lineTags_rung_eq _ _ i ((rungList_value A i).trans hr))
    (packed_trimmed_edge_sources A sub cert noOuter)
    (outerDegrees (blocksFrom (packedActualSignature A))) rfl
    dSpec full
  rw [h]
  rfl

end PrismCounterexample

namespace PrismCounterexample

open SimpleGraph Gadget

@[local simp] private theorem parallel_degree_list (s t : Signature) :
    (rawParallel s t).1 =
      [s.1[0]! + t.1[0]!, s.1[1]! + t.1[1]!, s.1[2]! + t.1[2]!, s.1[3]! + t.1[3]!] := rfl

@[local simp] private theorem mirrored_degree_list (s t : Signature) :
    (swapSides (rawParallel s t)).1 =
      [s.1[2]! + t.1[2]!, s.1[3]! + t.1[3]!, s.1[0]! + t.1[0]!, s.1[1]! + t.1[1]!] := rfl

private theorem sig_at0 (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (states : Piece → Signature)
    (degrees : ∀ (p : Piece) (q : Fin 4),
      (states p).1[q.val]! = Gadget.deg (rawSelected A p) (piecePort p q).val) (p : Piece) :
    (states p).1[0]?.getD 0 = Gadget.deg (rawSelected A p) 0 := by
  simpa [piecePort] using degrees p 0

private theorem sig_at1 (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (states : Piece → Signature)
    (degrees : ∀ (p : Piece) (q : Fin 4),
      (states p).1[q.val]! = Gadget.deg (rawSelected A p) (piecePort p q).val) (p : Piece) :
    (states p).1[1]?.getD 0 = Gadget.deg (rawSelected A p) 1 := by
  simpa [piecePort] using degrees p 1

private theorem size_at_least_ten (p : Piece) : 10 ≤ pieceSize p := by
  unfold pieceSize
  split <;> decide

private theorem sig_at2 (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (states : Piece → Signature)
    (degrees : ∀ (p : Piece) (q : Fin 4),
      (states p).1[q.val]! = Gadget.deg (rawSelected A p) (piecePort p q).val) (p : Piece) :
    (states p).1[2]?.getD 0 = Gadget.deg (rawSelected A p) (pieceSize p - 2) := by
  have h : (piecePort p 2).val = pieceSize p - 2 := by
    change (if 2 < (2 : ℕ) then 2 else pieceSize p - 4 + 2) = _
    have := size_at_least_ten p
    norm_num
    omega
  simpa [h] using degrees p 2

private theorem sig_at3 (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (states : Piece → Signature)
    (degrees : ∀ (p : Piece) (q : Fin 4),
      (states p).1[q.val]! = Gadget.deg (rawSelected A p) (piecePort p q).val) (p : Piece) :
    (states p).1[3]?.getD 0 = Gadget.deg (rawSelected A p) (pieceSize p - 1) := by
  have h : (piecePort p 3).val = pieceSize p - 1 := by
    change (if 3 < (2 : ℕ) then 3 else pieceSize p - 4 + 3) = _
    have := size_at_least_ten p
    norm_num
    omega
  simpa [h] using degrees p 3

private theorem incoming_joint_degree (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism) (states : Piece → Signature)
    (degrees : ∀ (p : Piece) (q : Fin 4),
      (states p).1[q.val]! = Gadget.deg (rawSelected A p) (piecePort p q).val) (i : Fin 5) (l : Fin 2) :
    A.degree (jointVertex ⟨i.val+1, by omega⟩ l) =
      ((blocksFrom states)[i.val]!).1[2 + l.val]! +
      ((blocksFrom states)[i.val+1]!).1[l.val]! +
      (jointRungSelected A ⟨i.val+1, by omega⟩).toNat := by
  fin_cases i <;> fin_cases l
  · simpa [blocksFrom, pieceSize, Nat.add_assoc, sig_at2 A states degrees] using degree_joint1 A sub 0
  · simpa [blocksFrom, pieceSize, Nat.add_assoc, sig_at3 A states degrees] using degree_joint1 A sub 1
  · simpa [blocksFrom, Nat.add_assoc, sig_at0 A states degrees] using degree_joint2 A sub 0
  · simpa [blocksFrom, Nat.add_assoc, sig_at1 A states degrees] using degree_joint2 A sub 1
  · simpa [blocksFrom, pieceSize, Nat.add_assoc, sig_at2 A states degrees, sig_at0 A states degrees] using degree_joint3 A sub 0
  · simpa [blocksFrom, pieceSize, Nat.add_assoc, sig_at3 A states degrees, sig_at1 A states degrees] using degree_joint3 A sub 1
  · simpa [blocksFrom, pieceSize, Nat.add_assoc, sig_at2 A states degrees] using degree_joint4 A sub 0
  · simpa [blocksFrom, pieceSize, Nat.add_assoc, sig_at3 A states degrees] using degree_joint4 A sub 1
  · simpa [blocksFrom, Nat.add_assoc, sig_at0 A states degrees] using degree_joint5 A sub 0
  · simpa [blocksFrom, Nat.add_assoc, sig_at1 A states degrees] using degree_joint5 A sub 1

private theorem joint_inner (i : Fin 5) (l : Fin 2) :
    (jointVertex ⟨i.val+1, by omega⟩ l).1 ≠ 0 ∧
      (jointVertex ⟨i.val+1, by omega⟩ l).1 ≠ 76 := by
  fin_cases i <;> fin_cases l <;> decide

private theorem bool_to_rung (r : Bool) : r.toNat = if r then 1 else 0 := by
  cases r <;> rfl

theorem jointOK_for (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism)
    (full : ∀ v : PairPoint, v.1 ≠ 0 → v.1 ≠ 76 → A.degree v = 2)
    (states : Piece → Signature)
    (degrees : ∀ (p : Piece) (q : Fin 4),
      (states p).1[q.val]! = Gadget.deg (rawSelected A p) (piecePort p q).val) (i : Fin 5) :
    jointOK (blocksFrom states)[i.val]!
      (blocksFrom states)[i.val + 1]!
      (jointRungSelected A ⟨i.val+1, by omega⟩) = true := by
  unfold jointOK
  apply decide_eq_true
  have d (l : Fin 2) :
      A.degree (jointVertex ⟨i.val+1, by omega⟩ l) = 2 :=
    full _ (joint_inner i l).1 (joint_inner i l).2
  constructor
  · have h := incoming_joint_degree A sub states degrees i 0
    rw [d 0, bool_to_rung] at h
    exact h.symm
  · have h := incoming_joint_degree A sub states degrees i 1
    rw [d 1, bool_to_rung] at h
    exact h.symm

theorem outer_degrees_for (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism) (states : Piece → Signature)
    (degrees : ∀ (p : Piece) (q : Fin 4),
      (states p).1[q.val]! = Gadget.deg (rawSelected A p) (piecePort p q).val)
    (noRung0 : ¬ A.Adj (jointVertex 0 0) (jointVertex 0 1))
    (noRung6 : ¬ A.Adj (jointVertex 6 0) (jointVertex 6 1))
    (i : Fin 4) :
    A.degree (physicalSite (outerPort i)) =
      (outerDegrees (blocksFrom states))[i.val]! := by
  have off0 : jointRungSelected A 0 = false := by simp [jointRungSelected, noRung0]
  have off6 : jointRungSelected A 6 = false := by simp [jointRungSelected, noRung6]
  fin_cases i
  · change A.degree (jointVertex 0 0) = _
    simpa [outerDegrees, blocksFrom, off0, sig_at0 A states degrees] using degree_joint0 A sub 0
  · change A.degree (jointVertex 0 1) = _
    simpa [outerDegrees, blocksFrom, off0, sig_at1 A states degrees] using degree_joint0 A sub 1
  · change A.degree (jointVertex 6 0) = _
    simpa [outerDegrees, blocksFrom, pieceSize, off6, sig_at2 A states degrees] using degree_joint6 A sub 0
  · change A.degree (jointVertex 6 1) = _
    simpa [outerDegrees, blocksFrom, pieceSize, off6, sig_at3 A states degrees] using degree_joint6 A sub 1

end PrismCounterexample

namespace PrismCounterexample

open SimpleGraph Gadget

def ParallelCertificate : Prop :=
  ∀ {s t : Signature}, s ∈ sideStates → t ∈ sideStates →
    (rawParallelDegrees s t).all (· ≤ 2) = true → rawParallel s t ∈ rawStates

def LineCertificate : Prop :=
  ∀ {j₁ l₁ r₁ j₂ l₂ r₂ : Signature} {a b c d e : Bool},
    j₁ ∈ rawStates → l₁ ∈ mirroredRawStates → r₁ ∈ cycleStates →
    j₂ ∈ rawStates → l₂ ∈ mirroredRawStates → r₂ ∈ cycleStates →
    jointOK j₁ l₁ a = true → jointOK l₁ r₁ b = true →
    jointOK r₁ j₂ c = true → jointOK j₂ l₂ d = true → jointOK l₂ r₂ e = true →
    Gadget.projected (outerDegrees [j₁,l₁,r₁,j₂,l₂,r₂])
      (lineTags [j₁,l₁,r₁,j₂,l₂,r₂] [a,b,c,d,e]) outerSlots = none

theorem parallel_degree_bound_for (A : SimpleGraph PairPoint) [DecidableRel A.Adj]
    (sub : A ≤ pairPrism) (bound : ∀ v, A.degree v ≤ 2) (states : Piece → Signature)
    (degrees : ∀ p (q : Fin 4),
      (states p).1[q.val]! = Gadget.deg (rawSelected A p) (piecePort p q).val)
    {p q : Piece} (hne : p ≠ q)
    (same : ∀ i : Fin 4, pieceEmbed p (piecePort p i) = pieceEmbed q (piecePort q i)) :
    (rawParallelDegrees (states p) (states q)).all (· ≤ 2) = true := by
  apply List.all_eq_true.mpr
  intro m hm
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
  let slot : Fin 4 := ⟨i, List.mem_range.mp hi⟩
  change decide ((states p).1[slot.val]! + (states q).1[slot.val]! ≤ 2) = true
  rw [degrees p slot, degrees q slot]
  exact decide_eq_true ((two_port_degrees_le A sub hne (same slot)).trans (bound _))

set_option maxRecDepth 3000 in
private theorem finite_profiles_rejected
    (parallelMem : ParallelCertificate) (reject : LineCertificate)
    (states : Piece → Signature) (rung : Fin 5 → Bool)
    (mem : ∀ p, states p ∈ letterTable p)
    (port01 : (rawParallelDegrees (states 0) (states 1)).all (· ≤ 2) = true)
    (port23 : (rawParallelDegrees (states 2) (states 3)).all (· ≤ 2) = true)
    (port56 : (rawParallelDegrees (states 5) (states 6)).all (· ≤ 2) = true)
    (port78 : (rawParallelDegrees (states 7) (states 8)).all (· ≤ 2) = true)
    (inner : ∀ j : Fin 5, jointOK (blocksFrom states)[j.val]!
      (blocksFrom states)[j.val+1]! (rung j) = true) :
    Gadget.projected (outerDegrees (blocksFrom states))
      (lineTags (blocksFrom states) [rung 0,rung 1,rung 2,rung 3,rung 4]) outerSlots = none := by
  have j₁ : rawParallel (states 0) (states 1) ∈ rawStates :=
    parallelMem (mem 0) (mem 1) port01
  have l₁ : swapSides (rawParallel (states 2) (states 3)) ∈ mirroredRawStates :=
    List.mem_map.mpr ⟨_, parallelMem (mem 2) (mem 3) port23, rfl⟩
  have r₁ : states 4 ∈ cycleStates := mem 4
  have j₂ : rawParallel (states 5) (states 6) ∈ rawStates :=
    parallelMem (mem 5) (mem 6) port56
  have l₂ : swapSides (rawParallel (states 7) (states 8)) ∈ mirroredRawStates :=
    List.mem_map.mpr ⟨_, parallelMem (mem 7) (mem 8) port78, rfl⟩
  have r₂ : states 9 ∈ cycleStates := mem 9
  exact reject j₁ l₁ r₁ j₂ l₂ r₂ (inner 0) (inner 1) (inner 2) (inner 3) (inner 4)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in

theorem local_obstruction_from_certificates
    (sideCert : PackedSideCertificate)
    (parallelMem : ParallelCertificate) (reject : LineCertificate) : localObstruction := by
  intro A _ sub degree full openA
  let B := trimOuterRungs A
  have subB : B ≤ pairPrism := (trimOuterRungs_le A).trans sub
  have degreeB (v : PairPoint) : B.degree v ≤ 2 :=
    (trimOuterRungs_degree_le A v).trans (degree v)
  have fullB (v : PairPoint) (h0 : v.1 ≠ 0) (h76 : v.1 ≠ 76) : B.degree v = 2 :=
    (trimOuterRungs_degree_of_interior A v h0 h76).trans (full v h0 h76)
  have openB : ∀ S : Finset PairPoint, S.Nonempty →
      (∀ u ∈ S, ∀ v, B.Adj u v → v ∈ S) → ∃ v ∈ S, B.degree v < 2 :=
    trimOuterRungs_not_closed_full A degree openA
  have noOuter (u v : PairPoint) (h : B.Adj u v) : ¬ extremeRung u v := h.2
  let states := packedActualSignature B
  have degs (p : Piece) (q : Fin 4) :
      (states p).1[q.val]! = Gadget.deg (rawSelected B p) (piecePort p q).val := by
    change (packedActualSignature B p).1[q.val]! = _
    rw [packedActual_degree B p]
    exact actualSig_degree B p q
  have cert (p : Piece) : packedStateTest (pieceSize p) (letterTable p) (rawSelected B p) = true :=
    packedLocal_check B p (local_degree_bound B degreeB p) (local_full_degree B subB fullB p) sideCert
  have mem (p : Piece) : states p ∈ letterTable p :=
    packedActual_mem B subB degreeB fullB openB p (cert p)
  have outerLeft : ¬ B.Adj (jointVertex 0 0) (jointVertex 0 1) :=
    fun chosen => noOuter _ _ chosen ⟨rfl, Or.inl rfl⟩
  have outerRight : ¬ B.Adj (jointVertex 6 0) (jointVertex 6 1) :=
    fun chosen => noOuter _ _ chosen ⟨rfl, Or.inr rfl⟩
  have innerEquations := jointOK_for B subB fullB states degs
  have outerEquations := outer_degrees_for B subB states degs
    outerLeft outerRight
  have yes := packed_projected_some B subB degreeB fullB openB noOuter outerEquations cert
  have h01 := parallel_degree_bound_for B subB degreeB states degs (p := 0) (q := 1)
    (by decide) (by intro i; fin_cases i <;> rfl)
  have h23 := parallel_degree_bound_for B subB degreeB states degs (p := 2) (q := 3)
    (by decide) (by intro i; fin_cases i <;> rfl)
  have h56 := parallel_degree_bound_for B subB degreeB states degs (p := 5) (q := 6)
    (by decide) (by intro i; fin_cases i <;> rfl)
  have h78 := parallel_degree_bound_for B subB degreeB states degs (p := 7) (q := 8)
    (by decide) (by intro i; fin_cases i <;> rfl)
  have no := finite_profiles_rejected parallelMem reject states (actualRung B) mem
    h01 h23 h56 h78 innerEquations
  exact Bool.false_ne_true ((congrArg Option.isSome no).symm.trans yes)

end PrismCounterexample

namespace PrismCounterexample.Gadget

/-- The same check with row choices materialized once as finite data. -/
def checkRows (choices : ℕ → List (List Edge)) (port : ℕ → Bool) (test : List Edge → Bool)
    (i : ℕ) (prior : List Edge) : ℕ → Bool
  | 0 => test prior
  | n + 1 =>
    (choices i).all fun selected =>
      let next := prior ++ selected
      if degreeOK port i next then checkRows choices port test (i+1) next n else true

theorem checkRows_eq (choices : ℕ → List (List Edge)) (allowed : List Edge)
    (port : ℕ → Bool) (test : List Edge → Bool) (n i : ℕ) (prior : List Edge)
    (hchoices : ∀ j, i ≤ j → j < i+n → choices j = (row allowed j).sublists) :
    checkRows choices port test i prior n = check allowed port test i prior n := by
  induction n generalizing i prior with
  | zero => rfl
  | succ n ih =>
    rw [checkRows, check, hchoices i le_rfl (by omega)]
    apply List.all_congr rfl
    intro selected
    dsimp only
    rw [ih (i+1) (prior ++ selected) (fun j hlo hhi => hchoices j (by omega) (by omega))]

private def sideRowCache : Array (List (List Edge)) := #[
  [[], [(0, 2)], [(0, 8)], [(0, 2), (0, 8)]],
  [[], [(1, 3)], [(1, 9)], [(1, 3), (1, 9)]],
  [[], [(2, 4)], [(2, 3)], [(2, 4), (2, 3)]],
  [[], [(3, 5)]],
  [[], [(4, 6)], [(4, 5)], [(4, 6), (4, 5)]],
  [[], [(5, 7)]],
  [[], [(6, 8)], [(6, 10)], [(6, 8), (6, 10)], [(6, 16)], [(6, 8), (6, 16)], [(6, 10), (6, 16)], [(6, 8), (6, 10), (6, 16)], [(6, 7)], [(6, 8), (6, 7)], [(6, 10), (6, 7)], [(6, 8), (6, 10), (6, 7)], [(6, 16), (6, 7)], [(6, 8), (6, 16), (6, 7)], [(6, 10), (6, 16), (6, 7)], [(6, 8), (6, 10), (6, 16), (6, 7)]],
  [[], [(7, 9)], [(7, 11)], [(7, 9), (7, 11)], [(7, 17)], [(7, 9), (7, 17)], [(7, 11), (7, 17)], [(7, 9), (7, 11), (7, 17)]],
  [[], [(8, 18)], [(8, 9)], [(8, 18), (8, 9)]],
  [[], [(9, 19)]],
  [[], [(10, 12)], [(10, 11)], [(10, 12), (10, 11)]],
  [[], [(11, 13)]],
  [[], [(12, 14)], [(12, 13)], [(12, 14), (12, 13)]],
  [[], [(13, 15)]],
  [[], [(14, 16)], [(14, 18)], [(14, 16), (14, 18)], [(14, 15)], [(14, 16), (14, 15)], [(14, 18), (14, 15)], [(14, 16), (14, 18), (14, 15)]],
  [[], [(15, 17)], [(15, 19)], [(15, 17), (15, 19)]],
  [[], [(16, 18)], [(16, 17)], [(16, 18), (16, 17)]],
  [[], [(17, 19)]],
  [[]],
  [[]]]

def sideChoices (i : ℕ) : List (List Edge) := sideRowCache[i]!

private theorem sideChoices_complete (i : Fin 20) :
    sideChoices i.val = (row sideEdges i.val).sublists := by
  fin_cases i <;> decide +kernel

theorem sideCheckRows (test : List Edge → Bool) (n i : ℕ) (prior : List Edge) (hi : i+n ≤ 20) :
    checkRows sideChoices (isPort 20) test i prior n = check sideEdges (isPort 20) test i prior n :=
  checkRows_eq _ _ _ _ _ _ _ fun j _ hj => sideChoices_complete ⟨j,by omega⟩

end PrismCounterexample.Gadget

namespace PrismCounterexample.Gadget

private def initial0 : List Edge := [(2, 4), (2, 3), (3, 5), (4, 6), (5, 7)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk0 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial0 14 = true := by
  decide +kernel

private def initial1 : List Edge := [(2, 4), (2, 3), (3, 5), (4, 5)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk1 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial1 14 = true := by
  decide +kernel

private def initial2 : List Edge := [(1, 3), (2, 4), (2, 3), (4, 5), (5, 7)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk2 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial2 14 = true := by
  decide +kernel

private def initial3 : List Edge := [(1, 9), (2, 4), (2, 3), (3, 5), (4, 6), (5, 7)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk3 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial3 14 = true := by
  decide +kernel

private def initial4 : List Edge := [(1, 9), (2, 4), (2, 3), (3, 5), (4, 5)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk4 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial4 14 = true := by
  decide +kernel

private def initial5 : List Edge := [(1, 3), (1, 9), (2, 4), (2, 3), (4, 5), (5, 7)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk5 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial5 14 = true := by
  decide +kernel

private def initial6 : List Edge := [(0, 2), (2, 3), (3, 5), (4, 6), (4, 5)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk6 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial6 14 = true := by
  decide +kernel

private def initial7 : List Edge := [(0, 2), (1, 3), (2, 4), (3, 5), (4, 6), (5, 7)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk7 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial7 14 = true := by
  decide +kernel

private def initial8 : List Edge := [(0, 2), (1, 3), (2, 4), (3, 5), (4, 5)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk8 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial8 14 = true := by
  decide +kernel

private def initial9 : List Edge := [(0, 2), (1, 3), (2, 3), (4, 6), (4, 5), (5, 7)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk9 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial9 14 = true := by
  decide +kernel

private def initial10 : List Edge := [(0, 2), (1, 9), (2, 3), (3, 5), (4, 6), (4, 5)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk10 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial10 14 = true := by
  decide +kernel

private def initial11 : List Edge := [(0, 2), (1, 3), (1, 9), (2, 4), (3, 5), (4, 6), (5, 7)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk11 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial11 14 = true := by
  decide +kernel

private def initial12 : List Edge := [(0, 2), (1, 3), (1, 9), (2, 4), (3, 5), (4, 5)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk12 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial12 14 = true := by
  decide +kernel

private def initial13 : List Edge := [(0, 2), (1, 3), (1, 9), (2, 3), (4, 6), (4, 5), (5, 7)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk13 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial13 14 = true := by
  decide +kernel

private def initial14 : List Edge := [(0, 8), (2, 4), (2, 3), (3, 5), (4, 6), (5, 7)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk14 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial14 14 = true := by
  decide +kernel

private def initial15 : List Edge := [(0, 8), (2, 4), (2, 3), (3, 5), (4, 5)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk15 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial15 14 = true := by
  decide +kernel

private def initial16 : List Edge := [(0, 8), (1, 3), (2, 4), (2, 3), (4, 5), (5, 7)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk16 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial16 14 = true := by
  decide +kernel

private def initial17 : List Edge := [(0, 8), (1, 9), (2, 4), (2, 3), (3, 5), (4, 6), (5, 7)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk17 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial17 14 = true := by
  decide +kernel

private def initial18 : List Edge := [(0, 8), (1, 9), (2, 4), (2, 3), (3, 5), (4, 5)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk18 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial18 14 = true := by
  decide +kernel

private def initial19 : List Edge := [(0, 8), (1, 3), (1, 9), (2, 4), (2, 3), (4, 5), (5, 7)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk19 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial19 14 = true := by
  decide +kernel

private def initial20 : List Edge := [(0, 2), (0, 8), (2, 3), (3, 5), (4, 6), (4, 5)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk20 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial20 14 = true := by
  decide +kernel

private def initial21 : List Edge := [(0, 2), (0, 8), (1, 3), (2, 4), (3, 5), (4, 6), (5, 7)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk21 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial21 14 = true := by
  decide +kernel

private def initial22 : List Edge := [(0, 2), (0, 8), (1, 3), (2, 4), (3, 5), (4, 5)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk22 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial22 14 = true := by
  decide +kernel

private def initial23 : List Edge := [(0, 2), (0, 8), (1, 3), (2, 3), (4, 6), (4, 5), (5, 7)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk23 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial23 14 = true := by
  decide +kernel

private def initial24 : List Edge := [(0, 2), (0, 8), (1, 9), (2, 3), (3, 5), (4, 6), (4, 5)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk24 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial24 14 = true := by
  decide +kernel

private def initial25 : List Edge := [(0, 2), (0, 8), (1, 3), (1, 9), (2, 4), (3, 5), (4, 6), (5, 7)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk25 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial25 14 = true := by
  decide +kernel

private def initial26 : List Edge := [(0, 2), (0, 8), (1, 3), (1, 9), (2, 4), (3, 5), (4, 5)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk26 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial26 14 = true := by
  decide +kernel

private def initial27 : List Edge := [(0, 2), (0, 8), (1, 3), (1, 9), (2, 3), (4, 6), (4, 5), (5, 7)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem sideChunk27 :
    checkRows sideChoices (isPort 20) (packedStateTest 20 sideStates) 6 initial27 14 = true := by
  decide +kernel

private def sideInitials : List (List Edge) :=
 [initial0, initial1, initial2, initial3, initial4, initial5, initial6, initial7, initial8, initial9, initial10, initial11, initial12, initial13, initial14, initial15, initial16, initial17, initial18, initial19, initial20, initial21, initial22, initial23, initial24, initial25, initial26, initial27]

private theorem initials_complete :
    (enumerate sideEdges (isPort 20) 0 [] 6).all sideInitials.contains = true := by
  decide +kernel

theorem side_packed_certificate :
    check sideEdges (isPort 20) (packedStateTest 20 sideStates) 0 [] 20 = true := by
  rw [show 20 = 6+14 by decide, check_append, List.all_eq_true]
  intro first hf
  rw [← sideCheckRows (packedStateTest 20 sideStates) 14 6 first (by decide)]
  have ht := List.all_eq_true.mp initials_complete first hf
  have hm : first ∈ sideInitials := List.contains_iff_mem.mp ht
  simp only [sideInitials, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact sideChunk0
  · exact sideChunk1
  · exact sideChunk2
  · exact sideChunk3
  · exact sideChunk4
  · exact sideChunk5
  · exact sideChunk6
  · exact sideChunk7
  · exact sideChunk8
  · exact sideChunk9
  · exact sideChunk10
  · exact sideChunk11
  · exact sideChunk12
  · exact sideChunk13
  · exact sideChunk14
  · exact sideChunk15
  · exact sideChunk16
  · exact sideChunk17
  · exact sideChunk18
  · exact sideChunk19
  · exact sideChunk20
  · exact sideChunk21
  · exact sideChunk22
  · exact sideChunk23
  · exact sideChunk24
  · exact sideChunk25
  · exact sideChunk26
  · exact sideChunk27

end PrismCounterexample.Gadget

namespace PrismCounterexample.Gadget

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem raw_parallel_check :
    sideStates.all (fun s => sideStates.all fun t =>
      if (rawParallelDegrees s t).all (· ≤ 2) then rawStates.contains (rawParallel s t) else true) = true := by
  decide +kernel

theorem raw_parallel_mem {s t : Signature} (hs : s ∈ sideStates) (ht : t ∈ sideStates)
    (hd : (rawParallelDegrees s t).all (· ≤ 2) = true) : rawParallel s t ∈ rawStates := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp raw_parallel_check s hs) t ht
  simp only [if_pos hd] at h
  exact List.contains_iff_mem.mp h

theorem raw_mirror_mem {s : Signature} (hs : s ∈ rawStates) : swapSides s ∈ mirroredRawStates :=
  List.mem_map.mpr ⟨s,hs,rfl⟩

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk0 : checkLine ([0, 0, 2, 2], [0, 1, 2, 2]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk1 : checkLine ([0, 1, 1, 2], [0, 1, 1, 1]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk2 : checkLine ([0, 1, 2, 1], [0, 1, 1, 1]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk3 : checkLine ([0, 2, 0, 2], [0, 1, 2, 1]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk4 : checkLine ([0, 2, 1, 1], [0, 1, 1, 1]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk5 : checkLine ([0, 2, 2, 0], [0, 1, 1, 3]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk6 : checkLine ([0, 2, 2, 2], [0, 1, 1, 1]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk7 : checkLine ([1, 0, 1, 2], [0, 1, 0, 0]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk8 : checkLine ([1, 0, 2, 1], [0, 1, 0, 0]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk9 : checkLine ([1, 1, 0, 2], [0, 0, 2, 0]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk10 : checkLine ([1, 1, 1, 1], [0, 1, 0, 1]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk11 : checkLine ([1, 1, 1, 1], [0, 1, 1, 0]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk12 : checkLine ([1, 1, 2, 0], [0, 0, 0, 3]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk13 : checkLine ([1, 1, 2, 2], [0, 0, 0, 0]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk14 : checkLine ([1, 1, 2, 2], [0, 0, 2, 2]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk15 : checkLine ([1, 2, 1, 2], [0, 0, 0, 0]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk16 : checkLine ([1, 2, 1, 2], [0, 1, 0, 1]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk17 : checkLine ([1, 2, 2, 1], [0, 0, 0, 0]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk18 : checkLine ([1, 2, 2, 1], [0, 1, 1, 0]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk19 : checkLine ([2, 0, 0, 2], [0, 1, 2, 0]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk20 : checkLine ([2, 0, 1, 1], [0, 1, 0, 0]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk21 : checkLine ([2, 0, 2, 0], [0, 1, 0, 3]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk22 : checkLine ([2, 0, 2, 2], [0, 1, 0, 0]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk23 : checkLine ([2, 1, 1, 2], [0, 0, 0, 0]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk24 : checkLine ([2, 1, 1, 2], [0, 1, 1, 0]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk25 : checkLine ([2, 1, 2, 1], [0, 0, 0, 0]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk26 : checkLine ([2, 1, 2, 1], [0, 1, 0, 1]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk27 : checkLine ([2, 2, 0, 2], [0, 0, 2, 0]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk28 : checkLine ([2, 2, 1, 1], [0, 0, 0, 0]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk29 : checkLine ([2, 2, 2, 0], [0, 0, 0, 3]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk30 : checkLine ([2, 2, 2, 2], [0, 0, 0, 0]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk31 : checkLine ([2, 2, 2, 2], [0, 0, 2, 2]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk32 : checkLine ([2, 2, 2, 2], [0, 1, 0, 1]) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem lineChunk33 : checkLine ([2, 2, 2, 2], [0, 1, 1, 0]) = true := by
  decide +kernel

theorem checkLine_of_raw {j : Signature} (hj : j ∈ rawStates) : checkLine j = true := by
  simp only [rawStates, List.mem_cons, List.not_mem_nil, or_false] at hj
  rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact lineChunk0
  · exact lineChunk1
  · exact lineChunk2
  · exact lineChunk3
  · exact lineChunk4
  · exact lineChunk5
  · exact lineChunk6
  · exact lineChunk7
  · exact lineChunk8
  · exact lineChunk9
  · exact lineChunk10
  · exact lineChunk11
  · exact lineChunk12
  · exact lineChunk13
  · exact lineChunk14
  · exact lineChunk15
  · exact lineChunk16
  · exact lineChunk17
  · exact lineChunk18
  · exact lineChunk19
  · exact lineChunk20
  · exact lineChunk21
  · exact lineChunk22
  · exact lineChunk23
  · exact lineChunk24
  · exact lineChunk25
  · exact lineChunk26
  · exact lineChunk27
  · exact lineChunk28
  · exact lineChunk29
  · exact lineChunk30
  · exact lineChunk31
  · exact lineChunk32
  · exact lineChunk33

theorem line_rejected {j₁ l₁ r₁ j₂ l₂ r₂ : Signature} {a b c d e : Bool}
    (hj₁ : j₁ ∈ rawStates) (hl₁ : l₁ ∈ mirroredRawStates) (hr₁ : r₁ ∈ cycleStates)
    (hj₂ : j₂ ∈ rawStates) (hl₂ : l₂ ∈ mirroredRawStates) (hr₂ : r₂ ∈ cycleStates)
    (ha : jointOK j₁ l₁ a = true) (hb : jointOK l₁ r₁ b = true)
    (hc : jointOK r₁ j₂ c = true) (hd : jointOK j₂ l₂ d = true) (he : jointOK l₂ r₂ e = true) :
    projected (outerDegrees [j₁,l₁,r₁,j₂,l₂,r₂])
      (lineTags [j₁,l₁,r₁,j₂,l₂,r₂] [a,b,c,d,e]) outerSlots = none := by
  have h0 := checkLine_of_raw hj₁
  have h1 := List.all_eq_true.mp h0 (l₁,a) (allowedNext_mem hl₁ ha)
  have h2 := List.all_eq_true.mp h1 (r₁,b) (allowedNext_mem hr₁ hb)
  have h3 := List.all_eq_true.mp h2 (j₂,c) (allowedNext_mem hj₂ hc)
  have h4 := List.all_eq_true.mp h3 (l₂,d) (allowedNext_mem hl₂ hd)
  have h5 := List.all_eq_true.mp h4 (r₂,e) (allowedNext_mem hr₂ he)
  simpa only [rejectLine, Option.isNone_iff_eq_none] using h5

end PrismCounterexample.Gadget

namespace PrismCounterexample

open SimpleGraph Gadget

theorem all_local_cases : localObstruction :=
  local_obstruction_from_certificates side_packed_certificate
    (fun hs ht hd => raw_parallel_mem hs ht hd)
    (fun hj₁ hl₁ hr₁ hj₂ hl₂ hr₂ ha hb hc hd he =>
      line_rejected hj₁ hl₁ hr₁ hj₂ hl₂ hr₂ ha hb hc hd he)

end PrismCounterexample

theorem OMA.disproof :
    ¬ (type_of% @OMA.S_opg_every_prism_over_a_3_connected_planar_graph_is_hamiltonian.main) :=
  PrismCounterexample.exact_disproof_of PrismCounterexample.all_local_cases
