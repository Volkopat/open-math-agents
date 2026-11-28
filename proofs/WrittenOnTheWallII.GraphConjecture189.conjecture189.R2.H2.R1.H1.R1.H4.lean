import OMAReductions.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1_H1_R1
-- Written on the Wall II, Graph 189. Integration by @ali-hamdan-007.
-- R2 by @carl2sheriff, with R1 path and metric arguments by
-- @computerfreak97 (PR 2971) and philipsaint's Dirac formalization.
-- The linked-set theorem of Ma, Ning and Zhao was formalized by @koolkao,
-- https://github.com/lefttosolve2/open-math-agents/pull/7971
-- Sources and credits are in github.com/ali-hamdan-007/open-math-agents,
-- research/parallel-lean-results, research/graph189/full/direct/continuation.
section
namespace Graph189AtomCounts
theorem atom_count {ac atc ad sc st sd bc bt bd s a : ℕ}
    (size : a = ac+atc+ad) (row : s = sc+st+sd) (col : s = atc+st+bt)
    (cSize : a ≤ ac+sc+bc) (dSize : a ≤ ad+sd+bd)
    (cCorner : 0 < ac → s < atc+st+sc) (dCorner : 0 < ad → s < atc+st+sd)
    (cOpp : 0 < bc → s ≤ bt+st+sc) (dOpp : 0 < bd → s ≤ bt+st+sd) :
    ac = 0 ∧ ad = 0 ∧ 2*a ≤ s := by
  have first : ac = 0 := by
    by_cases pos : ac = 0
    · exact pos
    have split := cCorner (by omega)
    by_cases opposite : 0 < bd
    · have := dOpp opposite
      omega
    · omega
  have last : ad = 0 := by
    by_cases pos : ad = 0
    · exact pos
    have split := dCorner (by omega)
    by_cases opposite : 0 < bc
    · have := cOpp opposite
      omega
    · omega
  have c : a ≤ sc := by
    by_cases h : 0 < bc
    · have := cOpp h
      omega
    · omega
  have d : a ≤ sd := by
    by_cases h : 0 < bd
    · have := dOpp h
      omega
    · omega
  exact ⟨first,last,by omega⟩
end Graph189AtomCounts
end
section
namespace Graph189CutSides
open Finset SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
theorem walk_exits (P : V → Prop) {x y : V} (p : G.Walk x y) (hx : P x) (hy : ¬ P y) :
    ∃ u v, P u ∧ ¬ P v ∧ G.Adj u v ∧ v ∈ p.support := by
  classical
  induction p with
  | nil => exact (hy hx).elim
  | @cons x t y e p ih =>
    by_cases ht : P t
    · obtain ⟨u,v,hu,hv,huv,hm⟩ := ih ht hy
      exact ⟨u,v,hu,hv,huv, List.mem_cons_of_mem _ hm⟩
    · exact ⟨x,t,hx,ht,e, List.mem_cons_of_mem _ p.start_mem_support⟩
structure CutSides (G : SimpleGraph V) (A B S : Finset V) : Prop where
  left_nonempty : A.Nonempty
  right_nonempty : B.Nonempty
  apart : Disjoint A B
  left_cut : Disjoint A S
  right_cut : Disjoint B S
  cover : ∀ u, u ∈ A ∨ u ∈ B ∨ u ∈ S
  no_cross : ∀ u ∈ A, ∀ v ∈ B, ¬ G.Adj u v
namespace CutSides
variable {A B S : Finset V} (sides : CutSides G A B S)
include sides
theorem swap : CutSides G B A S where
  left_nonempty := sides.right_nonempty
  right_nonempty := sides.left_nonempty
  apart := sides.apart.symm
  left_cut := sides.right_cut
  right_cut := sides.left_cut
  cover u := by rcases sides.cover u with h | h | h <;> tauto
  no_cross v hv u hu h := sides.no_cross u hu v hv h.symm
variable [DecidableEq V]
theorem contact {i : V}
    (restore : (G.induce {u : V | u ∉ S.erase i}).Connected) :
    ∃ a ∈ A, G.Adj a i := by
  classical
  obtain ⟨x,hx⟩ := sides.left_nonempty
  obtain ⟨y,hy⟩ := sides.right_nonempty
  let T : Set V := {u : V | u ∉ S.erase i}
  have hxt : x ∈ T := fun h => disjoint_left.mp sides.left_cut hx (mem_erase.mp h).2
  have hyt : y ∈ T := fun h => disjoint_left.mp sides.right_cut hy (mem_erase.mp h).2
  obtain ⟨p⟩ := restore (⟨x,hxt⟩ : T) (⟨y,hyt⟩ : T)
  obtain ⟨u,v,hu,hv,edge,_⟩ := walk_exits (G := G.induce T) (fun t : T => t.val ∈ A)
    p hx (fun h => disjoint_left.mp sides.apart h hy)
  have adj : G.Adj u.val v.val := edge
  rcases sides.cover v.val with h | h | h
  · exact (hv h).elim
  · exact (sides.no_cross u.val hu v.val h adj).elim
  · have eq : v.val = i := by
      by_contra ne
      exact v.property (mem_erase.mpr ⟨ne,h⟩)
    exact ⟨u.val,hu,eq ▸ adj⟩
theorem contacts_of_minimum
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {u : V | u ∉ T}).Connected)
    {i : V} (hi : i ∈ S) :
    (∃ a ∈ A, G.Adj a i) ∧ (∃ b ∈ B, G.Adj b i) := by
  have h := smaller (S.erase i) (card_erase_lt_of_mem hi)
  exact ⟨sides.contact h, sides.swap.contact h⟩
end CutSides
end Graph189CutSides
end
section
namespace Graph189CutCorner
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {A B S C D T : Finset V}
omit [Fintype V] in
theorem three_parts (l : Graph189CutSides.CutSides G A B S) (X : Finset V) :
    (X ∩ A).card + (X ∩ S).card + (X ∩ B).card = X.card := by
  have dis (P Q : Finset V) (h : Disjoint P Q) : Disjoint (X ∩ P) (X ∩ Q) :=
    Finset.disjoint_left.mpr (fun _ i j => Finset.disjoint_left.mp h (mem_inter.mp i).2 (mem_inter.mp j).2)
  have full : (X ∩ A) ∪ (X ∩ S) ∪ (X ∩ B) = X := by
    ext u
    simp only [mem_union,mem_inter]
    rcases l.cover u with hu | hu | hu <;> tauto
  rw [← card_union_of_disjoint (dis _ _ l.left_cut),
    ← card_union_of_disjoint (disjoint_union_left.mpr ⟨dis _ _ l.apart,dis _ _ l.right_cut.symm⟩),full]
def boundary (A S C T : Finset V) := ((A ∩ T) ∪ (S ∩ T)) ∪ (S ∩ C)
omit [Fintype V] in
theorem boundary_card (l : Graph189CutSides.CutSides G A B S)
    (r : Graph189CutSides.CutSides G C D T) :
    (boundary A S C T).card = (A ∩ T).card + (S ∩ T).card + (S ∩ C).card := by
  have x : Disjoint (A ∩ T) (S ∩ T) := Finset.disjoint_left.mpr (fun _ p q =>
    Finset.disjoint_left.mp l.left_cut (mem_inter.mp p).1 (mem_inter.mp q).1)
  have y : Disjoint (A ∩ T) (S ∩ C) := Finset.disjoint_left.mpr (fun _ p q =>
    Finset.disjoint_left.mp l.left_cut (mem_inter.mp p).1 (mem_inter.mp q).1)
  have z : Disjoint (S ∩ T) (S ∩ C) := Finset.disjoint_left.mpr (fun _ p q =>
    Finset.disjoint_left.mp r.left_cut (mem_inter.mp q).2 (mem_inter.mp p).2)
  rw [boundary,card_union_of_disjoint (disjoint_union_left.mpr ⟨y,z⟩),card_union_of_disjoint x]
theorem corner (l : Graph189CutSides.CutSides G A B S) (r : Graph189CutSides.CutSides G C D T)
    (nonempty : (A ∩ C).Nonempty) :
    ∃ F, Graph189CutSides.CutSides G (A ∩ C) F (boundary A S C T) := by
  classical
  let U := A ∩ C
  let K := boundary A S C T
  let F := univ \ (U ∪ K)
  have bk {v} (hv : v ∈ B) : v ∉ K := by
    intro h
    rcases mem_union.mp h with h | h
    · rcases mem_union.mp h with h | h
      · exact Finset.disjoint_left.mp l.apart (mem_inter.mp h).1 hv
      · exact Finset.disjoint_left.mp l.right_cut hv (mem_inter.mp h).1
    · exact Finset.disjoint_left.mp l.right_cut hv (mem_inter.mp h).1
  obtain ⟨b,hb⟩ := l.right_nonempty
  have bu : b ∉ U := fun h => Finset.disjoint_left.mp l.apart (mem_inter.mp h).1 hb
  have ff : b ∈ F := mem_sdiff.mpr ⟨mem_univ _,fun h => (mem_union.mp h).elim bu (bk hb)⟩
  have uk : Disjoint U K := by
    apply Finset.disjoint_left.mpr
    intro v huv hkv
    obtain ⟨a,c⟩ := mem_inter.mp huv
    rcases mem_union.mp hkv with h | h
    · rcases mem_union.mp h with h | h
      · exact Finset.disjoint_left.mp r.left_cut c (mem_inter.mp h).2
      · exact Finset.disjoint_left.mp l.left_cut a (mem_inter.mp h).1
    · exact Finset.disjoint_left.mp l.left_cut a (mem_inter.mp h).1
  refine ⟨F,⟨nonempty,⟨b,ff⟩,?_,uk,?_,?_,?_⟩⟩
  · exact Finset.disjoint_left.mpr (fun _ hu hf => (mem_sdiff.mp hf).2 (mem_union_left _ hu))
  · exact Finset.disjoint_left.mpr (fun _ hf hk => (mem_sdiff.mp hf).2 (mem_union_right _ hk))
  · intro v
    by_cases hu : v ∈ U
    · exact Or.inl hu
    by_cases hk : v ∈ K
    · exact Or.inr (Or.inr hk)
    exact Or.inr (Or.inl (mem_sdiff.mpr ⟨mem_univ _,fun h => (mem_union.mp h).elim hu hk⟩))
  · intro u hu v hv edge
    obtain ⟨ua,uc⟩ := mem_inter.mp hu
    have no := (mem_sdiff.mp hv).2
    rcases l.cover v with va | vb | vs
    · rcases r.cover v with vc | vd | vt
      · exact no (mem_union_left _ (mem_inter.mpr ⟨va,vc⟩))
      · exact r.no_cross u uc v vd edge
      · exact no (mem_union_right _ (mem_union_left _ (mem_union_left _ (mem_inter.mpr ⟨va,vt⟩))))
    · exact l.no_cross u ua v vb edge
    · rcases r.cover v with vc | vd | vt
      · exact no (mem_union_right _ (mem_union_right _ (mem_inter.mpr ⟨vs,vc⟩)))
      · exact r.no_cross u uc v vd edge
      · exact no (mem_union_right _ (mem_union_left _ (mem_union_right _ (mem_inter.mpr ⟨vs,vt⟩))))
end Graph189CutCorner
end
section
open Finset SimpleGraph
namespace Graph189Atom
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable {A B S C D T : Finset V}
theorem in_cut (l : Graph189CutSides.CutSides G A B S) (r : Graph189CutSides.CutSides G C D T)
    (same : T.card = S.card)
    (minCut : ∀ {U W K : Finset V}, Graph189CutSides.CutSides G U W K → S.card ≤ K.card)
    (atom : ∀ {U W K : Finset V}, Graph189CutSides.CutSides G U W K →
      K.card = S.card → A.card ≤ U.card)
    (meet : (A ∩ T).Nonempty) : A ⊆ T ∧ 2*A.card ≤ S.card := by
  classical
  have floor {U W L M : Finset V} (left : Graph189CutSides.CutSides G U W S)
      (right : Graph189CutSides.CutSides G L M T) (h : 0 < (U ∩ L).card) :
      S.card ≤ (U ∩ T).card+(S ∩ T).card+(S ∩ L).card := by
    obtain ⟨F,c⟩ := Graph189CutCorner.corner left right (card_pos.mp h)
    simpa only [← Graph189CutCorner.boundary_card left right] using minCut c
  have strict {L M : Finset V} (right : Graph189CutSides.CutSides G L M T)
      (h : 0 < (A ∩ L).card) (hlt : (A ∩ L).card < A.card) :
      S.card < (A ∩ T).card+(S ∩ T).card+(S ∩ L).card := by
    obtain ⟨F,c⟩ := Graph189CutCorner.corner l right (card_pos.mp h)
    have lower := minCut c
    have diff : (Graph189CutCorner.boundary A S L T).card ≠ S.card :=
      fun eq => (not_lt_of_ge (atom c eq)) hlt
    rw [← Graph189CutCorner.boundary_card l right]
    omega
  have aSize := Graph189CutCorner.three_parts r A
  have sSize := Graph189CutCorner.three_parts r S
  have tSize := Graph189CutCorner.three_parts l T
  have cSize := Graph189CutCorner.three_parts l C
  have dSize := Graph189CutCorner.three_parts l D
  simp only [inter_comm T A,inter_comm T S,inter_comm T B] at tSize
  simp only [inter_comm C A,inter_comm C S,inter_comm C B] at cSize
  simp only [inter_comm D A,inter_comm D S,inter_comm D B] at dSize
  have met := card_pos.mpr meet
  obtain ⟨lac,lad,half⟩ := Graph189AtomCounts.atom_count aSize.symm sSize.symm
    (tSize.trans same).symm (cSize ▸ atom r same) (dSize ▸ atom r.swap same)
    (fun h => strict r h (by omega)) (fun h => strict r.swap h (by omega))
    (floor l.swap r) (floor l.swap r.swap)
  refine ⟨?_,half⟩
  intro x hx
  rcases r.cover x with c | d | t
  · have h := card_pos.mpr (show (A ∩ C).Nonempty from ⟨x,mem_inter.mpr ⟨hx,c⟩⟩)
    omega
  · have h := card_pos.mpr (show (A ∩ D).Nonempty from ⟨x,mem_inter.mpr ⟨hx,d⟩⟩)
    omega
  · exact t
end Graph189Atom
end
section
open Finset SimpleGraph
namespace Graph189Removable
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem degree_in_side {A B S : Finset V} (l : Graph189CutSides.CutSides G A B S)
    {v : V} (hv : v ∈ A) : G.degree v + 1 ≤ A.card + S.card := by
  classical
  have incl : G.neighborFinset v ⊆ A.erase v ∪ S := by
    intro y hy
    have edge := (G.mem_neighborFinset _ _).mp hy
    rcases l.cover y with h | h | h
    · exact mem_union_left _ (mem_erase.mpr ⟨edge.ne.symm,h⟩)
    · exact (l.no_cross v hv y h edge).elim
    · exact mem_union_right _ h
  have h := (card_le_card incl).trans (card_union_le _ _)
  rw [G.card_neighborFinset_eq_degree] at h
  have e := card_erase_of_mem hv
  have pos := card_pos.mpr (show A.Nonempty from ⟨v,hv⟩)
  omega
theorem exists_outside_every_min_cut {s : ℕ}
    (hasCut : ∃ A B S : Finset V, S.card = s ∧ Graph189CutSides.CutSides G A B S)
    (minCut : ∀ {U W K : Finset V}, Graph189CutSides.CutSides G U W K → s ≤ K.card)
    (degree : 3*s < 2*(G.minDegree+1)) :
    ∃ v : V, ∀ {C D T : Finset V}, Graph189CutSides.CutSides G C D T → T.card = s → v ∉ T := by
  classical
  let family : Finset (Finset V) := univ.filter fun X =>
    ∃ B S : Finset V, S.card = s ∧ Graph189CutSides.CutSides G X B S
  obtain ⟨A0,B0,S0,hs0,l0⟩ := hasCut
  have h0 : A0 ∈ family := mem_filter.mpr ⟨mem_univ _,B0,S0,hs0,l0⟩
  obtain ⟨A,hA,hmin⟩ := family.exists_min_image Finset.card ⟨A0,h0⟩
  obtain ⟨B,S,hs,l⟩ := (mem_filter.mp hA).2
  obtain ⟨v,hv⟩ := l.left_nonempty
  have d := degree_in_side l hv
  have mv := G.minDegree_le_degree v
  refine ⟨v,?_⟩
  intro C D T r ht vin
  have meet : (A ∩ T).Nonempty := ⟨v,mem_inter.mpr ⟨hv,vin⟩⟩
  have atom {U W K : Finset V} (q : Graph189CutSides.CutSides G U W K)
      (eq : K.card = S.card) : A.card ≤ U.card :=
    hmin U (mem_filter.mpr ⟨mem_univ _,W,K,eq.trans hs,q⟩)
  have bound {U W K : Finset V} (q : Graph189CutSides.CutSides G U W K) : S.card ≤ K.card :=
    hs ▸ minCut q
  have half := (Graph189Atom.in_cut l r (ht.trans hs.symm) bound atom meet).2
  omega
end Graph189Removable
end
section
namespace Graph189UniversalCycle
open SimpleGraph
variable {V : Type*} {G K : SimpleGraph V}
def completeAt (G : SimpleGraph V) (z : V) : SimpleGraph V where
  Adj a b := G.Adj a b ∨ (a = z ∨ b = z) ∧ a ≠ b
  symm := by
    constructor
    rintro a b (h|⟨hz,hn⟩)
    · exact Or.inl h.symm
    · exact Or.inr ⟨hz.symm,hn.symm⟩
  loopless := by
    constructor
    intro a h
    rcases h with h|⟨_,h⟩
    · exact G.loopless.irrefl a h
    · exact h rfl
private theorem transfer_walk {z a b : V}
    (away : ∀ a b, a ≠ z → b ≠ z → G.Adj a b → K.Adj a b)
    (p : G.Walk a b) (avoid : z ∉ p.support) :
    ∃ q : K.Walk a b, q.support = p.support ∧ q.length = p.length := by
  induction p with
  | nil => exact ⟨.nil,rfl,rfl⟩
  | @cons a b c hab p ih =>
    have rest : z ∉ p.support := fun h => avoid (by simp [h])
    obtain ⟨q,hq,hl⟩ := ih rest
    have ax : a ≠ z := by rintro rfl; exact avoid (by simp)
    have bx : b ≠ z := by rintro rfl; exact rest p.start_mem_support
    exact ⟨q.cons (away a b ax bx hab), by simp [hq], by simp [hl]⟩
theorem close_path {z a b : V} (hz : ∀ v, v ≠ z → K.Adj z v)
    (p : K.Walk a b) (hp : p.IsPath) (avoid : z ∉ p.support) (pos : 0 < p.length) :
    ∃ c : K.Walk z z, c.IsCycle ∧ c.length = p.length + 2 := by
  have ha := hz a (fun h => avoid (h ▸ p.start_mem_support))
  have hb := hz b (fun h => avoid (h ▸ p.end_mem_support))
  refine ⟨.cons ha (p.concat hb.symm),?_,by simp [Nat.add_assoc]⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  refine ⟨?_,by simp only [Walk.length_cons,Walk.length_concat]; omega⟩
  rw [Walk.tail_cons]
  exact (Walk.isPath_copy _ _ _).mpr (hp.concat avoid hb.symm)
private theorem open_cycle {z : V} (c : K.Walk z z) (hc : c.IsCycle) :
    ∃ a b, ∃ p : K.Walk a b, p.IsPath ∧ z ∉ p.support ∧
      p.length + 2 = c.length ∧ ∀ v, v ∈ p.support ↔ v ≠ z ∧ v ∈ c.support := by
  cases c with
  | nil => exact (hc.not_nil Walk.Nil.nil).elim
  | @cons _ a _ hza r =>
    have path := ((Walk.cons_isCycle_iff r hza).mp hc).1
    have rn := Walk.not_nil_of_isCycle_cons hc
    have split : r.support = r.dropLast.support ++ [z] := by
      rw [r.support_dropLast rn]
      have ne := r.support_ne_nil
      conv_lhs => rw [←List.dropLast_append_getLast ne]
      congr 1
      simp
    have nd := path.support_nodup
    rw [split,List.nodup_append] at nd
    have avoid : z ∉ r.dropLast.support := fun hz => nd.2.2 z hz z (by simp) rfl
    refine ⟨a,r.penultimate,r.dropLast,Walk.IsPath.mk' nd.1,avoid,?_,?_⟩
    · have := r.length_dropLast_add_one rn
      simp only [Walk.length_cons]
      omega
    · intro v
      rw [Walk.support_cons,split]
      simp only [List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
      constructor
      · intro hv
        exact ⟨fun h => avoid (h ▸ hv),Or.inr (Or.inl hv)⟩
      · rintro ⟨hne,h|h|h⟩
        · exact (hne h).elim
        · exact h
        · exact (hne h).elim
theorem longest_cycle_transfer (z : V) (hz : ∀ v, v ≠ z → K.Adj z v)
    (same : ∀ a b, a ≠ z → b ≠ z → (K.Adj a b ↔ G.Adj a b))
    {v : V} (c : K.Walk v v) (hc : c.IsCycle)
    (maximal : ∀ v (r : K.Walk v v), r.IsCycle → r.length ≤ c.length) :
    z ∈ c.support ∧ ∃ a b, ∃ p : G.Walk a b, p.IsPath ∧ z ∉ p.support ∧
      p.length + 2 = c.length ∧ (∀ v, v ∈ p.support ↔ v ≠ z ∧ v ∈ c.support) ∧
      ∀ a' b' (q : G.Walk a' b'), q.IsPath → z ∉ q.support → q.length ≤ p.length := by
  classical
  have belongs : z ∈ c.support := by
    by_contra h
    have path : c.dropLast.IsPath := by
      apply Walk.IsPath.mk'
      rw [c.support_dropLast hc.not_nil]
      exact c.tail_support_perm_dropLast_support.nodup_iff.mp hc.support_nodup
    have av : z ∉ c.dropLast.support := by
      rw [c.support_dropLast hc.not_nil]
      exact fun hz' => h (List.mem_of_mem_dropLast hz')
    have len := c.length_dropLast_add_one hc.not_nil
    have sz := hc.three_le_length
    obtain ⟨r,hr,l⟩ := close_path hz c.dropLast path av (by omega)
    have := maximal z r hr
    omega
  refine ⟨belongs,?_⟩
  obtain ⟨a,b,q,hq,avoid,sz,vertices⟩ := open_cycle (c.rotate z belongs) (hc.rotate belongs)
  obtain ⟨p,hp,pl⟩ := transfer_walk (fun a b ha hb => (same a b ha hb).mp) q avoid
  rw [Walk.length_rotate] at sz
  refine ⟨a,b,p,Walk.IsPath.mk' (by rw [hp]; exact hq.support_nodup),(by rw [hp]; exact avoid),by omega,?_,?_⟩
  · intro y
    rw [hp,vertices,Walk.mem_support_rotate_iff]
  · intro x y t ht av
    by_cases zero : t.length = 0
    · omega
    obtain ⟨r,rs,rl⟩ := transfer_walk (fun a b ha hb => (same a b ha hb).mpr) t av
    have hr : r.IsPath := Walk.IsPath.mk' (by rw [rs]; exact ht.support_nodup)
    obtain ⟨cycle,hcy,le⟩ := close_path hz r hr (by rw [rs]; exact av) (by omega)
    have := maximal z cycle hcy
    omega
theorem completeAt_longest (G : SimpleGraph V) (z : V) {v : V}
    (c : (completeAt G z).Walk v v) (hc : c.IsCycle)
    (maximal : ∀ v (r : (completeAt G z).Walk v v), r.IsCycle → r.length ≤ c.length) :
    z ∈ c.support ∧ ∃ a b, ∃ p : G.Walk a b, p.IsPath ∧ z ∉ p.support ∧
      p.length + 2 = c.length ∧ (∀ v, v ∈ p.support ↔ v ≠ z ∧ v ∈ c.support) ∧
      ∀ a' b' (q : G.Walk a' b'), q.IsPath → z ∉ q.support → q.length ≤ p.length := by
  apply longest_cycle_transfer z _ _ c hc maximal
  · exact fun v h => Or.inr ⟨Or.inl rfl,h.symm⟩
  · intro a b ha hb
    change (G.Adj a b ∨ (a = z ∨ b = z) ∧ a ≠ b) ↔ G.Adj a b
    simp [ha,hb]
theorem longest_in_deletion (G : SimpleGraph V) (z : V) {v : V}
    (c : (completeAt G z).Walk v v) (hc : c.IsCycle)
    (maximal : ∀ v (r : (completeAt G z).Walk v v), r.IsCycle → r.length ≤ c.length) :
    ∃ a b, ∃ p : (G.induce {u | u ≠ z}).Walk a b, p.IsPath ∧ p.length+2 = c.length ∧
      (∀ u, u ∈ p.support ↔ u.val ∈ c.support) ∧
      ∀ a' b' (q : (G.induce {u | u ≠ z}).Walk a' b'), q.IsPath → q.length ≤ p.length := by
  classical
  obtain ⟨_,a,b,p,hp,avoid,sz,verts,longest⟩ := completeAt_longest G z c hc maximal
  let S : Set V := {u | u ≠ z}
  have sub : ∀ u ∈ p.support, u ∈ S := by
    intro u hu eq
    exact avoid (eq ▸ hu)
  let q := p.induce S sub
  let f := (Embedding.induce (G:=G) S).toHom
  have mapQ : q.map f = p := Walk.map_induce p sub
  have qp : q.IsPath := (Walk.isPath_map_iff_of_injective
    (f:=f) Subtype.val_injective).mp (by rw [mapQ]; exact hp)
  have ql : q.length = p.length := by
    calc
      q.length = (q.map f).length := (Walk.length_map _ _).symm
      _ = p.length := congrArg (fun walk : G.Walk a b => walk.length) mapQ
  refine ⟨_,_,q,qp,by omega,?_,?_⟩
  · intro u
    have supp : List.map Subtype.val q.support = p.support := by
      calc
        List.map Subtype.val q.support = (q.map f).support := (Walk.support_map f q).symm
        _ = p.support := congrArg (fun walk : G.Walk a b => walk.support) mapQ
    constructor
    · intro hu
      have hh : u.val ∈ p.support := by
        rw [←supp]
        exact List.mem_map.mpr ⟨u,hu,rfl⟩
      exact ((verts u.val).mp hh).2
    · intro hu
      have hh := (verts u.val).mpr ⟨u.property,hu⟩
      rw [←supp] at hh
      obtain ⟨t,ht,eq⟩ := List.mem_map.mp hh
      have et : t = u := Subtype.ext eq
      exact et ▸ ht
  · intro a' b' r path
    have avoid' : z ∉ (r.map f).support := by
      rw [Walk.support_map]
      intro hz
      obtain ⟨t,_,eq⟩ := List.mem_map.mp hz
      exact t.property eq
    have pr : (r.map f).IsPath := (Walk.isPath_map_iff_of_injective
      (f:=f) Subtype.val_injective).mpr path
    have h := longest _ _ (r.map f) pr avoid'
    simpa only [Walk.length_map,ql] using h
end Graph189UniversalCycle
end
section
open Finset SimpleGraph
namespace Graph189HighPredecessor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
theorem common_lower {a b z : V} (hab : a ≠ b) (hna : ¬ G.Adj a b)
    (hza : G.Adj z a) (hzb : G.Adj z b) {k : ℕ}
    (cap : G.distEven z ≤ k+1) :
    G.degree a + G.degree b + 1 ≤ G.degree z + k +
      (G.neighborFinset a ∩ G.neighborFinset b).card := by
  classical
  let U := G.neighborFinset a ∪ G.neighborFinset b
  let E := univ.filter (fun v => Even (G.dist z v))
  have inside {v u : V} (hzu : G.Adj z u) (huv : G.Adj u v) :
      v ∈ G.neighborFinset z ∪ E := by
    by_cases hzv : G.Adj z v
    · exact mem_union_left _ ((G.mem_neighborFinset z v).mpr hzv)
    apply mem_union_right
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    by_cases he : z = v
    · subst v; simp
    let path : G.Walk z v := .cons hzu (.cons huv .nil)
    have hlo := path.reachable.one_lt_dist_of_ne_of_not_adj he hzv
    have hhi : G.dist z v ≤ 2 := G.dist_le path
    have : G.dist z v = 2 := by omega
    simp [this]
  have cover : insert a (insert b U) ⊆ G.neighborFinset z ∪ E := by
    intro v hv
    rcases mem_insert.mp hv with rfl | hv
    · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr hza)
    rcases mem_insert.mp hv with rfl | hv
    · exact mem_union_left _ ((G.mem_neighborFinset _ _).mpr hzb)
    rcases mem_union.mp hv with hv | hv
    · exact inside hza ((G.mem_neighborFinset _ _).mp hv)
    · exact inside hzb ((G.mem_neighborFinset _ _).mp hv)
  have ha : a ∉ U := by
    intro hv
    rcases mem_union.mp hv with hv | hv
    · exact G.loopless.irrefl a ((G.mem_neighborFinset _ _).mp hv)
    · exact hna ((G.mem_neighborFinset _ _).mp hv).symm
  have hb : b ∉ U := by simp [U, hna]
  have ha' : a ∉ insert b U := by simp [hab,ha]
  have hsize := (card_le_card cover).trans (card_union_le (G.neighborFinset z) E)
  rw [card_insert_of_notMem ha',card_insert_of_notMem hb,G.card_neighborFinset_eq_degree] at hsize
  have he : E.card ≤ k+1 := cap
  have hu := card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset b)
  rw [G.card_neighborFinset_eq_degree,G.card_neighborFinset_eq_degree] at hu
  change U.card + _ = _ at hu
  omega
end Graph189HighPredecessor
end
section
open SimpleGraph
open scoped BigOperators
namespace OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
lemma degree_pair [DecidableRel G.Adj] [Nontrivial V] (x y : V) (hne : x ≠ y) :
    secondSmallestDegree G ≤ G.degree x ∨ secondSmallestDegree G ≤ G.degree y := by
  classical
  let ds := degreeSequence G
  have hlen : 2 ≤ ds.length := by
    simpa [ds, degreeSequence] using Nat.succ_le_of_lt (Fintype.one_lt_card (α := V))
  obtain ⟨a,b,l,heq⟩ : ∃ a b l, ds = a :: b :: l := by
    cases h : ds with
    | nil => simp [h] at hlen
    | cons a tail =>
      cases hh : tail with
      | nil => simp [h, hh] at hlen
      | cons b l => exact ⟨a,b,l,rfl⟩
  have hs : ds.Pairwise (· ≤ ·) := by simp [ds, degreeSequence]
  rw [heq] at hs
  have hlow : ∀ t ∈ l, b ≤ t := (List.pairwise_cons.mp (List.pairwise_cons.mp hs).2).1
  have hnil : l.filter (fun t => decide (t < b)) = [] := by
    simpa [List.filter_eq_nil_iff] using hlow
  have hct : (ds.filter (fun t => decide (t < b))).length ≤ 1 := by
    rw [heq]
    by_cases h : a < b <;> simp [h,hnil]
  have hcoeds : (↑ds : Multiset ℕ) = Finset.univ.val.map (fun v : V => G.degree v) := by
    simp [ds, degreeSequence]
  let low := Finset.univ.filter (fun v : V => G.degree v < b)
  have hl : low.card ≤ 1 := by
    change (Multiset.filter (fun t => G.degree t < b) Finset.univ.val).card ≤ 1
    have hct' : (Multiset.filter (fun t => t < b) (↑ds : Multiset ℕ)).card ≤ 1 := hct
    rw [hcoeds, Multiset.filter_map, Multiset.card_map] at hct'
    exact hct'
  have hb : secondSmallestDegree G = b := by
    change ds.getD 1 0 = b
    simp [heq]
  rw [hb]
  by_contra! h
  exact hne (Finset.card_le_one.mp hl x (by simpa [low] using h.1) y (by simpa [low] using h.2))
end OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
end
section
namespace Graph189CutSides
open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
omit [DecidableEq V] in
theorem exists_cutSides_of_disconnected (S : Finset V) (survives : ∃ u, u ∉ S)
    (disc : ¬(G.induce {u : V | u ∉ S}).Connected) :
    ∃ A B, CutSides G A B S := by
  classical
  let T : Set V := {u : V | u ∉ S}
  let H := G.induce T
  obtain ⟨x,hx⟩ := survives
  let a : T := ⟨x,hx⟩
  have disconnected : ¬ H.Connected := disc
  obtain ⟨b,hb⟩ : ∃ b : T, ¬H.Reachable a b := by
    by_contra! hh
    exact disconnected ((H.connected_iff_exists_forall_reachable).mpr ⟨a,hh⟩)
  let P (v : V) := ∃ hv : v ∈ T, H.Reachable a ⟨v,hv⟩
  let A := univ.filter P
  let B := univ.filter (fun v => v ∈ T ∧ ¬P v)
  refine ⟨A,B,?_⟩
  refine ⟨⟨x,mem_filter.mpr ⟨mem_univ _,hx,Reachable.refl a⟩⟩,?_,?_,?_,?_,?_,?_⟩
  · exact ⟨b.val,mem_filter.mpr ⟨mem_univ _,b.property,fun ⟨_,h⟩ => hb h⟩⟩
  · exact disjoint_left.mpr fun _ ha h => (mem_filter.mp h).2.2 (mem_filter.mp ha).2
  ·
    apply Finset.disjoint_left.mpr
    intro v hv hs
    exact ((mem_filter.mp hv).2.choose : v ∈ T) hs
  · exact disjoint_left.mpr fun _ hv hs => (mem_filter.mp hv).2.1 hs
  · intro v
    by_cases hs : v ∈ S
    · exact Or.inr (Or.inr hs)
    by_cases hp : P v
    · exact Or.inl (mem_filter.mpr ⟨mem_univ _,hp⟩)
    · exact Or.inr (Or.inl (mem_filter.mpr ⟨mem_univ _,hs,hp⟩))
  · intro u hu v hv edge
    obtain ⟨hut,reach⟩ := (mem_filter.mp hu).2
    obtain ⟨hvt,notP⟩ := (mem_filter.mp hv).2
    have e : H.Adj ⟨u,hut⟩ ⟨v,hvt⟩ := edge
    exact notP ⟨hvt,reach.trans e.reachable⟩
namespace CutSides
variable {A B S : Finset V} (sides : CutSides G A B S)
include sides
variable [Nontrivial V] [DecidableRel G.Adj]
theorem anchor_degree
    (smaller : ∀ T : Finset V, T.card < S.card → (G.induce {u : V | u ∉ T}).Connected)
    (cap : ∀ v, G.distEven v ≤ 1 + G.secondSmallestDegree) {z : V} (hz : z ∈ S) :
    G.secondSmallestDegree + 1 ≤ G.degree z + S.card := by
  classical
  have spos : 0 < S.card := card_pos.mpr ⟨z,hz⟩
  by_cases high : G.secondSmallestDegree ≤ G.degree z
  · omega
  obtain ⟨⟨a,ha,az⟩,⟨b,hb,bz⟩⟩ := sides.contacts_of_minimum smaller hz
  have ah := (degree_pair (G := G) a z az.ne).resolve_right high
  have bh := (degree_pair (G := G) b z bz.ne).resolve_right high
  have neq : a ≠ b := fun e => disjoint_left.mp sides.apart (e ▸ ha) hb
  have cap' : G.distEven z ≤ G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm 1] using cap z
  have width := Graph189HighPredecessor.common_lower neq (sides.no_cross _ ha _ hb) az.symm bz.symm cap'
  have overlap : G.neighborFinset a ∩ G.neighborFinset b ⊆ S := by
    intro v hv
    obtain ⟨av,bv⟩ := mem_inter.mp hv
    rcases sides.cover v with h | h | hs
    · exact (sides.no_cross v h b hb ((G.mem_neighborFinset _ _).mp bv).symm).elim
    · exact (sides.no_cross a ha v h ((G.mem_neighborFinset _ _).mp av)).elim
    · exact hs
  have bound := card_le_card overlap
  omega
end CutSides
end Graph189CutSides
end
section
namespace Graph189CutSides
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem connected_after_smaller_deletion (T : Finset V) (ht : T.card < G.vertexConnectivity) :
    (G.induce {u : V | u ∉ T}).Connected := by
  classical
  by_contra bad
  have hn := Fintype.one_lt_card (α := V)
  have bound : G.vertexConnectivity ≤ T.card := by
    unfold vertexConnectivity
    rw [if_neg (by omega : ¬ Fintype.card V ≤ 1)]
    exact Nat.sInf_le ⟨T,rfl,Or.inl bad⟩
  omega
end Graph189CutSides
end
section
namespace Graph189UniversalCycle
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [Nontrivial V]
variable {G : SimpleGraph V}
instance instCompleteDecidable [DecidableEq V] [DecidableRel G.Adj] {z : V} :
    DecidableRel (completeAt G z).Adj := fun a b =>
  inferInstanceAs (Decidable (G.Adj a b ∨ (a = z ∨ b = z) ∧ a ≠ b))
omit [Fintype V] [Nontrivial V] in
private theorem completion_preconnected {z : V} (S : Finset V) (hz : z ∉ S) :
    ((completeAt G z).induce {u : V | u ∉ S}).Connected := by
  let t : {u : V | u ∉ S} := ⟨z,hz⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨t,fun u => ?_⟩
  by_cases hu : u.val = z
  · have h : u = t := Subtype.ext hu
    rw [h]
  · exact (show ((completeAt G z).induce {u : V | u ∉ S}).Adj t u from
      Or.inr ⟨Or.inl rfl,Ne.symm hu⟩).reachable
omit [Fintype V] [Nontrivial V] in
private theorem completion_preserves_connected {z : V} (S : Finset V)
    (hc : (G.induce {u : V | u ∉ S}).Connected) :
    ((completeAt G z).induce {u : V | u ∉ S}).Connected := by
  have inc : G.induce {u : V | u ∉ S} ≤ (completeAt G z).induce {u : V | u ∉ S} :=
    fun _ _ h => Or.inl h
  exact hc.mono inc
private theorem connectivity_bounds (K : SimpleGraph V) (z : V) {s : ℕ}
    (hsize : s ≤ Fintype.card V - 1)
    (small : ∀ S : Finset V, S.card < s → (K.induce {u : V | u ∉ S}).Connected) :
    s ≤ K.vertexConnectivity := by
  classical
  let M : Set ℕ := {j | ∃ S : Finset V, S.card = j ∧
    (¬(K.induce ((S : Set V)ᶜ)).Connected ∨ S.card = Fintype.card V-1)}
  have hn := Fintype.one_lt_card (α := V)
  have eq : K.vertexConnectivity = sInf M := by
    unfold vertexConnectivity
    rw [if_neg (by omega : ¬Fintype.card V ≤ 1)]
  have sz : (univ.erase z).card = Fintype.card V-1 := by
    rw [card_erase_of_mem (mem_univ z),card_univ]
  have ex : M.Nonempty := ⟨_,univ.erase z,sz,Or.inr sz⟩
  rw [eq]
  obtain ⟨T,ht,htc|htc⟩ := Nat.sInf_mem ex
  · by_contra! bad
    exact htc (small T (ht ▸ bad))
  · omega
private theorem conn_le_order (K : SimpleGraph V) (z : V) :
    K.vertexConnectivity ≤ Fintype.card V - 1 := by
  classical
  have hn := Fintype.one_lt_card (α:=V)
  unfold vertexConnectivity
  rw [if_neg (by omega : ¬Fintype.card V ≤ 1)]
  have sz : (univ.erase z).card = Fintype.card V-1 := by
    rw [card_erase_of_mem (mem_univ z),card_univ]
  exact Nat.sInf_le ⟨univ.erase z,sz,Or.inr sz⟩
theorem completeAt_connectivity (z : V) :
    G.vertexConnectivity ≤ (completeAt G z).vertexConnectivity := by
  apply connectivity_bounds _ z (conn_le_order G z)
  intro S hS
  exact completion_preserves_connected S (Graph189CutSides.connected_after_smaller_deletion S hS)
theorem completeAt_connectivity_add_one (z : V)
    (room : G.vertexConnectivity < Fintype.card V - 1)
    (no_cut : ∀ S : Finset V, S.card = G.vertexConnectivity → z ∈ S →
       (G.induce {u : V | u ∉ S}).Connected) :
    G.vertexConnectivity + 1 ≤ (completeAt G z).vertexConnectivity := by
  apply connectivity_bounds _ z (by omega)
  intro S hS
  by_cases hz : z ∈ S
  · apply completion_preserves_connected
    rcases lt_or_ge S.card G.vertexConnectivity with h|h
    · exact Graph189CutSides.connected_after_smaller_deletion S h
    · exact no_cut S (by omega) hz
  · exact completion_preconnected S hz
variable [DecidableEq V] [DecidableRel G.Adj]
omit [Nontrivial V] in
theorem degree_le_completeAt (z v : V) : G.degree v ≤ (completeAt G z).degree v := by
  rw [←G.card_neighborFinset_eq_degree,←(completeAt G z).card_neighborFinset_eq_degree]
  apply card_le_card
  intro x hx
  exact ((completeAt G z).mem_neighborFinset _ _).mpr (Or.inl ((G.mem_neighborFinset _ _).mp hx))
omit [Nontrivial V] in
theorem completeAt_degree_self (z : V) : (completeAt G z).degree z = Fintype.card V - 1 := by
  have eq : (completeAt G z).neighborFinset z = univ.erase z := by
    ext a
    simp only [SimpleGraph.mem_neighborFinset,mem_erase,mem_univ,and_true]
    constructor
    · intro h
      exact h.ne.symm
    · intro h
      exact Or.inr ⟨Or.inl rfl,h.symm⟩
  rw [←(completeAt G z).card_neighborFinset_eq_degree,eq,card_erase_of_mem (mem_univ z),card_univ]
theorem minDegree_le_completeAt (z : V) : G.minDegree ≤ (completeAt G z).minDegree := by
  obtain ⟨u,hu⟩ := (completeAt G z).exists_minimal_degree_vertex
  exact (G.minDegree_le_degree u).trans ((degree_le_completeAt z u).trans_eq hu.symm)
theorem secondDegree_le_completeAt_minDegree (z : V) (hz : G.degree z = G.minDegree) :
    G.secondSmallestDegree ≤ (completeAt G z).minDegree := by
  classical
  have high (v : V) (different : v ≠ z) : G.secondSmallestDegree ≤ G.degree v := by
    rcases degree_pair (G:=G) v z different with h|h
    · exact h
    · exact h.trans (hz ▸ G.minDegree_le_degree v)
  obtain ⟨w,hw⟩ := (completeAt G z).exists_minimal_degree_vertex
  rw [hw]
  by_cases eq : w = z
  · subst w
    rw [completeAt_degree_self]
    obtain ⟨v,hv⟩ := exists_ne z
    have := high v hv
    have := G.degree_lt_card_verts v
    omega
  · exact (high w eq).trans (degree_le_completeAt z w)
end Graph189UniversalCycle
end
section
open SimpleGraph Finset
namespace Graph189CriticalConnectivity
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]
omit [Fintype V] [DecidableEq V] [Nontrivial V] [DecidableRel G.Adj] in
theorem disconnected {A B S : Finset V} (sides : Graph189CutSides.CutSides G A B S) :
    ¬(G.induce {v : V | v ∉ S}).Connected := by
  classical
  intro conn
  obtain ⟨x,hx⟩ := sides.left_nonempty
  obtain ⟨y,hy⟩ := sides.right_nonempty
  let T : Set V := {v | v ∉ S}
  have xs : x ∈ T := fun h => Finset.disjoint_left.mp sides.left_cut hx h
  have ys : y ∈ T := fun h => Finset.disjoint_left.mp sides.right_cut hy h
  obtain ⟨p⟩ := conn (⟨x,xs⟩ : T) (⟨y,ys⟩ : T)
  obtain ⟨u,v,hu,hv,step,_⟩ := Graph189CutSides.walk_exits (G := G.induce T)
    (fun z : T => z.val ∈ A) p hx (fun h => Finset.disjoint_left.mp sides.apart h hy)
  rcases sides.cover v.val with ha | hb | hs
  · exact hv ha
  · exact sides.no_cross u.val hu v.val hb step
  · exact v.property hs
theorem free_vertex (room : G.vertexConnectivity < Fintype.card V - 1)
    (degree : 3*G.vertexConnectivity < 2*(G.minDegree+1)) :
    ∃ z : V, ∀ S : Finset V, S.card = G.vertexConnectivity → z ∈ S →
      (G.induce {v : V | v ∉ S}).Connected := by
  classical
  have parts (S : Finset V) (hs : S.card = G.vertexConnectivity)
      (bad : ¬ (G.induce {v : V | v ∉ S}).Connected) :
      ∃ A B, Graph189CutSides.CutSides G A B S := by
    have survives : ∃ u, u ∉ S := by
      by_contra! full
      have eq := Finset.eq_univ_iff_forall.mpr full
      rw [eq,card_univ] at hs
      omega
    exact Graph189CutSides.exists_cutSides_of_disconnected S survives bad
  have minCut {U W K : Finset V} (cut : Graph189CutSides.CutSides G U W K) :
      G.vertexConnectivity ≤ K.card := by
    by_contra! smaller
    exact disconnected cut (Graph189CutSides.connected_after_smaller_deletion K smaller)
  by_cases existsCut : ∃ A B S : Finset V, S.card = G.vertexConnectivity ∧
      Graph189CutSides.CutSides G A B S
  · obtain ⟨z,free⟩ := Graph189Removable.exists_outside_every_min_cut existsCut minCut degree
    refine ⟨z,?_⟩
    intro S hs hz
    by_contra bad
    obtain ⟨A,B,sides⟩ := parts S hs bad
    exact free sides hs hz
  · refine ⟨Classical.arbitrary V,?_⟩
    intro S hs _
    by_contra bad
    obtain ⟨A,B,sides⟩ := parts S hs bad
    exact existsCut ⟨A,B,S,hs,sides⟩
theorem exists_completion (room : G.vertexConnectivity < Fintype.card V - 1)
    (degree : 3*G.vertexConnectivity < 2*(G.minDegree+1)) :
    ∃ z : V, G.vertexConnectivity+1 ≤ (Graph189UniversalCycle.completeAt G z).vertexConnectivity := by
  obtain ⟨z,free⟩ := free_vertex room degree
  exact ⟨z,Graph189UniversalCycle.completeAt_connectivity_add_one z room free⟩
end Graph189CriticalConnectivity
end
section
open Finset SimpleGraph Graph189CutSides Graph189UniversalCycle
namespace Graph189AtomNonneighbor
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem free_nonneighbor (z : V)
    {U W T : Finset V} (given : CutSides G U W T) (size : T.card=G.vertexConnectivity) (onCut : z∈T)
    (room : G.vertexConnectivity < Fintype.card V-1)
    (large : 3*G.vertexConnectivity<2*(G.minDegree+1))
    (low : G.degree z < G.secondSmallestDegree)
    (deficit : G.degree z+G.vertexConnectivity ≤ G.secondSmallestDegree+1) :
    ∃ w : V, w≠z ∧ ¬G.Adj z w ∧
      G.vertexConnectivity+1≤(completeAt G w).vertexConnectivity := by
  classical
  let s := G.vertexConnectivity
  let family : Finset (Finset V) := univ.filter fun X => ∃ B S : Finset V, S.card=s ∧ CutSides G X B S
  have init : U∈family := mem_filter.mpr ⟨mem_univ _,W,T,size,given⟩
  obtain ⟨A,hA,smallest⟩ := family.exists_min_image Finset.card ⟨U,init⟩
  obtain ⟨B,S,sz,cut⟩ := (mem_filter.mp hA).2
  have minimal {X Y Z : Finset V} (c : CutSides G X Y Z) : S.card ≤ Z.card := by
    by_contra! smaller
    exact Graph189CriticalConnectivity.disconnected c (connected_after_smaller_deletion Z (smaller.trans_eq sz))
  have atom {X Y Z : Finset V} (c : CutSides G X Y Z) (eq : Z.card=S.card) : A.card ≤ X.card :=
    smallest X (mem_filter.mpr ⟨mem_univ _,Y,Z,eq.trans sz,c⟩)
  obtain ⟨a,ha⟩ := cut.left_nonempty
  have deg := Graph189Removable.degree_in_side cut ha
  have min := G.minDegree_le_degree a
  have free {v : V} (va : v∈A) {X Y Z : Finset V} (other : CutSides G X Y Z) (eq : Z.card=s) :
      v∉Z := by
    intro mem
    have bound := (Graph189Atom.in_cut cut other (eq.trans sz.symm) minimal atom
      (show (A∩Z).Nonempty from ⟨v,mem_inter.mpr ⟨va,mem⟩⟩)).2
    change 3*s<2*(G.minDegree+1) at large
    omega
  have za : z∉A := fun h => free h given size onCut
  have ahigh := (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair
    (G:=G) a z (fun e => za (e ▸ ha))).resolve_right (not_le.mpr low)
  have non : ∃ w∈A, ¬G.Adj z w := by
    by_contra! every
    have zs : z∈S := by
      rcases cut.cover z with left|right|center
      · exact (za left).elim
      · exact (cut.no_cross a ha z right (every a ha).symm).elim
      · exact center
    have small (L : Finset V) (lt : L.card < S.card) : (G.induce {v : V | v∉L}).Connected :=
      connected_after_smaller_deletion L (lt.trans_eq sz)
    obtain ⟨b,hb,bz⟩ := (cut.contacts_of_minimum small zs).2
    have fresh : b∉A := fun h => Finset.disjoint_left.mp cut.apart h hb
    have inc : insert b A ⊆ G.neighborFinset z := by
      intro v hv
      apply (G.mem_neighborFinset _ _).mpr
      rcases mem_insert.mp hv with rfl|h
      · exact bz.symm
      · exact every v h
    have count := card_le_card inc
    rw [card_insert_of_notMem fresh,G.card_neighborFinset_eq_degree] at count
    change G.degree z+s ≤ G.secondSmallestDegree+1 at deficit
    omega
  obtain ⟨w,wa,missing⟩ := non
  refine ⟨w,fun eq => za (eq ▸ wa),missing,completeAt_connectivity_add_one w room ?_⟩
  intro K ks wk
  by_contra bad
  have survive : ∃ v, v∉K := by
    by_contra! all
    have eq := eq_univ_iff_forall.mpr all
    rw [eq,card_univ] at ks
    omega
  obtain ⟨X,Y,c⟩ := exists_cutSides_of_disconnected K survive bad
  exact free wa c ks wk
theorem repaired_minDegree (z w : V) (ne : w≠z) (missing : ¬G.Adj z w)
    (low : G.degree z+1=G.secondSmallestDegree) :
    G.secondSmallestDegree≤(completeAt G w).minDegree := by
  classical
  let K := completeAt G w
  obtain ⟨u,mu⟩ := K.exists_minimal_degree_vertex
  change G.secondSmallestDegree ≤ K.minDegree
  rw [mu]
  by_cases eq : u=z
  · subst u
    have add : insert w (G.neighborFinset z) ⊆ K.neighborFinset z := by
      intro t ht
      apply (K.mem_neighborFinset _ _).mpr
      rcases mem_insert.mp ht with rfl|h
      · exact Or.inr ⟨Or.inr rfl,ne.symm⟩
      · exact Or.inl ((G.mem_neighborFinset _ _).mp h)
    have count := card_le_card add
    rw [card_insert_of_notMem (fun h => missing ((G.mem_neighborFinset _ _).mp h)),
      G.card_neighborFinset_eq_degree,K.card_neighborFinset_eq_degree,low] at count
    exact count
  have high := (OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair
    (G:=G) u z eq).resolve_right (by omega)
  exact high.trans (degree_le_completeAt w u)
end Graph189AtomNonneighbor
end
section
namespace OMA.BondyK
open SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
lemma chain_sub {R : V → V → Prop} {l l₁ : List V} (h : l.IsChain R) (hs : l₁ <:+: l) :
    l₁.IsChain R := by
  obtain ⟨s, t, rfl⟩ := hs
  exact (List.isChain_append.mp (List.isChain_append.mp h).1).2.1
lemma chain_pre {R : V → V → Prop} {l l₁ : List V} (h : l.IsChain R) (hs : l₁ <+: l) :
    l₁.IsChain R := by
  obtain ⟨t, rfl⟩ := hs
  exact (List.isChain_append.mp h).1
def ABP (G : SimpleGraph V) (A B : Finset V) (l : List V) : Prop :=
  l.Nodup ∧ l.IsChain G.Adj ∧ (∃ a ∈ A, l.head? = some a) ∧ (∃ b ∈ B, l.getLast? = some b)
def Sep (G : SimpleGraph V) (A B S : Finset V) : Prop :=
  ∀ l, ABP G A B l → ∃ x ∈ l, x ∈ S
lemma getLast?_app_cons (p q : List V) (y : V) :
    (p ++ y :: q).getLast? = (y :: q).getLast? := by
  rw [List.getLast?_append, List.getLast?_cons]; rfl
lemma erase_loops {R : V → V → Prop} : ∀ l : List V, l.IsChain R →
    ∃ l' : List V, l'.Nodup ∧ l'.IsChain R ∧ l'.head? = l.head? ∧
      l'.getLast? = l.getLast? ∧ ∀ z ∈ l', z ∈ l
  | [], _ => ⟨[], List.nodup_nil, List.isChain_nil, rfl, rfl, fun _ h => h⟩
  | z :: t, h => by
    obtain ⟨t', hnd, hch, hhd, hlast, hsub⟩ := erase_loops t (List.isChain_cons.mp h).2
    by_cases hz : z ∈ t'
    · obtain ⟨u, w, rfl⟩ := List.append_of_mem hz
      have ht : t ≠ [] := by
        rintro rfl; exact absurd (hsub z (by simp)) (by simp)
      obtain ⟨c, hc⟩ : ∃ c, t.getLast? = some c := by
        cases h' : t.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp h') ht
        | some c => exact ⟨c, rfl⟩
      refine ⟨z :: w, hnd.sublist (List.sublist_append_right u _), hch.right_of_append, rfl,
        ?_, ?_⟩
      · rw [getLast?_app_cons] at hlast
        rw [hlast, hc, List.getLast?_cons, hc]; rfl
      · intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (hsub a (by simp [ha]))
    · refine ⟨z :: t', List.nodup_cons.mpr ⟨hz, hnd⟩,
        hch.cons (fun y hy => (List.isChain_cons.mp h).1 y (by rw [← hhd]; exact hy)), rfl,
        by rw [List.getLast?_cons, List.getLast?_cons, hlast], ?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ha
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (hsub a ha)
lemma sep_chain {A B S : Finset V} (hS : Sep G A B S) {l : List V}
    (hch : l.IsChain G.Adj) (hA : ∃ a ∈ A, l.head? = some a)
    (hB : ∃ b ∈ B, l.getLast? = some b) : ∃ z ∈ l, z ∈ S := by
  obtain ⟨l', hnd, hch', hhd, hlast, hsub⟩ := erase_loops l hch
  obtain ⟨z, hz, hzS⟩ := hS l' ⟨hnd, hch', by rw [hhd]; exact hA, by rw [hlast]; exact hB⟩
  exact ⟨z, hsub z hz, hzS⟩
lemma abp_mono {H : SimpleGraph V} (hle : H ≤ G) {A B : Finset V} {l : List V}
    (h : ABP H A B l) : ABP G A B l :=
  ⟨h.1, h.2.1.imp (fun _ _ h => hle h), h.2.2⟩
lemma abp_reverse {A B : Finset V} {l : List V} (h : ABP G A B l) : ABP G B A l.reverse := by
  obtain ⟨hnd, hch, ⟨a, ha, hha⟩, ⟨b, hb, hlb⟩⟩ := h
  exact ⟨List.nodup_reverse.mpr hnd, List.isChain_reverse.mpr (hch.imp fun _ _ h => h.symm),
    ⟨b, hb, by simpa using hlb⟩, ⟨a, ha, by simpa using hha⟩⟩
lemma sep_reverse {A B S : Finset V} (h : Sep G A B S) : Sep G B A S := fun l hl => by
  obtain ⟨z, hz, hzS⟩ := h l.reverse (abp_reverse hl)
  exact ⟨z, List.mem_reverse.mp hz, hzS⟩
lemma exists_bad {R R' : V → V → Prop} : ∀ l : List V, l.IsChain R → ¬ l.IsChain R' →
    ∃ p u v q, l = p ++ u :: v :: q ∧ R u v ∧ ¬ R' u v
  | [], _, h' => absurd List.isChain_nil h'
  | [a], _, h' => absurd (List.isChain_singleton a) h'
  | a :: b :: t, h, h' => by
    rw [List.isChain_cons_cons] at h
    by_cases hab : R' a b
    · have : ¬ (b :: t).IsChain R' := fun hc => h' (List.isChain_cons_cons.mpr ⟨hab, hc⟩)
      obtain ⟨p, u, v, q, hl, h1, h2⟩ := exists_bad (b :: t) h.2 this
      exact ⟨a :: p, u, v, q, by rw [hl]; rfl, h1, h2⟩
    · exact ⟨[], a, b, t, rfl, h.1, hab⟩
lemma chain_del {H : SimpleGraph V} {x y : V}
    (hH : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(x, y))
    {l : List V} (hl : l.IsChain G.Adj) (hy : y ∉ l ∨ x ∉ l) : l.IsChain H.Adj :=
  hl.imp_of_mem_imp fun u v hu hv huv => (hH u v).mpr ⟨huv, fun he => by
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> subst h1 h2 <;> tauto⟩
lemma nodup_aux {p q : List V} {a b : V} (h : (p ++ a :: b :: q).Nodup) : b ∉ p ++ [a] := by
  intro hb
  rw [List.nodup_append] at h
  rcases List.mem_append.mp hb with hb | hb
  · exact h.2.2 b hb b (by simp) rfl
  · have := List.nodup_cons.mp h.2.1
    simp at hb; subst hb; exact this.1 (by simp)
lemma nodup_aux2 {p q : List V} {a b : V} (h : (p ++ a :: b :: q).Nodup) : a ∉ b :: q :=
  (List.nodup_cons.mp (List.nodup_append.mp h).2.1).1
lemma abp_of_prefix {A B : Finset V} {m l : List V} (hp : m <+: l) (hnd : l.Nodup)
    (hA : ∃ a ∈ A, l.head? = some a) (hch : m.IsChain G.Adj)
    (hB : ∃ b ∈ B, m.getLast? = some b) : ABP G A B m := by
  refine ⟨hnd.sublist hp.sublist, hch, ?_, hB⟩
  obtain ⟨t, rfl⟩ := hp
  obtain ⟨b, -, hb⟩ := hB
  obtain ⟨a, ha, hha⟩ := hA
  cases m with
  | nil => simp at hb
  | cons c m => exact ⟨a, ha, by simpa using hha⟩
lemma sep_last {A X : Finset V} : Sep G A X X := fun l hl => by
  obtain ⟨b, hb, hlb⟩ := hl.2.2.2
  exact ⟨b, List.mem_of_getLast? hlb, hb⟩
lemma sep_of_pre {H : SimpleGraph V} {A B X T : Finset V}
    (hpre : ∀ l, ABP G A B l → ∃ m, m <+: l ∧ ABP H A X m) (hT : Sep H A X T) :
    Sep G A B T := fun l hl => by
  obtain ⟨m, hm, hmX⟩ := hpre l hl
  obtain ⟨z, hz, hzT⟩ := hT m hmX
  exact ⟨z, hm.subset hz, hzT⟩
lemma sep_of_suf {H : SimpleGraph V} {A B Y T : Finset V}
    (hsuf : ∀ l, ABP G A B l → ∃ m, m <:+ l ∧ ABP H Y B m) (hT : Sep H Y B T) :
    Sep G A B T := fun l hl => by
  obtain ⟨m, hm, hmX⟩ := hsuf l hl
  obtain ⟨z, hz, hzT⟩ := hT m hmX
  exact ⟨z, hm.subset hz, hzT⟩
lemma exists_first (P : V → Prop) : ∀ l : List V, (∃ z ∈ l, P z) →
    ∃ l1 z l2, l = l1 ++ z :: l2 ∧ P z ∧ ∀ w ∈ l1, ¬ P w
  | [], h => by simp at h
  | a :: t, h => by
    by_cases ha : P a
    · exact ⟨[], a, t, rfl, ha, by simp⟩
    · obtain ⟨z, hz, hPz⟩ := h
      have : ∃ z ∈ t, P z := by
        rcases List.mem_cons.mp hz with rfl | hz
        · exact absurd hPz ha
        · exact ⟨z, hz, hPz⟩
      obtain ⟨l1, z', l2, rfl, h1, h2⟩ := exists_first P t this
      exact ⟨a :: l1, z', l2, rfl, h1, by simp [ha]; exact h2⟩
lemma exists_last (P : V → Prop) (l : List V) (h : ∃ z ∈ l, P z) :
    ∃ l1 z l2, l = l1 ++ z :: l2 ∧ P z ∧ ∀ w ∈ l2, ¬ P w := by
  obtain ⟨l1, z, l2, hl, h1, h2⟩ := exists_first P l.reverse (by simpa using h)
  refine ⟨l2.reverse, z, l1.reverse, ?_, h1, by simpa using h2⟩
  rw [← List.reverse_reverse l, hl]; simp
lemma trim {A B : Finset V} {l : List V} (hl : ABP G A B l) :
    ∃ l', ABP G A B l' ∧ (∀ x ∈ l'.tail, x ∉ A) ∧ (∀ x ∈ l'.dropLast, x ∉ B) ∧
      ∀ x ∈ l', x ∈ l := by
  obtain ⟨hnd, hch, ⟨a, ha, hha⟩, ⟨b, hb, hlb⟩⟩ := hl
  obtain ⟨l1, b', l2, rfl, hb', hl1⟩ :=
    exists_first (· ∈ B) l ⟨b, List.mem_of_getLast? hlb, hb⟩
  have hmA : ∃ z ∈ l1 ++ [b'], z ∈ A := by
    refine ⟨a, ?_, ha⟩
    rcases l1 with _ | ⟨c, l1'⟩
    · simp at hha; simp [hha]
    · simp at hha; simp [hha]
  obtain ⟨m1, a', m2, hm, ha', hm2⟩ := exists_last (· ∈ A) (l1 ++ [b']) hmA
  have hL : l1 ++ b' :: l2 = m1 ++ (a' :: m2) ++ l2 := by
    rw [← hm]; simp
  have hinf : a' :: m2 <:+: l1 ++ b' :: l2 := ⟨m1, l2, hL.symm⟩
  refine ⟨a' :: m2, ⟨hnd.sublist hinf.sublist, chain_sub hch hinf, ⟨a', ha', rfl⟩,
    ⟨b', hb', ?_⟩⟩, hm2, ?_, fun z hz => hinf.subset hz⟩
  · rw [← getLast?_app_cons m1, ← hm]; simp
  · have : l1 = m1 ++ (a' :: m2).dropLast := by
      rw [← List.dropLast_append_cons, ← hm, List.dropLast_concat]
    intro z hz
    exact hl1 z (by rw [this]; exact List.mem_append_right _ hz)
lemma trim_family {A B : Finset V} {k : ℕ} {P : Fin k → List V} (hP : ∀ i, ABP G A B (P i))
    (hd : ∀ i j, i ≠ j → ∀ x ∈ P i, x ∉ P j) :
    ∃ P' : Fin k → List V, (∀ i, ABP G A B (P' i) ∧ (∀ x ∈ (P' i).tail, x ∉ A) ∧
        (∀ x ∈ (P' i).dropLast, x ∉ B)) ∧ ∀ i j, i ≠ j → ∀ x ∈ P' i, x ∉ P' j := by
  choose P' h1 h2 h3 h4 using fun i => trim (hP i)
  exact ⟨P', fun i => ⟨h1 i, h2 i, h3 i⟩,
    fun i j hij x hx hx' => hd i j hij x (h4 i x hx) (h4 j x hx')⟩
lemma base {A B : Finset V} {k : ℕ} (hE : ∀ u v, ¬ G.Adj u v)
    (hsep : ∀ S, Sep G A B S → k ≤ S.card) :
    ∃ P : Fin k → List V, (∀ i, ABP G A B (P i)) ∧ ∀ i j, i ≠ j → ∀ x ∈ P i, x ∉ P j := by
  have hk : k ≤ (A ∩ B).card := hsep _ (fun l hl => by
    obtain ⟨hnd, hch, ⟨a, ha, hha⟩, ⟨b, hb, hlb⟩⟩ := hl
    obtain ⟨t, rfl⟩ := List.head?_eq_some_iff.mp hha
    cases t with
    | nil =>
      simp at hlb
      exact ⟨a, by simp, Finset.mem_inter.mpr ⟨ha, by rw [hlb]; exact hb⟩⟩
    | cons c t => exact absurd (List.isChain_cons_cons.mp hch).1 (hE a c))
  let e := (A ∩ B).equivFin.symm
  refine ⟨fun i => [(e (Fin.castLE hk i)).1], fun i => ⟨List.nodup_singleton _,
    List.isChain_singleton _, ⟨_, (Finset.mem_inter.mp (e _).2).1, rfl⟩,
    ⟨_, (Finset.mem_inter.mp (e _).2).2, rfl⟩⟩, ?_⟩
  intro i j hij x hx hx'
  simp only [List.mem_singleton] at hx hx'
  exact hij (Fin.castLE_injective hk (e.injective (Subtype.ext (hx.symm.trans hx'))))
lemma pre {H : SimpleGraph V} {x y : V}
    (hH : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(x, y))
    {A B S : Finset V} (hSH : Sep H A B S) {q : List V} (hq : (y :: q).IsChain H.Adj)
    (hqB : ∃ b ∈ B, (y :: q).getLast? = some b) (hqS : ∀ z ∈ y :: q, z ∉ S)
    {l : List V} (hl : ABP G A B l) : ∃ m, m <+: l ∧ ABP H A (insert x S) m := by
  obtain ⟨hnd, hch, hA, hB⟩ := hl
  have key : ∀ l1, l1 <+: l → l1.IsChain H.Adj → (∃ z ∈ l1, z ∈ S) →
      ∃ m, m <+: l ∧ ABP H A (insert x S) m := by
    rintro l1 hp hc ⟨z, hz, hzS⟩
    obtain ⟨s, t, rfl⟩ := List.append_of_mem hz
    have hp' : s ++ [z] <+: s ++ z :: t := ⟨t, by simp⟩
    exact ⟨s ++ [z], hp'.trans hp, abp_of_prefix (hp'.trans hp) hnd hA (chain_pre hc hp')
      ⟨z, Finset.mem_insert_of_mem hzS, by simp⟩⟩
  by_cases hl : l.IsChain H.Adj
  · exact key l (List.prefix_refl l) hl (sep_chain hSH hl hA hB)
  · obtain ⟨p, u, v, q', rfl, huv, hnuv⟩ := exists_bad l hch hl
    have he : s(u, v) = s(x, y) := by
      by_contra hne; exact hnuv ((hH u v).mpr ⟨huv, hne⟩)
    have hp : p ++ [u] <+: p ++ u :: v :: q' := ⟨v :: q', by simp⟩
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1 h2
      exact ⟨p ++ [u], hp, abp_of_prefix hp hnd hA
        (chain_del hH (chain_pre hch hp) (Or.inl (nodup_aux hnd)))
        ⟨u, Finset.mem_insert_self _ _, by simp⟩⟩
    · subst h1 h2
      have hc : (p ++ [u]).IsChain H.Adj :=
        chain_del hH (chain_pre hch hp) (Or.inr (nodup_aux hnd))
      by_cases hm : ∃ z ∈ p ++ [u], z ∈ S
      · exact key _ hp hc hm
      · exfalso
        push_neg at hm
        obtain ⟨z, hz, hzS⟩ := sep_chain hSH (l := p ++ u :: q)
          (List.isChain_split.mpr ⟨hc, hq⟩) (by simpa using hA)
          (by rw [getLast?_app_cons]; exact hqB)
        rcases List.mem_append.mp hz with hz | hz
        · exact hm z (List.mem_append_left _ hz) hzS
        · exact hqS z hz hzS
lemma suf {H : SimpleGraph V} {x y : V}
    (hH : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(x, y))
    {A B S : Finset V} (hSH : Sep H A B S) {p : List V} (hp : (p ++ [x]).IsChain H.Adj)
    (hpA : ∃ a ∈ A, (p ++ [x]).head? = some a) (hpS : ∀ z ∈ p ++ [x], z ∉ S)
    {l : List V} (hl : ABP G A B l) : ∃ m, m <:+ l ∧ ABP H (insert y S) B m := by
  have hH' : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(y, x) := by
    intro u v; rw [Sym2.eq_swap (a := y)]; exact hH u v
  have e : x :: p.reverse = (p ++ [x]).reverse := by simp
  obtain ⟨m, hm, hmA⟩ := pre (x := y) (y := x) (q := p.reverse) hH' (sep_reverse hSH)
    (by rw [e]; exact List.isChain_reverse.mpr (hp.imp fun _ _ h => h.symm))
    (by rw [e, List.getLast?_reverse]; exact hpA)
    (fun z hz => hpS z (by rw [e] at hz; simp at hz ⊢; tauto)) (abp_reverse hl)
  exact ⟨m.reverse, List.reverse_prefix.mp (by simpa using hm), by simpa using abp_reverse hmA⟩
lemma mem_tail_of {c d : List V} {v z : V} (hz : z ∈ d) : z ∈ (c ++ v :: d).tail := by
  cases c <;> simp [hz]
lemma glue {H : SimpleGraph V} (hle : H ≤ G) {x y : V} (hxy : G.Adj x y) {A B S : Finset V}
    (hx : x ∉ S) (hy : y ∉ S) (hSH : Sep H A B S) {k : ℕ} (hk : S.card + 1 = k)
    {P Q : Fin k → List V}
    (hP : ∀ i, ABP H A (insert x S) (P i) ∧ ∀ z ∈ (P i).dropLast, z ∉ insert x S)
    (hPd : ∀ i j, i ≠ j → ∀ z ∈ P i, z ∉ P j)
    (hQ : ∀ j, ABP H (insert y S) B (Q j) ∧ ∀ z ∈ (Q j).tail, z ∉ insert y S)
    (hQd : ∀ i j, i ≠ j → ∀ z ∈ Q i, z ∉ Q j) :
    ∃ R : Fin k → List V, (∀ i, ABP G A B (R i)) ∧ ∀ i j, i ≠ j → ∀ z ∈ R i, z ∉ R j := by
  have hxy' : x ≠ y := G.ne_of_adj hxy
  choose lt hltX hlt using fun i => (hP i).1.2.2.2
  choose hd hhdY hhd using fun j => (hQ j).1.2.2.1
  have hPdec : ∀ i, ∃ a, P i = a ++ [lt i] := fun i => List.getLast?_eq_some_iff.mp (hlt i)
  have hQdec : ∀ j, ∃ d, Q j = hd j :: d := fun j => List.head?_eq_some_iff.mp (hhd j)
  have hltmem : ∀ i, lt i ∈ P i := fun i => List.mem_of_getLast? (hlt i)
  have hhdmem : ∀ j, hd j ∈ Q j := fun j => List.mem_of_head? (hhd j)
  have hPS : ∀ i, ∀ z ∈ P i, z ∈ S → z = lt i := by
    intro i z hz hzS
    obtain ⟨a, ha⟩ := hPdec i
    rw [ha] at hz
    rcases List.mem_append.mp hz with h | h
    · exact absurd (Finset.mem_insert_of_mem hzS)
        ((hP i).2 z (by rw [ha, List.dropLast_concat]; exact h))
    · simpa using h
  have hQS : ∀ j, ∀ z ∈ Q j, z ∈ S → z = hd j := by
    intro j z hz hzS
    obtain ⟨d, hd'⟩ := hQdec j
    rw [hd'] at hz
    rcases List.mem_cons.mp hz with h | h
    · exact h
    · exact absurd (Finset.mem_insert_of_mem hzS) ((hQ j).2 z (by rw [hd']; exact h))
  have meet : ∀ i j, ∀ v ∈ P i, v ∈ Q j → v ∈ S := by
    intro i j v hvP hvQ
    by_contra hvS
    obtain ⟨a, b, hab⟩ := List.append_of_mem hvP
    obtain ⟨c, d, hcd⟩ := List.append_of_mem hvQ
    have h1 : (a ++ [v]).IsChain H.Adj := chain_pre (hP i).1.2.1 ⟨b, by rw [hab]; simp⟩
    have h2 : (v :: d).IsChain H.Adj := (hQ j).1.2.1.suffix ⟨c, hcd.symm⟩
    obtain ⟨a0, ha0, hha0⟩ := (hP i).1.2.2.1
    obtain ⟨b0, hb0, hlb0⟩ := (hQ j).1.2.2.2
    obtain ⟨z, hz, hzS⟩ := sep_chain hSH (List.isChain_split.mpr ⟨h1, h2⟩)
      ⟨a0, ha0, by rw [hab] at hha0; simpa using hha0⟩
      ⟨b0, hb0, by rw [hcd, getLast?_app_cons] at hlb0; rw [getLast?_app_cons]; exact hlb0⟩
    rcases List.mem_append.mp hz with hz | hz
    · exact (hP i).2 z (by rw [hab, List.dropLast_append_cons]; exact List.mem_append_left _ hz)
        (Finset.mem_insert_of_mem hzS)
    · rcases List.mem_cons.mp hz with rfl | hz
      · exact hvS hzS
      · exact (hQ j).2 z (by rw [hcd]; exact mem_tail_of hz) (Finset.mem_insert_of_mem hzS)
  have hdinj : Function.Injective hd := by
    intro j j' h
    by_contra hne
    exact hQd j j' hne (hd j) (hhdmem j) (h ▸ hhdmem j')
  have hY : (insert y S).card = k := by rw [Finset.card_insert_of_notMem hy, hk]
  have hsurj : ∀ w ∈ insert y S, ∃ j, hd j = w := by
    have himg : Finset.univ.image hd = insert y S := by
      apply Finset.eq_of_subset_of_card_le
      · intro w hw
        obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hw
        exact hhdY j
      · rw [Finset.card_image_of_injective _ hdinj, Finset.card_univ, Fintype.card_fin, hY]
    intro w hw
    rw [← himg] at hw
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hw
    exact ⟨j, hj⟩
  obtain ⟨f, hf⟩ : ∃ f : V → V, f = fun v => if v = x then y else v := ⟨_, rfl⟩
  have hfx : f x = y := by simp [hf]
  have hfS : ∀ v, v ≠ x → f v = v := by intro v hv; simp [hf, hv]
  have hltS : ∀ i, lt i ≠ x → lt i ∈ S := fun i h =>
    (Finset.mem_insert.mp (hltX i)).resolve_left h
  have hfY : ∀ i, f (lt i) ∈ insert y S := by
    intro i
    by_cases h : lt i = x
    · rw [h, hfx]; exact Finset.mem_insert_self _ _
    · rw [hfS _ h]; exact Finset.mem_insert_of_mem (hltS i h)
  choose σ hσ using fun i => hsurj _ (hfY i)
  have hσinj : Function.Injective σ := by
    intro i i' h
    have h1 : f (lt i) = f (lt i') := by rw [← hσ i, ← hσ i', h]
    have h2 : lt i = lt i' := by
      by_cases ha : lt i = x <;> by_cases hb : lt i' = x
      · rw [ha, hb]
      · rw [ha, hfx, hfS _ hb] at h1; exact absurd (h1 ▸ hltS i' hb) hy
      · rw [hb, hfx, hfS _ ha] at h1; exact absurd (h1.symm ▸ hltS i ha) hy
      · rwa [hfS _ ha, hfS _ hb] at h1
    by_contra hne
    exact hPd i i' hne _ (hltmem i) (h2 ▸ hltmem i')
  obtain ⟨R, hR⟩ : ∃ R : Fin k → List V, R = fun i =>
      if lt i = x then P i ++ Q (σ i) else P i ++ (Q (σ i)).tail := ⟨_, rfl⟩
  have memR : ∀ i z, z ∈ R i → z ∈ P i ∨ z ∈ Q (σ i) := by
    intro i z hz
    rw [hR] at hz
    simp only at hz
    split_ifs at hz
    · exact List.mem_append.mp hz
    · rcases List.mem_append.mp hz with h | h
      · exact Or.inl h
      · exact Or.inr (List.mem_of_mem_tail h)
  have hRabp : ∀ i, ABP G A B (R i) := by
    intro i
    obtain ⟨a, ha⟩ := hPdec i
    obtain ⟨d, hd'⟩ := hQdec (σ i)
    have hPch : (P i).IsChain G.Adj := (hP i).1.2.1.imp fun _ _ h => hle h
    have hQch : (Q (σ i)).IsChain G.Adj := (hQ (σ i)).1.2.1.imp fun _ _ h => hle h
    have hPnd := (hP i).1.1
    have hQnd := (hQ (σ i)).1.1
    obtain ⟨a0, ha0, hha0⟩ := (hP i).1.2.2.1
    obtain ⟨b0, hb0, hlb0⟩ := (hQ (σ i)).1.2.2.2
    rw [ha] at hPch hPnd hha0
    rw [hd'] at hQch hQnd hlb0
    by_cases hx' : lt i = x
    · have hdy : hd (σ i) = y := by rw [hσ i, hx', hfx]
      have hRi : R i = a ++ [lt i] ++ hd (σ i) :: d := by
        rw [hR]; simp only [if_pos hx']; rw [ha, hd']
      rw [hRi]
      refine ⟨?_, ?_, ⟨a0, ha0, by simpa using hha0⟩,
        ⟨b0, hb0, by rw [getLast?_app_cons]; exact hlb0⟩⟩
      · rw [List.nodup_append]
        refine ⟨hPnd, hQnd, ?_⟩
        rintro z hz z' hz' rfl
        have hzS := meet i (σ i) z (by rw [ha]; exact hz) (by rw [hd']; exact hz')
        have := hPS i z (by rw [ha]; exact hz) hzS
        exact hx (by rw [← hx', ← this]; exact hzS)
      · refine hPch.append hQch ?_
        intro u hu w hw
        simp at hu hw
        rw [← hu, ← hw, hx', hdy]; exact hxy
    · have hdl : hd (σ i) = lt i := by rw [hσ i, hfS _ hx']
      have hRi : R i = a ++ lt i :: d := by
        rw [hR]; simp only [if_neg hx']; rw [ha, hd', hdl]; simp
      rw [hdl] at hQch hQnd hlb0
      rw [hRi]
      refine ⟨?_, List.isChain_split.mpr ⟨hPch, hQch⟩, ⟨a0, ha0, by simpa using hha0⟩,
        ⟨b0, hb0, by rw [getLast?_app_cons]; exact hlb0⟩⟩
      have e : a ++ lt i :: d = (a ++ [lt i]) ++ d := by simp
      rw [e, List.nodup_append]
      refine ⟨hPnd, (List.nodup_cons.mp hQnd).2, ?_⟩
      rintro z hz z' hz' rfl
      have hzQ : z ∈ Q (σ i) := by rw [hd', hdl]; exact List.mem_cons_of_mem _ hz'
      have hzS := meet i (σ i) z (by rw [ha]; exact hz) hzQ
      have := hQS (σ i) z hzQ hzS
      rw [hdl] at this
      exact (List.nodup_cons.mp hQnd).1 (this ▸ hz')
  refine ⟨R, hRabp, ?_⟩
  have cross : ∀ i i', i ≠ i' → ∀ z ∈ P i, z ∉ Q (σ i') := by
    intro i i' hii' z h1 h2
    have hzS := meet i (σ i') z h1 h2
    have e1 := hPS i z h1 hzS
    have e2 := hQS (σ i') z h2 hzS
    have hne : lt i ≠ x := fun h => hx (by rw [← h, ← e1]; exact hzS)
    have : hd (σ i) = hd (σ i') := by rw [hσ i, hfS _ hne, ← e1, e2]
    exact hii' (hσinj (hdinj this))
  intro i i' hii' z hz hz'
  rcases memR i z hz with h1 | h1 <;> rcases memR i' z hz' with h2 | h2
  · exact hPd i i' hii' z h1 h2
  · exact cross i i' hii' z h1 h2
  · exact cross i' i (Ne.symm hii') z h2 h1
  · exact hQd (σ i) (σ i') (fun h => hii' (hσinj h)) z h1 h2
lemma step {H : SimpleGraph V} {x y : V} (hle : H ≤ G) (hxy : G.Adj x y)
    (hH : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(x, y))
    (ih : ∀ (A B : Finset V) (k : ℕ), (∀ S, Sep H A B S → k ≤ S.card) →
      ∃ P : Fin k → List V, (∀ i, ABP H A B (P i)) ∧ ∀ i j, i ≠ j → ∀ z ∈ P i, z ∉ P j)
    {A B : Finset V} {k : ℕ} (hsep : ∀ S, Sep G A B S → k ≤ S.card)
    {S : Finset V} (hSH : Sep H A B S) (hSk : S.card < k)
    {p q : List V} (hl0 : ABP G A B (p ++ x :: y :: q)) (hav : ∀ z ∈ p ++ x :: y :: q, z ∉ S) :
    ∃ P : Fin k → List V, (∀ i, ABP G A B (P i)) ∧ ∀ i j, i ≠ j → ∀ z ∈ P i, z ∉ P j := by
  obtain ⟨hnd, hch, hA, hB⟩ := hl0
  have hx : x ∉ S := hav x (by simp)
  have hy : y ∉ S := hav y (by simp)
  have hp : p ++ [x] <+: p ++ x :: y :: q := ⟨y :: q, by simp⟩
  have hs : y :: q <:+ p ++ x :: y :: q := ⟨p ++ [x], by simp⟩
  have hpch : (p ++ [x]).IsChain H.Adj :=
    chain_del hH (chain_pre hch hp) (Or.inl (nodup_aux hnd))
  have hqch : (y :: q).IsChain H.Adj :=
    chain_del hH (hch.suffix hs) (Or.inr (nodup_aux2 hnd))
  have hpre : ∀ l, ABP G A B l → ∃ m, m <+: l ∧ ABP H A (insert x S) m := fun l hl =>
    pre hH hSH hqch (by rw [← getLast?_app_cons p]; simpa using hB)
      (fun z hz => hav z (by simp at hz ⊢; tauto)) hl
  have hsuf : ∀ l, ABP G A B l → ∃ m, m <:+ l ∧ ABP H (insert y S) B m := fun l hl =>
    suf hH hSH hpch (by simpa using hA) (fun z hz => hav z (by simp at hz ⊢; tauto)) hl
  have hXk : k ≤ (insert x S).card := hsep _ (sep_of_pre hpre sep_last)
  have hk : S.card + 1 = k := by rw [Finset.card_insert_of_notMem hx] at hXk; omega
  obtain ⟨P, hP, hPd⟩ := ih A (insert x S) k (fun T hT => hsep T (sep_of_pre hpre hT))
  obtain ⟨Q, hQ, hQd⟩ := ih (insert y S) B k (fun T hT => hsep T (sep_of_suf hsuf hT))
  obtain ⟨P', hP', hP'd⟩ := trim_family hP hPd
  obtain ⟨Q', hQ', hQ'd⟩ := trim_family hQ hQd
  exact glue hle hxy hx hy hSH hk (fun i => ⟨(hP' i).1, (hP' i).2.2⟩) hP'd
    (fun j => ⟨(hQ' j).1, (hQ' j).2.1⟩) hQ'd
theorem menger_aux (G : SimpleGraph V) : ∀ (A B : Finset V) (k : ℕ),
    (∀ S, Sep G A B S → k ≤ S.card) →
    ∃ P : Fin k → List V, (∀ i, ABP G A B (P i)) ∧ ∀ i j, i ≠ j → ∀ x ∈ P i, x ∉ P j := by
  induction G using WellFoundedLT.induction with
  | _ G ih =>
  intro A B k hsep
  by_cases hE : ∃ x y, G.Adj x y
  swap
  · push_neg at hE; exact base hE hsep
  obtain ⟨x, y, hxy⟩ := hE
  obtain ⟨H, hHdef⟩ : ∃ H, H = G.deleteEdges {s(x, y)} := ⟨_, rfl⟩
  have hH : ∀ u v, H.Adj u v ↔ G.Adj u v ∧ s(u, v) ≠ s(x, y) := by
    intro u v; rw [hHdef, deleteEdges_adj]; simp
  have hle : H ≤ G := hHdef ▸ deleteEdges_le _
  have hlt : H < G := lt_of_le_of_ne hle (fun h => ((hH x y).mp (by rw [h]; exact hxy)).2 rfl)
  by_cases hc : ∀ S, Sep H A B S → k ≤ S.card
  · obtain ⟨P, hP, hPd⟩ := ih H hlt A B k hc
    exact ⟨P, fun i => abp_mono hle (hP i), hPd⟩
  · push_neg at hc
    obtain ⟨S, hSH, hSk⟩ := hc
    have hnG : ¬ Sep G A B S := fun h => absurd (hsep S h) (by omega)
    simp only [Sep, not_forall, not_exists, not_and] at hnG
    obtain ⟨l0, hl0, hav⟩ := hnG
    have hnH : ¬ l0.IsChain H.Adj := fun hc => by
      obtain ⟨z, hz, hzS⟩ := hSH l0 ⟨hl0.1, hc, hl0.2.2⟩; exact hav z hz hzS
    obtain ⟨p, u, v, q, rfl, huv, hnuv⟩ := exists_bad l0 hl0.2.1 hnH
    have he : s(u, v) = s(x, y) := by
      by_contra hne; exact hnuv ((hH u v).mpr ⟨huv, hne⟩)
    rcases Sym2.eq_iff.mp he with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rw [h1, h2] at hl0 hav
    · exact step hle hxy hH (ih H hlt) hsep hSH hSk hl0 hav
    · exact step hle hxy.symm (fun a b => by rw [hH a b, Sym2.eq_swap (a := x) (b := y)])
        (ih H hlt) hsep hSH hSk hl0 hav
theorem menger [DecidableRel G.Adj] (A B : Finset V) (k : ℕ)
    (hsep : ∀ S : Finset V, (∀ l, ABP G A B l → ∃ x ∈ l, x ∈ S) → k ≤ S.card) :
    ∃ P : Fin k → List V, (∀ i, ABP G A B (P i)) ∧
      ∀ i j, i ≠ j → ∀ x ∈ P i, x ∉ P j := by
  exact menger_aux G A B k hsep
theorem menger_trim [DecidableRel G.Adj] (A B : Finset V) (k : ℕ)
    (hsep : ∀ S : Finset V, (∀ l, ABP G A B l → ∃ x ∈ l, x ∈ S) → k ≤ S.card) :
    ∃ P : Fin k → List V, (∀ i, ABP G A B (P i) ∧ (∀ x ∈ (P i).tail, x ∉ A) ∧
        (∀ x ∈ (P i).dropLast, x ∉ B)) ∧
      ∀ i j, i ≠ j → ∀ x ∈ P i, x ∉ P j := by
  obtain ⟨P, hP, hPd⟩ := menger A B k hsep
  exact trim_family hP hPd
def VL (G : SimpleGraph V) (H : Finset V) (P : List V) : Prop :=
  P.Nodup ∧ P.IsChain G.Adj ∧ ∀ z ∈ P, z ∈ H
def CL (G : SimpleGraph V) (l : List V) : Prop :=
  l.IsChain G.Adj ∧ ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, G.Adj x y
lemma walk_of_chain : ∀ (l : List V) (x : V), (x :: l).IsChain G.Adj →
    ∃ y, ∃ p : G.Walk x y, p.support = x :: l ∧ (x :: l).getLast? = some y
  | [], x, _ => ⟨x, Walk.nil, rfl, rfl⟩
  | z :: l, x, h => by
    rw [List.isChain_cons_cons] at h
    obtain ⟨y, p, hp, hl⟩ := walk_of_chain l z h.2
    exact ⟨y, Walk.cons h.1 p, by simp [hp], by simpa using hl⟩
lemma start_edge {u v w : V} (p : G.Walk u v) (hp : p.IsPath) (h : s(u, w) ∈ p.edges) :
    w = p.getVert 1 := by
  cases p with
  | nil => simp at h
  | @cons _ x _ hadj q =>
    rw [Walk.edges_cons, List.mem_cons] at h
    rw [Walk.cons_isPath_iff] at hp
    rcases h with h | h
    · rcases Sym2.eq_iff.mp h with ⟨-, h2⟩ | ⟨h1, -⟩
      · simp [h2]
      · exact absurd h1 (G.ne_of_adj hadj)
    · exact absurd (q.fst_mem_support_of_mem_edges h) hp.2
lemma cycle_of_CL (l : List V) (hnd : l.Nodup) (hc : CL G l) (h3 : 3 ≤ l.length) :
    ∃ a, ∃ w : G.Walk a a, w.IsCycle ∧ w.length = l.length := by
  obtain _ | ⟨x, t⟩ := l
  · simp at h3
  obtain ⟨y, p, hp, hl⟩ := walk_of_chain t x hc.1
  have hyx : G.Adj y x := hc.2 y hl x rfl
  have hpath : p.IsPath := Walk.IsPath.mk' (by rw [hp]; exact hnd)
  have hlen : p.length + 1 = (x :: t).length := by
    rw [← hp, Walk.length_support]
  refine ⟨y, Walk.cons hyx p, ?_, by simp [hlen]⟩
  rw [Walk.cons_isCycle_iff]
  refine ⟨hpath, fun he => ?_⟩
  rw [Sym2.eq_swap] at he
  have h1 := start_edge p hpath he
  have hy : p.getVert p.length = y := p.getVert_length
  have := hpath.getVert_injOn (show 1 ∈ {i | i ≤ p.length} by simp; omega)
    (show p.length ∈ {i | i ≤ p.length} by simp) (by rw [hy, ← h1])
  omega
lemma cycle_length_le {a : V} (w : G.Walk a a) (hw : w.IsCycle) : w.length ≤ Fintype.card V := by
  have h1 := hw.support_nodup
  have h2 : w.support.tail.length = w.length := by
    rw [List.length_tail, Walk.length_support]; simp
  rw [← h2]
  exact h1.length_le_card
lemma le_circumference [DecidableRel G.Adj] {a : V} (w : G.Walk a a) (hw : w.IsCycle) :
    w.length ≤ G.circumference := by
  apply le_csSup
  · exact ⟨Fintype.card V, by rintro m ⟨b, w', hw', rfl⟩; exact cycle_length_le w' hw'⟩
  · exact ⟨a, w, hw, rfl⟩
structure Cy (G : SimpleGraph V) (c : ℕ) (f : ℕ → V) : Prop where
  three : 3 ≤ c
  per : ∀ t, f (t + c) = f t
  adj : ∀ t, G.Adj (f t) (f (t + 1))
  inj : ∀ i j, i < c → j < c → f i = f j → i = j
  long : ∀ l : List V, l.Nodup → CL G l → l.length ≤ c
variable {c : ℕ} {f : ℕ → V}
lemma Cy.mod (hD : Cy G c f) (t : ℕ) : f t = f (t % c) := by
  conv_lhs => rw [← Nat.mod_add_div t c]
  induction t / c with
  | zero => simp
  | succ k ih => rw [Nat.mul_succ, ← Nat.add_assoc, hD.per, ih]
lemma Cy.per' (hD : Cy G c f) (t k : ℕ) : f (t + c * k) = f t := by
  rw [hD.mod, Nat.add_mul_mod_self_left, ← hD.mod]
lemma Cy.eq_iff (hD : Cy G c f) (i j : ℕ) : f i = f j ↔ i % c = j % c := by
  have hc : 0 < c := by have := hD.three; omega
  constructor
  · intro h
    rw [hD.mod i, hD.mod j] at h
    exact hD.inj _ _ (Nat.mod_lt _ hc) (Nat.mod_lt _ hc) h
  · intro h
    rw [hD.mod i, hD.mod j, h]
lemma Cy.ne_of_window (hD : Cy G c f) {b i j : ℕ} (hi1 : b ≤ i) (hi2 : i < b + c) (hj1 : b ≤ j)
    (hj2 : j < b + c) (hij : i ≠ j) : f i ≠ f j := by
  intro h
  rw [hD.eq_iff] at h
  have hc : 0 < c := by have := hD.three; omega
  rcases Nat.lt_or_ge i j with hl | hl
  · have : (j - i) % c = 0 := by
      have := Nat.sub_mod_eq_zero_of_mod_eq h.symm
      exact this
    have h1 : 0 < j - i := by omega
    have h2 : j - i < c := by omega
    rw [Nat.mod_eq_of_lt h2] at this
    omega
  · have : (i - j) % c = 0 := Nat.sub_mod_eq_zero_of_mod_eq h
    have h1 : 0 < i - j := by omega
    have h2 : i - j < c := by omega
    rw [Nat.mod_eq_of_lt h2] at this
    omega
def up (f : ℕ → V) (s k : ℕ) : List V := (List.range' s k).map f
def dn (f : ℕ → V) (s k : ℕ) : List V := ((List.range' s k).map f).reverse
lemma chain_up (hD : Cy G c f) (s k : ℕ) : (up f s k).IsChain G.Adj := by
  induction k generalizing s with
  | zero => simp [up]
  | succ k ih =>
    cases k with
    | zero => simp [up]
    | succ k =>
      have := ih (s + 1)
      simp only [up, List.range'_succ, List.map_cons] at this ⊢
      exact List.IsChain.cons_cons (hD.adj s) this
lemma chain_dn (hD : Cy G c f) (s k : ℕ) : (dn f s k).IsChain G.Adj := by
  unfold dn
  rw [List.isChain_reverse]
  exact (chain_up hD s k).imp (fun _ _ h => h.symm)
lemma up_head (s k : ℕ) : (up f s (k + 1)).head? = some (f s) := by
  simp [up, List.range'_succ]
lemma up_last (s k : ℕ) : (up f s (k + 1)).getLast? = some (f (s + k)) := by
  simp [up, List.getLast?_map, List.getLast?_range']
lemma dn_head (s k : ℕ) : (dn f s (k + 1)).head? = some (f (s + k)) := by
  simp [dn, List.head?_reverse, List.getLast?_map, List.getLast?_range']
lemma dn_last (s k : ℕ) : (dn f s (k + 1)).getLast? = some (f s) := by
  simp [dn, List.getLast?_reverse, List.range'_succ]
lemma nodup_map_window (hD : Cy G c f) (I : List ℕ) (b : ℕ) (hI : ∀ i ∈ I, b ≤ i ∧ i < b + c)
    (hnd : I.Nodup) : (I.map f).Nodup := by
  rw [List.nodup_map_iff_inj_on hnd]
  intro i hi j hj hij
  by_contra hne
  exact hD.ne_of_window (hI i hi).1 (hI i hi).2 (hI j hj).1 (hI j hj).2 hne hij
lemma reroute (hD : Cy G c f) (l O : List V) (I : List ℕ) (b : ℕ) (hperm : l.Perm (O ++ I.map f))
    (hcl : CL G l) (hO : O.Nodup) (hOff : ∀ x ∈ O, ∀ t, f t ≠ x)
    (hI : ∀ i ∈ I, b ≤ i ∧ i < b + c) (hInd : I.Nodup) : O.length + I.length ≤ c := by
  have hnd : l.Nodup := by
    rw [hperm.nodup_iff, List.nodup_append]
    refine ⟨hO, nodup_map_window hD I b hI hInd, ?_⟩
    intro x hx y hy hxy
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hy
    exact hOff x hx i hxy.symm
  have := hD.long l hnd hcl
  rw [hperm.length_eq, List.length_append, List.length_map] at this
  exact this
structure OffL (G : SimpleGraph V) (f : ℕ → V) (X : List V) : Prop where
  ne : X ≠ []
  nd : X.Nodup
  ch : X.IsChain G.Adj
  off : ∀ x ∈ X, ∀ t, f t ≠ x
lemma R1 (hD : Cy G c f) {X : List V} (hX : OffL G f X) {b j : ℕ} (hj : 1 ≤ j) (hjc : j ≤ c)
    (h1 : ∀ z ∈ X.head?, G.Adj (f b) z) (h2 : ∀ z ∈ X.getLast?, G.Adj z (f (b + j))) :
    X.length + 1 ≤ j := by
  obtain ⟨k, hk⟩ : ∃ k, c - j = k := ⟨_, rfl⟩
  have key := reroute hD (X ++ up f (b + j) (k + 1)) X (List.range' (b + j) (k + 1)) (b + 1)
    (by simp [up]) ?_ hX.nd hX.off ?_ List.nodup_range'
  · simp at key; omega
  · refine ⟨List.IsChain.append hX.ch (chain_up hD _ _) ?_, ?_⟩
    · intro x hx y hy
      rw [up_head] at hy; cases hy; exact h2 x hx
    · intro x hx y hy
      rw [List.getLast?_append, up_last] at hx
      simp at hx; subst hx
      have hb : f (b + j + k) = f b := by
        rw [show b + j + k = b + c by omega, hD.per]
      rw [hb]
      rw [List.head?_append] at hy
      obtain ⟨x0, l0, hx0⟩ := List.ne_nil_iff_exists_cons.mp hX.ne
      rw [hx0] at hy h1; simp at hy h1; subst hy; exact h1
  · intro i hi; simp at hi; omega
lemma OffL.head (hX : OffL G f X) : ∃ x0, X.head? = some x0 := by
  obtain ⟨x0, l0, rfl⟩ := List.ne_nil_iff_exists_cons.mp hX.ne
  exact ⟨x0, rfl⟩
lemma closing_aux {l : List V} {X : List V} (hX : OffL G f X) {v : V}
    (hl : l.getLast? = some v) (h1 : ∀ z ∈ X.head?, G.Adj v z) :
    ∀ x ∈ (X ++ l).getLast?, ∀ y ∈ (X ++ l).head?, G.Adj x y := by
  intro x hx y hy
  rw [List.getLast?_append, hl] at hx
  simp at hx; subst hx
  obtain ⟨x0, hx0⟩ := hX.head
  rw [List.head?_append, hx0] at hy
  simp at hy; subst hy
  exact h1 _ hx0
lemma R3 (hD : Cy G c f) {X : List V} (hX : OffL G f X) {b j p q : ℕ} (hj : 1 ≤ j)
    (hjp : j + 1 ≤ p) (hpq : p < q) (hqc : q ≤ c)
    (h1 : ∀ z ∈ X.head?, G.Adj (f b) z) (h2 : ∀ z ∈ X.getLast?, G.Adj z (f (b + j)))
    (h3 : G.Adj (f (b + 1)) (f (b + p))) (h4 : G.Adj (f (b + j + 1)) (f (b + q))) :
    X.length + p + 1 ≤ q := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨d, hd⟩ : ∃ d, p - (j' + 1) = d + 1 := ⟨p - j' - 2, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, c - q = k := ⟨_, rfl⟩
  have key := reroute hD
    (X ++ (dn f (b + 1) (j' + 1) ++ (dn f (b + j' + 1 + 1) (d + 1) ++ up f (b + q) (k + 1)))) X
    ((List.range' (b + 1) (j' + 1)).reverse ++ ((List.range' (b + j' + 1 + 1) (d + 1)).reverse
      ++ List.range' (b + q) (k + 1))) (b + 1)
    (by simp [up, dn, List.map_reverse]) ?_ hX.nd hX.off ?_ ?_
  · simp at key; omega
  · have hbc : f (b + q + k) = f b := by rw [show b + q + k = b + c by omega, hD.per]
    refine ⟨?_, closing_aux hX (by simp [up_last, hbc]) h1⟩
    refine List.IsChain.append hX.ch ?_ ?_
    · refine List.IsChain.append (chain_dn hD _ _) ?_ ?_
      · refine List.IsChain.append (chain_dn hD _ _) (chain_up hD _ _) ?_
        intro x hx y hy
        rw [dn_last] at hx; rw [up_head] at hy; cases hx; cases hy
        exact h4
      · intro x hx y hy
        rw [dn_last] at hx; cases hx
        rw [List.head?_append, dn_head] at hy; simp at hy; subst hy
        rw [show b + j' + 1 + 1 + d = b + p by omega]; exact h3
    · intro x hx y hy
      rw [List.head?_append, dn_head] at hy; simp at hy; subst hy
      rw [show b + 1 + j' = b + (j' + 1) by omega]; exact h2 x hx
  · intro i hi; simp at hi; omega
  · simp only [List.nodup_append, List.nodup_reverse, List.mem_reverse, List.mem_range'_1,
      List.mem_append]
    refine ⟨List.nodup_range', ⟨List.nodup_range', List.nodup_range', ?_⟩, ?_⟩
    · intro a ha b' hb'; omega
    · intro a ha b' hb'; omega
lemma R22 (hD : Cy G c f) {X : List V} (hX : OffL G f X) {r : V} (hr : ∀ t, f t ≠ r)
    (hrX : r ∉ X) {b j : ℕ} (hj : 1 ≤ j) (hjc : j + 1 ≤ c)
    (h1 : ∀ z ∈ X.head?, G.Adj (f b) z) (h2 : ∀ z ∈ X.getLast?, G.Adj z (f (b + j)))
    (h3 : G.Adj (f (b + 1)) r) (h4 : G.Adj r (f (b + j + 1))) : False := by
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  obtain ⟨k, hk⟩ : ∃ k, c - (j' + 1) - 1 = k := ⟨_, rfl⟩
  have key := reroute hD
    (X ++ (dn f (b + 1) (j' + 1) ++ (r :: up f (b + j' + 1 + 1) (k + 1)))) (X ++ [r])
    ((List.range' (b + 1) (j' + 1)).reverse ++ List.range' (b + j' + 1 + 1) (k + 1)) (b + 1)
    ?_ ?_ ?_ ?_ ?_ ?_
  · simp at key; omega
  · simp only [up, dn, List.map_append, List.map_reverse, List.append_assoc]
    refine List.Perm.append_left X ?_
    simp only [List.singleton_append]
    exact List.perm_middle
  · have hbc : f (b + j' + 1 + 1 + k) = f b := by
      rw [show b + j' + 1 + 1 + k = b + c by omega, hD.per]
    have hl : (r :: up f (b + j' + 1 + 1) (k + 1)).getLast? = some (f b) := by
      rw [List.getLast?_cons, up_last]; simp [hbc]
    refine ⟨?_, closing_aux hX (by rw [List.getLast?_append, hl]; simp) h1⟩
    refine List.IsChain.append hX.ch ?_ ?_
    · refine List.IsChain.append (chain_dn hD _ _) ?_ ?_
      · rw [List.isChain_cons]
        refine ⟨?_, chain_up hD _ _⟩
        intro y hy; rw [up_head] at hy; cases hy; exact h4
      · intro x hx y hy
        rw [dn_last] at hx; cases hx; simp at hy; subst hy; exact h3
    · intro x hx y hy
      rw [List.head?_append, dn_head] at hy; simp at hy; subst hy
      rw [show b + 1 + j' = b + (j' + 1) by omega]; exact h2 x hx
  · rw [List.nodup_append]
    refine ⟨hX.nd, List.nodup_singleton r, ?_⟩
    intro x hx y hy hxy; simp at hy; subst hy; subst hxy; exact hrX hx
  · intro x hx t; simp at hx; rcases hx with hx | rfl
    · exact hX.off x hx t
    · exact hr t
  · intro i hi; simp at hi; omega
  · simp only [List.nodup_append, List.nodup_reverse, List.mem_reverse, List.mem_range'_1]
    refine ⟨List.nodup_range', List.nodup_range', ?_⟩
    intro a ha b' hb'; omega
def PH (G : SimpleGraph V) (f : ℕ → V) (x y : V) (K : ℕ) : Prop :=
  ∃ X : List V, OffL G f X ∧ K ≤ X.length ∧ (∀ z ∈ X.head?, G.Adj x z) ∧
    (∀ z ∈ X.getLast?, G.Adj z y)
lemma PH.symm {x y : V} {K : ℕ} (h : PH G f x y K) : PH G f y x K := by
  obtain ⟨X, hX, hK, h1, h2⟩ := h
  refine ⟨X.reverse, ⟨by simpa using hX.ne, List.nodup_reverse.mpr hX.nd, ?_, ?_⟩, by simpa, ?_, ?_⟩
  · rw [List.isChain_reverse]; exact hX.ch.imp (fun _ _ h => h.symm)
  · intro x hx; exact hX.off x (List.mem_reverse.mp hx)
  · intro z hz; rw [List.head?_reverse] at hz; exact (h2 z hz).symm
  · intro z hz; rw [List.getLast?_reverse] at hz; exact (h1 z hz).symm
lemma PH.mono {x y : V} {K K' : ℕ} (h : PH G f x y K) (hK : K' ≤ K) : PH G f x y K' := by
  obtain ⟨X, hX, hk, h1, h2⟩ := h; exact ⟨X, hX, by omega, h1, h2⟩
lemma Cy.shift (hD : Cy G c f) {s t : ℕ} (h : s = t + c) : f s = f t := by
  rw [h, hD.per]
def HP (G : SimpleGraph V) (H : Finset V) (x y : V) (X : List V) : Prop :=
  X.Nodup ∧ X.IsChain G.Adj ∧ (∀ z ∈ X, z ∈ H) ∧ X.head? = some x ∧ X.getLast? = some y
structure Comp (G : SimpleGraph V) (f : ℕ → V) (H : Finset V) : Prop where
  off : ∀ x ∈ H, ∀ t, f t ≠ x
  cl : ∀ x ∈ H, ∀ y, G.Adj x y → y ∈ H ∨ ∃ t, f t = y
  conn : ∀ x ∈ H, ∀ y ∈ H, ∃ X, HP G H x y X
variable {H : Finset V}
lemma HP.offL (hC : Comp G f H) {x y : V} {X : List V} (h : HP G H x y X) : OffL G f X :=
  ⟨by rintro rfl; simp [HP] at h, h.1, h.2.1, fun z hz => hC.off z (h.2.2.1 z hz)⟩
lemma ph_of (hC : Comp G f H) {a b z z' : V} (hz : z ∈ H) (hz' : z' ∈ H) (ha : G.Adj a z)
    (hb : G.Adj b z') : PH G f a b 1 := by
  obtain ⟨X, hX⟩ := hC.conn z hz z' hz'
  exact ⟨X, hX.offL hC, by have := (hX.offL hC).ne; exact List.length_pos_iff.mpr this,
    by intro w hw; rw [hX.2.2.2.1] at hw; cases hw; exact ha,
    by intro w hw; rw [hX.2.2.2.2] at hw; cases hw; exact hb.symm⟩
def Att (G : SimpleGraph V) (f : ℕ → V) (H : Finset V) (s : ℕ) : Prop := ∃ z ∈ H, G.Adj (f s) z
lemma G1 (hD : Cy G c f) (hC : Comp G f H) {s : ℕ} (hs : Att G f H s) :
    ∀ z ∈ H, ¬ G.Adj (f (s + 1)) z := by
  intro z hz hadj
  obtain ⟨z0, hz0, ha⟩ := hs
  obtain ⟨X, hX, hK, h1, h2⟩ := ph_of hC hz0 hz ha hadj
  have := R1 hD hX (b := s) (j := 1) le_rfl (by have := hD.three; omega) h1 h2
  omega
lemma G3 (hD : Cy G c f) (hC : Comp G f H) {s j : ℕ} (hs : Att G f H s)
    (hsj : Att G f H (s + j)) (hj : 1 ≤ j) (hjc : j < c) {r : V} (hrH : r ∉ H)
    (hrC : ∀ t, f t ≠ r) (h3 : G.Adj (f (s + 1)) r) (h4 : G.Adj r (f (s + j + 1))) : False := by
  obtain ⟨z, hz, hsz⟩ := hs
  obtain ⟨z', hz', hsz'⟩ := hsj
  obtain ⟨X, hX⟩ := hC.conn z hz z' hz'
  exact R22 hD (hX.offL hC) hrC (fun h => hrH (hX.2.2.1 r h)) (b := s) (j := j) hj (by omega)
    (by intro w hw; rw [hX.2.2.2.1] at hw; cases hw; exact hsz)
    (by intro w hw; rw [hX.2.2.2.2] at hw; cases hw; exact hsz'.symm) h3 h4
lemma split_Ioc (P : ℕ → Prop) [DecidablePred P] {a b d : ℕ} (hab : a ≤ b) (hbd : b ≤ d) :
    ((Finset.Ioc a d).filter P).card =
      ((Finset.Ioc a b).filter P).card + ((Finset.Ioc b d).filter P).card := by
  simp only [Finset.card_filter]
  exact (Finset.sum_Ioc_consecutive _ hab hbd).symm
lemma Cy.exists_window (hD : Cy G c f) (b t : ℕ) : ∃ t', b < t' ∧ t' ≤ b + c ∧ f t' = f t := by
  have hc : 0 < c := by have := hD.three; omega
  set m := t + c * (b + 1) - (b + 1)
  have hm : b + 1 ≤ t + c * (b + 1) := by nlinarith
  refine ⟨b + 1 + m % c, by omega, by have := Nat.mod_lt m hc; omega, ?_⟩
  have e1 : f (b + 1 + m % c + c * (m / c)) = f (b + 1 + m % c) := hD.per' _ _
  have e2 : b + 1 + m % c + c * (m / c) = t + c * (b + 1) := by
    have := Nat.mod_add_div m c; omega
  rw [← e1, e2, hD.per']
lemma Cy.mem_cset (hD : Cy G c f) (t : ℕ) : f t ∈ (Finset.range c).image f := by
  obtain ⟨t', h1, h2, h3⟩ := hD.exists_window 0 t
  rw [Finset.mem_image]
  refine ⟨t' % c, Finset.mem_range.mpr (Nat.mod_lt _ (by have := hD.three; omega)), ?_⟩
  rw [← hD.mod, h3]
lemma card_on_cycle [DecidableRel G.Adj] (hD : Cy G c f) (b : ℕ) (x : V) :
    ((Finset.Ioc b (b + c)).filter (fun t => G.Adj x (f t))).card =
      ((G.neighborFinset x).filter (· ∈ (Finset.range c).image f)).card := by
  have hinj : Set.InjOn f ((Finset.Ioc b (b + c)).filter (fun t => G.Adj x (f t))) := by
    intro i hi j hj hij
    simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_setOf_eq] at hi hj
    by_contra hne
    exact hD.ne_of_window (b := b + 1) (by omega) (by omega) (by omega) (by omega) hne hij
  rw [← Finset.card_image_of_injOn hinj]
  congr 1
  ext y
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_Ioc, mem_neighborFinset]
  constructor
  · rintro ⟨t, ⟨-, h⟩, rfl⟩; exact ⟨h, Finset.mem_image.mp (hD.mem_cset t)⟩
  · rintro ⟨h, hy⟩
    obtain ⟨t, -, rfl⟩ := hy
    obtain ⟨t', h1, h2, h3⟩ := hD.exists_window b t
    exact ⟨t', ⟨⟨h1, h2⟩, by rw [h3]; exact h⟩, h3⟩
lemma card_cset (hD : Cy G c f) : ((Finset.range c).image f).card = c := by
  rw [Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  exact hD.inj i j (Finset.mem_range.mp hi) (Finset.mem_range.mp hj) hij
section count
variable [DecidableRel G.Adj]
def cn (G : SimpleGraph V) [DecidableRel G.Adj] (f : ℕ → V) (x : V) (a b : ℕ) : Finset ℕ :=
  (Finset.Ioc a b).filter (fun t => G.Adj x (f t))
lemma cn_split (x : V) {a b d : ℕ} (hab : a ≤ b) (hbd : b ≤ d) :
    (cn G f x a d).card = (cn G f x a b).card + (cn G f x b d).card :=
  split_Ioc (fun t => G.Adj x (f t)) hab hbd
def sh (q m i : ℕ) : ℕ := if i ≤ m then m - i else m + q - i
lemma sh_le {q m i : ℕ} (hm : m < q) (hi : i < q) : sh q m i ≤ q - 1 := by
  unfold sh; split_ifs <;> omega
lemma sh_eq_zero {q m i : ℕ} (hi : i < q) (h : sh q m i = 0) : i = m ∨ m < i ∧ False := by
  unfold sh at h; split_ifs at h with h1
  · left; omega
  · omega
lemma sh_inj {q m i j : ℕ} (hm : m < q) (hi : i < q) (hj : j < q) (h : sh q m i = sh q m j) :
    i = j := by
  unfold sh at h; split_ifs at h <;> omega
def bp (c : ℕ) (s : ℕ → ℕ) (m i : ℕ) : ℕ := if i ≤ m then s i + c else s i
lemma arc_bound (hD : Cy G c f) (hC : Comp G f H) {q m : ℕ} (hm : m < q) {s : ℕ → ℕ}
    (hs : ∀ i j, i < j → j ≤ q → s i < s j) (hq : s q = s 0 + c)
    (hatt : ∀ i < q, Att G f H (s i))
    (hph : ∀ i < q, ∀ j < q, i < j → PH G f (f (s i)) (f (s j)) (q - 1)) :
    (∑ i ∈ Finset.range q, (cn G f (f (s i + 1)) (s m) (s (m + 1))).card) + s m + 2 ≤
      s (m + 1) + q := by
  have hs0 : ∀ i, i ≤ q → s 0 ≤ s i := by
    intro i hi; rcases Nat.eq_zero_or_pos i with rfl | h
    · exact le_rfl
    · exact (hs 0 i h hi).le
  have hsq : ∀ i, i < q → s i < s 0 + c := by intro i hi; rw [← hq]; exact hs i q hi le_rfl
  have hmm : s m < s (m + 1) := hs m (m + 1) (by omega) (by omega)
  set img : ℕ → Finset ℕ := fun i => (cn G f (f (s i + 1)) (s m) (s (m + 1))).image
    (· + sh q m i) with himg
  have hcard : ∀ i, (img i).card = (cn G f (f (s i + 1)) (s m) (s (m + 1))).card := by
    intro i; exact Finset.card_image_of_injective _ (add_left_injective _)
  have hsub : ∀ i ∈ Finset.range q, img i ⊆ Finset.Ioc (s m + 1) (s (m + 1) + q - 1) := by
    intro i hi y hy
    rw [Finset.mem_range] at hi
    simp only [himg, Finset.mem_image, cn, Finset.mem_filter, Finset.mem_Ioc] at hy
    obtain ⟨t, ⟨⟨ht1, ht2⟩, hadj⟩, rfl⟩ := hy
    have hle := sh_le hm hi
    rw [Finset.mem_Ioc]
    refine ⟨?_, by omega⟩
    by_cases h0 : sh q m i = 0
    · rcases sh_eq_zero hi h0 with rfl | ⟨-, hf⟩
      · rw [h0, Nat.add_zero]
        rcases Nat.lt_or_ge (s i + 1) t with h | h
        · exact h
        · exfalso; have : t = s i + 1 := by omega
          subst this; exact G.irrefl hadj
      · exact hf.elim
    · omega
  have hdisj : ∀ i ∈ (Finset.range q : Set ℕ), ∀ j ∈ (Finset.range q : Set ℕ), i ≠ j →
      Disjoint (img i) (img j) := by
    have key : ∀ i j, i < q → j < q → sh q m i < sh q m j → ∀ t t', s m < t → t ≤ s (m + 1) →
        s m < t' → t' ≤ s (m + 1) → G.Adj (f (s i + 1)) (f t) → G.Adj (f (s j + 1)) (f t') →
        t + sh q m i = t' + sh q m j → False := by
      intro i j hi hj hlt t t' ht1 ht2 ht1' ht2' ha ha' heq
      have hlei := sh_le hm hi
      have hlej := sh_le hm hj
      set bi := bp c s m i with hbi
      set bj := bp c s m j with hbj
      have fbi : f bi = f (s i) := by
        simp only [hbi, bp]; split_ifs
        · exact hD.shift rfl
        · rfl
      have fbj : f bj = f (s j) := by
        simp only [hbj, bp]; split_ifs
        · exact hD.shift rfl
        · rfl
      have fbi1 : f (bi + 1) = f (s i + 1) := by
        simp only [hbi, bp]; split_ifs
        · exact hD.shift (by omega)
        · rfl
      have fbj1 : f (bj + 1) = f (s j + 1) := by
        simp only [hbj, bp]; split_ifs
        · exact hD.shift (by omega)
        · rfl
      have hord : bj < bi := by
        have hsij : ∀ a b, a < b → b < q → s a < s b := fun a b h hb => hs a b h (by omega)
        simp only [hbi, hbj, bp]
        unfold sh at hlt
        by_cases hi' : i ≤ m <;> by_cases hj' : j ≤ m <;>
          simp only [hi', hj', if_true, if_false] at hlt ⊢
        · have := hsij j i (by omega) hi; omega
        · have := hsq j hj; have := hs0 i (by omega); omega
        · omega
        · have := hsij j i (by omega) hi; omega
      have hbi_le : bi ≤ s m + c := by
        simp only [hbi, bp]; split_ifs with h
        · rcases Nat.lt_or_ge i m with h' | h'
          · have := hs i m h' (by omega); omega
          · have : i = m := by omega
            subst this; omega
        · have := hsq i hi; have := hs0 m (by omega); omega
      have ht_le : t ≤ bj := by
        simp only [hbj, bp]; split_ifs with h
        · have := hs0 j (by omega)
          have : s (m + 1) ≤ s q := by
            rcases Nat.lt_or_ge (m + 1) q with h' | h'
            · exact (hs _ _ h' le_rfl).le
            · rw [show m + 1 = q by omega]
          omega
        · have : s (m + 1) ≤ s j := by
            rcases Nat.lt_or_ge (m + 1) j with h' | h'
            · exact (hs _ _ h' (by omega)).le
            · rw [show m + 1 = j by omega]
          omega
      have hX : PH G f (f bj) (f bi) (q - 1) := by
        rw [fbi, fbj]
        rcases Nat.lt_or_ge i j with h | h
        · exact (hph i hi j hj h).symm
        · have hne : i ≠ j := fun h' => by subst h'; omega
          exact hph j hj i hi (by omega)
      obtain ⟨X, hXo, hXl, h1, h2⟩ := hX
      have := R3 hD hXo (b := bj) (j := bi - bj) (p := t' + c - bj) (q := t + c - bj)
        (by omega) (by omega) (by omega) (by omega) h1
        (by rw [show bj + (bi - bj) = bi by omega]; exact h2)
        (by rw [fbj1, show bj + (t' + c - bj) = t' + c by omega, hD.shift rfl]; exact ha')
        (by rw [show bj + (bi - bj) + 1 = bi + 1 by omega, fbi1,
              show bj + (t + c - bj) = t + c by omega, hD.shift rfl]; exact ha)
      omega
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    rw [Finset.disjoint_left]
    intro y hy hy'
    simp only [himg, Finset.mem_image, cn, Finset.mem_filter, Finset.mem_Ioc] at hy hy'
    obtain ⟨t, ⟨⟨ht1, ht2⟩, ha⟩, rfl⟩ := hy
    obtain ⟨t', ⟨⟨ht1', ht2'⟩, ha'⟩, heq⟩ := hy'
    rcases Nat.lt_trichotomy (sh q m i) (sh q m j) with h | h | h
    · exact key i j hi hj h t t' ht1 ht2 ht1' ht2' ha ha' heq.symm
    · exact hij (sh_inj hm hi hj h)
    · exact key j i hj hi h t' t ht1' ht2' ht1 ht2 ha' ha heq
  have hU := Finset.card_biUnion (s := Finset.range q) (t := img) hdisj
  have hU2 := Finset.card_le_card (Finset.biUnion_subset.mpr hsub)
  rw [Nat.card_Ioc] at hU2
  simp only [hcard] at hU
  omega
lemma succ_count (hD : Cy G c f) (hC : Comp G f H) {q : ℕ} (hq1 : 1 ≤ q) {s : ℕ → ℕ}
    (hs : ∀ i j, i < j → j ≤ q → s i < s j) (hq : s q = s 0 + c)
    (hatt : ∀ i < q, Att G f H (s i))
    (hph : ∀ i < q, ∀ j < q, i < j → PH G f (f (s i)) (f (s j)) (q - 1)) :
    (∑ i ∈ Finset.range q, (cn G f (f (s i + 1)) (s 0) (s 0 + c)).card) + 2 * q ≤ c + q * q := by
  have hmono : ∀ m, m ≤ q → s 0 ≤ s m := by
    intro m hm; rcases Nat.eq_zero_or_pos m with rfl | h
    · exact le_rfl
    · exact (hs 0 m h hm).le
  have hsplit : ∀ x M, M ≤ q → (cn G f x (s 0) (s M)).card =
      ∑ m ∈ Finset.range M, (cn G f x (s m) (s (m + 1))).card := by
    intro x M
    induction M with
    | zero => intro _; simp [cn]
    | succ M ih =>
      intro hM
      rw [Finset.sum_range_succ, ← ih (by omega)]
      exact cn_split x (hmono M (by omega)) (hs M (M + 1) (by omega) hM).le
  have h1 : ∀ i, (cn G f (f (s i + 1)) (s 0) (s 0 + c)).card =
      ∑ m ∈ Finset.range q, (cn G f (f (s i + 1)) (s m) (s (m + 1))).card := by
    intro i; rw [← hq]; exact hsplit _ q le_rfl
  simp only [h1]
  rw [Finset.sum_comm]
  have harc : ∀ m ∈ Finset.range q,
      (∑ i ∈ Finset.range q, (cn G f (f (s i + 1)) (s m) (s (m + 1))).card) + s m + 2 ≤
        s (m + 1) + q := fun m hm =>
    arc_bound hD hC (Finset.mem_range.mp hm) hs hq hatt hph
  have hsum := Finset.sum_le_sum harc
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul] at hsum
  have htel : ∑ m ∈ Finset.range q, s (m + 1) = (∑ m ∈ Finset.range q, s m) + s q - s 0 := by
    have e1 := Finset.sum_range_succ' (fun m => s m) q
    have e2 := Finset.sum_range_succ (fun m => s m) q
    omega
  have h0 : s 0 ≤ (∑ m ∈ Finset.range q, s m) := by
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    rw [Finset.sum_range_succ']; omega
  rw [htel, hq] at hsum
  have : (∑ m ∈ Finset.range q, s m) + (s 0 + c) - s 0 = (∑ m ∈ Finset.range q, s m) + c := by
    omega
  rw [this] at hsum
  nlinarith
end count
section degsum
variable [DecidableRel G.Adj]
def Rest (c : ℕ) (f : ℕ → V) (H : Finset V) : Finset V :=
  Finset.univ.filter (fun y => y ∉ (Finset.range c).image f ∧ y ∉ H)
lemma offCs (hC : Comp G f H) : ∀ y ∈ H, y ∉ (Finset.range c).image f := by
  intro y hy hyC
  obtain ⟨t, -, ht⟩ := Finset.mem_image.mp hyC
  exact hC.off y hy t ht
lemma deg_split (hC : Comp G f H) (x : V) : G.degree x =
    ((G.neighborFinset x).filter (· ∈ (Finset.range c).image f)).card +
      ((G.neighborFinset x).filter (· ∈ H)).card +
      ((G.neighborFinset x).filter (· ∈ Rest c f H)).card := by
  set Cs := (Finset.range c).image f with hCs
  rw [← card_neighborFinset_eq_degree,
    ← Finset.card_filter_add_card_filter_not (s := G.neighborFinset x) (· ∈ Cs)]
  have : ((G.neighborFinset x).filter (fun a => ¬ a ∈ Cs)) =
      ((G.neighborFinset x).filter (· ∈ H)) ∪ ((G.neighborFinset x).filter (· ∈ Rest c f H)) := by
    ext y; simp only [Finset.mem_filter, Finset.mem_union, Rest, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨h1, h2⟩; by_cases hy : y ∈ H
      · exact Or.inl ⟨h1, hy⟩
      · exact Or.inr ⟨h1, h2, hy⟩
    · rintro (⟨h1, h2⟩ | ⟨h1, h2, -⟩)
      · exact ⟨h1, offCs hC y h2⟩
      · exact ⟨h1, h2⟩
  rw [this, Finset.card_union_of_disjoint, Nat.add_assoc]
  rw [Finset.disjoint_left]
  intro y h1 h2
  simp only [Finset.mem_filter, Rest, Finset.mem_univ, true_and] at h1 h2
  exact h2.2.2 h1.2
lemma n_split (hD : Cy G c f) (hC : Comp G f H) :
    Fintype.card V = c + H.card + (Rest c f H).card := by
  set Cs := (Finset.range c).image f with hCs
  have hcs : Cs.card = c := card_cset hD
  have : (Finset.univ : Finset V) = Cs ∪ H ∪ Rest c f H := by
    ext y; simp only [Finset.mem_univ, Finset.mem_union, Rest, Finset.mem_filter, true_iff]
    tauto
  have hu : Fintype.card V = (Cs ∪ H ∪ Rest c f H).card := by rw [← this, Finset.card_univ]
  rw [hu, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint, hcs]
  · rw [Finset.disjoint_left]; intro y h1 h2; exact offCs hC y h2 h1
  · rw [Finset.disjoint_left]; intro y h1 h2
    simp only [Rest, Finset.mem_filter, Finset.mem_univ, true_and] at h2
    rcases Finset.mem_union.mp h1 with h | h
    · exact h2.1 h
    · exact h2.2 h
lemma succ_deg (hD : Cy G c f) (hC : Comp G f H) {q : ℕ} (hq1 : 1 ≤ q) {s : ℕ → ℕ}
    (hs : ∀ i j, i < j → j ≤ q → s i < s j) (hq : s q = s 0 + c)
    (hatt : ∀ i < q, Att G f H (s i))
    (hph : ∀ i < q, ∀ j < q, i < j → PH G f (f (s i)) (f (s j)) (q - 1)) :
    (∑ i ∈ Finset.range q, G.degree (f (s i + 1))) + 2 * q + H.card ≤
      Fintype.card V + q * q := by
  have hSC := succ_count hD hC hq1 hs hq hatt hph
  have hsq : ∀ i, i < q → s i < s 0 + c := by intro i hi; rw [← hq]; exact hs i q hi le_rfl
  have hs0 : ∀ i, i ≤ q → s 0 ≤ s i := by
    intro i hi; rcases Nat.eq_zero_or_pos i with rfl | h
    · exact le_rfl
    · exact (hs 0 i h hi).le
  have hCpart : ∀ i, ((G.neighborFinset (f (s i + 1))).filter
      (· ∈ (Finset.range c).image f)).card = (cn G f (f (s i + 1)) (s 0) (s 0 + c)).card := by
    intro i; rw [← card_on_cycle hD (s 0)]; rfl
  have sH : ∀ i < q, ((G.neighborFinset (f (s i + 1))).filter (· ∈ H)).card = 0 := by
    intro i hi
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy hyH
    exact G1 hD hC (hatt i hi) y hyH ((mem_neighborFinset _ _ _).mp hy)
  have hdisj : ∀ i ∈ (Finset.range q : Set ℕ), ∀ j ∈ (Finset.range q : Set ℕ), i ≠ j →
      Disjoint ((G.neighborFinset (f (s i + 1))).filter (· ∈ Rest c f H))
        ((G.neighborFinset (f (s j + 1))).filter (· ∈ Rest c f H)) := by
    have key : ∀ i j, i < j → j < q → Disjoint
        ((G.neighborFinset (f (s i + 1))).filter (· ∈ Rest c f H))
        ((G.neighborFinset (f (s j + 1))).filter (· ∈ Rest c f H)) := by
      intro i j hij hj
      have hlt := hs i j hij (by omega)
      have hjc := hsq j hj
      have hi0 := hs0 i (by omega)
      rw [Finset.disjoint_left]
      intro y h1 h2
      simp only [Finset.mem_filter, mem_neighborFinset, Rest, Finset.mem_univ, true_and] at h1 h2
      have hatj : Att G f H (s i + (s j - s i)) := by
        rw [show s i + (s j - s i) = s j by omega]; exact hatt j hj
      refine G3 hD hC (hatt i (by omega)) hatj (by omega) (by omega) h1.2.2
        (fun t ht => h1.2.1 (ht ▸ hD.mem_cset t)) h1.1 ?_
      rw [show s i + (s j - s i) + 1 = s j + 1 by omega]; exact h2.1.symm
    intro i hi j hj hij
    rcases Nat.lt_or_gt_of_ne hij with h | h
    · exact key i j h (by simpa using hj)
    · exact (key j i h (by simpa using hi)).symm
  have hR := Finset.card_biUnion (s := Finset.range q)
    (t := fun i => (G.neighborFinset (f (s i + 1))).filter (· ∈ Rest c f H)) hdisj
  have hR2 : ((Finset.range q).biUnion
      (fun i => (G.neighborFinset (f (s i + 1))).filter (· ∈ Rest c f H))).card ≤
      (Rest c f H).card := by
    apply Finset.card_le_card
    intro y hy
    simp only [Finset.mem_biUnion, Finset.mem_filter] at hy
    obtain ⟨_, _, _, h⟩ := hy; exact h
  have hdeg : ∀ i ∈ Finset.range q, G.degree (f (s i + 1)) =
      (cn G f (f (s i + 1)) (s 0) (s 0 + c)).card +
        ((G.neighborFinset (f (s i + 1))).filter (· ∈ Rest c f H)).card := by
    intro i hi
    rw [deg_split hC, hCpart, sH i (Finset.mem_range.mp hi), Nat.add_zero]
  rw [Finset.sum_congr rfl hdeg, Finset.sum_add_distrib]
  have hn := n_split hD hC
  omega
lemma vert_deg (hD : Cy G c f) (hC : Comp G f H) {v : V} (hv : v ∈ H) {q : ℕ} {s : ℕ → ℕ}
    (hN : ∀ t, G.Adj v (f t) → ∃ i < q, f t = f (s i)) :
    G.degree v + 1 ≤ H.card + q := by
  have hvR : ((G.neighborFinset v).filter (· ∈ Rest c f H)).card = 0 := by
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy hyR
    simp only [Rest, Finset.mem_filter, Finset.mem_univ, true_and] at hyR
    rcases hC.cl v hv y ((mem_neighborFinset _ _ _).mp hy) with h | ⟨t, rfl⟩
    · exact hyR.2 h
    · exact hyR.1 (hD.mem_cset t)
  have hvH : ((G.neighborFinset v).filter (· ∈ H)).card + 1 ≤ H.card := by
    have : (G.neighborFinset v).filter (· ∈ H) ⊆ H.erase v := by
      intro y hy
      simp only [Finset.mem_filter, mem_neighborFinset] at hy
      exact Finset.mem_erase.mpr ⟨(G.ne_of_adj hy.1).symm, hy.2⟩
    have := Finset.card_le_card this
    rw [Finset.card_erase_of_mem hv] at this
    have : 1 ≤ H.card := Finset.card_pos.mpr ⟨v, hv⟩
    omega
  have hvC : ((G.neighborFinset v).filter (· ∈ (Finset.range c).image f)).card ≤ q := by
    have : (G.neighborFinset v).filter (· ∈ (Finset.range c).image f) ⊆
        (Finset.range q).image (fun i => f (s i)) := by
      intro y hy
      simp only [Finset.mem_filter, mem_neighborFinset, Finset.mem_image, Finset.mem_range] at hy
      obtain ⟨hadj, t, -, rfl⟩ := hy
      obtain ⟨i, hi, he⟩ := hN t hadj
      exact Finset.mem_image.mpr ⟨i, Finset.mem_range.mpr hi, he.symm⟩
    exact (Finset.card_le_card this).trans (Finset.card_image_le.trans (by simp))
  rw [deg_split hC, hvR]
  omega
end degsum
section link
variable [DecidableRel G.Adj]
lemma decomp (Q : List V) {a b : ℕ} (hab : a < b) (hb : b < Q.length) :
    ∃ Q1 M Q2, Q = Q1 ++ Q[a] :: (M ++ Q[b] :: Q2) ∧ M.length = b - a - 1 := by
  refine ⟨Q.take a, (Q.drop (a + 1)).take (b - a - 1), Q.drop (b + 1), ?_, ?_⟩
  · have e1 : Q.drop a = Q[a] :: Q.drop (a + 1) := List.drop_eq_getElem_cons (by omega)
    have e2 : (Q.drop (a + 1)).drop (b - a - 1) = Q[b] :: Q.drop (b + 1) := by
      rw [List.drop_drop, show a + 1 + (b - a - 1) = b by omega]
      exact List.drop_eq_getElem_cons hb
    calc Q = Q.take a ++ Q.drop a := (List.take_append_drop a Q).symm
      _ = Q.take a ++ Q[a] :: ((Q.drop (a + 1)).take (b - a - 1) ++
          (Q.drop (a + 1)).drop (b - a - 1)) := by rw [e1, List.take_append_drop]
      _ = _ := by rw [e2]
  · simp only [List.length_take, List.length_drop]; omega
end link
section linked
variable [DecidableRel G.Adj]
def KSep (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∀ S : Finset V, S.card + 1 ≤ k → ∀ X : Finset V, (∀ a ∈ X, a ∉ S) →
    (∀ a ∈ X, ∀ b, G.Adj a b → b ∉ S → b ∈ X) → X.Nonempty → ∀ y, y ∉ S → y ∉ X → False
lemma mem_cset_iff (hD : Cy G c f) (y : V) : y ∈ (Finset.range c).image f ↔ ∃ t, f t = y := by
  constructor
  · intro h; obtain ⟨t, -, ht⟩ := Finset.mem_image.mp h; exact ⟨t, ht⟩
  · rintro ⟨t, rfl⟩; exact hD.mem_cset t
lemma k_le_c (hD : Cy G c f) (hC : Comp G f H) {k : ℕ} (hK : KSep G k) (hH : H.Nonempty) :
    k ≤ c := by
  set A := ((Finset.range c).image f).filter (fun y => ∃ z ∈ H, G.Adj y z) with hA
  by_contra hlt
  push_neg at hlt
  have hAc : A.card ≤ c := (Finset.card_filter_le _ _).trans (card_cset hD).le
  have hclos : ∀ a ∈ H, ∀ b, G.Adj a b → b ∉ A → b ∈ H := by
    intro a ha b hab hbA
    rcases hC.cl a ha b hab with h | ⟨t, rfl⟩
    · exact h
    · exact absurd (Finset.mem_filter.mpr ⟨hD.mem_cset t, a, ha, hab.symm⟩) hbA
  have hHA : ∀ a ∈ H, a ∉ A := by
    intro a ha haA
    obtain ⟨t, -, ht⟩ := Finset.mem_image.mp (Finset.mem_filter.mp haA).1
    exact hC.off a ha t ht
  by_cases hne : A.Nonempty
  · obtain ⟨y, hy⟩ := hne
    obtain ⟨hyC, z, hz, hyz⟩ := Finset.mem_filter.mp hy
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hyC
    refine hK A (by omega) H hHA hclos hH (f (t + 1)) ?_ ?_
    · intro h
      obtain ⟨-, z', hz', h'⟩ := Finset.mem_filter.mp h
      exact G1 hD hC ⟨z, hz, hyz⟩ z' hz' h'
    · intro h; exact hC.off _ h (t + 1) rfl
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    refine hK A (by rw [hne]; simp; omega) H hHA hclos hH (f 0) ?_ ?_
    · rw [hne]; simp
    · intro h; exact hC.off _ h 0 rfl
lemma chain_in_H (hC : Comp G f H) : ∀ l : List V, l.IsChain G.Adj → (∀ x ∈ l.head?, x ∈ H) →
    (∀ x ∈ l, ∀ t, f t ≠ x) → ∀ x ∈ l, x ∈ H
  | [], _, _, _ => by simp
  | [a], _, h1, _ => by simpa using h1
  | a :: b :: l, hch, h1, hoff => by
    have ha : a ∈ H := h1 a rfl
    rw [List.isChain_cons_cons] at hch
    have hb : b ∈ H := by
      rcases hC.cl a ha b hch.1 with h | ⟨t, ht⟩
      · exact h
      · exact absurd ht (hoff b (by simp) t)
    have := chain_in_H hC (b :: l) hch.2 (by simpa using hb)
      (fun x hx => hoff x (List.mem_cons_of_mem a hx))
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact this x hx
lemma sep_ge (hD : Cy G c f) (hC : Comp G f H) {k : ℕ} (hK : KSep G k) {D : Finset V}
    (hDH : D ⊆ H) (hDk : k + 1 ≤ D.card) (S : Finset V)
    (hS : ∀ l, ABP G D ((Finset.range c).image f) l → ∃ x ∈ l, x ∈ S) : k ≤ S.card := by
  by_contra hlt
  push_neg at hlt
  have hH : H.Nonempty := by
    obtain ⟨x, hx⟩ := Finset.card_pos.mp (show 0 < D.card by omega); exact ⟨x, hDH hx⟩
  have hkc := k_le_c hD hC hK hH
  obtain ⟨d0, hd0D, hd0S⟩ : ∃ d ∈ D, d ∉ S := by
    by_contra h; push_neg at h
    have := Finset.card_le_card (show D ⊆ S from h); omega
  obtain ⟨y, hyC, hyS⟩ : ∃ y ∈ (Finset.range c).image f, y ∉ S := by
    by_contra h; push_neg at h
    have := Finset.card_le_card (show (Finset.range c).image f ⊆ S from h)
    rw [card_cset hD] at this; omega
  classical
  set X : Finset V := Finset.univ.filter (fun z => ∃ hz : z ∉ S, ∃ d, ∃ hd : d ∉ S, d ∈ D ∧
    (G.induce ((S : Set V)ᶜ)).Reachable ⟨d, hd⟩ ⟨z, hz⟩) with hX
  have memX : ∀ z, z ∈ X ↔ ∃ hz : z ∉ S, ∃ d, ∃ hd : d ∉ S, d ∈ D ∧
      (G.induce ((S : Set V)ᶜ)).Reachable ⟨d, hd⟩ ⟨z, hz⟩ := by
    intro z; simp [hX]
  refine hK S (by omega) X (fun a ha => ((memX a).mp ha).1) ?_ ⟨d0, (memX d0).mpr
    ⟨hd0S, d0, hd0S, hd0D, Reachable.refl _⟩⟩ y hyS ?_
  · intro a ha b hab hbS
    obtain ⟨haS, d, hdS, hdD, hr⟩ := (memX a).mp ha
    exact (memX b).mpr ⟨hbS, d, hdS, hdD, hr.trans (Adj.reachable (G := G.induce ((S : Set V)ᶜ))
      (u := ⟨a, haS⟩) (v := ⟨b, hbS⟩) hab)⟩
  · intro hy
    obtain ⟨hyS', d, hdS, hdD, hr⟩ := (memX y).mp hy
    obtain ⟨w⟩ := hr
    obtain ⟨p, hp⟩ := w.toPath
    obtain ⟨x, hx, hxS⟩ := hS (p.support.map Subtype.val) ⟨hp.support_nodup.map Subtype.val_injective,
      (List.isChain_map Subtype.val).mpr p.isChain_adj_support,
      ⟨d, hdD, by rw [Walk.support_eq_cons, List.map_cons, List.head?_cons]⟩,
      ⟨y, hyC, by rw [List.getLast?_map, List.getLast?_eq_getLast_of_ne_nil (Walk.support_ne_nil _),
        Walk.getLast_support]; rfl⟩⟩
    obtain ⟨x', -, rfl⟩ := List.mem_map.mp hx
    exact x'.2 hxS
lemma path_parts (hD : Cy G c f) (hC : Comp G f H) {D : Finset V} (hDH : D ⊆ H) {l : List V}
    (hl : ABP G D ((Finset.range c).image f) l ∧ (∀ x ∈ l.tail, x ∉ D) ∧
      (∀ x ∈ l.dropLast, x ∉ (Finset.range c).image f)) :
    ∃ d a w M, l = M ++ [a] ∧ M.head? = some d ∧ M.getLast? = some w ∧ d ∈ D ∧
      (∃ t, f t = a) ∧ G.Adj w a ∧ (∀ x ∈ M, x ∈ H) ∧ (∀ x ∈ M.tail, x ∉ D) ∧ M.Nodup ∧
      M.IsChain G.Adj := by
  obtain ⟨⟨hnd, hch, ⟨d, hd, hdh⟩, ⟨a, ha, hal⟩⟩, htl, hdl⟩ := hl
  have hne : l ≠ [] := by intro h; rw [h] at hdh; simp at hdh
  have hsplit : l = l.dropLast ++ [a] := by
    have h := List.dropLast_append_getLast hne
    rw [List.getLast?_eq_getLast_of_ne_nil hne, Option.some.injEq] at hal
    rw [← hal]; exact h.symm
  set M := l.dropLast with hM
  have hMne : M ≠ [] := by
    intro h
    rw [h] at hsplit; rw [hsplit] at hdh; simp at hdh; subst hdh
    obtain ⟨t, -, ht⟩ := Finset.mem_image.mp ha
    exact hC.off _ (hDH hd) t ht
  have hMh : M.head? = some d := by
    rw [hsplit, List.head?_append] at hdh
    obtain ⟨m, M', hm⟩ := List.ne_nil_iff_exists_cons.mp hMne
    rw [hm] at hdh ⊢; simpa using hdh
  obtain ⟨w, hw⟩ : ∃ w, M.getLast? = some w := by
    obtain ⟨w, hw⟩ := Option.isSome_iff_exists.mp (List.getLast?_isSome.mpr hMne); exact ⟨w, hw⟩
  rw [hsplit] at hnd hch
  have hMch : M.IsChain G.Adj := (List.isChain_append.mp hch).1
  have hwa : G.Adj w a := (List.isChain_append.mp hch).2.2 w hw a rfl
  have hMoff : ∀ x ∈ M, ∀ t, f t ≠ x := by
    intro x hx t ht; exact hdl x hx (by rw [← ht]; exact hD.mem_cset t)
  refine ⟨d, a, w, M, hsplit, hMh, hw, hd, (mem_cset_iff hD a).mp ha, hwa,
    chain_in_H hC M hMch (by rw [hMh]; intro x hx; cases hx; exact hDH hd) hMoff, ?_,
    (List.nodup_append.mp hnd).1, hMch⟩
  intro x hx
  apply htl
  rw [hsplit]
  obtain ⟨m, M', hm⟩ := List.ne_nil_iff_exists_cons.mp hMne
  rw [hm] at hx ⊢; simp only [List.tail_cons] at hx; simp [hx]
lemma getLast?_tail_append {X M : List V} {d : V} (hX : X.tail ≠ []) (hXl : X.getLast? = some d)
    (hMh : M.head? = some d) : (X.tail ++ M.tail).getLast? = M.getLast? := by
  obtain ⟨m, M', rfl⟩ : ∃ m M', M = m :: M' := by
    cases M with
    | nil => simp at hMh
    | cons m M' => exact ⟨m, M', rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at hMh; subst hMh
  cases M' with
  | nil =>
    simp only [List.tail_cons, List.append_nil, List.getLast?_singleton]
    obtain ⟨x, X', rfl⟩ : ∃ x X', X = x :: X' := by
      cases X with
      | nil => simp at hX
      | cons x X' => exact ⟨x, X', rfl⟩
    simp only [List.tail_cons] at hX ⊢
    rw [List.getLast?_cons, List.getLast?_eq_getLast_of_ne_nil hX] at hXl
    rw [List.getLast?_eq_getLast_of_ne_nil hX]; simpa using hXl
  | cons m' M'' =>
    rw [List.getLast?_append_of_ne_nil _ (by simp), List.tail_cons, List.getLast?_cons_cons]
lemma ends_linked (hC : Comp G f H) {D : Finset V} (hDH : D ⊆ H) {k : ℕ}
    {di dj wi wj ai aj : V} {Mi Mj X : List V}
    (hMih : Mi.head? = some di) (hMil : Mi.getLast? = some wi) (hMjh : Mj.head? = some dj)
    (hMjl : Mj.getLast? = some wj) (hwi : G.Adj wi ai) (hwj : G.Adj wj aj)
    (hMiH : ∀ x ∈ Mi, x ∈ H) (hMjH : ∀ x ∈ Mj, x ∈ H) (hMiD : ∀ x ∈ Mi.tail, x ∉ D)
    (hMjD : ∀ x ∈ Mj.tail, x ∉ D) (hMin : Mi.Nodup) (hMjn : Mj.Nodup) (hMic : Mi.IsChain G.Adj)
    (hMjc : Mj.IsChain G.Adj) (hdisj : ∀ x ∈ Mi, x ∉ Mj)
    (hX : HP G D di dj X) (hXk : k ≤ X.length) (hdd : di ≠ dj) :
    PH G f ai aj k := by
  obtain ⟨hXn, hXc, hXD, hXh, hXl⟩ := hX
  obtain ⟨x0, X', rfl⟩ : ∃ x0 X', X = x0 :: X' := by
    cases X with
    | nil => simp at hXh
    | cons x X' => exact ⟨x, X', rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at hXh; subst hXh
  have hX'ne : X' ≠ [] := by
    intro h; subst h; simp at hXl; exact hdd hXl
  obtain ⟨m0, Mj', rfl⟩ : ∃ m0 Mj', Mj = m0 :: Mj' := by
    cases Mj with
    | nil => simp at hMjh
    | cons m Mj' => exact ⟨m, Mj', rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at hMjh; subst hMjh
  have hdiMi : ∀ x ∈ Mi, x ∈ D → x = x0 := by
    intro x hx hxD
    obtain ⟨m, Mi', rfl⟩ : ∃ m Mi', Mi = m :: Mi' := by
      cases Mi with
      | nil => simp at hx
      | cons m Mi' => exact ⟨m, Mi', rfl⟩
    simp only [List.head?_cons, Option.some.injEq] at hMih; subst hMih
    rcases List.mem_cons.mp hx with rfl | hx
    · rfl
    · exact absurd hxD (hMiD x hx)
  refine ⟨Mi.reverse ++ (X' ++ Mj'), ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · simp [hX'ne]
  · rw [List.nodup_append, List.nodup_append]
    refine ⟨List.nodup_reverse.mpr hMin, ⟨(List.nodup_cons.mp hXn).2, (List.nodup_cons.mp hMjn).2,
      ?_⟩, ?_⟩
    · intro x hx y hy hxy; subst hxy; exact hMjD x hy (hXD x (by simp [hx]))
    · intro x hx y hy hxy; subst hxy
      rw [List.mem_reverse] at hx
      rcases List.mem_append.mp hy with hy | hy
      · have := hdiMi x hx (hXD x (by simp [hy])); subst this
        exact (List.nodup_cons.mp hXn).1 hy
      · exact hdisj x hx (List.mem_cons_of_mem _ hy)
  · rw [List.isChain_append, List.isChain_append]
    refine ⟨List.isChain_reverse.mpr (hMic.imp (fun _ _ h => h.symm)),
      ⟨(List.isChain_cons.mp hXc).2, (List.isChain_cons.mp hMjc).2, ?_⟩, ?_⟩
    · intro x hx y hy
      have : x = m0 := by
        rw [List.getLast?_cons, List.getLast?_eq_getLast_of_ne_nil hX'ne] at hXl
        rw [List.getLast?_eq_getLast_of_ne_nil hX'ne] at hx; simp at hXl hx; rw [← hx, hXl]
      subst this
      exact (List.isChain_cons.mp hMjc).1 y hy
    · intro x hx y hy
      rw [List.getLast?_reverse, hMih] at hx; cases hx
      rw [List.head?_append] at hy
      obtain ⟨x1, X'', rfl⟩ := List.ne_nil_iff_exists_cons.mp hX'ne
      simp at hy; subst hy
      exact (List.isChain_cons.mp hXc).1 _ rfl
  · intro x hx t ht
    rcases List.mem_append.mp hx with hx | hx
    · exact hC.off x (hMiH x (List.mem_reverse.mp hx)) t ht
    · rcases List.mem_append.mp hx with hx | hx
      · exact hC.off x (hDH (hXD x (by simp [hx]))) t ht
      · exact hC.off x (hMjH x (by simp [hx])) t ht
  · simp only [List.length_append, List.length_reverse, List.length_cons] at hXk ⊢
    have : 1 ≤ Mi.length := List.length_pos_iff.mpr (by intro h; rw [h] at hMih; simp at hMih)
    omega
  · intro z hz
    rw [List.head?_append, List.head?_reverse, hMil] at hz; cases hz; exact hwi.symm
  · intro z hz
    have e := getLast?_tail_append (X := x0 :: X') (M := m0 :: Mj') (d := m0)
      (by simpa using hX'ne) hXl rfl
    simp only [List.tail_cons] at e
    rw [List.getLast?_append_of_ne_nil _ (by simp [hX'ne]), e, hMjl] at hz
    cases hz; exact hwj
lemma sort_pos {q c : ℕ} (hq : 1 ≤ q) (t : Fin q → ℕ) (ht : Function.Injective t)
    (htc : ∀ i, t i < c) :
    ∃ s : ℕ → ℕ, (∀ i j, i < j → j ≤ q → s i < s j) ∧ s q = s 0 + c ∧
      (∀ j < q, ∃ i, s j = t i) ∧ ∀ i, ∃ j < q, s j = t i := by
  set T := Finset.univ.image t with hT
  have hTc : T.card = q := by rw [hT, Finset.card_image_of_injective _ ht]; simp
  set τ := T.orderEmbOfFin hTc
  refine ⟨fun j => if h : j < q then τ ⟨j, h⟩ else τ ⟨0, hq⟩ + c, ?_,
    by simp only []; rw [dif_neg (lt_irrefl q), dif_pos (show 0 < q by omega)], ?_, ?_⟩
  · intro i j hij hj
    have hi : i < q := by omega
    simp only [dif_pos hi]
    by_cases hjq : j < q
    · simp only [dif_pos hjq]; exact τ.lt_iff_lt.mpr (by simp [Fin.lt_def]; omega)
    · simp only [dif_neg hjq]
      have hm : τ ⟨i, hi⟩ ∈ T := T.orderEmbOfFin_mem hTc ⟨i, hi⟩
      obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hm
      have := htc a; rw [ha] at this; omega
  · intro j hj
    simp only [dif_pos hj]
    have hm : τ ⟨j, hj⟩ ∈ T := T.orderEmbOfFin_mem hTc ⟨j, hj⟩
    obtain ⟨a, -, ha⟩ := Finset.mem_image.mp hm
    exact ⟨a, ha.symm⟩
  · intro i
    have : t i ∈ Set.range τ := by
      rw [Finset.range_orderEmbOfFin]; exact Finset.mem_coe.mpr (Finset.mem_image_of_mem _ (by simp))
    obtain ⟨⟨j, hj⟩, hji⟩ := this
    exact ⟨j, hj, by simp only [dif_pos hj]; exact hji⟩
lemma ends_sorted (hD : Cy G c f) (hC : Comp G f H) {k : ℕ} {D : Finset V} (hDH : D ⊆ H)
    (hDl : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → ∃ X, HP G D x y X ∧ k ≤ X.length) {q : ℕ} (hq : 1 ≤ q)
    (P : Fin q → List V)
    (hP : ∀ i, ABP G D ((Finset.range c).image f) (P i) ∧ (∀ x ∈ (P i).tail, x ∉ D) ∧
      (∀ x ∈ (P i).dropLast, x ∉ (Finset.range c).image f))
    (hdisj : ∀ i j, i ≠ j → ∀ x ∈ P i, x ∉ P j) :
    ∃ s : ℕ → ℕ, (∀ i j, i < j → j ≤ q → s i < s j) ∧ s q = s 0 + c ∧
      (∀ j < q, Att G f H (s j)) ∧ (∀ i < q, ∀ j < q, i < j → PH G f (f (s i)) (f (s j)) k) ∧
      (∀ i, ∃ j < q, (P i).getLast? = some (f (s j))) := by
  have hc : 0 < c := by have := hD.three; omega
  choose d a w M hPM hMh hMl hdD hat hwa hMH hMD hMn hMc using
    fun i => path_parts hD hC hDH (hP i)
  choose tt htt using hat
  set t' : Fin q → ℕ := fun i => tt i % c with ht'
  have ft' : ∀ i, f (t' i) = a i := by intro i; simp only [ht']; rw [← hD.mod, htt]
  have aP : ∀ i, a i ∈ P i := by intro i; rw [hPM i]; simp
  have dP : ∀ i, d i ∈ P i := by
    intro i; rw [hPM i]; exact List.mem_append_left _ (List.mem_of_head? (hMh i))
  have wM : ∀ i, w i ∈ M i := fun i => List.mem_of_getLast? (hMl i)
  have tinj : Function.Injective t' := by
    intro i j hij
    by_contra hne
    have : a i = a j := by rw [← ft', ← ft', hij]
    exact hdisj i j hne _ (aP i) (this ▸ aP j)
  obtain ⟨s, hs, hsq, hs1, hs2⟩ := sort_pos hq t' tinj (fun i => Nat.mod_lt _ hc)
  refine ⟨s, hs, hsq, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨i, hi⟩ := hs1 j hj
    exact ⟨w i, hMH i _ (wM i), by rw [hi, ft']; exact (hwa i).symm⟩
  · intro i hi j hj hij
    obtain ⟨α, hα⟩ := hs1 i hi
    obtain ⟨β, hβ⟩ := hs1 j hj
    have hne : α ≠ β := by
      intro h; subst h; have := hs i j hij (by omega); omega
    have hdd : d α ≠ d β := fun h => hdisj α β hne _ (dP α) (h ▸ dP β)
    obtain ⟨X, hX, hXk⟩ := hDl _ (hdD α) _ (hdD β) hdd
    have hdM : ∀ x ∈ M α, x ∉ M β := by
      intro x hx hx'
      exact hdisj α β hne x (by rw [hPM α]; exact List.mem_append_left _ hx)
        (by rw [hPM β]; exact List.mem_append_left _ hx')
    rw [hα, hβ, ft', ft']
    exact ends_linked hC hDH (hMh α) (hMl α) (hMh β) (hMl β) (hwa α) (hwa β) (hMH α) (hMH β)
      (hMD α) (hMD β) (hMn α) (hMn β) (hMc α) (hMc β) hdM hX hXk hdd
  · intro i
    obtain ⟨j, hj, hji⟩ := hs2 i
    exact ⟨j, hj, by rw [hPM i, List.getLast?_concat, hji, ft']⟩
lemma linked_contra (hD : Cy G c f) (hC : Comp G f H) {δ k : ℕ} (hδ : ∀ x, δ ≤ G.degree x)
    (hk : 1 ≤ k) (hkn : Fintype.card V + k * (k - 1) ≤ (k + 1) * δ) (hK : KSep G k)
    {D : Finset V} (hDH : D ⊆ H) (hDk : k + 1 ≤ D.card)
    (hDl : ∀ x ∈ D, ∀ y ∈ D, x ≠ y → ∃ X, HP G D x y X ∧ k ≤ X.length) : False := by
  set Cs := (Finset.range c).image f with hCs
  have hsepk := sep_ge hD hC hK hDH hDk
  have hHD : D.card ≤ H.card := Finset.card_le_card hDH
  have hk1 : k * (k - 1) + k = k * k := by
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩; simp; ring
  by_cases h : ∀ S : Finset V, (∀ l, ABP G D Cs l → ∃ x ∈ l, x ∈ S) → k + 1 ≤ S.card
  · obtain ⟨P, hP, hdisj⟩ := menger_trim D Cs (k + 1) h
    obtain ⟨s, hs, hsq, hatt, hph, -⟩ := ends_sorted hD hC hDH hDl (by omega) P hP hdisj
    have := succ_deg hD hC (q := k + 1) (by omega) hs hsq hatt
      (fun i hi j hj hij => by simpa using hph i hi j hj hij)
    have hsum : (k + 1) * δ ≤ ∑ i ∈ Finset.range (k + 1), G.degree (f (s i + 1)) := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range (k + 1)) => hδ (f (s i + 1)))
      simpa [Finset.sum_const, Finset.card_range, smul_eq_mul] using this
    have e : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by ring
    omega
  · push_neg at h
    obtain ⟨S, hS, hSk⟩ := h
    have hSc : S.card = k := le_antisymm (by omega) (hsepk S hS)
    obtain ⟨P, hP, hdisj⟩ := menger_trim D Cs k (fun S' hS' => hsepk S' hS')
    obtain ⟨s, hs, hsq, hatt, hph, hend⟩ := ends_sorted hD hC hDH hDl hk P hP hdisj
    have hmeet : ∀ i, ∃ x ∈ P i, x ∈ S := fun i => hS _ (hP i).1
    choose σ hσP hσS using hmeet
    have σinj : Function.Injective σ := by
      intro i j hij; by_contra hne; exact hdisj i j hne _ (hσP i) (hij ▸ hσP j)
    have himg : Finset.univ.image σ = S := by
      apply Finset.eq_of_subset_of_card_le
      · intro x hx; obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx; exact hσS i
      · rw [Finset.card_image_of_injective _ σinj, hSc]; simp
    have onP : ∀ x ∈ S, ∃ i, x ∈ P i := by
      intro x hx; rw [← himg] at hx
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx; exact ⟨i, hσP i⟩
    obtain ⟨v, hvD, hvS⟩ : ∃ v ∈ D, v ∉ S := by
      by_contra h'; push_neg at h'
      have := Finset.card_le_card (show D ⊆ S from h'); omega
    have hvH := hDH hvD
    have hN : ∀ t, G.Adj v (f t) → ∃ j < k, f t = f (s j) := by
      intro t hvt
      have hl : ABP G D Cs [v, f t] := ⟨by simp; intro h; exact hC.off v hvH t h.symm,
        by simp [hvt], ⟨v, hvD, rfl⟩, ⟨f t, hD.mem_cset t, rfl⟩⟩
      obtain ⟨x, hx, hxS⟩ := hS _ hl
      simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact absurd hxS hvS
      · obtain ⟨i, hi⟩ := onP _ hxS
        obtain ⟨j, hj, hjl⟩ := hend i
        refine ⟨j, hj, ?_⟩
        have hne : P i ≠ [] := by intro h; rw [h] at hi; simp at hi
        have hsplit := List.dropLast_append_getLast hne
        rw [← hsplit] at hi
        rcases List.mem_append.mp hi with h1 | h1
        · exact absurd (hD.mem_cset t) ((hP i).2.2 _ h1)
        · simp at h1
          rw [List.getLast?_eq_getLast_of_ne_nil hne] at hjl
          simp at hjl; rw [h1, hjl]
    have hv := vert_deg hD hC hvH hN
    have hsd := succ_deg hD hC (q := k) hk hs hsq hatt
      (fun i hi j hj hij => (hph i hi j hj hij).mono (by omega))
    have hsum : k * δ ≤ ∑ i ∈ Finset.range k, G.degree (f (s i + 1)) := by
      have := Finset.sum_le_sum (fun i (_ : i ∈ Finset.range k) => hδ (f (s i + 1)))
      simpa [Finset.sum_const, Finset.card_range, smul_eq_mul] using this
    have hvd := hδ v
    have e : (k + 1) * δ = k * δ + δ := by ring
    omega
end linked
section cyc
lemma HP.reverse' {D : Finset V} {x y : V} {X : List V} (h : HP G D x y X) : HP G D y x X.reverse :=
  ⟨List.nodup_reverse.mpr h.1, List.isChain_reverse.mpr (h.2.1.imp (fun _ _ h => h.symm)),
    fun z hz => h.2.2.1 z (List.mem_reverse.mp hz), by rw [List.head?_reverse]; exact h.2.2.2.2,
    by rw [List.getLast?_reverse]; exact h.2.2.2.1⟩
lemma arcs {l : List V} (hnd : l.Nodup) (hch : l.IsChain G.Adj)
    (hcl : ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, G.Adj x y) {i j : ℕ} (hij : i < j) (hj : j < l.length) :
    HP G l.toFinset l[i] l[j] ((l.drop i).take (j - i + 1)) ∧
      HP G l.toFinset l[j] l[i] (l.drop j ++ l.take (i + 1)) := by
  have hi : i < l.length := by omega
  constructor
  · refine ⟨(hnd.sublist (List.drop_sublist _ _)).sublist (List.take_sublist _ _),
      chain_sub (chain_sub hch (List.drop_suffix _ _).isInfix) (List.take_prefix _ _).isInfix,
      fun z hz => List.mem_toFinset.mpr (List.mem_of_mem_drop (List.mem_of_mem_take hz)), ?_, ?_⟩
    · rw [List.drop_eq_getElem_cons hi, List.take_succ_cons]; rfl
    · rw [List.getLast?_eq_getElem?]
      simp only [List.length_take, List.length_drop, List.getElem?_take, List.getElem?_drop]
      rw [show min (j - i + 1) (l.length - i) = j - i + 1 by omega]
      rw [if_pos (by omega), show i + (j - i + 1 - 1) = j by omega]
      exact List.getElem?_eq_getElem hj
  · have hdj : l.drop j = l[j] :: l.drop (j + 1) := List.drop_eq_getElem_cons hj
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [List.nodup_append]
      refine ⟨hnd.sublist (List.drop_sublist _ _), hnd.sublist (List.take_sublist _ _), ?_⟩
      intro a ha b hb hab; subst hab
      have := List.disjoint_take_drop hnd (show i + 1 ≤ j by omega)
      exact this hb ha
    · rw [List.isChain_append]
      refine ⟨chain_sub hch (List.drop_suffix _ _).isInfix, chain_sub hch (List.take_prefix _ _).isInfix, ?_⟩
      intro a ha b hb
      have hne : l ≠ [] := by intro h; rw [h] at hj; simp at hj
      rw [List.getLast?_drop, if_neg (by omega)] at ha
      rw [List.head?_take, if_neg (by omega)] at hb
      exact hcl a ha b hb
    · intro z hz
      rcases List.mem_append.mp hz with hz | hz
      · exact List.mem_toFinset.mpr (List.mem_of_mem_drop hz)
      · exact List.mem_toFinset.mpr (List.mem_of_mem_take hz)
    · rw [List.head?_append, hdj]; simp
    · rw [List.getLast?_append_of_ne_nil _ (List.ne_nil_of_length_pos (by simp; omega)),
        List.getLast?_eq_getElem?]
      simp only [List.length_take, List.getElem?_take]
      rw [show min (i + 1) l.length = i + 1 by omega, if_pos (by omega),
        show i + 1 - 1 = i by omega]
      exact List.getElem?_eq_getElem hi
lemma cyc_linked {H : Finset V} {k : ℕ} {l : List V} (hl : VL G H l)
    (hcl : ∀ x ∈ l.getLast?, ∀ y ∈ l.head?, G.Adj x y) (hL : 2 * k ≤ l.length + 2) :
    ∀ x ∈ l.toFinset, ∀ y ∈ l.toFinset, x ≠ y → ∃ X, HP G l.toFinset x y X ∧ k ≤ X.length := by
  intro x hx y hy hxy
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hx)
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (List.mem_toFinset.mp hy)
  have hij : i ≠ j := by intro h; subst h; exact hxy rfl
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · obtain ⟨h1, h2⟩ := arcs hl.1 hl.2.1 hcl h hj
    by_cases hlen : k ≤ j - i + 1
    · refine ⟨_, h1, ?_⟩
      simp only [List.length_take, List.length_drop]; omega
    · refine ⟨_, h2.reverse', ?_⟩
      simp only [List.length_reverse, List.length_append, List.length_drop, List.length_take]
      omega
  · obtain ⟨h1, h2⟩ := arcs hl.1 hl.2.1 hcl h hi
    by_cases hlen : k ≤ i - j + 1
    · refine ⟨_, h1.reverse', ?_⟩
      simp only [List.length_reverse, List.length_take, List.length_drop]; omega
    · refine ⟨_, h2, ?_⟩
      simp only [List.length_append, List.length_drop, List.length_take]; omega
end cyc
section glue
variable [DecidableRel G.Adj]
def cyc {a : V} (C : G.Walk a a) : ℕ → V := fun t => C.getVert (t % C.length)
lemma cy_of {a : V} (C : G.Walk a a) (hC : C.IsCycle) (hlong : C.length = G.circumference) :
    Cy G C.length (cyc C) := by
  have hc := hC.three_le_length
  refine ⟨hc, fun t => by simp [cyc], fun t => ?_, fun i j hi hj h => ?_, fun l hnd hcl => ?_⟩
  · simp only [cyc]
    have hlt : t % C.length < C.length := Nat.mod_lt _ (by omega)
    have hm : (t + 1) % C.length = (t % C.length + 1) % C.length := by
      rw [Nat.add_mod, Nat.mod_eq_of_lt (show 1 < C.length by omega)]
    rw [hm]
    by_cases h : t % C.length + 1 < C.length
    · rw [Nat.mod_eq_of_lt h]; exact C.adj_getVert_succ hlt
    · have h' : t % C.length + 1 = C.length := by omega
      rw [h', Nat.mod_self, Walk.getVert_zero]
      have := C.adj_getVert_succ hlt
      rwa [h', Walk.getVert_length] at this
  · simp only [cyc, Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h
    exact hC.getVert_injOn' (by simp; omega) (by simp; omega) h
  · by_cases h3 : l.length < 3
    · omega
    · obtain ⟨b, w, hw, hwl⟩ := cycle_of_CL l hnd hcl (by omega)
      rw [← hwl, hlong]; exact le_circumference w hw
lemma mem_support_cyc {a : V} (C : G.Walk a a) (hC : C.IsCycle) (y : V) :
    y ∈ C.support ↔ ∃ t, cyc C t = y := by
  have hc := hC.three_le_length
  constructor
  · intro hy
    obtain ⟨n, hn, hnl⟩ := Walk.mem_support_iff_exists_getVert.mp hy
    rcases Nat.lt_or_ge n C.length with h | h
    · exact ⟨n, by simp [cyc, Nat.mod_eq_of_lt h, hn]⟩
    · refine ⟨0, ?_⟩
      have : n = C.length := by omega
      subst this
      simp [cyc, ← hn, Walk.getVert_length]
  · rintro ⟨t, rfl⟩; exact Walk.getVert_mem_support _ _
lemma reach_mem {s : Set V} {x y : s} (w : (G.induce s).Walk x y) {z : s} (hz : z ∈ w.support) :
    (G.induce s).Reachable x z := ⟨w.takeUntil z hz⟩
def offWalk {a b : V} (w : G.Walk a b) : Set V := {v | v ∉ w.support}
end glue
end OMA.BondyK
end
section
namespace Graph189RootedPath
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V} {z u : V}
theorem exists_rooted_longest [Fintype V] (G : SimpleGraph V) (z : V) :
    ∃ (v : V) (P : G.Walk z v), P.IsPath ∧
      ∀ {b} (Q : G.Walk z b), Q.IsPath → Q.length ≤ P.length := by
  classical
  let Good (m : ℕ) := ∃ (v : V) (P : G.Walk z v), P.IsPath ∧ P.length = m
  have base : Good 0 := ⟨z,.nil,by simp,rfl⟩
  obtain ⟨v,P,hp,hlen⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) base
  refine ⟨v,P,hp,?_⟩
  intro b Q hQ
  rw [hlen]
  have card := hQ.support_nodup.length_le_card
  have size := Q.length_support
  exact Nat.le_findGreatest (by omega) (show Good Q.length from ⟨b,Q,hQ,rfl⟩)
end Graph189RootedPath
end
section
namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset
theorem cycle_of_degree {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (z : V) {d : ℕ} (two : 2 ≤ d) (degree : ∀ v, d ≤ G.degree v) :
    ∃ y, ∃ Q : G.Walk y y, Q.IsCycle ∧ d+1 ≤ Q.length := by
  obtain ⟨x,P,hp,maximal⟩ := Graph189RootedPath.exists_rooted_longest G z
  let R := P.reverse
  have all (v : V) (adj : G.Adj x v) : v ∈ R.support := by
    by_contra outside
    have absent : v ∉ P.support := by simpa [R] using outside
    have extended := maximal (P.concat adj) (hp.concat absent adj)
    simp at extended
  let U := (R.support.take d).toFinset
  have first : x ∈ U := by
    apply List.mem_toFinset.mpr
    apply (List.mem_take_iff_idxOf_lt R.start_mem_support).mpr
    have idx := R.length_takeUntil R.start_mem_support
    simp at idx
    omega
  have small : (U.erase x).card < d := by
    have one := card_erase_add_one first
    have le := List.toFinset_card_le (R.support.take d)
    have len := List.length_take_le d R.support
    change U.card ≤ _ at le
    omega
  have outside : ∃ v ∈ G.neighborFinset x, v ∉ U := by
    by_contra! h
    have sub : G.neighborFinset x ⊆ U.erase x :=
      fun v hv => mem_erase.mpr ⟨((G.mem_neighborFinset x v).mp hv).ne.symm,h v hv⟩
    have bound := card_le_card sub
    rw [G.card_neighborFinset_eq_degree] at bound
    have := degree x
    omega
  obtain ⟨y,adj,far⟩ := outside
  have edge := (G.mem_neighborFinset x y).mp adj
  have hy := all y edge
  let T := R.takeUntil y hy
  have farIndex : d ≤ R.support.idxOf y := by
    by_contra! h
    exact far (List.mem_toFinset.mpr ((List.mem_take_iff_idxOf_lt hy).mpr h))
  have long : d ≤ T.length := by rwa [R.length_takeUntil hy]
  refine ⟨y,T.cons edge.symm,?_,by simp only [Walk.length_cons]; omega⟩
  apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
  refine ⟨?_,by simp only [Walk.length_cons]; omega⟩
  rw [Walk.tail_cons]
  exact (Walk.isPath_copy _ _ _).mpr (hp.reverse.takeUntil hy)
theorem original_dist_two {V : Type*} {G : SimpleGraph V} {S : Set V}
    {x y : S} (two : (G.induce S).dist x y = 2) : G.dist x.val y.val = 2 := by
  have hr : (G.induce S).Reachable x y := Reachable.of_dist_ne_zero (by omega)
  obtain ⟨P,len⟩ := hr.exists_walk_length_eq_dist
  let f := (Embedding.induce (G:=G) S).toHom
  let W := P.map f
  have le := G.dist_le W
  rw [Walk.length_map,len,two] at le
  have ne : x.val ≠ y.val := by
    intro eq
    rw [Subtype.ext eq,SimpleGraph.dist_self] at two
    omega
  have na : ¬G.Adj x.val y.val := by
    intro h
    have ha : (G.induce S).Adj x y := h
    rw [dist_eq_one_iff_adj.mpr ha] at two
    omega
  have gt := W.reachable.one_lt_dist_of_ne_of_not_adj ne na
  change 1 < G.dist x.val y.val at gt
  exact Nat.le_antisymm le (by omega)
noncomputable def exactTwo {V : Type*} [Fintype V] (G : SimpleGraph V) (x : V) : Finset V := by
  classical
  exact univ.filter (fun v => G.dist x v = 2)
theorem induced_second_layer {V : Type*} [Fintype V] {G : SimpleGraph V} (S : Set V)
    [Fintype S] (x : S) {k : ℕ} (cap : G.distEven x.val ≤ k+1) :
    (exactTwo (G.induce S) x).card ≤ k := by
  classical
  let f : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let T := (exactTwo (G.induce S) x).map f
  have two : ∀ v ∈ T, G.dist x.val v = 2 := by
    intro v hv
    obtain ⟨u,hu,rfl⟩ := mem_map.mp hv
    exact original_dist_two (Finset.mem_filter.mp hu).2
  have missing : x.val ∉ T := by
    intro hx
    have h := two _ hx
    simp at h
  have sub : insert x.val T ⊆ univ.filter (fun y => Even (G.dist x.val y)) := by
    intro v hv
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rcases mem_insert.mp hv with rfl|h
    · simp
    · rw [two v h]
      decide
  have cmp := card_le_card sub
  rw [card_insert_of_notMem missing] at cmp
  have ct : T.card = (exactTwo (G.induce S) x).card := card_map _
  change T.card + 1 ≤ G.distEven x.val at cmp
  omega
end Graph189ExteriorDegreeCycle
end
section
namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
theorem degree_induce_filter {V : Type*} [Fintype V] {G : SimpleGraph V}
    [DecidableRel G.Adj] (S : Set V) [Fintype S] [DecidablePred (· ∈ S)] (x : S) :
    (G.induce S).degree x = ((G.neighborFinset x.val).filter (fun v => v ∈ S)).card := by
  classical
  let f : S ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have same : ((G.induce S).neighborFinset x).map f =
      (G.neighborFinset x.val).filter (fun y => y ∈ S) := by
    ext y
    constructor
    · intro hy
      obtain ⟨u,hu,rfl⟩ := mem_map.mp hy
      exact mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr
        (((G.induce S).mem_neighborFinset _ _).mp hu),u.property⟩
    · intro hy
      obtain ⟨he,hs⟩ := mem_filter.mp hy
      exact mem_map.mpr ⟨⟨y,hs⟩,((G.induce S).mem_neighborFinset _ _).mpr
        ((G.mem_neighborFinset _ _).mp he),rfl⟩
  have card := congrArg Finset.card same
  rwa [card_map,(G.induce S).card_neighborFinset_eq_degree] at card
theorem degree_le_deletion_add_one {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (w : V) (x : {u : V | u ≠ w}) :
    G.degree x.val ≤ (G.induce {u : V | u ≠ w}).degree x + 1 := by
  rw [degree_induce_filter,←G.card_neighborFinset_eq_degree]
  have eq : (G.neighborFinset x.val).filter (fun v => v ∈ {u : V | u ≠ w}) =
      (G.neighborFinset x.val).erase w := by ext u; simp [and_comm]
  rw [eq]
  have := pred_card_le_card_erase (a:=w) (s:=G.neighborFinset x.val)
  omega
theorem cycle_of_nonisolated_degree {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {d : ℕ} (two : 2 ≤ d)
    (edge : ∃ x y, G.Adj x y)
    (degree : ∀ x y, G.Adj x y → d ≤ G.degree x) :
    ∃ a, ∃ Q : G.Walk a a, Q.IsCycle ∧ d+1 ≤ Q.length := by
  classical
  let S : Set V := {v | ∃ y, G.Adj v y}
  obtain ⟨x,y,hxy⟩ := edge
  have sd (v : S) : d ≤ (G.induce S).degree v := by
    rw [degree_induce_filter]
    have eq : (G.neighborFinset v.val).filter (fun u => u ∈ S) = G.neighborFinset v.val := by
      apply filter_eq_self.mpr
      exact fun u hu => ⟨v.val,((G.mem_neighborFinset _ _).mp hu).symm⟩
    rw [eq,G.card_neighborFinset_eq_degree]
    obtain ⟨b,hb⟩ := v.property
    exact degree v.val b hb
  obtain ⟨v,Q,hQ,len⟩ := cycle_of_degree (G:=G.induce S) ⟨x,y,hxy⟩ two sd
  let f := (Embedding.induce (G:=G) S).toHom
  exact ⟨f v,Q.map f,hQ.map Subtype.val_injective,len.trans_eq (Walk.length_map f Q).symm⟩
end Graph189ExteriorDegreeCycle
end
section
namespace Graph189
open SimpleGraph Finset
private theorem append_chain {V : Type*} {G : SimpleGraph V} {L R : List V}
    {a b : V} (hl : L.IsChain G.Adj) (hr : R.IsChain G.Adj)
    (ha : L.getLast? = some a) (hb : R.head? = some b) (h : G.Adj a b) :
    (L ++ R).IsChain G.Adj := by
  apply hl.append hr
  intro x hx y hy
  rw [ha] at hx
  rw [hb] at hy
  have hax : a = x := by simpa using hx
  have hby : b = y := by simpa using hy
  exact hax ▸ hby ▸ h
private theorem reverse_chain {V : Type*} {G : SimpleGraph V} {L : List V}
    (h : L.IsChain G.Adj) : L.reverse.IsChain G.Adj :=
  List.isChain_reverse.mpr (h.imp fun _ _ h => h.symm)
private theorem split_at_pair {V : Type*} (l : List V) (i : ℕ) (hi : i + 1 < l.length) :
    ∃ P Q, l = P ++ l[i]'(by omega) :: l[i + 1] :: Q := by
  refine ⟨l.take i, l.drop (i + 2), ?_⟩
  conv_lhs => rw [← List.take_append_drop i l]
  rw [List.drop_eq_getElem_cons (by omega : i < l.length), List.drop_eq_getElem_cons hi]
private theorem trace_of_list {V : Type*} [DecidableEq V] {G : SimpleGraph V} (l : List V)
    (hn : l.Nodup) (hc : l.IsChain G.Adj) (hall : ∀ z : V, z ∈ l) (hne : l ≠ []) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  let p := Walk.ofSupport l hne hc
  have hs : p.support = l := Walk.support_ofSupport hne hc
  exact ⟨_, _, p, (Walk.IsPath.mk' (by rwa [hs])).isHamiltonian_of_mem (fun z => by
    rw [hs]
    exact hall z)⟩
private theorem trace_of_permuted_chain {V : Type*} [DecidableEq V] {G : SimpleGraph V} {l W : List V}
    (hn : l.Nodup) (hall : ∀ z : V, z ∈ l) (h : W.Perm l) (hc : W.IsChain G.Adj)
    (x : V) : ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  have hm (z : V) : z ∈ W := h.mem_iff.mpr (hall z)
  exact trace_of_list W (h.nodup_iff.mpr hn) hc hm (List.ne_nil_of_mem (hm x))
private theorem augmented_chain_excluding {V : Type*} {G : SimpleGraph V} {l : List V}
    {x y : V} (hc : l.IsChain (G ⊔ edge x y).Adj) (h : x ∉ l ∨ y ∉ l) :
    l.IsChain G.Adj := by
  apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
  intro a b P Q he
  have ha : a ∈ l := by rw [he]; simp
  have hb : b ∈ l := by rw [he]; simp
  have hab := List.isChain_iff_forall_rel_of_append_cons_cons.mp hc he
  rcases hab with hab | hab
  · exact hab
  · have hr := (edge_adj x y a b).mp hab
    rcases hr.1 with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact (h.elim (fun hn => hn ha) (fun hn => hn hb)).elim
    · exact (h.elim (fun hn => hn hb) (fun hn => hn ha)).elim
private theorem repair_left {V : Type*} {G : SimpleGraph V} {L R : List V}
    {x y u v : V} (hl : L.IsChain G.Adj) (hr : R.IsChain G.Adj)
    (hx : L.getLast? = some x) (hy : R.head? = some y)
    (hxu : G.Adj x u) (hyv : G.Adj y v)
    {P Q : List V} (hcut : L = P ++ u :: v :: Q) :
    ∃ W : List V, W.Perm (L ++ R) ∧ W.IsChain G.Adj := by
  let L₁ := P ++ [u]
  let L₂ := v :: Q
  have hl12 : L = L₁ ++ L₂ := by simpa [L₁,L₂,List.append_assoc] using hcut
  have hl₁ : L₁.IsChain G.Adj := (hl12 ▸ hl).left_of_append
  have hl₂ : L₂.IsChain G.Adj := (hl12 ▸ hl).right_of_append
  have hx₂ : L₂.getLast? = some x := by
    rw [hl12, List.getLast?_append_of_ne_nil _ (by simp [L₂])] at hx
    exact hx
  have hv₂ : L₂.head? = some v := by simp [L₂]
  have hrevH : L₂.reverse.head? = some x := by rwa [List.head?_reverse]
  have hrevL : L₂.reverse.getLast? = some v := by rwa [List.getLast?_reverse]
  have hlast : L₁.getLast? = some u := by simp [L₁]
  refine ⟨L₁ ++ (L₂.reverse ++ R), ?_, ?_⟩
  · apply (((List.reverse_perm L₂).append_right R).append_left L₁).trans
    exact List.Perm.of_eq ((List.append_assoc L₁ L₂ R).symm.trans
      (congrArg (· ++ R) hl12.symm))
  · have hjoin := append_chain (reverse_chain hl₂) hr hrevL hy hyv.symm
    apply append_chain hl₁ hjoin hlast _ hxu.symm
    simp [hrevH]
private theorem repair_right {V : Type*} {G : SimpleGraph V} {L R : List V}
    {x y u v : V} (hl : L.IsChain G.Adj) (hr : R.IsChain G.Adj)
    (hx : L.getLast? = some x) (hy : R.head? = some y)
    (hxu : G.Adj x u) (hyv : G.Adj y v)
    {P Q : List V} (hcut : R = P ++ u :: v :: Q) :
    ∃ W : List V, W.Perm (L ++ R) ∧ W.IsChain G.Adj := by
  have hy' : R.reverse.getLast? = some y := by rwa [List.getLast?_reverse]
  have hx' : L.reverse.head? = some x := by rwa [List.head?_reverse]
  have hcut' : R.reverse = Q.reverse ++ v :: u :: P.reverse := by
    rw [hcut]
    simp [List.reverse_append, List.reverse_cons, List.append_assoc]
  obtain ⟨W, hW, hc⟩ :=
    repair_left (reverse_chain hr) (reverse_chain hl) hy' hx' hyv hxu hcut'
  refine ⟨W, hW.trans ?_, hc⟩
  rw [← List.reverse_append]
  exact List.reverse_perm _
private theorem split_closure {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (hd : Fintype.card V ≤ G.degree x + G.degree y + 1)
    (P Q : List V) (hn : (P ++ x :: y :: Q).Nodup)
    (hc : (P ++ x :: y :: Q).IsChain (G ⊔ edge x y).Adj)
    (hall : ∀ z : V, z ∈ P ++ x :: y :: Q) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let L := P ++ [x]
  let R := y :: Q
  let l := L ++ R
  have hLRe : l = P ++ x :: y :: Q := by simp [l,L,R,List.append_assoc]
  rw [← hLRe] at hn hc hall
  have hno_x : x ∉ R := by
    intro h
    exact (List.nodup_append.mp hn).2.2 x (by simp [L]) x h rfl
  have hno_y : y ∉ L := by
    intro h
    exact (List.nodup_append.mp hn).2.2 y h y (by simp [R]) rfl
  have hl := augmented_chain_excluding (x := x) (y := y) hc.left_of_append (Or.inr hno_y)
  have hr := augmented_chain_excluding (x := x) (y := y) hc.right_of_append (Or.inl hno_x)
  have hx : L.getLast? = some x := by simp [L]
  have hy : R.head? = some y := by simp [R]
  have hLe : L ≠ [] := by simp [L]
  have hRe : R ≠ [] := by simp [R]
  let s := L.head hLe
  let t := R.getLast hRe
  have hs : L.head? = some s := List.head?_eq_some_head hLe
  have ht : R.getLast? = some t := List.getLast?_eq_some_getLast hRe
  have hst : l.head? = some s := by simp [l,hs]
  have htt : l.getLast? = some t := by simp [l,ht]
  by_cases hxt : G.Adj x t
  · apply trace_of_permuted_chain hn hall ((List.reverse_perm R).append_left L) _ x
    apply append_chain hl (reverse_chain hr) hx _ hxt
    rwa [List.head?_reverse]
  by_cases hys : G.Adj y s
  · apply trace_of_permuted_chain hn hall ((List.reverse_perm L).append_right R) _ x
    apply append_chain (reverse_chain hl) hr _ hy hys.symm
    rwa [List.getLast?_reverse]
  have hlen : l.length = Fintype.card V := by
    rw [← List.toFinset_card_of_nodup hn]
    have he : l.toFinset = univ := by ext z; simp [hall]
    simp [he]
  let I := Fin (l.length - 1)
  let u (i : I) : V := l[i.val]'(by have := i.isLt; omega)
  let v (i : I) : V := l[i.val+1]'(by have := i.isLt; omega)
  let S : Finset I := univ.filter fun i => G.Adj x (u i)
  let T : Finset I := univ.filter fun i => G.Adj y (v i)
  have hS : G.degree x ≤ S.card := by
    have hsub : G.neighborFinset x ⊆ S.image u := by
      intro z hz
      have hzx := (mem_neighborFinset G x z).mp hz
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (hall z)
      have hjlt : j < l.length - 1 := by
        by_contra! hh
        have hj' : j + 1 = l.length := by omega
        have hz : l[j] = t := by
          have hlne : l ≠ [] := List.ne_nil_of_mem (hall x)
          have hget : l.getLast hlne = t := List.getLast_of_getLast?_eq_some htt
          rw [List.getLast_eq_getElem] at hget
          have he : j = l.length - 1 := by omega
          exact he ▸ hget
        exact hxt (hz ▸ hzx)
      refine mem_image.mpr ⟨⟨j,hjlt⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩, rfl⟩
      exact hzx
    exact (card_le_card hsub).trans card_image_le
  have hT : G.degree y ≤ T.card := by
    have hsub : G.neighborFinset y ⊆ T.image v := by
      intro z hz
      have hzy := (mem_neighborFinset G y z).mp hz
      obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (hall z)
      have hj0 : 0 < j := by
        by_contra! hh
        have he : j = 0 := by omega
        have hlne : l ≠ [] := List.ne_nil_of_mem (hall x)
        have hget : l.head hlne = s := List.head_of_head?_eq_some hst
        rw [List.head_eq_getElem] at hget
        subst j
        exact hys (hget ▸ hzy)
      have hjlt : j - 1 < l.length - 1 := by omega
      let i : I := ⟨j - 1, hjlt⟩
      have hi : v i = l[j] := by
        change l[j - 1 + 1]'(by omega) = l[j]
        congr 1
        omega
      exact mem_image.mpr ⟨i, mem_filter.mpr ⟨mem_univ _, hi.symm ▸ hzy⟩, hi⟩
    exact (card_le_card hsub).trans card_image_le
  have hpidx : P.length < l.length - 1 := by rw [hLRe]; simp
  let i₀ : I := ⟨P.length, hpidx⟩
  have hu₀ : u i₀ = x := by
    change (L ++ R)[P.length]'(by simp [L, R]) = x
    rw [List.getElem_append_left (by simp [L]), List.getElem_append_right le_rfl]
    simp
  have hv₀ : v i₀ = y := by
    change (L ++ R)[P.length + 1]'(by simp [L, R]) = y
    rw [List.getElem_append_right (by simp [L])]
    simp [L, R]
  have hout : i₀ ∉ S ∪ T := by
    simp [S,T,hu₀,hv₀]
  have hcap : (S ∪ T).card < l.length - 1 := by
    have hne : S ∪ T ≠ (univ : Finset I) := fun h => hout (h ▸ mem_univ _)
    have hh := card_lt_card (ssubset_univ_iff.mpr hne)
    simpa [I] using hh
  obtain ⟨i, hiS, hiT⟩ : ∃ i, i ∈ S ∧ i ∈ T := by
    by_contra! h
    have hdis : Disjoint S T := disjoint_left.mpr h
    have hcard := card_union_of_disjoint hdis
    omega
  have hxu : G.Adj x (u i) := (mem_filter.mp hiS).2
  have hyv : G.Adj y (v i) := (mem_filter.mp hiT).2
  have hin : i.val ≠ P.length := by
    intro h
    have hi0 : i = i₀ := Fin.ext h
    exact hout (mem_union_left _ (hi0 ▸ hiS))
  have hit := i.isLt
  have hLv : L.length = P.length + 1 := by simp [L]
  rcases lt_or_gt_of_ne hin with hbefore | hafter
  · have hixy : i.val + 1 < L.length := by omega
    obtain ⟨A,B,hAB⟩ := split_at_pair L i.val hixy
    have hu : u i = L[i.val]'(by omega) := List.getElem_append_left (by omega)
    have hv : v i = L[i.val+1] := List.getElem_append_left hixy
    rw [← hu, ← hv] at hAB
    obtain ⟨W, hw, hWc⟩ := repair_left hl hr hx hy hxu hyv hAB
    exact trace_of_permuted_chain hn hall hw hWc x
  · let j := i.val - L.length
    have hlen' : l.length = L.length + R.length := List.length_append
    have hj : j + 1 < R.length := by dsimp [j]; omega
    obtain ⟨A,B,hAB⟩ := split_at_pair R j hj
    have hu : u i = R[j]'(by omega) := List.getElem_append_right (by omega)
    have hv : v i = R[j+1] := by
      unfold v
      change (L ++ R)[i.val+1] = R[j+1]
      rw [List.getElem_append_right (by omega)]
      congr 1
      dsimp [j]
      omega
    rw [← hu, ← hv] at hAB
    obtain ⟨W, hw, hWc⟩ := repair_right hl hr hx hy hxu hyv hAB
    exact trace_of_permuted_chain hn hall hw hWc x
theorem traceable_of_sup_edge {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (_hne : x ≠ y) (_hxy : ¬ G.Adj x y)
    (hd : Fintype.card V ≤ G.degree x + G.degree y + 1)
    (hpath : ∃ a b : V, ∃ p : (G ⊔ edge x y).Walk a b, p.IsHamiltonian) :
    ∃ a b : V, ∃ p : G.Walk a b, p.IsHamiltonian := by
  obtain ⟨a,b,p,hp⟩ := hpath
  let l := p.support
  have hn := hp.isPath.support_nodup
  have hall := hp.mem_support
  have hc := p.isChain_adj_support
  by_cases hG : l.IsChain G.Adj
  · exact trace_of_list l hn hG hall p.support_ne_nil
  obtain ⟨i, hi, hbad⟩ := List.exists_not_getElem_of_not_isChain hG
  obtain ⟨P,Q,he⟩ := split_at_pair l i hi
  have hu : (G ⊔ edge x y).Adj l[i] l[i+1] :=
    List.isChain_iff_forall_rel_of_append_cons_cons.mp hc he
  rcases hu with h | h
  · exact (hbad h).elim
  have hh := (edge_adj x y _ _).mp h
  rcases hh.1 with ⟨hx,hy⟩ | ⟨hx,hy⟩
  · rw [hx,hy] at he
    exact split_closure hd P Q (he ▸ hn) (he ▸ hc) (he ▸ hall)
  · rw [hx,hy] at he
    have hc' : l.IsChain (G ⊔ edge y x).Adj := by simpa only [edge_comm y x] using hc
    exact split_closure (by omega) P Q (he ▸ hn) (he ▸ hc') (he ▸ hall)
end Graph189
end
section
open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y a b : V}
theorem gap_length_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (A J B : List V) (split : p.support = A ++ J ++ B)
    (q : G.Walk a b) (hq : q.IsPath) (disjoint : List.Disjoint q.support p.support)
    (left : ∀ z∈A.getLast?, G.Adj z a) (right : ∀ z∈B.head?, G.Adj b z) :
    q.support.length ≤ J.length := by
  classical
  let L := (A ++ q.support) ++ B
  have pnd := hp.support_nodup
  have pc := p.isChain_adj_support
  rw [split] at pnd pc disjoint
  have ca := pc.left_of_append.left_of_append
  have cb := pc.right_of_append
  have qsHead : q.support.head? = some a := by
    rw [List.head?_eq_some_head q.support_ne_nil, q.head_support]
  have qsLast : q.support.getLast? = some b := by
    rw [List.getLast?_eq_some_getLast q.support_ne_nil, q.getLast_support]
  have first : (A++q.support).IsChain G.Adj := by
    apply ca.append q.isChain_adj_support
    intro z hz w hw
    rw [qsHead] at hw
    have same : a=w := by simpa using hw
    exact same ▸ left z hz
  have chain : L.IsChain G.Adj := by
    apply first.append cb
    intro z hz w hw
    have last : (A++q.support).getLast? = some b := by
      simp [List.getLast?_append,qsLast]
    rw [last] at hz
    have same : b=z := by simpa using hz
    exact same ▸ right w hw
  have nd : L.Nodup := by
    refine List.Nodup.append ?_ pnd.of_append_right ?_
    · apply List.Nodup.append pnd.of_append_left.of_append_left hq.support_nodup
      rw [List.disjoint_left]
      intro z hzA hzQ
      exact List.disjoint_left.mp disjoint hzQ (by simp [hzA])
    · rw [List.disjoint_left]
      intro z hz hzB
      rcases List.mem_append.mp hz with hzA | hzQ
      · exact List.disjoint_left.mp pnd.disjoint (by simp [hzA]) hzB
      · exact List.disjoint_left.mp disjoint hzQ (by simp [hzB])
  have hn : L≠[] := by simp [L,q.support_ne_nil]
  let r := Walk.ofSupport L hn chain
  have rs : r.support = L := Walk.support_ofSupport hn chain
  have rlen := longest r (Walk.IsPath.mk' (by rwa [rs]))
  have lhs := r.length_support
  have rhs := p.length_support
  rw [rs] at lhs
  rw [split] at rhs
  simp only [L,List.length_append] at lhs rhs
  omega
end Graph189ExteriorGap
end
section
open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y a b : V}
theorem prefix_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (i : Fin p.support.length) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (contact : G.Adj b p.support[i.val]) : q.support.length ≤ i.val := by
  let L := p.support
  have head : (L.drop i.val).head? = some L[i.val] := by
    simp [List.head?_drop]
  have gap := gap_length_of_detour p hp longest [] (L.take i.val) (L.drop i.val)
    (by simp [L]) q hq disjoint (by simp) (by
      intro z hz
      rw [head] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact)
  have small := List.length_take_le i.val L
  omega
theorem suffix_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (i : Fin p.support.length) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (contact : G.Adj p.support[i.val] a) : i.val + 1 + q.support.length ≤ p.support.length := by
  let L := p.support
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have gap := gap_length_of_detour p hp longest (L.take (i.val+1)) (L.drop (i.val+1)) []
    (by simp [L]) q hq disjoint (by
      intro z hz
      rw [last] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact) (by simp)
  simp only [L,List.length_drop] at gap
  have hi := i.isLt
  omega
theorem interval_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    (i j : Fin p.support.length) (hij : i < j) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (left : G.Adj p.support[i.val] a) (right : G.Adj b p.support[j.val]) :
    i.val+1+q.support.length ≤ j.val := by
  let L := p.support
  let gap := j.val-(i.val+1)
  have ij : i.val+1+gap=j.val := by
    change i.val < j.val at hij
    dsimp [gap]
    omega
  have split : L = L.take (i.val+1) ++ (L.drop (i.val+1)).take gap ++ L.drop j.val := by
    rw [←List.take_add,ij,List.take_append_drop]
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have head : (L.drop j.val).head? = some L[j.val] := by
    simp [List.head?_drop]
  have bound := gap_length_of_detour p hp longest _ _ _ split q hq disjoint (by
    intro z hz
    rw [last] at hz
    have eq : L[i.val] = z := by simpa using hz
    exact eq ▸ left) (by
    intro z hz
    rw [head] at hz
    have eq : L[j.val] = z := by simpa using hz
    exact eq ▸ right)
  have small := List.length_take_le gap (L.drop (i.val+1))
  omega
end Graph189ExteriorGap
end
section
open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}
theorem omitted_contact_internal (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (outside : a∉p.support) (i : Fin p.support.length) (contact : G.Adj p.support[i.val] a) :
    0 < i.val ∧ i.val + 1 < p.support.length := by
  let q : G.Walk a a := Walk.nil
  have hq : q.IsPath := by simp [q]
  have hd : List.Disjoint q.support p.support := by simpa [q,List.disjoint_left] using outside
  have h₁ := prefix_of_detour p hp longest i q hq hd contact.symm
  have h₂ := suffix_of_detour p hp longest i q hq hd contact
  simp only [q,Walk.support_nil,List.length_singleton] at h₁ h₂
  omega
theorem omitted_contact_spacing (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (outside : a∉p.support) (i j : Fin p.support.length) (ordered : i < j)
    (first : G.Adj p.support[i.val] a) (second : G.Adj p.support[j.val] a) :
    i.val+2 ≤ j.val := by
  let q : G.Walk a a := Walk.nil
  have hq : q.IsPath := by simp [q]
  have hd : List.Disjoint q.support p.support := by simpa [q,List.disjoint_left] using outside
  exact interval_of_detour p hp longest i j ordered q hq hd first second.symm
theorem adjacent_omitted_contact_spacing (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    (i j : Fin p.support.length) (ordered : i < j)
    (first : G.Adj p.support[i.val] a) (second : G.Adj p.support[j.val] b) :
    i.val+3 ≤ j.val := by
  let q : G.Walk a b := Walk.cons ab Walk.nil
  have hq : q.IsPath := Walk.IsPath.mk' (by simp [q,ab.ne])
  have hd : List.Disjoint q.support p.support := by
    rw [List.disjoint_left]
    intro z hz h
    rcases (show z=a ∨ z=b by simpa [q] using hz) with rfl | rfl
    · exact ha h
    · exact hb h
  exact interval_of_detour p hp longest i j ordered q hq hd first second.symm
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}
def crossIndices (A B : Finset ℕ) : Finset ℕ :=
  (A.image (fun i => i-1) ∪ (A∩B).image (fun i => i+1)) ∪ (B \ A)
private theorem card_crossIndices (A B : Finset ℕ) (positive : ∀ i∈A, 0 < i)
    (separated : ∀ i∈A, ∀ j∈B, i=j ∨ i+3 ≤ j ∨ j+3 ≤ i) :
    (crossIndices A B).card = A.card+B.card := by
  have dis₁ : Disjoint (A.image (fun i => i-1)) ((A∩B).image (fun i => i+1)) := by
    rw [Finset.disjoint_left]
    intro t ht hw
    obtain ⟨i,hi,ei⟩ := Finset.mem_image.mp ht
    obtain ⟨j,hj,ej⟩ := Finset.mem_image.mp hw
    have := positive i hi
    rcases separated i hi j (Finset.mem_inter.mp hj).2 with h | h | h <;> omega
  have dis₂ : Disjoint (A.image (fun i => i-1) ∪ (A∩B).image (fun i => i+1)) (B \ A) := by
    rw [Finset.disjoint_left]
    intro t ht hw
    have hb := (Finset.mem_sdiff.mp hw).1
    rcases Finset.mem_union.mp ht with h | h
    · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
      have := positive i hi
      rcases separated i hi t hb with h | h | h <;> omega
    · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
      rcases separated i (Finset.mem_inter.mp hi).1 t hb with h | h | h <;> omega
  have inj : Set.InjOn (fun i : ℕ => i-1) (A : Set ℕ) := by
    intro i hi j hj heq
    change i-1=j-1 at heq
    have := positive i hi
    have := positive j hj
    omega
  have cover : (B \ A) ∪ (A∩B) = B := by ext t; simp; tauto
  have dis : Disjoint (B \ A) (A∩B) := Finset.disjoint_left.mpr
    (fun _ h₁ h₂ => (Finset.mem_sdiff.mp h₁).2 (Finset.mem_inter.mp h₂).1)
  have hc := Finset.card_union_of_disjoint dis
  rw [cover] at hc
  rw [crossIndices,Finset.card_union_of_disjoint dis₂,Finset.card_union_of_disjoint dis₁,
    Finset.card_image_of_injOn inj,Finset.card_image_of_injective _
      (show Function.Injective (fun i : ℕ => i+1) by intro i j h; change i+1=j+1 at h; omega)]
  omega
noncomputable def contactPositions (p : G.Walk x y) (a : V) : Finset ℕ := by
  classical
  exact (Finset.range p.support.length).filter (fun i => G.Adj (p.getVert i) a)
theorem mem_contactPositions (p : G.Walk x y) (a : V) (i : ℕ) :
    i∈contactPositions p a ↔ i < p.support.length ∧ G.Adj (p.getVert i) a := by
  classical
  simp [contactPositions]
theorem get_at (p : G.Walk x y) {i : ℕ} (hi : i < p.support.length) :
    p.support[i] = p.getVert i := (p.getVert_eq_support_getElem (by
      have := p.length_support
      omega)).symm
theorem two_step_metric {a b z : V} (different : a≠b) (missing : ¬G.Adj a b)
    (az : G.Adj a z) (bz : G.Adj b z) : G.dist a b = 2 := by
  have h := SimpleGraph.edist_eq_two_iff.mpr ⟨different,missing,⟨z,az,bz⟩⟩
  simp [SimpleGraph.dist,h]
theorem cross_position_witnesses [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b) :
    let A := contactPositions p a
    let B := contactPositions p b
    (crossIndices A B).card=A.card+B.card ∧
    (∀ i∈crossIndices A B, i < p.support.length ∧ G.dist a (p.getVert i)=2) := by
  classical
  let A := contactPositions p a
  let B := contactPositions p b
  have inside (i : ℕ) (h : i∈A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨hi,hc⟩ := (mem_contactPositions p a i).mp h
    exact omitted_contact_internal p hp longest ha ⟨i,hi⟩ (by simpa [get_at] using hc)
  have own (i j : ℕ) (hi : i∈A) (hj : j∈A) (lt : i < j) : i+2 ≤ j := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p a j).mp hj
    exact omitted_contact_spacing p hp longest ha ⟨i,ri⟩ ⟨j,rj⟩ lt
      (by simpa [get_at] using ci) (by simpa [get_at] using cj)
  have separate (i : ℕ) (hi : i∈A) (j : ℕ) (hj : j∈B) : i=j ∨ i+3 ≤ j ∨ j+3 ≤ i := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p b j).mp hj
    rcases lt_trichotomy i j with lt | same | gt
    · exact Or.inr (Or.inl (adjacent_omitted_contact_spacing p hp longest ha hb ab
        ⟨i,ri⟩ ⟨j,rj⟩ lt (by simpa [get_at] using ci) (by simpa [get_at] using cj)))
    · exact Or.inl same
    · exact Or.inr (Or.inr (adjacent_omitted_contact_spacing p hp longest hb ha ab.symm
        ⟨j,rj⟩ ⟨i,ri⟩ gt (by simpa [get_at] using cj) (by simpa [get_at] using ci)))
  have shell (i : ℕ) (hi : i∈crossIndices A B) : i < p.support.length ∧ G.dist a (p.getVert i)=2 := by
    have different (j : ℕ) : a≠p.getVert j := fun eq => ha (eq ▸ p.getVert_mem_support j)
    have ls := p.length_support
    have via (i j : ℕ) (hpi : i < p.support.length) (hj : j∈A) (no : i∉A)
        (ij : G.Adj (p.getVert i) (p.getVert j)) : G.dist a (p.getVert i)=2 := by
      have hc := ((mem_contactPositions p a j).mp hj).2
      exact two_step_metric (different _) (fun h => no ((mem_contactPositions p a i).mpr ⟨hpi,h.symm⟩)) hc.symm ij
    rcases Finset.mem_union.mp hi with h | h
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
        obtain ⟨pos,back⟩ := inside j hj
        have inrange : j-1 < p.support.length := by omega
        refine ⟨inrange,via (j-1) j inrange hj (fun hi => ?_) ?_⟩
        · have aux := own (j-1) j hi hj (by omega)
          omega
        · have edge := p.adj_getVert_succ (i := j-1) (by omega)
          rwa [show j-1+1=j by omega] at edge
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
        have jA := (Finset.mem_inter.mp hj).1
        obtain ⟨_,back⟩ := inside j jA
        refine ⟨back,via (j+1) j back jA (fun hi => ?_) ?_⟩
        · have aux := own j (j+1) jA hi (by omega)
          omega
        · exact (p.adj_getVert_succ (i := j) (by omega)).symm
    · obtain ⟨hB,hA⟩ := Finset.mem_sdiff.mp h
      obtain ⟨ri,ci⟩ := (mem_contactPositions p b i).mp hB
      exact ⟨ri,two_step_metric (different _) (fun h => hA ((mem_contactPositions p a i).mpr ⟨ri,h.symm⟩)) ab ci⟩
  exact ⟨card_crossIndices A B (fun i h => (inside i h).1) separate,shell⟩
theorem cross_positions_le_path_shell [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b) :
    (contactPositions p a).card + (contactPositions p b).card ≤
      (p.support.toFinset.filter (fun z => G.dist a z=2)).card := by
  classical
  let A := contactPositions p a
  let B := contactPositions p b
  obtain ⟨count,shell⟩ := cross_position_witnesses p hp longest ha hb ab
  change (crossIndices A B).card=A.card+B.card at count
  have inj : Set.InjOn p.getVert ((crossIndices A B : Finset ℕ) : Set ℕ) := by
    intro i hi j hj same
    exact hp.getVert_injOn (by change i ≤ p.length; have := (shell i hi).1; have := p.length_support; omega)
      (by change j ≤ p.length; have := (shell j hj).1; have := p.length_support; omega) same
  have incl : (crossIndices A B).image p.getVert ⊆ p.support.toFinset.filter (fun z => G.dist a z=2) := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support i),(shell i hi).2⟩
  have bound := Finset.card_le_card incl
  rw [Finset.card_image_of_injOn inj,count] at bound
  exact bound
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
theorem contact_card_neighbors (p : G.Walk x y) (hp : p.IsPath) (a : V) :
    (contactPositions p a).card = (G.neighborFinset a ∩ p.support.toFinset).card := by
  classical
  have inj : Set.InjOn p.getVert ((contactPositions p a : Finset ℕ) : Set ℕ) := by
    intro i hi j hj h
    have il := ((mem_contactPositions p a i).mp hi).1
    have jl := ((mem_contactPositions p a j).mp hj).1
    have ls := p.length_support
    exact hp.getVert_injOn (by change i ≤ p.length; omega) (by change j ≤ p.length; omega) h
  have eq : (contactPositions p a).image p.getVert = G.neighborFinset a ∩ p.support.toFinset := by
    ext z
    constructor
    · intro hz
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
      have nb := ((mem_contactPositions p a i).mp hi).2.symm
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset a _).mpr nb,List.mem_toFinset.mpr (p.getVert_mem_support i)⟩
    · intro hz
      obtain ⟨hadj,hm⟩ := Finset.mem_inter.mp hz
      have hza := ((G.mem_neighborFinset a z).mp hadj).symm
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp hm)
      have eql : p.getVert i=z := (get_at p hi).symm.trans he
      exact Finset.mem_image.mpr ⟨i,(mem_contactPositions p a i).mpr ⟨hi,eql ▸ hza⟩,eql⟩
  rw [←eq,Finset.card_image_of_injOn inj]
theorem exterior_contact_degree (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    (G.neighborFinset a ∩ p.support.toFinset).card + G.degree b ≤
      k+1+((G.neighborFinset b \ p.support.toFinset) ∩ G.neighborFinset a).card := by
  classical
  let P := p.support.toFinset
  let A := G.neighborFinset a
  let B := G.neighborFinset b
  let D := B \ P
  let C := D ∩ A
  let X := (D.erase a) \ A
  let Q := P.filter (fun z => G.dist a z=2)
  have acol := cross_positions_le_path_shell p hp longest ha hb ab
  rw [contact_card_neighbors p hp a,contact_card_neighbors p hp b] at acol
  change (A∩P).card+(B∩P).card ≤ Q.card at acol
  have ain : a∈D := Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ab.symm,
    fun h => ha (List.mem_toFinset.mp h)⟩
  have inter : (D.erase a) ∩ A = C := by
    ext z
    simp only [C,Finset.mem_inter,Finset.mem_erase]
    constructor
    · rintro ⟨⟨_,hd⟩,hA⟩
      exact ⟨hd,hA⟩
    · rintro ⟨hd,hA⟩
      exact ⟨⟨fun eq => G.irrefl (eq ▸ (G.mem_neighborFinset a z).mp hA),hd⟩,hA⟩
  have part₁ := Finset.card_sdiff_add_card_inter B P
  have part₂ := Finset.card_erase_add_one ain
  have part₃ := Finset.card_sdiff_add_card_inter (D.erase a) A
  rw [inter] at part₃
  change X.card+C.card=(D.erase a).card at part₃
  have shell (z : V) (hz : z∈X) : G.dist a z=2 := by
    obtain ⟨hD,hA⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨ne,hd⟩ := Finset.mem_erase.mp hD
    have hzB := (Finset.mem_sdiff.mp hd).1
    exact two_step_metric ne.symm (fun hadj => hA ((G.mem_neighborFinset a z).mpr hadj)) ab
      ((G.mem_neighborFinset b z).mp hzB).symm
  have dis : Disjoint Q X := Finset.disjoint_left.mpr (by
    intro z hQ hX
    have dm := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hX).1).2
    exact (Finset.mem_sdiff.mp dm).2 (Finset.mem_filter.mp hQ).1)
  have incl : Q ∪ X ⊆ Finset.univ.filter (fun z => G.dist a z=2) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_union.mp hz with h | h
    · exact (Finset.mem_filter.mp h).2
    · exact shell z h
  have total := (Finset.card_le_card incl).trans quota
  rw [Finset.card_union_of_disjoint dis] at total
  change D.card+(B∩P).card=B.card at part₁
  change (A∩P).card+B.card ≤ k+1+C.card
  omega
theorem cross_contact_degree (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    (G.neighborFinset a ∩ p.support.toFinset).card + G.degree b ≤
      k+(G.neighborFinset a \ p.support.toFinset).card := by
  classical
  let P := p.support.toFinset
  let A := G.neighborFinset a
  let B := G.neighborFinset b
  let C := (B \ P) ∩ A
  have bound := exterior_contact_degree p hp longest ha hb ab quota
  change (A∩P).card+G.degree b ≤ k+1+C.card at bound
  have absent : b∉C := by
    intro h
    have nb := (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).1).1
    exact G.irrefl ((G.mem_neighborFinset _ _).mp nb)
  have share : insert b C ⊆ A \ P := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | h
    · exact Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ab,
        fun h => hb (List.mem_toFinset.mp h)⟩
    · obtain ⟨hD,hA⟩ := Finset.mem_inter.mp h
      exact Finset.mem_sdiff.mpr ⟨hA,(Finset.mem_sdiff.mp hD).2⟩
  have count := Finset.card_le_card share
  rw [Finset.card_insert_of_notMem absent] at count
  change (A∩P).card+G.degree b ≤ k+(A \ P).card
  omega
theorem half_degree_outside_longest (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k)
    (high : k ≤ G.degree b) :
    G.degree a ≤ 2*(G.neighborFinset a \ p.support.toFinset).card := by
  have cross := cross_contact_degree p hp longest ha hb ab quota
  have parts := Finset.card_sdiff_add_card_inter (G.neighborFinset a) p.support.toFinset
  change (G.neighborFinset a).card ≤ 2*(G.neighborFinset a \ p.support.toFinset).card
  omega
end Graph189ExteriorGap
end
section
namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset Graph189ExteriorGap Graph189UniversalCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
theorem deletion_exterior_local_degree {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (w : V) {u v : {x : V | x ≠ w}}
    (p : (G.induce {x : V | x ≠ w}).Walk u v) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : (G.induce {x : V | x ≠ w}).Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : {x : V | x ≠ w}} (ha : a ∉ p.support) (hb : b ∉ p.support)
    (edge : (G.induce {x : V | x ≠ w}).Adj a b) {k D : ℕ}
    (cap : G.distEven a.val ≤ k+1) (da : D+1 ≤ G.degree a.val) (db : D+1 ≤ G.degree b.val) :
    2*D ≤ k+2*((G.induce {x : V | x ≠ w}).neighborFinset a \ p.support.toFinset).card := by
  classical
  let H := G.induce {x : V | x ≠ w}
  have quota := induced_second_layer (G:=G) {x : V | x ≠ w} a cap
  have contact := cross_contact_degree p hp longest ha hb edge quota
  have split := card_sdiff_add_card_inter (H.neighborFinset a) p.support.toFinset
  rw [H.card_neighborFinset_eq_degree] at split
  have ax := degree_le_deletion_add_one (G:=G) w a
  have by' := degree_le_deletion_add_one (G:=G) w b
  change G.degree a.val ≤ H.degree a+1 at ax
  change G.degree b.val ≤ H.degree b+1 at by'
  change (H.neighborFinset a ∩ p.support.toFinset).card+H.degree b ≤
    k+(H.neighborFinset a \ p.support.toFinset).card at contact
  change 2*D ≤ k+2*(H.neighborFinset a \ p.support.toFinset).card
  omega
theorem deletion_gap {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    (w : V) {x y : {u : V | u ≠ w}} (p : (G.induce {u : V | u ≠ w}).Walk x y)
    (hp : p.IsPath)
    (gap : ∀ a b, ∀ r : G.Walk a b, r.IsPath → r.support.length + 3 < Fintype.card V) :
    3 ≤ (univ.filter (fun v => v ∉ p.support)).card := by
  classical
  let S := {u : V | u ≠ w}
  let f := (Embedding.induce (G:=G) S).toHom
  have qpath := (Walk.isPath_map_iff_of_injective (p:=p) (f:=f) Subtype.val_injective).mpr hp
  have big := gap _ _ (p.map f) qpath
  rw [Walk.support_map,List.length_map] at big
  have part := card_filter_add_card_filter_not (s:=(univ : Finset S)) (p:=fun v => v ∈ p.support)
  have first : (univ.filter (fun v : S => v ∈ p.support)) = p.support.toFinset := by
    ext t
    simp
  rw [first,List.toFinset_card_of_nodup hp.support_nodup,card_univ] at part
  have sz : Fintype.card S = Fintype.card V - 1 := by
    change Fintype.card {u : V // ¬u = w} = Fintype.card V - 1
    rw [Fintype.card_subtype_compl (fun u : V => u = w),Fintype.card_subtype_eq]
  calc
    3 ≤ ((univ : Finset S).filter (fun t : S => ¬t ∈ p.support)).card := by omega
    _ = _ := by congr 1
theorem path_of_exterior_cycle {V : Type*} {G : SimpleGraph V} {a : V} (C : G.Walk a a)
    (hc : C.IsCycle) : C.dropLast.IsPath ∧ C.dropLast.support.length = C.length := by
  constructor
  · apply Walk.IsPath.mk'
    rw [C.support_dropLast hc.not_nil]
    exact hc.nodup_dropLast_support
  · have drop := C.length_dropLast_add_one hc.not_nil
    rw [C.dropLast.length_support]
    omega
end Graph189ExteriorDegreeCycle
end
section
open SimpleGraph Finset OMA.BondyK
namespace Graph189BondyExterior
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]
private theorem periodic_longest {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (longest : ∀ b (R : G.Walk b b), R.IsCycle → R.length ≤ C.length) : Cy G C.length (cyc C) := by
  have upper : ∀ m ∈ G.cycleLengths, m ≤ C.length := by
    rintro m ⟨b,R,hR,rfl⟩
    exact longest b R hR
  have max : C.length = G.circumference := by
    change C.length = sSup G.cycleLengths
    have mem : C.length ∈ G.cycleLengths := ⟨a,C,hC,rfl⟩
    exact (le_csSup ⟨C.length,upper⟩ mem).antisymm (csSup_le ⟨_,mem⟩ upper)
  exact cy_of C hC max
private theorem actual_component {a : V} (C : G.Walk a a) (hC : C.IsCycle) (u : offWalk C) :
    ∃ H : Finset V, Comp G (cyc C) H ∧
      ∀ y, y∈H ↔ ∃ hy : y∈offWalk C, (G.induce (offWalk C)).Reachable u ⟨y,hy⟩ := by
  have hsupp := mem_support_cyc C hC
  have mem_s : ∀ y, y ∈ offWalk C ↔ y ∉ C.support := fun y => Iff.rfl
  classical
  obtain ⟨H, hH⟩ : ∃ H : Finset V, H = Finset.univ.filter
      (fun y => ∃ hy : y ∈ offWalk C, (G.induce (offWalk C)).Reachable u ⟨y, hy⟩) := ⟨_, rfl⟩
  have memH : ∀ y, y ∈ H ↔ ∃ hy : y ∈ offWalk C, (G.induce (offWalk C)).Reachable u ⟨y, hy⟩ := by
    intro y; simp [hH]
  have hComp : Comp G (cyc C) H := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx t ht
      obtain ⟨hxs, -⟩ := (memH x).mp hx
      exact (mem_s x).mp hxs ((hsupp x).mpr ⟨t, ht⟩)
    · intro x hx y hxy
      obtain ⟨hxs, hr⟩ := (memH x).mp hx
      by_cases hy : y ∈ C.support
      · exact Or.inr ((hsupp y).mp hy)
      · left
        have hys : y ∈ offWalk C := (mem_s y).mpr hy
        exact (memH y).mpr ⟨hys, hr.trans (Adj.reachable (G := G.induce (offWalk C))
          (u := ⟨x, hxs⟩) (v := ⟨y, hys⟩) hxy)⟩
    · intro x hx y hy
      obtain ⟨hxs, hrx⟩ := (memH x).mp hx
      obtain ⟨hys, hry⟩ := (memH y).mp hy
      obtain ⟨w⟩ := hrx.symm.trans hry
      obtain ⟨p, hp⟩ := w.toPath
      refine ⟨p.support.map Subtype.val, ?_, ?_, ?_, ?_, ?_⟩
      · exact hp.support_nodup.map Subtype.val_injective
      · exact (List.isChain_map Subtype.val).mpr p.isChain_adj_support
      · intro z hz
        obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
        exact (memH z').mpr ⟨z'.2, hrx.trans (reach_mem p hz')⟩
      · rw [Walk.support_eq_cons, List.map_cons, List.head?_cons]
      · rw [List.getLast?_map, List.getLast?_eq_getLast_of_ne_nil (Walk.support_ne_nil _),
          Walk.getLast_support]; rfl
  exact ⟨H,hComp,memH⟩
private theorem separator_of_connectivity {k : ℕ} (conn : k ≤ G.vertexConnectivity) : KSep G k := by
  intro S hS X hXS hXcl hXne y hyS hyX
  obtain ⟨x, hx⟩ := hXne
  have hconn := Graph189CutSides.connected_after_smaller_deletion (G:=G) S (by omega)
  obtain ⟨w⟩ := hconn.preconnected ⟨x, hXS x hx⟩ ⟨y, hyS⟩
  have key : ∀ (p q : ((S : Set V)ᶜ : Set V)) (w : (G.induce ((S : Set V)ᶜ)).Walk p q),
      p.1 ∈ X → q.1 ∈ X := by
    intro p q w
    induction w with
    | nil => exact id
    | @cons p0 p1 q h w ih =>
      intro hp
      exact ih (hXcl _ hp _ h (fun h' => p1.2 h'))
  exact hyX (key _ _ w hx)
theorem excludes_long_exterior {k : ℕ} (positive : 1 ≤ k)
    (conn : k ≤ G.vertexConnectivity)
    (degree : Fintype.card V + k*(k-1) ≤ (k+1)*G.minDegree)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (longest : ∀ b (R : G.Walk b b), R.IsCycle → R.length ≤ C.length)
    {u : {t : V | t ∉ C.support}} (Q : (G.induce {t : V | t ∉ C.support}).Walk u u)
    (hQ : Q.IsCycle) (size : k+1 ≤ Q.length) (twice : 2*k ≤ Q.length+2) : False := by
  classical
  have hD := periodic_longest C hC longest
  obtain ⟨H,hComp,memH⟩ := actual_component C hC u
  let P := Q.dropLast
  have hP : P.IsPath := hQ.isPath_dropLast
  have hVL : VL G H (P.support.map Subtype.val) := by
    refine ⟨hP.support_nodup.map Subtype.val_injective,
      (List.isChain_map Subtype.val).mpr P.isChain_adj_support, ?_⟩
    intro z hz
    obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
    exact (memH z').mpr ⟨z'.2, reach_mem P hz'⟩
  have len : (P.support.map Subtype.val).length = Q.length := by
    simpa [P] using (Graph189ExteriorDegreeCycle.path_of_exterior_cycle Q hQ).2
  have first : (P.support.map Subtype.val).head? = some u.val := by
    rw [←P.cons_tail_support,List.map_cons,List.head?_cons]
  have last : (P.support.map Subtype.val).getLast? = some Q.penultimate.val := by
    rw [List.getLast?_map,List.getLast?_eq_getLast_of_ne_nil (Walk.support_ne_nil _),Walk.getLast_support]
    rfl
  have closure : ∀ b ∈ (P.support.map Subtype.val).getLast?, ∀ a ∈ (P.support.map Subtype.val).head?,
      G.Adj b a := by
    intro b hb a ha
    rw [first] at ha
    rw [last] at hb
    rw [Option.mem_def,Option.some.injEq] at ha hb
    subst a b
    exact Walk.adj_penultimate hQ.not_nil
  let M := (P.support.map Subtype.val).toFinset
  have card : M.card = Q.length := (List.toFinset_card_of_nodup hVL.1).trans len
  exact linked_contra hD hComp (fun v => G.minDegree_le_degree v) positive degree (separator_of_connectivity conn) (D:=M)
    (fun v hv => hVL.2.2 v (List.mem_toFinset.mp hv)) (by omega)
    (cyc_linked hVL closure (by omega))
private theorem degree_of_short {n d k : ℕ} (pos : 1 ≤ k) (min : k ≤ d)
    (short : n < (k+1)*(d-k+2)-1) : n+k*(k-1) ≤ (k+1)*d := by
  have step : n+2 ≤ (k+1)*(d-k+2) := by omega
  obtain ⟨m,hd⟩ := Nat.exists_eq_add_of_le min
  rw [hd,Nat.add_sub_cancel_left] at step
  rw [hd]
  obtain ⟨h,hl⟩ := Nat.exists_eq_add_of_le pos
  rw [hl,Nat.add_sub_cancel_left]
  rw [hl] at step
  nlinarith
theorem order_of_long_exterior {k : ℕ} (pos : 1 ≤ k) (conn : k ≤ G.vertexConnectivity)
    (min : k ≤ G.minDegree) {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (longest : ∀ b (R : G.Walk b b), R.IsCycle → R.length ≤ C.length)
    {u : {t : V | t ∉ C.support}} (Q : (G.induce {t : V | t ∉ C.support}).Walk u u)
    (hQ : Q.IsCycle) (size : k+1 ≤ Q.length) (twice : 2*k ≤ Q.length+2) :
    (k+1)*(G.minDegree-k+2)-1 ≤ Fintype.card V := by
  by_contra! short
  apply excludes_long_exterior pos conn _ C hC longest Q hQ size twice
  exact degree_of_short pos min short
end Graph189BondyExterior
end
section
namespace Graph189ExteriorGap
open SimpleGraph Finset
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
theorem single_positions_lt_path_shell (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (ha : a ∉ p.support) (touch : (contactPositions p a).Nonempty) :
    (contactPositions p a).card + 1 ≤
      (p.support.toFinset.filter (fun v => G.dist a v = 2)).card := by
  classical
  let A := contactPositions p a
  let m := A.max' touch
  have hm : m ∈ A := Finset.max'_mem _ _
  have internal (i : ℕ) (hi : i ∈ A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    exact omitted_contact_internal p hp longest ha ⟨i,ri⟩ (by simpa [get_at] using ci)
  have spaced (i j : ℕ) (hi : i ∈ A) (hj : j ∈ A) (lt : i < j) : i+2 ≤ j := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p a j).mp hj
    exact omitted_contact_spacing p hp longest ha ⟨i,ri⟩ ⟨j,rj⟩ lt
      (by simpa [get_at] using ci) (by simpa [get_at] using cj)
  let B := A.image (fun i => i-1)
  let W := insert (m+1) B
  have different (i : ℕ) : a ≠ p.getVert i := fun eq => ha (eq ▸ p.getVert_mem_support i)
  have ls := p.length_support
  have via (i j : ℕ) (hi : i < p.support.length) (hj : j ∈ A) (no : i ∉ A)
      (edge : G.Adj (p.getVert i) (p.getVert j)) : G.dist a (p.getVert i) = 2 := by
    have c := ((mem_contactPositions p a j).mp hj).2
    exact two_step_metric (different _) (fun h => no ((mem_contactPositions p a i).mpr ⟨hi,h.symm⟩)) c.symm edge
  have valid (i : ℕ) (hi : i ∈ W) : i < p.support.length ∧ G.dist a (p.getVert i) = 2 := by
    rcases mem_insert.mp hi with rfl|h
    · have ht := (internal m hm).2
      refine ⟨ht,via _ m ht hm (fun mem => ?_) ((p.adj_getVert_succ (i:=m) (by omega)).symm)⟩
      have := spaced m (m+1) hm mem (by omega)
      omega
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp h
      obtain ⟨positive,back⟩ := internal j hj
      have lim : j-1 < p.support.length := by omega
      refine ⟨lim,via _ j lim hj (fun mem => ?_) ?_⟩
      · have := spaced (j-1) j mem hj (by omega)
        omega
      · have edge := p.adj_getVert_succ (i:=j-1) (by omega)
        rwa [show j-1+1=j by omega] at edge
  have maxoutside : m+1 ∉ B := by
    intro h
    obtain ⟨i,hi,eq⟩ := mem_image.mp h
    have lim : i ≤ m := Finset.le_max' _ _ hi
    omega
  have predinj : Set.InjOn (fun i : ℕ => i-1) (A : Set ℕ) := by
    intro i hi j hj eq
    have := (internal i hi).1
    have := (internal j hj).1
    change i-1=j-1 at eq
    omega
  have nodeinj : Set.InjOn p.getVert (W : Set ℕ) := by
    intro i hi j hj eq
    exact hp.getVert_injOn (by change i ≤ p.length; have := (valid i hi).1; omega)
      (by change j ≤ p.length; have := (valid j hj).1; omega) eq
  have sub : W.image p.getVert ⊆ p.support.toFinset.filter (fun v => G.dist a v = 2) := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support _),(valid i hi).2⟩
  have count := card_le_card sub
  rw [card_image_of_injOn nodeinj,show W = insert (m+1) B from rfl,card_insert_of_notMem maxoutside,
    show B = A.image (fun i => i-1) from rfl,card_image_of_injOn predinj] at count
  exact count
end Graph189ExteriorGap
end
section
namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset Graph189ExteriorGap
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
private theorem count_two {V : Type*} [Fintype V] {G : SimpleGraph V} (U : Finset V) {x : V} {k : ℕ}
    (two : ∀ v ∈ U, G.dist x v = 2) (cap : G.distEven x ≤ k+1) : U.card ≤ k := by
  classical
  have nx : x ∉ U := by intro hx; have h := two _ hx; simp at h
  have sub : insert x U ⊆ univ.filter (fun v => Even (G.dist x v)) := by
    intro v hv
    apply mem_filter.mpr
    refine ⟨mem_univ _,?_⟩
    rcases mem_insert.mp hv with rfl|h
    · simp
    · rw [two v h]; decide
  have bound := card_le_card sub
  rw [card_insert_of_notMem nx] at bound
  change U.card+1 ≤ G.distEven x at bound
  omega
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem high_isolated_saturation (w : V) {x y : {u : V | u ≠ w}}
    (p : (G.induce {u : V | u ≠ w}).Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : (G.induce {u : V | u ≠ w}).Walk u v, r.IsPath → r.length ≤ p.length)
    (a : {u : V | u ≠ w}) (outside : a ∉ p.support)
    (isolated : ∀ b, (G.induce {u : V | u ≠ w}).Adj a b → b ∈ p.support)
    {k : ℕ} (pos : 2 ≤ k) (high : k ≤ G.degree a.val) (cap : G.distEven a.val ≤ k+1) :
    G.Adj a.val w ∧
    (p.support.toFinset.filter (fun v => (G.induce {u : V | u ≠ w}).dist a v = 2)).card = k := by
  classical
  let H := G.induce {u : V | u ≠ w}
  have sub : H.neighborFinset a ⊆ p.support.toFinset := by
    intro b hb
    exact List.mem_toFinset.mpr (isolated b ((H.mem_neighborFinset _ _).mp hb))
  have size : (contactPositions p a).card = H.degree a := by
    rw [contact_card_neighbors p hp,inter_eq_left.mpr sub,H.card_neighborFinset_eq_degree]
  have lost := degree_le_deletion_add_one (G:=G) w a
  change G.degree a.val ≤ H.degree a + 1 at lost
  have touch : (contactPositions p a).Nonempty := card_pos.mp (by omega)
  have least := single_positions_lt_path_shell p hp longest outside touch
  rw [size] at least
  let Q := p.support.toFinset.filter (fun v => H.dist a v = 2)
  have small : Q.card ≤ k := by
    have incl : Q ⊆ exactTwo H a := fun _ h => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp h).2⟩
    exact (card_le_card incl).trans (induced_second_layer _ a cap)
  change H.degree a+1 ≤ Q.card at least
  refine ⟨?_,by change Q.card = k; omega⟩
  by_contra no
  have same : H.degree a = G.degree a.val := by
    rw [degree_induce_filter]
    have eq : (G.neighborFinset a.val).filter (fun u => u ∈ {v : V | v ≠ w}) =
        G.neighborFinset a.val := by
      apply filter_eq_self.mpr
      intro v hv h
      exact no (Eq.mp (congrArg (G.Adj a.val) h) ((G.mem_neighborFinset a.val v).mp hv))
    rw [eq,G.card_neighborFinset_eq_degree]
  omega
theorem unique_high_isolated (w : V) {x y : {u : V | u ≠ w}}
    (p : (G.induce {u : V | u ≠ w}).Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : (G.induce {u : V | u ≠ w}).Walk u v, r.IsPath → r.length ≤ p.length)
    (independent : ∀ a ∉ p.support, ∀ b ∉ p.support, ¬ (G.induce {u : V | u ≠ w}).Adj a b)
    {k : ℕ} (pos : 2 ≤ k) (cap : ∀ v, G.distEven v ≤ k+1)
    {a b : {u : V | u ≠ w}} (ha : a ∉ p.support) (hb : b ∉ p.support)
    (ahigh : k ≤ G.degree a.val) (bhigh : k ≤ G.degree b.val) : a = b := by
  classical
  by_contra diff
  have isolated (c : {u : V | u ≠ w}) (hc : c ∉ p.support) (t : {u : V | u ≠ w})
      (adj : (G.induce {u : V | u ≠ w}).Adj c t) : t ∈ p.support := by
    by_contra h
    exact independent c hc t h adj
  obtain ⟨aw,full⟩ := high_isolated_saturation w p hp longest a ha (isolated a ha) pos ahigh (cap a.val)
  obtain ⟨bw,_⟩ := high_isolated_saturation w p hp longest b hb (isolated b hb) pos bhigh (cap b.val)
  have extTwo : G.dist a.val b.val = 2 := two_step_metric
    (fun eq => diff (Subtype.ext eq)) (independent a ha b hb) aw bw
  let f : {u : V | u ≠ w} ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let Q := p.support.toFinset.filter (fun v => (G.induce {u : V | u ≠ w}).dist a v = 2)
  have missing : b.val ∉ Q.map f := by
    intro h
    obtain ⟨t,ht,eq⟩ := mem_map.mp h
    have same : t = b := Subtype.ext eq
    exact hb (same ▸ List.mem_toFinset.mp (mem_filter.mp ht).1)
  have cost := count_two (insert b.val (Q.map f)) (x:=a.val) (k:=k) (by
    intro v hv
    rcases mem_insert.mp hv with rfl|hm
    · exact extTwo
    · obtain ⟨t,ht,rfl⟩ := mem_map.mp hm
      exact original_dist_two (mem_filter.mp ht).2) (cap a.val)
  rw [card_insert_of_notMem missing,card_map] at cost
  change Q.card=k at full
  omega
theorem independent_omits_at_most_two [Nontrivial V] (w : V) {x y : {u : V | u ≠ w}}
    (p : (G.induce {u : V | u ≠ w}).Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : (G.induce {u : V | u ≠ w}).Walk u v, r.IsPath → r.length ≤ p.length)
    (independent : ∀ a ∉ p.support, ∀ b ∉ p.support, ¬ (G.induce {u : V | u ≠ w}).Adj a b)
    (pos : 2 ≤ G.secondSmallestDegree) (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) :
    (univ.filter (fun v => v ∉ p.support)).card ≤ 2 := by
  classical
  let X := univ.filter (fun v => v ∉ p.support)
  let high (a : {u : V | u ≠ w}) := G.secondSmallestDegree ≤ G.degree a.val
  have one : (X.filter high).card ≤ 1 := by
    apply card_le_one_iff.mpr
    intro a b ha hb
    obtain ⟨ha,ah⟩ := mem_filter.mp ha
    obtain ⟨hb,bh⟩ := mem_filter.mp hb
    exact unique_high_isolated w p hp longest independent pos cap (mem_filter.mp ha).2 (mem_filter.mp hb).2 ah bh
  have low : (X.filter (fun a => ¬high a)).card ≤ 1 := by
    apply card_le_one_iff.mpr
    intro a b ha hb
    by_contra h
    have vne : a.val ≠ b.val := fun eq => h (Subtype.ext eq)
    exact (degree_pair (G:=G) a.val b.val vne).elim (mem_filter.mp ha).2 (mem_filter.mp hb).2
  have part := card_filter_add_card_filter_not (s:=X) (p:=high)
  change X.card ≤ 2
  omega
end Graph189ExteriorDegreeCycle
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
theorem adjacent_ambient_degree_sum (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    G.degree a + G.degree b ≤ k+2*(G.neighborFinset a \ p.support.toFinset).card := by
  have cross := cross_contact_degree p hp longest ha hb ab quota
  have parts := Finset.card_sdiff_add_card_inter (G.neighborFinset a) p.support.toFinset
  change (G.neighborFinset a).card + G.degree b ≤ k+2*(G.neighborFinset a \ p.support.toFinset).card
  omega
theorem nonisolated_exterior_half (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (ha : a∉p.support) (nonisolated : (G.neighborFinset a \ p.support.toFinset).Nonempty)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k)
    (high : k ≤ G.degree a) (minimum : ∀ v : V, 3 ≤ G.degree v)
    (uniqueLow : ∀ u v : V, G.degree u < k → G.degree v < k → u=v) :
    (∃ b : V, b∉p.support ∧ G.Adj a b ∧ k ≤ G.degree b) ∧
      G.degree a ≤ 2*(G.neighborFinset a \ p.support.toFinset).card := by
  let E := G.neighborFinset a \ p.support.toFinset
  have member (z : V) (hz : z∈E) : z∉p.support ∧ G.Adj a z :=
    ⟨fun h => (Finset.mem_sdiff.mp hz).2 (List.mem_toFinset.mpr h),
      (G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp hz).1⟩
  obtain ⟨w,hw⟩ := nonisolated
  obtain ⟨hwo,aw⟩ := member w hw
  have sum := adjacent_ambient_degree_sum p hp longest ha hwo aw quota
  have card : 1 < E.card := by
    change G.degree a + G.degree w ≤ k + 2*E.card at sum
    have := minimum w
    omega
  obtain ⟨s,hs,t,ht,ne⟩ := Finset.one_lt_card.mp card
  have good : ∃ b∈E, k ≤ G.degree b := by
    by_cases highS : k ≤ G.degree s
    · exact ⟨s,hs,highS⟩
    · refine ⟨t,ht,?_⟩
      by_contra! lowT
      exact ne (uniqueLow s t (by omega) lowT)
  obtain ⟨b,hb,highB⟩ := good
  obtain ⟨off,adj⟩ := member b hb
  exact ⟨⟨b,off,adj,highB⟩,half_degree_outside_longest p hp longest ha off adj quota highB⟩
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}
def ExteriorRoute (p : G.Walk x y) (a b : V) (k : ℕ) : Prop :=
  ∃ q : G.Walk a b, q.IsPath ∧ List.Disjoint q.support p.support ∧ k ≤ q.support.length
theorem longest_matched_route_order (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    {j middle left right : ℕ} (mark : Fin (j+1) ↪o Fin p.support.length)
    (port : Fin (j+1) → V) (contacts : ∀ i, G.Adj p.support[(mark i).val] (port i))
    (inner : ∀ i : Fin j, ExteriorRoute p (port i.castSucc) (port i.succ) middle)
    (before : ∃ a, ExteriorRoute p a (port 0) left)
    (after : ∃ b, ExteriorRoute p (port (Fin.last j)) b right) :
    left + j*(middle+1) + 1 + right ≤ p.support.length := by
  obtain ⟨a,q,hq,hdis,hlen⟩ := before
  have hfirst := prefix_of_detour p hp longest (mark 0) q hq hdis (contacts 0).symm
  obtain ⟨b,r,hr,hother,hend⟩ := after
  have hlast := suffix_of_detour p hp longest (mark (Fin.last j)) r hr hother (contacts _)
  have spread (i : Fin j) : (mark i.castSucc).val + 1 + middle ≤ (mark i.succ).val := by
    obtain ⟨t,ht,hd,hm⟩ := inner i
    have bound := interval_of_detour p hp longest _ _ (mark.strictMono i.castSucc_lt_succ)
      t ht hd (contacts _) (contacts _).symm
    omega
  have positions : ∀ i : Fin (j+1), left+i.val*(middle+1) ≤ (mark i).val := by
    intro i
    induction i using Fin.induction with
    | zero => simpa using hlen.trans hfirst
    | succ i ih =>
      have step := spread i
      simp only [Fin.val_succ,Fin.val_castSucc,Nat.succ_mul] at ih ⊢
      omega
  have last := positions (Fin.last j)
  simp only [Fin.val_last] at last
  omega
theorem card_outside_add_path [Fintype V] [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (W : Finset V) (outside : ∀ z∈W, z∉p.support) :
    W.card+p.support.length ≤ Fintype.card V := by
  have dis : Disjoint W p.support.toFinset := Finset.disjoint_left.mpr (by
    intro z hz h
    exact outside z hz (List.mem_toFinset.mp h))
  have bound := (W ∪ p.support.toFinset).card_le_univ
  rw [Finset.card_union_of_disjoint dis,List.toFinset_card_of_nodup hp.support_nodup] at bound
  exact bound
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
theorem high_exterior_half (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (ha : a∉p.support) {k : ℕ}
    (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k)
    (high : k ≤ G.degree a) (minimum : ∀ v : V, 3 ≤ G.degree v)
    (uniqueLow : ∀ u v : V, G.degree u < k → G.degree v < k → u=v) :
    (∃ b : V, b∉p.support ∧ G.Adj a b ∧ k ≤ G.degree b) ∧
      G.degree a ≤ 2*(G.neighborFinset a \ p.support.toFinset).card := by
  classical
  apply nonisolated_exterior_half p hp longest ha _ quota high minimum uniqueLow
  by_contra! empty
  have parts := Finset.card_sdiff_add_card_inter (G.neighborFinset a) p.support.toFinset
  rw [empty,Finset.card_empty,zero_add] at parts
  have num := contact_card_neighbors p hp a
  have min := minimum a
  change 3 ≤ (G.neighborFinset a).card at min
  have touch : (contactPositions p a).Nonempty := Finset.card_pos.mp (by omega)
  have shift := single_positions_lt_path_shell p hp longest ha touch
  have sub : p.support.toFinset.filter (fun z => G.dist a z=2) ⊆
      Finset.univ.filter (fun z => G.dist a z=2) := by
    intro z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hz).2⟩
  have size := (Finset.card_le_card sub).trans quota
  change k ≤ (G.neighborFinset a).card at high
  omega
end Graph189ExteriorGap
end
section
namespace Graph189ExteriorGap
open SimpleGraph Finset
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
theorem double_positions_le_path_shell (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length)
    {a : V} (ha : a ∉ p.support) (wide : ∀ i∈contactPositions p a, ∀ j∈contactPositions p a, i < j → i+3 ≤ j) :
    2 * (contactPositions p a).card ≤
      (p.support.toFinset.filter (fun v => G.dist a v = 2)).card := by
  classical
  let A := contactPositions p a
  have internal (i : ℕ) (hi : i ∈ A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    exact omitted_contact_internal p hp longest ha ⟨i,ri⟩ (by simpa [get_at] using ci)
  have spaced (i j : ℕ) (hi : i ∈ A) (hj : j ∈ A) (lt : i < j) : i+2 ≤ j := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p a j).mp hj
    exact omitted_contact_spacing p hp longest ha ⟨i,ri⟩ ⟨j,rj⟩ lt
      (by simpa [get_at] using ci) (by simpa [get_at] using cj)
  let B := A.image (fun i => i-1)
  let F := A.image (fun i => i+1)
  let W := F ∪ B
  have different (i : ℕ) : a ≠ p.getVert i := fun eq => ha (eq ▸ p.getVert_mem_support i)
  have ls := p.length_support
  have via (i j : ℕ) (hi : i < p.support.length) (hj : j ∈ A) (no : i ∉ A)
      (edge : G.Adj (p.getVert i) (p.getVert j)) : G.dist a (p.getVert i) = 2 := by
    have c := ((mem_contactPositions p a j).mp hj).2
    exact two_step_metric (different _) (fun h => no ((mem_contactPositions p a i).mpr ⟨hi,h.symm⟩)) c.symm edge
  have valid (i : ℕ) (hi : i ∈ W) : i < p.support.length ∧ G.dist a (p.getVert i) = 2 := by
    rcases mem_union.mp hi with h|h
    · obtain ⟨m,hm,rfl⟩ := mem_image.mp h
      have ht := (internal m hm).2
      refine ⟨ht,via _ m ht hm (fun mem => ?_) ((p.adj_getVert_succ (i:=m) (by omega)).symm)⟩
      have := spaced m (m+1) hm mem (by omega)
      omega
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp h
      obtain ⟨positive,back⟩ := internal j hj
      have lim : j-1 < p.support.length := by omega
      refine ⟨lim,via _ j lim hj (fun mem => ?_) ?_⟩
      · have := spaced (j-1) j mem hj (by omega)
        omega
      · have edge := p.adj_getVert_succ (i:=j-1) (by omega)
        rwa [show j-1+1=j by omega] at edge
  have disjoint : Disjoint F B := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    obtain ⟨i,hi,ei⟩ := mem_image.mp hv
    obtain ⟨j,hj,ej⟩ := mem_image.mp hw
    have := (internal j hj).1
    change i+1=v at ei
    change j-1=v at ej
    have := wide i hi j hj (by omega)
    omega
  have predinj : Set.InjOn (fun i : ℕ => i-1) (A : Set ℕ) := by
    intro i hi j hj eq
    have := (internal i hi).1
    have := (internal j hj).1
    change i-1=j-1 at eq
    omega
  have nodeinj : Set.InjOn p.getVert (W : Set ℕ) := by
    intro i hi j hj eq
    exact hp.getVert_injOn (by change i ≤ p.length; have := (valid i hi).1; omega)
      (by change j ≤ p.length; have := (valid j hj).1; omega) eq
  have sub : W.image p.getVert ⊆ p.support.toFinset.filter (fun v => G.dist a v = 2) := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support _),(valid i hi).2⟩
  have count := card_le_card sub
  rw [card_image_of_injOn nodeinj,show W = F ∪ B from rfl,card_union_of_disjoint disjoint,
    show B = A.image (fun i => i-1) from rfl,card_image_of_injOn predinj,
    show F = A.image (fun i => i+1) from rfl,card_image_of_injective _ (show Function.Injective (fun i : ℕ => i+1) by
      intro i j eq; change i+1=j+1 at eq; omega)] at count
  change 2*A.card ≤ _
  omega
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
private theorem replace_position (p : G.Walk x y) (hp : p.IsPath) (A B : List V)
    (mid a : V) (split : p.support=A++mid::B) (outside : a∉p.support)
    (left : ∀ z∈A.getLast?, G.Adj z a) (right : ∀ z∈B.head?, G.Adj a z) :
    ∃ u v, ∃ q : G.Walk u v, q.IsPath ∧ q.length=p.length ∧
      q.support.toFinset=insert a (p.support.toFinset.erase mid) := by
  have nd := hp.support_nodup
  have chain := p.isChain_adj_support
  rw [split] at nd chain outside
  have ndA := nd.of_append_left
  have ndMB := nd.of_append_right
  have ndB := (List.nodup_cons.mp ndMB).2
  have midB := (List.nodup_cons.mp ndMB).1
  have midA : mid∉A := fun h => List.disjoint_left.mp nd.disjoint h (by simp)
  have aA : a∉A := fun h => outside (List.mem_append_left _ h)
  have aB : a∉B := fun h => outside (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  let L := A++a::B
  have fresh : L.Nodup := by
    refine List.Nodup.append ndA (List.nodup_cons.mpr ⟨aB,ndB⟩) ?_
    rw [List.disjoint_left]
    intro z hz hz'
    rcases List.mem_cons.mp hz' with rfl | inB
    · exact aA hz
    · exact List.disjoint_left.mp nd.disjoint hz (List.mem_cons_of_mem _ inB)
  have rightChain : (a::B).IsChain G.Adj := chain.right_of_append.of_cons.cons right
  have adjacent : L.IsChain G.Adj := by
    apply chain.left_of_append.append rightChain
    intro z hz w hw
    have same : a=w := by simpa using hw
    exact same ▸ left z hz
  have hn : L≠[] := by simp [L]
  let q := Walk.ofSupport L hn adjacent
  have qs : q.support=L := Walk.support_ofSupport hn adjacent
  refine ⟨_,_,q,Walk.IsPath.mk' (by rwa [qs]),?_,?_⟩
  · have ql := q.length_support
    have pl := p.length_support
    rw [qs] at ql
    rw [split] at pl
    simp only [L,List.length_append,List.length_cons] at ql pl
    omega
  · ext z
    simp only [qs,split,L,List.mem_toFinset,Finset.mem_insert,Finset.mem_erase,List.mem_append,List.mem_cons]
    by_cases eq : z=mid
    · subst z
      simp [midA,midB]
    · simp [eq]
      tauto
theorem swap_contact_midpoint (p : G.Walk x y) (hp : p.IsPath) {a : V} (outside : a∉p.support)
    (i : ℕ) (lastValid : i+2 < p.support.length)
    (left : G.Adj (p.getVert i) a) (right : G.Adj (p.getVert (i+2)) a) :
    ∃ u v, ∃ q : G.Walk u v, q.IsPath ∧ q.length=p.length ∧
      q.support.toFinset=insert a (p.support.toFinset.erase (p.getVert (i+1))) := by
  let L := p.support
  let A := L.take (i+1)
  let B := L.drop (i+2)
  have mid : i+1 < L.length := by dsimp [L]; omega
  have first : i < L.length := by dsimp [L]; omega
  have pl : L=A++L[i+1]::B := by
    change L=L.take (i+1)++L[i+1]::L.drop (i+2)
    rw [←List.drop_eq_getElem_cons mid,List.take_append_drop]
  have lastA : A.getLast?=some L[i] :=
    (congrArg List.getLast? (List.take_succ_eq_append_getElem first)).trans List.getLast?_concat
  have firstB : B.head?=some L[i+2] := by simp [B,List.head?_drop]
  have changed := replace_position p hp A B L[i+1] a pl outside (by
    intro z hz
    rw [lastA] at hz
    have eq : L[i]=z := by simpa using hz
    exact eq ▸ (by simpa [L,get_at] using left)) (by
    intro z hz
    rw [firstB] at hz
    have eq : L[i+2]=z := by simpa using hz
    exact eq ▸ (by simpa [L,get_at] using right.symm))
  simpa [L,get_at] using changed
end Graph189ExteriorGap
end
section
namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset Graph189ExteriorGap
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
private theorem exact_quota {V : Type*} [Fintype V] {G : SimpleGraph V} (a : V) {k : ℕ} (cap : G.distEven a ≤ k+1) :
    (exactTwo G a).card ≤ k := by
  classical
  let T := exactTwo G a
  have missing : a ∉ T := by
    intro h
    have two : G.dist a a=2 := (mem_filter.mp h).2
    simp at two
  have cover : insert a T ⊆ univ.filter (fun z => Even (G.dist a z)) := by
    intro v hv
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    rcases mem_insert.mp hv with rfl|h
    · simp
    · rw [show G.dist a v=2 from (mem_filter.mp h).2]; decide
  have sz := card_le_card cover
  rw [card_insert_of_notMem missing] at sz
  change T.card+1 ≤ G.distEven a at sz
  change T.card ≤ k
  omega
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
private theorem no_high_off_almost_longest {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (longest : ∀ {x y}, ∀ r : G.Walk x y, r.IsPath → r.length ≤ p.length)
    (near : Fintype.card V ≤ p.support.length+3)
    (k5 : 5 ≤ G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (minimum : ∀ v, 3 ≤ G.degree v) {x : V} (hx : x ∉ p.support) :
    G.degree x < G.secondSmallestDegree := by
  classical
  by_contra! hi
  have uq (a b : V) (ha : G.degree a < G.secondSmallestDegree) (hb : G.degree b < G.secondSmallestDegree) :
      a=b := by
    by_contra h
    exact (degree_pair (G:=G) a b h).elim (fun h => by omega) (fun h => by omega)
  obtain ⟨_,half⟩ := high_exterior_half p hp longest hx (exact_quota x (cap x)) hi minimum uq
  let T := univ \ p.support.toFinset
  have sz : T.card + p.support.length = Fintype.card V := by
    have h := card_sdiff_add_card_inter (univ : Finset V) p.support.toFinset
    rwa [univ_inter,List.toFinset_card_of_nodup hp.support_nodup,card_univ] at h
  have xin : x ∈ T := mem_sdiff.mpr ⟨mem_univ _,fun h => hx (List.mem_toFinset.mp h)⟩
  have sub : G.neighborFinset x \ p.support.toFinset ⊆ T.erase x := by
    intro y hy
    obtain ⟨edge,off⟩ := mem_sdiff.mp hy
    exact mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp edge).ne.symm,mem_sdiff.mpr ⟨mem_univ _,off⟩⟩
  have bound := card_le_card sub
  have one := card_erase_add_one xin
  omega
theorem near_longest_has_hamiltonian_low_deletion {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (longest : ∀ {x y}, ∀ r : G.Walk x y, r.IsPath → r.length ≤ p.length)
    (near : Fintype.card V ≤ p.support.length+3)
    (notTrace : ¬ ∃ x y, ∃ q : G.Walk x y, q.IsHamiltonian)
    (k5 : 5 ≤ G.secondSmallestDegree) (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (minimum : ∀ v : V, 3 ≤ G.degree v) :
    ∃ z : V, G.degree z < G.secondSmallestDegree ∧
      ∃ x y, ∃ q : (G.induce {a : V | a ≠ z}).Walk x y, q.IsHamiltonian := by
  classical
  obtain ⟨a,ha⟩ : ∃ a, a ∉ p.support := by
    by_contra! covers
    exact notTrace ⟨u,v,p,hp.isHamiltonian_of_mem covers⟩
  have low := no_high_off_almost_longest p hp longest near k5 cap minimum ha
  let S := {z : V | z ≠ a}
  have sub : ∀ x ∈ p.support, x ∈ S := fun z hz eq => ha (eq ▸ hz)
  let q := p.induce S sub
  let f := (Embedding.induce (G:=G) S).toHom
  have mapped : q.map f = p := Walk.map_induce p sub
  have path : q.IsPath := (Walk.isPath_map_iff_of_injective (f:=f) Subtype.val_injective).mp
    (by rw [mapped]; exact hp)
  refine ⟨a,low,_,_,q,path.isHamiltonian_of_mem ?_⟩
  intro z
  have belongs : z.val ∈ p.support := by
    by_contra off
    have zlow := no_high_off_almost_longest p hp longest near k5 cap minimum off
    exact (degree_pair (G:=G) z.val a z.property).elim (fun h => by omega) (fun h => by omega)
  have supp : List.map Subtype.val q.support = p.support := by
    calc
      List.map Subtype.val q.support = (q.map f).support := (Walk.support_map f q).symm
      _ = p.support := congrArg (fun r : G.Walk u v => r.support) mapped
  rw [←supp] at belongs
  obtain ⟨t,ht,eq⟩ := List.mem_map.mp belongs
  exact (Subtype.ext eq : t = z) ▸ ht
theorem high_min_longest_gap {u v : V} (p : G.Walk u v) (hp : p.IsPath)
    (longest : ∀ {x y}, ∀ r : G.Walk x y, r.IsPath → r.length ≤ p.length)
    (notTrace : ¬ ∃ x y, ∃ q : G.Walk x y, q.IsHamiltonian)
    (k5 : 5 ≤ G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (minimum : ∀ v, G.secondSmallestDegree < 2*G.degree v) :
    p.support.length+3 < Fintype.card V := by
  classical
  by_contra! near
  have three (v : V) : 3 ≤ G.degree v := by have := minimum v; omega
  obtain ⟨a,ha⟩ : ∃ a, a ∉ p.support := by
    by_contra! covers
    exact notTrace ⟨u,v,p,hp.isHamiltonian_of_mem covers⟩
  have low := no_high_off_almost_longest p hp longest near k5 cap three ha
  have solo (b : V) (hb : b ∉ p.support) : b=a := by
    by_contra h
    have bl := no_high_off_almost_longest p hp longest near k5 cap three hb
    exact (degree_pair (G:=G) b a h).elim (fun h => by omega) (fun h => by omega)
  have wide (i : ℕ) (hi : i ∈ contactPositions p a) (j : ℕ) (hj : j ∈ contactPositions p a)
      (ord : i < j) : i+3 ≤ j := by
    obtain ⟨ir,ic⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨jr,jc⟩ := (mem_contactPositions p a j).mp hj
    have spaced := omitted_contact_spacing p hp longest ha ⟨i,ir⟩ ⟨j,jr⟩ ord
      (by simpa [get_at] using ic) (by simpa [get_at] using jc)
    by_contra! bad
    have eq : j=i+2 := by change i+2 ≤ j at spaced; omega
    obtain ⟨b,c,q,hq,len,supp⟩ := swap_contact_midpoint p hp ha i (eq ▸ jr) ic (eq ▸ jc)
    have md : p.getVert (i+1) ≠ a := fun e => ha (e ▸ p.getVert_mem_support _)
    have off : p.getVert (i+1) ∉ q.support := by
      intro h
      have on := List.mem_toFinset.mpr h
      rw [supp] at on
      exact (mem_insert.mp on).elim md (fun j => (mem_erase.mp j).1 rfl)
    have longest' : ∀ {x y}, ∀ r : G.Walk x y, r.IsPath → r.length ≤ q.length := by
      intro x y r hr
      rw [len]
      exact longest r hr
    have near' : Fintype.card V ≤ q.support.length+3 := by
      rw [q.length_support,len,←p.length_support]
      exact near
    have midlow := no_high_off_almost_longest q hq longest' near' k5 cap three off
    have different : p.getVert (i+1) ≠ a := fun e => ha (e ▸ p.getVert_mem_support _)
    exact (degree_pair (G:=G) (p.getVert (i+1)) a different).elim (fun h => by omega) (fun h => by omega)
  have costs := double_positions_le_path_shell p hp longest ha wide
  rw [contact_card_neighbors p hp a] at costs
  have sub : G.neighborFinset a ⊆ p.support.toFinset := by
    intro b hb
    apply List.mem_toFinset.mpr
    by_contra absent
    exact ((G.mem_neighborFinset a b).mp hb).ne (solo b absent).symm
  rw [inter_eq_left.mpr sub,G.card_neighborFinset_eq_degree] at costs
  have bound : p.support.toFinset.filter (fun v => G.dist a v = 2) ⊆ exactTwo G a :=
    fun z hz => mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hz).2⟩
  have quota := (card_le_card bound).trans (exact_quota a (cap a))
  have := minimum a
  omega
private theorem exists_longest_from_vertex {W : Type*} [Fintype W] {G : SimpleGraph W} (a : W) :
    ∃ x y, ∃ p : G.Walk x y, p.IsPath ∧
      ∀ {i j}, ∀ q : G.Walk i j, q.IsPath → q.length ≤ p.length := by
  classical
  let Good (m : ℕ) := ∃ x y, ∃ q : G.Walk x y, q.IsPath ∧ q.length=m
  have base : Good 0 := ⟨a,a,.nil,by simp,rfl⟩
  obtain ⟨x,y,p,hp,sz⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card W)) base
  have maximal {i j} (q : G.Walk i j) (hq : q.IsPath) : q.length ≤ p.length := by
    rw [sz]
    have len := q.length_support
    have bound := hq.support_nodup.length_le_card
    exact Nat.le_findGreatest (by omega) (show Good q.length from ⟨i,j,q,hq,rfl⟩)
  exact ⟨x,y,p,hp,maximal⟩
theorem high_min_all_paths_gap
    (notTrace : ¬ ∃ x y, ∃ q : G.Walk x y, q.IsHamiltonian)
    (k5 : 5 ≤ G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (minimum : ∀ v, G.secondSmallestDegree < 2*G.degree v) :
    ∀ a b, ∀ r : G.Walk a b, r.IsPath → r.support.length+3 < Fintype.card V := by
  classical
  intro a b r hr
  obtain ⟨x,y,p,hp,maximal⟩ := exists_longest_from_vertex (G:=G) a
  have upper := high_min_longest_gap p hp maximal notTrace k5 cap minimum
  have le := maximal r hr
  have l1 := r.length_support
  have l2 := p.length_support
  omega
end Graph189ExteriorDegreeCycle
end
section
namespace Graph189ExteriorDegreeCycle
open SimpleGraph
theorem exists_longest_cycle {V : Type*} [Fintype V] (K : SimpleGraph V)
    (has : ∃ a, ∃ C : K.Walk a a, C.IsCycle) :
    ∃ a, ∃ C : K.Walk a a, C.IsCycle ∧ ∀ b (Q : K.Walk b b), Q.IsCycle → Q.length ≤ C.length := by
  classical
  have bounded {b} (Q : K.Walk b b) (hQ : Q.IsCycle) : Q.length ≤ Fintype.card V := by
    have h := hQ.support_nodup.length_le_card
    rw [List.length_tail,Q.length_support] at h
    omega
  let Good (m : ℕ) := ∃ a, ∃ C : K.Walk a a, C.IsCycle ∧ C.length=m
  obtain ⟨b,Q,hQ⟩ := has
  have init : Good Q.length := ⟨b,Q,hQ,rfl⟩
  obtain ⟨a,C,hC,sz⟩ := Nat.findGreatest_spec (bounded Q hQ) init
  refine ⟨a,C,hC,?_⟩
  intro u p hp
  rw [sz]
  exact Nat.le_findGreatest (bounded p hp) (show Good p.length from ⟨u,p,hp,rfl⟩)
end Graph189ExteriorDegreeCycle
end
section
open Finset SimpleGraph Graph189ExteriorDegreeCycle Graph189UniversalCycle
namespace Graph189RepairedConeOrder
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem order_three (w : V) (k7 : 7 ≤ G.secondSmallestDegree)
    (notTrace : ¬∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (half : G.secondSmallestDegree<2*G.minDegree)
    (conn : 3≤(completeAt G w).vertexConnectivity) (min : G.secondSmallestDegree≤(completeAt G w).minDegree) :
    4*(G.secondSmallestDegree-3+2)-1 ≤ Fintype.card V := by
  classical
  let K := completeAt G w
  let k := G.secondSmallestDegree
  change 7 ≤ k at k7
  change k<2*G.minDegree at half
  change k ≤ K.minDegree at min
  have two (v : V) : 2 ≤ K.degree v := by have := K.minDegree_le_degree v; omega
  obtain ⟨b,R,hR,_⟩ := cycle_of_degree (G:=K) w (d:=2) (by decide) two
  obtain ⟨a,C,hC,mxC⟩ := exists_longest_cycle K ⟨b,R,hR⟩
  let U : Set V := {v | v≠w}
  let H := G.induce U
  have same : K.induce U=H := by
    ext x y
    constructor
    · rintro (orig|⟨touch,_⟩)
      · exact orig
      · exact (touch.elim x.property y.property).elim
    · exact fun e => Or.inl e
  have inH (v : U) : k ≤ H.degree v+1 := by
    have loss := degree_le_deletion_add_one (G:=K) w v
    change K.degree v.val≤(K.induce U).degree v+1 at loss
    have comp := degree_le_of_le (v:=v) same.le
    exact min.trans ((K.minDegree_le_degree v.val).trans (loss.trans (Nat.add_le_add_right comp 1)))
  obtain ⟨u,v,p,hp,_,supp,maxp⟩ := longest_in_deletion G w C hC mxC
  have mx {x y} (q : H.Walk x y) (hq : q.IsPath) : q.length ≤ p.length := maxp _ _ q hq
  let T : Set U := {t | t∉p.support.toFinset}
  let J := H.induce T
  have gap := high_min_all_paths_gap notTrace (by change 5 ≤ k; omega) cap (fun t => by
    have := G.minDegree_le_degree t
    change k<2*G.degree t
    omega)
  have missed := deletion_gap w p hp gap
  have edge : ∃ x y : T, J.Adj x y := by
    by_contra! no
    have independent : ∀ a∉p.support, ∀ b∉p.support, ¬H.Adj a b := by
      intro a ha b hb
      exact no ⟨a,fun h => ha (List.mem_toFinset.mp h)⟩ ⟨b,fun h => hb (List.mem_toFinset.mp h)⟩
    have ub := independent_omits_at_most_two w p hp mx independent (by change 2 ≤ k; omega) cap
    omega
  have degree (x y : T) (adj : J.Adj x y) : 3 ≤ J.degree x := by
    have lim := induced_second_layer U x.val (cap x.val.val)
    have bound := Graph189ExteriorGap.cross_contact_degree p hp mx
      (a:=x.val) (b:=y.val) (fun h => x.property (List.mem_toFinset.mpr h))
      (fun h => y.property (List.mem_toFinset.mpr h)) adj lim
    have pop := card_sdiff_add_card_inter (H.neighborFinset x.val) p.support.toFinset
    have dx := inH x.val
    have dy := inH y.val
    change (H.neighborFinset x.val∩p.support.toFinset).card+H.degree y.val ≤
      k+(H.neighborFinset x.val\p.support.toFinset).card at bound
    change _+_=H.degree x.val at pop
    change 3≤(H.induce T).degree x
    rw [degree_induce_filter]
    have filt : (H.neighborFinset x.val).filter (fun v => v∈T)=H.neighborFinset x.val\p.support.toFinset := by
      ext t
      simp [T]
    rw [filt]
    omega
  obtain ⟨r,q,hq,sz⟩ := cycle_of_nonisolated_degree (G:=J) (d:=3) (by decide) edge degree
  let f : J →g K.induce {t : V | t∉C.support} := {
    toFun := fun t => ⟨t.val.val,fun h => t.property (List.mem_toFinset.mpr ((supp _).mpr h))⟩
    map_rel' := fun h => Or.inl h }
  have inj : Function.Injective f := fun x y h => Subtype.ext (Subtype.ext
    (congrArg (fun t : {v : V | v∉C.support} => t.val) h))
  have long : 4≤(q.map f).length := by rwa [Walk.length_map]
  have order := Graph189BondyExterior.order_of_long_exterior (G:=K) (k:=3) (by decide) conn
    (by omega) C hC mxC (q.map f) (hq.map inj) long (by omega)
  change 4*(k-3+2)-1 ≤ Fintype.card V
  omega
end Graph189RepairedConeOrder
end
section
open SimpleGraph Finset
namespace Graph189TerminalLeafClosure
variable {V : Type*}
def terminalAdj (G : SimpleGraph V) (u v : V) : V ⊕ Bool → V ⊕ Bool → Prop
  | .inl a, .inl b => G.Adj a b
  | .inl a, .inr leaf => a = (if leaf then v else u)
  | .inr leaf, .inl a => a = (if leaf then v else u)
  | .inr _, .inr _ => False
def terminalLeaves (G : SimpleGraph V) (u v : V) : SimpleGraph (V ⊕ Bool) where
  Adj := terminalAdj G u v
  symm := by
    constructor
    intro a b h
    cases a <;> cases b
    · exact G.adj_symm h
    · exact h
    · exact h
    · exact h
  loopless := by
    constructor
    intro a
    cases a with
    | inl a => exact G.irrefl
    | inr l => exact id
instance terminalDecidable (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] (u v : V) :
    DecidableRel (terminalLeaves G u v).Adj := by
  intro a b
  cases a <;> cases b <;> simp only [terminalLeaves,terminalAdj] <;> infer_instance
theorem core_degree_le [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u v z : V) : G.degree z ≤ (terminalLeaves G u v).degree (.inl z) := by
  classical
  have inc : (G.neighborFinset z).image (Sum.inl : V → V ⊕ Bool) ⊆
      (terminalLeaves G u v).neighborFinset (.inl z) := by
    intro b hb
    obtain ⟨c,hc,rfl⟩ := Finset.mem_image.mp hb
    simp only [SimpleGraph.mem_neighborFinset] at hc ⊢
    exact hc
  have h := Finset.card_le_card inc
  rw [Finset.card_image_of_injective _ (fun _ _ h => Sum.inl.inj h)] at h
  exact h
theorem terminalLeaves_sup_edge (G : SimpleGraph V) (u v a b : V) :
    terminalLeaves (G ⊔ edge a b) u v =
      terminalLeaves G u v ⊔ edge (.inl a) (.inl b) := by
  ext x y
  cases x <;> cases y <;> simp [terminalLeaves,terminalAdj,SimpleGraph.edge_adj]
theorem leaf_traceable_of_core_edge [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (u v a b : V) (hne : a≠b) (hab : ¬G.Adj a b)
    (degree : Fintype.card V + 1 ≤ G.degree a + G.degree b)
    (path : ∃ x y, ∃ p : (terminalLeaves (G ⊔ edge a b) u v).Walk x y, p.IsHamiltonian) :
    ∃ x y, ∃ p : (terminalLeaves G u v).Walk x y, p.IsHamiltonian := by
  rw [terminalLeaves_sup_edge] at path
  apply Graph189.traceable_of_sup_edge (G := terminalLeaves G u v) (x := .inl a) (y := .inl b)
  · exact fun h => hne (Sum.inl.inj h)
  · exact hab
  · have ha := core_degree_le G u v a
    have hb := core_degree_le G u v b
    simp only [Fintype.card_sum, Fintype.card_bool]
    omega
  · exact path
end Graph189TerminalLeafClosure
end
section
open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} {G : SimpleGraph V} {u v : V}
theorem neighbor_of_leaf {y : V ⊕ Bool} {l : Bool}
    (h : (terminalLeaves G u v).Adj y (.inr l)) :
    y = .inl (if l then v else u) := by
  cases y with
  | inl y => exact congrArg Sum.inl h
  | inr y => exact False.elim h
theorem leaf_not_interior {a b : V ⊕ Bool} (p : (terminalLeaves G u v).Walk a b)
    (hp : p.IsPath) {i : ℕ} (hpos : 0 < i) (hbefore : i < p.length)
    {l : Bool} (atLeaf : p.getVert i = .inr l) : False := by
  have hi : i-1+1=i := by omega
  have left := p.adj_getVert_succ (i := i-1) (by omega)
  rw [hi,atLeaf] at left
  have right := (p.adj_getVert_succ hbefore).symm
  rw [atLeaf] at right
  have same : p.getVert (i-1) = p.getVert (i+1) :=
    (neighbor_of_leaf left).trans (neighbor_of_leaf right).symm
  have bad : i-1=i+1 := hp.getVert_injOn
      (show i-1 ≤ p.length by omega) (show i+1 ≤ p.length by omega) same
  omega
theorem hamiltonian_leaf_at_end [DecidableEq V] {a b : V ⊕ Bool}
    (p : (terminalLeaves G u v).Walk a b) (hp : p.IsHamiltonian) (l : Bool) :
    a = .inr l ∨ b = .inr l := by
  obtain ⟨i,hi⟩ := hp.getVert_surjective (Sum.inr l)
  by_cases hz : i=0
  · left
    simpa [hz] using hi
  by_cases small : i < p.length
  · exact False.elim (leaf_not_interior p hp.isPath (i := i) (Nat.pos_of_ne_zero hz) small hi)
  · right
    rwa [p.getVert_of_length_le (by omega)] at hi
end Graph189TerminalLeafClosure
end
section
open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
private theorem strip_oriented
    (p : (terminalLeaves G u v).Walk (.inr false) (.inr true)) (hp : p.IsHamiltonian) :
    ∃ q : G.Walk u v, q.IsHamiltonian := by
  have nonnil : ¬p.Nil := Walk.not_nil_of_ne (by simp)
  have first : p.snd = .inl u := neighbor_of_leaf (p.adj_snd nonnil).symm
  have qnn : ¬p.tail.Nil := Walk.not_nil_of_ne (by rw [first]; simp)
  have last : p.tail.penultimate = .inl v := neighbor_of_leaf (p.tail.adj_penultimate qnn)
  let t := p.tail.dropLast
  have parts : (.inr false) :: (t.support ++ [.inr true]) = p.support := by
    rw [show t.support ++ [.inr true] = p.tail.support from Walk.support_dropLast_concat qnn]
    exact Walk.cons_support_tail nonnil
  have nd := hp.isPath.support_nodup
  rw [←parts] at nd
  have ndf := List.nodup_cons.mp nd
  have core : ∀ z∈t.support, ∃ w : V, z = Sum.inl w := by
    intro z hz
    cases z with
    | inl w => exact ⟨w,rfl⟩
    | inr l =>
      cases l
      · exact (ndf.1 (List.mem_append_left _ hz)).elim
      · exact (List.disjoint_left.mp ndf.2.disjoint hz (by simp)).elim
  let project : V ⊕ Bool → V := Sum.elim id (fun l => if l then v else u)
  let L := t.support.map project
  have hn : L ≠ [] := by simp [L, t.support_ne_nil]
  have chain : L.IsChain G.Adj := by
    apply (List.isChain_map project).2
    apply t.isChain_adj_support.imp_of_mem_imp
    intro a b ha hb hab
    obtain ⟨i,rfl⟩ := core a ha
    obtain ⟨j,rfl⟩ := core b hb
    exact hab
  have nodup : L.Nodup := by
    apply List.Nodup.map_on _ ndf.2.of_append_left
    intro a ha b hb h
    obtain ⟨i,rfl⟩ := core a ha
    obtain ⟨j,rfl⟩ := core b hb
    exact congrArg Sum.inl h
  have all (w : V) : w ∈ L := by
    have hw := hp.mem_support (.inl w)
    rw [←parts] at hw
    have hmem : Sum.inl w ∈ t.support := by simpa using hw
    exact List.mem_map.mpr ⟨.inl w,hmem,rfl⟩
  let q := Walk.ofSupport L hn chain
  have qs : q.support = L := Walk.support_ofSupport hn chain
  have qh : q.IsHamiltonian := (Walk.IsPath.mk' (by rwa [qs])).isHamiltonian_of_mem
    (fun w => by rw [qs]; exact all w)
  have hstart : L.head hn = u := by
    simp [L,List.head_map,t,project,first]
  have hfinish : L.getLast hn = v := by
    simp [L,List.getLast_map,t,project,last]
  exact ⟨q.copy hstart hfinish, fun w => by simpa [Walk.support_copy] using qh w⟩
theorem prescribed_of_leaf_traceable
    (path : ∃ x y, ∃ p : (terminalLeaves G u v).Walk x y, p.IsHamiltonian) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  obtain ⟨x,y,p,hp⟩ := path
  rcases hamiltonian_leaf_at_end p hp false with hx | hy
  · subst x
    rcases hamiltonian_leaf_at_end p hp true with hf | hy
    · simp at hf
    · subst y
      exact strip_oriented p hp
  · subst y
    rcases hamiltonian_leaf_at_end p hp true with hx | hf
    · subst x
      apply strip_oriented p.reverse
      intro w
      simpa using hp w
    · simp at hf
end Graph189TerminalLeafClosure
end
section
open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v : V}
def oldEmbedding (G : SimpleGraph V) (u v : V) : G →g terminalLeaves G u v where
  toFun := Sum.inl
  map_rel' := fun h => h
theorem leaf_traceable_of_prescribed {p : G.Walk u v} (hp : p.IsHamiltonian) :
    ∃ x y, ∃ q : (terminalLeaves G u v).Walk x y, q.IsHamiltonian := by
  let h₁ : (terminalLeaves G u v).Adj (.inr false) (.inl u) := rfl
  let h₂ : (terminalLeaves G u v).Adj (.inl v) (.inr true) := rfl
  let q := Walk.cons h₁ ((p.map (oldEmbedding G u v)).concat h₂)
  have qs : q.support = Sum.inr false :: (p.support.map Sum.inl ++ [Sum.inr true]) := by
    simp [q,oldEmbedding]
    intro a ha
    rfl
  have mapped : (p.support.map (Sum.inl : V → V⊕Bool)).Nodup :=
    hp.isPath.support_nodup.map (fun _ _ h => Sum.inl.inj h)
  have nd : q.support.Nodup := by
    rw [qs]
    simp [List.nodup_append',mapped]
  refine ⟨_,_,q,(Walk.IsPath.mk' nd).isHamiltonian_of_mem ?_⟩
  intro w
  rw [qs]
  cases w with
  | inl z => simp [hp.mem_support z]
  | inr l => cases l <;> simp
theorem prescribed_of_sup_edge [Fintype V] [DecidableRel G.Adj] {a b : V}
    (distinct : a≠b) (missing : ¬G.Adj a b)
    (degree : Fintype.card V+1 ≤ G.degree a+G.degree b)
    (path : ∃ p : (G⊔edge a b).Walk u v, p.IsHamiltonian) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  obtain ⟨p,hp⟩ := path
  exact prescribed_of_leaf_traceable (leaf_traceable_of_core_edge G u v a b distinct missing degree
    (leaf_traceable_of_prescribed hp))
end Graph189TerminalLeafClosure
end
section
open SimpleGraph
namespace Graph189TerminalLeafClosure
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem prescribed_of_supergraph {G H : SimpleGraph V} [DecidableRel G.Adj] (incl : G ≤ H)
    (degree : ∀ a b, H.Adj a b → ¬G.Adj a b → Fintype.card V+1 ≤ G.degree a+G.degree b)
    {u v : V} (path : ∃ p : H.Walk u v, p.IsHamiltonian) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  suffices all : ∀ J : SimpleGraph V, G ≤ J → J ≤ H → ∃ p : J.Walk u v, p.IsHamiltonian by
    exact all G le_rfl incl
  intro J
  induction J using WellFoundedGT.induction with
  | ind J ih =>
    intro lower upper
    by_cases eq : J=H
    · subst J
      exact path
    have missing : ∃ a b, H.Adj a b ∧ ¬J.Adj a b := by
      by_contra! all
      exact eq (le_antisymm upper fun a b hab => all a b hab)
    obtain ⟨a,b,hab,hnot⟩ := missing
    have hEdge : edge a b ≤ H := by
      intro i j hij
      obtain ⟨h,_⟩ := (edge_adj a b i j).mp hij
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact hab
      · exact hab.symm
    have strict : J < J⊔edge a b := by
      apply lt_of_le_of_ne le_sup_left
      intro same
      have key : (J⊔edge a b).Adj a b := Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,hab.ne⟩)
      exact hnot (same.symm ▸ key)
    apply prescribed_of_sup_edge hab.ne hnot _ (ih _ strict (lower.trans le_sup_left) (sup_le upper hEdge))
    exact (degree _ _ hab (fun h => hnot (lower h))).trans
      (Nat.add_le_add (degree_le_of_le (v := a) lower) (degree_le_of_le (v := b) lower))
theorem complete_prescribed (u v : V) (hne : u ≠ v) :
    ∃ p : (⊤ : SimpleGraph V).Walk u v, p.IsHamiltonian := by
  classical
  let M := ((Finset.univ.erase u).erase v).toList
  let L := u :: (M ++ [v])
  have nd : L.Nodup := by
    simp [L,M,List.nodup_append',Finset.nodup_toList,hne]
  have chain : L.IsChain (⊤ : SimpleGraph V).Adj := by
    apply List.isChain_iff_forall_rel_of_append_cons_cons.mpr
    intro x y A B eq
    apply (top_adj _ _).mpr
    intro same
    subst y
    rw [eq] at nd
    have tail := nd.of_append_right
    exact (List.nodup_cons.mp tail).1 (by simp)
  have hn : L ≠ [] := by simp [L]
  let p := Walk.ofSupport L hn chain
  have ps : p.support = L := Walk.support_ofSupport hn chain
  have ph : p.IsHamiltonian := (Walk.IsPath.mk' (by rwa [ps])).isHamiltonian_of_mem (by
    intro z
    rw [ps]
    by_cases hzu : z=u
    · simp [L,hzu]
    by_cases hzv : z=v <;> simp [L,M,hzu,hzv])
  have hs : L.head hn = u := by simp [L]
  have he : L.getLast hn = v := by simp [L]
  exact ⟨p.copy hs he, fun z => by simpa [Walk.support_copy] using ph z⟩
end Graph189TerminalLeafClosure
end
section
open Finset SimpleGraph
namespace Graph189LongPathClosure
variable {V : Type*} {G : SimpleGraph V}
private theorem route_common {a b c : V} (ac : G.Adj a c) (bc : G.Adj b c)
    {u v : V} (p : (G ⊔ edge a b).Walk u v) (hp : p.IsPath) (fresh : c∉p.support) :
    ∃ q : G.Walk u v, q.IsPath ∧ p.support ⊆ q.support ∧
      (∀ t∈q.support, t∈p.support ∨ t=c) ∧ (c∈q.support → a∈p.support ∧ b∈p.support) := by
  induction p with
  | nil =>
    refine ⟨.nil,by simp,fun _ h => h,fun _ h => Or.inl h,fun h => (fresh h).elim⟩
  | @cons u v w e p ih =>
    have xn : u∉p.support := (List.nodup_cons.mp hp.support_nodup).1
    have cu : c≠u := fun eq => fresh (by simp [eq])
    have cf : c∉p.support := fun h => fresh (by simp [h])
    obtain ⟨q,hq,contains,extra,ifc⟩ := ih hp.of_cons cf
    have outside : u∉q.support := by
      intro h
      exact (extra u h).elim xn cu.symm
    by_cases old : G.Adj u v
    · refine ⟨.cons old q,hq.cons outside,?_,?_,?_⟩
      · simpa only [Walk.support_cons] using List.cons_subset_cons u contains
      · intro t ht
        rcases List.mem_cons.mp ht with rfl|h
        · exact Or.inl (by simp)
        · exact (extra t h).imp_left (fun mem => List.mem_cons_of_mem _ mem)
      · intro h
        have both := ifc ((List.mem_cons.mp h).resolve_left cu)
        exact ⟨List.mem_cons_of_mem _ both.1,List.mem_cons_of_mem _ both.2⟩
    · obtain ⟨orient,_⟩ := (edge_adj a b u v).mp (e.resolve_left old)
      have ua : u=a ∨ u=b := orient.imp (fun h => h.1) (fun h => h.1)
      have unused : c∉q.support := fun h => ua.elim (fun eq => xn (eq ▸ (ifc h).1)) (fun eq => xn (eq ▸ (ifc h).2))
      have first : G.Adj u c := ua.elim (fun eq => eq ▸ ac) (fun eq => eq ▸ bc)
      have last : G.Adj c v := orient.elim (fun h => h.2 ▸ bc.symm) (fun h => h.2 ▸ ac.symm)
      refine ⟨.cons first (.cons last q),(hq.cons unused).cons (by simp [outside,cu.symm]),?_,?_,?_⟩
      · intro t ht
        rcases List.mem_cons.mp ht with rfl|h
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (contains h))
      · intro t ht
        rcases List.mem_cons.mp ht with rfl|h
        · exact Or.inl (by simp)
        rcases List.mem_cons.mp h with rfl|h
        · exact Or.inr rfl
        exact (extra t h).imp_left (fun mem => List.mem_cons_of_mem _ mem)
      · intro _
        rcases orient with ⟨rfl,rfl⟩|⟨rfl,rfl⟩ <;> simp [p.start_mem_support]
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
theorem long_of_sup_edge {a b u v : V} (degree : Fintype.card V+1 ≤ G.degree a+G.degree b)
    (p : (G⊔edge a b).Walk u v) (hp : p.IsPath) :
    ∃ q : G.Walk u v, q.IsPath ∧ p.support.length ≤ q.support.length := by
  classical
  let U := p.support.toFinset
  by_cases common : ∃ c, c∉p.support ∧ G.Adj a c ∧ G.Adj b c
  · obtain ⟨c,fresh,ac,bc⟩ := common
    obtain ⟨q,path,sub,_,_⟩ := route_common ac bc p hp fresh
    have cmp := card_le_card (show p.support.toFinset ⊆ q.support.toFinset from
      fun t h => List.mem_toFinset.mpr (sub (List.mem_toFinset.mp h)))
    rw [List.toFinset_card_of_nodup hp.support_nodup,List.toFinset_card_of_nodup path.support_nodup] at cmp
    exact ⟨q,path,cmp⟩
  let H := G.induce (U : Set V)
  let K := (G⊔edge a b).induce (U : Set V)
  have reach (t : V) (ht : t∈p.support) : t∈(U : Set V) := List.mem_toFinset.mpr ht
  let r := p.induce (U : Set V) reach
  let lift := (Embedding.induce (G:=G⊔edge a b) (U : Set V)).toHom
  have mapped : r.map lift=p := Walk.map_induce p reach
  have hPath : r.IsPath := (Walk.isPath_map_iff_of_injective (f:=lift) Subtype.val_injective).mp
    (by rw [mapped]; exact hp)
  have hHamilton : r.IsHamiltonian := hPath.isHamiltonian_of_mem (by
    intro t
    have mem : t.val∈p.support := List.mem_toFinset.mp t.property
    have supp : r.support.map lift=p.support := (Walk.support_map lift r).symm.trans
      (congrArg (fun w : (G⊔edge a b).Walk u v => w.support) mapped)
    rw [←supp] at mem
    obtain ⟨z,hz,eq⟩ := List.mem_map.mp mem
    exact (Subtype.ext eq : z=t) ▸ hz)
  have bound (x y : U) (xy : K.Adj x y) (missing : ¬H.Adj x y) :
      Fintype.card U + 1 ≤ H.degree x+H.degree y := by
    obtain ⟨orient,_⟩ := (edge_adj a b x.val y.val).mp (xy.resolve_left missing)
    have d : Fintype.card V+1 ≤ G.degree x.val+G.degree y.val := by
      rcases orient with h|h <;> rw [h.1,h.2] <;> omega
    let A := G.neighborFinset x.val
    let B := G.neighborFinset y.val
    have dis : Disjoint (A \ U) (B \ U) := by
      rw [Finset.disjoint_left]
      intro c ca cb
      have off : c∉p.support := fun h => (mem_sdiff.mp ca).2 (List.mem_toFinset.mpr h)
      have cx := (G.mem_neighborFinset _ _).mp (mem_sdiff.mp ca).1
      have cy := (G.mem_neighborFinset _ _).mp (mem_sdiff.mp cb).1
      rcases orient with h|h <;> rw [h.1] at cx <;> rw [h.2] at cy
      · exact common ⟨c,off,cx,cy⟩
      · exact common ⟨c,off,cy,cx⟩
    have loss := card_le_card (show (A \ U) ∪ (B \ U) ⊆ Uᶜ from by
      intro t ht
      exact mem_compl.mpr ((mem_union.mp ht).elim (fun h => (mem_sdiff.mp h).2) (fun h => (mem_sdiff.mp h).2)))
    rw [card_union_of_disjoint dis] at loss
    have ax := card_sdiff_add_card_inter A U
    have by' := card_sdiff_add_card_inter B U
    change Fintype.card V+1 ≤ A.card+B.card at d
    have count := card_add_card_compl U
    change Fintype.card U+1 ≤ (G.induce (U : Set V)).degree x+(G.induce (U : Set V)).degree y
    rw [Fintype.card_coe,Graph189ExteriorDegreeCycle.degree_induce_filter,Graph189ExteriorDegreeCycle.degree_induce_filter]
    have filter (s : Finset V) : s.filter (fun v => v∈(U : Set V))=s∩U := by ext v; simp
    rw [filter,filter]
    change U.card+1 ≤ (A∩U).card+(B∩U).card
    omega
  obtain ⟨q,hq⟩ := Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) (H:=K)
    (fun _ _ h => Or.inl h) bound ⟨r,hHamilton⟩
  let inc := (Embedding.induce (G:=G) (U : Set V)).toHom
  refine ⟨q.map inc,hq.isPath.map Subtype.val_injective,?_⟩
  have size : (q.map inc).support.length=q.support.length := by rw [Walk.support_map,List.length_map]
  have card : Fintype.card U=p.support.length := (Fintype.card_coe _).trans (List.toFinset_card_of_nodup hp.support_nodup)
  exact le_of_eq (size.trans (hq.length_support.trans card)).symm
theorem long_of_supergraph {K : SimpleGraph V} (incl : G ≤ K)
    (degree : ∀ x y, K.Adj x y → ¬G.Adj x y → Fintype.card V+1 ≤ G.degree x+G.degree y)
    {u v : V} (p : K.Walk u v) (hp : p.IsPath) :
    ∃ q : G.Walk u v, q.IsPath ∧ p.support.length ≤ q.support.length := by
  classical
  suffices all : ∀ J : SimpleGraph V, G ≤ J → J ≤ K →
      ∃ q : J.Walk u v, q.IsPath ∧ p.support.length ≤ q.support.length by
    exact all G le_rfl incl
  intro J
  induction J using WellFoundedGT.induction with
  | ind J ih =>
    intro lower upper
    by_cases eq : J=K
    · subst J
      exact ⟨p,hp,le_rfl⟩
    have miss : ∃ a b, K.Adj a b ∧ ¬J.Adj a b := by
      by_contra! all
      exact eq (le_antisymm upper fun a b hab => all a b hab)
    obtain ⟨a,b,ab,missing⟩ := miss
    have extra : edge a b ≤ K := by
      intro x y xy
      obtain ⟨h,_⟩ := (edge_adj a b x y).mp xy
      rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ab
      · exact ab.symm
    have strict : J < J⊔edge a b := by
      apply lt_of_le_of_ne le_sup_left
      intro same
      have ad : (J⊔edge a b).Adj a b := Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,ab.ne⟩)
      exact missing (same.symm ▸ ad)
    obtain ⟨r,hr,sz⟩ := ih _ strict (lower.trans le_sup_left) (sup_le upper extra)
    have d := (degree a b ab (fun h => missing (lower h))).trans
      (Nat.add_le_add (degree_le_of_le (v:=a) lower) (degree_le_of_le (v:=b) lower))
    obtain ⟨q,hq,size⟩ := long_of_sup_edge d r hr
    exact ⟨q,hq,sz.trans size⟩
end Graph189LongPathClosure
end
section
open Finset SimpleGraph
namespace Graph189RotationExterior
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
omit [DecidableEq V] [DecidableRel G.Adj] in
private theorem exists_longest (z : V) :
    ∃ x y, ∃ p : G.Walk x y, p.IsPath ∧
      ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length := by
  classical
  let Good (n : ℕ) := ∃ a b, ∃ r : G.Walk a b, r.IsPath ∧ r.length=n
  have base : Good 0 := ⟨z,z,.nil,by simp,rfl⟩
  obtain ⟨x,y,p,hp,sz⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) base
  refine ⟨x,y,p,hp,?_⟩
  intro a b r hr
  rw [sz]
  have := r.length_support
  have := hr.support_nodup.length_le_card
  exact Nat.le_findGreatest (by omega) (show Good r.length from ⟨_,_,r,hr,rfl⟩)
private theorem neighbors_in_prefix {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (maximal : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    {L : ℕ} (two : 2 ≤ L) (short : ∀ v (q : G.Walk v v), q.IsCycle → q.length ≤ L) :
    G.neighborFinset x ⊆ (p.support.take L).toFinset := by
  intro v hv
  have edge := (G.mem_neighborFinset _ _).mp hv
  have mem : v ∈ p.support := by
    by_contra miss
    have bound := maximal (p.cons edge.symm) (Walk.IsPath.mk' (by simp [miss,hp.support_nodup]))
    simp at bound
  apply List.mem_toFinset.mpr
  apply (List.mem_take_iff_idxOf_lt mem).mpr
  by_contra! far
  let T := p.takeUntil v mem
  have len : L ≤ T.length := by rwa [p.length_takeUntil mem]
  have cycle : (T.cons edge.symm).IsCycle := by
    apply Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    refine ⟨?_,by simp only [Walk.length_cons]; omega⟩
    rw [Walk.tail_cons]
    exact (Walk.isPath_copy _ _ _).mpr (hp.takeUntil mem)
  have bound := short v _ cycle
  simp only [Walk.length_cons] at bound
  omega
omit [Fintype V] [DecidableRel G.Adj] in
private theorem rotate {x y : V} (p : G.Walk x y) (hp : p.IsPath) {i L : ℕ}
    (inside : i+1 < p.support.length) (near : i+1 ≤ L)
    (pivot : G.Adj x (p.getVert (i+1))) :
    ∃ b, ∃ r : G.Walk (p.getVert i) b, r.IsPath ∧ r.length=p.length ∧
      (r.support.take L).toFinset=(p.support.take L).toFinset := by
  let A := p.support.take (i+1)
  let B := p.support.drop (i+1)
  have split : p.support=A++B := (List.take_append_drop _ _).symm
  have size : A.length=i+1 := by
    change (p.support.take (i+1)).length=i+1
    exact List.length_take_of_le (by omega)
  have last : A.getLast?=some (p.getVert i) := by
    have nearI : i < p.support.length := by omega
    rw [←Graph189ExteriorGap.get_at p nearI]
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem (l:=p.support) (i:=i) nearI)).trans
      List.getLast?_concat
  have first : A.head?=some x := by
    simp only [A,List.head?_take,show i+1≠0 by omega,if_false]
    rw [List.head?_eq_some_head p.support_ne_nil,p.head_support]
  have startB : B.head?=some (p.getVert (i+1)) := by
    simp only [B,List.head?_drop,List.getElem?_eq_getElem inside,Graph189ExteriorGap.get_at]
  let S := A.reverse++B
  have chain := p.isChain_adj_support
  have nd := hp.support_nodup
  rw [split] at chain nd
  have chainR : A.reverse.IsChain G.Adj := List.isChain_reverse.mpr
    (chain.left_of_append.imp (fun _ _ edge => edge.symm))
  have chainS : S.IsChain G.Adj := by
    apply chainR.append chain.right_of_append
    intro v hv w hw
    rw [List.getLast?_reverse, first] at hv
    rw [startB] at hw
    exact (Option.mem_some_iff.mp hv) ▸ (Option.mem_some_iff.mp hw) ▸ pivot
  have ndS : S.Nodup := List.Nodup.append (by simpa using nd.of_append_left) nd.of_append_right
    (by simpa using nd.disjoint)
  have headS : S.head?=some (p.getVert i) := by simp [S,List.head?_append,last]
  have sNe : S≠[] := by intro empty; simp [empty] at headS
  let r := Walk.ofSupport S sNe chainS
  have supp : r.support=S := Walk.support_ofSupport sNe chainS
  have start : S.head sNe=p.getVert i := by rw [List.head?_eq_some_head sNe] at headS; simpa using headS
  have path : r.IsPath := Walk.IsPath.mk' (by rwa [supp])
  have len : r.length=p.length := by
    have lhs := r.length_support
    have rhs := p.length_support
    rw [supp] at lhs
    rw [split] at rhs
    simp only [S,List.length_append,List.length_reverse] at lhs rhs
    omega
  have sets : (S.take L).toFinset=(p.support.take L).toFinset := by
    have le : A.length ≤ L := size.trans_le near
    have rev : A.reverse.length ≤ L := by simpa using le
    rw [split]
    simp only [S,List.take_append,List.take_of_length_le le,List.take_of_length_le rev,List.length_reverse]
    simp
  exact ⟨_,r.copy start rfl,(Walk.isPath_copy _ _ _).mpr path,by simpa using len,by simpa [supp] using sets⟩
theorem degree_window_at {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ p.length)
    {d L : ℕ} (two : 2 ≤ L) (degree : d ≤ G.degree x)
    (short : ∀ v (q : G.Walk v v), q.IsCycle → q.length ≤ L) :
    ∃ B E : Finset V, d ≤ E.card ∧ E⊆B ∧ B.card ≤ L ∧
      ∀ v∈E, G.neighborFinset v⊆B := by
  classical
  let B := (p.support.take L).toFinset
  let N := G.neighborFinset x
  let idx (v : V) := p.support.idxOf v
  let prev (v : V) := p.getVert (idx v-1)
  let E := N.image prev
  have initial : N ⊆ B := neighbors_in_prefix p hp mx two short
  have mem {v : V} (hv : v ∈ N) : v ∈ p.support := List.mem_of_mem_take (List.mem_toFinset.mp (initial hv))
  have range {v : V} (hv : v ∈ N) : idx v < p.support.length := List.idxOf_lt_length_iff.mpr (mem hv)
  have value {v : V} (hv : v ∈ N) : p.getVert (idx v)=v :=
    (Graph189ExteriorGap.get_at p (range hv)).symm.trans (List.getElem_idxOf (range hv))
  have pos {v : V} (hv : v ∈ N) : 0 < idx v := by
    by_contra! zero
    have eq := value hv
    rw [show idx v=0 by omega,Walk.getVert_zero] at eq
    exact ((G.mem_neighborFinset _ _).mp hv).ne eq
  have near {v : V} (hv : v ∈ N) : idx v < L :=
    (List.mem_take_iff_idxOf_lt (mem hv)).mp (List.mem_toFinset.mp (initial hv))
  have inj : Set.InjOn prev (N : Set V) := by
    intro a ha b hb eq
    have pa := pos ha
    have pb := pos hb
    have ra := range ha
    have rb := range hb
    have := p.length_support
    have same : idx a-1=idx b-1 := hp.getVert_injOn
      (by change idx a-1 ≤ p.length; omega) (by change idx b-1 ≤ p.length; omega) eq
    have index : idx a=idx b := by omega
    exact (value ha).symm.trans ((congrArg p.getVert index).trans (value hb))
  have enough : d ≤ E.card := by
    change d ≤ (N.image prev).card
    rw [card_image_of_injOn inj]
    exact degree.trans_eq (G.card_neighborFinset_eq_degree x).symm
  have sub : E ⊆ B := by
    intro v hv
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    let j := idx w-1
    have jw : j < p.support.length := by have := range hw; dsimp [j]; omega
    have jl : j < L := by have := near hw; dsimp [j]; omega
    apply List.mem_toFinset.mpr
    apply List.mem_take_iff_getElem.mpr
    exact ⟨j,lt_min jl jw, Graph189ExteriorGap.get_at p jw⟩
  have constrained (v : V) (hv : v ∈ E) : G.neighborFinset v ⊆ B := by
    obtain ⟨w,hw,rfl⟩ := mem_image.mp hv
    have pp := pos hw
    have len := range hw
    have small := near hw
    have step : idx w-1+1=idx w := by omega
    obtain ⟨b,r,hr,eq,same⟩ := rotate p hp (i:=idx w-1) (L:=L) (by omega) (by omega)
      (by rw [step,value hw]; exact (G.mem_neighborFinset _ _).mp hw)
    have mx' {a b} (s : G.Walk a b) (hs : s.IsPath) : s.length ≤ r.length := (mx s hs).trans_eq eq.symm
    have bound := neighbors_in_prefix r hr mx' two short
    rw [same] at bound
    exact bound
  have lengthB : B.card ≤ L := (List.toFinset_card_le _).trans (List.length_take_le _ _)
  exact ⟨B,E,enough,sub,lengthB,constrained⟩
theorem degree_window (z : V) {d L : ℕ} (two : 2 ≤ L)
    (minimum : ∀ v, d ≤ G.degree v)
    (short : ∀ v (q : G.Walk v v), q.IsCycle → q.length ≤ L) :
    ∃ B E : Finset V, d ≤ E.card ∧ E ⊆ B ∧ B.card ≤ L ∧
      ∀ v ∈ E, G.neighborFinset v ⊆ B := by
  classical
  obtain ⟨x,y,p,hp,mx⟩ := exists_longest (G:=G) z
  exact degree_window_at p hp mx two (minimum x) short
end Graph189RotationExterior
end
section
open SimpleGraph Finset
namespace Graph189LinkedExterior
def Linked {W : Type*} (H : SimpleGraph W) (l : Nat) : Prop :=
  ∃ D : Finset W, l+1 ≤ D.card ∧ ∀ u∈D, ∀ v∈D, u≠v →
    ∃ p : H.Walk u v, p.IsPath ∧ l ≤ p.support.length ∧ ∀ b∈p.support,b∈D
theorem map {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W} (f : G →g H)
    (injective : Function.Injective f) {l : Nat} (linked : Linked G l) : Linked H l := by
  classical
  obtain ⟨D,size,paths⟩ := linked
  let e : V ↪ W := ⟨f,injective⟩
  refine ⟨D.map e,by simpa using size,?_⟩
  intro u hu v hv ne
  obtain ⟨x,hx,rfl⟩ := mem_map.mp hu
  obtain ⟨y,hy,rfl⟩ := mem_map.mp hv
  obtain ⟨q,hq,len,within⟩ := paths x hx y hy (fun same => ne (congrArg e same))
  refine ⟨q.map f,hq.map injective,?_,?_⟩
  · simpa only [Walk.support_map,List.length_map] using len
  · intro b hb
    rw [Walk.support_map] at hb
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hb
    exact mem_map.mpr ⟨a,within a ha,rfl⟩
end Graph189LinkedExterior
end
section
namespace Graph189NativeCycleLinked
open SimpleGraph Finset
theorem of_cycle {V : Type*} [DecidableEq V] {G : SimpleGraph V} {r : V}
    (C : G.Walk r r) (hc : C.IsCycle) {l : ℕ} (size : l+1 ≤ C.length)
    (long : 2*l ≤ C.length+2) : Graph189LinkedExterior.Linked G l := by
  classical
  let S := C.support.toFinset
  have enough : C.length ≤ S.card := by
    have sub : C.support.tail.toFinset ⊆ S := by
      intro v hv
      exact List.mem_toFinset.mpr (List.mem_of_mem_tail (List.mem_toFinset.mp hv))
    have cmp := card_le_card sub
    rw [List.toFinset_card_of_nodup hc.support_nodup,List.length_tail,C.length_support] at cmp
    omega
  refine ⟨S,size.trans enough,?_⟩
  intro a ha b hb ne
  let R := C.rotate a (List.mem_toFinset.mp ha)
  have rc : R.IsCycle := hc.rotate (List.mem_toFinset.mp ha)
  have on : b∈R.support := (C.mem_support_rotate_iff a _).mpr (List.mem_toFinset.mp hb)
  let L := R.takeUntil b on
  let T := R.dropUntil b on
  have split : L.append T=R := R.take_spec on
  have cyc : (L.append T).IsCycle := split ▸ rc
  have lp : L.IsPath := rc.isPath_takeUntil on
  have tp : T.IsPath := cyc.isPath_of_append_right (L.not_nil_of_ne ne)
  have lengths : L.length+T.length=C.length := by
    rw [← Walk.length_append,split]
    exact C.length_rotate _ _
  have inS (v : V) (hv : v∈R.support) : v∈S :=
    List.mem_toFinset.mpr ((C.mem_support_rotate_iff a _).mp hv)
  by_cases large : l ≤ L.length+1
  · exact ⟨L,lp,by rwa [L.length_support],fun v hv => inS v (R.support_takeUntil_subset_support on hv)⟩
  · refine ⟨T.reverse,tp.reverse,by rw [Walk.length_support,Walk.length_reverse]; omega,?_⟩
    intro v hv
    exact inS v (R.support_dropUntil_subset_support on (by simpa using hv))
end Graph189NativeCycleLinked
end
section
open SimpleGraph Finset
namespace Graph189RotationLinked
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
private def fill (G : SimpleGraph V) (P : V → Prop) : SimpleGraph V where
  Adj x y := G.Adj x y ∨ P x ∧ P y ∧ x≠y
  symm := ⟨fun _ _ h => h.elim (fun e => Or.inl e.symm) (fun ⟨px,py,ne⟩ => Or.inr ⟨py,px,ne.symm⟩)⟩
  loopless := ⟨fun _ h => h.elim (fun e => G.irrefl e) (fun h => h.2.2 rfl)⟩
private theorem route_clique (R : Finset V)
    (clique : ∀ u∈R, ∀ v∈R, u≠v → G.Adj u v)
    (ports : ∀ v, v∉R → 2 ≤ (G.neighborFinset v ∩ R).card)
    (x y : V) (different : x≠y) :
    ∃ q : G.Walk x y, q.IsPath ∧ R.card ≤ q.support.length := by
  classical
  have get {w : V} (out : w∉R) (avoid : V) : ∃ v∈R, G.Adj w v ∧ v≠avoid := by
    obtain ⟨v,hv,ne⟩ := exists_mem_ne (ports w out) avoid
    exact ⟨v,(mem_inter.mp hv).2,(G.mem_neighborFinset _ _).mp (mem_inter.mp hv).1,ne⟩
  have ends : ∃ u∈R, ∃ v∈R, u≠v ∧ (x=u ∨ x∉R ∧ G.Adj x u) ∧ (y=v ∨ y∉R ∧ G.Adj y v) := by
    by_cases hx : x∈R
    · by_cases hy : y∈R
      · exact ⟨x,hx,y,hy,different,Or.inl rfl,Or.inl rfl⟩
      obtain ⟨v,hv,edge,ne⟩ := get hy x
      exact ⟨x,hx,v,hv,ne.symm,Or.inl rfl,Or.inr ⟨hy,edge⟩⟩
    obtain ⟨u,hu,ux,uy⟩ := get hx y
    by_cases hy : y∈R
    · exact ⟨u,hu,y,hy,uy,Or.inr ⟨hx,ux⟩,Or.inl rfl⟩
    obtain ⟨v,hv,vy,ne⟩ := get hy u
    exact ⟨u,hu,v,hv,ne.symm,Or.inr ⟨hx,ux⟩,Or.inr ⟨hy,vy⟩⟩
  obtain ⟨u,hu,v,hv,ne,xu,yv⟩ := ends
  let i : R := ⟨u,hu⟩
  let j : R := ⟨v,hv⟩
  let f : (⊤ : SimpleGraph R) →g G := {
    toFun := Subtype.val
    map_rel' := fun {a b} h => clique _ a.property _ b.property (fun eq => (top_adj _ _).mp h (Subtype.ext eq)) }
  obtain ⟨q,hq⟩ := Graph189TerminalLeafClosure.complete_prescribed i j (fun eq => ne (congrArg Subtype.val eq))
  let r : G.Walk u v := q.map f
  have hpath : r.IsPath := hq.isPath.map Subtype.val_injective
  have contained (t : V) (ht : t∈r.support) : t∈R := by
    have h : t∈q.support.map f := (Walk.support_map f q) ▸ ht
    obtain ⟨w,_,rfl⟩ := List.mem_map.mp h
    exact w.property
  have size : r.support.length=R.card := by
    have mapped := congrArg List.length (Walk.support_map f q)
    rw [List.length_map,hq.length_support,Fintype.card_coe] at mapped
    exact mapped
  rcases xu with rfl|⟨xo,link⟩ <;> rcases yv with rfl|⟨yo,back⟩
  · exact ⟨r,hpath,size.ge⟩
  · refine ⟨r.concat back.symm,hpath.concat (fun h => yo (contained _ h)) back.symm,?_⟩
    simp [size]
  · refine ⟨r.cons link,hpath.cons (fun h => xo (contained _ h)),?_⟩
    simp [size]
  · let t := r.cons link
    have tp : t.IsPath := hpath.cons (fun h => xo (contained _ h))
    have fresh : y∉t.support := fun h => yo (contained _ ((List.mem_cons.mp h).resolve_left different.symm))
    refine ⟨t.concat back.symm,tp.concat fresh back.symm,?_⟩
    simp [t,size]
    omega
private theorem pair_degree (B R S : Finset V) (sb : S⊆B)
    (near : ∀ r∈R, G.neighborFinset r⊆B)
    (removed : ∀ v∈B, v∉S → (G.neighborFinset v ∩ R).card ≤ 1)
    {x y : S} (xr : x.val∈R) (yr : y.val∈R) (ne : x≠y)
    (sum : B.card+1 ≤ G.degree x.val + G.degree y.val) :
    Fintype.card S+1 ≤ (G.induce (S : Set V)).degree x+(G.induce (S : Set V)).degree y := by
  classical
  let A := G.neighborFinset x.val
  let C := G.neighborFinset y.val
  have dis : Disjoint (A \ S) (C \ S) := by
    rw [Finset.disjoint_left]
    intro t hx hy
    have tx := ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp hx).1).symm
    have ty := ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp hy).1).symm
    have bound := removed t (near _ xr (mem_sdiff.mp hx).1) (mem_sdiff.mp hx).2
    have many := one_lt_card.mpr (show ∃ a∈G.neighborFinset t∩R, ∃ b∈G.neighborFinset t∩R, a≠b from
      ⟨x.val,mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr tx,xr⟩,
       y.val,mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ty,yr⟩,fun h => ne (Subtype.ext h)⟩)
    omega
  have loss := card_le_card (show (A\S) ∪ (C\S) ⊆ B\S from by
    intro t ht
    rcases mem_union.mp ht with h|h
    · exact mem_sdiff.mpr ⟨near _ xr (mem_sdiff.mp h).1,(mem_sdiff.mp h).2⟩
    · exact mem_sdiff.mpr ⟨near _ yr (mem_sdiff.mp h).1,(mem_sdiff.mp h).2⟩)
  rw [card_union_of_disjoint dis] at loss
  have ax := card_sdiff_add_card_inter A S
  have cy := card_sdiff_add_card_inter C S
  have rem := card_sdiff_add_card_eq_card sb
  change B.card+1 ≤ A.card+C.card at sum
  rw [Fintype.card_coe,Graph189ExteriorDegreeCycle.degree_induce_filter,Graph189ExteriorDegreeCycle.degree_induce_filter]
  have filter (T : Finset V) : T.filter (fun v => v∈(S : Set V))=T∩S := by ext v; simp
  rw [filter,filter]
  change S.card+1 ≤ (A∩S).card+(C∩S).card
  omega
theorem linked_of_window (B R : Finset V) {d : ℕ} (rows : d ≤ R.card) (rb : R⊆B)
    (small : B.card+1≤2*d) (minimum : ∀ w∈R, d ≤ G.degree w)
    (near : ∀ w∈R, G.neighborFinset w⊆B) : Graph189LinkedExterior.Linked G d := by
  classical
  let S := R ∪ B.filter (fun w => 2≤(G.neighborFinset w∩R).card)
  have rs : R⊆S := subset_union_left
  have sb : S⊆B := union_subset rb (filter_subset _ _)
  have removed (t : V) (tb : t∈B) (out : t∉S) : (G.neighborFinset t∩R).card≤1 := by
    by_contra! big
    exact out (mem_union_right _ (mem_filter.mpr ⟨tb,big⟩))
  have size : d+1 ≤ S.card := by
    by_contra! few
    have er := card_le_card rs
    have same : S=R := (eq_of_subset_of_card_le rs (by omega)).symm
    have choose (r : R) : ∃ w : ↥(B\R), G.Adj r.val w.val := by
      by_contra! all
      have inc : G.neighborFinset r.val ⊆ R.erase r.val := by
        intro t ht
        have e := (G.mem_neighborFinset _ _).mp ht
        apply mem_erase.mpr
        refine ⟨e.ne.symm,?_⟩
        by_contra missing
        exact all ⟨t,mem_sdiff.mpr ⟨near _ r.property ht,missing⟩⟩ e
      have count := card_le_card inc
      rw [G.card_neighborFinset_eq_degree,card_erase_of_mem r.property] at count
      have lo := minimum r.val r.property
      have pos := card_pos.mpr (show R.Nonempty from ⟨r.val,r.property⟩)
      omega
    choose f edge using choose
    have injective : Function.Injective f := by
      intro x y eq
      by_contra ne
      let t := (f x).val
      have xadj : G.Adj t x.val := (edge x).symm
      have yadj : G.Adj t y.val := by
        change G.Adj (f x).val y.val
        rw [eq]
        exact (edge y).symm
      have enough : 1 < (G.neighborFinset t∩R).card := one_lt_card.mpr
        ⟨x.val,mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr xadj,x.property⟩,
         y.val,mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr yadj,y.property⟩,fun h => ne (Subtype.ext h)⟩
      have bound := removed t (mem_sdiff.mp (f x).property).1 (by rw [same]; exact (mem_sdiff.mp (f x).property).2)
      omega
    have bound := card_le_card_of_injective injective
    have sizeB := card_sdiff_add_card_eq_card rb
    omega
  let H := G.induce (S : Set V)
  let P (w : S) := w.val∈R
  let J := fill H P
  let emb : R ↪ S := ⟨fun w => ⟨w.val,rs w.property⟩,fun _ _ e => Subtype.ext (congrArg (fun t : S => t.val) e)⟩
  let Z := (univ : Finset R).map emb
  have zm (w : S) : w∈Z ↔ w.val∈R := by
    constructor
    · intro h
      obtain ⟨r,_,rfl⟩ := mem_map.mp h
      exact r.property
    · intro h
      exact mem_map.mpr ⟨⟨w.val,h⟩,mem_univ _,Subtype.ext rfl⟩
  have zsize : Z.card=R.card := by simp [Z]
  have complete (u : S) (hu : u∈Z) (v : S) (hv : v∈Z) (ne : u≠v) : J.Adj u v :=
    Or.inr ⟨(zm _).mp hu,(zm _).mp hv,ne⟩
  have ports (w : S) (no : w∉Z) : 2≤(J.neighborFinset w∩Z).card := by
    have out : w.val∉R := fun h => no ((zm _).mpr h)
    have orig := (mem_filter.mp ((mem_union.mp w.property).resolve_left out)).2
    obtain ⟨u,hu,v,hv,ne⟩ := one_lt_card.mp orig
    let i : S := ⟨u,rs (mem_inter.mp hu).2⟩
    let j : S := ⟨v,rs (mem_inter.mp hv).2⟩
    have wi : J.Adj w i := Or.inl ((G.mem_neighborFinset _ _).mp (mem_inter.mp hu).1)
    have wj : J.Adj w j := Or.inl ((G.mem_neighborFinset _ _).mp (mem_inter.mp hv).1)
    exact one_lt_card.mpr ⟨i,mem_inter.mpr ⟨(J.mem_neighborFinset _ _).mpr wi,(zm _).mpr (mem_inter.mp hu).2⟩,
      j,mem_inter.mpr ⟨(J.mem_neighborFinset _ _).mpr wj,(zm _).mpr (mem_inter.mp hv).2⟩,fun h => ne (congrArg Subtype.val h)⟩
  have degree (x y : S) (xy : J.Adj x y) (nonedge : ¬H.Adj x y) : Fintype.card S+1 ≤ H.degree x+H.degree y := by
    obtain ⟨xr,yr,ne⟩ := xy.resolve_left nonedge
    have dx := minimum _ xr
    have dy := minimum _ yr
    exact pair_degree B R S sb near removed xr yr ne (by omega)
  have linked : Graph189LinkedExterior.Linked H d := by
    refine ⟨univ,by simpa using size,?_⟩
    intro x _ y _ ne
    obtain ⟨q,hq,sz⟩ := route_clique Z complete ports x y ne
    obtain ⟨r,hr,count⟩ := Graph189LongPathClosure.long_of_supergraph (G:=H) (K:=J)
      (fun _ _ h => Or.inl h) degree q hq
    rw [zsize] at sz
    exact ⟨r,hr,rows.trans (sz.trans count),fun w _ => mem_univ w⟩
  exact Graph189LinkedExterior.map (Embedding.induce (G:=G) (S : Set V)).toHom Subtype.val_injective linked
theorem of_minimum (z : V) {l : ℕ} (three : 3 ≤ l) (minimum : ∀ v, l ≤ G.degree v) :
    Graph189LinkedExterior.Linked G l := by
  let L := 2*l-3
  by_cases long : ∃ x, ∃ q : G.Walk x x, q.IsCycle ∧ L+1 ≤ q.length
  · obtain ⟨_,q,hq,sz⟩ := long
    apply Graph189NativeCycleLinked.of_cycle q hq <;> dsimp [L] at sz <;> omega
  have short (x : V) (q : G.Walk x x) (hq : q.IsCycle) : q.length ≤ L := by
    by_contra! big
    exact long ⟨x,q,hq,big⟩
  obtain ⟨B,E,sz,sub,len,near⟩ := Graph189RotationExterior.degree_window z (by dsimp [L]; omega) minimum short
  exact linked_of_window B E sz sub (by dsimp [L] at len; omega) (fun w _ => minimum w) near
end Graph189RotationLinked
end
section
open SimpleGraph Finset
universe u
namespace Graph189ExteriorCore
structure Core {V : Type u} (G : SimpleGraph V) (d : ℕ) where
  X : Type u
  [finite : Fintype X]
  root : X
  graph : SimpleGraph X
  [decAdj : DecidableRel graph.Adj]
  hom : graph →g G
  injective : Function.Injective hom
  degree : ∀ x, d ≤ graph.degree x
instance {V : Type u} {G : SimpleGraph V} {d : ℕ} (K : Core G d) : Fintype K.X := K.finite
instance {V : Type u} {G : SimpleGraph V} {d : ℕ} (K : Core G d) : DecidableRel K.graph.Adj := K.decAdj
def Core.map_into {V W : Type u} {G : SimpleGraph V} {H : SimpleGraph W} {d : ℕ}
    (K : Core G d) (f : G →g H) (inj : Function.Injective f) : Core H d where
  X := K.X
  root := K.root
  graph := K.graph
  hom := f.comp K.hom
  injective := inj.comp K.injective
  degree := K.degree
theorem of_nonisolated {V : Type u} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
    [DecidableRel G.Adj] {d : ℕ} (edge : ∃ x y, G.Adj x y)
    (degree : ∀ x y, G.Adj x y → d ≤ G.degree x) : Nonempty (Core G d) := by
  classical
  let S : Set V := {v | ∃ w, G.Adj v w}
  obtain ⟨x,y,e⟩ := edge
  refine ⟨{
    X := S
    root := ⟨x,y,e⟩
    graph := G.induce S
    hom := (Embedding.induce (G:=G) S).toHom
    injective := Subtype.val_injective
    degree := ?_ }⟩
  intro a
  rw [Graph189ExteriorDegreeCycle.degree_induce_filter]
  have eq : (G.neighborFinset a.val).filter (fun u => u ∈ S) = G.neighborFinset a.val := by
    apply filter_eq_self.mpr
    exact fun u hu => ⟨a.val,((G.mem_neighborFinset _ _).mp hu).symm⟩
  rw [eq,G.card_neighborFinset_eq_degree]
  obtain ⟨b,adj⟩ := a.property
  exact degree a.val b adj
end Graph189ExteriorCore
end
section
namespace Graph189ExteriorDegreeCycle
open Finset SimpleGraph Graph189ExteriorGap
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
private theorem insert_two {V : Type*} [DecidableEq V] {G : SimpleGraph V} {u v a b : V}
    (p : G.Walk u v) (hp : p.IsPath) (i : ℕ) (valid : i+1 < p.support.length)
    (ha : a ∉ p.support) (hb : b ∉ p.support) (ab : G.Adj a b)
    (first : G.Adj (p.getVert i) a) (last : G.Adj b (p.getVert (i+1)))
    (covers : ∀ z, z=a ∨ z=b ∨ z ∈ p.support) :
    ∃ x y, ∃ q : G.Walk x y, q.IsHamiltonian := by
  let A := p.support.take (i+1)
  let B := p.support.drop (i+1)
  have pl : p.support=A++B := (List.take_append_drop _ _).symm
  have nd := hp.support_nodup
  have chain := p.isChain_adj_support
  rw [pl] at nd chain ha hb
  have front : i < p.support.length := by omega
  have la : A.getLast? = some p.support[i] :=
    (congrArg List.getLast? (List.take_succ_eq_append_getElem front)).trans List.getLast?_concat
  have fb : B.head? = some p.support[i+1] := by simp [B,List.head?_drop]
  have ca : (A++[a,b]).IsChain G.Adj := by
    apply chain.left_of_append.append (by simp [ab])
    intro z hz w hw
    rw [la] at hz
    have zz : p.support[i]=z := by simpa using hz
    have ww : a=w := by simpa using hw
    subst w
    exact zz ▸ (by simpa [get_at] using first)
  let L := (A++[a,b])++B
  have ch : L.IsChain G.Adj := by
    apply ca.append chain.right_of_append
    intro z hz w hw
    have zz : b=z := by simpa [List.getLast?_append] using hz
    rw [fb] at hw
    have ww : p.support[i+1]=w := by simpa using hw
    subst z
    exact ww ▸ (by simpa [get_at] using last)
  have new : L.Nodup := by
    refine List.Nodup.append ?_ nd.of_append_right ?_
    · apply List.Nodup.append nd.of_append_left (by simp [ab.ne])
      apply List.disjoint_left.mpr
      intro z hz hz'
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz'
      rcases hz' with rfl|rfl
      · exact ha (List.mem_append_left _ hz)
      · exact hb (List.mem_append_left _ hz)
    · apply List.disjoint_left.mpr
      intro z hz hzB
      rcases List.mem_append.mp hz with hzA|hz'
      · exact List.disjoint_left.mp nd.disjoint hzA hzB
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at hz'
        rcases hz' with rfl|rfl
        · exact ha (List.mem_append_right _ hzB)
        · exact hb (List.mem_append_right _ hzB)
  have non : L≠[] := by simp [L]
  let q := Walk.ofSupport L non ch
  have qs : q.support=L := Walk.support_ofSupport non ch
  refine ⟨_,_,q,(Walk.IsPath.mk' (by rwa [qs] : q.support.Nodup)).isHamiltonian_of_mem ?_⟩
  intro z
  rw [qs]
  rcases covers z with rfl|rfl|old
  · simp [L]
  · simp [L]
  · rw [pl,List.mem_append] at old
    simp only [L,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
    tauto
theorem singleton_minimum_deletion_traceable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (w : V) (minw : G.degree w=G.minDegree)
    {u v : {x : V | x ≠ w}} (p : (G.induce {x : V | x ≠ w}).Walk u v) (hp : p.IsPath)
    (longest : ∀ {i j}, ∀ q : (G.induce {x : V | x ≠ w}).Walk i j, q.IsPath → q.length ≤ p.length)
    (x : {z : V | z ≠ w}) (outside : x∉p.support) (sole : ∀ y, y ≠ x → y∈p.support)
    (large : 3 ≤ G.secondSmallestDegree) (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) :
    ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian := by
  classical
  let S := {v : V | v ≠ w}
  let H := G.induce S
  have high (z : S) : G.secondSmallestDegree ≤ G.degree z.val := by
    rcases degree_pair (G:=G) z.val w z.property with h|h
    · exact h
    · rw [minw] at h
      exact h.trans (G.minDegree_le_degree z.val)
  have iso (y : S) (adj : H.Adj x y) : y ∈ p.support := sole y adj.ne.symm
  obtain ⟨xw,full⟩ := high_isolated_saturation w p hp longest x outside iso (by omega) (high x) (cap x.val)
  have count : (contactPositions p x).card=H.degree x := by
    rw [contact_card_neighbors p hp x,inter_eq_left.mpr (fun y hy =>
      List.mem_toFinset.mpr (iso y ((H.mem_neighborFinset x y).mp hy))),H.card_neighborFinset_eq_degree]
  have lost := degree_le_deletion_add_one (G:=G) w x
  change G.degree x.val ≤ H.degree x+1 at lost
  obtain ⟨i,hi,hi₂⟩ : ∃ i∈contactPositions p x, i+2∈contactPositions p x := by
    by_contra! no
    have wide (i : ℕ) (hi : i∈contactPositions p x) (j : ℕ) (hj : j∈contactPositions p x)
        (lt : i < j) : i+3 ≤ j := by
      obtain ⟨ir,ic⟩ := (mem_contactPositions p x i).mp hi
      obtain ⟨jr,jc⟩ := (mem_contactPositions p x j).mp hj
      have sep := omitted_contact_spacing p hp longest outside ⟨i,ir⟩ ⟨j,jr⟩ lt
        (by simpa [get_at] using ic) (by simpa [get_at] using jc)
      change i+2 ≤ j at sep
      by_contra! bad
      exact no i hi ((show j=i+2 by omega) ▸ hj)
    have expensive := double_positions_le_path_shell p hp longest outside wide
    rw [full,count] at expensive
    have := high x
    omega
  obtain ⟨ir,ic⟩ := (mem_contactPositions p x i).mp hi
  obtain ⟨jr,jc⟩ := (mem_contactPositions p x (i+2)).mp hi₂
  let m := p.getVert (i+1)
  have mx : m≠x := fun h => outside (h ▸ p.getVert_mem_support (i+1))
  obtain ⟨b,c,q,hq,len,sup⟩ := swap_contact_midpoint p hp outside i jr ic jc
  have never : m∉q.support := by
    intro h
    have member := List.mem_toFinset.mpr h
    rw [sup] at member
    exact (mem_insert.mp member).elim mx (fun t => (mem_erase.mp t).1 rfl)
  have iso' (y : S) (adj : H.Adj m y) : y∈q.support := by
    apply List.mem_toFinset.mp
    rw [sup]
    by_cases same : y=x
    · exact mem_insert.mpr (Or.inl same)
    · exact mem_insert.mpr (Or.inr (mem_erase.mpr ⟨adj.ne.symm,List.mem_toFinset.mpr (sole y same)⟩))
  have qlong {a b} (r : H.Walk a b) (hr : r.IsPath) : r.length ≤ q.length := by
    rw [len]
    exact longest r hr
  obtain ⟨mw,_⟩ := high_isolated_saturation w q hq qlong m never iso' (by omega) (high m) (cap m.val)
  let f := (Embedding.induce (G:=G) S).toHom
  let P := p.map f
  have path : P.IsPath := (Walk.isPath_map_iff_of_injective (f:=f) Subtype.val_injective).mpr hp
  have members (z : V) : z∈P.support ↔ ∃ t : S, t∈p.support ∧ (t.val:V)=z := by
    rw [show P=p.map f from rfl,Walk.support_map]
    exact List.mem_map
  have PL := P.length_support
  have old := p.length_support
  have eqLen : P.length=p.length := Walk.length_map f p
  refine insert_two P path i (by omega) (a:=x.val) (b:=w) ?_ ?_ xw ?_ ?_ ?_
  · intro h
    obtain ⟨t,ht,te⟩ := (members _).mp h
    exact outside ((Subtype.ext te : t=x) ▸ ht)
  · intro h
    obtain ⟨t,_,te⟩ := (members _).mp h
    exact t.property te
  · change G.Adj ((p.map f).getVert i) x.val
    rw [Walk.getVert_map]
    exact ic
  · change G.Adj w ((p.map f).getVert (i+1))
    rw [Walk.getVert_map]
    exact mw.symm
  · intro z
    by_cases zw : z=w
    · exact Or.inr (Or.inl zw)
    · let t : S := ⟨z,zw⟩
      by_cases tx : t=x
      · exact Or.inl (congrArg Subtype.val tx)
      · exact Or.inr (Or.inr ((members z).mpr ⟨t,sole t tx,rfl⟩))
end Graph189ExteriorDegreeCycle
end
section
namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
theorem minimum_deletion_exterior_edge (w : V) (minw : G.degree w=G.minDegree)
    {u v : {x : V | x ≠ w}} (p : (G.induce {x : V | x ≠ w}).Walk u v) (hp : p.IsPath)
    (longest : ∀ {i j}, ∀ q : (G.induce {x : V | x ≠ w}).Walk i j, q.IsPath → q.length ≤ p.length)
    (notTrace : ¬ ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian)
    (notH : ¬ ∃ a b, ∃ q : (G.induce {x : V | x ≠ w}).Walk a b, q.IsHamiltonian)
    (large : 3 ≤ G.secondSmallestDegree) (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) :
    ∃ a ∉ p.support, ∃ b ∉ p.support, (G.induce {x : V | x ≠ w}).Adj a b := by
  classical
  by_contra! independent
  obtain ⟨a,ha⟩ : ∃ a, a ∉ p.support := by
    by_contra! all
    exact notH ⟨u,v,p,hp.isHamiltonian_of_mem all⟩
  have high (a : {x : V | x ≠ w}) : G.secondSmallestDegree ≤ G.degree a.val := by
    rcases degree_pair (G:=G) a.val w a.property with h|h
    · exact h
    · rw [minw] at h
      exact h.trans (G.minDegree_le_degree a.val)
  have sole (b : {x : V | x ≠ w}) (ne : b≠a) : b∈p.support := by
    by_contra hb
    exact ne (unique_high_isolated w p hp longest independent (by omega) cap hb ha (high b) (high a))
  exact notTrace (singleton_minimum_deletion_traceable w minw p hp longest a ha sole large cap)
end Graph189ExteriorDegreeCycle
end
section
open SimpleGraph Finset Graph189UniversalCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ExteriorDegreeCycle
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
theorem minimum_completion_exterior_core (w : V) (minw : G.degree w=G.minDegree)
    {a : V} (C : (completeAt G w).Walk a a) (hC : C.IsCycle)
    (longest : ∀ v (q : (completeAt G w).Walk v v), q.IsCycle → q.length ≤ C.length)
    (notTrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    (notH : ¬ ∃ a b, ∃ p : (G.induce {x : V | x ≠ w}).Walk a b, p.IsHamiltonian)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (k5 : 5 ≤ G.secondSmallestDegree) :
    Nonempty (Graph189ExteriorCore.Core ((completeAt G w).induce {v : V | v ∉ C.support})
      ((G.secondSmallestDegree-1)/2)) := by
  classical
  let U : Set V := {v | v ≠ w}
  let H := G.induce U
  obtain ⟨u,v,p,hp,_,support,maxp⟩ := longest_in_deletion G w C hC longest
  have mx {x y} (r : H.Walk x y) (hr : r.IsPath) : r.length ≤ p.length := maxp _ _ r hr
  let T : Set U := {t | t ∉ p.support.toFinset}
  let J := H.induce T
  have edge := minimum_deletion_exterior_edge w minw p hp mx notTrace notH (by omega) cap
  have high (v : U) : G.secondSmallestDegree ≤ G.degree v.val := by
    rcases degree_pair (G:=G) v.val w v.property with h|h
    · exact h
    · rw [minw] at h
      exact h.trans (G.minDegree_le_degree _)
  have connectedEdge : ∃ x y, J.Adj x y := by
    obtain ⟨x,hx,y,hy,xy⟩ := edge
    exact ⟨⟨x,fun h => hx (List.mem_toFinset.mp h)⟩,⟨y,fun h => hy (List.mem_toFinset.mp h)⟩,xy⟩
  have degree (x y : T) (adj : J.Adj x y) : (G.secondSmallestDegree-1)/2 ≤ J.degree x := by
    let D := G.secondSmallestDegree-1
    have bound (v : U) : D+1 ≤ G.degree v.val := by dsimp [D]; have := high v; omega
    have da := deletion_exterior_local_degree w p hp mx
      (a:=x.val) (b:=y.val) (fun h => x.property (List.mem_toFinset.mpr h))
      (fun h => y.property (List.mem_toFinset.mpr h)) adj (cap x.val.val) (bound x.val) (bound y.val)
    change 2*D ≤ G.secondSmallestDegree+2*(H.neighborFinset x.val \ p.support.toFinset).card at da
    change _ ≤ (H.induce T).degree x
    rw [degree_induce_filter]
    have same : (H.neighborFinset x.val).filter (fun v => v ∈ T) = H.neighborFinset x.val \ p.support.toFinset := by
      ext v
      simp [T]
    rw [same]
    dsimp [D] at da
    omega
  obtain ⟨core⟩ := Graph189ExteriorCore.of_nonisolated connectedEdge degree
  let f : J →g (completeAt G w).induce {v : V | v ∉ C.support} := {
    toFun := fun v => ⟨v.val.val,fun h => v.property (List.mem_toFinset.mpr ((support _).mpr h))⟩
    map_rel' := fun h => Or.inl h }
  have inj : Function.Injective f := by
    intro x y eq
    exact Subtype.ext (Subtype.ext (congrArg (fun v : {u : V | u ∉ C.support} => v.val) eq))
  exact ⟨core.map_into f inj⟩
end Graph189ExteriorDegreeCycle
end
section
abbrev Arxiv.«2606.03696».offWalk {V : Type*} {G : SimpleGraph V} {x y : V} (q : G.Walk x y) : Set V :=
  OMA.BondyK.offWalk q
end
section
namespace OMA.BondyK
open SimpleGraph Finset Arxiv.«2606.03696»
theorem graph189_order_of_linked {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {k : ℕ}
    (hk : 1 ≤ k) (min : k ≤ G.minDegree)
    (deletion : ∀ S : Finset V, S.card < k → (G.induce ((S : Set V)ᶜ)).Connected)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (longest : ∀ b, ∀ Q : G.Walk b b, Q.IsCycle → Q.length ≤ C.length)
    (linked : Graph189LinkedExterior.Linked (G.induce (offWalk C)) k) :
    (k+1)*(G.minDegree-k+2)-1 ≤ Fintype.card V := by
  classical
  by_contra! fail
  have order : Fintype.card V+2≤(k+1)*(G.minDegree-k+2) := by omega
  have hkn : Fintype.card V+k*(k-1)≤(k+1)*G.minDegree := by
    obtain ⟨d,hd⟩ := Nat.exists_eq_add_of_le min
    rw [hd,Nat.add_sub_cancel_left] at order
    rw [hd]
    obtain ⟨h,hl⟩ := Nat.exists_eq_add_of_le hk
    rw [hl,Nat.add_sub_cancel_left]
    rw [hl] at order
    nlinarith
  let L : Set ℕ := {m | ∃ b, ∃ q : G.Walk b b, q.IsCycle ∧ q.length=m}
  have mem : C.length∈L := ⟨a,C,hC,rfl⟩
  have upper : ∀ m∈L, m ≤ C.length := by
    rintro m ⟨b,q,hq,rfl⟩
    exact longest b q hq
  have hlong : C.length=G.circumference :=
    (le_csSup ⟨C.length,upper⟩ mem).antisymm (csSup_le ⟨_,mem⟩ upper)
  obtain ⟨D,size,paths⟩ := linked
  obtain ⟨u,hu⟩ := Finset.card_pos.mp (show 0 < D.card by omega)
  have hD := cy_of C hC hlong
  have hsupp := mem_support_cyc C hC
  have mem_s : ∀ y, y ∈ offWalk C ↔ y ∉ C.support := fun y => Iff.rfl
  classical
  obtain ⟨H, hH⟩ : ∃ H : Finset V, H = Finset.univ.filter
      (fun y => ∃ hy : y ∈ offWalk C, (G.induce (offWalk C)).Reachable u ⟨y, hy⟩) := ⟨_, rfl⟩
  have memH : ∀ y, y ∈ H ↔ ∃ hy : y ∈ offWalk C, (G.induce (offWalk C)).Reachable u ⟨y, hy⟩ := by
    intro y; simp [hH]
  have hComp : Comp G (cyc C) H := by
    refine ⟨?_, ?_, ?_⟩
    · intro x hx t ht
      obtain ⟨hxs, -⟩ := (memH x).mp hx
      exact (mem_s x).mp hxs ((hsupp x).mpr ⟨t, ht⟩)
    · intro x hx y hxy
      obtain ⟨hxs, hr⟩ := (memH x).mp hx
      by_cases hy : y ∈ C.support
      · exact Or.inr ((hsupp y).mp hy)
      · left
        have hys : y ∈ offWalk C := (mem_s y).mpr hy
        exact (memH y).mpr ⟨hys, hr.trans (Adj.reachable (G := G.induce (offWalk C))
          (u := ⟨x, hxs⟩) (v := ⟨y, hys⟩) hxy)⟩
    · intro x hx y hy
      obtain ⟨hxs, hrx⟩ := (memH x).mp hx
      obtain ⟨hys, hry⟩ := (memH y).mp hy
      obtain ⟨w⟩ := hrx.symm.trans hry
      obtain ⟨p, hp⟩ := w.toPath
      refine ⟨p.support.map Subtype.val, ?_, ?_, ?_, ?_, ?_⟩
      · exact hp.support_nodup.map Subtype.val_injective
      · exact (List.isChain_map Subtype.val).mpr p.isChain_adj_support
      · intro z hz
        obtain ⟨z', hz', rfl⟩ := List.mem_map.mp hz
        exact (memH z').mpr ⟨z'.2, hrx.trans (reach_mem p hz')⟩
      · rw [← p.cons_tail_support, List.map_cons, List.head?_cons]
      · rw [List.getLast?_map, List.getLast?_eq_getLast_of_ne_nil (Walk.support_ne_nil _),
          Walk.getLast_support]; rfl
  have hKs : KSep G k := by
    intro S hS X hXS hXcl hXne y hyS hyX
    obtain ⟨x, hx⟩ := hXne
    have hconn := deletion S (by omega)
    obtain ⟨w⟩ := hconn.preconnected ⟨x, hXS x hx⟩ ⟨y, hyS⟩
    have key : ∀ (p q : ((S : Set V)ᶜ : Set V)) (w : (G.induce ((S : Set V)ᶜ)).Walk p q),
        p.1 ∈ X → q.1 ∈ X := by
      intro p q w
      induction w with
      | nil => exact id
      | @cons p0 p1 q h w ih =>
        intro hp
        exact ih (hXcl _ hp _ h (fun h' => p1.2 h'))
    exact hyX (key _ _ w hx)
  let e : offWalk C ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  let M := D.map e
  have sub : M⊆H := by
    intro z hz
    obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hz
    apply (memH _).mpr
    refine ⟨y.property,?_⟩
    by_cases eq : u=y
    · subst y
      exact SimpleGraph.Reachable.refl _
    · obtain ⟨p,_,_,_⟩ := paths u hu y hy eq
      exact ⟨p⟩
  have msize : k+1 ≤ M.card := by simpa [M] using size
  apply linked_contra hD hComp (fun x => G.minDegree_le_degree x) hk hkn hKs sub msize
  intro x hx y hy ne
  obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hx
  obtain ⟨w,hw,rfl⟩ := Finset.mem_map.mp hy
  obtain ⟨p,hp,plen,within⟩ := paths v hv w hw (fun same => ne (congrArg e same))
  refine ⟨p.support.map Subtype.val,?_,by simpa only [List.length_map] using plen⟩
  refine ⟨hp.support_nodup.map Subtype.val_injective,
    (List.isChain_map Subtype.val).mpr p.isChain_adj_support,?_,?_,?_⟩
  · intro z hz
    obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hz
    exact Finset.mem_map.mpr ⟨b,within b hb,rfl⟩
  · rw [← p.cons_tail_support, List.map_cons, List.head?_cons]
    all_goals rfl
  · rw [List.getLast?_map, List.getLast?_eq_getLast_of_ne_nil (Walk.support_ne_nil _),
        Walk.getLast_support]
    rfl
end OMA.BondyK
end
section
open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y a b : V}
theorem splice_support (p : G.Walk x y) (hp : p.IsPath)
    (A J B : List V) (split : p.support = A ++ J ++ B)
    (q : G.Walk a b) (hq : q.IsPath) (disjoint : List.Disjoint q.support p.support)
    (left : ∀ z∈A.getLast?, G.Adj z a) (right : ∀ z∈B.head?, G.Adj b z) :
    ∃ u v, ∃ r : G.Walk u v, r.IsPath ∧ r.support = A ++ q.support ++ B := by
  classical
  let L := (A ++ q.support) ++ B
  have pnd := hp.support_nodup
  have pc := p.isChain_adj_support
  rw [split] at pnd pc disjoint
  have ca := pc.left_of_append.left_of_append
  have cb := pc.right_of_append
  have qsHead : q.support.head? = some a := by
    rw [List.head?_eq_some_head q.support_ne_nil, q.head_support]
  have qsLast : q.support.getLast? = some b := by
    rw [List.getLast?_eq_some_getLast q.support_ne_nil, q.getLast_support]
  have first : (A++q.support).IsChain G.Adj := by
    apply ca.append q.isChain_adj_support
    intro z hz w hw
    rw [qsHead] at hw
    have same : a=w := by simpa using hw
    exact same ▸ left z hz
  have chain : L.IsChain G.Adj := by
    apply first.append cb
    intro z hz w hw
    have last : (A++q.support).getLast? = some b := by
      simp [List.getLast?_append,qsLast]
    rw [last] at hz
    have same : b=z := by simpa using hz
    exact same ▸ right w hw
  have nd : L.Nodup := by
    refine List.Nodup.append ?_ pnd.of_append_right ?_
    · apply List.Nodup.append pnd.of_append_left.of_append_left hq.support_nodup
      rw [List.disjoint_left]
      intro z hzA hzQ
      exact List.disjoint_left.mp disjoint hzQ (by simp [hzA])
    · rw [List.disjoint_left]
      intro z hz hzB
      rcases List.mem_append.mp hz with hzA | hzQ
      · exact List.disjoint_left.mp pnd.disjoint (by simp [hzA]) hzB
      · exact List.disjoint_left.mp disjoint hzQ (by simp [hzB])
  have hn : L≠[] := by simp [L,q.support_ne_nil]
  let r := Walk.ofSupport L hn chain
  have rs : r.support = L := Walk.support_ofSupport hn chain
  exact ⟨_,_,r,Walk.IsPath.mk' (by rwa [rs]),rs⟩
private theorem kept_gap (p : G.Walk x y) (hp : p.IsPath) (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support →
      r.length ≤ p.length)
    (A J B : List V) (split : p.support = A ++ J ++ B)
    (kept : p.support[t.val] ∈ A ∨ p.support[t.val] ∈ B)
    (q : G.Walk a b) (hq : q.IsPath) (disjoint : List.Disjoint q.support p.support)
    (left : ∀ z∈A.getLast?, G.Adj z a) (right : ∀ z∈B.head?, G.Adj b z) :
    q.support.length ≤ J.length := by
  obtain ⟨u,v,r,hr,rs⟩ := splice_support p hp A J B split q hq disjoint left right
  have member : p.support[t.val] ∈ r.support := by
    rw [rs]
    rcases kept with h | h <;> simp [h]
  have cmp := longest r hr member
  have pr := p.length_support
  have qr := r.length_support
  rw [split] at pr
  rw [rs] at qr
  simp only [List.length_append] at pr qr
  omega
private theorem mem_kept_suffix {L : List V} {t i : Fin L.length} (hi : i ≤ t) :
    L[t.val] ∈ L.drop i.val := by
  apply List.mem_drop_iff_getElem.mpr
  have le : i.val ≤ t.val := hi
  exact ⟨t.val-i.val,by have := t.isLt; omega,by simp [Nat.add_sub_of_le le]⟩
private theorem mem_kept_prefix {L : List V} {t i : Fin L.length} (hi : t ≤ i) :
    L[t.val] ∈ L.take (i.val+1) := by
  apply List.mem_take_iff_getElem.mpr
  exact ⟨t.val,lt_min (by change t.val ≤ i.val at hi; omega) t.isLt,rfl⟩
theorem protected_prefix_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (i : Fin p.support.length) (hi : i ≤ t) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (contact : G.Adj b p.support[i.val]) : q.support.length ≤ i.val := by
  let L := p.support
  have head : (L.drop i.val).head? = some L[i.val] := by
    simp [List.head?_drop]
  have gap := kept_gap p hp t longest [] (L.take i.val) (L.drop i.val)
    (by simp [L]) (Or.inr (mem_kept_suffix hi)) q hq disjoint (by simp) (by
      intro z hz
      rw [head] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact)
  have small := List.length_take_le i.val L
  omega
theorem protected_suffix_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (i : Fin p.support.length) (ht : t ≤ i) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (contact : G.Adj p.support[i.val] a) : i.val + 1 + q.support.length ≤ p.support.length := by
  let L := p.support
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have gap := kept_gap p hp t longest (L.take (i.val+1)) (L.drop (i.val+1)) []
    (by simp [L]) (Or.inl (mem_kept_prefix ht)) q hq disjoint (by
      intro z hz
      rw [last] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact) (by simp)
  simp only [L,List.length_drop] at gap
  have ilt := i.isLt
  omega
theorem protected_interval_of_detour (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (i j : Fin p.support.length) (hij : i < j) (ht : j ≤ t ∨ t ≤ i) (q : G.Walk a b) (hq : q.IsPath)
    (disjoint : List.Disjoint q.support p.support)
    (left : G.Adj p.support[i.val] a) (right : G.Adj b p.support[j.val]) :
    i.val+1+q.support.length ≤ j.val := by
  let L := p.support
  let gap := j.val-(i.val+1)
  have ij : i.val+1+gap=j.val := by
    change i.val < j.val at hij
    dsimp [gap]
    omega
  have split : L = L.take (i.val+1) ++ (L.drop (i.val+1)).take gap ++ L.drop j.val := by
    rw [←List.take_add,ij,List.take_append_drop]
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have head : (L.drop j.val).head? = some L[j.val] := by
    simp [List.head?_drop]
  have bound := kept_gap p hp t longest _ _ _ split (ht.elim (fun h => Or.inr (mem_kept_suffix h))
    (fun h => Or.inl (mem_kept_prefix h))) q hq disjoint (by
    intro z hz
    rw [last] at hz
    have eq : L[i.val] = z := by simpa using hz
    exact eq ▸ left) (by
    intro z hz
    rw [head] at hz
    have eq : L[j.val] = z := by simpa using hz
    exact eq ▸ right)
  have small := List.length_take_le gap (L.drop (i.val+1))
  omega
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x y : V}
omit [Fintype V] in
theorem route_of_induced_hamilton (p : G.Walk x y) (K : Finset V)
    (outside : ∀ z∈K, z∉p.support) {a b : K}
    {q : (G.induce (K : Set V)).Walk a b} (hq : q.IsHamiltonian) :
    ExteriorRoute p a.val b.val K.card := by
  let e := SimpleGraph.Embedding.induce (G := G) (K : Set V)
  let r := q.map e.toHom
  refine ⟨r, hq.isPath.map e.injective, ?_, ?_⟩
  · rw [List.disjoint_left]
    intro z hz hp
    change z∈(q.map e.toHom).support at hz
    rw [Walk.support_map] at hz
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hz
    exact outside w.val w.property hp
  · change K.card≤(q.map e.toHom).support.length
    rw [Walk.support_map,List.length_map,hq.length_support]
    simp
theorem exterior_hamilton_connected_matching (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → r.length ≤ p.length)
    (K : Finset V) (size : 1 < K.card) (outside : ∀ z∈K, z∉p.support)
    (hconn : ∀ a b : K, a≠b → ∃ q : (G.induce (K : Set V)).Walk a b, q.IsHamiltonian)
    (marks : Finset (Fin p.support.length)) (nonempty : marks.Nonempty)
    (attach : marks ↪ K) (contacts : ∀ i : marks, G.Adj p.support[i.val.val] (attach i).val) :
    (marks.card+2)*K.card + marks.card ≤ Fintype.card V := by
  classical
  obtain ⟨j,hj⟩ : ∃ j : ℕ, marks.card=j+1 := ⟨marks.card-1, by
    have := Finset.card_pos.mpr nonempty
    omega⟩
  let iso := marks.orderIsoOfFin hj
  let M := marks.orderEmbOfFin hj
  let T := fun i : Fin (j+1) => attach (iso i)
  have touching (i : Fin (j+1)) : G.Adj p.support[(M i).val] (T i).val := contacts (iso i)
  have inj : Function.Injective T := attach.injective.comp iso.injective
  have route (a b : K) (ne : a≠b) : ExteriorRoute p a.val b.val K.card := by
    obtain ⟨q,hq⟩ := hconn a b ne
    exact route_of_induced_hamilton p K outside hq
  have another (w : K) : ∃ z : K, z≠w := by
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp size
    by_cases eq : a=w.val
    · exact ⟨⟨b,hb⟩,fun h => hab (eq.trans (congrArg Subtype.val h).symm)⟩
    · exact ⟨⟨a,ha⟩,fun h => eq (congrArg Subtype.val h)⟩
  have inner (i : Fin j) : ExteriorRoute p (T i.castSucc).val (T i.succ).val K.card :=
    route _ _ (inj.ne (ne_of_lt i.castSucc_lt_succ))
  obtain ⟨a,ha⟩ := another (T 0)
  obtain ⟨b,hb⟩ := another (T (Fin.last j))
  have bound := longest_matched_route_order p hp longest M (fun i => (T i).val) touching inner
    ⟨a.val,route _ _ ha⟩ ⟨b.val,route _ _ hb.symm⟩
  have total := card_outside_add_path p hp K outside
  rw [hj]
  simp only [Nat.mul_add,Nat.mul_one,Nat.add_mul] at bound ⊢
  omega
end Graph189ExteriorGap
end
section
open Finset
namespace Graph189ExteriorGap
variable {L R : Type*} [Fintype L] [DecidableEq L] [DecidableEq R]
theorem hall_at_least (neighbors : L → Finset R) (s : ℕ) (small : s ≤ Fintype.card L)
    (hall : ∀ T : Finset L, T.card ≤ (T.biUnion neighbors).card + (Fintype.card L-s)) :
    ∃ U : Finset L, s ≤ U.card ∧ ∃ f : U ↪ R, ∀ u, f u ∈ neighbors u.val := by
  classical
  let d := Fintype.card L-s
  let choices := fun u : L => (neighbors u).disjSum (Finset.univ : Finset (Fin d))
  have full (T : Finset L) : T.card ≤ (T.biUnion choices).card := by
    by_cases empty : T=∅
    · simp [empty]
    obtain ⟨u,hu⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have eq : T.biUnion choices = (T.biUnion neighbors).disjSum (Finset.univ : Finset (Fin d)) := by
      ext k
      cases k with
      | inl x => simp [choices]
      | inr y =>
        simp [choices]
        exact ⟨u,hu⟩
    rw [eq,Finset.card_disjSum,Finset.card_univ,Fintype.card_fin]
    exact hall T
  obtain ⟨f,hf,acceptable⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' choices).mp full
  let U := (Finset.univ : Finset L).filter (fun u => ∃ r : R, f u = Sum.inl r)
  have real (u : U) : ∃ r : R, f u.val = Sum.inl r := (Finset.mem_filter.mp u.property).2
  let g := fun u : U => (real u).choose
  have hg (u : U) : f u.val = Sum.inl (g u) := (real u).choose_spec
  have gi : Function.Injective g := by
    intro u v eq
    apply Subtype.ext
    apply hf
    exact (hg u).trans ((congrArg Sum.inl eq).trans (hg v).symm)
  let D := (Finset.univ : Finset L) \ U
  have dummy (u : D) : ∃ i : Fin d, f u.val = Sum.inr i := by
    cases eq : f u.val with
    | inr j => exact ⟨j,rfl⟩
    | inl r => exact ((Finset.mem_sdiff.mp u.property).2 (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _,r,eq⟩)).elim
  let index := fun u : D => (dummy u).choose
  have di : Function.Injective index := by
    intro u v eq
    apply Subtype.ext
    apply hf
    exact (dummy u).choose_spec.trans ((congrArg Sum.inr eq).trans (dummy v).choose_spec.symm)
  have cap := Fintype.card_le_of_injective index di
  change Fintype.card D ≤ Fintype.card (Fin d) at cap
  simp only [Fintype.card_coe,Fintype.card_fin] at cap
  have part := Finset.card_sdiff_add_card_inter (Finset.univ : Finset L) U
  simp only [Finset.univ_inter,Finset.card_univ] at part
  change D.card+U.card=Fintype.card L at part
  refine ⟨U,by dsimp [d] at cap; omega,⟨g,gi⟩,?_⟩
  intro u
  have spec := acceptable u.val
  rw [hg] at spec
  simpa [choices] using spec
theorem hall_on_dense_vertices (neighbors : L → Finset R) (s : ℕ)
    (U : Finset L) (size : U.card=s) (degree : ∀ u∈U, s ≤ (neighbors u).card) :
    ∃ f : U ↪ R, ∀ u, f u ∈ neighbors u.val := by
  classical
  let links := fun u : U => neighbors u.val
  have h (T : Finset U) : T.card ≤ (T.biUnion links).card := by
    by_cases empty : T=∅
    · simp [empty]
    obtain ⟨u,hu⟩ := Finset.nonempty_iff_ne_empty.mpr empty
    have subset : links u ⊆ T.biUnion links := by
      intro z hz
      exact Finset.mem_biUnion.mpr ⟨u,hu,hz⟩
    have small : T.card ≤ U.card := by simpa using T.card_le_univ
    exact (small.trans (size.le.trans (degree u.val u.property))).trans (Finset.card_le_card subset)
  obtain ⟨f,hi,good⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' links).mp h
  exact ⟨⟨f,hi⟩,good⟩
end Graph189ExteriorGap
end
section
open Finset SimpleGraph
namespace Graph189ExteriorAttachment
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
theorem marks_of_many_neighbors (p : G.Walk x y) (W : Finset V) (j : ℕ)
    (size : j ≤ W.card)
    (rows : ∀ w ∈ W, j ≤ ((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w)).card) :
    ∃ marks : Finset (Fin p.support.length), marks.card = j ∧
      ∃ attach : marks ↪ W, ∀ i : marks, G.Adj p.support[i.val.val] (attach i).val := by
  classical
  obtain ⟨U,uw,us⟩ := exists_subset_card_eq size
  let N (w : V) := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] w)
  obtain ⟨f,edges⟩ := Graph189ExteriorGap.hall_on_dense_vertices N j U us (fun w hw => rows w (uw hw))
  let M := (univ : Finset U).image f
  let f' (u : U) : M := ⟨f u,mem_image_of_mem _ (mem_univ _)⟩
  have bij : Function.Bijective f' := by
    constructor
    · intro a b eq; exact f.injective (congrArg Subtype.val eq)
    · intro m
      obtain ⟨u,_,eq⟩ := mem_image.mp m.property
      exact ⟨u,Subtype.ext eq⟩
  let equiv := Equiv.ofBijective f' bij
  let inc : U ↪ W := ⟨fun u => ⟨u.val,uw u.property⟩,
    fun _ _ eq => Subtype.ext (congrArg (fun w : W => w.val) eq)⟩
  have card : M.card = U.card := by simpa using Fintype.card_congr equiv.symm
  refine ⟨M,card.trans us,equiv.symm.toEmbedding.trans inc,?_⟩
  intro m
  have eq : f (equiv.symm m) = m.val := congrArg Subtype.val (equiv.apply_symm_apply m)
  have edge := (mem_filter.mp (edges (equiv.symm m))).2
  rw [eq] at edge
  exact edge
end Graph189ExteriorAttachment
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}
theorem protected_matched_route_order (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → p.support[t.val] ∈ r.support →
      r.length ≤ p.length)
    {j m : ℕ} (mark : Fin (j+1) ↪o Fin p.support.length)
    (port : Fin (j+1) → V) (contacts : ∀ i, G.Adj p.support[(mark i).val] (port i))
    (inner : ∀ i : Fin j, ExteriorRoute p (port i.castSucc) (port i.succ) m)
    (before : ∃ a, ExteriorRoute p a (port 0) m)
    (after : ∃ b, ExteriorRoute p (port (Fin.last j)) b m) :
    (j+1)*(m+1) ≤ p.support.length := by
  let pos (i : Fin (j+1)) := (mark i).val + if t < mark i then m else 0
  have first : m ≤ pos 0 := by
    by_cases h : t < mark 0
    · simp [pos,h]
    obtain ⟨a,q,hq,dis,order⟩ := before
    have bound := protected_prefix_of_detour p hp t longest (mark 0) (le_of_not_gt h)
      q hq dis (contacts 0).symm
    simpa [pos,h] using order.trans bound
  have step (i : Fin j) : pos i.castSucc + (m+1) ≤ pos i.succ := by
    have lt := mark.strictMono i.castSucc_lt_succ
    by_cases left : t < mark i.castSucc
    · obtain ⟨q,hq,dis,order⟩ := inner i
      have bound := protected_interval_of_detour p hp t longest _ _ lt (Or.inr left.le)
        q hq dis (contacts _) (contacts _).symm
      simp only [pos,if_pos left,if_pos (left.trans lt)]
      omega
    by_cases right : t < mark i.succ
    · simp only [pos,if_neg left,if_pos right]
      change (mark i.castSucc).val < (mark i.succ).val at lt
      omega
    obtain ⟨q,hq,dis,order⟩ := inner i
    have bound := protected_interval_of_detour p hp t longest _ _ lt (Or.inl (le_of_not_gt right))
      q hq dis (contacts _) (contacts _).symm
    simp only [pos,if_neg left,if_neg right]
    omega
  have positions (i : Fin (j+1)) : m+i.val*(m+1) ≤ pos i := by
    induction i using Fin.induction with
    | zero => simpa using first
    | succ i ih =>
      have hs := step i
      simp only [Fin.val_succ,Fin.val_castSucc,Nat.succ_mul] at ih ⊢
      omega
  have finish : pos (Fin.last j)+1 ≤ p.support.length := by
    by_cases h : t < mark (Fin.last j)
    · obtain ⟨b,q,hq,dis,order⟩ := after
      have bound := protected_suffix_of_detour p hp t longest _ h.le q hq dis (contacts _)
      simp only [pos,if_pos h]
      omega
    · simpa [pos,h] using (mark (Fin.last j)).isLt
  have last := positions (Fin.last j)
  simp only [Fin.val_last,Nat.succ_mul] at last ⊢
  omega
theorem protected_hamilton_connected_matching [Fintype V] [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (K : Finset V) (size : 1 < K.card) (outside : ∀ z∈K, z∉p.support)
    (hconn : ∀ a b : K, a≠b → ∃ q : (G.induce (K : Set V)).Walk a b, q.IsHamiltonian)
    (marks : Finset (Fin p.support.length)) (nonempty : marks.Nonempty)
    (attach : marks ↪ K) (contacts : ∀ i : marks, G.Adj p.support[i.val.val] (attach i).val) :
    (marks.card+1)*K.card + marks.card ≤ Fintype.card V := by
  classical
  obtain ⟨j,hj⟩ : ∃ j : ℕ, marks.card=j+1 := ⟨marks.card-1, by
    have := Finset.card_pos.mpr nonempty
    omega⟩
  let iso := marks.orderIsoOfFin hj
  let M := marks.orderEmbOfFin hj
  let T := fun i : Fin (j+1) => attach (iso i)
  have touching (i : Fin (j+1)) : G.Adj p.support[(M i).val] (T i).val := contacts (iso i)
  have inj : Function.Injective T := attach.injective.comp iso.injective
  have route (a b : K) (ne : a≠b) : ExteriorRoute p a.val b.val K.card := by
    obtain ⟨q,hq⟩ := hconn a b ne
    exact route_of_induced_hamilton p K outside hq
  have another (w : K) : ∃ z : K, z≠w := by
    obtain ⟨a,ha,b,hb,hab⟩ := Finset.one_lt_card.mp size
    by_cases eq : a=w.val
    · exact ⟨⟨b,hb⟩,fun h => hab (eq.trans (congrArg Subtype.val h).symm)⟩
    · exact ⟨⟨a,ha⟩,fun h => eq (congrArg Subtype.val h)⟩
  have inner (i : Fin j) : ExteriorRoute p (T i.castSucc).val (T i.succ).val K.card :=
    route _ _ (inj.ne (ne_of_lt i.castSucc_lt_succ))
  obtain ⟨a,ha⟩ := another (T 0)
  obtain ⟨b,hb⟩ := another (T (Fin.last j))
  have bound := protected_matched_route_order p hp t longest M (fun i => (T i).val) touching inner
    ⟨a.val,route _ _ ha⟩ ⟨b.val,route _ _ hb.symm⟩
  have total := card_outside_add_path p hp K outside
  rw [hj]
  simp only [Nat.mul_add,Nat.mul_one,Nat.add_mul,Nat.one_mul] at bound ⊢
  omega
theorem protected_order_of_contacts [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (p : G.Walk x y) (hp : p.IsPath) {z : V} (zp : z ∈ p.support)
    (longest : ∀ {a b}, ∀ r : G.Walk a b, r.IsPath → z ∈ r.support → r.length ≤ p.length)
    (W : Finset V) (size : 1 < W.card) (outside : ∀ a ∈ W, a ∉ p.support)
    (hconn : ∀ a b : W, a ≠ b → ∃ q : (G.induce (W : Set V)).Walk a b, q.IsHamiltonian)
    {u : ℕ} (nonzero : 0 < u) (enough : u ≤ W.card)
    (rows : ∀ w ∈ W, u ≤ ((Finset.univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w)).card) :
    (u+1)*W.card+u ≤ Fintype.card V := by
  obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp zp
  let t : Fin p.support.length := ⟨i,hi⟩
  obtain ⟨marks,card,attach,contacts⟩ :=
    Graph189ExteriorAttachment.marks_of_many_neighbors p W u enough rows
  have bound := protected_hamilton_connected_matching p hp t
    (fun r hr member => longest r hr (e ▸ member)) W size outside hconn marks
      (card_pos.mp (by omega)) attach contacts
  rwa [card] at bound
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}
theorem protected_contact_internal (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a : V} (outside : a∉p.support) (i : Fin p.support.length) (contact : G.Adj p.support[i.val] a) :
    0 < i.val ∧ i.val + 1 < p.support.length := by
  let q : G.Walk a a := Walk.nil
  have hq : q.IsPath := by simp [q]
  have hd : List.Disjoint q.support p.support := by simpa [q,List.disjoint_left] using outside
  constructor
  · by_contra! zero
    have le : i ≤ t := by change i.val ≤ t.val; omega
    have bound := protected_prefix_of_detour p hp t longest i le q hq hd contact.symm
    simp only [q,Walk.support_nil,List.length_singleton] at bound
    omega
  · by_contra! last
    have le : t ≤ i := by change t.val ≤ i.val; have := t.isLt; omega
    have bound := protected_suffix_of_detour p hp t longest i le q hq hd contact
    simp only [q,Walk.support_nil,List.length_singleton] at bound
    omega
theorem protected_contact_spacing (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a : V} (outside : a∉p.support) (i j : Fin p.support.length) (ordered : i < j)
    (first : G.Adj p.support[i.val] a) (second : G.Adj p.support[j.val] a) :
    i.val+2 ≤ j.val := by
  let q : G.Walk a a := Walk.nil
  have hq : q.IsPath := by simp [q]
  have hd : List.Disjoint q.support p.support := by simpa [q,List.disjoint_left] using outside
  by_contra! close
  have le : j ≤ t ∨ t ≤ i := by
    change j.val ≤ t.val ∨ t.val ≤ i.val
    change i.val < j.val at ordered
    omega
  have h := protected_interval_of_detour p hp t longest i j ordered le q hq hd first second.symm
  simp only [q,Walk.support_nil,List.length_singleton] at h
  omega
theorem protected_cross_spacing (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    (i j : Fin p.support.length) (ordered : i < j)
    (first : G.Adj p.support[i.val] a) (second : G.Adj p.support[j.val] b) :
    i.val+3 ≤ j.val ∨ i.val+1=t.val ∧ t.val+1=j.val := by
  let q : G.Walk a b := Walk.cons ab Walk.nil
  have hq : q.IsPath := Walk.IsPath.mk' (by simp [q,ab.ne])
  have hd : List.Disjoint q.support p.support := by
    rw [List.disjoint_left]
    intro z hz h
    rcases (show z=a ∨ z=b by simpa [q] using hz) with rfl | rfl
    · exact ha h
    · exact hb h
  by_cases le : j ≤ t ∨ t ≤ i
  · left
    exact protected_interval_of_detour p hp t longest i j ordered le q hq hd first second.symm
  · change ¬(j.val ≤ t.val ∨ t.val ≤ i.val) at le
    omega
private theorem card_protected_cross (A B : Finset ℕ) (t : ℕ) (positive : ∀ i∈A, 0 < i)
    (separated : ∀ i∈A, ∀ j∈B, i=j ∨ i+3 ≤ j ∨ j+3 ≤ i ∨ (i+1=t ∧ t+1=j) ∨ (j+1=t ∧ t+1=i)) :
    A.card+B.card ≤ (crossIndices A B).card+1 := by
  have overlap : ((A.image (fun i => i-1)) ∩ ((A∩B).image (fun i => i+1))) ⊆ {t} := by
    intro v hv
    obtain ⟨i,hi,ei⟩ := mem_image.mp (mem_inter.mp hv).1
    obtain ⟨j,hj,ej⟩ := mem_image.mp (mem_inter.mp hv).2
    have := positive i hi
    have := separated i hi j (mem_inter.mp hj).2
    apply mem_singleton.mpr
    omega
  have loss := Finset.card_le_card overlap
  rw [card_singleton] at loss
  have dis₂ : Disjoint (A.image (fun i => i-1) ∪ (A∩B).image (fun i => i+1)) (B \ A) := by
    rw [Finset.disjoint_left]
    intro t ht hw
    have hb := (Finset.mem_sdiff.mp hw).1
    rcases Finset.mem_union.mp ht with h | h
    · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
      have := positive i hi
      have := separated i hi t hb
      omega
    · obtain ⟨i,hi,eq⟩ := Finset.mem_image.mp h
      have := separated i (Finset.mem_inter.mp hi).1 t hb
      omega
  have inj : Set.InjOn (fun i : ℕ => i-1) (A : Set ℕ) := by
    intro i hi j hj heq
    change i-1=j-1 at heq
    have := positive i hi
    have := positive j hj
    omega
  have cover : (B \ A) ∪ (A∩B) = B := by ext t; simp; tauto
  have dis : Disjoint (B \ A) (A∩B) := Finset.disjoint_left.mpr
    (fun _ h₁ h₂ => (Finset.mem_sdiff.mp h₁).2 (Finset.mem_inter.mp h₂).1)
  have hc := Finset.card_union_of_disjoint dis
  rw [cover] at hc
  have total := card_union_add_card_inter (A.image (fun i => i-1)) ((A∩B).image (fun i => i+1))
  rw [card_image_of_injOn inj,card_image_of_injective _
    (show Function.Injective (fun i : ℕ => i+1) by intro i j h; change i+1=j+1 at h; omega)] at total
  rw [crossIndices,card_union_of_disjoint dis₂]
  omega
theorem protected_cross_indices [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b) :
    ((contactPositions p a).card + (contactPositions p b).card ≤
      (crossIndices (contactPositions p a) (contactPositions p b)).card+1) ∧
      ∀ i ∈ crossIndices (contactPositions p a) (contactPositions p b),
        i < p.support.length ∧ G.dist a (p.getVert i)=2 := by
  classical
  let A := contactPositions p a
  let B := contactPositions p b
  have inside (i : ℕ) (h : i∈A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨hi,hc⟩ := (mem_contactPositions p a i).mp h
    exact protected_contact_internal p hp t longest ha ⟨i,hi⟩ (by simpa [get_at] using hc)
  have own (i j : ℕ) (hi : i∈A) (hj : j∈A) (lt : i < j) : i+2 ≤ j := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p a j).mp hj
    exact protected_contact_spacing p hp t longest ha ⟨i,ri⟩ ⟨j,rj⟩ lt
      (by simpa [get_at] using ci) (by simpa [get_at] using cj)
  have separate (i : ℕ) (hi : i∈A) (j : ℕ) (hj : j∈B) :
      i=j ∨ i+3 ≤ j ∨ j+3 ≤ i ∨ (i+1=t.val ∧ t.val+1=j) ∨ (j+1=t.val ∧ t.val+1=i) := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p b j).mp hj
    rcases lt_trichotomy i j with lt | same | gt
    · have h := protected_cross_spacing p hp t longest ha hb ab ⟨i,ri⟩ ⟨j,rj⟩ lt
        (by simpa [get_at] using ci) (by simpa [get_at] using cj)
      change i+3 ≤ j ∨ i+1=t.val ∧ t.val+1=j at h
      tauto
    · exact Or.inl same
    · have h := protected_cross_spacing p hp t longest hb ha ab.symm ⟨j,rj⟩ ⟨i,ri⟩ gt
        (by simpa [get_at] using cj) (by simpa [get_at] using ci)
      change j+3 ≤ i ∨ j+1=t.val ∧ t.val+1=i at h
      tauto
  have shell (i : ℕ) (hi : i∈crossIndices A B) : i < p.support.length ∧ G.dist a (p.getVert i)=2 := by
    have different (j : ℕ) : a≠p.getVert j := fun eq => ha (eq ▸ p.getVert_mem_support j)
    have ls := p.length_support
    have via (i j : ℕ) (hpi : i < p.support.length) (hj : j∈A) (no : i∉A)
        (ij : G.Adj (p.getVert i) (p.getVert j)) : G.dist a (p.getVert i)=2 := by
      have hc := ((mem_contactPositions p a j).mp hj).2
      exact two_step_metric (different _) (fun h => no ((mem_contactPositions p a i).mpr ⟨hpi,h.symm⟩)) hc.symm ij
    rcases Finset.mem_union.mp hi with h | h
    · rcases Finset.mem_union.mp h with h | h
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
        obtain ⟨pos,back⟩ := inside j hj
        have inrange : j-1 < p.support.length := by omega
        refine ⟨inrange,via (j-1) j inrange hj (fun hi => ?_) ?_⟩
        · have aux := own (j-1) j hi hj (by omega)
          omega
        · have edge := p.adj_getVert_succ (i := j-1) (by omega)
          rwa [show j-1+1=j by omega] at edge
      · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
        have jA := (Finset.mem_inter.mp hj).1
        obtain ⟨_,back⟩ := inside j jA
        refine ⟨back,via (j+1) j back jA (fun hi => ?_) ?_⟩
        · have aux := own j (j+1) jA hi (by omega)
          omega
        · exact (p.adj_getVert_succ (i := j) (by omega)).symm
    · obtain ⟨hB,hA⟩ := Finset.mem_sdiff.mp h
      obtain ⟨ri,ci⟩ := (mem_contactPositions p b i).mp hB
      exact ⟨ri,two_step_metric (different _) (fun h => hA ((mem_contactPositions p a i).mpr ⟨ri,h.symm⟩)) ab ci⟩
  exact ⟨card_protected_cross A B t.val (fun i h => (inside i h).1) separate,shell⟩
theorem protected_cross_positions [DecidableEq V] (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b) :
    (contactPositions p a).card + (contactPositions p b).card ≤
      (p.support.toFinset.filter (fun z => G.dist a z=2)).card+1 := by
  classical
  let A := contactPositions p a
  let B := contactPositions p b
  obtain ⟨count,shell⟩ := protected_cross_indices p hp t longest ha hb ab
  have inj : Set.InjOn p.getVert ((crossIndices A B : Finset ℕ) : Set ℕ) := by
    intro i hi j hj same
    exact hp.getVert_injOn (by change i ≤ p.length; have := (shell i hi).1; have := p.length_support; omega)
      (by change j ≤ p.length; have := (shell j hj).1; have := p.length_support; omega) same
  have incl : (crossIndices A B).image p.getVert ⊆ p.support.toFinset.filter (fun z => G.dist a z=2) := by
    intro z hz
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hz
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support i),(shell i hi).2⟩
  have bound := Finset.card_le_card incl
  rw [Finset.card_image_of_injOn inj] at bound
  exact count.trans (Nat.add_le_add_right bound 1)
variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
theorem protected_exterior_contact_degree (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    (G.neighborFinset a ∩ p.support.toFinset).card + G.degree b ≤
      k+2+((G.neighborFinset b \ p.support.toFinset) ∩ G.neighborFinset a).card := by
  classical
  let P := p.support.toFinset
  let A := G.neighborFinset a
  let B := G.neighborFinset b
  let D := B \ P
  let C := D ∩ A
  let X := (D.erase a) \ A
  let Q := P.filter (fun z => G.dist a z=2)
  have acol := protected_cross_positions p hp t longest ha hb ab
  rw [contact_card_neighbors p hp a,contact_card_neighbors p hp b] at acol
  change (A∩P).card+(B∩P).card ≤ Q.card+1 at acol
  have ain : a∈D := Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ab.symm,
    fun h => ha (List.mem_toFinset.mp h)⟩
  have inter : (D.erase a) ∩ A = C := by
    ext z
    simp only [C,Finset.mem_inter,Finset.mem_erase]
    constructor
    · rintro ⟨⟨_,hd⟩,hA⟩
      exact ⟨hd,hA⟩
    · rintro ⟨hd,hA⟩
      exact ⟨⟨fun eq => G.irrefl (eq ▸ (G.mem_neighborFinset a z).mp hA),hd⟩,hA⟩
  have part₁ := Finset.card_sdiff_add_card_inter B P
  have part₂ := Finset.card_erase_add_one ain
  have part₃ := Finset.card_sdiff_add_card_inter (D.erase a) A
  rw [inter] at part₃
  change X.card+C.card=(D.erase a).card at part₃
  have shell (z : V) (hz : z∈X) : G.dist a z=2 := by
    obtain ⟨hD,hA⟩ := Finset.mem_sdiff.mp hz
    obtain ⟨ne,hd⟩ := Finset.mem_erase.mp hD
    have hzB := (Finset.mem_sdiff.mp hd).1
    exact two_step_metric ne.symm (fun hadj => hA ((G.mem_neighborFinset a z).mpr hadj)) ab
      ((G.mem_neighborFinset b z).mp hzB).symm
  have dis : Disjoint Q X := Finset.disjoint_left.mpr (by
    intro z hQ hX
    have dm := (Finset.mem_erase.mp (Finset.mem_sdiff.mp hX).1).2
    exact (Finset.mem_sdiff.mp dm).2 (Finset.mem_filter.mp hQ).1)
  have incl : Q ∪ X ⊆ Finset.univ.filter (fun z => G.dist a z=2) := by
    intro z hz
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩
    rcases Finset.mem_union.mp hz with h | h
    · exact (Finset.mem_filter.mp h).2
    · exact shell z h
  have total := (Finset.card_le_card incl).trans quota
  rw [Finset.card_union_of_disjoint dis] at total
  change D.card+(B∩P).card=B.card at part₁
  change (A∩P).card+B.card ≤ k+2+C.card
  omega
theorem protected_cross_contact_degree (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k) :
    (G.neighborFinset a ∩ p.support.toFinset).card + G.degree b ≤
      k+1+(G.neighborFinset a \ p.support.toFinset).card := by
  classical
  let P := p.support.toFinset
  let A := G.neighborFinset a
  let B := G.neighborFinset b
  let C := (B \ P) ∩ A
  have bound := protected_exterior_contact_degree p hp t longest ha hb ab quota
  change (A∩P).card+G.degree b ≤ k+2+C.card at bound
  have absent : b∉C := by
    intro h
    have nb := (Finset.mem_sdiff.mp (Finset.mem_inter.mp h).1).1
    exact G.irrefl ((G.mem_neighborFinset _ _).mp nb)
  have share : insert b C ⊆ A \ P := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | h
    · exact Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ab,
        fun h => hb (List.mem_toFinset.mp h)⟩
    · obtain ⟨hD,hA⟩ := Finset.mem_inter.mp h
      exact Finset.mem_sdiff.mpr ⟨hA,(Finset.mem_sdiff.mp hD).2⟩
  have count := Finset.card_le_card share
  rw [Finset.card_insert_of_notMem absent] at count
  change (A∩P).card+G.degree b ≤ k+1+(A \ P).card
  omega
theorem protected_half_degree (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a b : V} (ha : a∉p.support) (hb : b∉p.support) (ab : G.Adj a b)
    {k : ℕ} (quota : (Finset.univ.filter (fun z => G.dist a z=2)).card ≤ k)
    (high : k ≤ G.degree b) :
    G.degree a ≤ 2*(G.neighborFinset a \ p.support.toFinset).card+1 := by
  have cross := protected_cross_contact_degree p hp t longest ha hb ab quota
  have parts := Finset.card_sdiff_add_card_inter (G.neighborFinset a) p.support.toFinset
  change (G.neighborFinset a).card ≤ 2*(G.neighborFinset a \ p.support.toFinset).card+1
  omega
omit [Fintype V] [DecidableRel G.Adj] in
theorem protected_single_shell (p : G.Walk x y) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    {a : V} (ha : a ∉ p.support) (touch : (contactPositions p a).Nonempty) :
    (contactPositions p a).card + 1 ≤
      (p.support.toFinset.filter (fun v => G.dist a v = 2)).card := by
  classical
  let A := contactPositions p a
  let m := A.max' touch
  have hm : m ∈ A := Finset.max'_mem _ _
  have internal (i : ℕ) (hi : i ∈ A) : 0 < i ∧ i+1 < p.support.length := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    exact protected_contact_internal p hp t longest ha ⟨i,ri⟩ (by simpa [get_at] using ci)
  have spaced (i j : ℕ) (hi : i ∈ A) (hj : j ∈ A) (lt : i < j) : i+2 ≤ j := by
    obtain ⟨ri,ci⟩ := (mem_contactPositions p a i).mp hi
    obtain ⟨rj,cj⟩ := (mem_contactPositions p a j).mp hj
    exact protected_contact_spacing p hp t longest ha ⟨i,ri⟩ ⟨j,rj⟩ lt
      (by simpa [get_at] using ci) (by simpa [get_at] using cj)
  let B := A.image (fun i => i-1)
  let W := insert (m+1) B
  have different (i : ℕ) : a ≠ p.getVert i := fun eq => ha (eq ▸ p.getVert_mem_support i)
  have ls := p.length_support
  have via (i j : ℕ) (hi : i < p.support.length) (hj : j ∈ A) (no : i ∉ A)
      (edge : G.Adj (p.getVert i) (p.getVert j)) : G.dist a (p.getVert i) = 2 := by
    have c := ((mem_contactPositions p a j).mp hj).2
    exact two_step_metric (different _) (fun h => no ((mem_contactPositions p a i).mpr ⟨hi,h.symm⟩)) c.symm edge
  have valid (i : ℕ) (hi : i ∈ W) : i < p.support.length ∧ G.dist a (p.getVert i) = 2 := by
    rcases mem_insert.mp hi with rfl|h
    · have ht := (internal m hm).2
      refine ⟨ht,via _ m ht hm (fun mem => ?_) ((p.adj_getVert_succ (i:=m) (by omega)).symm)⟩
      have := spaced m (m+1) hm mem (by omega)
      omega
    · obtain ⟨j,hj,rfl⟩ := mem_image.mp h
      obtain ⟨positive,back⟩ := internal j hj
      have lim : j-1 < p.support.length := by omega
      refine ⟨lim,via _ j lim hj (fun mem => ?_) ?_⟩
      · have := spaced (j-1) j mem hj (by omega)
        omega
      · have edge := p.adj_getVert_succ (i:=j-1) (by omega)
        rwa [show j-1+1=j by omega] at edge
  have maxoutside : m+1 ∉ B := by
    intro h
    obtain ⟨i,hi,eq⟩ := mem_image.mp h
    have lim : i ≤ m := Finset.le_max' _ _ hi
    omega
  have predinj : Set.InjOn (fun i : ℕ => i-1) (A : Set ℕ) := by
    intro i hi j hj eq
    have := (internal i hi).1
    have := (internal j hj).1
    change i-1=j-1 at eq
    omega
  have nodeinj : Set.InjOn p.getVert (W : Set ℕ) := by
    intro i hi j hj eq
    exact hp.getVert_injOn (by change i ≤ p.length; have := (valid i hi).1; omega)
      (by change j ≤ p.length; have := (valid j hj).1; omega) eq
  have sub : W.image p.getVert ⊆ p.support.toFinset.filter (fun v => G.dist a v = 2) := by
    intro v hv
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hv
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr (p.getVert_mem_support _),(valid i hi).2⟩
  have count := card_le_card sub
  rw [card_image_of_injOn nodeinj,show W = insert (m+1) B from rfl,card_insert_of_notMem maxoutside,
    show B = A.image (fun i => i-1) from rfl,card_image_of_injOn predinj] at count
  exact count
end Graph189ExteriorGap
end
section
open SimpleGraph Finset Graph189ExteriorDegreeCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
theorem protected_exterior_minimum (p : G.Walk a b) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (low : G.degree p.support[t.val] < G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (x : (p.support.toFinsetᶜ : Finset V)) :
    G.secondSmallestDegree / 2 ≤ (G.induce ((p.support.toFinsetᶜ : Finset V) : Set V)).degree x := by
  classical
  let P := p.support.toFinset
  let E := Pᶜ
  let k := G.secondSmallestDegree
  have quota (v : V) : (univ.filter (fun y => G.dist v y = 2)).card ≤ k := by
    let T := univ.filter (fun y => G.dist v y = 2)
    have miss : v ∉ T := by simp [T]
    have sub : insert v T ⊆ univ.filter (fun y => Even (G.dist v y)) := by
      intro y hy
      rcases mem_insert.mp hy with rfl | h
      · simp
      · exact mem_filter.mpr ⟨mem_univ _,by rw [(mem_filter.mp h).2]; decide⟩
    have h := card_le_card sub
    rw [card_insert_of_notMem miss] at h
    change T.card+1 ≤ G.distEven v at h
    have capv := cap v
    change G.distEven v ≤ k+1 at capv
    change T.card ≤ k
    omega
  have high {v : V} (out : v ∉ p.support) : k ≤ G.degree v := by
    have ne : v ≠ p.support[t.val] := fun h => out (h ▸ List.getElem_mem _)
    exact (degree_pair (G:=G) v _ ne).resolve_right (Nat.not_le.mpr low)
  have outside : x.val ∉ p.support := fun h => (mem_compl.mp x.property) (List.mem_toFinset.mpr h)
  have gram : ((G.neighborFinset x.val).filter (fun u => u ∈ (E : Set V))) = G.neighborFinset x.val \ P := by
    ext v
    simp [E]
  change k/2 ≤ (G.induce (E : Set V)).degree x
  rw [degree_induce_filter,gram]
  obtain ⟨y,hy⟩ : (G.neighborFinset x.val \ P).Nonempty := by
    apply Classical.byContradiction
    intro empty
    have sub : G.neighborFinset x.val ⊆ P := by
      intro v hv
      by_contra out
      exact empty ⟨v,mem_sdiff.mpr ⟨hv,out⟩⟩
    have eq : (contactPositions p x.val).card = G.degree x.val := by
      rw [contact_card_neighbors p hp]
      change (G.neighborFinset x.val ∩ P).card = G.degree x.val
      rw [inter_eq_left.mpr sub, G.card_neighborFinset_eq_degree]
    have hx := high outside
    have pos : (contactPositions p x.val).Nonempty := card_pos.mp (by change _ < k at low; omega)
    have shift := protected_single_shell p hp t longest outside pos
    have shell : P.filter (fun y => G.dist x.val y=2) ⊆ univ.filter (fun y => G.dist x.val y=2) :=
      filter_subset_filter _ (subset_univ _)
    have count := (card_le_card shell).trans (quota _)
    change (contactPositions p x.val).card + 1 ≤ (P.filter _).card at shift
    omega
  have outy : y ∉ p.support := fun h => (mem_sdiff.mp hy).2 (List.mem_toFinset.mpr h)
  have bound := protected_half_degree p hp t longest outside outy
    ((G.mem_neighborFinset _ _).mp (mem_sdiff.mp hy).1) (quota _) (high outy)
  have := high outside
  change G.degree x.val ≤ 2*(G.neighborFinset x.val \ P).card+1 at bound
  omega
theorem protected_exterior_hamilton_connected (p : G.Walk a b) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → p.support[t.val] ∈ r.support → r.length ≤ p.length)
    (low : G.degree p.support[t.val] < G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (room : (p.support.toFinsetᶜ : Finset V).card + 2 ≤ G.secondSmallestDegree)
    (x y : (p.support.toFinsetᶜ : Finset V)) (ne : x ≠ y) :
    ∃ q : (G.induce ((p.support.toFinsetᶜ : Finset V) : Set V)).Walk x y, q.IsHamiltonian := by
  classical
  let E := p.support.toFinsetᶜ
  let H := G.induce (E : Set V)
  apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) le_top _ (Graph189TerminalLeafClosure.complete_prescribed x y ne)
  intro i j _ _
  have hi := protected_exterior_minimum p hp t longest low cap i
  have hj := protected_exterior_minimum p hp t longest low cap j
  change G.secondSmallestDegree / 2 ≤ H.degree i at hi
  change G.secondSmallestDegree / 2 ≤ H.degree j at hj
  change E.card+2 ≤ _ at room
  change Fintype.card E+1 ≤ H.degree i + H.degree j
  rw [Fintype.card_coe]
  omega
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {x y : V}
omit [Fintype V] in
theorem vertex_positions_equiv (p : G.Walk x y) (M : Finset V) (onPath : ∀ z∈M, z∈p.support) :
    ∃ marks : Finset (Fin p.support.length), ∃ e : marks ≃ M,
      ∀ i : marks, p.support[i.val.val]=(e i).val := by
  classical
  let pos (u : M) : Fin p.support.length :=
    ⟨p.support.idxOf u.val,List.idxOf_lt_length_iff.mpr (onPath u.val u.property)⟩
  have eval (u : M) : p.support[(pos u).val] = u.val := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (onPath u.val u.property))
  have inj : Function.Injective pos := by
    intro a b h
    apply Subtype.ext
    calc
      a.val = p.support[(pos a).val] := (eval a).symm
      _ = p.support[(pos b).val] := by rw [h]
      _ = b.val := eval b
  let marks := M.attach.image pos
  let embed (u : M) : marks := ⟨pos u, Finset.mem_image.mpr ⟨u,Finset.mem_attach _ _,rfl⟩⟩
  have bij : Function.Bijective embed := by
    constructor
    · intro a b eq
      exact inj (congrArg Subtype.val eq)
    · intro i
      obtain ⟨u,hu,eq⟩ := Finset.mem_image.mp i.property
      exact ⟨u,Subtype.ext eq⟩
  let e := Equiv.ofBijective embed bij
  refine ⟨marks,e.symm,?_⟩
  intro i
  have posEq : pos (e.symm i)=i.val := congrArg Subtype.val (e.apply_symm_apply i)
  have value := eval (e.symm i)
  rwa [posEq] at value
end Graph189ExteriorGap
end
section
open Finset SimpleGraph
namespace Graph189DenseExteriorOrder
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj] {x y : V}
theorem neighbors_on_path (p : G.Walk x y) (W : Finset V)
    (boundary : ∀ w ∈ W, ∀ v, G.Adj w v → v ∉ W → v ∈ p.support)
    {w : V} (hw : w ∈ W) :
    G.degree w+1 ≤ W.card+((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w)).card := by
  classical
  let R := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] w)
  let P := R.image (fun i => p.support[i.val])
  have sub : insert w (G.neighborFinset w) ⊆ W ∪ P := by
    intro v hv
    rcases mem_insert.mp hv with rfl | h
    · exact mem_union_left _ hw
    have edge := (G.mem_neighborFinset _ _).mp h
    by_cases vw : v ∈ W
    · exact mem_union_left _ vw
    obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp (boundary w hw v edge vw)
    exact mem_union_right _ (mem_image.mpr ⟨⟨i,hi⟩,
      mem_filter.mpr ⟨mem_univ _,by simpa only [eq] using edge.symm⟩,eq⟩)
  have h := (card_le_card sub).trans (card_union_le W P)
  rw [card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree] at h
  exact h.trans (Nat.add_le_add_left card_image_le _)
end Graph189DenseExteriorOrder
end
section
open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
theorem protected_contact_witness (p : G.Walk a b) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {x y}, ∀ q : G.Walk x y, q.IsPath → p.support[t.val] ∈ q.support → q.length ≤ p.length)
    (low : G.degree p.support[t.val] < G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (omits : (p.support.toFinsetᶜ : Finset V).Nonempty)
    {s : ℕ} (s3 : 3 ≤ s) (small : 2*s ≤ G.secondSmallestDegree)
    (room : (p.support.toFinsetᶜ : Finset V).card+s ≤ G.secondSmallestDegree+1) :
    let m := (p.support.toFinsetᶜ : Finset V).card
    let u := G.secondSmallestDegree+1-m
    u ≤ m ∧ (u+1)*m+u ≤ Fintype.card V ∧
      ∀ v ∈ (p.support.toFinsetᶜ : Finset V), u ≤ ((univ : Finset (Fin p.support.length)).filter
        (fun i => G.Adj p.support[i.val] v)).card := by
  classical
  let E := p.support.toFinsetᶜ
  let m := E.card
  let k := G.secondSmallestDegree
  let u := k+1-m
  change m+s ≤ k+1 at room
  change 2*s ≤ k at small
  obtain ⟨v,hv⟩ := omits
  let w : E := ⟨v,hv⟩
  have half := protected_exterior_minimum p hp t longest low cap w
  have upper := (G.induce (E : Set V)).degree_lt_card_verts w
  change (G.induce (E : Set V)).degree w < Fintype.card E at upper
  rw [Fintype.card_coe] at upper
  change _ < m at upper
  change k/2 ≤ (G.induce (E : Set V)).degree w at half
  have enough : u ≤ m := by dsimp [u]; omega
  have su : s ≤ u := by dsimp [u]; omega
  have sm : s ≤ m := by omega
  have sum : m+u=k+1 := by dsimp [u]; omega
  have outside {v : V} (hv : v ∈ E) : v ∉ p.support :=
    fun h => (mem_compl.mp hv) (List.mem_toFinset.mpr h)
  have boundary (w : V) (_ : w ∈ E) (v : V) (_ : G.Adj w v) (hv : v ∉ E) : v ∈ p.support := by
    simpa [E] using hv
  have rows (v : V) (hv : v ∈ E) : u ≤ ((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] v)).card := by
    have ne : v ≠ p.support[t.val] := fun eq => outside hv (eq ▸ List.getElem_mem _)
    have high := (degree_pair (G:=G) v _ ne).resolve_right (not_le.mpr low)
    have d := Graph189DenseExteriorOrder.neighbors_on_path p E boundary hv
    change k ≤ G.degree v at high
    change G.degree v+1 ≤ m+_ at d
    omega
  have bound := protected_order_of_contacts p hp (List.getElem_mem (l:=p.support) t.isLt) longest E
    (by change 1 < m; omega) (fun _ hv => outside hv)
    (protected_exterior_hamilton_connected p hp t longest low cap (by change m+2 ≤ k; omega))
    (by omega : 0 < u) enough rows
  exact ⟨enough,bound,rows⟩
theorem protected_order_of_exterior_size (p : G.Walk a b) (hp : p.IsPath)
    (t : Fin p.support.length)
    (longest : ∀ {x y}, ∀ q : G.Walk x y, q.IsPath → p.support[t.val] ∈ q.support → q.length ≤ p.length)
    (low : G.degree p.support[t.val] < G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (omits : (p.support.toFinsetᶜ : Finset V).Nonempty)
    {s : ℕ} (s3 : 3 ≤ s) (small : 2*s ≤ G.secondSmallestDegree)
    (room : (p.support.toFinsetᶜ : Finset V).card+s ≤ G.secondSmallestDegree+1) :
    (s+1)*(G.secondSmallestDegree-s+2) ≤ Fintype.card V+1 := by
  let m := (p.support.toFinsetᶜ : Finset V).card
  let k := G.secondSmallestDegree
  let u := k+1-m
  obtain ⟨enough,bound,_⟩ := protected_contact_witness p hp t longest low cap omits s3 small room
  change m+s ≤ k+1 at room
  change 2*s ≤ k at small
  change u ≤ m at enough
  change (u+1)*m+u ≤ Fintype.card V at bound
  have su : s ≤ u := by dsimp [u]; omega
  have sm : s ≤ m := by omega
  have sum : m+u=k+1 := by dsimp [u]; omega
  change (s+1)*(k-s+2) ≤ Fintype.card V+1
  zify [show s ≤ k by omega] at bound sum ⊢
  have x : 0 ≤ (m:ℤ)-s := by omega
  have y : 0 ≤ (u:ℤ)-s := by omega
  nlinarith only [bound,mul_nonneg x y,sum,congrArg (fun i : ℤ => (s:ℤ)*i) sum]
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {x y : V}
private theorem singleton_gap (p : G.Walk x y) (hp : p.IsPath) {z : V}
    (outside : z ∉ p.support) {m : ℕ}
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support →
      r.support.length+m ≤ p.support.length+1)
    (A J B : List V) (split : p.support=A++J++B)
    (left : ∀ v∈A.getLast?, G.Adj v z) (right : ∀ v∈B.head?, G.Adj z v) :
    m ≤ J.length := by
  let q : G.Walk z z := Walk.nil
  have dis : List.Disjoint q.support p.support := by simpa [q,List.disjoint_left] using outside
  obtain ⟨a,b,r,hr,rs⟩ := splice_support p hp A J B split q (by simp [q]) dis left right
  have count := maximal r hr (by simp [rs,q])
  rw [rs,split] at count
  simp only [q,Walk.support_nil,List.length_append,List.length_singleton] at count
  omega
private theorem first_tail (p : G.Walk x y) (hp : p.IsPath)
    {m : ℕ} {z : V} (outside : z ∉ p.support)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support →
      r.support.length + m ≤ p.support.length+1)
    (i : Fin p.support.length)
    (contact : G.Adj z p.support[i.val]) : m ≤ i.val := by
  let L := p.support
  have head : (L.drop i.val).head? = some L[i.val] := by
    simp [List.head?_drop]
  have gap := singleton_gap p hp outside maximal [] (L.take i.val) (L.drop i.val)
    (by simp [L]) (by simp) (by
      intro z hz
      rw [head] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact)
  have small := List.length_take_le i.val L
  omega
private theorem last_tail (p : G.Walk x y) (hp : p.IsPath)
    {m : ℕ} {z : V} (outside : z ∉ p.support)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support →
      r.support.length + m ≤ p.support.length+1)
    (i : Fin p.support.length)
    (contact : G.Adj p.support[i.val] z) : i.val + 1 + m ≤ p.support.length := by
  let L := p.support
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have gap := singleton_gap p hp outside maximal (L.take (i.val+1)) (L.drop (i.val+1)) []
    (by simp [L]) (by
      intro z hz
      rw [last] at hz
      have eq : L[i.val] = z := by simpa using hz
      exact eq ▸ contact) (by simp)
  simp only [L,List.length_drop] at gap
  have hi := i.isLt
  omega
private theorem inner_gap (p : G.Walk x y) (hp : p.IsPath)
    {m : ℕ} {z : V} (outside : z ∉ p.support)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support →
      r.support.length + m ≤ p.support.length+1)
    (i j : Fin p.support.length) (hij : i < j)
    (left : G.Adj p.support[i.val] z) (right : G.Adj z p.support[j.val]) :
    i.val+1+m ≤ j.val := by
  let L := p.support
  let gap := j.val-(i.val+1)
  have ij : i.val+1+gap=j.val := by
    change i.val < j.val at hij
    dsimp [gap]
    omega
  have split : L = L.take (i.val+1) ++ (L.drop (i.val+1)).take gap ++ L.drop j.val := by
    rw [←List.take_add,ij,List.take_append_drop]
  have last : (L.take (i.val+1)).getLast? = some L[i.val] := by
    exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
      (l := L) (i := i.val) i.isLt)).trans List.getLast?_concat
  have head : (L.drop j.val).head? = some L[j.val] := by
    simp [List.head?_drop]
  have bound := singleton_gap p hp outside maximal _ _ _ split (by
    intro z hz
    rw [last] at hz
    have eq : L[i.val] = z := by simpa using hz
    exact eq ▸ left) (by
    intro z hz
    rw [head] at hz
    have eq : L[j.val] = z := by simpa using hz
    exact eq ▸ right)
  have small := List.length_take_le gap (L.drop (i.val+1))
  omega
variable [DecidableEq V] [Fintype V] [DecidableRel G.Adj]
theorem protected_exterior_size_upper (p : G.Walk x y) (hp : p.IsPath) {z : V}
    (outside : z ∉ p.support) (all : ∀ v, v ≠ z → v ∈ p.support)
    (pos : 0 < G.degree z) {a b : V} (Q : G.Walk a b) (hQ : Q.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support → r.length ≤ Q.length) :
    1+G.degree z+(G.degree z+1)*(Q.support.toFinsetᶜ : Finset V).card ≤ Fintype.card V := by
  classical
  let m := (Q.support.toFinsetᶜ : Finset V).card
  have size : p.support.length+1=Fintype.card V := by
    have h : insert z p.support.toFinset=univ := by
      ext v
      by_cases e : v=z
      · simp [e]
      · simp [all v e]
    have eq := congrArg Finset.card h
    rwa [card_insert_of_notMem (by simpa using outside),
      List.toFinset_card_of_nodup hp.support_nodup,card_univ] at eq
  have mx {u v} (r : G.Walk u v) (hr : r.IsPath) (contains : z∈r.support) :
      r.support.length + m ≤ p.support.length+1 := by
    have bound := maximal r hr contains
    have total := card_add_card_compl Q.support.toFinset
    rw [List.toFinset_card_of_nodup hQ.support_nodup] at total
    change Q.support.length+m=Fintype.card V at total
    have := Q.length_support
    have := r.length_support
    omega
  let N := G.neighborFinset z
  have onPath (v : V) (hv : v∈N) : v∈p.support :=
    all v ((G.mem_neighborFinset _ _).mp hv).ne.symm
  obtain ⟨marks,e,values⟩ := vertex_positions_equiv p N onPath
  have card : marks.card = G.degree z := by
    have eq : marks.card = N.card := by
      simpa only [Fintype.card_coe] using Fintype.card_congr e
    exact eq.trans (G.card_neighborFinset_eq_degree z)
  let j := marks.card-1
  have hj : marks.card = j+1 := by dsimp [j]; omega
  let iso := marks.orderIsoOfFin hj
  let M := marks.orderEmbOfFin hj
  have adj (i : Fin (j+1)) : G.Adj z p.support[(M i).val] := by
    change G.Adj z p.support[(iso i).val.val]
    rw [values (iso i)]
    exact (G.mem_neighborFinset _ _).mp (e (iso i)).property
  have fst := first_tail p hp outside mx (M 0) (adj _)
  have lst := last_tail p hp outside mx (M (Fin.last j)) (adj _).symm
  have spread (i : Fin j) : (M i.castSucc).val+1+m ≤ (M i.succ).val :=
    inner_gap p hp outside mx (M i.castSucc) (M i.succ) (M.strictMono i.castSucc_lt_succ)
      (adj _).symm (adj _)
  have lower (i : Fin (j+1)) : (i.val+1)*m+i.val ≤ (M i).val := by
    induction i using Fin.induction with
    | zero => simpa using fst
    | succ i ih =>
      have step := spread i
      simp only [Fin.val_castSucc,Fin.val_succ,Nat.succ_mul] at ih step ⊢
      omega
  have final := lower (Fin.last j)
  simp only [Fin.val_last] at final
  change 1+G.degree z+(G.degree z+1)*m ≤ _
  rw [←card,hj]
  rw [Nat.succ_mul]
  omega
omit [DecidableRel G.Adj] [DecidableEq V] in
theorem exists_longest_through (G : SimpleGraph V) (z : V) :
    ∃ a b, ∃ Q : G.Walk a b, Q.IsPath ∧ ∃ t : Fin Q.support.length,
      Q.support[t.val] = z ∧
        ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support → r.length ≤ Q.length := by
  classical
  let Good (n : ℕ) := ∃ a b, ∃ Q : G.Walk a b, Q.IsPath ∧ z ∈ Q.support ∧ Q.length=n
  have base : Good 0 := ⟨z,z,.nil,by simp,by simp,rfl⟩
  obtain ⟨a,b,Q,hQ,mem,sz⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) base
  obtain ⟨i,hi,eq⟩ := List.mem_iff_getElem.mp mem
  refine ⟨a,b,Q,hQ,⟨i,hi⟩,eq,?_⟩
  intro u v r hr member
  rw [sz]
  have len := r.length_support
  have bound := hr.support_nodup.length_le_card
  exact Nat.le_findGreatest (by omega) (show Good r.length from ⟨u,v,r,hr,member,rfl⟩)
theorem protected_size_of_traceable_deletion (z : V) (pos : 0 < G.degree z)
    {x y : {v : V | v ≠ z}} (p : (G.induce {v : V | v ≠ z}).Walk x y) (hp : p.IsHamiltonian)
    {a b : V} (Q : G.Walk a b) (hQ : Q.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support → r.length ≤ Q.length) :
    1+G.degree z+(G.degree z+1)*(Q.support.toFinsetᶜ : Finset V).card ≤ Fintype.card V := by
  let e := Embedding.induce (G:=G) {v : V | v ≠ z}
  apply protected_exterior_size_upper (p.map e.toHom) (hp.isPath.map e.injective) _ _ pos Q hQ maximal
  · rw [Walk.support_map]
    intro h
    obtain ⟨v,_,eq⟩ := List.mem_map.mp h
    exact v.property eq
  · intro v ne
    rw [Walk.support_map]
    exact List.mem_map.mpr ⟨⟨v,ne⟩,hp.mem_support _,rfl⟩
theorem protected_size_under_base_failure (z : V) (pos : 0 < G.degree z)
    {x y : {v : V | v ≠ z}} (p : (G.induce {v : V | v ≠ z}).Walk x y) (hp : p.IsHamiltonian)
    {a b : V} (Q : G.Walk a b) (hQ : Q.IsPath)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → z ∈ r.support → r.length ≤ Q.length)
    {s k : ℕ} (sk : s ≤ k) (sd : s ≤ G.degree z)
    (failure : Fintype.card V+1 < (s+1)*(k-s+2)) :
    (Q.support.toFinsetᶜ : Finset V).card+s ≤ k := by
  let m := (Q.support.toFinsetᶜ : Finset V).card
  have lower := protected_size_of_traceable_deletion z pos p hp Q hQ maximal
  change 1+G.degree z+(G.degree z+1)*m ≤ _ at lower
  change m+s ≤ k
  by_contra! small
  have cmp := Nat.mul_le_mul (Nat.add_le_add_right sd 1)
    (show k-s+2 ≤ m+1 by omega)
  rw [show (G.degree z+1)*(m+1) = (G.degree z+1)*m+(G.degree z+1) from Nat.mul_succ _ _] at cmp
  omega
end Graph189ExteriorGap
end
section
open Finset SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
theorem order_of_traceable_low_deletion (z : V)
    (low : G.degree z < G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (nontrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    {x y : {v : V | v ≠ z}} (p : (G.induce {v : V | v ≠ z}).Walk x y) (hp : p.IsHamiltonian)
    {s : ℕ} (s3 : 3 ≤ s) (small : 2*s ≤ G.secondSmallestDegree) (sd : s ≤ G.degree z) :
    (s+1)*(G.secondSmallestDegree-s+2) ≤ Fintype.card V+1 := by
  classical
  by_contra! fail
  obtain ⟨a,b,Q,hQ,t,eq,maximal⟩ := exists_longest_through G z
  have size := protected_size_under_base_failure z (by omega) p hp Q hQ maximal
    (by omega : s ≤ G.secondSmallestDegree) sd fail
  have out : (Q.support.toFinsetᶜ : Finset V).Nonempty := by
    by_contra empty
    apply nontrace
    refine ⟨a,b,Q,hQ.isHamiltonian_of_mem (fun v => ?_)⟩
    by_contra absent
    exact empty ⟨v,by simpa using absent⟩
  have bound := protected_order_of_exterior_size Q hQ t (fun q hq h => maximal q hq (eq ▸ h))
    (eq ▸ low) cap out s3 small (by omega)
  omega
end Graph189ExteriorGap
end
section
open SimpleGraph
namespace Graph189ExteriorDegreeCycle
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
theorem low_of_traceable_minimum_deletion (hk : 5 ≤ G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (nontrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian) (z : V)
    (minimum : G.degree z=G.minDegree) {x y : {v : V | v ≠ z}}
    (p : (G.induce {v : V | v ≠ z}).Walk x y) (hp : p.IsHamiltonian) :
    G.degree z < G.secondSmallestDegree := by
  classical
  by_contra! high
  have all (v : V) : G.secondSmallestDegree < 2*G.degree v := by
    have h := G.minDegree_le_degree v
    rw [←minimum] at h
    omega
  let inc := (Embedding.induce (G:=G) {v : V | v ≠ z}).toHom
  have gap := high_min_all_paths_gap nontrace hk cap all _ _ (p.map inc) (hp.isPath.map Subtype.val_injective)
  rw [Walk.support_map,List.length_map,hp.length_support] at gap
  have one : Fintype.card {v : V | v ≠ z}=Fintype.card V-1 := by
    change Fintype.card {v : V // ¬ v=z} = _
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq]
  rw [one] at gap
  omega
end Graph189ExteriorDegreeCycle
end
section
open SimpleGraph Finset
namespace Graph189CutSides
variable {V : Type*} [Fintype V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem connectivity_le_degree (z : V) : G.vertexConnectivity ≤ G.degree z := by
  classical
  let S := G.neighborFinset z
  have sz : S.card=G.degree z := G.card_neighborFinset_eq_degree z
  have convention : G.vertexConnectivity ≤ Fintype.card V-1 := by
    unfold vertexConnectivity
    rw [if_neg (not_le.mpr (Fintype.one_lt_card (α:=V)))]
    exact Nat.sInf_le ⟨univ.erase z,by simp,Or.inr (by simp)⟩
  by_contra! fail
  have conn := connected_after_smaller_deletion (G:=G) S (sz ▸ fail)
  let W := {v : V | v ∉ S}
  let z' : W := ⟨z, show z ∉ G.neighborFinset z by simp⟩
  have card : 1 < Fintype.card W := by
    have same : W = ((Sᶜ : Finset V) : Set V) := by ext v; simp [W]
    rw [Fintype.card_congr (Equiv.setCongr same)]
    change 1 < Fintype.card (Sᶜ : Finset V)
    rw [Fintype.card_coe,Finset.card_compl]
    omega
  let _ : Nontrivial W := Fintype.one_lt_card_iff_nontrivial.mp card
  obtain ⟨w,edge⟩ := conn.preconnected.exists_adj_of_nontrivial z'
  exact w.property ((G.mem_neighborFinset z w.val).mpr edge)
end Graph189CutSides
end
section
open SimpleGraph Finset Graph189UniversalCycle
namespace Graph189RotationLinked
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
theorem order_of_core {l d : ℕ} (three : 3 ≤ l) (conn : l ≤ G.vertexConnectivity) (min : l ≤ G.minDegree)
    {a : V} (C : G.Walk a a) (hC : C.IsCycle)
    (longest : ∀ b (q : G.Walk b b), q.IsCycle → q.length ≤ C.length)
    (core : Graph189ExteriorCore.Core (G.induce {v : V | v∉C.support}) d) (enough : l ≤ d) :
    (l+1)*(G.minDegree-l+2)-1 ≤ Fintype.card V := by
  classical
  have linked := of_minimum (G:=core.graph) core.root three (fun w => enough.trans (core.degree w))
  exact OMA.BondyK.graph189_order_of_linked (by omega) min (fun S h =>
    Graph189CutSides.connected_after_smaller_deletion S (h.trans_le conn)) C hC longest
    (Graph189LinkedExterior.map core.hom core.injective linked)
theorem minimum_order (w : V) (minw : G.degree w=G.minDegree)
    (notTrace : ¬∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    (notH : ¬∃ a b, ∃ p : (G.induce {x : V | x≠w}).Walk a b, p.IsHamiltonian)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    {l : ℕ} (three : 3 ≤ l) (conn : l≤(completeAt G w).vertexConnectivity)
    (enough : 2*l+1 ≤ G.secondSmallestDegree) :
    (l+1)*(G.secondSmallestDegree-l+2)-1 ≤ Fintype.card V := by
  classical
  let K := completeAt G w
  have mindeg := secondDegree_le_completeAt_minDegree (G:=G) w minw
  change G.secondSmallestDegree ≤ K.minDegree at mindeg
  have two (v : V) : 2 ≤ K.degree v := by have := K.minDegree_le_degree v; omega
  obtain ⟨a,R,hR,_⟩ := Graph189ExteriorDegreeCycle.cycle_of_degree (G:=K) w (d:=2) (by decide) two
  obtain ⟨a,C,hC,mx⟩ := Graph189ExteriorDegreeCycle.exists_longest_cycle K ⟨a,R,hR⟩
  obtain ⟨core⟩ := Graph189ExteriorDegreeCycle.minimum_completion_exterior_core w minw C hC mx notTrace notH cap (by omega)
  have lower := order_of_core (G:=K) three conn (by omega) C hC mx core (by omega)
  have cmp := Nat.mul_le_mul_left (l+1) (show G.secondSmallestDegree-l+2 ≤ K.minDegree-l+2 by omega)
  omega
theorem base_order (notTrace : ¬∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    {l : ℕ} (three : 3 ≤ l) (conn : l ≤ G.vertexConnectivity)
    (enough : 2*l+1 ≤ G.secondSmallestDegree) :
    (l+1)*(G.secondSmallestDegree-l+2) ≤ Fintype.card V+1 := by
  classical
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  by_cases deletion : ∃ u v, ∃ p : (G.induce {v : V | v≠z}).Walk u v, p.IsHamiltonian
  · obtain ⟨u,v,p,hp⟩ := deletion
    have low := Graph189ExteriorDegreeCycle.low_of_traceable_minimum_deletion (by omega) cap notTrace z hz.symm p hp
    exact Graph189ExteriorGap.order_of_traceable_low_deletion z low cap notTrace p hp three
      (by omega) (conn.trans (Graph189CutSides.connectivity_le_degree z))
  have order := minimum_order z hz.symm notTrace deletion cap three (conn.trans (completeAt_connectivity z)) enough
  omega
end Graph189RotationLinked
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {u v : V}
theorem order_of_three_selected (p : G.Walk u v) (hp : p.IsPath) (t : Fin p.support.length)
    (maximal : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → p.support[t.val]∈q.support → q.length ≤ p.length)
    (E W : Finset V) (outside : ∀ a∈E, a∉p.support)
    (many : 3 ≤ W.card)
    (contacts : ∀ a∈W, 3 ≤ ((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] a)).card)
    (paths : ∀ a b : W, a≠b → ExteriorRoute p a.val b.val E.card) :
    4*E.card+3 ≤ Fintype.card V := by
  classical
  obtain ⟨M,sz,f,attached⟩ := Graph189ExteriorAttachment.marks_of_many_neighbors p W 3 many contacts
  let A := M.orderEmbOfFin (show M.card=2+1 from sz)
  let B := M.orderIsoOfFin sz
  let T (i : Fin 3) := f (B i)
  have inj : Function.Injective T := f.injective.comp B.injective
  have touch (i : Fin 3) : G.Adj p.support[(A i).val] (T i).val := attached (B i)
  have inner (i : Fin 2) : ExteriorRoute p (T i.castSucc).val (T i.succ).val E.card :=
    paths _ _ (inj.ne (ne_of_lt i.castSucc_lt_succ))
  have before := paths (T 1) (T 0) (inj.ne (by decide))
  have after := paths (T (Fin.last 2)) (T 0) (inj.ne (by decide))
  have bound := protected_matched_route_order p hp t maximal A (fun i => (T i).val) touch inner
    ⟨_,before⟩ ⟨_,after⟩
  have total := card_outside_add_path p hp E outside
  change 3*(E.card+1) ≤ p.support.length at bound
  omega
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189TerminalLeafClosure
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem endpoint_degree_gain (G : SimpleGraph V) [DecidableRel G.Adj] (u v a : V)
    (endpoint : a=u ∨ a=v) :
    G.degree a+1 ≤ (terminalLeaves G u v).degree (.inl a) := by
  classical
  obtain ⟨l,attached⟩ : ∃ l : Bool, (terminalLeaves G u v).Adj (.inl a) (.inr l) := by
    rcases endpoint with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  let core := (G.neighborFinset a).image (Sum.inl : V → V⊕Bool)
  have absent : Sum.inr l∉core := by simp [core]
  have incl : insert (.inr l) core ⊆ (terminalLeaves G u v).neighborFinset (.inl a) := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hc
    · exact ((terminalLeaves G u v).mem_neighborFinset _ _).mpr attached
    · obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hc
      simp only [SimpleGraph.mem_neighborFinset] at hb ⊢
      exact hb
  have count := Finset.card_le_card incl
  rw [Finset.card_insert_of_notMem absent,show core.card=G.degree a from
    Finset.card_image_of_injective _ (fun _ _ h => Sum.inl.inj h)] at count
  exact count
theorem prescribed_of_incident_edge {G : SimpleGraph V} [DecidableRel G.Adj] {u v a b : V}
    (distinct : a≠b) (missing : ¬G.Adj a b)
    (incident : (a=u ∨ a=v) ∨ (b=u ∨ b=v))
    (degree : Fintype.card V ≤ G.degree a+G.degree b)
    (path : ∃ p : (G⊔edge a b).Walk u v, p.IsHamiltonian) :
    ∃ p : G.Walk u v, p.IsHamiltonian := by
  obtain ⟨p,hp⟩ := path
  have aug := leaf_traceable_of_prescribed hp
  rw [terminalLeaves_sup_edge] at aug
  apply prescribed_of_leaf_traceable
  apply Graph189.traceable_of_sup_edge (G := terminalLeaves G u v) (x := .inl a) (y := .inl b)
  · exact fun h => distinct (Sum.inl.inj h)
  · exact missing
  · have ha := core_degree_le G u v a
    have hb := core_degree_le G u v b
    simp only [Fintype.card_sum,Fintype.card_bool]
    rcases incident with atA | atB
    · have := endpoint_degree_gain G u v a atA
      omega
    · have := endpoint_degree_gain G u v b atB
      omega
  · exact aug
end Graph189TerminalLeafClosure
end
section
open SimpleGraph Finset
namespace Graph189TerminalLeafClosure
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
theorem prescribed_of_simplicial (x y : V) (ne : x≠y)
    (half : ∀ v, Fintype.card V ≤ 2*G.degree v)
    (clique : ∀ a b, G.Adj x a → G.Adj x b → a≠b → G.Adj a b) :
    ∃ p : G.Walk x y, p.IsHamiltonian := by
  classical
  suffices all : ∀ J : SimpleGraph V, G ≤ J → ∃ p : J.Walk x y, p.IsHamiltonian by
    exact all G le_rfl
  intro J
  induction J using WellFoundedGT.induction with
  | ind J ih =>
    intro incl
    by_cases universal : ∀ a, x≠a → J.Adj x a
    · apply prescribed_of_supergraph (H:=⊤) le_top _ (complete_prescribed x y ne)
      intro a b hab missing
      have ax : x≠a := by rintro rfl; exact missing (universal b hab.ne)
      have bx : x≠b := by rintro rfl; exact missing (universal a hab.ne.symm).symm
      have gain (v : V) (dv : x≠v) (old : ¬G.Adj x v) : G.degree v+1 ≤ J.degree v := by
        have sub : insert x (G.neighborFinset v) ⊆ J.neighborFinset v := by
          intro z hz
          rcases mem_insert.mp hz with rfl|h
          · exact (J.mem_neighborFinset _ _).mpr (universal v dv).symm
          · exact (J.mem_neighborFinset _ _).mpr (incl ((G.mem_neighborFinset _ _).mp h))
        have count := card_le_card sub
        rw [card_insert_of_notMem (fun h => old ((G.mem_neighborFinset _ _).mp h).symm)] at count
        exact count
      have da := degree_le_of_le (v:=a) incl
      have db := degree_le_of_le (v:=b) incl
      have ha := half a
      have hb := half b
      by_cases old : G.Adj x a
      · have lost : ¬G.Adj x b := fun h => missing (incl (clique a b old h hab.ne))
        have := gain b bx lost
        omega
      · have := gain a ax old
        omega
    · push_neg at universal
      obtain ⟨a,ax,missing⟩ := universal
      have strict : J < J⊔edge x a := by
        apply lt_of_le_of_ne le_sup_left
        intro same
        have added : (J⊔edge x a).Adj x a :=
          Or.inr ((edge_adj _ _ _ _).mpr ⟨Or.inl ⟨rfl,rfl⟩,ax⟩)
        exact missing (same.symm ▸ added)
      have dx := degree_le_of_le (v:=x) incl
      have da := degree_le_of_le (v:=a) incl
      have hx := half x
      have ha := half a
      exact prescribed_of_incident_edge ax missing (Or.inl (Or.inl rfl)) (by omega)
        (ih _ strict (incl.trans le_sup_left))
theorem prescribed_of_two_exceptions {d : ℕ} (order : Fintype.card V=2*d) (three : 3 ≤ d)
    (half : ∀ v, d ≤ G.degree v) (L : Finset V) (few : L.card≤2)
    (better : ∀ v∉L, d < G.degree v) (x y : V) (ne : x≠y) :
    ∃ p : G.Walk x y, p.IsHamiltonian := by
  classical
  let K : SimpleGraph V := {
    Adj a b := G.Adj a b ∨ (a≠b ∧ (a∉L ∨ b∉L))
    symm := ⟨fun _ _ h => h.elim (fun e => Or.inl e.symm)
      (fun h => Or.inr ⟨h.1.symm,h.2.symm⟩)⟩
    loopless := ⟨fun a h => h.elim (G.irrefl) (fun h => h.1 rfl)⟩ }
  have incl : G ≤ K := fun _ _ h => Or.inl h
  apply prescribed_of_supergraph (H:=K) incl
  · intro a b h missing
    obtain ⟨_,ha|hb⟩ := h.resolve_left missing
    · have := better a ha
      have := half b
      omega
    · have := better b hb
      have := half a
      omega
  apply prescribed_of_supergraph (H:=⊤) le_top _ (complete_prescribed x y ne)
  intro a b hab missing
  have inA : a∈L := by by_contra h; exact missing (Or.inr ⟨hab.ne,Or.inl h⟩)
  have inB : b∈L := by by_contra h; exact missing (Or.inr ⟨hab.ne,Or.inr h⟩)
  have near (v : V) (inside : v∈L) : (Lᶜ : Finset V).card ≤ K.degree v := by
    apply card_le_card
    intro z hz
    have out := mem_compl.mp hz
    exact (K.mem_neighborFinset _ _).mpr (Or.inr ⟨fun h => out (h ▸ inside),Or.inr out⟩)
  have x1 := near a inA
  have x2 := near b inB
  rw [card_compl] at x1 x2
  omega
end Graph189TerminalLeafClosure
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {u v : V}
theorem adjacent_of_odd_equality (p : G.Walk u v) (hp : p.IsPath) (t : Fin p.support.length)
    (longest : ∀ {i j}, ∀ q : G.Walk i j, q.IsPath → p.support[t.val]∈q.support → q.length ≤ p.length)
    {a b c : V} (ha : a∉p.support) (hb : b∉p.support) (hc : c∉p.support)
    (ab : G.Adj a b) (ac : G.Adj a c) (diff : b≠c) {d : ℕ}
    (degreeA : 2*d+1 ≤ G.degree a) (degreeB : 2*d+1 ≤ G.degree b)
    (size : (G.neighborFinset a \ p.support.toFinset).card=d)
    (quota : (univ.filter (fun w => G.dist a w=2)).card≤2*d+1) : G.Adj b c := by
  classical
  let P := p.support.toFinset
  let A := G.neighborFinset a \ P
  let C := (G.neighborFinset b \ P) ∩ G.neighborFinset a
  have bound := protected_exterior_contact_degree p hp t longest ha hb ab quota
  change (G.neighborFinset a ∩ P).card + G.degree b ≤ 2*d+1+2+C.card at bound
  have parts := card_sdiff_add_card_inter (G.neighborFinset a) P
  rw [G.card_neighborFinset_eq_degree] at parts
  change A.card+(G.neighborFinset a ∩ P).card=G.degree a at parts
  change A.card=d at size
  have memB : b∈A := mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ab,fun h => hb (List.mem_toFinset.mp h)⟩
  have memC : c∈A := mem_sdiff.mpr ⟨(G.mem_neighborFinset _ _).mpr ac,fun h => hc (List.mem_toFinset.mp h)⟩
  have incl : C ⊆ A.erase b := by
    intro z hz
    obtain ⟨hzB,hzA⟩ := mem_inter.mp hz
    obtain ⟨bz,off⟩ := mem_sdiff.mp hzB
    exact mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp bz).ne.symm,mem_sdiff.mpr ⟨hzA,off⟩⟩
  have erased := card_erase_add_one memB
  have eq : C=A.erase b := eq_of_subset_of_card_le incl (by omega)
  have common : c∈C := eq ▸ mem_erase.mpr ⟨diff.symm,memC⟩
  exact (G.mem_neighborFinset _ _).mp (mem_sdiff.mp (mem_inter.mp common).1).1
end Graph189ExteriorGap
end
section
open SimpleGraph Finset Graph189ExteriorDegreeCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {u v : V}
theorem extreme_two_routes (p : G.Walk u v) (hp : p.IsPath) (t : Fin p.support.length)
    (mx : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → p.support[t.val]∈q.support → q.length ≤ p.length)
    (low : G.degree p.support[t.val] < G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (large : 7 ≤ G.secondSmallestDegree) (order : Fintype.card V ≤ 3*G.secondSmallestDegree+1)
    (size : (p.support.toFinsetᶜ : Finset V).card+1=G.secondSmallestDegree) :
    let E := (p.support.toFinsetᶜ : Finset V)
    ∀ x y : E, x≠y → ∃ q : (G.induce (E : Set V)).Walk x y, q.IsHamiltonian := by
  classical
  let P := p.support.toFinset
  let E := (Pᶜ : Finset V)
  let F := G.induce (E : Set V)
  let k := G.secondSmallestDegree
  let d := k/2
  change E.card+1=k at size
  change 7 ≤ k at large
  change Fintype.card V ≤ 3*k+1 at order
  change ∀ x y : E, x≠y → ∃ q : F.Walk x y, q.IsHamiltonian
  have half (a : E) : d ≤ F.degree a := protected_exterior_minimum p hp t mx low cap a
  have nE : Fintype.card E=E.card := Fintype.card_coe E
  by_cases enough : E.card+1 ≤ 2*d
  · intro x y ne
    apply Graph189TerminalLeafClosure.prescribed_of_supergraph (H:=⊤) le_top _ (Graph189TerminalLeafClosure.complete_prescribed x y ne)
    intro a b _ _
    have h := half a
    have h' := half b
    change Fintype.card E+1 ≤ F.degree a+F.degree b
    omega
  have odd : k=2*d+1 := by dsimp [d] at *; omega
  have count : Fintype.card E=2*d := by omega
  have out (a : V) (h : a∈E) : a∉p.support := by simpa [E,P] using h
  have high (a : V) (h : a∈E) : k ≤ G.degree a :=
    (degree_pair (G:=G) a p.support[t.val] (fun e => out a h (e ▸ List.getElem_mem _))).resolve_right (not_le.mpr low)
  have internal (a : E) : F.degree a=(G.neighborFinset a.val \ P).card := by
    rw [show F.degree a = _ from degree_induce_filter (E : Set V) a]
    congr 1
    ext b
    simp [E]
  let W := E.filter (fun a => (G.neighborFinset a \ P).card=d)
  let incl : W ↪ E := ⟨fun a => ⟨a.val,(mem_filter.mp a.property).1⟩,
    fun a b h => Subtype.ext (congrArg (fun i : E => i.val) h)⟩
  let L : Finset E := univ.map incl
  by_cases many : 3 ≤ W.card
  · exfalso
    have rows (a : V) (h : a∈W) : 3 ≤ ((univ : Finset (Fin p.support.length)).filter
        (fun i => G.Adj p.support[i.val] a)).card := by
      let A := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] a)
      have sub : G.neighborFinset a ∩ P ⊆ A.image (fun i => p.support[i.val]) := by
        intro b hb
        obtain ⟨ab,mem⟩ := mem_inter.mp hb
        obtain ⟨j,hj,val⟩ := List.mem_iff_getElem.mp (List.mem_toFinset.mp mem)
        exact mem_image.mpr ⟨⟨j,hj⟩,mem_filter.mpr ⟨mem_univ _,by simpa [val] using ((G.mem_neighborFinset _ _).mp ab).symm⟩,val⟩
      have enough := (card_le_card sub).trans card_image_le
      have degree := high a (mem_filter.mp h).1
      have eq := (mem_filter.mp h).2
      have parts := card_sdiff_add_card_inter (G.neighborFinset a) P
      rw [G.card_neighborFinset_eq_degree] at parts
      change 3 ≤ A.card
      omega
    have route (a b : W) (diff : a≠b) : ExteriorRoute p a.val b.val E.card := by
      have clique (c e : E) (ac : F.Adj (incl a) c) (ae : F.Adj (incl a) e) (ne : c≠e) : F.Adj c e := by
        have exactQ : (univ.filter (fun w => G.dist a.val w=2)).card ≤ 2*d+1 := by
          let T := univ.filter (fun w => G.dist a.val w=2)
          have short : a.val ∉ T := by simp [T]
          have sub : insert a.val T ⊆ univ.filter (fun w => Even (G.dist a.val w)) := by
            intro w hw
            rcases mem_insert.mp hw with rfl | h
            · simp
            · exact mem_filter.mpr ⟨mem_univ _,by rw [(mem_filter.mp h).2]; decide⟩
          have h := (card_le_card sub).trans (cap a.val)
          rw [card_insert_of_notMem short] at h
          change T.card+1 ≤ k+1 at h
          change T.card ≤ 2*d+1
          omega
        exact adjacent_of_odd_equality p hp t mx (out _ (incl a).property) (out _ c.property) (out _ e.property)
          ac ae (fun eq => ne (Subtype.ext eq)) (odd ▸ high _ (incl a).property) (odd ▸ high _ c.property)
          (mem_filter.mp a.property).2 exactQ
      obtain ⟨q,hq⟩ := Graph189TerminalLeafClosure.prescribed_of_simplicial (G:=F) (incl a) (incl b)
        (incl.injective.ne diff) (fun v => by
          change Fintype.card E ≤ 2*F.degree v
          rw [count]
          exact Nat.mul_le_mul_left 2 (half v)) clique
      exact route_of_induced_hamilton p E out hq
    have bound := order_of_three_selected p hp t mx E W out many rows route
    omega
  · have few : L.card≤2 := by simp [L]; omega
    have better (a : E) (notin : a∉L) : d < F.degree a := by
      have h := half a
      by_contra! no
      apply notin
      have eq := internal a
      let v : W := ⟨a.val,mem_filter.mpr ⟨a.property,by omega⟩⟩
      exact mem_map.mpr ⟨v,mem_univ _,Subtype.ext rfl⟩
    exact Graph189TerminalLeafClosure.prescribed_of_two_exceptions count (by omega) half L few better
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189FourTerminalGap
open Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {a b : V}
theorem impossible_of_exact_length (p : G.Walk a b) (hp : p.IsPath) {x : V} (outside : x ∉ p.support)
    {i j lo hi m : ℕ} (left : 0 < i) (spaced : i+2 ≤ j) (right : j+1 < p.support.length)
    (marks : contactPositions p x = {i,j})
    (bound : hi ≤ p.support.length) (size : lo+m=hi)
    (unmarked : ∀ h ∈ Ico lo hi, h ≠ i ∧ h ≠ j)
    (via : ∀ h ∈ Ico lo hi, ∃ w, G.Adj x w ∧ G.Adj (p.getVert h) w)
    (quota : (univ.filter (fun y => G.dist x y=2)).card ≤ m+1) : False := by
  classical
  let J := Ico lo hi
  let W : Finset ℕ := {i-1,i+1,j-1,j+1}
  have skipI : ¬(lo ≤ i ∧ i < hi) := fun h => (unmarked i (mem_Ico.mpr h)).1 rfl
  have skipJ : ¬(lo ≤ j ∧ j < hi) := fun h => (unmarked j (mem_Ico.mpr h)).2 rfl
  have pair : ∃ u ∈ W, ∃ v ∈ W, u≠v ∧ u∉J ∧ v∉J := by
    by_cases before : hi ≤ i
    · refine ⟨j-1,by simp [W],j+1,by simp [W],by omega,?_,?_⟩ <;> simp [J] <;> omega
    by_cases after : j < lo
    · refine ⟨i-1,by simp [W],i+1,by simp [W],by omega,?_,?_⟩ <;> simp [J] <;> omega
    refine ⟨i-1,by simp [W],j+1,by simp [W],by omega,?_,?_⟩ <;> simp [J] <;> omega
  obtain ⟨u,hu,v,hv,ne,uout,vout⟩ := pair
  have mark {h : ℕ} (m : h=i ∨ h=j) : G.Adj x (p.getVert h) := by
    have hm : h ∈ contactPositions p x := by simpa [marks] using m
    exact ((mem_contactPositions p x h).mp hm).2.symm
  have charge (h : ℕ) (hh : h < p.support.length) (missing : h≠i ∧ h≠j)
      (link : ∃ w, G.Adj x w ∧ G.Adj (p.getVert h) w) : G.dist x (p.getVert h)=2 := by
    obtain ⟨w,hx,hw⟩ := link
    have different : x ≠ p.getVert h := fun eq => outside (eq ▸ p.getVert_mem_support h)
    apply two_step_metric different _ hx hw
    intro adj
    have hm := (mem_contactPositions p x h).mpr ⟨hh,adj.symm⟩
    rw [marks] at hm
    simp only [mem_insert,mem_singleton,missing.1,missing.2,or_self] at hm
  have shifts (h : ℕ) (hh : h∈W) : h < p.support.length ∧ G.dist x (p.getVert h)=2 := by
    have len := p.length_support
    have before (t : ℕ) (pos : 0 < t) (range : t < p.support.length) (hit : t=i ∨ t=j)
        (miss : t-1≠i ∧ t-1≠j) : G.dist x (p.getVert (t-1))=2 := by
      have step := p.adj_getVert_succ (i:=t-1) (by omega)
      rw [show t-1+1=t by omega] at step
      exact charge _ (by omega) miss ⟨_,mark hit,step⟩
    have after (t : ℕ) (range : t+1 < p.support.length) (hit : t=i ∨ t=j)
        (miss : t+1≠i ∧ t+1≠j) : G.dist x (p.getVert (t+1))=2 :=
      charge _ range miss ⟨_,mark hit,(p.adj_getVert_succ (i:=t) (by omega)).symm⟩
    simp only [W,mem_insert,mem_singleton] at hh
    rcases hh with rfl|rfl|rfl|rfl
    · exact ⟨by omega,before i left (by omega) (Or.inl rfl) (by omega)⟩
    · exact ⟨by omega,after i (by omega) (Or.inl rfl) (by omega)⟩
    · exact ⟨by omega,before j (by omega) (by omega) (Or.inr rfl) (by omega)⟩
    · exact ⟨right,after j right (Or.inr rfl) (by omega)⟩
  let T := insert u (insert v J)
  have good (h : ℕ) (hh : h ∈ T) : h < p.support.length ∧ G.dist x (p.getVert h)=2 := by
    rcases mem_insert.mp hh with rfl | hrest
    · exact shifts _ hu
    rcases mem_insert.mp hrest with rfl | member
    · exact shifts _ hv
    have r := (mem_Ico.mp member).2.trans_le bound
    exact ⟨r,charge _ r (unmarked _ member) (via _ member)⟩
  have count : T.card=m+2 := by
    have jcard : J.card=hi-lo := Nat.card_Ico _ _
    rw [show T=insert u (insert v J) from rfl,card_insert_of_notMem (by simpa [ne] using uout),
      card_insert_of_notMem vout,jcard]
    omega
  have inj : Set.InjOn p.getVert (T : Set ℕ) := by
    intro h hh e he eq
    have := (good _ hh).1
    have := (good _ he).1
    have := p.length_support
    exact hp.getVert_injOn (by change h ≤ p.length; omega) (by change e ≤ p.length; omega) eq
  have sub : T.image p.getVert ⊆ univ.filter (fun y => G.dist x y=2) := by
    intro w hw
    obtain ⟨e,he,rfl⟩ := mem_image.mp hw
    exact mem_filter.mpr ⟨mem_univ _,(good _ he).2⟩
  have large := (card_le_card sub).trans quota
  rw [card_image_of_injOn inj,count] at large
  omega
theorem impossible_of_length (p : G.Walk a b) (hp : p.IsPath) {x : V} (outside : x ∉ p.support)
    {i j lo hi m : ℕ} (left : 0 < i) (spaced : i+2 ≤ j) (right : j+1 < p.support.length)
    (marks : contactPositions p x = {i,j})
    (bound : hi ≤ p.support.length) (size : lo+m=hi)
    (unmarked : ∀ h ∈ Ico lo hi, h ≠ i ∧ h ≠ j)
    (via : ∀ h ∈ Ico lo hi, ∃ w, G.Adj x w ∧ G.Adj (p.getVert h) w)
    (cap : G.distEven x ≤ m+2) : False := by
  classical
  apply impossible_of_exact_length p hp outside left spaced right marks bound size unmarked via
  let T := univ.filter (fun y => G.dist x y=2)
  have missing : x ∉ T := by simp [T]
  have sub : insert x T ⊆ univ.filter (fun y => Even (G.dist x y)) := by
    intro w hw
    rcases mem_insert.mp hw with rfl|h
    · simp
    · exact mem_filter.mpr ⟨mem_univ _,by rw [(mem_filter.mp h).2]; decide⟩
  have count := card_le_card sub
  rw [card_insert_of_notMem missing] at count
  change T.card+1 ≤ G.distEven x at count
  change T.card ≤ m+1
  omega
end Graph189FourTerminalGap
end
section
namespace Graph189ExteriorGap
theorem exists_tight_protected_gap {L j m : ℕ} (t : Fin L)
    (a : Fin (j+1) ↪o Fin L)
    (prefix_pos : 0 < (a 0).val)
    (suffix_pos : (a (Fin.last j)).val+1 < L)
    (gap_pos : ∀ i : Fin j, (a i.castSucc).val+2 ≤ (a i.succ).val)
    (prefix_min : a 0 ≤ t → m ≤ (a 0).val)
    (suffix_min : t ≤ a (Fin.last j) → (a (Fin.last j)).val+1+m ≤ L)
    (gap_min : ∀ i : Fin j, a i.succ ≤ t ∨ t ≤ a i.castSucc →
      (a i.castSucc).val+1+m ≤ (a i.succ).val)
    (cap : L ≤ (j+1)*m+2*(j+1)) :
    (a 0 ≤ t ∧ (a 0).val=m) ∨
    (t ≤ a (Fin.last j) ∧ (a (Fin.last j)).val+1+m=L) ∨
    ∃ i : Fin j, (a i.succ ≤ t ∨ t ≤ a i.castSucc) ∧
      (a i.castSucc).val+1+m=(a i.succ).val := by
  by_contra! fail
  obtain ⟨first,last,inside⟩ := fail
  let pos (i : Fin (j+1)) := (a i).val + if t < a i then m else 0
  have base : m+1 ≤ pos 0 := by
    by_cases h : t < a 0
    · simp only [pos,if_pos h]; omega
    have le := le_of_not_gt h
    have := first le
    have := prefix_min le
    simp only [pos,if_neg h]; omega
  have step (i : Fin j) : pos i.castSucc+(m+2) ≤ pos i.succ := by
    have ordered := a.strictMono i.castSucc_lt_succ
    by_cases l : t < a i.castSucc
    · have h : a i.succ ≤ t ∨ t ≤ a i.castSucc := Or.inr l.le
      have := gap_min i h
      have := inside i h
      simp only [pos,if_pos l,if_pos (l.trans ordered)]; omega
    by_cases r : t < a i.succ
    · have := gap_pos i
      simp only [pos,if_neg l,if_pos r]; omega
    have h : a i.succ ≤ t ∨ t ≤ a i.castSucc := Or.inl (le_of_not_gt r)
    have := gap_min i h
    have := inside i h
    simp only [pos,if_neg l,if_neg r]; omega
  have acc (i : Fin (j+1)) : m+1+i.val*(m+2) ≤ pos i := by
    induction i using Fin.induction with
    | zero => simpa using base
    | succ i ih =>
      have h := step i
      simp only [Fin.val_succ,Fin.val_castSucc,Nat.succ_mul] at ih ⊢
      omega
  have finish : pos (Fin.last j)+2 ≤ L := by
    by_cases h : t < a (Fin.last j)
    · have := suffix_min h.le
      have := last h.le
      simp only [pos,if_pos h]; omega
    · simp only [pos,if_neg h]; omega
  have lower := acc (Fin.last j)
  simp only [Fin.val_last,Nat.mul_add,Nat.succ_mul] at lower cap
  omega
end Graph189ExteriorGap
end
section
namespace Graph189ExteriorGap
open Finset
theorem locate_tight_protected_gap {L j m : ℕ} (t : Fin L)
    (M : Finset (Fin L)) (count : M.card=j+1) (positive : 0 < m)
    (prefix_pos : 0 < (M.orderEmbOfFin count 0).val)
    (suffix_pos : (M.orderEmbOfFin count (Fin.last j)).val+1 < L)
    (gap_pos : ∀ i : Fin j, (M.orderEmbOfFin count i.castSucc).val+2 ≤ (M.orderEmbOfFin count i.succ).val)
    (prefix_min : M.orderEmbOfFin count 0 ≤ t → m ≤ (M.orderEmbOfFin count 0).val)
    (suffix_min : t ≤ M.orderEmbOfFin count (Fin.last j) →
      (M.orderEmbOfFin count (Fin.last j)).val+1+m ≤ L)
    (gap_min : ∀ i : Fin j, M.orderEmbOfFin count i.succ ≤ t ∨ t ≤ M.orderEmbOfFin count i.castSucc →
      (M.orderEmbOfFin count i.castSucc).val+1+m ≤ (M.orderEmbOfFin count i.succ).val)
    (cap : L ≤ (j+1)*m+2*(j+1)) :
    ∃ lo hi, lo < hi ∧ hi ≤ L ∧ hi-lo=m ∧ (t.val < lo ∨ hi ≤ t.val) ∧
      (lo=0 ∨ ∃ i∈M, i.val+1=lo) ∧ (hi=L ∨ ∃ i∈M, i.val=hi) ∧
      (0 < lo ∨ hi < L) ∧ ∀ i∈M, i.val < lo ∨ hi ≤ i.val := by
  let a := M.orderEmbOfFin count
  have marked (i : Fin (j+1)) : a i ∈ M := M.orderEmbOfFin_mem count i
  have preimage (i : Fin L) (hi : i∈M) : ∃ h, a h=i := by
    change i ∈ Set.range (M.orderEmbOfFin count)
    rwa [M.range_orderEmbOfFin]
  rcases exists_tight_protected_gap t a prefix_pos suffix_pos gap_pos prefix_min suffix_min gap_min cap
      with ⟨safe,size⟩ | ⟨safe,size⟩ | ⟨d,safe,size⟩
  · refine ⟨0,(a 0).val,by omega,(a 0).isLt.le,by omega,Or.inr safe,Or.inl rfl,
      Or.inr ⟨_,marked 0,rfl⟩,Or.inr (a 0).isLt,?_⟩
    intro i hi
    obtain ⟨d,rfl⟩ := preimage i hi
    exact Or.inr (a.monotone (Fin.zero_le d))
  · refine ⟨(a (Fin.last j)).val+1,L,by omega,le_rfl,by omega,Or.inl ?_,
      Or.inr ⟨_,marked _,rfl⟩,Or.inl rfl,Or.inl (by omega),?_⟩
    · change t.val ≤ (a (Fin.last j)).val at safe
      omega
    · intro i hi
      obtain ⟨d,rfl⟩ := preimage i hi
      exact Or.inl (Nat.lt_succ_of_le (show (a d).val ≤ (a (Fin.last j)).val from a.monotone (Fin.le_last d)))
  · refine ⟨(a d.castSucc).val+1,(a d.succ).val,by omega,(a d.succ).isLt.le,by omega,?_,
      Or.inr ⟨_,marked _,rfl⟩,Or.inr ⟨_,marked _,rfl⟩,Or.inl (by omega),?_⟩
    · rcases safe with left|right
      · exact Or.inr left
      · exact Or.inl (Nat.lt_succ_of_le right)
    · intro i hi
      obtain ⟨h,rfl⟩ := preimage i hi
      by_cases small : h ≤ d.castSucc
      · exact Or.inl (Nat.lt_succ_of_le (show (a h).val ≤ (a d.castSucc).val from a.monotone small))
      · exact Or.inr (a.monotone (show d.succ ≤ h by
          change ¬ h.val ≤ d.val at small
          change d.val+1 ≤ h.val
          omega))
end Graph189ExteriorGap
end
section
open SimpleGraph
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {a b x y : V}
theorem protected_swap_neighbors_with_route (p : G.Walk a b) (hp : p.IsPath) (z : V)
    (A J B : List V) (split : p.support=A++J++B) (kept : z ∈ A ∨ z ∈ B)
    (q : G.Walk x y) (hq : q.IsPath) (dis : List.Disjoint q.support p.support)
    (size : q.support.length=J.length)
    (left : ∀ v∈A.getLast?, G.Adj v x) (right : ∀ v∈B.head?, G.Adj y v)
    (uniform : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → z ∈ r.support → q.support ⊆ r.support → r.length=p.length →
      ∀ c ∈ r.support, ∀ v ∉ r.support, ∀ w ∉ r.support, G.Adj c v → G.Adj c w)
    {c : V} (contact : c ∈ A ∨ c ∈ B) (neighbor : ∃ v ∈ J, G.Adj c v) :
    ∀ v ∈ J, G.Adj c v := by
  obtain ⟨i,j,r,hr,e⟩ := splice_support p hp A J B split q hq dis left right
  have nd := hp.support_nodup
  rw [split] at nd
  have separated (v : V) (hv : v ∈ J) : v ∉ r.support := by
    rw [e]
    intro h
    rcases List.mem_append.mp h with mid | last
    · rcases List.mem_append.mp mid with first | new
      · exact List.disjoint_left.mp nd.of_append_left.disjoint first hv
      · exact List.disjoint_left.mp dis new (by simp [split,hv])
    · exact List.disjoint_left.mp nd.disjoint (by simp [hv]) last
  have length : r.length=p.length := by
    have h := r.length_support
    have g := p.length_support
    rw [split] at g
    rw [e] at h
    simp only [List.length_append,size] at h g
    omega
  have keep (v : V) (h : v∈A ∨ v∈B) : v∈r.support := by
    rw [e]
    rcases h with h | h <;> simp [h]
  obtain ⟨v,hv,edge⟩ := neighbor
  exact fun w hw => uniform r hr (keep z kept) (fun v hv => by rw [e]; simp [hv]) length c (keep c contact)
    v (separated v hv) w (separated w hw) edge
theorem protected_swap_neighbors (p : G.Walk a b) (hp : p.IsPath) (z : V)
    (A J B : List V) (split : p.support=A++J++B) (kept : z ∈ A ∨ z ∈ B)
    (q : G.Walk x y) (hq : q.IsPath) (dis : List.Disjoint q.support p.support)
    (size : q.support.length=J.length)
    (left : ∀ v∈A.getLast?, G.Adj v x) (right : ∀ v∈B.head?, G.Adj y v)
    (uniform : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → z ∈ r.support → r.length=p.length →
      ∀ c ∈ r.support, ∀ v ∉ r.support, ∀ w ∉ r.support, G.Adj c v → G.Adj c w)
    {c : V} (contact : c ∈ A ∨ c ∈ B) (neighbor : ∃ v ∈ J, G.Adj c v) :
    ∀ v ∈ J, G.Adj c v := by
  apply protected_swap_neighbors_with_route p hp z A J B split kept q hq dis size left right _ contact neighbor
  exact fun r hr hz _ => uniform r hr hz
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} {G : SimpleGraph V} {a b x y : V}
theorem interval_exchange_witnesses_with_route (p : G.Walk a b) (hp : p.IsPath) (t : Fin p.support.length)
    (M : Finset (Fin p.support.length)) (q : G.Walk x y) (hq : q.IsPath)
    (dis : List.Disjoint q.support p.support)
    (touch : ∀ i ∈ M, G.Adj p.support[i.val] x ∧ G.Adj p.support[i.val] y)
    (uniform : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → p.support[t.val] ∈ r.support → q.support ⊆ r.support → r.length=p.length →
      ∀ c ∈ r.support, ∀ v ∉ r.support, ∀ w ∉ r.support, G.Adj c v → G.Adj c w)
    {lo hi : ℕ} (nonempty : lo < hi) (bound : hi ≤ p.support.length) (size : hi-lo=q.support.length)
    (safe : t.val < lo ∨ hi ≤ t.val) (lower : lo=0 ∨ ∃ i∈M, i.val+1=lo)
    (upper : hi=p.support.length ∨ ∃ i∈M, i.val=hi) (one : 0 < lo ∨ hi < p.support.length) :
    ∀ i ∈ Ico lo hi, ∃ w, G.Adj x w ∧ G.Adj (p.getVert i) w := by
  let L := p.support
  let A := L.take lo
  let J := (L.drop lo).take (hi-lo)
  let B := L.drop hi
  have split : p.support=A++J++B := by
    change L=L.take lo++(L.drop lo).take (hi-lo)++L.drop hi
    rw [←List.take_add, Nat.add_sub_of_le nonempty.le,List.take_append_drop]
  have kept (i : Fin L.length) (s : i.val < lo ∨ hi ≤ i.val) : L[i.val]∈A ∨ L[i.val]∈B := by
    rcases s with u|v
    · exact Or.inl (List.mem_take_iff_getElem.mpr ⟨i.val,lt_min u i.isLt,rfl⟩)
    · exact Or.inr (List.mem_drop_iff_getElem.mpr
        ⟨i.val-hi,by have := i.isLt; omega,by simp [Nat.add_sub_of_le v]⟩)
  have inside (i : ℕ) (u : lo ≤ i) (v : i < hi) : p.getVert i ∈ J := by
    have ri : i < L.length := v.trans_le bound
    apply List.mem_take_iff_getElem.mpr
    refine ⟨i-lo,?_,?_⟩
    · rw [List.length_drop]
      exact lt_min (Nat.sub_lt_sub_right u v) (Nat.sub_lt_sub_right u ri)
    · simpa only [List.getElem_drop, Nat.add_sub_of_le u] using get_at p ri
  have left : ∀ v∈A.getLast?, G.Adj v x := by
    intro v hv
    rcases lower with h | ⟨i,mem,e⟩
    · simp [A,h] at hv
    · have last : A.getLast? = some L[i.val] := by
        change (L.take lo).getLast? = _
        rw [←e]
        exact (congrArg List.getLast? (List.take_succ_eq_append_getElem
          (l:=L) (i:=i.val) i.isLt)).trans List.getLast?_concat
      have same : L[i.val]=v := by simpa [last] using hv
      exact same ▸ (touch i mem).1
  have right : ∀ v∈B.head?, G.Adj y v := by
    intro v hv
    rcases upper with h | ⟨i,mem,e⟩
    · simp [B,L,h] at hv
    · have first : B.head?=some L[i.val] := by simp [B,←e,List.head?_drop]
      have same : L[i.val]=v := by simpa [first] using hv
      exact same ▸ (touch i mem).2.symm
  have length : q.support.length=J.length := by
    simp only [J,List.length_take,List.length_drop]
    rw [min_eq_left (Nat.sub_le_sub_right bound lo)]
    exact size.symm
  have witness : ∃ c, (c∈A ∨ c∈B) ∧ G.Adj x c ∧ ∃ v∈J, G.Adj c v := by
    rcases one with first|last
    · obtain zero | ⟨i,mem,e⟩ := lower
      · omega
      have edge := p.adj_getVert_succ (i:=i.val) (by have := p.length_support; omega)
      rw [e] at edge
      refine ⟨L[i.val],kept i (Or.inl (by omega)),(touch i mem).1.symm,
        p.getVert lo,inside lo le_rfl nonempty,?_⟩
      change G.Adj p.support[i.val] _
      rw [get_at p i.isLt]
      exact edge
    · obtain tail | ⟨i,mem,e⟩ := upper
      · omega
      have edge := p.adj_getVert_succ (i:=hi-1) (by have := p.length_support; omega)
      rw [show hi-1+1=hi by omega] at edge
      refine ⟨L[i.val],kept i (Or.inr e.ge),(touch i mem).1.symm,
        p.getVert (hi-1),inside _ (by omega) (by omega),?_⟩
      change G.Adj p.support[i.val] _
      rw [get_at p i.isLt,e]
      exact edge.symm
  obtain ⟨c,hc,cx,neighbor⟩ := witness
  have all := protected_swap_neighbors_with_route p hp _ A J B split (kept t safe) q hq dis length left right uniform hc neighbor
  intro i h
  exact ⟨c,cx,(all _ (inside i (mem_Ico.mp h).1 (mem_Ico.mp h).2)).symm⟩
theorem interval_exchange_witnesses (p : G.Walk a b) (hp : p.IsPath) (t : Fin p.support.length)
    (M : Finset (Fin p.support.length)) (q : G.Walk x y) (hq : q.IsPath)
    (dis : List.Disjoint q.support p.support)
    (touch : ∀ i ∈ M, G.Adj p.support[i.val] x ∧ G.Adj p.support[i.val] y)
    (uniform : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → p.support[t.val] ∈ r.support → r.length=p.length →
      ∀ c ∈ r.support, ∀ v ∉ r.support, ∀ w ∉ r.support, G.Adj c v → G.Adj c w)
    {lo hi : ℕ} (nonempty : lo < hi) (bound : hi ≤ p.support.length) (size : hi-lo=q.support.length)
    (safe : t.val < lo ∨ hi ≤ t.val) (lower : lo=0 ∨ ∃ i∈M, i.val+1=lo)
    (upper : hi=p.support.length ∨ ∃ i∈M, i.val=hi) (one : 0 < lo ∨ hi < p.support.length) :
    ∀ i ∈ Ico lo hi, ∃ w, G.Adj x w ∧ G.Adj (p.getVert i) w := by
  apply interval_exchange_witnesses_with_route p hp t M q hq dis touch _ nonempty bound size safe lower upper one
  exact fun r hr hz _ => uniform r hr hz
end Graph189ExteriorGap
end
section
open SimpleGraph Finset
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V}
theorem two_mark_exchange (p : G.Walk a b) (hp : p.IsPath) (t : Fin p.support.length)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → p.support[t.val]∈q.support → q.length ≤ p.length)
    (E : Finset V) (many : 1 < E.card) (outside : ∀ {v}, v∈E → v∉p.support)
    (routes : ∀ x y : E, x≠y → ∃ q : (G.induce (E : Set V)).Walk x y, q.IsHamiltonian)
    (M : Finset (Fin p.support.length)) (sz : M.card=2)
    (links : ∀ w∈E, ∀ i : Fin p.support.length, G.Adj p.support[i.val] w ↔ i∈M)
    (common : ∀ {i j}, ∀ r : G.Walk i j, r.IsPath → p.support[t.val]∈r.support →
      r.length=p.length → ∀ v∈r.support, ∀ u∉r.support, ∀ w∉r.support, G.Adj v u → G.Adj v w)
    (room : p.support.length ≤ 2*E.card+4) (cap : ∀ x∈E, G.distEven x ≤ E.card+2) : False := by
  classical
  obtain ⟨x,hx⟩ := card_pos.mp (by omega : 0 < E.card)
  let X : E := ⟨x,hx⟩
  obtain ⟨y,hy,ne⟩ := exists_mem_ne many x
  let Y : E := ⟨y,hy⟩
  obtain ⟨w,hw⟩ := routes X Y (fun e => ne (congrArg Subtype.val e).symm)
  let inc := (Embedding.induce (G:=G) (E : Set V)).toHom
  let q := w.map inc
  have hq : q.IsPath := hw.isPath.map Subtype.val_injective
  have dis : List.Disjoint q.support p.support := by
    apply List.disjoint_left.mpr
    intro v hv
    rw [show q.support=w.support.map inc from Walk.support_map _ _] at hv
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hv
    exact outside u.property
  have qlen : q.support.length=E.card := by
    change (w.map inc).support.length=E.card
    rw [Walk.support_map,List.length_map,hw.length_support]
    exact Fintype.card_coe E
  have touch (i : Fin p.support.length) (hi : i∈M) :
      G.Adj p.support[i.val] x ∧ G.Adj p.support[i.val] y := ⟨(links x hx i).mpr hi,(links y hy i).mpr hi⟩
  let A := M.orderEmbOfFin (show M.card=1+1 from sz)
  have mem (i : Fin 2) : A i∈M := M.orderEmbOfFin_mem sz i
  have adj (i : Fin 2) := touch (A i) (mem i)
  have first := (protected_contact_internal p hp t mx (outside hx) _ (adj 0).1).1
  have last := (protected_contact_internal p hp t mx (outside hx) _ (adj (Fin.last 1)).1).2
  have space (i : Fin 1) := protected_contact_spacing p hp t mx (outside hx) _ _ (A.strictMono i.castSucc_lt_succ)
    (adj i.castSucc).1 (adj i.succ).1
  obtain ⟨lo,hi,nonempty,bound,len,safe,lb,ub,one,unmarked⟩ := locate_tight_protected_gap t M
    (j:=1) (m:=E.card) sz (by omega) first last space
    (fun h => by have ql := protected_prefix_of_detour p hp t mx _ h q hq dis (adj 0).2.symm; simpa only [qlen] using ql)
    (fun h => by have ql := protected_suffix_of_detour p hp t mx _ h q hq dis (adj _).1; simpa only [qlen] using ql)
    (fun i h => by have ql := protected_interval_of_detour p hp t mx _ _ (A.strictMono i.castSucc_lt_succ) h
                    q hq dis (adj i.castSucc).1 (adj i.succ).2.symm; simpa only [qlen] using ql)
    room
  have witnesses := interval_exchange_witnesses p hp t M q hq dis touch common nonempty bound
    (len.trans qlen.symm) safe lb ub one
  let I := A 0
  let J := A (Fin.last 1)
  have spaced : I.val+2 ≤ J.val := space 0
  have neq : I≠J := fun e => by rw [e] at spaced; omega
  have pair : M={I,J} := by
    symm
    apply eq_of_subset_of_card_le (by
      intro v hv
      rcases mem_insert.mp hv with rfl|h
      · exact mem 0
      obtain rfl := mem_singleton.mp h
      exact mem (Fin.last 1))
    rw [card_pair neq,sz]
  have mark : contactPositions p x = {I.val,J.val} := by
    ext l
    constructor
    · intro h
      obtain ⟨hl,edge⟩ := (mem_contactPositions p x l).mp h
      have inM := (links x hx ⟨l,hl⟩).mp (by simpa [get_at] using edge)
      rw [pair] at inM
      simpa only [mem_insert,mem_singleton,Fin.ext_iff] using inM
    · intro h
      rcases mem_insert.mp h with rfl|other
      · exact (mem_contactPositions p x I.val).mpr ⟨I.isLt,by simpa [get_at] using (adj 0).1⟩
      have e := mem_singleton.mp other
      subst l
      exact (mem_contactPositions p x J.val).mpr ⟨J.isLt,by rw [←get_at p J.isLt]; exact (adj (Fin.last 1)).1⟩
  have range : lo+E.card=hi := by rw [←len,Nat.add_sub_of_le nonempty.le]
  refine Graph189FourTerminalGap.impossible_of_length p hp (outside hx) (i:=I.val) (j:=J.val) (lo:=lo) (hi:=hi) first spaced last mark bound range ?_ witnesses ?_
  · intro l hl
    have h := mem_Ico.mp hl
    have old := unmarked I (mem 0)
    have next := unmarked J (mem (Fin.last 1))
    omega
  · exact cap x hx
end Graph189ExteriorGap
end
section
open Finset SimpleGraph
namespace Graph189ExteriorAttachment
theorem extra_port {V : Type*} {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
    (p : G.Walk x y) (W : Finset V) (j : ℕ) (many : j < W.card)
    (rows : ∀ w ∈ W, j ≤ ((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w)).card)
    (cover : j < (W.biUnion (fun w => (univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] w))).card) :
    ∃ marks : Finset (Fin p.support.length), marks.card = j+1 ∧
      ∃ attach : marks ↪ W, ∀ i : marks, G.Adj p.support[i.val.val] (attach i).val := by
  classical
  let N (w : V) := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] w)
  let F (w : W) := N w.val
  have size : Fintype.card W = W.card := Fintype.card_coe W
  have whole : (univ.biUnion F).card = (W.biUnion N).card := by
    congr 1
    ext i
    constructor
    · intro hi
      obtain ⟨w,_,hw⟩ := mem_biUnion.mp hi
      exact mem_biUnion.mpr ⟨w.val,w.property,hw⟩
    · intro hi
      obtain ⟨w,hw,edge⟩ := mem_biUnion.mp hi
      exact mem_biUnion.mpr ⟨⟨w,hw⟩,mem_univ _,edge⟩
  have hall (T : Finset W) : T.card ≤ (T.biUnion F).card + (Fintype.card W-(j+1)) := by
    by_cases all : T=univ
    · rw [all,card_univ,whole,size]
      change j < (W.biUnion N).card at cover
      omega
    rcases T.eq_empty_or_nonempty with rfl | ⟨w,hw⟩
    · simp
    have proper : T.card < W.card := by
      by_contra! h
      exact all (Finset.eq_of_subset_of_card_le (subset_univ _) (by simpa using h))
    have incl : F w ⊆ T.biUnion F := fun i hi => mem_biUnion.mpr ⟨w,hw,hi⟩
    have lower := (rows w.val w.property).trans (card_le_card incl)
    omega
  obtain ⟨U,large,f,edge⟩ := Graph189ExteriorGap.hall_at_least F (j+1) (by omega) hall
  obtain ⟨B,sub,cardB⟩ := exists_subset_card_eq large
  let inc : B ↪ U := ⟨fun b => ⟨b.val,sub b.property⟩,
    fun _ _ e => Subtype.ext (congrArg (fun w : U => w.val) e)⟩
  let pos := inc.trans f
  let M := (univ : Finset B).image pos
  let chosen (b : B) : M := ⟨pos b,mem_image_of_mem _ (mem_univ _)⟩
  have bij : Function.Bijective chosen := by
    constructor
    · intro u v eq
      exact pos.injective (congrArg Subtype.val eq)
    · intro i
      obtain ⟨b,_,eq⟩ := mem_image.mp i.property
      exact ⟨b,Subtype.ext eq⟩
  let equiv := Equiv.ofBijective chosen bij
  let vertex : B ↪ W := ⟨Subtype.val,Subtype.val_injective⟩
  have card : M.card = B.card := by simpa using Fintype.card_congr equiv.symm
  refine ⟨M,card.trans cardB,equiv.symm.toEmbedding.trans vertex,?_⟩
  intro i
  have value : pos (equiv.symm i) = i.val := congrArg Subtype.val (equiv.apply_symm_apply i)
  have adj := (mem_filter.mp (edge (inc (equiv.symm i)))).2
  change G.Adj p.support[(pos (equiv.symm i)).val] (equiv.symm i).val.val at adj
  exact (congrArg (fun index : Fin p.support.length =>
    G.Adj (p.support.get index) (equiv.symm i).val.val) value).mp adj
end Graph189ExteriorAttachment
end
section
open SimpleGraph Finset
namespace Graph189LayerCover
variable {V : Type*} [Fintype V]
noncomputable def layer (G : SimpleGraph V) (z : V) (n : ℕ) : Finset V := by
  classical
  exact univ.filter (fun v => G.dist z v = n)
@[simp] theorem in_layer {G : SimpleGraph V} {z y : V} {n : ℕ} :
    y ∈ layer G z n ↔ G.dist z y = n := by classical simp [layer]
private theorem minimal_cover (A B : Finset V) (R : V → V → Prop)
    (hc : ∀ b ∈ B, ∃ a ∈ A, R a b) :
    ∃ T ⊆ A, (∀ b ∈ B, ∃ a ∈ T, R a b) ∧
      ∀ a ∈ T, ∃ b ∈ B, R a b ∧ ∀ a' ∈ T, a' ≠ a → ¬ R a' b := by
  classical
  let covers (S : Finset V) := ∀ b ∈ B, ∃ a ∈ S, R a b
  let family := A.powerset.filter covers
  have ha : A ∈ family := mem_filter.mpr ⟨mem_powerset.mpr (fun _ h => h), hc⟩
  obtain ⟨T,hT,hmin⟩ := family.exists_min_image Finset.card ⟨A,ha⟩
  obtain ⟨hsub,hcovers⟩ := mem_filter.mp hT
  have hsub' := mem_powerset.mp hsub
  refine ⟨T,hsub',hcovers,?_⟩
  intro a haT
  have missing : ¬ covers (T.erase a) := by
    intro h
    have hs : T.erase a ∈ family := mem_filter.mpr
      ⟨mem_powerset.mpr ((erase_subset a T).trans hsub'),h⟩
    exact (not_le_of_gt (card_erase_lt_of_mem haT)) (hmin _ hs)
  change ¬ (∀ b ∈ B, ∃ a' ∈ T.erase a, R a' b) at missing
  push Not at missing
  obtain ⟨b,hb,hprivate⟩ := missing
  obtain ⟨x,hx,hxb⟩ := hcovers b hb
  have hxa : x = a := by
    by_contra h
    exact hprivate x (mem_erase.mpr ⟨h,hx⟩) hxb
  exact ⟨b,hb,hxa ▸ hxb,fun a' ha' hdiff => hprivate a' (mem_erase.mpr ⟨hdiff,ha'⟩)⟩
omit [Fintype V] in
private theorem predecessor {G : SimpleGraph V} {z y : V} {d : ℕ}
    (h : G.dist z y = d+1) : ∃ p, G.dist z p = d ∧ G.Adj p y := by
  have hr : G.dist y z = d+1 := by rwa [dist_comm]
  have hpos : G.Reachable y z := Reachable.of_dist_ne_zero (by omega)
  obtain ⟨walk,hlen⟩ := hpos.exists_walk_length_eq_dist
  cases walk with
  | nil => simp at h
  | cons hy tail =>
    rename_i p
    have hlen' : tail.length = d := by rw [Walk.length_cons,hr] at hlen; omega
    have hle : G.dist z p ≤ d := by rw [dist_comm]; exact hlen' ▸ G.dist_le tail
    have ht := hy.diff_dist_adj (u := z)
    exact ⟨p,by omega,hy.symm⟩
omit [Fintype V] in
private theorem dist_two {G : SimpleGraph V} {x y q : V}
    (hne : x ≠ y) (hna : ¬G.Adj x y) (h1 : G.Adj x q) (h2 : G.Adj q y) :
    G.dist x y = 2 := by
  let w : G.Walk x y := .cons h1 (.cons h2 .nil)
  have hlo := w.reachable.one_lt_dist_of_ne_of_not_adj hne hna
  have hhi : G.dist x y ≤ 2 := G.dist_le w
  omega
omit [Fintype V] in
private theorem second_step {G : SimpleGraph V} (hc : G.Connected) (z y : V)
    (h : 2 ≤ G.dist z y) : ∃ b, G.dist z b = 2 ∧ G.dist z y = 2 + G.dist b y := by
  generalize hd : G.dist z y = d at h ⊢
  induction d using Nat.strong_induction_on generalizing y with
  | h d ih =>
    by_cases e : d=2
    · exact ⟨y,hd.trans e,by simp [e]⟩
    · obtain ⟨m,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show d≠0 by omega)
      obtain ⟨p,hp,hpy⟩ := predecessor hd
      obtain ⟨b,hb,split⟩ := ih m (by omega) p hp (by omega)
      have up := hc.dist_triangle (u:=b) (v:=p) (w:=y)
      rw [dist_eq_one_iff_adj.mpr hpy] at up
      have low := hc.dist_triangle (u:=z) (v:=b) (w:=y)
      exact ⟨b,hb,by omega⟩
theorem order_of_cover (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (z : V) (k : ℕ) (cap : ∀ v, G.distEven v ≤ k+1) (R : Finset V)
    (arms : ∀ a ∈ R, G.Adj z a)
    (covers : ∀ b ∈ layer G z 2, ∃ a ∈ R, G.Adj a b) :
    ∃ t ≤ R.card, t ≤ k+1 ∧ Fintype.card V ≤ 1+G.degree z+k+t*(k+1-t) := by
  classical
  obtain ⟨T,hTR,hTc,hTp⟩ := minimal_cover R (layer G z 2) G.Adj covers
  let port (a : V) : V := if h : a ∈ T then (hTp a h).choose else z
  have hp (a : V) (h : a ∈ T) : G.dist z (port a) = 2 ∧ G.Adj a (port a) ∧
      ∀ a' ∈ T, a' ≠ a → ¬ G.Adj a' (port a) := by
    simpa [port,h] using (hTp a h).choose_spec
  have hA (a : V) (h : a ∈ T) : G.dist z a = 1 := dist_eq_one_iff_adj.mpr (arms a (hTR h))
  let evenSet (a : V) := (univ.filter (fun v => Even (G.dist a v))).erase a
  have quota (a : V) : (evenSet a).card ≤ k := by
    have self : a ∈ univ.filter (fun v => Even (G.dist a v)) := by simp
    have bound := cap a
    change (univ.filter (fun v => Even (G.dist a v))).card ≤ k+1 at bound
    unfold evenSet
    rw [card_erase_of_mem self]
    omega
  have evenMem {a v : V} (n : a ≠ v) (ev : Even (G.dist a v)) : v ∈ evenSet a :=
    mem_erase.mpr ⟨Ne.symm n, mem_filter.mpr ⟨mem_univ _,ev⟩⟩
  let F := univ.filter (fun v => 3 ≤ G.dist z v ∧ ¬ Even (G.dist z v))
  let W (a : V) := F.filter (fun c => c ∈ evenSet a)
  have cov : F ⊆ T.biUnion W := by
    intro c hcF
    obtain ⟨far,odd⟩ := (mem_filter.mp hcF).2
    obtain ⟨b,hb,hsplit⟩ := second_step hc z c (by omega)
    obtain ⟨a,ha,hab⟩ := hTc b (in_layer.mpr hb)
    have upper := hc.dist_triangle (u:=a) (v:=b) (w:=c)
    rw [dist_eq_one_iff_adj.mpr hab] at upper
    have lower := hc.dist_triangle (u:=z) (v:=a) (w:=c)
    have unit := hA a ha
    have distinct : a ≠ c := by rintro rfl; omega
    have even : Even (G.dist a c) := by rw [Nat.even_iff] at odd ⊢; omega
    exact mem_biUnion.mpr ⟨a,ha,mem_filter.mpr ⟨hcF,evenMem distinct even⟩⟩
  have row (a : V) (ha : a ∈ T) : (W a).card + T.card ≤ k+1 := by
    let f (j : V) := if G.Adj a j then port j else j
    have hzj (j : V) (hj : j ∈ T) : G.dist z (f j) ≤ 2 := by
      by_cases h : G.Adj a j <;> simp [f,h,(hp j hj).1,hA j hj]
    have finj : Set.InjOn f ↑(T.erase a) := by
      intro j hj l hl hEq
      obtain ⟨_,hjT⟩ := mem_erase.mp hj
      obtain ⟨_,hlT⟩ := mem_erase.mp hl
      by_cases hjA : G.Adj a j <;> by_cases hlA : G.Adj a l <;> simp [f,hjA,hlA] at hEq
      · by_contra hne
        exact (hp l hlT).2.2 j hjT hne (hEq ▸ (hp j hjT).2.1)
      · have h1 := (hp j hjT).1; have h2 := hA l hlT; rw [hEq] at h1; omega
      · have h1 := (hp l hlT).1; have h2 := hA j hjT; rw [hEq] at h2; omega
      · exact hEq
    let E := (T.erase a).image f
    have heq : E.card = (T.erase a).card := card_image_of_injOn finj
    have hdis : Disjoint (W a) E := by
      apply Finset.disjoint_left.mpr
      intro x hx hw
      obtain ⟨j,hj,rfl⟩ := mem_image.mp hw
      have h1 := (mem_filter.mp (mem_filter.mp hx).1).2.1
      have h2 := hzj j (mem_erase.mp hj).2
      omega
    have incl : W a ∪ E ⊆ evenSet a := by
      intro x hx
      rcases mem_union.mp hx with hw|he
      · exact (mem_filter.mp hw).2
      · obtain ⟨j,hj,rfl⟩ := mem_image.mp he
        obtain ⟨hne,hj⟩ := mem_erase.mp hj
        suffices hd : G.dist a (f j) = 2 by
          apply evenMem _ (by simp [hd])
          intro eq
          rw [← eq, SimpleGraph.dist_self] at hd
          omega
        by_cases haj : G.Adj a j
        · simp only [f,if_pos haj]
          have hza := hA a ha
          have hzj' := (hp j hj).1
          apply dist_two _ ((hp j hj).2.2 a ha hne.symm) haj (hp j hj).2.1
          rintro heq'; rw [heq'] at hza; omega
        · simp only [f,if_neg haj]
          exact dist_two hne.symm haj (dist_eq_one_iff_adj.mp (hA a ha)).symm
            (dist_eq_one_iff_adj.mp (hA j hj))
    have hcount := (card_le_card incl).trans (quota a)
    rw [card_union_of_disjoint hdis,heq] at hcount
    have he := card_erase_add_one ha
    omega
  have hsize : T.card ≤ k+1 := by
    rcases T.eq_empty_or_nonempty with he|⟨a,ha⟩
    · simp [he]
    · have := row a ha; omega
  have farCount : F.card ≤ T.card*(k+1-T.card) := by
    calc F.card ≤ (T.biUnion W).card := card_le_card cov
         _ ≤ ∑ a ∈ T, (W a).card := card_biUnion_le
         _ ≤ ∑ _ ∈ T, (k+1-T.card) := sum_le_sum (fun a ha => by have := row a ha; omega)
         _ = T.card*(k+1-T.card) := by simp
  have all : (univ : Finset V) ⊆ (({z} ∪ G.neighborFinset z) ∪ evenSet z) ∪ F := by
    intro v hv
    by_cases same : v = z
    · subst v; simp
    by_cases adj : G.Adj z v
    · exact mem_union_left _ (mem_union_left _ (mem_union_right _ ((G.mem_neighborFinset z v).mpr adj)))
    by_cases e : Even (G.dist z v)
    · exact mem_union_left _ (mem_union_right _ (evenMem (Ne.symm same) e))
    have pos := (hc z v).one_lt_dist_of_ne_of_not_adj (Ne.symm same) adj
    exact mem_union_right _ (mem_filter.mpr ⟨hv,by rw [Nat.even_iff] at e; omega, e⟩)
  have one := card_union_le ({z} : Finset V) (G.neighborFinset z)
  have two := card_union_le ({z} ∪ G.neighborFinset z) (evenSet z)
  have three := card_union_le (({z} ∪ G.neighborFinset z) ∪ evenSet z) F
  have hcard := card_le_card all
  rw [card_univ] at hcard
  simp only [card_singleton,G.card_neighborFinset_eq_degree] at one
  exact ⟨T.card,card_le_card hTR,hsize,by have h := quota z; omega⟩
end Graph189LayerCover
end
section
open SimpleGraph Finset
namespace Graph189LayerCutoff
variable {V : Type*} [Fintype V]
private theorem row_mono {a t k : ℕ} (hta : t ≤ a) (ha : 2*a ≤ k+1) :
    t*(k+1-t) ≤ a*(k+1-a) := by
  have ht : t ≤ k+1 := by omega
  have hak : a ≤ k+1 := by omega
  have hsum : a+t ≤ k+1 := by omega
  have h : 0 ≤ (a-t : ℤ) * ((k:ℤ)+1-a-t) :=
    mul_nonneg (by omega) (by omega)
  zify [ht, hak]
  nlinarith
theorem order_of_small_cover (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (z : V) (k : ℕ) (cap : ∀ v, G.distEven v ≤ k+1) (R : Finset V)
    (arms : ∀ a ∈ R, G.Adj z a)
    (covers : ∀ b ∈ Graph189LayerCover.layer G z 2, ∃ a ∈ R, G.Adj a b)
    (hs : 2*R.card ≤ k+1) :
    Fintype.card V ≤ 1+G.degree z+k+R.card*(k+1-R.card) := by
  obtain ⟨t, hta, _, horder⟩ := Graph189LayerCover.order_of_cover G hc z k cap R arms covers
  exact horder.trans (Nat.add_le_add_left (row_mono hta hs) _)
theorem order_of_small_degree (G : SimpleGraph V) [DecidableRel G.Adj] (hc : G.Connected)
    (z : V) (k : ℕ) (cap : ∀ v, G.distEven v ≤ k+1) (hs : 2*G.degree z ≤ k+1) :
    Fintype.card V ≤ 1+G.degree z+k+G.degree z*(k+1-G.degree z) := by
  classical
  have covers : ∀ b ∈ Graph189LayerCover.layer G z 2, ∃ a ∈ G.neighborFinset z, G.Adj a b := by
    intro b hb
    have two := Graph189LayerCover.in_layer.mp hb
    obtain ⟨walk, hlen⟩ := (hc b z).exists_walk_length_eq_dist
    have hdist : G.dist b z = 2 := by rwa [dist_comm]
    rw [hdist] at hlen
    cases walk with
    | nil => simp at hlen
    | cons e walk =>
      rename_i a
      have hlen' : walk.length = 1 := by rw [Walk.length_cons] at hlen; omega
      have hle : G.dist z a ≤ 1 := by rw [dist_comm]; exact hlen' ▸ G.dist_le walk
      have had := e.diff_dist_adj (u := z)
      exact ⟨a, (G.mem_neighborFinset z a).mpr (dist_eq_one_iff_adj.mp (by omega)), e.symm⟩
  simpa only [G.card_neighborFinset_eq_degree] using
    (order_of_small_cover G hc z k cap (G.neighborFinset z)
      (fun a ha => (G.mem_neighborFinset z a).mp ha) covers (by simpa using hs))
end Graph189LayerCutoff
end
section
open Finset SimpleGraph
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ExteriorGap
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {a b : V}
theorem uniform_contacts_of_order (Q : G.Walk a b) (hQ : Q.IsPath)
    (t : Fin Q.support.length)
    (maximal : ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → Q.support[t.val] ∈ r.support → r.length ≤ Q.length)
    (E : Finset V) (outside : ∀ w ∈ E, w ∉ Q.support) (many : 1 < E.card)
    (routes : ∀ x y : E, x ≠ y → ∃ q : (G.induce (E : Set V)).Walk x y, q.IsHamiltonian)
    (s : ℕ) (small : s < E.card) (upper : Fintype.card V < (s+2)*E.card+(s+1))
    (rows : ∀ v ∈ E, s ≤ ((univ : Finset (Fin Q.support.length)).filter
      (fun i => G.Adj Q.support[i.val] v)).card) :
    ∃ marks : Finset (Fin Q.support.length), marks.card = s ∧
      ∀ w ∈ E, ∀ i : Fin Q.support.length, G.Adj Q.support[i.val] w ↔ i ∈ marks := by
  classical
  let N (w : V) := (univ : Finset (Fin Q.support.length)).filter (fun i => G.Adj Q.support[i.val] w)
  let A := E.biUnion N
  have bound : A.card ≤ s := by
    by_contra! extra
    obtain ⟨marks,number,f,edge⟩ := Graph189ExteriorAttachment.extra_port Q E s small rows extra
    have order := protected_hamilton_connected_matching Q hQ t maximal E many outside routes marks
      (card_pos.mp (by omega)) f edge
    rw [number] at order
    exact (not_lt_of_ge order) upper
  have incl {w : V} (hw : w ∈ E) : N w ⊆ A := fun _ hi => mem_biUnion.mpr ⟨w,hw,hi⟩
  have same {w : V} (hw : w ∈ E) : N w = A :=
    eq_of_subset_of_card_le (incl hw) (bound.trans (rows w hw))
  obtain ⟨w,hw⟩ := card_pos.mp (show 0 < E.card by omega)
  exact ⟨A,le_antisymm bound ((rows w hw).trans (card_le_card (incl hw))),fun v hv i => by
    rw [← same hv]
    simp [N]⟩
variable [Nontrivial V]
end Graph189ExteriorGap
end
section
open SimpleGraph Finset Graph189ExteriorGap
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189DegreeTwoDeletion
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
private theorem exterior_data {u v : V} (p : G.Walk u v) (hp : p.IsPath) (t : Fin p.support.length)
    (mx : ∀ {a b}, ∀ q : G.Walk a b, q.IsPath → p.support[t.val]∈q.support → q.length ≤ p.length)
    (low : G.degree p.support[t.val] < G.secondSmallestDegree)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    (large : 7 ≤ G.secondSmallestDegree) (order : Fintype.card V ≤ 3*G.secondSmallestDegree+1)
    (size : (p.support.toFinsetᶜ : Finset V).card+1=G.secondSmallestDegree) :
    let E := (p.support.toFinsetᶜ : Finset V)
    (∀ x y : E, x≠y → ∃ q : (G.induce (E : Set V)).Walk x y, q.IsHamiltonian) ∧
      ∃ M : Finset (Fin p.support.length), M.card=2 ∧
        ∀ w∈E, ∀ i : Fin p.support.length, G.Adj p.support[i.val] w ↔ i∈M := by
  classical
  let E := (p.support.toFinsetᶜ : Finset V)
  change E.card+1=G.secondSmallestDegree at size
  have out (w : V) (hw : w∈E) : w∉p.support := by simpa [E] using hw
  have routes := extreme_two_routes p hp t mx low cap large order size
  refine ⟨routes,uniform_contacts_of_order p hp t mx E out (by omega) routes 2 (by omega) (by omega) ?_⟩
  intro w hw
  have high := (degree_pair (G:=G) w p.support[t.val] (fun e => out w hw (e ▸ List.getElem_mem _))).resolve_right (not_le.mpr low)
  have bound := Graph189DenseExteriorOrder.neighbors_on_path p E
    (fun _ _ x _ nx => by simpa [E] using nx) hw
  omega
theorem traceable (hc : G.Connected) (z : V) (degree : G.degree z=2)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (large : 7 ≤ G.secondSmallestDegree)
    {a b : {v : V | v≠z}} (P : (G.induce {v : V | v≠z}).Walk a b) (hP : P.IsHamiltonian) :
    ∃ u v, ∃ p : G.Walk u v, p.IsHamiltonian := by
  classical
  by_contra nontrace
  let k := G.secondSmallestDegree
  change 7 ≤ k at large
  have order : Fintype.card V ≤ 3*k+1 := by
    have h := Graph189LayerCutoff.order_of_small_degree G hc z k cap (by rw [degree]; omega)
    rw [degree] at h
    omega
  obtain ⟨u,v,p,hp,t,eq,longest⟩ := exists_longest_through G z
  let E := (p.support.toFinsetᶜ : Finset V)
  have mx : ∀ {i j}, ∀ q : G.Walk i j, q.IsPath → p.support[t.val]∈q.support → q.length ≤ p.length :=
    fun q hq h => longest q hq (eq ▸ h)
  have low : G.degree p.support[t.val] < k := by rw [eq,degree]; omega
  have gap := protected_size_of_traceable_deletion z (by omega) P hP p hp longest
  rw [degree] at gap
  change 1+2+(2+1)*E.card ≤ Fintype.card V at gap
  have present : E.Nonempty := by
    by_contra empty
    apply nontrace
    refine ⟨u,v,p,hp.isHamiltonian_of_mem (fun w => ?_)⟩
    by_contra missing
    exact empty ⟨w,by simpa [E] using missing⟩
  have size : E.card+1=k := by
    by_contra fail
    have fit : E.card+3 ≤ k+1 := by omega
    have order' := protected_order_of_exterior_size p hp t mx low cap present (s:=3) (by decide)
      (by change 2*3 ≤ k; omega) fit
    change 4*(k-3+2) ≤ Fintype.card V+1 at order'
    omega
  obtain ⟨routes,M,sz,links⟩ := exterior_data p hp t mx low cap large order size
  have total := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at total
  change p.support.length+E.card=Fintype.card V at total
  have common {i j} (r : G.Walk i j) (hr : r.IsPath) (retained : p.support[t.val]∈r.support)
      (same : r.length=p.length) (w : V) (hw : w∈r.support) (x : V) (hx : x∉r.support)
      (y : V) (hy : y∉r.support) (wx : G.Adj w x) : G.Adj w y := by
    have count := card_add_card_compl r.support.toFinset
    rw [List.toFinset_card_of_nodup hr.support_nodup] at count
    have len : r.support.length=p.support.length := by rw [r.length_support,same,←p.length_support]
    obtain ⟨j,hj,atZ⟩ := List.mem_iff_getElem.mp (show z∈r.support from eq ▸ retained)
    let T : Fin r.support.length := ⟨j,hj⟩
    have lo : G.degree r.support[T.val] < k := by change G.degree r.support[j] < k; rw [atZ,degree]; omega
    have mx' : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → r.support[T.val]∈q.support → q.length ≤ r.length := by
      intro _ _ q hq ht
      rw [same]
      apply longest q hq
      simpa only [T,atZ] using ht
    obtain ⟨_,_,_,both⟩ := exterior_data r hr T mx' lo cap large order
      (by change (r.support.toFinsetᶜ : Finset V).card+1=k; omega)
    obtain ⟨l,hl,ev⟩ := List.mem_iff_getElem.mp hw
    rw [←ev] at wx ⊢
    exact (both y (by simpa using hy) ⟨l,hl⟩).mpr ((both x (by simpa using hx) ⟨l,hl⟩).mp wx)
  apply two_mark_exchange p hp t mx E (by omega) (fun {v} h => by simpa [E] using h)
    routes M sz links common (by omega)
  intro x _
  have h := cap x
  change G.distEven x ≤ k+1 at h
  omega
end Graph189DegreeTwoDeletion
end
section
namespace Graph189ExteriorDegreeCycle
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
theorem nontrivial_deletion_cycle_rounded {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (w : V) {u v : {x : V | x ≠ w}}
    (p : (G.induce {x : V | x ≠ w}).Walk u v) (hp : p.IsPath)
    (longest : ∀ {i j}, ∀ q : (G.induce {x : V | x ≠ w}).Walk i j, q.IsPath → q.length ≤ p.length)
    (edge : ∃ a ∉ p.support, ∃ b ∉ p.support, (G.induce {x : V | x ≠ w}).Adj a b)
    {k D d : ℕ} (cap : ∀ v, G.distEven v ≤ k+1) (degree : ∀ v : {x : V | x ≠ w}, D+1 ≤ G.degree v.val)
    (two : 2 ≤ d) (room : k+2*d ≤ 2*D+1) :
    ∃ a, ∃ Q : ((G.induce {x : V | x ≠ w}).induce {v | v ∉ p.support.toFinset}).Walk a a,
      Q.IsCycle ∧ d+1 ≤ Q.length := by
  classical
  let H := G.induce {x : V | x ≠ w}
  let T := {t : {x : V | x ≠ w} | t ∉ p.support.toFinset}
  apply cycle_of_nonisolated_degree two
  · obtain ⟨a,ha,b,hb,adj⟩ := edge
    exact ⟨⟨a,fun h => ha (List.mem_toFinset.mp h)⟩,⟨b,fun h => hb (List.mem_toFinset.mp h)⟩,adj⟩
  · intro a b adj
    have da := deletion_exterior_local_degree w p hp longest
      (a:=a.val) (b:=b.val) (fun h => a.property (List.mem_toFinset.mpr h))
      (fun h => b.property (List.mem_toFinset.mpr h)) adj (cap a.val.val) (degree a.val) (degree b.val)
    rw [degree_induce_filter]
    have eq : (H.neighborFinset a.val).filter (fun u => u∈T) = H.neighborFinset a.val \ p.support.toFinset := by
      ext z
      simp [T]
    rw [eq]
    change 2*D ≤ k+2*(H.neighborFinset a.val \ p.support.toFinset).card at da
    omega
theorem minimum_deletion_half_cycle {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (w : V) (minw : G.degree w=G.minDegree)
    {u v : {x : V | x ≠ w}} (p : (G.induce {x : V | x ≠ w}).Walk u v) (hp : p.IsPath)
    (longest : ∀ {i j}, ∀ q : (G.induce {x : V | x ≠ w}).Walk i j, q.IsPath → q.length ≤ p.length)
    (notTrace : ¬ ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian)
    (notH : ¬ ∃ a b, ∃ q : (G.induce {x : V | x ≠ w}).Walk a b, q.IsHamiltonian)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (k5 : 5 ≤ G.secondSmallestDegree) :
    ∃ a, ∃ Q : ((G.induce {x : V | x ≠ w}).induce {v | v ∉ p.support.toFinset}).Walk a a,
      Q.IsCycle ∧ (G.secondSmallestDegree+1)/2 ≤ Q.length := by
  have edge := minimum_deletion_exterior_edge w minw p hp longest notTrace notH (by omega) cap
  have high (a : {x : V | x ≠ w}) : G.secondSmallestDegree-1+1 ≤ G.degree a.val := by
    rcases degree_pair (G:=G) a.val w a.property with h|h
    · omega
    · rw [minw] at h
      have := G.minDegree_le_degree a.val
      omega
  obtain ⟨a,Q,hQ,sz⟩ := nontrivial_deletion_cycle_rounded (D:=G.secondSmallestDegree-1)
    (d:=(G.secondSmallestDegree-1)/2) w p hp longest edge cap high (by omega) (by omega)
  exact ⟨a,Q,hQ,by omega⟩
end Graph189ExteriorDegreeCycle
end
section
namespace Graph189ExteriorDegreeCycle
open SimpleGraph Graph189UniversalCycle
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
theorem minimum_completion_half_cycle {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (w : V) (minw : G.degree w=G.minDegree)
    {v : V} (C : (completeAt G w).Walk v v) (hc : C.IsCycle)
    (longest : ∀ a (R : (completeAt G w).Walk a a), R.IsCycle → R.length ≤ C.length)
    (notTrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    (notH : ¬ ∃ a b, ∃ p : (G.induce {x : V | x ≠ w}).Walk a b, p.IsHamiltonian)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1) (k5 : 5 ≤ G.secondSmallestDegree) :
    ∃ a, ∃ Q : ((completeAt G w).induce {t : V | t ∉ C.support}).Walk a a,
      Q.IsCycle ∧ (G.secondSmallestDegree+1)/2 ≤ Q.length := by
  classical
  let H := G.induce {u : V | u ≠ w}
  obtain ⟨u,v,p,hp,_,support,maxp⟩ := longest_in_deletion G w C hc longest
  obtain ⟨a,Q,hQ,len⟩ := minimum_deletion_half_cycle w minw p hp (fun r => maxp _ _ r) notTrace notH cap k5
  let U := {t : {v : V | v ≠ w} | t ∉ p.support.toFinset}
  let W := {t : V | t ∉ C.support}
  let f : H.induce U →g (completeAt G w).induce W := {
    toFun := fun t => ⟨t.val.val,fun h => t.property (List.mem_toFinset.mpr ((support _).mpr h))⟩
    map_rel' := fun h => Or.inl h }
  have inj : Function.Injective f := by
    intro i j h
    have values : i.val.val=j.val.val := congrArg (fun z : W => z.val) h
    exact Subtype.ext (Subtype.ext values)
  exact ⟨f a,Q.map f,hQ.map inj,len.trans_eq (Walk.length_map f Q).symm⟩
end Graph189ExteriorDegreeCycle
end
section
open SimpleGraph Graph189UniversalCycle
namespace Graph189ExteriorDegreeCycle
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
theorem minimum_bondy_order (w : V) (minw : G.degree w=G.minDegree)
    (notTrace : ¬ ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian)
    (notH : ¬ ∃ a b, ∃ p : (G.induce {x : V | x ≠ w}).Walk a b, p.IsHamiltonian)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    {l : ℕ} (three : 3 ≤ l) (conn : l ≤ (completeAt G w).vertexConnectivity)
    (enough : 4*l ≤ G.secondSmallestDegree+5) :
    (l+1)*(G.secondSmallestDegree-l+2)-1 ≤ Fintype.card V := by
  classical
  let K := completeAt G w
  have minimum := secondDegree_le_completeAt_minDegree (G:=G) w minw
  change G.secondSmallestDegree ≤ K.minDegree at minimum
  have two (v : V) : 2 ≤ K.degree v := by
    have := K.minDegree_le_degree v
    omega
  obtain ⟨z,C,hC,_⟩ := cycle_of_degree (G:=K) w (d:=2) (by decide) two
  obtain ⟨a,P,hP,maximal⟩ := exists_longest_cycle K ⟨z,C,hC⟩
  obtain ⟨b,Q,hQ,sz⟩ := minimum_completion_half_cycle w minw P hP maximal notTrace notH cap (by omega)
  have order := Graph189BondyExterior.order_of_long_exterior (G:=K) (k:=l) (by omega) conn
    (by omega) P hP maximal Q hQ (by omega) (by omega)
  have comparison := Nat.mul_le_mul_left (l+1)
    (show G.secondSmallestDegree-l+2 ≤ K.minDegree-l+2 by omega)
  omega
end Graph189ExteriorDegreeCycle
end
section
open SimpleGraph Finset Graph189UniversalCycle Graph189ExteriorDegreeCycle
namespace Graph189DegreeTwoOriginal
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem traceable (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree)
    (conn : 2 ≤ G.vertexConnectivity) (z : V) (degree : G.degree z=2) (large : 7 ≤ G.secondSmallestDegree) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  have upper (v : V) : G.distEven v ≤ 1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have point (v : V) : G.distEven v ≤ G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using upper v
  by_cases H : ∃ a b, ∃ p : (G.induce {v : V | v≠z}).Walk a b, p.IsHamiltonian
  · obtain ⟨a,b,p,hp⟩ := H
    exact Graph189DegreeTwoDeletion.traceable hc z degree point large p hp
  by_contra nontrace
  obtain ⟨w,hw⟩ := G.exists_minimal_degree_vertex
  have lm := Graph189CutSides.connectivity_le_degree (G:=G) w
  have zm := G.minDegree_le_degree z
  have zc := Graph189CutSides.connectivity_le_degree (G:=G) z
  have minimum : G.degree z=G.minDegree := by omega
  have maxk := (secondDegree_le_completeAt_minDegree (G:=G) z minimum).trans
    ((completeAt G z).minDegree_le_degree z)
  rw [completeAt_degree_self] at maxk
  have room : G.vertexConnectivity < Fintype.card V-1 := by omega
  have free (T : Finset V) (size : T.card=G.vertexConnectivity) (inside : z∈T) :
      (G.induce {v : V | v∉T}).Connected := by
    by_contra bad
    have survives : ∃ v, v∉T := by
      by_contra! full
      have eq := eq_univ_iff_forall.mpr full
      rw [eq,card_univ] at size
      omega
    obtain ⟨A,B,sides⟩ := Graph189CutSides.exists_cutSides_of_disconnected T survives bad
    have bound := sides.anchor_degree (fun U h => Graph189CutSides.connected_after_smaller_deletion
      (G:=G) U (h.trans_eq size)) upper inside
    omega
  have lift := completeAt_connectivity_add_one z room free
  have lower := minimum_bondy_order z minimum nontrace H point (l:=3) (by decide) (by omega) (by omega)
  change 4*(G.secondSmallestDegree-3+2)-1 ≤ Fintype.card V at lower
  have bound := Graph189LayerCutoff.order_of_small_degree G hc z G.secondSmallestDegree point
    (by rw [degree]; omega)
  rw [degree] at bound
  omega
end Graph189DegreeTwoOriginal
end
section
open SimpleGraph Finset
namespace Graph189ParentConnectivity
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem two_of_deletions (hc : G.Connected) (order : 3 ≤ Fintype.card V)
    (deletion : ∀ z : V, (G.induce {v : V | v≠z}).Connected) : 2 ≤ G.vertexConnectivity := by
  classical
  let M : Set ℕ := {j | ∃ S : Finset V, S.card=j ∧
    (¬(G.induce ((S : Set V)ᶜ)).Connected ∨ S.card=Fintype.card V-1)}
  have h : G.vertexConnectivity=sInf M := by
    unfold vertexConnectivity
    rw [if_neg (by omega : ¬Fintype.card V≤1)]
  obtain ⟨z⟩ := hc.nonempty
  have ex : M.Nonempty := ⟨_,univ.erase z,rfl,Or.inr (by simp)⟩
  rw [h]
  obtain ⟨T,sz,bad|full⟩ := Nat.sInf_mem ex
  · by_contra! small
    apply bad
    change (G.induce {v : V | v∉T}).Connected
    by_cases empty : T=∅
    · subst T
      rw [show {v : V | v∉(∅ : Finset V)}=Set.univ by ext; simp]
      exact hc.map G.induceUnivIso.symm.toHom G.induceUnivIso.symm.surjective
    obtain ⟨v,rfl⟩ := card_eq_one.mp (show T.card=1 by
      have := card_pos.mpr (nonempty_iff_ne_empty.mpr empty)
      omega)
    rw [show {w : V | w∉({v} : Finset V)}={w : V | w≠v} by ext; simp]
    exact deletion v
  · omega
end Graph189ParentConnectivity
end
section
open Finset SimpleGraph Graph189UniversalCycle Graph189ExteriorDegreeCycle Graph189CutSides
namespace Graph189ModerateEight
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
theorem traceable_below_four (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 7 ≤ G.secondSmallestDegree) (conn : 2 ≤ G.vertexConnectivity)
    (order : Fintype.card V+5<4*G.secondSmallestDegree) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian := by
  classical
  let k := G.secondSmallestDegree
  let n := Fintype.card V
  let s := G.vertexConnectivity
  change 7 ≤ k at large
  change 2 ≤ s at conn
  change n+5<4*k at order
  have upper (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have point (v : V) : G.distEven v ≤ G.secondSmallestDegree+1 := by simpa only [Nat.add_comm] using upper v
  by_contra nontrace
  by_cases three : 3 ≤ s
  · have bound := Graph189RotationLinked.base_order nontrace point (l:=3) (by decide)
      three (by change 2*3+1 ≤ k; omega)
    change 4*(k-3+2) ≤ n+1 at bound
    omega
  have two : s=2 := by omega
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have minimum := hz.symm
  have sd := connectivity_le_degree (G:=G) z
  change s ≤ G.degree z at sd
  by_cases lowTwo : G.degree z=2
  · exact nontrace (Graph189DegreeTwoOriginal.traceable hc cap conn z lowTwo large)
  have zthree : 3 ≤ G.degree z := by omega
  by_cases H : ∃ a b, ∃ p : (G.induce {x : V | x≠z}).Walk a b, p.IsHamiltonian
  · obtain ⟨a,b,p,hp⟩ := H
    have low := low_of_traceable_minimum_deletion (by change 5 ≤ k; omega) point nontrace z minimum p hp
    have bound := Graph189ExteriorGap.order_of_traceable_low_deletion z low point nontrace p hp
      (s:=3) (by decide) (by change 2*3 ≤ k; omega) zthree
    change 4*(k-3+2) ≤ n+1 at bound
    omega
  have max := (secondDegree_le_completeAt_minDegree (G:=G) z minimum).trans ((completeAt G z).minDegree_le_degree z)
  rw [completeAt_degree_self] at max
  change k ≤ n-1 at max
  have room : G.vertexConnectivity < Fintype.card V-1 := by change s < n-1; omega
  by_cases free : ∀ T : Finset V, T.card=G.vertexConnectivity → z∈T →
      (G.induce {v : V | v∉T}).Connected
  · have connK := completeAt_connectivity_add_one z room free
    have bound := Graph189RotationLinked.minimum_order z minimum nontrace H point (l:=3)
      (by decide) (by change s+1 ≤ _ at connK; omega) (by change 2*3+1 ≤ k; omega)
    change 4*(k-3+2)-1 ≤ n at bound
    omega
  push Not at free
  obtain ⟨T,size,zin,bad⟩ := free
  have survive : ∃ t, t∉T := by
    by_contra! all
    have eq := eq_univ_iff_forall.mpr all
    rw [eq,card_univ] at size
    change n=s at size
    omega
  obtain ⟨A,B,cut⟩ := exists_cutSides_of_disconnected T survive bad
  have sep := cut.anchor_degree (fun L h => connected_after_smaller_deletion L (h.trans_eq size)) upper zin
  change k+1 ≤ G.degree z+T.card at sep
  change T.card=s at size
  have near : k ≤ G.minDegree+1 := by omega
  have complete : ∃ w : V, 3≤(completeAt G w).vertexConnectivity ∧ k≤(completeAt G w).minDegree := by
    by_cases tie : k ≤ G.minDegree
    · obtain ⟨w,gain⟩ := Graph189CriticalConnectivity.exists_completion (G:=G) room
        (by change 3*s<2*(G.minDegree+1); omega)
      change s+1 ≤ _ at gain
      exact ⟨w,by omega,tie.trans (minDegree_le_completeAt w)⟩
    have eq : G.degree z+1=k := by omega
    obtain ⟨w,wz,miss,gain⟩ := Graph189AtomNonneighbor.free_nonneighbor z cut size zin room
      (by change 3*s<2*(G.minDegree+1); omega) (by change G.degree z < k; omega)
      (by change G.degree z+s ≤ k+1; omega)
    change s+1 ≤ _ at gain
    exact ⟨w,by omega,Graph189AtomNonneighbor.repaired_minDegree z w wz miss eq⟩
  obtain ⟨w,gain,minK⟩ := complete
  have bound := Graph189RepairedConeOrder.order_three w large nontrace point
    (by change k<2*G.minDegree; omega) gain minK
  change 4*(k-3+2)-1 ≤ n at bound
  omega
theorem traceable_moderate (hc : G.Connected)
    (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (large : 8 ≤ G.secondSmallestDegree) (conn : 2 ≤ G.vertexConnectivity)
    (order : Fintype.card V≤3*G.secondSmallestDegree+2) :
    ∃ a b, ∃ p : G.Walk a b, p.IsHamiltonian :=
  traceable_below_four hc cap (by omega) conn (by omega)
end Graph189ModerateEight
end
section
open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189TwoExteriorLinks
variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} {x y : V}
structure Arm (p : G.Walk x y) (W : Finset V) where
  mark : Fin p.support.length
  root : V
  inside : root∈W
  port : V
  contact : G.Adj port p.support[mark.val]
  route : G.Walk root port
  simple : route.IsPath
  off : ∀ v∈route.support, v∉p.support
  away : ∀ v∈route.support.tail, v∉W
theorem arm_of_list (p : G.Walk x y) {W : Finset V}
    (apart : ∀ v∈W, v∉p.support) {l : List V}
    (h : OMA.BondyK.ABP G W p.support.toFinset l ∧
      (∀ v∈l.tail, v∉W) ∧ (∀ v∈l.dropLast,v∉p.support.toFinset)) :
    ∃ a : Arm p W, (∀ v∈a.route.support, v∈l) ∧ p.support[a.mark.val]∈l := by
  obtain ⟨⟨nd,ch,⟨r,hr,first⟩,⟨b,hb,last⟩⟩,tail,lastOff⟩ := h
  have ne : l≠[] := by intro e; simp [e] at first
  have split : l=l.dropLast++[b] := by
    rw [List.getLast?_eq_getLast_of_ne_nil ne,Option.some.injEq] at last
    rw [←last,List.dropLast_append_getLast]
  let M := l.dropLast
  have mne : M≠[] := by
    intro eq
    change l.dropLast=[] at eq
    rw [split,eq] at first
    simp only [List.nil_append,List.head?_cons,Option.some.injEq] at first
    exact apart r hr (first ▸ List.mem_toFinset.mp hb)
  have hd : M.head mne=r := by
    have e : l=M++[b] := split
    rw [e,List.head?_append,List.head?_eq_some_head mne] at first
    simpa using first
  have dc := nd
  have cc := ch
  change l=M++[b] at split
  rw [split] at dc cc
  have subch := (List.isChain_append.mp cc).1
  let q := Walk.ofSupport M mne subch
  have supp : q.support=M := Walk.support_ofSupport mne subch
  let j : Fin p.support.length := ⟨p.support.idxOf b,List.idxOf_lt_length_iff.mpr (List.mem_toFinset.mp hb)⟩
  have mark : p.support[j.val]=b := List.getElem_idxOf j.isLt
  have touch : G.Adj (M.getLast mne) p.support[j.val] := by
    rw [mark]
    exact (List.isChain_append.mp cc).2.2 _ (List.getLast?_eq_getLast_of_ne_nil mne) _ rfl
  let a : Arm p W := {
    mark := j
    root := M.head mne
    inside := hd ▸ hr
    port := M.getLast mne
    contact := touch
    route := q
    simple := Walk.IsPath.mk' (by rw [supp]; exact dc.of_append_left)
    off := by
      intro v hv hit
      rw [supp] at hv
      exact lastOff v hv (List.mem_toFinset.mpr hit)
    away := by
      intro v hv
      rw [supp] at hv
      apply tail
      rw [split,List.tail_append_of_ne_nil mne]
      exact List.mem_append_left _ hv }
  refine ⟨a,?_,?_⟩
  · intro v hv
    change v∈q.support at hv
    rw [supp] at hv
    rw [split]
    exact List.mem_append_left _ hv
  · change p.support[j.val]∈l
    rw [mark]
    exact List.mem_of_getLast? last
omit [DecidableEq V] in
private theorem Arm.start {p : G.Walk x y} {W : Finset V} (a : Arm p W)
    (outside : ∀ v∈W, v∉p.support) {b : V} (q : G.Walk a.root b) (hq : q.IsPath)
    (uses : ∀ v∈q.support, v∈W) :
    (a.route.reverse.append q).IsPath ∧
      ∀ v∈(a.route.reverse.append q).support, v∉p.support := by
  constructor
  · apply Walk.IsPath.mk'
    rw [Walk.support_append_eq_support_dropLast_append,Walk.support_reverse,List.dropLast_reverse]
    apply List.Nodup.append (by simpa using a.simple.support_nodup.tail) hq.support_nodup
    intro u hu hv
    exact a.away u (List.mem_reverse.mp hu) (uses u hv)
  · intro v hv
    rcases (Walk.mem_support_append_iff _ _).mp hv with ha|hb
    · exact a.off v (by simpa using ha)
    · exact outside v (uses v hb)
omit [DecidableEq V] in
theorem ordered_positions {p : G.Walk x y} (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ p.length)
    {W : Finset V} (outside : ∀ v∈W, v∉p.support)
    (a b : Arm p W) (before : a.mark < b.mark)
    (distinct : ∀ v∈a.route.support, v∉b.route.support) {m t : ℕ}
    (start : ∀ r∈W, ∃ u, ∃ q : G.Walk r u, q.IsPath ∧ m ≤ q.support.length ∧ ∀ v∈q.support,v∈W)
    (join : ∀ r∈W, ∀ s∈W, r≠s → ∃ q : G.Walk r s, q.IsPath ∧ t ≤ q.support.length ∧ ∀ v∈q.support,v∈W) :
    m ≤ a.mark.val ∧ a.mark.val+1+t ≤ b.mark.val ∧ b.mark.val+1+m ≤ p.support.length := by
  obtain ⟨_,q1,h1,len1,W1⟩ := start a.root a.inside
  obtain ⟨h1',off1⟩ := a.start outside q1 h1 W1
  obtain ⟨_,q2,h2,len2,W2⟩ := start b.root b.inside
  obtain ⟨h2',off2⟩ := b.start outside q2 h2 W2
  have localDis {i j} (q : G.Walk i j) (h : ∀ v∈q.support,v∉p.support) :
      List.Disjoint q.support p.support := List.disjoint_left.mpr h
  have l := prefix_of_detour p hp longest a.mark (a.route.reverse.append q1).reverse h1'.reverse
    (by
      apply List.disjoint_left.mpr
      intro v hv
      rw [Walk.support_reverse,List.mem_reverse] at hv
      exact off1 v hv) a.contact
  have r := suffix_of_detour p hp longest b.mark _ h2' (localDis _ off2) b.contact.symm
  have diff : a.root≠b.root := by
    intro eq
    apply distinct _ a.route.start_mem_support
    rw [eq]
    exact b.route.start_mem_support
  obtain ⟨q,hq,len,mem⟩ := join a.root a.inside b.root b.inside diff
  obtain ⟨path,dis⟩ := a.start outside q hq mem
  let T := (a.route.reverse.append q).append b.route
  have pathT : T.IsPath := by
    apply Walk.IsPath.mk'
    rw [show T=(a.route.reverse.append q).append b.route from rfl,Walk.support_append]
    apply List.Nodup.append path.support_nodup b.simple.support_nodup.tail
    intro u hu hv
    rcases (Walk.mem_support_append_iff _ _).mp hu with ha|hh
    · exact distinct u (by simpa using ha) (List.mem_of_mem_tail hv)
    · exact b.away u hv (mem u hh)
  have disT : List.Disjoint T.support p.support := by
    apply List.disjoint_left.mpr
    intro v hv
    rcases (Walk.mem_support_append_iff _ _).mp hv with h|h
    · exact dis v h
    · exact b.off v h
  have inner := interval_of_detour p hp longest a.mark b.mark before T pathT disT a.contact.symm b.contact
  have plen := p.length_support
  simp only [T,Walk.length_support,Walk.length_append,Walk.length_reverse] at l r inner len1 len2 len
  exact ⟨by omega,by omega,by omega⟩
theorem arms [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (p : G.Walk x y) (hp : p.IsPath) (W : Finset V) (outside : ∀ v∈W,v∉p.support)
    (count : ℕ) (conn : count ≤ G.vertexConnectivity) (wide : count ≤ W.card) (longP : count ≤ p.support.length) :
    ∃ A : Fin count→Arm p W, Function.Injective (fun i => (A i).mark) ∧
      ∀ i j, i≠j → ∀ v∈(A i).route.support,v∉(A j).route.support := by
  classical
  let P := p.support.toFinset
  have szP : count ≤ P.card := by
    rw [show P=p.support.toFinset from rfl,List.toFinset_card_of_nodup hp.support_nodup]
    exact longP
  obtain ⟨L,hL,separate⟩ := OMA.BondyK.menger_trim (G:=G) W P count (by
    intro S separates
    by_contra! small
    have leftover (T : Finset V) (big : count ≤ T.card) : ∃ v∈T,v∉S := by
      by_contra! inc
      have := card_le_card (show T⊆S from inc)
      omega
    obtain ⟨r,hr,rS⟩ := leftover W wide
    obtain ⟨b,hb,bS⟩ := leftover P szP
    obtain ⟨q,hq⟩ := (Graph189CutSides.connected_after_smaller_deletion (G:=G) S (small.trans_le conn)).exists_isPath
      (⟨r,rS⟩ : {v : V | v∉S}) ⟨b,bS⟩
    obtain ⟨v,hv,vs⟩ := separates (q.support.map Subtype.val) ⟨hq.support_nodup.map Subtype.val_injective,
      (List.isChain_map Subtype.val).mpr q.isChain_adj_support,
      ⟨r,hr,by rw [←q.cons_tail_support,List.map_cons,List.head?_cons]⟩,
      ⟨b,hb,by rw [List.getLast?_map,List.getLast?_eq_getLast_of_ne_nil q.support_ne_nil,q.getLast_support]; rfl⟩⟩
    obtain ⟨v,_,rfl⟩ := List.mem_map.mp hv
    exact v.property vs)
  choose A included ends using fun i => arm_of_list p outside (hL i)
  refine ⟨A,?_,fun i j ne v hi hj => separate i j ne v (included i v hi) (included j v hj)⟩
  intro i j eq
  by_contra ne
  apply separate i j ne _ (ends i)
  change (A i).mark=(A j).mark at eq
  simpa only [eq] using ends j
theorem path_of_routes [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ p.length)
    (conn : 2 ≤ G.vertexConnectivity) (W : Finset V) (outside : ∀ v∈W,v∉p.support)
    (wide : 2 ≤ W.card) (longP : 2 ≤ p.support.length) {m t : ℕ}
    (start : ∀ r∈W, ∃ u, ∃ q : G.Walk r u, q.IsPath ∧ m ≤ q.support.length ∧ ∀ v∈q.support,v∈W)
    (join : ∀ r∈W, ∀ s∈W, r≠s → ∃ q : G.Walk r s, q.IsPath ∧ t ≤ q.support.length ∧ ∀ v∈q.support,v∈W) :
    2*m+t+2 ≤ p.support.length := by
  classical
  obtain ⟨A,inj,separate⟩ := arms p hp W outside 2 conn wide longP
  let a := A 0
  let b := A 1
  have dis := separate 0 1 (by decide)
  have diff : a.mark≠b.mark := fun eq => (show (0:Fin 2)≠1 by decide) (inj eq)
  rcases lt_or_gt_of_ne diff with ab|ba
  · obtain ⟨l,mid,r⟩ := ordered_positions hp longest outside a b ab dis start join
    omega
  · obtain ⟨l,mid,r⟩ := ordered_positions hp longest outside b a ba (fun v hb ha => dis v ha hb) start join
    omega
theorem cycle_routes {r : V} (C : G.Walk r r) (hc : C.IsCycle) :
    let W := C.support.toFinset
    C.length ≤ W.card ∧
    (∀ a∈W, ∃ u, ∃ q : G.Walk a u, q.IsPath ∧ C.length ≤ q.support.length ∧ ∀ v∈q.support,v∈W) ∧
    (∀ a∈W, ∀ b∈W, a≠b → ∃ q : G.Walk a b, q.IsPath ∧ (C.length+1)/2+1 ≤ q.support.length ∧ ∀ v∈q.support,v∈W) := by
  classical
  let W := C.support.toFinset
  have width : C.length ≤ W.card := by
    have sub : C.support.tail.toFinset⊆W := by
      intro v hv
      exact List.mem_toFinset.mpr (List.mem_of_mem_tail (List.mem_toFinset.mp hv))
    have h := card_le_card sub
    rw [List.toFinset_card_of_nodup hc.support_nodup,List.length_tail,C.length_support] at h
    omega
  have contains (a : V) (ha : a∈W) (v : V) (hv : v∈(C.rotate a (List.mem_toFinset.mp ha)).support) :
      v∈W := List.mem_toFinset.mpr ((C.mem_support_rotate_iff a _).mp hv)
  have start (a : V) (ha : a∈W) :
      ∃ u, ∃ q : G.Walk a u, q.IsPath ∧ C.length ≤ q.support.length ∧ ∀ v∈q.support, v∈W := by
    let R := C.rotate a (List.mem_toFinset.mp ha)
    have rc : R.IsCycle := hc.rotate _
    have l : R.length=C.length := C.length_rotate _ _
    have h := R.length_dropLast_add_one rc.not_nil
    refine ⟨_,R.dropLast,rc.isPath_dropLast,by rw [Walk.length_support]; omega,?_⟩
    intro v hv
    apply contains a ha
    rw [Walk.support_dropLast rc.not_nil] at hv
    exact List.dropLast_subset _ hv
  have pair (a : V) (ha : a∈W) (b : V) (hb : b∈W) (diff : a≠b) :
      ∃ q : G.Walk a b, q.IsPath ∧ (C.length+1)/2+1 ≤ q.support.length ∧ ∀ v∈q.support,v∈W := by
    let R := C.rotate a (List.mem_toFinset.mp ha)
    have rc : R.IsCycle := hc.rotate _
    have on : b∈R.support := (C.mem_support_rotate_iff a _).mpr (List.mem_toFinset.mp hb)
    let L := R.takeUntil b on
    let T := R.dropUntil b on
    have split : L.append T=R := R.take_spec on
    have cycle : (L.append T).IsCycle := split ▸ rc
    have lp : L.IsPath := rc.isPath_takeUntil on
    have tp : T.IsPath := cycle.isPath_of_append_right (L.not_nil_of_ne diff)
    have lengths : L.length+T.length=C.length := by
      rw [←Walk.length_append,split]
      exact C.length_rotate _ _
    by_cases large : (C.length+1)/2 ≤ L.length
    · exact ⟨L,lp,by rw [L.length_support]; omega,fun v hv =>
        contains a ha v (R.support_takeUntil_subset_support on hv)⟩
    · exact ⟨T.reverse,tp.reverse,by rw [Walk.length_support,Walk.length_reverse]; omega,fun v hv =>
        contains a ha v (R.support_dropUntil_subset_support on (by simpa using hv))⟩
  exact ⟨width,start,pair⟩
theorem path_of_cycle [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ p.length)
    (conn : 2 ≤ G.vertexConnectivity) {r : V} (C : G.Walk r r) (hc : C.IsCycle)
    (outside : ∀ v∈C.support,v∉p.support) :
    2*C.length+(C.length+1)/2+3 ≤ p.support.length := by
  classical
  let W := C.support.toFinset
  obtain ⟨width,start,pair⟩ := cycle_routes C hc
  change C.length ≤ W.card at width
  obtain ⟨_,q,hq,ql,_⟩ := start r (List.mem_toFinset.mpr C.start_mem_support)
  have mx := longest q hq
  have hq' := q.length_support
  have hp' := p.length_support
  have three := hc.three_le_length
  have ord := path_of_routes p hp longest conn W (fun v hv => outside v (List.mem_toFinset.mp hv))
    (by omega) (by omega) start pair
  omega
theorem order_of_cycle [Fintype V] [Nontrivial V] [DecidableRel G.Adj]
    (p : G.Walk x y) (hp : p.IsPath)
    (longest : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ p.length)
    (conn : 2 ≤ G.vertexConnectivity) {r : V} (C : G.Walk r r) (hc : C.IsCycle)
    (outside : ∀ v∈C.support,v∉p.support) :
    3*C.length+(C.length+1)/2+3 ≤ Fintype.card V := by
  classical
  have n := card_outside_add_path p hp C.support.toFinset (fun v hv => outside v (List.mem_toFinset.mp hv))
  have width := (cycle_routes C hc).1
  have l := path_of_cycle p hp longest conn C hc outside
  omega
end Graph189TwoExteriorLinks
end
section
open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189ThreeRegularMinimum
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
omit [DecidableEq V] [DecidableRel G.Adj] in
theorem longest_path (z : V) :
    ∃ x y : V, ∃ p : G.Walk x y, p.IsPath ∧
      ∀ {u v}, ∀ r : G.Walk u v, r.IsPath → r.length ≤ p.length := by
  classical
  let Good (n : ℕ) := ∃ x y : V, ∃ p : G.Walk x y, p.IsPath ∧ p.length = n
  have base : Good 0 := ⟨z,z,.nil,by simp,rfl⟩
  obtain ⟨x,y,p,hp,hlen⟩ := Nat.findGreatest_spec (Nat.zero_le (Fintype.card V)) base
  refine ⟨x,y,p,hp,?_⟩
  intro u v r hr
  rw [hlen]
  have card := hr.support_nodup.length_le_card
  have size := r.length_support
  exact Nat.le_findGreatest (by omega) (show Good r.length from ⟨u,v,r,hr,rfl⟩)
end Graph189ThreeRegularMinimum
end
section
open Finset SimpleGraph Graph189ExteriorGap Graph189ExteriorDegreeCycle
namespace Graph189OrdinaryRotationWindow
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
omit [Nontrivial V] in
theorem full_ports {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ p.length)
    (W D : Finset V) (lower : 4 ≤ W.card) (upper : W.card≤5) (many : 3 ≤ D.card) (sub : D⊆W)
    (outside : ∀ v∈W, v∉p.support)
    (clique : ∀ a∈D, ∀ b∈W, a≠b → G.Adj a b)
    (bound : ∀ a∈D, ∀ b, G.Adj a b → b∉W → b∈p.support)
    (high : ∀ a∈D, W.card+2 ≤ G.degree a) : 5*W.card+3 ≤ Fintype.card V := by
  classical
  let H := G.induce (W : Set V)
  have degree (a : W) : 3 ≤ H.degree a := by
    change 3≤(G.induce (W : Set V)).degree a
    rw [degree_induce_filter]
    by_cases inside : a.val∈D
    · have inc : W.erase a.val⊆(G.neighborFinset a.val).filter (fun v => v∈(W : Set V)) := by
        intro v hv
        obtain ⟨ne,mem⟩ := mem_erase.mp hv
        exact mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr (clique _ inside _ mem ne.symm),mem⟩
      have h := card_le_card inc
      rw [card_erase_of_mem a.property] at h
      omega
    · have inc : D⊆(G.neighborFinset a.val).filter (fun v => v∈(W : Set V)) := by
        intro v hv
        exact mem_filter.mpr ⟨(G.mem_neighborFinset _ _).mpr
          (clique v hv _ a.property (fun e => inside (e ▸ hv))).symm,sub hv⟩
      exact many.trans (card_le_card inc)
  have hc (a b : W) (ne : a≠b) : ∃ q : H.Walk a b, q.IsHamiltonian := by
    apply Graph189TerminalLeafClosure.prescribed_of_supergraph (G:=H) le_top _
      (Graph189TerminalLeafClosure.complete_prescribed a b ne)
    intro u v _ _
    have h1 := degree u
    have h2 := degree v
    change Fintype.card W+1 ≤ H.degree u+H.degree v
    rw [Fintype.card_coe]
    omega
  have rows (a : V) (ha : a∈D) : 3≤((univ : Finset (Fin p.support.length)).filter
      (fun i => G.Adj p.support[i.val] a)).card := by
    let R := (univ : Finset (Fin p.support.length)).filter (fun i => G.Adj p.support[i.val] a)
    let P := R.image (fun i => p.support[i.val])
    have subset : insert a (G.neighborFinset a)⊆W∪P := by
      intro v hv
      rcases mem_insert.mp hv with rfl|h
      · exact mem_union_left _ (sub ha)
      have adj := (G.mem_neighborFinset _ _).mp h
      by_cases vw : v∈W
      · exact mem_union_left _ vw
      obtain ⟨i,hi,e⟩ := List.mem_iff_getElem.mp (bound a ha v adj vw)
      exact mem_union_right _ (mem_image.mpr ⟨⟨i,hi⟩,mem_filter.mpr
        ⟨mem_univ _,by simpa only [e] using adj.symm⟩,e⟩)
    have h := (card_le_card subset).trans (card_union_le W P)
    rw [card_insert_of_notMem (by simp),G.card_neighborFinset_eq_degree] at h
    have pc : P.card ≤ R.card := card_image_le
    have d := high a ha
    change 3 ≤ R.card
    omega
  obtain ⟨M,sz,f,adj⟩ := Graph189ExteriorAttachment.marks_of_many_neighbors p D 3 many rows
  let inc : D ↪ W := ⟨fun v => ⟨v.val,sub v.property⟩,fun _ _ h => Subtype.ext (congrArg (fun t : W => (t : V)) h)⟩
  have h := exterior_hamilton_connected_matching p hp mx W (by omega) outside hc M
    (card_pos.mp (by omega)) (f.trans inc) adj
  rw [sz] at h
  exact h
theorem of_cycle_cap {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ p.length)
    {k d L : ℕ} (original : G.secondSmallestDegree=k)
    (positive : 0 < d) (rounding : 2*d ≤ k+1) (two : 2 ≤ L)
    (bounded : ∀ {r}, ∀ C : G.Walk r r, C.IsCycle → (∀ v∈C.support,v∉p.support) → C.length ≤ L)
    (minimum : ∀ v, 3 ≤ G.degree v) (quota : ∀ v, (univ.filter (fun w => G.dist v w=2)).card ≤ k)
    {highVertex : V} (omitted : highVertex∉p.support) (large : k ≤ G.degree highVertex) :
    let E := p.support.toFinsetᶜ
    let J := G.induce (E : Set V)
    (∀ a : E, k ≤ G.degree a.val → d ≤ J.degree a) ∧
    ∃ B R : Finset E, d ≤ R.card ∧ R⊆B ∧ B.card ≤ L ∧ ∀ v∈R,J.neighborFinset v⊆B := by
  classical
  let E := p.support.toFinsetᶜ
  let J := G.induce (E : Set V)
  let emb := Embedding.induce (G:=G) (E : Set V)
  have off (a : E) : a.val∉p.support := fun hit => (mem_compl.mp a.property) (List.mem_toFinset.mpr hit)
  have unique (a b : V) (aLow : G.degree a < k) (bLow : G.degree b < k) : a=b := by
    by_contra ne
    have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) a b ne
    omega
  have degree (a : E) (hi : k ≤ G.degree a.val) : d ≤ J.degree a := by
    have lower := (high_exterior_half p hp mx (off a) (quota _) hi minimum unique).2
    have eq : J.degree a=(G.neighborFinset a.val \ p.support.toFinset).card := by
      rw [degree_induce_filter]
      congr 1
      ext v
      simp [E]
    omega
  have short (a : E) (c : J.Walk a a) (hc : c.IsCycle) : c.length ≤ L := by
    have bound := bounded (c.map emb.toHom) (hc.map emb.injective) (fun v hv => by
      rw [Walk.support_map] at hv
      obtain ⟨w,_,rfl⟩ := List.mem_map.mp hv
      exact off w)
    simpa only [Walk.length_map] using bound
  let h : E := ⟨highVertex,mem_compl.mpr fun mem => omitted (List.mem_toFinset.mp mem)⟩
  obtain ⟨a,b,q,hq,maxQ⟩ := Graph189ThreeRegularMinimum.longest_path (G:=J) h
  have positive : 0 < q.length := by
    have dh := degree h large
    obtain ⟨w,e⟩ := card_pos.mp (show 0<(J.neighborFinset h).card by
      rw [J.card_neighborFinset_eq_degree]
      omega)
    have edge := (J.mem_neighborFinset _ _).mp e
    have length := maxQ edge.toWalk edge.isPath_toWalk
    rw [edge.length_toWalk] at length
    omega
  have ab : a≠b := by
    intro eq
    subst b
    have zero := (Walk.isPath_iff_nil.mp hq).length_eq_zero
    omega
  have endpoints := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) a.val b.val
    (fun e => ab (Subtype.ext e))
  have win : ∃ B R : Finset E, d ≤ R.card ∧ R⊆B ∧ B.card ≤ L ∧ ∀ v∈R,J.neighborFinset v⊆B := by
    rcases endpoints with ha|hb
    · exact Graph189RotationExterior.degree_window_at q hq maxQ two (degree a (by omega)) short
    · apply Graph189RotationExterior.degree_window_at q.reverse hq.reverse _ two (degree b (by omega)) short
      intro u v r hr
      simpa using maxQ r hr
  exact ⟨degree,win⟩
theorem of_high {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ p.length)
    (conn : 2 ≤ G.vertexConnectivity) {k d L : ℕ} (original : G.secondSmallestDegree=k)
    (positive : 0 < d) (rounding : 2*d ≤ k+1) (two : 2 ≤ L)
    (oversized : ∀ q, L < q → Fintype.card V<3*q+(q+1)/2+3)
    (minimum : ∀ v, 3 ≤ G.degree v) (quota : ∀ v, (univ.filter (fun w => G.dist v w=2)).card ≤ k)
    {highVertex : V} (omitted : highVertex∉p.support) (large : k ≤ G.degree highVertex) :
    let E := p.support.toFinsetᶜ
    let J := G.induce (E : Set V)
    (∀ a : E, k ≤ G.degree a.val → d ≤ J.degree a) ∧
    ∃ B R : Finset E, d ≤ R.card ∧ R⊆B ∧ B.card ≤ L ∧ ∀ v∈R,J.neighborFinset v⊆B := by
  apply of_cycle_cap p hp mx original positive rounding two _ minimum quota omitted large
  intro r c hc out
  have n := Graph189TwoExteriorLinks.order_of_cycle p hp mx conn c hc out
  by_contra! longer
  exact (not_lt_of_ge n) (oversized c.length longer)
end Graph189OrdinaryRotationWindow
end
section
open Finset SimpleGraph Graph189ExteriorGap Graph189ExteriorDegreeCycle
namespace Graph189SevenRotation
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem no_high {x y : V} (p : G.Walk x y) (hp : p.IsPath)
    (mx : ∀ {u v}, ∀ q : G.Walk u v, q.IsPath → q.length ≤ p.length)
    (conn : 2 ≤ G.vertexConnectivity) (order : Fintype.card V≤23)
    (original : G.secondSmallestDegree=7) (minimum : ∀ v, 3 ≤ G.degree v)
    (quota : ∀ v, (univ.filter (fun w => G.dist v w=2)).card≤7)
    {highVertex : V} (omitted : highVertex∉p.support) (large : 7 ≤ G.degree highVertex) : False := by
  classical
  let E := p.support.toFinsetᶜ
  let J := G.induce (E : Set V)
  have off (a : E) : a.val∉p.support := fun hit => (mem_compl.mp a.property) (List.mem_toFinset.mpr hit)
  have unique (a b : V) (aLow : G.degree a<7) (bLow : G.degree b<7) : a=b := by
    by_contra ne
    have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) a b ne
    omega
  obtain ⟨degree,B,R,rank,sub,width,neighbor⟩ := Graph189OrdinaryRotationWindow.of_high p hp mx conn
    (d:=4) (L:=5) original (by decide) (by decide) (by decide) (by omega) minimum quota omitted large
  let D := R.filter (fun v => 7 ≤ G.degree v.val)
  have few : (R \ D).card≤1 := by
    apply card_le_one.mpr
    intro u hu v hv
    apply Subtype.ext
    apply unique
    · by_contra! high
      exact (mem_sdiff.mp hu).2 (mem_filter.mpr ⟨(mem_sdiff.mp hu).1,high⟩)
    · by_contra! high
      exact (mem_sdiff.mp hv).2 (mem_filter.mpr ⟨(mem_sdiff.mp hv).1,high⟩)
  have split := card_sdiff_add_card_eq_card (show D⊆R from filter_subset _ _)
  have many : 3 ≤ D.card := by omega
  have full (a : E) (ha : a∈D) : J.neighborFinset a=B.erase a ∧ B.card=5 := by
    have ar := (mem_filter.mp ha).1
    have degreeA : 4 ≤ J.degree a := degree a (mem_filter.mp ha).2
    have inc : J.neighborFinset a⊆B.erase a := by
      intro v hv
      exact mem_erase.mpr ⟨((J.mem_neighborFinset _ _).mp hv).ne.symm,neighbor a ar hv⟩
    have size := card_le_card inc
    rw [J.card_neighborFinset_eq_degree,card_erase_of_mem (sub ar)] at size
    exact ⟨eq_of_subset_of_card_le inc (by
      rw [J.card_neighborFinset_eq_degree,card_erase_of_mem (sub ar)]
      omega),by omega⟩
  obtain ⟨d,hd⟩ := card_pos.mp (show 0 < D.card by omega)
  let f : E ↪ V := ⟨Subtype.val,Subtype.val_injective⟩
  have ord := Graph189OrdinaryRotationWindow.full_ports p hp mx (B.map f) (D.map f)
    (by rw [card_map,(full d hd).2]; decide) (by rw [card_map,(full d hd).2])
    (by rwa [card_map]) (map_subset_map.mpr ((filter_subset _ _).trans sub))
    (fun v hv => by obtain ⟨v,_,rfl⟩ := mem_map.mp hv; exact off v)
    (by
      intro a ha b hb diff
      obtain ⟨u,hu,rfl⟩ := mem_map.mp ha
      obtain ⟨v,hv,rfl⟩ := mem_map.mp hb
      apply (J.mem_neighborFinset u v).mp
      rw [(full u hu).1]
      exact mem_erase.mpr ⟨fun eq => diff (congrArg f eq.symm),hv⟩)
    (by
      intro a ha v step no
      obtain ⟨u,hu,rfl⟩ := mem_map.mp ha
      by_contra offV
      let w : E := ⟨v,mem_compl.mpr fun mem => offV (List.mem_toFinset.mp mem)⟩
      have e : J.Adj u w := step
      exact no (mem_map.mpr ⟨w,neighbor u (mem_filter.mp hu).1 ((J.mem_neighborFinset _ _).mpr e),rfl⟩))
    (by
      intro a ha
      obtain ⟨u,hu,rfl⟩ := mem_map.mp ha
      rw [card_map,(full d hd).2]
      exact (mem_filter.mp hu).2)
  rw [card_map,(full d hd).2] at ord
  omega
end Graph189SevenRotation
end
section
open SimpleGraph Finset Graph189ExteriorGap
namespace Graph189SevenProtected
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
theorem traceable (z : V) (low : G.degree z < G.secondSmallestDegree) (three : 3 ≤ G.degree z)
    (seven : G.secondSmallestDegree=7) (order : Fintype.card V≤23)
    (cap : ∀ v, G.distEven v ≤ G.secondSmallestDegree+1)
    {u v : {t : V | t≠z}} (r : (G.induce {t : V | t≠z}).Walk u v) (hr : r.IsHamiltonian) :
    ∃ a b, ∃ q : G.Walk a b, q.IsHamiltonian := by
  classical
  obtain ⟨a,b,p,hp,t,atZ,mx⟩ := exists_longest_through G z
  let E := p.support.toFinsetᶜ
  by_cases empty : E=∅
  · refine ⟨a,b,p,hp.isHamiltonian_iff.mpr ?_⟩
    intro w
    by_contra no
    have mem : w∈E := mem_compl.mpr (fun h => no (List.mem_toFinset.mp h))
    simp [empty] at mem
  have size := protected_size_of_traceable_deletion z (by omega) r hr p hp mx
  change 1+G.degree z+(G.degree z+1)*E.card ≤ _ at size
  have scale := Nat.mul_le_mul_right E.card (by omega : 4 ≤ G.degree z+1)
  have small : E.card≤4 := by omega
  have indexed {x y} (q : G.Walk x y) (hq : q.IsPath) (mem : p.support[t.val]∈q.support) :
      q.length ≤ p.length := mx q hq (atZ ▸ mem)
  obtain ⟨enough,bound,_⟩ := protected_contact_witness p hp t indexed (atZ ▸ low) cap
    (nonempty_iff_ne_empty.mpr empty) (s:=3) (by decide) (by omega) (by change E.card+3 ≤ _; omega)
  change G.secondSmallestDegree+1-E.card ≤ E.card at enough
  change (G.secondSmallestDegree+1-E.card+1)*E.card + (G.secondSmallestDegree+1-E.card) ≤ _ at bound
  have exactSize : E.card=4 := by omega
  rw [exactSize,seven] at bound
  omega
end Graph189SevenProtected
end
section
open SimpleGraph Finset
namespace Graph189ModerateSeven
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem seven_two_connected (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (conn : 2 ≤ G.vertexConnectivity) (seven : G.secondSmallestDegree=7) (small : Fintype.card V≤23) :
    ∃ a b, ∃ p : G.Walk a b,p.IsHamiltonian := by
  classical
  have large : 7 ≤ G.secondSmallestDegree := seven.ge
  have point (v : V) : G.distEven v≤1+G.secondSmallestDegree :=
    (le_max' _ _ (mem_image_of_mem _ (mem_univ v))).trans cap
  have localCap (v : V) : G.distEven v ≤ G.secondSmallestDegree+1 := by
    simpa only [Nat.add_comm] using point v
  obtain ⟨z,hz⟩ := G.exists_minimal_degree_vertex
  have lower := Graph189CutSides.connectivity_le_degree (G:=G) z
  by_cases dz : G.degree z=2
  · exact Graph189DegreeTwoOriginal.traceable hc cap conn z dz large
  have min (v : V) : 3 ≤ G.degree v := by have := G.minDegree_le_degree v; omega
  have quota (v : V) : (univ.filter (fun w => G.dist v w=2)).card≤7 := by
    let D := univ.filter (fun w => G.dist v w=2)
    have sub : insert v D⊆univ.filter (fun w => Even (G.dist v w)) := by
      intro w hw
      rcases mem_insert.mp hw with rfl|h
      · simp
      · exact mem_filter.mpr ⟨mem_univ _,by simp [(mem_filter.mp h).2]⟩
    have no : v∉D := by simp [D]
    have bd := card_le_card sub
    rw [card_insert_of_notMem no] at bd
    change D.card+1 ≤ G.distEven v at bd
    have lim := point v
    change D.card≤7
    omega
  obtain ⟨a,b,p,hp,mx⟩ := Graph189ThreeRegularMinimum.longest_path (G:=G) z
  let E := p.support.toFinsetᶜ
  have low (v : V) (hv : v∈E) : G.degree v<7 := by
    by_contra! high
    exact Graph189SevenRotation.no_high p hp mx conn small seven min quota (by simpa [E] using hv) high
  have few : E.card≤1 := by
    apply card_le_one.mpr
    intro u hu v hv
    by_contra ne
    have pair := OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1.degree_pair (G:=G) u v ne
    have l1 := low u hu
    have l2 := low v hv
    omega
  have pop := card_add_card_compl p.support.toFinset
  rw [List.toFinset_card_of_nodup hp.support_nodup] at pop
  change p.support.length+E.card=Fintype.card V at pop
  by_contra nontrace
  obtain ⟨w,lw,_,_,r,hr⟩ := Graph189ExteriorDegreeCycle.near_longest_has_hamiltonian_low_deletion
    p hp mx (by omega) nontrace (by omega) localCap min
  exact nontrace (Graph189SevenProtected.traceable w lw (min w) seven small localCap r hr)
end Graph189ModerateSeven
end
section
open SimpleGraph Finset
open OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R1
namespace Graph189ModerateForDesk
variable {V : Type*} [Fintype V] [DecidableEq V] [Nontrivial V] {G : SimpleGraph V} [DecidableRel G.Adj]
theorem seven_up (hc : G.Connected) (cap : (univ.image (distEven G)).max' (by simp)≤1+G.secondSmallestDegree)
    (conn : 2 ≤ G.vertexConnectivity) (large : 7 ≤ G.secondSmallestDegree)
    (upper : Fintype.card V≤3*G.secondSmallestDegree+2) :
    ∃a b,∃r : G.Walk a b,r.IsHamiltonian := by
  by_cases eight : 8 ≤ G.secondSmallestDegree
  · exact Graph189ModerateEight.traceable_moderate hc cap eight conn upper
  exact Graph189ModerateSeven.seven_two_connected hc cap conn (by omega) (by omega)
end Graph189ModerateForDesk
end
section
open SimpleGraph Finset
namespace Graph189ModerateSplitProofs
private theorem maximum {V : Type} [Fintype V] [DecidableEq V] [Nontrivial V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (point : ∀ x, G.distEven x ≤ 1+G.secondSmallestDegree) :
    (univ.image (distEven G)).max' (by simp) ≤ 1+G.secondSmallestDegree := by
  classical
  apply max'_le
  intro _ hw
  obtain ⟨w,_,rfl⟩ := mem_image.mp hw
  exact point w
theorem seven : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1_H1_R1.H4 := by
  intro V _ _ _ G _ hc point lower uncut upper _wide degree
  have conn := Graph189ParentConnectivity.two_of_deletions hc (by omega) uncut
  exact Graph189ModerateForDesk.seven_up hc (maximum G point) conn degree upper
end Graph189ModerateSplitProofs
end
theorem OMA.solution : OMA.R_WrittenOnTheWallII_GraphConjecture189_conjecture189_R2_H2_R1_H1_R1.H4 := Graph189ModerateSplitProofs.seven
