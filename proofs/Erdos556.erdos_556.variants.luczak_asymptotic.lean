import FormalConjectures.ErdosProblems.«556»
import Mathlib

/-!
Łuczak's asymptotic bound for three-colour cycle Ramsey numbers.

The odd branch adapts the cube profiles and graph decomposition from Hanan
Beer (@hananzlt), PR 7648, based on plby/lean-proofs at
8822f7ddef30fadbd92e1c6ab4ed897af356af5e and the work of Kohayakawa,
Simonovits and Skokan. Bondy–Chvátal credits Shuhao Song; Menger credits
the Lean-Proofs Authors. The original helper names are mapped in PR 7648.
Here the decomposition is extended to seven times the cycle length. Rescaling
a limiting profile to mass four gives the asymptotic odd upper bound.
The even branch reuses Devin Robison's merged proof (PR 4480) and its
contributions credited below to @green-notes and @MrSeizy.
-/
open Classical renaming choose_spec → clCS
open Finset renaming card → fsCard
open Finset renaming card_biUnion_le → fsCBL
open Finset renaming card_insert_of_notMem → fsCION
open Finset renaming card_le_card → fsCLC
open Finset renaming card_le_univ → fsCLU
open Finset renaming card_pos → fsCP
open Finset renaming card_union_le → fsCUL
open Finset renaming card_univ → fsCU
open Finset renaming disjoint_left → fsDL
open Finset renaming disjoint_of_subset_right → fsDOSR
open Finset renaming disjoint_right → fsDR
open Finset renaming erase_subset → fsES
open Finset renaming inter_subset_right → fsISR
open Finset renaming mem_biUnion → fsMB
open Finset renaming mem_erase → fsME
open Finset renaming mem_filter → fsMF
open Finset renaming mem_image → fsMI
open Finset renaming mem_insert → fsMI2
open Finset renaming mem_insert_of_mem → fsMIOM
open Finset renaming mem_insert_self → fsMIS
open Finset renaming mem_inter → fsMI3
open Finset renaming mem_of_mem_erase → fsMOME
open Finset renaming mem_offDiag → fsMO
open Finset renaming mem_product → fsMP
open Finset renaming mem_range → fsMR
open Finset renaming mem_sdiff → fsMS
open Finset renaming mem_singleton → fsMS2
open Finset renaming mem_union → fsMU
open Finset renaming mem_union_left → fsMUL
open Finset renaming mem_union_right → fsMUR
open Finset renaming mem_univ → fsMU2
open Finset renaming mul_sum → fsMS3
open Finset renaming ne_of_mem_erase → fsNOME
open Finset renaming notMem_empty → fsNE
open Finset renaming range → fsRange
open Finset renaming sum_congr → fsSC
open Finset renaming sum_le_sum → fsSLS
open Finset renaming univ → fsUniv
open Fintype renaming card → ftCard
open Fintype renaming card_coe → ftCC
open Fintype renaming card_congr → ftCC2
open Fintype renaming card_fin → ftCF
open Fintype renaming card_le_of_injective → ftCLOI
open Fintype renaming card_pos_iff → ftCPI
open Fintype renaming card_prod → ftCP
open Fintype renaming ofFinite → ftOfFin
open Fintype renaming one_lt_card_iff_nontrivial → ftOLCIN
open Fintype renaming sum_equiv → ftSE
open Function.Embedding renaming subtype → fnSubty
open List renaming cons_append → lsCA
open List renaming disjoint_left → lsDL
open List renaming filter_cons → lsFC
open List renaming flatMap_cons → lsFC2
open List renaming getElem_cons_succ → lsGCS
open List renaming getElem_cons_zero → lsGCZ
open List renaming getElem_mem → lsGM
open List renaming getElem_of_mem → lsGOM
open List renaming getLast_cons → lsGC
open List renaming getLast_eq_getElem → lsGEG
open List renaming head_append_of_ne_nil → lsHAONN
open List renaming head_eq_getElem → lsHEG
open List.IsChain renaming cons_cons → lsCC
open List.IsChain renaming singleton → lsSingl
open List renaming isChain_iff_getElem → lsIIG
open List renaming length_cons → lsLC
open List renaming length_take → lsLT
open List renaming mem_append → lsMA
open List renaming mem_append_left → lsMAL
open List renaming mem_append_right → lsMAR
open List renaming mem_cons → lsMC
open List renaming mem_cons_of_mem → lsMCOM
open List renaming mem_cons_self → lsMCS
open List renaming mem_filter → lsMF
open List renaming mem_flatMap → lsMF2
open List renaming mem_map → lsMM
open List renaming mem_of_mem_tail → lsMOMT
open List renaming mem_of_mem_take → lsMOMT2
open List renaming mem_reverse → lsMR
open List renaming mem_singleton → lsMS
open List renaming mem_toFinset → lsMT
open List renaming ne_nil_of_length_pos → lsNNOLP
open List renaming nil_append → lsNA
open List renaming nodup_append → lsNA2
open List renaming nodup_cons → lsNC
open List renaming not_mem_nil → lsNMN
open List.Perm renaming mem_iff → lsMI
open List renaming toFinset_append → lsTA
open List renaming toFinset_card_le → lsTCL
open List renaming toFinset_card_of_nodup → lsTCON
open List renaming toFinset_cons → lsTC
open List renaming toFinset_nil → lsTN
open Nat renaming add_assoc → natAA
open Nat renaming add_le_add_right → natALAR
open Nat renaming add_sub_of_le → natASOL
open Nat renaming card → natCard
open Nat renaming card_eq_fintype_card → natCEFC
open Nat renaming cast_add → natCA
open Nat renaming cast_le → natCL
open Nat renaming cast_mul → natCM
open Nat renaming cast_nonneg → natCN
open Nat renaming cast_ofNat → natCO
open Nat renaming cast_zero → natCZ
open Nat renaming div_add_mod → natDAM
open Nat renaming div_mul_le_self → natDMLS
open Nat renaming even_iff → natEI
open Nat renaming le_ceil → natLC
open Nat renaming le_div_iff_mul_le → natLDIML
open Nat renaming lt_succ_of_le → natLSOL
open Nat renaming mod_eq_of_lt → natMEOL
open Nat renaming mod_lt → natML
open Nat renaming mul_comm → natMC
open Nat renaming mul_le_mul_left → natMLML
open Nat renaming mul_le_mul_right → natMLMR
open Nat renaming odd_iff → natOI
open Nat renaming strong_induction_on → natSIO
open Nat renaming sub_add_cancel → natSAC
open Nat renaming sub_le_sub_right → natSLSR
open Or renaming inl → orInl
open Or renaming inr → orInr
open Set renaming mem_compl_iff → stMCI
open Set renaming mem_range_self → stMRS
open Set renaming mem_singleton_iff → stMSI
open Set renaming mem_toFinset → stMT
open Set renaming ncard_coe_finset → stNCF
open SimpleGraph renaming disjoint_edgeFinset → sgDE
open SimpleGraph renaming edgeDensity_comm → sgEC
open SimpleGraph renaming edgeDensity_def → sgED
open SimpleGraph.Embedding renaming induce → sgInduce
open SimpleGraph renaming mem_neighborFinset → sgMN
open SimpleGraph renaming mk_mem_interedges_iff → sgMMII
open SimpleGraph.Walk renaming mem_support_iff → sgMSI
open SimpleGraph.Walk renaming mem_support_rotate_iff → sgMSRI
open SimpleGraph.Walk renaming not_nil_iff_lt_length → sgNNILL
open SimpleGraph.Walk renaming not_nil_of_ne → sgNNON
open SimpleGraph.Walk renaming support_reverse → sgSR
open Subtype renaming ext → subExt
open Subtype renaming val → subVal
open Subtype renaming val_injective → subVI
open SimpleGraph.Walk renaming cons → wkCons
open SimpleGraph.Walk renaming cons_isPath_iff → wkCII
open SimpleGraph.Walk renaming drop_getVert → wkDG
open SimpleGraph.Walk renaming drop_length → wkDL
open SimpleGraph.Walk renaming length_append → wkLA
open SimpleGraph.Walk renaming length_concat → wkLC
open SimpleGraph.Walk renaming length_cons → wkLC2
open SimpleGraph.Walk renaming length_map → wkLM
open SimpleGraph.Walk renaming length_reverse → wkLR
open SimpleGraph.Walk renaming length_support → wkLS
open SimpleGraph.Walk renaming length_tail → wkLT
open SimpleGraph.Walk renaming mem_support_append_iff → wkMSAI
open SimpleGraph.Walk renaming mem_support_iff_exists_getVert → wkMSIEG
open SimpleGraph.Walk renaming not_nil_of_ne → wkNNON
open SimpleGraph.Walk renaming support_concat → wkSC
open SimpleGraph.Walk renaming support_cons → wkSC2
open SimpleGraph.Walk renaming support_map → wkSM
open SimpleGraph.Walk renaming support_reverse → wkSR
open SimpleGraph.Walk renaming take_length → wkTL

namespace Erdos556
open SimpleGraph
open scoped SimpleGraph
structure q4 (V:Type*) where
  colour:V → V → Fin 3
  symm: ∀ u v,colour u v=colour v u
def q4.graph {V:Type*} (c:q4 V) (i:Fin 3) :
    SimpleGraph V where
  Adj u v:=u ≠ v ∧ c.colour u v=i
  symm:= ⟨by
    intro u v h
    exact ⟨h.1.symm,(c.symm v u).trans h.2⟩⟩
  loopless:= ⟨by simp⟩
@[simp] theorem q4.e4 {V:Type*} (c:q4 V)
    (i:Fin 3) (u v :V) :
    (c.graph i).Adj u v ↔ u ≠ v ∧ c.colour u v=i:=Iff.rfl
def q4.comap {V W :Type*} (c:q4 V) (f:W → V) :
    q4 W where
  colour u v:=c.colour (f u) (f v)
  symm u v:=c.symm (f u) (f v)
theorem q4.tY {V W :Type*} (c:q4 V)
    (f:W ↪ V) (i:Fin 3) :
    (c.comap f).graph i = (c.graph i).comap f :=by
  ext u v
  simp only [e4,comap,SimpleGraph.comap_adj]
  exact and_congr_left fun _ => f.injective.ne_iff.symm
def rr (n m :ℕ) : Prop:=
  ∀ c :q4 (Fin m),∃ i:Fin 3,cycleGraph n ⊑ c.graph i
noncomputable def sS (n:ℕ) : ℕ:=
  sInf {m:ℕ | rr n m}
theorem rr.mono {n a b:ℕ} (h:rr n a) (hab:a ≤ b) :
    rr n b:=by
  intro c
  let f :Fin a ↪ Fin b :=Fin.castLEEmb hab
  obtain ⟨i,hi⟩ :=h (c.comap f)
  refine ⟨i,?_⟩
  rw [c.tY f i] at hi
  exact hi.trans (SimpleGraph.Embedding.comap f (c.graph i)).isContained
end Erdos556
namespace Erdos556
open Finset
abbrev wz:=Fin 3 → Bool
abbrev q1:=Fin 3 → Option Bool
def q0 (p:q1) : Finset wz:=
  univ.filter (fun v => ∀ i,p i=none ∨ p i =some (v i))
def q3 (p:q1) : ℕ:=
  (univ.filter (fun i => p i=none)).card
def cubeFace (i:Fin 3) (b:Bool) : q1:=
  fun j => if j =i then some b else none
def qF:q1:=fun _ => none
theorem sM (p:q1) : q3 p ≤ 3 :=by
  have h :=card_le_univ (univ.filter (fun i :Fin 3 => p i=none))
  simpa only [q3,ftCF] using h
theorem qU: ∀ p:q1,
    (q0 p).card=2^q3 p :=by
  decide
theorem r4: ∀ (i:Fin 3) (b:Bool),q3 (cubeFace i b) = 2:=by
  decide
theorem zx:q3 qF=3:=by decide
theorem sz: ∀ p:q1,
    q3 p =3 ↔ p=qF:=by
  decide
theorem u1: ∀ p:q1,
    q3 p =2 ↔ ∃ (i:Fin 3) (b:Bool),p=cubeFace i b:=by
  decide
end Erdos556
namespace Erdos556
theorem ru: ∀ p q:q1,
    q3 p =1 → q3 q =1 → p ≠ q →
    ((q0 p) ∩ (q0 q)).card ≠ 1 →
    Disjoint (q0 p) (q0 q) :=by
  decide
theorem ui: ∀ (i j :Fin 3) (b c :Bool),
    Disjoint (q0 (cubeFace i b)) (q0 (cubeFace j c)) ↔
      i=j ∧ b ≠ c:=by
  decide
end Erdos556
namespace Erdos556
open Finset
structure q6 (w:q1 → ℝ) : Prop where
  nonneg: ∀ p,0 ≤ w p
  sum_four: ∑ p,w p=4
  vertex_zero: ∀ p,q3 p =0 → w p=0
  edge_le_one: ∀ p,q3 p =1 → w p ≤ 1
  compatible: ∀ p q,0 < w p → 0 < w q →
    (q0 p ∩ q0 q).card ≠ 1
def qb (p q :q1) : ℝ:=
  if Disjoint (q0 p) (q0 q) then 0 else 1
def qd (w:q1 → ℝ) : ℝ:=
  (∑ p,∑ q,qb p q*w p*w q) - ∑ p,(q3 p :ℝ) * w p
def qm (w:q1 → ℝ) (p:q1) : ℝ:=
  2* (∑ q,qb p q*w q) - q3 p
theorem sm (p q :q1) : qb p q=qb q p:=by
  simp only [qb,disjoint_comm]
theorem vU (p:q1) : qb p p=1:=by
  have hcard:0 < (q0 p).card:=by rw [qU];positivity
  have hne: ¬ Disjoint (q0 p) (q0 p) :=by
    simpa only [disjoint_self,Finset.bot_eq_empty,← card_eq_zero] using Nat.ne_of_gt hcard
  simp only [qb,if_neg hne]
theorem vh (E:Finset q1) (S:Finset wz)
    (hdim: ∀ p ∈ E,q3 p =1)
    (hdisj: (E:Set q1).Pairwise (fun p q=> Disjoint (q0 p)
      (q0 q)))
    (hsub: ∀ p ∈ E,q0 p ⊆ S) : 2*E.card ≤ S.card:=by
  have hsum: (∑ p ∈ E,(q0 p).card) = 2*E.card:=by
    calc
      (∑ p ∈ E,(q0 p).card) = ∑ _p ∈ E,2:=by
        apply sum_congr rfl
        intro p hp
        rw [qU,hdim p hp]
        norm_num
      _=2*E.card:=by simp [natMC]
  rw [← hsum,← card_biUnion hdisj]
  apply card_le_card
  intro v hv
  obtain ⟨p,hp,hvp⟩ :=mem_biUnion.mp hv
  exact hsub p hp hvp
open scoped Classical in
noncomputable def ql (w:q1 → ℝ) : Finset q1:=
  univ.filter (fun p => q3 p =1 ∧ 0 < w p)
theorem q6.s0 {w:q1 → ℝ} (hw:q6 w) :
    (ql w :Set q1).Pairwise
      (fun p q=> Disjoint (q0 p) (q0 q)) :=by
  intro p hp q hq hpq
  obtain ⟨_,hpdim,hpw⟩ :=mem_filter.mp hp
  obtain ⟨_,hqdim,hqw⟩ :=mem_filter.mp hq
  exact ru p q hpdim hqdim hpq (hw.compatible p q hpw hqw)
theorem q6.vl {w:q1 → ℝ} (hw:q6 w) :
    (ql w).card ≤ 4:=by
  have h :=vh (ql w) univ
    (fun p hp=> (mem_filter.mp hp).2.1) hw.s0 (fun _ _=> subset_univ _)
  have hcard: (univ:Finset wz).card=8:=by decide
  rw [hcard] at h
  omega
end Erdos556
namespace Erdos556
open Finset
theorem vn {V P R:Type*} [Fintype V] [Fintype P] [DecidableEq P]
    [Semiring R] (label:V → P) (f:P → R) :
    (∑ v,f (label v)) = ∑ p,((univ.filter (fun v => label v =p)).card:R) * f p :=by
  classical
  have h :=sum_fiberwise' (univ:Finset V) label f
  simpa only [sum_const,nsmul_eq_mul] using h.symm
theorem aE {V P :Type*} [Fintype V] [Fintype P] [DecidableEq P]
    (label:V → P) : (∑ p,(univ.filter (fun v => label v =p)).card) = ftCard V :=by
  simpa using (vn label (fun _ => (1:ℕ))).symm
theorem yG {V P R:Type*} [Fintype V] [Fintype P] [DecidableEq P]
    [Semiring R] (label:V → P) (f:P → P → R) :
    (∑ u,∑ v,f (label u) (label v)) =
      ∑ p,∑ q,((univ.filter (fun v => label v =p)).card:R) *
        ((univ.filter (fun v => label v =q)).card:R) * f p q:=by
  classical
  calc
    _= ∑ u,∑ q,((univ.filter (fun v => label v =q)).card:R) * f (label u) q :=by
      apply sum_congr rfl
      intro u _
      exact vn label (f (label u))
    _= ∑ p,((univ.filter (fun v => label v =p)).card:R) *
        (∑ q,((univ.filter (fun v => label v =q)).card:R) * f p q) :=
      vn label (fun p => ∑ q,((univ.filter (fun v => label v =q)).card:R) * f
        p q)
    _=_:=by simp only [mul_sum,mul_assoc]
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem q7 {V:Type*} (G:SimpleGraph V) [Fintype G.edgeSet] :
    G.edgeFinset.card=natCard G.edgeSet:=
  G.card_edgeSet.symm.trans natCEFC.symm
theorem tf {V W :Type*} [Fintype V]
    [DecidableEq W] (G:SimpleGraph V) [DecidableRel G.Adj]
    (f:V ↪ W) (A:Finset W) :
    ((G.map f).induce (A:Set W)).edgeFinset.card=
      (G.induce ((univ.filter (fun v => f v ∈ A) : Finset V) : Set V)).edgeFinset.card:=by
  classical
  let B :=univ.filter (fun v :V=> f v ∈ A)
  let g : (B:Set V) ↪ (A:Set W) :=
    { toFun:=fun v => ⟨f v.val,(mem_filter.mp v.property).2⟩
      inj':=fun u v h => subExt (f.injective (congrArg subVal h))}
  have e : (G.map f).induce (A:Set W) ≃g (G.induce (B:Set V)).map g :=
    { toEquiv:=Equiv.refl _
      map_rel_iff':=by
        intro u v
        constructor
        · rintro ⟨hne,a,b,hab,ha,hb⟩
          change (G.map f).Adj u.val v.val
          refine ⟨fun h => hne (subExt h),a.val,b.val,hab,?_,?_⟩
          · exact congrArg subVal ha
          · exact congrArg subVal hb
        · intro huv
          change (G.map f).Adj u.val v.val at huv
          obtain ⟨hne,a,b,hab,ha,hb⟩ :=huv
          have haB:a ∈ B:=mem_filter.mpr ⟨mem_univ _,ha ▸ u.property⟩
          have hbB:b ∈ B:=mem_filter.mpr ⟨mem_univ _,hb ▸ v.property⟩
          refine ⟨fun h => hne (congrArg subVal h),⟨a,haB⟩,⟨b,hbB⟩,hab,?_,?_⟩
          · exact subExt ha
          · exact subExt hb}
  exact e.card_edgeFinset_eq.trans (card_edgeFinset_map g (G.induce (B:Set V)))
theorem t1 {V W :Type*} [Fintype V]
    [DecidableEq W] (f:V ↪ W) (A:Finset W) :
    (univ.filter (fun v => f v ∈ A)).card ≤ A.card:=by
  classical
  let B :=univ.filter (fun v :V=> f v ∈ A)
  let g : (B:Set V) ↪ (A:Set W) :=
    { toFun:=fun v => ⟨f v.val,(mem_filter.mp v.property).2⟩
      inj':=fun u v h => subExt (f.injective (congrArg subVal h))}
  have h :=ftCLOI g g.injective
  have hcardB:ftCard (B:Set V) = B.card:=by
    calc
      ftCard (B:Set V) = (B:Set V).ncard:=natCEFC.symm
      _=B.card:=stNCF B
  have hcardA:ftCard (A:Set W) = A.card:=by
    calc
      ftCard (A:Set W) = (A:Set W).ncard:=natCEFC.symm
      _=A.card:=stNCF A
  rw [hcardB,hcardA] at h
  exact h
theorem x2 {V W :Type*} [Fintype V]
    [DecidableEq W] (G:SimpleGraph V) [DecidableRel G.Adj]
    (f:V ↪ W) (D:ℝ) (hD:0 ≤ D)
    (h: ∀ S:Finset V,((G.induce (S:Set V)).edgeFinset.card:ℝ) ≤ D*S.card) :
    ∀ A :Finset W,(((G.map f).induce (A:Set W)).edgeFinset.card:ℝ) ≤ D*A.card:=by
  classical
  intro A
  rw [tf G f A]
  apply (h _).trans
  apply mul_le_mul_of_nonneg_left _ hD
  exact_mod_cast t1 f A
theorem ac {V W :Type*}
    (G:SimpleGraph V) (f:V ↪ W) (S:Finset V)
    (h: ∀ a b,G.Adj a b → a ∈ S ∧ b ∈ S) :
    ∀ a b,(G.map f).Adj a b → a ∈ S.map f ∧ b ∈ S.map f :=by
  classical
  rintro a b ⟨_,u,v,huv,rfl,rfl⟩
  exact ⟨mem_map.mpr ⟨u,(h u v huv).1,rfl⟩,mem_map.mpr ⟨v,(h u v huv).2,rfl⟩⟩
theorem tW {V W :Type*}
    (G:SimpleGraph V) (f:V ↪ W) (S:Finset V)
    (h: ∀ a b,G.Adj a b → a ∉ S ∧ b ∉ S) :
    ∀ a b,(G.map f).Adj a b → a ∉ S.map f ∧ b ∉ S.map f :=by
  classical
  rintro a b ⟨_,u,v,huv,rfl,rfl⟩
  have hoff (x:V) (hx:x ∉ S) : f x ∉ S.map f :=by
    intro hxmem
    obtain ⟨y,hy,hyx⟩ :=mem_map.mp hxmem
    exact hx ((f.injective hyx) ▸ hy)
  exact ⟨hoff u (h u v huv).1,hoff v (h u v huv).2⟩
end Erdos556
namespace Erdos556
open SimpleGraph Finset
def qJ {V:Type*} (label:V → q1) : SimpleGraph V where
  Adj u v:=Disjoint (q0 (label u)) (q0 (label v))
  symm:= ⟨fun _ _ h => h.symm⟩
  loopless:= ⟨by
    intro v h
    have he:q0 (label v) = ∅ :=by
      simpa only [disjoint_self,Finset.bot_eq_empty] using h
    have hp:0 < (q0 (label v)).card:=by rw [qU];positivity
    rw [he,card_empty] at hp
    omega⟩
def qO (w:q1 → ℝ) : ℝ:=
  ∑ p,∑ q,if Disjoint (q0 p) (q0 q) then w p*w q else 0
theorem sb {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] :
    2* (natCard G.edgeSet:ℝ) = ∑ u,∑ v,if G.Adj u v then (1:ℝ) else 0 :=by
  classical
  have hdegree (u:V) : G.degree u = ∑ v,if G.Adj u v then (1:ℕ) else 0 :=by
    rw [sum_boole,← card_neighborFinset_eq_degree]
    congr 1
    ext v
    simp
  have h :=G.sum_degrees_eq_twice_card_edges
  simp only [hdegree,q7] at h
  exact_mod_cast h.symm
theorem sY {V:Type*} [Fintype V]
    (label:V → q1) :
    2* (natCard (qJ label).edgeSet:ℝ) =
      qO (fun p => ((univ.filter (fun v => label v =p)).card:ℝ)) :=by
  classical
  rw [sb]
  have hadj: (∑ u,∑ v,if (qJ label).Adj u v then (1:ℝ) else 0) =
      ∑ u,∑ v,if Disjoint (q0 (label u)) (q0 (label v)) then (1:ℝ)
        else 0 :=by
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro v _
    by_cases h :Disjoint (q0 (label u)) (q0 (label v)) <;>
      simp [qJ,h]
  rw [hadj]
  rw [yG label (fun p q=>
    if Disjoint (q0 p) (q0 q) then (1:ℝ) else 0)]
  unfold qO
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  split_ifs <;> simp
theorem zv (w:q1 → ℝ) :
    qd w = (∑ p,w p) ^ 2-qO w -
      ∑ p,(q3 p :ℝ) * w p :=by
  have h : (∑ p,∑ q,qb p q*w p*w q) + qO w = (∑ p,w p) ^ 2:=by
    calc
      _= ∑ p,∑ q,(qb p q*w p*w q+
          if Disjoint (q0 p) (q0 q) then w p*w q else 0) :=by
        simp only [qO,sum_add_distrib]
      _= ∑ p,∑ q,w p*w q:=by
        apply sum_congr rfl
        intro p _
        apply sum_congr rfl
        intro q _
        unfold qb
        split_ifs <;> simp
      _=_:=by
        simp only [pow_two,sum_mul,mul_sum]
        exact sum_comm
  unfold qd
  linarith
end Erdos556
namespace Erdos556
open SimpleGraph
theorem rq {V:Type*} {G:SimpleGraph V}
    {u v :V} (p:G.Walk u v) (hp:p.IsPath) (S:Set V) (hv:v ∈ S) :
    ∃ w ∈ S,∃ q:G.Walk u w,q.IsPath ∧ q.length ≤ p.length ∧
      q.support ⊆ p.support ∧ ∀ x ∈ q.support,x ∈ S → x=w:=by
  classical
  let P (m:ℕ) : Prop:= ∃ w ∈ S,∃ q:G.Walk u w,
    q.IsPath ∧ q.support ⊆ p.support ∧ q.length=m
  have hex: ∃ m,P m:= ⟨p.length,v,hv,p,hp,List.Subset.refl _,rfl⟩
  obtain ⟨w,hw,q,hq,hsub,hlen⟩ :=Nat.find_spec hex
  have hmin {z:V} (hz:z ∈ S) (r:G.Walk u z) (hr:r.IsPath)
      (hrs:r.support ⊆ p.support) : q.length ≤ r.length:=by
    rw [hlen]
    exact Nat.find_min' hex ⟨z,hz,r,hr,hrs,rfl⟩
  refine ⟨w,hw,q,hq,hmin hv p hp (List.Subset.refl _),hsub,?_⟩
  intro x hx hxS
  by_contra hxw
  have hlt:=q.length_takeUntil_lt_length hx hxw
  have hle:=hmin hxS (q.takeUntil x hx) (hq.takeUntil hx)
    (fun _ hz=> hsub (q.support_takeUntil_subset_support hx hz))
  omega
theorem qr {V:Type*} {G:SimpleGraph V}
    {u v w:V} (p:G.Walk u v) (q:G.Walk v w)
    (hp:p.IsPath) (hq:q.IsPath)
    (hinter: ∀ x ∈ p.support,x ∈ q.support → x=v) :
    (p.append q).IsPath:=by
  induction p with
  | nil=> simpa using hq
  | @cons u z v huz p ih=>
      have hp':=hp.of_cons
      have hu:u ∉ p.support:= (wkCII huz p).mp hp |>.2
      have huv:u ≠ v:=fun h => hu (h ▸ p.end_mem_support)
      have huq:u ∉ q.support:=fun h => huv (hinter u (by simp) h)
      have hi: ∀ x ∈ p.support,x ∈ q.support → x=v:=
        fun x hx hxq=> hinter x (by simp [hx]) hxq
      exact (ih q hp' hq hi).cons (by
        intro hx
        rcases (wkMSAI _ _).mp hx with hx | hx
        · exact hu hx
        · exact huq hx)
end Erdos556
namespace Erdos556
open SimpleGraph
theorem qz {V:Type*} {G:SimpleGraph V} {u v x:V}
    (p:G.Walk u v) (i:ℕ) (hi:i ≤ p.length) :
    x ∈ (p.take i).support ↔ ∃ j,j ≤ i ∧ p.getVert j =x:=by
  constructor
  · intro hx
    obtain ⟨j,hjx,hj⟩ :=wkMSIEG.mp hx
    have hj':j ≤ i:=by simpa only [wkTL,min_eq_left hi] using hj
    refine ⟨j,hj',?_⟩
    simpa only [Walk.take_getVert,inf_eq_right.mpr hj'] using hjx
  · rintro ⟨j,hj,hjx⟩
    apply wkMSIEG.mpr
    refine ⟨j,?_,?_⟩
    · simpa only [Walk.take_getVert,inf_eq_right.mpr hj] using hjx
    · simpa only [wkTL,min_eq_left hi] using hj
theorem rd {V:Type*} {G:SimpleGraph V} {u v x:V}
    (p:G.Walk u v) (i:ℕ) (hi:i ≤ p.length) :
    x ∈ (p.drop i).support ↔ ∃ j,i ≤ j ∧ j ≤ p.length ∧ p.getVert j =x:=by
  constructor
  · intro hx
    obtain ⟨j,hjx,hj⟩ :=wkMSIEG.mp hx
    rw [wkDL] at hj
    refine ⟨i+j,by omega,by omega,?_⟩
    simpa only [wkDG] using hjx
  · rintro ⟨j,hij,hj,hjx⟩
    apply wkMSIEG.mpr
    refine ⟨j-i,?_,?_⟩
    · simpa only [wkDG,natASOL hij] using hjx
    · rw [wkDL]
      omega
theorem vJ {V:Type*} {G:SimpleGraph V} {u v :V}
    (p:G.Walk u v) (hp:p.IsPath) (i j :ℕ) (hij:i < j) (hj:j ≤ p.length) :
    (p.take i).support.Disjoint (p.drop j).support:=by
  rw [lsDL]
  intro x hx hy
  obtain ⟨a,ha,hax⟩ := (qz p i (by omega)).mp hx
  obtain ⟨b,hjb,hb,hbx⟩ := (rd p j hj).mp hy
  have hab:a=b:=hp.getVert_injOn (by change a ≤ p.length;omega) hb (hax.trans hbx.symm)
  omega
def sX {V:Type*} {G:SimpleGraph V} {u v :V}
    (p:G.Walk u v) (i j :ℕ) (hij:i ≤ j) : G.Walk (p.getVert i) (p.getVert j) :=
  ((p.drop i).take (j-i)).copy rfl (by
    rw [wkDG,natASOL hij])
theorem y2 {V:Type*} {G:SimpleGraph V} {u v :V}
    (p:G.Walk u v) (i j :ℕ) (hij:i ≤ j) (hj:j ≤ p.length) :
    (sX p i j hij).length=j-i:=by
  simp only [sX,Walk.length_copy,wkTL,wkDL]
  exact min_eq_left (by omega)
theorem aj {V:Type*} {G:SimpleGraph V} {u v :V}
    (p:G.Walk u v) (hp:p.IsPath) (i j :ℕ) (hij:i ≤ j) :
    (sX p i j hij).IsPath:=by
  simpa only [sX,Walk.isPath_copy] using ((hp.drop i).take (j-i))
theorem vo {V:Type*} {G:SimpleGraph V} {u v x:V}
    (p:G.Walk u v) (i j :ℕ) (hij:i ≤ j) (hj:j ≤ p.length) :
    x ∈ (sX p i j hij).support ↔
      ∃ a,i ≤ a ∧ a ≤ j ∧ p.getVert a =x:=by
  rw [sX,Walk.support_copy]
  have hlen:j-i ≤ (p.drop i).length:=by rw [wkDL];omega
  rw [qz (p.drop i) (j-i) hlen]
  constructor
  · rintro ⟨a,ha,hax⟩
    refine ⟨i+a,by omega,by omega,?_⟩
    simpa only [wkDG] using hax
  · rintro ⟨a,hia,haj,hax⟩
    refine ⟨a-i,by omega,?_⟩
    simpa only [wkDG,natASOL hia] using hax
end Erdos556
namespace Erdos556
open SimpleGraph
def rF {V:Type*} {G:SimpleGraph V} {v:V}
    (c:G.Walk v v) (i j :ℕ) : G.Walk (c.getVert j) (c.getVert i) :=
  (c.drop j).append (c.take i)
theorem uF {V:Type*} {G:SimpleGraph V} {v:V}
    (c:G.Walk v v) (i j :ℕ) (hi:i ≤ c.length) :
    (rF c i j).length=c.length-j+i:=by
  simp only [rF,wkLA,wkDL,
    wkTL,min_eq_left hi]
theorem x5 {V:Type*} {G:SimpleGraph V} {v:V}
    (c:G.Walk v v) (hc:c.IsCycle) (i j :ℕ) (hij:i < j) (hj:j ≤ c.length) :
    (rF c i j).IsPath:=by
  apply qr (c.drop j) (c.take i)
    (hc.isPath_drop (by omega)) (hc.isPath_take (by omega))
  intro x hxd hxt
  obtain ⟨a,hja,ha,hax⟩ := (rd c j hj).mp hxd
  obtain ⟨b,hb,hbx⟩ := (qz c i (by omega)).mp hxt
  by_cases he:a=c.length
  · rw [he,Walk.getVert_length] at hax
    exact hax.symm
  · have hab:=hc.getVert_injOn' (by change a ≤ c.length-1;omega)
      (by change b ≤ c.length-1;omega) (hax.trans hbx.symm)
    omega
theorem xU {V:Type*} {G:SimpleGraph V} {v x :V}
    (c:G.Walk v v) (i j :ℕ) (hi:i ≤ c.length) (hj:j ≤ c.length)
    (hx:x ∈ (rF c i j).support) : x ∈ c.support:=by
  rcases (wkMSAI (c.drop j) (c.take i)).mp hx with hxd | hxt
  · obtain ⟨a,_,_,hax⟩ := (rd c j hj).mp hxd
    exact hax ▸ c.getVert_mem_support a
  · obtain ⟨a,_,hax⟩ := (qz c i hi).mp hxt
    exact hax ▸ c.getVert_mem_support a
theorem rA {V:Type*} {G:SimpleGraph V} {v:V}
    (c:G.Walk v v) (hc:c.IsCycle) (i j a:ℕ)
    (hia:i ≤ a) (haj:a ≤ j) (hj:j < c.length)
    (ha:c.getVert a ∈ (rF c i j).support) : a=i ∨ a=j:=by
  rcases (wkMSAI (c.drop j) (c.take i)).mp ha with had | hat
  · obtain ⟨b,hjb,hb,hba⟩ := (rd c j hj.le).mp had
    by_cases hbe:b=c.length
    · rw [hbe,Walk.getVert_length] at hba
      have h := (hc.getVert_endpoint_iff (by omega)).mp hba.symm
      left
      omega
    · have hba':=hc.getVert_injOn' (by change b ≤ c.length-1;omega)
        (by change a ≤ c.length-1;omega) hba
      right
      omega
  · obtain ⟨b,hbi,hba⟩ := (qz c i (by omega)).mp hat
    have hba':=hc.getVert_injOn' (by change b ≤ c.length-1;omega)
      (by change a ≤ c.length-1;omega) hba
    left
    omega
end Erdos556
namespace Erdos556
open Finset
theorem wj {I V :Type*} [DecidableEq V]
    (A:Finset I) (S:I → Finset V) (m:ℕ)
    (hinter: ∀ i ∈ A,∀ j ∈ A,i ≠ j → (S i ∩ S j).card ≤ m) :
    (∑ i ∈ A,(S i).card) ≤ (A.biUnion S).card+A.card^2*m:=by
  classical
  induction A using Finset.induction_on with
  | empty=> simp
  | @insert i A hi ih=>
      have hpair: ∀ a ∈ A,∀ b ∈ A,a ≠ b → (S a ∩ S b).card ≤ m:=by
        intro a ha b hb hab
        exact hinter a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab
      have hrec:=ih hpair
      have hcross: (S i ∩ A.biUnion S).card ≤ A.card*m:=by
        have hsub:S i ∩ A.biUnion S ⊆ A.biUnion (fun j => S i ∩ S j) :=by
          intro x hx
          obtain ⟨hxi,hxA⟩ :=mem_inter.mp hx
          obtain ⟨j,hj,hxj⟩ :=mem_biUnion.mp hxA
          exact mem_biUnion.mpr ⟨j,hj,mem_inter.mpr ⟨hxi,hxj⟩⟩
        calc
          (S i ∩ A.biUnion S).card ≤ (A.biUnion (fun j => S i ∩ S j)).card:=card_le_card hsub
          _ ≤ ∑ j ∈ A,(S i ∩ S j).card:=card_biUnion_le
          _ ≤ ∑ _j ∈ A,m:=by
            apply sum_le_sum
            intro j hj
            exact hinter i (mem_insert_self _ _) j (mem_insert_of_mem hj)
              (fun h => hi (h.symm ▸ hj))
          _=A.card*m:=by simp
      have hunion:=card_union_add_card_inter (S i) (A.biUnion S)
      rw [sum_insert hi,biUnion_insert,card_insert_of_notMem hi]
      calc
        (S i).card+ ∑ j ∈ A,(S j).card ≤
            (S i).card+ (A.biUnion S).card+A.card^2*m:=by omega
        _= (S i ∪ A.biUnion S).card+ (S i ∩ A.biUnion S).card+A.card^2*m:=by omega
        _ ≤ (S i ∪ A.biUnion S).card+A.card*m+A.card^2*m:=by omega
        _ ≤ (S i ∪ A.biUnion S).card+ (A.card+1) ^ 2*m:=by
          nlinarith [Nat.zero_le (A.card*m)]
theorem yl {I V :Type*} [Fintype I] [Fintype V]
    [DecidableEq V] (S:I → Finset V) (d m :ℕ)
    (hsize: ∀ i,d ≤ (S i).card)
    (hcount:ftCard V + (ftCard I) ^ 2*m < ftCard I *d) :
    ∃ i j:I,i ≠ j ∧ m < (S i ∩ S j).card:=by
  classical
  by_contra! h
  have hsum:ftCard I *d ≤ ∑ i,(S i).card:=by
    calc
      ftCard I *d= ∑ _i:I,d:=by simp
      _ ≤ ∑ i,(S i).card:=sum_le_sum fun i _=> hsize i
  have hbound:=wj univ S m
    (fun i _ j _ hij=> h i j hij)
  rw [card_univ] at hbound
  have hcard:=card_le_univ (univ.biUnion S)
  omega
theorem vN {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (D d :ℕ)
    (hN:0 < ftCard V) (hscale:ftCard V ≤ D *d)
    (hdegree: ∀ v,d ≤ G.degree v) (S:Finset V) (hS:2*S.card ≤ d)
    (a:Fin (4*D) → V) :
    ∃ i j:Fin (4*D),i ≠ j ∧
      ftCard V / (2* (4*D) ^ 2) <
        ((G.neighborFinset (a i) ∩ G.neighborFinset (a j)) \ S).card:=by
  classical
  let W (i:Fin (4*D)) :=G.neighborFinset (a i) \ S
  have hsize (i:Fin (4*D)) : d-S.card ≤ (W i).card:=by
    have hi:=hdegree (a i)
    have hint: (S ∩ G.neighborFinset (a i)).card ≤ S.card:=card_le_card inter_subset_left
    dsimp [W]
    rw [card_sdiff]
    rw [G.card_neighborFinset_eq_degree]
    omega
  have hcount:ftCard V + (4*D) ^ 2*
      (ftCard V / (2* (4*D) ^ 2)) < 4*D* (d-S.card) :=by
    have hd:d ≤ 2* (d-S.card) :=by omega
    have hmul:=natMLML (2*D) hd
    have hdiv:=natDMLS (ftCard V) (2* (4*D) ^ 2)
    nlinarith
  obtain ⟨i,j,hij,hc⟩ :=yl W (d-S.card)
    (ftCard V / (2* (4*D) ^ 2)) hsize (by simpa only [ftCF] using hcount)
  refine ⟨i,j,hij,?_⟩
  have heq:W i ∩ W j= (G.neighborFinset (a i) ∩ G.neighborFinset (a j)) \ S:=by
    ext v
    simp only [W,mem_inter,mem_sdiff]
    tauto
  rwa [heq] at hc
end Erdos556
namespace Erdos556
open Finset
theorem wC {V:Type*} [Fintype V]
    (D L d:ℕ) (hL:0 < L) (hN:0 < ftCard V)
    (hscale:ftCard V ≤ D *d)
    (S:Fin (2*D*L) → Finset V) (hsize: ∀ i,d ≤ (S i).card) :
    ∃ (X:Finset (Fin (2*D*L))) (W:Finset V),
      L ≤ X.card ∧ ftCard V ≤ 2 *D*2^ (2*D*L) * W.card ∧
      ∀ i ∈ X,∀ v ∈ W,v ∈ S i:=by
  classical
  let I :=Fin (2*D*L)
  let pattern (v:V) : Finset I :=univ.filter (fun i => v ∈ S i)
  let A :=univ.filter (fun v => L ≤ (pattern v).card)
  have hinc: (∑ i :I,(S i).card) = ∑ v :V,(pattern v).card:=by
    have hs (i:I) : (S i).card= ∑ v:V,if v ∈ S i then 1 else 0 :=by simp
    have hp (v:V) : (pattern v).card= ∑ i:I,if v ∈ S i then 1 else 0 :=by
      simp [pattern]
    simp_rw [hs,hp]
    exact sum_comm
  have hlower: (2*D*L) * d ≤ ∑ v :V,(pattern v).card:=by
    rw [← hinc]
    calc
      (2*D*L) * d= ∑ _i:I,d:=by simp [I]
      _ ≤ ∑ i :I,(S i).card:=sum_le_sum fun i _=> hsize i
  have hpoint (v:V) : (pattern v).card ≤ L+if v ∈ A then 2 *D*L else 0 :=by
    by_cases hv:v ∈ A
    · rw [if_pos hv]
      have h :=card_le_univ (pattern v)
      simp only [I,ftCF] at h
      omega
    · rw [if_neg hv]
      have h : ¬ L ≤ (pattern v).card:=by simpa only [A,mem_filter,mem_univ,true_and] using hv
      omega
  have hupper: (∑ v :V,(pattern v).card) ≤ L*ftCard V + (2*D*L) * A.card:=by
    calc
      (∑ v :V,(pattern v).card) ≤ ∑ v :V,(L+if v ∈ A then 2 *D*L else 0) :=
        sum_le_sum fun v _=> hpoint v
      _=L*ftCard V + (2*D*L) * A.card:=by
        simp [sum_add_distrib,natMC]
  have hA:ftCard V ≤ 2 *D*A.card:=by
    have hscaled:=natMLML (2*L) hscale
    have h :L*ftCard V ≤ L * (2*D*A.card) :=by
      nlinarith only [hlower,hupper,hscaled]
    exact (mul_le_mul_iff_right₀ hL).mp h
  let fiber (X:Finset I) :=A.filter (fun v => pattern v =X)
  obtain ⟨X,_,hmax⟩ :=exists_max_image (univ:Finset (Finset I))
    (fun X => (fiber X).card) univ_nonempty
  have hfib:A.card= ∑ X:Finset I,(fiber X).card:=
    card_eq_sum_card_fiberwise (fun v _=> mem_univ (pattern v))
  have hbound:A.card ≤ 2^ (2*D*L) * (fiber X).card:=by
    rw [hfib]
    calc
      (∑ Y :Finset I,(fiber Y).card) ≤ ∑ _Y:Finset I,(fiber X).card:=
        sum_le_sum fun Y _=> hmax Y (mem_univ Y)
      _=2^ (2*D*L) * (fiber X).card:=by simp [I]
  have hlarge:ftCard V ≤ 2 *D*2^ (2*D*L) * (fiber X).card:=by
    calc
      ftCard V ≤ 2 *D*A.card:=hA
      _ ≤ 2*D* (2^ (2*D*L) * (fiber X).card) :=natMLML _ hbound
      _=2*D*2^ (2*D*L) * (fiber X).card:=by ring
  have hnon: (fiber X).Nonempty:=by
    apply card_pos.mp
    by_contra h
    have hz: (fiber X).card=0:=by omega
    rw [hz,mul_zero] at hlarge
    omega
  obtain ⟨v,hv⟩ :=hnon
  have hvA:= (mem_filter.mp hv).1
  have hvX:= (mem_filter.mp hv).2
  have hX:L ≤ X.card:=by
    rw [← hvX]
    exact (mem_filter.mp hvA).2
  refine ⟨X,fiber X,hX,hlarge,?_⟩
  intro i hi v hv
  have hpat:= (mem_filter.mp hv).2
  have hi':i ∈ pattern v :=by rw [hpat];exact hi
  exact (mem_filter.mp hi').2
end Erdos556
namespace Erdos556
open SimpleGraph Finset
def xW {V:Type*} [DecidableEq V] {G:SimpleGraph V} {z:V}
    (c:G.Walk z z) (W:Finset V) : Finset ℕ :=
  (range c.length).filter (fun i => c.getVert i ∈ W)
theorem ae {V:Type*} [DecidableEq V] {G:SimpleGraph V} {z:V}
    (c:G.Walk z z) (hc:c.IsCycle) (W:Finset V) (hW: ∀ x ∈ W,x ∈ c.support) :
    (xW c W).image c.getVert=W:=by
  ext x
  constructor
  · intro hx
    obtain ⟨i,hi,hix⟩ :=mem_image.mp hx
    exact hix ▸ (mem_filter.mp hi).2
  · intro hx
    obtain ⟨i,hix,hi⟩ :=wkMSIEG.mp (hW x hx)
    by_cases hie:i=c.length
    · have hzx:z=x:=by simpa only [hie,Walk.getVert_length] using hix
      apply mem_image.mpr
      refine ⟨0,mem_filter.mpr ⟨mem_range.mpr (by have h :=hc.three_le_length;omega),?_⟩,?_⟩
      · simpa only [Walk.getVert_zero,hzx] using hx
      · simpa only [Walk.getVert_zero] using hzx
    · exact mem_image.mpr ⟨i,mem_filter.mpr ⟨mem_range.mpr (by omega),hix ▸ hx⟩,hix⟩
theorem ax {V:Type*} [DecidableEq V] {G:SimpleGraph V} {z:V}
    (c:G.Walk z z) (hc:c.IsCycle) (W:Finset V) (hW: ∀ x ∈ W,x ∈ c.support) :
    (xW c W).card=W.card:=by
  have hinj:Set.InjOn c.getVert (xW c W:Set ℕ) :=by
    intro i hi j hj hij
    have hi':=mem_range.mp (mem_filter.mp hi).1
    have hj':=mem_range.mp (mem_filter.mp hj).1
    exact hc.getVert_injOn' (by change i ≤ c.length-1;omega)
      (by change j ≤ c.length-1;omega) hij
  have hcard:=card_image_of_injOn hinj
  rw [ae c hc W hW] at hcard
  exact hcard.symm
theorem vC {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] {z:V} (c:G.Walk z z) (hc:c.IsCycle)
    (D L d:ℕ) (hL:0 < L) (hscale:ftCard V ≤ D *d)
    (hdegree: ∀ v,d ≤ G.degree v) (hlen:4*D*L ≤ c.length) :
    ∃ (A:Finset ℕ) (W:Finset V),A.card=L ∧
      (∀ i ∈ A,i < 4*D*L ∧ Even i) ∧
      (A.image c.getVert).card=L ∧
      ftCard V ≤ 2 *D*2^ (2*D*L) * W.card ∧
      ∀ i ∈ A,∀ w ∈ W,G.Adj (c.getVert i) w :=by
  classical
  obtain ⟨I,W,hI,hW,hcommon⟩ :=wC D L d hL
    (ftCPI.mpr ⟨z⟩) hscale
    (fun i => G.neighborFinset (c.getVert (2*i.val)))
    (fun i => by simpa only [G.card_neighborFinset_eq_degree] using hdegree (c.getVert (2*i.val)))
  obtain ⟨J,hJI,hJ⟩ :=exists_subset_card_eq hI
  let f :Fin (2*D*L) ↪ ℕ:=
    ⟨fun i => 2 *i.val,by
      intro i j h
      change 2 *i.val=2*j.val at h
      exact Fin.ext (by omega)⟩
  let A :=J.map f
  have hA:A.card=L:=by simpa only [A,card_map] using hJ
  have hpos (i:ℕ) (hi:i ∈ A) : i < 4*D*L ∧ Even i :=by
    obtain ⟨a,ha,rfl⟩ :=mem_map.mp hi
    have hat:=a.isLt
    change 2 *a.val < 4*D*L ∧ Even (2*a.val)
    have hb:=Nat.mul_lt_mul_of_pos_left hat (by decide:0 < 2)
    have he:2* (2*D*L) = 4*D*L:=by ring
    rw [he] at hb
    exact ⟨hb,⟨a.val,by omega⟩⟩
  have hinj:Set.InjOn c.getVert (A:Set ℕ) :=by
    intro i hi j hj hij
    have hi':= (hpos i hi).1
    have hj':= (hpos j hj).1
    exact hc.getVert_injOn' (by change i ≤ c.length-1;omega)
      (by change j ≤ c.length-1;omega) hij
  refine ⟨A,W,hA,hpos,(card_image_of_injOn hinj).trans hA,hW,?_⟩
  intro i hi w hw
  obtain ⟨a,ha,rfl⟩ :=mem_map.mp hi
  exact (G.mem_neighborFinset _ _).mp (hcommon a (hJI ha) w hw)
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem xB {V:Type*} [DecidableEq V] {G:SimpleGraph V} {z:V}
    (c:G.Walk z z) (W:Finset V) (N K Q M :ℕ) (hM:M ≤ c.length)
    (hsize:N ≤ K*W.card) (hN:2*K* (Q+M+1) ≤ N)
    (hoff: (W \ c.support.toFinset).card < Q) :
    ∃ U :Finset V,U ⊆ W ∧ (∀ x ∈ U,x ∈ c.support) ∧
      (∀ i,i ≤ M → c.getVert i ∉ U) ∧ N ≤ 2*K*U.card:=by
  let P := (c.take M).support.toFinset
  let E :=W \ c.support.toFinset
  let U := (W ∩ c.support.toFinset) \ P
  have hP:P.card ≤ M+1:=by
    have h :=lsTCL (c.take M).support
    simpa only [wkLS,wkTL,min_eq_left hM] using h
  have hcover:W ⊆ U ∪ E ∪ P:=by
    intro x hxW
    by_cases hxP:x ∈ P
    · exact mem_union_right _ hxP
    by_cases hxC:x ∈ c.support.toFinset
    · exact mem_union_left _ (mem_union_left _ (mem_sdiff.mpr ⟨mem_inter.mpr ⟨hxW,hxC⟩,hxP⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_sdiff.mpr ⟨hxW,hxC⟩))
  have hcount:W.card ≤ U.card+Q+M+1:=by
    have h₁:=card_le_card hcover
    have h₂:=card_union_le (U ∪ E) P
    have h₃:=card_union_le U E
    change E.card < Q at hoff
    omega
  refine ⟨U,(sdiff_subset).trans inter_subset_left,?_,?_,?_⟩
  · intro x hx
    exact lsMT.mp (mem_inter.mp (mem_sdiff.mp hx).1).2
  · intro i hi hmem
    have hp:c.getVert i ∈ P :=lsMT.mpr
      ((qz c M hM).mpr ⟨i,hi,rfl⟩)
    exact (mem_sdiff.mp hmem).2 hp
  · have hmul:=natMLML K hcount
    nlinarith only [hsize,hN,hmul]
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem xa (S:Finset ℕ) (N Q :ℕ) (hQ:0 < Q)
    (hS: ∀ i ∈ S,i < N) (hc:2* (N/Q+1) < S.card) :
    ∃ i ∈ S,∃ j ∈ S,i < j ∧ j < i+Q ∧ i%2=j%2:=by
  let f (i:ℕ) := (i/Q,i%2)
  let T :=range (N/Q+1) ×ˢ range 2
  have hT:T.card < S.card:=by simpa only [T,card_product,card_range,natMC] using hc
  have hf: ∀ i ∈ S,f i ∈ T:=by
    intro i hi
    apply mem_product.mpr
    refine ⟨mem_range.mpr ?_,mem_range.mpr (natML _ (by decide))⟩
    exact natLSOL (Nat.div_le_div_right (hS i hi).le)
  obtain ⟨i,hi,j,hj,hij,heq⟩ :=exists_ne_map_eq_of_card_lt_of_maps_to hT hf
  have hdiv:i/Q=j/Q:=congrArg Prod.fst heq
  have hpar:i%2=j%2:=congrArg Prod.snd heq
  have hclose:j < i+Q ∧ i < j+Q:=by
    have hiq:=natDAM i Q
    have hjq:=natDAM j Q
    have him:=natML i hQ
    have hjm:=natML j hQ
    rw [hdiv] at hiq
    omega
  rcases lt_or_gt_of_ne hij with hij | hji
  · exact ⟨i,hi,j,hj,hij,hclose.1,hpar⟩
  · exact ⟨j,hj,i,hi,hji,hclose.2,hpar.symm⟩
theorem th (N K :ℕ) (hK:0 < K) (hN:4*K ≤ N) :
    2* (N/ (4*K) + 1) ≤ N/K:=by
  have hq:1 ≤ N/ (4*K) := (natLDIML (by omega)).mpr (by omega)
  have hmul:=natDMLS N (4*K)
  have hdiv:4* (N/ (4*K)) ≤ N/K:=by
    apply (natLDIML hK).mpr
    nlinarith only [hmul]
  omega
theorem vE {V:Type*}
    {G:SimpleGraph V} {u v :V} (p:G.Walk u v)
    (W:Finset V) (hW: ∀ x ∈ W,x ∈ p.support)
    (N K :ℕ) (hK:0 < K) (hN:4*K ≤ N) (hpN:p.length < N)
    (hcard:N/K < W.card) :
    ∃ i j:ℕ,i < j ∧ j ≤ p.length ∧ j < i+4*K ∧
      i%2=j%2 ∧ p.getVert i ∈ W ∧ p.getVert j ∈ W :=by
  classical
  let S :=W.image (fun x => p.support.idxOf x)
  have hidx (x:V) (hx:x ∈ W) : p.support.idxOf x ≤ p.length:=by
    have h :=List.idxOf_lt_length_of_mem (hW x hx)
    rw [wkLS] at h
    omega
  have hinj:Set.InjOn (fun x => p.support.idxOf x) (W:Set V) :=by
    intro x hx y hy hxy
    have h :=congrArg p.getVert hxy
    simpa only [p.getVert_support_idxOf (hW x hx),p.getVert_support_idxOf (hW y hy)] using h
  have hScard:S.card=W.card:=card_image_of_injOn hinj
  have hS (i:ℕ) (hi:i ∈ S) : i < N:=by
    obtain ⟨x,hx,rfl⟩ :=mem_image.mp hi
    exact (hidx x hx).trans_lt hpN
  have hc:2* (N/ (4*K) + 1) < S.card:=by
    rw [hScard]
    exact (th N K hK hN).trans_lt hcard
  obtain ⟨i,hi,j,hj,hij,hclose,hpar⟩ :=
    xa S N (4*K) (by omega) hS hc
  obtain ⟨x,hx,hxi⟩ :=mem_image.mp hi
  obtain ⟨y,hy,hyj⟩ :=mem_image.mp hj
  have hix:p.getVert i =x:=by rw [← hxi];exact p.getVert_support_idxOf (hW x hx)
  have hjy:p.getVert j =y:=by rw [← hyj];exact p.getVert_support_idxOf (hW y hy)
  refine ⟨i,j,hij,?_,hclose,hpar,hix ▸ hx,hjy ▸ hy⟩
  rw [← hyj]
  exact hidx y hy
end Erdos556
namespace Erdos556
open Finset
theorem yJ (S:Finset ℕ) (N Q L:ℕ) (hQ:0 < Q)
    (hS: ∀ i ∈ S,i < N)
    (hc:2* (N/Q+1) * (L-1) < S.card) :
    ∃ T :Finset ℕ,T ⊆ S ∧ T.card=L ∧
      ∀ i ∈ T,∀ j ∈ T,i%2=j%2 ∧ j < i+Q:=by
  let f (i:ℕ) := (i/Q,i%2)
  let B :=range (N/Q+1) ×ˢ range 2
  have hf: ∀ i ∈ S,f i ∈ B:=by
    intro i hi
    apply mem_product.mpr
    refine ⟨mem_range.mpr ?_,mem_range.mpr (natML _ (by decide))⟩
    exact natLSOL (Nat.div_le_div_right (hS i hi).le)
  have hBc:B.card* (L-1) < S.card:=by
    simpa only [B,card_product,card_range,natMC (N/Q+1) 2] using hc
  obtain ⟨b,_,hb⟩ :=exists_lt_card_fiber_of_mul_lt_card_of_maps_to hf hBc
  obtain ⟨T,hT,hTc⟩ :=exists_subset_card_eq (show L ≤ (S.filter (fun i => f i=b)).card by
    omega)
  refine ⟨T,hT.trans (filter_subset _ _),hTc,?_⟩
  intro i hi j hj
  have hi':= (mem_filter.mp (hT hi)).2
  have hj':= (mem_filter.mp (hT hj)).2
  have heq:=hi'.trans hj'.symm
  have hdiv:i/Q=j/Q:=congrArg Prod.fst heq
  have hpar:i%2=j%2:=congrArg Prod.snd heq
  refine ⟨hpar,?_⟩
  have hiq:=natDAM i Q
  have hjq:=natDAM j Q
  have him:=natML i hQ
  have hjm:=natML j hQ
  rw [hdiv] at hiq
  omega
theorem yL (N K L:ℕ) (hK:0 < K) (hL:0 < L)
    (hN:8*K*L ≤ N) :
    2* (N/ (8*K*L) + 1) * (L-1) < N/ (2*K) :=by
  have hQ:0 < 8*K*L:=by positivity
  have hq:1 ≤ N/ (8*K*L) := (natLDIML hQ).mpr (by omega)
  have hmul:=natDMLS N (8*K*L)
  have hdiv:4*L* (N/ (8*K*L)) ≤ N/ (2*K) :=by
    apply (natLDIML (by omega)).mpr
    nlinarith only [hmul]
  have hsub:L-1+1=L:=by omega
  have hprod:0 ≤ (N/ (8*K*L) - 1) * (L-1) :=Nat.zero_le _
  have hqsub:N/ (8*K*L) - 1+1=N/ (8*K*L) :=by omega
  nlinarith
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem ys {V:Type*} {G:SimpleGraph V} {z:V}
    (c:G.Walk z z) (hc:c.IsCycle) (W:Finset V) (hW: ∀ x ∈ W,x ∈ c.support)
    (M N K L :ℕ) (hK:0 < K) (hL:0 < L) (hN:8*K*L ≤ N)
    (hcN:c.length ≤ N) (hsize:N ≤ 2*K*W.card)
    (hoff: ∀ i,i ≤ M → c.getVert i ∉ W) :
    ∃ B :Finset ℕ,B.card=L ∧
      (∀ i ∈ B,M < i ∧ i < c.length ∧ c.getVert i ∈ W) ∧
      ∀ i ∈ B,∀ j ∈ B,i%2=j%2 ∧ j < i+8*K*L:=by
  classical
  let S :=xW c W
  have hScard:S.card=W.card:=ax c hc W hW
  have hS (i:ℕ) (hi:i ∈ S) : i < N:=
    (mem_range.mp (mem_filter.mp hi).1).trans_le hcN
  have hdiv:N/ (2*K) ≤ W.card:=by
    have h :=Nat.div_le_div_right hsize (c:=2*K)
    simpa only [Nat.mul_div_cancel_left W.card (by omega:0 < 2*K)] using h
  have hcount:2* (N/ (8*K*L) + 1) * (L-1) < S.card:=by
    rw [hScard]
    exact (yL N K L hK hL hN).trans_le hdiv
  obtain ⟨B,hBS,hB,hpar⟩ :=yJ S N (8*K*L) L
    (by positivity) hS hcount
  refine ⟨B,hB,?_,hpar⟩
  intro i hi
  obtain ⟨hiN,hiW⟩ :=mem_filter.mp (hBS hi)
  exact ⟨by by_contra h;exact hoff i (by omega) hiW,mem_range.mp hiN,hiW⟩
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem vx {V:Type*} [DecidableEq V]
    {G:SimpleGraph V} {w:V} (c:G.Walk w w) (hc:c.IsCycle)
    (A:Finset ℕ) (hA:2 ≤ A.card) (M:ℕ) (hM:M < c.length)
    (hAM: ∀ i ∈ A,i ≤ M) (hpar: ∀ i ∈ A,∀ j ∈ A,i%2=j%2)
    (Y:Finset V) (hY: ∀ y ∈ Y,y ∉ c.support) :
    ∃ u ∈ A.image c.getVert,∃ v ∈ A.image c.getVert,u ≠ v ∧
      ∃ p :G.Walk u v,p.IsPath ∧ c.length ≤ p.length+M ∧
        p.length%2=c.length%2 ∧
        ∀ z ∈ p.support,z ∈ A.image c.getVert ∪ Y → z=u ∨ z=v:=by
  classical
  have hAnon:A.Nonempty:=card_pos.mp (by omega)
  let i :=A.min' hAnon
  let j :=A.max' hAnon
  have hiA:i ∈ A:=A.min'_mem hAnon
  have hjA:j ∈ A:=A.max'_mem hAnon
  have hij:i < j:=A.min'_lt_max'_of_card (by omega)
  have hiM:=hAM i hiA
  have hjM:=hAM j hjA
  have huv:c.getVert j ≠ c.getVert i :=by
    intro heq
    have h :=hc.getVert_injOn' (by change j ≤ c.length-1;omega)
      (by change i ≤ c.length-1;omega) heq
    omega
  refine ⟨c.getVert j,mem_image.mpr ⟨j,hjA,rfl⟩,
    c.getVert i,mem_image.mpr ⟨i,hiA,rfl⟩,huv,
    rF c i j,x5 c hc i j hij (by omega),?_,?_,?_⟩
  · rw [uF c i j (by omega)]
    omega
  · rw [uF c i j (by omega)]
    have h :=hpar i hiA j hjA
    omega
  · intro z hz hzR
    rcases mem_union.mp hzR with hzA | hzY
    · obtain ⟨a,haA,haz⟩ :=mem_image.mp hzA
      have hia:i ≤ a:=A.min'_le a haA
      have haj:a ≤ j:=A.le_max' a haA
      have haz':c.getVert a ∈ (rF c i j).support:=haz ▸ hz
      rcases rA c hc i j a hia haj (by omega) haz'
        with hai | haj
      · right
        rw [← haz,hai]
      · left
        rw [← haz,haj]
    · exact (hY z hzY (xU c i j (by omega) (by omega) hz)).elim
end Erdos556
namespace Erdos556
open SimpleGraph
theorem vb {V:Type*} {G:SimpleGraph V} {z:V}
    (c:G.Walk z z) (hc:c.IsCycle) (u v w y w':ℕ)
    (huv:u < v) (hvw:v < w) (hwy:w < y) (hyw:y < w') (hw':w' < c.length)
    (huy:G.Adj (c.getVert u) (c.getVert y))
    (hvy:G.Adj (c.getVert v) (c.getVert y)) :
    ∃ p :G.Walk (c.getVert w') (c.getVert w),p.IsPath ∧
      p.length+v+w'=c.length+u+w+2 ∧
      (∀ a,u < a → a < v → c.getVert a ∉ p.support) ∧
      (∀ a,w < a → a < w' → a ≠ y → c.getVert a ∉ p.support) :=by
  let q :=rF c u w'
  let r :=sX c v w (by omega)
  have hq:q.IsPath:=x5 c hc u w' (by omega) hw'.le
  have hr:r.IsPath:=by
    simp only [r,sX,Walk.isPath_copy]
    exact (hc.isPath_drop (by omega:0 < v)).take (w-v)
  have hqavoid (a:ℕ) (hua:u < a) (haw:a < w') : c.getVert a ∉ q.support:=by
    intro ha
    have h :=rA c hc u w' a hua.le haw.le hw' ha
    omega
  have hrmem (a:V) (ha:a ∈ r.support) :
      ∃ k,v ≤ k ∧ k ≤ w ∧ c.getVert k =a:=
    (vo c v w (by omega) (by omega)).mp ha
  have hyq:c.getVert y ∉ q.support:=hqavoid y (by omega) hyw
  have hyr:c.getVert y ∉ r.support:=by
    intro hy
    obtain ⟨k,hvk,hkw,hky⟩ :=hrmem _ hy
    have h :=hc.getVert_injOn' (by change k ≤ c.length-1;omega)
      (by change y ≤ c.length-1;omega) hky
    omega
  have hqr:q.support.Disjoint r.support:=by
    rw [lsDL]
    intro a haq har
    obtain ⟨k,hvk,hkw,hka⟩ :=hrmem a har
    exact hqavoid k (by omega) (by omega) (hka ▸ haq)
  let p := (q.concat huy).append (wkCons hvy.symm r)
  have hp:p.IsPath:=by
    apply qr (q.concat huy) (wkCons hvy.symm r)
      (hq.concat hyq huy) ((wkCII _ _).mpr ⟨hr,hyr⟩)
    intro a ha hb
    simp only [wkSC,lsMA,lsMS] at ha
    simp only [wkSC2,lsMC] at hb
    rcases ha with haq | hay
    · rcases hb with hay | har
      · exact hay
      · exact (hqr haq har).elim
    · exact hay
  have havoid (a:ℕ) (hua:u < a) (haw:a < w')
      (havw: ¬ (v ≤ a ∧ a ≤ w)) (hay:a ≠ y) : c.getVert a ∉ p.support:=by
    intro ha
    rcases (wkMSAI (q.concat huy) (wkCons hvy.symm r)).mp ha with ha | ha
    · simp only [wkSC,lsMA,lsMS] at ha
      rcases ha with haq | hay'
      · exact hqavoid a hua haw haq
      · exact hay (hc.getVert_injOn' (by change a ≤ c.length-1;omega)
          (by change y ≤ c.length-1;omega) hay')
    · simp only [wkSC2,lsMC] at ha
      rcases ha with hay' | har
      · exact hay (hc.getVert_injOn' (by change a ≤ c.length-1;omega)
          (by change y ≤ c.length-1;omega) hay')
      · obtain ⟨k,hvk,hkw,hka⟩ :=hrmem _ har
        have hka':=hc.getVert_injOn' (by change k ≤ c.length-1;omega)
          (by change a ≤ c.length-1;omega) hka
        exact havw (by omega)
  refine ⟨p,hp,?_,?_,?_⟩
  · simp only [p,q,r,wkLA,wkLC,wkLC2,
      uF c u w' (by omega),y2 c v w (by omega) (by omega)]
    omega
  · intro a hua hav
    exact havoid a hua (by omega) (by omega) (by omega)
  · intro a hwa haw hay
    exact havoid a (by omega) haw (by omega) hay
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem vg {V:Type*} [DecidableEq V]
    {G:SimpleGraph V} {z:V} (c:G.Walk z z) (hc:c.IsCycle)
    (A B :Finset ℕ) (Q M H:ℕ) (hQ:0 < Q)
    (hA:A.card=Q+2) (hB:B.card=Q+3) (hM:M < c.length)
    (hAM: ∀ a ∈ A,a ≤ M) (hBM: ∀ b ∈ B,M < b ∧ b < c.length)
    (hparA: ∀ a ∈ A,∀ b ∈ A,a%2=b%2)
    (hparB: ∀ a ∈ B,∀ b ∈ B,a%2=b%2)
    (hdiam: ∀ a ∈ B,∀ b ∈ B,b < a+H)
    (hcomplete: ∀ a ∈ A,∀ b ∈ B,G.Adj (c.getVert a) (c.getVert b)) :
    ∃ X Y:Finset V,X.card=Q+2 ∧ Y.card=Q ∧ Disjoint X Y ∧
      (∀ x ∈ X,∀ y ∈ Y,G.Adj x y) ∧
      ∃ u ∈ X,∃ v ∈ X,u ≠ v ∧ ∃ p:G.Walk u v,p.IsPath ∧
        c.length ≤ p.length+M+H ∧ p.length%2=c.length%2 ∧
        ∀ w ∈ p.support,w ∈ X ∪ Y → w=u ∨ w=v:=by
  classical
  have hAn:A.Nonempty:=card_pos.mp (by omega)
  have hBn:B.Nonempty:=card_pos.mp (by omega)
  let a :=A.min' hAn
  let b :=A.max' hAn
  let w :=B.min' hBn
  let w':=B.max' hBn
  have ha:a ∈ A:=A.min'_mem hAn
  have hb:b ∈ A:=A.max'_mem hAn
  have hw:w ∈ B:=B.min'_mem hBn
  have hw':w' ∈ B:=B.max'_mem hBn
  have hab:a < b:=A.min'_lt_max'_of_card (by omega)
  have hww:w < w':=B.min'_lt_max'_of_card (by omega)
  have hmiddle: (B \ {w,w'}).Nonempty:=by
    apply card_pos.mp
    have hpair: ({w,w'} : Finset ℕ).card ≤ 2:= (card_insert_le _ _).trans (by simp)
    have hint:=card_le_card (show ({w,w'} : Finset ℕ) ∩ B ⊆ {w,w'} from inter_subset_left)
    rw [card_sdiff]
    omega
  obtain ⟨y,hy⟩ :=hmiddle
  have hyB:= (mem_sdiff.mp hy).1
  have hyw:y ≠ w:=fun h => (mem_sdiff.mp hy).2 (by simp [h])
  have hyw':y ≠ w':=fun h => (mem_sdiff.mp hy).2 (by simp [h])
  have hwy:w < y:=lt_of_le_of_ne (B.min'_le y hyB) hyw.symm
  have hywlt:y < w':=lt_of_le_of_ne (B.le_max' y hyB) hyw'
  have hbM:=hAM b hb
  have haM:=hAM a ha
  have hwM:= (hBM w hw).1
  have hwlen:= (hBM w' hw').2
  have hallA (i:ℕ) (hi:i ∈ A) : i < c.length:= (hAM i hi).trans_lt hM
  have hinjA:Set.InjOn c.getVert (A:Set ℕ) :=by
    intro i hi j hj hij
    exact hc.getVert_injOn' (by change i ≤ c.length-1;have h :=hallA i hi;omega)
      (by change j ≤ c.length-1;have h :=hallA j hj;omega) hij
  have hinjB:Set.InjOn c.getVert (B:Set ℕ) :=by
    intro i hi j hj hij
    exact hc.getVert_injOn' (by change i ≤ c.length-1;have h := (hBM i hi).2;omega)
      (by change j ≤ c.length-1;have h := (hBM j hj).2;omega) hij
  have habv:c.getVert a ≠ c.getVert b :=fun h => (ne_of_lt hab) (hinjA ha hb h)
  have hwyv:c.getVert w ≠ c.getVert y :=fun h => hyw (hinjB hw hyB h).symm
  have hw'yv:c.getVert w' ≠ c.getVert y :=fun h => hyw' (hinjB hw' hyB h).symm
  let X := (B.image c.getVert).erase (c.getVert y)
  let Y := ((A.image c.getVert).erase (c.getVert a)).erase (c.getVert b)
  have hX:X.card=Q+2:=by
    dsimp [X]
    rw [card_erase_of_mem (mem_image.mpr ⟨y,hyB,rfl⟩),card_image_of_injOn hinjB,hB]
    omega
  have hY:Y.card=Q:=by
    dsimp [Y]
    rw [card_erase_of_mem (mem_erase.mpr ⟨habv.symm,mem_image.mpr ⟨b,hb,rfl⟩⟩),
      card_erase_of_mem (mem_image.mpr ⟨a,ha,rfl⟩),card_image_of_injOn hinjA,hA]
    omega
  have hXYcomplete (x:V) (hx:x ∈ X) (v:V) (hv:v ∈ Y) : G.Adj x v:=by
    obtain ⟨i,hi,rfl⟩ :=mem_image.mp (mem_of_mem_erase hx)
    obtain ⟨j,hj,rfl⟩ :=mem_image.mp (mem_of_mem_erase (mem_of_mem_erase hv))
    exact (hcomplete j hj i hi).symm
  have hXY:Disjoint X Y:=by
    rw [fsDL]
    intro x hx hy
    exact (hXYcomplete x hx x hy).ne rfl
  obtain ⟨p,hp,hlen,havoidA,havoidB⟩ :=vb c hc a b w y w'
    hab (by omega) hwy hywlt hwlen (hcomplete a ha y hyB) (hcomplete b hb y hyB)
  refine ⟨X,Y,hX,hY,hXY,hXYcomplete,c.getVert w',
    mem_erase.mpr ⟨hw'yv,mem_image.mpr ⟨w',hw',rfl⟩⟩,
    c.getVert w,mem_erase.mpr ⟨hwyv,mem_image.mpr ⟨w,hw,rfl⟩⟩,
    (fun h => (ne_of_lt hww) (hinjB hw' hw h).symm),p,hp,?_,?_,?_⟩
  · have hd:=hdiam w hw w' hw'
    omega
  · have h₁:=hparA a ha b hb
    have h₂:=hparB w hw w' hw'
    omega
  · intro v hv hvXY
    rcases mem_union.mp hvXY with hvX | hvY
    · have hvy:= (mem_erase.mp hvX).1
      obtain ⟨i,hi,hiv⟩ :=mem_image.mp (mem_of_mem_erase hvX)
      by_cases hiw:i=w
      · right
        rw [← hiv,hiw]
      by_cases hiw':i=w'
      · left
        rw [← hiv,hiw']
      have hwil:w ≤ i:=B.min'_le i hi
      have hiwl:i ≤ w':=B.le_max' i hi
      have hiy:i ≠ y:=fun h => hvy (by rw [← hiv,h])
      exact (havoidB i (by omega) (by omega) hiy (hiv ▸ hv)).elim
    · have hvb:= (mem_erase.mp hvY).1
      have hva:= (mem_erase.mp (mem_of_mem_erase hvY)).1
      obtain ⟨i,hi,hiv⟩ :=mem_image.mp (mem_of_mem_erase (mem_of_mem_erase hvY))
      have hai:a ≤ i:=A.min'_le i hi
      have hib:i ≤ b:=A.le_max' i hi
      have hia:i ≠ a:=fun h => hva (by rw [← hiv,h])
      have hib':i ≠ b:=fun h => hvb (by rw [← hiv,h])
      exact (havoidA i (by omega) (by omega) (hiv ▸ hv)).elim
end Erdos556
namespace Erdos556
open SimpleGraph Finset
def rR (D Q :ℕ) :=4*D* (Q+2)
def rl (D Q :ℕ) :=2*D*2^ (2*D* (Q+2))
def sd (D Q :ℕ) :=8*rl D Q* (Q+3)
theorem tl {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] {z:V} (c:G.Walk z z) (hc:c.IsCycle)
    (D d Q:ℕ) (hD:0 < D) (hQ:0 < Q)
    (hscale:ftCard V ≤ D *d) (hdegree: ∀ v,d ≤ G.degree v)
    (hlen:rR D Q < c.length)
    (hNloss:2*rl D Q* (Q+rR D Q+1) ≤
      ftCard V)
    (hNblock:sd D Q ≤ ftCard V) :
    ∃ X Y:Finset V,X.card=Q+2 ∧ Y.card=Q ∧ Disjoint X Y ∧
      (∀ x ∈ X,∀ y ∈ Y,G.Adj x y) ∧
      ∃ u ∈ X,∃ v ∈ X,u ≠ v ∧ ∃ p:G.Walk u v,p.IsPath ∧
        c.length ≤ p.length+rR D Q+sd D Q ∧
        p.length%2=c.length%2 ∧
        ∀ w ∈ p.support,w ∈ X ∪ Y → w=u ∨ w=v:=by
  classical
  let M :=rR D Q
  let K :=rl D Q
  let H :=sd D Q
  obtain ⟨A,W,hA,hAP,hAX,hWsize,hcomplete⟩ :=vC
    G c hc D (Q+2) d (by omega) hscale hdegree hlen.le
  have hAM (i:ℕ) (hi:i ∈ A) : i ≤ M:= (hAP i hi).1.le
  have hparA (i:ℕ) (hi:i ∈ A) (j:ℕ) (hj:j ∈ A) : i%2=j%2:=by
    have hiE:=natEI.mp (hAP i hi).2
    have hjE:=natEI.mp (hAP j hj).2
    omega
  let E :=W \ c.support.toFinset
  by_cases hext:Q ≤ E.card
  · obtain ⟨Y,hYE,hY⟩ :=exists_subset_card_eq hext
    have hYW:Y ⊆ W:=hYE.trans sdiff_subset
    have hYoff (y:V) (hy:y ∈ Y) : y ∉ c.support:=by
      intro hyc
      exact (mem_sdiff.mp (hYE hy)).2 (lsMT.mpr hyc)
    let X :=A.image c.getVert
    have hcomp (x:V) (hx:x ∈ X) (y:V) (hy:y ∈ Y) : G.Adj x y:=by
      obtain ⟨i,hi,rfl⟩ :=mem_image.mp hx
      exact hcomplete i hi y (hYW hy)
    have hXY:Disjoint X Y:=by
      rw [fsDL]
      intro x hx hy
      exact (hcomp x hx x hy).ne rfl
    obtain ⟨u,hu,v,hv,huv,p,hp,hpL,hpPar,hpOff⟩ :=
      vx c hc A (by omega) M hlen hAM hparA Y hYoff
    exact ⟨X,Y,hAX,hY,hXY,hcomp,u,hu,v,hv,huv,p,hp,
      by omega,hpPar,hpOff⟩
  · have hK:0 < K:=by dsimp [K,rl];positivity
    obtain ⟨U,hUW,hUC,hUoff,hUsize⟩ :=xB c W
      (ftCard V) K Q M hlen.le hWsize hNloss (Nat.lt_of_not_ge hext)
    have hcN:c.length ≤ ftCard V :=by
      have h :=hc.isPath_tail.length_lt
      rw [wkLT] at h
      have hlen3:=hc.three_le_length
      omega
    obtain ⟨B,hB,hBM,hblock⟩ :=ys c hc U hUC M
      (ftCard V) K (Q+3) hK (by omega) hNblock hcN hUsize hUoff
    have hcomp (i:ℕ) (hi:i ∈ A) (j:ℕ) (hj:j ∈ B) :
        G.Adj (c.getVert i) (c.getVert j) :=hcomplete i hi _ (hUW (hBM j hj).2.2)
    exact vg c hc A B Q M H hQ hA hB hlen hAM
      (fun j hj=> ⟨(hBM j hj).1,(hBM j hj).2.1⟩) hparA
      (fun i hi j hj=> (hblock i hi j hj).1) (fun i hi j hj=> (hblock i hi j hj).2) hcomp
end Erdos556
namespace Erdos556
open SimpleGraph
theorem zg {V:Type*} {G:SimpleGraph V} {u v :V}
    (p:G.Walk u v) (hp:p.IsPath) (i j :ℕ) (hij:i < j) (hj:j ≤ p.length)
    (x:V) (hx:x ∉ p.support) (hix:G.Adj (p.getVert i) x)
    (hjx:G.Adj (p.getVert j) x) :
    ∃ q :G.Walk u v,q.IsPath ∧ q.length+j=p.length+i+2 ∧
      ∀ z ∈ q.support,z ∈ p.support ∨ z=x:=by
  have hi:i ≤ p.length:=hij.le.trans hj
  have hpre (z:V) (hz:z ∈ (p.take i).support) : z ∈ p.support:=by
    obtain ⟨a,_,hax⟩ := (qz p i hi).mp hz
    exact hax ▸ p.getVert_mem_support a
  have hpost (z:V) (hz:z ∈ (p.drop j).support) : z ∈ p.support:=by
    obtain ⟨a,_,_,hax⟩ := (rd p j hj).mp hz
    exact hax ▸ p.getVert_mem_support a
  let a :G.Walk u x:= (p.take i).concat hix
  let b :G.Walk x v:=wkCons hjx.symm (p.drop j)
  have ha:a.IsPath:= (hp.take i).concat (fun h => hx (hpre x h)) hix
  have hb:b.IsPath:= (wkCII _ _).mpr
    ⟨hp.drop j,fun h => hx (hpost x h)⟩
  have hab: (a.append b).IsPath:=by
    apply qr a b ha hb
    intro z hza hzb
    simp only [a,wkSC,lsMA,lsMS] at hza
    simp only [b,wkSC2,lsMC] at hzb
    rcases hza with hza | hzx
    · rcases hzb with hzx | hzb
      · exact hzx
      · exact ((vJ p hp i j hij hj) hza hzb).elim
    · exact hzx
  refine ⟨a.append b,hab,?_,?_⟩
  · simp only [a,b,wkLA,wkLC,wkLC2,
      wkTL,min_eq_left hi,wkDL]
    omega
  · intro z hz
    rcases (wkMSAI a b).mp hz with hz | hz
    · simp only [a,wkSC,lsMA,lsMS] at hz
      exact hz.elim (fun h => orInl (hpre z h)) orInr
    · simp only [b,wkSC2,lsMC] at hz
      exact hz.elim orInr (fun h => orInl (hpost z h))
theorem v7 {V:Type*} {G:SimpleGraph V} {u v :V}
    (p:G.Walk u v) (hp:p.IsPath) (i j :ℕ) (hij:i+4 ≤ j)
    (hj:j ≤ p.length) (hpar:i%2=j%2)
    (x:V) (hx:x ∉ p.support) (hix:G.Adj (p.getVert i) x)
    (hjx:G.Adj (p.getVert j) x) :
    ∃ q :G.Walk u v,q.IsPath ∧ q.length < p.length ∧
      p.length ≤ q.length+ (j-i) ∧ q.length%2=p.length%2 ∧
      ∀ z ∈ q.support,z ∈ p.support ∨ z=x:=by
  obtain ⟨q,hq,hlen,hs⟩ :=zg p hp i j (by omega) hj x hx hix hjx
  exact ⟨q,hq,by omega,by omega,by omega,hs⟩
theorem zm {V:Type*} {G:SimpleGraph V} {u v :V}
    (p:G.Walk u v) (hp:p.IsPath) (i i' j j':ℕ)
    (hii:i < i') (hij:i' ≤ j) (hjj:j < j') (hj':j' ≤ p.length)
    (hchord₁:G.Adj (p.getVert i) (p.getVert j))
    (hchord₂:G.Adj (p.getVert i') (p.getVert j')) :
    ∃ q :G.Walk u v,q.IsPath ∧ q.length+i'+j'=p.length+i+j+2 ∧
      ∀ z ∈ q.support,z ∈ p.support:=by
  have hi:i ≤ p.length:=by omega
  have hi':i' ≤ p.length:=by omega
  have hj:j ≤ p.length:=by omega
  let a := (p.take i).concat hchord₁
  let b := (sX p i' j hij).reverse
  let c :=wkCons hchord₂ (p.drop j')
  have hbmem (z:V) (hz:z ∈ b.support) :
      ∃ k,i' ≤ k ∧ k ≤ j ∧ p.getVert k =z:=by
    apply (vo p i' j hij hj).mp
    simpa only [b,wkSR,lsMR] using hz
  have ha:a.IsPath:=by
    apply (hp.take i).concat
    intro hz
    obtain ⟨k,hk,hkj⟩ := (qz p i hi).mp hz
    have hkj':=hp.getVert_injOn (by change k ≤ p.length;omega) hj hkj
    omega
  have hb:b.IsPath:= (aj p hp i' j hij).reverse
  have hab: (a.append b).IsPath:=by
    apply qr a b ha hb
    intro z hza hzb
    simp only [a,wkSC,lsMA,lsMS] at hza
    rcases hza with hza | hzj
    · obtain ⟨k,hk,hkz⟩ := (qz p i hi).mp hza
      obtain ⟨l,hil,hlj,hlz⟩ :=hbmem z hzb
      have hkl:=hp.getVert_injOn (by change k ≤ p.length;omega)
        (by change l ≤ p.length;omega) (hkz.trans hlz.symm)
      omega
    · exact hzj
  have hc:c.IsPath:=by
    apply (wkCII _ _).mpr
    refine ⟨hp.drop j',?_⟩
    intro hz
    obtain ⟨k,hjk,hk,hki⟩ := (rd p j' hj').mp hz
    have hki':=hp.getVert_injOn hk hi' hki
    omega
  have habpre (z:V) (hz:z ∈ (a.append b).support) : z ∈ (p.take j).support:=by
    apply (qz p j hj).mpr
    rcases (wkMSAI a b).mp hz with hza | hzb
    · simp only [a,wkSC,lsMA,lsMS] at hza
      rcases hza with hza | hzj
      · obtain ⟨k,hk,hkz⟩ := (qz p i hi).mp hza
        exact ⟨k,by omega,hkz⟩
      · exact ⟨j,le_rfl,hzj.symm⟩
    · obtain ⟨k,_,hk,hkz⟩ :=hbmem z hzb
      exact ⟨k,hk,hkz⟩
  have hpath: ((a.append b).append c).IsPath:=by
    apply qr (a.append b) c hab hc
    intro z hzab hzc
    simp only [c,wkSC2,lsMC] at hzc
    rcases hzc with hzi | hzc
    · exact hzi
    · exact ((vJ p hp j j' hjj hj') (habpre z hzab) hzc).elim
  refine ⟨(a.append b).append c,hpath,?_,?_⟩
  · simp only [a,b,c,wkLA,wkLC,wkTL,
      min_eq_left hi,wkLR,y2 p i' j hij hj,
      wkLC2,wkDL]
    omega
  · intro z hz
    rcases (wkMSAI (a.append b) c).mp hz with hzab | hzc
    · obtain ⟨k,_,hkz⟩ := (qz p j hj).mp (habpre z hzab)
      exact hkz ▸ p.getVert_mem_support k
    · simp only [c,wkSC2,lsMC] at hzc
      rcases hzc with hzi | hzc
      · exact hzi ▸ p.getVert_mem_support i'
      · obtain ⟨k,_,_,hkz⟩ := (rd p j' hj').mp hzc
        exact hkz ▸ p.getVert_mem_support k
theorem vf {V:Type*} {G:SimpleGraph V} {u v :V}
    (p:G.Walk u v) (hp:p.IsPath) (i i' j j':ℕ)
    (hii:i+4 ≤ i') (hij:i' ≤ j) (hjj:j+2 ≤ j') (hj':j' ≤ p.length)
    (hpar₁:i%2=i'%2) (hpar₂:j%2=j'%2)
    (hchord₁:G.Adj (p.getVert i) (p.getVert j))
    (hchord₂:G.Adj (p.getVert i') (p.getVert j')) :
    ∃ q :G.Walk u v,q.IsPath ∧ q.length < p.length ∧
      p.length ≤ q.length+ (i'-i) + (j'-j) ∧
      q.length%2=p.length%2 ∧ ∀ z ∈ q.support,z ∈ p.support:=by
  obtain ⟨q,hq,hlen,hs⟩ :=zm p hp i i' j j'
    (by omega) hij (by omega) hj' hchord₁ hchord₂
  exact ⟨q,hq,by omega,by omega,by omega,hs⟩
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem u8 {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (D d :ℕ) (hD:0 < D)
    (hscale:ftCard V ≤ D *d) (hdegree: ∀ v,d ≤ G.degree v)
    (hN:8* (4*D) ^ 2 ≤ ftCard V)
    (R:Finset V) (hR:2* (R.card+16*D+1) ≤ d)
    {u v :V} (p:G.Walk u v) (hp:p.IsPath) (hlen:16*D ≤ p.length) :
    ∃ q :G.Walk u v,q.IsPath ∧ q.length < p.length ∧
      p.length ≤ q.length+ (16*D+8* (4*D) ^ 2) ∧
      q.length%2=p.length%2 ∧
      ∀ z ∈ q.support,z ∈ p.support ∨ z ∉ R:=by
  classical
  let S :=R ∪ (p.take (16*D)).support.toFinset
  have hprefix: (p.take (16*D)).support.toFinset.card ≤ 16*D+1:=by
    have h :=lsTCL (p.take (16*D)).support
    simpa only [wkLS,wkTL,min_eq_left hlen] using h
  have hS:2*S.card ≤ d:=by
    have h :=card_union_le R (p.take (16*D)).support.toFinset
    change S.card ≤ R.card+ (p.take (16*D)).support.toFinset.card at h
    omega
  let a (i:Fin (4*D)) :=p.getVert (4*i.val)
  have hpositive:0 < ftCard V :=by nlinarith
  obtain ⟨i₀,j₀,hne,hc⟩ :=vN G D d hpositive
    hscale hdegree S hS a
  have hordered: ∃ i j:Fin (4*D),i.val < j.val ∧
      ftCard V / (2* (4*D) ^ 2) <
        ((G.neighborFinset (a i) ∩ G.neighborFinset (a j)) \ S).card:=by
    have hne':i₀.val ≠ j₀.val:=fun h => hne (Fin.ext h)
    rcases lt_or_gt_of_ne hne' with hij | hji
    · exact ⟨i₀,j₀,hij,hc⟩
    · refine ⟨j₀,i₀,hji,?_⟩
      rwa [inter_comm]
  obtain ⟨i,j,hij,hcommon⟩ :=hordered
  let W := (G.neighborFinset (a i) ∩ G.neighborFinset (a j)) \ S
  have hmem (x:V) (hx:x ∈ W) :
      G.Adj (p.getVert (4*i.val)) x ∧ G.Adj (p.getVert (4*j.val)) x ∧ x ∉ S :=by
    obtain ⟨hxij,hxS⟩ :=mem_sdiff.mp hx
    obtain ⟨hxi,hxj⟩ :=mem_inter.mp hxij
    exact ⟨(G.mem_neighborFinset _ _).mp hxi,(G.mem_neighborFinset _ _).mp hxj,hxS⟩
  have h4j:4*j.val ≤ p.length:=by have h :=j.isLt;omega
  have h4i:4*i.val+4 ≤ 4*j.val:=by omega
  have hpar: (4*i.val) % 2= (4*j.val) % 2:=by omega
  by_cases hex: ∃ x ∈ W,x ∉ p.support
  · obtain ⟨x,hxW,hx⟩ :=hex
    obtain ⟨hix,hjx,hxS⟩ :=hmem x hxW
    have hxR:x ∉ R:=fun h => hxS (mem_union_left _ h)
    obtain ⟨q,hq,hlt,hbound,hparq,hsupport⟩ :=
      v7 p hp (4*i.val) (4*j.val)
        h4i h4j hpar x hx hix hjx
    refine ⟨q,hq,hlt,?_,hparq,?_⟩
    · have hjlt:=j.isLt
      omega
    · intro z hz
      rcases hsupport z hz with hzp | hzx
      · exact orInl hzp
      · exact orInr (hzx ▸ hxR)
  · have hW: ∀ x ∈ W,x ∈ p.support:=by
      intro x hx
      by_contra h
      exact hex ⟨x,hx,h⟩
    have hK:0 < 2* (4*D) ^ 2:=by positivity
    have hN':4* (2* (4*D) ^ 2) ≤ ftCard V :=by nlinarith only [hN]
    obtain ⟨s,t,hst,ht,hclose,hparst,hsW,htW⟩ :=
      vE p W hW (ftCard V)
        (2* (4*D) ^ 2) hK hN' hp.length_lt hcommon
    have hs:16*D < s:=by
      by_contra h
      have hs':s ≤ 16*D:=by omega
      have hsP:p.getVert s ∈ (p.take (16*D)).support:=
        (qz p (16*D) hlen).mpr ⟨s,hs',rfl⟩
      exact (hmem _ hsW).2.2 (mem_union_right R (lsMT.mpr hsP))
    have hst2:s+2 ≤ t:=by omega
    have hjs:4*j.val ≤ s:=by have hjlt:=j.isLt;omega
    obtain ⟨q,hq,hlt,hbound,hparq,hsupport⟩ :=
      vf p hp (4*i.val) (4*j.val) s t
        h4i hjs hst2 ht hpar hparst (hmem _ hsW).1 (hmem _ htW).2.1
    refine ⟨q,hq,hlt,?_,hparq,fun z hz=> orInl (hsupport z hz)⟩
    have hjlt:=j.isLt
    omega
end Erdos556
namespace Erdos556
open SimpleGraph
theorem zu {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (D d :ℕ) (hD:0 < D)
    (hscale:ftCard V ≤ D *d) (hdegree: ∀ v,d ≤ G.degree v)
    (hN:8* (4*D) ^ 2 ≤ ftCard V)
    (R:Finset V) (hR:2* (R.card+16*D+1) ≤ d)
    (t:ℕ) (ht:16*D ≤ t) {u v :V}
    (p:G.Walk u v) (hp:p.IsPath) (hlen:t ≤ p.length)
    (hoff: ∀ z ∈ p.support,z ∈ R → z=u ∨ z=v) :
    ∃ q :G.Walk u v,q.IsPath ∧ q.length ≤ t ∧
      t < q.length+ (16*D+8* (4*D) ^ 2) ∧
      q.length%2=p.length%2 ∧
      ∀ z ∈ q.support,z ∈ R → z=u ∨ z=v:=by
  classical
  have aux: ∀ M:ℕ,∀ p:G.Walk u v,p.length=M → p.IsPath → t ≤ p.length →
      (∀ z ∈ p.support,z ∈ R → z=u ∨ z=v) →
      ∃ q :G.Walk u v,q.IsPath ∧ q.length ≤ t ∧
        t < q.length+ (16*D+8* (4*D) ^ 2) ∧
        q.length%2=p.length%2 ∧
        ∀ z ∈ q.support,z ∈ R → z=u ∨ z=v:=by
    intro M
    induction M using natSIO with
    | h M ih=>
        intro p hpM hp htP hoff
        by_cases hstop:p.length ≤ t
        · exact ⟨p,hp,hstop,by omega,rfl,hoff⟩
        obtain ⟨q,hq,hlt,hbound,hpar,hsupp⟩ :=
          u8 G D d hD hscale hdegree hN R hR
            p hp (by omega)
        have hoffq: ∀ z ∈ q.support,z ∈ R → z=u ∨ z=v:=by
          intro z hz hzR
          rcases hsupp z hz with hzp | hzoff
          · exact hoff z hzp hzR
          · exact (hzoff hzR).elim
        by_cases htq:t ≤ q.length
        · obtain ⟨w,hw,hwt,hwin,hwpar,hwoff⟩ :=
            ih q.length (by omega) q rfl hq htq hoffq
          exact ⟨w,hw,hwt,hwin,hwpar.trans hpar,hwoff⟩
        · exact ⟨q,hq,by omega,by omega,hpar,hoffq⟩
  exact aux p.length p rfl hp hlen hoff
end Erdos556
namespace Erdos556
open SimpleGraph
theorem yP {V:Type*} {G:SimpleGraph V}
    {u v :V} (p:G.Walk u v) (hp:p.length=G.dist u v)
    {i j :ℕ} (hij:i ≤ j) (hj:j ≤ p.length) :
    G.dist (p.getVert i) (p.getVert j) = j-i:=by
  have hsub:= ((p.take j).isSubwalk_drop i).trans (p.isSubwalk_take j)
  have h :=length_eq_dist_of_subwalk hp hsub
  simpa only [wkDL,wkTL,Walk.take_getVert,
    inf_eq_left.mpr hj,inf_eq_right.mpr hij] using h.symm
theorem sx {V:Type*} {G:SimpleGraph V}
    {u v :V} (p:G.Walk u v) (hp:p.length=G.dist u v)
    {i j :ℕ} (hij:i+3 ≤ j) (hj:j ≤ p.length) (z:V) :
    ¬ (G.Adj (p.getVert i) z ∧ G.Adj (p.getVert j) z) :=by
  rintro ⟨hi,hjz⟩
  have hdist:=G.dist_le (wkCons hi (wkCons hjz.symm Walk.nil))
  rw [yP p hp (by omega) hj] at hdist
  simp only [wkLC2,Walk.length_nil] at hdist
  omega
theorem sU {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] {u v :V} (p:G.Walk u v)
    (hp:p.length=G.dist u v) (d:ℕ) (hdeg: ∀ w,d ≤ G.degree w) :
    (p.length/3+1) * d ≤ ftCard V :=by
  classical
  let I :=Fin (p.length/3+1)
  let W (i:I) :=G.neighborSet (p.getVert (3*i.val))
  let f : (Σ i :I,W i) → V:=fun x => x.2.val
  have hindex (i:I) : 3*i.val ≤ p.length:=by
    have hi:=i.isLt
    omega
  have hinj:Function.Injective f :=by
    rintro ⟨i,x⟩ ⟨j,y⟩ hxy
    have hij:i=j:=by
      by_contra hne
      have hval:i.val ≠ j.val:=fun h => hne (Fin.ext h)
      rcases lt_or_gt_of_ne hval with hij | hji
      · apply sx p hp
          (i:=3*i.val) (j:=3*j.val) (by omega) (hindex j) x.val
        refine ⟨x.property,?_⟩
        have heq:x.val=y.val:=hxy
        rw [heq]
        exact y.property
      · apply sx p hp
          (i:=3*j.val) (j:=3*i.val) (by omega) (hindex i) y.val
        refine ⟨y.property,?_⟩
        have heq:x.val=y.val:=hxy
        rw [← heq]
        exact x.property
    subst j
    have heq:x=y:=subExt hxy
    subst y
    rfl
  have hc:=ftCLOI f hinj
  have hsum: (p.length/3+1) * d ≤ ftCard (Σ i :I,W i) :=by
    rw [Fintype.card_sigma]
    calc
      (p.length/3+1) * d= ∑ _i:I,d:=by simp [I]
      _ ≤ ∑ i :I,ftCard (W i) :=by
        apply fsSLS
        intro i _
        simpa only [W,card_neighborSet_eq_degree] using hdeg (p.getVert (3*i.val))
  exact hsum.trans hc
theorem xD {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (hconn:G.Connected)
    (d:ℕ) (hd:0 < d) (hdeg: ∀ w,d ≤ G.degree w) (u v :V) :
    ∃ p :G.Walk u v,p.IsPath ∧ d*p.length < 3*ftCard V :=by
  classical
  obtain ⟨p,hp,hdist⟩ :=hconn.exists_path_of_dist u v
  refine ⟨p,hp,?_⟩
  have hc:=sU G p hdist d hdeg
  have hlen:p.length < 3* (p.length/3+1) :=by omega
  nlinarith
end Erdos556
namespace Erdos556
open SimpleGraph Finset
def q8 {V:Type*} (G:SimpleGraph V) (b:ℕ) : Prop:=
  ∀ S :Finset V,S.card ≤ b → (G.induce (S:Set V)ᶜ).Preconnected
theorem q8.mono {V:Type*} {G:SimpleGraph V} {a b :ℕ}
    (h:q8 G b) (hab:a ≤ b) : q8 G a:=
  fun S hS=> h S (hS.trans hab)
theorem qW {V:Type*} [Fintype V]
    [DecidableEq V] (G:SimpleGraph V) [DecidableRel G.Adj]
    (S:Finset V) (v: ↥((S:Set V)ᶜ)) :
    G.degree v.val ≤ (G.induce (S:Set V)ᶜ).degree v +S.card:=by
  classical
  have hdeg: (G.induce (S:Set V)ᶜ).degree v =
      (G.neighborFinset v.val \ S).card:=by
    have h :=congrArg fsCard (G.map_neighborFinset_induce v)
    simpa [← sdiff_eq_inter_compl] using h
  rw [hdeg,← G.card_neighborFinset_eq_degree v.val]
  have h :=card_sdiff_add_card_inter (G.neighborFinset v.val) S
  have hle:=card_le_card (inter_subset_right (s₁:=G.neighborFinset v.val) (s₂:=S))
  omega
theorem sB {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (b d :ℕ)
    (hconn:q8 G b) (hd:0 < d)
    (hdeg: ∀ w,d+b ≤ G.degree w) (S:Finset V) (hS:S.card ≤ b)
    (u v :V) (hu:u ∉ S) (hv:v ∉ S) :
    ∃ p :G.Walk u v,p.IsPath ∧ d*p.length < 3*ftCard V ∧
      ∀ x ∈ p.support,x ∉ S:=by
  classical
  let U := (S:Set V)ᶜ
  let u':U:= ⟨u,hu⟩
  let v':U:= ⟨v,hv⟩
  let:Nonempty U := ⟨u'⟩
  have hc: (G.induce U).Connected:= ⟨hconn S hS⟩
  have hmin (w:U) : d ≤ (G.induce U).degree w :=by
    have h :=qW G S w
    have hg:=hdeg w.val
    change G.degree w.val ≤ (G.induce U).degree w +S.card at h
    omega
  obtain ⟨p,hp,hlen⟩ :=xD
    (G.induce U) hc d hd hmin u' v'
  let f :G.induce U ↪g G :=sgInduce U
  refine ⟨p.map f.toHom,hp.map f.injective,?_,?_⟩
  · change d * (p.map f.toHom).length < 3*ftCard V
    simp only [wkLM]
    exact hlen.trans_le (natMLML 3 (ftCLOI
      (fun x :U=> x.val) subVI))
  · intro x hx
    change x ∈ (p.map f.toHom).support at hx
    rw [wkSM,lsMM] at hx
    obtain ⟨y,_,hy⟩ :=hx
    subst x
    exact y.property
end Erdos556
namespace Erdos556
open SimpleGraph
theorem uX {V:Type*} {G:SimpleGraph V}
    {v:V} (p:G.Walk v v) (hp:Odd p.length) :
    ∃ (w:V) (q:G.Walk w w),q.IsCycle ∧ Odd q.length ∧ q.length ≤ p.length:=by
  classical
  let P (m:ℕ) : Prop:= ∃ (w:V) (q:G.Walk w w),Odd q.length ∧ q.length=m
  have hex: ∃ m,P m:= ⟨p.length,v,p,hp,rfl⟩
  obtain ⟨w,q,hodd,hlen⟩ :=Nat.find_spec hex
  have hmin {z:V} (r:G.Walk z z) (hr:Odd r.length) : q.length ≤ r.length:=by
    rw [hlen]
    exact Nat.find_min' hex ⟨z,r,hr,rfl⟩
  have hnotnil: ¬ q.Nil:=by
    rw [Walk.not_nil_iff_lt_length]
    have hmod:=natOI.mp hodd
    omega
  have htail:q.tail.IsPath:=by
    apply Walk.isPath_iff_isSubwalk_imp_nil.mpr
    intro z r hr
    by_contra hrnil
    have hrpos:0 < r.length:=Walk.not_nil_iff_lt_length.mp hrnil
    have hrle:=Walk.length_le_of_isSubwalk hr
    rw [wkLT] at hrle
    by_cases hrodd:Odd r.length
    · have:=hmin r hrodd
      omega
    · obtain ⟨a,b,hab⟩ :=hr
      have htotal:q.length=a.length+r.length+b.length+1:=by
        have h :=congrArg Walk.length hab
        simp only [wkLT,wkLA] at h
        have hpos:=Walk.not_nil_iff_lt_length.mp hnotnil
        omega
      let s :=wkCons (q.adj_snd hnotnil) (a.append b)
      have hslen:s.length=a.length+b.length+1:=by
        simp only [s,wkLC2,wkLA]
      have hsodd:Odd s.length:=by
        have hqmod:=natOI.mp hodd
        have hrmod:=natEI.mp (Nat.not_odd_iff_even.mp hrodd)
        apply natOI.mpr
        omega
      have:=hmin s hsodd
      omega
  have hthree:3 ≤ q.length:=by
    have hne:q.length ≠ 1:=fun h => (Walk.adj_of_length_eq_one h).ne rfl
    have hmod:=natOI.mp hodd
    omega
  exact ⟨w,q,Walk.isCycle_iff_isPath_tail_and_le_length.mpr ⟨htail,hthree⟩,
    hodd,hmin p hp⟩
theorem xJ {V:Type*} (G:SimpleGraph V) :
    G.Colorable 2 ↔ ∀ (v:V) (p:G.Walk v v),p.IsCycle → ¬ Odd p.length:=by
  rw [two_colorable_iff_forall_loop_even]
  constructor
  · intro h v p _ ho
    exact (Nat.not_even_iff_odd.mpr ho) (h v p)
  · intro h v p
    apply Nat.not_odd_iff_even.mp
    intro ho
    obtain ⟨w,q,hq,hodd,_⟩ :=uX p ho
    exact h w q hq hodd
theorem tr {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (hconn:G.Connected)
    (hnonbip: ¬ G.Colorable 2) (d:ℕ) (hd:0 < d)
    (hdeg: ∀ v,d ≤ G.degree v) :
    ∃ (w:V) (q:G.Walk w w),q.IsCycle ∧ Odd q.length ∧
      d*q.length < 6*ftCard V +d:=by
  classical
  let root:V:=Classical.choice hconn.nonempty
  let f (v:V) : Fin 2 := ⟨G.dist root v %2,natML _ (by decide)⟩
  have hex: ∃ a b,G.Adj a b ∧ f a =f b:=by
    by_contra h
    push Not at h
    apply hnonbip
    exact ⟨{ toFun:=f,map_rel':=fun {a b} hab=> h a b hab}⟩
  obtain ⟨a,b,hab,hpar⟩ :=hex
  obtain ⟨pa,_,hpa⟩ :=hconn.exists_path_of_dist root a
  obtain ⟨pb,_,hpb⟩ :=hconn.exists_path_of_dist root b
  have hshort {x y :V} (r:G.Walk x y) (hr:r.length=G.dist x y) :
      d*r.length < 3*ftCard V :=by
    have hc:=sU G r hr d hdeg
    have hlen:r.length < 3* (r.length/3+1) :=by omega
    nlinarith
  have ha:=hshort pa hpa
  have hb:=hshort pb hpb
  let p := (pa.concat hab).append pb.reverse
  have hlen:p.length=pa.length+1+pb.length:=by
    simp only [p,wkLA,wkLC,wkLR]
  have hodd:Odd p.length:=by
    have heq:=congrArg Fin.val hpar
    change G.dist root a %2=G.dist root b %2 at heq
    rw [← hpa,← hpb] at heq
    apply natOI.mpr
    omega
  have hbound:d*p.length < 6*ftCard V +d:=by nlinarith
  obtain ⟨w,q,hq,hqodd,hqle⟩ :=uX p hodd
  exact ⟨w,q,hq,hqodd,(natMLML d hqle).trans_lt hbound⟩
end Erdos556
namespace Erdos556
open SimpleGraph
def qT {V:Type*} (G:SimpleGraph V) (b:ℕ) : Prop:=
  ∀ S :Finset V,S.card ≤ b → ¬ (G.induce (S:Set V)ᶜ).Colorable 2
theorem z3 {V:Type*} (G:SimpleGraph V)
    (h: ¬ G.Colorable 2) : Nonempty V :=by
  by_contra hn
  have:IsEmpty V :=not_nonempty_iff.mp hn
  apply h
  refine ⟨{ toFun:=fun x => isEmptyElim x,map_rel':= ?_}⟩
  intro x
  exact isEmptyElim x
theorem xA {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (b d :ℕ)
    (hconn:q8 G b) (hnonbip:qT G b)
    (hd:0 < d) (hdeg: ∀ w,d+b ≤ G.degree w)
    (S:Finset V) (hS:S.card ≤ b) :
    ∃ (w:V) (c:G.Walk w w),c.IsCycle ∧ Odd c.length ∧
      d*c.length < 6*ftCard V +d ∧ ∀ x ∈ c.support,x ∉ S:=by
  classical
  let U := (S:Set V)ᶜ
  have hnb: ¬ (G.induce U).Colorable 2 :=hnonbip S hS
  have:Nonempty U :=z3 _ hnb
  have hc: (G.induce U).Connected:= ⟨hconn S hS⟩
  have hmin (v:U) : d ≤ (G.induce U).degree v :=by
    have h :=qW G S v
    have hg:=hdeg v.val
    change G.degree v.val ≤ (G.induce U).degree v +S.card at h
    omega
  obtain ⟨w,c,hcyc,hodd,hlen⟩ :=tr (G.induce U) hc hnb d hd hmin
  let f :G.induce U ↪g G :=sgInduce U
  refine ⟨f w,c.map f.toHom,hcyc.map f.injective,?_,?_,?_⟩
  · simpa only [wkLM] using hodd
  · simp only [wkLM]
    have hcard:=ftCLOI (fun x :U=> x.val) subVI
    omega
  · intro x hx
    rw [wkSM,lsMM] at hx
    obtain ⟨y,_,hy⟩ :=hx
    subst x
    exact y.property
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem wX {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (b d D:ℕ)
    (hconn:q8 G b) (hd:0 < d)
    (hdeg: ∀ w,d+b ≤ G.degree w) (hN:ftCard V ≤ D *d)
    (S:Finset V) (hbudget:S.card+3*D+1 ≤ b)
    (C:Set V) (hC:C.Nontrivial) (hCS: ∀ z ∈ C,z ∉ S)
    (u v :V) (hu:u ∉ S) (hv:v ∉ S) (huv:u ≠ v) :
    ∃ x ∈ C,∃ y ∈ C,∃ (p:G.Walk u x) (q:G.Walk v y),
      p.IsPath ∧ q.IsPath ∧ p.length < 3*D ∧ q.length < 3*D ∧ x ≠ y ∧
      (∀ z ∈ p.support,z ∈ C → z=x) ∧
      (∀ z ∈ q.support,z ∈ C → z=y) ∧
      (∀ z ∈ p.support,z ∉ q.support) ∧
      (∀ z ∈ p.support,z ∉ S) ∧ (∀ z ∈ q.support,z ∉ S) :=by
  classical
  obtain ⟨w,hwC,hwv⟩ :=hC.exists_ne v
  have hfirst: (insert v S).card ≤ b:= (card_insert_le v S).trans (by omega)
  obtain ⟨p',hp',hplen,hpavoid⟩ :=sB G b d hconn hd hdeg
    (insert v S) hfirst u w (by simpa using And.intro huv hu)
    (by simpa using And.intro hwv (hCS w hwC))
  obtain ⟨x,hxC,p,hp,hpp',hpsub,hpC⟩ :=rq p' hp' C hwC
  have hpbound:p.length < 3*D:=by nlinarith
  have hpav (z:V) (hz:z ∈ p.support) : z ∉ insert v S:=
    hpavoid z (hpsub hz)
  have hpcard:p.support.toFinset.card ≤ 3*D:=by
    have hcard:=lsTCL p.support
    rw [p.length_support] at hcard
    omega
  let T :=S ∪ p.support.toFinset
  have hT:T.card ≤ b:= (card_union_le S p.support.toFinset).trans (by omega)
  obtain ⟨z,hzC,hzx⟩ :=hC.exists_ne x
  have hzT:z ∉ T:=by
    simp only [T,mem_union,lsMT,not_or]
    exact ⟨hCS z hzC,fun h => hzx (hpC z h hzC)⟩
  have hvT:v ∉ T:=by
    simp only [T,mem_union,lsMT,not_or]
    exact ⟨hv,fun h => hpav v h (mem_insert_self v S)⟩
  obtain ⟨q',hq',hqlen,hqavoid⟩ :=sB G b d hconn hd hdeg
    T hT v z hvT hzT
  obtain ⟨y,hyC,q,hq,hqq',hqsub,hqC⟩ :=rq q' hq' C hzC
  have hqbound:q.length < 3*D:=by nlinarith
  have hqav (z:V) (hz:z ∈ q.support) : z ∉ T:=hqavoid z (hqsub hz)
  have hpq (z:V) (hzp:z ∈ p.support) (hzq:z ∈ q.support) : False:=
    hqav z hzq (mem_union_right S (lsMT.mpr hzp))
  have hxy:x ≠ y:=by
    intro h
    exact hpq x p.end_mem_support (h ▸ q.end_mem_support)
  refine ⟨x,hxC,y,hyC,p,q,hp,hq,hpbound,hqbound,hxy,hpC,hqC,hpq,?_,?_⟩
  · intro z hz hzS
    exact hpav z hz (mem_insert_of_mem hzS)
  · intro z hz hzS
    exact hqav z hz (mem_union_left _ hzS)
end Erdos556
namespace Erdos556
open SimpleGraph
theorem zH {V:Type*} {G:SimpleGraph V}
    {w:V} (c:G.Walk w w) (hc:c.IsCycle) (hodd:Odd c.length)
    (u v :V) (hu:u ∈ c.support) (hv:v ∈ c.support) (huv:u ≠ v) :
    ∃ p q:G.Walk u v,p.IsPath ∧ q.IsPath ∧
      p.length+q.length=c.length ∧ p.length%2 ≠ q.length%2 ∧
      p.support ⊆ c.support ∧ q.support ⊆ c.support:=by
  classical
  let r :=c.rotate u hu
  have hr:r.IsCycle:=hc.rotate hu
  have hvr:v ∈ r.support:= (c.mem_support_rotate_iff u hu).mpr hv
  let p :=r.takeUntil v hvr
  let s :=r.dropUntil v hvr
  have hp:p.IsPath:=hr.isPath_takeUntil hvr
  have hs:s.IsPath:=by
    have hcycle: (p.append s).IsCycle:=by
      simpa only [p,s,Walk.take_spec] using hr
    exact hcycle.isPath_of_append_right (wkNNON huv)
  have hlen:p.length+s.reverse.length=c.length:=by
    have h :=congrArg Walk.length (r.take_spec hvr)
    simpa only [wkLA,r,Walk.length_rotate,wkLR] using h
  refine ⟨p,s.reverse,hp,hs.reverse,hlen,?_,?_,?_⟩
  · have ho:=natOI.mp hodd
    omega
  · intro x hx
    exact (c.mem_support_rotate_iff u hu).mp (r.support_takeUntil_subset_support hvr hx)
  · intro x hx
    rw [wkSR,lsMR] at hx
    exact (c.mem_support_rotate_iff u hu).mp (r.support_dropUntil_subset_support hvr hx)
theorem rE {V:Type*} {G:SimpleGraph V}
    {w u v x y:V} (c:G.Walk w w) (hc:c.IsCycle) (hodd:Odd c.length)
    (p:G.Walk u x) (q:G.Walk v y) (hp:p.IsPath) (hq:q.IsPath)
    (hx:x ∈ c.support) (hy:y ∈ c.support) (hxy:x ≠ y)
    (hpC: ∀ z ∈ p.support,z ∈ c.support → z=x)
    (hqC: ∀ z ∈ q.support,z ∈ c.support → z=y)
    (hpq: ∀ z ∈ p.support,z ∉ q.support) :
    ∃ p₀ p₁:G.Walk u v,p₀.IsPath ∧ p₁.IsPath ∧
      p₀.length%2 ≠ p₁.length%2 ∧
      p₀.length ≤ p.length+q.length+c.length ∧
      p₁.length ≤ p.length+q.length+c.length ∧
      (∀ z ∈ p₀.support,z ∈ p.support ∨ z ∈ q.support ∨ z ∈ c.support) ∧
      (∀ z ∈ p₁.support,z ∈ p.support ∨ z ∈ q.support ∨ z ∈ c.support) :=by
  obtain ⟨a,b,ha,hb,hlen,hpar,haC,hbC⟩ :=
    zH c hc hodd x y hx hy hxy
  have hpath (r:G.Walk x y) (hr:r.IsPath) (hrC:r.support ⊆ c.support) :
      ((p.append r).append q.reverse).IsPath:=by
    have hpr:=qr p r hp hr
      (fun z hz hzr=> hpC z hz (hrC hzr))
    apply qr (p.append r) q.reverse hpr hq.reverse
    intro z hz hzq
    rw [wkSR,lsMR] at hzq
    rcases (wkMSAI _ _).mp hz with hzp | hzr
    · exact (hpq z hzp hzq).elim
    · exact hqC z hzq (hrC hzr)
  have hsupport (r:G.Walk x y) (hrC:r.support ⊆ c.support) (z:V)
      (hz:z ∈ ((p.append r).append q.reverse).support) :
      z ∈ p.support ∨ z ∈ q.support ∨ z ∈ c.support:=by
    rcases (wkMSAI _ _).mp hz with hzpr | hzq
    · rcases (wkMSAI _ _).mp hzpr with hzp | hzr
      · exact orInl hzp
      · exact orInr (orInr (hrC hzr))
    · exact orInr (orInl (by simpa only [wkSR,lsMR] using hzq))
  refine ⟨(p.append a).append q.reverse,(p.append b).append q.reverse,
    hpath a ha haC,hpath b hb hbC,?_,?_,?_,hsupport a haC,hsupport b hbC⟩
  · simp only [wkLA,wkLR]
    omega
  · simp only [wkLA,wkLR]
    omega
  · simp only [wkLA,wkLR]
    omega
end Erdos556
namespace Erdos556
open SimpleGraph Finset
def qZ {V:Type*} (G:SimpleGraph V) (L:ℕ) (u v :V)
    (S:Finset V) : Prop:=
  ∀ r :Fin 2,∃ p:G.Walk u v,p.IsPath ∧ p.length ≤ L ∧ p.length%2=r.val ∧
    ∀ x ∈ p.support,x ≠ u → x ≠ v → x ∈ S
theorem qZ.mono {V:Type*} {G:SimpleGraph V} {L:ℕ} {u v :V}
    {S T :Finset V} (h:qZ G L u v S) (hST:S ⊆ T) :
    qZ G L u v T :=by
  intro r
  obtain ⟨p,hp,hlen,hpar,hs⟩ :=h r
  exact ⟨p,hp,hlen,hpar,fun x hx hxu hxv=> hST (hs x hx hxu hxv)⟩
theorem vz {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (b d D:ℕ)
    (hconn:q8 G (b+3*D+3))
    (hnonbip:qT G (b+3*D+3))
    (hd:0 < d) (hdeg: ∀ w,d+ (b+3*D+3) ≤ G.degree w)
    (hN:ftCard V ≤ D *d) (u v :V) (huv:u ≠ v)
    (S:Finset V) (hS:S.card ≤ b) :
    ∃ T :Finset V,qZ G (12*D+3) u v T ∧
      T.card ≤ 12*D+3 ∧ Disjoint S T:=by
  classical
  let S₀:= (S.erase u).erase v
  have hS₀:S₀.card ≤ b:=
    (card_le_card ((erase_subset v (S.erase u)).trans (erase_subset u S))).trans hS
  let F :=insert u (insert v S₀)
  have hF:F.card ≤ b+3*D+3:=by
    have h1:=card_insert_le u (insert v S₀)
    have h2:=card_insert_le v S₀
    dsimp [F]
    omega
  obtain ⟨w,c,hc,hodd,hclen,hcav⟩ :=xA G
    (b+3*D+3) d hconn hnonbip hd hdeg F hF
  have hcshort:c.length ≤ 6*D:=by nlinarith
  let C :Set V := {z | z ∈ c.support}
  have hC:C.Nontrivial:=by
    refine ⟨w,c.start_mem_support,c.snd,?_,(c.adj_snd hc.not_nil).ne⟩
    exact lsMOMT (Walk.snd_mem_tail_support hc.not_nil)
  have hCS (z:V) (hz:z ∈ C) : z ∉ S₀:=by
    intro hzS
    exact hcav z hz (mem_insert_of_mem (mem_insert_of_mem hzS))
  obtain ⟨x,hxC,y,hyC,p,q,hp,hq,hplen,hqlen,hxy,hpC,hqC,hpq,hpav,hqav⟩ :=
    wX G (b+3*D+3) d D hconn hd hdeg hN
      S₀ (by omega) C hC hCS u v (by simp [S₀]) (by simp [S₀]) huv
  obtain ⟨p₀,p₁,hp₀,hp₁,hpar,hlen₀,hlen₁,hs₀,hs₁⟩ :=
    rE c hc hodd p q hp hq hxC hyC hxy hpC hqC hpq
  let U := (p.support.toFinset ∪ q.support.toFinset) ∪ c.support.toFinset
  let T := (U.erase u).erase v
  have hmem {z:V} (hz:z ∈ p.support ∨ z ∈ q.support ∨ z ∈ c.support)
      (hzu:z ≠ u) (hzv:z ≠ v) : z ∈ T:=by
    simp only [T,U,mem_erase,mem_union,lsMT]
    exact ⟨hzv,hzu,by tauto⟩
  have hTsize:T.card ≤ 12*D+3:=by
    have hTle:T.card ≤ U.card:=
      card_le_card ((erase_subset v (U.erase u)).trans (erase_subset u U))
    have hUle:U.card ≤ p.support.toFinset.card+q.support.toFinset.card+
        c.support.toFinset.card:=
      (card_union_le _ _).trans (natALAR (card_union_le _ _) _)
    have hpcard:=lsTCL p.support
    have hqcard:=lsTCL q.support
    have hccard:=lsTCL c.support
    rw [p.length_support] at hpcard
    rw [q.length_support] at hqcard
    rw [c.length_support] at hccard
    omega
  have hST:Disjoint S T:=by
    rw [fsDL]
    intro z hzS hzT
    simp only [T,U,mem_erase,mem_union,lsMT] at hzT
    have hzS₀:z ∈ S₀:=by
      simp only [S₀,mem_erase]
      exact ⟨hzT.1,hzT.2.1,hzS⟩
    rcases hzT.2.2 with (hzp | hzq) | hzc
    · exact hpav z hzp hzS₀
    · exact hqav z hzq hzS₀
    · exact hCS z hzc hzS₀
  refine ⟨T,?_,hTsize,hST⟩
  intro r
  by_cases h :p₀.length%2=r.val
  · exact ⟨p₀,hp₀,by omega,h,fun z hz hzu hzv=> hmem (hs₀ z hz) hzu hzv⟩
  · have hr:p₁.length%2=r.val:=by have:=r.isLt;omega
    exact ⟨p₁,hp₁,by omega,hr,fun z hz hzu hzv=> hmem (hs₁ z hz) hzu hzv⟩
end Erdos556
section cw
/-
Copyright 2026 The Lean-Proofs Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/
/-
# Elementary finite Bernoulli sampling
This self-contained finite-sum development is adapted from the proved
Bernoulli counting lemmas in `Erdos76/Kahn.lean` and
`Erdos76/FiniteBernoulliLocality.lean`. No local lemma or hypergraph theorem
is imported or assumed.
-/
namespace Erdos556.Bernoulli
open Finset
open scoped BigOperators
noncomputable section
open scoped Classical
def qv {Ω:Type*} [Fintype Ω] (mass:Ω → ℝ) (event:Ω → Prop) : ℝ:=
  ∑ x,if event x then mass x else 0
variable {E:Type*} [DecidableEq E]
def q9 (U:Finset E) (p:E → ℝ) (S:Finset E) : ℝ:=
  (∏ e ∈ S,p e) * ∏ e ∈ U \ S,(1-p e)
lemma yC (U:Finset E) (p:E → ℝ) :
    ∑ S ∈ U.powerset,q9 U p S =1:=by
  simp only [q9]
  rw [← prod_add]
  simp
lemma tO {U S :Finset E} {p:E → ℝ}
    (hS:S ⊆ U) (hp₀: ∀ e ∈ U,0 ≤ p e) (hp₁: ∀ e ∈ U,p e ≤ 1) :
    0 ≤ q9 U p S :=by
  apply mul_nonneg
  · exact prod_nonneg fun e he ↦ hp₀ e (hS he)
  · exact prod_nonneg fun e he ↦ sub_nonneg.mpr (hp₁ e (mem_sdiff.mp he).1)
lemma tS {U T :Finset E} {p:E → ℝ} {e:E}
    (_heU:e ∈ U) (hT:T ⊆ U.erase e) :
    q9 U p (insert e T) = p e *q9 (U.erase e) p T:=by
  have heT:e ∉ T:=by
    intro he
    exact (mem_erase.mp (hT he)).1 rfl
  have hdiff:U \ insert e T=U.erase e \ T :=by
    ext x
    simp only [mem_sdiff,mem_insert,mem_erase]
    tauto
  simp only [q9,prod_insert heT,hdiff]
  ring
lemma zn {U:Finset E} {p:E → ℝ} {e:E} (heU:e ∈ U) :
    ∑ S ∈ U.powerset with e ∈ S,q9 U p S =p e:=by
  have hsets:U.powerset.filter (fun S ↦ e ∈ S) =
      (U.erase e).powerset.image (insert e) :=by
    ext S
    simp only [mem_filter,mem_powerset,mem_image]
    constructor
    · rintro ⟨hSU,heS⟩
      refine ⟨S.erase e,?_,?_⟩
      · intro x hx
        obtain ⟨hxe,hxS⟩ :=mem_erase.mp hx
        exact mem_erase.mpr ⟨hxe,hSU hxS⟩
      · simpa using insert_erase heS
    · rintro ⟨T,hT,rfl⟩
      exact ⟨insert_subset heU (hT.trans (erase_subset _ _)),mem_insert_self _ _⟩
  rw [hsets,sum_image]
  · calc
      ∑ T ∈ (U.erase e).powerset,q9 U p (insert e T) =
          ∑ T ∈ (U.erase e).powerset,p e*q9 (U.erase e) p T:=by
        apply sum_congr rfl
        intro T hT
        exact tS heU (mem_powerset.mp hT)
      _=p e* ∑ T ∈ (U.erase e).powerset,q9 (U.erase e) p T:=by
        rw [mul_sum]
      _=p e:=by rw [yC,mul_one]
  · intro A hA B hB hAB
    have heA:e ∉ A:=by
      intro heA
      exact (mem_erase.mp ((mem_powerset.mp hA) heA)).1 rfl
    have heB:e ∉ B:=by
      intro heB
      exact (mem_erase.mp ((mem_powerset.mp hB) heB)).1 rfl
    simpa [heA,heB] using congrArg (fun S :Finset E ↦ S.erase e) hAB
lemma yc (U:Finset E) (p:E → ℝ) :
    ∑ S ∈ U.powerset,q9 U p S * (S.card:ℝ) = ∑ e ∈ U,p e:=by
  calc
    ∑ S ∈ U.powerset,q9 U p S * (S.card:ℝ) =
        ∑ S ∈ U.powerset,∑ e ∈ U,if e ∈ S then q9 U p S else 0 :=by
      apply sum_congr rfl
      intro S hS
      rw [← sum_filter]
      have hfilter:U.filter (fun e ↦ e ∈ S) = S:=by
        ext e
        simp only [mem_filter]
        constructor
        · exact fun h ↦ h.2
        · intro heS
          exact ⟨(mem_powerset.mp hS) heS,heS⟩
      rw [hfilter]
      simp [mul_comm]
    _= ∑ e ∈ U,∑ S ∈ U.powerset,
          if e ∈ S then q9 U p S else 0 :=by rw [sum_comm]
    _= ∑ e ∈ U,p e:=by
      apply sum_congr rfl
      intro e heU
      rw [← sum_filter,zn heU]
variable [Fintype E]
def AgreesOn (R S T:Finset E) : Prop:=S ∩ R=T ∩ R
def qP (R:Finset E) (event:Finset E → Prop) : Prop:=
  ∀ S T,AgreesOn R S T → (event S ↔ event T)
omit [Fintype E] in
lemma xY {R R' S T:Finset E} (hRR':R ⊆ R')
    (h:AgreesOn R' S T) : AgreesOn R S T :=by
  unfold AgreesOn at h ⊢
  ext e
  have hmem:e ∈ S ∩ R' ↔ e ∈ T ∩ R':=by rw [h]
  simp only [mem_inter] at hmem ⊢
  constructor
  · rintro ⟨heS,heR⟩
    exact ⟨(hmem.mp ⟨heS,hRR' heR⟩).1,heR⟩
  · rintro ⟨heT,heR⟩
    exact ⟨(hmem.mpr ⟨heT,hRR' heR⟩).1,heR⟩
omit [Fintype E] in
lemma a9 (R:Finset E) : qP R (fun _ ↦ True) :=by
  intro S T hST
  simp
omit [Fintype E] in
lemma av {R T :Finset E} {A B :Finset E → Prop}
    (hA:qP R A) (hB:qP T B) :
    qP (R ∪ T) (fun S ↦ A S ∧ B S) :=by
  intro S V hSV
  have hR:AgreesOn R S V :=xY subset_union_left hSV
  have hT:AgreesOn T S V :=xY subset_union_right hSV
  exact and_congr (hA S V hR) (hB S V hT)
abbrev Subsets (U:Finset E) := {S:Finset E //S ⊆ U}
def y1 (U:Finset E) :
    Subsets U ≃ ↥U.powerset:=
  Equiv.subtypeEquivRight (by intro S;simp)
def t4:Subsets (fsUniv:Finset E) ≃ Finset E where
  toFun S :=S.1
  invFun S := ⟨S,subset_univ S⟩
  left_inv _S:=subExt rfl
  right_inv _S:=rfl
def tT {U V :Finset E} (hUV:Disjoint U V) :
    Subsets (U ∪ V) ≃ Subsets U × Subsets V where
  toFun S :=
    (⟨S.1 ∩ U,inter_subset_right⟩,⟨S.1 ∩ V,inter_subset_right⟩)
  invFun P := ⟨P.1.1 ∪ P.2.1,union_subset_union P.1.2 P.2.2⟩
  left_inv S :=by
    apply subExt
    ext e
    simp only [mem_union,mem_inter]
    constructor
    · intro h
      rcases h with h | h
      · exact h.1
      · exact h.1
    · intro heS
      have hsplit:e ∈ U ∨ e ∈ V:=by
        simpa only [mem_union] using S.2 heS
      rcases hsplit with heU | heV
      · exact orInl ⟨heS,heU⟩
      · exact orInr ⟨heS,heV⟩
  right_inv P :=by
    rcases P with ⟨A,B⟩
    apply Prod.ext
    · apply subExt
      ext e
      simp only [mem_inter,mem_union]
      constructor
      · rintro ⟨heA | heB,heU⟩
        · exact heA
        · exact False.elim ((fsDL.mp hUV) heU (B.2 heB))
      · intro heA
        exact ⟨orInl heA,A.2 heA⟩
    · apply subExt
      ext e
      simp only [mem_inter,mem_union]
      constructor
      · rintro ⟨heA | heB,heV⟩
        · exact False.elim ((fsDL.mp hUV) (A.2 heA) heV)
        · exact heB
      · intro heB
        exact ⟨orInr heB,B.2 heB⟩
def qo (U:Finset E) (p:E → ℝ) (event:Finset E → Prop) : ℝ:=
  ∑ S :Subsets U,if event S.1 then q9 U p S.1 else 0
lemma zp (U:Finset E) (p:E → ℝ) :
    ∑ S :Subsets U,q9 U p S.1=1:=by
  calc
    (∑ S :Subsets U,q9 U p S.1) =
        ∑ S : ↥U.powerset,q9 U p S.1:=by
      apply ftSE (y1 U)
      intro S
      rfl
    _= ∑ S ∈ U.powerset,q9 U p S :=by
      simpa using
        (Finset.sum_attach U.powerset
          (fun S :Finset E ↦ q9 U p S))
    _=1:=yC U p
lemma wh (U:Finset E) (p:E → ℝ) :
    qo U p (fun _ ↦ True) = 1:=by
  unfold qo
  simpa using zp U p
lemma s1 (p:E → ℝ)
    (event:Finset E → Prop) :
    qv
        (fun S :Finset E ↦ q9 fsUniv p S) event=
      qo fsUniv p event:=by
  unfold qv qo
  symm
  apply ftSE t4
  intro S
  by_cases h :event S.1 <;> simp [h,t4]
omit [Fintype E] in
lemma xy {U V A B :Finset E} {p:E → ℝ}
    (hUV:Disjoint U V) (hA:A ⊆ U) (hB:B ⊆ V) :
    q9 (U ∪ V) p (A ∪ B) =
      q9 U p A *q9 V p B :=by
  have hAB:Disjoint A B:=hUV.mono hA hB
  have hdiff: (U ∪ V) \ (A ∪ B) = (U \ A) ∪ (V \ B) :=by
    ext e
    simp only [mem_sdiff,mem_union]
    constructor
    · rintro ⟨heU | heV,hnot⟩
      · exact orInl ⟨heU,fun heA ↦ hnot (orInl heA)⟩
      · exact orInr ⟨heV,fun heB ↦ hnot (orInr heB)⟩
    · rintro (⟨heU,heA⟩ | ⟨heV,heB⟩)
      · refine ⟨orInl heU,?_⟩
        rintro (hAe | hBe)
        · exact heA hAe
        · exact (fsDL.mp hUV) heU (hB hBe)
      · refine ⟨orInr heV,?_⟩
        rintro (hAe | hBe)
        · exact (fsDL.mp hUV) (hA hAe) heV
        · exact heB hBe
  have hdiffDisj:Disjoint (U \ A) (V \ B) :=
    hUV.mono sdiff_subset sdiff_subset
  simp only [q9,prod_union hAB,hdiff,prod_union hdiffDisj]
  ring
lemma sk {U V :Finset E} {p:E → ℝ}
    {A B :Finset E → Prop} (hUV:Disjoint U V)
    (hA:qP U A) (hB:qP V B) :
    qo (U ∪ V) p (fun S ↦ A S ∧ B S) =
      qo U p A *qo V p B :=by
  let split:Subsets (U ∪ V) ≃ Subsets U × Subsets V :=
    tT hUV
  let summand:Subsets (U ∪ V) → ℝ:=fun S ↦
    if A S.1 ∧ B S.1 then q9 (U ∪ V) p S.1 else 0
  calc
    qo (U ∪ V) p (fun S ↦ A S ∧ B S) =
        ∑ S :Subsets (U ∪ V),summand S :=by
      unfold qo
      apply sum_congr rfl
      intro S _
      by_cases h :A S.1 ∧ B S.1 <;> simp [summand,h]
    _= ∑ P:Subsets U × Subsets V,summand (split.symm P) :=by
      apply ftSE split
      intro S
      simp only [Equiv.symm_apply_apply]
    _= ∑ X:Subsets U,∑ Y:Subsets V,summand (split.symm (X,Y)) :=by
      rw [Fintype.sum_prod_type]
    _= ∑ X:Subsets U,∑ Y:Subsets V,
        (if A X.1 then q9 U p X.1 else 0) *
          (if B Y.1 then q9 V p Y.1 else 0) :=by
      apply sum_congr rfl
      intro X _
      apply sum_congr rfl
      intro Y _
      have hsplit: (split.symm (X,Y)).1=X.1 ∪ Y.1:=rfl
      have hAgreeA:AgreesOn U (X.1 ∪ Y.1) X.1:=by
        unfold AgreesOn
        ext e
        simp only [mem_inter,mem_union]
        constructor
        · rintro ⟨heX | heY,heU⟩
          · exact ⟨heX,X.2 heX⟩
          · exact False.elim ((fsDL.mp hUV) heU (Y.2 heY))
        · rintro ⟨heX,heU⟩
          exact ⟨orInl heX,heU⟩
      have hAgreeB:AgreesOn V (X.1 ∪ Y.1) Y.1:=by
        unfold AgreesOn
        ext e
        simp only [mem_inter,mem_union]
        constructor
        · rintro ⟨heX | heY,heV⟩
          · exact False.elim ((fsDL.mp hUV) (X.2 heX) heV)
          · exact ⟨heY,Y.2 heY⟩
        · rintro ⟨heY,heV⟩
          exact ⟨orInr heY,heV⟩
      have hAE:A (X.1 ∪ Y.1) ↔ A X.1:=hA _ _ hAgreeA
      have hBE:B (X.1 ∪ Y.1) ↔ B Y.1:=hB _ _ hAgreeB
      rw [show summand (split.symm (X,Y)) =
          if A (X.1 ∪ Y.1) ∧ B (X.1 ∪ Y.1) then
            q9 (U ∪ V) p (X.1 ∪ Y.1) else 0 by
              change (if A (split.symm (X,Y)).1 ∧ B (split.symm (X,Y)).1 then
                q9 (U ∪ V) p (split.symm (X,Y)).1 else 0) = _
              rw [hsplit]]
      rw [xy hUV X.2 Y.2]
      by_cases hAX:A X.1 <;> by_cases hBY:B Y.1 <;>
        simp_all
    _= (∑ X :Subsets U,if A X.1 then q9 U p X.1 else 0) *
        ∑ Y :Subsets V,if B Y.1 then q9 V p Y.1 else 0 :=by
      rw [sum_mul]
      apply sum_congr rfl
      intro X _
      rw [mul_sum]
    _=qo U p A *qo V p B :=by
      rfl
lemma r9 {R:Finset E} {p:E → ℝ}
    {event:Finset E → Prop} (hlocal:qP R event) :
    qv
        (fun S :Finset E ↦ q9 fsUniv p S) event=
      qo R p event:=by
  calc
    qv
        (fun S :Finset E ↦ q9 fsUniv p S) event=
        qo fsUniv p event:=
      s1 p event
    _=qo R p event:=by
      have hfactor:=sk
        (p:=p) (U:=R) (V:=fsUniv \ R)
        (A:=event) (B:=fun _ ↦ True) Finset.disjoint_sdiff hlocal
        (a9 (fsUniv \ R))
      have hcover:R ∪ (fsUniv \ R) = (fsUniv:Finset E) :=
        union_sdiff_of_subset (subset_univ R)
      rw [hcover] at hfactor
      simpa [wh] using hfactor
theorem yz {R T :Finset E} {p:E → ℝ}
    {A B :Finset E → Prop} (hRT:Disjoint R T)
    (hA:qP R A) (hB:qP T B) :
    qv
        (fun S :Finset E ↦ q9 fsUniv p S)
        (fun S ↦ A S ∧ B S) =
      qv
          (fun S :Finset E ↦ q9 fsUniv p S) A *
        qv
          (fun S :Finset E ↦ q9 fsUniv p S) B :=by
  calc
    qv
        (fun S :Finset E ↦ q9 fsUniv p S)
        (fun S ↦ A S ∧ B S) =
        qo (R ∪ T) p (fun S ↦ A S ∧ B S) :=
      r9 (av hA hB)
    _=qo R p A *qo T p B :=
      sk hRT hA hB
    _=qv
          (fun S :Finset E ↦ q9 fsUniv p S) A *
        qv
          (fun S :Finset E ↦ q9 fsUniv p S) B :=by
      rw [r9 hA,
        r9 hB]
end
end Erdos556.Bernoulli
end cw
section du
namespace Erdos556.Bernoulli
open Finset
open scoped BigOperators
noncomputable section
open scoped Classical
theorem dN {Ω:Type*} [Fintype Ω] (mass:Ω → ℝ)
    (hsum: ∑ x,mass x =1) (A:Ω → Prop) :
    qv mass (fun x => ¬ A x) = 1-qv mass A :=by
  have hsplit:qv mass A +qv mass (fun x => ¬ A x) = 1:=by
    unfold qv
    rw [← sum_add_distrib,← hsum]
    apply sum_congr rfl
    intro x _
    by_cases ha:A x <;> simp [ha]
  linarith
theorem bu {Ω:Type*} [Fintype Ω] (mass:Ω → ℝ)
    (hmass: ∀ x,0 ≤ mass x) (A B :Ω → Prop) :
    qv mass (fun x => A x ∨ B x) ≤ qv mass A +qv mass B :=by
  unfold qv
  rw [← sum_add_distrib]
  apply sum_le_sum
  intro x _
  by_cases ha:A x <;> by_cases hb:B x <;> simp [ha,hb,hmass x]
theorem a5 {Ω I :Type*} [Fintype Ω] [Fintype I]
    (mass:Ω → ℝ) (hmass: ∀ x,0 ≤ mass x) (A:I → Ω → Prop) :
    qv mass (fun x => ∃ i,A i x) ≤ ∑ i,qv mass (A i) :=by
  unfold qv
  rw [sum_comm]
  apply sum_le_sum
  intro x _
  by_cases h : ∃ i,A i x
  · obtain ⟨i,hi⟩ :=h
    rw [if_pos ⟨i,hi⟩]
    have hle:=single_le_sum (s:= (univ:Finset I))
      (f:=fun j => if A j x then mass x else 0)
      (fun j _=> by split_ifs <;> simp_all) (mem_univ i)
    simpa only [if_pos hi] using hle
  · rw [if_neg h]
    apply sum_nonneg
    intro i _
    split_ifs <;> simp_all
theorem aI {Ω:Type*} [Fintype Ω]
    (mass X :Ω → ℝ) (hmass: ∀ x,0 ≤ mass x) (hX: ∀ x,0 ≤ X x) (t:ℝ) :
    t*qv mass (fun x => t < X x) ≤ ∑ x,mass x *X x:=by
  unfold qv
  rw [mul_sum]
  apply sum_le_sum
  intro x _
  by_cases hx:t < X x
  · rw [if_pos hx,mul_comm t]
    exact mul_le_mul_of_nonneg_left hx.le (hmass x)
  · rw [if_neg hx,mul_zero]
    exact mul_nonneg (hmass x) (hX x)
theorem wl {Ω:Type*} [Fintype Ω]
    (mass:Ω → ℝ) (hsum: ∑ x,mass x =1) (A:Ω → Prop)
    (hA:qv mass A < 1) : ∃ x,¬ A x:=by
  by_contra h
  push Not at h
  have heq:qv mass A =1:=by simp [qv,h,hsum]
  linarith
variable {E:Type*} [Fintype E] [DecidableEq E]
theorem uM (p:E → ℝ) :
    ∑ S :Finset E,q9 univ p S=1:=by
  have h :=s1 p (fun _ => True)
  simpa only [qv,if_true,wh] using h
omit [Fintype E] in
theorem zV (L:Finset E) : qP L (fun X => L ⊆ X) :=by
  intro X Y hXY
  unfold AgreesOn at hXY
  constructor
  · intro hLX x hxL
    have hx:x ∈ X ∩ L:=mem_inter.mpr ⟨hLX hxL,hxL⟩
    rw [hXY] at hx
    exact (mem_inter.mp hx).1
  · intro hLY x hxL
    have hx:x ∈ Y ∩ L:=mem_inter.mpr ⟨hLY hxL,hxL⟩
    rw [← hXY] at hx
    exact (mem_inter.mp hx).1
omit [Fintype E] in
theorem am {L:Finset E} {A:Finset E → Prop}
    (hA:qP L A) : qP L (fun X => ¬ A X) :=by
  intro X Y hXY
  exact not_congr (hA X Y hXY)
theorem au (p:E → ℝ) (L:Finset E) :
    qv (q9 univ p) (fun X => L ⊆ X) = ∏ e ∈ L,p e:=by
  rw [r9 (zV L)]
  unfold qo
  rw [sum_eq_single (⟨L,subset_rfl⟩ : Subsets L)]
  · simp [q9]
  · intro X _ hX
    have hn: ¬ L ⊆ X.val:=by
      intro h
      exact hX (subExt (Subset.antisymm X.property h))
    simp [hn]
  · simp
omit [Fintype E] in
theorem yf {I:Type*}
    (R:I → Finset E) (A:I → Finset E → Prop)
    (hA: ∀ i,qP (R i) (A i)) (J:Finset I) :
    qP (J.biUnion R) (fun S => ∀ i ∈ J,A i S) :=by
  classical
  intro S T hST
  constructor
  · intro h i hi
    have hsub:R i ⊆ J.biUnion R :=subset_biUnion_of_mem R hi
    exact (hA i S T (xY hsub hST)).mp (h i hi)
  · intro h i hi
    have hsub:R i ⊆ J.biUnion R :=subset_biUnion_of_mem R hi
    exact (hA i S T (xY hsub hST)).mpr (h i hi)
theorem yT {I:Type*}
    (p:E → ℝ) (R:I → Finset E) (A:I → Finset E → Prop)
    (hA: ∀ i,qP (R i) (A i)) (J:Finset I)
    (hdisj: (J:Set I).Pairwise fun i j=> Disjoint (R i) (R j)) :
    qv (q9 univ p) (fun S => ∀ i ∈ J,A i S) =
      ∏ i ∈ J,qv (q9 univ p) (A i) :=by
  classical
  revert hdisj
  induction J using Finset.induction_on with
  | empty=>
      intro _
      simp [qv,uM]
  | @insert i J hi ih=>
      intro hdisj
      have hD:Disjoint (R i) (J.biUnion R) :=by
        rw [disjoint_biUnion_right]
        intro j hj
        exact hdisj (mem_insert_self i J) (mem_insert_of_mem hj)
          (by intro h;subst j;exact hi hj)
      have hDJ: (J:Set I).Pairwise fun i j=> Disjoint (R i) (R j) :=
        hdisj.mono (subset_insert i J)
      simp only [forall_mem_insert,prod_insert hi]
      rw [yz hD (hA i)
        (yf R A hA J),ih hDJ]
theorem tH {I:Type*}
    (q:ℝ) (R:I → Finset E) (J:Finset I)
    (hdisj: (J:Set I).Pairwise fun i j=> Disjoint (R i) (R j)) :
    qv (q9 univ (fun _ :E=> q))
      (fun S => ∀ i ∈ J,¬ R i ⊆ S) = ∏ i ∈ J,(1-q^ (R i).card) :=by
  classical
  rw [yT (fun _ => q) R (fun i S=> ¬ R i ⊆ S)
    (fun i => am (zV (R i))) J hdisj]
  apply prod_congr rfl
  intro i _
  rw [dN _ (uM _) (fun S => R i ⊆ S),
    au]
  simp
theorem yQ {I:Type*}
    (q:ℝ) (hq0:0 ≤ q) (hq1:q ≤ 1) (R:I → Finset E) (J:Finset I)
    (hdisj: (J:Set I).Pairwise fun i j=> Disjoint (R i) (R j)) (L:ℕ)
    (hsize: ∀ i ∈ J,(R i).card ≤ L) :
    qv (q9 univ (fun _ :E=> q))
      (fun S => ∀ i ∈ J,¬ R i ⊆ S) ≤ (1-q^L) ^ J.card:=by
  classical
  rw [tH q R J hdisj]
  calc
    ∏ i ∈ J,(1-q^ (R i).card) ≤ ∏ _i ∈ J,(1-q^L) :=by
      apply prod_le_prod
      · intro i _
        exact sub_nonneg.mpr (pow_le_one₀ hq0 hq1)
      · intro i hi
        exact sub_le_sub_left (pow_le_pow_of_le_one hq0 hq1 (hsize i hi)) 1
    _= (1-q^L) ^ J.card:=by simp
omit [DecidableEq E] in
theorem wY {I:Type*} [Fintype I]
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1) (L m :ℕ)
    (R:I → Fin m → Finset E)
    (hdisj: ∀ i,(Set.univ:Set (Fin m)).Pairwise
      fun j k=> Disjoint (R i j) (R i k))
    (hsize: ∀ i j,(R i j).card ≤ L)
    (hfail: (ftCard I :ℝ) * (1-q^L) ^ m < 1/2)
    (hE:0 < ftCard E) :
    ∃ S :Finset E,(S.card:ℝ) ≤ 2*q*ftCard E ∧
      ∀ i,∃ j,R i j ⊆ S:=by
  classical
  let mass:Finset E → ℝ :=q9 univ (fun _ => q)
  have hmass (S:Finset E) : 0 ≤ mass S :=
    tO (subset_univ S) (fun _ _=> hq0.le) (fun _ _=> hq1)
  have hsum: ∑ S,mass S =1:=uM _
  have hmean: ∑ S:Finset E,mass S * (S.card:ℝ) =
      q*ftCard E :=by
    simpa [mass,mul_comm] using
      yc (univ:Finset E) (fun _ => q)
  let t :ℝ:=2*q*ftCard E
  have ht:0 < t:=by
    dsimp [t]
    exact mul_pos (mul_pos (by norm_num) hq0) (by exact_mod_cast hE)
  have hlarge:qv mass (fun S => t < (S.card:ℝ)) ≤ 1/2:=by
    apply (mul_le_mul_iff_right₀ ht).mp
    calc
      t*qv mass (fun S => t < (S.card:ℝ)) ≤
          ∑ S :Finset E,mass S * (S.card:ℝ) :=
        aI mass (fun S => S.card) hmass (fun S => by positivity) t
      _=t* (1/2) :=by rw [hmean];dsimp [t];ring
  let bad:I → Finset E → Prop:=fun i S=> ∀ j,¬ R i j ⊆ S
  have hbad (i:I) : qv mass (bad i) ≤ (1-q^L) ^ m:=by
    simpa only [mass,bad,mem_univ,forall_true_left,card_univ,ftCF]
      using yQ q hq0.le hq1 (R i) univ
        (by simpa only [coe_univ] using hdisj i) L (fun j _=> hsize i j)
  have hsome:qv mass (fun S => ∃ i,bad i S) < 1/2:=by
    calc
      qv mass (fun S => ∃ i,bad i S) ≤ ∑ i,qv mass (bad i) :=
        a5 mass hmass bad
      _ ≤ ∑ _i:I,(1-q^L) ^ m:=sum_le_sum (fun i _=> hbad i)
      _= (ftCard I :ℝ) * (1-q^L) ^ m:=by simp
      _ < 1/2:=hfail
  have hall:qv mass (fun S => t < (S.card:ℝ) ∨ ∃ i,bad i S) < 1:=by
    have h :=bu mass hmass
      (fun S => t < (S.card:ℝ)) (fun S => ∃ i,bad i S)
    linarith
  obtain ⟨S,hS⟩ :=wl mass hsum _ hall
  refine ⟨S,le_of_not_gt (fun h => hS (orInl h)),?_⟩
  intro i
  by_contra hi
  push Not at hi
  exact hS (orInr ⟨i,hi⟩)
end
end Erdos556.Bernoulli
end du
namespace Erdos556
open Finset
theorem tt {E:Type*}
    (P:Finset E → Prop) (L b m:ℕ) (hbound:m*L ≤ b)
    (havoid: ∀ S:Finset E,S.card ≤ b →
      ∃ T :Finset E,P T ∧ T.card ≤ L ∧ Disjoint S T) :
    ∃ R :Fin m → Finset E,(∀ i,P (R i) ∧ (R i).card ≤ L) ∧
      Pairwise (fun i j=> Disjoint (R i) (R j)) :=by
  classical
  induction m with
  | zero=>
      refine ⟨Fin.elim0,?_,?_⟩
      · intro i;exact Fin.elim0 i
      · intro i;exact Fin.elim0 i
  | succ m ih=>
      obtain ⟨R,hR,hD⟩ :=ih (by nlinarith)
      let S := (univ:Finset (Fin m)).biUnion R
      have hS:S.card ≤ b:=by
        calc
          S.card ≤ ∑ i :Fin m,(R i).card:=card_biUnion_le
          _ ≤ ∑ _i:Fin m,L:=sum_le_sum (fun i _=> (hR i).2)
          _=m*L:=by simp
          _ ≤ b:=by nlinarith
      obtain ⟨T,hT,hsize,hST⟩ :=havoid S hS
      have hTR (i:Fin m) : Disjoint T (R i) :=
        hST.symm.mono_right (subset_biUnion_of_mem R (mem_univ i))
      refine ⟨Fin.cons T R,?_,?_⟩
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact ⟨hT,hsize⟩
        · exact hR j
      · intro i j hij
        revert hij
        refine Fin.cases ?_ (fun i => ?_) i <;>
          refine Fin.cases ?_ (fun j => ?_) j
        · intro h;exact (h rfl).elim
        · intro _;exact hTR j
        · intro _;exact (hTR i).symm
        · intro h
          exact hD (fun he=> h (congrArg Fin.succ he))
theorem xq {E I :Type*}
    [Fintype I] (R:I → Finset E) (T:Finset E)
    (hD:Pairwise (fun i j=> Disjoint (R i) (R j)))
    (hmeet: ∀ i,¬ Disjoint T (R i)) : ftCard I ≤ T.card:=by
  classical
  have hx: ∀ i,∃ x,x ∈ T ∧ x ∈ R i:=by
    intro i
    simpa only [fsDL,not_forall,not_not,exists_prop] using hmeet i
  choose x hxT hxR using hx
  let f :I → T:=fun i => ⟨x i,hxT i⟩
  have hinj:Function.Injective f :=by
    intro i j hij
    by_contra hne
    have heq:x i=x j:=congrArg subVal hij
    exact fsDL.mp (hD hne) (hxR i) (heq ▸ hxR j)
  simpa only [ftCC] using ftCLOI f hinj
theorem y7 {E I :Type*}
    [Fintype I] (R:I → Finset E) (T:Finset E)
    (hD:Pairwise (fun i j=> Disjoint (R i) (R j)))
    (hcard:T.card < ftCard I) : ∃ i,Disjoint T (R i) :=by
  classical
  by_contra h
  push Not at h
  exact (Nat.not_le_of_gt hcard) (xq R T hD h)
end Erdos556
namespace Erdos556
open Finset
theorem uA {E I :Type*} [Fintype E]
    [Fintype I] (P:I → Finset E → Prop) (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1)
    (L b m a :ℕ) (hbound: ((a+1) * m) * L ≤ b)
    (havoid: ∀ i S,S.card ≤ b →
      ∃ T :Finset E,P i T ∧ T.card ≤ L ∧ Disjoint S T)
    (hfail: (ftCard I :ℝ) * (a+1) * (1-q^L) ^ m < 1/2)
    (hE:0 < ftCard E) :
    ∃ S :Finset E,(S.card:ℝ) ≤ 2*q*ftCard E ∧
      ∀ i T,T.card ≤ a → ∃ U :Finset E,
        U ⊆ S ∧ P i U ∧ U.card ≤ L ∧ Disjoint T U:=by
  classical
  have hpacks (i:I) :=tt (P i) L b ((a+1) * m)
    hbound (havoid i)
  choose R hR hD using hpacks
  let Q (i:I × Fin (a+1)) (j:Fin m) : Finset E :=
    R i.1 (finProdFinEquiv (i.2,j))
  have hQD (i:I × Fin (a+1)) :
      (Set.univ:Set (Fin m)).Pairwise fun j k=> Disjoint (Q i j) (Q i k) :=by
    intro j _ k _ hjk
    apply hD i.1
    intro heq
    exact hjk (congrArg Prod.snd (finProdFinEquiv.injective heq))
  have hQS (i:I × Fin (a+1)) (j:Fin m) : (Q i j).card ≤ L:=
    (hR i.1 (finProdFinEquiv (i.2,j))).2
  have hfailure: (ftCard (I × Fin (a+1)) : ℝ) *
      (1-q^L) ^ m < 1/2:=by
    simpa only [ftCP,ftCF,natCM,natCA,
      Nat.cast_one] using hfail
  obtain ⟨S,hS,hhit⟩ :=Bernoulli.wY
    q hq0 hq1 L m Q hQD hQS hfailure hE
  refine ⟨S,hS,?_⟩
  intro i T hT
  have hg (g:Fin (a+1)) : ∃ j,Q (i,g) j ⊆ S :=hhit (i,g)
  choose j hj using hg
  let F (g:Fin (a+1)) : Finset E :=Q (i,g) (j g)
  have hFD:Pairwise (fun g h=> Disjoint (F g) (F h)) :=by
    intro g h hgh
    apply hD i
    intro heq
    exact hgh (congrArg Prod.fst (finProdFinEquiv.injective heq))
  obtain ⟨g,hgT⟩ :=y7 F T hFD
    (by simpa only [ftCF] using natLSOL hT)
  exact ⟨F g,hj g,(hR i (finProdFinEquiv (g,j g))).1,hQS (i,g) (j g),hgT⟩
end Erdos556
namespace Erdos556
open SimpleGraph Finset
def qY {V:Type*} (G:SimpleGraph V) (L:ℕ) (u v :V)
    (S:Finset V) : Prop:=
  ∃ p :G.Walk u v,p.IsPath ∧ p.length ≤ L ∧
    ∀ x ∈ p.support,x ≠ u → x ≠ v → x ∈ S
theorem qY.mono {V:Type*} {G:SimpleGraph V} {L:ℕ} {u v :V}
    {S T :Finset V} (h:qY G L u v S) (hST:S ⊆ T) :
    qY G L u v T :=by
  obtain ⟨p,hp,hlen,hs⟩ :=h
  exact ⟨p,hp,hlen,fun x hx hxu hxv=> hST (hs x hx hxu hxv)⟩
theorem x6 {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (b d L:ℕ)
    (hconn:q8 G b) (hd:0 < d)
    (hdeg: ∀ w,d+b ≤ G.degree w) (hdiam:3*ftCard V ≤ d *L)
    (u v :V) (S:Finset V) (hS:S.card ≤ b) :
    ∃ T :Finset V,qY G L u v T ∧ T.card ≤ L ∧ Disjoint S T:=by
  classical
  let S':= (S.erase u).erase v
  have hS':S'.card ≤ b:=
    (fsCLC ((erase_subset v (S.erase u)).trans (erase_subset u S))).trans hS
  obtain ⟨p,hp,hlen,hav⟩ :=sB G b d hconn hd hdeg S' hS'
    u v (by simp [S']) (by simp [S'])
  have hlen':p.length+1 ≤ L:=by nlinarith
  let T := (p.support.toFinset.erase u).erase v
  refine ⟨T,⟨p,hp,by omega,?_⟩,?_,?_⟩
  · intro x hx hxu hxv
    simp only [T,mem_erase,lsMT]
    exact ⟨hxv,hxu,hx⟩
  · calc
      T.card ≤ p.support.toFinset.card:=
        fsCLC ((erase_subset v _).trans (erase_subset u _))
      _ ≤ p.support.length:=lsTCL p.support
      _=p.length+1:=p.length_support
      _ ≤ L:=hlen'
  · rw [fsDL]
    intro x hxS hxT
    simp only [T,mem_erase,lsMT] at hxT
    apply hav x hxT.2.2
    simp only [S',mem_erase]
    exact ⟨hxT.1,hxT.2.1,hxS⟩
theorem zM {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (b d L m a:ℕ)
    (hconn:q8 G b) (hd:0 < d)
    (hdeg: ∀ w,d+b ≤ G.degree w) (hdiam:3*ftCard V ≤ d *L)
    (hbound: ((a+1) * m) * L ≤ b)
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1)
    (hfail: (ftCard V :ℝ) ^ 2* (a+1) * (1-q^L) ^ m < 1/2)
    (hV:0 < ftCard V) :
    ∃ R :Finset V,(R.card:ℝ) ≤ 2*q*ftCard V ∧
      ∀ u v S,S.card ≤ a → qY G L u v (R \ S) :=by
  classical
  let P : (V × V) → Finset V → Prop:=fun uv=> qY G L uv.1 uv.2
  have hav (uv:V × V) (S:Finset V) (hS:S.card ≤ b) :
      ∃ T :Finset V,P uv T ∧ T.card ≤ L ∧ Disjoint S T:=
    x6 G b d L hconn hd hdeg hdiam uv.1 uv.2 S hS
  have hf: (ftCard (V × V) : ℝ) * (a+1) *
      (1-q^L) ^ m < 1/2:=by
    simpa only [ftCP,natCM,pow_two] using hfail
  obtain ⟨R,hR,hhit⟩ :=uA P q hq0 hq1 L b m a
    hbound hav hf hV
  refine ⟨R,hR,?_⟩
  intro u v S hS
  obtain ⟨T,hTR,hP,_,hST⟩ :=hhit (u,v) S hS
  apply hP.mono
  intro x hx
  exact mem_sdiff.mpr ⟨hTR hx,fun hxS=> fsDL.mp hST hxS hx⟩
end Erdos556
namespace Erdos556
open SimpleGraph
theorem s9 {V:Type*} {G:SimpleGraph V}
    {u v :V} (p:G.Walk u v) (hp:p.IsPath) : u ∉ p.support.tail:=by
  have h :=hp.support_nodup
  rw [← p.cons_tail_support,lsNC] at h
  exact h.1
theorem qy {V:Type*} {G:SimpleGraph V}
    {u v :V} (p q :G.Walk u v) (hp:p.IsPath) (hq:q.IsPath) (hlen:1 < p.length)
    (hinter: ∀ x ∈ p.support,x ∈ q.support → x=u ∨ x=v) :
    (p.append q.reverse).IsCycle:=by
  apply hp.isCycle_append hq.reverse _ (orInl hlen)
  rw [lsDL]
  intro x hxp hxq
  have hxp':x ∈ p.support:=lsMOMT hxp
  have hxq':x ∈ q.support:=by
    simpa only [wkSR,lsMR] using lsMOMT hxq
  rcases hinter x hxp' hxq' with hxu | hxv
  · exact s9 p hp (hxu ▸ hxp)
  · exact s9 q.reverse hq.reverse (hxv ▸ hxq)
theorem sZ {V:Type*} {G:SimpleGraph V}
    {u v :V} (p:G.Walk u v) (hp:p.IsPath) (hlen:1 < p.length)
    (L:ℕ) (R:Finset V) (hav: ∀ x ∈ p.support,x ∉ R)
    (hconn:qZ G L u v R) :
    ∃ c :G.Walk u u,c.IsCycle ∧ Odd c.length ∧
      p.length ≤ c.length ∧ c.length ≤ p.length+L:=by
  let r :Fin 2 := ⟨(p.length+1) % 2,natML _ (by decide)⟩
  obtain ⟨q,hq,hqL,hqpar,hqR⟩ :=hconn r
  have hc: (p.append q.reverse).IsCycle:=by
    apply qy p q hp hq hlen
    intro x hxp hxq
    by_cases hxu:x=u
    · exact orInl hxu
    by_cases hxv:x=v
    · exact orInr hxv
    exact (hav x hxp (hqR x hxq hxu hxv)).elim
  refine ⟨p.append q.reverse,hc,?_,?_,?_⟩
  · apply natOI.mpr
    simp only [wkLA,wkLR]
    change q.length%2= (p.length+1) % 2 at hqpar
    omega
  · simp only [wkLA,wkLR]
    omega
  · simp only [wkLA,wkLR]
    omega
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem rf {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) (L:ℕ) (hL:0 < L) (X Y :Finset V)
    (hXY:Disjoint X Y) (hcomplete: ∀ x ∈ X,∀ y ∈ Y,G.Adj x y)
    (hX:L+1 ≤ X.card) (hY:L ≤ Y.card)
    (u v :V) (hu:u ∈ X) (hv:v ∈ X) (huv:u ≠ v) :
    ∃ p :G.Walk u v,p.IsPath ∧ p.length=2*L ∧
      ∀ z ∈ p.support,z ∈ X ∪ Y:=by
  induction L generalizing X Y u v with
  | zero=> omega
  | succ L ih=>
      classical
      obtain ⟨y,hy⟩ :=card_pos.mp (show 0 < Y.card by omega)
      have huy:u ≠ y:=fun h => fsDL.mp hXY hu (h.symm ▸ hy)
      have hvy:v ≠ y:=fun h => fsDL.mp hXY hv (h.symm ▸ hy)
      by_cases hzero:L=0
      · subst L
        let p :G.Walk u v:=wkCons (hcomplete u hu y hy)
          (wkCons (hcomplete v hv y hy).symm Walk.nil)
        refine ⟨p,?_,rfl,?_⟩
        · apply (wkCII _ _).mpr
          refine ⟨(wkCII _ _).mpr ⟨?_,?_⟩,?_⟩
          · exact Walk.IsPath.nil
          · simpa using hvy.symm
          · simpa only [wkSC2,Walk.support_nil,lsMC,
              lsNMN,or_false,not_or] using And.intro huy huv
        · intro z hz
          simp only [p,wkSC2,Walk.support_nil,lsMC,
            lsNMN,or_false] at hz
          rcases hz with rfl | rfl | rfl
          · exact mem_union_left _ hu
          · exact mem_union_right _ hy
          · exact mem_union_left _ hv
      · have hwex: (X \ {u,v}).Nonempty:=by
          apply card_pos.mp
          have hle: ({u,v} : Finset V).card ≤ 2:=by
            exact (card_insert_le _ _).trans (by simp)
          have hc:=card_le_card (show X ∩ {u,v} ⊆ ({u,v} : Finset V) from inter_subset_right)
          rw [card_sdiff,inter_comm]
          omega
        obtain ⟨w,hw⟩ :=hwex
        have hwX:w ∈ X:= (mem_sdiff.mp hw).1
        have hwu:w ≠ u:=fun h => (mem_sdiff.mp hw).2 (by simp [h])
        have hwv:w ≠ v:=by
          have hn:= (mem_sdiff.mp hw).2
          exact fun h => hn (by simp [h])
        have hX':L+1 ≤ (X.erase u).card:=by rw [card_erase_of_mem hu];omega
        have hY':L ≤ (Y.erase y).card:=by rw [card_erase_of_mem hy];omega
        have hXY':Disjoint (X.erase u) (Y.erase y) :=
          hXY.mono (erase_subset _ _) (erase_subset _ _)
        have hcomplete': ∀ x ∈ X.erase u,∀ z ∈ Y.erase y,G.Adj x z:=
          fun x hx z hz=> hcomplete x (mem_of_mem_erase hx) z (mem_of_mem_erase hz)
        obtain ⟨q,hq,hqlen,hqS⟩ :=ih (by omega) (X.erase u) (Y.erase y) hXY'
          hcomplete' hX' hY' w v (mem_erase.mpr ⟨hwu,hwX⟩)
          (mem_erase.mpr ⟨huv.symm,hv⟩) hwv
        have huq:u ∉ q.support:=by
          intro h
          rcases mem_union.mp (hqS u h) with hx | hz
          · exact (mem_erase.mp hx).1 rfl
          · exact fsDL.mp hXY hu (mem_of_mem_erase hz)
        have hyq:y ∉ q.support:=by
          intro h
          rcases mem_union.mp (hqS y h) with hx | hz
          · exact fsDL.mp hXY (mem_of_mem_erase hx) hy
          · exact (mem_erase.mp hz).1 rfl
        let p :G.Walk u v:=wkCons (hcomplete u hu y hy)
          (wkCons (hcomplete w hwX y hy).symm q)
        refine ⟨p,?_,?_,?_⟩
        · apply (wkCII _ _).mpr
          refine ⟨(wkCII _ _).mpr ⟨hq,hyq⟩,?_⟩
          simpa only [wkSC2,lsMC,not_or] using And.intro huy huq
        · simp only [p,wkLC2,hqlen]
          omega
        · intro z hz
          simp only [p,wkSC2,lsMC] at hz
          rcases hz with rfl | rfl | hz
          · exact mem_union_left _ hu
          · exact mem_union_right _ hy
          · exact (union_subset_union (erase_subset _ _) (erase_subset _ _)) (hqS z hz)
theorem wq {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) (L:ℕ) (hL:0 < L) (X Y :Finset V)
    (hXY:Disjoint X Y) (hcomplete: ∀ x ∈ X,∀ y ∈ Y,G.Adj x y)
    (hX:L+1 ≤ X.card) (hY:L ≤ Y.card)
    (u v :V) (hu:u ∈ X) (hv:v ∈ X) (huv:u ≠ v)
    (p:G.Walk u v) (hp:p.IsPath) (hlen:1 < p.length)
    (hoff: ∀ z ∈ p.support,z ∈ X ∪ Y → z=u ∨ z=v) :
    ∃ c :G.Walk u u,c.IsCycle ∧ c.length=p.length+2*L:=by
  obtain ⟨q,hq,hqL,hqS⟩ :=rf G L hL X Y
    hXY hcomplete hX hY u v hu hv huv
  refine ⟨p.append q.reverse,?_,?_⟩
  · exact qy p q hp hq hlen
      (fun z hzp hzq=> hoff z hzp (hqS z hzq))
  · simp only [wkLA,wkLR,hqL]
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem u9 {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (D d :ℕ) (hD:0 < D)
    (hscale:ftCard V ≤ D *d) (hdegree: ∀ v,d ≤ G.degree v)
    (hN:8* (4*D) ^ 2 ≤ ftCard V)
    (X Y :Finset V) (hXY:Disjoint X Y)
    (hcomplete: ∀ x ∈ X,∀ y ∈ Y,G.Adj x y)
    (hX:16*D+8* (4*D) ^ 2+1 ≤ X.card)
    (hY:16*D+8* (4*D) ^ 2 ≤ Y.card)
    (hR:2* ((X ∪ Y).card+16*D+1) ≤ d)
    (u v :V) (hu:u ∈ X) (hv:v ∈ X) (huv:u ≠ v)
    (p:G.Walk u v) (hp:p.IsPath)
    (hoff: ∀ z ∈ p.support,z ∈ X ∪ Y → z=u ∨ z=v)
    (n:ℕ) (hn:32*D+8* (4*D) ^ 2+4 ≤ n)
    (hnp:n ≤ p.length+2) (hpar:n%2=p.length%2) :
    ∃ c :G.Walk u u,c.IsCycle ∧ c.length=n:=by
  obtain ⟨q,hq,hqt,hwin,hqpar,hqoff⟩ :=zu G D d hD
    hscale hdegree hN (X ∪ Y) hR (n-2) (by omega) p hp (by omega) hoff
  let L := (n-q.length) / 2
  have hqparn:q.length%2=n%2:=hqpar.trans hpar.symm
  have hqgt:1 < q.length:=by omega
  have hL:0 < L:=by dsimp [L];omega
  have hLe:L ≤ 16*D+8* (4*D) ^ 2:=by dsimp [L];omega
  have hlen:q.length+2*L=n:=by dsimp [L];omega
  obtain ⟨c,hc,hclen⟩ :=wq G L hL X Y hXY hcomplete
    (by omega) (by omega) u v hu hv huv q hq hqgt hqoff
  exact ⟨c,hc,hclen.trans hlen⟩
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem zG (D:ℕ) (hD:0 < D) :
    ∃ N₀ K :ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (d:ℕ),
      N₀ ≤ ftCard V → ftCard V ≤ D *d → (∀ v,d ≤ G.degree v) →
      ∀ (z:V) (c:G.Walk z z),c.IsCycle →
      ∀ n :ℕ,K ≤ n → n+K ≤ c.length → n%2=c.length%2 →
      ∃ (w:V) (q:G.Walk w w),q.IsCycle ∧ q.length=n:=by
  let Q :=16*D+8* (4*D) ^ 2
  let M :=rR D Q
  let H :=sd D Q
  let L :=rl D Q
  let C :=2* (2*Q+16*D+3)
  let K :=M+H+ (32*D+8* (4*D) ^ 2+4) + 1
  let N₀:=D*C+8* (4*D) ^ 2+2*L* (Q+M+1) + H
  have hQ:0 < Q:=by dsimp [Q];omega
  refine ⟨N₀,K,?_⟩
  intro V _ _ G _ d hN hscale hdegree z c hc n hn hnc hpar
  have hNshort:8* (4*D) ^ 2 ≤ ftCard V :=by dsimp [N₀] at hN;omega
  have hNloss:2*L* (Q+M+1) ≤ ftCard V :=by dsimp [N₀] at hN;omega
  have hNblock:H ≤ ftCard V :=by dsimp [N₀] at hN;omega
  have hDC:D*C ≤ D*d:=by
    have h :D*C ≤ ftCard V :=by dsimp [N₀] at hN;omega
    exact h.trans hscale
  have hC:C ≤ d:= (mul_le_mul_iff_right₀ hD).mp hDC
  have hlen:M < c.length:=by dsimp [K] at hn hnc;omega
  obtain ⟨X,Y,hX,hY,hXY,hcomplete,u,hu,v,hv,huv,p,hp,hpL,hpPar,hpOff⟩ :=
    tl G c hc D d Q hD hQ hscale hdegree hlen hNloss hNblock
  have hR:2* ((X ∪ Y).card+16*D+1) ≤ d:=by
    rw [card_union_of_disjoint hXY,hX,hY]
    dsimp [C] at hC
    omega
  have htarget:32*D+8* (4*D) ^ 2+4 ≤ n:=by dsimp [K] at hn;omega
  have hpath:n ≤ p.length+2:=by
    change c.length ≤ p.length+M+H at hpL
    dsimp [K] at hnc
    omega
  have hX':16*D+8* (4*D) ^ 2+1 ≤ X.card:=by
    change X.card=16*D+8* (4*D) ^ 2+2 at hX
    omega
  have hY':16*D+8* (4*D) ^ 2 ≤ Y.card:=hY.ge
  obtain ⟨q,hq,hqlen⟩ :=u9 G D d hD
    hscale hdegree hNshort X Y hXY hcomplete hX' hY' hR u v hu hv huv p hp hpOff
    n htarget hpath (hpar.trans hpPar.symm)
  exact ⟨u,q,hq,hqlen⟩
theorem uR (D:ℕ) (hD:0 < D) :
    ∃ N₀ K :ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (d n :ℕ),
      N₀ ≤ ftCard V → ftCard V ≤ D *d → (∀ v,d ≤ G.degree v) →
      3 ≤ n → Odd n → K ≤ n → ¬ cycleGraph n ⊑ G →
      ∀ (z:V) (c:G.Walk z z),c.IsCycle → Odd c.length → c.length < n+K:=by
  obtain ⟨N₀,K,hspec⟩ :=zG D hD
  refine ⟨N₀,K,?_⟩
  intro V _ _ G _ d n hN hscale hdegree hn hodd hnK hno z c hc hcodd
  by_contra hlong
  have hpar:n%2=c.length%2:= (natOI.mp hodd).trans (natOI.mp hcodd).symm
  obtain ⟨w,q,hq,hqlen⟩ :=hspec G d hN hscale hdegree z c hc n hnK (by omega) hpar
  apply hno
  exact (cycleGraph_isContained_iff (by omega)).mpr ⟨w,q,hq,hqlen⟩
end Erdos556
namespace Erdos556
open SimpleGraph
def dj {V:Type*} [DecidableEq V] (G:SimpleGraph V)
    (S:Finset V) (v:S) :
    (G.induce (S:Set V)).induce ({v}ᶜ:Set S) ≃g
      G.induce (S.erase v.val:Set V) where
  toEquiv:=
    { toFun:=fun x => ⟨x.val.val,fsME.mpr ⟨by
        intro h
        exact x.property (subExt h),x.val.property⟩⟩
      invFun:=fun x => ⟨⟨x.val,(fsME.mp x.property).2⟩,by
        intro h
        exact (fsME.mp x.property).1 (congrArg subVal h)⟩
      left_inv:=fun _ => rfl
      right_inv:=fun _ => rfl}
  map_rel_iff':=by intro x y;rfl
theorem rN {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) (v:S) :
    (G.induce (S.erase v.val:Set V)).edgeFinset.card+
      (G.induce (S:Set V)).degree v = (G.induce (S:Set V)).edgeFinset.card:=by
  rw [← (dj G S v).card_edgeFinset_eq]
  rw [card_edgeFinset_induce_compl_singleton,card_edgeFinset_deleteIncidenceSet]
  exact natSAC ((G.induce (S:Set V)).degree_le_card_edgeFinset v)
theorem a4 {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (d:ℝ) :
    ∃ S :Finset V,
      (G.edgeFinset.card:ℝ) - d*ftCard V ≤
        ((G.induce (S:Set V)).edgeFinset.card:ℝ) - d*S.card ∧
      ∀ v :S,d < (G.induce (S:Set V)).degree v :=by
  classical
  let excess (S:Finset V) : ℝ:=
    ((G.induce (S:Set V)).edgeFinset.card:ℝ) - d*S.card
  let baseline:ℝ:= (G.edgeFinset.card:ℝ) - d*ftCard V
  let good:Finset (Finset V) :=fsUniv.filter fun S => baseline ≤ excess S
  have huniv: (fsUniv:Finset V) ∈ good:=by
    have he: (G.induce ((fsUniv:Finset V) : Set V)).edgeFinset.card=
        G.edgeFinset.card:=by
      rw [← G.card_filter_edgeFinset_toFinset_subset fsUniv]
      simp
    simp [good,excess,baseline,he]
  obtain ⟨S,hS,hminimal⟩ :=good.exists_min_image fsCard ⟨_,huniv⟩
  have hgood:baseline ≤ excess S := (fsMF.mp hS).2
  refine ⟨S,hgood,?_⟩
  intro v
  by_contra hdegree
  have hdegree': ((G.induce (S:Set V)).degree v :ℝ) ≤ d:=by
    exact le_of_not_gt hdegree
  let T :=S.erase v.val
  have hcard:T.card+1=S.card:=Finset.card_erase_add_one v.property
  have hedge:=rN G S v
  have hedgeR: ((G.induce (T:Set V)).edgeFinset.card:ℝ) +
      (G.induce (S:Set V)).degree v = (G.induce (S:Set V)).edgeFinset.card:=by
    exact_mod_cast hedge
  have hcardR: (T.card:ℝ) + 1=S.card:=by exact_mod_cast hcard
  have hT:T ∈ good:=by
    apply fsMF.mpr
    refine ⟨fsMU2 _,?_⟩
    dsimp [excess] at hgood ⊢
    nlinarith
  have hle:=hminimal T hT
  omega
end Erdos556
namespace Erdos556
open SimpleGraph Finset
noncomputable def sy {V:Type*} [DecidableEq V] (G:SimpleGraph V)
    (S:Finset V) (T:Finset S) :
    (G.induce (S:Set V)).induce (T:Set S) ≃g
      G.induce (T.map (fnSubty (fun v => v ∈ S)) : Set V) :=by
  let f : ↥(T:Set S) → ↥(T.map (fnSubty (fun v => v ∈ S)) : Set V) :=
    fun x => ⟨x.val.val,mem_map.mpr ⟨x.val,x.property,rfl⟩⟩
  have hinj:Function.Injective f :=by
    intro x y h
    apply subExt
    apply subExt
    change (f x).val= (f y).val
    exact congrArg subVal h
  have hsurj:Function.Surjective f :=by
    intro y
    obtain ⟨x,hx,hxy⟩ :=mem_map.mp y.property
    exact ⟨⟨x,hx⟩,subExt hxy⟩
  exact { toEquiv:=Equiv.ofBijective f ⟨hinj,hsurj⟩,map_rel_iff':=Iff.rfl}
theorem u7 {V:Type*} [Finite V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (k η :ℝ) (hη:0 ≤ η)
    (A:Finset V)
    (he:k*A.card+η* (A.card:ℝ) ^ 2 < ((G.induce (A:Set V)).edgeFinset.card:ℝ)) :
    ∃ S :Finset V,S.Nonempty ∧
      k*S.card+η* (S.card:ℝ) ^ 2 < ((G.induce (S:Set V)).edgeFinset.card:ℝ) ∧
      (∀ v :S,k < (G.induce (S:Set V)).degree v) ∧
      ∀ T :Finset V,T.card < S.card →
        ((G.induce (T:Set V)).edgeFinset.card:ℝ) ≤ k*T.card+η* (T.card:ℝ) ^ 2:=by
  classical
  let:=ftOfFin V
  let good:Finset (Finset V) :=univ.filter fun S =>
    k*S.card+η* (S.card:ℝ) ^ 2 < ((G.induce (S:Set V)).edgeFinset.card:ℝ)
  have hA:A ∈ good:=mem_filter.mpr ⟨mem_univ _,he⟩
  obtain ⟨S,hS,hminimal⟩ :=good.exists_min_image fsCard ⟨_,hA⟩
  have hgood:= (mem_filter.mp hS).2
  have hsmall (T:Finset V) (hT:T.card < S.card) :
      ((G.induce (T:Set V)).edgeFinset.card:ℝ) ≤ k*T.card+η* (T.card:ℝ) ^ 2:=by
    by_contra hn
    have hTgood:T ∈ good:=mem_filter.mpr ⟨mem_univ _,lt_of_not_ge hn⟩
    exact (Nat.not_le_of_gt hT) (hminimal T hTgood)
  have hdegree (v:S) : k < (G.induce (S:Set V)).degree v :=by
    by_contra hdeg
    have hdeg':=le_of_not_gt hdeg
    let T :=S.erase v.val
    have hcard:T.card+1=S.card:=card_erase_add_one v.property
    have hcardR: (T.card:ℝ) + 1=S.card:=by exact_mod_cast hcard
    have hedge:=rN G S v
    have hedgeR: ((G.induce (T:Set V)).edgeFinset.card:ℝ) +
        (G.induce (S:Set V)).degree v = (G.induce (S:Set V)).edgeFinset.card:=by
      exact_mod_cast hedge
    have hT:=hsmall T (by omega)
    have hnonneg:=mul_nonneg hη (by positivity: (0:ℝ) ≤ 2* (T.card:ℝ) + 1)
    rw [← hcardR] at hgood
    nlinarith
  have hnonempty:S.Nonempty:=by
    by_contra h
    have hzero:S.card=0:=card_eq_zero.mpr (not_nonempty_iff_eq_empty.mp h)
    have hScard:ftCard (S:Set V) = S.card:=by
      calc
        ftCard (S:Set V) = (S:Set V).ncard:=natCEFC.symm
        _=S.card:=stNCF S
    have hb:= (G.induce (S:Set V)).card_edgeFinset_le_card_choose_two
    rw [hScard,hzero] at hb
    norm_num only [Nat.choose_zero_succ] at hb
    have hezero: (G.induce (S:Set V)).edgeFinset.card=0:=Nat.eq_zero_of_le_zero hb
    simp [hzero,hezero] at hgood
  exact ⟨S,hnonempty,hgood,hdegree,hsmall⟩
theorem s5
    {V:Type*} [Finite V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (k η :ℝ) (hη:0 ≤ η) (A:Finset V)
    (he:k*A.card+η* (A.card:ℝ) ^ 2 < ((G.induce (A:Set V)).edgeFinset.card:ℝ)) :
    ∃ S :Finset V,S.Nonempty ∧
      k*S.card+η* (S.card:ℝ) ^ 2 < ((G.induce (S:Set V)).edgeFinset.card:ℝ) ∧
      (∀ v :S,k < (G.induce (S:Set V)).degree v) ∧
      ∀ T :Finset S,T.card < S.card →
        (((G.induce (S:Set V)).induce (T:Set S)).edgeFinset.card:ℝ) ≤
          k*T.card+η* (T.card:ℝ) ^ 2:=by
  classical
  let:=ftOfFin V
  obtain ⟨S,hS,hdense,hdeg,hsmall⟩ :=
    u7 G k η hη A he
  refine ⟨S,hS,hdense,hdeg,?_⟩
  intro T hT
  have h :=hsmall (T.map (fnSubty (fun v => v ∈ S)))
    (by simpa only [card_map] using hT)
  rw [← (sy G S T).card_edgeFinset_eq,card_map] at h
  exact h
theorem yr (a b t N k β η e :ℝ)
    (ha0:0 ≤ a) (hb0:0 ≤ b) (ht0:0 ≤ t) (hk0:0 ≤ k) (hη:0 ≤ η)
    (hN:N=a+b+t) (ht:t ≤ β) (hβ:β ≤ k)
    (ha:k-β ≤ a) (hb:k-β ≤ b)
    (hbudget:β*N ≤ 2*η* (k-β) ^ 2)
    (he:e ≤ k* (a+b) + η* (a^2+b^2) + t*N) :
    e ≤ k*N+η*N^2:=by
  have hr0:0 ≤ k-β:=sub_nonneg.mpr hβ
  have hab: (k-β) ^ 2 ≤ a*b:=by
    simpa only [pow_two] using mul_le_mul ha hb hr0 ha0
  have hprod:=mul_le_mul_of_nonneg_left hab (by positivity:0 ≤ 2*η)
  have hN0:0 ≤ N:=by linarith
  have htN:=mul_le_mul_of_nonneg_right ht hN0
  have hkt:=mul_nonneg hk0 ht0
  have hquad:=mul_nonneg hη (mul_nonneg ht0 (by linarith:0 ≤ 2*N-t))
  have hid:k*N+η*N^2-
      (k* (a+b) + η* (a^2+b^2) + t*N) =
      k*t+η*t* (2*N-t) + 2*η* (a*b) - t*N:=by
    rw [hN]
    ring
  nlinarith
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem rk {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (S:Finset V) (h: ¬ (G.induce (S:Set V)ᶜ).Preconnected) :
    ∃ A B:Finset V,A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      Disjoint A S ∧ Disjoint B S ∧ A ∪ B ∪ S=univ ∧
      ∀ a ∈ A,∀ b ∈ B,¬ G.Adj a b:=by
  classical
  let U := (S:Set V)ᶜ
  let H :=G.induce U
  obtain ⟨u,v,huv⟩ : ∃ u v:U,¬ H.Reachable u v:=by
    simpa only [SimpleGraph.Preconnected,not_forall] using h
  let A := ({x:V | ∃ hx:x ∉ S,H.Reachable u ⟨x,hx⟩} : Set V).toFinset
  let B := (S ∪ A)ᶜ
  have hA (x:V) : x ∈ A ↔ ∃ hx:x ∉ S,H.Reachable u ⟨x,hx⟩ :=by
    simp only [A,stMT,Set.mem_ofPred_eq]
  have hAS:Disjoint A S:=by
    rw [fsDL]
    intro x hx
    exact ((hA x).mp hx).choose
  have hAB:Disjoint A B:=by
    rw [fsDL]
    intro x hxA hxB
    exact (mem_compl.mp hxB) (mem_union_right S hxA)
  have hBS:Disjoint B S:=by
    rw [fsDL]
    intro x hxB hxS
    exact (mem_compl.mp hxB) (mem_union_left A hxS)
  have hAnon:A.Nonempty:= ⟨u.val,(hA _).mpr ⟨u.property,.rfl⟩⟩
  have hBnon:B.Nonempty:=by
    refine ⟨v.val,?_⟩
    simp only [B,mem_compl,mem_union,not_or]
    refine ⟨v.property,?_⟩
    intro hvA
    obtain ⟨_,hreach⟩ := (hA _).mp hvA
    exact huv hreach
  have hcover:A ∪ B ∪ S=univ:=by
    calc
      A ∪ B ∪ S= (S ∪ A) ∪ (S ∪ A)ᶜ:=by dsimp [B];ac_rfl
      _=univ:=Finset.union_compl (S ∪ A)
  refine ⟨A,B,hAnon,hBnon,hAB,hAS,hBS,hcover,?_⟩
  intro a ha b hb hab
  obtain ⟨haS,hreach⟩ := (hA a).mp ha
  have hbS:b ∉ S:=fun h => (mem_compl.mp hb) (mem_union_left A h)
  have hadj:H.Adj ⟨a,haS⟩ ⟨b,hbS⟩ :=hab
  have hbA:b ∈ A:= (hA b).mpr ⟨hbS,hreach.trans hadj.reachable⟩
  exact (mem_compl.mp hb) (mem_union_right S hbA)
theorem qR {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (A B S:Finset V)
    (hcover:A ∪ B ∪ S=univ) (hcross: ∀ a ∈ A,∀ b ∈ B,¬ G.Adj a b)
    (a:V) (ha:a ∈ A) : G.degree a ≤ A.card+S.card:=by
  have hsub:G.neighborFinset a ⊆ A ∪ S :=by
    intro x hx
    have hall:x ∈ A ∪ B ∪ S:=by rw [hcover];exact mem_univ _
    rcases mem_union.mp hall with hAB | hS
    · rcases mem_union.mp hAB with hA | hB
      · exact mem_union_left _ hA
      · exact (hcross a ha x hB ((G.mem_neighborFinset a x).mp hx)).elim
    · exact mem_union_right _ hS
  rw [← G.card_neighborFinset_eq_degree a]
  exact (card_le_card hsub).trans (card_union_le A S)
theorem vp {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (A B S:Finset V)
    (hcover:A ∪ B ∪ S=univ) (hcross: ∀ a ∈ A,∀ b ∈ B,¬ G.Adj a b) :
    G.edgeFinset.card ≤ (G.induce (A:Set V)).edgeFinset.card+
      (G.induce (B:Set V)).edgeFinset.card+S.card*ftCard V :=by
  classical
  let X :=G.edgeFinset.filter (fun e => e.toFinset ⊆ A)
  let Y :=G.edgeFinset.filter (fun e => e.toFinset ⊆ B)
  let Z :=S.biUnion (fun v => G.incidenceFinset v)
  have hpart (v:V) (hv:v ∉ S) : v ∈ A ∨ v ∈ B:=by
    have hall:v ∈ A ∪ B ∪ S:=by rw [hcover];exact mem_univ v
    exact mem_union.mp ((mem_union.mp hall).resolve_right hv)
  have hZmem (e:Sym2 V) (he:e ∈ G.edgeFinset) (v:V) (hv:v ∈ S) (hve:v ∈ e) :
      e ∈ Z:=by
    apply mem_biUnion.mpr
    refine ⟨v,hv,?_⟩
    rw [G.incidenceFinset_eq_filter]
    exact mem_filter.mpr ⟨he,hve⟩
  have hedgecover:G.edgeFinset ⊆ X ∪ Y ∪ Z:=by
    intro e he
    rcases e with ⟨⟨u,v⟩⟩
    by_cases huS:u ∈ S
    · exact mem_union_right _ (hZmem _ he u huS (by simp))
    by_cases hvS:v ∈ S
    · exact mem_union_right _ (hZmem _ he v hvS (by simp))
    have huv:G.Adj u v:=by simpa using he
    rcases hpart u huS with huA | huB <;> rcases hpart v hvS with hvA | hvB
    · apply mem_union_left
      apply mem_union_left
      exact mem_filter.mpr ⟨he,by simpa only [Sym2.toFinset_mk_eq,
        insert_subset_iff,singleton_subset_iff] using And.intro huA hvA⟩
    · exact (hcross u huA v hvB huv).elim
    · exact (hcross v hvA u huB huv.symm).elim
    · apply mem_union_left
      apply mem_union_right
      exact mem_filter.mpr ⟨he,by simpa only [Sym2.toFinset_mk_eq,
        insert_subset_iff,singleton_subset_iff] using And.intro huB hvB⟩
  have hX:X.card= (G.induce (A:Set V)).edgeFinset.card:=
    G.card_filter_edgeFinset_toFinset_subset A
  have hY:Y.card= (G.induce (B:Set V)).edgeFinset.card:=
    G.card_filter_edgeFinset_toFinset_subset B
  have hZ:Z.card ≤ S.card*ftCard V :=by
    calc
      Z.card ≤ ∑ v ∈ S,(G.incidenceFinset v).card:=card_biUnion_le
      _ ≤ ∑ _v ∈ S,ftCard V :=by
        apply sum_le_sum
        intro v _
        rw [G.card_incidenceFinset_eq_degree]
        exact (G.degree_lt_card_verts v).le
      _=S.card*ftCard V :=by simp
  have h1:=card_le_card hedgecover
  have h2:=card_union_le (X ∪ Y) Z
  have h3:=card_union_le X Y
  omega
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem sl
    {V:Type*} [Fintype V] (G:SimpleGraph V) [DecidableRel G.Adj]
    (b:ℕ) (k η :ℝ) (hk:0 ≤ k) (hη:0 ≤ η) (hbk: (b:ℝ) ≤ k)
    (hbudget: (b:ℝ) * ftCard V ≤ 2 *η* (k-b) ^ 2)
    (he:k*ftCard V +η* (ftCard V :ℝ) ^ 2 < (G.edgeFinset.card:ℝ))
    (hdeg: ∀ v,k < (G.degree v :ℝ))
    (hsmall: ∀ T:Finset V,T.card < ftCard V →
      ((G.induce (T:Set V)).edgeFinset.card:ℝ) ≤ k*T.card+η* (T.card:ℝ) ^ 2) :
    q8 G b:=by
  classical
  intro S hS
  by_contra hconn
  obtain ⟨A,B,hA,hB,hAB,hAS,hBS,hcover,hcross⟩ :=
    rk G S hconn
  have hASBS:Disjoint (A ∪ B) S :=Finset.disjoint_union_left.mpr ⟨hAS,hBS⟩
  have hcards:A.card+B.card+S.card=ftCard V :=by
    have h :=congrArg fsCard hcover
    simpa only [card_union_of_disjoint hASBS,card_union_of_disjoint hAB,card_univ] using h
  have hApos:=hA.card_pos
  have hBpos:=hB.card_pos
  have heA:=hsmall A (by omega)
  have heB:=hsmall B (by omega)
  have hSR: (S.card:ℝ) ≤ b:=by exact_mod_cast hS
  obtain ⟨a,haA⟩ :=hA
  obtain ⟨c,hcB⟩ :=hB
  have hda:=qR G A B S hcover hcross a haA
  have hdc:=qR G B A S
    (by rw [union_comm B A];exact hcover)
    (fun x hx y hy hxy=> hcross y hy x hx hxy.symm) c hcB
  have hdaR: (G.degree a :ℝ) ≤ (A.card:ℝ) + S.card:=by exact_mod_cast hda
  have hdcR: (G.degree c :ℝ) ≤ (B.card:ℝ) + S.card:=by exact_mod_cast hdc
  have ha:k- (b:ℝ) ≤ A.card:=by have:=hdeg a;linarith
  have hb:k- (b:ℝ) ≤ B.card:=by have:=hdeg c;linarith
  have hedge:=vp G A B S hcover hcross
  have hedgeR: (G.edgeFinset.card:ℝ) ≤
      ((G.induce (A:Set V)).edgeFinset.card:ℝ) +
      ((G.induce (B:Set V)).edgeFinset.card:ℝ) + (S.card:ℝ) * ftCard V :=by
    exact_mod_cast hedge
  have hbound:=yr (A.card:ℝ) (B.card:ℝ) (S.card:ℝ)
    (ftCard V :ℝ) k (b:ℝ) η (G.edgeFinset.card:ℝ)
    (by positivity) (by positivity) (by positivity) hk hη
    (by exact_mod_cast hcards.symm) hSR hbk ha hb hbudget (by linarith)
  exact (not_le_of_gt he) hbound
theorem sR
    {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (b:ℕ) (k η :ℝ)
    (hk:0 ≤ k) (hη:0 ≤ η) (hbk: (b:ℝ) ≤ k)
    (hbudget: (b:ℝ) * ftCard V ≤ 2 *η* (k-b) ^ 2)
    (A:Finset V)
    (he:k*A.card+η* (A.card:ℝ) ^ 2 < ((G.induce (A:Set V)).edgeFinset.card:ℝ)) :
    ∃ S :Finset V,S.Nonempty ∧
      k*S.card+η* (S.card:ℝ) ^ 2 < ((G.induce (S:Set V)).edgeFinset.card:ℝ) ∧
      (∀ v :S,k < (G.induce (S:Set V)).degree v) ∧
      q8 (G.induce (S:Set V)) b :=by
  classical
  obtain ⟨S,hS,hdense,hdeg,hsmall⟩ :=
    s5 G k η hη A he
  have hcard:ftCard (S:Set V) = S.card:=by
    calc
      ftCard (S:Set V) = (S:Set V).ncard:=natCEFC.symm
      _=S.card:=stNCF S
  have hcardle: (ftCard (S:Set V) : ℝ) ≤ ftCard V :=by
    exact_mod_cast ftCLOI (fun x : (S:Set V) => x.val) subVI
  have hbudget': (b:ℝ) * ftCard (S:Set V) ≤ 2*η* (k-b) ^ 2:=
    (mul_le_mul_of_nonneg_left hcardle (natCN b)).trans hbudget
  refine ⟨S,hS,hdense,hdeg,?_⟩
  apply sl (G.induce (S:Set V))
    b k η hk hη hbk hbudget'
  · simpa only [hcard] using hdense
  · exact hdeg
  · intro T hT
    exact hsmall T (by simpa only [hcard] using hT)
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem rc {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) :
    G.edgeFinset.card ≤ (G.induce (S:Set V)ᶜ).edgeFinset.card+
      S.card*ftCard V :=by
  classical
  let A :=G.edgeFinset.filter (fun e => e.toFinset ⊆ Sᶜ)
  let B :=S.biUnion (fun v => G.incidenceFinset v)
  have hcover:G.edgeFinset ⊆ A ∪ B:=by
    intro e he
    by_cases h :e.toFinset ⊆ Sᶜ
    · exact mem_union_left _ (mem_filter.mpr ⟨he,h⟩)
    · obtain ⟨x,hxe,hx⟩ :=not_subset.mp h
      have hxS:x ∈ S:=by simpa only [mem_compl,not_not] using hx
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨x,hxS,?_⟩
      rw [G.incidenceFinset_eq_filter]
      exact mem_filter.mpr ⟨he,by simpa using hxe⟩
  have hA:A.card= (G.induce (S:Set V)ᶜ).edgeFinset.card:=by
    have h :=congrArg fsCard (G.map_edgeFinset_induce (s:= (S:Set V)ᶜ))
    simp only [card_map] at h
    have heq:G.edgeFinset ∩ ((S:Set V)ᶜ).toFinset.sym2=A:=by
      simp [A,G.filter_edgeFinset_toFinset_subset]
    rw [heq] at h
    exact h.symm
  have hB:B.card ≤ S.card*ftCard V :=by
    calc
      B.card ≤ ∑ v ∈ S,(G.incidenceFinset v).card:=card_biUnion_le
      _ ≤ ∑ _v ∈ S,ftCard V :=by
        apply sum_le_sum
        intro v _
        rw [G.card_incidenceFinset_eq_degree]
        exact (G.degree_lt_card_verts v).le
      _=S.card*ftCard V :=by simp
  exact (card_le_card hcover).trans ((card_union_le A B).trans (by omega))
end Erdos556
section dK
/-
Copyright (c) 2024 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song, Yury Kudryashov
-/
namespace Erdos556.Function
open Filter _root_.Function
variable {α:Type*} [PartialOrder α] [hα:WellFoundedGT α] {f:α → α}
lemma Monotone.eventuallyConst_atTop {ι:Type*}
    [SemilatticeSup ι] [Nonempty ι] {g:ι → α} (hg:Monotone g) :
    EventuallyConst g atTop:=by
  rw [Filter.eventuallyConst_atTop]
  obtain ⟨x,hx⟩ : ∃ x,g x=_:=hα.wf.min_mem _ (Set.range_nonempty _)
  refine ⟨x,fun z hz ↦ ?_⟩
  have hxz:g x ≤ g z:=hg hz
  have hnlt: ¬g x < g z:=by
    simpa [hx] using hα.wf.not_lt_min (Set.range g) (stMRS z)
  exact (eq_of_le_of_not_lt hxz hnlt).symm
lemma rH (hf:id ≤ f) (x:α) :
    EventuallyConst (fun n ↦ f^[n] x) atTop:=
  Monotone.eventuallyConst_atTop (fun _ _ h ↦ monotone_iterate_of_id_le hf h x)
noncomputable def ai {f:ℕ → α} (hf:EventuallyConst f atTop) :=
  (eventuallyConst_atTop.mp hf).choose
noncomputable def rT (hf:id ≤ f) (x:α) : ℕ:=
  ai (rH hf x)
lemma wK (hf:id ≤ f) (x:α) :
    ∀ m ≥ rT hf x,
      f^[m] x =f^[rT hf x] x :=
  (eventuallyConst_atTop.mp (rH hf x)).choose_spec
noncomputable def v3 (hf:id ≤ f) (x:α) :=
  f^[rT hf x] x
lemma t0 (hf:id ≤ f) (x:α) :
    IsFixedPt f (v3 hf x) :=by
  unfold IsFixedPt
  simp only [v3,← iterate_succ_apply']
  apply wK
  simp
lemma tJ (hf:id ≤ f) (x:α) : x ≤ v3 hf x :=by
  simp only [v3]
  conv_lhs=> rw [← iterate_zero_apply f x]
  apply f.monotone_iterate_of_id_le hf
  simp
end Erdos556.Function
end dK
section d0
/-
Copyright (c) 2024 Shuhao Song. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Shuhao Song
-/
/-
# Bondy--Chvátal theorem
This is the proved Mathlib development by Shuhao Song from commit
`c83689ab8f` of the `meow-sister/BondyChvatal_PR` branch, vendored here
because the theorem is not part of the Mathlib v4.33.0 module set.
-/
namespace SimpleGraph
open Walk Function Erdos556.Function
open scoped List
variable {V:Type*} [Fintype V] [DecidableEq V] (G:SimpleGraph V)
def rO:=by
  classical
  exact { (u,v) : V × V | G.degree u +G.degree v ≥ (ftCard V) ∧ u ≠ v ∧ ¬G.Adj u v}
noncomputable def qg:SimpleGraph V :=by
  classical
  exact if h : (rO G).Nonempty then
    G ⊔ edge h.some.1 h.some.2
  else
    G
omit [DecidableEq V] in
lemma s6:G ≤ qg G :=by
  classical
  unfold qg
  split_ifs with h
  repeat simp
noncomputable def qE:=Erdos556.Function.v3 s6 G
omit [DecidableEq V] in
lemma sa: (qg G \ G).edgeSet.Subsingleton:=by
  classical
  unfold qg
  split_ifs with h
  · simp only [sup_sdiff_left_self,edgeSet_sdiff]
    apply Set.Subsingleton.anti (t:= (edge h.some.1 h.some.2).edgeSet)
    · have:h.some.1 ≠ h.some.2:=h.some_mem.2.1
      simp [edgeSet_edge_of_ne this]
    · apply Set.sdiff_subset
  · simp
omit [DecidableEq V] in
lemma xx {u v :V} (huv: ¬G.Adj u v)
    (huv':G.qg.Adj u v) :
    G.qg.deleteEdges {s(u,v)} = G:=by
  classical
  rw [← edgeSet_inj]
  ext e
  simp only [edgeSet_deleteEdges,Set.mem_sdiff,stMSI]
  apply Iff.intro
  · rintro ⟨he₁,he₂⟩
    by_contra he₃
    have mem₁:e ∈ (qg G \ G).edgeSet:=by simpa using ⟨he₁,he₃⟩
    have mem₂:s(u,v) ∈ (qg G \ G).edgeSet:=by simpa using ⟨huv',huv⟩
    exact he₂ <| (sa G) mem₁ mem₂
  · intro he
    apply And.intro (edgeSet_mono (s6 G) he)
    intro he'
    simp only [he',mem_edgeSet] at he
    exact huv he
omit [DecidableEq V] in
lemma uY:
    qg G =G ↔ rO G = ∅ :=by
  classical
  unfold qg
  split_ifs with h
  · have: (G ⊔ edge h.some.1 h.some.2=G) ↔ False:=by
      rw [sup_eq_left,iff_false]
      intro hle
      have hedge: (edge h.some.1 h.some.2).Adj h.some.1 h.some.2:=
        (edge_adj ..).mpr ⟨orInl ⟨rfl,rfl⟩,h.some_mem.2.1⟩
      exact h.some_mem.2.2 (hle hedge)
    simp only [this,false_iff]
    simpa [← Set.not_nonempty_iff_eq_empty] using h
  · simpa [← Set.not_nonempty_iff_eq_empty] using h
omit [DecidableEq V] in
open Classical in
lemma zF:qg G =G ↔
    ∀ {u} {v},u ≠ v → G.degree u +G.degree v ≥ (ftCard V) → G.Adj u v:=by
  classical
  rw [uY]
  constructor
  · intro hempty u v huv hdeg
    by_contra hadj
    have hmem: (u,v) ∈ rO G := ⟨hdeg,huv,hadj⟩
    rw [hempty] at hmem
    exact hmem
  · intro h
    ext ⟨u,v⟩
    constructor
    · intro huv
      exact (huv.2.2 (h huv.2.1 huv.1)).elim
    · intro hfalse
      exact hfalse.elim
omit [DecidableEq V] in
open Classical in
lemma zr {u v :V} (huv: ¬G.Adj u v)
    (huv':G.qg.Adj u v) :
    G.degree u +G.degree v ≥ (ftCard V) :=by
  classical
  have ne: (rO G).Nonempty:=by
    by_contra h
    simp only [Set.nonempty_iff_ne_empty,← uY,Decidable.not_not] at h
    rw [h] at huv'
    exact huv huv'
  let w :=ne.some
  have prop₁:G.degree w.1+G.degree w.2 ≥ (ftCard V) :=ne.some_mem.1
  have mem₁:s(u,v) ∈ (qg G \ G).edgeSet:=by simpa using ⟨huv',huv⟩
  have mem₂:s(w.1,w.2) ∈ (qg G \ G).edgeSet:=by
    have prop₂:w.1 ≠ w.2:=ne.some_mem.2.1
    have prop₃: ¬G.Adj w.1 w.2:=ne.some_mem.2.2
    have G_eq:G.qg=G ⊔ edge w.1 w.2:=by simp [qg,ne,w]
    simpa [-Prod.mk.eta,G_eq,edge_adj] using And.intro prop₂ prop₃
  have edge_eq:= (sa G mem₁ mem₂).symm
  simp only [Prod.mk.eta,Sym2.eq,Sym2.rel_iff'] at edge_eq
  rcases edge_eq with h | h
  · rw [h] at prop₁
    simpa using prop₁
  · rw [h] at prop₁
    rw [add_comm]
    simpa using prop₁
omit [DecidableEq V] in
lemma rs:G ≤ qE G :=by
  classical
  rw [qE]
  apply Erdos556.Function.tJ
omit [DecidableEq V] in
open Classical in
lemma rK: ∀ {u} {v},u ≠ v →
    G.qE.degree u +G.qE.degree v ≥ (ftCard V) →
      G.qE.Adj u v:=by
  classical
  have:qg (qE G) = qE G :=
    t0 s6 G
  rwa [zF] at this
variable {G}
namespace Walk
variable {a:V} {p:G.Walk a a}
omit [Fintype V] in
protected theorem IsHamiltonianCycle.aC [Finite V] (hp:p.IsHamiltonianCycle)
    {H:SimpleGraph V} (h: ∀ e ∈ p.edges,e ∈ H.edgeSet) :
    (p.transfer H h).IsHamiltonianCycle:=by
  classical
  let:=ftOfFin V
  rw [isHamiltonianCycle_iff_isCycle_and_length_eq]
  exact ⟨hp.isCycle.transfer h,by simpa using hp.length_eq⟩
omit [DecidableEq V] [Fintype V] in
private lemma IsCycle.rB (hp:p.IsCycle)
    {d e :G.Dart} (hd:d ∈ p.darts) (he:e ∈ p.darts)
    (hfst:d.fst=e.fst) : d=e:=by
  classical
  obtain ⟨i,hi,rfl⟩ :=lsGOM hd
  obtain ⟨j,hj,rfl⟩ :=lsGOM he
  have hget:p.getVert i =p.getVert j :=by
    simpa [p.darts_getElem_eq_getVert i hi,p.darts_getElem_eq_getVert j hj] using hfst
  have hi':i ≤ p.length-1:=by
    have hi_len:i < p.length:=by simpa using hi
    omega
  have hj':j ≤ p.length-1:=by
    have hj_len:j < p.length:=by simpa using hj
    omega
  have hij:=hp.getVert_injOn' hi' hj' hget
  subst j
  rfl
omit [DecidableEq V] [Fintype V] in
private lemma IsCycle.zU (hp:p.IsCycle)
    {d e :G.Dart} (hd:d ∈ p.darts) (he:e ∈ p.darts)
    (hsnd:d.snd=e.snd) : d=e:=by
  classical
  obtain ⟨i,hi,rfl⟩ :=lsGOM hd
  obtain ⟨j,hj,rfl⟩ :=lsGOM he
  have hget:p.getVert (i+1) = p.getVert (j+1) :=by
    simpa [p.darts_getElem_eq_getVert i hi,p.darts_getElem_eq_getVert j hj] using hsnd
  have hi':i < p.length:=by simpa using hi
  have hj':j < p.length:=by simpa using hj
  have hij:=hp.getVert_injOn
    (show 1 ≤ i +1 ∧ i+1 ≤ p.length by omega)
    (show 1 ≤ j +1 ∧ j+1 ≤ p.length by omega) hget
  have:i=j:=Nat.add_right_cancel hij
  subst j
  rfl
omit [DecidableEq V] [Fintype V] in
private lemma uj {u v :V}
    {r:G.Walk u v} (hnodup:r.support.dropLast.Nodup)
    {d e :G.Dart} (hd:d ∈ r.darts) (he:e ∈ r.darts)
    (hfst:d.fst=e.fst) : d=e:=by
  classical
  obtain ⟨i,hi,rfl⟩ :=lsGOM hd
  obtain ⟨j,hj,rfl⟩ :=lsGOM he
  have hi':i < r.support.dropLast.length:=by simpa using hi
  have hj':j < r.support.dropLast.length:=by simpa using hj
  have hget:r.support.dropLast[i]'hi'=r.support.dropLast[j]'hj':=by
    simpa [r.fst_darts_getElem hi,r.fst_darts_getElem hj] using hfst
  have hij:= (List.Nodup.getElem_inj_iff hnodup).mp hget
  subst j
  rfl
private theorem rV
    (hp:p.length=ftCard V) (hV:3 ≤ ftCard V)
    (hsupport:p.support.tail.toFinset=fsUniv) :
    p.IsHamiltonianCycle:=by
  classical
  rw [isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨?_,hp⟩
  rw [isCycle_iff_isPath_tail_and_le_length]
  refine ⟨?_,by omega⟩
  apply IsPath.mk'
  rw [support_tail_of_not_nil p (by rw [not_nil_iff_lt_length,hp];omega)]
  have hcard:p.support.tail.toFinset.card=p.support.tail.length:=by
    rw [hsupport]
    simp [hp]
  have hmulti: ((p.support.tail:Multiset V).toFinset.card=
      (p.support.tail:Multiset V).card) :=by simpa using hcard
  simpa using Multiset.toFinset_card_eq_card_iff_nodup.mp hmulti
namespace IsHamiltonianCycle
omit [Fintype V]
variable (b:V)
private lemma yk (hp:p.IsHamiltonianCycle) : b ∈ p.support.tail:=by
  classical
  rw [← support_tail_of_not_nil p hp.not_nil]
  exact hp.isHamiltonian_tail.mem_support b
private lemma zj (hp:p.IsHamiltonianCycle) :
    b ∈ p.support.dropLast:=by
  classical
  have hb:b ∈ p.tail.support:=by
    simpa [support_tail_of_not_nil p hp.not_nil] using hp.yk b
  have hb':b ∈ p.dropLast.support:=
    (lsMI (support_tail_perm_support_dropLast p)).mp hb
  simpa [support_dropLast hp.not_nil] using hb'
noncomputable def zf (hp:p.IsHamiltonianCycle) : G.Dart:=
  Exists.choose <| show ∃ d ∈ p.darts,d.fst=b by
    simpa [← Walk.map_fst_darts] using hp.zj b
noncomputable def qk (hp:p.IsHamiltonianCycle) : V:=
  (hp.zf b).snd
lemma qH (hp:p.IsHamiltonianCycle) :
    ∃ d ∈ p.darts,d.fst=b ∧ d.snd=hp.qk b :=by
  classical
  unfold qk zf
  generalize_proofs hd
  have hspec:=hd.choose_spec
  set d :=hd.choose
  exact ⟨d,hspec.1,hspec.2,rfl⟩
lemma xe (hp:p.IsHamiltonianCycle) : Function.Injective hp.qk:=by
  classical
  intro v₁ v₂ hnext
  obtain ⟨d₁,hd₁,hd₁fst,hd₁snd⟩ :=hp.qH v₁
  obtain ⟨d₂,hd₂,hd₂fst,hd₂snd⟩ :=hp.qH v₂
  have heq:d₁=d₂:=hp.isCycle.zU hd₁ hd₂ <| by
    rw [hd₁snd,hd₂snd]
    exact hnext
  rw [← hd₁fst,← hd₂fst,heq]
lemma uE (hp:p.IsHamiltonianCycle)
    {i:ℕ} (hi:i < p.length) (hi':p.getVert i =b) :
    p.getVert (i+1) = hp.qk b :=by
  classical
  have hiD:i < p.darts.length:=by simpa using hi
  have hdi:p.darts[i] ∈ p.darts:=lsGM hiD
  obtain ⟨d,hd,hdfst,hdsnd⟩ :=hp.qH b
  have hfst:p.darts[i].fst=d.fst:=by
    rw [p.darts_getElem_eq_getVert i hiD,hdfst]
    exact hi'
  have heq:=hp.isCycle.rB hdi hd hfst
  have hsnd:=congrArg (fun z :G.Dart ↦ z.snd) heq
  rw [p.darts_getElem_eq_getVert i hiD,hdsnd] at hsnd
  exact hsnd
lemma tX (hp:p.IsHamiltonianCycle) (hb:b ∈ p.support) (c:V) :
    ((hp.rotate hb).qk c) = hp.qk c :=by
  classical
  obtain ⟨d₁,hd₁,hd₁fst,hd₁snd⟩ := (hp.rotate hb).qH c
  obtain ⟨d₂,hd₂,hd₂fst,hd₂snd⟩ :=hp.qH c
  have hd₁':d₁ ∈ p.darts:=by
    simpa using (List.IsRotated.mem_iff (rotate_darts p b hb)).mp hd₁
  have heq:d₁=d₂:=hp.isCycle.rB hd₁' hd₂ <| by
    rw [hd₁fst,hd₂fst]
  rw [← hd₁snd,← hd₂snd,heq]
variable {b}
theorem t7 (hp:p.IsHamiltonianCycle) : hp.qk b ≠ b :=by
  classical
  obtain ⟨d,-,hdfst,hdsnd⟩ :=hp.qH b
  intro h
  exact d.adj.ne (hdfst.trans (hdsnd.trans h).symm)
theorem tL (hp:p.IsHamiltonianCycle) :
    hp.qk (hp.qk b) ≠ b:=by
  classical
  have hb:b ∈ p.support:=hp.mem_support b
  let q :=p.rotate b hb
  have hq:q.IsHamiltonianCycle:=hp.rotate hb
  have hlen:3 ≤ q.length:=hq.isCycle.three_le_length
  have hq0:q.getVert 0 =b:=by simp [q]
  have hq1:q.getVert 1 =hq.qk b :=
    hq.uE b (i:=0) (by omega) hq0
  have hq2:q.getVert 2 =hq.qk (hq.qk b) :=
    hq.uE (hq.qk b) (i:=1) (by omega) hq1
  have hrot: ∀ c,hq.qk c =hp.qk c :=by
    intro c
    change (hp.rotate hb).qk c =hp.qk c
    exact IsHamiltonianCycle.tX b hp hb c
  simp only [hrot] at hq1 hq2
  intro h
  have h02:q.getVert 0 =q.getVert 2 :=by rw [hq0,hq2,h]
  have:=hq.isCycle.getVert_injOn'
    (show 0 ≤ q.length-1 by omega)
    (show 2 ≤ q.length-1 by omega) h02
  omega
end IsHamiltonianCycle
end Walk
private theorem zi
    {u u' v v':V} {p:G.Walk u u'}
    (hV: (ftCard V) ≥ 3) (hp:p.support ~ fsUniv.toList)
    (ne:v ≠ u') (vu':G.Adj v u') (v'u:G.Adj v' u)
    (d:G.Dart) (hd:d ∈ p.darts) (hd₁:d.fst=v) (hd₂:d.snd=v') :
    IsHamiltonian G :=by
  classical
  have hv:v ∈ p.support:=by simp [lsMI hp]
  have not_nil: ¬(p.dropUntil v hv).Nil:=not_nil_of_ne ne
  have snd_eq_v': (p.dropUntil v hv).getVert 1 =v':=by
    have hsupport:p.support.Nodup:=by
      rw [List.Perm.nodup_iff hp]
      apply Finset.nodup_toList
    have hdrop:p.support.dropLast.Nodup:=p.support.dropLast_prefix.nodup hsupport
    have hfirst: (p.dropUntil v hv).firstDart not_nil ∈ p.darts:=
      p.darts_dropUntil_subset_darts hv
        ((p.dropUntil v hv).firstDart_mem_darts not_nil)
    have heq: (p.dropUntil v hv).firstDart not_nil=d:=
      uj hdrop hfirst hd (by simp [hd₁])
    have hsnd:=congrArg (fun z :G.Dart ↦ z.snd) heq
    simpa [hd₂] using hsnd
  let q := (p.takeUntil _ hv)
    |>.append vu'.toWalk
    |>.append (p.dropUntil v hv |>.tail |>.reverse.copy rfl snd_eq_v')
    |>.append v'u.toWalk
  suffices q.IsHamiltonianCycle from fun _ ↦ ⟨u,q,this⟩
  apply rV
  · have hsum: (p.takeUntil v hv).length+ (p.dropUntil v hv).length=p.length:=by
      have hwalk:=congrArg Walk.length (p.take_spec hv)
      simpa only [wkLA] using hwalk
    have:=calc
      p.length+1=p.support.length:=by simp
      _=fsUniv.toList.length:=by apply List.Perm.length_eq hp
      _= (ftCard V) :=by simp
    have:=Walk.length_tail_add_one not_nil
    simp [q,add_assoc]
    omega
  · assumption
  · simp only [tail_support_append,support_cons,support_nil,List.tail_cons,support_copy,
      support_reverse,List.append_assoc,
      lsCA,lsTA,lsTC,
      lsTN,insert_empty_eq,Finset.union_insert,Finset.eq_univ_iff_forall,
      fsMI2,fsMU,lsMT,fsMS2,
      fsNE,false_or,q]
    intro w
    by_contra hw
    simp only [not_or] at hw
    rcases hw with ⟨hw₁,hw₂,hw₃,hw₄⟩
    have mem_tail:w ∈ p.support.tail:=by
      have mem:w ∈ p.support:=by simp [lsMI hp]
      rw [← Walk.cons_tail_support] at mem
      simp only [lsMC] at mem
      exact mem.resolve_left hw₄
    have not_mem_drop:w ∉ (p.dropUntil v hv).support.tail:=by
      have tail_not_nil: (p.dropUntil v hv).support.tail ≠ [] :=by
        have hpos:0 < (p.dropUntil v hv).length:=
          not_nil_iff_lt_length.mp not_nil
        apply lsNNOLP
        rw [List.length_tail,length_support]
        omega
      have: (p.dropUntil v hv).support.tail.getLast tail_not_nil=u':=by
        rw [List.getLast_tail,getLast_support]
      have hw_dropLast:
          w ∉ (p.dropUntil v hv).support.tail.dropLast:=by
        simpa only [List.tail_reverse,lsMR,
          support_tail_of_not_nil _ not_nil] using hw₃
      intro hwmem
      rw [← List.dropLast_append_getLast tail_not_nil,this,
        lsMA,lsMS] at hwmem
      exact hwmem.elim hw_dropLast hw₁
    have append:p.support.tail=
        (p.takeUntil v hv).support.tail++ (p.dropUntil v hv).support.tail:=by
      rw [← tail_support_append,take_spec]
    simp only [append,lsMA] at mem_tail
    rcases mem_tail with h | h
    · exact hw₂ h
    · exact not_mem_drop h
open Classical in
private theorem xN
    {u v :V} {q:G.qg.Walk u u} (hq:q.IsHamiltonianCycle)
    (hV: (ftCard V) ≥ 3) (huv:G.degree u +G.degree v ≥ (ftCard V))
    (hv:v=hq.qk u) (not_adj: ¬G.Adj u v) :
    ∃ w w' d,G.Adj w v ∧ G.Adj w' u ∧ d ∈ q.darts ∧ d.fst=w' ∧ d.snd=w:=by
  classical
  let X := (hq.qk ·) '' {w | G.Adj u w} \ {u}
  let Y := {w | G.Adj v w} \ {hq.qk v}
  have cardX:G.degree u -1 ≤ X.toFinset.card:=calc
    _= (G.neighborFinset u).card-1:=by simp
    _= (fsUniv.filter (G.Adj u)).card-1:=by rw [neighborFinset_eq_filter]
    _ ≤ ((fsUniv.filter (G.Adj u)).image (hq.qk ·)).card-
        ({u} : Finset _).card:=by
      simp [Finset.card_image_of_injective _ hq.xe]
    _ ≤ (((fsUniv.filter (G.Adj u)).image (hq.qk ·)) \ {u}).card:=by
      apply Finset.le_card_sdiff
    _=_:=by simp [X]
  have cardY:G.degree v -1 ≤ Y.toFinset.card:=calc
    _= (G.neighborFinset v).card-1:=by simp
    _ ≤ (fsUniv.filter (G.Adj v)).card- ({hq.qk v} : Finset _).card:=by
      simp [neighborFinset_eq_filter]
    _ ≤ (fsUniv.filter (G.Adj v) \ {hq.qk v}).card:=by
      apply Finset.le_card_sdiff
    _=_:=by simp [Y]
  have card_union: (X ∪ Y).toFinset.card ≤ (ftCard V) - 3:=calc
    _ ≤ ({v,hq.qk v,u}ᶜ:Finset _).card:=by
      apply fsCLC
      rw [Finset.subset_compl_comm]
      intro w hw
      simp only [fsMI2,fsMS2,Set.toFinset_union,
        Set.toFinset_sdiff,Set.toFinset_image,Set.toFinset_ofPred,Set.toFinset_singleton,
        Finset.compl_union,fsMI3,Finset.mem_compl,fsMS,
        fsMI,fsMF,fsMU2,true_and,not_and,
        Decidable.not_not,forall_exists_index,and_imp,X,Y] at hw ⊢
      apply And.intro
      · intro w' adj qk
        rcases hw with hw | hw | hw
        · rw [hw,hv] at qk
          rw [hq.xe qk] at adj
          simp at adj
        · rw [hw] at qk
          rw [hq.xe qk] at adj
          exact False.elim (not_adj adj)
        · exact hw
      · intro adj
        rcases hw with hw | hw | hw
        · rw [hw] at adj
          simp at adj
        · exact hw
        · rw [hw] at adj
          exact False.elim (not_adj adj.symm)
    _=_:=by
      suffices ({v,hq.qk v,u} : Finset _).card=3 by rw [Finset.card_compl,this]
      rw [fsCION,fsCION]
      · simp
      · simpa [hv] using hq.tL
      · simpa [hv] using And.intro hq.t7.symm hq.t7
  have non_empty: (X ∩ Y).toFinset.card ≠ 0:=fun h ↦ by
    suffices (ftCard V) - 2 ≤ (ftCard V) - 3 by omega
    calc
      _ ≤ (G.degree u +G.degree v) - 2:=natSLSR huv _
      _ ≤ (G.degree u -1) + (G.degree v -1) :=by omega
      _ ≤ X.toFinset.card+Y.toFinset.card:=add_le_add cardX cardY
      _= (X ∪ Y).toFinset.card+ (X ∩ Y).toFinset.card:=by
        simpa [-Set.toFinset_card] using (Finset.card_union_add_card_inter _ _).symm
      _ ≤ (ftCard V) - 3+0:=add_le_add card_union (le_of_eq h)
      _= (ftCard V) - 3:=by simp
  obtain ⟨w,hw⟩ :=Finset.card_ne_zero.mp non_empty
  simp only [Set.toFinset_inter,Set.toFinset_sdiff,Set.toFinset_image,
    Set.toFinset_ofPred,Set.toFinset_singleton,fsMI3,fsMS,
    fsMI,fsMF,fsMU2,true_and,fsMS2,
    X,Y] at hw
  rcases hw with ⟨⟨⟨w',hw'₁,hw'₂⟩,-⟩,hw₂,-⟩
  obtain ⟨d,hd₁,hd₂⟩ :=hq.qH w'
  rw [hw'₂] at hd₂
  exact ⟨w,w',d,hw₂.symm,hw'₁.symm,hd₁,hd₂⟩
theorem yp (hG:IsHamiltonian (qg G)) :
    IsHamiltonian G :=by
  classical
  by_cases trivial:ftCard V =1
  · exact absurd trivial
  · by_contra nonHamiltonian
    obtain ⟨a,p,hp⟩ :=hG trivial
    obtain ⟨d,hd,hd'⟩ : ∃ d ∈ p.darts,¬G.Adj d.fst d.snd:=by
      by_contra h
      simp only [not_exists,not_and,Decidable.not_not] at h
      have edgeSubset (e) (he:e ∈ p.edges) : e ∈ G.edgeSet:=by
        simp only [edges,lsMM] at he
        obtain ⟨d,hd,hd'⟩ :=he
        rw [← hd']
        exact h _ hd
      let q :=p.transfer G edgeSubset
      suffices q.IsHamiltonianCycle from nonHamiltonian (fun _ ↦ ⟨a,q,this⟩)
      exact hp.aC edgeSubset
    set u :=d.fst
    set v :=d.snd
    have hu:u ∈ p.support:=Walk.dart_fst_mem_support_of_mem_darts _ hd
    let q :=p.rotate u hu
    have hq:q.IsHamiltonianCycle:=hp.rotate hu
    have hd_q:d ∈ q.darts:=by
      simpa [q] using List.IsRotated.mem_iff (rotate_darts p u hu) |>.mpr hd
    have q_not_nil: ¬q.Nil:=by
      erw [nil_rotate]
      exact hp.1.not_nil
    have next_u_eq_v:q.getVert 1 =v:=by
      have heq:q.firstDart q_not_nil=d:=
        hq.isCycle.rB (q.firstDart_mem_darts q_not_nil) hd_q (by simp [u])
      have hsnd:=congrArg (fun z :G.qg.Dart ↦ z.snd) heq
      simpa [v] using hsnd
    have uv_not_edge:s(u,v) ∉ q.tail.edges:=by
      have:q=cons (q.adj_snd q_not_nil) q.tail:=by
        exact (q.cons_tail_eq q_not_nil).symm
      have:q.edges=s(u,v) ::q.tail.edges:=by
        simp only [this,edges_cons]
        simp [next_u_eq_v]
      intro h
      have nodup:=hq.1.edges_nodup
      rw [this] at nodup
      exact List.not_nodup_cons_of_mem h nodup
    have G_closure_del:G.qg.deleteEdges {s(u,v)} = G:=by
      exact xx _ hd' d.adj
    let q':=q.tail
      |>.toDeleteEdge s(u,v) uv_not_edge
      |>.transfer G (by
        simp (config:= {singlePass:=true}) only [← G_closure_del]
        exact edges_subset_edgeSet _)
      |>.copy next_u_eq_v rfl
    have perm_q':q'.support ~ fsUniv.toList:=by
      rw [isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one] at hq
      simp only [transfer_transfer,support_copy,support_transfer,
        List.perm_iff_count,q']
      intro a
      rw [List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp)]
      simpa [support_tail_of_not_nil _ q_not_nil] using hq.2 _
    have hV: (ftCard V) ≥ 3:=hq.length_eq ▸ hq.isCycle.three_le_length
    have deg_sum:=zr G hd' d.adj
    have next_u:v=hq.qk u :=by
      obtain ⟨d',hd'₁,hd'₂,hd'₃⟩ :=hq.qH u
      have heq:d=d':=
        hq.isCycle.rB hd_q hd'₁ (by simpa [u] using hd'₂.symm)
      change d.snd=hq.qk u
      rw [← hd'₃]
      exact congrArg (fun z :G.qg.Dart ↦ z.snd) heq
    obtain ⟨w,w',d',hw,hw',d'_mem,hd'₁,hd'₂⟩ :=
      xN hq hV deg_sum next_u hd'
    have q'_support:q'.support=q.support.tail:=by
      simp [q',support_tail_of_not_nil _ q_not_nil]
    obtain ⟨i,i_lt,hi⟩ :=lsGOM d'_mem
    simp only [length_darts] at i_lt
    have hi_darts:i < q.darts.length:=by simpa using i_lt
    rw [← hi,q.darts_getElem_eq_getVert i hi_darts] at hd'₂
    rw [← hi,q.darts_getElem_eq_getVert i hi_darts] at hd'₁
    change q.getVert i =w' at hd'₁
    change q.getVert (i+1) = w at hd'₂
    have i_nz:i ≠ 0:=by
      rintro rfl
      have huw':u=w':=by simpa using hd'₁
      exact G.loopless.irrefl _ (huw' ▸ hw'.symm)
    have i_min_1:i-1 < q'.darts.length:=by
      have q'_length:q'.length=q.length-1:=by
        simp [transfer_transfer,length_copy,length_transfer,q']
      simp [q'_length]
      omega
    have hd''₁: (q'.darts[i-1]).fst=w':=by
      rw [q'.darts_getElem_eq_getVert (i-1) i_min_1]
      change q'.getVert (i-1) = w'
      rw [show q'.getVert (i-1) = q.tail.getVert (i-1) by
        simp only [Walk.getVert_eq_getD_support,support_copy,support_transfer,q']]
      rw [q.getVert_tail,show i -1+1=i by omega,hd'₁]
    have hd''₂: (q'.darts[i-1]).snd=w:=by
      rw [q'.darts_getElem_eq_getVert (i-1) i_min_1]
      change q'.getVert (i-1+1) = w
      rw [show q'.getVert (i-1+1) = q.tail.getVert (i-1+1) by
        simp only [Walk.getVert_eq_getD_support,support_copy,support_transfer,q']]
      rw [q.getVert_tail,show i -1+1+1=i+1 by omega,hd'₂]
    have w'_ne_u:w' ≠ u:=fun eq ↦ by simp [eq] at hw'
    have Hamiltonian:=
      zi hV perm_q' w'_ne_u hw' hw q'.darts[i-1]
      (lsGM i_min_1) hd''₁ hd''₂
    exact nonHamiltonian Hamiltonian
private theorem yt {n} (hG: ¬IsHamiltonian G) :
    ¬IsHamiltonian (qg^[n] G) :=by
  classical
  induction n with
  | zero=> simpa
  | succ m ih=>
    rw [add_comm]
    contrapose ih
    simp only [iterate_add_apply,iterate_one] at ih ⊢
    exact yp ih
theorem sI:IsHamiltonian (qE G) ↔ IsHamiltonian G :=by
  classical
  apply Iff.intro <;> intro hG
  · unfold qE Erdos556.Function.v3 at hG
    contrapose hG
    exact yt hG
  · exact IsHamiltonian.mono (rs _) hG
private theorem wg (hV:3 ≤ ftCard V) :
    (⊤ : SimpleGraph V).IsHamiltonian:=by
  classical
  obtain ⟨r,hr⟩ : ∃ r,ftCard V =r+3:=
    ⟨ftCard V -3,by omega⟩
  let e :Fin (r+3) ≃ V:=by
    simpa [hr] using (Fintype.equivFin V).symm
  let f :cycleGraph (r+3) →g (⊤ : SimpleGraph V) :=
    ⟨fun x ↦ e x,fun {a b} hab ↦ by
      simp only [top_adj,ne_eq]
      exact e.injective.ne hab.ne⟩
  let p := (cycleGraph.cycle r).map f
  intro _
  refine ⟨f 0,p,?_⟩
  rw [Walk.isHamiltonianCycle_iff_isCycle_and_length_eq]
  refine ⟨?_,?_⟩
  · exact cycleGraph.isCycle_cycle.map e.injective
  · simp [p,hr]
theorem x3 [DecidableRel G.Adj] (hV: (ftCard V) ≥ 3)
    (hG: ∀ u,2*G.degree u ≥ (ftCard V)) : G.IsHamiltonian:=by
  classical
  suffices G.qE= (⊤ : SimpleGraph V) from
    sI.mp (this ▸ wg hV)
  rw [eq_top_iff]
  intro u v ne
  simp only [top_adj,ne_eq] at ne
  apply rK G ne
  calc
    (ftCard V) ≤ G.degree u +G.degree v :=by
      have:=hG u
      have:=hG v
      omega
    _ ≤ G.qE.degree u +G.qE.degree v :=
      add_le_add (G.degree_le_of_le (v:=u) (rs G))
        (G.degree_le_of_le (v:=v) (rs G))
end SimpleGraph
end d0
namespace Erdos556
open SimpleGraph
theorem wH {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] {u v :V} (p:G.Walk u v) (hp:p.IsHamiltonian)
    (hcard:3 ≤ ftCard V) (hdeg:ftCard V ≤ G.degree u +G.degree v) :
    G.IsHamiltonian:=by
  classical
  have hlen:=hp.length_eq
  have hlen₂:2 ≤ p.length:=by omega
  have hne:u ≠ v:=by
    intro h
    have heq:p.getVert 0 =p.getVert p.length:=by simpa using h
    have hi:0=p.length:=hp.isPath.getVert_injOn (by simp) (by simp) heq
    omega
  have hcl:=G.rs
  have hcladj:G.qE.Adj u v:=G.rK hne
    (hdeg.trans (Nat.add_le_add (G.degree_le_of_le (v:=u) hcl)
      (G.degree_le_of_le (v:=v) hcl)))
  have hsub: ∀ e ∈ p.edges,e ∈ G.qE.edgeSet:=
    fun _ he ↦ edgeSet_mono hcl (p.edges_subset_edgeSet he)
  let p':=p.transfer G.qE hsub
  have hp':p'.IsHamiltonian:=by
    apply (hp.isPath.transfer hsub).isHamiltonian_of_mem
    intro x
    rw [Walk.support_transfer]
    exact hp.mem_support x
  let q :=wkCons hcladj.symm p'
  have hq:q.IsCycle:=by
    apply (Walk.cons_isCycle_iff p' hcladj.symm).mpr
    refine ⟨hp'.isPath,?_⟩
    intro he
    have h :=hp'.isPath.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ he)
    have hp'len:p'.length=p.length:=Walk.length_transfer p hsub
    omega
  have hqham:q.IsHamiltonianCycle:=by
    apply Walk.isHamiltonianCycle_iff_isCycle_and_length_eq.mpr
    refine ⟨hq,?_⟩
    dsimp only [q,p']
    rw [wkLC2,Walk.length_transfer]
    omega
  exact (SimpleGraph.sI (G:=G)).mp (fun _ ↦ ⟨v,q,hqham⟩)
theorem s7 {V:Type*} [Fintype V]
    [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] {u v :V} (p:G.Walk u v) (hp:p.IsPath)
    (hlen:2 ≤ p.length)
    (hdeg:p.length+1 ≤
      (G.induce {x | x ∈ p.support}).degree ⟨u,p.start_mem_support⟩ +
      (G.induce {x | x ∈ p.support}).degree ⟨v,p.end_mem_support⟩) :
    cycleGraph (p.length+1) ⊑ G.induce {x | x ∈ p.support} :=by
  classical
  let S :Set V := {x | x ∈ p.support}
  let p':=p.induce S (fun _ hx ↦ hx)
  have hp':p'.IsPath:=by
    apply (Walk.isPath_map_iff_of_injective (f:= (Embedding.induce (G:=G) S).toHom)
      (p:=p') (Embedding.induce (G:=G) S).injective).mp
    rw [Walk.map_induce]
    exact hp
  have hham:p'.IsHamiltonian:=by
    apply hp'.isHamiltonian_of_mem
    intro x
    rw [Walk.support_induce]
    simpa only [List.mem_attachWith] using (show x.val ∈ p.support from x.property)
  have hcard:ftCard S =p.length+1:=by
    have hS:S= (p.support.toFinset:Set V) :=by ext x;simp [S]
    calc
      ftCard S =S.ncard:=natCEFC.symm
      _=p.support.toFinset.card:=by rw [hS,stNCF]
      _=p.length+1:=by
        rw [lsTCON hp.support_nodup,wkLS]
  have hG:=wH (G.induce S) p' hham
    (by rw [hcard];omega) (by rw [hcard];exact hdeg)
  obtain ⟨z,q,hq⟩ :=hG (by rw [hcard];omega)
  have hc:cycleGraph (p.length+1) ⊑ G.induce S :=
    (cycleGraph_isContained_iff (by omega)).mpr
      ⟨z,q,hq.isCycle,hq.length_eq.trans hcard⟩
  exact hc
theorem uz {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] {u v :V} (p:G.Walk u v) (hp:p.IsPath)
    (hlen:2 ≤ p.length)
    (hdeg:p.length+1 ≤
      (G.induce {x | x ∈ p.support}).degree ⟨u,p.start_mem_support⟩ +
      (G.induce {x | x ∈ p.support}).degree ⟨v,p.end_mem_support⟩) :
    cycleGraph (p.length+1) ⊑ G:=
  (s7 G p hp hlen hdeg).trans
    (Embedding.induce {x | x ∈ p.support}).isContained
theorem vK {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) (hconn:G.Connected) {v:V} (q:G.Walk v v) (hq:q.IsCycle)
    (hmax: ∀ {a b :V} (p:G.Walk a b),p.IsPath → p.length < q.length) :
    G.IsHamiltonian:=by
  classical
  have hall: ∀ x,x ∈ q.support:=by
    intro x
    by_contra hx
    obtain ⟨p⟩ :=hconn.preconnected v x
    obtain ⟨d,_,hd,hdout⟩ :=p.exists_boundary_dart {z | z ∈ q.support}
      q.start_mem_support hx
    let r :=q.rotate d.fst hd
    have hr:r.IsCycle:=hq.rotate hd
    have houts:d.snd ∉ r.tail.support:=by
      intro hmem
      have hmem':d.snd ∈ r.support:=by
        rw [← Walk.cons_support_tail hr.not_nil]
        exact lsMCOM _ hmem
      exact hdout ((q.mem_support_rotate_iff d.fst hd).mp hmem')
    have hp':=hr.isPath_tail.concat houts d.adj
    have hlt:=hmax _ hp'
    have heq: (r.tail.concat d.adj).length=q.length:=by
      rw [wkLC,wkLT,Walk.length_rotate]
      exact natSAC (by have:=hq.three_le_length;omega)
    rw [heq] at hlt
    exact hlt.false
  refine fun _ ↦ ⟨v,q,⟨hq,?_⟩⟩
  apply hq.isPath_tail.isHamiltonian_of_mem
  intro x
  have hx:=hall x
  rw [← Walk.cons_tail_support q] at hx
  rcases lsMC.mp hx with rfl | hx
  · exact q.tail.end_mem_support
  · rwa [Walk.support_tail_of_not_nil q hq.not_nil]
lemma sD {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S:Set V) [DecidablePred (· ∈ S)]
    (v:V) (hv:v ∈ S) (hwithin: ∀ w,G.Adj v w → w ∈ S) :
    (G.induce S).degree ⟨v,hv⟩ = G.degree v :=by
  classical
  let e : (G.induce S).neighborSet ⟨v,hv⟩ ≃ G.neighborSet v :=
    { toFun:=fun w ↦ ⟨w.val.val,w.property⟩
      invFun:=fun w ↦ ⟨⟨w.val,hwithin w.val w.property⟩,w.property⟩
      left_inv:=fun _ ↦ rfl
      right_inv:=fun _ ↦ rfl}
  rw [← card_neighborSet_eq_degree,← card_neighborSet_eq_degree]
  exact ftCC2 e
theorem sV {V:Type*}
    [Fintype V] [DecidableEq V] (G:SimpleGraph V) [DecidableRel G.Adj]
    (hconn:G.Connected) {u v :V} (p:G.Walk u v) (hp:p.IsPath)
    (hmax: ∀ {a b :V} (q:G.Walk a b),q.IsPath → q.length ≤ p.length)
    (hlen:2 ≤ p.length) (hdeg:p.length+1 ≤ G.degree u +G.degree v) :
    G.IsHamiltonian:=by
  classical
  have hstart: ∀ w,G.Adj u w → w ∈ p.support:=by
    intro w hw
    by_contra hnot
    have hq: (wkCons hw.symm p).IsPath:= (wkCII _ _).mpr ⟨hp,hnot⟩
    have h :=hmax _ hq
    simp only [wkLC2] at h
    omega
  have hend: ∀ w,G.Adj v w → w ∈ p.support:=by
    intro w hw
    by_contra hnot
    have h :=hmax _ (hp.concat hnot hw)
    simp only [wkLC] at h
    omega
  have hcopy:=uz G p hp hlen (by
    rw [sD G {x | x ∈ p.support} u p.start_mem_support hstart,
      sD G {x | x ∈ p.support} v p.end_mem_support hend]
    exact hdeg)
  obtain ⟨x,q,hq,hqlen⟩ := (cycleGraph_isContained_iff (by omega)).mp hcopy
  apply vK G hconn q hq
  intro a b r hr
  rw [hqlen]
  exact natLSOL (hmax r hr)
end Erdos556
namespace Erdos556
open SimpleGraph
theorem z8 {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (u:V) (hu:2 ≤ G.degree u) :
    ∃ (a b :V) (p:G.Walk a b),p.IsPath ∧ p.length=2:=by
  classical
  have hnb:1 < (G.neighborFinset u).card:=by
    rw [card_neighborFinset_eq_degree]
    omega
  obtain ⟨a,ha,b,hb,hab⟩ :=Finset.one_lt_card.mp hnb
  have hua:G.Adj u a:= (G.mem_neighborFinset u a).mp ha
  have hub:G.Adj u b:= (G.mem_neighborFinset u b).mp hb
  let p :=wkCons hua.symm (wkCons hub Walk.nil)
  refine ⟨a,b,p,?_,rfl⟩
  simp [p,wkCII,hua.ne.symm,hub.ne,hab]
theorem ur {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (hconn:G.Connected)
    (d:ℕ) (hd:2 ≤ d) (hdeg: ∀ v,d ≤ G.degree v) :
    ∃ (u v :V) (p:G.Walk u v),p.IsPath ∧
      min (2*d+1) (ftCard V) ≤ p.length+1:=by
  classical
  have:Nonempty V :=hconn.nonempty
  obtain ⟨u,v,p,hp,hmax⟩ :=Walk.exists_isPath_forall_isPath_length_le_length G
  refine ⟨u,v,p,hp,?_⟩
  by_contra hlong
  have hshort:p.length+1 < min (2*d+1) (ftCard V) :=by omega
  obtain ⟨a,b,q,hq,hqlen⟩ :=z8 G u (hd.trans (hdeg u))
  have hlen:2 ≤ p.length:=by
    have h :=hmax a b q hq
    omega
  have hham:=sV G hconn p hp
    (fun {_ _} q hq=> hmax _ _ q hq) hlen (by
      have hu:=hdeg u
      have hv:=hdeg v
      omega)
  obtain ⟨z,q,hq⟩ :=hham (by omega)
  have h :=hmax _ _ q.tail hq.isCycle.isPath_tail
  rw [wkLT,hq.length_eq] at h
  omega
theorem wk {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj]
    (hmax: ∀ {u v} (p:G.Walk u v),p.IsPath → p.length ≤ 1) (v:V) :
    G.degree v ≤ 1 :=by
  classical
  by_contra h
  obtain ⟨a,b,p,hp,hlen⟩ :=z8 G v (by omega)
  have:=hmax p hp
  omega
theorem vW {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj]
    (hmax: ∀ {u v} (p:G.Walk u v),p.IsPath → p.length ≤ 0) (v:V) :
    G.degree v =0:=by
  classical
  by_contra h
  have hn: (G.neighborFinset v).Nonempty:=by
    rw [← fsCP,card_neighborFinset_eq_degree]
    omega
  obtain ⟨w,hw⟩ :=hn
  have hadj:G.Adj v w:= (G.mem_neighborFinset v w).mp hw
  have hp: (wkCons hadj Walk.nil).IsPath:=by
    simp [wkCII,hadj.ne]
  have:=hmax _ hp
  simp only [wkLC2,Walk.length_nil] at this
  omega
theorem tc {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (C:G.ConnectedComponent)
    [Fintype C] [DecidableRel C.toSimpleGraph.Adj] (v:C) :
    C.toSimpleGraph.degree v =G.degree v.val:=by
  classical
  let e :C.toSimpleGraph.neighborSet v ≃ G.neighborSet v.val:=
    { toFun:=fun w => ⟨w.val.val,w.property⟩
      invFun:=fun w => ⟨⟨w.val,C.mem_supp_of_adj_mem_supp v.property w.property⟩,
        w.property⟩
      left_inv:=fun _ => rfl
      right_inv:=fun _ => rfl}
  rw [← card_neighborSet_eq_degree,← card_neighborSet_eq_degree]
  exact ftCC2 e
theorem wP {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (k:ℕ) (hk:2 ≤ k)
    (hmin: ∀ v,k < 2*G.degree v)
    (hmax: ∀ {u v} (p:G.Walk u v),p.IsPath → p.length ≤ k) (v:V) :
    G.degree v ≤ k :=by
  classical
  let C :=G.connectedComponentMk v
  have hd: ∀ w:C,k/2+1 ≤ C.toSimpleGraph.degree w :=by
    intro w
    rw [tc]
    have h :=hmin w.val
    omega
  obtain ⟨a,b,p,hp,hlen⟩ :=ur C.toSimpleGraph
    C.connected_toSimpleGraph (k/2+1) (by omega) hd
  have hp': (p.map C.toSimpleGraph_hom).IsPath:=
    hp.map (by intro x y h;exact subExt h)
  have hbound:=hmax _ hp'
  rw [wkLM] at hbound
  have hcard:ftCard C ≤ k +1:=by omega
  let v':C:= ⟨v,ConnectedComponent.connectedComponentMk_mem⟩
  have hdeg:=C.toSimpleGraph.degree_lt_card_verts v'
  rw [tc] at hdeg
  exact Nat.le_of_lt_succ (hdeg.trans_le hcard)
theorem vi {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (k:ℕ)
    (hdeg: ∀ v,G.degree v ≤ k) :
    2*G.edgeFinset.card ≤ k*ftCard V :=by
  classical
  calc
    2*G.edgeFinset.card= ∑ v,G.degree v :=G.sum_degrees_eq_twice_card_edges.symm
    _ ≤ ∑ _v:V,k:=fsSLS fun v _=> hdeg v
    _=k*ftCard V :=by simp [natMC]
universe u
private theorem a3 (N:ℕ) :
    ∀ (V:Type u) [Fintype V]
      (G:SimpleGraph V) [DecidableRel G.Adj],ftCard V =N →
      ∀ k :ℕ,
      (∀ {a b :V} (p:G.Walk a b),p.IsPath → p.length ≤ k) →
      2*G.edgeFinset.card ≤ k*ftCard V :=by
  classical
  induction N using natSIO with
  | h N ih=>
      intro V _ G _ hcard k hmax
      classical
      by_cases hsmall:k ≤ 1
      · apply vi G k
        intro v
        rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hsmall with rfl | rfl
        · exact (vW G hmax v).le
        · exact wk G hmax v
      · have hk:2 ≤ k:=by omega
        by_cases hlow: ∃ v,2*G.degree v ≤ k
        · obtain ⟨v,hv⟩ :=hlow
          let S :Set V := {v}ᶜ
          let H :=G.induce S
          have hS:ftCard S =ftCard V -1:=by
            simpa [S] using Set.card_ne_eq v
          have hpos:0 < ftCard V :=ftCPI.mpr ⟨v⟩
          have hlt:ftCard S < N :=by omega
          have hmaxH: ∀ {a b :S} (p:H.Walk a b),p.IsPath → p.length ≤ k:=by
            intro a b p hp
            let f := (Embedding.induce (G:=G) S).toHom
            have hp': (p.map f).IsPath:=hp.map (by
              intro x y h
              exact subExt h)
            simpa only [wkLM] using hmax (p.map f) hp'
          have hrec:=ih (ftCard S) hlt S H rfl k hmaxH
          have hedge:H.edgeFinset.card+G.degree v =G.edgeFinset.card:=by
            dsimp [H,S]
            rw [card_edgeFinset_induce_compl_singleton,
              card_edgeFinset_deleteIncidenceSet]
            exact natSAC (G.degree_le_card_edgeFinset v)
          have hcardadd:ftCard S +1=ftCard V :=by omega
          nlinarith
        · apply vi G k
          apply wP G k hk
          · intro v
            by_contra h
            exact hlow ⟨v,by omega⟩
          · exact hmax
theorem ty {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (k:ℕ)
    (hmax: ∀ {a b :V} (p:G.Walk a b),p.IsPath → p.length ≤ k) :
    2*G.edgeFinset.card ≤ k*ftCard V :=
  a3 (ftCard V) V G rfl k hmax
theorem z6 {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (k:ℕ)
    (he:k*ftCard V < 2 *G.edgeFinset.card) :
    ∃ (a b :V) (p:G.Walk a b),p.IsPath ∧ k < p.length:=by
  classical
  by_contra h
  push Not at h
  have hb:=ty G k (fun p hp=> h _ _ p hp)
  omega
end Erdos556
namespace Erdos556
open Filter
open scoped Topology
theorem y6 {r:ℝ} (hr0:0 ≤ r) (hr1:r < 1) :
    Tendsto (fun n :ℕ=> ((n:ℝ) + 1) ^ 2*r^n) atTop (𝓝 0) :=by
  have h2:=tendsto_pow_const_mul_const_pow_of_lt_one 2 hr0 hr1
  have h1:=tendsto_self_mul_const_pow_of_lt_one hr0 hr1
  have h0:=tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1
  convert (h2.add (h1.const_mul 2)).add h0 using 1
  · ext n
    ring
  · norm_num
theorem ti (K:ℕ) (hK:0 < K) (C:ℝ) (hC:0 ≤ C)
    {r:ℝ} (hr0:0 ≤ r) (hr1:r < 1) :
    Tendsto (fun n :ℕ=> (n:ℝ) ^ 2*C*r^ (n/K)) atTop (𝓝 0) :=by
  have hdiv:Tendsto (fun n :ℕ=> n /K) atTop atTop:=
    Nat.tendsto_div_const_atTop hK.ne'
  have hmajor:Tendsto
      (fun n :ℕ=> ((K:ℝ) ^ 2*C) * (((n/K:ℕ) : ℝ) + 1) ^ 2*r^ (n/K))
      atTop (𝓝 0) :=by
    convert ((y6 hr0 hr1).comp hdiv).const_mul
      ((K:ℝ) ^ 2*C) using 1
    · ext n
      simp only [Function.comp_apply]
      ring
    · simp
  apply squeeze_zero (fun n => by positivity) (fun n => ?_) hmajor
  have hn:n ≤ K* (n/K+1) :=by
    have hmod:=natML n hK
    have hdecomp:=Nat.mod_add_div n K
    nlinarith
  have hnR: (n:ℝ) ≤ (K:ℝ) * (((n/K:ℕ) : ℝ) + 1) :=by
    exact_mod_cast hn
  have hsq: (n:ℝ) ^ 2 ≤ ((K:ℝ) * (((n/K:ℕ) : ℝ) + 1)) ^ 2:=by
    gcongr
  calc
    (n:ℝ) ^ 2*C*r^ (n/K) ≤
        ((K:ℝ) * (((n/K:ℕ) : ℝ) + 1)) ^ 2*C*r^ (n/K) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hsq hC) (pow_nonneg hr0 _)
    _= ((K:ℝ) ^ 2*C) * (((n/K:ℕ) : ℝ) + 1) ^ 2*r^ (n/K) :=by ring
theorem uW (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1)
    (L K a:ℕ) (hK:0 < K) :
    ∀ᶠ n :ℕ in atTop,
      (n:ℝ) ^ 2* (a+1) * (1-q^L) ^ (n/K) < 1/2:=by
  have hr0:0 ≤ 1-q^L:=sub_nonneg.mpr (pow_le_one₀ hq0.le hq1)
  have hr1:1-q^L < 1:=by have:=pow_pos hq0 L;linarith
  have h :=ti K hK ((a:ℝ) + 1) (by positivity) hr0 hr1
  exact h.eventually (gt_mem_nhds (by norm_num: (0:ℝ) < 1/2))
end Erdos556
namespace Erdos556
open SimpleGraph Finset Filter
theorem td {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (b d D m a:ℕ)
    (hconn:q8 G (b+3*D+3))
    (hnonbip:qT G (b+3*D+3))
    (hd:0 < d) (hdeg: ∀ w,d+ (b+3*D+3) ≤ G.degree w)
    (hN:ftCard V ≤ D *d)
    (hbound: ((a+1) * m) * (12*D+3) ≤ b)
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1)
    (hfail: (ftCard V :ℝ) ^ 2* (a+1) *
      (1-q^ (12*D+3)) ^ m < 1/2)
    (hV:0 < ftCard V) :
    ∃ R :Finset V,(R.card:ℝ) ≤ 2*q*ftCard V ∧
      ∀ u v,u ≠ v → ∀ S,S.card ≤ a →
        qZ G (12*D+3) u v (R \ S) :=by
  classical
  let I := {uv:V × V//uv.1 ≠ uv.2}
  let P :I → Finset V → Prop:=fun uv=> qZ G (12*D+3) uv.val.1 uv.val.2
  have hav (uv:I) (S:Finset V) (hS:S.card ≤ b) :
      ∃ T :Finset V,P uv T ∧ T.card ≤ 12*D+3 ∧ Disjoint S T:=
    vz G b d D hconn hnonbip hd hdeg hN
      uv.val.1 uv.val.2 uv.property S hS
  have hI: (ftCard I :ℝ) ≤ (ftCard V :ℝ) ^ 2:=by
    have h :=ftCLOI (fun uv:I=> uv.val) subVI
    rw [ftCP] at h
    rw [pow_two]
    exact_mod_cast h
  have hr:0 ≤ 1-q^ (12*D+3) :=sub_nonneg.mpr (pow_le_one₀ hq0.le hq1)
  have hf: (ftCard I :ℝ) * (a+1) * (1-q^ (12*D+3)) ^ m < 1/2:=by
    apply lt_of_le_of_lt _ hfail
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hI (by positivity)) (pow_nonneg hr _)
  obtain ⟨R,hR,hhit⟩ :=uA P q hq0 hq1 (12*D+3) b m a
    hbound hav hf hV
  refine ⟨R,hR,?_⟩
  intro u v huv S hS
  obtain ⟨T,hTR,hP,_,hST⟩ :=hhit ⟨(u,v),huv⟩ S hS
  apply hP.mono
  intro x hx
  exact mem_sdiff.mpr ⟨hTR hx,fun hxS=> fsDL.mp hST hxS hx⟩
theorem xw (D B a:ℕ) (hB:0 < B)
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (b d :ℕ),
      N₀ ≤ ftCard V → q8 G (b+3*D+3) →
      qT G (b+3*D+3) →
      (∀ w,d+ (b+3*D+3) ≤ G.degree w) → ftCard V ≤ D *d →
      ftCard V ≤ B *b →
      ∃ R :Finset V,(R.card:ℝ) ≤ 2*q*ftCard V ∧
        ∀ u v,u ≠ v → ∀ S,S.card ≤ a →
          qZ G (12*D+3) u v (R \ S) :=by
  let L :=12*D+3
  let K :=B* ((a+1) * L)
  have hL:0 < L:=by dsimp [L];omega
  have hK:0 < K:=Nat.mul_pos hB (Nat.mul_pos (by omega) hL)
  obtain ⟨N₁,hN₁⟩ :=eventually_atTop.mp (uW q hq0 hq1 L K a hK)
  refine ⟨max N₁ 1,?_⟩
  intro V _ _ G _ b d hN hc hnb hg hd hb
  have hV:0 < ftCard V :=by omega
  have hdpos:0 < d:=by nlinarith
  let m :=ftCard V /K
  have hbudget: ((a+1) * m) * L ≤ b:=by
    have hmul:B* (((a+1) * m) * L) ≤ B*b:=by
      calc
        B* (((a+1) * m) * L) = m*K:=by dsimp [K];ring
        _ ≤ ftCard V :=natDMLS _ _
        _ ≤ B*b:=hb
    nlinarith
  exact td G b d D m a hc hnb hdpos hg hd hbudget q hq0 hq1
    (hN₁ _ (by omega)) hV
end Erdos556
namespace Erdos556
open SimpleGraph
theorem wL {V:Type*} {G:SimpleGraph V}
    (R:Finset V) (L k :ℕ) (hk:1 ≤ k)
    (hres: ∀ u v,u ≠ v → qZ G L u v R)
    (hodd: ∀ (w:V) (c:G.Walk w w),c.IsCycle → Odd c.length → c.length ≤ 2*k)
    {u v :V} (p:G.Walk u v) (hp:p.IsPath) (hav: ∀ x ∈ p.support,x ∉ R) :
    p.length ≤ 2*k:=by
  by_contra hlen
  have huv:u ≠ v:=by
    intro h
    have hz:= ((hp.nil_iff_eq).mpr h).length_eq_zero
    omega
  obtain ⟨c,hc,ho,hge,_⟩ :=sZ
    p hp (by omega) L R hav (hres u v huv)
  have hle:=hodd u c hc ho
  omega
theorem xO {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (R:Finset V) (L k :ℕ) (hk:1 ≤ k)
    (hres: ∀ u v,u ≠ v → qZ G L u v R)
    (hodd: ∀ (w:V) (c:G.Walk w w),c.IsCycle → Odd c.length → c.length ≤ 2*k) :
    G.edgeFinset.card ≤ (k+R.card) * ftCard V :=by
  classical
  let U := (R:Set V)ᶜ
  let H :=G.induce U
  let f :H ↪g G :=sgInduce U
  have hpaths {u v :U} (p:H.Walk u v) (hp:p.IsPath) : p.length ≤ 2*k:=by
    have h :=wL R L k hk hres hodd
      (p.map f.toHom) (hp.map f.injective) (by
        intro x hx
        rw [wkSM,lsMM] at hx
        obtain ⟨y,_,hy⟩ :=hx
        subst x
        exact y.property)
    simpa only [wkLM] using h
  have hbound:=ty H (2*k) hpaths
  have hcard:=ftCLOI (fun x :U=> x.val) subVI
  have hretained:H.edgeFinset.card ≤ k*ftCard V :=by
    have hmul:=natMLML k hcard
    nlinarith
  have hdeleted:=rc G R
  change G.edgeFinset.card ≤ H.edgeFinset.card+R.card*ftCard V at hdeleted
  nlinarith
theorem ua (D B :ℕ) (hB:0 < B)
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (b d k:ℕ),
      N₀ ≤ ftCard V → q8 G (b+3*D+3) →
      qT G (b+3*D+3) →
      (∀ w,d+ (b+3*D+3) ≤ G.degree w) → ftCard V ≤ D *d →
      ftCard V ≤ B *b → 1 ≤ k →
      (∀ (w:V) (c:G.Walk w w),c.IsCycle → Odd c.length → c.length ≤ 2*k) →
      (G.edgeFinset.card:ℝ) ≤ (k:ℝ) * ftCard V +
        2*q* (ftCard V :ℝ) ^ 2:=by
  obtain ⟨N₀,hN₀⟩ :=xw D B 0 hB q hq0 hq1
  refine ⟨N₀,?_⟩
  intro V _ _ G _ b d k hN hc hnb hg hd hb hk ho
  obtain ⟨R,hR,hres⟩ :=hN₀ G b d hN hc hnb hg hd hb
  have hres' (u v :V) (huv:u ≠ v) : qZ G (12*D+3) u v R :=by
    simpa only [Finset.sdiff_empty] using hres u v huv ∅ (by simp)
  have he:=xO G R (12*D+3) k hk hres' ho
  have heR: (G.edgeFinset.card:ℝ) ≤ ((k:ℝ) + R.card) * ftCard V :=by
    exact_mod_cast he
  have hm:=mul_le_mul_of_nonneg_right hR (natCN (ftCard V) :
    (0:ℝ) ≤ ftCard V)
  nlinarith
end Erdos556
namespace Erdos556
open SimpleGraph
universe u
variable {V:Type u} [Fintype V] [DecidableEq V]
variable {G:SimpleGraph V}
def qh (G:SimpleGraph V) : Prop:=
  3 ≤ ftCard V ∧ G.Connected ∧
    ∀ v :V,(G.induce ({v}ᶜ:Set V)).Connected
namespace qh
omit [DecidableEq V] in
theorem xV (hG:qh G) : 3 ≤ ftCard V :=hG.1
omit [DecidableEq V] in
theorem connected (hG:qh G) : G.Connected:=hG.2.1
omit [DecidableEq V] in
theorem t9 (hG:qh G) (v:V) :
    (G.induce ({v}ᶜ:Set V)).Connected:=
  hG.2.2 v
omit [DecidableEq V] in
theorem nontrivial (hG:qh G) : Nontrivial V :=by
  classical
  exact ftOLCIN.mp (by
    have h :=hG.xV
    omega)
omit [DecidableEq V] in
theorem exists_ne (hG:qh G) (v:V) : ∃ w :V,w ≠ v:=by
  classical
  let:=hG.nontrivial
  exact _root_.exists_ne v
omit [DecidableEq V] in
theorem dU (hG:qh G) (v:V) :
    ∃ x y:V,x ≠ v ∧ y ≠ v ∧ x ≠ y:=by
  classical
  have hcard:2 ≤ ftCard ({v}ᶜ:Set V) :=by
    rw [Fintype.card_compl_set,Set.card_singleton]
    have h :=hG.xV
    omega
  let:Nontrivial ({v}ᶜ:Set V) :=
    ftOLCIN.mp (by omega)
  obtain ⟨x,y,hxy⟩ :=exists_pair_ne ({v}ᶜ:Set V)
  have hx: (x:V) ≠ v:=by
    simpa only [stMCI,stMSI] using x.2
  have hy: (y:V) ≠ v:=by
    simpa only [stMCI,stMSI] using y.2
  exact ⟨x,y,hx,hy,fun h ↦ hxy (subExt h)⟩
omit [DecidableEq V] in
theorem sT (hG:qh G) (z:V) {x y :V}
    (hx:x ≠ z) (hy:y ≠ z) :
    ∃ p :G.Walk x y,p.IsPath ∧ z ∉ p.support:=by
  classical
  let x': ({z}ᶜ:Set V) := ⟨x,hx⟩
  let y': ({z}ᶜ:Set V) := ⟨y,hy⟩
  obtain ⟨p,hp⟩ := (hG.t9 z).exists_isPath x' y'
  let e :G.induce ({z}ᶜ:Set V) ↪g G :=
    sgInduce ({z}ᶜ:Set V)
  let q :=p.map e.toHom
  have hqpath:q.IsPath:=hp.map e.injective
  have hqavoid:z ∉ q.support:=by
    intro hz
    have hsupport:q.support=p.support.map e :=by
      exact SimpleGraph.Walk.support_map e.toHom p
    rw [hsupport,lsMM] at hz
    obtain ⟨w,hw,hwz⟩ :=hz
    have hwne: (w:V) ≠ z:=by
      simpa only [stMCI,stMSI] using w.2
    exact hwne hwz
  have hex:e x'=x:=by rfl
  have hey:e y'=y:=by rfl
  let q':G.Walk x y:=q.copy hex hey
  have hq'path:q'.IsPath:=
    (SimpleGraph.Walk.isPath_copy q hex hey).2 hqpath
  have hq'avoid:z ∉ q'.support:=by
    simpa only [q',SimpleGraph.Walk.support_copy] using hqavoid
  exact ⟨q',hq'path,hq'avoid⟩
end qh
structure te (G:SimpleGraph V) (A B :Set V) where
  a₁:V
  a₂:V
  b₁:V
  b₂:V
  p:G.Walk a₁ b₁
  q:G.Walk a₂ b₂
  p_isPath:p.IsPath
  q_isPath:q.IsPath
  a₁_mem:a₁ ∈ A
  a₂_mem:a₂ ∈ A
  b₁_mem:b₁ ∈ B
  b₂_mem:b₂ ∈ B
  disjoint_support:p.support.Disjoint q.support
  p_interior: ∀ x ∈ p.support.tail.dropLast,x ∉ A ∪ B
  q_interior: ∀ x ∈ q.support.tail.dropLast,x ∉ A ∪ B
namespace te
variable {A B :Set V}
end te
end Erdos556
namespace Erdos556
open SimpleGraph
theorem qh.iso {V W :Type*} [Fintype V] [Fintype W]
    {G:SimpleGraph V} {H:SimpleGraph W}
    (hG:qh G) (e:G ≃g H) : qh H :=by
  classical
  refine ⟨?_,hG.connected.map e.toHom e.surjective,?_⟩
  · rw [← ftCC2 e.toEquiv]
    exact hG.xV
  · intro w
    have hbij:Set.BijOn e ({e.symm w}ᶜ:Set V) ({w}ᶜ:Set W) :=by
      refine ⟨?_,e.injective.injOn,?_⟩
      · intro x hx
        change e x ≠ w
        intro heq
        apply hx
        exact e.injective (heq.trans (e.apply_symm_apply w).symm)
      · intro y hy
        refine ⟨e.symm y,?_,e.apply_symm_apply y⟩
        intro h
        exact hy (e.symm.injective h)
    let f :=e.induce hbij
    exact (hG.t9 (e.symm w)).map f.toHom f.surjective
end Erdos556
section dx
/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
namespace Erdos556
open SimpleGraph
universe u
variable {V:Type u} [Fintype V] [DecidableEq V]
variable {G:SimpleGraph V}
variable {A B S:Set V}
namespace te
end te
namespace qh
end qh
structure x7 (G:SimpleGraph V) (A B :Set V) where
  a₁:V
  a₂:V
  b₁:V
  b₂:V
  p:G.Walk a₁ b₁
  q:G.Walk a₂ b₂
  p_isPath:p.IsPath
  q_isPath:q.IsPath
  a₁_mem:a₁ ∈ A
  a₂_mem:a₂ ∈ A
  b₁_mem:b₁ ∈ B
  b₂_mem:b₂ ∈ B
  disjoint_support:p.support.Disjoint q.support
namespace x7
structure ee {a b :V} (p:G.Walk a b) (A B :Set V) where
  left:V
  right:V
  walk:G.Walk left right
  isPath:walk.IsPath
  left_mem:left ∈ A
  right_mem:right ∈ B
  support_subset:walk.support ⊆ p.support
  interior: ∀ x ∈ walk.support.tail.dropLast,x ∉ A ∪ B
end x7
namespace qh
end qh
end Erdos556
end dx
section cI
/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
The definitions `IsArm`, `ArmsDisj`, and the indexed-arc proof below are
adapted from `ListColoring.RubinCases` at commit
80a728c86f28222a58b11a777f9d22419fd2fb69 of
https://github.com/rkirov/list-color-function, released under Apache 2.0.
-/
namespace Erdos556
open SimpleGraph
variable {V:Type*} {G:SimpleGraph V}
theorem yg {v:V} {c:G.Walk v v} (hc:c.IsCycle)
    {a b :V} (ha:a ∈ c.support) (hb:b ∈ c.support) (hab:a ≠ b) :
    ∃ (p q :G.Walk a b),p.IsPath ∧ q.IsPath ∧
      1 ≤ p.length ∧ 1 ≤ q.length ∧ p.length+q.length=c.length ∧
      (∀ x ∈ p.support,x ∈ q.support → x=a ∨ x=b) ∧
      (∀ x,x ∈ c.support ↔ x ∈ p.support ∨ x ∈ q.support) ∧
      (∀ e,e ∈ p.edges → e ∈ c.edges) ∧
      (∀ e,e ∈ q.edges → e ∈ c.edges) :=by
  classical
  let c':G.Walk a a:=c.rotate a ha
  have hc':c'.IsCycle:= (SimpleGraph.Walk.isCycle_rotate ha).mpr hc
  have hb':b ∈ c'.support:=
    (sgMSRI c a ha).mpr hb
  let p :G.Walk a b:=c'.takeUntil b hb'
  let r :G.Walk b a:=c'.dropUntil b hb'
  let q :G.Walk a b:=r.reverse
  have hdecomp:p.append r =c':=by
    exact c'.take_spec hb'
  have hpPath:p.IsPath:=hc'.isPath_takeUntil hb'
  have happCycle: (p.append r).IsCycle:=by
    rw [hdecomp]
    exact hc'
  have hrPath:r.IsPath:=by
    exact happCycle.isPath_of_append_right (sgNNON hab)
  have hqPath:q.IsPath:=hrPath.reverse
  have hpPos:1 ≤ p.length:=by
    have:0 < p.length:=sgNNILL.mp
      (sgNNON hab)
    omega
  have hqPos:1 ≤ q.length:=by
    have:0 < r.length:=sgNNILL.mp
      (sgNNON hab.symm)
    have:1 ≤ r.length:=by omega
    simpa [q] using this
  have hlen:p.length+q.length=c.length:=by
    have:=congrArg SimpleGraph.Walk.length hdecomp
    simpa [q,c',SimpleGraph.Walk.length_rotate] using this
  have htailNodup: (p.support.tail++r.support.tail).Nodup:=by
    rw [← SimpleGraph.Walk.tail_support_append]
    rw [hdecomp]
    exact hc'.support_nodup
  have hmeet: ∀ x ∈ p.support,x ∈ q.support → x=a ∨ x=b:=by
    intro x hxp hxq
    by_contra h
    push Not at h
    have hxpt:x ∈ p.support.tail:=
      (sgMSI p).mp hxp |>.resolve_left h.1
    have hxr:x ∈ r.support:=by
      simpa [q,sgSR] using hxq
    have hxrt:x ∈ r.support.tail:=
      (sgMSI r).mp hxr |>.resolve_left h.2
    exact (List.disjoint_of_nodup_append htailNodup hxpt hxrt)
  have hsupp: ∀ x,x ∈ c.support ↔ x ∈ p.support ∨ x ∈ q.support:=by
    intro x
    rw [← sgMSRI c a ha]
    change x ∈ c'.support ↔ x ∈ p.support ∨ x ∈ q.support
    rw [← hdecomp,SimpleGraph.Walk.mem_support_append_iff]
    simp only [q,sgSR,lsMR]
  have hedg: ∀ e:Sym2 V,e ∈ c'.edges ↔ e ∈ c.edges:=fun _ ↦
    (SimpleGraph.Walk.rotate_edges c a ha).mem_iff
  have hpEdges: ∀ e,e ∈ p.edges → e ∈ c.edges:=by
    intro e he
    apply (hedg e).mp
    exact SimpleGraph.Walk.edges_takeUntil_subset_edges c' hb' he
  have hqEdges: ∀ e,e ∈ q.edges → e ∈ c.edges:=by
    intro e he
    apply (hedg e).mp
    apply SimpleGraph.Walk.edges_dropUntil_subset_edges c' hb'
    simpa [q,SimpleGraph.Walk.edges_reverse] using he
  exact ⟨p,q,hpPath,hqPath,hpPos,hqPos,hlen,hmeet,hsupp,hpEdges,hqEdges⟩
end Erdos556
end cI
section cL
/-
Copyright 2026 The Lean-Proofs Authors.
Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at
    http://www.apache.org/licenses/LICENSE-2.0
Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
namespace Erdos556
open SimpleGraph
universe u
variable {V:Type u} [Fintype V] [DecidableEq V]
variable {G:SimpleGraph V}
def rg (G:SimpleGraph V) (x y :V) : Prop:=
  ∃ (z:V) (c:G.Walk z z),c.IsCycle ∧ x ∈ c.support ∧ y ∈ c.support
abbrev sg (V:Type u) :=Sum V Bool
def qA (G:SimpleGraph V) (A B :Set V) :
    SimpleGraph (sg V) where
  Adj s t:=
    match s,t with
    | Sum.inl x,Sum.inl y => G.Adj x y
    | Sum.inl x,Sum.inr false=> x ∈ A
    | Sum.inr false,Sum.inl x => x ∈ A
    | Sum.inl x,Sum.inr true=> x ∈ B
    | Sum.inr true,Sum.inl x => x ∈ B
    | Sum.inr _,Sum.inr _ => False
  symm:= ⟨by
    intro s t h
    cases s with
    | inl x =>
        cases t with
        | inl y => exact h.symm
        | inr i => cases i <;> exact h
    | inr i =>
        cases t with
        | inl x => cases i <;> exact h
        | inr k =>
            cases i <;> cases k <;> exact False.elim h⟩
  loopless:= ⟨by
    intro s h
    cases s with
    | inl x => exact h.ne rfl
    | inr i => cases i <;> exact False.elim h⟩
omit [DecidableEq V] [Fintype V] in
@[simp] theorem e3 {A B :Set V} {x y :V} :
    (qA G A B).Adj (Sum.inl x) (Sum.inl y) ↔ G.Adj x y:=
  Iff.rfl
omit [DecidableEq V] [Fintype V] in
@[simp] theorem dY {A B :Set V} {x:V} :
    (qA G A B).Adj (Sum.inl x) (Sum.inr false) ↔ x ∈ A:=
  Iff.rfl
omit [DecidableEq V] [Fintype V] in
@[simp] theorem u2 {A B :Set V} {x:V} :
    (qA G A B).Adj (Sum.inr false) (Sum.inl x) ↔ x ∈ A:=
  Iff.rfl
omit [DecidableEq V] [Fintype V] in
@[simp] theorem dM {A B :Set V} {x:V} :
    (qA G A B).Adj (Sum.inl x) (Sum.inr true) ↔ x ∈ B:=
  Iff.rfl
omit [DecidableEq V] [Fintype V] in
@[simp] theorem sJ {A B :Set V} {x:V} :
    (qA G A B).Adj (Sum.inr true) (Sum.inl x) ↔ x ∈ B:=
  Iff.rfl
def qn (G:SimpleGraph V) (A B :Set V) :
    G ↪g qA G A B where
  toFun:=Sum.inl
  inj':=Sum.inl_injective
  map_rel_iff':=Iff.rfl
namespace qh
omit [DecidableEq V] in
theorem vX (hG:qh G) {x y :V}
    (hxy:G.Adj x y) :
    ∃ c :G.Walk x x,c.IsCycle ∧ y ∈ c.support:=by
  classical
  obtain ⟨r,s,hry,hsy,hrs⟩ :=hG.dU y
  let t :V:=if r =x then s else r
  have hty:t ≠ y:=by
    dsimp [t]
    split <;> assumption
  have htx:t ≠ x:=by
    dsimp [t]
    split_ifs with hrx
    · exact fun hsx ↦ hrs (hrx.trans hsx.symm)
    · exact hrx
  obtain ⟨p,hp,hpy⟩ :=hG.sT y hxy.ne hty
  have hp_nonNil: ¬ p.Nil:=by
    exact wkNNON htx.symm
  let w :V:=p.snd
  have hxw:G.Adj x w:=p.adj_snd hp_nonNil
  have hwy:w ≠ y:=by
    intro h
    exact hpy (h ▸ lsMOMT (p.snd_mem_tail_support hp_nonNil))
  obtain ⟨q₀,hq₀,hq₀x⟩ :=
    hG.sT x hxy.ne.symm hxw.ne.symm
  let q :G.Walk y x:=q₀.concat hxw.symm
  have hq:q.IsPath:=hq₀.concat hq₀x hxw.symm
  have hedge:s(x,y) ∉ q.edges:=by
    intro he
    have he':s(y,x) ∈ q.edges:=by simpa [Sym2.eq_swap] using he
    have hlen:q.length=1:=hq.length_eq_one_of_mem_edges he'
    have hq₀len:q₀.length=0:=by
      have:q.length=q₀.length+1:=by simp [q]
      omega
    exact hwy (q₀.eq_of_length_eq_zero hq₀len).symm
  let c :G.Walk x x:=wkCons hxy q
  have hc:c.IsCycle:= (Walk.cons_isCycle_iff q hxy).2 ⟨hq,hedge⟩
  refine ⟨c,hc,?_⟩
  simp [c]
omit [DecidableEq V] [Fintype V] in
private theorem yM
    {z:V} {c:G.Walk z z} (hc:c.IsCycle)
    {x w t:V} (hx:x ∈ c.support) (hw:w ∈ c.support)
    (ht:t ∈ c.support) (hxw:x ≠ w) :
    ∃ r :G.Walk x w,
      r.IsPath ∧ t ∈ r.support ∧ (∀ v ∈ r.support,v ∈ c.support) :=by
  classical
  let c':G.Walk x x:=c.rotate x hx
  have hc':c'.IsCycle:=hc.rotate hx
  have hw':w ∈ c'.support:=by
    simpa [c'] using (c.mem_support_rotate_iff x hx).2 hw
  have ht':t ∈ c'.support:=by
    simpa [c'] using (c.mem_support_rotate_iff x hx).2 ht
  let r₁:G.Walk x w:=c'.takeUntil w hw'
  let d :G.Walk w x:=c'.dropUntil w hw'
  let r₂:G.Walk x w:=d.reverse
  have hr₁:r₁.IsPath:=hc'.isPath_takeUntil hw'
  have hr₂:r₂.IsPath:=by
    apply Walk.isPath_reverse_iff d |>.mpr
    have hcycleappend: (r₁.append d).IsCycle:=by
      simpa [r₁,d] using hc'
    exact Walk.IsCycle.isPath_of_append_right (wkNNON hxw) hcycleappend
  have hr₁_sub: ∀ v ∈ r₁.support,v ∈ c.support:=by
    intro v hv
    have hv':v ∈ c'.support:=c'.support_takeUntil_subset_support hw' hv
    exact (c.mem_support_rotate_iff x hx).1 (by simpa [c'] using hv')
  have hr₂_sub: ∀ v ∈ r₂.support,v ∈ c.support:=by
    intro v hv
    have hvd:v ∈ d.support:=by simpa [r₂] using hv
    have hv':v ∈ c'.support:=c'.support_dropUntil_subset_support hw' hvd
    exact (c.mem_support_rotate_iff x hx).1 (by simpa [c'] using hv')
  by_cases htr₁:t ∈ r₁.support
  · exact ⟨r₁,hr₁,htr₁,hr₁_sub⟩
  · refine ⟨r₂,hr₂,?_,hr₂_sub⟩
    have htappend:t ∈ (r₁.append d).support:=by
      simpa [r₁,d,Walk.take_spec c' hw'] using ht'
    rw [wkMSAI] at htappend
    have htd:t ∈ d.support:=htappend.resolve_left htr₁
    simpa [r₂] using htd
omit [DecidableEq V] [Fintype V] in
private theorem vT
    {root x y:V} (hxy:G.Adj x y) (hcycle:rg G root x)
    (p:G.Walk y root) (hp:p.IsPath) (hpx:x ∉ p.support) :
    rg G root y :=by
  classical
  rcases hcycle with ⟨z,c,hc,hroot,hx⟩
  by_cases hyc:y ∈ c.support
  · exact ⟨z,c,hc,hroot,hyc⟩
  let Cset:Finset V :=c.support.toFinset
  have hmeet: {v ∈ Cset | v ∈ p.support}.Nonempty:=by
    refine ⟨root,?_⟩
    simp [Cset,hroot]
  obtain ⟨w,hwC,hwp,hfirst⟩ :=
    p.exists_mem_support_forall_mem_support_imp_eq Cset hmeet
  have hwc:w ∈ c.support:=by simpa [Cset] using hwC
  have hxw:x ≠ w:=by
    intro h
    exact hpx (h ▸ hwp)
  let q :G.Walk y w:=p.takeUntil w hwp
  have hq:q.IsPath:=hp.takeUntil hwp
  obtain ⟨r,hr,hrootr,hrsub⟩ :=
    yM hc hx hwc hroot hxw
  let body:G.Walk x y:=r.append q.reverse
  have hdisj:r.support.Disjoint q.reverse.support.tail:=by
    rw [lsDL]
    intro v hvr hvqtail
    have hvc:v ∈ c.support:=hrsub v hvr
    have hvq:v ∈ q.support:=by
      have:v ∈ q.reverse.support:=lsMOMT hvqtail
      simpa using this
    have hvw:v=w:=hfirst v (by simpa [Cset] using hvc) hvq
    subst v
    have hne:=hq.reverse.support_nodup.rel_head_tail hvqtail
    exact hne (by simp)
  have hbody:body.IsPath:=by
    simp only [Walk.isPath_def,body,Walk.support_append]
    exact List.Nodup.append hr.support_nodup hq.reverse.support_nodup.tail hdisj
  have hedge:s(y,x) ∉ body.edges:=by
    intro he
    simp only [body,Walk.edges_append,lsMA] at he
    rcases he with her | heq
    · have hyv:y ∈ r.support:=r.fst_mem_support_of_mem_edges her
      exact hyc (hrsub y hyv)
    · have hex:s(x,y) ∈ q.edges:=by
        simpa [Walk.edges_reverse,Sym2.eq_swap] using heq
      have hxp:x ∈ p.support:=by
        exact p.support_takeUntil_subset_support hwp
          (q.fst_mem_support_of_mem_edges hex)
      exact hpx hxp
  let d :G.Walk y y:=wkCons hxy.symm body
  have hd:d.IsCycle:= (Walk.cons_isCycle_iff body hxy.symm).2 ⟨hbody,hedge⟩
  refine ⟨y,d,hd,?_,?_⟩
  · have:root ∈ body.support:=by
      simp only [body,wkMSAI]
      exact orInl hrootr
    simp only [d,wkSC2,lsMC]
    exact orInr this
  · simp [d]
omit [DecidableEq V] in
private theorem tV
    (hG:qh G) {root x y:V} (hrx:root ≠ x)
    (hxy:G.Adj x y) (hcycle:rg G root x) :
    rg G root y :=by
  classical
  obtain ⟨p,hp,hpx⟩ :=hG.sT x hxy.ne.symm hrx
  exact vT hxy hcycle p hp hpx
omit [DecidableEq V] in
private theorem ye
    (hG:qh G) {root x :V} :
    ∀ (l:List V),List.IsChain G.Adj (x::l) →
      root ∉ x::l → rg G root x →
      ∀ y ∈ x ::l,rg G root y :=by
  classical
  intro l
  induction l generalizing x with
  | nil=>
      intro _ _ hcycle y hy
      simp only [lsMS] at hy
      simpa [hy] using hcycle
  | cons v l ih=>
      intro hchain hroot hcycle y hy
      have hc:=List.isChain_cons_cons.mp hchain
      have hrel:G.Adj x v:=hc.1
      have htailchain:List.IsChain G.Adj (v::l) :=hc.2
      have hrootx:root ≠ x:=by
        intro h
        exact hroot (by simp [h])
      have hroottail:root ∉ v::l:=by
        intro h
        exact hroot (lsMCOM x h)
      have hnext:rg G root v :=
        tV hG hrootx hrel hcycle
      simp only [lsMC] at hy
      rcases hy with rfl | hy
      · exact hcycle
      · exact ih htailchain hroottail hnext y (by simpa only [lsMC] using hy)
omit [DecidableEq V] in
private theorem yI
    (hG:qh G) {root x y:V}
    (p:G.Walk x y) (_hp:p.IsPath) (hroot:root ∉ p.support)
    (hcycle:rg G root x) :
    rg G root y :=by
  classical
  exact ye hG p.support.tail
    (by rw [p.cons_tail_support];exact p.isChain_adj_support)
    (by rw [p.cons_tail_support];exact hroot) hcycle y
    (by rw [p.cons_tail_support];exact p.end_mem_support)
omit [DecidableEq V] in
theorem ar (hG:qh G) (x:V) :
    rg G x x :=by
  classical
  obtain ⟨t,htx⟩ :=hG.exists_ne x
  obtain ⟨p,hp⟩ :=hG.connected.exists_isPath x t
  have hp_nonNil: ¬ p.Nil:=wkNNON htx.symm
  have hxsnd:G.Adj x p.snd:=p.adj_snd hp_nonNil
  obtain ⟨c,hc,-⟩ :=hG.vX hxsnd
  exact ⟨x,c,hc,c.start_mem_support,c.start_mem_support⟩
omit [DecidableEq V] in
theorem dS (hG:qh G) (x y :V) :
    rg G x y :=by
  classical
  by_cases hxy:x=y
  · subst y
    exact hG.ar x
  obtain ⟨p,hp⟩ :=hG.connected.exists_isPath x y
  cases p with
  | nil=> exact (hxy rfl).elim
  | @cons x v y h p =>
      have hp':p.IsPath:=hp.of_cons
      have hxnot:x ∉ p.support:= (wkCII h p).1 hp |>.2
      obtain ⟨c,hc,hv⟩ :=hG.vX h
      have hbase:rg G x v :=
        ⟨x,c,hc,c.start_mem_support,hv⟩
      exact yI hG p hp' hxnot hbase
private theorem tB
    {W:Type*} {H:SimpleGraph W} (r:W)
    (h: ∀ w:W,Nonempty (H.Walk w r)) : H.Connected:=by
  refine { preconnected:= ?_,nonempty:= ⟨r⟩}
  intro u v
  obtain ⟨p⟩ :=h u
  obtain ⟨q⟩ :=h v
  exact ⟨p.append q.reverse⟩
private theorem r0
    {W:Type*} {H:SimpleGraph W} (z r :W) (hr:r ≠ z)
    (h: ∀ w:W,w ≠ z →
      ∃ p :H.Walk w r,z ∉ p.support) :
    (H.induce ({z}ᶜ:Set W)).Connected:=by
  classical
  let r': ({z}ᶜ:Set W) := ⟨r,by simpa using hr⟩
  refine { preconnected:= ?_,nonempty:= ⟨r'⟩}
  intro u v
  have hu': (u:W) ∉ ({z} : Set W) :=u.2
  have hv': (v:W) ∉ ({z} : Set W) :=v.2
  have hu: (u:W) ≠ z:=fun huz ↦ hu' (by simpa using huz)
  have hv: (v:W) ≠ z:=fun hvz ↦ hv' (by simpa using hvz)
  obtain ⟨p,hp⟩ :=h u hu
  obtain ⟨q,hq⟩ :=h v hv
  let w :H.Walk u v:=p.append q.reverse
  have hw: ∀ x ∈ w.support,x ∈ ({z}ᶜ:Set W) :=by
    intro x hx
    rw [wkMSAI] at hx
    simp only [stMCI,stMSI]
    rcases hx with hxp | hxq
    · exact fun hzx ↦ hp (hzx ▸ hxp)
    · have hxq':x ∈ q.support:=by simpa using hxq
      exact fun hzx ↦ hq (hzx ▸ hxq')
  let wi:=w.induce ({z}ᶜ:Set W) hw
  exact ⟨wi.copy (subExt rfl) (subExt rfl)⟩
omit [DecidableEq V] [Fintype V] in
private theorem wu (hG:G.Connected) (A B :Set V) (x y :V) :
    ∃ p : (qA G A B).Walk (Sum.inl x) (Sum.inl y),
      ∀ z ∈ p.support,z ∈ Set.range (Sum.inl:V → sg V) :=by
  classical
  obtain ⟨p⟩ :=hG x y
  let r :=p.map (qn G A B).toHom
  have hr: ∀ z ∈ r.support,
      z ∈ Set.range (Sum.inl:V → sg V) :=by
    intro z hz
    simp only [r,wkSM,lsMM] at hz
    obtain ⟨w,-,rfl⟩ :=hz
    exact stMRS w
  let hx: (qn G A B) x =Sum.inl x :=rfl
  let hy: (qn G A B) y =Sum.inl y :=rfl
  let r':=r.copy hx hy
  have hsupp:r'.support=r.support:=Walk.support_copy r hx hy
  refine ⟨r',?_⟩
  intro z hz
  exact hr z (hsupp ▸ hz)
omit [DecidableEq V] in
private theorem wr (hG:qh G)
    (A B :Set V) (z:V) {x y :V} (hx:x ≠ z) (hy:y ≠ z) :
    ∃ p : (qA G A B).Walk (Sum.inl x) (Sum.inl y),
      Sum.inl z ∉ p.support:=by
  classical
  obtain ⟨p,-,hpz⟩ :=hG.sT z hx hy
  refine ⟨p.map (qn G A B).toHom,?_⟩
  intro hz
  change (qn G A B) z ∈
    (p.map (qn G A B).toHom).support at hz
  rw [wkSM,lsMM] at hz
  obtain ⟨w,hw,hwz⟩ :=hz
  exact hpz ((Sum.inl_injective hwz) ▸ hw)
omit [DecidableEq V] [Fintype V] in
private theorem tF (hG:G.Connected)
    {A B :Set V} (hA:A.Nonempty) (hB:B.Nonempty) :
    (qA G A B).Connected:=by
  classical
  obtain ⟨a,ha⟩ :=hA
  obtain ⟨b,hb⟩ :=hB
  apply tB (H:=qA G A B) (Sum.inl a)
  intro w
  cases w with
  | inl x =>
      obtain ⟨p,-⟩ :=wu hG A B x a
      exact ⟨p⟩
  | inr i =>
      cases i with
      | false=>
          exact ⟨wkCons (u2.mpr ha) Walk.nil⟩
      | true=>
          obtain ⟨p,-⟩ :=wu hG A B b a
          exact ⟨wkCons (sJ.mpr hb) p⟩
omit [DecidableEq V] in
private theorem xh (hG:qh G)
    {A B :Set V} (hA:2 ≤ A.ncard) (hB:2 ≤ B.ncard) (z:V) :
    ((qA G A B).induce
      ({Sum.inl z}ᶜ:Set (sg V))).Connected:=by
  classical
  obtain ⟨a,ha,haz⟩ :=A.exists_ne_of_one_lt_ncard (by omega) z
  obtain ⟨b,hb,hbz⟩ :=B.exists_ne_of_one_lt_ncard (by omega) z
  apply r0
    (H:=qA G A B) (Sum.inl z) (Sum.inl a) (by simpa)
  intro w hw
  cases w with
  | inl x =>
      have hxz:x ≠ z:=by
        intro hxz
        exact hw (by simp [hxz])
      exact wr hG A B z hxz haz
  | inr i =>
      cases i with
      | false=>
          refine ⟨wkCons (u2.mpr ha) Walk.nil,?_⟩
          simp [haz.symm]
      | true=>
          obtain ⟨p,hp⟩ :=wr hG A B z hbz haz
          refine ⟨wkCons (sJ.mpr hb) p,?_⟩
          simpa using hp
omit [DecidableEq V] [Fintype V] in
private theorem wV (hG:G.Connected)
    {A B :Set V} (hB:B.Nonempty) :
    ((qA G A B).induce
      ({Sum.inr false}ᶜ:Set (sg V))).Connected:=by
  classical
  obtain ⟨b,hb⟩ :=hB
  apply r0
    (H:=qA G A B) (Sum.inr false) (Sum.inl b) (by simp)
  intro w hw
  cases w with
  | inl x =>
      obtain ⟨p,hpold⟩ :=wu hG A B x b
      refine ⟨p,?_⟩
      intro h
      obtain ⟨y,hy⟩ :=hpold _ h
      cases hy
  | inr i =>
      cases i with
      | false=> exact (hw rfl).elim
      | true=>
          refine ⟨wkCons (sJ.mpr hb) Walk.nil,?_⟩
          simp
omit [DecidableEq V] [Fintype V] in
private theorem wI (hG:G.Connected)
    {A B :Set V} (hA:A.Nonempty) :
    ((qA G A B).induce
      ({Sum.inr true}ᶜ:Set (sg V))).Connected:=by
  classical
  obtain ⟨a,ha⟩ :=hA
  apply r0
    (H:=qA G A B) (Sum.inr true) (Sum.inl a) (by simp)
  intro w hw
  cases w with
  | inl x =>
      obtain ⟨p,hpold⟩ :=wu hG A B x a
      refine ⟨p,?_⟩
      intro h
      obtain ⟨y,hy⟩ :=hpold _ h
      cases hy
  | inr i =>
      cases i with
      | false=>
          refine ⟨wkCons (u2.mpr ha) Walk.nil,?_⟩
          simp
      | true=> exact (hw rfl).elim
omit [DecidableEq V] in
theorem yK (hG:qh G) {A B :Set V}
    (hA:2 ≤ A.ncard) (hB:2 ≤ B.ncard) :
    qh (qA G A B) :=by
  classical
  have hAne:A.Nonempty:= (Set.ncard_pos (Set.toFinite A)).mp (by omega)
  have hBne:B.Nonempty:= (Set.ncard_pos (Set.toFinite B)).mp (by omega)
  refine ⟨?_,tF hG.connected hAne hBne,?_⟩
  · have hcard:=hG.xV
    simp [sg]
    omega
  · intro z
    cases z with
    | inl x => exact xh hG hA hB x
    | inr i =>
        cases i with
        | false=> exact wV hG.connected hBne
        | true=> exact wI hG.connected hAne
private structure w5 (G:SimpleGraph V) (A B :Set V)
    (p: (qA G A B).Walk (Sum.inr false) (Sum.inr true)) where
  a:V
  b:V
  walk: (qA G A B).Walk (Sum.inl a) (Sum.inl b)
  isPath:walk.IsPath
  a_mem:a ∈ A
  b_mem:b ∈ B
  support_subset_tail:walk.support ⊆ p.support.tail
  old_support: ∀ x ∈ walk.support,
    x ∈ Set.range (Sum.inl:V → sg V)
omit [DecidableEq V] [Fintype V] in
private theorem ya {A B :Set V}
    (p: (qA G A B).Walk (Sum.inr false) (Sum.inr true))
    (hp:p.IsPath) : Nonempty (w5 G A B p) :=by
  classical
  have hp_nonNil: ¬p.Nil:=wkNNON (by simp)
  have htailPath:p.tail.IsPath:=hp.tail
  have htail_nonNil: ¬p.tail.Nil:=by
    intro hnil
    have hsnd:p.snd=Sum.inr true:=htailPath.nil_iff_eq.mp hnil
    have hadj:=p.adj_snd hp_nonNil
    rw [hsnd] at hadj
    simp [qA] at hadj
  have hpen:p.tail.penultimate=p.penultimate:=by
    have h :=Walk.penultimate_cons_of_not_nil
      (p.adj_snd hp_nonNil) p.tail htail_nonNil
    rw [p.cons_tail_eq hp_nonNil] at h
    exact h.symm
  have hleft:=p.adj_snd hp_nonNil
  have hright:=p.adj_penultimate hp_nonNil
  cases hs:p.snd with
  | inr i =>
    rw [hs] at hleft
    cases i <;> simp [qA] at hleft
  | inl a =>
    rw [hs] at hleft
    cases ht:p.penultimate with
    | inr i =>
      rw [ht] at hright
      cases i <;> simp [qA] at hright
    | inl b =>
      rw [ht] at hright
      have ha:a ∈ A:=by simpa using hleft
      have hb:b ∈ B:=by simpa using hright
      let m₀:=p.tail.dropLast
      have hm₀:m₀.IsPath:=hp.tail.dropLast
      have hmend:p.tail.penultimate=Sum.inl b :=hpen.trans ht
      let m : (qA G A B).Walk (Sum.inl a) (Sum.inl b) :=
        m₀.copy hs hmend
      have hmsub:m.support ⊆ p.support.tail:=by
        intro x hx
        have hx₀:x ∈ m₀.support:=by simpa [m] using hx
        have hxdrop:x ∈ p.tail.support.dropLast:=by
          simpa [m₀,Walk.support_dropLast htail_nonNil] using hx₀
        have hxtail:x ∈ p.tail.support:=List.mem_of_mem_dropLast hxdrop
        simpa [p.support_tail_of_not_nil hp_nonNil] using hxtail
      have halpha:Sum.inr false ∉ p.support.tail:=by
        have hn:=hp.support_nodup
        rw [← p.cons_tail_support] at hn
        exact (lsNC.mp hn).1
      have hbeta:Sum.inr true ∉ m.support:=by
        intro hx
        have hx₀:Sum.inr true ∈ m₀.support:=by simpa [m] using hx
        have hn:=hp.tail.support_nodup
        rw [← p.tail.support_dropLast_concat htail_nonNil] at hn
        exact hn.disjoint hx₀ (by simp)
      refine ⟨{
        a:=a
        b:=b
        walk:=m
        isPath:=by simpa [m] using hm₀
        a_mem:=ha
        b_mem:=hb
        support_subset_tail:=hmsub
        old_support:= ?_}⟩
      intro x hx
      cases x with
      | inl v => exact ⟨v,rfl⟩
      | inr i =>
          cases i with
          | false=> exact (halpha (hmsub hx)).elim
          | true=> exact (hbeta hx).elim
omit [DecidableEq V] [Fintype V] in
private theorem ad {A B :Set V} {a b :V}
    (p: (qA G A B).Walk (Sum.inl a) (Sum.inl b))
    (hold: ∀ x ∈ p.support,
      x ∈ Set.range (Sum.inl:V → sg V)) :
    ∃ q :G.Walk a b,q.map (qn G A B).toHom=p:=by
  classical
  let e :=qn G A B
  have hold': ∀ x ∈ p.support,x ∈ Set.range e :=by
    intro x hx
    obtain ⟨v,hv⟩ :=hold x hx
    refine ⟨v,?_⟩
    change Sum.inl v =x
    exact hv
  let p':=p.induce (Set.range e) hold'
  let q₀:=p'.map e.isoInduceRange.symm.toHom
  have hqa:e.isoInduceRange.symm
      ⟨Sum.inl a,stMRS a⟩ = a:=by
    exact e.isoInduceRange.symm_apply_apply a
  have hqb:e.isoInduceRange.symm
      ⟨Sum.inl b,stMRS b⟩ = b:=by
    exact e.isoInduceRange.symm_apply_apply b
  let q :G.Walk a b:=q₀.copy hqa hqb
  refine ⟨q,?_⟩
  apply Walk.ext_support
  calc
    (q.map (qn G A B).toHom).support=
        (q₀.map e.toHom).support:=by
      simp [q,e]
    _=p.support:=by
      simp only [q₀,wkSM,List.map_map]
      change List.map (fun x :Set.range e => e (e.isoInduceRange.symm x))
          p'.support=p.support
      have hfun: (fun x :Set.range e => e (e.isoInduceRange.symm x)) =
          (fun x :Set.range e => (x:sg V)) :=by
        funext x
        exact congrArg subVal (e.isoInduceRange.apply_symm_apply x)
      rw [hfun]
      change ((p.induce (Set.range e) hold').support.map subVal) = p.support
      rw [Walk.support_induce]
      exact List.attachWith_map_subtype_val hold'
omit [DecidableEq V] [Fintype V] in
private theorem w5.tw {A B :Set V}
    {p: (qA G A B).Walk (Sum.inr false) (Sum.inr true)}
    (S:w5 G A B p) :
    ∃ q :G.Walk S.a S.b,
      q.IsPath ∧ q.map (qn G A B).toHom=S.walk:=by
  classical
  obtain ⟨q,hq⟩ :=ad S.walk S.old_support
  refine ⟨q,?_,hq⟩
  have hmapped: (q.map (qn G A B).toHom).IsPath:=by
    rw [Walk.isPath_def,hq]
    exact S.isPath.support_nodup
  exact (Walk.isPath_map_iff_of_injective
    (f:= (qn G A B).toHom)
    (qn G A B).injective).mp hmapped
omit [DecidableEq V] in
theorem yF (hG:qh G) {A B :Set V}
    (hA:2 ≤ A.ncard) (hB:2 ≤ B.ncard) :
    Nonempty (x7 G A B) :=by
  classical
  let H :=qA G A B
  have hH:qh H :=hG.yK hA hB
  obtain ⟨z,c,hc,hleft,hright⟩ :=
    hH.dS (Sum.inr false) (Sum.inr true)
  obtain ⟨p,q,hp,hq,-,-,-,hmeet,-,-,-⟩ :=
    yg hc hleft hright (by simp)
  obtain ⟨P⟩ :=ya p hp
  obtain ⟨Q⟩ :=ya q hq
  obtain ⟨pG,hpG,hpmap⟩ :=P.tw
  obtain ⟨qG,hqG,hqmap⟩ :=Q.tw
  have hdisj:pG.support.Disjoint qG.support:=by
    rw [lsDL]
    intro x hxp hxq
    have hxp':Sum.inl x ∈ P.walk.support:=by
      have hxpmap: (qn G A B) x ∈
          (pG.map (qn G A B).toHom).support:=by
        rw [wkSM]
        exact lsMM.mpr ⟨x,hxp,rfl⟩
      rw [hpmap] at hxpmap
      exact hxpmap
    have hxq':Sum.inl x ∈ Q.walk.support:=by
      have hxqmap: (qn G A B) x ∈
          (qG.map (qn G A B).toHom).support:=by
        rw [wkSM]
        exact lsMM.mpr ⟨x,hxq,rfl⟩
      rw [hqmap] at hxqmap
      exact hxqmap
    have hxpArc:Sum.inl x ∈ p.support:=
      lsMOMT (P.support_subset_tail hxp')
    have hxqArc:Sum.inl x ∈ q.support:=
      lsMOMT (Q.support_subset_tail hxq')
    rcases hmeet (Sum.inl x) hxpArc hxqArc with h | h <;> simp at h
  exact ⟨{
    a₁:=P.a
    a₂:=Q.a
    b₁:=P.b
    b₂:=Q.b
    p:=pG
    q:=qG
    p_isPath:=hpG
    q_isPath:=hqG
    a₁_mem:=P.a_mem
    a₂_mem:=Q.a_mem
    b₁_mem:=P.b_mem
    b₂_mem:=Q.b_mem
    disjoint_support:=hdisj}⟩
end qh
end Erdos556
end cL
namespace Erdos556
open SimpleGraph
private theorem y4 (A B C:Prop) :
    ((A ↔ B) ↔ (B ↔ C)) ↔ (A ↔ C) :=by
  tauto
theorem xt {V:Type*} {G:SimpleGraph V}
    (S:Set V) (colour:S → Bool) {u v :S}
    (p:G.Walk u.val v.val) (hp:p.IsPath)
    (hwrong: ¬ (Even p.length ↔ (colour u ↔ colour v))) :
    ∃ a b:S,a.val ≠ b.val ∧ ∃ q :G.Walk a.val b.val,q.IsPath ∧
      ¬ (Even q.length ↔ (colour a ↔ colour b)) ∧ q.length ≤ p.length ∧
      ∀ z ∈ q.support,z ≠ a.val → z ≠ b.val → z ∉ S:=by
  classical
  let P (m:ℕ) : Prop:= ∃ a b :S,∃ q:G.Walk a.val b.val,
    q.IsPath ∧ ¬ (Even q.length ↔ (colour a ↔ colour b)) ∧ q.length=m
  have hex: ∃ m,P m:= ⟨p.length,u,v,p,hp,hwrong,rfl⟩
  obtain ⟨a,b,q,hq,hqw,hlen⟩ :=Nat.find_spec hex
  have hmin {x y :S} (r:G.Walk x.val y.val) (hr:r.IsPath)
      (hw: ¬ (Even r.length ↔ (colour x ↔ colour y))) : q.length ≤ r.length:=by
    rw [hlen]
    exact Nat.find_min' hex ⟨x,y,r,hr,hw,rfl⟩
  have hcons {x y :S} (r:G.Walk x.val y.val) (hr:r.IsPath)
      (hlt:r.length < q.length) : Even r.length ↔ (colour x ↔ colour y) :=by
    by_contra hw
    exact (Nat.not_le_of_gt hlt) (hmin (x:=x) (y:=y) r hr hw)
  have hab:a.val ≠ b.val:=by
    intro h
    have heq:a=b:=subExt h
    subst b
    have hz:= (Walk.isPath_iff_nil.mp hq).length_eq_zero
    exact hqw (by simp [hz])
  refine ⟨a,b,hab,q,hq,hqw,hmin (x:=u) (y:=v) p hp hwrong,?_⟩
  intro z hz hza hzb hzS
  let x :S:= ⟨z,hzS⟩
  let r :G.Walk a.val x.val:=q.takeUntil z hz
  let s :G.Walk x.val b.val:=q.dropUntil z hz
  have hr:=hcons (x:=a) (y:=x) r (hq.takeUntil hz) (q.length_takeUntil_lt_length hz hzb)
  have hs:=hcons (x:=x) (y:=b) s (hq.dropUntil hz) (q.length_dropUntil_lt_length hz hza)
  have hsum:q.length=r.length+s.length:=by
    have h :=congrArg Walk.length (q.take_spec hz)
    simpa only [wkLA] using h.symm
  apply hqw
  rw [hsum,Nat.even_add,hr,hs]
  exact y4 _ _ _
theorem xC {V:Type*} {G:SimpleGraph V}
    (S:Set V) (colour: (G.induce S).Coloring Bool) {u v :S}
    (p: (G.induce S).Walk u v) (hp:p.IsPath) (hlen:1 < p.length)
    (q:G.Walk u.val v.val) (hq:q.IsPath)
    (hqS: ∀ z ∈ q.support,z ≠ u.val → z ≠ v.val → z ∉ S)
    (hwrong: ¬ (Even q.length ↔ (colour u ↔ colour v))) :
    ∃ c :G.Walk u.val u.val,c.IsCycle ∧ Odd c.length ∧ p.length ≤ c.length:=by
  let f :G.induce S ↪g G :=
    { toFun:=subVal,inj':=subVI,map_rel_iff':=Iff.rfl}
  have hpS (z:V) (hz:z ∈ (p.map f.toHom).support) : z ∈ S:=by
    rw [wkSM,lsMM] at hz
    obtain ⟨x,_,hx⟩ :=hz
    subst z
    exact x.property
  have hcycle: ((p.map f.toHom).append q.reverse).IsCycle:=by
    apply qy (p.map f.toHom) q
      (hp.map f.injective) hq (by simpa only [wkLM] using hlen)
    intro z hzp hzq
    by_cases hzu:z=u.val
    · exact orInl hzu
    by_cases hzv:z=v.val
    · exact orInr hzv
    exact (hqS z hzq hzu hzv (hpS z hzp)).elim
  have hpar:p.length%2 ≠ q.length%2:=by
    intro h
    apply hwrong
    have heq:Even q.length ↔ Even p.length:=by
      simp only [natEI]
      omega
    exact heq.trans (colour.even_length_iff_congr p)
  refine ⟨(p.map f.toHom).append q.reverse,hcycle,?_,?_⟩
  · apply natOI.mpr
    change ((p.map f.toHom).append q.reverse).length%2=1
    simp only [wkLA,wkLM,wkLR]
    omega
  · change p.length ≤ ((p.map f.toHom).append q.reverse).length
    simp only [wkLA,wkLM,wkLR]
    omega
end Erdos556
namespace Erdos556
open SimpleGraph
theorem ve {V:Type*} [Fintype V]
    {G:SimpleGraph V} (hG:qh G) (hnonbip: ¬ G.Colorable 2)
    (S:Set V) (hS:2 ≤ S.ncard) (colour:S → Bool) :
    ∃ a b:S,∃ p:G.Walk a.val b.val,p.IsPath ∧
      ¬ (Even p.length ↔ (colour a ↔ colour b)) :=by
  classical
  obtain ⟨w,c,hc,ho⟩ : ∃ (w:V) (c:G.Walk w w),c.IsCycle ∧ Odd c.length:=by
    by_contra h
    apply hnonbip
    apply (xJ G).mpr
    intro w c hc ho
    exact h ⟨w,c,hc,ho⟩
  let C :Set V := {z | z ∈ c.support}
  have hC:C.Nontrivial:=by
    refine ⟨w,c.start_mem_support,c.snd,?_,(c.adj_snd hc.not_nil).ne⟩
    exact lsMOMT (Walk.snd_mem_tail_support hc.not_nil)
  have hCcard:2 ≤ C.ncard:=Set.one_lt_ncard_iff_nontrivial.mpr hC
  obtain ⟨P⟩ :=hG.yF hS hCcard
  obtain ⟨x,hxC,p,hp,_,hpsub,hpC⟩ :=
    rq P.p P.p_isPath C P.b₁_mem
  obtain ⟨y,hyC,q,hq,_,hqsub,hqC⟩ :=
    rq P.q P.q_isPath C P.b₂_mem
  have hpq (z:V) (hzp:z ∈ p.support) (hzq:z ∈ q.support) : False:=
    P.disjoint_support (hpsub hzp) (hqsub hzq)
  have hxy:x ≠ y:=by
    intro h
    exact hpq x p.end_mem_support (h ▸ q.end_mem_support)
  obtain ⟨r,s,hr,hs,hpar,_,_,_,_⟩ :=
    rE c hc ho p q hp hq hxC hyC hxy hpC hqC hpq
  let a :S:= ⟨P.a₁,P.a₁_mem⟩
  let b :S:= ⟨P.a₂,P.a₂_mem⟩
  by_cases h :Even r.length ↔ (colour a ↔ colour b)
  · refine ⟨a,b,s,hs,?_⟩
    intro h'
    have he:=h.trans h'.symm
    simp only [natEI] at he
    apply hpar
    omega
  · exact ⟨a,b,r,hr,h⟩
theorem vu {V:Type*} [Fintype V]
    {G:SimpleGraph V} (hG:qh G) (hnonbip: ¬ G.Colorable 2)
    (S:Set V) (hS:2 ≤ S.ncard) (colour:S → Bool) :
    ∃ a b:S,a.val ≠ b.val ∧ ∃ p :G.Walk a.val b.val,p.IsPath ∧
      ¬ (Even p.length ↔ (colour a ↔ colour b)) ∧
      ∀ z ∈ p.support,z ≠ a.val → z ≠ b.val → z ∉ S:=by
  classical
  obtain ⟨u,v,p,hp,hw⟩ :=ve hG hnonbip S hS colour
  obtain ⟨a,b,hab,q,hq,hqw,_,hav⟩ :=
    xt S colour (u:=u) (v:=v) p hp hw
  exact ⟨a,b,hab,q,hq,hqw,hav⟩
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem ub {V:Type*} [DecidableEq V]
    {G:SimpleGraph V} (L:ℕ) (R:Finset V)
    (hres: ∀ x y S,S.card ≤ L+1 → qY G L x y (R \ S))
    (u v :V) (huv:u ≠ v) {a b :V} (p:G.Walk a b) (hp:p.IsPath)
    (hlen:0 < p.length) (hav: ∀ x ∈ p.support,x ∉ R ∧ x ≠ u ∧ x ≠ v) :
    ∃ q :G.Walk u v,q.IsPath ∧ p.length ≤ q.length ∧ q.length ≤ p.length+2*L:=by
  classical
  have hab:a ≠ b:=by
    intro h
    have hz:= ((hp.nil_iff_eq).mpr h).length_eq_zero
    omega
  have hau:a ≠ u:= (hav a p.start_mem_support).2.1
  have hav':a ≠ v:= (hav a p.start_mem_support).2.2
  have hbu:b ≠ u:= (hav b p.end_mem_support).2.1
  obtain ⟨r,hr,hrlen,hrR⟩ :=hres u a {v} (by simp)
  have hrv:v ∉ r.support:=by
    intro hv
    have h :=hrR v hv huv.symm hav'.symm
    exact (mem_sdiff.mp h).2 (mem_singleton_self v)
  have hrP (z:V) (hzr:z ∈ r.support) (hzp:z ∈ p.support) : z=a:=by
    by_contra hza
    have hzu:= (hav z hzp).2.1
    exact (hav z hzp).1 (mem_sdiff.mp (hrR z hzr hzu hza)).1
  have hrb:b ∉ r.support:=by
    intro h
    exact hab (hrP b h p.end_mem_support).symm
  have hcard:r.support.toFinset.card ≤ L+1:=by
    have h :=lsTCL r.support
    rw [r.length_support] at h
    omega
  obtain ⟨s,hs,hslen,hsR⟩ :=hres v b r.support.toFinset hcard
  have hrs (z:V) (hzr:z ∈ r.support) (hzs:z ∈ s.support) : False:=by
    have hzv:z ≠ v:=fun h => hrv (h ▸ hzr)
    have hzb:z ≠ b:=fun h => hrb (h ▸ hzr)
    exact (mem_sdiff.mp (hsR z hzs hzv hzb)).2 (lsMT.mpr hzr)
  have hsP (z:V) (hzp:z ∈ p.support) (hzs:z ∈ s.support) : z=b:=by
    by_contra hzb
    have hzv:= (hav z hzp).2.2
    exact (hav z hzp).1 (mem_sdiff.mp (hsR z hzs hzv hzb)).1
  have hrp: (r.append p).IsPath:=qr r p hr hp hrP
  have hq: ((r.append p).append s.reverse).IsPath:=by
    apply qr (r.append p) s.reverse hrp hs.reverse
    intro z hz hzsr
    have hzs:z ∈ s.support:=by
      simpa only [wkSR,lsMR] using hzsr
    rcases (wkMSAI _ _).mp hz with hzr | hzp
    · exact (hrs z hzr hzs).elim
    · exact hsP z hzp hzs
  refine ⟨(r.append p).append s.reverse,hq,?_,?_⟩ <;>
    simp only [wkLA,wkLR] <;> omega
end Erdos556
namespace Erdos556
open SimpleGraph Filter
theorem sh (D B a:ℕ) (hD:0 < D) (hB:0 < B)
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (b d :ℕ),
      N₀ ≤ ftCard V → q8 G b →
      (∀ w,d+b ≤ G.degree w) → ftCard V ≤ D *d →
      ftCard V ≤ B *b →
      ∃ R :Finset V,(R.card:ℝ) ≤ 2*q*ftCard V ∧
        ∀ u v S,S.card ≤ a → qY G (3*D) u v (R \ S) :=by
  let L :=3*D
  let K :=B* ((a+1) * L)
  have hL:0 < L:=by dsimp [L];omega
  have hK:0 < K:=Nat.mul_pos hB (Nat.mul_pos (by omega) hL)
  obtain ⟨N₁,hN₁⟩ :=eventually_atTop.mp (uW q hq0 hq1 L K a hK)
  refine ⟨max N₁ 1,?_⟩
  intro V _ _ G _ b d hN hc hg hd hb
  have hV:0 < ftCard V :=by omega
  have hdpos:0 < d:=by nlinarith
  let m :=ftCard V /K
  have hbudget: ((a+1) * m) * L ≤ b:=by
    have hmul:B* (((a+1) * m) * L) ≤ B*b:=by
      calc
        B* (((a+1) * m) * L) = m*K:=by dsimp [K];ring
        _ ≤ ftCard V :=natDMLS _ _
        _ ≤ B*b:=hb
    nlinarith
  have hdiam:3*ftCard V ≤ d *L:=by dsimp [L];nlinarith
  exact zM G b d L m a hc hdpos hg hdiam hbudget q hq0 hq1
    (hN₁ _ (by omega)) hV
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem vA {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (L k :ℕ) (R:Finset V)
    (hres: ∀ x y S,S.card ≤ L+1 → qY G L x y (R \ S))
    (he: (k+R.card+2) * ftCard V < G.edgeFinset.card)
    (u v :V) (huv:u ≠ v) :
    ∃ p :G.Walk u v,p.IsPath ∧ 2*k < p.length:=by
  classical
  let S :=insert u (insert v R)
  let U := (S:Set V)ᶜ
  let H :=G.induce U
  have hS:S.card ≤ R.card+2:=by
    have h1:=card_insert_le u (insert v R)
    have h2:=card_insert_le v R
    dsimp [S]
    omega
  have hdeleted:=rc G S
  change G.edgeFinset.card ≤ H.edgeFinset.card+S.card*ftCard V at hdeleted
  have hmul:=natMLMR (ftCard V) hS
  have hH:k*ftCard V < H.edgeFinset.card:=by nlinarith
  have hcard:=ftCLOI (fun x :U=> x.val) subVI
  have hH': (2*k) * ftCard U < 2 *H.edgeFinset.card:=by
    have hmul':=natMLML k hcard
    nlinarith
  obtain ⟨a,b,p,hp,hlen⟩ :=z6 H (2*k) hH'
  let f :H ↪g G :=sgInduce U
  have hav (x:V) (hx:x ∈ (p.map f.toHom).support) : x ∉ R ∧ x ≠ u ∧ x ≠ v:=by
    rw [wkSM,lsMM] at hx
    obtain ⟨y,_,hy⟩ :=hx
    subst x
    have h :=y.property
    change y.val ∉ insert u (insert v R) at h
    simp only [mem_insert,not_or] at h
    exact ⟨h.2.2,h.1,h.2.1⟩
  have hpos:0 < (p.map f.toHom).length:=by
    simpa only [wkLM] using (Nat.lt_of_le_of_lt (Nat.zero_le _) hlen)
  obtain ⟨q,hq,hge,_⟩ :=ub L R hres u v huv
    (p.map f.toHom) (hp.map f.injective) hpos hav
  simp only [wkLM] at hge
  exact ⟨q,hq,hlen.trans_le hge⟩
theorem w1 (D B :ℕ) (hD:0 < D) (hB:0 < B)
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (b d k:ℕ),
      N₀ ≤ ftCard V → q8 G b →
      (∀ w,d+b ≤ G.degree w) → ftCard V ≤ D *d → ftCard V ≤ B *b →
      (k:ℝ) * ftCard V +2*q* (ftCard V :ℝ) ^ 2+
        2*ftCard V < (G.edgeFinset.card:ℝ) →
      ∀ u v,u ≠ v → ∃ p:G.Walk u v,p.IsPath ∧ 2*k < p.length:=by
  obtain ⟨N₀,hN₀⟩ :=sh D B (3*D+1) hD hB q hq0 hq1
  refine ⟨N₀,?_⟩
  intro V _ _ G _ b d k hN hc hg hd hb he u v huv
  obtain ⟨R,hR,hres⟩ :=hN₀ G b d hN hc hg hd hb
  have hmul:=mul_le_mul_of_nonneg_right hR (natCN (ftCard V) :
    (0:ℝ) ≤ ftCard V)
  have heR: ((k:ℝ) + R.card+2) * ftCard V < (G.edgeFinset.card:ℝ) :=by
    nlinarith
  have heN: (k+R.card+2) * ftCard V < G.edgeFinset.card:=by exact_mod_cast heR
  exact vA G (3*D) k R hres heN u v huv
end Erdos556
namespace Erdos556
open SimpleGraph
theorem xl {V:Type*} [Fintype V]
    {G:SimpleGraph V} (hG:qh G) (hnonbip: ¬ G.Colorable 2)
    (S:Set V) (hS:2 ≤ S.ncard) (colour: (G.induce S).Coloring Bool)
    (k:ℕ) (hk:1 ≤ k)
    (hlong: ∀ u v:S,u ≠ v → ∃ p: (G.induce S).Walk u v,
      p.IsPath ∧ 2*k < p.length) :
    ∃ (w:V) (c:G.Walk w w),c.IsCycle ∧ Odd c.length ∧ 2*k < c.length:=by
  classical
  obtain ⟨u,v,huv,q,hq,hwrong,hqS⟩ :=
    vu hG hnonbip S hS colour
  obtain ⟨p,hp,hlen⟩ :=hlong u v (fun h => huv (congrArg subVal h))
  obtain ⟨c,hc,ho,hge⟩ :=xC S colour p hp (by omega)
    q hq hqS hwrong
  exact ⟨u.val,c,hc,ho,hlen.trans_le hge⟩
theorem ux (D B :ℕ) (hD:0 < D) (hB:0 < B)
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) (b d k:ℕ),
      qh G → ¬ G.Colorable 2 → 2 ≤ S.card →
      N₀ ≤ ftCard (S:Set V) → q8 (G.induce (S:Set V)) b →
      (∀ w : (S:Set V),d+b ≤ (G.induce (S:Set V)).degree w) →
      ftCard (S:Set V) ≤ D*d → ftCard (S:Set V) ≤ B*b → 1 ≤ k →
      (G.induce (S:Set V)).Colorable 2 →
      (∀ (w:V) (c:G.Walk w w),c.IsCycle → Odd c.length → c.length ≤ 2*k) →
      ((G.induce (S:Set V)).edgeFinset.card:ℝ) ≤
        (k:ℝ) * ftCard (S:Set V) + 2*q* (ftCard (S:Set V) : ℝ) ^ 2+
          2*ftCard (S:Set V) :=by
  obtain ⟨N₀,hN₀⟩ :=w1 D B hD hB q hq0 hq1
  refine ⟨N₀,?_⟩
  intro V _ _ G _ S b d k hG hnb hS hN hc hg hd hb hk hcol ho
  by_contra he
  have hdensity:=lt_of_not_ge he
  have hlong:=hN₀ (G.induce (S:Set V)) b d k hN hc hg hd hb hdensity
  obtain ⟨colour⟩ :=hcol
  let col: (G.induce (S:Set V)).Coloring Bool:=
    SimpleGraph.recolorOfEquiv _ finTwoEquiv colour
  have hScard:2 ≤ (S:Set V).ncard:=by simpa only [stNCF] using hS
  obtain ⟨w,c,hcyc,hodd,hlen⟩ :=xl
    hG hnb (S:Set V) hScard col k hk hlong
  exact (Nat.not_le_of_gt hlen) (ho w c hcyc hodd)
end Erdos556
namespace Erdos556
open SimpleGraph Finset
noncomputable def bB {V:Type*} [DecidableEq V] (G:SimpleGraph V)
    (S:Finset V) (T:Finset ↥((S:Set V)ᶜ)) :
    (G.induce (S:Set V)ᶜ).induce (T:Set ↥((S:Set V)ᶜ))ᶜ ≃g
      G.induce (↑(S ∪ T.map (fnSubty (fun v => v ∈ (S:Set V)ᶜ)) :
        Finset V) : Set V)ᶜ:=by
  let U := (S:Set V)ᶜ
  let F :=S ∪ T.map (fnSubty (fun v => v ∈ U))
  let f : ↥((T:Set U)ᶜ) → ↥((F:Set V)ᶜ) :=fun x => ⟨x.val.val,by
    intro hx
    rcases mem_union.mp hx with hxS | hxT
    · exact x.val.property hxS
    · obtain ⟨y,hyT,hyx⟩ :=mem_map.mp hxT
      have heq:y=x.val:=subExt hyx
      exact x.property (heq ▸ hyT)⟩
  have hinj:Function.Injective f :=by
    intro x y h
    apply subExt
    apply subExt
    change (f x).val= (f y).val
    exact congrArg subVal h
  have hsurj:Function.Surjective f :=by
    intro y
    have hyS:y.val ∉ S:=fun h => y.property (mem_union_left _ h)
    let x :U:= ⟨y.val,hyS⟩
    have hxT:x ∉ T:=by
      intro h
      exact y.property (mem_union_right S (mem_map.mpr ⟨x,h,rfl⟩))
    exact ⟨⟨x,hxT⟩,rfl⟩
  exact { toEquiv:=Equiv.ofBijective f ⟨hinj,hsurj⟩,map_rel_iff':=Iff.rfl}
theorem q8.e6 {V:Type*}
    {G:SimpleGraph V} {b s :ℕ} (hG:q8 G (b+s))
    (S:Finset V) (hS:S.card ≤ s) :
    q8 (G.induce (S:Set V)ᶜ) b :=by
  classical
  intro T hT
  let F :=S ∪ T.map (fnSubty (fun v => v ∈ (S:Set V)ᶜ))
  have hF:F.card ≤ b+s:=by
    have h :=card_union_le S (T.map (fnSubty (fun v => v ∈ (S:Set V)ᶜ)))
    rw [card_map] at h
    dsimp [F]
    omega
  exact (bB G S T).preconnected_iff.mpr (hG F hF)
end Erdos556
namespace Erdos556
open SimpleGraph Finset
noncomputable def cZ {V W :Type*} [DecidableEq V] [DecidableEq W]
    {G:SimpleGraph V} {H:SimpleGraph W} (e:G ≃g H) (S:Finset V) :
    G.induce (S:Set V)ᶜ ≃g H.induce (S.map e.toEquiv.toEmbedding:Set W)ᶜ where
  toEquiv:=
    { toFun:=fun x => ⟨e x.val,by
        intro hx
        obtain ⟨y,hy,hyx⟩ :=mem_map.mp hx
        exact x.property (e.injective hyx ▸ hy)⟩
      invFun:=fun y => ⟨e.symm y.val,by
        intro hy
        exact y.property (mem_map.mpr ⟨e.symm y.val,hy,e.apply_symm_apply y.val⟩)⟩
      left_inv:=fun x => subExt (e.symm_apply_apply x.val)
      right_inv:=fun y => subExt (e.apply_symm_apply y.val)}
  map_rel_iff':=by intro x y;exact e.map_adj_iff
theorem q8.iso {V W :Type*}
    {G:SimpleGraph V} {H:SimpleGraph W} {b:ℕ}
    (hG:q8 G b) (e:G ≃g H) : q8 H b:=by
  classical
  intro S hS
  have h :=hG (S.map e.symm.toEquiv.toEmbedding) (by simpa only [card_map] using hS)
  exact (cZ e.symm S).preconnected_iff.mpr h
end Erdos556
namespace Erdos556
open SimpleGraph Finset
def x8 {V:Type*} (G:SimpleGraph V) (S T :Set V) (h:S=T) :
    G.induce S ≃g G.induce T :=by
  subst T
  exact SimpleGraph.Iso.refl
def xX {V:Type*} [DecidableEq V] (S:Finset V) (T:Finset S) : Finset V :=
  Tᶜ.map (fnSubty (fun v => v ∈ S))
theorem ak {V:Type*} [DecidableEq V] (S:Finset V) (T:Finset S) :
    (xX S T).card=S.card-T.card:=by
  simp only [xX,card_map,card_compl,ftCC]
noncomputable def tk {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) (S:Finset V) (T:Finset S) :
    (G.induce (S:Set V)).induce (T:Set S)ᶜ ≃g
      G.induce (xX S T:Set V) :=
  (x8 (G.induce (S:Set V)) (T:Set S)ᶜ
    (↑(Tᶜ:Finset S) : Set S) (Finset.coe_compl T).symm).trans
      (sy G S Tᶜ)
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem wW (D B :ℕ) (hD:0 < D) (hB:0 < B)
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) (b d k:ℕ),
      qh G → ¬ G.Colorable 2 → N₀+ (b+3*D+3) + 2 ≤ S.card →
      q8 (G.induce (S:Set V)) (2* (b+3*D+3)) →
      (∀ w :S,d+2* (b+3*D+3) ≤ (G.induce (S:Set V)).degree w) →
      S.card ≤ D*d → S.card ≤ B*b → 1 ≤ k →
      (∀ (w:V) (c:G.Walk w w),c.IsCycle → Odd c.length → c.length ≤ 2*k) →
      ((G.induce (S:Set V)).edgeFinset.card:ℝ) ≤
        (k:ℝ) * S.card+2*q* (S.card:ℝ) ^ 2+ (b+3*D+5:ℕ) * (S.card:ℝ) :=by
  obtain ⟨N₁,hN₁⟩ :=ua D B hB q hq0 hq1
  obtain ⟨N₂,hN₂⟩ :=ux D B hD hB q hq0 hq1
  refine ⟨max N₁ N₂,?_⟩
  intro V _ _ G _ S b d k hG hnb hN hc hg hd hb hk ho
  classical
  let J :=G.induce (S:Set V)
  let t :=b+3*D+3
  have hScard:ftCard (S:Set V) = S.card:=by
    calc
      ftCard (S:Set V) = (S:Set V).ncard:=natCEFC.symm
      _=S.card:=stNCF S
  have hoJ (w: (S:Set V)) (c:J.Walk w w) (hcyc:c.IsCycle) (hodd:Odd c.length) :
      c.length ≤ 2*k:=by
    let f :J ↪g G :=sgInduce (S:Set V)
    have h :=ho (f w) (c.map f.toHom) (hcyc.map f.injective)
      (by simpa only [wkLM] using hodd)
    simpa only [wkLM] using h
  by_cases hrobust:qT J t
  · have hg' (w: (S:Set V)) : d+ (b+3*D+3) ≤ J.degree w :=by
      have h :=hg w
      change d +2* (b+3*D+3) ≤ J.degree w at h
      omega
    have hcore:=hN₁ J b d k (by rw [hScard];omega) (hc.mono (by omega))
      hrobust hg' (by simpa only [hScard] using hd) (by simpa only [hScard] using hb) hk hoJ
    rw [hScard] at hcore
    have hnonneg: (0:ℝ) ≤ (b+3*D+5:ℕ) * (S.card:ℝ) :=by positivity
    exact hcore.trans (le_add_of_nonneg_right hnonneg)
  · obtain ⟨T,hT,hcol⟩ : ∃ T :Finset (S:Set V),T.card ≤ t ∧
        (J.induce (T:Set (S:Set V))ᶜ).Colorable 2 :=by
      simpa only [qT,not_forall,not_not,exists_prop] using hrobust
    let K :=xX S T
    let H :=J.induce (T:Set (S:Set V))ᶜ
    let e :H ≃g G.induce (K:Set V) :=tk G S T
    have hK:K.card=S.card-T.card:=ak S T
    have hKle:K.card ≤ S.card:=by omega
    have hKcard:ftCard (K:Set V) = K.card:=by
      calc
        ftCard (K:Set V) = (K:Set V).ncard:=natCEFC.symm
        _=K.card:=stNCF K
    have hHC:q8 H b:=
      (hc.mono (show b +t ≤ 2* (b+3*D+3) by dsimp [t];omega)).e6 T hT
    have hHD (w: ↥((T:Set (S:Set V))ᶜ)) : d+b ≤ H.degree w :=by
      have h :=qW J T w
      have hdeg:=hg w.val
      change d +2* (b+3*D+3) ≤ J.degree w.val at hdeg
      change J.degree w.val ≤ H.degree w +T.card at h
      dsimp [t] at hT
      omega
    have hKD (v: (K:Set V)) : d+b ≤ (G.induce (K:Set V)).degree v :=by
      calc
        d+b ≤ H.degree (e.symm v) :=hHD _
        _= (G.induce (K:Set V)).degree v :=by rw [← e.degree_eq,e.apply_symm_apply]
    have hcolK: (G.induce (K:Set V)).Colorable 2 :=hcol.of_hom e.symm.toHom
    have hcore:=hN₂ G K b d k hG hnb (by dsimp [t] at hT;omega)
      (by rw [hKcard];dsimp [t] at hT;omega) (hHC.iso e) hKD
      (by rw [hKcard];omega) (by rw [hKcard];omega) hk hcolK ho
    rw [hKcard] at hcore
    have hKL: (K.card:ℝ) ≤ S.card:=by exact_mod_cast hKle
    have hmain: (k:ℝ) * K.card+2*q* (K.card:ℝ) ^ 2+2*K.card ≤
        (k:ℝ) * S.card+2*q* (S.card:ℝ) ^ 2+2*S.card:=by
      gcongr
    have hdel:=rc J T
    change J.edgeFinset.card ≤ H.edgeFinset.card+T.card*ftCard (S:Set V) at hdel
    rw [e.card_edgeFinset_eq,hScard] at hdel
    have hdelR: (J.edgeFinset.card:ℝ) ≤ ((G.induce (K:Set V)).edgeFinset.card:ℝ) +
        (T.card:ℝ) * S.card:=by exact_mod_cast hdel
    have hTR: (T.card:ℝ) ≤ (b+3*D+3:ℕ) :=by exact_mod_cast hT
    have hmul:=mul_le_mul_of_nonneg_right hTR (natCN S.card: (0:ℝ) ≤ S.card)
    push_cast at hmul ⊢
    nlinarith
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem uV (D B :ℕ) (hD:0 < D) (hB:0 < B)
    (q:ℝ) (hq0:0 < q) (hq1:q ≤ 1) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (b d k:ℕ) (r η :ℝ),
      qh G → ¬ G.Colorable 2 → 1 ≤ k → 0 ≤ r → 0 ≤ η →
      ((2* (b+3*D+3) : ℕ) : ℝ) ≤ r →
      ((2* (b+3*D+3) : ℕ) : ℝ) * ftCard V ≤
        2*η* (r- (2* (b+3*D+3) : ℕ)) ^ 2 →
      ((d+2* (b+3*D+3) : ℕ) : ℝ) ≤ r →
      ftCard V ≤ D *d → ftCard V ≤ B *b →
      ((N₀+ (b+3*D+3) + 2:ℕ) : ℝ) ≤ r →
      (k:ℝ) + 2*q*ftCard V + (b+3*D+5:ℕ) ≤ r →
      (∀ (w:V) (c:G.Walk w w),c.IsCycle → Odd c.length → c.length ≤ 2*k) →
      ∀ A :Finset V,((G.induce (A:Set V)).edgeFinset.card:ℝ) ≤
        r*A.card+η* (A.card:ℝ) ^ 2:=by
  obtain ⟨N₀,hN₀⟩ :=wW D B hD hB q hq0 hq1
  refine ⟨N₀,?_⟩
  intro V _ _ G _ b d k r η hG hnb hk hr hη ht hbudget hdeg hDcard hBcard horder hmargin ho A
  by_contra hA
  obtain ⟨S,hS,hdense,hmin,hc⟩ :=sR
    G (2* (b+3*D+3)) r η hr hη ht hbudget A (lt_of_not_ge hA)
  have hScard:ftCard (S:Set V) = S.card:=by
    calc
      ftCard (S:Set V) = (S:Set V).ncard:=natCEFC.symm
      _=S.card:=stNCF S
  have hSle:S.card ≤ ftCard V :=card_le_univ S
  obtain ⟨v,hv⟩ :=hS
  have hminv:=hmin ⟨v,hv⟩
  have hvdeg:= (G.induce (S:Set V)).degree_lt_card_verts ⟨v,hv⟩
  rw [hScard] at hvdeg
  have hvdegR: ((G.induce (S:Set V)).degree ⟨v,hv⟩ : ℝ) < S.card:=by exact_mod_cast hvdeg
  have hSorder:N₀+ (b+3*D+3) + 2 ≤ S.card:=by
    have h : ((N₀+ (b+3*D+3) + 2:ℕ) : ℝ) ≤ S.card:=by linarith
    exact_mod_cast h
  have hdegrees (w:S) : d+2* (b+3*D+3) ≤ (G.induce (S:Set V)).degree w :=by
    have h :=hdeg.trans (hmin w).le
    exact_mod_cast h
  have hbound:=hN₀ G S b d k hG hnb hSorder hc hdegrees
    (hSle.trans hDcard) (hSle.trans hBcard) hk ho
  have hSleR: (S.card:ℝ) ≤ ftCard V :=by exact_mod_cast hSle
  have hsq:=mul_le_mul_of_nonneg_right hSleR (natCN S.card: (0:ℝ) ≤ S.card)
  have hqmul:=mul_le_mul_of_nonneg_left hsq (by positivity: (0:ℝ) ≤ 2*q)
  have hrmul:=mul_le_mul_of_nonneg_right hmargin (natCN S.card: (0:ℝ) ≤ S.card)
  have hηmul:=mul_nonneg hη (sq_nonneg (S.card:ℝ))
  nlinarith
end Erdos556
namespace Erdos556
private theorem zJ (ε B t N x:ℝ)
    (hε:0 ≤ ε) (ht:0 ≤ t) (hN:0 ≤ N)
    (hB:4096 ≤ ε*B) (htB:B*t ≤ 2*N) (hx:N ≤ 32*x) :
    2*t*N ≤ ε*x^2:=by
  have h1:=mul_le_mul_of_nonneg_right hB (by positivity:0 ≤ 2*t*N)
  have h2:=mul_le_mul_of_nonneg_right htB (by positivity:0 ≤ 2*ε*N)
  have hsq:N^2 ≤ (32*x) ^ 2:=by gcongr
  have h3:=mul_le_mul_of_nonneg_left hsq hε
  nlinarith
private theorem tG (N B :ℕ) (hB:0 < B) (hN:B ≤ N) :
    N ≤ 2*B* (N/B) :=by
  have hb:1 ≤ N/B:=Nat.div_pos hN hB
  have hmod:=natML N hB
  have hsum:=Nat.mod_add_div N B
  have hmul:=natMLML B hb
  nlinarith
theorem ay (ε:ℝ) (hε:0 < ε) (B N₀ N k:ℕ)
    (hB:128 ≤ B) (hεB:4096 ≤ ε*B)
    (hN:195*B ≤ N) (hN₀:64* (N₀+2) ≤ N) (hk:N ≤ 16*k) :
    ∃ b d:ℕ,
      N ≤ 64*d ∧ N ≤ (2*B) * b ∧
      ((2* (b+195) : ℕ) : ℝ) ≤ (k:ℝ) + ε*N/2 ∧
      ((2* (b+195) : ℕ) : ℝ) * N ≤
        ε* ((k:ℝ) + ε*N/2- (2* (b+195) : ℕ)) ^ 2 ∧
      ((d+2* (b+195) : ℕ) : ℝ) ≤ (k:ℝ) + ε*N/2 ∧
      ((N₀+ (b+195) + 2:ℕ) : ℝ) ≤ (k:ℝ) + ε*N/2 ∧
      (k:ℝ) + ε/8*N+ (b+197:ℕ) ≤ (k:ℝ) + ε*N/2:=by
  let b :=N/B
  let d :=N/32
  let t :=b+195
  let r :ℝ:= (k:ℝ) + ε*N/2
  have hBpos:0 < B:=by omega
  have hBN:B ≤ N:=by nlinarith
  have hdb:N ≤ (2*B) * b:=tG N B hBpos hBN
  have hdd:N ≤ 64*d:=by dsimp [d];omega
  have hBb:b*B ≤ N:=natDMLS _ _
  have hBt:B*t ≤ 2*N:=by dsimp [t];nlinarith
  have hBtR: (B:ℝ) * t ≤ 2*N:=by exact_mod_cast hBt
  have hB128: (128:ℝ) ≤ B:=by exact_mod_cast hB
  have h64t: (64:ℝ) * t ≤ N:=by
    have h :=mul_le_mul_of_nonneg_right hB128 (natCN t : (0:ℝ) ≤ t)
    nlinarith
  have hdN: (32:ℝ) * d ≤ N:=by
    have h :d*32 ≤ N:=natDMLS _ _
    exact_mod_cast (by nlinarith:32*d ≤ N)
  have hkR: (N:ℝ) ≤ 16*k:=by exact_mod_cast hk
  have hrk: (k:ℝ) ≤ r:=by dsimp [r];exact le_add_of_nonneg_right (by positivity)
  have hdegree: (d:ℝ) + 2*t ≤ r:=by nlinarith
  have htR: (2:ℝ) * t ≤ r:=by have:= (natCN d : (0:ℝ) ≤ d);linarith
  have hx: (N:ℝ) ≤ 32* (r-2*t) :=by nlinarith
  have hbudget:=zJ ε B t N (r-2*t) hε.le
    (natCN _) (natCN _) hεB hBtR hx
  have hN₀R: (64:ℝ) * ((N₀:ℝ) + 2) ≤ N:=by exact_mod_cast hN₀
  have horder: (N₀:ℝ) + t+2 ≤ r:=by nlinarith
  have hBNR: (B:ℝ) ≤ N:=by exact_mod_cast hBN
  have hεN: (4096:ℝ) ≤ ε*N:=
    hεB.trans (mul_le_mul_of_nonneg_left hBNR hε.le)
  have h8t: (8:ℝ) * t ≤ ε*N:=by
    have h1:=mul_le_mul_of_nonneg_right (show (16:ℝ) ≤ ε*B by linarith)
      (natCN t : (0:ℝ) ≤ t)
    have h2:=mul_le_mul_of_nonneg_left hBtR hε.le
    nlinarith
  have hmargin: (k:ℝ) + ε/8*N+ ((t:ℝ) + 2) ≤ r:=by
    dsimp [r]
    nlinarith
  refine ⟨b,d,hdd,hdb,?_,?_,?_,?_,?_⟩
  · simpa only [natCM,natCO,r,t] using htR
  · simpa only [natCM,natCO,r,t] using hbudget
  · simpa only [natCA,natCM,natCO,r,t] using hdegree
  · simpa only [natCA,natCO,r,t] using horder
  · have heq:b+197=t+2:=by dsimp [t]
    simpa only [heq,natCA,natCO,r] using hmargin
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem v2 (ε:ℝ) (hε:0 < ε) (hε1:ε ≤ 1) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (k:ℕ),
      N₀ ≤ ftCard V → ftCard V ≤ 16*k → qh G → ¬ G.Colorable 2 →
      (∀ (w:V) (c:G.Walk w w),c.IsCycle → Odd c.length → c.length ≤ 2*k) →
      ∀ A :Finset V,((G.induce (A:Set V)).edgeFinset.card:ℝ) ≤
        ((k:ℝ) + ε*ftCard V) * A.card:=by
  obtain ⟨B,hB⟩ :=exists_nat_gt ((4096:ℝ) / ε+128)
  have hdiv0: (0:ℝ) ≤ 4096/ε:=by positivity
  have hB128R: (128:ℝ) ≤ B:=by linarith
  have hB128:128 ≤ B:=by exact_mod_cast hB128R
  have hεB: (4096:ℝ) ≤ ε*B:=by
    have h : (4096:ℝ) / ε < B:=by linarith
    have h':= (div_lt_iff₀ hε).mp h
    nlinarith
  have hBpos:0 < 2*B:=by omega
  have hqpos:0 < ε/16:=by positivity
  have hqle:ε/16 ≤ 1:=by linarith
  obtain ⟨N₁,hN₁⟩ :=uV 64 (2*B)
    (by decide) hBpos (ε/16) hqpos hqle
  refine ⟨max (195*B) (64* (N₁+2)),?_⟩
  intro V _ _ G _ k hN hk hG hnb ho
  let N :=ftCard V
  have hLarge:195*B ≤ N:=by dsimp [N];omega
  have hThreshold:64* (N₁+2) ≤ N:=by dsimp [N];omega
  have hkpos:1 ≤ k:=by dsimp [N] at hLarge;nlinarith
  obtain ⟨b,d,hDd,hBb,ht,hbudget,hdegree,horder,hmargin⟩ :=
    ay ε hε B N₁ N k hB128 hεB hLarge hThreshold hk
  have hηeq:2* (ε/2) = ε:=by ring
  have hqeq:2* (ε/16) = ε/8:=by ring
  have hquad:=hN₁ G b d k ((k:ℝ) + ε*N/2) (ε/2) hG hnb hkpos
    (by positivity) (by positivity)
    (by simpa [natAA] using ht)
    (by simpa [natAA,hηeq] using hbudget)
    (by simpa [natAA] using hdegree)
    hDd hBb (by simpa [natAA] using horder)
    (by simpa [natAA,hqeq] using hmargin) ho
  intro A
  have hA:=hquad A
  have hcard: (A.card:ℝ) ≤ N:=by exact_mod_cast card_le_univ A
  have hsq:=mul_le_mul_of_nonneg_right hcard (natCN A.card: (0:ℝ) ≤ A.card)
  have hεsq:=mul_le_mul_of_nonneg_left hsq (by positivity: (0:ℝ) ≤ ε/2)
  change ((G.induce (A:Set V)).edgeFinset.card:ℝ) ≤ ((k:ℝ) + ε*N) * A.card
  nlinarith
theorem xz (ε:ℝ) (hε:0 < ε) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (k:ℕ),
      N₀ ≤ ftCard V → ftCard V ≤ 16*k → qh G → ¬ G.Colorable 2 →
      (∀ (w:V) (c:G.Walk w w),c.IsCycle → Odd c.length → c.length ≤ 2*k) →
      ∀ A :Finset V,((G.induce (A:Set V)).edgeFinset.card:ℝ) ≤
        ((k:ℝ) + ε*ftCard V) * A.card:=by
  have hδ:0 < min ε 1:=lt_min hε (by norm_num)
  obtain ⟨N₀,hN₀⟩ :=v2 (min ε 1) hδ (min_le_right _ _)
  refine ⟨N₀,?_⟩
  intro V _ _ G _ k hN hk hG hnb ho A
  apply (hN₀ G k hN hk hG hnb ho A).trans
  gcongr
  exact min_le_left ε 1
end Erdos556
namespace Erdos556
open SimpleGraph Finset
def rp {V:Type*} (G:SimpleGraph V) (P:Finset (Finset V)) : SimpleGraph V where
  Adj u v:=G.Adj u v ∧ ∃ A ∈ P,u ∈ A ∧ v ∈ A
  symm:= ⟨by
    rintro u v ⟨huv,A,hA,hu,hv⟩
    exact ⟨huv.symm,A,hA,hv,hu⟩⟩
  loopless:= ⟨by intro u h;exact h.1.ne rfl⟩
theorem ah {V:Type*} (G:SimpleGraph V) (P:Finset (Finset V)) :
    rp G P ≤ G:=fun _ _ h => h.1
theorem xE {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (P:Finset (Finset V))
    [DecidableRel (rp G P).Adj]
    (hP: (P:Set (Finset V)).Pairwise Disjoint) :
    (rp G P).edgeFinset.card= ∑ A ∈ P,(G.induce (A:Set V)).edgeFinset.card:=by
  classical
  let E (A:Finset V) :=G.edgeFinset.filter (fun e => e.toFinset ⊆ A)
  have hedges: (rp G P).edgeFinset=P.biUnion E :=by
    ext e
    rcases e with ⟨⟨u,v⟩⟩
    change s(u,v) ∈ (rp G P).edgeFinset ↔ s(u,v) ∈ P.biUnion E
    rw [SimpleGraph.mem_edgeFinset,SimpleGraph.mem_edgeSet]
    change (G.Adj u v ∧ ∃ A ∈ P,u ∈ A ∧ v ∈ A) ↔ s(u,v) ∈ P.biUnion E
    simp only [mem_edgeFinset,mem_edgeSet,mem_biUnion,E,mem_filter,
      Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff]
    constructor
    · rintro ⟨huv,A,hA,hu,hv⟩
      exact ⟨A,hA,huv,hu,hv⟩
    · rintro ⟨A,hA,huv,hu,hv⟩
      exact ⟨huv,A,hA,hu,hv⟩
  have hdisj: (P:Set (Finset V)).Pairwise fun A B=> Disjoint (E A) (E B) :=by
    intro A hA B hB hAB
    rw [fsDL]
    intro e heA heB
    have ha:= (mem_filter.mp heA).2
    have hb:= (mem_filter.mp heB).2
    obtain ⟨v,hv⟩ :=Finset.nonempty_iff_ne_empty.mpr (Sym2.toFinset_ne_empty e)
    exact fsDL.mp (hP hA hB hAB) (ha hv) (hb hv)
  rw [hedges,card_biUnion hdisj]
  apply sum_congr rfl
  intro A _
  exact G.card_filter_edgeFinset_toFinset_subset A
theorem a1 {V:Type*}
    (G:SimpleGraph V) (P:Finset (Finset V)) (n:ℕ) [NeZero n]
    (hP: (P:Set (Finset V)).Pairwise Disjoint)
    (hcolour: ∀ A ∈ P,(G.induce (A:Set V)).Colorable n) :
    (rp G P).Colorable n :=by
  classical
  let C (A:P) : (G.induce (A.val:Set V)).Coloring (Fin n) :=
    Classical.choice (hcolour A.val A.property)
  let Q (v:V) : Prop:= ∃ A:P,v ∈ A.val
  let f (v:V) : Fin n :=if h :Q v then
    C (Classical.choose h) ⟨v,clCS h⟩ else 0
  have hf (A:P) (v:V) (hv:v ∈ A.val) : f v =C A ⟨v,hv⟩ :=by
    have hvQ:Q v:= ⟨A,hv⟩
    dsimp [f]
    rw [dif_pos hvQ]
    have heq:Classical.choose hvQ=A:=by
      apply subExt
      by_contra hne
      exact fsDL.mp
        (hP (Classical.choose hvQ).property A.property hne) (clCS hvQ) hv
    subst heq
    rfl
  refine ⟨{ toFun:=f,map_rel':= ?_}⟩
  intro u v huv
  obtain ⟨hG,A,hA,hu,hv⟩ :=huv
  rw [hf ⟨A,hA⟩ u hu,hf ⟨A,hA⟩ v hv]
  exact (C ⟨A,hA⟩).valid hG
end Erdos556
namespace Erdos556
open SimpleGraph Finset
def qp {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) (r:ℕ) (P:Finset (Finset V)) : Prop:=
  (P:Set (Finset V)).Pairwise Disjoint ∧
    ∀ A ∈ P,r < A.card ∧ qh (G.induce (A:Set V))
theorem qp.nonempty {V:Type*} [DecidableEq V]
    {G:SimpleGraph V} {r:ℕ} {P:Finset (Finset V)}
    (hP:qp G r P) {A:Finset V} (hA:A ∈ P) : A.Nonempty:=
  card_pos.mp ((Nat.zero_le r).trans_lt (hP.2 A hA).1)
def s4 {V:Type*} [DecidableEq V] (S:Finset V) (P:Finset (Finset S)) :
    Finset (Finset V) :=
  P.map (Finset.mapEmbedding (fnSubty (fun v => v ∈ S))).toEmbedding
theorem vH {V:Type*} [DecidableEq V] (S:Finset V) (P:Finset (Finset S))
    (A:Finset V) : A ∈ s4 S P ↔
      ∃ T ∈ P,T.map (fnSubty (fun v => v ∈ S)) = A:=by
  exact Finset.mem_map
theorem rP {V:Type*} [DecidableEq V]
    {S:Finset V} {P:Finset (Finset S)} {A:Finset V} (hA:A ∈ s4 S P) : A ⊆ S:=by
  obtain ⟨T,_,rfl⟩ := (vH S P A).mp hA
  intro x hx
  obtain ⟨y,_,hyx⟩ :=mem_map.mp hx
  exact hyx ▸ y.property
theorem qp.lift {V:Type*} [DecidableEq V]
    {G:SimpleGraph V} {r:ℕ} {S:Finset V} {P:Finset (Finset S)}
    (hP:qp (G.induce (S:Set V)) r P) :
    qp G r (s4 S P) :=by
  constructor
  · intro A hA B hB hAB
    obtain ⟨T,hT,rfl⟩ := (vH S P A).mp hA
    obtain ⟨U,hU,rfl⟩ := (vH S P B).mp hB
    apply (Finset.disjoint_map _).mpr
    exact hP.1 hT hU (fun h => hAB (congrArg (Finset.map _) h))
  · intro A hA
    obtain ⟨T,hT,rfl⟩ := (vH S P A).mp hA
    refine ⟨by simpa only [card_map] using (hP.2 T hT).1,?_⟩
    exact (hP.2 T hT).2.iso (sy G S T)
theorem vF {V:Type*} [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) (P:Finset (Finset S)) :
    (∑ A ∈ s4 S P,(G.induce (A:Set V)).edgeFinset.card) =
      ∑ T ∈ P,((G.induce (S:Set V)).induce (T:Set S)).edgeFinset.card:=by
  rw [s4,sum_map]
  apply sum_congr rfl
  intro T _
  exact (sy G S T).card_edgeFinset_eq.symm
theorem ab {V:Type*} [DecidableEq V]
    {S T :Finset V} (hST:Disjoint S T) (P:Finset (Finset S)) (Q:Finset (Finset T))
    (hP: ∀ A ∈ P,A.Nonempty) : Disjoint (s4 S P) (s4 T Q) :=by
  rw [fsDL]
  intro A hAP hAQ
  have hAS:=rP hAP
  have hAT:=rP hAQ
  obtain ⟨U,hU,rfl⟩ := (vH S P A).mp hAP
  obtain ⟨x,hx⟩ :=hP U hU
  have hxmap:x.val ∈ U.map (fnSubty (fun v => v ∈ S)) :=
    mem_map.mpr ⟨x,hx,rfl⟩
  exact fsDL.mp hST (hAS hxmap) (hAT hxmap)
theorem qp.union {V:Type*} [DecidableEq V]
    {G:SimpleGraph V} {r:ℕ} {P Q :Finset (Finset V)}
    (hP:qp G r P) (hQ:qp G r Q)
    (hcross: ∀ A ∈ P,∀ B ∈ Q,Disjoint A B) :
    qp G r (P ∪ Q) :=by
  constructor
  · intro A hA B hB hAB
    rcases mem_union.mp hA with hAP | hAQ <;> rcases mem_union.mp hB with hBP | hBQ
    · exact hP.1 hAP hBP hAB
    · exact hcross A hAP B hBQ
    · exact (hcross B hBP A hAQ).symm
    · exact hQ.1 hAQ hBQ hAB
  · intro A hA
    exact (mem_union.mp hA).elim (hP.2 A) (hQ.2 A)
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem uU {V:Type*} [Fintype V]
    [DecidableEq V] (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) :
    G.edgeFinset.card ≤ (G.induce (S:Set V)ᶜ).edgeFinset.card+
      ∑ v ∈ S,G.degree v :=by
  classical
  let A :=G.edgeFinset.filter (fun e => e.toFinset ⊆ Sᶜ)
  let B :=S.biUnion (fun v => G.incidenceFinset v)
  have hcover:G.edgeFinset ⊆ A ∪ B:=by
    intro e he
    by_cases h :e.toFinset ⊆ Sᶜ
    · exact mem_union_left _ (mem_filter.mpr ⟨he,h⟩)
    · obtain ⟨x,hxe,hx⟩ :=not_subset.mp h
      have hxS:x ∈ S:=by simpa only [mem_compl,not_not] using hx
      apply mem_union_right
      apply mem_biUnion.mpr
      refine ⟨x,hxS,?_⟩
      rw [G.incidenceFinset_eq_filter]
      exact mem_filter.mpr ⟨he,by simpa using hxe⟩
  have hA:A.card= (G.induce (S:Set V)ᶜ).edgeFinset.card:=by
    have h :=congrArg fsCard (G.map_edgeFinset_induce (s:= (S:Set V)ᶜ))
    simp only [card_map] at h
    have heq:G.edgeFinset ∩ ((S:Set V)ᶜ).toFinset.sym2=A:=by
      simp [A,G.filter_edgeFinset_toFinset_subset]
    rw [heq] at h
    exact h.symm
  have hB:B.card ≤ ∑ v ∈ S,G.degree v :=by
    simpa only [G.card_incidenceFinset_eq_degree] using
      (card_biUnion_le:B.card ≤ ∑ v ∈ S,(G.incidenceFinset v).card)
  exact (card_le_card hcover).trans ((card_union_le A B).trans (by omega))
theorem rU
    {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) (d:ℕ)
    (hd: ∀ v ∈ S,G.degree v ≤ d) :
    G.edgeFinset.card ≤ (G.induce (S:Set V)ᶜ).edgeFinset.card+S.card*d:=by
  have hsum: (∑ v ∈ S,G.degree v) ≤ S.card*d:=by
    calc
      (∑ v ∈ S,G.degree v) ≤ ∑ _v ∈ S,d:=sum_le_sum hd
      _=S.card*d:=by simp
  exact (uU G S).trans (by omega)
theorem ze (r a b s N:ℕ)
    (ha:r < a) (hb:r < b) (hs:s ≤ 1) (hN:a+b+s=N) :
    (r+1) ^ 2*a+a^2+ ((r+1) ^ 2*b+b^2) +
      (r+1) * (s*N) ≤ (r+1) ^ 2*N+N^2:=by
  have hra:r+1 ≤ a:=ha
  have hrb:r+1 ≤ b:=hb
  have h1:=natMLMR b hra
  have h2:=natMLMR a hrb
  interval_cases s <;> nlinarith
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem uw {V:Type*} [Fintype V]
    [DecidableEq V] (G:SimpleGraph V) (hcard:3 ≤ ftCard V)
    (hG: ¬ qh G) :
    ∃ A B S :Finset V,A.Nonempty ∧ B.Nonempty ∧ Disjoint A B ∧
      Disjoint A S ∧ Disjoint B S ∧ A ∪ B ∪ S=univ ∧ S.card ≤ 1 ∧
      ∀ a ∈ A,∀ b ∈ B,¬ G.Adj a b:=by
  classical
  have hex: ∃ S:Finset V,S.card ≤ 1 ∧ ¬ (G.induce (S:Set V)ᶜ).Preconnected:=by
    by_cases hc:G.Connected
    · have hv: ∃ v:V,¬ (G.induce ({v}ᶜ:Set V)).Connected:=by
        by_contra! h
        exact hG ⟨hcard,hc,h⟩
      obtain ⟨v,hv⟩ :=hv
      refine ⟨{v},by simp,?_⟩
      rw [Finset.coe_singleton]
      intro hp
      have hn:0 < ftCard ({v}ᶜ:Set V) :=by
        rw [Fintype.card_compl_set,Set.card_singleton]
        omega
      let:Nonempty ({v}ᶜ:Set V) :=ftCPI.mp hn
      exact hv ⟨hp⟩
    · refine ⟨∅,by simp,?_⟩
      rw [Finset.coe_empty,Set.compl_empty]
      intro hp
      let:Nonempty V :=ftCPI.mp (by omega)
      exact hc ⟨(G.induceUnivIso.preconnected_iff).mp hp⟩
  obtain ⟨S,hS,hdisc⟩ :=hex
  obtain ⟨A,B,hA,hB,hAB,hAS,hBS,hcover,hcross⟩ :=
    rk G S hdisc
  exact ⟨A,B,S,hA,hB,hAB,hAS,hBS,hcover,hS,hcross⟩
theorem tp {V:Type*} [Fintype V] [DecidableEq V]
    (A B S:Finset V) (hAB:Disjoint A B) (hAS:Disjoint A S)
    (hBS:Disjoint B S) (hcover:A ∪ B ∪ S=univ) :
    A.card+B.card+S.card=ftCard V :=by
  have h :=congrArg fsCard hcover
  rwa [card_union_of_disjoint (Finset.disjoint_union_left.mpr ⟨hAS,hBS⟩),
    card_union_of_disjoint hAB,card_univ] at h
end Erdos556
namespace Erdos556
open SimpleGraph Finset
private theorem yu (r N e:ℕ) (hN:N ≤ r)
    (he:2*e ≤ N*N) : (r+1) * e ≤ (r+1) ^ 2*N+N^2:=by
  have h1:=natMLMR N hN
  have h2:e ≤ (r+1) * N:=by nlinarith
  have h3:=natMLML (r+1) h2
  nlinarith
private theorem tZ (r a b N e f s:ℕ) (hN:a+b=N)
    (he:e ≤ f+a* (r+1))
    (hf: (r+1) * f ≤ (r+1) * s+ (r+1) ^ 2*b+b^2) :
    (r+1) * e ≤ (r+1) * s+ (r+1) ^ 2*N+N^2:=by
  have h :=natMLML (r+1) he
  nlinarith
universe u
private theorem xP (N:ℕ) :
    ∀ (V:Type u) [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj],ftCard V =N →
      ∀ r :ℕ,2 ≤ r → ∃ P:Finset (Finset V),
        qp G r P ∧
        (r+1) * G.edgeFinset.card ≤
          (r+1) * (∑ A ∈ P,(G.induce (A:Set V)).edgeFinset.card) +
            (r+1) ^ 2*ftCard V + (ftCard V) ^ 2:=by
  induction N using natSIO with
  | h N ih=>
      intro V _ _ G _ hcard r hr
      classical
      by_cases hsmall:ftCard V ≤ r
      · refine ⟨∅,⟨by simp,by simp⟩,?_⟩
        simp only [sum_empty,mul_zero,zero_add]
        apply yu r (ftCard V) G.edgeFinset.card hsmall
        calc
          2*G.edgeFinset.card= ∑ v,G.degree v :=G.sum_degrees_eq_twice_card_edges.symm
          _ ≤ ∑ _v:V,ftCard V :=sum_le_sum fun v _=> (G.degree_lt_card_verts v).le
          _=ftCard V *ftCard V :=by simp
      by_cases htwo:qh G
      · let e :G.induce (↑(univ:Finset V) : Set V) ≃g G :=
          (x8 G _ _ Finset.coe_univ).trans G.induceUnivIso
        have hc:qh (G.induce (↑(univ:Finset V) : Set V)) :=
          htwo.iso e.symm
        have he: (G.induce (↑(univ:Finset V) : Set V)).edgeFinset.card=G.edgeFinset.card:=by
          exact e.card_edgeFinset_eq
        refine ⟨{univ},⟨by simp,?_⟩,?_⟩
        · intro A hA
          have hA':A=univ:=mem_singleton.mp hA
          subst A
          exact ⟨by simpa only [card_univ] using Nat.lt_of_not_ge hsmall,hc⟩
        · simp only [sum_singleton,he]
          omega
      have hsmallside: ∀ A:Finset V,A.Nonempty → A.card < ftCard V →
          (∀ v ∈ A,G.degree v ≤ r +1) → ∃ P :Finset (Finset V),
          qp G r P ∧
          (r+1) * G.edgeFinset.card ≤
            (r+1) * (∑ A ∈ P,(G.induce (A:Set V)).edgeFinset.card) +
              (r+1) ^ 2*ftCard V + (ftCard V) ^ 2:=by
        intro A hA hAlt hdeg
        let T :=Aᶜ
        have hTcard:ftCard (T:Set V) = T.card:=ftCC T
        have hsum:A.card+T.card=ftCard V :=by
          dsimp [T]
          rw [card_compl]
          exact natASOL (card_le_univ A)
        have hTlt:ftCard (T:Set V) < N:=by
          have hpos:=card_pos.mpr hA
          omega
        obtain ⟨P,hP,heP⟩ :=ih (ftCard (T:Set V)) hTlt
          (T:Set V) (G.induce (T:Set V)) rfl r hr
        refine ⟨s4 T P,hP.lift,?_⟩
        rw [vF]
        rw [hTcard] at heP
        have he:=rU G A (r+1) hdeg
        have he':G.edgeFinset.card ≤ (G.induce (T:Set V)).edgeFinset.card+
            A.card* (r+1) :=by
          have heq:= (x8 G (A:Set V)ᶜ (T:Set V)
            (Finset.coe_compl A).symm).card_edgeFinset_eq
          rw [heq] at he
          exact he
        exact tZ r A.card T.card (ftCard V) _ _ _ hsum he' heP
      obtain ⟨A,B,S,hA,hB,hAB,hAS,hBS,hcover,hS,hcross⟩ :=
        uw G (by omega) htwo
      have hsum:=tp A B S hAB hAS hBS hcover
      have hApos:=card_pos.mpr hA
      have hBpos:=card_pos.mpr hB
      by_cases hAsmall:A.card ≤ r
      · apply hsmallside A hA (by omega)
        intro v hv
        have hd:=qR G A B S hcover hcross v hv
        omega
      by_cases hBsmall:B.card ≤ r
      · apply hsmallside B hB (by omega)
        intro v hv
        have hcover':B ∪ A ∪ S=univ:=by rw [union_comm B A];exact hcover
        have hcross': ∀ b ∈ B,∀ a ∈ A,¬ G.Adj b a:=
          fun b hb a ha hadj=> hcross a ha b hb hadj.symm
        have hd:=qR G B A S hcover' hcross' v hv
        omega
      have hAc:ftCard (A:Set V) = A.card:=ftCC A
      have hBc:ftCard (B:Set V) = B.card:=ftCC B
      obtain ⟨P,hP,heP⟩ :=ih (ftCard (A:Set V)) (by omega)
        (A:Set V) (G.induce (A:Set V)) rfl r hr
      obtain ⟨Q,hQ,heQ⟩ :=ih (ftCard (B:Set V)) (by omega)
        (B:Set V) (G.induce (B:Set V)) rfl r hr
      have hPQ:Disjoint (s4 A P) (s4 B Q) :=
        ab hAB P Q (fun _ h=> hP.nonempty h)
      refine ⟨s4 A P ∪ s4 B Q,hP.lift.union hQ.lift ?_,?_⟩
      · intro X hX Y hY
        exact hAB.mono (rP hX) (rP hY)
      · rw [sum_union hPQ,vF,vF]
        rw [hAc] at heP
        rw [hBc] at heQ
        have hedge:=vp G A B S hcover hcross
        have hedge':=natMLML (r+1) hedge
        have hpot:=ze r A.card B.card S.card (ftCard V)
          (by omega) (by omega) hS hsum
        nlinarith only [heP,heQ,hedge',hpot]
theorem zY {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (r:ℕ) (hr:2 ≤ r) :
    ∃ P :Finset (Finset V),qp G r P ∧
      (r+1) * G.edgeFinset.card ≤
        (r+1) * (∑ A ∈ P,(G.induce (A:Set V)).edgeFinset.card) +
          (r+1) ^ 2*ftCard V + (ftCard V) ^ 2:=
  xP (ftCard V) V G rfl r hr
end Erdos556
namespace Erdos556
open SimpleGraph Finset
private theorem yH (r N e s :ℕ) (ε:ℝ)
    (_hε:0 < ε) (hr:2 ≤ ε* (r+1))
    (hN:2* (r+1) ≤ ε*N)
    (he: (r+1) * e ≤ (r+1) * s+ (r+1) ^ 2*N+N^2) :
    (e:ℝ) ≤ s+ε* (N:ℝ) ^ 2:=by
  have heR: ((r:ℝ) + 1) * e ≤ ((r:ℝ) + 1) * s+
      ((r:ℝ) + 1) ^ 2*N+ (N:ℝ) ^ 2:=by exact_mod_cast he
  have h1:=mul_le_mul_of_nonneg_right hN
    (by positivity: (0:ℝ) ≤ ((r:ℝ) + 1) * N)
  have h2:=mul_le_mul_of_nonneg_right hr
    (by positivity: (0:ℝ) ≤ (N:ℝ) ^ 2)
  have hbound: ((r:ℝ) + 1) * e ≤ ((r:ℝ) + 1) * (s+ε* (N:ℝ) ^ 2) :=by
    nlinarith only [heR,h1,h2]
  exact (mul_le_mul_iff_right₀ (by positivity: (0:ℝ) < (r:ℝ) + 1)).mp hbound
theorem wF (ε:ℝ) (hε:0 < ε) (R:ℕ) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj],N₀ ≤ ftCard V →
      ∃ P :Finset (Finset V),qp G R P ∧
        (G.edgeFinset.card:ℝ) ≤
          (∑ A ∈ P,((G.induce (A:Set V)).edgeFinset.card:ℝ)) +
            ε* (ftCard V :ℝ) ^ 2:=by
  obtain ⟨r,hr⟩ :=exists_nat_gt ((R:ℝ) + 2+2/ε)
  have hdiv: (0:ℝ) ≤ 2/ε:=by positivity
  have hrR:R ≤ r:=by exact_mod_cast (show (R:ℝ) ≤ r by linarith)
  have hr2:2 ≤ r:=by exact_mod_cast (show (2:ℝ) ≤ r by linarith)
  have hrε: (2:ℝ) ≤ ε* (r+1) :=by
    have hx:2/ε < (r:ℝ) + 1:=by linarith [natCN R (α:=ℝ)]
    have hx':= (div_lt_iff₀ hε).mp hx
    nlinarith
  obtain ⟨N₀,hN₀⟩ :=exists_nat_gt (2* ((r:ℝ) + 1) / ε)
  refine ⟨N₀,?_⟩
  intro V _ _ G _ hN
  obtain ⟨P,hP,heP⟩ :=zY G r hr2
  have hNreal: (N₀:ℝ) ≤ ftCard V :=by exact_mod_cast hN
  have hNε:2* ((r:ℝ) + 1) ≤ ε*ftCard V :=by
    have hx:= (div_lt_iff₀ hε).mp (hN₀.trans_le hNreal)
    nlinarith
  refine ⟨P,⟨hP.1,fun A hA=> ⟨hrR.trans_lt (hP.2 A hA).1,(hP.2 A hA).2⟩⟩,?_⟩
  have h :=yH r (ftCard V) G.edgeFinset.card
    (∑ A ∈ P,(G.induce (A:Set V)).edgeFinset.card) ε hε hrε hNε heP
  simpa only [Nat.cast_sum] using h
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem zo {V:Type*}
    (G:SimpleGraph V) [DecidableRel G.Adj] (A:Finset V) (d:ℝ)
    (h: ∀ T:Finset A,(((G.induce (A:Set V)).induce (T:Set A)).edgeFinset.card:ℝ) ≤
      d*T.card) :
    ∀ S :Finset V,S ⊆ A → ((G.induce (S:Set V)).edgeFinset.card:ℝ) ≤ d*S.card:=by
  classical
  intro S hS
  let T :Finset A :=S.subtype (fun v => v ∈ A)
  have hmap:T.map (fnSubty (fun v => v ∈ A)) = S:=
    subtype_map_of_mem (fun v hv=> hS hv)
  have hcard:T.card=S.card:=by
    have hc:=congrArg fsCard hmap
    simpa only [card_map] using hc
  let e : (G.induce (A:Set V)).induce (T:Set A) ≃g G.induce (S:Set V) :=
    (sy G A T).trans (x8 G _ _ (congrArg (fun U :Finset V =>
      (U:Set V)) hmap))
  have hT:=h T
  rw [e.card_edgeFinset_eq,hcard] at hT
  exact hT
theorem xs {V:Type*} [Finite V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (P:Finset (Finset V))
    [DecidableRel (rp G P).Adj] (S:Finset V) :
    ((rp G P).induce (S:Set V)).edgeFinset.card ≤
      ∑ A ∈ P,(G.induce (↑(A ∩ S) : Set V)).edgeFinset.card:=by
  classical
  let:=ftOfFin V
  let E (A:Finset V) :=G.edgeFinset.filter (fun e => e.toFinset ⊆ A ∩ S)
  let F := (rp G P).edgeFinset.filter (fun e => e.toFinset ⊆ S)
  have hcover:F ⊆ P.biUnion E :=by
    intro e he
    obtain ⟨he,hS⟩ :=mem_filter.mp he
    rcases e with ⟨⟨u,v⟩⟩
    rw [mem_edgeFinset,mem_edgeSet] at he
    obtain ⟨huv,A,hA,hu,hv⟩ :=he
    apply mem_biUnion.mpr
    refine ⟨A,hA,mem_filter.mpr ⟨?_,?_⟩⟩
    · simpa using huv
    · have huS:u ∈ S:=hS (by simp)
      have hvS:v ∈ S:=hS (by simp)
      simpa only [Sym2.toFinset_mk_eq,insert_subset_iff,singleton_subset_iff,mem_inter]
        using And.intro (And.intro hu huS) (And.intro hv hvS)
  calc
    ((rp G P).induce (S:Set V)).edgeFinset.card=F.card:=
      ((rp G P).card_filter_edgeFinset_toFinset_subset S).symm
    _ ≤ (P.biUnion E).card:=card_le_card hcover
    _ ≤ ∑ A ∈ P,(E A).card:=card_biUnion_le
    _= ∑ A ∈ P,(G.induce (↑(A ∩ S) : Set V)).edgeFinset.card:=by
      apply sum_congr rfl
      intro A _
      exact G.card_filter_edgeFinset_toFinset_subset (A ∩ S)
theorem z0 {V:Type*} [DecidableEq V]
    (P:Finset (Finset V)) (hP: (P:Set (Finset V)).Pairwise Disjoint) (S:Finset V) :
    (∑ A ∈ P,(A ∩ S).card) ≤ S.card:=by
  have hdisj: (P:Set (Finset V)).Pairwise fun A B=> Disjoint (A ∩ S) (B ∩ S) :=by
    intro A hA B hB hAB
    exact (hP hA hB hAB).mono (inter_subset_left) (inter_subset_left)
  rw [← card_biUnion hdisj]
  apply card_le_card
  intro v hv
  obtain ⟨A,_,hvA⟩ :=mem_biUnion.mp hv
  exact (mem_inter.mp hvA).2
theorem z5 {V:Type*} [Finite V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (P:Finset (Finset V))
    [DecidableRel (rp G P).Adj]
    (hP: (P:Set (Finset V)).Pairwise Disjoint) (d:ℝ) (hd:0 ≤ d)
    (h: ∀ A ∈ P,∀ S:Finset V,S ⊆ A →
      ((G.induce (S:Set V)).edgeFinset.card:ℝ) ≤ d*S.card) :
    ∀ S :Finset V,(((rp G P).induce (S:Set V)).edgeFinset.card:ℝ) ≤ d*S.card:=by
  classical
  let:=ftOfFin V
  intro S
  have hcard: (∑ A ∈ P,((A ∩ S).card:ℝ)) ≤ S.card:=by
    exact_mod_cast z0 P hP S
  calc
    (((rp G P).induce (S:Set V)).edgeFinset.card:ℝ) ≤
        ∑ A ∈ P,((G.induce (↑(A ∩ S) : Set V)).edgeFinset.card:ℝ) :=by
      exact_mod_cast xs G P S
    _ ≤ ∑ A ∈ P,d* (A ∩ S).card:=by
      apply sum_le_sum
      intro A hA
      exact h A hA (A ∩ S) inter_subset_left
    _=d* ∑ A ∈ P,((A ∩ S).card:ℝ) := (mul_sum _ _ _).symm
    _ ≤ d*S.card:=mul_le_mul_of_nonneg_left hcard hd
end Erdos556
namespace Erdos556
open SimpleGraph Finset
open scoped Classical in
theorem xK (ε:ℝ) (hε:0 < ε) :
    ∃ N₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (k:ℕ),
      N₀ ≤ ftCard V → ftCard V ≤ 16*k →
      (∀ (w:V) (c:G.Walk w w),c.IsCycle → Odd c.length → c.length ≤ 2*k) →
      ∃ (B F :SimpleGraph V) (S:Finset V),
        B ≤ G ∧ F ≤ G ∧ B.Colorable 2 ∧
        (∀ u v,B.Adj u v → u ∉ S ∧ v ∉ S) ∧
        (∀ u v,F.Adj u v → u ∈ S ∧ v ∈ S) ∧
        (G.edgeFinset.card:ℝ) ≤ B.edgeFinset.card+F.edgeFinset.card+
          ε* (ftCard V :ℝ) ^ 2 ∧
        (∀ A :Finset V,((F.induce (A:Set V)).edgeFinset.card:ℝ) ≤
          ((k:ℝ) + ε*ftCard V) * A.card) :=by
  obtain ⟨R,hR⟩ :=xz ε hε
  obtain ⟨N₀,hN₀⟩ :=wF ε hε R
  refine ⟨N₀,?_⟩
  intro V _ _ G _ k hN hk ho
  classical
  obtain ⟨P,hP,heP⟩ :=hN₀ G hN
  let Q :Finset (Finset V) :=P.filter (fun A => (G.induce (A:Set V)).Colorable 2)
  let T :Finset (Finset V) :=P.filter (fun A => ¬ (G.induce (A:Set V)).Colorable 2)
  let S :Finset V :=T.biUnion id
  let B :=rp G Q
  let F :=rp G T
  have hQsub:Q ⊆ P:=filter_subset _ _
  have hTsub:T ⊆ P:=filter_subset _ _
  have hQ: (Q:Set (Finset V)).Pairwise Disjoint:=hP.1.mono hQsub
  have hT: (T:Set (Finset V)).Pairwise Disjoint:=hP.1.mono hTsub
  have hB:B.Colorable 2 :=a1 G Q 2 hQ
    (fun A hA=> (mem_filter.mp hA).2)
  have hQT:Disjoint Q T:=by
    rw [fsDL]
    intro A hAQ hAT
    exact (mem_filter.mp hAT).2 (mem_filter.mp hAQ).2
  have hQTunion:Q ∪ T=P:=filter_union_filter_not_eq _ _
  have heq:B.edgeFinset.card+F.edgeFinset.card=
      ∑ A ∈ P,(G.induce (A:Set V)).edgeFinset.card:=by
    rw [xE G Q hQ,xE G T hT,
      ← sum_union hQT,hQTunion]
  refine ⟨B,F,S,ah G Q,ah G T,hB,?_,?_,?_,?_⟩
  · intro u v huv
    obtain ⟨_,A,hA,hu,hv⟩ :=huv
    have hoff (x:V) (hx:x ∈ A) : x ∉ S:=by
      intro hxS
      obtain ⟨C,hC,hxC⟩ :=mem_biUnion.mp hxS
      have hAC:A ≠ C:=by
        intro he
        subst C
        exact fsDL.mp hQT hA hC
      exact fsDL.mp (hP.1 (hQsub hA) (hTsub hC) hAC) hx hxC
    exact ⟨hoff u hu,hoff v hv⟩
  · intro u v huv
    obtain ⟨_,A,hA,hu,hv⟩ :=huv
    exact ⟨mem_biUnion.mpr ⟨A,hA,hu⟩,mem_biUnion.mpr ⟨A,hA,hv⟩⟩
  · have heqR: (B.edgeFinset.card:ℝ) + F.edgeFinset.card=
        ∑ A ∈ P,((G.induce (A:Set V)).edgeFinset.card:ℝ) :=by exact_mod_cast heq
    rw [heqR]
    exact heP
  · apply z5 G T hT
      ((k:ℝ) + ε*ftCard V) (by positivity)
    intro A hA
    have hAR:R < A.card:= (hP.2 A (hTsub hA)).1
    have hAc:ftCard (A:Set V) = A.card:=ftCC A
    have hAk:ftCard (A:Set V) ≤ 16*k:=by
      rw [hAc]
      exact (card_le_univ A).trans hk
    have hoA (w: (A:Set V)) (c: (G.induce (A:Set V)).Walk w w)
        (hc:c.IsCycle) (hcodd:Odd c.length) : c.length ≤ 2*k:=by
      let f :G.induce (A:Set V) ↪g G :=sgInduce (A:Set V)
      have h :=ho (f w) (c.map f.toHom) (hc.map f.injective)
        (by simpa only [wkLM] using hcodd)
      simpa only [wkLM] using h
    have hd:=hR (G.induce (A:Set V)) k (by omega) hAk
      (hP.2 A (hTsub hA)).2 (mem_filter.mp hA).2 hoA
    apply zo G A
    intro U
    apply (hd U).trans
    gcongr
    rw [hAc]
    exact_mod_cast card_le_univ A
end Erdos556
namespace Erdos556
open SimpleGraph Finset
open scoped Classical in
theorem vd (ε:ℝ) (hε:0 < ε) :
    ∃ n₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (G:SimpleGraph V) [DecidableRel G.Adj] (n:ℕ),
      n₀ ≤ n → Odd n → n ≤ ftCard V → ftCard V ≤ 7 *n →
      (¬ cycleGraph n ⊑ G) →
      ∃ (B F :SimpleGraph V) (T:Finset V),
        B ≤ G ∧ F ≤ G ∧ B.Colorable 2 ∧
        (∀ u v,B.Adj u v → u ∉ T ∧ v ∉ T) ∧
        (∀ u v,F.Adj u v → u ∈ T ∧ v ∈ T) ∧
        (G.edgeFinset.card:ℝ) ≤ B.edgeFinset.card+F.edgeFinset.card+
          ε* (ftCard V :ℝ) ^ 2 ∧
        (∀ A :Finset V,((F.induce (A:Set V)).edgeFinset.card:ℝ) ≤
          ((n:ℝ) / 2+ε*ftCard V) * A.card) :=by
  obtain ⟨D,hDreal⟩ :=exists_nat_gt (2/ε)
  have hD:0 < D:=by
    have hp:0 < 2/ε:=by positivity
    have hpD:0 < (D:ℝ) :=hp.trans hDreal
    exact_mod_cast hpD
  have hDε:2 ≤ ε* (D:ℝ) :=by
    have h := (div_lt_iff₀ hε).mp hDreal
    nlinarith
  obtain ⟨N₁,K,hspec⟩ :=uR D hD
  obtain ⟨N₂,hdecomp⟩ :=xK (ε/2) (by positivity)
  obtain ⟨M,hM⟩ :=exists_nat_ge ((K:ℝ) / ε)
  have hKM: (K:ℝ) ≤ ε*M:=by
    have h := (div_le_iff₀ hε).mp hM
    nlinarith
  let R :=max N₁ N₂
  refine ⟨max (D* (R+1)) (max K (max M 8)),?_⟩
  intro V _ _ G _ n hn hodd hnN hNn hno
  classical
  let N :=ftCard V
  let q :=N/D
  have hn3:3 ≤ n:=by omega
  have hnK:K ≤ n:=by omega
  have hKN: (K:ℝ) ≤ ε*N:=by
    have hMN:M ≤ N:=by omega
    exact hKM.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hMN) hε.le)
  have hqN: (D:ℝ) * q ≤ N:=by exact_mod_cast (Nat.mul_div_le N D)
  have hqsmall:2* (q:ℝ) ≤ ε*N:=by
    have h₁:=mul_le_mul_of_nonneg_right hDε (show 0 ≤ (q:ℝ) by positivity)
    have h₂:=mul_le_mul_of_nonneg_left hqN hε.le
    nlinarith only [h₁,h₂]
  have hpruneLoss: (q:ℝ) * N ≤ ε/2* (N:ℝ) ^ 2:=by
    have h :=mul_le_mul_of_nonneg_right hqsmall (show 0 ≤ (N:ℝ) by positivity)
    nlinarith only [h]
  obtain ⟨S,hprune,hdegree⟩ :=a4 G (q:ℝ)
  have hcardS:ftCard (S:Set V) = S.card:=by
    calc
      ftCard (S:Set V) = (S:Set V).ncard:=natCEFC.symm
      _=S.card:=stNCF S
  have hSN:S.card ≤ N:=card_le_univ S
  have hcoreLoss: (G.edgeFinset.card:ℝ) ≤ (G.induce (S:Set V)).edgeFinset.card+
      ε/2* (N:ℝ) ^ 2:=by
    have hnonneg:0 ≤ (q:ℝ) * S.card:=by positivity
    change (G.edgeFinset.card:ℝ) - (q:ℝ) * N ≤
      ((G.induce (S:Set V)).edgeFinset.card:ℝ) - (q:ℝ) * S.card at hprune
    linarith
  by_cases hSempty:S= ∅
  · have hezero: (G.induce (S:Set V)).edgeFinset.card=0:=by
      have h := (G.induce (S:Set V)).card_edgeFinset_le_card_choose_two
      have hSc:S.card=0:=by rw [hSempty,card_empty]
      rw [hcardS,hSc] at h
      exact Nat.eq_zero_of_le_zero (by simpa only [Nat.choose_zero_succ] using h)
    rw [hezero,natCZ,zero_add] at hcoreLoss
    refine ⟨⊥,⊥,∅,bot_le,bot_le,?_,?_,?_,?_,?_⟩
    · exact ⟨{ toFun:=fun _ => (0:Fin 2),map_rel':=fun h => h.elim}⟩
    · intro u v h
      exact h.elim
    · intro u v h
      exact h.elim
    · have hbot:natCard (⊥ : SimpleGraph V).edgeSet=0:=by
        rw [edgeSet_bot]
        simp
      have hnonneg:0 ≤ ε* (N:ℝ) ^ 2:=by positivity
      have hres: (G.edgeFinset.card:ℝ) ≤ ε* (N:ℝ) ^ 2:=by linarith
      simpa only [q7,hbot,natCZ,zero_add] using hres
    · intro A
      have he:natCard (((⊥ : SimpleGraph V).induce (A:Set V)).edgeSet) = 0:=by
        change natCard (⊥ : SimpleGraph (A:Set V)).edgeSet=0
        rw [edgeSet_bot]
        simp
      simpa only [q7,he,natCZ] using
        (show (0:ℝ) ≤ ((n:ℝ) / 2+ε*ftCard V) * A.card by positivity)
  · have hqR:R+1 ≤ q:=by
      apply (natLDIML hD).mpr
      have hnR:D* (R+1) ≤ n:=by omega
      exact (by simpa only [natMC] using hnR.trans hnN)
    obtain ⟨s,hs⟩ :=nonempty_iff_ne_empty.mpr hSempty
    have hdegNat (v: (S:Set V)) : q+1 ≤ (G.induce (S:Set V)).degree v :=by
      have h :q < (G.induce (S:Set V)).degree v :=by exact_mod_cast hdegree v
      omega
    have hSlarge:R ≤ ftCard (S:Set V) :=by
      have h₁:=hdegNat ⟨s,hs⟩
      have h₂:= (G.induce (S:Set V)).degree_lt_card_verts ⟨s,hs⟩
      omega
    have hscale:ftCard (S:Set V) ≤ D* (q+1) :=by
      rw [hcardS]
      exact hSN.trans (Nat.lt_mul_div_succ N hD).le
    have hnoS: ¬ cycleGraph n ⊑ G.induce (S:Set V) :=fun h =>
      hno (h.trans (Embedding.induce (S:Set V)).isContained)
    have hcut:=hspec (G.induce (S:Set V)) (q+1) n
      (by dsimp only [R] at hSlarge;omega) hscale hdegNat hn3 hodd hnK hnoS
    let k := (n+K) / 2
    have hkN:ftCard (S:Set V) ≤ 16*k:=by
      rw [hcardS]
      have h :7*n ≤ 16*k:=by dsimp only [k];omega
      exact hSN.trans (hNn.trans h)
    have hoddBound (v: (S:Set V)) (w: (G.induce (S:Set V)).Walk v v)
        (hw:w.IsCycle) (ho:Odd w.length) : w.length ≤ 2*k:=by
      have h :=hcut v w hw ho
      dsimp only [k]
      omega
    obtain ⟨B,F,T,hBG,hFG,hBcol,hBoff,hFon,hE,hFden⟩ :=
      hdecomp (G.induce (S:Set V)) k (by dsimp only [R] at hSlarge;omega) hkN hoddBound
    let f : (S:Set V) ↪ V:=fnSubty _
    have hBmap:B.map f ≤ G := (map_le_iff_le_comap f B G).mpr hBG
    have hFmap:F.map f ≤ G := (map_le_iff_le_comap f F G).mpr hFG
    refine ⟨B.map f,F.map f,T.map f,hBmap,hFmap,hBcol.map f,
      tW B f T hBoff,ac F f T hFon,?_,?_⟩
    · have hBcard:=card_edgeFinset_map f B
      have hFcard:=card_edgeFinset_map f F
      simp only [q7] at hBcard hFcard ⊢
      rw [hBcard,hFcard]
      have hSNreal: (S.card:ℝ) ≤ N:=by exact_mod_cast hSN
      have hsq: (S.card:ℝ) ^ 2 ≤ (N:ℝ) ^ 2:=by nlinarith
      have herror:=mul_le_mul_of_nonneg_left hsq (show 0 ≤ ε /2 by positivity)
      rw [hcardS] at hE
      simp only [q7] at hE hcoreLoss
      change (natCard G.edgeSet:ℝ) ≤ (natCard B.edgeSet:ℝ) + natCard F.edgeSet+ε* (N:
        ℝ) ^ 2
      linarith
    · have hkReal:2* (k:ℝ) ≤ (n:ℝ) + K:=by
        exact_mod_cast (show 2 *k ≤ n+K from Nat.mul_div_le (n+K) 2)
      have hSNreal: (ftCard (S:Set V) : ℝ) ≤ N:=by rw [hcardS];exact_mod_cast hSN
      have hmul:=mul_le_mul_of_nonneg_left hSNreal hε.le
      have hcoef: (k:ℝ) + ε/2*ftCard (S:Set V) ≤ (n:ℝ) / 2+ε*N:=by
        nlinarith only [hkReal,hKN,hmul]
      have hden:=x2 F f
        ((k:ℝ) + ε/2*ftCard (S:Set V)) (by positivity) hFden
      intro A
      have hres:= (hden A).trans (mul_le_mul_of_nonneg_right hcoef (by positivity))
      simpa only [q7] using hres
end Erdos556
namespace Erdos556
open SimpleGraph
instance q4.graphDecidableAdj {V:Type*} [DecidableEq V]
    (c:q4 V) (i:Fin 3) : DecidableRel (c.graph i).Adj:=
  fun u v=> inferInstanceAs (Decidable (u ≠ v ∧ c.colour u v=i))
end Erdos556
namespace Erdos556
open Finset
def qV (p q :q1) (i:Fin 3) : Prop:=
  (p i =some false ∧ q i =some true) ∨ (p i =some true ∧ q i =some false)
instance (p q :q1) (i:Fin 3) : Decidable (qV p q i) :=
  inferInstanceAs (Decidable ((p i =some false ∧ q i =some true) ∨
    (p i =some true ∧ q i =some false)))
def q5 (p q :q1) (i:Fin 3) : Prop:=
  qV p q i ∧ ∀ j,j ≠ i → ¬ qV p q j
instance (p q :q1) (i:Fin 3) : Decidable (q5 p q i) :=
  inferInstanceAs (Decidable (qV p q i ∧ ∀ j,j ≠ i → ¬ qV p q j))
def uf (p:Fin 4 → q1) (k:Fin 3 → Fin 3) : Prop:=
  q5 (p 0) (p 2) (k 0) ∧ q5 (p 1) (p 3) (k 0) ∧
  q5 (p 0) (p 1) (k 1) ∧ q5 (p 2) (p 3) (k 1)
def uq (p:Fin 4 → q1) (k:Fin 3 → Fin 3) : Prop:=
  q5 (p 0) (p 2) (k 0) ∧ q5 (p 0) (p 3) (k 0) ∧
  q5 (p 1) (p 2) (k 0) ∧ q5 (p 1) (p 3) (k 0) ∧
  q5 (p 0) (p 1) (k 1) ∧ q5 (p 2) (p 3) (k 2)
instance (p:Fin 4 → q1) (k:Fin 3 → Fin 3) : Decidable (uf p k) :=
  inferInstanceAs (Decidable (q5 (p 0) (p 2) (k 0) ∧
    q5 (p 1) (p 3) (k 0) ∧ q5 (p 0) (p 1) (k 1) ∧
    q5 (p 2) (p 3) (k 1)))
instance (p:Fin 4 → q1) (k:Fin 3 → Fin 3) : Decidable (uq p k) :=
  inferInstanceAs (Decidable (q5 (p 0) (p 2) (k 0) ∧
    q5 (p 0) (p 3) (k 0) ∧ q5 (p 1) (p 2) (k 0) ∧
    q5 (p 1) (p 3) (k 0) ∧ q5 (p 0) (p 1) (k 1) ∧
    q5 (p 2) (p 3) (k 2)))
end Erdos556
namespace Erdos556
open SimpleGraph Finset
structure q2 {V:Type*} (c:q4 V) (E D :ℝ) where
  bipartite:Fin 3 → SimpleGraph V
  sparse:Fin 3 → SimpleGraph V
  stars:Fin 3 → Finset V
  bicolouring: ∀ i,(bipartite i).Coloring Bool
  bipartite_le: ∀ i,bipartite i ≤ c.graph i
  sparse_le: ∀ i,sparse i ≤ c.graph i
  bipartite_off: ∀ i u v,(bipartite i).Adj u v → u ∉ stars i ∧ v ∉ stars i
  sparse_on: ∀ i u v,(sparse i).Adj u v → u ∈ stars i ∧ v ∈ stars i
  edge_loss: ∀ i,(natCard (c.graph i).edgeSet:ℝ) ≤
    natCard (bipartite i).edgeSet+natCard (sparse i).edgeSet+E
  hereditary_density: ∀ i (A:Finset V),(natCard ((sparse i).induce (A:Set V)).edgeSet:ℝ) ≤
    D*A.card
theorem wZ (ε:ℝ) (hε:0 < ε) :
    ∃ n₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (c:q4 V) (n:ℕ),
      n₀ ≤ n → Odd n → n ≤ ftCard V → ftCard V ≤ 7 *n →
      (∀ i,¬ cycleGraph n ⊑ c.graph i) →
      Nonempty (q2 c (ε* (ftCard V :ℝ) ^ 2)
        ((n:ℝ) / 2+ε*ftCard V)) :=by
  obtain ⟨n₀,hn₀⟩ :=vd ε hε
  refine ⟨n₀,?_⟩
  intro V _ _ c n hn hodd hnN hNn hno
  classical
  choose B F T hBG hFG hcol hBoff hFon he hden using
    fun i => hn₀ (c.graph i) n hn hodd hnN hNn (hno i)
  refine ⟨{
    bipartite:=B
    sparse:=F
    stars:=T
    bicolouring:=fun i => (B i).recolorOfEquiv finTwoEquiv (Classical.choice (hcol i))
    bipartite_le:=hBG
    sparse_le:=hFG
    bipartite_off:=hBoff
    sparse_on:=hFon
    edge_loss:= ?_
    hereditary_density:= ?_}⟩
  · intro i
    simpa only [q7] using he i
  · intro i A
    simpa only [q7] using hden i A
def q2.profile {V:Type*} [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) (v:V) : q1:=
  fun i => if v ∈ h.stars i then none else some (h.bicolouring i v)
def q2.qa {V:Type*} [Fintype V] [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) (p:q1) :
      Finset V :=
  univ.filter (fun v => h.profile v =p)
def q2.retained {V:Type*}
    {c:q4 V} {E D :ℝ} (h:q2 c E D) : SimpleGraph V :=
  ⨆ i,h.bipartite i ⊔ h.sparse i
def q2.missing {V:Type*}
    {c:q4 V} {E D :ℝ} (h:q2 c E D) : SimpleGraph V :=
  h.retainedᶜ
theorem q2.ry {V:Type*} [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D)
    (i:Fin 3) (u v :V) (huv: (h.bipartite i).Adj u v) :
    qV (h.profile u) (h.profile v) i :=by
  have hu:= (h.bipartite_off i u v huv).1
  have hv:= (h.bipartite_off i u v huv).2
  have hbits:= (h.bicolouring i).valid huv
  simp only [qV,profile,if_neg hu,if_neg hv,Option.some.injEq]
  cases huval:h.bicolouring i u <;> cases hvval:h.bicolouring i v <;> simp_all
theorem q2.z1 {V:Type*} [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D)
    (i:Fin 3) (u v :V) (huv: (h.sparse i).Adj u v) :
    h.profile u i=none ∧ h.profile v i=none:=by
  have hu:= (h.sparse_on i u v huv).1
  have hv:= (h.sparse_on i u v huv).2
  simp only [profile,if_pos hu,if_pos hv,and_self]
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem q2.r3 {V:Type*} [Fintype V] [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) (p:q1) (v:
      V) :
    v ∈ h.qa p ↔ h.profile v =p:=by
  simp only [qa,mem_filter,mem_univ,true_and]
theorem q2.xF {V:Type*} [Fintype V] [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) :
    (∑ p,(h.qa p).card) = ftCard V :=aE h.profile
theorem q2.aK {V:Type*} [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) (v:V) (i:Fin 3) :
    h.profile v i=none ↔ v ∈ h.stars i :=by
  by_cases hv:v ∈ h.stars i <;> simp [profile,hv]
theorem q2.tQ {V:Type*} [Fintype V] [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) :
    (∑ i,(h.stars i).card) = ∑ p,q3 p * (h.qa p).card:=by
  classical
  have hstar (i:Fin 3) : (h.stars i).card= ∑ v,if h.profile v i=none then 1 else 0 :=by
    rw [sum_boole]
    congr 1
    ext v
    simp only [mem_filter,mem_univ,true_and,h.aK]
  calc
    _= ∑ i,∑ v,if h.profile v i=none then 1 else 0 :=sum_congr rfl (fun i _=> hstar i)
    _= ∑ v,∑ i,if h.profile v i=none then 1 else 0 :=sum_comm
    _= ∑ v,q3 (h.profile v) :=by
      apply sum_congr rfl
      intro v _
      rw [q3,sum_boole]
      simp only [Nat.cast_id]
    _= ∑ p,(h.qa p).card*q3 p :=vn h.profile
      q3
    _=_:=sum_congr rfl (fun _ _=> natMC _ _)
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem vZ {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] :
    G.edgeFinset.card+Gᶜ.edgeFinset.card= (ftCard V).choose 2 :=by
  classical
  have hdisj:Disjoint G.edgeFinset Gᶜ.edgeFinset:=by
    rw [fsDL]
    intro e he hec
    rcases e with ⟨⟨u,v⟩⟩
    have hG:G.Adj u v:=by simpa using he
    have hc:Gᶜ.Adj u v:=by simpa using hec
    have hc':u ≠ v ∧ ¬ G.Adj u v:=by simpa only [compl_adj] using hc
    exact hc'.2 hG
  have hunion:G.edgeFinset ∪ Gᶜ.edgeFinset= (⊤ : SimpleGraph V).edgeFinset:=by
    ext e
    rcases e with ⟨⟨u,v⟩⟩
    simp only [mem_union,mem_edgeFinset,mem_edgeSet,top_adj,compl_adj]
    constructor
    · rintro (h | h)
      · exact h.ne
      · exact h.1
    · intro hne
      by_cases h :G.Adj u v
      · exact orInl h
      · exact orInr ⟨hne,h⟩
  calc
    G.edgeFinset.card+Gᶜ.edgeFinset.card= (G.edgeFinset ∪ Gᶜ.edgeFinset).card:=
      (card_union_of_disjoint hdisj).symm
    _= (ftCard V).choose 2 :=by rw [hunion,card_edgeFinset_top_eq_card_choose_two]
end Erdos556
namespace Erdos556
open SimpleGraph Finset
open scoped Classical in
theorem c8 {V I :Type*} [Fintype V] [DecidableEq V] [Fintype I]
    (G:I → SimpleGraph V) : (⨆ i,G i).edgeFinset=univ.biUnion (fun i => (G i).edgeFinset) :=by
  ext e
  simp only [mem_edgeFinset,edgeSet_iSup,Set.mem_iUnion,mem_biUnion,mem_univ,true_and]
theorem wD {V I :Type*} [Finite V] [Fintype I]
    (G:I → SimpleGraph V) (hdis: ∀ i j,i ≠ j → Disjoint (G i) (G j)) :
    natCard (⨆ i,G i).edgeSet= ∑ i,natCard (G i).edgeSet:=by
  classical
  let:=ftOfFin V
  have hd: ((univ:Finset I) : Set I).Pairwise (fun i j=> Disjoint (G i).edgeFinset (G
    j).edgeFinset) :=by
    intro i _ j _ hij
    exact sgDE.mpr (hdis i j hij)
  have h : (⨆ i,G i).edgeFinset.card= ∑ i,(G i).edgeFinset.card:=by
    rw [c8,card_biUnion hd]
  simpa only [q7] using h
theorem yD {V:Type*} [Finite V]
    (G H :SimpleGraph V) (hdis:Disjoint G H) :
    natCard (G ⊔ H).edgeSet=natCard G.edgeSet+natCard H.edgeSet:=by
  classical
  let:=ftOfFin V
  have h : (G ⊔ H).edgeFinset.card=G.edgeFinset.card+H.edgeFinset.card:=by
    rw [edgeFinset_sup,card_union_of_disjoint (sgDE.mpr hdis)]
  simpa only [q7] using h
theorem v1 {V:Type*} [Finite V]
    (G:SimpleGraph V) : natCard G.edgeSet+natCard Gᶜ.edgeSet=natCard (⊤ : SimpleGraph
      V).edgeSet:=by
  classical
  let:=ftOfFin V
  have h :=vZ G
  have ht:=card_edgeFinset_top_eq_card_choose_two (V:=V)
  simp only [q7] at h ht
  exact h.trans ht.symm
theorem q4.zs {V:Type*} (c:q4 V)
    (i j :Fin 3) (hij:i ≠ j) : Disjoint (c.graph i) (c.graph j) :=by
  apply SimpleGraph.disjoint_left.mpr
  intro u v hi hj
  exact hij (hi.2.symm.trans hj.2)
theorem q4.aF {V:Type*} (c:q4 V) :
    (⨆ i,c.graph i) = ⊤ :=by
  ext u v
  rw [iSup_adj,top_adj]
  constructor
  · rintro ⟨i,hi⟩
    exact hi.1
  · intro huv
    exact ⟨c.colour u v,huv,rfl⟩
theorem q4.bz {V:Type*} [Finite V]
    (c:q4 V) :
    (∑ i,natCard (c.graph i).edgeSet) = natCard (⊤ : SimpleGraph V).edgeSet:=by
  classical
  let:=ftOfFin V
  have h :=wD c.graph c.zs
  rw [c.aF] at h
  exact h.symm
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem q2.co {V:Type*}
    {c:q4 V} {E D :ℝ} (h:q2 c E D) (i:Fin 3) :
    Disjoint (h.bipartite i) (h.sparse i) :=by
  apply SimpleGraph.disjoint_left.mpr
  intro u v hB hF
  exact (h.bipartite_off i u v hB).1 (h.sparse_on i u v hF).1
theorem q2.zD {V:Type*} [Finite V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) :
    natCard h.retained.edgeSet=
      ∑ i,(natCard (h.bipartite i).edgeSet+natCard (h.sparse i).edgeSet) :=by
  classical
  let:=ftOfFin V
  have hdis (i j :Fin 3) (hij:i ≠ j) :
      Disjoint (h.bipartite i ⊔ h.sparse i) (h.bipartite j ⊔ h.sparse j) :=
    (c.zs i j hij).mono (sup_le (h.bipartite_le i) (h.sparse_le i))
      (sup_le (h.bipartite_le j) (h.sparse_le j))
  dsimp only [retained]
  rw [wD _ hdis]
  apply sum_congr rfl
  intro i _
  exact yD _ _ (h.co i)
theorem q2.v9 {V:Type*} [Finite V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) :
    (natCard h.missing.edgeSet:ℝ) ≤ 3*E:=by
  classical
  let:=ftOfFin V
  have hcol: (∑ i,(natCard (c.graph i).edgeSet:ℝ)) = natCard (⊤ : SimpleGraph V).edgeSet:=by
    exact_mod_cast c.bz
  have hret: (natCard h.retained.edgeSet:ℝ) =
      ∑ i,((natCard (h.bipartite i).edgeSet:ℝ) + natCard (h.sparse i).edgeSet) :=by
    exact_mod_cast h.zD
  have hcomp: (natCard h.retained.edgeSet:ℝ) + natCard h.missing.edgeSet=
      natCard (⊤ : SimpleGraph V).edgeSet:=by
    exact_mod_cast v1 h.retained
  have hsum: (∑ i,(natCard (c.graph i).edgeSet:ℝ)) ≤
      (∑ i,((natCard (h.bipartite i).edgeSet:ℝ) + natCard (h.sparse i).edgeSet)) + 3*E:=by
    calc
      _ ≤ ∑ i,((natCard (h.bipartite i).edgeSet:ℝ) + natCard (h.sparse i).edgeSet+E) :=
        sum_le_sum (fun i _=> h.edge_loss i)
      _=_:=by rw [sum_add_distrib];simp
  linarith
theorem q2.tU {V:Type*} [Finite V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) (i:Fin 3) :
    (natCard (h.sparse i).edgeSet:ℝ) ≤ D* (h.stars i).card:=by
  classical
  let:=ftOfFin V
  have hsupp: (h.sparse i).support ⊆ (h.stars i :Set V) :=by
    intro u hu
    obtain ⟨v,huv⟩ :=hu
    exact (h.sparse_on i u v huv).1
  have hcount:= (h.sparse i).card_edgeFinset_induce_of_support_subset hsupp
  simp only [q7] at hcount
  have hd:=h.hereditary_density i (h.stars i)
  rw [hcount] at hd
  exact hd
end Erdos556
namespace Erdos556
theorem re: ∀ (p q :q1) (i:Fin 3),
    qV p q i → Disjoint (q0 p) (q0 q) :=by decide
theorem uc: ∀ (p q :q1) (i:Fin 3),
    (q0 p ∩ q0 q).card=1 → ¬ (p i =none ∧ q i =none) :=by decide
theorem xm: ∀ p:q1,q3 p =1 →
    ∃ i,p i=none ∧ ∀ j,p j=none → j=i:=by decide
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem xj {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (B:Finset V) (u:V)
    (h: ∀ v ∈ B,u ≠ v → G.Adj u v) : B.card ≤ G.degree u +1:=by
  classical
  have hsub:B.erase u ⊆ G.neighborFinset u :=by
    intro v hv
    exact (G.mem_neighborFinset u v).mpr (h v (mem_of_mem_erase hv) (mem_erase.mp hv).1.symm)
  have hc:=card_le_card hsub
  rw [card_neighborFinset_eq_degree] at hc
  by_cases hu:u ∈ B
  · rw [card_erase_of_mem hu] at hc
    omega
  · rw [erase_eq_of_notMem hu] at hc
    omega
theorem xb {V:Type*} [Fintype V]
    (G:SimpleGraph V) (A B :Finset V)
    (h: ∀ u ∈ A,∀ v ∈ B,u ≠ v → G.Adj u v) :
    A.card*B.card ≤ 2*natCard G.edgeSet+ftCard V :=by
  classical
  calc
    A.card*B.card= ∑ _u ∈ A,B.card:=by simp
    _ ≤ ∑ u ∈ A,(G.degree u +1) :=
      sum_le_sum (fun u hu=> xj G B u (h u hu))
    _= (∑ u ∈ A,G.degree u) + A.card:=by rw [sum_add_distrib];simp
    _ ≤ (∑ u,G.degree u) + ftCard V :=
      Nat.add_le_add (sum_le_sum_of_subset (subset_univ _)) (card_le_univ A)
    _=_:=by rw [G.sum_degrees_eq_twice_card_edges,q7]
theorem zW {V:Type*} [Finite V]
    (G H :SimpleGraph V) (h:G ≤ H) : natCard G.edgeSet ≤ natCard H.edgeSet:=by
  classical
  let:=ftOfFin V
  have hc:=card_le_card (edgeFinset_mono h)
  simpa only [q7] using hc
theorem t2 {V:Type*} [Finite V]
    (G:SimpleGraph V) (S:Finset V) : natCard (G.induce (S:Set V)).edgeSet ≤ natCard
      G.edgeSet:=by
  classical
  let:=ftOfFin V
  let f := (Embedding.induce (G:=G) (S:Set V)).toCopy.mapEdgeSet
  have h :=ftCLOI f f.injective
  simpa only [← natCEFC] using h
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem yx {V:Type*} [Fintype V] :
    2* (natCard (⊤ : SimpleGraph V).edgeSet:ℝ) + ftCard V =
      (ftCard V :ℝ) ^ 2:=by
  classical
  rw [sb]
  have hd: (∑ u :V,∑ v:V,if u =v then (1:ℝ) else 0) = ftCard V :=by
    simp
  rw [← hd]
  calc
    _= ∑ u:V,∑ v:V,
        ((if (⊤ : SimpleGraph V).Adj u v then (1:ℝ) else 0) +
          if u =v then 1 else 0) :=by simp only [sum_add_distrib]
    _= ∑ _u:V,∑ _v:V,(1:ℝ) :=by
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro v _
      by_cases huv:u=v <;> simp [top_adj,huv]
    _=_:=by simp [pow_two]
def q2.bipartiteUnion {V:Type*}
    {c:q4 V} {E D :ℝ} (h:q2 c E D) :
    SimpleGraph V := ⨆ i,h.bipartite i
theorem q2.vm {V:Type*} [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) :
    h.bipartiteUnion ≤ qJ h.profile:=by
  intro u v huv
  obtain ⟨i,hi⟩ :=iSup_adj.mp huv
  exact re _ _ _ (h.ry i u v hi)
theorem q2.yj {V:Type*}
    [Finite V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) :
    natCard h.bipartiteUnion.edgeSet= ∑ i,natCard (h.bipartite i).edgeSet:=by
  classical
  let:=ftOfFin V
  apply wD
  intro i j hij
  exact (c.zs i j hij).mono (h.bipartite_le i) (h.bipartite_le j)
theorem q2.yE {V:Type*}
    [Fintype V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) :
    (ftCard V :ℝ) ^ 2 ≤ ftCard V +
      2*natCard h.bipartiteUnion.edgeSet+
      2*D* (∑ p,(q3 p :ℝ) * (h.qa p).card) + 6*E:=by
  have hret: (natCard h.retained.edgeSet:ℝ) =
      (natCard h.bipartiteUnion.edgeSet:ℝ) + ∑ i,(natCard (h.sparse i).edgeSet:ℝ) :=by
    have hh:=h.zD
    rw [sum_add_distrib,← h.yj] at hh
    exact_mod_cast hh
  have hf: (∑ i,(natCard (h.sparse i).edgeSet:ℝ)) ≤
      D* (∑ p,(q3 p :ℝ) * (h.qa p).card) :=by
    calc
      _ ≤ ∑ i,D* (h.stars i).card:=sum_le_sum (fun i _=> h.tU i)
      _=D* (∑ i,((h.stars i).card:ℝ)) := (mul_sum _ _ _).symm
      _=_:=by
        congr 1
        exact_mod_cast h.tQ
  have hcomp: (natCard h.retained.edgeSet:ℝ) + natCard h.missing.edgeSet=
      natCard (⊤ : SimpleGraph V).edgeSet:=by
    exact_mod_cast v1 h.retained
  have hm:=h.v9
  have ht:=yx (V:=V)
  linarith
theorem q2.yS {V:Type*}
    [Fintype V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) (n:ℝ) :
    (ftCard V :ℝ) ^ 2-
        qO (fun p => ((h.qa p).card:ℝ)) -
        n* (∑ p,(q3 p :ℝ) * (h.qa p).card) ≤
      ftCard V + (2*D-n) *
        (∑ p,(q3 p :ℝ) * (h.qa p).card) + 6*E:=by
  have hpot:=sY h.profile
  have hle: (natCard h.bipartiteUnion.edgeSet:ℝ) ≤
      natCard (qJ h.profile).edgeSet:=by
    exact_mod_cast zW _ _ h.vm
  have hb:=h.yE
  change 2 * (natCard (qJ h.profile).edgeSet:ℝ) =
    qO (fun p => ((h.qa p).card:ℝ)) at hpot
  nlinarith
theorem q2.wR {V:Type*}
    [Fintype V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) :
    (∑ p,(q3 p :ℝ) * (h.qa p).card) ≤ 3*ftCard V :=by
  have hs: (∑ i,(h.stars i).card) ≤ 3*ftCard V :=by
    calc
      _ ≤ ∑ _i:Fin 3,ftCard V :=sum_le_sum (fun i _=> card_le_univ _)
      _=_:=by simp
  rw [h.tQ] at hs
  exact_mod_cast hs
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem q2.uZ {V:Type*}
    [DecidableEq V] {c:q4 V} {E D :ℝ} (h:q2 c E D)
    (u v :V) (huv:u ≠ v)
    (hinter: (q0 (h.profile u) ∩ q0 (h.profile v)).card=1) :
    h.missing.Adj u v:=by
  rw [missing,compl_adj]
  refine ⟨huv,?_⟩
  intro hret
  obtain ⟨i,hi⟩ :=iSup_adj.mp hret
  rcases hi with hB | hF
  · have hdis:=re _ _ i (h.ry i u v hB)
    have he:q0 (h.profile u) ∩ q0 (h.profile v) = ∅ :=
      Finset.disjoint_iff_inter_eq_empty.mp hdis
    rw [he,card_empty] at hinter
    omega
  · exact uc _ _ i hinter
      (h.z1 i u v hF)
theorem q2.su {V:Type*}
    [Fintype V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) (p q :q1)
    (hpq: (q0 p ∩ q0 q).card=1) :
    ((h.qa p).card:ℝ) * (h.qa q).card ≤ 6*E+ftCard V :=by
  classical
  have hpair: ∀ u ∈ h.qa p,∀ v ∈ h.qa q,u ≠ v → h.missing.Adj u v:=by
    intro u hu v hv huv
    apply h.uZ u v huv
    rw [(h.r3 p u).mp hu,(h.r3 q v).mp hv]
    exact hpq
  have hc:=xb h.missing (h.qa p) (h.qa q) hpair
  have hcR: ((h.qa p).card:ℝ) * (h.qa q).card ≤
      2* (natCard h.missing.edgeSet:ℝ) + ftCard V :=by exact_mod_cast hc
  have hm:=h.v9
  linarith
theorem q2.zQ {V:Type*}
    [Fintype V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) (p:q1) (hp:q3 p =0) :
    ((h.qa p).card:ℝ) ^ 2 ≤ 6*E+ftCard V :=by
  have hpq: (q0 p ∩ q0 p).card=1:=by
    rw [inter_self,qU,hp]
    rfl
  simpa only [pow_two] using h.su p p hpq
theorem q2.w4 {V:Type*}
    [Fintype V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) (p:q1) (i:Fin 3)
    (hfree: ∀ j,p j=none → j=i)
    (u v :V) (hu:u ∈ h.qa p) (hv:v ∈ h.qa p)
    (hwrong: (c.graph i)ᶜ.Adj u v) : h.missing.Adj u v:=by
  rw [missing,compl_adj]
  refine ⟨hwrong.1,?_⟩
  intro hret
  obtain ⟨j,hj⟩ :=iSup_adj.mp hret
  have hup:= (h.r3 p u).mp hu
  have hvp:= (h.r3 p v).mp hv
  rcases hj with hB | hF
  · have hopp:=h.ry j u v hB
    rw [hup,hvp] at hopp
    rcases hopp with ⟨h0,h1⟩ | ⟨h1,h0⟩ <;>
      have he: (some false:Option Bool) = some true:=h0.symm.trans h1 <;> cases he
  · have hpf:= (h.z1 j u v hF).1
    rw [hup] at hpf
    have hji:=hfree j hpf
    subst j
    exact hwrong.2 (h.sparse_le i hF)
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem wo {V:Type*} [Fintype V]
    (G:SimpleGraph V) [DecidableRel G.Adj]
    (A:Finset V) (v:V) (hv:v ∈ A)
    (hadj: ∀ u ∈ A,u ≠ v → G.Adj v u) : A.card ≤ G.degree v +1:=by
  classical
  have hsub:A.erase v ⊆ G.neighborFinset v :=by
    intro u hu
    rw [mem_erase] at hu
    exact (G.mem_neighborFinset v u).mpr (hadj u hu.2 hu.1)
  have h :=card_le_card hsub
  rw [card_erase_of_mem hv,G.card_neighborFinset_eq_degree] at h
  have hp:=card_pos.mpr ⟨v,hv⟩
  omega
theorem zO {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (A:Finset V) (d:ℕ)
    (hN:3 ≤ ftCard V)
    (hsize:ftCard V +2*d ≤ 2*A.card)
    (hcore: ∀ v ∈ A,A.card ≤ G.degree v +d)
    (hout: ∀ v ∉ A,ftCard V -A.card+1 ≤ G.degree v) :
    G.IsHamiltonian:=by
  classical
  let H :=G.qE
  have hle:G ≤ H:=G.rs
  have hcard:A.card ≤ ftCard V :=card_le_univ A
  have hcoreH (u v :V) (hu:u ∈ A) (hv:v ∈ A) (huv:u ≠ v) :
      H.Adj u v:=by
    apply G.rK huv
    change ftCard V ≤ H.degree u +H.degree v
    have hu':= (hcore u hu).trans (natALAR (G.degree_le_of_le hle) d)
    have hv':= (hcore v hv).trans (natALAR (G.degree_le_of_le hle) d)
    omega
  have hdegA (u:V) (hu:u ∈ A) : A.card ≤ H.degree u +1:=by
    apply wo H A u hu
    intro v hv hvu
    exact hcoreH u v hu hv hvu.symm
  have hcross (u v :V) (hu:u ∈ A) (hv:v ∉ A) : H.Adj u v:=by
    have huv:u ≠ v:=fun h => hv (h ▸ hu)
    apply G.rK huv
    change ftCard V ≤ H.degree u +H.degree v
    have hu':=hdegA u hu
    have hv':= (hout v hv).trans (G.degree_le_of_le hle)
    omega
  have hdegOut (u:V) (hu:u ∉ A) : A.card ≤ H.degree u :=by
    have hsub:A ⊆ H.neighborFinset u :=by
      intro v hv
      exact (H.mem_neighborFinset u v).mpr (hcross v u hv hu).symm
    exact card_le_card hsub
  have htop:H= ⊤ :=by
    apply top_unique
    intro u v huv
    have hne:u ≠ v:=by simpa only [top_adj] using huv
    by_cases hu:u ∈ A
    · by_cases hv:v ∈ A
      · exact hcoreH u v hu hv hne
      · exact hcross u v hu hv
    · by_cases hv:v ∈ A
      · exact (hcross v u hv hu).symm
      · apply G.rK hne
        change ftCard V ≤ H.degree u +H.degree v
        have hu':=hdegOut u hu
        have hv':=hdegOut v hv
        omega
  apply G.sI.mp
  change H.IsHamiltonian
  rw [htop]
  apply SimpleGraph.x3 hN
  intro v
  rw [((⊤ : SimpleGraph V).degree_eq_card_sub_one v).mpr (by simp [IsUniversal])]
  omega
theorem wS {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) (v: (S:Set V)) :
    (G.induce (S:Set V)).degree v = (G.neighborFinset v.val ∩ S).card:=by
  classical
  have h :=congrArg fsCard (G.map_neighborFinset_induce v)
  simpa only [card_map,card_neighborFinset_eq_degree,Finset.toFinset_coe,
    ← SimpleGraph.card_neighborSet_eq_degree,← natCEFC] using h
theorem wE {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (A W :Finset V) (d:ℕ)
    (hdis:Disjoint A W) (hN:3 ≤ A.card+W.card)
    (hsize:W.card+2*d ≤ A.card)
    (hcore: ∀ v ∈ A,A.card ≤ (G.neighborFinset v ∩ A).card+d)
    (hout: ∀ v ∈ W,W.card+1 ≤ (G.neighborFinset v ∩ A).card) :
    (G.induce ((A ∪ W:Finset V) : Set V)).IsHamiltonian:=by
  classical
  let S :=A ∪ W
  let H :=G.induce (S:Set V)
  let A':Finset (S:Set V) :=univ.filter (fun v => v.val ∈ A)
  have hcard:ftCard (S:Set V) = A.card+W.card:=by
    calc
      ftCard (S:Set V) = (S:Set V).ncard:=natCEFC.symm
      _=S.card:=stNCF S
      _=A.card+W.card:=card_union_of_disjoint hdis
  have himage:A'.image subVal=A:=by
    ext v
    simp only [A',mem_image,mem_filter,mem_univ,true_and]
    constructor
    · rintro ⟨x,hx,rfl⟩
      exact hx
    · intro hv
      exact ⟨⟨v,mem_union_left W hv⟩,hv,rfl⟩
  have hAcard:A'.card=A.card:=by
    rw [← himage,card_image_of_injective _ subVI]
  have hdeg (v: (S:Set V)) : (G.neighborFinset v.val ∩ A).card ≤ H.degree v :=by
    rw [wS]
    apply card_le_card
    exact inter_subset_inter_left (subset_union_left:A ⊆ S)
  apply zO H A' d
  · simpa only [hcard] using hN
  · rw [hcard,hAcard]
    omega
  · intro v hv
    have hvA:v.val ∈ A:= (mem_filter.mp hv).2
    rw [hAcard]
    exact (hcore v.val hvA).trans (natALAR (hdeg v) d)
  · intro v hv
    have hvA:v.val ∉ A:=by simpa only [A',mem_filter,mem_univ,true_and] using hv
    have hvW:v.val ∈ W:= (mem_union.mp v.property).resolve_left hvA
    rw [hcard,hAcard,Nat.add_sub_cancel_left]
    exact (hout v.val hvW).trans (hdeg v)
theorem sr {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (A W :Finset V) (d:ℕ)
    (hdis:Disjoint A W) (hN:3 ≤ A.card+W.card)
    (hsize:W.card+2*d ≤ A.card)
    (hcore: ∀ v ∈ A,A.card ≤ (G.neighborFinset v ∩ A).card+d)
    (hout: ∀ v ∈ W,W.card+1 ≤ (G.neighborFinset v ∩ A).card) :
    ∃ (v:V) (c:G.Walk v v),c.IsCycle ∧ c.length=A.card+W.card:=by
  classical
  let S :=A ∪ W
  have hcard:ftCard (S:Set V) = A.card+W.card:=by
    calc
      ftCard (S:Set V) = (S:Set V).ncard:=natCEFC.symm
      _=S.card:=stNCF S
      _=A.card+W.card:=card_union_of_disjoint hdis
  have hHam: (G.induce (S:Set V)).IsHamiltonian:=
    wE G A W d hdis hN hsize hcore hout
  let:Nontrivial (S:Set V) :=ftOLCIN.mp (by omega)
  obtain ⟨v⟩ := (inferInstance:Nonempty (S:Set V))
  obtain ⟨c,hc⟩ :=hHam.exists_isHamiltonianCycle v
  refine ⟨(Embedding.induce (S:Set V)).toHom v,
    c.map (Embedding.induce (S:Set V)).toHom,
    hc.isCycle.map subVI,?_⟩
  rw [wkLM,hc.length_eq,hcard]
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem a7 {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) :
    ∑ v ∈ S,(G.neighborFinset v ∩ S).card=
      2* (G.induce (S:Set V)).edgeFinset.card:=by
  classical
  rw [← (G.induce (S:Set V)).sum_degrees_eq_twice_card_edges]
  simp_rw [wS]
  exact (Finset.sum_coe_sort S (fun v => (G.neighborFinset v ∩ S).card)).symm
theorem vk {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) (r:ℕ) :
    ∃ A :Finset V,A ⊆ S ∧
      r* (S.card-A.card) ≤ 2* (G.induce (S:Set V)).edgeFinset.card ∧
      ∀ v ∈ A,(G.neighborFinset v ∩ S).card ≤ r:=by
  classical
  let A :=S.filter (fun v => (G.neighborFinset v ∩ S).card ≤ r)
  have hAS:A ⊆ S:=filter_subset _ _
  refine ⟨A,hAS,?_,fun v hv=> (mem_filter.mp hv).2⟩
  have hbad (v:V) (hv:v ∈ S \ A) : r ≤ (G.neighborFinset v ∩ S).card:=by
    have hvS:= (mem_sdiff.mp hv).1
    have hvA:= (mem_sdiff.mp hv).2
    have hn: ¬ (G.neighborFinset v ∩ S).card ≤ r:=by
      intro h
      exact hvA (mem_filter.mpr ⟨hvS,h⟩)
    omega
  calc
    r* (S.card-A.card) = ∑ _v ∈ S \ A,r:=by
      rw [sum_const,smul_eq_mul,card_sdiff,inter_eq_left.mpr hAS,natMC]
    _ ≤ ∑ v ∈ S \ A,(G.neighborFinset v ∩ S).card:=sum_le_sum hbad
    _ ≤ ∑ v ∈ S,(G.neighborFinset v ∩ S).card:=
      sum_le_sum_of_subset sdiff_subset
    _=2* (G.induce (S:Set V)).edgeFinset.card:=a7 G S
theorem r1 {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (S:Finset V) (v:V) (hv:v ∈ S) :
    (G.neighborFinset v ∩ S).card+ (Gᶜ.neighborFinset v ∩ S).card+1=S.card:=by
  classical
  have hdis:Disjoint (G.neighborFinset v ∩ S) (Gᶜ.neighborFinset v ∩ S) :=by
    apply fsDL.mpr
    intro u hu huc
    have h := (G.mem_neighborFinset v u).mp (mem_inter.mp hu).1
    have hc:= (Gᶜ.mem_neighborFinset v u).mp (mem_inter.mp huc).1
    exact (show ¬ G.Adj v u from hc.2) h
  have hunion: (G.neighborFinset v ∩ S) ∪ (Gᶜ.neighborFinset v ∩ S) = S.erase v :=by
    ext u
    simp only [mem_union,mem_inter,mem_neighborFinset,compl_adj,mem_erase]
    constructor
    · rintro (⟨h,hu⟩ | ⟨⟨h,_⟩,hu⟩)
      · exact ⟨h.ne.symm,hu⟩
      · exact ⟨h.symm,hu⟩
    · rintro ⟨huv,hu⟩
      by_cases h :G.Adj v u
      · exact orInl ⟨h,hu⟩
      · exact orInr ⟨⟨huv.symm,h⟩,hu⟩
  have h :=congrArg fsCard hunion
  rw [card_union_of_disjoint hdis,card_erase_of_mem hv] at h
  have hp:=card_pos.mpr ⟨v,hv⟩
  omega
theorem sL {V:Type*} [Fintype V] [DecidableEq V]
    (G:SimpleGraph V) [DecidableRel G.Adj] (A S :Finset V) (r:ℕ)
    (hAS:A ⊆ S) (hclean: ∀ v ∈ A,(Gᶜ.neighborFinset v ∩ S).card ≤ r) :
    ∀ v ∈ A,A.card ≤ (G.neighborFinset v ∩ A).card+ (r+1) :=by
  intro v hv
  have h :=r1 G A v hv
  have hle: (Gᶜ.neighborFinset v ∩ A).card ≤ r:=
    (card_le_card (inter_subset_inter_left hAS)).trans (hclean v hv)
  omega
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem uN {V:Type*} [Finite V]
    (G:SimpleGraph V) (S:Finset V) (n:ℕ) (hn:8 ≤ n)
    (hno: ¬ cycleGraph n ⊑ G) :
    n*S.card ≤ n*n+16*natCard (Gᶜ.induce (S:Set V)).edgeSet:=by
  classical
  let:=ftOfFin V
  let q :=n/4
  obtain ⟨A,hAS,hbad,hclean⟩ :=vk Gᶜ S q
  have hAn:A.card < n:=by
    by_contra hlarge
    obtain ⟨C,hCA,hCc⟩ :=exists_subset_card_eq (show n ≤ A.card by omega)
    have hCS:C ⊆ S:=hCA.trans hAS
    have hCcore: ∀ v ∈ C,C.card ≤ (G.neighborFinset v ∩ C).card+ (q+1) :=
      sL G C S q hCS (fun v hv=> hclean v (hCA hv))
    obtain ⟨v,c,hc,hlen⟩ :=sr G C ∅ (q+1)
      (by simp) (by simp only [card_empty,add_zero,hCc];omega)
      (by simp only [card_empty,zero_add,hCc];dsimp only [q];omega) hCcore
      (by intro v hv;simp at hv)
    apply hno
    apply (cycleGraph_isContained_iff (by omega:2 < n)).mpr
    exact ⟨v,c,hc,by simpa only [card_empty,add_zero,hCc] using hlen⟩
  have hq:n ≤ 8*q:=by dsimp only [q];omega
  have hloss:=natMLMR (S.card-A.card) hq
  rw [q7] at hbad
  have hNl:n* (S.card-A.card) ≤ 16*natCard (Gᶜ.induce (S:Set V)).edgeSet:=by
    nlinarith only [hloss,hbad]
  have hAc:=card_le_card hAS
  have hsum:=natSAC hAc
  have hAn':=natMLML n hAn.le
  nlinarith only [hNl,hsum,hAn']
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem q2.t5 {V:Type*} [Fintype V] [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D)
    (n:ℕ) (hn:8 ≤ n) (hno: ∀ i,¬ cycleGraph n ⊑ c.graph i)
    (p:q1) (hp:q3 p =1) :
    (n:ℝ) * (h.qa p).card ≤ (n:ℝ) ^ 2+48*E:=by
  classical
  obtain ⟨i,hi,huniq⟩ :=xm p hp
  let S :=h.qa p
  have hsub: (c.graph i)ᶜ.induce (S:Set V) ≤ h.missing.induce (S:Set V) :=by
    intro u v huv
    exact h.w4 p i huniq u.val v.val u.property v.property huv
  have hwrong:natCard ((c.graph i)ᶜ.induce (S:Set V)).edgeSet ≤ natCard h.missing.edgeSet:=
    (zW _ _ hsub).trans (t2 h.missing S)
  have hbound:=uN (c.graph i) S n hn (hno i)
  have hboundR: (n:ℝ) * S.card ≤ (n:ℝ) ^ 2+
      16* (natCard ((c.graph i)ᶜ.induce (S:Set V)).edgeSet:ℝ) :=by
    rw [pow_two]
    exact_mod_cast hbound
  have hwrongR: (natCard ((c.graph i)ᶜ.induce (S:Set V)).edgeSet:ℝ) ≤
      natCard h.missing.edgeSet:=by exact_mod_cast hwrong
  have hmissing:=h.v9
  change (n:ℝ) * S.card ≤ (n:ℝ) ^ 2+48*E
  linarith
end Erdos556
namespace Erdos556
open Finset
def qQ (x y :q1 → ℝ) : ℝ:=
  ∑ p,∑ q,qb p q*x p*y q
def u0 (x:q1 → ℝ) : ℝ:=
  ∑ p,(q3 p :ℝ) * x p
theorem yO (w:q1 → ℝ) :
    qd w =qQ w w-u0 w :=rfl
theorem tD (x y z:q1 → ℝ) :
    qQ (x+y) z =qQ x z+qQ y z:=by
  simp only [qQ,Pi.add_apply,mul_add,add_mul,sum_add_distrib]
theorem x4 (x y z:q1 → ℝ) :
    qQ x (y+z) = qQ x y+qQ x z:=by
  simp only [qQ,Pi.add_apply,mul_add,sum_add_distrib]
theorem aD (x y :q1 → ℝ) : qQ x y=qQ y x:=by
  rw [qQ,sum_comm]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  rw [sm q p]
  ring
theorem u3 (x:q1 → ℝ) (p:q1) (t:ℝ) :
    qQ (Pi.single p t) x =t* ∑ q,qb p q*x q:=by
  classical
  simp [qQ,Pi.single_apply,mul_ite,mul_sum,mul_comm,mul_left_comm]
theorem ym (x:q1 → ℝ) (p:q1) (t:ℝ) :
    qQ x (Pi.single p t) = t* ∑ q,qb p q*x q:=by
  rw [aD,u3]
theorem yb (p:q1) (s t :ℝ) :
    qQ (Pi.single p s) (Pi.single p t) = s*t:=by
  classical
  rw [u3]
  simp [Pi.single_apply,mul_ite,vU]
theorem dd (x y :q1 → ℝ) : u0 (x+y) = u0 x +u0
    y:=by
  simp only [u0,Pi.add_apply,mul_add,sum_add_distrib]
theorem aA (p:q1) (t:ℝ) :
    u0 (Pi.single p t) = q3 p *t:=by
  classical
  simp [u0,Pi.single_apply,mul_ite]
theorem rI (w:q1 → ℝ) (p:q1) (t:ℝ) :
    qd (w+Pi.single p t) = qd w +t*qm w p+t^2:=by
  simp only [yO]
  rw [tD,x4,x4,
    ym,u3,yb,
    dd,aA]
  dsimp [qm]
  ring
theorem uk (w:q1 → ℝ) (p q :q1) (t:ℝ) :
    qm (w+Pi.single p t) q =qm w q+2*t*qb q p:=by
  classical
  simp only [qm,Pi.add_apply,mul_add,sum_add_distrib]
  have hsum: (∑ r,qb q r* (Pi.single p t:q1 → ℝ) r) = qb q p*t
    :=by
    simp [Pi.single_apply,mul_ite]
  rw [hsum]
  ring
end Erdos556
namespace Erdos556
def up (w:q1 → ℝ) (p q :q1) (t:ℝ) : q1 → ℝ:=
  (w+Pi.single p t) + Pi.single q (-t)
def qx (w:q1 → ℝ) (p q :q1) : q1 → ℝ:=
  up w p q (w q)
theorem xT (w:q1 → ℝ) (p q :q1) (t:ℝ)
    (hpq:qb p q=1) :
    qd (up w p q t) = qd w +t* (qm w p-qm w q) :=by
  rw [up,rI,rI,uk,
    sm q p,hpq]
  ring
theorem uG (w:q1 → ℝ) (p q :q1) (hpq:p ≠ q) :
    qx w p q q=0:=by
  classical
  simp [qx,up,Ne.symm hpq]
theorem uH (w:q1 → ℝ) (p q :q1) (hpq:p ≠ q) :
    qx w p q p=w p+w q:=by
  classical
  simp [qx,up,hpq]
theorem rL (w:q1 → ℝ) (p q r:q1)
    (hrp:r ≠ p) (hrq:r ≠ q) : qx w p q r=w r:=by
  classical
  simp [qx,up,hrp,hrq]
theorem si (w:q1 → ℝ) (p q :q1)
    (hp:0 ≤ w p) (hq:0 ≤ w q) (hpq:qb p q=1) :
    qd (qx w p q) ≤ qd w ∨
      qd (qx w q p) ≤ qd w :=by
  by_cases hgrad:qm w p ≤ qm w q
  · left
    rw [qx,xT w p q (w q) hpq]
    have h :=mul_nonpos_of_nonneg_of_nonpos hq (sub_nonpos.mpr hgrad)
    linarith
  · right
    have hqp:qb q p=1:= (sm q p).trans hpq
    rw [qx,xT w q p (w p) hqp]
    have h :=mul_nonpos_of_nonneg_of_nonpos hp (by linarith:qm w q-qm w
      p ≤ 0)
    linarith
end Erdos556
namespace Erdos556
open Finset
theorem e1 (w:q1 → ℝ) (p q :q1) (t:ℝ) :
    (∑ r,up w p q t r) = ∑ r,w r:=by
  classical
  simp [up,Pi.add_apply,sum_add_distrib]
theorem v0 {w:q1 → ℝ} {p q r:q1}
    (hpq:p ≠ q) (hp:0 < w p) (hr:0 < qx w p q r) : 0 < w r :=by
  by_cases hrp:r=p
  · exact hrp ▸ hp
  by_cases hrq:r=q
  · rw [hrq,uG w p q hpq] at hr
    exact hr.false.elim
  · rwa [rL w p q r hrp hrq] at hr
theorem q6.transfer {w:q1 → ℝ} (hw:q6 w)
    (p q :q1) (hpq:p ≠ q) (hp:0 < w p)
    (hpdim:2 ≤ q3 p) (hqdim:2 ≤ q3 q) :
    q6 (qx w p q) :=by
  constructor
  · intro r
    by_cases hrp:r=p
    · rw [hrp,uH w p q hpq]
      exact add_nonneg (hw.nonneg p) (hw.nonneg q)
    by_cases hrq:r=q
    · rw [hrq,uG w p q hpq]
    · rw [rL w p q r hrp hrq]
      exact hw.nonneg r
  · rw [qx,e1]
    exact hw.sum_four
  · intro r hr
    have hrp:r ≠ p:=by intro h;subst r;omega
    have hrq:r ≠ q:=by intro h;subst r;omega
    rw [rL w p q r hrp hrq]
    exact hw.vertex_zero r hr
  · intro r hr
    have hrp:r ≠ p:=by intro h;subst r;omega
    have hrq:r ≠ q:=by intro h;subst r;omega
    rw [rL w p q r hrp hrq]
    exact hw.edge_le_one r hr
  · intro r s hr hs
    exact hw.compatible r s (v0 hpq hp hr)
      (v0 hpq hp hs)
open scoped Classical in
noncomputable def qe (w:q1 → ℝ) : Finset q1:=
  univ.filter (fun p => 2 ≤ q3 p ∧ 0 < w p)
theorem za {w:q1 → ℝ} (hw:q6 w)
    (p q :q1) (hpq:p ≠ q) (hp:0 < w p)
    (hpdim:2 ≤ q3 p) :
    qe (qx w p q) = (qe w).erase q :=by
  classical
  ext r
  simp only [qe,mem_filter,mem_univ,true_and,mem_erase]
  by_cases hrp:r=p
  · subst r
    rw [uH w p q hpq]
    have hpos:0 < w p+w q:=add_pos_of_pos_of_nonneg hp (hw.nonneg q)
    exact ⟨fun _ => ⟨hpq,hpdim,hp⟩,fun _ => ⟨hpdim,hpos⟩⟩
  by_cases hrq:r=q
  · subst r
    rw [uG w p q hpq]
    simp
  · rw [rL w p q r hrp hrq]
    exact ⟨fun h => ⟨hrq,h⟩,fun h => h.2⟩
theorem rh {w:q1 → ℝ} (hw:q6 w)
    (p q :q1) (hpq:p ≠ q) (hp:0 < w p) (hq:0 < w q)
    (hpdim:2 ≤ q3 p) (hqdim:2 ≤ q3 q) :
    (qe (qx w p q)).card < (qe w).card:=by
  classical
  rw [za hw p q hpq hp hpdim]
  exact card_erase_lt_of_mem (mem_filter.mpr ⟨mem_univ q,hqdim,hq⟩)
end Erdos556
namespace Erdos556
open Finset
theorem yW (w:q1 → ℝ) (hw:q6 w) :
    ∃ v :q1 → ℝ,q6 v ∧
      (qe v :Set q1).Pairwise
        (fun p q=> Disjoint (q0 p) (q0 q)) ∧
      qd v ≤ qd w :=by
  classical
  have aux: ∀ M:ℕ,∀ w:q1 → ℝ,q6 w →
      (qe w).card=M →
      ∃ v :q1 → ℝ,q6 v ∧
        (qe v :Set q1).Pairwise
          (fun p q=> Disjoint (q0 p) (q0 q)) ∧
        qd v ≤ qd w :=by
    intro M
    induction M using natSIO with
    | h M ih=>
        intro w hw hM
        by_cases hdisj: (qe w :Set q1).Pairwise
            (fun p q=> Disjoint (q0 p) (q0 q))
        · exact ⟨w,hw,hdisj,le_rfl⟩
        simp only [Set.Pairwise] at hdisj
        push Not at hdisj
        obtain ⟨p,hpH,q,hqH,hpq,hnot⟩ :=hdisj
        have hpdim:= (mem_filter.mp hpH).2.1
        have hqdim:= (mem_filter.mp hqH).2.1
        have hp:= (mem_filter.mp hpH).2.2
        have hq:= (mem_filter.mp hqH).2.2
        have hover:qb p q=1:=by simp only [qb,if_neg hnot]
        have step (x:q1 → ℝ) (hx:q6 x)
            (hxc: (qe x).card < (qe w).card)
            (hxe:qd x ≤ qd w) :
            ∃ v :q1 → ℝ,q6 v ∧
              (qe v :Set q1).Pairwise
                (fun p q=> Disjoint (q0 p) (q0 q)) ∧
              qd v ≤ qd w :=by
          obtain ⟨v,hv,hvd,hve⟩ :=ih (qe x).card (by omega) x hx rfl
          exact ⟨v,hv,hvd,hve.trans hxe⟩
        rcases si w p q (hw.nonneg p) (hw.nonneg q) hover with
          hE | hE
        · exact step (qx w p q) (hw.transfer p q hpq hp hpdim hqdim)
            (rh hw p q hpq hp hq hpdim hqdim) hE
        · exact step (qx w q p) (hw.transfer q p hpq.symm hq hqdim hpdim)
            (rh hw q p hpq.symm hq hp hqdim hpdim) hE
  exact aux (qe w).card w hw rfl
end Erdos556
namespace Erdos556
open Finset
theorem ws (x:q1 → ℝ)
    (hzero: ∀ p q,p ≠ q → qb p q*x p*x q=0) :
    qQ x x= ∑ p,x p^2:=by
  unfold qQ
  apply sum_congr rfl
  intro p _
  rw [sum_eq_single p]
  · rw [vU]
    ring
  · intro q _ hqp
    exact hzero p q hqp.symm
  · intro hp
    exact (hp (mem_univ p)).elim
theorem vB (x:q1 → ℝ) (S:Finset q1)
    (hsupport: ∀ p,p ∉ S → x p=0)
    (hdim: ∀ p ∈ S,q3 p =1)
    (hdisj: (S:Set q1).Pairwise (fun p q=> Disjoint (q0 p)
      (q0 q))) :
    qd x = (∑ p ∈ S,x p^2) - ∑ p ∈ S,x p:=by
  classical
  have hzero (p q :q1) (hpq:p ≠ q) : qb p q*x p*x q=0:=by
    by_cases hp:p ∈ S
    · by_cases hq:q ∈ S
      · simp only [qb,if_pos (hdisj hp hq hpq),zero_mul]
      · rw [hsupport q hq,mul_zero]
    · rw [hsupport p hp,mul_zero,zero_mul]
  have hsq: (∑ p,x p^2) = ∑ p ∈ S,x p^2:=by
    symm
    apply sum_subset (subset_univ S)
    intro p _ hp
    rw [hsupport p hp]
    norm_num
  have hlin:u0 x = ∑ p ∈ S,x p:=by
    calc
      u0 x = ∑ p ∈ S,(q3 p :ℝ) * x p :=by
        symm
        apply sum_subset (subset_univ S)
        intro p _ hp
        rw [hsupport p hp,mul_zero]
      _= ∑ p ∈ S,x p:=by
        apply sum_congr rfl
        intro p hp
        rw [hdim p hp]
        norm_num
  rw [yO,ws x hzero,hsq,hlin]
theorem tE (p:q1) : qb qF p =1:=by
  have hfull:q0 qF=univ:=by decide
  have hnon: (q0 p).Nonempty:=by
    apply card_pos.mp
    rw [qU]
    positivity
  have hnot: ¬ Disjoint (q0 qF) (q0 p) :=by
    intro hd
    obtain ⟨v,hv⟩ :=hnon
    exact fsDL.mp hd (by rw [hfull];exact mem_univ v) hv
  simp only [qb,if_neg hnot]
theorem xg (x:q1 → ℝ) :
    qm x qF=2* (∑ p,x p) - 3:=by
  simp only [qm,tE,one_mul,zx,natCO]
end Erdos556
namespace Erdos556
open Finset
theorem wT {I:Type*} (S:Finset I) (f:I → ℝ)
    (m:ℕ) (hcard:S.card ≤ m) :
    (∑ i ∈ S,f i) ^ 2 ≤ (m:ℝ) * ∑ i ∈ S,f i^2:=by
  have h :=sum_mul_sq_le_sq_mul_sq S f (fun _ => (1:ℝ))
  have h': (∑ i ∈ S,f i) ^ 2 ≤ (S.card:ℝ) * ∑ i ∈ S,f i^2:=by
    simpa only [mul_one,one_pow,sum_const,nsmul_eq_mul,mul_one,mul_comm] using h
  apply h'.trans
  apply mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
  exact sum_nonneg fun i _=> sq_nonneg (f i)
theorem zC {I:Type*} (S:Finset I) (f:I → ℝ)
    (hf: ∀ i ∈ S,f i ≤ 1) : (∑ i ∈ S,f i) ≤ S.card:=by
  calc
    (∑ i ∈ S,f i) ≤ ∑ _i ∈ S,(1:ℝ) :=sum_le_sum hf
    _=S.card:=by simp
theorem q6.aB {w:q1 → ℝ} (hw:q6 w) :
    (∑ p ∈ ql w,w p) ^ 2 ≤ 4* ∑ p ∈ ql w,w p^2:=by
  exact wT (ql w) w 4 hw.vl
end Erdos556
namespace Erdos556
theorem a8 (z E S:ℝ) (hz:0 ≤ z) (hE:0 ≤ E)
    (htotal:E+z=4) (hS:E^2 ≤ 4*S) :
    z ≤ z^2+2*z*E+S-E-3*z:=by
  have hzE:0 ≤ z*E:=mul_nonneg hz hE
  nlinarith
theorem xZ (y₀ y₁ E₀ E₁ S₀ S₁:ℝ)
    (hE₀:0 ≤ E₀) (hE₀':E₀ ≤ 2) (hE₁:0 ≤ E₁) (hE₁':E₁ ≤ 2)
    (hS₀:E₀^2 ≤ 2*S₀) (hS₁:E₁^2 ≤ 2*S₁)
    (htotal:y₀+E₀+y₁+E₁=4) :
    0 ≤ y₀^2+2*y₀*E₀+S₀-2*y₀-E₀+
      (y₁^2+2*y₁*E₁+S₁-2*y₁-E₁) :=by
  have hprod₀:=mul_nonneg hE₀ (sub_nonneg.mpr hE₀')
  have hprod₁:=mul_nonneg hE₁ (sub_nonneg.mpr hE₁')
  have hs₀:=sq_nonneg (y₀+E₀-2)
  have hs₁:=sq_nonneg (y₁+E₁-2)
  nlinarith
theorem y5 (y₀ y₁ E₀ E₁ S₀ S₁:ℝ)
    (hE₀:0 ≤ E₀) (hE₀':E₀ ≤ 2) (hE₁:0 ≤ E₁) (hE₁':E₁ ≤ 2)
    (hS₀:E₀^2 ≤ 2*S₀) (hS₁:E₁^2 ≤ 2*S₁)
    (htotal:y₀+E₀+y₁+E₁=4)
    (hzero:y₀^2+2*y₀*E₀+S₀-2*y₀-E₀+
      (y₁^2+2*y₁*E₁+S₁-2*y₁-E₁) = 0) :
    y₀+E₀=2 ∧ y₁+E₁=2 ∧ (E₀=0 ∨ E₀=2) ∧ (E₁=0 ∨ E₁=2) :=by
  have hprod₀:=mul_nonneg hE₀ (sub_nonneg.mpr hE₀')
  have hprod₁:=mul_nonneg hE₁ (sub_nonneg.mpr hE₁')
  have hs₀:=sq_nonneg (y₀+E₀-2)
  have hs₁:=sq_nonneg (y₁+E₁-2)
  have hL₀:y₀+E₀=2:=by nlinarith
  have hL₁:y₁+E₁=2:=by nlinarith
  have hE₀zero:E₀* (2-E₀) = 0:=by nlinarith
  have hE₁zero:E₁* (2-E₁) = 0:=by nlinarith
  refine ⟨hL₀,hL₁,?_,?_⟩
  · rcases mul_eq_zero.mp hE₀zero with h | h
    · exact orInl h
    · right;linarith
  · rcases mul_eq_zero.mp hE₁zero with h | h
    · exact orInl h
    · right;linarith
end Erdos556
namespace Erdos556
open Finset
theorem q6.u6 {w:q1 → ℝ}
    (hw:q6 w)
    (hhigh: ∀ p,2 ≤ q3 p → p ≠ qF → w p =0) :
    w qF ≤ qd w :=by
  classical
  let E :=ql w
  let x (p:q1) : ℝ:=if p =qF then 0 else w p
  have hx (p:q1) (hp:p ∈ E) : x p =w p:=by
    have hd:= (mem_filter.mp hp).2.1
    have hne:p ≠ qF:=by intro h;subst p;rw [zx] at hd;omega
    exact if_neg hne
  have hzero (p:q1) (hp:p ∉ E) : x p =0:=by
    by_cases hpc:p=qF
    · exact if_pos hpc
    rw [show x p=w p from if_neg hpc]
    by_cases hd0:q3 p =0
    · exact hw.vertex_zero p hd0
    by_cases hd1:q3 p =1
    · have hnot: ¬ 0 < w p:=fun h => hp (mem_filter.mpr ⟨mem_univ p,hd1,h⟩)
      exact le_antisymm (le_of_not_gt hnot) (hw.nonneg p)
    · exact hhigh p (by omega) hpc
  have hdecomp:w=x+Pi.single qF (w qF) :=by
    funext p
    by_cases hpc:p=qF
    · subst p
      simp [x]
    · simp [x,hpc]
  have hsum: (∑ p,x p) = ∑ p ∈ E,w p:=by
    calc
      (∑ p,x p) = ∑ p ∈ E,x p:=by
        symm
        exact sum_subset (subset_univ E) (fun p _ hp=> hzero p hp)
      _= ∑ p ∈ E,w p:=sum_congr rfl hx
  have henergy:qd x = (∑ p ∈ E,w p^2) - ∑ p ∈ E,w p:=by
    rw [vB x E hzero (fun p hp=> (mem_filter.mp hp).2.1)
      hw.s0]
    congr 1
    · exact sum_congr rfl (fun p hp=> congrArg (fun a :ℝ=> a ^2) (hx p hp))
    · exact sum_congr rfl hx
  have htotal: (∑ p ∈ E,w p) + w qF=4:=by
    calc
      (∑ p ∈ E,w p) + w qF= (∑ p,x p) + w qF:=by rw [hsum]
      _= ∑ p,((x+Pi.single qF (w qF)) : q1 → ℝ) p :=by
        simp [Pi.add_apply,sum_add_distrib]
      _= ∑ p,w p:=congrArg (fun f :q1 → ℝ=> ∑ p,f p) hdecomp.symm
      _=4:=hw.sum_four
  have hfull:qd w = (∑ p ∈ E,w p^2) - (∑ p ∈ E,w p) +
      w qF* (2* (∑ p ∈ E,w p) - 3) + (w qF) ^ 2:=by
    calc
      qd w =qd (x+Pi.single qF (w qF)) :=congrArg qd
        hdecomp
      _=_:=by rw [rI,henergy,xg,hsum]
  have hbound:=a8 (w qF) (∑ p ∈ E,w p) (∑ p ∈ E,w p^2)
    (hw.nonneg qF) (sum_nonneg fun p _=> hw.nonneg p) htotal hw.aB
  rw [hfull]
  nlinarith only [hbound]
end Erdos556
namespace Erdos556
open Finset
theorem z4: ∀ (i:Fin 3) (b:Bool),cubeFace i b ≠ cubeFace i (!b) :=by
  decide
theorem se: ∀ (i:Fin 3) (b:Bool) (p:q1),
    q3 p =1 →
    (q0 p ∩ q0 (cubeFace i b)).card ≠ 1 →
    q0 p ⊆ q0 (cubeFace i b) ∨
      q0 p ⊆ q0 (cubeFace i (!b)) :=by
  decide
theorem ta: ∀ (i:Fin 3) (b:Bool) (p:q1),
    q3 p =1 →
    ¬ (q0 p ⊆ q0 (cubeFace i b) ∧
      q0 p ⊆ q0 (cubeFace i (!b))) :=by
  decide
theorem tC {p q :q1} (hsub:q0 q ⊆ q0 p) :
    qb p q=1:=by
  have hnon: (q0 q).Nonempty:=by
    apply card_pos.mp
    rw [qU]
    positivity
  have hnot: ¬ Disjoint (q0 p) (q0 q) :=by
    intro h
    obtain ⟨v,hv⟩ :=hnon
    exact fsDL.mp h (hsub hv) hv
  simp only [qb,if_neg hnot]
theorem zZ (i:Fin 3) (b:Bool) :
    qb (cubeFace i b) (cubeFace i (!b)) = 0:=by
  have hb:b ≠ !b:=by cases b <;> decide
  have hdisj:= (ui i i b (!b)).mpr ⟨rfl,hb⟩
  simp only [qb,if_pos hdisj]
theorem we (i:Fin 3) (b:Bool) (p:q1)
    (hsub:q0 p ⊆ q0 (cubeFace i (!b))) :
    qb (cubeFace i b) p =0:=by
  have hb:b ≠ !b:=by cases b <;> decide
  have hdisj:= ((ui i i b (!b)).mpr ⟨rfl,hb⟩).mono_right hsub
  simp only [qb,if_pos hdisj]
end Erdos556
namespace Erdos556
open Finset
noncomputable def qf (w:q1 → ℝ) (i:Fin 3) (b:Bool) :
    Finset q1:=
  (ql w).filter (fun p => q0 p ⊆ q0 (cubeFace i b))
theorem ut (w:q1 → ℝ) (i:Fin 3) (b:Bool) :
    qf w i b ⊆ ql w :=filter_subset _ _
theorem q6.uL {w:q1 → ℝ} (hw:q6 w)
    (i:Fin 3) (b:Bool) : (qf w i b).card ≤ 2:=by
  have h :=vh (qf w i b) (q0 (cubeFace i b))
    (fun p hp=> (mem_filter.mp (mem_filter.mp hp).1).2.1)
    (hw.s0.mono (ut w i b))
    (fun p hp=> (mem_filter.mp hp).2)
  rw [qU,r4] at h
  norm_num at h
  omega
theorem w0 (w:q1 → ℝ) (i:Fin 3) (b:Bool) :
    Disjoint (qf w i b) (qf w i (!b)) :=by
  rw [fsDL]
  intro p hp hq
  have hd:= (mem_filter.mp (mem_filter.mp hp).1).2.1
  exact ta i b p hd ⟨(mem_filter.mp hp).2,(mem_filter.mp hq).2⟩
theorem xc {w:q1 → ℝ} (hw:q6 w)
    (i:Fin 3) (b:Bool) (hb:0 < w (cubeFace i b)) :
    qf w i b ∪ qf w i (!b) = ql w :=by
  apply Subset.antisymm
  · exact union_subset (ut w i b) (ut w i (!b))
  · intro p hp
    have hd:= (mem_filter.mp hp).2.1
    have hwpos:= (mem_filter.mp hp).2.2
    rcases se i b p hd (hw.compatible p (cubeFace i b) hwpos hb) with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨hp,h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hp,h⟩)
theorem q6.ud {w:q1 → ℝ} (hw:q6 w)
    (i:Fin 3) (b:Bool) : (∑ p ∈ qf w i b,w p) ≤ 2:=by
  apply (zC (qf w i b) w ?_).trans
  · exact_mod_cast hw.uL i b
  · intro p hp
    exact hw.edge_le_one p (mem_filter.mp (mem_filter.mp hp).1).2.1
theorem q6.sf {w:q1 → ℝ} (hw:q6 w)
    (i:Fin 3) (b:Bool) :
    (∑ p ∈ qf w i b,w p) ^ 2 ≤ 2* ∑ p ∈ qf w i b,w p^2:=
  wT (qf w i b) w 2 (hw.uL i b)
theorem sG (w x :q1 → ℝ) (i:Fin 3) (b:Bool)
    (hx: ∀ p ∈ ql w,x p=w p)
    (hzero: ∀ p,p ∉ ql w → x p=0)
    (hpart: ∀ p ∈ ql w,
      q0 p ⊆ q0 (cubeFace i b) ∨
        q0 p ⊆ q0 (cubeFace i (!b))) :
    qm x (cubeFace i b) = 2* (∑ p ∈ qf w i b,w p) - 2:=by
  classical
  have hsum: (∑ p,qb (cubeFace i b) p *x p) = ∑ p ∈ qf w i b,w p:=by
    calc
      (∑ p,qb (cubeFace i b) p *x p) =
          ∑ p ∈ ql w,qb (cubeFace i b) p *x p:=by
        symm
        apply sum_subset (subset_univ _)
        intro p _ hp
        rw [hzero p hp,mul_zero]
      _= ∑ p ∈ qf w i b,w p:=by
        rw [qf,sum_filter]
        apply sum_congr rfl
        intro p hp
        rw [hx p hp]
        by_cases hsub:q0 p ⊆ q0 (cubeFace i b)
        · rw [if_pos hsub,tC hsub,one_mul]
        · rw [if_neg hsub,
            we i b p ((hpart p hp).resolve_left hsub),zero_mul]
  simp only [qm,hsum,r4,natCO]
end Erdos556
namespace Erdos556
open Finset
theorem q6.sQ {w:q1 → ℝ}
    (hw:q6 w) (i:Fin 3) (b:Bool) (hface:0 < w (cubeFace i b))
    (hhigh: ∀ r,2 ≤ q3 r → r ≠ cubeFace i b → r ≠ cubeFace i (!b) → w r =0) :
    0 ≤ qd w ∧ (qd w =0 →
      w (cubeFace i b) + (∑ r ∈ qf w i b,w r) = 2 ∧
      w (cubeFace i (!b)) + (∑ r ∈ qf w i (!b),w r) = 2 ∧
      ((∑ r ∈ qf w i b,w r) = 0 ∨ (∑ r ∈ qf w i b,w r) = 2) ∧
      ((∑ r ∈ qf w i (!b),w r) = 0 ∨
        (∑ r ∈ qf w i (!b),w r) = 2)) :=by
  classical
  let p :=cubeFace i b
  let q :=cubeFace i (!b)
  have hpq:p ≠ q:=z4 i b
  let E :=ql w
  let x (r:q1) : ℝ:=if r =p ∨ r=q then 0 else w r
  have hx (r:q1) (hr:r ∈ E) : x r =w r:=by
    have hd:= (mem_filter.mp hr).2.1
    have hrp:r ≠ p:=by
      intro h
      subst r
      change q3 (cubeFace i b) = 1 at hd
      rw [r4] at hd
      omega
    have hrq:r ≠ q:=by
      intro h
      subst r
      change q3 (cubeFace i (!b)) = 1 at hd
      rw [r4] at hd
      omega
    exact if_neg (not_or.mpr ⟨hrp,hrq⟩)
  have hzero (r:q1) (hr:r ∉ E) : x r =0:=by
    by_cases hfaces:r=p ∨ r=q
    · exact if_pos hfaces
    rw [show x r=w r from if_neg hfaces]
    by_cases hd0:q3 r =0
    · exact hw.vertex_zero r hd0
    by_cases hd1:q3 r =1
    · have hn: ¬ 0 < w r:=fun h => hr (mem_filter.mpr ⟨mem_univ r,hd1,h⟩)
      exact le_antisymm (le_of_not_gt hn) (hw.nonneg r)
    · exact hhigh r (by omega) (not_or.mp hfaces).1 (not_or.mp hfaces).2
  have hdecomp:w= (x+Pi.single p (w p)) + Pi.single q (w q) :=by
    funext r
    by_cases hrp:r=p
    · subst r
      simp [x,hpq]
    by_cases hrq:r=q
    · subst r
      simp [x,Ne.symm hpq]
    · simp [x,hrp,hrq]
  have hsum: (∑ r,x r) = ∑ r ∈ E,w r:=by
    calc
      (∑ r,x r) = ∑ r ∈ E,x r:=by
        symm
        exact sum_subset (subset_univ E) (fun r _ hr=> hzero r hr)
      _= ∑ r ∈ E,w r:=sum_congr rfl hx
  have henergy:qd x = (∑ r ∈ E,w r^2) - ∑ r ∈ E,w r:=by
    rw [vB x E hzero (fun r hr=> (mem_filter.mp hr).2.1)
      hw.s0]
    congr 1
    · exact sum_congr rfl (fun r hr=> congrArg (fun a :ℝ=> a ^2) (hx r hr))
    · exact sum_congr rfl hx
  let E₀:= ∑ r ∈ qf w i b,w r
  let E₁:= ∑ r ∈ qf w i (!b),w r
  let S₀:= ∑ r ∈ qf w i b,w r^2
  let S₁:= ∑ r ∈ qf w i (!b),w r^2
  have hsplit: (∑ r ∈ E,w r) = E₀+E₁:=by
    dsimp only [E]
    rw [← xc hw i b hface,sum_union (w0 w i b)]
  have hsplitSq: (∑ r ∈ E,w r^2) = S₀+S₁:=by
    dsimp only [E]
    rw [← xc hw i b hface,sum_union (w0 w i b)]
  have hpart (r:q1) (hr:r ∈ E) :
      q0 r ⊆ q0 p ∨ q0 r ⊆ q0 q :=
    se i b r (mem_filter.mp hr).2.1
      (hw.compatible r p (mem_filter.mp hr).2.2 hface)
  have hgrad₀:qm x p=2*E₀-2:=
    sG w x i b hx hzero hpart
  have hgrad₁:qm x q=2*E₁-2:=by
    apply sG w x i (!b) hx hzero
    intro r hr
    simpa only [Bool.not_not] using (hpart r hr).symm
  have htotal:w p+E₀+w q+E₁=4:=by
    have ht: (∑ r,x r) + w p +w q=4:=by
      calc
        (∑ r,x r) + w p +w q=
            ∑ r,(((x+Pi.single p (w p)) + Pi.single q (w q)) : q1 → ℝ) r :=by
          simp [Pi.add_apply,sum_add_distrib]
        _= ∑ r,w r:=congrArg (fun f :q1 → ℝ=> ∑ r,f r) hdecomp.symm
        _=4:=hw.sum_four
    rw [hsum,hsplit] at ht
    linarith
  have hover:qb q p=0:= (sm q p).trans (zZ i b)
  have hfull:qd w =
      (w p) ^ 2+2*w p*E₀+S₀-2*w p-E₀+
        ((w q) ^ 2+2*w q*E₁+S₁-2*w q-E₁) :=by
    calc
      qd w =qd ((x+Pi.single p (w p)) + Pi.single q (w q)) :=
        congrArg qd hdecomp
      _=_:=by
        rw [rI,rI,uk,
          hgrad₀,hgrad₁,hover,henergy,hsplit,hsplitSq]
        ring
  constructor
  · rw [hfull]
    exact xZ (w p) (w q) E₀ E₁ S₀ S₁
      (sum_nonneg fun r _=> hw.nonneg r) (hw.ud i b)
      (sum_nonneg fun r _=> hw.nonneg r) (hw.ud i (!b))
      (hw.sf i b) (hw.sf i (!b)) htotal
  · intro hzero
    rw [hfull] at hzero
    exact y5 (w p) (w q) E₀ E₁ S₀ S₁
      (sum_nonneg fun r _=> hw.nonneg r) (hw.ud i b)
      (sum_nonneg fun r _=> hw.nonneg r) (hw.ud i (!b))
      (hw.sf i b) (hw.sf i (!b)) htotal hzero
theorem q6.zc {w:q1 → ℝ}
    (hw:q6 w) (i:Fin 3) (b:Bool) (hface:0 < w (cubeFace i b))
    (hhigh: ∀ r,2 ≤ q3 r → r ≠ cubeFace i b → r ≠ cubeFace i (!b) → w r =0) :
    0 ≤ qd w :=
  (hw.sQ i b hface hhigh).1
end Erdos556
namespace Erdos556
open Finset
theorem u5: ∀ (i:Fin 3) (b:Bool) (p:q1),
    2 ≤ q3 p → Disjoint (q0 (cubeFace i b)) (q0 p) →
      p=cubeFace i (!b) :=by
  decide
theorem uy (w:q1 → ℝ) (hw:q6 w)
    (hdisj: (qe w :Set q1).Pairwise
      (fun p q=> Disjoint (q0 p) (q0 q))) :
    0 ≤ qd w :=by
  classical
  by_cases hface: ∃ p:q1,q3 p =2 ∧ 0 < w p
  · obtain ⟨p,hpdim,hp⟩ :=hface
    obtain ⟨i,b,rfl⟩ := (u1 p).mp hpdim
    apply hw.zc i b hp
    intro r hr hrp hrq
    by_contra hrzero
    have hrpos:0 < w r:=lt_of_le_of_ne (hw.nonneg r) (Ne.symm hrzero)
    have hpH:cubeFace i b ∈ qe w :=
      mem_filter.mpr ⟨mem_univ _,by rw [r4],hp⟩
    have hrH:r ∈ qe w :=mem_filter.mpr ⟨mem_univ _,hr,hrpos⟩
    exact hrq (u5 i b r hr (hdisj hpH hrH hrp.symm))
  · have hhigh: ∀ p,2 ≤ q3 p → p ≠ qF → w p =0:=by
      intro p hpdim hpne
      have hdim3:q3 p ≠ 3 :=fun h => hpne ((sz p).mp h)
      have hmax:=sM p
      have hdim2:q3 p =2:=by omega
      have hnot: ¬ 0 < w p:=fun h => hface ⟨p,hdim2,h⟩
      exact le_antisymm (le_of_not_gt hnot) (hw.nonneg p)
    exact (hw.nonneg qF).trans (hw.u6 hhigh)
theorem zS (w:q1 → ℝ) (hw:q6 w) : 0 ≤ qd w :=by
  obtain ⟨v,hv,hdisj,henergy⟩ :=yW w hw
  exact (uy v hv hdisj).trans henergy
end Erdos556
open Finset

namespace LuczakProfile

-- Q is the quadratic overlap term and L the linear dimension term in
-- the cube-profile energy of the Kohayakawa–Simonovits–Skokan argument.
theorem mass_le_four {ι : Type*} [Fintype ι] (w : ι → ℝ)
    (Q L : (ι → ℝ) → ℝ)
    (hQ : ∀ a : ℝ, Q (fun i => a * w i) = a^2 * Q w)
    (hL : ∀ a : ℝ, L (fun i => a * w i) = a * L w)
    (hpos : 4 < ∑ i, w i → 0 < Q w)
    (henergy : Q w ≤ L w)
    (hnormal : ∀ a : ℝ, 0 < a → a ≤ 1 → (∑ i, a * w i) = 4 →
      L (fun i => a * w i) ≤ Q (fun i => a * w i)) :
    ∑ i, w i ≤ 4 := by
  by_contra! he
  let a := 4 / ∑ i, w i
  have hs : 0 < ∑ i, w i := by linarith
  have ha : 0 < a := div_pos (by norm_num) hs
  have halt : a < 1 := (div_lt_one hs).mpr he
  have hsum : (∑ i, a * w i) = 4 := by
    rw [← fsMS3]
    exact div_mul_cancel₀ _ hs.ne'
  have h := hnormal a ha halt.le hsum
  rw [hQ, hL, pow_two, mul_assoc] at h
  have hbound := (mul_le_mul_iff_right₀ ha).mp h
  have hstrict : a * Q w < 1 * Q w := mul_lt_mul_of_pos_right halt (hpos he)
  linarith

end LuczakProfile

namespace Erdos556

theorem asymptotic_cube_mass (w : q1 → ℝ) (hw : ∀ p, 0 ≤ w p)
    (hv : ∀ p, q3 p = 0 → w p = 0)
    (he : ∀ p, q3 p = 1 → w p ≤ 1)
    (hc : ∀ p q, 0 < w p → 0 < w q → (q0 p ∩ q0 q).card ≠ 1)
    (henergy : qd w ≤ 0) : ∑ p, w p ≤ 4 := by
  classical
  let Q := fun v : q1 → ℝ => ∑ p, ∑ q, qb p q * v p * v q
  let L := fun v : q1 → ℝ => ∑ p, (q3 p : ℝ) * v p
  apply LuczakProfile.mass_le_four w Q L
  · intro a
    dsimp only [Q]
    simp only [fsMS3]
    exact fsSC rfl fun p _ => fsSC rfl fun q _ => by ring
  · intro a
    dsimp only [L]
    simp only [fsMS3]
    exact fsSC rfl fun p _ => by ring
  · intro hmass
    have hex : ∃ p, 0 < w p := by
      by_contra! hall
      have h := Finset.sum_nonpos (fun i (_ : i ∈ fsUniv) => hall i)
      linarith
    obtain ⟨p, hp⟩ := hex
    have hb (i j : q1) : 0 ≤ qb i j := by unfold qb; split <;> norm_num
    have ht (i j : q1) : 0 ≤ qb i j * w i * w j :=
      mul_nonneg (mul_nonneg (hb i j) (hw i)) (hw j)
    have hdiag := Finset.single_le_sum (fun j _ => ht p j) (fsMU2 p)
    have hrow := Finset.single_le_sum (fun i (_ : i ∈ fsUniv) =>
      Finset.sum_nonneg (fun j (_ : j ∈ fsUniv) => ht i j)) (fsMU2 p)
    have hd : 0 < qb p p * w p * w p := by rw [vU, one_mul]; exact mul_pos hp hp
    exact (hd.trans_le hdiag).trans_le hrow
  · exact sub_nonpos.mp henergy
  · intro a ha ha1 hsum
    apply sub_nonneg.mp (zS _ ⟨fun p => mul_nonneg ha.le (hw p), hsum,
      fun p h => by simp [hv p h],
      fun p h => (mul_le_mul_of_nonneg_right ha1 (hw p)).trans (by simpa using he p h),
      fun p q hp hq => hc p q (pos_of_mul_pos_right hp ha.le) (pos_of_mul_pos_right hq ha.le)⟩)

end Erdos556
open Finset Filter
open scoped Topology
namespace Erdos556

structure LooseProfile (w : q1 → ℝ) (δ : ℝ) : Prop where
  nonneg : ∀ p, 0 ≤ w p
  mass : ∑ p, w p ≤ 7
  vertex : ∀ p, q3 p = 0 → w p ≤ δ
  edge : ∀ p, q3 p = 1 → w p ≤ 1 + δ
  pairs : ∀ p q, (q0 p ∩ q0 q).card = 1 → w p * w q ≤ δ
  energy : qd w ≤ δ

theorem asymptotic_mass_bound (η : ℝ) (hη : 0 < η) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w, LooseProfile w δ → ∑ p, w p ≤ 4 + η := by
  classical
  by_contra! h
  let ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hpos (n : ℕ) : 0 < ε n := by unfold ε; positivity
  choose w hw hlarge using fun n => h (ε n) (hpos n)
  let K : Set (q1 → ℝ) := Set.Icc (fun _ => 0) (fun _ => 7)
  have hK : IsCompact K := isCompact_Icc
  have hmem (n : ℕ) : w n ∈ K := by
    refine ⟨(hw n).nonneg, fun p => ?_⟩
    exact (single_le_sum (fun q _ => (hw n).nonneg q) (mem_univ p)).trans (hw n).mass
  obtain ⟨v, _, φ, hφ, hv⟩ := hK.tendsto_subseq hmem
  have hε : Tendsto (ε ∘ φ) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat.comp hφ.tendsto_atTop
  have hp (p : q1) := (tendsto_pi_nhds.mp hv) p
  have hn (p : q1) : 0 ≤ v p := ge_of_tendsto' (hp p) fun n => (hw (φ n)).nonneg p
  have hc : Continuous qd := by unfold qd; fun_prop
  have hm := asymptotic_cube_mass v hn
    (fun p hd => le_antisymm (le_of_tendsto_of_tendsto' (hp p) hε
      (fun n => (hw (φ n)).vertex p hd)) (hn p))
    (fun p hd => by
      have hlim := le_of_tendsto_of_tendsto' (hp p) (tendsto_const_nhds.add hε)
        (fun n => (hw (φ n)).edge p hd)
      simpa using hlim)
    (fun p q h₁ h₂ heq => (not_lt_of_ge (le_of_tendsto_of_tendsto'
      ((hp p).mul (hp q)) hε (fun n => (hw (φ n)).pairs p q heq))) (mul_pos h₁ h₂))
    (le_of_tendsto_of_tendsto' ((hc.tendsto v).comp hv) hε (fun n => (hw (φ n)).energy))
  have hs := tendsto_finsetSum univ (fun p _ => hp p)
  have hlow := ge_of_tendsto' hs (fun n => (hlarge (φ n)).le)
  linarith
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem tP (w:q1 → ℝ) (n:ℝ) :
    qO (fun p => w p/n) = qO w /n^2:=by
  unfold qO
  simp only [sum_div]
  apply sum_congr rfl
  intro p _
  apply sum_congr rfl
  intro q _
  split_ifs <;> simp [div_mul_div_comm,pow_two]
theorem yX (w:q1 → ℝ) (n:ℝ) (hn:n ≠ 0) :
    qd (fun p => w p/n) * n^2=
      (∑ p,w p) ^ 2-qO w -n* (∑ p,(q3 p :ℝ) * w p) :=by
  rw [zv,tP,← sum_div]
  have hsum: (∑ p,(q3 p :ℝ) * (w p /n)) =
      (∑ p,(q3 p :ℝ) * w p) / n:=by
    simp only [sum_div,mul_div_assoc]
  rw [hsum]
  field_simp
noncomputable def q2.rQ {V:Type*} [Fintype V] [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D)
    (n:ℝ) (p:q1) : ℝ:= (h.qa p).card/n
theorem q2.aH {V:Type*} [Fintype V] [DecidableEq V]
    {c:q4 V} {E D :ℝ} (h:q2 c E D) (n:ℝ) :
    (∑ p,h.rQ n p) = ftCard V /n:=by
  unfold rQ
  rw [← sum_div]
  congr 1
  exact_mod_cast h.xF
theorem q2.uC {V:Type*}
    [Fintype V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) (n:ℝ) (hn:n ≠ 0) :
    qd (h.rQ n) * n^2= (ftCard V :ℝ) ^ 2-
      qO (fun p => ((h.qa p).card:ℝ)) -
      n* (∑ p,(q3 p :ℝ) * (h.qa p).card) :=by
  unfold rQ
  rw [yX _ n hn]
  have hs: (∑ p,((h.qa p).card:ℝ)) = ftCard V :=by
    exact_mod_cast h.xF
  rw [hs]
theorem q2.yw {V:Type*}
    [Fintype V] [DecidableEq V] {c:q4 V} {E D :ℝ}
    (h:q2 c E D) (n:ℕ) (hn:8 ≤ n)
    (hno: ∀ i,¬ cycleGraph n ⊑ c.graph i) (δ:ℝ) (hδ:0 ≤ δ)
    (hsize: (ftCard V :ℝ) ≤ 7*n)
    (hvertex:6*E+ftCard V ≤ δ ^2* (n:ℝ) ^ 2)
    (hedge:48*E ≤ δ* (n:ℝ) ^ 2)
    (hpair:6*E+ftCard V ≤ δ * (n:ℝ) ^ 2)
    (henergy: (ftCard V :ℝ) + (2*D-n) *
        (∑ p,(q3 p :ℝ) * (h.qa p).card) + 6*E ≤ δ* (n:ℝ) ^ 2) :
    LooseProfile (h.rQ n) δ :=by
  have hnpos: (0:ℝ) < n:=by exact_mod_cast (show 0 < n by omega)
  have hnsq: (0:ℝ) < (n:ℝ) ^ 2:=sq_pos_of_pos hnpos
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro p
    exact div_nonneg (natCN _) hnpos.le
  · rw [h.aH]
    exact (div_le_iff₀ hnpos).mpr (by linarith)
  · intro p hp
    apply (div_le_iff₀ hnpos).mpr
    have hb:= (h.zQ p hp).trans hvertex
    have hm: (0:ℝ) ≤ (h.qa p).card:=by positivity
    have hdn:=mul_nonneg hδ hnpos.le
    nlinarith
  · intro p hp
    apply (div_le_iff₀ hnpos).mpr
    have hb:=h.t5 n hn hno p hp
    nlinarith
  · intro p q hpq
    dsimp only [rQ]
    rw [div_mul_div_comm,← pow_two]
    apply (div_le_iff₀ hnsq).mpr
    exact (h.su p q hpq).trans hpair
  · have he:=h.uC n hnpos.ne'
    have hb:= (h.yS n).trans henergy
    nlinarith
end Erdos556
namespace Erdos556
open SimpleGraph Finset
theorem vy (δ:ℝ) (hδ:0 < δ) :
    ∃ ε :ℝ,0 < ε ∧ ε ≤ δ ∧ ∃ n₀:ℕ,∀ {V:Type*} [Fintype V] [DecidableEq V]
      (c:q4 V) (n:ℕ),n₀ ≤ n → ftCard V ≤7*n →
      (∀ i,¬ cycleGraph n ⊑ c.graph i) →
      ∀ h :q2 c (ε* (ftCard V :ℝ) ^ 2)
        ((n:ℝ) / 2+ε*ftCard V),LooseProfile (h.rQ n) δ :=by
  let t :ℝ:=min δ (min (δ^2) 1)
  have ht:0 < t:=lt_min hδ (lt_min (sq_pos_of_pos hδ) zero_lt_one)
  have htδ:t ≤ δ:=min_le_left _ _
  have htδsq:t ≤ δ^2:= (min_le_right _ _).trans (min_le_left _ _)
  let ε :ℝ:=t/100000
  have hε:0 < ε:=div_pos ht (by norm_num)
  have hεδ:ε ≤ δ:=by
    have hεt:ε ≤ t:=by dsimp only [ε];nlinarith
    exact hεt.trans htδ
  obtain ⟨m,hm⟩ :=exists_nat_ge (100000/t)
  refine ⟨ε,hε,hεδ,max 8 m,?_⟩
  intro V _ _ c n hn hN hno h
  have hn8:8 ≤ n:= (le_max_left _ _).trans hn
  have hmn:m ≤ n:= (le_max_right _ _).trans hn
  have hnpos: (0:ℝ) < n:=by exact_mod_cast (show 0 < n by omega)
  have htn:100000 ≤ t*n:=by
    have hmnR: (m:ℝ) ≤ n:=by exact_mod_cast hmn
    have hh:= (div_le_iff₀ ht).mp (hm.trans hmnR)
    nlinarith
  have hNnonneg: (0:ℝ) ≤ ftCard V :=by positivity
  have hNle: (ftCard V :ℝ) ≤ 7*n:=by exact_mod_cast hN
  have hNsq: (ftCard V :ℝ) ^ 2 ≤ 49* (n:ℝ) ^ 2:=by nlinarith [sq_nonneg (7*(n:ℝ) - ftCard V), mul_nonneg (sub_nonneg.mpr hNle) (add_nonneg (by positivity : 0 ≤ 7*(n:ℝ)) hNnonneg)]
  have heq:100000*ε=t:=by dsimp only [ε];ring
  have hlarge:100000* (n:ℝ) ≤ t* (n:ℝ) ^ 2:=by
    nlinarith [mul_le_mul_of_nonneg_right htn hnpos.le]
  have hcommon: (ftCard V :ℝ) + 48* (ε* (ftCard V :ℝ) ^ 2) ≤
      t* (n:ℝ) ^ 2:=by
    have hscaled:=mul_le_mul_of_nonneg_left hNsq hε.le
    have heqscaled:100000*ε* (n:ℝ) ^ 2=t* (n:ℝ) ^ 2:=by rw [heq]
    nlinarith [mul_nonneg ht.le (sq_nonneg (n:ℝ))]
  have htδn:=mul_le_mul_of_nonneg_right htδ (sq_nonneg (n:ℝ))
  have htδsqn:=mul_le_mul_of_nonneg_right htδsq (sq_nonneg (n:ℝ))
  have hE:0 ≤ ε* (ftCard V :ℝ) ^ 2:=mul_nonneg hε.le (sq_nonneg _)
  apply h.yw n hn8 hno δ hδ.le
  · exact hNle
  · linarith
  · linarith
  · linarith
  · have hW:=h.wR
    have hmul:=mul_le_mul_of_nonneg_left hW (mul_nonneg (by positivity: (0:ℝ) ≤ 2*ε)
      hNnonneg)
    nlinarith
end Erdos556


section R1Section
-- Reduction Erdos556.erdos_556.variants.luczak_asymptotic_even.R1 of Erdős Problem 556 — luczak asymptotic even
-- Credit: @green-notes
-- Each H becomes its own step once this file is accepted. Proving all of them closes the problem.

/-
# Łuczak's asymptotic bound for even cycles via Szemerédi regularity and connected matchings

We reduce `Erdos556.erdos_556.variants.luczak_asymptotic_even` (`R(C_n; 3) ≤ (3 + ε)n` for large
even `n`) to two independent combinatorial pillars, while discharging the pigeonhole edge-counting
and Szemerédi regularity cluster-graph extraction directly inside this reduction:

* `H1`: Connected matching density lemma — any graph on `t` vertices with strictly more than
  `(k - 1) * t` edges contains a matching of size at least `k` inside a single connected
  component (Erdős–Gallai / Tutte–Berge).
* `H2`: Łuczak's blow-up / cycle-embedding lemma — a connected matching of `k` edges in an
  `η`-uniform, `d`-dense cluster graph with equipartite parts of size `m` embeds `C_n` for every
  even `4 ≤ n ≤ (1 - δ) * 2 * k * m` once `m` is sufficiently large relative to `(d, δ, t)`.
-/

namespace OMA.Erdos556R1

open Filter SimpleGraph Finset

/-- Connected matching density lemma: any graph on `t` vertices with strictly more than
`(k - 1) * t` edges contains a matching covering at least `2 * k` vertices within a single
connected component. -/
def H1 : Prop :=
  ∀ (t k : ℕ) (R : SimpleGraph (Fin t)) [DecidableRel R.Adj],
    1 ≤ k → (k - 1) * t < R.edgeFinset.card →
    ∃ M : R.Subgraph, M.IsMatching ∧ 2 * k ≤ M.verts.ncard ∧
      ∀ u ∈ M.verts, ∀ v ∈ M.verts, R.Reachable u v

/-- Łuczak's connected-matching blow-up lemma for even cycles: given density `d > 0` and slack
`δ ∈ (0, 1)`, there exists regularity parameter `η > 0` such that for any number of clusters `t`
and sufficiently large equipartite part size `m ≥ m₀`, any `η`-uniform `d`-dense cluster graph `R`
with a connected matching `M` covering at least `2 * k` clusters embeds `C_n` in `G` for all even
`4 ≤ n ≤ (1 - δ) * (2 * k * m)`. -/
def H2 : Prop :=
  ∀ (d δ : ℝ), 0 < d → 0 < δ → δ < 1 →
    ∃ η > (0 : ℝ), ∀ (t : ℕ), ∃ m₀ : ℕ,
      ∀ (N n m k : ℕ) (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
        (parts : Fin t → Finset (Fin N)) (R : SimpleGraph (Fin t)) (M : R.Subgraph),
        Even n → 4 ≤ n → 1 ≤ k → m₀ ≤ m → (n : ℝ) ≤ (1 - δ) * (2 * (k : ℝ) * (m : ℝ)) →
        Pairwise (fun i j => Disjoint (parts i) (parts j)) →
        (∀ i : Fin t, m ≤ (parts i).card ∧ (parts i).card ≤ m + 1) →
        (∀ u v : Fin t, R.Adj u v →
          G.IsUniform η (parts u) (parts v) ∧ (d : ℝ) ≤ (G.edgeDensity (parts u) (parts v) : ℝ)) →
        M.IsMatching → 2 * k ≤ M.verts.ncard →
        (∀ u ∈ M.verts, ∀ v ∈ M.verts, R.Reachable u v) →
        (cycleGraph n).IsContained G

lemma dense_color_of_three_colouring (N : ℕ) (c : Fin 3 → SimpleGraph (Fin N))
    [∀ i, DecidableRel (c i).Adj]
    (hc : (⊤ : SimpleGraph (Fin N)).IsEdgeColouring c) :
    ∃ i : Fin 3, N * (N - 1) ≤ 6 * (c i).edgeFinset.card := by
  have hcov : (⊤ : SimpleGraph (Fin N)).edgeFinset ⊆
      (fsUniv : Finset (Fin 3)).biUnion (fun i => (c i).edgeFinset) := by
    intro e he
    induction e using Sym2.ind with
    | _ x y =>
      rw [mem_edgeFinset, mem_edgeSet, top_adj] at he
      have hi : (⨆ i, c i).Adj x y := by rw [← hc.1]; exact (top_adj x y).mpr he
      rw [iSup_adj] at hi
      obtain ⟨i, hi⟩ := hi
      exact mem_biUnion.mpr ⟨i, mem_univ i, mem_edgeFinset.mpr hi⟩
  have hcard : (⊤ : SimpleGraph (Fin N)).edgeFinset.card ≤
      ∑ i : Fin 3, (c i).edgeFinset.card :=
    (fsCLC hcov).trans fsCBL
  have htop : (⊤ : SimpleGraph (Fin N)).edgeFinset.card = Nat.choose N 2 := by
    convert SimpleGraph.card_edgeFinset_top_eq_card_choose_two (V := Fin N)
    simp
  have hchoose : 2 * Nat.choose N 2 = N * (N - 1) := by
    rw [Nat.choose_two_right]
    exact Nat.mul_div_cancel' (Nat.even_mul_pred_self N).two_dvd
  rw [htop] at hcard
  have hsum : ∑ i : Fin 3, (c i).edgeFinset.card =
      (c 0).edgeFinset.card + (c 1).edgeFinset.card + (c 2).edgeFinset.card := by
    simp [Fin.sum_univ_three, add_assoc]
  have hmax : ∃ i : Fin 3, Nat.choose N 2 ≤ 3 * (c i).edgeFinset.card := by
    by_contra! h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    omega
  obtain ⟨i, hi⟩ := hmax
  exact ⟨i, by omega⟩

lemma regularity_cluster_graph (N : ℕ) (hN : 0 < N)
    (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (hG : N * (N - 1) ≤ 6 * G.edgeFinset.card)
    (η d : ℝ) (hη : 0 < η) (hd : 0 ≤ d) (l : ℕ) (hl : l ≤ N) (hl_pos : 0 < l) :
    ∃ (t : ℕ) (parts : Fin t → Finset (Fin N)) (R : SimpleGraph (Fin t))
      (_ : DecidableRel R.Adj),
      l ≤ t ∧ t ≤ SzemerediRegularity.bound η l ∧
      Pairwise (fun i j => Disjoint (parts i) (parts j)) ∧
      (∀ i : Fin t, N / t ≤ (parts i).card ∧ (parts i).card ≤ N / t + 1) ∧
      (∀ u v : Fin t, R.Adj u v →
        G.IsUniform η (parts u) (parts v) ∧ d ≤ (G.edgeDensity (parts u) (parts v) : ℝ)) ∧
      (N : ℝ) * (N - 1) / 3 ≤
        (N : ℝ) * (N + t) / t + η * (N + t) ^ 2 + d * (N + t) ^ 2 +
          2 * (R.edgeFinset.card : ℝ) * ((N / t : ℕ) + 1 : ℝ) ^ 2 := by
  classical
  have hl_card : l ≤ ftCard (Fin N) := by simpa using hl
  obtain ⟨P, hP₁, hP₂, hP₃, hP₄⟩ := szemeredi_regularity G hη hl_card
  set t := P.parts.card
  have ht_pos : 0 < t := lt_of_lt_of_le hl_pos hP₂
  let e : Fin t ≃ P.parts := (Finset.equivFin P.parts).symm
  let parts : Fin t → Finset (Fin N) := fun i => (e i).1
  let R : SimpleGraph (Fin t) :=
    { Adj := fun u v => u ≠ v ∧ G.IsUniform η (parts u) (parts v) ∧
        d ≤ (G.edgeDensity (parts u) (parts v) : ℝ)
      symm := ⟨fun u v ⟨hne, hu, hd_uv⟩ =>
        ⟨hne.symm, hu.symm, by rwa [sgEC]⟩⟩
      loopless := ⟨fun u ⟨hne, _⟩ => hne rfl⟩ }
  letI : DecidableRel R.Adj := Classical.decRel R.Adj
  refine ⟨t, parts, R, inferInstance, hP₂, hP₃, ?_, ?_, ?_, ?_⟩
  · intro i j hij
    exact P.disjoint (e i).2 (e j).2 (fun h => hij (e.injective (subExt h)))
  · intro i
    have hmem : parts i ∈ P.parts := (e i).2
    have h1 := hP₁.average_le_card_part hmem
    have h2 := hP₁.card_part_le_average_add_one hmem
    simp only [fsCU, ftCF] at h1 h2
    exact ⟨h1, h2⟩
  · intro u v huv
    exact ⟨huv.2.1, huv.2.2⟩
  · have hA : (fsUniv : Finset (Fin N)).Nonempty := ⟨⟨0, hN⟩, fsMU2 _⟩
    let densePairs : Finset (Finset (Fin N) × Finset (Fin N)) :=
      P.parts.offDiag.filter (fun uv => G.IsUniform η uv.1 uv.2 ∧
        d ≤ (G.edgeDensity uv.1 uv.2 : ℝ))
    have hsub : (fsUniv ×ˢ fsUniv).filter (fun xy : Fin N × Fin N => G.Adj xy.1 xy.2) ⊆
        (P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2) ∪
          P.parts.biUnion Finset.offDiag ∪
          (P.sparsePairs G d).biUnion (fun uv => G.interedges uv.1 uv.2) ∪
          densePairs.biUnion (fun uv => G.interedges uv.1 uv.2) := by
      rintro ⟨x, y⟩ hxy
      simp only [fsMF, fsMP, fsMU2, true_and] at hxy
      obtain ⟨U, hU, hx⟩ := P.exists_mem (fsMU2 x)
      obtain ⟨V, hV, hy⟩ := P.exists_mem (fsMU2 y)
      by_cases hUV : U = V
      · subst hUV
        refine fsMUL _ (fsMUL _ (fsMUR _ ?_))
        exact fsMB.mpr ⟨U, hU, fsMO.mpr ⟨hx, hy, G.ne_of_adj hxy⟩⟩
      · by_cases huni : G.IsUniform η U V
        · by_cases hd_uv : d ≤ (G.edgeDensity U V : ℝ)
          · refine fsMUR _ (fsMB.mpr ⟨(U, V), ?_, ?_⟩)
            · exact fsMF.mpr ⟨fsMO.mpr ⟨hU, hV, hUV⟩, huni, hd_uv⟩
            · exact G.mk_mem_interedges_iff.mpr ⟨hx, hy, hxy⟩
          · refine fsMUL _ (fsMUR _ ?_)
            refine fsMB.mpr ⟨(U, V), ?_, G.mk_mem_interedges_iff.mpr ⟨hx, hy, hxy⟩⟩
            exact (P.mk_mem_sparsePairs G U V d).mpr ⟨hU, hV, hUV, not_le.mp hd_uv⟩
        · refine fsMUL _ (fsMUL _ (fsMUL _ ?_))
          refine fsMB.mpr ⟨(U, V), ?_, fsMP.mpr ⟨hx, hy⟩⟩
          exact (P.mk_mem_nonUniforms G).mpr ⟨hU, hV, hUV, huni⟩
    have hcard_edges : 2 * G.edgeFinset.card ≤
        ((P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2)).card +
        (P.parts.biUnion Finset.offDiag).card +
        ((P.sparsePairs G d).biUnion (fun uv => G.interedges uv.1 uv.2)).card +
        (densePairs.biUnion (fun uv => G.interedges uv.1 uv.2)).card := by
      have h2 := G.two_mul_card_edgeFinset
      rw [Finset.univ_product_univ] at hsub
      have hc := fsCLC hsub
      rw [← h2] at hc
      exact hc.trans (by
        refine (fsCUL _ _).trans (natALAR ?_ _)
        refine (fsCUL _ _).trans (natALAR ?_ _)
        exact fsCUL _ _)
    have h_dense_card : densePairs.card = 2 * R.edgeFinset.card := by
      have h2R := R.two_mul_card_edgeFinset
      rw [← Finset.univ_product_univ] at h2R
      rw [h2R]
      symm
      refine Finset.card_bij (fun uv _ => (parts uv.1, parts uv.2)) ?_ ?_ ?_
      · intro ⟨u, v⟩ huv
        simp only [fsMF, fsMP, fsMU2, true_and] at huv
        refine fsMF.mpr ⟨fsMO.mpr ⟨(e u).2, (e v).2, ?_⟩, huv.2.1, huv.2.2⟩
        exact fun h => huv.1 (e.injective (subExt h))
      · intro ⟨u₁, v₁⟩ _ ⟨u₂, v₂⟩ _ heq
        simp only [Prod.mk.injEq] at heq
        exact Prod.ext (e.injective (subExt heq.1)) (e.injective (subExt heq.2))
      · intro ⟨U, V⟩ hUV
        simp only [densePairs, fsMF, fsMO] at hUV
        obtain ⟨⟨hU, hV, hne⟩, huni, hd_uv⟩ := hUV
        refine ⟨(e.symm ⟨U, hU⟩, e.symm ⟨V, hV⟩), ?_, ?_⟩
        · simp only [fsMF, fsMP, fsMU2, true_and]
          refine ⟨fun h => hne ?_, ?_, ?_⟩
          · exact congrArg subVal (e.symm.injective h)
          · simpa [parts] using huni
          · simpa [parts] using hd_uv
        · simp [parts]
    have h_dense_inter : ((densePairs.biUnion (fun uv => G.interedges uv.1 uv.2)).card : ℝ) ≤
        2 * (R.edgeFinset.card : ℝ) * ((N / t : ℕ) + 1 : ℝ) ^ 2 := by
      have h1 : (densePairs.biUnion (fun uv => G.interedges uv.1 uv.2)).card ≤
          ∑ uv ∈ densePairs, (G.interedges uv.1 uv.2).card := fsCBL
      have h2 : ∑ uv ∈ densePairs, (G.interedges uv.1 uv.2).card ≤
          densePairs.card * (N / t + 1) ^ 2 := by
        calc ∑ uv ∈ densePairs, (G.interedges uv.1 uv.2).card
            ≤ ∑ _uv ∈ densePairs, (N / t + 1) ^ 2 := by
              refine fsSLS fun uv huv => ?_
              have hmem := fsMO.mp (fsMF.mp huv).1
              have hu := hP₁.card_part_le_average_add_one hmem.1
              have hv := hP₁.card_part_le_average_add_one hmem.2.1
              simp only [fsCU, ftCF] at hu hv
              rw [sq]
              exact (G.card_interedges_le_mul uv.1 uv.2).trans (Nat.mul_le_mul hu hv)
          _ = densePairs.card * (N / t + 1) ^ 2 := by simp
      have h3 : (densePairs.biUnion (fun uv => G.interedges uv.1 uv.2)).card ≤
          2 * R.edgeFinset.card * (N / t + 1) ^ 2 := by
        rw [← h_dense_card]
        exact h1.trans h2
      exact_mod_cast h3
    have h_nonuni : (((P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2)).card : ℝ) ≤
        η * ((N : ℝ) + t) ^ 2 := by
      have h1 : ((P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2)).card ≤
          ∑ uv ∈ P.nonUniforms G η, uv.1.card * uv.2.card := by
        calc ((P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2)).card
            ≤ ∑ uv ∈ P.nonUniforms G η, (uv.1 ×ˢ uv.2).card := fsCBL
          _ = ∑ uv ∈ P.nonUniforms G η, uv.1.card * uv.2.card := by
              refine fsSC rfl fun uv _ => Finset.card_product _ _
      have h2 := hP₁.sum_nonUniforms_lt' (𝕜 := ℝ) hA hη hP₄
      simp only [fsCU, ftCF] at h2
      have h2le : (∑ uv ∈ P.nonUniforms G η, (#uv.1 : ℝ) * (#uv.2 : ℝ)) ≤ η * ((N : ℝ) + t) ^ 2 := by
        simpa [t] using h2.le
      calc (((P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2)).card : ℝ)
          ≤ ((∑ uv ∈ P.nonUniforms G η, uv.1.card * uv.2.card : ℕ) : ℝ) := natCL.mpr h1
        _ = ∑ uv ∈ P.nonUniforms G η, (#uv.1 : ℝ) * (#uv.2 : ℝ) := by push_cast; rfl
        _ ≤ η * ((N : ℝ) + t) ^ 2 := h2le
    have h_off : ((P.parts.biUnion Finset.offDiag).card : ℝ) ≤ (N : ℝ) * ((N : ℝ) + t) / t := by
      have h := hP₁.card_biUnion_offDiag_le' (𝕜 := ℝ)
      simpa [t] using h
    have h_sparse : (((P.sparsePairs G d).biUnion (fun uv => G.interedges uv.1 uv.2)).card : ℝ) ≤
        d * ((N : ℝ) + t) ^ 2 := by
      have h := hP₁.card_interedges_sparsePairs_le' (G := G) (ε := d) hd
      simpa [t] using h
    have hG_real : (N : ℝ) * ((N : ℝ) - 1) / 3 ≤ 2 * (G.edgeFinset.card : ℝ) := by
      have hG' : (N : ℝ) * ((N : ℝ) - 1) ≤ 6 * (G.edgeFinset.card : ℝ) := by
        have hcast : ((N * (N - 1) : ℕ) : ℝ) ≤ ((6 * G.edgeFinset.card : ℕ) : ℝ) :=
          natCL.mpr hG
        rw [natCM, Nat.cast_sub hN, Nat.cast_one] at hcast
        push_cast at hcast
        exact hcast
      linarith
    have hcard_real : 2 * (G.edgeFinset.card : ℝ) ≤
        (((P.nonUniforms G η).biUnion (fun uv => uv.1 ×ˢ uv.2)).card : ℝ) +
        ((P.parts.biUnion Finset.offDiag).card : ℝ) +
        (((P.sparsePairs G d).biUnion (fun uv => G.interedges uv.1 uv.2)).card : ℝ) +
        ((densePairs.biUnion (fun uv => G.interedges uv.1 uv.2)).card : ℝ) := by
      exact_mod_cast hcard_edges
    linarith

lemma cluster_edge_bound (ε' η d : ℝ) (N t k eR : ℕ)
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1)
    (hη_le : η ≤ ε' / 1000) (hd_le : d ≤ ε' / 1000)
    (ht_pos : 0 < t) (hN_pos : 0 < N)
    (ht_ge : 1000 / ε' ≤ (t : ℝ))
    (ht_leN : (t : ℝ) ≤ ε' / 10000 * (N : ℝ))
    (hk_le : (k : ℝ) ≤ (t : ℝ) / (6 + ε' / 2))
    (hR_ineq : (N : ℝ) * ((N : ℝ) - 1) / 3 ≤
      (N : ℝ) * ((N : ℝ) + (t : ℝ)) / (t : ℝ) +
      η * ((N : ℝ) + (t : ℝ)) ^ 2 + d * ((N : ℝ) + (t : ℝ)) ^ 2 +
      2 * (eR : ℝ) * ((↑(N / t) : ℝ) + 1) ^ 2) :
    (k - 1) * t < eR := by
  have ht_real_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos
  have hN_real_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN_pos
  have hN_ge_inv : (10000 : ℝ) / ε' ≤ (N : ℝ) / (t : ℝ) := by
    rw [div_le_div_iff₀ hε' ht_real_pos]
    have h1 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 10000)).mp
      (by linarith : (t : ℝ) ≤ ε' * (N : ℝ) / 10000)
    linarith
  have h_one_le_Nt : (1 : ℝ) ≤ ε' / 10000 * ((N : ℝ) / (t : ℝ)) := by
    have h1 := (div_le_iff₀ hε').mp hN_ge_inv
    linarith
  have ht_ge1 : (1 : ℝ) ≤ (t : ℝ) := by exact_mod_cast ht_pos
  have h_one_le_N : (1 : ℝ) ≤ ε' / 10000 * (N : ℝ) := by
    have hNt1 : (N : ℝ) / (t : ℝ) ≤ (N : ℝ) := div_le_self hN_real_pos.le ht_ge1
    nlinarith
  have h_m_cast_le : (↑(N / t) : ℝ) ≤ (N : ℝ) / (t : ℝ) :=
    (le_div_iff₀ ht_real_pos).mpr (by exact_mod_cast natDMLS N t)
  have h_N_add_t : (N : ℝ) + (t : ℝ) ≤ (1 + ε' / 10000) * (N : ℝ) := by linarith
  have h_N_sub_1 : (1 - ε' / 10000) * (N : ℝ) ≤ (N : ℝ) - 1 := by linarith
  have h_m_add_1 : (↑(N / t) : ℝ) + 1 ≤ (1 + ε' / 10000) * ((N : ℝ) / (t : ℝ)) := by linarith
  have h_inv_t : (1 : ℝ) / (t : ℝ) ≤ ε' / 1000 := by
    rw [div_le_div_iff₀ ht_real_pos (by norm_num), one_mul]
    linarith only [(div_le_iff₀ hε').mp ht_ge]
  have hLHS : (1 - ε' / 10000) / 3 * (N : ℝ) ^ 2 ≤ (N : ℝ) * ((N : ℝ) - 1) / 3 := by
    have hmul := mul_le_mul_of_nonneg_left h_N_sub_1 hN_real_pos.le
    linarith
  have h_off_term : (N : ℝ) * ((N : ℝ) + (t : ℝ)) / (t : ℝ) ≤
      (ε' / 1000) * (1 + ε' / 10000) * (N : ℝ) ^ 2 := by
    have h1 : (N : ℝ) * ((N : ℝ) + (t : ℝ)) / (t : ℝ) =
        ((N : ℝ) * ((N : ℝ) + (t : ℝ))) * (1 / (t : ℝ)) := by ring
    rw [h1]
    have h2 : (N : ℝ) * ((N : ℝ) + (t : ℝ)) ≤ (N : ℝ) * ((1 + ε' / 10000) * (N : ℝ)) := by
      gcongr
    calc ((N : ℝ) * ((N : ℝ) + (t : ℝ))) * (1 / (t : ℝ))
        ≤ ((N : ℝ) * ((1 + ε' / 10000) * (N : ℝ))) * (ε' / 1000) := by
          gcongr
      _ = (ε' / 1000) * (1 + ε' / 10000) * (N : ℝ) ^ 2 := by ring
  have h_sq_term : (η + d) * ((N : ℝ) + (t : ℝ)) ^ 2 ≤
      (ε' / 500) * (1 + ε' / 10000) ^ 2 * (N : ℝ) ^ 2 := by
    have hsq : ((N : ℝ) + (t : ℝ)) ^ 2 ≤ ((1 + ε' / 10000) * (N : ℝ)) ^ 2 := by gcongr
    have hhd : η + d ≤ ε' / 500 := by linarith
    calc (η + d) * ((N : ℝ) + (t : ℝ)) ^ 2
        ≤ (ε' / 500) * ((1 + ε' / 10000) * (N : ℝ)) ^ 2 := by gcongr
      _ = (ε' / 500) * (1 + ε' / 10000) ^ 2 * (N : ℝ) ^ 2 := by ring
  have h_edge_term : 2 * (eR : ℝ) * ((↑(N / t) : ℝ) + 1) ^ 2 ≤
      2 * (eR : ℝ) * ((1 + ε' / 10000) ^ 2 * (N : ℝ) ^ 2 / (t : ℝ) ^ 2) := by
    have hsq : ((↑(N / t) : ℝ) + 1) ^ 2 ≤ ((1 + ε' / 10000) * ((N : ℝ) / (t : ℝ))) ^ 2 := by
      gcongr
    have hsq' : ((1 + ε' / 10000) * ((N : ℝ) / (t : ℝ))) ^ 2 =
        (1 + ε' / 10000) ^ 2 * (N : ℝ) ^ 2 / (t : ℝ) ^ 2 := by ring
    rw [← hsq']
    gcongr
  have hN2_pos : (0 : ℝ) < (N : ℝ) ^ 2 := by positivity
  have h_comb : (1 / 3 - 0.0034 * ε') * (N : ℝ) ^ 2 ≤
      2 * (eR : ℝ) * ((1 + ε' / 10000) ^ 2 * (N : ℝ) ^ 2 / (t : ℝ) ^ 2) := by
    have h_num1 : (ε' / 1000) * (1 + ε' / 10000) ≤ 0.0011 * ε' := by nlinarith only [hε', hε'1]
    have hsq_bnd : (1 + ε' / 10000) ^ 2 ≤ 1.05 := by nlinarith only [hε', hε'1]
    have h_num2 : (ε' / 500) * (1 + ε' / 10000) ^ 2 ≤ 0.0021 * ε' := by
      nlinarith only [hε', hsq_bnd]
    have h_num3 : 1 / 3 - 0.0001 * ε' ≤ (1 - ε' / 10000) / 3 := by linarith
    have h1 : (1 / 3 - 0.0001 * ε') * (N : ℝ) ^ 2 ≤ (N : ℝ) * ((N : ℝ) - 1) / 3 := by
      nlinarith only [h_num3, hLHS, hN2_pos]
    have h2 : (N : ℝ) * ((N : ℝ) + (t : ℝ)) / (t : ℝ) ≤ 0.0011 * ε' * (N : ℝ) ^ 2 := by
      nlinarith only [h_num1, h_off_term, hN2_pos]
    have h3 : (η + d) * ((N : ℝ) + (t : ℝ)) ^ 2 ≤ 0.0021 * ε' * (N : ℝ) ^ 2 := by
      nlinarith only [h_num2, h_sq_term, hN2_pos]
    have h3' : η * ((N : ℝ) + (t : ℝ)) ^ 2 + d * ((N : ℝ) + (t : ℝ)) ^ 2 ≤
        0.0021 * ε' * (N : ℝ) ^ 2 := by
      linarith only [h3, show (η + d) * ((N : ℝ) + (t : ℝ)) ^ 2 =
        η * ((N : ℝ) + (t : ℝ)) ^ 2 + d * ((N : ℝ) + (t : ℝ)) ^ 2 by ring]
    have h_epsN2 : 0 ≤ ε' * (N : ℝ) ^ 2 := by positivity
    linarith only [hR_ineq, h1, h2, h3', h_edge_term, h_epsN2]
  have h_divN : (1 / 3 - 0.0034 * ε') ≤
      2 * (eR : ℝ) * (1 + ε' / 10000) ^ 2 / (t : ℝ) ^ 2 := by
    have h_eq : 2 * (eR : ℝ) * ((1 + ε' / 10000) ^ 2 * (N : ℝ) ^ 2 / (t : ℝ) ^ 2) =
        (2 * (eR : ℝ) * (1 + ε' / 10000) ^ 2 / (t : ℝ) ^ 2) * (N : ℝ) ^ 2 := by ring
    rw [h_eq] at h_comb
    exact le_of_mul_le_mul_right h_comb hN2_pos
  have h_mul_t : (1 / 3 - 0.0034 * ε') * (t : ℝ) ^ 2 ≤
      2 * (eR : ℝ) * (1 + ε' / 10000) ^ 2 :=
    (le_div_iff₀ (by positivity)).mp h_divN
  have h_k_le : ((k - 1 : ℕ) : ℝ) * (t : ℝ) ≤ (t : ℝ) ^ 2 / (6 + ε' / 2) := by
    have hkm1 : ((k - 1 : ℕ) : ℝ) ≤ (k : ℝ) := by exact_mod_cast Nat.sub_le k 1
    calc ((k - 1 : ℕ) : ℝ) * (t : ℝ)
        ≤ (k : ℝ) * (t : ℝ) := by gcongr
      _ ≤ ((t : ℝ) / (6 + ε' / 2)) * (t : ℝ) := by gcongr
      _ = (t : ℝ) ^ 2 / (6 + ε' / 2) := by ring
  have h_strict : 2 * ((t : ℝ) ^ 2 / (6 + ε' / 2)) * (1 + ε' / 10000) ^ 2 <
      (1 / 3 - 0.0034 * ε') * (t : ℝ) ^ 2 := by
    have h6 : 0 < 6 + ε' / 2 := by linarith
    have ht2 : (0 : ℝ) < (t : ℝ) ^ 2 := by positivity
    suffices hcoef : 2 * (1 + ε' / 10000) ^ 2 < (1 / 3 - 0.0034 * ε') * (6 + ε' / 2) by
      have hmul : 2 * ((t : ℝ) ^ 2 / (6 + ε' / 2)) * (1 + ε' / 10000) ^ 2 =
          (2 * (1 + ε' / 10000) ^ 2 / (6 + ε' / 2)) * (t : ℝ) ^ 2 := by ring
      rw [hmul]
      exact mul_lt_mul_of_pos_right ((div_lt_iff₀ h6).mpr hcoef) ht2
    nlinarith only [hε', hε'1]
  have h_final_real : ((k - 1 : ℕ) : ℝ) * (t : ℝ) < (eR : ℝ) := by
    have hpos_c : (0 : ℝ) < 2 * (1 + ε' / 10000) ^ 2 := by positivity
    have h1 : 2 * (((k - 1 : ℕ) : ℝ) * (t : ℝ)) * (1 + ε' / 10000) ^ 2 ≤
        2 * ((t : ℝ) ^ 2 / (6 + ε' / 2)) * (1 + ε' / 10000) ^ 2 := by
      gcongr
    have h2 : 2 * (((k - 1 : ℕ) : ℝ) * (t : ℝ)) * (1 + ε' / 10000) ^ 2 <
        2 * (eR : ℝ) * (1 + ε' / 10000) ^ 2 := by
      linarith only [h1, h_strict, h_mul_t]
    nlinarith only [h2, hpos_c]
  exact_mod_cast h_final_real

lemma blowup_size_bound (ε' δ : ℝ) (N n t m k : ℕ)
    (hε' : 0 < ε') (hε'1 : ε' ≤ 1) (hδ : δ = ε' / 20)
    (ht_pos : 0 < t) (hn_pos : (0 : ℝ) < (n : ℝ))
    (ht_ge : 1000 / ε' ≤ (t : ℝ))
    (ht_leN : (t : ℝ) ≤ ε' / 10000 * (N : ℝ))
    (hN_ge : (3 + ε') * (n : ℝ) - 1 < (N : ℝ))
    (h_n_big : 10000 / ε' ≤ 3 * (n : ℝ))
    (hk_gt : (t : ℝ) / (6 + ε' / 2) - 1 < (k : ℝ))
    (hm_gt : (N : ℝ) / (t : ℝ) - 1 < (m : ℝ)) :
    (n : ℝ) ≤ (1 - δ) * (2 * (k : ℝ) * (m : ℝ)) := by
  have ht_real_pos : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht_pos
  have h_one_lt_tk : (1 : ℝ) < (ε' / 100) * ((t : ℝ) / (6 + ε' / 2)) := by
    rw [div_mul_div_comm, lt_div_iff₀ (by positivity)]
    have h1 : (1000 : ℝ) ≤ ε' * (t : ℝ) := by linarith only [(div_le_iff₀ hε').mp ht_ge]
    linarith
  have hk_lower : (1 - ε' / 100) * ((t : ℝ) / (6 + ε' / 2)) < (k : ℝ) := by linarith
  have hN_ge_inv : (10000 : ℝ) / ε' ≤ (N : ℝ) / (t : ℝ) := by
    rw [div_le_div_iff₀ hε' ht_real_pos]
    have h1 := (le_div_iff₀ (by norm_num : (0 : ℝ) < 10000)).mp
      (by linarith : (t : ℝ) ≤ ε' * (N : ℝ) / 10000)
    linarith
  have h_one_le_Nt : (1 : ℝ) ≤ ε' / 10000 * ((N : ℝ) / (t : ℝ)) := by
    have h1 := (div_le_iff₀ hε').mp hN_ge_inv
    linarith
  have hm_lower : (1 - ε' / 10000) * ((N : ℝ) / (t : ℝ)) < (m : ℝ) := by linarith
  have hN_lower : (3 + 0.99 * ε') * (n : ℝ) ≤ (N : ℝ) := by
    have h1 : (1 : ℝ) ≤ 0.01 * ε' * (n : ℝ) := by
      have h2 := (div_le_iff₀ hε').mp h_n_big
      linarith
    linarith
  have hm_lower2 : (1 - ε' / 10000) * ((3 + 0.99 * ε') * (n : ℝ) / (t : ℝ)) ≤ (m : ℝ) := by
    have h1 : (3 + 0.99 * ε') * (n : ℝ) / (t : ℝ) ≤ (N : ℝ) / (t : ℝ) := by gcongr
    have h2 : 0 ≤ (1 - ε' / 10000) := by linarith
    nlinarith only [h1, h2, hm_lower]
  have h_prod : (1 - ε' / 20) * (2 * ((1 - ε' / 100) * ((t : ℝ) / (6 + ε' / 2))) *
      ((1 - ε' / 10000) * ((3 + 0.99 * ε') * (n : ℝ) / (t : ℝ)))) ≤
      (1 - δ) * (2 * (k : ℝ) * (m : ℝ)) := by
    rw [hδ]
    have hk0 : 0 ≤ (1 - ε' / 100) * ((t : ℝ) / (6 + ε' / 2)) :=
      mul_nonneg (by linarith) (by positivity)
    have hm0 : 0 ≤ (1 - ε' / 10000) * ((3 + 0.99 * ε') * (n : ℝ) / (t : ℝ)) :=
      mul_nonneg (by linarith) (by positivity)
    have hd0 : 0 ≤ 1 - ε' / 20 := by linarith
    gcongr
  have h_simp : (1 - ε' / 20) * (2 * ((1 - ε' / 100) * ((t : ℝ) / (6 + ε' / 2))) *
      ((1 - ε' / 10000) * ((3 + 0.99 * ε') * (n : ℝ) / (t : ℝ)))) =
      (2 * (1 - ε' / 20) * (1 - ε' / 100) * (1 - ε' / 10000) * (3 + 0.99 * ε') / (6 + ε' / 2)) *
        (n : ℝ) := by
    field_simp
  have h_ge_one : (1 : ℝ) ≤ 2 * (1 - ε' / 20) * (1 - ε' / 100) * (1 - ε' / 10000) *
      (3 + 0.99 * ε') / (6 + ε' / 2) := by
    rw [le_div_iff₀ (by linarith)]
    have hp1 : 1 - 0.061 * ε' ≤ (1 - ε' / 20) * (1 - ε' / 100) := by nlinarith only [hε', hε'1]
    have hp2 : 1 - 0.062 * ε' ≤ (1 - ε' / 20) * (1 - ε' / 100) * (1 - ε' / 10000) := by
      nlinarith only [hε', hε'1, hp1]
    have hp3 : 6 + ε' / 2 ≤ 2 * (1 - 0.062 * ε') * (3 + 0.99 * ε') := by
      nlinarith only [hε', hε'1]
    have hp4 : 2 * (1 - 0.062 * ε') * (3 + 0.99 * ε') ≤
        2 * (1 - ε' / 20) * (1 - ε' / 100) * (1 - ε' / 10000) * (3 + 0.99 * ε') := by
      nlinarith only [hε', hε'1, hp2]
    linarith only [hp3, hp4]
  have h_n_prod : (n : ℝ) ≤ (2 * (1 - ε' / 20) * (1 - ε' / 100) * (1 - ε' / 10000) *
      (3 + 0.99 * ε') / (6 + ε' / 2)) * (n : ℝ) := by
    nlinarith only [h_ge_one, hn_pos]
  linarith only [h_prod, h_simp, h_n_prod]

theorem main : H1 → H2 → type_of% @Erdos556.erdos_556.variants.luczak_asymptotic_even := by
  intro h1 h2 ε hε
  classical
  set ε' : ℝ := min ε 1
  have hε' : 0 < ε' := lt_min hε zero_lt_one
  have hε'1 : ε' ≤ 1 := min_le_right ε 1
  have hε'ε : ε' ≤ ε := min_le_left ε 1
  set d : ℝ := ε' / 1000
  set δ : ℝ := ε' / 20
  have hd : 0 < d := by positivity
  have hδ0 : 0 < δ := by positivity
  have hδ1 : δ < 1 := by dsimp [δ]; linarith
  obtain ⟨η₀, hη₀, hm₀_all⟩ := h2 d δ hd hδ0 hδ1
  set η : ℝ := min η₀ (ε' / 1000)
  have hη : 0 < η := lt_min hη₀ (by positivity)
  have hη_le0 : η ≤ η₀ := min_le_left _ _
  have hη_le : η ≤ ε' / 1000 := min_le_right _ _
  set l : ℕ := Nat.ceil (1000 / ε')
  have hl_real : 1000 / ε' ≤ (l : ℝ) := natLC _
  have hl_ge : 1000 ≤ l := by
    have : (1000 : ℝ) ≤ 1000 / ε' := by rw [le_div_iff₀ hε']; nlinarith
    exact_mod_cast this.trans hl_real
  have hl_pos : 0 < l := by omega
  obtain ⟨M_bound, hM_eq⟩ : ∃ M, M = SzemerediRegularity.bound η l := ⟨_, rfl⟩
  have hM_pos : 0 < M_bound := hM_eq ▸ SzemerediRegularity.bound_pos η l
  have hl_le_M : l ≤ M_bound := hM_eq ▸ SzemerediRegularity.le_bound η l
  obtain ⟨m_req, hm_req_eq⟩ : ∃ mr, mr = (fsRange (M_bound + 1)).sup (fun t => (hm₀_all t).choose) :=
    ⟨_, rfl⟩
  obtain ⟨N₀, hN₀_eq⟩ : ∃ n0, n0 = Nat.ceil ((10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound + 100) / 3) + 4 :=
    ⟨_, rfl⟩
  rw [Filter.eventually_atTop]
  refine ⟨N₀, fun n hn heven => ?_⟩
  have hN₀_ge4 : 4 ≤ N₀ := by rw [hN₀_eq]; exact Nat.le_add_left 4 _
  have hn4 : 4 ≤ n := hN₀_ge4.trans hn
  have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
  obtain ⟨N, hN_eq⟩ : ∃ N, N = Nat.floor ((3 + ε') * (n : ℝ)) := ⟨_, rfl⟩
  have hN_le : (N : ℝ) ≤ (3 + ε') * (n : ℝ) := hN_eq ▸ Nat.floor_le (by positivity)
  have hN_gt : (3 + ε') * (n : ℝ) - 1 < (N : ℝ) := hN_eq ▸ Nat.sub_one_lt_floor _
  have hn_bound : (10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound + 100) / 3 ≤ (n : ℝ) := by
    have h1n : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have h2n : (10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound + 100) / 3 ≤
        (Nat.ceil ((10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound + 100) / 3) : ℝ) :=
      natLC _
    have h3n : ((Nat.ceil ((10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound + 100) / 3) : ℕ) : ℝ) ≤ (N₀ : ℝ) := by
      rw [hN₀_eq]; exact_mod_cast Nat.le_add_right _ 4
    linarith
  have hN_big : 10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound + 99 ≤ (N : ℝ) := by
    have h3n : (3 + ε') * (n : ℝ) - 1 ≥ 3 * (n : ℝ) - 1 := by nlinarith
    linarith
  have hN_pos : 0 < N := by
    have : (1 : ℝ) ≤ (N : ℝ) := by
      have : (0 : ℝ) < 10000 * (M_bound : ℝ) / ε' + (m_req : ℝ) * M_bound := by positivity
      linarith
    exact_mod_cast this
  have hRamsey_le : multicolourRamsey (cycleGraph n) 3 ≤ N := by
    apply Nat.sInf_le
    intro c hc
    obtain ⟨ic, hic⟩ := dense_color_of_three_colouring N c hc
    let G := c ic
    have hlN : l ≤ N := by
      have h1 : (l : ℝ) ≤ (M_bound : ℝ) := by exact_mod_cast hl_le_M
      have h2 : (M_bound : ℝ) ≤ 10000 * (M_bound : ℝ) / ε' := by
        rw [le_div_iff₀ hε']; nlinarith only [hε', hε'1]
      have h3 : (10000 * (M_bound : ℝ) / ε' : ℝ) ≤ (N : ℝ) := by
        linarith [show (0 : ℝ) ≤ (m_req : ℝ) * M_bound + 99 by positivity]
      exact natCL.mp (h1.trans (h2.trans h3))
    obtain ⟨t, parts, R, _, htl, htM, hdisj, hparts_card, hR_prop, hR_ineq⟩ :=
      regularity_cluster_graph N hN_pos G hic η d hη hd.le l hlN hl_pos
    rw [← hM_eq] at htM
    have ht_pos : 0 < t := lt_of_lt_of_le hl_pos htl
    have ht_ge_1000 : (1000 : ℝ) / ε' ≤ (t : ℝ) := hl_real.trans (by exact_mod_cast htl)
    have ht_1000 : (1000 : ℝ) ≤ (t : ℝ) := by
      have : (1000 : ℝ) ≤ 1000 / ε' := by rw [le_div_iff₀ hε']; nlinarith only [hε', hε'1]
      exact this.trans ht_ge_1000
    obtain ⟨m, hm_eq⟩ : ∃ m, m = N / t := ⟨_, rfl⟩
    obtain ⟨k, hk_eq⟩ : ∃ k, k = Nat.floor ((t : ℝ) / (6 + ε' / 2)) := ⟨_, rfl⟩
    have hk_pos_real : (1 : ℝ) ≤ (t : ℝ) / (6 + ε' / 2) := by
      rw [le_div_iff₀ (by linarith)]; linarith
    have hk1 : 1 ≤ k := by rw [hk_eq]; exact Nat.le_floor (by simpa using hk_pos_real)
    have hm_ge : (hm₀_all t).choose ≤ m := by
      have hsup : (hm₀_all t).choose ≤ m_req := by
        rw [hm_req_eq]
        exact Finset.le_sup (f := fun s => (hm₀_all s).choose)
          (fsMR.mpr (natLSOL htM))
      have hmul : m_req * t ≤ N := by
        have h1 : (m_req : ℝ) * (t : ℝ) ≤ (m_req : ℝ) * (M_bound : ℝ) := by gcongr
        have h2 : (m_req : ℝ) * (M_bound : ℝ) ≤ (N : ℝ) := by
          have : (0 : ℝ) ≤ 10000 * (M_bound : ℝ) / ε' + 99 := by positivity
          linarith
        exact_mod_cast h1.trans h2
      rw [hm_eq]
      exact hsup.trans ((natLDIML ht_pos).mpr hmul)
    have ht_le_epsN : (t : ℝ) ≤ ε' / 10000 * (N : ℝ) := by
      have h1 : (t : ℝ) ≤ (M_bound : ℝ) := by exact_mod_cast htM
      have h2 : 10000 * (M_bound : ℝ) / ε' ≤ (N : ℝ) := by
        have : (0 : ℝ) ≤ (m_req : ℝ) * M_bound + 99 := by positivity
        linarith
      have h3 : (M_bound : ℝ) ≤ ε' / 10000 * (N : ℝ) := by
        rw [div_le_iff₀ hε'] at h2; linarith
      exact h1.trans h3
    have hk_le : (k : ℝ) ≤ (t : ℝ) / (6 + ε' / 2) := hk_eq ▸ Nat.floor_le (by positivity)
    have hR_gt : (k - 1) * t < R.edgeFinset.card :=
      cluster_edge_bound ε' η d N t k R.edgeFinset.card hε' hε'1 hη_le le_rfl
        ht_pos hN_pos ht_ge_1000 ht_le_epsN hk_le hR_ineq
    obtain ⟨M, hM_match, hM_card, hM_reach⟩ := h1 t k R hk1 hR_gt
    have hn_big3 : 10000 / ε' ≤ 3 * (n : ℝ) := by
      have hM1 : (1 : ℝ) ≤ (M_bound : ℝ) := by exact_mod_cast hM_pos
      have h1 : (10000 : ℝ) ≤ 10000 * (M_bound : ℝ) := by linarith
      have h1' : (10000 : ℝ) / ε' ≤ 10000 * (M_bound : ℝ) / ε' := div_le_div_of_nonneg_right h1 hε'.le
      have h2 : (0 : ℝ) ≤ (m_req : ℝ) * M_bound + 100 := by positivity
      linarith
    have hk_gt : (t : ℝ) / (6 + ε' / 2) - 1 < (k : ℝ) := hk_eq ▸ Nat.sub_one_lt_floor _
    have hm_gt : (N : ℝ) / (t : ℝ) - 1 < (m : ℝ) := by
      rw [hm_eq, sub_lt_iff_lt_add, div_lt_iff₀ (by exact_mod_cast ht_pos)]
      calc (N : ℝ) < (↑(N / t * t + t) : ℝ) := by exact_mod_cast Nat.lt_div_mul_add ht_pos
        _ = (↑(N / t) + 1) * ↑t := by push_cast; ring
    have h_n_le : (n : ℝ) ≤ (1 - δ) * (2 * (k : ℝ) * (m : ℝ)) :=
      blowup_size_bound ε' δ N n t m k hε' hε'1 rfl ht_pos hn_pos ht_ge_1000 ht_le_epsN
        hN_gt hn_big3 hk_gt hm_gt
    have hparts_card' : ∀ i : Fin t, m ≤ (parts i).card ∧ (parts i).card ≤ m + 1 := by
      rw [hm_eq]; exact hparts_card
    exact ⟨ic, (hm₀_all t).choose_spec N n m k G parts R M heven hn4 hk1 hm_ge h_n_le
      hdisj hparts_card' (fun u v huv => ⟨(hR_prop u v huv).1.mono hη_le0, (hR_prop u v huv).2⟩)
      hM_match hM_card hM_reach⟩
  have h_final : (multicolourRamsey (cycleGraph n) 3 : ℝ) ≤ (3 + ε) * (n : ℝ) := by
    calc (multicolourRamsey (cycleGraph n) 3 : ℝ)
        ≤ (N : ℝ) := by exact_mod_cast hRamsey_le
      _ ≤ (3 + ε') * (n : ℝ) := hN_le
      _ ≤ (3 + ε) * (n : ℝ) := by gcongr
  exact h_final

end OMA.Erdos556R1
end R1Section

section H1Section
/- A dense component yields a matching by coloring each edge with the sum of its endpoint labels. -/

open SimpleGraph Finset
open scoped SimpleGraph

-- Credit: @MrSeizy
theorem h1_proof : OMA.Erdos556R1.H1 := by
  intro t k R _ hk hd
  classical
  let S (c : R.ConnectedComponent) := univ.filter (fun x => R.connectedComponentMk x = c)
  let comp (e : Sym2 (Fin t)) := R.connectedComponentMk e.out.1
  let E (c : R.ConnectedComponent) := R.edgeFinset.filter (fun e => comp e = c)
  have hS : ∑ c, (S c).card = t := by
    simpa [S] using sum_card_fiberwise_eq_card_filter (univ : Finset (Fin t)) univ
      R.connectedComponentMk
  have hE : ∑ c, (E c).card = R.edgeFinset.card := by
    simpa [E] using sum_card_fiberwise_eq_card_filter R.edgeFinset univ comp
  obtain ⟨c, hc⟩ : ∃ c, (k - 1) * (S c).card < (E c).card := by
    by_contra! h
    have hle := sum_le_sum (fun c (_ : c ∈ univ) => h c)
    rw [← mul_sum, hS, hE] at hle
    omega
  have hmem (x : Fin t) : x ∈ S c ↔ x ∈ c.supp := by simp [S]
  have hends {x y : Fin t} (he : s(x,y) ∈ E c) : x ∈ S c ∧ y ∈ S c := by
    obtain ⟨hR, hcomp⟩ := mem_filter.mp he
    have hadj : R.Adj x y := mem_edgeFinset.mp hR
    have hout : (s(x,y) : Sym2 (Fin t)).out.1 ∈ c.supp := hcomp
    have hxy := c.mem_supp_congr_adj hadj
    rcases Sym2.mem_iff.mp (Sym2.out_fst_mem s(x,y)) with hx | hy
    · rw [hx] at hout
      exact ⟨(hmem _).mpr hout, (hmem _).mpr (hxy.mp hout)⟩
    · rw [hy] at hout
      exact ⟨(hmem _).mpr (hxy.mpr hout), (hmem _).mpr hout⟩
  have hspos : 0 < (S c).card := by
    obtain ⟨x, hx⟩ := c.nonempty_supp
    exact card_pos.mpr ⟨x, (hmem _).mpr hx⟩
  let : NeZero (S c).card := ⟨hspos.ne'⟩
  -- The finite-set labeling follows the odd_lower_bound sibling proof.
  let equiv : S c ≃ Fin (S c).card := Finset.equivFinOfCardEq rfl
  let label (x : Fin t) : Fin (S c).card := if hx : x ∈ S c then equiv ⟨x, hx⟩ else 0
  have hinj {x y} (hx : x ∈ S c) (hy : y ∈ S c) (h : label x = label y) : x = y := by
    simp only [label, dif_pos hx, dif_pos hy] at h
    exact congrArg subVal (equiv.injective h)
  let color : Sym2 (Fin t) → Fin (S c).card :=
    Sym2.lift ⟨fun x y => label x + label y, fun x y => add_comm _ _⟩
  obtain ⟨a, _, ha⟩ := exists_lt_card_fiber_of_mul_lt_card_of_maps_to
    (s := E c) (t := univ) (f := color) (fun _ _ => mem_univ _)
    (by simpa [natMC] using hc)
  let F := (E c).filter (fun e => color e = a)
  have hsize : k ≤ F.card := by
    change k - 1 < F.card at ha
    omega
  have uniqueNbr {x y z : Fin t} (hy : s(x,y) ∈ F) (hz : s(x,z) ∈ F) : y = z := by
    obtain ⟨he, hy'⟩ := mem_filter.mp hy
    obtain ⟨hf, hz'⟩ := mem_filter.mp hz
    have h : label x + label y = label x + label z := hy'.trans hz'.symm
    exact hinj (hends he).2 (hends hf).2 (add_left_cancel h)
  let M : R.Subgraph := {
    verts := ↑(F.biUnion Sym2.toFinset)
    Adj := fun x y => s(x,y) ∈ F
    adj_sub := fun h => mem_edgeFinset.mp (mem_filter.mp (mem_filter.mp h).1).1
    edge_vert := fun {x y} h => mem_biUnion.mpr ⟨_, h, Sym2.mem_toFinset.mpr (Sym2.mem_mk_left x y)⟩
    symm := ⟨fun x y h => by rwa [Sym2.eq_swap]⟩ }
  have incident {x : Fin t} (hx : x ∈ M.verts) : ∃ y, s(x,y) ∈ F := by
    obtain ⟨e, he, hx'⟩ := mem_biUnion.mp hx
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hx')
    exact ⟨y, he⟩
  have disj : (F : Set (Sym2 (Fin t))).PairwiseDisjoint Sym2.toFinset := by
    intro e he f hf hne
    apply fsDL.mpr
    intro x hx hx'
    obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hx)
    obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp (Sym2.mem_toFinset.mp hx')
    exact hne (congrArg (fun w => s(x,w)) (uniqueNbr he hf))
  have inside {x : Fin t} (hx : x ∈ M.verts) : x ∈ c.supp := by
    obtain ⟨y, hy⟩ := incident hx
    exact (hmem x).mp (hends (mem_filter.mp hy).1).1
  refine ⟨M, ?_, ?_, fun _ hu _ hv => c.reachable_of_mem_supp (inside hu) (inside hv)⟩
  · intro x hx
    obtain ⟨y, hy⟩ := incident hx
    exact ⟨y, hy, fun _ hz => uniqueNbr hz hy⟩
  · have hcard (e) (he : e ∈ F) : e.toFinset.card = 2 :=
      e.card_toFinset_of_not_isDiag (R.not_isDiag_of_mem_edgeFinset
        (mem_filter.mp (mem_filter.mp he).1).1)
    change 2 * k ≤ (↑(F.biUnion Sym2.toFinset) : Set (Fin t)).ncard
    rw [stNCF, card_biUnion disj, sum_const_nat hcard, natMC F.card]
    omega
end H1Section

section H2Section
open SimpleGraph Finset

namespace H2Proof

/- ### Uniformity and typical-degree helpers -/

private lemma card_bad_lt {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {d η : ℝ} (hη : 0 < η) {U V V' : Finset (Fin N)}
    (huni : G.IsUniform η U V) (hd : d ≤ (G.edgeDensity U V : ℝ))
    (hU : 0 < U.card) (hV : 0 < V.card) (hV' : V' ⊆ V)
    (hV'card : (V.card : ℝ) * η ≤ (V'.card : ℝ)) :
    ((U.filter (fun u => ((G.neighborFinset u ∩ V').card : ℝ) ≤ (d - η) * (V'.card : ℝ))).card : ℝ) <
      (U.card : ℝ) * η := by
  set B := U.filter (fun u => ((G.neighborFinset u ∩ V').card : ℝ) ≤ (d - η) * (V'.card : ℝ))
  by_contra! hle
  have hB_pos : 0 < B.card := by
    have h1 : (0 : ℝ) < (U.card : ℝ) * η := by positivity
    exact_mod_cast h1.trans_le hle
  have hV'_pos : 0 < V'.card := by
    have h1 : (0 : ℝ) < (V.card : ℝ) * η := by positivity
    exact_mod_cast h1.trans_le hV'card
  have hdiff := huni (Finset.filter_subset _ _) hV' hle hV'card
  have hgt : d - η < (G.edgeDensity B V' : ℝ) := by
    rw [abs_sub_lt_iff] at hdiff
    linarith
  have hsub : G.interedges B V' ⊆
      B.biUnion (fun u => (G.neighborFinset u ∩ V').image (fun v => (u, v))) := by
    intro ⟨u, v⟩ huv
    rw [sgMMII] at huv
    exact fsMB.mpr ⟨u, huv.1,
      fsMI.mpr ⟨v, fsMI3.mpr ⟨(G.mem_neighborFinset u v).mpr huv.2.2, huv.2.1⟩, rfl⟩⟩
  have hcard_ie : (G.interedges B V').card ≤ ∑ u ∈ B, (G.neighborFinset u ∩ V').card := by
    calc (G.interedges B V').card
        ≤ (B.biUnion (fun u => (G.neighborFinset u ∩ V').image (fun v => (u, v)))).card :=
          fsCLC hsub
      _ ≤ ∑ u ∈ B, ((G.neighborFinset u ∩ V').image (fun v => (u, v))).card :=
          fsCBL
      _ ≤ ∑ u ∈ B, (G.neighborFinset u ∩ V').card :=
          fsSLS fun _ _ => Finset.card_image_le
  have hcard_real : ((G.interedges B V').card : ℝ) ≤ (B.card : ℝ) * ((d - η) * (V'.card : ℝ)) := by
    calc ((G.interedges B V').card : ℝ)
        ≤ ((∑ u ∈ B, (G.neighborFinset u ∩ V').card : ℕ) : ℝ) := natCL.mpr hcard_ie
      _ = ∑ u ∈ B, ((G.neighborFinset u ∩ V').card : ℝ) := by push_cast; rfl
      _ ≤ ∑ _u ∈ B, (d - η) * (V'.card : ℝ) := by
          refine fsSLS fun u hu => ?_
          exact (fsMF.mp hu).2
      _ = (B.card : ℝ) * ((d - η) * (V'.card : ℝ)) := by simp [Finset.sum_const, nsmul_eq_mul]
  have hden_pos : (0 : ℝ) < (B.card : ℝ) * (V'.card : ℝ) := by positivity
  have hle_den : (G.edgeDensity B V' : ℝ) ≤ d - η := by
    rw [sgED]
    push_cast
    rw [div_le_iff₀ hden_pos]
    linarith
  linarith

private lemma exists_good_two {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {d η : ℝ} (hη : 0 < η) {U P avoid V₁ T₁ V₂ T₂ : Finset (Fin N)}
    (hPU : P ⊆ U) (hU : 0 < U.card)
    (huni₁ : G.IsUniform η U V₁) (hd₁ : d ≤ (G.edgeDensity U V₁ : ℝ))
    (hV₁ : 0 < V₁.card) (hT₁ : T₁ ⊆ V₁) (hT₁c : (V₁.card : ℝ) * η ≤ (T₁.card : ℝ))
    (huni₂ : G.IsUniform η U V₂) (hd₂ : d ≤ (G.edgeDensity U V₂ : ℝ))
    (hV₂ : 0 < V₂.card) (hT₂ : T₂ ⊆ V₂) (hT₂c : (V₂.card : ℝ) * η ≤ (T₂.card : ℝ))
    (hP : (avoid.card : ℝ) + 2 * (U.card : ℝ) * η ≤ (P.card : ℝ)) :
    ∃ u ∈ P, u ∉ avoid ∧
      (d - η) * (T₁.card : ℝ) < ((G.neighborFinset u ∩ T₁).card : ℝ) ∧
      (d - η) * (T₂.card : ℝ) < ((G.neighborFinset u ∩ T₂).card : ℝ) := by
  set B₁ := U.filter (fun u => ((G.neighborFinset u ∩ T₁).card : ℝ) ≤ (d - η) * (T₁.card : ℝ))
  set B₂ := U.filter (fun u => ((G.neighborFinset u ∩ T₂).card : ℝ) ≤ (d - η) * (T₂.card : ℝ))
  have hB₁ : (B₁.card : ℝ) < (U.card : ℝ) * η := card_bad_lt G hη huni₁ hd₁ hU hV₁ hT₁ hT₁c
  have hB₂ : (B₂.card : ℝ) < (U.card : ℝ) * η := card_bad_lt G hη huni₂ hd₂ hU hV₂ hT₂ hT₂c
  set rem := P \ (avoid ∪ B₁ ∪ B₂)
  have hrem_pos : 0 < rem.card := by
    have h1 : P.card ≤ rem.card + (avoid ∪ B₁ ∪ B₂).card := by
      calc P.card ≤ (rem ∪ (avoid ∪ B₁ ∪ B₂)).card := fsCLC (fun x hx => by
            by_cases h : x ∈ avoid ∪ B₁ ∪ B₂
            · exact fsMUR _ h
            · exact fsMUL _ (fsMS.mpr ⟨hx, h⟩))
        _ ≤ rem.card + (avoid ∪ B₁ ∪ B₂).card := fsCUL _ _
    have h2 : (avoid ∪ B₁ ∪ B₂).card ≤ avoid.card + B₁.card + B₂.card :=
      (fsCUL _ _).trans (natALAR (fsCUL _ _) _)
    have h12 : P.card ≤ rem.card + avoid.card + B₁.card + B₂.card := by omega
    have h3 : ((P.card : ℝ)) ≤ (rem.card : ℝ) + (avoid.card : ℝ) + (B₁.card : ℝ) + (B₂.card : ℝ) := by
      exact_mod_cast h12
    have h4 : (0 : ℝ) < (rem.card : ℝ) := by linarith
    exact_mod_cast h4
  obtain ⟨u, hu⟩ := fsCP.mp hrem_pos
  rw [fsMS, fsMU, fsMU] at hu
  have huU : u ∈ U := hPU hu.1
  have hnotB₁ : u ∉ B₁ := fun h => hu.2 (orInl (orInr h))
  have hnotB₂ : u ∉ B₂ := fun h => hu.2 (orInr h)
  refine ⟨u, hu.1, fun h => hu.2 (orInl (orInl h)), ?_, ?_⟩
  · by_contra! hle
    exact hnotB₁ (fsMF.mpr ⟨huU, hle⟩)
  · by_contra! hle
    exact hnotB₂ (fsMF.mpr ⟨huU, hle⟩)

private lemma no_empty_pair_of_uniform {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {d η : ℝ} (hd_gt : η < d) {U V A' B' : Finset (Fin N)}
    (huni : G.IsUniform η U V) (hd : d ≤ (G.edgeDensity U V : ℝ))
    (hA' : A' ⊆ U) (hB' : B' ⊆ V) {cA cB : ℕ}
    (hcA : (U.card : ℝ) * η ≤ (cA : ℝ)) (hcB : (V.card : ℝ) * η ≤ (cB : ℝ)) :
    ∀ X ⊆ A', ∀ Y ⊆ B', cA ≤ X.card → cB ≤ Y.card → ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y := by
  intro X hX Y hY hXc hYc
  have hX' : (U.card : ℝ) * η ≤ (X.card : ℝ) := hcA.trans (natCL.mpr hXc)
  have hY' : (V.card : ℝ) * η ≤ (Y.card : ℝ) := hcB.trans (natCL.mpr hYc)
  have hdiff := huni (hX.trans hA') (hY.trans hB') hX' hY'
  have hpos : (0 : ℝ) < (G.edgeDensity X Y : ℝ) := by
    rw [abs_sub_lt_iff] at hdiff
    linarith
  have hne : (G.interedges X Y).Nonempty := by
    rw [sgED] at hpos
    push_cast at hpos
    by_contra! hem
    simp [hem] at hpos
  obtain ⟨⟨x, y⟩, hxy⟩ := hne
  rw [sgMMII] at hxy
  exact ⟨x, hxy.1, y, hxy.2.1, hxy.2.2⟩

/- ### Splitting a cluster into disjoint Res, Cap, Body -/

private lemma split_cluster {N : ℕ} (S : Finset (Fin N)) (q : ℕ) (hq : 2 * q ≤ S.card) :
    ∃ Res Cap Body : Finset (Fin N),
      Res ⊆ S ∧ Cap ⊆ S ∧ Body ⊆ S ∧
      Disjoint Res Cap ∧ Disjoint Res Body ∧ Disjoint Cap Body ∧
      Res.card = q ∧ Cap.card = q ∧ Body.card = S.card - 2 * q := by
  classical
  set L := S.toList
  have hnodup : L.Nodup := S.nodup_toList
  have hlen : L.length = S.card := S.length_toList
  set L1 := L.take q
  set L2 := (L.drop q).take q
  set L3 := L.drop (2 * q)
  have hcat : L1 ++ L2 ++ L3 = L := by
    have h1 : L2 ++ L3 = L.drop q := by
      simp only [L2, L3]
      rw [show 2 * q = q + q by omega, ← List.drop_drop]
      exact List.take_append_drop q (L.drop q)
    rw [List.append_assoc, h1]
    exact List.take_append_drop q L
  have hnodup_cat : (L1 ++ L2 ++ L3).Nodup := hcat.symm ▸ hnodup
  have hn12 : (L1 ++ L2).Nodup := (lsNA2.mp hnodup_cat).1
  have hn1 : L1.Nodup := (lsNA2.mp hn12).1
  have hn2 : L2.Nodup := (lsNA2.mp hn12).2.1
  have hn3 : L3.Nodup := (lsNA2.mp hnodup_cat).2.1
  refine ⟨L1.toFinset, L2.toFinset, L3.toFinset, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [lsMT] at hx
    exact S.mem_toList.mp (by show x ∈ L; rw [← hcat]; exact lsMAL _ (lsMAL _ hx))
  · intro x hx
    rw [lsMT] at hx
    exact S.mem_toList.mp (by show x ∈ L; rw [← hcat]; exact lsMAL _ (lsMAR _ hx))
  · intro x hx
    rw [lsMT] at hx
    exact S.mem_toList.mp (by show x ∈ L; rw [← hcat]; exact lsMAR _ hx)
  · rw [fsDL]
    intro x hx1 hx2
    rw [lsMT] at hx1 hx2
    exact (lsNA2.mp hn12).2.2 x hx1 x hx2 rfl
  · rw [fsDL]
    intro x hx1 hx3
    rw [lsMT] at hx1 hx3
    exact (lsNA2.mp hnodup_cat).2.2 x (lsMAL _ hx1) x hx3 rfl
  · rw [fsDL]
    intro x hx2 hx3
    rw [lsMT] at hx2 hx3
    exact (lsNA2.mp hnodup_cat).2.2 x (lsMAR _ hx2) x hx3 rfl
  · rw [lsTCON hn1, lsLT, hlen]
    omega
  · rw [lsTCON hn2, lsLT, List.length_drop, hlen]
    omega
  · rw [lsTCON hn3, List.length_drop, hlen]

/- ### DFS long alternating path lemma -/

private noncomputable def bipartAdj {N : ℕ} (G : SimpleGraph (Fin N))
    (A' B' : Finset (Fin N)) (x y : Fin N) : Prop :=
  ((x ∈ A' ∧ y ∈ B') ∨ (x ∈ B' ∧ y ∈ A')) ∧ G.Adj x y

private lemma bipartAdj_symm {N : ℕ} {G : SimpleGraph (Fin N)} {A' B' : Finset (Fin N)}
    {x y : Fin N} (h : bipartAdj G A' B' x y) : bipartAdj G A' B' y x :=
  ⟨by rcases h.1 with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> [exact orInr ⟨hy, hx⟩; exact orInl ⟨hy, hx⟩],
    h.2.symm⟩

open Classical in
private noncomputable def dfsStep {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A' B' : Finset (Fin N)) (cA cB : ℕ)
    (P : List (Fin N)) (D W : Finset (Fin N)) :
    List (Fin N) × Finset (Fin N) × Finset (Fin N) :=
  if _ : cA ≤ (D ∩ A').card ∨ cB ≤ (D ∩ B').card then (P, D, W)
  else match P with
  | [] => ([], D, W)
  | v :: rest =>
    if hex : ∃ w ∈ W, bipartAdj G A' B' v w then
      dfsStep G A' B' cA cB (hex.choose :: v :: rest) D (W.erase hex.choose)
    else
      dfsStep G A' B' cA cB rest (insert v D) W
termination_by 2 * W.card + P.length
decreasing_by
  · have hc : (W.erase hex.choose).card < W.card := Finset.card_erase_lt_of_mem hex.choose_spec.1
    simp only [lsLC]
    omega
  · simp only [lsLC]
    omega

open Classical in
private lemma dfsStep_spec {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A' B' : Finset (Fin N)) (hdisj : Disjoint A' B') (cA cB : ℕ)
    (a₀ : Fin N) (ha₀ : a₀ ∈ A') (hdeg₀ : cB ≤ (G.neighborFinset a₀ ∩ B').card) :
    ∀ n : ℕ, ∀ (P : List (Fin N)) (D W : Finset (Fin N)),
      2 * W.card + P.length = n →
      P ≠ [] →
      P.getLast? = some a₀ →
      P.Nodup →
      P.IsChain (bipartAdj G A' B') →
      P.toFinset ⊆ A' ∪ B' →
      D ⊆ A' ∪ B' →
      W ⊆ A' ∪ B' →
      A' ∪ B' ⊆ P.toFinset ∪ D ∪ W →
      Disjoint D W →
      Disjoint D P.toFinset →
      Disjoint W P.toFinset →
      (∀ d ∈ D, ∀ w ∈ W, ¬ bipartAdj G A' B' d w) →
      (D ∩ A').card ≤ cA →
      (D ∩ B').card ≤ cB →
      let res := dfsStep G A' B' cA cB P D W
      res.1 ≠ [] ∧
      res.1.getLast? = some a₀ ∧
      res.1.Nodup ∧
      res.1.IsChain (bipartAdj G A' B') ∧
      res.1.toFinset ⊆ A' ∪ B' ∧
      res.2.1 ⊆ A' ∪ B' ∧
      res.2.2 ⊆ A' ∪ B' ∧
      A' ∪ B' ⊆ res.1.toFinset ∪ res.2.1 ∪ res.2.2 ∧
      (∀ d ∈ res.2.1, ∀ w ∈ res.2.2, ¬ bipartAdj G A' B' d w) ∧
      (res.2.1 ∩ A').card ≤ cA ∧
      (res.2.1 ∩ B').card ≤ cB ∧
      (cA ≤ (res.2.1 ∩ A').card ∨ cB ≤ (res.2.1 ∩ B').card) := by
  intro n
  induction n using natSIO with
  | _ n ih =>
    intro P D W hn hPne hPlast hPnodup hPchain hPsub hDsub hWsub hcov
      hDW hDP hWP hnoEdge hDA hDB
    unfold dfsStep
    by_cases hstop : cA ≤ (D ∩ A').card ∨ cB ≤ (D ∩ B').card
    · simp only [dif_pos hstop]
      exact ⟨hPne, hPlast, hPnodup, hPchain, hPsub, hDsub, hWsub, hcov, hnoEdge, hDA, hDB, hstop⟩
    · simp only [dif_neg hstop]
      rcases P with _ | ⟨v, rest⟩
      · exact (hPne rfl).elim
      · by_cases hex : ∃ w ∈ W, bipartAdj G A' B' v w
        · simp only [dif_pos hex]
          set w := hex.choose
          have hwW : w ∈ W := hex.choose_spec.1
          have hvw : bipartAdj G A' B' v w := hex.choose_spec.2
          have hwsub : w ∈ A' ∪ B' := hWsub hwW
          have hwnP : w ∉ (v :: rest).toFinset := fsDL.mp hWP hwW
          have hwnD : w ∉ D := fsDR.mp hDW hwW
          have hlt : 2 * (W.erase w).card + (w :: v :: rest).length < n := by
            have hc := Finset.card_erase_lt_of_mem hwW
            simp only [lsLC] at hn ⊢
            omega
          refine ih _ hlt (w :: v :: rest) D (W.erase w) rfl (by simp) ?_ ?_ ?_ ?_ hDsub ?_ ?_ ?_ ?_ ?_ ?_ hDA hDB
          · simpa using hPlast
          · exact lsNC.mpr ⟨by simpa [lsMT] using hwnP, hPnodup⟩
          · exact lsCC (bipartAdj_symm hvw) hPchain
          · intro x hx
            rw [lsTC, fsMI2] at hx
            rcases hx with rfl | hx
            · exact hwsub
            · exact hPsub hx
          · exact (fsES w W).trans hWsub
          · intro x hx
            rcases fsMU.mp (hcov hx) with hPD | hW
            · rcases fsMU.mp hPD with hP | hD
              · rw [lsTC, fsMU, fsMU, fsMI2]
                exact orInl (orInl (orInr hP))
              · exact fsMUL _ (fsMUR _ hD)
            · by_cases hxw : x = w
              · subst hxw
                rw [lsTC, fsMU, fsMU, fsMI2]
                exact orInl (orInl (orInl rfl))
              · exact fsMUR _ (fsME.mpr ⟨hxw, hW⟩)
          · exact fsDOSR (fsES w W) hDW
          · rw [lsTC, Finset.disjoint_insert_right]
            exact ⟨hwnD, hDP⟩
          · rw [lsTC, Finset.disjoint_insert_right]
            exact ⟨Finset.notMem_erase w W, Finset.disjoint_of_subset_left (fsES w W) hWP⟩
          · intro d hd x hx
            exact hnoEdge d hd x (fsMOME hx)
        · simp only [dif_neg hex]
          have hvP : v ∈ (v :: rest).toFinset := by simp
          have hvsub : v ∈ A' ∪ B' := hPsub hvP
          have hvnD : v ∉ D := fsDR.mp hDP hvP
          have hvnW : v ∉ W := fsDR.mp hWP hvP
          have hvnR : v ∉ rest.toFinset := by
            intro h
            have : v ∈ rest := lsMT.mp h
            exact (lsNC.mp hPnodup).1 this
          have hrest_ne : rest ≠ [] := by
            intro hnil
            subst hnil
            simp only [List.getLast?_singleton, Option.some.injEq] at hPlast
            subst hPlast
            have hsubB : G.neighborFinset v ∩ B' ⊆ D ∩ B' := by
              intro b hb
              rw [fsMI3, sgMN] at hb
              have hbAB : b ∈ A' ∪ B' := fsMUR _ hb.2
              rcases fsMU.mp (hcov hbAB) with hPD | hW
              · rcases fsMU.mp hPD with hP | hD
                · rw [lsMT, lsMS] at hP
                  subst hP
                  exact (fsDL.mp hdisj ha₀ hb.2).elim
                · exact fsMI3.mpr ⟨hD, hb.2⟩
              · exact (hex ⟨b, hW, orInl ⟨ha₀, hb.2⟩, hb.1⟩).elim
            have hle : cB ≤ (D ∩ B').card := hdeg₀.trans (fsCLC hsubB)
            exact hstop (orInr hle)
          have hlt : 2 * W.card + rest.length < n := by
            simp only [lsLC] at hn
            omega
          have hDA' : ((insert v D) ∩ A').card ≤ cA := by
            by_cases hvA : v ∈ A'
            · have : insert v D ∩ A' = insert v (D ∩ A') := by
                ext x; simp only [fsMI3, fsMI2]
                exact ⟨fun ⟨h1, h2⟩ => h1.elim orInl (fun hd => orInr ⟨hd, h2⟩),
                       fun h => h.elim (fun he => ⟨orInl he, he ▸ hvA⟩) (fun ⟨hd, ha⟩ => ⟨orInr hd, ha⟩)⟩
              rw [this, fsCION (fun h => hvnD (fsMI3.mp h).1)]
              have : (D ∩ A').card < cA := not_le.mp (fun h => hstop (orInl h))
              omega
            · have : insert v D ∩ A' = D ∩ A' := by
                ext x; simp only [fsMI3, fsMI2]
                exact ⟨fun ⟨h1, h2⟩ => ⟨h1.elim (fun he => (hvA (he ▸ h2)).elim) id, h2⟩,
                       fun ⟨hd, ha⟩ => ⟨orInr hd, ha⟩⟩
              rw [this]
              exact (not_le.mp (fun h => hstop (orInl h))).le
          have hDB' : ((insert v D) ∩ B').card ≤ cB := by
            by_cases hvB : v ∈ B'
            · have : insert v D ∩ B' = insert v (D ∩ B') := by
                ext x; simp only [fsMI3, fsMI2]
                exact ⟨fun ⟨h1, h2⟩ => h1.elim orInl (fun hd => orInr ⟨hd, h2⟩),
                       fun h => h.elim (fun he => ⟨orInl he, he ▸ hvB⟩) (fun ⟨hd, hb⟩ => ⟨orInr hd, hb⟩)⟩
              rw [this, fsCION (fun h => hvnD (fsMI3.mp h).1)]
              have : (D ∩ B').card < cB := not_le.mp (fun h => hstop (orInr h))
              omega
            · have : insert v D ∩ B' = D ∩ B' := by
                ext x; simp only [fsMI3, fsMI2]
                exact ⟨fun ⟨h1, h2⟩ => ⟨h1.elim (fun he => (hvB (he ▸ h2)).elim) id, h2⟩,
                       fun ⟨hd, hb⟩ => ⟨orInr hd, hb⟩⟩
              rw [this]
              exact (not_le.mp (fun h => hstop (orInr h))).le
          refine ih _ hlt rest (insert v D) W rfl hrest_ne ?_ (lsNC.mp hPnodup).2
            hPchain.tail ?_ ?_ hWsub ?_ ?_ ?_ ?_ ?_ hDA' hDB'
          · rcases rest with _ | ⟨r, rs⟩
            · exact (hrest_ne rfl).elim
            · simpa using hPlast
          · exact fun x hx => hPsub (by simp [lsMT] at hx ⊢; right; exact hx)
          · rw [Finset.insert_subset_iff]
            exact ⟨hvsub, hDsub⟩
          · intro x hx
            rcases fsMU.mp (hcov hx) with hPD | hW
            · rcases fsMU.mp hPD with hP | hD
              · simp only [lsTC, fsMI2] at hP
                rcases hP with rfl | hxR
                · exact fsMUL _ (fsMUR _ (fsMIS _ _))
                · exact fsMUL _ (fsMUL _ hxR)
              · exact fsMUL _ (fsMUR _ (fsMIOM hD))
            · exact fsMUR _ hW
          · exact Finset.disjoint_insert_left.mpr ⟨hvnW, hDW⟩
          · rw [Finset.disjoint_insert_left]
            exact ⟨hvnR, fsDOSR
              (by intro x hx; simp [lsMT] at hx ⊢; right; exact hx) hDP⟩
          · exact fsDOSR
              (by intro x hx; simp [lsMT] at hx ⊢; right; exact hx) hWP
          · intro d hd w hw hadj
            rcases fsMI2.mp hd with rfl | hd
            · exact hex ⟨w, hw, hadj⟩
            · exact hnoEdge d hd w hw hadj

private lemma alternating_chain_props {N : ℕ} (G : SimpleGraph (Fin N)) :
    ∀ (Q : List (Fin N)) (A' B' : Finset (Fin N)),
      Disjoint A' B' → Q ≠ [] →
      (∀ h : Q ≠ [], Q.head h ∈ A') →
      Q.IsChain (bipartAdj G A' B') → Q.Nodup →
      (Q.toFinset ∩ A').card ≤ (Q.length + 1) / 2 ∧
      (Q.toFinset ∩ B').card ≤ Q.length / 2 ∧
      (∀ i (hi : i < Q.length), (Even i → Q[i] ∈ A') ∧ (Odd i → Q[i] ∈ B')) := by
  intro Q
  induction Q with
  | nil => intro _ _ _ hne; exact (hne rfl).elim
  | cons a t ih =>
    intro A' B' hdisj _ hhead hchain hnodup
    have haA : a ∈ A' := hhead (by simp)
    have haB : a ∉ B' := fsDL.mp hdisj haA
    rcases t with _ | ⟨b, ts⟩
    · refine ⟨?_, ?_, ?_⟩
      · simp [haA]
      · simp [haB]
      · intro i hi
        have hi0 : i = 0 := by simpa using hi
        subst hi0
        exact ⟨fun _ => haA, fun hodd => by simp at hodd⟩
    · have hab : bipartAdj G A' B' a b := List.IsChain.rel_head hchain
      have hbB : b ∈ B' := by
        rcases hab.1 with ⟨_, hb⟩ | ⟨ha, _⟩
        · exact hb
        · exact (haB ha).elim
      have hchain_t : (b :: ts).IsChain (bipartAdj G B' A') := by
        refine hchain.tail.imp fun {x y} hxy => ?_
        rcases hxy.1 with ⟨hx, hy⟩ | ⟨hx, hy⟩
        · exact ⟨orInr ⟨hx, hy⟩, hxy.2⟩
        · exact ⟨orInl ⟨hx, hy⟩, hxy.2⟩
      have hrec := ih B' A' hdisj.symm (by simp) (fun _ => hbB) hchain_t (lsNC.mp hnodup).2
      have hanT : a ∉ (b :: ts).toFinset := by
        simpa [lsMT] using (lsNC.mp hnodup).1
      have hsubA : (a :: b :: ts).toFinset ∩ A' = insert a ((b :: ts).toFinset ∩ A') := by
        ext x; simp [haA]
      have hsubB : (a :: b :: ts).toFinset ∩ B' = (b :: ts).toFinset ∩ B' := by
        ext x; simp [haB]
      refine ⟨?_, ?_, ?_⟩
      · rw [hsubA, fsCION (fun h => hanT (fsMI3.mp h).1)]
        have := hrec.2.1
        simp only [lsLC] at this ⊢
        omega
      · rw [hsubB]
        have := hrec.1
        simp only [lsLC] at this ⊢
        omega
      · intro i hi
        rcases i with _ | i
        · exact ⟨fun _ => haA, fun hodd => by simp at hodd⟩
        · have hi' : i < (b :: ts).length := by simpa using hi
          have hstep := hrec.2.2 i hi'
          refine ⟨fun heven => ?_, fun hodd => ?_⟩
          · rcases Nat.even_or_odd i with h | h
            · exact absurd h (Nat.even_add_one.mp heven)
            · exact hstep.2 h
          · rcases Nat.even_or_odd i with h | h
            · exact hstep.1 h
            · exact absurd h (Nat.odd_add_one.mp hodd)

private lemma dfs_long_path {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (A' B' : Finset (Fin N)) (hdisj : Disjoint A' B') {cA cB : ℕ}
    (hcA : 0 < cA) (hcB : 0 < cB)
    (hnoempty : ∀ X ⊆ A', ∀ Y ⊆ B', cA ≤ X.card → cB ≤ Y.card → ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y)
    (a₀ : Fin N) (ha₀ : a₀ ∈ A') (hdeg₀ : cB ≤ (G.neighborFinset a₀ ∩ B').card) :
    ∃ Q : List (Fin N),
      Q ≠ [] ∧ Q.head? = some a₀ ∧ Q.Nodup ∧ Q.IsChain (bipartAdj G A' B') ∧
      Q.toFinset ⊆ A' ∪ B' ∧
      2 * (min A'.card B'.card - 2 * max cA cB) + 1 ≤ Q.length ∧
      (∀ i (hi : i < Q.length), (Even i → Q[i] ∈ A') ∧ (Odd i → Q[i] ∈ B')) := by
  have ha₀_sub : a₀ ∈ A' ∪ B' := fsMUL _ ha₀
  set W₀ := (A' ∪ B').erase a₀
  have hspec := dfsStep_spec G A' B' hdisj cA cB a₀ ha₀ hdeg₀
    (2 * W₀.card + [a₀].length) [a₀] ∅ W₀ rfl (by simp) (by simp) (by simp) (by simp)
    (by simp [ha₀_sub]) (by simp) (fsES _ _)
    (fun x hx => by
      by_cases h : x = a₀
      · subst h; simp
      · exact fsMUR _ (fsME.mpr ⟨h, hx⟩))
    (by simp) (by simp) (by simp [W₀]) (by simp) (by simp) (by simp)
  set res := dfsStep G A' B' cA cB [a₀] ∅ W₀
  set P := res.1
  set D := res.2.1
  set W := res.2.2
  obtain ⟨hPne, hPlast, hPnodup, hPchain, hPsub, hDsub, hWsub, hcov, hnoEdge, hDA, hDB, hstop⟩ := hspec
  set Q := P.reverse
  have hQne : Q ≠ [] := by simpa [Q] using hPne
  have hQhead : Q.head? = some a₀ := by
    rw [List.head?_reverse]
    exact hPlast
  have hQnodup : Q.Nodup := List.nodup_reverse.mpr hPnodup
  have hQchain : Q.IsChain (bipartAdj G A' B') := by
    rw [List.isChain_reverse]
    exact hPchain.imp (fun {_ _} h => bipartAdj_symm h)
  have hQsub : Q.toFinset ⊆ A' ∪ B' := by
    intro x hx
    exact hPsub (by simpa [Q] using hx)
  have hprops := alternating_chain_props G Q A' B' hdisj hQne (fun h => by
    have := List.head?_eq_some_head h
    rw [hQhead] at this
    exact (Option.some.inj this).symm ▸ ha₀) hQchain hQnodup
  have hQpos : 0 < Q.length := List.length_pos_of_ne_nil hQne
  have hlen : 2 * (min A'.card B'.card - 2 * max cA cB) + 1 ≤ Q.length := by
    rcases hstop with hDA_ge | hDB_ge
    · have hWB : (W ∩ B').card < cB := by
        by_contra! hWB_ge
        obtain ⟨x, hx, y, hy, hadj⟩ := hnoempty (D ∩ A') fsISR
          (W ∩ B') fsISR hDA_ge hWB_ge
        exact hnoEdge x (fsMI3.mp hx).1 y (fsMI3.mp hy).1
          ⟨orInl ⟨(fsMI3.mp hx).2, (fsMI3.mp hy).2⟩, hadj⟩
      have hB_cov : B' ⊆ (Q.toFinset ∩ B') ∪ (D ∩ B') ∪ (W ∩ B') := by
        intro b hb
        have hbAB : b ∈ A' ∪ B' := fsMUR _ hb
        rcases fsMU.mp (hcov hbAB) with hPD | hW
        · rcases fsMU.mp hPD with hP | hD
          · exact fsMUL _ (fsMUL _
              (fsMI3.mpr ⟨by simpa [Q] using hP, hb⟩))
          · exact fsMUL _ (fsMUR _ (fsMI3.mpr ⟨hD, hb⟩))
        · exact fsMUR _ (fsMI3.mpr ⟨hW, hb⟩)
      have hB_card : B'.card ≤ (Q.toFinset ∩ B').card + (D ∩ B').card + (W ∩ B').card :=
        (fsCLC hB_cov).trans
          ((fsCUL _ _).trans (natALAR (fsCUL _ _) _))
      have hQB := hprops.2.1
      have hDB' : (D ∩ B').card ≤ cB := hDB
      have hmin := min_le_right A'.card B'.card
      have hmax := le_max_right cA cB
      omega
    · have hWA : (W ∩ A').card < cA := by
        by_contra! hWA_ge
        obtain ⟨x, hx, y, hy, hadj⟩ := hnoempty (W ∩ A') fsISR
          (D ∩ B') fsISR hWA_ge hDB_ge
        exact hnoEdge y (fsMI3.mp hy).1 x (fsMI3.mp hx).1
          ⟨orInr ⟨(fsMI3.mp hy).2, (fsMI3.mp hx).2⟩, hadj.symm⟩
      have hA_cov : A' ⊆ (Q.toFinset ∩ A') ∪ (D ∩ A') ∪ (W ∩ A') := by
        intro a ha
        have haAB : a ∈ A' ∪ B' := fsMUL _ ha
        rcases fsMU.mp (hcov haAB) with hPD | hW
        · rcases fsMU.mp hPD with hP | hD
          · exact fsMUL _ (fsMUL _
              (fsMI3.mpr ⟨by simpa [Q] using hP, ha⟩))
          · exact fsMUL _ (fsMUR _ (fsMI3.mpr ⟨hD, ha⟩))
        · exact fsMUR _ (fsMI3.mpr ⟨hW, ha⟩)
      have hA_card : A'.card ≤ (Q.toFinset ∩ A').card + (D ∩ A').card + (W ∩ A').card :=
        (fsCLC hA_cov).trans
          ((fsCUL _ _).trans (natALAR (fsCUL _ _) _))
      have hQA := hprops.1
      have hDA' : (D ∩ A').card ≤ cA := hDA
      have hmin := min_le_left A'.card B'.card
      have hmax := le_max_left cA cB
      omega
  exact ⟨Q, hQne, hQhead, hQnodup, hQchain, hQsub, hlen, hprops.2.2⟩

/- ### Extracting disjoint matching edges and building closed walk in R -/

private lemma extract_matching_pairs {t : ℕ} {R : SimpleGraph (Fin t)} (M : R.Subgraph)
    (hM : M.IsMatching) :
    ∀ (k : ℕ) (S : Finset (Fin t)),
      (∀ x ∈ S, x ∈ M.verts) →
      (∀ x ∈ S, ∀ y, M.Adj x y → y ∈ S) →
      2 * k ≤ S.card →
      ∃ edges : List (Fin t × Fin t),
        edges.length = k ∧
        (∀ p ∈ edges, M.Adj p.1 p.2) ∧
        (∀ p ∈ edges, p.1 ∈ S ∧ p.2 ∈ S) ∧
        (edges.flatMap (fun p => [p.1, p.2])).Nodup := by
  intro k
  induction k with
  | zero =>
    intro S _ _ _
    exact ⟨[], rfl, by simp, by simp, by simp⟩
  | succ k ih =>
    intro S hSverts hSclosed hScard
    have hSne : S.Nonempty := fsCP.mp (by omega)
    obtain ⟨u, huS⟩ := hSne
    obtain ⟨v, hvAdj, hvUniq⟩ := hM (hSverts u huS)
    have hvS : v ∈ S := hSclosed u huS v hvAdj
    have huv : u ≠ v := R.ne_of_adj (M.adj_sub hvAdj)
    set S' := (S.erase u).erase v
    have hS'verts : ∀ x ∈ S', x ∈ M.verts := fun x hx =>
      hSverts x (fsMOME (fsMOME hx))
    have hS'closed : ∀ x ∈ S', ∀ y, M.Adj x y → y ∈ S' := by
      intro x hx y hxy
      have hxS := fsMOME (fsMOME hx)
      have hxv : x ≠ v := fsNOME hx
      have hxu : x ≠ u := fsNOME (fsMOME hx)
      have hyS := hSclosed x hxS y hxy
      refine fsME.mpr ⟨?_, fsME.mpr ⟨?_, hyS⟩⟩
      · intro hyv; subst hyv
        exact hxu (hM.eq_of_adj_right hxy hvAdj)
      · intro hyu; subst hyu
        exact hxv (hvUniq x hxy.symm)
    have hS'card : 2 * k ≤ S'.card := by
      have h1 : (S.erase u).card = S.card - 1 := Finset.card_erase_of_mem huS
      have hv_er : v ∈ S.erase u := fsME.mpr ⟨huv.symm, hvS⟩
      have h2 : S'.card = (S.erase u).card - 1 := Finset.card_erase_of_mem hv_er
      omega
    obtain ⟨edges, hlen, hadj, hmemS', hnodup⟩ := ih S' hS'verts hS'closed hS'card
    have hnotU : u ∉ edges.flatMap (fun p => [p.1, p.2]) := by
      rw [lsMF2]
      rintro ⟨q, hq, hzq⟩
      have hqS' := hmemS' q hq
      simp only [lsMC, lsMS, lsNMN, or_false] at hzq
      rcases hzq with rfl | rfl
      · exact fsNOME (fsMOME hqS'.1) rfl
      · exact fsNOME (fsMOME hqS'.2) rfl
    have hnotV : v ∉ edges.flatMap (fun p => [p.1, p.2]) := by
      rw [lsMF2]
      rintro ⟨q, hq, hzq⟩
      have hqS' := hmemS' q hq
      simp only [lsMC, lsMS, lsNMN, or_false] at hzq
      rcases hzq with rfl | rfl
      · exact fsNOME hqS'.1 rfl
      · exact fsNOME hqS'.2 rfl
    refine ⟨(u, v) :: edges, by simp [hlen], ?_, ?_, ?_⟩
    · intro p hp
      rcases lsMC.mp hp with rfl | hp
      · exact hvAdj
      · exact hadj p hp
    · intro p hp
      rcases lsMC.mp hp with rfl | hp
      · exact ⟨huS, hvS⟩
      · exact ⟨fsMOME (fsMOME (hmemS' p hp).1),
               fsMOME (fsMOME (hmemS' p hp).2)⟩
    · simp only [lsFC2, lsCA, lsNA, lsNC]
      refine ⟨?_, hnotV, hnodup⟩
      simp only [lsMC]
      rintro (rfl | h)
      · exact huv rfl
      · exact hnotU h

private lemma walk_boundary_edge {t : ℕ} {R : SimpleGraph (Fin t)}
    {V : Finset (Fin t)} {a b : Fin t} (ha : a ∈ V) (hb : b ∉ V)
    (hwalk : R.Reachable a b) :
    ∃ x y : Fin t, R.Adj x y ∧ x ∈ V ∧ y ∉ V := by
  obtain ⟨w⟩ := hwalk
  induction w with
  | nil => exact (hb ha).elim
  | @cons u v c huv _ ih =>
    by_cases hv : v ∈ V
    · exact ih hv hb
    · exact ⟨u, v, huv, ha, hv⟩

private def spliceAt {α : Type*} [DecidableEq α] (x : α)
    (ins W : List (α × α × Bool)) : List (α × α × Bool) :=
  match W with
  | [] => ins
  | e :: rest => if e.1 = x then ins ++ e :: rest else e :: spliceAt x ins rest

private lemma isChain_append {α : Type*} {r : α → α → Prop} {l₁ l₂ : List α}
    (h₁ : l₁.IsChain r) (h₂ : l₂.IsChain r)
    (hbd : ∀ a ∈ l₁.getLast?, ∀ b ∈ l₂.head?, r a b) :
    (l₁ ++ l₂).IsChain r := by
  induction l₁ with
  | nil => simpa using h₂
  | cons x xs ih =>
    rcases xs with _ | ⟨y, ys⟩
    · simp only [lsNA, List.singleton_append]
      rcases l₂ with _ | ⟨b, bs⟩
      · exact h₁
      · exact lsCC (hbd x (by simp) b (by simp)) h₂
    · simp only [lsCA]
      exact lsCC (List.IsChain.rel_head h₁)
        (ih h₁.tail (fun a ha b hb => hbd a (by simpa using ha) b hb))

private lemma spliceAt_props {α : Type*} [DecidableEq α] (x : α)
    (ins W : List (α × α × Bool))
    (hWne : W ≠ []) (hex : ∃ e ∈ W, e.1 = x)
    (hWchain : W.IsChain (fun a b => a.2.1 = b.1))
    (hins_ne : ins ≠ [])
    (hins_head : (ins.head hins_ne).1 = x)
    (hins_last : (ins.getLast hins_ne).2.1 = x)
    (hins_chain : ins.IsChain (fun a b => a.2.1 = b.1)) :
    let W' := spliceAt x ins W
    W' ≠ [] ∧
    (∀ h' : W' ≠ [], (W'.head h').1 = (W.head hWne).1) ∧
    (∀ h' : W' ≠ [], W'.getLast h' = W.getLast hWne) ∧
    W'.length = W.length + ins.length ∧
    W'.IsChain (fun a b => a.2.1 = b.1) ∧
    (∀ e, e ∈ W' ↔ e ∈ ins ∨ e ∈ W) ∧
    List.Perm (W'.filter (·.2.2)) (ins.filter (·.2.2) ++ W.filter (·.2.2)) := by
  induction W with
  | nil => exact (hWne rfl).elim
  | cons e rest ih =>
    unfold spliceAt
    by_cases he : e.1 = x
    · rw [if_pos he]
      have hne' : ins ++ e :: rest ≠ [] := List.append_ne_nil_of_right_ne_nil _ (by simp)
      refine ⟨hne', ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro h'
        rw [lsHAONN hins_ne]
        simpa [he] using hins_head
      · intro h'
        exact List.getLast_append_of_ne_nil _ (by simp)
      · simp; omega
      · refine isChain_append hins_chain hWchain ?_
        intro a ha b hb
        have ha' : a = ins.getLast hins_ne := (by
          rw [List.getLast?_eq_some_getLast hins_ne] at ha
          simpa using ha : ins.getLast hins_ne = a).symm
        have hb' : b = e := (by simpa using hb : e = b).symm
        subst ha'; subst hb'
        simpa [he] using hins_last
      · intro z; simp
      · rw [List.filter_append]
    · rw [if_neg he]
      have hex_rest : ∃ e' ∈ rest, e'.1 = x := by
        rcases hex with ⟨e', he', hx'⟩
        rcases lsMC.mp he' with rfl | he'
        · exact (he hx').elim
        · exact ⟨e', he', hx'⟩
      have hrest_ne : rest ≠ [] := by
        rintro rfl; obtain ⟨e', he', _⟩ := hex_rest; exact (lsNMN he').elim
      obtain ⟨hne_r, hhead_r, hlast_r, hlen_r, hchain_r, hmem_r, hperm_r⟩ :=
        ih hrest_ne hex_rest hWchain.tail
      refine ⟨by simp, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro _; simp
      · intro h'
        rw [lsGC hne_r, hlast_r hne_r, lsGC hrest_ne]
      · simp [hlen_r]; omega
      · refine List.IsChain.cons_of_ne_nil hne_r hchain_r ?_
        rw [hhead_r hne_r]
        rcases rest with _ | ⟨r, rs⟩
        · exact (hrest_ne rfl).elim
        · simp only [List.head_cons]
          exact lsIIG.mp hWchain 0 (by simp)
      · intro z
        simp only [lsMC, hmem_r]
        tauto
      · by_cases hp : e.2.2 = true
        · simp only [lsFC, hp, ↓reduceIte]
          exact (hperm_r.cons e).trans (List.perm_middle.symm)
        · have hp' : e.2.2 = false := Bool.eq_false_iff.mpr hp
          simp only [lsFC, hp', Bool.false_eq_true, ↓reduceIte]
          exact hperm_r

private lemma nodup_flatMap_pair_unique {α : Type*} :
    ∀ (L : List (α × α)) (p q : α × α),
      (L.flatMap (fun r => [r.1, r.2])).Nodup →
      p ∈ L → q ∈ L → (q.1 = p.1 ∨ q.1 = p.2 ∨ q.2 = p.1 ∨ q.2 = p.2) → q = p := by
  intro L
  induction L with
  | nil => intro p q _ hp; exact (lsNMN hp).elim
  | cons a t ih =>
    intro p q hnodup hp hq heq
    simp only [lsFC2, lsCA, lsNA, lsNC] at hnodup
    rcases lsMC.mp hp with hpa | hp'
    · rcases lsMC.mp hq with hqa | hq'
      · exact hqa.trans hpa.symm
      · exfalso
        have h1 : q.1 ∈ t.flatMap (fun r => [r.1, r.2]) := lsMF2.mpr ⟨q, hq', by simp⟩
        have h2 : q.2 ∈ t.flatMap (fun r => [r.1, r.2]) := lsMF2.mpr ⟨q, hq', by simp⟩
        rw [hpa] at heq
        rcases heq with h | h | h | h
        · exact hnodup.1 (lsMC.mpr (orInr (h ▸ h1)))
        · exact hnodup.2.1 (h ▸ h1)
        · exact hnodup.1 (lsMC.mpr (orInr (h ▸ h2)))
        · exact hnodup.2.1 (h ▸ h2)
    · rcases lsMC.mp hq with hqa | hq'
      · exfalso
        have h1 : p.1 ∈ t.flatMap (fun r => [r.1, r.2]) := lsMF2.mpr ⟨p, hp', by simp⟩
        have h2 : p.2 ∈ t.flatMap (fun r => [r.1, r.2]) := lsMF2.mpr ⟨p, hp', by simp⟩
        rw [hqa] at heq
        rcases heq with h | h | h | h
        · exact hnodup.1 (lsMC.mpr (orInr (h.symm ▸ h1)))
        · exact hnodup.1 (lsMC.mpr (orInr (h.symm ▸ h2)))
        · exact hnodup.2.1 (h.symm ▸ h1)
        · exact hnodup.2.1 (h.symm ▸ h2)
      · exact ih p q hnodup.2.2 hp' hq' heq

private lemma filter_length_insert_two {α : Type*} [DecidableEq α]
    (L : List (α × α)) (hL : L.Nodup) (V : Finset α) (y y' : α)
    (p : α × α) (hpL : p ∈ L) (hp_eq : (p.1 = y ∧ p.2 = y') ∨ (p.1 = y' ∧ p.2 = y))
    (huniq : ∀ q ∈ L, (q.1 = y ∨ q.1 = y') → q = p)
    (hyV : y ∉ V) (hy'V : y' ∉ V) :
    (L.filter (fun q => decide (q.1 ∈ insert y (insert y' V)))).length =
      (L.filter (fun q => decide (q.1 ∈ V))).length + 1 := by
  induction L with
  | nil => exact (lsNMN hpL).elim
  | cons a t ih =>
    have hat : a ∉ t := (lsNC.mp hL).1
    have ht : t.Nodup := (lsNC.mp hL).2
    rcases lsMC.mp hpL with hpa | hp
    · have hp_old : decide (p.1 ∈ V) = false := by
        rw [decide_eq_false_iff_not]
        rcases hp_eq with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact h1 ▸ hyV
        · exact h1 ▸ hy'V
      have hp_new : decide (p.1 ∈ insert y (insert y' V)) = true := by
        rw [decide_eq_true_eq]
        rcases hp_eq with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact h1 ▸ fsMIS _ _
        · exact h1 ▸ fsMIOM (fsMIS _ _)
      have hcongr : t.filter (fun q => decide (q.1 ∈ insert y (insert y' V))) =
          t.filter (fun q => decide (q.1 ∈ V)) := by
        refine List.filter_congr fun q hqt => ?_
        have hqn : q ≠ p := fun h => hat (hpa ▸ h ▸ hqt)
        have hqnot : ¬ (q.1 = y ∨ q.1 = y') := fun h => hqn (huniq q (lsMCOM _ hqt) h)
        have hiff : q.1 ∈ insert y (insert y' V) ↔ q.1 ∈ V := by simp only [fsMI2]; tauto
        simp only [hiff]
      rw [← hpa]
      simp only [lsFC, hp_old, hp_new, Bool.false_eq_true, ↓reduceIte, hcongr, lsLC]
    · have ha_neq : a ≠ p := fun h => hat (h ▸ hp)
      have ha_not : ¬ (a.1 = y ∨ a.1 = y') := fun h => ha_neq (huniq a lsMCS h)
      have hiff : a.1 ∈ insert y (insert y' V) ↔ a.1 ∈ V := by simp only [fsMI2]; tauto
      have hsame : decide (a.1 ∈ insert y (insert y' V)) = decide (a.1 ∈ V) := by simp only [hiff]
      have ih' := ih ht hp (fun q hqt h => huniq q (lsMCOM _ hqt) h)
      simp only [lsFC, hsame]
      cases h : decide (a.1 ∈ V)
      · simp only [Bool.false_eq_true, ↓reduceIte, ih']
      · simp only [↓reduceIte, lsLC, ih']

private lemma build_closed_walk {t : ℕ} {R : SimpleGraph (Fin t)}
    (chosen : List (Fin t × Fin t)) (hchosen_ne : chosen ≠ [])
    (hchosen_adj : ∀ p ∈ chosen, R.Adj p.1 p.2)
    (hchosen_nodup : (chosen.flatMap (fun p => [p.1, p.2])).Nodup)
    (hchosen_reach : ∀ p ∈ chosen, ∀ q ∈ chosen, R.Reachable p.1 q.1) :
    ∃ W : List (Fin t × Fin t × Bool),
      W ≠ [] ∧
      (∀ e ∈ W, R.Adj e.1 e.2.1) ∧
      W.IsChain (fun a b => a.2.1 = b.1) ∧
      (∀ h : W ≠ [], (W.getLast h).2.1 = (W.head h).1) ∧
      (∀ h : W ≠ [], (W.getLast h).2.2 = false) ∧
      Even W.length ∧ 2 ≤ W.length ∧ W.length ≤ 2 * t ∧
      chosen.length ≤ W.length / 2 ∧
      (chosen.length = 1 → W.length = 2) ∧
      W.countP (·.2.2) = chosen.length ∧
      ((W.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1])).Nodup := by
  classical
  rcases chosen with _ | ⟨⟨u₁, v₁⟩, rest_ch⟩
  · exact (hchosen_ne rfl).elim
  have h1_mem : (u₁, v₁) ∈ (u₁, v₁) :: rest_ch := lsMCS
  have h1_adj : R.Adj u₁ v₁ := hchosen_adj _ h1_mem
  have huv1 : u₁ ≠ v₁ := R.ne_of_adj h1_adj
  set W₀ : List (Fin t × Fin t × Bool) := [(u₁, v₁, true), (v₁, u₁, false)]
  set V₀ : Finset (Fin t) := {u₁, v₁}
  have hV₀_card : V₀.card = 2 := Finset.card_pair huv1
  have ht2 : 2 ≤ t := by
    have h1 : V₀.card ≤ t := by simpa using fsCLU V₀
    omega
  by_cases hrest : rest_ch = []
  · subst hrest
    refine ⟨W₀, by simp [W₀], ?_, lsCC rfl (lsSingl _),
      by simp [W₀], by simp [W₀], ⟨1, rfl⟩, by simp [W₀], by simp [W₀]; omega,
      by simp [W₀], fun _ => by simp [W₀], by simp [W₀], by simp [W₀, huv1]⟩
    intro e he
    simp only [W₀, lsMC, lsMS, lsNMN, or_false] at he
    rcases he with rfl | rfl
    · exact h1_adj
    · exact h1_adj.symm
  set ch := (u₁, v₁) :: rest_ch
  have hch_nodup : ch.Nodup := by
    have : ∀ (L : List (Fin t × Fin t)), (L.flatMap (fun p => [p.1, p.2])).Nodup → L.Nodup := by
      intro L h
      induction L with
      | nil => simp
      | cons a ts ih =>
        simp only [lsFC2, lsCA, lsNA, lsNC] at h
        refine lsNC.mpr ⟨fun ha => ?_, ih h.2.2⟩
        exact h.1 (lsMCOM _ (lsMF2.mpr ⟨a, ha, lsMCS⟩))
    exact this ch hchosen_nodup
  have hstep : ∀ n : ℕ, ∀ (W : List (Fin t × Fin t × Bool)) (V : Finset (Fin t)),
      t - V.card = n →
      W ≠ [] →
      (∀ e ∈ W, R.Adj e.1 e.2.1) →
      W.IsChain (fun a b => a.2.1 = b.1) →
      (∀ h : W ≠ [], (W.getLast h).2.1 = (W.head h).1) →
      (∀ h : W ≠ [], (W.getLast h).2.2 = false) →
      u₁ ∈ V →
      (∀ e ∈ W, e.1 ∈ V ∧ e.2.1 ∈ V) →
      (∀ v ∈ V, ∃ e ∈ W, e.1 = v) →
      W.length = 2 * (V.card - 1) → 2 ≤ V.card →
      (∀ p ∈ ch, (p.1 ∈ V ∧ p.2 ∈ V) ∨ (p.1 ∉ V ∧ p.2 ∉ V)) →
      W.countP (·.2.2) = (ch.filter (fun p => decide (p.1 ∈ V))).length →
      ((W.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1])).Nodup →
      ∃ W' : List (Fin t × Fin t × Bool),
        W' ≠ [] ∧
        (∀ e ∈ W', R.Adj e.1 e.2.1) ∧
        W'.IsChain (fun a b => a.2.1 = b.1) ∧
        (∀ h : W' ≠ [], (W'.getLast h).2.1 = (W'.head h).1) ∧
        (∀ h : W' ≠ [], (W'.getLast h).2.2 = false) ∧
        Even W'.length ∧ 2 ≤ W'.length ∧ W'.length ≤ 2 * t ∧
        ch.length ≤ W'.length / 2 ∧
        (ch.length = 1 → W'.length = 2) ∧
        W'.countP (·.2.2) = ch.length ∧
        ((W'.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1])).Nodup := by
    intro n
    induction n using natSIO with
    | _ n ih =>
      intro W V hn hWne hWadj hWchain hWwrap hWlastf hu1V hWV hVW hWlen hV2 hchInv hWcnt hWnodup
      by_cases hall : ∀ p ∈ ch, p.1 ∈ V ∧ p.2 ∈ V
      · have hfilt : ch.filter (fun p => decide (p.1 ∈ V)) = ch :=
          List.filter_eq_self.mpr fun p hp => decide_eq_true (hall p hp).1
        have hch_sub : ∀ z ∈ ch.flatMap (fun p => [p.1, p.2]), z ∈ V := by
          intro z hz
          rw [lsMF2] at hz
          obtain ⟨p, hp, hzp⟩ := hz
          rcases lsMC.mp hzp with rfl | hzp
          · exact (hall p hp).1
          · rw [lsMS] at hzp; subst hzp; exact (hall p hp).2
        have h2ch : 2 * ch.length ≤ V.card := by
          have h1 : (ch.flatMap (fun p => [p.1, p.2])).toFinset ⊆ V := fun z hz =>
            hch_sub z (lsMT.mp hz)
          have h2 := fsCLC h1
          rw [lsTCON hchosen_nodup] at h2
          have h3 : (ch.flatMap (fun p => [p.1, p.2])).length = 2 * ch.length := by
            clear h1 h2 hch_sub hfilt hall
            induction ch with
            | nil => simp
            | cons a ts ihc => simp [ihc]; omega
          omega
        have hVt : V.card ≤ t := by simpa using fsCLU V
        refine ⟨W, hWne, hWadj, hWchain, hWwrap, hWlastf, ?_, by omega, by omega, by omega,
          fun hch1 => by exfalso; simp [ch] at hch1; exact hrest hch1, ?_, hWnodup⟩
        · exact ⟨V.card - 1, by omega⟩
        · rw [hWcnt, hfilt]
      · push_neg at hall
        obtain ⟨p, hp_ch, hp_not⟩ := hall
        have hp_out : p.1 ∉ V ∧ p.2 ∉ V := by
          rcases hchInv p hp_ch with h | h
          · exact (hp_not h.1 h.2).elim
          · exact h
        obtain ⟨x, y, hxyAdj, hxV, hyV⟩ :=
          walk_boundary_edge hu1V hp_out.1 (hchosen_reach (u₁, v₁) h1_mem p hp_ch)
        obtain ⟨ex, hexW, hex1⟩ := hVW x hxV
        by_cases hy_ch : ∃ q ∈ ch, q.1 = y ∨ q.2 = y
        · obtain ⟨q, hq_ch, hqy⟩ := hy_ch
          set y' := if q.1 = y then q.2 else q.1
          have hy'_eq : (q.1 = y ∧ q.2 = y') ∨ (q.1 = y' ∧ q.2 = y) := by
            by_cases h : q.1 = y
            · exact orInl ⟨h, by simp [y', h]⟩
            · exact orInr ⟨by simp [y', h], hqy.resolve_left h⟩
          have hq_adj : R.Adj y y' := by
            rcases hy'_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [← h1, ← h2]; exact hchosen_adj q hq_ch
            · rw [← h1, ← h2]; exact (hchosen_adj q hq_ch).symm
          have hyy' : y ≠ y' := R.ne_of_adj hq_adj
          have hy'V : y' ∉ V := by
            rcases hchInv q hq_ch with h | h
            · exfalso
              rcases hqy with h1 | h1
              · exact hyV (h1 ▸ h.1)
              · exact hyV (h1 ▸ h.2)
            · rcases hy'_eq with ⟨_, h2⟩ | ⟨h1, _⟩
              · exact h2 ▸ h.2
              · exact h1 ▸ h.1
          set ins : List (Fin t × Fin t × Bool) :=
            [(x, y, false), (y, y', true), (y', y, false), (y, x, false)]
          have hins_ne : ins ≠ [] := by simp [ins]
          have hins_chain : ins.IsChain (fun a b => a.2.1 = b.1) := by
            simp only [ins]
            exact lsCC rfl (lsCC rfl
              (lsCC rfl (lsSingl _)))
          obtain ⟨hne', hhead', hlast', hlen', hchain', hmem', hperm'⟩ :=
            spliceAt_props x ins W hWne ⟨ex, hexW, hex1⟩ hWchain hins_ne rfl rfl hins_chain
          set W' := spliceAt x ins W
          set V' := insert y (insert y' V)
          have hV'card : V'.card = V.card + 2 := by
            have hy_ins : y ∉ insert y' V := by
              simp [hyy', hyV]
            rw [fsCION hy_ins, fsCION hy'V]
          have hVt : V.card ≤ t := by simpa using fsCLU V
          have hV't : V'.card ≤ t := by simpa using fsCLU V'
          have hlt : t - V'.card < n := by omega
          refine ih _ hlt W' V' rfl hne' ?_ hchain' ?_ ?_ ?_ ?_ ?_ ?_ (by omega) ?_ ?_ ?_
          · intro e he
            rcases (hmem' e).mp he with he_ins | he_W
            · simp only [ins, lsMC, lsMS, lsNMN, or_false] at he_ins
              rcases he_ins with rfl | rfl | rfl | rfl
              · exact hxyAdj
              · exact hq_adj
              · exact hq_adj.symm
              · exact hxyAdj.symm
            · exact hWadj e he_W
          · intro h'
            rw [hlast' h', hhead' h', hWwrap hWne]
          · intro h'
            rw [hlast' h', hWlastf hWne]
          · exact fsMIOM (fsMIOM hu1V)
          · intro e he
            rcases (hmem' e).mp he with he_ins | he_W
            · simp only [ins, lsMC, lsMS, lsNMN, or_false] at he_ins
              rcases he_ins with rfl | rfl | rfl | rfl
              · exact ⟨fsMIOM (fsMIOM hxV),
                       fsMIS _ _⟩
              · exact ⟨fsMIS _ _,
                       fsMIOM (fsMIS _ _)⟩
              · exact ⟨fsMIOM (fsMIS _ _),
                       fsMIS _ _⟩
              · exact ⟨fsMIS _ _,
                       fsMIOM (fsMIOM hxV)⟩
            · have := hWV e he_W
              exact ⟨fsMIOM (fsMIOM this.1),
                     fsMIOM (fsMIOM this.2)⟩
          · intro v hv
            simp only [V', fsMI2] at hv
            rcases hv with hvy | hvy' | hv
            · exact ⟨(y, y', true), (hmem' _).mpr (orInl (by simp [ins])), hvy.symm⟩
            · exact ⟨(y', y, false), (hmem' _).mpr (orInl (by simp [ins])), hvy'.symm⟩
            · obtain ⟨e, heW, he1⟩ := hVW v hv
              exact ⟨e, (hmem' _).mpr (orInr heW), he1⟩
          · rw [hlen', hV'card, hWlen]; simp [ins]; omega
          · intro r hr
            rcases hchInv r hr with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
            · exact orInl ⟨fsMIOM (fsMIOM hr1),
                            fsMIOM (fsMIOM hr2)⟩
            · by_cases hr_eq : r = q
              · subst hr_eq
                rcases hy'_eq with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · exact orInl ⟨h1 ▸ fsMIS _ _,
                                h2 ▸ fsMIOM (fsMIS _ _)⟩
                · exact orInl ⟨h1 ▸ fsMIOM (fsMIS _ _),
                                h2 ▸ fsMIS _ _⟩
              · refine orInr ⟨?_, ?_⟩
                · simp only [V', fsMI2, not_or]
                  refine ⟨fun h => hr_eq (nodup_flatMap_pair_unique ch q r hchosen_nodup hq_ch hr ?_),
                          fun h => hr_eq (nodup_flatMap_pair_unique ch q r hchosen_nodup hq_ch hr ?_), hr1⟩
                  · rcases hy'_eq with ⟨h1, _⟩ | ⟨_, h2⟩ <;> [exact orInl (h.trans h1.symm); exact orInr (orInl (h.trans h2.symm))]
                  · rcases hy'_eq with ⟨_, h2⟩ | ⟨h1, _⟩ <;> [exact orInr (orInl (h.trans h2.symm)); exact orInl (h.trans h1.symm)]
                · simp only [V', fsMI2, not_or]
                  refine ⟨fun h => hr_eq (nodup_flatMap_pair_unique ch q r hchosen_nodup hq_ch hr ?_),
                          fun h => hr_eq (nodup_flatMap_pair_unique ch q r hchosen_nodup hq_ch hr ?_), hr2⟩
                  · rcases hy'_eq with ⟨h1, _⟩ | ⟨_, h2⟩ <;> [exact orInr (orInr (orInl (h.trans h1.symm))); exact orInr (orInr (orInr (h.trans h2.symm)))]
                  · rcases hy'_eq with ⟨_, h2⟩ | ⟨h1, _⟩ <;> [exact orInr (orInr (orInr (h.trans h2.symm))); exact orInr (orInr (orInl (h.trans h1.symm)))]
          · rw [List.countP_eq_length_filter] at hWcnt ⊢
            have hperm_len := hperm'.length_eq
            have hins_filt : ins.filter (·.2.2) = [(y, y', true)] := by simp [ins]
            rw [hins_filt, List.length_append] at hperm_len
            simp only [List.length_singleton] at hperm_len
            have huniq_q : ∀ r ∈ ch, (r.1 = y ∨ r.1 = y') → r = q := by
              intro r hr h
              refine nodup_flatMap_pair_unique ch q r hchosen_nodup hq_ch hr ?_
              rcases h with h | h
              · rcases hy'_eq with ⟨h1, _⟩ | ⟨_, h2⟩
                · exact orInl (h.trans h1.symm)
                · exact orInr (orInl (h.trans h2.symm))
              · rcases hy'_eq with ⟨_, h2⟩ | ⟨h1, _⟩
                · exact orInr (orInl (h.trans h2.symm))
                · exact orInl (h.trans h1.symm)
            rw [hperm_len, hWcnt, filter_length_insert_two ch hch_nodup V y y' q hq_ch hy'_eq huniq_q hyV hy'V]
            omega
          · have hperm_flat : List.Perm ((W'.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1]))
                (y :: y' :: (W.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1])) := by
              have h1 := hperm'.flatMap (fun e _ => List.Perm.refl [e.1, e.2.1])
              simpa [ins] using h1
            rw [hperm_flat.nodup_iff, lsNC, lsNC]
            refine ⟨?_, ?_, hWnodup⟩
            · intro h
              rcases lsMC.mp h with hy0 | h
              · exact hyy' hy0
              · rw [lsMF2] at h
                rcases h with ⟨e, he, hye⟩
                have heW : e ∈ W := (lsMF.mp he).1
                rcases lsMC.mp hye with hye | hye
                · exact hyV (hye ▸ (hWV e heW).1)
                · rw [lsMS] at hye
                  exact hyV (hye ▸ (hWV e heW).2)
            · rw [lsMF2]
              rintro ⟨e, he, hy'e⟩
              have heW : e ∈ W := (lsMF.mp he).1
              rcases lsMC.mp hy'e with hy'e | hy'e
              · exact hy'V (hy'e ▸ (hWV e heW).1)
              · rw [lsMS] at hy'e
                exact hy'V (hy'e ▸ (hWV e heW).2)
        · push_neg at hy_ch
          set ins : List (Fin t × Fin t × Bool) := [(x, y, false), (y, x, false)]
          have hins_ne : ins ≠ [] := by simp [ins]
          have hins_chain : ins.IsChain (fun a b => a.2.1 = b.1) := by
            simp only [ins]
            exact lsCC rfl (lsSingl _)
          obtain ⟨hne', hhead', hlast', hlen', hchain', hmem', hperm'⟩ :=
            spliceAt_props x ins W hWne ⟨ex, hexW, hex1⟩ hWchain hins_ne rfl rfl hins_chain
          set W' := spliceAt x ins W
          set V' := insert y V
          have hV'card : V'.card = V.card + 1 := fsCION hyV
          have hV't : V'.card ≤ t := by simpa using fsCLU V'
          have hlt : t - V'.card < n := by omega
          refine ih _ hlt W' V' rfl hne' ?_ hchain' ?_ ?_ ?_ ?_ ?_ ?_ (by omega) ?_ ?_ ?_
          · intro e he
            rcases (hmem' e).mp he with he_ins | he_W
            · simp only [ins, lsMC, lsMS, lsNMN, or_false] at he_ins
              rcases he_ins with rfl | rfl
              · exact hxyAdj
              · exact hxyAdj.symm
            · exact hWadj e he_W
          · intro h'; rw [hlast' h', hhead' h', hWwrap hWne]
          · intro h'; rw [hlast' h', hWlastf hWne]
          · exact fsMIOM hu1V
          · intro e he
            rcases (hmem' e).mp he with he_ins | he_W
            · simp only [ins, lsMC, lsMS, lsNMN, or_false] at he_ins
              rcases he_ins with rfl | rfl
              · exact ⟨fsMIOM hxV, fsMIS _ _⟩
              · exact ⟨fsMIS _ _, fsMIOM hxV⟩
            · have := hWV e he_W
              exact ⟨fsMIOM this.1, fsMIOM this.2⟩
          · intro v hv
            rcases fsMI2.mp hv with hvy | hv
            · exact ⟨(y, x, false), (hmem' _).mpr (orInl (by simp [ins])), hvy.symm⟩
            · obtain ⟨e, heW, he1⟩ := hVW v hv
              exact ⟨e, (hmem' _).mpr (orInr heW), he1⟩
          · rw [hlen', hV'card, hWlen]; simp [ins]; omega
          · intro r hr
            rcases hchInv r hr with ⟨hr1, hr2⟩ | ⟨hr1, hr2⟩
            · exact orInl ⟨fsMIOM hr1, fsMIOM hr2⟩
            · exact orInr ⟨fun h => by
                  rcases fsMI2.mp h with h | h
                  · exact (hy_ch r hr).1 h
                  · exact hr1 h,
                fun h => by
                  rcases fsMI2.mp h with h | h
                  · exact (hy_ch r hr).2 h
                  · exact hr2 h⟩
          · rw [List.countP_eq_length_filter] at hWcnt ⊢
            have hperm_len := hperm'.length_eq
            have hins_filt : ins.filter (·.2.2) = [] := by simp [ins]
            rw [hins_filt, lsNA] at hperm_len
            have hcongr : ch.filter (fun r => decide (r.1 ∈ V')) = ch.filter (fun r => decide (r.1 ∈ V)) := by
              refine List.filter_congr fun r hr => ?_
              have hry : r.1 ≠ y := fun h => (hy_ch r hr).1 h
              simp [V', hry]
            rw [hperm_len, hWcnt, hcongr]
          · have hperm_flat : List.Perm ((W'.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1]))
                ((W.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1])) := by
              have h1 := hperm'.flatMap (fun e _ => List.Perm.refl [e.1, e.2.1])
              simpa [ins] using h1
            exact hperm_flat.nodup_iff.mpr hWnodup
  have hchInv₀ : ∀ p ∈ ch, (p.1 ∈ V₀ ∧ p.2 ∈ V₀) ∨ (p.1 ∉ V₀ ∧ p.2 ∉ V₀) := by
    intro p hp
    by_cases hp1 : p = (u₁, v₁)
    · subst hp1; exact orInl ⟨by simp [V₀], by simp [V₀]⟩
    · refine orInr ⟨?_, ?_⟩
      · simp only [V₀, fsMI2, fsMS2, not_or]
        exact ⟨fun h => hp1 (nodup_flatMap_pair_unique ch (u₁, v₁) p hchosen_nodup h1_mem hp (orInl h)),
               fun h => hp1 (nodup_flatMap_pair_unique ch (u₁, v₁) p hchosen_nodup h1_mem hp (orInr (orInl h)))⟩
      · simp only [V₀, fsMI2, fsMS2, not_or]
        exact ⟨fun h => hp1 (nodup_flatMap_pair_unique ch (u₁, v₁) p hchosen_nodup h1_mem hp (orInr (orInr (orInl h)))),
               fun h => hp1 (nodup_flatMap_pair_unique ch (u₁, v₁) p hchosen_nodup h1_mem hp (orInr (orInr (orInr h))))⟩
  have hWcnt₀ : W₀.countP (·.2.2) = (ch.filter (fun p => decide (p.1 ∈ V₀))).length := by
    have hfilt : ch.filter (fun p => decide (p.1 ∈ V₀)) = [(u₁, v₁)] := by
      simp only [ch, lsFC, decide_eq_true (by simp [V₀] : u₁ ∈ V₀),
        ↓reduceIte, List.cons.injEq, true_and]
      rw [List.filter_eq_nil_iff]
      intro p hp
      have hne1 : p ≠ (u₁, v₁) := by
        intro h; subst h
        simp only [ch, lsFC2, lsCA, lsNA, lsNC] at hchosen_nodup
        exact hchosen_nodup.1 (lsMCOM _ (lsMF2.mpr ⟨(u₁, v₁), hp, lsMCS⟩))
      have hp_out : p.1 ∉ V₀ := by
        rcases hchInv₀ p (lsMCOM _ hp) with h | h
        · exfalso
          exact hne1 (nodup_flatMap_pair_unique ch (u₁, v₁) p hchosen_nodup h1_mem (lsMCOM _ hp)
            (orInl (by
              rcases fsMI2.mp h.1 with h1 | h1
              · exact h1
              · rw [fsMS2] at h1
                exfalso; exact hne1 (nodup_flatMap_pair_unique ch (u₁, v₁) p hchosen_nodup h1_mem
                  (lsMCOM _ hp) (orInr (orInl h1))))))
        · exact h.1
      simp [hp_out]
    simp [W₀, hfilt]
  refine hstep (t - V₀.card) W₀ V₀ rfl (by simp [W₀]) ?_ ?_ (by simp [W₀]) (by simp [W₀])
    (by simp [V₀]) ?_ ?_ (by simp [W₀, hV₀_card]) (by omega) hchInv₀ hWcnt₀ ?_
  · intro e he
    simp only [W₀, lsMC, lsMS, lsNMN, or_false] at he
    rcases he with rfl | rfl
    · exact h1_adj
    · exact h1_adj.symm
  · exact lsCC rfl (lsSingl _)
  · intro e he
    simp only [W₀, lsMC, lsMS, lsNMN, or_false] at he
    rcases he with rfl | rfl <;> simp [V₀]
  · intro v hv
    simp only [V₀, fsMI2, fsMS2] at hv
    rcases hv with hvu | hvv
    · rw [hvu]; exact ⟨(u₁, v₁, true), by simp [W₀], rfl⟩
    · rw [hvv]; exact ⟨(v₁, u₁, false), by simp [W₀], rfl⟩
  · simp [W₀, huv1]

/- ### Length assignment and cycle assembly -/

private def assignList {α : Type*} (B : ℕ) (W : List (α × α × Bool)) (D : ℕ) : List ℕ :=
  match W with
  | [] => []
  | e :: rest =>
    if e.2.2 then min B D :: assignList B rest (D - min B D)
    else 0 :: assignList B rest D

private lemma assignList_length {α : Type*} (B : ℕ) :
    ∀ (W : List (α × α × Bool)) (D : ℕ), (assignList B W D).length = W.length := by
  intro W
  induction W with
  | nil => intro D; simp [assignList]
  | cons e rest ih =>
    intro D
    unfold assignList
    by_cases hf : e.2.2 = true <;> simp [hf, ih]

private lemma assignList_props {α : Type*} (B : ℕ) :
    ∀ (W : List (α × α × Bool)) (D : ℕ),
      D ≤ W.countP (·.2.2) * B →
      (assignList B W D).length = W.length ∧
      (assignList B W D).sum = D ∧
      (∀ i (hi : i < W.length), (assignList B W D)[i]'(assignList_length B W D ▸ hi) ≤ B) ∧
      (∀ i (hi : i < W.length), W[i].2.2 = false →
        (assignList B W D)[i]'(assignList_length B W D ▸ hi) = 0) := by
  intro W
  induction W with
  | nil =>
    intro D hD
    simp [assignList] at hD ⊢
    omega
  | cons e rest ih =>
    intro D hD
    by_cases hf : e.2.2 = true
    · have hD' : D - min B D ≤ rest.countP (·.2.2) * B := by
        have hcnt : (e :: rest).countP (·.2.2) = rest.countP (·.2.2) + 1 := by
          simp [List.countP_cons, hf]
        rw [hcnt, Nat.add_one_mul] at hD
        by_cases hBD : B ≤ D
        · rw [min_eq_left hBD]; omega
        · rw [min_eq_right (Nat.le_of_not_le hBD)]; simp
      obtain ⟨hlen, hsum, hleB, hzero⟩ := ih (D - min B D) hD'
      refine ⟨assignList_length B (e :: rest) D, ?_, ?_, ?_⟩
      · simp only [assignList, if_pos hf, List.sum_cons, hsum]; omega
      · intro i hi
        rcases i with _ | i
        · simp only [assignList, if_pos hf, lsGCZ]; exact min_le_left B D
        · simp only [assignList, if_pos hf, lsGCS]
          exact hleB i (by simpa using hi)
      · intro i hi hif
        rcases i with _ | i
        · simp [hf] at hif
        · simp only [assignList, if_pos hf, lsGCS]
          exact hzero i (by simpa using hi) (by simpa using hif)
    · have hf' : e.2.2 = false := Bool.eq_false_iff.mpr hf
      have hcnt : (e :: rest).countP (·.2.2) = rest.countP (·.2.2) := by
        simp [List.countP_cons, hf']
      rw [hcnt] at hD
      obtain ⟨hlen, hsum, hleB, hzero⟩ := ih D hD
      refine ⟨assignList_length B (e :: rest) D, ?_, ?_, ?_⟩
      · simp only [assignList, if_neg hf, List.sum_cons, zero_add, hsum]
      · intro i hi
        rcases i with _ | i
        · simp only [assignList, if_neg hf, lsGCZ]; omega
        · simp only [assignList, if_neg hf, lsGCS]
          exact hleB i (by simpa using hi)
      · intro i hi hif
        rcases i with _ | i
        · simp only [assignList, if_neg hf, lsGCZ]
        · simp only [assignList, if_neg hf, lsGCS]
          exact hzero i (by simpa using hi) (by simpa using hif)

private lemma sum_range_eq_list_sum : ∀ (l : List ℕ) (f : ℕ → ℕ),
    (∀ i (hi : i < l.length), f i = l[i]) →
    ∑ i ∈ fsRange l.length, f i = l.sum := by
  intro l
  induction l with
  | nil => simp
  | cons a t ih =>
    intro f hf
    rw [lsLC, Finset.sum_range_succ', List.sum_cons, add_comm]
    congr 1
    · exact hf 0 (Nat.zero_lt_succ _)
    · exact ih (fun i => f (i + 1)) (fun i hi => by
        rw [hf (i + 1) (Nat.succ_lt_succ hi), lsGCS])

private lemma cycleGraph_of_cycleList {N n : ℕ} (G : SimpleGraph (Fin N)) (hn4 : 4 ≤ n)
    (cyc : List (Fin N)) (hlen : cyc.length = n) (hnodup : cyc.Nodup)
    (hstep : ∀ i (hi : i + 1 < cyc.length), G.Adj cyc[i] cyc[i + 1])
    (hwrap : ∀ h : 0 < cyc.length, G.Adj cyc[cyc.length - 1] cyc[0]) :
    (cycleGraph n).IsContained G := by
  have hn0 : 0 < n := by omega
  haveI : NeZero n := ⟨by omega⟩
  let f : Fin n → Fin N := fun i => cyc[i.val]'(hlen ▸ i.isLt)
  have hinj : Function.Injective f := by
    intro i j hij
    exact Fin.ext (congrArg (@Fin.val cyc.length)
      (List.nodup_iff_injective_getElem.mp hnodup (a₁ := ⟨i.val, hlen ▸ i.isLt⟩) (a₂ := ⟨j.val, hlen ▸ j.isLt⟩) hij))
  let hhom : (cycleGraph n) →g G := ⟨f, by
    intro a b hab
    have hcases : (a - b).val = 1 ∨ (b - a).val = 1 := SimpleGraph.cycleGraph_adj'.mp hab
    have step_adj : ∀ x y : Fin n, (y - x).val = 1 → G.Adj (f x) (f y) := by
      intro x y hxy
      have hy_val : y.val = (x.val + 1) % n := by
        rw [Fin.coe_sub] at hxy
        by_cases hle : x.val ≤ y.val
        · have h1 : y.val - x.val = 1 := by
            rw [show (n - x.val + y.val) % n = (n + (y.val - x.val)) % n by congr 1; omega,
              Nat.add_mod_left, natMEOL (by omega)] at hxy
            exact hxy
          have : x.val + 1 < n := by omega
          rw [natMEOL this]; omega
        · have h1 : n - x.val + y.val = 1 := by
            rw [natMEOL (by omega)] at hxy; exact hxy
          have hx_last : x.val = n - 1 := by omega
          have hy0 : y.val = 0 := by omega
          rw [hx_last, show n - 1 + 1 = n by omega, Nat.mod_self, hy0]
      rcases eq_or_ne (x.val + 1) n with hlast | hlt
      · have hy0 : y.val = 0 := by rw [hy_val, hlast, Nat.mod_self]
        have hxlast : x.val = cyc.length - 1 := by omega
        simpa [f, hxlast, hy0] using hwrap (hlen ▸ hn0)
      · have hlt' : x.val + 1 < cyc.length := by omega
        have hy' : y.val = x.val + 1 := by rw [hy_val, natMEOL (by omega)]
        simpa [f, hy'] using hstep x.val hlt'
    rcases hcases with h | h
    · exact (step_adj b a h).symm
    · exact step_adj a b h⟩
  exact ⟨⟨hhom, fun i j h => hinj h⟩⟩

private lemma assemble_cycle {N n L : ℕ} (G : SimpleGraph (Fin N)) (hn4 : 4 ≤ n) (hL : 0 < L)
    (z : ℕ → Fin N) (segs : ℕ → List (Fin N))
    (hne : ∀ i < L, segs i ≠ [])
    (hhead : ∀ i < L, ∀ h : segs i ≠ [], (segs i).head h = z i)
    (hnodup : ∀ i < L, (segs i).Nodup)
    (hchain : ∀ i < L, (segs i).IsChain G.Adj)
    (hnext : ∀ i < L, ∀ h : segs i ≠ [], G.Adj ((segs i).getLast h) (z ((i + 1) % L)))
    (hdisj : ∀ i₁ < L, ∀ i₂ < L, i₁ ≠ i₂ → Disjoint (segs i₁).toFinset (segs i₂).toFinset)
    (hsum : ∑ i ∈ fsRange L, (segs i).length = n) :
    (cycleGraph n).IsContained G := by
  have hbuild : ∀ k : ℕ, 1 ≤ k → k ≤ L →
      let pref := (List.range k).flatMap segs
      pref ≠ [] ∧
      (∀ h : pref ≠ [], pref.head h = z 0) ∧
      (∀ h : pref ≠ [], ∀ hk : segs (k - 1) ≠ [], pref.getLast h = (segs (k - 1)).getLast hk) ∧
      pref.Nodup ∧
      pref.IsChain G.Adj ∧
      pref.toFinset = (fsRange k).biUnion (fun i => (segs i).toFinset) ∧
      pref.length = ∑ i ∈ fsRange k, (segs i).length := by
    intro k hk1 hkL
    induction k with
    | zero => omega
    | succ k ih =>
      rcases eq_or_lt_of_le hk1 with hkeq1 | hkgt1
      · have hk0 : k = 0 := by omega
        subst hk0
        have h0ne : segs 0 ≠ [] := hne 0 hL
        refine ⟨by simpa using h0ne, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro _; simpa using hhead 0 hL h0ne
        · intro _ _; simp
        · simpa using hnodup 0 hL
        · simpa using hchain 0 hL
        · simp
        · simp
      · have hk1' : 1 ≤ k := by omega
        obtain ⟨hpne, hphead, hplast, hpnodup, hpchain, hpfin, hplen⟩ := ih hk1' (by omega)
        have hkne : segs k ≠ [] := hne k hkL
        have hk1ne : segs (k - 1) ≠ [] := hne (k - 1) (by omega)
        have heq_cat : (List.range (k + 1)).flatMap segs = (List.range k).flatMap segs ++ segs k := by
          rw [List.range_succ, List.flatMap_append, List.flatMap_singleton]
        rw [heq_cat]
        set pref := (List.range k).flatMap segs
        have hne' : pref ++ segs k ≠ [] := List.append_ne_nil_of_right_ne_nil _ hkne
        have hdisj_k : Disjoint pref.toFinset (segs k).toFinset := by
          rw [hpfin, Finset.disjoint_biUnion_left]
          intro i hi
          exact hdisj i (by rw [fsMR] at hi; omega) k hkL (by rw [fsMR] at hi; omega)
        refine ⟨hne', ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro h'
          rw [lsHAONN hpne, hphead hpne]
        · intro h' _
          simpa using List.getLast_append_of_ne_nil h' hkne
        · rw [lsNA2]
          refine ⟨hpnodup, hnodup k hkL, fun a ha b hb heq => ?_⟩
          subst heq
          exact fsDL.mp hdisj_k (lsMT.mpr ha) (lsMT.mpr hb)
        · refine isChain_append hpchain (hchain k hkL) ?_
          intro a ha b hb
          have ha' : a = pref.getLast hpne := (by
            rw [List.getLast?_eq_some_getLast hpne] at ha; simpa using ha : pref.getLast hpne = a).symm
          have hb' : b = (segs k).head hkne := (by
            rw [List.head?_eq_some_head hkne] at hb; simpa using hb : (segs k).head hkne = b).symm
          subst ha'; subst hb'
          rw [hplast hpne hk1ne, hhead k hkL hkne]
          have hmod : (k - 1 + 1) % L = k := by
            rw [show k - 1 + 1 = k by omega, natMEOL hkL]
          simpa [hmod] using hnext (k - 1) (by omega) hk1ne
        · rw [lsTA, hpfin, Finset.range_add_one, Finset.biUnion_insert, Finset.union_comm]
        · rw [List.length_append, hplen, Finset.sum_range_succ]
  obtain ⟨hcyne, hcyhead, hcylast, hcynodup, hcychain, _, hcylen⟩ := hbuild L hL le_rfl
  set cyc := (List.range L).flatMap segs
  have hL1ne : segs (L - 1) ≠ [] := hne (L - 1) (by omega)
  refine cycleGraph_of_cycleList G hn4 cyc (hcylen.trans hsum) hcynodup ?_ ?_
  · intro i hi
    exact lsIIG.mp hcychain i hi
  · intro h0
    have hne' : cyc ≠ [] := lsNNOLP h0
    have hlast_eq : cyc[cyc.length - 1] = cyc.getLast hne' := (lsGEG hne').symm
    have hhead_eq : cyc[0] = cyc.head hne' := (lsHEG hne').symm
    rw [hlast_eq, hhead_eq, hcylast hne' hL1ne, hcyhead hne']
    have hmod : (L - 1 + 1) % L = 0 := by rw [show L - 1 + 1 = L by omega, Nat.mod_self]
    simpa [hmod] using hnext (L - 1) (by omega) hL1ne

/- ### Bridge segment for a blown-up matching step -/

private lemma true_indices_disjoint {α : Type*} [DecidableEq α] :
    ∀ (W : List (α × α × Bool)),
      ((W.filter (·.2.2)).flatMap (fun e => [e.1, e.2.1])).Nodup →
      ∀ (i₁ i₂ : ℕ) (hi₁ : i₁ < W.length) (hi₂ : i₂ < W.length),
        i₁ < i₂ → W[i₁].2.2 = true → W[i₂].2.2 = true →
        Disjoint ({W[i₁].1, W[i₁].2.1} : Finset α) ({W[i₂].1, W[i₂].2.1} : Finset α) := by
  intro W
  induction W with
  | nil => intro _ i₁ _ hi₁; simp at hi₁
  | cons e rest ih =>
    intro hnodup i₁ i₂ hi₁ hi₂ hlt h1 h2
    have hnodup_rest : ((rest.filter (·.2.2)).flatMap (fun x => [x.1, x.2.1])).Nodup := by
      by_cases he : e.2.2 = true
      · simp only [lsFC, he, ↓reduceIte, lsFC2, lsCA,
          lsNA, lsNC] at hnodup
        exact hnodup.2.2
      · have he' : e.2.2 = false := Bool.eq_false_iff.mpr he
        simp only [lsFC, he', Bool.false_eq_true, ↓reduceIte] at hnodup
        exact hnodup
    rcases i₁ with _ | j₁ <;> rcases i₂ with _ | j₂
    · omega
    · simp only [lsGCZ] at h1
      simp only [lsFC, h1, ↓reduceIte, lsFC2, lsCA,
        lsNA, lsNC] at hnodup
      have hj₂ : j₂ < rest.length := by simpa using hi₂
      have hmem : rest[j₂]'hj₂ ∈ rest.filter (·.2.2) :=
        lsMF.mpr ⟨lsGM hj₂, by simpa using h2⟩
      have hm1 : (rest[j₂]'hj₂).1 ∈ (rest.filter (·.2.2)).flatMap (fun x => [x.1, x.2.1]) :=
        lsMF2.mpr ⟨rest[j₂]'hj₂, hmem, by simp⟩
      have hm2 : (rest[j₂]'hj₂).2.1 ∈ (rest.filter (·.2.2)).flatMap (fun x => [x.1, x.2.1]) :=
        lsMF2.mpr ⟨rest[j₂]'hj₂, hmem, by simp⟩
      rw [fsDL]
      intro z hz1 hz2
      simp only [lsGCZ, lsGCS, fsMI2,
        fsMS2] at hz1 hz2
      rcases hz1 with rfl | rfl <;> rcases hz2 with heq | heq
      · exact hnodup.1 (lsMCOM _ (heq ▸ hm1))
      · exact hnodup.1 (lsMCOM _ (heq ▸ hm2))
      · exact hnodup.2.1 (heq ▸ hm1)
      · exact hnodup.2.1 (heq ▸ hm2)
    · omega
    · exact ih hnodup_rest j₁ j₂ (by simpa using hi₁) (by simpa using hi₂) (by omega)
        (by simpa using h1) (by simpa using h2)

private lemma bridge_segment {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {d η : ℝ} (hη : 0 < η) (hd_gt : η < d)
    {U V ResU CapU BodyU BodyV : Finset (Fin N)}
    (hResU : ResU ⊆ U) (hCapU : CapU ⊆ U) (hBodyU : BodyU ⊆ U) (hBodyV : BodyV ⊆ V)
    (hdisjUV : Disjoint U V)
    (hRC : Disjoint ResU CapU) (hRB : Disjoint ResU BodyU) (hCB : Disjoint CapU BodyU)
    (huni : G.IsUniform η U V) (hd : d ≤ (G.edgeDensity U V : ℝ))
    (hUpos : 0 < U.card) (hVpos : 0 < V.card)
    (c : ℕ) (hcU : (U.card : ℝ) * η ≤ (c : ℝ)) (hcV : (V.card : ℝ) * η ≤ (c : ℝ))
    (hcBodyU : (c : ℝ) ≤ (d - η) * (BodyU.card : ℝ))
    (hCapCard : (U.card : ℝ) * η ≤ (CapU.card : ℝ))
    (hBodyUcard : (U.card : ℝ) * η ≤ (BodyU.card : ℝ))
    (hBodyVcard : (V.card : ℝ) * η ≤ (BodyV.card : ℝ))
    {zu zv : Fin N} (hzu : zu ∈ ResU)
    (hzu_deg : (d - η) * (BodyV.card : ℝ) < ((G.neighborFinset zu ∩ BodyV).card : ℝ))
    (hzv_deg : (d - η) * (CapU.card : ℝ) < ((G.neighborFinset zv ∩ CapU).card : ℝ))
    (hSend_big : (U.card : ℝ) * η ≤ (d - η) * (CapU.card : ℝ))
    (hPool_big : 3 * ((max U.card V.card : ℝ) * η + 1) ≤ (d - η) * (BodyV.card : ℝ))
    (ℓ : ℕ) (hℓ1 : 1 ≤ ℓ) (hℓ_len : ℓ ≤ min (BodyV.card - c) BodyU.card - 2 * c) :
    ∃ seg : List (Fin N),
      seg ≠ [] ∧
      seg.length = 2 * ℓ + 1 ∧
      (∀ h : seg ≠ [], seg.head h = zu) ∧
      (∀ h : seg ≠ [], G.Adj (seg.getLast h) zv) ∧
      seg.Nodup ∧
      seg.IsChain G.Adj ∧
      seg.toFinset ⊆ insert zu (BodyU ∪ BodyV ∪ CapU) := by
  set S_end := G.neighborFinset zv ∩ CapU
  have hSend_sub : S_end ⊆ U := fsISR.trans hCapU
  have hSend_card : (U.card : ℝ) * η ≤ (S_end.card : ℝ) := hSend_big.trans hzv_deg.le
  have huniVU : G.IsUniform η V U := huni.symm
  have hdVU : d ≤ (G.edgeDensity V U : ℝ) := by rwa [sgEC]
  set B_bad := V.filter (fun y => ((G.neighborFinset y ∩ S_end).card : ℝ) ≤ (d - η) * (S_end.card : ℝ))
  have hB_bad : (B_bad.card : ℝ) < (V.card : ℝ) * η :=
    card_bad_lt G hη huniVU hdVU hVpos hUpos hSend_sub hSend_card
  set Body'V := BodyV \ B_bad
  have hBody'V_sub : Body'V ⊆ V := Finset.sdiff_subset.trans hBodyV
  have hBody'V_card : BodyV.card - c ≤ Body'V.card := by
    have hB_le : B_bad.card ≤ c := by
      have h1 : (B_bad.card : ℝ) < (c : ℝ) := hB_bad.trans_le hcV
      exact_mod_cast h1.le
    have h2 : BodyV.card ≤ Body'V.card + B_bad.card := by
      calc BodyV.card ≤ (Body'V ∪ B_bad).card := fsCLC (fun x hx => by
            by_cases h : x ∈ B_bad
            · exact fsMUR _ h
            · exact fsMUL _ (fsMS.mpr ⟨hx, h⟩))
        _ ≤ Body'V.card + B_bad.card := fsCUL _ _
    omega
  set P := G.neighborFinset zu ∩ Body'V
  have hP_sub : P ⊆ V := fsISR.trans hBody'V_sub
  have hP_card : ((∅ : Finset (Fin N)).card : ℝ) + 2 * (V.card : ℝ) * η ≤ (P.card : ℝ) := by
    have h1 : (G.neighborFinset zu ∩ BodyV).card ≤ P.card + B_bad.card := by
      calc (G.neighborFinset zu ∩ BodyV).card
          ≤ (P ∪ B_bad).card := fsCLC (fun x hx => by
              rw [fsMI3] at hx
              by_cases h : x ∈ B_bad
              · exact fsMUR _ h
              · exact fsMUL _ (fsMI3.mpr ⟨hx.1, fsMS.mpr ⟨hx.2, h⟩⟩))
        _ ≤ P.card + B_bad.card := fsCUL _ _
    have h1r : ((G.neighborFinset zu ∩ BodyV).card : ℝ) ≤ (P.card : ℝ) + (B_bad.card : ℝ) := by
      exact_mod_cast h1
    have hmaxV : (V.card : ℝ) ≤ (max U.card V.card : ℝ) := by exact_mod_cast le_max_right U.card V.card
    simp only [Finset.card_empty, natCZ, zero_add]
    nlinarith
  obtain ⟨y₁, hy₁P, _, hy₁_BodyU, _⟩ := exists_good_two G hη hP_sub hVpos huniVU hdVU
    hUpos hBodyU hBodyUcard huniVU hdVU hUpos hBodyU hBodyUcard hP_card
  have hy₁_Body'V : y₁ ∈ Body'V := (fsMI3.mp hy₁P).2
  have hzy₁ : G.Adj zu y₁ := (G.mem_neighborFinset zu y₁).mp (fsMI3.mp hy₁P).1
  have hy₁_deg : c ≤ (G.neighborFinset y₁ ∩ BodyU).card := by
    exact_mod_cast (hcBodyU.trans_lt hy₁_BodyU).le
  have hc_pos : 0 < c := by
    have h1 : (0 : ℝ) < (U.card : ℝ) * η := by positivity
    exact_mod_cast h1.trans_le hcU
  have hdisj_BU : Disjoint Body'V BodyU :=
    hdisjUV.symm.mono hBody'V_sub hBodyU
  have hnoempty : ∀ X ⊆ Body'V, ∀ Y ⊆ BodyU, c ≤ X.card → c ≤ Y.card →
      ∃ x ∈ X, ∃ y ∈ Y, G.Adj x y :=
    no_empty_pair_of_uniform G hd_gt huniVU hdVU hBody'V_sub hBodyU hcV hcU
  obtain ⟨Q, hQne, hQhead, hQnodup, hQchain, hQsub, hQlen, hQalt⟩ :=
    dfs_long_path G Body'V BodyU hdisj_BU hc_pos hc_pos hnoempty y₁ hy₁_Body'V hy₁_deg
  have htake_le : 2 * ℓ - 1 ≤ Q.length := by
    have h1 : min (BodyV.card - c) BodyU.card ≤ min Body'V.card BodyU.card := by omega
    omega
  set Q' := Q.take (2 * ℓ - 1)
  have hQ'len : Q'.length = 2 * ℓ - 1 := List.length_take_of_le htake_le
  have hQ'ne : Q' ≠ [] := lsNNOLP (by omega)
  have hQ'head : Q'.head hQ'ne = y₁ := by
    rw [lsHEG hQ'ne]
    simp only [Q', List.getElem_take]
    rw [← lsHEG hQne, ← Option.some.injEq]
    rw [List.head?_eq_some_head hQne] at hQhead
    exact hQhead
  have hQ'nodup : Q'.Nodup := hQnodup.take
  have hQ'chain : Q'.IsChain G.Adj := by
    have h1 : Q'.IsChain (bipartAdj G Body'V BodyU) := hQchain.take (2 * ℓ - 1)
    exact h1.imp (fun {_ _} h => h.2)
  have hQ'sub : Q'.toFinset ⊆ BodyU ∪ BodyV := by
    intro x hx
    have hxQ : x ∈ Q := lsMOMT2 (lsMT.mp hx)
    rcases fsMU.mp (hQsub (lsMT.mpr hxQ)) with hV | hU
    · exact fsMUR _ (Finset.sdiff_subset hV)
    · exact fsMUL _ hU
  set y_last := Q'.getLast hQ'ne
  have hy_last_eq : y_last = Q[2 * ℓ - 2]'(by omega) := by
    change Q'.getLast hQ'ne = Q[2 * ℓ - 2]'(by omega)
    rw [lsGEG hQ'ne]
    simp only [Q', hQ'len]
    exact List.getElem_take
  have hy_last_Body'V : y_last ∈ Body'V := by
    rw [hy_last_eq]
    exact (hQalt (2 * ℓ - 2) (by omega)).1 ⟨ℓ - 1, by omega⟩
  have hy_last_bad : y_last ∉ B_bad := (fsMS.mp hy_last_Body'V).2
  have hy_last_V : y_last ∈ V := hBody'V_sub hy_last_Body'V
  have hy_last_deg : (d - η) * (S_end.card : ℝ) < ((G.neighborFinset y_last ∩ S_end).card : ℝ) := by
    by_contra! hle
    exact hy_last_bad (fsMF.mpr ⟨hy_last_V, hle⟩)
  have hy_last_pos : 0 < (G.neighborFinset y_last ∩ S_end).card := by
    have hSpos : (0 : ℝ) < (S_end.card : ℝ) := by
      have : (0 : ℝ) < (U.card : ℝ) * η := by positivity
      exact this.trans_le hSend_card
    have h1 : (0 : ℝ) < (d - η) * (S_end.card : ℝ) := mul_pos (sub_pos.mpr hd_gt) hSpos
    exact_mod_cast h1.trans hy_last_deg
  obtain ⟨x_last, hx_last⟩ := fsCP.mp hy_last_pos
  rw [fsMI3, sgMN] at hx_last
  have hx_last_CapU : x_last ∈ CapU := (fsMI3.mp hx_last.2).2
  have hx_last_zv : G.Adj x_last zv :=
    ((G.mem_neighborFinset zv x_last).mp (fsMI3.mp hx_last.2).1).symm
  set seg := zu :: (Q' ++ [x_last])
  have hseg_ne : seg ≠ [] := by simp [seg]
  have hzu_not_BUV : zu ∉ BodyU ∪ BodyV := by
    intro h
    rcases fsMU.mp h with hU | hV
    · exact fsDL.mp hRB hzu hU
    · exact fsDL.mp hdisjUV (hResU hzu) (hBodyV hV)
  have hx_not_BUV : x_last ∉ BodyU ∪ BodyV := by
    intro h
    rcases fsMU.mp h with hU | hV
    · exact fsDL.mp hCB hx_last_CapU hU
    · exact fsDL.mp hdisjUV (hCapU hx_last_CapU) (hBodyV hV)
  have hzu_ne_x : zu ≠ x_last := fun h =>
    fsDL.mp hRC hzu (h ▸ hx_last_CapU)
  refine ⟨seg, hseg_ne, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [seg, hQ'len]; omega
  · intro _; simp [seg]
  · intro _
    have h1 : seg.getLast hseg_ne = (Q' ++ [x_last]).getLast (by simp) :=
      lsGC (by simp)
    rw [h1, List.getLast_append_singleton]
    exact hx_last_zv
  · rw [show seg = zu :: (Q' ++ [x_last]) from rfl, lsNC]
    refine ⟨?_, ?_⟩
    · simp only [lsMA, lsMS, not_or]
      exact ⟨fun h => hzu_not_BUV (hQ'sub (lsMT.mpr h)), hzu_ne_x⟩
    · rw [lsNA2]
      refine ⟨hQ'nodup, List.nodup_singleton _, fun a ha b hb heq => ?_⟩
      rw [lsMS] at hb
      subst hb; subst heq
      exact hx_not_BUV (hQ'sub (lsMT.mpr ha))
  · refine List.IsChain.cons_of_ne_nil (by simp) ?_ ?_
    · refine isChain_append hQ'chain (List.isChain_singleton _) ?_
      intro a ha b hb
      have ha' : a = y_last := (by
        rw [List.getLast?_eq_some_getLast hQ'ne] at ha; simpa using ha : y_last = a).symm
      have hb' : b = x_last := (by simpa using hb : x_last = b).symm
      subst ha'; subst hb'
      exact hx_last.1
    · rw [lsHAONN hQ'ne, hQ'head]
      exact hzy₁
  · intro x hx
    simp only [seg, lsTC, lsTA, lsTN,
      fsMI2, fsMU, fsNE, or_false] at hx
    rcases hx with rfl | hxQ | rfl
    · exact fsMIS _ _
    · exact fsMIOM (fsMUL _ (by
        have := hQ'sub hxQ
        rcases fsMU.mp this with h | h
        · exact fsMUL _ h
        · exact fsMUR _ h))
    · exact fsMIOM (fsMUR _ hx_last_CapU)

/- ### Selecting tour transition vertices along closed walk W -/

set_option maxHeartbeats 800000 in
private lemma embed_tour_vertices {N t : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    {d η : ℝ} (hη : 0 < η)
    (parts : Fin t → Finset (Fin N)) (R : SimpleGraph (Fin t))
    (hparts_pos : ∀ i : Fin t, 0 < (parts i).card)
    (hR : ∀ u v : Fin t, R.Adj u v → G.IsUniform η (parts u) (parts v) ∧ d ≤ (G.edgeDensity (parts u) (parts v) : ℝ))
    (Res Cap Body : Fin t → Finset (Fin N))
    (hRes_sub : ∀ i, Res i ⊆ parts i) (hCap_sub : ∀ i, Cap i ⊆ parts i) (hBody_sub : ∀ i, Body i ⊆ parts i)
    (hRes_sz : ∀ i j, (parts j).card * η ≤ (Res i).card)
    (hCap_sz : ∀ i j, (parts j).card * η ≤ (Cap i).card)
    (hBody_sz : ∀ i j, (parts j).card * η ≤ (Body i).card)
    (L : ℕ) (w w' : ℕ → Fin t)
    (hw_adj : ∀ i < L, R.Adj (w i) (w' i))
    (hw'_eq : ∀ i, i + 1 < L → w' i = w (i + 1))
    (hw_wrap : w' (L - 1) = w 0)
    (len : ℕ → ℕ)
    (hlen_L : len (L - 1) = 0)
    (hL_ge : 2 ≤ L)
    (hL2_len0 : L = 2 → 0 < len 0)
    (hPool_Res : ∀ i, (L : ℝ) + 2 * ((parts i).card : ℝ) * η ≤ (Res i).card)
    (hPool_Send : ∀ i j, (parts j).card * η ≤ (d - η) * (Res i).card ∧
      (L : ℝ) + 2 * ((parts j).card : ℝ) * η ≤ (d - η) * (Res i).card)
    (hPool_Send2 : ∀ i j, (L : ℝ) + 2 * ((parts j).card : ℝ) * η ≤ (d - η) * ((d - η) * (Res i).card)) :
    ∃ z : ℕ → Fin N,
      (∀ i < L, z i ∈ Res (w i)) ∧
      (∀ i₁ < L, ∀ i₂ < L, i₁ ≠ i₂ → z i₁ ≠ z i₂) ∧
      (∀ i (hi : i + 1 < L),
        if 0 < len i then (d - η) * ((Body (w' i)).card : ℝ) < ((G.neighborFinset (z i) ∩ Body (w' i)).card : ℝ)
        else if i + 1 < L - 1 then (d - η) * ((Res (w' i)).card : ℝ) < ((G.neighborFinset (z i) ∩ Res (w' i)).card : ℝ)
        else (d - η) * ((G.neighborFinset (z 0) ∩ Res (w (L - 1))).card : ℝ) <
          ((G.neighborFinset (z i) ∩ (G.neighborFinset (z 0) ∩ Res (w (L - 1)))).card : ℝ)) ∧
      (∀ i (hi : 0 < i) (hiL : i < L),
        if 0 < len (i - 1) then (d - η) * ((Cap (w (i - 1))).card : ℝ) < ((G.neighborFinset (z i) ∩ Cap (w (i - 1))).card : ℝ)
        else G.Adj (z (i - 1)) (z i)) ∧
      G.Adj (z (L - 1)) (z 0) := by
  classical
  let S_end : Fin N → Finset (Fin N) := fun z0 => G.neighborFinset z0 ∩ Res (w (L - 1))
  let TargetNext : Fin N → (i : ℕ) → i + 1 < L → Finset (Fin N) := fun z0 i _ =>
    if 0 < len i then Body (w' i)
    else if i + 1 < L - 1 then Res (w' i)
    else S_end z0
  have hT_sub : ∀ z0 i (hi : i + 1 < L), TargetNext z0 i hi ⊆ parts (w' i) := by
    intro z0 i hi
    simp only [TargetNext]
    split_ifs with h1 h2
    · exact hBody_sub _
    · exact hRes_sub _
    · have heq : w (L - 1) = w' i := by
        have hL1 : i + 1 = L - 1 := by omega
        rw [← hL1, ← hw'_eq i hi]
      rw [← heq]
      exact fsISR.trans (hRes_sub _)
  have hbind : ∀ k : ℕ, 1 ≤ k → k ≤ L →
      ∃ z : ℕ → Fin N,
        (∀ i < k, z i ∈ Res (w i)) ∧
        (∀ i₁ < k, ∀ i₂ < k, i₁ ≠ i₂ → z i₁ ≠ z i₂) ∧
        (d - η) * ((Res (w (L - 1))).card : ℝ) < ((G.neighborFinset (z 0) ∩ Res (w (L - 1))).card : ℝ) ∧
        (∀ i (hi : i < k) (hi1 : i + 1 < L),
          (d - η) * ((TargetNext (z 0) i hi1).card : ℝ) <
            ((G.neighborFinset (z i) ∩ TargetNext (z 0) i hi1).card : ℝ)) ∧
        (∀ i (hi : 0 < i) (hik : i < k),
          if 0 < len (i - 1) then
            (d - η) * ((Cap (w (i - 1))).card : ℝ) < ((G.neighborFinset (z i) ∩ Cap (w (i - 1))).card : ℝ)
          else G.Adj (z (i - 1)) (z i)) ∧
        (k = L → G.Adj (z (L - 1)) (z 0)) := by
    intro k hk1 hkL
    induction k with
    | zero => omega
    | succ k ih =>
      rcases eq_or_lt_of_le hk1 with hkeq1 | hkgt1
      · have hk0 : k = 0 := by omega
        subst hk0
        have h0L : 0 + 1 < L := by omega
        let T1 := if 0 < len 0 then Body (w' 0) else Res (w' 0)
        have hT1_sub : T1 ⊆ parts (w' 0) := by
          dsimp [T1]; split_ifs <;> [exact hBody_sub _; exact hRes_sub _]
        have hT1_sz : (parts (w' 0)).card * η ≤ (T1.card : ℝ) := by
          dsimp [T1]; split_ifs <;> [exact hBody_sz _ _; exact hRes_sz _ _]
        have hR01 := hR (w 0) (w' 0) (hw_adj 0 (by omega))
        have hRL0 : R.Adj (w 0) (w (L - 1)) := by
          have := hw_adj (L - 1) (by omega)
          rw [hw_wrap] at this
          exact this.symm
        have hR0L := hR (w 0) (w (L - 1)) hRL0
        have hP0 : ((∅ : Finset (Fin N)).card : ℝ) + 2 * ((parts (w 0)).card : ℝ) * η ≤ (Res (w 0)).card := by
          simp only [Finset.card_empty, natCZ, zero_add]
          exact le_trans (by linarith) (hPool_Res (w 0))
        obtain ⟨z0, hz0_Res, _, hz0_T1, hz0_SL⟩ := exists_good_two G hη (hRes_sub (w 0))
          (hparts_pos _) hR01.1 hR01.2 (hparts_pos _) hT1_sub hT1_sz
          hR0L.1 hR0L.2 (hparts_pos _) (hRes_sub _) (hRes_sz _ _) hP0
        refine ⟨fun _ => z0, ?_, ?_, hz0_SL, ?_, ?_, ?_⟩
        · intro i hi; rw [show i = 0 by omega]; exact hz0_Res
        · intro i₁ hi₁ i₂ hi₂ hne; omega
        · intro i hi hi1
          have hi0 : i = 0 := by omega
          subst hi0
          have hT_eq : TargetNext z0 0 hi1 = T1 := by
            dsimp [TargetNext, T1]
            by_cases h0 : 0 < len 0
            · simp [h0]
            · have hLne2 : L ≠ 2 := fun h2 => h0 (hL2_len0 h2)
              have h1L : 0 + 1 < L - 1 := by omega
              simp [h0, h1L]
          simpa [hT_eq] using hz0_T1
        · intro i hi hik; omega
        · intro hL1; omega
      · obtain ⟨z, hz_Res, hz_inj, hz0_SL, hz_next, hz_prev, _⟩ := ih (by omega) (by omega)
        set avoid := (fsRange k).image z
        have havoid_card : avoid.card ≤ L :=
          (Finset.card_image_le.trans (Finset.card_range k).le).trans (by omega)
        have hSend_sz : (parts (w (L - 1))).card * η ≤ ((S_end (z 0)).card : ℝ) :=
          (hPool_Send (w (L - 1)) (w (L - 1))).1.trans hz0_SL.le
        have hT_sz : ∀ i (hi : i + 1 < L), (parts (w' i)).card * η ≤ ((TargetNext (z 0) i hi).card : ℝ) := by
          intro i hi
          dsimp [TargetNext]
          split_ifs with h1 h2
          · exact hBody_sz _ _
          · exact hRes_sz _ _
          · have heq : w (L - 1) = w' i := by
              have hL1 : i + 1 = L - 1 := by omega
              rw [← hL1, ← hw'_eq i hi]
            rw [← heq]
            exact hSend_sz
        have hk_w : w' (k - 1) = w k := by
          simpa [show k - 1 + 1 = k by omega] using hw'_eq (k - 1) (by omega)
        have hR_prev : R.Adj (w k) (w (k - 1)) := by
          have := hw_adj (k - 1) (by omega)
          rw [hk_w] at this
          exact this.symm
        have hR_prev_p := hR (w k) (w (k - 1)) hR_prev
        have hSend_sub_wk : S_end (z 0) ⊆ parts (w (L - 1)) := fsISR.trans (hRes_sub _)
        have hpick : ∃ zk : Fin N,
            zk ∈ Res (w k) ∧ zk ∉ avoid ∧
            (if 0 < len (k - 1) then
              (d - η) * ((Cap (w (k - 1))).card : ℝ) < ((G.neighborFinset zk ∩ Cap (w (k - 1))).card : ℝ)
            else G.Adj (z (k - 1)) zk) ∧
            (∀ hk1L : k + 1 < L,
              (d - η) * ((TargetNext (z 0) k hk1L).card : ℝ) <
                ((G.neighborFinset zk ∩ TargetNext (z 0) k hk1L).card : ℝ)) ∧
            (k = L - 1 → G.Adj zk (z 0)) := by
          by_cases hlen_prev : 0 < len (k - 1)
          · by_cases hk1L : k + 1 < L
            · have hR_next := hR (w k) (w' k) (hw_adj k hkL)
              have hP : (avoid.card : ℝ) + 2 * ((parts (w k)).card : ℝ) * η ≤ (Res (w k)).card := by
                have hav : (avoid.card : ℝ) ≤ (L : ℝ) := natCL.mpr havoid_card
                linarith only [hav, hPool_Res (w k)]
              obtain ⟨zk, hzkP, hzk_av, hzk_cap, hzk_next⟩ := exists_good_two G hη (hRes_sub (w k))
                (hparts_pos _) hR_prev_p.1 hR_prev_p.2 (hparts_pos _) (hCap_sub _) (hCap_sz _ _)
                hR_next.1 hR_next.2 (hparts_pos _) (hT_sub (z 0) k hk1L) (hT_sz k hk1L) hP
              refine ⟨zk, hzkP, hzk_av, by simp [hlen_prev, hzk_cap], fun _ => hzk_next, fun h => by omega⟩
            · have hk_eq : k = L - 1 := by omega
              have hP_sub : S_end (z 0) ⊆ parts (w k) := by rw [hk_eq]; exact hSend_sub_wk
              have hP : (avoid.card : ℝ) + 2 * ((parts (w k)).card : ℝ) * η ≤ ((S_end (z 0)).card : ℝ) := by
                have hav : (avoid.card : ℝ) ≤ (L : ℝ) := natCL.mpr havoid_card
                have hps := (hPool_Send (w (L - 1)) (w k)).2
                rw [hk_eq] at hps ⊢
                linarith only [hav, hps, hz0_SL]
              obtain ⟨zk, hzkP, hzk_av, hzk_cap, _⟩ := exists_good_two G hη hP_sub
                (hparts_pos _) hR_prev_p.1 hR_prev_p.2 (hparts_pos _) (hCap_sub _) (hCap_sz _ _)
                hR_prev_p.1 hR_prev_p.2 (hparts_pos _) (hCap_sub _) (hCap_sz _ _) hP
              have hzk_Res : zk ∈ Res (w k) := by rw [hk_eq]; exact (fsMI3.mp hzkP).2
              have hzk_z0 : G.Adj zk (z 0) :=
                ((G.mem_neighborFinset (z 0) zk).mp (fsMI3.mp hzkP).1).symm
              exact ⟨zk, hzk_Res, hzk_av, by simp [hlen_prev, hzk_cap], fun h => (hk1L h).elim, fun _ => hzk_z0⟩
          · have hk_prev_lt : k - 1 + 1 < L := by omega
            have hz_prev_deg := hz_next (k - 1) (by omega) hk_prev_lt
            by_cases hk1L : k + 1 < L
            · have hk_lt_L1 : k - 1 + 1 < L - 1 := by omega
              have hT_eq : TargetNext (z 0) (k - 1) hk_prev_lt = Res (w k) := by
                simp only [TargetNext, hlen_prev, ↓reduceIte, hk_lt_L1, hk_w]
              rw [hT_eq] at hz_prev_deg
              set P := G.neighborFinset (z (k - 1)) ∩ Res (w k)
              have hP_sub : P ⊆ parts (w k) := fsISR.trans (hRes_sub _)
              have hP : (avoid.card : ℝ) + 2 * ((parts (w k)).card : ℝ) * η ≤ (P.card : ℝ) := by
                have hav : (avoid.card : ℝ) ≤ (L : ℝ) := natCL.mpr havoid_card
                have hps := (hPool_Send (w k) (w k)).2
                linarith only [hav, hps, hz_prev_deg]
              have hR_next := hR (w k) (w' k) (hw_adj k hkL)
              obtain ⟨zk, hzkP, hzk_av, hzk_next, _⟩ := exists_good_two G hη hP_sub
                (hparts_pos _) hR_next.1 hR_next.2 (hparts_pos _) (hT_sub (z 0) k hk1L) (hT_sz k hk1L)
                hR_next.1 hR_next.2 (hparts_pos _) (hT_sub (z 0) k hk1L) (hT_sz k hk1L) hP
              have hzk_Res : zk ∈ Res (w k) := (fsMI3.mp hzkP).2
              have hzk_adj : G.Adj (z (k - 1)) zk := (G.mem_neighborFinset (z (k - 1)) zk).mp (fsMI3.mp hzkP).1
              exact ⟨zk, hzk_Res, hzk_av, by simp [hlen_prev, hzk_adj], fun _ => hzk_next, fun h => by omega⟩
            · have hk_eq : k = L - 1 := by omega
              have hk_lt_L1 : ¬ (k - 1 + 1 < L - 1) := by omega
              have hT_eq : TargetNext (z 0) (k - 1) hk_prev_lt = S_end (z 0) := by
                simp only [TargetNext, hlen_prev, ↓reduceIte, hk_lt_L1]
              rw [hT_eq] at hz_prev_deg
              set P := G.neighborFinset (z (k - 1)) ∩ S_end (z 0)
              have hP_pos : avoid.card < P.card := by
                have h1 : (avoid.card : ℝ) ≤ (L : ℝ) := natCL.mpr havoid_card
                have h2 : (L : ℝ) < (d - η) * ((d - η) * ((Res (w (L - 1))).card : ℝ)) := by
                  have hnn := hPool_Send2 (w (L - 1)) (w k)
                  have hp : (0 : ℝ) < 2 * ((parts (w k)).card : ℝ) * η := by
                    have := hparts_pos (w k)
                    positivity
                  linarith only [hnn, hp]
                have h3 : (d - η) * ((d - η) * ((Res (w (L - 1))).card : ℝ)) <
                    (d - η) * ((S_end (z 0)).card : ℝ) := by
                  have hdn : 0 < d - η := by
                    have hps1 := (hPool_Send (w (L - 1)) (w (L - 1))).1
                    have hpos1 : (0 : ℝ) < (parts (w (L - 1))).card * η := by
                      have := hparts_pos (w (L - 1)); positivity
                    have hpos2 : (0 : ℝ) ≤ (Res (w (L - 1))).card := natCN _
                    nlinarith only [hps1, hpos1, hpos2]
                  exact mul_lt_mul_of_pos_left hz0_SL hdn
                exact_mod_cast (h1.trans_lt (h2.trans h3)).trans hz_prev_deg
              have hrem : (P \ avoid).Nonempty := fsCP.mp (by
                have : P.card ≤ (P \ avoid).card + avoid.card := by
                  calc P.card ≤ ((P \ avoid) ∪ avoid).card := fsCLC (fun x hx => by
                        by_cases h : x ∈ avoid
                        · exact fsMUR _ h
                        · exact fsMUL _ (fsMS.mpr ⟨hx, h⟩))
                    _ ≤ (P \ avoid).card + avoid.card := fsCUL _ _
                omega)
              obtain ⟨zk, hzk⟩ := hrem
              rw [fsMS] at hzk
              have hzk_mem := fsMI3.mp hzk.1
              have hzk_Send := fsMI3.mp hzk_mem.2
              have hzk_Res : zk ∈ Res (w k) := by rw [hk_eq]; exact hzk_Send.2
              have hzk_adj : G.Adj (z (k - 1)) zk := (G.mem_neighborFinset (z (k - 1)) zk).mp hzk_mem.1
              have hzk_z0 : G.Adj zk (z 0) := ((G.mem_neighborFinset (z 0) zk).mp hzk_Send.1).symm
              exact ⟨zk, hzk_Res, hzk.2, by simp [hlen_prev, hzk_adj], fun h => (hk1L h).elim, fun _ => hzk_z0⟩
        obtain ⟨zk, hzk_Res, hzk_av, hzk_prev, hzk_next, hzk_wrap⟩ := hpick
        let z' : ℕ → Fin N := fun i => if i = k then zk else z i
        have hz'0 : z' 0 = z 0 := if_neg (by omega : (0 : ℕ) ≠ k)
        refine ⟨z', ?_, ?_, ?_, ?_, ?_, ?_⟩
        · intro i hi
          by_cases hik : i = k
          · subst hik; dsimp only [z']; rw [if_pos rfl]; exact hzk_Res
          · dsimp only [z']; rw [if_neg hik]; exact hz_Res i (by omega)
        · intro i₁ hi₁ i₂ hi₂ hne
          by_cases h1 : i₁ = k <;> by_cases h2 : i₂ = k
          · exact (hne (h1.trans h2.symm)).elim
          · subst h1; dsimp only [z']; rw [if_pos rfl, if_neg h2]
            intro heq
            exact hzk_av (fsMI.mpr ⟨i₂, fsMR.mpr (by omega), heq.symm⟩)
          · subst h2; dsimp only [z']; rw [if_neg h1, if_pos rfl]
            intro heq
            exact hzk_av (fsMI.mpr ⟨i₁, fsMR.mpr (by omega), heq⟩)
          · dsimp only [z']; rw [if_neg h1, if_neg h2]
            exact hz_inj i₁ (by omega) i₂ (by omega) hne
        · rw [hz'0]; exact hz0_SL
        · intro i hi hi1
          rw [hz'0]
          by_cases hik : i = k
          · subst hik
            have hzk1 : z' i = zk := by dsimp [z']; exact if_pos rfl
            rw [hzk1]; exact hzk_next hi1
          · have hzi : z' i = z i := by dsimp [z']; exact if_neg hik
            rw [hzi]; exact hz_next i (by omega) hi1
        · intro i hi hik
          by_cases hkeq : i = k
          · subst hkeq
            have hzk1 : z' i = zk := by dsimp [z']; exact if_pos rfl
            have hzm1 : z' (i - 1) = z (i - 1) := by dsimp [z']; exact if_neg (by omega : i - 1 ≠ i)
            rw [hzk1, hzm1]; exact hzk_prev
          · have him1 : i - 1 ≠ k := by omega
            have hzi : z' i = z i := by dsimp [z']; exact if_neg hkeq
            have hzm : z' (i - 1) = z (i - 1) := by dsimp [z']; exact if_neg him1
            rw [hzi, hzm]; exact hz_prev i hi (by omega)
        · intro hkL1
          have hk_eq : k = L - 1 := by omega
          subst hk_eq
          rw [hz'0]
          simp only [z', if_pos rfl]; exact hzk_wrap rfl
  obtain ⟨z, hz_Res, hz_inj, hz0_SL, hz_next, hz_prev, hz_wrap⟩ := hbind L (by omega) le_rfl
  refine ⟨z, hz_Res, hz_inj, ?_, hz_prev, hz_wrap rfl⟩
  intro i hi
  have h := hz_next i (by omega) hi
  dsimp [TargetNext, S_end] at h
  split_ifs at h ⊢ <;> exact h

end H2Proof

set_option maxHeartbeats 800000 in
theorem h2_proof : OMA.Erdos556R1.H2 := by
  intro d δ hd hδ0 hδ1
  let d' : ℝ := min d 1
  have hd' : 0 < d' := lt_min hd zero_lt_one
  have hd'1 : d' ≤ 1 := min_le_right d 1
  have hd'd : d' ≤ d := min_le_left d 1
  let η : ℝ := min (d' / 4) (min (δ / 16) (d' ^ 2 * δ / 256))
  have hη : 0 < η := lt_min (by positivity) (lt_min (by positivity) (by positivity))
  have hη_d' : η ≤ d' / 4 := min_le_left _ _
  have hη_δ : η ≤ δ / 16 := (min_le_right _ _).trans (min_le_left _ _)
  have hη_sq : η ≤ d' ^ 2 * δ / 256 := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨η, hη, fun t => ?_⟩
  let m₀ : ℕ := Nat.ceil (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) + 32
  refine ⟨m₀, fun N n m k G _ parts R M heven hn4 hk1 hm hm₀ hdisj hparts hR hM hMcard hMreach => ?_⟩
  classical
  have hm32 : 32 ≤ m := le_trans (by omega : 32 ≤ m₀) hm
  have hm_pos : 0 < m := by omega
  have hm_real_pos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm_pos
  have hparts_pos : ∀ i : Fin t, 0 < (parts i).card := fun i =>
    lt_of_lt_of_le hm_pos (hparts i).1
  have hS_card : 2 * k ≤ M.verts.toFinset.card := by
    rwa [← Set.ncard_eq_toFinset_card']
  obtain ⟨edges, hedges_len, hedges_adj, _, hedges_nodup⟩ :=
    H2Proof.extract_matching_pairs M hM k M.verts.toFinset
      (fun x hx => stMT.mp hx)
      (fun x hx y hxy => stMT.mpr (M.edge_vert hxy.symm))
      hS_card
  have hR_has_edge : ∃ u v : Fin t, R.Adj u v := by
    have hne : edges ≠ [] := by intro h; simp [h] at hedges_len; omega
    obtain ⟨⟨u, v⟩, rest, h⟩ := List.exists_cons_of_ne_nil hne
    exact ⟨u, v, M.adj_sub (hedges_adj (u, v) (by simp [h]))⟩
  have hd1 : d ≤ 1 := by
    obtain ⟨u, v, huv⟩ := hR_has_edge
    have h1 := (hR u v huv).2
    have h2 : (G.edgeDensity (parts u) (parts v) : ℝ) ≤ 1 := by
      exact_mod_cast SimpleGraph.edgeDensity_le_one G (parts u) (parts v)
    linarith
  have hd_gt : η < d := by linarith
  have hd_sub_ge : 3 / 4 * d' ≤ d - η := by linarith
  have hη_d1 : η ≤ d' / 256 := by
    have h1 : d' ^ 2 * δ / 256 ≤ d' * 1 / 256 := by nlinarith
    linarith
  have hη_δd : η ≤ d' * δ / 256 := by
    have h1 : d' ^ 2 * δ / 256 ≤ d' * δ / 256 := by nlinarith
    linarith
  have h1mδ : 0 < 1 - δ := sub_pos.mpr hδ1
  have hm_t_den : (t : ℝ) / (1 - δ) ≤ (m : ℝ) := by
    have h1 : (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) ≤ (m₀ : ℝ) := by
      calc _ ≤ (Nat.ceil (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) : ℝ) :=
            natLC _
        _ ≤ (m₀ : ℝ) := by simp only [m₀, natCA, natCO]; linarith
    have h2 : (0 : ℝ) ≤ 256 * (t : ℝ) / (d' ^ 2 * δ) := by positivity
    have h3 : (0 : ℝ) ≤ 32 / δ := by positivity
    have h4 : (0 : ℝ) ≤ 32 / (d' * δ) := by positivity
    have h5 : (m₀ : ℝ) ≤ (m : ℝ) := natCL.mpr hm
    linarith
  have hm_t_sq : 256 * (t : ℝ) / (d' ^ 2 * δ) ≤ (m : ℝ) := by
    have h1 : (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) ≤ (m₀ : ℝ) := by
      calc _ ≤ (Nat.ceil (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) : ℝ) :=
            natLC _
        _ ≤ (m₀ : ℝ) := by simp only [m₀, natCA, natCO]; linarith
    have h2 : (0 : ℝ) ≤ (t : ℝ) / (1 - δ) := by positivity
    have h3 : (0 : ℝ) ≤ 32 / δ := by positivity
    have h4 : (0 : ℝ) ≤ 32 / (d' * δ) := by positivity
    have h5 : (m₀ : ℝ) ≤ (m : ℝ) := natCL.mpr hm
    linarith
  have hm_δ : 32 / δ ≤ (m : ℝ) := by
    have h1 : (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) ≤ (m₀ : ℝ) := by
      calc _ ≤ (Nat.ceil (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) : ℝ) :=
            natLC _
        _ ≤ (m₀ : ℝ) := by simp only [m₀, natCA, natCO]; linarith
    have h2 : (0 : ℝ) ≤ 256 * (t : ℝ) / (d' ^ 2 * δ) := by positivity
    have h3 : (0 : ℝ) ≤ (t : ℝ) / (1 - δ) := by positivity
    have h4 : (0 : ℝ) ≤ 32 / (d' * δ) := by positivity
    have h5 : (m₀ : ℝ) ≤ (m : ℝ) := natCL.mpr hm
    linarith
  have hm_dδ : 32 / (d' * δ) ≤ (m : ℝ) := by
    have h1 : (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) ≤ (m₀ : ℝ) := by
      calc _ ≤ (Nat.ceil (256 * (t : ℝ) / (d' ^ 2 * δ) + (t : ℝ) / (1 - δ) + 32 / δ + 32 / (d' * δ)) : ℝ) :=
            natLC _
        _ ≤ (m₀ : ℝ) := by simp only [m₀, natCA, natCO]; linarith
    have h2 : (0 : ℝ) ≤ 256 * (t : ℝ) / (d' ^ 2 * δ) := by positivity
    have h3 : (0 : ℝ) ≤ (t : ℝ) / (1 - δ) := by positivity
    have h4 : (0 : ℝ) ≤ 32 / δ := by positivity
    have h5 : (m₀ : ℝ) ≤ (m : ℝ) := natCL.mpr hm
    linarith
  have hchoose_r : ∃ r : ℕ, 1 ≤ r ∧ r ≤ k ∧ (n : ℝ) ≤ (1 - δ) * (2 * (r : ℝ) * (m : ℝ)) ∧
      (2 ≤ r → (1 - δ) * (2 * ((r - 1 : ℕ) : ℝ) * (m : ℝ)) < (n : ℝ)) := by
    let S : Finset ℕ := (Finset.Icc (1 : ℕ) k).filter (fun j => (n : ℝ) ≤ (1 - δ) * (2 * (j : ℝ) * (m : ℝ)))
    have hkS : k ∈ S := fsMF.mpr ⟨Finset.mem_Icc.mpr ⟨hk1, le_rfl⟩, hm₀⟩
    have hSne : S.Nonempty := ⟨k, hkS⟩
    let r := S.min' hSne
    have hrS : r ∈ S := Finset.min'_mem S hSne
    have hr_mem := fsMF.mp hrS
    have hr_icc := Finset.mem_Icc.mp hr_mem.1
    refine ⟨r, hr_icc.1, hr_icc.2, hr_mem.2, fun hr2 => ?_⟩
    by_contra! hle
    have hr1_mem : r - 1 ∈ S := fsMF.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, hle⟩
    have := Finset.min'_le S (r - 1) hr1_mem
    omega
  obtain ⟨r, hr1, hrk, hnr, hnr_min⟩ := hchoose_r
  set chosen := edges.take r
  have hchosen_len : chosen.length = r := by rw [lsLT, hedges_len]; exact min_eq_left hrk
  have hchosen_ne : chosen ≠ [] := lsNNOLP (by omega)
  have hchosen_adj : ∀ p ∈ chosen, R.Adj p.1 p.2 := fun p hp =>
    M.adj_sub (hedges_adj p (lsMOMT2 hp))
  have hchosen_nodup : (chosen.flatMap (fun p => [p.1, p.2])).Nodup := by
    have h1 : chosen.flatMap (fun p => [p.1, p.2]) <+: edges.flatMap (fun p => [p.1, p.2]) :=
      (List.take_prefix r edges).flatMap (fun p => [p.1, p.2])
    exact hedges_nodup.sublist h1.sublist
  have hchosen_reach : ∀ p ∈ chosen, ∀ q ∈ chosen, R.Reachable p.1 q.1 := fun p hp q hq =>
    hMreach p.1 (M.edge_vert (hedges_adj p (lsMOMT2 hp)))
      q.1 (M.edge_vert (hedges_adj q (lsMOMT2 hq)))
  obtain ⟨W, hWne, hWadj, hWchain, hWwrap, hWlastf, hWeven, hW2, hW2t, hr_le_W2, hW1_eq, hWcnt, hWnodup⟩ :=
    H2Proof.build_closed_walk chosen hchosen_ne hchosen_adj hchosen_nodup hchosen_reach
  rw [hchosen_len] at hr_le_W2 hW1_eq hWcnt
  set L := W.length
  have hL_le_n : L ≤ n := by
    rcases eq_or_lt_of_le hr1 with rfl | hr2
    · have : L = 2 := hW1_eq rfl
      omega
    · have hgt := hnr_min hr2
      have h2m : 2 * (1 - δ) * (m : ℝ) < (n : ℝ) := by
        have h1 : (1 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ r - 1)
        nlinarith
      have ht_le : (t : ℝ) ≤ (1 - δ) * (m : ℝ) := by linarith [(div_le_iff₀ h1mδ).mp hm_t_den]
      have hLt : (L : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast hW2t
      have hLn_real : (L : ℝ) < (n : ℝ) := by linarith
      exact_mod_cast hLn_real.le
  obtain ⟨n_half, hn_half⟩ := heven
  obtain ⟨L_half, hL_half⟩ := hWeven
  set D := n_half - L_half
  have hn_eq : n = L + 2 * D := by omega
  set B := Nat.floor ((1 - δ) * (m : ℝ))
  have hD_le : D ≤ r * B := by
    have hB_gt : (1 - δ) * (m : ℝ) < (B : ℝ) + 1 := Nat.lt_floor_add_one _
    have h1 : (D : ℝ) + (r : ℝ) ≤ (n_half : ℝ) := by
      have : L_half ≥ r := by omega
      exact_mod_cast (by omega : D + r ≤ n_half)
    have h2 : (n_half : ℝ) ≤ (1 - δ) * (r : ℝ) * (m : ℝ) := by
      have h2n : (n : ℝ) = 2 * (n_half : ℝ) := by exact_mod_cast (by omega : n = 2 * n_half)
      linarith
    have h3 : (1 - δ) * (r : ℝ) * (m : ℝ) < (r : ℝ) * ((B : ℝ) + 1) := by
      have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
      nlinarith
    have h4 : (D : ℝ) < (r : ℝ) * (B : ℝ) := by linarith
    have h4n : D < r * B := by exact_mod_cast h4
    exact h4n.le
  set lens := H2Proof.assignList B W D
  obtain ⟨hlens_len, hlens_sum, hlens_leB, hlens_zero⟩ := H2Proof.assignList_props B W D (hWcnt ▸ hD_le)
  have hlens_L : lens.length = L := hlens_len
  let len : ℕ → ℕ := fun i => if h : i < L then lens[i]'(hlens_len ▸ h) else 0
  have hlen_L : len (L - 1) = 0 := by
    simp only [len, dif_pos (by omega : L - 1 < L)]
    refine hlens_zero (L - 1) (by omega) ?_
    have h1 := hWlastf hWne
    rwa [lsGEG hWne] at h1
  have hL2_len0 : L = 2 → 0 < len 0 := by
    intro hL2
    have hlen1_0 : len 1 = 0 := by simpa [hL2] using hlen_L
    have hL_half1 : L_half = 1 := by omega
    have hD_pos : 0 < D := by omega
    have hsum0 : len 0 + len 1 = D := by
      have hsum_rng := H2Proof.sum_range_eq_list_sum lens len (fun i hi => by
        have hiL : i < L := hlens_L ▸ hi
        simp [len, hiL])
      rw [hlens_L, hL2, hlens_sum] at hsum_rng
      simpa [Finset.sum_range_succ] using hsum_rng
    omega
  set q := Nat.ceil (δ / 8 * (m : ℝ))
  have hq_ge : δ / 8 * (m : ℝ) ≤ (q : ℝ) := natLC _
  have hq_lt : (q : ℝ) < δ / 8 * (m : ℝ) + 1 := Nat.ceil_lt_add_one (by positivity)
  have h2q_le : 2 * q ≤ m := by
    have h1 : (2 * q : ℝ) < δ / 4 * (m : ℝ) + 2 := by linarith only [hq_lt]
    have h2 : δ / 4 * (m : ℝ) + 2 ≤ 1 / 4 * (m : ℝ) + 2 := by nlinarith only [hδ1, hm_real_pos]
    have h3 : (1 / 4 * (m : ℝ) + 2 : ℝ) ≤ (m : ℝ) := by
      have : (32 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm32
      linarith only [this]
    exact_mod_cast (h1.trans_le (h2.trans h3)).le
  have hsplit_all : ∀ i : Fin t, ∃ Res Cap Body : Finset (Fin N),
      Res ⊆ parts i ∧ Cap ⊆ parts i ∧ Body ⊆ parts i ∧
      Disjoint Res Cap ∧ Disjoint Res Body ∧ Disjoint Cap Body ∧
      Res.card = q ∧ Cap.card = q ∧ Body.card = (parts i).card - 2 * q :=
    fun i => H2Proof.split_cluster (parts i) q (h2q_le.trans (hparts i).1)
  choose Res Cap Body hRes_sub hCap_sub hBody_sub hRC hRB hCB hRes_card hCap_card hBody_card using hsplit_all
  set c := Nat.ceil ((m + 1 : ℝ) * η)
  have hc_ge : (m + 1 : ℝ) * η ≤ (c : ℝ) := natLC _
  have hc_lt : (c : ℝ) < (m + 1 : ℝ) * η + 1 := Nat.ceil_lt_add_one (by positivity)
  have hm1_2m : (m + 1 : ℝ) ≤ 2 * (m : ℝ) := by
    have : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm_pos
    linarith only [this]
  have hparts_le : ∀ i : Fin t, ((parts i).card : ℝ) ≤ (m : ℝ) + 1 := fun i => by
    exact_mod_cast (hparts i).2
  have hc_parts : ∀ i : Fin t, ((parts i).card : ℝ) * η ≤ (c : ℝ) := fun i =>
    (mul_le_mul_of_nonneg_right (hparts_le i) hη.le).trans hc_ge
  have h_m1η_q : (m + 1 : ℝ) * η ≤ (q : ℝ) := by
    have h1 : (m + 1 : ℝ) * η ≤ 2 * (m : ℝ) * (δ / 16) := mul_le_mul hm1_2m hη_δ hη.le (by positivity)
    linarith only [h1, hq_ge]
  have hRes_sz : ∀ i j : Fin t, ((parts j).card : ℝ) * η ≤ ((Res i).card : ℝ) := fun i j => by
    rw [hRes_card i]
    exact (mul_le_mul_of_nonneg_right (hparts_le j) hη.le).trans h_m1η_q
  have hCap_sz : ∀ i j : Fin t, ((parts j).card : ℝ) * η ≤ ((Cap i).card : ℝ) := fun i j => by
    rw [hCap_card i]
    exact (mul_le_mul_of_nonneg_right (hparts_le j) hη.le).trans h_m1η_q
  have hBody_ge : ∀ i : Fin t, (m : ℝ) / 2 ≤ ((Body i).card : ℝ) := fun i => by
    have hb1 : m - 2 * q ≤ (Body i).card := by rw [hBody_card i]; exact natSLSR (hparts i).1 _
    have hb2 : (m : ℝ) - 2 * (q : ℝ) ≤ ((Body i).card : ℝ) := by
      have : ((m - 2 * q : ℕ) : ℝ) = (m : ℝ) - 2 * (q : ℝ) := by
        rw [Nat.cast_sub h2q_le]; push_cast; rfl
      rw [← this]; exact_mod_cast hb1
    have h2q : 2 * (q : ℝ) ≤ δ / 4 * (m : ℝ) + 2 := by linarith only [hq_lt]
    have h32 : (32 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm32
    nlinarith only [hb2, h2q, h32, hδ1, hδ0]
  have hBody_sz : ∀ i j : Fin t, ((parts j).card : ℝ) * η ≤ ((Body i).card : ℝ) := fun i j => by
    have h1 : ((parts j).card : ℝ) * η ≤ 2 * (m : ℝ) * (δ / 16) :=
      mul_le_mul ((hparts_le j).trans hm1_2m) hη_δ hη.le (by positivity)
    have h2 : 2 * (m : ℝ) * (δ / 16) ≤ (m : ℝ) / 2 := by nlinarith only [hδ1, hm_real_pos]
    exact h1.trans (h2.trans (hBody_ge i))
  have hBody_pool : ∀ i j₁ j₂ : Fin t,
      3 * ((max (parts j₁).card (parts j₂).card : ℝ) * η + 1) ≤ (d - η) * ((Body i).card : ℝ) := by
    intro i j₁ j₂
    have hmax : (max (parts j₁).card (parts j₂).card : ℝ) ≤ (m : ℝ) + 1 := by
      exact_mod_cast max_le (hparts j₁).2 (hparts j₂).2
    have h1 : 3 * ((max (parts j₁).card (parts j₂).card : ℝ) * η + 1) ≤ 3 * (2 * (m : ℝ) * (d' / 256) + 1) := by
      have : (max (parts j₁).card (parts j₂).card : ℝ) * η ≤ 2 * (m : ℝ) * (d' / 256) :=
        mul_le_mul (hmax.trans hm1_2m) hη_d1 hη.le (by positivity)
      linarith only [this]
    have h2 : (32 : ℝ) ≤ d' * (m : ℝ) := by
      have hdm := (div_le_iff₀ (by positivity : 0 < d' * δ)).mp hm_dδ
      have hle : d' * δ * (m : ℝ) ≤ d' * (m : ℝ) :=
        mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hd'.le hδ1.le) hm_real_pos.le
      linarith only [hdm, hle, show (m : ℝ) * (d' * δ) = d' * δ * (m : ℝ) by ring]
    have h3 : 3 * (2 * (m : ℝ) * (d' / 256) + 1) ≤ 3 / 8 * (d' * (m : ℝ)) := by
      have heq : 3 * (2 * (m : ℝ) * (d' / 256) + 1) = 3 / 128 * (d' * (m : ℝ)) + 3 := by ring
      rw [heq]
      linarith only [h2]
    have h4 : 3 / 8 * (d' * (m : ℝ)) ≤ (d - η) * ((Body i).card : ℝ) := by
      have hb := hBody_ge i
      nlinarith only [hb, hd_sub_ge, hd', hm_real_pos]
    exact h1.trans (h3.trans h4)
  have hc_Body : ∀ i : Fin t, (c : ℝ) ≤ (d - η) * ((Body i).card : ℝ) := fun i => by
    have h1 : (c : ℝ) ≤ 3 * ((max (parts i).card (parts i).card : ℝ) * η + 1) := by
      have hm_le : (m : ℝ) ≤ (parts i).card := by exact_mod_cast (hparts i).1
      have h2m : (m + 1 : ℝ) * η ≤ 2 * ((parts i).card : ℝ) * η := by
        nlinarith only [hm1_2m, hm_le, hη]
      simp only [max_self]
      linarith only [hc_lt, h2m]
    exact h1.trans (hBody_pool i i i)
  have hd'2 : d' ^ 2 ≤ 1 := by rw [sq]; exact mul_le_one₀ hd'1 hd'.le hd'1
  have hSend_big : ∀ i j : Fin t, ((parts j).card : ℝ) * η ≤ (d - η) * ((Cap i).card : ℝ) := by
    intro i j
    rw [hCap_card i]
    have h1 : ((parts j).card : ℝ) * η ≤ 2 * (m : ℝ) * (d' * δ / 256) :=
      mul_le_mul ((hparts_le j).trans hm1_2m) hη_δd hη.le (by positivity)
    have h2 : 2 * (m : ℝ) * (d' * δ / 256) ≤ (3 / 4 * d') * (δ / 8 * (m : ℝ)) := by
      have hdm0 : 0 ≤ d' * δ * (m : ℝ) := by positivity
      linarith only [hdm0, show 2 * (m : ℝ) * (d' * δ / 256) = (1 / 128) * (d' * δ * (m : ℝ)) by ring,
        show (3 / 4 * d') * (δ / 8 * (m : ℝ)) = (3 / 32) * (d' * δ * (m : ℝ)) by ring]
    have h3 : (3 / 4 * d') * (δ / 8 * (m : ℝ)) ≤ (d - η) * (q : ℝ) :=
      mul_le_mul hd_sub_ge hq_ge (by positivity) (by linarith only [hd_sub_ge, hd'])
    exact h1.trans (h2.trans h3)
  have hPool_Res : ∀ i : Fin t, (L : ℝ) + 2 * ((parts i).card : ℝ) * η ≤ ((Res i).card : ℝ) := by
    intro i
    rw [hRes_card i]
    have hL2t : (L : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast hW2t
    have ht_bnd : 2 * (t : ℝ) ≤ d' ^ 2 * δ * (m : ℝ) / 128 := by
      have h1 := (div_le_iff₀ (by positivity : 0 < d' ^ 2 * δ)).mp hm_t_sq
      linarith only [h1, show (m : ℝ) * (d' ^ 2 * δ) = d' ^ 2 * δ * (m : ℝ) by ring]
    have h2η' : 2 * ((parts i).card : ℝ) * η ≤ d' ^ 2 * δ * (m : ℝ) / 64 := by
      have hle := (hparts_le i).trans hm1_2m
      have h1 := mul_le_mul hle hη_sq hη.le (by positivity)
      linarith only [h1, show 2 * (m : ℝ) * (d' ^ 2 * δ / 256) = d' ^ 2 * δ * (m : ℝ) / 128 by ring]
    have h3' : d' ^ 2 * δ * (m : ℝ) / 128 + d' ^ 2 * δ * (m : ℝ) / 64 ≤ δ / 8 * (m : ℝ) := by
      have hδm0 : 0 ≤ δ * (m : ℝ) := by positivity
      have hsq : d' ^ 2 * (δ * (m : ℝ)) ≤ 1 * (δ * (m : ℝ)) := mul_le_mul_of_nonneg_right hd'2 hδm0
      linarith only [hsq, hδm0, show d' ^ 2 * δ * (m : ℝ) = d' ^ 2 * (δ * (m : ℝ)) by ring]
    linarith only [hL2t, ht_bnd, h2η', h3', hq_ge]
  have hPool_Send : ∀ i j : Fin t, ((parts j).card : ℝ) * η ≤ (d - η) * ((Res i).card : ℝ) ∧
      (L : ℝ) + 2 * ((parts j).card : ℝ) * η ≤ (d - η) * ((Res i).card : ℝ) := by
    intro i j
    rw [hRes_card i]
    have hL2t : (L : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast hW2t
    have ht_bnd : 2 * (t : ℝ) ≤ d' ^ 2 * δ * (m : ℝ) / 128 := by
      have h1 := (div_le_iff₀ (by positivity : 0 < d' ^ 2 * δ)).mp hm_t_sq
      linarith only [h1, show (m : ℝ) * (d' ^ 2 * δ) = d' ^ 2 * δ * (m : ℝ) by ring]
    have h2η : 2 * ((parts j).card : ℝ) * η ≤ d' ^ 2 * δ * (m : ℝ) / 64 := by
      have hle := (hparts_le j).trans hm1_2m
      have h1 := mul_le_mul hle hη_sq hη.le (by positivity)
      linarith only [h1, show 2 * (m : ℝ) * (d' ^ 2 * δ / 256) = d' ^ 2 * δ * (m : ℝ) / 128 by ring]
    have h1η : ((parts j).card : ℝ) * η ≤ d' ^ 2 * δ * (m : ℝ) / 128 := by
      have hle := (hparts_le j).trans hm1_2m
      have h1 := mul_le_mul hle hη_sq hη.le (by positivity)
      linarith only [h1, show 2 * (m : ℝ) * (d' ^ 2 * δ / 256) = d' ^ 2 * δ * (m : ℝ) / 128 by ring]
    have hRHS : (3 / 4 * d') * (δ / 8 * (m : ℝ)) ≤ (d - η) * (q : ℝ) :=
      mul_le_mul hd_sub_ge hq_ge (by positivity) (by linarith only [hd_sub_ge, hd'])
    have hdm_bnd : d' ^ 2 * δ * (m : ℝ) ≤ d' * δ * (m : ℝ) := by
      have hδm0 : 0 ≤ δ * (m : ℝ) := by positivity
      have hsq : d' ^ 2 ≤ d' := by rw [sq]; exact mul_le_of_le_one_left hd'.le hd'1
      have h1 := mul_le_mul_of_nonneg_right hsq hδm0
      linarith only [h1, show d' ^ 2 * (δ * (m : ℝ)) = d' ^ 2 * δ * (m : ℝ) by ring,
        show d' * (δ * (m : ℝ)) = d' * δ * (m : ℝ) by ring]
    have hdm0 : 0 ≤ d' * δ * (m : ℝ) := by positivity
    have hA : d' ^ 2 * δ * (m : ℝ) / 128 + d' ^ 2 * δ * (m : ℝ) / 64 ≤
        (3 / 4 * d') * (δ / 8 * (m : ℝ)) := by
      linarith only [hdm_bnd, hdm0, show (3 / 4 * d') * (δ / 8 * (m : ℝ)) = 3 / 32 * (d' * δ * (m : ℝ)) by ring]
    have hB : d' ^ 2 * δ * (m : ℝ) / 128 ≤ (3 / 4 * d') * (δ / 8 * (m : ℝ)) := by
      linarith only [hdm_bnd, hdm0, show (3 / 4 * d') * (δ / 8 * (m : ℝ)) = 3 / 32 * (d' * δ * (m : ℝ)) by ring]
    exact ⟨h1η.trans (hB.trans hRHS), by linarith only [hL2t, ht_bnd, h2η, hA, hRHS]⟩
  have hPool_Send2 : ∀ i j : Fin t,
      (L : ℝ) + 2 * ((parts j).card : ℝ) * η ≤ (d - η) * ((d - η) * ((Res i).card : ℝ)) := by
    intro i j
    rw [hRes_card i]
    have hL2t : (L : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast hW2t
    have ht_bnd : 2 * (t : ℝ) ≤ d' ^ 2 * δ * (m : ℝ) / 128 := by
      have h1 := (div_le_iff₀ (by positivity : 0 < d' ^ 2 * δ)).mp hm_t_sq
      linarith only [h1, show (m : ℝ) * (d' ^ 2 * δ) = d' ^ 2 * δ * (m : ℝ) by ring]
    have h2η : 2 * ((parts j).card : ℝ) * η ≤ d' ^ 2 * δ * (m : ℝ) / 64 := by
      have hle := (hparts_le j).trans hm1_2m
      have h1 := mul_le_mul hle hη_sq hη.le (by positivity)
      linarith only [h1, show 2 * (m : ℝ) * (d' ^ 2 * δ / 256) = d' ^ 2 * δ * (m : ℝ) / 128 by ring]
    have hRHS : (3 / 4 * d') * ((3 / 4 * d') * (δ / 8 * (m : ℝ))) ≤ (d - η) * ((d - η) * (q : ℝ)) := by
      have hq' : (3 / 4 * d') * (δ / 8 * (m : ℝ)) ≤ (d - η) * (q : ℝ) :=
        mul_le_mul hd_sub_ge hq_ge (by positivity) (by linarith only [hd_sub_ge, hd'])
      exact mul_le_mul hd_sub_ge hq' (by positivity) (by linarith only [hd_sub_ge, hd'])
    have hA : d' ^ 2 * δ * (m : ℝ) / 128 + d' ^ 2 * δ * (m : ℝ) / 64 ≤
        (3 / 4 * d') * ((3 / 4 * d') * (δ / 8 * (m : ℝ))) := by
      have hpos : 0 ≤ d' ^ 2 * δ * (m : ℝ) := by positivity
      linarith only [hpos, show (3 / 4 * d') * ((3 / 4 * d') * (δ / 8 * (m : ℝ))) = 9 / 128 * (d' ^ 2 * δ * (m : ℝ)) by ring]
    linarith only [hL2t, ht_bnd, h2η, hA, hRHS]
  let w : ℕ → Fin t := fun i => if h : i < L then W[i].1 else (W.head hWne).1
  let w' : ℕ → Fin t := fun i => if h : i < L then W[i].2.1 else (W.head hWne).1
  have hw_adj : ∀ i (hi : i < L), R.Adj (w i) (w' i) := fun i hi => by
    simp only [w, w', dif_pos hi]
    exact hWadj W[i] (lsGM hi)
  have hw'_eq : ∀ i (hi : i + 1 < L), w' i = w (i + 1) := fun i hi => by
    simp only [w', w, dif_pos (by omega : i < L), dif_pos hi]
    exact lsIIG.mp hWchain i hi
  have hw_wrap : w' (L - 1) = w 0 := by
    simp only [w', w, dif_pos (by omega : L - 1 < L), dif_pos (by omega : 0 < L)]
    have h1 := hWwrap hWne
    rwa [lsGEG hWne, lsHEG hWne] at h1
  obtain ⟨z, hz_Res, hz_inj, hz_next, hz_prev, hz_wrap⟩ :=
    H2Proof.embed_tour_vertices G hη parts R hparts_pos hR Res Cap Body
      hRes_sub hCap_sub hBody_sub hRes_sz hCap_sz hBody_sz
      L w w' hw_adj hw'_eq hw_wrap len hlen_L hW2 hL2_len0 hPool_Res hPool_Send hPool_Send2
  have hℓ_bound : ∀ i (hi : i < L), len i ≤ min ((Body (w' i)).card - c) (Body (w i)).card - 2 * c := by
    intro i hi
    have hleB : len i ≤ B := by
      simp only [len, dif_pos hi]
      exact hlens_leB i hi
    have hB_real : (B : ℝ) ≤ (1 - δ) * (m : ℝ) := Nat.floor_le (by positivity)
    have hc_ub : (c : ℝ) < 2 * (m : ℝ) * (δ / 16) + 1 := by
      have : (m + 1 : ℝ) * η ≤ 2 * (m : ℝ) * (δ / 16) := mul_le_mul hm1_2m hη_δ hη.le (by positivity)
      linarith only [this, hc_lt]
    have hq_ub : (q : ℝ) < δ / 8 * (m : ℝ) + 1 := hq_lt
    have hBU : (m : ℝ) - 2 * (q : ℝ) ≤ ((Body (w i)).card : ℝ) := by
      have hb1 : m - 2 * q ≤ (Body (w i)).card := by
        rw [hBody_card (w i)]; exact natSLSR (hparts (w i)).1 _
      have hb2 : ((m - 2 * q : ℕ) : ℝ) = (m : ℝ) - 2 * (q : ℝ) := by
        rw [Nat.cast_sub h2q_le]; push_cast; rfl
      rw [← hb2]; exact_mod_cast hb1
    have hBV : (m : ℝ) - 2 * (q : ℝ) ≤ ((Body (w' i)).card : ℝ) := by
      have hb1 : m - 2 * q ≤ (Body (w' i)).card := by
        rw [hBody_card (w' i)]; exact natSLSR (hparts (w' i)).1 _
      have hb2 : ((m - 2 * q : ℕ) : ℝ) = (m : ℝ) - 2 * (q : ℝ) := by
        rw [Nat.cast_sub h2q_le]; push_cast; rfl
      rw [← hb2]; exact_mod_cast hb1
    have h32 : (32 : ℝ) ≤ δ * (m : ℝ) := by
      have := (div_le_iff₀ hδ0).mp hm_δ
      linarith only [this]
    have h1 : (len i : ℝ) ≤ (1 - δ) * (m : ℝ) := (natCL.mpr hleB).trans hB_real
    have h2 : (1 - δ) * (m : ℝ) ≤ ((Body (w' i)).card : ℝ) - 3 * (c : ℝ) := by
      nlinarith only [hBV, hc_ub, hq_ub, h32, hδ0, hδ1, hm_real_pos]
    have h3 : (1 - δ) * (m : ℝ) ≤ ((Body (w i)).card : ℝ) - 3 * (c : ℝ) := by
      nlinarith only [hBU, hc_ub, hq_ub, h32, hδ0, hδ1, hm_real_pos]
    have hn1 : len i ≤ (Body (w' i)).card - 3 * c := by
      have : (len i : ℝ) + 3 * (c : ℝ) ≤ ((Body (w' i)).card : ℝ) := by linarith only [h1, h2]
      have : len i + 3 * c ≤ (Body (w' i)).card := by exact_mod_cast this
      omega
    have hn2 : len i ≤ (Body (w i)).card - 3 * c := by
      have : (len i : ℝ) + 3 * (c : ℝ) ≤ ((Body (w i)).card : ℝ) := by linarith only [h1, h3]
      have : len i + 3 * c ≤ (Body (w i)).card := by exact_mod_cast this
      omega
    omega
  have hseg_exists : ∀ i : ℕ, i < L →
      ∃ seg : List (Fin N),
        seg ≠ [] ∧
        seg.length = 2 * len i + 1 ∧
        (∀ h : seg ≠ [], seg.head h = z i) ∧
        (∀ h : seg ≠ [], G.Adj (seg.getLast h) (z ((i + 1) % L))) ∧
        seg.Nodup ∧
        seg.IsChain G.Adj ∧
        (0 < len i → seg.toFinset ⊆ insert (z i) (Body (w i) ∪ Body (w' i) ∪ Cap (w i))) ∧
        (len i = 0 → seg = [z i]) := by
    intro i hi
    by_cases hli : 0 < len i
    · have hi1 : i + 1 < L := by
        by_contra! hge
        have : i = L - 1 := by omega
        subst this
        omega
      have hmod : (i + 1) % L = i + 1 := natMEOL hi1
      have hzu_deg := hz_next i hi1
      simp only [hli, ↓reduceIte] at hzu_deg
      have hzv_deg := hz_prev (i + 1) (by omega) hi1
      simp only [show i + 1 - 1 = i by omega, hli, ↓reduceIte] at hzv_deg
      have hR_uv := hR (w i) (w' i) (hw_adj i hi)
      obtain ⟨seg, hne, hlen_s, hhead_s, hlast_s, hnodup_s, hchain_s, hsub_s⟩ :=
        H2Proof.bridge_segment G hη hd_gt (hRes_sub (w i)) (hCap_sub (w i)) (hBody_sub (w i)) (hBody_sub (w' i))
          (hdisj (R.ne_of_adj (hw_adj i hi))) (hRC (w i)) (hRB (w i)) (hCB (w i))
          hR_uv.1 hR_uv.2 (hparts_pos (w i)) (hparts_pos (w' i)) c
          (hc_parts (w i)) (hc_parts (w' i))
          (hc_Body (w i)) (hCap_sz (w i) (w i)) (hBody_sz (w i) (w i)) (hBody_sz (w' i) (w' i))
          (hz_Res i hi) hzu_deg hzv_deg (hSend_big (w i) (w i)) (hBody_pool (w' i) (w i) (w' i))
          (len i) hli (hℓ_bound i hi)
      refine ⟨seg, hne, hlen_s, hhead_s, ?_, hnodup_s, hchain_s, fun _ => hsub_s, fun h => by omega⟩
      rw [hmod]
      exact hlast_s
    · have hli0 : len i = 0 := by omega
      refine ⟨[z i], by simp, by simp [hli0], fun _ => rfl, ?_, List.nodup_singleton _, List.isChain_singleton _, fun h => by omega, fun _ => rfl⟩
      intro _
      simp only [List.getLast_singleton]
      by_cases hi1 : i + 1 < L
      · have hmod : (i + 1) % L = i + 1 := natMEOL hi1
        rw [hmod]
        have hp := hz_prev (i + 1) (by omega) hi1
        simpa [show i + 1 - 1 = i by omega, hli0] using hp
      · have hieq : i = L - 1 := by omega
        subst hieq
        have hmod : (L - 1 + 1) % L = 0 := by rw [show L - 1 + 1 = L by omega, Nat.mod_self]
        rw [hmod]
        exact hz_wrap
  let segs : ℕ → List (Fin N) := fun i =>
    if h : i < L then (hseg_exists i h).choose else []
  have hsegs_spec : ∀ i (hi : i < L),
      segs i ≠ [] ∧
      (segs i).length = 2 * len i + 1 ∧
      (∀ h : segs i ≠ [], (segs i).head h = z i) ∧
      (∀ h : segs i ≠ [], G.Adj ((segs i).getLast h) (z ((i + 1) % L))) ∧
      (segs i).Nodup ∧
      (segs i).IsChain G.Adj ∧
      (0 < len i → (segs i).toFinset ⊆ insert (z i) (Body (w i) ∪ Body (w' i) ∪ Cap (w i))) ∧
      (len i = 0 → segs i = [z i]) := by
    intro i hi
    simp only [segs, dif_pos hi]
    exact (hseg_exists i hi).choose_spec
  have hlen_true : ∀ i (hi : i < L), 0 < len i → W[i].2.2 = true := by
    intro i hi hpos
    by_contra hfalse
    have hf : W[i].2.2 = false := Bool.eq_false_iff.mpr hfalse
    have hz := hlens_zero i hi hf
    simp only [len, dif_pos hi] at hpos
    rw [hz] at hpos
    omega
  have hW_disj_true : ∀ i₁ < L, ∀ i₂ < L, i₁ ≠ i₂ → 0 < len i₁ → 0 < len i₂ →
      Disjoint ({w i₁, w' i₁} : Finset (Fin t)) ({w i₂, w' i₂} : Finset (Fin t)) := by
    intro i₁ hi₁ i₂ hi₂ hne hpos₁ hpos₂
    have ht1 := hlen_true i₁ hi₁ hpos₁
    have ht2 := hlen_true i₂ hi₂ hpos₂
    simp only [w, w', dif_pos hi₁, dif_pos hi₂]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · exact H2Proof.true_indices_disjoint W hWnodup i₁ i₂ hi₁ hi₂ hlt ht1 ht2
    · exact (H2Proof.true_indices_disjoint W hWnodup i₂ i₁ hi₂ hi₁ hlt ht2 ht1).symm
  have hz_not_BBC : ∀ i₁ < L, ∀ i₂ < L,
      z i₁ ∉ Body (w i₂) ∪ Body (w' i₂) ∪ Cap (w i₂) := by
    intro i₁ hi₁ i₂ hi₂ hmem
    have hz1 : z i₁ ∈ Res (w i₁) := hz_Res i₁ hi₁
    have hzR := hRes_sub (w i₁) hz1
    simp only [fsMU] at hmem
    rcases hmem with (hB1 | hB2) | hC
    · by_cases heq : w i₁ = w i₂
      · rw [heq] at hz1
        exact fsDL.mp (hRB (w i₂)) hz1 hB1
      · exact fsDL.mp (hdisj heq) hzR (hBody_sub _ hB1)
    · by_cases heq : w i₁ = w' i₂
      · rw [heq] at hz1
        exact fsDL.mp (hRB (w' i₂)) hz1 hB2
      · exact fsDL.mp (hdisj heq) hzR (hBody_sub _ hB2)
    · by_cases heq : w i₁ = w i₂
      · rw [heq] at hz1
        exact fsDL.mp (hRC (w i₂)) hz1 hC
      · exact fsDL.mp (hdisj heq) hzR (hCap_sub _ hC)
  have hdisj_segs : ∀ i₁ < L, ∀ i₂ < L, i₁ ≠ i₂ →
      Disjoint (segs i₁).toFinset (segs i₂).toFinset := by
    intro i₁ hi₁ i₂ hi₂ hne
    rw [fsDL]
    intro x hx₁ hx₂
    by_cases h1 : 0 < len i₁ <;> by_cases h2 : 0 < len i₂
    · have hs1 := (hsegs_spec i₁ hi₁).2.2.2.2.2.2.1 h1 hx₁
      have hs2 := (hsegs_spec i₂ hi₂).2.2.2.2.2.2.1 h2 hx₂
      rcases fsMI2.mp hs1 with rfl | hx1' <;>
        rcases fsMI2.mp hs2 with hzx | hx2'
      · exact hz_inj i₁ hi₁ i₂ hi₂ hne hzx
      · exact hz_not_BBC i₁ hi₁ i₂ hi₂ hx2'
      · exact hz_not_BBC i₂ hi₂ i₁ hi₁ (hzx ▸ hx1')
      · have hd := hW_disj_true i₁ hi₁ i₂ hi₂ hne h1 h2
        have hx_in₁ : ∃ u ∈ ({w i₁, w' i₁} : Finset (Fin t)), x ∈ parts u := by
          simp only [fsMU] at hx1'
          rcases hx1' with (h | h) | h
          · exact ⟨w i₁, by simp, hBody_sub _ h⟩
          · exact ⟨w' i₁, by simp, hBody_sub _ h⟩
          · exact ⟨w i₁, by simp, hCap_sub _ h⟩
        have hx_in₂ : ∃ v ∈ ({w i₂, w' i₂} : Finset (Fin t)), x ∈ parts v := by
          simp only [fsMU] at hx2'
          rcases hx2' with (h | h) | h
          · exact ⟨w i₂, by simp, hBody_sub _ h⟩
          · exact ⟨w' i₂, by simp, hBody_sub _ h⟩
          · exact ⟨w i₂, by simp, hCap_sub _ h⟩
        obtain ⟨u, hu, hxu⟩ := hx_in₁
        obtain ⟨v, hv, hxv⟩ := hx_in₂
        have huv : u ≠ v := fun h => fsDL.mp hd hu (h ▸ hv)
        exact fsDL.mp (hdisj huv) hxu hxv
    · have hl2 : len i₂ = 0 := by omega
      have hs1 := (hsegs_spec i₁ hi₁).2.2.2.2.2.2.1 h1 hx₁
      have hs2 := (hsegs_spec i₂ hi₂).2.2.2.2.2.2.2 hl2
      rw [hs2] at hx₂
      simp only [lsTC, lsTN, fsMI2,
        fsNE, or_false] at hx₂
      subst hx₂
      rcases fsMI2.mp hs1 with hzx | hx1'
      · exact hz_inj i₂ hi₂ i₁ hi₁ hne.symm hzx
      · exact hz_not_BBC i₂ hi₂ i₁ hi₁ hx1'
    · have hl1 : len i₁ = 0 := by omega
      have hs1 := (hsegs_spec i₁ hi₁).2.2.2.2.2.2.2 hl1
      have hs2 := (hsegs_spec i₂ hi₂).2.2.2.2.2.2.1 h2 hx₂
      rw [hs1] at hx₁
      simp only [lsTC, lsTN, fsMI2,
        fsNE, or_false] at hx₁
      subst hx₁
      rcases fsMI2.mp hs2 with hzx | hx2'
      · exact hz_inj i₁ hi₁ i₂ hi₂ hne hzx
      · exact hz_not_BBC i₁ hi₁ i₂ hi₂ hx2'
    · have hl1 : len i₁ = 0 := by omega
      have hl2 : len i₂ = 0 := by omega
      rw [lsMT, (hsegs_spec i₁ hi₁).2.2.2.2.2.2.2 hl1, lsMS] at hx₁
      rw [lsMT, (hsegs_spec i₂ hi₂).2.2.2.2.2.2.2 hl2, lsMS] at hx₂
      exact hz_inj i₁ hi₁ i₂ hi₂ hne (hx₁.symm.trans hx₂)
  have hsum_segs : ∑ i ∈ fsRange L, (segs i).length = n := by
    have h1 : ∑ i ∈ fsRange L, (segs i).length = ∑ i ∈ fsRange L, (2 * len i + 1) :=
      fsSC rfl fun i hi => (hsegs_spec i (fsMR.mp hi)).2.1
    rw [h1, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
      ← fsMS3]
    have h2 : ∑ i ∈ fsRange L, len i = D := by
      have h3 : ∑ i ∈ fsRange L, len i = lens.sum := by
        rw [← hlens_L]
        exact H2Proof.sum_range_eq_list_sum lens len (fun i hi => by
          have hiL : i < L := hlens_L ▸ hi
          simp [len, hiL])
      exact h3.trans hlens_sum
    omega
  exact H2Proof.assemble_cycle G hn4 (by omega) z segs
    (fun i hi => (hsegs_spec i hi).1)
    (fun i hi => (hsegs_spec i hi).2.2.1)
    (fun i hi => (hsegs_spec i hi).2.2.2.2.1)
    (fun i hi => (hsegs_spec i hi).2.2.2.2.2.1)
    (fun i hi => (hsegs_spec i hi).2.2.2.1)
    hdisj_segs
    hsum_segs
end H2Section

theorem LuczakEvenBound : type_of% @Erdos556.erdos_556.variants.luczak_asymptotic_even :=
  OMA.Erdos556R1.main h1_proof h2_proof
namespace OMA556
open SimpleGraph
theorem aq {V:Type*} (c:Erdos556.q4 V) :
    (⊤ : SimpleGraph V).IsEdgeColouring c.graph:=by
  constructor
  · ext u v
    rw [top_adj,iSup_adj]
    constructor
    · intro huv
      exact ⟨c.colour u v,huv,rfl⟩
    · rintro ⟨i,hi⟩
      exact hi.1
  · intro i j hij
    apply disjoint_iff_inf_le.mpr
    intro u v h
    exact (hij (h.1.2.symm.trans h.2.2)).elim
theorem ap {V:Type*} (c:Fin 3 → SimpleGraph V)
    (hc: (⊤ : SimpleGraph V).IsEdgeColouring c) :
    ∃ d :Erdos556.q4 V,∀ i,d.graph i =c i:=by
  classical
  have exists_colour (u v :V) (huv:u ≠ v) : ∃ i,(c i).Adj u v:=by
    apply iSup_adj.mp
    rw [← hc.1]
    exact (top_adj _ _).mpr huv
  have unique_colour {u v :V} {i j :Fin 3}
      (hi: (c i).Adj u v) (hj: (c j).Adj u v) : i=j:=by
    by_contra hij
    exact (disjoint_iff_inf_le.mp (hc.2 i j hij)) ⟨hi,hj⟩
  let col (u v :V) : Fin 3 :=
    if h :u=v then 0 else Classical.choose (exists_colour u v h)
  have chosen {u v :V} (h:u ≠ v) : (c (col u v)).Adj u v:=by
    dsimp only [col]
    rw [dif_neg h]
    exact clCS (exists_colour u v h)
  have symm (u v :V) : col u v=col v u:=by
    by_cases huv:u=v
    · subst v;rfl
    · exact unique_colour (chosen huv) (chosen (Ne.symm huv)).symm
  let d :Erdos556.q4 V := ⟨col,symm⟩
  refine ⟨d,?_⟩
  intro i
  ext u v
  change (u ≠ v ∧ col u v=i) ↔ (c i).Adj u v
  constructor
  · rintro ⟨huv,hi⟩
    simpa only [hi] using chosen huv
  · intro hi
    exact ⟨hi.ne,unique_colour (chosen hi.ne) hi⟩
theorem aM (n:ℕ) :
    multicolourRamsey (cycleGraph n) 3 =Erdos556.sS n :=by
  unfold multicolourRamsey Erdos556.sS
  congr 1
  ext m
  constructor
  · intro h c
    exact h c.graph (aq c)
  · intro h c hc
    obtain ⟨d,hd⟩ :=ap c hc
    obtain ⟨i,hi⟩ :=h d
    rw [hd] at hi
    exact ⟨i,hi⟩
open Erdos556 Filter
theorem oddAsymptotic (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, Odd n →
      (multicolourRamsey (cycleGraph n) 3 : ℝ) ≤ (4+ε)*n := by
  classical
  let t := min ε 1
  have ht : 0 < t := lt_min hε zero_lt_one
  obtain ⟨δ, hδ, hbound⟩ := asymptotic_mass_bound (t/2) (by positivity)
  obtain ⟨e, he, _, k, hk⟩ := vy δ hδ
  obtain ⟨j, hj⟩ := wZ e he
  obtain ⟨l, hl⟩ := exists_nat_gt (2/t)
  filter_upwards [eventually_ge_atTop k, eventually_ge_atTop j,
    eventually_ge_atTop l] with n hnk hnj hnl
  intro ho
  let m := ⌊(4+t)*(n:ℝ)⌋₊
  have hn : 0 ≤ (n:ℝ) := by positivity
  have htn : 2 < t*(n:ℝ) := by
    have hln : (l:ℝ) ≤ n := by exact_mod_cast hnl
    have hh := (div_lt_iff₀ ht).mp (hl.trans_le hln)
    linarith
  have hnpos : 0 < (n:ℝ) := by by_contra! h; have := mul_nonpos_of_nonneg_of_nonpos ht.le h; linarith
  have hm : (m:ℝ) ≤ (4+t)*n := Nat.floor_le (by positivity)
  have hM : (4+t)*n < (m:ℝ)+1 := Nat.lt_floor_add_one _
  have hgap : (4+t/2)*n < (m:ℝ) := by nlinarith
  have hmn : n ≤ m := by
    have hh : (n:ℝ) ≤ m := by nlinarith
    exact_mod_cast hh
  have hm7 : m ≤ 7*n := by
    have hh := mul_le_mul_of_nonneg_right (min_le_right ε (1:ℝ)) hn
    change t*n ≤ 1*n at hh
    have hh' : (m:ℝ) ≤ 7*n := by nlinarith
    exact_mod_cast hh'
  have hr : rr n m := by
    intro c
    by_contra hbad
    have hno : ∀ i, ¬ cycleGraph n ⊑ c.graph i := fun i hi => hbad ⟨i, hi⟩
    have hc : ftCard (Fin m) ≤ 7*n := by simpa using hm7
    obtain ⟨d⟩ := hj c n hnj ho (by simpa using hmn) hc hno
    have hb := hbound _ (hk c n hnk hc hno d)
    rw [d.aH, ftCF] at hb
    exact (not_lt_of_ge ((div_le_iff₀ hnpos).mp hb)) hgap
  rw [aM]
  have hu : sS n ≤ m := csInf_le (OrderBot.bddBelow _) hr
  exact (show (sS n : ℝ) ≤ m by exact_mod_cast hu).trans
    (hm.trans (mul_le_mul_of_nonneg_right (add_le_add_right (min_le_left ε 1) 4) hn))
end OMA556

theorem OMA.solution : type_of% @Erdos556.erdos_556.variants.luczak_asymptotic := by
  intro ε hε
  filter_upwards [OMA556.oddAsymptotic ε hε, LuczakEvenBound 1 zero_lt_one] with n ho he
  rcases Nat.even_or_odd n with hn | hn
  · have h := he hn
    linarith [mul_nonneg hε.le (natCN (α := ℝ) n)]
  · exact ho hn
