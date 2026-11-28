import OMAReductions.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R3
import Mathlib

/-!
# Unbalanced EC3 absorption: the exact R1.H3 statement

Credit: @fqlx for the three graph lemmas, the H3 correction, and integration.
This reuses the conditional reduction proposed by @tgg6956g2z-bot in PR14987.
Its original H3 omits the necessary hypothesis `12 * Q.card ≤ A.card`.
Here that hypothesis is added and proved at the reduction's call site from
`Q ⊆ M` and the existing bound `12 * M.card ≤ A''.card`.

The dense-join proof reuses accepted R2 helpers by @abduljaleel and accepted
R2.H2 Hall absorption by @steveDOTdigital (PR7465).
The closure development is extracted from the accepted odd-cycle proof by
@hananzlt (PR7761, commit df069abd4765cd0d5ad58f4161be516d73c3c6f5),
which reuses plby/lean-proofs commit8822f7ddef30fadbd92e1c6ab4ed897af356af5e.
The original Shuhao Song and Yury Kudryashov copyright notices are retained.
This proves the EC3 absorption input, not the full large-even-cycle theorem.
-/



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
    simpa [hx] using hα.wf.not_lt_min (Set.range g) (Set.mem_range_self z)
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
  exact { (u,v) : V × V | G.degree u +G.degree v ≥ (Fintype.card V) ∧ u ≠ v ∧ ¬G.Adj u v}
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
  simp only [edgeSet_deleteEdges,Set.mem_sdiff,Set.mem_singleton_iff]
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
        (edge_adj ..).mpr ⟨Or.inl ⟨rfl,rfl⟩,h.some_mem.2.1⟩
      exact h.some_mem.2.2 (hle hedge)
    simp only [this,false_iff]
    simpa [← Set.not_nonempty_iff_eq_empty] using h
  · simpa [← Set.not_nonempty_iff_eq_empty] using h
omit [DecidableEq V] in
open Classical in
lemma zF:qg G =G ↔
    ∀ {u} {v},u ≠ v → G.degree u +G.degree v ≥ (Fintype.card V) → G.Adj u v:=by
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
    G.degree u +G.degree v ≥ (Fintype.card V) :=by
  classical
  have ne: (rO G).Nonempty:=by
    by_contra h
    simp only [Set.nonempty_iff_ne_empty,← uY,Decidable.not_not] at h
    rw [h] at huv'
    exact huv huv'
  let w :=ne.some
  have prop₁:G.degree w.1+G.degree w.2 ≥ (Fintype.card V) :=ne.some_mem.1
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
    G.qE.degree u +G.qE.degree v ≥ (Fintype.card V) →
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
  let:=Fintype.ofFinite V
  rw [isHamiltonianCycle_iff_isCycle_and_length_eq]
  exact ⟨hp.isCycle.transfer h,by simpa using hp.length_eq⟩
omit [DecidableEq V] [Fintype V] in
private lemma IsCycle.rB (hp:p.IsCycle)
    {d e :G.Dart} (hd:d ∈ p.darts) (he:e ∈ p.darts)
    (hfst:d.fst=e.fst) : d=e:=by
  classical
  obtain ⟨i,hi,rfl⟩ :=List.getElem_of_mem hd
  obtain ⟨j,hj,rfl⟩ :=List.getElem_of_mem he
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
  obtain ⟨i,hi,rfl⟩ :=List.getElem_of_mem hd
  obtain ⟨j,hj,rfl⟩ :=List.getElem_of_mem he
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
  obtain ⟨i,hi,rfl⟩ :=List.getElem_of_mem hd
  obtain ⟨j,hj,rfl⟩ :=List.getElem_of_mem he
  have hi':i < r.support.dropLast.length:=by simpa using hi
  have hj':j < r.support.dropLast.length:=by simpa using hj
  have hget:r.support.dropLast[i]'hi'=r.support.dropLast[j]'hj':=by
    simpa [r.fst_darts_getElem hi,r.fst_darts_getElem hj] using hfst
  have hij:= (List.Nodup.getElem_inj_iff hnodup).mp hget
  subst j
  rfl
private theorem rV
    (hp:p.length=Fintype.card V) (hV:3 ≤ Fintype.card V)
    (hsupport:p.support.tail.toFinset=Finset.univ) :
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
    (List.Perm.mem_iff (support_tail_perm_support_dropLast p)).mp hb
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
  have hdi:p.darts[i] ∈ p.darts:=List.getElem_mem hiD
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
    (hV: (Fintype.card V) ≥ 3) (hp:p.support ~ Finset.univ.toList)
    (ne:v ≠ u') (vu':G.Adj v u') (v'u:G.Adj v' u)
    (d:G.Dart) (hd:d ∈ p.darts) (hd₁:d.fst=v) (hd₂:d.snd=v') :
    IsHamiltonian G :=by
  classical
  have hv:v ∈ p.support:=by simp [List.Perm.mem_iff hp]
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
      simpa only [Walk.length_append] using hwalk
    have:=calc
      p.length+1=p.support.length:=by simp
      _=Finset.univ.toList.length:=by apply List.Perm.length_eq hp
      _= (Fintype.card V) :=by simp
    have:=Walk.length_tail_add_one not_nil
    simp [q,add_assoc]
    omega
  · assumption
  · simp only [tail_support_append,support_cons,support_nil,List.tail_cons,support_copy,
      support_reverse,List.append_assoc,
      List.cons_append,List.toFinset_append,List.toFinset_cons,
      List.toFinset_nil,insert_empty_eq,Finset.union_insert,Finset.eq_univ_iff_forall,
      Finset.mem_insert,Finset.mem_union,List.mem_toFinset,Finset.mem_singleton,
      Finset.notMem_empty,false_or,q]
    intro w
    by_contra hw
    simp only [not_or] at hw
    rcases hw with ⟨hw₁,hw₂,hw₃,hw₄⟩
    have mem_tail:w ∈ p.support.tail:=by
      have mem:w ∈ p.support:=by simp [List.Perm.mem_iff hp]
      rw [← Walk.cons_tail_support] at mem
      simp only [List.mem_cons] at mem
      exact mem.resolve_left hw₄
    have not_mem_drop:w ∉ (p.dropUntil v hv).support.tail:=by
      have tail_not_nil: (p.dropUntil v hv).support.tail ≠ [] :=by
        have hpos:0 < (p.dropUntil v hv).length:=
          not_nil_iff_lt_length.mp not_nil
        apply List.ne_nil_of_length_pos
        rw [List.length_tail,length_support]
        omega
      have: (p.dropUntil v hv).support.tail.getLast tail_not_nil=u':=by
        rw [List.getLast_tail,getLast_support]
      have hw_dropLast:
          w ∉ (p.dropUntil v hv).support.tail.dropLast:=by
        simpa only [List.tail_reverse,List.mem_reverse,
          support_tail_of_not_nil _ not_nil] using hw₃
      intro hwmem
      rw [← List.dropLast_append_getLast tail_not_nil,this,
        List.mem_append,List.mem_singleton] at hwmem
      exact hwmem.elim hw_dropLast hw₁
    have append:p.support.tail=
        (p.takeUntil v hv).support.tail++ (p.dropUntil v hv).support.tail:=by
      rw [← tail_support_append,take_spec]
    simp only [append,List.mem_append] at mem_tail
    rcases mem_tail with h | h
    · exact hw₂ h
    · exact not_mem_drop h
open Classical in
private theorem xN
    {u v :V} {q:G.qg.Walk u u} (hq:q.IsHamiltonianCycle)
    (hV: (Fintype.card V) ≥ 3) (huv:G.degree u +G.degree v ≥ (Fintype.card V))
    (hv:v=hq.qk u) (not_adj: ¬G.Adj u v) :
    ∃ w w' d,G.Adj w v ∧ G.Adj w' u ∧ d ∈ q.darts ∧ d.fst=w' ∧ d.snd=w:=by
  classical
  let X := (hq.qk ·) '' {w | G.Adj u w} \ {u}
  let Y := {w | G.Adj v w} \ {hq.qk v}
  have cardX:G.degree u -1 ≤ X.toFinset.card:=calc
    _= (G.neighborFinset u).card-1:=by simp
    _= (Finset.univ.filter (G.Adj u)).card-1:=by rw [neighborFinset_eq_filter]
    _ ≤ ((Finset.univ.filter (G.Adj u)).image (hq.qk ·)).card-
        ({u} : Finset _).card:=by
      simp [Finset.card_image_of_injective _ hq.xe]
    _ ≤ (((Finset.univ.filter (G.Adj u)).image (hq.qk ·)) \ {u}).card:=by
      apply Finset.le_card_sdiff
    _=_:=by simp [X]
  have cardY:G.degree v -1 ≤ Y.toFinset.card:=calc
    _= (G.neighborFinset v).card-1:=by simp
    _ ≤ (Finset.univ.filter (G.Adj v)).card- ({hq.qk v} : Finset _).card:=by
      simp [neighborFinset_eq_filter]
    _ ≤ (Finset.univ.filter (G.Adj v) \ {hq.qk v}).card:=by
      apply Finset.le_card_sdiff
    _=_:=by simp [Y]
  have card_union: (X ∪ Y).toFinset.card ≤ (Fintype.card V) - 3:=calc
    _ ≤ ({v,hq.qk v,u}ᶜ:Finset _).card:=by
      apply Finset.card_le_card
      rw [Finset.subset_compl_comm]
      intro w hw
      simp only [Finset.mem_insert,Finset.mem_singleton,Set.toFinset_union,
        Set.toFinset_sdiff,Set.toFinset_image,Set.toFinset_ofPred,Set.toFinset_singleton,
        Finset.compl_union,Finset.mem_inter,Finset.mem_compl,Finset.mem_sdiff,
        Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,not_and,
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
      rw [Finset.card_insert_of_notMem,Finset.card_insert_of_notMem]
      · simp
      · simpa [hv] using hq.tL
      · simpa [hv] using And.intro hq.t7.symm hq.t7
  have non_empty: (X ∩ Y).toFinset.card ≠ 0:=fun h ↦ by
    suffices (Fintype.card V) - 2 ≤ (Fintype.card V) - 3 by omega
    calc
      _ ≤ (G.degree u +G.degree v) - 2:=Nat.sub_le_sub_right huv _
      _ ≤ (G.degree u -1) + (G.degree v -1) :=by omega
      _ ≤ X.toFinset.card+Y.toFinset.card:=add_le_add cardX cardY
      _= (X ∪ Y).toFinset.card+ (X ∩ Y).toFinset.card:=by
        simpa [-Set.toFinset_card] using (Finset.card_union_add_card_inter _ _).symm
      _ ≤ (Fintype.card V) - 3+0:=add_le_add card_union (le_of_eq h)
      _= (Fintype.card V) - 3:=by simp
  obtain ⟨w,hw⟩ :=Finset.card_ne_zero.mp non_empty
  simp only [Set.toFinset_inter,Set.toFinset_sdiff,Set.toFinset_image,
    Set.toFinset_ofPred,Set.toFinset_singleton,Finset.mem_inter,Finset.mem_sdiff,
    Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_singleton,
    X,Y] at hw
  rcases hw with ⟨⟨⟨w',hw'₁,hw'₂⟩,-⟩,hw₂,-⟩
  obtain ⟨d,hd₁,hd₂⟩ :=hq.qH w'
  rw [hw'₂] at hd₂
  exact ⟨w,w',d,hw₂.symm,hw'₁.symm,hd₁,hd₂⟩
theorem yp (hG:IsHamiltonian (qg G)) :
    IsHamiltonian G :=by
  classical
  by_cases trivial:Fintype.card V =1
  · exact absurd trivial
  · by_contra nonHamiltonian
    obtain ⟨a,p,hp⟩ :=hG trivial
    obtain ⟨d,hd,hd'⟩ : ∃ d ∈ p.darts,¬G.Adj d.fst d.snd:=by
      by_contra h
      simp only [not_exists,not_and,Decidable.not_not] at h
      have edgeSubset (e) (he:e ∈ p.edges) : e ∈ G.edgeSet:=by
        simp only [edges,List.mem_map] at he
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
    have perm_q':q'.support ~ Finset.univ.toList:=by
      rw [isHamiltonianCycle_iff_isCycle_and_support_count_tail_eq_one] at hq
      simp only [transfer_transfer,support_copy,support_transfer,
        List.perm_iff_count,q']
      intro a
      rw [List.count_eq_one_of_mem (Finset.nodup_toList _) (by simp)]
      simpa [support_tail_of_not_nil _ q_not_nil] using hq.2 _
    have hV: (Fintype.card V) ≥ 3:=hq.length_eq ▸ hq.isCycle.three_le_length
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
    obtain ⟨i,i_lt,hi⟩ :=List.getElem_of_mem d'_mem
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
      (List.getElem_mem i_min_1) hd''₁ hd''₂
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
private theorem wg (hV:3 ≤ Fintype.card V) :
    (⊤ : SimpleGraph V).IsHamiltonian:=by
  classical
  obtain ⟨r,hr⟩ : ∃ r,Fintype.card V =r+3:=
    ⟨Fintype.card V -3,by omega⟩
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
theorem x3 [DecidableRel G.Adj] (hV: (Fintype.card V) ≥ 3)
    (hG: ∀ u,2*G.degree u ≥ (Fintype.card V)) : G.IsHamiltonian:=by
  classical
  suffices G.qE= (⊤ : SimpleGraph V) from
    sI.mp (this ▸ wg hV)
  rw [eq_top_iff]
  intro u v ne
  simp only [top_adj,ne_eq] at ne
  apply rK G ne
  calc
    (Fintype.card V) ≤ G.degree u +G.degree v :=by
      have:=hG u
      have:=hG v
      omega
    _ ≤ G.qE.degree u +G.qE.degree v :=
      add_le_add (G.degree_le_of_le (v:=u) (rs G))
        (G.degree_le_of_le (v:=v) (rs G))
end SimpleGraph
end d0


namespace FourBlockPaths

/-- Extend a finite embedding while preserving its original initial segment. -/
theorem extend_fin_embedding {A : Type*} [Fintype A] {k l : ℕ}
    (hkl : k ≤ l) (f : Fin k ↪ A) (hsize : l ≤ Fintype.card A) :
    ∃ g : Fin l ↪ A, ∀ i : Fin k, g (Fin.castLE hkl i) = f i := by
  classical
  revert hsize
  induction l, hkl using Nat.le_induction with
  | base =>
    intro _
    exact ⟨f, fun _ => rfl⟩
  | succ n hkn ih =>
    intro hsize
    obtain ⟨g, hg⟩ := ih (by omega)
    have hnot : ¬ Function.Surjective g := by
      intro h
      have hb := Fintype.card_le_of_surjective g h
      simp only [Fintype.card_fin] at hb
      omega
    obtain ⟨x, hx⟩ : ∃ x : A, x ∉ Set.range g := by
      simpa only [Function.Surjective, Set.mem_range, not_forall, not_exists] using hnot
    refine ⟨Fin.Embedding.snoc g hx, ?_⟩
    intro i
    change Fin.Embedding.snoc g hx (Fin.castLE hkn i).castSucc = f i
    rw [Fin.Embedding.snoc_castSucc, hg]


end FourBlockPaths


/-
Cycle construction for a cyclic sequence of singleton and two-vertex path segments.
New proof for the EC3 matching-absorption step of Erdos556, developed by @fqlx.
-/

open SimpleGraph Finset

namespace MatchingSplice

theorem cycle_of_slots {V : Type*} (G : SimpleGraph V)
    {b k : ℕ} (hb : 2 ≤ b) (hk : k ≤ b)
    (x z : Fin b ↪ V) (y : Fin b → V)
    (hy : ∀ i j, i.val < k → j.val < k → y i = y j → i = j)
    (hxy : ∀ i j, j.val < k → x i ≠ y j)
    (hxz : ∀ i j, x i ≠ z j)
    (hyz : ∀ i j, i.val < k → y i ≠ z j)
    (hmatch : ∀ i, i.val < k → G.Adj (x i) (y i))
    (hsingle : ∀ i, k ≤ i.val → G.Adj (x i) (z i))
    (hdouble : ∀ i, i.val < k → G.Adj (y i) (z i))
    (hnext : ∀ i, G.Adj (z i) (x (finRotate b i))) :
    cycleGraph (2 * b + k) ⊑ G := by
  classical
  let ix (a : Fin (2*b+k)) : Fin b :=
    ⟨if a.val < 3*k then a.val / 3 else k + (a.val - 3*k) / 2, by
      have := a.isLt
      split <;> omega⟩
  let isX (a : Fin (2*b+k)) : Prop :=
    (a.val < 3*k ∧ a.val % 3 = 0) ∨
      (3*k ≤ a.val ∧ (a.val - 3*k) % 2 = 0)
  let isY (a : Fin (2*b+k)) : Prop := a.val < 3*k ∧ a.val % 3 = 1
  let f (a : Fin (2*b+k)) : V :=
    if isX a then x (ix a) else if isY a then y (ix a) else z (ix a)
  have xrep (a) (ha : isX a) :
      (a.val = 3 * (ix a).val ∧ (ix a).val < k) ∨
      (a.val = 2 * (ix a).val + k ∧ k ≤ (ix a).val) := by
    dsimp only [ix, isX] at *
    split <;> omega
  have yrep (a) (ha : isY a) :
      a.val = 3 * (ix a).val + 1 ∧ (ix a).val < k := by
    dsimp only [ix, isY] at *
    split <;> omega
  have zrep (a) (ha : ¬ isX a) (ha' : ¬ isY a) :
      (a.val = 3 * (ix a).val + 2 ∧ (ix a).val < k) ∨
      (a.val = 2 * (ix a).val + k + 1 ∧ k ≤ (ix a).val) := by
    dsimp only [ix, isX, isY] at *
    split <;> omega
  have hinj : Function.Injective f := by
    intro a c hac
    by_cases ha : isX a
    · by_cases hc : isX c
      · have he := congrArg Fin.val (x.injective (by simpa only [f, if_pos ha, if_pos hc] using hac))
        have ha' := xrep a ha
        have hc' := xrep c hc
        apply Fin.ext
        omega
      · by_cases hcy : isY c
        · exact (hxy _ _ (yrep c hcy).2 (by simpa only [f, if_pos ha, if_neg hc, if_pos hcy] using hac)).elim
        · exact (hxz _ _ (by simpa only [f, if_pos ha, if_neg hc, if_neg hcy] using hac)).elim
    · by_cases hay : isY a
      · by_cases hc : isX c
        · exact (hxy _ _ (yrep a hay).2 (by simpa only [f, if_neg ha, if_pos hay, if_pos hc] using hac.symm)).elim
        · by_cases hcy : isY c
          · have he := congrArg Fin.val (hy (ix a) (ix c) (yrep a hay).2 (yrep c hcy).2
              (by simpa only [f, if_neg ha, if_pos hay, if_neg hc, if_pos hcy] using hac))
            have ha' := yrep a hay
            have hc' := yrep c hcy
            exact Fin.ext (by omega)
          · exact (hyz _ _ (yrep a hay).2
              (by simpa only [f, if_neg ha, if_pos hay, if_neg hc, if_neg hcy] using hac)).elim
      · by_cases hc : isX c
        · exact (hxz _ _ (by simpa only [f, if_neg ha, if_neg hay, if_pos hc] using hac.symm)).elim
        · by_cases hcy : isY c
          · exact (hyz _ _ (yrep c hcy).2
              (by simpa only [f, if_neg ha, if_neg hay, if_neg hc, if_pos hcy] using hac.symm)).elim
          · have he := congrArg Fin.val (z.injective
              (by simpa only [f, if_neg ha, if_neg hay, if_neg hc, if_neg hcy] using hac))
            have ha' := zrep a ha hay
            have hc' := zrep c hc hcy
            apply Fin.ext
            omega
  have rotval (i : Fin b) : (finRotate b i).val = (i.val+1)%b := by
    rw [finRotate_apply]
    simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < b)]
  have step (a c : Fin (2*b+k)) (hstep : (c-a).val = 1) : G.Adj (f a) (f c) := by
    have haLt := a.isLt
    have hcLt := c.isLt
    have hiaLt := (ix a).isLt
    have hicLt := (ix c).isLt
    rw [Fin.val_sub] at hstep
    have hac : c.val = a.val+1 ∨ (a.val+1 = 2*b+k ∧ c.val=0) := by
      by_cases hle : a.val ≤ c.val
      · rw [show 2*b+k-a.val+c.val = (2*b+k)+(c.val-a.val) by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hstep
        exact Or.inl (by omega)
      · rw [Nat.mod_eq_of_lt (by omega)] at hstep
        exact Or.inr (by omega)
    by_cases ha : isX a
    · have har := xrep a ha
      have hc : ¬ isX c := by
        intro h
        have hcr := xrep c h
        omega
      by_cases hcy : isY c
      · have hcr := yrep c hcy
        have he : ix a = ix c := Fin.ext (by omega)
        simpa only [f, if_pos ha, if_neg hc, if_pos hcy, he] using hmatch (ix c) hcr.2
      · have hcr := zrep c hc hcy
        have he : ix a = ix c := Fin.ext (by omega)
        have hi : k ≤ (ix c).val := by omega
        simpa only [f, if_pos ha, if_neg hc, if_neg hcy, he] using hsingle (ix c) hi
    · by_cases hay : isY a
      · have har := yrep a hay
        have hc : ¬ isX c := by
          intro h
          have hcr := xrep c h
          omega
        have hcy : ¬ isY c := by
          intro h
          have hcr := yrep c h
          omega
        have hcr := zrep c hc hcy
        have he : ix a = ix c := Fin.ext (by omega)
        simpa only [f, if_neg ha, if_pos hay, if_neg hc, if_neg hcy, ← he] using hdouble (ix a) har.2
      · have har := zrep a ha hay
        have hc : isX c := by
          by_contra hn
          by_cases hyc : isY c
          · have hcr := yrep c hyc
            omega
          · have hcr := zrep c hn hyc
            omega
        have hcr := xrep c hc
        have he : finRotate b (ix a) = ix c := by
          apply Fin.ext
          rw [rotval]
          by_cases hlast : (ix a).val+1=b
          · rw [hlast, Nat.mod_self]
            omega
          · rw [Nat.mod_eq_of_lt (by omega)]
            omega
        simpa only [f, if_neg ha, if_neg hay, if_pos hc, he] using hnext (ix a)
  refine ⟨⟨⟨f, ?_⟩, hinj⟩⟩
  intro a c hac
  rcases cycleGraph_adj'.mp hac with h | h
  · exact (step c a h).symm
  · exact step a c h

end MatchingSplice


/-
# Dense bipartite cycle with a bounded exceptional set

This independently proves the exact H1 statement proposed in PR14987,
Erdos556.erdos_556.variants.benevides_skokan_large_even.R1.H3.R1.
It does not prove that reduction's H2 or H3, or the original Ramsey theorem.

Credit: @fqlx for the interface and proof of the final lemma.
The cycle embedding is copied from accepted R2 (credit: @abduljaleel).
The Hall absorption helpers are copied from accepted R2.H2
(credit: @steveDOTdigital), with their mathematics unchanged.
The H1 statement is from PR14987 (credit: @tgg6956g2z-bot).
-/

open Finset SimpleGraph
namespace EC3DenseJoinProof

theorem cycle_rotate_val {m : ℕ} (hm : 2 ≤ m) (i : Fin m) :
    (finRotate m i).val = (i.val + 1) % m := by
  haveI : NeZero m := ⟨by omega⟩
  rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (by omega : 1 < m)]

theorem cycle_of_alternating_representatives {V : Type*} (G : SimpleGraph V)
    {m : ℕ} (hm : 2 ≤ m) (U : Finset V) (x y : Fin m → V)
    (hx : Function.Injective x) (hy : Function.Injective y) (hxu : ∀ i, x i ∉ U)
    (hmem : ∀ i, y i ∈ U ∧ G.Adj (x i) (y i) ∧ G.Adj (x (finRotate m i)) (y i)) :
    (cycleGraph (2 * m)).IsContained G := by
  have hxy (i j : Fin m) : x i ≠ y j := fun h => hxu i (by simpa only [h] using (hmem j).1)
  let half (a : Fin (2 * m)) : Fin m := ⟨a.val / 2, by have := a.isLt; omega⟩
  let f (a : Fin (2 * m)) := if a.val % 2 = 0 then x (half a) else y (half a)
  have hinj : Function.Injective f := by
    intro a b hab
    by_cases ha : a.val % 2 = 0 <;> by_cases hb : b.val % 2 = 0
    · have he := congrArg Fin.val (hx (by simpa [f, ha, hb] using hab : x (half a) = x (half b)))
      dsimp [half] at he
      exact Fin.ext (by omega)
    · exact ((hxy _ _) (by simpa [f, ha, hb] using hab : x (half a) = y (half b))).elim
    · exact ((hxy _ _) (by simpa [f, ha, hb] using hab.symm : x (half b) = y (half a))).elim
    · have he := congrArg Fin.val (hy (by simpa [f, ha, hb] using hab : y (half a) = y (half b)))
      dsimp [half] at he
      exact Fin.ext (by omega)
  have step (a b : Fin (2 * m)) (hz : (b - a).val = 1) : G.Adj (f a) (f b) := by
    have hsize := a.isLt
    have hbsize := b.isLt
    rw [Fin.coe_sub] at hz
    have hab : b.val = a.val + 1 ∨ (a.val + 1 = 2 * m ∧ b.val = 0) := by
      by_cases hle : a.val ≤ b.val
      · rw [show 2 * m - a.val + b.val = 2 * m + (b.val - a.val) by omega,
          Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)] at hz
        exact Or.inl (by omega)
      · rw [Nat.mod_eq_of_lt (by omega)] at hz
        exact Or.inr (by omega)
    rcases hab with h | ⟨haLast, hbZero⟩
    · by_cases ha : a.val % 2 = 0
      · have hb : b.val % 2 ≠ 0 := by omega
        have he : half a = half b := Fin.ext (by dsimp [half]; omega)
        simpa only [f, ha, hb, if_true, if_false, ← he] using (hmem (half a)).2.1
      · have hb : b.val % 2 = 0 := by omega
        have he : finRotate m (half a) = half b := by
          apply Fin.ext
          rw [cycle_rotate_val hm]
          dsimp [half]
          rw [Nat.mod_eq_of_lt (by omega)]
          omega
        simpa only [f, ha, hb, if_true, if_false, ← he] using (hmem (half a)).2.2.symm
    · have ha : a.val % 2 ≠ 0 := by omega
      have he : finRotate m (half a) = half b := by
        apply Fin.ext
        rw [cycle_rotate_val hm]
        dsimp [half]
        simp [show a.val / 2 + 1 = m by omega, hbZero]
      have hb : b.val % 2 = 0 := by omega
      simpa only [f, ha, hb, if_true, if_false, ← he] using (hmem (half a)).2.2.symm
  let hom : cycleGraph (2 * m) →g G := ⟨f, by
    intro a b hab
    rcases cycleGraph_adj'.mp hab with h | h
    · exact (step b a h).symm
    · exact step a b h⟩
  exact ⟨⟨hom, hinj⟩⟩

private def nb {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (x : V) := U.filter (G.Adj x)

private def holes {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (x : V) := U.filter (fun y => ¬ G.Adj x y)

private def both {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (x y : V) := U.filter (fun z => G.Adj x z ∧ G.Adj y z)

private theorem part {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (x : V) : (nb G U x).card + (holes G U x).card = U.card :=
  card_filter_add_card_filter_not (G.Adj x)

private theorem common {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (U : Finset V) (a b : V) :
    (nb G U a).card ≤ (both G U a b).card + (holes G U b).card := by
  have sub : nb G U a ⊆ both G U a b ∪ holes G U b := by
    intro z hz
    obtain ⟨hu,ha⟩ := mem_filter.mp hz
    by_cases hb : G.Adj b z
    · exact mem_union_left _ (mem_filter.mpr ⟨hu,ha,hb⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hu,hb⟩)
  exact (card_le_card sub).trans (card_union_le ..)

private theorem nb_restrict {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (R U : Finset V) (h : R ⊆ U) (x : V) :
    (nb G U x).card ≤ (nb G R x).card + (U.card-R.card) := by
  have sub : nb G U x ⊆ nb G R x ∪ (U \ R) := by
    intro z hz
    obtain ⟨hu,ha⟩ := mem_filter.mp hz
    by_cases hr : z ∈ R
    · exact mem_union_left _ (mem_filter.mpr ⟨hr,ha⟩)
    · exact mem_union_right _ (mem_sdiff.mpr ⟨hu,hr⟩)
  simpa [card_sdiff_of_subset h] using (card_le_card sub).trans (card_union_le ..)

private theorem hole_mono {V : Type*} (G : SimpleGraph V) [DecidableRel G.Adj]
    {R U : Finset V} (h : R ⊆ U) (x : V) : (holes G R x).card ≤ (holes G U x).card :=
  card_le_card (filter_subset_filter _ h)

/-- Order a finite set with its exceptional entries in mutually nonconsecutive
cyclic slots. Extend the injection assigning those entries even positions. -/
private theorem separated_order {V : Type*} [DecidableEq V] {m : ℕ} (hm : 2 ≤ m)
    (S P : Finset V) (hP : P ⊆ S) (hs : S.card=m) (hp : 2*P.card ≤ m) :
    ∃ x : Fin m → V, Function.Injective x ∧ (∀ i,x i ∈ S) ∧
      ∀ i, x i ∉ P ∨ x (finRotate m i) ∉ P := by
  classical
  let e := S.equivFinOfCardEq hs
  let b (w : P) : Fin m := e ⟨w.val,hP w.property⟩
  let k := P.equivFin
  let pos (w : P) : Fin m := ⟨2*(k w).val,by have := (k w).isLt; omega⟩
  have hb : Function.Injective b := by
    intro v w eq; exact Subtype.ext (congrArg (fun z : S => z.val) (e.injective eq))
  have hpos : Function.Injective pos := by
    intro v w eq; apply k.injective; apply Fin.ext
    have eq' := congrArg Fin.val eq
    change 2*_ = 2*_ at eq'; omega
  obtain ⟨φ,hφ⟩ := Equiv.Perm.exists_extending_pair b pos hb hpos
  let x (i : Fin m) := (e.symm (φ.symm i)).val
  have ispos (i : Fin m) (hi : x i ∈ P) : i=pos ⟨x i,hi⟩ := by
    rw [←hφ]
    have he : b ⟨x i,hi⟩=φ.symm i := by
      apply e.symm.injective; apply Subtype.ext
      simp [b,x]
    rw [he,φ.apply_symm_apply]
  refine ⟨x,Subtype.val_injective.comp (e.symm.injective.comp φ.symm.injective),
    fun i => (e.symm (φ.symm i)).property,?_⟩
  intro i
  by_contra! outside
  obtain ⟨hi,hj⟩ := outside
  have ei := congrArg Fin.val (ispos i hi)
  have ej := congrArg Fin.val (ispos (finRotate m i) hj)
  rw [cycle_rotate_val hm] at ej
  change i.val=2*(k ⟨x i,hi⟩).val at ei
  change (i.val+1)%m=2*(k ⟨x (finRotate m i),hj⟩).val at ej
  have lt := (k ⟨x i,hi⟩).isLt
  rw [Nat.mod_eq_of_lt (by omega)] at ej
  omega

private theorem hall_cycle {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] {m : ℕ}
    (hm : 2 ≤ m) (R : Finset V) (x : Fin m → V) (hx : Function.Injective x)
    (out : ∀ i,x i ∉ R)
    (hall : ∀ s : Finset (Fin m), s.card ≤ (s.biUnion fun i => both G R (x i) (x (finRotate m i))).card)
    : cycleGraph (2*m) ⊑ G := by
  classical
  let t (i : Fin m) := both G R (x i) (x (finRotate m i))
  obtain ⟨y,hy,ht⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  exact cycle_of_alternating_representatives G hm R x y hx hy out (fun i => mem_filter.mp (ht i))

/-- Fill the gaps by Hall. A gap touching an exceptional center needs only
enough neighbors to cover the at most twice as many exceptional gaps. -/
private theorem absorb {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {m : ℕ} (hm : 2 ≤ m) (R S P : Finset V) (sep : Disjoint S R) (hP : P ⊆ S)
    (hs : S.card=m) (hp : 2*P.card ≤ m)
    (one : ∀ a ∈ S, ∀ b ∈ S, a ∉ P ∨ b ∉ P → 2*P.card ≤ (both G R a b).card)
    (two : ∀ a ∈ S, ∀ b ∈ S, a ∉ P → b ∉ P → m ≤ (both G R a b).card) :
    cycleGraph (2*m) ⊑ G := by
  classical
  obtain ⟨x,hx,hxS,hpos⟩ := separated_order hm S P hP hs hp
  apply hall_cycle G hm R x hx (fun i => Finset.disjoint_left.mp sep (hxS i))
  intro s
  let t (i : Fin m) := both G R (x i) (x (finRotate m i))
  change s.card ≤ (s.biUnion t).card
  rcases s.eq_empty_or_nonempty with rfl | ⟨i,hi⟩
  · simp
  have le (j : Fin m) (hj : j ∈ s) : (t j).card ≤ (s.biUnion t).card :=
    card_le_card (fun z hz => mem_biUnion.mpr ⟨j,hj,hz⟩)
  by_cases good : ∃ j ∈ s,x j ∉ P ∧ x (finRotate m j) ∉ P
  · obtain ⟨j,hj,h₁,h₂⟩ := good
    exact (show s.card ≤ m by simpa using card_le_univ s).trans
      ((two _ (hxS j) _ (hxS _) h₁ h₂).trans (le j hj))
  · let bad (g : Fin m → V) := univ.filter (fun j => g j ∈ P)
    have cardBad (g : Fin m → V) (hg : Function.Injective g) : (bad g).card ≤ P.card :=
      card_le_card_of_injOn g (fun _ h => (mem_filter.mp h).2) hg.injOn
    have sub : s ⊆ bad x ∪ bad (x ∘ finRotate m) := by
      intro j hj
      by_cases h : x j ∈ P
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,h⟩)
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _,
          by by_contra hn; exact good ⟨j,hj,h,hn⟩⟩)
    have hs' := (card_le_card sub).trans (card_union_le ..)
    have left := cardBad x hx
    have right := cardBad _ (hx.comp (finRotate m).injective)
    have low := (one _ (hxS i) _ (hxS _) (hpos i)).trans (le i hi)
    omega

/-- The exact single-colour hypothesis H1 of PR14987, unconditionally proved. -/
theorem dense_bipartite_cycle_with_exceptions
    (m d : ℕ) (G : SimpleGraph (Fin (4 * m))) [DecidableRel G.Adj]
    (A B₀ B : Finset (Fin (4 * m)))
    (hm : 2 ≤ m) (_hd : 1 ≤ d) (_hmd : 100 * d ≤ m)
    (hAB : Disjoint A B) (hB₀B : B₀ ⊆ B)
    (hA : m + 10 * d ≤ A.card) (hB : m ≤ B.card)
    (hB₀ : m ≤ B₀.card + m / 20)
    (hexcellent : ∀ x ∈ B₀, (A.filter (fun y => ¬ G.Adj x y)).card ≤ d)
    (hmoderate : ∀ x ∈ B, A.card ≤ 4 * (A.filter (G.Adj x)).card) :
    cycleGraph (2 * m) ⊑ G := by
  classical
  obtain ⟨S₀, hS₀B₀, hS₀⟩ := exists_subset_card_eq (min_le_right m B₀.card)
  obtain ⟨S, hS₀S, hSB, hS⟩ := exists_subsuperset_card_eq (hS₀B₀.trans hB₀B)
    (hS₀.trans_le (min_le_left ..)) hB
  let P := S \ S₀
  have hPS : P ⊆ S := sdiff_subset
  have hp : P.card ≤ m / 20 := by
    have h := card_sdiff_add_card_eq_card hS₀S
    change P.card + S₀.card = S.card at h
    omega
  have hsep : Disjoint S A := by
    apply Finset.disjoint_left.mpr
    intro x hxS hxA
    exact Finset.disjoint_left.mp hAB hxA (hSB hxS)
  have good (x) (hx : x ∈ S) (hxp : x ∉ P) : (holes G A x).card ≤ d := by
    have hxS₀ : x ∈ S₀ := by
      by_contra h
      exact hxp (mem_sdiff.mpr ⟨hx, h⟩)
    exact hexcellent x (hS₀B₀ hxS₀)
  have moderate (x) (hx : x ∈ S) : A.card ≤ 4 * (nb G A x).card :=
    hmoderate x (hSB hx)
  apply absorb G hm A S P hsep hPS hS (by omega)
  · intro a ha b hb hab
    rcases hab with hagood | hbgood
    · have hcomm := common G A b a
      have hnb := moderate b hb
      have hholes := good a ha hagood
      have heq : both G A b a = both G A a b := by
        ext z
        simp only [both, mem_filter, and_comm]
      rw [heq] at hcomm
      omega
    · have hcomm := common G A a b
      have hnb := moderate a ha
      have hholes := good b hb hbgood
      omega
  · intro a ha b hb hagood hbgood
    have hpart := part G A a
    have hcomm := common G A a b
    have haholes := good a ha hagood
    have hbholes := good b hb hbgood
    omega

end EC3DenseJoinProof


/-
Matching-spliced dense bipartite cycle, the exact H2 proposed in PR14987.
The matching edges are kept as two-vertex segments. Hall's theorem assigns
the opposite part to the cyclic gaps between all segments.
Credit: @fqlx. The finite-embedding extension helper is from our separately
audited FourBlockPaths work; it depends only on Mathlib.
-/

open SimpleGraph Finset

namespace EC3Matching

theorem matching_spliced_cycle {V : Type*} [DecidableEq V]
    (m d : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A B : Finset V)
    (hm : 2 ≤ m) (hd : 1 ≤ d) (hmd : 100*d ≤ m)
    (hAB : Disjoint A B)
    (hb : B.card < m) (hb' : m ≤ B.card + m/20)
    (hsize : 2*m+10*d ≤ A.card+B.card)
    (hBA : ∀ z ∈ B, (A.filter (fun a => ¬ G.Adj z a)).card ≤ d)
    (hAb : ∀ a ∈ A, (B.filter (fun z => ¬ G.Adj a z)).card ≤ d)
    (hM : ∃ u v : Fin (2*(m-B.card)) → V,
      Function.Injective u ∧ Function.Injective v ∧
      (∀ i, u i ∈ A ∧ v i ∈ A ∧ G.Adj (u i) (v i)) ∧
      (∀ i j, u i ≠ v j)) :
    cycleGraph (2*m) ⊑ G := by
  classical
  let b := B.card
  let k := 2*(m-b)
  have hb2 : 2 ≤ b := by dsimp [b]; omega
  have hk : k ≤ b := by dsimp [b,k]; omega
  have hbk : b+k ≤ A.card := by dsimp [b,k]; omega
  have hbd : 4*d ≤ b := by dsimp [b]; omega
  have htotal : 2*b+k=2*m := by dsimp [b,k]; omega
  obtain ⟨u,v,hu,hv,huv,hdisj⟩ := hM
  change Fin k → V at u v
  let f (i : Fin (2*k)) : A :=
    if h : i.val < k then ⟨u ⟨i.val,h⟩,(huv _).1⟩
    else ⟨v ⟨i.val-k,by have := i.isLt; omega⟩,(huv _).2.1⟩
  have hf : Function.Injective f := by
    intro i j he
    have he' := congrArg Subtype.val he
    dsimp only [f] at he'
    split at he' <;> split at he'
    · exact Fin.ext (congrArg (fun z : Fin k => z.val) (hu he'))
    · exact (hdisj _ _ he').elim
    · exact (hdisj _ _ he'.symm).elim
    · have h := congrArg (fun z : Fin k => z.val) (hv he')
      change i.val-k=j.val-k at h
      exact Fin.ext (by omega)
  obtain ⟨p,hp⟩ := FourBlockPaths.extend_fin_embedding
    (show 2*k ≤ b+k by omega) (⟨f,hf⟩ : Fin (2*k) ↪ A)
    (by simpa using hbk)
  have p_u (i : Fin k) : (p ⟨i.val,by have := i.isLt; omega⟩).val = u i := by
    have h := congrArg Subtype.val (hp ⟨i.val,by have := i.isLt; omega⟩)
    simpa [f, i.isLt] using h
  have p_v (i : Fin k) : (p ⟨i.val+k,by have := i.isLt; omega⟩).val = v i := by
    have h := congrArg Subtype.val (hp ⟨i.val+k,by have := i.isLt; omega⟩)
    have hlt : ¬ i.val+k < k := by omega
    simpa [f, hlt] using h
  let xi (i : Fin b) : Fin (b+k) :=
    ⟨if i.val < k then i.val else i.val+k, by have := i.isLt; split <;> omega⟩
  let yi (i : Fin b) : Fin (b+k) := ⟨i.val+k, by have := i.isLt; omega⟩
  have hxi : Function.Injective xi := by
    intro i j he
    have h := congrArg Fin.val he
    dsimp only [xi] at h
    apply Fin.ext
    split at h <;> split at h <;> omega
  have hyi : Function.Injective yi := by
    intro i j he
    have h := congrArg Fin.val he
    dsimp only [yi] at h
    exact Fin.ext (by omega)
  let x : Fin b ↪ V := ⟨fun i => (p (xi i)).val, Subtype.val_injective.comp (p.injective.comp hxi)⟩
  let y : Fin b ↪ V := ⟨fun i => (p (yi i)).val, Subtype.val_injective.comp (p.injective.comp hyi)⟩
  have hxA (i) : x i ∈ A := (p (xi i)).property
  have hyA (i) : y i ∈ A := (p (yi i)).property
  have hxy : ∀ i j : Fin b, j.val < k → x i ≠ y j := by
    intro i j hj he
    have h := congrArg Fin.val (p.injective (Subtype.ext he))
    dsimp only [xi,yi] at h
    split at h <;> omega
  have same (i : Fin b) (hi : k ≤ i.val) : x i = y i := by
    dsimp only [x,y,Function.Embedding.coeFn_mk]
    congr 2
    apply Fin.ext
    simp only [xi,yi,if_neg (by omega : ¬i.val<k)]
  have hedge (i : Fin b) (hi : i.val < k) : G.Adj (x i) (y i) := by
    have hu' : x i = u ⟨i.val,hi⟩ := by
      dsimp only [x,Function.Embedding.coeFn_mk,xi]
      simpa only [if_pos hi] using p_u ⟨i.val,hi⟩
    have hv' : y i = v ⟨i.val,hi⟩ := p_v ⟨i.val,hi⟩
    rw [hu',hv']
    exact (huv _).2.2
  let t (i : Fin b) : Finset V := B.filter
    (fun z => G.Adj (y i) z ∧ G.Adj (x (finRotate b i)) z)
  have row (i : Fin b) : b ≤ (t i).card + 2*d := by
    let L := B.filter (fun z => ¬G.Adj (y i) z)
    let R := B.filter (fun z => ¬G.Adj (x (finRotate b i)) z)
    have sub : B ⊆ t i ∪ (L ∪ R) := by
      intro z hz
      by_cases h1 : G.Adj (y i) z
      · by_cases h2 : G.Adj (x (finRotate b i)) z
        · exact mem_union_left _ (mem_filter.mpr ⟨hz,h1,h2⟩)
        · exact mem_union_right _ (mem_union_right _ (mem_filter.mpr ⟨hz,h2⟩))
      · exact mem_union_right _ (mem_union_left _ (mem_filter.mpr ⟨hz,h1⟩))
    have hL : L.card ≤ d := hAb _ (hyA i)
    have hR : R.card ≤ d := hAb _ (hxA _)
    have h := (card_le_card sub).trans (card_union_le ..)
    have h' := card_union_le L R
    dsimp [b]
    omega
  have column (z : V) (hz : z ∈ B) (w : Fin b ↪ V) (hw : ∀ i,w i ∈ A) :
      (univ.filter (fun i : Fin b => ¬G.Adj (w i) z)).card ≤ d := by
    apply (card_le_card_of_injOn w (t := A.filter (fun a => ¬G.Adj z a)) ?_ w.injective.injOn).trans (hBA z hz)
    intro i hi
    exact mem_filter.mpr ⟨hw i,fun h => (mem_filter.mp hi).2 h.symm⟩
  have hall : ∀ s : Finset (Fin b), s.card ≤ (s.biUnion t).card := by
    intro s
    rcases s.eq_empty_or_nonempty with rfl | ⟨i,hi⟩
    · simp
    by_cases hs : s.card ≤ 2*d
    · have hti : (t i).card ≤ (s.biUnion t).card := card_le_card
        (fun z hz => mem_biUnion.mpr ⟨i,hi,hz⟩)
      have hrow := row i
      omega
    · have hsub : B ⊆ s.biUnion t := by
        intro z hz
        by_contra hnot
        have h1 := column z hz y hyA
        let w : Fin b ↪ V := ⟨fun j => x (finRotate b j), x.injective.comp (finRotate b).injective⟩
        have h2 := column z hz w (fun j => hxA _)
        let L := univ.filter (fun j : Fin b => ¬G.Adj (y j) z)
        let R := univ.filter (fun j : Fin b => ¬G.Adj (x (finRotate b j)) z)
        have sub : s ⊆ L ∪ R := by
          intro j hj
          by_cases hL : G.Adj (y j) z
          · apply mem_union_right
            apply mem_filter.mpr
            refine ⟨mem_univ _,?_⟩
            intro hR
            exact hnot (mem_biUnion.mpr ⟨j,hj,mem_filter.mpr ⟨hz,hL,hR⟩⟩)
          · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _,hL⟩)
        have hc := (card_le_card sub).trans (card_union_le ..)
        change L.card ≤ d at h1
        change R.card ≤ d at h2
        omega
      exact (show s.card ≤ b by simpa using card_le_univ s).trans (card_le_card hsub)
  obtain ⟨z,hz,hzt⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' t).mp hall
  let z' : Fin b ↪ V := ⟨z,hz⟩
  have hzB (i) : z' i ∈ B := (mem_filter.mp (hzt i)).1
  have hyz (i) : G.Adj (y i) (z' i) := (mem_filter.mp (hzt i)).2.1
  have hzx (i) : G.Adj (z' i) (x (finRotate b i)) := (mem_filter.mp (hzt i)).2.2.symm
  rw [←htotal]
  apply MatchingSplice.cycle_of_slots G hb2 hk x z' y
  · intro i j _ _ hij
    exact y.injective hij
  · exact hxy
  · intro i j he
    exact Finset.disjoint_left.mp hAB (hxA i) (he ▸ hzB j)
  · intro i j _ he
    exact Finset.disjoint_left.mp hAB (hyA i) (he ▸ hzB j)
  · exact hedge
  · intro i hi
    rw [same i hi]
    exact hyz i
  · intro i _
    exact hyz i
  · exact hzx

end EC3Matching


/-
Credit: @fqlx.
An unconditional Hamiltonicity lemma for the repaired PR14987.H3 configuration.
The missing smallness invariant `12 * Q.card ≤ A.card` is essential: the H3
statement in that PR without it has an explicit counterexample.

The imported closure proof was extracted and kernel-audited from the accepted
Łuczak proof by @hananzlt; its original Bondy--Chvátal development credits
Shuhao Song. This file is a scratch lemma, not a proof of the Ramsey target.
-/

open Finset SimpleGraph
namespace EC3RepairedHamiltonian

theorem hamiltonian_repaired_core {V : Type*} [Fintype V] [DecidableEq V]
    (m d : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A Q D₀ D : Finset V)
    (hm : 2 ≤ m) (hd : 1 ≤ d) (hmd : 100 * d ≤ m)
    (hcard : Fintype.card V = 2 * m)
    (hcover : ∀ x, x ∈ A ∨ x ∈ Q ∨ x ∈ D)
    (hsum : A.card + Q.card + D.card = 2 * m)
    (hAQ : Disjoint A Q) (hAD : Disjoint A D) (hQD : Disjoint Q D)
    (hD₀D : D₀ ⊆ D) (hDsize : D.card ≤ D₀.card + 10 * d)
    (hclique : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → G.Adj x y)
    (hAsize : 9 * m ≤ 10 * A.card)
    (hQsize : 12 * Q.card ≤ A.card)
    (hTsize : m + 10 * d ≤ A.card + Q.card)
    (hQdeg : ∀ q ∈ Q, A.card ≤ 3 * (A.filter (G.Adj q)).card ∧
      (D₀.filter (fun y => ¬ G.Adj q y)).card ≤ d)
    (hD₀deg : ∀ x ∈ D₀, (Q.filter (fun y => ¬ G.Adj x y)).card ≤ d ∧
      (A.filter (fun y => ¬ G.Adj x y)).card ≤ d)
    (hDdeg : ∀ x ∈ D, A.card ≤ 4 * (A.filter (G.Adj x)).card) :
    G.IsHamiltonian := by
  classical
  let H := G.qE
  have hGH : G ≤ H := SimpleGraph.rs G
  have closed (x y : V) (hne : x ≠ y)
      (hdeg : 2 * m ≤ H.degree x + H.degree y) : H.Adj x y :=
    SimpleGraph.rK G hne (by simpa only [hcard] using hdeg)
  have card_deg (X : Finset V) (x : V)
      (hx : ∀ y ∈ X, H.Adj x y) : X.card ≤ H.degree x := by
    exact card_le_card (show X ⊆ H.neighborFinset x from fun y hy => by
      simpa only [mem_neighborFinset] using hx y hy)
  have clique_deg (X : Finset V)
      (hX : ∀ x ∈ X, ∀ y ∈ X, x ≠ y → H.Adj x y)
      (x : V) (hx : x ∈ X) : X.card ≤ H.degree x + 1 := by
    have h := card_deg (X.erase x) x (by
      intro y hy
      rcases mem_erase.mp hy with ⟨hyx, hyX⟩
      exact hX x hx y hyX hyx.symm)
    have hc := card_erase_of_mem hx
    omega
  have part (X : Finset V) (x : V) :
      (X.filter (G.Adj x)).card + (X.filter (fun y => ¬ G.Adj x y)).card = X.card :=
    card_filter_add_card_filter_not (G.Adj x)
  have hA90 : 90 * d ≤ A.card := by omega
  have hAD₀ : Disjoint A D₀ := hAD.mono_right hD₀D
  have hQD₀ : Disjoint Q D₀ := hQD.mono_right hD₀D
  have hAcli : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → H.Adj x y :=
    fun x hx y hy hne => hGH (hclique x hx y hy hne)
  have hAdeg (x : V) (hx : x ∈ A) : A.card ≤ H.degree x + 1 :=
    clique_deg A hAcli x hx
  have initial_union_degree (X Y : Finset V) (hXY : Disjoint X Y) (x : V) :
      (X.filter (G.Adj x)).card + (Y.filter (G.Adj x)).card ≤ H.degree x := by
    have h := card_deg ((X.filter (G.Adj x)) ∪ (Y.filter (G.Adj x))) x (by
      intro y hy
      rcases mem_union.mp hy with hy | hy <;> exact hGH (mem_filter.mp hy).2)
    rw [card_union_of_disjoint (hXY.mono (filter_subset ..) (filter_subset ..))] at h
    exact h
  have hAQedges : ∀ x ∈ A, ∀ q ∈ Q, H.Adj x q := by
    intro x hx q hq
    apply closed x q (fun h => Finset.disjoint_left.mp hAQ hx (h.symm ▸ hq))
    have ha := hAdeg x hx
    have hq1 := (hQdeg q hq).1
    have hq2 := (hQdeg q hq).2
    have hp := part D₀ q
    have hu := initial_union_degree A D₀ hAD₀ q
    omega
  have hQafter (q : V) (hq : q ∈ Q) : A.card + D₀.card ≤ H.degree q + d := by
    have h := card_deg (A ∪ (D₀.filter (G.Adj q))) q (by
      intro x hx
      rcases mem_union.mp hx with hx | hx
      · exact (hAQedges x hx q hq).symm
      · exact hGH (mem_filter.mp hx).2)
    rw [card_union_of_disjoint (hAD₀.mono_right (filter_subset ..))] at h
    have hp := part D₀ q
    have hh := (hQdeg q hq).2
    omega
  have hQcli : ∀ x ∈ Q, ∀ y ∈ Q, x ≠ y → H.Adj x y := by
    intro x hx y hy hne
    apply closed x y hne
    have hxdeg := hQafter x hx
    have hydeg := hQafter y hy
    omega
  let T := A ∪ Q
  have hTcard : T.card = A.card + Q.card := card_union_of_disjoint hAQ
  have hTcli : ∀ x ∈ T, ∀ y ∈ T, x ≠ y → H.Adj x y := by
    intro x hx y hy hne
    rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
    · exact hAcli x hx y hy hne
    · exact hAQedges x hx y hy
    · exact (hAQedges y hy x hx).symm
    · exact hQcli x hx y hy hne
  have hTD₀ : Disjoint T D₀ := disjoint_union_left.mpr ⟨hAD₀, hQD₀⟩
  have hD₀initial (x : V) (hx : x ∈ D₀) : T.card ≤ H.degree x + 2 * d := by
    have hu := initial_union_degree A Q hAQ x
    have ha := (hD₀deg x hx).2
    have hq := (hD₀deg x hx).1
    have hpa := part A x
    have hpq := part Q x
    omega
  have hTD₀edges : ∀ x ∈ T, ∀ y ∈ D₀, H.Adj x y := by
    intro x hx y hy
    apply closed x y (fun h => Finset.disjoint_left.mp hTD₀ hx (h.symm ▸ hy))
    have hxd := clique_deg T hTcli x hx
    have hyd := hD₀initial y hy
    omega
  have hD₀after (x : V) (hx : x ∈ D₀) : T.card ≤ H.degree x :=
    card_deg T x (fun y hy => (hTD₀edges y hy x hx).symm)
  have hD₀cli : ∀ x ∈ D₀, ∀ y ∈ D₀, x ≠ y → H.Adj x y := by
    intro x hx y hy hne
    apply closed x y hne
    have hxd := hD₀after x hx
    have hyd := hD₀after y hy
    omega
  let C := T ∪ D₀
  let P := D \ D₀
  have hCcard : C.card = A.card + Q.card + D₀.card := by
    change (T ∪ D₀).card = A.card + Q.card + D₀.card
    rw [card_union_of_disjoint hTD₀, hTcard]
  have hPcard : P.card + D₀.card = D.card := card_sdiff_add_card_eq_card hD₀D
  have hPsmall : P.card ≤ 10 * d := by omega
  have hCPsum : C.card + P.card = 2 * m := by omega
  have hCcli : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → H.Adj x y := by
    intro x hx y hy hne
    rcases mem_union.mp hx with hx | hx <;> rcases mem_union.mp hy with hy | hy
    · exact hTcli x hx y hy hne
    · exact hTD₀edges x hx y hy
    · exact (hTD₀edges y hy x hx).symm
    · exact hD₀cli x hx y hy hne
  have hCPdis : Disjoint C P := by
    apply Finset.disjoint_left.mpr
    intro x hxC hxP
    rcases mem_sdiff.mp hxP with ⟨hxD, hxnot⟩
    rcases mem_union.mp hxC with hxT | hxD₀
    · rcases mem_union.mp hxT with hxA | hxQ
      · exact Finset.disjoint_left.mp hAD hxA hxD
      · exact Finset.disjoint_left.mp hQD hxQ hxD
    · exact hxnot hxD₀
  have hPCedges : ∀ x ∈ P, ∀ y ∈ C, H.Adj x y := by
    intro x hx y hy
    apply closed x y (fun h => Finset.disjoint_left.mp hCPdis hy (h ▸ hx))
    have hyd := clique_deg C hCcli y hy
    have hxd := hDdeg x (mem_sdiff.mp hx).1
    have hsub := card_deg (A.filter (G.Adj x)) x (by
      intro z hz
      exact hGH (mem_filter.mp hz).2)
    omega
  have hPcli : ∀ x ∈ P, ∀ y ∈ P, x ≠ y → H.Adj x y := by
    intro x hx y hy hne
    apply closed x y hne
    have hxd := card_deg C x (fun z hz => hPCedges x hx z hz)
    have hyd := card_deg C y (fun z hz => hPCedges y hy z hz)
    omega
  have hCPcover (x : V) : x ∈ C ∨ x ∈ P := by
    rcases hcover x with hxA | hxQ | hxD
    · exact Or.inl (mem_union_left _ (mem_union_left _ hxA))
    · exact Or.inl (mem_union_left _ (mem_union_right _ hxQ))
    · by_cases hxD₀ : x ∈ D₀
      · exact Or.inl (mem_union_right _ hxD₀)
      · exact Or.inr (mem_sdiff.mpr ⟨hxD, hxD₀⟩)
  have hall : ∀ x y : V, x ≠ y → H.Adj x y := by
    intro x y hne
    rcases hCPcover x with hx | hx <;> rcases hCPcover y with hy | hy
    · exact hCcli x hx y hy hne
    · exact (hPCedges y hy x hx).symm
    · exact hPCedges x hx y hy
    · exact hPcli x hx y hy hne
  apply SimpleGraph.sI.mp
  apply SimpleGraph.x3 (G := H) (by omega)
  intro x
  have h := clique_deg univ (fun u _ v _ hne => hall u v hne) x (mem_univ x)
  rw [card_univ] at h
  omega

end EC3RepairedHamiltonian


/-
# Finite subset selection for repaired EC3 absorption

Keep the complete block A and trim Q and D to obtain exactly 2m vertices.
Choose Q first, then preserve as many of the good D₀ vertices as possible.
The resulting exceptional D vertices still number at most 10d.
-/

open Finset

namespace EC3SubsetSelection

theorem exists_trimmed_blocks {V : Type*} [DecidableEq V]
    (m d : ℕ) (A Q D₀ D : Finset V)
    (hmd : 10 * d ≤ m) (hA : A.card < 2 * m)
    (hD₀D : D₀ ⊆ D)
    (htotal : 2 * m ≤ A.card + Q.card + D.card)
    (hleft : m + 10 * d ≤ A.card + Q.card)
    (hbad : D.card ≤ D₀.card + 10 * d) :
    ∃ Q' D₀' D' : Finset V,
      Q' ⊆ Q ∧ D₀' ⊆ D₀ ∧ D₀' ⊆ D' ∧ D' ⊆ D ∧
      A.card + Q'.card + D'.card = 2 * m ∧
      m + 10 * d ≤ A.card + Q'.card ∧
      D'.card ≤ D₀'.card + 10 * d := by
  obtain ⟨Q', hQ'Q, hQ'card⟩ :=
    Finset.exists_subset_card_eq (Nat.min_le_left Q.card (2 * m - A.card))
  let r := 2 * m - A.card - Q'.card
  have hQ'bound : Q'.card ≤ 2 * m - A.card := by
    rw [hQ'card]
    exact Nat.min_le_right _ _
  have hrD : r ≤ D.card := by
    dsimp only [r]
    omega
  obtain ⟨D₀', hD₀'D₀, hD₀'card⟩ :=
    Finset.exists_subset_card_eq (Nat.min_le_left D₀.card r)
  have hD₀'r : D₀'.card ≤ r := by
    rw [hD₀'card]
    exact Nat.min_le_right _ _
  obtain ⟨D', hD₀'D', hD'D, hD'card⟩ :=
    Finset.exists_subsuperset_card_eq (hD₀'D₀.trans hD₀D) hD₀'r hrD
  refine ⟨Q', D₀', D', hQ'Q, hD₀'D₀, hD₀'D', hD'D, ?_, ?_, ?_⟩
  · dsimp only [r] at hD'card
    omega
  · omega
  · have hsize := Finset.card_le_card hD'D
    omega


end EC3SubsetSelection


/-
Finite-set transport and vertex selection for the repaired EC3 clique-absorption
lemma. The exact missing assumption is `12 * Q.card ≤ A.card`.
Credit: @fqlx; the repaired configuration and surrounding EC3 reduction are
based on PR14987 by @tgg6956g2z-bot, with its false original H3 corrected.
-/

open SimpleGraph Finset

namespace EC3RepairedAbsorption

theorem cycle_of_exact_core {V : Type*} [DecidableEq V]
    (m d : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A Q D₀ D : Finset V)
    (hm : 2 ≤ m) (hd : 1 ≤ d) (hmd : 100*d ≤ m)
    (hsum : A.card+Q.card+D.card=2*m)
    (hAQ : Disjoint A Q) (hAD : Disjoint A D) (hQD : Disjoint Q D)
    (hD₀D : D₀ ⊆ D) (hDsize : D.card ≤ D₀.card+10*d)
    (hclique : ∀ x ∈ A, ∀ y ∈ A, x ≠ y → G.Adj x y)
    (hAsize : 9*m ≤ 10*A.card) (hQsize : 12*Q.card ≤ A.card)
    (hTsize : m+10*d ≤ A.card+Q.card)
    (hQdeg : ∀ q ∈ Q, A.card ≤ 3*(A.filter (G.Adj q)).card ∧
      (D₀.filter (fun y => ¬G.Adj q y)).card ≤ d)
    (hD₀deg : ∀ x ∈ D₀, (Q.filter (fun y => ¬G.Adj x y)).card ≤ d ∧
      (A.filter (fun y => ¬G.Adj x y)).card ≤ d)
    (hDdeg : ∀ x ∈ D, A.card ≤ 4*(A.filter (G.Adj x)).card) :
    cycleGraph (2*m) ⊑ G := by
  classical
  let S := A ∪ Q ∪ D
  have hAS : A ⊆ S := fun x hx => mem_union_left _ (mem_union_left _ hx)
  have hQS : Q ⊆ S := fun x hx => mem_union_left _ (mem_union_right _ hx)
  have hDS : D ⊆ S := fun x hx => mem_union_right _ hx
  have hD₀S : D₀ ⊆ S := hD₀D.trans hDS
  have hScard : S.card=2*m := by
    rw [show S.card=(A∪Q).card+D.card from card_union_of_disjoint (disjoint_union_left.mpr ⟨hAD,hQD⟩),
      card_union_of_disjoint hAQ,hsum]
  let lift (X : Finset V) : Finset S := X.subtype (fun x => x∈S)
  have mem_lift (X : Finset V) (x : S) : x∈lift X ↔ x.val∈X := by
    simp only [lift,Finset.mem_subtype]
  have card_lift (X : Finset V) (hX : X⊆S) : (lift X).card=X.card := by
    rw [Finset.card_subtype,filter_eq_self.mpr hX]
  have card_filter (X : Finset V) (hX : X⊆S) (P : V→Prop) [DecidablePred P] :
      ((lift X).filter (fun x : S => P x.val)).card=(X.filter P).card := by
    have he : (lift X).filter (fun x : S => P x.val)=lift (X.filter P) := by
      ext x
      simp only [mem_filter,mem_lift]
    rw [he,card_lift _ ((filter_subset ..).trans hX)]
  have disj_lift {X Y : Finset V} (h : Disjoint X Y) : Disjoint (lift X) (lift Y) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    exact Finset.disjoint_left.mp h ((mem_lift _ _).mp hx) ((mem_lift _ _).mp hy)
  let H := G.induce (S : Set V)
  have hcard : Fintype.card S=2*m := by simpa using hScard
  have hham : H.IsHamiltonian := by
    apply EC3RepairedHamiltonian.hamiltonian_repaired_core m d H
      (lift A) (lift Q) (lift D₀) (lift D) hm hd hmd hcard
    · intro x
      have hx : x.val∈S := x.property
      rcases mem_union.mp hx with hx | hx
      · rcases mem_union.mp hx with hx | hx
        · exact Or.inl ((mem_lift _ _).mpr hx)
        · exact Or.inr (Or.inl ((mem_lift _ _).mpr hx))
      · exact Or.inr (Or.inr ((mem_lift _ _).mpr hx))
    · simpa only [card_lift A hAS,card_lift Q hQS,card_lift D hDS] using hsum
    · exact disj_lift hAQ
    · exact disj_lift hAD
    · exact disj_lift hQD
    · intro x hx
      exact (mem_lift _ _).mpr (hD₀D ((mem_lift _ _).mp hx))
    · simpa only [card_lift D hDS,card_lift D₀ hD₀S] using hDsize
    · intro x hx y hy hne
      exact hclique _ ((mem_lift _ _).mp hx) _ ((mem_lift _ _).mp hy)
        (fun he => hne (Subtype.ext he))
    · simpa only [card_lift A hAS] using hAsize
    · simpa only [card_lift A hAS,card_lift Q hQS] using hQsize
    · simpa only [card_lift A hAS,card_lift Q hQS] using hTsize
    · intro q hq
      have h := hQdeg q.val ((mem_lift _ _).mp hq)
      change (lift A).card ≤ 3*((lift A).filter (fun x => G.Adj q.val x.val)).card ∧
        ((lift D₀).filter (fun x => ¬G.Adj q.val x.val)).card ≤ d
      rw [card_lift A hAS,
        card_filter A hAS (fun y => G.Adj q.val y),
        card_filter D₀ hD₀S (fun y => ¬G.Adj q.val y)]
      exact h
    · intro x hx
      have h := hD₀deg x.val ((mem_lift _ _).mp hx)
      change ((lift Q).filter (fun y => ¬G.Adj x.val y.val)).card ≤ d ∧
        ((lift A).filter (fun y => ¬G.Adj x.val y.val)).card ≤ d
      rw [card_filter Q hQS (fun y => ¬G.Adj x.val y),
        card_filter A hAS (fun y => ¬G.Adj x.val y)]
      exact h
    · intro x hx
      have h := hDdeg x.val ((mem_lift _ _).mp hx)
      change (lift A).card ≤ 4*((lift A).filter (fun y => G.Adj x.val y.val)).card
      rw [card_lift A hAS,card_filter A hAS (fun y => G.Adj x.val y)]
      exact h
  obtain ⟨z,p,hp⟩ := hham (by change Fintype.card S ≠ 1; omega)
  have hc : cycleGraph (2*m) ⊑ H :=
    (cycleGraph_isContained_iff (by omega)).mpr ⟨z,p,hp.isCycle,hp.length_eq.trans hcard⟩
  exact hc.trans (Embedding.induce (G:=G) (S : Set V)).isContained

theorem repaired_clique_absorption {V : Type*} [DecidableEq V]
    (m d : ℕ) (G : SimpleGraph V) [DecidableRel G.Adj]
    (A Q D₀ D : Finset V)
    (hm : 2 ≤ m) (hd : 1 ≤ d) (hmd : 100*d ≤ m)
    (hAQ : Disjoint A Q) (hAD : Disjoint A D) (hQD : Disjoint Q D)
    (hD₀D : D₀⊆D) (hDsize : D.card≤D₀.card+10*d)
    (hclique : ∀ x∈A,∀ y∈A,x≠y→G.Adj x y)
    (hAsize : 9*m≤10*A.card) (hQsize : 12*Q.card≤A.card)
    (htotal : 2*m≤A.card+Q.card+D.card)
    (hTsize : m+10*d≤A.card+Q.card)
    (hQdeg : ∀q∈Q,A.card≤3*(A.filter (G.Adj q)).card ∧
      (D₀.filter (fun y=>¬G.Adj q y)).card≤d)
    (hD₀deg : ∀x∈D₀,(Q.filter (fun y=>¬G.Adj x y)).card≤d ∧
      (A.filter (fun y=>¬G.Adj x y)).card≤d)
    (hDdeg : ∀x∈D,A.card≤4*(A.filter (G.Adj x)).card) :
    cycleGraph (2*m) ⊑ G := by
  classical
  by_cases ha : 2*m≤A.card
  · obtain ⟨e⟩ : Nonempty (Fin (2*m) ↪ A) := Function.Embedding.nonempty_of_card_le (by simpa using ha)
    let f : cycleGraph (2*m) →g G := ⟨fun i=>(e i).val,by
      intro i j hij
      exact hclique _ (e i).property _ (e j).property
        (fun he=>hij.ne (e.injective (Subtype.ext he)))⟩
    exact ⟨⟨f,Subtype.val_injective.comp e.injective⟩⟩
  · obtain ⟨Q',D₀',D',hQ',hD₀',hD₀D',hD',hsum,hleft,hbad⟩ :=
      EC3SubsetSelection.exists_trimmed_blocks m d A Q D₀ D
        (by omega) (by omega) hD₀D htotal hTsize hDsize
    apply cycle_of_exact_core m d G A Q' D₀' D' hm hd hmd hsum
      (hAQ.mono_right hQ') (hAD.mono_right hD') (hQD.mono hQ' hD')
      hD₀D' hbad hclique hAsize
    · exact (Nat.mul_le_mul_left 12 (card_le_card hQ')).trans hQsize
    · exact hleft
    · intro q hq
      have h := hQdeg q (hQ' hq)
      exact ⟨h.1,(card_le_card (filter_subset_filter _ hD₀')).trans h.2⟩
    · intro x hx
      have h := hD₀deg x (hD₀' hx)
      exact ⟨(card_le_card (filter_subset_filter _ hQ')).trans h.1,h.2⟩
    · intro x hx
      exact hDdeg x (hD' hx)

end EC3RepairedAbsorption


-- Reduction Erdos556.erdos_556.variants.benevides_skokan_large_even.R1.H3.R1
-- of step Erdos556.erdos_556.variants.benevides_skokan_large_even.R1.H3
-- Credit: @tgg6956g2z-bot

/-
# Repaired EC3 absorption reduction

We discharge the 3-colour vertex cleaning, pigeonhole classification, maximal red/blue
matching extraction inside `A'`, and all EC3 block-size arithmetic directly in `main`,
reducing `R1.H3` to three standalone single-colour graph lemmas:

* `H1`: Dense bipartite cycle with bounded exceptions (Hall's theorem, as in `R2.H2`).
* `H2`: Greedy matching-spliced dense bipartite cycle.
* `H3`: Green clique + dense bipartite alternating-path absorption.
-/

open Filter SimpleGraph Finset

namespace OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R1_H3_R1

private lemma natCard_eq_filter_card {N : ℕ} (P : Fin N → Prop) [DecidablePred P] :
    Nat.card {v : Fin N // P v} = (Finset.univ.filter P).card := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

private lemma natCard_edges_eq_sum {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (f : Fin N → Fin 4) (S T : Finset (Fin 4)) :
    Nat.card {e : Fin N × Fin N // f e.1 ∈ S ∧ f e.2 ∈ T ∧ G.Adj e.1 e.2} =
      ∑ x ∈ Finset.univ.filter (fun v : Fin N => f v ∈ S),
        ((Finset.univ.filter (fun v : Fin N => f v ∈ T)).filter (G.Adj x)).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let X := Finset.univ.filter (fun v : Fin N => f v ∈ S)
  let Y := Finset.univ.filter (fun v : Fin N => f v ∈ T)
  have hsub : Finset.univ.filter (fun e : Fin N × Fin N => f e.1 ∈ S ∧ f e.2 ∈ T ∧ G.Adj e.1 e.2) =
      (X.sigma (fun x => Y.filter (G.Adj x))).map
        ⟨fun p => (p.1, p.2), fun a b h => by
          rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
          simp only [Prod.mk.injEq] at h
          exact Sigma.ext h.1 (heq_of_eq h.2)⟩ := by
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Finset.mem_sigma, X, Y]
    constructor
    · rintro ⟨hu, hv, huv⟩; exact ⟨⟨u, v⟩, ⟨hu, hv, huv⟩, rfl⟩
    · rintro ⟨⟨u', v'⟩, ⟨hu', hv', huv⟩, h⟩
      cases h
      exact ⟨hu', hv', huv⟩
  rw [hsub, Finset.card_map, Finset.card_sigma]

private lemma natCard_edges_eq_sum_swap {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (f : Fin N → Fin 4) (S T : Finset (Fin 4)) :
    Nat.card {e : Fin N × Fin N // f e.1 ∈ S ∧ f e.2 ∈ T ∧ G.Adj e.1 e.2} =
      ∑ y ∈ Finset.univ.filter (fun v : Fin N => f v ∈ T),
        ((Finset.univ.filter (fun v : Fin N => f v ∈ S)).filter (G.Adj y)).card := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  let X := Finset.univ.filter (fun v : Fin N => f v ∈ S)
  let Y := Finset.univ.filter (fun v : Fin N => f v ∈ T)
  have hsub : Finset.univ.filter (fun e : Fin N × Fin N => f e.1 ∈ S ∧ f e.2 ∈ T ∧ G.Adj e.1 e.2) =
      (Y.sigma (fun y => X.filter (G.Adj y))).map
        ⟨fun p => (p.2, p.1), fun a b h => by
          rcases a with ⟨a1, a2⟩; rcases b with ⟨b1, b2⟩
          simp only [Prod.mk.injEq] at h
          exact Sigma.ext h.2 (heq_of_eq h.1)⟩ := by
    ext ⟨u, v⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Finset.mem_sigma, X, Y]
    constructor
    · rintro ⟨hu, hv, huv⟩; exact ⟨⟨v, u⟩, ⟨hv, hu, huv.symm⟩, rfl⟩
    · rintro ⟨⟨v', u'⟩, ⟨hv', hu', hvu⟩, h⟩
      cases h
      exact ⟨hu', hv', hvu.symm⟩
  rw [hsub, Finset.card_map, Finset.card_sigma]

private lemma bad_card_le_of_dense {N : ℕ} (G : SimpleGraph (Fin N)) [DecidableRel G.Adj]
    (X Y : Finset (Fin N)) (d : ℕ) (hd : 0 < d) (δ : ℝ)
    (hδ : δ * (X.card : ℝ) * (Y.card : ℝ) ≤ (d : ℝ) * (d : ℝ))
    (hdense : (1 - δ) * (X.card : ℝ) * (Y.card : ℝ) ≤
      ∑ x ∈ X, ((Y.filter (G.Adj x)).card : ℝ)) :
    (X.filter (fun x => d < (Y.filter (fun y => ¬ G.Adj x y)).card)).card ≤ d := by
  classical
  let bad := X.filter (fun x => d < (Y.filter (fun y => ¬ G.Adj x y)).card)
  have hpart : ∀ x ∈ X, (Y.filter (G.Adj x)).card + (Y.filter (fun y => ¬ G.Adj x y)).card = Y.card :=
    fun x _ => Finset.card_filter_add_card_filter_not (G.Adj x)
  have hsum_nat : (∑ x ∈ X, (Y.filter (G.Adj x)).card) +
      (∑ x ∈ X, (Y.filter (fun y => ¬ G.Adj x y)).card) = X.card * Y.card := by
    rw [← Finset.sum_add_distrib]
    calc ∑ x ∈ X, ((Y.filter (G.Adj x)).card + (Y.filter (fun y => ¬ G.Adj x y)).card)
        = ∑ _x ∈ X, Y.card := Finset.sum_congr rfl hpart
      _ = X.card * Y.card := by simp
  have hsum_real : (∑ x ∈ X, ((Y.filter (fun y => ¬ G.Adj x y)).card : ℝ)) ≤
      (d : ℝ) * (d : ℝ) := by
    have h1 : ((∑ x ∈ X, (Y.filter (G.Adj x)).card : ℕ) : ℝ) +
        ((∑ x ∈ X, (Y.filter (fun y => ¬ G.Adj x y)).card : ℕ) : ℝ) =
        (X.card : ℝ) * (Y.card : ℝ) := by exact_mod_cast hsum_nat
    push_cast at h1
    linarith
  have hmiss_nat : ∑ x ∈ X, (Y.filter (fun y => ¬ G.Adj x y)).card ≤ d * d := by
    exact_mod_cast hsum_real
  have hlow : bad.card * (d + 1) ≤ ∑ x ∈ X, (Y.filter (fun y => ¬ G.Adj x y)).card := by
    calc bad.card * (d + 1) = ∑ _x ∈ bad, (d + 1) := by simp
      _ ≤ ∑ x ∈ bad, (Y.filter (fun y => ¬ G.Adj x y)).card := by
        apply Finset.sum_le_sum
        intro x hx
        exact (Finset.mem_filter.mp hx).2
      _ ≤ ∑ x ∈ X, (Y.filter (fun y => ¬ G.Adj x y)).card :=
        Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)
  change bad.card ≤ d
  by_contra! h
  have hle : (d + 1) * (d + 1) ≤ d * d :=
    (Nat.mul_le_mul_right (d + 1) h).trans (hlow.trans hmiss_nat)
  nlinarith only [hle]
 
private lemma exists_maximal_matching {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (A : Finset V) (K : ℕ) :
    (∃ u v : Fin K → V, Function.Injective u ∧ Function.Injective v ∧
      (∀ i, u i ∈ A ∧ v i ∈ A ∧ G.Adj (u i) (v i)) ∧ (∀ i j, u i ≠ v j)) ∨
    (∃ M ⊆ A, M.card ≤ 2 * (K - 1) ∧
      ∀ x ∈ A \ M, ∀ y ∈ A \ M, ¬ G.Adj x y) := by
  classical
  have haux : ∀ k : ℕ, k ≤ K →
      (∃ u v : Fin k → V, Function.Injective u ∧ Function.Injective v ∧
        (∀ i, u i ∈ A ∧ v i ∈ A ∧ G.Adj (u i) (v i)) ∧ (∀ i j, u i ≠ v j)) ∨
      (∃ M ⊆ A, M.card ≤ 2 * (K - 1) ∧ ∀ x ∈ A \ M, ∀ y ∈ A \ M, ¬ G.Adj x y) := by
    intro k
    induction k with
    | zero =>
      intro _
      left
      exact ⟨Fin.elim0, Fin.elim0, fun i => i.elim0, fun i => i.elim0,
        fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      rcases ih (by omega) with ⟨u, v, hu, hv, huv, hdisj⟩ | hmax
      · let U : Finset V := Finset.univ.image u
        let W : Finset V := Finset.univ.image v
        let M : Finset V := U ∪ W
        have hMA : M ⊆ A := by
          intro z hz
          rcases Finset.mem_union.mp hz with h | h
          · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h; exact (huv i).1
          · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp h; exact (huv i).2.1
        have hMcard : M.card ≤ 2 * k := by
          change (U ∪ W).card ≤ 2 * k
          have h1 := Finset.card_union_le U W
          have h2 : U.card ≤ k := (Finset.card_image_le).trans (by simp)
          have h3 : W.card ≤ k := (Finset.card_image_le).trans (by simp)
          omega
        by_cases hedge : ∃ x ∈ A \ M, ∃ y ∈ A \ M, G.Adj x y
        · obtain ⟨x, hx, y, hy, hxy⟩ := hedge
          have hxA : x ∈ A := (Finset.mem_sdiff.mp hx).1
          have hxM : x ∉ M := (Finset.mem_sdiff.mp hx).2
          have hyA : y ∈ A := (Finset.mem_sdiff.mp hy).1
          have hyM : y ∉ M := (Finset.mem_sdiff.mp hy).2
          have hne : x ≠ y := G.ne_of_adj hxy
          left
          refine ⟨Fin.snoc u x, Fin.snoc v y, ?_, ?_, ?_, ?_⟩
          · intro a b hab
            revert hab
            refine Fin.lastCases ?_ (fun a' => ?_) a <;> refine Fin.lastCases ?_ (fun b' => ?_) b <;> intro hab
            · rfl
            · simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
              exact (hxM (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨b', Finset.mem_univ _, hab.symm⟩))).elim
            · simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
              exact (hxM (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a', Finset.mem_univ _, hab⟩))).elim
            · simp only [Fin.snoc_castSucc] at hab
              exact congrArg Fin.castSucc (hu hab)
          · intro a b hab
            revert hab
            refine Fin.lastCases ?_ (fun a' => ?_) a <;> refine Fin.lastCases ?_ (fun b' => ?_) b <;> intro hab
            · rfl
            · simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
              exact (hyM (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b', Finset.mem_univ _, hab.symm⟩))).elim
            · simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
              exact (hyM (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a', Finset.mem_univ _, hab⟩))).elim
            · simp only [Fin.snoc_castSucc] at hab
              exact congrArg Fin.castSucc (hv hab)
          · intro i
            refine Fin.lastCases ?_ (fun i' => ?_) i
            · simpa [Fin.snoc_last] using ⟨hxA, hyA, hxy⟩
            · simpa [Fin.snoc_castSucc] using huv i'
          · intro a b hab
            revert hab
            refine Fin.lastCases ?_ (fun a' => ?_) a <;> refine Fin.lastCases ?_ (fun b' => ?_) b <;> intro hab
            · simp only [Fin.snoc_last] at hab; exact hne hab
            · simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
              exact hxM (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨b', Finset.mem_univ _, hab.symm⟩))
            · simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
              exact hyM (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a', Finset.mem_univ _, hab⟩))
            · simp only [Fin.snoc_castSucc] at hab
              exact hdisj a' b' hab
        · push_neg at hedge
          right
          exact ⟨M, hMA, by omega, hedge⟩
      · exact Or.inr hmax
  exact haux K le_rfl

/-- Single-colour dense bipartite cycle with bounded exceptions. -/
def H1 : Prop :=
  ∀ (m d : ℕ) (G : SimpleGraph (Fin (4 * m))) [DecidableRel G.Adj]
    (A B₀ B : Finset (Fin (4 * m))),
    2 ≤ m → 1 ≤ d → 100 * d ≤ m →
    Disjoint A B → B₀ ⊆ B →
    m + 10 * d ≤ A.card → m ≤ B.card → m ≤ B₀.card + m / 20 →
    (∀ x ∈ B₀, (A.filter (fun y => ¬ G.Adj x y)).card ≤ d) →
    (∀ x ∈ B, A.card ≤ 4 * (A.filter (G.Adj x)).card) →
    cycleGraph (2 * m) ⊑ G

/-- Single-colour matching-spliced dense bipartite cycle. -/
def H2 : Prop :=
  ∀ (m d : ℕ) (G : SimpleGraph (Fin (4 * m))) [DecidableRel G.Adj]
    (A B₀ : Finset (Fin (4 * m))),
    2 ≤ m → 1 ≤ d → 100 * d ≤ m →
    Disjoint A B₀ →
    B₀.card < m → m ≤ B₀.card + m / 20 →
    2 * m + 10 * d ≤ A.card + B₀.card →
    (∀ x ∈ B₀, (A.filter (fun y => ¬ G.Adj x y)).card ≤ d) →
    (∀ x ∈ A, (B₀.filter (fun y => ¬ G.Adj x y)).card ≤ d) →
    (∃ u v : Fin (2 * (m - B₀.card)) → Fin (4 * m),
      Function.Injective u ∧ Function.Injective v ∧
      (∀ i, u i ∈ A ∧ v i ∈ A ∧ G.Adj (u i) (v i)) ∧
      (∀ i j, u i ≠ v j)) →
    cycleGraph (2 * m) ⊑ G

/-- Single-colour clique with dense bipartite alternating-path absorption. -/
def H3 : Prop :=
  ∀ (m d : ℕ) (G : SimpleGraph (Fin (4 * m))) [DecidableRel G.Adj]
    (A Q D₀ D : Finset (Fin (4 * m))),
    2 ≤ m → 1 ≤ d → 100 * d ≤ m →
    Disjoint A Q → Disjoint A D → Disjoint Q D → D₀ ⊆ D →
    D.card ≤ D₀.card + 10 * d →
    (∀ x ∈ A, ∀ y ∈ A, x ≠ y → G.Adj x y) →
    9 * m ≤ 10 * A.card →
    12 * Q.card ≤ A.card →
    2 * m ≤ A.card + Q.card + D.card →
    m + 10 * d ≤ A.card + Q.card →
    m + 10 * d ≤ A.card + D₀.card →
    (∀ q ∈ Q, A.card ≤ 3 * (A.filter (G.Adj q)).card ∧
      (D₀.filter (fun y => ¬ G.Adj q y)).card ≤ d) →
    (∀ x ∈ D₀, (Q.filter (fun y => ¬ G.Adj x y)).card ≤ d ∧
      (A.filter (fun y => ¬ G.Adj x y)).card ≤ d) →
    (∀ x ∈ D, A.card ≤ 4 * (A.filter (G.Adj x)).card) →
    cycleGraph (2 * m) ⊑ G

section

set_option maxHeartbeats 4000000 in
theorem main :
    H1 → H2 → H3 →
    OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R3.H3 := by
  classical
  intro h1 h2 h3
  refine ⟨1 / 100, by norm_num, fun μ hμ_pos hμ_le => ?_⟩
  let δ₀ : ℝ := μ * μ / 10000000000
  have hδ₀_pos : 0 < δ₀ := by positivity
  refine ⟨δ₀, hδ₀_pos, ?_⟩
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (20000 / μ)
  filter_upwards [eventually_ge_atTop (2 * max M₀ 2000)] with n hn heven
  obtain ⟨m, hm_eq⟩ := heven
  have hn2m : n = 2 * m := by omega
  subst hn2m
  have hm_ge_2000 : 2000 ≤ m := by omega
  have hm_ge_M0 : M₀ ≤ m := by omega
  have hμm_upper : μ * (m : ℝ) ≤ (m : ℝ) / 100 := by
    calc
      μ * (m : ℝ) ≤ (1 / 100 : ℝ) * (m : ℝ) :=
        mul_le_mul_of_nonneg_right hμ_le (Nat.cast_nonneg m)
      _ = _ := by ring
  have hm_mu : (20000 : ℝ) < μ * (m : ℝ) := by
    have h1' : (20000 : ℝ) / μ < (m : ℝ) := lt_of_lt_of_le hM₀ (by exact_mod_cast hm_ge_M0)
    simpa only [mul_comm (m : ℝ) μ] using (div_lt_iff₀ hμ_pos).mp h1'
  rw [show 2 * (2 * m) = 4 * m by omega]
  intro δ hδ_pos hδ_le c hc f hsizes hdense
  letI : ∀ i, DecidableRel (c i).Adj := fun i => Classical.decRel _
  let W : Fin 4 → Finset (Fin (4 * m)) := fun j => Finset.univ.filter (fun v => f v = j)
  have hdisW : ∀ i j : Fin 4, i ≠ j → Disjoint (W i) (W j) := by
    intro i j hij
    refine Finset.disjoint_left.mpr fun x hx hy => hij ?_
    exact (Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2
  have hsumW : (W 0).card + (W 1).card + (W 2).card + (W 3).card = 4 * m := by
    have huniv : Finset.univ = W 0 ∪ W 1 ∪ W 2 ∪ W 3 := by
      ext v
      simp only [Finset.mem_univ, Finset.mem_union, Finset.mem_filter, true_and, true_iff, W]
      generalize f v = j
      fin_cases j <;> decide
    have h01 : Disjoint (W 0) (W 1) := hdisW 0 1 (by decide)
    have h01_2 : Disjoint (W 0 ∪ W 1) (W 2) :=
      Finset.disjoint_union_left.mpr ⟨hdisW 0 2 (by decide), hdisW 1 2 (by decide)⟩
    have h012_3 : Disjoint (W 0 ∪ W 1 ∪ W 2) (W 3) :=
      Finset.disjoint_union_left.mpr ⟨Finset.disjoint_union_left.mpr
        ⟨hdisW 0 3 (by decide), hdisW 1 3 (by decide)⟩, hdisW 2 3 (by decide)⟩
    have hc4 : (Finset.univ : Finset (Fin (4 * m))).card = 4 * m := by simp
    rw [huniv, Finset.card_union_of_disjoint h012_3, Finset.card_union_of_disjoint h01_2,
      Finset.card_union_of_disjoint h01] at hc4
    exact hc4
  have ha_eq (j : Fin 4) : (Nat.card {v : Fin (4 * m) // f v = j} : ℝ) = ((W j).card : ℝ) := by
    rw [natCard_eq_filter_card]
  have hW_sing (j : Fin 4) : Finset.univ.filter (fun v : Fin (4 * m) => f v ∈ ({j} : Finset (Fin 4))) = W j := by
    ext v; simp [W]
  rcases hsizes with ⟨hmin012, ha3_low, hdom, ha03_up⟩
  simp only [ha_eq, Nat.cast_mul, Nat.cast_ofNat] at hmin012 ha3_low hdom ha03_up
  have h2m_div : ((2 * m : ℕ) : ℝ) / 2 = (m : ℝ) := by push_cast; ring
  have ha0_low : (1 - 4 / 5 * μ) * (m : ℝ) ≤ (W 0).card := by
    have := le_trans hmin012 (min_le_left _ _); linarith [h2m_div]
  have ha1_low : (1 - 4 / 5 * μ) * (m : ℝ) ≤ (W 1).card := by
    have := le_trans hmin012 (le_trans (min_le_right _ _) (min_le_left _ _)); linarith [h2m_div]
  have ha2_low : (1 - 4 / 5 * μ) * (m : ℝ) ≤ (W 2).card := by
    have := le_trans hmin012 (le_trans (min_le_right _ _) (min_le_right _ _)); linarith [h2m_div]
  have ha3_low' : μ * (m : ℝ) ≤ (W 3).card := by linarith [h2m_div]
  have ha0_ge1 : ((W 1).card : ℝ) + μ * (m : ℝ) ≤ (W 0).card := by
    have := le_max_left ((W 1).card : ℝ) (max ((W 2).card : ℝ) ((W 3).card : ℝ)); linarith [h2m_div]
  have ha0_ge2 : ((W 2).card : ℝ) + μ * (m : ℝ) ≤ (W 0).card := by
    have := le_trans (le_max_left ((W 2).card : ℝ) ((W 3).card : ℝ)) (le_max_right ((W 1).card : ℝ) _); linarith [h2m_div]
  have ha0_ge3 : ((W 3).card : ℝ) + μ * (m : ℝ) ≤ (W 0).card := by
    have := le_trans (le_max_right ((W 2).card : ℝ) ((W 3).card : ℝ)) (le_max_right ((W 1).card : ℝ) _); linarith [h2m_div]
  have ha03_up' : ((W 0).card : ℝ) + ((W 3).card : ℝ) ≤ (2 + 3 / 5 * μ) * (m : ℝ) := by
    have : ((2 * m : ℕ) : ℝ) = 2 * (m : ℝ) := by push_cast; ring
    linarith
  have ha12_low : (2 - 3 / 5 * μ) * (m : ℝ) ≤ ((W 1).card : ℝ) + ((W 2).card : ℝ) := by
    have hsumR : ((W 0).card : ℝ) + ((W 1).card : ℝ) + ((W 2).card : ℝ) + ((W 3).card : ℝ) = 4 * (m : ℝ) := by
      exact_mod_cast hsumW
    linarith
  let d : ℕ := Nat.floor (μ * (m : ℝ) / 1000)
  have hd_pos : 1 ≤ d := by
    have : (1 : ℝ) ≤ μ * (m : ℝ) / 1000 := by linarith
    apply Nat.le_floor
    exact_mod_cast this
  have hd_upper : (d : ℝ) ≤ μ * (m : ℝ) / 1000 := Nat.floor_le (by positivity)
  have hd_lower : μ * (m : ℝ) / 2000 ≤ (d : ℝ) := by
    have hlt := Nat.lt_floor_add_one (μ * (m : ℝ) / 1000)
    linarith
  have h100d : 100 * d ≤ m := by
    have : (100 * d : ℝ) ≤ (m : ℝ) := by linarith
    exact_mod_cast this
  have hpair_dense (k : Fin 3) (i j : Fin 4)
      (hmem : (k, ({i} : Finset (Fin 4)), ({j} : Finset (Fin 4))) ∈
        ([(0, {0}, {1}), (0, {2}, {3}), (1, {0}, {3}), (1, {1}, {2}), (2, {0}, {2}), (2, {1}, {3})] :
          List (Fin 3 × Finset (Fin 4) × Finset (Fin 4)))) :
      (1 - δ) * ((W i).card : ℝ) * ((W j).card : ℝ) ≤
        ∑ x ∈ W i, (((W j).filter ((c k).Adj x)).card : ℝ) ∧
      (1 - δ) * ((W j).card : ℝ) * ((W i).card : ℝ) ≤
        ∑ y ∈ W j, (((W i).filter ((c k).Adj y)).card : ℝ) := by
    have h0 := hdense k {i} {j} hmem
    have h1 := h0
    rw [natCard_eq_filter_card, natCard_eq_filter_card, natCard_edges_eq_sum, hW_sing i, hW_sing j] at h0
    rw [natCard_eq_filter_card, natCard_eq_filter_card, natCard_edges_eq_sum_swap, hW_sing i, hW_sing j] at h1
    push_cast at h0 h1
    exact ⟨h0, by linarith⟩
  have hδ_cap (X Y : Finset (Fin (4 * m))) : δ * (X.card : ℝ) * (Y.card : ℝ) ≤ (d : ℝ) * (d : ℝ) := by
    have hX : (X.card : ℝ) ≤ 4 * (m : ℝ) := by exact_mod_cast (by simpa using Finset.card_le_univ X : X.card ≤ 4 * m)
    have hY : (Y.card : ℝ) ≤ 4 * (m : ℝ) := by exact_mod_cast (by simpa using Finset.card_le_univ Y : Y.card ≤ 4 * m)
    have h1 : δ * (X.card : ℝ) * (Y.card : ℝ) ≤ δ₀ * (4 * (m : ℝ)) * (4 * (m : ℝ)) := by
      gcongr
    have h2 : δ₀ * (4 * (m : ℝ)) * (4 * (m : ℝ)) ≤ (μ * (m : ℝ) / 2000) * (μ * (m : ℝ) / 2000) := by
      dsimp only [δ₀]; linarith only [sq_nonneg (μ * (m : ℝ))]
    have h3 : (μ * (m : ℝ) / 2000) * (μ * (m : ℝ) / 2000) ≤ (d : ℝ) * (d : ℝ) :=
      mul_self_le_mul_self (by positivity) hd_lower
    exact h1.trans (h2.trans h3)
  have hd01 := hpair_dense 0 0 1 (by simp)
  have hd13 := hpair_dense 1 0 3 (by simp)
  have hd22 := hpair_dense 2 0 2 (by simp)
  let A_bad1 := (W 0).filter (fun x => d < ((W 1).filter (fun y => ¬ (c 0).Adj x y)).card)
  let A_bad2 := (W 0).filter (fun x => d < ((W 2).filter (fun y => ¬ (c 2).Adj x y)).card)
  let A_bad3 := (W 0).filter (fun x => d < ((W 3).filter (fun y => ¬ (c 1).Adj x y)).card)
  have hAb1 : A_bad1.card ≤ d := bad_card_le_of_dense (c 0) (W 0) (W 1) d hd_pos δ (hδ_cap _ _) hd01.1
  have hAb2 : A_bad2.card ≤ d := bad_card_le_of_dense (c 2) (W 0) (W 2) d hd_pos δ (hδ_cap _ _) hd22.1
  have hAb3 : A_bad3.card ≤ d := bad_card_le_of_dense (c 1) (W 0) (W 3) d hd_pos δ (hδ_cap _ _) hd13.1
  let A' := (W 0) \ (A_bad1 ∪ A_bad2 ∪ A_bad3)
  have hA'_sub : A' ⊆ W 0 := Finset.sdiff_subset
  have hA'_card : (W 0).card ≤ A'.card + 3 * d := by
    have h1 := Finset.card_sdiff_add_card_inter (W 0) (A_bad1 ∪ A_bad2 ∪ A_bad3)
    change A'.card + _ = _ at h1
    have h2 : ((W 0) ∩ (A_bad1 ∪ A_bad2 ∪ A_bad3)).card ≤ (A_bad1 ∪ A_bad2 ∪ A_bad3).card :=
      Finset.card_le_card Finset.inter_subset_right
    have h3 := (Finset.card_union_le (A_bad1 ∪ A_bad2) A_bad3).trans
      (Nat.add_le_add_right (Finset.card_union_le A_bad1 A_bad2) _)
    omega
  let B₀ := (W 1).filter (fun x => ((W 0).filter (fun y => ¬ (c 0).Adj x y)).card ≤ d)
  let C₀ := (W 2).filter (fun x => ((W 0).filter (fun y => ¬ (c 2).Adj x y)).card ≤ d)
  let D₀ := (W 3).filter (fun x => ((W 0).filter (fun y => ¬ (c 1).Adj x y)).card ≤ d)
  have hB0_card : (W 1).card ≤ B₀.card + d := by
    have hbad := bad_card_le_of_dense (c 0) (W 1) (W 0) d hd_pos δ (hδ_cap _ _) hd01.2
    have hsum := Finset.card_filter_add_card_filter_not (s := W 1)
      (fun x => ((W 0).filter (fun y => ¬ (c 0).Adj x y)).card ≤ d)
    change B₀.card + _ = _ at hsum
    have hnot : ((W 1).filter (fun x => ¬ ((W 0).filter (fun y => ¬ (c 0).Adj x y)).card ≤ d)).card ≤ d := by
      simpa only [not_le] using hbad
    omega
  have hC0_card : (W 2).card ≤ C₀.card + d := by
    have hbad := bad_card_le_of_dense (c 2) (W 2) (W 0) d hd_pos δ (hδ_cap _ _) hd22.2
    have hsum := Finset.card_filter_add_card_filter_not (s := W 2)
      (fun x => ((W 0).filter (fun y => ¬ (c 2).Adj x y)).card ≤ d)
    change C₀.card + _ = _ at hsum
    have hnot : ((W 2).filter (fun x => ¬ ((W 0).filter (fun y => ¬ (c 2).Adj x y)).card ≤ d)).card ≤ d := by
      simpa only [not_le] using hbad
    omega
  have hD0_card : (W 3).card ≤ D₀.card + d := by
    have hbad := bad_card_le_of_dense (c 1) (W 3) (W 0) d hd_pos δ (hδ_cap _ _) hd13.2
    have hsum := Finset.card_filter_add_card_filter_not (s := W 3)
      (fun x => ((W 0).filter (fun y => ¬ (c 1).Adj x y)).card ≤ d)
    change D₀.card + _ = _ at hsum
    have hnot : ((W 3).filter (fun x => ¬ ((W 0).filter (fun y => ¬ (c 1).Adj x y)).card ≤ d)).card ≤ d := by
      simpa only [not_le] using hbad
    omega
  have hA'_ge_m : m + 100 * d ≤ A'.card := by
    have hR : (m : ℝ) + 100 * (d : ℝ) ≤ (A'.card : ℝ) := by
      have : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
      linarith
    exact_mod_cast hR
  let outA := Finset.univ \ A'
  let Ball := outA.filter (fun x => A'.card ≤ 3 * (A'.filter ((c 0).Adj x)).card)
  let Call := outA.filter (fun x => A'.card ≤ 3 * (A'.filter ((c 2).Adj x)).card)
  let Dall := outA.filter (fun x => A'.card ≤ 3 * (A'.filter ((c 1).Adj x)).card)
  have hB0_sub_Ball : B₀ ⊆ Ball := by
    intro x hx
    have hx1 : x ∈ W 1 := (Finset.mem_filter.mp hx).1
    have hxmiss : (A'.filter (fun y => ¬ (c 0).Adj x y)).card ≤ d :=
      (Finset.card_le_card (Finset.filter_subset_filter _ hA'_sub)).trans (Finset.mem_filter.mp hx).2
    have hpart := Finset.card_filter_add_card_filter_not (s := A') ((c 0).Adj x)
    have hxout : x ∈ outA := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      fun hxA => Finset.disjoint_left.mp (hdisW 0 1 (by decide)) (hA'_sub hxA) hx1⟩
    exact Finset.mem_filter.mpr ⟨hxout, by omega⟩
  have hC0_sub_Call : C₀ ⊆ Call := by
    intro x hx
    have hx2 : x ∈ W 2 := (Finset.mem_filter.mp hx).1
    have hxmiss : (A'.filter (fun y => ¬ (c 2).Adj x y)).card ≤ d :=
      (Finset.card_le_card (Finset.filter_subset_filter _ hA'_sub)).trans (Finset.mem_filter.mp hx).2
    have hpart := Finset.card_filter_add_card_filter_not (s := A') ((c 2).Adj x)
    have hxout : x ∈ outA := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      fun hxA => Finset.disjoint_left.mp (hdisW 0 2 (by decide)) (hA'_sub hxA) hx2⟩
    exact Finset.mem_filter.mpr ⟨hxout, by omega⟩
  have hD0_sub_Dall : D₀ ⊆ Dall := by
    intro x hx
    have hx3 : x ∈ W 3 := (Finset.mem_filter.mp hx).1
    have hxmiss : (A'.filter (fun y => ¬ (c 1).Adj x y)).card ≤ d :=
      (Finset.card_le_card (Finset.filter_subset_filter _ hA'_sub)).trans (Finset.mem_filter.mp hx).2
    have hpart := Finset.card_filter_add_card_filter_not (s := A') ((c 1).Adj x)
    have hxout : x ∈ outA := Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,
      fun hxA => Finset.disjoint_left.mp (hdisW 0 3 (by decide)) (hA'_sub hxA) hx3⟩
    exact Finset.mem_filter.mpr ⟨hxout, by omega⟩
  have hB0_m20 : m ≤ B₀.card + m / 20 := by
    have hR : (m : ℝ) ≤ (B₀.card : ℝ) + (m : ℝ) / 25 := by
      have : ((W 1).card : ℝ) ≤ (B₀.card : ℝ) + (d : ℝ) := by exact_mod_cast hB0_card
      linarith
    have hN : 25 * m ≤ 25 * B₀.card + m := by exact_mod_cast (by linarith : 25 * (m : ℝ) ≤ 25 * (B₀.card : ℝ) + (m : ℝ))
    omega
  have hC0_m20 : m ≤ C₀.card + m / 20 := by
    have hR : (m : ℝ) ≤ (C₀.card : ℝ) + (m : ℝ) / 25 := by
      have : ((W 2).card : ℝ) ≤ (C₀.card : ℝ) + (d : ℝ) := by exact_mod_cast hC0_card
      linarith
    have hN : 25 * m ≤ 25 * C₀.card + m := by exact_mod_cast (by linarith : 25 * (m : ℝ) ≤ 25 * (C₀.card : ℝ) + (m : ℝ))
    omega
  by_cases hBall : m ≤ Ball.card
  · refine ⟨0, h1 m d (c 0) A' B₀ Ball (by omega) hd_pos h100d
      (Finset.disjoint_sdiff.mono_right (Finset.filter_subset _ _)) hB0_sub_Ball
      (by omega) hBall hB0_m20 ?_ ?_⟩
    · intro x hx
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hA'_sub)).trans (Finset.mem_filter.mp hx).2
    · intro x hx
      have := (Finset.mem_filter.mp hx).2; omega
  by_cases hCall : m ≤ Call.card
  · refine ⟨2, h1 m d (c 2) A' C₀ Call (by omega) hd_pos h100d
      (Finset.disjoint_sdiff.mono_right (Finset.filter_subset _ _)) hC0_sub_Call
      (by omega) hCall hC0_m20 ?_ ?_⟩
    · intro x hx
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hA'_sub)).trans (Finset.mem_filter.mp hx).2
    · intro x hx
      have := (Finset.mem_filter.mp hx).2; omega
  push_neg at hBall hCall
  have hB0_lt : B₀.card < m := lt_of_le_of_lt (Finset.card_le_card hB0_sub_Ball) hBall
  have hC0_lt : C₀.card < m := lt_of_le_of_lt (Finset.card_le_card hC0_sub_Call) hCall
  have hW1_le : (W 1).card ≤ m + d := by omega
  have hW2_le : (W 2).card ≤ m + d := by omega
  have ha0_ge_high : (1 + 7 / 10 * μ) * (m : ℝ) ≤ (W 0).card := by
    have : (1 - 3 / 10 * μ) * (m : ℝ) ≤ max ((W 1).card : ℝ) ((W 2).card : ℝ) := by
      rcases le_total ((W 1).card : ℝ) ((W 2).card : ℝ) with h | h
      · rw [max_eq_right h]; linarith
      · rw [max_eq_left h]; linarith
    rcases le_total ((W 1).card : ℝ) ((W 2).card : ℝ) with h | h
    · rw [max_eq_right h] at this; linarith
    · rw [max_eq_left h] at this; linarith
  have hA'B0_sum : 2 * m + 10 * d ≤ A'.card + B₀.card := by
    have hR : 2 * (m : ℝ) + 10 * (d : ℝ) ≤ (A'.card : ℝ) + (B₀.card : ℝ) := by
      have h1' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
      have h2' : ((W 1).card : ℝ) ≤ (B₀.card : ℝ) + (d : ℝ) := by exact_mod_cast hB0_card
      have h3' : ((W 2).card : ℝ) ≤ (m : ℝ) + (d : ℝ) := by exact_mod_cast hW2_le
      linarith
    exact_mod_cast hR
  have hA'C0_sum : 2 * m + 10 * d ≤ A'.card + C₀.card := by
    have hR : 2 * (m : ℝ) + 10 * (d : ℝ) ≤ (A'.card : ℝ) + (C₀.card : ℝ) := by
      have h1' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
      have h2' : ((W 2).card : ℝ) ≤ (C₀.card : ℝ) + (d : ℝ) := by exact_mod_cast hC0_card
      have h3' : ((W 1).card : ℝ) ≤ (m : ℝ) + (d : ℝ) := by exact_mod_cast hW1_le
      linarith
    exact_mod_cast hR
  rcases exists_maximal_matching (c 0) A' (2 * (m - B₀.card)) with hm0 | ⟨M₀, hM0_sub, hM0_card, hM0_max⟩
  · refine ⟨0, h2 m d (c 0) A' B₀ (by omega) hd_pos h100d
      (Finset.disjoint_left.mpr fun x hxA hxB =>
        Finset.disjoint_left.mp (hdisW 0 1 (by decide)) (hA'_sub hxA) (Finset.mem_filter.mp hxB).1)
      hB0_lt hB0_m20 hA'B0_sum ?_ ?_ hm0⟩
    · intro x hx
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hA'_sub)).trans (Finset.mem_filter.mp hx).2
    · intro x hx
      have hx_not : x ∉ A_bad1 := fun h => (Finset.mem_sdiff.mp hx).2
        (Finset.mem_union_left _ (Finset.mem_union_left _ h))
      have hx0 : x ∈ W 0 := hA'_sub hx
      have hle : ((W 1).filter (fun y => ¬ (c 0).Adj x y)).card ≤ d := by
        by_contra hlt; push_neg at hlt
        exact hx_not (Finset.mem_filter.mpr ⟨hx0, hlt⟩)
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans hle
  rcases exists_maximal_matching (c 2) A' (2 * (m - C₀.card)) with hm2 | ⟨M₂, hM2_sub, hM2_card, hM2_max⟩
  · refine ⟨2, h2 m d (c 2) A' C₀ (by omega) hd_pos h100d
      (Finset.disjoint_left.mpr fun x hxA hxC =>
        Finset.disjoint_left.mp (hdisW 0 2 (by decide)) (hA'_sub hxA) (Finset.mem_filter.mp hxC).1)
      hC0_lt hC0_m20 hA'C0_sum ?_ ?_ hm2⟩
    · intro x hx
      exact (Finset.card_le_card (Finset.filter_subset_filter _ hA'_sub)).trans (Finset.mem_filter.mp hx).2
    · intro x hx
      have hx_not : x ∉ A_bad2 := fun h => (Finset.mem_sdiff.mp hx).2
        (Finset.mem_union_left _ (Finset.mem_union_right _ h))
      have hx0 : x ∈ W 0 := hA'_sub hx
      have hle : ((W 2).filter (fun y => ¬ (c 2).Adj x y)).card ≤ d := by
        by_contra hlt; push_neg at hlt
        exact hx_not (Finset.mem_filter.mpr ⟨hx0, hlt⟩)
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans hle
  let M := M₀ ∪ M₂
  let A'' := A' \ M
  have hM_sub : M ⊆ A' := Finset.union_subset hM0_sub hM2_sub
  have hrBC : ((m - B₀.card : ℕ) : ℝ) + ((m - C₀.card : ℕ) : ℝ) ≤
      3 / 5 * μ * (m : ℝ) + 2 * (d : ℝ) := by
    rw [Nat.cast_sub (le_of_lt hB0_lt), Nat.cast_sub (le_of_lt hC0_lt)]
    have hB : ((W 1).card : ℝ) ≤ (B₀.card : ℝ) + (d : ℝ) := by exact_mod_cast hB0_card
    have hC : ((W 2).card : ℝ) ≤ (C₀.card : ℝ) + (d : ℝ) := by exact_mod_cast hC0_card
    linarith only [hB, hC, ha12_low]
  have hBDeficit : ((m - B₀.card : ℕ) : ℝ) ≤ 3 / 5 * μ * (m : ℝ) + 2 * (d : ℝ) := by
    linarith only [hrBC, Nat.cast_nonneg (α := ℝ) (m - C₀.card)]
  have hCDeficit : ((m - C₀.card : ℕ) : ℝ) ≤ 3 / 5 * μ * (m : ℝ) + 2 * (d : ℝ) := by
    linarith only [hrBC, Nat.cast_nonneg (α := ℝ) (m - B₀.card)]
  have hM_card : (M.card : ℝ) ≤ 12 / 5 * μ * (m : ℝ) + 8 * (d : ℝ) := by
    have h1' : M.card ≤ 4 * (m - B₀.card) + 4 * (m - C₀.card) := by
      have hUnion : M.card ≤ M₀.card + M₂.card := Finset.card_union_le M₀ M₂
      omega
    have h2' : (M.card : ℝ) ≤ 4 * ((m - B₀.card : ℕ) : ℝ) + 4 * ((m - C₀.card : ℕ) : ℝ) := by
      exact_mod_cast h1'
    linarith only [h2', hrBC]
  have hA''_card_add : A''.card + M.card = A'.card := Finset.card_sdiff_add_card_eq_card hM_sub
  have hA''_90 : 9 * m ≤ 10 * A''.card := by
    have hR : 9 * (m : ℝ) ≤ 10 * (A''.card : ℝ) := by
      have h1' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
      have h2' : (A''.card : ℝ) + (M.card : ℝ) = (A'.card : ℝ) := by exact_mod_cast hA''_card_add
      linarith
    exact_mod_cast hR
  let X₀ := M.filter (fun x => A''.card ≤ 3 * (A''.filter ((c 0).Adj x)).card)
  let X₂ := M.filter (fun x => A''.card ≤ 3 * (A''.filter ((c 2).Adj x)).card)
  let Q := M \ (X₀ ∪ X₂)
  by_cases hBX0 : m ≤ Ball.card + X₀.card
  · obtain ⟨X₀', hX0'_sub, hX0'_card⟩ := Finset.exists_subset_card_eq (show m - Ball.card ≤ X₀.card by omega)
    have hX0'_A' : X₀' ⊆ A' := hX0'_sub.trans ((Finset.filter_subset _ _).trans hM_sub)
    have hX0'_disj_A'' : Disjoint X₀' A'' :=
      Finset.disjoint_left.mpr fun x hx hA'' => (Finset.mem_sdiff.mp hA'').2
        (Finset.mem_filter.mp (hX0'_sub hx)).1
    have hdisj_BX : Disjoint Ball X₀' :=
      Finset.disjoint_left.mpr fun x hxB hxX => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hxB).1).2 (hX0'_A' hxX)
    have hArem_card : m + 10 * d ≤ (A' \ X₀').card := by
      have hsub := Finset.card_sdiff_add_card_eq_card hX0'_A'
      have hR : (m : ℝ) + 10 * (d : ℝ) ≤ ((A' \ X₀').card : ℝ) := by
        have h1' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
        have h2' : ((A' \ X₀').card : ℝ) + (X₀'.card : ℝ) = (A'.card : ℝ) := by exact_mod_cast hsub
        have h3' : (X₀'.card : ℝ) ≤ ((m - B₀.card : ℕ) : ℝ) := by
          have : B₀.card ≤ Ball.card := Finset.card_le_card hB0_sub_Ball
          exact_mod_cast (show X₀'.card ≤ m - B₀.card by omega)
        have h4' : ((m - B₀.card : ℕ) : ℝ) ≤ 3 / 5 * μ * (m : ℝ) + 2 * (d : ℝ) := hBDeficit
        linarith
      exact_mod_cast hR
    refine ⟨0, h1 m d (c 0) (A' \ X₀') B₀ (Ball ∪ X₀') (by omega) hd_pos h100d
      (Finset.disjoint_union_right.mpr ⟨Finset.disjoint_sdiff.mono Finset.sdiff_subset (Finset.filter_subset _ _),
        Finset.sdiff_disjoint⟩)
      (hB0_sub_Ball.trans Finset.subset_union_left) hArem_card
      (by rw [Finset.card_union_of_disjoint hdisj_BX]; omega) hB0_m20 ?_ ?_⟩
    · intro x hx
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.sdiff_subset.trans hA'_sub))).trans
        (Finset.mem_filter.mp hx).2
    · intro x hx
      rcases Finset.mem_union.mp hx with hxB | hxX
      · have hdeg := (Finset.mem_filter.mp hxB).2
        have hdiff : (A'.filter ((c 0).Adj x)).card ≤ ((A' \ X₀').filter ((c 0).Adj x)).card + X₀'.card := by
          have hsub : A'.filter ((c 0).Adj x) ⊆ (A' \ X₀').filter ((c 0).Adj x) ∪ X₀' := by
            intro y hy
            by_cases hyX : y ∈ X₀'
            · exact Finset.mem_union_right _ hyX
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
                ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hy).1, hyX⟩, (Finset.mem_filter.mp hy).2⟩)
          exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have hsubA := Finset.card_sdiff_add_card_eq_card hX0'_A'
        have hX0'_small : 12 * X₀'.card ≤ A'.card := by
          have hR : 12 * (X₀'.card : ℝ) ≤ (A'.card : ℝ) := by
            have h1' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
            have h2' : (X₀'.card : ℝ) ≤ ((m - B₀.card : ℕ) : ℝ) := by
              have : B₀.card ≤ Ball.card := Finset.card_le_card hB0_sub_Ball
              exact_mod_cast (show X₀'.card ≤ m - B₀.card by omega)
            have h3' : ((m - B₀.card : ℕ) : ℝ) ≤ 3 / 5 * μ * (m : ℝ) + 2 * (d : ℝ) := hBDeficit
            linarith
          exact_mod_cast hR
        omega
      · have hdeg := (Finset.mem_filter.mp (hX0'_sub hxX)).2
        have hA''_sub : A'' ⊆ A' \ X₀' := Finset.subset_sdiff.mpr ⟨Finset.sdiff_subset, hX0'_disj_A''.symm⟩
        have hmono : (A''.filter ((c 0).Adj x)).card ≤ ((A' \ X₀').filter ((c 0).Adj x)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ hA''_sub)
        have hA'le : 3 * (A' \ X₀').card ≤ 4 * A''.card := by
          have hR : 3 * ((A' \ X₀').card : ℝ) ≤ 4 * (A''.card : ℝ) := by
            have h1' : (A' \ X₀').card ≤ A'.card := Finset.card_le_card Finset.sdiff_subset
            have h2' : (A''.card : ℝ) + (M.card : ℝ) = (A'.card : ℝ) := by exact_mod_cast hA''_card_add
            have h3' : ((A' \ X₀').card : ℝ) ≤ (A'.card : ℝ) := by exact_mod_cast h1'
            have h4' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
            linarith
          exact_mod_cast hR
        omega
  by_cases hCX2 : m ≤ Call.card + X₂.card
  · obtain ⟨X₂', hX2'_sub, hX2'_card⟩ := Finset.exists_subset_card_eq (show m - Call.card ≤ X₂.card by omega)
    have hX2'_A' : X₂' ⊆ A' := hX2'_sub.trans ((Finset.filter_subset _ _).trans hM_sub)
    have hX2'_disj_A'' : Disjoint X₂' A'' :=
      Finset.disjoint_left.mpr fun x hx hA'' => (Finset.mem_sdiff.mp hA'').2
        (Finset.mem_filter.mp (hX2'_sub hx)).1
    have hdisj_CX : Disjoint Call X₂' :=
      Finset.disjoint_left.mpr fun x hxC hxX => (Finset.mem_sdiff.mp (Finset.mem_filter.mp hxC).1).2 (hX2'_A' hxX)
    have hArem_card : m + 10 * d ≤ (A' \ X₂').card := by
      have hsub := Finset.card_sdiff_add_card_eq_card hX2'_A'
      have hR : (m : ℝ) + 10 * (d : ℝ) ≤ ((A' \ X₂').card : ℝ) := by
        have h1' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
        have h2' : ((A' \ X₂').card : ℝ) + (X₂'.card : ℝ) = (A'.card : ℝ) := by exact_mod_cast hsub
        have h3' : (X₂'.card : ℝ) ≤ ((m - C₀.card : ℕ) : ℝ) := by
          have : C₀.card ≤ Call.card := Finset.card_le_card hC0_sub_Call
          exact_mod_cast (show X₂'.card ≤ m - C₀.card by omega)
        have h4' : ((m - C₀.card : ℕ) : ℝ) ≤ 3 / 5 * μ * (m : ℝ) + 2 * (d : ℝ) := hCDeficit
        linarith
      exact_mod_cast hR
    refine ⟨2, h1 m d (c 2) (A' \ X₂') C₀ (Call ∪ X₂') (by omega) hd_pos h100d
      (Finset.disjoint_union_right.mpr ⟨Finset.disjoint_sdiff.mono Finset.sdiff_subset (Finset.filter_subset _ _),
        Finset.sdiff_disjoint⟩)
      (hC0_sub_Call.trans Finset.subset_union_left) hArem_card
      (by rw [Finset.card_union_of_disjoint hdisj_CX]; omega) hC0_m20 ?_ ?_⟩
    · intro x hx
      exact (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.sdiff_subset.trans hA'_sub))).trans
        (Finset.mem_filter.mp hx).2
    · intro x hx
      rcases Finset.mem_union.mp hx with hxC | hxX
      · have hdeg := (Finset.mem_filter.mp hxC).2
        have hdiff : (A'.filter ((c 2).Adj x)).card ≤ ((A' \ X₂').filter ((c 2).Adj x)).card + X₂'.card := by
          have hsub : A'.filter ((c 2).Adj x) ⊆ (A' \ X₂').filter ((c 2).Adj x) ∪ X₂' := by
            intro y hy
            by_cases hyX : y ∈ X₂'
            · exact Finset.mem_union_right _ hyX
            · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
                ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hy).1, hyX⟩, (Finset.mem_filter.mp hy).2⟩)
          exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
        have hsubA := Finset.card_sdiff_add_card_eq_card hX2'_A'
        have hX2'_small : 12 * X₂'.card ≤ A'.card := by
          have hR : 12 * (X₂'.card : ℝ) ≤ (A'.card : ℝ) := by
            have h1' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
            have h2' : (X₂'.card : ℝ) ≤ ((m - C₀.card : ℕ) : ℝ) := by
              have : C₀.card ≤ Call.card := Finset.card_le_card hC0_sub_Call
              exact_mod_cast (show X₂'.card ≤ m - C₀.card by omega)
            have h3' : ((m - C₀.card : ℕ) : ℝ) ≤ 3 / 5 * μ * (m : ℝ) + 2 * (d : ℝ) := hCDeficit
            linarith
          exact_mod_cast hR
        omega
      · have hdeg := (Finset.mem_filter.mp (hX2'_sub hxX)).2
        have hA''_sub : A'' ⊆ A' \ X₂' := Finset.subset_sdiff.mpr ⟨Finset.sdiff_subset, hX2'_disj_A''.symm⟩
        have hmono : (A''.filter ((c 2).Adj x)).card ≤ ((A' \ X₂').filter ((c 2).Adj x)).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ hA''_sub)
        have hA'le : 3 * (A' \ X₂').card ≤ 4 * A''.card := by
          have hR : 3 * ((A' \ X₂').card : ℝ) ≤ 4 * (A''.card : ℝ) := by
            have h1' : (A' \ X₂').card ≤ A'.card := Finset.card_le_card Finset.sdiff_subset
            have h2' : (A''.card : ℝ) + (M.card : ℝ) = (A'.card : ℝ) := by exact_mod_cast hA''_card_add
            have h3' : ((A' \ X₂').card : ℝ) ≤ (A'.card : ℝ) := by exact_mod_cast h1'
            have h4' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
            linarith
          exact_mod_cast hR
        omega
  push_neg at hBX0 hCX2
  have houtA_cover : outA ⊆ Ball ∪ Call ∪ Dall := by
    intro x hx
    have hxA : x ∉ A' := (Finset.mem_sdiff.mp hx).2
    have hcov : A' ⊆ A'.filter ((c 0).Adj x) ∪ A'.filter ((c 2).Adj x) ∪ A'.filter ((c 1).Adj x) := by
      intro y hy
      have hne : x ≠ y := fun h => hxA (h ▸ hy)
      have hedge : (⊤ : SimpleGraph (Fin (4 * m))).Adj x y := hne
      rw [hc.1, SimpleGraph.iSup_adj] at hedge
      obtain ⟨k, hk⟩ := hedge
      fin_cases k
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hy, hk⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy, hk⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy, hk⟩))
    have hsum := (Finset.card_le_card hcov).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    by_cases h0 : A'.card ≤ 3 * (A'.filter ((c 0).Adj x)).card
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hx, h0⟩))
    by_cases h2 : A'.card ≤ 3 * (A'.filter ((c 2).Adj x)).card
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, h2⟩))
    exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx, by omega⟩)
  have h4m_sum : A'.card + outA.card = 4 * m := by
    have := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ A')
    change outA.card + A'.card = _ at this
    simpa only [Nat.add_comm A'.card outA.card, Finset.card_univ, Fintype.card_fin] using this
  have hQ_card : A'.card ≤ A''.card + Q.card + X₀.card + X₂.card := by
    have h1' := Finset.card_sdiff_add_card_eq_card (Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _) : X₀ ∪ X₂ ⊆ M)
    change Q.card + _ = _ at h1'
    have h2' := Finset.card_union_le X₀ X₂
    omega
  have htotal_green : 2 * m ≤ A''.card + Q.card + Dall.card := by
    have h1' := (Finset.card_le_card houtA_cover).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    omega
  have hAQ_ge : m + 10 * d ≤ A''.card + Q.card := by
    have hR : (m : ℝ) + 10 * (d : ℝ) ≤ (A''.card : ℝ) + (Q.card : ℝ) := by
      have h1' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
      have h2' : (A'.card : ℝ) ≤ (A''.card : ℝ) + (Q.card : ℝ) + (X₀.card : ℝ) + (X₂.card : ℝ) := by
        exact_mod_cast hQ_card
      have h3' : (X₀.card : ℝ) + (X₂.card : ℝ) ≤ ((m - B₀.card : ℕ) : ℝ) + ((m - C₀.card : ℕ) : ℝ) := by
        have hb : B₀.card ≤ Ball.card := Finset.card_le_card hB0_sub_Ball
        have hc' : C₀.card ≤ Call.card := Finset.card_le_card hC0_sub_Call
        exact_mod_cast (show X₀.card + X₂.card ≤ (m - B₀.card) + (m - C₀.card) by omega)
      linarith
    exact_mod_cast hR
  have hAD0_ge : m + 10 * d ≤ A''.card + D₀.card := by
    have hTotal : ((W 0).card : ℝ) + ((W 1).card : ℝ) +
        ((W 2).card : ℝ) + ((W 3).card : ℝ) = 4 * (m : ℝ) := by exact_mod_cast hsumW
    have hCleanA : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
    have hMatching : (A''.card : ℝ) + (M.card : ℝ) = (A'.card : ℝ) := by exact_mod_cast hA''_card_add
    have hW1 : ((W 1).card : ℝ) ≤ (m : ℝ) + (d : ℝ) := by exact_mod_cast hW1_le
    have hW2 : ((W 2).card : ℝ) ≤ (m : ℝ) + (d : ℝ) := by exact_mod_cast hW2_le
    have hCleanD : ((W 3).card : ℝ) ≤ (D₀.card : ℝ) + (d : ℝ) := by exact_mod_cast hD0_card
    have hR : (m : ℝ) + 10 * (d : ℝ) ≤ (A''.card : ℝ) + (D₀.card : ℝ) := by
      linarith only [hTotal, hCleanA, hMatching, hW1, hW2, hCleanD, hM_card, hd_upper, hμm_upper]
    exact_mod_cast hR
  have hDall_le : Dall.card ≤ D₀.card + 10 * d := by
    have hsub : Dall \ D₀ ⊆ (W 0 \ A') ∪ (W 1 \ B₀) ∪ (W 2 \ C₀) ∪ (W 3 \ D₀) := by
      intro x hx
      have hxDall : x ∈ Dall := (Finset.mem_sdiff.mp hx).1
      have hxnotD0 : x ∉ D₀ := (Finset.mem_sdiff.mp hx).2
      have hxout : x ∈ outA := (Finset.mem_filter.mp hxDall).1
      have hxnotA' : x ∉ A' := (Finset.mem_sdiff.mp hxout).2
      have hxdeg1 : A'.card ≤ 3 * (A'.filter ((c 1).Adj x)).card := (Finset.mem_filter.mp hxDall).2
      have hcase : x ∈ W 0 ∨ x ∈ W 1 ∨ x ∈ W 2 ∨ x ∈ W 3 := by
        simp only [W, Finset.mem_filter, Finset.mem_univ, true_and]
        generalize f x = j
        fin_cases j <;> decide
      rcases hcase with hx0 | hx1 | hx2 | hx3
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hx0, hxnotA'⟩)))
      · refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx1, fun hxB0 => ?_⟩)))
        have hmiss : (A'.filter (fun y => ¬ (c 0).Adj x y)).card ≤ d :=
          (Finset.card_le_card (Finset.filter_subset_filter _ hA'_sub)).trans (Finset.mem_filter.mp hxB0).2
        have hdisj01 : A'.filter ((c 1).Adj x) ⊆ A'.filter (fun y => ¬ (c 0).Adj x y) := by
          intro y hy
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, fun h0 =>
            SimpleGraph.disjoint_left.mp (hc.2 0 1 (by decide)) x y h0 (Finset.mem_filter.mp hy).2⟩
        have := Finset.card_le_card hdisj01
        omega
      · refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx2, fun hxC0 => ?_⟩))
        have hmiss : (A'.filter (fun y => ¬ (c 2).Adj x y)).card ≤ d :=
          (Finset.card_le_card (Finset.filter_subset_filter _ hA'_sub)).trans (Finset.mem_filter.mp hxC0).2
        have hdisj21 : A'.filter ((c 1).Adj x) ⊆ A'.filter (fun y => ¬ (c 2).Adj x y) := by
          intro y hy
          exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hy).1, fun h2 =>
            SimpleGraph.disjoint_left.mp (hc.2 2 1 (by decide)) x y h2 (Finset.mem_filter.mp hy).2⟩
        have := Finset.card_le_card hdisj21
        omega
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hx3, hxnotD0⟩)
    have h1' := Finset.card_sdiff_add_card_eq_card hD0_sub_Dall
    have h2' := (Finset.card_le_card hsub).trans ((Finset.card_union_le _ _).trans
      (Nat.add_le_add_right ((Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)) _))
    have hs0 := Finset.card_sdiff_add_card_eq_card hA'_sub
    have hs1 := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ (W 1) : B₀ ⊆ W 1)
    have hs2 := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ (W 2) : C₀ ⊆ W 2)
    have hs3 := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ (W 3) : D₀ ⊆ W 3)
    change (W 1 \ B₀).card + B₀.card = (W 1).card at hs1
    change (W 2 \ C₀).card + C₀.card = (W 2).card at hs2
    change (W 3 \ D₀).card + D₀.card = (W 3).card at hs3
    omega
  have hMsmall : 12 * M.card ≤ A''.card := by
    have hR : 12 * (M.card : ℝ) ≤ (A''.card : ℝ) := by
      have h1' : ((W 0).card : ℝ) ≤ (A'.card : ℝ) + 3 * (d : ℝ) := by exact_mod_cast hA'_card
      have h2' : (A''.card : ℝ) + (M.card : ℝ) = (A'.card : ℝ) := by exact_mod_cast hA''_card_add
      linarith
    exact_mod_cast hR
  have hQsmall : 12 * Q.card ≤ A''.card :=
    (Nat.mul_le_mul_left 12
      (Finset.card_le_card (Finset.sdiff_subset : Q ⊆ M))).trans hMsmall
  refine ⟨1, h3 m d (c 1) A'' Q D₀ Dall (by omega) hd_pos h100d
    (Finset.sdiff_disjoint.mono_right Finset.sdiff_subset)
    (Finset.disjoint_sdiff.mono Finset.sdiff_subset (Finset.filter_subset _ _))
    (Finset.disjoint_sdiff.mono (Finset.sdiff_subset.trans hM_sub) (Finset.filter_subset _ _))
    hD0_sub_Dall hDall_le ?_ hA''_90 hQsmall htotal_green hAQ_ge hAD0_ge ?_ ?_ ?_⟩
  · intro x hx y hy hne
    have hxM0 : x ∈ A' \ M₀ := Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,
      fun h => (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _ h)⟩
    have hyM0 : y ∈ A' \ M₀ := Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hy).1,
      fun h => (Finset.mem_sdiff.mp hy).2 (Finset.mem_union_left _ h)⟩
    have hxM2 : x ∈ A' \ M₂ := Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1,
      fun h => (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_right _ h)⟩
    have hyM2 : y ∈ A' \ M₂ := Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hy).1,
      fun h => (Finset.mem_sdiff.mp hy).2 (Finset.mem_union_right _ h)⟩
    have hno0 : ¬ (c 0).Adj x y := hM0_max x hxM0 y hyM0
    have hno2 : ¬ (c 2).Adj x y := hM2_max x hxM2 y hyM2
    have hedge : (⊤ : SimpleGraph (Fin (4 * m))).Adj x y := hne
    rw [hc.1, SimpleGraph.iSup_adj] at hedge
    obtain ⟨k, hk⟩ := hedge
    fin_cases k
    · exact (hno0 hk).elim
    · exact hk
    · exact (hno2 hk).elim
  · intro q hq
    have hqM : q ∈ M := (Finset.mem_sdiff.mp hq).1
    have hqnot : q ∉ X₀ ∪ X₂ := (Finset.mem_sdiff.mp hq).2
    have hqA' : q ∈ A' := hM_sub hqM
    have hqnotA'' : q ∉ A'' := fun h => (Finset.mem_sdiff.mp h).2 hqM
    have hcov : A'' ⊆ A''.filter ((c 0).Adj q) ∪ A''.filter ((c 2).Adj q) ∪ A''.filter ((c 1).Adj q) := by
      intro y hy
      have hne : q ≠ y := fun h => hqnotA'' (h ▸ hy)
      have hedge : (⊤ : SimpleGraph (Fin (4 * m))).Adj q y := hne
      rw [hc.1, SimpleGraph.iSup_adj] at hedge
      obtain ⟨k, hk⟩ := hedge
      fin_cases k
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hy, hk⟩))
      · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy, hk⟩)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hy, hk⟩))
    have hsum := (Finset.card_le_card hcov).trans
      ((Finset.card_union_le _ _).trans (Nat.add_le_add_right (Finset.card_union_le _ _) _))
    have h0lt : 3 * (A''.filter ((c 0).Adj q)).card < A''.card := by
      by_contra hge; push_neg at hge
      exact hqnot (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hqM, hge⟩))
    have h2lt : 3 * (A''.filter ((c 2).Adj q)).card < A''.card := by
      by_contra hge; push_neg at hge
      exact hqnot (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hqM, hge⟩))
    have hqnot3 : q ∉ A_bad3 := fun h => (Finset.mem_sdiff.mp hqA').2 (Finset.mem_union_right _ h)
    have hqmiss : ((W 3).filter (fun y => ¬ (c 1).Adj q y)).card ≤ d := by
      by_contra hlt; push_neg at hlt
      exact hqnot3 (Finset.mem_filter.mpr ⟨hA'_sub hqA', hlt⟩)
    exact ⟨by omega, (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.filter_subset _ _))).trans hqmiss⟩
  · intro x hx
    have hxmiss : ((W 0).filter (fun y => ¬ (c 1).Adj x y)).card ≤ d := (Finset.mem_filter.mp hx).2
    exact ⟨(Finset.card_le_card (Finset.filter_subset_filter _ ((Finset.sdiff_subset.trans hM_sub).trans hA'_sub))).trans hxmiss,
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.sdiff_subset.trans hA'_sub))).trans hxmiss⟩
  · intro x hx
    have hdeg := (Finset.mem_filter.mp hx).2
    have hdiff : (A'.filter ((c 1).Adj x)).card ≤ (A''.filter ((c 1).Adj x)).card + M.card := by
      have hsub : A'.filter ((c 1).Adj x) ⊆ A''.filter ((c 1).Adj x) ∪ M := by
        intro y hy
        by_cases hyM : y ∈ M
        · exact Finset.mem_union_right _ hyM
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨Finset.mem_sdiff.mpr ⟨(Finset.mem_filter.mp hy).1, hyM⟩, (Finset.mem_filter.mp hy).2⟩)
      exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
    omega

end

end OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R1_H3_R1



theorem OMA.solution :
    OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R3.H3 := by
  apply OMA.R_Erdos556_erdos_556_variants_benevides_skokan_large_even_R1_H3_R1.main
  · intro m d G _ A B₀ B
    exact EC3DenseJoinProof.dense_bipartite_cycle_with_exceptions m d G A B₀ B
  · intro m d G _ A B₀
    exact EC3Matching.matching_spliced_cycle m d G A B₀
  · intro m d G _ A Q D₀ D hm hd hmd hAQ hAD hQD hD₀D hDsize hclique
      hAsize hQsize htotal hTsize _hAD₀
    exact EC3RepairedAbsorption.repaired_clique_absorption m d G A Q D₀ D
      hm hd hmd hAQ hAD hQD hD₀D hDsize hclique hAsize hQsize htotal hTsize
