import FormalConjectures.Arxiv.«2605.02731».DeanCycles
import Mathlib
/-! Proof of Dean's conjecture for k=5. -/
section M0
namespace DeanK5
open SimpleGraph
def Kc0 {V : Type} [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ S : Finset V,S.card < k →
      (G.induce ((S : Set V)ᶜ)).Connected
def Rt0 {V : Type} [Fintype V] (G : SimpleGraph V) (x y : V) : Prop :=
  x≠y∧Kc0 (G ⊔ SimpleGraph.edge x y) 2
def Adm0 {V : Type} (G : SimpleGraph V) (x y : V) (q : ℕ) : Prop :=
  ∃ a d : ℕ,2≤ a∧(d=1∨d=2) ∧
    ∀ i : Fin q,∃ p : G.Walk x y,p.IsPath∧p.length=a+i.val*d
def qal2 {V : Type} (G : SimpleGraph V) (x y : V) (q : ℕ) : Prop :=
  ∃ a d : ℕ,1≤ a∧(d=1∨d=2) ∧
    ∀ i : Fin q,∃ p : G.Walk x y,p.IsPath∧p.length=a+i.val*d
def COY4 : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x y : V) (z : Option V) (q : ℕ),
    1≤ q→ q≤ 4→ Rt0 G x y →
    (∃ v : V,v≠x∧v≠y∧z≠some v) →
    (∀ v : V,v≠x→ v≠y→ z≠some v→ q+1≤ G.degree v) →
    Adm0 G x y q
def Nf0 {V : Type} (G : SimpleGraph V) : Prop :=
  ∀ v : V,∀ w : G.Walk v v,w.IsCycle→ ¬ 5∣w.length
variable {V W : Type} {G : SimpleGraph V}
theorem qf7 {v : V} {w : G.Walk v v} (hw : w.IsCycle) :
    w.length∈G.cycleLengths :=
  ⟨v,w,hw,rfl⟩
theorem noFive_iff_cycleLengths : Nf0 G↔∀ m∈G.cycleLengths,¬ 5∣m:=by
  constructor
  · rintro h m ⟨v,w,hw,rfl⟩
    exact h v w hw
  · intro h v w hw
    exact h _ (qf7 hw)
theorem qaf7 {H : SimpleGraph W} (f : H →g G) (hf : Function.Injective f)
    (hG : Nf0 G) : Nf0 H:=by
  intro v w hw
  have h:=hG (f v) (w.map f) ((Walk.isCycle_map_iff_of_injective hf).mpr hw)
  rwa [Walk.length_map] at h
theorem qaa4 {H : SimpleGraph W} (f : H ↪g G) (hG : Nf0 G) : Nf0 H :=
  qaf7 f.toHom f.injective hG
theorem qaq7 {H : SimpleGraph V} (h : H≤ G) (hG : Nf0 G) : Nf0 H :=
  qaf7 (SimpleGraph.Hom.ofLE h) (fun _ _ hab=>hab) hG
theorem qk1 (s : Set V) (hG : Nf0 G) : Nf0 (G.induce s) :=
  qaa4 (SimpleGraph.Embedding.induce s) hG
theorem qb8 {H : SimpleGraph W} (f : G →g H) (hf : Function.Injective f)
    {u v : V} {p : G.Walk u v} (hp : p.IsPath) : (p.map f).IsPath :=
  (Walk.isPath_map_iff_of_injective hf).mpr hp
theorem qan9 {H : SimpleGraph W} (f : G →g H) (hf : Function.Injective f)
    {u : V} {p : G.Walk u u} (hp : p.IsCycle) : (p.map f).IsCycle :=
  (Walk.isCycle_map_iff_of_injective hf).mpr hp
theorem qao0 {H : SimpleGraph W} (f : G →g H) {u v : V} (p : G.Walk u v) :
    (p.map f).length=p.length :=
  Walk.length_map f p
theorem qan8 {H : SimpleGraph W} (f : G →g H) {u v : V} (p : G.Walk u v) :
    (p.map f).support=p.support.map f :=
  Walk.support_map f p
theorem qd3 (s : Set V) {u v : s} {p : (G.induce s).Walk u v}
    (hp : p.IsPath) :
    ∃ q : G.Walk u v,q.IsPath∧q.length=p.length ∧
      q.support=p.support.map Subtype.val∧∀ a∈q.support,a∈s:=by
  let e : G.induce s ↪g G:=SimpleGraph.Embedding.induce s
  obtain ⟨q,hq,hl,hs⟩ : ∃ q : G.Walk u v,q.IsPath∧q.length=p.length ∧
      q.support=p.support.map Subtype.val :=
    ⟨p.map e.toHom,qb8 _ e.injective hp,Walk.length_map _ _,
      Walk.support_map _ _⟩
  refine ⟨q,hq,hl,hs,fun a ha=>?_⟩
  rw [hs,List.mem_map] at ha
  obtain ⟨b,-,rfl⟩:=ha
  exact b.property
theorem qaj7 (s : Set V) {u v : V} {q : G.Walk u v} (hq : q.IsPath)
    (hs : ∀ a∈q.support,a∈s) :
    (q.induce s hs).IsPath∧(q.induce s hs).length=q.length:=by
  have h:=Walk.map_induce q hs
  refine ⟨Walk.IsPath.of_map (f:=(SimpleGraph.Embedding.induce s).toHom) ?_,?_⟩
  · rw [h]
    exact hq
  · exact (Walk.length_map _ _).symm.trans (congrArg Walk.length h)
theorem qy4 {u v : V} (h : G.Reachable u v) : ∃ p : G.Walk u v,p.IsPath :=
  h.exists_isPath
theorem qz1 {u v : V} (w : G.Walk u v) :
    ∃ p : G.Walk u v,p.IsPath∧p.support⊆w.support∧p.length≤ w.length:=by
  classical
  exact ⟨w.bypass,w.bypass_isPath,w.support_bypass_subset_support,
    w.length_bypass_le_length⟩
theorem qo4 [Fintype V] {x y : V} (h : Rt0 G x y) : Rt0 G y x:=by
  obtain ⟨hne,hk⟩:=h
  refine ⟨hne.symm,?_⟩
  rwa [SimpleGraph.edge_comm]
theorem qn4 {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    u∉p.support.tail∧p.support.tail.Nodup:=by
  have h:=hp.support_nodup
  rw [← Walk.cons_tail_support] at h
  exact List.nodup_cons.mp h
theorem qd0 {u v : V} {p : G.Walk u v} (hp : p.IsPath) :
    u∉p.support.tail :=
  (qn4 hp).1
theorem qg5 {u v w : V} {p : G.Walk u v} (hw : w∈p.support)
    (hu : w≠u) (hv : w≠v) : w∈p.support.tail.dropLast:=by
  cases p with
  | nil =>
    rw [Walk.support_nil,List.mem_singleton] at hw
    exact absurd hw hu
  | cons h p' =>
    rw [Walk.support_cons,List.mem_cons] at hw
    rw [Walk.support_cons,List.tail_cons]
    rcases hw with rfl|hw
    · exact absurd rfl hu
    · rw [← Walk.dropLast_support_concat,List.mem_append,List.mem_singleton] at hw
      exact hw.resolve_right hv
theorem qa3 {u v w : V} {p : G.Walk u v} {q : G.Walk v w}
    (hp : p.IsPath) (hq : q.IsPath) (hpq : ∀ a,a∈p.support→ a∈q.support→ a=v) :
    (p.append q).IsPath∧(p.append q).length=p.length+q.length ∧
      (p.append q).support=p.support ++ q.support.tail:=by
  refine ⟨?_,Walk.length_append p q,Walk.support_append p q⟩
  rw [Walk.isPath_def,Walk.support_append,List.nodup_append']
  refine ⟨hp.support_nodup,(qn4 hq).2,?_⟩
  intro a ha hb
  have hav:=hpq a ha (List.mem_of_mem_tail hb)
  subst hav
  exact qd0 hq hb
theorem qf0 {u v w : V} (h : G.Adj u v) {p : G.Walk v w}
    (hp : p.IsPath) (hu : u∉p.support) :
    (Walk.cons h p).IsPath∧(Walk.cons h p).length=p.length+1 :=
  ⟨(Walk.cons_isPath_iff h p).mpr ⟨hp,hu⟩,Walk.length_cons h p⟩
theorem qn6 {u v w : V} {p : G.Walk u v} (hp : p.IsPath)
    (h : G.Adj v w) (hw : w∉p.support) :
    (p.concat h).IsPath∧(p.concat h).length=p.length+1 :=
  ⟨hp.concat hw h,Walk.length_concat p h⟩
theorem qn1 {x y : V} {p q : G.Walk x y} (hp : p.IsPath) (hq : q.IsPath)
    (hint : ∀ v,v∈p.support→ v∈q.support→ v=x∨v=y)
    (hlen : 3≤ p.length+q.length) :
    (p.append q.reverse).IsCycle∧p.length+q.length∈G.cycleLengths:=by
  have hc : (p.append q.reverse).IsCycle:=by
    refine hp.isCycle_append hq.reverse ?_ ?_
    · intro v hv1 hv2
      have hv2' : v∈q.support:=by
        have h:=List.mem_of_mem_tail hv2
        rwa [Walk.support_reverse,List.mem_reverse] at h
      rcases hint v (List.mem_of_mem_tail hv1) hv2' with rfl|rfl
      · exact qd0 hp hv1
      · exact qd0 hq.reverse hv2
    · rw [Walk.length_reverse]
      omega
  refine ⟨hc,?_⟩
  have h:=qf7 hc
  rwa [Walk.length_append,Walk.length_reverse] at h
theorem qah4 {x y : V} {p q : G.Walk x y} (hp : p.IsPath)
    (hq : q.IsPath) (hd : List.Disjoint p.support.tail.dropLast q.support.tail.dropLast)
    (hlen : 3≤ p.length+q.length) :
    (p.append q.reverse).IsCycle∧p.length+q.length∈G.cycleLengths:=by
  refine qn1 hp hq (fun v hv1 hv2=>?_) hlen
  by_contra hne
  obtain ⟨hx,hy⟩:=not_or.mp hne
  exact hd (qg5 hv1 hx hy) (qg5 hv2 hx hy)
theorem qc4 (hG : Nf0 G) {x y : V} {p q : G.Walk x y} (hp : p.IsPath)
    (hq : q.IsPath) (hint : ∀ v,v∈p.support→ v∈q.support→ v=x∨v=y)
    (hlen : 3≤ p.length+q.length) : ¬ 5∣p.length+q.length :=
  noFive_iff_cycleLengths.mp hG _ (qn1 hp hq hint hlen).2
theorem qq4 {d : ℕ} (hd : d=1∨d=2) (a : ℕ) :
    ∃ i : Fin 5,5∣a+i.val*d:=by
  rcases hd with rfl|rfl
  · exact ⟨⟨(5 - a % 5) % 5,by omega⟩,by dsimp only;omega⟩
  · exact ⟨⟨(5 - a % 5)*3 % 5,by omega⟩,by dsimp only;omega⟩
theorem qai8 {p q d₁ d₂ : ℕ} (hp : 1≤ p) (hq : 1≤ q)
    (hd₁ : d₁=1∨d₁=2) (hd₂ : d₂=1∨d₂=2) :
    ∃ d : ℕ,(d=1∨d=2)∧∀ k : ℕ,k < p+q - 1 →
      ∃ i j : ℕ,i < p∧j < q∧i*d₁+j*d₂=k*d:=by
  rcases hd₁ with rfl|rfl <;> rcases hd₂ with rfl|rfl
  · refine ⟨1,Or.inl rfl,fun k hk=>?_⟩
    by_cases h : k < p
    · exact ⟨k,0,h,hq,by omega⟩
    · exact ⟨p - 1,k - (p - 1),by omega,by omega,by omega⟩
  · by_cases hp1 : p=1
    · subst hp1
      exact ⟨2,Or.inr rfl,fun k hk=>⟨0,k,by omega,by omega,by omega⟩⟩
    · refine ⟨1,Or.inl rfl,fun k hk=>?_⟩
      by_cases h : k / 2 < q
      · exact ⟨k % 2,k / 2,by omega,h,by omega⟩
      · exact ⟨k - 2*(q - 1),q - 1,by omega,by omega,by omega⟩
  · by_cases hq1 : q=1
    · subst hq1
      exact ⟨2,Or.inr rfl,fun k hk=>⟨k,0,by omega,by omega,by omega⟩⟩
    · refine ⟨1,Or.inl rfl,fun k hk=>?_⟩
      by_cases h : k / 2 < p
      · exact ⟨k / 2,k % 2,h,by omega,by omega⟩
      · exact ⟨p - 1,k - 2*(p - 1),by omega,by omega,by omega⟩
  · refine ⟨2,Or.inr rfl,fun k hk=>?_⟩
    by_cases h : k < p
    · exact ⟨k,0,h,hq,by omega⟩
    · exact ⟨p - 1,k - (p - 1),by omega,by omega,by omega⟩
theorem qi9 {p q d₁ d₂ : ℕ} (hp : 1≤ p) (hq : 1≤ q)
    (hd₁ : d₁=1∨d₁=2) (hd₂ : d₂=1∨d₂=2) (a₁ a₂ : ℕ) :
    ∃ a d : ℕ,a₁+a₂≤ a∧(d=1∨d=2) ∧
      ∀ k : Fin (p+q - 1),∃ (i : Fin p) (j : Fin q),
        (a₁+i.val*d₁)+(a₂+j.val*d₂)=a+k.val*d:=by
  obtain ⟨d,hd,h⟩:=qai8 hp hq hd₁ hd₂
  refine ⟨a₁+a₂,d,le_rfl,hd,fun k=>?_⟩
  obtain ⟨i,j,hi,hj,hij⟩:=h k.val k.isLt
  exact ⟨⟨i,hi⟩,⟨j,hj⟩,by dsimp only;omega⟩
theorem qi3 {p q d₁ d₂ : ℕ} (hp : 1≤ p) (hq : 1≤ q) (hpq : 6≤ p+q)
    (hd₁ : d₁=1∨d₁=2) (hd₂ : d₂=1∨d₂=2) (a₁ a₂ b : ℕ) :
    ∃ (i : Fin p) (j : Fin q),5∣(a₁+i.val*d₁)+(a₂+j.val*d₂)+b:=by
  obtain ⟨a,d,-,hd,h⟩:=qi9 hp hq hd₁ hd₂ a₁ a₂
  obtain ⟨k,hk⟩:=qq4 hd (a+b)
  obtain ⟨i,j,hij⟩:=h ⟨k.val,by omega⟩
  refine ⟨i,j,?_⟩
  rw [hij]
  show 5∣a+k.val*d+b
  omega
theorem qk5 {p q d₁ d₂ : ℕ} (hp : 2≤ p) (hq : 2≤ q)
    (hd₁ : d₁=1∨d₁=2) (hd₂ : d₂=1∨d₂=2) (hne : d₁≠d₂)
    (hlarge : 5≤ p+2*q - 2∨5≤ 2*p+q - 2) (a₁ a₂ b : ℕ) :
    ∃ (i : Fin p) (j : Fin q),5∣(a₁+i.val*d₁)+(a₂+j.val*d₂)+b:=by
  have h5 : 5≤ p+q:=by omega
  obtain ⟨k,hk⟩:=qq4 (Or.inl rfl) (a₁+a₂+b)
  have hk5:=k.isLt
  rcases hd₁ with rfl|rfl <;> rcases hd₂ with rfl|rfl
  · exact absurd rfl hne
  · by_cases h : k.val / 2 < q
    · exact ⟨⟨k.val % 2,by omega⟩,⟨k.val / 2,h⟩,by dsimp only;omega⟩
    · exact ⟨⟨k.val - 2*(q - 1),by omega⟩,⟨q - 1,by omega⟩,by dsimp only;omega⟩
  · by_cases h : k.val / 2 < p
    · exact ⟨⟨k.val / 2,h⟩,⟨k.val % 2,by omega⟩,by dsimp only;omega⟩
    · exact ⟨⟨p - 1,by omega⟩,⟨k.val - 2*(p - 1),by omega⟩,by dsimp only;omega⟩
  · exact absurd rfl hne
theorem qg4 {d : ℕ} (hd : d=1∨d=2) (a b : ℕ) :
    Function.Injective (fun i : Fin 3=>(a+i.val*d+b) % 5):=by
  intro i j h
  have h' : (a+i.val*d+b) % 5=(a+j.val*d+b) % 5:=h
  have hi:=i.isLt
  have hj:=j.isLt
  apply Fin.ext
  rcases hd with rfl|rfl <;> omega
theorem qn0 (f g : Fin 3→ ℕ) (b : ℕ)
    (hf : Function.Injective (fun i=>f i % 5))
    (hg : Function.Injective (fun j=>g j % 5)) :
    ∃ i j : Fin 3,5∣f i+g j+b:=by
  have hg' : Function.Injective (fun j=>(5 - (g j+b) % 5) % 5):=by
    intro j j' h
    have h' : (5 - (g j+b) % 5) % 5=(5 - (g j'+b) % 5) % 5:=h
    apply hg
    show g j % 5=g j' % 5
    omega
  have hA : (Finset.univ.image (fun i=>f i % 5)).card=3:=by
    rw [Finset.card_image_of_injective _ hf,Finset.card_univ,Fintype.card_fin]
  have hB : (Finset.univ.image (fun j=>(5 - (g j+b) % 5) % 5)).card=3:=by
    rw [Finset.card_image_of_injective _ hg',Finset.card_univ,Fintype.card_fin]
  have hsub : Finset.univ.image (fun i=>f i % 5) ∪
      Finset.univ.image (fun j=>(5 - (g j+b) % 5) % 5)⊆Finset.range 5:=by
    intro r hr
    simp only [Finset.mem_union,Finset.mem_image,Finset.mem_univ,true_and] at hr
    rw [Finset.mem_range]
    rcases hr with ⟨i,rfl⟩|⟨j,rfl⟩ <;> omega
  have hne : (Finset.univ.image (fun i=>f i % 5) ∩
      Finset.univ.image (fun j=>(5 - (g j+b) % 5) % 5)).Nonempty:=by
    rw [Finset.nonempty_iff_ne_empty]
    intro h
    have h1:=Finset.card_union_add_card_inter (Finset.univ.image (fun i=>f i % 5))
      (Finset.univ.image (fun j=>(5 - (g j+b) % 5) % 5))
    have h2:=Finset.card_le_card hsub
    rw [h,Finset.card_empty,hA,hB] at h1
    rw [Finset.card_range] at h2
    omega
  obtain ⟨r,hr⟩:=hne
  simp only [Finset.mem_inter,Finset.mem_image,Finset.mem_univ,true_and] at hr
  obtain ⟨⟨i,hi⟩,⟨j,hj⟩⟩:=hr
  exact ⟨i,j,by omega⟩
theorem qt8 (f g : Fin 3→ ℕ)
    (hf : Function.Injective (fun i=>f i % 5))
    (hg : Function.Injective (fun j=>g j % 5)) :
    ∃ i j : Fin 3,5∣f i+g j:=by
  simpa using qn0 f g 0 hf hg
theorem qe0 (hG : Nf0 G) {x y : V}
    {p q a₁ a₂ d₁ d₂ b : ℕ} (hp : 1≤ p) (hq : 1≤ q) (hpq : 6≤ p+q)
    (hd₁ : d₁=1∨d₁=2) (hd₂ : d₂=1∨d₂=2)
    (P : Fin p→ G.Walk x y) (Q : Fin q→ G.Walk x y)
    (hP : ∀ i,(P i).IsPath∧(P i).length=a₁+i.val*d₁)
    (hQ : ∀ j,(Q j).IsPath∧(Q j).length=a₂+j.val*d₂+b)
    (hint : ∀ i j v,v∈(P i).support→ v∈(Q j).support→ v=x∨v=y)
    (hlen : ∀ i j,3≤ (P i).length+(Q j).length) : False:=by
  obtain ⟨i,j,h⟩:=qi3 hp hq hpq hd₁ hd₂ a₁ a₂ b
  apply qc4 hG (hP i).1 (hQ j).1 (hint i j) (hlen i j)
  rw [(hP i).2,(hQ j).2]
  omega
theorem qad2 (hG : Nf0 G) {x y : V}
    {p q a₁ a₂ d₁ d₂ b : ℕ} (hp : 2≤ p) (hq : 2≤ q) (hpq : 5≤ p+q)
    (hd₁ : d₁=1∨d₁=2) (hd₂ : d₂=1∨d₂=2) (hne : d₁≠d₂)
    (P : Fin p→ G.Walk x y) (Q : Fin q→ G.Walk x y)
    (hP : ∀ i,(P i).IsPath∧(P i).length=a₁+i.val*d₁)
    (hQ : ∀ j,(Q j).IsPath∧(Q j).length=a₂+j.val*d₂+b)
    (hint : ∀ i j v,v∈(P i).support→ v∈(Q j).support→ v=x∨v=y)
    (hlen : ∀ i j,3≤ (P i).length+(Q j).length) : False:=by
  obtain ⟨i,j,h⟩ :=
    qk5 hp hq hd₁ hd₂ hne (Or.inl (by omega)) a₁ a₂ b
  apply qc4 hG (hP i).1 (hQ j).1 (hint i j) (hlen i j)
  rw [(hP i).2,(hQ j).2]
  omega
theorem qe4 (hG : Nf0 G) {x y : V}
    (f g : Fin 3→ G.Walk x y) (hf : ∀ i,(f i).IsPath) (hg : ∀ j,(g j).IsPath)
    (hint : ∀ i j v,v∈(f i).support→ v∈(g j).support→ v=x∨v=y)
    (hlen : ∀ i j,3≤ (f i).length+(g j).length)
    (hfi : Function.Injective (fun i=>(f i).length % 5))
    (hgi : Function.Injective (fun j=>(g j).length % 5)) : False:=by
  obtain ⟨i,j,h⟩ :=
    qt8 (fun i=>(f i).length) (fun j=>(g j).length) hfi hgi
  exact qc4 hG (hf i) (hg j) (hint i j) (hlen i j) h
theorem qan6 {x y : V} {q : ℕ} (h : Adm0 G x y q) :
    ∃ a d : ℕ,2≤ a∧(d=1∨d=2)∧∃ P : Fin q→ G.Walk x y,
      ∀ i,(P i).IsPath∧(P i).length=a+i.val*d:=by
  obtain ⟨a,d,ha,hd,hP⟩:=h
  choose P hP1 hP2 using hP
  exact ⟨a,d,ha,hd,P,fun i=>⟨hP1 i,hP2 i⟩⟩
theorem qg1 {x y : V} {q : ℕ} (h : Adm0 G x y q) :
    Adm0 G y x q:=by
  obtain ⟨a,d,ha,hd,hP⟩:=h
  refine ⟨a,d,ha,hd,fun i=>?_⟩
  obtain ⟨p,hp,hl⟩:=hP i
  exact ⟨p.reverse,hp.reverse,by rw [Walk.length_reverse,hl]⟩
theorem qc0 {x y : V} {q q' : ℕ} (hq : q'≤ q) (h : Adm0 G x y q) :
    Adm0 G x y q':=by
  obtain ⟨a,d,ha,hd,hP⟩:=h
  exact ⟨a,d,ha,hd,fun i=>hP (Fin.castLE hq i)⟩
theorem qj2 {H : SimpleGraph W} (f : G →g H) (hf : Function.Injective f)
    {x y : V} {q : ℕ} (h : Adm0 G x y q) : Adm0 H (f x) (f y) q:=by
  obtain ⟨a,d,ha,hd,hP⟩:=h
  refine ⟨a,d,ha,hd,fun i=>?_⟩
  obtain ⟨p,hp,hl⟩:=hP i
  exact ⟨p.map f,qb8 f hf hp,by rw [Walk.length_map,hl]⟩
theorem qp2 {H : SimpleGraph V} (hle : H≤ G) {x y : V} {q : ℕ}
    (h : Adm0 H x y q) : Adm0 G x y q :=
  qj2 (SimpleGraph.Hom.ofLE hle) (fun _ _ hab=>hab) h
theorem qae8 {x y : V} {q : ℕ} (h : Adm0 G x y q) :
    qal2 G x y q:=by
  obtain ⟨a,d,ha,hd,hP⟩:=h
  exact ⟨a,d,by omega,hd,hP⟩
end DeanK5
end M0
section M1
namespace Dt
open SimpleGraph
variable {V : Type} {J : SimpleGraph V}
private abbrev Gir (J : SimpleGraph V):=∀ n∈J.cycleLengths,6≤ n∧n≠10
private def TracePath (J : SimpleGraph V) (f : ℕ→ V) (n : ℕ) : Prop :=
  (∀ k < n,J.Adj (f k) (f (k+1)))∧Set.InjOn f (Set.Iic n)
private theorem TracePath.restrict {f : ℕ→ V} {n s t : ℕ}
    (p : TracePath J f n) (hs : s≤ t) (ht : t≤ n) : TracePath J (fun k=>f (s+k)) (t-s):=by
  refine ⟨fun k hk=>p.1 (s+k) (by omega),?_⟩
  intro k hk l hl h
  change k≤ t-s at hk
  change l≤ t-s at hl
  have:=p.2 (show s+k≤ n by omega) (show s+l≤ n by omega) h
  omega
private structure Route (J : SimpleGraph V) (A : Set V) (a b : V) (n : ℕ) where
  walk : J.Walk a b
  simple : walk.IsPath
  length : walk.length=n
  within : ∀ x∈walk.support,x∈A
namespace Route
variable {A B : Set V} {a b c x y : V} {n m : ℕ}
private def ofTrace (f : ℕ→ V) (h : TracePath J f n) (ha : f 0=a) (hb : f n=b)
    (hm : ∀ k≤ n,f k∈A) : Route J A a b n:=by
  let l:=List.ofFn fun k : Fin (n+1)=>f k
  have hn : l≠[]:=by simp [l]
  have hc : l.IsChain J.Adj:=List.isChain_ofFn.mpr fun k hk=>h.1 k (by omega)
  refine ⟨(Walk.ofSupport l hn hc).copy ?_ ?_,?_,?_,?_⟩
  · simpa [l,List.head_ofFn] using ha
  · simpa only [l,List.getLast_ofFn,Nat.add_sub_cancel] using hb
  · rw [Walk.isPath_def,Walk.support_copy,Walk.support_ofSupport]
    exact List.nodup_ofFn_ofInjective fun i j e=>Fin.ext (h.2 (Nat.le_of_lt_succ i.isLt) (Nat.le_of_lt_succ j.isLt) e)
  · simp [l]
  · simp only [Walk.support_copy,Walk.support_ofSupport,l,List.mem_ofFn]
    rintro x ⟨k,rfl⟩
    exact hm k (by omega)
private def cast (p : Route J A a b n) (ha : a=x) (hb : b=y) (hn : n=m) : Route J A x y m :=
  ha ▸ hb ▸ hn ▸ p
private def mono (p : Route J A a b n) (h : A⊆B) : Route J B a b n :=
  { p with within:=fun x hx=>h (p.within x hx) }
private def f (p : Route J A a b n):=p.walk.getVert
private theorem path (p : Route J A a b n) : TracePath J p.f n:=by
  rcases p with ⟨w,hw,rfl,_⟩
  exact ⟨fun _=>w.adj_getVert_succ,hw.getVert_injOn⟩
private theorem first (p : Route J A a b n) : p.f 0=a:=p.walk.getVert_zero
private theorem last (p : Route J A a b n) : p.f n=b:=by
  exact (congrArg p.walk.getVert p.length.symm).trans p.walk.getVert_length
private theorem mem (p : Route J A a b n) (k : ℕ) (hk : k≤ n) : p.f k∈A :=
  p.within _ (Walk.mem_support_iff_exists_getVert.mpr ⟨k,rfl,by simpa only [p.length] using hk⟩)
private theorem ne (p : Route J A a b n) (hn : 0 < n) : a≠b:=by
  intro e
  have:=p.path.2 (show n≤ n from le_rfl) (Nat.zero_le _) (p.last.trans (e.symm.trans p.first.symm))
  omega
private def reverse (p : Route J A a b n) : Route J A b a n :=
  ⟨p.walk.reverse,p.simple.reverse,by simp [p.length],fun x hx=>p.within x (by simpa using hx)⟩
private theorem not_tail (p : Route J A a b n) : a∉p.walk.support.tail:=by
  have h:=p.simple.support_nodup
  rw [← p.walk.cons_tail_support,List.nodup_cons] at h
  exact h.1
private def join (p : Route J A a b n) (q : Route J B b c m)
    (h : ∀ x∈A,x∈B→ x=b) : Route J (A∪B) a c (n+m) where
  walk:=p.walk.append q.walk
  length:=by simp [p.length,q.length]
  simple:=by
    rw [Walk.isPath_def,Walk.support_append,List.nodup_append]
    refine ⟨p.simple.support_nodup,q.simple.support_nodup.tail,?_⟩
    rintro x hx _ hy rfl
    exact q.not_tail (h _ (p.within _ hx) (q.within _ (List.mem_of_mem_tail hy)) ▸ hy)
  within:=by
    simp only [Walk.support_append,List.mem_append]
    rintro x (hx|hx)
    · exact Or.inl (p.within x hx)
    · exact Or.inr (q.within x (List.mem_of_mem_tail hx))
private theorem cycle (p : Route J A a b n) (q : Route J B b a m) (hlen : 3≤ n+m)
    (h : ∀ x∈A,x∈B→ x=a∨x=b) : n+m∈J.cycleLengths:=by
  refine ⟨a,p.walk.append q.walk,p.simple.isCycle_append q.simple ?_ ?_,by simp [p.length,q.length]⟩
  · refine List.disjoint_left.mpr (fun x hx hy=>?_)
    rcases h x (p.within x (List.mem_of_mem_tail hx)) (q.within x (List.mem_of_mem_tail hy)) with rfl|rfl
    · exact p.not_tail hx
    · exact q.not_tail hy
  · rw [p.length,q.length]
    omega
private def edge (h : J.Adj a b) : Route J ({a,b} : Set V) a b 1 :=
  ⟨.cons h .nil,by simp [Walk.isPath_def,h.ne],rfl,by simp⟩
private def via (h : J.Adj a b) (h' : J.Adj b c) (hne : a≠c) :
    Route J ({a,b,c} : Set V) a c 2 :=
  ((edge h).join (edge h') (by
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
    rintro x (rfl|rfl) (h₁|h₂) <;> simp_all)).mono (by simp [Set.insert_subset_iff])
end Route
private def qar7 {P : Fin 3→ Type} (p : P 0) (q : P 1) (r : P 2) (i : Fin 3) : P i:=by
  refine Fin.cases p (fun j=>?_) i
  refine Fin.cases q (fun k=>?_) j
  exact Fin.cases r (fun z=>z.elim0) k
private structure Theta (J : SimpleGraph V) where
  a : V
  b : V
  l : Fin 3→ ℕ
  p : ∀ i,Route J Set.univ a b (l i)
  pos : ∀ i,0 < l i
  two : ∀ i j,i≠j→ 3≤ l i+l j
  cross : ∀ i j,i≠j→ ∀ x∈(p i).walk.support,x∈(p j).walk.support→ x=a∨x=b
namespace Theta
variable (T : Theta J)
private def f (i : Fin 3):=(T.p i).f
private theorem start (i : Fin 3) : T.f i 0=T.a:=(T.p i).first
private theorem stop (i : Fin 3) : T.f i (T.l i)=T.b:=(T.p i).last
private theorem adj (i : Fin 3) : ∀ k < T.l i,J.Adj (T.f i k) (T.f i (k+1)) :=
  (T.p i).path.1
private theorem a_ne_b : T.a≠T.b:=(T.p 0).ne (T.pos 0)
private def verts [DecidableEq V] : Finset V :=
  Finset.univ.biUnion fun i=>(T.p i).walk.support.toFinset
private def len:=T.l 0+T.l 1+T.l 2
private def IsMin:=∀ U : Theta J,T.len≤ U.len
private def Edge (x y : V) : Prop :=
  ∃ i,∃ k < T.l i,(T.f i k=x∧T.f i (k+1)=y)∨(T.f i k=y∧T.f i (k+1)=x)
private abbrev Ind [DecidableEq V] : Prop:=∀ x∈T.verts,∀ y∈T.verts,J.Adj x y→ T.Edge x y
private def rev : Theta J where
  a:=T.b
  b:=T.a
  l:=T.l
  p i:=(T.p i).reverse
  pos:=T.pos
  two:=T.two
  cross i j h x hx hy:=(T.cross i j h x (by simpa [Route.reverse] using hx)
    (by simpa [Route.reverse] using hy)).symm
private theorem qam9 : T.rev.l=T.l:=rfl
private theorem qar9 (i : Fin 3) (k : ℕ) : T.rev.f i k=T.f i (T.l i-k):=by
  simp [rev,f,Route.f,Route.reverse,Walk.getVert_reverse,(T.p i).length]
private theorem rev_verts [DecidableEq V] : T.rev.verts=T.verts:=by
  ext x
  simp [rev,verts,Route.reverse]
variable {T}
private theorem IsMin.rev (h : T.IsMin) : T.rev.IsMin:=h
private theorem qw3 {i : Fin 3} {k m : ℕ} (hk : k≤ T.l i) (hm : m≤ T.l i)
    (h : T.f i k=T.f i m) : k=m:=(T.p i).path.2 hk hm h
private theorem qaq9 {i : Fin 3} {k : ℕ} (hk : k≤ T.l i) (h : T.f i k=T.a) : k=0 :=
  qw3 hk (Nat.zero_le _) (h.trans (T.start i).symm)
private theorem qap3 {i : Fin 3} {k : ℕ} (hk : k≤ T.l i) (h : T.f i k=T.b) : k=T.l i :=
  qw3 hk le_rfl (h.trans (T.stop i).symm)
private theorem qab1 {i : Fin 3} {k : ℕ} (hk : k≤ T.l i) :
    T.f i k∈(T.p i).walk.support :=
  Walk.mem_support_iff_exists_getVert.mpr ⟨k,rfl,by simpa only [(T.p i).length] using hk⟩
private theorem qam1 {i j : Fin 3} (hij : i≠j) {k m : ℕ} (hk : k≤ T.l i) (hm : m≤ T.l j)
    (h : T.f i k=T.f j m) : (k=0∧m=0)∨(k=T.l i∧m=T.l j):=by
  rcases T.cross i j hij _ (qab1 hk) (h ▸ qab1 hm) with e|e
  · exact Or.inl ⟨qaq9 hk e,qaq9 hm (h.symm.trans e)⟩
  · exact Or.inr ⟨qap3 hk e,qap3 hm (h.symm.trans e)⟩
private theorem inj (i j : Fin 3) (k m : ℕ) (hk : k≤ T.l i) (hm : m≤ T.l j)
    (h : T.f i k=T.f j m) : (i=j∧k=m)∨(k=0∧m=0)∨(k=T.l i∧m=T.l j):=by
  by_cases e : i=j
  · subst j
    exact Or.inl ⟨rfl,qw3 hk hm h⟩
  · exact Or.inr (qam1 e hk hm h)
private theorem mem_verts [DecidableEq V] {x : V} : x∈T.verts↔∃ i k,k≤ T.l i∧T.f i k=x:=by
  simp [verts,Walk.mem_support_iff_exists_getVert,f,Route.f,Route.length,and_comm]
private theorem f_mem [DecidableEq V] {i : Fin 3} {k : ℕ} (hk : k≤ T.l i) : T.f i k∈T.verts :=
  mem_verts.2 ⟨i,k,hk,rfl⟩
private theorem qar5 [DecidableEq V] : T.a∈T.verts:=by
  rw [← T.start 0]
  exact f_mem (Nat.zero_le _)
private theorem qas2 [DecidableEq V] : T.b∈T.verts:=by
  rw [← T.stop 0]
  exact f_mem le_rfl
private theorem third (i j : Fin 3) (hij : i≠j) :
    ∃ k : Fin 3,k≠i∧k≠j∧∀ m : Fin 3,m=i∨m=j∨m=k:=by
  fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> decide
private theorem len_eq {i j k : Fin 3} (hij : i≠j) (hik : i≠k) (hjk : j≠k) :
    T.l i+T.l j+T.l k=T.len:=by
  unfold len
  fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hik hjk ⊢ <;> omega
private def span (T : Theta J) (i : Fin 3) (s t : ℕ) : Set V :=
  {x|∃ k,s≤ k∧k≤ t∧k≤ T.l i∧T.f i k=x}
private theorem span_mem [DecidableEq V] {i : Fin 3} {s t : ℕ} :
    T.span i s t⊆(T.verts : Set V):=by
  rintro _ ⟨k,_,_,hk,rfl⟩
  exact f_mem hk
private def seg (T : Theta J) (i : Fin 3) {s t : ℕ} (hst : s≤ t) (ht : t≤ T.l i) :
    Route J (T.span i s t) (T.f i s) (T.f i t) (t-s) :=
  Route.ofTrace _ ((T.p i).path.restrict hst ht) rfl (congrArg (T.f i) (by omega))
    (fun k hk=>⟨s+k,by omega,by omega,by omega,rfl⟩)
private def pre (T : Theta J) (i : Fin 3) {t : ℕ} (ht : t≤ T.l i) :
    Route J (T.span i 0 t) T.a (T.f i t) t :=
  (T.seg i (Nat.zero_le _) ht).cast (T.start i) rfl (Nat.sub_zero _)
private def post (T : Theta J) (i : Fin 3) {s : ℕ} (hs : s≤ T.l i) :
    Route J (T.span i s (T.l i)) (T.f i s) T.b (T.l i-s) :=
  (T.seg i hs le_rfl).cast rfl (T.stop i) rfl
private def arm (T : Theta J) (i : Fin 3) :
    Route J (T.span i 0 (T.l i)) T.a T.b (T.l i) :=
  (T.pre i le_rfl).cast rfl (T.stop i) rfl
end Theta
namespace Theta
private def rim [DecidableEq V] (T : Theta J) (a b : V) : Set V :=
  {x|x=a∨x=b∨x∉T.verts}
end Theta
namespace Theta
variable (T : Theta J)
private theorem armCycle {i j : Fin 3} (hij : i≠j) : T.l i+T.l j∈J.cycleLengths :=
  (T.arm i).cycle (T.arm j).reverse (T.two i j hij) (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only })
private theorem girthArms (hg : Gir J) {i j : Fin 3} (hij : i≠j) : 6≤ T.l i+T.l j :=
  (hg _ (T.armCycle hij)).1
end Theta
private def Theta.ofRoutes {A B C : Set V} {a b : V} {l m n : ℕ}
    (p : Route J A a b l) (q : Route J B a b m) (r : Route J C a b n)
    (hp : 0 < l) (hq : 0 < m) (hr : 0 < n)
    (h₁ : 3≤ l+m) (h₂ : 3≤ l+n) (h₃ : 3≤ m+n)
    (hpq : ∀ x∈A,x∈B→ x=a∨x=b)
    (hpr : ∀ x∈A,x∈C→ x=a∨x=b)
    (hqr : ∀ x∈B,x∈C→ x=a∨x=b) : Theta J:=by
  let arm : (i : Fin 3)→ Route J Set.univ a b (![l,m,n] i) :=
    qar7 (p.mono (Set.subset_univ _)) (q.mono (Set.subset_univ _)) (r.mono (Set.subset_univ _))
  refine ⟨a,b,![l,m,n],arm,?_,?_,?_⟩
  · intro i
    fin_cases i <;> simpa
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
  · intro i j hij x hx hy
    fin_cases i <;> fin_cases j <;> simp at hij
    · exact hpq x (p.within x hx) (q.within x hy)
    · exact hpr x (p.within x hx) (r.within x hy)
    · exact hpq x (p.within x hy) (q.within x hx)
    · exact hqr x (q.within x hx) (r.within x hy)
    · exact hpr x (p.within x hy) (r.within x hx)
    · exact hqr x (q.within x hy) (r.within x hx)
namespace Theta
variable {T : Theta J}
private theorem qap6 {x y : V} (h : T.Edge x y) : T.Edge y x:=by
  obtain ⟨i,k,hk,h⟩:=h
  exact ⟨i,k,hk,h.symm⟩
variable [DecidableEq V]
private abbrev Detour (T : Theta J) (x y : V) (d : ℕ) :=
  Route J (T.rim x y) x y d
private def qao6 {x y : V} {d : ℕ} (R : T.Detour x y d) :
    T.Detour y x d :=
  R.reverse.mono fun _ h=>h.elim (Or.inr ∘ Or.inl) (Or.imp_right Or.inr)
private theorem qaf6 (hg : Gir J) (hmin : T.IsMin) {i : Fin 3} {s t d : ℕ}
    (hst : s < t) (ht : t≤ T.l i) (hd : 0 < d) (hd' : d≤ 2)
    (R : T.Detour (T.f i s) (T.f i t) d)
    (hE : d=1→ ¬ T.Edge (T.f i s) (T.f i t)) : False:=by
  have h₃ : 3≤ t-s+d:=by
    by_contra h
    exact hE (by omega) ⟨i,s,by omega,Or.inl ⟨rfl,congrArg (T.f i) (by omega)⟩⟩
  have hl:=(hg _ ((T.seg i hst.le ht).cycle R.reverse h₃ (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only }))).1
  obtain ⟨j,hji,_,_⟩:=third i (i+1) (by fin_cases i <;> decide)
  obtain ⟨k,hki,hkj,_⟩:=third i j hji.symm
  have hsum:=T.len_eq hji.symm hki.symm hkj.symm
  let p:=((T.pre i (show s≤ T.l i by omega)).join R (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only })).join
    (T.post i ht) (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only })
  have hpair (j : Fin 3) : 3≤ s+d+(T.l i-t)+T.l j:=by
    have:=T.pos j
    by_contra h
    apply hE (by omega)
    have hs : s=0:=by omega
    have ht' : t=T.l i:=by omega
    have hj : T.l j=1:=by omega
    exact ⟨j,0,by omega,Or.inl ⟨by rw [hs,T.start,T.start],
      by rw [ht',T.stop,← hj,Nat.zero_add,T.stop]⟩⟩
  have h:=hmin (ofRoutes p (T.arm j) (T.arm k) (by omega) (T.pos j) (T.pos k)
    (hpair j) (hpair k) (T.two j k hkj.symm)
    (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only }) (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only }) (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only }))
  change T.len≤ s+d+(T.l i-t)+T.l j+T.l k at h
  omega
private theorem qaq6 (hg : Gir J) (hmin : T.IsMin) {i : Fin 3} {s t d : ℕ}
    (hs : s≤ T.l i) (ht : t≤ T.l i) (hd : 0 < d) (hd' : d≤ 2)
    (R : T.Detour (T.f i s) (T.f i t) d)
    (hE : d=1→ ¬ T.Edge (T.f i s) (T.f i t)) : False:=by
  have hne : s≠t:=fun h=>R.ne hd (congrArg (T.f i) h)
  rcases lt_or_gt_of_ne hne with h|h
  · exact qaf6 hg hmin h ht hd hd' R hE
  · exact qaf6 hg hmin h hs hd hd' (qao6 R) (fun hd e=>hE hd (qap6 e))
private theorem qw9 (hmin : T.IsMin) {i j : Fin 3} (hij : i≠j) {s t d : ℕ}
    (hs₀ : 0 < s) (hs : s < T.l i) (ht₀ : 0 < t) (ht : t < T.l j) (hd : 0 < d)
    (R : T.Detour (T.f i s) (T.f j t) d) : s≤ d:=by
  obtain ⟨k,hki,hkj,_⟩:=third i j hij
  have hsum:=T.len_eq hij hki.symm hkj.symm
  let p:=(T.pre j ht.le).reverse.join (T.arm k) (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only })
  let q:=R.reverse.join (T.post i hs.le) (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only })
  have h:=hmin (ofRoutes (T.post j ht.le) p q (by omega) (by have:=T.pos k;omega)
    (by omega) (by have:=T.two j k hkj.symm;omega) (by omega) (by have:=T.pos k;omega)
    (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only }) (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only }) (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only }))
  change T.len≤ T.l j-t+(t+T.l k)+(d+(T.l i-s)) at h
  omega
private theorem qaj2 (hg : Gir J) {i j : Fin 3} (hij : i≠j) {s t d : ℕ}
    (hs₀ : 0 < s) (hs : s < T.l i) (ht₀ : 0 < t) (ht : t < T.l j) (hd : 0 < d)
    (R : T.Detour (T.f i s) (T.f j t) d) : 6≤ s+d+t:=by
  let q:=R.join (T.pre j ht.le).reverse (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only })
  have h:=(hg _ ((T.pre i hs.le).cycle q (by omega) (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only }))).1
  omega
private def qan5 {i j : Fin 3} (hij : i≠j) (hi : T.l i=4) (hj : T.l j=4)
    (R : T.Detour (T.f i 2) (T.f j 2) 2) : Theta J :=
  let p:=(T.pre i (t:=2) (by omega)).reverse.join (T.pre j (t:=2) (by omega))
    (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only })
  let q:=(T.post i (s:=2) (by omega)).join (T.post j (s:=2) (by omega)).reverse
    (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only })
  ofRoutes p (q.cast rfl rfl (by omega : (T.l i-2)+(T.l j-2)=4)) R
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only }) (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only }) (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only })
private theorem minRoute (hg : Gir J) (hmin : T.IsMin) {i j : Fin 3} {s t d : ℕ}
    (hs : s≤ T.l i) (ht : t≤ T.l j) (hd : 0 < d) (hd' : d≤ 2)
    (R : T.Detour (T.f i s) (T.f j t) d)
    (hE : d=1→ ¬ T.Edge (T.f i s) (T.f j t)) :
    d=2∧i≠j∧s=2∧t=2∧T.l i=4∧T.l j=4 ∧
      ∀ k,k≠i→ k≠j→ T.l k=2:=by
  by_cases hij : i=j
  · subst j
    exact (qaq6 hg hmin hs ht hd hd' R hE).elim
  have hstart (i j : Fin 3) : T.f i 0=T.f j 0:=(T.start i).trans (T.start j).symm
  have hstop (i j : Fin 3) : T.f i (T.l i)=T.f j (T.l j):=(T.stop i).trans (T.stop j).symm
  have move {x y : V} (hx : T.f i s=x) (hy : T.f j t=y) :
      T.Detour x y d:=hx ▸ hy ▸ R
  have same {k : Fin 3} {u v : ℕ} (hu : u≤ T.l k) (hv : v≤ T.l k)
      (e₁ : T.f i s=T.f k u) (e₂ : T.f j t=T.f k v) : False :=
    qaq6 hg hmin hu hv hd hd' (move e₁ e₂) (by simpa only [← e₁,← e₂] using hE)
  have hs₀ : 0 < s:=by
    by_contra h
    obtain rfl : s=0:=by omega
    exact same (Nat.zero_le _) ht (hstart i j) rfl
  have hs' : s < T.l i:=by
    by_contra h
    obtain rfl : s=T.l i:=by omega
    exact same le_rfl ht (hstop i j) rfl
  have ht₀ : 0 < t:=by
    by_contra h
    obtain rfl : t=0:=by omega
    exact same hs (Nat.zero_le _) rfl (hstart j i)
  have ht' : t < T.l j:=by
    by_contra h
    obtain rfl : t=T.l j:=by omega
    exact same hs le_rfl rfl (hstop j i)
  have e₁ : T.f i s=T.rev.f i (T.l i-s):=by rw [qar9];congr 1;omega
  have e₂ : T.f j t=T.rev.f j (T.l j-t):=by rw [qar9];congr 1;omega
  have R' : T.rev.Detour (T.rev.f i (T.l i-s)) (T.rev.f j (T.l j-t)) d :=
    (move e₁ e₂).mono (by simp [rim,rev_verts])
  have c₁:=qw9 hmin hij hs₀ hs' ht₀ ht' hd R
  have c₂:=qw9 hmin (Ne.symm hij) ht₀ ht' hs₀ hs' hd (qao6 R)
  have c₃:=qw9 hmin.rev hij (by omega) (by rw [qam9];omega) (by omega) (by rw [qam9];omega) hd R'
  have c₄:=qw9 hmin.rev (Ne.symm hij) (by omega) (by rw [qam9];omega) (by omega) (by rw [qam9];omega) hd
    (qao6 R')
  have c₅:=qaj2 hg hij hs₀ hs' ht₀ ht' hd R
  have c₆:=qaj2 hg hij (by omega) (by rw [qam9];omega) (by omega) (by rw [qam9];omega) hd R'
  obtain ⟨hd₂,hs₂,ht₂,hi,hj⟩ : d=2∧s=2∧t=2∧T.l i=4∧T.l j=4:=by omega
  subst d s t
  refine ⟨rfl,hij,rfl,rfl,hi,hj,fun k hki hkj=>?_⟩
  have h:=hmin (qan5 hij hi hj R)
  change T.len≤ 10 at h
  have:=T.len_eq hij hki.symm hkj.symm
  have:=T.girthArms hg hki.symm
  omega
end Theta
private def Route.inside {A B : Set V} {a b : V} {n : ℕ}
    (p : Route J A a b n) (ha : a∈B) (hb : b∈B) (h : A⊆B) :
    (J.induce B).Walk ⟨a,ha⟩ ⟨b,hb⟩ :=
  p.walk.induce B fun _ hx=>h (p.within _ hx)
private theorem Route.inside_spec {A B : Set V} {a b : V} {n : ℕ}
    (p : Route J A a b n) (ha : a∈B) (hb : b∈B) (h : A⊆B) :
    (p.inside ha hb h).IsPath∧(p.inside ha hb h).length=n:=by
  have hm:=Walk.map_induce p.walk (fun _ hx=>h (p.within _ hx))
  exact ⟨Walk.IsPath.of_map (f:=(Embedding.induce B).toHom) (hm ▸ p.simple),
    (Walk.length_map ..).symm.trans ((congrArg Walk.length hm).trans p.length)⟩
namespace Theta
variable [DecidableEq V] (T : Theta J)
private theorem connFrom (S : Set V) (small : S.Subsingleton) (ha : T.a∉S) :
    (J.induce ((T.verts : Set V)\S)).Connected:=by
  let A:=(T.verts : Set V)\S
  change (J.induce A).Connected
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨T.a,qar5,ha⟩,?_⟩
  rintro ⟨x,hx,hxs⟩
  obtain ⟨i,k,hk,rfl⟩:=mem_verts.1 hx
  by_cases h : ∃ m≤ k,T.f i m∈S
  · obtain ⟨m,hm,hmS⟩:=h
    have hm₀ : 0 < m:=by
      by_contra h
      exact ha (by simpa [show m=0 by omega,T.start] using hmS)
    have hmk : m < k:=lt_of_le_of_ne hm (fun h=>hxs (h ▸ hmS))
    have hb : T.b∉S:=fun h=>by
      have:=qap3 (T:=T) (hm.trans hk) (small hmS h)
      omega
    have hji : i+1≠i:=by fin_cases i <;> decide
    have h₁ : T.span (i+1) 0 (T.l (i+1))⊆(T.verts : Set V)\S:=by
      rintro y ⟨q,_,_,hq,rfl⟩
      refine ⟨f_mem hq,fun hqS=>?_⟩
      rcases qam1 hji hq (hm.trans hk) (small hqS hmS) with h|h <;> omega
    have h₂ : T.span i k (T.l i)⊆(T.verts : Set V)\S:=by
      rintro y ⟨q,hq,_,hql,rfl⟩
      refine ⟨f_mem hql,fun hqS=>?_⟩
      have:=qw3 hql (hm.trans hk) (small hqS hmS)
      omega
    exact ⟨((T.arm (i+1)).inside (B:=A) ⟨qar5,ha⟩ ⟨qas2,hb⟩ h₁).append
      ((T.post i hk).inside (B:=A) ⟨hx,hxs⟩ ⟨qas2,hb⟩ h₂).reverse⟩
  · exact ⟨(T.pre i hk).inside (B:=A) ⟨qar5,ha⟩ ⟨hx,hxs⟩
      (by rintro _ ⟨m,_,hm,hml,rfl⟩;exact ⟨f_mem hml,fun hmS=>h ⟨m,hm,hmS⟩⟩)⟩
private theorem conn (S : Set V) (small : S.Subsingleton) :
    (J.induce ((T.verts : Set V)\S)).Connected:=by
  by_cases ha : T.a∈S
  · rw [← T.rev_verts]
    exact T.rev.connFrom S small (fun hb=>T.a_ne_b (small ha hb))
  · exact T.connFrom S small ha
private theorem large (hg : Gir J) : 2 < T.verts.card:=by
  have:=T.girthArms hg (show (0 : Fin 3)≠1 by decide)
  obtain ⟨i,hi⟩ : ∃ i,3≤ T.l i:=by
    by_cases h : 3≤ T.l 0
    · exact ⟨0,h⟩
    · exact ⟨1,by omega⟩
  refine Finset.two_lt_card_iff.mpr ⟨T.f i 0,T.f i 1,T.f i 2,
    f_mem (by omega),f_mem (by omega),f_mem (by omega),?_,?_,?_⟩ <;>
    (intro h;have:=qw3 (by omega) (by omega) h;omega)
private theorem deg [Fintype V] [DecidableRel J.Adj] (hI : T.Ind) {x : V} (hx : x∈T.verts) :
    (J.neighborFinset x∩T.verts).card≤ 3:=by
  obtain ⟨i,s,hs,rfl⟩:=mem_verts.1 hx
  let f : Fin 3→ V:=if s=0 then fun j=>T.f j 1 else
    if s=T.l i then fun j=>T.f j (T.l j-1) else ![T.f i (s-1),T.f i (s+1),T.f i s]
  refine (Finset.card_le_card (t:=Finset.univ.image f) ?_).trans (Finset.card_image_le.trans (by simp))
  intro y hy
  simp only [Finset.mem_inter,mem_neighborFinset] at hy
  obtain ⟨j,k,hk,h⟩:=hI _ hx y hy.2 hy.1
  have candidate {v : V} (j : Fin 3) (h : f j=v) : v∈Finset.univ.image f :=
    Finset.mem_image.mpr ⟨j,by simp,h⟩
  have hpos:=T.pos i
  have hinj:=T.inj j i
  by_cases h₀ : s=0
  · have h₁ : T.f j 1∈Finset.univ.image f:=candidate j (by simp [f,h₀])
    grind only
  by_cases h₁ : s=T.l i
  · have h₂ : T.f j (T.l j-1)∈Finset.univ.image f:=candidate j (by simp only [f,if_neg h₀,if_pos h₁])
    grind only
  have hpre : T.f i (s-1)∈Finset.univ.image f:=candidate 0 (by simp [f,h₀,h₁])
  have hpost : T.f i (s+1)∈Finset.univ.image f:=candidate 1 (by simp [f,h₀,h₁])
  grind only
end Theta
private def qao1 {a b : V} (p : J.Walk a b) (hp : p.IsPath) {s t : ℕ}
    (hst : s≤ t) (ht : t≤ p.length) :
    Route J {x|∃ k,s≤ k∧k≤ t∧p.getVert k=x}
      (p.getVert s) (p.getVert t) (t-s) :=
  Route.ofTrace _ ((show TracePath J p.getVert p.length from
    ⟨fun _=>p.adj_getVert_succ,hp.getVert_injOn⟩).restrict hst ht)
    rfl (congrArg p.getVert (by omega)) (fun k hk=>⟨s+k,by omega,by omega,rfl⟩)
private theorem qak7 [Fintype V] [DecidableEq V] [DecidableRel J.Adj] [Nonempty V]
    (hdeg : ∀ v,4≤ J.degree v) : Nonempty (Theta J):=by
  obtain ⟨a,b,p,hp,hmax⟩:=Walk.exists_isPath_forall_isPath_length_le_length J
  have hnb (y : V) (hy : y∈(J.neighborFinset a).erase (p.getVert 1)) :
      ∃ k,2≤ k∧k≤ p.length∧p.getVert k=y∧J.Adj (p.getVert 0) y:=by
    simp only [Finset.mem_erase,mem_neighborFinset] at hy
    have hm : y∈p.support:=by
      by_contra hm
      have:=hmax y b (.cons hy.2.symm p) (hp.cons hm)
      simp at this
    obtain ⟨k,he,hk⟩:=Walk.mem_support_iff_exists_getVert.mp hm
    have hk₀ : k≠0:=fun h=>hy.2.ne (by simpa [h] using he)
    have hk₁ : k≠1:=fun h=>hy.1 (by simpa [h] using he.symm)
    exact ⟨k,by omega,hk,he,by simpa using hy.2⟩
  have hcard:=Finset.pred_card_le_card_erase (s:=J.neighborFinset a) (a:=p.getVert 1)
  rw [card_neighborFinset_eq_degree] at hcard
  have hd:=hdeg a
  obtain ⟨x,hx,y,hy,hxy⟩:=Finset.one_lt_card.mp (by omega : 1 < ((J.neighborFinset a).erase (p.getVert 1)).card)
  obtain ⟨i,hi,hi',rfl,ei⟩:=hnb x hx
  obtain ⟨j,hj,hj',rfl,ej⟩:=hnb y hy
  suffices key : ∀ {i j},2≤ i→ i < j→ j≤ p.length →
      J.Adj (p.getVert 0) (p.getVert i)→ J.Adj (p.getVert 0) (p.getVert j)→ Nonempty (Theta J) by
    rcases lt_or_gt_of_ne (show i≠j from fun h=>hxy (congrArg p.getVert h)) with h|h
    · exact key hi h hj' ei ej
    · exact key hj h hi' ej ei
  intro i j hi hij hj ei ej
  let P:=qao1 p hp (Nat.zero_le i) (show i≤ p.length by omega)
  let Q:=Route.edge ei
  let R:=(Route.edge ej).join (qao1 p hp hij.le hj).reverse (by
    intro x hx hy
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx
    obtain ⟨k,hk,hkj,he⟩:=hy
    rcases hx with rfl|rfl
    · have:=hp.getVert_injOn (show k≤ p.length by omega) (show 0≤ p.length by omega) he
      omega
    · rfl)
  refine ⟨Theta.ofRoutes P Q R (by omega) (by decide) (by omega) (by omega) (by omega) (by omega)
    (fun _ _ h=>h) ?_ (fun _ h _=>h)⟩
  intro x hx hy
  obtain ⟨k,_,hki,rfl⟩:=hx
  rcases hy with h|⟨l,hil,hlj,he⟩
  · simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
    rcases h with h|h
    · exact Or.inl h
    · have:=hp.getVert_injOn (show k≤ p.length by omega) hj h
      omega
  · have:=hp.getVert_injOn (show l≤ p.length by omega) (show k≤ p.length by omega) he
    exact Or.inr (congrArg p.getVert (by omega))
private theorem qaq3 [Fintype V] [DecidableEq V] [DecidableRel J.Adj] [Nonempty V]
    (hdeg : ∀ v,4≤ J.degree v) : ∃ T : Theta J,T.IsMin:=by
  classical
  obtain ⟨T⟩:=qak7 hdeg
  have h : ∃ n,∃ T : Theta J,T.len=n:=⟨T.len,T,rfl⟩
  obtain ⟨T,hT⟩:=Nat.find_spec h
  exact ⟨T,fun U=>hT ▸ Nat.find_min' h ⟨U,rfl⟩⟩
private abbrev Routes (J : SimpleGraph V) (A : Set V) :=
  ∃ x y : V,x≠y∧∃ n : Fin 3→ ℕ,Function.Injective (fun i=>n i % 5) ∧
    Nonempty (∀ i,Route J A x y (n i))
private theorem qaf2 {A : Set V} {x y : V} {l m n : ℕ}
    (p : Route J A x y l) (q : Route J A x y m) (r : Route J A x y n) (hp : 0 < l)
    (h₁ : l%5≠m%5) (h₂ : l%5≠n%5) (h₃ : m%5≠n%5) : Routes J A:=by
  refine ⟨x,y,p.ne hp,![l,m,n],?_,⟨?_⟩⟩
  · intro i j h
    fin_cases i <;> fin_cases j <;> simp at h ⊢ <;> omega
  · exact qar7 p q r
private abbrev PathResidues (J : SimpleGraph V) (U : Set V) :=
  ∃ x y : U,x≠y∧∃ p : Fin 3→ (J.induce U).Walk x y,
    (∀ i,(p i).IsPath)∧Function.Injective (fun i=>(p i).length % 5)
private theorem Routes.paths {A B : Set V} (H : Routes J A) (h : A⊆B) : PathResidues J B:=by
  obtain ⟨x,y,hxy,n,hn,⟨p⟩⟩:=H
  have hx : x∈B:=h ((p 0).first ▸ (p 0).mem 0 (Nat.zero_le _))
  have hy : y∈B:=h ((p 0).last ▸ (p 0).mem _ le_rfl)
  refine ⟨⟨x,hx⟩,⟨y,hy⟩,fun e=>hxy (congrArg Subtype.val e),
    fun i=>(p i).inside hx hy h,fun i=>((p i).inside_spec hx hy h).1,?_⟩
  intro i j e
  apply hn
  simpa only [(p i).inside_spec hx hy h |>.2,(p j).inside_spec hx hy h |>.2] using e
namespace Theta
variable [DecidableEq V] (T : Theta J)
private theorem twoResidues {i j k : Fin 3} (hij : i≠j) (hik : i≠k)
    (hi : 3≤ T.l i) (e : T.l i%5=T.l j%5) (hne : T.l k%5≠T.l i%5) :
    Routes J (T.verts : Set V):=by
  have step (c : ℕ) (hc : c < T.l i)
      (h₁ : (T.l i-c)%5≠(c+T.l j)%5) (h₂ : (T.l i-c)%5≠(c+T.l k)%5)
      (h₃ : (c+T.l j)%5≠(c+T.l k)%5) : Routes J (T.verts : Set V):=by
    let p:=(T.pre i hc.le).reverse
    exact qaf2 ((T.post i hc.le).mono T.span_mem)
      ((p.join (T.arm j) (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only })).mono (Set.union_subset T.span_mem T.span_mem))
      ((p.join (T.arm k) (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only })).mono (Set.union_subset T.span_mem T.span_mem))
      (by omega) h₁ h₂ h₃
  by_cases h : (T.l i-1)%5=(1+T.l k)%5
  · exact step 2 (by omega) (by omega) (by omega) (by omega)
  · exact step 1 (by omega) (by omega) h (by omega)
private theorem allResidues {i j k : Fin 3} (hij : i≠j) (hik : i≠k) (hjk : j≠k)
    (hi : 3≤ T.l i) (hj : 3≤ T.l j) (e₁ : T.l i%5=T.l j%5) (e₂ : T.l j%5=T.l k%5) :
    Routes J (T.verts : Set V):=by
  let a:=(T.pre i (t:=1) (by omega)).reverse
  let b:=T.post i (s:=1) (by omega)
  let c:=(T.post j (s:=2) (by omega)).reverse
  let d:=T.pre j (t:=2) (by omega)
  let p:=b.join c (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only })
  let q:=(a.join (T.arm k) (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only })).join c (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only })
  let r:=(b.join (T.arm k).reverse (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only })).join d (by classical { intro x;simp only [Set.mem_union,Theta.span,Set.mem_ofPred_eq,Theta.rim];intro hx hy;have hi:=T.inj;have hs:=T.start;have ht:=T.stop;have hm (i : Fin 3) (k : ℕ) (hk : k≤ T.l i) : T.f i k∈T.verts:=T.f_mem hk;grind only })
  exact qaf2 (p.mono (Set.union_subset T.span_mem T.span_mem))
    (q.mono (Set.union_subset (Set.union_subset T.span_mem T.span_mem) T.span_mem))
    (r.mono (Set.union_subset (Set.union_subset T.span_mem T.span_mem) T.span_mem))
    (by omega) (by omega) (by omega) (by omega)
private theorem residues (hg : Gir J) : Routes J (T.verts : Set V):=by
  by_cases h : Function.Injective (fun i=>T.l i%5)
  · exact ⟨T.a,T.b,T.a_ne_b,T.l,h,⟨fun i=>(T.arm i).mono T.span_mem⟩⟩
  obtain ⟨i,j,e,hij⟩ : ∃ i j,T.l i%5=T.l j%5∧i≠j:=by
    by_contra H
    exact h fun i j e=>by_contra fun h=>H ⟨i,j,e,h⟩
  obtain ⟨k,hki,hkj,_⟩:=third i j hij
  have:=T.girthArms hg hij
  have:=T.girthArms hg hki
  have:=T.girthArms hg hkj
  by_cases ek : T.l k%5=T.l i%5
  · by_cases hi : 3≤ T.l i
    · by_cases hj : 3≤ T.l j
      · exact T.allResidues hij hki.symm hkj.symm hi hj e (by omega)
      · exact T.allResidues hki.symm hij hkj hi (by omega) ek.symm (by omega)
    · exact T.allResidues hkj.symm hij.symm hki (by omega) (by omega) (by omega) ek
  · by_cases hi : 3≤ T.l i
    · exact T.twoResidues hij hki.symm hi e ek
    · exact T.twoResidues hij.symm hkj.symm (by omega) e.symm (by omega)
end Theta
private def kn (v : Fin 10) : List (Fin 10) :=
  ![[1,5,8],[0,2],[1,3,9],[2,4],[3,7,8],[0,6],[5,7,9],[4,6],[0,4],[2,6]] v
private def qao4 : ℕ→ Fin 10→ List (List (Fin 10))
  | 0,a=>[[a]]
  | n+1,a=>(kn a).flatMap fun b =>
      (qao4 n b).filterMap fun p=>if a∈p then none else some (a :: p)
private def Certificate (a b : Fin 10) (n : ℕ) (p : List (Fin 10)) : Prop :=
  p[0]! = a∧p[n]! = b∧(∀ i : Fin n,p[i.val+1]!∈kn p[i.val]!) ∧
    ∀ i j : Fin (n+1),p[i.val]! = p[j.val]!→ i=j
private instance (a b : Fin 10) (n : ℕ) (p : List (Fin 10)) :
    Decidable (Certificate a b n p):=by unfold Certificate;infer_instance
private theorem qao3 : ∀ a b : Fin 10,a≠b→ b∉kn a →
    ∃ n∈([2,3,4] : List ℕ),∃ p∈qao4 n a,Certificate a b n p:=by decide
private theorem qak2 : ∀ a b : Fin 10,a≠b →
    ∃ n∈([1,2,3,8] : List ℕ),∃ p∈qao4 n a,Certificate a b n p:=by decide
private theorem qar3 : ∀ a : Fin 10,(kn a).toFinset.card≤ 3:=by decide
private def Certificate.route {a b : Fin 10} {n : ℕ} {p : List (Fin 10)}
    (h : Certificate a b n p) (f : Fin 10→ V) (hf : Function.Injective f)
    (hE : ∀ i j,j∈kn i→ J.Adj (f i) (f j)) :
    Route J (Set.range f) (f a) (f b) n :=
  Route.ofTrace (fun k=>f p[k]!)
    ⟨fun k hk=>hE _ _ (h.2.2.1 ⟨k,hk⟩),fun i hi j hj he =>
      congrArg Fin.val (h.2.2.2 ⟨i,Nat.lt_succ_of_le hi⟩ ⟨j,Nat.lt_succ_of_le hj⟩ (hf he))⟩
    (congrArg f h.1) (congrArg f h.2.1) (fun k _=>⟨p[k]!,rfl⟩)
private def qn5 (T : Theta J) (i j k : Fin 3) (w : V) (x : Fin 10) : V :=
  if x.val≤ 4 then T.f i x.val else if x.val≤ 7 then T.f j (x.val-4)
  else if x.val=8 then T.f k 1 else w
namespace Theta
variable [DecidableEq V] {T : Theta J} {i j k : Fin 3} {w : V}
private theorem klabel_inj (hij : i≠j) (hki : k≠i) (hkj : k≠j)
    (hi : T.l i=4) (hj : T.l j=4) (hk : T.l k=2) (hw : w∉T.verts) :
    Function.Injective (qn5 T i j k w):=by
  intro x y h
  apply Fin.ext
  have hx:=x.isLt
  have hy:=y.isLt
  have hinj:=T.inj
  have hm (r : Fin 3) (s : ℕ) (hs : s≤ T.l r) : T.f r s∈T.verts:=f_mem hs
  simp only [qn5] at h
  split_ifs at h <;> grind only
omit [DecidableEq V] in
private theorem klabel_edges (hi : T.l i=4) (hj : T.l j=4) (hk : T.l k=2)
    (h₁ : J.Adj (T.f i 2) w) (h₂ : J.Adj w (T.f j 2)) :
    ∀ x y,y∈kn x→ J.Adj (qn5 T i j k w x) (qn5 T i j k w y):=by
  have ja : T.f j 0=T.f i 0:=(T.start j).trans (T.start i).symm
  have jb : T.f j 4=T.f i 4:=by simpa only [hi,hj] using (T.stop j).trans (T.stop i).symm
  have ka : T.f k 0=T.f i 0:=(T.start k).trans (T.start i).symm
  have kb : T.f k 2=T.f i 4:=by rw [← hk,T.stop,← hi,T.stop]
  have hi':=T.adj i
  have hj':=T.adj j
  have hk':=T.adj k
  have hs (u v : V) : J.Adj u v→ J.Adj v u:=Adj.symm
  intro x y h
  fin_cases x <;> fin_cases y
  all_goals try (exfalso;revert h;decide)
  all_goals
    norm_num [qn5]
    grind only
private theorem klabel_cover (hcov : ∀ r,r=i∨r=j∨r=k)
    (hi : T.l i=4) (hj : T.l j=4) (hk : T.l k=2) :
    Set.range (qn5 T i j k w)=↑(insert w T.verts):=by
  ext v
  constructor
  · rintro ⟨r,rfl⟩
    rw [Finset.mem_coe,Finset.mem_insert]
    unfold qn5
    split_ifs <;> first|exact Or.inl rfl|exact Or.inr (f_mem (by omega))
  · simp only [Finset.mem_coe,Finset.mem_insert,mem_verts]
    rintro (rfl|⟨r,m,hm,rfl⟩)
    · exact ⟨9,rfl⟩
    rcases hcov r with e|e|e <;> subst r
    · exact ⟨⟨m,by omega⟩,by simp [qn5,show m≤ 4 by omega]⟩
    · by_cases h₀ : m=0
      · exact ⟨0,by simp [qn5,h₀,T.start]⟩
      by_cases h₄ : m=4
      · exact ⟨4,by simpa [qn5,h₄,hi,hj] using (T.stop i).trans (T.stop j).symm⟩
      exact ⟨⟨m+4,by omega⟩,by simp [qn5,show ¬m+4≤ 4 by omega,show m+4≤ 7 by omega]⟩
    · have : m≤ 2:=by omega
      interval_cases m
      · exact ⟨0,by simp [qn5,T.start]⟩
      · exact ⟨8,rfl⟩
      · exact ⟨4,by simpa [qn5,hi,hk] using (T.stop i).trans (T.stop k).symm⟩
end Theta
private theorem qap0 [Fintype V] [DecidableEq V] [DecidableRel J.Adj] (hg : Gir J)
    (U : Finset V) (f : Fin 10→ V) (hf : Function.Injective f) (hU : Set.range f=↑U)
    (hE : ∀ a b,b∈kn a→ J.Adj (f a) (f b)) :
    (∀ x∈U,(J.neighborFinset x∩U).card≤ 3) ∧
    ∀ z,z∉U→ (J.neighborFinset z∩U).card≤ 1:=by
  constructor
  · intro x hx
    obtain ⟨a,rfl⟩ : x∈Set.range f:=hU.symm ▸ hx
    refine (Finset.card_le_card (t:=(kn a).toFinset.image f) ?_).trans
      (Finset.card_image_le.trans (qar3 a))
    intro y hy
    simp only [Finset.mem_inter,mem_neighborFinset] at hy
    obtain ⟨b,rfl⟩ : y∈Set.range f:=hU.symm ▸ hy.2
    refine Finset.mem_image.mpr ⟨b,List.mem_toFinset.mpr ?_,rfl⟩
    by_contra hn
    obtain ⟨n,hn',p,_,hp⟩:=qao3 a b (fun h=>hy.1.ne (congrArg f h)) hn
    simp at hn'
    have:=(hg _ ((hp.route f hf hE).cycle (Route.edge hy.1.symm) (by omega)
      (by intro y _ hy;simpa [or_comm] using hy))).1
    omega
  · intro z hz
    by_contra h
    obtain ⟨x,hx,y,hy,hxy⟩:=Finset.one_lt_card.mp (by omega : 1 < (J.neighborFinset z∩U).card)
    simp only [Finset.mem_inter,mem_neighborFinset] at hx hy
    obtain ⟨a,rfl⟩ : x∈Set.range f:=hU.symm ▸ hx.2
    obtain ⟨b,rfl⟩ : y∈Set.range f:=hU.symm ▸ hy.2
    obtain ⟨n,hn,p,_,hp⟩:=qak2 a b (fun e=>hxy (congrArg f e))
    simp at hn
    have hc:=(hp.route f hf hE).cycle (Route.via hy.1.symm hx.1 hxy.symm) (by omega) (by
      intro v hv hv'
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hv'
      rcases hv' with rfl|rfl|rfl
      · exact Or.inr rfl
      · exact (hz (show _∈(U : Set V) by rwa [← hU])).elim
      · exact Or.inl rfl)
    obtain ⟨h₁,h₂⟩:=hg _ hc
    omega
private theorem qal0 {A B : Set V} (hA : (J.induce A).Connected) (hAB : A⊆B)
    (hB : ∀ x∈B,x∈A∨∃ y∈A,J.Adj x y) : (J.induce B).Connected:=by
  obtain ⟨v⟩:=hA.nonempty
  have hreach : ∀ (y : V) (hy : y∈A),
      (J.induce B).Reachable ⟨v.1,hAB v.2⟩ ⟨y,hAB hy⟩:=by
    intro y hy
    exact (hA.preconnected v ⟨y,hy⟩).map (J.induceHomOfLE hAB).toHom
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨v.1,hAB v.2⟩,?_⟩
  rintro ⟨x,hx⟩
  rcases hB x hx with h|⟨y,hy,hxy⟩
  · exact hreach x h
  · exact (hreach y hy).trans (Adj.reachable (induce_adj.2 hxy.symm))
private theorem qaq1 [DecidableEq V] (T : Theta J) {w x y : V}
    (hx : x∈T.verts) (hy : y∈T.verts) (hne : x≠y)
    (ex : J.Adj w x) (ey : J.Adj w y) (S : Finset V) (hS : S.card < 2) :
    (J.induce ((↑(insert w T.verts) : Set V)\↑S)).Connected:=by
  have hs : (S : Set V).Subsingleton:=Finset.card_le_one.mp (by omega)
  refine qal0 (T.conn ↑S hs) (fun v hv=>⟨Finset.mem_insert_of_mem hv.1,hv.2⟩) ?_
  intro z hz
  rcases Finset.mem_insert.mp hz.1 with rfl|hT
  · by_cases h : x∈S
    · exact Or.inr ⟨y,⟨hy,fun h'=>hne (hs h h')⟩,ey⟩
    · exact Or.inr ⟨x,⟨hx,h⟩,ex⟩
  · exact Or.inl ⟨hT,hz.2⟩
private theorem Theta.induced [DecidableEq V] {T : Theta J} (hg : Gir J) (hmin : T.IsMin) :
    T.Ind:=by
  intro x hx y hy h
  by_contra he
  obtain ⟨i,s,hs,rfl⟩:=T.mem_verts.mp hx
  obtain ⟨j,t,ht,rfl⟩:=T.mem_verts.mp hy
  let p:=(Route.edge h).mono (B:=T.rim (T.f i s) (T.f j t))
    (by simp [Theta.rim,Set.insert_subset_iff])
  have h:=(T.minRoute hg hmin hs ht (by decide) (by decide) p (fun _=>he)).1
  omega
theorem thetaCore_H2 :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (J : SimpleGraph V)
      [DecidableRel J.Adj],
      (∀ v,4≤ J.degree v) →
      (∀ S : Finset V,S.card < 2→ (J.induce ((S : Set V)ᶜ)).Connected) →
      (∀ n∈({3,4,5,10} : Finset ℕ),n∉J.cycleLengths) →
      ∃ U : Finset V,2 < U.card ∧
        (∀ S : Finset V,S.card < 2 →
          (J.induce ((U : Set V)\(S : Set V))).Connected) ∧
        (∀ v∈U,(J.neighborFinset v∩U).card≤ 3) ∧
        (∀ v,v∉U→ (J.neighborFinset v∩U).card≤ 1) ∧
        ∃ x y : (U : Set V),x≠y ∧
          ∃ p : Fin 3→ (J.induce (U : Set V)).Walk x y,
            (∀ i,(p i).IsPath)∧Function.Injective (fun i=>(p i).length % 5):=by
  intro V _ _ J _ hdeg hconn hcyc
  have hg : Gir J:=by
    rintro n ⟨v,p,hp,rfl⟩
    have hl:=hp.three_le_length
    have hm : p.length∈J.cycleLengths:=⟨v,p,hp,rfl⟩
    refine ⟨?_,fun h=>hcyc _ (by simp [h]) hm⟩
    by_contra h
    rcases (show p.length=3∨p.length=4∨p.length=5 by omega) with e|e|e <;>
      exact hcyc _ (by simp [e]) hm
  have : Nonempty V:=by
    obtain ⟨v⟩:=(hconn ∅ (by simp)).nonempty
    exact ⟨v.val⟩
  obtain ⟨T,hmin⟩:=qaq3 hdeg
  by_cases h : ∃ w,w∉T.verts∧1 < (J.neighborFinset w∩T.verts).card
  · obtain ⟨w,hw,hn⟩:=h
    obtain ⟨x,hx,y,hy,hne⟩:=Finset.one_lt_card.mp hn
    simp only [Finset.mem_inter,mem_neighborFinset] at hx hy
    have hc:=qaq1 T hx.2 hy.2 hne hx.1 hy.1
    obtain ⟨i,s,hs,rfl⟩:=T.mem_verts.mp hx.2
    obtain ⟨j,t,ht,rfl⟩:=T.mem_verts.mp hy.2
    let p:=(Route.via hx.1.symm hy.1 hne).mono (B:=T.rim (T.f i s) (T.f j t))
      (by simp [Theta.rim,Set.insert_subset_iff,hw])
    obtain ⟨_,hij,rfl,rfl,hi,hj,hl⟩:=T.minRoute hg hmin hs ht (by decide) le_rfl p (by omega)
    obtain ⟨k,hki,hkj,hcov⟩:=Theta.third i j hij
    have hk:=hl k hki hkj
    obtain ⟨hd,he⟩:=qap0 hg _ _ (T.klabel_inj hij hki hkj hi hj hk hw)
      (T.klabel_cover hcov hi hj hk) (T.klabel_edges hi hj hk hx.1.symm hy.1)
    have hsub:=Finset.subset_insert w T.verts
    exact ⟨insert w T.verts,(T.large hg).trans_le (Finset.card_le_card hsub),hc,hd,he,
      (T.residues hg).paths hsub⟩
  · exact ⟨T.verts,T.large hg,fun S hS=>T.conn ↑S (Finset.card_le_one.mp (by omega)),
      fun _ hx=>T.deg (T.induced hg hmin) hx,fun w hw=>Nat.le_of_not_gt (fun h'=>h ⟨w,hw,h'⟩),
      (T.residues hg).paths subset_rfl⟩
end Dt
end M1
section M2
namespace DeanK5
open SimpleGraph
variable {V W : Type}
section Rc0
variable {G : SimpleGraph V}
def Rc0 (G : SimpleGraph V) (t : Finset V) (u v : V) : Prop :=
  ∃ p : G.Walk u v,∀ a∈p.support,a∈t
def Lk0 (G : SimpleGraph V) (t : Finset V) : Prop :=
  ∀ u∈t,∀ v∈t,Rc0 G t u v
theorem Rc0.refl {t : Finset V} {u : V} (hu : u∈t) : Rc0 G t u u :=
  ⟨Walk.nil,fun a ha=>by rw [Walk.mem_support_nil_iff] at ha;exact ha ▸ hu⟩
theorem Rc0.symm {t : Finset V} {u v : V} (h : Rc0 G t u v) : Rc0 G t v u:=by
  obtain ⟨p,hp⟩:=h
  exact ⟨p.reverse,fun a ha=>hp a (by simpa using ha)⟩
theorem Rc0.trans {t : Finset V} {u v w : V} (h₁ : Rc0 G t u v) (h₂ : Rc0 G t v w) :
    Rc0 G t u w:=by
  obtain ⟨p,hp⟩:=h₁
  obtain ⟨q,hq⟩:=h₂
  refine ⟨p.append q,fun a ha=>?_⟩
  rcases (Walk.mem_support_append_iff p q).mp ha with ha|ha
  exacts [hp a ha,hq a ha]
theorem Rc0.adj {t : Finset V} {u v : V} (hu : u∈t) (hv : v∈t) (h : G.Adj u v) :
    Rc0 G t u v :=
  ⟨Walk.cons h Walk.nil,fun a ha=>by
    simp only [Walk.support_cons,Walk.support_nil,List.mem_cons,List.not_mem_nil,
      or_false] at ha
    rcases ha with rfl|rfl <;> assumption⟩
theorem Rc0.mono {s t : Finset V} {u v : V} (hst : s⊆t) (h : Rc0 G s u v) :
    Rc0 G t u v:=by
  obtain ⟨p,hp⟩:=h
  exact ⟨p,fun a ha=>hst (hp a ha)⟩
theorem Rc0.left_mem {t : Finset V} {u v : V} (h : Rc0 G t u v) : u∈t :=
  h.elim fun p hp=>hp u p.start_mem_support
theorem Rc0.right_mem {t : Finset V} {u v : V} (h : Rc0 G t u v) : v∈t :=
  h.elim fun p hp=>hp v p.end_mem_support
theorem qai3 {H : SimpleGraph W} (f : V→ W) {u v : V} (p : G.Walk u v)
    (hf : ∀ a∈p.support,∀ b∈p.support,G.Adj a b→ f a=f b∨H.Adj (f a) (f b)) :
    ∃ q : H.Walk (f u) (f v),∀ c∈q.support,∃ a∈p.support,f a=c:=by
  induction p with
  | nil=>exact ⟨Walk.nil,fun c hc =>
      ⟨_,Walk.start_mem_support _,(Walk.mem_support_nil_iff.mp hc).symm⟩⟩
  | @cons a b w h p ih =>
    obtain ⟨q,hq⟩:=ih fun x hx y hy hxy=>hf x (by simp [hx]) y (by simp [hy]) hxy
    have hq' : ∀ c∈q.support,∃ x∈(Walk.cons h p).support,f x=c:=fun c hc=>by
      obtain ⟨x,hx,rfl⟩:=hq c hc
      exact ⟨x,by simp [hx],rfl⟩
    rcases hf a (by simp) b (by simp) h with he|he
    · exact ⟨q.copy he.symm rfl,fun c hc=>hq' c (by simpa using hc)⟩
    · refine ⟨Walk.cons he q,fun c hc=>?_⟩
      rw [Walk.support_cons,List.mem_cons] at hc
      rcases hc with rfl|hc
      exacts [⟨a,by simp,rfl⟩,hq' c hc]
theorem Rc0.proj {H : SimpleGraph W} (f : V→ W) {s : Finset V}
    {t : Finset W} {u v : V}
    (hf : ∀ a∈s,∀ b∈s,G.Adj a b→ f a=f b∨H.Adj (f a) (f b))
    (hst : ∀ a∈s,f a∈t) (h : Rc0 G s u v) : Rc0 H t (f u) (f v):=by
  obtain ⟨p,hp⟩:=h
  obtain ⟨q,hq⟩:=qai3 (H:=H) f p fun a ha b hb=>hf a (hp a ha) b (hp b hb)
  refine ⟨q,fun c hc=>?_⟩
  obtain ⟨a,ha,rfl⟩:=hq c hc
  exact hst a (hp a ha)
theorem Rc0.map {H : SimpleGraph W} (f : G →g H) {s : Finset V}
    {t : Finset W} {u v : V} (hst : ∀ a∈s,f a∈t) (h : Rc0 G s u v) :
    Rc0 H t (f u) (f v) :=
  h.proj f (fun _ _ _ _ hab=>Or.inr (f.map_adj hab)) hst
theorem Rc0.mono_graph {H : SimpleGraph V} (hle : G≤ H) {t : Finset V} {u v : V}
    (h : Rc0 G t u v) : Rc0 H t u v:=by
  obtain ⟨p,hp⟩:=h
  exact ⟨p.mapLe hle,fun a ha=>hp a (by simpa using ha)⟩
theorem qa4 {t : Finset V} (c : V) (h : ∀ v∈t,Rc0 G t c v) : Lk0 G t :=
  fun u hu v hv=>(h u hu).symm.trans (h v hv)
theorem Lk0.mono_graph {H : SimpleGraph V} (hle : G≤ H) {t : Finset V}
    (h : Lk0 G t) : Lk0 H t :=
  fun u hu v hv=>(h u hu v hv).mono_graph hle
theorem qg2 (t : Finset V) {u : V} (hu : u∈t) :
    ∃ R⊆t,u∈R∧(∀ a∈R,∀ d∈t,G.Adj a d→ d∈R)∧∀ a∈R,Rc0 G t u a:=by
  classical
  refine ⟨t.filter (Rc0 G t u),Finset.filter_subset _ _,
    Finset.mem_filter.mpr ⟨hu,Rc0.refl hu⟩,fun a ha d hd had=>?_,
    fun a ha=>(Finset.mem_filter.mp ha).2⟩
  have ha':=Finset.mem_filter.mp ha
  exact Finset.mem_filter.mpr ⟨hd,ha'.2.trans (Rc0.adj ha'.1 hd had)⟩
theorem qg6 {t : Finset V} (h : ¬ Lk0 G t) :
    ∃ R⊆t,R.Nonempty∧(∃ v∈t,v∉R)∧∀ a∈R,∀ d∈t,G.Adj a d→ d∈R:=by
  simp only [Lk0,not_forall] at h
  obtain ⟨u,hu,v,hv,huv⟩:=h
  obtain ⟨R,hRt,huR,hcl,hreach⟩:=qg2 (G:=G) t hu
  exact ⟨R,hRt,⟨u,huR⟩,⟨v,hv,fun hvR=>huv (hreach v hvR)⟩,hcl⟩
theorem qb9 {C : Finset V} {D : V→ Prop}
    (hC : ∀ c∈C,∀ w,G.Adj c w→ w∈C∨D w) :
    ∀ {u v : V} (p : G.Walk u v),u∈C→ (∀ a∈p.support,¬ D a) →
      ∀ a∈p.support,a∈C:=by
  intro u v p
  induction p with
  | nil =>
    intro hu _ a ha
    rw [Walk.mem_support_nil_iff] at ha
    exact ha ▸ hu
  | @cons a b c h p ih =>
    intro hu hD x hx
    have hb : b∈C:=(hC a hu b h).resolve_right (hD b (by simp))
    rw [Walk.support_cons,List.mem_cons] at hx
    rcases hx with rfl|hx
    · exact hu
    · exact ih hb (fun y hy=>hD y (by simp [hy])) x hx
theorem qab4 [DecidableEq V] {C : Finset V} {g v : V} (hC : ∀ c∈C,∀ w,G.Adj c w→ w∈C∨w=g)
    {p : G.Walk g v} (hp : p.IsPath) (hg : g∉C) (hv : v∉C) : ∀ a∈p.support,a∉C:=by
  cases p with
  | nil =>
    intro a ha
    rw [Walk.mem_support_nil_iff] at ha
    exact ha ▸ hg
  | cons h q =>
    intro a ha haC
    rw [Walk.cons_isPath_iff] at hp
    rw [Walk.support_cons,List.mem_cons] at ha
    rcases ha with rfl|ha
    · exact hg haC
    · exact hv (qb9 (D:=(·=g)) hC (q.dropUntil a ha) haC
        (fun y hy hyg=>hp.2 (hyg ▸ q.support_dropUntil_subset_support ha hy)) _
        (Walk.end_mem_support _))
theorem qv2 {H : SimpleGraph W} (f : G ↪g H) :
    ∀ {a b : W} (p : H.Walk a b) (u v : V),f u=a→ f v=b →
      (∀ c∈p.support,c∈Set.range f) →
      ∃ q : G.Walk u v,q.length=p.length∧q.support.map f=p.support:=by
  intro a b p
  induction p with
  | nil =>
    intro u v hu hv _
    obtain rfl : u=v:=f.injective (hu.trans hv.symm)
    exact ⟨Walk.nil,rfl,by simp [hu]⟩
  | @cons a c b h p ih =>
    intro u v hu hv hr
    obtain ⟨t,rfl⟩:=hr c (by simp)
    obtain ⟨q,hl,hs⟩:=ih t v rfl hv fun x hx=>hr x (by simp [hx])
    subst hu
    exact ⟨Walk.cons (f.map_adj_iff.mp h) q,by simp [hl],by simp [hs]⟩
theorem qe9 (S : V→ Prop) :
    ∀ {u v : V} (p : G.Walk u v),S v→ ∃ r,S r∧∃ q : G.Walk u r,
      (∀ t∈q.support,t∈p.support)∧(∀ t∈q.support,S t→ t=r) ∧
      (p.IsPath→ q.IsPath):=by
  classical
  intro u v p
  induction p with
  | nil=>exact fun hv=>⟨_,hv,Walk.nil,fun t ht=>ht,fun t ht _=>by simpa using ht,
      fun _=>Walk.IsPath.nil⟩
  | @cons a b c h p ih =>
    intro hc
    by_cases ha : S a
    · exact ⟨a,ha,Walk.nil,fun t ht=>by simp_all,fun t ht _=>by simpa using ht,
        fun _=>Walk.IsPath.nil⟩
    obtain ⟨r,hr,q,hq,hqS,hqp⟩:=ih hc
    refine ⟨r,hr,Walk.cons h q,fun t ht=>?_,fun t ht hS=>?_,fun hp=>?_⟩
    · rw [Walk.support_cons,List.mem_cons] at ht ⊢
      exact ht.imp_right (hq t)
    · rw [Walk.support_cons,List.mem_cons] at ht
      rcases ht with rfl|ht
      exacts [absurd hS ha,hqS t ht hS]
    · rw [Walk.cons_isPath_iff] at hp ⊢
      exact ⟨hqp hp.1,fun hm=>hp.2 (hq a hm)⟩
theorem qg3 {s : Finset V} (h : (G.induce (s : Set V)).Connected) :
    Lk0 G s:=by
  intro u hu v hv
  obtain ⟨p⟩:=h ⟨u,hu⟩ ⟨v,hv⟩
  let e : G.induce (s : Set V) ↪g G:=Embedding.induce _
  refine ⟨p.map e.toHom,fun a ha=>?_⟩
  have ha' : a∈(p.map e.toHom).support:=ha
  rw [Walk.support_map,List.mem_map] at ha'
  obtain ⟨b,-,rfl⟩:=ha'
  exact b.2
theorem qd1 {s : Finset V} (hne : s.Nonempty) (h : Lk0 G s) :
    (G.induce (s : Set V)).Connected:=by
  obtain ⟨c,hc⟩:=hne
  have key : ∀ v : (s : Set V),(G.induce (s : Set V)).Reachable ⟨c,hc⟩ v:=fun v=>by
    obtain ⟨p,hp⟩:=h c hc v.1 v.2
    exact ⟨p.induce _ fun a ha=>Finset.mem_coe.mpr (hp a ha)⟩
  have : Nonempty (s : Set V):=⟨⟨c,hc⟩⟩
  exact ⟨fun u v=>(key u).symm.trans (key v)⟩
end Rc0
section KConnBasics
variable {G : SimpleGraph V}
theorem qf8 [Fintype V] (h : 2 < Fintype.card V) (u v : V) : ∃ w,w≠u∧w≠v:=by
  classical
  obtain ⟨w,-,hw⟩:=Finset.exists_mem_notMem_of_card_lt_card (s:={u,v})
    (t:=Finset.univ) (by rw [Finset.card_univ];exact lt_of_le_of_lt Finset.card_le_two h)
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hw
  exact ⟨w,hw.1,hw.2⟩
theorem qy6 [Fintype V] {k₁ k₂ : ℕ} (hk : k₁≤ k₂) (h : Kc0 G k₂) : Kc0 G k₁ :=
  ⟨lt_of_le_of_lt hk h.1,fun S hS=>h.2 S (lt_of_lt_of_le hS hk)⟩
theorem kConn_iff_linked [Fintype V] [DecidableEq V] {k : ℕ} :
    Kc0 G k↔k < Fintype.card V∧∀ S : Finset V,S.card < k→ Lk0 G Sᶜ:=by
  refine and_congr_right fun hk=>forall_congr' fun S=>imp_congr_right fun hS=>?_
  have hcoe : ((Sᶜ : Finset V) : Set V)=(S : Set V)ᶜ:=Finset.coe_compl S
  constructor
  · intro h
    apply qg3
    rw [hcoe]
    exact h
  · intro h
    have hne : (Sᶜ : Finset V).Nonempty:=by
      by_contra hne
      rw [Finset.not_nonempty_iff_eq_empty,Finset.compl_eq_empty_iff] at hne
      rw [hne,Finset.card_univ] at hS
      omega
    rw [← hcoe]
    exact qd1 hne h
theorem kConn_two_iff [Fintype V] [DecidableEq V] :
    Kc0 G 2↔2 < Fintype.card V∧∀ w : V,Lk0 G (Finset.univ.erase w):=by
  rw [kConn_iff_linked]
  refine and_congr_right fun hc=>⟨fun h w=>?_,fun h S hS=>?_⟩
  · have:=h {w} (by simp)
    rwa [Finset.compl_singleton] at this
  · rcases (by omega : S.card=0∨S.card=1) with h0|h1
    · rw [Finset.card_eq_zero] at h0
      subst h0
      intro u _ v _
      obtain ⟨w,hwu,hwv⟩:=qf8 hc u v
      exact (h w u (by simp [hwu.symm]) v (by simp [hwv.symm])).mono (by simp)
    · obtain ⟨w,rfl⟩:=Finset.card_eq_one.mp h1
      rw [Finset.compl_singleton]
      exact h w
theorem kConn_one_iff [Fintype V] : Kc0 G 1↔1 < Fintype.card V∧G.Connected:=by
  classical
  rw [kConn_iff_linked]
  refine and_congr_right fun hc=>⟨fun h=>?_,fun h S hS=>?_⟩
  · have hl:=h ∅ (by simp)
    rw [Finset.compl_empty] at hl
    have : Nonempty V:=Fintype.card_pos_iff.mp (by omega)
    exact ⟨fun u v=>(hl u (by simp) v (by simp)).elim fun p _=>⟨p⟩⟩
  · rw [Nat.lt_one_iff,Finset.card_eq_zero] at hS
    subst hS
    intro u _ v _
    obtain ⟨p⟩:=h.preconnected u v
    exact ⟨p,by simp⟩
theorem qc7 [Fintype V] (h : Kc0 G 2) : G.Connected :=
  (kConn_one_iff.mp (qy6 (by norm_num) h)).2
theorem qe8 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {k : ℕ}
    (h : Kc0 G k) (v : V) : k≤ G.degree v:=by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨hk,hl⟩:=kConn_iff_linked.mp h
  have hN : (G.neighborFinset v).card < k:=by rwa [card_neighborFinset_eq_degree]
  obtain ⟨w,-,hw⟩:=Finset.exists_mem_notMem_of_card_lt_card
    (s:=insert v (G.neighborFinset v)) (t:=Finset.univ)
    (by rw [Finset.card_univ];exact lt_of_le_of_lt (Finset.card_insert_le _ _) (by omega))
  rw [Finset.mem_insert,not_or] at hw
  obtain ⟨p,hp⟩:=hl _ hN v (by simp) w (Finset.mem_compl.mpr hw.2)
  cases p with
  | nil=>exact hw.1 rfl
  | cons ha q =>
    exact Finset.mem_compl.mp (hp _ (by simp)) ((G.mem_neighborFinset _ _).mpr ha)
theorem qf1 [Fintype V] [Fintype W] {H : SimpleGraph W} (f : G →g H)
    (hf : Function.Bijective f) {k : ℕ} (h : Kc0 G k) : Kc0 H k:=by
  classical
  obtain ⟨hk,hl⟩:=kConn_iff_linked.mp h
  refine kConn_iff_linked.mpr ⟨by rw [← Fintype.card_of_bijective hf];exact hk,
    fun S hS u hu v hv=>?_⟩
  obtain ⟨u,rfl⟩:=hf.2 u
  obtain ⟨v,rfl⟩:=hf.2 v
  have hT : (Finset.univ.filter fun a=>f a∈S).card < k :=
    lt_of_le_of_lt (Finset.card_le_card_of_injOn f (fun a ha=>by simpa using ha)
      hf.1.injOn) hS
  exact (hl _ hT u (by simpa using hu) v (by simpa using hv)).map f
    (fun a ha=>by simpa using ha)
theorem qs4 [Fintype V] [Fintype W] {H : SimpleGraph W} (e : G ≃g H) {k : ℕ}
    (h : Kc0 G k) : Kc0 H k :=
  qf1 e.toHom e.bijective h
theorem qao5 [Fintype V] [Fintype W] {H : SimpleGraph W} (e : G ≃g H) {x y : V}
    (h : Rt0 G x y) : Rt0 H (e x) (e y):=by
  refine ⟨e.injective.ne h.1,
    qf1 (G:=G ⊔ edge x y) ⟨fun a=>e a,fun {a b} hab=>?_⟩ e.bijective h.2⟩
  simp only [sup_adj,edge_adj] at hab ⊢
  rcases hab with hab|⟨hab,hne⟩
  · exact Or.inl (e.map_adj_iff.mpr hab)
  · refine Or.inr ⟨?_,e.injective.ne hne⟩
    rcases hab with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    exacts [Or.inl ⟨rfl,rfl⟩,Or.inr ⟨rfl,rfl⟩]
theorem qh5 [Fintype V] [DecidableEq V] {k r : ℕ} (T : Finset V)
    (hT : T.card≤ r) (h : Kc0 G (k+r)) : Kc0 (G.induce ((T : Set V)ᶜ)) k:=by
  classical
  obtain ⟨hk,hl⟩:=kConn_iff_linked.mp h
  refine kConn_iff_linked.mpr ⟨?_,fun S hS u hu v hv=>?_⟩
  · have hTc : Fintype.card (T : Set V)=T.card:=by simp
    rw [Fintype.card_compl_set,hTc]
    omega
  have hcard : (T∪S.image Subtype.val).card < k+r :=
    lt_of_le_of_lt (Finset.card_union_le _ _) (by
      have:=Finset.card_image_le (s:=S) (f:=Subtype.val)
      omega)
  have hnot : ∀ a : ((T : Set V)ᶜ : Set V),a∉S→ a.1∉T∪S.image Subtype.val:=by
    intro a ha hm
    rcases Finset.mem_union.mp hm with hm|hm
    · exact a.2 hm
    · obtain ⟨b,hb,hba⟩:=Finset.mem_image.mp hm
      exact ha (Subtype.ext hba ▸ hb)
  obtain ⟨p,hp⟩:=hl _ hcard u.1 (Finset.mem_compl.mpr (hnot u (Finset.mem_compl.mp hu)))
    v.1 (Finset.mem_compl.mpr (hnot v (Finset.mem_compl.mp hv)))
  have hpT : ∀ a∈p.support,a∈((T : Set V)ᶜ):=fun a ha h' =>
    Finset.mem_compl.mp (hp a ha) (Finset.mem_union_left _ h')
  refine ⟨p.induce _ hpT,fun a ha=>?_⟩
  have ha' : a∈(p.induce _ hpT).support:=ha
  rw [Walk.support_induce,List.mem_attachWith] at ha'
  refine Finset.mem_compl.mpr fun haS=>Finset.mem_compl.mp (hp _ ha') ?_
  exact Finset.mem_union_right _ (Finset.mem_image_of_mem _ haS)
theorem qw2 {s t : Set V} [Fintype s] [Fintype t] (hst : s=t) {k : ℕ}
    (h : Kc0 (G.induce s) k) : Kc0 (G.induce t) k:=by
  subst hst
  convert h
theorem qaj6 [Fintype V] [DecidableEq V] {k : ℕ} (h : Kc0 G (k+1))
    (v : V) : Kc0 (G.induce ({v}ᶜ : Set V)) k :=
  qw2 (by rw [Finset.coe_singleton]) (qh5 {v} (by simp) h)
theorem qq9 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {k : ℕ}
    (h : Kc0 G k) {Q U : Finset V} (hQ : Q.Nonempty) (hU : U.Nonempty) (hQU : Disjoint Q U)
    (hno : ∀ q∈Q,∀ u∈U,¬ G.Adj q u) :
    k≤ ((Q.biUnion fun q=>G.neighborFinset q)\Q).card:=by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨q,hq⟩:=hQ
  obtain ⟨u,hu⟩:=hU
  have huS : u∈((Q.biUnion fun q=>G.neighborFinset q)\Q)ᶜ:=Finset.mem_compl.mpr fun hm=>by
    obtain ⟨q',hq',hadj⟩:=Finset.mem_biUnion.mp (Finset.mem_sdiff.mp hm).1
    exact hno q' hq' u hu ((G.mem_neighborFinset _ _).mp hadj)
  obtain ⟨p,hp⟩:=(kConn_iff_linked.mp h).2 _ hlt q
    (Finset.mem_compl.mpr fun hm=>(Finset.mem_sdiff.mp hm).2 hq) u huS
  have hC : ∀ c∈Q,∀ w,G.Adj c w→ w∈Q∨w∈(Q.biUnion fun q=>G.neighborFinset q)\Q :=
    fun c hc w hw=>by
      by_cases hwQ : w∈Q
      · exact Or.inl hwQ
      · exact Or.inr (Finset.mem_sdiff.mpr
          ⟨Finset.mem_biUnion.mpr ⟨c,hc,(G.mem_neighborFinset _ _).mpr hw⟩,hwQ⟩)
  have:=qb9 hC p hq (fun a ha=>Finset.mem_compl.mp (hp a ha)) u p.end_mem_support
  exact Finset.disjoint_left.mp hQU this hu
theorem ql8 (hG : G.Connected) {Q S : Finset V} (hQ : Q.Nonempty) (hS : S.Nonempty)
    (hQS : Disjoint Q S) (hcl : ∀ q∈Q,∀ w,G.Adj q w→ w∈Q∨w∈S) :
    ∃ q∈Q,∃ s∈S,G.Adj q s:=by
  obtain ⟨q,hq⟩:=hQ
  obtain ⟨s,hs⟩:=hS
  obtain ⟨p⟩:=hG.preconnected q s
  obtain ⟨d,-,hd1,hd2⟩ :=
    p.exists_boundary_dart (Q : Set V) hq fun h=>Finset.disjoint_left.mp hQS h hs
  exact ⟨d.fst,hd1,d.snd,(hcl _ hd1 _ d.adj).resolve_left hd2,d.adj⟩
end KConnBasics
section Adjoin
variable {G : SimpleGraph V}
def av0 (G : SimpleGraph V) (Z : Finset V) : SimpleGraph (Option V) where
  Adj a b:=match a,b with
    | some u,some v=>G.Adj u v
    | none,some v=>v∈Z
    | some u,none=>u∈Z
    | none,none=>False
  symm:=⟨by
    rintro (_|a) (_|b) h
    exacts [h,h,h,h.symm]⟩
  loopless:=⟨by
    rintro (_|a) h
    exacts [h,G.irrefl h]⟩
@[simp] theorem adjoin_adj_some {Z : Finset V} {u v : V} :
    (av0 G Z).Adj (some u) (some v)↔G.Adj u v:=Iff.rfl
@[simp] theorem adjoin_adj_none_some {Z : Finset V} {v : V} :
    (av0 G Z).Adj none (some v)↔v∈Z:=Iff.rfl
@[simp] theorem adjoin_adj_some_none {Z : Finset V} {v : V} :
    (av0 G Z).Adj (some v) none↔v∈Z:=Iff.rfl
@[simp] theorem adjoin_not_adj_none {Z : Finset V} : ¬ (av0 G Z).Adj none none:=id
instance [DecidableEq V] [DecidableRel G.Adj] (Z : Finset V) :
    DecidableRel (av0 G Z).Adj:=fun a b =>
  match a,b with
  | some u,some v=>inferInstanceAs (Decidable (G.Adj u v))
  | none,some v=>inferInstanceAs (Decidable (v∈Z))
  | some u,none=>inferInstanceAs (Decidable (u∈Z))
  | none,none=>inferInstanceAs (Decidable False)
def qab2 (G : SimpleGraph V) (Z : Finset V) : G ↪g av0 G Z where
  toFun:=some
  inj':=Option.some_injective V
  map_rel_iff':=Iff.rfl
@[simp] theorem coe_someEmb {Z : Finset V} : ⇑(qab2 G Z)=some:=rfl
theorem qi2 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (Z : Finset V)
    (v : V) : (av0 G Z).degree (some v)=G.degree v+if v∈Z then 1 else 0:=by
  rw [← card_neighborFinset_eq_degree,← card_neighborFinset_eq_degree,
    neighborFinset_eq_filter,neighborFinset_eq_filter,Finset.card_filter,Finset.card_filter,
    Fintype.sum_option]
  simp [add_comm]
theorem qam6 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] (Z : Finset V) :
    (av0 G Z).degree none=Z.card:=by
  rw [← card_neighborFinset_eq_degree,neighborFinset_eq_filter,Finset.card_filter,
    Fintype.sum_option]
  simp
theorem qm5 [Fintype V] {Z : Finset V} (h : Kc0 G 2) (hZ : 2≤ Z.card) :
    Kc0 (av0 G Z) 2:=by
  classical
  obtain ⟨hc,hl⟩:=kConn_two_iff.mp h
  have hconn:=qc7 h
  refine kConn_two_iff.mpr ⟨by rw [Fintype.card_option];omega,fun w=>?_⟩
  cases w with
  | none =>
    obtain ⟨c⟩:=hconn.nonempty
    refine qa4 (some c) fun v hv=>?_
    obtain ⟨v,rfl⟩:=Option.ne_none_iff_exists'.mp (Finset.ne_of_mem_erase hv)
    obtain ⟨p⟩:=hconn.preconnected c v
    exact Rc0.map (qab2 G Z).toHom (s:=Finset.univ) (fun a _=>by simp) ⟨p,by simp⟩
  | some w =>
    refine qa4 none fun v hv=>?_
    cases v with
    | none=>exact Rc0.refl (by simp)
    | some v =>
      obtain ⟨z,hz,hzw⟩:=Finset.exists_mem_ne hZ w
      have hv' : v≠w:=fun h'=>Finset.ne_of_mem_erase hv (h' ▸ rfl)
      refine (Rc0.adj (by simp) (by simpa using hzw)
        (show (av0 G Z).Adj none (some z) from hz)).trans ?_
      exact (hl w z (by simpa using hzw) v (by simpa using hv')).map (qab2 G Z).toHom
        (fun a ha=>by simpa using ha)
theorem qad9 (G : SimpleGraph V) (Z : Finset V) (x y : V) :
    av0 G Z ⊔ edge (some x) (some y)=av0 (G ⊔ edge x y) Z:=by
  ext a b
  cases a <;> cases b <;> simp [edge_adj]
theorem qt6 [Fintype V] {Z : Finset V} {x y : V} (h : Rt0 G x y)
    (hZ : 2≤ Z.card) : Rt0 (av0 G Z) (some x) (some y) :=
  ⟨by simpa using h.1,by rw [qad9];exact qm5 h.2 hZ⟩
end Adjoin
section Induced
variable {G : SimpleGraph V}
theorem qg8 [DecidableEq V] (s : Finset V) (hc : 2 < s.card)
    (h : ∀ w∈s,Lk0 G (s.erase w)) : Kc0 (G.induce (s : Set V)) 2:=by
  classical
  refine kConn_two_iff.mpr ⟨by simpa using hc,fun w u hu v hv=>?_⟩
  obtain ⟨p,hp⟩:=h w.1 w.2 u.1
    (Finset.mem_erase.mpr ⟨fun h'=>Finset.ne_of_mem_erase hu (Subtype.ext h'),u.2⟩) v.1
    (Finset.mem_erase.mpr ⟨fun h'=>Finset.ne_of_mem_erase hv (Subtype.ext h'),v.2⟩)
  have hps : ∀ a∈p.support,a∈(s : Set V):=fun a ha =>
    Finset.mem_coe.mpr (Finset.mem_of_mem_erase (hp a ha))
  refine ⟨p.induce _ hps,fun a ha=>?_⟩
  have ha' : a∈(p.induce _ hps).support:=ha
  rw [Walk.support_induce,List.mem_attachWith] at ha'
  exact Finset.mem_erase.mpr
    ⟨fun h'=>Finset.ne_of_mem_erase (hp _ ha') (congrArg Subtype.val h'),Finset.mem_univ _⟩
theorem qac1 (s : Set V) {x y : V} (hx : x∈s) (hy : y∈s) :
    (G ⊔ edge x y).induce s=G.induce s ⊔ edge ⟨x,hx⟩ ⟨y,hy⟩:=by
  ext a b
  simp [edge_adj,Subtype.ext_iff]
theorem qb4 [DecidableEq V] {s : Finset V} {x y : V} (hxy : x≠y)
    (hc : 2 < s.card) (h : ∀ w∈s,Lk0 (G ⊔ edge x y) (s.erase w)) (hx : x∈s)
    (hy : y∈s) : Rt0 (G.induce (s : Set V)) ⟨x,hx⟩ ⟨y,hy⟩ :=
  ⟨fun h'=>hxy (congrArg Subtype.val h'),by
    rw [← qac1]
    exact qg8 s hc h⟩
def de0 (G : SimpleGraph V) (u v : V) : SimpleGraph V:=G\edge u v
theorem rooted_delEdge_iff [Fintype V] {x y : V} : Rt0 (de0 G x y) x y↔Rt0 G x y:=by
  unfold Rt0 de0
  rw [sdiff_sup_self]
theorem qe3 {x y : V} {t : Finset V} {u v : V} (hx : x∉t∨y∉t)
    (h : Rc0 (G ⊔ edge x y) t u v) : Rc0 G t u v :=
  h.proj (H:=G) id (fun a ha b hb hab=>by
    simp only [sup_adj,edge_adj] at hab
    rcases hab with hab|⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,-⟩
    · exact Or.inr hab
    · exact (hx.elim (fun h=>h ha) (fun h=>h hb)).elim
    · exact (hx.elim (fun h=>h hb) (fun h=>h ha)).elim) (fun a ha=>ha)
theorem qu9 [Fintype V] [DecidableEq V] {x y : V} (h : Rt0 G x y) :
    G.Connected:=by
  obtain ⟨hc,hl⟩:=kConn_two_iff.mp h.2
  have hx : ∀ a,a≠y→ G.Reachable a x:=fun a ha =>
    (qe3 (Or.inr (Finset.notMem_erase y _))
      (hl y a (by simp [ha]) x (by simp [h.1]))).elim fun p _=>⟨p⟩
  have hy : ∀ a,a≠x→ G.Reachable a y:=fun a ha =>
    (qe3 (Or.inl (Finset.notMem_erase x _))
      (hl x a (by simp [ha]) y (by simp [h.1.symm]))).elim fun p _=>⟨p⟩
  obtain ⟨t,htx,hty⟩:=qf8 hc x y
  have hxy : G.Reachable x y:=(hx t hty).symm.trans (hy t htx)
  have : Nonempty V:=⟨x⟩
  have hall : ∀ a,G.Reachable a x:=fun a =>
    if hay : a=y then hay ▸ hxy.symm else hx a hay
  exact ⟨fun a b=>(hall a).trans (hall b).symm⟩
end Induced
section EndBlocks
variable {G : SimpleGraph V}
def Ieb0 (G : SimpleGraph V) (B : Finset V) (b : V) : Prop :=
  b∈B∧2≤ B.card∧(∀ v∈B,v≠b→ ∀ w,G.Adj v w→ w∈B) ∧
    (2=B.card∨Kc0 (G.induce (B : Set V)) 2)
theorem ql3 [DecidableEq V] {B : Finset V} {b : V} (hB : Ieb0 G B b) :
    ∀ c∈B.erase b,∀ d,G.Adj c d→ d∈B.erase b∨d=b:=fun c hc d hd=>by
  have hdB:=hB.2.2.1 c (Finset.mem_of_mem_erase hc) (Finset.ne_of_mem_erase hc) d hd
  by_cases hdb : d=b
  · exact Or.inr hdb
  · exact Or.inl (Finset.mem_erase.mpr ⟨hdb,hdB⟩)
theorem kConn_induce_univ_iff [Fintype V] {k : ℕ} :
    Kc0 (G.induce ((Finset.univ : Finset V) : Set V)) k↔Kc0 G k:=by
  constructor
  · intro h
    refine qf1 (Embedding.induce _).toHom ⟨fun a b hab=>Subtype.ext hab,
      fun v=>⟨⟨v,Finset.mem_coe.mpr (Finset.mem_univ v)⟩,rfl⟩⟩ h
  · intro h
    refine qf1 (H:=G.induce ((Finset.univ : Finset V) : Set V))
      ⟨fun v=>⟨v,Finset.mem_coe.mpr (Finset.mem_univ v)⟩,fun hab=>hab⟩
      ⟨fun a b hab=>congrArg Subtype.val hab,fun v=>⟨v.1,rfl⟩⟩ h
theorem qac0 [Fintype V] (h : Kc0 G 2) (b : V) : Ieb0 G Finset.univ b:=by
  refine ⟨Finset.mem_univ b,?_,fun _ _ _ w _=>Finset.mem_univ w,Or.inr ?_⟩
  · rw [Finset.card_univ]
    exact h.1.le
  · exact kConn_induce_univ_iff.mpr h
theorem qc8 [DecidableEq V] :
    ∀ (C : Finset V) (b : V),b∉C→ C.Nonempty →
      (∀ c∈C,∀ w,G.Adj c w→ w∈C∨w=b) →
      ∃ B b',Ieb0 G B b'∧B.erase b'⊆C∧b'∈insert b C:=by
  intro C
  induction C using Finset.strongInduction with
  | H C ih =>
  intro b hb hne hcl
  have hBc : (insert b C).card=C.card+1:=Finset.card_insert_of_notMem hb
  have hC1 : 1≤ C.card:=hne.card_pos
  by_cases hgood : ∀ w∈insert b C,Lk0 G ((insert b C).erase w)
  · refine ⟨insert b C,b,⟨Finset.mem_insert_self b C,by omega,fun v hv hvb w hw=>?_,?_⟩,
      by rw [Finset.erase_insert hb],Finset.mem_insert_self b C⟩
    · rcases hcl v ((Finset.mem_insert.mp hv).resolve_left hvb) w hw with h'|rfl
      exacts [Finset.mem_insert_of_mem h',Finset.mem_insert_self _ _]
    · by_cases h2 : C.card=1
      · exact Or.inl (by omega)
      · exact Or.inr (qg8 _ (by omega) hgood)
  simp only [not_forall] at hgood
  obtain ⟨w,hw,hbad⟩:=hgood
  obtain ⟨R,hRs,hRne,⟨v,hvs,hvR⟩,hRcl⟩:=qg6 hbad
  have hmem : ∀ a∈(insert b C).erase w,a≠b→ a∈C:=fun a ha hab =>
    (Finset.mem_insert.mp (Finset.mem_of_mem_erase ha)).resolve_left hab
  have hnb : ∀ c∈C,∀ d,G.Adj c d→ d≠w→ d∈(insert b C).erase w:=fun c hc d hd hdw =>
    Finset.mem_erase.mpr ⟨hdw,by
      rcases hcl c hc d hd with h'|rfl
      exacts [Finset.mem_insert_of_mem h',Finset.mem_insert_self _ _]⟩
  suffices key : ∃ P ⊂ C,w∉P∧P.Nonempty∧∀ c∈P,∀ d,G.Adj c d→ d∈P∨d=w by
    obtain ⟨P,hPC,hwP,hPne,hPcl⟩:=key
    obtain ⟨B,b',hB,hsub,hb'⟩:=ih P hPC w hwP hPne hPcl
    refine ⟨B,b',hB,hsub.trans hPC.subset,?_⟩
    rcases Finset.mem_insert.mp hb' with rfl|h'
    exacts [hw,Finset.mem_insert_of_mem (hPC.subset h')]
  by_cases hbR : b∈R
  · have hwb : w≠b:=by
      rintro rfl
      exact Finset.notMem_erase w _ (hRs hbR)
    have hsub : (insert b C).erase w\R⊆C:=fun a ha=>hmem a (Finset.mem_sdiff.mp ha).1
      fun h'=>(Finset.mem_sdiff.mp ha).2 (h' ▸ hbR)
    refine ⟨_,(Finset.ssubset_iff_of_subset hsub).mpr ⟨w,hmem' hw hwb,fun h' =>
      Finset.notMem_erase w _ (Finset.mem_sdiff.mp h').1⟩,fun h' =>
      Finset.notMem_erase w _ (Finset.mem_sdiff.mp h').1,⟨v,Finset.mem_sdiff.mpr ⟨hvs,hvR⟩⟩,
      fun c hc d hd=>?_⟩
    by_cases hdw : d=w
    · exact Or.inr hdw
    · refine Or.inl (Finset.mem_sdiff.mpr ⟨hnb c (hsub hc) d hd hdw,fun hdR=>?_⟩)
      exact (Finset.mem_sdiff.mp hc).2 (hRcl d hdR c (Finset.mem_sdiff.mp hc).1 hd.symm)
  · have hsub : R⊆C:=fun a ha=>hmem a (hRs ha) fun h'=>hbR (h' ▸ ha)
    have hout : ∃ a∈C,a∉R:=by
      by_cases hwb : w=b
      · refine ⟨v,hmem v hvs ?_,hvR⟩
        subst hwb
        rintro rfl
        exact Finset.notMem_erase _ _ hvs
      · exact ⟨w,hmem' hw hwb,fun h'=>Finset.notMem_erase w _ (hRs h')⟩
    refine ⟨R,(Finset.ssubset_iff_of_subset hsub).mpr hout,
      fun h'=>Finset.notMem_erase w _ (hRs h'),hRne,fun c hc d hd=>?_⟩
    by_cases hdw : d=w
    · exact Or.inr hdw
    · exact Or.inl (hRcl c hc d (hnb c (hsub hc) d hd hdw) hd)
where
  hmem' {C : Finset V} {b w : V} (hw : w∈insert b C) (hwb : w≠b) : w∈C :=
    (Finset.mem_insert.mp hw).resolve_left hwb
theorem qf2 [Fintype V] [DecidableEq V] (hG : G.Connected)
    (hc : 2 < Fintype.card V) (h2 : ¬ Kc0 G 2) :
    ∃ B₁ b₁ B₂ b₂,Ieb0 G B₁ b₁∧Ieb0 G B₂ b₂ ∧
      Disjoint (B₁.erase b₁) (B₂.erase b₂)∧b₁∉B₂.erase b₂∧b₂∉B₁.erase b₁ ∧
      ∃ P : G.Walk b₁ b₂,P.IsPath∧∀ a∈P.support,a∉B₁.erase b₁∧a∉B₂.erase b₂:=by
  obtain ⟨w,hw⟩ : ∃ w,¬ Lk0 G (Finset.univ.erase w):=by
    by_contra hall
    simp only [not_exists,not_not] at hall
    exact h2 (kConn_two_iff.mpr ⟨hc,hall⟩)
  obtain ⟨R,hRs,hRne,⟨v,hvs,hvR⟩,hRcl⟩:=qg6 hw
  have hwR : w∉R:=fun h'=>Finset.notMem_erase w _ (hRs h')
  have hcl₁ : ∀ c∈R,∀ d,G.Adj c d→ d∈R∨d=w:=fun c hc d hd=>by
    by_cases hdw : d=w
    · exact Or.inr hdw
    · exact Or.inl (hRcl c hc d (by simp [hdw]) hd)
  have hcl₂ : ∀ c∈Finset.univ.erase w\R,∀ d,G.Adj c d →
      d∈Finset.univ.erase w\R∨d=w:=fun c hc d hd=>by
    by_cases hdw : d=w
    · exact Or.inr hdw
    · exact Or.inl (Finset.mem_sdiff.mpr ⟨by simp [hdw],fun hdR =>
        (Finset.mem_sdiff.mp hc).2 (hRcl d hdR c (Finset.mem_sdiff.mp hc).1 hd.symm)⟩)
  obtain ⟨B₁,b₁,hB₁,hsub₁,hb₁⟩:=qc8 R w hwR hRne hcl₁
  obtain ⟨B₂,b₂,hB₂,hsub₂,hb₂⟩:=qc8 _ w
    (fun h'=>Finset.notMem_erase w _ (Finset.mem_sdiff.mp h').1)
    ⟨v,Finset.mem_sdiff.mpr ⟨hvs,hvR⟩⟩ hcl₂
  have hdisj : Disjoint R (Finset.univ.erase w\R):=Finset.disjoint_sdiff
  have hout₁ : b₁∉B₂.erase b₂:=fun h'=>by
    have h'':=hsub₂ h'
    rcases Finset.mem_insert.mp hb₁ with rfl|hR
    · exact Finset.notMem_erase b₁ _ (Finset.mem_sdiff.mp h'').1
    · exact Finset.disjoint_left.mp hdisj hR h''
  have hout₂ : b₂∉B₁.erase b₁:=fun h'=>by
    have h'':=hsub₁ h'
    rcases Finset.mem_insert.mp hb₂ with rfl|hR
    · exact hwR h''
    · exact Finset.disjoint_right.mp hdisj hR h''
  obtain ⟨P,hP⟩:=(hG.preconnected b₁ b₂).exists_isPath
  refine ⟨B₁,b₁,B₂,b₂,hB₁,hB₂,Disjoint.mono hsub₁ hsub₂ hdisj,hout₁,hout₂,P,hP,
    fun a ha=>⟨qab4 (ql3 hB₁) hP (Finset.notMem_erase _ _) hout₂ a ha,
      qab4 (ql3 hB₂) hP.reverse (Finset.notMem_erase _ _) hout₁ a
        (by simpa using ha)⟩⟩
theorem qag0 [Fintype V] [DecidableEq V] (hG : G.Connected)
    (hc : 2 < Fintype.card V) (c : V) :
    ∃ B b,Ieb0 G B b∧c∉B.erase b∧(Kc0 G 2→ B=Finset.univ):=by
  by_cases h2 : Kc0 G 2
  · exact ⟨_,c,qac0 h2 c,Finset.notMem_erase c _,fun _=>rfl⟩
  · obtain ⟨B₁,b₁,B₂,b₂,hB₁,hB₂,hd,-⟩:=qf2 hG hc h2
    by_cases hc₁ : c∈B₁.erase b₁
    · exact ⟨B₂,b₂,hB₂,Finset.disjoint_left.mp hd hc₁,fun h=>absurd h h2⟩
    · exact ⟨B₁,b₁,hB₁,hc₁,fun h=>absurd h h2⟩
end EndBlocks
section RootedSides
variable {G : SimpleGraph V}
def qar6 (G : SimpleGraph V) (b : V) : Prop :=
  ∃ u v,u≠b∧v≠b∧∀ p : G.Walk u v,b∈p.support
theorem qh7 [Fintype V] [DecidableEq V] (hc : 2 < Fintype.card V)
    (h : ¬ Kc0 G 2) : ∃ b,qar6 G b:=by
  by_contra hno
  refine h (kConn_two_iff.mpr ⟨hc,fun w u hu v hv=>?_⟩)
  by_contra hr
  refine hno ⟨w,u,v,Finset.ne_of_mem_erase hu,Finset.ne_of_mem_erase hv,fun p=>?_⟩
  by_contra hp
  exact hr ⟨p,fun a ha=>Finset.mem_erase.mpr ⟨fun h'=>hp (h' ▸ ha),Finset.mem_univ a⟩⟩
theorem qq0 [Fintype V] [DecidableEq V] {x y b : V} (h : Rt0 G x y)
    (hbx : b≠x) (hby : b≠y) {C : Finset V} (hxC : x∈C) (hyC : y∉C) (hbC : b∉C)
    (hcl : ∀ c∈C,∀ w,G.Adj c w→ w∈C∨w=b) (hlink : Lk0 G C) (hC : C≠{x})
    (hx : x∈insert b C) (hb : b∈insert b C) :
    Rt0 (G.induce ((insert b C : Finset V) : Set V)) ⟨x,hx⟩ ⟨b,hb⟩:=by
  obtain ⟨-,hl⟩:=kConn_two_iff.mp h.2
  have hcard : 2 < (insert b C).card:=by
    rw [Finset.card_insert_of_notMem hbC]
    have : 1 < C.card:=by
      by_contra h'
      exact hC (Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hxC,fun a ha=>Finset.card_le_one.mp (by omega) a ha x hxC⟩)
    omega
  have hyB : y∉insert b C:=by simp [hby.symm,hyC]
  have key : ∀ a d,G.Adj a d→ a∈insert b C→ d∉insert b C→ a=b:=fun a d had ha hd=>by
    rcases Finset.mem_insert.mp ha with rfl|haC
    · rfl
    · rcases hcl a haC d had with h'|rfl
      · exact absurd (Finset.mem_insert_of_mem h') hd
      · exact absurd (Finset.mem_insert_self _ _) hd
  refine qb4 hbx.symm hcard (fun w hw=>?_) hx hb
  by_cases hwb : w=b
  · subst hwb
    rw [Finset.erase_insert hbC]
    exact hlink.mono_graph le_sup_left
  refine qa4 b fun v hv=>?_
  have hr:=hl w b (by simp [Ne.symm hwb]) v (by simp [Finset.ne_of_mem_erase hv])
  have hπ:=hr.proj (H:=G ⊔ edge x b) (t:=(insert b C).erase w)
    (fun a=>if a∈insert b C then a else b)
    (fun a _ d _ had=>?_) (fun a ha=>?_)
  · rwa [if_pos (Finset.mem_insert_self b C),if_pos (Finset.mem_of_mem_erase hv)] at hπ
  · simp only [sup_adj,edge_adj] at had
    rcases had with had|⟨⟨rfl,rfl⟩|⟨rfl,rfl⟩,-⟩
    · split_ifs with ha hd hd
      · exact Or.inr (Or.inl had)
      · exact Or.inl (key a d had ha hd)
      · exact Or.inl (key d a had.symm hd ha).symm
      · exact Or.inl rfl
    · rw [if_pos hx,if_neg hyB]
      exact Or.inr (Or.inr (by simp [edge_adj,hbx,hbx.symm]))
    · rw [if_pos hx,if_neg hyB]
      exact Or.inr (Or.inr (by simp [edge_adj,hbx,hbx.symm]))
  · split_ifs with ha'
    · exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase ha,ha'⟩
    · exact Finset.mem_erase.mpr ⟨Ne.symm hwb,Finset.mem_insert_self b C⟩
theorem qm4 [Fintype V] [DecidableEq V] {x y b : V} (h : Rt0 G x y)
    (hb : qar6 G b) :
    b≠x∧b≠y∧∃ Cx Cy : Finset V,x∈Cx∧y∈Cy∧b∉Cx∧b∉Cy ∧
      Disjoint Cx Cy∧(∀ a,a≠b→ a∈Cx∨a∈Cy) ∧
      (∀ c∈Cx,∀ w,G.Adj c w→ w∈Cx∨w=b) ∧
      (∀ c∈Cy,∀ w,G.Adj c w→ w∈Cy∨w=b)∧Lk0 G Cx∧Lk0 G Cy ∧
      (Cx={x}∨∀ (h₁ : x∈insert b Cx) (h₂ : b∈insert b Cx),
        Rt0 (G.induce ((insert b Cx : Finset V) : Set V)) ⟨x,h₁⟩ ⟨b,h₂⟩) ∧
      (Cy={y}∨∀ (h₁ : b∈insert b Cy) (h₂ : y∈insert b Cy),
        Rt0 (G.induce ((insert b Cy : Finset V) : Set V)) ⟨b,h₁⟩ ⟨y,h₂⟩):=by
  classical
  obtain ⟨u₀,v₀,hu₀,hv₀,hsep⟩:=hb
  obtain ⟨-,hl⟩:=kConn_two_iff.mp h.2
  set t:=Finset.univ.erase b with ht
  have hmt : ∀ a,a≠b→ a∈t:=fun a ha=>Finset.mem_erase.mpr ⟨ha,Finset.mem_univ a⟩
  have hsep' : ¬ Rc0 G t u₀ v₀:=fun ⟨p,hp⟩=>Finset.notMem_erase b _ (hp b (hsep p))
  have hbx : b≠x:=by
    rintro rfl
    exact hsep' (qe3 (Or.inl (Finset.notMem_erase _ _))
      (hl b u₀ (hmt _ hu₀) v₀ (hmt _ hv₀)))
  have hby : b≠y:=by
    rintro rfl
    exact hsep' (qe3 (Or.inr (Finset.notMem_erase _ _))
      (hl b u₀ (hmt _ hu₀) v₀ (hmt _ hv₀)))
  have hxy_or : ∀ a∈t,Rc0 G t a x∨Rc0 G t a y:=fun a ha=>by
    obtain ⟨p,hp⟩:=hl b a ha x (hmt _ hbx.symm)
    obtain ⟨r,hr,q,hqs,hqS,-⟩:=qe9 (fun z=>z=x∨z=y) p (Or.inl rfl)
    obtain ⟨q',hq'⟩:=qai3 (H:=G) id q fun a' ha' d' hd' had=>by
      simp only [sup_adj] at had
      rcases had with had|had
      · exact Or.inr had
      · rw [edge_adj] at had
        obtain ⟨hh,-⟩:=had
        have h1:=hqS a' ha' (by rcases hh with ⟨rfl,-⟩|⟨rfl,-⟩ <;> simp)
        have h2:=hqS d' hd' (by rcases hh with ⟨-,rfl⟩|⟨-,rfl⟩ <;> simp)
        exact Or.inl (h1.trans h2.symm)
    have hreach : Rc0 G t a r:=⟨q',fun z hz=>by
      obtain ⟨z',hz',rfl⟩:=hq' z hz
      exact hp z' (hqs z' hz')⟩
    rcases hr with rfl|rfl
    exacts [Or.inl hreach,Or.inr hreach]
  have hnxy : ¬ Rc0 G t x y:=fun hxy=>hsep' (by
    have hx' : ∀ a∈t,Rc0 G t a x:=fun a ha =>
      (hxy_or a ha).elim id fun h'=>h'.trans hxy.symm
    exact (hx' u₀ (hmt _ hu₀)).trans (hx' v₀ (hmt _ hv₀)).symm)
  have side : ∀ r,r≠b→ r∈t.filter (Rc0 G t r)∧b∉t.filter (Rc0 G t r) ∧
      (∀ c∈t.filter (Rc0 G t r),∀ w,G.Adj c w→ w∈t.filter (Rc0 G t r)∨w=b) ∧
      Lk0 G (t.filter (Rc0 G t r)):=by
    intro r hrb
    set C:=t.filter (Rc0 G t r) with hC
    have hrC : r∈C:=Finset.mem_filter.mpr ⟨hmt _ hrb,Rc0.refl (hmt _ hrb)⟩
    have hcl : ∀ c∈C,∀ w,G.Adj c w→ w∈C∨w=b:=fun c hc w hw=>by
      by_cases hwb : w=b
      · exact Or.inr hwb
      · have hc':=Finset.mem_filter.mp hc
        exact Or.inl (Finset.mem_filter.mpr
          ⟨hmt _ hwb,hc'.2.trans (Rc0.adj hc'.1 (hmt _ hwb) hw)⟩)
    refine ⟨hrC,fun h'=>Finset.notMem_erase b _ (Finset.mem_filter.mp h').1,hcl,
      qa4 r fun a ha=>?_⟩
    obtain ⟨p,hp⟩:=(Finset.mem_filter.mp ha).2
    exact ⟨p,qb9 (D:=(·=b)) hcl p hrC
      (fun z hz hzb=>Finset.notMem_erase b _ (hzb ▸ hp z hz))⟩
  obtain ⟨hxC,hbCx,hclx,hlx⟩:=side x hbx.symm
  obtain ⟨hyC,hbCy,hcly,hly⟩:=side y hby.symm
  have hdisj : Disjoint (t.filter (Rc0 G t x)) (t.filter (Rc0 G t y)) :=
    Finset.disjoint_left.mpr fun a hax hay =>
      hnxy ((Finset.mem_filter.mp hax).2.trans (Finset.mem_filter.mp hay).2.symm)
  refine ⟨hbx,hby,_,_,hxC,hyC,hbCx,hbCy,hdisj,fun a hab=>?_,hclx,hcly,hlx,hly,
    ?_,?_⟩
  · rcases hxy_or a (hmt _ hab) with h'|h'
    · exact Or.inl (Finset.mem_filter.mpr ⟨hmt _ hab,h'.symm⟩)
    · exact Or.inr (Finset.mem_filter.mpr ⟨hmt _ hab,h'.symm⟩)
  · by_cases hCx : t.filter (Rc0 G t x)={x}
    · exact Or.inl hCx
    · exact Or.inr fun h₁ h₂=>qq0 h hbx hby hxC
        (Finset.disjoint_right.mp hdisj hyC) hbCx hclx hlx hCx h₁ h₂
  · by_cases hCy : t.filter (Rc0 G t y)={y}
    · exact Or.inl hCy
    · exact Or.inr fun h₁ h₂=>qo4 (qq0 (qo4 h) hby hbx hyC
        (Finset.disjoint_left.mp hdisj hxC) hbCy hcly hly hCy h₂ h₁)
theorem qai2 [Fintype V] [DecidableEq V] {x y : V} (h : Rt0 G x y)
    (h2 : ¬ Kc0 G 2) {B : Finset V} {b : V} (hB : Ieb0 G B b) :
    x∈B.erase b∨y∈B.erase b:=by
  by_contra hno
  rw [not_or] at hno
  obtain ⟨hc,hl⟩:=kConn_two_iff.mp h.2
  by_cases hBu : B=Finset.univ
  · subst hBu
    rcases hB.2.2.2 with h'|h'
    · rw [Finset.card_univ] at h'
      omega
    · exact h2 (kConn_induce_univ_iff.mp h')
  obtain ⟨t,htB⟩ : ∃ t,t∉B:=by
    by_contra hall
    simp only [not_exists,not_not] at hall
    exact hBu (Finset.eq_univ_of_forall hall)
  obtain ⟨i,hiB,hib⟩:=Finset.exists_mem_ne (by have:=hB.2.1;omega : 1 < B.card) b
  obtain ⟨p,hp⟩:=hl b i (by simp [hib]) t (by simp;rintro rfl;exact htB hB.1)
  have hcl : ∀ c∈B.erase b,∀ d,(G ⊔ edge x y).Adj c d→ d∈B.erase b∨d=b :=
    fun c hc d hd=>by
      have hG : G.Adj c d:=by
        simp only [sup_adj,edge_adj] at hd
        rcases hd with hd|⟨⟨rfl,-⟩|⟨rfl,-⟩,-⟩
        exacts [hd,absurd hc hno.1,absurd hc hno.2]
      exact ql3 hB c hc d hG
  exact htB (Finset.mem_of_mem_erase (qb9 (D:=(·=b)) hcl p
    (Finset.mem_erase.mpr ⟨hib,hiB⟩) (fun z hz hzb=>Finset.notMem_erase b _ (hzb ▸ hp z hz))
    t p.end_mem_support))
theorem qak0 [DecidableEq V] {Q : Finset V} {x y : V} (hxy : x≠y) (hxQ : x∉Q)
    (hyQ : y∉Q) (hQ : Lk0 G Q) (hx : ∃ q∈Q,G.Adj x q) (hy : ∃ q∈Q,G.Adj y q)
    (hcut : ∀ w∈Q,∀ C⊆Q.erase w,C.Nonempty →
      (∀ c∈C,∀ d∈Q.erase w,G.Adj c d→ d∈C)→ ∃ c∈C,G.Adj c x∨G.Adj c y)
    (h₁ : x∈insert x (insert y Q)) (h₂ : y∈insert x (insert y Q)) :
    Rt0 (de0 (G.induce ((insert x (insert y Q) : Finset V) : Set V)) ⟨x,h₁⟩ ⟨y,h₂⟩)
      ⟨x,h₁⟩ ⟨y,h₂⟩:=by
  rw [rooted_delEdge_iff]
  obtain ⟨qx,hqx,hxq⟩:=hx
  obtain ⟨qy,hqy,hyq⟩:=hy
  have hle : G≤ G ⊔ edge x y:=le_sup_left
  have hxy' : (G ⊔ edge x y).Adj x y:=Or.inr (by simp [edge_adj,hxy])
  have hcard : 2 < (insert x (insert y Q)).card:=by
    rw [Finset.card_insert_of_notMem (by simp [hxy,hxQ]),Finset.card_insert_of_notMem hyQ]
    have:=Finset.card_pos.mpr ⟨qx,hqx⟩
    omega
  have hQU : ∀ w,w∉Q→ Q⊆(insert x (insert y Q)).erase w:=fun w hw q hq =>
    Finset.mem_erase.mpr ⟨fun h'=>hw (h' ▸ hq),by simp [hq]⟩
  refine qb4 hxy hcard (fun w hw=>?_) h₁ h₂
  have hmem : ∀ v∈(insert x (insert y Q)).erase w,v=x∨v=y∨v∈Q:=fun v hv=>by
    simpa using Finset.mem_of_mem_erase hv
  rcases Finset.mem_insert.mp hw with rfl|hw'
  · have hyU : y∈(insert w (insert y Q)).erase w:=by simp [hxy.symm]
    refine qa4 y fun v hv=>?_
    rcases hmem v hv with rfl|rfl|hvQ
    · exact absurd rfl (Finset.ne_of_mem_erase hv)
    · exact Rc0.refl hyU
    · exact (Rc0.adj hyU (hQU _ hxQ hqy) (hle hyq)).trans
        (((hQ qy hqy v hvQ).mono (hQU _ hxQ)).mono_graph hle)
  rcases Finset.mem_insert.mp hw' with rfl|hwQ
  · have hxU : x∈(insert x (insert w Q)).erase w:=by simp [hxy]
    refine qa4 x fun v hv=>?_
    rcases hmem v hv with rfl|rfl|hvQ
    · exact Rc0.refl hxU
    · exact absurd rfl (Finset.ne_of_mem_erase hv)
    · exact (Rc0.adj hxU (hQU _ hyQ hqx) (hle hxq)).trans
        (((hQ qx hqx v hvQ).mono (hQU _ hyQ)).mono_graph hle)
  have hxU : x∈(insert x (insert y Q)).erase w :=
    Finset.mem_erase.mpr ⟨fun h'=>hxQ (h' ▸ hwQ),by simp⟩
  have hyU : y∈(insert x (insert y Q)).erase w :=
    Finset.mem_erase.mpr ⟨fun h'=>hyQ (h' ▸ hwQ),by simp⟩
  have hQw : Q.erase w⊆(insert x (insert y Q)).erase w:=fun q hq =>
    Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hq,by simp [Finset.mem_of_mem_erase hq]⟩
  refine qa4 x fun v hv=>?_
  rcases hmem v hv with rfl|rfl|hvQ
  · exact Rc0.refl hxU
  · exact Rc0.adj hxU hyU hxy'
  have hvQw : v∈Q.erase w:=Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hv,hvQ⟩
  obtain ⟨R,hRs,hvR,hRcl,hRr⟩:=qg2 (G:=G) (Q.erase w) hvQw
  obtain ⟨c,hcR,hc⟩:=hcut w hwQ R hRs ⟨v,hvR⟩ hRcl
  have hcv : Rc0 (G ⊔ edge x y) _ c v:=(((hRr c hcR).mono hQw).mono_graph hle).symm
  rcases hc with hc|hc
  · exact (Rc0.adj hxU (hQw (hRs hcR)) (hle hc.symm)).trans hcv
  · exact ((Rc0.adj hxU hyU hxy').trans (Rc0.adj hyU (hQw (hRs hcR)) (hle hc.symm))).trans hcv
end RootedSides
section Boundary
variable {Q : SimpleGraph W} {A₁ A₂ : Finset W}
theorem qa8 (i : Fin 2) : i=0∨i=1:=by
  revert i
  decide
def qm8 (A₁ A₂ : Finset W) (i : Fin 2) : Finset W:=if i=0 then A₁ else A₂
@[simp] theorem rootSet_zero : qm8 A₁ A₂ 0=A₁:=by simp [qm8]
@[simp] theorem rootSet_one : qm8 A₁ A₂ 1=A₂:=by simp [qm8]
def bg0 (Q : SimpleGraph W) (A₁ A₂ : Finset W) : SimpleGraph (Fin 2 ⊕ W) where
  Adj a b:=match a,b with
    | Sum.inr u,Sum.inr v=>Q.Adj u v
    | Sum.inl i,Sum.inr u=>u∈qm8 A₁ A₂ i
    | Sum.inr u,Sum.inl i=>u∈qm8 A₁ A₂ i
    | Sum.inl _,Sum.inl _=>False
  symm:=⟨by
    rintro (i|u) (j|v) h
    exacts [h,h,h,h.symm]⟩
  loopless:=⟨by
    rintro (i|u) h
    exacts [h,Q.irrefl h]⟩
@[simp] theorem bnd_adj_inr {u v : W} :
    (bg0 Q A₁ A₂).Adj (Sum.inr u) (Sum.inr v)↔Q.Adj u v:=Iff.rfl
@[simp] theorem bnd_adj_inl_inr {i : Fin 2} {u : W} :
    (bg0 Q A₁ A₂).Adj (Sum.inl i) (Sum.inr u)↔u∈qm8 A₁ A₂ i:=Iff.rfl
@[simp] theorem bnd_adj_inr_inl {i : Fin 2} {u : W} :
    (bg0 Q A₁ A₂).Adj (Sum.inr u) (Sum.inl i)↔u∈qm8 A₁ A₂ i:=Iff.rfl
@[simp] theorem bnd_not_adj_inl {i j : Fin 2} :
    ¬ (bg0 Q A₁ A₂).Adj (Sum.inl i) (Sum.inl j):=id
def qas3 (Q : SimpleGraph W) (A₁ A₂ : Finset W) : Q ↪g bg0 Q A₁ A₂ where
  toFun:=Sum.inr
  inj':=Sum.inr_injective
  map_rel_iff':=Iff.rfl
theorem qv7 {H : SimpleGraph (Fin 2 ⊕ W)} (hle : bg0 Q A₁ A₂≤ H)
    {s : Finset W} {t : Finset (Fin 2 ⊕ W)} {u v : W} (hst : ∀ a∈s,Sum.inr a∈t)
    (h : Rc0 Q s u v) : Rc0 H t (Sum.inr u) (Sum.inr v) :=
  h.proj Sum.inr (fun _ _ _ _ hab=>Or.inr (hle hab)) hst
theorem qw1 [Fintype W] [DecidableEq W] {H : SimpleGraph (Fin 2 ⊕ W)}
    (hle : bg0 Q A₁ A₂≤ H) (hQ : Q.Connected) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty)
    (hw : ∀ w : W,Rc0 H (Finset.univ.erase (Sum.inr w)) (Sum.inl 0) (Sum.inl 1) ∧
      ∀ u,u≠w→ Rc0 H (Finset.univ.erase (Sum.inr w)) (Sum.inl 0) (Sum.inr u)) :
    Kc0 H 2:=by
  obtain ⟨a₁,ha₁⟩:=hA₁
  obtain ⟨a₂,ha₂⟩:=hA₂
  have hQl : ∀ u v : W,Rc0 Q Finset.univ u v:=fun u v =>
    (hQ.preconnected u v).elim fun p=>⟨p,by simp⟩
  refine kConn_two_iff.mpr ⟨?_,fun w=>?_⟩
  · rw [Fintype.card_sum,Fintype.card_fin]
    have:=Fintype.card_pos_iff.mpr ⟨a₁⟩
    omega
  have root : ∀ i j : Fin 2,i≠j→ ∀ a∈qm8 A₁ A₂ j,
      Lk0 H (Finset.univ.erase (Sum.inl i)):=fun i j hij a ha=>by
    have hj : (Sum.inl j : Fin 2 ⊕ W)∈Finset.univ.erase (Sum.inl i):=by simp [Ne.symm hij]
    refine qa4 (Sum.inl j) fun v hv=>?_
    rcases v with k|u
    · have hk : k=j:=by
        rcases qa8 i with rfl|rfl <;> rcases qa8 j with rfl|rfl <;>
          rcases qa8 k with rfl|rfl <;> simp_all
      subst hk
      exact Rc0.refl hj
    · exact (Rc0.adj hj (by simp) (hle (show (bg0 Q A₁ A₂).Adj (Sum.inl j)
        (Sum.inr a) from ha))).trans
        (qv7 hle (fun _ _=>by simp) (hQl a u))
  rcases w with i|w
  · rcases qa8 i with rfl|rfl
    · exact root 0 1 (by simp) a₂ (by simpa using ha₂)
    · exact root 1 0 (by simp) a₁ (by simpa using ha₁)
  refine qa4 (Sum.inl 0) fun v hv=>?_
  rcases v with k|u
  · rcases qa8 k with rfl|rfl
    · exact Rc0.refl (by simp)
    · exact (hw w).1
  · exact (hw w).2 u fun h'=>by simp [h'] at hv
theorem qab3 [Fintype W] [DecidableEq W] (hQ : Q.Connected) (hA₁ : A₁.Nonempty)
    (hA₂ : A₂.Nonempty)
    (hcut : ∀ w : W,∀ C⊆Finset.univ.erase w,C.Nonempty →
      (∀ c∈C,∀ d∈Finset.univ.erase w,Q.Adj c d→ d∈C)→ ∃ c∈C,c∈A₁∨c∈A₂) :
    Rt0 (bg0 Q A₁ A₂) (Sum.inl 0) (Sum.inl 1):=by
  have hle : bg0 Q A₁ A₂≤ bg0 Q A₁ A₂ ⊔ edge (Sum.inl 0) (Sum.inl 1) :=
    le_sup_left
  have hroot : (bg0 Q A₁ A₂ ⊔ edge (Sum.inl 0) (Sum.inl 1)).Adj (Sum.inl 0)
      (Sum.inl 1):=Or.inr (by simp [edge_adj])
  refine ⟨by simp,qw1 hle hQ hA₁ hA₂ fun w=>?_⟩
  have h01 : Rc0 (bg0 Q A₁ A₂ ⊔ edge (Sum.inl 0) (Sum.inl 1))
      (Finset.univ.erase (Sum.inr w)) (Sum.inl 0) (Sum.inl 1) :=
    Rc0.adj (by simp) (by simp) hroot
  refine ⟨h01,fun u hu=>?_⟩
  obtain ⟨R,hRs,huR,hRcl,hRr⟩:=qg2 (G:=Q) (u:=u) (Finset.univ.erase w)
    (by simpa using hu)
  obtain ⟨c,hcR,hc⟩:=hcut w R hRs ⟨u,huR⟩ hRcl
  have hcw : c≠w:=Finset.ne_of_mem_erase (hRs hcR)
  have hcu:=(qv7 hle (t:=Finset.univ.erase (Sum.inr w)) (fun a ha=>by
    simpa using Finset.ne_of_mem_erase ha) (hRr c hcR)).symm
  rcases hc with hc|hc
  · exact (Rc0.adj (by simp) (by simp [hcw]) (hle (show (bg0 Q A₁ A₂).Adj
      (Sum.inl 0) (Sum.inr c) by simpa using hc))).trans hcu
  · exact (h01.trans (Rc0.adj (by simp) (by simp [hcw]) (hle (show (bg0 Q A₁ A₂).Adj
      (Sum.inl 1) (Sum.inr c) by simpa using hc)))).trans hcu
theorem qt7 [Fintype W] [DecidableEq W] (hQ : Kc0 Q 2) (hA₁ : 2≤ A₁.card)
    (hA₂ : 2≤ A₂.card) : Kc0 (bg0 Q A₁ A₂) 2:=by
  obtain ⟨-,hl⟩:=kConn_two_iff.mp hQ
  refine qw1 le_rfl (qc7 hQ) (Finset.card_pos.mp (by omega))
    (Finset.card_pos.mp (by omega)) fun w=>?_
  obtain ⟨a,ha,haw⟩:=Finset.exists_mem_ne hA₁ w
  obtain ⟨b,hb,hbw⟩:=Finset.exists_mem_ne hA₂ w
  have hst : ∀ x∈Finset.univ.erase w,(Sum.inr x : Fin 2 ⊕ W)∈Finset.univ.erase (Sum.inr w) :=
    fun x hx=>by simpa using Finset.ne_of_mem_erase hx
  have h0a : Rc0 (bg0 Q A₁ A₂) (Finset.univ.erase (Sum.inr w)) (Sum.inl 0)
      (Sum.inr a):=Rc0.adj (by simp) (by simp [haw]) (by simpa using ha)
  refine ⟨(h0a.trans (qv7 le_rfl hst (hl w a (by simp [haw]) b (by simp [hbw])))).trans
    (Rc0.adj (by simp [hbw]) (by simp) (by simpa using hb)),fun u hu =>
    h0a.trans (qv7 le_rfl hst (hl w a (by simp [haw]) u (by simp [hu])))⟩
theorem qaq5 :
    ∀ {a b : Fin 2 ⊕ W} (p : (bg0 Q A₁ A₂).Walk a b) (u : W),a=Sum.inr u →
      b=Sum.inl 1→ p.IsPath→ Sum.inl 0∉p.support →
      ∃ u₂∈A₂,∃ m : Q.Walk u u₂,p.length=m.length+1 ∧
        p.support=m.support.map Sum.inr ++ [Sum.inl 1]:=by
  intro a b p
  induction p with
  | nil =>
    intro u hu hb
    exact absurd (hu.symm.trans hb) (by simp)
  | @cons a c b h p ih =>
    intro u hu hb hp h0
    subst hu
    rw [Walk.cons_isPath_iff] at hp
    cases c with
    | inl i =>
      rcases qa8 i with rfl|rfl
      · exact absurd (by simp) h0
      · subst hb
        obtain rfl:=(Walk.isPath_iff_nil.mp hp.1).eq_nil
        exact ⟨u,by simpa using h,Walk.nil,by simp,by simp⟩
    | inr v =>
      obtain ⟨u₂,hu₂,m,hl,hs⟩:=ih v rfl hb hp.1 fun h'=>h0 (by simp [h'])
      exact ⟨u₂,hu₂,Walk.cons (show Q.Adj u v from h) m,by simp [hl],by simp [hs]⟩
theorem qe2 {p : (bg0 Q A₁ A₂).Walk (Sum.inl 0) (Sum.inl 1)}
    (hp : p.IsPath) :
    ∃ u₁∈A₁,∃ u₂∈A₂,∃ m : Q.Walk u₁ u₂,m.IsPath∧p.length=m.length+2 ∧
      p.support=Sum.inl 0 :: (m.support.map Sum.inr ++ [Sum.inl 1]):=by
  have key : ∀ {a b} (p : (bg0 Q A₁ A₂).Walk a b),a=Sum.inl 0→ b=Sum.inl 1 →
      p.IsPath→ ∃ u₁∈A₁,∃ u₂∈A₂,∃ m : Q.Walk u₁ u₂,p.length=m.length+2 ∧
        p.support=Sum.inl 0 :: (m.support.map Sum.inr ++ [Sum.inl 1]):=by
    intro a b p ha hb hp
    cases p with
    | nil=>exact absurd (ha.symm.trans hb) (by simp)
    | @cons _ c _ h p =>
      subst ha
      rw [Walk.cons_isPath_iff] at hp
      cases c with
      | inl i=>exact absurd h bnd_not_adj_inl
      | inr u =>
        obtain ⟨u₂,hu₂,m,hl,hs⟩:=qaq5 p u rfl hb hp.1 hp.2
        exact ⟨u,by simpa using h,u₂,hu₂,m,by simp [hl],by simp [hs]⟩
  obtain ⟨u₁,hu₁,u₂,hu₂,m,hl,hs⟩:=key p rfl rfl hp
  refine ⟨u₁,hu₁,u₂,hu₂,m,?_,hl,hs⟩
  have hnd:=hp.support_nodup
  rw [hs,List.nodup_cons] at hnd
  exact Walk.IsPath.mk' (List.Nodup.of_map Sum.inr (hnd.2.sublist (List.sublist_append_left _ _)))
theorem qam0 {G : SimpleGraph V} (ι : Q ↪g G) {r₀ r₁ : V} (h01 : r₀≠r₁)
    (hr₀ : ∀ u,ι u≠r₀) (hr₁ : ∀ u,ι u≠r₁) (hA₁ : ∀ u∈A₁,G.Adj r₀ (ι u))
    (hA₂ : ∀ u∈A₂,G.Adj (ι u) r₁)
    {p : (bg0 Q A₁ A₂).Walk (Sum.inl 0) (Sum.inl 1)} (hp : p.IsPath) :
    ∃ q : G.Walk r₀ r₁,q.IsPath∧q.length=p.length ∧
      ∀ a∈q.support,a=r₀∨a=r₁∨a∈Set.range ι:=by
  obtain ⟨u₁,hu₁,u₂,hu₂,m,hm,hl,-⟩:=qe2 hp
  have hm' : (m.map ι.toHom).IsPath:=qb8 _ ι.injective hm
  have hmem : ∀ a∈(m.map ι.toHom).support,a∈Set.range ι:=fun a ha=>by
    rw [Walk.support_map,List.mem_map] at ha
    obtain ⟨b,-,rfl⟩:=ha
    exact ⟨b,rfl⟩
  have hn₁ : r₁∉(m.map ι.toHom).support:=fun h'=>by
    obtain ⟨b,hb⟩:=hmem _ h'
    exact hr₁ b hb
  refine ⟨Walk.cons (hA₁ u₁ hu₁) ((m.map ι.toHom).concat (hA₂ u₂ hu₂)),?_,by simp [hl],?_⟩
  · refine (Walk.cons_isPath_iff _ _).mpr ⟨hm'.concat hn₁ _,fun h'=>?_⟩
    rw [Walk.support_concat,List.mem_append,List.mem_singleton] at h'
    rcases h' with h'|h'
    · obtain ⟨b,hb⟩:=hmem _ h'
      exact hr₀ b hb
    · exact h01 h'
  · intro a ha
    rw [Walk.support_cons,List.mem_cons,Walk.support_concat,List.mem_append,
      List.mem_singleton] at ha
    rcases ha with rfl|ha|rfl
    exacts [Or.inl rfl,Or.inr (Or.inr (hmem a ha)),Or.inr (Or.inl rfl)]
end Boundary
section Contract
variable {G : SimpleGraph V}
theorem qf4 {Z : Finset V} {v : V} {p : (av0 G Z).Walk none (some v)}
    (hp : p.IsPath) :
    ∃ a∈Z,∃ m : G.Walk a v,m.IsPath∧p.length=m.length+1 ∧
      p.support=none :: m.support.map some:=by
  cases p with
  | @cons _ c _ h q =>
    rw [Walk.cons_isPath_iff] at hp
    cases c with
    | none=>exact absurd h adjoin_not_adj_none
    | some a =>
      obtain ⟨m,hl,hs⟩:=qv2 (qab2 G Z) q a v rfl rfl fun c hc=>by
        cases c with
        | none=>exact absurd hc hp.2
        | some c=>exact ⟨c,rfl⟩
      have hs' : m.support.map some=q.support:=by simpa using hs
      refine ⟨a,h,m,?_,by simp [hl],by simp [hs']⟩
      have hnd:=hp.1.support_nodup
      rw [← hs'] at hnd
      exact Walk.IsPath.mk' (hnd.of_map _)
def cs0 [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (S : Finset V) : SimpleGraph (Option ((S : Set V)ᶜ : Set V)) :=
  av0 (G.induce ((S : Set V)ᶜ)) (Finset.univ.filter fun v=>∃ s∈S,G.Adj v.1 s)
theorem qy7 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {S : Finset V}
    {k : ℕ} (hk : Kc0 G k) (hS : S.Nonempty) (hQ : Kc0 (G.induce ((S : Set V)ᶜ)) (k - 1)) :
    Kc0 (cs0 G S) k:=by
  classical
  obtain ⟨-,hl⟩:=kConn_iff_linked.mp hk
  obtain ⟨hcQ,hlQ⟩:=kConn_iff_linked.mp hQ
  refine kConn_iff_linked.mpr ⟨by rw [Fintype.card_option];omega,fun T hT u hu v hv=>?_⟩
  by_cases hn : none∈T
  · obtain ⟨u,rfl⟩:=Option.ne_none_iff_exists'.mp fun h : u=none =>
      Finset.mem_compl.mp hu (h ▸ hn)
    obtain ⟨v,rfl⟩:=Option.ne_none_iff_exists'.mp fun h : v=none =>
      Finset.mem_compl.mp hv (h ▸ hn)
    have hsub : insert none ((Finset.univ.filter fun a=>some a∈T).map
        Function.Embedding.some)⊆T:=fun o ho=>by
      simp only [Finset.mem_insert,Finset.mem_map,Finset.mem_filter,Finset.mem_univ,
        true_and,Function.Embedding.some_apply] at ho
      rcases ho with rfl|⟨a,ha,rfl⟩
      exacts [hn,ha]
    have hc:=Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simp),Finset.card_map] at hc
    exact (hlQ (Finset.univ.filter fun a=>some a∈T) (by omega) u (by simpa using hu) v
      (by simpa using hv)).map
      (qab2 _ _).toHom (fun a ha=>by simpa using ha)
  obtain ⟨s₀,hs₀⟩:=hS
  let π : V→ Option ((S : Set V)ᶜ : Set V):=fun a =>
    if h : a∈S then none else some ⟨a,h⟩
  let ρ : Option ((S : Set V)ᶜ : Set V)→ V:=fun o=>o.elim s₀ Subtype.val
  have hπρ : ∀ o,π (ρ o)=o:=by
    rintro (_|x)
    · simp [π,ρ,hs₀]
    · have hx : x.1∉S:=x.2
      simp [π,ρ,hx]
  have hT₀ : (Finset.univ.filter fun a=>π a∈T).card < k:=by
    refine lt_of_le_of_lt (Finset.card_le_card_of_injOn π (fun a ha=>by simpa using ha)
      fun a ha b hb hab=>?_) hT
    have hna : a∉S:=fun h'=>hn (by simpa [π,h'] using (Finset.mem_filter.mp ha).2)
    have hnb : b∉S:=fun h'=>hn (by simpa [π,h'] using (Finset.mem_filter.mp hb).2)
    simpa [π,hna,hnb] using hab
  have hr:=hl _ hT₀ (ρ u) (by simpa [hπρ] using hu) (ρ v) (by simpa [hπρ] using hv)
  have:=hr.proj (H:=cs0 G S) (t:=Tᶜ) π (fun a _ d _ had=>?_)
    (fun a ha=>by simpa using ha)
  · rwa [hπρ,hπρ] at this
  by_cases ha : a∈S <;> by_cases hd : d∈S
  · exact Or.inl (by simp [π,ha,hd])
  · exact Or.inr (by simpa [π,ha,hd,cs0] using ⟨a,ha,had.symm⟩)
  · exact Or.inr (by simpa [π,ha,hd,cs0] using ⟨d,hd,had⟩)
  · exact Or.inr (by simpa [π,ha,hd,cs0] using had)
theorem qv9 [Fintype V] [DecidableEq V] [DecidableRel G.Adj] {S : Finset V}
    {v : ((S : Set V)ᶜ : Set V)} {p : (cs0 G S).Walk none (some v)} (hp : p.IsPath) :
    ∃ s∈S,∃ q : G.Walk s v.1,q.IsPath∧q.length=p.length ∧
      ∀ a∈q.support.tail,a∉S:=by
  obtain ⟨a,ha,m,hm,hl,-⟩:=qf4 hp
  obtain ⟨s,hs,hadj⟩:=(Finset.mem_filter.mp ha).2
  obtain ⟨q,hq,hql,-,hqin⟩:=qd3 _ hm
  refine ⟨s,hs,Walk.cons hadj.symm q,(Walk.cons_isPath_iff _ _).mpr ⟨hq,fun h' =>
    hqin s h' hs⟩,by rw [Walk.length_cons,hql];exact hl.symm,fun b hb=>?_⟩
  rw [Walk.support_cons,List.tail_cons] at hb
  exact hqin b hb
end Contract
section Links
variable {G : SimpleGraph V}
def qai0 (G : SimpleGraph V) (u v : V) : Prop :=
  ∃ A B : G.Walk u v,A.IsPath∧B.IsPath ∧
    (∀ z∈A.support,z∈B.support→ z=u∨z=v)∧3≤ A.length+B.length
theorem qd2 {u v : V} (p : G.Walk u v) (h : u≠v) : 0 < p.length :=
  Nat.pos_of_ne_zero fun h0=>h (Walk.eq_of_length_eq_zero h0)
theorem qo5 {u v : V} : ∀ p : G.Walk u v,p.length=1→ s(u,v)∈p.edges
  | .nil,h=>by simp at h
  | .cons _ .nil,_=>by simp
  | .cons _ (.cons _ _),h=>by simp at h
theorem qai4 [Fintype V] [DecidableEq V] (h : Kc0 G 2) {u v : V} (huv : G.Adj u v) :
    qai0 G u v:=by
  obtain ⟨hc,hl⟩:=kConn_two_iff.mp h
  obtain ⟨t,htu,htv⟩:=qf8 hc u v
  obtain ⟨p₁,hp₁⟩:=hl v u (by simp [huv.ne]) t (by simp [htv])
  obtain ⟨p₂,hp₂⟩:=hl u t (by simp [htu]) v (by simp [huv.ne.symm])
  have hnot : s(u,v)∉(p₁.append p₂).edges:=by
    intro he
    rw [Walk.edges_append,List.mem_append] at he
    rcases he with he|he
    · exact Finset.notMem_erase v _ (hp₁ v (p₁.snd_mem_support_of_mem_edges he))
    · exact Finset.notMem_erase u _ (hp₂ u (p₂.fst_mem_support_of_mem_edges he))
  have hB : 2≤ (p₁.append p₂).bypass.length:=by
    have h0:=qd2 (p₁.append p₂).bypass huv.ne
    by_contra hlt
    exact hnot (Walk.edges_bypass_subset_edges _ (qo5 _ (by omega)))
  refine ⟨Walk.cons huv Walk.nil,(p₁.append p₂).bypass,(Walk.cons_isPath_iff _ _).mpr ⟨Walk.IsPath.nil,
    by simpa using huv.ne⟩,Walk.bypass_isPath _,fun z hz _=>by simpa using hz,?_⟩
  rw [Walk.length_cons,Walk.length_nil]
  omega
theorem qv4 [DecidableEq V] {u v w x : V} {R₁ R₂ : G.Walk u w} (hR₁ : R₁.IsPath)
    (hR₂ : R₂.IsPath) (hR : ∀ z∈R₁.support,z∈R₂.support→ z=u∨z=w) (huw : u≠w)
    (huv : u≠v) (hvw : G.Adj v w) (hx : x∈R₁.support) (hxw : x≠w) {Q₁ : G.Walk v x}
    (hQ₁ : Q₁.IsPath) (hQS : ∀ z∈Q₁.support,z∈R₁.support∨z∈R₂.support→ z=x) :
    qai0 G u v:=by
  have hvR₂ : v∉R₂.support:=fun hv=>by
    have hvx:=hQS v Q₁.start_mem_support (Or.inr hv)
    rcases hR v (hvx ▸ hx) hv with h'|h'
    exacts [huv h'.symm,hvw.ne h']
  have hT:=hR₁.takeUntil hx
  have hwT : w∉(R₁.takeUntil x hx).support :=
    Walk.endpoint_notMem_support_takeUntil hR₁ hx hxw.symm
  have hTR : ∀ z∈(R₁.takeUntil x hx).support,z∈R₁.support:=fun z hz =>
    R₁.support_takeUntil_subset_support hx hz
  obtain ⟨hB,-,-⟩:=qa3 hT hQ₁.reverse fun z hz₁ hz₂ =>
    hQS z (by simpa using hz₂) (Or.inl (hTR z hz₁))
  refine ⟨R₂.concat hvw.symm,_,hR₂.concat hvR₂ hvw.symm,hB,fun z hz₁ hz₂=>?_,?_⟩
  · rw [Walk.support_concat,List.mem_append,List.mem_singleton] at hz₁
    rcases hz₁ with hz₁|rfl
    · rw [Walk.mem_support_append_iff] at hz₂
      rcases hz₂ with hz₂|hz₂
      · rcases hR z (hTR z hz₂) hz₁ with h'|rfl
        · exact Or.inl h'
        · exact absurd hz₂ hwT
      · have hzx:=hQS z (by simpa using hz₂) (Or.inr hz₁)
        rcases hR z (hzx ▸ hx) hz₁ with h'|h'
        exacts [Or.inl h',absurd (hzx ▸ h') hxw]
    · exact Or.inr rfl
  · have h1:=qd2 R₂ huw
    have h2:=qd2 ((R₁.takeUntil x hx).append Q₁.reverse) huv
    rw [Walk.length_concat]
    omega
theorem qy2 [Fintype V] [DecidableEq V] (h : Kc0 G 2) {u v : V} (huv : u≠v) :
    qai0 G u v:=by
  obtain ⟨-,hl⟩:=kConn_two_iff.mp h
  obtain ⟨p⟩:=(qc7 h).preconnected v u
  induction p with
  | nil=>exact absurd rfl huv
  | @cons v w u hvw p ih =>
    by_cases hwu : w=u
    · subst hwu
      exact qai4 h hvw.symm
    obtain ⟨R₁,R₂,hR₁,hR₂,hR,-⟩:=ih (Ne.symm hwu)
    obtain ⟨Q,hQ⟩:=hl w v (by simp [hvw.ne]) u (by simp [Ne.symm hwu])
    obtain ⟨x,hxS,Q₁,hQ₁s,hQ₁S,hQ₁p⟩:=qe9
      (fun z=>z∈R₁.support∨z∈R₂.support) Q.bypass (Or.inl R₁.start_mem_support)
    have hQ₁:=hQ₁p Q.bypass_isPath
    have hxw : x≠w:=fun hxw=>Finset.notMem_erase w _
      (hxw ▸ hQ x (Q.support_bypass_subset_support (hQ₁s x Q₁.end_mem_support)))
    rcases hxS with hx|hx
    · exact qv4 hR₁ hR₂ hR (Ne.symm hwu) huv hvw hx hxw hQ₁ hQ₁S
    · exact qv4 hR₂ hR₁ (fun z h₂ h₁=>hR z h₁ h₂) (Ne.symm hwu) huv hvw hx hxw hQ₁
        fun z hz hS=>hQ₁S z hz hS.symm
theorem qv3 [Fintype V] [DecidableEq V] (h : Kc0 G 2) {A B : Finset V}
    (hA : 2≤ A.card) (hB : 2≤ B.card) :
    ∃ a₁∈A,∃ a₂∈A,∃ b₁∈B,∃ b₂∈B,a₁≠a₂∧b₁≠b₂ ∧
      ∃ (P₁ : G.Walk a₁ b₁) (P₂ : G.Walk a₂ b₂),P₁.IsPath∧P₂.IsPath ∧
        ∀ z∈P₁.support,z∉P₂.support:=by
  obtain ⟨P,R,hP,hR,hPR,-⟩:=qy2 (qt7 h hA hB)
    (by simp : (Sum.inl 0 : Fin 2 ⊕ V)≠Sum.inl 1)
  obtain ⟨a₁,ha₁,b₁,hb₁,m₁,hm₁,-,hs₁⟩:=qe2 hP
  obtain ⟨a₂,ha₂,b₂,hb₂,m₂,hm₂,-,hs₂⟩:=qe2 hR
  have hdisj : ∀ z∈m₁.support,z∉m₂.support:=fun z hz₁ hz₂=>by
    have:=hPR (Sum.inr z) (by rw [hs₁];simp [hz₁]) (by rw [hs₂];simp [hz₂])
    simp at this
  exact ⟨a₁,ha₁,a₂,ha₂,b₁,hb₁,b₂,hb₂,
    fun h'=>hdisj a₁ m₁.start_mem_support (h' ▸ m₂.start_mem_support),
    fun h'=>hdisj b₁ m₁.end_mem_support (h' ▸ m₂.end_mem_support),m₁,m₂,hm₁,hm₂,hdisj⟩
theorem qy1 [Fintype V] [DecidableEq V] (h : Kc0 G 2) {a₁ a₂ b₁ b₂ : V}
    (ha : a₁≠a₂) (hb : b₁≠b₂) :
    (∃ (P₁ : G.Walk a₁ b₁) (P₂ : G.Walk a₂ b₂),P₁.IsPath∧P₂.IsPath ∧
      ∀ z∈P₁.support,z∉P₂.support) ∨
    (∃ (P₁ : G.Walk a₁ b₂) (P₂ : G.Walk a₂ b₁),P₁.IsPath∧P₂.IsPath ∧
      ∀ z∈P₁.support,z∉P₂.support):=by
  obtain ⟨c₁,hc₁,c₂,hc₂,d₁,hd₁,d₂,hd₂,hc,hd,P₁,P₂,hP₁,hP₂,hP⟩ :=
    qv3 h (Finset.card_pair ha).ge (Finset.card_pair hb).ge
  have hP' : ∀ z∈P₂.support,z∉P₁.support:=fun z h₂ h₁=>hP z h₁ h₂
  simp only [Finset.mem_insert,Finset.mem_singleton] at hc₁ hc₂ hd₁ hd₂
  rcases hc₁ with rfl|rfl <;> rcases hc₂ with rfl|rfl <;> rcases hd₁ with rfl|rfl <;>
    rcases hd₂ with rfl|rfl
  all_goals first
    | exact absurd rfl hc
    | exact absurd rfl hd
    | exact Or.inl ⟨P₁,P₂,hP₁,hP₂,hP⟩
    | exact Or.inr ⟨P₁,P₂,hP₁,hP₂,hP⟩
    | exact Or.inl ⟨P₂,P₁,hP₂,hP₁,hP'⟩
    | exact Or.inr ⟨P₂,P₁,hP₂,hP₁,hP'⟩
end Links
end DeanK5
end M2
section M3
namespace DeanK5
open SimpleGraph
section Families
variable {V W : Type} {G : SimpleGraph V}
def AdmH (G : SimpleGraph V) (x y : V) (q : ℕ) (S : Set V) : Prop :=
  ∃ a d : ℕ,2≤ a∧(d=1∨d=2) ∧
    ∀ i : Fin q,∃ p : G.Walk x y,p.IsPath∧p.length=a+i.val*d∧∀ v∈p.support,v∈S
theorem AdmH.mono {x y : V} {q : ℕ} {S T : Set V} (h : AdmH G x y q S) (hST : S⊆T) :
    AdmH G x y q T:=by
  obtain ⟨a,d,ha,hd,h⟩:=h
  exact ⟨a,d,ha,hd,fun i=>(h i).elim fun p hp=>⟨p,hp.1,hp.2.1,fun v hv =>
    hST (hp.2.2 v hv)⟩⟩
theorem AdmH.admissible {x y : V} {q : ℕ} {S : Set V} (h : AdmH G x y q S) :
    Adm0 G x y q:=by
  obtain ⟨a,d,ha,hd,h⟩:=h
  exact ⟨a,d,ha,hd,fun i=>(h i).elim fun p hp=>⟨p,hp.1,hp.2.1⟩⟩
theorem qx7 {H : SimpleGraph W} (f : H →g G) (hf : Function.Injective f) {x y : W}
    {q : ℕ} (h : Adm0 H x y q) : AdmH G (f x) (f y) q (Set.range f):=by
  obtain ⟨a,d,ha,hd,h⟩:=h
  refine ⟨a,d,ha,hd,fun i=>?_⟩
  obtain ⟨p,hp,hl⟩:=h i
  refine ⟨p.map f,qb8 f hf hp,by rw [Walk.length_map,hl],fun v hv=>?_⟩
  rw [Walk.support_map,List.mem_map] at hv
  obtain ⟨w,-,rfl⟩:=hv
  exact ⟨w,rfl⟩
theorem qar1 {X : Finset V} {x y : (X : Set V)} {q : ℕ}
    (h : Adm0 (G.induce (X : Set V)) x y q) : AdmH G x.1 y.1 q (X : Set V):=by
  refine (qx7 (Embedding.induce (G:=G) (X : Set V)).toHom
    (Embedding.induce (G:=G) _).injective h).mono ?_
  rintro _ ⟨v,rfl⟩
  exact v.2
theorem AdmH.false (hG : Nf0 G) {x y : V} {A₁ A₂ : Set V}
    (h₁ : AdmH G x y 3 (insert x (insert y A₁))) (h₂ : AdmH G x y 3 (insert x (insert y A₂)))
    (hA : Disjoint A₁ A₂) : False:=by
  obtain ⟨a₁,d₁,ha₁,hd₁,h₁⟩:=h₁
  obtain ⟨a₂,d₂,ha₂,hd₂,h₂⟩:=h₂
  choose P hP using h₁
  choose Q hQ using h₂
  refine qe0 hG (b:=0) (by norm_num) (by norm_num) (by norm_num)
    hd₁ hd₂ P Q (fun i=>⟨(hP i).1,(hP i).2.1⟩) (fun j=>⟨(hQ j).1,(hQ j).2.1⟩)
    (fun i j v hv hw=>?_) (fun i j=>by rw [(hP i).2.1,(hQ j).2.1];omega)
  have h1:=(hP i).2.2 v hv
  have h2:=(hQ j).2.2 v hw
  simp only [Set.mem_insert_iff] at h1 h2
  by_contra hne
  push Not at hne
  exact Set.disjoint_left.mp hA ((h1.resolve_left hne.1).resolve_left hne.2)
    ((h2.resolve_left hne.1).resolve_left hne.2)
end Families
section Restore
variable {V W : Type}
theorem qan4 [Fintype W] (h : 3 < Fintype.card W) (a b c : W) :
    ∃ v,v≠a∧v≠b∧v≠c:=by
  classical
  obtain ⟨v,-,hv⟩:=Finset.exists_mem_notMem_of_card_lt_card (s:={a,b,c})
    (t:=Finset.univ) (by rw [Finset.card_univ];exact lt_of_le_of_lt Finset.card_le_three h)
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hv
  exact ⟨v,hv.1,hv.2.1,hv.2.2⟩
theorem qak1 (coy : COY4) [Fintype W] [DecidableEq W] {H : SimpleGraph W} [DecidableRel H.Adj]
    {x y : W} (hr : Rt0 H x y) (hW : 4≤ Fintype.card W) {q : ℕ} (hq1 : 1≤ q) (hq4 : q≤ 4)
    {Z : Finset W} (_hxZ : x∉Z) (_hyZ : y∉Z) (hq : ∀ v,v≠x→ v≠y→ q≤ H.degree v)
    (hq' : ∀ v,v≠x→ v≠y→ v∉Z→ q+1≤ H.degree v) :
    (Z.card≤ 1→ Adm0 H x y q) ∧
      (2≤ Z.card→ Adm0 (av0 H Z) (some x) (some y) q):=by
  refine ⟨fun hZ=>?_,fun hZ=>?_⟩
  · have : Nonempty W:=⟨x⟩
    obtain ⟨a,ha⟩:=Finset.card_le_one_iff_subset_singleton.mp hZ
    obtain ⟨w,hwx,hwy,hwa⟩:=qan4 (by omega) x y a
    refine coy W H x y (some a) q hq1 hq4 hr
      ⟨w,hwx,hwy,fun h=>hwa (Option.some_injective _ h).symm⟩
      fun v hvx hvy hva=>hq' v hvx hvy fun hv=>hva ?_
    rw [Finset.mem_singleton.mp (ha hv)]
  · obtain ⟨w,hwx,hwy⟩:=qf8 (by omega) x y
    refine coy (Option W) (av0 H Z) (some x) (some y) (some none) q hq1 hq4
      (qt6 hr hZ) ⟨some w,by simpa using hwx,by simpa using hwy,by simp⟩ ?_
    rintro (_|v) hvx hvy hvn
    · exact absurd rfl hvn
    · rw [qi2]
      have hvx' : v≠x:=fun h=>hvx (h ▸ rfl)
      have hvy' : v≠y:=fun h=>hvy (h ▸ rfl)
      split_ifs with hvZ
      · exact Nat.add_le_add_right (hq v hvx' hvy') 1
      · exact (hq' v hvx' hvy' hvZ).trans (Nat.le_add_right _ _)
variable {B : SimpleGraph V}
theorem qq2 [DecidableEq V] (coy : COY4) {X : Finset V}
    {H : SimpleGraph (X : Set V)} [DecidableRel H.Adj] (hHB : H≤ B.induce (X : Set V))
    {x y : (X : Set V)} (hr : Rt0 H x y) (hX : 4≤ X.card) {q : ℕ} (hq1 : 1≤ q)
    (hq4 : q≤ 4) {Z : Finset (X : Set V)} (hxZ : x∉Z) (hyZ : y∉Z)
    (hq : ∀ v,v≠x→ v≠y→ q≤ H.degree v)
    (hq' : ∀ v,v≠x→ v≠y→ v∉Z→ q+1≤ H.degree v) {c : Option V}
    (hcX : ∀ cv,c=some cv→ cv∉X) (hcZ : ∀ v∈Z,∃ cv,c=some cv∧B.Adj cv v.1) :
    AdmH B x.1 y.1 q ((X : Set V)∪{v|2≤ Z.card∧c=some v}):=by
  obtain ⟨h1,h2⟩:=qak1 coy hr (by simpa using hX) hq1 hq4 hxZ hyZ hq hq'
  by_cases hZ : 2≤ Z.card
  · obtain ⟨z,hz⟩:=Finset.card_pos.mp (by omega : 0 < Z.card)
    obtain ⟨cv,hcv,-⟩:=hcZ z hz
    have hadj : ∀ v∈Z,B.Adj cv v.1:=fun v hv=>by
      obtain ⟨cv',hcv',h⟩:=hcZ v hv
      obtain rfl : cv=cv':=Option.some_injective _ (hcv.symm.trans hcv')
      exact h
    let f : av0 H Z →g B:=⟨fun o=>o.elim cv Subtype.val,fun {a b} h=>by
      rcases a with _|a <;> rcases b with _|b
      exacts [absurd h adjoin_not_adj_none,hadj b h,(hadj a h).symm,hHB h]⟩
    have hf : Function.Injective f:=by
      rintro (_|a) (_|b) h
      · rfl
      · exact (hcX cv hcv (by rw [show cv=b.1 from h];exact b.2)).elim
      · exact (hcX cv hcv (by rw [← show a.1=cv from h];exact a.2)).elim
      · exact congrArg some (Subtype.ext h)
    refine (qx7 f hf (h2 hZ)).mono ?_
    rintro _ ⟨_|v,rfl⟩
    · exact Or.inr ⟨hZ,hcv⟩
    · exact Or.inl v.2
  · refine (qx7 ((Embedding.induce (X : Set V)).toHom.comp (Hom.ofLE hHB))
      (fun a b h=>Subtype.ext h) (h1 (by omega))).mono ?_
    rintro _ ⟨v,rfl⟩
    exact Or.inl v.2
theorem qa5 [DecidableRel B.Adj] (X : Finset V) (v : (X : Set V)) :
    (B.induce (X : Set V)).degree v=(X.filter (B.Adj v.1)).card:=by
  rw [← card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun w _=>w.1) (fun w hw=>?_) (fun a _ b _ h=>Subtype.ext h)
    (fun b hb=>?_)
  · rw [mem_neighborFinset] at hw
    exact Finset.mem_filter.mpr ⟨w.2,hw⟩
  · obtain ⟨hbX,hb⟩:=Finset.mem_filter.mp hb
    exact ⟨⟨b,hbX⟩,(mem_neighborFinset _ _ _).mpr hb,rfl⟩
theorem qc3 [DecidableRel B.Adj] {X : Finset V} {v : V} (hv : v∈X) :
    (X.filter (B.Adj v)).card < X.card :=
  Finset.card_lt_card (Finset.filter_ssubset.mpr ⟨v,hv,B.irrefl⟩)
theorem qb5 [Fintype V] [DecidableRel B.Adj] (v : V) :
    B.degree v=(Finset.univ.filter (B.Adj v)).card:=by
  rw [← card_neighborFinset_eq_degree,neighborFinset_eq_filter]
theorem qal8 [DecidableEq V] [DecidableRel B.Adj] (coy : COY4) {X : Finset V} {x y : V}
    (hx : x∈X) (hy : y∈X) (hr : Rt0 (B.induce (X : Set V)) ⟨x,hx⟩ ⟨y,hy⟩)
    {Z : Finset V} {c : Option V} (hZ : ∀ v∈Z,v∈X∧v≠x∧v≠y)
    (hcX : ∀ cv,c=some cv→ cv∉X) (hcZ : ∀ v∈Z,∃ cv,c=some cv∧B.Adj cv v)
    (h3 : ∀ v∈X,v≠x→ v≠y→ 3≤ (X.filter (B.Adj v)).card)
    (h4 : ∀ v∈X,v≠x→ v≠y→ v∉Z→ 4≤ (X.filter (B.Adj v)).card) :
    AdmH B x y 3 ((X : Set V)∪{v|2≤ Z.card∧c=some v}):=by
  set Z' : Finset (X : Set V):=Finset.univ.filter fun v=>v.1∈Z with hZ'
  have hcard : Z'.card=Z.card:=Finset.card_bij (fun v _=>v.1)
    (fun v hv=>(Finset.mem_filter.mp hv).2) (fun a _ b _ h=>Subtype.ext h)
    (fun b hb=>⟨⟨b,(hZ b hb).1⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hb⟩,rfl⟩)
  have hne : ∀ {v : (X : Set V)} {a : V} {ha : a∈X},v≠⟨a,ha⟩→ v.1≠a :=
    fun h h'=>h (Subtype.ext h')
  obtain ⟨w,hwx,hwy⟩:=qf8 hr.2.1 ⟨x,hx⟩ ⟨y,hy⟩
  have hX : 4≤ X.card:=by
    have:=h3 w.1 w.2 (hne hwx) (hne hwy)
    have:=qc3 (B:=B) w.2
    omega
  have h:=qq2 coy le_rfl hr hX (q:=3) (by norm_num) (by norm_num) (Z:=Z')
    (fun h=>(hZ x (Finset.mem_filter.mp h).2).2.1 rfl)
    (fun h=>(hZ y (Finset.mem_filter.mp h).2).2.2 rfl)
    (fun v h1 h2=>by rw [qa5];exact h3 v.1 v.2 (hne h1) (hne h2))
    (fun v h1 h2 h3'=>by
      rw [qa5]
      exact h4 v.1 v.2 (hne h1) (hne h2) fun h =>
        h3' (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))
    hcX (fun v hv=>hcZ v.1 (Finset.mem_filter.mp hv).2)
  rwa [hcard] at h
end Restore
section Sides
variable {V : Type} {B : SimpleGraph V}
theorem qf9 {T C : Finset V} (hl : Lk0 B T) (hCT : C⊆T) {c u : V} (hc : c∈C)
    (hu : u∈T) (huC : u∉C) : ∃ a∈C,∃ d∈T,d∉C∧B.Adj a d:=by
  by_contra hno
  push Not at hno
  obtain ⟨p,hp⟩:=hl c (hCT hc) u hu
  exact huC (qb9 (D:=fun w=>w∉T) (fun a ha w hw=>(em (w∈T)).imp
    (fun hwT=>not_not.mp fun hwC=>hno a ha w hwT hwC hw) id) p hc
    (fun a ha h=>h (hp a ha)) u p.end_mem_support)
theorem qi7 (Y : Finset V) {u : V} (hu : u∈Y) :
    ∃ Q⊆Y,(∀ a,a∈Q↔Rc0 B Y u a)∧Lk0 B Q ∧
      ∀ q∈Q,∀ d∈Y,B.Adj q d→ d∈Q:=by
  classical
  have hcl : ∀ q∈Y.filter (Rc0 B Y u),∀ d∈Y,B.Adj q d→ d∈Y.filter (Rc0 B Y u) :=
    fun q hq d hd h=>Finset.mem_filter.mpr ⟨hd,(Finset.mem_filter.mp hq).2.trans
      (Rc0.adj (Finset.mem_filter.mp hq).1 hd h)⟩
  refine ⟨_,Finset.filter_subset _ _,fun a=>⟨fun h=>(Finset.mem_filter.mp h).2,
    fun h=>Finset.mem_filter.mpr ⟨h.right_mem,h⟩⟩,qa4 u fun a ha=>?_,hcl⟩
  obtain ⟨p,hp⟩:=(Finset.mem_filter.mp ha).2
  exact ⟨p,qb9 (D:=fun w=>w∉Y) (fun q hq w hw=>(em (w∈Y)).imp
    (fun h=>hcl q hq w h hw) id) p (Finset.mem_filter.mpr ⟨hu,Rc0.refl hu⟩)
    (fun a ha h=>h (hp a ha))⟩
theorem qad6 [DecidableEq V] {X K Y Q : Finset V} {x y : V}
    (hY : ∀ d,d∈Y↔d∈X∧d≠x∧d≠y∧d∉K) (hQY : Q⊆Y)
    (hQcl : ∀ q∈Q,∀ d∈Y,B.Adj q d→ d∈Q) (hQne : Q.Nonempty)
    (hl : Lk0 B (X\insert y K)) (hx : x∈X) (hxy : x≠y) (hxK : x∉K) :
    ∃ q∈Q,B.Adj x q:=by
  obtain ⟨q₀,hq₀⟩:=hQne
  have hsub : Q⊆X\insert y K:=fun q hq=>by
    obtain ⟨h1,-,h2,h3⟩:=(hY q).mp (hQY hq)
    simp [h1,h2,h3]
  obtain ⟨a,ha,d,hd,hdQ,had⟩:=qf9 hl hsub hq₀
    (by simp [hx,hxy,hxK] : x∈X\insert y K) (fun h=>((hY x).mp (hQY h)).2.1 rfl)
  by_cases hdx : d=x
  · exact ⟨a,ha,hdx ▸ had.symm⟩
  · simp only [Finset.mem_sdiff,Finset.mem_insert,not_or] at hd
    exact absurd (hQcl a ha d ((hY d).mpr ⟨hd.1,hdx,hd.2.1,hd.2.2⟩) had) hdQ
theorem qaj4 [DecidableEq V] [DecidableRel B.Adj] (coy : COY4) {X K Y Q : Finset V}
    {x y : V} {c : Option V} (hx : x∈X) (hy : y∈X) (hxy : x≠y) (hxK : x∉K)
    (hyK : y∉K) (hK1 : K.card≤ 1) (hY : ∀ d,d∈Y↔d∈X∧d≠x∧d≠y∧d∉K)
    (hl : ∀ w,Lk0 B (X\insert w K)) (hQY : Q⊆Y) (hQ : Lk0 B Q) (hQne : Q.Nonempty)
    (hQcl : ∀ q∈Q,∀ d∈Y,B.Adj q d→ d∈Q)
    (hδ : ∀ v∈Q,4≤ (X.filter (B.Adj v)).card)
    (hcX : ∀ cv,c=some cv→ cv∉insert x (insert y Q))
    (hcZ : ∀ v∈Q,(X.filter (B.Adj v)).card≤ 4→ (∃ k∈K,B.Adj v k) →
      ∃ cv,c=some cv∧B.Adj cv v) :
    AdmH B x y 3 (insert x (insert y ((Q : Set V)∪{v|c=some v}))):=by
  have hQ' : ∀ q∈Q,q∈X∧q≠x∧q≠y∧q∉K:=fun q hq=>(hY q).mp (hQY hq)
  have hcl : ∀ q∈Q,∀ d∈X,B.Adj q d→ d=x∨d=y∨d∈Q∨d∈K:=by
    intro q hq d hd h
    by_contra hn
    push Not at hn
    exact hn.2.2.1 (hQcl q hq d ((hY d).mpr ⟨hd,hn.1,hn.2.1,hn.2.2.2⟩) h)
  have hxQ : x∉Q:=fun h=>(hQ' x h).2.1 rfl
  have hyQ : y∉Q:=fun h=>(hQ' y h).2.2.1 rfl
  have hcut : ∀ w∈Q,∀ C⊆Q.erase w,C.Nonempty →
      (∀ a∈C,∀ d∈Q.erase w,B.Adj a d→ d∈C)→ ∃ a∈C,B.Adj a x∨B.Adj a y:=by
    intro w hw C hC hCne hCcl
    by_contra hno
    push Not at hno
    obtain ⟨c₀,hc₀⟩:=hCne
    have hsub : C⊆X\insert w K:=fun a ha=>by
      have h1:=hC ha
      obtain ⟨h2,-,-,h3⟩:=hQ' a (Finset.mem_of_mem_erase h1)
      simp [h2,h3,Finset.ne_of_mem_erase h1]
    obtain ⟨a,ha,d,hd,hdC,had⟩:=qf9 (hl w) hsub hc₀
      (by simp [hx,hxK,show x≠w from fun h=>hxQ (h ▸ hw)] : x∈X\insert w K)
      (fun h=>hxQ (Finset.mem_of_mem_erase (hC h)))
    simp only [Finset.mem_sdiff,Finset.mem_insert,not_or] at hd
    rcases hcl a (Finset.mem_of_mem_erase (hC ha)) d hd.1 had with h|h|hdQ|hdK
    · exact (hno a ha).1 (h ▸ had)
    · exact (hno a ha).2 (h ▸ had)
    · exact hdC (hCcl a ha d (Finset.mem_erase.mpr ⟨hd.2.1,hdQ⟩) had)
    · exact hd.2.2 hdK
  have hr:=rooted_delEdge_iff.mp (qak0 hxy hxQ hyQ hQ
    (qad6 hY hQY hQcl hQne (hl y) hx hxy hxK)
    (qad6 (fun d=>by rw [hY d];tauto) hQY hQcl hQne (hl x) hy hxy.symm hyK)
    hcut (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)))
  have hmem : ∀ v∈insert x (insert y Q),v≠x→ v≠y→ v∈Q:=fun v hv h1 h2=>by
    simp only [Finset.mem_insert] at hv
    tauto
  have hside : ∀ v∈Q,(X.filter (B.Adj v)).card ≤
      ((insert x (insert y Q)).filter (B.Adj v)).card+(K.filter (B.Adj v)).card :=
    fun v hv=>by
      refine (Finset.card_le_card fun d hd=>?_).trans (Finset.card_union_le _ _)
      obtain ⟨hdX,hvd⟩:=Finset.mem_filter.mp hd
      rcases hcl v hv d hdX hvd with rfl|rfl|h|h
      · simp [hvd]
      · simp [hvd]
      · simp [h,hvd]
      · simp [h,hvd]
  refine (qal8 coy _ _ hr (c:=c)
    (Z:=Q.filter fun v=>(X.filter (B.Adj v)).card≤ 4∧∃ k∈K,B.Adj v k)
    (fun v hv=>have hv:=(Finset.mem_filter.mp hv).1
      ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv),(hQ' v hv).2.1,(hQ' v hv).2.2.1⟩)
    hcX (fun v hv=>hcZ v (Finset.mem_filter.mp hv).1 (Finset.mem_filter.mp hv).2.1
      (Finset.mem_filter.mp hv).2.2)
    (fun v hv h1 h2=>?_) (fun v hv h1 h2 hvZ=>?_)).mono ?_
  · have:=hside v (hmem v hv h1 h2)
    have:=hδ v (hmem v hv h1 h2)
    have:=(Finset.card_filter_le K (B.Adj v)).trans hK1
    omega
  · have hvQ:=hmem v hv h1 h2
    have hs:=hside v hvQ
    have:=hδ v hvQ
    have:=(Finset.card_filter_le K (B.Adj v)).trans hK1
    rcases (K.filter (B.Adj v)).eq_empty_or_nonempty with h|⟨k,hk⟩
    · rw [h,Finset.card_empty] at hs
      omega
    · have : ¬ (X.filter (B.Adj v)).card≤ 4:=fun h' =>
        hvZ (Finset.mem_filter.mpr ⟨hvQ,h',k,Finset.mem_filter.mp hk⟩)
      omega
  · intro v hv
    simp only [Set.mem_union,Finset.coe_insert,Set.mem_insert_iff,Finset.mem_coe,
      Set.mem_ofPred_eq] at hv ⊢
    tauto
theorem qao9 [DecidableEq V] [DecidableRel B.Adj] (coy : COY4) (hB : Nf0 B)
    {X K : Finset V} {x y : V} {e c : Option V} (hx : x∈X) (hy : y∈X) (hxy : x≠y)
    (hxK : x∉K) (hyK : y∉K) (he : ∀ k,e=some k↔k∈K) (hKX : K⊆X)
    (hcX : ∀ cv,c=some cv→ cv∉X) (hl : ∀ w,Lk0 B (X\insert w K))
    (hδ : ∀ v∈X,v≠x→ v≠y→ v∉K→ 4≤ (X.filter (B.Adj v)).card)
    (hD : ∀ v∈X,(X.filter (B.Adj v)).card≤ 4→ (∃ k∈K,B.Adj v k) →
      ∃ cv,c=some cv∧B.Adj cv v)
    (hcut : ¬ Lk0 B (X\insert x (insert y K))) : False:=by
  have hY : ∀ d,d∈X\insert x (insert y K)↔d∈X∧d≠x∧d≠y∧d∉K :=
    fun d=>by simp
  have hK1 : K.card≤ 1:=Finset.card_le_one.mpr fun a ha b hb =>
    Option.some_injective _ (((he a).mpr ha).symm.trans ((he b).mpr hb))
  simp only [Lk0,not_forall] at hcut
  obtain ⟨u,hu,v,hv,huv⟩:=hcut
  obtain ⟨Q₁,hQ₁Y,hQ₁r,hQ₁,hQ₁cl⟩:=qi7 (B:=B) _ hu
  obtain ⟨Q₂,hQ₂Y,hQ₂r,hQ₂,hQ₂cl⟩:=qi7 (B:=B) _ hv
  have hQ : ∀ {Q},Q⊆X\insert x (insert y K)→ ∀ w∈Q,w∈X∧w≠x∧w≠y∧w∉K :=
    fun hQY w hw=>(hY w).mp (hQY hw)
  have hδQ : ∀ {Q},Q⊆X\insert x (insert y K)→ ∀ w∈Q,4≤ (X.filter (B.Adj w)).card :=
    fun hQY w hw=>have h:=hQ hQY w hw;hδ w h.1 h.2.1 h.2.2.1 h.2.2.2
  have h₁:=qaj4 coy (c:=e) hx hy hxy hxK hyK hK1 hY hl hQ₁Y hQ₁
    ⟨u,(hQ₁r u).mpr (Rc0.refl hu)⟩ hQ₁cl (hδQ hQ₁Y) (fun k hk h=>by
      have hkK:=(he k).mp hk
      simp only [Finset.mem_insert] at h
      rcases h with rfl|rfl|h
      exacts [hxK hkK,hyK hkK,(hQ hQ₁Y k h).2.2.2 hkK])
    (fun w _ _ ⟨k,hk,hwk⟩=>⟨k,(he k).mpr hk,hwk.symm⟩)
  have h₂:=qaj4 coy (c:=c) hx hy hxy hxK hyK hK1 hY hl hQ₂Y hQ₂
    ⟨v,(hQ₂r v).mpr (Rc0.refl hv)⟩ hQ₂cl (hδQ hQ₂Y) (fun cv hcv h=>hcX cv hcv (by
      simp only [Finset.mem_insert] at h
      rcases h with rfl|rfl|h
      exacts [hx,hy,(hQ hQ₂Y cv h).1]))
    (fun w hw=>hD w (hQ hQ₂Y w hw).1)
  refine h₁.false hB h₂ (Set.disjoint_left.mpr fun a ha hb=>?_)
  simp only [Set.mem_union,Finset.mem_coe,Set.mem_ofPred_eq] at ha hb
  rcases ha with ha|ha <;> rcases hb with hb|hb
  · exact huv (((hQ₁r a).mp ha).trans ((hQ₂r a).mp hb).symm)
  · exact hcX a hb (hQ hQ₁Y a ha).1
  · exact (hQ hQ₂Y a hb).2.2.2 ((he a).mp ha)
  · exact hcX a hb (hKX ((he a).mp ha))
theorem qak3 [DecidableEq V] [DecidableRel B.Adj] (coy : COY4) (hB : Nf0 B)
    {U : Finset V} {c : Option V} (hcU : ∀ cv,c=some cv→ cv∉U)
    (hδ : ∀ v∈U,4≤ (U.filter (B.Adj v)).card)
    (hD : ∀ v∈U,(U.filter (B.Adj v)).card≤ 4→ ∃ cv,c=some cv∧B.Adj cv v)
    (L2 : ∀ T : Finset V,T.card < 2→ Lk0 B (U\T)) :
    ∀ T : Finset V,T.card < 4→ Lk0 B (U\T):=by
  have reduce : ∀ {k : ℕ},(∀ T : Finset V,T.card < k→ Lk0 B (U\T)) →
      ∀ T : Finset V,T.card≤ k→ ¬ T⊆U→ Lk0 B (U\T):=by
    intro k hk T hT hTU
    obtain ⟨t,htT,htU⟩:=Finset.not_subset.mp hTU
    have : U\T=U\T.erase t:=by
      ext a
      simp only [Finset.mem_sdiff,Finset.mem_erase,not_and]
      exact ⟨fun h=>⟨h.1,fun _=>h.2⟩,fun h=>⟨h.1,h.2 fun hat=>htU (hat ▸ h.1)⟩⟩
    rw [this]
    exact hk _ (by rw [Finset.card_erase_of_mem htT];have:=Finset.card_pos.mpr ⟨t,htT⟩;omega)
  have L3 : ∀ T : Finset V,T.card < 3→ Lk0 B (U\T):=by
    intro T hT
    by_cases hTU : T⊆U
    · rcases (by omega : T.card < 2∨T.card=2) with h|h
      · exact L2 T h
      · obtain ⟨x,y,hxy,rfl⟩:=Finset.card_eq_two.mp h
        by_contra hno
        exact qao9 coy hB (K:=∅) (e:=none) (c:=none) (hTU (by simp)) (hTU (by simp)) hxy
          (by simp) (by simp) (by simp) (Finset.empty_subset _) (by simp)
          (fun w=>L2 _ (by simp)) (fun v hv _ _ _=>hδ v hv) (by simp) (by simpa using hno)
    · exact reduce L2 T (by omega) hTU
  intro T hT
  by_cases hTU : T⊆U
  · rcases (by omega : T.card < 3∨T.card=3) with h|h
    · exact L3 T h
    · obtain ⟨x,y,z,hxy,hxz,hyz,rfl⟩:=Finset.card_eq_three.mp h
      by_contra hno
      exact qao9 coy hB (K:={z}) (e:=some z) (c:=c) (hTU (by simp)) (hTU (by simp)) hxy
        (by simpa using hxz) (by simpa using hyz)
        (fun k=>by rw [Option.some_inj,Finset.mem_singleton,eq_comm])
        (Finset.singleton_subset_iff.mpr (hTU (by simp))) hcU
        (fun w=>L3 _ (Finset.card_le_two.trans_lt (by norm_num))) (fun v hv _ _ _=>hδ v hv)
        (fun v hv h _=>hD v hv h) hno
  · exact reduce L3 T (by omega) hTU
theorem kConn_induce_iff [DecidableEq V] {U : Finset V} {k : ℕ} :
    Kc0 (B.induce (U : Set V)) k ↔
      k < U.card∧∀ T : Finset V,T.card < k→ Lk0 B (U\T):=by
  have hc : Fintype.card (U : Set V)=U.card:=by simp
  rw [kConn_iff_linked,hc]
  refine and_congr_right fun _=>⟨fun h T hT u hu v hv=>?_,fun h T hT u hu v hv=>?_⟩
  · have hu':=Finset.mem_sdiff.mp hu
    have hv':=Finset.mem_sdiff.mp hv
    have hT' : (Finset.univ.filter fun a : (U : Set V)=>a.1∈T).card < k :=
      lt_of_le_of_lt (Finset.card_le_card_of_injOn Subtype.val
        (fun a ha=>(Finset.mem_filter.mp ha).2) (fun a _ b _ h=>Subtype.ext h)) hT
    exact (h _ hT' ⟨u,hu'.1⟩ (by simp [hu'.2]) ⟨v,hv'.1⟩ (by simp [hv'.2])).map
      (Embedding.induce (G:=B) _).toHom fun a ha=>Finset.mem_sdiff.mpr ⟨a.2,fun h' =>
        Finset.mem_compl.mp ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h'⟩)⟩
  · have hT' : (T.map (Function.Embedding.subtype _)).card < k:=by rwa [Finset.card_map]
    have hm : ∀ a : (U : Set V),a∉T→ a.1∈U\T.map (Function.Embedding.subtype _) :=
      fun a ha=>Finset.mem_sdiff.mpr ⟨a.2,fun h=>by
        obtain ⟨b,hb,hba⟩:=Finset.mem_map.mp h
        exact ha (Subtype.ext hba ▸ hb)⟩
    obtain ⟨p,hp⟩:=h _ hT' u.1 (hm u (Finset.mem_compl.mp hu)) v.1
      (hm v (Finset.mem_compl.mp hv))
    obtain ⟨q,-,hq⟩:=qv2 (Embedding.induce (U : Set V)) p u v rfl rfl fun a ha =>
      ⟨⟨a,(Finset.mem_sdiff.mp (hp a ha)).1⟩,rfl⟩
    refine ⟨q,fun a ha=>Finset.mem_compl.mpr fun haT=>?_⟩
    have : a.1∈p.support:=by
      rw [← hq]
      exact List.mem_map_of_mem ha
    exact (Finset.mem_sdiff.mp (hp _ this)).2 (Finset.mem_map_of_mem _ haT)
end Sides
structure H40 {V : Type} [Fintype V] [DecidableEq V] (B : SimpleGraph V)
    [DecidableRel B.Adj] where
  U : Finset V
  c : Option V
  hc_not_mem : ∀ v,c=some v→ v∉U
  hc_compl : ∀ v,v∈U∨c=some v
  hconn4 : Kc0 (B.induce (U : Set V)) 4
  hdeg4 : ∀ v : (U : Set V),4≤ (B.induce (U : Set V)).degree v
  D : Finset (U : Set V)
  hD_def : ∀ v : (U : Set V),v∈D↔(B.induce (U : Set V)).degree v=4
  hD_card : D.card≤ 4
  hD_adj : ∀ v∈D,∃ cv,c=some cv∧B.Adj cv v.val
  hdeg5_off_D : ∀ v : (U : Set V),v∉D→ 5≤ (B.induce (U : Set V)).degree v
section Host
variable {V : Type} [Fintype V] [DecidableEq V] {B : SimpleGraph V} [DecidableRel B.Adj]
theorem qw4 (coy : COY4) (hB : Nf0 B) {U : Finset V} {c : Option V}
    (hcU : ∀ v,c=some v→ v∉U) (hcomp : ∀ v,v∈U∨c=some v) (hUne : U.Nonempty)
    (hδ : ∀ v∈U,4≤ (U.filter (B.Adj v)).card)
    (hD : ∀ v∈U,(U.filter (B.Adj v)).card≤ 4→ ∃ cv,c=some cv∧B.Adj cv v)
    (hDc : (U.filter fun v=>(U.filter (B.Adj v)).card≤ 4).card≤ 4)
    (L2 : ∀ T : Finset V,T.card < 2→ Lk0 B (U\T)) : Nonempty (H40 B):=by
  have hU5 : 4 < U.card:=by
    obtain ⟨v,hv⟩:=hUne
    have:=hδ v hv
    have:=qc3 (B:=B) hv
    omega
  refine ⟨⟨U,c,hcU,hcomp,kConn_induce_iff.mpr ⟨hU5,qak3 coy hB hcU hδ hD L2⟩,
    fun v=>by rw [qa5];exact hδ v.1 v.2,
    Finset.univ.filter fun v=>(B.induce (U : Set V)).degree v=4,fun v=>by simp,
    ?_,fun v hv=>?_,fun v hv=>?_⟩⟩
  · refine le_trans (Finset.card_le_card_of_injOn (fun v=>v.1) (fun v hv=>?_)
      (fun a _ b _ h=>Subtype.ext h)) hDc
    have h4:=(Finset.mem_filter.mp hv).2
    rw [qa5] at h4
    exact Finset.mem_filter.mpr ⟨v.2,h4.le⟩
  · have h4:=(Finset.mem_filter.mp hv).2
    rw [qa5] at h4
    exact hD v.1 v.2 h4.le
  · have h4:=hδ v.1 v.2
    have hne : (B.induce (U : Set V)).degree v≠4:=fun h =>
      hv (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)
    rw [qa5] at hne ⊢
    omega
theorem qap5 (coy : COY4) (B : SimpleGraph V) [DecidableRel B.Adj] (h2 : Kc0 B 2)
    (hB : Nf0 B) (hdeg : ∃ opt : Option V,∀ v : V,opt≠some v→ 5≤ B.degree v) :
    Nonempty (H40 B):=by
  have hB2 : ∀ T : Finset V,T.card < 2→ Lk0 B (Finset.univ\T):=fun T hT=>by
    have:=(kConn_iff_linked.mp h2).2 T hT
    rwa [Finset.compl_eq_univ_sdiff] at this
  have hdf:=qb5 (B:=B)
  have hne : (Finset.univ : Finset V).Nonempty:=Finset.univ_nonempty_iff.mpr
    (Fintype.card_pos_iff.mp (by have:=h2.1;omega))
  by_cases hall : ∀ v,5≤ B.degree v
  · have h5 : ∀ v,5≤ (Finset.univ.filter (B.Adj v)).card:=fun v=>hdf v ▸ hall v
    refine qw4 coy hB (U:=Finset.univ) (c:=none) (fun v h=>absurd h (by simp))
      (fun v=>Or.inl (Finset.mem_univ v)) hne (fun v _=>(h5 v).trans' (by norm_num))
      (fun v _ h=>absurd (h5 v) (by omega)) ?_ hB2
    rw [Finset.card_eq_zero.mpr (Finset.filter_eq_empty_iff.mpr fun v _ h=>absurd (h5 v)
      (by omega))]
    exact Nat.zero_le _
  push Not at hall
  obtain ⟨cv,hcv⟩:=hall
  obtain ⟨opt,hopt⟩:=hdeg
  have hoc : opt=some cv:=by
    by_contra h
    exact absurd (hopt cv h) (by omega)
  have h5 : ∀ v,v≠cv→ 5≤ (Finset.univ.filter (B.Adj v)).card:=fun v hv =>
    hdf v ▸ hopt v (by rw [hoc];exact fun h=>hv (Option.some_injective _ h).symm)
  have hsub : ∀ v,Finset.univ.filter (B.Adj v) ⊆
      insert cv ((Finset.univ.erase cv).filter (B.Adj v)):=fun v a ha=>by
    by_cases hac : a=cv
    · exact hac ▸ Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (by simpa [hac] using ha)
  have hlow : ∀ v,v≠cv→ ((Finset.univ.erase cv).filter (B.Adj v)).card≤ 4 →
      B.Adj cv v:=fun v hv h=>by
    by_contra hadj
    have hsub' : Finset.univ.filter (B.Adj v)⊆(Finset.univ.erase cv).filter (B.Adj v) :=
      fun a ha=>by
        have:=(Finset.mem_filter.mp ha).2
        simp only [Finset.mem_filter,Finset.mem_erase,Finset.mem_univ,and_true]
        exact ⟨fun h=>hadj (h ▸ this.symm),this⟩
    have:=(h5 v hv).trans (Finset.card_le_card hsub')
    omega
  refine qw4 coy hB (U:=Finset.univ.erase cv) (c:=some cv)
    (fun v h=>by rw [Option.some_inj] at h;simp [h])
    (fun v=>(em (v=cv)).elim (fun h=>Or.inr (by rw [h])) fun h=>Or.inl (by simp [h]))
    ⟨_,Finset.mem_erase.mpr ⟨(qf8 h2.1 cv cv).choose_spec.1,Finset.mem_univ _⟩⟩
    (fun v hv=>?_) (fun v hv h=>⟨cv,rfl,hlow v (Finset.ne_of_mem_erase hv) h⟩) ?_ ?_
  · have:=(h5 v (Finset.ne_of_mem_erase hv)).trans
      ((Finset.card_le_card (hsub v)).trans (Finset.card_insert_le _ _))
    omega
  · refine le_trans (Finset.card_le_card fun v hv=>?_) ((hdf cv).symm.le.trans (by omega))
    obtain ⟨hv,h⟩:=Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlow v (Finset.ne_of_mem_erase hv) h⟩
  · intro T hT
    have hUT : Finset.univ.erase cv\T=Finset.univ\insert cv T:=by
      ext a
      simp
    rw [hUT]
    by_contra hno
    have hc2 : 2≤ (insert cv T).card:=by
      by_contra h
      exact hno (hB2 _ (by omega))
    have hcT : cv∉T:=fun h=>by
      rw [Finset.insert_eq_of_mem h] at hc2
      omega
    rw [Finset.card_insert_of_notMem hcT] at hc2
    obtain ⟨w,rfl⟩:=Finset.card_eq_one.mp (by omega : T.card=1)
    exact qao9 coy hB (K:=∅) (e:=none) (c:=none) (Finset.mem_univ cv)
      (Finset.mem_univ w) (fun h=>hcT (by simp [h])) (by simp) (by simp) (by simp)
      (Finset.empty_subset _) (by simp) (fun w=>hB2 _ (by simp))
      (fun v _ hv _ _=>(h5 v hv).trans' (by norm_num)) (by simp) (by simpa using hno)
namespace H40
variable (h : H40 B)
theorem card_U : 5≤ h.U.card:=(kConn_induce_iff.mp h.hconn4).1
theorem linked : ∀ T : Finset V,T.card < 4→ Lk0 B (h.U\T) :=
  (kConn_induce_iff.mp h.hconn4).2
theorem qam7 (hc : h.c=none) : h.D=∅ :=
  Finset.eq_empty_of_forall_notMem fun v hv=>by
    obtain ⟨cv,hcv,-⟩:=h.hD_adj v hv
    simp [hc] at hcv
theorem qap9 {v : V} (hv : v∈h.U) : 5≤ B.degree v:=by
  have hsub : h.U.filter (B.Adj v)⊆Finset.univ.filter (B.Adj v) :=
    Finset.filter_subset_filter _ (Finset.subset_univ _)
  have hJ : (B.induce (h.U : Set V)).degree ⟨v,hv⟩=(h.U.filter (B.Adj v)).card :=
    qa5 h.U ⟨v,hv⟩
  rw [qb5]
  by_cases hD : (⟨v,hv⟩ : (h.U : Set V))∈h.D
  · obtain ⟨cv,hcv,hadj⟩:=h.hD_adj _ hD
    have : (insert cv (h.U.filter (B.Adj v))).card≤ (Finset.univ.filter (B.Adj v)).card :=
      Finset.card_le_card (Finset.insert_subset
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hadj.symm⟩) hsub)
    rw [Finset.card_insert_of_notMem fun h'=>h.hc_not_mem cv hcv (Finset.mem_filter.mp h').1]
      at this
    have:=(h.hD_def _).mp hD
    omega
  · have:=h.hdeg5_off_D _ hD
    have:=Finset.card_le_card hsub
    omega
theorem restore_on_sub (coy : COY4) {X : Finset V} (hXU : X⊆h.U) {x y : V} (hx : x∈X)
    (hy : y∈X) (hr : Rt0 (B.induce (X : Set V)) ⟨x,hx⟩ ⟨y,hy⟩) {Z : Finset V}
    (hZ : ∀ v∈Z,v∈X∧v≠x∧v≠y)
    (hZD : ∀ v (hv : v∈h.U),v∈Z→ (⟨v,hv⟩ : (h.U : Set V))∈h.D)
    (h3 : ∀ v∈X,v≠x→ v≠y→ 3≤ (X.filter (B.Adj v)).card)
    (h4 : ∀ v∈X,v≠x→ v≠y→ v∉Z→ 4≤ (X.filter (B.Adj v)).card) :
    AdmH B x y 3 ((X : Set V)∪{v|2≤ Z.card∧h.c=some v}) :=
  qal8 coy hx hy hr hZ (fun cv hcv hX=>h.hc_not_mem cv hcv (hXU hX))
    (fun v hv=>h.hD_adj _ (hZD v (hXU (hZ v hv).1) hv)) h3 h4
end H40
end Host
theorem qh6 (coy : COY4) {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hmin : 5≤ G.minDegree) (hG : Nf0 G) :
    ∃ E : Finset V,Nf0 (G.induce (E : Set V))∧Nonempty (H40 (G.induce (E : Set V))):=by
  rcases isEmpty_or_nonempty V with hV|⟨⟨v₀⟩⟩
  · simp at hmin
  have hd : ∀ v,5≤ (Finset.univ.filter (G.Adj v)).card:=fun v =>
    qb5 (B:=G) v ▸ hmin.trans (G.minDegree_le_degree v)
  obtain ⟨w₀,hw₀⟩:=Finset.card_pos.mp (by have:=hd v₀;omega :
    0 < (Finset.univ.filter (G.Adj v₀)).card)
  have hw₀Y : w₀∈Finset.univ.erase v₀:=by simp [(Finset.mem_filter.mp hw₀).2.ne.symm]
  obtain ⟨C,hCY,hCr,-,hCcl⟩:=qi7 (B:=G) _ hw₀Y
  obtain ⟨E,b,hE,-,-⟩:=qc8 (G:=G) C v₀
    (fun h=>Finset.notMem_erase v₀ _ (hCY h)) ⟨w₀,(hCr w₀).mpr (Rc0.refl hw₀Y)⟩
    fun c hc w hw=>(em (w=v₀)).symm.imp (fun hwv=>hCcl c hc w (by simp [hwv]) hw) id
  have hfE : ∀ v∈E,v≠b→ E.filter (G.Adj v)=Finset.univ.filter (G.Adj v) :=
    fun v hv hvb=>by
      ext a
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨fun h=>h.2,fun h=>⟨hE.2.2.1 v hv hvb a h,h⟩⟩
  obtain ⟨i,hiE,hib⟩:=Finset.exists_mem_ne (show 1 < E.card by have:=hE.2.1;omega) b
  have hE6 : 6≤ E.card:=by
    have:=qc3 (B:=G) hiE
    rw [hfE i hiE hib] at this
    have:=hd i
    omega
  refine ⟨E,qk1 _ hG,qap5 coy _ (hE.2.2.2.resolve_left (by omega))
    (qk1 _ hG) ⟨some ⟨b,hE.1⟩,fun v hv=>?_⟩⟩
  rw [qa5,hfE v.1 v.2 fun h=>hv (congrArg some (Subtype.ext h)).symm]
  exact hd v.1
end DeanK5
end M3
section M4
namespace DeanK5
open SimpleGraph
private theorem qae3 {V : Type} {B : SimpleGraph V} (hB : Nf0 B)
    {x y z u v : V} (hxy : B.Adj x y) (hyz : B.Adj y z) (hzu : B.Adj z u)
    (huv : B.Adj u v) (hvx : B.Adj v x) (hn : [x,y,z,u,v].Nodup) : False:=by
  let w:=Walk.cons hvx (Walk.cons hxy (Walk.cons hyz (Walk.cons hzu huv.toWalk)))
  have hw : w.IsCycle:=Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    ⟨Walk.IsPath.mk' hn,by change 3≤ 5;decide⟩
  exact hB _ w hw (by change 5∣5;decide)
section Host
variable {V : Type} [Fintype V] [DecidableEq V] {B : SimpleGraph V} [DecidableRel B.Adj]
theorem qaf5 (coy : COY4) (hB : Nf0 B) (h : H40 B)
    {x y a b : V} (hx : x∈h.U) (hy : y∈h.U) (ha : a∈h.U) (hb : b∈h.U)
    (hxb : x≠b) (hxy : B.Adj x y) (hxa : B.Adj x a) (hya : B.Adj y a)
    (hyb : B.Adj y b) (hab : B.Adj a b) : False:=by
  classical
  let T : Finset V:={a,b}
  let X:=h.U\T
  have hTU : T⊆h.U:=Finset.insert_subset ha (Finset.singleton_subset_iff.mpr hb)
  have hT : T.card=2:=by simp [T,hab.ne]
  have hxX : x∈X:=by simp [X,T,hx,hxa.ne,hxb]
  have hyX : y∈X:=by simp [X,T,hy,hya.ne,hyb.ne]
  have hXU : X⊆h.U:=Finset.sdiff_subset
  have hnotBoth (w : V) (hw : w∈X) (hwx : w≠x) (hwy : w≠y) :
      ¬ (B.Adj w a∧B.Adj w b):=by
    rintro ⟨hwa,hwb⟩
    exact qae3 hB hxy hyb hwb.symm hwa hxa.symm (by
      simp [hxy.ne,hxb,Ne.symm hwx,hxa.ne,hyb.ne,Ne.symm hwy,hya.ne,hwb.ne.symm,
        hab.ne.symm,hwa.ne])
  have hU:=h.card_U
  by_cases hsmall : h.U.card=5
  · have complete (u : V) (hu : u∈h.U) (v : V) (hv : v∈h.U) (hne : u≠v) :
        B.Adj u v:=by
      have hdeg:=h.hdeg4 ⟨u,hu⟩
      rw [qa5] at hdeg
      have he : h.U.filter (B.Adj u)=h.U.erase u :=
        Finset.eq_of_subset_of_card_le
          (fun w hw=>Finset.mem_erase.mpr
            ⟨(Finset.mem_filter.mp hw).2.ne.symm,(Finset.mem_filter.mp hw).1⟩)
          (by simpa [Finset.card_erase_of_mem hu,hsmall] using hdeg)
      exact (Finset.mem_filter.mp (he.symm ▸ Finset.mem_erase.mpr ⟨hne.symm,hv⟩)).2
    have hfour : ({x,y,a,b} : Finset V).card=4:=by
      simp [Finset.card_insert_of_notMem,hxy.ne,hxa.ne,hxb,hya.ne,hyb.ne,hab.ne]
    obtain ⟨w,hw,hn⟩:=Finset.exists_mem_notMem_of_card_lt_card (t:=h.U) (by rw [hfour,hsmall];decide)
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hn
    exact hnotBoth w (by simp [X,T,hw,hn.2.2.1,hn.2.2.2]) hn.1 hn.2.1
      ⟨complete w hw a ha hn.2.2.1,complete w hw b hb hn.2.2.2⟩
  have hX : 4≤ X.card:=by
    change 4≤ (h.U\T).card
    rw [Finset.card_sdiff_of_subset hTU,hT]
    omega
  have hr : Rt0 (B.induce (X : Set V)) ⟨x,hxX⟩ ⟨y,hyX⟩:=by
    apply qb4 hxy.ne (by omega) _ hxX hyX
    intro w _
    have he : X.erase w=h.U\(insert w T):=by
      ext v
      simp [X,and_left_comm]
    rw [he]
    exact (h.linked _ (lt_of_le_of_lt (Finset.card_insert_le _ _) (by omega))).mono_graph le_sup_left
  let Z:=X.filter fun v=>v≠x∧v≠y∧(∃ hv : v∈h.U,(⟨v,hv⟩ : (h.U : Set V))∈h.D)
  have hZ (v : V) (hv : v∈Z):=Finset.mem_filter.mp hv
  have hloss (v : V) (hv : v∈X) (hvx : v≠x) (hvy : v≠y) :
      (h.U.filter (B.Adj v)).card≤ (X.filter (B.Adj v)).card+1:=by
    have he : (h.U.filter (B.Adj v)).filter (fun w=>w∉T)=X.filter (B.Adj v):=by
      ext w
      simp [X,and_right_comm]
    have hn : (T.filter (B.Adj v)).card≤ 1:=by
      apply Finset.card_le_one_iff.mpr
      intro u w hu hw
      obtain ⟨hu,hadju⟩:=Finset.mem_filter.mp hu
      obtain ⟨hw,hadjw⟩:=Finset.mem_filter.mp hw
      simp only [T,Finset.mem_insert,Finset.mem_singleton] at hu hw
      rcases hu with rfl|rfl <;> rcases hw with rfl|rfl
      · rfl
      · exact (hnotBoth v hv hvx hvy ⟨hadju,hadjw⟩).elim
      · exact (hnotBoth v hv hvx hvy ⟨hadjw,hadju⟩).elim
      · rfl
    have he' : ((h.U.filter (B.Adj v)).filter fun w=>¬ w∉T)=T.filter (B.Adj v):=by
      ext w
      simp only [Finset.mem_filter,not_not]
      exact ⟨fun h=>⟨h.2,h.1.2⟩,fun h=>⟨⟨hTU h.1,h.2⟩,h.1⟩⟩
    have hc:=Finset.card_filter_add_card_filter_not (s:=h.U.filter (B.Adj v)) (·∉T)
    rw [he,he'] at hc
    omega
  have hpaths:=h.restore_on_sub coy hXU hxX hyX hr (Z:=Z)
    (fun v hv=>⟨(hZ v hv).1,(hZ v hv).2.1,(hZ v hv).2.2.1⟩)
    (fun v _ hv=>(hZ v hv).2.2.2.elim fun _ hD=>hD)
    (fun v hv hvx hvy=>by
      have hd:=h.hdeg4 ⟨v,hXU hv⟩
      rw [qa5] at hd
      change _≤ (h.U.filter (B.Adj v)).card at hd
      have:=hloss v hv hvx hvy
      omega)
    (fun v hv hvx hvy hvZ=>by
      have hd:=h.hdeg5_off_D ⟨v,hXU hv⟩ (fun hD =>
        hvZ (Finset.mem_filter.mpr ⟨hv,hvx,hvy,hXU hv,hD⟩))
      rw [qa5] at hd
      change _≤ (h.U.filter (B.Adj v)).card at hd
      have:=hloss v hv hvx hvy
      omega)
  obtain ⟨m,d,hm,hd,hpaths⟩:=hpaths
  choose P hP using hpaths
  let Q : Fin 3→ B.Walk x y :=
    ![hxy.toWalk,Walk.cons hxa hya.symm.toWalk,Walk.cons hxa (Walk.cons hab hyb.symm.toWalk)]
  have hQpath (i : Fin 3) : (Q i).IsPath:=by
    fin_cases i <;>
      simp [Q,Walk.isPath_def,hxy.ne,hxa.ne,hxb,hya.ne.symm,
        hab.ne,hyb.ne.symm]
  have hQlen (i : Fin 3) : (Q i).length=i.val+1:=by fin_cases i <;> rfl
  refine qe4 hB P Q (fun i=>(hP i).1) hQpath ?_ ?_ ?_ ?_
  · intro i j v hv hw
    have hv':=(hP i).2.2 v hv
    have hnot : v∉T:=by
      rcases hv' with hv'|⟨_,hc⟩
      · exact (Finset.mem_sdiff.mp hv').2
      · intro hvT
        exact h.hc_not_mem v hc (by
          simp only [T,Finset.mem_insert,Finset.mem_singleton] at hvT
          rcases hvT with rfl|rfl <;> assumption)
    fin_cases j <;> simp [Q] at hw <;>
      simp_all [T]
  · intro i j
    rw [(hP i).2.1,hQlen]
    omega
  · intro i j hij
    apply qg4 hd m 0
    change (P i).length % 5=(P j).length % 5 at hij
    simpa only [Nat.add_zero,(hP i).2.1,(hP j).2.1] using hij
  · intro i j hij
    change (Q i).length % 5=(Q j).length % 5 at hij
    rw [hQlen,hQlen] at hij
    have hi:=i.isLt
    have hj:=j.isLt
    exact Fin.ext (by omega)
private theorem qad3 {W : Type} [Fintype W] [DecidableEq W]
    {G : SimpleGraph W} [DecidableRel G.Adj] {S : Finset W}
    [DecidableRel (cs0 G S).Adj] (v : ((S : Set W)ᶜ : Set W))
    (hunique : ∀ a∈S,∀ b∈S,G.Adj v.1 a→ G.Adj v.1 b→ a=b) :
    (cs0 G S).degree (some v)=G.degree v.1:=by
  classical
  symm
  rw [← card_neighborFinset_eq_degree,← card_neighborFinset_eq_degree]
  let f (a : W):=if ha : a∈S then none else some (⟨a,ha⟩ : ((S : Set W)ᶜ : Set W))
  refine Finset.card_bij (fun a _=>f a) ?_ ?_ ?_
  · intro a ha
    rw [mem_neighborFinset] at ha ⊢
    by_cases h : a∈S
    · rw [show f a=none by simp [f,h]]
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,a,h,ha⟩
    · simpa [f,h,cs0] using ha
  · intro a ha b hb hab
    rw [mem_neighborFinset] at ha hb
    by_cases haS : a∈S <;> by_cases hbS : b∈S
    · exact hunique a haS b hbS ha hb
    · simp [f,haS,hbS] at hab
    · simp [f,haS,hbS] at hab
    · simpa [f,haS,hbS] using hab
  · intro o ho
    rw [mem_neighborFinset] at ho
    rcases o with _|a
    · obtain ⟨b,hb,hadj⟩:=(Finset.mem_filter.mp ho).2
      exact ⟨b,(mem_neighborFinset _ _ _).mpr hadj,by simp [f,hb]⟩
    · have ha : a.1∉S:=a.2
      exact ⟨a.1,(mem_neighborFinset _ _ _).mpr ho,by simp [f,ha]⟩
omit [Fintype V] [DecidableEq V] [DecidableRel B.Adj] in
private theorem qs1 (hB : Nf0 B) {p e t : V}
    (hep : B.Adj e p) (het : B.Adj e t) (htp : B.Adj t p)
    {w : B.Walk e p} (hw : w.IsPath) (hlen : 2≤ w.length) (ht : t∉w.support) :
    (¬ 5∣w.length+1)∧(¬ 5∣w.length+2):=by
  let long:=Walk.cons het htp.toWalk
  have hlong : long.IsPath:=by
    simp [long,Walk.isPath_def,het.ne,hep.ne,htp.ne]
  refine ⟨qc4 hB hw hep.isPath_toWalk (fun v _ hv=>?_) (by
    change 3≤ w.length+1
    omega),qc4 hB hw hlong (fun v hv hv'=>?_) (by
    change 3≤ w.length+2
    omega)⟩
  · simpa using hv
  · change v∈[e,t,p] at hv'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hv'
    rcases hv' with rfl|rfl|rfl
    · exact Or.inl rfl
    · exact (ht hv).elim
    · exact Or.inr rfl
private theorem qm7 (hB : Nf0 B) {p q r : V}
    (hpq : B.Adj p q) (hpr : B.Adj p r) (hqr : B.Adj q r)
    {hp : p∈(({q,r} : Finset V) : Set V)ᶜ}
    (hpaths : Adm0 (cs0 B ({q,r} : Finset V)) none (some ⟨p,hp⟩) 4) :
    False:=by
  obtain ⟨a,d,ha,hd,hpaths⟩:=hpaths
  have hbad (i : Fin 4) : (¬ 5∣a+i.val*d+1)∧(¬ 5∣a+i.val*d+2):=by
    obtain ⟨w,hw,hlen⟩:=hpaths i
    obtain ⟨e,he,w',hw',hlen',htail⟩:=qv9 hw
    simp only [Finset.mem_insert,Finset.mem_singleton] at he
    rw [hlen] at hlen'
    have hav : ∀ b∈({q,r} : Finset V),b≠e→ b∉w'.support:=by
      intro b hb hbe hbw
      rw [← Walk.cons_tail_support w',List.mem_cons] at hbw
      exact htail b (hbw.resolve_left hbe) hb
    rcases he with rfl|rfl
    · simpa only [hlen'] using qs1 hB hpq.symm hqr hpr.symm hw' (by omega)
        (hav r (by simp) hqr.ne.symm)
    · simpa only [hlen'] using qs1 hB hpr.symm hqr.symm hpq.symm hw' (by omega)
        (hav q (by simp) hqr.ne)
  have h0:=hbad 0
  have h1:=hbad 1
  have h2:=hbad 2
  have h3:=hbad 3
  rcases hd with rfl|rfl <;> norm_num at h0 h1 h2 h3 <;> omega
end Host
theorem qan2 (coy : COY4) {V : Type} [Fintype V] [DecidableEq V]
    {B : SimpleGraph V} [DecidableRel B.Adj] (hB : Nf0 B) (h : H40 B) :
    3∉(B.induce (h.U : Set V)).cycleLengths:=by
  classical
  intro hcycle
  let J:=B.induce (h.U : Set V)
  obtain ⟨s,hs⟩:=(is3Clique_iff_exists_cycle_length_three (G:=J)).mpr hcycle
  obtain ⟨p,q,r,hpq,hpr,hqr,-⟩:=is3Clique_iff.mp hs
  let S : Finset (h.U : Set V):={q,r}
  let Q:=((S : Set (h.U : Set V))ᶜ : Set (h.U : Set V))
  let p' : Q:=⟨p,by
    change p∉S
    simp [S,hpq.ne,hpr.ne]⟩
  let K:=cs0 J S
  let H:=de0 K (some p') none
  let : DecidableRel K.Adj:=by unfold K cs0;infer_instance
  let : DecidableRel H.Adj:=by unfold H de0;infer_instance
  have hS : S.card=2:=by simp [S,hqr.ne]
  have hQ2 : Kc0 (J.induce ((S : Set (h.U : Set V))ᶜ)) 2 :=
    qh5 (k:=2) (r:=2) S (by omega) h.hconn4
  have hK2 : Kc0 K 2 :=
    qy7 (qy6 (by decide) h.hconn4) ⟨q,by simp [S]⟩
      (qy6 (by decide) hQ2)
  have hr : Rt0 H (some p') none :=
    rooted_delEdge_iff.mpr ⟨by simp,hK2.1,fun U hU =>
      (hK2.2 U hU).mono (fun _ _ hab=>Or.inl hab)⟩
  have hcard : 4≤ Fintype.card (Option Q):=by
    have hc : 2 < Fintype.card Q:=hQ2.1
    rw [Fintype.card_option]
    omega
  have hdeg (v : Q) (hv : v≠p') : H.degree (some v)=J.degree v.1:=by
    have hadj (o : Option Q) : H.Adj (some v) o↔K.Adj (some v) o:=by
      simp [H,de0,edge_adj,hv]
    have hsame : H.neighborFinset (some v)=K.neighborFinset (some v):=by
      ext o
      simpa only [mem_neighborFinset] using hadj o
    rw [← card_neighborFinset_eq_degree,hsame,card_neighborFinset_eq_degree]
    apply qad3
    intro a ha b hb hva hvb
    have hne : p.val≠v.1.val:=fun he=>hv (Subtype.ext (Subtype.ext he.symm))
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at ha hb
    rcases ha with rfl|rfl <;> rcases hb with rfl|rfl
    · rfl
    · exact (qaf5 coy hB h p.2 a.2 b.2 v.1.2 hne hpq hpr hqr hva.symm hvb.symm).elim
    · exact (qaf5 coy hB h p.2 b.2 a.2 v.1.2 hne hpq hpr hqr hvb.symm hva.symm).elim
    · rfl
  let Z : Finset (Option Q):=Finset.univ.filter fun o =>
    o.elim False fun v=>v≠p'∧v.1∈h.D
  have hZ (v : Q) : some v∈Z↔v≠p'∧v.1∈h.D:=by simp [Z]
  have hnZ : none∉Z:=by simp [Z]
  obtain ⟨hbase,hrestored⟩:=qak1 coy hr hcard (q:=4) (by decide) (by decide)
    (fun hmem=>(hZ p').mp hmem |>.1 rfl) hnZ
    (by
      rintro (_|v) hv hn
      · exact (hn rfl).elim
      · rw [hdeg v (fun he=>hv (congrArg some he))]
        exact h.hdeg4 v.1)
    (by
      rintro (_|v) hv hn hz
      · exact (hn rfl).elim
      · have hv' : v≠p':=fun he=>hv (congrArg some he)
        rw [hdeg v hv']
        exact h.hdeg5_off_D v.1 fun hD=>hz ((hZ v).mpr ⟨hv',hD⟩))
  let T : Finset V:={q.val,r.val}
  let L:=cs0 B T
  let g (v : Q) : ((T : Set V)ᶜ : Set V):=⟨v.1.val,by
    have hn : v.1∉S:=v.2
    change v.1.val∉T
    simpa only [S,T,Finset.mem_insert,Finset.mem_singleton,Subtype.ext_iff] using hn⟩
  have hg : Function.Injective g:=by
    intro a b he
    have he':=congrArg Subtype.val he
    change a.1.val=b.1.val at he'
    exact Subtype.ext (Subtype.ext he')
  have hattach (v : Q) (hv : ∃ a∈S,J.Adj v.1 a) : L.Adj none (some (g v)):=by
    obtain ⟨a,ha,hadj⟩:=hv
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,a.val,?_,hadj⟩
    simp only [S,Finset.mem_insert,Finset.mem_singleton] at ha
    rcases ha with rfl|rfl <;> simp [T]
  let f : H →g L:=⟨Option.map g,fun {a b} hab=>by
    have hk : K.Adj a b:=hab.1
    rcases a with _|a <;> rcases b with _|b
    · exact hk
    · exact hattach b (Finset.mem_filter.mp hk).2
    · exact (hattach a (Finset.mem_filter.mp hk).2).symm
    · exact hk⟩
  have hf : Function.Injective f:=by
    rintro (_|a) (_|b) he
    · rfl
    · cases he
    · cases he
    · exact congrArg some (hg (Option.some.inj he))
  apply qm7 hB (show B.Adj p.val q.val from hpq)
    (show B.Adj p.val r.val from hpr) (show B.Adj q.val r.val from hqr)
    (hp:=(g p').2)
  apply qg1
  by_cases hz : Z.card≤ 1
  · exact qj2 f hf (hbase hz)
  have hbig : 2≤ Z.card:=by omega
  obtain ⟨o,ho⟩:=Finset.card_pos.mp (by omega : 0 < Z.card)
  have hex : ∃ cv,h.c=some cv:=by
    rcases o with _|v
    · exact (hnZ ho).elim
    · obtain ⟨cv,hc,-⟩:=h.hD_adj v.1 ((hZ v).mp ho).2
      exact ⟨cv,hc⟩
  obtain ⟨cv,hc⟩:=hex
  have hcv:=h.hc_not_mem cv hc
  let c' : ((T : Set V)ᶜ : Set V):=⟨cv,by
    change cv∉T
    intro hmem
    simp only [T,Finset.mem_insert,Finset.mem_singleton] at hmem
    rcases hmem with rfl|rfl
    · exact hcv q.2
    · exact hcv r.2⟩
  have hcAdj (o : Option Q) (ho : o∈Z) : L.Adj (some c') (f o):=by
    rcases o with _|v
    · exact (hnZ ho).elim
    · obtain ⟨cv',hc',hadj⟩:=h.hD_adj v.1 ((hZ v).mp ho).2
      obtain rfl:=Option.some.inj (hc'.symm.trans hc)
      exact hadj
  let F : av0 H Z →g L:=⟨fun o=>o.elim (some c') f,fun {a b} hab=>by
    rcases a with _|a <;> rcases b with _|b
    · exact (adjoin_not_adj_none hab).elim
    · exact hcAdj b hab
    · exact (hcAdj a hab).symm
    · exact f.map_adj hab⟩
  have hcf (o : Option Q) : some c'≠f o:=by
    rcases o with _|v
    · simp [f]
    · intro he
      have he':=congrArg Subtype.val (Option.some.inj he)
      change cv=v.1.val at he'
      exact hcv (he' ▸ v.1.2)
  have hF : Function.Injective F:=by
    rintro (_|a) (_|b) he
    · rfl
    · exact (hcf b he).elim
    · exact (hcf a he.symm).elim
    · exact congrArg some (hf he)
  exact qj2 F hF (hrestored hbig)
end DeanK5
end M4
section M5
namespace DeanK5
open SimpleGraph
private def Cross {X : Type} (G : SimpleGraph X) (S T : Finset X) : Prop :=
  ∀ a∈S,∀ b∈T,G.Adj a b
private def Missing {X : Type} (G : SimpleGraph X) (S T : Finset X) (x y : X) : Prop :=
  x∈S∧y∈T∧∀ a∈S,∀ b∈T,G.Adj a b↔a≠x∨b≠y
private theorem Cross.flip {X : Type} {G : SimpleGraph X} {S T : Finset X}
    (h : Cross G S T) : Cross G T S :=
  fun b hb a ha=>(h a ha b hb).symm
private theorem Missing.flip {X : Type} {G : SimpleGraph X} {S T : Finset X} {x y : X}
    (h : Missing G S T x y) : Missing G T S y x :=
  ⟨h.2.1,h.1,fun b hb a ha=>(G.adj_comm b a).trans ((h.2.2 a ha b hb).trans or_comm)⟩
private def Route {X : Type} [DecidableEq X] (G : SimpleGraph X) (F : Finset X)
    (a b : X) (n : ℕ) : Prop :=
  ∃ p : G.Walk a b,p.IsPath∧p.length=n∧∀ v∈p.support,v∈F
section Routes
variable {X : Type} [DecidableEq X] {G : SimpleGraph X} {F S T : Finset X}
private theorem Route.mono {K : Finset X} {a b : X} {n : ℕ}
    (h : Route G F a b n) (hK : F⊆K) : Route G K a b n:=by
  obtain ⟨p,hp,hl,hs⟩:=h
  exact ⟨p,hp,hl,fun v hv=>hK (hs v hv)⟩
private theorem Route.rev {a b : X} {n : ℕ} (h : Route G F a b n) : Route G F b a n:=by
  obtain ⟨p,hp,hl,hs⟩:=h
  exact ⟨p.reverse,hp.reverse,by simpa using hl,fun v hv=>hs v (by simpa using hv)⟩
private theorem Route.edge {a b : X} (ha : a∈F) (hb : b∈F) (e : G.Adj a b) :
    Route G F a b 1 :=
  ⟨e.toWalk,(Adj.isPath_toWalk e),rfl,by simp [Adj.toWalk,ha,hb]⟩
private theorem Route.prepend {a b c : X} {n : ℕ} (e : G.Adj a b) (ha : a∉F)
    (h : Route G F b c n) : Route G (insert a F) a c (n+1):=by
  obtain ⟨p,hp,rfl,hs⟩:=h
  refine ⟨Walk.cons e p,(qf0 e hp (fun hv=>ha (hs _ hv))).1,rfl,?_⟩
  intro v hv
  simp only [Walk.support_cons,List.mem_cons] at hv
  exact Finset.mem_insert.mpr (hv.imp_right (hs v))
private theorem qal3 {a t u b : X} {n : ℕ} (hd : Disjoint S T)
    (ha : a∈S) (ht : t∈T) (e : G.Adj a t) (f : G.Adj t u)
    (h : Route G (S.erase a∪T.erase t) u b n) : Route G (S∪T) a b (n+2):=by
  have htS : t∉S:=fun hm=>Finset.disjoint_left.mp hd hm ht
  have haT : a∉T:=fun hm=>Finset.disjoint_left.mp hd ha hm
  have hta : a≠t:=fun e=>haT (e ▸ ht)
  have h':=(h.prepend f (by simp [htS])).prepend e (by simp [hta,haT])
  exact h'.mono (by simp [ha,ht,Finset.insert_subset_iff,Finset.union_subset_iff,
    (Finset.erase_subset a S).trans Finset.subset_union_left,
    (Finset.erase_subset t T).trans Finset.subset_union_right])
private theorem ql0 (i : ℕ) {a b : X} (hd : Disjoint S T) (hc : Cross G S T)
    (ha : a∈S) (hb : b∈T) (hs : i+1≤ S.card) (ht : i+1≤ T.card) :
    Route G (S∪T) a b (2*i+1):=by
  induction i generalizing S T a b with
  | zero=>exact Route.edge (Finset.mem_union_left _ ha) (Finset.mem_union_right _ hb) (hc a ha b hb)
  | succ i ih =>
    obtain ⟨u,hu,hua⟩:=Finset.exists_mem_ne (by omega : 1 < S.card) a
    obtain ⟨t,ht',htb⟩:=Finset.exists_mem_ne (by omega : 1 < T.card) b
    have h:=ih (hd.mono (Finset.erase_subset _ _) (Finset.erase_subset _ _))
      (fun v hv w hw=>hc v (Finset.mem_of_mem_erase hv) w (Finset.mem_of_mem_erase hw))
      (Finset.mem_erase.mpr ⟨hua,hu⟩) (Finset.mem_erase.mpr ⟨Ne.symm htb,hb⟩)
      (by rw [Finset.card_erase_of_mem ha];omega) (by rw [Finset.card_erase_of_mem ht'];omega)
    convert qal3 hd ha ht' (hc a ha t ht') (hc u hu t ht').symm h using 1
    omega
private theorem qq7 (i : ℕ) {a b : X} (hd : Disjoint S T) (hc : Cross G S T)
    (ha : a∈S) (hb : b∈S) (hab : a≠b) (hs : i+2≤ S.card) (ht : i+1≤ T.card) :
    Route G (S∪T) a b (2*i+2):=by
  obtain ⟨t,ht'⟩:=Finset.card_pos.mp (by omega : 0 < T.card)
  have h:=ql0 i (hd.mono_left (Finset.erase_subset a S))
    (fun v hv w hw=>hc v (Finset.mem_of_mem_erase hv) w hw)
    (Finset.mem_erase.mpr ⟨hab.symm,hb⟩) ht' (by rw [Finset.card_erase_of_mem ha];omega) ht
  have h':=h.rev.prepend (hc a ha t ht') (by simp [fun hv=>Finset.disjoint_left.mp hd ha hv])
  exact h'.mono (by simp [ha,Finset.insert_subset_iff,Finset.union_subset_iff,
    (Finset.erase_subset a S).trans Finset.subset_union_left])
private theorem qz2 (i : ℕ) {a b y : X} (hd : Disjoint S T)
    (hm : Missing G S T a y) (hb : b∈T)
    (hs : i+2≤ S.card) (ht : i+2≤ T.card) (ht3 : 3≤ T.card) :
    Route G (S∪T) a b (2*(i+1)+1):=by
  obtain ⟨ha,hy,hc⟩:=hm
  obtain ⟨t,hte,hty⟩:=Finset.exists_mem_ne
    (by rw [Finset.card_erase_of_mem hb];omega : 1 < (T.erase b).card) y
  obtain ⟨htb,ht'⟩:=Finset.mem_erase.mp hte
  obtain ⟨u,hu,hua⟩:=Finset.exists_mem_ne (by omega : 1 < S.card) a
  have h:=ql0 i (hd.mono (Finset.erase_subset a S) (Finset.erase_subset t T))
    (fun v hv w hw=>(hc v (Finset.mem_of_mem_erase hv) w (Finset.mem_of_mem_erase hw)).mpr
      (Or.inl (Finset.ne_of_mem_erase hv))) (Finset.mem_erase.mpr ⟨hua,hu⟩)
    (Finset.mem_erase.mpr ⟨htb.symm,hb⟩)
    (by rw [Finset.card_erase_of_mem ha];omega) (by rw [Finset.card_erase_of_mem ht'];omega)
  convert qal3 hd ha ht' ((hc a ha t ht').mpr (Or.inr hty))
    ((hc u hu t ht').mpr (Or.inl hua)).symm h using 1
  omega
private theorem qaf3 (i : ℕ) {a b x y : X} (hd : Disjoint S T)
    (hm : Missing G S T x y) (ha : a∈S) (hb : b∈T) (e : G.Adj a b)
    (hs : i+1≤ S.card) (ht : i+1≤ T.card) (hs3 : 3≤ S.card) (ht3 : 3≤ T.card) :
    Route G (S∪T) a b (2*i+1):=by
  cases i with
  | zero=>exact Route.edge (Finset.mem_union_left _ ha) (Finset.mem_union_right _ hb) e
  | succ i =>
    by_cases hax : a=x
    · subst x
      exact qz2 i hd hm hb hs ht ht3
    by_cases hby : b=y
    · subst y
      have h:=qz2 i hd.symm hm.flip ha ht hs hs3
      simpa only [Finset.union_comm T S] using h.rev
    obtain ⟨hx,hy,hc⟩:=hm
    cases i with
    | zero =>
      have h:=ql0 1 (hd.mono_left (Finset.erase_subset x S))
        (fun v hv w hw=>(hc v (Finset.mem_of_mem_erase hv) w hw).mpr
          (Or.inl (Finset.ne_of_mem_erase hv))) (Finset.mem_erase.mpr ⟨hax,ha⟩) hb
        (by rw [Finset.card_erase_of_mem hx];omega) ht
      exact h.mono (Finset.union_subset_union (Finset.erase_subset _ _) Finset.Subset.rfl)
    | succ j =>
      let L:=S.erase a
      let R:=(T.erase b).erase y
      have hLS : L⊆S:=Finset.erase_subset _ _
      have hRT : R⊆T:=(Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
      obtain ⟨u,hu,hux⟩:=Finset.exists_mem_ne
        (by dsimp [L];rw [Finset.card_erase_of_mem ha];omega : 1 < L.card) x
      have hxL : x∈L:=Finset.mem_erase.mpr ⟨Ne.symm hax,hx⟩
      have h:=qq7 j (hd.mono hLS hRT)
        (fun v hv w hw=>(hc v (hLS hv) w (hRT hw)).mpr (Or.inr (Finset.ne_of_mem_erase hw)))
        hu hxL hux (by dsimp [L];rw [Finset.card_erase_of_mem ha];omega)
        (by dsimp [R];rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨Ne.symm hby,hy⟩),
          Finset.card_erase_of_mem hb];omega)
      have hyL : y∉L:=fun hv=>Finset.disjoint_left.mp hd (hLS hv) hy
      have haT : a∉T:=fun hv=>Finset.disjoint_left.mp hd ha hv
      have hbS : b∉S:=fun hv=>Finset.disjoint_left.mp hd hv hb
      have hay : a≠y:=fun he=>haT (he ▸ hy)
      have h':=(h.prepend ((hc u (hLS hu) y hy).mpr (Or.inl hux)).symm
        (by simp [hyL,R])).prepend ((hc a ha y hy).mpr (Or.inl hax))
        (by have hn : a∉R:=fun hv=>haT (hRT hv);simp [hay,L,hn])
      have h'':=h'.rev.prepend ((hc x hx b hb).mpr (Or.inr hby)).symm
        (by have hn : b∉L:=fun hv=>hbS (hLS hv)
            simp [hby,Ne.symm (show a≠b from fun he=>haT (he ▸ hb)),hn,R])
      convert h''.rev.mono (K:=S∪T) ?_ using 1
      · omega
      · simp [Finset.insert_subset_iff,Finset.union_subset_iff,ha,hb,hy,
          hLS.trans Finset.subset_union_left,hRT.trans Finset.subset_union_right]
end Routes
section Cores
variable {X : Type} [DecidableEq X] {G : SimpleGraph X} {S T : Finset X}
private def HasK (G : SimpleGraph X) (s t : ℕ) : Prop :=
  ∃ S T : Finset X,S.card=s∧T.card=t∧Disjoint S T∧Cross G S T
private def qae2 (G : SimpleGraph X) (r : ℕ) : Prop :=
  ∃ S T : Finset X,S.card=r∧T.card=r∧Disjoint S T ∧
    ∃ x y,Missing G S T x y
private theorem qag3 (h3 : 3∉G.cycleLengths) {a b c : X}
    (e : G.Adj a b) (f : G.Adj b c) (g : G.Adj c a) : False:=by
  have h:=(Route.edge (F:={c,b}) (by simp) (by simp) f.symm).prepend g.symm
    (by simp [e.ne,g.ne.symm])
  obtain ⟨p,hp,hl,-⟩:=h
  exact h3 (by simpa [hl] using (qn1 hp (Adj.isPath_toWalk e)
    (fun v _ hv=>by simpa [Adj.toWalk] using hv) (by simp [hl,Adj.toWalk])).2)
private theorem qae5 (h4 : 4∈G.cycleLengths) : HasK G 2 2:=by
  obtain ⟨a,p,hp,hl⟩:=h4
  cases p with
  | nil=>simp at hl
  | @cons _ b _ e p =>
    have hp':=(Walk.cons_isCycle_iff p e).mp hp |>.1
    cases p with
    | nil=>simp at hl
    | @cons _ c _ f p =>
      cases p with
      | nil=>simp at hl
      | @cons _ d _ g p =>
        cases p with
        | nil=>simp at hl
        | @cons _ z _ k p =>
          have hnil : p.Nil:=Walk.length_eq_zero_iff.mp (by simp only [Walk.length_cons] at hl;omega)
          cases hnil
          have hn:=hp'.support_nodup
          simp only [Walk.support_cons,Walk.support_nil,List.nodup_cons,List.mem_cons,
            List.not_mem_nil,or_false,not_false_eq_true,
            List.nodup_nil,and_true] at hn
          obtain ⟨hb,hc,hd⟩:=hn
          have hac : a≠c:=fun h=>hc (Or.inr h.symm)
          have hbd : b≠d:=fun h=>hb (Or.inr (Or.inl h))
          refine ⟨{a,c},{b,d},by simp [hac],by simp [hbd],?_,?_⟩
          · simp [Finset.disjoint_left,e.ne,k.ne.symm,f.ne.symm,g.ne]
          · intro u hu v hv
            simp only [Finset.mem_insert,Finset.mem_singleton] at hu hv
            rcases hu with rfl|rfl <;> rcases hv with rfl|rfl
            exacts [e,k.symm,f.symm,g]
private theorem qw5 (hG : Nf0 G) {a b : X} (e : G.Adj a b)
    (h : Route G (S∪T) a b 9) : False:=by
  obtain ⟨p,hp,hl,-⟩:=h
  apply qc4 hG hp (Adj.isPath_toWalk e)
    (fun v _ hv=>by simpa [Adj.toWalk] using hv) (by simp [hl,Adj.toWalk])
  simp [hl,Adj.toWalk]
private theorem qah7 (hG : Nf0 G) {s : ℕ} (h : HasK G s s) : s≤ 4:=by
  by_contra! hlt
  obtain ⟨S,T,hs,ht,hd,hc⟩:=h
  obtain ⟨a,ha⟩:=Finset.card_pos.mp (by omega : 0 < S.card)
  obtain ⟨b,hb⟩:=Finset.card_pos.mp (by omega : 0 < T.card)
  exact qw5 hG (hc a ha b hb) (ql0 4 hd hc ha hb (by omega) (by omega))
private theorem qai6 (hG : Nf0 G) {r : ℕ} (h : qae2 G r) : r≤ 4:=by
  by_contra! hlt
  obtain ⟨S,T,hs,ht,hd,x,y,hm⟩:=h
  obtain ⟨b,hb,hby⟩:=Finset.exists_mem_ne (by omega : 1 < T.card) y
  have e:=(hm.2.2 x hm.1 b hb).mpr (Or.inr hby)
  exact qw5 hG e
    (qaf3 4 hd hm hm.1 hb e (by omega) (by omega) (by omega) (by omega))
variable [DecidableRel G.Adj]
private structure SquareCore (G : SimpleGraph X) [DecidableRel G.Adj]
    (r : ℕ) (S T : Finset X) : Prop where
  lower : 2≤ r
  upper : r≤ 4
  left_card : r≤ S.card
  right_card : r≤ T.card
  disj : Disjoint S T
  shape : (Cross G S T∧(S.card=r∨T.card=r)) ∨
    ∃ x y,Missing G S T x y∧S.card=r∧T.card=r∧3≤ r
  exterior : ∀ v∉S∪T,((S∪T).filter (G.Adj v)).card≤ r - 1
private theorem SquareCore.flip {r : ℕ} (h : SquareCore G r S T) : SquareCore G r T S where
  lower:=h.lower
  upper:=h.upper
  left_card:=h.right_card
  right_card:=h.left_card
  disj:=h.disj.symm
  shape:=h.shape.elim (fun ⟨hc,hs⟩=>Or.inl ⟨hc.flip,hs.symm⟩)
    (fun ⟨x,y,hm,hs,ht,hr⟩=>Or.inr ⟨y,x,hm.flip,ht,hs,hr⟩)
  exterior:=by simpa only [Finset.union_comm T S] using h.exterior
omit [DecidableEq X] in
private theorem qam5 (v : X) (h : S.card≤ (S.filter (G.Adj v)).card) :
    ∀ a∈S,G.Adj v a:=by
  have he:=Finset.eq_of_subset_of_card_le (Finset.filter_subset (G.Adj v) S) h
  intro a ha
  exact (Finset.mem_filter.mp (he.symm ▸ ha)).2
private theorem qab8 (h3 : 3∉G.cycleLengths) {r : ℕ} {x y v : X}
    (hs : S.card=r) (ht : T.card=r) (hr : 3≤ r) (hd : Disjoint S T)
    (hm : Missing G S T x y) (hv : v∉S∪T) (hmax : ¬ HasK G r r) :
    ((S∪T).filter (G.Adj v)).card≤ r - 1:=by
  classical
  obtain ⟨hx,hy,hc⟩:=hm
  have hvS : v∉S:=fun h=>hv (Finset.mem_union_left _ h)
  have hvT : v∉T:=fun h=>hv (Finset.mem_union_right _ h)
  have hleft : (S.filter (G.Adj v)).card < r:=by
    by_contra! hl
    have hAll:=qam5 v (hs ▸ hl)
    apply hmax
    refine ⟨S,insert v (T.erase y),hs,?_,?_,?_⟩
    · rw [Finset.card_insert_of_notMem (fun h=>hvT (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem hy,ht]
      omega
    · exact Finset.disjoint_insert_right.mpr ⟨hvS,hd.mono_right (Finset.erase_subset _ _)⟩
    · intro a ha b hb
      rcases Finset.mem_insert.mp hb with rfl|hb
      · exact (hAll a ha).symm
      · exact (hc a ha b (Finset.mem_of_mem_erase hb)).mpr (Or.inr (Finset.ne_of_mem_erase hb))
  have hright : (T.filter (G.Adj v)).card < r:=by
    by_contra! hl
    have hAll:=qam5 v (ht ▸ hl)
    apply hmax
    refine ⟨insert v (S.erase x),T,?_,ht,?_,?_⟩
    · rw [Finset.card_insert_of_notMem (fun h=>hvS (Finset.mem_of_mem_erase h)),
        Finset.card_erase_of_mem hx,hs]
      omega
    · exact Finset.disjoint_insert_left.mpr ⟨hvT,hd.mono_left (Finset.erase_subset _ _)⟩
    · intro a ha b hb
      rcases Finset.mem_insert.mp ha with rfl|ha
      · exact hAll b hb
      · exact (hc a (Finset.mem_of_mem_erase ha) b hb).mpr (Or.inl (Finset.ne_of_mem_erase ha))
  by_cases hL : (S.filter (G.Adj v)).Nonempty
  · by_cases hR : (T.filter (G.Adj v)).Nonempty
    · obtain ⟨a,ha⟩:=hL
      obtain ⟨b,hb⟩:=hR
      obtain ⟨ha,hva⟩:=Finset.mem_filter.mp ha
      obtain ⟨hb,hvb⟩:=Finset.mem_filter.mp hb
      have hsub : (S∪T).filter (G.Adj v)⊆{x,y}:=by
        intro w hw
        obtain ⟨hw,hvw⟩:=Finset.mem_filter.mp hw
        rcases Finset.mem_union.mp hw with hws|hwt
        · by_cases h : w=x
          · simp [h]
          · exact (qag3 h3 hvw ((hc w hws b hb).mpr (Or.inl h)) hvb.symm).elim
        · by_cases h : w=y
          · simp [h]
          · exact (qag3 h3 hva ((hc a ha w hwt).mpr (Or.inr h)) hvw.symm).elim
      have:=(Finset.card_le_card hsub).trans Finset.card_le_two
      omega
    · rw [Finset.filter_union,Finset.not_nonempty_iff_eq_empty.mp hR,Finset.union_empty]
      omega
  · rw [Finset.filter_union,Finset.not_nonempty_iff_eq_empty.mp hL,Finset.empty_union]
    omega
private theorem qaa8 (h3 : 3∉G.cycleLengths) {s t : ℕ} {v : X}
    (hs : S.card=s) (ht : T.card=t) (hst : s≤ t)
    (hd : Disjoint S T) (hc : Cross G S T) (hv : v∉S∪T)
    (hmax : ∀ n,HasK G s n→ n≤ t) (hnext : ¬ HasK G (s+1) (s+1))
    (hmiss : ¬ qae2 G (s+1)) : ((S∪T).filter (G.Adj v)).card≤ s - 1:=by
  classical
  have hvS : v∉S:=fun h=>hv (Finset.mem_union_left _ h)
  have hvT : v∉T:=fun h=>hv (Finset.mem_union_right _ h)
  have hleft : (S.filter (G.Adj v)).card < s:=by
    by_contra! hl
    have he:=qam5 v (hs ▸ hl)
    have hK : HasK G s (t+1):=⟨S,insert v T,hs,by
      rw [Finset.card_insert_of_notMem hvT,ht],Finset.disjoint_insert_right.mpr ⟨hvS,hd⟩,
      fun a ha b hb=>(Finset.mem_insert.mp hb).elim (fun h=>h ▸ (he a ha).symm)
        (hc a ha b)⟩
    have:=hmax _ hK
    omega
  have hright : (T.filter (G.Adj v)).card < s:=by
    by_contra! hl
    by_cases heq : t=s
    · have he:=qam5 v (by omega : T.card≤ (T.filter (G.Adj v)).card)
      have hK : HasK G s (t+1):=⟨T,insert v S,ht.trans heq,by
        rw [Finset.card_insert_of_notMem hvS,hs,heq],Finset.disjoint_insert_right.mpr
        ⟨hvT,hd.symm⟩,fun a ha b hb=>(Finset.mem_insert.mp hb).elim
          (fun h=>h ▸ (he a ha).symm) (hc.flip a ha b)⟩
      have:=hmax _ hK
      omega
    · obtain ⟨R,hR,hRc⟩:=Finset.exists_subset_card_eq hl
      have hRT:=hR.trans (Finset.filter_subset (G.Adj v) T)
      obtain ⟨y,hy,hyR⟩:=Finset.exists_mem_notMem_of_card_lt_card
        (by omega : R.card < T.card)
      have hsub : insert y R⊆T:=Finset.insert_subset hy hRT
      have hd':=Finset.disjoint_insert_left.mpr ⟨fun h=>hvT (hsub h),hd.mono_right hsub⟩
      have hSc : (insert v S).card=s+1:=by rw [Finset.card_insert_of_notMem hvS,hs]
      have hTc : (insert y R).card=s+1:=by rw [Finset.card_insert_of_notMem hyR,hRc]
      have hAdj : ∀ a∈insert v S,∀ b∈insert y R,a≠v∨b≠y→ G.Adj a b:=by
        intro a ha b hb hab
        rcases Finset.mem_insert.mp ha with rfl|ha
        · have hbR:=(Finset.mem_insert.mp hb).resolve_left (hab.resolve_left (by simp))
          exact (Finset.mem_filter.mp (hR hbR)).2
        · exact hc a ha b (hsub hb)
      by_cases hvy : G.Adj v y
      · apply hnext
        refine ⟨_,_,hSc,hTc,hd',fun a ha b hb=>?_⟩
        by_cases hab : a≠v∨b≠y
        · exact hAdj a ha b hb hab
        · push Not at hab
          simpa [hab.1,hab.2] using hvy
      · apply hmiss
        refine ⟨_,_,hSc,hTc,hd',v,y,by simp,by simp,fun a ha b hb=>⟨?_,hAdj a ha b hb⟩⟩
        intro e
        by_contra hab
        push Not at hab
        exact hvy (by simpa [hab.1,hab.2] using e)
  by_cases hL : (S.filter (G.Adj v)).Nonempty
  · obtain ⟨a,ha⟩:=hL
    obtain ⟨ha,hva⟩:=Finset.mem_filter.mp ha
    have hR : T.filter (G.Adj v)=∅:=Finset.eq_empty_of_forall_notMem fun b hb=>by
      obtain ⟨hb,hvb⟩:=Finset.mem_filter.mp hb
      exact qag3 h3 hva (hc a ha b hb) hvb.symm
    rw [Finset.filter_union,hR,Finset.union_empty]
    omega
  · rw [Finset.filter_union,Finset.not_nonempty_iff_eq_empty.mp hL,Finset.empty_union]
    omega
private theorem qam8 [Fintype X] (hG : Nf0 G) (h3 : 3∉G.cycleLengths)
    (h4 : 4∈G.cycleLengths) : ∃ r S T,SquareCore G r S T:=by
  classical
  let s:=Nat.findGreatest (fun n=>HasK G n n) 4
  have h22:=qae5 h4
  have hs2 : 2≤ s:=Nat.le_findGreatest (by decide) h22
  have hs4 : s≤ 4:=Nat.findGreatest_le _
  have hss : HasK G s s:=Nat.findGreatest_spec (P:=fun n=>HasK G n n) (by decide : 2≤ 4) h22
  have hnext : ¬ HasK G (s+1) (s+1):=fun hk=>by
    have : s+1≤ s:=Nat.le_findGreatest (qah7 hG hk) hk
    omega
  by_cases hm : qae2 G (s+1)
  · have h4':=qai6 hG hm
    obtain ⟨S,T,hs,ht,hd,x,y,hxy⟩:=hm
    exact ⟨s+1,S,T,by
      refine ⟨by omega,h4',by omega,by omega,hd,Or.inr ⟨x,y,hxy,hs,ht,by omega⟩,?_⟩
      exact fun v hv=>qab8 h3 hs ht (by omega) hd hxy hv hnext⟩
  · let t:=Nat.findGreatest (HasK G s) (Fintype.card X)
    have hb : ∀ n,HasK G s n→ n≤ Fintype.card X:=by
      rintro n ⟨_,T,-,rfl,-,-⟩
      exact Finset.card_le_univ T
    have hst : s≤ t:=Nat.le_findGreatest (hb s hss) hss
    have hmax : ∀ n,HasK G s n→ n≤ t:=fun n hk=>Nat.le_findGreatest (hb n hk) hk
    have hstK : HasK G s t:=Nat.findGreatest_spec (hb s hss) hss
    obtain ⟨S,T,hs,ht,hd,hc⟩:=hstK
    exact ⟨s,S,T,by
      refine ⟨hs2,hs4,by omega,by omega,hd,Or.inl ⟨hc,Or.inl hs⟩,?_⟩
      exact fun v hv=>qaa8 h3 hs ht hst hd hc hv hmax hnext hm⟩
end Cores
section Components
variable {X : Type} [Fintype X] [DecidableEq X] {G : SimpleGraph X} [DecidableRel G.Adj]
variable {S T F Q : Finset X}
omit [Fintype X] [DecidableRel G.Adj] in
private theorem ql1 (h3 : 3∉G.cycleLengths) (hc : Cross G S T)
    (ht : T.Nonempty) {a b : X} (ha : a∈S) (hb : b∈S) : ¬ G.Adj a b:=by
  obtain ⟨t,ht⟩:=ht
  exact fun e=>qag3 h3 e (hc b hb t ht) (hc a ha t ht).symm
private theorem qz7 (hspan : ∀ v,v∈S∪T) {b : X}
    (hS : ∀ a∈S,G.Adj b a) (hT : ∀ a∈T,¬ G.Adj b a) : G.degree b=S.card:=by
  rw [qb5]
  congr 1
  ext a
  simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  exact ⟨fun h=>(Finset.mem_union.mp (hspan a)).resolve_right (fun ha=>hT a ha h),hS a⟩
private theorem ql9 (h3 : 3∉G.cycleLengths)
    {D : Finset X} (hD : ∀ v,v∈D↔G.degree v=4) (hDc : D.card≤ 4)
    (hdeg : ∀ v,4≤ G.degree v) (hc : Cross G S T) (hd : Disjoint S T)
    (hs : 2≤ S.card) (ht : S.card≤ T.card) (hs4 : S.card≤ 4) :
    ∃ v,v∉S∪T:=by
  by_contra! hspan
  have hnS:=Finset.card_pos.mp (by omega : 0 < S.card)
  have hnT:=Finset.card_pos.mp (by omega : 0 < T.card)
  have heT : ∀ b∈T,G.degree b=S.card:=fun b hb=>qz7 hspan
    (fun a ha=>(hc a ha b hb).symm) (fun a ha=>ql1 h3 hc.flip hnS hb ha)
  obtain ⟨b,hb⟩:=hnT
  have hs4' : S.card=4:=by have:=hdeg b;have:=heT b hb;omega
  have htD : T⊆D:=fun v hv=>(hD v).mpr ((heT v hv).trans hs4')
  have:=Finset.card_le_card htD
  have ht4 : T.card=4:=by omega
  have hsD : S⊆D:=fun v hv=>(hD v).mpr
    ((qz7 (S:=T) (T:=S) (by simpa only [Finset.union_comm T S] using hspan)
      (hc v hv) (fun a ha=>ql1 h3 hc ⟨b,hb⟩ hv ha)).trans ht4)
  have hcd:=Finset.card_le_card (Finset.union_subset hsD htD)
  rw [Finset.card_union_of_disjoint hd] at hcd
  omega
private theorem qad1 (h3 : 3∉G.cycleLengths) {r : ℕ} (h : SquareCore G r S T)
    {D : Finset X} (hD : ∀ v,v∈D↔G.degree v=4) (hDc : D.card≤ 4)
    (hdeg : ∀ v,4≤ G.degree v) : ∃ v,v∉S∪T:=by
  classical
  rcases h.shape with ⟨hc,hs|ht⟩|⟨x,y,hm,hs,ht,hr⟩
  · exact ql9 h3 hD hDc hdeg hc h.disj (hs ▸ h.lower)
      (hs ▸ h.right_card) (hs ▸ h.upper)
  · simpa only [Finset.union_comm T S] using
      ql9 h3 hD hDc hdeg hc.flip h.disj.symm (ht ▸ h.lower)
        (ht ▸ h.left_card) (ht ▸ h.upper)
  · by_contra! hspan
    obtain ⟨hx,hy,hc⟩:=hm
    have hpart : Cross G S (T.erase y):=fun a ha b hb =>
      (hc a ha b (Finset.mem_of_mem_erase hb)).mpr (Or.inr (Finset.ne_of_mem_erase hb))
    have hne:=Finset.card_pos.mp
      (by rw [Finset.card_erase_of_mem hy,ht];omega : 0 < (T.erase y).card)
    have he : G.degree x=(T.erase y).card:=by
      rw [qb5]
      congr 1
      ext a
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase]
      refine ⟨fun e=>?_,fun ⟨hne',ha⟩=>(hc x hx a ha).mpr (Or.inr hne')⟩
      obtain ha|ha:=Finset.mem_union.mp (hspan a)
      · exact (ql1 h3 hpart hne hx ha e).elim
      · exact ⟨((hc x hx a ha).mp e).resolve_left (by simp),ha⟩
    rw [Finset.card_erase_of_mem hy,ht] at he
    have:=h.upper
    have:=hdeg x
    omega
private structure Exterior (G : SimpleGraph X) (F Q : Finset X) : Prop where
  disj : Disjoint Q F
  linked : Lk0 G Q
  closed : ∀ v∈Q,∀ w,G.Adj v w→ w∈Q∨w∈F
  card : 2≤ Q.card
private theorem qs6 {v : X} (hv : v∈Q) (hd : Disjoint Q F)
    (hc : ∀ v∈Q,∀ w,G.Adj v w→ w∈Q∨w∈F) :
    G.degree v=(Q.filter (G.Adj v)).card+(F.filter (G.Adj v)).card:=by
  rw [qb5,← Finset.card_union_of_disjoint
    (hd.mono (Finset.filter_subset (G.Adj v) Q) (Finset.filter_subset (G.Adj v) F))]
  congr 1
  ext w
  simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union]
  exact ⟨fun e=>(hc v hv w e).imp (fun h=>⟨h,e⟩) (fun h=>⟨h,e⟩),
    fun h=>h.elim And.right And.right⟩
private theorem qai5 {r : ℕ} (h : SquareCore G r S T) (hdeg : ∀ v,4≤ G.degree v)
    (he : ∃ v,v∉S∪T) : ∃ Q,Exterior G (S∪T) Q:=by
  classical
  obtain ⟨u,hu⟩:=he
  obtain ⟨Q,hQ,hreach,hl,hc⟩ :=
    qi7 (B:=G) ((S∪T)ᶜ) (u:=u) (Finset.mem_compl.mpr hu)
  have huQ:=(hreach u).mpr (Rc0.refl (Finset.mem_compl.mpr hu))
  have hd : Disjoint Q (S∪T):=Finset.disjoint_left.mpr fun _ ha hb =>
    Finset.mem_compl.mp (hQ ha) hb
  have hcl : ∀ v∈Q,∀ w,G.Adj v w→ w∈Q∨w∈S∪T:=by
    intro v hv w e
    by_cases hw : w∈S∪T
    · exact Or.inr hw
    · exact Or.inl (hc v hv w (Finset.mem_compl.mpr hw) e)
  refine ⟨Q,hd,hl,hcl,?_⟩
  have:=qs6 huQ hd hcl
  have:=qc3 (B:=G) huQ
  have:=hdeg u
  have:=h.exterior u hu
  have:=h.upper
  omega
private def qm1 (G : SimpleGraph X) [DecidableRel G.Adj] (F Q : Finset X) : Finset X :=
  F.filter fun a=>∃ v∈Q,G.Adj v a
private theorem qt3 (hG : Kc0 G 4) (h : Exterior G F Q) (hF : 4≤ F.card) :
    4≤ (qm1 G F Q).card:=by
  by_contra! hsmall
  let R:=qm1 G F Q
  change R.card < 4 at hsmall
  have hRF : R⊆F:=Finset.filter_subset _ _
  obtain ⟨a,ha,haR⟩:=Finset.exists_mem_notMem_of_card_lt_card
    (show R.card < F.card by omega)
  obtain ⟨v,hv⟩:=Finset.card_pos.mp (by have:=h.card;omega : 0 < Q.card)
  obtain ⟨w,hw,z,hz,hzQ,e⟩:=qf9 ((kConn_iff_linked.mp hG).2 R hsmall)
    (fun _ hb=>Finset.mem_compl.mpr fun hr=>Finset.disjoint_left.mp h.disj hb (hRF hr))
    hv (Finset.mem_compl.mpr haR) (fun haQ=>Finset.disjoint_left.mp h.disj haQ ha)
  have hzF:=(h.closed w hw z e).resolve_left hzQ
  exact Finset.mem_compl.mp hz (Finset.mem_filter.mpr ⟨hzF,w,hw,e⟩)
end Components
section BoundaryLift
variable {X W V : Type} {I : SimpleGraph W} {B : SimpleGraph V}
private theorem qaa0 (f : I →g B) (hf : Function.Injective f)
    {K : Set V} (hfK : ∀ w,f w∉K) {A₁ A₂ : Finset W}
    {j : X→ V} {P : X→ X→ Prop}
    (chooseEnds : ∀ u∈A₁,∀ v∈A₂,∃ a b,P a b ∧
      j a∈K∧j b∈K∧j a≠j b∧B.Adj (j a) (f u)∧B.Adj (f v) (j b))
    {p : (bg0 I A₁ A₂).Walk (Sum.inl 0) (Sum.inl 1)} (hp : p.IsPath) :
    ∃ a b,P a b∧∃ q : B.Walk (j a) (j b),q.IsPath∧q.length=p.length ∧
      ∀ z∈q.support,z∈K→ z=j a∨z=j b:=by
  obtain ⟨u,hu,v,hv,m,hm,hl,-⟩:=qe2 hp
  obtain ⟨a,b,habP,haK,hbK,hab,ea,eb⟩:=chooseEnds u hu v hv
  let n:=m.map f
  have hn:=qb8 f hf hm
  have houtside : ∀ z∈n.support,z∉K:=by
    intro z hz
    rw [Walk.support_map,List.mem_map] at hz
    obtain ⟨w,-,rfl⟩:=hz
    exact hfK w
  have hbn : j b∉n.support:=fun hz=>houtside (j b) hz hbK
  have han : j a∉(n.concat eb).support:=by
    simp only [Walk.support_concat,List.mem_append,List.mem_singleton,not_or]
    exact ⟨fun hz=>houtside (j a) hz haK,hab⟩
  refine ⟨a,b,habP,Walk.cons ea (n.concat eb),
    (qf0 ea (hn.concat hbn eb) han).1,?_,?_⟩
  · simp [n,hl]
  · intro z hz hzK
    simp only [Walk.support_cons,List.mem_cons,Walk.support_concat,List.mem_append,
      List.not_mem_nil,or_false] at hz
    exact hz.elim Or.inl fun hz=>hz.elim (fun hn=>(houtside z hn hzK).elim) Or.inr
private def qf6 (o : Option (Fin 2 ⊕ W)) : Fin 2 ⊕ Option W :=
  match o with
  | none=>Sum.inr none
  | some (Sum.inl i)=>Sum.inl i
  | some (Sum.inr w)=>Sum.inr (some w)
private theorem qp3 : Function.Injective (qf6 (W:=W)):=by
  rintro (_|a|a) (_|b|b) <;> simp [qf6]
private def qd4 : W ↪ Fin 2 ⊕ W:=⟨Sum.inr,Sum.inr_injective⟩
private def qk0 : W ↪ Option W:=⟨some,Option.some_injective W⟩
private def qab7 (I : SimpleGraph W) (A₁ A₂ Z : Finset W) :
    av0 (bg0 I A₁ A₂) (Z.map qd4) →g
      bg0 (av0 I Z) (A₁.map qk0) (A₂.map qk0) :=
  ⟨qf6,by
    rintro (_|i|u) (_|j|v) h
    · exact h
    · simp [qd4] at h
    · simpa [qf6,qd4] using h
    · simp [qd4] at h
    · exact h
    · rcases qa8 i with rfl|rfl <;> simpa [qf6,qk0] using h
    · simpa [qf6,qd4] using h
    · rcases qa8 j with rfl|rfl <;> simpa [qf6,qk0] using h
    · exact h⟩
end BoundaryLift
section Boundary
variable {X : Type} [Fintype X] [DecidableEq X] {G : SimpleGraph X} [DecidableRel G.Adj]
variable {F Q O : Finset X}
omit [DecidableRel G.Adj] in
private theorem qae6 (hG : Kc0 G 4) (h : Exterior G F Q) (hOF : O⊆F)
    (hO : O.card≤ 1) (hF : 4≤ F.card) {A₁ A₂ : Finset (Q : Set X)}
    (hA₁ : A₁.Nonempty) (hA₂ : A₂.Nonempty)
    (hrep : ∀ v : (Q : Set X),∀ a∈F,a∉O→ G.Adj v.val a→ v∈A₁∨v∈A₂) :
    Rt0 (bg0 (G.induce (Q : Set X)) A₁ A₂) (Sum.inl 0) (Sum.inl 1):=by
  classical
  refine qab3 (qd1 ⟨(hA₁.choose).val,(hA₁.choose).property⟩
    h.linked) hA₁ hA₂ ?_
  intro w C hC hne hcl
  let C':=C.image Subtype.val
  have hC' : C'⊆(insert w.val O)ᶜ:=by
    intro x hx
    obtain ⟨a,ha,rfl⟩:=Finset.mem_image.mp hx
    refine Finset.mem_compl.mpr (fun hs=>?_)
    rcases Finset.mem_insert.mp hs with he|hO'
    · exact Finset.ne_of_mem_erase (hC ha) (Subtype.ext he)
    · exact Finset.disjoint_left.mp h.disj a.property (hOF hO')
  obtain ⟨a,ha,haO⟩:=Finset.exists_mem_notMem_of_card_lt_card (by omega : O.card < F.card)
  have ha' : a∈(insert w.val O)ᶜ:=Finset.mem_compl.mpr (by
    simp [haO,show a≠w.val from fun he =>
      Finset.disjoint_left.mp h.disj w.property (he ▸ ha)])
  have haC : a∉C':=by
    intro ha'
    obtain ⟨u,-,rfl⟩:=Finset.mem_image.mp ha'
    exact Finset.disjoint_left.mp h.disj u.property ha
  have hsmall : (insert w.val O).card < 4:=by
    have:=Finset.card_insert_le w.val O
    omega
  obtain ⟨b,hb⟩:=hne
  have hb' : b.val∈C':=Finset.mem_image_of_mem _ hb
  obtain ⟨u,hu,v,hv,hvC,e⟩ :=
    qf9 ((kConn_iff_linked.mp hG).2 _ hsmall) hC' hb' ha' haC
  obtain ⟨c,hc,rfl⟩:=Finset.mem_image.mp hu
  rcases h.closed c.val c.property v e with hvQ|hvF
  · let d : (Q : Set X):=⟨v,hvQ⟩
    have hdw : d≠w:=fun he=>Finset.mem_compl.mp hv (Finset.mem_insert.mpr
      (Or.inl (congrArg Subtype.val he)))
    exact (hvC (Finset.mem_image_of_mem _ (hcl c hc d (by simp [hdw]) e))).elim
  · exact ⟨c,hc,hrep c v hvF (fun ho=>Finset.mem_compl.mp hv (Finset.mem_insert_of_mem ho)) e⟩
omit [Fintype X] in
private theorem qae7 {A₁ A₂ : Finset (Q : Set X)}
    [DecidableRel (bg0 (G.induce (Q : Set X)) A₁ A₂).Adj] (v : (Q : Set X)) :
    (bg0 (G.induce (Q : Set X)) A₁ A₂).degree (Sum.inr v) =
      (Q.filter (G.Adj v.val)).card+((if v∈A₁ then 1 else 0)+(if v∈A₂ then 1 else 0)):=by
  let I:=G.induce (Q : Set X)
  let R:=Finset.univ.filter fun i : Fin 2=>v∈qm8 A₁ A₂ i
  have he : (bg0 I A₁ A₂).neighborFinset (Sum.inr v) =
      R.disjSum (I.neighborFinset v):=by
    ext z
    rcases z with i|w <;> simp [R]
  rw [← card_neighborFinset_eq_degree,he,Finset.card_disjSum,card_neighborFinset_eq_degree,
    qa5]
  simp only [R,Finset.card_filter,Fin.sum_univ_two,rootSet_zero,rootSet_one]
  ac_rfl
end Boundary
section Host
variable {V : Type} [Fintype V] [DecidableEq V] {B : SimpleGraph V} [DecidableRel B.Adj]
variable (h : H40 B)
private abbrev U:=(h.U : Set V)
private abbrev J:=B.induce (h.U : Set V)
private def qaa1 (F : Finset (U h)) (P : (U h)→ (U h)→ Prop) (q : ℕ) : Prop :=
  ∃ m d : ℕ,2≤ m∧(d=1∨d=2)∧∀ i : Fin q,
    ∃ a b,P a b∧∃ p : B.Walk a.val b.val,p.IsPath∧p.length=m+i.val*d ∧
      ∀ z∈p.support,z∈Subtype.val '' (F : Set (U h))→ z=a.val∨z=b.val
private theorem qs5 (coy : COY4) {F Q O : Finset (U h)}
    (c : Exterior (J h) F Q) (hOF : O⊆F) (hO : O.card≤ 1) (hF : 4≤ F.card)
    {A₁ A₂ : Finset (Q : Set (U h))} (h₁ : A₁.Nonempty) (h₂ : A₂.Nonempty)
    (rep : ∀ v : (Q : Set (U h)),∀ a∈F,a∉O→ (J h).Adj v.val a→ v∈A₁∨v∈A₂)
    {q : ℕ} (hq₁ : 1≤ q) (hq₄ : q≤ 4)
    (loss : ∀ v : (Q : Set (U h)),(F.filter ((J h).Adj v.val)).card+q ≤
      4+((if v∈A₁ then 1 else 0)+(if v∈A₂ then 1 else 0)))
    {P : (U h)→ (U h)→ Prop}
    (ends : ∀ u∈A₁,∀ v∈A₂,∃ a b,P a b∧a∈F∧b∈F ∧
      a≠b∧(J h).Adj a u.val∧(J h).Adj v.val b) :
    qaa1 h F P q:=by
  classical
  let W:=(Q : Set (U h))
  let I:=(J h).induce (Q : Set (U h))
  let H:=bg0 I A₁ A₂
  let Z₀ : Finset W:=Finset.univ.filter fun v=>v.val∈h.D
  let Z:=Z₀.map qd4
  have hZ (v : W) : Sum.inr v∈Z↔v.val∈h.D:=by simp [Z,Z₀,qd4]
  have hI (v : W) : ∀ z∈(F : Set (U h)),v.val.val≠z.val:=by
    intro z hz he
    exact Finset.disjoint_left.mp c.disj v.property ((Subtype.ext he).symm ▸ hz)
  let K : Set V:=Subtype.val '' (F : Set (U h))
  have hIK (v : W) : v.val.val∉K:=by rintro ⟨z,hz,he⟩;exact hI v z hz he.symm
  have aux (v : W) : (J h).degree v.val+q≤ 4+H.degree (Sum.inr v):=by
    have:=loss v
    have hJ:=qs6 v.property c.disj c.closed
    have hH:=qae7 (G:=(J h)) (A₁:=A₁) (A₂:=A₂) v
    change H.degree (Sum.inr v)=_ at hH
    omega
  have hW : 4≤ Fintype.card (Fin 2 ⊕ W):=by
    simpa [W,Fintype.card_sum] using Nat.add_le_add_left c.card 2
  have hr : Rt0 H (Sum.inl 0) (Sum.inl 1):=qae6 h.hconn4 c hOF hO hF h₁ h₂ rep
  obtain ⟨direct,extra⟩:=qak1 coy hr hW hq₁ hq₄ (Z:=Z)
    (by simp [Z,qd4]) (by simp [Z,qd4])
    (by
      rintro (i|v) hv₀ hv₁
      · rcases qa8 i with rfl|rfl <;> contradiction
      · have:=aux v
        have hd : 4≤ (J h).degree v.val:=h.hdeg4 v.val
        omega)
    (by
      rintro (i|v) hv₀ hv₁ hvZ
      · rcases qa8 i with rfl|rfl <;> contradiction
      · have:=aux v
        have hd : 5≤ (J h).degree v.val:=h.hdeg5_off_D v.val (fun hv=>hvZ ((hZ v).mpr hv))
        omega)
  have choose (u : W) (hu : u∈A₁) (v : W) (hv : v∈A₂) :
      ∃ a b : (U h),P a b∧a.val∈K∧b.val∈K ∧
        a.val≠b.val∧B.Adj a.val u.val.val∧B.Adj v.val.val b.val:=by
    obtain ⟨a,b,hp,ha,hb,hab,ea,eb⟩:=ends u hu v hv
    exact ⟨a,b,hp,⟨a,ha,rfl⟩,⟨b,hb,rfl⟩,fun he=>hab (Subtype.ext he),ea,eb⟩
  by_cases hz : 2≤ Z.card
  · obtain ⟨w,hw⟩ : Z₀.Nonempty:=by
      apply Finset.card_pos.mp
      have hz₀ : 2≤ Z₀.card:=by simpa [Z] using hz
      omega
    obtain ⟨cv,hcv,-⟩:=h.hD_adj w.val (Finset.mem_filter.mp hw).2
    have hcvU:=h.hc_not_mem cv hcv
    have hcvK : cv∉K:=fun ⟨a,_,he⟩=>hcvU (he ▸ a.property)
    have hcZ : ∀ v∈Z₀,B.Adj cv v.val.val:=by
      intro v hv
      obtain ⟨cv',hcv',e⟩:=h.hD_adj v.val (Finset.mem_filter.mp hv).2
      exact (Option.some_injective _ (hcv'.symm.trans hcv)) ▸ e
    let f : av0 I Z₀ →g B:=⟨fun o=>o.elim cv fun v=>v.val.val,by
      rintro (_|u) (_|v) e
      exacts [e.elim,hcZ v e,(hcZ u e).symm,e]⟩
    have hf : Function.Injective f:=by
      rintro (_|u) (_|v) e
      · rfl
      · exact (hcvU (show cv∈h.U from (show cv=v.val.val from e).symm ▸ v.val.property)).elim
      · exact (hcvU (show cv∈h.U from (show u.val.val=cv from e) ▸ u.val.property)).elim
      · exact congrArg some (Subtype.ext (Subtype.ext e))
    have hfK : ∀ w,f w∉K:=by
      rintro (_|w)
      · exact hcvK
      · exact hIK w
    obtain ⟨m,d,hm,hd,hs⟩:=extra hz
    refine ⟨m,d,hm,hd,fun i=>?_⟩
    obtain ⟨p,hp,hl⟩:=hs i
    let e:=qab7 I A₁ A₂ Z₀
    have hpm : (p.map e).IsPath:=qb8 e qp3 hp
    obtain ⟨a,b,hab,t,ht,htlen,hts⟩:=qaa0 f hf hfK (j:=Subtype.val)
      (P:=P) (fun u hu v hv=>by
        obtain ⟨u',hu',rfl⟩:=Finset.mem_map.mp hu
        obtain ⟨v',hv',rfl⟩:=Finset.mem_map.mp hv
        exact choose u' hu' v' hv') hpm
    exact ⟨a,b,hab,t,ht,htlen.trans ((Walk.length_map _ _).trans hl),hts⟩
  · let f : I →g B:=(Embedding.induce (h.U : Set V)).toHom.comp
      (Embedding.induce (Q : Set (U h))).toHom
    have hf : Function.Injective f:=fun _ _ e=>Subtype.ext (Subtype.ext e)
    obtain ⟨m,d,hm,hd,hs⟩:=direct (by omega)
    refine ⟨m,d,hm,hd,fun i=>?_⟩
    obtain ⟨p,hp,hl⟩:=hs i
    obtain ⟨a,b,hab,t,ht,htlen,hts⟩:=qaa0 f hf hIK (j:=Subtype.val) choose hp
    exact ⟨a,b,hab,t,ht,htlen.trans hl,hts⟩
private theorem qx3 (hB : Nf0 B) {F : Finset (U h)} {P : (U h)→ (U h)→ Prop}
    {p q n : ℕ} (hp : 1≤ p) (hq : 1≤ q) (hs : 6≤ p+q) (hn : 1≤ n)
    (family : qaa1 h F P q)
    (core : ∀ a b,P a b→ ∀ i : Fin p,Route (J h) F a b (n+i.val*2)) : False:=by
  obtain ⟨m,d,hm,hd,hf⟩:=family
  obtain ⟨j,i,hdiv⟩:=qi3 hq hp (by omega) hd (Or.inr rfl) m n 0
  obtain ⟨a,b,hab,t,ht,htl,hts⟩:=hf j
  obtain ⟨s,hsp,hsl,hss⟩:=core a b hab i
  let e : J h →g B:=(Embedding.induce (h.U : Set V)).toHom
  have hmap:=Walk.length_map e s
  have hint : ∀ z,z∈t.support→ z∈(s.map e).support→ z=a.val∨z=b.val:=by
    intro z hz hz'
    apply hts z hz
    rw [Walk.support_map,List.mem_map] at hz'
    obtain ⟨w,hw,rfl⟩:=hz'
    exact ⟨w,hss w hw,rfl⟩
  have hlen : 3≤ t.length+(s.map e).length:=by
    rw [htl,hmap,hsl]
    omega
  have hdiv' : 5∣t.length+(s.map e).length:=by
    rw [htl,hmap,hsl]
    simpa using hdiv
  exact qc4 hB ht (qb8 e Subtype.val_injective hsp) hint hlen hdiv'
private def qai1 (Q S : Finset (U h)) : Prop :=
  ∃ v∈Q,∃ a∈S,(J h).Adj v a
private theorem qae1 (coy : COY4) (hB : Nf0 B) {r : ℕ}
    {S T Q O : Finset (U h)} (c : SquareCore (J h) r S T)
    (e : Exterior (J h) (S∪T) Q) (hOT : O⊆T) (hO : O.card≤ 1)
    (hOr : O.card≤ r - 2) (hc : Cross (J h) S (T\O))
    (hS : qai1 h Q S) (hT : qai1 h Q (T\O)) : False:=by
  classical
  let A₁ : Finset (Q : Set (U h)) :=
    Finset.univ.filter fun v=>∃ a∈S,(J h).Adj v.val a
  let A₂ : Finset (Q : Set (U h)) :=
    Finset.univ.filter fun v=>∃ b∈T\O,(J h).Adj v.val b
  have mem₁ (v : (Q : Set (U h))) :
      v∈A₁↔∃ a∈S,(J h).Adj v.val a:=by simp [A₁]
  have mem₂ (v : (Q : Set (U h))) :
      v∈A₂↔∃ b∈T\O,(J h).Adj v.val b:=by simp [A₂]
  have ne₁ : A₁.Nonempty:=by
    obtain ⟨u,hu,a,ha,e⟩:=hS
    exact ⟨⟨u,hu⟩,(mem₁ _).mpr ⟨a,ha,e⟩⟩
  have ne₂ : A₂.Nonempty:=by
    obtain ⟨v,hv,b,hb,e⟩:=hT
    exact ⟨⟨v,hv⟩,(mem₂ _).mpr ⟨b,hb,e⟩⟩
  have rep : ∀ v : (Q : Set (U h)),∀ a∈S∪T,a∉O →
      (J h).Adj v.val a→ v∈A₁∨v∈A₂:=by
    intro v a ha haO ea
    rcases Finset.mem_union.mp ha with ha|ha
    · exact Or.inl ((mem₁ v).mpr ⟨a,ha,ea⟩)
    · exact Or.inr ((mem₂ v).mpr ⟨a,Finset.mem_sdiff.mpr ⟨ha,haO⟩,ea⟩)
  have hr₂:=c.lower
  have hr₄:=c.upper
  have hF : 4≤ (S∪T).card:=by
    rw [Finset.card_union_of_disjoint c.disj]
    have:=c.left_card
    have:=c.right_card
    omega
  refine qx3 h hB (F:=S∪T)
    (P:=fun a b=>a∈S∧b∈T∧(J h).Adj a b) (p:=r) (q:=6 - r) (n:=1)
    (by omega) (by omega) (by omega) (by simp) ?_ ?_
  · refine qs5 h coy e (hOT.trans Finset.subset_union_right) hO hF ne₁ ne₂ rep
      (by omega) (by omega) ?_ (P:=fun a b=>a∈S∧b∈T∧(J h).Adj a b) ?_
    · intro v
      have hbound:=c.exterior v.val (fun hv=>Finset.disjoint_left.mp e.disj v.property hv)
      by_cases hv₁ : v∈A₁
      · simp only [hv₁,if_true]
        omega
      by_cases hv₂ : v∈A₂
      · simp only [hv₁,hv₂,if_false,if_true]
        omega
      have hsub : (S∪T).filter ((J h).Adj v.val)⊆O:=by
        intro a ha
        obtain ⟨ha,ea⟩:=Finset.mem_filter.mp ha
        by_contra hn
        exact (rep v a ha hn ea).elim hv₁ hv₂
      have:=Finset.card_le_card hsub
      simp only [hv₁,hv₂,if_false]
      omega
    · intro u hu v hv
      obtain ⟨a,ha,ea⟩:=(mem₁ u).mp hu
      obtain ⟨b,hb,eb⟩:=(mem₂ v).mp hv
      have hbT:=(Finset.mem_sdiff.mp hb).1
      exact ⟨a,b,⟨ha,hbT,hc a ha b hb⟩,Finset.mem_union_left _ ha,
        Finset.mem_union_right _ hbT,fun he=>Finset.disjoint_left.mp c.disj ha (he ▸ hbT),
        ea.symm,eb⟩
  · intro a b hab i
    obtain ⟨ha,hb,eab⟩:=hab
    have hi₁ : i.val+1≤ S.card:=i.isLt.trans_le c.left_card
    have hi₂ : i.val+1≤ T.card:=i.isLt.trans_le c.right_card
    rcases c.shape with ⟨hc',-⟩|⟨x,y,hm,hs,ht,hr⟩
    · simpa [Nat.add_comm,Nat.mul_comm] using ql0 i.val c.disj hc' ha hb hi₁ hi₂
    · simpa [Nat.add_comm,Nat.mul_comm] using
        qaf3 i.val c.disj hm ha hb eab hi₁ hi₂ (by omega) (by omega)
private theorem qx8 (coy : COY4) (hB : Nf0 B) {r : ℕ} {S T Q : Finset (U h)}
    {x y : U h} (c : SquareCore (J h) r S T) (e : Exterior (J h) (S∪T) Q)
    (hm : Missing (J h) S T x y) (hr : 3≤ r)
    (hS : qai1 h Q S) (hT : qai1 h Q (T.erase y)) : False:=by
  apply qae1 h coy hB c e (O:={y}) (by simpa using hm.2.1) (by simp) (by simp only [Finset.card_singleton];omega)
  · intro a ha b hb
    exact (hm.2.2 a ha b (Finset.mem_sdiff.mp hb).1).mpr
      (Or.inr (by simpa using (Finset.mem_sdiff.mp hb).2))
  · exact hS
  · simpa only [Finset.sdiff_singleton_eq_erase] using hT
private theorem qao8 (coy : COY4) (hB : Nf0 B) {r : ℕ} {S T Q : Finset (U h)}
    (c : SquareCore (J h) r S T) (e : Exterior (J h) (S∪T) Q)
    (hT : ¬ qai1 h Q T) : False:=by
  classical
  have hr₂:=c.lower
  have hr₄:=c.upper
  have hF : 4≤ (S∪T).card:=by
    rw [Finset.card_union_of_disjoint c.disj]
    have:=c.left_card
    have:=c.right_card
    omega
  have left (v : (Q : Set (U h))) {a : U h} (ha : a∈S∪T)
      (ea : (J h).Adj v.val a) : a∈S :=
    (Finset.mem_union.mp ha).resolve_right (fun haT=>hT ⟨v.val,v.property,a,haT,ea⟩)
  let R:=qm1 (J h) (S∪T) Q
  have hR : 4≤ R.card:=qt3 h.hconn4 e hF
  have hRS : R⊆S:=by
    intro a ha
    obtain ⟨ha,v,hv,ev⟩:=Finset.mem_filter.mp ha
    exact left ⟨v,hv⟩ ha ev
  have hS : 4≤ S.card:=hR.trans (Finset.card_le_card hRS)
  obtain ⟨a₀,ha₀⟩:=Finset.card_pos.mp (by omega : 0 < R.card)
  obtain ⟨b₀,hb₀,hba⟩:=Finset.exists_mem_ne (by omega : 1 < R.card) a₀
  obtain ⟨-,u,hu,eu⟩:=Finset.mem_filter.mp ha₀
  obtain ⟨-,v,hv,ev⟩:=Finset.mem_filter.mp hb₀
  let N (w : (Q : Set (U h))):=S.filter ((J h).Adj w.val)
  have memN (w : (Q : Set (U h))) (a : U h) :
      a∈N w↔a∈S∧(J h).Adj w.val a:=Finset.mem_filter
  have eqN (w : (Q : Set (U h))) :
      (S∪T).filter ((J h).Adj w.val)=N w:=by
    ext a
    simp only [Finset.mem_filter,memN]
    exact ⟨fun h=>⟨left w h.1 h.2,h.2⟩,fun h=>⟨Finset.mem_union_left _ h.1,h.2⟩⟩
  let A₁:=Finset.univ.filter fun w=>2≤ (N w).card∨a₀∈N w
  let A₂:=Finset.univ.filter fun w=>((N w).erase a₀).Nonempty
  have mem₁ (w : (Q : Set (U h))) : w∈A₁↔2≤ (N w).card∨a₀∈N w:=by
    simp [A₁]
  have mem₂ (w : (Q : Set (U h))) : w∈A₂↔((N w).erase a₀).Nonempty:=by simp [A₂]
  have ne₁ : A₁.Nonempty:=⟨⟨u,hu⟩,(mem₁ _).mpr (Or.inr ((memN _ _).mpr ⟨hRS ha₀,eu⟩))⟩
  have ne₂ : A₂.Nonempty :=
    ⟨⟨v,hv⟩,(mem₂ _).mpr ⟨b₀,Finset.mem_erase.mpr ⟨hba,(memN _ _).mpr ⟨hRS hb₀,ev⟩⟩⟩⟩
  have repN (w : (Q : Set (U h))) (a : U h) (ha : a∈N w) : w∈A₁∨w∈A₂:=by
    by_cases h : a=a₀
    · exact Or.inl ((mem₁ _).mpr (Or.inr (h ▸ ha)))
    · exact Or.inr ((mem₂ _).mpr ⟨a,Finset.mem_erase.mpr ⟨h,ha⟩⟩)
  let q:=if r=2 then 4 else 3
  let p:=6 - q
  have hq : q=4∨q=3:=by dsimp [q];split_ifs <;> simp
  refine qx3 h hB (F:=S∪T)
    (P:=fun a b=>a∈S∧b∈S∧a≠b) (p:=p) (q:=q) (n:=2)
    (by dsimp [p];omega) (by omega) (by dsimp [p];omega) (by simp) ?_ ?_
  · refine qs5 h coy e (O:=∅) (by simp) (by simp) hF ne₁ ne₂
      (fun w a ha _ ea=>repN w a ((memN _ _).mpr ⟨left w ha ea,ea⟩))
      (by omega) (by omega) ?_ (P:=fun a b=>a∈S∧b∈S∧a≠b) ?_
    · intro w
      rw [eqN]
      have hc:=c.exterior w.val (fun hw=>Finset.disjoint_left.mp e.disj w.property hw)
      rw [eqN] at hc
      by_cases big : 2≤ (N w).card
      · obtain ⟨a,ha,hne⟩:=Finset.exists_mem_ne (by omega : 1 < (N w).card) a₀
        have h₁:=(mem₁ w).mpr (Or.inl big)
        have h₂:=(mem₂ w).mpr ⟨a,Finset.mem_erase.mpr ⟨hne,ha⟩⟩
        have hq₃ : q=3:=by
          have : r≠2:=by omega
          simp [q,this]
        simp only [h₁,h₂,if_true,hq₃]
        omega
      · by_cases hz : (N w).card=0
        · omega
        · obtain ⟨a,ha⟩:=Finset.card_pos.mp (by omega : 0 < (N w).card)
          rcases repN w a ha with hh|hh <;> simp only [hh,if_true] <;> omega
    · intro w hw w' hw'
      obtain ⟨b,hb⟩:=(mem₂ w').mp hw'
      obtain ⟨hb₁,hb₂⟩:=Finset.mem_erase.mp hb
      obtain ⟨a,ha,hab⟩ : ∃ a∈N w,a≠b:=((mem₁ w).mp hw).elim
        (fun hh=>Finset.exists_mem_ne (by omega) b) (fun hh=>⟨a₀,hh,hb₁.symm⟩)
      obtain ⟨haS,ea⟩:=(memN _ _).mp ha
      obtain ⟨hbS,eb⟩:=(memN _ _).mp hb₂
      exact ⟨a,b,⟨haS,hbS,hab⟩,Finset.mem_union_left _ haS,
        Finset.mem_union_left _ hbS,hab,ea.symm,eb⟩
  · intro a b hab i
    obtain ⟨ha,hb,hab⟩:=hab
    have hi:=i.isLt
    have hi₃ : i.val < 3:=by dsimp [p] at hi;omega
    have hiT : i.val+1≤ T.card:=by
      have ht:=c.right_card
      by_cases he : r=2
      · simp [p,q,he] at hi
        omega
      · omega
    rcases c.shape with ⟨hc,-⟩|⟨x,y,hm,hs,ht,hr⟩
    · simpa [Nat.add_comm,Nat.mul_comm] using
        qq7 i.val c.disj hc ha hb hab (by omega) hiT
    · have h':=qq7 i.val (c.disj.mono_right (Finset.erase_subset y T))
        (fun u hu v hv=>(hm.2.2 u hu v (Finset.mem_of_mem_erase hv)).mpr
          (Or.inr (Finset.ne_of_mem_erase hv))) ha hb hab (by omega)
        (by rw [Finset.card_erase_of_mem hm.2.1];omega)
      simpa [Nat.add_comm,Nat.mul_comm] using
        h'.mono (Finset.union_subset_union Finset.Subset.rfl (Finset.erase_subset y T))
end Host
theorem qaq2 (coy : COY4) {V : Type} [Fintype V] [DecidableEq V]
    {B : SimpleGraph V} [DecidableRel B.Adj] (hB : Nf0 B) (h : H40 B)
    (h3 : 3∉(B.induce (h.U : Set V)).cycleLengths) :
    4∉(B.induce (h.U : Set V)).cycleLengths:=by
  classical
  intro h4
  obtain ⟨r,S,T,c⟩:=qam8 (qk1 (h.U : Set V) hB) h3 h4
  obtain ⟨Q,e⟩:=qai5 c h.hdeg4 (qad1 h3 c h.hD_def h.hD_card h.hdeg4)
  have e' : Exterior (J h) (T∪S) Q:=by simpa only [Finset.union_comm T S] using e
  by_cases hS : qai1 h Q S
  · by_cases hT : qai1 h Q T
    · rcases c.shape with ⟨hc,-⟩|⟨x,y,hm,hs,ht,hr⟩
      · exact qae1 h coy hB c e (O:=∅) (by simp) (by simp) (by simp)
          (by simpa using hc) hS (by simpa using hT)
      · by_cases hT' : qai1 h Q (T.erase y)
        · exact qx8 h coy hB c e hm hr hS hT'
        · have hS' : qai1 h Q (S.erase x):=by
            by_contra hn
            have hF : 4≤ (S∪T).card:=by rw [Finset.card_union_of_disjoint c.disj];omega
            have hc : 4≤ (qm1 (J h) (S∪T) Q).card :=
              qt3 h.hconn4 e hF
            have hsub : qm1 (J h) (S∪T) Q⊆{x,y}:=by
              intro a ha
              obtain ⟨ha,v,hv,ev⟩:=Finset.mem_filter.mp ha
              rcases Finset.mem_union.mp ha with ha|ha
              · by_cases he : a=x
                · simp [he]
                · exact (hn ⟨v,hv,a,Finset.mem_erase.mpr ⟨he,ha⟩,ev⟩).elim
              · by_cases he : a=y
                · simp [he]
                · exact (hT' ⟨v,hv,a,Finset.mem_erase.mpr ⟨he,ha⟩,ev⟩).elim
            have:=(Finset.card_le_card hsub).trans Finset.card_le_two
            omega
          exact qx8 h coy hB c.flip e' hm.flip hr hT hS'
    · exact qao8 h coy hB c e hT
  · exact qao8 h coy hB c.flip e' hS
end DeanK5
end M5
section M6
namespace DeanK5
open SimpleGraph
variable {V : Type} {B : SimpleGraph V}
private structure Ep0 (B : SimpleGraph V) (x y : V) (S : Set V) where
  walk : B.Walk x y
  isPath : walk.IsPath
  inside : ∀ v∈walk.support,v∈S
private def qt9 {X : Finset V} {x y : (X : Set V)}
    (p : (B.induce (X : Set V)).Walk x y) (hp : p.IsPath) :
    Ep0 B x.val y.val (X : Set V) where
  walk:=p.map (Embedding.induce (X : Set V)).toHom
  isPath:=qb8 _ (Embedding.induce (G:=B) (X : Set V)).injective hp
  inside:=by
    intro v hv
    change v∈(p.map (Embedding.induce (G:=B) (X : Set V)).toHom).support at hv
    rw [Walk.support_map,List.mem_map] at hv
    obtain ⟨w,-,rfl⟩:=hv
    exact w.property
private def Ep0.attach {x y u v : V} {S : Set V} (P : Ep0 B x y S)
    (hu : B.Adj u x) (hv : B.Adj y v) (huS : u∉S) (hvS : v∉S) (hne : u≠v) :
    Ep0 B u v (insert u (insert v S)) where
  walk:=(Walk.cons hu P.walk).concat hv
  isPath:=by
    refine (qn6
      (qf0 hu P.isPath (fun h=>huS (P.inside _ h))).1 hv ?_).1
    simp only [Walk.support_cons,List.mem_cons,not_or]
    exact ⟨hne.symm,fun h=>hvS (P.inside _ h)⟩
  inside:=by
    intro z hz
    simp only [Walk.support_concat,Walk.support_cons,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hz
    exact hz.elim (fun h=>h.elim Or.inl (fun h=>Or.inr (Or.inr (P.inside _ h))))
      (fun h=>Or.inr (Or.inl h))
private theorem qw7 (hB : Nf0 B) {a b c d : V} {S T L R : Set V}
    (A : AdmH B a b 3 S) (C : AdmH B c d 3 T)
    (P : Ep0 B a c L) (Q : Ep0 B d b R)
    (hST : ∀ z∈S,z∈T→ z=a∨z=b)
    (hSL : ∀ z∈S,z∈L→ z=a) (hSR : ∀ z∈S,z∈R→ z=b)
    (hLT : ∀ z∈L,z∈T→ z=c) (hRT : ∀ z∈R,z∈T→ z=d)
    (hLR : Disjoint L R) : False:=by
  obtain ⟨s,ds,hs,hds,A⟩:=A
  obtain ⟨t,dt,ht,hdt,C⟩:=C
  choose p hp hlp hsp using A
  choose q hq hlq hsq using C
  have h₁ (j : Fin 3) : (P.walk.append (q j)).IsPath :=
    (qa3 P.isPath (hq j)
      (fun z hz hw=>hLT z (P.inside z hz) (hsq j z hw))).1
  have h₂ (j : Fin 3) : ((P.walk.append (q j)).append Q.walk).IsPath:=by
    refine (qa3 (h₁ j) Q.isPath fun z hz hw=>?_).1
    rcases (Walk.mem_support_append_iff _ _).mp hz with hz|hz
    · exact (Set.disjoint_left.mp hLR (P.inside z hz) (Q.inside z hw)).elim
    · exact hRT z (Q.inside z hw) (hsq j z hz)
  refine qe0 hB (a₁:=s) (a₂:=t)
    (b:=P.walk.length+Q.walk.length)
    (by decide) (by decide) (by decide) hds hdt p
    (fun j=>(P.walk.append (q j)).append Q.walk)
    (fun i=>⟨hp i,hlp i⟩)
    (fun j=>⟨h₂ j,by simp only [Walk.length_append,hlq];omega⟩) ?_ ?_
  · intro i j z hz hw
    simp only [Walk.mem_support_append_iff] at hw
    rcases hw with (hw|hw)|hw
    · exact Or.inl (hSL z (hsp i z hz) (P.inside z hw))
    · exact hST z (hsp i z hz) (hsq j z hw)
    · exact Or.inr (hSR z (hsp i z hz) (Q.inside z hw))
  · intro i j
    simp only [Walk.length_append,hlp,hlq]
    omega
private def qc1 (X : Finset V) (Y : Finset (X : Set V)) : Finset V :=
  Y.map ⟨Subtype.val,Subtype.val_injective⟩
private theorem extImage_mem {X : Finset V} {Y : Finset (X : Set V)} {v : V} :
    v∈qc1 X Y↔∃ hv : v∈X,(⟨v,hv⟩ : (X : Set V))∈Y:=by
  simp only [qc1,Finset.mem_map,Function.Embedding.coeFn_mk]
  exact ⟨fun ⟨⟨w,hw⟩,hy,e⟩=>e ▸ ⟨hw,hy⟩,fun ⟨hv,hy⟩=>⟨⟨v,hv⟩,hy,rfl⟩⟩
private theorem qq5 {X : Finset V} {Y : Finset (X : Set V)} :
    qc1 X Y⊆X:=fun _ h=>(extImage_mem.mp h).choose
private theorem extImage_coe {X : Finset V} {Y : Finset (X : Set V)} {v : (X : Set V)} :
    v.val∈qc1 X Y↔v∈Y :=
  ⟨fun h=>(extImage_mem.mp h).choose_spec,fun h=>extImage_mem.mpr ⟨v.property,h⟩⟩
private def qac4 (X : Finset V) (Y : Finset (X : Set V)) :
    (B.induce (X : Set V)).induce (Y : Set (X : Set V)) ≃g B.induce (qc1 X Y : Set V) where
  toEquiv :=
    { toFun:=fun v=>⟨v.val.val,extImage_coe.mpr v.property⟩
      invFun:=fun v=>⟨⟨v.val,qq5 v.property⟩,extImage_coe.mp v.property⟩
      left_inv:=fun _=>rfl
      right_inv:=fun _=>rfl }
  map_rel_iff':=Iff.rfl
private theorem qo8 [DecidableEq V] [DecidableRel B.Adj] {U : Finset V}
    (S : Finset (U : Set V)) (v : (U : Set V)) :
    ((B.induce (U : Set V)).neighborFinset v∩S).card =
      ((qc1 U S).filter (B.Adj v.val)).card:=by
  rw [← Finset.card_map (f:=(⟨Subtype.val,Subtype.val_injective⟩ : (U : Set V) ↪ V))]
  congr 1
  ext w
  simp only [Finset.mem_map,Finset.mem_inter,mem_neighborFinset,Finset.mem_filter,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨z,⟨hz,hS⟩,rfl⟩
    exact ⟨extImage_coe.mpr hS,hz⟩
  · rintro ⟨hw,hadj⟩
    obtain ⟨hU,hS⟩:=extImage_mem.mp hw
    exact ⟨⟨w,hU⟩,⟨hadj,hS⟩,rfl⟩
private def qaf9 {K : Finset V} {a b : (K : Set V)}
    (p : (B.induce (K : Set V)).Walk a b) (hp : p.IsPath) :
    Ep0 B a.val b.val {z|∃ w∈p.support,w.val=z} where
  walk:=(qt9 p hp).walk
  isPath:=(qt9 p hp).isPath
  inside:=by
    intro z hz
    have hw : (qt9 p hp).walk.support=p.support.map Subtype.val :=
      Walk.support_map (Embedding.induce (G:=B) (K : Set V)).toHom p
    exact List.mem_map.mp (hw ▸ hz)
private def Ep0.reverse {a b : V} {S : Set V} (P : Ep0 B a b S) : Ep0 B b a S :=
  ⟨P.walk.reverse,P.isPath.reverse,fun z hz =>
    P.inside z (by simpa only [Walk.support_reverse,List.mem_reverse] using hz)⟩
section Host
variable [Fintype V] [DecidableEq V] [DecidableRel B.Adj]
omit [Fintype V] in
private theorem qs7 {U K : Finset V} (hK : K⊆U) (v : V) :
    (U.filter (B.Adj v)).card =
      (K.filter (B.Adj v)).card+((U\K).filter (B.Adj v)).card:=by
  calc
    _=(((U\K)∪K).filter (B.Adj v)).card:=by rw [Finset.sdiff_union_of_subset hK]
    _=_:=by
      rw [Finset.filter_union,Finset.card_union_of_disjoint,Nat.add_comm]
      exact Finset.disjoint_left.mpr fun z hw hz =>
        (Finset.mem_sdiff.mp (Finset.mem_filter.mp hw).1).2 (Finset.mem_filter.mp hz).1
private theorem qk6 (h : H40 B) {K X : Finset V} (hK : K⊆h.U)
    {v : V} (hv : v∈h.U\K) (hkv : (K.filter (B.Adj v)).card≤ 1)
    (hcl : ∀ w∈h.U\K,B.Adj v w→ w∈X) :
    3≤ (X.filter (B.Adj v)).card ∧
      (v∉qc1 h.U h.D→ 4≤ (X.filter (B.Adj v)).card):=by
  have hvU:=(Finset.mem_sdiff.mp hv).1
  have hsplit:=qs7 (B:=B) hK v
  have hle : ((h.U\K).filter (B.Adj v)).card≤ (X.filter (B.Adj v)).card :=
    Finset.card_le_card fun w hw =>
      let ⟨hwW,hadj⟩:=Finset.mem_filter.mp hw
      Finset.mem_filter.mpr ⟨hcl w hwW hadj,hadj⟩
  have hd:=h.hdeg4 ⟨v,hvU⟩
  rw [qa5] at hd
  change 4≤ (h.U.filter (B.Adj v)).card at hd
  refine ⟨by omega,fun hD=>?_⟩
  have hd':=h.hdeg5_off_D ⟨v,hvU⟩ (fun hm=>hD (extImage_coe.mpr hm))
  rw [qa5] at hd'
  change 5≤ (h.U.filter (B.Adj v)).card at hd'
  omega
private def qh1 (h : H40 B) (X : Finset V) (a b : V) : Finset V :=
  ((X∩qc1 h.U h.D).erase a).erase b
private theorem qd9 (h : H40 B) {X : Finset V} {a b v : V} :
    v∈qh1 h X a b↔v∈X∧v≠a∧v≠b∧v∈qc1 h.U h.D:=by
  simp only [qh1,Finset.mem_erase,Finset.mem_inter]
  tauto
omit [Fintype V] [DecidableEq V] [DecidableRel B.Adj] in
private theorem qap4 {X : Finset V} (hX : Kc0 (B.induce (X : Set V)) 2)
    {a b : V} (ha : a∈X) (hb : b∈X) (hab : a≠b) :
    Rt0 (B.induce (X : Set V)) ⟨a,ha⟩ ⟨b,hb⟩ :=
  ⟨fun e=>hab (congrArg Subtype.val e),hX.1,fun S hS =>
    (hX.2 S hS).mono (fun _ _ ha=>Or.inl ha)⟩
private theorem qn7 (coy : COY4) (h : H40 B) {X : Finset V} (hX : X⊆h.U)
    {a b : V} (ha : a∈X) (hb : b∈X) (hab : a≠b)
    (h2 : Kc0 (B.induce (X : Set V)) 2)
    (hd : ∀ v∈X,v≠a→ v≠b→ 3≤ (X.filter (B.Adj v)).card ∧
      (v∉qc1 h.U h.D→ 4≤ (X.filter (B.Adj v)).card)) :
    AdmH B a b 3 ((X : Set V)∪{v|2≤ (qh1 h X a b).card∧h.c=some v}) :=
  h.restore_on_sub coy hX ha hb (qap4 h2 ha hb hab)
    (fun _ hv=>let hm:=(qd9 h).mp hv;⟨hm.1,hm.2.1,hm.2.2.1⟩)
    (fun _ _ hvZ=>extImage_coe.mp ((qd9 h).mp hvZ).2.2.2)
    (fun v hv hva hvb=>(hd v hv hva hvb).1)
    (fun v hv hva hvb hvZ =>
      (hd v hv hva hvb).2 fun hvD=>hvZ ((qd9 h).mpr ⟨hv,hva,hvb,hvD⟩))
private theorem qw8 (coy : COY4) (h : H40 B) {X Z : Finset V} (hX : X⊆h.U)
    {b : V} (hb : b∈X) (h2 : Kc0 (B.induce (X : Set V)) 2)
    (hZ : 2≤ Z.card) (hZD : ∀ z∈Z,z∈X∧z∈qc1 h.U h.D)
    (hd : ∀ v∈X,v≠b→ 3≤ (X.filter (B.Adj v)).card ∧
      (v∉qc1 h.U h.D→ 4≤ (X.filter (B.Adj v)).card)) :
    ∃ cv,h.c=some cv∧AdmH B cv b 3 (insert cv (X : Set V)):=by
  classical
  obtain ⟨z,hz⟩:=Finset.card_pos.mp (by omega : 0 < Z.card)
  obtain ⟨cv,hcv,-⟩:=h.hD_adj ⟨z,hX (hZD z hz).1⟩
    (extImage_coe.mp (hZD z hz).2)
  let A : Finset (X : Set V):=Finset.univ.filter fun v=>v.val∈qc1 h.U h.D
  have hA : Z.card≤ A.card:=by
    rw [← Finset.card_map (f:=(⟨Subtype.val,Subtype.val_injective⟩ : (X : Set V) ↪ V))]
    refine Finset.card_le_card fun v hv=>?_
    obtain ⟨hvX,hvD⟩:=hZD v hv
    exact Finset.mem_map.mpr ⟨⟨v,hvX⟩,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hvD⟩,rfl⟩
  have h2':=qm5 (Z:=A) h2 (hZ.trans hA)
  let b' : (X : Set V):=⟨b,hb⟩
  obtain ⟨w,hw,-⟩:=qf8 h2.1 b' b'
  have hr : Rt0 (av0 (B.induce (X : Set V)) A) none (some b') :=
    ⟨by simp,h2'.1,fun S hS=>(h2'.2 S hS).mono (fun _ _ ha=>Or.inl ha)⟩
  have hP:=coy _ _ none (some b') none 3 (by decide) (by decide) hr
    ⟨some w,by simp,by simpa using hw,by simp⟩
  have hP' : Adm0 (av0 (B.induce (X : Set V)) A) none (some b') 3:=by
    refine hP ?_
    rintro (_|v) hv hvb _
    · exact (hv rfl).elim
    · have hvb' : v.val≠b:=fun e=>hvb (congrArg some (Subtype.ext e))
      have hdv:=hd v.val v.property hvb'
      rw [qi2,qa5]
      split_ifs with hmem
      · omega
      · exact hdv.2 fun hD=>hmem (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hD⟩)
  let f : av0 (B.induce (X : Set V)) A →g B :=
    ⟨fun o=>o.elim cv Subtype.val,by
      rintro (_|u) (_|v) hv
      · exact (adjoin_not_adj_none hv).elim
      · obtain ⟨cv',hc',ha⟩:=h.hD_adj ⟨v.val,hX v.property⟩
          (extImage_coe.mp (Finset.mem_filter.mp hv).2)
        exact (Option.some_injective _ (hc'.symm.trans hcv)) ▸ ha
      · obtain ⟨cv',hc',ha⟩:=h.hD_adj ⟨u.val,hX u.property⟩
          (extImage_coe.mp (Finset.mem_filter.mp hv).2)
        exact (Option.some_injective _ (hc'.symm.trans hcv)) ▸ ha.symm
      · exact hv⟩
  have hcvX : cv∉X:=fun hm=>h.hc_not_mem cv hcv (hX hm)
  have hf : Function.Injective f:=by
    rintro (_|u) (_|v) e
    · rfl
    · exact (hcvX ((show cv=v.val from e).symm ▸ v.property)).elim
    · exact (hcvX ((show u.val=cv from e) ▸ u.property)).elim
    · exact congrArg some (Subtype.ext e)
  refine ⟨cv,hcv,(qx7 f hf hP').mono ?_⟩
  rintro _ ⟨_|v,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr v.property
private noncomputable def extNeighbors (B : SimpleGraph V) (K X : Finset V) : Finset V:=by
  classical
  exact K.filter fun y=>∃ x∈X,B.Adj y x
omit [Fintype V] [DecidableEq V] [DecidableRel B.Adj] in
private theorem extNeighbors_mem {K X : Finset V} {y : V} :
    y∈extNeighbors B K X↔y∈K∧∃ x∈X,B.Adj y x:=by
  classical
  exact Finset.mem_filter
private theorem qar0 (h : H40 B) {K X T : Finset V}
    (hX : X⊆h.U\K) (hne : X.Nonempty) (hXT : Disjoint X T)
    (hcl : ∀ x∈X,∀ v∈h.U\K,B.Adj x v→ v∈X∨v∈T)
    {y : V} (hy : y∈h.U) (hyX : y∉X) (hyT : y∉T)
    (hyN : y∉extNeighbors B K X) : 4≤ (T∪extNeighbors B K X).card:=by
  by_contra! hcard
  obtain ⟨x,hx⟩:=hne
  have hsub : X⊆h.U\(T∪extNeighbors B K X):=by
    intro v hv
    have hvW:=Finset.mem_sdiff.mp (hX hv)
    exact Finset.mem_sdiff.mpr ⟨hvW.1,fun hm =>
      (Finset.mem_union.mp hm).elim (Finset.disjoint_left.mp hXT hv)
        (fun hm=>hvW.2 (extNeighbors_mem.mp hm).1)⟩
  have hy' : y∈h.U\(T∪extNeighbors B K X):=by simp [hy,hyT,hyN]
  obtain ⟨u,hu,v,hv,hvX,hadj⟩:=qf9 (h.linked _ hcard) hsub hx hy' hyX
  obtain ⟨hvU,hvm⟩:=Finset.mem_sdiff.mp hv
  by_cases hvK : v∈K
  · exact hvm (Finset.mem_union_right _ (extNeighbors_mem.mpr ⟨hvK,u,hu,hadj.symm⟩))
  · exact (hcl u hu v (Finset.mem_sdiff.mpr ⟨hvU,hvK⟩) hadj).elim hvX
      (fun hvT=>hvm (Finset.mem_union_left _ hvT))
private structure Ec0 (h : H40 B) (K : Finset V) : Prop where
  sub : K⊆h.U
  conn : Kc0 (B.induce (K : Set V)) 2
  outer : ∀ v∈h.U\K,(K.filter (B.Adj v)).card≤ 1
private structure ExtBlock (B : SimpleGraph V) (W E : Finset V) (b : V) : Prop where
  gate : b∈E
  sub : E⊆W
  conn : Kc0 (B.induce (E : Set V)) 2
  closed : ∀ v∈E,v≠b→ ∀ w∈W,B.Adj v w→ w∈E
omit [Fintype V] [DecidableEq V] [DecidableRel B.Adj] in
private theorem qar4 {K : Finset V} (hK : Kc0 (B.induce (K : Set V)) 2)
    {a b : V} (ha : a∈K) (hb : b∈K) : Nonempty (Ep0 B a b (K : Set V)):=by
  obtain ⟨p,hp⟩:=qy4 ((qc7 hK).preconnected ⟨a,ha⟩ ⟨b,hb⟩)
  exact ⟨qt9 p hp⟩
omit [Fintype V] [DecidableEq V] in
private theorem qz5 {Q W : Finset V} (hQ : Q⊆W)
    (hcl : ∀ v∈Q,∀ w∈W,B.Adj v w→ w∈Q)
    (hd : ∀ v∈Q,3≤ (Q.filter (B.Adj v)).card)
    {E : Finset (Q : Set V)} {b : (Q : Set V)}
    (hE : Ieb0 (B.induce (Q : Set V)) E b) : ExtBlock B W (qc1 Q E) b.val:=by
  classical
  have hmem : ∀ v∈qc1 Q E,v≠b.val→ ∀ w∈W,B.Adj v w→ w∈qc1 Q E:=by
    intro v hv hvb w hw hadj
    obtain ⟨hvQ,hvE⟩:=extImage_mem.mp hv
    have hwQ:=hcl v hvQ w hw hadj
    exact extImage_mem.mpr ⟨hwQ,hE.2.2.1 ⟨v,hvQ⟩ hvE
      (fun e=>hvb (congrArg Subtype.val e)) ⟨w,hwQ⟩ hadj⟩
  obtain ⟨v,hv,hvb⟩:=Finset.exists_mem_ne (by have:=hE.2.1;omega : 1 < E.card) b
  have hvE:=extImage_coe.mpr hv
  have hcard:=qc3 (B:=B) hvE
  have hle : (Q.filter (B.Adj v.val)).card≤ ((qc1 Q E).filter (B.Adj v.val)).card :=
    Finset.card_le_card fun w hw =>
      let ⟨hwQ,ha⟩:=Finset.mem_filter.mp hw
      Finset.mem_filter.mpr ⟨hmem _ hvE (fun e=>hvb (Subtype.ext e)) w (hQ hwQ) ha,ha⟩
  have hvd:=hd v.val v.property
  have hc : (qc1 Q E).card=E.card:=Finset.card_map _
  exact ⟨extImage_coe.mpr hE.1,fun _ hv=>hQ (qq5 hv),
    qs4 (qac4 Q E) (hE.2.2.2.resolve_left (by omega)),hmem⟩
private theorem qn8 (h : H40 B) {K E : Finset V} (C : Ec0 h K)
    {b : V} (A : ExtBlock B (h.U\K) E b) :
    3≤ (extNeighbors B K (E.erase b)).card:=by
  classical
  by_contra! hn
  have hnK : (extNeighbors B K (E.erase b)).card < K.card:=by
    have hc:=(kConn_induce_iff.mp C.conn).1
    omega
  obtain ⟨y,hy,hyN⟩:=Finset.exists_mem_notMem_of_card_lt_card hnK
  have hE:=(kConn_induce_iff.mp A.conn).1
  obtain ⟨u,hu,hub⟩:=Finset.exists_mem_ne (by omega : 1 < E.card) b
  have hcut:=qar0 h (K:=K) (X:=E.erase b) (T:={b})
    (fun _ hv=>A.sub (Finset.mem_of_mem_erase hv)) ⟨u,Finset.mem_erase.mpr ⟨hub,hu⟩⟩
    (by simp) (fun v hv w hw ha=>by
      have hwE:=A.closed v (Finset.mem_of_mem_erase hv) (Finset.ne_of_mem_erase hv) w hw ha
      by_cases e : w=b <;> simp [hwE,e])
    (C.sub hy) (fun hyE=>(Finset.mem_sdiff.mp (A.sub (Finset.mem_of_mem_erase hyE))).2 hy)
    (fun hyb=>(Finset.mem_sdiff.mp (A.sub A.gate)).2 (Finset.mem_singleton.mp hyb ▸ hy)) hyN
  have hle:=Finset.card_union_le ({b} : Finset V) (extNeighbors B K (E.erase b))
  rw [Finset.card_singleton] at hle
  omega
private theorem qu0 (coy : COY4) (hB : Nf0 B) (h : H40 B)
    {K Q : Finset V} (C : Ec0 h K) (hQ : Q⊆h.U\K)
    (hne : Q.Nonempty) (hlink : Lk0 B Q)
    (hcl : ∀ v∈Q,∀ w∈h.U\K,B.Adj v w→ w∈Q) :
    Kc0 (B.induce (Q : Set V)) 2:=by
  classical
  have hd v (hv : v∈Q):=(qk6 h C.sub (hQ hv) (C.outer v (hQ hv)) (hcl v hv)).1
  obtain ⟨q,hq⟩:=hne
  have hcard : 2 < Fintype.card (Q : Set V):=by
    have:=hd q hq
    have:=qc3 (B:=B) hq
    simpa using (show 2 < Q.card by omega)
  by_contra hno
  obtain ⟨E,b,F,d,hE,hF,hEF,hbF,hdE,p,hp,hps⟩ :=
    qf2 (qd1 ⟨q,hq⟩ hlink) hcard hno
  let X:=qc1 Q E
  let Y:=qc1 Q F
  let W:=h.U\K
  have A : ExtBlock B W X b.val:=qz5 hQ hcl hd hE
  have D : ExtBlock B W Y d.val:=qz5 hQ hcl hd hF
  have hXU : X⊆h.U:=fun _ hv=>(Finset.mem_sdiff.mp (A.sub hv)).1
  have hYU : Y⊆h.U:=fun _ hv=>(Finset.mem_sdiff.mp (D.sub hv)).1
  have hXK : ∀ v∈X,v∉K:=fun _ hv=>(Finset.mem_sdiff.mp (A.sub hv)).2
  have hYK : ∀ v∈Y,v∉K:=fun _ hv=>(Finset.mem_sdiff.mp (D.sub hv)).2
  have hx v (hv : v∈X) (hvb : v≠b.val) :=
    qk6 h C.sub (A.sub hv) (C.outer v (A.sub hv)) (A.closed v hv hvb)
  have hy v (hv : v∈Y) (hvd : v≠d.val) :=
    qk6 h C.sub (D.sub hv) (C.outer v (D.sub hv)) (D.closed v hv hvd)
  have hXY : ∀ v∈X,v∈Y→ v=b.val∧v=d.val:=by
    intro v hv hw
    obtain ⟨hvQ,hvE⟩:=extImage_mem.mp hv
    have hvF:=(extImage_coe (v:=⟨v,hvQ⟩)).mp hw
    by_cases e : (⟨v,hvQ⟩ : (Q : Set V))=b
    · have he:=congrArg Subtype.val e
      have hf : (⟨v,hvQ⟩ : (Q : Set V))=d:=by
        by_contra hne'
        exact hbF (e ▸ Finset.mem_erase.mpr ⟨hne',hvF⟩)
      exact ⟨he,congrArg Subtype.val hf⟩
    · have hmem:=Finset.mem_erase.mpr ⟨e,hvE⟩
      by_cases f : (⟨v,hvQ⟩ : (Q : Set V))=d
      · exact (hdE (f ▸ hmem)).elim
      · exact (Finset.disjoint_left.mp hEF hmem (Finset.mem_erase.mpr ⟨f,hvF⟩)).elim
  let R : Set V:={z|z∈W∧(z∈X→ z=b.val)∧(z∈Y→ z=d.val)}
  let l:=qt9 p hp
  let P : Ep0 B b.val d.val R :=
    ⟨l.walk,l.isPath,by
      intro v hv
      have he : l.walk.support=p.support.map Subtype.val :=
        Walk.support_map (Embedding.induce (G:=B) (Q : Set V)).toHom p
      rw [he,List.mem_map] at hv
      obtain ⟨z,hz,rfl⟩:=hv
      obtain ⟨h₁,h₂⟩:=hps z hz
      refine ⟨hQ z.property,fun hzX=>?_,fun hzY=>?_⟩
      · by_contra e
        exact h₁ (Finset.mem_erase.mpr ⟨fun f=>e (congrArg Subtype.val f),extImage_coe.mp hzX⟩)
      · by_contra e
        exact h₂ (Finset.mem_erase.mpr ⟨fun f=>e (congrArg Subtype.val f),extImage_coe.mp hzY⟩)⟩
  have hN₁:=qn8 h C A
  have hN₂:=qn8 h C D
  obtain ⟨a,ha⟩:=Finset.card_pos.mp (by omega : 0 < (extNeighbors B K (X.erase b.val)).card)
  obtain ⟨e,he,hae⟩:=Finset.exists_mem_ne
    (by omega : 1 < (extNeighbors B K (Y.erase d.val)).card) a
  obtain ⟨haK,u,hu,hau⟩:=extNeighbors_mem.mp ha
  obtain ⟨heK,v,hv,hev⟩:=extNeighbors_mem.mp he
  have huX:=Finset.mem_of_mem_erase hu
  have hvY:=Finset.mem_of_mem_erase hv
  have hub:=Finset.ne_of_mem_erase hu
  have hvd:=Finset.ne_of_mem_erase hv
  have huY : u∉Y:=fun h=>hub (hXY u huX h).1
  have hvX : v∉X:=fun h=>hvd (hXY v h hvY).2
  have huv : u≠v:=fun e=>huY (e ▸ hvY)
  obtain ⟨L⟩:=qar4 C.conn haK heK
  let Z₁:=qh1 h X u b.val
  let Z₂:=qh1 h Y v d.val
  by_cases hZ : 2≤ Z₁.card∧2≤ Z₂.card
  · obtain ⟨cv,hc,S⟩:=qw8 coy h hXU A.gate A.conn hZ.1
      (fun z hz=>let hm:=(qd9 h).mp hz;⟨hm.1,hm.2.2.2⟩) hx
    obtain ⟨cv',hc',T⟩:=qw8 coy h hYU D.gate D.conn hZ.2
      (fun z hz=>let hm:=(qd9 h).mp hz;⟨hm.1,hm.2.2.2⟩) hy
    obtain rfl : cv=cv':=Option.some_injective _ (hc.symm.trans hc')
    have hcv:=h.hc_not_mem cv hc
    let N : Ep0 B cv cv {cv}:=⟨Walk.nil,by simp,by simp⟩
    refine qw7 hB T S N P ?_ ?_ ?_ ?_ ?_ ?_
    · intro z hz hw
      simp only [Set.mem_insert_iff,Finset.mem_coe] at hz hw
      grind
    · intro z _ hz
      exact hz
    · intro z hz hw
      change z∈W∧_ at hw
      simp only [Set.mem_insert_iff,Finset.mem_coe] at hz
      rcases hz with rfl|hz
      · exact (hcv (Finset.mem_sdiff.mp hw.1).1).elim
      · exact hw.2.2 hz
    · intro z hz _
      exact hz
    · intro z hz hw
      change z∈W∧_ at hz
      simp only [Set.mem_insert_iff,Finset.mem_coe] at hw
      rcases hw with rfl|hw
      · exact (hcv (Finset.mem_sdiff.mp hz.1).1).elim
      · exact hz.2.1 hw
    · refine Set.disjoint_left.mpr ?_
      intro z hz hw
      have e : z=cv:=hz
      subst z
      exact hcv (Finset.mem_sdiff.mp hw.1).1
  · have S:=qn7 coy h hXU huX A.gate hub A.conn (fun z hz _ hzb=>hx z hz hzb)
    have T:=qn7 coy h hYU hvY D.gate hvd D.conn (fun z hz _ hzd=>hy z hz hzd)
    have hcU : ∀ z,h.c=some z→ z∉h.U:=h.hc_not_mem
    let M:=L.attach hau.symm hev (hXK u huX) (hYK v hvY) huv
    let M' : Ep0 B v u (insert u (insert v (K : Set V))) :=
      ⟨M.walk.reverse,M.isPath.reverse,by
        intro z hz
        exact M.inside z (by simpa only [Walk.support_reverse,List.mem_reverse] using hz)⟩
    refine qw7 hB T S M' P ?_ ?_ ?_ ?_ ?_ (Set.disjoint_left.mpr ?_)
    all_goals
      intro z
      simp only [Set.mem_union,Set.mem_ofPred_eq,Set.mem_insert_iff,Finset.mem_coe,R]
      have hzW : z∈W→ z∈h.U∧z∉K:=Finset.mem_sdiff.mp
      have hKz : z∈K→ z∈h.U:=fun hz=>C.sub hz
      change ¬ (2≤ Z₁.card∧2≤ Z₂.card) at hZ
      grind
private theorem ql2 (h : H40 B) {K : Finset V} (C : Ec0 h K)
    {x a b : V} (hx : x∈h.U\K) (ha : a∈K) (hb : b∈K)
    (hab : a≠b) (hxa : B.Adj x a) (hxb : B.Adj x b) : False:=by
  have hn:=C.outer x hx
  exact (show ¬ 1 < (K.filter (B.Adj x)).card by omega)
    (Finset.one_lt_card.mpr ⟨a,Finset.mem_filter.mpr ⟨ha,hxa⟩,
      b,Finset.mem_filter.mpr ⟨hb,hxb⟩,hab⟩)
private theorem qac5 (coy : COY4) (hB : Nf0 B) (h : H40 B)
    {K X Y : Finset V} (C : Ec0 h K) (hX : X⊆h.U\K) (hY : Y⊆h.U\K)
    (hXY : Disjoint X Y)
    (hX2 : Kc0 (B.induce (X : Set V)) 2) (hY2 : Kc0 (B.induce (Y : Set V)) 2)
    (hclX : ∀ v∈X,∀ w∈h.U\K,B.Adj v w→ w∈X)
    (hclY : ∀ v∈Y,∀ w∈h.U\K,B.Adj v w→ w∈Y)
    {a₁ a₂ b₁ b₂ : (K : Set V)} {u₁ u₂ v₁ v₂ : V}
    (hu₁ : u₁∈X) (hu₂ : u₂∈X) (hv₁ : v₁∈Y) (hv₂ : v₂∈Y)
    (hua : B.Adj u₁ a₁.val) (hua' : B.Adj a₂.val u₂)
    (hvb : B.Adj b₁.val v₁) (hvb' : B.Adj v₂ b₂.val)
    (ha : a₁≠a₂) (hb : b₁≠b₂)
    {p : (B.induce (K : Set V)).Walk a₁ b₁} {q : (B.induce (K : Set V)).Walk a₂ b₂}
    (hp : p.IsPath) (hq : q.IsPath) (hpq : ∀ z∈p.support,z∉q.support) : False:=by
  have hXU : ∀ z∈X,z∈h.U:=fun _ hz=>(Finset.mem_sdiff.mp (hX hz)).1
  have hYU : ∀ z∈Y,z∈h.U:=fun _ hz=>(Finset.mem_sdiff.mp (hY hz)).1
  have hXK : ∀ z∈X,z∉K:=fun _ hz=>(Finset.mem_sdiff.mp (hX hz)).2
  have hYK : ∀ z∈Y,z∉K:=fun _ hz=>(Finset.mem_sdiff.mp (hY hz)).2
  have hxu v (hv : v∈X) :=
    qk6 h C.sub (hX hv) (C.outer v (hX hv)) (hclX v hv)
  have hyv v (hv : v∈Y) :=
    qk6 h C.sub (hY hv) (C.outer v (hY hv)) (hclY v hv)
  have hu : u₁≠u₂:=by
    rintro rfl
    exact ql2 h C (hX hu₁) a₁.property a₂.property (fun e=>ha (Subtype.ext e))
      hua hua'.symm
  have hv : v₁≠v₂:=by
    rintro rfl
    exact ql2 h C (hY hv₁) b₁.property b₂.property (fun e=>hb (Subtype.ext e))
      hvb.symm hvb'
  have hxyn : ∀ z∈X,z∉Y:=Finset.disjoint_left.mp hXY
  have h₁ : u₁≠v₁:=fun e=>hxyn u₁ hu₁ (e ▸ hv₁)
  have h₂ : u₂≠v₂:=fun e=>hxyn u₂ hu₂ (e ▸ hv₂)
  have hcU : ∀ z,h.c=some z→ z∉h.U:=h.hc_not_mem
  let Z₁:=qh1 h X u₁ u₂
  let Z₂:=qh1 h Y v₁ v₂
  by_cases hZ : 2≤ Z₁.card∧2≤ Z₂.card
  · obtain ⟨cv,hc,S⟩:=qw8 coy h hXU hu₁ hX2 hZ.1
      (fun z hz=>let hm:=(qd9 h).mp hz;⟨hm.1,hm.2.2.2⟩)
      (fun v hv _=>hxu v hv)
    obtain ⟨cv',hc',T⟩:=qw8 coy h hYU hv₁ hY2 hZ.2
      (fun z hz=>let hm:=(qd9 h).mp hz;⟨hm.1,hm.2.2.2⟩)
      (fun v hv _=>hyv v hv)
    obtain rfl : cv=cv':=Option.some_injective _ (hc.symm.trans hc')
    let N : Ep0 B cv cv {cv}:=⟨Walk.nil,by simp,by simp⟩
    let P:=((qt9 p hp).attach hua hvb (hXK u₁ hu₁) (hYK v₁ hv₁) h₁).reverse
    refine qw7 hB S T N P ?_ ?_ ?_ ?_ ?_ (Set.disjoint_left.mpr ?_)
    all_goals
      intro z
      simp only [Set.mem_insert_iff,Set.mem_singleton_iff,Finset.mem_coe]
      have hKz : z∈K→ z∈h.U:=fun hz=>C.sub hz
      grind
  · have S:=qn7 coy h hXU hu₁ hu₂ hu hX2 (fun v hv _ _=>hxu v hv)
    have T:=qn7 coy h hYU hv₁ hv₂ hv hY2 (fun v hv _ _=>hyv v hv)
    let A : Set V:={z|∃ w∈p.support,w.val=z}
    let D : Set V:={z|∃ w∈q.support,w.val=z}
    have hAK : A⊆(K : Set V):=by rintro _ ⟨w,-,rfl⟩;exact w.property
    have hDK : D⊆(K : Set V):=by rintro _ ⟨w,-,rfl⟩;exact w.property
    have hAD : ∀ z∈A,z∉D:=by
      rintro _ ⟨w,hw,rfl⟩ ⟨v,hv,e⟩
      exact hpq w hw ((Subtype.ext e : v=w) ▸ hv)
    let P:=(qaf9 p hp).attach hua hvb
      (fun hz=>hXK u₁ hu₁ (hAK hz)) (fun hz=>hYK v₁ hv₁ (hAK hz)) h₁
    let Q:=((qaf9 q hq).attach hua'.symm hvb'.symm
      (fun hz=>hXK u₂ hu₂ (hDK hz)) (fun hz=>hYK v₂ hv₂ (hDK hz)) h₂).reverse
    refine qw7 hB S T P Q ?_ ?_ ?_ ?_ ?_ (Set.disjoint_left.mpr ?_)
    all_goals
      intro z
      simp only [Set.mem_union,Set.mem_insert_iff,Finset.mem_coe]
      have hAz : z∈A→ z∈K:=fun hz=>hAK hz
      have hDz : z∈D→ z∈K:=fun hz=>hDK hz
      have hKz : z∈K→ z∈h.U:=fun hz=>C.sub hz
      change ¬ (2≤ Z₁.card∧2≤ Z₂.card) at hZ
      clear*- hxyn hXK hYK hXU hYU hcU hAz hDz hKz hAD hZ hu hv hu₁ hu₂ hv₁ hv₂
      grind
private theorem qaj0 (coy : COY4) (hB : Nf0 B) (h : H40 B)
    {K : Finset V} (C : Ec0 h K) : Lk0 B (h.U\K):=by
  classical
  let W:=h.U\K
  by_contra hn
  change ¬ Lk0 B W at hn
  unfold Lk0 at hn
  push Not at hn
  obtain ⟨x,hx,y,hy,hxy⟩:=hn
  obtain ⟨X,hX,hXR,hXL,hXC⟩:=qi7 (B:=B) W hx
  obtain ⟨Y,hY,hYR,hYL,hYC⟩:=qi7 (B:=B) W hy
  have hxX:=(hXR x).mpr (Rc0.refl hx)
  have hyY:=(hYR y).mpr (Rc0.refl hy)
  have hXY : Disjoint X Y:=Finset.disjoint_left.mpr fun z hzX hzY =>
    hxy (((hXR z).mp hzX).trans ((hYR z).mp hzY).symm)
  have hX2:=qu0 coy hB h C hX ⟨x,hxX⟩ hXL hXC
  have hY2:=qu0 coy hB h C hY ⟨y,hyY⟩ hYL hYC
  have hN {Q : Finset V} (hQ : Q⊆W) (hQne : Q.Nonempty)
      (hQC : ∀ v∈Q,∀ w∈W,B.Adj v w→ w∈Q) {z : V} (hz : z∈W) (hzQ : z∉Q) :
      4≤ (extNeighbors B K Q).card:=by
    have hz':=Finset.mem_sdiff.mp hz
    simpa only [Finset.empty_union] using
      qar0 h (T:=∅) hQ hQne (by simp) (fun v hv w hw ha=>Or.inl (hQC v hv w hw ha))
        hz'.1 hzQ (Finset.notMem_empty z) (fun hn=>hz'.2 (extNeighbors_mem.mp hn).1)
  have hNX:=hN hX ⟨x,hxX⟩ hXC hy (fun hm=>Finset.disjoint_left.mp hXY hm hyY)
  have hNY:=hN hY ⟨y,hyY⟩ hYC hx (Finset.disjoint_left.mp hXY hxX)
  obtain ⟨a₁,ha₁,a₂,ha₂,ha⟩:=Finset.one_lt_card.mp
    (by omega : 1 < (extNeighbors B K X).card)
  have hrem : 1 < (extNeighbors B K Y\{a₁,a₂}).card:=by
    rw [Finset.card_sdiff]
    have:=(Finset.card_le_card
      (Finset.inter_subset_left : {a₁,a₂}∩extNeighbors B K Y⊆{a₁,a₂})).trans
      Finset.card_le_two
    omega
  obtain ⟨b₁,hb₁,b₂,hb₂,hb⟩:=Finset.one_lt_card.mp hrem
  obtain ⟨ha₁K,u₁,hu₁,hua⟩:=extNeighbors_mem.mp ha₁
  obtain ⟨ha₂K,u₂,hu₂,hua'⟩:=extNeighbors_mem.mp ha₂
  obtain ⟨hb₁K,v₁,hv₁,hvb⟩:=extNeighbors_mem.mp (Finset.mem_sdiff.mp hb₁).1
  obtain ⟨hb₂K,v₂,hv₂,hvb'⟩:=extNeighbors_mem.mp (Finset.mem_sdiff.mp hb₂).1
  have ha' : (⟨a₁,ha₁K⟩ : (K : Set V))≠⟨a₂,ha₂K⟩:=fun e=>ha (congrArg Subtype.val e)
  have hb' : (⟨b₁,hb₁K⟩ : (K : Set V))≠⟨b₂,hb₂K⟩:=fun e=>hb (congrArg Subtype.val e)
  rcases qy1 C.conn ha' hb' with ⟨p,q,hp,hq,hpq⟩|⟨p,q,hp,hq,hpq⟩
  · exact qac5 coy hB h C hX hY hXY hX2 hY2 hXC hYC hu₁ hu₂ hv₁ hv₂
      hua.symm hua' hvb hvb'.symm ha' hb' hp hq hpq
  · exact qac5 coy hB h C hX hY hXY hX2 hY2 hXC hYC hu₁ hu₂ hv₂ hv₁
      hua.symm hua' hvb' hvb.symm ha' hb'.symm hp hq hpq
end Host
theorem qag2 (coy : COY4) {V : Type} [Fintype V] [DecidableEq V]
    {B : SimpleGraph V} [DecidableRel B.Adj] (hB : Nf0 B) (h : H40 B)
    (h3 : 3∉(B.induce (h.U : Set V)).cycleLengths)
    (h4 : 4∉(B.induce (h.U : Set V)).cycleLengths) : False:=by
  classical
  let J:=B.induce (h.U : Set V)
  have hJ:=noFive_iff_cycleLengths.mp (qk1 (h.U : Set V) hB)
  have hcyc : ∀ n∈({3,4,5,10} : Finset ℕ),n∉J.cycleLengths:=by
    intro n hn
    simp only [Finset.mem_insert,Finset.mem_singleton] at hn
    rcases hn with rfl|rfl|rfl|rfl
    · exact h3
    · exact h4
    · exact fun hm=>hJ 5 hm (by decide)
    · exact fun hm=>hJ 10 hm (by decide)
  obtain ⟨S,hS,hconn,hd,ho,x,y,hxy,p,hp,hmod⟩ :=
    Dt.thetaCore_H2 (h.U : Set V) J h.hdeg4
      (fun T ht=>h.hconn4.2 T (by omega)) hcyc
  let K:=qc1 h.U S
  let W:=h.U\K
  let e:=qac4 (B:=B) h.U S
  have hKS : K⊆h.U:=qq5
  have hK2 : Kc0 (B.induce (K : Set V)) 2:=by
    apply qs4 e
    refine qg8 S hS fun v _=>?_
    apply qg3
    have hv:=hconn {v} (by simp)
    have he : (S : Set (h.U : Set V))\(({v} : Finset (h.U : Set V)) : Set (h.U : Set V)) =
        (S.erase v : Set (h.U : Set V)):=by ext w;simp [and_comm]
    rwa [he] at hv
  have hinner : ∀ v∈K,(K.filter (B.Adj v)).card≤ 3:=by
    intro v hv
    obtain ⟨hvU,hvS⟩:=extImage_mem.mp hv
    exact (qo8 (B:=B) S ⟨v,hvU⟩).symm ▸ hd ⟨v,hvU⟩ hvS
  have houter : ∀ v∈W,(K.filter (B.Adj v)).card≤ 1:=by
    intro v hv
    obtain ⟨hvU,hvK⟩:=Finset.mem_sdiff.mp hv
    exact (qo8 (B:=B) S ⟨v,hvU⟩).symm ▸
      ho ⟨v,hvU⟩ (fun hm=>hvK (extImage_coe.mpr hm))
  have C : Ec0 h K:=⟨hKS,hK2,houter⟩
  have hAttach : ∀ v∈K,∃ w∈W,B.Adj v w:=by
    intro v hv
    have hdeg:=h.hdeg4 ⟨v,hKS hv⟩
    rw [qa5] at hdeg
    change 4≤ (h.U.filter (B.Adj v)).card at hdeg
    have hs:=qs7 (B:=B) hKS v
    have:=hinner v hv
    have hpos : 0 < ((h.U\K).filter (B.Adj v)).card:=by omega
    exact (Finset.card_pos.mp hpos).imp (fun _ hw=>Finset.mem_filter.mp hw)
  let a:=(e x).val
  let b:=(e y).val
  have ha : a∈K:=(e x).property
  have hb : b∈K:=(e y).property
  have hab : a≠b:=fun hn=>hxy (e.injective (Subtype.ext hn))
  obtain ⟨u,hu,hau⟩:=hAttach a ha
  obtain ⟨v,hv,hbv⟩:=hAttach b hb
  have huv : u≠v:=by
    rintro rfl
    exact ql2 h C hu ha hb hab hau.symm hbv.symm
  have hW2:=qu0 coy hB h C (subset_rfl : W⊆W) ⟨u,hu⟩
    (qaj0 coy hB h C) (fun _ _ _ hw _=>hw)
  have hWsub : W⊆h.U:=fun _ hw=>(Finset.mem_sdiff.mp hw).1
  let T : Set V:=(W : Set V)∪{z|2≤ (qh1 h W u v).card∧h.c=some z}
  have hP : AdmH B u v 3 T :=
    qn7 coy h hWsub hu hv huv hW2
      (fun w hw _ _=>qk6 h hKS hw (houter w hw) (fun _ hm _=>hm))
  obtain ⟨s,d,hs,hd,hP⟩:=hP
  choose q hq hlen hsup using hP
  have hTK : ∀ z∈T,z∉K:=by
    intro z hz
    rcases hz with hz|⟨_,hc⟩
    · exact (Finset.mem_sdiff.mp hz).2
    · exact fun hzK=>h.hc_not_mem z hc (hKS hzK)
  let G (i : Fin 3) : Ep0 B a b (insert a (insert b T)) :=
    (Ep0.mk (q i) (hq i) (hsup i)).attach hau hbv.symm
      (fun hm=>hTK a hm ha) (fun hm=>hTK b hm hb) hab
  let F (i : Fin 3) : Ep0 B a b (K : Set V) :=
    qt9 ((p i).map e.toHom) (qb8 _ e.injective (hp i))
  have hF i : (F i).walk.length=(p i).length:=by
    exact (Walk.length_map (Embedding.induce (G:=B) (K : Set V)).toHom _).trans
      (Walk.length_map e.toHom _)
  have hG i : (G i).walk.length=s+i.val*d+2:=by
    simp only [G,Ep0.attach,Walk.length_concat,Walk.length_cons,hlen]
  refine qe4 hB (fun i=>(F i).walk) (fun j=>(G j).walk)
    (fun i=>(F i).isPath) (fun j=>(G j).isPath) ?_ ?_ ?_ ?_
  · intro i j z hz hw
    rcases (G j).inside z hw with hza|hzb|hzT
    · exact Or.inl hza
    · exact Or.inr hzb
    · exact (hTK z hzT ((F i).inside z hz)).elim
  · intro i j
    rw [hG]
    omega
  · simpa only [hF] using hmod
  · simpa only [hG] using qg4 hd s 2
end DeanK5
end M6
section M7
namespace DeanK5
theorem deanFromCOY (coy : COY4) :
    type_of% @Arxiv.«2605.02731».dean_conjecture.variants.five:=by
  intro V _ _ G _ hmin
  by_contra hno
  have hG : Nf0 G:=noFive_iff_cycleLengths.mpr fun m hm hd=>hno ⟨m,hm,hd⟩
  obtain ⟨E,hE,⟨h⟩⟩:=qh6 coy G hmin hG
  have h3:=qan2 coy hE h
  have h4:=qaq2 coy hE h h3
  exact qag2 coy hE h h3 h4
end DeanK5
end M7
section M8
namespace DeanK5
open SimpleGraph
def Ch0 {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x y : V) (z : Option V) (q : ℕ) : Prop :=
  1≤ q∧Rt0 G x y ∧
  (∃ v : V,v≠x∧v≠y∧z≠some v) ∧
  (∀ v : V,v≠x→ v≠y→ z≠some v→ q+1≤ G.degree v)
def Cb0 (N : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (x y : V) (z : Option V) (q : ℕ),
    q≤ 4→ Fintype.card V+G.edgeFinset.card < N →
    Ch0 G x y z q→ Adm0 G x y q
def Ca0 (q N : ℕ) : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) (z : Option V),Fintype.card V+G.edgeFinset.card < N →
    Ch0 G x y z q→ Adm0 G x y q
theorem Ca0.mono {q N M : ℕ} (h : Ca0 q N) (hM : M≤ N) : Ca0 q M:=by
  intro V _ _ G _ x y z hlt hH
  exact h V G x y z (by omega) hH
theorem Cb0.toAt {N q : ℕ} (h : Cb0 N) (hq : q≤ 4) : Ca0 q N:=by
  intro V _ _ G _ x y z hlt hH
  exact h V G x y z q hq hlt hH
variable {V W : Type}
theorem qu8 [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
    {x y : V} {z : Option V} {q : ℕ} (h : Ch0 G x y z q) : Ch0 G y x z q :=
  ⟨h.1,qo4 h.2.1,h.2.2.1.imp fun _ hv=>⟨hv.2.1,hv.1,hv.2.2⟩,
    fun v h1 h2 h3=>h.2.2.2 v h2 h1 h3⟩
namespace Cb
section Generic
variable {G : SimpleGraph V}
theorem qh0 {H : SimpleGraph W} [Fintype G.edgeSet] [Fintype H.edgeSet]
    (f : W→ V) (hf : Function.Injective f) (hadj : ∀ a b,H.Adj a b→ G.Adj (f a) (f b)) :
    H.edgeFinset.card≤ G.edgeFinset.card:=by
  refine Finset.card_le_card_of_injOn (Sym2.map f) (fun e he=>?_)
    (Sym2.map.injective hf).injOn
  revert he
  refine Sym2.ind (fun a b=>?_) e
  intro he
  simp only [Finset.mem_coe,mem_edgeFinset,mem_edgeSet] at he ⊢
  exact hadj a b he
theorem card_edge_le_of_proj {H : SimpleGraph W} [Fintype G.edgeSet] [Fintype H.edgeSet]
    (π : V→ W) (h : ∀ a b,H.Adj a b→ ∃ u v,G.Adj u v∧π u=a∧π v=b) :
    H.edgeFinset.card≤ G.edgeFinset.card:=by
  classical
  refine le_trans (Finset.card_le_card fun e he=>?_)
    (Finset.card_image_le (s:=G.edgeFinset) (f:=Sym2.map π))
  revert he
  refine Sym2.ind (fun a b=>?_) e
  intro he
  rw [mem_edgeFinset,mem_edgeSet] at he
  obtain ⟨u,v,huv,rfl,rfl⟩:=h a b he
  exact Finset.mem_image.mpr ⟨s(u,v),by rwa [mem_edgeFinset,mem_edgeSet],rfl⟩
theorem qj6 {H : SimpleGraph W} {v : V} {w : W} [Fintype (G.neighborSet v)]
    [Fintype (H.neighborSet w)] (g : V→ W) (hg : ∀ u,G.Adj v u→ H.Adj w (g u))
    (hinj : ∀ u₁ u₂,G.Adj v u₁→ G.Adj v u₂→ g u₁=g u₂→ u₁=u₂) :
    G.degree v≤ H.degree w:=by
  rw [← card_neighborFinset_eq_degree,← card_neighborFinset_eq_degree]
  refine Finset.card_le_card_of_injOn g (fun u hu=>?_) (fun u₁ h₁ u₂ h₂ h=>?_)
  · simp only [Finset.mem_coe,mem_neighborFinset] at hu ⊢
    exact hg u hu
  · simp only [Finset.mem_coe,mem_neighborFinset] at h₁ h₂
    exact hinj u₁ u₂ h₁ h₂ h
theorem qo9 [DecidableEq V] (s : Finset V) {u : V} (hu : u∈s)
    (hcl : ∀ w,G.Adj u w→ w∈s) [Fintype (G.neighborSet u)]
    [Fintype ((G.induce (s : Set V)).neighborSet ⟨u,hu⟩)] :
    G.degree u≤ (G.induce (s : Set V)).degree ⟨u,hu⟩ :=
  qj6 (fun w=>if h : w∈s then ⟨w,h⟩ else ⟨u,hu⟩)
    (fun w hw=>by simp only [dif_pos (hcl w hw)];exact hw)
    (fun w₁ w₂ h₁ h₂ h=>by
      simp only [dif_pos (hcl w₁ h₁),dif_pos (hcl w₂ h₂),Subtype.mk.injEq] at h
      exact h)
theorem qs9 {a b v : V} [Fintype (G.neighborSet v)]
    [Fintype ((de0 G a b).neighborSet v)] (hva : v≠a) (hvb : v≠b) :
    G.degree v≤ (de0 G a b).degree v :=
  qj6 id (fun w hw=>by
    simp only [de0,sdiff_adj,edge_adj,id]
    refine ⟨hw,?_⟩
    rintro ⟨⟨h,-⟩|⟨h,-⟩,-⟩
    exacts [hva h,hvb h]) (fun _ _ _ _ h=>h)
theorem qj8 {a b : V} [Fintype G.edgeSet] [Fintype (de0 G a b).edgeSet]
    (h : G.Adj a b) : (de0 G a b).edgeFinset.card < G.edgeFinset.card:=by
  refine Finset.card_lt_card (edgeFinset_ssubset_edgeFinset.mpr
    (lt_of_le_of_ne sdiff_le fun he=>?_))
  have h' : (de0 G a b).Adj a b:=by rw [he];exact h
  simp [de0,edge_adj,h.ne] at h'
theorem qaa6 [Fintype V] [DecidableEq V] {H : SimpleGraph V} (hle : G≤ H)
    {k : ℕ} (h : Kc0 G k) : Kc0 H k:=by
  obtain ⟨hk,hl⟩:=kConn_iff_linked.mp h
  exact kConn_iff_linked.mpr ⟨hk,fun S hS=>(hl S hS).mono_graph hle⟩
theorem card_lt_of_notMem [Fintype V] {s : Finset V} {a : V} (h : a∉s) :
    s.card < Fintype.card V:=by
  rw [← Finset.card_univ]
  exact Finset.card_lt_card ⟨Finset.subset_univ _,fun h'=>h (h' (Finset.mem_univ a))⟩
theorem exists_pull {ι : W→ V} (hι : Function.Injective ι) (z : Option V) :
    ∃ z' : Option W,∀ w,z'=some w↔z=some (ι w):=by
  by_cases h : ∃ w,z=some (ι w)
  · obtain ⟨w₀,hw₀⟩:=h
    refine ⟨some w₀,fun w=>⟨fun h'=>?_,fun h'=>?_⟩⟩
    · rw [Option.some.inj h'] at hw₀
      exact hw₀
    · rw [hw₀,Option.some.injEq] at h'
      rw [hι h']
  · exact ⟨none,fun w=>⟨fun h'=>absurd h' (by simp),fun h'=>absurd ⟨w,h'⟩ h⟩⟩
theorem map_some_iff {o : Option W} {a : W} : o.map some=some (some a)↔o=some a:=by
  cases o <;> simp
theorem qaj1 [Fintype V] [DecidableEq V] (z : Option V) (a b c : V)
    (h : 4 < Fintype.card V) : ∃ v,v≠a∧v≠b∧v≠c∧z≠some v:=by
  have key : ∀ s : Finset V,s.card≤ 4→ ∃ v,v∉s:=fun s hs=>by
    obtain ⟨v,-,hv⟩:=Finset.exists_mem_notMem_of_card_lt_card (s:=s) (t:=Finset.univ)
      (by rw [Finset.card_univ];omega)
    exact ⟨v,hv⟩
  cases z with
  | none =>
    obtain ⟨v,hv⟩:=key {a,b,c} (Finset.card_le_three.trans (by norm_num))
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hv
    exact ⟨v,hv.1,hv.2.1,hv.2.2,by simp⟩
  | some w =>
    obtain ⟨v,hv⟩:=key {a,b,c,w} Finset.card_le_four
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hv
    exact ⟨v,hv.1,hv.2.1,hv.2.2.1,fun h=>hv.2.2.2 (Option.some.inj h).symm⟩
theorem qr5 {a b u w : V} (h : (G ⊔ edge a b).Adj u w)
    (hn : ¬ (u=a∧w=b∨u=b∧w=a)) : G.Adj u w:=by
  rw [sup_adj,edge_adj] at h
  exact h.resolve_right fun h'=>hn h'.1
theorem exists_adj_ne [Fintype V] [DecidableEq V] (hK : Kc0 G 2) (u b : V) :
    ∃ w,G.Adj u w∧w≠b:=by
  classical
  have h:=qe8 hK u
  rw [← card_neighborFinset_eq_degree] at h
  obtain ⟨w,hw,hwb⟩:=Finset.exists_mem_ne (by omega : 1 < (G.neighborFinset u).card) b
  exact ⟨w,(mem_neighborFinset _ _ _).mp hw,hwb⟩
theorem qr3 [Fintype V] [DecidableEq V] (hK : Kc0 G 2) {w r u : V} {R : Finset V}
    (hr : r∈R) (hu : u∉R) (hrw : r≠w) (huw : u≠w) :
    ∃ c∈R,∃ d,d∉R∧d≠w∧G.Adj c d:=by
  obtain ⟨p,hp⟩:=(kConn_two_iff.mp hK).2 w r (by simp [hrw]) u (by simp [huw])
  obtain ⟨d,hd,h1,h2⟩:=p.exists_boundary_dart (R : Set V) hr hu
  exact ⟨d.fst,h1,d.snd,h2,
    Finset.ne_of_mem_erase (hp _ (p.dart_snd_mem_support_of_mem_darts hd)),d.adj⟩
theorem qal1 (t : Finset V) {u : V} (hu : u∈t) :
    ∃ R⊆t,u∈R∧(∀ a∈R,∀ d,G.Adj a d→ d∈R∨d∉t)∧Lk0 G R:=by
  obtain ⟨R,hRt,huR,hcl,hr⟩:=qg2 (G:=G) t hu
  have hcl' : ∀ a∈R,∀ d,G.Adj a d→ d∈R∨d∉t:=fun a ha d hd=>by
    by_cases hdt : d∈t
    · exact Or.inl (hcl a ha d hdt hd)
    · exact Or.inr hdt
  refine ⟨R,hRt,huR,hcl',qa4 u fun v hv=>?_⟩
  obtain ⟨p,hp⟩:=hr v hv
  exact ⟨p,qb9 (D:=(·∉t)) hcl' p huR fun a ha h=>h (hp a ha)⟩
theorem qe6 [DecidableEq V] {D : Finset V} {t c : V} (hl : Lk0 G D) (hc : c∈D)
    (h : G.Adj t c) : Lk0 G (insert t D):=by
  refine qa4 t fun v hv=>?_
  rcases Finset.mem_insert.mp hv with rfl|hv
  · exact Rc0.refl (Finset.mem_insert_self _ _)
  · exact (Rc0.adj (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hc) h).trans
      ((hl c hc v hv).mono (Finset.subset_insert _ _))
theorem adj_of_linked {C : Finset V} {y c : V} (hl : Lk0 G C) (hy : y∈C) (hc : c∈C)
    (hcy : c≠y) : ∃ w∈C,G.Adj y w:=by
  obtain ⟨p,hp⟩:=hl y hy c hc
  cases p with
  | nil=>exact absurd rfl hcy
  | cons h p=>exact ⟨_,hp _ (by simp),h⟩
theorem qah9 {x y : V} {P₁ P₂ : G.Walk x y} (h₁ : P₁.IsPath) (h₂ : P₂.IsPath)
    (hl : 2≤ P₁.length) (hd : P₂.length=P₁.length+1∨P₂.length=P₁.length+2) :
    Adm0 G x y 2:=by
  refine ⟨P₁.length,P₂.length - P₁.length,hl,by omega,fun i=>?_⟩
  rcases qa8 i with rfl|rfl
  · exact ⟨P₁,h₁,by rw [show ((0 : Fin 2) : ℕ)=0 from rfl];omega⟩
  · exact ⟨P₂,h₂,by rw [show ((1 : Fin 2) : ℕ)=1 from rfl];omega⟩
end Generic
section Calls
variable {G : SimpleGraph V}
def qan7 (G : SimpleGraph V) (s : Finset V) (x y : V) (q : ℕ) : Prop :=
  ∃ a d : ℕ,2≤ a∧(d=1∨d=2) ∧
    ∀ i : Fin q,∃ p : G.Walk x y,p.IsPath∧p.length=a+i.val*d∧∀ v∈p.support,v∈s
theorem qm2 {s : Finset V} {x y : V} {q : ℕ} (h : qan7 G s x y q) :
    Adm0 G x y q:=by
  obtain ⟨a,d,ha,hd,hP⟩:=h
  exact ⟨a,d,ha,hd,fun i=>(hP i).elim fun p hp=>⟨p,hp.1,hp.2.1⟩⟩
theorem qr4 {s : Finset V} {x r y : V} {q : ℕ} (h : qan7 G s x r q) (Q : G.Walk r y)
    (hQ : Q.IsPath) (hQs : ∀ a∈Q.support,a∈s→ a=r) : Adm0 G x y q:=by
  obtain ⟨a,d,ha,hd,hP⟩:=h
  refine ⟨a+Q.length,d,by omega,hd,fun i=>?_⟩
  obtain ⟨p,hp,hl,hs⟩:=hP i
  obtain ⟨hpath,hlen,-⟩:=qa3 hp hQ fun b hb hb'=>hQs b hb' (hs b hb)
  exact ⟨p.append Q,hpath,by rw [hlen,hl];ring⟩
theorem induce_call {q N : ℕ} (ih : Ca0 q N) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (s : Finset V) {x r : V} (hx : x∈s) (hr : r∈s) (z : Option V) (hq : 1≤ q)
    (hR : Rt0 (G.induce (s : Set V)) ⟨x,hx⟩ ⟨r,hr⟩) (hN : s.card+G.edgeFinset.card < N)
    (hdeg : ∀ u∈s,u≠x→ u≠r→ z≠some u →
      q+1≤ G.degree u∧∀ w,G.Adj u w→ w∈s)
    (hwit : ∃ u∈s,u≠x∧u≠r∧z≠some u) : qan7 G s x r q:=by
  classical
  obtain ⟨z',hz'⟩:=exists_pull (W:=↥(s : Set V)) Subtype.val_injective z
  have hmeas : Fintype.card (s : Set V)+(G.induce (s : Set V)).edgeFinset.card < N:=by
    have h1 : Fintype.card (s : Set V)=s.card:=by simp
    have h2:=qh0 (G:=G) (H:=G.induce (s : Set V)) Subtype.val
      Subtype.val_injective fun _ _ h=>h
    omega
  have hwit' : ∃ u : (s : Set V),u≠⟨x,hx⟩∧u≠⟨r,hr⟩∧z'≠some u:=by
    obtain ⟨u,hu,hux,hur,huz⟩:=hwit
    exact ⟨⟨u,hu⟩,fun h=>hux (congrArg Subtype.val h),fun h=>hur (congrArg Subtype.val h),
      fun h=>huz ((hz' _).mp h)⟩
  have hdeg' : ∀ u : (s : Set V),u≠⟨x,hx⟩→ u≠⟨r,hr⟩→ z'≠some u →
      q+1≤ (G.induce (s : Set V)).degree u:=by
    intro u hux hur huz
    obtain ⟨hd,hcl⟩:=hdeg u.1 u.2 (fun h=>hux (Subtype.ext h)) (fun h=>hur (Subtype.ext h))
      (fun h=>huz ((hz' u).mpr h))
    exact hd.trans (qo9 s u.2 hcl)
  obtain ⟨a,d,ha,hd,hP⟩ :=
    ih _ (G.induce (s : Set V)) ⟨x,hx⟩ ⟨r,hr⟩ z' hmeas ⟨hq,hR,hwit',hdeg'⟩
  refine ⟨a,d,ha,hd,fun i=>?_⟩
  obtain ⟨p,hp,hl⟩:=hP i
  obtain ⟨p',hp',hl',-,hs⟩:=qd3 (G:=G) (s : Set V) hp
  exact ⟨p',hp',hl'.trans hl,fun v hv=>hs v hv⟩
theorem rooted_adjoin [Fintype V] [DecidableEq V] {A : Finset V} (Z : Finset (A : Set V)) {r : V}
    (hr : r∈A) (hcard : 2≤ A.card) (hA : Lk0 G A)
    (hcut : ∀ w∈A,∀ v∈A.erase w,∃ c∈A.erase w,
      (c=r∨∃ h : c∈A,(⟨c,h⟩ : (A : Set V))∈Z)∧Rc0 G (A.erase w) c v) :
    Rt0 (av0 (G.induce (A : Set V)) Z) none (some ⟨r,hr⟩):=by
  classical
  obtain ⟨g,hg⟩ : ∃ g : V→ Option (A : Set V),∀ w (h : w∈A),g w=some ⟨w,h⟩ :=
    ⟨fun w=>if h : w∈A then some ⟨w,h⟩ else none,fun w h=>dif_pos h⟩
  have hproj : ∀ (t : Finset V) (T : Finset (Option (A : Set V))) (u v : V),t⊆A →
      (∀ a∈t,g a∈T)→ Rc0 G t u v →
      Rc0 (av0 (G.induce (A : Set V)) Z ⊔ edge none (some ⟨r,hr⟩)) T (g u) (g v) :=
    fun t T u v htA hT h=>h.proj g (fun a ha b hb hab=>Or.inr (Or.inl (by
      rw [hg a (htA ha),hg b (htA hb)];exact hab))) hT
  have hcA : Fintype.card (A : Set V)=A.card:=by simp
  refine ⟨by simp,kConn_two_iff.mpr ⟨by rw [Fintype.card_option,hcA];omega,fun w=>?_⟩⟩
  cases w with
  | none =>
    refine qa4 (some ⟨r,hr⟩) fun v hv=>?_
    obtain ⟨v,rfl⟩:=Option.ne_none_iff_exists'.mp (Finset.ne_of_mem_erase hv)
    have h:=hproj A (Finset.univ.erase none) r v.1 subset_rfl (fun a ha=>by simp [hg a ha])
      (hA r hr v.1 v.2)
    rwa [hg r hr,hg v.1 v.2] at h
  | some w =>
    refine qa4 none fun v hv=>?_
    cases v with
    | none=>exact Rc0.refl (by simp)
    | some v =>
      have hvw : v.1∈A.erase w.1:=Finset.mem_erase.mpr
        ⟨fun h=>Finset.ne_of_mem_erase hv (congrArg some (Subtype.ext h)),v.2⟩
      obtain ⟨c,hc,hcz,hcv⟩:=hcut w.1 w.2 v.1 hvw
      have hcA:=Finset.mem_of_mem_erase hc
      have hT : ∀ a∈A.erase w.1,g a∈Finset.univ.erase (some w):=fun a ha=>by
        rw [hg a (Finset.mem_of_mem_erase ha)]
        refine Finset.mem_erase.mpr ⟨fun h=>Finset.ne_of_mem_erase ha ?_,Finset.mem_univ _⟩
        exact congrArg Subtype.val (Option.some.inj h)
      have h2:=hproj _ _ c v.1 (Finset.erase_subset _ _) hT hcv
      rw [hg v.1 v.2] at h2
      have hcT:=hT c hc
      rw [hg c hcA] at h2 hcT
      refine Rc0.trans (Rc0.adj (by simp) hcT ?_) h2
      rcases hcz with hcr|⟨h,hcZ⟩
      · exact Or.inr (by simp [edge_adj,hcr])
      · exact Or.inl hcZ
theorem qae0 {q N : ℕ} (ih : Ca0 q N) [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (A K : Finset V) {r : V} (hr : r∈A) (z : Option V) (hq : 1≤ q)
    (hKA : ∀ k∈K,k∉A) (hA : Lk0 G A) (hcard : 2≤ A.card)
    (hcut : ∀ w∈A,∀ R⊆A.erase w,R.Nonempty →
      (∀ c∈R,∀ d∈A.erase w,G.Adj c d→ d∈R)→ ∃ c∈R,c=r∨∃ k∈K,G.Adj c k)
    (hN : A.card+1+G.edgeFinset.card < N)
    (hdeg : ∀ u∈A,u≠r→ z≠some u→ q+1≤ G.degree u ∧
      (∀ w,G.Adj u w→ w∈A∨w∈K)∧∀ k₁∈K,∀ k₂∈K,G.Adj u k₁→ G.Adj u k₂→ k₁=k₂)
    (hwit : ∃ u∈A,u≠r∧z≠some u) :
    ∃ a d : ℕ,2≤ a∧(d=1∨d=2)∧∀ i : Fin q,∃ k∈K,∃ p : G.Walk k r,
      p.IsPath∧p.length=a+i.val*d∧∀ v∈p.support.tail,v∈A:=by
  classical
  obtain ⟨Z,hZ⟩ : ∃ Z : Finset (A : Set V),∀ a,a∈Z↔∃ k∈K,G.Adj a.1 k :=
    ⟨Finset.univ.filter fun a=>∃ k∈K,G.Adj a.1 k,fun a=>by simp⟩
  obtain ⟨g,hg,hg'⟩ : ∃ g : V→ Option (A : Set V),(∀ w (h : w∈A),g w=some ⟨w,h⟩) ∧
      ∀ w,w∉A→ g w=none :=
    ⟨fun w=>if h : w∈A then some ⟨w,h⟩ else none,fun w h=>dif_pos h,fun w h=>dif_neg h⟩
  have hroot:=rooted_adjoin (G:=G) Z hr hcard hA fun w hw v hv=>by
    obtain ⟨R,hRs,hvR,hRcl,hRr⟩:=qg2 (G:=G) (A.erase w) hv
    obtain ⟨c,hc,hcz⟩:=hcut w hw R hRs ⟨v,hvR⟩ hRcl
    refine ⟨c,hRs hc,?_,(hRr c hc).symm⟩
    rcases hcz with h|⟨k,hk,hck⟩
    · exact Or.inl h
    · exact Or.inr ⟨Finset.mem_of_mem_erase (hRs hc),(hZ _).mpr ⟨k,hk,hck⟩⟩
  obtain ⟨z',hz'⟩:=exists_pull (W:=↥(A : Set V)) Subtype.val_injective z
  have hmeas : Fintype.card (Option (A : Set V)) +
      (av0 (G.induce (A : Set V)) Z).edgeFinset.card < N:=by
    have h1 : Fintype.card (A : Set V)=A.card:=by simp
    have h2:=card_edge_le_of_proj (G:=G) (H:=av0 (G.induce (A : Set V)) Z) g
      fun a b hab=>by
        cases a with
        | none =>
          cases b with
          | none=>exact absurd hab adjoin_not_adj_none
          | some b =>
            obtain ⟨k,hk,hbk⟩:=(hZ b).mp hab
            exact ⟨k,b.1,hbk.symm,hg' k (hKA k hk),hg b.1 b.2⟩
        | some a =>
          cases b with
          | none =>
            obtain ⟨k,hk,hak⟩:=(hZ a).mp hab
            exact ⟨a.1,k,hak,hg a.1 a.2,hg' k (hKA k hk)⟩
          | some b=>exact ⟨a.1,b.1,hab,hg a.1 a.2,hg b.1 b.2⟩
    rw [Fintype.card_option,h1]
    omega
  have hwit' : ∃ o : Option (A : Set V),o≠none∧o≠some ⟨r,hr⟩∧z'.map some≠some o:=by
    obtain ⟨u,hu,hur,huz⟩:=hwit
    exact ⟨some ⟨u,hu⟩,by simp,fun h=>hur (by simpa using h),
      fun h=>huz ((hz' _).mp (map_some_iff.mp h))⟩
  have hdeg' : ∀ o : Option (A : Set V),o≠none→ o≠some ⟨r,hr⟩→ z'.map some≠some o →
      q+1≤ (av0 (G.induce (A : Set V)) Z).degree o:=by
    intro o hon hor hoz
    cases o with
    | none=>exact absurd rfl hon
    | some u =>
      obtain ⟨hd,hcl,huniq⟩:=hdeg u.1 u.2 (fun h=>hor (congrArg some (Subtype.ext h)))
        fun h=>hoz (map_some_iff.mpr ((hz' u).mpr h))
      refine hd.trans (qj6 g (fun w hw=>?_) fun w₁ w₂ h₁ h₂ h=>?_)
      · by_cases hwA : w∈A
        · rw [hg w hwA]
          exact hw
        · rw [hg' w hwA]
          exact (hZ u).mpr ⟨w,(hcl w hw).resolve_left hwA,hw⟩
      · by_cases h₁A : w₁∈A <;> by_cases h₂A : w₂∈A
        · rw [hg _ h₁A,hg _ h₂A] at h
          simpa using h
        · rw [hg _ h₁A,hg' _ h₂A] at h
          exact absurd h (by simp)
        · rw [hg' _ h₁A,hg _ h₂A] at h
          exact absurd h (by simp)
        · exact huniq w₁ ((hcl w₁ h₁).resolve_left h₁A) w₂ ((hcl w₂ h₂).resolve_left h₂A) h₁ h₂
  obtain ⟨a,d,ha,hd,hP⟩:=ih _ (av0 (G.induce (A : Set V)) Z) none
    (some ⟨r,hr⟩) (z'.map some) hmeas ⟨hq,hroot,hwit',hdeg'⟩
  refine ⟨a,d,ha,hd,fun i=>?_⟩
  obtain ⟨p,hp,hl⟩:=hP i
  obtain ⟨c,hc,m,hm,hml,-⟩:=qf4 hp
  obtain ⟨k,hk,hck⟩:=(hZ c).mp hc
  obtain ⟨m',hm',hml',-,hms⟩:=qd3 (G:=G) (A : Set V) hm
  refine ⟨k,hk,Walk.cons hck.symm m',
    (Walk.cons_isPath_iff _ _).mpr ⟨hm',fun h=>hKA k hk (hms k h)⟩,?_,fun v hv=>?_⟩
  · rw [Walk.length_cons,hml',← hml,hl]
  · rw [Walk.support_cons,List.tail_cons] at hv
    exact hms v hv
theorem qq1 [Fintype V] [DecidableEq V] (hK : Kc0 G 2) {R : Finset V} {x v : V}
    (hxv : x≠v) (hxR : x∉R) (hvR : v∉R)
    (hcl : ∀ c∈R,∀ w,G.Adj c w→ w∈R∨w=x∨w=v) (hc : 2 < Rᶜ.card) :
    Rt0 (G.induce ((Rᶜ : Finset V) : Set V)) ⟨x,Finset.mem_compl.mpr hxR⟩
      ⟨v,Finset.mem_compl.mpr hvR⟩:=by
  obtain ⟨-,hl⟩:=kConn_two_iff.mp hK
  refine qb4 hxv hc (fun w hw=>?_) _ _
  obtain ⟨ρ,hρR,hρw,hρxv⟩ : ∃ ρ,ρ∉R∧ρ≠w∧(ρ=x∨ρ=v):=by
    by_cases h : w=x
    · exact ⟨v,hvR,fun h'=>hxv (h ▸ h').symm,Or.inr rfl⟩
    · exact ⟨x,hxR,Ne.symm h,Or.inl rfl⟩
  have hedge : ∀ b,(b=x∨b=v)→ ρ=b∨(G ⊔ edge x v).Adj ρ b:=fun b hb=>by
    by_cases h : ρ=b
    · exact Or.inl h
    · refine Or.inr (Or.inr ?_)
      rw [edge_adj]
      refine ⟨?_,h⟩
      rcases hρxv with h1|h1 <;> rcases hb with h2|h2
      · exact absurd (h1.trans h2.symm) h
      · exact Or.inl ⟨h1,h2⟩
      · exact Or.inr ⟨h1,h2⟩
      · exact absurd (h1.trans h2.symm) h
  intro u hu u' hu'
  have hm : ∀ a,a∈Rᶜ.erase w→ a∈Finset.univ.erase w:=fun a ha =>
    Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase ha,Finset.mem_univ a⟩
  have h:=(hl w u (hm u hu) u' (hm u' hu')).proj (H:=G ⊔ edge x v) (t:=Rᶜ.erase w)
    (fun a=>if a∈R then ρ else a) (fun a _ b _ hab=>?_) (fun a ha=>?_)
  · have hu1 : u∉R:=Finset.mem_compl.mp (Finset.mem_of_mem_erase hu)
    have hu2 : u'∉R:=Finset.mem_compl.mp (Finset.mem_of_mem_erase hu')
    simp only [if_neg hu1,if_neg hu2] at h
    exact h
  · by_cases haR : a∈R <;> by_cases hbR : b∈R
    · left
      simp [haR,hbR]
    · rw [if_pos haR,if_neg hbR]
      exact hedge b ((hcl a haR b hab).resolve_left hbR)
    · rw [if_neg haR,if_pos hbR]
      exact (hedge a ((hcl b hbR a hab.symm).resolve_left haR)).imp Eq.symm fun h=>h.symm
    · rw [if_neg haR,if_neg hbR]
      exact Or.inr (Or.inl hab)
  · split_ifs with h'
    · exact Finset.mem_erase.mpr ⟨hρw,Finset.mem_compl.mpr hρR⟩
    · exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase ha,Finset.mem_compl.mpr h'⟩
end Calls
section Normalise
variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
  {z : Option V} {q : ℕ}
theorem qq3 (ih : Ca0 q (Fintype.card V+G.edgeFinset.card))
    (hH : Ch0 G x y z q) (hf : ¬ Adm0 G x y q) : ¬ G.Adj x y:=by
  intro hxy
  classical
  have hlt:=qj8 (G:=G) hxy
  exact hf (qp2 (show de0 G x y≤ G from sdiff_le)
    (ih V (de0 G x y) x y z (by omega) ⟨hH.1,rooted_delEdge_iff.mpr hH.2.1,hH.2.2.1,
      fun v h1 h2 h3=>(hH.2.2.2 v h1 h2 h3).trans (qs9 h1 h2)⟩))
theorem qal7 {N : ℕ} (ih : Ca0 q N) (hq : 1≤ q) {b : V} {Cx Cy : Finset V}
    (hdeg : ∀ v,v≠x→ v≠y→ z≠some v→ q+1≤ G.degree v)
    (hxC : x∈Cx) (hyC : y∈Cy) (hbCy : b∉Cy) (hdisj : Disjoint Cx Cy)
    (hclx : ∀ c∈Cx,∀ w,G.Adj c w→ w∈Cx∨w=b)
    (hcly : ∀ c∈Cy,∀ w,G.Adj c w→ w∈Cy∨w=b) (hly : Lk0 G Cy)
    (hconn : G.Connected)
    (hrx : ∀ h₁ h₂,Rt0 (G.induce ((insert b Cx : Finset V) : Set V)) ⟨x,h₁⟩ ⟨b,h₂⟩)
    (hN : (insert b Cx).card+G.edgeFinset.card < N) {v : V} (hv : v∈Cx) (hvx : v≠x)
    (hvb : v≠b) (hvz : z≠some v) : Adm0 G x y q:=by
  have hxs : x∈insert b Cx:=Finset.mem_insert_of_mem hxC
  have hbs : b∈insert b Cx:=Finset.mem_insert_self b Cx
  have hdeg' : ∀ u∈insert b Cx,u≠x→ u≠b→ z≠some u →
      q+1≤ G.degree u∧∀ w,G.Adj u w→ w∈insert b Cx:=fun u hu hux hub huz=>by
    have huC:=(Finset.mem_insert.mp hu).resolve_left hub
    refine ⟨hdeg u hux (fun h=>Finset.disjoint_left.mp hdisj huC (h ▸ hyC)) huz,
      fun w hw=>?_⟩
    rcases hclx u huC w hw with h|h
    · exact Finset.mem_insert_of_mem h
    · exact h ▸ hbs
  have hA:=induce_call ih (insert b Cx) hxs hbs z hq (hrx hxs hbs) hN hdeg'
    ⟨v,Finset.mem_insert_of_mem hv,hvx,hvb,hvz⟩
  obtain ⟨c,hc,b',hb',hcb⟩:=ql8 hconn ⟨y,hyC⟩
    ⟨b,Finset.mem_singleton_self b⟩ (Finset.disjoint_singleton_right.mpr hbCy)
    fun c hc w hw=>(hcly c hc w hw).imp_right Finset.mem_singleton.mpr
  rw [Finset.mem_singleton.mp hb'] at hcb
  obtain ⟨p,hp⟩:=qe6 hly hc hcb.symm b (Finset.mem_insert_self _ _) y
    (Finset.mem_insert_of_mem hyC)
  refine qr4 hA p.bypass p.bypass_isPath fun a ha has=>?_
  rcases Finset.mem_insert.mp (hp a (p.support_bypass_subset_support ha)) with h|h
  · exact h
  · rcases Finset.mem_insert.mp has with h'|h'
    · exact h'
    · exact absurd h (Finset.disjoint_left.mp hdisj h')
theorem qaf4 (ih : Ca0 q (Fintype.card V+G.edgeFinset.card))
    (hH : Ch0 G x y z q) (hf : ¬ Adm0 G x y q) (h5 : 5≤ Fintype.card V) :
    Kc0 G 2:=by
  by_contra h2
  obtain ⟨b,hb⟩:=qh7 (by omega) h2
  obtain ⟨hbx,hby,Cx,Cy,hxC,hyC,hbCx,hbCy,hdisj,hcov,hclx,hcly,hlx,hly,hrx,hry⟩ :=
    qm4 hH.2.1 hb
  obtain ⟨v,hvx,hvy,hvb,hvz⟩:=qaj1 z x y b (by omega)
  have hconn:=qu9 hH.2.1
  have hyx : y∉insert b Cx:=by
    rw [Finset.mem_insert,not_or]
    exact ⟨Ne.symm hby,fun h=>Finset.disjoint_left.mp hdisj h hyC⟩
  have hxy : x∉insert b Cy:=by
    rw [Finset.mem_insert,not_or]
    exact ⟨Ne.symm hbx,fun h=>Finset.disjoint_right.mp hdisj h hxC⟩
  have h1:=card_lt_of_notMem hyx
  have h2:=card_lt_of_notMem hxy
  rcases hcov v hvb with hv|hv
  · exact hf (qal7 ih hH.1 hH.2.2.2 hxC hyC hbCy hdisj hclx hcly hly hconn
      (hrx.resolve_left fun h=>hvx (Finset.mem_singleton.mp (h ▸ hv))) (by omega) hv hvx hvb
      hvz)
  · exact hf (qg1 (qal7 ih hH.1 (fun u h1 h2 h3=>hH.2.2.2 u h2 h1 h3) hyC hxC
      hbCx hdisj.symm hcly hclx hlx hconn
      (fun h₁ h₂=>qo4
        ((hry.resolve_left fun h=>hvy (Finset.mem_singleton.mp (h ▸ hv))) h₂ h₁))
      (by omega) hv hvy hvb hvz))
end Normalise
theorem qan0 {q N : ℕ} (ih : Ca0 q N) (hq : 1≤ q) (n : ℕ) :
    ∀ (W : Type) [Fintype W] [DecidableEq W] (H : SimpleGraph W) [DecidableRel H.Adj]
      (x e y : W),Fintype.card W≤ n→ Fintype.card W+H.edgeFinset.card < N →
      Rt0 H x e→ y≠x→ y≠e→ ¬ H.Adj x y →
      (∀ v,v≠x→ v≠y→ v≠e→ q+1≤ H.degree v) →
      (∃ v,v≠x∧v≠y∧v≠e)→ Adm0 H x y q:=by
  induction n with
  | zero =>
    intro W _ _ H _ x e y hc
    exact absurd (Fintype.card_pos_iff.mpr ⟨x⟩) (by omega)
  | succ n ihn =>
    intro W _ _ H _ x e y hc hN hR hyx hye hxy hdeg hwit
    classical
    by_cases hRy : Rt0 H x y
    · exact ih W H x y (some e) hN ⟨hq,hRy,
        hwit.imp fun v ⟨h1,h2,h3⟩=>⟨h1,h2,fun h=>h3 (Option.some.inj h).symm⟩,
        fun v h1 h2 h3=>hdeg v h1 h2 fun h=>h3 (h ▸ rfl)⟩
    obtain ⟨c,hc'⟩:=qh7 hR.2.1 fun h=>hRy ⟨hyx.symm,h⟩
    have hcH : qar6 H c:=by
      obtain ⟨u,v,hu,hv,hp⟩:=hc'
      exact ⟨u,v,hu,hv,fun p=>by simpa using hp (p.mapLe le_sup_left)⟩
    obtain ⟨hcx,hce,Cx,Ce,hxC,heC,hcCx,hcCe,hdisj,hcov,hclx,-,hlx,hle,hrx,-⟩ :=
      qm4 hR hcH
    have hsub : ∀ C : Finset W,c∉C→ C⊆Finset.univ.erase c:=fun C hC b hb =>
      Finset.mem_erase.mpr ⟨fun h=>hC (h ▸ hb),Finset.mem_univ b⟩
    have hyCe : y∉Ce:=by
      intro hy
      obtain ⟨u,v,hu,hv,hp⟩:=hc'
      have hto : ∀ a,a≠c→ Rc0 (H ⊔ edge x y) (Finset.univ.erase c) a x:=fun a ha=>by
        rcases hcov a ha with h|h
        · exact ((hlx a h x hxC).mono (hsub _ hcCx)).mono_graph le_sup_left
        · refine (((hle a h y hy).mono (hsub _ hcCe)).mono_graph le_sup_left).trans ?_
          exact Rc0.adj (hsub _ hcCe hy) (hsub _ hcCx hxC) (Or.inr (by simp [edge_adj,hyx]))
      obtain ⟨p,hp'⟩:=(hto u hu).trans (hto v hv).symm
      exact Finset.notMem_erase c _ (hp' c (hp p))
    have heCx : e∉Cx:=fun h=>Finset.disjoint_left.mp hdisj h heC
    have hes : e∉insert c Cx:=by simp [Ne.symm hce,heCx]
    have hscard:=card_lt_of_notMem hes
    have hcs : c∈insert c Cx:=Finset.mem_insert_self c Cx
    have hxs : x∈insert c Cx:=Finset.mem_insert_of_mem hxC
    have hcl : ∀ u∈insert c Cx,u≠c→ ∀ w,H.Adj u w→ w∈insert c Cx :=
      fun u hu huc w hw=>by
        rcases hclx u ((Finset.mem_insert.mp hu).resolve_left huc) w hw with h|h
        · exact Finset.mem_insert_of_mem h
        · exact h ▸ hcs
    have hdC : ∀ u∈insert c Cx,u≠c→ u≠e:=fun u hu huc h =>
      heCx (h ▸ (Finset.mem_insert.mp hu).resolve_left huc)
    have hmeas : (insert c Cx).card+H.edgeFinset.card < N:=by omega
    by_cases hyc : y=c
    · subst hyc
      obtain ⟨w,hw,hwe⟩:=exists_adj_ne hR.2 x e
      have hxw : H.Adj x w:=qr5 hw (by rintro (⟨-,h⟩|⟨h,-⟩);exacts [hwe h,hR.1 h])
      have hwy : w≠y:=fun h=>hxy (h ▸ hxw)
      have hwC : w∈Cx:=(hclx x hxC w hxw).resolve_right hwy
      have hrx':=hrx.resolve_left fun h=>H.ne_of_adj hxw
        (Finset.mem_singleton.mp (h ▸ hwC)).symm
      exact qm2 (induce_call ih (insert y Cx) hxs hcs none hq (hrx' hxs hcs) hmeas
        (fun u hu hux huy _=>⟨hdeg u hux huy (hdC u hu huy),hcl u hu huy⟩)
        ⟨w,Finset.mem_insert_of_mem hwC,(H.ne_of_adj hxw).symm,hwy,by simp⟩)
    · have hyC : y∈Cx:=(hcov y hyc).resolve_right hyCe
      have hys : y∈insert c Cx:=Finset.mem_insert_of_mem hyC
      obtain ⟨w,hw,hwc⟩:=exists_adj_ne hR.2 y c
      have hyw : H.Adj y w:=qr5 hw (by rintro (⟨h,-⟩|⟨h,-⟩);exacts [hyx h,hye h])
      have hwC : w∈Cx:=(hclx y hyC w hyw).resolve_right hwc
      have hrx':=hrx.resolve_left fun h=>hyx (Finset.mem_singleton.mp (h ▸ hyC))
      have h1 : Fintype.card ((insert c Cx : Finset W) : Set W)=(insert c Cx).card:=by
        simp
      have h2:=qh0 (G:=H)
        (H:=H.induce ((insert c Cx : Finset W) : Set W)) Subtype.val
        Subtype.val_injective fun _ _ h=>h
      have hA:=ihn _ (H.induce ((insert c Cx : Finset W) : Set W)) ⟨x,hxs⟩ ⟨c,hcs⟩ ⟨y,hys⟩
        (by omega) (by omega)
        (hrx' hxs hcs) (fun h=>hyx (congrArg Subtype.val h))
        (fun h=>hyc (congrArg Subtype.val h)) hxy
        (fun v hvx hvy hvc=>(hdeg v.1 (fun h=>hvx (Subtype.ext h))
          (fun h=>hvy (Subtype.ext h)) (hdC v.1 v.2 fun h=>hvc (Subtype.ext h))).trans
          (qo9 _ v.2 (hcl v.1 v.2 fun h=>hvc (Subtype.ext h))))
        ⟨⟨w,Finset.mem_insert_of_mem hwC⟩,
          fun h=>hxy (by
            have h' : w=x:=congrArg Subtype.val h
            rw [h'] at hyw
            exact hyw.symm),
          fun h=>H.ne_of_adj hyw (congrArg Subtype.val h).symm,
          fun h=>hwc (congrArg Subtype.val h)⟩
      exact qj2 (Embedding.induce (G:=H) _).toHom
        (Embedding.induce (G:=H) _).injective hA
section Normalise2
variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
  {z : Option V} {q : ℕ}
theorem qh4 (ih : Ca0 q (Fintype.card V+G.edgeFinset.card))
    (hH : Ch0 G x y z q) (hf : ¬ Adm0 G x y q) (hK : Kc0 G 2) (hxy : ¬ G.Adj x y)
    {zv : V} (hz : z=some zv) (hzx : zv≠x) (hzy : zv≠y) : ¬ G.Adj x zv:=by
  intro hxz
  classical
  have hR : Rt0 (de0 G x zv) x zv :=
    rooted_delEdge_iff.mpr ⟨hzx.symm,qaa6 le_sup_left hK⟩
  have hlt:=qj8 (G:=G) hxz
  have hdeg : ∀ v,v≠x→ v≠y→ v≠zv→ q+1≤ (de0 G x zv).degree v :=
    fun v h1 h2 h3=>(hH.2.2.2 v h1 h2 (by rw [hz];exact fun h=>h3 (Option.some.inj h).symm)).trans
      (qs9 h1 h3)
  have hwit : ∃ v,v≠x∧v≠y∧v≠zv:=by
    obtain ⟨v,h1,h2,h3⟩:=hH.2.2.1
    exact ⟨v,h1,h2,fun h=>h3 (by rw [hz,h])⟩
  exact hf (qp2 (show de0 G x zv≤ G from sdiff_le)
    (qan0 ih hH.1 _ V (de0 G x zv) x zv y le_rfl (by omega) hR hH.2.1.1.symm
      hzy.symm (fun h=>hxy ((show de0 G x zv≤ G from sdiff_le) h)) hdeg hwit))
end Normalise2
section Routes
variable {G : SimpleGraph V} {x y : V}
theorem qar2 [Fintype V] [DecidableEq V] (hK : Kc0 G 2) (hne : x≠y)
    (hxy : ¬ G.Adj x y) {a b : V} (ha : G.Adj x a) (hb : G.Adj x b) (hab : G.Adj a b) : Adm0 G x y 2:=by
  obtain ⟨p,hp⟩:=(kConn_two_iff.mp hK).2 x y (by simp [hne.symm]) a
    (by simp [(G.ne_of_adj ha).symm])
  obtain ⟨r,hr,Q,hQs,hQS,hQp⟩ :=
    qe9 (fun t=>t=a∨t=b) p.bypass (Or.inl rfl)
  have hQ:=hQp p.bypass_isPath
  have hxQ : x∉Q.support:=fun h =>
    Finset.notMem_erase x _ (hp x (p.support_bypass_subset_support (hQs x h)))
  have hxr : G.Adj x r:=by rcases hr with h|h <;> rw [h] <;> assumption
  obtain ⟨s,hxs,hsr,hsQ⟩ : ∃ s,G.Adj x s∧G.Adj s r∧s∉Q.support:=by
    rcases hr with h|h
    · exact ⟨b,hb,by rw [h];exact hab.symm,
        fun h'=>G.ne_of_adj hab ((hQS b h' (Or.inr rfl)).trans h).symm⟩
    · exact ⟨a,ha,by rw [h];exact hab,
        fun h'=>G.ne_of_adj hab ((hQS a h' (Or.inl rfl)).trans h)⟩
  have hl:=qd2 Q fun h=>hxy (by rw [h];exact hxr)
  refine qah9 (P₁:=Walk.cons hxr Q.reverse)
    (P₂:=Walk.cons hxs (Walk.cons hsr Q.reverse)) ?_ ?_ (by simp;omega) (Or.inl (by simp))
  · exact (Walk.cons_isPath_iff _ _).mpr ⟨hQ.reverse,by simpa using hxQ⟩
  · refine (Walk.cons_isPath_iff _ _).mpr
      ⟨(Walk.cons_isPath_iff _ _).mpr ⟨hQ.reverse,by simpa using hsQ⟩,?_⟩
    simp [hxQ,G.ne_of_adj hxs]
theorem qal5 {t t' v c : V} {P : G.Walk c y} (hP : P.IsPath) (hxt : G.Adj x t)
    (hxt' : G.Adj x t') (hvt : G.Adj v t) (hvt' : G.Adj v t') (htc : G.Adj t c) (htt' : t≠t')
    (hvx : v≠x) (hout : ∀ a∈P.support,a≠x∧a≠t∧a≠t'∧a≠v) :
    Adm0 G x y 2:=by
  have hx : x∉P.support:=fun h=>(hout x h).1 rfl
  have ht : t∉P.support:=fun h=>(hout t h).2.1 rfl
  have ht' : t'∉P.support:=fun h=>(hout t' h).2.2.1 rfl
  have hv : v∉P.support:=fun h=>(hout v h).2.2.2 rfl
  have h1:=G.ne_of_adj hxt
  have h2:=G.ne_of_adj hxt'
  have h3:=G.ne_of_adj hvt
  have h4:=G.ne_of_adj hvt'
  refine qah9 (P₁:=Walk.cons hxt (Walk.cons htc P))
    (P₂:=Walk.cons hxt' (Walk.cons hvt'.symm (Walk.cons hvt (Walk.cons htc P)))) ?_ ?_
    (by simp) (Or.inr (by simp only [Walk.length_cons]))
  · simp [Walk.cons_isPath_iff,hP,hx,ht,h1]
  · simp [Walk.cons_isPath_iff,hP,hx,ht,ht',hv,h1,h2,h3,h4.symm,htt'.symm,hvx.symm]
end Routes
section Small2
variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
  {z : Option V}
theorem qar8 (ih : Ca0 2 (Fintype.card V+G.edgeFinset.card)) (hH : Ch0 G x y z 2)
    (hK : Kc0 G 2) (hxy : ¬ G.Adj x y)
    (hz : ∀ zv,z=some zv→ zv≠x→ zv≠y→ ¬ G.Adj x zv) {v t₁ t₂ : V} (hvx : v≠x)
    (hvy : v≠y) (h₁ : G.Adj x t₁) (h₂ : G.Adj x t₂) (h₁₂ : t₁≠t₂) (hv₁ : G.Adj v t₁)
    (hv₂ : G.Adj v t₂) : Adm0 G x y 2:=by
  have hyt : ∀ t,G.Adj x t→ y≠t:=fun t ht h=>hxy (by rw [h];exact ht)
  have hyB : y∈({x,t₁,t₂,v} : Finset V)ᶜ:=by
    simp only [Finset.mem_compl,Finset.mem_insert,Finset.mem_singleton,not_or]
    exact ⟨hH.2.1.1.symm,hyt t₁ h₁,hyt t₂ h₂,hvy.symm⟩
  obtain ⟨R,hRB,hyR,hRcl,hRl⟩:=qal1 (G:=G) _ hyB
  have hnot : ∀ b,(b=x∨b=t₁∨b=t₂∨b=v)→ b∉R:=fun b hb h=>by
    have:=Finset.mem_compl.mp (hRB h)
    simp only [Finset.mem_insert,Finset.mem_singleton] at this
    exact this hb
  have hout : ∀ c∈R,∀ w,G.Adj c w→ w∈R∨w=x∨w=t₁∨w=t₂∨w=v :=
    fun c hc w hw=>by
      rcases hRcl c hc w hw with h|h
      · exact Or.inl h
      · simp only [Finset.mem_compl,not_not,Finset.mem_insert,Finset.mem_singleton] at h
        exact Or.inr h
  have hpath : ∀ c∈R,∃ P : G.Walk c y,P.IsPath∧∀ a∈P.support,a∈R:=fun c hc=>by
    obtain ⟨p,hp⟩:=hRl c hc y hyR
    exact ⟨p.bypass,p.bypass_isPath,fun a ha=>hp a (p.support_bypass_subset_support ha)⟩
  by_cases hat : ∃ c∈R,G.Adj c t₁∨G.Adj c t₂
  · obtain ⟨c,hc,hct⟩:=hat
    obtain ⟨P,hP,hPR⟩:=hpath c hc
    have hPo : ∀ a∈P.support,a≠x∧a≠t₁∧a≠t₂∧a≠v:=fun a ha =>
      ⟨fun h=>hnot a (Or.inl h) (hPR a ha),fun h=>hnot a (Or.inr (Or.inl h)) (hPR a ha),
        fun h=>hnot a (Or.inr (Or.inr (Or.inl h))) (hPR a ha),
        fun h=>hnot a (Or.inr (Or.inr (Or.inr h))) (hPR a ha)⟩
    rcases hct with h|h
    · exact qal5 hP h₁ h₂ hv₁ hv₂ h.symm h₁₂ hvx hPo
    · exact qal5 hP h₂ h₁ hv₂ hv₁ h.symm h₁₂.symm hvx fun a ha =>
        ⟨(hPo a ha).1,(hPo a ha).2.2.1,(hPo a ha).2.1,(hPo a ha).2.2.2⟩
  replace hat : ∀ c∈R,¬ G.Adj c t₁∧¬ G.Adj c t₂:=fun c hc =>
    not_or.mp fun h=>hat ⟨c,hc,h⟩
  have hcl : ∀ c∈R,∀ w,G.Adj c w→ w∈R∨w=x∨w=v:=fun c hc w hw=>by
    rcases hout c hc w hw with h|h|h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd (h ▸ hw) (hat c hc).1
    · exact absurd (h ▸ hw) (hat c hc).2
    · exact Or.inr (Or.inr h)
  have hxR:=hnot x (Or.inl rfl)
  have hvR:=hnot v (Or.inr (Or.inr (Or.inr rfl)))
  have ht₁R:=hnot t₁ (Or.inr (Or.inl rfl))
  have hc3 : 2 < Rᶜ.card:=Finset.two_lt_card_iff.mpr ⟨x,v,t₁,Finset.mem_compl.mpr hxR,
    Finset.mem_compl.mpr hvR,Finset.mem_compl.mpr ht₁R,hvx.symm,G.ne_of_adj h₁,
    G.ne_of_adj hv₁⟩
  have hRc : Rᶜ.card < Fintype.card V:=card_lt_of_notMem (Finset.notMem_compl.mpr hyR)
  have hA:=induce_call ih Rᶜ (Finset.mem_compl.mpr hxR) (Finset.mem_compl.mpr hvR) z
    (by norm_num) (qq1 hK hvx.symm hxR hvR hcl hc3) (by omega)
    (fun u hu hux huv huz=>⟨hH.2.2.2 u hux (fun h=>Finset.mem_compl.mp hu (h ▸ hyR)) huz,
      fun w hw=>Finset.mem_compl.mpr fun hwR=>by
        rcases hcl w hwR u hw.symm with h|h|h
        · exact Finset.mem_compl.mp hu h
        · exact hux h
        · exact huv h⟩)
    ⟨t₁,Finset.mem_compl.mpr ht₁R,(G.ne_of_adj h₁).symm,(G.ne_of_adj hv₁).symm,
      fun h=>hz t₁ h (G.ne_of_adj h₁).symm (hyt t₁ h₁).symm h₁⟩
  obtain ⟨c,hc,d,hdR,hdx,hcd⟩ :=
    qr3 hK hyR ht₁R hH.2.1.1.symm (G.ne_of_adj h₁).symm
  have hdv : d=v:=((hcl c hc d hcd).resolve_left hdR).resolve_left hdx
  rw [hdv] at hcd
  obtain ⟨P,hP,hPR⟩:=hpath c hc
  refine qr4 hA (Walk.cons hcd.symm P)
    ((Walk.cons_isPath_iff _ _).mpr ⟨hP,fun h=>hvR (hPR v h)⟩) fun a ha has=>?_
  rw [Walk.support_cons,List.mem_cons] at ha
  rcases ha with h|h
  · exact h
  · exact absurd (hPR a h) (Finset.mem_compl.mp has)
theorem qaq0 (hH : Ch0 G x y z 2) (h4 : Fintype.card V=4) : Adm0 G x y 2:=by
  obtain ⟨-,⟨hne,hK⟩,⟨u,hux,huy,huz⟩,hdeg⟩:=hH
  have hall : ∀ w,w≠u→ G.Adj u w:=by
    have he : G.neighborFinset u=Finset.univ.erase u:=Finset.eq_of_subset_of_card_le
      (fun w hw=>Finset.mem_erase.mpr
        ⟨(G.ne_of_adj ((mem_neighborFinset _ _ _).mp hw)).symm,Finset.mem_univ w⟩)
      (by
        rw [Finset.card_erase_of_mem (Finset.mem_univ u),Finset.card_univ,h4,
          card_neighborFinset_eq_degree]
        have:=hdeg u hux huy huz
        omega)
    intro w hw
    rw [← mem_neighborFinset,he]
    exact Finset.mem_erase.mpr ⟨hw,Finset.mem_univ w⟩
  obtain ⟨v,-,hv⟩:=Finset.exists_mem_notMem_of_card_lt_card (s:={x,y,u})
    (t:=Finset.univ) (by rw [Finset.card_univ,h4];exact Finset.card_le_three.trans_lt (by norm_num))
  simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hv
  obtain ⟨hvx,hvy,hvu⟩:=hv
  have huniv : ∀ w,w=x∨w=y∨w=u∨w=v:=by
    have h : ({x,y,u,v} : Finset V)=Finset.univ:=Finset.eq_univ_of_card _ (by
      rw [h4,Finset.card_insert_of_notMem (by simp [hne,Ne.symm hux,Ne.symm hvx]),
        Finset.card_insert_of_notMem (by simp [Ne.symm huy,Ne.symm hvy]),
        Finset.card_pair (Ne.symm hvu)])
    intro w
    have hw:=Finset.mem_univ w
    rw [← h] at hw
    simpa using hw
  obtain ⟨w,hw,hwu⟩:=exists_adj_ne hK v u
  have hvw : G.Adj v w:=qr5 hw (by rintro (⟨h,-⟩|⟨h,-⟩);exacts [hvx h,hvy h])
  have hxu : G.Adj x u:=(hall x (Ne.symm hux)).symm
  have huy' : G.Adj u y:=hall y (Ne.symm huy)
  have huv : G.Adj u v:=hall v hvu
  have hP₁ : (Walk.cons hxu (Walk.cons huy' Walk.nil)).IsPath:=by
    simp [Walk.cons_isPath_iff,hne,Ne.symm hux,huy]
  rcases huniv w with h|h|h|h
  · rw [h] at hvw
    refine qah9 hP₁ (P₂:=Walk.cons hvw.symm (Walk.cons huv.symm (Walk.cons huy' Walk.nil)))
      ?_ (by simp) (Or.inl (by simp))
    simp [Walk.cons_isPath_iff,hne,Ne.symm hux,huy,hvy,hvu,Ne.symm hvx]
  · rw [h] at hvw
    refine qah9 hP₁ (P₂:=Walk.cons hxu (Walk.cons huv (Walk.cons hvw Walk.nil)))
      ?_ (by simp) (Or.inl (by simp))
    simp [Walk.cons_isPath_iff,hne,Ne.symm hux,huy,hvy,Ne.symm hvu,Ne.symm hvx]
  · exact absurd h hwu
  · exact absurd (h ▸ hvw) (G.irrefl)
theorem qao7 (ih : Ca0 2 (Fintype.card V+G.edgeFinset.card)) (hH : Ch0 G x y z 2)
    (hf : ¬ Adm0 G x y 2) (hK : Kc0 G 2) (hxy : ¬ G.Adj x y)
    (hz : ∀ zv,z=some zv→ zv≠x→ zv≠y→ ¬ G.Adj x zv∧¬ G.Adj y zv)
    (hdxy : G.degree x≤ G.degree y) : False:=by
  have hne : x≠y:=hH.2.1.1
  have hdeg3:=hH.2.2.2
  have htri : ∀ a b,G.Adj x a→ G.Adj x b→ ¬ G.Adj a b:=fun a b ha hb hab =>
    hf (qar2 hK hne hxy ha hb hab)
  have hsq : ∀ v t₁ t₂,v≠x→ v≠y→ G.Adj x t₁→ G.Adj x t₂→ G.Adj v t₁→ G.Adj v t₂ →
      t₁=t₂:=fun v t₁ t₂ hvx hvy h₁ h₂ hv₁ hv₂=>by
    by_contra h₁₂
    exact hf (qar8 ih hH hK hxy (fun zv h h' h''=>(hz zv h h' h'').1) hvx hvy h₁ h₂ h₁₂
      hv₁ hv₂)
  obtain ⟨T,hT⟩ : ∃ T : Finset V,T=G.neighborFinset x:=⟨_,rfl⟩
  have hmT : ∀ t,t∈T↔G.Adj x t:=fun t=>by rw [hT,mem_neighborFinset]
  have hTc : T.card=G.degree x:=by rw [hT,card_neighborFinset_eq_degree]
  have hT2 : 2≤ T.card:=by rw [hTc];exact qe8 hK x
  have hxT : x∉T:=fun h=>G.irrefl ((hmT x).mp h)
  have hyT : y∉T:=fun h=>hxy ((hmT y).mp h)
  have hTne : ∀ t∈T,t≠x∧t≠y:=fun t ht =>
    ⟨fun h=>hxT (h ▸ ht),fun h=>hyT (h ▸ ht)⟩
  have hzT : ∀ t∈T,z≠some t:=fun t ht h =>
    (hz t h (hTne t ht).1 (hTne t ht).2).1 ((hmT t).mp ht)
  have hcardT : (insert x T).card=T.card+1:=Finset.card_insert_of_notMem hxT
  have hle:=Finset.card_le_univ (insert x T)
  have hyB : y∈(insert x T)ᶜ:=by
    rw [Finset.mem_compl,Finset.mem_insert,not_or]
    exact ⟨hne.symm,hyT⟩
  obtain ⟨C,hCB,hyC,hCcl,hCl⟩:=qal1 (G:=G) _ hyB
  have hCx : ∀ c∈C,c≠x∧c∉T:=fun c hc=>by
    have:=Finset.mem_compl.mp (hCB hc)
    rw [Finset.mem_insert,not_or] at this
    exact this
  have hCout : ∀ c∈C,∀ w,G.Adj c w→ w∈C∨w∈T:=fun c hc w hw=>by
    rcases hCcl c hc w hw with h|h
    · exact Or.inl h
    · rw [Finset.mem_compl,not_not,Finset.mem_insert] at h
      rcases h with h|h
      · exact absurd ((hmT c).mpr (h ▸ hw).symm) (hCx c hc).2
      · exact Or.inr h
  by_cases hCy : C={y}
  ·
    have hNy : ∀ w,G.Adj y w→ w∈T:=fun w hw=>(hCout y hyC w hw).resolve_left fun h=>by
      rw [hCy,Finset.mem_singleton] at h
      exact G.ne_of_adj hw h.symm
    have hNeq : G.neighborFinset y=T:=Finset.eq_of_subset_of_card_le
      (fun w hw=>hNy w ((mem_neighborFinset _ _ _).mp hw))
      (by rw [hTc,card_neighborFinset_eq_degree];exact hdxy)
    have hTy : ∀ t∈T,G.Adj y t:=fun t ht=>(mem_neighborFinset _ _ _).mp (hNeq ▸ ht)
    obtain ⟨t₀,ht₀⟩ : T.Nonempty:=Finset.card_pos.mp (by omega)
    obtain ⟨u₀,hu₀,hu₀n⟩:=Finset.exists_mem_notMem_of_card_lt_card (s:={x,y})
      (t:=G.neighborFinset t₀) (by
        rw [card_neighborFinset_eq_degree]
        have:=hdeg3 t₀ (hTne t₀ ht₀).1 (hTne t₀ ht₀).2 (hzT t₀ ht₀)
        exact Finset.card_le_two.trans_lt (by omega))
    rw [mem_neighborFinset] at hu₀
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hu₀n
    have hu₀T : u₀∉T:=fun h=>htri t₀ u₀ ((hmT _).mp ht₀) ((hmT _).mp h) hu₀
    obtain ⟨U,hU⟩ : ∃ U : Finset V,U=(insert y (insert x T))ᶜ:=⟨_,rfl⟩
    have hmU : ∀ w,w∈U↔w≠y∧w≠x∧w∉T:=fun w=>by
      rw [hU,Finset.mem_compl,Finset.mem_insert,Finset.mem_insert,not_or,not_or]
    have hu₀U : u₀∈U:=(hmU u₀).mpr ⟨hu₀n.2,hu₀n.1,hu₀T⟩
    have hUT : ∀ w∈U,∀ t,G.Adj w t→ t∈U∨t∈T:=fun w hw t hwt=>by
      by_cases htU : t∈U
      · exact Or.inl htU
      · right
        rw [hmU] at htU hw
        by_contra htT
        by_cases hty : t=y
        · exact hw.2.2 (hNy w (hty ▸ hwt).symm)
        · by_cases htx : t=x
          · exact hw.2.2 ((hmT w).mpr (htx ▸ hwt).symm)
          · exact htU ⟨hty,htx,htT⟩
    obtain ⟨u₁,hu₁U,hu₁z⟩ : ∃ u∈U,z≠some u:=by
      by_contra hno'
      have hno : ∀ u∈U,z=some u:=fun u hu=>by_contra fun h=>hno' ⟨u,hu,h⟩
      have hz₀:=hno u₀ hu₀U
      have hin : ∀ w,G.Adj u₀ w→ w∈T:=fun w hw=>by
        rcases hUT u₀ hu₀U w hw with h|h
        · exact absurd (Option.some.inj ((hno w h).symm.trans hz₀)) (G.ne_of_adj hw).symm
        · exact h
      obtain ⟨w₁,hw₁,w₂,hw₂,h12⟩:=Finset.one_lt_card.mp (by
        rw [card_neighborFinset_eq_degree]
        have:=qe8 hK u₀
        omega : 1 < (G.neighborFinset u₀).card)
      rw [mem_neighborFinset] at hw₁ hw₂
      exact h12 (hsq u₀ w₁ w₂ ((hmU u₀).mp hu₀U).2.1 ((hmU u₀).mp hu₀U).1
        ((hmT _).mp (hin w₁ hw₁)) ((hmT _).mp (hin w₂ hw₂)) hw₁ hw₂)
    obtain ⟨D,hDU,hu₁D,hDcl,hDl⟩:=qal1 (G:=G) U hu₁U
    have hDn : ∀ d∈D,d≠y∧d≠x∧d∉T:=fun d hd=>(hmU d).mp (hDU hd)
    have hDout : ∀ d∈D,∀ w,G.Adj d w→ w∈D∨w∈T:=fun d hd w hw=>by
      rcases hDcl d hd w hw with h|h
      · exact Or.inl h
      · exact Or.inr ((hUT d (hDU hd) w hw).resolve_left h)
    have hxD : x∉D:=fun h=>(hDn x h).2.1 rfl
    have hyD : y∉D:=fun h=>(hDn y h).1 rfl
    obtain ⟨c,hc,t,htD,-,hct⟩:=qr3 hK hu₁D hyD (hDn u₁ hu₁D).2.1 hne.symm
    have htT : t∈T:=(hDout c hc t hct).resolve_left htD
    have hcardU : D.card+2 < Fintype.card V:=by
      have h1 : D.card≤ U.card:=Finset.card_le_card hDU
      have h2 : U.card=Fintype.card V - (insert y (insert x T)).card:=by
        rw [hU,Finset.card_compl]
      have h3 : (insert y (insert x T)).card=T.card+2:=by
        rw [Finset.card_insert_of_notMem (by rw [Finset.mem_insert,not_or];exact ⟨hne.symm,hyT⟩),
          hcardT]
      have h4:=Finset.card_le_univ (insert y (insert x T))
      omega
    obtain ⟨a,d,ha,hd,hP⟩:=qae0 ih (insert t D) (T.erase t)
      (Finset.mem_insert_self t D) z (by norm_num)
      (fun k hk hkA=>by
        rcases Finset.mem_insert.mp hkA with h|h
        · exact Finset.ne_of_mem_erase hk h
        · exact (hDn k h).2.2 (Finset.mem_of_mem_erase hk))
      (qe6 hDl hc hct.symm)
      (by rw [Finset.card_insert_of_notMem htD];have:=Finset.card_pos.mpr ⟨u₁,hu₁D⟩;omega)
      (fun w hw R hRs ⟨r,hr⟩ hRcl=>by
        by_cases htR : t∈R
        · exact ⟨t,htR,Or.inl rfl⟩
        have hRD : ∀ a∈R,a∈D:=fun a ha=>by
          rcases Finset.mem_insert.mp (Finset.mem_of_mem_erase (hRs ha)) with h|h
          · exact absurd (h ▸ ha) htR
          · exact h
        have hxw : x≠w:=fun h=>by
          rcases Finset.mem_insert.mp (h ▸ hw) with h'|h'
          · exact hxT (h' ▸ htT)
          · exact hxD h'
        obtain ⟨c₁,hc₁,d₁,hd₁R,hd₁w,hcd₁⟩:=qr3 hK hr (u:=x)
          (fun h=>hxD (hRD x h)) (Finset.ne_of_mem_erase (hRs hr)) hxw
        refine ⟨c₁,hc₁,Or.inr ⟨d₁,?_,hcd₁⟩⟩
        rcases hDout c₁ (hRD c₁ hc₁) d₁ hcd₁ with h|h
        · exact absurd (hRcl c₁ hc₁ d₁ (Finset.mem_erase.mpr ⟨hd₁w,Finset.mem_insert_of_mem h⟩)
            hcd₁) hd₁R
        · refine Finset.mem_erase.mpr ⟨fun h'=>hd₁R (hRcl c₁ hc₁ d₁
            (Finset.mem_erase.mpr ⟨hd₁w,h' ▸ Finset.mem_insert_self t D⟩) hcd₁),h⟩)
      (by rw [Finset.card_insert_of_notMem htD];omega)
      (fun u hu hut huz=>by
        have huD:=(Finset.mem_insert.mp hu).resolve_left hut
        refine ⟨hdeg3 u (hDn u huD).2.1 (hDn u huD).1 huz,fun w hw=>?_,
          fun k₁ hk₁ k₂ hk₂ h₁ h₂=>hsq u k₁ k₂ (hDn u huD).2.1 (hDn u huD).1
            ((hmT _).mp (Finset.mem_of_mem_erase hk₁)) ((hmT _).mp (Finset.mem_of_mem_erase hk₂))
            h₁ h₂⟩
        rcases hDout u huD w hw with h|h
        · exact Or.inl (Finset.mem_insert_of_mem h)
        · by_cases hwt : w=t
          · exact Or.inl (hwt ▸ Finset.mem_insert_self t D)
          · exact Or.inr (Finset.mem_erase.mpr ⟨hwt,h⟩))
      ⟨u₁,Finset.mem_insert_of_mem hu₁D,fun h=>htD (h ▸ hu₁D),hu₁z⟩
    refine hf ⟨a+2,d,by omega,hd,fun i=>?_⟩
    obtain ⟨k,hk,p,hp,hl,hs⟩:=hP i
    have hkT:=Finset.mem_of_mem_erase hk
    have hnot : ∀ b,b=x∨b=y→ b∉p.support:=fun b hb h=>by
      rw [← Walk.cons_tail_support,List.mem_cons] at h
      have hbT : b∉T:=by rcases hb with rfl|rfl <;> assumption
      rcases h with h|h
      · exact hbT (h ▸ hkT)
      · rcases Finset.mem_insert.mp (hs b h) with h'|h'
        · exact hbT (h' ▸ htT)
        · rcases hb with rfl|rfl
          exacts [hxD h',hyD h']
    have hxp : x∉(p.concat (hTy t htT).symm).support:=by
      rw [Walk.support_concat,List.mem_append,List.mem_singleton,not_or]
      exact ⟨hnot x (Or.inl rfl),hne⟩
    exact ⟨Walk.cons ((hmT k).mp hkT) (p.concat (hTy t htT).symm),
      (Walk.cons_isPath_iff _ _).mpr ⟨hp.concat (hnot y (Or.inr rfl)) _,hxp⟩,
      by rw [Walk.length_cons,Walk.length_concat,hl];ring⟩
  obtain ⟨c₀,hc₀,hc₀y⟩ : ∃ c∈C,c≠y:=by
    by_contra hno'
    have hno : ∀ c∈C,c=y:=fun c hc=>by_contra fun h=>hno' ⟨c,hc,h⟩
    exact hCy (Finset.eq_singleton_iff_unique_mem.mpr ⟨hyC,hno⟩)
  obtain ⟨c,hc,hyc⟩:=adj_of_linked hCl hyC hc₀ hc₀y
  have hCc : C.card≤ (insert x T)ᶜ.card:=Finset.card_le_card hCB
  rw [Finset.card_compl] at hCc
  obtain ⟨a,d,ha,hd,hP⟩:=qae0 ih C T hyC z (by norm_num)
    (fun k hk hkC=>(hCx k hkC).2 hk) hCl
    (Finset.one_lt_card.mpr ⟨y,hyC,c,hc,G.ne_of_adj hyc⟩)
    (fun w hw R hRs ⟨r,hr⟩ hRcl=>by
      obtain ⟨c',hc',d',hdR,hdw,hcd⟩:=qr3 hK hr (u:=x)
        (fun h=>(hCx x (Finset.mem_of_mem_erase (hRs h))).1 rfl)
        (Finset.ne_of_mem_erase (hRs hr)) (hCx w hw).1.symm
      refine ⟨c',hc',Or.inr ⟨d',?_,hcd⟩⟩
      rcases hCout c' (Finset.mem_of_mem_erase (hRs hc')) d' hcd with h|h
      · exact absurd (hRcl c' hc' d' (Finset.mem_erase.mpr ⟨hdw,h⟩) hcd) hdR
      · exact h)
    (by omega)
    (fun u hu huy huz=>⟨hdeg3 u (hCx u hu).1 huy huz,hCout u hu,
      fun k₁ hk₁ k₂ hk₂ h₁ h₂=>hsq u k₁ k₂ (hCx u hu).1 huy ((hmT _).mp hk₁)
        ((hmT _).mp hk₂) h₁ h₂⟩)
    ⟨c,hc,(G.ne_of_adj hyc).symm,fun h=>(hz c h (hCx c hc).1 (G.ne_of_adj hyc).symm).2 hyc⟩
  refine hf ⟨a+1,d,by omega,hd,fun i=>?_⟩
  obtain ⟨k,hk,p,hp,hl,hs⟩:=hP i
  have hxp : x∉p.support:=by
    rw [← Walk.cons_tail_support,List.mem_cons,not_or]
    exact ⟨fun h=>hxT (h ▸ hk),fun h=>(hCx x (hs x h)).1 rfl⟩
  exact ⟨Walk.cons ((hmT k).mp hk) p,(Walk.cons_isPath_iff _ _).mpr ⟨hp,hxp⟩,
    by rw [Walk.length_cons,hl];ring⟩
end Small2
theorem qap7 : ∀ N,Ca0 2 N:=by
  intro N
  induction N with
  | zero =>
    intro V _ _ G _ x y z h
    exact absurd h (Nat.not_lt_zero _)
  | succ n ihn =>
    intro V _ _ G _ x y z hlt hH
    have ih : Ca0 2 (Fintype.card V+G.edgeFinset.card):=ihn.mono (by omega)
    by_contra hf
    obtain ⟨u,hux,huy,huz⟩:=hH.2.2.1
    have h4 : 4≤ Fintype.card V:=by
      have:=hH.2.2.2 u hux huy huz
      have:=G.degree_lt_card_verts u
      omega
    rcases Nat.lt_or_ge (Fintype.card V) 5 with h5|h5
    · exact hf (qaq0 hH (by omega))
    have hxy:=qq3 ih hH hf
    have hK:=qaf4 ih hH hf h5
    have hH':=qu8 hH
    have hf' : ¬ Adm0 G y x 2:=fun h=>hf (qg1 h)
    have hxz : ∀ zv,z=some zv→ zv≠x→ zv≠y→ ¬ G.Adj x zv :=
      fun zv h1 h2 h3=>qh4 ih hH hf hK hxy h1 h2 h3
    have hyz : ∀ zv,z=some zv→ zv≠x→ zv≠y→ ¬ G.Adj y zv :=
      fun zv h1 h2 h3=>qh4 ih hH' hf' hK (fun h=>hxy h.symm) h1 h3 h2
    rcases le_total (G.degree x) (G.degree y) with hd|hd
    · exact qao7 ih hH hf hK hxy (fun zv h1 h2 h3=>⟨hxz zv h1 h2 h3,hyz zv h1 h2 h3⟩) hd
    · exact qao7 ih hH' hf' hK (fun h=>hxy h.symm)
        (fun zv h1 h2 h3=>⟨hyz zv h1 h3 h2,hxz zv h1 h3 h2⟩) hd
end Cb
section Exported
open Cb
variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V}
  {z : Option V} {q : ℕ}
theorem qas1 (h : Ch0 G x y z 1) : Adm0 G x y 1:=by
  obtain ⟨-,⟨hne,hK⟩,-,-⟩:=h
  obtain ⟨t,ht,hty⟩:=exists_adj_ne hK x y
  have hxt : G.Adj x t:=qr5 ht (by rintro (⟨-,h⟩|⟨h,-⟩);exacts [hty h,hne h])
  obtain ⟨p,hp⟩:=qe3 (Or.inl (Finset.notMem_erase x _))
    ((kConn_two_iff.mp hK).2 x t (by simp [(G.ne_of_adj hxt).symm]) y (by simp [hne.symm]))
  have hx : x∉p.bypass.support:=fun h' =>
    Finset.notMem_erase x _ (hp x (p.support_bypass_subset_support h'))
  have hl:=qd2 p.bypass hty
  refine ⟨p.bypass.length+1,1,by omega,Or.inl rfl,fun i=>⟨Walk.cons hxt p.bypass,
    (Walk.cons_isPath_iff _ _).mpr ⟨p.bypass_isPath,hx⟩,?_⟩⟩
  have:=i.2
  rw [Walk.length_cons]
  omega
theorem qas0 (h : Ch0 G x y z 2) : Adm0 G x y 2 :=
  qap7 _ V G x y z (Nat.lt_succ_self _) h
theorem qb6 (_ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q) : 3≤ q:=by
  by_contra h
  rcases (by have:=hHyp.1;omega : q=1∨q=2) with rfl|rfl
  · exact hfail (qas1 hHyp)
  · exact hfail (qas0 hHyp)
theorem qy8 (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q) :
    5≤ Fintype.card V:=by
  have h3:=qb6 ih hHyp hq4 hfail
  obtain ⟨v,h1,h2,h3'⟩:=hHyp.2.2.1
  have:=hHyp.2.2.2 v h1 h2 h3'
  have:=G.degree_lt_card_verts v
  omega
theorem qb3 (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q) : ¬ G.Adj x y :=
  qq3 (ih.toAt hq4) hHyp hfail
theorem qb7 (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q) : Kc0 G 2 :=
  qaf4 (ih.toAt hq4) hHyp hfail (qy8 ih hHyp hq4 hfail)
theorem qm6 (_ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (_hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q) :
    Ch0 G y x z q∧¬ Adm0 G y x q :=
  ⟨qu8 hHyp,fun h=>hfail (qg1 h)⟩
theorem qf3 (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q) (zv : V)
    (hz : z=some zv) (hzx : zv≠x) (hzy : zv≠y) : ¬ G.Adj x zv :=
  qh4 (ih.toAt hq4) hHyp hfail (qb7 ih hHyp hq4 hfail)
    (qb3 ih hHyp hq4 hfail) hz hzx hzy
theorem qd5 (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q) (zv : V)
    (hz : z=some zv) (hzx : zv≠x) (hzy : zv≠y) : ¬ G.Adj y zv :=
  qh4 (ih.toAt hq4) (qu8 hHyp) (fun h=>hfail (qg1 h))
    (qb7 ih hHyp hq4 hfail) (fun h=>qb3 ih hHyp hq4 hfail h.symm)
    hz hzy hzx
theorem qam2 (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q) :
    ¬ G.Adj x y∧∀ zv,z=some zv→ zv≠x→ zv≠y→ ¬ G.Adj x zv∧¬ G.Adj y zv :=
  ⟨qb3 ih hHyp hq4 hfail,fun zv hz hzx hzy =>
    ⟨qf3 ih hHyp hq4 hfail zv hz hzx hzy,
      qd5 ih hHyp hq4 hfail zv hz hzx hzy⟩⟩
end Exported
end DeanK5
end M8
section M9
namespace DeanK5
open SimpleGraph
variable {V : Type}
inductive Ck0
  | t1
  | t2
  | t3
  deriving DecidableEq
def Ck0.rank : Ck0→ ℕ
  | .t1=>1
  | .t2=>2
  | .t3=>3
theorem Ck0.rank_injective : Function.Injective Ck0.rank:=by
  intro a b h
  cases a <;> cases b <;> first|rfl|exact absurd h (by decide)
def CliqueIn (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ a∈A,∀ b∈A,a≠b→ G.Adj a b
def IndepIn (G : SimpleGraph V) (A : Finset V) : Prop :=
  ∀ a∈A,∀ b∈A,¬ G.Adj a b
def Cs0 (G : SimpleGraph V) (x : V) : Ck0→ Finset V→ Finset V→ Prop
  | .t1,S,T=>S=∅∧2≤ T.card∧(∀ t∈T,G.Adj x t)∧CliqueIn G T
  | .t2,S,T=>S.card=2∧2≤ T.card∧(∀ s∈S,G.Adj x s)∧IndepIn G S ∧
      CliqueIn G T∧∀ s∈S,∀ t∈T,G.Adj s t
  | .t3,S,T=>S.card+1≤ T.card∧2≤ T.card∧(∀ t∈T,G.Adj x t)∧IndepIn G S ∧
      IndepIn G T∧∀ s∈S,∀ t∈T,G.Adj s t
structure Cc0 (G : SimpleGraph V) (x y : V) where
  kind : Ck0
  S : Finset V
  T : Finset V
  x_ne_y : x≠y
  x_notMem_S : x∉S
  x_notMem_T : x∉T
  y_notMem_S : y∉S
  y_notMem_T : y∉T
  disj : Disjoint S T
  shape : Cs0 G x kind S T
namespace Cc0
variable {G : SimpleGraph V} {x y : V}
def verts [DecidableEq V] (H : Cc0 G x y) : Finset V:=insert x (H.S∪H.T)
def ell (H : Cc0 G x y) : ℕ :=
  match H.kind with
  | .t1=>H.T.card - 1
  | .t2=>H.T.card
  | .t3=>H.S.card
theorem shape1 (H : Cc0 G x y) (hk : H.kind=.t1) :
    H.S=∅∧2≤ H.T.card∧(∀ t∈H.T,G.Adj x t)∧CliqueIn G H.T:=by
  have h:=H.shape
  rw [hk] at h
  exact h
theorem shape2 (H : Cc0 G x y) (hk : H.kind=.t2) :
    H.S.card=2∧2≤ H.T.card∧(∀ s∈H.S,G.Adj x s)∧IndepIn G H.S ∧
      CliqueIn G H.T∧∀ s∈H.S,∀ t∈H.T,G.Adj s t:=by
  have h:=H.shape
  rw [hk] at h
  exact h
theorem shape3 (H : Cc0 G x y) (hk : H.kind=.t3) :
    H.S.card+1≤ H.T.card∧2≤ H.T.card∧(∀ t∈H.T,G.Adj x t)∧IndepIn G H.S ∧
      IndepIn G H.T∧∀ s∈H.S,∀ t∈H.T,G.Adj s t:=by
  have h:=H.shape
  rw [hk] at h
  exact h
theorem ell_t1 (H : Cc0 G x y) (hk : H.kind=.t1) : H.ell=H.T.card - 1:=by
  unfold ell
  rw [hk]
theorem ell_t2 (H : Cc0 G x y) (hk : H.kind=.t2) : H.ell=H.T.card:=by
  unfold ell
  rw [hk]
theorem ell_t3 (H : Cc0 G x y) (hk : H.kind=.t3) : H.ell=H.S.card:=by
  unfold ell
  rw [hk]
theorem ell_le_card [Fintype V] (H : Cc0 G x y) : H.ell≤ Fintype.card V:=by
  have h1:=Finset.card_le_univ H.S
  have h2:=Finset.card_le_univ H.T
  unfold ell
  split <;> omega
theorem two_le_T (H : Cc0 G x y) : 2≤ H.T.card:=by
  cases hk : H.kind
  exacts [(H.shape1 hk).2.1,(H.shape2 hk).2.1,(H.shape3 hk).2.1]
section Verts
variable [DecidableEq V]
theorem x_mem_verts (H : Cc0 G x y) : x∈H.verts:=Finset.mem_insert_self _ _
theorem S_subset_verts (H : Cc0 G x y) : H.S⊆H.verts:=fun _ h =>
  Finset.mem_insert_of_mem (Finset.mem_union_left _ h)
theorem T_subset_verts (H : Cc0 G x y) : H.T⊆H.verts:=fun _ h =>
  Finset.mem_insert_of_mem (Finset.mem_union_right _ h)
theorem y_notMem_verts (H : Cc0 G x y) : y∉H.verts:=by
  simp only [verts,Finset.mem_insert,Finset.mem_union,not_or]
  exact ⟨H.x_ne_y.symm,H.y_notMem_S,H.y_notMem_T⟩
theorem mem_verts {H : Cc0 G x y} {v : V} : v∈H.verts↔v=x∨v∈H.S∨v∈H.T:=by
  simp [verts]
end Verts
end Cc0
section Constructors
variable {G : SimpleGraph V} {x y : V}
theorem CliqueIn.mono {A B : Finset V} (h : CliqueIn G B) (hAB : A⊆B) : CliqueIn G A :=
  fun a ha b hb=>h a (hAB ha) b (hAB hb)
theorem IndepIn.mono {A B : Finset V} (h : IndepIn G B) (hAB : A⊆B) : IndepIn G A :=
  fun a ha b hb=>h a (hAB ha) b (hAB hb)
theorem qq8 {A B : Finset V} (h : ∀ a∈A,∀ b∈B,G.Adj a b) : Disjoint A B :=
  Finset.disjoint_left.mpr fun a ha hb=>G.irrefl (h a ha a hb)
theorem qa0 {A : Finset V} {a b : V} (ha : a∈A) (hb : b∉A) : a≠b :=
  fun h=>hb (h ▸ ha)
def Cc0.mk1 (hxy : x≠y) (T : Finset V) (hT : 2≤ T.card) (hxT : ∀ t∈T,G.Adj x t)
    (hK : CliqueIn G T) (hyT : y∉T) : Cc0 G x y where
  kind:=.t1
  S:=∅
  T:=T
  x_ne_y:=hxy
  x_notMem_S:=Finset.notMem_empty x
  x_notMem_T:=fun h=>G.irrefl (hxT x h)
  y_notMem_S:=Finset.notMem_empty y
  y_notMem_T:=hyT
  disj:=Finset.disjoint_empty_left T
  shape:=⟨rfl,hT,hxT,hK⟩
def Cc0.mk2 (hxy : x≠y) (S T : Finset V) (hS : S.card=2) (hT : 2≤ T.card)
    (hxS : ∀ s∈S,G.Adj x s) (hIS : IndepIn G S) (hKT : CliqueIn G T)
    (hST : ∀ s∈S,∀ t∈T,G.Adj s t) (hxT : x∉T) (hyS : y∉S) (hyT : y∉T) :
    Cc0 G x y where
  kind:=.t2
  S:=S
  T:=T
  x_ne_y:=hxy
  x_notMem_S:=fun h=>G.irrefl (hxS x h)
  x_notMem_T:=hxT
  y_notMem_S:=hyS
  y_notMem_T:=hyT
  disj:=qq8 hST
  shape:=⟨hS,hT,hxS,hIS,hKT,hST⟩
def Cc0.mk3 (hxy : x≠y) (S T : Finset V) (hc : S.card+1≤ T.card) (hT : 2≤ T.card)
    (hxT : ∀ t∈T,G.Adj x t) (hIS : IndepIn G S) (hIT : IndepIn G T)
    (hST : ∀ s∈S,∀ t∈T,G.Adj s t) (hxS : x∉S) (hyS : y∉S) (hyT : y∉T) :
    Cc0 G x y where
  kind:=.t3
  S:=S
  T:=T
  x_ne_y:=hxy
  x_notMem_S:=hxS
  x_notMem_T:=fun h=>G.irrefl (hxT x h)
  y_notMem_S:=hyS
  y_notMem_T:=hyT
  disj:=qq8 hST
  shape:=⟨hc,hT,hxT,hIS,hIT,hST⟩
@[simp] theorem Cc0.mk1_kind {hxy : x≠y} {T : Finset V} {hT hxT hK hyT} :
    (Cc0.mk1 (G:=G) hxy T hT hxT hK hyT).kind=.t1:=rfl
@[simp] theorem Cc0.mk2_kind {hxy : x≠y} {S T : Finset V} {hS hT hxS hIS hKT hST hxT hyS hyT} :
    (Cc0.mk2 (G:=G) hxy S T hS hT hxS hIS hKT hST hxT hyS hyT).kind=.t2:=rfl
@[simp] theorem Cc0.mk3_kind {hxy : x≠y} {S T : Finset V} {hc hT hxT hIS hIT hST hxS hyS hyT} :
    (Cc0.mk3 (G:=G) hxy S T hc hT hxT hIS hIT hST hxS hyS hyT).kind=.t3:=rfl
theorem Cc0.mk1_ell {hxy : x≠y} {T : Finset V} {hT hxT hK hyT} :
    (Cc0.mk1 (G:=G) hxy T hT hxT hK hyT).ell=T.card - 1:=rfl
theorem Cc0.mk2_ell {hxy : x≠y} {S T : Finset V} {hS hT hxS hIS hKT hST hxT hyS hyT} :
    (Cc0.mk2 (G:=G) hxy S T hS hT hxS hIS hKT hST hxT hyS hyT).ell=T.card:=rfl
theorem Cc0.mk3_ell {hxy : x≠y} {S T : Finset V} {hc hT hxT hIS hIT hST hxS hyS hyT} :
    (Cc0.mk3 (G:=G) hxy S T hc hT hxT hIS hIT hST hxS hyS hyT).ell=S.card:=rfl
theorem Cc0.mk3_T {hxy : x≠y} {S T : Finset V} {hc hT hxT hIS hIT hST hxS hyS hyT} :
    (Cc0.mk3 (G:=G) hxy S T hc hT hxT hIS hIT hST hxS hyS hyT).T=T:=rfl
def Cc0.sub3 (H : Cc0 G x y) (hk : H.kind=.t3) (S' T' : Finset V) (hS : S'⊆H.S)
    (hT : T'⊆H.T) (hc : S'.card+1≤ T'.card) (h2 : 2≤ T'.card) : Cc0 G x y :=
  have h:=H.shape3 hk
  Cc0.mk3 H.x_ne_y S' T' hc h2 (fun t ht=>h.2.2.1 t (hT ht)) (h.2.2.2.1.mono hS)
    (h.2.2.2.2.1.mono hT) (fun s hs t ht=>h.2.2.2.2.2 s (hS hs) t (hT ht))
    (fun h'=>H.x_notMem_S (hS h')) (fun h'=>H.y_notMem_S (hS h'))
    (fun h'=>H.y_notMem_T (hT h'))
variable [DecidableEq V]
theorem qa9' {P : V→ Prop} {a : V} {A : Finset V} (ha : P a) (hA : ∀ c∈A,P c) :
    ∀ c∈insert a A,P c:=fun c hc=>by
  rcases Finset.mem_insert.mp hc with rfl|hc
  exacts [ha,hA c hc]
theorem qb0 {P : V→ Prop} {a b : V} (ha : P a) (hb : P b) :
    ∀ c∈({a,b} : Finset V),P c :=
  qa9' ha fun _ hc=>(Finset.mem_singleton.mp hc) ▸ hb
theorem qa2' {a c : V} {A : Finset V} (h₁ : c≠a) (h₂ : c∉A) : c∉insert a A:=by
  simp [h₁,h₂]
theorem qf5 {a b c : V} (ha : c≠a) (hb : c≠b) : c∉({a,b} : Finset V):=by
  simp [ha,hb]
theorem qo7 {a b : V} (h : G.Adj a b) : CliqueIn G {a,b} :=
  qb0 (qb0 (fun h'=>absurd rfl h') fun _=>h)
    (qb0 (fun _=>h.symm) fun h'=>absurd rfl h')
theorem qai9 {a b : V} (h : ¬ G.Adj a b) : IndepIn G {a,b} :=
  qb0 (qb0 (G.irrefl) h) (qb0 (fun h'=>h h'.symm) G.irrefl)
theorem IndepIn.insert {A : Finset V} {a : V} (hA : IndepIn G A) (ha : ∀ c∈A,¬ G.Adj a c) :
    IndepIn G (insert a A) :=
  qa9' (qa9' G.irrefl ha)
    fun c hc=>qa9' (fun h=>ha c hc h.symm) (hA c hc)
end Constructors
section PathsIn
variable {G : SimpleGraph V}
def Pi0 (G : SimpleGraph V) (A : Finset V) (u v : V) (n : ℕ) : Prop :=
  ∃ p : G.Walk u v,p.IsPath∧p.length=n∧∀ c∈p.support,c∈A
theorem Pi0.mono {A B : Finset V} {u v : V} {n : ℕ} (h : Pi0 G A u v n) (hAB : A⊆B) :
    Pi0 G B u v n:=by
  obtain ⟨p,hp,hl,hs⟩:=h
  exact ⟨p,hp,hl,fun c hc=>hAB (hs c hc)⟩
theorem Pi0.len {A : Finset V} {u v : V} {n m : ℕ} (h : Pi0 G A u v n) (e : n=m) :
    Pi0 G A u v m :=
  e ▸ h
theorem Pi0.nil {A : Finset V} {u : V} (hu : u∈A) : Pi0 G A u u 0 :=
  ⟨Walk.nil,Walk.IsPath.nil,rfl,fun c hc=>by
    rw [Walk.support_nil,List.mem_singleton] at hc
    exact hc ▸ hu⟩
variable [DecidableEq V]
theorem Pi0.cons {A : Finset V} {u w v : V} {n : ℕ} (h : G.Adj u w) (hp : Pi0 G A w v n)
    (hu : u∉A) : Pi0 G (insert u A) u v (n+1):=by
  obtain ⟨p,hp,hl,hs⟩:=hp
  refine ⟨Walk.cons h p,(Walk.cons_isPath_iff h p).mpr ⟨hp,fun hm=>hu (hs u hm)⟩,
    by rw [Walk.length_cons,hl],fun c hc=>?_⟩
  rw [Walk.support_cons,List.mem_cons] at hc
  rcases hc with rfl|hc
  · exact Finset.mem_insert_self _ _
  · exact Finset.mem_insert_of_mem (hs c hc)
theorem Pi0.concat {A : Finset V} {u w v : V} {n : ℕ} (hp : Pi0 G A u w n)
    (h : G.Adj w v) (hv : v∉A) : Pi0 G (insert v A) u v (n+1):=by
  obtain ⟨p,hp,hl,hs⟩:=hp
  refine ⟨p.concat h,hp.concat (fun hm=>hv (hs v hm)) h,by rw [Walk.length_concat,hl],
    fun c hc=>?_⟩
  rw [Walk.support_concat,List.mem_append,List.mem_singleton] at hc
  rcases hc with hc|rfl
  · exact Finset.mem_insert_of_mem (hs c hc)
  · exact Finset.mem_insert_self _ _
theorem Pi0.edge {u v : V} (h : G.Adj u v) : Pi0 G {u,v} u v 1 :=
  (Pi0.nil (Finset.mem_singleton_self v)).cons h (by simpa using h.ne)
theorem CliqueIn.insert {K : Finset V} {a : V} (hK : CliqueIn G K) (ha : ∀ t∈K,G.Adj a t) :
    CliqueIn G (insert a K):=by
  intro u hu v hv huv
  rw [Finset.mem_insert] at hu hv
  rcases hu with rfl|hu <;> rcases hv with rfl|hv
  · exact absurd rfl huv
  · exact ha v hv
  · exact (ha u hu).symm
  · exact hK u hu v hv huv
theorem qg9 : ∀ (j : ℕ) (K : Finset V),CliqueIn G K→ ∀ u∈K,∀ v∈K,u≠v →
    1≤ j→ j+1≤ K.card→ Pi0 G K u v j
  | 0,_,_,_,_,_,_,_,h,_=>absurd h (by norm_num)
  | 1,K,hK,u,hu,v,hv,huv,_,_ =>
    (Pi0.edge (hK u hu v hv huv)).mono (by
      intro c hc
      rw [Finset.mem_insert,Finset.mem_singleton] at hc
      rcases hc with rfl|rfl
      exacts [hu,hv])
  | j+2,K,hK,u,hu,v,hv,huv,_,hc=>by
    obtain ⟨w,hw,hwuv⟩:=Finset.exists_mem_notMem_of_card_lt_card (s:={u,v}) (t:=K)
      (lt_of_le_of_lt Finset.card_le_two (by omega))
    simp only [Finset.mem_insert,Finset.mem_singleton,not_or] at hwuv
    have hp:=qg9 (j+1) (K.erase u) (hK.mono (Finset.erase_subset u K)) w
      (Finset.mem_erase.mpr ⟨hwuv.1,hw⟩) v (Finset.mem_erase.mpr ⟨huv.symm,hv⟩) hwuv.2
      (by omega) (by rw [Finset.card_erase_of_mem hu];omega)
    refine ((hp.cons (hK u hu w hw (Ne.symm hwuv.1)) (Finset.notMem_erase u K)).mono ?_).len rfl
    rw [Finset.insert_erase hu]
theorem qk4 : ∀ (m : ℕ) (A B : Finset V),(∀ a∈A,∀ b∈B,G.Adj b a) →
    ∀ a∈A,∀ b∈B,m+1≤ A.card→ m+1≤ B.card→ Pi0 G (A∪B) b a (2*m+1)
  | 0,A,B,hAB,a,ha,b,hb,_,_ =>
    (Pi0.edge (hAB a ha b hb)).mono (by
      intro c hc
      rw [Finset.mem_insert,Finset.mem_singleton] at hc
      rcases hc with rfl|rfl
      exacts [Finset.mem_union_right _ hb,Finset.mem_union_left _ ha])
  | m+1,A,B,hAB,a,ha,b,hb,hA,hB=>by
    obtain ⟨a',ha',ha'a⟩:=Finset.exists_mem_ne (by omega : 1 < A.card) a
    obtain ⟨b',hb',hb'b⟩:=Finset.exists_mem_ne (by omega : 1 < B.card) b
    have hp:=qk4 m (A.erase a') (B.erase b) (fun c hc d hd =>
      hAB c (Finset.mem_of_mem_erase hc) d (Finset.mem_of_mem_erase hd)) a
      (Finset.mem_erase.mpr ⟨ha'a.symm,ha⟩) b' (Finset.mem_erase.mpr ⟨hb'b,hb'⟩)
      (by rw [Finset.card_erase_of_mem ha'];omega) (by rw [Finset.card_erase_of_mem hb];omega)
    have h1 : a'∉A.erase a'∪B.erase b:=by
      rw [Finset.mem_union,not_or]
      exact ⟨Finset.notMem_erase a' A,
        fun h=>G.irrefl (hAB a' ha' a' (Finset.mem_of_mem_erase h))⟩
    have h2 : b∉insert a' (A.erase a'∪B.erase b):=by
      rw [Finset.mem_insert,Finset.mem_union,not_or,not_or]
      refine ⟨fun h=>?_,fun h=>G.irrefl (hAB b (Finset.mem_of_mem_erase h) b hb),
        Finset.notMem_erase b B⟩
      subst h
      exact G.irrefl (hAB _ ha' _ hb)
    refine (((hp.cons (hAB a' ha' b' hb').symm h1).cons (hAB a' ha' b hb) h2).mono ?_).len
      (by ring)
    intro c hc
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_erase] at hc
    rcases hc with rfl|rfl|⟨-,hc⟩|⟨-,hc⟩
    · exact Finset.mem_union_right _ hb
    · exact Finset.mem_union_left _ ha'
    · exact Finset.mem_union_left _ hc
    · exact Finset.mem_union_right _ hc
theorem qx5 (m : ℕ) {A B : Finset V} (hAB : ∀ a∈A,∀ b∈B,G.Adj b a)
    {b b' : V} (hb : b∈B) (hb' : b'∈B) (hne : b≠b') (hA : m+1≤ A.card)
    (hB : m+2≤ B.card) : Pi0 G (A∪B) b b' (2*m+2):=by
  obtain ⟨a,ha⟩:=Finset.card_pos.mp (by omega : 0 < A.card)
  have hp:=qk4 m A (B.erase b') (fun c hc d hd =>
    hAB c hc d (Finset.mem_of_mem_erase hd)) a ha b (Finset.mem_erase.mpr ⟨hne,hb⟩) hA
    (by rw [Finset.card_erase_of_mem hb'];omega)
  have h1 : b'∉A∪B.erase b':=by
    rw [Finset.mem_union,not_or]
    exact ⟨fun h=>G.irrefl (hAB b' h b' hb'),Finset.notMem_erase b' B⟩
  refine ((hp.concat (hAB a ha b' hb').symm h1).mono ?_).len rfl
  intro c hc
  simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_erase] at hc
  rcases hc with rfl|hc|⟨-,hc⟩
  · exact Finset.mem_union_right _ hb'
  · exact Finset.mem_union_left _ hc
  · exact Finset.mem_union_right _ hc
end PathsIn
section CorePaths
variable {G : SimpleGraph V} [DecidableEq V] {x y : V}
theorem Cc0.subset_verts {H : Cc0 G x y} {A : Finset V}
    (h : ∀ c∈A,c=x∨c∈H.S∨c∈H.T) : A⊆H.verts :=
  fun c hc=>Cc0.mem_verts.mpr (h c hc)
theorem qx1 (H : Cc0 G x y) (hk : H.kind=.t1) {t : V} (ht : t∈H.T) :
    ∀ j∈Finset.Icc 1 (H.ell+1),Pi0 G H.verts x t j:=by
  intro j hj
  rw [Finset.mem_Icc,H.ell_t1 hk] at hj
  obtain ⟨hS,hT,hxT,hK⟩:=H.shape1 hk
  refine (qg9 j _ (hK.insert hxT) x (Finset.mem_insert_self _ _) t
    (Finset.mem_insert_of_mem ht) (fun h=>H.x_notMem_T (h ▸ ht)) hj.1 ?_).mono ?_
  · rw [Finset.card_insert_of_notMem H.x_notMem_T]
    omega
  · intro c hc
    rw [Cc0.verts,hS,Finset.empty_union]
    exact hc
theorem ql6 (H : Cc0 G x y) (hk : H.kind=.t2) {t : V} (ht : t∈H.T) :
    ∀ j∈Finset.Icc 2 (H.ell+2),Pi0 G H.verts x t j:=by
  intro j hj
  rw [Finset.mem_Icc,H.ell_t2 hk] at hj
  obtain ⟨hS,hT,hxS,-,hKT,hST⟩:=H.shape2 hk
  obtain ⟨s₁,hs₁,s₂,hs₂,hne⟩:=Finset.one_lt_card.mp (by omega : 1 < H.S.card)
  have hs₂T : s₂∉H.T:=Finset.disjoint_left.mp H.disj hs₂
  have hs₁K : s₁∉insert s₂ H.T:=by
    rw [Finset.mem_insert,not_or]
    exact ⟨hne,Finset.disjoint_left.mp H.disj hs₁⟩
  have hxK : x∉insert s₁ (insert s₂ H.T):=by
    simp only [Finset.mem_insert,not_or]
    exact ⟨(hxS s₁ hs₁).ne,(hxS s₂ hs₂).ne,H.x_notMem_T⟩
  have hsub : insert x (insert s₁ (insert s₂ H.T))⊆H.verts:=Cc0.subset_verts fun c hc=>by
    simp only [Finset.mem_insert] at hc
    rcases hc with rfl|rfl|rfl|hc
    exacts [Or.inl rfl,Or.inr (Or.inl hs₁),Or.inr (Or.inl hs₂),Or.inr (Or.inr hc)]
  rcases Nat.lt_or_ge j 3 with hj3|hj3
  · exact ((((Pi0.nil (Finset.mem_insert_of_mem ht)).cons (hST s₁ hs₁ t ht) hs₁K).cons
      (hxS s₁ hs₁) hxK).mono hsub).len (by omega)
  · obtain ⟨t',ht',ht't⟩:=Finset.exists_mem_ne (by omega : 1 < H.T.card) t
    have hp:=qg9 (j - 2) _ (hKT.insert (hST s₂ hs₂)) t' (Finset.mem_insert_of_mem ht')
      t (Finset.mem_insert_of_mem ht) ht't (by omega)
      (by rw [Finset.card_insert_of_notMem hs₂T];omega)
    exact (((hp.cons (hST s₁ hs₁ t' ht') hs₁K).cons (hxS s₁ hs₁) hxK).mono hsub).len (by omega)
theorem qh8 (H : Cc0 G x y) (hk : H.kind=.t2) {s : V} (hs : s∈H.S) :
    ∀ j∈insert 1 (Finset.Icc 3 (H.ell+2)),Pi0 G H.verts x s j:=by
  intro j hj
  obtain ⟨hS,hT,hxS,-,hKT,hST⟩:=H.shape2 hk
  rw [Finset.mem_insert,Finset.mem_Icc,H.ell_t2 hk] at hj
  rcases hj with rfl|hj
  · refine (Pi0.edge (hxS s hs)).mono (Cc0.subset_verts fun c hc=>?_)
    rw [Finset.mem_insert,Finset.mem_singleton] at hc
    rcases hc with rfl|rfl
    exacts [Or.inl rfl,Or.inr (Or.inl hs)]
  obtain ⟨s',hs',hs's⟩:=Finset.exists_mem_ne (by omega : 1 < H.S.card) s
  obtain ⟨t',ht'⟩:=Finset.card_pos.mp (by omega : 0 < H.T.card)
  have hsT : s∉H.T:=Finset.disjoint_left.mp H.disj hs
  have hs'K : s'∉insert s H.T:=by
    rw [Finset.mem_insert,not_or]
    exact ⟨hs's,Finset.disjoint_left.mp H.disj hs'⟩
  have hxK : x∉insert s' (insert s H.T):=by
    simp only [Finset.mem_insert,not_or]
    exact ⟨(hxS s' hs').ne,(hxS s hs).ne,H.x_notMem_T⟩
  have hsub : insert x (insert s' (insert s H.T))⊆H.verts:=Cc0.subset_verts fun c hc=>by
    simp only [Finset.mem_insert] at hc
    rcases hc with rfl|rfl|rfl|hc
    exacts [Or.inl rfl,Or.inr (Or.inl hs'),Or.inr (Or.inl hs),Or.inr (Or.inr hc)]
  have hp:=qg9 (j - 2) _ (hKT.insert (hST s hs)) t' (Finset.mem_insert_of_mem ht') s
    (Finset.mem_insert_self _ _) (fun h=>hsT (h ▸ ht')) (by omega)
    (by rw [Finset.card_insert_of_notMem hsT];omega)
  exact (((hp.cons (hST s' hs' t' ht') hs'K).cons (hxS s' hs') hxK).mono hsub).len (by omega)
theorem ql4 (H : Cc0 G x y) (hk : H.kind=.t3) {A : Finset V}
    (hA : A⊆H.T) (hcard : H.ell+1≤ A.card) {t : V} (ht : t∈A) (i : Fin (H.ell+1)) :
    Pi0 G (insert x (H.S∪A)) x t (1+2*i.val):=by
  obtain ⟨-,-,hxT,-,-,hST⟩:=H.shape3 hk
  have hi:=i.isLt
  have hAB : ∀ a∈A,∀ b∈insert x H.S,G.Adj b a:=by
    intro a ha b hb
    rcases Finset.mem_insert.mp hb with rfl|hb
    · exact hxT a (hA ha)
    · exact hST b hb a (hA ha)
  have hB : (insert x H.S).card=H.ell+1:=by
    rw [Finset.card_insert_of_notMem H.x_notMem_S,H.ell_t3 hk]
  refine ((qk4 i.val A _ hAB t ht x (Finset.mem_insert_self _ _) (by omega)
    (by omega)).mono ?_).len (by ring)
  intro c hc
  simp only [Finset.mem_union,Finset.mem_insert] at hc ⊢
  tauto
theorem ql5 (H : Cc0 G x y) (hk : H.kind=.t3) {t : V} (ht : t∈H.T) :
    ∀ i : Fin (H.ell+1),Pi0 G H.verts x t (1+2*i.val):=fun i =>
  ql4 H hk subset_rfl (by have:=(H.shape3 hk).1;rw [H.ell_t3 hk];omega) ht i
theorem qaj3 (H : Cc0 G x y) (hk : H.kind=.t3) {t t' : V} (ht : t∈H.T)
    (ht' : t'∈H.T) (hne : t≠t') (hc : H.ell+2≤ H.T.card) :
    ∀ i : Fin (H.ell+1),Pi0 G (H.verts.erase t') x t (1+2*i.val):=by
  intro i
  refine (ql4 H hk (Finset.erase_subset t' H.T)
    (by rw [Finset.card_erase_of_mem ht'];omega) (Finset.mem_erase.mpr ⟨hne,ht⟩) i).mono ?_
  intro c hc
  rw [Finset.mem_erase]
  simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_erase] at hc
  rcases hc with rfl|hcS|⟨hct,hcT⟩
  · exact ⟨fun h=>H.x_notMem_T (h ▸ ht'),H.x_mem_verts⟩
  · exact ⟨fun h=>Finset.disjoint_left.mp H.disj hcS (h ▸ ht'),H.S_subset_verts hcS⟩
  · exact ⟨hct,H.T_subset_verts hcT⟩
theorem qr0 (H : Cc0 G x y) (hk : H.kind=.t3) {s t₀ : V} (hs : s∈H.S)
    (ht₀ : t₀∈H.T) : ∀ i : Fin H.ell,Pi0 G (H.verts.erase t₀) x s (2+2*i.val):=by
  intro i
  obtain ⟨hc,-,hxT,-,-,hST⟩:=H.shape3 hk
  have hl:=H.ell_t3 hk
  have hi:=i.isLt
  have hAB : ∀ a∈H.T.erase t₀,∀ b∈insert x H.S,G.Adj b a:=by
    intro a ha b hb
    rcases Finset.mem_insert.mp hb with rfl|hb
    · exact hxT a (Finset.mem_of_mem_erase ha)
    · exact hST b hb a (Finset.mem_of_mem_erase ha)
  have hB : (insert x H.S).card=H.ell+1:=by
    rw [Finset.card_insert_of_notMem H.x_notMem_S,hl]
  have hA : (H.T.erase t₀).card=H.T.card - 1:=Finset.card_erase_of_mem ht₀
  refine ((qx5 i.val hAB (Finset.mem_insert_self x H.S)
    (Finset.mem_insert_of_mem hs) (fun h=>H.x_notMem_S (h ▸ hs)) (by omega)
    (by omega)).mono ?_).len (by ring)
  intro c hc
  rw [Finset.mem_erase]
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_erase] at hc
  rcases hc with ⟨hct,hcT⟩|rfl|hcS
  · exact ⟨hct,H.T_subset_verts hcT⟩
  · exact ⟨fun h=>H.x_notMem_T (h ▸ ht₀),H.x_mem_verts⟩
  · exact ⟨fun h=>Finset.disjoint_left.mp H.disj hcS (h ▸ ht₀),H.S_subset_verts hcS⟩
theorem qah5 (H : Cc0 G x y) {t : V} (ht : t∈H.T) :
    ∃ a d : ℕ,1≤ a∧(d=1∨d=2) ∧
      ∀ i : Fin (H.ell+1),Pi0 G H.verts x t (a+i.val*d):=by
  cases hk : H.kind
  · refine ⟨1,1,le_rfl,Or.inl rfl,fun i=>?_⟩
    have hi:=i.isLt
    exact qx1 H hk ht _ (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  · refine ⟨2,1,by norm_num,Or.inl rfl,fun i=>?_⟩
    have hi:=i.isLt
    exact ql6 H hk ht _ (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
  · exact ⟨1,2,le_rfl,Or.inr rfl,fun i=>(ql5 H hk ht i).len (by ring)⟩
theorem qah6 (H : Cc0 G x y) {s : V} (hs : s∈H.S) :
    ∃ a d : ℕ,2≤ a∧(d=1∨d=2) ∧
      ∀ i : Fin H.ell,Pi0 G H.verts x s (a+i.val*d):=by
  cases hk : H.kind
  · rw [(H.shape1 hk).1] at hs
    exact absurd hs (Finset.notMem_empty s)
  · refine ⟨3,1,by norm_num,Or.inl rfl,fun i=>?_⟩
    have hi:=i.isLt
    exact qh8 H hk hs _
      (Finset.mem_insert_of_mem (Finset.mem_Icc.mpr ⟨by omega,by omega⟩))
  · obtain ⟨t₀,ht₀⟩:=Finset.card_pos.mp (by have:=H.two_le_T;omega : 0 < H.T.card)
    exact ⟨2,2,le_rfl,Or.inr rfl,fun i =>
      ((qr0 H hk hs ht₀ i).mono (Finset.erase_subset _ _)).len (by ring)⟩
end CorePaths
section Fact3
variable {G : SimpleGraph V} {x y : V}
theorem qj9 {A : Finset V} {r : V} {n a d : ℕ} (hd : d=1∨d=2)
    (hP : ∀ i : Fin n,Pi0 G A x r (a+i.val*d)) {Q : G.Walk r y} (hQ : Q.IsPath)
    (hQA : ∀ c∈Q.support,c∈A→ c=r) (ha : 2≤ a+Q.length) : Adm0 G x y n:=by
  refine ⟨a+Q.length,d,ha,hd,fun i=>?_⟩
  obtain ⟨p,hp,hl,hs⟩:=hP i
  obtain ⟨h1,h2,-⟩:=qa3 hp hQ fun c hc1 hc2=>hQA c hc2 (hs c hc1)
  exact ⟨p.append Q,h1,by rw [h2,hl];ring⟩
variable [DecidableEq V]
theorem qu5 (H : Cc0 G x y) {q : ℕ} (hq : ¬ Adm0 G x y q) {r : V}
    (hr : r∈H.T) {Q : G.Walk r y} (hQ : Q.IsPath) (hQA : ∀ c∈Q.support,c∈H.verts→ c=r)
    (hQl : 1≤ Q.length) : H.ell+2≤ q:=by
  by_contra hlt
  obtain ⟨a,d,ha,hd,hP⟩:=qah5 H hr
  exact hq (qc0 (by omega) (qj9 hd hP hQ hQA (by omega)))
theorem qak8 (H : Cc0 G x y) {q : ℕ} (hq : ¬ Adm0 G x y q) {r : V}
    (hr : r∈H.S) {Q : G.Walk r y} (hQ : Q.IsPath) (hQA : ∀ c∈Q.support,c∈H.verts→ c=r)
    (hQl : 1≤ Q.length) : H.ell+1≤ q:=by
  by_contra hlt
  obtain ⟨a,d,ha,hd,hP⟩:=qah6 H hr
  exact hq (qc0 (by omega) (qj9 hd hP hQ hQA (by omega)))
variable [Fintype V]
theorem qah3 {A : Finset V} {c t : V} (hc : Rc0 G Aᶜ y c) (ht : t∈A)
    (hct : G.Adj c t) :
    ∃ Q : G.Walk t y,Q.IsPath∧(∀ v∈Q.support,v∈A→ v=t)∧1≤ Q.length:=by
  obtain ⟨w,hw⟩:=hc
  obtain ⟨p,hp,hps,-⟩:=qz1 w
  have hout : ∀ v∈p.reverse.support,v∉A:=fun v hv =>
    Finset.mem_compl.mp (hw v (hps (by simpa using hv)))
  refine ⟨Walk.cons hct.symm p.reverse,
    (Walk.cons_isPath_iff _ _).mpr ⟨hp.reverse,fun h=>hout t h ht⟩,fun v hv hvA=>?_,
    by simp⟩
  rw [Walk.support_cons,List.mem_cons] at hv
  rcases hv with rfl|hv
  · rfl
  · exact absurd hvA (hout v hv)
theorem qac6 (hG : Kc0 G 2) {A : Finset V} {u : V} (hx : x∈A) (hy : y∉A)
    (hu : u∈A) (hux : u≠x) :
    ∃ r∈A,r≠x∧∃ Q : G.Walk r y,Q.IsPath∧(∀ v∈Q.support,v∈A→ v=r) ∧
      1≤ Q.length:=by
  obtain ⟨-,hl⟩:=kConn_two_iff.mp hG
  have hyx : y≠x:=fun h=>hy (h ▸ hx)
  obtain ⟨w,hw⟩:=hl x y (by simp [hyx]) u (by simp [hux])
  obtain ⟨p,hp,hps,-⟩:=qz1 w
  obtain ⟨r,hr,q,hqs,hqA,hqp⟩:=qe9 (G:=G) (·∈A) p hu
  have hrx : r≠x:=fun h =>
    Finset.notMem_erase x _ (h ▸ hw r (hps (hqs r q.end_mem_support)))
  refine ⟨r,hr,hrx,q.reverse,(hqp hp).reverse,
    fun v hv hvA=>hqA v (by simpa using hv) hvA,?_⟩
  have:=qd2 q (fun h=>hy (h ▸ hr))
  rw [Walk.length_reverse]
  omega
theorem qak9 (hG : Kc0 G 2) (H : Cc0 G x y) {q : ℕ}
    (hq : ¬ Adm0 G x y q) : H.ell+1≤ q:=by
  obtain ⟨t,ht⟩:=Finset.card_pos.mp (by have:=H.two_le_T;omega : 0 < H.T.card)
  obtain ⟨r,hr,hrx,Q,hQ,hQA,hQl⟩:=qac6 hG H.x_mem_verts H.y_notMem_verts
    (H.T_subset_verts ht) (fun h=>H.x_notMem_T (h ▸ ht))
  rcases Cc0.mem_verts.mp hr with h|h|h
  · exact absurd h hrx
  · exact qak8 H hq h hQ hQA hQl
  · have:=qu5 H hq h hQ hQA hQl
    omega
theorem qj7 (H : Cc0 G x y) {q : ℕ} (hq : ¬ Adm0 G x y q) {c t : V}
    (hc : Rc0 G H.vertsᶜ y c) (ht : t∈H.T) (hct : G.Adj c t) : H.ell+2≤ q:=by
  obtain ⟨Q,hQ,hQA,hQl⟩:=qah3 hc (H.T_subset_verts ht) hct
  exact qu5 H hq ht hQ hQA hQl
theorem qt1 (hG : Kc0 G 2) (H : Cc0 G x y) (hk : H.kind=.t1) {q : ℕ}
    (hq : ¬ Adm0 G x y q) : H.ell+2≤ q:=by
  obtain ⟨t,ht⟩:=Finset.card_pos.mp (by have:=H.two_le_T;omega : 0 < H.T.card)
  obtain ⟨r,hr,hrx,Q,hQ,hQA,hQl⟩:=qac6 hG H.x_mem_verts H.y_notMem_verts
    (H.T_subset_verts ht) (fun h=>H.x_notMem_T (h ▸ ht))
  rcases Cc0.mem_verts.mp hr with h|h|h
  · exact absurd h hrx
  · rw [(H.shape1 hk).1] at h
    exact absurd h (Finset.notMem_empty r)
  · exact qu5 H hq h hQ hQA hQl
end Fact3
section Selection
def qr6 [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (z : Option V) (a b : V) :
    Prop :=
  G.degree a≤ G.degree b ∧
    (G.degree a=G.degree b→ ∀ w,z=some w→ G.dist a w≤ G.dist b w)
variable {G : SimpleGraph V} {x y : V}
def Ibc0 (H : Cc0 G x y) : Prop :=
  (∀ H' : Cc0 G x y,H.kind.rank≤ H'.kind.rank) ∧
    ∀ H' : Cc0 G x y,H'.kind=H.kind →
      H'.ell≤ H.ell∧(H'.ell=H.ell→ H'.T.card≤ H.T.card)
def Ioc0 [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (x y : V) (z : Option V)
    (H : Cc0 G x y) : Prop :=
  Ibc0 H∧(∀ H' : Cc0 G y x,H.kind.rank≤ H'.kind.rank) ∧
    ∀ H' : Cc0 G y x,H'.kind.rank=H.kind.rank→ qr6 G z x y
theorem Ibc0.ell_ge {H : Cc0 G x y} (hH : Ibc0 H) (H' : Cc0 G x y)
    (hk : H'.kind=H.kind) : H'.ell≤ H.ell :=
  (hH.2 H' hk).1
theorem Ibc0.rank_ge {H : Cc0 G x y} (hH : Ibc0 H) {k : Ck0}
    (hk : H.kind=k) (H' : Cc0 G x y) : k.rank≤ H'.kind.rank :=
  hk ▸ hH.1 H'
theorem qn9 {P : ℕ→ Prop} (B : ℕ) (hP : ∃ n,P n) (hB : ∀ n,P n→ n≤ B) :
    ∃ n,P n∧∀ m,P m→ m≤ n:=by
  classical
  obtain ⟨n,hn⟩:=hP
  exact ⟨Nat.findGreatest P B,Nat.findGreatest_spec (hB n hn) hn,
    fun m hm=>Nat.le_findGreatest (hB m hm) hm⟩
theorem qu4 [Fintype V] (k : Ck0) (h : ∃ H : Cc0 G x y,H.kind=k) :
    ∃ H : Cc0 G x y,H.kind=k∧∀ H' : Cc0 G x y,H'.kind=k →
      H'.ell≤ H.ell∧(H'.ell=H.ell→ H'.T.card≤ H.T.card):=by
  obtain ⟨m,⟨H₁,hk₁,hm₁⟩,hmax⟩ :=
    qn9 (P:=fun m=>∃ H : Cc0 G x y,H.kind=k∧H.ell=m)
      (Fintype.card V) (h.elim fun H hH=>⟨H.ell,H,hH,rfl⟩)
      (fun m ⟨H,_,hm⟩=>hm ▸ H.ell_le_card)
  obtain ⟨n,⟨H,hk,hm,hn⟩,hnmax⟩ :=
    qn9 (P:=fun n=>∃ H : Cc0 G x y,H.kind=k∧H.ell=m∧H.T.card=n)
      (Fintype.card V) ⟨_,H₁,hk₁,hm₁,rfl⟩ (fun n ⟨H,_,_,hn⟩=>hn ▸ Finset.card_le_univ _)
  refine ⟨H,hk,fun H' hk'=>⟨?_,fun he=>?_⟩⟩
  · rw [hm]
    exact hmax _ ⟨H',hk',rfl⟩
  · rw [hn]
    exact hnmax _ ⟨H',hk',he.trans hm,rfl⟩
variable [Fintype V] [DecidableRel G.Adj]
theorem qaa3 (z : Option V) (a b : V) : qr6 G z a b∨qr6 G z b a:=by
  rcases lt_trichotomy (G.degree a) (G.degree b) with h|h|h
  · exact Or.inl ⟨h.le,fun e=>absurd e h.ne⟩
  · cases z with
    | none=>exact Or.inl ⟨h.le,fun _ w hw=>by cases hw⟩
    | some w =>
      rcases le_total (G.dist a w) (G.dist b w) with h'|h'
      · exact Or.inl ⟨h.le,fun _ w' hw'=>by cases hw';exact h'⟩
      · exact Or.inr ⟨h.ge,fun _ w' hw'=>by cases hw';exact h'⟩
  · exact Or.inr ⟨h.le,fun e=>absurd e h.ne⟩
theorem qu3 [DecidableEq V] (hG : Kc0 G 2) (hxy : x≠y) (hadj : ¬ G.Adj x y) :
    Nonempty (Cc0 G x y):=by
  by_cases h : ∃ t∈G.neighborFinset x,∃ t'∈G.neighborFinset x,G.Adj t t'
  · obtain ⟨t,ht,t',ht',htt'⟩:=h
    rw [mem_neighborFinset] at ht ht'
    exact ⟨Cc0.mk1 hxy {t,t'} (Finset.card_pair htt'.ne).ge (qb0 ht ht')
      (qo7 htt') (qf5 (fun h=>hadj (h ▸ ht)) (fun h=>hadj (h ▸ ht')))⟩
  · simp only [not_exists,not_and] at h
    have hd:=qe8 hG x
    rw [← card_neighborFinset_eq_degree] at hd
    exact ⟨Cc0.mk3 hxy ∅ (G.neighborFinset x) (by rw [Finset.card_empty];omega) hd
      (fun t ht=>(mem_neighborFinset _ _ _).mp ht) (fun a ha=>absurd ha (Finset.notMem_empty a))
      h (fun s hs=>absurd hs (Finset.notMem_empty s)) (Finset.notMem_empty x)
      (Finset.notMem_empty y) (fun hy=>hadj ((mem_neighborFinset _ _ _).mp hy))⟩
theorem qj0 (z : Option V) (r₀ : ℕ) (h₁ : ∀ H : Cc0 G x y,r₀≤ H.kind.rank)
    (h₂ : ∀ H : Cc0 G y x,r₀≤ H.kind.rank) (H₀ : Cc0 G x y) (hH₀ : H₀.kind.rank=r₀)
    (hpref : ∀ H' : Cc0 G y x,H'.kind.rank=r₀→ qr6 G z x y) :
    ∃ H : Cc0 G x y,Ioc0 G x y z H:=by
  obtain ⟨H,hk,hbest⟩:=qu4 H₀.kind ⟨H₀,rfl⟩
  have hr : H.kind.rank=r₀:=by rw [hk,hH₀]
  refine ⟨H,⟨fun H'=>hr ▸ h₁ H',fun H' hk'=>hbest H' (hk'.trans hk)⟩,fun H'=>hr ▸ h₂ H',
    fun H' hH'=>hpref H' (hH'.trans hr)⟩
theorem qu2 [DecidableEq V] (hG : Kc0 G 2) (hxy : x≠y) (hadj : ¬ G.Adj x y)
    (z : Option V) :
    (∃ H : Cc0 G x y,Ioc0 G x y z H) ∨
      ∃ H : Cc0 G y x,Ioc0 G y x z H:=by
  classical
  obtain ⟨H₁⟩:=qu3 hG hxy hadj
  have hP : ∃ r,(∃ H : Cc0 G x y,H.kind.rank=r)∨∃ H : Cc0 G y x,H.kind.rank=r :=
    ⟨_,Or.inl ⟨H₁,rfl⟩⟩
  have hm₁ : ∀ H : Cc0 G x y,Nat.find hP≤ H.kind.rank:=fun H =>
    Nat.find_min' hP (Or.inl ⟨H,rfl⟩)
  have hm₂ : ∀ H : Cc0 G y x,Nat.find hP≤ H.kind.rank:=fun H =>
    Nat.find_min' hP (Or.inr ⟨H,rfl⟩)
  by_cases hB : ∃ H : Cc0 G y x,H.kind.rank=Nat.find hP
  · obtain ⟨H₂,hH₂⟩:=hB
    by_cases hA : ∃ H : Cc0 G x y,H.kind.rank=Nat.find hP
    · obtain ⟨H₀,hH₀⟩:=hA
      rcases qaa3 (G:=G) z x y with h|h
      · exact Or.inl (qj0 z _ hm₁ hm₂ H₀ hH₀ fun _ _=>h)
      · exact Or.inr (qj0 z _ hm₂ hm₁ H₂ hH₂ fun _ _=>h)
    · exact Or.inr (qj0 z _ hm₂ hm₁ H₂ hH₂ fun H' hH'=>absurd ⟨H',hH'⟩ hA)
  · obtain ⟨H₀,hH₀⟩:=(Nat.find_spec hP).resolve_right hB
    exact Or.inl (qj0 z _ hm₁ hm₂ H₀ hH₀ fun H' hH'=>absurd ⟨H',hH'⟩ hB)
end Selection
section Claim33
variable {G : SimpleGraph V} {x y : V}
theorem qe1 [DecidableRel G.Adj] {T : Finset V} {v : V}
    (h : 0 < (T.filter (G.Adj v)).card) : ∃ t∈T,G.Adj v t:=by
  obtain ⟨t,ht⟩:=Finset.card_pos.mp h
  exact ⟨t,(Finset.mem_filter.mp ht).1,(Finset.mem_filter.mp ht).2⟩
variable [DecidableEq V]
theorem qg7 (hmin : ∀ H' : Cc0 G x y,2≤ H'.kind.rank) (hxy : x≠y) {v t : V}
    (hxv : G.Adj x v) (hxt : G.Adj x t) (hvt : G.Adj v t) (hvy : v≠y) (hty : t≠y) : False :=
  absurd (hmin (Cc0.mk1 hxy {v,t} (Finset.card_pair hvt.ne).ge (qb0 hxv hxt)
    (qo7 hvt) (qf5 hvy.symm hty.symm))) (by simp [Ck0.rank])
theorem qab5 (hmin : ∀ H' : Cc0 G x y,3≤ H'.kind.rank) (hxy : x≠y)
    {v s t₁ t₂ : V} (h12 : t₁≠t₂) (hn12 : ¬ G.Adj t₁ t₂) (hx₁ : G.Adj x t₁) (hx₂ : G.Adj x t₂)
    (hv₁ : G.Adj v t₁) (hv₂ : G.Adj v t₂) (hs₁ : G.Adj s t₁) (hs₂ : G.Adj s t₂) (hvs : G.Adj v s)
    (hxv : x≠v) (hxs : x≠s) (hvy : v≠y) (hsy : s≠y) (h1y : t₁≠y) (h2y : t₂≠y) :
    False :=
  absurd (hmin (Cc0.mk2 hxy {t₁,t₂} {v,s} (Finset.card_pair h12)
    (Finset.card_pair hvs.ne).ge (qb0 hx₁ hx₂) (qai9 hn12) (qo7 hvs)
    (qb0 (qb0 hv₁.symm hs₁.symm) (qb0 hv₂.symm hs₂.symm))
    (qf5 hxv hxs) (qf5 h1y.symm h2y.symm) (qf5 hvy.symm hsy.symm)))
    (by simp [Ck0.rank])
variable [DecidableRel G.Adj]
theorem qt4 (hmin : ∀ H' : Cc0 G x y,3≤ H'.kind.rank) {H : Cc0 G x y}
    (hk : H.kind=.t3) {v : V} (hv : v∉H.verts) (hvy : v≠y)
    (h2 : 2≤ (H.T.filter (G.Adj v)).card) : ∀ s∈H.S,¬ G.Adj v s:=by
  intro s hs hvs
  obtain ⟨-,-,hxT,-,hIT,hST⟩:=H.shape3 hk
  obtain ⟨t₁,ht₁,t₂,ht₂,h12⟩:=Finset.one_lt_card.mp (by omega :
    1 < (H.T.filter (G.Adj v)).card)
  rw [Finset.mem_filter] at ht₁ ht₂
  exact qab5 hmin H.x_ne_y h12 (hIT _ ht₁.1 _ ht₂.1) (hxT _ ht₁.1) (hxT _ ht₂.1)
    ht₁.2 ht₂.2 (hST s hs _ ht₁.1) (hST s hs _ ht₂.1) hvs (qa0 H.x_mem_verts hv)
    (qa0 hs H.x_notMem_S).symm hvy (qa0 hs H.y_notMem_S)
    (qa0 ht₁.1 H.y_notMem_T) (qa0 ht₂.1 H.y_notMem_T)
variable [Fintype V]
theorem qv0 (H : Cc0 G x y) (v : V) :
    (G.neighborFinset v∩H.verts).card ≤
      (if G.Adj v x then 1 else 0)+(H.S.filter (G.Adj v)).card+(H.T.filter (G.Adj v)).card:=by
  have e : G.neighborFinset v∩H.verts=(insert x (H.S∪H.T)).filter (G.Adj v):=by
    ext c
    simp [Cc0.verts,and_comm]
  rw [e,Finset.filter_insert,Finset.filter_union]
  have:=Finset.card_union_le (H.S.filter (G.Adj v)) (H.T.filter (G.Adj v))
  split_ifs
  · have:=Finset.card_insert_le x (H.S.filter (G.Adj v)∪H.T.filter (G.Adj v))
    omega
  · omega
theorem qw6 {H : Cc0 G x y} (hk : H.kind=.t3) {v : V}
    (h1 : G.Adj v x→ ∀ t∈H.T,¬ G.Adj v t)
    (h2 : 2≤ (H.T.filter (G.Adj v)).card→ ∀ s∈H.S,¬ G.Adj v s)
    (h3 : (H.T.filter (G.Adj v)).card≤ H.S.card+1)
    (h4 : G.Adj v x→ ¬ ∀ s∈H.S,G.Adj v s) :
    (G.neighborFinset v∩H.verts).card≤ H.ell+1 ∧
      ((G.neighborFinset v∩H.verts).card=H.ell+1→ ¬ G.Adj v x ∧
        ((H.S.filter (G.Adj v)).card=0∧(H.T.filter (G.Adj v)).card=H.ell+1 ∨
          (H.T.filter (G.Adj v)).card=1∧(H.S.filter (G.Adj v)).card=H.ell)):=by
  have hl:=H.ell_t3 hk
  have hc:=qv0 H v
  have hSf:=Finset.card_filter_le H.S (G.Adj v)
  by_cases hvx : G.Adj v x
  · rw [if_pos hvx,Finset.card_filter_eq_zero_iff.mpr (h1 hvx)] at hc
    have hlt : (H.S.filter (G.Adj v)).card < H.S.card :=
      lt_of_le_of_ne hSf fun he=>h4 hvx (Finset.card_filter_eq_iff.mp he)
    exact ⟨by omega,fun he=>absurd he (by omega)⟩
  · rw [if_neg hvx] at hc
    by_cases h2T : 2≤ (H.T.filter (G.Adj v)).card
    · have h0:=Finset.card_filter_eq_zero_iff.mpr (h2 h2T)
      exact ⟨by omega,fun he=>⟨hvx,Or.inl ⟨h0,by omega⟩⟩⟩
    · exact ⟨by omega,fun he=>⟨hvx,Or.inr ⟨by omega,by omega⟩⟩⟩
theorem qad0 {H : Cc0 G x y} (hH : Ibc0 H) (hk : H.kind=.t1) {v : V}
    (hv : v∉H.verts) (hvy : v≠y) :
    (G.neighborFinset v∩H.verts).card≤ H.ell+1 ∧
      ((G.neighborFinset v∩H.verts).card=H.ell+1→ ∃ t∈H.T,G.Adj v t):=by
  obtain ⟨hS,hT,hxT,hK⟩:=H.shape1 hk
  have hl:=H.ell_t1 hk
  have hc:=qv0 H v
  rw [hS,Finset.filter_empty,Finset.card_empty] at hc
  have hvT : v∉H.T:=fun h=>hv (H.T_subset_verts h)
  have hTf:=Finset.card_filter_le H.T (G.Adj v)
  refine ⟨?_,fun he=>qe1 ?_⟩
  · by_contra hlt
    have hvx : G.Adj v x:=by
      by_contra h
      rw [if_neg h] at hc
      omega
    rw [if_pos hvx] at hc
    have hall : ∀ t∈H.T,G.Adj v t:=Finset.card_filter_eq_iff.mp (by omega)
    have:=hH.ell_ge (Cc0.mk1 H.x_ne_y (insert v H.T)
      (by rw [Finset.card_insert_of_notMem hvT];omega) (qa9' hvx.symm hxT)
      (hK.insert hall) (qa2' hvy.symm H.y_notMem_T)) (by simp [hk])
    rw [Cc0.mk1_ell,Finset.card_insert_of_notMem hvT] at this
    omega
  · split_ifs at hc <;> omega
theorem qac9 {H : Cc0 G x y} (hH : Ibc0 H) (hk : H.kind=.t2) {v : V}
    (hv : v∉H.verts) (hvy : v≠y) :
    (G.neighborFinset v∩H.verts).card≤ H.ell+1 ∧
      ((G.neighborFinset v∩H.verts).card=H.ell+1→ ∃ t∈H.T,G.Adj v t):=by
  obtain ⟨hS2,hT,hxS,hIS,hKT,hST⟩:=H.shape2 hk
  have hl:=H.ell_t2 hk
  have hc:=qv0 H v
  have hvT : v∉H.T:=fun h=>hv (H.T_subset_verts h)
  have hSf:=Finset.card_filter_le H.S (G.Adj v)
  have hTf:=Finset.card_filter_le H.T (G.Adj v)
  have hx0 : G.Adj v x→ (H.S.filter (G.Adj v)).card=0:=fun hvx =>
    Finset.card_filter_eq_zero_iff.mpr fun s hs hvs=>qg7 (hH.rank_ge hk) H.x_ne_y
      hvx.symm (hxS s hs) hvs hvy (qa0 hs H.y_notMem_S)
  refine ⟨?_,fun he=>qe1 ?_⟩
  · by_contra hlt
    by_cases hvx : G.Adj v x
    · rw [if_pos hvx,hx0 hvx] at hc
      omega
    rw [if_neg hvx] at hc
    have hallS : ∀ s∈H.S,G.Adj v s:=Finset.card_filter_eq_iff.mp (by omega)
    have hallT : ∀ t∈H.T,G.Adj v t:=Finset.card_filter_eq_iff.mp (by omega)
    have:=hH.ell_ge (Cc0.mk2 H.x_ne_y H.S (insert v H.T) hS2
      (by rw [Finset.card_insert_of_notMem hvT];omega) hxS hIS (hKT.insert hallT)
      (fun s hs=>qa9' (hallS s hs).symm (hST s hs))
      (qa2' (qa0 H.x_mem_verts hv) H.x_notMem_T) H.y_notMem_S
      (qa2' hvy.symm H.y_notMem_T)) (by simp [hk])
    rw [Cc0.mk2_ell,Finset.card_insert_of_notMem hvT] at this
    omega
  · by_contra h0
    by_cases hvx : G.Adj v x
    · rw [if_pos hvx,hx0 hvx] at hc
      omega
    · rw [if_neg hvx] at hc
      omega
theorem qac8 {H : Cc0 G x y} (hH : Ibc0 H) (hk : H.kind=.t3) {v : V}
    (hv : v∉H.verts) (hvy : v≠y) :
    (G.neighborFinset v∩H.verts).card≤ H.ell+1 ∧
      ((G.neighborFinset v∩H.verts).card=H.ell+1→ ¬ G.Adj v x ∧
        ((H.S.filter (G.Adj v)).card=0∧(H.T.filter (G.Adj v)).card=H.ell+1 ∨
          (H.T.filter (G.Adj v)).card=1∧(H.S.filter (G.Adj v)).card=H.ell)):=by
  obtain ⟨hc3,hT2,hxT,hIS,hIT,hST⟩:=H.shape3 hk
  have hmin : ∀ H' : Cc0 G x y,3≤ H'.kind.rank:=hH.rank_ge hk
  have hxv : x≠v:=qa0 H.x_mem_verts hv
  have hvS : v∉H.S:=fun h=>hv (H.S_subset_verts h)
  have hvT : v∉H.T:=fun h=>hv (H.T_subset_verts h)
  have h1 : G.Adj v x→ ∀ t∈H.T,¬ G.Adj v t:=fun hvx t ht hvt =>
    qg7 (fun H'=>le_trans (by norm_num) (hmin H')) H.x_ne_y hvx.symm (hxT t ht) hvt
      hvy (qa0 ht H.y_notMem_T)
  have h2:=qt4 hmin hk hv hvy
  refine qw6 hk h1 h2 ?_ ?_
  · by_contra hlt
    have:=hH.ell_ge (Cc0.mk3 H.x_ne_y (insert v H.S) (H.T.filter (G.Adj v))
      (by rw [Finset.card_insert_of_notMem hvS];omega) (by omega)
      (fun t ht=>hxT t (Finset.mem_filter.mp ht).1) (hIS.insert (h2 (by omega)))
      (hIT.mono (Finset.filter_subset _ _))
      (qa9' (fun t ht=>(Finset.mem_filter.mp ht).2)
        fun s hs t ht=>hST s hs t (Finset.mem_filter.mp ht).1)
      (qa2' hxv H.x_notMem_S) (qa2' hvy.symm H.y_notMem_S)
      (fun h=>H.y_notMem_T (Finset.mem_filter.mp h).1)) (by simp [hk])
    rw [Cc0.mk3_ell,Finset.card_insert_of_notMem hvS,H.ell_t3 hk] at this
    omega
  · intro hvx hall
    have:=hH.2 (Cc0.mk3 H.x_ne_y H.S (insert v H.T)
      (by rw [Finset.card_insert_of_notMem hvT];omega)
      (by rw [Finset.card_insert_of_notMem hvT];omega) (qa9' hvx.symm hxT)
      hIS (hIT.insert (h1 hvx)) (fun s hs=>qa9' (hall s hs).symm (hST s hs))
      H.x_notMem_S H.y_notMem_S (qa2' hvy.symm H.y_notMem_T)) (by simp [hk])
    rw [Cc0.mk3_ell,Cc0.mk3_T,Finset.card_insert_of_notMem hvT,H.ell_t3 hk] at this
    have:=this.2 rfl
    omega
theorem ql7 {H : Cc0 G x y} (hH : Ibc0 H) {v : V} (hv : v∉H.verts)
    (hvy : v≠y) :
    (G.neighborFinset v∩H.verts).card≤ H.ell+1 ∧
      ((G.neighborFinset v∩H.verts).card=H.ell+1→ ∃ t∈H.T,G.Adj v t):=by
  cases hk : H.kind
  · exact qad0 hH hk hv hvy
  · exact qac9 hH hk hv hvy
  · obtain ⟨h1,h2⟩:=qac8 hH hk hv hvy
    refine ⟨h1,fun he=>qe1 ?_⟩
    rcases (h2 he).2 with ⟨-,h⟩|⟨h,-⟩ <;> omega
end Claim33
section Flat
variable {G : SimpleGraph V} {x y : V} [DecidableEq V]
def Ifo0 (H Hf : Cc0 G x y) (t₀ : V) : Prop :=
  H.kind=.t3∧t₀∈H.T∧Hf.kind=.t3∧Hf.T=H.T.erase t₀ ∧
    ((H.T.card=H.S.card+1∧∃ s₀∈H.S,Hf.S=H.S.erase s₀) ∨
      (H.S.card+2≤ H.T.card∧Hf.S=H.S))
theorem qak6 (H : Cc0 G x y) (hk : H.kind=.t3) {t₀ : V} (ht₀ : t₀∈H.T)
    (h3 : 3≤ H.T.card) : ∃ Hf : Cc0 G x y,Ifo0 H Hf t₀:=by
  have hc:=(H.shape3 hk).1
  have hTe : (H.T.erase t₀).card=H.T.card - 1:=Finset.card_erase_of_mem ht₀
  by_cases hM : H.T.card=H.S.card+1
  · obtain ⟨s₀,hs₀⟩:=Finset.card_pos.mp (by omega : 0 < H.S.card)
    have hSe : (H.S.erase s₀).card=H.S.card - 1:=Finset.card_erase_of_mem hs₀
    exact ⟨H.sub3 hk (H.S.erase s₀) (H.T.erase t₀) (Finset.erase_subset _ _)
      (Finset.erase_subset _ _) (by omega) (by omega),hk,ht₀,rfl,rfl,
      Or.inl ⟨hM,s₀,hs₀,rfl⟩⟩
  · exact ⟨H.sub3 hk H.S (H.T.erase t₀) subset_rfl (Finset.erase_subset _ _) (by omega)
      (by omega),hk,ht₀,rfl,rfl,Or.inr ⟨by omega,rfl⟩⟩
theorem Ifo0.S_subset {H Hf : Cc0 G x y} {t₀ : V} (hf : Ifo0 H Hf t₀) :
    Hf.S⊆H.S:=by
  rcases hf.2.2.2.2 with ⟨-,s₀,-,hS⟩|⟨-,hS⟩
  · rw [hS]
    exact Finset.erase_subset _ _
  · exact hS.subset
theorem Ifo0.T_subset {H Hf : Cc0 G x y} {t₀ : V} (hf : Ifo0 H Hf t₀) :
    Hf.T⊆H.T:=by
  rw [hf.2.2.2.1]
  exact Finset.erase_subset _ _
theorem Ifo0.verts_subset {H Hf : Cc0 G x y} {t₀ : V} (hf : Ifo0 H Hf t₀) :
    Hf.verts⊆H.verts :=
  Finset.insert_subset_insert x (Finset.union_subset_union hf.S_subset hf.T_subset)
theorem Ifo0.t₀_notMem {H Hf : Cc0 G x y} {t₀ : V} (hf : Ifo0 H Hf t₀) :
    t₀∉Hf.verts:=by
  rw [Cc0.mem_verts,hf.2.2.2.1]
  rintro (h|h|h)
  · exact H.x_notMem_T (h ▸ hf.2.1)
  · exact Finset.disjoint_left.mp H.disj (hf.S_subset h) hf.2.1
  · exact Finset.notMem_erase t₀ _ h
theorem Ifo0.ell {H Hf : Cc0 G x y} {t₀ : V} (hf : Ifo0 H Hf t₀) :
    Hf.T.card+1=H.T.card∧((H.T.card=H.ell+1∧Hf.ell+1=H.ell) ∨
      (H.ell+2≤ H.T.card∧Hf.ell=H.ell)):=by
  obtain ⟨hk,ht₀,hfk,hfT,hfS⟩:=hf
  have hT:=Finset.card_pos.mpr ⟨t₀,ht₀⟩
  rw [H.ell_t3 hk,Hf.ell_t3 hfk,hfT,Finset.card_erase_of_mem ht₀]
  refine ⟨by omega,?_⟩
  rcases hfS with ⟨hTS,s₀,hs₀,hS⟩|⟨hTS,hS⟩
  · have:=Finset.card_pos.mpr ⟨s₀,hs₀⟩
    rw [hS,Finset.card_erase_of_mem hs₀]
    exact Or.inl ⟨hTS,by omega⟩
  · rw [hS]
    exact Or.inr ⟨hTS,rfl⟩
variable [Fintype V] [DecidableRel G.Adj]
def Ft0 (z : Option V) (H : Cc0 G x y) (t₀ : V) : Prop :=
  H.kind=.t3∧3≤ H.T.card∧(∀ c,Rc0 G H.vertsᶜ y c→ c=y) ∧
    G.neighborFinset x=H.T∧G.neighborFinset y=H.T∧t₀∈H.T ∧
    ∃ d d₀,Rc0 G H.vertsᶜ d d₀∧G.Adj d₀ t₀∧d≠y∧z≠some d
theorem qp4 {z : Option V} {H : Cc0 G x y} {t₀ : V}
    (htr : Ft0 z H t₀) : ∃ Hf : Cc0 G x y,Ifo0 H Hf t₀ :=
  qak6 H htr.1 htr.2.2.2.2.2.1 htr.2.1
theorem qac3 {H Hf : Cc0 G x y} {t₀ : V} (hH : Ibc0 H)
    (hNx : G.neighborFinset x=H.T) (hf : Ifo0 H Hf t₀) {v : V} (hv : v∉Hf.verts)
    (hvy : v≠y) (hvt : v≠t₀) :
    (G.neighborFinset v∩Hf.verts).card≤ Hf.ell+1 ∧
      ((G.neighborFinset v∩Hf.verts).card=Hf.ell+1→ ∃ t∈Hf.T,G.Adj v t):=by
  have hTsub:=hf.T_subset
  obtain ⟨hk,ht₀,hfk,hfT,hfS⟩:=hf
  obtain ⟨hc3,hT2,hxT,hIS,hIT,hST⟩:=H.shape3 hk
  have hmin : ∀ H' : Cc0 G x y,3≤ H'.kind.rank:=hH.rank_ge hk
  have hvx : ¬ G.Adj v x:=by
    intro h
    have hvT : v∈H.T:=by
      rw [← hNx]
      exact (mem_neighborFinset _ _ _).mpr h.symm
    refine hv (Hf.T_subset_verts ?_)
    rw [hfT]
    exact Finset.mem_erase.mpr ⟨hvt,hvT⟩
  have h2:=qt4 hmin hfk hv hvy
  have hTf:=Finset.card_filter_le Hf.T (G.Adj v)
  have hTe : Hf.T.card=H.T.card - 1:=by rw [hfT,Finset.card_erase_of_mem ht₀]
  have h3 : (Hf.T.filter (G.Adj v)).card≤ Hf.S.card+1:=by
    rcases hfS with ⟨hTS,s₀,hs₀,hS⟩|⟨hTS,hS⟩
    · have:=Finset.card_pos.mpr ⟨s₀,hs₀⟩
      rw [hS,Finset.card_erase_of_mem hs₀]
      omega
    · by_contra hlt
      rw [hS] at hlt
      have hvS : v∉H.S:=fun h=>hv (Hf.S_subset_verts (by rw [hS];exact h))
      have h2' : ∀ s∈H.S,¬ G.Adj v s:=by
        rw [← hS]
        exact h2 (by omega)
      have:=hH.ell_ge (Cc0.mk3 H.x_ne_y (insert v H.S) (Hf.T.filter (G.Adj v))
        (by rw [Finset.card_insert_of_notMem hvS];omega) (by omega)
        (fun t ht=>hxT t (hTsub (Finset.mem_filter.mp ht).1)) (hIS.insert h2')
        (hIT.mono ((Finset.filter_subset _ _).trans hTsub))
        (qa9' (fun t ht=>(Finset.mem_filter.mp ht).2) fun s hs t ht =>
          hST s hs t (hTsub (Finset.mem_filter.mp ht).1))
        (qa2' (qa0 Hf.x_mem_verts hv) H.x_notMem_S)
        (qa2' hvy.symm H.y_notMem_S)
        (fun h=>H.y_notMem_T (hTsub (Finset.mem_filter.mp h).1))) (by simp [hk])
      rw [Cc0.mk3_ell,Finset.card_insert_of_notMem hvS,H.ell_t3 hk] at this
      omega
  have key:=qw6 hfk (fun h=>absurd h hvx) h2 h3 (fun h=>absurd h hvx)
  refine ⟨key.1,fun he=>qe1 ?_⟩
  rcases (key.2 he).2 with ⟨-,h⟩|⟨h,-⟩ <;> omega
theorem qs0 {z : Option V} {H Hf : Cc0 G x y} {t₀ : V}
    (htr : Ft0 z H t₀) (hf : Ifo0 H Hf t₀) (hyz : ∀ w,z=some w→ ¬ G.Adj y w) :
    ∃ a b : V,a≠b∧a≠y∧b≠y∧z≠some a∧z≠some b ∧
      Rc0 G Hf.vertsᶜ y a∧Rc0 G Hf.vertsᶜ y b:=by
  obtain ⟨-,-,-,-,hNy,ht₀,d,d₀,hd,hd₀,hdy,hdz⟩:=htr
  have hcompl : H.vertsᶜ⊆Hf.vertsᶜ:=Finset.compl_subset_compl.mpr hf.verts_subset
  have ht₀f : t₀∈Hf.vertsᶜ:=Finset.mem_compl.mpr hf.t₀_notMem
  have hyt₀ : G.Adj y t₀:=by
    rw [← mem_neighborFinset,hNy]
    exact ht₀
  have hr₀ : Rc0 G Hf.vertsᶜ y t₀ :=
    Rc0.adj (Finset.mem_compl.mpr Hf.y_notMem_verts) ht₀f hyt₀
  refine ⟨t₀,d,qa0 (H.T_subset_verts ht₀) (Finset.mem_compl.mp hd.left_mem),
    qa0 ht₀ H.y_notMem_T,hdy,fun h=>hyz t₀ h hyt₀,hdz,hr₀,?_⟩
  exact (hr₀.trans (Rc0.adj ht₀f (hcompl hd.right_mem) hd₀.symm)).trans (hd.mono hcompl).symm
end Flat
end DeanK5
end M9
section M10
namespace DeanK5
open SimpleGraph
variable {V : Type}
section Components
variable [DecidableEq V] {G : SimpleGraph V} {Y : Finset V} {u v : V}
noncomputable def ci0 (G : SimpleGraph V) (Y : Finset V) (u : V) : Finset V:=by
  classical
  exact Y.filter (Rc0 G Y u)
omit [DecidableEq V] in
theorem mem_compIn : v∈ci0 G Y u↔Rc0 G Y u v:=by
  classical
  unfold ci0
  exact Finset.mem_filter.trans ⟨And.right,fun h=>⟨h.right_mem,h⟩⟩
omit [DecidableEq V] in
theorem qe7 : ci0 G Y u⊆Y :=
  fun _ h=>(mem_compIn.mp h).right_mem
theorem qo6 {a : V} (ha : u∈ci0 G Y v) (hb : G.Adj u a) :
    a∈ci0 G Y v∨a∉Y:=by
  by_cases h : a∈Y
  · exact Or.inl (mem_compIn.mpr ((mem_compIn.mp ha).trans
      (Rc0.adj (qe7 ha) h hb)))
  · exact Or.inr h
theorem qk3 : Lk0 G (ci0 G Y u):=by
  apply qa4 u
  intro a ha
  obtain ⟨p,hp⟩:=mem_compIn.mp ha
  have hu : u∈ci0 G Y u:=mem_compIn.mpr (Rc0.refl (hp u p.start_mem_support))
  exact ⟨p,qb9 (D:=(·∉Y)) (fun _ hb _ hc=>qo6 hb hc) p hu
    (fun b hb hc=>hc (hp b hb))⟩
omit [DecidableEq V] in
theorem qaa9 (h : ¬ Rc0 G Y u v) :
    Disjoint (ci0 G Y u) (ci0 G Y v) :=
  Finset.disjoint_left.mpr fun _ hu hv=>h ((mem_compIn.mp hu).trans (mem_compIn.mp hv).symm)
end Components
namespace Cr
variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {x y : V} {z : Option V} {q : ℕ}
private theorem outside_mem {A : Finset V} {v : V} : v∈Aᶜ↔v∉A :=
  Finset.mem_compl
private theorem qt5 {H : Cc0 G x y}
    (hxy : ¬ G.Adj x y) (hC : ci0 G H.vertsᶜ y={y}) :
    G.neighborFinset y⊆H.S∪H.T:=by
  intro v hv
  have hyv:=(G.mem_neighborFinset y v).mp hv
  have hvH : v∈H.verts:=by
    by_contra hn
    have hm:=mem_compIn.mpr (Rc0.adj (outside_mem.mpr H.y_notMem_verts)
      (outside_mem.mpr hn) hyv)
    rw [hC,Finset.mem_singleton] at hm
    exact hyv.ne hm.symm
  exact Finset.mem_union.mpr ((Cc0.mem_verts.mp hvH).resolve_left
    (fun hvx=>hxy (hvx ▸ hyv.symm)))
omit [DecidableEq V] in
private theorem qab0 (H : Cc0 G x y) (hopt : Ioc0 G x y z H)
    (J : Cc0 G y x) (hk : J.kind=H.kind) {B : Finset V}
    (hy : G.neighborFinset y⊆B) (hx : B⊆G.neighborFinset x) :
    G.neighborFinset x=B∧G.neighborFinset y=B:=by
  have hdeg:=(hopt.2.2 J (congrArg Ck0.rank hk)).1
  rw [← card_neighborFinset_eq_degree,← card_neighborFinset_eq_degree] at hdeg
  exact ⟨(Finset.eq_of_subset_of_card_le hx (hdeg.trans (Finset.card_le_card hy))).symm,
    Finset.eq_of_subset_of_card_le hy ((Finset.card_le_card hx).trans hdeg)⟩
private theorem singleton_twin (hK : Kc0 G 2) (hxy : ¬ G.Adj x y)
    (H : Cc0 G x y) (hopt : Ioc0 G x y z H)
    (hC : ci0 G H.vertsᶜ y={y}) :
    (H.kind=.t2→ G.neighborFinset x=H.S∧G.neighborFinset y=H.S) ∧
    (H.kind=.t1∨H.kind=.t3→ G.neighborFinset x=H.T∧G.neighborFinset y=H.T):=by
  have hsub:=qt5 hxy hC
  have h2 : 2≤ (G.neighborFinset y).card:=by
    rw [card_neighborFinset_eq_degree]
    exact qe8 hK y
  have hn : x∉G.neighborFinset y:=fun h=>hxy ((G.mem_neighborFinset y x).mp h).symm
  have hy : ∀ v∈G.neighborFinset y,G.Adj y v:=fun v=>(G.mem_neighborFinset y v).mp
  have hrank : ∀ J : Cc0 G y x,H.kind.rank≤ J.kind.rank:=hopt.2.1
  have htwin : ∀ (J : Cc0 G y x),J.kind=H.kind→ ∀ B : Finset V,
      G.neighborFinset y⊆B→ (∀ v∈B,G.Adj x v) →
      G.neighborFinset x=B∧G.neighborFinset y=B :=
    fun J hk B hb hx=>qab0 H hopt J hk hb fun v hv =>
      (G.mem_neighborFinset x v).mpr (hx v hv)
  constructor
  · intro hk
    obtain ⟨hs,ht,hxS,hIS,hKT,hST⟩:=H.shape2 hk
    have hyS : G.neighborFinset y⊆H.S:=by
      intro v hv
      rcases Finset.mem_union.mp (hsub hv) with hs'|ht'
      · exact hs'
      obtain ⟨w,hw,hwv⟩:=Finset.exists_mem_ne (by omega : 1 < (G.neighborFinset y).card) v
      have hvw : G.Adj v w:=(Finset.mem_union.mp (hsub hw)).elim
        (fun hwS=>(hST w hwS v ht').symm) (fun hwT=>hKT v ht' w hwT hwv.symm)
      exact (qg7 (fun J=>by simpa [hk,Ck0.rank] using hrank J)
        H.x_ne_y.symm (hy v hv) (hy w hw) hvw
        (qa0 hv hn) (qa0 hw hn)).elim
    have hS:=Finset.eq_of_subset_of_card_le hyS (by omega)
    let J:=Cc0.mk2 H.x_ne_y.symm H.S H.T hs ht
      (fun s h=>hy s (hS ▸ h)) hIS hKT hST H.y_notMem_T H.x_notMem_S H.x_notMem_T
    exact htwin J hk.symm H.S hyS hxS
  · rintro (hk|hk)
    · obtain ⟨hs,-,hxT,hKT⟩:=H.shape1 hk
      rw [hs,Finset.empty_union] at hsub
      let J:=Cc0.mk1 H.x_ne_y.symm (G.neighborFinset y) h2 hy (hKT.mono hsub) hn
      exact htwin J hk.symm H.T hsub hxT
    · obtain ⟨hc,-,hxT,hIS,hIT,hST⟩:=H.shape3 hk
      have hmin : ∀ J : Cc0 G y x,2≤ J.kind.rank:=fun J =>
        le_trans (by simp [hk,Ck0.rank]) (hrank J)
      have hside : G.neighborFinset y⊆H.S∨G.neighborFinset y⊆H.T:=by
        by_cases hs : G.neighborFinset y⊆H.S
        · exact Or.inl hs
        · right
          obtain ⟨t,hty,htS⟩:=Finset.not_subset.mp hs
          have htT:=(Finset.mem_union.mp (hsub hty)).resolve_left htS
          intro v hv
          refine (Finset.mem_union.mp (hsub hv)).resolve_left fun hvS=>?_
          exact qg7 hmin H.x_ne_y.symm (hy v hv) (hy t hty) (hST v hvS t htT)
            (qa0 hv hn) (qa0 hty hn)
      have hind:=hside.elim hIS.mono hIT.mono
      let J:=Cc0.mk3 H.x_ne_y.symm ∅ (G.neighborFinset y) (by rw [Finset.card_empty];omega) h2 hy
        (by simp [IndepIn]) hind (by simp) (by simp) (by simp) hn
      have hdeg:=(hopt.2.2 J (congrArg Ck0.rank hk.symm)).1
      have hcard : H.T.card≤ (G.neighborFinset y).card:=by
        rw [card_neighborFinset_eq_degree]
        exact (Finset.card_le_card (show H.T⊆G.neighborFinset x from fun t ht =>
          (G.mem_neighborFinset x t).mpr (hxT t ht))).trans (by simpa using hdeg)
      exact htwin J hk.symm H.T (hside.resolve_left fun hs=>by
        have:=Finset.card_le_card hs
        omega) hxT
end Cr
section Reduction
variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {x y : V} {z : Option V} {q : ℕ}
theorem qb2 (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q)
    {H : Cc0 G x y} (hopt : Ioc0 G x y z H)
    (hC : ci0 G (Finset.univ\H.verts) y={y}) :
    (H.kind=.t2→ G.neighborFinset x=H.S∧G.neighborFinset y=H.S) ∧
    (H.kind=.t1∨H.kind=.t3→ G.neighborFinset x=H.T∧G.neighborFinset y=H.T) :=
  Cr.singleton_twin (qb7 ih hHyp hq4 hfail)
    (qb3 ih hHyp hq4 hfail) H hopt hC
end Reduction
namespace Cr
open Cb
variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {x y : V} {z : Option V} {q : ℕ}
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem qaf8 {A B : Finset V} {s t u : V} {m n : ℕ}
    (hP : Pi0 G A s t m) (hQ : Pi0 G B t u n)
    (hAB : ∀ v∈A,v∈B→ v=t) : ∃ p : G.Walk s u,p.IsPath∧p.length=m+n:=by
  obtain ⟨p,hp,hpl,hps⟩:=hP
  obtain ⟨r,hr,hrl,hrs⟩:=hQ
  have hh:=qa3 hp hr (fun v hv hw=>hAB v (hps v hv) (hrs v hw))
  exact ⟨p.append r,hh.1,by rw [hh.2.1,hpl,hrl]⟩
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem qah0 {A : Finset V} {p n a b e d : ℕ}
    (hp : 1≤ p) (hn : 1≤ n) (hab : 2≤ a+b)
    (he : e=1∨e=2) (hd : d=1∨d=2)
    (hQ : ∀ j : Fin n,∃ t,∃ B : Finset V,Pi0 G B t y (b+j.val*d) ∧
      (∀ i : Fin p,Pi0 G A x t (a+i.val*e))∧∀ v∈A,v∈B→ v=t) :
    Adm0 G x y (p+n - 1):=by
  obtain ⟨c,f,hc,hf,hsum⟩:=qi9 hp hn he hd a b
  refine ⟨c,f,hab.trans hc,hf,fun k=>?_⟩
  obtain ⟨i,j,hij⟩:=hsum k
  obtain ⟨t,B,hB,hA,hAB⟩:=hQ j
  rw [← hij]
  exact qaf8 (hA i) hB hAB
omit [DecidableRel G.Adj] in
private theorem qx2 {H : Cc0 G x y} {d : V}
    {D : Finset V} (hD : D=ci0 G H.vertsᶜ d) :
    ∀ v∈D,∀ w,G.Adj v w→ w∈D∨w∈H.verts:=by
  subst D
  intro v hv w hadj
  exact (qo6 hv hadj).imp_right (fun h=>by simpa using h)
private theorem qad5 (hK : Kc0 G 2) {A D : Finset V} {v : V}
    (hv : v∉D) (hvA : v∉A) (hD : D.Nonempty)
    (hbound : ∀ c∈D,∀ w,G.Adj c w→ w∈D∨w∈A) :
    ∃ t∈A,∃ c∈D,G.Adj c t:=by
  have hcut:=qq9 hK hD (Finset.singleton_nonempty v)
    (Finset.disjoint_singleton_right.mpr hv) (by
      intro c hc w hw h
      have hwv:=Finset.mem_singleton.mp hw
      subst w
      exact (hbound c hc v h).elim hv hvA)
  obtain ⟨t,ht⟩:=Finset.card_pos.mp (by omega : 0 <
    ((D.biUnion fun c=>G.neighborFinset c)\D).card)
  obtain ⟨ht₁,ht₂⟩:=Finset.mem_sdiff.mp ht
  obtain ⟨c,hc,hct⟩:=Finset.mem_biUnion.mp ht₁
  have h:=(G.mem_neighborFinset c t).mp hct
  exact ⟨t,(hbound c hc t h).resolve_left ht₂,c,hc,h⟩
private theorem qj5 {A : Finset V} (hxy : x≠y) (hx : x∉A) (hy : y∉A) :
    A.card+2≤ Fintype.card V:=by
  have h:=Finset.card_le_univ (insert x (insert y A))
  rw [Finset.card_insert_of_notMem (qa2' hxy hx),Finset.card_insert_of_notMem hy] at h
  omega
private theorem qp0 (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hK : Kc0 G 2)
    {D B : Finset V} {t c : V} {loss : ℕ}
    (hD : Lk0 G D) (hxD : x∉D) (hyD : y∉D)
    (hxB : x∉B) (hyB : y∉B) (hDB : Disjoint D B)
    (ht : t∈B) (hc : c∈D) (hct : G.Adj c t)
    (hcl : ∀ v∈D,∀ w,G.Adj v w→ w∈D∨w∈B)
    (hord : ∃ v∈D,z≠some v) (hloss : loss < q)
    (hcount : ∀ v∈D,(G.neighborFinset v∩B.erase t).card≤ loss+1) :
    ∃ a d : ℕ,2≤ a∧(d=1∨d=2)∧∀ i : Fin (q - loss),∃ k∈B.erase t,
      Pi0 G (insert k (insert t D)) k t (a+i.val*d):=by
  classical
  let A:=insert t D
  let K:=B.erase t
  have htD:=Finset.disjoint_right.mp hDB ht
  have htA : t∈A:=Finset.mem_insert_self _ _
  have hKA : ∀ k∈K,k∉A:=by
    intro k hk
    obtain ⟨hnt,hkB⟩:=Finset.mem_erase.mp hk
    exact qa2' hnt (Finset.disjoint_right.mp hDB hkB)
  have hnd : D.Nonempty:=⟨c,hc⟩
  have hA : Lk0 G A:=qe6 hD hc hct.symm
  have hcard : 2≤ A.card:=by
    change 2≤ (insert t D).card
    rw [Finset.card_insert_of_notMem htD]
    exact Nat.succ_le_succ (Finset.card_pos.mpr hnd)
  have hxA : x∉A:=qa2' (fun h=>hxB (h ▸ ht)) hxD
  have hyA : y∉A:=qa2' (fun h=>hyB (h ▸ ht)) hyD
  have hsize:=qj5 hHyp.2.1.1 hxA hyA
  have hcut : ∀ w∈A,∀ v∈A.erase w,∃ u∈A.erase w,
      (u=t∨∃ k∈K,G.Adj u k)∧Rc0 G (A.erase w) u v:=by
    intro w hw v hv
    obtain ⟨R,hRA,hvR,hRcl,hR⟩:=qg2 (G:=G) (A.erase w) hv
    by_cases htR : t∈R
    · exact ⟨t,hRA htR,Or.inl rfl,(hR t htR).symm⟩
    obtain ⟨u,hu,k,hkR,hkw,huk⟩:=qr3 hK hvR (fun hx=>hxA (Finset.mem_of_mem_erase
      (hRA hx))) (Finset.ne_of_mem_erase hv) (fun h=>hxA (h ▸ hw))
    have huD : u∈D :=
      (Finset.mem_insert.mp (Finset.mem_of_mem_erase (hRA hu))).resolve_left (fun h=>htR (h ▸ hu))
    have hkA : k∉A:=fun hk=>hkR (hRcl u hu k (Finset.mem_erase.mpr ⟨hkw,hk⟩) huk)
    have hkB:=(hcl u huD k huk).resolve_left (fun hk=>hkA (Finset.mem_insert_of_mem hk))
    exact ⟨u,hRA hu,Or.inr ⟨k,Finset.mem_erase.mpr
      ⟨fun h=>hkA (h ▸ htA),hkB⟩,huk⟩,(hR u hu).symm⟩
  let Z : Finset (A : Set V):=Finset.univ.filter fun v=>∃ k∈K,G.Adj v.1 k
  have hZ (v : (A : Set V)) : v∈Z↔∃ k∈K,G.Adj v.1 k:=by
    simp [Z]
  let J:=av0 (G.induce (A : Set V)) Z
  let r : (A : Set V):=⟨t,htA⟩
  have hroot : Rt0 J none (some r) :=
    rooted_adjoin Z htA hcard hA (fun w hw v hv=>by
      obtain ⟨u,hu,h,hp⟩:=hcut w hw v hv
      exact ⟨u,hu,h.imp_right fun huK=>⟨Finset.mem_of_mem_erase hu,(hZ _).mpr huK⟩,hp⟩)
  let g : V→ Option (A : Set V):=fun v=>if h : v∈A then some ⟨v,h⟩ else none
  have hg (v : V) (hv : v∈A) : g v=some ⟨v,hv⟩:=dif_pos hv
  have hg' (v : V) (hv : v∉A) : g v=none:=dif_neg hv
  have hmeas : Fintype.card (Option (A : Set V))+J.edgeFinset.card <
      Fintype.card V+G.edgeFinset.card:=by
    have hedges : J.edgeFinset.card≤ G.edgeFinset.card:=by
      apply card_edge_le_of_proj g
      intro a b hab
      cases a <;> cases b
      · exact (adjoin_not_adj_none hab).elim
      · rename_i b
        obtain ⟨k,hk,hbk⟩:=(hZ b).mp hab
        exact ⟨k,b.1,hbk.symm,hg' k (hKA k hk),hg b.1 b.2⟩
      · rename_i a
        obtain ⟨k,hk,hak⟩:=(hZ a).mp hab
        exact ⟨a.1,k,hak,hg a.1 a.2,hg' k (hKA k hk)⟩
      · rename_i a b
        exact ⟨a.1,b.1,hab,hg a.1 a.2,hg b.1 b.2⟩
    have hAcard : Fintype.card (A : Set V)=A.card:=by simp
    rw [Fintype.card_option,hAcard]
    omega
  obtain ⟨z',hz'⟩:=exists_pull (W:=↥(A : Set V)) Subtype.val_injective z
  have hwit : ∃ o : Option (A : Set V),o≠none∧o≠some r∧z'.map some≠some o:=by
    obtain ⟨v,hv,hz⟩:=hord
    exact ⟨some ⟨v,Finset.mem_insert_of_mem hv⟩,by simp,
      fun h=>htD ((show v=t from congrArg Subtype.val (Option.some.inj h)) ▸ hv),
      fun h=>hz ((hz' _).mp (map_some_iff.mp h))⟩
  have hdeg : ∀ o : Option (A : Set V),o≠none→ o≠some r→ z'.map some≠some o →
      q - loss+1≤ J.degree o:=by
    intro o ho hr hz
    cases o with
    | none=>exact (ho rfl).elim
    | some v =>
      have hvt : v.1≠t:=fun h=>hr (congrArg some (Subtype.ext h))
      have hvD:=(Finset.mem_insert.mp v.2).resolve_left hvt
      have hdv:=hHyp.2.2.2 v.1 (qa0 hvD hxD) (qa0 hvD hyD)
        (fun h=>hz (map_some_iff.mpr ((hz' v).mpr h)))
      let U:=G.neighborFinset v.1
      have hsum:=Finset.card_sdiff_add_card_inter U K
      have hUd : U.card=G.degree v.1:=card_neighborFinset_eq_degree _ _
      have hcnt : (U∩K).card≤ loss+1:=hcount _ hvD
      have hin (w : V) (hw : w∈U\K) : w∈A :=
        (hcl _ hvD w ((G.mem_neighborFinset _ _).mp (Finset.mem_sdiff.mp hw).1)).elim
          (fun h=>Finset.mem_insert_of_mem h)
          (fun h=>Finset.mem_insert.mpr (Or.inl (by
            by_contra h'
            exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_erase.mpr ⟨h',h⟩))))
      have hkeep : ∀ M : Finset V,M⊆U →
          (∀ a∈M,∀ b∈M,a∈K→ b∈K→ a=b) →
          M.card≤ J.degree (some v):=by
        intro M hMU hone
        rw [← card_neighborFinset_eq_degree]
        apply Finset.card_le_card_of_injOn g
        · intro w hw
          change w∈M at hw
          change g w∈J.neighborFinset (some v)
          rw [mem_neighborFinset]
          have hvw:=(G.mem_neighborFinset _ _).mp (hMU hw)
          by_cases hwK : w∈K
          · rw [hg' w (hKA w hwK)]
            exact (hZ v).mpr ⟨w,hwK,hvw⟩
          · rw [hg w (hin w (Finset.mem_sdiff.mpr ⟨hMU hw,hwK⟩))]
            exact hvw
        · intro a ha b hb he
          change a∈M at ha
          change b∈M at hb
          by_cases haK : a∈K <;> by_cases hbK : b∈K
          · exact hone a ha b hb haK hbK
          · rw [hg' a (hKA a haK),hg b (hin b (Finset.mem_sdiff.mpr ⟨hMU hb,hbK⟩))] at he
            simp at he
          · rw [hg a (hin a (Finset.mem_sdiff.mpr ⟨hMU ha,haK⟩)),hg' b (hKA b hbK)] at he
            simp at he
          · rw [hg a (hin a (Finset.mem_sdiff.mpr ⟨hMU ha,haK⟩)),
              hg b (hin b (Finset.mem_sdiff.mpr ⟨hMU hb,hbK⟩))] at he
            simpa using he
      by_cases he : (U∩K).Nonempty
      · obtain ⟨w,hw⟩:=he
        have hwN : w∉U\K:=fun h=>(Finset.mem_sdiff.mp h).2 (Finset.mem_inter.mp hw).2
        have hk:=hkeep (insert w (U\K))
          (Finset.insert_subset_iff.mpr ⟨(Finset.mem_inter.mp hw).1,Finset.sdiff_subset⟩)
          (fun a ha b hb hak hbk=>by
            have ea:=(Finset.mem_insert.mp ha).resolve_right
              (fun h=>(Finset.mem_sdiff.mp h).2 hak)
            have eb:=(Finset.mem_insert.mp hb).resolve_right
              (fun h=>(Finset.mem_sdiff.mp h).2 hbk)
            exact ea.trans eb.symm)
        rw [Finset.card_insert_of_notMem hwN] at hk
        omega
      · have hk:=hkeep (U\K) Finset.sdiff_subset fun a ha _ _ hak _ =>
          ((Finset.mem_sdiff.mp ha).2 hak).elim
        have he' : U∩K=∅:=Finset.not_nonempty_iff_eq_empty.mp he
        rw [he',Finset.card_empty] at hsum
        omega
  obtain ⟨a,d,ha,hd,hP⟩ :=
    ih _ J none (some r) (z'.map some) (q - loss) (by omega) hmeas
      ⟨by omega,hroot,hwit,hdeg⟩
  refine ⟨a,d,ha,hd,fun i=>?_⟩
  obtain ⟨p,hp,hpl⟩:=hP i
  obtain ⟨v,hv,m,hm,hml,-⟩:=qf4 hp
  obtain ⟨k,hk,hvk⟩:=(hZ v).mp hv
  obtain ⟨m',hm',hml',-,hms⟩:=qd3 (G:=G) (A : Set V) hm
  have hIn : Pi0 G A v.1 t m'.length:=⟨m',hm',rfl,fun w hw=>hms w hw⟩
  exact ⟨k,hk,(hIn.cons hvk.symm (hKA k hk)).len (by rw [hml',← hml,hpl])⟩
end Cr
namespace Cr
variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {x y : V} {z : Option V} {q : ℕ}
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qaa7 (H : Cc0 G x y) (hk : H.kind=.t1∨H.kind=.t3)
    {t : V} (ht : t∈H.T) (m : ℕ) (hm : m≤ H.ell) (hmT : m+2≤ H.T.card) :
    ∃ e : ℕ,(e=1∨e=2)∧∀ k∈H.T.erase t,∀ i : Fin (m+1),
      Pi0 G (H.verts.erase t) x k (1+i.val*e):=by
  have hxt : x≠t:=fun h=>H.x_notMem_T (h ▸ ht)
  have hcard:=Finset.card_erase_of_mem ht
  rcases hk with hk|hk
  · obtain ⟨-,-,hxT,hKT⟩:=H.shape1 hk
    refine ⟨1,Or.inl rfl,fun k hk' i=>?_⟩
    have hkT:=Finset.mem_of_mem_erase hk'
    refine (qg9 _ _ ((hKT.mono (Finset.erase_subset t H.T)).insert
      (fun v hv=>hxT v (Finset.mem_of_mem_erase hv))) x (Finset.mem_insert_self _ _)
      k (Finset.mem_insert_of_mem hk') (fun h=>H.x_notMem_T (h ▸ hkT)) (by omega) ?_).mono ?_
    · rw [Finset.card_insert_of_notMem (fun h=>H.x_notMem_T (Finset.mem_of_mem_erase h))]
      have:=i.isLt
      omega
    · intro v hv
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact Finset.mem_erase.mpr ⟨hxt,H.x_mem_verts⟩
      · exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hv,
          H.T_subset_verts (Finset.mem_of_mem_erase hv)⟩
  · obtain ⟨-,-,hxT,-,-,hST⟩:=H.shape3 hk
    have hS : (insert x H.S).card=H.ell+1:=by
      rw [Finset.card_insert_of_notMem H.x_notMem_S,H.ell_t3 hk]
    have hadj : ∀ k∈H.T.erase t,∀ v∈insert x H.S,G.Adj v k:=by
      intro k hk' v hv
      rcases Finset.mem_insert.mp hv with rfl|hv
      · exact hxT k (Finset.mem_of_mem_erase hk')
      · exact hST v hv k (Finset.mem_of_mem_erase hk')
    refine ⟨2,Or.inr rfl,fun k hk' i=>?_⟩
    have hi:=i.isLt
    refine ((qk4 i.val _ _ hadj k hk' x (Finset.mem_insert_self _ _)
      (by omega) (by omega)).mono ?_).len (by ring)
    intro v hv
    rcases Finset.mem_union.mp hv with hv|hv
    · exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hv,
        H.T_subset_verts (Finset.mem_of_mem_erase hv)⟩
    rcases Finset.mem_insert.mp hv with rfl|hv
    · exact Finset.mem_erase.mpr ⟨hxt,H.x_mem_verts⟩
    · exact Finset.mem_erase.mpr ⟨qa0 hv (Finset.disjoint_right.mp H.disj ht),
        H.S_subset_verts hv⟩
private theorem other_hits (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q)
    {H : Cc0 G x y} (hk : H.kind=.t1∨H.kind=.t3)
    {D : Finset V} {b : V} (hD : D=ci0 G H.vertsᶜ b) (hyD : y∉D)
    (hord : ∃ v∈D,z≠some v)
    (hx : ∀ v∈D,¬ G.Adj v x) (hy : ∀ t∈H.T,G.Adj y t)
    (hext : ∀ v∈D,(G.neighborFinset v∩H.verts).card≤ H.ell+1) :
    ∃ v∈D,∃ s∈H.S,G.Adj v s:=by
  classical
  by_contra! hno
  have hK:=qb7 ih hHyp hq4 hfail
  have hbound : ∀ v∈D,∀ w,G.Adj v w→ w∈D∨w∈H.T:=by
    intro v hv w hadj
    refine (qx2 hD v hv w hadj).imp_right fun hw=>?_
    rcases Cc0.mem_verts.mp hw with rfl|hs|ht
    · exact (hx v hv hadj).elim
    · exact (hno v hv w hs hadj).elim
    · exact ht
  have hne : D.Nonempty:=hord.imp fun _ h=>h.1
  obtain ⟨t,ht,c,hc,hct⟩:=qad5 hK hyD H.y_notMem_T hne hbound
  have hsub : D⊆H.vertsᶜ:=hD ▸ qe7
  have hxD : x∉D:=fun h=>outside_mem.mp (hsub h) H.x_mem_verts
  have hdis : Disjoint D H.T:=Finset.disjoint_left.mpr fun v hv hw =>
    outside_mem.mp (hsub hv) (H.T_subset_verts hw)
  have hell:=qj7 H hfail (Rc0.refl (outside_mem.mpr H.y_notMem_verts)) ht (hy t ht)
  have hcard : H.ell+1≤ H.T.card:=by
    rcases hk with h|h
    · rw [H.ell_t1 h]
      have:=H.two_le_T
      omega
    · rw [H.ell_t3 h]
      exact (H.shape3 h).1
  let m:=min H.ell (H.T.card - 2)
  have hm : m≤ H.ell:=min_le_left _ _
  have hmT : m+2≤ H.T.card:=by
    have h:=min_le_right H.ell (H.T.card - 2)
    have:=H.two_le_T
    omega
  have hcount : ∀ v∈D,(G.neighborFinset v∩H.T.erase t).card≤ m+1:=by
    intro v hv
    have h₁:=(Finset.card_le_card (Finset.inter_subset_right :
      G.neighborFinset v∩H.T.erase t⊆H.T.erase t))
    rw [Finset.card_erase_of_mem ht] at h₁
    have h₂:=(Finset.card_le_card (Finset.inter_subset_inter
      (show G.neighborFinset v⊆G.neighborFinset v from subset_rfl)
      ((Finset.erase_subset t H.T).trans H.T_subset_verts))).trans (hext v hv)
    by_cases hh : H.ell≤ H.T.card - 2
    · simpa [m,min_eq_left hh] using h₂
    · have hle : H.T.card - 2≤ H.ell:=by omega
      have hT:=H.two_le_T
      rw [show m=H.T.card - 2 by simp [m,min_eq_right hle]]
      omega
  obtain ⟨a,d,ha,hd,hP⟩:=qp0 ih hHyp hq4 hK (hD ▸ qk3)
    hxD hyD H.x_notMem_T H.y_notMem_T hdis ht hc hct hbound hord (show m < q by omega) hcount
  obtain ⟨e,he,hA⟩:=qaa7 H hk ht m hm hmT
  have hjoin : Adm0 G x y ((m+1)+(q - m) - 1):=by
    apply qah0 (A:=H.verts.erase t) (a:=1) (b:=a+1) (e:=e) (d:=d)
      (by omega) (by omega) (by omega) he hd
    intro j
    obtain ⟨k,hkt,hp⟩:=hP j
    have hyB : y∉insert k (insert t D):=qa2'
      (qa0 (Finset.mem_of_mem_erase hkt) H.y_notMem_T).symm
      (qa2' (qa0 ht H.y_notMem_T).symm hyD)
    refine ⟨k,_,(hp.concat (hy t ht).symm hyB).len (by ring),hA k hkt,?_⟩
    intro v hv hw
    simp only [Finset.mem_insert] at hw
    rcases hw with rfl|rfl|rfl|hw
    · exact (H.y_notMem_verts (Finset.mem_of_mem_erase hv)).elim
    · rfl
    · exact (Finset.notMem_erase _ _ hv).elim
    · exact (outside_mem.mp (hsub hw) (Finset.mem_of_mem_erase hv)).elim
  exact hfail (qc0 (by omega) hjoin)
end Cr
section Attachments
variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {x y : V} {z : Option V} {q : ℕ}
theorem qo2 (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q)
    {H : Cc0 G x y} (hopt : Ioc0 G x y z H)
    (hC : ci0 G (Finset.univ\H.verts) y={y})
    (hk : H.kind=.t1∨H.kind=.t3)
    {D : Finset V} {b : V} (hD : D=ci0 G (Finset.univ\H.verts) b)
    (hyD : y∉D) (hord : ∃ v∈D,z≠some v) :
    ∃ v∈D,∃ s∈H.S,G.Adj v s:=by
  obtain ⟨hx,hy⟩:=(qb2 ih hHyp hq4 hfail hopt hC).2 hk
  have hsub : D⊆H.vertsᶜ:=hD ▸ qe7
  apply Cr.other_hits ih hHyp hq4 hfail hk hD hyD hord
  · intro v hv hvx
    have : v∈G.neighborFinset x:=(G.mem_neighborFinset _ _).mpr hvx.symm
    rw [hx] at this
    exact Cr.outside_mem.mp (hsub hv) (H.T_subset_verts this)
  · intro t ht
    exact (G.mem_neighborFinset _ _).mp (hy.symm ▸ ht)
  · intro v hv
    exact (ql7 hopt.1 (Cr.outside_mem.mp (hsub hv))
      (qa0 hv hyD)).1
end Attachments
namespace Cr
open Cb
variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {x y : V} {z : Option V} {q : ℕ}
private theorem qp6 (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hK : Kc0 G 2)
    {s t : V} (hst : s≠t)
    (hx : G.neighborFinset x={s,t}) (hy : G.neighborFinset y={s,t})
    (hwit : ∃ v,v≠x∧v≠y∧v≠s∧v≠t∧z≠some v) :
    Adm0 G x y q:=by
  let R : Finset V:={x,y}
  let A:=Rᶜ
  have hxs : G.Adj x s:=(G.mem_neighborFinset _ _).mp (hx.symm ▸ Finset.mem_insert_self _ _)
  have hxt : G.Adj x t:=(G.mem_neighborFinset _ _).mp (hx.symm ▸ Finset.mem_insert_of_mem
    (Finset.mem_singleton_self _))
  have hys : G.Adj y s:=(G.mem_neighborFinset _ _).mp (hy.symm ▸ Finset.mem_insert_self _ _)
  have hyt : G.Adj y t:=(G.mem_neighborFinset _ _).mp (hy.symm ▸ Finset.mem_insert_of_mem
    (Finset.mem_singleton_self _))
  have hxA : x∉A:=by simp [A,R]
  have hyA : y∉A:=by simp [A,R]
  have hs : s∈A:=by simp [A,R,hxs.ne.symm,hys.ne.symm]
  have ht : t∈A:=by simp [A,R,hxt.ne.symm,hyt.ne.symm]
  obtain ⟨v,hvx,hvy,hvs,hvt,hvz⟩:=hwit
  have hv : v∈A:=by simp [A,R,hvx,hvy]
  have hcard : 2 < A.card:=by
    have hsub : ({v,s,t} : Finset V)⊆A:=Finset.insert_subset_iff.mpr
      ⟨hv,Finset.insert_subset_iff.mpr ⟨hs,Finset.singleton_subset_iff.mpr ht⟩⟩
    have h:=Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (qf5 hvs hvt),Finset.card_pair hst] at h
    omega
  have hcl : ∀ c∈R,∀ w,G.Adj c w→ w∈R∨w=s∨w=t:=by
    intro c hc w hadj
    right
    have he : G.neighborFinset c={s,t}:=by
      rcases (show c=x∨c=y by simpa [R] using hc) with rfl|rfl
      exacts [hx,hy]
    have h:=(G.mem_neighborFinset c w).mpr hadj
    simpa [he] using h
  have hroot:=qq1 hK hst (outside_mem.mp hs) (outside_mem.mp ht) hcl hcard
  have hsize:=qj5 hHyp.2.1.1 hxA hyA
  obtain ⟨a,d,ha,hd,hP⟩:=induce_call (ih.toAt hq4) A hs ht z hHyp.1 hroot (by omega)
    (fun u hu hus hut huz=>⟨hHyp.2.2.2 u (qa0 hu hxA)
      (qa0 hu hyA) huz,fun w huw=>by
        apply outside_mem.mpr
        intro hw
        rcases (hcl w hw u huw.symm).resolve_left (outside_mem.mp hu) with h|h
        exacts [hus h,hut h]⟩) ⟨v,hv,hvs,hvt,hvz⟩
  refine ⟨a+2,d,by omega,hd,fun i=>?_⟩
  have hp : Pi0 G A s t (a+i.val*d):=hP i
  have h:=((hp.cons hxs hxA).concat hyt.symm (qa2' hHyp.2.1.1.symm hyA)).len
    (show (a+i.val*d)+1+1=(a+2)+i.val*d by ring)
  obtain ⟨p,hp,hl,-⟩:=h
  exact ⟨p,hp,hl⟩
omit [DecidableRel G.Adj] in
private theorem qk7 {H : Cc0 G x y}
    (hC : ci0 G H.vertsᶜ y={y}) {v : V} (hvy : v≠y) :
    y∉ci0 G H.vertsᶜ v:=by
  intro h
  have h':=mem_compIn.mpr (mem_compIn.mp h).symm
  rw [hC,Finset.mem_singleton] at h'
  exact hvy h'
private theorem qc9 (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q) :
    ∀ v,z=some v→ ¬ G.Adj y v:=by
  intro v hz h
  by_cases hvx : v=x
  · exact qb3 ih hHyp hq4 hfail (hvx ▸ h.symm)
  · exact qd5 ih hHyp hq4 hfail v hz hvx h.ne.symm h
private theorem qp9 (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q)
    {H : Cc0 G x y} (hopt : Ioc0 G x y z H)
    (hC : ci0 G H.vertsᶜ y={y}) (hk : H.kind=.t1) : False:=by
  classical
  obtain ⟨hS,hT,hxT,hKT⟩:=H.shape1 hk
  obtain ⟨-,hy⟩:=(qb2 ih hHyp hq4 hfail hopt hC).2 (Or.inl hk)
  have hyT : ∀ t∈H.T,G.Adj y t:=fun t ht=>(G.mem_neighborFinset _ _).mp (hy.symm ▸ ht)
  have hzT : ∀ t∈H.T,z≠some t:=fun t ht hz =>
    qc9 ih hHyp hq4 hfail t hz (hyT t ht)
  have hall : ∀ v,v∉H.verts→ v≠y→ z=some v:=by
    intro v hv hvy
    by_contra hz
    obtain ⟨-,-,s,hs,-⟩:=qo2 ih hHyp hq4 hfail hopt hC (Or.inl hk)
      (b:=v) rfl (qk7 hC hvy)
      ⟨v,mem_compIn.mpr (Rc0.refl (outside_mem.mpr hv)),hz⟩
    simp [hS] at hs
  have hK:=qb7 ih hHyp hq4 hfail
  have hsmall:=qt1 hK H hk hfail
  rw [H.ell_t1 hk] at hsmall
  obtain ⟨s,hs,t,ht,hst⟩:=Finset.one_lt_card.mp (by omega : 1 < H.T.card)
  have hdeg : ∀ t∈H.T,q+1≤ G.degree t:=fun t ht =>
    hHyp.2.2.2 t (qa0 ht H.x_notMem_T) (qa0 ht H.y_notMem_T) (hzT t ht)
  have hord:=(hdeg t ht).trans_lt (degree_lt_card_verts (G:=G) t)
  have hbase : (insert y H.verts).card=H.T.card+2:=by
    rw [Finset.card_insert_of_notMem H.y_notMem_verts,Cc0.verts,hS,Finset.empty_union,
      Finset.card_insert_of_notMem H.x_notMem_T]
  obtain ⟨r,-,hr⟩:=Finset.exists_mem_notMem_of_card_lt_card
    (s:=insert y H.verts) (t:=Finset.univ) (by rw [Finset.card_univ,hbase];omega)
  obtain ⟨hry,hrH⟩:=not_or.mp (fun h=>hr (Finset.mem_insert.mpr h))
  have hz:=hall r hrH hry
  have hcov : (Finset.univ : Finset V)=insert r (insert y H.verts):=by
    refine Finset.eq_univ_of_forall (fun v=>?_) |>.symm
    by_cases h : v∈insert y H.verts
    · exact Finset.mem_insert_of_mem h
    · have hv:=not_or.mp (fun h'=>h (Finset.mem_insert.mpr h'))
      exact Finset.mem_insert.mpr (Or.inl (Option.some.inj ((hall v hv.2 hv.1).symm.trans hz)))
  have hvcard : Fintype.card V=H.T.card+3:=by
    rw [← Finset.card_univ,hcov,Finset.card_insert_of_notMem hr,hbase]
  have hTc : H.T.card=q - 1:=by omega
  have hrT : r∉H.T:=fun h=>hrH (H.T_subset_verts h)
  have hradj : ∀ t∈H.T,G.Adj r t:=by
    intro t ht
    have hsub : G.neighborFinset t⊆Finset.univ.erase t:=by
      intro w hw
      exact Finset.mem_erase.mpr ⟨((G.mem_neighborFinset _ _).mp hw).ne.symm,Finset.mem_univ _⟩
    have hle : (Finset.univ.erase t).card≤ (G.neighborFinset t).card:=by
      rw [Finset.card_erase_of_mem (Finset.mem_univ t),Finset.card_univ,card_neighborFinset_eq_degree]
      have:=hdeg t ht
      omega
    have:=Finset.eq_of_subset_of_card_le hsub hle
    exact ((G.mem_neighborFinset t r).mp (this.symm ▸ Finset.mem_erase.mpr
      ⟨qa0 ht hrT |>.symm,Finset.mem_univ r⟩)).symm
  apply hfail
  refine ⟨2,1,le_rfl,Or.inl rfl,fun i=>?_⟩
  have hi:=i.isLt
  by_cases h : i.val+1≤ H.T.card
  · have hp:=qg9 (i.val+1) _ (hKT.insert hxT) x (Finset.mem_insert_self _ _)
      t (Finset.mem_insert_of_mem ht) (fun h'=>H.x_notMem_T (h' ▸ ht))
      (by omega) (by rw [Finset.card_insert_of_notMem H.x_notMem_T];omega)
    obtain ⟨p,hp,hl,-⟩:=(hp.concat (hyT t ht).symm
      (qa2' H.x_ne_y.symm H.y_notMem_T)).len (show i.val+1+1=2+i.val*1 by omega)
    exact ⟨p,hp,hl⟩
  · have hp:=qg9 H.T.card _ (hKT.insert hradj)
      s (Finset.mem_insert_of_mem hs) t (Finset.mem_insert_of_mem ht) hst (by omega)
      (by rw [Finset.card_insert_of_notMem hrT])
    have hxr : x≠r:=fun he=>hrH (he ▸ H.x_mem_verts)
    obtain ⟨p,hp,hl,-⟩:=((hp.cons (hxT s hs) (qa2' hxr H.x_notMem_T)).concat
      (hyT t ht).symm (qa2' H.x_ne_y.symm (qa2' (Ne.symm hry) H.y_notMem_T))).len
        (show H.T.card+1+1=2+i.val*1 by omega)
    exact ⟨p,hp,hl⟩
private theorem qp8 (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q)
    {H : Cc0 G x y} (hopt : Ioc0 G x y z H)
    (hC : ci0 G H.vertsᶜ y={y}) (hk : H.kind=.t2) : False:=by
  obtain ⟨hS,hT,-,-,-,-⟩:=H.shape2 hk
  obtain ⟨s,t,hst,hstS⟩:=Finset.card_eq_two.mp hS
  obtain ⟨hx,hy⟩:=(qb2 ih hHyp hq4 hfail hopt hC).1 hk
  rw [hstS] at hx hy
  obtain ⟨a,ha,b,hb,hab⟩:=Finset.one_lt_card.mp (by omega : 1 < H.T.card)
  have hw : ∃ v∈H.T,z≠some v:=by
    by_cases h : z=some a
    · exact ⟨b,hb,fun h'=>hab (Option.some.inj (h.symm.trans h'))⟩
    · exact ⟨a,ha,h⟩
  obtain ⟨v,hv,hvz⟩:=hw
  have hn : v∉H.S:=Finset.disjoint_right.mp H.disj hv
  have hs : s∈H.S:=hstS.symm ▸ Finset.mem_insert_self _ _
  have ht : t∈H.S:=hstS.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  exact hfail (qp6 ih hHyp hq4 (qb7 ih hHyp hq4 hfail) hst hx hy
    ⟨v,qa0 hv H.x_notMem_T,qa0 hv H.y_notMem_T,
      (qa0 hs hn).symm,(qa0 ht hn).symm,hvz⟩)
end Cr
namespace Cr
variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {x y : V} {z : Option V} {q : ℕ}
private theorem qag5 (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hK : Kc0 G 2)
    {H : Cc0 G x y} (hk : H.kind=.t3) (hS : H.S.card≤ 2)
    (hy : ∀ t∈H.T,G.Adj y t)
    {D : Finset V} (hD : Lk0 G D) (hsub : D⊆H.vertsᶜ) (hyD : y∉D)
    (hord : ∃ v∈D,z≠some v)
    (hcl : ∀ v∈D,∀ w,G.Adj v w→ w∈D∨w∈H.S)
    {s c : V} (hs : s∈H.S) (hc : c∈D) (hcs : G.Adj c s) : Adm0 G x y q:=by
  obtain ⟨-,hT,hxT,-,-,hST⟩:=H.shape3 hk
  obtain ⟨t₁,ht₁,t₂,ht₂,h12⟩:=Finset.one_lt_card.mp (by omega : 1 < H.T.card)
  have hdis : Disjoint D H.S:=Finset.disjoint_left.mpr fun _ hv hw =>
    outside_mem.mp (hsub hv) (H.S_subset_verts hw)
  have hxD : x∉D:=fun h=>outside_mem.mp (hsub h) H.x_mem_verts
  obtain ⟨a,d,ha,hd,hP⟩:=qp0 ih hHyp hq4 hK hD hxD hyD
    H.x_notMem_S H.y_notMem_S hdis hs hc hcs hcl hord (loss:=0) (show 0 < q from hHyp.1)
    (fun v _=>by
      have h:=Finset.card_le_card (Finset.inter_subset_right :
        G.neighborFinset v∩H.S.erase s⊆H.S.erase s)
      rw [Finset.card_erase_of_mem hs] at h
      omega)
  refine ⟨a+4,d,by omega,hd,fun i=>?_⟩
  obtain ⟨k,hk',hp⟩:=hP ⟨i.val,by simpa only [Nat.sub_zero] using i.isLt⟩
  have hkS:=Finset.mem_of_mem_erase hk'
  have hxk : x≠k:=(qa0 hkS H.x_notMem_S).symm
  have hxs : x≠s:=(qa0 hs H.x_notMem_S).symm
  have hxt : x≠t₁:=(hxT t₁ ht₁).ne
  have htD : t₂∉D:=fun h=>outside_mem.mp (hsub h) (H.T_subset_verts ht₂)
  have htS : t₂∉H.S:=Finset.disjoint_right.mp H.disj ht₂
  have htB : t₂∉insert k (insert s D):=qa2'
    (qa0 hkS htS).symm (qa2' (qa0 hs htS).symm htD)
  have hyB : y∉insert t₂ (insert k (insert s D)):=qa2' (hy t₂ ht₂).ne
    (qa2' (qa0 hkS H.y_notMem_S).symm
      (qa2' (qa0 hs H.y_notMem_S).symm hyD))
  have hp₁:=(Pi0.edge (hST k hkS t₁ ht₁).symm).cons (hxT t₁ ht₁) (qf5 hxt hxk)
  have hp₂:=(hp.concat (hST s hs t₂ ht₂) htB).concat (hy t₂ ht₂).symm hyB
  have hJ:=qaf8 hp₁ hp₂ (fun v hv hv'=>by
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv hv'
    rcases hv with h|h|h
    · subst v
      exact (hv'.elim (fun h=>H.x_ne_y h) fun h=>h.elim (hxT t₂ ht₂).ne
        (fun h=>h.elim hxk (fun h=>h.elim hxs hxD))).elim
    · subst v
      have hn₁ : t₁∉H.S:=Finset.disjoint_right.mp H.disj ht₁
      exact (hv'.elim (qa0 ht₁ H.y_notMem_T) fun h=>h.elim h12
        (fun h=>h.elim (qa0 hkS hn₁).symm (fun h =>
          h.elim (qa0 hs hn₁).symm
          (fun h=>outside_mem.mp (hsub h) (H.T_subset_verts ht₁))))).elim
    · exact h)
  obtain ⟨p,hp,hl⟩:=hJ
  exact ⟨p,hp,hl.trans (by ring)⟩
end Cr
open Cr in
theorem qo0 [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V} {z : Option V} {q : ℕ}
    (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q)
    {H : Cc0 G x y} (hopt : Ioc0 G x y z H)
    (hC : ci0 G (Finset.univ\H.verts) y={y}) (hk : H.kind=.t3) :
    ∃ t∈H.T,∃ v w,Rc0 G H.vertsᶜ v w∧G.Adj w t∧v≠y∧z≠some v:=by
  classical
  obtain ⟨hx,hy⟩:=(qb2 ih hHyp hq4 hfail hopt hC).2 (Or.inr hk)
  obtain ⟨hSTc,hT2,hxT,hIS,hIT,hST⟩:=H.shape3 hk
  have hyT : ∀ t∈H.T,G.Adj y t:=fun t ht=>(G.mem_neighborFinset _ _).mp (hy.symm ▸ ht)
  have hzT : ∀ t∈H.T,z≠some t:=fun t ht hz =>
    qc9 ih hHyp hq4 hfail t hz (hyT t ht)
  have hdT : ∀ t∈H.T,q+1≤ G.degree t:=fun t ht =>
    hHyp.2.2.2 t (qa0 ht H.x_notMem_T) (qa0 ht H.y_notMem_T) (hzT t ht)
  have hK:=qb7 ih hHyp hq4 hfail
  obtain ⟨t,ht⟩:=Finset.card_pos.mp (by omega : 0 < H.T.card)
  have hell:=qj7 H hfail (Rc0.refl (outside_mem.mpr H.y_notMem_verts)) ht (hyT t ht)
  rw [H.ell_t3 hk] at hell
  by_contra hno
  let B:=insert x (insert y H.S)
  have hB : B.card=H.S.card+2:=by
    change (insert x (insert y H.S)).card=_
    rw [Finset.card_insert_of_notMem (qa2' H.x_ne_y H.x_notMem_S),
      Finset.card_insert_of_notMem H.y_notMem_S]
  have hout : ∀ t∈H.T,∀ v,G.Adj t v→ v∉B→ v∉H.verts∧z=some v:=by
    intro u hu v huv hv
    have hvx : v≠x:=fun e=>hv (e ▸ Finset.mem_insert_self _ _)
    have hvy : v≠y:=fun e=>hv (e ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hvS : v∉H.S:=fun h=>hv (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
    have hvT : v∉H.T:=fun h=>hIT u hu v h huv
    have hvH : v∉H.verts:=fun h =>
      (Cc0.mem_verts.mp h).elim hvx (fun h=>h.elim hvS hvT)
    exact ⟨hvH,Classical.byContradiction fun hz =>
      hno ⟨u,hu,v,v,Rc0.refl (outside_mem.mpr hvH),huv.symm,hvy,hz⟩⟩
  have hlt : B.card < (G.neighborFinset t).card:=by
    rw [hB,card_neighborFinset_eq_degree]
    exact lt_of_le_of_lt hell (Nat.lt_of_succ_le (hdT t ht))
  obtain ⟨r,hr,hrB⟩:=Finset.exists_mem_notMem_of_card_lt_card hlt
  obtain ⟨hrH,hz⟩:=hout t ht r ((G.mem_neighborFinset _ _).mp hr) hrB
  have hry : r≠y:=fun h=>hrB (h ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  have hrx : r≠x:=qa0 H.x_mem_verts hrH |>.symm
  have hBc : (insert r B).card=H.S.card+3:=by
    rw [Finset.card_insert_of_notMem hrB,hB]
  have heq : ∀ t∈H.T,G.neighborFinset t=insert r B:=by
    intro t ht
    apply Finset.eq_of_subset_of_card_le
    · intro v hv
      by_cases hvB : v∈B
      · exact Finset.mem_insert_of_mem hvB
      · have h:=(hout t ht v ((G.mem_neighborFinset _ _).mp hv) hvB).2
        exact Finset.mem_insert.mpr (Or.inl (Option.some.inj (h.symm.trans hz)))
    · rw [hBc,card_neighborFinset_eq_degree]
      have:=hdT t ht
      omega
  have hrT : ∀ t∈H.T,G.Adj r t:=fun t ht =>
    ((G.mem_neighborFinset t r).mp ((heq t ht).symm ▸ Finset.mem_insert_self _ _)).symm
  have hSpos : 0 < H.S.card:=by
    have hd:=hdT t ht
    rw [← card_neighborFinset_eq_degree,heq t ht,hBc] at hd
    have:=qb6 ih hHyp hq4 hfail
    omega
  have hrS : ∀ s∈H.S,¬ G.Adj r s:=by
    apply qt4 (hopt.1.rank_ge hk) hk hrH hry
    rw [Finset.filter_true_of_mem hrT]
    exact hT2
  have hNr : G.neighborFinset r=H.T:=by
    ext v
    rw [mem_neighborFinset]
    refine ⟨fun h=>?_,hrT v⟩
    by_cases hv : v∈H.verts
    · rcases Cc0.mem_verts.mp hv with rfl|hs|ht
      · exact (qf3 ih hHyp hq4 hfail r hz hrx hry h.symm).elim
      · exact (hrS v hs h).elim
      · exact ht
    · have hvy : v≠y:=fun e =>
        qc9 ih hHyp hq4 hfail r hz (e ▸ h.symm)
      have hvz : z≠some v:=fun e=>h.ne (Option.some.inj (hz.symm.trans e))
      exact (hno ⟨t,ht,v,r,Rc0.adj (outside_mem.mpr hv) (outside_mem.mpr hrH) h.symm,
        hrT t ht,hvy,hvz⟩).elim
  have hTsmall : H.T.card=H.S.card+1:=by
    by_contra hcard
    have hrSn : r∉H.S:=fun h=>hrH (H.S_subset_verts h)
    let J:=Cc0.mk3 H.x_ne_y (insert r H.S) H.T
      (by rw [Finset.card_insert_of_notMem hrSn];omega) hT2 hxT
      (hIS.insert hrS) hIT (qa9' hrT hST)
      (qa2' hrx.symm H.x_notMem_S) (qa2' hry.symm H.y_notMem_S) H.y_notMem_T
    have h:=hopt.1.ell_ge J hk.symm
    change (insert r H.S).card≤ H.ell at h
    rw [Finset.card_insert_of_notMem hrSn,H.ell_t3 hk] at h
    omega
  obtain ⟨s,hs⟩:=Finset.card_pos.mp hSpos
  have hsord : z≠some s:=fun h=>hrH (Option.some.inj (hz.symm.trans h) ▸ H.S_subset_verts hs)
  have hds:=hHyp.2.2.2 s (qa0 hs H.x_notMem_S)
    (qa0 hs H.y_notMem_S) hsord
  obtain ⟨v,hv,hvT⟩:=Finset.exists_mem_notMem_of_card_lt_card
    (s:=H.T) (t:=G.neighborFinset s) (by rw [card_neighborFinset_eq_degree];omega)
  have hsv:=(G.mem_neighborFinset _ _).mp hv
  have hvx : v≠x:=fun h=>(Finset.disjoint_left.mp H.disj hs)
    (hx ▸ (G.mem_neighborFinset x s).mpr (h ▸ hsv.symm))
  have hvy : v≠y:=fun h=>(Finset.disjoint_left.mp H.disj hs)
    (hy ▸ (G.mem_neighborFinset y s).mpr (h ▸ hsv.symm))
  have hvz : z≠some v:=fun h=>(Finset.disjoint_left.mp H.disj hs)
    (hNr ▸ (G.mem_neighborFinset r s).mpr (Option.some.inj (hz.symm.trans h) ▸ hsv.symm))
  have hvH : v∉H.verts:=fun h=>(Cc0.mem_verts.mp h).elim hvx
    (fun h=>h.elim (fun hvS=>hIS s hs v hvS hsv) hvT)
  let D:=ci0 G H.vertsᶜ v
  have hvD : v∈D:=mem_compIn.mpr (Rc0.refl (outside_mem.mpr hvH))
  have hyD : y∉D:=qk7 hC hvy
  have hbound : ∀ d∈D,∀ w,G.Adj d w→ w∈D∨w∈H.S:=by
    intro d hd w hdw
    refine (qx2 (D:=D) rfl d hd w hdw).imp_right fun hw=>?_
    rcases Cc0.mem_verts.mp hw with hwx|hs'|ht'
    · subst w
      have hdT : d∈H.T:=hx ▸ (G.mem_neighborFinset x d).mpr hdw.symm
      exact (outside_mem.mp (qe7 hd) (H.T_subset_verts hdT)).elim
    · exact hs'
    · exact (hno ⟨w,ht',v,d,mem_compIn.mp hd,hdw,hvy,hvz⟩).elim
  exact hfail (qag5 ih hHyp hq4 hK hk (by omega) hyT qk3 qe7
    hyD ⟨v,hvD,hvz⟩ hbound hs hvD hsv.symm)
open Cr in
theorem qo1 [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V} {z : Option V} {q : ℕ}
    (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q)
    {H : Cc0 G x y} (hopt : Ioc0 G x y z H)
    (hC : ci0 G (Finset.univ\H.verts) y={y}) : ∃ t,Ft0 z H t:=by
  cases hk : H.kind
  · exact (qp9 ih hHyp hq4 hfail hopt hC hk).elim
  · exact (qp8 ih hHyp hq4 hfail hopt hC hk).elim
  · obtain ⟨t,ht,v,w,hvw,hwt,hvy,hvz⟩:=qo0 ih hHyp hq4 hfail hopt hC hk
    obtain ⟨hx,hy⟩:=(qb2 ih hHyp hq4 hfail hopt hC).2 (Or.inr hk)
    by_cases hT : 3≤ H.T.card
    · refine ⟨t,hk,hT,fun c hc=>?_,hx,hy,ht,v,w,hvw,hwt,hvy,hvz⟩
      have h : c∈ci0 G (Finset.univ\H.verts) y:=mem_compIn.mpr hc
      rwa [hC,Finset.mem_singleton] at h
    · obtain ⟨s₁,s₂,hs,hS⟩:=Finset.card_eq_two.mp (by have:=H.two_le_T;omega : H.T.card=2)
      rw [hS] at hx hy
      have hvH:=outside_mem.mp hvw.left_mem
      have h₁ : s₁∈H.T:=hS.symm ▸ Finset.mem_insert_self _ _
      have h₂ : s₂∈H.T:=hS.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
      exact (hfail (qp6 ih hHyp hq4 (qb7 ih hHyp hq4 hfail) hs hx hy
        ⟨v,(qa0 H.x_mem_verts hvH).symm,hvy,
          (qa0 (H.T_subset_verts h₁) hvH).symm,
          (qa0 (H.T_subset_verts h₂) hvH).symm,hvz⟩)).elim
structure Wc0 [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (x y : V) (z : Option V) where
  base : Cc0 G x y
  hopt : Ioc0 G x y z base
  core : Cc0 G x y
  isFlat : Option V
  h_mode : match isFlat with
    | none=>core=base∧ci0 G (Finset.univ\base.verts) y≠{y}
    | some t=>Ifo0 base core t∧Ft0 z base t
  hK : Kc0 G 2
  C : Finset V
  hC_eq : C=ci0 G (Finset.univ\core.verts) y
  hC_nontriv : ∃ v∈C,v≠y∧z≠some v
  h_ext_deg : ∀ v∉core.verts,v≠y→ isFlat≠some v →
    (G.neighborFinset v∩core.verts).card≤ core.ell+1 ∧
      ((G.neighborFinset v∩core.verts).card=core.ell+1→ ∃ t∈core.T,G.Adj v t)
  h_flat_large : ∀ t,isFlat=some t→ 2≤ (C.filter (fun v=>v≠y∧z≠some v)).card
namespace Wc0
open Cr
variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {x y : V} {z : Option V} {q : ℕ}
theorem h_ell_le (W : Wc0 G x y z) (hfail : ¬ Adm0 G x y q) :
    W.core.ell≤ q - 1:=by
  have:=qak9 W.hK W.core hfail
  omega
theorem h_ell_le_tight (W : Wc0 G x y z) (hfail : ¬ Adm0 G x y q)
    (h : W.core.kind=.t1∨∃ v∈W.C,∃ t∈W.core.T,G.Adj v t) :
    W.core.ell≤ q - 2:=by
  have hb : W.core.ell+2≤ q:=by
    rcases h with hk|⟨v,hv,t,ht,hvt⟩
    · exact qt1 W.hK W.core hk hfail
    · rw [W.hC_eq] at hv
      exact qj7 W.core hfail (mem_compIn.mp hv) ht hvt
  omega
theorem qan1 (W : Wc0 G x y z)
    (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q)
    (hk : W.core.kind=.t1∨W.core.kind=.t3)
    {D : Finset V} {b : V} (hD : D=ci0 G (Finset.univ\W.core.verts) b)
    (hyD : y∉D) (hord : ∃ v∈D,z≠some v)
    (hcase : W.isFlat≠none ∨
      (∀ v∈D,¬ G.Adj v x)∧(∀ t∈W.core.T,G.Adj y t)) :
    ∃ v∈D,∃ s∈W.core.S,G.Adj v s:=by
  have hsub : D⊆W.core.vertsᶜ:=hD ▸ qe7
  have hext : ∀ v∈D,W.isFlat≠some v →
      (G.neighborFinset v∩W.core.verts).card≤ W.core.ell+1:=fun v hv hm =>
    (W.h_ext_deg v (outside_mem.mp (hsub hv)) (qa0 hv hyD) hm).1
  cases hf : W.isFlat with
  | none =>
    obtain ⟨hx,hy⟩:=hcase.resolve_left (fun h=>h hf)
    exact other_hits ih hHyp hq4 hfail hk hD hyD hord hx hy
      (fun v hv=>hext v hv (by simp [hf]))
  | some t =>
    have hmode:=W.h_mode
    rw [hf] at hmode
    obtain ⟨hflat,htr⟩:=hmode
    have htx:=htr.2.2.2.1
    have hty:=htr.2.2.2.2.1
    have ht : G.Adj y t:=(G.mem_neighborFinset _ _).mp (hty.symm ▸ hflat.2.1)
    have htD : t∉D:=by
      intro h
      have hreach:=Rc0.adj (outside_mem.mpr hflat.t₀_notMem)
        (outside_mem.mpr W.core.y_notMem_verts) ht.symm
      apply hyD
      rw [hD] at h ⊢
      exact mem_compIn.mpr ((mem_compIn.mp h).trans hreach)
    apply other_hits ih hHyp hq4 hfail hk hD hyD hord
    · intro v hv hvx
      have hvT : v∈W.base.T:=htx ▸ (G.mem_neighborFinset _ _).mpr hvx.symm
      have hvT' : v∈W.core.T:=by
        rw [hflat.2.2.2.1]
        exact Finset.mem_erase.mpr ⟨qa0 hv htD,hvT⟩
      exact outside_mem.mp (hsub hv) (W.core.T_subset_verts hvT')
    · exact fun s hs=>(G.mem_neighborFinset _ _).mp (hty.symm ▸ hflat.T_subset hs)
    · exact fun v hv=>hext v hv (fun e=>htD (Option.some.inj (hf.symm.trans e) ▸ hv))
end Wc0
namespace Cr
variable [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {x y : V} {z : Option V} {q : ℕ}
private theorem working_of_optimal (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q)
    {H : Cc0 G x y} (hopt : Ioc0 G x y z H) : Nonempty (Wc0 G x y z):=by
  classical
  have hK:=qb7 ih hHyp hq4 hfail
  have hyz:=qc9 ih hHyp hq4 hfail
  by_cases hC : ci0 G H.vertsᶜ y={y}
  · obtain ⟨t,htr⟩:=qo1 ih hHyp hq4 hfail hopt hC
    obtain ⟨Hf,hf⟩:=qp4 htr
    let C:=ci0 G Hf.vertsᶜ y
    obtain ⟨a,b,hab,hay,hby,haz,hbz,ha,hb⟩:=qs0 htr hf hyz
    have haC : a∈C:=mem_compIn.mpr ha
    have hbC : b∈C:=mem_compIn.mpr hb
    have hcount : 2≤ (C.filter (fun v=>v≠y∧z≠some v)).card :=
      Nat.succ_le_of_lt (Finset.one_lt_card.mpr
        ⟨a,Finset.mem_filter.mpr ⟨haC,hay,haz⟩,b,Finset.mem_filter.mpr ⟨hbC,hby,hbz⟩,hab⟩)
    exact ⟨{ base:=H
             hopt:=hopt
             core:=Hf
             isFlat:=some t
             h_mode:=⟨hf,htr⟩
             hK:=hK
             C:=C
             hC_eq:=rfl
             hC_nontriv:=⟨a,haC,hay,haz⟩
             h_ext_deg:=fun v hv hvy hvt=>qac3 hopt.1 htr.2.2.2.1 hf hv hvy
               (fun h=>hvt (congrArg some h.symm))
             h_flat_large:=fun _ _=>hcount }⟩
  · let C:=ci0 G H.vertsᶜ y
    have hy : y∈C:=mem_compIn.mpr (Rc0.refl (outside_mem.mpr H.y_notMem_verts))
    have hex : ∃ v∈C,v≠y:=by
      by_contra! h
      exact hC (Finset.eq_singleton_iff_unique_mem.mpr ⟨hy,h⟩)
    obtain ⟨v,hv,hvy⟩:=hex
    obtain ⟨w,hw,hyw⟩:=Cb.adj_of_linked qk3 hy hv hvy
    exact ⟨{ base:=H
             hopt:=hopt
             core:=H
             isFlat:=none
             h_mode:=⟨rfl,hC⟩
             hK:=hK
             C:=C
             hC_eq:=rfl
             hC_nontriv:=⟨w,hw,hyw.ne.symm,fun h=>hyz w h hyw⟩
             h_ext_deg:=fun _ hv hvy _=>ql7 hopt.1 hv hvy
             h_flat_large:=fun _ h=>by cases h }⟩
end Cr
theorem qu1 [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {x y : V} {z : Option V} {q : ℕ}
    (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q) :
    Nonempty (Wc0 G x y z)∨Nonempty (Wc0 G y x z):=by
  rcases qu2 (qb7 ih hHyp hq4 hfail) hHyp.2.1.1
    (qb3 ih hHyp hq4 hfail) z with ⟨H,hH⟩|⟨H,hH⟩
  · exact Or.inl (Cr.working_of_optimal ih hHyp hq4 hfail hH)
  · obtain ⟨hh,hf⟩:=qm6 ih hHyp hq4 hfail
    exact Or.inr (Cr.working_of_optimal ih hh hq4 hf hH)
end DeanK5
end M10
section M11
namespace DeanK5
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {x y : V} {z : Option V} {q : ℕ}
namespace Fa
open Cb
omit [Fintype V] [DecidableRel G.Adj] in
theorem qae9 {A B : Finset V} {p n a b d e : ℕ}
    (hp : 1≤ p) (hn : 1≤ n) (hab : 2≤ a+b)
    (hd : d=1∨d=2) (he : e=1∨e=2)
    (h : ∀ j : Fin n,∃ t,Pi0 G (insert t B) t y (b+j.val*e) ∧
      ∀ i : Fin p,Pi0 G A x t (a+i.val*d)) (hAB : Disjoint A B) :
    Adm0 G x y (p+n - 1):=by
  classical
  obtain ⟨c,f,hc,hf,hs⟩:=qi9 hp hn hd he a b
  refine ⟨c,f,hab.trans hc,hf,fun k=>?_⟩
  obtain ⟨i,j,hij⟩:=hs k
  obtain ⟨t,⟨Q,hQ,hlQ,hsQ⟩,hP⟩:=h j
  obtain ⟨P,hP,hlP,hsP⟩:=hP i
  have hj:=qa3 hP hQ fun v hv hw =>
    (Finset.mem_insert.mp (hsQ v hw)).resolve_right (Finset.disjoint_left.mp hAB (hsP v hv))
  exact ⟨P.append Q,hj.1,by rw [hj.2.1,hlP,hlQ,hij]⟩
theorem qa1 (W : Wc0 G x y z) {v : V} (hv : v∈W.C) :
    v∉W.core.verts :=
  (Finset.mem_sdiff.mp (qe7 (W.hC_eq ▸ hv))).2
theorem qc2 (W : Wc0 G x y z) : y∈W.C:=by
  rw [W.hC_eq]
  exact mem_compIn.mpr (Rc0.refl (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,W.core.y_notMem_verts⟩))
theorem linked (W : Wc0 G x y z) : Lk0 G W.C :=
  W.hC_eq.symm ▸ qk3
theorem qh9 (W : Wc0 G x y z) {v w : V} (hv : v∈W.C) (h : G.Adj v w) :
    w∈W.C∨w∈W.core.verts:=by
  rw [W.hC_eq] at hv ⊢
  exact (qo6 hv h).imp_right fun h=>by simpa using h
theorem mem_neighbors_in {C : Finset V} {u v : V} :
    v∈G.neighborFinset u∩C↔G.Adj u v∧v∈C:=by
  rw [Finset.mem_inter,mem_neighborFinset]
private theorem qab6 (W : Wc0 G x y z) {v : V} (hv : v∈W.C) : v≠x :=
  (qa0 W.core.x_mem_verts (qa1 W hv)).symm
theorem qj4 (W : Wc0 G x y z) {v : V} (hv : v∈W.C) :
    G.degree v=(G.neighborFinset v∩W.C).card+(G.neighborFinset v∩W.core.verts).card:=by
  have hd : Disjoint (G.neighborFinset v∩W.C) (G.neighborFinset v∩W.core.verts) :=
    Finset.disjoint_left.mpr fun _ h h' =>
      qa1 W (Finset.mem_inter.mp h).2 (Finset.mem_inter.mp h').2
  have hu : (G.neighborFinset v∩W.C)∪(G.neighborFinset v∩W.core.verts) =
      G.neighborFinset v:=by
    ext w
    simp only [Finset.mem_union,Finset.mem_inter,mem_neighborFinset]
    exact ⟨fun h=>h.elim And.left And.left,
      fun h=>(qh9 W hv h).elim (fun hw=>Or.inl ⟨h,hw⟩) (fun hw=>Or.inr ⟨h,hw⟩)⟩
  rw [← card_neighborFinset_eq_degree,← Finset.card_union_of_disjoint hd,hu]
theorem qt2 (W : Wc0 G x y z) {u v : V} (hu : u∈W.C) (hv : v∈W.C) :
    ∃ n,Pi0 G W.C u v n:=by
  classical
  obtain ⟨P,hP⟩:=linked W u hu v hv
  exact ⟨_,P.bypass,P.bypass_isPath,rfl,fun a ha=>hP a (P.support_bypass_subset_support ha)⟩
omit [DecidableRel G.Adj] in
private theorem qy3 {D : Finset V} {s : V} (hK : Kc0 G 2)
    (hxs : x≠s) (hx : x∈Dᶜ) (hs : s∈Dᶜ) (hc : 2 < Dᶜ.card)
    (hout : ∀ v∈D,∀ w,G.Adj v w→ w∈D∨w=x∨w=s) :
    Rt0 (G.induce (Dᶜ : Finset V)) ⟨x,hx⟩ ⟨s,hs⟩:=by
  classical
  refine qb4 hxs hc (fun w _ u hu v hv=>?_) hx hs
  let r:=if w=x then s else x
  have hr : r∈Dᶜ.erase w:=by
    by_cases he : w=x
    · simpa [r,he,hxs.symm] using hs
    · simpa [r,he,Ne.symm he] using hx
  let f:=fun a : V=>if a∈D then r else a
  have houtside (a : V) (ha : a∈Dᶜ.erase w) : f a=a :=
    if_neg (Finset.mem_compl.mp (Finset.mem_of_mem_erase ha))
  have hedge (a : V) (ha : a∈D) (b : V) (hb : b∉D) (hbw : b≠w) (hab : G.Adj a b) :
      f a=f b∨(G ⊔ edge x s).Adj (f a) (f b):=by
    simp only [f,if_pos ha,if_neg hb]
    rcases (hout a ha b hab).resolve_left hb with rfl|rfl
    · exact Or.inl (if_neg (Ne.symm hbw))
    · by_cases he : w=x
      · exact Or.inl (if_pos he)
      · exact Or.inr (Or.inr (by simp [r,he,edge_adj,hxs]))
  have hreach:=(kConn_two_iff.mp hK).2 w u (by simp [Finset.ne_of_mem_erase hu]) v
    (by simp [Finset.ne_of_mem_erase hv])
  have hproj : Rc0 (G ⊔ edge x s) (Dᶜ.erase w) (f u) (f v):=by
    apply hreach.proj f
    · intro a ha b hb hab
      by_cases haD : a∈D <;> by_cases hbD : b∈D
      · exact Or.inl (by simp [f,haD,hbD])
      · exact hedge a haD b hbD (Finset.ne_of_mem_erase hb) hab
      · exact (hedge b hbD a haD (Finset.ne_of_mem_erase ha) hab.symm).elim
          (Or.inl ∘ Eq.symm) (Or.inr ∘ Adj.symm)
      · simpa [f,haD,hbD] using
          (Or.inr (Or.inl hab) : a=b∨(G ⊔ edge x s).Adj a b)
    · intro a ha
      by_cases haD : a∈D
      · simpa [f,haD] using hr
      · simp [f,haD,Finset.ne_of_mem_erase ha]
  rwa [houtside u hu,houtside v hv] at hproj
end Fa
open Fa Cb in
theorem qp5 (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q)
    (W : Wc0 G x y z) (hS : W.core.S.card=1) :
    ∃ v∈W.C,∃ t∈W.core.T,G.Adj v t:=by
  classical
  by_contra hT
  obtain ⟨s,hs⟩:=Finset.card_eq_one.mp hS
  have hsS : s∈W.core.S:=hs.symm ▸ Finset.mem_singleton_self s
  have hxs : x≠s:=fun e=>W.core.x_notMem_S (e ▸ hsS)
  have hsub : W.core.verts⊆W.Cᶜ:=fun v hv =>
    Finset.mem_compl.mpr fun hc=>qa1 W hc hv
  have hx:=hsub W.core.x_mem_verts
  have hs':=hsub (W.core.S_subset_verts hsS)
  have hout (v : V) (hv : v∈W.C) (w : V) (h : G.Adj v w) :
      w∈W.C∨w=x∨w=s:=by
    refine (qh9 W hv h).imp_right fun hw=>?_
    rw [Cc0.mem_verts,hs,Finset.mem_singleton] at hw
    exact hw.elim Or.inl fun hw=>Or.inr (hw.resolve_right fun ht=>hT ⟨v,hv,w,ht,h⟩)
  have hTc:=W.core.two_le_T
  have hTs : W.core.T⊆W.Cᶜ:=fun _ ht=>hsub (W.core.T_subset_verts ht)
  have hc : 2 < W.Cᶜ.card:=by
    have hle:=Finset.card_le_card (Finset.insert_subset hx hTs)
    rw [Finset.card_insert_of_notMem W.core.x_notMem_T] at hle
    omega
  have hsize:=card_lt_of_notMem (s:=W.Cᶜ) (Finset.notMem_compl.mpr (qc2 W))
  obtain ⟨t₁,ht₁,t₂,ht₂,hne⟩:=Finset.one_lt_card.mp (by omega : 1 < W.core.T.card)
  have ht (t : V) (ht : t∈W.core.T) : t≠x∧t≠s :=
    ⟨qa0 ht W.core.x_notMem_T,fun e=>Finset.disjoint_left.mp W.core.disj hsS (e ▸ ht)⟩
  have hwit : ∃ t∈W.Cᶜ,t≠x∧t≠s∧z≠some t:=by
    by_cases ht₁z : z=some t₁
    · exact ⟨t₂,hTs ht₂,(ht _ ht₂).1,(ht _ ht₂).2,
        fun e=>hne (Option.some.inj (ht₁z.symm.trans e))⟩
    · exact ⟨t₁,hTs ht₁,(ht _ ht₁).1,(ht _ ht₁).2,ht₁z⟩
  have hA:=induce_call (ih.toAt hq4) W.Cᶜ hx hs' z hHyp.1
    (qy3 W.hK hxs hx hs' hc hout) (by omega) (fun u hu hux hus huz =>
      ⟨hHyp.2.2.2 u hux (qa0 (qc2 W) (Finset.mem_compl.mp hu)).symm huz,
        fun w huw=>Finset.mem_compl.mpr fun hw =>
          ((hout w hw u huw.symm).resolve_left (Finset.mem_compl.mp hu)).elim hux hus⟩) hwit
  obtain ⟨c,hc,d,hd,hdx,hcd⟩:=qr3 W.hK (qc2 W)
    (qa1 W · (W.core.T_subset_verts ht₁))
    (fun e=>qa1 W (qc2 W) (e ▸ W.core.x_mem_verts))
    (ht _ ht₁).1
  have hds:=((hout c hc d hcd).resolve_left hd).resolve_left hdx
  subst d
  obtain ⟨n,hP⟩:=qt2 W hc (qc2 W)
  obtain ⟨Q,hQ,-,hQs⟩:=hP.cons hcd.symm (Finset.mem_compl.mp hs')
  exact hfail (qr4 hA Q hQ fun v hv hv' =>
    (Finset.mem_insert.mp (hQs v hv)).resolve_right (Finset.mem_compl.mp hv'))
namespace Fa
omit [Fintype V] [DecidableRel G.Adj] in
theorem qaf0 (H : Cc0 G x y) :
    ∃ a d : ℕ,1≤ a∧(d=1∨d=2) ∧
      ∀ t∈H.T,∀ i : Fin (H.ell+1),Pi0 G H.verts x t (a+i.val*d):=by
  cases hk : H.kind
  · refine ⟨1,1,le_rfl,Or.inl rfl,fun t ht i=>qx1 H hk ht _ ?_⟩
    exact Finset.mem_Icc.mpr ⟨by omega,by have:=i.isLt;omega⟩
  · refine ⟨2,1,by omega,Or.inl rfl,fun t ht i=>ql6 H hk ht _ ?_⟩
    exact Finset.mem_Icc.mpr ⟨by omega,by have:=i.isLt;omega⟩
  · exact ⟨1,2,le_rfl,Or.inr rfl,fun t ht i=>(ql5 H hk ht i).len (by ring)⟩
omit [Fintype V] [DecidableRel G.Adj] in
theorem qaf1 (H : Cc0 G x y) :
    ∃ a d : ℕ,2≤ a∧(d=1∨d=2) ∧
      ∀ s∈H.S,∀ i : Fin H.ell,Pi0 G H.verts x s (a+i.val*d):=by
  cases hk : H.kind
  · refine ⟨2,1,le_rfl,Or.inl rfl,fun s hs _=>?_⟩
    rw [(H.shape1 hk).1] at hs
    exact (Finset.notMem_empty s hs).elim
  · refine ⟨3,1,by omega,Or.inl rfl,fun s hs i=>qh8 H hk hs _ ?_⟩
    exact Finset.mem_insert_of_mem (Finset.mem_Icc.mpr ⟨by omega,by have:=i.isLt;omega⟩)
  · obtain ⟨t,ht⟩:=Finset.card_pos.mp (by have:=H.two_le_T;omega : 0 < H.T.card)
    exact ⟨2,2,le_rfl,Or.inr rfl,fun s hs i =>
      ((qr0 H hk hs ht i).mono (Finset.erase_subset _ _)).len (by ring)⟩
theorem qag4 (W : Wc0 G x y z) {n b e : ℕ} (hn : 1≤ n) (hb : 1≤ b)
    (he : e=1∨e=2)
    (h : ∀ j : Fin n,∃ t∈W.core.T,Pi0 G (insert t W.C) t y (b+j.val*e)) :
    Adm0 G x y (W.core.ell+1+n - 1):=by
  obtain ⟨a,d,ha,hd,hP⟩:=qaf0 W.core
  exact qae9 (by omega) hn (by omega) hd he
    (fun j=>(h j).imp fun t ⟨ht,hQ⟩=>⟨hQ,hP t ht⟩)
    (Finset.disjoint_left.mpr fun _ hv hc=>qa1 W hc hv)
theorem qal6 (W : Wc0 G x y z) {n b e : ℕ} (hn : 1≤ n) (hp : 1≤ W.core.ell)
    (he : e=1∨e=2)
    (h : ∀ j : Fin n,∃ s∈W.core.S,Pi0 G (insert s W.C) s y (b+j.val*e)) :
    Adm0 G x y (W.core.ell+n - 1):=by
  obtain ⟨a,d,ha,hd,hP⟩:=qaf1 W.core
  exact qae9 hp hn (by omega) hd he
    (fun j=>(h j).imp fun s ⟨hs,hQ⟩=>⟨hQ,hP s hs⟩)
    (Finset.disjoint_left.mpr fun _ hv hc=>qa1 W hc hv)
private theorem qac2 (W : Wc0 G x y z) {t : V} (ht : W.isFlat=some t) :
    Ifo0 W.base W.core t∧Ft0 z W.base t:=by
  simpa only [ht] using W.h_mode
private theorem qaq8 (W : Wc0 G x y z) {t : V} (ht : W.isFlat=some t) :
    G.neighborFinset y∩W.C={t}:=by
  obtain ⟨hf,htr⟩:=qac2 W ht
  have hNy:=htr.2.2.2.2.1
  ext v
  rw [Finset.mem_inter,Finset.mem_singleton,hNy]
  constructor
  · rintro ⟨hv,hvC⟩
    by_contra hne
    apply qa1 W hvC
    exact W.core.T_subset_verts (hf.2.2.2.1.symm ▸ Finset.mem_erase.mpr ⟨hne,hv⟩)
  · rintro rfl
    have hyt : G.Adj y v:=(mem_neighborFinset _ _ _).mp (hNy.symm ▸ hf.2.1)
    exact ⟨hf.2.1,W.hC_eq.symm ▸ mem_compIn.mpr (Rc0.adj
      (by simp [W.core.y_notMem_verts]) (by simp [hf.t₀_notMem]) hyt)⟩
private theorem qap2 (W : Wc0 G x y z) {t s : V} (ht : W.isFlat=some t)
    (hs : s∈W.base.S) (hS : W.core.S=W.base.S.erase s) :
    3≤ (G.neighborFinset t∩W.C).card:=by
  obtain ⟨hf,htr⟩:=qac2 W ht
  have hyt:=mem_neighbors_in.mp
    ((qaq8 W ht).symm ▸ Finset.mem_singleton_self t)
  have hts:=(W.base.shape3 hf.1).2.2.2.2.2 s hs t hf.2.1
  have hsH : s∉W.core.verts:=by
    rw [Cc0.mem_verts,hS]
    exact fun h=>h.elim (qa0 hs W.base.x_notMem_S) fun h =>
      h.elim (Finset.notMem_erase _ _) (fun h=>Finset.disjoint_left.mp W.base.disj hs (hf.T_subset h))
  obtain ⟨d,d₀,hD,hd₀,hdy,-⟩:=htr.2.2.2.2.2.2
  have hd₀H : d₀∉W.base.verts:=Finset.mem_compl.mp hD.right_mem
  have hd₀y : d₀≠y:=fun e=>hdy (htr.2.2.1 d (e ▸ hD.symm))
  have hin (v : V) (hv : G.Adj t v) (hvH : v∉W.core.verts) :
      v∈G.neighborFinset t∩W.C :=
    mem_neighbors_in.mpr ⟨hv,(qh9 W hyt.2 hv).resolve_right hvH⟩
  have hy:=hin y hyt.1.symm W.core.y_notMem_verts
  have hsub : ({y,s,d₀} : Finset V)⊆G.neighborFinset t∩W.C :=
    Finset.insert_subset hy (Finset.insert_subset (hin s hts.symm hsH)
      (Finset.singleton_subset_iff.mpr (hin d₀ hd₀.symm (fun h=>hd₀H (hf.verts_subset h)))))
  have hcard:=Finset.card_le_card hsub
  have hsd : s≠d₀:=qa0 (W.base.S_subset_verts hs) hd₀H
  rw [Finset.card_insert_of_notMem (qf5
    (qa0 hs W.base.y_notMem_S).symm hd₀y.symm),Finset.card_pair hsd] at hcard
  exact hcard
private theorem qy9 (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q)
    (W : Wc0 G x y z) {b zv : V} (hz : z=some zv) (hzC : zv∈W.C) (hzy : zv≠y)
    (hleaf : G.neighborFinset zv∩W.C={b})
    (hT : ∀ t∈W.core.T,¬ G.Adj zv t) : ∃ s∈W.core.S,G.Adj zv s:=by
  have hzx:=qab6 W hzC
  obtain ⟨v,hv,hvb⟩:=Cb.exists_adj_ne W.hK zv b
  have hv' : v∉W.C:=fun hvC=>hvb (Finset.mem_singleton.mp (hleaf ▸
    mem_neighbors_in.mpr ⟨hv,hvC⟩))
  rcases Cc0.mem_verts.mp ((qh9 W hzC hv).resolve_left hv') with rfl|hs|ht
  · exact (qf3 ih hHyp hq4 hfail zv hz hzx hzy hv.symm).elim
  · exact ⟨v,hs,hv⟩
  · exact (hT v ht hv).elim
omit [Fintype V] [DecidableRel G.Adj] in
theorem qv1 {A D : Finset V} {c v : V} (hc : c∉D) (hv : v∉D)
    (hD : ∀ a∈D,∀ w∈A,G.Adj a w→ w∈D∨w=c)
    {P : G.Walk c v} (hP : P.IsPath) (hA : ∀ a∈P.support,a∈A) :
    ∀ a∈P.support,a∉D:=by
  cases P with
  | nil=>simpa using hc
  | cons h Q =>
    rw [Walk.cons_isPath_iff] at hP
    intro a ha haD
    rw [Walk.support_cons,List.mem_cons] at ha
    rcases ha with rfl|ha
    · exact hc haD
    · apply hv
      apply qb9 (D:=fun w=>w∉A∨w=c)
        (fun u hu w huw=>by
          by_cases hw : w∈A
          · exact (hD u hu w hw huw).imp_right Or.inr
          · exact Or.inr (Or.inl hw)) (Q.dropUntil a ha) haD _ _ (Walk.end_mem_support _)
      intro w hw
      have hwQ:=Q.support_dropUntil_subset_support ha hw
      exact fun e=>e.elim (fun e=>e (hA w (by simp [hwQ]))) (fun e=>hP.2 (e ▸ hwQ))
theorem qap1 (W : Wc0 G x y z) {b zv : V} (hbC : b∈W.C)
    (hzC : zv∈W.C) (hby : b≠y) (hzy : zv≠y) (hleaf : G.neighborFinset zv∩W.C={b})
    (hb2 : (G.neighborFinset b∩W.C).card=2) :
    ∃ c∈W.C,∃ n,G.Adj b zv∧G.Adj b c∧c≠zv ∧
      G.neighborFinset b∩W.C={zv,c}∧Pi0 G ((W.C.erase zv).erase b) c y n:=by
  classical
  have hzb:=(mem_neighbors_in.mp (hleaf.symm ▸ Finset.mem_singleton_self b)).1
  have hzm:=mem_neighbors_in.mpr ⟨hzb.symm,hzC⟩
  obtain ⟨c,hc,hcz⟩:=Finset.exists_mem_ne (by omega : 1 < (G.neighborFinset b∩W.C).card) zv
  have he:=Finset.eq_of_subset_of_card_le
    (Finset.insert_subset hzm (Finset.singleton_subset_iff.mpr hc))
    (by rw [hb2,Finset.card_pair hcz.symm])
  obtain ⟨hbc,hcC⟩:=mem_neighbors_in.mp hc
  obtain ⟨n,P,hP,hl,hPs⟩:=qt2 W hcC (qc2 W)
  have hav (a : V) (ha : a∈P.support) : a∉({b,zv} : Finset V) :=
    qv1 (by simp [hbc.ne.symm,hcz]) (by simp [hby.symm,hzy.symm])
      (fun u hu w hw huw=>by
        rcases Finset.mem_insert.mp hu with rfl|hu
        · have hw':=Finset.mem_insert.mp (he.symm ▸ mem_neighbors_in.mpr ⟨huw,hw⟩)
          exact hw'.elim (fun e=>Or.inl (by simp [e])) (fun e=>Or.inr (Finset.mem_singleton.mp e))
        · rw [Finset.mem_singleton.mp hu] at huw
          have e:=Finset.mem_singleton.mp (hleaf ▸ mem_neighbors_in.mpr ⟨huw,hw⟩)
          exact Or.inl (by simp [e])) hP hPs a ha
  exact ⟨c,hcC,n,hzb.symm,hbc,hcz,he.symm,P,hP,hl,
    fun a ha=>by simpa [and_assoc] using And.intro (hav a ha) (hPs a ha)⟩
private theorem qk8 (W : Wc0 G x y z) {b : V}
    (h : ∀ v∈W.C,v=y∨v=b∨z=some v) :
    (W.C.filter (fun v=>v≠y∧z≠some v)).card≤ 1:=by
  simpa using (Finset.card_le_card (t:={b}) fun v hv=>by
    obtain ⟨hvC,hvy,hvz⟩:=Finset.mem_filter.mp hv
    exact Finset.mem_singleton.mpr ((h v hvC).resolve_left hvy |>.resolve_right hvz) :
      (W.C.filter (fun v=>v≠y∧z≠some v)).card≤ ({b} : Finset V).card)
private theorem qy0 (W : Wc0 G x y z)
    (h : (W.C.filter (fun v=>v≠y∧z≠some v)).card≤ 1) :
    W.isFlat=none∧W.core=W.base:=by
  cases hf : W.isFlat with
  | none=>exact ⟨rfl,(show W.core=W.base∧_ by simpa only [hf] using W.h_mode).1⟩
  | some t =>
    have:=W.h_flat_large t hf
    omega
private theorem qr9 (W : Wc0 G x y z) {b zv c : V}
    (hz : z=some zv) (hzy : zv≠y)
    (hleaf : G.neighborFinset zv∩W.C={b})
    (hpair : G.neighborFinset b∩W.C={zv,c}) : W.isFlat≠some b:=by
  classical
  intro hf
  have hy:=qaq8 W hf
  have hyb:=(mem_neighbors_in.mp (hy.symm ▸ Finset.mem_singleton_self b)).1
  have hc : c=y:=by
    have h:=Finset.mem_insert.mp (hpair ▸ mem_neighbors_in.mpr ⟨hyb.symm,qc2 W⟩)
    exact (Finset.mem_singleton.mp (h.resolve_left hzy.symm)).symm
  subst c
  have hsub : W.C⊆{y,b,zv}:=by
    intro v hv
    obtain ⟨P,hP⟩:=linked W y (qc2 W) v hv
    refine qb9 (D:=fun w=>w∉W.C) (fun a ha w haw=>?_)
      P (Finset.mem_insert_self _ _) (fun a ha h=>h (hP a ha)) v P.end_mem_support
    by_cases hw : w∈W.C
    · left
      have h:=mem_neighbors_in.mpr ⟨haw,hw⟩
      simp only [Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with rfl|rfl|rfl <;>
        simp_all only [Finset.mem_insert,Finset.mem_singleton] <;> tauto
    · exact Or.inr hw
  have hord (v : V) (hv : v∈W.C) : v=y∨v=b∨z=some v:=by
    have hm : v=y∨v=b∨v=zv:=by simpa using hsub hv
    rcases hm with rfl|rfl|rfl <;> simp [hz]
  simp [(qy0 W (qk8 W hord)).1] at hf
private theorem qw0 (W : Wc0 G x y z) {b c : V}
    (hbC : b∈W.C) (hby : b≠y) (hbc : G.Adj b c) (hbflat : W.isFlat≠some b)
    (he : (G.neighborFinset b∩W.core.verts).card=W.core.ell+1)
    (hc2 : (G.neighborFinset c∩W.C).card < 3) : W.isFlat≠some c:=by
  classical
  intro hc
  obtain ⟨hf,_⟩:=qac2 W hc
  rcases hf.2.2.2.2 with ⟨_,s,hs,hS⟩|⟨_,hS⟩
  · have:=qap2 W hc hs hS
    omega
  have hcB : c∈W.base.verts:=W.base.T_subset_verts hf.2.1
  have hbB : b∉W.base.verts:=by
    intro hb
    apply qa1 W hbC
    rcases Cc0.mem_verts.mp hb with rfl|hb|hb
    · exact W.core.x_mem_verts
    · exact W.core.S_subset_verts (hS.symm ▸ hb)
    · exact W.core.T_subset_verts (hf.2.2.2.1.symm ▸
        Finset.mem_erase.mpr ⟨fun e=>hbflat (e ▸ hc),hb⟩)
  have hh:=(ql7 W.hopt.1 hbB hby).1
  have hsub : insert c (G.neighborFinset b∩W.core.verts)⊆G.neighborFinset b∩W.base.verts :=
    Finset.insert_subset (mem_neighbors_in.mpr ⟨hbc,hcB⟩)
      (fun _ h=>Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp h).1,hf.verts_subset (Finset.mem_inter.mp h).2⟩)
  have hcard:=Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (fun h=>hf.t₀_notMem (Finset.mem_inter.mp h).2),he] at hcard
  rw [W.base.ell_t3 hf.1,← hS,← W.core.ell_t3 hf.2.2.1] at hh
  omega
end Fa
open Fa in
theorem qh2 (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q)
    (W : Wc0 G x y z) {b zv : V} (hz : z=some zv) (hzC : zv∈W.C)
    (hzy : zv≠y) (hbC : b∈W.C) (hby : b≠y)
    (hleaf : G.neighborFinset zv∩W.C={b}) (hb2 : (G.neighborFinset b∩W.C).card=2) :
    W.core.ell=q - 2 ∧
    (G.neighborFinset b∩W.core.verts).card=W.core.ell+1 ∧
    (∃ t∈W.core.T,G.Adj b t)∧(∃ s∈W.core.S,G.Adj zv s) ∧
    (∀ t∈W.core.T,¬ G.Adj zv t) ∧
    ∃ c∈W.C,c≠zv∧G.neighborFinset b∩W.C={zv,c} ∧
      (∀ t∈W.core.T,¬ G.Adj c t)∧(c≠y→ 3≤ (G.neighborFinset c∩W.C).card):=by
  classical
  have h3:=qb6 ih hHyp hq4 hfail
  obtain ⟨c,hcC,n,hbz,hbc,hcz,hpair,hP⟩:=qap1 W hbC hzC hby hzy hleaf hb2
  have hbflat:=qr9 W hz hzy hleaf hpair
  have hbx:=qab6 W hbC
  have hd:=hHyp.2.2.2 b hbx hby fun h=>hbz.ne (Option.some.inj (h.symm.trans hz))
  have hs:=qj4 W hbC
  rw [hb2] at hs
  obtain ⟨hbnd,heq⟩:=W.h_ext_deg b (qa1 W hbC) hby hbflat
  have hPC:=hP.mono ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
  have hB:=hP.cons hbc (Finset.notMem_erase _ _)
  have hBC:=hB.mono (Finset.insert_subset hbC ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _)))
  have hZC:=((hB.cons hbz.symm (by simp [hbz.ne.symm])).mono
    (Finset.insert_subset hzC (Finset.insert_subset hbC
      ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))))).len (by omega : n+1+1=n+2)
  have htb' : ∃ t∈W.core.T,G.Adj b t:=by
    by_contra hT
    have hle:=W.h_ell_le hfail
    have hlt : (G.neighborFinset b∩W.core.verts).card < W.core.ell+1 :=
      lt_of_le_of_ne hbnd (fun e=>hT (heq e))
    have hno (v : V) (hv : v∈W.C) (t : V) (ht : t∈W.core.T) : ¬ G.Adj v t :=
      fun h=>by have:=W.h_ell_le_tight hfail (Or.inr ⟨v,hv,t,ht,h⟩);omega
    obtain ⟨sz,hsz,hzs⟩:=qy9 ih hHyp hq4 hfail W hz hzC hzy hleaf (hno zv hzC)
    obtain ⟨s,hs,hbs⟩ : ∃ s∈W.core.S,G.Adj b s:=by
      by_contra hn
      have hc:=Finset.card_le_card (s:=G.neighborFinset b∩W.core.verts) (t:={x})
        (fun v hv=>by
          obtain ⟨hv,hvH⟩:=Finset.mem_inter.mp hv
          have ha:=(mem_neighborFinset _ _ _).mp hv
          exact Finset.mem_singleton.mpr ((Cc0.mem_verts.mp hvH).resolve_right fun h =>
            h.elim (fun h=>hn ⟨v,h,ha⟩) (fun h=>hno b hbC v h ha)))
      simp at hc
      omega
    apply hfail (qc0 (by omega : q≤ W.core.ell+2 - 1) ?_)
    apply qal6 W (b:=n+2) (e:=1) (by omega) (by omega) (Or.inl rfl)
    intro j
    rcases qa8 j with rfl|rfl
    · exact ⟨s,hs,(hBC.cons hbs.symm (fun h=>qa1 W h (W.core.S_subset_verts hs))).len
        (by simp)⟩
    · exact ⟨sz,hsz,(hZC.cons hzs.symm (fun h=>qa1 W h (W.core.S_subset_verts hsz))).len
        (by simp)⟩
  obtain ⟨tb,htb,hbt⟩:=htb'
  have htight:=W.h_ell_le_tight hfail (Or.inr ⟨b,hbC,tb,htb,hbt⟩)
  have hell : W.core.ell=q - 2:=by omega
  have he : (G.neighborFinset b∩W.core.verts).card=W.core.ell+1:=by omega
  have htout (t : V) (ht : t∈W.core.T) : t∉W.C :=
    fun h=>qa1 W h (W.core.T_subset_verts ht)
  have hTb:=hBC.cons hbt.symm (htout tb htb)
  have hnz (t : V) (ht : t∈W.core.T) (hzt : G.Adj zv t) : False:=by
    apply hfail (qc0 (by omega : q≤ W.core.ell+1+2 - 1) ?_)
    apply qag4 W (b:=n+2) (e:=1) (by omega) (by omega) (Or.inl rfl)
    intro j
    rcases qa8 j with rfl|rfl
    · exact ⟨tb,htb,hTb.len (by simp)⟩
    · exact ⟨t,ht,(hZC.cons hzt.symm (htout t ht)).len (by simp)⟩
  have hnc (t : V) (ht : t∈W.core.T) (hct : G.Adj c t) : False:=by
    apply hfail (qc0 (by omega : q≤ W.core.ell+1+2 - 1) ?_)
    apply qag4 W (b:=n+1) (e:=1) (by omega) (by omega) (Or.inl rfl)
    intro j
    rcases qa8 j with rfl|rfl
    · exact ⟨t,ht,(hPC.cons hct.symm (htout t ht)).len (by simp)⟩
    · exact ⟨tb,htb,hTb.len (by simp)⟩
  refine ⟨hell,he,⟨tb,htb,hbt⟩,qy9 ih hHyp hq4 hfail W hz hzC hzy hleaf hnz,
    hnz,c,hcC,hcz,hpair,hnc,fun hcy=>?_⟩
  by_contra hc2
  have hcf:=qw0 W hbC hby hbc hbflat he (by omega)
  obtain ⟨hcbd,hce⟩:=W.h_ext_deg c (qa1 W hcC) hcy hcf
  have hcne : (G.neighborFinset c∩W.core.verts).card≠W.core.ell+1 :=
    fun e=>(hce e).elim fun t ⟨ht,hct⟩=>hnc t ht hct
  have hcz' : z≠some c:=fun e=>hcz (Option.some.inj (e.symm.trans hz))
  have hcx:=qab6 W hcC
  have:=hHyp.2.2.2 c hcx hcy hcz'
  have:=qj4 W hcC
  omega
namespace Fa
private theorem qal9 (hHyp : Ch0 G x y z q) (hfail : ¬ Adm0 G x y q)
    (hq : 2≤ q) (W : Wc0 G x y z) {b : V} (hby : b≠y) (hbz : z≠some b)
    (hbC : b∈W.C) (hsub : W.C⊆{y,b}) : False:=by
  classical
  have hflat:=(qy0 W (qk8 W fun v hv=>by simpa using
    (Or.imp_right Or.inl (show v=y∨v=b by simpa using hsub hv) :
      v=y∨v=b∨z=some v))).1
  have hext:=W.h_ext_deg b (qa1 W hbC) hby (by simp [hflat])
  have hle:=W.h_ell_le hfail
  have hc : (G.neighborFinset b∩W.C).card≤ 1:=by
    simpa using (Finset.card_le_card (t:={y}) fun v hv=>by
      obtain ⟨hv,hvC⟩:=Finset.mem_inter.mp hv
      have hm : v=y∨v=b:=by simpa using hsub hvC
      exact Finset.mem_singleton.mpr (hm.resolve_right (mem_neighborFinset G b v |>.mp hv |>.ne.symm)))
  have hd:=hHyp.2.2.2 b (qab6 W hbC) hby hbz
  have hs:=qj4 W hbC
  obtain ⟨t,ht,hbt⟩:=hext.2 (by have:=hext.1;omega)
  have:=W.h_ell_le_tight hfail (Or.inr ⟨b,hbC,t,ht,hbt⟩)
  have:=hext.1
  omega
private theorem qaa5 (W : Wc0 G x y z) {b zv : V}
    (he : W.C={y,b,zv}) (hby : b≠y) (hzy : zv≠y) (hbz : b≠zv)
    (hyz : ¬ G.Adj y zv) :
    G.Adj b y∧G.Adj b zv ∧
      G.neighborFinset zv∩W.C={b}∧G.neighborFinset b∩W.C={zv,y}:=by
  have hbC : b∈W.C:=by simp [he]
  have hzC : zv∈W.C:=by simp [he]
  obtain ⟨u,huC,hyu⟩:=Cb.adj_of_linked (linked W) (qc2 W) hbC hby
  have hby' : G.Adj b y:=by
    have hu : u=y∨u=b∨u=zv:=by simpa [he] using huC
    rcases hu with rfl|rfl|rfl
    · exact (hyu.ne rfl).elim
    · exact hyu.symm
    · exact (hyz hyu).elim
  obtain ⟨u,huC,hzu⟩:=Cb.adj_of_linked (linked W) hzC hbC hbz
  have hbz' : G.Adj b zv:=by
    have hu : u=y∨u=b∨u=zv:=by simpa [he] using huC
    rcases hu with rfl|rfl|rfl
    · exact (hyz hzu.symm).elim
    · exact hzu.symm
    · exact (hzu.ne rfl).elim
  refine ⟨hby',hbz',?_,?_⟩ <;> ext v <;>
    simp only [he,Finset.mem_inter,mem_neighborFinset,Finset.mem_insert,Finset.mem_singleton]
  · constructor
    · rintro ⟨h,(rfl|rfl|rfl)⟩
      · exact (hyz h.symm).elim
      · rfl
      · exact (h.ne rfl).elim
    · rintro rfl
      exact ⟨hbz'.symm,Or.inr (Or.inl rfl)⟩
  · constructor
    · rintro ⟨h,(rfl|rfl|rfl)⟩ <;> simp_all
    · rintro (rfl|rfl) <;> simp_all
private theorem qaa2 (W : Wc0 G x y z)
    (hfail : ¬ Adm0 G x y q) (hk : W.core.kind=.t2) (hell : W.core.ell=q - 2)
    {b zv t s : V} (hbC : b∈W.C) (hzC : zv∈W.C)
    (ht : t∈W.core.T) (hs : s∈W.core.S)
    (hbt : G.Adj b t) (hzs : G.Adj zv s) (hbz : G.Adj b zv) (hby : G.Adj b y)
    (hzy : zv≠y) : False:=by
  have h3 : 2≤ W.core.ell:=by rw [W.core.ell_t2 hk];exact W.core.two_le_T
  have hB:=qa1 W hbC
  have hZ:=qa1 W hzC
  have hy:=W.core.y_notMem_verts
  have hQ:=qh8 W.core hk hs (W.core.ell+2)
    (Finset.mem_insert_of_mem (Finset.mem_Icc.mpr ⟨by omega,le_rfl⟩))
  have hQ':=((hQ.concat hzs.symm hZ).concat hbz.symm (by simp [hbz.ne,hB])).concat hby
    (by simp [hby.ne.symm,hzy.symm,hy])
  refine hfail ⟨4,1,by omega,Or.inl rfl,fun i=>?_⟩
  have hi:=i.isLt
  by_cases h : i.val≤ W.core.ell
  · have hp:=ql6 W.core hk ht (2+i.val) (Finset.mem_Icc.mpr ⟨by omega,by omega⟩)
    obtain ⟨P,hP,hl,_⟩:=(hp.concat hbt.symm hB).concat hby (by simp [hby.ne.symm,hy])
    exact ⟨P,hP,by omega⟩
  · obtain ⟨P,hP,hl,_⟩:=hQ'
    exact ⟨P,hP,by omega⟩
end Fa
open Fa in
theorem qg0 (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q)
    (W : Wc0 G x y z) : ¬ ∃ b zv,z=some zv∧W.C={y,b,zv}:=by
  classical
  rintro ⟨b,zv,hz,he⟩
  obtain ⟨w,hw,hwy,hwz⟩:=W.hC_nontriv
  have hw' : w=y∨w=b∨w=zv:=by simpa [he] using hw
  have hwb:=(hw'.resolve_left hwy).resolve_right (fun e=>hwz (e ▸ hz))
  subst w
  have hbz : b≠zv:=fun e=>hwz (e ▸ hz)
  by_cases hzy : zv=y
  · apply qal9 hHyp hfail (Nat.le_of_succ_le (qb6 ih hHyp hq4 hfail)) W hwy hwz hw
    intro v hv
    simpa [he,hzy,or_comm] using hv
  have hzC : zv∈W.C:=by simp [he]
  have hzx:=qab6 W hzC
  have hyz:=qd5 ih hHyp hq4 hfail zv hz hzx hzy
  obtain ⟨hby,hbz',hleaf,hpair⟩:=qaa5 W he hwy hzy hbz hyz
  obtain ⟨hell,_,⟨t,ht,hbt⟩,⟨s,hs,hzs⟩,hnz,c,_,hcz,hc,hnc,_⟩ :=
    qh2 ih hHyp hq4 hfail W hz hzC hzy hw hwy hleaf
      (by rw [hpair,Finset.card_pair hzy])
  have hcy : c=y:=by
    have hm : c∈({zv,y} : Finset V):=hpair ▸ hc.symm ▸ Finset.mem_insert_of_mem
      (Finset.mem_singleton_self c)
    simpa [hcz] using hm
  subst c
  have hk : W.core.kind=.t3:=by
    cases hk : W.core.kind
    · rw [(W.core.shape1 hk).1] at hs
      exact (Finset.notMem_empty _ hs).elim
    · exact (qaa2 W hfail hk hell hw hzC ht hs hbt hzs hbz' hby hzy).elim
    · rfl
  have hord : ∀ v∈W.C,v=y∨v=b∨z=some v:=by
    intro v hv
    have hm : v=y∨v=b∨v=zv:=by simpa [he] using hv
    rcases hm with rfl|rfl|rfl <;> simp [hz]
  have hcore:=(qy0 W (qk8 W hord)).2
  have hopt : Ioc0 G x y z W.core:=hcore.symm ▸ W.hopt
  have hxy:=qb3 ih hHyp hq4 hfail
  obtain ⟨H⟩:=qu3 W.hK W.core.x_ne_y.symm (fun h=>hxy h.symm)
  have hr:=hopt.2.1 H
  have hr' : H.kind.rank=W.core.kind.rank:=by
    rw [hk] at hr ⊢
    cases hk' : H.kind <;> simp [hk',Ck0.rank] at hr ⊢
  obtain ⟨hdeg,hdist⟩:=hopt.2.2 H hr'
  have hNy : G.neighborFinset y⊆insert b W.core.S:=by
    intro v hv
    have hyv:=(mem_neighborFinset _ _ _).mp hv
    rcases qh9 W (qc2 W) hyv with hC|hH
    · rcases hord v hC with rfl|rfl|hvz
      · exact (hyv.ne rfl).elim
      · exact Finset.mem_insert_self _ _
      · exact (hyz (Option.some.inj (hvz.symm.trans hz) ▸ hyv)).elim
    · rcases Cc0.mem_verts.mp hH with rfl|hs|ht
      · exact (hxy hyv.symm).elim
      · exact Finset.mem_insert_of_mem hs
      · exact (hnc v ht hyv).elim
  have hTy : G.degree y≤ W.core.ell+1:=by
    have h:=Finset.card_le_card hNy
    rw [card_neighborFinset_eq_degree,Finset.card_insert_of_notMem
      (fun h=>qa1 W hw (W.core.S_subset_verts h)),← W.core.ell_t3 hk] at h
    omega
  have hTx : W.core.T⊆G.neighborFinset x:=fun t ht =>
    (mem_neighborFinset _ _ _).mpr ((W.core.shape3 hk).2.2.1 t ht)
  have hcard:=Finset.card_le_card hTx
  rw [card_neighborFinset_eq_degree] at hcard
  have hCT:=(W.core.shape3 hk).1
  rw [← W.core.ell_t3 hk] at hCT
  have hNx:=Finset.eq_of_subset_of_card_le hTx (by rw [card_neighborFinset_eq_degree];omega)
  have hd:=hdist (by omega) zv hz
  have hdy:=G.dist_le (Walk.cons hby.symm (Walk.cons hbz' Walk.nil))
  have hdx : G.dist x zv≤ 2:=by simpa using hd.trans hdy
  have hxz:=qf3 ih hHyp hq4 hfail zv hz hzx hzy
  have hconn:=qc7 W.hK
  have hpos:=hconn.one_lt_dist_of_ne_of_not_adj hzx.symm hxz
  obtain ⟨P,hP⟩:=hconn.exists_walk_length_eq_dist x zv
  have hlen : P.length=2:=by omega
  cases P with
  | nil=>simp at hlen
  | cons h P =>
    cases P with
    | nil=>simp at hlen
    | cons h' P =>
      have hnil : P.length=0:=by simpa using hlen
      cases P with
      | nil=>exact hnz _ (hNx ▸ (mem_neighborFinset _ _ _).mpr h) h'.symm
      | cons _ _=>simp at hnil
open Fa in
theorem qn3 (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q)
    (W : Wc0 G x y z) : 2≤ (W.C.filter (fun v=>v≠y∧z≠some v)).card:=by
  classical
  by_contra h
  obtain ⟨b,hb,hby,hbz⟩:=W.hC_nontriv
  have huniq (v : V) (hv : v∈W.C) : v=y∨v=b∨z=some v:=by
    by_contra! hn
    have h2 : 1 < (W.C.filter (fun v=>v≠y∧z≠some v)).card :=
      Finset.one_lt_card.mpr ⟨v,Finset.mem_filter.mpr ⟨hv,hn.1,hn.2.2⟩,
      b,Finset.mem_filter.mpr ⟨hb,hby,hbz⟩,hn.2.1⟩
    omega
  by_cases hz : ∃ zv∈W.C,z=some zv
  · obtain ⟨zv,hzC,hz⟩:=hz
    apply qg0 ih hHyp hq4 hfail W
    refine ⟨b,zv,hz,Finset.Subset.antisymm (fun v hv=>?_)
      (Finset.insert_subset (qc2 W) (Finset.insert_subset hb (Finset.singleton_subset_iff.mpr hzC)))⟩
    rcases huniq v hv with rfl|rfl|e
    · simp
    · simp
    · simp [Option.some.inj (e.symm.trans hz)]
  · apply qal9 hHyp hfail (Nat.le_of_succ_le (qb6 ih hHyp hq4 hfail)) W hby hbz hb
    intro v hv
    simpa using (huniq v hv).imp_right (fun h=>h.resolve_right (fun e=>hz ⟨v,hv,e⟩))
end DeanK5
end M11
section M12
namespace DeanK5
open SimpleGraph
variable {V : Type} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
  {x y : V} {z : Option V} {q : ℕ}
def Ici0 (G : SimpleGraph V) (C : Finset V) (v : V) : Prop :=
  v∈C∧¬ Lk0 G (C.erase v)
structure Ibo0 (G : SimpleGraph V) (C B : Finset V) : Prop where
  subset : B⊆C
  card : 2≤ B.card
  linked : Lk0 G B
  erase_linked : ∀ v∈B,Lk0 G (B.erase v)
  separates : ∀ v∈C,v∉B→ ∃ c∈B,∀ w∈B,¬ Rc0 G (C.erase c) v w
def Bb0 (G : SimpleGraph V) (C B : Finset V) (v : V) : Prop :=
  ∃ u∈C,u∉B∧G.Adj v u
structure Fb0 (G : SimpleGraph V) (C : Finset V) (y : V) (z : Option V)
    (B : Finset V) (b : V) : Prop where
  block : Ibo0 G C B
  exit_mem : b∈B
  exit_reach : Rc0 G (C\B.erase b) b y
  exception : ∃ e : Option V,
    (∀ v∈B.erase b,(Ici0 G C v∨v=y∨z=some v)→ e=some v) ∧
      ∃ v∈B.erase b,e≠some v
omit [Fintype V] [DecidableRel G.Adj] in
theorem Ibo0.maximal {A B D : Finset V} (hB : Ibo0 G A B)
    (hBD : B⊆D) (hDA : D⊆A) (hD : ∀ w∈D,Lk0 G (D.erase w)) : D=B:=by
  refine Finset.Subset.antisymm (fun v hv=>?_) hBD
  by_contra hvB
  obtain ⟨c,hc,hsep⟩:=hB.separates v (hDA hv) hvB
  have hcard:=Finset.card_erase_add_one hc
  obtain ⟨u,hu⟩:=Finset.card_pos.mp (show 0 < (B.erase c).card by have:=hB.card;omega)
  have hv' : v∈D.erase c:=Finset.mem_erase.mpr ⟨fun e=>hvB (e ▸ hc),hv⟩
  exact hsep u (Finset.mem_of_mem_erase hu)
    ((hD c (hBD hc) v hv' u (Finset.erase_subset_erase _ hBD hu)).mono (Finset.erase_subset_erase _ hDA))
namespace Fb
open Cb Fa
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qe5 {A : Finset V} {u v : V} (h : Rc0 G A u v) :
    ∃ n,Pi0 G A u v n:=by
  obtain ⟨p,hp⟩:=h
  exact ⟨_,p.bypass,p.bypass_isPath,rfl,fun w hw=>hp w (p.support_bypass_subset_support hw)⟩
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem qi4 {A : Finset V} {u v : V} (h : Rc0 G A u v) (hne : u≠v) :
    ∃ a∈A,G.Adj u a:=by
  obtain ⟨p,hp⟩:=h
  cases p with
  | nil=>exact (hne rfl).elim
  | cons had p=>exact ⟨_,hp _ (by simp),had⟩
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qi5 {A B : Finset V} {u v : V} (h : Rc0 G A u v) (hv : v∈B) :
    ∃ a∈B,Rc0 G (A\B.erase a) u a:=by
  obtain ⟨p,hp⟩:=h
  obtain ⟨a,ha,r,hrs,hr,-⟩:=qe9 (·∈B) p hv
  exact ⟨a,ha,r,fun t ht=>Finset.mem_sdiff.mpr
    ⟨hp t (hrs t ht),fun h=>(Finset.ne_of_mem_erase h) (hr t ht (Finset.mem_of_mem_erase h))⟩⟩
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qr1 {A P : Finset V} {w u v : V}
    (_ : P⊆A.erase w) (hcl : ∀ c∈P,∀ d∈A.erase w,G.Adj c d→ d∈P)
    (hu : u∈P) (hv : v∉P) (r : Rc0 G (A.erase w) u v) : False:=by
  obtain ⟨p,hp⟩:=r
  exact hv (qb9 (D:=fun d=>d∉A.erase w)
    (fun c hc d h=>or_iff_not_imp_right.mpr fun hn=>hcl c hc d (not_not.mp hn) h)
    p hu (fun a ha h=>h (hp a ha)) v p.end_mem_support)
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qaj9 {A P : Finset V} {w : V} (hA : Lk0 G A) (hw : w∈A)
    (hP : P⊆A.erase w) (hne : P.Nonempty)
    (hcl : ∀ c∈P,∀ d∈A.erase w,G.Adj c d→ d∈P) (hl : Lk0 G P) :
    Lk0 G (insert w P):=by
  obtain ⟨v,hv⟩:=hne
  obtain ⟨c,hc,r⟩:=qi5 (hA w hw v (Finset.mem_of_mem_erase (hP hv))) hv
  obtain ⟨a,ha,had⟩:=qi4 r.symm (Finset.ne_of_mem_erase (hP hc))
  have haw : a=w:=by
    by_contra h
    exact (Finset.mem_sdiff.mp ha).2 (Finset.mem_erase.mpr ⟨had.ne.symm,
      hcl c hc a (Finset.mem_erase.mpr ⟨h,(Finset.mem_sdiff.mp ha).1⟩) had⟩)
  subst a
  have hcw : Rc0 G (insert w P) w c :=
    Rc0.adj (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hc) had.symm
  refine qa4 w fun a ha=>?_
  rcases Finset.mem_insert.mp ha with rfl|ha
  · exact Rc0.refl (Finset.mem_insert_self _ _)
  · exact hcw.trans ((hl c hc a ha).mono (Finset.subset_insert _ _))
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qah8 {A P B : Finset V} {w : V} (hw : w∈A)
    (hP : P⊆A.erase w) (hcl : ∀ c∈P,∀ d∈A.erase w,G.Adj c d→ d∈P)
    (hB : Ibo0 G (insert w P) B) : Ibo0 G A B:=by
  classical
  have hsub : insert w P⊆A:=Finset.insert_subset_iff.mpr
    ⟨hw,hP.trans (Finset.erase_subset _ _)⟩
  refine ⟨hB.subset.trans hsub,hB.card,hB.linked,hB.erase_linked,?_⟩
  intro v hv hvB
  let f : V→ V:=fun a=>if a∈P then a else w
  have hfix (a : V) (ha : a∈insert w P) : f a=a:=by
    rcases Finset.mem_insert.mp ha with rfl|ha
    · simp [f]
    · simp [f,ha]
  by_cases hgate : w∈B∧v∉P
  · refine ⟨w,hgate.1,fun a ha r=>?_⟩
    have haP:=(Finset.mem_insert.mp (hB.subset ha)).resolve_left (Finset.ne_of_mem_erase r.right_mem)
    exact qr1 hP hcl haP hgate.2 r.symm
  have hfB : f v∉B:=by
    by_cases hvP : v∈P
    · simpa [f,hvP] using hvB
    · simpa [f,hvP] using fun hwB=>hgate ⟨hwB,hvP⟩
  have hgoal (c : V) (hc : c∈B)
      (hs : ∀ a∈B,¬ Rc0 G ((insert w P).erase c) (f v) a) :
      ∀ a∈B,¬ Rc0 G (A.erase c) v a:=by
    intro a ha r
    by_cases hcw : c=w
    · subst w
      have haP:=(Finset.mem_insert.mp (hB.subset ha)).resolve_left (Finset.ne_of_mem_erase r.right_mem)
      obtain ⟨p,hp⟩:=r.symm
      have hstay:=qb9 (D:=fun d=>d∉A.erase c)
        (fun d hd e he=>or_iff_not_imp_right.mpr fun hn=>hcl d hd e (not_not.mp hn) he)
        p haP (fun d hd hn=>hn (hp d hd))
      have hvP:=hstay _ p.end_mem_support
      apply hs a ha
      simp only [f,if_pos hvP]
      exact Rc0.symm ⟨p,fun d hd=>Finset.mem_erase.mpr
        ⟨Finset.ne_of_mem_erase (hp d hd),Finset.mem_insert_of_mem (hstay d hd)⟩⟩
    · have hproj:=r.proj (H:=G) (t:=(insert w P).erase c) f
        (fun d hd e he hed=>by
          have hadj : ∀ i∈P,∀ j∈A,j∉P→ G.Adj i j→ j=w :=
            fun i hi j hj hjP hij=>by
              by_contra hjw
              exact hjP (hcl i hi j (Finset.mem_erase.mpr ⟨hjw,hj⟩) hij)
          by_cases hdP : d∈P <;> by_cases heP : e∈P
          · exact Or.inr (by simpa [f,hdP,heP] using hed)
          · simpa [f,hdP,heP,hadj d hdP e (Finset.mem_of_mem_erase he) heP hed] using
              (Or.inr hed : d=e∨G.Adj d e)
          · simpa [f,hdP,heP,hadj e heP d (Finset.mem_of_mem_erase hd) hdP hed.symm] using
              (Or.inr hed : d=e∨G.Adj d e)
          · exact Or.inl (by simp [f,hdP,heP]))
        (fun d hd=>by
          by_cases hdP : d∈P
          · change (if d∈P then d else w)∈(insert w P).erase c
            rw [if_pos hdP]
            exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hd,Finset.mem_insert.mpr (Or.inr hdP)⟩
          · change (if d∈P then d else w)∈(insert w P).erase c
            rw [if_neg hdP]
            exact Finset.mem_erase.mpr ⟨Ne.symm hcw,Finset.mem_insert_self w P⟩)
      exact hs a ha (hfix a (hB.subset ha) ▸ hproj)
  have hfv : f v∈insert w P:=by by_cases h : v∈P <;> simp [f,h]
  obtain ⟨c,hc,hs⟩:=hB.separates (f v) hfv hfB
  exact ⟨c,hc,hgoal c hc hs⟩
private def qm3 (G : SimpleGraph V) (A M : Finset V) : Prop :=
  ∃ B,Ibo0 G A B∧∃ E : Finset V,E⊆B∧E.card≤ 2∧(B\E).Nonempty ∧
    ∀ v∈B,(v∈M∨Bb0 G A B v)→ v∈E
private def Side (G : SimpleGraph V) (A : Finset V) (w : V) (P : Finset V) : Prop :=
  P⊆A.erase w∧P.Nonempty∧Lk0 G P ∧
    ∀ c∈P,∀ d∈A.erase w,G.Adj c d→ d∈P
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qag6 {A : Finset V} {w v : V} (hv : v∈A.erase w) :
    ∃ P,v∈P∧Side G A w P:=by
  obtain ⟨P,hP,hvP,hcl,hreach⟩:=qg2 (G:=G) _ hv
  refine ⟨P,hvP,hP,⟨v,hvP⟩,fun a ha b hb=>?_,hcl⟩
  have hin (u : V) (hu : u∈P) : Rc0 G P v u:=by
    obtain ⟨p,hp⟩:=hreach u hu
    exact ⟨p,qb9 (D:=fun d=>d∉A.erase w)
      (fun c hc d h=>or_iff_not_imp_right.mpr fun hn=>hcl c hc d (not_not.mp hn) h)
      p hvP (fun d hd hn=>hn (hp d hd))⟩
  exact (hin a ha).symm.trans (hin b hb)
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qo3 {A P Q : Finset V} {w : V}
    (hP : Side G A w P) (hQ : Side G A w Q) (h : P≠Q) : Disjoint P Q:=by
  refine Finset.disjoint_left.mpr fun a ha hqa=>h (Finset.Subset.antisymm ?_ ?_)
  · intro b hb
    by_contra hqb
    exact qr1 hQ.1 hQ.2.2.2 hqa hqb ((hP.2.2.1 a ha b hb).mono hP.1)
  · intro b hb
    by_contra hpb
    exact qr1 hP.1 hP.2.2.2 ha hpb ((hQ.2.2.1 a hqa b hb).mono hQ.1)
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qak4 {A M P : Finset V} {w : V} (hw : w∈A)
    (hP : Side G A w P) (h : qm3 G (insert w P) (insert w (M∩P))) :
    qm3 G A M:=by
  obtain ⟨B,hB,E,hEB,hc,hne,hE⟩:=h
  refine ⟨B,qah8 hw hP.1 hP.2.2.2 hB,E,hEB,hc,hne,fun v hv hm=>?_⟩
  apply hE v hv
  rcases Finset.mem_insert.mp (hB.subset hv) with rfl|hvP
  · exact Or.inl (Finset.mem_insert_self _ _)
  rcases hm with hm|⟨u,hu,huB,had⟩
  · exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_inter.mpr ⟨hm,hvP⟩))
  · refine Or.inr ⟨u,?_,huB,had⟩
    by_cases huw : u=w
    · exact huw ▸ Finset.mem_insert_self _ _
    · exact Finset.mem_insert_of_mem (hP.2.2.2 v hvP u (Finset.mem_erase.mpr ⟨huw,hu⟩) had)
private theorem qs3 {A P : Finset V} {w v : V} (hP : Side G A w P)
    (hw : w∈A) (hv : v∈P) :
    G.neighborFinset v∩A=G.neighborFinset v∩insert w P:=by
  ext a
  simp only [mem_neighbors_in,Finset.mem_insert]
  refine and_congr_right fun ha=>⟨fun haA=>?_,fun h=>h.elim (· ▸ hw) fun h =>
    Finset.mem_of_mem_erase (hP.1 h)⟩
  by_cases haw : a=w
  · exact Or.inl haw
  · exact Or.inr (hP.2.2.2 v hv a (Finset.mem_erase.mpr ⟨haw,haA⟩) ha)
private theorem qy5 (A M : Finset V) (hM : M⊆A) (hm : M.card≤ 2)
    (hc : 2≤ A.card) (hl : Lk0 G A) (hn : ¬ qm3 G A M) :
    M.card=2∧∀ v∈A,(G.neighborFinset v∩A).card=if v∈M then 1 else 2:=by
  classical
  induction A using Finset.strongInduction generalizing M with
  | H A ih =>
    by_cases hcut : ∃ w∈A,¬ Lk0 G (A.erase w)
    · obtain ⟨w,hw,hb⟩:=hcut
      obtain ⟨R,hR,⟨u,hu⟩,⟨v,hv,hvR⟩,hRcl⟩:=qg6 hb
      obtain ⟨P,huP,hP⟩:=qag6 (hR hu)
      obtain ⟨Q,hvQ,hQ⟩:=qag6 hv
      have hPQ : P≠Q:=by
        rintro rfl
        exact qr1 hR hRcl hu hvR ((hP.2.2.1 u huP v hvQ).mono hP.1)
      have hdis:=qo3 hP hQ hPQ
      have proper (D : Finset V) (hD : Side G A w D) (e : ∃ a∈A.erase w,a∉D) :
          insert w D ⊂ A:=by
        have hsub:=Finset.insert_subset_iff.mpr ⟨hw,hD.1.trans (Finset.erase_subset _ _)⟩
        obtain ⟨a,ha,haD⟩:=e
        exact (Finset.ssubset_iff_of_subset hsub).mpr ⟨a,Finset.mem_of_mem_erase ha,
          fun h=>(Finset.mem_insert.mp h).elim (Finset.ne_of_mem_erase ha) haD⟩
      have recSide (D : Finset V) (hD : Side G A w D) (hD' : insert w D ⊂ A)
          (hDc : (M∩D).card≤ 1) :
          (M∩D).card=1∧∀ a∈insert w D,
            (G.neighborFinset a∩insert w D).card=if a∈insert w (M∩D) then 1 else 2:=by
        have hcn : (insert w (M∩D)).card=(M∩D).card+1 :=
          Finset.card_insert_of_notMem fun hwD =>
            Finset.notMem_erase w _ (hD.1 (Finset.mem_inter.mp hwD).2)
        have hcard : (insert w D).card=D.card+1 :=
          Finset.card_insert_of_notMem fun hwD=>Finset.notMem_erase w _ (hD.1 hwD)
        have hp:=hD.2.1.card_pos
        obtain ⟨hc',hdegs⟩:=ih (insert w D) hD' (insert w (M∩D))
          (Finset.insert_subset_insert w Finset.inter_subset_right) (by omega) (by omega)
          (qaj9 hl hw hD.1 hD.2.1 hD.2.2.2 hD.2.2.1)
          (fun h=>hn (qak4 hw hD h))
        exact ⟨by omega,hdegs⟩
      have hP':=proper P hP ⟨v,hv,Finset.disjoint_right.mp hdis hvQ⟩
      have hQ':=proper Q hQ ⟨u,hR hu,Finset.disjoint_left.mp hdis huP⟩
      have hsum : (M∩P).card+(M∩Q).card≤ M.card:=by
        rw [← Finset.card_union_of_disjoint (Disjoint.mono Finset.inter_subset_right
          Finset.inter_subset_right hdis)]
        exact Finset.card_le_card (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
      have hpc : (M∩P).card≤ 1:=by
        by_contra h
        have hh:=(recSide Q hQ hQ' (by omega)).1
        omega
      have hqc : (M∩Q).card≤ 1:=by
        by_contra h
        have hh:=(recSide P hP hP' (by omega)).1
        omega
      obtain ⟨hpm,hpd⟩:=recSide P hP hP' hpc
      obtain ⟨hqm,hqd⟩:=recSide Q hQ hQ' hqc
      have hmcover : (M∩P)∪(M∩Q)=M:=by
        apply Finset.eq_of_subset_of_card_le
          (Finset.union_subset Finset.inter_subset_left Finset.inter_subset_left)
        rw [Finset.card_union_of_disjoint (Disjoint.mono Finset.inter_subset_right
          Finset.inter_subset_right hdis)]
        omega
      have hcover : ∀ a∈A.erase w,a∈P∨a∈Q:=by
        intro a ha
        by_contra h
        obtain ⟨D,haD,hD⟩:=qag6 ha
        have hdp : D≠P:=fun e=>h (Or.inl (e ▸ haD))
        have hdq : D≠Q:=fun e=>h (Or.inr (e ▸ haD))
        have hdP:=qo3 hD hP hdp
        have hdQ:=qo3 hD hQ hdq
        have he : M∩D=∅:=by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro c hc
          obtain ⟨hcm,hcD⟩:=Finset.mem_inter.mp hc
          rcases Finset.mem_union.mp (hmcover.symm ▸ hcm) with hcp|hcq
          · exact Finset.disjoint_left.mp hdP hcD (Finset.mem_inter.mp hcp).2
          · exact Finset.disjoint_left.mp hdQ hcD (Finset.mem_inter.mp hcq).2
        have hd:=(recSide D hD (proper D hD ⟨u,hR hu,Finset.disjoint_right.mp hdP huP⟩)
          (by simp [he])).1
        simp [he] at hd
      have hwn : w∉M:=by
        rw [← hmcover]
        simp [show w∉P from fun h=>Finset.notMem_erase _ _ (hP.1 h),
          show w∉Q from fun h=>Finset.notMem_erase _ _ (hQ.1 h)]
      refine ⟨by omega,fun a ha=>?_⟩
      by_cases haw : a=w
      · subst a
        have hnp : G.neighborFinset w∩insert w P=G.neighborFinset w∩P:=by
          ext c
          simp only [mem_neighbors_in,Finset.mem_insert]
          exact and_congr_right fun hj=>or_iff_right hj.ne.symm
        have hnq : G.neighborFinset w∩insert w Q=G.neighborFinset w∩Q:=by
          ext c
          simp only [mem_neighbors_in,Finset.mem_insert]
          exact and_congr_right fun hj=>or_iff_right hj.ne.symm
        have hu : G.neighborFinset w∩A =
            (G.neighborFinset w∩P)∪(G.neighborFinset w∩Q):=by
          ext c
          simp only [mem_neighbors_in,Finset.mem_union]
          exact ⟨fun ⟨hj,hc⟩=>(hcover c (Finset.mem_erase.mpr ⟨hj.ne.symm,hc⟩)).imp
              (fun h=>⟨hj,h⟩) (fun h=>⟨hj,h⟩),
            fun h=>h.elim (fun ⟨hj,h⟩=>⟨hj,Finset.mem_of_mem_erase (hP.1 h)⟩)
              (fun ⟨hj,h⟩=>⟨hj,Finset.mem_of_mem_erase (hQ.1 h)⟩)⟩
        have h1:=hpd w (Finset.mem_insert_self _ _)
        have h2:=hqd w (Finset.mem_insert_self _ _)
        rw [hnp,if_pos (Finset.mem_insert_self _ _)] at h1
        rw [hnq,if_pos (Finset.mem_insert_self _ _)] at h2
        rw [hu,Finset.card_union_of_disjoint (Disjoint.mono Finset.inter_subset_right
          Finset.inter_subset_right hdis),h1,h2,if_neg hwn]
      · rcases hcover a (Finset.mem_erase.mpr ⟨haw,ha⟩) with hp|hq
        · rw [qs3 hP hw hp,hpd a (Finset.mem_insert_of_mem hp)]
          simp [haw,hp]
        · rw [qs3 hQ hw hq,hqd a (Finset.mem_insert_of_mem hq)]
          simp [haw,hq]
    · have hdel : ∀ w∈A,Lk0 G (A.erase w):=fun w hw=>not_not.mp fun h=>hcut ⟨w,hw,h⟩
      have he : A=M:=by
        apply Finset.Subset.antisymm ?_ hM
        by_contra h
        exact hn ⟨A,⟨subset_rfl,hc,hl,hdel,fun _ hv hv'=>(hv' hv).elim⟩,
          M,hM,hm,Finset.sdiff_nonempty.mpr h,fun v _ hv=>hv.elim id
            (fun ⟨u,hu,hu',_⟩=>(hu' hu).elim)⟩
      have h₂ : A.card=2:=by rw [he] at hc ⊢;omega
      refine ⟨he ▸ h₂,fun a ha=>?_⟩
      obtain ⟨v,hv,hva⟩:=Finset.exists_mem_notMem_of_card_lt_card
        (show ({a} : Finset V).card < A.card by simp [h₂])
      have hne : v≠a:=by simpa using hva
      have hset : A={a,v}:=(Finset.eq_of_subset_of_card_le
        (Finset.insert_subset_iff.mpr ⟨ha,Finset.singleton_subset_iff.mpr hv⟩)
        (by rw [h₂,Finset.card_pair (Ne.symm hne)])).symm
      have hAdj : G.Adj a v:=by
        obtain ⟨c,hc,hadj⟩:=qi4 (hl a ha v hv) (Ne.symm hne)
        have hcv : c=v:=(show c=a∨c=v by simpa [hset] using hc).resolve_left hadj.ne.symm
        exact hcv ▸ hadj
      have hN : G.neighborFinset a∩A={v}:=by
        ext c
        simp [hset,hAdj]
      simp [hN,← he,ha]
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qi8 {A B : Finset V} {u a : V}
    (hr : Rc0 G (A\B.erase a) u a) (hu : u≠a) : Bb0 G A B a:=by
  obtain ⟨d,hd,had⟩:=qi4 hr.symm (Ne.symm hu)
  exact ⟨d,(Finset.mem_sdiff.mp hd).1,fun h=>(Finset.mem_sdiff.mp hd).2
    (Finset.mem_erase.mpr ⟨had.ne.symm,h⟩),had⟩
omit [Fintype V] [DecidableRel G.Adj] in
theorem qa7 {A B : Finset V} {a : V} (hA : Lk0 G A)
    (hB : Ibo0 G A B) (ha : a∈B) : Bb0 G A B a↔Ici0 G A a:=by
  classical
  constructor
  · rintro ⟨v,hv,hvB,hav⟩
    obtain ⟨c,hc,hsep⟩:=hB.separates v hv hvB
    have hca : c=a:=by
      by_contra h
      exact hsep a ha (Rc0.adj (Finset.mem_erase.mpr ⟨fun e=>hvB (e.symm ▸ hc),hv⟩)
        (Finset.mem_erase.mpr ⟨Ne.symm h,hB.subset ha⟩) hav.symm)
    subst c
    refine ⟨hB.subset ha,fun hl=>?_⟩
    have hcard:=Finset.card_erase_add_one ha
    obtain ⟨d,hd⟩:=Finset.card_pos.mp (show 0 < (B.erase a).card by have:=hB.card;omega)
    exact hsep d (Finset.mem_of_mem_erase hd)
      (hl v (Finset.mem_erase.mpr ⟨hav.ne.symm,hv⟩) d
        (Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hd,hB.subset (Finset.mem_of_mem_erase hd)⟩))
  · intro haCut
    by_contra hn
    have hl:=hB.erase_linked a ha
    have hsub : B.erase a⊆A.erase a:=Finset.erase_subset_erase _ hB.subset
    have hcard:=Finset.card_erase_add_one ha
    obtain ⟨d,hd⟩:=Finset.card_pos.mp (show 0 < (B.erase a).card by have:=hB.card;omega)
    apply haCut.2 (qa4 d fun v hv=>?_)
    by_cases hvB : v∈B
    · exact (hl d hd v (Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hv,hvB⟩)).mono hsub
    · obtain ⟨c,hc,hvc⟩:=qi5
        (hA v (Finset.mem_of_mem_erase hv) d (hB.subset (Finset.mem_of_mem_erase hd)))
        (Finset.mem_of_mem_erase hd)
      have hca : c≠a:=fun e=>hn (e ▸ qi8 hvc (fun f=>hvB (f.symm ▸ hc)))
      refine ((hl d hd c (Finset.mem_erase.mpr ⟨hca,hc⟩)).mono hsub).trans (hvc.symm.mono ?_)
      exact fun u hu=>Finset.mem_erase.mpr ⟨fun e=>(Finset.mem_sdiff.mp hu).2
        (e.symm ▸ Finset.mem_erase.mpr ⟨Ne.symm hca,ha⟩),(Finset.mem_sdiff.mp hu).1⟩
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qag8 {A M : Finset V} (hA : Lk0 G A) (hy : y∈A)
    (hM : ∀ v∈A,(v=y∨z=some v)→ v∈M) (hm : qm3 G A M) :
    ∃ B b,Fb0 G A y z B b:=by
  classical
  obtain ⟨B,hB,E,hEB,hEc,hne,hmark⟩:=hm
  obtain ⟨u,hu⟩:=hne
  obtain ⟨b,hb,hr⟩:=qi5
    (hA y hy u (hB.subset (Finset.mem_sdiff.mp hu).1)) (Finset.mem_sdiff.mp hu).1
  have hbE : b∈E:=by
    by_cases hby : b=y
    · exact hmark b hb (Or.inl (hM b (hB.subset hb) (Or.inl hby)))
    · exact hmark b hb (Or.inr (qi8 hr (Ne.symm hby)))
  have hc:=Finset.card_erase_add_one hbE
  have hs : (E.erase b).card≤ 1:=by omega
  have hu' : u∈B.erase b:=Finset.mem_erase.mpr
    ⟨fun e=>(Finset.mem_sdiff.mp hu).2 (e.symm ▸ hbE),(Finset.mem_sdiff.mp hu).1⟩
  refine ⟨B,b,hB,hb,hr.symm,?_⟩
  have hcover (v : V) (hv : v∈B.erase b) (h : Ici0 G A v∨v=y∨z=some v) :
      v∈E.erase b:=Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hv,
    hmark v (Finset.mem_of_mem_erase hv) (h.elim
      (fun h=>Or.inr ((qa7 hA hB (Finset.mem_of_mem_erase hv)).mpr h))
      (fun h=>Or.inl (hM v (hB.subset (Finset.mem_of_mem_erase hv)) h)))⟩
  by_cases h : (E.erase b).Nonempty
  · obtain ⟨v,hv⟩:=h
    refine ⟨some v,fun w hw hm=>congrArg some (Finset.card_le_one.mp hs v hv w (hcover w hw hm)),
      u,hu',fun e=>(Finset.mem_sdiff.mp hu).2 (Option.some.inj e ▸ Finset.mem_of_mem_erase hv)⟩
  · exact ⟨none,fun w hw hm=>(h ⟨w,hcover w hw hm⟩).elim,u,hu',by simp⟩
omit [Fintype V] in
private theorem qan3 (C : Finset V) (y : V) (z : Option V)
    [DecidablePred (fun v=>v=y∨z=some v)] :
    (C.filter (fun v=>v=y∨z=some v)).card≤ 2:=by
  cases z with
  | none =>
    refine (Finset.card_le_card (t:={y}) fun v hv=>?_).trans (by simp)
    simpa using (Finset.mem_filter.mp hv).2
  | some zv =>
    exact (Finset.card_le_card (t:={y,zv}) fun v hv=>by
      have h:=(Finset.mem_filter.mp hv).2
      simpa [Option.some.injEq,eq_comm (a:=zv)] using h).trans (by simpa using Finset.card_insert_le y ({zv} : Finset V))
private theorem qh3 {C : Finset V} {v b : V}
    (hc : (G.neighborFinset v∩C).card=1) (hb : b∈C) (h : G.Adj v b) :
    G.neighborFinset v∩C={b} :=
  (Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr (mem_neighbors_in.mpr ⟨h,hb⟩))
    (by rw [hc,Finset.card_singleton])).symm
end Fb
open Fa Fb
variable (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hHyp : Ch0 G x y z q) (hq4 : q≤ 4) (hfail : ¬ Adm0 G x y q)
    (W : Wc0 G x y z)
include ih hHyp hq4 hfail W in
theorem qb1 : ∃ B b,Fb0 G W.C y z B b:=by
  classical
  let M:=W.C.filter (fun v=>v=y∨z=some v)
  have hy:=qc2 W
  have hl:=linked W
  by_cases hm : qm3 G W.C M
  · exact qag8 hl hy (fun v hv h=>Finset.mem_filter.mpr ⟨hv,h⟩) hm
  have hlow:=qn3 ih hHyp hq4 hfail W
  have hh:=hlow.trans (Finset.card_filter_le W.C _)
  obtain ⟨hcM,hdeg⟩:=qy5 W.C M (Finset.filter_subset _ _)
    (qan3 W.C y z) hh hl hm
  obtain ⟨zv,hz,hzC,hzy⟩ : ∃ zv,z=some zv∧zv∈W.C∧zv≠y:=by
    have hyM : y∈M:=Finset.mem_filter.mpr ⟨hy,Or.inl rfl⟩
    obtain ⟨v,hv,hvy⟩:=Finset.exists_mem_notMem_of_card_lt_card
      (show ({y} : Finset V).card < M.card by simp [hcM])
    have hne : v≠y:=by simpa using hvy
    exact ⟨v,(Finset.mem_filter.mp hv).2.resolve_left hne,(Finset.mem_filter.mp hv).1,hne⟩
  have hzM : zv∈M:=Finset.mem_filter.mpr ⟨hzC,Or.inr hz⟩
  obtain ⟨b,hbC,hzb⟩:=qi4 (hl zv hzC y hy) hzy
  have hby : b≠y:=by
    intro e
    exact qd5 ih hHyp hq4 hfail zv hz
      (fun f=>qa1 W hzC (f.symm ▸ W.core.x_mem_verts)) hzy (e ▸ hzb.symm)
  have hbz : b≠zv:=hzb.ne.symm
  have hbM : b∉M:=fun h=>(Finset.mem_filter.mp h).2.elim hby
    (fun e=>hbz (Option.some.inj (e.symm.trans hz)))
  have hz1 : (G.neighborFinset zv∩W.C).card=1:=by simpa [hzM] using hdeg zv hzC
  have hb2 : (G.neighborFinset b∩W.C).card=2:=by simpa [hbM] using hdeg b hbC
  obtain ⟨c,hc,hcz,hpair,-,hc3⟩ :=
    (qh2 ih hHyp hq4 hfail W hz hzC hzy hbC hby
      (qh3 hz1 hbC hzb) hb2).2.2.2.2.2
  have hcy : c=y:=by
    by_contra h
    have hd:=hc3 h
    have he:=hdeg c hc
    split at he <;> omega
  subst c
  have hbyAdj : G.Adj b y:=mem_neighbors_in.mp
    (hpair.symm ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self y)) |>.1
  have hyM : y∈M:=Finset.mem_filter.mpr ⟨hy,Or.inl rfl⟩
  have hy1 : (G.neighborFinset y∩W.C).card=1:=by simpa [hyM] using hdeg y hy
  have hyN:=qh3 hy1 hbC hbyAdj.symm
  have hzN:=qh3 hz1 hbC hzb
  exfalso
  apply qg0 ih hHyp hq4 hfail W
  refine ⟨b,zv,hz,Finset.Subset.antisymm ?_ (Finset.insert_subset_iff.mpr
    ⟨hy,Finset.insert_subset_iff.mpr ⟨hbC,Finset.singleton_subset_iff.mpr hzC⟩⟩)⟩
  intro a ha
  obtain ⟨p,hp⟩:=hl y hy a ha
  exact qb9 (C:={y,b,zv}) (D:=fun d=>d∉W.C)
    (fun v hv u had=>by
      apply or_iff_not_imp_right.mpr
      intro hu
      have huN:=mem_neighbors_in.mpr ⟨had,not_not.mp hu⟩
      simp only [Finset.mem_insert,Finset.mem_singleton] at hv
      rcases hv with rfl|rfl|rfl
      · rw [hyN] at huN
        exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp huN)))
      · rw [hpair] at huN
        rcases Finset.mem_insert.mp huN with rfl|h
        · simp
        · rw [Finset.mem_singleton] at h
          exact h ▸ Finset.mem_insert_self _ _
      · rw [hzN] at huN
        exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp huN))))
    p (by simp) (fun d hd hn=>hn (hp d hd)) a p.end_mem_support
namespace Fb
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem qad8 {A D E : Finset V} {u v w : V} {m n : ℕ}
    (p : Pi0 G A u v m) (r : Pi0 G D v w n) (hAD : ∀ a∈A,a∈D→ a=v)
    (hA : A⊆E) (hD : D⊆E) :
    Pi0 G E u w (m+n):=by
  obtain ⟨P,hP,hPl,hPs⟩:=p
  obtain ⟨R,hR,hRl,hRs⟩:=r
  have h:=qa3 hP hR fun a ha hb=>hAD a (hPs a ha) (hRs a hb)
  refine ⟨P.append R,h.1,by rw [h.2.1,hPl,hRl],fun a ha=>?_⟩
  exact ((Walk.mem_support_append_iff _ _).mp ha).elim (fun ha=>hA (hPs a ha))
    fun ha=>hD (hRs a ha)
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qp1 {A B : Finset V} {b u : V} (hB : Fb0 G A y z B b)
    (hu : u∈B) (hr : Rc0 G (A.erase b) y u) : False:=by
  have hyb:=Finset.ne_of_mem_erase hr.left_mem
  have hyB : y∉B:=fun hy =>
    (Finset.mem_sdiff.mp hB.exit_reach.right_mem).2 (Finset.mem_erase.mpr ⟨hyb,hy⟩)
  obtain ⟨c,hc,hsep⟩:=hB.block.separates y (Finset.mem_of_mem_erase hr.left_mem) hyB
  by_cases hcb : c=b
  · exact hsep u hu (hcb.symm ▸ hr)
  · apply hsep b hB.exit_mem
    exact hB.exit_reach.symm.mono fun a ha=>Finset.mem_erase.mpr
      ⟨fun e=>(Finset.mem_sdiff.mp ha).2 (e.symm ▸ Finset.mem_erase.mpr ⟨hcb,hc⟩),
        (Finset.mem_sdiff.mp ha).1⟩
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qr2 {C B : Finset V} {b v : V} {e : Option V}
    (he : ∀ u∈B.erase b,(Ici0 G C u∨u=y∨z=some u)→ e=some u)
    (hv : v∈B) (hvb : v≠b) (hve : e≠some v) :
    ¬ Ici0 G C v∧v≠y∧z≠some v:=by
  have hh:=fun h=>hve (he v (Finset.mem_erase.mpr ⟨hvb,hv⟩) h)
  exact ⟨fun h=>hh (Or.inl h),fun h=>hh (Or.inr (Or.inl h)),fun h=>hh (Or.inr (Or.inr h))⟩
private theorem qah1 {t : V} (ht : W.isFlat=some t) :
    Ici0 G W.C t:=by
  have hmode : Ifo0 W.base W.core t∧Ft0 z W.base t:=by
    simpa only [ht] using W.h_mode
  obtain ⟨hf,htr⟩:=hmode
  have hyt : G.Adj y t:=by rw [← mem_neighborFinset,htr.2.2.2.2.1];exact hf.2.1
  have hmem:=mem_compIn.mpr (Rc0.adj
    (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y,W.core.y_notMem_verts⟩)
    (Finset.mem_sdiff.mpr ⟨Finset.mem_univ t,hf.t₀_notMem⟩) hyt)
  rw [← W.hC_eq] at hmem
  refine ⟨hmem,fun hl=>?_⟩
  obtain ⟨u,hu,huy,hut⟩ : ∃ u∈W.C,u≠y∧u≠t:=by
    have h:=W.h_flat_large t ht
    obtain ⟨u,hu,hut⟩:=Finset.exists_mem_notMem_of_card_lt_card
      (show ({t} : Finset V).card < (W.C.filter (fun v=>v≠y∧z≠some v)).card by
        simp only [Finset.card_singleton];omega)
    exact ⟨u,(Finset.mem_filter.mp hu).1,(Finset.mem_filter.mp hu).2.1,by simpa using hut⟩
  obtain ⟨a,ha,hya⟩:=qi4 (hl y (Finset.mem_erase.mpr ⟨hyt.ne,qc2 W⟩)
    u (Finset.mem_erase.mpr ⟨hut,hu⟩)) (Ne.symm huy)
  have haT : a∈W.base.T:=by rwa [← htr.2.2.2.2.1,mem_neighborFinset]
  have haT' : a∈W.core.T:=by
    rw [hf.2.2.2.1]
    exact Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase ha,haT⟩
  exact qa1 W (Finset.mem_of_mem_erase ha) (W.core.T_subset_verts haT')
private theorem qv8 {B : Finset V} {b v : V}
    (hB : Fb0 G W.C y z B b) (hv : v∈B) (hc : ¬ Ici0 G W.C v) :
    G.neighborFinset v∩W.C=G.neighborFinset v∩B:=by
  ext w
  simp only [mem_neighbors_in]
  refine and_congr_right fun hw=>⟨fun hwC=>?_,fun h=>hB.block.subset h⟩
  by_contra hwB
  exact hc ((qa7 (linked W) hB.block hv).mp ⟨w,hwC,hwB,hw⟩)
private theorem qx4 {B : Finset V} (hB : B⊆W.C) :
    B.card+1 < Fintype.card V:=by
  obtain ⟨t,ht⟩:=Finset.card_pos.mp (show 0 < W.core.T.card by have:=W.core.two_le_T;omega)
  have hx : x∉B:=fun hx=>qa1 W (hB hx) W.core.x_mem_verts
  have ht' : t∉insert x B:=fun h=>(Finset.mem_insert.mp h).elim
    (fun e=>W.core.x_notMem_T (e ▸ ht)) (fun h=>qa1 W (hB h) (W.core.T_subset_verts ht))
  simpa [Finset.card_insert_of_notMem hx] using Cb.card_lt_of_notMem ht'
private theorem qae4 {B : Finset V} (v : (B : Set V)) :
    (G.induce (B : Set V)).degree v=(G.neighborFinset v.1∩B).card:=by
  rw [← card_neighborFinset_eq_degree]
  refine Finset.card_bij (fun w _=>w.1) (fun w hw=>?_) (fun _ _ _ _ h=>Subtype.ext h) ?_
  · exact mem_neighbors_in.mpr ⟨((G.induce (B : Set V)).mem_neighborFinset v w).mp hw,w.2⟩
  · intro w hw
    obtain ⟨had,hwB⟩:=mem_neighbors_in.mp hw
    exact ⟨⟨w,hwB⟩,((G.induce (B : Set V)).mem_neighborFinset v _).mpr had,rfl⟩
end Fb
include ih W in
theorem qd6 {B K : Finset V} {b : V} (hB : Fb0 G W.C y z B b)
    (e : Option V) {n : ℕ} (hn : 1≤ n) (hn4 : n≤ 4) (hK : Disjoint K B)
    (hattach : ∃ u∈B.erase b,∃ k∈K,G.Adj u k)
    (hwit : ∃ u∈B.erase b,e≠some u)
    (hdeg : ∀ v∈B.erase b,e≠some v→ n+1≤ (G.neighborFinset v∩B).card +
      if (G.neighborFinset v∩K).Nonempty then 1 else 0) :
    ∃ a d : ℕ,2≤ a∧(d=1∨d=2) ∧
      ∀ i : Fin n,∃ k∈K,Pi0 G (insert k B) k b (a+i.val*d):=by
  classical
  let I:=G.induce (B : Set V)
  let Z : Finset (B : Set V):=Finset.univ.filter fun v=>(G.neighborFinset v.1∩K).Nonempty
  have hZ : ∀ v : (B : Set V),v∈Z↔∃ k∈K,G.Adj v.1 k:=by
    intro v
    simp only [Z,Finset.mem_filter_univ,Finset.Nonempty,mem_neighbors_in]
    exact ⟨fun ⟨k,hk,ha⟩=>⟨k,ha,hk⟩,fun ⟨k,hk,ha⟩=>⟨k,ha,hk⟩⟩
  let J:=av0 I Z
  let r : (B : Set V):=⟨b,hB.exit_mem⟩
  have hroot : Rt0 J none (some r) :=
    Cb.rooted_adjoin Z hB.exit_mem hB.block.card hB.block.linked fun w hw v hv=>by
      by_cases hwb : w=b
      · subst w
        obtain ⟨u,hu,k,hk,ha⟩:=hattach
        exact ⟨u,hu,Or.inr ⟨Finset.mem_of_mem_erase hu,(hZ _).mpr ⟨k,hk,ha⟩⟩,
          hB.block.erase_linked b hw u hu v hv⟩
      · have hb:=Finset.mem_erase.mpr ⟨Ne.symm hwb,hB.exit_mem⟩
        exact ⟨b,hb,Or.inl rfl,hB.block.erase_linked w hw b hb v hv⟩
  let π (v : V) : Option (B : Set V):=if hv : v∈B then some ⟨v,hv⟩ else none
  have hπi (v : (B : Set V)) : π v.1=some v:=dif_pos v.2
  have hπo (v : V) (hv : v∈K) : π v=none:=dif_neg (Finset.disjoint_left.mp hK hv)
  have hedge : J.edgeFinset.card≤ G.edgeFinset.card :=
    Cb.card_edge_le_of_proj π (fun a c hac=>by
      cases a <;> cases c
      · exact (adjoin_not_adj_none hac).elim
      · rename_i v
        obtain ⟨k,hk,h⟩:=(hZ v).mp hac
        exact ⟨k,v.1,h.symm,hπo k hk,hπi v⟩
      · rename_i v
        obtain ⟨k,hk,h⟩:=(hZ v).mp hac
        exact ⟨v.1,k,h,hπi v,hπo k hk⟩
      · rename_i u v
        exact ⟨u.1,v.1,hac,hπi u,hπi v⟩)
  have hm:=qx4 W hB.block.subset
  have hcard : Fintype.card (Option (B : Set V))=B.card+1:=by simp
  obtain ⟨e',he'⟩:=Cb.exists_pull (W:=(B : Set V)) Subtype.val_injective e
  have hh : Ch0 J none (some r) (e'.map some) n:=by
    refine ⟨hn,hroot,?_,?_⟩
    · obtain ⟨v,hv,he⟩:=hwit
      exact ⟨some ⟨v,Finset.mem_of_mem_erase hv⟩,by simp,by simpa [r] using Finset.ne_of_mem_erase hv,
        fun h=>he ((he' _).mp (Cb.map_some_iff.mp h))⟩
    · intro v hv hvr hve
      cases v with
      | none=>exact (hv rfl).elim
      | some v =>
        have hvb : v.1≠b:=fun h=>hvr (congrArg some (Subtype.ext h))
        have he : e≠some v.1:=fun h=>hve (Cb.map_some_iff.mpr ((he' _).mpr h))
        rw [show J.degree (some v)=I.degree v+if v∈Z then 1 else 0 from qi2 Z v,
          qae4]
        have hZ' : v∈Z↔(G.neighborFinset v.1∩K).Nonempty:=by
          simp only [Z,Finset.mem_filter_univ]
        rw [ite_congr (propext hZ') (fun _=>rfl) (fun _=>rfl)]
        exact hdeg v.1 (Finset.mem_erase.mpr ⟨hvb,v.2⟩) he
  obtain ⟨a,d,ha,hd,hp⟩:=ih _ J none (some r) (e'.map some) n hn4 (by rw [hcard];omega) hh
  refine ⟨a,d,ha,hd,fun i=>?_⟩
  obtain ⟨p,hp',hpl⟩:=hp i
  obtain ⟨v,hv,m,hmp,hml,-⟩:=qf4 hp'
  obtain ⟨k,hk,had⟩:=(hZ v).mp hv
  obtain ⟨P,hP,hPl,-,hPs⟩:=qd3 (G:=G) (B : Set V) hmp
  exact ⟨k,hk,((show Pi0 G B v.1 b m.length from ⟨P,hP,hPl,hPs⟩).cons had.symm
    (Finset.disjoint_left.mp hK hk)).len (hml.symm.trans hpl)⟩
namespace Fb
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qj3 {B K A : Finset V}
    {b : V} (hBA : B⊆A)
    (hKA : Disjoint K A) {n a d : ℕ}
    (hP : ∀ i : Fin n,∃ k∈K,Pi0 G (insert k B) k b (a+i.val*d))
    (r : ℕ) (hR : Pi0 G (A\B.erase b) b y r) :
    ∀ i : Fin n,∃ k∈K,Pi0 G (insert k A) k y (a+r+i.val*d):=by
  intro i
  obtain ⟨k,hk,hp⟩:=hP i
  refine ⟨k,hk,(qad8 hp hR ?_ (Finset.insert_subset_insert k hBA)
    (Finset.sdiff_subset.trans (Finset.subset_insert _ _))).len (by omega)⟩
  intro v hv hvR
  have hvB:=(Finset.mem_insert.mp hv).resolve_left
    (fun e=>Finset.disjoint_left.mp hKA hk (e ▸ (Finset.mem_sdiff.mp hvR).1))
  exact Classical.byContradiction fun h=>(Finset.mem_sdiff.mp hvR).2 (Finset.mem_erase.mpr ⟨h,hvB⟩)
private theorem qd8 :
    Disjoint W.core.verts W.C :=
  Finset.disjoint_left.mpr fun _ h h'=>qa1 W h' h
private theorem qag1 {v : V} (hv : v∈W.core.verts) :
    ∃ a,Pi0 G W.core.verts x v a:=by
  rcases Cc0.mem_verts.mp hv with rfl|hs|ht
  · exact ⟨0,Pi0.nil W.core.x_mem_verts⟩
  · have hp : 0 < W.core.ell:=by
      cases hk : W.core.kind
      · rw [(W.core.shape1 hk).1] at hs
        exact (Finset.notMem_empty _ hs).elim
      · rw [W.core.ell_t2 hk];have:=W.core.two_le_T;omega
      · rw [W.core.ell_t3 hk];exact Finset.card_pos.mpr ⟨v,hs⟩
    obtain ⟨a,d,-,-,hP⟩:=qaf1 W.core
    exact ⟨_,hP v hs ⟨0,hp⟩⟩
  · obtain ⟨a,d,-,-,hP⟩:=qaf0 W.core
    exact ⟨_,hP v ht ⟨0,by omega⟩⟩
private theorem qm9 {B : Finset V} {b v : V}
    (hB : Fb0 G W.C y z B b) (hv : v∈B) (hc : ¬ Ici0 G W.C v) :
    G.degree v=(G.neighborFinset v∩B).card+(G.neighborFinset v∩W.core.verts).card:=by
  rw [qj4 W (hB.block.subset hv),qv8 W hB hv hc]
private theorem qs8 {B K : Finset V} (hB : B⊆W.C)
    (hK : K⊆W.core.verts) : Disjoint K B :=
  Disjoint.mono hK hB (qd8 W)
include ih hHyp hq4 hfail W in
private theorem no_T {B : Finset V} {b : V} (hB : Fb0 G W.C y z B b) :
    ∀ u∈B.erase b,∀ t∈W.core.T,¬ G.Adj u t:=by
  classical
  intro u hu t ht h
  obtain ⟨e,he,hwit⟩:=hB.exception
  have hell:=W.h_ell_le_tight hfail
    (Or.inr ⟨u,hB.block.subset (Finset.mem_of_mem_erase hu),t,ht,h⟩)
  have hk : Disjoint W.core.T W.C:=Disjoint.mono W.core.T_subset_verts subset_rfl (qd8 W)
  have hq:=hHyp.1
  obtain ⟨a,d,ha,hd,hP⟩:=qd6 ih W hB e
    (n:=q - W.core.ell) (by omega) (by omega) (Disjoint.mono_right hB.block.subset hk)
    ⟨u,hu,t,ht,h⟩ hwit (fun v hv hve=>by
      have hvB:=Finset.mem_of_mem_erase hv
      have hvC:=hB.block.subset hvB
      obtain ⟨hcut,hvy,hvz⟩:=qr2 he hvB (Finset.ne_of_mem_erase hv) hve
      have hflat : W.isFlat≠some v:=fun h=>hcut (qah1 W h)
      have hdg:=hHyp.2.2.2 v (fun e=>qa1 W hvC (e.symm ▸ W.core.x_mem_verts)) hvy hvz
      have hsplit:=qm9 W hB hvB hcut
      obtain ⟨hlim,hh⟩:=W.h_ext_deg v (qa1 W hvC) hvy hflat
      split
      · omega
      · rename_i hn
        have hlt : (G.neighborFinset v∩W.core.verts).card≠W.core.ell+1:=by
          intro heq
          obtain ⟨k,hk,hvk⟩:=hh heq
          exact hn ⟨k,mem_neighbors_in.mpr ⟨hvk,hk⟩⟩
        omega)
  obtain ⟨r,hR⟩:=qe5 hB.exit_reach
  have hh:=qag4 W (n:=q - W.core.ell) (b:=a+r) (by omega) (by omega) hd
    (qj3 hB.block.subset hk hP r hR)
  exact hfail ((show W.core.ell+1+(q - W.core.ell) - 1=q by omega) ▸ hh)
def qc5 (G : SimpleGraph V) (B K : Finset V) (b : V)
    [DecidablePred (fun k=>∃ u∈B.erase b,G.Adj u k)] : Finset V :=
  K.filter fun k=>∃ u∈B.erase b,G.Adj u k
private theorem qv6 {b : V} {P : Finset V}
    (hb : b∈W.C) (hP : Side G W.C b P) :
    ∃ k∈W.core.verts,∃ u∈P,G.Adj k u:=by
  obtain ⟨v,hv⟩:=hP.2.1
  have hx : x∉P:=fun h=>qa1 W (Finset.mem_of_mem_erase (hP.1 h)) W.core.x_mem_verts
  have hxb : x≠b:=fun e=>qa1 W hb (e ▸ W.core.x_mem_verts)
  obtain ⟨u,hu,hr⟩:=qi5 ((kConn_two_iff.mp W.hK).2 b x (by simpa using hxb)
    v (by simpa using Finset.ne_of_mem_erase (hP.1 hv))) hv
  obtain ⟨k,hk,had⟩:=qi4 hr.symm (fun e=>hx (e ▸ hu))
  have hkP : k∉P:=fun hkP=>(Finset.mem_sdiff.mp hk).2 (Finset.mem_erase.mpr ⟨had.ne.symm,hkP⟩)
  refine ⟨k,(qh9 W (Finset.mem_of_mem_erase (hP.1 hu)) had).resolve_left ?_,u,hu,had.symm⟩
  exact fun h=>hkP (hP.2.2.2 u hu k (Finset.mem_erase.mpr
    ⟨Finset.ne_of_mem_erase (Finset.mem_sdiff.mp hk).1,h⟩) had)
include ih hHyp hq4 hfail W in
private theorem qr8 {B : Finset V} {b : V} (hB : Fb0 G W.C y z B b)
    (h0 : ∀ u∈B.erase b,∀ k∈W.core.verts,¬ G.Adj u k) : False:=by
  classical
  obtain ⟨e,he,u,hu,hue⟩:=hB.exception
  have huB:=Finset.mem_of_mem_erase hu
  have huC : u∈W.C.erase b:=Finset.mem_erase.mpr ⟨Finset.ne_of_mem_erase hu,hB.block.subset huB⟩
  obtain ⟨P,huP,hP⟩:=qag6 huC
  have hyP : y∉P:=fun h=>qp1 hB huB ((hP.2.2.1 y h u huP).mono hP.1)
  have hbP : b∉P:=fun h=>Finset.notMem_erase _ _ (hP.1 h)
  have hcl : ∀ a∈P,∀ v∈W.C,G.Adj a v→ v∈P∨v=b:=fun a ha v hv had=>by
    by_cases h : v=b
    · exact Or.inr h
    · exact Or.inl (hP.2.2.2 a ha v (Finset.mem_erase.mpr ⟨h,hv⟩) had)
  obtain ⟨r,R,hR,hRl,hRs⟩:=qe5 hB.exit_reach
  have hRC : ∀ a∈R.support,a∈W.C:=fun a ha=>(Finset.mem_sdiff.mp (hRs a ha)).1
  have hRP:=qv1 hbP hyP hcl hR hRC
  obtain ⟨k,hk,v,hv,hkv⟩:=qv6 W (hB.block.subset hB.exit_mem) hP
  have hj : Rc0 G (insert k P) k u :=
    (Rc0.adj (Finset.mem_insert_self _ _) (Finset.mem_insert_of_mem hv) hkv).trans
      ((hP.2.2.1 v hv u huP).mono (Finset.subset_insert _ _))
  obtain ⟨c,hc,hkc⟩:=qi5 hj huB
  have hkB : k∉B:=fun h=>qa1 W (hB.block.subset h) hk
  have hck : c≠k:=fun h=>hkB (h ▸ hc)
  have hcP:=(Finset.mem_insert.mp (Finset.mem_sdiff.mp hkc.right_mem).1).resolve_left hck
  have hcb : c≠b:=fun h=>hbP (h ▸ hcP)
  have hce : e=some c:=by
    by_contra hn
    obtain ⟨hcut,-,-⟩:=qr2 he hc hcb hn
    obtain ⟨w,hw,hcw⟩:=qi4 hkc.symm hck
    have hwB : w∉B:=fun h=>(Finset.mem_sdiff.mp hw).2 (Finset.mem_erase.mpr ⟨hcw.ne.symm,h⟩)
    rcases Finset.mem_insert.mp (Finset.mem_sdiff.mp hw).1 with rfl|hwP
    · exact h0 c (Finset.mem_erase.mpr ⟨hcb,hc⟩) _ hk hcw
    · exact hcut ((qa7 (linked W) hB.block hc).mp
        ⟨w,Finset.mem_of_mem_erase (hP.1 hwP),hwB,hcw⟩)
  have huc : u≠c:=fun h=>hue (h.symm ▸ hce)
  have hcard : 2 < B.card:=by
    have hs : ({u,c,b} : Finset V)⊆B:=Finset.insert_subset_iff.mpr
      ⟨huB,Finset.insert_subset_iff.mpr ⟨hc,Finset.singleton_subset_iff.mpr hB.exit_mem⟩⟩
    have hh:=Finset.card_le_card hs
    rw [Finset.card_insert_of_notMem (by simpa using And.intro huc (Finset.ne_of_mem_erase hu)),
      Finset.card_pair hcb] at hh
    omega
  have hroot:=qb4 hcb hcard
    (fun w hw=>(hB.block.erase_linked w hw).mono_graph le_sup_left) hc hB.exit_mem
  obtain ⟨a,d,ha,hd,hPaths⟩:=Cb.induce_call (ih.toAt hq4) B hc hB.exit_mem none hHyp.1
    hroot (by have:=qx4 W hB.block.subset;omega)
    (fun w hw hwc hwb _=>by
      have hwe : e≠some w:=fun f=>hwc (Option.some.inj (f.symm.trans hce))
      obtain ⟨hcut,hwy,hwz⟩:=qr2 he hw hwb hwe
      have hwC:=hB.block.subset hw
      refine ⟨hHyp.2.2.2 w (fun e=>qa1 W hwC (e.symm ▸ W.core.x_mem_verts)) hwy hwz,
        fun v hv=>?_⟩
      rcases qh9 W hwC hv with hvC|hvC
      · by_contra h
        exact hcut ((qa7 (linked W) hB.block hw).mp ⟨v,hvC,h,hv⟩)
      · exact (h0 w (Finset.mem_erase.mpr ⟨hwb,hw⟩) v hvC hv).elim)
    ⟨u,huB,huc,Finset.ne_of_mem_erase hu,by simp⟩
  obtain ⟨j,hJ⟩:=qe5 hkc
  obtain ⟨i,hI⟩:=qag1 W hk
  have hQ : Pi0 G ((W.core.verts∪P)\B.erase c) x c (i+j) :=
    qad8 hI hJ (fun v hv h=>(Finset.mem_insert.mp (Finset.mem_sdiff.mp h).1).resolve_right
      (fun h=>qa1 W (Finset.mem_of_mem_erase (hP.1 h)) hv))
      (fun v hv=>Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hv,
        fun h=>qa1 W (hB.block.subset (Finset.mem_of_mem_erase h)) hv⟩)
      (fun v hv=>Finset.mem_sdiff.mpr ⟨(Finset.mem_insert.mp (Finset.mem_sdiff.mp hv).1).elim
        (fun e=>Finset.mem_union_left _ (e.symm ▸ hk)) (Finset.mem_union_right _),
        (Finset.mem_sdiff.mp hv).2⟩)
  refine hfail ⟨i+j+a+r,d,by omega,hd,fun l=>?_⟩
  obtain ⟨p,hp,hpl,hps⟩:=hPaths l
  obtain ⟨Q,hQp,hQl,hQs⟩:=hQ
  have h1:=qa3 hQp hp fun v hv hv'=>by
    by_contra h
    exact (Finset.mem_sdiff.mp (hQs v hv)).2 (Finset.mem_erase.mpr ⟨h,hps v hv'⟩)
  have h2:=qa3 h1.1 hR fun v hv hv'=>by
    rcases (Walk.mem_support_append_iff _ _).mp hv with h|h
    · exact ((Finset.mem_union.mp (Finset.mem_sdiff.mp (hQs v h)).1).elim
        (qa1 W (hRC v hv')) (hRP v hv')).elim
    · by_contra hn
      exact (Finset.mem_sdiff.mp (hRs v hv')).2 (Finset.mem_erase.mpr ⟨hn,hps v h⟩)
  exact ⟨(Q.append p).append R,h2.1,by rw [h2.2.1,h1.2.1,hQl,hpl,hRl];omega⟩
private theorem qx6 {B : Finset V} {b : V}
    (hT : ∀ u∈B.erase b,∀ t∈W.core.T,¬ G.Adj u t) {u k : V}
    (hu : u∈B.erase b) (hk : k∈W.core.verts) (had : G.Adj u k) :
    k=x∨k∈W.core.S :=
  (Cc0.mem_verts.mp hk).elim Or.inl fun h=>Or.inr (h.resolve_right fun ht=>hT u hu k ht had)
include ih hHyp hq4 hfail W in
private theorem qr7 {B : Finset V} {b k : V} (hB : Fb0 G W.C y z B b)
    (hk : k∈W.core.verts) (ha : ∃ u∈B.erase b,G.Adj u k)
    (honly : ∀ u∈B.erase b,∀ w∈W.core.verts,G.Adj u w→ w=k) : False:=by
  classical
  obtain ⟨e,he,hwit⟩:=hB.exception
  have hsub : ({k} : Finset V)⊆W.core.verts:=Finset.singleton_subset_iff.mpr hk
  obtain ⟨a,d,ha',hd,hP⟩:=qd6 ih W hB e hHyp.1 hq4
    (qs8 W hB.block.subset hsub) (by simpa using ha) hwit (fun u hu hue=>by
      have huB:=Finset.mem_of_mem_erase hu
      have huC:=hB.block.subset huB
      obtain ⟨hcut,huy,huz⟩:=qr2 he huB (Finset.ne_of_mem_erase hu) hue
      have hdeg:=hHyp.2.2.2 u (fun e=>qa1 W huC (e.symm ▸ W.core.x_mem_verts)) huy huz
      have hsplit:=qm9 W hB huB hcut
      have hN : G.neighborFinset u∩W.core.verts⊆G.neighborFinset u∩{k}:=by
        intro v hv
        obtain ⟨had,hv⟩:=mem_neighbors_in.mp hv
        exact mem_neighbors_in.mpr ⟨had,Finset.mem_singleton.mpr (honly u hu v hv had)⟩
      split
      · have hcard:=(Finset.card_le_card hN).trans (Finset.card_le_card Finset.inter_subset_right)
        simp only [Finset.card_singleton] at hcard
        omega
      · rename_i h
        have hc:=Finset.card_le_card hN
        rw [Finset.not_nonempty_iff_eq_empty.mp h,Finset.card_empty] at hc
        omega)
  obtain ⟨r,hR⟩:=qe5 hB.exit_reach
  obtain ⟨i,hI⟩:=qag1 W hk
  have hp:=qj3 hB.block.subset (Disjoint.mono_left hsub (qd8 W)) hP r hR
  have hh:=qae9 (p:=1) (n:=q) (a:=i) (b:=a+r) (d:=1) (e:=d)
    le_rfl hHyp.1 (by omega) (Or.inl rfl) hd (fun j=>by
      obtain ⟨v,hv,h⟩:=hp j
      obtain rfl:=Finset.mem_singleton.mp hv
      exact ⟨v,h,fun l=>by simpa [show l.val=0 by omega] using hI⟩) (qd8 W)
  exact hfail ((show 1+q - 1=q by omega) ▸ hh)
end Fb
include ih hHyp hq4 hfail W in
theorem qa6 {B : Finset V} {b : V} (hB : Fb0 G W.C y z B b) :
    (∀ u∈B.erase b,∀ t∈W.core.T,¬ G.Adj u t) ∧
    (∀ u∈B.erase b,∀ k∈W.core.verts,G.Adj u k→ k=x∨k∈W.core.S) ∧
    2≤ (qc5 G B (insert x W.core.S) b).card:=by
  classical
  have hT:=no_T ih hHyp hq4 hfail W hB
  have hA:=fun u hu k hk had=>qx6 W hT (u:=u) (k:=k) hu hk had
  refine ⟨hT,hA,?_⟩
  let K:=qc5 G B (insert x W.core.S) b
  have hm {k : V} : k∈K↔(k=x∨k∈W.core.S)∧∃ u∈B.erase b,G.Adj u k:=by
    simp only [K,qc5,Finset.mem_filter,Finset.mem_insert]
  change 2≤ K.card
  by_contra hn
  have hc : K.card≤ 1:=by omega
  by_cases hne : K.Nonempty
  · obtain ⟨k,hk⟩:=hne
    obtain ⟨hk',ha⟩:=hm.mp hk
    have hkH : k∈W.core.verts:=hk'.elim (fun e=>e.symm ▸ W.core.x_mem_verts)
      (fun h=>W.core.S_subset_verts h)
    exact qr7 ih hHyp hq4 hfail W hB hkH ha (fun u hu v hv had =>
      Finset.card_le_one.mp hc v (hm.mpr ⟨hA u hu v hv had,u,hu,had⟩) k hk)
  · exact qr8 ih hHyp hq4 hfail W hB (fun u hu k hk had =>
      hne ⟨k,hm.mpr ⟨hA u hu k hk had,u,hu,had⟩⟩)
include ih hHyp hq4 hfail W in
theorem qu7 : W.core.kind≠.t1:=by
  classical
  intro hk
  obtain ⟨B,b,hB⟩:=qb1 ih hHyp hq4 hfail W
  have h:=(qa6 ih hHyp hq4 hfail W hB).2.2
  rw [(W.core.shape1 hk).1] at h
  have h':=Finset.card_filter_le (insert x (∅ : Finset V)) (fun k=>∃ u∈B.erase b,G.Adj u k)
  have hc : (insert x (∅ : Finset V)).card=1:=by simp
  unfold qc5 at h
  omega
namespace Fb
private theorem qao2 {B : Finset V} {b : V}
    (h : 2≤ (qc5 G B (insert x W.core.S) b).card) :
    ∃ u∈B.erase b,∃ s∈W.core.S,G.Adj u s:=by
  by_contra hn
  have hs : qc5 G B (insert x W.core.S) b⊆{x}:=by
    intro k hk
    obtain ⟨hk,u,hu,had⟩:=Finset.mem_filter.mp hk
    exact Finset.mem_singleton.mpr ((Finset.mem_insert.mp hk).resolve_right
      fun hs=>hn ⟨u,hu,k,hs,had⟩)
  have hc:=Finset.card_le_card hs
  simp only [Finset.card_singleton] at hc
  omega
private theorem qz6 {B : Finset V} {b v : V}
    (hB : Fb0 G W.C y z B b) (hv : v∈B.erase b) (hcut : ¬ Ici0 G W.C v)
    (hT : ∀ t∈W.core.T,¬ G.Adj v t) {loss : ℕ} (hpos : 1≤ loss)
    (hbound : (G.neighborFinset v∩W.core.verts).card≤ loss+1) :
    G.degree v≤ (G.neighborFinset v∩B).card +
      (if (G.neighborFinset v∩W.core.S).Nonempty then 1 else 0)+loss:=by
  rw [qm9 W hB (Finset.mem_of_mem_erase hv) hcut]
  split
  · omega
  · rename_i hS
    have hs : G.neighborFinset v∩W.core.verts⊆{x}:=by
      intro w hw
      obtain ⟨had,hw⟩:=mem_neighbors_in.mp hw
      rcases Cc0.mem_verts.mp hw with h|h|h
      · exact Finset.mem_singleton.mpr h
      · exact (hS ⟨w,mem_neighbors_in.mpr ⟨had,h⟩⟩).elim
      · exact (hT w h had).elim
    have hs':=Finset.card_le_card hs
    simp only [Finset.card_singleton] at hs'
    omega
private theorem qz8 : W.core.kind=W.base.kind:=by
  cases h : W.isFlat with
  | none =>
    have hh:=W.h_mode
    simp only [h] at hh
    rw [hh.1]
  | some v =>
    have hh : Ifo0 W.base W.core v∧Ft0 z W.base v:=by
      simpa only [h] using W.h_mode
    exact hh.1.2.2.1.trans hh.1.1.symm
end Fb
include ih hHyp hq4 hfail W in
theorem qu6 : W.core.kind≠.t2:=by
  classical
  intro hk
  have hk':=(qz8 W).symm.trans hk
  have htri : ∀ H : Cc0 G x y,2≤ H.kind.rank :=
    fun H=>(show 2≤ Ck0.t2.rank by decide).trans (W.hopt.1.rank_ge hk' H)
  obtain ⟨B,b,hB⟩:=qb1 ih hHyp hq4 hfail W
  obtain ⟨hT,hA,hAS⟩:=qa6 ih hHyp hq4 hfail W hB
  obtain ⟨e,he,hwit⟩:=hB.exception
  have hcl:=W.core.shape2 hk
  have hq:=qb6 ih hHyp hq4 hfail
  have hs : Disjoint W.core.S W.C:=Disjoint.mono_left W.core.S_subset_verts (qd8 W)
  obtain ⟨a,d,ha,hd,hP⟩:=qd6 ih W hB e (n:=q - 1) (by omega)
    (by omega) (Disjoint.mono_right hB.block.subset hs) (qao2 W hAS) hwit (fun v hv hve=>by
      have hvB:=Finset.mem_of_mem_erase hv
      have hvC:=hB.block.subset hvB
      obtain ⟨hc,hvy,hvz⟩:=qr2 he hvB (Finset.ne_of_mem_erase hv) hve
      have hdg:=hHyp.2.2.2 v (fun e=>qa1 W hvC (e.symm ▸ W.core.x_mem_verts)) hvy hvz
      have hbound : (G.neighborFinset v∩W.core.verts).card≤ 1+1:=by
        by_cases hx : G.Adj x v
        · have hsub : G.neighborFinset v∩W.core.verts⊆{x}:=by
            intro k h
            obtain ⟨had,h⟩:=mem_neighbors_in.mp h
            exact Finset.mem_singleton.mpr ((hA v hv k h had).resolve_right fun hk =>
              qg7 htri W.core.x_ne_y hx (hcl.2.2.1 k hk) had hvy
                (fun e=>W.core.y_notMem_S (e ▸ hk)))
          exact (Finset.card_le_card hsub).trans (by simp)
        · have hsub : G.neighborFinset v∩W.core.verts⊆W.core.S:=by
            intro k h
            obtain ⟨had,h⟩:=mem_neighbors_in.mp h
            exact (hA v hv k h had).resolve_left fun e=>hx (e ▸ had.symm)
          exact (Finset.card_le_card hsub).trans (by omega)
      have h:=qz6 W hB hv hc (hT v hv) le_rfl hbound
      omega)
  obtain ⟨r,hR⟩:=qe5 hB.exit_reach
  have hQ:=qj3 hB.block.subset hs hP r hR
  have h:=qae9 (A:=W.core.verts) (B:=W.C) (p:=2) (n:=q - 1) (a:=1)
    (b:=a+r) (d:=2) (e:=d) (by omega) (by omega) (by omega) (Or.inr rfl) hd
    (fun j=>by
      obtain ⟨s,hs,h⟩:=hQ j
      refine ⟨s,h,fun i=>qh8 W.core hk hs _ ?_⟩
      rcases qa8 i with rfl|rfl
      · exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem (Finset.mem_Icc.mpr ⟨by decide,?_⟩)
        have:=W.core.two_le_T
        rw [W.core.ell_t2 hk]
        change 3≤ W.core.T.card+2
        omega) (qd8 W)
  exact hfail ((show 2+(q - 1) - 1=q by omega) ▸ h)
namespace Fb
include ih hHyp hq4 hfail W in
private theorem qap8 {B : Finset V} {b : V} (hB : Fb0 G W.C y z B b)
    {loss : ℕ} (hpos : 1≤ loss) (hsmall : loss < q) (hell : W.core.ell≤ loss+1) :
    ∃ a d : ℕ,2≤ a∧(d=1∨d=2) ∧
      ∀ i : Fin (q - loss),∃ s∈W.core.S,Pi0 G (insert s B) s b (a+i.val*d):=by
  obtain ⟨hT,-,hAS⟩:=qa6 ih hHyp hq4 hfail W hB
  obtain ⟨e,he,hwit⟩:=hB.exception
  refine qd6 ih W hB e (by omega) (by omega)
    (qs8 W hB.block.subset W.core.S_subset_verts) (qao2 W hAS) hwit ?_
  intro v hv hve
  have hvB:=Finset.mem_of_mem_erase hv
  have hvC:=hB.block.subset hvB
  obtain ⟨hc,hvy,hvz⟩:=qr2 he hvB (Finset.ne_of_mem_erase hv) hve
  have hdg:=hHyp.2.2.2 v (fun e=>qa1 W hvC (e.symm ▸ W.core.x_mem_verts)) hvy hvz
  have hm : W.isFlat≠some v:=fun h=>hc (qah1 W h)
  obtain ⟨hle,hsat⟩:=W.h_ext_deg v (qa1 W hvC) hvy hm
  have hbound : (G.neighborFinset v∩W.core.verts).card≤ W.core.ell:=by
    by_contra hn
    obtain ⟨t,ht,hvt⟩:=hsat (by omega)
    exact hT v hv t ht hvt
  have hd:=qz6 W hB hv hc (hT v hv) hpos (hbound.trans hell)
  omega
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qak5 {C B : Finset V} {b v : V} (hB : Fb0 G C y z B b)
    (hv : v∉B) (hvy : v≠y) (hdel : Lk0 G (C.erase v)) :
    ∃ r,Pi0 G ((C.erase v)\B.erase b) b y r:=by
  have hy : y∈C:=(Finset.mem_sdiff.mp hB.exit_reach.right_mem).1
  obtain ⟨c,hc,hr⟩:=qi5
    (hdel y (Finset.mem_erase.mpr ⟨Ne.symm hvy,hy⟩) b
      (Finset.mem_erase.mpr ⟨fun e=>hv (e ▸ hB.exit_mem),hB.block.subset hB.exit_mem⟩)) hB.exit_mem
  have hcb : c=b:=by
    by_contra hn
    apply qp1 hB hc (hr.mono ?_)
    exact fun u hu=>Finset.mem_erase.mpr ⟨fun e=>(Finset.mem_sdiff.mp hu).2
      (e.symm ▸ Finset.mem_erase.mpr ⟨Ne.symm hn,hB.exit_mem⟩),
      Finset.mem_of_mem_erase (Finset.mem_sdiff.mp hu).1⟩
  subst c
  exact qe5 hr.symm
end Fb
include ih hHyp hq4 hfail W in
theorem qc6 : W.core.kind=.t3∧W.core.ell=1:=by
  classical
  have h1:=qu7 ih hHyp hq4 hfail W
  have h2:=qu6 ih hHyp hq4 hfail W
  have hk : W.core.kind=.t3:=by
    cases h : W.core.kind
    · exact (h1 h).elim
    · exact (h2 h).elim
    · rfl
  refine ⟨hk,?_⟩
  obtain ⟨B,b,hB⟩:=qb1 ih hHyp hq4 hfail W
  obtain ⟨u,hu,s,hs,hus⟩:=qao2 W
    (qa6 ih hHyp hq4 hfail W hB).2.2
  have hpos : 1≤ W.core.ell:=W.core.ell_t3 hk ▸ Finset.card_pos.mpr ⟨s,hs⟩
  have hmax:=W.h_ell_le hfail
  by_contra hne
  obtain ⟨a,d,ha,hd,hP⟩:=qap8 ih hHyp hq4 hfail W hB
    (loss:=W.core.ell - 1) (by omega) (by omega) (by omega)
  obtain ⟨r,hR⟩:=qe5 hB.exit_reach
  have hdis:=Disjoint.mono_left W.core.S_subset_verts (qd8 W)
  have h:=qal6 W (n:=q - (W.core.ell - 1)) (b:=a+r) (by omega) hpos hd
    (qj3 hB.block.subset hdis hP r hR)
  exact hfail ((show W.core.ell+(q - (W.core.ell - 1)) - 1=q by omega) ▸ h)
namespace Fb
include ih hHyp hq4 hfail W in
private theorem qq6 {v s : V} (hv : v∈W.C) (hvy : v≠y)
    (hcut : ¬ Ici0 G W.C v) (hS : W.core.S={s}) (ht : ∃ t∈W.core.T,G.Adj v t)
    (d : ℕ) (hd : d=1∨d=2)
    (hP : ∀ i : Fin 2,Pi0 G (insert v W.core.verts) x s (2+i.val*d)) : False:=by
  classical
  have hq:=qb6 ih hHyp hq4 hfail
  have hell:=(qc6 ih hHyp hq4 hfail W).2
  obtain ⟨B,b,hB⟩:=qb1 ih hHyp hq4 hfail W
  have hT:=(qa6 ih hHyp hq4 hfail W hB).1
  have hvB : v∉B:=by
    intro hvB
    by_cases hvb : v=b
    · subst v
      exact hcut ((qa7 (linked W) hB.block hB.exit_mem).mp
        (qi8 hB.exit_reach.symm (Ne.symm hvy)))
    · obtain ⟨t,ht,had⟩:=ht
      exact hT v (Finset.mem_erase.mpr ⟨hvb,hvB⟩) t ht had
  obtain ⟨r,hR⟩:=qak5 hB hvB hvy (by
    by_contra hn
    exact hcut ⟨hv,hn⟩)
  obtain ⟨a,e,ha,he,hQ⟩:=qap8 ih hHyp hq4 hfail W hB
    (loss:=1) le_rfl (by omega) (by omega)
  have hds : Disjoint (insert v W.core.verts) (W.C.erase v):=by
    refine Finset.disjoint_left.mpr fun u hu huc=>?_
    exact (Finset.mem_insert.mp hu).elim (Finset.ne_of_mem_erase huc)
      (qa1 W (Finset.mem_of_mem_erase huc))
  have hbsub : B⊆W.C.erase v:=fun u hu =>
    Finset.mem_erase.mpr ⟨fun e=>hvB (e ▸ hu),hB.block.subset hu⟩
  have hdp : Disjoint W.core.S (W.C.erase v):=Disjoint.mono
    W.core.S_subset_verts (Finset.erase_subset _ _) (qd8 W)
  have hL:=qj3 hbsub hdp hQ r hR
  have hh:=qae9 (p:=2) (n:=q - 1) (a:=2) (b:=a+r) (d:=d) (e:=e)
    (by omega) (by omega) (by omega) hd he
    (fun j=>by
      obtain ⟨w,hw,h⟩:=hL j
      have hw' : w=s:=Finset.mem_singleton.mp (hS ▸ hw)
      subst w
      exact ⟨s,h,hP⟩) hds
  exact hfail ((show 2+(q - 1) - 1=q by omega) ▸ hh)
end Fb
include ih hHyp hq4 hfail W in
theorem qn2 {v : V} (hv : v∈W.C) (hvy : v≠y) (_hvz : z≠some v)
    (hcut : ¬ Ici0 G W.C v) :
    (G.neighborFinset v∩W.core.T).card≤ 1 ∧
      ((∃ s∈W.core.S,G.Adj v s)→ ∀ t∈W.core.T,¬ G.Adj v t):=by
  classical
  obtain ⟨hk,hell⟩:=qc6 ih hHyp hq4 hfail W
  obtain ⟨s,hS⟩:=Finset.card_eq_one.mp ((W.core.ell_t3 hk).symm.trans hell)
  have hs : s∈W.core.S:=hS.symm ▸ Finset.mem_singleton_self s
  have hshape:=W.core.shape3 hk
  have hvH:=qa1 W hv
  have two (t : V) (ht : t∈W.core.T) : Pi0 G (insert v W.core.verts) x s 2:=by
    have h:=(Pi0.edge (hshape.2.2.1 t ht)).concat (hshape.2.2.2.2.2 s hs t ht).symm
      (by simp [show s≠x from fun e=>W.core.x_notMem_S (e ▸ hs),
        show s≠t from fun e=>Finset.disjoint_left.mp W.core.disj hs (e.symm ▸ ht)])
    apply h.mono
    simp [Finset.insert_subset_iff,W.core.x_mem_verts,W.core.T_subset_verts ht,
      W.core.S_subset_verts hs]
  constructor
  · by_contra hn
    obtain ⟨t,ht,u,hu,htu⟩:=Finset.one_lt_card.mp (show 1 < (G.neighborFinset v∩W.core.T).card by omega)
    obtain ⟨hvt,ht⟩:=mem_neighbors_in.mp ht
    obtain ⟨hvu,hu⟩:=mem_neighbors_in.mp hu
    have htH:=W.core.T_subset_verts ht
    have huH:=W.core.T_subset_verts hu
    have hvx : v≠x:=fun e=>hvH (e.symm ▸ W.core.x_mem_verts)
    have hvt' : v≠t:=hvt.ne
    have hvu' : v≠u:=hvu.ne
    have hutx : u≠x:=fun e=>W.core.x_notMem_T (e ▸ hu)
    have hst : s≠t:=fun e=>Finset.disjoint_left.mp W.core.disj hs (e.symm ▸ ht)
    have hsu : s≠u:=fun e=>Finset.disjoint_left.mp W.core.disj hs (e.symm ▸ hu)
    have hsx : s≠x:=fun e=>W.core.x_notMem_S (e ▸ hs)
    have hsv : s≠v:=fun e=>hvH (e ▸ W.core.S_subset_verts hs)
    apply qq6 ih hHyp hq4 hfail W hv hvy hcut hS ⟨t,ht,hvt⟩ 2 (Or.inr rfl)
    intro i
    rcases qa8 i with rfl|rfl
    · exact two t ht
    · have p:=(Pi0.edge (hshape.2.2.1 t ht)).concat hvt.symm (by simp [hvx,hvt'])
      have p':=p.concat hvu (by simp [Ne.symm hvu',hutx,Ne.symm htu])
      have p'':=p'.concat (hshape.2.2.2.2.2 s hs u hu).symm (by simp [hsu,hsv,hsx,hst])
      exact p''.mono (by simp [Finset.insert_subset_iff,htH,huH,W.core.x_mem_verts,
        W.core.S_subset_verts hs])
  · rintro ⟨u,hu,hvu⟩ t ht hvt
    have hus : u=s:=Finset.mem_singleton.mp (hS ▸ hu)
    subst u
    have hvx : v≠x:=fun e=>hvH (e.symm ▸ W.core.x_mem_verts)
    have hsx : s≠x:=fun e=>W.core.x_notMem_S (e ▸ hs)
    have hst : s≠t:=fun e=>Finset.disjoint_left.mp W.core.disj hs (e.symm ▸ ht)
    apply qq6 ih hHyp hq4 hfail W hv hvy hcut hS ⟨t,ht,hvt⟩ 1 (Or.inl rfl)
    intro i
    rcases qa8 i with rfl|rfl
    · exact two t ht
    · have p:=(Pi0.edge (hshape.2.2.1 t ht)).concat hvt.symm (by simp [hvx,hvt.ne])
      have p':=p.concat hvu (by simp [hvu.ne.symm,hsx,hst])
      exact p'.mono (by simp [Finset.insert_subset_iff,W.core.T_subset_verts ht,W.core.x_mem_verts,
        W.core.S_subset_verts hs])
include ih hHyp hq4 hfail W in
theorem qd7 :
    (∃ s,W.core.S={s}) ∧
    ∀ v∈W.C,v≠y→ z≠some v→ ¬ Ici0 G W.C v →
      (G.neighborFinset v∩W.core.verts).card≤ 1:=by
  classical
  obtain ⟨hk,hell⟩:=qc6 ih hHyp hq4 hfail W
  refine ⟨Finset.card_eq_one.mp ((W.core.ell_t3 hk).symm.trans hell),?_⟩
  intro v hv hvy hvz hc
  obtain ⟨hle,hsat⟩:=W.h_ext_deg v (qa1 W hv) hvy (fun h=>hc (qah1 W h))
  by_contra hn
  obtain ⟨t,ht,hvt⟩:=hsat (by omega)
  obtain ⟨hT,hST⟩:=qn2 ih hHyp hq4 hfail W hv hvy hvz hc
  have hk':=(qz8 W).symm.trans hk
  have htri : ∀ H : Cc0 G x y,2≤ H.kind.rank :=
    fun H=>(show 2≤ Ck0.t3.rank by decide).trans (W.hopt.1.rank_ge hk' H)
  have hx : ¬ G.Adj v x:=fun h =>
    qg7 htri W.core.x_ne_y h.symm ((W.core.shape3 hk).2.2.1 t ht) hvt hvy
      (fun e=>W.core.y_notMem_T (e ▸ ht))
  have hsub : G.neighborFinset v∩W.core.verts⊆G.neighborFinset v∩W.core.T:=by
    intro u hu
    obtain ⟨had,hu⟩:=mem_neighbors_in.mp hu
    rcases Cc0.mem_verts.mp hu with rfl|hu|hu
    · exact (hx had).elim
    · exact (hST ⟨u,hu,had⟩ t ht hvt).elim
    · exact mem_neighbors_in.mpr ⟨had,hu⟩
  exact hn ((Finset.card_le_card hsub).trans hT)
end DeanK5
end M12
section M13
namespace DeanK5
namespace Cf
open SimpleGraph Finset Cb Fa Fb
variable {V : Type} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {x y : V} {z : Option V} {q : ℕ}
section Graph
variable {A B P : Finset V} {a b c v w : V}
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem route (h : Rc0 G A a b) : ∃ n,Pi0 G A a b n:=by
  classical
  obtain ⟨p,hp⟩:=h
  exact ⟨_,p.bypass,p.bypass_isPath,rfl,fun t ht=>hp t (p.support_bypass_subset_support ht)⟩
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem qi6 (h : Rc0 G A a b) (hne : a≠b) : ∃ c∈A,G.Adj a c:=by
  obtain ⟨p,hp⟩:=h
  cases p with
  | nil=>exact (hne rfl).elim
  | cons h p=>exact ⟨_,hp _ (by simp),h⟩
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem stay (hcl : ∀ a∈P,∀ b∈A,G.Adj a b→ b∈P)
    (ha : a∈P) (h : Rc0 G A a b) : Rc0 G P a b:=by
  obtain ⟨p,hp⟩:=h
  exact ⟨p,qb9 (D:=(·∉A))
    (fun u hu v had=>or_iff_not_imp_right.mpr fun hn=>hcl u hu v (not_not.mp hn) had)
    p ha (fun v hv hn=>hn (hp v hv))⟩
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem qz0 {H : SimpleGraph V} {f : V→ V}
    (h : Rc0 G A a b) (hm : ∀ v∈A,f v∈B)
    (he : ∀ u∈A,∀ v∈A,G.Adj u v→ Rc0 H B (f u) (f v)) :
    Rc0 H B (f a) (f b):=by
  obtain ⟨p,hp⟩:=h
  induction p with
  | nil=>exact Rc0.refl (hm _ (hp _ (by simp)))
  | cons had p ih =>
    exact (he _ (hp _ (by simp)) _ (hp _ (by simp)) had).trans (ih fun v hv=>hp v (by simp [hv]))
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem qai7 {D : Finset V} {m n : ℕ} (h : Pi0 G A a b m)
    (h' : Pi0 G B b c n) (hi : ∀ v∈A,v∈B→ v=b)
    (hA : A⊆D) (hB : B⊆D) : Pi0 G D a c (m+n):=by
  obtain ⟨p,hp,hl,hs⟩:=h
  obtain ⟨r,hr,hl',hs'⟩:=h'
  have hj:=qa3 hp hr fun v hv hv'=>hi v (hs v hv) (hs' v hv')
  refine ⟨p.append r,hj.1,by rw [hj.2.1,hl,hl'],fun v hv=>?_⟩
  rw [Walk.support_append,List.mem_append] at hv
  exact hv.elim (fun hv=>hA (hs v hv)) (fun hv=>hB (hs' v (List.mem_of_mem_tail hv)))
omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
private theorem qah2 {D : Finset V} {n k : ℕ} (h : qan7 G A a b n)
    (r : Pi0 G B b c k) (hi : ∀ v∈A,v∈B→ v=b)
    (hA : A⊆D) (hB : B⊆D) : qan7 G D a c n:=by
  classical
  obtain ⟨l,d,hl,hd,hP⟩:=h
  refine ⟨l+k,d,by omega,hd,fun i=>?_⟩
  exact (qai7 (show Pi0 G A a b (l+i.val*d) from hP i) r hi hA hB).len (by omega)
end Graph
section Blocks
variable {A B P : Finset V} {a b c v w : V}
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qv5 (hc : 2 < B.card) (a b : V) :
    ∃ v∈B,v≠a∧v≠b:=by
  classical
  obtain ⟨v,hv,h⟩:=exists_mem_notMem_of_card_lt_card
    (show ({a,b} : Finset V).card < B.card from (card_insert_le _ _).trans_lt (by simpa using hc))
  exact ⟨v,hv,by simpa using h⟩
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qz9 (hA : Lk0 G A) (hBA : B⊆A) (hb : b∈B) (hc : 2≤ B.card)
    (he : ∀ w∈B,Lk0 G (B.erase w))
    (hcl : ∀ u∈B.erase b,∀ v∈A,G.Adj u v→ v∈B) : Ibo0 G A B:=by
  classical
  have hstay (u : V) (hu : u∈B.erase b) (v : V) (hv : v∈A.erase b) (h : Rc0 G (A.erase b) u v) :
      v∈B.erase b :=
    (stay (fun p hp t ht h=>mem_erase.mpr
      ⟨ne_of_mem_erase ht,hcl p hp t (mem_of_mem_erase ht) h⟩) hu h).right_mem
  refine ⟨hBA,hc,?_,he,fun v hv hvB=>⟨b,hb,fun u hu h=>?_⟩⟩
  · intro u hu v hv
    by_cases h : 2 < B.card
    · obtain ⟨w,hw,hwu,hwv⟩:=qv5 h u v
      exact (he w hw u (mem_erase.mpr ⟨hwu.symm,hu⟩)
        v (mem_erase.mpr ⟨hwv.symm,hv⟩)).mono (erase_subset _ _)
    · obtain ⟨t,ht,htb⟩:=exists_mem_ne (by omega : 1 < B.card) b
      have hBt : B={b,t}:=(eq_of_subset_of_card_le
        (insert_subset hb (singleton_subset_iff.mpr ht))
        (by rw [card_pair htb.symm];omega)).symm
      obtain ⟨r,hr,htr⟩:=qi6 (hA t (hBA ht) b (hBA hb)) htb
      have hrB:=hcl t (mem_erase.mpr ⟨htb,ht⟩) r hr htr
      have hrb : r=b:=((by simpa [hBt] using hrB : r=b∨r=t)).resolve_right htr.ne.symm
      have htb':=Rc0.adj ht hb (hrb ▸ htr)
      exact qa4 b (fun v hv=>by
        have hv' : v=b∨v=t:=by simpa [hBt] using hv
        rcases hv' with rfl|rfl
        · exact Rc0.refl hb
        · exact htb'.symm) u hu v hv
  · exact hvB (mem_of_mem_erase (hstay u
      (mem_erase.mpr ⟨ne_of_mem_erase h.right_mem,hu⟩) v h.left_mem h.symm))
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qz4 (hA : Lk0 G A) (hw : w∈A) (hP : P⊆A.erase w)
    (hne : P.Nonempty) (hcl : ∀ u∈P,∀ v∈A.erase w,G.Adj u v→ v∈P) :
    ∃ B b,Ibo0 G A B∧b∈B∧B⊆insert w P∧B.erase b⊆P ∧
      ∀ u∈B.erase b,∀ v∈A,G.Adj u v→ v∈B:=by
  classical
  let J : SimpleGraph V :=
    { Adj:=fun u v=>G.Adj u v∧u∈A∧v∈A
      symm:=⟨fun _ _ h=>⟨h.1.symm,h.2.2,h.2.1⟩⟩
      loopless:=⟨fun _ h=>G.irrefl h.1⟩ }
  obtain ⟨B,b,hB,hBP,hbP⟩:=qc8 (G:=J) P w
    (fun h=>notMem_erase _ _ (hP h)) hne (fun u hu v hv=>by
      by_cases hvw : v=w
      · exact Or.inr hvw
      · exact Or.inl (hcl u hu v (mem_erase.mpr ⟨hvw,hv.2.2⟩) hv.1))
  have hbA : b∈A:=(mem_insert.mp hbP).elim (· ▸ hw)
    (fun h=>mem_of_mem_erase (hP h))
  have hBA : B⊆A:=fun v hv=>by
    by_cases h : v=b
    · exact h.symm ▸ hbA
    · exact mem_of_mem_erase (hP (hBP (mem_erase.mpr ⟨h,hv⟩)))
  have hC (u : V) (hu : u∈B.erase b) (v : V) (hv : v∈A) (had : G.Adj u v) : v∈B :=
    hB.2.2.1 u (mem_of_mem_erase hu) (ne_of_mem_erase hu) v
      ⟨had,hBA (mem_of_mem_erase hu),hv⟩
  have hBi : B⊆insert w P:=fun v hv=>by
    by_cases h : v=b
    · exact h.symm ▸ hbP
    · exact mem_insert_of_mem (hBP (mem_erase.mpr ⟨h,hv⟩))
  refine ⟨B,b,qz9 hA hBA hB.1 hB.2.1 (fun v hv=>?_) hC,hB.1,hBi,hBP,hC⟩
  rcases hB.2.2.2 with h₂|hK
  · intro u hu t ht
    have hcard:=card_erase_add_one hv
    have e:=card_le_one.mp (by omega : (B.erase v).card≤ 1) u hu t ht
    exact e ▸ Rc0.refl (G:=G) hu
  · intro u hu t ht
    have hmem (u : V) (hu : u∈B.erase v) :
        (⟨u,mem_of_mem_erase hu⟩ : (B : Set V)) ∈
          Finset.univ.erase (⟨v,hv⟩ : (B : Set V)):=by
      apply mem_erase.mpr
      exact ⟨fun h=>ne_of_mem_erase hu (congrArg Subtype.val h),mem_univ _⟩
    exact ((kConn_two_iff.mp hK).2 ⟨v,hv⟩ _ (hmem u hu) _ (hmem t ht)).map
      (⟨Subtype.val,fun h=>h.1⟩ : J.induce (B : Set V) →g G) (fun d hd =>
        mem_erase.mpr ⟨fun e=>ne_of_mem_erase hd (Subtype.ext e),d.2⟩)
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qad7 (hA : Lk0 G A) (hb : b∈A) (hv : v∈A)
    (hout : v∉B.erase b) (hcl : ∀ u∈B.erase b,∀ v∈A,G.Adj u v→ v∈B) :
    Rc0 G (A\B.erase b) b v:=by
  obtain ⟨n,p,hp,_,hps⟩:=route (hA b hb v hv)
  exact ⟨p,fun t ht=>mem_sdiff.mpr ⟨hps t ht,
    qv1 (notMem_erase _ _) hout (fun u hu v hv had=>by
      by_cases e : v=b
      · exact Or.inr e
      · exact Or.inl (mem_erase.mpr ⟨e,hcl u hu v hv had⟩)) hp hps t ht⟩⟩
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qag9 (hA : Lk0 G A) (hB : Ibo0 G A B)
    (hcl : ∀ u∈B.erase b,∀ v∈A,G.Adj u v→ v∈B) :
    ∀ u∈B.erase b,¬ Ici0 G A u:=by
  intro u hu hcut
  obtain ⟨v,hv,hvB,had⟩:=(qa7 hA hB (mem_of_mem_erase hu)).mpr hcut
  exact hvB (hcl u hu v hv had)
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qi0 (hb : b∈B) (hc : 2≤ B.card) : (B.erase b).Nonempty:=by
  have:=card_erase_add_one hb
  exact card_pos.mp (by omega)
end Blocks
section Chain
variable {A B : Finset V} {a b c u v w : V}
omit [Fintype V] [DecidableRel G.Adj] in
private def qx9 (G : SimpleGraph V) (A : Finset V) (a b : V) : Prop :=
  ∀ w∈A,¬ Lk0 G (A.erase w)→ ∀ v∈A.erase w,
    Rc0 G (A.erase w) v a∨Rc0 G (A.erase w) v b
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qx0 (h : qx9 G A a b) (hw : w∈A)
    (hc : ¬ Lk0 G (A.erase w)) : w≠a∧w≠b∧¬ Rc0 G (A.erase w) a b:=by
  have hno {r : V} (hr : ∀ v∈A.erase w,Rc0 G (A.erase w) v r) : False :=
    hc (qa4 r fun v hv=>(hr v hv).symm)
  refine ⟨fun e=>hno (r:=b) (fun v hv=>(h w hw hc v hv).resolve_left
    (fun r=>ne_of_mem_erase r.right_mem e.symm)),fun e=>hno (r:=a) (fun v hv =>
    (h w hw hc v hv).resolve_right (fun r=>ne_of_mem_erase r.right_mem e.symm)),?_⟩
  exact fun r=>hno (r:=a) fun v hv=>(h w hw hc v hv).elim id (fun h=>h.trans r.symm)
private structure Terminal (G : SimpleGraph V) (A : Finset V) (a b : V)
    (B : Finset V) (c : V) : Prop where
  block : Ibo0 G A B
  entry : c∈B
  root : b∈B.erase c
  upstream : a∉B.erase c
  closed : ∀ u∈B.erase c,∀ v∈A,G.Adj u v→ v∈B
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qal4 (hA : Lk0 G A) (ha : a∈A) (hb : b∈A) (hab : a≠b)
    (h : qx9 G A a b) : ∃ B c,Terminal G A a b B c:=by
  classical
  by_cases her : ∀ w∈A,Lk0 G (A.erase w)
  · have hcard:=one_lt_card.mpr ⟨a,ha,b,hb,hab⟩
    exact ⟨A,a,⟨qz9 hA subset_rfl ha (by omega) her
      (fun _ _ _ hv _=>hv),ha,mem_erase.mpr ⟨hab.symm,hb⟩,
      notMem_erase _ _,fun _ _ _ hv _=>hv⟩⟩
  push Not at her
  obtain ⟨w,hw,hc⟩:=her
  obtain ⟨hwa,hwb,hn⟩:=qx0 h hw hc
  obtain ⟨P,hPA,hbP,hcl,hr⟩:=qg2 (G:=G) (A.erase w)
    (mem_erase.mpr ⟨hwb.symm,hb⟩)
  obtain ⟨B,c,hB,hcB,hBP,hi,hC⟩:=qz4 hA hw hPA ⟨b,hbP⟩ hcl
  have haB : a∉B:=fun haB=>(mem_insert.mp (hBP haB)).elim hwa.symm
    (fun haP=>hn (hr a haP).symm)
  obtain ⟨u,hu⟩:=qi0 hcB hB.card
  have huA:=erase_subset_erase _ hB.subset hu
  have hcA:=hB.subset hcB
  have hclose : ∀ u∈B.erase c,∀ v∈A.erase c,G.Adj u v→ v∈B.erase c :=
    fun u hu v hv h=>mem_erase.mpr ⟨ne_of_mem_erase hv,
      hC u hu v (mem_of_mem_erase hv) h⟩
  have hcut : ¬ Lk0 G (A.erase c):=fun hl=>haB (mem_of_mem_erase
    (stay hclose hu (hl u huA a (mem_erase.mpr ⟨fun e=>haB (e.symm ▸ hcB),ha⟩))).right_mem)
  have hreach:=(h c hcA hcut u huA).resolve_left
    (fun r=>haB (mem_of_mem_erase (stay hclose hu r).right_mem))
  exact ⟨B,c,⟨hB,hcB,(stay hclose hu hreach).right_mem,fun h=>haB (mem_of_mem_erase h),hC⟩⟩
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qz3 (hby : b≠y) (hb : b∈A)
    (hleaf : ∀ v∈A,G.Adj y v→ v=b) (hw : w≠b)
    (h : Rc0 G (A.erase w) u v) :
    Rc0 G ((A.erase y).erase w) (if u=y then b else u) (if v=y then b else v):=by
  classical
  let f (v : V):=if v=y then b else v
  have hmem (v : V) (hv : v∈A.erase w) : f v∈(A.erase y).erase w:=by
    by_cases he : v=y
    · exact mem_erase.mpr ⟨by simpa [f,he] using hw.symm,
        by simpa [f,he] using mem_erase.mpr ⟨hby,hb⟩⟩
    · exact mem_erase.mpr ⟨by simpa [f,he] using ne_of_mem_erase hv,
        by simpa [f,he] using mem_erase.mpr ⟨he,mem_of_mem_erase hv⟩⟩
  refine qz0 (f:=f) h hmem ?_
  intro u hu v hv had
  by_cases huy : u=y
  · subst u
    have e:=hleaf v (mem_of_mem_erase hv) had
    exact (show f y=f v by simp [f,e]) ▸ Rc0.refl (G:=G) (hmem y hu)
  by_cases hvy : v=y
  · subst v
    have e:=hleaf u (mem_of_mem_erase hu) had.symm
    exact (show f y=f u by simp [f,e]) ▸ Rc0.refl (G:=G) (hmem y hv)
  exact Rc0.adj (hmem u hu) (hmem v hv) (by simpa [f,huy,hvy] using had)
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qk2 (hby : b≠y) (hb : b∈A)
    (hleaf : ∀ v∈A,G.Adj y v→ v=b) (hu : u≠y) (hv : v≠y)
    (h : Rc0 G (A.erase w) u v) : Rc0 G ((A.erase y).erase w) u v:=by
  classical
  by_cases he : w=b
  · subst w
    exact stay (A:=A.erase b) (P:=(A.erase y).erase b)
      (fun i hi j hj had=>mem_erase.mpr ⟨ne_of_mem_erase hj,mem_erase.mpr
        ⟨fun e=>ne_of_mem_erase hi (hleaf i (mem_of_mem_erase (mem_of_mem_erase hi)) (e ▸ had.symm)),
          mem_of_mem_erase hj⟩⟩)
      (mem_erase.mpr ⟨ne_of_mem_erase h.left_mem,
        mem_erase.mpr ⟨hu,mem_of_mem_erase h.left_mem⟩⟩) h
  · simpa [hu,hv] using qz3 hby hb hleaf he h
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qaj8 (hby : b≠y) (hb : b∈A)
    (hleaf : ∀ v∈A,G.Adj y v→ v=b) (h : qx9 G A a y) (hay : a≠y) :
    qx9 G (A.erase y) a b:=by
  classical
  intro w hw hc
  have hsub : (A.erase y).erase w⊆A.erase w:=erase_subset_erase _ (erase_subset _ _)
  have hc' : ¬ Lk0 G (A.erase w):=fun hl=>hc fun v hv u hu =>
    qk2 hby hb hleaf (ne_of_mem_erase (mem_of_mem_erase hv))
      (ne_of_mem_erase (mem_of_mem_erase hu)) (hl v (hsub hv) u (hsub hu))
  have hall:=h w (mem_of_mem_erase hw) hc'
  have hwb : w≠b:=by
    rintro rfl
    apply hc (qa4 a fun v hv=>?_)
    rcases hall v (hsub hv) with hr|hr
    · exact (qk2 hby hb hleaf (ne_of_mem_erase (mem_of_mem_erase hv)) hay hr).symm
    · obtain ⟨d,hd,had⟩:=qi6 hr.symm (ne_of_mem_erase (mem_of_mem_erase hv)).symm
      exact (ne_of_mem_erase hd (hleaf d (mem_of_mem_erase hd) had)).elim
  intro v hv
  rcases hall v (hsub hv) with hr|hr
  · exact Or.inl (qk2 hby hb hleaf (ne_of_mem_erase (mem_of_mem_erase hv)) hay hr)
  · exact Or.inr (by
      simpa [ne_of_mem_erase (mem_of_mem_erase hv)] using qz3 hby hb hleaf hwb hr)
omit [Fintype V] [DecidableRel G.Adj] in
private theorem qab9 (hby : b≠y) (hb : b∈B) (hB : Ibo0 G (A.erase y) B)
    (hleaf : ∀ v∈A,G.Adj y v→ v=b) : Ibo0 G A B:=by
  refine ⟨hB.subset.trans (erase_subset _ _),hB.card,hB.linked,hB.erase_linked,?_⟩
  have hbA:=mem_of_mem_erase (hB.subset hb)
  intro v hv hvB
  by_cases h : v=y
  · subst v
    refine ⟨b,hb,fun u hu r=>?_⟩
    obtain ⟨d,hd,had⟩:=qi6 r (ne_of_mem_erase (hB.subset hu)).symm
    exact ne_of_mem_erase hd (hleaf d (mem_of_mem_erase hd) had)
  · obtain ⟨w,hw,hs⟩:=hB.separates v (mem_erase.mpr ⟨h,hv⟩) hvB
    exact ⟨w,hw,fun u hu r=>hs u hu
      (qk2 hby hbA hleaf h (ne_of_mem_erase (hB.subset hu)) r)⟩
end Chain
section Counterexample
variable (ih : Cb0 (Fintype.card V+G.edgeFinset.card))
    (hH : Ch0 G x y z q) (hq : q≤ 4) (hf : ¬ Adm0 G x y q)
    (W : Wc0 G x y z)
include W
private theorem qj1 {v : V} (hv : v∈W.C) : v≠x :=
  fun e=>qa1 W hv (e.symm ▸ W.core.x_mem_verts)
private theorem qaj5 (hk : W.core.kind=.t3) : W.base.kind=.t3:=by
  have h:=W.h_mode
  cases he : W.isFlat with
  | none=>rw [he] at h;exact h.1 ▸ hk
  | some t=>rw [he] at h;exact h.1.1
include ih hH hq hf in
private theorem qi1 {B : Finset V} {b s : V} (hs : W.core.S={s})
    (hB : Fb0 G W.C y z B b) :
    (∀ u∈B.erase b,∀ t∈W.core.T,¬ G.Adj u t) ∧
    (∃ u∈B.erase b,G.Adj u x)∧(∃ u∈B.erase b,G.Adj u s):=by
  classical
  obtain ⟨hT,-,hc⟩:=qa6 ih hH hq hf W hB
  let K:=qc5 G B (insert x W.core.S) b
  have hK : K=insert x W.core.S :=
    eq_of_subset_of_card_le (filter_subset _ _) (by
      rw [hs]
      exact (card_insert_le x {s}).trans (by simpa using hc))
  exact ⟨hT,(mem_filter.mp (hK.symm ▸ mem_insert_self x W.core.S : x∈K)).2,
    (mem_filter.mp (hK.symm ▸ mem_insert_of_mem
      (hs.symm ▸ mem_singleton_self s) : s∈K)).2⟩
include hH in
private theorem qk9 {v : V} (hv : v∈W.C) (hy : v≠y) (hz : z≠some v) :
    q+1≤ G.degree v :=
  hH.2.2.2 v (qj1 W hv) hy hz
include ih hH hq hf in
private theorem qam4 {s zv : V} (hs : W.core.S={s}) (hk : W.core.kind=.t3)
    (hz : z=some zv) (hzC : zv∈W.C) (hzy : zv≠y) :
    ∃ v∈W.C.erase y,∃ t∈W.core.T,G.Adj v t:=by
  classical
  by_contra hn
  let D:=W.C.erase y
  let A:=Dᶜ
  let H:=G ⊔ edge x y
  have hcore : W.core.verts⊆A:=fun v hv =>
    mem_compl.mpr fun h=>qa1 W (mem_of_mem_erase h) hv
  have hx:=hcore W.core.x_mem_verts
  have hy : y∈A:=mem_compl.mpr (notMem_erase _ _)
  have hsS : s∈W.core.S:=hs.symm ▸ mem_singleton_self s
  have hS:=hcore (W.core.S_subset_verts hsS)
  have hout : ∀ a∈D,∀ b,G.Adj a b→ b∉D→ b=x∨b=y∨b=s:=by
    intro a ha b hab hb
    rcases qh9 W (mem_of_mem_erase ha) hab with hbC|hbK
    · exact Or.inr (Or.inl (by simpa [D,hbC] using hb))
    · rw [Cc0.mem_verts,hs,mem_singleton] at hbK
      rcases hbK with h|h|h
      · exact Or.inl h
      · exact Or.inr (Or.inr h)
      · exact (hn ⟨a,ha,b,h,hab⟩).elim
  obtain ⟨v,hv,t,ht,hvt⟩:=qp5 ih hH hq hf W (by simp [hs])
  have hyt : G.Adj y t:=by
    by_cases he : v=y
    · exact he ▸ hvt
    · exact (hn ⟨v,mem_erase.mpr ⟨he,hv⟩,t,ht,hvt⟩).elim
  have hT : W.core.T⊆A:=fun _ ht=>hcore (W.core.T_subset_verts ht)
  have htS : ∀ t∈W.core.T,t≠s:=fun t ht e =>
    disjoint_left.mp W.core.disj hsS (e ▸ ht)
  have htY : ∀ t∈W.core.T,t≠y:=fun _ ht e=>W.core.y_notMem_T (e ▸ ht)
  have htX : ∀ t∈W.core.T,t≠x:=fun _ ht e=>W.core.x_notMem_T (e ▸ ht)
  have hc : 2 < A.card:=by
    have h:=card_le_card (insert_subset hx hT)
    rw [card_insert_of_notMem W.core.x_notMem_T] at h
    have:=W.core.two_le_T
    omega
  have hlinked (w : V) (_ : w∈A) : Lk0 H (A.erase w):=by
    let r:=if x=w then y else x
    have hr : r∈A.erase w:=by
      by_cases e : x=w
      · simpa [r,e] using (mem_erase.mpr ⟨fun h=>W.core.x_ne_y (e.trans h.symm),hy⟩ : y∈A.erase w)
      · simp [r,e,hx]
    have hgate (b : V) (hb : b∈A.erase w) (he : b=x∨b=y∨b=s) :
        Rc0 H (A.erase w) r b:=by
      rcases he with rfl|rfl|rfl
      · have e:=ne_of_mem_erase hb
        simpa [r,e] using (Rc0.refl (G:=H) hb)
      · by_cases e : x=w
        · simpa [r,e] using (Rc0.refl (G:=H) hb)
        · exact Rc0.adj (by simpa [r,e] using hr) hb
            (by simp [H,r,e,edge_adj,W.core.x_ne_y])
      · by_cases e : x=w
        · have htt : t∈A.erase w:=mem_erase.mpr ⟨by simpa [← e] using htX t ht,hT ht⟩
          exact (Rc0.adj hr htt (by simpa [r,e,H] using (Or.inl hyt :
            G.Adj y t∨(edge x y).Adj y t))).trans
            (Rc0.adj htt hb (Or.inl ((W.core.shape3 hk).2.2.2.2.2 b hsS t ht).symm))
        · obtain ⟨u,hu,huw⟩:=exists_mem_ne
            (by have:=W.core.two_le_T;omega : 1 < W.core.T.card) w
          have hu':=mem_erase.mpr ⟨huw,hT hu⟩
          exact (Rc0.adj hr hu' (by simpa [r,e,H] using (Or.inl
            ((W.core.shape3 hk).2.2.1 u hu) : G.Adj x u∨(edge x y).Adj x u))).trans
            (Rc0.adj hu' hb (Or.inl ((W.core.shape3 hk).2.2.2.2.2 b hsS u hu).symm))
    let f (v : V):=if v∈D then r else v
    have hkeep (v : V) (hv : v∈Finset.univ.erase w) (h : v∉D) : v∈A.erase w :=
      mem_erase.mpr ⟨ne_of_mem_erase hv,mem_compl.mpr h⟩
    intro a ha b hb
    have hab:=(kConn_two_iff.mp W.hK).2 w a (by simp [ne_of_mem_erase ha])
      b (by simp [ne_of_mem_erase hb])
    have h:=qz0 (H:=H) (B:=A.erase w) (f:=f) hab
      (fun v hv=>by
        by_cases h : v∈D
        · simpa [f,h] using hr
        · simpa [f,h] using hkeep v hv h)
      (fun u hu v hv huv=>by
        by_cases h₁ : u∈D <;> by_cases h₂ : v∈D
        · simpa [f,h₁,h₂] using (Rc0.refl (G:=H) hr)
        · simpa [f,h₁,h₂] using hgate v (hkeep v hv h₂) (hout u h₁ v huv h₂)
        · simpa [f,h₁,h₂] using (hgate u (hkeep u hu h₁) (hout v h₂ u huv.symm h₁)).symm
        · simpa [f,h₁,h₂] using Rc0.adj (G:=H) (hkeep u hu h₁) (hkeep v hv h₂) (Or.inl huv))
    simpa [f,mem_compl.mp (mem_of_mem_erase ha),
      mem_compl.mp (mem_of_mem_erase hb)] using h
  have hzD : zv∈D:=mem_erase.mpr ⟨hzy,hzC⟩
  have hm:=card_lt_of_notMem (s:=A) (notMem_compl.mpr hzD)
  apply hf (qm2 (induce_call (ih.toAt hq) A hx hy (some s) hH.1
    (qb4 W.core.x_ne_y hc hlinked hx hy) (by omega) ?_
    ⟨t,hT ht,htX t ht,htY t ht,by simpa using (htS t ht).symm⟩))
  intro u hu hux huy hus
  have hus' : u≠s:=fun e=>hus (congrArg some e.symm)
  have huz : z≠some u:=fun e=>mem_compl.mp hu ((Option.some.inj (hz.symm.trans e)) ▸ hzD)
  refine ⟨hH.2.2.2 u hux huy huz,fun v huv=>mem_compl.mpr fun hv=>?_⟩
  rcases hout v hv u huv.symm (mem_compl.mp hu) with h|h|h
  exacts [hux h,huy h,hus' h]
omit W [Fintype V] [DecidableRel G.Adj] in
private theorem qag7 {A : Finset V} {r b : V} (hr : r∉A) (hb : b∈A)
    (hc : 2≤ A.card) (hl : Lk0 G A) (her : ∀ w∈A,Lk0 G (A.erase w))
    (ha : ∃ u∈A.erase b,G.Adj u r) :
    Rt0 (G.induce (↑(insert r A) : Set V))
      ⟨r,mem_insert_self _ _⟩ ⟨b,mem_insert_of_mem hb⟩:=by
  classical
  refine qb4 (s:=insert r A) (x:=r) (y:=b) (fun e=>hr (e.symm ▸ hb))
    (by rw [card_insert_of_notMem hr];omega) (fun w hw=>?_) _ _
  by_cases he : w=r
  · subst w
    simpa [erase_insert hr] using hl.mono_graph (H:=G ⊔ edge r b) le_sup_left
  have hwA:=(mem_insert.mp hw).resolve_left he
  have hD:=(her w hwA).mono_graph (H:=G ⊔ edge r b) le_sup_left
  rw [erase_insert_of_ne (Ne.symm he)]
  by_cases hwb : w=b
  · subst w
    obtain ⟨u,hu,had⟩:=ha
    exact qe6 hD hu (Or.inl had.symm)
  · exact qe6 hD (mem_erase.mpr ⟨Ne.symm hwb,hb⟩)
      (Or.inr (by simp [edge_adj,show r≠b from fun e=>hr (e.symm ▸ hb)]))
include ih hH hq hf in
private theorem qam3 {B : Finset V} {b s : V} (hs : W.core.S={s})
    (hB : Fb0 G W.C y z B b)
    (hclosed : ∀ u∈B.erase b,¬ Ici0 G W.C u)
    (hy : y∉B.erase b) (hz : ∀ u∈B.erase b,z≠some u) : False:=by
  classical
  obtain ⟨hT,hxA,hsA⟩:=qi1 ih hH hq hf W hs hB
  have hq3:=qb6 ih hH hq hf
  have hsS : s∈W.core.S:=hs.symm ▸ mem_singleton_self s
  have hnv (u : V) (hu : u∈B.erase b) (v : V) (had : G.Adj u v) :
      v∈B∨v=x∨v=s:=by
    rcases qh9 W (hB.block.subset (mem_of_mem_erase hu)) had with hv|hv
    · exact Or.inl (by
        by_contra hn
        exact hclosed u hu ((qa7 (linked W) hB.block
          (mem_of_mem_erase hu)).mp ⟨v,hv,hn,had⟩))
    · rw [Cc0.mem_verts,hs,mem_singleton] at hv
      exact Or.inr (hv.imp_right (fun h=>h.resolve_right fun ht=>hT u hu v ht had))
  have hdeg (u : V) (hu : u∈B.erase b) : q+1≤ G.degree u :=
    qk9 hH W (hB.block.subset (mem_of_mem_erase hu)) (fun e=>hy (e ▸ hu)) (hz u hu)
  have hxB : x∉B:=fun h=>qa1 W (hB.block.subset h) W.core.x_mem_verts
  have hsB : s∉B:=fun h=>qa1 W (hB.block.subset h) (W.core.S_subset_verts hsS)
  obtain ⟨u,hu,hux⟩:=hxA
  have h3 : 2 < B.card:=by
    have hsub : G.neighborFinset u⊆insert x (insert s (B.erase u)):=by
      intro v hv
      have had:=(G.mem_neighborFinset _ _).mp hv
      rcases hnv u hu v had with h|rfl|rfl
      · exact mem_insert_of_mem (mem_insert_of_mem (mem_erase.mpr ⟨had.ne.symm,h⟩))
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_insert_self _ _)
    have hc:=card_le_card hsub
    rw [card_neighborFinset_eq_degree] at hc
    have h₁:=card_insert_le x (insert s (B.erase u))
    have h₂:=card_insert_le s (B.erase u)
    have h₃:=card_erase_add_one (mem_of_mem_erase hu)
    have:=hdeg u hu
    omega
  obtain ⟨t,ht⟩:=card_pos.mp (show 0 < W.core.T.card by have:=W.core.two_le_T;omega)
  have hxne : x≠s:=fun e=>W.core.x_notMem_S (e ▸ hsS)
  have htX : t≠x:=fun e=>W.core.x_notMem_T (e ▸ ht)
  have htS : t≠s:=fun e=>disjoint_left.mp W.core.disj hsS (e ▸ ht)
  have htB : t∉B:=fun h=>qa1 W (hB.block.subset h) (W.core.T_subset_verts ht)
  obtain ⟨n,p,hp,-,hps⟩:=route hB.exit_reach
  have finish (A : Finset V) (hBA : B⊆A) (hA : A⊆insert s B)
      (hAl : Lk0 G A) (hAe : ∀ w∈A,Lk0 G (A.erase w)) (e : Option V)
      (hdeg' : ∀ u∈insert x A,u≠x→ u≠b→ e≠some u →
        q+1≤ G.degree u∧∀ v,G.Adj u v→ v∈insert x A)
      (hw : ∃ u∈B.erase b,e≠some u) : False:=by
    have hxA' : x∉A:=fun h=>(mem_insert.mp (hA h)).elim hxne hxB
    have hc : 2≤ A.card:=hB.block.card.trans (card_le_card hBA)
    have hxE : ∃ u∈A.erase b,G.Adj u x:=by
      exact ⟨u,erase_subset_erase _ hBA hu,hux⟩
    have hm : (insert x A).card < Fintype.card V:=card_lt_of_notMem (fun h =>
      (mem_insert.mp h).elim htX (fun h=>(mem_insert.mp (hA h)).elim htS htB))
    obtain ⟨v,hv,hve⟩:=hw
    have hP:=induce_call (ih.toAt hq) (insert x A) (mem_insert_self _ _)
      (mem_insert_of_mem (hBA hB.exit_mem)) e hH.1
      (qag7 hxA' (hBA hB.exit_mem) hc hAl hAe hxE) (by omega) hdeg'
      ⟨v,mem_insert_of_mem (hBA (mem_of_mem_erase hv)),
        qj1 W (hB.block.subset (mem_of_mem_erase hv)),
        ne_of_mem_erase hv,hve⟩
    exact hf (qr4 hP p hp fun v hv hvi=>by
      have hh:=mem_sdiff.mp (hps v hv)
      rcases mem_insert.mp hvi with rfl|hvA
      · exact (qa1 W hh.1 W.core.x_mem_verts).elim
      · rcases mem_insert.mp (hA hvA) with rfl|hvB
        · exact (qa1 W hh.1 (W.core.S_subset_verts hsS)).elim
        · exact not_not.mp (fun h=>hh.2 (mem_erase.mpr ⟨h,hvB⟩)))
  by_cases hS : 2≤ (G.neighborFinset s∩B).card
  · have hAl : Lk0 G (insert s B):=by
      obtain ⟨u,hu,had⟩:=hsA
      exact qe6 hB.block.linked (mem_of_mem_erase hu) had.symm
    have hAe : ∀ w∈insert s B,Lk0 G ((insert s B).erase w):=by
      intro w hw
      by_cases he : w=s
      · subst w
        simpa [erase_insert hsB] using hB.block.linked
      · have hwB:=(mem_insert.mp hw).resolve_left he
        obtain ⟨v,hv,hvw⟩:=exists_mem_ne (by omega :
          1 < (G.neighborFinset s∩B).card) w
        obtain ⟨had,hvB⟩:=mem_neighbors_in.mp hv
        rw [erase_insert_of_ne (Ne.symm he)]
        exact qe6 (hB.block.erase_linked w hwB) (mem_erase.mpr ⟨hvw,hvB⟩) had
    refine finish (insert s B) (subset_insert _ _) subset_rfl hAl hAe (some s) ?_
      ⟨u,hu,by simpa using (qa0 (mem_of_mem_erase hu) hsB).symm⟩
    intro v hv hvx hvb hvs
    have hvB:=(mem_insert.mp ((mem_insert.mp hv).resolve_left hvx)).resolve_left
      (fun e=>hvs (congrArg some e.symm))
    have hv':=mem_erase.mpr ⟨hvb,hvB⟩
    exact ⟨hdeg v hv',fun w had=>by
      rcases hnv v hv' w had with h|rfl|rfl
      · exact mem_insert_of_mem (mem_insert_of_mem h)
      · exact mem_insert_self _ _
      · exact mem_insert_of_mem (mem_insert_self _ _)⟩
  · obtain ⟨v,hv,hva⟩:=hsA
    have hvN:=mem_neighbors_in.mpr ⟨hva.symm,mem_of_mem_erase hv⟩
    have hc:=card_erase_add_one hB.exit_mem
    obtain ⟨w,hw,hwv⟩:=exists_mem_ne (by omega : 1 < (B.erase b).card) v
    refine finish B subset_rfl (subset_insert _ _) hB.block.linked hB.block.erase_linked
      (some v) ?_ ⟨w,hw,by simpa using hwv.symm⟩
    intro a ha hax hab hav
    have haB:=(mem_insert.mp ha).resolve_left hax
    have ha':=mem_erase.mpr ⟨hab,haB⟩
    refine ⟨hdeg a ha',fun w had=>?_⟩
    rcases hnv a ha' w had with h|rfl|he
    · exact mem_insert_of_mem h
    · exact mem_insert_self _ _
    · subst w
      exact (hav (congrArg some (card_le_one.mp (by omega :
        (G.neighborFinset s∩B).card≤ 1) v hvN a (mem_neighbors_in.mpr ⟨had.symm,haB⟩)))).elim
include ih hH hq hf in
private theorem qad4 {s : V} (hs : W.core.S={s}) (hk : W.core.kind=.t3) :
    ∃ v∈W.C,z=some v∧v≠y∧qx9 G W.C v y:=by
  classical
  have hy:=qc2 W
  have hL:=linked W
  obtain ⟨u,hu,huy,huz⟩:=W.hC_nontriv
  have hC : 2≤ W.C.card:=one_lt_card.mpr ⟨u,hu,y,hy,huy⟩
  have hcut : ∃ w∈W.C,¬ Lk0 G (W.C.erase w):=by
    by_contra hn
    push Not at hn
    have hB : Fb0 G W.C y z W.C y :=
      ⟨⟨subset_rfl,hC,hL,hn,fun _ hv hn=>(hn hv).elim⟩,hy,
       Rc0.refl (mem_sdiff.mpr ⟨hy,notMem_erase _ _⟩),
       z,fun v hv hm=>(hm.resolve_left (fun h=>h.2 (hn v h.1))).resolve_left (ne_of_mem_erase hv),
       u,mem_erase.mpr ⟨huy,hu⟩,huz⟩
    by_cases hz : ∃ v∈W.C.erase y,z=some v
    · obtain ⟨v,hv,hz⟩:=hz
      obtain ⟨w,hw,t,ht,had⟩:=qam4 ih hH hq hf W hs hk hz
        (mem_of_mem_erase hv) (ne_of_mem_erase hv)
      exact (qi1 ih hH hq hf W hs hB).1 w hw t ht had
    · exact qam3 ih hH hq hf W hs hB (fun v _ h=>h.2 (hn v h.1))
        (notMem_erase _ _) (fun v hv e=>hz ⟨v,hv,e⟩)
  have hcover (w : V) (hw : w∈W.C) (a : V) (ha : a∈W.C.erase w) :
      Rc0 G (W.C.erase w) a y∨∃ v,z=some v∧Rc0 G (W.C.erase w) a v:=by
    by_contra hn
    obtain ⟨P,hP,haP,hcl,hr⟩:=qg2 (G:=G) _ ha
    obtain ⟨B,b,hB,hb,_,hi,hclose⟩:=qz4 hL hw hP ⟨a,haP⟩ hcl
    have hyB : y∉B.erase b:=fun hy=>hn (Or.inl (hr y (hi hy)))
    have hzB : ∀ v∈B.erase b,z≠some v :=
      fun v hv e=>hn (Or.inr ⟨v,e,hr v (hi hv)⟩)
    have hncut:=qag9 hL hB hclose
    obtain ⟨v,hv⟩:=qi0 hb hB.card
    have hF : Fb0 G W.C y z B b :=
      ⟨hB,hb,qad7 hL (hB.subset hb) hy hyB hclose,none,
        fun u hu e=>(e.elim (hncut u hu) (fun e =>
          e.elim (fun e=>hyB (e ▸ hu)) (hzB u hu))).elim,v,hv,by simp⟩
    exact qam3 ih hH hq hf W hs hF hncut hyB hzB
  obtain ⟨w,hw,hbad⟩:=hcut
  have hreach : ∃ a∈W.C.erase w,¬ Rc0 G (W.C.erase w) a y:=by
    by_contra! hn
    exact hbad (qa4 y fun a ha=>(hn a ha).symm)
  obtain ⟨a,ha,hn⟩:=hreach
  obtain ⟨v,hz,hv⟩:=(hcover w hw a ha).resolve_left hn
  refine ⟨v,mem_of_mem_erase hv.right_mem,hz,fun e=>?_,?_⟩
  · exact hn (e ▸ hv)
  · intro c hc _ u hu
    rcases hcover c hc u hu with hr|⟨v',hz',hr⟩
    · exact Or.inr hr
    · exact Or.inl ((Option.some.inj (hz'.symm.trans hz)) ▸ hr)
omit W in
private theorem qac7 {B : Finset V} (u : ↥(B : Set V)) :
    (G.induce (B : Set V)).degree u=(G.neighborFinset u.1∩B).card:=by
  classical
  rw [← card_neighborFinset_eq_degree]
  refine card_bij (fun v _=>v.1) (fun v hv=>?_) (fun _ _ _ _ h=>Subtype.ext h) ?_
  · exact mem_neighbors_in.mpr ⟨((G.induce (B : Set V)).mem_neighborFinset u v).mp hv,v.2⟩
  · intro v hv
    obtain ⟨h,hvB⟩:=mem_neighbors_in.mp hv
    exact ⟨⟨v,hvB⟩,((G.induce (B : Set V)).mem_neighborFinset u _).mpr h,rfl⟩
include ih hH hq hf in
private theorem qaq4 {A B : Finset V} {a b v t : V} {k : ℕ}
    (hk : W.core.kind=.t3) (hell : W.core.ell=1)
    (hA : A⊆W.C) (hyA : y∈A→ y=b)
    (hB : Ibo0 G W.C B) (hc : 2 < B.card)
    (ha : a∈B) (hb : b∈B) (hab : a≠b)
    (hord : ∀ u∈B,u≠a→ u≠b→ u≠y∧z≠some u∧¬ Ici0 G W.C u)
    (hS : Pi0 G ({b,y} : Finset V) b y k) (hyB : y∈B→ y=b)
    (hR : Rc0 G (A\B.erase a) v a) (ht : t∈W.core.T) (hvt : G.Adj v t) : False:=by
  classical
  let I:=G.induce (B : Set V)
  let a' : ↥(B : Set V):=⟨a,ha⟩
  let b' : ↥(B : Set V):=⟨b,hb⟩
  have hroot : Rt0 I a' b':=qb4 hab hc
    (fun w hw=>(hB.erase_linked w hw).mono_graph le_sup_left) ha hb
  obtain ⟨w,hw,hwa,hwb⟩:=qv5 hc a b
  have hcard : Fintype.card ↥(B : Set V)=B.card:=by simp
  have hm : B.card < Fintype.card V:=card_lt_of_notMem
    (fun hx=>qa1 W (hB.subset hx) W.core.x_mem_verts)
  have he:=qh0 (G:=G) (H:=I) Subtype.val Subtype.val_injective (fun _ _ h=>h)
  have hq3:=qb6 ih hH hq hf
  have hd:=(qd7 ih hH hq hf W).2
  have hI : Ch0 I a' b' none (q - 1):=by
    refine ⟨by omega,hroot,⟨⟨w,hw⟩,fun e=>hwa (congrArg Subtype.val e),
      fun e=>hwb (congrArg Subtype.val e),by simp⟩,?_⟩
    intro u hua hub _
    obtain ⟨huy,huz,hcut⟩:=hord u.1 u.2 (fun e=>hua (Subtype.ext e)) (fun e=>hub (Subtype.ext e))
    have hsub : G.neighborFinset u.1∩W.C⊆G.neighborFinset u.1∩B:=by
      intro p hp
      obtain ⟨had,hpC⟩:=mem_neighbors_in.mp hp
      exact mem_neighbors_in.mpr ⟨had,by
        by_contra hn
        exact hcut ((qa7 (linked W) hB u.2).mp ⟨p,hpC,hn,had⟩)⟩
    have hc':=card_le_card hsub
    have hdeg:=qk9 hH W (hB.subset u.2) huy huz
    have hsplit:=qj4 W (hB.subset u.2)
    have hExt:=hd u.1 (hB.subset u.2) huy huz hcut
    rw [qac7]
    omega
  obtain ⟨l,d,hl,hstep,hP⟩:=ih _ I a' b' none (q - 1) (by omega) (by rw [hcard];omega) hI
  have hFam : qan7 G B a b (q - 1):=⟨l,d,hl,hstep,fun i=>by
    obtain ⟨p,hp,hpl⟩:=hP i
    obtain ⟨p',hp',hl',-,hs⟩:=qd3 (G:=G) (B : Set V) hp
    exact ⟨p',hp',hl'.trans hpl,fun u hu=>hs u hu⟩⟩
  have hFam':=qah2 hFam hS
    (fun u hu hu'=>by
      rcases mem_insert.mp hu' with h|h
      · exact h
      · have e:=mem_singleton.mp h
        exact e.trans (hyB (e ▸ hu)))
    (subset_insert y B) (insert_subset (mem_insert_of_mem hb)
      (singleton_subset_iff.mpr (mem_insert_self _ _)))
  obtain ⟨l',d',hl',hstep',hQ⟩:=hFam'
  obtain ⟨n,hn⟩:=route hR
  have htn : t∉A\B.erase a:=fun h =>
    qa1 W (hA (mem_sdiff.mp h).1) (W.core.T_subset_verts ht)
  have htPath:=hn.cons hvt.symm htn
  let U:=W.core.verts∪(A\B.erase a)
  let D:=(insert y B).erase a
  have hdis : Disjoint U D:=disjoint_left.mpr fun u hu hd=>by
    have hD:=mem_of_mem_erase hd
    rcases mem_union.mp hu with h|h
    · exact qa1 W ((mem_insert.mp hD).elim (· ▸ qc2 W) (fun h=>hB.subset h)) h
    · have h':=mem_sdiff.mp h
      have huB:=(mem_insert.mp hD).elim (fun e=>(e.trans (hyA (e ▸ h'.1))).symm ▸ hb) id
      exact h'.2 (mem_erase.mpr ⟨ne_of_mem_erase hd,huB⟩)
  have hCore (i : Fin 2) : Pi0 G U x a (1+(n+1)+i.val*2):=by
    have hi:=ql5 W.core hk ht (Fin.cast (by omega : 2=W.core.ell+1) i)
    have hi' : Pi0 G W.core.verts x t (1+2*i.val):=by simpa using hi
    refine (qai7 hi' htPath (fun u hu hu'=>(mem_insert.mp hu').resolve_right fun h =>
      qa1 W (hA (mem_sdiff.mp h).1) hu) subset_union_left ?_).len (by omega)
    exact insert_subset (mem_union_left _ (W.core.T_subset_verts ht)) subset_union_right
  apply hf
  have hjoin : Adm0 G x y (2+(q - 1) - 1):=qae9 (G:=G) (x:=x) (y:=y) (p:=2) (n:=q - 1)
    (a:=1+(n+1)) (d:=2) (b:=l') (e:=d') (by omega) (by omega)
    (by omega) (Or.inr rfl) hstep' (fun i=>⟨a,by
      rw [show insert a D=insert y B from insert_erase (mem_insert_of_mem ha)]
      exact hQ i,hCore⟩) hdis
  exact qc0 (by omega) hjoin
include ih hH hq hf in
private theorem qs2 {s : V} {A B : Finset V} {zv a b : V} {k : ℕ}
    (hs : W.core.S={s}) (hk : W.core.kind=.t3) (hell : W.core.ell=1)
    (hz : z=some zv) (hAs : A⊆W.C) (hAl : Lk0 G A) (hyA : y∈A→ y=b)
    (hcl : ∀ u∈A,u≠b→ ∀ v∈W.C,G.Adj u v→ v∈A)
    (hB : Terminal G A zv b B a) (hBC : Ibo0 G W.C B) (hc : 2 < B.card)
    (hpath : Pi0 G ({b,y} : Finset V) b y k) :
    ∀ v∈A.erase b,∀ t∈W.core.T,¬ G.Adj v t:=by
  classical
  have hb:=mem_of_mem_erase hB.root
  have hba:=ne_of_mem_erase hB.root
  have hyB : y∈B→ y=b:=fun h=>hyA (hB.block.subset h)
  have hord (u : V) (hu : u∈B) (hua : u≠a) (hub : u≠b) :
      u≠y∧z≠some u∧¬ Ici0 G W.C u:=by
    refine ⟨fun h=>hub (h.trans (hyB (h ▸ hu))),fun h=>?_,fun h=>?_⟩
    · exact hB.upstream ((Option.some.inj (h.symm.trans hz)) ▸ mem_erase.mpr ⟨hua,hu⟩)
    · obtain ⟨v,hv,hvB,had⟩:=(qa7 (linked W) hBC hu).mpr h
      exact hvB (hB.closed u (mem_erase.mpr ⟨hua,hu⟩) v (hcl u (hB.block.subset hu) hub v hv had) had)
  obtain ⟨u,hu,hua,hub⟩:=qv5 hc a b
  have hFB : Fb0 G W.C y z B b:=by
    refine ⟨hBC,hb,?_,some a,fun v hv hm=>?_,u,mem_erase.mpr ⟨hub,hu⟩,
      fun e=>hua (Option.some.inj e).symm⟩
    · obtain ⟨p,-,-,hp⟩:=hpath
      refine ⟨p,fun v hv=>?_⟩
      rcases mem_insert.mp (hp v hv) with rfl|h
      · exact mem_sdiff.mpr ⟨hBC.subset hb,notMem_erase _ _⟩
      · obtain rfl:=mem_singleton.mp h
        exact mem_sdiff.mpr ⟨qc2 W,fun h =>
          ne_of_mem_erase h (hyB (mem_of_mem_erase h))⟩
    · by_cases e : v=a
      · exact congrArg some e.symm
      · obtain ⟨hy,hz,hc⟩:=hord v (mem_of_mem_erase hv) e (ne_of_mem_erase hv)
        exact (hm.elim hc (fun h=>h.elim hy hz)).elim
  intro v hv t ht had
  by_cases hvB : v∈B
  · exact (qi1 ih hH hq hf W hs hFB).1 v
      (mem_erase.mpr ⟨ne_of_mem_erase hv,hvB⟩) t ht had
  · exact qaq4 ih hH hq hf W hk hell hAs hyA hBC hc hB.entry hb hba.symm hord hpath hyB
      (qad7 hAl (hB.block.subset hB.entry) (mem_of_mem_erase hv)
        (fun h=>hvB (mem_of_mem_erase h)) hB.closed).symm ht had
omit W [Fintype V] [DecidableRel G.Adj] in
private theorem qp7 {A B : Finset V} {zv a b : V} (hB : Terminal G A zv b B a)
    (hc : B.card≤ 2) : G.Adj b a∧∀ v∈A,G.Adj b v→ v=a:=by
  have hb:=mem_of_mem_erase hB.root
  have hba:=ne_of_mem_erase hB.root
  have hEq : B={a,b}:=(eq_of_subset_of_card_le
    (insert_subset hB.entry (singleton_subset_iff.mpr hb))
    (by rw [card_pair hba.symm];exact hc)).symm
  have h (v : V) (hv : v∈B) (had : G.Adj b v) : v=a :=
    (show v=a∨v=b by simpa [hEq] using hv).resolve_right had.ne.symm
  obtain ⟨v,hv,had⟩:=qi6 (hB.block.linked b hb a hB.entry) hba
  exact ⟨h v hv had ▸ had,fun v hv had=>h v (hB.closed b hB.root v hv had) had⟩
omit W [Fintype V] [DecidableRel G.Adj] in
private theorem qm0 {A B : Finset V} {b c : V} (hB : Ibo0 G A B)
    (hb : b∈B) (h : ∀ v∈B,G.Adj b v→ v=c) : B.card≤ 2:=by
  by_contra! hcard
  obtain ⟨v,hv,hvb,hvc⟩:=qv5 hcard b c
  obtain ⟨w,hw,hbw⟩:=qi6 (hB.linked b hb v hv) hvb.symm
  have hwc:=h w hw hbw
  have hc : c∈B:=hwc ▸ hw
  obtain ⟨d,hd,hbd⟩:=qi6
    (hB.erase_linked c hc b (mem_erase.mpr ⟨hwc ▸ hbw.ne,hb⟩)
      v (mem_erase.mpr ⟨hvc,hv⟩)) hvb.symm
  exact ne_of_mem_erase hd (h d (mem_of_mem_erase hd) hbd)
include ih hH hq hf in
private theorem qt0 : False:=by
  classical
  obtain ⟨hk,hell⟩:=qc6 ih hH hq hf W
  obtain ⟨s,hs⟩:=(qd7 ih hH hq hf W).1
  obtain ⟨zv,hzC,hz,hzy,hchain⟩:=qad4 ih hH hq hf W hs hk
  have hT:=qam4 ih hH hq hf W hs hk hz hzC hzy
  obtain ⟨B₁,b,hB₁⟩:=qal4 (linked W) hzC (qc2 W) hzy hchain
  by_cases h₁ : 2 < B₁.card
  · obtain ⟨v,hv,t,ht,had⟩:=hT
    exact qs2 ih hH hq hf W hs hk hell hz subset_rfl (linked W)
      (fun _=>rfl) (fun _ _ _ _ h _=>h) hB₁ hB₁.block h₁
      (Pi0.nil (mem_insert_self _ _)) v hv t ht had
  obtain ⟨hyb,hleaf⟩:=qp7 hB₁ (by omega)
  have hbC:=hB₁.block.subset hB₁.entry
  have hby:=hyb.ne.symm
  have hbz : b≠zv:=fun e=>qd5 ih hH hq hf zv hz
    (qj1 W hzC) hzy (e ▸ hyb)
  have hnxy:=qb3 ih hH hq hf
  have hrank (J : Cc0 G y x) : 3≤ J.kind.rank:=by
    have h:=W.hopt.2.1 J
    simpa [qaj5 W hk,Ck0.rank] using h
  obtain ⟨J⟩:=qu3 W.hK W.core.x_ne_y.symm (fun h=>hnxy h.symm)
  have hJ : J.kind=.t3:=by
    have h:=hrank J
    cases hj : J.kind <;> simp_all [Ck0.rank]
  have hdegxy:=(W.hopt.2.2 J (by rw [hJ,qaj5 W hk])).1
  obtain ⟨B,r,hFB⟩:=qb1 ih hH hq hf W
  obtain ⟨_,⟨u,hu,hux⟩,_⟩:=qi1 ih hH hq hf W hs hFB
  have huC:=hFB.block.subset (mem_of_mem_erase hu)
  have huT : u∉W.core.T:=fun h=>qa1 W huC (W.core.T_subset_verts h)
  have hxS : insert u W.core.T⊆G.neighborFinset x:=by
    refine insert_subset ((G.mem_neighborFinset _ _).mpr hux.symm) (fun t ht=>?_)
    exact (G.mem_neighborFinset _ _).mpr ((W.core.shape3 hk).2.2.1 t ht)
  have hdx:=card_le_card hxS
  rw [card_insert_of_notMem huT,card_neighborFinset_eq_degree] at hdx
  have hdy : W.core.T.card+1≤ G.degree y:=hdx.trans hdegxy
  have hY (v : V) (h : G.Adj y v) : v=b∨v=s∨v∈W.core.T:=by
    rcases qh9 W (qc2 W) h with hv|hv
    · exact Or.inl (hleaf v hv h)
    · rw [Cc0.mem_verts,hs,mem_singleton] at hv
      exact Or.inr (hv.resolve_left fun e=>hnxy (e ▸ h.symm))
  have hnoTri (v t : V) (hv : v≠x) (ht : t≠x)
      (h : G.Adj y v) (h' : G.Adj y t) (h'' : G.Adj v t) : False :=
    qg7 (fun J=>(by decide : 2≤ 3).trans (hrank J)) W.core.x_ne_y.symm h h' h'' hv ht
  have hys : ¬ G.Adj y s:=by
    intro h
    have hYt : ∃ t∈W.core.T,G.Adj y t:=by
      by_contra hn
      have hsub : G.neighborFinset y⊆({b,s} : Finset V):=fun v hv=>by
        have had:=(G.mem_neighborFinset _ _).mp hv
        exact mem_insert.mpr ((hY v had).imp_right fun h =>
          mem_singleton.mpr (h.resolve_right fun ht=>hn ⟨v,ht,had⟩))
      have hc:=card_le_card hsub
      rw [card_neighborFinset_eq_degree] at hc
      have h₂:=card_insert_le b ({s} : Finset V)
      rw [card_singleton] at h₂
      have:=W.core.two_le_T
      omega
    obtain ⟨t,ht,hyt⟩:=hYt
    have hsS : s∈W.core.S:=hs.symm ▸ mem_singleton_self s
    exact hnoTri s t (fun e=>W.core.x_notMem_S (e ▸ hsS)) (fun e=>W.core.x_notMem_T (e ▸ ht))
      h hyt ((W.core.shape3 hk).2.2.2.2.2 s hsS t ht)
  have hYs : G.neighborFinset y⊆insert b W.core.T:=by
    intro v hv
    have had:=(G.mem_neighborFinset _ _).mp hv
    exact mem_insert.mpr ((hY v had).imp_right fun h=>h.resolve_left fun e=>hys (e ▸ had))
  have hbT : b∉W.core.T:=fun h=>qa1 W hbC (W.core.T_subset_verts h)
  have hYeq : G.neighborFinset y=insert b W.core.T:=eq_of_subset_of_card_le hYs (by
    rwa [card_insert_of_notMem hbT,card_neighborFinset_eq_degree])
  have hyDeg : G.degree y=W.core.T.card+1:=by
    rw [← card_neighborFinset_eq_degree,hYeq,card_insert_of_notMem hbT]
  have hbnoT (t : V) (ht : t∈W.core.T) : ¬ G.Adj b t:=fun h =>
    hnoTri b t (qj1 W hbC) (fun e=>W.core.x_notMem_T (e ▸ ht)) hyb
      ((G.mem_neighborFinset _ _).mp (hYeq.symm ▸ mem_insert_of_mem ht)) h
  let A:=W.C.erase y
  have hAl : Lk0 G A:=by
    by_contra hn
    exact (qx0 hchain (qc2 W) hn).2.1 rfl
  have hbA : b∈A:=mem_erase.mpr ⟨hby,hbC⟩
  obtain ⟨B₂,c,hB₂⟩:=qal4 hAl (mem_erase.mpr ⟨hzy,hzC⟩) hbA hbz.symm
    (qaj8 hby hbC hleaf hchain hzy)
  by_cases h₂ : 2 < B₂.card
  · have hcutT:=qs2 ih hH hq hf W hs hk hell hz (erase_subset _ _) hAl
      (fun h=>(notMem_erase _ _ h).elim)
      (fun v hv hvb w hw had=>mem_erase.mpr ⟨fun e=>hvb (hleaf v
        (mem_of_mem_erase hv) (e ▸ had.symm)),hw⟩)
      hB₂ (qab9 hby (mem_of_mem_erase hB₂.root) hB₂.block hleaf)
      h₂ (Pi0.edge hyb.symm)
    obtain ⟨v,hv,t,ht,had⟩:=hT
    by_cases e : v=b
    · exact hbnoT t ht (e ▸ had)
    · exact hcutT v (mem_erase.mpr ⟨e,hv⟩) t ht had
  obtain ⟨hbc,hnext⟩:=qp7 hB₂ (by omega)
  have hcC:=mem_of_mem_erase (hB₂.block.subset hB₂.entry)
  have hcy:=ne_of_mem_erase (hB₂.block.subset hB₂.entry)
  have hcutb : Ici0 G W.C b:=⟨hbC,fun hl=>by
    obtain ⟨v,hv,had⟩:=qi6 (hl y (mem_erase.mpr ⟨hyb.ne,qc2 W⟩)
        c (mem_erase.mpr ⟨hbc.ne.symm,hcC⟩)) hcy.symm
    exact ne_of_mem_erase hv (hleaf v (mem_of_mem_erase hv) had)⟩
  have hub : u≠b:=by
    rintro rfl
    obtain ⟨e,he,v,hv,hv'⟩:=hFB.exception
    have heq:=he u hu (Or.inl hcutb)
    have huv : u≠v:=fun h=>hv' (heq.trans (congrArg some h))
    have hc₀:=one_lt_card.mpr ⟨u,hu,v,hv,huv⟩
    have hc₁:=card_erase_add_one hFB.exit_mem
    have hc₂ : B.card≤ 2:=by
      by_cases hyB : y∈B
      · exact qm0 hFB.block hyB (fun v hv=>hleaf v (hFB.block.subset hv))
      · exact qm0 hFB.block (mem_of_mem_erase hu) (fun v hv =>
          hnext v (mem_erase.mpr ⟨fun e=>hyB (e ▸ hv),hFB.block.subset hv⟩))
    omega
  have hXeq : G.neighborFinset x=insert u W.core.T:=(eq_of_subset_of_card_le hxS (by
    rw [card_insert_of_notMem huT,card_neighborFinset_eq_degree,← hyDeg]
    exact hdegxy)).symm
  have hbnoX : ¬ G.Adj b x:=fun h=>by
    have h':=(G.mem_neighborFinset x b).mpr h.symm
    rw [hXeq,mem_insert] at h'
    exact h'.elim hub.symm hbT
  have hbdeg:=qk9 hH W hbC hby
    (fun e=>hbz (Option.some.inj (e.symm.trans hz)))
  have hbN : G.neighborFinset b⊆({y,c,s} : Finset V):=by
    intro v hv
    have had:=(G.mem_neighborFinset _ _).mp hv
    rcases qh9 W hbC had with hvC|hvK
    · by_cases hvy : v=y
      · exact mem_insert.mpr (Or.inl hvy)
      · exact mem_insert.mpr (Or.inr (mem_insert.mpr
          (Or.inl (hnext v (mem_erase.mpr ⟨hvy,hvC⟩) had))))
    · rw [Cc0.mem_verts,hs,mem_singleton] at hvK
      rcases hvK with rfl|rfl|ht
      · exact (hbnoX had).elim
      · simp
      · exact (hbnoT v ht had).elim
  have hbcard:=card_le_card hbN
  rw [card_neighborFinset_eq_degree] at hbcard
  have h₃:=card_insert_le y ({c,s} : Finset V)
  have h₄:=card_insert_le c ({s} : Finset V)
  rw [card_singleton] at h₄
  have:=qb6 ih hH hq hf
  omega
end Counterexample
private theorem coy_bound (N : ℕ) : Cb0 N:=by
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro V _ _ G _ x y z q hq hm hH
    by_contra hf
    have hsmall:=ih _ hm
    rcases qu1 hsmall hH hq hf with ⟨⟨W⟩⟩|⟨⟨W⟩⟩
    · exact qt0 hsmall hH hq hf W
    · obtain ⟨hH',hf'⟩:=qm6 hsmall hH hq hf
      exact qt0 hsmall hH' hq hf' W
end Cf
theorem coy4 : COY4:=by
  intro V _ _ G _ x y z q hq hq4 hR hw hd
  exact Cf.coy_bound (Fintype.card V+G.edgeFinset.card+1)
    V G x y z q hq4 (Nat.lt_succ_self _) ⟨hq,hR,hw,hd⟩
end DeanK5
end M13
theorem OMA.solution : type_of% @Arxiv.«2605.02731».dean_conjecture.variants.five :=
  DeanK5.deanFromCOY DeanK5.coy4
