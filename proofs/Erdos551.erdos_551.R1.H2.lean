import OMAReductions.R_Erdos551_erdos_551_R1
import Mathlib
import Mathlib.Tactic.Eval
/- Adapted from OpenAI math, Apache-2.0, revision 3344da59991ed94f9ba711217b29c1d760badfa6. Source: lean/OAI/Combinatorics/Ramsey/CycleClique. -/
namespace OAI
namespace CycleClique
open scoped SimpleGraph
def RamseyProperty (m n N:ℕ):Prop :=
 ∀ G:SimpleGraph (Fin N),
   SimpleGraph.cycleGraph m⊑G∨(⊤ :SimpleGraph (Fin n))⊑Gᶜ
noncomputable def cycleCliqueRamsey (m n:ℕ):ℕ :=
 sInf {N:ℕ | RamseyProperty m n N}
def z0 {V:Type*} (G:SimpleGraph V) (I:Set V):Set V :=
 I∪{v | ∃ u∈I,G.Adj u v}
end CycleClique
namespace CycleClique
open scoped SimpleGraph
theorem z82 {V:Type*} {H:SimpleGraph V}
   (z4b:H.Connected) (hnb:¬ H.IsBipartite) (χ:V → Fin 2)
   (hnc:∃ y z,χ y≠χ z) :
   ∃ x y z,H.Adj x y∧H.Adj x z∧χ y≠χ z:=by
 classical
 by_contra h
 push Not at h
 have hcol:¬ (∀ ⦃v w⦄,H.Adj v w → χ v≠χ w):=by
   intro hc
   exact hnb ⟨SimpleGraph.Coloring.mk χ (fun {v w} hvw => hc hvw)⟩
 push Not at hcol
 obtain ⟨a,b,hab,heq⟩:=hcol
 have propagate:∀ {u v:V} (p:H.Walk u v),
     ∀ z,H.Adj u z → χ u=χ z → χ v=χ u:=by
   intro u v p
   induction p with
   | nil => simp
   | @cons u w v huw p ih =>
     intro z huz heq
     have hwu: χ w=χ u:=(h u z w huz huw).symm.trans heq.symm
     exact (ih u huw.symm hwu).trans hwu
 obtain ⟨y,z,hyz⟩:=hnc
 have hy: χ y=χ a:=by
   obtain ⟨p⟩:=z4b.preconnected a y
   exact propagate p b hab heq
 have hz: χ z=χ a:=by
   obtain ⟨p⟩:=z4b.preconnected a z
   exact propagate p b hab heq
 exact hyz (hy.trans hz.symm)
theorem z95 {V:Type*} [Fintype V]
   (G:SimpleGraph V) (x:V) :
   ∃ (v:V) (p:G.Walk x v),p.IsPath ∧
     ∀ (w:V) (q:G.Walk x w),q.IsPath → q.length≤ p.length:=by
 let S:={n:ℕ | ∃ (v:V) (p:G.Walk x v),p.IsPath∧p.length=n}
 have hS:S.Finite:=(Set.finite_le_nat (Fintype.card V)).subset (by
   rintro n ⟨v,p,hp,rfl⟩
   exact hp.length_lt.le)
 obtain ⟨n,⟨⟨v,p,hp,hn⟩,hmax⟩⟩ :=
   hS.exists_maximal ⟨0,⟨x,.nil,by simp⟩⟩
 refine ⟨v,p,hp,fun w q hq => ?_⟩
 have:=hmax (show q.length∈S from ⟨w,q,hq,rfl⟩)
 omega
theorem z19 {V:Type*} {G:SimpleGraph V}
   {x v:V} (p:G.Walk x v) (hp:p.IsPath)
   (hmax:∀ (w:V) (q:G.Walk x w),q.IsPath → q.length≤ p.length) :
   ∀ w,G.Adj v w → w∈p.support:=by
 intro w hvw
 by_contra hw
 have:=hmax w (p.concat hvw) (hp.concat hw hvw)
 simp only [SimpleGraph.Walk.length_concat] at this
 omega
theorem z112 {V:Type*} {G:SimpleGraph V}
   {x b y z:V} (χ:V → Fin 2) (hxy:G.Adj x y) (hxz:G.Adj x z)
   (hyz: χ y≠χ z) (p:G.Walk x b) (hp:p.IsPath)
   (hy:y∉p.support) (hz:z∉p.support)
   {ℓ:ℕ} (hℓ: 1≤ℓ) (hlen: ℓ≤ p.length+1) :
   ∃ a b,χ a≠χ b ∧ ∃ q:G.Walk a b,q.IsPath∧q.length=ℓ:=by
 let q:=p.take (ℓ - 1)
 have hq:q.IsPath:=hp.take _
 have hsub:∀ v,v∈q.support → v∈p.support:=by
   intro v hv
   rw [SimpleGraph.Walk.support_take] at hv
   exact List.mem_of_mem_take hv
 have z65:q.length=ℓ - 1:=by
   simp only [q,SimpleGraph.Walk.take_length]
   omega
 by_cases hcy: χ y=χ (p.getVert (ℓ - 1))
 · refine ⟨z,_,?_,.cons hxz.symm q,?_,?_⟩
   · exact fun hcz => hyz (hcy.trans hcz.symm)
   · exact (SimpleGraph.Walk.cons_isPath_iff _ _).mpr ⟨hq,fun h => hz (hsub _ h)⟩
   · simp only [SimpleGraph.Walk.length_cons,z65]
     omega
 · refine ⟨y,_,hcy,.cons hxy.symm q,?_,?_⟩
   · exact (SimpleGraph.Walk.cons_isPath_iff _ _).mpr ⟨hq,fun h => hy (hsub _ h)⟩
   · simp only [SimpleGraph.Walk.length_cons,z65]
     omega
theorem z83 {V:Type*} {G:SimpleGraph V} {x v:V}
   (p:G.Walk x v) (hp:p.IsPath) (i:ℕ) (hi:i < p.length)
   (hiv:G.Adj (p.getVert i) v) :
   ∃ q:G.Walk x (p.getVert (i+1)),q.IsPath∧q.support.Perm p.support ∧
     ∀ j,j≤ i → q.getVert j=p.getVert j:=by
 let q:=(p.take i).append (.cons hiv (p.drop (i+1)).reverse)
 have z104:q.support =
     p.support.take (i+1) ++ (p.support.drop (i+1)).reverse:=by
   simp only [q,SimpleGraph.Walk.support_append,SimpleGraph.Walk.support_cons,
     List.tail_cons,SimpleGraph.Walk.support_take,SimpleGraph.Walk.support_reverse,
     SimpleGraph.Walk.drop_support_eq_support_drop_min,Nat.min_eq_left (by omega :
       i+1≤ p.length)]
 have zc:q.support.Perm p.support:=by
   rw [z104]
   simpa only [List.take_append_drop] using
     (List.reverse_perm (p.support.drop (i+1))).append_left (p.support.take (i+1))
 refine ⟨q,(q.isPath_def).mpr (zc.nodup_iff.mpr hp.support_nodup),zc,?_⟩
 intro j hj
 simp only [q,SimpleGraph.Walk.getVert_append',SimpleGraph.Walk.take_length,
   Nat.min_eq_left hi.le,if_pos hj,SimpleGraph.Walk.take_getVert,
   Nat.min_eq_right hj]
theorem z197 {V:Type*} {G:SimpleGraph V} {x v:V}
   (p:G.Walk x v) (hp:p.IsPath) (i:ℕ) (hi:i < p.length)
   (hiv:G.Adj (p.getVert i) v) :
   ∃ q:G.Walk x (p.getVert (i+1)),q.IsPath∧q.support.Perm p.support:=by
 obtain ⟨q,hq,zc,_⟩:=z83 p hp i hi hiv
 exact ⟨q,hq,zc⟩
def z10 {V:Type*} (G:SimpleGraph V) (x:V) (W:List V):Set V :=
 {v | ∃ p:G.Walk x v,p.IsPath∧p.support.Perm W}
theorem z4f {V:Type*} {G:SimpleGraph V} {x v:V} {W:List V}
   (hv:v∈z10 G x W):v∈W:=by
 obtain ⟨p,_,zc⟩:=hv
 exact zc.mem_iff.mp p.end_mem_support
theorem za5 {V:Type*} {G:SimpleGraph V} {x:V} {W:List V}
   (hW: 1 < W.length):x∉z10 G x W:=by
 rintro ⟨p,hp,zc⟩
 have hp0:=(SimpleGraph.Walk.isPath_iff_nil.mp hp).length_eq_zero
 have hlen:=zc.length_eq
 rw [SimpleGraph.Walk.length_support] at hlen
 omega
theorem z75 {V:Type*} {G:SimpleGraph V} {x e:V}
   {W:List V} (p:G.Walk x e) (hp:p.IsPath) (zc:p.support.Perm W)
   (i:ℕ) (hi:i < p.length) (hie:G.Adj (p.getVert i) e) :
   p.getVert (i+1)∈z10 G x W:=by
 obtain ⟨q,hq,hqp⟩:=z197 p hp i hi hie
 exact ⟨q,hq,hqp.trans zc⟩
theorem z6d {V:Type*} [Fintype V] {G:SimpleGraph V}
   [DecidableRel G.Adj] {x e:V} {W:List V}
   (p:G.Walk x e) (hp:p.IsPath) (zc:p.support.Perm W)
   (hnb:∀ v,G.Adj e v → v∈p.support) :
   G.degree e≤(z10 G x W).ncard:=by
 classical
 have hidx:∀ v:G.neighborSet e,
     ∃ n,n < p.length∧p.getVert n=v.val:=by
   intro v
   obtain ⟨n,hn,hle⟩:=SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
     (hnb v.val v.property)
   refine ⟨n,lt_of_le_of_ne hle ?_,hn⟩
   intro heq
   subst n
   have:e=v.val:=by simpa using hn
   exact G.ne_of_adj v.property this
 choose idx hi heq using hidx
 let f:G.neighborSet e → z10 G x W:=fun v =>
   ⟨p.getVert (idx v+1),z75 p hp zc (idx v) (hi v)
     (by rw [heq]; exact v.property.symm)⟩
 have hf:Function.Injective f:=by
   intro a b hab
   have hget:p.getVert (idx a+1)=p.getVert (idx b+1):=congrArg Subtype.val hab
   have hia:=hi a
   have hib:=hi b
   have z21d:=hp.getVert_injOn (by dsimp; omega) (by dsimp; omega) hget
   have:idx a=idx b:=by omega
   apply Subtype.ext
   rw [← heq a,← heq b,this]
 have z3b:=Fintype.card_le_of_injective f hf
 rw [← Nat.card_coe_set_eq,Nat.card_eq_fintype_card,
   ← SimpleGraph.card_neighborSet_eq_degree]
 exact z3b
theorem z72 {V:Type*} {G:SimpleGraph V} {x v:V}
   (p:G.Walk x v)
   (hmax:∀ (w:V) (q:G.Walk x w),q.IsPath → q.length≤ p.length)
   {e:V} (he:e∈z10 G x p.support) :
   ∀ w,G.Adj e w → w∈p.support:=by
 obtain ⟨q,hq,hqp⟩:=he
 have hlen:q.length=p.length:=by
   have:=hqp.length_eq
   simp only [SimpleGraph.Walk.length_support] at this
   omega
 intro w hew
 apply hqp.mem_iff.mp
 exact z19 q hq (by simpa only [hlen] using hmax) w hew
theorem z161 {V:Type*} [Fintype V] {G:SimpleGraph V}
   {x v:V} (p:G.Walk x v) (hp:p.IsPath)
   (hmax:∀ (w:V) (q:G.Walk x w),q.IsPath → q.length≤ p.length)
   (z9f:∀ a∈z10 G x p.support,∀ b∈z10 G x p.support,
     a≠b → ¬ G.Adj a b → 
     p.length+2≤(z0 G {a,b}).ncard) :
   G.IsClique (z10 G x p.support):=by
 classical
 intro a ha b hb hab
 by_contra hnab
 have hsub:z0 G {a,b}⊆(p.support.toFinset:Set V):=by
   intro w hw
   rcases hw with hw | ⟨u,hu,huw⟩
   · rcases hw with rfl | hw
     · simpa using z4f ha
     · have:w=b:=by simpa using hw
       subst w
       simpa using z4f hb
   · rcases hu with rfl | hu
     · simpa using z72 p hmax ha w huw
     · have:u=b:=by simpa using hu
       subst u
       simpa using z72 p hmax hb w huw
 have hle:=Set.ncard_le_ncard hsub
 have z3b:(p.support.toFinset:Set V).ncard=p.length+1:=by
   simp only [Set.ncard_coe_finset,List.toFinset_card_of_nodup hp.support_nodup,
     SimpleGraph.Walk.length_support]
 have:=z9f a ha b hb hab hnab
 omega
theorem zfd {V:Type*} {G:SimpleGraph V} {x v:V}
   {W:List V} (p:G.Walk x v) (hp:p.IsPath) (zc:p.support.Perm W)
   (z20:G.IsClique (z10 G x W))
   (i:ℕ) (hi:i < p.length) (hEi:p.getVert i∈z10 G x W) :
   p.getVert (i+1)∈z10 G x W:=by
 apply z75 p hp zc i hi
 apply z20 hEi (show v∈z10 G x W from ⟨p,hp,zc⟩)
 intro heq
 have:=(hp.getVert_eq_end_iff hi.le).mp heq
 omega
theorem zaa {V:Type*} {G:SimpleGraph V} {x v:V}
   {W:List V} (p:G.Walk x v) (hp:p.IsPath) (zc:p.support.Perm W)
   (z20:G.IsClique (z10 G x W)) (hW: 1 < W.length) :
   ∃ k,0 < k∧k≤ p.length ∧ ∀ i,i≤ p.length → 
     (p.getVert i∈z10 G x W↔k≤ i):=by
 classical
 have hex:∃ i,i≤ p.length∧p.getVert i∈z10 G x W:=by
   refine ⟨p.length,le_rfl,?_⟩
   simpa using (show v∈z10 G x W from ⟨p,hp,zc⟩)
 let k:=Nat.find hex
 have hk:=Nat.find_spec hex
 have zb1: 0 < k:=by
   by_contra h
   have hk0:k=0:=by omega
   have hx:x∈z10 G x W:=by simpa only [← show k=Nat.find hex from rfl,
     hk0,SimpleGraph.Walk.getVert_zero] using hk.2
   exact za5 hW hx
 refine ⟨k,zb1,hk.1,fun i hi => ⟨?_,?_⟩⟩
 · intro hEi
   exact Nat.find_min' hex ⟨hi,hEi⟩
 · intro hki
   induction i,hki using Nat.le_induction with
   | base => exact hk.2
   | succ i hki ih =>
     exact zfd p hp zc z20 i (by omega) (ih (by omega))
theorem z63 {V:Type*} {G:SimpleGraph V} {x v:V}
   (p:G.Walk x v) (hp:p.IsPath)
   (z20:G.IsClique (z10 G x p.support))
   {k:ℕ} (_:k≤ p.length)
   (z40:∀ i,i≤ p.length → 
     (p.getVert i∈z10 G x p.support↔k≤ i))
   {w:V} (hw:w∈z10 G x p.support) (hw0:w≠p.getVert k) :
   ∃ q:G.Walk x w,q.IsPath∧q.support.Perm p.support ∧
     ∀ j,j≤ k → q.getVert j=p.getVert j:=by
 obtain ⟨i,hiw,hi⟩:=SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
   (z4f hw)
 have hki:k < i:=by
   have:=(z40 i hi).mp (hiw ▸ hw)
   by_contra hn
   have:k=i:=by omega
   exact hw0 (hiw.symm.trans (congrArg p.getVert this.symm))
 have z205:p.getVert (i - 1)∈z10 G x p.support :=
   (z40 _ (by omega)).mpr (by omega)
 have hadj:G.Adj (p.getVert (i - 1)) v:=by
   apply z20 z205 (show v∈z10 G x p.support from ⟨p,hp,.refl _⟩)
   intro heq
   have:=(hp.getVert_eq_end_iff (by omega)).mp heq
   omega
 have hrot:=z83 p hp (i - 1) (by omega) hadj
 rw [Nat.sub_add_cancel (by omega: 1≤ i),hiw] at hrot
 obtain ⟨q,hq,zc,hpre⟩:=hrot
 exact ⟨q,hq,zc,fun j hj => hpre j (by omega)⟩
theorem z5f {V:Type*} {G:SimpleGraph V} {x v:V}
   (p:G.Walk x v)
   (hmax:∀ (w:V) (q:G.Walk x w),q.IsPath → q.length≤ p.length)
   {k:ℕ} (zb1: 0 < k) (hk:k≤ p.length)
   (z40:∀ i,i≤ p.length → 
     (p.getVert i∈z10 G x p.support↔k≤ i))
   {w:V} (q:G.Walk x w) (hq:q.IsPath) (zc:q.support.Perm p.support)
   (hpre:∀ j,j < k → q.getVert j=p.getVert j) :
   ∀ a,G.Adj w a → a∈z10 G x p.support∨a=p.getVert (k - 1):=by
 have hlen:q.length=p.length:=by
   have:=zc.length_eq
   simp only [SimpleGraph.Walk.length_support] at this
   omega
 intro a ha
 by_cases haE:a∈z10 G x p.support
 · exact Or.inl haE
 right
 obtain ⟨j,hja,hj⟩:=SimpleGraph.Walk.mem_support_iff_exists_getVert.mp
   (z72 p hmax ⟨q,hq,zc⟩ a ha)
 have hjk:j < k:=by
   by_contra hn
   exact haE (hja ▸ (z40 j hj).mpr (by omega))
 have z1ec:j=k - 1:=by
   by_contra hn
   have z208:j+1 < k:=by omega
   have hadj:G.Adj (q.getVert j) w:=by rw [hpre j hjk,hja]; exact ha.symm
   have he:=z75 q hq zc j (by omega) hadj
   rw [hpre (j+1) z208] at he
   have:=(z40 (j+1) (by omega)).mp he
   omega
 exact hja.symm.trans (congrArg p.getVert z1ec)
theorem z5d {V:Type*} {G:SimpleGraph V} {x v:V}
   (p:G.Walk x v) (hp:p.IsPath)
   (hmax:∀ (w:V) (q:G.Walk x w),q.IsPath → q.length≤ p.length)
   (z20:G.IsClique (z10 G x p.support))
   {k:ℕ} (zb1: 0 < k) (hk:k≤ p.length)
   (z40:∀ i,i≤ p.length → 
     (p.getVert i∈z10 G x p.support↔k≤ i))
   {w:V} (hw:w∈z10 G x p.support) (hw0:w≠p.getVert k) :
   ∀ a,G.Adj w a → a∈z10 G x p.support∨a=p.getVert (k - 1):=by
 obtain ⟨q,hq,zc,hpre⟩:=z63 p hp z20 hk
   z40 hw hw0
 exact z5f p hmax zb1 hk z40 q hq zc
   (fun j hj => hpre j hj.le)
theorem z64 {V:Type*} {G:SimpleGraph V} {x v:V}
   (p:G.Walk x v) (hp:p.IsPath)
   (hmax:∀ (w:V) (q:G.Walk x w),q.IsPath → q.length≤ p.length)
   (z20:G.IsClique (z10 G x p.support))
   {k:ℕ} (zb1: 0 < k) (hk:k≤ p.length)
   (z40:∀ i,i≤ p.length → 
     (p.getVert i∈z10 G x p.support↔k≤ i))
   {w₁:V} (hw₁:w₁∈z10 G x p.support) (hne:w₁≠p.getVert k)
   (z103:G.Adj (p.getVert (k - 1)) w₁) :
   ∀ w∈z10 G x p.support,∀ a,G.Adj w a → 
     a∈z10 G x p.support∨a=p.getVert (k - 1):=by
 intro w hw
 by_cases hww0:w=p.getVert k
 · subst w
   obtain ⟨q,hq,zc,hpre⟩:=z63 p hp z20 hk
     z40 hw₁ hne
   have hlen:q.length=p.length:=by
     have:=zc.length_eq
     simp only [SimpleGraph.Walk.length_support] at this
     omega
   have hadj:G.Adj (q.getVert (k - 1)) w₁:=by
     rw [hpre _ (by omega)]
     exact z103
   have hrot:=z83 q hq (k - 1) (by omega) hadj
   rw [Nat.sub_add_cancel zb1,hpre k le_rfl] at hrot
   obtain ⟨r,hr,hrperm,hrpre⟩:=hrot
   exact z5f p hmax zb1 hk z40 r hr
     (hrperm.trans zc) (fun j hj => (hrpre j (by omega)).trans (hpre j (by omega)))
 · exact z5d p hp hmax z20 zb1 hk z40 hw hww0
def z4a {V:Type*} (G:SimpleGraph V) (S:Set V):SimpleGraph V where
 Adj a b:=G.Adj a b∧a∈S∧b∈S
 symm:=⟨fun _ _ h => ⟨h.1.symm,h.2.2,h.2.1⟩⟩
 loopless:=⟨fun _ h => h.1.ne rfl⟩
theorem z159 {V:Type*} (G:SimpleGraph V) (S:Set V):z4a G S≤ G :=
 fun _ _ h => h.1
theorem z67 {V:Type*} {G:SimpleGraph V} {S:Set V} {x v:V}
   (p:(z4a G S).Walk x v) (hx:x∈S):∀ w∈p.support,w∈S:=by
 induction p with
 | nil => simpa using hx
 | @cons u v w huv p ih =>
   intro a ha
   simp only [SimpleGraph.Walk.support_cons,List.mem_cons] at ha
   rcases ha with rfl | ha
   · exact huv.2.1
   · exact ih huv.2.2 a ha
def zcc {V:Type*} {G:SimpleGraph V} {S:Set V} {x v:V}
   (p:G.Walk x v) (hS:∀ w∈p.support,w∈S):(z4a G S).Walk x v :=
 match p with
 | .nil => .nil
 | .cons h p => .cons ⟨h,hS _ (by simp),hS _ (by simp)⟩
   (zcc p (fun w hw => hS w (by simp [hw])))
@[simp] theorem walkWithin_support {V:Type*} {G:SimpleGraph V} {S:Set V} {x v:V}
   (p:G.Walk x v) (hS:∀ w∈p.support,w∈S):(zcc p hS).support=p.support:=by
 induction p with
 | nil => rfl
 | @cons a b c h p ih =>
   change a ::(zcc p _).support=a ::p.support
   rw [ih]
theorem z15c {V:Type*} {H:SimpleGraph V} {x y z:V}
   (hxy:x≠y) (hxz:x≠z) :
   ∃ S:Set V,x∈S∧y∉S∧z∉S ∧
     (∀ a∈S,∀ b∈S,(z4a H S).Reachable a b) ∧
     (∀ a∈S,∀ b,H.Adj a b → b∈S∨b=y∨b=z):=by
 let D:=z4a H {v | v≠y∧v≠z}
 let S:={v | D.Reachable x v}
 have hx:x∈S:=SimpleGraph.Reachable.rfl
 have z1a2:∀ v∈S,v≠y∧v≠z:=by
   rintro v ⟨p⟩
   exact z67 p ⟨hxy,hxz⟩ v p.end_mem_support
 refine ⟨S,hx,fun hy => (z1a2 y hy).1 rfl,fun hz => (z1a2 z hz).2 rfl,?_,?_⟩
 · intro a ha b hb
   obtain ⟨p⟩:=(ha:D.Reachable x a).symm.trans hb
   have hS:∀ w∈p.support,w∈S:=by
     intro w hw
     obtain ⟨i,hi,_⟩:=SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
     rw [← hi]
     exact (ha:D.Reachable x a).trans ⟨p.take i⟩
   exact ⟨zcc (p.mapLe (z159 H _)) (by simpa using hS)⟩
 · intro a ha b hab
   by_cases hby:b=y
   · exact Or.inr (Or.inl hby)
   by_cases hbz:b=z
   · exact Or.inr (Or.inr hbz)
   exact Or.inl ((ha:D.Reachable x a).trans (SimpleGraph.Adj.reachable
     (show D.Adj a b from ⟨hab,z1a2 a ha,hby,hbz⟩)))
theorem z28 {V:Type*} [Fintype V] (G:SimpleGraph V) [DecidableRel G.Adj]
   (v:V):(G.neighborSet v).ncard=G.degree v:=by
 rw [← Nat.card_coe_set_eq,Nat.card_eq_fintype_card,SimpleGraph.card_neighborSet_eq_degree]
theorem z29 {V:Type*} [Fintype V]
   {G:SimpleGraph V} [DecidableRel G.Adj] {v:V} {S:Set V}
   (hv:v∈S) (hS:∀ w,G.Adj v w → w∈S):G.degree v+1≤ S.ncard:=by
 have hsub:insert v (G.neighborSet v)⊆S:=by
   intro w hw
   rcases hw with rfl | hw
   · exact hv
   · exact hS w hw
 have hc:=Set.ncard_le_ncard hsub
 simpa only [Set.ncard_insert_of_notMem G.notMem_neighborSet_self,
   z28] using hc
theorem z3c {V:Type*} [Fintype V]
   {G:SimpleGraph V} [DecidableRel G.Adj] {v:V} {S:Set V}
   (hv:v∈S) (hS:∀ w,G.Adj v w → w∈S)
   (z3b:S.ncard≤ G.degree v+1):∀ w∈S,w≠v → G.Adj v w:=by
 classical
 have hsub:insert v (G.neighborSet v)⊆S:=by
   intro w hw
   rcases hw with rfl | hw
   · exact hv
   · exact hS w hw
 have heq:insert v (G.neighborSet v)=S:=by
   apply Set.eq_of_subset_of_ncard_le hsub
   simpa only [Set.ncard_insert_of_notMem G.notMem_neighborSet_self,
     z28] using z3b
 intro w hw hne
 rw [← heq] at hw
 exact hw.resolve_left hne
theorem z35 {V:Type*} [Fintype V] {H:SimpleGraph V} {s:ℕ}
   (z37:¬ (⊤ :SimpleGraph (Fin s))⊑H) {E:Set V} (hE:H.IsClique E) :
   E.ncard < s:=by
 classical
 have hf:H.CliqueFree s:=by
   by_contra hn
   exact z37 ((SimpleGraph.not_cliqueFree_iff_top_isContained s).mp hn)
 by_contra hn
 have hle:s≤ E.toFinset.card:=by simpa only [← Set.ncard_eq_toFinset_card'] using
   (Nat.le_of_not_gt hn)
 apply hf.mono hle E.toFinset
 exact ⟨by simpa using hE,rfl⟩
theorem zcf {V:Type*} [Fintype V]
   {H K:SimpleGraph V} [DecidableRel H.Adj] [DecidableRel K.Adj] {v y z:V}
   (hb:∀ w,H.Adj v w → K.Adj v w∨w=y∨w=z) :
   H.degree v≤ K.degree v+2:=by
 have hsub:H.neighborSet v⊆insert y (insert z (K.neighborSet v)):=by
   intro w hw
   rcases hb w hw with hw | hw | hw
   · exact Or.inr (Or.inr hw)
   · exact Or.inl hw
   · exact Or.inr (Or.inl hw)
 have hle:=Set.ncard_le_ncard hsub
 have hy:=Set.ncard_insert_le y (insert z (K.neighborSet v))
 have hz:=Set.ncard_insert_le z (K.neighborSet v)
 rw [z28] at hle hz
 omega
theorem z49 {V:Type*} [Finite V] {E:Set V} {w₀:V}
   (z3b: 2≤ E.ncard):∃ w∈E,w≠w₀:=by
 by_contra hn
 push Not at hn
 have hsub:E⊆{w₀}:=fun w hw => hn w hw
 have hle:=Set.ncard_le_ncard hsub
 simp only [Set.ncard_singleton] at hle
 omega
theorem zdc {V:Type*} [Fintype V]
   {H K:SimpleGraph V} [DecidableRel H.Adj] [DecidableRel K.Adj]
   {s:ℕ} (hs: 4≤ s) (z37:¬ (⊤ :SimpleGraph (Fin s))⊑H)
   (z27:∀ w,s≤ H.degree w)
   {E:Set V} (hE:H.IsClique E) (z1bc:s - 2≤ E.ncard)
   {u w₀ y z:V} (hw₀:w₀∈E) (hu:u∉E) (hy:y∉E) (hz:z∉E)
   (huy:u≠y) (huz:u≠z)
   (z1e:∀ w∈E,∀ a,H.Adj w a → K.Adj w a∨a=y∨a=z)
   (z13e:∀ w∈E,w≠w₀ → ∀ a,K.Adj w a → a∈E∨a=u)
   (z1b9:∀ w∈E,K.degree w≤ E.ncard) :
   ∃ w∈E,w≠w₀∧K.Adj u w:=by
 classical
 have z17a:=z35 z37 hE
 have z1a3:E.ncard=s - 2∨E.ncard=s - 1:=by omega
 by_contra hno
 push Not at hno
 rcases z1a3 with z131 | z1a6
 · obtain ⟨w,hw,hww₀⟩:=z49 (show 2≤ E.ncard by omega)
   have hnb:∀ a,H.Adj w a → a∈insert u (insert y (insert z E)):=by
     intro a ha
     rcases z1e w hw a ha with ha | rfl | rfl
     · rcases z13e w hw hww₀ a ha with ha | rfl
       · exact Or.inr (Or.inr (Or.inr ha))
       · exact Or.inl rfl
     · exact Or.inr (Or.inl rfl)
     · exact Or.inr (Or.inr (Or.inl rfl))
   have z3b:(insert u (insert y (insert z E))).ncard≤ H.degree w+1:=by
     have:=Set.ncard_insert_le u (insert y (insert z E))
     have:=Set.ncard_insert_le y (insert z E)
     have:=Set.ncard_insert_le z E
     have:=z27 w
     omega
   have hwu:H.Adj w u:=z3c
     (by simp [hw]) hnb z3b u (by simp) (fun heq => hu (heq ▸ hw))
   rcases z1e w hw u hwu with hwu | h | h
   · exact hno w hw hww₀ hwu.symm
   · exact huy h
   · exact huz h
 · have z176:∀ w∈E,w≠w₀ → H.Adj w y∧H.Adj w z:=by
     intro w hw hww₀
     have hnb:∀ a,H.Adj w a → a∈insert y (insert z E):=by
       intro a ha
       rcases z1e w hw a ha with ha | rfl | rfl
       · rcases z13e w hw hww₀ a ha with haE | rfl
         · exact Or.inr (Or.inr haE)
         · exact False.elim (hno w hw hww₀ ha.symm)
       · exact Or.inl rfl
       · exact Or.inr (Or.inl rfl)
     have z3b:(insert y (insert z E)).ncard≤ H.degree w+1:=by
       have:=Set.ncard_insert_le y (insert z E)
       have:=Set.ncard_insert_le z E
       have:=z27 w
       omega
     have hall:=z3c (G:=H) (v:=w)
       (by simp [hw]) hnb z3b
     exact ⟨hall y (by simp) (fun heq => hy (heq ▸ hw)),
       hall z (by simp) (fun heq => hz (heq ▸ hw))⟩
   have z1f4:H.Adj w₀ y∨H.Adj w₀ z:=by
     by_contra hn
     push Not at hn
     have hsub:H.neighborSet w₀⊆K.neighborSet w₀:=by
       intro a ha
       rcases z1e w₀ hw₀ a ha with haK | rfl | rfl
       · exact haK
       · exact False.elim (hn.1 ha)
       · exact False.elim (hn.2 ha)
     have hc:=Set.ncard_le_ncard hsub
     rw [z28,z28] at hc
     have:=z1b9 w₀ hw₀
     have:=z27 w₀
     omega
   have hbad:∀ t,t∉E → H.Adj w₀ t → 
       (∀ w∈E,w≠w₀ → H.Adj w t) → False:=by
     intro t ht hw₀t hall
     have hEt:H.IsClique (insert t E):=hE.insert (by
       intro w hw _
       by_cases heq:w=w₀
       · subst w; exact hw₀t.symm
       · exact (hall w hw heq).symm)
     have:=z35 z37 hEt
     rw [Set.ncard_insert_of_notMem ht] at this
     omega
   rcases z1f4 with h | h
   · exact hbad y hy h (fun w hw hne => (z176 w hw hne).1)
   · exact hbad z hz h (fun w hw hne => (z176 w hw hne).2)
theorem zbb {V:Type*} [Fintype V]
   {H K:SimpleGraph V} [DecidableRel H.Adj] [DecidableRel K.Adj]
   {s:ℕ} (hs: 4≤ s) (z37:¬ (⊤ :SimpleGraph (Fin s))⊑H)
   (z27:∀ w,s≤ H.degree w)
   {E:Set V} (hE:H.IsClique E) (z1bc:s - 2≤ E.ncard)
   {u y z:V} (hu:u∉E) (hy:y∉E) (hz:z∉E)
   (z1e:∀ w∈E,∀ a,H.Adj w a → K.Adj w a∨a=y∨a=z)
   (z44:∀ w∈E,∀ a,K.Adj w a → a∈E∨a=u)
   (hKH:K≤ H):∃ w∈E,H.Adj w y∧H.Adj w z:=by
 classical
 have z17a:=z35 z37 hE
 have z1a3:E.ncard=s - 2∨E.ncard=s - 1:=by omega
 rcases z1a3 with z131 | z1a6
 · obtain ⟨w,hw,_⟩:=z49 (w₀:=u) (show 2≤ E.ncard by omega)
   have hnb:∀ a,H.Adj w a → a∈insert u (insert y (insert z E)):=by
     intro a ha
     rcases z1e w hw a ha with ha | rfl | rfl
     · rcases z44 w hw a ha with ha | rfl
       · exact Or.inr (Or.inr (Or.inr ha))
       · exact Or.inl rfl
     · exact Or.inr (Or.inl rfl)
     · exact Or.inr (Or.inr (Or.inl rfl))
   have z3b:(insert u (insert y (insert z E))).ncard≤ H.degree w+1:=by
     have:=Set.ncard_insert_le u (insert y (insert z E))
     have:=Set.ncard_insert_le y (insert z E)
     have:=Set.ncard_insert_le z E
     have:=z27 w
     omega
   have hall:=z3c (G:=H) (v:=w)
     (by simp [hw]) hnb z3b
   exact ⟨w,hw,hall y (by simp) (fun heq => hy (heq ▸ hw)),
     hall z (by simp) (fun heq => hz (heq ▸ hw))⟩
 · by_contra hno
   push Not at hno
   have z1f8:∀ w∈E,H.Adj w u:=by
     intro w hw
     by_contra hnwu
     have z1dc:¬ H.Adj w y ∨ ¬ H.Adj w z:=by tauto
     have z98:∀ t,(∀ a,H.Adj w a → a∈insert t E) → False:=by
       intro t hnb
       have z78:=z29
         (G:=H) (v:=w) (by simp [hw]) hnb
       have:=Set.ncard_insert_le t E
       have:=z27 w
       omega
     rcases z1dc with hny | hnz
     · apply z98 z
       intro a ha
       rcases z1e w hw a ha with haK | rfl | rfl
       · rcases z44 w hw a haK with haE | rfl
         · exact Or.inr haE
         · exact False.elim (hnwu (hKH haK))
       · exact False.elim (hny ha)
       · exact Or.inl rfl
     · apply z98 y
       intro a ha
       rcases z1e w hw a ha with haK | rfl | rfl
       · rcases z44 w hw a haK with haE | rfl
         · exact Or.inr haE
         · exact False.elim (hnwu (hKH haK))
       · exact Or.inl rfl
       · exact False.elim (hnz ha)
   have hEu:H.IsClique (insert u E):=hE.insert (fun w hw _ => (z1f8 w hw).symm)
   have:=z35 z37 hEu
   rw [Set.ncard_insert_of_notMem hu] at this
   omega
theorem z109 {V:Type*} {K:SimpleGraph V} {E:Set V} {u b:V}
   (p:K.Walk u b) (hp:p.IsPath) (hb:b∉E)
   (z44:∀ w∈E,∀ a,K.Adj w a → a∈E∨a=u) :
   ∀ w∈p.support,w∉E:=by
 intro w hw hwE
 obtain ⟨i,hi,hilen⟩:=SimpleGraph.Walk.mem_support_iff_exists_getVert.mp hw
 have hiE:p.getVert i∈E:=hi ▸ hwE
 obtain ⟨d,hd,hfst,hsnd⟩:=(p.drop i).exists_boundary_dart E hiE hb
 have z206:d.snd=u:=(z44 d.fst hfst d.snd d.adj).resolve_left hsnd
 have hdp:d∈p.darts:=by
   rw [SimpleGraph.Walk.darts_drop] at hd
   exact List.mem_of_mem_drop hd
 have z20b:u∈p.support.tail:=by
   rw [← SimpleGraph.Walk.map_snd_darts]
   exact List.mem_map.mpr ⟨d,hdp,z206⟩
 have hnd:=hp.support_nodup
 rw [← p.cons_tail_support,List.nodup_cons] at hnd
 exact hnd.1 z20b
theorem z92 {V:Type*} {H:SimpleGraph V}
   {S E:Set V} {u b:V} (hu:u∈S \ E) (hb:b∈S \ E)
   (z4b:(z4a H S).Reachable u b)
   (z44:∀ w∈E,∀ a,(z4a H S).Adj w a → a∈E∨a=u) :
   (z4a H (S \ E)).Reachable u b:=by
 obtain ⟨p,hp⟩:=z4b.exists_isPath
 have hS:=z67 p hu.1
 have hE:=z109 p hp hb.2 z44
 exact ⟨zcc (p.mapLe (z159 H S)) (by
   intro w hw
   have hw' :w∈p.support:=by simpa using hw
   exact ⟨hS w hw',hE w hw'⟩)⟩
theorem z111 {V:Type*} [Fintype V] {H:SimpleGraph V}
   [DecidableRel H.Adj] {s:ℕ} (hs: 4≤ s)
   (z37:¬ (⊤ :SimpleGraph (Fin s))⊑H) (z27:∀ w,s≤ H.degree w)
   (z9f:∀ a b,a≠b → ¬ H.Adj a b → 
     2*s≤(z0 H {a,b}).ncard)
   {S:Set V} (hS:S.Nonempty) {y z:V} (hy:y∉S) (hz:z∉S)
   (z1e:∀ a∈S,∀ b,H.Adj a b → b∈S∨b=y∨b=z) :
   2*s - 2≤ S.ncard:=by
 classical
 have zf7:¬ H.IsClique S:=by
   intro hcl
   have z131:=z35 z37 hcl
   obtain ⟨v,hv⟩:=hS
   have hnb:∀ w,H.Adj v w → w∈insert y (insert z S):=by
     intro w hw
     rcases z1e v hv w hw with hw | rfl | rfl
     · exact Or.inr (Or.inr hw)
     · exact Or.inl rfl
     · exact Or.inr (Or.inl rfl)
   have hc:=z29 (G:=H) (v:=v)
     (by simp [hv]) hnb
   have hc₁:=Set.ncard_insert_le y (insert z S)
   have hc₂:=Set.ncard_insert_le z S
   have z214:=z27 v
   have z3b:S.ncard=s - 1:=by omega
   have hall:∀ w∈S,H.Adj w y:=by
     intro w hw
     have hnb' :∀ a,H.Adj w a → a∈insert y (insert z S):=by
       intro a ha
       rcases z1e w hw a ha with ha | rfl | rfl
       · exact Or.inr (Or.inr ha)
       · exact Or.inl rfl
       · exact Or.inr (Or.inl rfl)
     apply z3c (G:=H) (v:=w) (by simp [hw]) hnb'
     · have:=z27 w
       omega
     · simp
     · exact fun heq => hy (heq ▸ hw)
   have hcl' :H.IsClique (insert y S):=hcl.insert (fun w hw _ => (hall w hw).symm)
   have hbad:=z35 z37 hcl'
   rw [Set.ncard_insert_of_notMem hy] at hbad
   omega
 change ¬ Set.Pairwise S H.Adj at zf7
 simp only [Set.Pairwise] at zf7
 push Not at zf7
 obtain ⟨a,ha,b,hb,hab,hnab⟩:=zf7
 have hsub:z0 H {a,b}⊆insert y (insert z S):=by
   intro w hw
   rcases hw with hw | ⟨v,hv,hvw⟩
   · have hwS:w∈S:=by
       rcases hw with rfl | hw
       · exact ha
       · have:w=b:=by simpa using hw
         simpa only [this] using hb
     exact Or.inr (Or.inr hwS)
   · have hvS:v∈S:=by
       rcases hv with rfl | hv
       · exact ha
       · have:v=b:=by simpa using hv
         simpa only [this] using hb
     rcases z1e v hvS w hvw with hw | rfl | rfl
     · exact Or.inr (Or.inr hw)
     · exact Or.inl rfl
     · exact Or.inr (Or.inl rfl)
 have hc:=Set.ncard_le_ncard hsub
 have hc₁:=Set.ncard_insert_le y (insert z S)
 have hc₂:=Set.ncard_insert_le z S
 have he:=z9f a b hab hnab
 omega
theorem za3 {V:Type*} {H:SimpleGraph V}
   {S I:Set V} {y z:V} (hI:I⊆S)
   (z1e:∀ a∈S,∀ b,H.Adj a b → b∈S∨b=y∨b=z) :
   z0 H I⊆insert y (insert z (z0 (z4a H S) I)):=by
 intro w hw
 rcases hw with hw | ⟨a,ha,haw⟩
 · exact Or.inr (Or.inr (Or.inl hw))
 · rcases z1e a (hI ha) w haw with hwS | rfl | rfl
   · exact Or.inr (Or.inr (Or.inr ⟨a,ha,haw,hI ha,hwS⟩))
   · exact Or.inl rfl
   · exact Or.inr (Or.inl rfl)
theorem z148 {V:Type*} [Fintype V] {G:SimpleGraph V}
   {E:Set V} (hE:G.IsClique E) {a b:V} (ha:a∈E) (hb:b∈E)
   (hab:a≠b):∃ p:G.Walk a b,p.IsPath ∧
     (∀ v,v∈p.support↔v∈E)∧p.length+1=E.ncard:=by
 classical
 let T:=(E.toFinset.erase a).erase b
 let L:=a ::(T.toList ++ [b])
 have hmem:∀ v,v∈L↔v∈E:=by
   intro v
   simp only [L,List.mem_cons,List.mem_append,Finset.mem_toList,
     List.not_mem_nil,or_false,T,Finset.mem_erase,Set.mem_toFinset]
   constructor
   · rintro (rfl | ⟨_,_,hv⟩ | rfl)
     · exact ha
     · exact hv
     · exact hb
   · intro hv
     by_cases hva:v=a
     · exact Or.inl hva
     by_cases hvb:v=b
     · exact Or.inr (Or.inr hvb)
     exact Or.inr (Or.inl ⟨hvb,hva,hv⟩)
 have hnd:L.Nodup:=by
   simp only [L,List.nodup_cons,List.mem_append,Finset.mem_toList,
     List.mem_singleton,T,Finset.mem_erase,List.nodup_append]
   refine ⟨?_,Finset.nodup_toList _,by simp,?_⟩
   · simp [hab]
   · intro c hc d hd
     have hdb:d=b:=by simpa using hd
     subst d
     exact hc.1
 have z130:L.IsChain G.Adj:=by
   apply List.Pairwise.isChain
   rw [List.pairwise_iff_getElem]
   intro i j hi hj hij
   exact hE ((hmem _).mp (List.getElem_mem hi)) ((hmem _).mp (List.getElem_mem hj))
     (fun heq => (Nat.ne_of_lt hij) (hnd.getElem_inj_iff.mp heq))
 let p₀:=SimpleGraph.Walk.ofSupport L (by simp [L]) z130
 have za6:L.head (by simp [L])=a:=rfl
 have z11c:L.getLast (by simp [L])=b:=by
   change ((a ::T.toList) ++ [b]).getLast _=b
   exact List.getLast_concat
 let p:=p₀.copy za6 z11c
 have z104:p.support=L:=by simp [p,p₀]
 have hp:p.IsPath:=p.isPath_def.mpr (z104 ▸ hnd)
 refine ⟨p,hp,fun v => by rw [z104]; exact hmem v,?_⟩
 have hset:(p.support.toFinset:Set V)=E:=by
   ext v
   simpa [z104] using hmem v
 rw [← hset,Set.ncard_coe_finset,List.toFinset_card_of_nodup hp.support_nodup,
   SimpleGraph.Walk.length_support]
theorem z14b {V:Type*} {G:SimpleGraph V} {a b u v:V}
   (p:G.Walk a b) (q:G.Walk u v) (hp:p.IsPath) (hq:q.IsPath)
   (hbu:G.Adj b u) (hdis:∀ w∈p.support,w∉q.support) :
   (p.append (.cons hbu q)).IsPath:=by
 rw [SimpleGraph.Walk.isPath_def,SimpleGraph.Walk.support_append,
   SimpleGraph.Walk.support_cons,List.tail_cons,List.nodup_append]
 refine ⟨hp.support_nodup,hq.support_nodup,?_⟩
 intro c hc d hd hcd
 subst d
 exact hdis c hc hd
theorem zf0 {V:Type*} [Fintype V] {H:SimpleGraph V}
   [DecidableRel H.Adj] {s:ℕ} (hs: 4≤ s)
   (z37:¬ (⊤ :SimpleGraph (Fin s))⊑H) (z27:∀ a,s≤ H.degree a)
   (z9f:∀ a b,a≠b → ¬ H.Adj a b → 
     2*s≤(z0 H {a,b}).ncard)
   {S E:Set V} {u y z w:V} (hu:u∈S \ E) (hw:w∈E)
   (hy:y∉S) (hz:z∉S) (hES:E⊆S) (hE:H.IsClique E)
   (z4b:∀ a∈S,∀ b∈S,(z4a H S).Reachable a b)
   (z1e:∀ a∈S,∀ b,H.Adj a b → b∈S∨b=y∨b=z)
   (z44:∀ a∈E,∀ b,(z4a H S).Adj a b → b∈E∨b=u)
   (z103:∃ e∈E,e≠w∧(z4a H S).Adj e u) :
   ∃ v,∃ p:(z4a H S).Walk w v,p.IsPath∧2*s - 2≤ p.length+1:=by
 classical
 let K:=z4a H S
 let D:=z4a H (S \ E)
 have hDK:D≤ K:=fun a b h => ⟨h.1,h.2.1.1,h.2.2.1⟩
 have z21a:=z111 hs z37 z27 z9f ⟨u,hu.1⟩ hy hz z1e
 have z218:=z35 z37 hE
 have z1e1: 2≤(S \ E).ncard:=by
   have:=Set.ncard_sdiff_add_ncard_of_subset hES
   omega
 obtain ⟨b,hb,hbu⟩:=z49 (w₀:=u) z1e1
 have z1ef:=z92 hu hb
   (z4b u hu.1 b hb.1) z44
 obtain ⟨r₀,hr₀⟩:=z1ef.exists_isPath
 obtain ⟨v,r,hr,hmax⟩:=z95 D u
 have hpos: 0 < r.length:=by
   have hle:=hmax b r₀ hr₀
   have hne:r₀.length≠0:=fun h => hbu (SimpleGraph.Walk.eq_of_length_eq_zero h).symm
   omega
 have hvu:v≠u:=by
   intro heq
   subst v
   have:=(SimpleGraph.Walk.isPath_iff_nil.mp hr).length_eq_zero
   omega
 have hrS:=z67 r hu
 have hv:v∈S \ E:=hrS v r.end_mem_support
 have hnbs:∀ a,K.Adj v a → a∈r.support:=by
   intro a ha
   have haE:a∉E:=by
     intro haE
     rcases z44 a haE v ha.symm with hvE | hvu'
     · exact hv.2 hvE
     · exact hvu hvu'
   exact z19 r hr hmax a ⟨ha.1,hv,ha.2.2,haE⟩
 have hvw:v≠w:=fun heq => hv.2 (heq ▸ hw)
 have hnvw:¬ H.Adj v w:=by
   intro hvw'
   rcases z44 w hw v ⟨hvw'.symm,hES hw,hv.1⟩ with hvE | hvu'
   · exact hv.2 hvE
   · exact hvu hvu'
 let T:Set V:=(r.support.toFinset:Set V)
 have z21b:T.ncard=r.length+1:=by
   simp only [T,Set.ncard_coe_finset,List.toFinset_card_of_nodup hr.support_nodup,
     SimpleGraph.Walk.length_support]
 have hsub:z0 H {v,w}⊆insert y (insert z (E∪T)):=by
   intro a ha
   rcases ha with ha | ⟨c,hc,hca⟩
   · rcases Set.mem_insert_iff.mp ha with rfl | ha
     · exact Or.inr (Or.inr (Or.inr (by simp [T])))
     · have:a=w:=Set.mem_singleton_iff.mp ha
       subst a
       exact Or.inr (Or.inr (Or.inl hw))
   · rcases Set.mem_insert_iff.mp hc with hc | hc
     · subst c
       rcases z1e v hv.1 a hca with haS | rfl | rfl
       · exact Or.inr (Or.inr (Or.inr (by simpa [T] using hnbs a ⟨hca,hv.1,haS⟩)))
       · exact Or.inl rfl
       · exact Or.inr (Or.inl rfl)
     · have:c=w:=Set.mem_singleton_iff.mp hc
       subst c
       rcases z1e w (hES hw) a hca with haS | rfl | rfl
       · rcases z44 w hw a ⟨hca,hES hw,haS⟩ with haE | rfl
         · exact Or.inr (Or.inr (Or.inl haE))
         · exact Or.inr (Or.inr (Or.inr (by simp [T])))
       · exact Or.inl rfl
       · exact Or.inr (Or.inl rfl)
 have hsum: 2*s - 2≤ E.ncard+(r.length+1):=by
   have:=z9f v w hvw hnvw
   have:=Set.ncard_le_ncard hsub
   have:=Set.ncard_insert_le y (insert z (E∪T))
   have:=Set.ncard_insert_le z (E∪T)
   have:=Set.ncard_union_le E T
   omega
 obtain ⟨e,he,hew,heu⟩:=z103
 have hEK:K.IsClique E:=fun a ha b hb hab => ⟨hE ha hb hab,hES ha,hES hb⟩
 obtain ⟨q,hq,hqE,hqcard⟩:=z148 hEK hw he hew.symm
 let rK:=r.mapLe hDK
 have hrK:rK.IsPath:=hr.mapLe hDK
 have hdis:∀ a∈q.support,a∉rK.support:=by
   intro a ha har
   have har' :a∈r.support:=by simpa [rK] using har
   exact (hrS a har').2 ((hqE a).mp ha)
 refine ⟨v,q.append (.cons heu rK),z14b q rK hq hrK heu hdis,?_⟩
 simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_cons,
   rK,SimpleGraph.Walk.length_mapLe]
 omega
theorem z194 {V:Type*} [Fintype V] (H:SimpleGraph V)
   [DecidableRel H.Adj] (s:ℕ) (hs: 4≤ s) (z4b:H.Connected)
   (hnb:¬ H.IsBipartite) (z37:¬ (⊤ :SimpleGraph (Fin s))⊑H)
   (z27:∀ v,s≤ H.degree v)
   (z9f:∀ a b,a≠b → ¬ H.Adj a b → 
     2*s≤(z0 H {a,b}).ncard)
   (χ:V → Fin 2) (hnc:∃ y z,χ y≠χ z)
   (ℓ:ℕ) (hℓ: 1≤ℓ) (z1bd: ℓ≤2*s - 2) :
   ∃ y z,χ y≠χ z ∧ ∃ p:H.Walk y z,p.IsPath∧p.length=ℓ:=by
 classical
 obtain ⟨x,y,z,hxy,hxz,hyzcol⟩ :=
   z82 z4b hnb χ hnc
 obtain ⟨S,hxS,hyS,hzS,hSconn,z1e⟩:=z15c hxy.ne hxz.ne
 let K:=z4a H S
 have hKH:K≤ H:=z159 H S
 have z78:∀ a∈S,∀ b,H.Adj a b → K.Adj a b∨b=y∨b=z:=by
   intro a ha b hab
   rcases z1e a ha b hab with hb | hb | hb
   · exact Or.inl ⟨hab,ha,hb⟩
   · exact Or.inr (Or.inl hb)
   · exact Or.inr (Or.inr hb)
 have z1a0:∀ a∈S,s - 2≤ K.degree a:=by
   intro a ha
   have:=zcf (z78 a ha)
   have:=z27 a
   omega
 obtain ⟨v,p,hp,hmax⟩:=z95 K x
 have hpS:=z67 p hxS
 have hvS:=hpS v p.end_mem_support
 have z1b4:∀ {a b:V},H.Adj a y → H.Adj a z → 
     (q:K.Walk a b) → q.IsPath → a∈S → ℓ≤ q.length+1 → 
     ∃ y z,χ y≠χ z ∧ ∃ r:H.Walk y z,r.IsPath∧r.length=ℓ:=by
   intro a b hay haz q hq ha hlen
   have hqS:=z67 q ha
   apply z112 χ hay haz hyzcol (q.mapLe hKH) (hq.mapLe hKH)
   · intro h
     exact hyS (hqS y (by simpa using h))
   · intro h
     exact hzS (hqS z (by simpa using h))
   · exact hℓ
   · simpa using hlen
 by_cases hlen: ℓ≤ p.length+1
 · exact z1b4 hxy hxz p hp hxS hlen
 have z11e: 0 < p.length:=by
   have z21e:(p.support.toFinset:Set V).ncard=p.length+1:=by
     simp only [Set.ncard_coe_finset,List.toFinset_card_of_nodup hp.support_nodup,
       SimpleGraph.Walk.length_support]
   have hnbp:=z19 p hp hmax
   have hc:=z29 (G:=K) (v:=v)
     (S:=(p.support.toFinset:Set V)) (by simp)
     (fun w hw => by simpa using hnbp w hw)
   have:=z1a0 v hvS
   omega
 let E:=z10 K x p.support
 have hES:E⊆S:=fun e he => hpS e (z4f he)
 have hcl:K.IsClique E:=by
   apply z161 p hp hmax
   intro a ha b hb hab hnab
   have haS:=hES ha
   have hbS:=hES hb
   have z203:¬ H.Adj a b:=fun h => hnab ⟨h,haS,hbS⟩
   have hI:({a,b}:Set V)⊆S:=by
     intro c hc
     rcases Set.mem_insert_iff.mp hc with hc | hc
     · exact hc ▸ haS
     · exact (Set.mem_singleton_iff.mp hc) ▸ hbS
   have hsub:=za3 hI z1e
   have hc:=Set.ncard_le_ncard hsub
   have hc₁:=Set.ncard_insert_le y (insert z (z0 K {a,b}))
   have hc₂:=Set.ncard_insert_le z (z0 K {a,b})
   have he:=z9f a b hab z203
   change (z0 H {a,b}).ncard ≤
     (insert y (insert z (z0 K {a,b}))).ncard at hc
   omega
 have hclH:H.IsClique E:=fun a ha b hb hab => hKH (hcl ha hb hab)
 have z1b2:∀ e∈E,K.degree e≤ E.ncard:=by
   intro e he
   obtain ⟨q,hq,zc⟩:=he
   apply z6d q hq zc
   intro a hea
   exact zc.mem_iff.mpr (z72 p hmax ⟨q,hq,zc⟩ a hea)
 have hvE:v∈E:=⟨p,hp,.refl _⟩
 have z1c0:s - 2≤ E.ncard:=(z1a0 v hvS).trans (z1b2 v hvE)
 obtain ⟨k,zb1,hk,z40⟩:=zaa p hp (.refl _) hcl
   (by simp only [SimpleGraph.Walk.length_support]; omega)
 let u:=p.getVert (k - 1)
 let w₀:=p.getVert k
 have huS:u∈S:=hpS u (p.getVert_mem_support _)
 have huE:u∉E:=by
   intro hu
   have:=(z40 (k - 1) (by omega)).mp hu
   omega
 have hw₀:w₀∈E:=(z40 k hk).mpr le_rfl
 have huw₀:K.Adj u w₀:=by
   have:=p.adj_getVert_succ (show k - 1 < p.length by omega)
   simpa only [Nat.sub_add_cancel zb1] using this
 have hyE:y∉E:=fun h => hyS (hES h)
 have hzE:z∉E:=fun h => hzS (hES h)
 have huy:u≠y:=fun heq => hyS (heq ▸ huS)
 have huz:u≠z:=fun heq => hzS (heq ▸ huS)
 have z1b1:∀ e∈E,∀ b,H.Adj e b → K.Adj e b∨b=y∨b=z :=
   fun e he => z78 e (hES he)
 obtain ⟨w₁,hw₁,hw₁ne,huw₁⟩:=zdc hs z37 z27
   hclH z1c0 hw₀ huE hyE hzE huy huz z1b1
   (fun e he hne => z5d p hp hmax hcl zb1 hk z40 he hne) z1b2
 have z44:=z64 p hp hmax hcl zb1 hk z40
   hw₁ hw₁ne huw₁
 obtain ⟨w,hw,hwy,hwz⟩:=zbb hs z37 z27
   hclH z1c0 huE hyE hzE z1b1 z44 hKH
 have z103:∃ e∈E,e≠w∧K.Adj e u:=by
   by_cases hww₀:w=w₀
   · exact ⟨w₁,hw₁,fun heq => hw₁ne (heq.trans hww₀),huw₁.symm⟩
   · exact ⟨w₀,hw₀,Ne.symm hww₀,huw₀.symm⟩
 obtain ⟨b,q,hq,z65⟩:=zf0 hs z37 z27 z9f
   ⟨huS,huE⟩ hw hyS hzS hES hclH hSconn z1e z44 z103
 exact z1b4 hwy hwz q hq (hES hw) (z1bd.trans z65)
end CycleClique
namespace CycleClique
open scoped SimpleGraph
theorem z7a {V:Type*} {G:SimpleGraph V}
   (z37:¬ (⊤ :SimpleGraph (Fin 3))⊑G) (v:V) :
   Gᶜ.IsClique (G.neighborSet v):=by
 classical
 intro a ha b hb hab
 refine ⟨hab,fun hadj => ?_⟩
 have hc:G.IsNClique 3 {v,a,b} :=
   SimpleGraph.is3Clique_triple_iff.mpr ⟨ha,hb,hadj⟩
 exact z37 ((SimpleGraph.not_cliqueFree_iff_top_isContained 3).mp hc.not_cliqueFree)
theorem RamseyProperty.mono {m n N M:ℕ} (h:RamseyProperty m n N) (hNM:N≤ M) :
   RamseyProperty m n M:=by
 intro G
 let f:Fin N → Fin M:=Fin.castLE hNM
 let H:=G.comap f
 have hc:H⊑G:=⟨⟨⟨f,fun {a b} hab => hab⟩,Fin.castLE_injective hNM⟩⟩
 have hcc:Hᶜ⊑Gᶜ:=by
   refine ⟨⟨⟨f,fun {a b} hab => ?_⟩,Fin.castLE_injective hNM⟩⟩
   exact ⟨fun heq => hab.1 (Fin.castLE_injective hNM heq),hab.2⟩
 rcases h H with hcycle | z20
 · exact Or.inl (hcycle.trans hc)
 · exact Or.inr (z20.trans hcc)
end CycleClique
namespace CycleClique
open scoped SimpleGraph
noncomputable def independence {V:Type*} (G:SimpleGraph V) (S:Set V):ℕ :=
 (G.induce S).indepNum
theorem z3d {V:Type*} [Fintype V] {G:SimpleGraph V}
   {I:Set V} (hI:G.IsIndepSet I):I.ncard≤ G.indepNum:=by
 classical
 have hc:=(show G.IsIndepSet (I.toFinset:Set V) by simpa using hI).card_le_indepNum
 rwa [← Set.ncard_eq_toFinset_card'] at hc
theorem z6 {V:Type*} [Fintype V] (G:SimpleGraph V)
   (S:Set V):∃ I⊆S,G.IsIndepSet I∧I.ncard=independence G S:=by
 classical
 obtain ⟨J,hJ⟩:=(G.induce S).exists_isNIndepSet_indepNum
 refine ⟨Subtype.val '' (J:Set S),?_,?_,?_⟩
 · rintro v ⟨w,_,rfl⟩
   exact w.property
 · rintro a ⟨x,hx,rfl⟩ b ⟨y,hy,rfl⟩ hxy hab
   exact hJ.isIndepSet hx hy (fun heq => hxy (congrArg Subtype.val heq)) hab
 · rw [Set.ncard_image_of_injective _ Subtype.val_injective,Set.ncard_coe_finset]
   exact hJ.card_eq
theorem z15 {V:Type*} [Fintype V] {G:SimpleGraph V}
   {I S:Set V} (hI:G.IsIndepSet I) (hIS:I⊆S):I.ncard≤ independence G S:=by
 classical
 let J:Set S:=Subtype.val ⁻¹' I
 have hJ:(G.induce S).IsIndepSet J:=by
   intro a ha b hb hab hadj
   exact hI ha hb (fun h => hab (Subtype.ext h)) hadj
 have heq:Subtype.val '' J=I:=by
   ext v
   constructor
   · rintro ⟨w,hw,rfl⟩
     exact hw
   · intro hv
     exact ⟨⟨v,hIS hv⟩,hv,rfl⟩
 have hc:=z3d hJ
 rw [← Set.ncard_image_of_injective J Subtype.val_injective,heq] at hc
 exact hc
theorem z76 {V:Type*} [Fintype V] {G:SimpleGraph V}
   {S T:Set V} (hST:S⊆T):independence G S≤ independence G T:=by
 obtain ⟨I,hIS,hI,z3b⟩:=z6 G S
 rw [← z3b]
 exact z15 hI (hIS.trans hST)
theorem z140 {V:Type*} [Fintype V] (G:SimpleGraph V) (S:Set V) :
   independence G S≤ S.ncard:=by
 obtain ⟨I,hIS,_,z3b⟩:=z6 G S
 rw [← z3b]
 exact Set.ncard_le_ncard hIS
theorem z14 {V:Type*} [Fintype V] {G:SimpleGraph V} {S:Set V}
   (hS:S.Nonempty): 0 < independence G S:=by
 obtain ⟨x,hx⟩:=hS
 have hI:G.IsIndepSet {x}:=Set.pairwise_singleton _ _
 have hc:=z15 hI (Set.singleton_subset_iff.mpr hx)
 simp only [Set.ncard_singleton] at hc
 omega
theorem z31 {V:Type*} [Fintype V] (G:SimpleGraph V) :
   independence G Set.univ=G.indepNum:=by
 classical
 apply le_antisymm
 · obtain ⟨I,_,hI,z3b⟩:=z6 G Set.univ
   rw [← z3b]
   exact z3d hI
 · obtain ⟨I,hI⟩:=G.exists_isNIndepSet_indepNum
   have hc:=z15 hI.isIndepSet (Set.subset_univ _)
   simpa only [Set.ncard_coe_finset,hI.card_eq] using hc
theorem z5c {V:Type*} [Fintype V] {G:SimpleGraph V}
   {I S:Set V} (hI:G.IsIndepSet I) (hIS:I⊆S) :
   independence G (S \ z0 G I)+I.ncard≤ independence G S:=by
 classical
 obtain ⟨J,hJsub,hJ,hJcard⟩:=z6 G
   (S \ z0 G I)
 have z1fe:Disjoint J I:=Set.disjoint_left.mpr (by
   intro v hv hi
   exact (hJsub hv).2 (Or.inl hi))
 have hJI:G.IsIndepSet (J∪I):=by
   intro a ha b hb hab hadj
   rcases ha with ha | ha <;> rcases hb with hb | hb
   · exact hJ ha hb hab hadj
   · exact (hJsub ha).2 (Or.inr ⟨b,hb,hadj.symm⟩)
   · exact (hJsub hb).2 (Or.inr ⟨a,ha,hadj⟩)
   · exact hI ha hb hab hadj
 have hc:=z15 hJI (Set.union_subset (fun _ h => (hJsub h).1) hIS)
 rwa [Set.ncard_union_eq z1fe,hJcard] at hc
theorem z8b {V:Type*} [Fintype V] (G:SimpleGraph V) (a:ℕ) :
   (¬ (⊤ :SimpleGraph (Fin (a+1)))⊑Gᶜ)↔G.indepNum≤ a:=by
 classical
 constructor
 · intro h
   obtain ⟨I,hI⟩:=G.exists_isNIndepSet_indepNum
   have hc:=z35 h ((SimpleGraph.isClique_compl G).mpr hI.isIndepSet)
   simp only [Set.ncard_coe_finset,hI.card_eq] at hc
   omega
 · intro h hc
   apply hc.not_cliqueFree
   intro I hI
   have hi:=(SimpleGraph.isNClique_compl G).mp hI
   have hb:=hi.isIndepSet.card_le_indepNum
   rw [hi.card_eq] at hb
   omega
end CycleClique
namespace CycleClique
open scoped SimpleGraph
theorem za7 {V:Type*} {G:SimpleGraph V} {S:Set V} {I:Set S} :
   (G.induce S).IsIndepSet I↔G.IsIndepSet (Subtype.val '' I):=by
 constructor
 · intro h a ha b hb hab hadj
   obtain ⟨x,hx,rfl⟩:=ha
   obtain ⟨y,hy,rfl⟩:=hb
   exact h hx hy (fun heq => hab (congrArg Subtype.val heq)) hadj
 · intro h a ha b hb hab hadj
   exact h ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩ (fun heq => hab (Subtype.ext heq)) hadj
theorem zf8 {V:Type*} [Fintype V] (G:SimpleGraph V)
   (S:Set V) (T:Set S) :
   independence (G.induce S) T=independence G (Subtype.val '' T):=by
 classical
 apply le_antisymm
 · obtain ⟨I,hIT,hI,hc⟩:=z6 (G.induce S) T
   have hb:=z15 (za7.mp hI) (Set.image_mono hIT)
   rwa [Set.ncard_image_of_injective _ Subtype.val_injective,hc] at hb
 · obtain ⟨I,hIT,hI,hc⟩:=z6 G (Subtype.val '' T)
   let J:Set S:=Subtype.val ⁻¹' I
   have heq:Subtype.val '' J=I:=by
     ext v
     constructor
     · rintro ⟨w,hw,rfl⟩
       exact hw
     · intro hv
       obtain ⟨w,_,rfl⟩:=hIT hv
       exact ⟨w,hv,rfl⟩
   have hJ:(G.induce S).IsIndepSet J:=za7.mpr (heq ▸ hI)
   have hJT:J⊆T:=by
     intro x hx
     obtain ⟨y,hy,hxy⟩:=hIT hx
     exact Subtype.val_injective hxy ▸ hy
   have hb:=z15 hJ hJT
   rw [← Set.ncard_image_of_injective J Subtype.val_injective,heq,hc] at hb
   exact hb
theorem z8a {V:Type*} [Fintype V] {G:SimpleGraph V}
   {A B S:Set V} (hA:A⊆S) (hB:B⊆S) (hdis:Disjoint A B)
   (z1c1:∀ a∈A,∀ b∈B,¬ G.Adj a b) :
   independence G A+independence G B≤ independence G S:=by
 classical
 obtain ⟨I,hIA,hI,hcI⟩:=z6 G A
 obtain ⟨J,hJB,hJ,hcJ⟩:=z6 G B
 have hdIJ:Disjoint I J:=hdis.mono hIA hJB
 have hIJ:G.IsIndepSet (I∪J):=by
   intro a ha b hb hab hadj
   rcases ha with ha | ha <;> rcases hb with hb | hb
   · exact hI ha hb hab hadj
   · exact z1c1 a (hIA ha) b (hJB hb) hadj
   · exact z1c1 b (hIA hb) a (hJB ha) hadj.symm
   · exact hJ ha hb hab hadj
 have hc:=z15 hIJ (Set.union_subset (hIA.trans hA) (hJB.trans hB))
 rwa [Set.ncard_union_eq hdIJ,hcI,hcJ] at hc
theorem zf {V:Type*} [Fintype V] {G:SimpleGraph V}
   {S:Set V} (hα:independence G S≤1):G.IsClique S:=by
 intro a ha b hb hab
 by_contra hn
 have hI:G.IsIndepSet {a,b}:=by
   intro x hx y hy hxy z70
   simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
   rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
   · exact hxy rfl
   · exact hn z70
   · exact hn z70.symm
   · exact hxy rfl
 have hc:=z15 hI (Set.insert_subset ha (Set.singleton_subset_iff.mpr hb))
 rw [Set.ncard_pair hab] at hc
 omega
theorem zcd {V:Type*} [Fintype V] {G:SimpleGraph V}
   (hbip:G.IsBipartite):Fintype.card V≤2*G.indepNum:=by
 classical
 obtain ⟨χ⟩:=hbip
 have z1d9:=z3d (χ.isIndepSet_colorClass (0:Fin 2))
 have hone:=z3d (χ.isIndepSet_colorClass (1:Fin 2))
 have z1f3: χ.colorClass 0∪χ.colorClass 1=Set.univ:=by
   ext v
   simp only [Set.mem_union,SimpleGraph.Coloring.colorClass,Set.mem_ofPred_eq,Set.mem_univ,iff_true]
   have:=(χ v).isLt
   omega
 have hdis:Disjoint (χ.colorClass 0) (χ.colorClass 1):=by
   apply Set.disjoint_left.mpr
   intro v hv₀ hv₁
   have z1d9: χ v=0:=hv₀
   have hone: χ v=1:=hv₁
   exact (by decide:(0:Fin 2)≠1) (z1d9.symm.trans hone)
 have hc:=Set.ncard_union_eq hdis
 rw [z1f3,Set.ncard_univ,Nat.card_eq_fintype_card] at hc
 omega
theorem z36 {V:Type*} [Fintype V]
   (G:SimpleGraph V) [DecidableRel G.Adj] (v:V) :
   (z0 G {v}).ncard=G.degree v+1:=by
 have heq:z0 G {v}=insert v (G.neighborSet v):=by
   ext w
   simp [z0,SimpleGraph.mem_neighborSet]
 rw [heq,Set.ncard_insert_of_notMem G.notMem_neighborSet_self,z28]
end CycleClique
namespace CycleClique
open scoped SimpleGraph
def z43 {V:Type*} (G:SimpleGraph V) (s ε:ℕ):Prop :=
 (s*G.indepNum+ε≤ Nat.card V) ∧
 ∀ T:Set V,T.Nonempty → T.ncard < Nat.card V → 
   T.ncard < s*independence G T+ε
theorem zfb {V:Type*} [Fintype V] [Nonempty V]
   {G:SimpleGraph V} {s ε:ℕ} (hε: ε≤1) (z85:z43 G s ε) :
   G.Connected:=by
 classical
 simp only [z43,Nat.card_eq_fintype_card] at z85
 obtain ⟨r⟩:= ‹Nonempty V›
 rw [SimpleGraph.connected_iff_exists_forall_reachable]
 refine ⟨r,fun w => ?_⟩
 by_contra hw
 let A:Set V:={v | G.Reachable r v}
 have hrA:r∈A:=SimpleGraph.Reachable.refl r
 have hwA:w∈Aᶜ:=hw
 have hsum:=Set.ncard_add_ncard_compl A
 rw [Nat.card_eq_fintype_card] at hsum
 have z21f: 0 < A.ncard:=(Set.ncard_pos).mpr ⟨r,hrA⟩
 have z220: 0 < Aᶜ.ncard:=(Set.ncard_pos).mpr ⟨w,hwA⟩
 have hA:=z85.2 A ⟨r,hrA⟩ (by omega)
 have hB:=z85.2 Aᶜ ⟨w,hwA⟩ (by omega)
 have hα:=z8a (G:=G) (Set.subset_univ A) (Set.subset_univ Aᶜ)
   disjoint_compl_right (by
     intro a ha b hb hab
     exact hb (ha.trans hab.reachable))
 rw [z31] at hα
 have hmul:=Nat.mul_le_mul_left s hα
 have hd:=z85.1
 nlinarith
theorem z8f {V:Type*} [Fintype V] {G:SimpleGraph V}
   {s ε:ℕ} (z85:z43 G s ε)
   {I:Set V} (hI:G.IsIndepSet I) (hne:I.Nonempty) :
   s*I.ncard≤(z0 G I).ncard ∧
   ((0 < ε∨(z0 G I)ᶜ.Nonempty) → 
     s*I.ncard < (z0 G I).ncard):=by
 classical
 simp only [z43,Nat.card_eq_fintype_card] at z85
 let N:=z0 G I
 have z223: 0 < N.ncard:=(Set.ncard_pos).mpr (hne.mono (fun _ h => Or.inl h))
 have hsum:=Set.ncard_add_ncard_compl N
 rw [Nat.card_eq_fintype_card] at hsum
 have hα:=z5c hI (Set.subset_univ I)
 rw [z31,← Set.compl_eq_univ_sdiff] at hα
 have hm:=Nat.mul_le_mul_left s hα
 have hd:=z85.1
 by_cases hR:Nᶜ.Nonempty
 · have hr:=z85.2 Nᶜ hR (by omega)
   have z15a:s*I.ncard < N.ncard:=by nlinarith
   exact ⟨z15a.le,fun _ => z15a⟩
 · have z219:Nᶜ.ncard=0:=(Set.ncard_eq_zero).mpr (Set.not_nonempty_iff_eq_empty.mp hR)
   refine ⟨?_,?_⟩
   · nlinarith
   · rintro (he | hn)
     · nlinarith
     · exact False.elim (hR hn)
theorem z126 {V:Type*} [Fintype V] (G:SimpleGraph V)
   (s ε:ℕ) {D:Set V} (hne:D.Nonempty)
   (hd:s*independence G D+ε≤ D.ncard) :
   ∃ S⊆D,S.Nonempty∧z43 (G.induce S) s ε:=by
 classical
 let A:Set ℕ:={n | ∃ S⊆D,S.Nonempty ∧
   s*independence G S+ε≤ S.ncard∧S.ncard=n}
 have hA:A.Nonempty:=⟨D.ncard,D,Set.Subset.rfl,hne,hd,rfl⟩
 obtain ⟨S,hSD,hS,hdS,hcS⟩:=Nat.sInf_mem hA
 refine ⟨S,hSD,hS,?_,?_⟩
 · simpa [independence,← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] using hdS
 · intro T hT hlt
   by_contra hn
   have him:Subtype.val '' T⊆D:=by
     rintro x ⟨y,hy,rfl⟩
     exact hSD y.property
   have z3b:(Subtype.val '' T).ncard=T.ncard :=
     Set.ncard_image_of_injective _ Subtype.val_injective
   have hm:(Subtype.val '' T).ncard∈A:=by
     refine ⟨Subtype.val '' T,him,hT.image _,?_,rfl⟩
     rw [← zf8,z3b]
     omega
   have hmin:=Nat.sInf_le hm
   rw [z3b,← hcS] at hmin
   have hSc:S.ncard=Nat.card S:=(Nat.card_coe_set_eq S).symm
   omega
theorem zd8 {V:Type*} [Fintype V] [Nonempty V]
   {G:SimpleGraph V} {s ε:ℕ} (hd:z43 G s ε)
   (z37:¬ (⊤ :SimpleGraph (Fin s))⊑G): 2≤ G.indepNum:=by
 classical
 have hpos: 0 < G.indepNum:=by
   simpa [z31] using
     (z14 (G:=G) (S:=Set.univ) Set.univ_nonempty)
 by_contra hn
 have ha:G.indepNum=1:=by omega
 have hcl:G.IsClique Set.univ:=zf (by
   rw [z31,ha])
 have hlt:=z35 z37 hcl
 rw [Set.ncard_univ,Nat.card_eq_fintype_card] at hlt
 have hc:=hd.1
 rw [ha,Nat.mul_one,Nat.card_eq_fintype_card] at hc
 omega
theorem ze8 {V:Type*} [Fintype V] [Nonempty V]
   {G:SimpleGraph V} {s ε:ℕ} [DecidableRel G.Adj] (hs: 4≤ s) (hε: ε≤1)
   (hd:z43 G s ε) (z37:¬ (⊤ :SimpleGraph (Fin s))⊑G) :
   G.Connected ∧ ¬ G.IsBipartite∧2*s+ε≤ Fintype.card V ∧
   (∀ v,s≤ G.degree v) ∧
   (∀ I,G.IsIndepSet I → I.Nonempty → 
     s*I.ncard≤(z0 G I).ncard ∧
     ((0 < ε∨(z0 G I)ᶜ.Nonempty) → 
       s*I.ncard < (z0 G I).ncard)):=by
 classical
 have hcV:Nat.card V=Fintype.card V:=Nat.card_eq_fintype_card
 have hα:=zd8 hd z37
 have z79: 2*s+ε≤ Fintype.card V:=by
   have:=hd.1
   nlinarith
 refine ⟨zfb hε hd,?_,z79,?_,
   fun I hI hne => z8f hd hI hne⟩
 · intro hbip
   have z17a:=zcd hbip
   have z1c6:=hd.1
   nlinarith
 · intro v
   have hexp:=z8f hd
     (show G.IsIndepSet {v} from Set.pairwise_singleton _ _) (Set.singleton_nonempty v)
   simp only [Set.ncard_singleton,Nat.mul_one,z36] at hexp
   by_cases hR:(z0 G {v})ᶜ.Nonempty
   · have:=hexp.2 (Or.inr hR)
     omega
   · have hN:z0 G {v}=Set.univ:=by
       apply Set.eq_univ_of_forall
       intro w
       by_contra hw
       exact hR ⟨w,hw⟩
     have hc:=z36 G v
     rw [hN,Set.ncard_univ,Nat.card_eq_fintype_card] at hc
     omega
end CycleClique
namespace CycleClique
open scoped SimpleGraph
theorem z9b {V:Type*} [Fintype V] {ι:Type*}
   (D: ι → Set V) (hdis:Pairwise (fun i j => Disjoint (D i) (D j)))
   (F:Finset ι):(⋃ i∈F,D i).ncard = ∑ i∈F,(D i).ncard:=by
 classical
 induction F using Finset.induction_on with
 | empty => simp
 | @insert i F hi ih =>
   have hu:(⋃ j∈insert i F,D j)=D i ∪ ⋃ j∈F,D j:=by
     simp only [Finset.mem_insert,Set.iUnion_iUnion_eq_or_left]
   rw [hu,Set.ncard_union_eq,Finset.sum_insert hi,ih]
   apply Set.disjoint_left.mpr
   intro v hvi hvF
   obtain ⟨j,hj,hvj⟩:=Set.mem_iUnion₂.mp hvF
   exact Set.disjoint_left.mp (hdis (by intro he; subst j; exact hi hj)) hvi hvj
theorem z6f {V:Type*} [Fintype V] {ι:Type*}
   (G:SimpleGraph V) (D: ι → Set V)
   (hdis:Pairwise (fun i j => Disjoint (D i) (D j)))
   (F:Finset ι)
   (hsep:∀ i∈F,∀ j∈F,i≠j → 
     ∀ x∈D i,∀ y∈D j,¬ G.Adj x y) :
   ∑ i∈F,independence G (D i)≤ independence G (⋃ i∈F,D i):=by
 classical
 revert hsep
 induction F using Finset.induction_on with
 | empty => simp
 | @insert i F hi ih =>
   intro hsep
   have hu:(⋃ j∈insert i F,D j)=D i ∪ ⋃ j∈F,D j:=by
     simp only [Finset.mem_insert,Set.iUnion_iUnion_eq_or_left]
   rw [hu,Finset.sum_insert hi]
   have hD:Disjoint (D i) (⋃ j∈F,D j):=by
     apply Set.disjoint_left.mpr
     intro v hvi hvF
     obtain ⟨j,hj,hvj⟩:=Set.mem_iUnion₂.mp hvF
     exact Set.disjoint_left.mp (hdis (by intro he; subst j; exact hi hj)) hvi hvj
   calc
     _≤ independence G (D i)+independence G (⋃ j∈F,D j):=by
       exact Nat.add_le_add_left (ih (fun j hj l hl hne =>
         hsep j (Finset.mem_insert_of_mem hj) l (Finset.mem_insert_of_mem hl) hne)) _
     _≤_:=z8a Set.subset_union_left Set.subset_union_right hD (by
       intro x hx y hy
       obtain ⟨j,hj,hyj⟩:=Set.mem_iUnion₂.mp hy
       exact hsep i (Finset.mem_insert_self _ _) j (Finset.mem_insert_of_mem hj)
         (by intro he; subst j; exact hi hj) x hx y hyj)
def z8 {V:Type*} (G:SimpleGraph V) (r:V) (i:ℕ):Set V :=
 {v | G.Reachable r v∧G.dist r v=i}
@[simp] theorem distanceLayer_zero {V:Type*} (G:SimpleGraph V) (r:V) :
   z8 G r 0={r}:=by
 ext v
 constructor
 · rintro ⟨hr,hd⟩
   exact (hr.dist_eq_zero_iff.mp hd).symm
 · rintro rfl
   exact ⟨.refl _,G.dist_self⟩
theorem z74 {V:Type*} (G:SimpleGraph V) (r:V) :
   Pairwise (fun i j => Disjoint (z8 G r i) (z8 G r j)):=by
 intro i j hij
 apply Set.disjoint_left.mpr
 intro v hv₁ hv₂
 exact hij (hv₁.2.symm.trans hv₂.2)
theorem zb7 {V:Type*} {G:SimpleGraph V} {r:V}
   {i j:ℕ} (hne:i≠j) (hpar:i % 2=j % 2)
   {x y:V} (hx:x∈z8 G r i) (hy:y∈z8 G r j) :
   ¬ G.Adj x y:=by
 intro hxy
 have hd:=hxy.diff_dist_adj (u:=r)
 rw [hx.2,hy.2] at hd
 omega
def z32 (i:ℕ):Finset ℕ :=
 (Finset.range (i+1)).filter (fun j => j % 2=i % 2)
def z1f (α:ℕ → ℕ) (i:ℕ):ℕ:= ∑ j∈z32 i,α j
@[simp] theorem paritySum_zero (α:ℕ → ℕ):z1f α 0=α 0:=by
 simp [z1f,z32,Finset.sum_filter]
theorem z157 (α:ℕ → ℕ) {i:ℕ} (hi: 1≤ i) :
   z1f α i+z1f α (i - 1) = ∑ j∈Finset.range (i+1),α j:=by
 unfold z1f z32
 rw [Finset.sum_filter,Finset.sum_filter]
 have hip:i - 1+1=i:=by omega
 rw [hip]
 have hpar:i % 2≠(i - 1) % 2:=by omega
 have hex:(∑ j∈Finset.range i,if j % 2=(i - 1) % 2 then α j else 0) =
     ∑ j∈Finset.range (i+1),if j % 2=(i - 1) % 2 then α j else 0:=by
   rw [Finset.sum_range_succ,if_neg hpar,Nat.add_zero]
 rw [hex,← Finset.sum_add_distrib]
 apply Finset.sum_congr rfl
 intro j hj
 by_cases he:j % 2=i % 2
 · have hne:j % 2≠(i - 1) % 2:=by omega
   simp only [if_pos he,if_neg hne,Nat.add_zero]
 · have he' :j % 2=(i - 1) % 2:=by omega
   simp only [if_neg he,if_pos he',Nat.zero_add]
theorem zfc {V:Type*} [Fintype V] (G:SimpleGraph V)
   (r:V) (i:ℕ) :
   z1f (fun j => independence G (z8 G r j)) i≤ G.indepNum:=by
 apply le_trans (z6f G (z8 G r)
   (z74 G r) (z32 i) ?_)
 · simpa [z31] using
     (z76 (G:=G) (Set.subset_univ (⋃ j∈z32 i,z8 G r j)))
 · intro j hj l hl hne x hx y hy
   simp only [z32,Finset.mem_filter,Finset.mem_range] at hj hl
   exact zb7 hne (hj.2.trans hl.2.symm) hx hy
@[simp] theorem independence_singleton {V:Type*} [Fintype V] (G:SimpleGraph V)
   (v:V):independence G {v}=1:=by
 have hp:=z14 (G:=G) (Set.singleton_nonempty v)
 have hc:=z140 G {v}
 simp only [Set.ncard_singleton] at hc
 omega
theorem z84 {V:Type*} [Fintype V] {G:SimpleGraph V}
   {k:ℕ} (hk: 1≤ k)
   (hexp:∀ I,G.IsIndepSet I → I.Nonempty → 
     k*I.ncard+1≤(z0 G I).ncard) (r:V) :
   (z8 G r 1).Nonempty:=by
 classical
 have h:=hexp {r} (Set.pairwise_singleton _ _) (Set.singleton_nonempty r)
 simp only [Set.ncard_singleton,Nat.mul_one,z36] at h
 have hpos: 0 < (G.neighborSet r).ncard:=by
   rw [z28]
   omega
 obtain ⟨v,hv⟩:=(Set.ncard_pos).mp hpos
 have hr:G.Adj r v:=hv
 exact ⟨v,hr.reachable,G.dist_eq_one_iff_adj.mpr hr⟩
theorem ze0 {V:Type*} {G:SimpleGraph V} {r:V}
   (hD:(z8 G r 1).Nonempty) (i:ℕ) :
   (⋃ j∈z32 i,z8 G r j).Nonempty:=by
 by_cases hi:i % 2=0
 · refine ⟨r,Set.mem_iUnion₂.mpr ⟨0,?_,?_⟩⟩
   · simp [z32,hi]
   · simp
 · obtain ⟨v,hv⟩:=hD
   refine ⟨v,Set.mem_iUnion₂.mpr ⟨1,?_,hv⟩⟩
   simp only [z32,Finset.mem_filter,Finset.mem_range]
   omega
theorem zb2 {V:Type*} {G:SimpleGraph V}
   {r:V} {i:ℕ} {I:Set V}
   (hI:I ⊆ ⋃ j∈z32 i,z8 G r j) :
   z0 G I ⊆ ⋃ j∈Finset.range (i+2),z8 G r j:=by
 intro v hv
 rcases hv with hv | ⟨w,hw,hwv⟩
 · obtain ⟨j,hj,hvj⟩:=Set.mem_iUnion₂.mp (hI hv)
   have hji:j < i+1:=(Finset.mem_filter.mp hj).1 |> Finset.mem_range.mp
   exact Set.mem_iUnion₂.mpr ⟨j,Finset.mem_range.mpr (by omega),hvj⟩
 · obtain ⟨j,hj,hwj⟩:=Set.mem_iUnion₂.mp (hI hw)
   have hji:j < i+1:=(Finset.mem_filter.mp hj).1 |> Finset.mem_range.mp
   have hd:=hwv.diff_dist_adj (u:=r)
   rw [hwj.2] at hd
   exact Set.mem_iUnion₂.mpr ⟨G.dist r v,Finset.mem_range.mpr (by omega),
     hwj.1.trans hwv.reachable,rfl⟩
theorem z14f {V:Type*} [Fintype V] {G:SimpleGraph V}
   {k:ℕ} (hk: 1≤ k)
   (hexp:∀ I,G.IsIndepSet I → I.Nonempty → 
     k*I.ncard+1≤(z0 G I).ncard)
   (r:V) {i:ℕ} (hi: 1≤ i) :
   k*z1f (fun j => independence G (z8 G r j)) (i - 1) ≤
     ∑ j∈Finset.range i,(z8 G r (j+1)).ncard:=by
 classical
 let U:= ⋃ j∈z32 (i - 1),z8 G r j
 have hUne:=ze0 (z84 hk hexp r) (i - 1)
 obtain ⟨I,hIU,hI,hcI⟩:=z6 G U
 have hneI:I.Nonempty:=(Set.ncard_pos).mp (by
   rw [hcI]
   exact z14 hUne)
 have hp:z1f (fun j => independence G (z8 G r j)) (i - 1) ≤
     independence G U:=by
   apply z6f G (z8 G r) (z74 G r)
   intro j hj l hl hne x hx y hy
   simp only [z32,Finset.mem_filter,Finset.mem_range] at hj hl
   exact zb7 hne (hj.2.trans hl.2.symm) hx hy
 have hN:=zb2 hIU
 have z3b:=Set.ncard_le_ncard hN
 rw [z9b _ (z74 G r)] at z3b
 have hii:i - 1+2=i+1:=by omega
 rw [hii,Finset.sum_range_succ',distanceLayer_zero,Set.ncard_singleton] at z3b
 have he:=hexp I hI hneI
 have hm:=Nat.mul_le_mul_left k hp
 rw [← hcI] at hm
 omega
theorem ze5 (α n:ℕ → ℕ) {s ε:ℕ}
   (hs: 4≤ s) (hε: ε≤1) (hα₀: α 0=1) (hn₁: 0 < n 1)
   (z1dd:∀ i,z1f α i≤2*s+ε)
   (z1c5:∀ i,1≤ i → i≤ s → 
     (2*s+ε)*z1f α (i - 1) ≤ ∑ j∈Finset.range i,n (j+1)) :
   ∃ i,1≤ i∧i≤ s∧0 < n i∧s*α i+ε≤ n i:=by
 classical
 by_contra hn
 push Not at hn
 have z1d8:∀ i,1≤ i → i≤ s → n i≤ s*α i:=by
   intro i hi his
   by_cases hni: 0 < n i
   · have:=hn i hi his hni
     omega
   · omega
 have hsum:∀ i,1≤ i → i≤ s → 
     (∑ j∈Finset.range i,n (j+1))≤ s * ∑ j∈Finset.range i,α (j+1):=by
   intro i hi his
   rw [Finset.mul_sum]
   apply Finset.sum_le_sum
   intro j hj
   have hj' :=Finset.mem_range.mp hj
   exact z1d8 (j+1) (by omega) (by omega)
 have z15a: ε=0 → ∀ i,1≤ i → i≤ s → 
     (∑ j∈Finset.range i,n (j+1)) < s * ∑ j∈Finset.range i,α (j+1):=by
   intro he i hi his
   rw [Finset.mul_sum]
   apply Finset.sum_lt_sum
   · intro j hj
     have hj' :=Finset.mem_range.mp hj
     exact z1d8 (j+1) (by omega) (by omega)
   · refine ⟨0,Finset.mem_range.mpr (by omega),?_⟩
     have:=hn 1 (by omega) (by omega) hn₁
     simpa [he] using this
 have hid:∀ i,1≤ i → 
     (∑ j∈Finset.range i,α (j+1))+1=z1f α i+z1f α (i - 1):=by
   intro i hi
   have h:=z157 α hi
   rw [Finset.sum_range_succ',hα₀] at h
   exact h.symm
 have z13f:∀ i,1≤ i → i≤ s → 0 < z1f α (i - 1) → 
     z1f α (i - 1)+2≤ z1f α i:=by
   intro i hi his hp
   have hl:=z1c5 i hi his
   have hw:=hsum i hi his
   have heq:=hid i hi
   by_contra hbad
   have z1b8:=Nat.mul_le_mul_left s
     (show z1f α i≤ z1f α (i - 1)+1 by omega)
   by_cases he: ε=0
   · have hst:=z15a he i hi his
     rw [he,Nat.add_zero] at hl
     nlinarith
   · have he₁: ε=1:=by omega
     rw [he₁] at hl
     nlinarith
 have z1b3:∀ i,i≤ s → 2*i+1≤ z1f α i:=by
   intro i
   induction i with
   | zero => simp [hα₀]
   | succ i ih =>
     intro his
     have hi:=ih (by omega)
     have hst:=z13f (i+1) (by omega) his (by simpa using (show 0 < z1f α i by omega))
     simp only [Nat.add_sub_cancel] at hst
     omega
 have z17a:=z1dd s
 by_cases he: ε=0
 · have:=z1b3 s (by omega)
   omega
 · have he₁: ε=1:=by omega
   have z19d:=z1b3 (s - 1) (by omega)
   have z227:s < z1f α (s - 1):=by omega
   have z11c:z1f α (s - 1)+3≤ z1f α s:=by
     have hl:=z1c5 s (by omega) (by omega)
     rw [he₁] at hl
     have hw:=hsum s (by omega) (by omega)
     have heq:=hid s (by omega)
     by_contra hbad
     have z1b8:=Nat.mul_le_mul_left s
       (show z1f α s≤ z1f α (s - 1)+2 by omega)
     nlinarith
   omega
theorem zdd {V:Type*} [Fintype V] {G:SimpleGraph V}
   {k:ℕ} (hk: 8≤ k) (hα:G.indepNum≤ k)
   (hexp:∀ I,G.IsIndepSet I → I.Nonempty → 
     k*I.ncard+1≤(z0 G I).ncard) (r:V) :
   ∃ i,1≤ i∧i≤ k / 2∧(z8 G r i).Nonempty ∧
     (k / 2)*independence G (z8 G r i)+k % 2 ≤
       (z8 G r i).ncard:=by
 classical
 have hmod: 2*(k / 2)+k % 2=k:=by omega
 obtain ⟨i,hi,his,hpos,hd⟩:=ze5
   (fun j => independence G (z8 G r j))
   (fun j => (z8 G r j).ncard)
   (s:=k / 2) (ε:=k % 2) (by omega) (by omega) (by simp)
   ((Set.ncard_pos).mpr (z84 (by omega) hexp r))
   (by intro i; rw [hmod]; exact (zfc G r i).trans hα)
   (by intro i hi his; rw [hmod]; exact z14f (by omega) hexp r hi)
 exact ⟨i,hi,his,(Set.ncard_pos).mp hpos,hd⟩
theorem ze6 {V:Type*} [Fintype V] {G:SimpleGraph V}
   {k:ℕ} (hk: 8≤ k) (hα:G.indepNum≤ k)
   (hexp:∀ I,G.IsIndepSet I → I.Nonempty → 
     k*I.ncard+1≤(z0 G I).ncard) (r:V) :
   ∃ i,1≤ i∧i≤ k / 2 ∧ ∃ S⊆z8 G r i,
     S.Nonempty∧z43 (G.induce S) (k / 2) (k % 2):=by
 obtain ⟨i,hi,his,hD,hd⟩:=zdd hk hα hexp r
 obtain ⟨S,hSD,hS,hmin⟩:=z126 G (k / 2) (k % 2) hD hd
 exact ⟨i,hi,his,S,hSD,hS,hmin⟩
end CycleClique
namespace CycleClique
open scoped SimpleGraph
theorem z7d {V:Type*} {G:SimpleGraph V} {r v:V}
   (hv:G.Reachable r v) (hne:v≠r) :
   ∃ w,G.Adj v w∧G.Reachable r w∧G.dist r w+1=G.dist r v:=by
 obtain ⟨p,hp⟩:=hv.symm.exists_walk_length_eq_dist
 rw [G.dist_comm] at hp
 cases p with
 | nil => exact False.elim (hne rfl)
 | @cons v w r hvw p =>
   refine ⟨w,hvw,p.reachable.symm,?_⟩
   have hle:G.dist r w≤ p.length:=by
     simpa only [G.dist_comm] using G.dist_le p
   have htri:=hvw.reachable.dist_triangle_right r
   have z20a:=hvw.symm.reachable.dist_triangle_right r
   rw [G.dist_eq_one_iff_adj.mpr hvw] at htri
   rw [G.dist_eq_one_iff_adj.mpr hvw.symm] at z20a
   simp only [SimpleGraph.Walk.length_cons] at hp
   omega
structure BreadthFirstParent {V:Type*} (G:SimpleGraph V) (r:V) where
 parent:V → V
 step:∀ v,G.Reachable r v → v≠r → 
   G.Adj v (parent v)∧G.Reachable r (parent v) ∧
     G.dist r (parent v)+1=G.dist r v
theorem zf3 {V:Type*} (G:SimpleGraph V) (r:V) :
   Nonempty (BreadthFirstParent G r):=by
 classical
 let f:V → V:=fun v => if h:G.Reachable r v∧v≠r then
   (z7d h.1 h.2).choose else v
 refine ⟨⟨f,?_⟩⟩
 intro v hv hne
 dsimp [f]
 rw [dif_pos ⟨hv,hne⟩]
 exact (z7d hv hne).choose_spec
theorem BreadthFirstParent.z86 {V:Type*} {G:SimpleGraph V} {r:V}
   (B:BreadthFirstParent G r) {v:V} (hv:G.Reachable r v)
   (n:ℕ) (hn:n≤ G.dist r v) :
   G.Reachable r (B.parent^[n] v)∧G.dist r (B.parent^[n] v)+n=G.dist r v:=by
 induction n with
 | zero => simpa using hv
 | succ n ih =>
   have hn' :n≤ G.dist r v:=by omega
   obtain ⟨hr,hd⟩:=ih hn'
   have hne:B.parent^[n] v≠r:=by
     intro heq
     rw [heq,G.dist_self] at hd
     omega
   obtain ⟨ha,hr',hd'⟩:=B.step _ hr hne
   rw [Function.iterate_succ_apply']
   exact ⟨hr',by omega⟩
theorem BreadthFirstParent.z152 {V:Type*} {G:SimpleGraph V} {r:V}
   (B:BreadthFirstParent G r) {v:V} (hv:G.Reachable r v)
   (n:ℕ) (hn:n≤ G.dist r v) :
   ∃ p:G.Walk v (B.parent^[n] v),p.IsPath∧p.length=n ∧
     ∀ w∈p.support,∃ j,j≤ n∧w=B.parent^[j] v:=by
 induction n with
 | zero =>
   refine ⟨.nil,by simp,rfl,?_⟩
   intro w hw
   refine ⟨0,by omega,?_⟩
   simpa using hw
 | succ n ih =>
   obtain ⟨p,hp,hlen,hsupp⟩:=ih (by omega)
   obtain ⟨hr,hd⟩:=B.z86 hv n (by omega)
   obtain ⟨ha,_,_⟩:=B.step _ hr (by
     intro heq
     rw [heq,G.dist_self] at hd
     omega)
   have hadj:G.Adj (B.parent^[n] v) (B.parent^[n+1] v):=by
     simpa only [Function.iterate_succ_apply'] using ha
   have hnot:B.parent^[n+1] v∉p.support:=by
     intro hw
     obtain ⟨j,hj,heq⟩:=hsupp _ hw
     have h₁:=(B.z86 hv (n+1) hn).2
     have h₂:=(B.z86 hv j (by omega)).2
     rw [heq] at h₁
     omega
   refine ⟨p.concat hadj,hp.concat hnot hadj,by rw [SimpleGraph.Walk.length_concat,hlen],?_⟩
   intro w hw
   rw [SimpleGraph.Walk.support_concat,List.mem_append,List.mem_singleton] at hw
   rcases hw with hw | rfl
   · obtain ⟨j,hj,heq⟩:=hsupp w hw
     exact ⟨j,by omega,heq⟩
   · exact ⟨n+1,by omega,rfl⟩
def z9 {V:Type*} {G:SimpleGraph V} {r:V}
   (B:BreadthFirstParent G r) (i:ℕ) (v:V) (j:ℕ):V :=
 B.parent^[i - j] v
theorem z14c {V:Type*} {G:SimpleGraph V} {r v:V}
   (B:BreadthFirstParent G r) {i j:ℕ}
   (hv:v∈z8 G r i) (hj:j≤ i) :
   G.Reachable r (z9 B i v j)∧G.dist r (z9 B i v j)=j:=by
 have h:=B.z86 hv.1 (i - j) (by rw [hv.2]; omega)
 rw [hv.2] at h
 exact ⟨h.1,by dsimp [z9]; omega⟩
@[simp] theorem layerAncestor_self {V:Type*} {G:SimpleGraph V} {r:V}
   (B:BreadthFirstParent G r) (i:ℕ) (v:V):z9 B i v i=v:=by
 simp [z9]
theorem zdf {V:Type*} {G:SimpleGraph V} {r v:V}
   (B:BreadthFirstParent G r) {i:ℕ} (hv:v∈z8 G r i) :
   z9 B i v 0=r:=by
 obtain ⟨hr,hd⟩:=z14c B hv (Nat.zero_le i)
 exact (hr.dist_eq_zero_iff.mp hd).symm
theorem za8 {V:Type*} {G:SimpleGraph V} {r:V}
   (B:BreadthFirstParent G r) {i j l:ℕ} (hjl:j≤ l) (hli:l≤ i) (v:V) :
   B.parent^[l - j] (z9 B i v l)=z9 B i v j:=by
 unfold z9
 rw [← Function.iterate_add_apply]
 congr 1
 omega
theorem zc1 {V:Type*} {G:SimpleGraph V} {r v:V}
   (B:BreadthFirstParent G r) {i j:ℕ}
   (hv:v∈z8 G r i) (hj:j≤ i) :
   ∃ p:G.Walk v (z9 B i v j),p.IsPath∧p.length=i - j ∧
     ∀ w∈p.support,j≤ G.dist r w∧G.dist r w≤ i ∧
       z9 B i v (G.dist r w)=w:=by
 obtain ⟨p,hp,hlen,hs⟩:=B.z152 hv.1 (i - j) (by rw [hv.2]; omega)
 refine ⟨p,hp,hlen,?_⟩
 intro w hw
 obtain ⟨t,ht,rfl⟩:=hs w hw
 have hd:=(B.z86 hv.1 t (by rw [hv.2]; omega)).2
 rw [hv.2] at hd
 refine ⟨by omega,by omega,?_⟩
 unfold z9
 rw [show i - G.dist r (B.parent^[t] v)=t by omega]
theorem z151 {V:Type*} {G:SimpleGraph V} {r:V}
   (B:BreadthFirstParent G r) {i:ℕ} {S:Set V}
   (hS:S⊆z8 G r i) (hne:∃ x∈S,∃ y∈S,x≠y) :
   ∃ d,d < i ∧ ∃ c,(∀ v∈S,z9 B i v d=c) ∧
     ∃ x∈S,∃ y∈S,z9 B i x (d+1)≠z9 B i y (d+1):=by
 classical
 obtain ⟨x,hx,y,hy,hxy⟩:=hne
 let P:ℕ → Prop:=fun d => ∀ v∈S,z9 B i v d=z9 B i x d
 have h₀:P 0:=by
   intro v hv
   rw [zdf B (hS hv),zdf B (hS hx)]
 let d:=Nat.findGreatest P i
 have hd:d≤ i:=Nat.findGreatest_le i
 have hPd:P d:=Nat.findGreatest_spec (Nat.zero_le i) h₀
 have hdlt:d < i:=by
   by_contra hn
   have he:d=i:=by omega
   have hh:=hPd y hy
   simp only [he,layerAncestor_self] at hh
   exact hxy hh.symm
 refine ⟨d,hdlt,z9 B i x d,hPd,?_⟩
 by_contra hn
 push Not at hn
 have z1e3:P (d+1):=by
   intro v hv
   exact hn v hv x hx
 have hh:=Nat.le_findGreatest (by omega:d+1≤ i) z1e3
 change d+1≤ d at hh
 omega
theorem z6e {V:Type*} {G:SimpleGraph V} {x y:V}
   (p:G.Walk x y) (hp:p.IsPath):x∉p.support.tail:=by
 have hn:=hp.support_nodup
 rw [← p.cons_tail_support,List.nodup_cons] at hn
 exact hn.1
theorem z150 {V:Type*} {G:SimpleGraph V} {r y z:V}
   (B:BreadthFirstParent G r) {i d:ℕ}
   (hy:y∈z8 G r i) (hz:z∈z8 G r i) (hd:d < i)
   (z18d:z9 B i y d=z9 B i z d)
   (z18c:z9 B i y (d+1)≠z9 B i z (d+1)) :
   ∃ p:G.Walk y z,p.IsPath∧p.length=2*(i - d) ∧
     ∀ w∈p.support,G.dist r w=i → w=y∨w=z:=by
 obtain ⟨p,hp,z11e,hps⟩:=zc1 B hy hd.le
 obtain ⟨q,hq,z65,hqs⟩:∃ q:G.Walk z (z9 B i y d),
     q.IsPath∧q.length=i - d ∧ ∀ w∈q.support,
       d≤ G.dist r w∧G.dist r w≤ i∧z9 B i z (G.dist r w)=w:=by
   obtain ⟨q,hq,hl,hs⟩:=zc1 B hz hd.le
   refine ⟨q.copy rfl z18d.symm,by simpa using hq,by simpa using hl,?_⟩
   simpa only [SimpleGraph.Walk.support_copy] using hs
 have z1eb:∀ w∈p.support,w∈q.support → w=z9 B i y d:=by
   intro w hw hwq
   obtain ⟨hwd,hwi,hye⟩:=hps w hw
   obtain ⟨_,_,hze⟩:=hqs w hwq
   by_cases he:G.dist r w=d
   · simpa only [he] using hye.symm
   · have hdl:d+1≤ G.dist r w:=by omega
     have h₁:=za8 B hdl hwi y
     have h₂:=za8 B hdl hwi z
     rw [hye] at h₁
     rw [hze] at h₂
     exact False.elim (z18c (h₁.symm.trans h₂))
 refine ⟨p.append q.reverse,?_,?_,?_⟩
 · rw [SimpleGraph.Walk.isPath_def,SimpleGraph.Walk.support_append,List.nodup_append']
   refine ⟨hp.support_nodup,hq.reverse.support_nodup.tail,?_⟩
   apply List.disjoint_left.mpr
   intro w hw hwq
   have hwq' :w∈q.support:=by
     simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using List.mem_of_mem_tail hwq
   have he:=z1eb w hw hwq'
   subst w
   exact z6e q.reverse hq.reverse hwq
 · simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse,z11e,z65]
   omega
 · intro w hw hwi
   rw [SimpleGraph.Walk.support_append,List.mem_append] at hw
   rcases hw with hw | hw
   · have hh:=(hps w hw).2.2
     simpa only [hwi,layerAncestor_self] using Or.inl hh.symm
   · have hwq:w∈q.support:=by
       simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using List.mem_of_mem_tail hw
     have hh:=(hqs w hwq).2.2
     simpa only [hwi,layerAncestor_self] using Or.inr hh.symm
theorem z149 {V:Type*} {G:SimpleGraph V} {r y z:V} {i:ℕ}
   (p:G.Walk y z) (hp:p.IsPath)
   (z1ba:∀ w∈p.support,G.dist r w=i)
   (q:G.Walk y z) (hq:q.IsPath) (z65: 1 < q.length)
   (z1bb:∀ w∈q.support,G.dist r w=i → w=y∨w=z) :
   (p.append q.reverse).IsCycle:=by
 apply hp.isCycle_append hq.reverse
 · apply List.disjoint_left.mpr
   intro w hwp hwq
   have hwp' :=List.mem_of_mem_tail hwp
   have hwq' :w∈q.support:=by
     simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using List.mem_of_mem_tail hwq
   rcases z1bb w hwq' (z1ba w hwp') with rfl | rfl
   · exact z6e p hp hwp
   · exact z6e q.reverse hq.reverse hwq
 · exact Or.inr (by simpa only [SimpleGraph.Walk.length_reverse] using z65)
end CycleClique
namespace CycleClique
open scoped SimpleGraph
theorem zb6 {V:Type*} {G:SimpleGraph V} {x y:V}
   (p:G.Walk x y) (hp:p.IsPath) (hlen: 2≤ p.length) (hyx:G.Adj y x) :
   (SimpleGraph.Walk.cons hyx p).IsCycle:=by
 apply (p.cons_isCycle_iff hyx).mpr
 refine ⟨hp,?_⟩
 intro he
 have hn:=hp.length_eq_one_of_mem_edges (by simpa only [Sym2.eq_swap] using he)
 omega
theorem z96 {V:Type*} {G:SimpleGraph V}
   (z4b:G.Connected) {x:V} (c:G.Walk x x) (hc:c.IsCycle)
   (hout:∃ z,z∉c.support) :
   ∃ u v,∃ p:G.Walk u v,p.IsPath∧p.length=c.length:=by
 classical
 obtain ⟨z,hz⟩:=hout
 obtain ⟨w⟩:=z4b.preconnected x z
 obtain ⟨d,_,hd,hdz⟩:=w.exists_boundary_dart {v | v∈c.support} c.start_mem_support hz
 let q:=c.rotate d.fst hd
 have hq:q.IsCycle:=hc.rotate hd
 have hlen:q.length=c.length:=c.length_rotate _ _
 have hnot:d.snd∉q.tail.reverse.support:=by
   intro hm
   have hm₁:d.snd∈q.tail.support:=by
     simpa only [SimpleGraph.Walk.support_reverse,List.mem_reverse] using hm
   have hm₂:d.snd∈q.support:=q.isSubwalk_rfl.tail.support_subset hm₁
   exact hdz ((c.mem_support_rotate_iff _ _).mp hm₂)
 let p:=SimpleGraph.Walk.cons d.adj.symm q.tail.reverse
 refine ⟨d.snd,_,p,?_,?_⟩
 · exact hq.isPath_tail.reverse.cons hnot
 · have hl:=hc.three_le_length
   simp only [p,SimpleGraph.Walk.length_cons,SimpleGraph.Walk.length_reverse,
     SimpleGraph.Walk.length_tail,hlen]
   omega
theorem zc6 {V:Type*} [Fintype V] {G:SimpleGraph V}
   [DecidableRel G.Adj] {d:ℕ} (hd: 2≤ d) (z4b:G.Connected)
   (z27:∀ v,d≤ G.degree v) :
   ∃ x y,∃ p:G.Walk x y,p.IsPath∧min (Fintype.card V) (2*d+1)≤ p.length+1:=by
 classical
 let:Nonempty V:=z4b.nonempty
 obtain ⟨x,y,p,hp,hmax⟩:=SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
 refine ⟨x,y,p,hp,?_⟩
 by_contra hn
 have hlen:p.length < 2*d:=by omega
 have z79:p.length+1 < Fintype.card V:=by omega
 let W:Set V:={v | v∈p.support}
 have z1a1:W.ncard=p.length+1:=by
   have heq:W=(p.support.toFinset:Set V):=by ext v; simp [W]
   rw [heq,Set.ncard_coe_finset,List.toFinset_card_of_nodup hp.support_nodup,
     SimpleGraph.Walk.length_support]
 have hnb:∀ v,G.Adj y v → v∈p.support :=
   z19 p hp (fun v q hq => hmax x v q hq)
 have hxnb:∀ v,G.Adj x v → v∈p.support:=by
   intro v hv
   have:=z19 p.reverse hp.reverse
     (fun v q hq => by simpa using hmax y v q hq) v hv
   simpa using this
 have z1c6:d≤ p.length:=by
   have hc:=z29 (G:=G) (v:=y)
     (show y∈W from p.end_mem_support) (fun v hv => hnb v hv)
   rw [z1a1] at hc
   have:=z27 y
   omega
 let E:=z10 G x p.support
 have hE:d≤ E.ncard :=
   (z27 y).trans (z6d p hp (List.Perm.refl _) hnb)
 have hxE:x∉E:=za5 (by rw [SimpleGraph.Walk.length_support]; omega)
 have hex:∃ e,e∈E∧G.Adj x e:=by
   by_contra hne
   push Not at hne
   have hdis:Disjoint E (G.neighborSet x):=by
     exact Set.disjoint_left.mpr (fun e he hn => hne e he hn)
   have hins:insert x (E∪G.neighborSet x)⊆W:=by
     intro v hv
     rcases hv with rfl | hv
     · exact p.start_mem_support
     · rcases hv with hv | hv
       · exact z4f hv
       · exact hxnb v hv
   have hnot:x∉E∪G.neighborSet x:=by simp [hxE]
   have hc:=Set.ncard_le_ncard hins
   rw [Set.ncard_insert_of_notMem hnot,Set.ncard_union_eq hdis,
     z28,z1a1] at hc
   have z22a:=z27 x
   omega
 obtain ⟨e,he,hxe⟩:=hex
 obtain ⟨q,hq,zc⟩:=he
 have z65:q.length=p.length:=by
   have:=zc.length_eq
   simp only [SimpleGraph.Walk.length_support] at this
   omega
 let c:=SimpleGraph.Walk.cons hxe.symm q
 have hc:c.IsCycle:=zb6 q hq (by omega) hxe.symm
 have hout:∃ z,z∉c.support:=by
   have hnW:W≠Set.univ:=by
     intro heq
     rw [heq,Set.ncard_univ,Nat.card_eq_fintype_card] at z1a1
     omega
   have z204:∃ z,z∉W:=by
     by_contra hh
     push Not at hh
     exact hnW (Set.eq_univ_of_forall hh)
   obtain ⟨z,hz⟩:=z204
   refine ⟨z,?_⟩
   intro hzc
   simp only [c,SimpleGraph.Walk.support_cons,List.mem_cons] at hzc
   rcases hzc with rfl | hzq
   · exact hz (zc.mem_iff.mp q.end_mem_support)
   · exact hz (zc.mem_iff.mp hzq)
 obtain ⟨u,v,R,hR,hRlen⟩:=z96 z4b c hc hout
 have hh:=hmax u v R hR
 simp only [c,SimpleGraph.Walk.length_cons,z65] at hRlen
 omega
end CycleClique
namespace CycleClique
open scoped SimpleGraph
theorem z125 {V:Type*} [Fintype V] {G:SimpleGraph V}
   {k:ℕ} (hk: 8≤ k) {r:V} {i:ℕ} (hi:i≤ k / 2)
   {S:Set V} (hSD:S⊆z8 G r i) (hS:S.Nonempty)
   (z85:z43 (G.induce S) (k / 2) (k % 2))
   (z37:¬ (⊤ :SimpleGraph (Fin (k / 2)))⊑G) :
   SimpleGraph.cycleGraph (k+1)⊑G:=by
 classical
 let:Nonempty S:=hS.to_subtype
 let H:=G.induce S
 let f:H ↪g G:=SimpleGraph.Embedding.induce S
 have z1c4:¬ (⊤ :SimpleGraph (Fin (k / 2)))⊑H :=
   fun hh => z37 (hh.trans f.isContained)
 obtain ⟨z4b,hnb,z79,z27,hexp⟩ :=
   ze8 (by omega: 4≤ k / 2) (by omega:k % 2≤1) z85 z1c4
 have z216:k≤ Fintype.card S:=by omega
 obtain ⟨B⟩:=zf3 G r
 have hneS:∃ x∈S,∃ y∈S,x≠y :=
   (Set.one_lt_ncard).mp (by
     rw [← Nat.card_coe_set_eq,Nat.card_eq_fintype_card]
     omega)
 obtain ⟨d,hd,c,hc,x,hx,z,hz,hxz⟩:=z151 B hSD hneS
 let ℓ:=k+1 - 2*(i - d)
 have z211: 1≤ℓ:=by dsimp [ℓ]; omega
 have z1d6:∀ a b:S,a≠b → ¬ H.Adj a b → 
     2*(k / 2)≤(z0 H {a,b}).ncard:=by
   intro a b hab hnadj
   have hI:H.IsIndepSet {a,b}:=by
     intro x hx y hy hxy z70
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
     rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
     · exact hxy rfl
     · exact hnadj z70
     · exact hnadj z70.symm
     · exact hxy rfl
   have he:=(hexp {a,b} hI (Set.insert_nonempty _ _)).1
   simpa only [Set.ncard_pair hab,Nat.mul_comm] using he
 have z1da:∃ y z:S,z9 B i y.val (d+1) ≠
     z9 B i z.val (d+1) ∧ ∃ p:H.Walk y z,p.IsPath∧p.length=ℓ:=by
   by_cases z21c:i - d=1
   · obtain ⟨y,z,p,hp,z1d5⟩:=zc6
       (by omega: 2≤ k / 2) z4b z27
     have hlen: ℓ≤ p.length:=by dsimp [ℓ] at *; omega
     have z1d7:=hp.take ℓ
     have z209:(p.take ℓ).length=ℓ:=by rw [SimpleGraph.Walk.take_length,inf_eq_left.mpr hlen]
     refine ⟨y,p.getVert ℓ,?_,p.take ℓ,z1d7,z209⟩
     have he:d+1=i:=by omega
     simp only [he,layerAncestor_self]
     intro heq
     have hn:=(z1d7.nil_iff_eq).mpr (Subtype.ext heq)
     have hh:=hn.length_eq_zero
     omega
   · let χ:S → Fin 2:=fun v =>
       if z9 B i v.val (d+1)=z9 B i x (d+1) then 0 else 1
     have hχ:∃ y z,χ y≠χ z:=by
       refine ⟨⟨x,hx⟩,⟨z,hz⟩,?_⟩
       simp [χ,Ne.symm hxz]
     have z1bd: ℓ≤2*(k / 2) - 2:=by dsimp [ℓ]; omega
     obtain ⟨y,z,hyz,p,hp,hlen⟩:=z194 H (k / 2) (by omega)
       z4b hnb z1c4 z27 z1d6 χ hχ ℓ z211 z1bd
     refine ⟨y,z,?_,p,hp,hlen⟩
     intro heq
     apply hyz
     simp only [χ,heq]
 obtain ⟨y,z,z18c,p,hp,hlen⟩:=z1da
 have z18d:z9 B i y.val d=z9 B i z.val d :=
   (hc y.val y.property).trans (hc z.val z.property).symm
 obtain ⟨q,hq,z65,z1bb⟩:=z150 B (hSD y.property) (hSD z.property)
   hd z18d z18c
 let inc:H  →g G:=⟨Subtype.val,fun ha => ha⟩
 let P:G.Walk y.val z.val:=p.map inc
 have hP:P.IsPath:=hp.map Subtype.val_injective
 have z1ba:∀ w∈P.support,G.dist r w=i:=by
   intro w hw
   rw [SimpleGraph.Walk.support_map] at hw
   obtain ⟨v,_,rfl⟩:=List.mem_map.mp hw
   exact (hSD v.property).2
 have hcyc:=z149 P hP z1ba q hq (by rw [z65]; omega) z1bb
 apply (SimpleGraph.cycleGraph_isContained_iff (by omega: 2 < k+1)).mpr
 refine ⟨y.val,P.append q.reverse,hcyc,?_⟩
 dsimp only [P]
 rw [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse,
   SimpleGraph.Walk.length_map,hlen,z65]
 dsimp [ℓ]
 omega
theorem z13c {V:Type*} [Fintype V] [Nonempty V]
   {G:SimpleGraph V} {k:ℕ} (hk: 8≤ k) (hα:G.indepNum≤ k)
   (hexp:∀ I,G.IsIndepSet I → I.Nonempty → 
     k*I.ncard+1≤(z0 G I).ncard)
   (hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G) :
   (⊤ :SimpleGraph (Fin (k / 2)))⊑G:=by
 by_contra z37
 obtain ⟨r⟩:= ‹Nonempty V›
 obtain ⟨i,_,hi,S,hSD,hS,z85⟩:=ze6 hk hα hexp r
 exact hcycle (z125 hk hi hSD hS z85 z37)
theorem z10c {V:Type*} [Fintype V] (G:SimpleGraph V)
   (a:ℕ) (z37:¬ (⊤ :SimpleGraph (Fin 3))⊑G) (hα:G.indepNum≤ a) :
   2*Fintype.card V≤ a*(a+3):=by
 classical
 induction a generalizing V with
 | zero =>
   have z1a5:IsEmpty V:=⟨fun v => by
     have hI:G.IsIndepSet {v}:=Set.pairwise_singleton _ _
     have hc:=(z3d hI).trans hα
     simp at hc⟩
   let:=z1a5
   simp
 | succ a ih =>
   cases isEmpty_or_nonempty V with
   | inl he => let:=he; simp
   | inr he =>
     let:=he
     obtain ⟨v⟩:=he
     have z1f6:G.IsIndepSet (G.neighborSet v) :=
       (SimpleGraph.isClique_compl G).mp (z7a z37 v)
     have z1e2:=(z3d z1f6).trans hα
     let N:=z0 G {v}
     let R:=Nᶜ
     have hNc:N.ncard≤ a+2:=by
       dsimp [N]
       rw [z36]
       rw [z28] at z1e2
       omega
     have hαR:(G.induce R).indepNum≤ a:=by
       have hh:=z5c
         (show G.IsIndepSet {v} from Set.pairwise_singleton _ _) (Set.subset_univ {v})
       rw [z31,Set.ncard_singleton,← Set.compl_eq_univ_sdiff] at hh
       change independence G R+1≤ G.indepNum at hh
       change independence G R≤ a
       omega
     have z1e9:¬ (⊤ :SimpleGraph (Fin 3))⊑G.induce R :=
       fun h => z37 (h.trans (SimpleGraph.Embedding.induce R).isContained)
     have hcR:=ih (G.induce R) z1e9 hαR
     rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hcR
     have hsum:=Set.ncard_add_ncard_compl N
     rw [Nat.card_eq_fintype_card] at hsum
     change 2*R.ncard≤ a*(a+3) at hcR
     nlinarith
theorem zb3 {V:Type*} [Fintype V] {G:SimpleGraph V}
   {k a:ℕ} (hk: 3≤ k) (_ha: 2≤ a) (hak:a≤ k)
   (z79:Fintype.card V=k*a+1) (hα:G.indepNum≤ a) :
   (⊤ :SimpleGraph (Fin 3))⊑G:=by
 by_contra z37
 have hh:=z10c G a z37 hα
 rw [z79] at hh
 have z1b8:a+3≤2*k:=by omega
 have hm:=Nat.mul_le_mul_left a z1b8
 nlinarith
theorem z17 {V:Type*} [Fintype V]
   (G:SimpleGraph V) (t:ℕ) :
   (⊤ :SimpleGraph (Fin t))⊑G↔t≤ G.cliqueNum:=by
 classical
 constructor
 · intro ht
   have hn:=ht.not_cliqueFree
   simp only [SimpleGraph.CliqueFree,not_forall,not_not] at hn
   obtain ⟨Q,hQ⟩:=hn
   have hh:=hQ.isClique.card_le_cliqueNum
   rwa [hQ.card_eq] at hh
 · intro ht
   by_contra hn
   obtain ⟨Q,hQ⟩:=G.exists_isNClique_cliqueNum
   have hh:=z35 hn hQ.isClique
   rw [Set.ncard_coe_finset,hQ.card_eq] at hh
   omega
theorem counterexample_clique_bound {V:Type*} [Fintype V] {G:SimpleGraph V}
   {k a:ℕ} (hk: 3≤ k) (ha: 2≤ a) (hak:a≤ k)
   (z79:Fintype.card V=k*a+1) (hα:G.indepNum≤ a)
   (hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G)
   (hexp:∀ I,G.IsIndepSet I → I.Nonempty → 
     k*I.ncard+1≤(z0 G I).ncard) :
   max 3 (k / 2)≤ G.cliqueNum∧G.cliqueNum≤ k:=by
 have z1a7:=(z17 G 3).mp
   (zb3 hk ha hak z79 hα)
 refine ⟨max_le z1a7 ?_,?_⟩
 · by_cases z1a6: 8≤ k
   · let:Nonempty V:=Fintype.card_pos_iff.mp (by omega)
     exact (z17 G _).mp
       (z13c z1a6 (hα.trans hak) hexp hcycle)
   · omega
 · by_contra hn
   have htop:=(z17 G (k+1)).mpr (by omega)
   exact hcycle ((SimpleGraph.IsContained.of_le (show SimpleGraph.cycleGraph (k+1) ≤ ⊤
     from le_top)).trans htop)
end CycleClique
namespace CycleClique
open scoped SimpleGraph
theorem zae {V:Type*} [Fintype V] {G:SimpleGraph V}
   (hα:G.indepNum≤2) {x y z:V} (hxy:x≠y) (hxz:x≠z)
   (hyz:y≠z) (hx:¬ G.Adj x z) (hy:¬ G.Adj y z):G.Adj x y:=by
 classical
 by_contra z70
 have hI:G.IsIndepSet {x,y,z}:=by
   intro a ha b hb hab
   simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at ha hb
   rcases ha with rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl
   · exact (hab rfl).elim
   · exact z70
   · exact hx
   · exact fun h => z70 h.symm
   · exact (hab rfl).elim
   · exact hy
   · exact fun h => hx h.symm
   · exact fun h => hy h.symm
   · exact (hab rfl).elim
 have hc:=(z3d hI).trans hα
 simp [Set.ncard_insert_of_notMem,hxy,hxz,hyz] at hc
theorem za {V:Type*} [Fintype V] {G:SimpleGraph V}
   {S:Set V} (hS:G.IsClique S):S.ncard≤ G.cliqueNum:=by
 classical
 have hh:G.IsClique (S.toFinset:Set V):=by simpa using hS
 simpa only [Set.ncard_eq_toFinset_card'] using hh.card_le_cliqueNum
theorem z2f {V:Type*} [Fintype V] {G:SimpleGraph V}
   (hα:G.indepNum≤2) {S:Set V} {z:V} (hz:z∉S)
   (zf4:∀ x∈S,¬ G.Adj x z):G.IsClique S:=by
 intro x hx y hy hxy
 exact zae hα (z:=z) hxy (fun he => hz (he ▸ hx))
   (fun he => hz (he ▸ hy)) (zf4 x hx) (zf4 y hy)
theorem zd6 {V:Type*} [Fintype V] {G:SimpleGraph V}
   {t:ℕ} (hα:G.indepNum≤2) (ht:G.cliqueNum≤ t)
   (z3b: 2*t < Fintype.card V):G.Connected:=by
 classical
 have hne:Nonempty V:=Fintype.card_pos_iff.mp (by omega)
 let:=hne
 refine ⟨?_⟩
 intro x y
 by_contra hxy
 let S:={v | G.Reachable x v}
 have hx:x∈S:=SimpleGraph.Reachable.rfl
 have hy:y∉S:=hxy
 have zf4:∀ a∈S,∀ b∈Sᶜ,¬ G.Adj a b:=by
   intro a ha b hb hab
   exact hb (ha.trans hab.reachable)
 have hS:G.IsClique S:=z2f hα hy (fun a ha => zf4 a ha y hy)
 have hR:G.IsClique Sᶜ:=z2f hα
   (show x∉Sᶜ from fun hh => hh hx) (fun b hb hab => zf4 x hx b hb hab.symm)
 have hcS:=(za hS).trans ht
 have hcR:=(za hR).trans ht
 have hsum:=Set.ncard_add_ncard_compl S
 rw [Nat.card_eq_fintype_card] at hsum
 omega
theorem z91 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {t:ℕ} (hα:G.indepNum≤2) (ht:G.cliqueNum≤ t)
   (z3b: 2*t < Fintype.card V) (v x y:V) (hxv:x≠v) (hyv:y≠v) :
   (z4a G {w | w≠v}).Reachable x y:=by
 classical
 let D:=z4a G {w | w≠v}
 by_contra hxy
 let A:Set V:={w | D.Reachable x w}
 let B:Set V:={w | w≠v} \ A
 have hxA:x∈A:=SimpleGraph.Reachable.rfl
 have hAv:∀ a∈A,a≠v:=by
   rintro a ⟨p⟩
   exact z67 p hxv a p.end_mem_support
 have hyB:y∈B:=⟨hyv,hxy⟩
 have zf4:∀ a∈A,∀ b∈B,¬ G.Adj a b:=by
   intro a ha b hb hab
   exact hb.2 (ha.trans (show D.Adj a b from ⟨hab,hAv a ha,hb.1⟩).reachable)
 have hA:G.IsClique A:=z2f hα hyB.2
   (fun a ha => zf4 a ha y hyB)
 have hB:G.IsClique B:=z2f hα
   (show x∉B from fun hh => hh.2 hxA) (fun b hb hab => zf4 x hxA b hb hab.symm)
 have hcA:=(za hA).trans ht
 have hcB:=(za hB).trans ht
 have hvAB:v∉A∪B:=by
   rintro (ha | hb)
   · exact hAv v ha rfl
   · exact hb.1 rfl
 have z20c:insert v (A∪B)=Set.univ:=by
   ext w
   simp only [Set.mem_insert_iff,Set.mem_union,Set.mem_univ,iff_true]
   by_cases hwv:w=v
   · exact Or.inl hwv
   · by_cases hw:w∈A
     · exact Or.inr (Or.inl hw)
     · exact Or.inr (Or.inr ⟨hwv,hw⟩)
 have hdis:Disjoint A B:=Set.disjoint_left.mpr (fun a ha hb => hb.2 ha)
 have hsum:A.ncard+B.ncard+1=Fintype.card V:=by
   have hh:=congrArg Set.ncard z20c
   simpa only [Set.ncard_insert_of_notMem hvAB,Set.ncard_union_eq hdis,
     Set.ncard_univ,Nat.card_eq_fintype_card] using hh
 have hAc:A.ncard=t:=by omega
 have hBc:B.ncard=t:=by omega
 have hone:(∀ a∈A,G.Adj v a)∨(∀ b∈B,G.Adj v b):=by
   by_cases ha:∀ a∈A,G.Adj v a
   · exact Or.inl ha
   · push Not at ha
     obtain ⟨a,ha,hva⟩:=ha
     refine Or.inr (fun b hb => ?_)
     exact zae hα (Ne.symm hb.1) (Ne.symm (hAv a ha))
       (fun he => hb.2 (he ▸ ha)) hva (fun h => zf4 a ha b hb h.symm)
 rcases hone with ha | hb
 · have hcl:G.IsClique (insert v A):=hA.insert (fun a ha' _ => ha a ha')
   have hc:=(za hcl).trans ht
   rw [Set.ncard_insert_of_notMem (fun hv => hAv v hv rfl),hAc] at hc
   omega
 · have hcl:G.IsClique (insert v B):=hB.insert (fun b hb' _ => hb b hb')
   have hc:=(za hcl).trans ht
   rw [Set.ncard_insert_of_notMem (fun hv => hv.1 rfl),hBc] at hc
   omega
theorem zb4 {V:Type*} [Fintype V]
   {G:SimpleGraph V} [DecidableRel G.Adj] (z4b:G.Connected)
   (z3b: 3≤ Fintype.card V)
   (hdel:∀ v x y,x≠v → y≠v → (z4a G {w | w≠v}).Reachable x y)
   (x:V): 2≤ G.degree x:=by
 classical
 obtain ⟨y,_,hyx⟩:=z49 (E:=Set.univ) (w₀:=x)
   (by simpa only [Set.ncard_univ,Nat.card_eq_fintype_card] using (by omega: 2≤ Fintype.card V))
 obtain ⟨p⟩:=z4b.preconnected x y
 have z11e: 0 < p.length:=SimpleGraph.Walk.not_nil_iff_lt_length.mp
   (fun hn => hyx hn.eq.symm)
 let w:=p.getVert 1
 have hxw:G.Adj x w:=by
   simpa only [SimpleGraph.Walk.getVert_zero,zero_add]
     using (p.adj_getVert_succ (i:= 0) z11e)
 have hex:∃ z:V,z≠x∧z≠w:=by
   by_contra hn
   push Not at hn
   have hsub:(Set.univ:Set V)⊆{x,w}:=by
     intro z _
     by_cases hz:z=x
     · exact Or.inl hz
     · exact Or.inr (hn z hz)
   have hh:=Set.ncard_le_ncard hsub
   rw [Set.ncard_univ,Nat.card_eq_fintype_card,Set.ncard_pair hxw.ne] at hh
   omega
 obtain ⟨z,hzx,hzw⟩:=hex
 obtain ⟨q⟩:=hdel w x z hxw.ne hzw
 have z65: 0 < q.length:=SimpleGraph.Walk.not_nil_iff_lt_length.mp
   (fun hn => hzx hn.eq.symm)
 let u:=q.getVert 1
 have hxu:(z4a G {a | a≠w}).Adj x u:=by
   simpa only [SimpleGraph.Walk.getVert_zero,zero_add]
     using q.adj_getVert_succ (i:= 0) z65
 have hh: 1 < (G.neighborSet x).ncard:=(Set.one_lt_ncard).mpr
   ⟨w,hxw,u,hxu.1,Ne.symm hxu.2.2⟩
 rw [z28] at hh
 omega
theorem z102 {V:Type*} [Fintype V] {G:SimpleGraph V}
   (z4b:G.Connected) (z3b: 3≤ Fintype.card V) (hα:G.indepNum≤2)
   (hdel:∀ v x y,x≠v → y≠v → (z4a G {w | w≠v}).Reachable x y) :
   ∃ x,∃ c:G.Walk x x,c.IsCycle∧c.length=Fintype.card V:=by
 classical
 let:Nonempty V:=z4b.nonempty
 have z27:=zb4 z4b z3b hdel
 obtain ⟨x,y,p,hp,hmax⟩:=SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
 obtain ⟨a,b,P,hP,hPlen⟩:=zc6 (by omega: 2≤2) z4b z27
 have hlen: 2≤ p.length:=by
   have hh:=hmax a b P hP
   omega
 have hW: 1 < p.support.length:=by rw [SimpleGraph.Walk.length_support]; omega
 have hyN:∀ z,G.Adj y z → z∈p.support :=
   z19 p hp (fun z q hq => hmax x z q hq)
 have hxN:∀ z,G.Adj x z → z∈p.support:=by
   intro z hxz
   have hh:=z19 p.reverse hp.reverse
     (fun z q hq => by simpa using hmax y z q hq) z hxz
   simpa using hh
 have z207:∀ z,z∈p.support:=by
   intro z
   by_contra hz
   have hxy:x≠y:=by
     intro hh
     have hn:=(hp.nil_iff_eq).mpr hh
     have hh:=hn.length_eq_zero
     omega
   have z70:=zae hα (z:=z) hxy
     (fun hh => hz (by rw [← hh]; exact p.start_mem_support))
     (fun hh => hz (by rw [← hh]; exact p.end_mem_support))
     (fun hh => hz (hxN z hh)) (fun hh => hz (hyN z hh))
   let c:=SimpleGraph.Walk.cons z70.symm p
   have hc:c.IsCycle:=zb6 p hp hlen z70.symm
   have hzc:z∉c.support:=by
     simp only [c,SimpleGraph.Walk.support_cons,List.mem_cons]
     exact fun hh => hh.elim (fun hh => hz (by rw [hh]; exact p.end_mem_support)) hz
   obtain ⟨u,v,q,hq,z65⟩:=z96 z4b c hc ⟨z,hzc⟩
   have hh:=hmax u v q hq
   simp only [c,SimpleGraph.Walk.length_cons] at z65
   omega
 have z1e5:p.length+1=Fintype.card V:=by
   have hh:p.support.toFinset=Finset.univ:=by ext z; simp [z207]
   have hc:=congrArg Finset.card hh
   simpa only [List.toFinset_card_of_nodup hp.support_nodup,
     SimpleGraph.Walk.length_support,Finset.card_univ] using hc
 let E:=z10 G x p.support
 have hxE:x∉E:=za5 hW
 have hyE:y∈E:=⟨p,hp,.refl _⟩
 have hEc: 2≤ E.ncard :=
   (z27 y).trans (z6d p hp (.refl _) hyN)
 have z1e6:∃ e∈E,G.Adj x e:=by
   by_contra hn
   push Not at hn
   have hcl:G.IsClique E:=z2f hα hxE
     (fun e he he' => hn e he he'.symm)
   obtain ⟨j,hjpos,hjlen,hseg⟩:=zaa p hp (.refl _) hcl hW
   have z226: 2≤ j:=by
     by_contra hh
     have z225:j=1:=by omega
     have za6:=p.adj_getVert_succ (i:= 0) (by omega)
     simp only [SimpleGraph.Walk.getVert_zero,zero_add] at za6
     exact hn (p.getVert 1) ((hseg 1 (by omega)).mpr (by omega)) za6
   let u:=p.getVert (j - 1)
   let w₀:=p.getVert j
   have huE:u∉E:=by
     exact fun hu => by have hh:=(hseg (j - 1) (by omega)).mp hu; omega
   have hxw:x≠w₀:=by
     intro hh
     exact hxE (hh ▸ (hseg j hjlen).mpr le_rfl)
   have hux:u≠x:=by
     intro hh
     have hh' :=(hp.getVert_eq_start_iff (show j - 1≤ p.length by omega)).mp hh
     omega
   obtain ⟨w₁,hw₁,hw₁ne⟩:=z49 (w₀:=w₀) hEc
   obtain ⟨q⟩:=hdel w₀ x w₁ hxw hw₁ne
   obtain ⟨d,hd,hdout,hdin⟩:=q.exists_boundary_dart Eᶜ hxE
     (show w₁∉Eᶜ from fun hh => hh hw₁)
   have z1d3:d.snd∈E:=not_not.mp hdin
   have z1c2:d.snd≠w₀:=d.adj.2.2
   have z13e:=z5d p hp (fun v q hq => hmax x v q hq)
     hcl hjpos hjlen hseg z1d3 z1c2 d.fst d.adj.1.symm
   have hdu:d.fst=u:=z13e.resolve_left hdout
   have z103:G.Adj u d.snd:=hdu ▸ d.adj.1
   have z44:=z64 p hp (fun v q hq => hmax x v q hq)
     hcl hjpos hjlen hseg z1d3 z1c2 z103
   have hyu:y≠u:=fun hh => huE (hh ▸ hyE)
   obtain ⟨q'⟩:=hdel u x y hux.symm hyu
   obtain ⟨d',_,hd'out,hd'in⟩:=q'.exists_boundary_dart Eᶜ hxE
     (show y∉Eᶜ from fun hh => hh hyE)
   have z11c:=z44 d'.snd (not_not.mp hd'in) d'.fst d'.adj.1.symm
   exact d'.adj.2.1 (z11c.resolve_left hd'out)
 obtain ⟨e,he,hxe⟩:=z1e6
 obtain ⟨q,hq,zc⟩:=he
 have z65:q.length=p.length:=by
   have hh:=zc.length_eq
   simp only [SimpleGraph.Walk.length_support] at hh
   omega
 refine ⟨e,.cons hxe.symm q,zb6 q hq (by omega) hxe.symm,?_⟩
 simpa only [SimpleGraph.Walk.length_cons,z65] using z1e5
end CycleClique
namespace CycleClique
open scoped SimpleGraph
theorem zd1 {n:ℕ} [NeZero n] (hn: 2≤ n) {a b:Fin n} :
   (SimpleGraph.cycleGraph n).Adj a b↔a=b+1∨b=a+1:=by
 obtain ⟨n,rfl⟩:∃ m,n=m+2:=⟨n - 2,by omega⟩
 rw [SimpleGraph.cycleGraph_adj,sub_eq_iff_eq_add,sub_eq_iff_eq_add]
 simp only [add_comm]
theorem z94 {V:Type*} {G:SimpleGraph V}
   {n:ℕ} [NeZero n] (hn: 2≤ n) (f:Fin n → V) (hf:Function.Injective f)
   (z13f:∀ i,G.Adj (f i) (f (i+1))):SimpleGraph.cycleGraph n⊑G:=by
 refine ⟨⟨⟨f,?_⟩,hf⟩⟩
 intro a b hab
 rcases (zd1 hn).mp hab with rfl | rfl
 · exact (z13f b).symm
 · exact z13f a
theorem zc2 {n:ℕ} [NeZero n] (hn: 2≤ n) (i:Fin n) :
   (i+1).val=if i.val+1=n then 0 else i.val+1:=by
 simp only [Fin.val_add,Fin.val_one',Nat.mod_eq_of_lt (by omega: 1 < n)]
 split_ifs with h
 · simp [h]
 · rw [Nat.mod_eq_of_lt (by omega)]
def z41 {n:ℕ} (hn: 3≤ n) (i:Fin (n - 1)):Fin n :=
 ⟨if i.val=0 then 0 else i.val+1,by split_ifs <;> omega⟩
theorem z12a {n:ℕ} (hn: 3≤ n) :
   Function.Injective (z41 hn):=by
 intro i j hij
 have hh:=congrArg Fin.val hij
 simp only [z41] at hh
 apply Fin.ext
 split_ifs at hh <;> omega
theorem z167 {n:ℕ} [NeZero n] [NeZero (n - 1)] (hn: 3≤ n)
   (i:Fin (n - 1)) :
   (z41 hn i=0∧z41 hn (i+1)=2) ∨
     z41 hn (i+1)=z41 hn i+1:=by
 have hval:=zc2 (by omega: 2≤ n - 1) i
 by_cases hi:i.val=0
 · left
   constructor <;> apply Fin.ext
   · simp [z41,hi]
   · have hi1:(i+1).val=1:=by rw [hval]; split_ifs <;> omega
     simp [z41,hi1,Nat.mod_eq_of_lt (by omega: 2 < n)]
 · right
   apply Fin.ext
   rw [zc2 (by omega) (z41 hn i)]
   simp only [z41]
   rw [hval]
   split_ifs <;> omega
def z42 {n:ℕ} (hn: 7≤ n) (i:Fin (n - 1)):Fin n :=
 ⟨if i.val < n - 6 then i.val+1 else
   if i.val < n - 4 then i.val+4 else i.val - 1,
   by split_ifs <;> omega⟩
theorem z115 {n:ℕ} (hn: 7≤ n) :
   Function.Injective (z42 hn):=by
 intro i j hij
 have hh:=congrArg Fin.val hij
 simp only [z42] at hh
 apply Fin.ext
 split_ifs at hh <;> omega
theorem z153 {n:ℕ} [NeZero n] [NeZero (n - 1)] (hn: 7≤ n)
   (i:Fin (n - 1)) :
   z42 hn (i+1)=z42 hn i+1 ∨
     z42 hn (i+1)=z42 hn i+4 ∨
     z42 hn i=z42 hn (i+1)+4:=by
 have hval:=zc2 (by omega: 2≤ n - 1) i
 have h1: 1 % n=1:=Nat.mod_eq_of_lt (by omega)
 have h4: 4 % n=4:=Nat.mod_eq_of_lt (by omega)
 have h1' :(1:Fin n).val=1:=by rw [Fin.val_one',h1]
 have h4' :(4:Fin n).val=4:=h4
 simp only [Fin.ext_iff,Fin.val_add,h1',h4',z42,hval]
 split_ifs <;> simp_all only [ite_false,ite_true]
 all_goals first
   | (left; rw [Nat.mod_eq_of_lt (by omega)] <;> omega)
   | (right; left; rw [Nat.mod_eq_of_lt (by omega)])
   | (right; right; rw [Nat.mod_eq_of_lt (by omega)]; omega)
   | (right; left; rw [Nat.mod_eq_sub_mod (by omega),Nat.mod_eq_of_lt (by omega)]; omega)
theorem zc3 {n:ℕ} [NeZero n] (i:Fin n) (d:ℕ)
   (hd: 0 < d) (hdn:d < n):i≠i+Fin.ofNat n d:=by
 intro he
 have hh:(0:Fin n)=Fin.ofNat n d:=add_left_cancel (show i+0=i+Fin.ofNat n d by
   simpa only [add_zero] using he)
 have hv:=congrArg Fin.val hh
 simp only [Fin.val_zero,Fin.val_ofNat,Nat.mod_eq_of_lt hdn] at hv
 omega
theorem z198 {V:Type*} [Fintype V] {G:SimpleGraph V}
   (hα:G.indepNum≤2) {n:ℕ} (hn: 7≤ n)
   (hc:SimpleGraph.cycleGraph n⊑G):SimpleGraph.cycleGraph (n - 1)⊑G:=by
 classical
 let:NeZero n:=⟨by omega⟩
 let:NeZero (n - 1):=⟨by omega⟩
 obtain ⟨f⟩:=hc
 have h22:(2:Fin n)+2=4:=by
   apply Fin.ext
   change (2 % n+2 % n) % n=4 % n
   simp only [Nat.mod_eq_of_lt (by omega: 2 < n)]
 have z13f:∀ i:Fin n,G.Adj (f i) (f (i+1)):=by
   intro i
   exact f.toHom.map_adj ((zd1 (by omega)).mpr (Or.inr rfl))
 by_cases z178:∃ i:Fin n,G.Adj (f i) (f (i+2))
 · obtain ⟨i,hi⟩:=z178
   let g:Fin (n - 1) → V:=fun j => f (i+z41 (by omega: 3≤ n) j)
   apply z94 (by omega) g
   · intro a b hab
     exact z12a (by omega) (add_left_cancel (f.injective hab))
   · intro j
     rcases z167 (by omega: 3≤ n) j with ⟨hj,hj'⟩ | hj
     · simpa only [g,hj,hj',add_zero] using hi
     · simpa only [g,hj,← add_assoc] using z13f (i+z41 (by omega) j)
 · push Not at z178
   have z19b:∀ i:Fin n,G.Adj (f i) (f (i+4)):=by
     intro i
     have h02:i≠i+2:=zc3 i 2 (by omega) (by omega)
     have h04:i≠i+4:=zc3 i 4 (by omega) (by omega)
     have h24:i+2≠i+4:=by
       have hn24:=zc3 (i+2) 2 (by omega) (by omega)
       change i+2≠i+2+2 at hn24
       simpa only [add_assoc,h22] using hn24
     apply zae hα (z:=f (i+2))
     · exact fun hh => h04 (f.injective hh)
     · exact fun hh => h02 (f.injective hh)
     · exact fun hh => h24 (f.injective hh).symm
     · exact z178 i
     · intro hh
       apply z178 (i+2)
       simpa only [add_assoc,h22] using hh.symm
   apply z94 (by omega) (fun j => f (z42 hn j))
   · exact f.injective.comp (z115 hn)
   · intro j
     rcases z153 hn j with hj | hj | hj
     · rw [hj]; exact z13f _
     · rw [hj]; exact z19b _
     · rw [hj]; exact (z19b _).symm
theorem zce {V:Type*} [Fintype V] {G:SimpleGraph V}
   (hα:G.indepNum≤2) {k:ℕ} (hk: 6≤ k) :
   ∀ n,k≤ n → SimpleGraph.cycleGraph n⊑G → SimpleGraph.cycleGraph k⊑G:=by
 intro n
 induction n using Nat.strong_induction_on with
 | h n ih =>
   intro hkn hc
   by_cases he:k=n
   · rw [he]; exact hc
   · exact ih (n - 1) (by omega) (by omega) (z198 hα (by omega) hc)
theorem z121 {V:Type*} [Fintype V] {G:SimpleGraph V}
   {k t:ℕ} (hk: 5≤ k) (_ht: 1≤ t)
   (hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G) (z20:G.cliqueNum≤ t)
   (Y:Set V) (hY:max k (2*t) < Y.ncard): 3≤ independence G Y:=by
 classical
 by_contra hn
 have hα:(G.induce Y).indepNum≤2:=by change independence G Y≤2; omega
 have hcY:(G.induce Y).cliqueNum≤ t:=by
   by_contra hh
   have hc:=(z17 (G.induce Y) (t+1)).mpr (by omega)
   have hc' :=(z17 G (t+1)).mp
     (hc.trans (SimpleGraph.Embedding.induce Y).isContained)
   omega
 have z3b:max k (2*t) < Fintype.card Y:=by
   rwa [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
 have z4b:=zd6 hα hcY (by omega)
 have hdel:=z91 hα hcY (by omega)
 obtain ⟨x,c,hc,hlen⟩:=z102 z4b (by omega) hα hdel
 have z1d5:SimpleGraph.cycleGraph (Fintype.card Y)⊑G.induce Y :=
   (SimpleGraph.cycleGraph_isContained_iff (by omega)).mpr ⟨x,c,hc,hlen⟩
 have z1f0:=zce hα (by omega: 6≤ k+1)
   (Fintype.card Y) (by omega) z1d5
 exact hcycle (z1f0.trans (SimpleGraph.Embedding.induce Y).isContained)
abbrev zb0 {V:Type*} (G:SimpleGraph V) (X:Set V):SimpleGraph V where
 Adj u v:=G.Adj u v∧(u∉X∨v∉X)
 symm:=⟨fun _ _ h => ⟨h.1.symm,h.2.symm⟩⟩
 loopless:=⟨fun _ h => h.1.ne rfl⟩
end CycleClique
namespace CycleClique
open scoped SimpleGraph
theorem z16a {V:Type*} (G:SimpleGraph V) (X:Set V) :
   zb0 G X≤ G:=fun _ _ h => h.1
def z5 {V:Type*} (G:SimpleGraph V) (X:Set V) (x y:V) (d:ℕ):Prop :=
 x∈X∧y∈X∧x≠y ∧ ∃ p:G.Walk x y,
   p.IsPath∧p.length=d+1 ∧ ∀ v∈p.support,v∈X → v=x∨v=y
def z1 {V:Type*} (G:SimpleGraph V) (X:Set V) (x:V):ℕ → Set V
 | 0 => G.neighborSet x \ X
 | r+1 => z0 G (z1 G X x r) \ X
theorem z1c {V:Type*} (G:SimpleGraph V) (X:Set V)
   (x:V) (r:ℕ):z1 G X x r⊆Xᶜ:=by
 cases r <;> exact fun _ h => h.2
theorem z55 {V:Type*} (G:SimpleGraph V) (X:Set V)
   (x:V) (r:ℕ):z1 G X x r⊆z1 G X x (r+1) :=
 fun _ h => ⟨Or.inl h,z1c G X x r h⟩
theorem zbf {V:Type*} (G:SimpleGraph V) (X:Set V)
   (x:V) (r:ℕ) :
   z0 G (z1 G X x r)⊆z1 G X x (r+1)∪X:=by
 intro v hv
 by_cases hx:v∈X
 · exact Or.inr hx
 · exact Or.inl ⟨hv,hx⟩
theorem z6a {V:Type*} {G:SimpleGraph V} {X:Set V} {x z:V}
   {r:ℕ} (hz:z∈z1 G X x r) :
   ∃ p:(zb0 G X).Walk x z,p.length≤ r+1 ∧
     ∀ v∈p.support,v=x∨v∉X:=by
 induction r generalizing z with
 | zero =>
   change G.Adj x z∧z∉X at hz
   let p:(zb0 G X).Walk x z:= .cons ⟨hz.1,Or.inr hz.2⟩ .nil
   refine ⟨p,by change 1≤1; omega,?_⟩
   dsimp [p]
   intro v hv
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hv
   rcases hv with rfl | rfl
   · exact Or.inl rfl
   · exact Or.inr hz.2
 | succ r ih =>
   change (z∈z1 G X x r ∨ ∃ u∈z1 G X x r,G.Adj u z)∧z∉X at hz
   rcases hz.1 with hold | ⟨u,hu,huz⟩
   · obtain ⟨p,hp,hs⟩:=ih hold
     exact ⟨p,by omega,hs⟩
   · obtain ⟨p,hp,hs⟩:=ih hu
     refine ⟨p.concat ⟨huz,Or.inr hz.2⟩,?_,?_⟩
     · rw [SimpleGraph.Walk.length_concat]
       omega
     · intro v hv
       simp only [SimpleGraph.Walk.support_concat,List.mem_append,List.mem_singleton] at hv
       rcases hv with hv | rfl
       · exact hs v hv
       · exact Or.inr hz.2
theorem z5a {V:Type*} {G:SimpleGraph V} {X:Set V}
   {x y:V} (hx:x∈X) (hy:y∈X) (hxy:x≠y)
   (p:(zb0 G X).Walk x y)
   (hs:∀ v∈p.support,v∈X → v=x∨v=y) :
   ∃ d,1≤ d∧d+1≤ p.length∧z5 G X x y d:=by
 classical
 let q:=p.bypass
 have hq:q.IsPath:=p.bypass_isPath
 have hpos: 0 < q.length:=SimpleGraph.Walk.not_nil_iff_lt_length.mp
   (fun hn => hxy hn.eq)
 have htwo: 2≤ q.length:=by
   by_contra hn
   have hh:=q.adj_of_length_eq_one (by omega)
   exact hh.2.elim (fun hn => hn hx) (fun hn => hn hy)
 refine ⟨q.length - 1,by omega,?_,hx,hy,hxy,
   q.mapLe (z16a G X),hq.mapLe _,?_,?_⟩
 · have hh:=p.length_bypass_le_length; dsimp [q] at *; omega
 · simp only [SimpleGraph.Walk.length_mapLe]; omega
 · intro v hv hvX
   have hvq:v∈q.support:=by simpa only [SimpleGraph.Walk.support_mapLe_eq_support] using hv
   exact hs v (p.support_bypass_subset_support hvq) hvX
theorem z90 {V:Type*} {G:SimpleGraph V} {X:Set V}
   {x y z:V} {r s:ℕ} (hx:x∈X) (hy:y∈X) (hxy:x≠y)
   (hzx:z∈z1 G X x r) (hzy:z∈z1 G X y s) :
   ∃ d,1≤ d∧d≤ r+s+1∧z5 G X x y d:=by
 obtain ⟨p,hp,hps⟩:=z6a hzx
 obtain ⟨q,hq,hqs⟩:=z6a hzy
 obtain ⟨d,hd,hlen,hout⟩:=z5a hx hy hxy (p.append q.reverse) (by
   intro v hv hvX
   rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hv with hv | hv
   · exact Or.inl ((hps v hv).resolve_right (fun hn => hn hvX))
   · exact Or.inr ((hqs v (by simpa using hv)).resolve_right (fun hn => hn hvX)))
 refine ⟨d,hd,?_,hout⟩
 simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse] at hlen
 omega
theorem z107 {V:Type*} {G:SimpleGraph V} {X:Set V}
   {x y z w:V} {r s:ℕ} (hx:x∈X) (hy:y∈X) (hxy:x≠y)
   (hz:z∈z1 G X x r) (hw:w∈z1 G X y s) (hzw:G.Adj z w) :
   ∃ d,1≤ d∧d≤ r+s+2∧z5 G X x y d:=by
 obtain ⟨p,hp,hps⟩:=z6a hz
 obtain ⟨q,hq,hqs⟩:=z6a hw
 let P:=(p.concat ⟨hzw,Or.inl (z1c G X x r hz)⟩).append q.reverse
 obtain ⟨d,hd,hlen,hout⟩:=z5a hx hy hxy P (by
   intro v hv hvX
   rcases (SimpleGraph.Walk.mem_support_append_iff _ _).mp hv with hv | hv
   · simp only [SimpleGraph.Walk.support_concat,List.mem_append,List.mem_singleton] at hv
     rcases hv with hv | rfl
     · exact Or.inl ((hps v hv).resolve_right (fun hn => hn hvX))
     · exact (z1c G X y s hw hvX).elim
   · exact Or.inr ((hqs v (by simpa using hv)).resolve_right (fun hn => hn hvX)))
 refine ⟨d,hd,?_,hout⟩
 dsimp [P] at hlen
 simp only [SimpleGraph.Walk.length_append,SimpleGraph.Walk.length_reverse] at hlen
 rw [SimpleGraph.Walk.length_concat] at hlen
 omega
theorem z47 {V:Type*} {G:SimpleGraph V} {X:Set V}
   {x y:V} {r s:ℕ} (hx:x∈X) (hy:y∈X) (hxy:x≠y)
   (hno:∀ d,1≤ d → d≤ r+s+2 → ¬ z5 G X x y d) :
   Disjoint (z1 G X x r) (z1 G X y s) ∧
     ∀ z∈z1 G X x r,∀ w∈z1 G X y s,¬ G.Adj z w:=by
 constructor
 · apply Set.disjoint_left.mpr
   intro z hzx hzy
   obtain ⟨d,hd,hd',hp⟩:=z90 hx hy hxy hzx hzy
   exact hno d hd (by omega) hp
 · intro z hz w hw hzw
   obtain ⟨d,hd,hd',hp⟩:=z107 hx hy hxy hz hw hzw
   exact hno d hd hd' hp
theorem z117 {V:Type*} {G:SimpleGraph V} {X:Set V}
   {x y z:V} {r:ℕ} (hx:x∈X) (hy:y∈X) (hxy:x≠y)
   (hz:z∈z1 G X x r) (hzy:G.Adj z y) :
   ∃ d,1≤ d∧d≤ r+1∧z5 G X x y d:=by
 obtain ⟨p,hp,hps⟩:=z6a hz
 obtain ⟨d,hd,hlen,hout⟩:=z5a hx hy hxy
   (p.concat ⟨hzy,Or.inl (z1c G X x r hz)⟩) (by
     intro v hv hvX
     simp only [SimpleGraph.Walk.support_concat,List.mem_append,List.mem_singleton] at hv
     rcases hv with hv | rfl
     · exact Or.inl ((hps v hv).resolve_right (fun hn => hn hvX))
     · exact Or.inr rfl)
 refine ⟨d,hd,?_,hout⟩
 rw [SimpleGraph.Walk.length_concat] at hlen
 omega
theorem z3f {V:Type*} {G:SimpleGraph V} {X:Set V}
   {x y:V} {r:ℕ} (hx:x∈X) (hy:y∈X) (hxy:x≠y)
   (hno:∀ d,1≤ d → d≤ r+1 → ¬ z5 G X x y d) :
   ∀ z∈z1 G X x r,¬ G.Adj z y:=by
 intro z hz hzy
 obtain ⟨d,hd,hd',hp⟩:=z117 hx hy hxy hz hzy
 exact hno d hd hd' hp
noncomputable local instance (p:Prop):Decidable p:=Classical.propDecidable p
end CycleClique
namespace CycleClique
open scoped SimpleGraph
noncomputable local instance (p:Prop):Decidable p:=Classical.propDecidable p
structure y0 {V:Type*} (G:SimpleGraph V) (Q:Set V) where
 chains:List (List V)
 nonempty:∀ c∈chains,c ≠ []
 nodup:chains.flatten.Nodup
 edges:∀ c∈chains,c.IsChain G.Adj
 positive:∀ c∈chains,c.IsChain (fun u v => u∉Q∨v∉Q)
 ends:∀ c∈chains,(∀ x∈c.head?,x∈Q)∧(∀ x∈c.getLast?,x∈Q)
 cover:∀ x∈Q,x∈chains.flatten
theorem z12c {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (hQ:G.IsClique Q) (C:List (List V)) (hne: []∉C)
   (hnd:C.flatten.Nodup) (z1a4:∀ c∈C,c.IsChain G.Adj)
   (z11b:∀ c∈C,(∀ x∈c.head?,x∈Q)∧(∀ x∈c.getLast?,x∈Q)) :
   C.flatten.IsChain G.Adj:=by
 apply (List.isChain_flatten hne).mpr
 refine ⟨z1a4,?_⟩
 apply List.Pairwise.isChain
 apply (List.nodup_flatten.mp hnd).2.imp_of_mem
 intro a b ha hb hab x hx y hy
 apply hQ ((z11b a ha).2 x hx) ((z11b b hb).1 y hy)
 intro hxy
 exact List.disjoint_left.mp hab (List.mem_of_mem_getLast? hx)
   (hxy ▸ List.mem_of_mem_head? hy)
theorem z10f {V:Type*} {Q:Set V} (C:List (List V))
   (hne:∀ c∈C,c ≠ [])
   (z11b:∀ c∈C,(∀ x∈c.head?,x∈Q)∧(∀ x∈c.getLast?,x∈Q))
   (hf:C.flatten ≠ []) :
   C.flatten.head hf∈Q∧C.flatten.getLast hf∈Q:=by
 have hc:C ≠ []:=by intro h; simp [h] at hf
 constructor
 · rw [List.head_flatten_eq_head_head hf (hne _ (List.head_mem hc))]
   apply (z11b _ (List.head_mem hc)).1
   exact List.head?_eq_some_head (hne _ (List.head_mem hc))
 · rw [List.getLast_flatten_eq_getLast_getLast hf (hne _ (List.getLast_mem hc))]
   apply (z11b _ (List.getLast_mem hc)).2
   exact List.getLast?_eq_some_getLast (hne _ (List.getLast_mem hc))
theorem zd0 {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (hQ:G.IsClique Q) (C:List (List V))
   (hne:∀ c∈C,c ≠ []) (hnd:C.flatten.Nodup)
   (z1a4:∀ c∈C,c.IsChain G.Adj)
   (z11b:∀ c∈C,(∀ x∈c.head?,x∈Q)∧(∀ x∈c.getLast?,x∈Q))
   (hlen: 3≤ C.flatten.length) :
   SimpleGraph.cycleGraph C.flatten.length⊑G:=by
 have hfn:C.flatten ≠ []:=by intro h; simp [h] at hlen
 have z1de:=z12c hQ C (fun hh => hne [] hh rfl) hnd z1a4 z11b
 let p:=SimpleGraph.Walk.ofSupport C.flatten hfn z1de
 have hp:p.IsPath:=p.isPath_def.mpr (by simpa [p] using hnd)
 have z11e:p.length=C.flatten.length - 1:=SimpleGraph.Walk.length_ofSupport _ _
 obtain ⟨hx,hy⟩:=z10f C hne z11b hfn
 have hxy:C.flatten.head hfn≠C.flatten.getLast hfn:=by
   intro heq
   obtain ⟨v,hv⟩:=(List.Nodup.head_eq_getLast_iff hfn hnd).mp heq
   simp [hv] at hlen
 have hadj:=hQ hy hx (Ne.symm hxy)
 have hc:(SimpleGraph.Walk.cons hadj p).IsCycle:=by
   apply (p.cons_isCycle_iff hadj).mpr
   refine ⟨hp,?_⟩
   intro he
   have hh:=hp.length_eq_one_of_mem_edges (by simpa only [Sym2.eq_swap] using he)
   omega
 apply (SimpleGraph.cycleGraph_isContained_iff (by omega)).mpr
 refine ⟨_,SimpleGraph.Walk.cons hadj p,hc,?_⟩
 rw [SimpleGraph.Walk.length_cons,z11e]
 omega
theorem z97 {V:Type*} (l:List V) :
   (l.map (fun v => [v])).flatten=l:=by
 induction l with
 | nil => rfl
 | cons x l ih => simp only [List.map_cons,List.flatten_cons,ih,List.singleton_append]
noncomputable def y0.empty {V:Type*} [Fintype V]
   (G:SimpleGraph V) (Q:Set V):y0 G Q:=by
 classical
 refine ⟨Q.toFinset.toList.map (fun v => [v]),?_,?_,?_,?_,?_,?_⟩
 · intro c hc
   obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hc
   simp
 · rw [z97]
   exact Q.toFinset.nodup_toList
 · intro c hc
   obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hc
   exact .singleton _
 · intro c hc
   obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hc
   exact .singleton _
 · intro c hc
   obtain ⟨v,hv,rfl⟩:=List.mem_map.mp hc
   have hvQ:v∈Q:=by simpa using hv
   simpa using And.intro hvQ hvQ
 · intro x hx
   simpa using hx
noncomputable def y0.z2 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q):ℕ :=
 P.chains.flatten.length - Q.ncard
noncomputable def y0.z4 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q):ℕ :=
 Q.ncard - P.chains.length
noncomputable def y0.z13 {V:Type*}
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q):List (List V):=by
 classical
 exact P.chains.filter (fun c => c.length=1)
noncomputable def y0.z46 {V:Type*}
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q):List (List V):=by
 classical
 exact P.chains.filter (fun c => c.length≠1)
noncomputable def y0.ze {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q):ℕ :=
 Q.ncard - P.z13.length
theorem y0.z66 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) :
   P.chains.flatten.length=Q.ncard+P.z2:=by
 classical
 have h:Q.ncard≤ P.chains.flatten.length:=by
   have hsub:Q⊆(P.chains.flatten.toFinset:Set V):=by
     intro x hx
     exact List.mem_toFinset.mpr (P.cover x hx)
   have hh:=Set.ncard_le_ncard hsub
   simpa only [Set.ncard_coe_finset,List.toFinset_card_of_nodup P.nodup] using hh
 dsimp [y0.z2]
 omega
theorem y0.z93 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) :
   P.chains.flatten.countP (fun x => decide (x∈Q))=Q.ncard:=by
 classical
 let l:=P.chains.flatten.filter (fun x => decide (x∈Q))
 have hnd:l.Nodup:=P.nodup.filter _
 have he:(l.toFinset:Set V)=Q:=by
   ext x
   simp only [Finset.mem_coe,List.mem_toFinset,l,List.mem_filter,decide_eq_true_eq]
   exact ⟨And.right,fun hx => ⟨P.cover x hx,hx⟩⟩
 have hc:=congrArg Set.ncard he
 simpa only [Set.ncard_coe_finset,List.toFinset_card_of_nodup hnd,
   l,← List.countP_eq_length_filter] using hc
theorem y0.z4c {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) :
   P.chains.length≤ Q.ncard:=by
 classical
 have hb:∀ c∈P.chains,1≤ c.countP (fun x => decide (x∈Q)):=by
   intro c hc
   apply Nat.succ_le_iff.mpr
   apply List.countP_pos_iff.mpr
   let x:=c.head (P.nonempty c hc)
   refine ⟨x,List.head_mem _,?_⟩
   apply decide_eq_true
   exact (P.ends c hc).1 x (List.head?_eq_some_head _)
 have hh:=List.sum_le_sum hb
 rw [← List.countP_flatten,P.z93] at hh
 simpa using hh
theorem y0.z50 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) :
   P.z13.length≤ Q.ncard :=
 (List.length_filter_le _ _).trans P.z4c
theorem y0.partition {V:Type*}
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) :
   (P.z46 ++ P.z13).Perm P.chains:=by
 classical
 simpa [y0.z46,y0.z13] using
   List.filter_append_perm (fun c:List V => decide (c.length≠1)) P.chains
theorem zac {V:Type*} (C:List (List V))
   (h:∀ c∈C,c.length=1):C.flatten.length=C.length:=by
 induction C with
 | nil => rfl
 | cons c C ih =>
   rw [List.flatten_cons,List.length_append,h c (by simp),
     ih (fun c hc => h c (by simp [hc])),List.length_cons]
   omega
theorem y0.z7c {V:Type*}
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) :
   P.z13.flatten.length=P.z13.length:=by
 apply zac
 intro c hc
 exact (List.mem_filter.mp hc).2 |> of_decide_eq_true
theorem y0.z81 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q)
   {k:ℕ} (hk: 3≤ k) (hQ:G.IsClique Q)
   (hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G)
   (ht:Q.ncard≤ k) (hlo:k+1 - Q.ncard≤ P.z2)
   (hhi:P.z2≤ k+1 - P.ze):False:=by
 classical
 let u:=k+1 - P.z2 - P.ze
 have hi:P.ze≤ Q.ncard:=Nat.sub_le _ _
 have he:P.ze+P.z13.length=Q.ncard:=by
   dsimp [y0.ze]
   have:=P.z50
   omega
 have hup:u≤ P.z13.length:=by dsimp [u]; omega
 let C:=P.z46 ++ P.z13.take u
 have hsub:C.Sublist (P.z46 ++ P.z13) :=
   List.Sublist.append (.refl _) (List.take_sublist _ _)
 have hmem:∀ c∈C,c∈P.chains:=fun c hc => P.partition.subset (hsub.subset hc)
 have hnd:C.flatten.Nodup:=hsub.flatten.nodup
   (P.partition.flatten.nodup_iff.mpr P.nodup)
 have z201:=P.partition.flatten.length_eq
 rw [List.flatten_append,List.length_append,P.z7c,
   P.z66] at z201
 have z202:(P.z13.take u).flatten.length=u:=by
   rw [zac _ (by
     intro c hc
     exact of_decide_eq_true (List.mem_filter.mp (List.mem_of_mem_take hc)).2),
     List.length_take,Nat.min_eq_left hup]
 have hlen:C.flatten.length=k+1:=by
   dsimp [C]
   rw [List.flatten_append,List.length_append,z202]
   dsimp [u] at *
   omega
 apply hcycle
 rw [← hlen]
 apply zd0 hQ C (fun c hc => P.nonempty c (hmem c hc)) hnd
   (fun c hc => P.edges c (hmem c hc)) (fun c hc => P.ends c (hmem c hc))
 omega
@[simp] theorem y0.empty_amount {V:Type*} [Fintype V]
   (G:SimpleGraph V) (Q:Set V):(y0.empty G Q).z2=0:=by
 classical
 simp [y0.z2,y0.empty,z97,Set.ncard_eq_toFinset_card']
end CycleClique
namespace CycleClique
open scoped SimpleGraph
noncomputable local instance (p:Prop):Decidable p:=Classical.propDecidable p
def y0.Optimal {V:Type*} [Fintype V] {G:SimpleGraph V} {Q:Set V}
   (k:ℕ) (P:y0 G Q):Prop :=
 P.z2 < k+1 - Q.ncard ∧
 (∀ R:y0 G Q,R.z2 < k+1 - Q.ncard → R.z2≤ P.z2) ∧
 (∀ R:y0 G Q,R.z2=P.z2 → P.z4≤ R.z4)
theorem y0.exists_optimal {V:Type*} [Fintype V]
   (G:SimpleGraph V) (Q:Set V) {k:ℕ} (ht:Q.ncard≤ k) :
   ∃ P:y0 G Q,P.Optimal k:=by
 classical
 let T:ℕ → Prop:=fun a => ∃ P:y0 G Q,P.z2=a
 let L:=Nat.findGreatest T (k - Q.ncard)
 have hT0:T 0:=⟨y0.empty G Q,y0.empty_amount G Q⟩
 have hTL:T L:=Nat.findGreatest_spec (Nat.zero_le _) hT0
 let E:ℕ → Prop:=fun e => ∃ P:y0 G Q,P.z2=L∧P.z4=e
 have hE:∃ e,E e:=by obtain ⟨P,hP⟩:=hTL; exact ⟨P.z4,P,hP,rfl⟩
 obtain ⟨P,hPL,hPe⟩:=Nat.find_spec hE
 refine ⟨P,?_,?_,?_⟩
 · have hh:=Nat.findGreatest_le (P:=T) (k - Q.ncard)
   dsimp [L] at hPL
   omega
 · intro R hR
   have hh:=Nat.le_findGreatest (P:=T) (show R.z2≤ k - Q.ncard by omega)
     ⟨R,rfl⟩
   dsimp [L] at hPL
   omega
 · intro R hR
   have hh:=Nat.find_min' hE (show E R.z4 from ⟨R,hR.trans hPL,rfl⟩)
   omega
theorem y0.z181 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} {k:ℕ} (P:y0 G Q)
   (hopt:P.Optimal k) (hk: 3≤ k) (hQ:G.IsClique Q)
   (hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G) (ht:Q.ncard≤ k)
   (R:y0 G Q)
   (hl:P.z2≤ R.z2) (htie:P.z2=R.z2 → R.z4 < P.z4)
   (hu:R.z2≤ k+1 - R.ze):False:=by
 by_cases hh:k+1 - Q.ncard≤ R.z2
 · exact R.z81 hk hQ hcycle ht hh hu
 · have hle:=hopt.2.1 R (by omega)
   have heq:R.z2=P.z2:=by omega
   have he:=hopt.2.2 R heq
   have he' :=htie heq.symm
   omega
theorem isChain_bridge {V:Type*} {R:V → V → Prop}
   (hR:∀ ⦃first second⦄,R first second → R second first)
   {x y:V} {u v I:List V} (hu:(x ::u).IsChain R)
   (hv:(y ::v).IsChain R) (hI:(x ::I ++ [y]).IsChain R) :
   ((x ::u).reverse ++ I ++ (y ::v)).IsChain R:=by
 have hr:(u.reverse ++ [x]).IsChain R:=by
   simpa using List.isChain_reverse.mpr (hu.imp (fun _ _ h => hR h))
 have h₁:(u.reverse ++ [x] ++ (I ++ [y])).IsChain R :=
   hr.append_overlap hI (by simp)
 have h₂:((u.reverse ++ [x] ++ I) ++ [y] ++ v).IsChain R:=by
   apply List.IsChain.append_overlap (l₂:= [y]) (by simpa only [List.append_assoc] using h₁)
     (by simpa using hv) (by simp)
 simpa only [List.reverse_cons,List.append_assoc,List.singleton_append] using h₂
theorem nodup_bridge {V:Type*} {A B C I:List V}
   (h:(A ++ B ++ C).Nodup) (hi:I.Nodup) (hdis:I.Disjoint (A ++ B ++ C)) :
   (A.reverse ++ I ++ B ++ C).Nodup:=by
 have hsym:=hdis.symm
 simp only [List.nodup_append,List.nodup_reverse,List.mem_append,List.mem_reverse,
   List.disjoint_left] at *
 aesop
theorem y0.z17c {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q)
   (C:List (List V)) {x y:V} (u v I:List V)
   (zc:((x ::u) ++ (y ::v) ++ C.flatten).Perm P.chains.flatten)
   (hne:∀ c∈C,c ≠ []) (hc:∀ c∈C,c.IsChain G.Adj)
   (hcp:∀ c∈C,c.IsChain (fun a b => a∉Q∨b∉Q))
   (hce:∀ c∈C,(∀ a∈c.head?,a∈Q)∧(∀ a∈c.getLast?,a∈Q))
   (hu:(x ::u).IsChain G.Adj) (hv:(y ::v).IsChain G.Adj)
   (hup:(x ::u).IsChain (fun a b => a∉Q∨b∉Q))
   (hvp:(y ::v).IsChain (fun a b => a∉Q∨b∉Q))
   (hue:∀ a∈(x ::u).getLast?,a∈Q)
   (hve:∀ a∈(y ::v).getLast?,a∈Q)
   (hI:(x ::I ++ [y]).IsChain G.Adj)
   (hIp:(x ::I ++ [y]).IsChain (fun a b => a∉Q∨b∉Q))
   (hIn:I.Nodup) (hId:I.Disjoint P.chains.flatten) :
   ∃ R:y0 G Q,R.z2=P.z2+I.length∧R.chains.length=C.length+1:=by
 classical
 let J:=(x ::u).reverse ++ I ++ (y ::v)
 have hJn:J ≠ []:=by simp [J]
 have hnd:(J ++ C.flatten).Nodup:=by
   apply nodup_bridge (zc.nodup_iff.mpr P.nodup) hIn
   apply List.disjoint_left.mpr
   intro a ha hb
   exact List.disjoint_left.mp hId ha (zc.subset hb)
 have hJe:(∀ a∈J.head?,a∈Q)∧(∀ a∈J.getLast?,a∈Q):=by
   constructor
   · intro a ha
     apply hue a
     simpa only [J,List.append_assoc,List.head?_append_of_ne_nil _ (by simp:(x ::u).reverse ≠ []),
       List.head?_reverse] using ha
   · intro a ha
     apply hve a
     simpa only [J,← List.append_assoc,
       List.getLast?_append_of_ne_nil _ (by simp:y ::v ≠ [])] using ha
 let R:y0 G Q :=
   { chains:=J ::C
     nonempty:=by intro c hc; simp only [List.mem_cons] at hc; rcases hc with rfl | hc; exact hJn; exact hne c hc
     nodup:=hnd
     edges:=by
       intro c hc'
       simp only [List.mem_cons] at hc'
       rcases hc' with rfl | hc'
       · exact isChain_bridge (fun _ _ h => h.symm) hu hv hI
       · exact hc c hc'
     positive:=by
       intro c hc'
       simp only [List.mem_cons] at hc'
       rcases hc' with rfl | hc'
       · exact isChain_bridge (fun _ _ h => h.symm) hup hvp hIp
       · exact hcp c hc'
     ends:=by intro c hc'; simp only [List.mem_cons] at hc'; rcases hc' with rfl | hc'; exact hJe; exact hce c hc'
     cover:=by
       intro a ha
       have hh:=zc.mem_iff.mpr (P.cover a ha)
       simp only [J,List.flatten_cons,List.mem_append,List.mem_reverse] at hh ⊢
       tauto }
 refine ⟨R,?_,rfl⟩
 have hh:=zc.length_eq
 rw [P.z66] at hh
 change ((x ::u).reverse ++ I ++ (y ::v) ++ C.flatten).length - Q.ncard =
   P.z2+I.length
 simp only [List.length_append,List.length_reverse] at hh ⊢
 omega
end CycleClique
namespace CycleClique
open scoped SimpleGraph
noncomputable local instance (p:Prop):Decidable p:=Classical.propDecidable p
noncomputable def zb {V:Type*} (Q:Set V) (b:Bool):List V → List V
 | [] => []
 | a ::l => (if b then [a] else []) ++ zb Q (decide (a∈Q)) l
theorem z39 {V:Type*} (Q:Set V) (b:Bool) (c:List V) :
   (zb Q b c).Sublist c:=by
 induction c generalizing b with
 | nil => simp [zb]
 | cons a c ih =>
   cases b <;> simp only [zb,Bool.false_eq_true,↓reduceIte,
     List.nil_append,List.singleton_append]
   · exact (ih _).cons _
   · exact (ih _).cons_cons _
theorem zed {V:Type*} (Q:Set V) (b:Bool) (c:List V)
   (hne:c ≠ []) (hend:∀ a∈c.getLast?,a∈Q) :
   (zb Q b c).length+1=c.countP (· ∈ Q)+(if b then 1 else 0):=by
 induction c generalizing b with
 | nil => contradiction
 | cons a c ih =>
   cases c with
   | nil =>
     have ha:a∈Q:=hend a (by simp)
     cases b <;> simp [zb,ha]
   | cons d c =>
     have he:∀ v∈(d ::c).getLast?,v∈Q:=by simpa using hend
     have hh:=ih (decide (a∈Q)) (by simp) he
     cases b <;> by_cases ha:a∈Q <;>
       simp [zb,ha,List.countP_cons] at hh ⊢ <;> omega
def z2c {V:Type*} (Q:Set V) (b:Bool) (A:List V):Prop :=
 (A = []∧b=true)∨(A ≠ [] ∧ ∀ a∈A.getLast?,a∈Q)
theorem z134 {V:Type*} {Q:Set V} {b:Bool} {a:V} {A:List V} :
   z2c Q (decide (a∈Q)) A↔z2c Q b (a ::A):=by
 cases A with
 | nil => simp [z2c]
 | cons d A => simp [z2c]
theorem z59 {V:Type*} (Q:Set V) (b:Bool) (c:List V) (x:V) :
   x∈zb Q b c ↔ ∃ A B,c=A ++ x ::B∧z2c Q b A:=by
 induction c generalizing b with
 | nil => simp [zb]
 | cons a c ih =>
   simp only [zb,List.mem_append]
   constructor
   · rintro (h | h)
     · have hb:b=true:=by cases b <;> simp_all
       have hx:x=a:=by simpa [hb] using h
       subst x
       exact ⟨[],c,rfl,Or.inl ⟨rfl,hb⟩⟩
     · obtain ⟨A,B,h,hcut⟩:=(ih _).mp h
       exact ⟨a ::A,B,by simp [h],z134.mp hcut⟩
   · rintro ⟨A,B,h,hcut⟩
     cases A with
     | nil =>
       have he:a=x∧c=B:=by simpa using h
       have hb:b=true:=by simpa [z2c] using hcut
       simp [hb,he.1]
     | cons d A =>
       have he:a=d∧c=A ++ x ::B:=by simpa using h
       rcases he with ⟨rfl,he⟩
       right
       exact (ih _).mpr ⟨A,B,he,z134.mpr hcut⟩
noncomputable def y0.reps {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q):List V:=(P.chains.map (zb Q true)).flatten
theorem z87 {V:Type*} (Q:Set V) (C:List (List V)) :
   (C.map (zb Q true)).flatten.Sublist C.flatten:=by
 induction C with
 | nil => simp
 | cons c cs ih =>
   simp only [List.map_cons,List.flatten_cons]
   exact (z39 Q true c).append ih
theorem y0.z9e {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q):P.reps.Sublist P.chains.flatten :=
 z87 Q P.chains
theorem zf9 {V:Type*} (Q:Set V) (C:List (List V))
   (hc:∀ c∈C,c ≠ [] ∧ ∀ a∈c.getLast?,a∈Q) :
   (C.map (zb Q true)).flatten.length=C.flatten.countP (· ∈ Q):=by
 induction C with
 | nil => simp
 | cons c cs ih =>
   have he:=zed Q true c (hc c (by simp)).1 (hc c (by simp)).2
   have ht:=ih (fun l hl => hc l (by simp [hl]))
   simp only [List.map_cons,List.flatten_cons,List.length_append,List.countP_append]
   simp only [↓reduceIte] at he
   omega
theorem y0.z129 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q):P.reps.length=Q.ncard :=
 (zf9 Q P.chains
   (fun c hc => ⟨P.nonempty c hc,(P.ends c hc).2⟩)).trans P.z93
theorem z9a {V:Type*} {Q:Set V} {b:Bool} {c A B:List V} {x:V}
   (hn:c.Nodup) (hx:x∈zb Q b c) (hc:c=A ++ x ::B) :
   z2c Q b A:=by
 obtain ⟨A',B',hc',hcut⟩:=(z59 Q b c x).mp hx
 have hh:=List.nodup_append.mp (hc ▸ hn)
 have hnA:x∉A:=fun h => hh.2.2 x h x (by simp) rfl
 have hnB:x∉B:=(List.nodup_cons.mp hh.2.1).1
 have he:=(List.append_cons_inj_of_notMem hnA hnB).mp (hc.symm.trans hc')
 simpa only [he.1] using hcut
theorem z123 {V:Type*} {c:List V} {x y:V}
   (hx:x∈c) (hy:y∈c) (hne:x≠y) :
   (∃ A u v,c=A ++ (x ::u) ++ y ::v) ∨
   (∃ A u v,c=A ++ (y ::u) ++ x ::v):=by
 obtain ⟨A,B,rfl⟩:=List.mem_iff_append.mp hx
 have hy' :y∈A∨y∈B:=by simpa [hne.symm] using hy
 rcases hy' with h | h
 · obtain ⟨C,D,rfl⟩:=List.mem_iff_append.mp h
   exact Or.inr ⟨C,D,B,by simp only [List.append_assoc,List.cons_append]⟩
 · obtain ⟨C,D,rfl⟩:=List.mem_iff_append.mp h
   exact Or.inl ⟨A,C,D,by simp only [List.append_assoc,List.cons_append]⟩
theorem z71 {V:Type*} {Q:Set V} {b:Bool} {c:List V}
   {x y:V} (hn:c.Nodup) (hx:x∈zb Q b c)
   (hy:y∈zb Q b c) (A u v:List V)
   (hc:c=A ++ (x ::u) ++ y ::v) :
   z2c Q b A ∧ ∀ a∈(x ::u).getLast?,a∈Q:=by
 refine ⟨z9a hn hx (by simpa only [List.append_assoc,List.cons_append] using hc),?_⟩
 have hh:=z9a hn hy hc
 rcases hh with ⟨hh,_⟩ | ⟨_,hh⟩
 · simp at hh
 · simpa only [List.getLast?_append_of_ne_nil _ (by simp:x ::u ≠ [])] using hh
noncomputable def z23 {V:Type*} (A:List V):List (List V) :=
 if A = [] then [] else [A]
@[simp] theorem prefixChains_flatten {V:Type*} (A:List V) :
   (z23 A).flatten=A:=by
 by_cases h:A = [] <;> simp [z23,h]
theorem z16d {V:Type*} {A c:List V} :
   c∈z23 A↔c=A∧A ≠ []:=by
 by_cases h:A = [] <;> simp [z23,h]
theorem z1b0 {V:Type*} {Q:Set V} {b:Bool} {c A B:List V}
   (hh:∀ a∈c.head?,a∈Q) (hc:c=A ++ B) (hcut:z2c Q b A)
   (hA:A ≠ []) :
   (∀ a∈A.head?,a∈Q)∧(∀ a∈A.getLast?,a∈Q):=by
 constructor
 · simpa only [hc,List.head?_append_of_ne_nil _ hA] using hh
 · rcases hcut with ⟨h,_⟩ | ⟨_,h⟩
   · contradiction
   · exact h
structure ClosedChain {V:Type*} (G:SimpleGraph V) (Q:Set V) (c:List V):Prop where
 nonempty:c ≠ []
 edges:c.IsChain G.Adj
 positive:c.IsChain (fun a b => a∉Q∨b∉Q)
 ends:(∀ a∈c.head?,a∈Q)∧(∀ a∈c.getLast?,a∈Q)
structure LooseTail {V:Type*} (G:SimpleGraph V) (Q:Set V) (c:List V):Prop where
 edges:c.IsChain G.Adj
 positive:c.IsChain (fun a b => a∉Q∨b∉Q)
 end_mem:∀ a∈c.getLast?,a∈Q
theorem y0.z11 {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q) {c:List V} (hc:c∈P.chains):ClosedChain G Q c :=
 ⟨P.nonempty c hc,P.edges c hc,P.positive c hc,P.ends c hc⟩
theorem ClosedChain.cut {V:Type*} {G:SimpleGraph V} {Q:Set V}
   {c A:List V} {x:V} {u:List V} (hc:ClosedChain G Q c)
   (he:c=A ++ x ::u) (hcut:z2c Q true A) :
   (∀ d∈z23 A,ClosedChain G Q d)∧LooseTail G Q (x ::u):=by
 have hed:(A ++ x ::u).IsChain G.Adj:=he ▸ hc.edges
 have hpo:(A ++ x ::u).IsChain (fun a b => a∉Q∨b∉Q):=he ▸ hc.positive
 constructor
 · intro d hd
   obtain ⟨rfl,hA⟩:=z16d.mp hd
   exact ⟨hA,hed.left_of_append,hpo.left_of_append,z1b0 hc.ends.1 he hcut hA⟩
 · refine ⟨hed.right_of_append,hpo.right_of_append,?_⟩
   simpa only [he,List.getLast?_append_of_ne_nil _ (by simp:x ::u ≠ [])] using hc.ends.2
theorem zee {V:Type*} (A U B W D:List V) :
   (U ++ W ++ (A ++ B ++ D)).Perm ((A ++ U) ++ (B ++ W) ++ D):=by
 apply Multiset.coe_eq_coe.mp
 simp only [← Multiset.coe_add]
 ac_rfl
theorem y0.z142 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q)
   {c d:List V} (D:List (List V)) (hP:P.chains.Perm (c ::d ::D))
   {x y:V} (A u B v I:List V) (hc:c=A ++ x ::u) (hd:d=B ++ y ::v)
   (zf5:z2c Q true A) (zf6:z2c Q true B)
   (hI:(x ::I ++ [y]).IsChain G.Adj)
   (hIp:(x ::I ++ [y]).IsChain (fun a b => a∉Q∨b∉Q))
   (hIn:I.Nodup) (hId:I.Disjoint P.chains.flatten) :
   ∃ R:y0 G Q,R.z2=P.z2+I.length:=by
 have hcc:=P.z11 (hP.mem_iff.mpr (by simp:c∈c ::d ::D))
 have hdd:=P.z11 (hP.mem_iff.mpr (by simp:d∈c ::d ::D))
 obtain ⟨hA,hu⟩:=hcc.cut hc zf5
 obtain ⟨hB,hv⟩:=hdd.cut hd zf6
 let C:=z23 A ++ z23 B ++ D
 have hC:∀ l∈C,ClosedChain G Q l:=by
   intro l hl
   simp only [C,List.mem_append] at hl
   rcases hl with (hl | hl) | hl
   · exact hA l hl
   · exact hB l hl
   · exact P.z11 (hP.mem_iff.mpr (by simp [hl]))
 have zc:((x ::u) ++ (y ::v) ++ C.flatten).Perm P.chains.flatten:=by
   apply List.Perm.trans _ hP.flatten.symm
   simp only [C,List.flatten_append,prefixChains_flatten,List.flatten_cons,hc,hd]
   simpa only [List.append_assoc] using zee A (x ::u) B (y ::v) D.flatten
 obtain ⟨R,hR,_⟩:=P.z17c C u v I zc
   (fun l hl => (hC l hl).nonempty) (fun l hl => (hC l hl).edges)
   (fun l hl => (hC l hl).positive) (fun l hl => (hC l hl).ends)
   hu.edges hv.edges hu.positive hv.positive hu.end_mem hv.end_mem hI hIp hIn hId
 exact ⟨R,hR⟩
theorem y0.z11f {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q)
   {c:List V} (D:List (List V)) (hP:P.chains.Perm (c ::D))
   {x y:V} (A u v I:List V) (hc:c=A ++ (x ::u) ++ y ::v)
   (hcut:z2c Q true A) (hum:∀ a∈(x ::u).getLast?,a∈Q)
   (hI:(x ::I ++ [y]).IsChain G.Adj)
   (hIp:(x ::I ++ [y]).IsChain (fun a b => a∉Q∨b∉Q))
   (hIn:I.Nodup) (hId:I.Disjoint P.chains.flatten) :
   ∃ R:y0 G Q,R.z2=P.z2+I.length:=by
 have hcc:=P.z11 (hP.mem_iff.mpr (by simp:c∈c ::D))
 obtain ⟨hA,hu⟩:=hcc.cut (by simpa only [List.append_assoc,List.cons_append] using hc) hcut
 have he:((x ::u) ++ y ::v).IsChain G.Adj:=by simpa only [List.cons_append] using hu.edges
 have hp:((x ::u) ++ y ::v).IsChain (fun a b => a∉Q∨b∉Q):=by
   simpa only [List.cons_append] using hu.positive
 have hve:∀ a∈(y ::v).getLast?,a∈Q:=by
   simpa only [hc,List.getLast?_append_of_ne_nil _ (by simp:y ::v ≠ [])] using hcc.ends.2
 let C:=z23 A ++ D
 have hC:∀ l∈C,ClosedChain G Q l:=by
   intro l hl
   simp only [C,List.mem_append] at hl
   rcases hl with hl | hl
   · exact hA l hl
   · exact P.z11 (hP.mem_iff.mpr (by simp [hl]))
 have zc:((x ::u) ++ (y ::v) ++ C.flatten).Perm P.chains.flatten:=by
   apply List.Perm.trans _ hP.flatten.symm
   simp only [C,List.flatten_append,prefixChains_flatten,List.flatten_cons,hc]
   apply Multiset.coe_eq_coe.mp
   simp only [← Multiset.coe_add]
   ac_rfl
 obtain ⟨R,hR,_⟩:=P.z17c C u v I zc
   (fun l hl => (hC l hl).nonempty) (fun l hl => (hC l hl).edges)
   (fun l hl => (hC l hl).positive) (fun l hl => (hC l hl).ends)
   he.left_of_append he.right_of_append hp.left_of_append hp.right_of_append
   hum hve hI hIp hIn hId
 exact ⟨R,hR⟩
theorem y0.zeb {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) {x y:V}
   (hx:x∈P.reps) (hy:y∈P.reps) (hxy:x≠y) (I:List V)
   (hI:(x ::I ++ [y]).IsChain G.Adj)
   (hIp:(x ::I ++ [y]).IsChain (fun a b => a∉Q∨b∉Q))
   (hIn:I.Nodup) (hId:I.Disjoint P.chains.flatten) :
   ∃ R:y0 G Q,R.z2=P.z2+I.length:=by
 classical
 obtain ⟨rc,hrc,hxc⟩:=List.mem_flatten.mp hx
 obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hrc
 obtain ⟨rd,hrd,hyd⟩:=List.mem_flatten.mp hy
 obtain ⟨d,hd,rfl⟩:=List.mem_map.mp hrd
 have hnc:=(List.nodup_flatten.mp P.nodup).1 c hc
 by_cases hcd:c=d
 · subst d
   have hp:=List.perm_cons_erase hc
   rcases z123 ((z39 Q true c).subset hxc)
     ((z39 Q true c).subset hyd) hxy with hh | hh
   · obtain ⟨A,u,v,he⟩:=hh
     obtain ⟨hA,hu⟩:=z71 hnc hxc hyd A u v he
     exact P.z11f (P.chains.erase c) hp A u v I he hA hu hI hIp hIn hId
   · obtain ⟨A,u,v,he⟩:=hh
     obtain ⟨hA,hu⟩:=z71 hnc hyd hxc A u v he
     have hi:(y ::I.reverse ++ [x]).IsChain G.Adj:=by
       simpa only [List.reverse_cons,List.reverse_append,List.reverse_singleton,
         List.singleton_append,List.append_assoc,List.reverse_nil,List.nil_append,List.cons_append] using
         List.isChain_reverse.mpr (hI.imp (fun _ _ h => h.symm))
     have hip:(y ::I.reverse ++ [x]).IsChain (fun a b => a∉Q∨b∉Q):=by
       simpa only [List.reverse_cons,List.reverse_append,List.reverse_singleton,
         List.singleton_append,List.append_assoc,List.reverse_nil,List.nil_append,List.cons_append] using
         List.isChain_reverse.mpr (hIp.imp (fun _ _ h => h.symm))
     obtain ⟨R,hR⟩:=P.z11f (P.chains.erase c) hp A u v I.reverse he hA hu hi hip
       (List.nodup_reverse.mpr hIn) (by simpa using hId)
     exact ⟨R,by simpa using hR⟩
 · have hp₁:=List.perm_cons_erase hc
   have hd' :d∈P.chains.erase c:=(List.mem_erase_of_ne (Ne.symm hcd)).mpr hd
   have hp₂:=List.perm_cons_erase hd'
   have hp:=hp₁.trans (hp₂.cons c)
   obtain ⟨A,u,hec,zf5⟩:=(z59 Q true c x).mp hxc
   obtain ⟨B,v,hed,zf6⟩:=(z59 Q true d y).mp hyd
   exact P.z142 ((P.chains.erase c).erase d) hp
     A u B v I hec hed zf5 zf6 hI hIp hIn hId
abbrev y0.vertices {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q):Set V:={v | v∈P.chains.flatten}
end CycleClique
namespace CycleClique
open scoped SimpleGraph
noncomputable local instance (p:Prop):Decidable p:=Classical.propDecidable p
inductive y8 {V:Type*} (Q:Set V):List V → List ℕ → Prop
 | singleton (x:V) (hx:x∈Q):y8 Q [x] []
 | step (x y:V) (I B:List V) (A:List ℕ) (hx:x∈Q)
     (hI:I ≠ []) (hout:∀ z∈I,z∉Q)
     (tail:y8 Q (y ::B) A) :
     y8 Q (x ::(I ++ y ::B)) (I.length ::A)
theorem z175 {V:Type*} (Q:Set V) (c:List V)
   (h:∃ x∈c,x∈Q) :
   ∃ I x B,c=I ++ x ::B∧(∀ z∈I,z∉Q)∧x∈Q:=by
 classical
 induction c with
 | nil => simp at h
 | cons x c ih =>
   by_cases hx:x∈Q
   · exact ⟨[],x,c,rfl,by simp,hx⟩
   · have ht:∃ y∈c,y∈Q:=by
       obtain ⟨y,hy,hyQ⟩:=h
       rcases List.mem_cons.mp hy with rfl | hy
       · exact (hx hyQ).elim
       · exact ⟨y,hy,hyQ⟩
     obtain ⟨I,y,B,he,hout,hy⟩:=ih ht
     refine ⟨x ::I,y,B,?_,?_,hy⟩
     · simp only [he,List.cons_append]
     · intro z hz
       rcases List.mem_cons.mp hz with rfl | hz
       · exact hx
       · exact hout z hz
theorem y8.z12d {V:Type*} {Q:Set V} {G:SimpleGraph V}
   (c:List V) (hc:ClosedChain G Q c):∃ A,y8 Q c A:=by
 cases c with
 | nil => exact (hc.nonempty rfl).elim
 | cons x l =>
   have hx:x∈Q:=hc.ends.1 x (by simp)
   by_cases hl:l = []
   · subst l
     exact ⟨[],.singleton x hx⟩
   · have hh:∃ y∈l,y∈Q:=by
       refine ⟨l.getLast hl,List.getLast_mem hl,?_⟩
       apply hc.ends.2
       simpa only [List.getLast?_cons_of_ne_nil hl,List.getLast?_eq_some_getLast hl] using
         (Option.mem_def.mpr rfl:l.getLast hl∈some (l.getLast hl))
     obtain ⟨I,y,B,he,hout,hy⟩:=z175 Q l hh
     have hec:x ::l=(x ::I) ++ y ::B:=by simp [he]
     have hI:I ≠ []:=by
       intro hi
       subst I
       have hp:=hc.positive
       rw [he] at hp
       exact hp.rel.elim (fun h => h hx) (fun h => h hy)
     have ht:ClosedChain G Q (y ::B):={
       nonempty:=by simp
       edges:=by rw [hec] at hc; exact hc.edges.right_of_append
       positive:=by rw [hec] at hc; exact hc.positive.right_of_append
       ends:=⟨by simpa using hy,by
         simpa only [hec,List.getLast?_append_of_ne_nil _ (by simp:y ::B ≠ [])] using hc.ends.2⟩ }
     obtain ⟨A,hA⟩:=y8.z12d (y ::B) ht
     exact ⟨I.length ::A,by simpa only [he] using y8.step x y I B A hx hI hout hA⟩
termination_by c.length
theorem y8.head_mem {V:Type*} {Q:Set V} {c:List V} {A:List ℕ}
   (h:y8 Q c A):∀ x∈c.head?,x∈Q:=by
 cases h <;> simp_all
theorem y8.count {V:Type*} {Q:Set V} {c:List V} {A:List ℕ}
   (h:y8 Q c A) :
   c.countP (fun v => decide (v∈Q))=A.length+1 ∧
   c.length=A.sum+A.length+1 ∧ ∀ a∈A,1≤ a:=by
 classical
 induction h with
 | singleton x hx => simp [hx]
 | step x y I B A hx hI hout zc5 ih =>
   have hcI:I.countP (fun v => decide (v∈Q))=0:=by
     apply List.countP_eq_zero.mpr
     simpa using hout
   have hi: 1≤ I.length:=List.length_pos_iff.mpr hI
   rcases ih with ⟨hc,hl,hp⟩
   constructor
   · simp only [List.countP_cons,List.countP_append,hcI,hx,decide_true,
       ite_true,List.length_cons] at hc ⊢
     omega
   constructor
   · simp only [List.length_cons,List.length_append,List.sum_cons] at hl ⊢
     omega
   · intro a ha
     rcases List.mem_cons.mp ha with rfl | ha
     · exact hi
     · exact hp a ha
theorem y8.z188 {V:Type*} {Q:Set V} {c:List V} {A:List ℕ}
   (h:y8 Q c A) {a:ℕ} (ha:a∈A) :
   ∃ U x I y B AL AR,c=U ++ x ::(I ++ y ::B)∧I.length=a ∧
     (∀ z∈I,z∉Q)∧y8 Q (U ++ [x]) AL ∧
     y8 Q (y ::B) AR∧A=AL ++ a ::AR:=by
 induction h with
 | singleton x hx => simp at ha
 | step p q J C A hp hJ hJout zc5 ih =>
   rcases List.mem_cons.mp ha with rfl | ha
   · exact ⟨[],p,J,q,C,[],A,rfl,rfl,hJout,.singleton p hp,zc5,rfl⟩
   · obtain ⟨U,x,I,y,B,AL,AR,he,hi,hout,z11d,hright,hA⟩:=ih ha
     have hne:U ++ [x] ≠ []:=by simp
     obtain ⟨q',D,hD⟩:=List.exists_cons_of_ne_nil hne
     have hq:q' = q:=by
       have hh:=congrArg List.head? he
       have hh' :=congrArg List.head? hD
       cases U <;> simp_all
     subst q'
     have z1ed:y8 Q ((p ::(J ++ U)) ++ [x]) (J.length ::AL):=by
       have hc:=y8.step p q J D AL hp hJ hJout (hD ▸ z11d)
       simpa only [← hD,List.append_assoc,List.cons_append] using hc
     refine ⟨p ::(J ++ U),x,I,y,B,J.length ::AL,AR,?_,hi,hout,
       z1ed,hright,?_⟩
     · rw [he]
       simp only [List.append_assoc,List.cons_append]
     · simp only [hA,List.cons_append]
def z3 {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q) (A:List ℕ):Prop :=
 ∃ blocks:List (List ℕ),List.Forall₂ (y8 Q) P.chains blocks∧blocks.flatten.Perm A
theorem y0.z12e {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q):∃ A,z3 P A:=by
 have hh:∀ c∈P.chains,∃ A,y8 Q c A :=
   fun c hc => y8.z12d c (P.z11 hc)
 have hex:∃ D,List.Forall₂ (y8 Q) P.chains D:=by
   generalize P.chains=C at hh ⊢
   revert hh
   induction C with
   | nil => intro _; exact ⟨[],.nil⟩
   | cons c C ih =>
     intro hh
     obtain ⟨A,hA⟩:=hh c (by simp)
     obtain ⟨D,hD⟩:=ih (fun d hd => hh d (by simp [hd]))
     exact ⟨A ::D,.cons hA hD⟩
 obtain ⟨D,hD⟩:=hex
 exact ⟨D.flatten,⟨D,hD,List.Perm.refl _⟩⟩
theorem z3.count {V:Type*} [Fintype V] {G:SimpleGraph V} {Q:Set V}
   {P:y0 G Q} {A:List ℕ} (h:z3 P A) :
   A.sum=P.z2∧A.length=P.z4 ∧ ∀ a∈A,1≤ a:=by
 obtain ⟨D,hD,zc⟩:=h
 have hh:P.chains.flatten.countP (fun x => decide (x∈Q))=D.flatten.length+P.chains.length ∧
     P.chains.flatten.length=D.flatten.sum+D.flatten.length+P.chains.length ∧
     ∀ a∈D.flatten,1≤ a:=by
   clear zc
   generalize P.chains=C at hD ⊢
   induction hD with
   | nil => simp
   | @cons c B C D hc hC ih =>
     obtain ⟨hq,hl,hp⟩:=hc.count
     rcases ih with ⟨hq',hl',hp'⟩
     constructor
     · simp only [List.flatten_cons,List.countP_append,List.length_append,List.length_cons]
       omega
     constructor
     · simp only [List.flatten_cons,List.length_append,List.sum_append,List.length_cons]
       omega
     · intro a ha
       simp only [List.flatten_cons,List.mem_append] at ha
       exact ha.elim (hp a) (hp' a)
 rw [P.z93,P.z66,zc.length_eq,zc.sum_eq] at hh
 dsimp [y0.z4]
 exact ⟨by omega,by omega,fun a ha => hh.2.2 a (zc.mem_iff.mpr ha)⟩
theorem z3.perm {V:Type*} {G:SimpleGraph V} {Q:Set V}
   {P:y0 G Q} {A B:List ℕ} (h:z3 P A) (hp:A.Perm B) :
   z3 P B:=by
 obtain ⟨D,hD,hDA⟩:=h
 exact ⟨D,hD,hDA.trans hp⟩
theorem y8.ends {V:Type*} {Q:Set V} {c:List V} {A:List ℕ}
   (h:y8 Q c A) :
   (∀ x∈c.head?,x∈Q) ∧ ∀ y∈c.getLast?,y∈Q:=by
 induction h with
 | singleton x hx => simpa using And.intro hx hx
 | step x y I B A hx hI hout zc5 ih =>
   constructor
   · simpa using hx
   · simpa only [show x ::(I ++ y ::B)=(x ::I) ++ y ::B from by simp,
       List.getLast?_append_of_ne_nil _ (by simp:y ::B ≠ [])] using ih.2
theorem zc4 {α β:Type*} {R: α → β → Prop}
   {C:List α} {D:List β} (h:List.Forall₂ R C D) {b: β} (hb:b∈D) :
   ∃ C₁ c C₂ D₁ D₂,C=C₁ ++ c ::C₂∧D=D₁ ++ b ::D₂ ∧
     List.Forall₂ R C₁ D₁∧R c b∧List.Forall₂ R C₂ D₂:=by
 induction h with
 | nil => simp at hb
 | @cons c d C D hcd hCD ih =>
   rcases List.mem_cons.mp hb with rfl | hb
   · exact ⟨[],c,C,[],D,rfl,rfl,.nil,hcd,hCD⟩
   · obtain ⟨C₁,c',C₂,D₁,D₂,hC,hD,hpre,hcc,hpost⟩:=ih hb
     exact ⟨c ::C₁,c',C₂,d ::D₁,D₂,
       by simp [hC],by simp [hD],.cons hcd hpre,hcc,hpost⟩
theorem z3.z1e0 {V:Type*} [Fintype V] {G:SimpleGraph V} {Q:Set V}
   {P:y0 G Q} {A:List ℕ} (h:z3 P A) {a:ℕ} (ha:a∈A) :
   ∃ R:y0 G Q,∃ B:List ℕ,z3 R B∧(a ::B).Perm A:=by
 obtain ⟨D,hD,hDA⟩:=h
 obtain ⟨C,hCD,haC⟩:=List.mem_flatten.mp (hDA.mem_iff.mpr ha)
 obtain ⟨CP,c,CS,DP,DS,hP,hD',hpre,hcC,hpost⟩:=zc4 hD hCD
 obtain ⟨U,x,I,y,B,AL,AR,he,hIa,hIo,z11d,hright,hC⟩:=hcC.z188 haC
 let J:=U ++ [x]
 let K:=y ::B
 let newC:=CP ++ J ::K ::CS
 let newD:=DP ++ AL ::AR ::DS
 have hec:c=J ++ I ++ K:=by simpa only [J,K,List.append_assoc,List.singleton_append,List.cons_append,List.nil_append] using he
 have zc:(I ++ newC.flatten).Perm P.chains.flatten:=by
   rw [hP]
   dsimp [newC]
   simp only [List.flatten_append,List.flatten_cons,hec]
   apply Multiset.coe_eq_coe.mp
   simp only [← Multiset.coe_add]
   ac_rfl
 have hnd:=List.nodup_append.mp (zc.nodup_iff.mpr P.nodup)
 have hcc:=P.z11 (by rw [hP]; simp:c∈P.chains)
 have hj:ClosedChain G Q J:={
   nonempty:=by simp [J]
   edges:=by rw [hec] at hcc; exact hcc.edges.left_of_append.left_of_append
   positive:=by rw [hec] at hcc; exact hcc.positive.left_of_append.left_of_append
   ends:=z11d.ends }
 have hk:ClosedChain G Q K:={
   nonempty:=by simp [K]
   edges:=by rw [hec] at hcc; exact hcc.edges.right_of_append
   positive:=by rw [hec] at hcc; exact hcc.positive.right_of_append
   ends:=hright.ends }
 have z19c:∀ l∈newC,ClosedChain G Q l:=by
   intro l hl
   simp only [newC,List.mem_append,List.mem_cons] at hl
   rcases hl with hl | rfl | rfl | hl
   · exact P.z11 (by rw [hP]; simp [hl])
   · exact hj
   · exact hk
   · exact P.z11 (by rw [hP]; simp [hl])
 let R:y0 G Q:={
   chains:=newC
   nonempty:=fun l hl => (z19c l hl).nonempty
   nodup:=hnd.2.1
   edges:=fun l hl => (z19c l hl).edges
   positive:=fun l hl => (z19c l hl).positive
   ends:=fun l hl => (z19c l hl).ends
   cover:=by
     intro v hv
     have hv' :=zc.mem_iff.mpr (P.cover v hv)
     rcases List.mem_append.mp hv' with hvi | hvn
     · exact (hIo v hvi hv).elim
     · exact hvn }
 have hd:List.Forall₂ (y8 Q) R.chains newD :=
   List.rel_append hpre (.cons z11d (.cons hright hpost))
 refine ⟨R,newD.flatten,⟨newD,hd,List.Perm.refl _⟩,?_⟩
 apply List.Perm.trans _ hDA
 rw [hD',hC]
 dsimp [newD]
 simp only [List.flatten_append,List.flatten_cons]
 apply Multiset.coe_eq_coe.mp
 simp only [← Multiset.coe_add,← Multiset.cons_coe,Multiset.cons_add,Multiset.add_cons]
 ac_rfl
theorem z3.erase {V:Type*} [Fintype V] {G:SimpleGraph V} {Q:Set V}
   {P:y0 G Q} {A:List ℕ} (h:z3 P A) {a:ℕ} (ha:a∈A) :
   ∃ R:y0 G Q,z3 R (A.erase a):=by
 obtain ⟨R,B,hB,hp⟩:=h.z1e0 ha
 have he:(a ::B).Perm (a ::A.erase a):=hp.trans (List.perm_cons_erase ha)
 exact ⟨R,hB.perm (List.Perm.cons_inv he)⟩
theorem z3.z1ac {V:Type*} [Fintype V] {G:SimpleGraph V} {Q:Set V}
   (C B:List ℕ) {P:y0 G Q} (h:z3 P (C ++ B)) :
   ∃ R:y0 G Q,z3 R B:=by
 induction C generalizing P with
 | nil => exact ⟨P,h⟩
 | cons a C ih =>
   obtain ⟨R,hR⟩:=h.erase (by simp:a∈(a ::C) ++ B)
   have hr:z3 R (C ++ B):=by simpa using hR
   exact ih hr
theorem z3.z212 {V:Type*} [Fintype V] {G:SimpleGraph V} {Q:Set V}
   {P:y0 G Q} {A B:List ℕ} (h:z3 P A) (hB:B.Sublist A) :
   ∃ R:y0 G Q,z3 R B:=by
 obtain ⟨C,hAC⟩:=hB.exists_perm_append
 exact (h.perm (hAC.trans (List.perm_append_comm))).z1ac C B
theorem y0.z38 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) :
   P.ze≤2*P.z4:=by
 classical
 have hb:∀ c∈P.chains,
     2≤ c.countP (fun v => decide (v∈Q))+if c.length=1 then 1 else 0:=by
   intro c hc
   obtain ⟨A,hA⟩:=y8.z12d c (P.z11 hc)
   have hh:=hA.count
   by_cases he:c.length=1
   · simp only [he,ite_true]
     omega
   · simp only [he,ite_false]
     have hn:A.length≠0:=by
       intro hn
       have heA:A = []:=List.length_eq_zero_iff.mp hn
       simp only [heA,List.sum_nil,List.length_nil] at hh
       omega
     omega
 have hs:=List.sum_le_sum hb
 have he:(P.chains.map (fun c =>
     c.countP (fun v => decide (v∈Q))+if c.length=1 then 1 else 0)).sum =
     Q.ncard+P.z13.length:=by
   rw [List.sum_map_add,← List.countP_flatten,P.z93]
   congr 1
   simp only [y0.z13,← List.countP_eq_length_filter]
   induction P.chains with
   | nil => simp
   | cons c C ih =>
     simp only [List.map_cons,List.sum_cons,List.countP_cons,decide_eq_true_eq]
     omega
 rw [he] at hs
 have hh:=P.z4c
 have hss:=P.z50
 have z11d:(P.chains.map (fun _ => 2)).sum=2*P.chains.length:=by simp [Nat.mul_comm]
 rw [z11d] at hs
 dsimp [y0.ze,y0.z4]
 omega
theorem y8.z158 {V:Type*} {Q:Set V} {c I:List V} {A:List ℕ}
   (h:y8 Q c A) (hI:I ≠ []) (hout:∀ z∈I,z∉Q)
   (hin:I <:+:c):∃ a∈A,I.length≤ a:=by
 induction h with
 | singleton x hx =>
   obtain ⟨z,hz⟩:=List.exists_mem_of_ne_nil I hI
   have he:z=x:=by simpa using hin.sublist.subset hz
   subst z
   exact (hout x hz hx).elim
 | step x y J B A hx hJ hJo zc5 ih =>
   have hy:y∈Q:=zc5.head_mem y (by simp)
   have hin' :I <:+:(x ::J) ++ y ::B:=by simpa only [List.cons_append] using hin
   rcases List.infix_append_iff_ne_nil.mp hin' with z11d | hright | ⟨I₁,I₂,hn₁,hn₂,he,hs,hp⟩
   · have hh:I.Sublist J:=by
       rcases List.sublist_cons_iff.mp z11d.sublist with h | ⟨D,hd,_⟩
       · exact h
       · exact (hout x (by simp [hd]) hx).elim
     exact ⟨J.length,by simp,hh.length_le⟩
   · obtain ⟨a,ha,hIa⟩:=ih hright
     exact ⟨a,by simp [ha],hIa⟩
   · obtain ⟨z,Z,hz⟩:=List.exists_cons_of_ne_nil hn₂
     obtain ⟨T,hT⟩:=hp
     rw [hz] at hT
     have hzy:z=y:=(List.cons.inj hT).1
     subst z
     have hyI:y∈I:=by rw [he,hz]; simp
     exact (hout y hyI hy).elim
theorem z3.z158 {V:Type*} {G:SimpleGraph V} {Q:Set V}
   {P:y0 G Q} {A:List ℕ} (h:z3 P A)
   {c I:List V} (hc:c∈P.chains) (hI:I ≠ []) (hout:∀ z∈I,z∉Q)
   (hin:I <:+:c):∃ a∈A,I.length≤ a:=by
 obtain ⟨D,hD,hDA⟩:=h
 obtain ⟨DP,B,DS,CP,CS,hDs,_,_,hBc,_⟩:=zc4 hD.flip hc
 obtain ⟨a,ha,hIa⟩:=y8.z158 hBc hI hout hin
 refine ⟨a,hDA.mem_iff.mp ?_,hIa⟩
 exact List.mem_flatten.mpr ⟨B,by rw [hDs]; simp,ha⟩
theorem z154 (A:List ℕ) (h:ℕ) (hh:h≤ A.sum) :
   ∃ B:List ℕ,B.Sublist A∧h≤ B.sum ∧ ∀ a∈B,(B.erase a).sum < h:=by
 let E:ℕ → Prop:=fun n => ∃ B:List ℕ,B.Sublist A∧h≤ B.sum∧B.length=n
 have hex:∃ n,E n:=⟨A.length,A,.refl _,hh,rfl⟩
 obtain ⟨B,hB,hb,hn⟩:=Nat.find_spec hex
 refine ⟨B,hB,hb,?_⟩
 intro a ha
 by_contra! he
 have hm:=Nat.find_min' hex (show E (B.erase a).length from
   ⟨B.erase a,(List.erase_sublist).trans hB,he,rfl⟩)
 have hl:=List.length_erase_add_one ha
 omega
theorem za0 {A:List ℕ} {a:ℕ} (ha:a∈A) :
   A.sum=a+(A.erase a).sum:=by
 simpa using (List.perm_cons_erase ha).sum_eq
theorem z58 (A:List ℕ) (b:ℕ) (h:∀ a∈A,b≤ a) :
   b*A.length≤ A.sum:=by
 have hh:=List.sum_le_sum h
 simpa [Nat.mul_comm] using hh
theorem z15e {t L r j s:ℕ} (ht: 9≤ t) (hL:L≤ t+1)
   (hwr:t+1≤2*r+j) (hj1: 1≤ j) (hj5:j≤5)
   (hs:s+1=r) (hb:(j+2)*s≤ L):False:=by
 interval_cases j <;> nlinarith
theorem y0.z122 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} {k d:ℕ} (P R:y0 G Q)
   (hopt:P.Optimal k) (hQ:G.IsClique Q)
   (hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G)
   (ht: 9≤ Q.ncard) (htk:Q.ncard≤ k) (hkt:k≤2*Q.ncard+1)
   (hd: 1≤ d) (hd6:d≤6) (hR:R.z2=P.z2+d)
   (he:R.z4≤ P.z4+1) {A:List ℕ}
   (hA:z3 R A) {b:ℕ} (hb:b∈A) (hbd:d≤ b) :
   P.z2=k - Q.ncard∧R.z4=P.z4+1 ∧
     2≤ d ∧ ∀ a∈A,d≤ a:=by
 let h:=k+1 - Q.ncard
 have hL:P.z2 < h:=hopt.1
 have hh:h≤ R.z2:=by
   by_contra! hh
   have hx:=hopt.2.1 R hh
   omega
 obtain ⟨hsum,hlen,hpos⟩:=hA.count
 obtain ⟨B,hBA,hBh,hBmin⟩:=z154 A h (by omega)
 obtain ⟨T,hT⟩:=hA.z212 hBA
 obtain ⟨hTS,hTL,hTP⟩:=hT.count
 have z229:B.sum≤ A.sum:=hBA.sum_le_sum (fun _ _ => Nat.zero_le _)
 have z215:B.length≤ A.length:=hBA.length_le
 have hEr:(A.erase b).sum≤ P.z2:=by
   have hs:=za0 hb
   omega
 have hbB:b∈B:=by
   by_contra hbB
   have hs:=(hBA.erase b).sum_le_sum (fun _ _ => Nat.zero_le _)
   rw [List.erase_of_not_mem hbB] at hs
   omega
 have z1f2:(B.erase b).sum≤ P.z2 :=
   le_trans ((hBA.erase b).sum_le_sum (fun _ _ => Nat.zero_le _)) hEr
 let j:=B.sum - h
 have hj:B.sum=h+j:=by dsimp [j]; omega
 have hj5:j≤5:=by omega
 have hwi:=T.z38
 have hwt:T.ze≤ Q.ncard:=Nat.sub_le _ _
 have hw:k+1 - T.ze < T.z2:=by
   by_contra! hw
   exact T.z81 (by omega) hQ hcycle htk (by omega) hw
 have hj1: 1≤ j:=by dsimp [h] at hj; omega
 have hwr:Q.ncard+1≤2*B.length+j:=by dsimp [h] at hj; omega
 have z131:∃ a∈B,a=j+1:=by
   by_contra! hn
   have hge:∀ a∈B,j+2≤ a:=by
     intro a ha
     have hm:=hBmin a ha
     have hs:=za0 ha
     have hne:=hn a ha
     omega
   have hbg:=z58 (B.erase b) (j+2)
     (fun a ha => hge a (List.mem_of_mem_erase ha))
   have hbl:=List.length_erase_add_one hbB
   have hLt:P.z2≤ Q.ncard+1:=by dsimp [h] at hL; omega
   exact z15e ht hLt hwr hj1 hj5 hbl (le_trans hbg z1f2)
 obtain ⟨a,ha,har⟩:=z131
 obtain ⟨U,hU⟩:=hT.erase ha
 have hcU:=hU.count
 have hSU:=za0 ha
 have hLU:=List.length_erase_add_one ha
 have z213:U.z2=h - 1:=by omega
 have hUL:U.z2≤ P.z2:=hopt.2.1 U (by dsimp [h] at *; omega)
 have hLeq:P.z2=k - Q.ncard:=by dsimp [h] at *; omega
 have z1f7:U.z2=P.z2:=by dsimp [h] at *; omega
 have hUE:=hopt.2.2 U z1f7
 have heq:R.z4=P.z4+1:=by omega
 have hBEq:B=A:=hBA.eq_of_length (by omega)
 subst B
 have hjd:j+1=d:=by dsimp [h] at hj; omega
 refine ⟨hLeq,heq,by omega,?_⟩
 intro a ha
 have hm:=hBmin a ha
 have hs:=za0 ha
 omega
theorem y0.z105 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q)
   (C:List (List V)) {x y:V} (u v I:List V)
   (zc:((x ::u) ++ (y ::v) ++ C.flatten).Perm P.chains.flatten)
   (hne:∀ c∈C,c ≠ []) (hc:∀ c∈C,c.IsChain G.Adj)
   (hcp:∀ c∈C,c.IsChain (fun a b => a∉Q∨b∉Q))
   (hce:∀ c∈C,(∀ a∈c.head?,a∈Q)∧(∀ a∈c.getLast?,a∈Q))
   (hu:(x ::u).IsChain G.Adj) (hv:(y ::v).IsChain G.Adj)
   (hup:(x ::u).IsChain (fun a b => a∉Q∨b∉Q))
   (hvp:(y ::v).IsChain (fun a b => a∉Q∨b∉Q))
   (hue:∀ a∈(x ::u).getLast?,a∈Q)
   (hve:∀ a∈(y ::v).getLast?,a∈Q)
   (hI:(x ::I ++ [y]).IsChain G.Adj)
   (hIp:(x ::I ++ [y]).IsChain (fun a b => a∉Q∨b∉Q))
   (hIn:I.Nodup) (hId:I.Disjoint P.chains.flatten) :
   ∃ R:y0 G Q,R.z2=P.z2+I.length∧R.chains=((x ::u).reverse ++ I ++ (y ::v)) ::C:=by
 classical
 let J:=(x ::u).reverse ++ I ++ (y ::v)
 have hJn:J ≠ []:=by simp [J]
 have hnd:(J ++ C.flatten).Nodup:=by
   apply nodup_bridge (zc.nodup_iff.mpr P.nodup) hIn
   apply List.disjoint_left.mpr
   intro a ha hb
   exact List.disjoint_left.mp hId ha (zc.subset hb)
 have hJe:(∀ a∈J.head?,a∈Q)∧(∀ a∈J.getLast?,a∈Q):=by
   constructor
   · intro a ha
     apply hue a
     simpa only [J,List.append_assoc,List.head?_append_of_ne_nil _ (by simp:(x ::u).reverse ≠ []),
       List.head?_reverse] using ha
   · intro a ha
     apply hve a
     simpa only [J,← List.append_assoc,
       List.getLast?_append_of_ne_nil _ (by simp:y ::v ≠ [])] using ha
 let R:y0 G Q :=
   { chains:=J ::C
     nonempty:=by intro c hc; simp only [List.mem_cons] at hc; rcases hc with rfl | hc; exact hJn; exact hne c hc
     nodup:=hnd
     edges:=by
       intro c hc'
       simp only [List.mem_cons] at hc'
       rcases hc' with rfl | hc'
       · exact isChain_bridge (fun _ _ h => h.symm) hu hv hI
       · exact hc c hc'
     positive:=by
       intro c hc'
       simp only [List.mem_cons] at hc'
       rcases hc' with rfl | hc'
       · exact isChain_bridge (fun _ _ h => h.symm) hup hvp hIp
       · exact hcp c hc'
     ends:=by intro c hc'; simp only [List.mem_cons] at hc'; rcases hc' with rfl | hc'; exact hJe; exact hce c hc'
     cover:=by
       intro a ha
       have hh:=zc.mem_iff.mpr (P.cover a ha)
       simp only [J,List.flatten_cons,List.mem_append,List.mem_reverse] at hh ⊢
       tauto }
 refine ⟨R,?_,rfl⟩
 have hh:=zc.length_eq
 rw [P.z66] at hh
 change ((x ::u).reverse ++ I ++ (y ::v) ++ C.flatten).length - Q.ncard =
   P.z2+I.length
 simp only [List.length_append,List.length_reverse] at hh ⊢
 omega
end CycleClique
namespace CycleClique
open scoped SimpleGraph
noncomputable local instance (p:Prop):Decidable p:=Classical.propDecidable p
theorem y0.z13a {V:Type*} [Fintype V] {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q):P.vertices.ncard=Q.ncard+P.z2:=by
 classical
 have he:P.vertices=(↑P.chains.flatten.toFinset:Set V):=by ext; simp
 rw [he,Set.ncard_coe_finset,List.toFinset_card_of_nodup P.nodup,P.z66]
theorem z5.z139 {V:Type*} {G:SimpleGraph V} {X:Set V} {x y:V} {d:ℕ}
   (h:z5 G X x y d) :
   ∃ I:List V,I.length=d∧(x ::I ++ [y]).IsChain G.Adj ∧
     I.Nodup ∧ ∀ a∈I,a∉X:=by
 obtain ⟨hx,hy,hxy,p,hp,hlen,hs⟩:=h
 cases p with
 | nil => simp at hlen
 | cons hadj q =>
   let I:=q.support.dropLast
   have he:q.support=I ++ [y]:=by
     simpa only [I,q.getLast_support] using (List.dropLast_concat_getLast q.support_ne_nil).symm
   have hn:(x ::I ++ [y]).Nodup:=by
     simpa only [SimpleGraph.Walk.support_cons,he,List.cons_append] using hp.support_nodup
   have zc5:=(List.nodup_cons.mp hn).2
   have hi:=(List.nodup_append.mp zc5).1
   have hxI:x∉I:=fun hx => (List.nodup_cons.mp hn).1 (by simp [hx])
   have hyI:y∉I:=fun hy => (List.nodup_append.mp zc5).2.2 y hy y (by simp) rfl
   refine ⟨I,?_,?_,hi,?_⟩
   · have hl:=q.length_support
     rw [he,List.length_append,List.length_singleton] at hl
     simp only [SimpleGraph.Walk.length_cons] at hlen
     omega
   · simpa only [SimpleGraph.Walk.support_cons,he,List.cons_append] using
       (SimpleGraph.Walk.cons hadj q).isChain_adj_support
   · intro a ha haX
     rcases hs a (by simp only [SimpleGraph.Walk.support_cons,he,List.mem_cons,
       List.mem_append]; exact Or.inr (Or.inl ha)) haX with rfl | rfl
     · exact hxI ha
     · exact hyI ha
theorem z56 {V:Type*} {Q:Set V} {x y:V} {I:List V}
   (hne:I ≠ []) (hout:∀ a∈I,a∉Q) :
   (x ::I ++ [y]).IsChain (fun a b => a∉Q∨b∉Q):=by
 induction I generalizing x with
 | nil => contradiction
 | cons a I ih =>
   have ha:=hout a (by simp)
   apply List.isChain_cons.mpr
   constructor
   · intro b hb
     have he:a=b:=by simpa using hb
     exact Or.inr (he ▸ ha)
   · cases I with
     | nil => simpa using (Or.inl ha:a∉Q∨y∉Q)
     | cons b I =>
       exact ih (by simp) (fun c hc => hout c (by simp [hc]))
theorem y0.z127 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} {k:ℕ} (P:y0 G Q)
   (hopt:P.Optimal k) (hk: 3≤ k) (hQ:G.IsClique Q)
   (hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G) (ht:Q.ncard≤ k)
   {x y:V} (hx:x∈P.reps) (hy:y∈P.reps) :
   ¬ z5 G P.vertices x y 1:=by
 intro hp
 obtain ⟨I,hIl,hI,hIn,hIo⟩:=hp.z139
 have hip:(x ::I ++ [y]).IsChain (fun a b => a∉Q∨b∉Q) :=
   z56 (by intro h; simp [h] at hIl)
     (fun a ha hQ => hIo a ha (P.cover a hQ))
 have hid:I.Disjoint P.chains.flatten:=List.disjoint_left.mpr hIo
 obtain ⟨R,hR⟩:=P.zeb hx hy hp.2.2.1 I hI hip hIn hid
 have hr:R.ze≤ Q.ncard:=Nat.sub_le _ _
 have hh:=hopt.1
 apply P.z181 hopt hk hQ hcycle ht R (by omega) (by omega)
 omega
theorem z6c {V:Type*} {R:V → V → Prop} {A I B:List V} {x y:V}
   (hc:(A ++ x ::y ::B).IsChain R) (hI:(x ::I ++ [y]).IsChain R) :
   (A ++ x ::I ++ y ::B).IsChain R:=by
 have hp:(A ++ [x]).IsChain R:=by
   apply List.IsChain.left_of_append (l₂:=y ::B)
   simpa only [List.append_assoc,List.singleton_append] using hc
 have hs:(y ::B).IsChain R:=by
   apply List.IsChain.right_of_append (l₁:=A ++ [x])
   simpa only [List.append_assoc,List.singleton_append] using hc
 have h₁:(A ++ [x] ++ (I ++ [y])).IsChain R:=hp.append_overlap hI (by simp)
 have h₂:(A ++ [x] ++ I ++ [y] ++ B).IsChain R :=
   (show (A ++ [x] ++ I ++ [y]).IsChain R by simpa only [List.append_assoc] using h₁).append_overlap
     hs (by simp)
 simpa only [List.append_assoc,List.singleton_append] using h₂
theorem y0.z1ad {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q)
   {c:List V} (hc:c∈P.chains) {x y:V} (A I B:List V)
   (he:c=A ++ x ::y ::B)
   (hI:(x ::I ++ [y]).IsChain G.Adj)
   (hIp:(x ::I ++ [y]).IsChain (fun a b => a∉Q∨b∉Q))
   (hIn:I.Nodup) (hId:I.Disjoint P.chains.flatten) :
   ∃ R:y0 G Q,R.z2=P.z2+I.length∧R.z4=P.z4:=by
 classical
 let D:=P.chains.erase c
 let J:=A ++ x ::I ++ y ::B
 have hp:P.chains.Perm (c ::D):=List.perm_cons_erase hc
 have hj:(J ++ D.flatten).Perm (I ++ P.chains.flatten):=by
   apply List.Perm.trans _ (hp.flatten.symm.append_left I)
   simp only [List.flatten_cons,he,J]
   apply Multiset.coe_eq_coe.mp
   simp only [← Multiset.coe_add,← Multiset.cons_coe,Multiset.cons_add,Multiset.add_cons]
   ac_nf
   exact Multiset.cons_swap ..
 have hnd:(J ++ D.flatten).Nodup:=hj.nodup_iff.mpr
   (List.nodup_append.mpr ⟨hIn,P.nodup,fun a ha b hb hab =>
     List.disjoint_left.mp hId ha (hab ▸ hb)⟩)
 have hje:(∀ a∈J.head?,a∈Q) ∧ ∀ a∈J.getLast?,a∈Q:=by
   have hh:=P.ends c hc
   constructor
   · simpa only [he,J,List.append_assoc,List.cons_append,List.head?_append,List.head?_cons] using hh.1
   · have hec:c=(A ++ [x]) ++ y ::B:=by simp only [he,List.append_assoc,List.singleton_append]
     have hej:J=(A ++ [x] ++ I) ++ y ::B:=by
       simp only [J,List.append_assoc,List.cons_append,List.nil_append]
     simpa only [hec,hej,List.getLast?_append_of_ne_nil _ (by simp:y ::B ≠ [])] using hh.2
 let R:y0 G Q :=
   { chains:=J ::D
     nonempty:=by
       intro d hd
       simp only [List.mem_cons] at hd
       rcases hd with rfl | hd
       · simp [J]
       · exact P.nonempty d (List.mem_of_mem_erase hd)
     nodup:=hnd
     edges:=by
       intro d hd
       simp only [List.mem_cons] at hd
       rcases hd with rfl | hd
       · exact z6c (he ▸ P.edges c hc) hI
       · exact P.edges d (List.mem_of_mem_erase hd)
     positive:=by
       intro d hd
       simp only [List.mem_cons] at hd
       rcases hd with rfl | hd
       · exact z6c (he ▸ P.positive c hc) hIp
       · exact P.positive d (List.mem_of_mem_erase hd)
     ends:=by
       intro d hd
       simp only [List.mem_cons] at hd
       rcases hd with rfl | hd
       · exact hje
       · exact P.ends d (List.mem_of_mem_erase hd)
     cover:=by
       intro a ha
       exact hj.mem_iff.mpr (List.mem_append_right _ (P.cover a ha)) }
 refine ⟨R,?_,?_⟩
 · have hh:=hj.length_eq
   simp only [List.length_append,P.z66] at hh
   change (J ++ D.flatten).length - Q.ncard=P.z2+I.length
   rw [List.length_append]
   omega
 · have hh:=hp.length_eq
   change Q.ncard - (J ::D).length=Q.ncard - P.chains.length
   simp only [List.length_cons] at hh ⊢
   omega
theorem y0.z155 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} {k:ℕ} (P:y0 G Q)
   (hopt:P.Optimal k) (hk: 3≤ k) (hQ:G.IsClique Q)
   (hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G) (ht:Q.ncard≤ k)
   {c:List V} (hc:c∈P.chains) {x y:V} (A B:List V)
   (he:c=A ++ x ::y ::B) :
   ¬ z5 G P.vertices x y 1:=by
 intro hp
 obtain ⟨I,hIl,hI,hIn,hIo⟩:=hp.z139
 have hip:(x ::I ++ [y]).IsChain (fun a b => a∉Q∨b∉Q) :=
   z56 (by intro h; simp [h] at hIl)
     (fun a ha hQ => hIo a ha (P.cover a hQ))
 obtain ⟨R,hR,_⟩:=P.z1ad hc A I B he hI hip hIn (List.disjoint_left.mpr hIo)
 have hr:R.ze≤ Q.ncard:=Nat.sub_le _ _
 have hh:=hopt.1
 apply P.z181 hopt hk hQ hcycle ht R (by omega) (by omega)
 omega
abbrev y0.zd {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q):Set V:={v | v∈P.reps}
theorem y0.z34 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) :
   P.zd.ncard=Q.ncard:=by
 classical
 have he:P.zd=(↑P.reps.toFinset:Set V):=by ext; simp
 rw [he,Set.ncard_coe_finset,List.toFinset_card_of_nodup (P.nodup.sublist P.z9e),
   P.z129]
end CycleClique
namespace CycleClique
open scoped SimpleGraph
noncomputable local instance (p:Prop):Decidable p:=Classical.propDecidable p
theorem y8.join {V:Type*} {Q:Set V} {c I:List V} {A B:List ℕ}
   {y:V} {v:List V} (hc:y8 Q c A) (hd:y8 Q (y ::v) B)
   (hI:I ≠ []) (ho:∀ z∈I,z∉Q) :
   y8 Q (c ++ I ++ (y ::v)) (A ++ I.length ::B):=by
 induction hc with
 | singleton x hx => simpa using y8.step x y I v B hx hI ho hd
 | step x z J D C hx hJ hJo zc5 ih =>
   simpa only [List.cons_append,List.append_assoc] using
     y8.step x z J (D ++ I ++ y ::v) (C ++ I.length ::B) hx hJ hJo ih
theorem y8.reverse {V:Type*} {Q:Set V} {c:List V} {A:List ℕ}
   (hc:y8 Q c A):y8 Q c.reverse A.reverse:=by
 induction hc with
 | singleton x hx => simpa using y8.singleton x hx
 | step x y I B A hx hI ho zc5 ih =>
   have hh:=ih.join (y8.singleton x hx)
     (List.reverse_ne_nil_iff.mpr hI) (by simpa using ho)
   simpa only [List.reverse_cons,List.reverse_append,List.length_reverse,
     List.append_assoc,List.append_nil] using hh
theorem z3.z1a9 {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q) {C:List (List V)} {D:List (List ℕ)}
   (hp:P.chains.Perm C) (hD:List.Forall₂ (y8 Q) C D) :
   z3 P D.flatten:=by
 obtain ⟨E,hE,hED⟩:=List.perm_comp_forall₂ hp hD
 exact ⟨E,hE,hED.flatten⟩
theorem y8.z18b {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (C:List (List V)) (h:∀ c∈C,ClosedChain G Q c) :
   ∃ D:List (List ℕ),List.Forall₂ (y8 Q) C D:=by
 induction C with
 | nil => exact ⟨[],.nil⟩
 | cons c C ih =>
   obtain ⟨A,hA⟩:=y8.z12d c (h c (by simp))
   obtain ⟨D,hD⟩:=ih (fun d hd => h d (by simp [hd]))
   exact ⟨A ::D,.cons hA hD⟩
theorem z3.z1ae {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P R:y0 G Q) {x y:V} {u v I:List V} {D:List (List V)}
   (hP:P.chains.Perm ((x ::u) ::(y ::v) ::D))
   (hR:R.chains=((x ::u).reverse ++ I ++ (y ::v)) ::D)
   (hI:I ≠ []) (ho:∀ z∈I,z∉Q) :
   ∃ A:List ℕ,z3 P A∧z3 R (I.length ::A):=by
 have hC:∀ c∈((x ::u) ::(y ::v) ::D),ClosedChain G Q c :=
   fun c hc => P.z11 (hP.mem_iff.mpr hc)
 obtain ⟨A,hA⟩:=y8.z12d (x ::u) (hC _ (by simp))
 obtain ⟨B,hB⟩:=y8.z12d (y ::v) (hC _ (by simp))
 obtain ⟨E,hE⟩:=y8.z18b D (fun c hc => hC _ (by simp [hc]))
 have hPp:=z3.z1a9 P hP (.cons hA (.cons hB hE))
 refine ⟨A ++ B ++ E.flatten,by simpa only [List.flatten_cons,List.append_assoc] using hPp,?_⟩
 have hr:List.Forall₂ (y8 Q) R.chains ((A.reverse ++ I.length ::B) ::E):=by
   rw [hR]
   exact .cons (hA.reverse.join hB hI ho) hE
 refine ⟨(A.reverse ++ I.length ::B) ::E,hr,?_⟩
 simp only [List.flatten_cons]
 apply List.Perm.trans ((List.reverse_perm A).append_right (I.length ::B) |>.append_right E.flatten)
 apply Multiset.coe_eq_coe.mp
 simp only [← Multiset.coe_add,← Multiset.cons_coe,Multiset.cons_add,Multiset.add_cons]
theorem y0.ze7 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q)
   {c d:List V} (D:List (List V)) (hP:P.chains.Perm (c ::d ::D))
   {x y:V} (A u B v I:List V) (hc:c=A ++ x ::u) (hd:d=B ++ y ::v)
   (zf5:z2c Q true A) (zf6:z2c Q true B)
   (hI:(x ::I ++ [y]).IsChain G.Adj)
   (hIp:(x ::I ++ [y]).IsChain (fun a b => a∉Q∨b∉Q))
   (hIn:I.Nodup) (hId:I.Disjoint P.chains.flatten) :
   ∃ R:y0 G Q,R.z2=P.z2+I.length ∧
     R.chains=((x ::u).reverse ++ I ++ (y ::v)) ::
     (z23 A ++ z23 B ++ D):=by
 have hcc:=P.z11 (hP.mem_iff.mpr (by simp:c∈c ::d ::D))
 have hdd:=P.z11 (hP.mem_iff.mpr (by simp:d∈c ::d ::D))
 obtain ⟨hA,hu⟩:=hcc.cut hc zf5
 obtain ⟨hB,hv⟩:=hdd.cut hd zf6
 let C:=z23 A ++ z23 B ++ D
 have hC:∀ l∈C,ClosedChain G Q l:=by
   intro l hl
   simp only [C,List.mem_append] at hl
   rcases hl with (hl | hl) | hl
   · exact hA l hl
   · exact hB l hl
   · exact P.z11 (hP.mem_iff.mpr (by simp [hl]))
 have zc:((x ::u) ++ (y ::v) ++ C.flatten).Perm P.chains.flatten:=by
   apply List.Perm.trans _ hP.flatten.symm
   simp only [C,List.flatten_append,prefixChains_flatten,List.flatten_cons,hc,hd]
   simpa only [List.append_assoc] using zee A (x ::u) B (y ::v) D.flatten
 obtain ⟨R,hR,hRC⟩:=P.z105 C u v I zc
   (fun l hl => (hC l hl).nonempty) (fun l hl => (hC l hl).edges)
   (fun l hl => (hC l hl).positive) (fun l hl => (hC l hl).ends)
   hu.edges hv.edges hu.positive hv.positive hu.end_mem hv.end_mem hI hIp hIn hId
 exact ⟨R,hR,hRC⟩
theorem y0.z133 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q)
   {c:List V} (D:List (List V)) (hP:P.chains.Perm (c ::D))
   {x y:V} (A u v I:List V) (hc:c=A ++ (x ::u) ++ y ::v)
   (hcut:z2c Q true A) (hum:∀ a∈(x ::u).getLast?,a∈Q)
   (hI:(x ::I ++ [y]).IsChain G.Adj)
   (hIp:(x ::I ++ [y]).IsChain (fun a b => a∉Q∨b∉Q))
   (hIn:I.Nodup) (hId:I.Disjoint P.chains.flatten) :
   ∃ R:y0 G Q,R.z2=P.z2+I.length ∧
     R.chains=((x ::u).reverse ++ I ++ (y ::v)) ::(z23 A ++ D):=by
 have hcc:=P.z11 (hP.mem_iff.mpr (by simp:c∈c ::D))
 obtain ⟨hA,hu⟩:=hcc.cut (by simpa only [List.append_assoc,List.cons_append] using hc) hcut
 have he:((x ::u) ++ y ::v).IsChain G.Adj:=by simpa only [List.cons_append] using hu.edges
 have hp:((x ::u) ++ y ::v).IsChain (fun a b => a∉Q∨b∉Q):=by
   simpa only [List.cons_append] using hu.positive
 have hve:∀ a∈(y ::v).getLast?,a∈Q:=by
   simpa only [hc,List.getLast?_append_of_ne_nil _ (by simp:y ::v ≠ [])] using hcc.ends.2
 let C:=z23 A ++ D
 have hC:∀ l∈C,ClosedChain G Q l:=by
   intro l hl
   simp only [C,List.mem_append] at hl
   rcases hl with hl | hl
   · exact hA l hl
   · exact P.z11 (hP.mem_iff.mpr (by simp [hl]))
 have zc:((x ::u) ++ (y ::v) ++ C.flatten).Perm P.chains.flatten:=by
   apply List.Perm.trans _ hP.flatten.symm
   simp only [C,List.flatten_append,prefixChains_flatten,List.flatten_cons,hc]
   apply Multiset.coe_eq_coe.mp
   simp only [← Multiset.coe_add]
   ac_rfl
 obtain ⟨R,hR,hRC⟩:=P.z105 C u v I zc
   (fun l hl => (hC l hl).nonempty) (fun l hl => (hC l hl).edges)
   (fun l hl => (hC l hl).positive) (fun l hl => (hC l hl).ends)
   he.left_of_append he.right_of_append hp.left_of_append hp.right_of_append
   hum hve hI hIp hIn hId
 exact ⟨R,hR,hRC⟩
theorem y0.z8c {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} {k:ℕ} (P R:y0 G Q)
   (hopt:P.Optimal k) (hQ:G.IsClique Q)
   (hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G)
   (ht: 9≤ Q.ncard) (htk:Q.ncard≤ k) (hkt:k≤2*Q.ncard+1)
   {I c:List V} (hI:I ≠ []) (hI6:I.length≤6) (hout:∀ z∈I,z∉Q)
   (hR:R.z2=P.z2+I.length) (he:R.z4≤ P.z4+1)
   (hc:c∈R.chains) (hin:I <:+:c) :
   P.z2=k - Q.ncard∧R.z4=P.z4+1∧2≤ I.length:=by
 obtain ⟨A,hA⟩:=R.z12e
 obtain ⟨b,hb,hbd⟩:=hA.z158 hc hI hout hin
 have hd: 1≤ I.length:=List.length_pos_iff.mpr hI
 obtain ⟨hL,heq,hd2,_⟩:=P.z122 R hopt hQ hcycle ht htk hkt hd hI6 hR he hA hb hbd
 exact ⟨hL,heq,hd2⟩
theorem zab {V:Type*} (A:List V) :
   (z23 A).length=if A = [] then 0 else 1:=by
 by_cases h:A = [] <;> simp [z23,h]
theorem y0.z137 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} {k:ℕ} (P:y0 G Q)
   (hopt:P.Optimal k) (hQ:G.IsClique Q)
   (hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G)
   (ht: 9≤ Q.ncard) (htk:Q.ncard≤ k) (hkt:k≤2*Q.ncard+1)
   {c d:List V} (D:List (List V)) (hP:P.chains.Perm (c ::d ::D))
   {x y:V} (A u B v I:List V) (hc:c=A ++ x ::u) (hd:d=B ++ y ::v)
   (zf5:z2c Q true A) (zf6:z2c Q true B)
   (hI:(x ::I ++ [y]).IsChain G.Adj)
   (hIp:(x ::I ++ [y]).IsChain (fun a b => a∉Q∨b∉Q))
   (hIn:I.Nodup) (hId:I.Disjoint P.chains.flatten)
   (hI0:I ≠ []) (hI6:I.length≤6) (hout:∀ z∈I,z∉Q) :
   A = []∧B = []∧P.z2=k - Q.ncard∧2≤ I.length ∧
     (D.filter (fun c => c.length=1)).length+2≤ I.length ∧
     ∃ F:List ℕ,z3 P F ∧ ∀ a∈F,I.length≤ a:=by
 classical
 obtain ⟨R,hR,hRC⟩:=P.ze7 D hP A u B v I hc hd zf5 zf6
   hI hIp hIn hId
 have hPC:=hP.length_eq
 simp only [List.length_cons] at hPC
 have hRCn:=congrArg List.length hRC
 simp only [List.length_cons,List.length_append,zab] at hRCn
 have hPle:=P.z4c
 have hRle:=R.z4c
 have he:R.z4≤ P.z4+1:=by dsimp [y0.z4]; omega
 have hr:=P.z8c R hopt hQ hcycle ht htk hkt hI0 hI6 hout hR he
   (by rw [hRC]; simp) (show I <:+:(x ::u).reverse ++ I ++ y ::v from
     ⟨(x ::u).reverse,y ::v,rfl⟩)
 have hAB:A = []∧B = []:=by
   have heq:=hr.2.1
   dsimp [y0.z4] at heq
   split_ifs at hRCn <;> first | (constructor <;> assumption) | omega
 obtain ⟨rfl,rfl⟩:=hAB
 simp only [List.nil_append] at hc hd
 subst c d
 simp only [z23,ite_true,List.nil_append] at hRC
 obtain ⟨F,hF,hRF⟩:=z3.z1ae P R hP hRC hI0 hout
 obtain ⟨hL,heq,hd2,hge⟩:=P.z122 R hopt hQ hcycle ht htk hkt
   (List.length_pos_iff.mpr hI0) hI6 hR he hRF (by simp) (le_refl _)
 have z1f5:(((x ::u).reverse ++ I ++ y ::v)).length≠1:=by simp; omega
 have z228:R.z13.length=(D.filter (fun c => c.length=1)).length:=by
   simp only [y0.z13,hRC,List.filter_cons,z1f5,decide_false,Bool.false_eq_true,ite_false]
 have hi:k+1 - R.ze < R.z2:=by
   by_contra! hi
   exact R.z81 (by omega) hQ hcycle htk (by omega) hi
 have hsle:=R.z50
 have z98:(D.filter (fun c => c.length=1)).length+2≤ I.length:=by
   dsimp [y0.ze] at hi
   omega
 exact ⟨rfl,rfl,hL,hd2,z98,F,hF,fun a ha => hge a (by simp [ha])⟩
theorem y0.zc8 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} {k:ℕ} (P:y0 G Q)
   (hopt:P.Optimal k) (hQ:G.IsClique Q)
   (hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G)
   (ht: 9≤ Q.ncard) (htk:Q.ncard≤ k) (hkt:k≤2*Q.ncard+1)
   {c:List V} (D:List (List V)) (hP:P.chains.Perm (c ::D))
   {x y:V} (A u v I:List V) (hc:c=A ++ (x ::u) ++ y ::v)
   (hcut:z2c Q true A) (hum:∀ a∈(x ::u).getLast?,a∈Q)
   (hI:(x ::I ++ [y]).IsChain G.Adj)
   (hIp:(x ::I ++ [y]).IsChain (fun a b => a∉Q∨b∉Q))
   (hIn:I.Nodup) (hId:I.Disjoint P.chains.flatten)
   (hI0:I ≠ []) (hI6:I.length≤6) (hout:∀ z∈I,z∉Q):False:=by
 obtain ⟨R,hR,hRC⟩:=P.z133 D hP A u v I hc hcut hum hI hIp hIn hId
 have hPC:=hP.length_eq
 simp only [List.length_cons] at hPC
 have hRCn:=congrArg List.length hRC
 simp only [List.length_cons,List.length_append,zab] at hRCn
 have hPle:=P.z4c
 have he:R.z4≤ P.z4:=by dsimp [y0.z4]; omega
 have hr:=P.z8c R hopt hQ hcycle ht htk hkt hI0 hI6 hout hR (by omega)
   (by rw [hRC]; simp) (show I <:+:(x ::u).reverse ++ I ++ y ::v from
     ⟨(x ::u).reverse,y ::v,rfl⟩)
 omega
theorem y0.z17b {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q)
   {c:List V} (hc:c∈P.chains) {x y:V} (A I B:List V)
   (he:c=A ++ x ::y ::B)
   (hI:(x ::I ++ [y]).IsChain G.Adj)
   (hIp:(x ::I ++ [y]).IsChain (fun a b => a∉Q∨b∉Q))
   (hIn:I.Nodup) (hId:I.Disjoint P.chains.flatten) :
   ∃ R:y0 G Q,R.z2=P.z2+I.length∧R.z4=P.z4 ∧ ∃ c∈R.chains,I <:+:c:=by
 classical
 let D:=P.chains.erase c
 let J:=A ++ x ::I ++ y ::B
 have hp:P.chains.Perm (c ::D):=List.perm_cons_erase hc
 have hj:(J ++ D.flatten).Perm (I ++ P.chains.flatten):=by
   apply List.Perm.trans _ (hp.flatten.symm.append_left I)
   simp only [List.flatten_cons,he,J]
   apply Multiset.coe_eq_coe.mp
   simp only [← Multiset.coe_add,← Multiset.cons_coe,Multiset.cons_add,Multiset.add_cons]
   ac_nf
   exact Multiset.cons_swap ..
 have hnd:(J ++ D.flatten).Nodup:=hj.nodup_iff.mpr
   (List.nodup_append.mpr ⟨hIn,P.nodup,fun a ha b hb hab =>
     List.disjoint_left.mp hId ha (hab ▸ hb)⟩)
 have hje:(∀ a∈J.head?,a∈Q) ∧ ∀ a∈J.getLast?,a∈Q:=by
   have hh:=P.ends c hc
   constructor
   · simpa only [he,J,List.append_assoc,List.cons_append,List.head?_append,List.head?_cons] using hh.1
   · have hec:c=(A ++ [x]) ++ y ::B:=by simp only [he,List.append_assoc,List.singleton_append]
     have hej:J=(A ++ [x] ++ I) ++ y ::B:=by
       simp only [J,List.append_assoc,List.cons_append,List.nil_append]
     simpa only [hec,hej,List.getLast?_append_of_ne_nil _ (by simp:y ::B ≠ [])] using hh.2
 let R:y0 G Q :=
   { chains:=J ::D
     nonempty:=by
       intro d hd
       simp only [List.mem_cons] at hd
       rcases hd with rfl | hd
       · simp [J]
       · exact P.nonempty d (List.mem_of_mem_erase hd)
     nodup:=hnd
     edges:=by
       intro d hd
       simp only [List.mem_cons] at hd
       rcases hd with rfl | hd
       · exact z6c (he ▸ P.edges c hc) hI
       · exact P.edges d (List.mem_of_mem_erase hd)
     positive:=by
       intro d hd
       simp only [List.mem_cons] at hd
       rcases hd with rfl | hd
       · exact z6c (he ▸ P.positive c hc) hIp
       · exact P.positive d (List.mem_of_mem_erase hd)
     ends:=by
       intro d hd
       simp only [List.mem_cons] at hd
       rcases hd with rfl | hd
       · exact hje
       · exact P.ends d (List.mem_of_mem_erase hd)
     cover:=by
       intro a ha
       exact hj.mem_iff.mpr (List.mem_append_right _ (P.cover a ha)) }
 refine ⟨R,?_,?_,J,by simp [R],(A ++ [x]),y ::B,?_⟩
 · have hh:=hj.length_eq
   simp only [List.length_append,P.z66] at hh
   change (J ++ D.flatten).length - Q.ncard=P.z2+I.length
   rw [List.length_append]
   omega
 · have hh:=hp.length_eq
   change Q.ncard - (J ::D).length=Q.ncard - P.chains.length
   simp only [List.length_cons] at hh ⊢
   omega
 · simp only [J,List.append_assoc,List.cons_append,List.nil_append]
theorem y0.z138 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} {k:ℕ} (P:y0 G Q)
   (hopt:P.Optimal k) (hQ:G.IsClique Q)
   (hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G)
   (ht: 9≤ Q.ncard) (htk:Q.ncard≤ k) (hkt:k≤2*Q.ncard+1)
   {x y:V} (hx:x∈P.reps) (hy:y∈P.reps) (hxy:x≠y) (I:List V)
   (hI:(x ::I ++ [y]).IsChain G.Adj)
   (hIp:(x ::I ++ [y]).IsChain (fun a b => a∉Q∨b∉Q))
   (hIn:I.Nodup) (hId:I.Disjoint P.chains.flatten)
   (hI0:I ≠ []) (hI6:I.length≤6) (hout:∀ z∈I,z∉Q) :
   ∃ u v:List V,∃ D:List (List V),∃ F:List ℕ,
     P.chains.Perm ((x ::u) ::(y ::v) ::D) ∧
     P.z2=k - Q.ncard∧2≤ I.length ∧
     (D.filter (fun c => c.length=1)).length+2≤ I.length ∧
     z3 P F ∧ ∀ a∈F,I.length≤ a:=by
 classical
 obtain ⟨rc,hrc,hxc⟩:=List.mem_flatten.mp hx
 obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hrc
 obtain ⟨rd,hrd,hyd⟩:=List.mem_flatten.mp hy
 obtain ⟨d,hd,rfl⟩:=List.mem_map.mp hrd
 have hnc:=(List.nodup_flatten.mp P.nodup).1 c hc
 by_cases hcd:c=d
 · subst d
   have hp:=List.perm_cons_erase hc
   rcases z123 ((z39 Q true c).subset hxc)
     ((z39 Q true c).subset hyd) hxy with hh | hh
   · obtain ⟨A,u,v,he⟩:=hh
     obtain ⟨hA,hu⟩:=z71 hnc hxc hyd A u v he
     exact (P.zc8 hopt hQ hcycle ht htk hkt
       (P.chains.erase c) hp A u v I he hA hu hI hIp hIn hId hI0 hI6 hout).elim
   · obtain ⟨A,u,v,he⟩:=hh
     obtain ⟨hA,hu⟩:=z71 hnc hyd hxc A u v he
     have hi:(y ::I.reverse ++ [x]).IsChain G.Adj:=by
       simpa only [List.reverse_cons,List.reverse_append,List.reverse_singleton,
         List.singleton_append,List.append_assoc,List.reverse_nil,List.nil_append,List.cons_append] using
         List.isChain_reverse.mpr (hI.imp (fun _ _ h => h.symm))
     have hip:(y ::I.reverse ++ [x]).IsChain (fun a b => a∉Q∨b∉Q):=by
       simpa only [List.reverse_cons,List.reverse_append,List.reverse_singleton,
         List.singleton_append,List.append_assoc,List.reverse_nil,List.nil_append,List.cons_append] using
         List.isChain_reverse.mpr (hIp.imp (fun _ _ h => h.symm))
     exact (P.zc8 hopt hQ hcycle ht htk hkt
       (P.chains.erase c) hp A u v I.reverse he hA hu hi hip (by simpa using hIn)
       (by simpa using hId) (by simpa using hI0) (by simpa using hI6) (by simpa using hout)).elim
 · have hp₁:=List.perm_cons_erase hc
   have hd' :d∈P.chains.erase c:=(List.mem_erase_of_ne (Ne.symm hcd)).mpr hd
   have hp₂:=List.perm_cons_erase hd'
   have hp:=hp₁.trans (hp₂.cons c)
   obtain ⟨A,u,hec,zf5⟩:=(z59 Q true c x).mp hxc
   obtain ⟨B,v,hed,zf6⟩:=(z59 Q true d y).mp hyd
   obtain ⟨rfl,rfl,hL,hd2,hS,F,hF,hFa⟩ :=
     P.z137 hopt hQ hcycle ht htk hkt ((P.chains.erase c).erase d)
       hp A u B v I hec hed zf5 zf6 hI hIp hIn hId hI0 hI6 hout
   simp only [List.nil_append] at hec hed
   exact ⟨u,v,(P.chains.erase c).erase d,F,by simpa [← hec,← hed] using hp,
     hL,hd2,hS,hF,hFa⟩
theorem y0.z135 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} {k:ℕ} (P:y0 G Q)
   (hopt:P.Optimal k) (hQ:G.IsClique Q)
   (hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G)
   (ht: 9≤ Q.ncard) (htk:Q.ncard≤ k) (hkt:k≤2*Q.ncard+1)
   {c:List V} (hc:c∈P.chains) {x y:V} (A I B:List V)
   (he:c=A ++ x ::y ::B)
   (hI:(x ::I ++ [y]).IsChain G.Adj)
   (hIp:(x ::I ++ [y]).IsChain (fun a b => a∉Q∨b∉Q))
   (hIn:I.Nodup) (hId:I.Disjoint P.chains.flatten)
   (hI0:I ≠ []) (hI6:I.length≤6) (hout:∀ z∈I,z∉Q):False:=by
 obtain ⟨R,hR,heR,cR,hcR,hiR⟩:=P.z17b hc A I B he hI hIp hIn hId
 have hh:=P.z8c R hopt hQ hcycle ht htk hkt hI0 hI6 hout hR (by omega) hcR hiR
 omega
noncomputable def z1d {V:Type*} (b:Bool) (c:List V):List V :=
 if b then c.reverse else c
@[simp] theorem flipChain_length {V:Type*} (b:Bool) (c:List V) :
   (z1d b c).length=c.length:=by cases b <;> simp [z1d]
theorem z18a {V:Type*} (b:Bool) (c:List V) :
   (z1d b c).Perm c:=by cases b <;> simp [z1d]
theorem za2 {V:Type*} (f:List V → Bool) (C:List (List V)) :
   (C.map (fun c => z1d (f c) c)).flatten.Perm C.flatten:=by
 induction C with
 | nil => simp
 | cons c C ih => exact (z18a (f c) c).append ih
noncomputable def y0.orient {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q) (f:List V → Bool):y0 G Q:=by
 classical
 let C:=P.chains.map (fun c => z1d (f c) c)
 have hp:C.flatten.Perm P.chains.flatten:=za2 f P.chains
 refine {
   chains:=C
   nonempty:= ?_
   nodup:=hp.nodup_iff.mpr P.nodup
   edges:= ?_
   positive:= ?_
   ends:= ?_
   cover:=fun v hv => hp.mem_iff.mpr (P.cover v hv) }
 · intro c hc
   obtain ⟨d,hd,rfl⟩:=List.mem_map.mp hc
   have hn:=P.nonempty d hd
   cases hf:f d <;> simpa [z1d,hf] using hn
 · intro c hc
   obtain ⟨d,hd,rfl⟩:=List.mem_map.mp hc
   have he:=P.edges d hd
   cases hf:f d
   · simpa [z1d,hf] using he
   · simpa [z1d,hf] using List.isChain_reverse.mpr (he.imp (fun _ _ h => h.symm))
 · intro c hc
   obtain ⟨d,hd,rfl⟩:=List.mem_map.mp hc
   have he:=P.positive d hd
   cases hf:f d
   · simpa [z1d,hf] using he
   · simpa [z1d,hf] using List.isChain_reverse.mpr (he.imp (fun _ _ h => h.symm))
 · intro c hc
   obtain ⟨d,hd,rfl⟩:=List.mem_map.mp hc
   have he:=P.ends d hd
   cases hf:f d
   · simpa [z1d,hf] using he
   · simpa [z1d,hf] using And.intro he.2 he.1
@[simp] theorem y0.orient_chains {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q) (f:List V → Bool) :
   (P.orient f).chains=P.chains.map (fun c => z1d (f c) c):=rfl
theorem y0.z164 {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q) (f:List V → Bool) :
   (P.orient f).chains.flatten.Perm P.chains.flatten:=za2 f P.chains
@[simp] theorem y0.orient_amount {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) (f:List V → Bool) :
   (P.orient f).z2=P.z2:=by
 change (P.orient f).chains.flatten.length - Q.ncard=P.chains.flatten.length - Q.ncard
 rw [(P.z164 f).length_eq]
@[simp] theorem y0.orient_edgeCount {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) (f:List V → Bool) :
   (P.orient f).z4=P.z4:=by simp [y0.z4]
@[simp] theorem y0.orient_singletons_length {V:Type*}
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) (f:List V → Bool) :
   (P.orient f).z13.length=P.z13.length:=by
 classical
 simp only [y0.z13,orient_chains,List.filter_map,List.length_map]
 congr 2
 funext c
 simp only [Function.comp_apply,flipChain_length]
@[simp] theorem y0.orient_incident {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) (f:List V → Bool) :
   (P.orient f).ze=P.ze:=by simp [y0.ze]
@[simp] theorem y0.orient_optimal {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) (f:List V → Bool) {k:ℕ} :
   (P.orient f).Optimal k↔P.Optimal k:=by simp [y0.Optimal]
end CycleClique
namespace CycleClique
open scoped SimpleGraph
noncomputable local instance (p:Prop):Decidable p:=Classical.propDecidable p
theorem za1 {V:Type*} (G:SimpleGraph V) {A B:Set V}
   (h:A⊆B):z0 G A⊆z0 G B:=by
 rintro v (hv | ⟨u,hu,huv⟩)
 · exact Or.inl (h hv)
 · exact Or.inr ⟨u,h hu,huv⟩
theorem z24 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {X Z A:Set V} {x:V} {r:ℕ}
   (hA:A⊆z1 G X x r) (hZ:Z⊆X)
   (z54:∀ u∈A,∀ z∈Z,¬ G.Adj u z) :
   (z0 G A).ncard+Z.ncard ≤
     X.ncard+(z1 G X x (r+1)).ncard:=by
 have hdis:Disjoint (z0 G A) Z:=by
   apply Set.disjoint_left.mpr
   rintro z (hz | ⟨u,hu,huz⟩) hzZ
   · exact z1c G X x r (hA hz) (hZ hzZ)
   · exact z54 u hu z hzZ huz
 have hs:z0 G A⊆z1 G X x (r+1)∪(X \ Z):=by
   intro z hz
   rcases zbf G X x r (za1 G hA hz) with hb | hx
   · exact Or.inl hb
   · exact Or.inr ⟨hx,fun hzZ => Set.disjoint_left.mp hdis hz hzZ⟩
 have hc:=Set.ncard_le_ncard hs
 have hu:=Set.ncard_union_le (z1 G X x (r+1)) (X \ Z)
 have hd:=Set.ncard_sdiff_add_ncard_of_subset hZ
 omega
theorem z143 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {X:Set V} {x:V} {k:ℕ}
   (hx:x∈X) (hX:X.ncard≤ k)
   (hdeg:k+1≤(z0 G {x}).ncard) :
   (z1 G X x 0).Nonempty:=by
 by_contra hn
 have hs:z0 G {x}⊆X:=by
   rintro v (hv | ⟨u,hu,huv⟩)
   · simpa using (Set.mem_singleton_iff.mp hv ▸ hx)
   · have he:u=x:=hu
     subst u
     by_contra hvX
     exact hn ⟨v,huv,hvX⟩
 have hh:=Set.ncard_le_ncard hs
 omega
theorem z69 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {X Z:Set V} {x:V} {k:ℕ}
   (hx:x∈X) (hX:X.ncard≤ k) (hZ:Z⊆X)
   (hdeg:∀ u,k+1≤(z0 G {u}).ncard)
   (z54:∀ u∈z1 G X x 0,∀ z∈Z,¬ G.Adj u z) :
   k+1+Z.ncard≤ X.ncard+(z1 G X x 1).ncard:=by
 obtain ⟨u,hu⟩:=z143 hx hX (hdeg x)
 have hc:=z24 (Set.singleton_subset_iff.mpr hu) hZ
   (by intro v hv; have he:v=u:=hv; subst v; exact z54 u hu)
 have hd:=hdeg u
 change (z0 G {u}).ncard+Z.ncard≤ X.ncard+(z1 G X x 1).ncard at hc
 omega
theorem zd9 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {X R:Set V} {x:V} {k t:ℕ}
   (hR:R⊆X) (hx:x∈R) (z177:R.ncard=t) (hX:X.ncard≤ k)
   (z20:G.cliqueNum≤ t)
   (hdeg:∀ u,k+1≤(z0 G {u}).ncard)
   (z54:∀ u∈z1 G X x 1,∀ z∈R \ {x},¬ G.Adj u z) :
   2≤ independence G (z1 G X x 2):=by
 have ht: 1≤ t:=by
   have hp:=(Set.ncard_pos).mpr (show R.Nonempty from ⟨x,hx⟩)
   omega
 have hZ:R \ {x}⊆X:=Set.sdiff_subset.trans hR
 have hcZ:(R \ {x}).ncard=t - 1:=by
   rw [Set.ncard_sdiff_singleton_of_mem hx,z177]
 have hb:=z69 (hR hx) hX hZ hdeg
   (fun u hu => z54 u (z55 G X x 0 hu))
 rw [hcZ] at hb
 by_contra hn
 have htwo:G.IsClique (z1 G X x 2):=zf (by omega)
 have hc2:=(za htwo).trans z20
 have hsub:=z55 G X x 1
 have hc12:(z1 G X x 1).ncard≤(z1 G X x 2).ncard:=Set.ncard_le_ncard hsub
 have hc1:(z1 G X x 1).ncard=t:=by omega
 have hadj:∀ z∈z1 G X x 1,G.Adj x z:=by
   intro z hz
   by_contra hneg
   have z1ee:∀ u∈({z}:Set V),∀ w∈R,¬ G.Adj u w:=by
     intro u hu w hw huw
     have he:u=z:=hu
     subst u
     by_cases hwx:w=x
     · subst w
       exact hneg huw.symm
     · exact z54 z hz w ⟨hw,hwx⟩ huw
   have hh:=z24 (Set.singleton_subset_iff.mpr hz) hR z1ee
   rw [z177] at hh
   change (z0 G {z}).ncard+t≤ X.ncard+(z1 G X x 2).ncard at hh
   have hd:=hdeg z
   omega
 have hxB:x∉z1 G X x 1:=fun hh =>
   z1c G X x 1 hh (hR hx)
 have hbig:G.IsClique (insert x (z1 G X x 1)):=by
   intro u hu v hv huv
   rcases hu with rfl | hu <;> rcases hv with rfl | hv
   · exact (huv rfl).elim
   · exact hadj v hv
   · exact (hadj u hu).symm
   · exact htwo (hsub hu) (hsub hv) huv
 have hc:=(za hbig).trans z20
 rw [Set.ncard_insert_of_notMem hxB,hc1] at hc
 omega
theorem zc9 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {X R:Set V} {x:V} {k t:ℕ}
   (hk: 5≤ k) (ht: 1≤ t) (htk:t < k)
   (hR:R⊆X) (hx:x∈R) (z177:R.ncard=t) (hX:X.ncard≤ k)
   (z20:G.cliqueNum≤ t) (hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G)
   (hexp:∀ I:Set V,G.IsIndepSet I → I.Nonempty → 
     k*I.ncard+1≤(z0 G I).ncard)
   (z54:∀ u∈z1 G X x 1,∀ z∈R \ {x},¬ G.Adj u z)
   (z1cf:¬ G.IsClique (z1 G X x 1)) :
   3≤ independence G (z1 G X x 2):=by
 have ha: 2≤ independence G (z1 G X x 1):=by
   by_contra hn
   exact z1cf (zf (by omega))
 obtain ⟨I,hIs,hI,hIc⟩:=z6 G (z1 G X x 1)
 have hIn:I.Nonempty:=(Set.ncard_pos).mp (by omega)
 have he:=hexp I hI hIn
 have hb:=z24 hIs (Set.sdiff_subset.trans hR)
   (fun u hu => z54 u (hIs hu))
 have hcZ:(R \ {x}).ncard=t - 1:=by
   rw [Set.ncard_sdiff_singleton_of_mem hx,z177]
 rw [hcZ] at hb
 change (z0 G I).ncard+(t - 1)≤ X.ncard+(z1 G X x 2).ncard at hb
 have hm: 2*k≤ k*I.ncard:=by
   have hh:=Nat.mul_le_mul_left k (show 2≤ I.ncard by omega)
   simpa only [Nat.mul_comm k 2] using hh
 apply z121 hk ht hcycle z20
 omega
theorem z62 {V:Type*} {G:SimpleGraph V}
   {X R:Set V} {x:V} {r:ℕ} (hR:R⊆X) (hx:x∈R)
   (hno:∀ y∈R,∀ d,1≤ d → d≤ r+1 → ¬ z5 G X x y d) :
   ∀ u∈z1 G X x r,∀ z∈R \ {x},¬ G.Adj u z:=by
 intro u hu z hz
 exact z3f (hR hx) (hR hz.1) (Ne.symm hz.2)
   (fun d hd hd' => hno z hz.1 d hd hd') u hu
end CycleClique
namespace CycleClique
open scoped SimpleGraph
noncomputable local instance (p:Prop):Decidable p:=Classical.propDecidable p
theorem y0.z19f {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q):P.chains.Nodup:=by
 apply (List.nodup_flatten.mp P.nodup).2.imp_of_mem
 intro a b ha hb hd heq
 subst b
 obtain ⟨x,hx⟩:=List.exists_mem_of_ne_nil a (P.nonempty a ha)
 exact List.disjoint_left.mp hd hx hx
theorem y0.zd7 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) :
   P.ze=P.z4+P.z46.length:=by
 have hh:=P.partition.length_eq
 simp only [List.length_append] at hh
 have hle:=P.z4c
 dsimp [y0.ze,y0.z4]
 omega
theorem y0.z9d {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q) {c:List V} (hc:c∈P.chains) {x:V}
   (hx:x∈zb Q true c):x∈P.reps:=by
 exact List.mem_flatten.mpr ⟨zb Q true c,List.mem_map.mpr ⟨c,hc,rfl⟩,hx⟩
theorem y0.z10b {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q) {c:List V} (hc:c∈P.chains) {x:V} (hx:x∈c) :
   x∈P.reps↔x∈zb Q true c:=by
 classical
 refine ⟨?_,P.z9d hc⟩
 intro hxr
 have hp:=List.perm_cons_erase hc
 have hnd:(c ++ (P.chains.erase c).flatten).Nodup:=hp.flatten.nodup_iff.mp P.nodup
 have hrp:=(hp.map (zb Q true)).flatten
 have hv:=hrp.mem_iff.mp hxr
 simp only [List.map_cons,List.flatten_cons,List.mem_append] at hv
 rcases hv with hv | hv
 · exact hv
 · exact ((List.nodup_append.mp hnd).2.2 x hx x
     ((z87 Q _).subset hv) rfl).elim
theorem ClosedChain.z9c {V:Type*} {G:SimpleGraph V} {Q:Set V}
   {c:List V} (hc:ClosedChain G Q c) {x:V} (hx:x∈Q) :
   x∈zb Q true c↔x∈c.head? :=by
 classical
 constructor
 · intro hrep
   obtain ⟨A,B,he,hcut⟩:=(z59 Q true c x).mp hrep
   rcases hcut with ⟨rfl,_⟩ | ⟨hne,hend⟩
   · simp [he]
   · have hp:=List.isChain_append.mp (he ▸ hc.positive)
     have hla:A.getLast hne∈A.getLast? :=List.getLast?_eq_some_getLast hne
     exact ((hp.2.2 _ hla x (by simp)).elim (fun h => h (hend _ hla)) (fun h => h hx)).elim
 · intro hh
   cases c with
   | nil => simp at hh
   | cons y B =>
     have he:y=x:=by simpa using hh
     subst y
     simp [zb]
theorem y0.z15f {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q) {x:V} (hx:x∈P.reps) (hxQ:x∉Q) :
   ∃ c∈P.chains,∃ A B:List V,∃ y:V,
     c=A ++ x ::y ::B∧y∉P.reps:=by
 obtain ⟨rc,hrc,hxc⟩:=List.mem_flatten.mp hx
 obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hrc
 obtain ⟨A,B,he,hcut⟩:=(z59 Q true c x).mp hxc
 have hnB:B ≠ []:=by
   intro hb
   have z20d:x∈c.getLast? :=by simp [he,hb]
   exact hxQ ((P.ends c hc).2 x z20d)
 obtain ⟨y,D,hB⟩:=List.exists_cons_of_ne_nil hnB
 subst B
 refine ⟨c,hc,A,D,y,he,?_⟩
 intro hy
 have hyc:y∈c:=by simp [he]
 have z210:=(P.z10b hc hyc).mp hy
 have hnc:=(List.nodup_flatten.mp P.nodup).1 c hc
 have z1fc:=z9a hnc z210 (show c=(A ++ [x]) ++ y ::D by
   simpa only [List.append_assoc,List.singleton_append] using he)
 rcases z1fc with ⟨z1a5,_⟩ | ⟨_,z11c⟩
 · simp at z1a5
 · exact hxQ (z11c x (by simp))
theorem ClosedChain.zcb {V:Type*} {G:SimpleGraph V} {Q:Set V}
   {c:List V} (hc:ClosedChain G Q c) (hn:c.Nodup) :
   (zb Q true c).countP (fun x => decide (x∈Q))=1:=by
 classical
 let x:=c.head hc.nonempty
 have hxQ:x∈Q:=hc.ends.1 x (List.head?_eq_some_head _)
 have he:((zb Q true c).filter (fun x => decide (x∈Q))).toFinset={x}:=by
   ext y
   simp only [List.mem_toFinset,List.mem_filter,decide_eq_true_eq,Finset.mem_singleton]
   constructor
   · rintro ⟨hy,hyQ⟩
     have hh:=hc.z9c hyQ |>.mp hy
     simpa only [List.head?_eq_some_head hc.nonempty,Option.mem_def,Option.some.injEq] using hh.symm
   · rintro rfl
     exact ⟨(hc.z9c hxQ).mpr (List.head?_eq_some_head _),hxQ⟩
 rw [List.countP_eq_length_filter,← List.toFinset_card_of_nodup
   (((z39 Q true c).nodup hn).filter _),he]
 simp
theorem y0.zcb {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q):P.reps.countP (fun x => decide (x∈Q))=P.chains.length:=by
 classical
 simp only [y0.reps,List.countP_flatten,List.map_map]
 have hm:P.chains.map (fun c => (zb Q true c).countP (fun x => decide (x∈Q))) =
     P.chains.map (fun _ => 1):=by
   apply List.map_congr_left
   intro c hc
   exact (P.z11 hc).zcb ((List.nodup_flatten.mp P.nodup).1 c hc)
 simp only [Function.comp_def]
 rw [hm]
 simp
theorem y0.z141 {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) :
   (P.reps.filter (fun x => x∉Q)).length=P.z4:=by
 classical
 have hh:=P.reps.length_eq_countP_add_countP (fun x => decide (x∈Q))
 rw [P.zcb,P.z129] at hh
 simp only [Bool.not_eq_true,decide_eq_false_iff_not,List.countP_eq_length_filter] at hh
 dsimp [y0.z4]
 omega
theorem y0.z119 {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q) {c d:List V} (hc:c∈P.chains) (hd:d∈P.chains) (hne:c≠d) :
   c.Disjoint d:=by
 classical
 have hp:=List.perm_cons_erase hc
 have hnd:(c ++ (P.chains.erase c).flatten).Nodup:=hp.flatten.nodup_iff.mp P.nodup
 apply List.disjoint_left.mpr
 intro x hx hy
 exact (List.nodup_append.mp hnd).2.2 x hx x
   (List.mem_flatten.mpr ⟨d,(List.mem_erase_of_ne (Ne.symm hne)).mpr hd,hy⟩) rfl
theorem z17d {V:Type*} (Q:Set V) {c:List V} (hn:c ≠ []) :
   c.head hn∈zb Q true c:=by
 cases c with
 | nil => contradiction
 | cons x c => simp [zb]
theorem y0.zef {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q) {c:List V} (hc:c∈P.chains) (hc1:c.length≠1)
   {x:V} (hx:x∈P.reps) (hxc:x∉c) :
   ∃ f:List V → Bool,∃ y:V,y∈P.chains.flatten∧y∉P.reps ∧
     x∈(P.orient f).reps∧y∈(P.orient f).reps:=by
 classical
 let f:List V → Bool:=fun d => decide (d=c)
 let y:=c.getLast (P.nonempty c hc)
 have hyc:y∈c:=List.getLast_mem _
 have hyQ:y∈Q:=(P.ends c hc).2 y (List.getLast?_eq_some_getLast _)
 have hyR:y∉P.reps:=by
   intro hy
   have hh:=(P.z11 hc).z9c hyQ |>.mp ((P.z10b hc hyc).mp hy)
   have hhe:c.head (P.nonempty c hc)=c.getLast (P.nonempty c hc):=by
     simpa only [List.head?_eq_some_head (P.nonempty c hc),Option.mem_def,Option.some.injEq] using hh
   obtain ⟨z,hz⟩:=(List.Nodup.head_eq_getLast_iff (P.nonempty c hc)
     ((List.nodup_flatten.mp P.nodup).1 c hc)).mp hhe
   exact hc1 (by simp [hz])
 have z20e:x∈(P.orient f).reps:=by
   obtain ⟨rc,hrc,hxr⟩:=List.mem_flatten.mp hx
   obtain ⟨d,hd,rfl⟩:=List.mem_map.mp hrc
   have hdc:d≠c:=by
     intro he
     subst d
     exact hxc ((z39 Q true c).subset hxr)
   have z1ff:d∈(P.orient f).chains:=by
     rw [orient_chains]
     exact List.mem_map.mpr ⟨d,hd,by simp [f,z1d,hdc]⟩
   exact (P.orient f).z9d z1ff hxr
 have z1fb:c.reverse∈(P.orient f).chains:=by
   rw [orient_chains]
   exact List.mem_map.mpr ⟨c,hc,by simp [f,z1d]⟩
 have z20f:y∈(P.orient f).reps:=by
   apply (P.orient f).z9d z1fb
   have hh:=z17d Q (show c.reverse ≠ [] by simpa using P.nonempty c hc)
   simpa using hh
 exact ⟨f,y,List.mem_flatten.mpr ⟨c,hc,hyc⟩,hyR,z20e,z20f⟩
theorem z1af {α:Type*} {l:List α} (hn:l.Nodup) (hl: 2≤ l.length) (a: α) :
   ∃ b∈l,b≠a:=by
 cases l with
 | nil => simp at hl
 | cons b l =>
   cases l with
   | nil => simp at hl
   | cons c l =>
     have hbc:b≠c:=by
       intro he
       exact (List.nodup_cons.mp hn).1 (by simp [he])
     by_cases hba:b=a
     · exact ⟨c,by simp,by intro he; exact hbc (hba.trans he.symm)⟩
     · exact ⟨b,by simp,hba⟩
theorem y0.z1bf {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q) (hu: 2≤ P.z46.length) {x:V} (hx:x∈P.reps) :
   ∃ f:List V → Bool,∃ y:V,y∈P.chains.flatten∧y∉P.reps ∧
     x∈(P.orient f).reps∧y∈(P.orient f).reps:=by
 classical
 obtain ⟨d,hd,hxd⟩:=List.mem_flatten.mp (P.z9e.subset hx)
 obtain ⟨c,hc,hcd⟩:=z1af (P.z19f.filter _) hu d
 have hc' :c∈P.chains∧c.length≠1:=by simpa [y0.z46] using hc
 exact P.zef hc'.1 hc'.2 hx (fun hxc =>
   List.disjoint_left.mp (P.z119 hc'.1 hd hcd) hxc hxd)
theorem zbc {t k L e v d:ℕ}
   (ht: 9≤ t) (hkt:k≤2*t+1) (hL:L+t=k)
   (hve:v≤2*e) (hdL:d*e≤ L) (htv:t≤ v+d)
   (hd: 2≤ d) (hd6:d≤6) :
   (d=2∧t≤ v+2) ∨
   (d=3∧((t=9∧e=3∧v=6)∨(t=11∧e=4∧v=8))) ∨
   (d=5∧t=9∧k=19∧e=2∧v=4):=by
 interval_cases d
 · exact Or.inl ⟨rfl,htv⟩
 · have htt:t≤11:=by nlinarith
   interval_cases t
   · exact Or.inr (Or.inl ⟨rfl,Or.inl ⟨rfl,by omega,by omega⟩⟩)
   · omega
   · exact Or.inr (Or.inl ⟨rfl,Or.inr ⟨rfl,by omega,by omega⟩⟩)
 · have htt:t≤9:=by nlinarith
   omega
 · have htt:t≤9:=by nlinarith
   exact Or.inr (Or.inr ⟨rfl,by omega,by omega,by omega,by omega⟩)
 · have htt:t≤9:=by nlinarith
   omega
@[simp] theorem y0.orient_vertices {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q) (f:List V → Bool):(P.orient f).vertices=P.vertices:=by
 ext x
 exact (P.z164 f).mem_iff
theorem y0.z7 {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q):P.zd⊆P.vertices:=P.z9e.subset
structure LargeSystem {V:Type*} [Fintype V] (G:SimpleGraph V) (Q:Set V)
   (k:ℕ) (P:y0 G Q):Prop where
 optimal:P.Optimal k
 clique:G.IsClique Q
 no_cycle:¬ SimpleGraph.cycleGraph (k+1)⊑G
 nine: 9≤ Q.ncard
 le_k:Q.ncard≤ k
 k_le:k≤2*Q.ncard+1
 maximal:G.cliqueNum≤ Q.ncard
 independent:G.indepNum≤ k
 expansion:∀ I:Set V,G.IsIndepSet I → I.Nonempty → 
   k*I.ncard+1≤(z0 G I).ncard
namespace LargeSystem
variable {V:Type*} [Fintype V] {G:SimpleGraph V} {Q:Set V} {k:ℕ}
 {P:y0 G Q} (H:LargeSystem G Q k P)
include H
theorem degree (x:V):k+1≤(z0 G {x}).ncard:=by
 simpa using H.expansion {x} (by simp) (Set.singleton_nonempty x)
theorem vertices_le:P.vertices.ncard≤ k:=by
 rw [P.z13a]
 have hh:=H.optimal.1
 have hk:=H.le_k
 omega
theorem orient (f:List V → Bool):LargeSystem G Q k (P.orient f) :=
 ⟨(P.orient_optimal f).mpr H.optimal,H.clique,H.no_cycle,H.nine,H.le_k,
   H.k_le,H.maximal,H.independent,H.expansion⟩
theorem no_one {x y:V} (hx:x∈P.reps) (hy:y∈P.reps) :
   ¬ z5 G P.vertices x y 1 :=
 P.z127 H.optimal (by have:=H.nine; have:=H.le_k; omega)
   H.clique H.no_cycle H.le_k hx hy
theorem misses_reps {x:V} (hx:x∈P.reps) :
   ∀ u∈z1 G P.vertices x 0,∀ z∈P.zd \ {x},¬ G.Adj u z:=by
 apply z62 P.z7 hx
 intro y hy d hd hd'
 have he:d=1:=by omega
 subst d
 exact H.no_one hx hy
theorem extra_degree {x y:V} (hx:x∈P.reps) (hy:y∈P.vertices)
   (hyR:y∉P.reps)
   (z54:∀ u∈z1 G P.vertices x 0,¬ G.Adj u y) :
   Q.ncard+1≤(z1 G P.vertices x 1).ncard:=by
 let Z:=insert y (P.zd \ {x})
 have ht: 1≤ Q.ncard:=by have:=H.nine; omega
 have hc:Z.ncard=Q.ncard:=by
   rw [Set.ncard_insert_of_notMem (by exact fun h => hyR h.1),
     Set.ncard_sdiff_singleton_of_mem (show x∈P.zd from hx),P.z34]
   omega
 have hZ:Z⊆P.vertices:=by
   intro z hz
   rcases hz with rfl | hz
   · exact hy
   · exact P.z7 hz.1
 have hb:=z69 (P.z7 hx) H.vertices_le hZ H.degree
   (by
     intro u hu z hz
     rcases hz with rfl | hz
     · exact z54 u hu
     · exact H.misses_reps hx u hu z hz)
 rw [hc] at hb
 have hs:=H.vertices_le
 omega
theorem interior_degree {x:V} (hx:x∈P.reps) (hxQ:x∉Q) :
   Q.ncard+1≤(z1 G P.vertices x 1).ncard:=by
 obtain ⟨c,hc,A,B,y,he,hyR⟩:=P.z15f hx hxQ
 have hy:y∈P.vertices:=List.mem_flatten.mpr ⟨c,hc,by simp [he]⟩
 apply H.extra_degree hx hy hyR
 apply z3f (P.z7 hx) hy
   (by intro heq; exact hyR (heq ▸ hx))
 intro d hd hd'
 have hd1:d=1:=by omega
 subst d
 exact P.z155 H.optimal (by have:=H.nine; have:=H.le_k; omega)
   H.clique H.no_cycle H.le_k hc A B he
theorem reverse_degree {x:V} (hx:x∈P.reps)
   (he:∃ f:List V → Bool,∃ y:V,y∈P.chains.flatten∧y∉P.reps ∧
     x∈(P.orient f).reps∧y∈(P.orient f).reps) :
   Q.ncard+1≤(z1 G P.vertices x 1).ncard:=by
 obtain ⟨f,y,hy,hyR,hx',hy'⟩:=he
 apply H.extra_degree hx hy hyR
 apply z3f (P.z7 hx) hy
   (by intro heq; exact hyR (heq ▸ hx))
 intro d hd hd'
 have hd1:d=1:=by omega
 subst d
 simpa using (H.orient f).no_one hx' hy'
theorem two_chains_degree (hu: 2≤ P.z46.length) {x:V} (hx:x∈P.reps) :
   Q.ncard+1≤(z1 G P.vertices x 1).ncard :=
 H.reverse_degree hx (P.z1bf hu hx)
theorem first_nonclique {x:V} (hb:Q.ncard+1≤(z1 G P.vertices x 1).ncard) :
   ¬ G.IsClique (z1 G P.vertices x 1):=by
 intro hc
 have hh:=(za hc).trans H.maximal
 omega
theorem first_pair {x:V} (hb:Q.ncard+1≤(z1 G P.vertices x 1).ncard) :
   2≤ independence G (z1 G P.vertices x 1):=by
 by_contra! hn
 exact H.first_nonclique hb (zf (by omega))
end LargeSystem
theorem zad {V:Type*} [Fintype V] {ι:Type*}
   (G:SimpleGraph V) (D: ι → Set V) (F:Finset ι)
   (hdis:∀ i∈F,∀ j∈F,i≠j → Disjoint (D i) (D j))
   (hsep:∀ i∈F,∀ j∈F,i≠j → 
     ∀ x∈D i,∀ y∈D j,¬ G.Adj x y) :
   ∑ i∈F,independence G (D i)≤ G.indepNum:=by
 classical
 have hh: ∑ i∈F,independence G (D i)≤ independence G (⋃ i∈F,D i):=by
   induction F using Finset.induction_on with
   | empty => simp
   | @insert i F hi ih =>
     have hu:(⋃ j∈insert i F,D j)=D i ∪ ⋃ j∈F,D j:=by simp
     rw [hu,Finset.sum_insert hi]
     have hD:Disjoint (D i) (⋃ j∈F,D j):=by
       apply Set.disjoint_left.mpr
       intro v hvi hvF
       obtain ⟨j,hj,hvj⟩:=Set.mem_iUnion₂.mp hvF
       exact Set.disjoint_left.mp
         (hdis i (by simp) j (by simp [hj]) (by intro he; subst j; exact hi hj)) hvi hvj
     calc
       _≤ independence G (D i)+independence G (⋃ j∈F,D j):=by
         exact Nat.add_le_add_left (ih
           (fun j hj l hl hne => hdis j (by simp [hj]) l (by simp [hl]) hne)
           (fun j hj l hl hne => hsep j (by simp [hj]) l (by simp [hl]) hne)) _
       _≤_:=z8a Set.subset_union_left Set.subset_union_right hD (by
         intro x hx y hy
         obtain ⟨j,hj,hyj⟩:=Set.mem_iUnion₂.mp hy
         exact hsep i (by simp) j (by simp [hj])
           (by intro he; subst j; exact hi hj) x hx y hyj)
 exact hh.trans (by simpa only [z31] using
   (z76 (G:=G) (Set.subset_univ (⋃ i∈F,D i))))
theorem packing_balls {V:Type*} [Fintype V] {G:SimpleGraph V} {X:Set V}
   (F:Finset V) (r w:V → ℕ) (hF:∀ x∈F,x∈X)
   (hno:∀ x∈F,∀ y∈F,x≠y → ∀ d,1≤ d → d≤ r x+r y+2 → 
     ¬ z5 G X x y d)
   (z132:∀ x∈F,w x≤ independence G (z1 G X x (r x))) :
   ∑ x∈F,w x≤ G.indepNum:=by
 have hh:=zad G (fun x => z1 G X x (r x)) F
   (fun x hx y hy hxy => (z47 (hF x hx) (hF y hy) hxy (hno x hx y hy hxy)).1)
   (fun x hx y hy hxy => (z47 (hF x hx) (hF y hy) hxy (hno x hx y hy hxy)).2)
 exact (Finset.sum_le_sum z132).trans hh
abbrev y0.z1a {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q):Set V:={x | [x]∈P.chains}
theorem y0.missing_eq_flat {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q):P.z1a={x | x∈P.z13.flatten}:=by
 classical
 ext x
 constructor
 · intro hx
   exact List.mem_flatten.mpr ⟨[x],by simpa [y0.z13] using hx,by simp⟩
 · intro hx
   obtain ⟨c,hc,hxc⟩:=List.mem_flatten.mp hx
   have hcf:c∈P.chains∧c.length=1:=by simpa [y0.z13] using hc
   obtain ⟨y,rfl⟩:=List.length_eq_one_iff.mp hcf.2
   have he:x=y:=by simpa using hxc
   simpa [he] using hcf.1
theorem y0.missing_subset_reps {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q):P.z1a⊆P.zd:=by
 intro x hx
 exact P.z9d hx (by simp [zb])
theorem y0.missing_subset_Q {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q):P.z1a⊆Q:=by
 intro x hx
 exact (P.ends [x] hx).1 x (by simp)
theorem y0.missing_ncard {V:Type*} [Fintype V] {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q):P.z1a.ncard=P.z13.length:=by
 classical
 have he:P.z1a=(↑P.z13.flatten.toFinset:Set V):=by
   rw [P.missing_eq_flat]
   ext; simp
 rw [he,Set.ncard_coe_finset,List.toFinset_card_of_nodup,P.z7c]
 exact ((List.filter_sublist).flatten).nodup P.nodup
theorem y0.incident_add_missing {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) :
   P.ze+P.z1a.ncard=Q.ncard:=by
 rw [P.missing_ncard]
 dsimp [y0.ze]
 exact Nat.sub_add_cancel P.z50
theorem y0.amount_pos_used {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) (ha: 0 < P.z2) :
   0 < P.z46.length:=by
 by_contra! hn
 have he:P.z46 = []:=List.length_eq_zero_iff.mp (by omega)
 have hh:=P.partition.flatten.length_eq
 simp only [he,List.nil_append,P.z7c] at hh
 have hle:=P.z50
 have hf:=P.z66
 omega
theorem y0.singleton_extra_rep {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) (ha: 0 < P.z2)
   {x:V} (hx:x∈P.z1a) :
   ∃ f:List V → Bool,∃ y:V,y∈P.chains.flatten∧y∉P.reps ∧
     x∈(P.orient f).reps∧y∈(P.orient f).reps:=by
 classical
 obtain ⟨c,hc⟩:=List.exists_mem_of_ne_nil P.z46
   (List.length_pos_iff.mp (P.amount_pos_used ha))
 have hcf:c∈P.chains∧c.length≠1:=by simpa [y0.z46] using hc
 apply P.zef hcf.1 hcf.2 (P.missing_subset_reps hx)
 intro hxc
 have hn:c ≠ [x]:=by intro he; simp [he] at hcf
 exact List.disjoint_left.mp (P.z119 hcf.1 hx hn) hxc (by simp)
theorem y0.interior_representatives_ncard {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) :
   (P.zd \ Q).ncard=P.z4:=by
 classical
 have he:P.zd \ Q =
     (↑(P.reps.filter (fun x => x∉Q)).toFinset:Set V):=by ext; simp
 rw [he,Set.ncard_coe_finset,List.toFinset_card_of_nodup
   ((P.z9e.nodup P.nodup).filter _),P.z141]
namespace LargeSystem
variable {V:Type*} [Fintype V] {G:SimpleGraph V} {Q:Set V} {k:ℕ}
 {P:y0 G Q} (H:LargeSystem G Q k P)
include H
theorem two_large_first (h2t: 2*Q.ncard≤ k) :
   ∃ x∈P.reps,∃ y∈P.reps,x≠y ∧
     Q.ncard+1≤(z1 G P.vertices x 1).ncard ∧
     Q.ncard+1≤(z1 G P.vertices y 1).ncard:=by
 have ht:=H.nine
 by_cases hs:P.vertices.ncard < k
 · have ha:∀ x∈P.reps,Q.ncard+1≤(z1 G P.vertices x 1).ncard:=by
     intro x hx
     have hb:=z69 (P.z7 hx) H.vertices_le
       (show P.zd \ {x}⊆P.vertices from Set.sdiff_subset.trans P.z7)
       H.degree (H.misses_reps hx)
     rw [Set.ncard_sdiff_singleton_of_mem (show x∈P.zd from hx),
       P.z34] at hb
     omega
   obtain ⟨x,hx,y,hy,hxy⟩:=(Set.one_lt_ncard).mp (show 1 < P.zd.ncard by
     rw [P.z34]; omega)
   exact ⟨x,hx,y,hy,hxy,ha x hx,ha y hy⟩
 · have hs:P.vertices.ncard=k:=by have:=H.vertices_le; omega
   have hL: 0 < P.z2:=by rw [P.z13a] at hs; omega
   by_cases he: 2≤ P.z4
   · obtain ⟨x,hx,y,hy,hxy⟩:=(Set.one_lt_ncard).mp
       (show 1 < (P.zd \ Q).ncard by rw [P.interior_representatives_ncard]; omega)
     exact ⟨x,hx.1,y,hy.1,hxy,H.interior_degree hx.1 hx.2,H.interior_degree hy.1 hy.2⟩
   · have z54: 2≤ P.z1a.ncard:=by
       have hv:=P.z38
       have hc:=P.incident_add_missing
       omega
     obtain ⟨x,hx,y,hy,hxy⟩:=(Set.one_lt_ncard).mp (show 1 < P.z1a.ncard by omega)
     exact ⟨x,P.missing_subset_reps hx,y,P.missing_subset_reps hy,hxy,
       H.reverse_degree (P.missing_subset_reps hx) (P.singleton_extra_rep hL hx),
       H.reverse_degree (P.missing_subset_reps hy) (P.singleton_extra_rep hL hy)⟩
theorem short:∃ x∈P.reps,∃ y∈P.reps,∃ d,2≤ d∧d≤6 ∧
   z5 G P.vertices x y d:=by
 classical
 by_contra hn
 have hno:∀ x∈P.reps,∀ y∈P.reps,∀ d,1≤ d → d≤6 → 
     ¬ z5 G P.vertices x y d:=by
   intro x hx y hy d hd hd' hp
   by_cases hd1:d=1
   · subst d; exact H.no_one hx hy hp
   · exact hn ⟨x,hx,y,hy,d,by omega,hd',hp⟩
 have z54:∀ x∈P.reps,∀ u∈z1 G P.vertices x 1,
     ∀ z∈P.zd \ {x},¬ G.Adj u z:=by
   intro x hx
   apply z62 P.z7 hx
   intro y hy d hd hd'
   exact hno x hx y hy d hd (by omega)
 have z1c8:∀ x∈P.reps,2≤ independence G (z1 G P.vertices x 2):=by
   intro x hx
   exact zd9 P.z7 hx P.z34
     H.vertices_le H.maximal H.degree (z54 x hx)
 let F:=P.reps.toFinset
 have hFc:F.card=Q.ncard:=by
   rw [List.toFinset_card_of_nodup (P.z9e.nodup P.nodup),P.z129]
 have z179:=packing_balls F (fun _ => 2) (fun _ => 2)
   (fun x hx => P.z7 (List.mem_toFinset.mp hx))
   (fun x hx y hy _ d hd hd' => hno x (List.mem_toFinset.mp hx) y
     (List.mem_toFinset.mp hy) d hd (by omega))
   (fun x hx => z1c8 x (List.mem_toFinset.mp hx))
 have h2t: 2*Q.ncard≤ k:=by
   have hi:=H.independent
   simpa only [Finset.sum_const,smul_eq_mul,hFc,Nat.mul_comm] using z179.trans hi
 obtain ⟨a,ha,b,hb,hab,haB,hbB⟩:=H.two_large_first h2t
 have z1df:∀ x∈P.reps,(x=a∨x=b) → 
     3≤ independence G (z1 G P.vertices x 2):=by
   intro x hx he
   apply zc9 (by have:=H.nine; omega) (by have:=H.nine; omega)
     (by have:=H.nine; omega) P.z7 hx P.z34
     H.vertices_le H.maximal H.no_cycle H.expansion (z54 x hx)
   apply H.first_nonclique
   rcases he with rfl | rfl
   · exact haB
   · exact hbB
 let W:V → ℕ:=fun x => 2+if x∈({a,b}:Finset V) then 1 else 0
 have hw:∀ x∈F,W x≤ independence G (z1 G P.vertices x 2):=by
   intro x hx
   have hxR:=List.mem_toFinset.mp hx
   dsimp [W]
   split_ifs with he
   · exact z1df x hxR (by simpa using he)
   · simpa using z1c8 x hxR
 have z1c7:=packing_balls F (fun _ => 2) W
   (fun x hx => P.z7 (List.mem_toFinset.mp hx))
   (fun x hx y hy _ d hd hd' => hno x (List.mem_toFinset.mp hx) y
     (List.mem_toFinset.mp hy) d hd (by omega)) hw
 have hsub:({a,b}:Finset V)⊆F:=by
   intro x hx
   simp only [Finset.mem_insert,Finset.mem_singleton] at hx
   rcases hx with rfl | rfl <;> exact List.mem_toFinset.mpr (by assumption)
 have hsum: ∑ x∈F,W x=2*Q.ncard+2:=by
   simp only [W,Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul,hFc,
     ← Finset.sum_filter]
   have z18e:F.filter (fun x => x∈({a,b}:Finset V))={a,b}:=by
     ext x; simp only [Finset.mem_filter]; exact ⟨And.right,fun hx => ⟨hsub hx,hx⟩⟩
   rw [z18e]
   simp [hab,Nat.mul_comm]
 rw [hsum] at z1c7
 have hi:=z1c7.trans H.independent
 have hk:=H.k_le
 omega
end LargeSystem
namespace LargeSystem
variable {V:Type*} [Fintype V] {G:SimpleGraph V} {Q:Set V} {k:ℕ}
 {P:y0 G Q} (H:LargeSystem G Q k P)
include H
theorem short_information {x y:V} {d:ℕ} (hx:x∈P.reps) (hy:y∈P.reps)
   (hd: 1≤ d) (hd6:d≤6) (hp:z5 G P.vertices x y d) :
   ∃ u v:List V,∃ D:List (List V),∃ F:List ℕ,
     P.chains.Perm ((x ::u) ::(y ::v) ::D) ∧
     P.z2=k - Q.ncard∧2≤ d ∧
     (D.filter (fun c => c.length=1)).length+2≤ d ∧
     z3 P F ∧ ∀ a∈F,d≤ a:=by
 obtain ⟨I,hIl,hI,hIn,hout⟩:=hp.z139
 have hI0:I ≠ []:=by intro he; simp [he] at hIl; omega
 have ho:∀ z∈I,z∉Q:=fun z hz hq => hout z hz (P.cover z hq)
 simpa only [hIl] using P.z138 H.optimal H.clique H.no_cycle H.nine H.le_k H.k_le
   hx hy hp.2.2.1 I hI (z56 hI0 ho) hIn
   (List.disjoint_left.mpr hout) hI0 (by omega) ho
theorem short_heads {x y:V} {d:ℕ} (hx:x∈P.reps) (hy:y∈P.reps)
   (hd: 1≤ d) (hd6:d≤6) (hp:z5 G P.vertices x y d):x∈Q∧y∈Q:=by
 obtain ⟨u,v,D,F,hP,_⟩:=H.short_information hx hy hd hd6 hp
 exact ⟨(P.ends (x ::u) (hP.mem_iff.mpr (by simp))).1 x (by simp),
   (P.ends (y ::v) (hP.mem_iff.mpr (by simp))).1 y (by simp)⟩
theorem no_short_interior {x y:V} (hx:x∈P.reps) (hy:y∈P.reps) (hxQ:x∉Q)
   (d:ℕ) (hd: 1≤ d) (hd6:d≤6):¬ z5 G P.vertices x y d :=
 fun hp => hxQ (H.short_heads hx hy hd hd6 hp).1
theorem no_short_step {c:List V} (hc:c∈P.chains) {x y:V} (A B:List V)
   (he:c=A ++ x ::y ::B) (d:ℕ) (hd: 1≤ d) (hd6:d≤6) :
   ¬ z5 G P.vertices x y d:=by
 intro hp
 obtain ⟨I,hIl,hI,hIn,hout⟩:=hp.z139
 have hI0:I ≠ []:=by intro hi; simp [hi] at hIl; omega
 have ho:∀ z∈I,z∉Q:=fun z hz hq => hout z hz (P.cover z hq)
 exact P.z135 H.optimal H.clique H.no_cycle H.nine H.le_k H.k_le hc A I B he
   hI (z56 hI0 ho) hIn (List.disjoint_left.mpr hout) hI0 (by omega) ho
theorem parameter {x y:V} {d:ℕ} (hx:x∈P.reps) (hy:y∈P.reps)
   (hd: 1≤ d) (hd6:d≤6) (hp:z5 G P.vertices x y d) :
   P.z2+Q.ncard=k∧(∃ A,z3 P A ∧ ∀ a∈A,d≤ a) ∧
   ((d=2∧Q.ncard≤ P.ze+2∧P.z1a⊆{x,y}) ∨
    (d=3∧((Q.ncard=9∧P.z4=3∧P.ze=6) ∨
               (Q.ncard=11∧P.z4=4∧P.ze=8))∧x∈P.z1a∧y∈P.z1a) ∨
    (d=5∧Q.ncard=9∧k=19∧P.z4=2∧P.ze=4 ∧
      x∈P.z1a∧y∈P.z1a)):=by
 classical
 obtain ⟨u,v,D,F,hP,hL,hd2,hD,hF,hFd⟩:=H.short_information hx hy hd hd6 hp
 have hsk:P.z2+Q.ncard=k:=by have:=H.le_k; omega
 have z98:=(hP.filter (fun c => decide (c.length=1))).length_eq
 change P.z13.length=_ at z98
 have huc:((x ::u).length=1)↔u = []:=by simp
 have hvc:((y ::v).length=1)↔v = []:=by simp
 simp only [List.filter_cons,huc,hvc] at z98
 have z217:P.z13.length≤(D.filter (fun c => c.length=1)).length+2:=by
   split_ifs at z98 <;> (try simp only [List.length_cons] at z98) <;> omega
 have hvt:Q.ncard≤ P.ze+d:=by
   have hh:=P.incident_add_missing
   rw [P.missing_ncard] at hh
   omega
 obtain ⟨hsum,hlen,_⟩:=hF.count
 have hm:d*P.z4≤ P.z2:=by simpa [hsum,hlen] using z58 F d hFd
 have hc:=zbc H.nine H.k_le hsk P.z38 hm hvt hd2 hd6
 have z176:P.z13.length=d → x∈P.z1a∧y∈P.z1a:=by
   intro hs
   have huv:u = []∧v = []:=by
     split_ifs at z98 with hu hv <;> (try simp only [List.length_cons] at z98) <;>
       first | exact ⟨of_decide_eq_true hu,of_decide_eq_true hv⟩ | omega
   obtain ⟨rfl,rfl⟩:=huv
   exact ⟨hP.mem_iff.mpr (by simp),hP.mem_iff.mpr (by simp)⟩
 refine ⟨hsk,⟨F,hF,hFd⟩,?_⟩
 rcases hc with hc | hc | hc
 · refine Or.inl ⟨hc.1,hc.2,?_⟩
   have hDz:D.filter (fun c => decide (c.length=1)) = []:=List.length_eq_zero_iff.mp (by omega)
   intro z hz
   have hz' :=hP.mem_iff.mp hz
   simp only [List.mem_cons] at hz'
   rcases hz' with he | he | hz'
   · have hzx:z=x:=List.cons.inj he |>.1
     exact Or.inl hzx
   · have hzy:z=y:=List.cons.inj he |>.1
     exact Or.inr hzy
   · have hf: [z]∈D.filter (fun c => decide (c.length=1)):=List.mem_filter.mpr ⟨hz',by simp⟩
     simp [hDz] at hf
 · have hs:P.z13.length=d:=by
     have hh:=P.incident_add_missing
     rw [P.missing_ncard] at hh
     rcases hc.2 with h9 | h11 <;> omega
   exact Or.inr (Or.inl ⟨hc.1,hc.2,z176 hs⟩)
 · have hs:P.z13.length=d:=by
     have hh:=P.incident_add_missing
     rw [P.missing_ncard] at hh
     omega
   exact Or.inr (Or.inr ⟨hc.1,hc.2.1,hc.2.2.1,hc.2.2.2.1,hc.2.2.2.2,z176 hs⟩)
theorem at_least_two_chains: 2≤ P.z46.length:=by
 obtain ⟨x,hx,y,hy,d,hd,hd6,hp⟩:=H.short
 obtain ⟨hL,⟨A,hA,hAd⟩,hh⟩:=H.parameter hx hy (by omega) hd6 hp
 obtain ⟨hs,hl,_⟩:=hA.count
 have hm:=z58 A d hAd
 rw [hs,hl] at hm
 have hve:=P.zd7
 have ht:=H.nine
 have hk:=H.k_le
 rcases hh with ⟨rfl,hv,_⟩ | ⟨rfl,hh,_⟩ | ⟨rfl,ht9,hk19,he,hv,_⟩
 · omega
 · rcases hh with hh | hh <;> omega
 · omega
theorem second_triple (hk2: 2*Q.ncard≤ k) {x:V} (hx:x∈P.reps) :
   3≤ independence G (z1 G P.vertices x 2):=by
 have hp:=H.first_pair (H.two_chains_degree H.at_least_two_chains hx)
 obtain ⟨I,hIs,hI,hIc⟩:=z6 G (z1 G P.vertices x 1)
 have hIn:I.Nonempty:=(Set.ncard_pos).mp (by omega)
 have he:=H.expansion I hI hIn
 have hb:=z24 hIs (Set.empty_subset P.vertices) (by simp)
 simp only [Set.ncard_empty,Nat.add_zero,Nat.reduceAdd] at hb
 have hs:=H.vertices_le
 have hm: 2*k≤ k*I.ncard:=by nlinarith
 apply z121 (by have:=H.nine; omega) (by have:=H.nine; omega) H.no_cycle H.maximal
 omega
end LargeSystem
theorem y0.incident_representatives_ncard {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) :
   (P.zd \ P.z1a).ncard=P.ze:=by
 have hh:=Set.ncard_sdiff_add_ncard_of_subset P.missing_subset_reps
 rw [P.z34] at hh
 have hc:=P.incident_add_missing
 omega
namespace LargeSystem
variable {V:Type*} [Fintype V] {G:SimpleGraph V} {Q:Set V} {k:ℕ}
 {P:y0 G Q} (H:LargeSystem G Q k P)
include H
theorem exclude_two_missing (hL:P.z2+Q.ncard=k)
   (hA:∃ A,z3 P A ∧ ∀ a∈A,2≤ a)
   (hv:Q.ncard≤ P.ze+2) (hM:P.z1a.Nonempty):False:=by
 classical
 let J:=P.zd \ P.z1a
 have hJc:J.ncard=P.ze:=P.incident_representatives_ncard
 have hno:∀ x∈J,∀ y∈J,∀ d,1≤ d → d≤6 → 
     ¬ z5 G P.vertices x y d:=by
   intro x hx y hy d hd hd6 hp
   obtain ⟨_,_,hc⟩:=H.parameter hx.1 hy.1 hd hd6 hp
   rcases hc with ⟨_,_,hm⟩ | ⟨_,hh,_⟩ | ⟨_,ht9,_,_,hv4,_⟩
   · obtain ⟨z,hz⟩:=hM
     rcases hm hz with he | he
     · exact hx.2 (he ▸ hz)
     · exact hy.2 (he ▸ hz)
   · rcases hh with hh | hh <;> omega
   · omega
 obtain ⟨A,hA,hAs⟩:=hA
 obtain ⟨hs,hl,_⟩:=hA.count
 have hm:=z58 A 2 hAs
 rw [hs,hl] at hm
 have hve:=P.z38
 have hk2: 2*Q.ncard≤ k+2:=by omega
 have z1d1:∀ x∈J,3≤ independence G (z1 G P.vertices x 2):=by
   intro x hx
   have z1d6:=H.first_pair (H.two_chains_degree H.at_least_two_chains hx.1)
   obtain ⟨I,hIs,hI,hIc⟩:=z6 G (z1 G P.vertices x 1)
   have he:=H.expansion I hI ((Set.ncard_pos).mp (by omega))
   have z54:∀ u∈I,∀ z∈J \ {x},¬ G.Adj u z:=by
     intro u hu z hz
     apply z3f (P.z7 hx.1)
       (P.z7 hz.1.1) (Ne.symm hz.2) _ u (hIs hu)
     intro d hd hd'
     exact hno x hx z hz.1 d hd (by omega)
   have hb:=z24 hIs
     (show J \ {x}⊆P.vertices from fun z hz => P.z7 hz.1.1) z54
   rw [Set.ncard_sdiff_singleton_of_mem hx,hJc] at hb
   norm_num only at hb
   have hr:=H.vertices_le
   have he2: 2*k≤ k*I.ncard:=by nlinarith
   apply z121 (by have:=H.nine; have:=H.le_k; omega)
     (by have:=H.nine; omega) H.no_cycle H.maximal
   have ht:=H.nine
   change max k (2*Q.ncard) < (z1 G P.vertices x 2).ncard
   omega
 have hp:=packing_balls J.toFinset (fun _ => 2) (fun _ => 3)
   (fun x hx => P.z7 (Set.mem_toFinset.mp hx).1)
   (fun x hx y hy _ d hd hd' => hno x (Set.mem_toFinset.mp hx) y
     (Set.mem_toFinset.mp hy) d hd (by omega))
   (fun x hx => z1d1 x (Set.mem_toFinset.mp hx))
 have hh: 3*P.ze≤ k:=by
   have ha:=hp.trans H.independent
   simpa only [Finset.sum_const,smul_eq_mul,← Set.ncard_eq_toFinset_card',hJc,Nat.mul_comm] using ha
 have ht:=H.nine
 have hk:=H.k_le
 omega
theorem exclude_three (hL:P.z2+Q.ncard=k)
   (hA:∃ A,z3 P A ∧ ∀ a∈A,3≤ a)
   (hv:(Q.ncard=9∧P.z4=3∧P.ze=6) ∨
     (Q.ncard=11∧P.z4=4∧P.ze=8)):False:=by
 classical
 obtain ⟨A,hA,hAs⟩:=hA
 obtain ⟨hs,hl,_⟩:=hA.count
 have hm:=z58 A 3 hAs
 rw [hs,hl] at hm
 have hk2: 2*Q.ncard≤ k:=by rcases hv with hv | hv <;> omega
 have hMc:P.z1a.ncard=3:=by have hh:=P.incident_add_missing; rcases hv with hv | hv <;> omega
 obtain ⟨z,hz⟩:=(Set.ncard_pos).mp (show 0 < P.z1a.ncard by omega)
 let J:=insert z (P.zd \ P.z1a)
 have hJc:J.ncard=P.ze+1:=by
   rw [Set.ncard_insert_of_notMem (by exact fun h => h.2 hz),P.incident_representatives_ncard]
 have hJR:J⊆P.zd:=by
   intro x hx
   rcases hx with rfl | hx
   · exact P.missing_subset_reps hz
   · exact hx.1
 have hJM:∀ x∈J,x∈P.z1a → x=z:=by
   intro x hx hxM
   exact hx.elim id (fun h => (h.2 hxM).elim)
 have hno:∀ x∈J,∀ y∈J,x≠y → ∀ d,1≤ d → d≤6 → 
     ¬ z5 G P.vertices x y d:=by
   intro x hx y hy hxy d hd hd6 hp
   obtain ⟨_,_,hc⟩:=H.parameter (hJR hx) (hJR hy) hd hd6 hp
   rcases hc with ⟨_,hv',_⟩ | ⟨_,_,hxM,hyM⟩ | ⟨_,ht9,_,_,hv4,_⟩
   · rcases hv with hv | hv <;> omega
   · exact hxy ((hJM x hx hxM).trans (hJM y hy hyM).symm)
   · rcases hv with hv | hv <;> omega
 have hp:=packing_balls J.toFinset (fun _ => 2) (fun _ => 3)
   (fun x hx => P.z7 (hJR (Set.mem_toFinset.mp hx)))
   (fun x hx y hy hxy d hd hd' => hno x (Set.mem_toFinset.mp hx) y
     (Set.mem_toFinset.mp hy) hxy d hd (by omega))
   (fun x hx => H.second_triple hk2 (hJR (Set.mem_toFinset.mp hx)))
 have hh: 3*(P.ze+1)≤ k:=by
   simpa only [Finset.sum_const,smul_eq_mul,← Set.ncard_eq_toFinset_card',hJc,Nat.mul_comm]
     using hp.trans H.independent
 have hk:=H.k_le
 rcases hv with hv | hv <;> omega
theorem exclude_five (ht:Q.ncard=9) (hk:k=19) (hv:P.ze=4):False:=by
 classical
 let F:=P.zd.toFinset
 let r:V → ℕ:=fun x => 1+if x∈P.z1a then 0 else 1
 let w:V → ℕ:=fun x => 2+if x∈P.z1a then 0 else 1
 have hF:∀ x∈F,x∈P.reps:=by
   intro x hx
   change x∈P.zd
   exact Set.mem_toFinset.mp hx
 have hno:∀ x∈F,∀ y∈F,x≠y → ∀ d,1≤ d → d≤ r x+r y+2 → 
     ¬ z5 G P.vertices x y d:=by
   intro x hx y hy hxy d hd hd' hp
   have hd6:d≤6:=by dsimp [r] at hd'; split_ifs at hd' <;> omega
   obtain ⟨_,_,hc⟩:=H.parameter (hF x hx) (hF y hy) hd hd6 hp
   rcases hc with ⟨_,hv',_⟩ | ⟨_,hh,_⟩ | ⟨rfl,_,_,_,_,hxM,hyM⟩
   · omega
   · rcases hh with hh | hh <;> omega
   · simp only [r,if_pos hxM,if_pos hyM] at hd'
     omega
 have hw:∀ x∈F,w x≤ independence G (z1 G P.vertices x (r x)):=by
   intro x hx
   by_cases hxM:x∈P.z1a
   · simpa only [w,r,if_pos hxM,Nat.add_zero] using H.first_pair (H.two_chains_degree H.at_least_two_chains (hF x hx))
   · simpa only [w,r,if_neg hxM,Nat.reduceAdd] using H.second_triple (by omega) (hF x hx)
 have z179:=packing_balls F r w (fun x hx => P.z7 (hF x hx)) hno hw
 have z18e:F.filter (fun x => x∉P.z1a)=(P.zd \ P.z1a).toFinset:=by
   ext x
   simp [F]
 have hsum: ∑ x∈F,w x=22:=by
   simp only [w,Finset.sum_add_distrib,Finset.sum_const,smul_eq_mul]
   have hi:(∑ x∈F,if x∈P.z1a then 0 else 1) =
       (F.filter (fun x => x∉P.z1a)).card:=by
     rw [Finset.card_filter]
     apply Finset.sum_congr rfl
     intro x _
     split_ifs <;> simp_all
   rw [hi,z18e]
   simp only [F,← Set.ncard_eq_toFinset_card',P.z34,
     P.incident_representatives_ncard,ht,hv]
 rw [hsum] at z179
 have hi:=H.independent
 omega
end LargeSystem
end CycleClique
namespace CycleClique
open scoped SimpleGraph
noncomputable local instance (p:Prop):Decidable p:=Classical.propDecidable p
noncomputable def z22 {V:Type*} (Q:Set V) (c:List V):List V :=
 if c.length=4 then c.tail.dropLast else (zb Q true c).filter (fun x => x∉Q)
theorem chosenChain_sublist {V:Type*} (Q:Set V) (c:List V) :
   (z22 Q c).Sublist c:=by
 classical
 unfold z22
 split_ifs
 · exact (List.dropLast_sublist _).trans (List.tail_sublist _)
 · exact List.filter_sublist.trans (z39 Q true c)
theorem ClosedChain.four {V:Type*} {G:SimpleGraph V} {Q:Set V} {c:List V}
   (h:ClosedChain G Q c) (hl:c.length=4) :
   ∃ u a b v,c = [u,a,b,v]∧u∈Q∧v∈Q∧a∉Q∧b∉Q:=by
 rcases c with _ | ⟨u,c⟩ <;> try simp at hl
 rcases c with _ | ⟨a,c⟩ <;> try simp at hl
 rcases c with _ | ⟨b,c⟩ <;> try simp at hl
 rcases c with _ | ⟨v,c⟩ <;> try simp at hl
 have hc:c = []:=List.length_eq_zero_iff.mp (by simpa using hl)
 subst c
 have hu:u∈Q:=h.ends.1 u (by simp)
 have hv:v∈Q:=h.ends.2 v (by simp)
 have ha:a∉Q:=h.positive.rel.resolve_left (not_not.mpr hu)
 have hb:b∉Q:=h.positive.tail.tail.rel.resolve_right (not_not.mpr hv)
 exact ⟨u,a,b,v,rfl,hu,hv,ha,hb⟩
theorem ClosedChain.chosen_rep {V:Type*} {G:SimpleGraph V} {Q:Set V} {c:List V}
   (h:ClosedChain G Q c) {x:V} (hx:x∈z22 Q c) :
   x∉Q ∧ ∃ b:Bool,x∈zb Q true (z1d b c):=by
 classical
 by_cases hl:c.length=4
 · obtain ⟨u,a,b,v,rfl,hu,hv,ha,hb⟩:=h.four hl
   have hh:x=a∨x=b:=by simpa [z22] using hx
   rcases hh with rfl | rfl
   · exact ⟨ha,false,by simp [z1d,zb,hu]⟩
   · exact ⟨hb,true,by simp [z1d,zb,hv]⟩
 · have hx' :=List.mem_filter.mp (show x∈(zb Q true c).filter (fun x => x∉Q) by
     simpa only [z22,if_neg hl] using hx)
   exact ⟨of_decide_eq_true hx'.2,false,by simpa [z1d] using hx'.1⟩
theorem ClosedChain.interior_count {V:Type*} {G:SimpleGraph V} {Q:Set V} {c:List V}
   (h:ClosedChain G Q c) (hn:c.Nodup) {A:List ℕ} (hA:y8 Q c A) :
   ((zb Q true c).filter (fun x => x∉Q)).length=A.length:=by
 classical
 have hl:=zed Q true c h.nonempty h.ends.2
 have hh:=(zb Q true c).length_eq_countP_add_countP (fun x => decide (x∈Q))
 rw [h.zcb hn] at hh
 simp only [Bool.not_eq_true,decide_eq_false_iff_not,List.countP_eq_length_filter] at hh
 have hc:=hA.count.1
 simp only [ite_true] at hl
 omega
theorem ClosedChain.chosen_count {V:Type*} {G:SimpleGraph V} {Q:Set V} {c:List V}
   (h:ClosedChain G Q c) (hn:c.Nodup) {A:List ℕ} (hA:y8 Q c A)
   (ha:∀ a∈A,2≤ a) (hc1:c.length≠1) :
   2*c.countP (fun x => decide (x∈Q))≤(z22 Q c).length+A.sum:=by
 classical
 obtain ⟨hc,hl,_⟩:=hA.count
 have hs:=z58 A 2 ha
 have hAp: 1≤ A.length:=by
   by_contra! hh
   have he:A = []:=List.length_eq_zero_iff.mp (by omega)
   simp only [he,List.length_nil,List.sum_nil] at hl
   exact hc1 (by omega)
 by_cases h4:c.length=4
 · obtain ⟨u,a,b,v,rfl,hu,hv,ha,hb⟩:=h.four h4
   simp only [z22,List.length_cons,List.length_nil,Nat.reduceAdd,ite_true,
     List.tail_cons,List.dropLast_cons_cons,List.dropLast_singleton]
   simp only [List.length_cons,List.length_nil] at hl
   omega
 · have hi:=h.interior_count hn hA
   simp only [z22,if_neg h4,hi]
   by_cases hA1:A.length=1
   · have hs3: 3≤ A.sum:=by omega
     omega
   · omega
theorem y0.orient_rep_chain {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q) (f:List V → Bool) {c:List V} (hc:c∈P.chains)
   {x:V} (hx:x∈zb Q true (z1d (f c) c)):x∈(P.orient f).reps:=by
 apply (P.orient f).z9d (show z1d (f c) c∈(P.orient f).chains from ?_) hx
 rw [y0.orient_chains]
 exact List.mem_map.mpr ⟨c,hc,rfl⟩
theorem y0.chosen_rep {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q) {c:List V} (hc:c∈P.chains) {x:V}
   (hx:x∈z22 Q c):x∉Q ∧ ∃ f:List V → Bool,x∈(P.orient f).reps:=by
 obtain ⟨hxQ,b,hb⟩:=(P.z11 hc).chosen_rep hx
 exact ⟨hxQ,fun _ => b,P.orient_rep_chain _ hc hb⟩
theorem y0.chosen_pair {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q) {c c' :List V} (hc:c∈P.chains) (hc' :c' ∈ P.chains)
   {x y:V} (hx:x∈z22 Q c) (hy:y∈z22 Q c') (hxy:x≠y) :
   (∃ f:List V → Bool,x∈(P.orient f).reps∧y∈(P.orient f).reps) ∨
   (∃ u v,c = [u,x,y,v])∨(∃ u v,c = [u,y,x,v]):=by
 classical
 by_cases hcc:c=c'
 · subst c'
   by_cases h4:c.length=4
   · obtain ⟨u,a,b,v,rfl,hu,hv,ha,hb⟩:=(P.z11 hc).four h4
     have hx' :x=a∨x=b:=by simpa [z22] using hx
     have hy' :y=a∨y=b:=by simpa [z22] using hy
     rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
     · exact (hxy rfl).elim
     · exact Or.inr (Or.inl ⟨u,v,rfl⟩)
     · exact Or.inr (Or.inr ⟨u,v,rfl⟩)
     · exact (hxy rfl).elim
   · have hx' :x∈zb Q true c:=List.mem_of_mem_filter (by
       simpa only [z22,if_neg h4] using hx)
     have hy' :y∈zb Q true c:=List.mem_of_mem_filter (by
       simpa only [z22,if_neg h4] using hy)
     exact Or.inl ⟨fun _ => false,P.orient_rep_chain _ hc (by simpa [z1d] using hx'),
       P.orient_rep_chain _ hc (by simpa [z1d] using hy')⟩
 · obtain ⟨_,b,hb⟩:=(P.z11 hc).chosen_rep hx
   obtain ⟨_,b',hb'⟩:=(P.z11 hc').chosen_rep hy
   let f:List V → Bool:=fun d => if d=c then b else b'
   exact Or.inl ⟨f,P.orient_rep_chain f hc (by simpa [f] using hb),
     P.orient_rep_chain f hc' (by simpa [f,Ne.symm hcc] using hb')⟩
noncomputable def y0.z12b {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q):List V:=(P.chains.map (z22 Q)).flatten
theorem y0.chosen_sublist {V:Type*} {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q):P.z12b.Sublist P.chains.flatten:=by
 suffices hh:∀ C:List (List V),(C.map (z22 Q)).flatten.Sublist C.flatten from hh P.chains
 intro C
 induction C with
 | nil => simp
 | cons c C ih =>
   simpa only [List.map_cons,List.flatten_cons] using (chosenChain_sublist Q c).append ih
theorem y0.chosen_count {V:Type*} [Fintype V] {G:SimpleGraph V} {Q:Set V}
   (P:y0 G Q) (hM:P.z1a = ∅)
   (hA:∃ A,z3 P A ∧ ∀ a∈A,2≤ a) :
   2*Q.ncard≤ P.z12b.length+P.z2:=by
 classical
 obtain ⟨A,⟨D,hD,zc⟩,hAs⟩:=hA
 have hs:D.flatten.sum=P.z2:=by
   rw [zc.sum_eq]
   exact (z3.count ⟨D,hD,zc⟩).1
 have hC1:∀ c∈P.chains,c.length≠1:=by
   intro c hc he
   obtain ⟨x,rfl⟩:=List.length_eq_one_iff.mp he
   have hx:x∈P.z1a:=hc
   rw [hM] at hx
   exact hx
 have hh:∀ (C:List (List V)) (D:List (List ℕ)),List.Forall₂ (y8 Q) C D → 
     (∀ c∈C,c.length≠1) → (∀ a∈D.flatten,2≤ a) → 
     (∀ c∈C,c.Nodup) → (∀ c∈C,ClosedChain G Q c) → 
     2*C.flatten.countP (fun x => decide (x∈Q)) ≤
     (C.map (z22 Q)).flatten.length+D.flatten.sum:=by
   intro C D hD
   induction hD with
   | nil => simp
   | @cons c a C D hca hD ih =>
     intro hC1 hdall hnd hc
     have hb:=(hc c (by simp)).chosen_count (hnd c (by simp)) hca
       (fun n hn => hdall n (List.mem_flatten.mpr ⟨a,by simp,hn⟩)) (hC1 c (by simp))
     have hi:=ih (fun c hc => hC1 c (by simp [hc]))
       (fun n hn => hdall n (List.mem_flatten.mpr (by
         obtain ⟨a,ha,hna⟩:=List.mem_flatten.mp hn
         exact ⟨a,by simp [ha],hna⟩)))
       (fun c hc => hnd c (by simp [hc])) (fun c hc' => hc c (by simp [hc']))
     simp only [List.flatten_cons,List.countP_append,List.map_cons,List.length_append,
       List.sum_append]
     omega
 have hh' :=hh P.chains D hD hC1 (fun a ha => hAs a (zc.mem_iff.mp ha))
   (List.nodup_flatten.mp P.nodup).1 (fun c hc => P.z11 hc)
 simpa only [P.z93,hs,y0.z12b] using hh'
theorem z5.symm {V:Type*} {G:SimpleGraph V} {X:Set V} {x y:V} {d:ℕ}
   (h:z5 G X x y d):z5 G X y x d:=by
 obtain ⟨hx,hy,hxy,p,hp,hl,hs⟩:=h
 refine ⟨hy,hx,Ne.symm hxy,p.reverse,hp.reverse,by simpa using hl,?_⟩
 intro v hv hvX
 exact (hs v (by simpa using hv) hvX).symm
namespace LargeSystem
variable {V:Type*} [Fintype V] {G:SimpleGraph V} {Q:Set V} {k:ℕ}
 {P:y0 G Q} (H:LargeSystem G Q k P)
include H
theorem exclude_two_full (hL:P.z2+Q.ncard=k)
   (hA:∃ A,z3 P A ∧ ∀ a∈A,2≤ a) (hM:P.z1a = ∅):False:=by
 classical
 have hv:P.ze=Q.ncard:=by
   have hh:=P.incident_add_missing
   simpa only [hM,Set.ncard_empty,Nat.add_zero] using hh
 have hm: 2*P.z4≤ P.z2:=by
   obtain ⟨A,hA,ha⟩:=hA
   have hh:=z58 A 2 ha
   simpa only [hA.count.1,hA.count.2.1] using hh
 have hk2: 2*Q.ncard≤ k:=by have:=P.z38; omega
 let F:=P.z12b.toFinset
 have hmem:∀ x∈F,∃ c∈P.chains,x∈z22 Q c:=by
   intro x hx
   obtain ⟨l,hl,hx⟩:=List.mem_flatten.mp (List.mem_toFinset.mp hx)
   obtain ⟨c,hc,rfl⟩:=List.mem_map.mp hl
   exact ⟨c,hc,hx⟩
 have hFX:∀ x∈F,x∈P.vertices:=by
   intro x hx
   exact P.chosen_sublist.subset (List.mem_toFinset.mp hx)
 have hno:∀ x∈F,∀ y∈F,x≠y → ∀ d,1≤ d → d≤6 → 
     ¬ z5 G P.vertices x y d:=by
   intro x hx y hy hxy d hd hd6 hp
   obtain ⟨c,hc,hxc⟩:=hmem x hx
   obtain ⟨c',hc',hyc⟩:=hmem y hy
   have hxQ:=(P.chosen_rep hc hxc).1
   rcases P.chosen_pair hc hc' hxc hyc hxy with ⟨f,hxr,hyr⟩ | ⟨u,v,he⟩ | ⟨u,v,he⟩
   · exact (H.orient f).no_short_interior hxr hyr hxQ d hd hd6 (by simpa using hp)
   · exact H.no_short_step hc [u] [v] (by simpa using he) d hd hd6 hp
   · exact H.no_short_step hc [u] [v] (by simpa using he) d hd hd6 hp.symm
 have hw:∀ x∈F,3≤ independence G (z1 G P.vertices x 2):=by
   intro x hx
   obtain ⟨c,hc,hxc⟩:=hmem x hx
   obtain ⟨_,f,hxr⟩:=P.chosen_rep hc hxc
   simpa using (H.orient f).second_triple hk2 hxr
 have z179:=packing_balls F (fun _ => 2) (fun _ => 3) hFX
   (fun x hx y hy hxy d hd hd6 => hno x hx y hy hxy d hd (by omega)) hw
 have hc:F.card=P.z12b.length:=List.toFinset_card_of_nodup (P.chosen_sublist.nodup P.nodup)
 have hp: 3*P.z12b.length≤ k:=by
   simpa only [Finset.sum_const,smul_eq_mul,hc,Nat.mul_comm] using z179.trans H.independent
 have hn:=P.chosen_count hM hA
 have ht:=H.nine
 have hk:=H.k_le
 omega
theorem contradiction:False:=by
 obtain ⟨x,hx,y,hy,d,hd,hd6,hp⟩:=H.short
 obtain ⟨hL,hA,hc⟩:=H.parameter hx hy (by omega) hd6 hp
 rcases hc with ⟨rfl,hv,_⟩ | ⟨rfl,hv,_⟩ | ⟨rfl,ht,hk,he,hv,_⟩
 · by_cases hM:P.z1a.Nonempty
   · exact H.exclude_two_missing hL hA hv hM
   · exact H.exclude_two_full hL hA (Set.not_nonempty_iff_eq_empty.mp hM)
 · exact H.exclude_three hL hA hv
 · exact H.exclude_five ht hk hv
end LargeSystem
end CycleClique
namespace CycleClique
open scoped SimpleGraph
structure FiniteHyp {V:Type*} [Fintype V] (G:SimpleGraph V) (k t:ℕ):Prop where
 hk: 5≤ k
 ht: 3≤ t
 htk:t≤ k
 hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G
 z20:G.cliqueNum≤ t
 hα:G.indepNum≤ k
 hexp:∀ I:Set V,G.IsIndepSet I → I.Nonempty → 
   k*I.ncard+1≤(z0 G I).ncard
namespace FiniteHyp
variable {V:Type*} [Fintype V] {G:SimpleGraph V} {k t:ℕ} (H:FiniteHyp G k t)
include H
theorem degree (x:V):k+1≤(z0 G {x}).ncard:=by
 simpa using H.hexp {x} (by intro a ha b hb hab; simp_all) (Set.singleton_nonempty x)
theorem z187 {X Z:Set V} {x:V} (hx:x∈X) (hZ:Z⊆X)
   (hxZ:x∉Z) (z54:∀ z∈Z,¬ G.Adj x z) :
   k+1+Z.ncard≤ X.ncard+(z1 G X x 0).ncard:=by
 have hs:z0 G {x}⊆z1 G X x 0∪(X \ Z):=by
   rintro v (hv | ⟨u,hu,huv⟩)
   · have he:v=x:=hv
     subst v
     exact Or.inr ⟨hx,hxZ⟩
   · have he:u=x:=hu
     subst u
     by_cases hvX:v∈X
     · exact Or.inr ⟨hvX,fun hvZ => z54 v hvZ huv⟩
     · exact Or.inl ⟨huv,hvX⟩
 have hc:=Set.ncard_le_ncard hs
 have hu:=Set.ncard_union_le (z1 G X x 0) (X \ Z)
 have hd:=Set.ncard_sdiff_add_ncard_of_subset hZ
 have hh:=H.degree x
 omega
theorem z186 {X:Set V} {x:V} (hx:x∈X)
   (hb:t≤(z1 G X x 0).ncard) :
   2≤ independence G (z1 G X x 0):=by
 by_contra hn
 have hC:=zf (G:=G) (S:=z1 G X x 0) (by omega)
 have hCx:G.IsClique (insert x (z1 G X x 0)):=by
   intro u hu v hv huv
   rcases hu with rfl | hu <;> rcases hv with rfl | hv
   · exact (huv rfl).elim
   · exact hv.1
   · exact hu.1.symm
   · exact hC hu hv huv
 have hc:=(za hCx).trans H.z20
 rw [Set.ncard_insert_of_notMem (show x∉z1 G X x 0 from
   fun hh => hh.2 hx)] at hc
 omega
theorem z185 {X Z:Set V} {x:V} {r u:ℕ}
   (hu: 1≤ u) (z132:u≤ independence G (z1 G X x r))
   (hZ:Z⊆X) (z54:∀ v∈z1 G X x r,∀ z∈Z,¬ G.Adj v z) :
   k*u+1+Z.ncard≤ X.ncard+(z1 G X x (r+1)).ncard:=by
 obtain ⟨I,hIs,hI,hIc⟩:=z6 G (z1 G X x r)
 have hIn:I.Nonempty:=(Set.ncard_pos).mp (by omega)
 have he:=H.hexp I hI hIn
 have hb:=z24 hIs hZ (fun v hv => z54 v (hIs hv))
 have hm:=Nat.mul_le_mul_left k (show u≤ I.ncard by omega)
 omega
theorem z1be {X:Set V} {x:V} {r:ℕ}
   (hb:t < (z1 G X x r).ncard) :
   2≤ independence G (z1 G X x r):=by
 by_contra hn
 have hc:=(za (zf
   (G:=G) (S:=z1 G X x r) (by omega))).trans H.z20
 omega
theorem z1ab {X:Set V} {x:V} {r:ℕ}
   (hb:max k (2*t) < (z1 G X x r).ncard) :
   3≤ independence G (z1 G X x r) :=
 z121 H.hk (by have:=H.ht; omega) H.hcycle H.z20 _ hb
theorem z173 {X Z:Set V} {x:V} {r:ℕ}
   (hx:x∈X) (hZ:Z⊆X) (hxZ:x∉Z)
   (hb:t≤(z1 G X x r).ncard)
   (hnum:X.ncard+t≤ k+1+Z.ncard)
   (z54:∀ v∈z1 G X x r,∀ z∈Z,¬ G.Adj v z) :
   2≤ independence G (z1 G X x (r+1)):=by
 by_contra hn
 have hC:=zf
   (G:=G) (S:=z1 G X x (r+1)) (by omega)
 have hc:=(za hC).trans H.z20
 have hsub:=z55 G X x r
 have hadj:∀ v∈z1 G X x r,G.Adj x v:=by
   intro v hv
   by_contra hneg
   have hZX:insert x Z⊆X:=Set.insert_subset hx hZ
   have hm:∀ u∈({v}:Set V),∀ z∈insert x Z,¬ G.Adj u z:=by
     intro u hu z hz huz
     have he:u=v:=hu
     subst u
     rcases hz with rfl | hz
     · exact hneg huz.symm
     · exact z54 v hv z hz huz
   have hh:=z24 (Set.singleton_subset_iff.mpr hv) hZX hm
   rw [Set.ncard_insert_of_notMem hxZ] at hh
   have hd:=H.degree v
   change (z0 G {v}).ncard+(Z.ncard+1) ≤
     X.ncard+(z1 G X x (r+1)).ncard at hh
   omega
 have hbig:G.IsClique (insert x (z1 G X x r)):=by
   intro u hu v hv huv
   rcases hu with rfl | hu <;> rcases hv with rfl | hv
   · exact (huv rfl).elim
   · exact hadj v hv
   · exact (hadj u hu).symm
   · exact hC (hsub hu) (hsub hv) huv
 have z1fa:=(za hbig).trans H.z20
 rw [Set.ncard_insert_of_notMem (show x∉z1 G X x r from
   fun hh => z1c G X x r hh hx)] at z1fa
 omega
end FiniteHyp
def labelAdj (E:List (ℕ × ℕ)) (a b:ℕ):Prop:=(a,b)∈E∨(b,a)∈E
instance (E:List (ℕ × ℕ)) (a b:ℕ):Decidable (labelAdj E a b):=by
 unfold labelAdj
 infer_instance
def z2b (n:ℕ) (q:Finset ℕ) (E:List (ℕ × ℕ)) (C:List (List ℕ)):Prop :=
 C.flatten.Nodup∧(∀ i∈C.flatten,i < n) ∧
 (∀ c∈C,c ≠ []∧c.IsChain (labelAdj E) ∧
   c.IsChain (fun a b => a∉q∨b∉q) ∧
   (∀ x∈c.head?,x∈q)∧(∀ x∈c.getLast?,x∈q)) ∧
 ∀ i∈q,i∈C.flatten
instance (n:ℕ) (q:Finset ℕ) (E:List (ℕ × ℕ)) (C:List (List ℕ)) :
   Decidable (z2b n q E C):=by
 unfold z2b
 infer_instance
structure LabelState {V:Type*} (G:SimpleGraph V) (Q:Set V)
   (n:ℕ) (q:Finset ℕ) (E:List (ℕ × ℕ)) where
 f:ℕ → V
 inj:Set.InjOn f (Set.Iio n)
 qb:∀ i∈q,i < n
 qimage:Q=f '' (↑q:Set ℕ)
 eb:∀ a b,(a,b)∈E → a < n∧b < n
 edges:∀ a b,labelAdj E a b → G.Adj (f a) (f b)
namespace LabelState
variable {V:Type*} {G:SimpleGraph V} {Q:Set V}
 {n:ℕ} {q:Finset ℕ} {E:List (ℕ × ℕ)} (S:LabelState G Q n q E)
def vertices:Set V:=S.f '' Set.Iio n
theorem z12 {i:ℕ} (hi:i < n):S.f i∈S.vertices:=⟨i,hi,rfl⟩
theorem ze3:S.vertices.ncard=n:=by
 rw [vertices,Set.InjOn.ncard_image S.inj,Set.ncard_Iio_nat]
include S in
theorem zda:Q.ncard=q.card:=by
 rw [S.qimage,Set.InjOn.ncard_image (S.inj.mono S.qb),Set.ncard_coe_finset]
theorem zfa {i:ℕ} (hi:i < n):S.f i∈Q↔i∈q:=by
 constructor
 · intro hx
   have him:S.f i∈S.f '' (↑q:Set ℕ):=S.qimage ▸ hx
   obtain ⟨j,hj,he⟩:=him
   have hji:=S.inj (S.qb j hj) hi he
   simpa only [hji,Finset.mem_coe] using hj
 · intro h
   exact Eq.mp (congrArg (fun A:Set V => S.f i∈A) S.qimage.symm)
     (show S.f i∈S.f '' (↑q:Set ℕ) from ⟨i,h,rfl⟩)
noncomputable def system {C:List (List ℕ)} (h:z2b n q E C):y0 G Q:=by
 classical
 refine {
   chains:=C.map (List.map S.f)
   nonempty:= ?_
   nodup:= ?_
   edges:= ?_
   positive:= ?_
   ends:= ?_
   cover:= ?_ }
 · intro c hc
   obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hc
   simpa using (h.2.2.1 a ha).1
 · rw [← List.map_flatten]
   exact h.1.map_on (fun a ha b hb he => S.inj (h.2.1 a ha) (h.2.1 b hb) he)
 · intro c hc
   obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hc
   apply (List.isChain_map S.f).mpr
   exact (h.2.2.1 a ha).2.1.imp (fun {u v} huv => S.edges u v huv)
 · intro c hc
   obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hc
   apply (List.isChain_map S.f).mpr
   apply (h.2.2.1 a ha).2.2.1.imp_of_mem_imp
   intro u v hu hv huv
   have hub:=h.2.1 u (List.mem_flatten.mpr ⟨a,ha,hu⟩)
   have hvb:=h.2.1 v (List.mem_flatten.mpr ⟨a,ha,hv⟩)
   simpa only [S.zfa hub,S.zfa hvb] using huv
 · intro c hc
   obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hc
   constructor
   · intro x hx
     simp only [List.head?_map,Option.mem_map] at hx
     obtain ⟨i,hi,rfl⟩:=hx
     exact (S.zfa (S.qb i ((h.2.2.1 a ha).2.2.2.1 i hi))).mpr
       ((h.2.2.1 a ha).2.2.2.1 i hi)
   · intro x hx
     simp only [List.getLast?_map,Option.mem_map] at hx
     obtain ⟨i,hi,rfl⟩:=hx
     exact (S.zfa (S.qb i ((h.2.2.1 a ha).2.2.2.2 i hi))).mpr
       ((h.2.2.1 a ha).2.2.2.2 i hi)
 · intro x hx
   rw [S.qimage] at hx
   obtain ⟨i,hi,rfl⟩:=hx
   rw [← List.map_flatten]
   exact List.mem_map.mpr ⟨i,h.2.2.2 i hi,rfl⟩
@[simp] theorem system_chains {C:List (List ℕ)} (h:z2b n q E C) :
   (S.system h).chains=C.map (List.map S.f):=rfl
theorem z199 [Fintype V] {C:List (List ℕ)} (h:z2b n q E C) :
   (S.system h).z2=C.flatten.length - q.card:=by
 simp only [y0.z2,S.system_chains,← List.map_flatten,List.length_map,S.zda]
theorem z1aa [Fintype V] {C:List (List ℕ)} (h:z2b n q E C) :
   (S.system h).z4=q.card - C.length:=by
 simp only [y0.z4,S.system_chains,List.length_map,S.zda]
theorem z183 [Fintype V] {C:List (List ℕ)} (h:z2b n q E C) :
   (S.system h).ze=q.card - (C.filter (fun c => c.length=1)).length:=by
 classical
 simp only [y0.ze,y0.z13,S.system_chains,List.filter_map,
   Function.comp_def,List.length_map,S.zda]
end LabelState
end CycleClique
namespace CycleClique
open scoped SimpleGraph
def pathEdges:List ℕ → List (ℕ × ℕ)
 | a ::b ::l => (a,b) ::pathEdges (b ::l)
 | _ => []
def pathLabels (n i j d:ℕ):List ℕ:=i ::(List.range' n d ++ [j])
def augmentedEdges (n:ℕ) (E:List (ℕ × ℕ)) (i j d:ℕ):List (ℕ × ℕ) :=
 E ++ pathEdges (pathLabels n i j d)
theorem z147 {L:List ℕ} {a b:ℕ} (hab:(a,b)∈pathEdges L) :
   a∈L∧b∈L:=by
 induction L using List.twoStepInduction with
 | nil => simp [pathEdges] at hab
 | singleton x => simp [pathEdges] at hab
 | cons_cons x y L ih₀ ih =>
   simp only [pathEdges,List.mem_cons] at hab
   rcases hab with he | hab
   · obtain ⟨rfl,rfl⟩:=Prod.mk.inj he
     simp
   · have hh:=ih y hab
     exact ⟨List.mem_cons_of_mem _ hh.1,List.mem_cons_of_mem _ hh.2⟩
theorem z108 {n i j d a:ℕ} (hi:i < n) (hj:j < n)
   (ha:a∈pathLabels n i j d):a < n+d:=by
 simp only [pathLabels,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at ha
 rcases ha with rfl | ha | rfl
 · omega
 · have hh:=List.mem_range'.mp ha
   obtain ⟨l,hl,he⟩:=hh
   simp only [Nat.one_mul] at he
   omega
 · omega
theorem zca {V:Type*} {G:SimpleGraph V} (f:ℕ → V)
   {L:List ℕ} (h:(L.map f).IsChain G.Adj) {a b:ℕ}
   (hab:(a,b)∈pathEdges L):G.Adj (f a) (f b):=by
 induction L using List.twoStepInduction with
 | nil => simp [pathEdges] at hab
 | singleton x => simp [pathEdges] at hab
 | cons_cons x y L ih₀ ih =>
   simp only [pathEdges,List.mem_cons] at hab
   rcases hab with he | hab
   · have he' :=Prod.mk.inj he
     obtain ⟨rfl,rfl⟩:=he'
     exact List.isChain_cons_cons.mp h |>.1
   · exact ih y (List.IsChain.tail h) hab
namespace LabelState
variable {V:Type*} {G:SimpleGraph V} {Q:Set V}
 {n:ℕ} {q:Finset ℕ} {E:List (ℕ × ℕ)} (S:LabelState G Q n q E)
def z26 (I:List V) (i:ℕ):V :=
 if i < n then S.f i else I[i-n]?.getD (S.f 0)
theorem z4e (I:List V) {i:ℕ} (hi:i < n) :
   S.z26 I i=S.f i:=by simp [z26,hi]
theorem z4d (I:List V) {i:ℕ} (hi:i < I.length) :
   S.z26 I (n+i)=I[i]:=by
 simp only [z26,Nat.not_lt.mpr (Nat.le_add_right n i),ite_false,
   Nat.add_sub_cancel_left,List.getElem?_eq_getElem hi,Option.getD_some]
theorem z13d {I:List V} (hI:I.Nodup)
   (hout:∀ v∈I,v∉S.vertices) :
   Set.InjOn (S.z26 I) (Set.Iio (n+I.length)):=by
 intro i hi j hj he
 change i < n+I.length at hi
 change j < n+I.length at hj
 by_cases hin:i < n <;> by_cases hjn:j < n
 · rw [S.z4e I hin,S.z4e I hjn] at he
   exact S.inj hin hjn he
 · have hji:j - n < I.length:=by omega
   have hjj:j=n+(j - n):=by omega
   rw [S.z4e I hin,hjj,S.z4d I hji] at he
   exact (hout _ (List.getElem_mem hji) (he ▸ S.z12 hin)).elim
 · have hii:i - n < I.length:=by omega
   have hii' :i=n+(i - n):=by omega
   rw [S.z4e I hjn,hii',S.z4d I hii] at he
   exact (hout _ (List.getElem_mem hii) (he.symm ▸ S.z12 hjn)).elim
 · have hii:i - n < I.length:=by omega
   have hji:j - n < I.length:=by omega
   have hii' :i=n+(i - n):=by omega
   have hjj:j=n+(j - n):=by omega
   have hie:S.z26 I i=I[i-n]:=by
     calc
       _=S.z26 I (n+(i-n)):=congrArg _ hii'
       _=_:=S.z4d I hii
   have hje:S.z26 I j=I[j-n]:=by
     calc
       _=S.z26 I (n+(j-n)):=congrArg _ hjj
       _=_:=S.z4d I hji
   have he' :I[i-n]=I[j-n]:=hie.symm.trans (he.trans hje)
   have hh:=hI.getElem_inj_iff.mp he'
   omega
theorem z114 (I:List V) :
   (List.range' n I.length).map (S.z26 I)=I:=by
 apply List.ext_getElem (by simp)
 intro i hi hi'
 simp only [List.getElem_map,List.getElem_range',Nat.one_mul,S.z4d I hi']
theorem z168 {i j d:ℕ} (hi:i < n) (hj:j < n)
   (hp:z5 G S.vertices (S.f i) (S.f j) d) :
   ∃ T:LabelState G Q (n+d) q (augmentedEdges n E i j d),
     ∀ a,a < n → T.f a=S.f a:=by
 obtain ⟨I,hIl,z130,hIn,hout⟩:=hp.z139
 let g:=S.z26 I
 have hold:∀ a,a < n → g a=S.f a:=fun a ha => S.z4e I ha
 have hmap:(pathLabels n i j d).map g=S.f i ::I ++ [S.f j]:=by
   simp only [pathLabels,List.map_cons,List.map_append,List.map_nil,hold i hi,hold j hj,
     ← hIl,g,S.z114,List.cons_append]
 refine ⟨{
   f:=g
   inj:=by simpa only [← hIl] using S.z13d hIn hout
   qb:=fun a ha => by have:=S.qb a ha; omega
   qimage:= ?_
   eb:= ?_
   edges:= ?_ },hold⟩
 · calc
     Q=S.f '' (↑q:Set ℕ):=S.qimage
     _=g '' (↑q:Set ℕ):=by
       apply Set.image_congr
       intro a ha
       exact (hold a (S.qb a ha)).symm
 · intro a b hab
   rcases List.mem_append.mp hab with hab | hab
   · have hh:=S.eb a b hab
     constructor <;> omega
   · have hh:=z147 hab
     exact ⟨z108 hi hj hh.1,z108 hi hj hh.2⟩
 · intro a b hab
   rcases hab with hab | hab
   · rcases List.mem_append.mp hab with hab | hab
     · obtain ⟨ha,hb⟩:=S.eb a b hab
       rw [hold a ha,hold b hb]
       exact S.edges a b (Or.inl hab)
     · exact zca g (hmap ▸ z130) hab
   · rcases List.mem_append.mp hab with hab | hab
     · obtain ⟨hb,ha⟩:=S.eb b a hab
       rw [hold a ha,hold b hb]
       exact S.edges a b (Or.inr hab)
     · exact (zca g (hmap ▸ z130) hab).symm
end LabelState
def z2a (n k:ℕ) (E:List (ℕ × ℕ)) (L:List ℕ):Prop :=
 L.Nodup∧L.length=k+1∧(∀ i∈L,i < n) ∧
 L.IsChain (labelAdj E) ∧ ∀ x∈L.head?,∀ y∈L.getLast?,labelAdj E y x
instance (n k:ℕ) (E:List (ℕ × ℕ)) (L:List ℕ) :
   Decidable (z2a n k E L):=by
 unfold z2a
 infer_instance
theorem zaf {V:Type*} {G:SimpleGraph V} (L:List V)
   (hl: 3≤ L.length) (hn:L.Nodup) (hc:L.IsChain G.Adj)
   (he:∀ x∈L.head?,∀ y∈L.getLast?,G.Adj y x) :
   SimpleGraph.cycleGraph L.length⊑G:=by
 have hne:L ≠ []:=by intro hh; simp [hh] at hl
 let p:=SimpleGraph.Walk.ofSupport L hne hc
 have hp:p.IsPath:=p.isPath_def.mpr (by simpa [p] using hn)
 have z11e:p.length=L.length - 1:=SimpleGraph.Walk.length_ofSupport _ _
 have hadj:=he (L.head hne) (List.head?_eq_some_head hne)
   (L.getLast hne) (List.getLast?_eq_some_getLast hne)
 have hcycle:(SimpleGraph.Walk.cons hadj p).IsCycle:=by
   apply (p.cons_isCycle_iff hadj).mpr
   refine ⟨hp,?_⟩
   intro hh
   have hh' :=hp.length_eq_one_of_mem_edges (by simpa only [Sym2.eq_swap] using hh)
   omega
 apply (SimpleGraph.cycleGraph_isContained_iff (by omega)).mpr
 refine ⟨_,SimpleGraph.Walk.cons hadj p,hcycle,?_⟩
 rw [SimpleGraph.Walk.length_cons,z11e]
 omega
theorem LabelState.cycle {V:Type*} {G:SimpleGraph V} {Q:Set V}
   {n k:ℕ} {q:Finset ℕ} {E:List (ℕ × ℕ)} (S:LabelState G Q n q E)
   (hk: 2≤ k) {L:List ℕ} (h:z2a n k E L) :
   SimpleGraph.cycleGraph (k+1)⊑G:=by
 have hc:=zaf (L.map S.f) (by simp only [List.length_map,h.2.1]; omega)
   (h.1.map_on (fun a ha b hb hab => S.inj (h.2.2.1 a ha) (h.2.2.1 b hb) hab))
   ((List.isChain_map S.f).mpr (h.2.2.2.1.imp (fun {a b} hab => S.edges a b hab))) (by
     intro x hx y hy
     simp only [List.head?_map,List.getLast?_map,Option.mem_map] at hx hy
     obtain ⟨a,ha,rfl⟩:=hx
     obtain ⟨b,hb,rfl⟩:=hy
     exact S.edges b a (h.2.2.2.2 a ha b hb))
 have hlen:(L.map S.f).length=k+1:=by simp only [List.length_map,h.2.1]
 rw [← hlen]
 exact hc
structure OriginalSystem {V:Type*} [Fintype V] (G:SimpleGraph V) (Q:Set V)
   (k t L e:ℕ) where
 P:y0 G Q
 optimal:P.Optimal k
 clique:G.IsClique Q
 card:Q.ncard=t
 z2:P.z2=L
 edges:P.z4=e
def Improvement (k t L e:ℕ) (C:List (List ℕ)):Prop :=
 let A:=C.flatten.length - t
 let N:=t - C.length
 let v:=t - (C.filter (fun c => c.length=1)).length
 (A < k+1 - t∧(L < A∨(L=A∧N < e))) ∨
 (k+1 - t≤ A∧A≤ k+1 - v)
instance (k t L e:ℕ) (C:List (List ℕ)):Decidable (Improvement k t L e C):=by
 unfold Improvement
 infer_instance
theorem OriginalSystem.impossible {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} {k t L e n:ℕ} {q:Finset ℕ} {E:List (ℕ × ℕ)}
   (H:FiniteHyp G k t) (O:OriginalSystem G Q k t L e)
   (S:LabelState G Q n q E) {C:List (List ℕ)}
   (hC:z2b n q E C) (hc:Improvement k t L e C):False:=by
 let R:=S.system hC
 have hqt:q.card=t:=S.zda.symm.trans O.card
 have hA:R.z2=C.flatten.length - t:=by rw [S.z199 hC,hqt]
 have he:R.z4=t - C.length:=by rw [S.z1aa hC,hqt]
 have hv:R.ze=t - (C.filter (fun c => c.length=1)).length:=by
   rw [S.z183 hC,hqt]
 change (_∧(_∨(_∧_)))∨(_∧_) at hc
 rcases hc with ⟨z131,hbetter | ⟨heq,hfewer⟩⟩ | ⟨hl,hu⟩
 · have hh:=O.optimal.2.1 R (by rw [O.card,hA]; exact z131)
   rw [hA,O.z2] at hh
   omega
 · have hh:=O.optimal.2.2 R (by rw [hA,O.z2]; exact heq.symm)
   rw [he,O.edges] at hh
   omega
 · exact R.z81 (by have:=H.hk; omega) O.clique H.hcycle
     (by rw [O.card]; exact H.htk) (by rw [hA,O.card]; exact hl) (by rw [hA,hv]; exact hu)
theorem z5.z1d2 {V:Type*} {G:SimpleGraph V} {X Y:Set V}
   {x y:V} {d:ℕ} (h:z5 G Y x y d) (hXY:X⊆Y)
   (hx:x∈X) (hy:y∈X):z5 G X x y d:=by
 obtain ⟨_,_,hne,p,hp,hl,hs⟩:=h
 exact ⟨hx,hy,hne,p,hp,hl,fun v hv hvX => hs v hv (hXY hvX)⟩
theorem LabelState.z14a {V:Type*} {G:SimpleGraph V} {Q:Set V}
   {n m:ℕ} {q:Finset ℕ} {E F:List (ℕ × ℕ)}
   (S:LabelState G Q n q E) (T:LabelState G Q m q F)
   (hnm:n≤ m) (he:∀ i,i < n → T.f i=S.f i)
   {i j d:ℕ} (hi:i < n) (hj:j < n)
   (hno:¬ z5 G S.vertices (S.f i) (S.f j) d) :
   ¬ z5 G T.vertices (T.f i) (T.f j) d:=by
 intro hp
 have hsub:S.vertices⊆T.vertices:=by
   rintro v ⟨a,ha,rfl⟩
   exact ⟨a,lt_of_lt_of_le ha hnm,he a ha⟩
 rw [he i hi,he j hj] at hp
 exact hno (hp.z1d2 hsub (S.z12 hi) (S.z12 hj))
abbrev y4:=List (ℕ × ℕ × ℕ)
def matrixEntry (M:y4) (i j d:ℕ):Prop :=
 (i,j,d)∈M∨(j,i,d)∈M
instance (M:y4) (i j d:ℕ):Decidable (matrixEntry M i j d):=by
 unfold matrixEntry
 infer_instance
structure ValidMatrix {V:Type*} {G:SimpleGraph V} {Q:Set V}
   {n:ℕ} {q:Finset ℕ} {E:List (ℕ × ℕ)} (S:LabelState G Q n q E)
   (M:y4):Prop where
 bounds:∀ c∈M,c.1 < n∧c.2.1 < n
 forbidden:∀ c∈M,¬ z5 G S.vertices (S.f c.1) (S.f c.2.1) c.2.2
namespace ValidMatrix
variable {V:Type*} {G:SimpleGraph V} {Q:Set V}
 {n:ℕ} {q:Finset ℕ} {E:List (ℕ × ℕ)} {S:LabelState G Q n q E}
 {M:y4} (hM:ValidMatrix S M)
include hM
theorem z106 {i j d:ℕ} (hm:matrixEntry M i j d) :
   ¬ z5 G S.vertices (S.f i) (S.f j) d:=by
 rcases hm with hm | hm
 · exact hM.forbidden _ hm
 · intro hp
   exact hM.forbidden _ hm hp.symm
theorem extend {m:ℕ} {F:List (ℕ × ℕ)} (T:LabelState G Q m q F)
   (hnm:n≤ m) (he:∀ i,i < n → T.f i=S.f i):ValidMatrix T M:=by
 constructor
 · intro c hc
   exact ⟨lt_of_lt_of_le (hM.bounds c hc).1 hnm,lt_of_lt_of_le (hM.bounds c hc).2 hnm⟩
 · intro c hc
   exact S.z14a T hnm he (hM.bounds c hc).1 (hM.bounds c hc).2
     (hM.forbidden c hc)
theorem insert {i j d:ℕ} (hi:i < n) (hj:j < n)
   (hno:¬ z5 G S.vertices (S.f i) (S.f j) d) :
   ValidMatrix S ((i,j,d) ::M):=by
 constructor
 · intro c hc
   rcases List.mem_cons.mp hc with rfl | hc
   · exact ⟨hi,hj⟩
   · exact hM.bounds c hc
 · intro c hc
   rcases List.mem_cons.mp hc with rfl | hc
   · exact hno
   · exact hM.forbidden c hc
end ValidMatrix
theorem z5.z1a8 {V:Type*} {G:SimpleGraph V} {X:Set V} {x y:V}
   (hx:x∈X) (hy:y∈X) (hxy:G.Adj x y):z5 G X x y 0:=by
 refine ⟨hx,hy,hxy.ne,SimpleGraph.Walk.cons hxy .nil,?_,rfl,?_⟩
 · rw [SimpleGraph.Walk.isPath_def]
   simpa using hxy.ne
 · intro v hv _
   simpa only [SimpleGraph.Walk.support_cons,SimpleGraph.Walk.support_nil,
     List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using hv
def Excluded (n:ℕ) (M:y4) (i lo hi:ℕ) (Z:Finset ℕ):Prop :=
 (∀ j∈Z,j < n∧j≠i) ∧
 ∀ j∈Z,∀ d∈Finset.Icc lo hi,matrixEntry M i j d
instance (n:ℕ) (M:y4) (i lo hi:ℕ) (Z:Finset ℕ) :
   Decidable (Excluded n M i lo hi Z):=by
 unfold Excluded
 infer_instance
namespace LabelState
variable {V:Type*} {G:SimpleGraph V} {Q:Set V}
 {n:ℕ} {q:Finset ℕ} {E:List (ℕ × ℕ)} (S:LabelState G Q n q E)
def z88 (Z:Finset ℕ):Set V:=S.f '' (↑Z:Set ℕ)
theorem zb5 (Z:Finset ℕ) (hZ:∀ j∈Z,j < n) :
   (S.z88 Z).ncard=Z.card:=by
 rw [z88,Set.InjOn.ncard_image (S.inj.mono hZ),Set.ncard_coe_finset]
theorem z99 (Z:Finset ℕ) (hZ:∀ j∈Z,j < n) :
   S.z88 Z⊆S.vertices:=by
 rintro v ⟨j,hj,rfl⟩
 exact S.z12 (hZ j hj)
theorem z11a {M:y4} {i lo hi:ℕ} {Z:Finset ℕ}
   (hib:i < n) (hZ:Excluded n M i lo hi Z):S.f i∉S.z88 Z:=by
 rintro ⟨j,hj,he⟩
 exact (hZ.1 j hj).2 (S.inj (hZ.1 j hj).1 hib he)
theorem z195 {M:y4} (hM:ValidMatrix S M)
   {i:ℕ} {Z:Finset ℕ} (hi:i < n) (hZ:Excluded n M i 0 0 Z) :
   ∀ z∈S.z88 Z,¬ G.Adj (S.f i) z:=by
 rintro z ⟨j,hj,rfl⟩ hij
 exact hM.z106 (hZ.2 j hj 0 (by simp))
   (z5.z1a8 (S.z12 hi) (S.z12 (hZ.1 j hj).1) hij)
theorem z145 {M:y4} (hM:ValidMatrix S M)
   {i r:ℕ} {Z:Finset ℕ} (hi:i < n) (hZ:Excluded n M i 1 (r+1) Z) :
   ∀ v∈z1 G S.vertices (S.f i) r,∀ z∈S.z88 Z,¬ G.Adj v z:=by
 intro v hv z hz
 obtain ⟨j,hj,rfl⟩:=hz
 apply z3f (S.z12 hi) (S.z12 (hZ.1 j hj).1)
   (fun he => (hZ.1 j hj).2 (S.inj (hZ.1 j hj).1 hi he.symm)) _ v hv
 intro d hd hd'
 exact hM.z106 (hZ.2 j hj d (Finset.mem_Icc.mpr ⟨hd,hd'⟩))
end LabelState
inductive ya where
 | zero (Z:Finset ℕ) (b u:ℕ)
 | succ (previous:ya) (Z:Finset ℕ) (b u:ℕ)
 deriving DecidableEq
namespace ya
def radius:ya → ℕ
 | .zero _ _ _ => 0
 | .succ p _ _ _ => p.radius+1
def size:ya → ℕ
 | .zero _ b _ => b
 | .succ _ _ b _ => b
def weight:ya → ℕ
 | .zero _ _ u => u
 | .succ _ _ _ u => u
def Valid (k t n:ℕ) (M:y4) (i:ℕ):ya → Prop
 | .zero Z b u => Excluded n M i 0 0 Z∧0 < b∧n+b≤ k+1+Z.card ∧
     1≤ u∧(u≤1∨(u≤2∧t≤ b))
 | .succ p Z b u => p.Valid k t n M i∧Excluded n M i 1 (p.radius+1) Z ∧
     (b≤ p.size∨n+b≤ k*p.weight+1+Z.card)∧1≤ u ∧
     (u≤ p.weight∨(u≤2∧t < b)∨(u≤3∧max k (2*t) < b) ∨
       (u≤2∧t≤ p.size∧n+t≤ k+1+Z.card))
instance instDecidableValid (k t n:ℕ) (M:y4) (i:ℕ) (B:ya) :
   Decidable (B.Valid k t n M i) :=
 match B with
 | .zero Z b u => by unfold Valid; infer_instance
 | .succ p Z b u => by
   unfold Valid
   exact @instDecidableAnd _ _ (instDecidableValid k t n M i p) inferInstance
theorem sound {V:Type*} [Fintype V] {G:SimpleGraph V} {Q:Set V}
   {k t n:ℕ} {q:Finset ℕ} {E:List (ℕ × ℕ)} (H:FiniteHyp G k t)
   (S:LabelState G Q n q E) {M:y4} (hM:ValidMatrix S M)
   {i:ℕ} (hi:i < n) (B:ya) (h:B.Valid k t n M i) :
   B.size≤(z1 G S.vertices (S.f i) B.radius).ncard ∧
   1≤ B.weight∧B.weight≤ independence G (z1 G S.vertices (S.f i) B.radius):=by
 induction B with
 | zero Z b u =>
   rcases h with ⟨hZ,hb,hn,hu,hw⟩
   have hs:=H.z187 (S.z12 hi) (S.z99 Z (fun j hj => (hZ.1 j hj).1))
     (S.z11a hi hZ) (S.z195 hM hi hZ)
   rw [S.ze3,S.zb5 Z (fun j hj => (hZ.1 j hj).1)] at hs
   have z78:b≤(z1 G S.vertices (S.f i) 0).ncard:=by omega
   refine ⟨z78,hu,?_⟩
   rcases hw with hw | ⟨hw,ht⟩
   · exact hw.trans (z14 ((Set.ncard_pos).mp (show 0 < (z1 G S.vertices (S.f i) 0).ncard by omega)))
   · exact hw.trans (H.z186 (S.z12 hi) (ht.trans z78))
 | succ p Z b u ih =>
   rcases h with ⟨hp,hZ,hb,hu,hw⟩
   obtain ⟨z1bc,hpos,z132⟩:=ih hp
   have hs:=H.z185 hpos z132
     (S.z99 Z (fun j hj => (hZ.1 j hj).1)) (S.z145 hM hi hZ)
   rw [S.ze3,S.zb5 Z (fun j hj => (hZ.1 j hj).1)] at hs
   have hsub:=z55 G S.vertices (S.f i) p.radius
   have z3b:=Set.ncard_le_ncard hsub
   have z78:b≤(z1 G S.vertices (S.f i) (p.radius+1)).ncard:=by
     rcases hb with hb | hb <;> omega
   refine ⟨z78,hu,?_⟩
   change u≤ independence G (z1 G S.vertices (S.f i) (p.radius+1))
   rcases hw with hw | ⟨hu2,ht⟩ | ⟨hu3,ht⟩ | ⟨hu2,ht,hn⟩
   · exact hw.trans (z132.trans (z76 hsub))
   · exact hu2.trans (H.z1be (ht.trans_le z78))
   · exact hu3.trans (H.z1ab (ht.trans_le z78))
   · apply hu2.trans
     apply H.z173 (S.z12 hi)
       (S.z99 Z (fun j hj => (hZ.1 j hj).1)) (S.z11a hi hZ)
       (ht.trans z1bc) _ (S.z145 hM hi hZ)
     simpa only [S.ze3,S.zb5 Z (fun j hj => (hZ.1 j hj).1)] using hn
end ya
inductive yb where
 | singleton (i:ℕ)
 | ball (i:ℕ) (B:ya)
 deriving DecidableEq
namespace yb
def base:yb → ℕ
 | .singleton i | .ball i _ => i
def radiusCode:yb → ℕ
 | .singleton _ => 0
 | .ball _ B => B.radius+1
def weight:yb → ℕ
 | .singleton _ => 1
 | .ball _ B => B.weight
def Valid (k t n:ℕ) (M:y4):yb → Prop
 | .singleton i => i < n
 | .ball i B => i < n∧B.radius≤2∧B.Valid k t n M i
instance (k t n:ℕ) (M:y4) (o:yb) :
   Decidable (o.Valid k t n M):=by
 cases o <;> unfold Valid <;> infer_instance
def Compatible (M:y4) (a b:yb):Prop :=
 a.base≠b.base ∧
 if a.radiusCode+b.radiusCode=0 then matrixEntry M a.base b.base 0
 else ∀ d∈Finset.Icc 1 (a.radiusCode+b.radiusCode),matrixEntry M a.base b.base d
instance (M:y4) (a b:yb):Decidable (Compatible M a b):=by
 unfold Compatible
 infer_instance
def vertices {V:Type*} (G:SimpleGraph V) (X:Set V) (f:ℕ → V):yb → Set V
 | .singleton i => {f i}
 | .ball i B => z1 G X (f i) B.radius
theorem z1cc {V:Type*} [Fintype V] {G:SimpleGraph V} {Q:Set V}
   {k t n:ℕ} {q:Finset ℕ} {E:List (ℕ × ℕ)} (H:FiniteHyp G k t)
   (S:LabelState G Q n q E) {M:y4} (hM:ValidMatrix S M)
   (o:yb) (ho:o.Valid k t n M) :
   o.weight≤ independence G (o.vertices G S.vertices S.f):=by
 cases o with
 | singleton i => exact z14 (Set.singleton_nonempty _)
 | ball i B => exact (B.sound H S hM ho.1 ho.2.2).2.2
theorem z5e {V:Type*} {G:SimpleGraph V} {Q:Set V}
   {k t n:ℕ} {q:Finset ℕ} {E:List (ℕ × ℕ)}
   (S:LabelState G Q n q E) {M:y4} (hM:ValidMatrix S M)
   (a b:yb) (ha:a.Valid k t n M) (hb:b.Valid k t n M)
   (hab:a.Compatible M b) :
   Disjoint (a.vertices G S.vertices S.f) (b.vertices G S.vertices S.f) ∧
   ∀ x∈a.vertices G S.vertices S.f,∀ y∈b.vertices G S.vertices S.f,¬ G.Adj x y:=by
 have ha' :a.base < n:=by cases a with
   | singleton i => exact ha
   | ball i B => exact ha.1
 have hb' :b.base < n:=by cases b with
   | singleton i => exact hb
   | ball i B => exact hb.1
 have hne:S.f a.base≠S.f b.base:=fun he => hab.1 (S.inj ha' hb' he)
 have hm:=hab.2
 cases a with
 | singleton i =>
   cases b with
   | singleton j =>
     simp only [radiusCode,Nat.zero_add,base] at hm
     refine ⟨Set.disjoint_singleton.mpr hne,?_⟩
     rintro x rfl y rfl hij
     exact hM.z106 hm (z5.z1a8 (S.z12 ha') (S.z12 hb') hij)
   | ball j B =>
     simp only [radiusCode,Nat.zero_add,Nat.add_eq_zero_iff,Nat.one_ne_zero,
       and_false,↓reduceIte,base] at hm
     constructor
     · apply Set.disjoint_left.mpr
       rintro x rfl hx
       exact z1c G S.vertices (S.f j) B.radius hx (S.z12 ha')
     · rintro x rfl y hy hxy
       apply z3f (S.z12 hb') (S.z12 ha') hne.symm _ y hy hxy.symm
       intro d hd hd' hp
       exact hM.z106 (hm d (Finset.mem_Icc.mpr ⟨hd,hd'⟩)) hp.symm
 | ball i A =>
   cases b with
   | singleton j =>
     simp only [radiusCode,Nat.add_zero,Nat.add_eq_zero_iff,Nat.one_ne_zero,
       and_false,↓reduceIte,base] at hm
     constructor
     · apply Set.disjoint_left.mpr
       rintro x hx rfl
       exact z1c G S.vertices (S.f i) A.radius hx (S.z12 hb')
     · rintro x hx y rfl hxy
       apply z3f (S.z12 ha') (S.z12 hb') hne _ x hx hxy
       intro d hd hd'
       exact hM.z106 (hm d (Finset.mem_Icc.mpr ⟨hd,hd'⟩))
   | ball j B =>
     change (if A.radius+1+(B.radius+1)=0 then _ else _) at hm
     rw [if_neg (by omega)] at hm
     apply z47 (S.z12 ha') (S.z12 hb') hne
     intro d hd hd'
     exact hM.z106 (hm d (Finset.mem_Icc.mpr ⟨hd,by dsimp [radiusCode]; omega⟩))
end yb
end CycleClique
namespace CycleClique
open scoped SimpleGraph
def PackingValid (k t n:ℕ) (M:y4) (P:Finset yb):Prop :=
 (∀ o∈P,o.Valid k t n M) ∧
 (∀ a∈P,∀ b∈P,a≠b → a.Compatible M b)∧k < ∑ o∈P,o.weight
instance (k t n:ℕ) (M:y4) (P:Finset yb) :
   Decidable (PackingValid k t n M P):=by
 unfold PackingValid
 infer_instance
theorem z156 {V:Type*} [Fintype V] {G:SimpleGraph V} {Q:Set V}
   {k t n:ℕ} {q:Finset ℕ} {E:List (ℕ × ℕ)} (H:FiniteHyp G k t)
   (S:LabelState G Q n q E) {M:y4} (hM:ValidMatrix S M)
   (P:Finset yb) (hP:PackingValid k t n M P):False:=by
 have hs:=zad G (fun o => o.vertices G S.vertices S.f) P
   (fun a ha b hb hab => (a.z5e S hM b (hP.1 a ha) (hP.1 b hb) (hP.2.1 a ha b hb hab)).1)
   (fun a ha b hb hab => (a.z5e S hM b (hP.1 a ha) (hP.1 b hb) (hP.2.1 a ha b hb hab)).2)
 have hw: ∑ o∈P,o.weight ≤ ∑ o∈P,independence G (o.vertices G S.vertices S.f) :=
   Finset.sum_le_sum (fun o ho => o.z1cc H S hM (hP.1 o ho))
 exact (Nat.not_lt_of_ge (hw.trans (hs.trans H.hα))) hP.2.2
inductive y2 where
 | system (C:List (List ℕ))
 | cycle (C:List ℕ)
 | packing (P:Finset yb)
 | edge (i j:ℕ)
 | forbid (i j d:ℕ) (reason next:y2)
 deriving DecidableEq
namespace y2
def Valid (k t n:ℕ) (q:Finset ℕ) (E:List (ℕ × ℕ)) (L e:ℕ)
   (M:y4):y2 → Prop
 | .system C => z2b n q E C∧Improvement k t L e C
 | .cycle C => z2a n k E C
 | .packing P => PackingValid k t n M P
 | .edge i j => i < n∧j < n∧labelAdj E i j∧matrixEntry M i j 0
 | .forbid i j d R N => i < n∧j < n ∧
     R.Valid k t (n+d) q (augmentedEdges n E i j d) L e M ∧
     N.Valid k t n q E L e ((i,j,d)::M)
instance instDecidableValid (k t n:ℕ) (q:Finset ℕ) (E:List (ℕ × ℕ))
   (L e:ℕ) (M:y4) (C:y2) :
   Decidable (C.Valid k t n q E L e M) :=
 match C with
 | .system _ | .cycle _ | .packing _ | .edge _ _ => by unfold Valid; infer_instance
 | .forbid i j d R N => by
   unfold Valid
   exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
     (@instDecidableAnd _ _ (instDecidableValid k t (n+d) q (augmentedEdges n E i j d) L e M R)
       (instDecidableValid k t n q E L e ((i,j,d)::M) N)))
theorem sound {V:Type*} [Fintype V] {G:SimpleGraph V} {Q:Set V}
   {k t L e:ℕ} (H:FiniteHyp G k t) (O:OriginalSystem G Q k t L e)
   (C:y2) {n:ℕ} {q:Finset ℕ} {E:List (ℕ × ℕ)}
   (S:LabelState G Q n q E) {M:y4} (hM:ValidMatrix S M)
   (h:C.Valid k t n q E L e M):False:=by
 induction C generalizing n E M with
 | system C => exact O.impossible H S h.1 h.2
 | cycle C => exact H.hcycle (S.cycle (by have:=H.hk; omega) h)
 | packing P => exact z156 H S hM P h
 | edge i j =>
   exact hM.z106 h.2.2.2 (z5.z1a8 (S.z12 h.1)
     (S.z12 h.2.1) (S.edges i j h.2.2.1))
 | forbid i j d R N ihR ihN =>
   obtain ⟨hi,hj,hR,hN⟩:=h
   have hno:¬ z5 G S.vertices (S.f i) (S.f j) d:=by
     intro hp
     obtain ⟨T,hT⟩:=S.z168 hi hj hp
     exact ihR T (hM.extend T (by omega) hT) hR
   exact ihN S (hM.insert hi hj hno) hN
end y2
open scoped SimpleGraph
def z48 (A:List ℕ):List ℕ:=min A A.reverse
theorem zb8 (A:List ℕ):z48 A=A∨z48 A=A.reverse :=
 min_choice A A.reverse
theorem z128 (A:List ℕ):z48 A≤(z48 A).reverse:=by
 rcases zb8 A with h | h
 · rw [h]
   exact h.symm.trans_le (min_le_right A A.reverse)
 · rw [h,List.reverse_reverse]
   exact h.symm.trans_le (min_le_left A A.reverse)
def z7f (D:List (List ℕ)):List (List ℕ) :=
 (D.map z48).mergeSort (fun a b => decide (a≤ b))
theorem z10e (D:List (List ℕ)):(z7f D).Pairwise (· ≤ ·):=by
 have h:=List.pairwise_mergeSort (le:=fun a b:List ℕ => decide (a≤ b))
   (fun a b c hab hbc => by simpa using le_trans (of_decide_eq_true hab) (of_decide_eq_true hbc))
   (fun a b => by simpa only [Bool.or_eq_true,decide_eq_true_eq] using le_total a b)
   (D.map z48)
 simpa only [z7f,decide_eq_true_eq] using h
theorem z10d (D:List (List ℕ)) :
   ∀ A∈z7f D,A≤ A.reverse:=by
 intro A hA
 obtain ⟨B,hB,rfl⟩:=List.mem_map.mp ((List.mergeSort_perm _ _).mem_iff.mp hA)
 exact z128 B
theorem ClosedChain.reverse {V:Type*} {G:SimpleGraph V} {Q:Set V} {c:List V}
   (hc:ClosedChain G Q c):ClosedChain G Q c.reverse:=by
 refine ⟨by simpa using hc.nonempty,?_,?_,?_⟩
 · exact List.isChain_reverse.mpr (hc.edges.imp (fun _ _ h => h.symm))
 · exact List.isChain_reverse.mpr (hc.positive.imp (fun _ _ h => h.symm))
 · simpa using And.intro hc.ends.2 hc.ends.1
theorem z160 {V:Type*} {G:SimpleGraph V} {Q:Set V}
   {C:List (List V)} {D:List (List ℕ)} (hD:List.Forall₂ (y8 Q) C D)
   (hC:∀ c∈C,ClosedChain G Q c) :
   ∃ C',C'.flatten.Perm C.flatten∧C'.length=C.length ∧
     List.Forall₂ (y8 Q) C' (D.map z48) ∧
     ∀ c∈C',ClosedChain G Q c:=by
 induction hD with
 | nil => exact ⟨[],List.Perm.refl _,rfl,.nil,by simp⟩
 | @cons c A C D hc hD ih =>
   obtain ⟨C',hp,hl,hD',hC'⟩:=ih (fun d hd => hC d (by simp [hd]))
   rcases zb8 A with ha | ha
   · refine ⟨c::C',?_,by simp [hl],?_,?_⟩
     · exact (List.Perm.refl c).append hp
     · simpa only [List.map_cons,ha] using List.Forall₂.cons hc hD'
     · intro d hd
       exact (List.mem_cons.mp hd).elim (fun he => he ▸ hC c (by simp)) (hC' d)
   · refine ⟨c.reverse::C',?_,by simp [hl],?_,?_⟩
     · exact (List.reverse_perm c).append hp
     · simpa only [List.map_cons,ha] using List.Forall₂.cons hc.reverse hD'
     · intro d hd
       exact (List.mem_cons.mp hd).elim (fun he => he ▸ (hC c (by simp)).reverse) (hC' d)
theorem y0.canonical_realization {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) :
   ∃ (R:y0 G Q) (D:List (List ℕ)),
     List.Forall₂ (y8 Q) R.chains D ∧
     D.Pairwise (· ≤ ·)∧(∀ A∈D,A≤ A.reverse) ∧
     R.z2=P.z2∧R.z4=P.z4:=by
 obtain ⟨A,D,hD,zc⟩:=P.z12e
 obtain ⟨C,hCperm,hClen,hCD,hC⟩:=z160 hD (fun c hc => P.z11 hc)
 have z1e8:=List.mergeSort_perm (D.map z48) (fun a b => decide (a≤ b))
 obtain ⟨C',hDC',hCperm'⟩:=List.perm_comp_forall₂ z1e8 hCD.flip
 have hf:C'.flatten.Perm P.chains.flatten:=hCperm'.flatten.trans hCperm
 have hc:∀ c∈C',ClosedChain G Q c:=fun c hc => hC c (hCperm'.mem_iff.mp hc)
 let R:y0 G Q:={
   chains:=C'
   nonempty:=fun c hc' => (hc c hc').nonempty
   nodup:=hf.nodup_iff.mpr P.nodup
   edges:=fun c hc' => (hc c hc').edges
   positive:=fun c hc' => (hc c hc').positive
   ends:=fun c hc' => (hc c hc').ends
   cover:=fun v hv => hf.mem_iff.mpr (P.cover v hv) }
 refine ⟨R,z7f D,hDC'.flip,z10e D,
   z10d D,?_,?_⟩
 · exact congrArg (fun z => z - Q.ncard) hf.length_eq
 · have hl:=hCperm'.length_eq.trans hClen
   exact congrArg (fun z => Q.ncard - z) hl
namespace y0
theorem optimal_of_same {V:Type*} [Fintype V] {G:SimpleGraph V} {Q:Set V}
   {k:ℕ} {P R:y0 G Q} (hP:P.Optimal k)
   (ha:R.z2=P.z2) (he:R.z4=P.z4):R.Optimal k:=by
 unfold Optimal at hP ⊢
 simpa only [ha,he] using hP
end y0
def z1b (A:List ℕ):ℕ:=A.sum+A.length+1
def z73 (b:ℕ):List ℕ → List ℕ
 | [] => [b]
 | a::A => b ::z73 (b+a+1) A
def z21 (b:ℕ):List (List ℕ) → List (List ℕ)
 | [] => []
 | A::D => List.range' b (z1b A) ::z21 (b+z1b A) D
def patternCliqueFrom (b:ℕ):List (List ℕ) → List ℕ
 | [] => []
 | A::D => z73 b A ++ patternCliqueFrom (b+z1b A) D
def patternOrder (D:List (List ℕ)):ℕ:=(D.map z1b).sum
def patternClique (D:List (List ℕ)):Finset ℕ:=(patternCliqueFrom 0 D).toFinset
def patternEdges (D:List (List ℕ)):List (ℕ × ℕ) :=
 (z21 0 D).flatMap pathEdges ++
   ((patternCliqueFrom 0 D).product (patternCliqueFrom 0 D)).filter (fun p => p.1 < p.2)
def patternAmount (D:List (List ℕ)):ℕ:=D.flatten.sum
def z89 (D:List (List ℕ)):ℕ:=D.flatten.length+D.length
def patternEdgeCount (D:List (List ℕ)):ℕ:=D.flatten.length
@[simp] theorem patternOrder_nil:patternOrder []=0:=rfl
@[simp] theorem patternOrder_cons (A:List ℕ) (D:List (List ℕ)) :
   patternOrder (A::D)=z1b A+patternOrder D:=rfl
@[simp] theorem patternChainsFrom_length (b:ℕ) (D:List (List ℕ)) :
   (z21 b D).length=D.length:=by
 induction D generalizing b with
 | nil => rfl
 | cons A D ih => simp [z21,ih]
theorem zfe (b:ℕ) (D:List (List ℕ)) :
   (z21 b D).flatten=List.range' b (patternOrder D):=by
 induction D generalizing b with
 | nil => simp [z21]
 | cons A D ih =>
   simp only [z21,List.flatten_cons,ih,patternOrder_cons]
   simpa only [Nat.one_mul] using (List.range'_append (step:= 1) (s:=b) (m:=z1b A) (n:=patternOrder D))
theorem z14e {b i:ℕ} {A:List ℕ} (hi:i∈z73 b A) :
   b≤ i∧i < b+z1b A:=by
 induction A generalizing b with
 | nil => simp only [z73,List.mem_singleton] at hi; subst i; simp [z1b]
 | cons a A ih =>
   rcases List.mem_cons.mp hi with rfl | hi
   · simp [z1b]
   · obtain ⟨hl,hu⟩:=ih hi
     simp only [z1b,List.sum_cons,List.length_cons] at *
     omega
theorem z10a {b i:ℕ} {D:List (List ℕ)}
   (hi:i∈patternCliqueFrom b D):b≤ i∧i < b+patternOrder D:=by
 induction D generalizing b with
 | nil => simp [patternCliqueFrom] at hi
 | cons A D ih =>
   rcases List.mem_append.mp hi with hi | hi
   · obtain ⟨hl,hu⟩:=z14e hi
     exact ⟨hl,by simp only [patternOrder_cons]; omega⟩
   · obtain ⟨hl,hu⟩:=ih hi
     exact ⟨by omega,by simp only [patternOrder_cons]; omega⟩
theorem z18f {V:Type*} (c:List V) (v:V) :
   (List.range' 0 c.length).map (fun i => c.getD i v)=c:=by
 apply List.ext_getElem (by simp)
 intro i hi hi'
 simp only [List.getElem_map,List.getElem_range',Nat.one_mul,Nat.zero_add]
 exact c.getD_eq_getElem v hi'
theorem y8.z1b7 {V:Type*} {Q:Set V} [DecidablePred (· ∈ Q)] {c:List V} {A:List ℕ}
   (hA:y8 Q c A) (f:ℕ → V) {b:ℕ}
   (hmap:(List.range' b (z1b A)).map f=c) :
   (z73 b A).map f=c.filter (fun v => decide (v∈Q)):=by
 induction hA generalizing b with
 | singleton x hx =>
   simpa [z1b,z73,hx] using hmap
 | step x y I B A hx hI hout zc5 ih =>
   have hh:=congrArg List.head? hmap
   have z200:f b=x:=by
     simpa only [z1b,List.sum_cons,List.length_cons,List.range'_succ,
       List.map_cons,List.head?_cons,Option.some.injEq] using hh
   have hd:=congrArg (List.drop (I.length+1)) hmap
   rw [← List.map_drop,List.drop_range'] at hd
   have hlen:z1b (I.length::A) - (I.length+1)=z1b A:=by
     simp only [z1b,List.sum_cons,List.length_cons]
     omega
   simp only [Nat.mul_one,hlen,List.drop_succ_cons,List.drop_left] at hd
   have z1d0:(List.range' (b+I.length+1) (z1b A)).map f=y::B:=by
     simpa only [Nat.add_assoc] using hd
   have z1ce:I.filter (fun v => decide (v∈Q)) = []:=by
     apply List.filter_eq_nil_iff.mpr
     simpa using hout
   rw [z73,List.map_cons,z200,ih z1d0]
   conv_rhs => rw [List.filter_cons]
   simp only [hx,decide_true,↓reduceIte,List.filter_append,z1ce,List.nil_append]
theorem z192 {V:Type*} {Q:Set V} {C:List (List V)} {D:List (List ℕ)}
   (h:List.Forall₂ (y8 Q) C D):C.flatten.length=patternOrder D:=by
 induction h with
 | nil => rfl
 | @cons c A C D hc h ih =>
   simp only [List.flatten_cons,List.length_append,patternOrder_cons,←ih]
   exact congrArg (· + C.flatten.length) hc.count.2.1
theorem z193 {V:Type*} {Q:Set V} [DecidablePred (· ∈ Q)] {C:List (List V)} {D:List (List ℕ)}
   (h:List.Forall₂ (y8 Q) C D) (f:ℕ → V) {b:ℕ}
   (hmap:(List.range' b (patternOrder D)).map f=C.flatten) :
   (z21 b D).map (List.map f)=C ∧
   (patternCliqueFrom b D).map f=C.flatten.filter (fun v => decide (v∈Q)):=by
 induction h generalizing b with
 | nil => simp [z21,patternCliqueFrom]
 | @cons c A C D hc h ih =>
   have z1f1:(List.range' b (z1b A)).map f ++
       (List.range' (b+z1b A) (patternOrder D)).map f=c ++ C.flatten:=by
     rw [←List.map_append]
     rw [show List.range' b (z1b A) ++ List.range' (b+z1b A) (patternOrder D) =
       List.range' b ((z1b A)+(patternOrder D)) by simp]
     exact hmap
   obtain ⟨za6,hrest⟩:=List.append_inj z1f1 (by simpa [z1b] using hc.count.2.1.symm)
   obtain ⟨hshape,z20⟩:=ih hrest
   constructor
   · simp only [z21,List.map_cons,za6,hshape]
   · simp only [patternCliqueFrom,List.map_append,hc.z1b7 f za6,z20,
       List.flatten_cons,List.filter_append]
noncomputable def y0.labelState {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q) (hQ:G.IsClique Q)
   {D:List (List ℕ)} (hD:List.Forall₂ (y8 Q) P.chains D) (v:V) :
   LabelState G Q (patternOrder D) (patternClique D) (patternEdges D):=by
 classical
 let f:ℕ → V:=fun i => P.chains.flatten.getD i v
 have hlen:=z192 hD
 have hmap:(List.range' 0 (patternOrder D)).map f=P.chains.flatten:=by
   rw [←hlen]
   exact z18f _ _
 obtain ⟨hshape,z20⟩:=z193 hD f hmap
 have hq:Q=f '' (↑(patternClique D):Set ℕ):=by
   ext x
   constructor
   · intro hx
     have hm:x∈(patternCliqueFrom 0 D).map f:=by
       rw [z20]
       exact List.mem_filter.mpr ⟨P.cover x hx,by simpa using hx⟩
     obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hm
     exact ⟨i,List.mem_toFinset.mpr hi,rfl⟩
   · rintro ⟨i,hi,rfl⟩
     have hm:f i∈(patternCliqueFrom 0 D).map f :=
       List.mem_map.mpr ⟨i,List.mem_toFinset.mp hi,rfl⟩
     rw [z20] at hm
     simpa using (List.mem_filter.mp hm).2
 have hinj:Set.InjOn f (Set.Iio (patternOrder D)):=by
   intro i hi j hj he
   have hi' :i < P.chains.flatten.length:=hlen ▸ hi
   have hj' :j < P.chains.flatten.length:=hlen ▸ hj
   apply (P.nodup.getElem_inj_iff (hi:=hi') (hj:=hj')).mp
   simpa [f,List.getElem?_eq_getElem hi',List.getElem?_eq_getElem hj'] using he
 have hqb:∀ i∈patternClique D,i < patternOrder D:=by
   intro i hi
   simpa using (z10a (List.mem_toFinset.mp hi)).2
 have heb:∀ a b,(a,b)∈patternEdges D → a < patternOrder D∧b < patternOrder D:=by
   intro a b hab
   rcases List.mem_append.mp hab with hab | hab
   · obtain ⟨c,hc,hab⟩:=List.mem_flatMap.mp hab
     obtain ⟨ha,hb⟩:=z147 hab
     have hal:a∈(z21 0 D).flatten:=List.mem_flatten.mpr ⟨c,hc,ha⟩
     have hbl:b∈(z21 0 D).flatten:=List.mem_flatten.mpr ⟨c,hc,hb⟩
     rw [zfe] at hal hbl
     simp only [List.mem_range'] at hal hbl
     exact ⟨by omega,by omega⟩
   · obtain ⟨hab,_⟩:=List.mem_filter.mp hab
     obtain ⟨ha,hb⟩:=List.mem_product.mp hab
     exact ⟨hqb a (List.mem_toFinset.mpr ha),hqb b (List.mem_toFinset.mpr hb)⟩
 have hadj:∀ a b,(a,b)∈patternEdges D → G.Adj (f a) (f b):=by
   intro a b hab
   rcases List.mem_append.mp hab with hab | hab
   · obtain ⟨c,hc,hab⟩:=List.mem_flatMap.mp hab
     have hcm:c.map f∈P.chains:=by
       rw [←hshape]
       exact List.mem_map.mpr ⟨c,hc,rfl⟩
     exact zca f (P.edges _ hcm) hab
   · obtain ⟨hab,hlt⟩:=List.mem_filter.mp hab
     obtain ⟨ha,hb⟩:=List.mem_product.mp hab
     have hai:=hqb a (List.mem_toFinset.mpr ha)
     have hbi:=hqb b (List.mem_toFinset.mpr hb)
     apply hQ
     · rw [hq]; exact ⟨a,List.mem_toFinset.mpr ha,rfl⟩
     · rw [hq]; exact ⟨b,List.mem_toFinset.mpr hb,rfl⟩
     · intro he
       have hh:=hinj hai hbi he
       have hh' :a < b:=of_decide_eq_true hlt
       omega
 exact {
   f:=f
   inj:=hinj
   qb:=hqb
   qimage:=hq
   eb:=heb
   edges:=fun a b hab => hab.elim (hadj a b) (fun h => (hadj b a h).symm) }
theorem y0.profile_parameters {V:Type*} [Fintype V]
   {G:SimpleGraph V} {Q:Set V} (P:y0 G Q)
   {D:List (List ℕ)} (hD:List.Forall₂ (y8 Q) P.chains D) :
   z89 D=Q.ncard∧patternAmount D=P.z2 ∧
   patternEdgeCount D=P.z4 ∧ ∀ a∈D.flatten,0 < a:=by
 obtain ⟨ha,he,hpos⟩:=z3.count (show z3 P D.flatten from ⟨D,hD,List.Perm.refl _⟩)
 have hl:=hD.length_eq
 have hle:=P.z4c
 refine ⟨?_,ha,he,hpos⟩
 change D.flatten.length+D.length=Q.ncard
 change D.flatten.length=Q.ncard - P.chains.length at he
 omega
def z68:ℕ → ℕ → List (List ℕ)
 | 0,_ => [[]]
 | l+1,B => [] ::(List.range B).flatMap (fun a =>
     (z68 l (B-(a+1))).map (fun A => (a+1)::A))
theorem z16c {A:List ℕ} {l B:ℕ}
   (hl:A.length≤ l) (hB:A.sum≤ B) (hpos:∀ a∈A,0 < a) :
   A∈z68 l B:=by
 induction l generalizing A B with
 | zero =>
   have ha:A = []:=List.length_eq_zero_iff.mp (by omega)
   simp [ha,z68]
 | succ l ih =>
   cases A with
   | nil => simp [z68]
   | cons a A =>
     have ha: 0 < a:=hpos a (by simp)
     have hs:a+A.sum≤ B:=by simpa using hB
     simp only [z68,List.mem_cons,List.cons_ne_nil,false_or,
       List.mem_flatMap,List.mem_map]
     refine ⟨a-1,List.mem_range.mpr (by omega),A,?_,?_⟩
     · apply ih
       · simpa using hl
       · omega
       · intro b hb; exact hpos b (by simp [hb])
     · congr 1; omega
def y7 (t B:ℕ) (lower:List ℕ):List (List (List ℕ)) :=
 if _ht:t=0 then [[]] else
   (z68 (t-1) B).flatMap (fun A =>
     if A≤ A.reverse∧lower≤ A then
       (y7 (t-(A.length+1)) (B-A.sum) A).map (A::·)
     else [])
termination_by t
decreasing_by omega
@[simp] theorem patternSize_cons (A:List ℕ) (D:List (List ℕ)) :
   z89 (A::D)=A.length+1+z89 D:=by
 simp [z89,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]
@[simp] theorem patternAmount_cons (A:List ℕ) (D:List (List ℕ)) :
   patternAmount (A::D)=A.sum+patternAmount D:=by
 simp [patternAmount]
theorem mem_patternChoices {D:List (List ℕ)} {t B:ℕ} {lower:List ℕ}
   (ht:z89 D=t) (hB:patternAmount D≤ B)
   (hpos:∀ a∈D.flatten,0 < a) (hs:D.Pairwise (· ≤ ·))
   (hn:∀ A∈D,A≤ A.reverse) (hl:∀ A∈D,lower≤ A) :
   D∈y7 t B lower:=by
 induction D generalizing t B lower with
 | nil =>
   have ht' :t=0:=ht.symm
   simp [ht',y7]
 | cons A D ih =>
   have ht' :A.length+1+z89 D=t:=by simpa using ht
   have ht0:t≠0:=by omega
   have haB:A.sum+patternAmount D≤ B:=by simpa using hB
   have hA:A∈z68 (t-1) B:=z16c (by omega) (by omega)
     (fun a ha => hpos a (by simp [ha]))
   rw [y7,dif_neg ht0]
   apply List.mem_flatMap.mpr
   refine ⟨A,hA,?_⟩
   rw [if_pos ⟨hn A (by simp),hl A (by simp)⟩]
   apply List.mem_map.mpr
   refine ⟨D,ih ?_ (by omega) (fun a ha => hpos a (by simp [ha]))
     (List.pairwise_cons.mp hs).2 (fun C hC => hn C (by simp [hC]))
     (List.pairwise_cons.mp hs).1,rfl⟩
   omega
end CycleClique
namespace CycleClique
open scoped SimpleGraph
def zc7:y4 → ℕ → ℕ → ℕ
 | [],_,_ => 0
 | (a,b,d) ::M,i,j =>
     if (a=i∧b=j)∨(a=j∧b=i) then 2^d ||| zc7 M i j
     else zc7 M i j
theorem z17e (M:y4) (i j d:ℕ) :
   (zc7 M i j).testBit d=true↔matrixEntry M i j d:=by
 induction M with
 | nil => simp [zc7,matrixEntry]
 | cons c M ih =>
   rcases c with ⟨a,b,e⟩
   simp only [zc7,matrixEntry,List.mem_cons,Prod.mk.injEq] at *
   split_ifs with he
   · rw [Nat.testBit_lor,Nat.testBit_two_pow]
     simp only [Bool.or_eq_true,decide_eq_true_eq,ih]
     rcases he with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> tauto
   · rw [ih]
     tauto
instance (priority:=high) fastMatrixEntry (M:y4) (i j d:ℕ) :
   Decidable (matrixEntry M i j d):=decidable_of_iff _ (z17e M i j d)
instance (priority:=high) fastExcluded (n:ℕ) (M:y4)
   (i lo hi:ℕ) (Z:Finset ℕ):Decidable (Excluded n M i lo hi Z):=by
 unfold Excluded
 infer_instance
instance (priority:=high) fastBallValid (k t n:ℕ) (M:y4) (i:ℕ)
   (B:ya):Decidable (B.Valid k t n M i) :=
 match B with
 | .zero Z b u => by unfold ya.Valid; infer_instance
 | .succ p Z b u => by
   unfold ya.Valid
   exact @instDecidableAnd _ _ (fastBallValid k t n M i p) inferInstance
instance (priority:=high) fastPackingOptionValid (k t n:ℕ)
   (M:y4) (o:yb):Decidable (o.Valid k t n M):=by
 cases o <;> unfold yb.Valid <;> infer_instance
instance (priority:=high) fastPackingCompatible (M:y4)
   (a b:yb):Decidable (a.Compatible M b):=by
 unfold yb.Compatible
 infer_instance
instance (priority:=high) fastPackingValid (k t n:ℕ)
   (M:y4) (P:Finset yb):Decidable (PackingValid k t n M P):=by
 unfold PackingValid
 infer_instance
instance (priority:=high) fastCertificateValid (k t n:ℕ) (q:Finset ℕ)
   (E:List (ℕ × ℕ)) (L e:ℕ) (M:y4) (C:y2) :
   Decidable (C.Valid k t n q E L e M) :=
 match C with
 | .system _ | .cycle _ | .packing _ | .edge _ _ => by unfold y2.Valid; infer_instance
 | .forbid i j d R N => by
   unfold y2.Valid
   exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
     (@instDecidableAnd _ _ (fastCertificateValid k t (n+d) q (augmentedEdges n E i j d) L e M R)
       (fastCertificateValid k t n q E L e ((i,j,d)::M) N)))
end CycleClique
namespace CycleClique
open scoped SimpleGraph
def y9:List (ℕ × ℕ) → ℕ
 | [] => 0
 | (a,b) ::E => 2^(Nat.pair a b) ||| y9 E
theorem z3e (E:List (ℕ × ℕ)) (a b:ℕ) :
   (y9 E).testBit (Nat.pair a b)=true↔(a,b)∈E:=by
 induction E with
 | nil => simp [y9]
 | cons e E ih =>
   rcases e with ⟨i,j⟩
   simp only [y9,Nat.testBit_lor,Nat.testBit_two_pow,Bool.or_eq_true,
     decide_eq_true_eq,Nat.pair_eq_pair,ih,List.mem_cons,Prod.mk.injEq]
   tauto
instance (priority:=high) globalLabelAdj (E:List (ℕ × ℕ)) (a b:ℕ) :
   Decidable (labelAdj E a b) :=
 decidable_of_iff ((y9 E).testBit (Nat.pair a b)=true ∨
   (y9 E).testBit (Nat.pair b a)=true)
   (by simp only [z3e,labelAdj])
instance (priority:=high) globalLabelValid (n:ℕ) (q:Finset ℕ)
   (E:List (ℕ × ℕ)) (C:List (List ℕ)):Decidable (z2b n q E C):=by
 unfold z2b
 infer_instance
instance (priority:=high) globalCertificateValid (k t n:ℕ) (q:Finset ℕ)
   (E:List (ℕ × ℕ)) (L e:ℕ) (M:y4) (C:y2) :
   Decidable (C.Valid k t n q E L e M) :=
 match C with
 | .system _ | .cycle _ | .packing _ | .edge _ _ => by unfold y2.Valid; infer_instance
 | .forbid i j d R N => by
   unfold y2.Valid
   exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
     (@instDecidableAnd _ _ (globalCertificateValid k t (n+d) q (augmentedEdges n E i j d) L e M R)
       (globalCertificateValid k t n q E L e ((i,j,d)::M) N)))
end CycleClique
namespace CycleClique
open scoped SimpleGraph
def z61 (a b d:ℕ):ℕ :=
 Nat.pair (Nat.pair (a / 32) (b / 32)) (d / 8)*8192 +
   (a % 32)*256+(b % 32)*8+d % 8
theorem z110 {a b d i j e:ℕ} :
   z61 a b d=z61 i j e↔a=i∧b=j∧d=e:=by
 constructor
 · intro h
   unfold z61 at h
   have hbig:Nat.pair (Nat.pair (a / 32) (b / 32)) (d / 8) =
       Nat.pair (Nat.pair (i / 32) (j / 32)) (e / 8):=by omega
   obtain ⟨hp,hd⟩:=Nat.pair_eq_pair.mp hbig
   obtain ⟨ha,hb⟩:=Nat.pair_eq_pair.mp hp
   omega
 · rintro ⟨rfl,rfl,rfl⟩
   rfl
def z51:y4 → ℕ
 | [] => 0
 | (a,b,d) ::M => 2^(z61 a b d) ||| z51 M
theorem z124 (M:y4) (i j d:ℕ) :
   (z51 M).testBit (z61 i j d)=true↔(i,j,d)∈M:=by
 induction M with
 | nil => simp [z51]
 | cons c M ih =>
   rcases c with ⟨a,b,e⟩
   simp only [z51,Nat.testBit_lor,Nat.testBit_two_pow,
     Bool.or_eq_true,decide_eq_true_eq,z110,ih,
     List.mem_cons,Prod.mk.injEq]
   tauto
instance (priority:=high) compactMatrixEntry (M:y4) (i j d:ℕ) :
   Decidable (matrixEntry M i j d) :=
 decidable_of_iff ((z51 M).testBit (z61 i j d)=true ∨
   (z51 M).testBit (z61 j i d)=true)
   (by simp only [z124,matrixEntry])
instance (priority:=high) compactExcluded (n:ℕ) (M:y4)
   (i lo hi:ℕ) (Z:Finset ℕ):Decidable (Excluded n M i lo hi Z):=by
 unfold Excluded
 infer_instance
instance (priority:=high) compactBallValid (k t n:ℕ) (M:y4) (i:ℕ)
   (B:ya):Decidable (B.Valid k t n M i) :=
 match B with
 | .zero Z b u => by unfold ya.Valid; infer_instance
 | .succ p Z b u => by
   unfold ya.Valid
   exact @instDecidableAnd _ _ (compactBallValid k t n M i p) inferInstance
instance (priority:=high) compactPackingOptionValid (k t n:ℕ)
   (M:y4) (o:yb):Decidable (o.Valid k t n M):=by
 cases o <;> unfold yb.Valid <;> infer_instance
instance (priority:=high) compactPackingCompatible (M:y4)
   (a b:yb):Decidable (a.Compatible M b):=by
 unfold yb.Compatible
 infer_instance
instance (priority:=high) compactPackingValid (k t n:ℕ)
   (M:y4) (P:Finset yb):Decidable (PackingValid k t n M P):=by
 unfold PackingValid
 infer_instance
instance (priority:=high) compactMatrixCertificateValid (k t n:ℕ) (q:Finset ℕ)
   (E:List (ℕ × ℕ)) (L e:ℕ) (M:y4) (C:y2) :
   Decidable (C.Valid k t n q E L e M) :=
 match C with
 | .system _ | .cycle _ | .packing _ | .edge _ _ => by unfold y2.Valid; infer_instance
 | .forbid i j d R N => by
   unfold y2.Valid
   exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
     (@instDecidableAnd _ _ (compactMatrixCertificateValid k t (n+d) q (augmentedEdges n E i j d) L e M R)
       (compactMatrixCertificateValid k t n q E L e ((i,j,d)::M) N)))
end CycleClique
namespace CycleClique
open scoped SimpleGraph
instance (priority:=high) compactLabelCycleValid (n k:ℕ)
   (E:List (ℕ × ℕ)) (C:List ℕ):Decidable (z2a n k E C):=by
 unfold z2a
 infer_instance
instance (priority:=high) compactAllCertificateValid (k t n:ℕ) (q:Finset ℕ)
   (E:List (ℕ × ℕ)) (L e:ℕ) (M:y4) (C:y2) :
   Decidable (C.Valid k t n q E L e M) :=
 match C with
 | .system _ | .cycle _ | .packing _ | .edge _ _ => by unfold y2.Valid; infer_instance
 | .forbid i j d R N => by
   unfold y2.Valid
   exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
     (@instDecidableAnd _ _ (compactAllCertificateValid k t (n+d) q (augmentedEdges n E i j d) L e M R)
       (compactAllCertificateValid k t n q E L e ((i,j,d)::M) N)))
end CycleClique
namespace CycleClique
open scoped SimpleGraph
def z2d:List ℕ → Bool
 | [] => true
 | a ::L => !(L.contains a) && z2d L
theorem z53 (L:List ℕ):z2d L=true↔L.Nodup:=by
 induction L with
 | nil => simp [z2d]
 | cons a L ih => simp [z2d,ih]
def z18 (R:ℕ → ℕ → Bool):List ℕ → Bool
 | [] => true
 | [_] => true
 | a ::b ::L => R a b && z18 R (b ::L)
theorem z52 (R:ℕ → ℕ → Bool) (L:List ℕ) :
   z18 R L=true↔L.IsChain (fun a b => R a b=true):=by
 induction L with
 | nil => simp [z18]
 | cons a L ih =>
   cases L with
   | nil => simp [z18]
   | cons b L => simp [z18,List.isChain_cons_cons,ih]
def z77 (n:ℕ) (q:Finset ℕ) (E:List (ℕ × ℕ))
   (C:List (List ℕ)):Bool :=
 z2d C.flatten && C.flatten.all (fun i => decide (i < n)) &&
 C.all (fun c => !c.isEmpty &&
   z18 (fun a b =>
     (y9 E).testBit (Nat.pair a b) ||
     (y9 E).testBit (Nat.pair b a)) c &&
   z18 (fun a b => decide (a∉q) || decide (b∉q)) c &&
   c.head?.all (fun a => decide (a∈q)) &&
   c.getLast?.all (fun a => decide (a∈q))) &&
 decide (∀ i∈q,i∈C.flatten)
theorem z60 (n:ℕ) (q:Finset ℕ) (E:List (ℕ × ℕ))
   (C:List (List ℕ)):z77 n q E C=true↔z2b n q E C:=by
 unfold z2b
 simp only [z77,Bool.and_eq_true,z53,List.all_eq_true,
   decide_eq_true_eq,z52,Bool.or_eq_true,z3e,
   Option.all_eq_true,Bool.not_eq_true',
   List.isEmpty_eq_false_iff,Option.mem_def]
 simp only [and_assoc]
 rfl
instance (priority:=high) compactBooleanLabelValid (n:ℕ) (q:Finset ℕ)
   (E:List (ℕ × ℕ)) (C:List (List ℕ)):Decidable (z2b n q E C) :=
 decidable_of_iff _ (z60 n q E C)
instance (priority:=high) compactBooleanCertificateValid (k t n:ℕ) (q:Finset ℕ)
   (E:List (ℕ × ℕ)) (L e:ℕ) (M:y4) (C:y2) :
   Decidable (C.Valid k t n q E L e M) :=
 match C with
 | .system _ | .cycle _ | .packing _ | .edge _ _ => by unfold y2.Valid; infer_instance
 | .forbid i j d R N => by
   unfold y2.Valid
   exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ inferInstance
     (@instDecidableAnd _ _ (compactBooleanCertificateValid k t (n+d) q (augmentedEdges n E i j d) L e M R)
       (compactBooleanCertificateValid k t n q E L e ((i,j,d)::M) N)))
end CycleClique
namespace CycleClique
open scoped SimpleGraph
def z25 (k t n:ℕ) (q:Finset ℕ) (E:List (ℕ × ℕ)) (L e:ℕ)
   (M:y4):y2 → Bool
 | .system C => z77 n q E C && decide (Improvement k t L e C)
 | .cycle C => decide (z2a n k E C)
 | .packing P => decide (PackingValid k t n M P)
 | .edge i j => decide (i < n) && decide (j < n) &&
     decide (labelAdj E i j) && decide (matrixEntry M i j 0)
 | .forbid i j d R N => decide (i < n) && decide (j < n) &&
     z25 k t (n+d) q (augmentedEdges n E i j d) L e M R &&
     z25 k t n q E L e ((i,j,d)::M) N
theorem zdb (k t n:ℕ) (q:Finset ℕ) (E:List (ℕ × ℕ))
   (L e:ℕ) (M:y4) (C:y2) :
   z25 k t n q E L e M C=true↔C.Valid k t n q E L e M:=by
 induction C generalizing n E M with
 | system C => simp [z25,y2.Valid,z60]
 | cycle C => simp [z25,y2.Valid]
 | packing P => simp [z25,y2.Valid]
 | edge i j => simp [z25,y2.Valid,and_assoc]
 | forbid i j d R N ihR ihN =>
   simp [z25,y2.Valid,ihR,ihN,and_assoc]
instance (priority:=high) fullyCompactCertificateValid (k t n:ℕ) (q:Finset ℕ)
   (E:List (ℕ × ℕ)) (L e:ℕ) (M:y4) (C:y2) :
   Decidable (C.Valid k t n q E L e M) :=
 decidable_of_iff _ (zdb k t n q E L e M C)
end CycleClique
namespace CycleClique
open scoped SimpleGraph
theorem z12f (E F:List (ℕ × ℕ)) :
   y9 (E ++ F)=y9 E ||| y9 F:=by
 induction E with
 | nil => simp [y9]
 | cons ab E ih =>
   rcases ab with ⟨a,b⟩
   simp only [List.cons_append,y9,ih,Nat.lor_assoc]
def zbe (n:ℕ) (q:Finset ℕ) (bits:ℕ)
   (C:List (List ℕ)):Bool :=
 z2d C.flatten && C.flatten.all (fun i => decide (i < n)) &&
 C.all (fun c => !c.isEmpty &&
   z18 (fun a b => bits.testBit (Nat.pair a b) ||
     bits.testBit (Nat.pair b a)) c &&
   z18 (fun a b => decide (a∉q) || decide (b∉q)) c &&
   c.head?.all (fun a => decide (a∈q)) &&
   c.getLast?.all (fun a => decide (a∈q))) &&
 decide (∀ i∈q,i∈C.flatten)
theorem zf2 (n:ℕ) (q:Finset ℕ) (E:List (ℕ × ℕ))
   (C:List (List ℕ)) :
   zbe n q (y9 E) C=true↔z2b n q E C :=
 z60 n q E C
def z7e (n k bits:ℕ) (C:List ℕ):Bool :=
 z2d C && decide (C.length=k+1) &&
 C.all (fun i => decide (i<n)) &&
 z18 (fun a b => bits.testBit (Nat.pair a b) ||
   bits.testBit (Nat.pair b a)) C &&
 C.head?.all (fun a => C.getLast?.all (fun b =>
   bits.testBit (Nat.pair a b) || bits.testBit (Nat.pair b a)))
theorem zf1 (n k:ℕ) (E:List (ℕ × ℕ)) (C:List ℕ) :
   z7e n k (y9 E) C=true↔z2a n k E C:=by
 simp only [z7e,z2a,Bool.and_eq_true,
   z53,decide_eq_true_eq,List.all_eq_true,
   z52,Bool.or_eq_true,z3e,
   Option.all_eq_true,labelAdj,Option.mem_def,and_assoc]
 simp only [or_comm]
 rfl
def z33 (k t n:ℕ) (q:Finset ℕ) (bits:ℕ) (L e:ℕ)
   (M:y4):y2 → Bool
 | .system C => zbe n q bits C && decide (Improvement k t L e C)
 | .cycle C => z7e n k bits C
 | .packing P => decide (PackingValid k t n M P)
 | .edge i j => decide (i < n) && decide (j < n) &&
     (bits.testBit (Nat.pair i j) || bits.testBit (Nat.pair j i)) &&
     decide (matrixEntry M i j 0)
 | .forbid i j d R N => decide (i < n) && decide (j < n) &&
     z33 k t (n+d) q
       (bits ||| y9 (pathEdges (pathLabels n i j d))) L e M R &&
     z33 k t n q bits L e ((i,j,d)::M) N
theorem ze2 (k t n:ℕ) (q:Finset ℕ) (E:List (ℕ × ℕ))
   (L e:ℕ) (M:y4) (C:y2) :
   z33 k t n q (y9 E) L e M C=true ↔
     C.Valid k t n q E L e M:=by
 induction C generalizing n E M with
 | system C => simp [z33,y2.Valid,zf2]
 | cycle C => exact zf1 n k E C
 | packing P => simp [z33,y2.Valid]
 | edge i j =>
   simp [z33,y2.Valid,z3e,labelAdj,and_assoc]
 | forbid i j d R N ihR ihN =>
   simp only [z33,Bool.and_eq_true,decide_eq_true_eq]
   rw [← z12f,← augmentedEdges,ihR,ihN]
   simp only [y2.Valid,and_assoc]
instance (priority:=high) cachedCertificateValid (k t n:ℕ) (q:Finset ℕ)
   (E:List (ℕ × ℕ)) (L e:ℕ) (M:y4) (C:y2) :
   Decidable (C.Valid k t n q E L e M) :=
 decidable_of_iff _ (ze2 k t n q E L e M C)
end CycleClique
namespace CycleClique
open scoped SimpleGraph
instance:Std.Commutative Nat.lor:=⟨Nat.lor_comm⟩
instance:Std.Associative Nat.lor:=⟨Nat.lor_assoc⟩
def zff (q:Finset ℕ):ℕ:=q.fold Nat.lor 0 (fun i => 2^i)
theorem z182 (q:Finset ℕ) (i:ℕ):(zff q).testBit i=true↔i∈q:=by
 induction q using Finset.induction_on with
 | empty => simp [zff]
 | @insert a s ha ih =>
   simp only [zff,Finset.fold_insert ha]
   change ((2^a ||| zff s).testBit i=true)↔_
   simp only [Nat.testBit_lor,Nat.testBit_two_pow,Bool.or_eq_true,
     decide_eq_true_eq,ih,Finset.mem_insert]
   tauto
end CycleClique
namespace CycleClique
open scoped SimpleGraph
theorem qCacheEdgeBits_append (E F:List (ℕ × ℕ)) :
   y9 (E ++ F)=y9 E ||| y9 F:=by
 induction E with
 | nil => simp [y9]
 | cons ab E ih =>
   rcases ab with ⟨a,b⟩
   simp only [List.cons_append,y9,ih,Nat.lor_assoc]
def qCachedLabelValidBool (n:ℕ) (q:Finset ℕ) (bits:ℕ)
   (C:List (List ℕ)):Bool :=
 z2d C.flatten && C.flatten.all (fun i => decide (i < n)) &&
 C.all (fun c => !c.isEmpty &&
   z18 (fun a b => bits.testBit (Nat.pair a b) ||
     bits.testBit (Nat.pair b a)) c &&
   z18 (fun a b => (!(zff q).testBit a) || (!(zff q).testBit b)) c &&
   c.head?.all (fun a => (zff q).testBit a) &&
   c.getLast?.all (fun a => (zff q).testBit a)) &&
 decide (∀ i∈q,i∈C.flatten)
theorem zea (n:ℕ) (q:Finset ℕ) (E:List (ℕ × ℕ))
   (C:List (List ℕ)) :
   qCachedLabelValidBool n q (y9 E) C=true↔z2b n q E C :=
 by
   have hf (i:ℕ):(zff q).testBit i=false↔i∉q:=by
     rw [Bool.eq_false_iff]
     exact not_congr (z182 q i)
   unfold z2b
   simp only [qCachedLabelValidBool,Bool.and_eq_true,z53,
     List.all_eq_true,decide_eq_true_eq,z52,
     Bool.or_eq_true,z3e,z182,Option.all_eq_true,
     Bool.not_eq_true',hf,List.isEmpty_eq_false_iff,Option.mem_def]
   simp only [and_assoc]
   rfl
def qCachedCycleValidBool (n k bits:ℕ) (C:List ℕ):Bool :=
 z2d C && decide (C.length=k+1) &&
 C.all (fun i => decide (i<n)) &&
 z18 (fun a b => bits.testBit (Nat.pair a b) ||
   bits.testBit (Nat.pair b a)) C &&
 C.head?.all (fun a => C.getLast?.all (fun b =>
   bits.testBit (Nat.pair a b) || bits.testBit (Nat.pair b a)))
theorem ze9 (n k:ℕ) (E:List (ℕ × ℕ)) (C:List ℕ) :
   qCachedCycleValidBool n k (y9 E) C=true↔z2a n k E C:=by
 simp only [qCachedCycleValidBool,z2a,Bool.and_eq_true,
   z53,decide_eq_true_eq,List.all_eq_true,
   z52,Bool.or_eq_true,z3e,
   Option.all_eq_true,labelAdj,Option.mem_def,and_assoc]
 simp only [or_comm]
 rfl
def z2e (k t n:ℕ) (q:Finset ℕ) (bits:ℕ) (L e:ℕ)
   (M:y4):y2 → Bool
 | .system C => qCachedLabelValidBool n q bits C && decide (Improvement k t L e C)
 | .cycle C => qCachedCycleValidBool n k bits C
 | .packing P => decide (PackingValid k t n M P)
 | .edge i j => decide (i < n) && decide (j < n) &&
     (bits.testBit (Nat.pair i j) || bits.testBit (Nat.pair j i)) &&
     decide (matrixEntry M i j 0)
 | .forbid i j d R N => decide (i < n) && decide (j < n) &&
     z2e k t (n+d) q
       (bits ||| y9 (pathEdges (pathLabels n i j d))) L e M R &&
     z2e k t n q bits L e ((i,j,d)::M) N
theorem qCachedCertificateBool_spec (k t n:ℕ) (q:Finset ℕ) (E:List (ℕ × ℕ))
   (L e:ℕ) (M:y4) (C:y2) :
   z2e k t n q (y9 E) L e M C=true ↔
     C.Valid k t n q E L e M:=by
 induction C generalizing n E M with
 | system C => simp [z2e,y2.Valid,zea]
 | cycle C => exact ze9 n k E C
 | packing P => simp [z2e,y2.Valid]
 | edge i j =>
   simp [z2e,y2.Valid,z3e,labelAdj,and_assoc]
 | forbid i j d R N ihR ihN =>
   simp only [z2e,Bool.and_eq_true,decide_eq_true_eq]
   rw [← qCacheEdgeBits_append,← augmentedEdges,ihR,ihN]
   simp only [y2.Valid,and_assoc]
instance (priority:=high) qCachedCertificateValid (k t n:ℕ) (q:Finset ℕ)
   (E:List (ℕ × ℕ)) (L e:ℕ) (M:y4) (C:y2) :
   Decidable (C.Valid k t n q E L e M) :=
 decidable_of_iff _ (qCachedCertificateBool_spec k t n q E L e M C)
end CycleClique
namespace CycleClique
open scoped SimpleGraph
open scoped SimpleGraph
theorem z45 {V:Type*} [Fintype V] {G:SimpleGraph V}
   {Q:Set V} (hQ:G.IsClique Q) {k d:ℕ} (hk: 3≤ k)
   (ht:Q.ncard≤ k) (hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G)
   {x y:V} (hd:k+1-Q.ncard≤ d) (hd' :d≤ k-1) :
   ¬ z5 G Q x y d:=by
 classical
 rintro ⟨hx,hy,hxy,p,hp,hlen,hint⟩
 let S:=(Q.toFinset.erase x).erase y
 have hs:S.card=Q.ncard-2:=by
   dsimp [S]
   rw [Finset.card_erase_of_mem (by simp [hy,hxy.symm]),
     Finset.card_erase_of_mem (by simpa using hx),← Set.ncard_eq_toFinset_card']
   omega
 obtain ⟨T,hTS,hTc⟩:=Finset.exists_subset_card_eq (show k-1-d≤ S.card by omega)
 let C:=p.support ::T.toList.map (fun v => [v])
 have hTf:∀ v∈T,v∈Q∧v≠x∧v≠y:=by
   intro v hv
   have hh:=hTS hv
   simp only [S,Finset.mem_erase,Set.mem_toFinset] at hh
   exact ⟨hh.2.2,hh.2.1,hh.1⟩
 have hf:C.flatten=p.support ++ T.toList:=by simp [C,z97]
 have hnd:C.flatten.Nodup:=by
   rw [hf,List.nodup_append]
   refine ⟨hp.support_nodup,Finset.nodup_toList _,?_⟩
   intro a ha b hb hab
   subst b
   have hh:=hTf a (Finset.mem_toList.mp hb)
   exact (hint a ha hh.1).elim hh.2.1 hh.2.2
 have hc:=zd0 hQ C (by
   intro c hc
   simp only [C,List.mem_cons,List.mem_map] at hc
   rcases hc with rfl | ⟨v,hv,rfl⟩
   · exact p.support_ne_nil
   · simp) hnd (by
   intro c hc
   simp only [C,List.mem_cons,List.mem_map] at hc
   rcases hc with rfl | ⟨v,hv,rfl⟩
   · exact p.isChain_adj_support
   · simp) (by
   intro c hc
   simp only [C,List.mem_cons,List.mem_map] at hc
   rcases hc with rfl | ⟨v,hv,rfl⟩
   · constructor
     · intro u hu
       have:u=x:=by simpa [List.head?_eq_some_head p.support_ne_nil] using hu.symm
       simpa [this] using hx
     · intro u hu
       have:u=y:=by simpa [List.getLast?_eq_some_getLast p.support_ne_nil] using hu.symm
       simpa [this] using hy
   · have hvQ:=(hTf v (Finset.mem_toList.mp hv)).1
     simpa using And.intro hvQ hvQ) (by
   rw [hf,List.length_append,SimpleGraph.Walk.length_support,Finset.length_toList,hTc]
   omega)
 have hcL:C.flatten.length=k+1:=by
   rw [hf,List.length_append,SimpleGraph.Walk.length_support,Finset.length_toList,hTc]
   omega
 exact hcycle (hcL ▸ hc)
theorem zd3 {V:Type*} {G:SimpleGraph V} {Q:Set V}
   {x y:V} {d:ℕ} (L:List V) (hL:L.Nodup) (z130:L.IsChain G.Adj)
   (za6:L.head? = some x) (z11c:L.getLast? = some y)
   (hlen:L.length=d+2) (hx:x∈Q) (hy:y∈Q)
   (hint:∀ v∈L,v∈Q → v=x∨v=y):z5 G Q x y d:=by
 have hne:L ≠ []:=by intro he; simp [he] at za6
 let p:=SimpleGraph.Walk.ofSupport L hne z130
 have he₁:L.head hne=x:=by simpa only [List.head?_eq_some_head hne,Option.some.injEq] using za6
 have he₂:L.getLast hne=y:=by simpa only [List.getLast?_eq_some_getLast hne,Option.some.injEq] using z11c
 let p' :=p.copy he₁ he₂
 have hs:p'.support=L:=by simp [p',p]
 have hp:p'.IsPath:=p'.isPath_def.mpr (hs ▸ hL)
 have hl:p'.length=d+1:=by
   have:=p'.length_support
   rw [hs,hlen] at this
   omega
 refine ⟨hx,hy,?_,p',hp,hl,?_⟩
 · intro he
   have:=(hp.nil_iff_eq.mpr he).length_eq_zero
   omega
 · simpa only [hs] using hint
def z5b {V:Type*} (G:SimpleGraph V) (Q:Set V) (x:V):Set V :=
 {u | G.Adj x u∧u∉Q}
def z16 {V:Type*} (G:SimpleGraph V) (Q S:Set V):Set V :=
 z0 G S \ Q
theorem zde {V:Type*} [Fintype V] {G:SimpleGraph V}
   {Q A B:Set V} (hQ:G.IsClique Q) (ht: 3≤ Q.ncard) (ht' :Q.ncard≤4)
   (hcycle:¬ SimpleGraph.cycleGraph 5⊑G)
   (hA:A⊆Qᶜ) (hB:B⊆Qᶜ) (hAB:Disjoint A B)
   (z44:∀ u∈A,∀ v∈B,∃ x∈Q,∃ y∈Q,x≠y∧G.Adj x u∧G.Adj y v) :
   Disjoint (z16 G Q A) (z16 G Q B):=by
 classical
 apply Set.disjoint_left.mpr
 intro z hzA hzB
 obtain ⟨u,hu,huz⟩:∃ u∈A,u=z∨G.Adj u z:=by
   rcases hzA.1 with hu | ⟨u,hu,huz⟩
   · exact ⟨z,hu,Or.inl rfl⟩
   · exact ⟨u,hu,Or.inr huz⟩
 obtain ⟨v,hv,hvz⟩:∃ v∈B,v=z∨G.Adj v z:=by
   rcases hzB.1 with hv | ⟨v,hv,hvz⟩
   · exact ⟨z,hv,Or.inl rfl⟩
   · exact ⟨v,hv,Or.inr hvz⟩
 have huv:u≠v:=fun he => Set.disjoint_left.mp hAB hu (he ▸ hv)
 obtain ⟨x,hx,y,hy,hxy,hxu,hyv⟩:=z44 u hu v hv
 have hun:=hA hu
 have hvn:=hB hv
 have hz:=hzA.2
 have hno2:=z45 hQ (k:=4) (by omega) ht' hcycle
   (x:=x) (y:=y) (d:=2) (by omega) (by omega)
 have hno3:=z45 hQ (k:=4) (by omega) ht' hcycle
   (x:=x) (y:=y) (d:=3) (by omega) (by omega)
 have hneq:∀ w,w∉Q → w≠x∧w≠y:=by
   intro w hw
   exact ⟨fun he => hw (he ▸ hx),fun he => hw (he ▸ hy)⟩
 have huq:=hneq u hun
 have hvq:=hneq v hvn
 have hzq:=hneq z hz
 have z1d4:¬ G.Adj u v:=by
   intro huvAdj
   apply hno2
   apply zd3 [x,u,v,y]
   · simp [hxy,huq.2,hvq.2,Ne.symm huq.1,Ne.symm hvq.1,huv]
   · simpa using And.intro hxu (And.intro huvAdj hyv.symm)
   · rfl
   · rfl
   · rfl
   · exact hx
   · exact hy
   · intro w hw hwQ
     simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
     rcases hw with rfl | rfl | rfl | rfl
     · exact Or.inl rfl
     · exact (hun hwQ).elim
     · exact (hvn hwQ).elim
     · exact Or.inr rfl
 rcases huz with rfl | huz
 · rcases hvz with he | hvz
   · exact huv he.symm
   · exact z1d4 hvz.symm
 rcases hvz with rfl | hvz
 · exact z1d4 huz
 apply hno3
 apply zd3 [x,u,z,v,y]
 · simp [hxy,huq.2,hvq.2,hzq.2,Ne.symm huq.1,
     Ne.symm hvq.1,Ne.symm hzq.1,huv,huz.ne,hvz.ne.symm]
 · simpa using And.intro hxu (And.intro huz (And.intro hvz.symm hyv.symm))
 · rfl
 · rfl
 · rfl
 · exact hx
 · exact hy
 · intro w hw hwQ
   simp only [List.mem_cons,List.not_mem_nil,or_false] at hw
   rcases hw with rfl | rfl | rfl | rfl | rfl
   · exact Or.inl rfl
   · exact (hun hwQ).elim
   · exact (hz hwQ).elim
   · exact (hvn hwQ).elim
   · exact Or.inr rfl
structure Frame {V:Type*} (G:SimpleGraph V) (t:ℕ) where
 q:Fin t ↪ V
 adj:∀ i j,i≠j → G.Adj (q i) (q j)
end CycleClique
namespace CycleClique
open scoped SimpleGraph
namespace Frame
variable {V:Type*} {G:SimpleGraph V} {t:ℕ} (T:Frame G t)
def Q:Set V:=Set.range T.q
def U (i:Fin t):Set V:=z5b G T.Q (T.q i)
theorem memQ (i:Fin t):T.q i∈T.Q:=⟨i,rfl⟩
theorem z80 [Fintype V]:T.Q.ncard=t:=by
 rw [Q,Set.ncard_range_of_injective T.q.injective]
 simp
theorem clique:G.IsClique T.Q:=by
 rintro x ⟨i,rfl⟩ y ⟨j,rfl⟩ hxy
 exact T.adj i j (fun he => hxy (congrArg T.q he))
theorem z101 (i:Fin t):T.U i⊆T.Qᶜ:=fun _ hu => hu.2
theorem neQ {u:V} (hu:u∉T.Q) (i:Fin t):u≠T.q i :=
 fun he => hu (he ▸ T.memQ i)
def z15b (e:Fin t ≃ Fin t):Frame G t where
 q:=e.toEmbedding.trans T.q
 adj i j hij:=T.adj (e i) (e j) (fun he => hij (e.injective he))
theorem z1ca (e:Fin t ≃ Fin t):(T.z15b e).Q=T.Q:=by
 ext u
 constructor
 · rintro ⟨i,rfl⟩
   exact T.memQ _
 · rintro ⟨i,rfl⟩
   exact ⟨e.symm i,by simp [z15b]⟩
theorem z1cb (e:Fin t ≃ Fin t) (i:Fin t) :
   (T.z15b e).U i=T.U (e i):=by
 simp only [U,z1ca]
 rfl
def z16f {a b c:V} (hab:G.Adj a b) (hbc:G.Adj b c) (hca:G.Adj c a):Frame G 3 where
 q:=⟨![a,b,c],by
   intro i j he
   fin_cases i <;> fin_cases j <;> aesop⟩
 adj i j hij:=by
   change G.Adj (![a,b,c] i) (![a,b,c] j)
   fin_cases i <;> fin_cases j <;> simp_all [SimpleGraph.adj_comm]
theorem z144 {a b c:V} (hab:G.Adj a b) (hbc:G.Adj b c) (hca:G.Adj c a) :
   (z16f hab hbc hca).Q={a,b,c}:=by
 ext u
 simp only [Q,Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
 constructor
 · rintro ⟨i,rfl⟩
   change ![a,b,c] i=a ∨ ![a,b,c] i=b ∨ ![a,b,c] i=c
   fin_cases i <;> simp
 · rintro (rfl | rfl | rfl)
   · exact ⟨0,rfl⟩
   · exact ⟨1,rfl⟩
   · exact ⟨2,rfl⟩
end Frame
theorem z6b {V ι:Type*} [Fintype V] [Fintype ι]
   {G:SimpleGraph V} {Q:Set V} (S: ι → Set V)
   (hdis:Pairwise (fun i j => Disjoint (z16 G Q (S i)) (z16 G Q (S j)))) :
   Q.ncard + ∑ i,(z16 G Q (S i)).ncard≤ Fintype.card V:=by
 classical
 have hc:=z9b (fun i => z16 G Q (S i)) hdis Finset.univ
 have hb:=Set.ncard_le_ncard (show (⋃ i∈Finset.univ,z16 G Q (S i))⊆Qᶜ from by
   rintro v hv
   obtain ⟨i,_,hi⟩:=Set.mem_iUnion₂.mp hv
   exact hi.2)
 have he:=Set.ncard_add_ncard_compl Q
 rw [Nat.card_eq_fintype_card] at he
 omega
theorem z57 {V:Type*} [Fintype V] {G:SimpleGraph V}
   {k:ℕ} (hexp:∀ I,G.IsIndepSet I → I.Nonempty → 
     k*I.ncard+1≤(z0 G I).ncard)
   {Q S R:Set V} (hS:S⊆Qᶜ) (hne:S.Nonempty)
   (hb:∀ u∈S,∀ x∈Q,G.Adj u x → x∈R) :
   k*independence G S+1≤(z16 G Q S).ncard+R.ncard:=by
 obtain ⟨I,hIS,hI,hIc⟩:=z6 G S
 have hi:=z14 (G:=G) hne
 have he:=hexp I hI ((Set.ncard_pos).mp (by omega))
 have hs:z0 G I⊆z16 G Q S∪R:=by
   intro x hx
   by_cases hxQ:x∈Q
   · right
     rcases hx with hx | ⟨u,hu,hux⟩
     · exact (hS (hIS hx) hxQ).elim
     · exact hb u (hIS hu) x hxQ hux
   · left
     exact ⟨za1 G hIS hx,hxQ⟩
 have hc:=(Set.ncard_le_ncard hs).trans (Set.ncard_union_le _ _)
 rw [hIc] at he
 omega
theorem z8e {V:Type*} [Fintype V] {G:SimpleGraph V}
   {k:ℕ} (hexp:∀ I,G.IsIndepSet I → I.Nonempty → 
     k*I.ncard+1≤(z0 G I).ncard)
   {Q I R:Set V} (hI:G.IsIndepSet I) (hS:I⊆Qᶜ) (hne:I.Nonempty)
   (hb:∀ u∈I,∀ x∈Q,G.Adj u x → x∈R) :
   k*I.ncard+1≤(z16 G Q I).ncard+R.ncard:=by
 have hi:=z15 hI (Set.Subset.refl I)
 exact (by gcongr:k*I.ncard+1≤ k*independence G I+1).trans
   (z57 hexp hS hne hb)
theorem Frame.z165 {V:Type*} [Fintype V] {G:SimpleGraph V} {k t:ℕ}
   (T:Frame G t) (hexp:∀ I,G.IsIndepSet I → I.Nonempty → 
     k*I.ncard+1≤(z0 G I).ncard) (i:Fin t) :
   k+1≤ t+(T.U i).ncard:=by
 have he:=hexp {T.q i} (Set.pairwise_singleton _ _) (Set.singleton_nonempty _)
 have hs:z0 G {T.q i}⊆T.Q∪T.U i:=by
   rintro x (rfl | ⟨y,hy,hyx⟩)
   · exact Or.inl (T.memQ i)
   · have he:y=T.q i:=hy
     subst y
     by_cases hx:x∈T.Q
     · exact Or.inl hx
     · exact Or.inr ⟨hyx,hx⟩
 have hc:=(Set.ncard_le_ncard hs).trans (Set.ncard_union_le _ _)
 rw [T.z80] at hc
 simp only [Set.ncard_singleton,Nat.mul_one] at he
 omega
theorem Frame.zd5 {V:Type*} [Fintype V] {G:SimpleGraph V} {t u:ℕ}
   (T:Frame G t) (hcl:G.cliqueNum≤ u) (i:Fin t) (hUi:G.IsClique (T.U i)) :
   (T.U i).ncard+1≤ u:=by
 have hC:G.IsClique (insert (T.q i) (T.U i)):=by
   intro x hx y hy hxy
   rcases hx with rfl | hx <;> rcases hy with rfl | hy
   · exact (hxy rfl).elim
   · exact hy.1
   · exact hx.1.symm
   · exact hUi hx hy hxy
 have hc:=(za hC).trans hcl
 rwa [Set.ncard_insert_of_notMem (fun hh => hh.2 (T.memQ i))] at hc
theorem Frame.z170 {V:Type*} {G:SimpleGraph V} {t:ℕ}
   (T:Frame G t) (i:Fin t):T.U i=z1 G T.Q (T.q i) 0:=rfl
theorem Frame.z169 {V:Type*} {G:SimpleGraph V} {t:ℕ}
   (T:Frame G t) (i:Fin t):z16 G T.Q (T.U i)=z1 G T.Q (T.q i) 1:=by
 ext x
 simp only [z16,z0,Set.mem_sdiff,Set.mem_union,Set.mem_ofPred_eq,
   z1,Frame.U,z5b]
 tauto
theorem Frame.z174 {V:Type*} {G:SimpleGraph V} {t:ℕ}
   (T:Frame G t) (hdis:Pairwise (fun i j => Disjoint (T.U i) (T.U j)))
   (i:Fin t) {u x:V} (hu:u∈T.U i) (hx:x∈T.Q) (hux:G.Adj u x) :
   x∈({T.q i}:Set V):=by
 obtain ⟨j,rfl⟩:=hx
 have hj:j=i:=by
   by_contra hji
   exact Set.disjoint_left.mp (hdis hji) (show u∈T.U j from ⟨hux.symm,hu.2⟩) hu
 subst j
 rfl
theorem Frame.zc0 {V:Type*} [Fintype V] {G:SimpleGraph V} {k t:ℕ}
   (T:Frame G t) (hexp:∀ I,G.IsIndepSet I → I.Nonempty → 
     k*I.ncard+1≤(z0 G I).ncard)
   (hdis:Pairwise (fun i j => Disjoint (T.U i) (T.U j)))
   (i:Fin t) (hne:(T.U i).Nonempty) :
   k*independence G (T.U i)≤(z16 G T.Q (T.U i)).ncard:=by
 have hh:=z57 hexp (T.z101 i) hne (R:={T.q i})
   (fun _ hu _ hx hux => T.z174 hdis i hu hx hux)
 simp only [Set.ncard_singleton] at hh
 omega
theorem Frame.zec {V:Type*} [Fintype V] {G:SimpleGraph V}
   (T:Frame G 3) (hcycle:¬ SimpleGraph.cycleGraph 5⊑G)
   (hdis:Pairwise (fun i j => Disjoint (T.U i) (T.U j))) :
   Pairwise (fun i j => Disjoint (z16 G T.Q (T.U i)) (z16 G T.Q (T.U j))):=by
 intro i j hij
 apply zde T.clique (by rw [T.z80]) (by rw [T.z80]; omega) hcycle
   (T.z101 i) (T.z101 j) (hdis hij)
 intro u hu v hv
 exact ⟨T.q i,T.memQ i,T.q j,T.memQ j,fun he => hij (T.q.injective he),hu.1,hv.1⟩
theorem z163 {V:Type*} [Fintype V] {G:SimpleGraph V}
   (z79:Fintype.card V≤17) (hcycle:¬ SimpleGraph.cycleGraph 5⊑G)
   (hexp:∀ I,G.IsIndepSet I → I.Nonempty → 4*I.ncard+1≤(z0 G I).ncard)
   (T:Frame G 4):False:=by
 have hno:∀ i j:Fin 4,i≠j → ∀ d,1≤ d → d≤3 → 
     ¬ z5 G T.Q (T.q i) (T.q j) d:=by
   intro i j hij d hd hd'
   exact z45 T.clique (by omega) (by rw [T.z80]) hcycle
     (by rw [T.z80]; omega) (by omega)
 have hdis:Pairwise (fun i j => Disjoint (T.U i) (T.U j)):=by
   intro i j hij
   rw [T.z170,T.z170]
   exact (z47 (T.memQ i) (T.memQ j)
     (fun he => hij (T.q.injective he)) (fun d hd hd' => hno i j hij d hd (by omega))).1
 have z1db:Pairwise (fun i j => Disjoint (z16 G T.Q (T.U i))
     (z16 G T.Q (T.U j))):=by
   intro i j hij
   apply Set.disjoint_left.mpr
   intro z hzi hzj
   rw [T.z169] at hzi hzj
   obtain ⟨d,hd,hd',hp⟩:=z90 (T.memQ i) (T.memQ j)
     (fun he => hij (T.q.injective he)) hzi hzj
   exact hno i j hij d hd hd' hp
 have hb:∀ i:Fin 4,4≤(z16 G T.Q (T.U i)).ncard:=by
   intro i
   have hu:=T.z165 hexp i
   have hne:(T.U i).Nonempty:=(Set.ncard_pos).mp (by omega)
   have hi:=z14 (G:=G) hne
   have he:=T.zc0 hexp hdis i hne
   omega
 have hs:=z6b T.U z1db
 rw [T.z80] at hs
 have hh:=Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hb i)
 simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at hh
 omega
structure FourHyp {V:Type*} [Fintype V] (G:SimpleGraph V):Prop where
 order:Fintype.card V≤17
 cycle:¬ SimpleGraph.cycleGraph 5⊑G
 clique:G.cliqueNum≤3
 expansion:∀ I,G.IsIndepSet I → I.Nonempty → 4*I.ncard+1≤(z0 G I).ncard
end CycleClique
namespace CycleClique
open scoped SimpleGraph
namespace FourHyp
variable {V:Type*} [Fintype V] {G:SimpleGraph V} (H:FourHyp G)
include H
theorem z13b (T:Frame G 3) (i:Fin 3): 2≤(T.U i).ncard:=by
 have:=T.z165 H.expansion i
 omega
theorem z30 (T:Frame G 3) (i:Fin 3):(T.U i).Nonempty :=
 (Set.ncard_pos).mp (lt_of_lt_of_le (by omega: 0<2) (H.z13b T i))
theorem z15d (T:Frame G 3)
   (hdis:Pairwise (fun i j => Disjoint (T.U i) (T.U j))) :
   ∀ i,(T.U i).ncard=2∧G.IsClique (T.U i):=by
 have hc:=T.zec H.cycle hdis
 have hb:=z6b T.U hc
 rw [T.z80,Fin.sum_univ_three] at hb
 have he:=fun i => T.zc0 H.expansion hdis i (H.z30 T i)
 have hi:=fun i => z14 (G:=G) (H.z30 T i)
 have he0:=he 0
 have he1:=he 1
 have he2:=he 2
 have hi0:=hi 0
 have hi1:=hi 1
 have hi2:=hi 2
 have ho:=H.order
 intro i
 have hai:independence G (T.U i)≤1:=by
   fin_cases i <;> dsimp at * <;> omega
 have hcli:=zf hai
 have hcu:=T.zd5 H.clique i hcli
 have hlo:=H.z13b T i
 exact ⟨by omega,hcli⟩
theorem z189 (T:Frame G 3) :
   ∃ S:Frame G 3,∃ i j:Fin 3,i≠j∧(S.U i∩S.U j).Nonempty:=by
 classical
 by_contra hn
 have hall:∀ S:Frame G 3,Pairwise (fun i j => Disjoint (S.U i) (S.U j)):=by
   intro S i j hij
   apply Set.disjoint_left.mpr
   intro u hui huj
   exact hn ⟨S,i,j,hij,u,hui,huj⟩
 have hT:=H.z15d T (hall T)
 have hsix:∀ i,6≤(z16 G T.Q (T.U i)).ncard:=by
   intro i
   obtain ⟨u,v,huv,hUi⟩:=Set.ncard_eq_two.mp (hT i).1
   have hu:u∈T.U i:=by rw [hUi]; simp
   have hv:v∈T.U i:=by rw [hUi]; simp
   let W:=Frame.z16f hu.1 ((hT i).2 hu hv huv) hv.1.symm
   have hW1:=H.z13b W 1
   have hW2:=H.z13b W 2
   have z1e7:Disjoint (W.U 1) (W.U 2):=hall W (by decide)
   have z1fd:Disjoint (T.U i) (W.U 1∪W.U 2):=by
     apply Set.disjoint_left.mpr
     intro x hx hxW
     have hxQ:x∈W.Q:=by
       rw [Frame.z144]
       rw [hUi] at hx
       simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx ⊢
       tauto
     rcases hxW with hxW | hxW <;> exact hxW.2 hxQ
   have hsub:T.U i∪(W.U 1∪W.U 2)⊆z16 G T.Q (T.U i):=by
     intro x hx
     rcases hx with hx | hx
     · exact ⟨Or.inl hx,hx.2⟩
     have hw:∃ y∈T.U i,G.Adj y x∧x∉W.Q:=by
       rcases hx with hx | hx
       · exact ⟨u,hu,hx.1,hx.2⟩
       · exact ⟨v,hv,hx.1,hx.2⟩
     obtain ⟨y,hy,hyx,hnW⟩:=hw
     refine ⟨Or.inr ⟨y,hy,hyx⟩,?_⟩
     intro hxQ
     have he:x=T.q i:=T.z174 (hall T) i hy hxQ hyx
     subst x
     exact hnW (W.memQ 0)
   have hb:=Set.ncard_le_ncard hsub
   rw [Set.ncard_union_eq z1fd,Set.ncard_union_eq z1e7,(hT i).1] at hb
   omega
 have hb:=z6b T.U (T.zec H.cycle (hall T))
 rw [T.z80,Fin.sum_univ_three] at hb
 have h0:=hsix 0
 have h1:=hsix 1
 have h2:=hsix 2
 have ho:=H.order
 omega
theorem z3a (T:Frame G 3) {A B:Set V} {i j:Fin 3}
   (hij:i≠j) (hA:A⊆T.U i) (hB:B⊆T.U j) (hdis:Disjoint A B) :
   Disjoint (z16 G T.Q A) (z16 G T.Q B):=by
 apply zde T.clique (by rw [T.z80]) (by rw [T.z80]; omega) H.cycle
   (fun _ hu => (hA hu).2) (fun _ hv => (hB hv).2) hdis
 intro u hu v hv
 exact ⟨T.q i,T.memQ i,T.q j,T.memQ j,
   fun he => hij (T.q.injective he),(hA hu).1,(hB hv).1⟩
theorem z17f (T:Frame G 3) {u v:V} {i j:Fin 3}
   (hij:i≠j) (hu:u∈T.U i) (hv:v∈T.U j) (huv:u≠v) :
   ¬ G.Adj u v:=by
 have hd:=H.z3a T hij (A:={u}) (B:={v})
   (by simpa) (by simpa) (by simp [huv])
 intro he
 exact Set.disjoint_left.mp hd (show v∈z16 G T.Q {u} from
   ⟨Or.inr ⟨u,rfl,he⟩,hv.2⟩) ⟨Or.inl rfl,hv.2⟩
theorem z120 (T:Frame G 3) {u:V}
   (h0:u∈T.U 0) (h1:u∈T.U 1):u∉T.U 2:=by
 intro h2
 have hc:G.IsClique (insert u T.Q):=by
   have ha:∀ x∈T.Q,G.Adj u x:=by
     rintro x ⟨i,rfl⟩
     fin_cases i
     · exact h0.1.symm
     · exact h1.1.symm
     · exact h2.1.symm
   intro x hx y hy hxy
   rcases hx with rfl | hx <;> rcases hy with rfl | hy
   · exact (hxy rfl).elim
   · exact ha y hy
   · exact (ha x hx).symm
   · exact T.clique hx hy hxy
 have hb:=(za hc).trans H.clique
 rw [Set.ncard_insert_of_notMem h0.2,T.z80] at hb
 omega
theorem z146 (T:Frame G 3) {i j l:Fin 3}
   (hij:i≠j) (hil:i≠l) (hjl:j≠l) {u v:V}
   (hu:u∈T.U i∩T.U j) (hv:v∈T.U i∩T.U l) (huv:u≠v):False:=by
 have hnu:=T.neQ hu.1.2
 have hnv:=T.neQ hv.1.2
 apply H.cycle
 apply zaf [T.q j,u,T.q i,v,T.q l] (by simp)
 · simp [T.q.injective.eq_iff,hil,hjl,Ne.symm hij,hnu,hnv,
     Ne.symm (hnu j),Ne.symm (hnv j),Ne.symm (hnv i),huv]
 · simpa using And.intro hu.2.1 (And.intro hu.1.1.symm
     (And.intro hv.1.1 hv.2.1.symm))
 · simpa using T.adj l j hjl.symm
theorem za9 (T:Frame G 3) (hne:(T.U 0∩T.U 1).Nonempty) :
   Disjoint (T.U 0) (T.U 2)∧Disjoint (T.U 1) (T.U 2):=by
 obtain ⟨u,hu0,hu1⟩:=hne
 constructor
 · apply Set.disjoint_left.mpr
   intro v hv0 hv2
   have huv:u≠v:=fun he => H.z120 T hu0 hu1 (he ▸ hv2)
   exact H.z146 T (by decide:(0:Fin 3)≠1) (by decide) (by decide)
     ⟨hu0,hu1⟩ ⟨hv0,hv2⟩ huv
 · apply Set.disjoint_left.mpr
   intro v hv1 hv2
   have huv:u≠v:=fun he => H.z120 T hu0 hu1 (he ▸ hv2)
   exact H.z146 T (by decide:(1:Fin 3)≠0) (by decide) (by decide)
     ⟨hu1,hu0⟩ ⟨hv1,hv2⟩ huv
theorem z14d (T:Frame G 3):G.IsIndepSet (T.U 0∩T.U 1):=by
 intro u hu v hv huv
 exact H.z17f T (by decide:(0:Fin 3)≠1) hu.1 hv.2 huv
def z7b (T:Frame G 3):Fin 4 → Set V :=
 ![T.U 0∩T.U 1,T.U 0 \ T.U 1,T.U 1 \ T.U 0,T.U 2]
theorem z118 (T:Frame G 3) (hne:(T.U 0∩T.U 1).Nonempty) :
   Pairwise (fun i j => Disjoint (z16 G T.Q (z7b T i))
     (z16 G T.Q (z7b T j))):=by
 have hd:=H.za9 T hne
 have h01:=H.z3a T (by decide:(1:Fin 3)≠0)
   (A:=T.U 0∩T.U 1) (B:=T.U 0 \ T.U 1) Set.inter_subset_right Set.sdiff_subset
   (Set.disjoint_left.mpr (by intro u hu hv; exact hv.2 hu.2))
 have h02:=H.z3a T (by decide:(0:Fin 3)≠1)
   (A:=T.U 0∩T.U 1) (B:=T.U 1 \ T.U 0) Set.inter_subset_left Set.sdiff_subset
   (Set.disjoint_left.mpr (by intro u hu hv; exact hv.2 hu.1))
 have h03:=H.z3a T (by decide:(0:Fin 3)≠2)
   (A:=T.U 0∩T.U 1) (B:=T.U 2) Set.inter_subset_left (Set.Subset.refl _)
   (hd.1.mono_left Set.inter_subset_left)
 have h12:=H.z3a T (by decide:(0:Fin 3)≠1)
   (A:=T.U 0 \ T.U 1) (B:=T.U 1 \ T.U 0) Set.sdiff_subset Set.sdiff_subset
   (Set.disjoint_left.mpr (by intro u hu hv; exact hu.2 hv.1))
 have h13:=H.z3a T (by decide:(0:Fin 3)≠2)
   (A:=T.U 0 \ T.U 1) (B:=T.U 2) Set.sdiff_subset (Set.Subset.refl _)
   (hd.1.mono_left Set.sdiff_subset)
 have h23:=H.z3a T (by decide:(1:Fin 3)≠2)
   (A:=T.U 1 \ T.U 0) (B:=T.U 2) Set.sdiff_subset (Set.Subset.refl _)
   (hd.2.mono_left Set.sdiff_subset)
 intro i j hij
 fin_cases i <;> fin_cases j <;> simp only [z7b] <;>
   first | exact (hij rfl).elim | assumption | exact h01.symm | exact h02.symm |
     exact h03.symm | exact h12.symm | exact h13.symm | exact h23.symm
theorem za4 (T:Frame G 3) (hne:(T.U 0∩T.U 1).Nonempty) :
   T.U 0=T.U 1∧(T.U 0).ncard=2∧G.IsIndepSet (T.U 0) ∧
     (T.U 2).ncard=2∧G.IsClique (T.U 2):=by
 have hd:=H.za9 T hne
 have hI:=H.z14d T
 have hbI:∀ u∈T.U 0∩T.U 1,∀ x∈T.Q,G.Adj u x → 
     x∈({T.q 0,T.q 1}:Set V):=by
   rintro u hu x ⟨i,rfl⟩ hux
   fin_cases i
   · simp
   · simp
   · exact (H.z120 T hu.1 hu.2 ⟨hux.symm,hu.1.2⟩).elim
 have hbA:∀ u∈T.U 0 \ T.U 1,∀ x∈T.Q,G.Adj u x → 
     x∈({T.q 0}:Set V):=by
   rintro u hu x ⟨i,rfl⟩ hux
   fin_cases i
   · rfl
   · exact (hu.2 ⟨hux.symm,hu.1.2⟩).elim
   · exact (Set.disjoint_left.mp hd.1 hu.1 ⟨hux.symm,hu.1.2⟩).elim
 have hbB:∀ u∈T.U 1 \ T.U 0,∀ x∈T.Q,G.Adj u x → 
     x∈({T.q 1}:Set V):=by
   rintro u hu x ⟨i,rfl⟩ hux
   fin_cases i
   · exact (hu.2 ⟨hux.symm,hu.1.2⟩).elim
   · rfl
   · exact (Set.disjoint_left.mp hd.2 hu.1 ⟨hux.symm,hu.1.2⟩).elim
 have hbD:∀ u∈T.U 2,∀ x∈T.Q,G.Adj u x → 
     x∈({T.q 2}:Set V):=by
   rintro u hu x ⟨i,rfl⟩ hux
   fin_cases i
   · exact (Set.disjoint_left.mp hd.1 ⟨hux.symm,hu.2⟩ hu).elim
   · exact (Set.disjoint_left.mp hd.2 ⟨hux.symm,hu.2⟩ hu).elim
   · rfl
 have heI:=z8e H.expansion hI (fun _ hu => hu.1.2) hne hbI
 have z1e4:({T.q 0,T.q 1}:Set V).ncard=2:=by
   simp [T.q.injective.eq_iff]
 rw [z1e4] at heI
 have heA:(T.U 0 \ T.U 1).Nonempty → 
     4≤(z16 G T.Q (T.U 0 \ T.U 1)).ncard:=by
   intro hn
   have hh:=z57 H.expansion (fun _ hu => hu.1.2) hn hbA
   have hi:=z14 (G:=G) hn
   simp only [Set.ncard_singleton] at hh
   omega
 have heB:(T.U 1 \ T.U 0).Nonempty → 
     4≤(z16 G T.Q (T.U 1 \ T.U 0)).ncard:=by
   intro hn
   have hh:=z57 H.expansion (fun _ hu => hu.1.2) hn hbB
   have hi:=z14 (G:=G) hn
   simp only [Set.ncard_singleton] at hh
   omega
 have heD:=z57 H.expansion (T.z101 2) (H.z30 T 2) hbD
 simp only [Set.ncard_singleton] at heD
 have hiD:=z14 (G:=G) (H.z30 T 2)
 have hs:=z6b (z7b T) (H.z118 T hne)
 rw [T.z80,Fin.sum_univ_four] at hs
 dsimp [z7b] at hs
 have ho:=H.order
 have hr:=(Set.ncard_pos).mpr hne
 have hU0:=H.z13b T 0
 have hU1:=H.z13b T 1
 have hr2:(T.U 0∩T.U 1).ncard=2:=by
   have hrne:(T.U 0∩T.U 1).ncard≠1:=by
     intro he
     have hA:(T.U 0 \ T.U 1).Nonempty:=by
       by_contra hn
       have hsub:T.U 0⊆T.U 0∩T.U 1:=by
         intro u hu
         refine ⟨hu,?_⟩
         by_contra hh
         exact hn ⟨u,hu,hh⟩
       have:=Set.ncard_le_ncard hsub
       omega
     have hB:(T.U 1 \ T.U 0).Nonempty:=by
       by_contra hn
       have hsub:T.U 1⊆T.U 0∩T.U 1:=by
         intro u hu
         refine ⟨?_,hu⟩
         by_contra hh
         exact hn ⟨u,hu,hh⟩
       have:=Set.ncard_le_ncard hsub
       omega
     have:=heA hA
     have:=heB hB
     omega
   omega
 have hA0:(T.U 0 \ T.U 1)=∅ :=by
   apply Set.not_nonempty_iff_eq_empty.mp
   intro hn
   have:=heA hn
   omega
 have hB0:(T.U 1 \ T.U 0)=∅ :=by
   apply Set.not_nonempty_iff_eq_empty.mp
   intro hn
   have:=heB hn
   omega
 have hEq:T.U 0=T.U 1:=Set.Subset.antisymm (Set.sdiff_eq_empty.mp hA0)
   (Set.sdiff_eq_empty.mp hB0)
 have hIe:T.U 0∩T.U 1=T.U 0:=by rw [← hEq,Set.inter_self]
 have hDcl:=zf (G:=G) (S:=T.U 2) (by omega)
 have z221:=T.zd5 H.clique 2 hDcl
 have z222:=H.z13b T 2
 exact ⟨hEq,by simpa only [hIe] using hr2,by simpa only [hIe] using hI,
   by omega,hDcl⟩
theorem zb9 (T:Frame G 3) (hne:(T.U 0∩T.U 1).Nonempty)
   {w:V} (hw:w∈T.U 0):(z5b G T.Q w).ncard≤2:=by
 have hs:=H.za4 T hne
 have hw1:w∈T.U 1:=hs.1 ▸ hw
 let S:=Frame.z16f (T.adj 0 1 (by decide)) hw1.1 hw.1.symm
 have hq2:T.q 2∉S.Q:=by
   rw [Frame.z144]
   simp [T.q.injective.eq_iff,Ne.symm (T.neQ hw.2 2)]
 have hov:(S.U 0∩S.U 1).Nonempty :=
   ⟨T.q 2,⟨T.adj 0 2 (by decide),hq2⟩,⟨T.adj 1 2 (by decide),hq2⟩⟩
 have hSc:=(H.za4 S hov).2.2.2.1
 have hsub:z5b G T.Q w⊆S.U 2:=by
   intro x hx
   refine ⟨hx.1,?_⟩
   rw [Frame.z144]
   simp only [Set.mem_insert_iff,Set.mem_singleton_iff]
   rintro (rfl | rfl | rfl)
   · exact hx.2 (T.memQ 0)
   · exact hx.2 (T.memQ 1)
   · exact hx.1.ne rfl
 exact (Set.ncard_le_ncard hsub).trans_eq hSc
theorem z136 (T:Frame G 3) (hne:(T.U 0∩T.U 1).Nonempty):False:=by
 have hs:=H.za4 T hne
 obtain ⟨w,z,hwz,hU⟩:=Set.ncard_eq_two.mp hs.2.1
 have hw:w∈T.U 0:=by rw [hU]; simp
 have hz:z∈T.U 0:=by rw [hU]; simp
 have hdw:=H.zb9 T hne hw
 have hdz:=H.zb9 T hne hz
 have hsub:z16 G T.Q (T.U 0) ⊆
     T.U 0∪(z5b G T.Q w∪z5b G T.Q z):=by
   intro x hx
   rcases hx.1 with hxI | ⟨u,hu,hux⟩
   · exact Or.inl hxI
   · rw [hU] at hu
     rcases hu with rfl | rfl
     · exact Or.inr (Or.inl ⟨hux,hx.2⟩)
     · exact Or.inr (Or.inr ⟨hux,hx.2⟩)
 have hb:=(Set.ncard_le_ncard hsub).trans (Set.ncard_union_le _ _)
 have hb' :=Set.ncard_union_le (z5b G T.Q w) (z5b G T.Q z)
 have z1e:∀ u∈T.U 0,∀ x∈T.Q,G.Adj u x → 
     x∈({T.q 0,T.q 1}:Set V):=by
   rintro u hu x ⟨i,rfl⟩ hux
   fin_cases i
   · simp
   · simp
   · exact (H.z120 T hu (hs.1 ▸ hu) ⟨hux.symm,hu.2⟩).elim
 have he:=z8e H.expansion hs.2.2.1 (T.z101 0)
   (H.z30 T 0) z1e
 have hc2:({T.q 0,T.q 1}:Set V).ncard=2:=by simp [T.q.injective.eq_iff]
 rw [hc2,hs.2.1] at he
 rw [hs.2.1] at hb
 omega
theorem contradiction (T:Frame G 3):False:=by
 obtain ⟨S,i,j,hij,hne⟩:=H.z189 T
 let e:Fin 3 ≃ Fin 3:=(Equiv.swap 1 ((Equiv.swap 0 i) j)).trans (Equiv.swap 0 i)
 have he0:e 0=i:=by
   fin_cases i <;> fin_cases j <;> simp_all [e,Equiv.swap_apply_def]
 have he1:e 1=j:=by
   fin_cases i <;> fin_cases j <;> simp_all [e,Equiv.swap_apply_def]
 apply H.z136 (S.z15b e)
 simpa only [Frame.z1cb,he0,he1] using hne
end FourHyp
end CycleClique
namespace CycleClique
open scoped SimpleGraph
structure ThreeHyp {V:Type*} [Fintype V] (G:SimpleGraph V) (a:ℕ):Prop where
 order:Fintype.card V=3*a+1
 alpha:G.indepNum≤ a
 a_max:a≤3
 cycle:¬ SimpleGraph.cycleGraph 4⊑G
 clique:G.cliqueNum≤3
 expansion:∀ I,G.IsIndepSet I → I.Nonempty → 3*I.ncard+1≤(z0 G I).ncard
namespace ThreeHyp
variable {V:Type*} [Fintype V] {G:SimpleGraph V} {a:ℕ} (H:ThreeHyp G a)
include H
theorem z5e (T:Frame G 3) {i j:Fin 3} (hij:i≠j) :
   Disjoint (T.U i) (T.U j) ∧ ∀ u∈T.U i,∀ v∈T.U j,¬ G.Adj u v:=by
 rw [T.z170,T.z170]
 apply z47 (T.memQ i) (T.memQ j) (fun he => hij (T.q.injective he))
 intro d hd hd'
 apply z45 T.clique (by omega) (by rw [T.z80]) H.cycle
 · rw [T.z80]
   omega
 · omega
theorem z30 (T:Frame G 3) (i:Fin 3):(T.U i).Nonempty:=by
 have hd:=T.z165 H.expansion i
 exact (Set.ncard_pos).mp (by omega)
theorem z190 (T:Frame G 3): ∑ i,independence G (T.U i)≤ a:=by
 classical
 have hh:=z6f G T.U (fun _ _ hij => (H.z5e T hij).1)
   Finset.univ (fun _ _ _ _ hij => (H.z5e T hij).2)
 have hb:=z76 (G:=G) (Set.subset_univ (⋃ i∈Finset.univ,T.U i))
 rw [z31] at hb
 exact hh.trans (hb.trans H.alpha)
theorem a_eq (T:Frame G 3):a=3:=by
 have hs:=H.z190 T
 rw [Fin.sum_univ_three] at hs
 have h0:=z14 (G:=G) (H.z30 T 0)
 have h1:=z14 (G:=G) (H.z30 T 1)
 have h2:=z14 (G:=G) (H.z30 T 2)
 have:=H.a_max
 omega
theorem z1cd (T:Frame G 3) (i:Fin 3):G.IsClique (T.U i):=by
 have hs:=H.z190 T
 rw [Fin.sum_univ_three] at hs
 have h0:=z14 (G:=G) (H.z30 T 0)
 have h1:=z14 (G:=G) (H.z30 T 1)
 have h2:=z14 (G:=G) (H.z30 T 2)
 have:=H.a_max
 apply zf
 fin_cases i <;> dsimp at * <;> omega
theorem z171 (T:Frame G 3) (i:Fin 3): 1≤(T.U i).ncard∧(T.U i).ncard≤2:=by
 have hmin:=(Set.ncard_pos).mpr (H.z30 T i)
 have hmax:=T.zd5 H.clique i (H.z1cd T i)
 omega
def W (T:Frame G 3):Set V:=T.Qᶜ \ ⋃ i,T.U i
omit H in
omit H in
theorem z184 (_H:ThreeHyp G a) (T:Frame G 3) {w:V}
   (hw:w∈W T) (i:Fin 3):w∉T.U i :=
 fun hh => hw.2 (Set.mem_iUnion.mpr ⟨i,hh⟩)
theorem z1b5 (T:Frame G 3) {w:V} (hw:w∈W T) (i:Fin 3):¬ G.Adj w (T.q i) :=
 fun hh => H.z184 T hw i ⟨hh.symm,hw.1⟩
theorem z19e (T:Frame G 3) :
   (W T).ncard+((T.U 0).ncard+(T.U 1).ncard+(T.U 2).ncard)=7:=by
 classical
 have hd:Pairwise (fun i j => Disjoint (T.U i) (T.U j)) :=
   fun _ _ hij => (H.z5e T hij).1
 have hsum:=z9b T.U hd Finset.univ
 simp only [Finset.mem_univ,Set.iUnion_true] at hsum
 rw [Fin.sum_univ_three] at hsum
 have hsub:(⋃ i,T.U i)⊆T.Qᶜ:=by
   intro u hu
   obtain ⟨i,hi⟩:=Set.mem_iUnion.mp hu
   exact hi.2
 have he:=Set.ncard_sdiff_add_ncard_of_subset hsub
 have hq:=Set.ncard_add_ncard_compl T.Q
 rw [T.z80,Nat.card_eq_fintype_card,H.order,H.a_eq T] at hq
 change (W T).ncard+(⋃ i,T.U i).ncard=_ at he
 omega
theorem z1b6 (T:Frame G 3):(W T).Nonempty:=by
 have hw:=H.z19e T
 have h0:=H.z171 T 0
 have h1:=H.z171 T 1
 have h2:=H.z171 T 2
 exact (Set.ncard_pos).mp (by omega)
theorem z191 (T:Frame G 3) {w u v:V} (hw:w∈W T) {i:Fin 3}
   (hu:u∈T.U i) (hv:v∈T.U i) (hwu:G.Adj w u) (hwv:G.Adj w v):u=v:=by
 by_contra huv
 have hnw:=T.neQ hw.1
 have hnu:=T.neQ hu.2
 have hnv:=T.neQ hv.2
 apply H.cycle
 apply zaf [w,u,T.q i,v] (by simp)
 · simp [hwu.ne,hwv.ne,hnw,hnu,Ne.symm (hnv i),huv]
 · simpa using And.intro hwu (And.intro hu.1.symm hv.1)
 · simpa using hwv.symm
theorem z16b {w u v z:V}
   (hwu:w≠u) (hwv:w≠v) (hwz:w≠z)
   (huv:u≠v) (huz:u≠z) (hvz:v≠z)
   (nwu:¬ G.Adj w u) (nwv:¬ G.Adj w v) (nwz:¬ G.Adj w z)
   (nuv:¬ G.Adj u v) (nuz:¬ G.Adj u z) (nvz:¬ G.Adj v z):False:=by
 have hI:G.IsIndepSet {w,u,v,z}:=by
   intro x hx y hy hxy hadj
   simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
   rcases hx with rfl | rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl | rfl <;>
     first | exact hxy rfl | exact nwu hadj | exact nwu hadj.symm |
       exact nwv hadj | exact nwv hadj.symm | exact nwz hadj | exact nwz hadj.symm |
       exact nuv hadj | exact nuv hadj.symm | exact nuz hadj | exact nuz hadj.symm |
       exact nvz hadj | exact nvz hadj.symm
 have hc:({w,u,v,z}:Set V).ncard=4:=by
   simp [Set.ncard_insert_of_notMem,hwu,hwv,hwz,huv,huz,hvz]
 have hb:=(z3d hI).trans H.alpha
 have:=H.a_max
 omega
theorem z172 (T:Frame G 3) {w u v:V} (hw:w∈W T)
   {i j:Fin 3} (hij:i≠j) (hu:u∈T.U i) (hv:v∈T.U j)
   (hwu:¬ G.Adj w u) (hwv:¬ G.Adj w v):False:=by
 obtain ⟨l,hli,hlj⟩:∃ l:Fin 3,l≠i∧l≠j:=by
   fin_cases i <;> fin_cases j <;> decide
 have hdis:=(H.z5e T hij).1
 have hnu:=T.neQ hu.2
 have hnv:=T.neQ hv.2
 apply H.z16b (w:=w) (u:=u) (v:=v) (z:=T.q l) (fun he => H.z184 T hw i (he ▸ hu))
   (fun he => H.z184 T hw j (he ▸ hv)) (T.neQ hw.1 l)
   (fun he => Set.disjoint_left.mp hdis hu (he ▸ hv)) (hnu l) (hnv l)
   hwu hwv (H.z1b5 T hw l) ((H.z5e T hij).2 u hu v hv)
 · intro hh
   exact Set.disjoint_left.mp (H.z5e T hli).1 ⟨hh.symm,hu.2⟩ hu
 · intro hh
   exact Set.disjoint_left.mp (H.z5e T hlj).1 ⟨hh.symm,hv.2⟩ hv
theorem zd4 (T:Frame G 3) {w:V} (hw:w∈W T) :
   ∃ h:Fin 3,∀ i,i≠h → ∀ u∈T.U i,G.Adj w u:=by
 classical
 by_cases hbad:∃ i:Fin 3,¬ ∀ u∈T.U i,G.Adj w u
 · obtain ⟨h,hh⟩:=hbad
   push Not at hh
   obtain ⟨v,hv,hwv⟩:=hh
   refine ⟨h,?_⟩
   intro i hih u hu
   by_contra hwu
   exact H.z172 T hw hih hu hv hwu hwv
 · push Not at hbad
   exact ⟨0,fun i _ => hbad i⟩
theorem zbd (T:Frame G 3) {w:V} (hw:w∈W T) (i:Fin 3)
   (hi:∀ u∈T.U i,G.Adj w u):(T.U i).ncard=1:=by
 obtain ⟨u,hu⟩:=H.z30 T i
 have he:T.U i={u}:=by
   apply Set.eq_singleton_iff_unique_mem.mpr
   refine ⟨hu,?_⟩
   intro v hv
   exact H.z191 T hw hv hu (hi v hv) (hi u hu)
 simp [he]
theorem z166 (T:Frame G 3): 3≤(W T).ncard:=by
 obtain ⟨w,hw⟩:=H.z1b6 T
 obtain ⟨h,hh⟩:=H.zd4 T hw
 have hs:=H.z19e T
 have hmax:=(H.z171 T h).2
 have hc:∀ i,i≠h → (T.U i).ncard=1:=by
   intro i hi
   exact H.zbd T hw i (hh i hi)
 fin_cases h
 · have h1:=hc 1 (by decide)
   have h2:=hc 2 (by decide)
   dsimp at *
   omega
 · have h0:=hc 0 (by decide)
   have h2:=hc 2 (by decide)
   dsimp at *
   omega
 · have h0:=hc 0 (by decide)
   have h1:=hc 1 (by decide)
   dsimp at *
   omega
theorem z196 {x y u v:V} (hxy:x≠y) (huv:u≠v)
   (hxu:G.Adj x u) (hxv:G.Adj x v) (hyu:G.Adj y u) (hyv:G.Adj y v):False:=by
 apply H.cycle
 apply zaf [x,u,y,v] (by simp)
 · simp [hxu.ne,hxv.ne,hyu.ne.symm,hyv.ne,hxy,huv]
 · simpa using And.intro hxu (And.intro hyu.symm hyv)
 · simpa using hxv.symm
theorem contradiction (T:Frame G 3):False:=by
 classical
 let f:W T → Fin 3:=fun w => (H.zd4 T w.property).choose
 have hf:∀ w:W T,∀ i,i≠f w → ∀ u∈T.U i,G.Adj w.val u :=
   fun w => (H.zd4 T w.property).choose_spec
 have hinj:Function.Injective f:=by
   intro w w' he
   apply Subtype.ext
   by_contra hww
   obtain ⟨i,j,hij,hi,hj⟩:∃ i j:Fin 3,i≠j∧i≠f w∧j≠f w:=by
     generalize f w=l
     fin_cases l <;> decide
   obtain ⟨u,hu⟩:=H.z30 T i
   obtain ⟨v,hv⟩:=H.z30 T j
   have huv:u≠v:=fun he => Set.disjoint_left.mp (H.z5e T hij).1 hu (he ▸ hv)
   exact H.z196 hww huv (hf w i hi u hu) (hf w j hj v hv)
     (hf w' i (he ▸ hi) u hu) (hf w' j (he ▸ hj) v hv)
 have hcW:Fintype.card (W T)=(W T).ncard:=by
   rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq]
 have z17a:(W T).ncard≤3:=by
   have hh:=Fintype.card_le_of_injective f hinj
   simpa only [hcW,Fintype.card_fin] using hh
 have z1c6:=H.z166 T
 have hvar:∀ i:Fin 3,∃ w:W T,f w≠i:=by
   intro i
   by_contra hh
   push Not at hh
   have hsub:Subsingleton (W T):=⟨fun w w' => hinj ((hh w).trans (hh w').symm)⟩
   have z1ea:=Fintype.card_le_one_iff_subsingleton.mpr hsub
   rw [hcW] at z1ea
   omega
 have hone:∀ i,(T.U i).ncard=1:=by
   intro i
   obtain ⟨w,hw⟩:=hvar i
   exact H.zbd T w.property i (hf w i hw.symm)
 have h0:=hone 0
 have h1:=hone 1
 have h2:=hone 2
 have hc:=H.z19e T
 omega
end ThreeHyp
end CycleClique
namespace CycleClique
open scoped SimpleGraph
open scoped SimpleGraph
theorem Frame.zd2 {V:Type*} [Fintype V] {G:SimpleGraph V}
   {t:ℕ} (ht:t≤ G.cliqueNum):Nonempty (Frame G t):=by
 obtain ⟨f⟩:=(z17 G t).mpr ht
 exact ⟨⟨f.toEmbedding,fun i j hij => f.toHom.map_rel' (by simpa using hij)⟩⟩
theorem reduced_small_impossible {V:Type*} [Fintype V] {G:SimpleGraph V}
   {k a:ℕ} (hk: 3≤ k) (hk' :k≤4) (ha: 2≤ a) (hak:a≤ k)
   (z79:Fintype.card V=k*a+1) (hα:G.indepNum≤ a)
   (hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G)
   (hexp:∀ I,G.IsIndepSet I → I.Nonempty → 
     k*I.ncard+1≤(z0 G I).ncard):False:=by
 obtain ⟨hl,hu⟩:=counterexample_clique_bound hk ha hak z79 hα hcycle hexp
 have z1a7: 3≤ G.cliqueNum:=(le_max_left _ _).trans hl
 obtain ⟨T⟩:=Frame.zd2 z1a7
 interval_cases k
 · exact (show ThreeHyp G a from ⟨z79,hα,hak,hcycle,hu,hexp⟩).contradiction T
 · have ho:Fintype.card V≤17:=by omega
   by_cases z19b: 4≤ G.cliqueNum
   · obtain ⟨S⟩:=Frame.zd2 z19b
     exact z163 ho hcycle hexp S
   · exact (show FourHyp G from ⟨ho,hcycle,by omega,hexp⟩).contradiction T
theorem reduced_large_impossible {V:Type*} [Fintype V] {G:SimpleGraph V}
   {k a:ℕ} (hk: 3≤ k) (ha: 2≤ a) (hak:a≤ k)
   (z79:Fintype.card V=k*a+1) (hα:G.indepNum≤ a)
   (hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G)
   (hexp:∀ I,G.IsIndepSet I → I.Nonempty → 
     k*I.ncard+1≤(z0 G I).ncard)
   (hnine: 9≤ G.cliqueNum):False:=by
 classical
 obtain ⟨hl,hu⟩:=counterexample_clique_bound hk ha hak z79 hα hcycle hexp
 obtain ⟨Q,hQ⟩:=G.exists_isNClique_cliqueNum
 have hc:(Q:Set V).ncard=G.cliqueNum:=by
   rw [Set.ncard_coe_finset,hQ.card_eq]
 obtain ⟨P,hP⟩:=y0.exists_optimal G (Q:Set V) (k:=k) (by omega)
 have z224:k/2≤ G.cliqueNum:=(le_max_right _ _).trans hl
 have H:LargeSystem G (Q:Set V) k P :=
   ⟨hP,hQ.isClique,hcycle,by omega,by omega,by omega,by omega,hα.trans hak,hexp⟩
 exact H.contradiction
end CycleClique
namespace CycleClique
open scoped SimpleGraph
theorem RamseyProperty.z180 {m n N:ℕ} (h:RamseyProperty m n N)
   {V:Type*} [Fintype V] (hNV:N≤ Fintype.card V) (G:SimpleGraph V) :
   SimpleGraph.cycleGraph m⊑G∨(⊤ :SimpleGraph (Fin n))⊑Gᶜ:=by
 classical
 obtain ⟨f⟩:=Function.Embedding.nonempty_of_card_le (show Fintype.card (Fin N) ≤
   Fintype.card V by simpa using hNV)
 let H:=G.comap f
 have hc:H⊑G:=⟨⟨⟨f,fun {a b} hab => hab⟩,f.injective⟩⟩
 have hcc:Hᶜ⊑Gᶜ:=by
   refine ⟨⟨⟨f,fun {a b} hab => ?_⟩,f.injective⟩⟩
   exact ⟨fun heq => hab.1 (f.injective heq),hab.2⟩
 rcases h H with hcycle | z20
 · exact Or.inl (hcycle.trans hc)
 · exact Or.inr (z20.trans hcc)
def z8d (a k:ℕ):SimpleGraph (Fin a × Fin k) where
 Adj u v:=u.1=v.1∧u.2≠v.2
 symm:=⟨fun _ _ h => ⟨h.1.symm,Ne.symm h.2⟩⟩
 loopless:=⟨fun _ h => h.2 rfl⟩
theorem ze4 {a k:ℕ} {u v:Fin a × Fin k}
   (p:(z8d a k).Walk u v):u.1=v.1:=by
 induction p with
 | nil => rfl
 | cons h p ih => exact h.1.trans ih
theorem z100 {m a k:ℕ} (hm: 0 < m) (hk:k < m) :
   ¬ SimpleGraph.cycleGraph m⊑z8d a k:=by
 rintro ⟨f⟩
 let x:Fin m:=⟨0,hm⟩
 have z1c3:∀ i:Fin m,(f x).1=(f i).1:=by
   intro i
   obtain ⟨p⟩:=SimpleGraph.cycleGraph_preconnected x i
   exact ze4 (p.map f.toHom)
 have hinj:Function.Injective (fun i:Fin m => (f i).2):=by
   intro i j hij
   apply f.injective
   exact Prod.ext ((z1c3 i).symm.trans (z1c3 j)) hij
 have hc:=Fintype.card_le_of_injective _ hinj
 simp only [Fintype.card_fin] at hc
 omega
theorem zba {n a k:ℕ} (ha:a < n) :
   ¬ (⊤ :SimpleGraph (Fin n))⊑(z8d a k)ᶜ:=by
 rintro ⟨f⟩
 have hinj:Function.Injective (fun i:Fin n => (f i).1):=by
   intro i j hij
   by_contra hne
   have hadj:=f.toHom.map_adj (show (⊤ :SimpleGraph (Fin n)).Adj i j from hne)
   apply hadj.2
   exact ⟨hij,fun heq => hne (f.injective (Prod.ext hij heq))⟩
 have hc:=Fintype.card_le_of_injective _ hinj
 simp only [Fintype.card_fin] at hc
 omega
theorem ze1 {m n:ℕ} (hm: 1≤ m) (hn: 1≤ n) :
   ¬ RamseyProperty m n ((m - 1)*(n - 1)):=by
 intro h
 have hd:=h.z180 (G:=z8d (n - 1) (m - 1)) (by
   simp only [Fintype.card_prod,Fintype.card_fin]
   exact le_of_eq (Nat.mul_comm _ _))
 rcases hd with hc | hk
 · exact z100 (by omega) (by omega) hc
 · exact zba (by omega) hk
theorem ramsey_property_lower_bound {m n N:ℕ} (hm: 1≤ m) (hn: 1≤ n)
   (hN:RamseyProperty m n N):(m - 1)*(n - 1)+1≤ N:=by
 by_contra hnle
 exact ze1 hm hn (hN.mono (by omega))
end CycleClique
namespace CycleClique
open scoped SimpleGraph
theorem z162 (k:ℕ):RamseyProperty (k+1) 1 1:=by
 intro G
 right
 refine ⟨⟨⟨id,?_⟩,Function.injective_id⟩⟩
 intro a b hab
 exact False.elim (hab (Subsingleton.elim a b))
theorem z16e (k:ℕ):RamseyProperty (k+1) 2 (k+1):=by
 classical
 intro G
 by_cases z19a:(⊤ :SimpleGraph (Fin 2))⊑Gᶜ
 · exact Or.inr z19a
 left
 have hi:=(z8b G 1).mp z19a
 have htop:∀ a b,a≠b → G.Adj a b:=by
   intro a b hab
   by_contra hn
   have hI:G.IsIndepSet {a,b}:=by
     intro x hx y hy hxy z70
     simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hx hy
     rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
     · exact hxy rfl
     · exact hn z70
     · exact hn z70.symm
     · exact hxy rfl
   have hc:=z3d hI
   rw [Set.ncard_pair hab] at hc
   omega
 exact ⟨⟨⟨id,fun {a b} hab => htop a b hab.ne⟩,Function.injective_id⟩⟩
theorem z116 {V:Type*} [Fintype V] {G:SimpleGraph V}
   {k b:ℕ} (hR:RamseyProperty (k+1) (b+1) (k*b+1))
   (hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G) (hα:G.indepNum≤ b) :
   Fintype.card V≤ k*b:=by
 by_contra hn
 rcases hR.z180 (by omega) G with hc | hb
 · exact hcycle hc
 · exact (z8b G b).mpr hα hb
theorem z113 {k a:ℕ} (G:SimpleGraph (Fin (k*a+1)))
   (hcycle:¬ SimpleGraph.cycleGraph (k+1)⊑G) (hα:G.indepNum≤ a)
   (z1c9:∀ b < a,RamseyProperty (k+1) (b+1) (k*b+1))
   {I:Set (Fin (k*a+1))} (hI:G.IsIndepSet I) (hne:I.Nonempty) :
   k*I.ncard+1≤(z0 G I).ncard:=by
 classical
 have hr: 0 < I.ncard:=(Set.ncard_pos).mpr hne
 have hrle:I.ncard≤ a:=(z3d hI).trans hα
 let S:=(z0 G I)ᶜ
 have z19d:=z1c9 (a - I.ncard) (by omega)
 have z78:=z5c hI (Set.subset_univ I)
 rw [z31] at z78
 have hαS:(G.induce S).indepNum≤ a - I.ncard:=by
   have heq:Set.univ \ z0 G I=S:=(Set.compl_eq_univ_sdiff _).symm
   rw [heq] at z78
   change independence G S≤ a - I.ncard
   omega
 have hcS:¬ SimpleGraph.cycleGraph (k+1)⊑G.induce S:=by
   intro hc
   exact hcycle (hc.trans (SimpleGraph.Embedding.induce S).isContained)
 have hc:=z116 z19d hcS hαS
 rw [← Nat.card_eq_fintype_card,Nat.card_coe_set_eq] at hc
 have hsum:=Set.ncard_add_ncard_compl (z0 G I)
 rw [Nat.card_eq_fintype_card,Fintype.card_fin] at hsum
 have hmul:k*(a - I.ncard)+k*I.ncard=k*a:=by
   rw [← Nat.mul_add,Nat.sub_add_cancel hrle]
 change S.ncard≤ k*(a - I.ncard) at hc
 change (z0 G I).ncard+S.ncard=k*a+1 at hsum
 omega
theorem minimal_expanding_counterexample {k a₀:ℕ} (ha₀: 2≤ a₀) (ha₀k:a₀≤ k)
   (hfailure:¬ RamseyProperty (k+1) (a₀+1) (k*a₀+1)) :
   ∃ a,2≤ a∧a≤ k ∧ ∃ G:SimpleGraph (Fin (k*a+1)),
     (¬ SimpleGraph.cycleGraph (k+1)⊑G)∧G.indepNum≤ a ∧
     ∀ I,G.IsIndepSet I → I.Nonempty → k*I.ncard+1≤(z0 G I).ncard:=by
 classical
 let A:Set ℕ:={a | 2≤ a∧a≤ k ∧
   ¬ RamseyProperty (k+1) (a+1) (k*a+1)}
 have hA:A.Nonempty:=⟨a₀,ha₀,ha₀k,hfailure⟩
 let a:=sInf A
 have z1f9:a∈A:=Nat.sInf_mem hA
 obtain ⟨ha,hak,hfail⟩:=z1f9
 have z19d:∀ b < a,RamseyProperty (k+1) (b+1) (k*b+1):=by
   intro b hba
   rcases b with _ | b
   · simpa using z162 k
   rcases b with _ | b
   · simpa using z16e k
   by_contra hn
   have hbA:b+2∈A:=⟨by omega,by omega,hn⟩
   have:=Nat.sInf_le hbA
   change a≤ b+2 at this
   omega
 unfold RamseyProperty at hfail
 obtain ⟨G,hn⟩:=not_forall.mp hfail
 obtain ⟨hcycle,z19a⟩:=not_or.mp hn
 have hα:=(z8b G a).mp z19a
 exact ⟨a,ha,hak,G,hcycle,hα,
   fun I hI hne => z113 G hcycle hα z19d hI hne⟩
end CycleClique
end OAI
namespace OAI.CycleClique
end OAI.CycleClique
namespace OAI.CycleClique
open scoped SimpleGraph
-- The finite certificate obligation remains explicit,not assumed as an axiom.
end OAI.CycleClique
section
/- Adapted from OpenAI math (Apache-2.0), revision
3344da59991ed94f9ba711217b29c1d760badfa6,
lean/OAI/Combinatorics/Ramsey/CycleClique and
preprints/Cycle-clique-Ramsey-numbers-September-25-2026/verification/code.
Certificate reconstruction: explicit witnesses are computed, then kernel-checked.
-/
namespace OAI.CycleClique
open scoped SimpleGraph
def y5 (k t : ℕ) (D : List (List ℕ)) : Prop :=
  ∃ C : y2, C.Valid k t (patternOrder D) (patternClique D)
    (patternEdges D) (patternAmount D) (patternEdgeCount D) []
theorem y5.impossible {V : Type*} [Fintype V] {G : SimpleGraph V}
    {Q : Set V} {k t : ℕ} {D : List (List ℕ)} (hD : y5 k t D)
    (H : FiniteHyp G k t) (P : y0 G Q) (hP : P.Optimal k)
    (hQ : G.IsClique Q) (hc : Q.ncard = t)
    (hprofile : List.Forall₂ (y8 Q) P.chains D) : False := by
  obtain ⟨C,hC⟩ := hD
  obtain ⟨v,hv⟩ := Set.nonempty_of_ncard_ne_zero (s := Q) (by have := H.ht; omega)
  obtain ⟨_,ha,he,_⟩ := P.profile_parameters hprofile
  let O : OriginalSystem G Q k t (patternAmount D) (patternEdgeCount D) :=
    ⟨P,hP,hQ,hc,ha.symm,he.symm⟩
  exact C.sound H O (P.labelState hQ hprofile v) (by constructor <;> simp) hC
theorem finite_verified_of_patterns {V : Type*} [Fintype V] {G : SimpleGraph V}
    {Q : Set V} {k t : ℕ} (H : FiniteHyp G k t) (hQ : G.IsClique Q)
    (hc : Q.ncard = t)
    (hverified : ∀ D ∈ y7 t (k-t) [], y5 k t D) : False := by
  obtain ⟨P,hP⟩ := y0.exists_optimal G Q (k := k) (by have := H.htk; omega)
  obtain ⟨R,D,hD,hs,hn,ha,he⟩ := P.canonical_realization
  have hR := y0.optimal_of_same hP ha he
  obtain ⟨ht,hL,he',hpos⟩ := R.profile_parameters hD
  have hbudget : patternAmount D ≤ k-t := by
    have hp := hR.1
    rw [←hL, hc] at hp
    omega
  have hm := mem_patternChoices (ht.trans hc) hbudget hpos hs hn (lower := []) (fun A _ => le_of_not_gt (by intro h; cases h))
  exact (hverified D hm).impossible H R hR hQ hc hD
namespace Compact
abbrev Chain := List Nat × Nat
def mask (xs : List Nat) : Nat := xs.foldl (fun m x => m ||| (1 <<< x)) 0
def adj (q : Nat) (E : List (Nat × Nat)) (x : Nat) : List Nat :=
  E.foldr (fun (a,b) s =>
    if q.testBit a && q.testBit b then s else
    if a == x then b::s else if b == x then a::s else s) []
def walks (q : Nat) (E : Array (List Nat)) (start : Nat) :
    Nat → Nat → List Nat → Nat → List Chain
  | 0, _, _, _ => []
  | fuel+1, x, path, used =>
    (if q.testBit x && start < x then [(path.reverse,used)] else []) ++
    ((E[x]?.getD []).filter (fun y => !used.testBit y)).flatMap
      (fun y => walks q E start fuel y (y::path) (used ||| (1 <<< y)))
def insertBy (x : Chain) : List Chain → List Chain
  | [] => [x]
  | y::ys => if y.1.length < x.1.length then x::y::ys else y::insertBy x ys
def improves (k t L e : Nat) (C : List (List Nat)) : Bool :=
  let A := C.flatten.length-t
  let N := t-C.length
  let v := t-(C.filter (fun c => c.length == 1)).length
  (A < k+1-t && (L < A || (L == A && N < e))) ||
  (k+1-t ≤ A && A ≤ k+1-v)
def firstSome {α β : Type} (f : α → Option β) : List α → Option β
  | [] => none
  | x::xs => match f x with
    | some y => some y
    | none => firstSome f xs
def select (k t L e : Nat) (q : List Nat) (cs : Array (List Chain)) :
    Nat → Nat → List (List Nat) → Option (List (List Nat))
  | 0, _, _ => none
  | fuel+1, used, C =>
    match q.find? (fun x => !used.testBit x) with
    | none => if improves k t L e C then some C else none
    | some x => firstSome (fun (c,m) =>
        if m.testBit x && m &&& used == 0 then
          select k t L e q cs fuel (used ||| m) (c::C) else none) (cs[x]?.getD [])
def system (k t L e n : Nat) (q : List Nat) (E : List (Nat × Nat))
    (i j d : Nat) : Option (List (List Nat)) :=
  let F := augmentedEdges n E i j d
  let qm := mask q
  let ad := ((List.range (n+d)).map (adj qm F)).toArray
  let cs := q.flatMap (fun x => walks qm ad x (n+d+1) x [x] (1 <<< x))
  let cs := cs.foldr insertBy []
  let buckets := ((List.range n).map (fun x => (cs.filter (fun c => c.2.testBit x)) ++ [([x],1 <<< x)])).toArray
  select k t L e q buckets (q.length+1) 0 []
def neighbors (E : List (Nat × Nat)) (x : Nat) : List Nat :=
  E.foldr (fun (a,b) s => if a == x then b::s else if b == x then a::s else s) []
def path (E : List (Nat × Nat)) (target : Nat) : Nat → Nat → Nat → Option (List Nat)
  | 0, x, _ => if x == target then some [x] else none
  | fuel+1, x, used => if x == target then none else
      firstSome (fun y => if used.testBit y then none else
        (path E target fuel y (used ||| (1 <<< y))).map (x::·)) (neighbors E x)
def direct (k t L e n : Nat) (q : List Nat) (E : List (Nat × Nat))
    (i j d : Nat) : y2 :=
  match system k t L e n q E i j d with
  | some C => .system C
  | none => .cycle ((path E j (k-d) i (1 <<< i)).getD [] ++
      (List.range' n d).reverse)
inductive Hint where
  | packing (options : List (Nat × List Nat))
  | forbid (i j d : Nat) (reason next : Hint)
def labelList (n z : Nat) : List Nat := (List.range n).filter z.testBit
def labels (n z : Nat) : Finset Nat := (labelList n z).toFinset
def growBall (k t n : Nat) : ya → List Nat → ya
  | p, [] => p
  | p, z::zs =>
    let Z := labels n z
    let b := max p.size (k*p.weight+1+Z.card-n)
    let u := max p.weight (1+(if t < b then 1 else 0)+(if max k (2*t) < b then 1 else 0))
    let u := if t ≤ p.size && n+t ≤ k+1+Z.card then max u 2 else u
    growBall k t n (.succ p Z b u) zs
def option (k t n : Nat) (o : Nat × List Nat) : yb :=
  match o.2 with
  | [] => .singleton o.1
  | z::zs =>
    let Z := labels n z
    let b := k+1+Z.card-n
    .ball o.1 (growBall k t n (.zero Z b (if t ≤ b then 2 else 1)) zs)
abbrev Need := Nat × Nat × Nat
def key (i j d : Nat) : Need := (min i j,max i j,d)
def ballNeeds (n i : Nat) : Nat → List Nat → List Need
  | _, [] => []
  | r, z::zs => (labelList n z).flatMap (fun j =>
      (if r == 0 then [0] else List.range' 1 r).map (fun d => key i j d)) ++
    ballNeeds n i (r+1) zs
def needs (n : Nat) (P : List (Nat × List Nat)) : List Need :=
  (P.flatMap (fun o => ballNeeds n o.1 0 o.2) ++ P.flatMap (fun a => P.flatMap (fun b =>
    if a.1 < b.1 then
      (if a.2.length+b.2.length == 0 then [0] else
        List.range' 1 (a.2.length+b.2.length)).map (fun d => key a.1 b.1 d)
    else [])))
def dedup : List Need → List Need
  | [] => []
  | x::xs => let r := dedup xs; if r.contains x then r else x::r
end Compact
end OAI.CycleClique
end
section
/- Bulk edits of OpenAI's CycleClique finite systems (Apache-2.0), pin
3344da59991ed94f9ba711217b29c1d760badfa6. Interval descriptors are checked;
vertex lists occur only behind the existential in the proof. -/
namespace OAI.CycleClique.Edit
structure Run where
  lo : Nat
  len : Nat -- number of edges
  rev : Bool
  deriving DecidableEq
namespace Run
def hi (p : Run) := p.lo+p.len
def a (p : Run) := if p.rev then p.hi else p.lo
def b (p : Run) := if p.rev then p.lo else p.hi
def word (p : Run) := (2^p.len-1) <<< p.lo
def raw (p : Run) := List.range' p.lo (p.len+1)
def xs (p : Run) := if p.rev then p.raw.reverse else p.raw
@[simp] theorem size (p : Run) : p.xs.length = p.len+1 := by simp [xs,raw]; split <;> simp
@[simp] theorem mem {p : Run} {x : Nat} : x ∈ p.xs ↔ p.lo ≤ x ∧ x ≤ p.hi := by
  simp only [xs]; split <;> simp [raw,List.mem_range'_1,hi] <;> omega
@[simp] theorem nodup (p : Run) : p.xs.Nodup := by unfold xs; split <;> simp [raw,List.nodup_range']
@[simp] theorem ends (p : Run) : p.xs.head? = some p.a ∧ p.xs.getLast? = some p.b := by
  simp only [xs,a,b]; split <;> simp [raw, List.head?_range', List.getLast?_range',hi]
theorem bit {p : Run} {x : Nat} (hx : p.lo ≤ x) (hy : x < p.hi) : p.word.testBit x := by
  simp [word,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one,hx,show x-p.lo<p.len by unfold hi at hy; omega]
theorem chain {R : Nat → Nat → Prop} (sym : ∀ ⦃a b⦄, R a b → R b a) (p : Run)
    (h : ∀ x, p.lo ≤ x → x < p.hi → R x (x+1)) : p.xs.IsChain R := by
  have aux : ∀ s l, (∀ x, s ≤ x → x < s+l → R x (x+1)) → (List.range' s (l+1)).IsChain R := by
    intro s l
    induction l generalizing s with
    | zero => simp
    | succ l ih =>
      intro hh
      rw [List.range'_succ]; apply List.IsChain.cons
      · exact ih (s+1) (fun x h₁ h₂ => hh x (by omega) (by omega))
      · intro y hy; simp [List.range'_succ] at hy; subst y; exact hh s (by omega) (by omega)
  have hh := aux _ _ h
  unfold xs; split
  · exact List.isChain_reverse.mpr (hh.imp (fun _ _ e => sym e))
  · exact hh
end Run
def AllEdges (n B : Nat) (q : Finset Nat) (E : List (Nat × Nat)) :=
  ∀ x ∈ List.range n, B.testBit x = true → labelAdj E x (x+1) ∧ (x ∉ q ∨ x+1 ∉ q)
instance {n B q E} : Decidable (AllEdges n B q E) := by unfold AllEdges; infer_instance
def Fits (k t L e size num ones : Nat) : Prop :=
  let A := size-t
  let N := t-num
  let v := t-ones
  (A < k+1-t ∧ (L < A ∨ (L=A ∧ N<e))) ∨ (k+1-t ≤ A ∧ A ≤ k+1-v)
instance {k t L e s c o} : Decidable (Fits k t L e s c o) := by unfold Fits; infer_instance
def Checks (k t L e n B i j d : Nat) (q : Finset Nat) (u v : Run) (rest : List Run) :=
  let ps := u::v::rest
  u.a = i ∧ v.a = j ∧ (d≠0 ∨ i∉q ∨ j∉q) ∧
  (∀ p ∈ ps, p.hi < n ∧ p.word &&& B = p.word ∧ p.b ∈ q) ∧
  (∀ p ∈ rest, p.a ∈ q) ∧
  ps.Pairwise (fun p r => p.hi < r.lo ∨ r.hi < p.lo) ∧
  (∀ x ∈ q, ∃ p ∈ ps, p.lo ≤ x ∧ x ≤ p.hi) ∧
  Fits k t L e ((ps.map (fun p => p.len+1)).sum+d) (rest.length+1) (rest.countP (fun p => decide (p.len=0)))
instance {k t L e n B i j d q u v r} : Decidable (Checks k t L e n B i j d q u v r) := by unfold Checks; dsimp only; infer_instance
private theorem disj {ps : List Run} (h : ps.Pairwise (fun p r => p.hi < r.lo ∨ r.hi < p.lo)) :
    (ps.map Run.xs).flatten.Nodup := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    obtain ⟨hh,ht⟩ := List.pairwise_cons.mp h
    simp only [List.map_cons,List.flatten_cons,List.nodup_append,Run.nodup,true_and]
    refine ⟨ih ht, ?_⟩; intro x hx y hy eq; subst y
    obtain ⟨c,hc,hy⟩ := List.mem_flatten.mp hy
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hc
    have := hh r hr; simp only [Run.mem] at hx hy; omega
private theorem pathAdj (xs : List Nat) : xs.IsChain (labelAdj (pathEdges xs)) := by
  induction xs using List.twoStepInduction with
  | nil => simp
  | singleton => simp
  | cons_cons x y l _ ih =>
    rw [List.isChain_cons_cons]; constructor
    · exact Or.inl (List.mem_cons_self ..)
    · apply (ih y).imp; intro a b h; rcases h with h|h
      · exact Or.inl (List.mem_cons_of_mem _ h)
      · exact Or.inr (List.mem_cons_of_mem _ h)
private theorem pathPos (q : Finset Nat) (i j : Nat) (I : List Nat) (hi : ∀ x ∈ I, x ∉ q)
    (h : I ≠ [] ∨ i ∉ q ∨ j ∉ q) : (i :: I ++ [j]).IsChain (fun x y => x ∉ q ∨ y ∉ q) := by
  induction I generalizing i with
  | nil => simpa using h
  | cons a l ih =>
    change (i :: a :: (l ++ [j])).IsChain _
    rw [List.isChain_cons_cons]
    exact ⟨Or.inr (hi a (by simp)), ih a (fun x hx => hi x (by simp [hx])) (Or.inr (Or.inl (hi a (by simp))))⟩
theorem checks_sound {k t L e n B i j d q E u v r} (base : AllEdges n B q E)
    (qb : ∀ x ∈ q, x<n) (h : Checks k t L e n B i j d q u v r) (M : y4) :
    ∃ C, (y2.system C).Valid k t (n+d) q (augmentedEdges n E i j d) L e M := by
  obtain ⟨hi,hj,hpos,hp,hr,hdis,hcov,hfit⟩ := h
  let ps := u::v::r
  let I := List.range' n d
  let F := augmentedEdges n E i j d
  let pos := fun x y : Nat => x ∉ q ∨ y ∉ q
  let J := u.xs.reverse ++ I ++ v.xs
  let rest := r.map Run.xs
  have ub : u ∈ ps := by simp [ps]
  have vb : v ∈ ps := by simp [ps]
  have link (p : Run) (hm : p ∈ ps) : p.xs.IsChain (labelAdj F) ∧ p.xs.IsChain pos := by
    have H (x) (hl : p.lo≤x) (hh : x<p.hi) := base x (List.mem_range.mpr (lt_trans hh (hp p hm).1)) (by
      have := congrArg (fun w : Nat => w.testBit x) (hp p hm).2.1
      simpa [Nat.testBit_and,p.bit hl hh] using this)
    constructor
    · apply p.chain (fun _ _ h => Or.symm h); intro x hl hh; rcases (H x hl hh).1 with h|h
      · exact Or.inl (List.mem_append_left _ h)
      · exact Or.inr (List.mem_append_left _ h)
    · exact p.chain (fun _ _ h => Or.symm h) (fun x hl hh => (H x hl hh).2)
  obtain ⟨ut,hu⟩ := List.head?_eq_some_iff.mp ((u.ends.1).trans (congrArg some hi))
  obtain ⟨vt,hv⟩ := List.head?_eq_some_iff.mp ((v.ends.1).trans (congrArg some hj))
  have aug : (i :: I ++ [j]).IsChain (labelAdj F) := by
    apply (pathAdj (pathLabels n i j d)).imp; intro a b h; rcases h with h|h
    · exact Or.inl (List.mem_append_right _ h)
    · exact Or.inr (List.mem_append_right _ h)
  have ip : (i :: I ++ [j]).IsChain pos := pathPos _ _ _ _ (by
    intro x hx hq; have := qb x hq; have := (List.mem_range'_1.mp hx).1; omega) (by
    rcases hpos with h|h; · left; intro hz; have := congrArg List.length hz; simp [I] at this; contradiction
    · exact Or.inr h)
  have jc : J.IsChain (labelAdj F) ∧ J.IsChain pos := by
    obtain ⟨a,b⟩ := link u ub; obtain ⟨c,f⟩ := link v vb
    rw [hu] at a b; rw [hv] at c f; unfold J; rw [hu,hv]
    exact ⟨isChain_bridge (fun _ _ h => Or.symm h) a c aug,isChain_bridge (fun _ _ h => Or.symm h) b f ip⟩
  have ne (p : Run) : p.xs ≠ [] := by intro e; have := p.size; rw [e] at this; simp at this
  have hJ : 1 < J.length := by simp [J,I]; omega
  have old {x} (hx : x ∈ (ps.map Run.xs).flatten) : x<n := by
    obtain ⟨c,hc,hx⟩ := List.mem_flatten.mp hx; obtain ⟨p,hm,rfl⟩ := List.mem_map.mp hc
    exact lt_of_le_of_lt (Run.mem.mp hx).2 (hp p hm).1
  have memJ (x) : x ∈ (J::rest).flatten ↔ x ∈ (ps.map Run.xs).flatten ∨ x ∈ I := by
    simp only [J,rest,ps,List.map_cons,List.flatten_cons,List.mem_append,List.mem_reverse]; tauto
  refine ⟨J::rest, ⟨?_,?_,?_,?_⟩,?_⟩
  · simp only [List.flatten_cons,J]; apply nodup_bridge
    · simpa [ps,rest,List.append_assoc] using disj hdis
    · exact List.nodup_range'
    · intro x hx hy; have := (List.mem_range'_1.mp hx).1
      have := old (by simpa [ps,rest,List.append_assoc] using hy); omega
  · intro x hx; rcases (memJ x).mp hx with h|h
    · have := old h; omega
    · exact (List.mem_range'_1.mp h).2
  · intro c hc; rcases List.mem_cons.mp hc with rfl|hc
    · refine ⟨by intro h; rw [h] at hJ; contradiction,jc.1,jc.2,?_,?_⟩
      · simpa [J,List.append_assoc,List.head?_append_of_ne_nil _ (List.reverse_ne_nil_iff.mpr (ne u)),List.head?_reverse,u.ends.2] using (hp u ub).2.2
      · simpa [J,List.getLast?_append_of_ne_nil _ (ne v),v.ends.2] using (hp v vb).2.2
    · obtain ⟨p,hm,rfl⟩ := List.mem_map.mp hc; have hm' : p ∈ ps := by simp [ps,hm]
      exact ⟨ne p,(link p hm').1,(link p hm').2,by simpa [p.ends.1] using hr p hm,by simpa [p.ends.2] using (hp p hm').2.2⟩
  · intro x hx; apply (memJ x).mpr; left; obtain ⟨p,hm,hx⟩ := hcov x hx
    exact List.mem_flatten.mpr ⟨p.xs,List.mem_map.mpr ⟨p,hm,rfl⟩,Run.mem.mpr hx⟩
  · change Fits k t L e _ _ _
    have hs : (J::rest).flatten.length = ((ps.map (fun p => p.len+1)).sum+d) := by
      simp [J,ps,rest,I,List.length_flatten,List.map_map,Function.comp_def]; omega
    have ho : ((J::rest).filter (fun c => decide (c.length=1))).length = r.countP (fun p => decide (p.len=0)) := by
      rw [←List.countP_eq_length_filter,List.countP_cons]; simp [show J.length ≠ 1 by omega,rest,List.countP_map,Function.comp_def]
    rw [hs,ho]; simpa [rest,ps] using hfit
end OAI.CycleClique.Edit
end
section
/- Based on OpenAI math, Apache-2.0, 3344da59991ed94f9ba711217b29c1d760badfa6. -/
namespace OAI.CycleClique.Edit.Word
def left (R x : Nat) := (R <<< 1).testBit x
@[simp] theorem left_zero (R) : left R 0 = false := by simp [left,Nat.testBit_shiftLeft]
@[simp] theorem left_succ (R x) : left R (x+1) = R.testBit x := by simp [left,Nat.testBit_shiftLeft]
def cnt (a l : Nat) (f : Nat → Bool) := ((List.range' a l).countP f)
theorem cnt_split (a l m) (f : Nat → Bool) : cnt a (l+m) f = cnt a l f + cnt (a+l) m f := by
  unfold cnt; rw [← List.range'_append,List.countP_append]; simp 
theorem cnt_full {a l} {f : Nat → Bool} (h : ∀ x, a ≤ x → x < a+l → f x) : cnt a l f = l := by
  have hh : ∀ x ∈ List.range' a l, f x := fun x hx => h x (List.mem_range'_1.mp hx).1 (List.mem_range'_1.mp hx).2
  simpa [cnt] using List.countP_eq_length.mpr hh
theorem cnt_empty {a l} {f : Nat → Bool} (h : ∀ x, a ≤ x → x < a+l → f x = false) : cnt a l f = 0 := by
  apply List.countP_eq_zero.mpr; intro x hx; simp [h x (List.mem_range'_1.mp hx).1 (List.mem_range'_1.mp hx).2]
def Sep (p r : Run) := p.hi < r.lo ∨ r.hi < p.lo
structure Tile (orient : Nat → Nat → Bool) (a n R : Nat) (A : Nat → Bool) (p : Run) : Prop where
  low : a ≤ p.lo
  high : p.hi < n
  direction : p.rev = orient p.lo p.hi
  first : left R p.lo = false
  last : R.testBit p.hi = false
  edge : ∀ x, p.lo ≤ x → x < p.hi → R.testBit x
  active : ∀ x, p.lo ≤ x → x ≤ p.hi → A x
def isolated (R : Nat) (A : Nat → Bool) (x : Nat) := A x && !(left R x || R.testBit x)
structure Partition (orient : Nat → Nat → Bool) (a n R : Nat) (A : Nat → Bool) (ps : List Run) : Prop where
  tiles : ∀ p ∈ ps, Tile orient a n R A p
  disj : ps.Pairwise Sep
  cover : ∀ x, a ≤ x → x < n → A x → ∃ p ∈ ps, p.lo ≤ x ∧ x ≤ p.hi
  vertices : (ps.map (fun p => p.len+1)).sum = cnt a (n-a) A
  edges : (ps.map Run.len).sum = cnt a (n-a) R.testBit
  singles : ∀ T : Nat → Bool, ps.countP (fun p => p.len == 0 && T p.lo) = cnt a (n-a) (fun x => isolated R A x && T x)
theorem partition (orient : Nat → Nat → Bool) {n R : Nat} {A : Nat → Bool} (inc : ∀ x, left R x || R.testBit x → A x)
    (bound : ∀ x, R.testBit x → x+1<n) (a : Nat) (start : left R a = false) :
    ∃ ps, Partition orient a n R A ps := by
  classical
  by_cases ha : a<n
  · have ex : ∃ y, a ≤ y ∧ R.testBit y = false := ⟨n-1,by omega,by
      cases hh : R.testBit (n-1) <;> simp_all; have := bound _ hh; omega⟩
    let b := Nat.find ex
    obtain ⟨hab, hb⟩ := Nat.find_spec ex
    change a ≤ b at hab; change R.testBit b = false at hb
    have bn:b<n := by have := Nat.find_min' ex (show a ≤ n-1 ∧ R.testBit (n-1) = false from ⟨by omega, by
                              cases hh : R.testBit (n-1) <;> simp_all; have := bound _ hh; omega⟩); dsimp [b]; omega
    have he (x) (hx : a≤x) (hy : x<b) : R.testBit x := by
      have := Nat.find_min ex hy; cases h : R.testBit x <;> simp_all
    obtain ⟨rs,h⟩ := partition orient inc bound (b+1) (by simpa using hb)
    let p := Run.mk a (b-a) (orient a b)
    have ph : p.hi=b := by simp [p,Run.hi]; omega
    have ps : p.lo=a := rfl
    have plen : p.len=b-a := rfl
    have spl (f : Nat → Bool) : cnt a (n-a) f = cnt a (b-a+1) f + cnt (b+1) (n-(b+1)) f := by
      rw [show n-a=b-a+1+(n-(b+1)) by omega,cnt_split]; congr 2 <;> omega
    have ce : cnt a (b-a+1) R.testBit = b-a := by
      rw [cnt_split,cnt_full (fun x hx hy => he x hx (by omega))]; simp [cnt,show a+(b-a)=b by omega,hb]
    have extend (r) (hr : r∈rs) : Tile orient a n R A r :=
      {h.tiles r hr with low := le_trans (by omega : a≤b+1) (h.tiles r hr).low}
    by_cases act : A a
    · have active (x) (hx : a≤x) (hy : x≤b) : A x := by
        rcases eq_or_lt_of_le hx with rfl|hx; exact act
        apply inc; cases x with
        | zero => omega
        | succ y => simp [he y (by omega) (by omega)]
      have ti : Tile orient a n R A p := by
        constructor <;> simp only [ps,ph] <;> first | assumption | rfl | omega
      refine ⟨p::rs,?_,?_,?_,?_,?_,?_⟩
      · intro r hr; rcases List.mem_cons.mp hr with rfl|hr; exact ti; exact extend r hr
      · exact List.pairwise_cons.mpr ⟨fun r hr => Or.inl (by have := (h.tiles r hr).low; omega),h.disj⟩
      · intro x hx hn hA; by_cases hy : x≤b
        · exact ⟨p,by simp,by omega,by omega⟩
        · obtain ⟨r,hr,hh⟩ := h.cover x (by omega) hn hA; exact ⟨r,by simp [hr],hh⟩
      · rw [spl,cnt_full (fun x hx hy => active x hx (by omega))]; simp [h.vertices,plen]
      · rw [spl,ce]; simp [h.edges,plen]
      · intro T; rw [spl,List.countP_cons,h.singles]; by_cases eq : a=b
        · cases ht : T a <;> simp [ht,ps,←eq,plen,cnt,isolated,act,start,←eq ▸ hb,Nat.add_comm]
        · simp [plen,show b-a≠0 by omega]; apply cnt_empty
          intro x hx hy; by_cases lt : x<b
          · simp [isolated,he x hx lt]
          · obtain ⟨y,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show x≠0 by omega)
            simp [isolated,he y (by omega) (by omega)]
    · have eq:b=a := by by_contra hh; exact act (inc a (by simp [he a le_rfl (by omega)]))
      have ab:b-a=0 := by omega
      refine ⟨rs,extend,h.disj,?_,?_,?_,?_⟩
      · intro x hx hn hA; apply h.cover x _ hn hA; have hxne : x≠a := fun e => act (e ▸ hA); omega
      · rw [spl]; simpa [cnt,ab,act] using h.vertices
      · rw [spl,ce]; simpa [ab] using h.edges
      · intro T; rw [spl]; simpa [cnt,ab,isolated,act] using h.singles T
  · refine ⟨[],by simp,by simp,?_,?_,?_,?_⟩
    · intro x hx hn; omega
    all_goals simp [cnt,show n-a=0 by omega]
termination_by n-a
decreasing_by omega
end OAI.CycleClique.Edit.Word
end
section
/- Based on OpenAI math, Apache-2.0, 3344da59991ed94f9ba711217b29c1d760badfa6. -/
namespace OAI.CycleClique.Edit.Word
def P (i j : Nat) := 2^i ||| 2^j
def U (R : Nat) := R ||| (R <<< 1)
def two (R : Nat) := R &&& (R <<< 1)
def active (Q R i j : Nat) := Q ||| U R ||| P i j
def deg1 (R i j : Nat) := (U R ^^^ two R) ^^^ P i j
def span (i j : Nat) := (2^(j-i)-1) <<< i
def single (Q R i j : Nat) := Q ^^^ (Q &&& (U R ||| P i j))
def pop : Nat → Nat → Nat
  | 0,_ => 0
  | l+1,z => (if z.testBit 0 then 1 else 0) + pop l (z >>> 1)
theorem pop_eq (n z) : pop n z = cnt 0 n z.testBit := by
  induction n generalizing z with
  | zero => simp [pop,cnt]
  | succ n ih =>
    rw [pop,ih]; unfold cnt; rw [List.range'_succ,List.countP_cons]; simp only [Nat.zero_add]
    have hh := List.map_add_range' (a:=1) 0 n 1
    simp only [Nat.add_zero] at hh
    rw [←hh,List.countP_map,show (z >>> 1).testBit = (fun x => z.testBit (1+x)) by funext; exact Nat.testBit_shiftRight _]; simp only [Function.comp_def]; split <;> omega
def wordOK (k t L e n B Q i j d R : Nat) : Bool :=
  let V := pop n (active Q R i j) + d
  decide (i<j ∧ j<n ∧ R < 2^(n-1) ∧ R &&& B = R ∧ P i j &&& two R = 0 ∧
    span i j &&& R ≠ span i j ∧ deg1 R i j &&& Q = deg1 R i j ∧
    (d≠0 ∨ Q.testBit i = false ∨ Q.testBit j = false) ∧
    Fits k t L e V (V-pop n R-d-1) (pop n (single Q R i j)))
theorem bit_span {i j x} (hij : i<j) : (span i j).testBit x ↔ i≤x ∧ x<j := by
  simp [span,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one]; omega
theorem subset_bit {a b : Nat} (h : a &&& b = a) {x} (ha : a.testBit x):b.testBit x := by
  have := congrArg (fun z : Nat => z.testBit x) h; simpa [Nat.testBit_and,ha] using this
theorem bitP (i j x : Nat) : (P i j).testBit x = decide (x=i ∨ x=j) := by
  simp [P,Nat.testBit_or,Nat.testBit_two_pow,eq_comm]
theorem wordBit (p : Run) (x : Nat) : p.word.testBit x ↔ p.lo ≤ x ∧ x<p.hi := by
  simp [Run.word,Run.hi,Nat.testBit_shiftLeft,Nat.testBit_two_pow_sub_one]; omega
end OAI.CycleClique.Edit.Word
end
section
/- Based on OpenAI math, Apache-2.0, 3344da59991ed94f9ba711217b29c1d760badfa6. -/
namespace OAI.CycleClique.Edit.Word
set_option maxHeartbeats 800000 in
theorem sound {k t L e n B Q i j d R : Nat} {q : Finset Nat} {E : List (Nat × Nat)}
    (base : AllEdges n B q E) (qb : ∀ x ∈ q, x<n) (mask : ∀ x, Q.testBit x ↔ x∈q)
    (ok : wordOK k t L e n B Q i j d R) (M : y4) :
    ∃ C, (y2.system C).Valid k t (n+d) q (augmentedEdges n E i j d) L e M := by
  classical
  obtain ⟨ij,jn,rb,sub,nothree,gap,one,pos,fit⟩ := of_decide_eq_true ok
  let A := (active Q R i j).testBit
  let F := fun (_ b : Nat) => decide (b=i ∨ b=j)
  have Ab (x) : A x = (Q.testBit x || (R.testBit x || left R x) || decide (x=i ∨ x=j)) := by
    simp [A,active,U,left,Nat.testBit_or,bitP]
  have ep (x) (h : x=i ∨ x=j) : A x := by simp [Ab,h]
  have bound (x) (hx : R.testBit x) : x+1<n := by
    have := Nat.ge_two_pow_of_testBit hx; by_contra hh
    have : 2^(n-1) ≤ 2^x := Nat.pow_le_pow_right (by decide) (by omega); omega
  obtain ⟨ps,hh⟩ := partition F (R:=R) (A:=A) (by intro x; rw [Ab]; cases R.testBit x <;> cases left R x <;> simp) bound 0 (left_zero R)
  have notboth (x) (h : x=i ∨ x=j) (l : left R x) (r : R.testBit x) : False := by
    have := congrArg (fun z : Nat => z.testBit x) nothree
    change (R <<< 1).testBit x = true at l
    simp only [Nat.testBit_and,bitP,two,h,decide_true,r,l,Bool.and_self,Nat.zero_testBit] at this; contradiction
  have inside (p : Run) (hp : p∈ps) (x) (h : x=i ∨ x=j) (hl : p.lo ≤ x) (hr : x ≤ p.hi) : x=p.lo ∨ x=p.hi := by
    by_contra! bad
    have he := (hh.tiles p hp).edge
    cases x with
    | zero => omega
    | succ y => exact notboth _ h (by simpa using he y (by omega) (by omega)) (he _ hl (by omega))
  have separate (p : Run) (hp : p∈ps) (a : p.lo ≤ i) (b : j ≤ p.hi) : False := by
    apply gap; apply Nat.eq_of_testBit_eq; intro x; rw [Nat.testBit_and]
    cases h : (span i j).testBit x with
    | false => simp
    | true => have := (bit_span ij).mp h; simp [(hh.tiles p hp).edge x (by omega) (by omega)]
  obtain ⟨u,hu,ui,iu⟩ := hh.cover i (by omega) (by omega) (ep _ (Or.inl rfl))
  obtain ⟨v,hv,vj,jv⟩ := hh.cover j (by omega) jn (ep _ (Or.inr rfl))
  have uv : v≠u := fun eq => separate u hu ui (eq ▸ jv)
  let rs := (ps.erase u).erase v
  have perm : ps.Perm (u::v::rs) := (List.perm_cons_erase hu).trans ((List.perm_cons_erase ((List.mem_erase_of_ne uv).mpr hv)).cons u)
  have disj := (perm.pairwise_iff (R:=Sep) (fun h => Or.symm h)).mp hh.disj
  have far (r) (hr : r∈rs) : Sep u r ∧ Sep v r :=
    ⟨(List.pairwise_cons.mp disj).1 _ (by simp [hr]), (List.pairwise_cons.mp (List.pairwise_cons.mp disj).2).1 _ hr⟩
  have remote (r) (hr : r∈rs) (x) (hl : r.lo ≤ x) (hb : x ≤ r.hi) : ¬(x=i ∨ x=j) := by
    obtain ⟨h₁,h₂⟩ := far r hr; unfold Sep at h₁ h₂; omega
  have choose (p : Run) (hp : p∈ps) (x) (hx : x=i ∨ x=j) (hl : p.lo≤x) (hb : x≤p.hi) : p.a=x ∧ (p.len=0 ∨ ¬(p.b=i ∨ p.b=j)) := by
    have z := inside p hp x hx hl hb
    have ns : p.lo>i ∨ p.hi<j := by by_contra! bad; exact separate p hp bad.1 bad.2
    have dir := (hh.tiles p hp).direction
    simp only [Run.a,Run.b,dir,F]; unfold Run.hi at *; split <;> simp only [decide_eq_true_eq] at * <;> omega
  have choiceU := choose u hu i (Or.inl rfl) ui iu
  have choiceV := choose v hv j (Or.inr rfl) vj jv
  have endpoint (p : Run) (hp : p∈ps) (x) (hx : x=p.lo ∨ x=p.hi) (H : p.len=0 ∨ ¬(x=i ∨ x=j)) : x∈q := by
    apply (mask x).mp
    obtain ⟨_,_,_,fst,lst,edge,act⟩ := hh.tiles p hp
    have hi : p.hi=p.lo+p.len := rfl
    have vertex := act x (by omega) (by omega)
    rw [Ab] at vertex
    have rule := @subset_bit _ _ one x
    simp only [deg1,U,two,Nat.testBit_xor,Nat.testBit_or,Nat.testBit_and,bitP] at rule
    change (((R.testBit x || left R x) ^^ (R.testBit x && left R x)) ^^ decide (x=i ∨ x=j)) = true → _ at rule
    have bits : (left R x = false ∨ R.testBit x = false) := by rcases hx with rfl|rfl; exact Or.inl fst; exact Or.inr lst
    have nontriv : p.len ≠ 0 → (left R x || R.testBit x) = true := by
      intro nz; rcases hx with rfl|rfl
      · simp [edge _ le_rfl (by omega)]
      · obtain ⟨y,hy⟩ := Nat.exists_eq_succ_of_ne_zero (show p.hi≠0 by omega)
        simp [hy,edge y (by omega) (by omega)]
    by_cases h0 : p.len=0
    · have xl : x=p.lo := by omega
      have xh : x=p.hi := by omega
      rw [←xl] at fst; rw [←xh] at lst
      cases h : decide (x=i ∨ x=j) <;> simp only [fst,lst,h,Bool.or_false,Bool.or_true,Bool.and_false,Bool.false_xor] at vertex rule <;> tauto
    · have hne := H.resolve_left h0
      have ht := nontriv h0
      cases l : left R x <;> cases r : R.testBit x <;> simp [l,r,hne] at bits ht rule ⊢ <;> assumption
  have ends (p : Run) : (p.a=p.lo ∨ p.a=p.hi) ∧ (p.b=p.lo ∨ p.b=p.hi) := by cases h : p.rev <;> simp [Run.a,Run.b,h]
  have memR (r) (hr : r∈rs) : r∈ps := perm.mem_iff.mpr (by simp [hr])
  have bq (p) (hp : p ∈ u::v::rs) : p.b ∈ q := by
    apply endpoint p (perm.mem_iff.mpr hp) p.b (ends p).2
    rcases List.mem_cons.mp hp with rfl|hp; exact choiceU.2
    rcases List.mem_cons.mp hp with rfl|hr; exact choiceV.2
    exact Or.inr (remote p hr _ (by have := (ends p).2; unfold Run.hi at *; omega) (by have := (ends p).2; unfold Run.hi at *; omega))
  have sumLen (l : List Run) : (l.map (fun p => p.len+1)).sum = (l.map Run.len).sum + l.length := by
    induction l with | nil => simp | cons a l ih => simp [ih]; omega
  have vert := (perm.map (fun p => p.len+1)).sum_eq.symm.trans hh.vertices
  have verts : ((u::v::rs).map (fun p => p.len+1)).sum = pop n (active Q R i j) := by simpa [pop_eq,A] using vert
  have edgeSum : ((u::v::rs).map Run.len).sum = pop n R := by simpa [pop_eq] using (perm.map Run.len).sum_eq.symm.trans hh.edges
  let T := fun x : Nat => !decide (x=i ∨ x=j)
  let pred := fun p : Run => (p.len == 0 && T p.lo)
  have reject (p : Run) (x) (hx : x=i ∨ x=j) (h₁ : p.lo≤x) (h₂ : x≤p.hi) : pred p = false := by
    by_cases hz : p.len=0
    · have eq : p.lo=x := by unfold Run.hi at h₂; omega
      simp [pred,T,hz,eq]; tauto
    · simp [pred,hz]
  have singles := (perm.countP_eq pred).symm.trans (hh.singles T)
  change (u::v::rs).countP pred = _ at singles
  simp only [List.countP_cons,reject u i (Or.inl rfl) ui iu,reject v j (Or.inr rfl) vj jv,Bool.false_eq_true,if_false,Nat.sub_zero,Nat.zero_add,Nat.add_zero] at singles
  have sc : rs.countP (fun p => decide (p.len=0)) = pop n (single Q R i j) := by
    rw [pop_eq]; trans rs.countP pred
    · apply List.countP_congr; intro p hp; have h := remote p hp p.lo le_rfl (by unfold Run.hi; omega); simp [pred,T]; tauto
    · rw [singles]; apply List.countP_congr; intro x _
      simp only [isolated,T,single,Nat.testBit_xor,Nat.testBit_and,U,Nat.testBit_or,bitP,Ab]
      change ((_ && !(left R x || R.testBit x)) && !decide (x=i ∨ x=j)) = true ↔ (Q.testBit x ^^ (Q.testBit x && ((R.testBit x || left R x) || decide (x=i ∨ x=j)))) = true
      cases Q.testBit x <;> cases left R x <;> cases R.testBit x <;> cases decide (x=i ∨ x=j) <;> decide
  apply checks_sound base qb (u:=u) (v:=v) (r:=rs) _ M
  refine ⟨choiceU.1,choiceV.1,?_,?_,?_,disj,?_,?_⟩
  · rcases pos with h|h|h; exact Or.inl h
    · exact Or.inr (Or.inl (fun hq => by simpa [h] using (mask i).mpr hq))
    · exact Or.inr (Or.inr (fun hq => by simpa [h] using (mask j).mpr hq))
  · intro p hp; have tile := hh.tiles p (perm.mem_iff.mpr hp)
    refine ⟨tile.high,?_,bq p hp⟩; apply Nat.eq_of_testBit_eq; intro x; rw [Nat.testBit_and]
    cases h : p.word.testBit x with
    | false => simp
    | true => obtain ⟨a,b⟩ := (wordBit p x).mp h; simp [subset_bit sub (tile.edge x a b)]
  · intro p hp; apply endpoint p (memR p hp) p.a (ends p).1; right
    apply remote p hp <;> have := (ends p).1 <;> unfold Run.hi at * <;> omega
  · intro x hx; obtain ⟨p,hp,hx⟩ := hh.cover x (by omega) (qb x hx) (by simp [Ab,(mask x).mpr hx]); exact ⟨p,perm.mem_iff.mp hp,hx⟩
  · rw [verts,sc]; have he := sumLen (u::v::rs); rw [verts,edgeSum] at he; simp only [List.length_cons] at he
    rwa [show pop n (active Q R i j) + d - pop n R - d - 1 = rs.length+1 by omega] at fit
end OAI.CycleClique.Edit.Word
end
section
/- Mask-to-interval decoder for base forests. Adapted from OpenAI math,
3344da59991ed94f9ba711217b29c1d760badfa6, Apache-2.0. -/
namespace OAI.CycleClique.Edit
abbrev Row := Nat × Nat × Nat × Nat
def mat (ws : List Row) (M : y4) := ws.foldl (fun m (i,j,d,_) => (i,j,d)::m) M
end OAI.CycleClique.Edit
end
section
/- Based on OpenAI math, Apache-2.0, 3344da59991ed94f9ba711217b29c1d760badfa6. -/
namespace OAI.CycleClique.Edit.Word
theorem exactMask {n Q : Nat} {q : Finset Nat} (qb : ∀ x∈q, x<n) (h : Q < 2^n)
    (hq : ∀ x ∈ List.range n, Q.testBit x ↔ x∈q) : ∀ x, Q.testBit x ↔ x∈q := by
  intro x; by_cases hx : x<n; exact hq x (List.mem_range.mpr hx)
  simp [Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by decide) (by omega : n≤x))),show x∉q by intro hh; exact hx (qb x hh)]
theorem fill {k t L e n B Q : Nat} {q : Finset Nat} {E : List (Nat × Nat)} (base : AllEdges n B q E) (qb : ∀ x ∈ q, x<n)
    (mask : ∀ x, Q.testBit x ↔ x∈q) (ws : List Row) (M : y4)
    (h : ws.all (fun (i,j,d,R) => wordOK k t L e n B Q i j d R))
    (last : ∃ C : y2, C.Valid k t n q E L e (mat ws M)) :
    ∃ C : y2, C.Valid k t n q E L e M := by
  induction ws generalizing M with
  | nil => exact last
  | cons w ws ih =>
    obtain ⟨i,j,d,R⟩ := w
    simp only [List.all_cons,Bool.and_eq_true] at h
    obtain ⟨hw,hws⟩ := h
    change wordOK k t L e n B Q i j d R = true at hw
    obtain ⟨C,hC⟩ := sound base qb mask hw M
    obtain ⟨N,hN⟩ := ih _ hws last
    have bounds := of_decide_eq_true hw
    exact ⟨.forbid i j d (.system C) N, lt_trans bounds.1 bounds.2.1,bounds.2.1,hC,hN⟩
end OAI.CycleClique.Edit.Word
end
section
/- Derived from OpenAI math, Apache-2.0, lean/OAI/Combinatorics/Ramsey/CycleClique,
3344da59991ed94f9ba711217b29c1d760badfa6. Mixed edit and original certificates. -/
namespace OAI.CycleClique.Edit
def SafeBase (B : Nat) (q : Finset Nat) (E : List (Nat × Nat)) (n : Nat) :=
  AllEdges n B q E ∧ B < 2^n
instance {B q E n} : Decidable (SafeBase B q E n) := by unfold SafeBase; infer_instance
theorem extend {n B q E i j d} (h : SafeBase B q E n) : SafeBase B q (augmentedEdges n E i j d) (n+d) := by
  constructor
  · intro x hx hb
    have hlt : x < n := by
      by_contra! hh
      have hn : B < 2^x := lt_of_lt_of_le h.2 (Nat.pow_le_pow_right (by decide) hh)
      simp [Nat.testBit_lt_two_pow hn] at hb
    obtain ⟨he,hp⟩ := h.1 x (List.mem_range.mpr hlt) hb
    refine ⟨?_,hp⟩
    rcases he with he|he
    · exact Or.inl (List.mem_append_left _ he)
    · exact Or.inr (List.mem_append_left _ he)
  · exact lt_of_lt_of_le h.2 (Nat.pow_le_pow_right (by decide) (Nat.le_add_right ..))
end OAI.CycleClique.Edit
end
section
/- Adapted from OpenAI math (Apache-2.0), CycleClique, revision
3344da59991ed94f9ba711217b29c1d760badfa6. -/
namespace OAI.CycleClique.Edit.Rows
open OAI.CycleClique.Compact
abbrev Opt := Nat × List Nat
abbrev Av := Nat → Nat → Nat
def Covers (A : Av) (M : y4) := ∀ i d j, (A i d).testBit j → matrixEntry M i j d
def subset (A : Av) (i lo hi z : Nat) := (List.range' lo (hi+1-lo)).all (fun d => z &&& A i d == z)
theorem sub_sound {A : Av} {i lo hi z d j : Nat} (h : subset A i lo hi z) (hl : lo ≤ d) (hu : d ≤ hi) (hb : z.testBit j) : (A i d).testBit j := by
  apply Word.subset_bit _ hb
  apply beq_iff_eq.mp (List.all_eq_true.mp h d _)
  apply List.mem_range'.mpr; exact ⟨d-lo,by omega,by omega⟩
def exc (A : Av) (i r z : Nat) := !z.testBit i && subset A i (min 1 r) r z
theorem exc_sound {A M n i r z} (ha : Covers A M) (h : exc A i r z) : Excluded n M i (min 1 r) r (labels n z) := by
  simp only [exc,Bool.and_eq_true,Bool.not_eq_true'] at h
  have mem {j} (hj : j ∈ labels n z) : j<n ∧ z.testBit j := by simpa [labels,labelList] using hj
  refine ⟨fun j hj => ⟨(mem hj).1,?_⟩,fun j hj d hd => ha _ _ _ (sub_sound h.2 (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2 (mem hj).2)⟩
  rintro rfl
  exact (by simpa [h.1] using (mem hj).2 : False)
def exs (A : Av) (i : Nat) : Nat → List Nat → Bool
 | _,[] => true
 | r,z::zs => exc A i r z && exs A i (r+1) zs
theorem grow_valid {A M k t n i} (ha : Covers A M) (p : ya) (zs : List Nat) (hp : p.Valid k t n M i) (h : exs A i (p.radius+1) zs) (hw : 1 ≤ p.weight) : (growBall k t n p zs).Valid k t n M i := by
  induction zs generalizing p with
  | nil => exact hp
  | cons z zs ih =>
    simp only [exs,Bool.and_eq_true] at h
    unfold growBall; apply ih
    · refine ⟨hp,?_,?_⟩
      · simpa using (exc_sound (n:=n) ha h.1)
      · split_ifs <;> simp_all <;> omega
    · exact h.2
    · simp only [ya.weight]; split_ifs <;> omega
theorem grow_rad (k t n) (p : ya) (zs : List Nat) : (growBall k t n p zs).radius = p.radius + zs.length := by
  induction zs generalizing p with
  | nil => simp [growBall]
  | cons z zs ih => rw [growBall,ih]; simp [ya.radius]; omega
theorem fields (k t n) (o : Opt) : (option k t n o).base = o.1 ∧ (option k t n o).radiusCode = o.2.length := by
  obtain ⟨i,_|⟨z,zs⟩⟩ := o <;> simp [option,yb.base,yb.radiusCode,grow_rad,ya.radius]
def localOK (k n : Nat) (A : Av) (o : Opt) := decide (o.1<n ∧ o.2.length ≤ 3) && exs A o.1 0 o.2 && match o.2 with
 | [] => true
 | z::_ => decide (n < k+1+(labels n z).card)
theorem local_sound {A M k t n} (ha : Covers A M) (o : Opt) (h : localOK k n A o) : (option k t n o).Valid k t n M := by
  obtain ⟨i,_|⟨z,zs⟩⟩ := o
  · simpa [localOK,option,yb.Valid,exs] using h
  simp only [localOK,List.length_cons,exs,Bool.and_eq_true,decide_eq_true_eq] at h
  refine ⟨h.1.1.1,?_,grow_valid ha _ zs ?_ h.1.2.2 ?_⟩
  · rw [grow_rad]; simp only [ya.radius]; omega
  · refine ⟨exc_sound ha h.1.2.1,?_⟩; split_ifs <;> omega
  · simp [ya.weight]; split <;> omega
end OAI.CycleClique.Edit.Rows
end
section
/- Adapted from OpenAI math, Apache-2.0; see RowLocal. -/
namespace OAI.CycleClique.Edit.Rows
open OAI.CycleClique.Compact
def bucket (r : Nat) : List Opt → Nat
 | [] => 0
 | o::os => (if o.2.length = r then 2^o.1 else 0) ||| bucket r os
theorem in_bucket {o : Opt} {os} (h : o ∈ os) : (bucket o.2.length os).testBit o.1 := by
  induction os with
  | nil => simp at h
  | cons a as ih => rcases List.mem_cons.mp h with rfl|h
                    · simp [bucket]
                    · simp [bucket,ih h]
def cross (A : Av) (o : Opt) (os : List Opt) := (List.range 4).all fun r =>
 let z := bucket r os
 let m := o.2.length + r
 !z.testBit o.1 && subset A o.1 (min 1 m) m z
theorem cross_sound {A M k t n} (ha : Covers A M) {o b : Opt} {os} (h : cross A o os) (hb:b ∈ os) (hr:b.2.length ≤ 3) : (option k t n o).Compatible M (option k t n b) := by
  have hc := List.all_eq_true.mp h b.2.length (List.mem_range.mpr (by omega))
  simp only [Bool.and_eq_true,Bool.not_eq_true'] at hc
  have bit := in_bucket hb
  simp only [yb.Compatible,(fields k t n o).1,(fields k t n b).1,(fields k t n o).2,(fields k t n b).2]
  refine ⟨fun eq => ?_,?_⟩
  · rw [eq] at hc; simp [bit] at hc
  · split <;> rename_i e
    · exact ha _ _ _ (sub_sound hc.2 (by omega) (by omega) bit)
    · intro d hd; have := Finset.mem_Icc.mp hd
      exact ha _ _ _ (sub_sound hc.2 (by omega) (by omega) bit)
theorem compat_swap {M a b} (h : yb.Compatible M a b) : yb.Compatible M b a := by
  unfold yb.Compatible at *; rw [Nat.add_comm]; refine ⟨Ne.symm h.1,?_⟩
  have H := h.2; split at H <;> rename_i e <;> simp only [e,ite_true,ite_false]
  · exact H.symm
  · exact fun d hd => (H d hd).symm
def optsOK (k n : Nat) (A : Av) : List Opt → Bool
 | [] => true
 | o::os => localOK k n A o && cross A o os && optsOK k n A os
abbrev plist (k t n : Nat) (os : List Opt) := os.map (option k t n)
def total (k t n : Nat) (os : List Opt) := (os.map fun o => (option k t n o).weight).sum
theorem opts_sound {A M k t n} (ha : Covers A M) (os : List Opt) (h : optsOK k n A os) :
 (∀ b ∈ os, b.2.length ≤ 3) ∧
 (∀ b ∈ plist k t n os, b.Valid k t n M) ∧
 (∀ a ∈ plist k t n os, ∀ b ∈ plist k t n os, a ≠ b → a.Compatible M b) ∧
 (∑ b ∈ (plist k t n os).toFinset, b.weight) = total k t n os := by
 induction os with
 | nil => simp [plist,total]
 | cons o os ih =>
   simp only [optsOK,Bool.and_eq_true] at h
   obtain ⟨len,valid,pairs,wt⟩ := ih h.2
   have c (b) (hb:b ∈ plist k t n os) : (option k t n o).Compatible M b := by
     obtain ⟨b,hmem,rfl⟩ := List.mem_map.mp hb; exact cross_sound ha h.1.2 hmem (len b hmem)
   have fresh : option k t n o ∉ (plist k t n os).toFinset := by
     intro ho; exact (c _ (List.mem_toFinset.mp ho)).1 rfl
   have lo := h.1.1; unfold localOK at lo
   simp only [Bool.and_eq_true,decide_eq_true_eq] at lo
   refine ⟨List.forall_mem_cons.mpr ⟨lo.1.1.2,len⟩,List.forall_mem_cons.mpr ⟨local_sound ha o h.1.1,valid⟩,?_,?_⟩
   · intro a ha b hb e; rcases List.mem_cons.mp ha with rfl|ha <;> rcases List.mem_cons.mp hb with rfl|hb
     · exact False.elim (e rfl)
     · exact c _ hb
     · exact compat_swap (c _ ha)
     · exact pairs _ ha _ hb e
   · simpa only [plist,List.map_cons,List.toFinset_cons,Finset.sum_insert fresh,total,List.sum_cons,add_right_inj] using congrArg ((option k t n o).weight + ·) wt
def check (k t n : Nat) (A : Av) (os : List Opt) := optsOK k n A os && decide (k < total k t n os)
theorem packing {A M k t n os} (ha : Covers A M) (h : check k t n A os) : PackingValid k t n M (plist k t n os).toFinset := by
 simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
 obtain ⟨_,v,p,w⟩ := opts_sound (t:=t) ha os h.1
 exact ⟨fun b hb => v b (List.mem_toFinset.mp hb),fun a ha b hb => p a (List.mem_toFinset.mp ha) b (List.mem_toFinset.mp hb),w.symm ▸ h.2⟩
end OAI.CycleClique.Edit.Rows
end
section
/- Adapted from OpenAI math, Apache-2.0; see RowLocal. -/
namespace OAI.CycleClique.Edit.Rows
-- Each 32-bit row has its own distance and source. Out-of-format entries
-- are ignored, never aliased; this can reject, but cannot certify, a leaf.
def off (i d : Nat) := i*256+d*32
def avail (z : Nat) : Av := fun i d => if d<8 then (z >>> off i d) &&& (2^32-1) else 0
def add (z i j d : Nat) := if i<32 ∧ j<32 ∧ d<8 then z ||| 2^(off i d + j) ||| 2^(off j d+i) else z
theorem avail_iff {z i j d} : (avail z i d).testBit j ↔ d<8 ∧ j<32 ∧ z.testBit (off i d+j) := by
 have mask : (4294967295 : Nat).testBit j = decide (j<32) := Nat.testBit_two_pow_sub_one 32 j
 unfold avail; split <;> simp_all [Nat.testBit_shiftRight,Nat.testBit_and,and_comm]
theorem rep_add {z M} (h : Covers (avail z) M) (i j d) : Covers (avail (add z i j d)) ((i,j,d)::M) := by
 intro a c b hab; obtain ⟨hc,hb,hab⟩ := avail_iff.mp hab
 have old (hz : z.testBit (off a c + b)) : matrixEntry ((i,j,d)::M) a b c := by
   rcases h _ _ _ (avail_iff.mpr ⟨hc,hb,hz⟩) with hh|hh
   · exact Or.inl (List.mem_cons_of_mem _ hh)
   · exact Or.inr (List.mem_cons_of_mem _ hh)
 unfold add at hab; split at hab
 · rename_i bounds; simp only [Nat.testBit_or,Bool.or_eq_true,Nat.testBit_two_pow,decide_eq_true_eq] at hab
   rcases hab with ((hh|hh)|hh)
   · exact old hh
   · unfold off at hh; have : a=i := by omega
     have : c=d := by omega
     have:b=j := by omega
     subst_vars; exact Or.inl (List.mem_cons_self ..)
   · unfold off at hh; have : a=j := by omega
     have : c=d := by omega
     have:b=i := by omega
     subst_vars; exact Or.inr (List.mem_cons_self ..)
 · exact old hab
def push (ws : List Row) (z : Nat) := ws.foldl (fun v (i,j,d,_) => add v i j d) z
theorem rep_push (ws : List Row) (z M) (h : Covers (avail z) M) : Covers (avail (push ws z)) (mat ws M) := by
 induction ws generalizing z M with
 | nil => exact h
 | cons w ws ih => obtain ⟨i,j,d,R⟩ := w; exact ih _ _ (rep_add h i j d)
end OAI.CycleClique.Edit.Rows
end
section
/- Adapted from OpenAI math (Apache-2.0); see RowLocal. Finset-free computation. -/
namespace OAI.CycleClique.Edit.Word
def byteCount (b : Nat) := (95125173855764218123276304889944061997689682402263585766959741291920687686033329201817409157123347502415384089435969498586180241031507595463600295898153685276653211633572815512294064538494957912327413386667662218713394765509704508661031522276467630197481635010039778342554499416459730172574551513689147646224 >>> (4*b)) % 16
private theorem byte_correct : ∀ b : Fin 256, byteCount b.val = pop 8 b.val:=by decide +kernel
private theorem low (z : Nat):byteCount (z%256) = pop 8 z := by
  rw [byte_correct ⟨z%256,Nat.mod_lt _ (by decide)⟩]
  change pop 8 (z % 2^8) = pop 8 z
  simp only [pop,Nat.testBit_shiftRight,Nat.testBit_mod_two_pow]; norm_num
private theorem splitPop (k n z : Nat) : pop (k+n) z = pop k z + pop n (z >>> k) := by
  induction k generalizing z with
  | zero => simp [pop]
  | succ k ih => rw [Nat.succ_add,pop,pop,ih,Nat.add_assoc]; congr 2; rw [←Nat.shiftRight_add,Nat.add_comm 1]
private theorem tail_eq (r z : Nat) (hr : r < 8):byteCount (z % 2^r) = pop r z := by
  rw [byte_correct ⟨z % 2^r, lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _)) (show 2^r ≤ 2^8 from Nat.pow_le_pow_right (by decide) (by omega))⟩]
  change pop 8 (z % 2^r) = pop r z
  interval_cases r <;> simp only [pop,Nat.testBit_shiftRight,Nat.testBit_mod_two_pow] <;> norm_num

def chunks (r : Nat) : Nat → Nat → Nat
 | 0,z => byteCount (z % 2^r)
 | k+1,z => byteCount (z%256) + chunks r k (z>>>8)
private theorem chunks_eq (r k z : Nat) (hr : r<8) : chunks r k z = pop (8*k+r) z := by
  induction k generalizing z with
  | zero => simp [chunks,tail_eq _ _ hr]
  | succ k ih => rw [show 8*(k+1)+r = 8+(8*k+r) by omega, splitPop, chunks, low, ih]
def fastPop (n z : Nat) := chunks (n%8) (n/8) z
theorem fastPop_eq (n z : Nat) : fastPop n z = pop n z := by
  unfold fastPop; rw [chunks_eq _ _ _ (Nat.mod_lt _ (by decide))]; congr 1; omega
end OAI.CycleClique.Edit.Word
/-! Adapted from OpenAI math (Apache-2.0); see RowLocal. Finset-free computation. -/
namespace OAI.CycleClique.Edit.Rows
open OAI.CycleClique.Compact

theorem numCard (n z : Nat) : (labels n z).card = Word.fastPop n z := by
 unfold labels labelList
 rw [List.toFinset_card_of_nodup ((List.nodup_range).filter _),Word.fastPop_eq,Word.pop_eq]
 simp [Word.cnt,List.countP_eq_length_filter,List.range_eq_range']

def nextW (k t n size w : Nat) : List Nat → Nat
 | [] => w
 | z::zs =>
   let c := Word.fastPop n z
   let b := max size (k*w+1+c-n)
   let u := max w (1+(if t<b then 1 else 0)+(if max k (2*t)<b then 1 else 0))
   let u := if t ≤ size && n+t ≤ k+1+c then max u 2 else u
   nextW k t n b u zs

theorem grow_w (k t n : Nat) (p : ya) (zs : List Nat) :
 (growBall k t n p zs).weight = nextW k t n p.size p.weight zs := by
 induction zs generalizing p with
 | nil => rfl
 | cons z zs ih => rw [growBall,ih,nextW]; simp [ya.size,ya.weight,numCard]

def weight (k t n : Nat) (o : Opt) := match o.2 with
 | [] => 1
 | z::zs => let b := k+1+Word.fastPop n z-n; nextW k t n b (if t ≤ b then 2 else 1) zs

theorem weight_eq (k t n) (o : Opt) : (option k t n o).weight = weight k t n o := by
 obtain ⟨i,_|⟨z,zs⟩⟩ := o
 · rfl
 · simp only [weight,option,yb.weight]; rw [grow_w]; simp [ya.size,ya.weight,numCard]

def onlyMasks (k n : Nat) (A : Av) (o : Opt) := decide (o.1<n ∧ o.2.length ≤ 3) && exs A o.1 0 o.2 && match o.2 with
 | [] => true
 | z::_ => decide (n < k+1+Word.fastPop n z)
def masksOK (k n : Nat) (A : Av) : List Opt → Bool
 | [] => true
 | o::os => onlyMasks k n A o && cross A o os && masksOK k n A os

theorem masks_eq (k n A os) : optsOK k n A os = masksOK k n A os := by
 induction os with
 | nil => rfl
 | cons o os ih => obtain ⟨i,_|⟨z,zs⟩⟩ := o <;> simp [optsOK,masksOK,localOK,onlyMasks,numCard,ih]

def maskCheck (k t n : Nat) (A : Av) (os : List Opt) := masksOK k n A os && decide (k < (os.map (weight k t n)).sum)
theorem mask_sound {A M k t n os} (ha : Covers A M) (h : maskCheck k t n A os) : PackingValid k t n M (plist k t n os).toFinset := by
 apply packing ha
 simpa only [maskCheck,check,total,masks_eq,weight_eq] using h

theorem packing_exact {A M k t n os} (ha : ∀ i d j, (A i d).testBit j ↔ matrixEntry M i j d) (h : maskCheck k t n A os) : PackingValid k t n M (plist k t n os).toFinset := mask_sound (fun i d j => (ha i d j).mp) h
end OAI.CycleClique.Edit.Rows
end
section
/- Derived from OpenAI math, Apache-2.0, lean/OAI/Combinatorics/Ramsey/CycleClique,
3344da59991ed94f9ba711217b29c1d760badfa6. Mixed edit and original certificates. -/
namespace OAI.CycleClique.Edit
inductive RCT where
 | group (ws : List Nat) (next : RCT)
 | split (i j d : Nat) (reason next : RCT)
 | pack (os : List Rows.Opt)
 | direct (c : y2)
namespace RC
-- One literal per maximal consecutive run of equal (i,j,R).
-- low 5 bits: i; next 5: j; next 3: first d; next 3: length-1.
def expand (code : Nat) : List Row :=
 let i := code % 32
 let j := (code >>> 5) % 32
 let lo := (code >>> 10) % 8
 let len := (code >>> 13) % 8 + 1
 let R := code >>> 16
 (List.range' lo len).map (fun d => (i,j,d,R))
open Word in
def intervalOK (k t L e n B Q i j R lo len : Nat) :=
 let v := fastPop n (active Q R i j)
 let s := fastPop n (single Q R i j)
 let paths := v - fastPop n R - 1
 decide (i<j ∧ j<n ∧ R < 2^(n-1) ∧ R &&& B = R ∧ P i j &&& two R = 0 ∧
    span i j &&& R ≠ span i j ∧ deg1 R i j &&& Q = deg1 R i j) &&
 (List.range' lo len).all (fun d => decide ((d≠0 ∨ Q.testBit i = false ∨ Q.testBit j = false) ∧ Fits k t L e (v+d) paths s))
theorem interval_sound {k t L e n B Q i j R lo len d} (h : intervalOK k t L e n B Q i j R lo len) (hd : d ∈ List.range' lo len) : Word.wordOK k t L e n B Q i j d R := by
 simp only [intervalOK,Word.fastPop_eq,Bool.and_eq_true,decide_eq_true_eq] at h
 obtain ⟨⟨a,b,c,f,g,m,q⟩,h⟩ := h
 obtain ⟨p,v⟩ := of_decide_eq_true (List.all_eq_true.mp h d hd)
 apply decide_eq_true; refine ⟨a,b,c,f,g,m,q,p,?_⟩
 convert v using 1; congr 1; omega
def codeOK (k t L e n B Q c : Nat) := intervalOK k t L e n B Q (c%32) ((c>>>5)%32) (c>>>16) ((c>>>10)%8) ((c>>>13)%8+1)
theorem code_sound {k t L e n B Q} (ws : List Nat) (h : ws.all (codeOK k t L e n B Q)) :
 (ws.flatMap expand).all (fun (i,j,d,R) => Word.wordOK k t L e n B Q i j d R) := by
 apply List.all_eq_true.mpr; intro w hw
 obtain ⟨c,hc,hw⟩ := List.mem_flatMap.mp hw
 obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hw
 exact interval_sound (List.all_eq_true.mp h c hc) hd
def check (k t L e B Q : Nat) (q : Finset Nat) : RCT → Nat → Nat → Nat → Bool
  | .group ws N, n, bits, z => ws.all (codeOK k t L e n B Q) && check k t L e B Q q N n bits (Rows.push (ws.flatMap expand) z)
  | .pack os,n,_,z => Rows.maskCheck k t n (Rows.avail z) os
  | .direct C,n,bits,_ => match C with
    | .system S => qCachedLabelValidBool n q bits S && decide (Improvement k t L e S)
    | .cycle S => qCachedCycleValidBool n k bits S
    | _ => false
  | .split i j d R N, n, bits,z => i<n && j<n &&
      check k t L e B Q q R (n+d) (bits ||| y9 (pathEdges (pathLabels n i j d))) z &&
      check k t L e B Q q N n bits (Rows.add z i j d)
theorem sound {k t L e B Q q} (T : RCT) {n E z M} (b : SafeBase B q E n) (qb : ∀ x ∈ q, x<n)
    (mask : ∀ x, Q.testBit x ↔ x∈q) (hz : Rows.Covers (Rows.avail z) M) (h : check k t L e B Q q T n (y9 E) z) :
    ∃ C : y2, C.Valid k t n q E L e M := by
  induction T generalizing n E z M with
  | pack os => exact ⟨.packing _, Rows.mask_sound hz h⟩
  | direct C => cases C with
    | system S => exact ⟨_, (qCachedCertificateBool_spec k t n q E L e M (.system S)).mp h⟩
    | cycle S => exact ⟨_, (qCachedCertificateBool_spec k t n q E L e M (.cycle S)).mp h⟩
    | _ => simp [check] at h
  | group ws N ih =>
    simp only [check,Bool.and_eq_true] at h
    obtain ⟨hw,hn⟩ := h
    exact Word.fill b.1 qb mask (ws.flatMap expand) M (code_sound ws hw) (ih b qb (Rows.rep_push (ws.flatMap expand) z M hz) hn)
  | split i j d R N ir it =>
    simp only [check,Bool.and_eq_true,decide_eq_true_eq] at h
    obtain ⟨⟨⟨hi,hj⟩,hr⟩,hn⟩ := h
    rw [← qCacheEdgeBits_append, ← augmentedEdges] at hr
    obtain ⟨r,vr⟩ := ir (extend b) (fun x hx => by have := qb x hx; omega) hz hr
    obtain ⟨v,hv⟩ := it b qb (Rows.rep_add hz i j d) hn
    exact ⟨.forbid i j d r v,hi,hj,vr,hv⟩
theorem verify {k t D B Q T} (b : SafeBase B (patternClique D) (patternEdges D) (patternOrder D))
    (qb : ∀ x ∈ patternClique D, x < patternOrder D)
    (m0 : Q < 2^(patternOrder D)) (m1 : ∀ x ∈ List.range (patternOrder D), Q.testBit x ↔ x ∈ patternClique D)
    (h : check k t (patternAmount D) (patternEdgeCount D) B Q (patternClique D) T (patternOrder D) (y9 (patternEdges D)) 0) : y5 k t D :=
  sound T b qb (Word.exactMask qb m0 m1) (by intro i d j h; simp [Rows.avail] at h) h
end RC
end OAI.CycleClique.Edit
end
section
/- Adapted from OpenAI math (Apache-2.0), CycleClique finite verification,
revision 3344da59991ed94f9ba711217b29c1d760badfa6. -/
namespace OAI.CycleClique.Compact
namespace HP
private def fld (z w i : Nat) := (z >>> (w*i)) % 2^w
private def pos (i : Nat) := fld ((#[0xaf962b260a9a029c30a4a0286e89f6a2728c9a3a25d6c94bc248488fbd234b08a9a22220863820fe8818c1fcd07d301eca878d11dc5075031cb2470b81bb246cc51ab9868cf19b10650118d78618417f685eb5174485b78169b8591215f8c56d815a98533e141144d7112ca4484e1190844381092c40ee0fd143d890ee6c3a360e39c37c20da5c35760d20833710c9b031940c2f42fd50bb482dc90b3602bec0ac702a4a0a5ac289609f2426fb09898256f092d022a607fec1d6d06cc0197005eac16260538c13c704ac811d90434c0fbe03b3c0de4034600c4402e180acd028780967022bc080501d8006c2018c8051300ed402d0007fc0141002540000,0x2017a80295ffdd7fc19fe2a7f521fc867eec5fadf7e81df93b7e13df76c7da3df5ab7d319f3de7c905f0417b8a5ec137a855e7fd797ade3ea7878ddfc9776b5dba476639d778755b5d3697453dcf41734a9caff723adc6d0712edc2b27028dbe7e6f1d5ba646e10db6166d009b1ec6bf29ad8a6ad35a90969aeda35f66d959422635958717604bd7be25d7e570985ad0d65ee582495b53559e5518b532254850510253f5f4eb6936c34c9452e1e4a6f925d0486c11d9f466d915b84483d0e504294506cb40d20ffb63f0e4f8443d358f18a3b804eaca39ce0e3d7381f8dd6836918d6f834ed0d066335a4ca2731c60c40330310be092ec30b81b2d56cb282,0x25bb596bd25a379661658c395f7657059590655779524e53c294bca5234945c2508a93f124f099394a4db29339a4c1992d164a7a9267648ca91ff64725919724592912e643f890d1242809069e40e29001a3f3c8fa1a3dac8f3763c1d8edaa3ab98e7c6390c8e0ea375b8da2a35a38d35234038cc8a32548c65630e48c06a2f4e8b9de2d9d8b32a2c018ac9e2a4a8a5c6289489eee26fe89896254d891fe23c488c2e2253885fa20ae87f821f138794a1d97873261bfc86d1a1a718666a18d085fee173a859e215bc853c6142f84d5212788468210c483ffa0f50839ca0da6833520c0282c520a458260a08c281fbe071d819720586812c203d880c220238,0x9c30e70179bd9a6ea29b7366cf19b05e6b489aa2669b39a346680899ca2665a9962a64b598f766303988866159982465fcc97c125e28975925c8f] : Array Nat)[i/113]!) 18 (i%113)
private def word (i : Nat) := ((#[0x3ddd711efffa66e90eb3893dbbdb10679b65ccaae2521b4d9ebbf91ae98f7dfc18d7191435621dc76843cc5bf9f3bbeb4ac346ab813af348b83e000000003fd000000007e200000001f5ffdefa07d4008417df2000000007c600000017b41bd014b5bdefafa93745002cba10b876a54ca79f2f6c3bc5c1c8fb081cc516a4a76015b3ea8a1a27afaafcd0f82fb01ae5d7af266f7cfb81b3b69f83b288c8cbe0051f5d840a7fe2ae1e2c8260af52eaa8f4b53415b659b851dd94f67098612cbfef499e7c5ff30d171d50d93fa8263fbf9662bf57138ab807ab69110728434602f41963b13fe4f1a27c7107f89836f5331fba825b21f3b42ffe65b923d96c68480a,0xccac9070f28d6bb2284b200e0e2cedc0acc1d84bec2b525b9401176d91abfcccce03e3063f644dfa66736c25269b7f46fb7e2aacd76bd1bdcdd824bbdd606155226abc6ea57e10fe8a82b63c5927fef5b99b679a6f07f040685622afc68f4baf20cd01d99ec9c4ba96015a8e9b3d68769e97cd47a755bc29c2b6fd0d24054e0bf9d87a5c628bd917a581a35e78baf0bab2789fde64524ff1342d7837353f7d24eceaf28407f85ab248be2596fae14caeb656fe1fb676a4a4f337adefae50f02e7740299ccb707ed5e7757e5a8131a7009897df71afdf97b08eb11da0fca2bf599e81f7bba8cf0686c4dc680ed181b70128a8e9834b5074bac0e275c3dfaab678,0x5fc376f3fada494925974c14fba806c8108f504930e94753face91ca88233150aa5be57bb8c57f464b3f87007f3a1c16b09d7befb88baaee00fff5bd9187fcafaf154ef5da7904ca28c1de327aba702d4a440cf3458de2ce3997c66332e019ba800006acb48e047ffda6d9147483b8bb08637cebecaab6951e2936e775f3a4c338061cb8013fe954f3396d70a9f779233e8cd4771d7c718b86f97a87cbc74c7de86ffafcbe428029d342ae1cf98f6209d5d2eb454c4bc5fd76230d3ff673bfa0eeaaafa9a15f592540ee35ecf10de8cc35bf8f0505edc7bbc5eb12975243bc5aed2990080e4ec24f49114623a760c86016ed31969aa8e08ef692da5ed5393e10,0xdf7d3058a3c379c0ca92f66709300efbea550ea44d6ab6d519fedf40978e7fec4fdec23c11325cffcf2a63e71f1920985b44c576cdda1d127cc904ba17d4d7f2116b049249248f605aaaaaa9e6caaaaaab9f18a112b79ec2be19088983b17632f8312ea5e315146a915114a00b4c97dcb7bd3c2ea47344b19eb3cdca6757ddcda7a1b7d81a98ef24eda49187726fe9a1ac09c002f00008077ff68580972809ba7bb043adfa727779ad675e8c18d00ef51ad79245a31c4f63a3c745d1745d001c6e38ce9b8e395e152a843600faaab0052af38fb6d07852cdc65143a4abffae2101f30adad8e9fc4acab52bfed721567d4fe7461047a9f76e7d5aa4770880c55c,0xe10abdc48e355f816c2968cbf928d264a8e284c6fafbf7ef6112bb1f5a7509557fe46f059219b7e213d9fa133b0010537c7dcadb42a10a5dd48f292117d5c34a826d19fbdc8f4ebca6e4f56c22f06accdcd05637445a4efbb04a090d1f7595c4b3b60393934d848e267c3f35ba781f961f9add41260e38e38e2f3f7b425ecfb338e38e39c4dfffefb791c1c72083e3180e38e38d516000000002a1aaaaaaaafc800000001ec2600000033faa0f9a579cfd5756091c395d41dade8af4d0fd9e5ed5eda13ec2b1df166ca7e4ed1d2e917b8ba38444c19d54d3ed9bbaf6f31ae57d94cc514514514de5e0a72efa9e79e79e2ef9e79e7b227ffffffced3000000127,0x916d984fd75267ac40824444d5fd1f86fd7d546b554b4724bfe1f666b6f9d4eaa5b528d57aebb3ff8a6620d5a7f633ff8041b5f3dede02fbdae9d84bb32e3fe2050a0e514241732e190eede10ceb74210b645af96a95adebc3c2d100c9ea656d363fa1e4b79514ddd96bcd6809c6ac4876b380e97befe81d96f6c25e18e6ed90e8ab5a2e1b03ebf1bffd9bb855c27388d377c8cd11ed46ab556b1e4b7bdc1ed0d2b026e993b6f15bce36c740a59748746a71d4e2ad52ded5b2faead51ff51937dbbe7b28bdf8573d0a27e10240b8a4c05aa5a5727a767d7765bbc2c9b035bd8fbb62015669a2e2f3f218708aacb9d208dfd08282c424a51d53200e4731a0de63,0x50022ebee006ff333aaf8dd1a3a55440d1dc20a00782ec0c52a3a28bf658d48b7de99482b1199f746334035be6497e162a291512f8fd6ad7ab08716cb72474e5e161c6137520fd236b7825583446afc7f2a9bb873c417c224774e6dfe050d06cdb7a65af2a86bda9c5c5fab4155bff2aea81ef5ea30b70cbfaf9a1c6fa4accb7e340bbdc157fb91dea8d1d820e8066abbf8fa0c910385c23ca084721905af922e0819cca1eb0e4542cca6efca5ec68cd789c5cff6bbc276e00e10f34f53c6db3511568270a6c4cea3db166bfcc686a595f7c717834e26a83eb3d9948cade7ecae928462675337cd89b21307aa24ce321230db33d8d50ca9c125987761b8f7281,0x301bf5e7a8e2d2f9fd92c60e77e8cc1ff8178003801bfd53eef1333b2d70dae49dad293c76d09231e1c2b952688d32099fe5d6ebe7ae241a4fda36827cac9886f2d4d37a64922f932a1c99a00519b32eb93699c115078c56350f5357ee2ccc6afd4ec509ebfc2a1114cf2a5475b0a6b9fef54e700ac801d1bc30156b277925f945659f1c6cb37cf49d803ff6864edad18161f38a213ea0d550f62eac99db49472d99f61c94930257c49f5626363e987b99ee87b438ae01eff3abbb348c32e2bbcab4e83b48b40fea12135ae60ce0f4a7bc642b7225d7f597cd14c7c3ec0016a80d57e74db21e9bcf5945d2be635529af28d89fc4e2fc332103894c7519ae78b1,0xcf2e6517e162800714b95f7e607480adf655c1cb4dced2661405c795dde404097b425d131c71c71d88e38e38e67eaaaaaaad4980000007c6a7f6ed7cc9bccbe3b2706386608275734ab32cbecf0fe50dccb0676811d68177b7af4d24b6941158fd3f9b077ece409a4672b20e546c69d6c524f5f40004083ff3c7ac4c7330474bba446bbeb2a2d545839a1cc9dbb07b8623b2ec2ca03677ae988feecbfdf03e7b8c90fcdc2648b43663f812c62fe1dbc44a199a00d4cf6ffe611a542e8191238c9268118f83e41e8f09cec4b363aeef7b4051a1d1e90fa852a5b38a4f7133340071bb27e320a067f00fd525bef38007a05b69dd28a1acf3164dd6a98fbd20e112,0x2b521f1fc48cd478b76d34e345a1a4c000630d64882224dc495414e4577ac97ab8494a9bac5c5644cac82a23d19e943f8c07f2730abee4de59c20de7eed097b42606887bbae54549900000cc00006011fdf5360c7437574760fdf65125be4a469d1b62e2377179390783d3e4b8613713ade95358b45bdd75232fd42cade7faf1764a781948b19ed097b426c0e38e38dec5555553b8178000003df1b95ee58e1c0a09d782fa8e04fd2d58aab8ecfd05385d45a193b20bd5e472c25cccabe3962d91d9877a3c27696854ac130f4a61133073fe775f3c78852987aa08d971bcd6e9e05e48b0fcd6fefffffffe9838e38e3a50caaaaaabbdf40462380246f5e5ee43,0x333411c401001f77617f4210b7e124031f8e16a82501380300180180200400600015800e28c9e00000033ff5f06881cae594f6f09e72405e64b6e328770b96a673f2faf0329161dc21b641511eccd6e9e06525d538e38e391c4d71c71c719ac38e38e390923c71c71c6c6f55555555c532aaaaaaaaa12f684bda5a638e38e39085097b425ee1573fffffffff651ffffffe7c39e00000033f22dea5d2a9ee26fa300ff3ae08b6233900a664d895dd682e6f6053f92e48300a1d139dbea29f2c890b34944181c0000000000402119576726e8ba2e8acad06b925c1aa8000000000087511074b59676b3644555f00003447dedf000000019f53708af4d15e8a7b79,0xd333f49936595075d976ebe75c927983fac5b43f3908710d64ddccccd1a927aed70e66833500021f29dd52262882bec6f40dc9adcbb0bcdeece66a4f939f4c63a52bad7d8c53a6b29eeed6850a883fffd1652e715ce404a4eb0d80123d1a158320acd2236533ace4043f2018f872c076f53f8bb33cd8eaa1b6548d1522ce6835de4f5a3206fce5b3becd24f33a99bd59418f9b4712f8088aa67f1f09db8b43fa732edb8fbed85b3d9333a66e0dcea6678291246999ae14bb74da7960eef05b2f9ee796f26ad4accc2092004d14cd19ab2f9aad9af926765a749e5a6674d7c219cc635739db182d9751bee39965d222b64fdfdb9dd852395a7c2fdf44de5c3e01,0xdb1f7a57ae8165579d3a3806468ed225559c513cf5fcde16fd3b6d3c7b06351f524cd40002e3f5ff1c2cc16c191d8dc475e32d224d9f431eb92bb2d2fec41518b2e25825ed209680c81f5d20901e53edd4dbf9cd6fd257aad8037be6102aeca929f86a6a9793c87a01b4ee636383cfdb45c10331ee334a04a111e55d05f3e9892391bd85444b005556ee3839b9c72acb56aab095364bfb6c1bc7934936e315bd9cb67bbfb059972e0e35f850d133affd0cc76719cbc4ebc1e1c813cac377ca6f816bf8f161f74352b3146b54000bc4fcb52682ca6f893cb653f3b201a61179b1a0d462ec5d76af1226151c5dbee569109c40b8f167c8d70fd715c2f334e66d99,0x38b391f245520b0053e76428d57e665f4489d1ebbdf421488d78f8d4a9952ce1ec8c88c01c2ed11fff4a9314429fa8dfbe284fe22a9dc60bab06306be737c0240a202f582645bf9f26a4f199b1558346469de3b0ccccd5dab51bfccf7c00e1934f99c3880025ec97cefedf022aa997b4efc7b15cfaaf94fd261b089b528d952dbcde730abfaa75dfc9dd20165bb370cc7b654a7c0e9c34579cd66e7ccb74799c334718e0d961ab46946d203565c26e7786a33ca71ba7f7a5224084243f9e336998d826d58fe25a5826dd1608a736a7491f948d56091b819b22932f69028dff20a02f1334a4aef0f216d2971ff2bd268805568ecfdfd26cb3565f33a249ae7ae4,0x238cf93d046d9424ad4b517777a88000567778257544fbb62b67557356fadd9b4a92f6107c0a4285fa9dad9484478c5c90a97a6a63cef580088b268b4bfd0a6572b872bd82fa023f090b05261eb900bc435ba2aaaaaab89c7b3a5970007d636463422728669bccb2a6451c96115167d051833a058077b1ba750ce405d341d558edf35ce9522b734b7dc3dda634cc9e5d009102600d2d1c92d0da1e73dd3cbc388f4600002a18d9fce893fe79a406c71920d458e9f5a993bb1b7c71ffaf8f8dbab3c3e742a09891f87d113e81530ebd81d35e162fd0b9e9a1552e1505219c31ac5c3028d46d3cd9ec6cf302d3587aefde8bf839660cfad44c23f6345bf92cd5fd,0x8f5c29be7a88293fdfe4f4d6380904f435e52115aaab2fbcf7af6e8741afc82de6d8162a42e90722798b42805e69b97e8df31fae7ef9f5f84cdfc856093173a71424c8339e9ad6ebeee14515aa6e6d0009000b001a23001c0f7784a29e0243cae75b83abbe15e8cd980c9c1bf42d3bab1c2182be598b83db2d8e7582e64213e93e93f9ab7bb6da231de8e2c11c7d555c01b1a0689b87738f6821c62e4dbd2b1ba89bff2913830072283d8c8d9ea21d2bd2d77607e3ebe31a1d29e3af06c49c511966402d845df7c1d7ac2eff008a8cadebe92b8e3708ddc892888555d708666f12ce8af094e389aa661547c203846cc4f8a310685d7a25f9ceea2d13076cc2ee,0xfa414b47bab42c65aa5bce6cc8b39a2c53615facebc3a40bc275c5d9686d8f172a4f6f179e5e184a2222d39dae47a6cbcaa9d75fbc3255f77a85a75ec255da194ede9052ac651dabf83c7a1f4600d0e68b6263a98ecd35b5dade9ae3087871024a5db90358affe346a4541ac1f34d10db2a9b0b3a2c98720ddddd9e07ae7d559ef3c2cbb806e4f16ca14ee6c6d7eb57b67e3dba3d865f7ec71f19687df43024c77ee781cf88f361a963ce4ad2ad41717f9f98ed1f077ea542cc1162af67574d7ccb3982c2328e6601eb65caab4f7a8469bbde2a06731390d546d6db710c02108b06c62ac80f01edbf0c49693c90d0576cf2e20cf69c9babbde17953cfe928352,0xd03341b6400424d011c3840adfdefceee0c79850e33d59e2ba64f28585be9c371292e978e410e6ee0086dc0563391a9bc168d276df3d2c786167822f1579017be65594dea84400ce9414734000508000a67e90d12c54c6d496a7e80e95c819ded92be96f51f7ee25466891fa6ab0d6f4c00872343813e04538582e249d835810633e2c28e7775884259cea9c05b05cda5114aa21749c7afaf5077a0acd5720341111efe2ffdf8dc46188131dfa29efbf27c0b9a98ad050ff95a17fc4d89579380713579be8cc14f647e861bc49a0e303ddeab630547bebf9e219c0005020000018025e8824280da20128d400080f7eaa219f10a18aab4c6a7291c028697132e0,0x56aedcdf3c96bec6ce9ff8ba16cac195f133bdcc373d55495162afd6fe6ade6697b1190817d1c8fefe795426674d0e63f6bbceb42a03f4be41d83e9dfe93a4e136d87a7a139f77d69aba2a8f2fec1c5c0091449ce4e297bd53923306eb2195a800004ba78dc79a087f7c3a68d21476b3f4dc29cbadabc0d8770d207805b1802d2f018348530d827d2edcd7f9223cc043e537a3385e220d1b71d051a22a8f51529a080ef6fff0c9c013da6a699999fc1332537ea9ab8ad3e5af082a8ab20b2761813f1fa33bc5c3e6b7325aeae58e86e82ae2c9216d285653b2150b9c9a4f16b7654d9f4f66ed93bf818ab6c83015424011c0325b5f2dae9f30dfe5ba0669c84c,0x42ec487e5f57502a0af0a48ed1b5dcc59e723e8cdb764231ca637a9d7f7a9bce74cf77475e240b69c2331a448b42735f5e7a1625c949e2c7bce20966ce76a1a653942a0cf3d9d47bc78eaf823ae0c4043e7944008fba8888902d82f0921ed9111ecccc32e0f71979c7776466e1c2880d045301b86b21ea657fd3d95c9c9ec32cfeccca2ba511efa881950894c29f24c370a1533713adea9431d8be83a6dc2141256d3c4c8f5ba7d7771c65af8aab0b155c587337fa2abd6a2a087279c3c4e132646b0ab2a46a26bd8726b81a30acee0d9f8dd8b14dc51e365f8973e546751806faa5d0026b6fe50fc4d7473643b18c3a5ab0247ccb72a27564229d01f324ccd6,0x17fb9bf75995b9d2c5cd9a2aa9d8bf777333695906666664f52e96e004594b12e13e7057d57f7315dbf0e6911eed7dd97b068dcc54c1064d70bdc9c7bcd3e4bf2a9d64fd60e78fffc83965d418371930beb300029cf9dbdf3b570d1f5c55eb82850c8c1a301b11945d8bf794befda02f11e399a7fffcb57b14118fa76eba0593b6c5dc2f2b4353fc4ba81fd40c38967c99186ebcd2f57e6d317361c79eb2d37a2b452a0ce51218df678b6ec4748fb3f5baa5ebadc37b68830869b1b4e87af103b3d071c5378dae923e722ca8cdb231e37d51761ad4c60d41ca3dcaf27bd001a662028e353350c36c8c8c27cec52ad100a44f1b66c2ec328f6eaa1103b1b22dfb,0x5c57275a3e3836f7abb9c03be6678a4ae416cc5f46a50229111439a8746491e1791615219daeba0e3b57218408182f4ffc4b039ea3288d79b3124f6de2648cfe1d10aa8a0b45869b6f602a3bfcdc54a66cf3935a9fb46a1563290b7859a198d047afcfba7add91c4f5d235df9994d487b320d9955bd7a272947eeafbe05794c57a8abd3a796075f7100aec4a887b0f60a9ae48dedf4f12fe7b3813af9057a79db2f837b4c907fdeb84e988b49ba3fc720c45a2cd121656b131a2e29128f5a106a03aa62b6983aad08e4d5794aa0aa44995c3b0ad0080d2b0369e4fd0fc98a32f635cef4323b6557338e2167a6d468c00fd82bafc2ffb5762c8f73aa13513cc92,0xe556debfd7850d195300d924b4ad3bc0f2112e35cf9b5955beaaf17a5dd75ad333aff8380f1a59089c995dd1d820d47719df68b6fa13186eff5cdf77b5aafe97037b0eca831258bf27ba1f1450caec62670adbacddf9bab447a2d6d46f0645b1a23e9a6c04a0ebd1cd43e0b5b6680717ea867563b3ce4a84153e357b75261dc9c89ec9fa3612a3fa48ba0cf73a10b4c9173b26f51be0a56d36d5a64050e6baa4514c8d3c4f421d7881156f01a2ad6a764fad14e52e58acfeec5e6825cae9c86c18527302dbb5e9f12b390a5e4b5be3e8fc36eee0053da5b68dedee08aaf95c7fb87a485297a6220ee8d0f7b72bf03ef300ec20dbeb0324034d12c00205dd94af,0xe1acef5cdaa7fe4cdcb5c25b8344ddb74f80cf67608158d343f399421cb3aa6bcd0dab3f25ba1a7b64d0bd3f2b86d166674cd2188665ddf413d794f4e7345a3f3ca4c8569397ff7e7ee80c592fe29daed2b8431451ca2632396d6ff7a563ffb9ae227884e3bc6e62d3738643a54dc547579d58e8e8ffa606b1ff332e0ce7c2ade850ebc0f25e690a673f5b99e8f614eb3877706230dfb0067a5a0fdff9a2f74d7f1f60ce6d440485391a1b0bcc2777997580dc32b8034fff33d6d9bef1eeec6db73417584d33a33b3ac31b4f5615e92107332f3d69227fbd050a0f19352071194258f955a4a20cb2af088b17e4b48a3e6501dfbf6571b85d760147cfed8672a,0xe6c7393e0fd995b4a1fe492458abe958708263546dd712331b56d98ba880b43cf60578214349a43c1fb2b8176d9ffd9c0d77f04da813e4e66dcf4e4d47e5fa68f09180090a44cfa44ef9d127ed430d5f88d1cfccaf70c3bdb907fdedfd8f3606482f26465ba63f1411b42cf5d8ec8a53444b2211223d70a675fc2ea2cd60350d602d0a1511641b5c76cefcee15ae5e9c69a7a7249e6df2ce4a7abf1b5517cf360612344767979ea82814c1df4d2d047002291febda968926f94f739192641b69a92c0ca5d6e3a0e451912dc63f1412a3550260ab45ddc4bdbbf2fd91b9fed69d670129f180044a39b80e90cd9b15ba5b53b414243b40d8f1326c85fa4ae76fdc,0x2eecda3f97fe07462f9c458a38efd4ebc6e217d7842f7ed4167d1212fa9ff042fb63e70f56611ee6ee9f9095ae88f8b7dd5959a4026b0ab653bb878895da08604803c2a22b118a3eac253574053b003f01bf57864bc5eb3bd907ca504755c154b35718da2312291ab3628ef2fa435baf3c8b143f6a6eef9bd059ac6c752c4008539146a2f4917e20db9ec1679b92cced1ba92d3203034fc794568153d2a9f843b87554f38b18c2e999eb9148dd5f948c3f03a730c3506f401417d4457ffd2f378ef775b8c6284a3142dfd488fcc53dcdc415a0ab1ff33c2b93d426e740bd2d7f4685c579f1c4bc9a4c70c215e7f0959d85908c58dba26879fd3f358588ddce90,0xc3a6d1489374bbf26366a81b04b276e14d3a0738b7c6da940da5b4e2e947074aff344d8fe3f89aa6f27e266ccf68551c5e33bbb75592b35e881e82e338cebc29b72baa62688b3505b97e1f9294438dbef7c52b16112ab327b5123453f01f4b53d6fb9042cc1e8bdf1960bd156bf0f1398881a727344f74cf6b0846e04eef2666489677ca4e1fa28aaad153743ae4a53b316067e7556a37f2fa068e95ac90fb4564016599c107b81775818e31459692e980340898b6ef3183d6123b82604e3a16d2fa76dab4f5410a20294c90f4445d8971ced95054a164571e1187988abe1a3eef8930a56b46849c3228ab0edb826c600c52b2f6bd1de87bcd3bab4387df77a,0xfe6122f0d3f3b44c9e9d4eb2959ea8acb7a521383cf7534ce7df2c3e0199d112f27f93478f1d655c67a8772a9551bb2c84e684c5c9835db1ed038eb38e5163a671c6e009c8e68ee3f574d3843866675d570faed1208d9f680f319be5eb62c95dfe288f9e8c7b3da6aa0260ed932f745bf5f4dad4262940302d4d1741de60ccbdf4b97890ce04b75ce766a4ec3d6c3375e22fe825e2031d690f5e7dc53ba5949c4530369dde7872e901ec58462d7657b33593665000deab770ab839277aec1949b4c8edecb3b7e08a3f7a7256e1b28730e9b307e80f21b35027447ad97594d3f071d2c30fb66b5a926eaa05860231b85b484d54189794b1c432cc7b86eec4b620,0x6702edb46cb3d92ab90fb9c176117b8de3be9251bdeac51fb1ce7ce35764536822298cae8057e360af347e0d6c3b31484b44051cc2a626aea5216a950a6a2e27ad5e69b7883b2a15761b2516e88e825df97a74ed085fb7bab9c2daafe0246995f6c6a45ece5125da29153a06b08ab23eeef6fe3511133e7b3f76b0d10d891e648dcc3d12595696d8cf5f78b83138da448658c60badfcc6253278350218da801b60a3a2ceb49673fcdb4e2e9e6a977237af253535f33053463495d0803c1eefbc1fd6597ea84d00f86a536a9f1dbd7d92b1c2c4a510d0bd74db6f369f5e46576b8e3c5f544bf610356dad2808c5cb0d2ca003cfdbf0571e3fadb7d49034fe5301,0xe4890fc0d0cdebada24b90864d9fdabe2cd5798d3396751d27c56ba3c9ca8c5c6a7ef9eedc1431a9fbe7e0755da5821a9ba4585de6141cd9c5dd3d6bdcd8d96b69b94b1a921a5ae88214f1fe34a7bbce61fe8a297723b0f9a557b97d2a7b72d750228d6309aa0da0890c186c9dbe506ecf07d010de571ccbb20ca4d3e654ebeac3f1d1e92e4970bd7da74b7d425eb851f53bcddcbe2c901320746627abbd0057a35dc7c418b2d6108801c798604a5bbab711644236ea824290cfdebf53d54cc90ce9c1bdf109c9c6467c033b685b498ab81e7bbd388b6e77038370a64eba4f886fefe727eb66f7a74fa7ecc91a7a24ae346f5ee7950f166a0fc4bbf95aed647b,0x49e5daa46cb9b07ade01095d909c18d747d75056264efefec0e0b57a7af760c14e37243da02e6fb2d16d2ebc5bbc7120a8043d9ed3a100ab59bf92c58d81ebe277f7a79a30344b0ef5aea8cb85515439a3dc245543aa71ac9f631691311b0b478af0855d2ea40509993ffa4fba0407c6a35cfbe8f6faa89ec5857b5ce70678fd6b7c07ecea5ae318907fa6d35351f3ecfe8e0cc038bf75276f6c2c01da1486e38c1c542ebf94ee5396b85f78e1a4d06619ffa8cdd617089a914d39ca639fcf0eda2b398510420676e1fcdd0012eae31d5882c8f90fe78160bd89e51c35e7a419b19ac6aacdac5f1fb293bb46b95fd843f3022d4dcc9da50ac7c050e205a38082,0x494706fda7381787eef92aff0e208b79d475afa61d1aeb6f4d382d1f059b1bc32dcce049b940e956d281a230114c5b874e14f727e55bd4790f9c1ed63994ee7578e3fcc38758b9f8e44205fc40280dc3b2cfe5954eac164f6fa7703379c17acd4dc9f96d9bb331d22e3b3331981706cfa473eef371c70e6f7723be162a93fcbb88063eb18400ea289634510eec3ac898ff55abbf7999cc0b273abece062ae14d76dd569eb901189760f6deb28c2eda1d5efad2681a4944ceedf5718748b99ad1a2af70e12fb200206e1a0a1f03dad62d15816aa4379ba9e281acad6637a7bb3489edfa2e3e1eb386c1c823640c22ee1afc1edd0c8a013b9dce3a2f022a749990,0xfccea4695ba781d3c0ccf148631bbf50ed5d178da55eaaa5180d8a6d6b9006d6d26caaec5e3dfde5416b375d538385a261e5cb4d9791f8f47ef4b2c1108baea2814c3fb7cb9aa8b5714689bbad3ffe2df761a1812bf174cd1c8f3a23e73ac0c27f86ebecf5884f30806d38e3871f67b55e1e2fd28321a06b6256f8293db38aafa86890d2ceb1cd29d13687fa1c0fc537996df359a56fbbddf85079a431cd303170b2fa58c257946c5f519947ecb714931f1461b826d535451c9b57a2cd05bdde7d344828c61054b8070e87bab2a7d84c3fb2352bdfb0de1b5880fdcf4c45624868ce80573a485cd8dc4602cb851eecf4b60c5ea223fca6c815752e2877fee22b,0xbfe454495d294744f325550ef8bcc3239038f1acaee00f82c50dd680a217d86cd614101c6c11cd9f5c8fd46974796d377945f83a14c3cbbbf946114fb9d386c671759bfee03b333718876fd6918444eab0691307b691447f874b3eae40d04087d7b0f885fded18d5bb2032a395a23fa316063ef7eaa4bb958ba6b232f0f1c0e6d7f01dd9b416a713c1b065dd91077d97106b70369d0369d036bf685c90a3aa5e0dbb1c4c56a828ad42a97f8a679a4aa46636adb3177f9f14143281d93b2719654a2d445e35462e48818b45dd782c441d6058c6b2b967ce536a7e4ea974633d9b1d46a84b3186224cf7f57b4d22419d9b2cf301c2e5bddb9ef1a01f59d2025549,0x8e8c8b7f4f38b92fb69f9f60bb434292d936e0f398943d492cd70922176a26d853da02c0e0473c37543a5b00c58ca0ca11bfd0ba423b32fe8ffaf377e1ae9c02b9fee948500850c4c3cded08592d8ca9947f834b3305fffc36602eb0276db4f53a571c39eca1317a7971b88bf3b41c0eaa50dfd7c30778d82bc244a8323def568f14b395b9913622222723606543e7cd4e3c1e7bbf1698f7c66417c4598e74606c7650407ba06d3944aad81500186141de4a389c7a3c7b032fc1187b3d60c3087e22cfe655a65d0070cdaeaa7897c0256826924a9d7b7cfdccd2031e4c711a9c59c27da8ca231b7c009d630cedb17c48f7a19e038423837dfcb1986fcf73bdc4,0x2971fd1268083694a8cc91c854dd312aa6e9363211a2ebb3bda0b8bb2eb1c432cb290e2df44a18ddec089ba8947bcabe420003ccaec97f851f5c853484ebbcbdf28f7c2dc4a0ef12ef017ae3487888d391a4a757f53697fad4a033bbbe6962344db905d913ffd1af30854f82c7ce24466fd80acf990af5c2f6bec6cada813c1dbec2c3f47bb8d5b9334749fb7e7fccc6676c8f1c4d7cc6ba9634016f3f1c0c2f9c5ca928a7cf4291b565511dfd43f7f78d9aad1f367dd3c7d38e63ce3161fddd5ae68cfbe9471c37f13288c8d67c9a0968e143592f1041c315b0b7e419ce9720e203d412e10b092715ad08b0b61d3ea19bc92f33fdf743cacbb66dd36f54b668,0x416fc1e99def3baffa95b0a3d6f283521a4fb9dccd51a7e73b4c133b0723b9830d60eef37d8962254004e25994bf9e53e38d744ec735ad8523a9e87eb0bb1b2bd366fa6ddfc8e5f29ce8e3cd35c10f0d81228f560f5c54c0e9978635425a1fd4284c9d409826f371173ffbf5e6f763ca4235483670646832b0757f3e904bd9a25f5cc4570dbc398b9eb2605ff09834cc40aa2d94456d573ca454272df129e50a95d3c0c3560c13cd4752edac08736d5de0c1f715f947adb16f96694e68ecce37d84b54747ed75c5e5fc6ebcb0c210b09b44afe822fd4b8e79bc4a85a4ed096ebf46f017573f4d9b6b49fa47f3ef0b8adbde27aee142e68917c7abc1d7ac4415b,0x5f4a93f113f53a4fa23a00a6cb871048e1cd0b228000680d554ab4057ae9da264a871cff5d2424bac44996aae96048c3b6468c5d925e4c4e380323f2b4866ec4b24d376cc7a293671189517ecceb7dae79f9de2f6629a0bb69a8dd195b65bfcbbf1c601ce26fd89e4e4e39966b5c8d68fdb71452c08532154dedde2fe34b525453a87b6d3dc8156dc9084fccceebb8cdef720c2639b1276aee1b9b352d86daeb020563afa8553f8060282f204d8bb39d9f6ad6e34de6d6b96f7e8a75dfbf436f6a52e2d2b93ef5722883311a0ed8d30bbea0244495253340e6621184929855c7c59fe009ccae7802d25a7d705bd383f5894849c0da1571d28a12bf3b6dae890e,0x4fa4fca7875003b7d6f79a4fc1dea9f7094a29ca734726f5d5add8cc39c1564b619349764ce47e64832a90dbfd48e7b5ccad74d7afd1d2777872ed79db9c195532bba5a29851391a006c1874c860143a33ded38b41777b38959ff5a426660d20f073ff6eac9a709a9d46c0f2858ba5539bbbdb76bef2b6199887288bab4a7dfc2a9aecc161744e79de46177587f203799e6fb9e4199ec44b3334478ee4f37ea5f21ba700000281ffe1056923c2e2a4c5bbb1b82c9f95cc47d4e9b78a7f01b5cf8cd9ace7164d26746c35836fe59bd0ba247848f19cabd0e9e07a7a5be5c164a2cfeac8216455e374555d648b76330b1db62e97794d6a362588da4b6cb2899555,0x252cc1889b44d0eb60170626479da229179faf6779d00e8c8c84ed88bed9a1f473c9c2c36ad466baabcbd594432eea48392cab27539db471d32e84f5b63121d5d7a21bb0a9958acf8258aef5fe8d60e01b95e8681dbba66b332f0dbab87a0ac2c5caac9c8ddf6896e4e9ed4dd1eec198e9416461959151249b196488a39ea6aa8247d7bc623173a636077bc24e900543c6dc38e8e4139edc745552aafea6deaabbd1367f3265606461bb9f922d75d89784bbfb836adb34e741ac426aa3eb42634abe7c7ea28b774256b4631e2b2917ed4d181fde2aefad17cb9e1620e3b994a5eba91bb1012d16dc2358d29092ee9946bbadb0d3a96384dea840eab1db363bca,0x8c585afe926c585ddfd0f4e7aa877a9beaa6b76207b2c863d908e05817fa3b77e82e6e43911d2959e825812b308bdff41b0e2ea0ab8d3612c33f68bc6c85b372ec1cf86bfe93e93e953e088893a158bf258ced41ddbdde8c4e620001444440884356abecea2ba25f039028e2dc4c84e53f5714350e18cd1671c635f4cf3f9f9999f5585eb30e7096f099aa3723682b15e46a942692aa011f84b4e0b57f23b8288bbbc0d64451791ea61516b67d96034db2c0b899e19c069be997bbaddc4790143f4b5b397acb6d0ca7921f2f45978dc4f5e1b5ff8e5b06297dfbb0e3796f2f93913fbac8304213bc7000c0d0c4be4d1bfff38717a80cfc200822b8627dbb8351,0xeb8d141995cfbd9a0ee6c7719c9a4a77e7dde764ca674babf5d001d0c84000101040900e0ce7d3405cfebfe78333ff588d7cda3ee19449ab49eb55d468cae5f83add30757a3337745003befd30637d43890b3f7e70641af8ee29c96570c625983732e00de065747f7a3d5d712b7da32a111908edb49799da61791507c39e66c7e32a6f43589674123cbc31aed4df9c7f0da4df03c1d62bb48290c2a4c79ceef5de8d7e3e32e2b39df3def23297314da0453bb7204e1cf234eef0c83ccf44a955537dc333ef23ee11277a7de4f8435a23a1fd2a79b28f84f48ee79314bb37cb84385228b5c2dce20ebc75fae03307ec5edf7a38ccbed19a4041a8f7b9df40caa0,0x9a6f57bf9b03316711d8035146a194167e0aad27f1506672b7e0a6da83e032a1ab6178472fe30339bba338f1180e6e3dabd225edd271c067dbc76b8dc6b4c16f1c96fdb17582748c908ad67f99f6929d1fea5e59c14623d05f9a29de377906f442559d61fb1f1d03a6faaf49e36a2514f2fcba7e4038d948b1ec33d152088893b1cd8d84e7b6f1e99a95217947720d6b994bc11d1ffa964146b33332151d0ea41eff7a58675e69f45638d6310676fb0182e818cb06414fc5e6675b1821982e2fd483f47686207beb9e4f6af72cf6a535553a910d2a5a1cffd8aa7c081f9bad9a9ae784e52cd07dfded49d1f5cbb808140f66fe04c10b00135555554f91dae6e2,0x60faaaaaab0c61fba37b8bcc30cdbb93117a7ba3227f45909b319de2934833bfed64760100381954bf3b10186742219f3827d89aaebcf2cacce22367f83be3ecf46850c733de38f43480510000800005ed4672a170cdb90f06a56aaa0aa24fd81467847c0f5665c4af46781c003be2ec1bc067c5eb2d09332280644dc9181d3624ecc1a2d6f9c8711fbf7a19e0a0db26e5c1e118f6b469cabc6b0c8ca57b74d10b97eab25ae7c3ece2a536fd70a218a22c1281cb4490b9d69463017ea4906976d7b077fcc162fc9630a44d10f99c2aa90026a0b7c883f00ae8d704009cd06b3665f56aede8195c361c7bb890401913a763a4dce07c06637a4da197f7c30c6273,0x36425ccb9a445b4dfc5b7af994671060f4e62f6d3e6569067ffffffe19d10b7b68bac89446b835581ef31b37ec04303532f1895ff7fbe983392c5c9ac3a326070fb6361d539e0dec1df38832240dce5df5b81aeaa666666668900005421d599c93213619ae9e11cb36cadebbce16a95f9336e668067b21bc96062cfd684e1802079efe95a5320544fd95b51df2f71814fc9729f5f3c57f414bb3033a6716d979015389a35ec56213a11edbccccccccce5c7a14ccf50f868630a5b8d6aa28d331c6a73a8cbfe6c540b467ba4f64a0ce58f4e86a153db98afd8ed9867ee2fe70ed93a98c1a232b18b4ae0aaf983b5faa77b45f4253a438bb2d3d1b7fddac44b0de,0xe951597076c43e83dbc7901c11f4dea93a4ccccf69e8532ea53774ac1af20fa94c07b3d8958d779d2fa987bd575fc0a9e652f730f325f900555b68a00599bfd534843756f9ea156da8054974d930d0609f55cc440d64292ab69157805608f6209140e4be633df599999a7149cd99459625ec61ac61b98f8479c3fa80d5e1d6a17b88c0500ceb81c7fb23637f50cf2838c6b9328b2888f6ce25af5eac60f8f0e7b57da66b8c029d4bd1eefc256a7fe6999bbc4ab2063b4397b9a1feeb54868639b94bb9abdf0a50d1c1f0b4ae0c2fd46666b2b8954b42191a0f32a935d66fc708110fcf572c5e5789da3d3f26e1cd7c40b2b87a8e482b11499e56105c2816732e,0x8925c95d235ac1b2f50b646076e87a101b008079752529ad6ee0d90000139ff18106a06a9e792e178ec300c50ec07869618a5ed74a9fad51614b8b90e4fbca5db9c86ed8d901b7b255679340dd376b5d8433ebcbd068d4002cc83e7d7932237f0573575dd567261902094ab8dca1acea29132d7b11226ad59d1ff125562f63564011e4be31dc7ffd610259cc00aa330c3950e2caffe0810d8d1c5bf35a00c600ceaccbb0aed189cd3c3583ab7952c87e2ae4351806dbcada92cbb868461aa7a001fa4144e43686b143dc9bd81e6df3c356ad99e654eda1df8d2a444f91ff19f7e4906c8d171a17d08cf8e3bedbeb834ff7b3be1d8746eaacd725007014833e4d,0x7fa4b750ad58b4d44708491f149d214a0ef5d7b2d038119c2ed360978df1a757e4b17e4b14720caeb5d072662293cc9b65925ec8ac4ec8511d2d88805033a5555555575ff15d55a557a768af17637e6e886ffff65579a3a6e324c98fd9be2bccfc6d9fae383f0664af36797ddfc1528a02680497aaaaab2808a9931756102fb26104fb7a803864a8c05010b20da274bb001b6afbd5835ae33a87bd85cff3700dae6bcec38c5d6322e8368e9c1b73cb1839c4b06d84ae03d5c100040670cf73c209a8e903c036538300cae59594f2e86da4d2167a53ec2aeac3640444492099f332dc1b3fcc50f1300002ec85ae15b921199bca0da742e7a8f679498fc8368bc1,0xf73779d5b35f541b4a005fcbfd8ffbfd401b8126849fee999f268b1f716121790d7be00bf8736e510bb81f8a33b140d5903e87144d58bc2525f7865132236a6108e1adf7b1a9fc00920feb333db3420843f8832681a08d2d5908fd3c436b1b1b01a9a0eaae02652475733444b78e4a2f1744f5d0efd00edfc7a21d2b4d190ae2c1966edc42d5552bb9a86aaaaac005555555541550011802d1a454ea29670770252aaaf59bb58b943740917397dc5ff100cb768af496d55647feaac00156789fffe76b832abf9e4b01e112305c9ae3721726a0e2db385a3e936fde59f1bb410d98424a6d91672323981c2ab5f111812020b22d90b6205639d1b008c1b2692f81,0xe0ffffefedfffef40cf99b2920d79cb67898f01c703894398c9a58c01c1071173cb179e2c5eaec398386880f05b02520041520381ad37a323ebe18672720e2006000000100002035836ced064f3bb438b3a3dcbc9ae05c5a99aaeab555ecc04fdb4880a08f88b55eab546af189d06583cec025c10c6ec2a870945e8d2d02aa3d658993f7aba16bd20a59b992000002af07e1152cc736b86a2040258146622fa6e61e6bd915ec1a9678bc7f792d4e9c129d53a1e942245f09db04a0004bbe391fabd5c1ab3fc00000008aa7dbabc0866956a50aab9b827c8ca7e9d8eb632975bb2e156a10cc194f001837c56f1c883b0f3dda701ba0103836022e942ac706f05c,0xfacf322bf000736cf4f4098203a6759a7301d417245d3ba7b9e7f0fbaa20edfa557325c4c4199de7f7c1d74a1e94cd9f8367c36ead07557e27136b6cdb3d8253607424b3a8c15d85966cc525074276cd488ca12257fdff301d4cfe4fd07ff283339b47073753990dc3191403637ea7cc6678bc7998ec7dd860be2faee48b3f0491cbb757a10f518cce6cb0c4de642e507f95f436b1221ccf8ced99083a0507a5fd2bef40ce78af07a0bbe13360e0801f365a1ff3dbbb1afd4c03c026553a0e78ad03549e1c533e43060398a46e98f7fd530f7f23e0e65c8ddde2be2f0f27fa0e0c15a852a619e014d6060e44c2cedb7ed1676b0a7f0e4c0577353406158a8990,0x47d16ffe3865516773be0ef8426377f5ad9491226238083cbdae6de215d040338878fe201ebffffffcd588ffb01a9ff836abab6bd293e9f67b0e1e83fa8eb834f4c080455ea2e1e1c084a1df6e84266e76339c83ccf72ccc2bd718e0a7b6f2a1079d5cadf3f983e307ef05f8c4fc5670c7ee9a1d3e0cd0970cdee6c63c4dee9559ef5f854300f0a316b62deb83ebebd70377ddf8265d4e63b5d6a51941687af61f4ea611f6fe3961486ffb106ffd7fcbfffffffe8c0739a18892f73130c5b4bdd383b5aa7aeff99e28ff5bc4a5075901afd4feb0037fc02000e7800000400005fffff6c072bfa408004ff7801000c03948ff7ffdffc00cffffcb01d240c34dff,0xf20f2aaf7357a15048bc1fc31cb18fdf1b8b665c67c80ba78e805330b0abd71c24b0435916015086d6ccee8dca6a0df913dd922c077ffff8007f85cb81e6244e7da0f43efc6003ed403f856df1c6dd15d82892d47867380e0fd610d0f74e4f66bb14b84afffe403f0a8dc0930c827ee3ed424e747d47fc72a9fd2f67231ec494c7f9407acfda5c7ca5c5fc728b7cb1df16b01f7d7f81339b4c222b8490fc0e3f37e5fc22ffcebbfb3c20080002c407b87d0cd203d3425d406fff7fe007c582e01580c200404400402003d4572b6f7c55a509bc0001b701ebf75251b84ec93014148f92057ed251a9b99d5dd37fb676a511abed8bd66fa04e54f84017f6407713,0xb6f8e52aae4376c6c144559c559b4ccffdbfa2f5a45d25a5ac60682330cbe96208853b58c685db1af6671dafd988f92dc00d638cabb21f28ded96a0e44275b27f2b58d86a7cac3b9912e39f42197a3ca113de147d6dcdfe84db2f4044ec30ce2564ffe6a4cc701d1a2711aa9b135ae6f95501bfae5948794a7b7bb18ad930f4e263374c7559584d3cd8b18d2b3dd23ccc2755967693d575b7f5952a9b11396b8c126df88e291409008821d5c1eba222cbcd5a5f5df1dffb051a4d02d5fa71c1c4380fcef3960bf454cde255e2abd0a5cdb845b347eeec40a1c23ff948a53b70c2a137797233d2fdfef9f48e77973b964b0d4004ace1ec8b6394640a730f411f0,0xafab37a5759cdc4615e988fa353f05510c6a244bfe3a356ce32b5716e4a256f9fac9c42da81b4bec079374dc12f5903f6f66572d46fcb33caadf51997e2cfdd97b59cd8100a955905df8d75d7d7a0cc2eb636701b6b717171d050d61fd7558ce333273b8a28fc4f145593d75029686334d905a15879d8485ddd876ad6571d772113e4f1630550499d6d5a31060855fa14f9b2ba405501fffd43e357e379e02c6d32d43d28ec7a9a99ae14bff3ccbd82e09c111c2573fdb7badc60e442c8e4190d48fc8d3038ee1c26b0c7b2ecbf47b06934c95ac39f76c193a65ad05e6aa5ae86a784cb9efbd7a1a067881ccca5f7256d24308d37de0e65c353be08c947362eb,0xce64117ce49e83865c519f8805d1be097c8b55416f137d138d4d2c601c2059611b0bec4702af5b07ab4bb5c774992bb922fa59ffb62479d6ccd90f5c380d7792da0c1ddfd2404aaa30c1d3f8c266b6d475686e1a782981d2799e3dc3ca18623456a2b3e3e2825d83fd9666f3b7441c177e95a20597ca32653ff41ebf45054e2439e5b74327b19fb191ec1c4750e32603fa32631aade087325d2888c8026a264b6c72c8bf3e34174eae988db34f248e4a71ee5f89526f0ccdd3f36ff02f43e42b78e57052d09053a777f558003cd4396ef71ab8aa70303b84cc6ef02ff85c5d6d05db42c13c38694b4634fe9ac827c3d73caf87013da1d6de08e00b06bc49a3b4,0xceda980438f66bfaaa7ebfaa7a453cf14c3003021be38c351985d56fe8f80bc775e005d032dad874be645c6a3c7d309970a26cfdb62b2382f8a6af8c337e18223fbeb34f4d7b7a5590ac3702d118773597eeaf5a62b15b90c40c1c2ea7aa1550f0d6cd072ace133724eeeacb31ae4e7ee7315eca4272d947135bbb2decd9f4df6e94c75c76df5e8ca177df34eec82e7ce3690b26637e2d97359c64e604108111505aaaacae7866dd9f86b9cf78734660b5be8918dc7bbfdbdda131581667e592d9a2c30b1ae7c80aeba5bd6936da3d9cb03f4047a3e28a86b72d4b0ccfb8d5aa85f1da94d34d56b6c7301737903d9fe973646d25dffa0b0af9e6b99d838dca69,0xef3b0ad23ad20fb60c130aa8c721c2d7b6c741e8889005cf02bd11221a77495be783901ec0f5742e179c95137b74d49cb5efa0995d550b7256e2c3469733cdce7cb2d0861dfeb982e3d5c47e09ca4588d0cf31e80caab40e54f3baa913dfc9f75194a43bcf0b2d87a59c546d4d57172ffc00b8c7e75d38aa67825c0fb0fd99cba928ed765a9036db80716f5ac73df6153cdc8cb3cc0776d291c406a4a8f81cfc558a4d4fb16d1116701fbee7bbabeb9f475a9684565d6201a0556dcd4a7d50fac2d09317f924e9d20e82579b154e86a73f0fcc4367649caff3e2f7b936c0109484ff0e3929888b4def0552b1fe1fd5d9e4275a82726c9e5e32a19a07f2c97976,0x7ecf1954bbab58140610e081ca274404dcbc4d83acdc6d1cbb3bf67c20ab3d94745adf8807622b5f52004c08b2470204c14059239570850b54c4b5c8d76bd0424775c4786637a2e7ad331ce8ff5dbdd6897b57712aff1fc508a507db22e76e7d2fb769172e69bc970b96d22ec6f14eab55ec567ade47612c2ac36fc42716d3b6aaffedd542c56ec2b4941d69edb1cca3e4ebb946df683a5240b2798e9709f2e0ccda429266bf950d14462c64b6d5d61608634b27e9b6f0fa5134c21db360626853dce398c0957c9999827e3bb74c04a1d5cf8905baeeeab06c6eab981d0289e05ba8ac28115a7cb97673ab9ac16bf99be938f732ba4b7b514e322e3c9cda6f52,0xc62007325323d37bb79d75c18a633152149daaab7f42e01e41d04f5815eed3e26a5ca468d4829d0464a3241fe59d651860d1c985075c518e15fafe6635f75a7aece94d3b9ee3fcf0c05ebfed2c25b85318cbe969f900f6ee630ef82e8f28947ffde531f679b311ffc8321fcf378df633480ed421afb036d5188c4c0d780338a05b66f114ae71af518ed90dcb2abbea14e932600db1aa61d43f21c2e514ef53c9cadf26f257f09c3a3d3b009d534ca1e8641dc7b130b1c80c0ea9cd5c984e8e5add0e9f49d3363f0020ab765339b97a6eaeb00d178a9e53f0a7ecd885f866957ba4b5b2e503ece293b4fdb8d89d2e56a2b6c0b47cb0875b64899861417add1a9b,0x394f4ce8555c0ffd4828c84b70a15d914466513a8b527337f29ebdf48a532d64034ffd0ac343de578bd6bb21a464417ed64e4d2255fec1130d944ac6bace5904048f4766d62409d9d389b0c468b48a777c6847d626c9b611b6aa82befab79d60ceb27a2ed15cca17871f69685e1963fb955a4d8d2bc68a3832ae934d6798f30e88137ee5501754c3fb765bd3fd44b76922818baa57ef69e60c9c7b29df20b04d84a14bbe1b6d3febc8913e05e3c670dfc44c63b06212ccc3f55c26c49eefaac8932e5f053ded831024399260a7725f423f8033bf50e8f59dc8c43abbfad7cc39ff0a67ea8008541e57286d916668fafd51068bbf6276ae71331618cb7af54107,0x4d0e9526118d01b262ca205f947c4d44eb4e1d51f5d24afb7063abf190d9cca75063ae4357e5c39a825c738c57fbea5477ec1b5f75d009244393d58c5b04829f45c2b854eda91dab4cb225cbaf53eef569b94a7618ae750b66a7d93664c4df47b88284c7092bb7ddae6457fcebd2b9caa3c205bdb69c93cf83d17e5aded4911b9ab1b7701857ca4a57e46e2cdc5339f6803e3daafa1d598511d555418fccc695f52e9c969e2dbedb597bd056685082082083ddafa32ebaece417a5399dfe29d1e48273de602eeef1ce5284ab6fbcb2821f87412057df1b2af9871872c763d55da0f54cac426b9923b99634514ad93011c4bf0a3f2992cc89e79fbeab2f9e35fe,0x193e5a0b44dc9480999687fcaf3121bb9752a99de97b50ec3472f6f48df53db2e131d177963a0b31219442cd8d457a07d3f0f2935a2fba1b0f284a56c99771edd274319fc3d0a89df114d7773171f185803d81844b784659f62d26ffa551bedede85e676e65db76390bd0a880d90ae3fea20c25b979ef74ccc70c891f9ad71d5f713cc037c7d2c6aa7fbb8b17943294f520020643979a647d59c9a3f8e5e87b3d12bff6e710f0ec992b405fdecc011fbfa9ae4295c4e9df7b2314c6145875de667a9f09106fc1bfa9a67519b40f075c623e9c8bfddad38de4090160e2f96ce4dc4ebefd6d6383ea3e719385d5005d41578e3ad087f325f7cc283ae36c85f772,0x28cee4457c9a33818fa15fe8fb5be8c96311fd49e814968698c2e7e8c3c6f06fa9e3a8e53ea9f5ae43fba5d04c8a408c40fa1303c670850f5994c23a51a360a0b395164611f3a9cc91d27f133922bbaa0fe5c8786202269dd60578e922827370d6b5905ad58a39eb8fde5944031fbd64ca53bd99f0a1f81a2f96a952e6c03797bc20e01dc89a67c4dc5516578d2f3630f9cacf20ea94fb87b66d41078c1ea39b943740acc6973ebad3fb24968b7628a58542ee53f1fec5cca1077c88832523c2740ded40bc98b18edd9f97fdd3fc462c9ad775ba9208dcc4a44dd46270d4a91445c6a320427065ea601b394f25cfb6018da0f3145543c36a263d6492c07aeda1,0xd6d85aa3ab4bd7ca82a521a646f062478c53ac2ed09cfc4ad1b5892695f1e6acef8cda53c00e73f29c3136ce3e5900c4d4623f0f6d33e28169d3a7eefc13e733bacc100a659fbe3e4b5cdc455c9538a5854bf477748f4974b01c541bc63569aa63b721ffa58e63ae8c72ad249644a86f5b2a401496afae8deb45a408e6fd2521e264739b7796206f3f3e15f1d78c5214f192f9634e164beb041841234c54c6c744e221599c20b2d87c682d90a545ac112b0cebbeddfed9048df03f5181cc79e4455a9455075cb30793e58652ba80e0ab622e977088843a3e8879e5c243bcf6bf0043829d487c552007e3cf9d07a24c56369553aa84270c8c4e520719ad560b25,0x736f78da530383d5253ff5ff8ae605f85b968df3fe8398af9c52366d7aa55c5f5159d7b65f26add1d64612291ee65aa1e72f456d99ebbe840f1f0e5c558b8f7e997a9a247a3ec510544c2fab0e9581621d9070aeb694cd4822caee83d9f43d5b5331928765fc95d3cc69f83aab94c4f743ff90409b15e79360aa2a259602f59f8303394ca904c0a8b1cde8f9553432b945d9d8b8ac362c1cca8f792ee69c2fb36a93278b3d83951e067ff384d639e4678062904043468637befdf2bbaed18babfed4652089791dee06bd126839715f6f25acd4096f31a932548aff8cae437044da47a7aee465b4c6263854e35a9b39abab9b9c801e7952d245e4b956fa515b89,0xa62809bfbfcf431fe5b8499c3b4812ecab717865cf93e5f4e3c0b2ef7dae55cfb4e29c0f0c5ccdb587570aa19bba20b7369556498be8c9b9dd0ebe73db7f7a93959ead9386f9e8ff295bac290d575302268d68ca5a23c843aca265b7c1d3d93442874da712d5902627478a02aa4f04829385841e7f467bead4ea5e7446ed075245c6e8532ec8364dce75ce2c10811de2bd1904aaca3fcbdedd489eb62142bee965bf13780264a38ba31f8f501d12fc27e587526ab55aec9b12a2a1d92be0c113373894df54329ea14b327eabf247ac77fb41ae1d88093852bec073c17c58ae1375330ef962d085dadd1fd203e2615391f99fac92dbd6b0c2cb2c145e8212dc0d,0x537665609ef87534742637c1d86ecf0f6f17a78643c27cd2571c097f5a7d58b3ca536f02184960682bb53439bece2b11e89ae55840d7d9424712906f84974cd522c57fb0b85098d57cac172555c6235d94b47f14c8c40680c9a463089651876fa809fe3a1ac577ea79a43cf42649bf24d6baa1489df049169d481f57bd4a177b5c8d05e38789b63c33b85c27e8cd1aab3afe3bca28871ff2db81711cc4533a43fb2f3476dc6419ecf9e6646d0d7a412a5f634a9de33768c3ac965bd14f4c07b20e27938c2eda80c821d5a559ae8d0a95ce26271fb227158d0d02c58bab3e017265d29c8b98938921eb23f2ceef4d6d2c91475ad58b18eadc56323a820ae8c604,0xa23722a25db40a0edc7367b9f43aa56a5b472fd240fdbb57eb60715138180af0bd201d8a83202d3b5d95a84b0f36161fa70279a354d8c1dc26809479a05d3caf6091a8a36ac86b7c4a2efd49313167902f20cdfd853b11ef32da6e7a7465e3e305b82ea0c19cc120adfe269465007547e0bedaa52b4866b9777e7bb4f2fadac16867c4b4ec6566995b1bb6542a4fc5521a89ee6ef20ec5783ac38b99d9ca1ff327fd8e039c9a404c59954c803d296aeac34e4563cf8c324298b388df9753c626dc5bed41d52256f1bc2cc2e70a23132f6af25785e21293782a20bd12cede8a1ed0e490fd50ebb609da24322ec082a0114351eb3db1c4d9bc764b9cd0bfb5134e,0x41e5d5affc03e18bffbfaadd094af307f0945a96f3c6d06c5bb9069950953e125b2c5d596cce05b098acb77f86db4b766eda5cb430a1ed8bf6f640c28f2a50bb1710cfe94886e568651b3fc3e673f2f2dc3c348747a9871629613c1c9a7d726bee8192474933b66c1fdbeb267dfc5bb7dfcd4f428faac1508e60605ea6d43d76c3132df3d37f0d0d71e70181c69e4dea1c8712ec74bfa1693dc58cf32d2d030f70ee0acf756b061fce6d0605b245664aa75f5cbefc38249ae4b8296b2ff9a3b16f3a9cfcbe7b26dbdbb7f1c93e83f30a3db14644f4ea88ef465b738ff074ec935501b6dfe1e3a6c0aac4f22e85fdb7e7f5a227a6d2ce55181cdf0f173b02caf,0xaece9391273b2a511956a79bf46b635f0f503e3c97ef94ee5b5c349e53af00b14658900a18ed1f16bf9056fdcc0f83057e024ea243fc147c39e4f5829182e6f57d7b3ce59968cde6b207bddd6a762f55f220c285a58c82060492b6d10b3d4a83112164a9195d4d6fe11ceb09b6a3c951676c38040345fc8de9f8045b52d2ae0ca608be1e5b94ec2eacba3ebbebd15ee82fda84f1d6b6db0aa74dcd7e532d93a0deb0744013e1419646fe42772ad58de4258dab94b7fbd4775386b448bef088eb177fb178f49e11539993abe5c4fa7c97a0250c6c4bef4cd9630936a5447018175d931c69843af328d35fe1bb2cb8aa8e8637dca2301dfdfa09102a83d2a0e4d2,0x6576bff5f4d9ef05731ae90389ee591f2bf8f72632d9a194ccc3ff0e2f52c5e35b41ab43ef8e5d2acc10620a13589c6951b5e189fee7709b4a285e0b45c6fa66ac653f3ebad6d281d6f64a2f5986b1f9edd0620f91a679098eea5a6f6a23e2b4ecdbb64998a517e39fdab663e3e692b46e7a7e1110863b281886cc4632825dfc1e9b956655e0f2e53f2b01089d6ef5e49b5ba69252b8b11f85e14c1d195642e2bcbef17c3fb02fb5a57fdaab8777f11d3b0805f8543910f5f508e25ac7c7602d7b932f28913fe80db1c8df2b2e086b7fa4e78451fcdfb959149fb2faf58f7d7f0b43499c8493611fd6191bdeab1f69a51192fe1ab1c8cc7f1a2cdc950dd43919,0x33522808a75f903b723a1753ccdd812152895ed2c500355ca66dfc77f0f59a447652d41a65d0746bb0218389e2aa766f2c66019bc996fc40dda7371787620d5f9fcd18009cdaa140ecfce3cea5c36c635411d4c2669d23adf5afc25d5d18f8d96eeac11eb2de88c7f1218b759e3cb2cf0acca79bc206f70b93b324f14040ee0cb5e799bd492fb446f131a5bb7450354a012d613318cfe77a89d966ccf64a688d0619de7f29168863f20c771bb0e000f3820a1df987d87e5326a656319072535e9f96250195f7138d001cc0686c4b007442dbf338ba4e715ae9716bf13612154f0c94b5deea792f53e9bfdbaf5fe47d988201896331d86df32514742dd34b79ad,0x1d0533d3ed5f744cc6c1a1e0c05fad603ba031d5bd12ccf8268e479dbd7e7138555b4c527649fc52d0e4af8da7174a85c7bd8090ecc31f29a5662fbd6e28525cdd9a0862383f7cc4f90beeb54d72075277514b4cd56943b5251d37e3cd78495e2a15f960c467036d18542a348c31915a39a4d9c3fbebec47ddca5327254852a01cc5fccafb35dc2763ff3f9e91e196699c2dfa6eab029b9b74c31c5b6e675a08e8eb9263236ded9376afacd7b7928fbb2b38e83a542696223ca5cc725c1f914a4a65ab170c89716cd73d8354bd435380ba1d4f2b841f2451a398c5fd5f6c8d1c976acdb9c4abde2c4aa7b43bffe6edfde30bea5083fd18768e6d3005df2277cf,0x43b9dc14781d49a5b95c564d14bc950d0b57585bd8aa886d3a04e8ad2bc55cfd5a9a8ba2885ebbfaf99a1e08e225d853823a6d15cd68a4cf1cf4b1d8d46da595d3d6810e50dd9bf476e4f0371545416962ef0b8911d417376285f20d166c8cbbe60650cb3d417baf377238d8c59718c0ecf045f9d3d13fa4d3b739ae9f5bc8af5692094adeab1ec3ecfba47a069bae8808f5d78f527cdc1aff8075901591a432e9c33fb59bff33eb8a689606f9f7f939ba843876149a32eb4b7e5823083deee1babeef7981dfeb393bb3219cb7742ad5ee4eff65f33f0bef0b5d36c6f9f97fb004e918f47736e79b19fad9f8414d773a78188f5a43334ba58aa4694e00ae3024,0xa9ccca50da893eb1164d217e94494ad2138fbff8175c63082276fae4995c4b0d12d0510aaa93ca6214e6a3dbefc3122cee5ce72b787841e0baf197f8b1708f6fbcaa1a52b993a983bb22f9063908bacd21adec986244766b6f43a694033819eea7020b8b3f0f9bd11cea4b5f35ebe31c6ce2482253fc385e594b576cd65ef0269a4f5c9bb875f6735730cc82d90262404a215c12ef4d43a8aa02b59b6b29545beb5dbc3cc40f45e892bdc924356241984b9c1083cf079458c4d1a89114bc5cb6787c2979aee6d7c7470adf8ec2c077dd89155ffa9e7085c4d8708a18c3bc082d9b08efb6c6a105f46566a6b92dc61cb4a818dc82c09494b93aa8213d1fb0aebf,0x746c0acd1ed8e060bf2d0c3951f28ba83fb5903db5ee2b1dd762eb888a883ddafb009786a130693542f54b2bb09a2e5bc3bed133766514aad7b788fd1415f90357554f9d8efdc1c329ecb2e604bb723923e17572973abcba8247cf61d9b4c7ff1eca657471aa6106d739970014f55c7f5dc4869f2a339b8f96fb3a0be3ab2b67d879d1bcb336abde94b2d8465e86109272a969b963c3fb1c6dfbaa63867bb51c905f093d2652e3a37398fea4180d1119d2cdacc59db39cf5d780ddc538a79faa4b17f3fbc76472b8f227c7d6b857252f03ba667f9f1c474a32dc065307b684272d4c1afcaa03846b9636ef3eb7bbaf4f0b70af9580b50fda63f52984f32a0d86,0xe544aca7970ded94f37c20dede3d616482a7647b55956867ffa5be57395a8d3c02ea8de2e8e6fb31b28a8eda9f4d1ac8495e541677be5fa664e93329c685571a04c2cc7ccfdef325c33377e85454177f52eeaba0daeaaab53ae9102d944293cc95bd18245c1cba083baf34334533b97f3c339a42a3ebb5edb298f5c6695818d42f754ab622083f5c12f15604abf8e427923752dcc51cccc1b3efcad9e254f48a42df54195e22cec49c7928c8d79dadf8fc656fa5f1431250e7f04bc3679a3c7e7787ffd47dbdc24dc5d4685a81e05f93df24c644cfd6a843f7ec43ff04109af9f110381c7fe106c770e805a1c004c649613479f76f42abc3e685d036c24fb185,0x679657fc8662984f32f8adc0d07573c7f58038653e3707e24,0] : Array Nat)[i]!)
private def page (i : Nat) :=
 let a := pos i
 let b := pos (i+1)
 (((word (a/2048) + (word (a/2048+1) <<< 2048)) >>> (a%2048)) % 2^(b-a))
private def search (x u : Nat) : Nat → Nat → Nat → Nat
 | 0,a,_ => a
 | n+1,a,b =>
  let m := (a+b+1)/2
  if fld u 8 m ≤ x then search x u n m b else search x u n a (m-1)
private def scan (u lim : Nat) (add : Bool) : Nat → Nat → Nat → Nat
 | 0, _, a => a
 | n+1, z, a =>
  let x := z%256
  let w := search x u 8 0 (lim-1)
  let lo := fld u 8 w
  let hi := if w+1==lim then 256 else fld u 8 (w+1)
  let q := (z/256)*(hi-lo)+x-lo
  let s := w-1
  let d := if w==0 then 0 else 2^s+q%2^s
  scan u lim add n (q >>> s) (if add then a+d else a ^^^ d)
private def op0 (i : Nat) :=
 fld 0x7fe00000001 32 i
private def op1 (i : Nat) :=
 fld 0x1007fe000005fe000003fe000002fe00000281000001fe0000000300000000 32 i
private def op2 (i : Nat) :=
 fld 0x3007fe001003fe001001fe0000204100001401000013fe0000110100001081000010410000102100000efe00000dfe00000c0100000bfe00000afe00000a01000009010000088100000841000006fe0000050100000481000004210000037e00000301000001810000017e00000141000000fe000000c1000000a100000061 32 i
private def op3 (i : Nat) := scan 0xfefefcfaf8f6f4f2f2f2f2f2f2f2f2f2f0eeeae8e8e8e8e8e4e0dcd2c6b6967e562c120c0a000000 40 true (i%20+1) (page (0+i/20)) 0
private def op4 (i : Nat) := scan 0xfffffffefcfbf8f6f3f0e9e2dadadadad9d9d8d6d4d1cecacac9c9c8c4c0bcb7ac9c8b6e4c3618100c010000 44 true (i%20+1) (page (7+i/20)) 0
private def op5 (i : Nat) := scan 0xfffffefdfcfbfaf8f5f1ece8e2dcd7d4d3d3d2d2d1d0ceccc9c4bcbbbab8b5b2afa89e896f5638251a080706000000 47 true (i%20+1) (page (33+i/20)) 0
private def token (z : Nat) : Nat × Nat :=
 if z%2<1 then (op0 ((z >>> 1)%2),2) else
 if z%4<2 then (op1 ((z >>> 2)%8),5) else
 if z%8<4 then (op2 ((z >>> 3)%32),8) else
 if z%16<8 then (op3 ((z >>> 4)%128),11) else
 if z%32<16 then (op4 ((z >>> 5)%512),14) else
 if z%64<32 then (op5 ((z >>> 6)%2048),17) else
 (0,1)
private def pack (i : Nat) := scan 0xfffffffffffffffffffffffffffffffffffefefefefefefefdfdfdfdfcfbfafafaf9f8f7f7f7f6f6f6f5f4f3f2f1f0efeeedecebeae9e8e7e6e5e4e3e2e1e0dfdedddcdbdad9d8d7d6d5d4d2d1cfcecccac8c6c4c1bdbbb8b3b0adaaa6a19b96928d8a85807c79756f6a66615c58524d4845403c3934312f2d2b29282725231b16110d090403020100000000 140 true (i%20+1) (page (70+i/20)) 0
private def optic (i v : Nat) : Nat × List Nat :=
 let z := v
 let ins := fun x : Nat => x%2^i + ((x >>> i) <<< (i+1))
 (i, ([ins (z >>> 30),ins ((z >>> 2)%131072),ins ((z >>> 19)%2048)] : List Nat).take (z%4))
private def unpack : Nat → Nat → Nat → Nat → List (Nat × List Nat)
 | 0, _, _, _ => []
 | n+1, z, i, v =>
  if z≤1 then [] else
  let (g,w) : Nat × Nat := if z%2 == 0 then (0,1) else if z%4 == 1 then (1,2) else ((z/4)%32,7)
  let j := (i+g)%32
  let (x,k) := token (z >>> w)
  let a := if x%2 == 0 then x/2 else v ^^^ (x/2)
  optic j a :: unpack n (z >>> (w+k)) (j+1) a
private def node (i : Nat) := scan 0xdcdad7d6d4d3d0c8b99e70000000000000000000000000000000000000000000000000 35 false (i%20+1) (page (172+i/20)) 0
private def hint : Nat → Nat → Hint
 | 0, _ => .packing []
 | n+1, i => if i<2027 then .packing (unpack 9 (pack i) 0 0) else
  let z := node (i-2027)
  .forbid (z%16) ((z/16)%32) ((z/512)%2) (hint n ((z >>> 10)%4096)) (hint n (z >>> 22))
private def root (i : Nat) := scan 0xfac6906645382f2820160d0300 13 false (i%20+1) (page (209+i/20)) 0
def rows (p n : Nat) := (List.range n).map fun i => hint 41 (root (p+i))
end HP
def h5_3 := HP.rows 0 4
def h5_4 := HP.rows 4 2
def h5_5 := HP.rows 6 1
def h6_3 := HP.rows 7 6
def h6_4 := HP.rows 13 5
def h6_5 := HP.rows 18 2
def h6_6 := HP.rows 20 1
def h7_3 := HP.rows 21 9
def h7_4 := HP.rows 30 9
def h7_5 := HP.rows 39 5
def h7_6 := HP.rows 44 2
def h7_7 := HP.rows 46 1
def h8_4 := HP.rows 47 16
def h8_5 := HP.rows 63 10
def h8_6 := HP.rows 73 5
def h8_7 := HP.rows 78 2
def h8_8 := HP.rows 80 1
def h9_4 := HP.rows 81 25
def h9_5 := HP.rows 106 20
def h9_6 := HP.rows 126 11
def h9_7 := HP.rows 137 5
def h9_8 := HP.rows 142 2
def h10_5 := HP.rows 144 35
def h10_6 := HP.rows 179 24
def h10_7 := HP.rows 203 11
def h10_8 := HP.rows 214 5
def h11_5 := HP.rows 219 60
def h11_6 := HP.rows 279 46
def h11_7 := HP.rows 325 25
def h11_8 := HP.rows 350 11
def h12_6 := HP.rows 361 87
def h12_7 := HP.rows 448 51
def h12_8 := HP.rows 499 26
def h13_6 := HP.rows 525 152
def h13_7 := HP.rows 677 104
def h13_8 := HP.rows 781 55
def h14_7 := HP.rows 836 197
def h14_8 := HP.rows 1033 118
def h15_7 := HP.rows 1151 364
def h15_8 := HP.rows 1515 237
def h16_8 := HP.rows 1752 468
def h17_8 := HP.rows 2220 879
end OAI.CycleClique.Compact
end
/-! Elementary-segment deletion search. OpenAI math CycleClique, Apache-2.0,
3344da59991ed94f9ba711217b29c1d760badfa6. -/
namespace OAI.CycleClique.Edit
open OAI.CycleClique.Compact
def cnt (z : Nat) := ((((z - ((z >>> 1) &&& 1431655765)) &&& 858993459) + (((z - ((z >>> 1) &&& 1431655765)) >>> 2) &&& 858993459)))
def pc (z : Nat) := let a := cnt z; ((((a+(a>>>4)) &&& 252645135)*16843009) >>> 24) % 256
def segs (n B cuts : Nat) :=
  let (r,w) := (List.range n).foldl (fun (r,w) x =>
    let brk := !B.testBit x || cuts.testBit x
    let r := if brk && w != 0 then w::r else r
    let w := if brk then 0 else w
    (r, if B.testBit x then w ||| (1 <<< x) else w)) (([],0) : List Nat × Nat)
  if w==0 then r else w::r
def powers : List Nat → List Nat
  | [] => [0]
  | x::xs => let ps := powers xs; ps ++ ps.map (fun s => s ||| x)
def viable (B Q i j : Nat) (ss : List Nat) :=
  let p := (1 <<< i) ||| (1 <<< j)
  let interval := (1 <<< (j-i))-1
  (powers ss).filterMap fun s =>
    let R := B-s
    let U := R ||| (R <<< 1); let two := R &&& (R <<< 1)
    if two &&& p != 0 || ((R >>> i) &&& interval) == interval || ((U ^^^ two ^^^ p) &&& Q) != (U ^^^ two ^^^ p) then none else
    let V := pc (Q ||| U ||| p)
    some (R,V,V-pc R-1,pc (Q-(Q &&& (U ||| p))))
def sk (k t L e n B Q i j : Nat) (ds : List Nat) : List Row × List Need :=
  let p := (1 <<< i) ||| (1 <<< j)
  let vs := viable B Q i j (segs n B (Q ||| p))
  ds.foldr (fun d (rs,fs) =>
    let res := if d == 0 && Q.testBit i && Q.testBit j then none else vs.find? (fun (_,V,c,o) =>
      let A := V+d-t
      (A < k+1-t && (L<A || (A==L && t-c<e))) || (k+1-t ≤ A && A ≤ k+1-(t-o)))
    match res with
    | none => (rs,(i,j,d)::fs)
    | some (r,_) => ((i,j,d,r)::rs,fs)) ([],[])
def ins (x : Need) : List Need → List Need
  | [] => [x]
  | y::ys => if decide (x ≤ y) then x::y::ys else y::ins x ys
def groupNeeds (ns : List Need) : List (Nat × Nat × List Nat) := ns.map (fun (i,j,d) => (i,j,[d]))
def incid (P : List (Nat × Nat × Nat)) (x : Nat) : List (Nat × Nat) :=
  P.filterMap fun (a,b,k) => if a == x then some (b,k) else if b == x then some (a,k) else none
def numberE : Nat → List (Nat × Nat) → List (Nat × Nat × Nat)
  | _, [] => []
  | i, (a,b)::xs => (a,b,i) :: numberE (i+1) xs
def follow (A : Array (List (Nat × Nat))) (node : Nat → Bool) : Nat → Nat → Nat → Nat → Nat
  | 0,_,_,m => m
  | f+1,cur,prev,m => if node cur then m else
    match (A[cur]?.getD []).find? (fun (_,k) => k != prev) with
    | some (z,k) => follow A node f z k (m ||| (1 <<< k))
    | none => m
def combos : Nat → List Nat → List Nat
  | 0, _ => [0]
  | _+1, [] => []
  | r+1, x::xs => (combos r xs).map (· ||| x) ++ combos (r+1) xs
def chainFrom (A : Array (List (Nat × Nat))) (K : Nat) : Nat → Nat → Nat → List Nat
  | 0,cur,_ => [cur]
  | f+1,cur,prev => match (A[cur]?.getD []).find? (fun (_,k) => k != prev && K.testBit k) with
    | none => [cur]
    | some (z,k) => cur :: chainFrom A K f z k
def segSys (k t L e N : Nat) (q : List Nat) (F : List (Nat × Nat)) : Option (List (List Nat)) :=
  let qm := mask q
  let P := numberE 0 (F.filter fun (a,b) => !(qm.testBit a && qm.testBit b))
  let A := ((List.range N).map (incid P)).toArray
  let node := fun x => qm.testBit x || (A[x]?.getD []).length != 2
  let segs := ((List.range N).flatMap fun x => if node x then (A[x]?.getD []).map (fun (y,k) => follow A node N y k (1 <<< k)) else []).foldl (fun s m => if s.contains m then s else s ++ [m]) []
  let all := 2^P.length - 1
  let test := fun (del : Nat) =>
    let K := all ^^^ del
    let deg := fun x => ((A[x]?.getD []).filter fun (_,k) => K.testBit k).length
    if !(List.range N).all (fun x => deg x ≤ 2 && (deg x != 1 || qm.testBit x)) then none else
    let C := (q.filter fun s => deg s ≤ 1).filterMap fun s =>
      let c := chainFrom A K N s (2^60)
      if s ≤ c.getLast?.getD s then some c else none
    let need := ((List.range N).filter fun x => deg x != 0 || qm.testBit x).length
    if C.flatten.length == need && improves k t L e C then some C else none
  firstSome (fun r => firstSome test (combos r segs)) [0,1,2,3]
def direct2 (k t L e n : Nat) (q : List Nat) (E : List (Nat × Nat)) (i j d : Nat) : y2 :=
  match segSys k t L e (n+d) q (augmentedEdges n E i j d) with
  | some C => .system C
  | none => direct k t L e n q E i j d
def make (k t L e n₀ B Q : Nat) (q : List Nat) : Hint → Nat → List (Nat × Nat) → List Need → RCT
  | .forbid i j d R N,n,E,M => .split i j d (make k t L e n₀ B Q q R (n+d) (augmentedEdges n E i j d) M) (make k t L e n₀ B Q q N n E (key i j d :: M))
  | .packing os,n,E,M =>
    let pairs := groupNeeds ((needs n os).filter (fun x => !M.contains x))
    let (ws,fs) := pairs.foldr (fun (i,j,ds) (rs,fs) =>
      let (r,f) := if j < n then sk k t L e n B Q i j ds else ([],ds.map (i,j,·))
      (r++rs,f++fs)) (([],[]) : List Row × List Need)
    .group (ws.map (fun (i,j,d,R) => i+32*j+1024*d+65536*R)) (fs.foldr (fun (i,j,d) h => .split i j d (.direct (direct2 k t L e n q E i j d)) h) (.pack os))
def baseMask (n Q : Nat) (E : List (Nat × Nat)) := ((List.range n).filter (fun x => E.contains (x,x+1) && !(Q.testBit x && Q.testBit (x+1)))).foldl (fun m x => m ||| (1 <<< x)) 0
end OAI.CycleClique.Edit
namespace OAI.CycleClique.Edit
open OAI.CycleClique.Compact Lean
private def certExpr : y2 → Expr
  | .system c => mkApp (mkConst ``y2.system) (toExpr c)
  | .cycle c => mkApp (mkConst ``y2.cycle) (toExpr c)
  | _ => mkApp (mkConst ``y2.cycle) (toExpr ([] : List Nat))
private def treeExpr : RCT → Expr
  | .direct c => mkApp (mkConst ``RCT.direct) (certExpr c)
  | .pack os => mkApp (mkConst ``RCT.pack) (toExpr (show List (Nat × List Nat) from os))
  | .group w n => mkApp2 (mkConst ``RCT.group) (toExpr w) (treeExpr n)
  | .split i j d r n => mkApp5 (mkConst ``RCT.split) (toExpr i) (toExpr j) (toExpr d) (treeExpr r) (treeExpr n)
instance : ToExpr RCT := ⟨treeExpr,mkConst ``RCT⟩
def segTree (k t : Nat) (D : List (List Nat)) (h : Hint) : RCT :=
  let q := patternCliqueFrom 0 D; let Q := mask q; let n := patternOrder D
  let E := patternEdges D; let B := baseMask n Q E
  make k t (patternAmount D) (patternEdgeCount D) n B Q q h n E []
abbrev y6 := List (List Nat) × RCT
def y1 (k t : Nat) (x : y6) :=
  let D := x.1; let q := patternCliqueFrom 0 D; let Q := mask q; let n := patternOrder D
  let E := patternEdges D; let B := baseMask n Q E
  decide (SafeBase B (patternClique D) E n) && decide (∀ x ∈ patternClique D, x<n) && decide (Q<2^n) && decide (∀ x ∈ List.range n, Q.testBit x ↔ x ∈ patternClique D) && RC.check k t (patternAmount D) (patternEdgeCount D) B Q (patternClique D) x.2 n (y9 E) 0
theorem entry_sound {k t x} (H : y1 k t x) : y5 k t x.1 := by
  simp only [y1,Bool.and_eq_true,decide_eq_true_eq] at H
  exact RC.verify H.1.1.1.1 H.1.1.1.2 H.1.1.2 H.1.2 H.2
def entries (k t : Nat) (hs : List Hint) := ((y7 t (k-t) []).zip hs).map fun (D,h) => (D,segTree k t D h)
theorem ye {k t L e B Q q i j d R N n bits z}
    (hb : (decide (i<n) && decide (j<n)) = true)
    (hr : RC.check k t L e B Q q R (n+d) (bits ||| y9 (pathEdges (pathLabels n i j d))) z)
    (hn : RC.check k t L e B Q q N n bits (Rows.add z i j d)) :
    RC.check k t L e B Q q (.split i j d R N) n bits z := by
  simp only [RC.check, Bool.and_eq_true] at *; exact ⟨⟨hb,hr⟩,hn⟩
theorem yc {k t x xs} (a : y1 k t x) (b : xs.all (y1 k t)) : (x::xs).all (y1 k t) := by simp [a,b]
theorem yd {k t ds} {xs : List y6} (h : xs.map Prod.fst = ds) (g : xs.all (y1 k t)) : ∀ D ∈ ds, y5 k t D := by
  subst ds; intro D hD; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hD
  exact entry_sound (List.all_eq_true.mp g x hx)
end OAI.CycleClique.Edit
namespace OAI.CycleClique.Edit
open OAI.CycleClique.Compact
def yf (k t : Nat) (hs : List Hint) (i n : Nat) : List y6 :=
  ((((y7 t (k-t) []).zip hs).drop i).take n).map fun (D,h) => (D,segTree k t D h)
theorem y3 {k t} (a : List y6) {b : List y6} (ha : a.all (y1 k t)) (hb:b.all (y1 k t)) : (a++b).all (y1 k t) := by simp [ha,hb]
end OAI.CycleClique.Edit
namespace OAI.CycleClique
open OAI.CycleClique.Compact OAI.CycleClique.Edit
section
noncomputable def b234:List y6:=eval% yf 17 8 h17_8 0 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb234:b234.all (y1 17 8):=by decide +kernel
noncomputable def b235:List y6:=eval% yf 17 8 h17_8 16 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb235:b235.all (y1 17 8):=by decide +kernel
noncomputable def b236:List y6:=eval% yf 17 8 h17_8 32 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb236:b236.all (y1 17 8):=by decide +kernel
noncomputable def b237:List y6:=eval% yf 17 8 h17_8 48 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb237:b237.all (y1 17 8):=by decide +kernel
noncomputable def b238:List y6:=eval% yf 17 8 h17_8 64 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb238:b238.all (y1 17 8):=by decide +kernel
noncomputable def b239:List y6:=eval% yf 17 8 h17_8 80 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb239:b239.all (y1 17 8):=by decide +kernel
noncomputable def b240:List y6:=eval% yf 17 8 h17_8 96 2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb240:b240.all (y1 17 8):=by decide +kernel
noncomputable def b241:List y6:=eval% yf 17 8 h17_8 98 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb241:b241.all (y1 17 8) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b242:List y6:=eval% yf 17 8 h17_8 99 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb242:b242.all (y1 17 8):=by decide +kernel
noncomputable def b243:List y6:=eval% yf 17 8 h17_8 115 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb243:b243.all (y1 17 8):=by decide +kernel
noncomputable def b244:List y6:=eval% yf 17 8 h17_8 131 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb244:b244.all (y1 17 8):=by decide +kernel
noncomputable def b245:List y6:=eval% yf 17 8 h17_8 147 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb245:b245.all (y1 17 8):=by decide +kernel
noncomputable def b246:List y6:=eval% yf 17 8 h17_8 163 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb246:b246.all (y1 17 8):=by decide +kernel
noncomputable def b247:List y6:=eval% yf 17 8 h17_8 179 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb247:b247.all (y1 17 8):=by decide +kernel
noncomputable def b248:List y6:=eval% yf 17 8 h17_8 195 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb248:b248.all (y1 17 8):=by decide +kernel
noncomputable def b249:List y6:=eval% yf 17 8 h17_8 211 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb249:b249.all (y1 17 8):=by decide +kernel
noncomputable def b250:List y6:=eval% yf 17 8 h17_8 227 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb250:b250.all (y1 17 8):=by decide +kernel
noncomputable def b251:List y6:=eval% yf 17 8 h17_8 243 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb251:b251.all (y1 17 8):=by decide +kernel
noncomputable def b252:List y6:=eval% yf 17 8 h17_8 259 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb252:b252.all (y1 17 8):=by decide +kernel
noncomputable def b253:List y6:=eval% yf 17 8 h17_8 275 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb253:b253.all (y1 17 8):=by decide +kernel
noncomputable def b254:List y6:=eval% yf 17 8 h17_8 291 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb254:b254.all (y1 17 8):=by decide +kernel
noncomputable def b255:List y6:=eval% yf 17 8 h17_8 307 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb255:b255.all (y1 17 8):=by decide +kernel
noncomputable def b256:List y6:=eval% yf 17 8 h17_8 323 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb256:b256.all (y1 17 8):=by decide +kernel
noncomputable def b257:List y6:=eval% yf 17 8 h17_8 339 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb257:b257.all (y1 17 8):=by decide +kernel
noncomputable def b258:List y6:=eval% yf 17 8 h17_8 355 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb258:b258.all (y1 17 8):=by decide +kernel
noncomputable def b259:List y6:=eval% yf 17 8 h17_8 371 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb259:b259.all (y1 17 8):=by decide +kernel
noncomputable def b260:List y6:=eval% yf 17 8 h17_8 387 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb260:b260.all (y1 17 8):=by decide +kernel
noncomputable def b261:List y6:=eval% yf 17 8 h17_8 403 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb261:b261.all (y1 17 8):=by decide +kernel
noncomputable def b262:List y6:=eval% yf 17 8 h17_8 419 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb262:b262.all (y1 17 8):=by decide +kernel
noncomputable def b263:List y6:=eval% yf 17 8 h17_8 435 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb263:b263.all (y1 17 8):=by decide +kernel
noncomputable def b264:List y6:=eval% yf 17 8 h17_8 451 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb264:b264.all (y1 17 8):=by decide +kernel
noncomputable def b265:List y6:=eval% yf 17 8 h17_8 467 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb265:b265.all (y1 17 8):=by decide +kernel
noncomputable def b266:List y6:=eval% yf 17 8 h17_8 483 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb266:b266.all (y1 17 8):=by decide +kernel
noncomputable def b267:List y6:=eval% yf 17 8 h17_8 499 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb267:b267.all (y1 17 8):=by decide +kernel
noncomputable def b268:List y6:=eval% yf 17 8 h17_8 515 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb268:b268.all (y1 17 8):=by decide +kernel
noncomputable def b269:List y6:=eval% yf 17 8 h17_8 531 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb269:b269.all (y1 17 8):=by decide +kernel
noncomputable def b270:List y6:=eval% yf 17 8 h17_8 547 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb270:b270.all (y1 17 8):=by decide +kernel
noncomputable def b271:List y6:=eval% yf 17 8 h17_8 563 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb271:b271.all (y1 17 8):=by decide +kernel
noncomputable def b272:List y6:=eval% yf 17 8 h17_8 579 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb272:b272.all (y1 17 8):=by decide +kernel
noncomputable def b273:List y6:=eval% yf 17 8 h17_8 595 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb273:b273.all (y1 17 8):=by decide +kernel
noncomputable def b274:List y6:=eval% yf 17 8 h17_8 611 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb274:b274.all (y1 17 8):=by decide +kernel
noncomputable def b275:List y6:=eval% yf 17 8 h17_8 627 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb275:b275.all (y1 17 8):=by decide +kernel
noncomputable def b276:List y6:=eval% yf 17 8 h17_8 643 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb276:b276.all (y1 17 8):=by decide +kernel
noncomputable def b277:List y6:=eval% yf 17 8 h17_8 659 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb277:b277.all (y1 17 8):=by decide +kernel
noncomputable def b278:List y6:=eval% yf 17 8 h17_8 675 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb278:b278.all (y1 17 8):=by decide +kernel
noncomputable def b279:List y6:=eval% yf 17 8 h17_8 691 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb279:b279.all (y1 17 8):=by decide +kernel
noncomputable def b280:List y6:=eval% yf 17 8 h17_8 707 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb280:b280.all (y1 17 8):=by decide +kernel
noncomputable def b281:List y6:=eval% yf 17 8 h17_8 723 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb281:b281.all (y1 17 8):=by decide +kernel
noncomputable def b282:List y6:=eval% yf 17 8 h17_8 739 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb282:b282.all (y1 17 8):=by decide +kernel
noncomputable def b283:List y6:=eval% yf 17 8 h17_8 755 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb283:b283.all (y1 17 8):=by decide +kernel
noncomputable def b284:List y6:=eval% yf 17 8 h17_8 771 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb284:b284.all (y1 17 8):=by decide +kernel
noncomputable def b285:List y6:=eval% yf 17 8 h17_8 787 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb285:b285.all (y1 17 8):=by decide +kernel
noncomputable def b286:List y6:=eval% yf 17 8 h17_8 803 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb286:b286.all (y1 17 8):=by decide +kernel
noncomputable def b287:List y6:=eval% yf 17 8 h17_8 819 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb287:b287.all (y1 17 8):=by decide +kernel
noncomputable def b288:List y6:=eval% yf 17 8 h17_8 835 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb288:b288.all (y1 17 8):=by decide +kernel
noncomputable def b289:List y6:=eval% yf 17 8 h17_8 851 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb289:b289.all (y1 17 8):=by decide +kernel
noncomputable def b290:List y6:=eval% yf 17 8 h17_8 867 12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb290:b290.all (y1 17 8):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA17_8 : (b234++b235++b236++b237++b238++b239++b240++b241++b242++b243++b244++b245++b246++b247++b248++b249++b250++b251++b252++b253++b254++b255++b256++b257++b258++b259++b260++b261++b262++b263++b264++b265++b266++b267++b268++b269++b270++b271++b272++b273++b274++b275++b276++b277++b278++b279++b280++b281++b282++b283++b284++b285++b286++b287++b288++b289++b290).map Prod.fst = y7 8 (17-8) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A17_8 : ∀ D ∈ y7 8 (17-8) [], y5 17 8 D := yd (xs := b234++b235++b236++b237++b238++b239++b240++b241++b242++b243++b244++b245++b246++b247++b248++b249++b250++b251++b252++b253++b254++b255++b256++b257++b258++b259++b260++b261++b262++b263++b264++b265++b266++b267++b268++b269++b270++b271++b272++b273++b274++b275++b276++b277++b278++b279++b280++b281++b282++b283++b284++b285++b286++b287++b288++b289++b290) CA17_8 (by
  refine y3 b234 pb234 ?_
  refine y3 b235 pb235 ?_
  refine y3 b236 pb236 ?_
  refine y3 b237 pb237 ?_
  refine y3 b238 pb238 ?_
  refine y3 b239 pb239 ?_
  refine y3 b240 pb240 ?_
  refine y3 b241 pb241 ?_
  refine y3 b242 pb242 ?_
  refine y3 b243 pb243 ?_
  refine y3 b244 pb244 ?_
  refine y3 b245 pb245 ?_
  refine y3 b246 pb246 ?_
  refine y3 b247 pb247 ?_
  refine y3 b248 pb248 ?_
  refine y3 b249 pb249 ?_
  refine y3 b250 pb250 ?_
  refine y3 b251 pb251 ?_
  refine y3 b252 pb252 ?_
  refine y3 b253 pb253 ?_
  refine y3 b254 pb254 ?_
  refine y3 b255 pb255 ?_
  refine y3 b256 pb256 ?_
  refine y3 b257 pb257 ?_
  refine y3 b258 pb258 ?_
  refine y3 b259 pb259 ?_
  refine y3 b260 pb260 ?_
  refine y3 b261 pb261 ?_
  refine y3 b262 pb262 ?_
  refine y3 b263 pb263 ?_
  refine y3 b264 pb264 ?_
  refine y3 b265 pb265 ?_
  refine y3 b266 pb266 ?_
  refine y3 b267 pb267 ?_
  refine y3 b268 pb268 ?_
  refine y3 b269 pb269 ?_
  refine y3 b270 pb270 ?_
  refine y3 b271 pb271 ?_
  refine y3 b272 pb272 ?_
  refine y3 b273 pb273 ?_
  refine y3 b274 pb274 ?_
  refine y3 b275 pb275 ?_
  refine y3 b276 pb276 ?_
  refine y3 b277 pb277 ?_
  refine y3 b278 pb278 ?_
  refine y3 b279 pb279 ?_
  refine y3 b280 pb280 ?_
  refine y3 b281 pb281 ?_
  refine y3 b282 pb282 ?_
  refine y3 b283 pb283 ?_
  refine y3 b284 pb284 ?_
  refine y3 b285 pb285 ?_
  refine y3 b286 pb286 ?_
  refine y3 b287 pb287 ?_
  refine y3 b288 pb288 ?_
  refine y3 b289 pb289 ?_
  exact pb290)
noncomputable def b204:List y6:=eval% yf 16 8 h16_8 0 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb204:b204.all (y1 16 8):=by decide +kernel
noncomputable def b205:List y6:=eval% yf 16 8 h16_8 16 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb205:b205.all (y1 16 8):=by decide +kernel
noncomputable def b206:List y6:=eval% yf 16 8 h16_8 32 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb206:b206.all (y1 16 8):=by decide +kernel
noncomputable def b207:List y6:=eval% yf 16 8 h16_8 48 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb207:b207.all (y1 16 8):=by decide +kernel
noncomputable def b208:List y6:=eval% yf 16 8 h16_8 64 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb208:b208.all (y1 16 8):=by decide +kernel
noncomputable def b209:List y6:=eval% yf 16 8 h16_8 80 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb209:b209.all (y1 16 8):=by decide +kernel
noncomputable def b210:List y6:=eval% yf 16 8 h16_8 96 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb210:b210.all (y1 16 8):=by decide +kernel
noncomputable def b211:List y6:=eval% yf 16 8 h16_8 112 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb211:b211.all (y1 16 8):=by decide +kernel
noncomputable def b212:List y6:=eval% yf 16 8 h16_8 128 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb212:b212.all (y1 16 8):=by decide +kernel
noncomputable def b213:List y6:=eval% yf 16 8 h16_8 144 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb213:b213.all (y1 16 8):=by decide +kernel
noncomputable def b214:List y6:=eval% yf 16 8 h16_8 160 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb214:b214.all (y1 16 8):=by decide +kernel
noncomputable def b215:List y6:=eval% yf 16 8 h16_8 176 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb215:b215.all (y1 16 8):=by decide +kernel
noncomputable def b216:List y6:=eval% yf 16 8 h16_8 192 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb216:b216.all (y1 16 8):=by decide +kernel
noncomputable def b217:List y6:=eval% yf 16 8 h16_8 208 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb217:b217.all (y1 16 8):=by decide +kernel
noncomputable def b218:List y6:=eval% yf 16 8 h16_8 224 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb218:b218.all (y1 16 8):=by decide +kernel
noncomputable def b219:List y6:=eval% yf 16 8 h16_8 240 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb219:b219.all (y1 16 8):=by decide +kernel
noncomputable def b220:List y6:=eval% yf 16 8 h16_8 256 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb220:b220.all (y1 16 8):=by decide +kernel
noncomputable def b221:List y6:=eval% yf 16 8 h16_8 272 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb221:b221.all (y1 16 8):=by decide +kernel
noncomputable def b222:List y6:=eval% yf 16 8 h16_8 288 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb222:b222.all (y1 16 8):=by decide +kernel
noncomputable def b223:List y6:=eval% yf 16 8 h16_8 304 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb223:b223.all (y1 16 8):=by decide +kernel
noncomputable def b224:List y6:=eval% yf 16 8 h16_8 320 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb224:b224.all (y1 16 8):=by decide +kernel
noncomputable def b225:List y6:=eval% yf 16 8 h16_8 336 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb225:b225.all (y1 16 8):=by decide +kernel
noncomputable def b226:List y6:=eval% yf 16 8 h16_8 352 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb226:b226.all (y1 16 8):=by decide +kernel
noncomputable def b227:List y6:=eval% yf 16 8 h16_8 368 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb227:b227.all (y1 16 8):=by decide +kernel
noncomputable def b228:List y6:=eval% yf 16 8 h16_8 384 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb228:b228.all (y1 16 8):=by decide +kernel
noncomputable def b229:List y6:=eval% yf 16 8 h16_8 400 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb229:b229.all (y1 16 8):=by decide +kernel
noncomputable def b230:List y6:=eval% yf 16 8 h16_8 416 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb230:b230.all (y1 16 8):=by decide +kernel
noncomputable def b231:List y6:=eval% yf 16 8 h16_8 432 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb231:b231.all (y1 16 8):=by decide +kernel
noncomputable def b232:List y6:=eval% yf 16 8 h16_8 448 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb232:b232.all (y1 16 8):=by decide +kernel
noncomputable def b233:List y6:=eval% yf 16 8 h16_8 464 4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb233:b233.all (y1 16 8):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA16_8 : (b204++b205++b206++b207++b208++b209++b210++b211++b212++b213++b214++b215++b216++b217++b218++b219++b220++b221++b222++b223++b224++b225++b226++b227++b228++b229++b230++b231++b232++b233).map Prod.fst = y7 8 (16-8) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A16_8 : ∀ D ∈ y7 8 (16-8) [], y5 16 8 D := yd (xs := b204++b205++b206++b207++b208++b209++b210++b211++b212++b213++b214++b215++b216++b217++b218++b219++b220++b221++b222++b223++b224++b225++b226++b227++b228++b229++b230++b231++b232++b233) CA16_8 (by
  refine y3 b204 pb204 ?_
  refine y3 b205 pb205 ?_
  refine y3 b206 pb206 ?_
  refine y3 b207 pb207 ?_
  refine y3 b208 pb208 ?_
  refine y3 b209 pb209 ?_
  refine y3 b210 pb210 ?_
  refine y3 b211 pb211 ?_
  refine y3 b212 pb212 ?_
  refine y3 b213 pb213 ?_
  refine y3 b214 pb214 ?_
  refine y3 b215 pb215 ?_
  refine y3 b216 pb216 ?_
  refine y3 b217 pb217 ?_
  refine y3 b218 pb218 ?_
  refine y3 b219 pb219 ?_
  refine y3 b220 pb220 ?_
  refine y3 b221 pb221 ?_
  refine y3 b222 pb222 ?_
  refine y3 b223 pb223 ?_
  refine y3 b224 pb224 ?_
  refine y3 b225 pb225 ?_
  refine y3 b226 pb226 ?_
  refine y3 b227 pb227 ?_
  refine y3 b228 pb228 ?_
  refine y3 b229 pb229 ?_
  refine y3 b230 pb230 ?_
  refine y3 b231 pb231 ?_
  refine y3 b232 pb232 ?_
  exact pb233)
noncomputable def b189:List y6:=eval% yf 15 8 h15_8 0 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb189:b189.all (y1 15 8):=by decide +kernel
noncomputable def b190:List y6:=eval% yf 15 8 h15_8 16 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb190:b190.all (y1 15 8):=by decide +kernel
noncomputable def b191:List y6:=eval% yf 15 8 h15_8 32 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb191:b191.all (y1 15 8):=by decide +kernel
noncomputable def b192:List y6:=eval% yf 15 8 h15_8 48 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb192:b192.all (y1 15 8):=by decide +kernel
noncomputable def b193:List y6:=eval% yf 15 8 h15_8 64 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb193:b193.all (y1 15 8):=by decide +kernel
noncomputable def b194:List y6:=eval% yf 15 8 h15_8 80 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb194:b194.all (y1 15 8):=by decide +kernel
noncomputable def b195:List y6:=eval% yf 15 8 h15_8 96 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb195:b195.all (y1 15 8):=by decide +kernel
noncomputable def b196:List y6:=eval% yf 15 8 h15_8 112 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb196:b196.all (y1 15 8):=by decide +kernel
noncomputable def b197:List y6:=eval% yf 15 8 h15_8 128 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb197:b197.all (y1 15 8):=by decide +kernel
noncomputable def b198:List y6:=eval% yf 15 8 h15_8 144 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb198:b198.all (y1 15 8):=by decide +kernel
noncomputable def b199:List y6:=eval% yf 15 8 h15_8 160 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb199:b199.all (y1 15 8):=by decide +kernel
noncomputable def b200:List y6:=eval% yf 15 8 h15_8 176 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb200:b200.all (y1 15 8):=by decide +kernel
noncomputable def b201:List y6:=eval% yf 15 8 h15_8 192 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb201:b201.all (y1 15 8):=by decide +kernel
noncomputable def b202:List y6:=eval% yf 15 8 h15_8 208 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb202:b202.all (y1 15 8):=by decide +kernel
noncomputable def b203:List y6:=eval% yf 15 8 h15_8 224 13
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb203:b203.all (y1 15 8):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA15_8 : (b189++b190++b191++b192++b193++b194++b195++b196++b197++b198++b199++b200++b201++b202++b203).map Prod.fst = y7 8 (15-8) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A15_8 : ∀ D ∈ y7 8 (15-8) [], y5 15 8 D := yd (xs := b189++b190++b191++b192++b193++b194++b195++b196++b197++b198++b199++b200++b201++b202++b203) CA15_8 (by
  refine y3 b189 pb189 ?_
  refine y3 b190 pb190 ?_
  refine y3 b191 pb191 ?_
  refine y3 b192 pb192 ?_
  refine y3 b193 pb193 ?_
  refine y3 b194 pb194 ?_
  refine y3 b195 pb195 ?_
  refine y3 b196 pb196 ?_
  refine y3 b197 pb197 ?_
  refine y3 b198 pb198 ?_
  refine y3 b199 pb199 ?_
  refine y3 b200 pb200 ?_
  refine y3 b201 pb201 ?_
  refine y3 b202 pb202 ?_
  exact pb203)
noncomputable def b160:List y6:=eval% yf 15 7 h15_7 0 8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb160:b160.all (y1 15 7):=by decide +kernel
set_option maxRecDepth 100000 in
noncomputable def b161:List y6:=eval% yf 15 7 h15_7 8 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb161:b161.all (y1 15 7) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b162:List y6:=eval% yf 15 7 h15_7 9 15
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb162:b162.all (y1 15 7):=by decide +kernel
noncomputable def b163:List y6:=eval% yf 15 7 h15_7 24 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb163:b163.all (y1 15 7) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b164:List y6:=eval% yf 15 7 h15_7 25 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb164:b164.all (y1 15 7):=by decide +kernel
noncomputable def b165:List y6:=eval% yf 15 7 h15_7 41 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb165:b165.all (y1 15 7):=by decide +kernel
noncomputable def b166:List y6:=eval% yf 15 7 h15_7 57 13
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb166:b166.all (y1 15 7):=by decide +kernel
noncomputable def b167:List y6:=eval% yf 15 7 h15_7 70 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb167:b167.all (y1 15 7) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b168:List y6:=eval% yf 15 7 h15_7 71 3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb168:b168.all (y1 15 7):=by decide +kernel
set_option maxRecDepth 100000 in
noncomputable def b169:List y6:=eval% yf 15 7 h15_7 74 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb169:b169.all (y1 15 7) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b170:List y6:=eval% yf 15 7 h15_7 75 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb170:b170.all (y1 15 7):=by decide +kernel
noncomputable def b171:List y6:=eval% yf 15 7 h15_7 91 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb171:b171.all (y1 15 7):=by decide +kernel
noncomputable def b172:List y6:=eval% yf 15 7 h15_7 107 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb172:b172.all (y1 15 7):=by decide +kernel
noncomputable def b173:List y6:=eval% yf 15 7 h15_7 123 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb173:b173.all (y1 15 7):=by decide +kernel
noncomputable def b174:List y6:=eval% yf 15 7 h15_7 139 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb174:b174.all (y1 15 7):=by decide +kernel
noncomputable def b175:List y6:=eval% yf 15 7 h15_7 155 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb175:b175.all (y1 15 7):=by decide +kernel
noncomputable def b176:List y6:=eval% yf 15 7 h15_7 171 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb176:b176.all (y1 15 7):=by decide +kernel
noncomputable def b177:List y6:=eval% yf 15 7 h15_7 187 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb177:b177.all (y1 15 7):=by decide +kernel
noncomputable def b178:List y6:=eval% yf 15 7 h15_7 203 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb178:b178.all (y1 15 7):=by decide +kernel
noncomputable def b179:List y6:=eval% yf 15 7 h15_7 219 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb179:b179.all (y1 15 7):=by decide +kernel
noncomputable def b180:List y6:=eval% yf 15 7 h15_7 235 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb180:b180.all (y1 15 7):=by decide +kernel
noncomputable def b181:List y6:=eval% yf 15 7 h15_7 251 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb181:b181.all (y1 15 7):=by decide +kernel
noncomputable def b182:List y6:=eval% yf 15 7 h15_7 267 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb182:b182.all (y1 15 7):=by decide +kernel
noncomputable def b183:List y6:=eval% yf 15 7 h15_7 283 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb183:b183.all (y1 15 7):=by decide +kernel
noncomputable def b184:List y6:=eval% yf 15 7 h15_7 299 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb184:b184.all (y1 15 7):=by decide +kernel
noncomputable def b185:List y6:=eval% yf 15 7 h15_7 315 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb185:b185.all (y1 15 7):=by decide +kernel
noncomputable def b186:List y6:=eval% yf 15 7 h15_7 331 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb186:b186.all (y1 15 7):=by decide +kernel
noncomputable def b187:List y6:=eval% yf 15 7 h15_7 347 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb187:b187.all (y1 15 7):=by decide +kernel
noncomputable def b188:List y6:=eval% yf 15 7 h15_7 363 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb188:b188.all (y1 15 7):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA15_7 : (b160++b161++b162++b163++b164++b165++b166++b167++b168++b169++b170++b171++b172++b173++b174++b175++b176++b177++b178++b179++b180++b181++b182++b183++b184++b185++b186++b187++b188).map Prod.fst = y7 7 (15-7) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A15_7 : ∀ D ∈ y7 7 (15-7) [], y5 15 7 D := yd (xs := b160++b161++b162++b163++b164++b165++b166++b167++b168++b169++b170++b171++b172++b173++b174++b175++b176++b177++b178++b179++b180++b181++b182++b183++b184++b185++b186++b187++b188) CA15_7 (by
  refine y3 b160 pb160 ?_
  refine y3 b161 pb161 ?_
  refine y3 b162 pb162 ?_
  refine y3 b163 pb163 ?_
  refine y3 b164 pb164 ?_
  refine y3 b165 pb165 ?_
  refine y3 b166 pb166 ?_
  refine y3 b167 pb167 ?_
  refine y3 b168 pb168 ?_
  refine y3 b169 pb169 ?_
  refine y3 b170 pb170 ?_
  refine y3 b171 pb171 ?_
  refine y3 b172 pb172 ?_
  refine y3 b173 pb173 ?_
  refine y3 b174 pb174 ?_
  refine y3 b175 pb175 ?_
  refine y3 b176 pb176 ?_
  refine y3 b177 pb177 ?_
  refine y3 b178 pb178 ?_
  refine y3 b179 pb179 ?_
  refine y3 b180 pb180 ?_
  refine y3 b181 pb181 ?_
  refine y3 b182 pb182 ?_
  refine y3 b183 pb183 ?_
  refine y3 b184 pb184 ?_
  refine y3 b185 pb185 ?_
  refine y3 b186 pb186 ?_
  refine y3 b187 pb187 ?_
  exact pb188)
noncomputable def b152:List y6:=eval% yf 14 8 h14_8 0 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb152:b152.all (y1 14 8):=by decide +kernel
noncomputable def b153:List y6:=eval% yf 14 8 h14_8 16 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb153:b153.all (y1 14 8):=by decide +kernel
noncomputable def b154:List y6:=eval% yf 14 8 h14_8 32 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb154:b154.all (y1 14 8):=by decide +kernel
noncomputable def b155:List y6:=eval% yf 14 8 h14_8 48 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb155:b155.all (y1 14 8):=by decide +kernel
noncomputable def b156:List y6:=eval% yf 14 8 h14_8 64 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb156:b156.all (y1 14 8):=by decide +kernel
noncomputable def b157:List y6:=eval% yf 14 8 h14_8 80 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb157:b157.all (y1 14 8):=by decide +kernel
noncomputable def b158:List y6:=eval% yf 14 8 h14_8 96 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb158:b158.all (y1 14 8):=by decide +kernel
noncomputable def b159:List y6:=eval% yf 14 8 h14_8 112 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb159:b159.all (y1 14 8):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA14_8 : (b152++b153++b154++b155++b156++b157++b158++b159).map Prod.fst = y7 8 (14-8) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A14_8 : ∀ D ∈ y7 8 (14-8) [], y5 14 8 D := yd (xs := b152++b153++b154++b155++b156++b157++b158++b159) CA14_8 (by
  refine y3 b152 pb152 ?_
  refine y3 b153 pb153 ?_
  refine y3 b154 pb154 ?_
  refine y3 b155 pb155 ?_
  refine y3 b156 pb156 ?_
  refine y3 b157 pb157 ?_
  refine y3 b158 pb158 ?_
  exact pb159)
noncomputable def b139:List y6:=eval% yf 14 7 h14_7 0 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb139:b139.all (y1 14 7):=by decide +kernel
noncomputable def b140:List y6:=eval% yf 14 7 h14_7 16 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb140:b140.all (y1 14 7):=by decide +kernel
noncomputable def b141:List y6:=eval% yf 14 7 h14_7 32 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb141:b141.all (y1 14 7):=by decide +kernel
noncomputable def b142:List y6:=eval% yf 14 7 h14_7 48 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb142:b142.all (y1 14 7):=by decide +kernel
noncomputable def b143:List y6:=eval% yf 14 7 h14_7 64 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb143:b143.all (y1 14 7):=by decide +kernel
noncomputable def b144:List y6:=eval% yf 14 7 h14_7 80 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb144:b144.all (y1 14 7):=by decide +kernel
noncomputable def b145:List y6:=eval% yf 14 7 h14_7 96 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb145:b145.all (y1 14 7):=by decide +kernel
noncomputable def b146:List y6:=eval% yf 14 7 h14_7 112 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb146:b146.all (y1 14 7):=by decide +kernel
noncomputable def b147:List y6:=eval% yf 14 7 h14_7 128 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb147:b147.all (y1 14 7):=by decide +kernel
noncomputable def b148:List y6:=eval% yf 14 7 h14_7 144 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb148:b148.all (y1 14 7):=by decide +kernel
noncomputable def b149:List y6:=eval% yf 14 7 h14_7 160 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb149:b149.all (y1 14 7):=by decide +kernel
noncomputable def b150:List y6:=eval% yf 14 7 h14_7 176 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb150:b150.all (y1 14 7):=by decide +kernel
noncomputable def b151:List y6:=eval% yf 14 7 h14_7 192 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb151:b151.all (y1 14 7):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA14_7 : (b139++b140++b141++b142++b143++b144++b145++b146++b147++b148++b149++b150++b151).map Prod.fst = y7 7 (14-7) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A14_7 : ∀ D ∈ y7 7 (14-7) [], y5 14 7 D := yd (xs := b139++b140++b141++b142++b143++b144++b145++b146++b147++b148++b149++b150++b151) CA14_7 (by
  refine y3 b139 pb139 ?_
  refine y3 b140 pb140 ?_
  refine y3 b141 pb141 ?_
  refine y3 b142 pb142 ?_
  refine y3 b143 pb143 ?_
  refine y3 b144 pb144 ?_
  refine y3 b145 pb145 ?_
  refine y3 b146 pb146 ?_
  refine y3 b147 pb147 ?_
  refine y3 b148 pb148 ?_
  refine y3 b149 pb149 ?_
  refine y3 b150 pb150 ?_
  exact pb151)
noncomputable def b135:List y6:=eval% yf 13 8 h13_8 0 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb135:b135.all (y1 13 8):=by decide +kernel
noncomputable def b136:List y6:=eval% yf 13 8 h13_8 16 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb136:b136.all (y1 13 8):=by decide +kernel
noncomputable def b137:List y6:=eval% yf 13 8 h13_8 32 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb137:b137.all (y1 13 8):=by decide +kernel
noncomputable def b138:List y6:=eval% yf 13 8 h13_8 48 7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb138:b138.all (y1 13 8):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA13_8 : (b135++b136++b137++b138).map Prod.fst = y7 8 (13-8) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A13_8 : ∀ D ∈ y7 8 (13-8) [], y5 13 8 D := yd (xs := b135++b136++b137++b138) CA13_8 (by
  refine y3 b135 pb135 ?_
  refine y3 b136 pb136 ?_
  refine y3 b137 pb137 ?_
  exact pb138)
noncomputable def b128:List y6:=eval% yf 13 7 h13_7 0 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb128:b128.all (y1 13 7):=by decide +kernel
noncomputable def b129:List y6:=eval% yf 13 7 h13_7 16 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb129:b129.all (y1 13 7):=by decide +kernel
noncomputable def b130:List y6:=eval% yf 13 7 h13_7 32 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb130:b130.all (y1 13 7):=by decide +kernel
noncomputable def b131:List y6:=eval% yf 13 7 h13_7 48 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb131:b131.all (y1 13 7):=by decide +kernel
noncomputable def b132:List y6:=eval% yf 13 7 h13_7 64 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb132:b132.all (y1 13 7):=by decide +kernel
noncomputable def b133:List y6:=eval% yf 13 7 h13_7 80 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb133:b133.all (y1 13 7):=by decide +kernel
noncomputable def b134:List y6:=eval% yf 13 7 h13_7 96 8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb134:b134.all (y1 13 7):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA13_7 : (b128++b129++b130++b131++b132++b133++b134).map Prod.fst = y7 7 (13-7) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A13_7 : ∀ D ∈ y7 7 (13-7) [], y5 13 7 D := yd (xs := b128++b129++b130++b131++b132++b133++b134) CA13_7 (by
  refine y3 b128 pb128 ?_
  refine y3 b129 pb129 ?_
  refine y3 b130 pb130 ?_
  refine y3 b131 pb131 ?_
  refine y3 b132 pb132 ?_
  refine y3 b133 pb133 ?_
  exact pb134)
noncomputable def b108:List y6:=eval% yf 13 6 h13_6 0 7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb108:b108.all (y1 13 6):=by decide +kernel
noncomputable def b109:List y6:=eval% yf 13 6 h13_6 7 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb109:b109.all (y1 13 6) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b110:List y6:=eval% yf 13 6 h13_6 8 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb110:b110.all (y1 13 6):=by decide +kernel
noncomputable def b111:List y6:=eval% yf 13 6 h13_6 13 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb111:b111.all (y1 13 6) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b112:List y6:=eval% yf 13 6 h13_6 14 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb112:b112.all (y1 13 6):=by decide +kernel
noncomputable def b113:List y6:=eval% yf 13 6 h13_6 19 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb113:b113.all (y1 13 6) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b114:List y6:=eval% yf 13 6 h13_6 20 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb114:b114.all (y1 13 6):=by decide +kernel
noncomputable def b115:List y6:=eval% yf 13 6 h13_6 25 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb115:b115.all (y1 13 6) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b116:List y6:=eval% yf 13 6 h13_6 26 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb116:b116.all (y1 13 6):=by decide +kernel
noncomputable def b117:List y6:=eval% yf 13 6 h13_6 42 2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb117:b117.all (y1 13 6):=by decide +kernel
noncomputable def b118:List y6:=eval% yf 13 6 h13_6 44 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb118:b118.all (y1 13 6) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b119:List y6:=eval% yf 13 6 h13_6 45 7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb119:b119.all (y1 13 6):=by decide +kernel
noncomputable def b120:List y6:=eval% yf 13 6 h13_6 52 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb120:b120.all (y1 13 6) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b121:List y6:=eval% yf 13 6 h13_6 53 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb121:b121.all (y1 13 6):=by decide +kernel
noncomputable def b122:List y6:=eval% yf 13 6 h13_6 69 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb122:b122.all (y1 13 6):=by decide +kernel
noncomputable def b123:List y6:=eval% yf 13 6 h13_6 85 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb123:b123.all (y1 13 6):=by decide +kernel
noncomputable def b124:List y6:=eval% yf 13 6 h13_6 101 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb124:b124.all (y1 13 6):=by decide +kernel
noncomputable def b125:List y6:=eval% yf 13 6 h13_6 117 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb125:b125.all (y1 13 6):=by decide +kernel
noncomputable def b126:List y6:=eval% yf 13 6 h13_6 133 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb126:b126.all (y1 13 6):=by decide +kernel
noncomputable def b127:List y6:=eval% yf 13 6 h13_6 149 3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb127:b127.all (y1 13 6):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA13_6 : (b108++b109++b110++b111++b112++b113++b114++b115++b116++b117++b118++b119++b120++b121++b122++b123++b124++b125++b126++b127).map Prod.fst = y7 6 (13-6) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A13_6 : ∀ D ∈ y7 6 (13-6) [], y5 13 6 D := yd (xs := b108++b109++b110++b111++b112++b113++b114++b115++b116++b117++b118++b119++b120++b121++b122++b123++b124++b125++b126++b127) CA13_6 (by
  refine y3 b108 pb108 ?_
  refine y3 b109 pb109 ?_
  refine y3 b110 pb110 ?_
  refine y3 b111 pb111 ?_
  refine y3 b112 pb112 ?_
  refine y3 b113 pb113 ?_
  refine y3 b114 pb114 ?_
  refine y3 b115 pb115 ?_
  refine y3 b116 pb116 ?_
  refine y3 b117 pb117 ?_
  refine y3 b118 pb118 ?_
  refine y3 b119 pb119 ?_
  refine y3 b120 pb120 ?_
  refine y3 b121 pb121 ?_
  refine y3 b122 pb122 ?_
  refine y3 b123 pb123 ?_
  refine y3 b124 pb124 ?_
  refine y3 b125 pb125 ?_
  refine y3 b126 pb126 ?_
  exact pb127)
noncomputable def b106:List y6:=eval% yf 12 8 h12_8 0 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb106:b106.all (y1 12 8):=by decide +kernel
noncomputable def b107:List y6:=eval% yf 12 8 h12_8 16 10
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb107:b107.all (y1 12 8):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA12_8 : (b106++b107).map Prod.fst = y7 8 (12-8) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A12_8 : ∀ D ∈ y7 8 (12-8) [], y5 12 8 D := yd (xs := b106++b107) CA12_8 (by
  refine y3 b106 pb106 ?_
  exact pb107)
noncomputable def b102:List y6:=eval% yf 12 7 h12_7 0 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb102:b102.all (y1 12 7):=by decide +kernel
noncomputable def b103:List y6:=eval% yf 12 7 h12_7 16 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb103:b103.all (y1 12 7):=by decide +kernel
noncomputable def b104:List y6:=eval% yf 12 7 h12_7 32 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb104:b104.all (y1 12 7):=by decide +kernel
noncomputable def b105:List y6:=eval% yf 12 7 h12_7 48 3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb105:b105.all (y1 12 7):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA12_7 : (b102++b103++b104++b105).map Prod.fst = y7 7 (12-7) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A12_7 : ∀ D ∈ y7 7 (12-7) [], y5 12 7 D := yd (xs := b102++b103++b104++b105) CA12_7 (by
  refine y3 b102 pb102 ?_
  refine y3 b103 pb103 ?_
  refine y3 b104 pb104 ?_
  exact pb105)
noncomputable def b91:List y6:=eval% yf 12 6 h12_6 0 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb91:b91.all (y1 12 6):=by decide +kernel
noncomputable def b92:List y6:=eval% yf 12 6 h12_6 6 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb92:b92.all (y1 12 6) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b93:List y6:=eval% yf 12 6 h12_6 7 8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb93:b93.all (y1 12 6):=by decide +kernel
noncomputable def b94:List y6:=eval% yf 12 6 h12_6 15 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb94:b94.all (y1 12 6) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b95:List y6:=eval% yf 12 6 h12_6 16 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb95:b95.all (y1 12 6):=by decide +kernel
noncomputable def b96:List y6:=eval% yf 12 6 h12_6 32 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb96:b96.all (y1 12 6):=by decide +kernel
noncomputable def b97:List y6:=eval% yf 12 6 h12_6 37 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb97:b97.all (y1 12 6) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b98:List y6:=eval% yf 12 6 h12_6 38 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb98:b98.all (y1 12 6):=by decide +kernel
noncomputable def b99:List y6:=eval% yf 12 6 h12_6 54 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb99:b99.all (y1 12 6):=by decide +kernel
noncomputable def b100:List y6:=eval% yf 12 6 h12_6 70 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb100:b100.all (y1 12 6):=by decide +kernel
noncomputable def b101:List y6:=eval% yf 12 6 h12_6 86 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb101:b101.all (y1 12 6):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA12_6 : (b91++b92++b93++b94++b95++b96++b97++b98++b99++b100++b101).map Prod.fst = y7 6 (12-6) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A12_6 : ∀ D ∈ y7 6 (12-6) [], y5 12 6 D := yd (xs := b91++b92++b93++b94++b95++b96++b97++b98++b99++b100++b101) CA12_6 (by
  refine y3 b91 pb91 ?_
  refine y3 b92 pb92 ?_
  refine y3 b93 pb93 ?_
  refine y3 b94 pb94 ?_
  refine y3 b95 pb95 ?_
  refine y3 b96 pb96 ?_
  refine y3 b97 pb97 ?_
  refine y3 b98 pb98 ?_
  refine y3 b99 pb99 ?_
  refine y3 b100 pb100 ?_
  exact pb101)
noncomputable def b90:List y6:=eval% yf 11 8 h11_8 0 11
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb90:b90.all (y1 11 8):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA11_8 : (b90).map Prod.fst = y7 8 (11-8) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A11_8 : ∀ D ∈ y7 8 (11-8) [], y5 11 8 D := yd (xs := b90) CA11_8 (by
  exact pb90)
noncomputable def b88:List y6:=eval% yf 11 7 h11_7 0 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb88:b88.all (y1 11 7):=by decide +kernel
noncomputable def b89:List y6:=eval% yf 11 7 h11_7 16 9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb89:b89.all (y1 11 7):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA11_7 : (b88++b89).map Prod.fst = y7 7 (11-7) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A11_7 : ∀ D ∈ y7 7 (11-7) [], y5 11 7 D := yd (xs := b88++b89) CA11_7 (by
  refine y3 b88 pb88 ?_
  exact pb89)
noncomputable def b83:List y6:=eval% yf 11 6 h11_6 0 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb83:b83.all (y1 11 6):=by decide +kernel
noncomputable def b84:List y6:=eval% yf 11 6 h11_6 5 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb84:b84.all (y1 11 6) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b85:List y6:=eval% yf 11 6 h11_6 6 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb85:b85.all (y1 11 6):=by decide +kernel
noncomputable def b86:List y6:=eval% yf 11 6 h11_6 22 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb86:b86.all (y1 11 6):=by decide +kernel
noncomputable def b87:List y6:=eval% yf 11 6 h11_6 38 8
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb87:b87.all (y1 11 6):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA11_6 : (b83++b84++b85++b86++b87).map Prod.fst = y7 6 (11-6) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A11_6 : ∀ D ∈ y7 6 (11-6) [], y5 11 6 D := yd (xs := b83++b84++b85++b86++b87) CA11_6 (by
  refine y3 b83 pb83 ?_
  refine y3 b84 pb84 ?_
  refine y3 b85 pb85 ?_
  refine y3 b86 pb86 ?_
  exact pb87)
noncomputable def b68:List y6:=eval% yf 11 5 h11_5 0 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb68:b68.all (y1 11 5):=by decide +kernel
noncomputable def b69:List y6:=eval% yf 11 5 h11_5 5 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb69:b69.all (y1 11 5) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b70:List y6:=eval% yf 11 5 h11_5 6 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb70:b70.all (y1 11 5) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b71:List y6:=eval% yf 11 5 h11_5 7 4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb71:b71.all (y1 11 5):=by decide +kernel
noncomputable def b72:List y6:=eval% yf 11 5 h11_5 11 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb72:b72.all (y1 11 5) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b73:List y6:=eval% yf 11 5 h11_5 12 3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb73:b73.all (y1 11 5):=by decide +kernel
noncomputable def b74:List y6:=eval% yf 11 5 h11_5 15 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb74:b74.all (y1 11 5) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b75:List y6:=eval% yf 11 5 h11_5 16 4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb75:b75.all (y1 11 5):=by decide +kernel
noncomputable def b76:List y6:=eval% yf 11 5 h11_5 20 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb76:b76.all (y1 11 5) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b77:List y6:=eval% yf 11 5 h11_5 21 12
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb77:b77.all (y1 11 5):=by decide +kernel
noncomputable def b78:List y6:=eval% yf 11 5 h11_5 33 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb78:b78.all (y1 11 5) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b79:List y6:=eval% yf 11 5 h11_5 34 3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb79:b79.all (y1 11 5):=by decide +kernel
noncomputable def b80:List y6:=eval% yf 11 5 h11_5 37 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb80:b80.all (y1 11 5) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b81:List y6:=eval% yf 11 5 h11_5 38 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb81:b81.all (y1 11 5):=by decide +kernel
noncomputable def b82:List y6:=eval% yf 11 5 h11_5 54 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb82:b82.all (y1 11 5):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA11_5 : (b68++b69++b70++b71++b72++b73++b74++b75++b76++b77++b78++b79++b80++b81++b82).map Prod.fst = y7 5 (11-5) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A11_5 : ∀ D ∈ y7 5 (11-5) [], y5 11 5 D := yd (xs := b68++b69++b70++b71++b72++b73++b74++b75++b76++b77++b78++b79++b80++b81++b82) CA11_5 (by
  refine y3 b68 pb68 ?_
  refine y3 b69 pb69 ?_
  refine y3 b70 pb70 ?_
  refine y3 b71 pb71 ?_
  refine y3 b72 pb72 ?_
  refine y3 b73 pb73 ?_
  refine y3 b74 pb74 ?_
  refine y3 b75 pb75 ?_
  refine y3 b76 pb76 ?_
  refine y3 b77 pb77 ?_
  refine y3 b78 pb78 ?_
  refine y3 b79 pb79 ?_
  refine y3 b80 pb80 ?_
  refine y3 b81 pb81 ?_
  exact pb82)
noncomputable def b67:List y6:=eval% yf 10 8 h10_8 0 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb67:b67.all (y1 10 8):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA10_8 : (b67).map Prod.fst = y7 8 (10-8) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A10_8 : ∀ D ∈ y7 8 (10-8) [], y5 10 8 D := yd (xs := b67) CA10_8 (by
  exact pb67)
noncomputable def b66:List y6:=eval% yf 10 7 h10_7 0 11
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb66:b66.all (y1 10 7):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA10_7 : (b66).map Prod.fst = y7 7 (10-7) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A10_7 : ∀ D ∈ y7 7 (10-7) [], y5 10 7 D := yd (xs := b66) CA10_7 (by
  exact pb66)
noncomputable def b62:List y6:=eval% yf 10 6 h10_6 0 4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb62:b62.all (y1 10 6):=by decide +kernel
noncomputable def b63:List y6:=eval% yf 10 6 h10_6 4 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb63:b63.all (y1 10 6) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b64:List y6:=eval% yf 10 6 h10_6 5 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb64:b64.all (y1 10 6):=by decide +kernel
noncomputable def b65:List y6:=eval% yf 10 6 h10_6 21 3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb65:b65.all (y1 10 6):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA10_6 : (b62++b63++b64++b65).map Prod.fst = y7 6 (10-6) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A10_6 : ∀ D ∈ y7 6 (10-6) [], y5 10 6 D := yd (xs := b62++b63++b64++b65) CA10_6 (by
  refine y3 b62 pb62 ?_
  refine y3 b63 pb63 ?_
  refine y3 b64 pb64 ?_
  exact pb65)
noncomputable def b55:List y6:=eval% yf 10 5 h10_5 0 4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb55:b55.all (y1 10 5):=by decide +kernel
noncomputable def b56:List y6:=eval% yf 10 5 h10_5 4 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb56:b56.all (y1 10 5) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b57:List y6:=eval% yf 10 5 h10_5 5 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb57:b57.all (y1 10 5) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b58:List y6:=eval% yf 10 5 h10_5 6 9
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb58:b58.all (y1 10 5):=by decide +kernel
noncomputable def b59:List y6:=eval% yf 10 5 h10_5 15 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb59:b59.all (y1 10 5) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b60:List y6:=eval% yf 10 5 h10_5 16 16
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb60:b60.all (y1 10 5):=by decide +kernel
noncomputable def b61:List y6:=eval% yf 10 5 h10_5 32 3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb61:b61.all (y1 10 5):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA10_5 : (b55++b56++b57++b58++b59++b60++b61).map Prod.fst = y7 5 (10-5) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A10_5 : ∀ D ∈ y7 5 (10-5) [], y5 10 5 D := yd (xs := b55++b56++b57++b58++b59++b60++b61) CA10_5 (by
  refine y3 b55 pb55 ?_
  refine y3 b56 pb56 ?_
  refine y3 b57 pb57 ?_
  refine y3 b58 pb58 ?_
  refine y3 b59 pb59 ?_
  refine y3 b60 pb60 ?_
  exact pb61)
noncomputable def b54:List y6:=eval% yf 9 8 h9_8 0 2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb54:b54.all (y1 9 8):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA9_8 : (b54).map Prod.fst = y7 8 (9-8) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A9_8 : ∀ D ∈ y7 8 (9-8) [], y5 9 8 D := yd (xs := b54) CA9_8 (by
  exact pb54)
noncomputable def b53:List y6:=eval% yf 9 7 h9_7 0 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb53:b53.all (y1 9 7):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA9_7 : (b53).map Prod.fst = y7 7 (9-7) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A9_7 : ∀ D ∈ y7 7 (9-7) [], y5 9 7 D := yd (xs := b53) CA9_7 (by
  exact pb53)
noncomputable def b52:List y6:=eval% yf 9 6 h9_6 0 11
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb52:b52.all (y1 9 6):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA9_6 : (b52).map Prod.fst = y7 6 (9-6) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A9_6 : ∀ D ∈ y7 6 (9-6) [], y5 9 6 D := yd (xs := b52) CA9_6 (by
  exact pb52)
noncomputable def b49:List y6:=eval% yf 9 5 h9_5 0 4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb49:b49.all (y1 9 5):=by decide +kernel
noncomputable def b50:List y6:=eval% yf 9 5 h9_5 4 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb50:b50.all (y1 9 5) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b51:List y6:=eval% yf 9 5 h9_5 5 15
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb51:b51.all (y1 9 5):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA9_5 : (b49++b50++b51).map Prod.fst = y7 5 (9-5) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A9_5 : ∀ D ∈ y7 5 (9-5) [], y5 9 5 D := yd (xs := b49++b50++b51) CA9_5 (by
  refine y3 b49 pb49 ?_
  refine y3 b50 pb50 ?_
  exact pb51)
noncomputable def b39:List y6:=eval% yf 9 4 h9_4 0 4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb39:b39.all (y1 9 4):=by decide +kernel
noncomputable def b40:List y6:=eval% yf 9 4 h9_4 4 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb40:b40.all (y1 9 4) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b41:List y6:=eval% yf 9 4 h9_4 5 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb41:b41.all (y1 9 4) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b42:List y6:=eval% yf 9 4 h9_4 6 3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb42:b42.all (y1 9 4):=by decide +kernel
noncomputable def b43:List y6:=eval% yf 9 4 h9_4 9 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb43:b43.all (y1 9 4) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b44:List y6:=eval% yf 9 4 h9_4 10 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb44:b44.all (y1 9 4):=by decide +kernel
noncomputable def b45:List y6:=eval% yf 9 4 h9_4 15 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb45:b45.all (y1 9 4) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b46:List y6:=eval% yf 9 4 h9_4 16 7
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb46:b46.all (y1 9 4):=by decide +kernel
noncomputable def b47:List y6:=eval% yf 9 4 h9_4 23 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb47:b47.all (y1 9 4) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b48:List y6:=eval% yf 9 4 h9_4 24 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb48:b48.all (y1 9 4):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA9_4 : (b39++b40++b41++b42++b43++b44++b45++b46++b47++b48).map Prod.fst = y7 4 (9-4) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A9_4 : ∀ D ∈ y7 4 (9-4) [], y5 9 4 D := yd (xs := b39++b40++b41++b42++b43++b44++b45++b46++b47++b48) CA9_4 (by
  refine y3 b39 pb39 ?_
  refine y3 b40 pb40 ?_
  refine y3 b41 pb41 ?_
  refine y3 b42 pb42 ?_
  refine y3 b43 pb43 ?_
  refine y3 b44 pb44 ?_
  refine y3 b45 pb45 ?_
  refine y3 b46 pb46 ?_
  refine y3 b47 pb47 ?_
  exact pb48)
noncomputable def b38:List y6:=eval% yf 8 8 h8_8 0 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb38:b38.all (y1 8 8):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA8_8 : (b38).map Prod.fst = y7 8 (8-8) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A8_8 : ∀ D ∈ y7 8 (8-8) [], y5 8 8 D := yd (xs := b38) CA8_8 (by
  exact pb38)
noncomputable def b37:List y6:=eval% yf 8 7 h8_7 0 2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb37:b37.all (y1 8 7):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA8_7 : (b37).map Prod.fst = y7 7 (8-7) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A8_7 : ∀ D ∈ y7 7 (8-7) [], y5 8 7 D := yd (xs := b37) CA8_7 (by
  exact pb37)
noncomputable def b36:List y6:=eval% yf 8 6 h8_6 0 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb36:b36.all (y1 8 6):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA8_6 : (b36).map Prod.fst = y7 6 (8-6) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A8_6 : ∀ D ∈ y7 6 (8-6) [], y5 8 6 D := yd (xs := b36) CA8_6 (by
  exact pb36)
noncomputable def b33:List y6:=eval% yf 8 5 h8_5 0 3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb33:b33.all (y1 8 5):=by decide +kernel
noncomputable def b34:List y6:=eval% yf 8 5 h8_5 3 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb34:b34.all (y1 8 5) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b35:List y6:=eval% yf 8 5 h8_5 4 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb35:b35.all (y1 8 5):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA8_5 : (b33++b34++b35).map Prod.fst = y7 5 (8-5) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A8_5 : ∀ D ∈ y7 5 (8-5) [], y5 8 5 D := yd (xs := b33++b34++b35) CA8_5 (by
  refine y3 b33 pb33 ?_
  refine y3 b34 pb34 ?_
  exact pb35)
noncomputable def b27:List y6:=eval% yf 8 4 h8_4 0 3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb27:b27.all (y1 8 4):=by decide +kernel
noncomputable def b28:List y6:=eval% yf 8 4 h8_4 3 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb28:b28.all (y1 8 4) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b29:List y6:=eval% yf 8 4 h8_4 4 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb29:b29.all (y1 8 4) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b30:List y6:=eval% yf 8 4 h8_4 5 6
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb30:b30.all (y1 8 4):=by decide +kernel
noncomputable def b31:List y6:=eval% yf 8 4 h8_4 11 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb31:b31.all (y1 8 4) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b32:List y6:=eval% yf 8 4 h8_4 12 4
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb32:b32.all (y1 8 4):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA8_4 : (b27++b28++b29++b30++b31++b32).map Prod.fst = y7 4 (8-4) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A8_4 : ∀ D ∈ y7 4 (8-4) [], y5 8 4 D := yd (xs := b27++b28++b29++b30++b31++b32) CA8_4 (by
  refine y3 b27 pb27 ?_
  refine y3 b28 pb28 ?_
  refine y3 b29 pb29 ?_
  refine y3 b30 pb30 ?_
  refine y3 b31 pb31 ?_
  exact pb32)
noncomputable def b26:List y6:=eval% yf 7 7 h7_7 0 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb26:b26.all (y1 7 7):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA7_7 : (b26).map Prod.fst = y7 7 (7-7) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A7_7 : ∀ D ∈ y7 7 (7-7) [], y5 7 7 D := yd (xs := b26) CA7_7 (by
  exact pb26)
noncomputable def b25:List y6:=eval% yf 7 6 h7_6 0 2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb25:b25.all (y1 7 6):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA7_6 : (b25).map Prod.fst = y7 6 (7-6) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A7_6 : ∀ D ∈ y7 6 (7-6) [], y5 7 6 D := yd (xs := b25) CA7_6 (by
  exact pb25)
noncomputable def b24:List y6:=eval% yf 7 5 h7_5 0 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb24:b24.all (y1 7 5):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA7_5 : (b24).map Prod.fst = y7 5 (7-5) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A7_5 : ∀ D ∈ y7 5 (7-5) [], y5 7 5 D := yd (xs := b24) CA7_5 (by
  exact pb24)
noncomputable def b21:List y6:=eval% yf 7 4 h7_4 0 3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb21:b21.all (y1 7 4):=by decide +kernel
noncomputable def b22:List y6:=eval% yf 7 4 h7_4 3 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb22:b22.all (y1 7 4) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b23:List y6:=eval% yf 7 4 h7_4 4 5
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb23:b23.all (y1 7 4):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA7_4 : (b21++b22++b23).map Prod.fst = y7 4 (7-4) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A7_4 : ∀ D ∈ y7 4 (7-4) [], y5 7 4 D := yd (xs := b21++b22++b23) CA7_4 (by
  refine y3 b21 pb21 ?_
  refine y3 b22 pb22 ?_
  exact pb23)
noncomputable def b15:List y6:=eval% yf 7 3 h7_3 0 3
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb15:b15.all (y1 7 3):=by decide +kernel
noncomputable def b16:List y6:=eval% yf 7 3 h7_3 3 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb16:b16.all (y1 7 3) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b17:List y6:=eval% yf 7 3 h7_3 4 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb17:b17.all (y1 7 3) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b18:List y6:=eval% yf 7 3 h7_3 5 2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb18:b18.all (y1 7 3):=by decide +kernel
noncomputable def b19:List y6:=eval% yf 7 3 h7_3 7 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb19:b19.all (y1 7 3) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b20:List y6:=eval% yf 7 3 h7_3 8 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb20:b20.all (y1 7 3) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA7_3 : (b15++b16++b17++b18++b19++b20).map Prod.fst = y7 3 (7-3) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A7_3 : ∀ D ∈ y7 3 (7-3) [], y5 7 3 D := yd (xs := b15++b16++b17++b18++b19++b20) CA7_3 (by
  refine y3 b15 pb15 ?_
  refine y3 b16 pb16 ?_
  refine y3 b17 pb17 ?_
  refine y3 b18 pb18 ?_
  refine y3 b19 pb19 ?_
  exact pb20)
noncomputable def b14:List y6:=eval% yf 6 6 h6_6 0 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb14:b14.all (y1 6 6):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA6_6 : (b14).map Prod.fst = y7 6 (6-6) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A6_6 : ∀ D ∈ y7 6 (6-6) [], y5 6 6 D := yd (xs := b14) CA6_6 (by
  exact pb14)
noncomputable def b13:List y6:=eval% yf 6 5 h6_5 0 2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb13:b13.all (y1 6 5):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA6_5 : (b13).map Prod.fst = y7 5 (6-5) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A6_5 : ∀ D ∈ y7 5 (6-5) [], y5 6 5 D := yd (xs := b13) CA6_5 (by
  exact pb13)
noncomputable def b10:List y6:=eval% yf 6 4 h6_4 0 2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb10:b10.all (y1 6 4):=by decide +kernel
noncomputable def b11:List y6:=eval% yf 6 4 h6_4 2 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb11:b11.all (y1 6 4) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b12:List y6:=eval% yf 6 4 h6_4 3 2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb12:b12.all (y1 6 4):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA6_4 : (b10++b11++b12).map Prod.fst = y7 4 (6-4) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A6_4 : ∀ D ∈ y7 4 (6-4) [], y5 6 4 D := yd (xs := b10++b11++b12) CA6_4 (by
  refine y3 b10 pb10 ?_
  refine y3 b11 pb11 ?_
  exact pb12)
noncomputable def b6:List y6:=eval% yf 6 3 h6_3 0 2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb6:b6.all (y1 6 3):=by decide +kernel
noncomputable def b7:List y6:=eval% yf 6 3 h6_3 2 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb7:b7.all (y1 6 3) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b8:List y6:=eval% yf 6 3 h6_3 3 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb8:b8.all (y1 6 3) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b9:List y6:=eval% yf 6 3 h6_3 4 2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb9:b9.all (y1 6 3):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA6_3 : (b6++b7++b8++b9).map Prod.fst = y7 3 (6-3) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A6_3 : ∀ D ∈ y7 3 (6-3) [], y5 6 3 D := yd (xs := b6++b7++b8++b9) CA6_3 (by
  refine y3 b6 pb6 ?_
  refine y3 b7 pb7 ?_
  refine y3 b8 pb8 ?_
  exact pb9)
noncomputable def b5:List y6:=eval% yf 5 5 h5_5 0 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb5:b5.all (y1 5 5):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA5_5 : (b5).map Prod.fst = y7 5 (5-5) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A5_5 : ∀ D ∈ y7 5 (5-5) [], y5 5 5 D := yd (xs := b5) CA5_5 (by
  exact pb5)
noncomputable def b4:List y6:=eval% yf 5 4 h5_4 0 2
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb4:b4.all (y1 5 4):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA5_4 : (b4).map Prod.fst = y7 4 (5-4) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A5_4 : ∀ D ∈ y7 4 (5-4) [], y5 5 4 D := yd (xs := b4) CA5_4 (by
  exact pb4)
noncomputable def b0:List y6:=eval% yf 5 3 h5_3 0 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb0:b0.all (y1 5 3):=by decide +kernel
noncomputable def b1:List y6:=eval% yf 5 3 h5_3 1 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb1:b1.all (y1 5 3) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b2:List y6:=eval% yf 5 3 h5_3 2 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb2:b2.all (y1 5 3) := by
  apply yc _ (by decide)
  simp only [y1,Bool.and_eq_true]
  refine ⟨⟨⟨⟨?_,?_⟩,?_⟩,?_⟩,?_⟩
  all_goals first | (apply ye <;> repeat' first | apply ye | decide +kernel) | decide +kernel
noncomputable def b3:List y6:=eval% yf 5 3 h5_3 3 1
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem pb3:b3.all (y1 5 3):=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem CA5_3 : (b0++b1++b2++b3).map Prod.fst = y7 3 (5-3) []:=by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem A5_3 : ∀ D ∈ y7 3 (5-3) [], y5 5 3 D := yd (xs := b0++b1++b2++b3) CA5_3 (by
  refine y3 b0 pb0 ?_
  refine y3 b1 pb1 ?_
  refine y3 b2 pb2 ?_
  exact pb3)
set_option maxHeartbeats 8000000 in
theorem finite_range_x17 {k t : ℕ} (hk : 5 ≤ k) (hku : k ≤ 17) (ht : 3 ≤ t) (htk : t ≤ k) (ht8 : t ≤ 8) (half : k/2 ≤ t) : ∀ D ∈ y7 t (k-t) [], y5 k t D := by
  interval_cases k <;> interval_cases t <;> first
    | omega
    | exact A5_3
    | exact A5_4
    | exact A5_5
    | exact A6_3
    | exact A6_4
    | exact A6_5
    | exact A6_6
    | exact A7_3
    | exact A7_4
    | exact A7_5
    | exact A7_6
    | exact A7_7
    | exact A8_4
    | exact A8_5
    | exact A8_6
    | exact A8_7
    | exact A8_8
    | exact A9_4
    | exact A9_5
    | exact A9_6
    | exact A9_7
    | exact A9_8
    | exact A10_5
    | exact A10_6
    | exact A10_7
    | exact A10_8
    | exact A11_5
    | exact A11_6
    | exact A11_7
    | exact A11_8
    | exact A12_6
    | exact A12_7
    | exact A12_8
    | exact A13_6
    | exact A13_7
    | exact A13_8
    | exact A14_7
    | exact A14_8
    | exact A15_7
    | exact A15_8
    | exact A16_8
    | exact A17_8
theorem exact_range_18 (m n : ℕ) (hm : 4 ≤ m) (hmu : m ≤ 18) (hn : 3 ≤ n) (hnm : n ≤ m) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph m)
      (SimpleGraph.completeGraph (Fin n)) = (m-1)*(n-1)+1 := by
  have hu : RamseyProperty m n ((m-1)*(n-1)+1) := by
    suffices h : RamseyProperty ((m-1)+1) ((n-1)+1) ((m-1)*(n-1)+1) by
      simpa only [Nat.sub_add_cancel (show 1 ≤ m by omega),
        Nat.sub_add_cancel (show 1 ≤ n by omega)] using h
    by_contra hfailure
    obtain ⟨a,ha,hak,G,hcycle,hα,hexp⟩ :=
      minimal_expanding_counterexample (by omega : 2 ≤ n-1)
        (by omega : n-1 ≤ m-1) hfailure
    by_cases hs : m-1 ≤ 4
    · exact reduced_small_impossible (by omega) hs ha hak (Fintype.card_fin _) hα hcycle hexp
    by_cases hnine : 9 ≤ G.cliqueNum
    · exact reduced_large_impossible (by omega) ha hak (Fintype.card_fin _) hα hcycle hexp hnine
    classical
    obtain ⟨hl,hu⟩ := counterexample_clique_bound (by omega) ha hak (Fintype.card_fin _) hα hcycle hexp
    obtain ⟨Q,hQ⟩ := G.exists_isNClique_cliqueNum
    have hc : (Q : Set (Fin ((m-1)*a+1))).ncard = G.cliqueNum := by
      rw [Set.ncard_coe_finset,hQ.card_eq]
    have h3 : 3 ≤ G.cliqueNum := (le_max_left _ _).trans hl
    have hh : (m-1)/2 ≤ G.cliqueNum := (le_max_right _ _).trans hl
    have H : FiniteHyp G (m-1) G.cliqueNum := ⟨by omega,h3,hu,hcycle,le_rfl,hα.trans hak,hexp⟩
    have ht8 : G.cliqueNum ≤ 8 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hnine)
    exact finite_verified_of_patterns H hQ.isClique hc
      (finite_range_x17 (by omega) (by omega) h3 hu ht8 hh)
  change cycleCliqueRamsey m n = _
  apply le_antisymm (Nat.sInf_le hu)
  exact ramsey_property_lower_bound (by omega) (by omega)
    (Nat.sInf_mem (s := {N | RamseyProperty m n N}) ⟨_,hu⟩)
theorem finite_leaf (k n : ℕ) (hk : k ≤ 18) (hn : 3 ≤ n) (hnk : n ≤ k) (he : ¬(n=3 ∧ k=3)) :
    SimpleGraph.graphRamsey (SimpleGraph.cycleGraph k) (SimpleGraph.completeGraph (Fin n)) = (k-1)*(n-1)+1 := exact_range_18 k n (by omega) hk hn hnk
end
end OAI.CycleClique
theorem OMA.solution : OMA.R_Erdos551_erdos_551_R1.H2 := OAI.CycleClique.finite_leaf
