import FormalConjectures.Wikipedia.UnionClosed
import Mathlib

/-! -/
namespace OMA.R_UnionClosed_union_closed_variants_univ_card_R1
open Finset UnionClosed
open scoped Classical
def H1:Prop:=∀ F:Finset (Finset (Fin 12)),IsUnionClosed F->∅∈F->univ∈F->
 (∃ S∈F,S.card=3)->(∀ S∈F,S.Nonempty->3≤ S.card)->
 ∃ w:Fin 12->ℕ,0 < ∑ i,w i∧
  F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i)
def H2:Prop:=∀ F:Finset (Finset (Fin 12)),IsUnionClosed F->∅∈F->univ∈F->
 (∃ S∈F,S.card=4)->(∀ S∈F,S.Nonempty->4≤ S.card)->
 ∃ w:Fin 12->ℕ,0 < ∑ i,w i∧
  F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i)
def H3:Prop:=∀ F:Finset (Finset (Fin 12)),IsUnionClosed F->∅∈F->univ∈F->
 (∃ S∈F,∃ T∈F,S≠T∧S.card=5∧T.card=5)->(∀ S∈F,S.Nonempty->5≤ S.card)->
 ∃ w:Fin 12->ℕ,0 < ∑ i,w i∧
  F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i)
lemma incidence (F:Finset (Finset (Fin 12))) (w:Fin 12->ℕ):
 (∑ S∈F,∑ i∈S,w i)=∑ i,w i*(F.filter (i∈·)).card:=by
 calc
  _=∑ S∈F,∑ i:Fin 12,if i∈S then w i else 0:=by simp
  _=∑ i:Fin 12,∑ S∈F,if i∈S then w i else 0:=sum_comm
  _=_:=by
   apply sum_congr rfl;intro i _;rw[←sum_filter];simp[Nat.mul_comm]
lemma witness (F:Finset (Finset (Fin 12))) (w:Fin 12->ℕ) (wp:0 < ∑ i,w i)
 (hw:F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i)):
 ∃ i,F.card≤ 2*(F.filter (i∈·)).card:=by
 by_contra! fail;have h:=sum_le_sum (s:=univ) (fun (i:Fin 12) _=>
  Nat.mul_le_mul_left (w i) (show 2*(F.filter (i∈·)).card+1≤ F.card from fail i))
 simp only[mul_add,mul_one,sum_add_distrib,←sum_mul] at h;rw[incidence] at hw;have v0:(∑ i,w i*(2*(F.filter (i∈·)).card))=
  2*(∑ i,w i*(F.filter (i∈·)).card):=by rw[mul_sum];apply sum_congr rfl;intros;ring
 rw[v0,mul_comm (∑ i,w i) F.card] at h;omega
lemma small_member (F:Finset (Finset (Fin 12))) (closed:IsUnionClosed F)
 (a b:Fin 12) (pair:{a,b}∈F):∃ i,F.card≤ 2*(F.filter (i∈·)).card:=by
 let A:=F.filter (a∈·);let B:=F.filter (b∈·);let none:=F \ (A∪B)
 have v0 {X:Finset (Fin 12)} (hX:X∈none):X∈F∧a∉X∧b∉X:=by
  have h:=mem_sdiff.mp hX;simpa[A,B,h.1] using h
 have inj:none.card≤ (A∩B).card:=by
  apply card_le_card_of_injOn (fun X=>X∪{a,b})
  · intro X hX;obtain ⟨xf,_,_⟩:=v0 hX;have u:=closed _ xf _ pair;exact mem_inter.mpr ⟨mem_filter.mpr ⟨u,by simp⟩,mem_filter.mpr ⟨u,by simp⟩⟩
  · intro X hX Y hY eq
    have x:=v0 hX;have y:=v0 hY;ext i;by_cases ia:i=a
    · simp[ia,x.2.1,y.2.1]
    by_cases ib:i=b
    · simp[ib,x.2.2,y.2.2]
    simpa[ia,ib] using Finset.ext_iff.mp eq i
 have sub:A∪B⊆F:=union_subset (filter_subset _ _) (filter_subset _ _);have v1:=card_sdiff_add_card_eq_card sub;have overlap:=card_union_add_card_inter A B;change none.card+(A∪B).card=F.card at v1;by_cases h:F.card≤ 2*A.card
 · exact ⟨a,h⟩
 · exact ⟨b,by change F.card≤ 2*B.card;omega⟩
lemma large_members (F:Finset (Finset (Fin 12))) (empty:∅∈F) (full:univ∈F)
 (hl:∀ S∈F,S.Nonempty->6≤ S.card):∃ i,F.card≤ 2*(F.filter (i∈·)).card:=by
 let M:=(F.erase ∅).erase univ;have ef:(univ:Finset (Fin 12))≠∅:=univ_nonempty.ne_empty;have nu:univ∉M:=notMem_erase _ _;have ne:∅∉M:=fun h=>(notMem_erase ∅ F) (mem_of_mem_erase h)
 have v0:F=insert ∅ (insert univ M):=by
  dsimp[M];rw[insert_erase (mem_erase.mpr ⟨ef,full⟩),insert_erase empty]
 have sum:6*M.card≤ ∑ S∈M,S.card:=by
  have h:=sum_le_sum (s:=M) (f:=fun _=>6) (g:=Finset.card) (fun S hS=>
   hl S (mem_of_mem_erase (mem_of_mem_erase hS)) (nonempty_iff_ne_empty.mpr (mem_erase.mp (mem_of_mem_erase hS)).1))
  simpa[Nat.mul_comm] using h
 apply witness F (fun _=>1) (by simp);simp only[sum_const,nsmul_eq_mul,Nat.cast_id,card_univ,Fintype.card_fin,mul_one]
 have n0:(∅:Finset (Fin 12))∉insert univ M:=by simp[ef.symm,ne]
 rw[v0,card_insert_of_notMem n0,card_insert_of_notMem nu,sum_insert n0,sum_insert nu];simp only[card_empty,card_univ,Fintype.card_fin,zero_add];omega
lemma unique_five (F:Finset (Finset (Fin 12))) (closed:IsUnionClosed F)
 (empty:∅∈F) (full:univ∈F) (low:∀ X∈F,X.Nonempty->5≤ X.card)
 (S:Finset (Fin 12)) (sf:S∈F) (sc:S.card=5)
 (only:∀ X∈F,X.card=5->X=S):∃ i,F.card≤ 2*(F.filter (i∈·)).card:=by
 have se:S≠∅:=by intro h;simp[h] at sc
 have su:S≠univ:=by intro h;simp[h] at sc
 have ue:(univ:Finset (Fin 12))≠∅:=univ_nonempty.ne_empty;by_cases big:∃ Y∈F,Y≠univ∧7≤Y.card
 · obtain ⟨Y,yf,yu,yc⟩:=big
   have ye:Y≠∅:=by intro e;simp[e] at yc
   have ys:Y≠S:=by intro e;rw[e,sc] at yc;omega
   let P:=(((F.erase ∅).erase univ).erase S).erase Y;have sm:S∈(F.erase ∅).erase univ:=mem_erase.mpr ⟨su,mem_erase.mpr ⟨se,sf⟩⟩;have ym:Y∈((F.erase ∅).erase univ).erase S:=mem_erase.mpr ⟨ys,mem_erase.mpr ⟨yu,mem_erase.mpr ⟨ye,yf⟩⟩⟩
   have allp:6*P.card≤ ∑ X∈P,X.card:=by
    have bound (X) (h:X∈P):6≤ X.card:=by
     simp only[P,mem_erase] at h;have l:=low X h.2.2.2.2 (nonempty_iff_ne_empty.mpr h.2.2.2.1);have ne:=h.2.1
     by_contra! no;exact ne (only X h.2.2.2.2 (by omega))
    have:=sum_le_sum (s:=P) (f:=fun _=>6) (g:=Finset.card) bound;simpa[Nat.mul_comm] using this
   have pe:∅∉P:=by simp[P]
   have pu:univ∉P:=by simp[P]
   have ps:S∉P:=by simp[P]
   have py:Y∉P:=notMem_erase _ _
   have split:F=insert ∅ (insert univ (insert S (insert Y P))):=by
    dsimp[P];rw[insert_erase ym,insert_erase sm,insert_erase (mem_erase.mpr ⟨ue,full⟩),insert_erase empty]
   apply witness F (fun _=>1) (by simp);simp only[sum_const,nsmul_eq_mul,Nat.cast_id,card_univ,Fintype.card_fin,mul_one];rw[split];simp[pe,pu,ps,py,se.symm,su.symm,ue.symm,ye.symm,yu.symm,ys.symm,sc];omega
 · have all (X) (hX:X∈F) (ne:X.Nonempty):S⊆X:=by
    by_cases whole:X=univ
    · simp[whole]
    by_cases five:X.card=5
    · rw[only X hX five]
    have c:=low X hX ne
    have upper:X.card<7:=by by_contra! no;exact big ⟨X,hX,whole,no⟩
    have six:X.card=6:=by omega
    by_contra no;have sub:X ⊂ X∪S:=Finset.ssubset_iff_subset_ne.mpr ⟨subset_union_left,fun eq=>by
      have h:S⊆X∪S:=subset_union_right;rw[←eq] at h;exact no h⟩
    have high:=card_lt_card sub;have v2:=card_union_le X S
    have v1:X∪S≠univ:=by intro eq;rw[eq] at v2;simp[six,sc] at v2
    exact big ⟨X∪S,closed _ hX _ sf,v1,by omega⟩
   obtain ⟨i,hi⟩:=nonempty_iff_ne_empty.mpr se
   have v0:F.erase ∅⊆F.filter (i∈·):=by
    intro X hX;exact mem_filter.mpr ⟨mem_of_mem_erase hX,all X (mem_of_mem_erase hX) (nonempty_iff_ne_empty.mpr (mem_erase.mp hX).1) hi⟩
   have h:=card_le_card v0;have p:0 < (F.erase ∅).card:=card_pos.mpr ⟨S,mem_erase.mpr ⟨se,sf⟩⟩;have eq:=card_erase_add_one empty;exact ⟨i,by omega⟩
lemma twelve (h₃:H1) (h₄:H2) (h₅:H3) (F:Finset (Finset (Fin 12)))
 (closed:IsUnionClosed F) (empty:∅∈F) (full:univ∈F):∃ i,F.card≤ 2*(F.filter (i∈·)).card:=by
 by_cases small:∃ S∈F,S.Nonempty∧S.card≤ 2
 · obtain ⟨S,hS,ne,le⟩:=small
   by_cases one:S.card=1
   · obtain ⟨a,rfl⟩:=card_eq_one.mp one;exact small_member F closed a a (by simpa using hS)
   · obtain ⟨a,b,_,rfl⟩:=card_eq_two.mp (show S.card=2 by have:=card_pos.mpr ne;omega);exact small_member F closed a b hS
 have v2 (S) (hS:S∈F) (ne:S.Nonempty):3≤ S.card:=by
   by_contra! no;exact small ⟨S,hS,ne,by omega⟩
 have v0 (k:ℕ) (bound:∀ S∈F,S.Nonempty->k≤ S.card)
    (no:¬ ∃ S∈F,S.card=k) (S) (hS:S∈F) (hne:S.Nonempty):k+1≤ S.card:=by
   have:=bound S hS hne;have diff:S.card≠k:=fun eq=>no ⟨S,hS,eq⟩;omega
 by_cases three:∃ S∈F,S.card=3
 · obtain ⟨w,p,b⟩:=h₃ F closed empty full three v2;exact witness F w p b
 have v3:=v0 3 v2 three;by_cases four:∃ S∈F,S.card=4
 · obtain ⟨w,p,b⟩:=h₄ F closed empty full four v3;exact witness F w p b
 have v1:=v0 4 v3 four;by_cases five:∃ S∈F,S.card=5
 · obtain ⟨S,sf,sc⟩:=five
   by_cases another:∃ T∈F,T.card=5∧T≠S
   · obtain ⟨T,tf,tc,ts⟩:=another;obtain ⟨w,p,b⟩:=h₅ F closed empty full ⟨S,sf,T,tf,ts.symm,sc,tc⟩ v1;exact witness F w p b
   · exact unique_five F closed empty full v1 S sf sc (fun X hX c=>by
      by_contra h;exact another ⟨X,hX,c,h⟩)
 exact large_members F empty full (v0 5 v1 five)
lemma support_mem {α:Type*} [DecidableEq α] {F:Finset (Finset α)} (h:IsUnionClosed F)
 (e:∅∈F) (B:Finset (Finset α)) (sub:B⊆F):B.biUnion id∈F:=by
 induction B using Finset.induction_on with
 | empty=>simpa using e
 | @insert X B _ ih=>
  rw[biUnion_insert];exact h _ (sub (mem_insert_self ..)) _ (ih (fun _ hB=>sub (mem_insert_of_mem hB)))
lemma clones {α:Type*} [Fintype α] [DecidableEq α] (T:Finset α) (n:T.Nonempty)
 (bound:Fintype.card α≤ 12):∃ f:Fin 12->α,(∀ i,f i∈T)∧∀ t∈T,∃ i,f i=t:=by
 obtain ⟨z,hz⟩:=n;let e:=Fintype.equivFin ↥T
 have size:Fintype.card ↥T≤ 12:=by simpa using (T.card_le_univ.trans bound)
 let f (i:Fin 12):α:=if hi:i.val < Fintype.card ↥T then (e.symm ⟨i.val,hi⟩).val else z;refine ⟨f,?_,?_⟩
 · intro i;dsimp[f];split_ifs;exact Subtype.property _;exact hz
 · intro t ht;let j:=e ⟨t,ht⟩;refine ⟨⟨j.val,j.isLt.trans_le size⟩,?_⟩;change (if hi:j.val < Fintype.card ↥T then (e.symm ⟨j.val,hi⟩).val else z)=t;rw[dif_pos j.isLt];exact congrArg Subtype.val (e.symm_apply_apply ⟨t,ht⟩)
theorem main:H1->H2->H3->type_of% @UnionClosed.union_closed.variants.univ_card:=by
 intro h₃ h₄ h₅ α de A fa neα nontrivial closed bound;by_cases zero:A=∅
 · subst A;obtain ⟨a⟩:=neα;exact ⟨a,by simp⟩
 have v3:∃ S∈A,S.Nonempty:=by
   by_contra! empty;apply nontrivial;apply (Finset.nonempty_iff_ne_empty.mpr zero).subset_singleton_iff.mp;intro S hS;exact mem_singleton.mpr (empty S hS)
 let F:=insert ∅ A
 have v1:IsUnionClosed F:=by
   intro X hx Y hy
   rcases mem_insert.mp hx with rfl|x<;>rcases mem_insert.mp hy with rfl|y
   · simp[F]
   · simpa[F] using (mem_insert_of_mem y:Y∈F)
   · simpa[F] using (mem_insert_of_mem x:X∈F)
   · exact mem_insert_of_mem (closed X x Y y)
 let T:=F.biUnion id;have en:∅∈F:=mem_insert_self ..;have top:T∈F:=support_mem v1 en F (by rfl);have sub (S:Finset α) (hS:S∈F):S⊆T:=fun i hi=>mem_biUnion.mpr ⟨S,hS,hi⟩;obtain ⟨S,sA,t,ht⟩:=v3;obtain ⟨f,inside,surj⟩:=clones T ⟨t,sub S (mem_insert_of_mem sA) ht⟩ bound;let v0 (S:Finset α):=univ.filter (fun i:Fin 12=>f i∈S);let B:=F.image v0
 have v2 (S:Finset α) (i:Fin 12):i∈v0 S↔f i∈S:=by simp[v0]
 have inj:Set.InjOn v0 (F:Set (Finset α)):=by
   intro X hx Y hy eq;ext i;by_cases ti:i∈T
   · obtain ⟨u,rfl⟩:=surj i ti;rw[←v2 X,←v2 Y,eq]
   · have nx:i∉X:=fun h=>ti (sub X hx h);have ny:i∉Y:=fun h=>ti (sub Y hy h);simp[nx,ny]
 have v4:IsUnionClosed B:=by
   intro U hu V hv;obtain ⟨X,hX,rfl⟩:=mem_image.mp hu;obtain ⟨Y,hY,rfl⟩:=mem_image.mp hv;refine mem_image.mpr ⟨X∪Y,v1 _ hX _ hY,?_⟩;ext i;simp[v0]
 have be:∅∈B:=mem_image.mpr ⟨∅,en,by simp[v0]⟩;have bt:univ∈B:=mem_image.mpr ⟨T,top,by ext i;simp[v0,inside]⟩;obtain ⟨i,hi⟩:=twelve h₃ h₄ h₅ B v4 be bt
 have v7:B.filter (i∈·)=(F.filter (f i∈·)).image v0:=by
   ext U;constructor
   · intro hU;obtain ⟨hU,u⟩:=mem_filter.mp hU;obtain ⟨X,hX,rfl⟩:=mem_image.mp hU;exact mem_image.mpr ⟨X,mem_filter.mpr ⟨hX,(v2 _ _).mp u⟩,rfl⟩
   · intro hU;obtain ⟨X,hX,rfl⟩:=mem_image.mp hU;exact mem_filter.mpr ⟨mem_image_of_mem _ (mem_filter.mp hX).1,(v2 _ _).mpr (mem_filter.mp hX).2⟩
 have v6:F.filter (f i∈·)=A.filter (f i∈·):=by ext X;simp[F];aesop
 have bc:B.card=F.card:=card_image_of_injOn inj
 have fi:Set.InjOn v0 (↑(F.filter (f i∈·)):Set (Finset α)):=
   inj.mono (fun _ hs=>(mem_filter.mp hs).1)
 have v5:(B.filter (i∈·)).card=(A.filter (f i∈·)).card:=by rw[v7,card_image_of_injOn fi,v6]
 rw[bc,v5] at hi;have hb:A.card≤ 2*(A.filter (f i∈·)).card:=(card_le_card (subset_insert ∅ A)).trans hi;refine ⟨f i,?_⟩
 have cast:(A.card:ℚ)≤ 2*((A.filter (f i∈·)).card:ℚ):=by exact_mod_cast hb
 linarith
end OMA.R_UnionClosed_union_closed_variants_univ_card_R1
namespace UC
open Finset
open List (not_mem_nil nodup_cons mem_append map_congr_left all_append nodup_nil mem_of_getElem? getD_eq_getElem?_getD getElem_mem mem_of_getElem contains_eq_mem getElem_map Perm Subperm)
open Bool (or_eq_false_iff eq_false_iff false_ne_true)
open Nat (shiftLeft shiftRight ble_eq beq_eq testBit_lor testBit_shiftRight testBit_shiftLeft testBit_two_pow bitwise_lt_two_pow eq_of_testBit_eq two_pow_pos zero_le shiftLeft_eq pow_le_pow_right lor_assoc testBit_succ beq ble land lor testBit_zero zero_testBit lor_comm shiftRight_eq_div_pow testBit_eq_false_of_lt pow_lt_pow_right mod_two_eq_zero_or_one mod_lt and_one_is_mod div_lt_of_lt_mul pow_one pow_add mul_le_mul_left testBit_land div_add_mod mul_le_mul_right)
open Option (getD_some isSome_iff_exists)
abbrev SS:=Finset (Finset (Fin 12))
abbrev SF:=Finset (Fin 12)
abbrev ff:=false
abbrev tt:=true
abbrev iUC {α:Type*} [DecidableEq α]:=@UnionClosed.IsUnionClosed α _
abbrev LN:=List Nat
abbrev LF:=List (Fin 12)
abbrev WF:=Fin 12->ℕ
lemma qF {α:Type*} {s:Finset α} {p:α->Prop} [DecidablePred p] {a:α}:a∈s.filter p↔a∈s∧p a:=Finset.mem_filter
lemma qC {α:Type*} {a b:α} {l:List α}:a∈b :: l↔a=b∨a∈l:=List.mem_cons
lemma qP {α:Type*} {s t:Finset α} {n:ℕ}:s∈t.powersetCard n↔s⊆t∧s.card=n:=Finset.mem_powersetCard
lemma qD {p:Prop} [Decidable p]:(decide p=true)=p:=decide_eq_true_eq
lemma qT {α:Type*} [DecidableEq α] {l:List α} (h:l.Nodup):l.toFinset.card=l.length:=List.toFinset_card_of_nodup h
lemma qI {α β:Type*} [DecidableEq β] {f:α->β} {s:Finset α} {b:β}:b∈s.image f↔∃ a∈s,f a=b:=Finset.mem_image
lemma qL {α:Type*} {s t:Finset α} (h:s⊆t):s.card≤ t.card:=Finset.card_le_card h
lemma qU {α:Type*} [DecidableEq α] {s t:Finset α}:s⊆s∪t:=Finset.subset_union_left
lemma qUr {α:Type*} [DecidableEq α] {s t:Finset α}:t⊆s∪t:=Finset.subset_union_right
lemma qN {α:Type*} {l:List α}:l.Nodup↔Function.Injective (fun i:Fin l.length=>l[i.val]):=List.nodup_iff_injective_getElem
lemma qE {α:Type*} {l:List α} {p:α->Bool}:l.all p=true↔∀ x∈l,p x=true:=List.all_eq_true
lemma qM {α:Type*} [DecidableEq α] {a:α} {l:List α}:a∈l.toFinset↔a∈l:=List.mem_toFinset
lemma qA (a b:Bool):((a&&b)=true)=(a=true∧b=true):=Bool.and_eq_true a b
lemma qOr {a b:Bool}:((a||b)=true)=(a=true∨b=true):=Bool.or_eq_true a b
lemma qFl:(false=true)=False:=Bool.false_eq_true
lemma qS {α:Type*} {s t:Finset α} (h1:s⊆t) (h2:t.card≤ s.card):s=t:=Finset.eq_of_subset_of_card_le h1 h2
lemma qK {α β:Type*} [DecidableEq β] (s:Finset α) {f:α->β} (h:Function.Injective f):(s.image f).card=s.card:=Finset.card_image_of_injective s h
lemma qO {α:Type*} {a:α} (b:α) {l:List α} (h:a∈l):a∈b :: l:=List.mem_cons_of_mem b h
lemma qG {α:Type*} {a:α} {l:List α}:a∈a :: l:=List.mem_cons_self
lemma qB {α:Type*} {p:α->Bool} {a:α} {l:List α}:a∈l.filter p↔a∈l∧p a=true:=List.mem_filter
lemma qR {m n:ℕ}:m∈List.range n↔m < n:=List.mem_range
lemma qMr {m n:ℕ}:m∈Finset.range n↔m < n:=Finset.mem_range
lemma qSd {α:Type*} [DecidableEq α] {a:α} {s t:Finset α}:a∈s \ t↔a∈s∧a∉t:=Finset.mem_sdiff
lemma qY (n m:ℕ):n*m=m*n:=Nat.mul_comm n m
lemma qW (a n:ℕ):a ^ (n+1)=a ^ n*a:=Nat.pow_succ a n
lemma qZ (n:ℕ):1*n=n:=Nat.one_mul n
lemma q0:((0:ℕ):ℤ)=0:=Nat.cast_zero
lemma q1:((1:ℕ):ℤ)=1:=Nat.cast_one
lemma qBi {α:Type*} [BEq α] [LawfulBEq α] {a b:α}:((a==b)=true)↔a=b:=beq_iff_eq
lemma qBs {α:Type*} [BEq α] [LawfulBEq α] (a:α):(a==a)=true:=beq_self_eq_true a
lemma qJ {α:Type*} {R:α->α->Prop} {a:α} {l:List α}:(a :: l).Pairwise R↔(∀ a'∈l,R a a')∧l.Pairwise R:=List.pairwise_cons
lemma qV {α:Type*} {l1 l2:List α}:(l1++l2).Nodup↔l1.Nodup∧l2.Nodup∧∀ a∈l1,∀ b∈l2,a≠b:=List.nodup_append
lemma qNt:(!true)=false:=Bool.not_true
lemma qNf:(!false)=true:=Bool.not_false
lemma q2 {n:ℕ} [n.AtLeastTwo]:((no_index (OfNat.ofNat n):ℕ):ℤ)=OfNat.ofNat n:=Nat.cast_ofNat
abbrev qEm:=@Finset.eq_empty_iff_forall_notMem
abbrev qCf:=@Fintype.card_fin
abbrev qPl:=@Nat.pow_le_pow_right
abbrev qEf:=@Bool.eq_false_iff
abbrev qSl:=@Nat.shiftLeft_eq
abbrev qSr:=@Nat.shiftRight_eq_div_pow
abbrev qCu:=@Finset.card_union_of_disjoint
abbrev qCa:=@Finset.card_union_add_card_inter
abbrev qNe:=@Finset.nonempty_iff_ne_empty
abbrev qLt:=@lt_of_lt_of_le
abbrev qNm:=@List.not_mem_nil
abbrev qCm:=@List.contains_eq_mem
abbrev qC1:=@Finset.card_eq_one
abbrev qMg:=@List.mem_of_getElem
abbrev qMe:=@Finset.mem_of_mem_erase
abbrev qSu:=@Finset.sdiff_union_inter
abbrev qSg:=@Finset.sum_range_succ
abbrev qCp:=@Finset.card_powersetCard
abbrev qMs:=@Finset.mem_singleton_self
abbrev qUs:=@Finset.union_subset
abbrev qAm:=@Nat.and_two_pow_sub_one_eq_mod
abbrev qFs:=@Finset.filter_subset
abbrev q3:=@Finset.length_toList
abbrev q4:=@List.nodup_cons
abbrev q5:=@Nat.bitwise_lt_two_pow
abbrev q7:=@Finset.mem_powerset
abbrev q8:=@Nat.eq_of_testBit_eq
abbrev qa:=@Finset.card_eq_zero
abbrev qb:=@Finset.mem_singleton
abbrev qc:=@Option.isSome_iff_exists
abbrev qd:=@List.getElem_mem
abbrev qe:=@Finset.card_sdiff_of_subset
abbrev qf:=@Finset.singleton_subset_iff
abbrev qg:=@Nat.testBit_eq_false_of_lt
abbrev qh:=@Finset.sum_congr
abbrev qi:=@Finset.sdiff_eq_empty_iff_subset
abbrev qj:=@Finset.sum_fiberwise_of_maps_to
abbrev qk:=@Nat.testBit_two_pow
abbrev ql:=@List.getElem_map
abbrev qm:=@Nat.testBit_succ
abbrev qn:=@Nat.mod_two_eq_zero_or_one
abbrev qo:=@Finset.mem_insert
abbrev qp:=@Finset.mem_toList
abbrev qq:=@Finset.union_inter_distrib_right
abbrev qr:=@Finset.card_pos
abbrev qs:=@or_false
abbrev qt:=@Option.getD_some
abbrev qu:=@Finset.card_compl
abbrev qv:=@Finset.nodup_toList
abbrev qw:=@Finset.card_singleton
abbrev sl:=Nat.shiftLeft
abbrev sr:=Nat.shiftRight
def Z3L:LF->Nat->SF
 | [],_=>∅
 | a :: as,x=>if x % 2=1 then insert a (Z3L as (x/2)) else Z3L as (x/2)
def Z3k:∀ {r:Nat},(Fin r->Bool)->Nat
 | 0,_=>0
 | _+1,f=>(if f 0 then 1 else 0)+2*Z3k (fun i=>f i.succ)
noncomputable def Z3M (ms:LF) (A:SF):Nat:=
 Z3k (fun i:Fin ms.length=>decide (ms.get i∈A))
def Z5o:Nat->Nat->Nat
 | 0,_=>0
 | n+1,x=>(x % 2)+Z5o n (x/2)
def Z5f:LN->Nat->Nat
 | [],_=>0
 | w :: ws,x=>(if x % 2=1 then w else 0)+Z5f ws (x/2)
def or7 (a b:Nat):Nat:=a|||b
def Z5p (a b:Nat):Nat:=a|||b
def bT (m u:Nat):Bool:=
 beq (m >>> u &&& 1) 1
def Z5r (_ a b:Nat):Nat:=a &&& b
def Z4X (_ a b:Nat):Nat:=a ^^^ (a &&& b)
lemma bTe (m u:Nat):bT m u=m.testBit u:=by
 dsimp[bT];rw[Nat.testBit,Nat.land_comm 1]
 cases h:(m >>> u &&& 1) with
 | zero=>rfl
 | succ k=>
  have hk:k=0:=by have:=Nat.and_lt_two_pow (m >>> u) (by omega:1 < 2 ^ 1);omega
  subst hk;simp
lemma ZF:∀ (u G a:Nat),G.testBit u=false->
 (G+2 ^ u).testBit a=(decide (a=u)||G.testBit a)
 | 0,G,a,hG=>by
  have hm:G % 2=0:=by
   rw[testBit_zero] at hG;cases h:G % 2 with
   | zero=>rfl
   | succ _=>
    have:G % 2=1:=by have:=mod_lt G (by omega:0 < 2);omega
    simp[this] at hG
  cases a with
  | zero=>simp[testBit_zero];omega
  | succ a=>
   simp only[qm,Nat.pow_zero]
   have v0:(G+1)/2=G/2:=by omega
   rw[v0];simp
 | u+1,G,a,hG=>by
  rw[qm] at hG;have ih:=ZF u (G/2);cases a with
  | zero=>
   simp only[testBit_zero,qW,qY _ 2]
   have:(G+2*2 ^ u)% 2=G % 2:=by omega
   simp[this]
  | succ a=>
   simp only[qm,qW,qY _ 2]
   have v0:(G+2*2 ^ u)/2=G/2+2 ^ u:=by omega
   rw[v0,ih (a:=a) hG];simp
lemma Z3m {a b:Nat} (_ha:a < 256) (_hb:b < 256):or7 a b=a|||b:=rfl
lemma Z1I {a b:Nat} (_ha:a < 4096) (_hb:b < 4096):Z5p a b=a|||b:=rfl
lemma Q1:∀ {r:Nat} (f:Fin r->Bool),Z3k f < 2 ^ r
 | 0,_=>by simp[Z3k]
 | n+1,f=>by
  have ih:=Q1 (fun i:Fin n=>f i.succ);dsimp[Z3k]
  split_ifs<;>simp[qW]<;>omega
lemma ZZ:∀ {r:Nat} (f:Fin r->Bool) (j:Fin r),
 (Z3k f).testBit j.val=f j
 | 0,_,j=>Fin.elim0 j
 | _+1,f,j=>by
  refine Fin.cases ?_ ?_ j
  · dsimp[Z3k]
    cases f 0<;>simp[testBit_zero]
  · intro i
    dsimp[Z3k];have ih:=ZZ (fun t=>f t.succ) i;cases h0:f 0
    · simp only[qFl,↓reduceIte];rw[qm,show (0+2*Z3k fun i=>f i.succ)/2=
       Z3k (fun i=>f i.succ) by omega]
      exact ih
    · simp only[↓reduceIte];rw[qm,show (1+2*Z3k fun i=>f i.succ)/2=
       Z3k (fun i=>f i.succ) by omega]
      exact ih
lemma Zt:∀ {r:Nat} (x:Nat),x < 2 ^ r->
 Z3k (fun i:Fin r=>x.testBit i.val)=x
 | 0,x,hx=>by simp at hx;simp[Z3k,hx]
 | n+1,x,hx=>by
  have v2:x/2 < 2 ^ n:=by
   rw[qW,qY] at hx;exact div_lt_of_lt_mul hx
  have ih:=Zt (x/2) v2;have v1:(fun i:Fin n=>x.testBit (i.val+1))=
   (fun i:Fin n=>(x/2).testBit i.val):=by
   funext i;exact qm x i.val
  have v0:Z3k (fun i:Fin n=>x.testBit (i.val+1))=x/2:=by rw[v1,ih]
  have hd:Z3k (fun i:Fin (n+1)=>x.testBit i.val)=
   (if x.testBit 0 then 1 else 0)+
    2*Z3k (fun i:Fin n=>x.testBit (i.val+1)):=rfl
  rw[hd,v0,testBit_zero];cases qn x with
  | inl h=>simp[h];omega
  | inr h=>simp[h];omega
lemma Yg:∀ (ms:LF) (x:Nat),Z3L ms x⊆ms.toFinset
 | [],_=>by simp[Z3L]
 | a :: as,x=>by
  intro b hb;dsimp[Z3L] at hb;split_ifs at hb
  · rcases qo.mp hb with rfl|hb'
    · exact qM.mpr qG
    · exact qM.mpr (qO a (qM.mp (Yg as (x/2) hb')))
  · exact qM.mpr (qO a (qM.mp (Yg as (x/2) hb)))
lemma Y8:∀ (ms:LF) (x:Nat) (b:Fin 12),
 b∈Z3L ms x↔∃ i:Fin ms.length,x.testBit i.val=true∧ms.get i=b
 | [],_,b=>by simp[Z3L]
 | a :: as,x,b=>by
  dsimp[Z3L]
  have hbit0:x.testBit 0=true↔x % 2=1:=by
   rw[testBit_zero];cases qn x with
   | inl h=>simp[h]
   | inr h=>simp[h]
  constructor
  · intro hb
    split_ifs at hb with hx
    · rcases qo.mp hb with rfl|hb'
      · exact ⟨⟨0,by simp⟩,hbit0.mpr hx,rfl⟩
      · obtain ⟨i,hi,heq⟩:=(Y8 as (x/2) b).mp hb';exact ⟨i.succ,(qm x i.val).symm ▸ hi,heq⟩
    · obtain ⟨i,hi,heq⟩:=(Y8 as (x/2) b).mp hb;exact ⟨i.succ,(qm x i.val).symm ▸ hi,heq⟩
  · rintro ⟨i,hi,rfl⟩
    refine Fin.cases ?_ ?_ i hi
    · intro h0;have hx:x % 2=1:=hbit0.mp h0;simp[hx]
    · intro j hj
      have v1:(x/2).testBit j.val=true:=(qm x j.val)▸ hj;have v0:as.get j∈Z3L as (x/2):=
       (Y8 as (x/2) (as.get j)).mpr ⟨j,v1,rfl⟩
      split_ifs
      · exact mem_insert_of_mem v0
      · exact v0
lemma Y9 (ms:LF) (hn:ms.Nodup) (x:Nat) (i:Fin ms.length):
 ms.get i∈Z3L ms x↔x.testBit i.val=true:=by
 rw[Y8];constructor
 · rintro ⟨j,hj,heq⟩
   have v0:j=i:=hn.get_inj_iff.mp heq;rwa[← v0]
 · intro hi;exact ⟨i,hi,rfl⟩
lemma ZH (ms:LF) (hn:ms.Nodup) {A:SF}
 (hA:A⊆ms.toFinset):Z3L ms (Z3M ms A)=A:=by
 ext a;constructor
 · intro ha;obtain ⟨i,hi,rfl⟩:=(Y8 ms _ a).mp ha;dsimp[Z3M] at hi;rw[ZZ] at hi;exact of_decide_eq_true hi
 · intro ha;have v0:a∈ms:=qM.mp (hA ha);obtain ⟨i,rfl⟩:=List.mem_iff_get.mp v0;rw[Y9 ms hn];dsimp[Z3M];rw[ZZ];exact decide_eq_true ha
lemma VK (ms:LF) (A:SF):
 Z3M ms A < 2 ^ ms.length:=
 Q1 _
lemma ZI (ms:LF) (hn:ms.Nodup) {x:Nat} (hx:x < 2 ^ ms.length):
 Z3M ms (Z3L ms x)=x:=by
 have v0:(fun i:Fin ms.length=>decide (ms.get i∈Z3L ms x))=
  (fun i:Fin ms.length=>x.testBit i.val):=by
  funext i;cases hb:x.testBit i.val
  · rw[decide_eq_false (mt (Y9 ms hn x i).mp (by simp[hb]))]
  · rw[decide_eq_true ((Y9 ms hn x i).mpr hb)]
 simpa[Z3M,List.get_eq_getElem] using congrArg Z3k v0|>.trans (Zt x hx)
lemma Q2 (ms:LF) (hn:ms.Nodup) {x y:Nat}
 (hx:x < 2 ^ ms.length) (hy:y < 2 ^ ms.length):
 Z3L ms x=Z3L ms y->x=y:=by
 intro h;have:=congrArg (Z3M ms) h;rwa[ZI ms hn hx,ZI ms hn hy] at this
lemma Q3 (ms:LF) (x y:Nat):
 Z3L ms (x|||y)=Z3L ms x∪Z3L ms y:=by
 ext a;simp only[mem_union,Y8,Nat.testBit_or,qOr];constructor
 · rintro ⟨i,hi|hi,rfl⟩
   · left;exact ⟨i,hi,rfl⟩
   · right;exact ⟨i,hi,rfl⟩
 · rintro (⟨i,hi,rfl⟩|⟨i,hi,rfl⟩)
   · exact ⟨i,Or.inl hi,rfl⟩
   · exact ⟨i,Or.inr hi,rfl⟩
lemma Xr (ms:LF):Z3L ms 0=∅:=by ext a;simp[Y8]
lemma Xs:∀ (ms:LF),ms.Nodup->∀ (x:Nat),
 (Z3L ms x).card=Z5o ms.length x
 | [],_,_=>by simp[Z3L,Z5o]
 | a :: as,hn,x=>by
  rw[q4] at hn;have ih:=Xs as hn.2 (x/2);have v0:a∉Z3L as (x/2):=fun h=>
   hn.1 (qM.mp (Yg as (x/2) h))
  dsimp[Z3L,Z5o]
  split_ifs with hx
  · rw[card_insert_of_notMem v0,ih,hx];omega
  · have h0:x % 2=0:=by omega
    rw[ih,h0,zero_add]
lemma Q4 (wf:WF):∀ (ms:LF),ms.Nodup->∀ (x:Nat),
 (∑ i∈Z3L ms x,wf i)=Z5f (ms.map wf) x:=by
 intro ms hn;induction ms with
 | nil=>intro x;simp[Z3L,Z5f]
 | cons a as ih=>
  intro x;rw[q4] at hn;have v0:a∉Z3L as (x/2):=fun h=>
   hn.1 (qM.mp (Yg as (x/2) h))
  dsimp[Z3L]
  split_ifs with hx
  · rw[sum_insert v0,ih hn.2 (x/2)];simp[Z5f,hx]
  · simp[Z5f,hx,ih hn.2 (x/2)]
def Q5 (fuel t:Nat):Nat:=
 match fuel with
 | 0=>0
 | fuel+1=>if beq t 0 then 0 else 1+Q5 fuel (sr t 1)
def Z3n (n:Nat):Nat:=
 if n≤ 1 then 1 else Q5 16 (n-1)
def Z1J:LN->Nat->Nat
 | [],_=>0
 | i :: is,g=>(if g % 2=1 then 2 ^ i else 0)|||Z1J is (g/2)
def Z3o:LN->Nat->Nat
 | _,0=>0
 | [],_=>0
 | p :: ps,g=>
  let rest:=Z3o ps (sr g 1)
  match land g 1 with
  | 0=>rest
  | _+1=>p+rest
lemma Z3o_eq_orig:∀ (ps:LN) (g:Nat),
 Z3o ps g=match ps with|[]=>0|p :: ps'=>(if g % 2==1 then p else 0)+Z3o ps' (g/2)
 | [],0=>rfl
 | [],g+1=>rfl
 | p :: ps,0=>by simp[Z3o]
 | p :: ps,g+1=>by
  change (let rest:=Z3o ps ((g+1)>>> 1)
   match (g+1)&&& 1 with|0=>rest|_ + 1=>p+rest)=_
  rw[qSr,pow_one,and_one_is_mod]
  cases h:(g+1)% 2 with
  | zero=>simp
  | succ k=>
   have hk:k=0:=by have:=mod_lt (g+1) (by omega:0 < 2);omega
   subst hk;simp
def bO:Nat->Nat->Nat->LN
 | 0,_,_=>[]
 | _+1,_,0=>[]
 | fuel+1,i,m+1=>if beq (land (m+1) 1) 1 then i :: bO fuel (i+1) (sr (m+1) 1) else bO fuel (i+1) (sr (m+1) 1)
def Z1K (n m:Nat):LN:=bO n 0 m
lemma Z8:∀ (is:LN) (x a:Nat),
 (Z1J is x).testBit a=true->a∈is
 | [],_,a,ha=>by simp[Z1J] at ha
 | i :: is,x,a,ha=>by
  dsimp[Z1J] at ha;rw[Nat.testBit_or,qOr] at ha;rcases ha with h1|h2
  · split_ifs at h1
    · rw[qk] at h1;exact (of_decide_eq_true h1)▸ qG
    · simp at h1
  · exact qO i (Z8 is (x/2) a h2)
lemma Z3:∀ (is:LN),is.Nodup->∀ (x:Nat),
 Z3o (is.map (fun i=>2 ^ i)) x=Z1J is x
 | [],_,x=>by rw[List.map_nil,Z3o_eq_orig];simp[Z1J]
 | i :: is,hnd,x=>by
  rw[q4] at hnd;have ih:=Z3 is hnd.2 (x/2);rw[List.map_cons,Z3o_eq_orig];dsimp[Z1J];rw[ih];by_cases hm:x % 2=1
  · simp only[hm,qBs,↓reduceIte]
    have v0:(Z1J is (x/2)).testBit i=false:=by
     cases htb:(Z1J is (x/2)).testBit i
     · rfl
     · exact False.elim (hnd.1 (Z8 is (x/2) i htb))
    rw[Nat.add_comm];apply q8;intro a;rw[ZF i _ a v0,Nat.testBit_or,qk];simp[eq_comm]
  · simp[hm,beq_false_of_ne hm]
lemma Q6 (f:Fin 12->Fin 12):∀ (ms:LF) (x:Nat),
 Z3L (ms.map f) x=(Z3L ms x).image f
 | [],_=>by simp[Z3L]
 | a :: as,x=>by
  rw[List.map_cons];dsimp[Z3L];split_ifs
  · rw[image_insert,Q6 f as (x/2)]
  · exact Q6 f as (x/2)
lemma Xu (ms:LF) {i:Nat} (hi:i < ms.length):
 Z3L ms (2 ^ i)={ms.get ⟨i,hi⟩}:=by
 ext a;rw[Y8,qb];constructor
 · rintro ⟨j,hj,rfl⟩
   rw[qk] at hj;have v1:i=j.val:=of_decide_eq_true hj;have v0:(⟨i,hi⟩:Fin ms.length)=j:=Fin.ext v1;rw[← v0]
 · intro ha;subst ha;refine ⟨⟨i,hi⟩,?_,rfl⟩;simp
lemma Zu (ms:LF):
 ∀ (idxs:LN),(∀ i∈idxs,i < ms.length)->∀ (g:Nat),
  Z3L (idxs.map (fun i=>ms.getD i 0)) g=Z3L ms (Z1J idxs g)
 | [],_,g=>by simp[Z3L,Z1J,Xr]
 | i :: is,hlt,g=>by
  have hi:i < ms.length:=hlt i qG;have v1:∀ j∈is,j < ms.length:=fun j hj=>hlt j (qO i hj);have ih:=Zu ms is v1 (g/2)
  have v0:ms.getD i 0=ms.get ⟨i,hi⟩:=by simp[getD_eq_getElem?_getD,hi]
  rw[List.map_cons];dsimp[Z3L,Z1J];rw[Q3,← ih]
  split_ifs with hg
  · rw[v0,Xu ms hi,insert_eq]
  · rw[Xr,empty_union]
lemma Z_ (ms ks:LF):∀ (g:Nat),g < 2 ^ ms.length->
 Z3L (ms++ks) g=Z3L ms g
 | g,hg=>by
  induction ms generalizing g with
  | nil=>simp at hg;subst hg;simp[Xr]
  | cons a as ih=>
   have v0:g/2 < 2 ^ as.length:=by
    dsimp at hg;rw[qW,qY] at hg;exact div_lt_of_lt_mul hg
   dsimp only[List.cons_append,Z3L];split_ifs
   · rw[ih (g/2) v0]
   · exact ih (g/2) v0
lemma Yh (ms ks:LF) (x:Nat):
 Z3L (ms++ks) x=Z3L ms x∪Z3L ks (x/2 ^ ms.length):=by
 induction ms generalizing x with
 | nil=>simp[Z3L]
 | cons a as ih=>
  dsimp only[List.cons_append,Z3L]
  have v0:x/2/2 ^ as.length=x/2 ^ (as.length+1):=by rw[Nat.div_div_eq_div_mul,qY,← qW]
  split_ifs
  · rw[ih (x/2),v0,insert_union,List.length_cons]
  · rw[ih (x/2),v0,List.length_cons]
lemma Xv (ks:LF):
 Z3L ks (2 ^ ks.length-1)=ks.toFinset:=by
 induction ks with
 | nil=>simp[Z3L]
 | cons a as ih=>
  have hp:1≤ 2 ^ as.length:=Nat.one_le_pow _ _ (by omega)
  have v1:(2 ^ (as.length+1)-1)% 2=1:=by
   rw[qW,qY];omega
  have v0:(2 ^ (as.length+1)-1)/2=2 ^ as.length-1:=by
   rw[qW,qY];omega
  dsimp[Z3L];rw[if_pos v1,v0,ih,List.toFinset_cons]
lemma Z9:∀ (i n m x:Nat),i < n->
 (x+m*2 ^ n).testBit i=x.testBit i
 | 0,n+1,m,x,_=>by
  simp only[testBit_zero];rw[qW,← Nat.mul_assoc,Nat.add_mul_mod_self_right]
 | i+1,n+1,m,x,hi=>by
  rw[qm,qm];rw[qW,← Nat.mul_assoc,Nat.add_mul_div_right _ _ (by omega)];exact Z9 i n m (x/2) (by omega)
lemma Zv (ms ks:LF) {x:Nat} (hx:x < 2 ^ ms.length):
 Z3L (ms++ks) (x+(2 ^ ks.length-1)*2 ^ ms.length)=
  Z3L ms x∪ks.toFinset:=by
 rw[Yh]
 have h1:Z3L ms (x+(2 ^ ks.length-1)*2 ^ ms.length)=Z3L ms x:=by
  ext b;simp only[Y8]
  constructor<;>rintro ⟨i,hi,rfl⟩<;>refine ⟨i,?_,rfl⟩
  · rw[Z9 _ _ _ _ i.isLt] at hi;exact hi
  · rw[Z9 _ _ _ _ i.isLt];exact hi
 have h2:(x+(2 ^ ks.length-1)*2 ^ ms.length)/2 ^ ms.length=2 ^ ks.length-1:=by rw[Nat.add_mul_div_right _ _ (two_pow_pos _),Nat.div_eq_of_lt hx,zero_add]
 rw[h1,h2,Xv]
lemma ZJ {ms ks:LF} (hn:(ms++ks).Nodup) {x:Nat}
 (hx:x < 2 ^ ms.length):
 (Z3L (ms++ks) (x+(2 ^ ks.length-1)*2 ^ ms.length)).card=
  ks.length+(Z3L ms x).card:=by
 rw[Zv ms ks hx]
 have hd:Disjoint (Z3L ms x) ks.toFinset:=by
  rw[disjoint_left];intro a ham hak;have h1:a∈ms:=qM.mp (Yg ms x ham);have h2:a∈ks:=qM.mp hak;rw[qV] at hn;exact hn.2.2 a h1 a h2 rfl
 rw[qCu hd,qT (qV.mp hn).2.1,
  add_comm]
structure bS where
 words:LN
 w9:Nat
 l9:Nat
 cWd:Nat
 bLf:Nat
def bS.init:LN->bS
 | []=>⟨[],0,0,0,0⟩
 | w :: ws=>⟨ws,sr w 60,900,land w 0xfffffffffffffff,60⟩
def bS.rB1 (bs:bS):Nat × bS:=
 if ble 1 bs.bLf then
  (land bs.cWd 1,⟨bs.words,bs.w9,bs.l9,sr bs.cWd 1,bs.bLf-1⟩)
 else if ble 1 bs.l9 then
  let c:=land bs.w9 0xfffffffffffffff
  (land c 1,⟨bs.words,sr bs.w9 60,bs.l9-60,sr c 1,59⟩)
 else
  match bs.words with
  | w :: ws=>
   let c:=land w 0xfffffffffffffff
   (land c 1,⟨ws,sr w 60,900,sr c 1,59⟩)
  | []=>(0,⟨[],0,0,0,0⟩)
def bS.rB:Nat->bS->Nat × bS
 | 0,bs=>(0,bs)
 | n+1,bs=>
  let k:=n+1
  if ble k bs.bLf then
   let p:=sl 1 k
   (land bs.cWd (p-1),⟨bs.words,bs.w9,bs.l9,sr bs.cWd k,bs.bLf-k⟩)
  else
   let (b,bs1):=bs.rB1;let (rest,bs2):=rB n bs1
   (b+2*rest,bs2)
def Z3p:Nat->Nat->LN
 | 0,_=>[]
 | r+1,c=>(land c 7):: Z3p r (sr c 3)
def Z3N:LF->Fin 12->Option Nat
 | [],_=>none
 | m :: ms,a=>if a=m then some 0 else (Z3N ms a).map (·+1)
lemma Xw:∀ (ms:LF) (a:Fin 12),
 Z3N ms a=none↔a∉ms
 | [],_=>by simp[Z3N]
 | m :: ms,a=>by
  dsimp[Z3N]
  split_ifs with h
  · subst h;simp
  · simp[Xw ms a,h]
lemma Q7:∀ (ms:LF),ms.Nodup->∀ (i:Nat) (hi:i < ms.length),
 Z3N ms ms[i]=some i
 | [],_,_,hi=>by simp at hi
 | m :: ms,hn,0,_=>by simp[Z3N]
 | m :: ms,hn,i+1,hi=>by
  rw[q4] at hn;dsimp[Z3N]
  have v0:i < ms.length:=by simpa using hi
  have v1:ms[i]≠m:=fun h=>hn.1 (h ▸ qd v0);rw[if_neg v1,Q7 ms hn.2 i v0];rfl
def Z4r (ms:LF) (p:LN) (a:Fin 12):Fin 12:=
 match Z3N ms a with
 | none=>a
 | some i=>ms.getD (p.getD i 0) 0
def Z3O (r:Nat) (p:LN):Bool:=
 p.length==r&&p.Nodup&&p.all (· < r)
lemma Xx (ms:LF) (p:LN) {a:Fin 12} (ha:a∉ms):
 Z4r ms p a=a:=by
 rw[Z4r,(Xw ms a).mpr ha]
lemma Q8 (ms:LF) (hn:ms.Nodup) (p:LN)
 (hpLen:p.length=ms.length) (hpLt:∀ j∈p,j < ms.length)
 {a:Fin 12} (ha:a∈ms):
 ∃ i:Fin ms.length,ms[i.val]=a∧
  ∃ hpi:p.getD i.val 0 < ms.length,Z4r ms p a=ms[p.getD i.val 0]'hpi:=by
 obtain ⟨i,rfl⟩:=List.mem_iff_get.mp ha
 have hi:i.val < p.length:=by rw[hpLen];exact i.isLt
 have v2:p.getD i.val 0∈p:=by
  rw[getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,qt];exact qd hi
 have v0:p.getD i.val 0 < ms.length:=hpLt _ v2;refine ⟨i,rfl,v0,?_⟩;have v1:Z3N ms ms[i.val]=some i.val:=Q7 ms hn i.val i.isLt;simp only[Z4r,List.get_eq_getElem,v1];rw[getD_eq_getElem?_getD,List.getElem?_eq_getElem v0,qt]
lemma Z1L (ms:LF) (hn:ms.Nodup) (p:LN)
 (hnp:p.Nodup) (hpLen:p.length=ms.length) (hpLt:∀ j∈p,j < ms.length):
 Function.Injective (Z4r ms p):=by
 intro a b hab
 by_cases ha:a∈ms<;>by_cases hb:b∈ms
 · obtain ⟨ia,haeq,hpia,hea⟩:=Q8 ms hn p hpLen hpLt ha
   obtain ⟨ib,hbeq,hpib,heb⟩:=Q8 ms hn p hpLen hpLt hb;rw[hea,heb] at hab;have v0:p.getD ia.val 0=p.getD ib.val 0:=
    Fin.val_eq_of_eq ((qN.mp hn) (a₁:=⟨p.getD ia.val 0,hpia⟩)
     (a₂:=⟨p.getD ib.val 0,hpib⟩) hab)
   have v2:ia.val < p.length:=by rw[hpLen];exact ia.isLt
   have v1:ib.val < p.length:=by rw[hpLen];exact ib.isLt
   rw[getD_eq_getElem?_getD,List.getElem?_eq_getElem v2,qt,
    getD_eq_getElem?_getD,List.getElem?_eq_getElem v1,qt] at v0
   have v4:(⟨ia.val,v2⟩:Fin p.length)=⟨ib.val,v1⟩:=
    (qN.mp hnp) v0
   have v3:ia=ib:=Fin.ext (congrArg (Fin.val:Fin p.length->Nat) v4);subst v3;rw[← haeq,← hbeq]
 · obtain ⟨_,_,hpia,hea⟩:=Q8 ms hn p hpLen hpLt ha;rw[hea,Xx ms p hb] at hab;exact False.elim (hb (hab ▸ qd hpia))
 · obtain ⟨_,_,hpib,heb⟩:=Q8 ms hn p hpLen hpLt hb;rw[Xx ms p ha,heb] at hab;exact False.elim (ha (hab.symm ▸ qd hpib))
 · rw[Xx ms p ha,Xx ms p hb] at hab;exact hab
noncomputable def Z3P (ms:LF) (hn:ms.Nodup) (p:LN)
 (hv:Z3O ms.length p=true):Equiv.Perm (Fin 12):=
 have h1:p.length=ms.length:=by
  simp only[Z3O,qA,qBi] at hv;exact hv.1.1
 have h2:p.Nodup:=by
  simp only[Z3O,qA,qD] at hv;exact hv.1.2
 have h3:∀ j∈p,j < ms.length:=by
  simp only[Z3O,qA,qE,qD] at hv;exact hv.2
 Equiv.ofBijective (Z4r ms p)
  ((Fintype.bijective_iff_injective_and_card (Z4r ms p)).mpr
   ⟨Z1L ms hn p h2 h1 h3,rfl⟩)
lemma Q9 (ms:LF) (hn:ms.Nodup) (p:LN)
 (hv:Z3O ms.length p=true):
 ms.map (Z3P ms hn p hv)=p.map (fun j=>ms.getD j 0):=by
 have h1:p.length=ms.length:=by
  simp only[Z3O,qA,qBi] at hv;exact hv.1.1
 apply List.ext_getElem (by simp[h1]);intro k hk1 hk2
 have v1:k < ms.length:=by simpa using hk1
 have v2:k < p.length:=by simpa[h1] using hk1
 simp only[ql];have v0:Z3N ms ms[k]=some k:=Q7 ms hn k v1;change Z4r ms p ms[k]=ms.getD p[k] 0;simp[Z4r,v0,getD_eq_getElem?_getD,v2]
lemma ZK (ms:LF) (hn:ms.Nodup) (p:LN)
 (hv:Z3O ms.length p=true) (x:Nat):
 (Z3L ms x).image (Z3P ms hn p hv)=Z3L ms (Z1J p x):=by
 have h3:∀ j∈p,j < ms.length:=by
  simp only[Z3O,qA,qE,qD] at hv;exact hv.2
 rw[← Q6,Q9 ms hn p hv,Zu ms p h3]
lemma Ya (ms:LF) (hn:ms.Nodup) (p:LN)
 (hv:Z3O ms.length p=true) {a:Fin 12} (ha:a∉ms):
 Z3P ms hn p hv a=a:=
 Xx ms p ha
def Z3q (ws p:LN):Bool:=
 (List.range ws.length).all (fun i=>ws.getD i 0==ws.getD (p.getD i 0) 0)
lemma Yi (ms:LF) (hn:ms.Nodup) (wf:WF)
 (p:LN) (hv:Z3O ms.length p=true)
 (hw:Z3q (ms.map wf) p=true):
 ∀ a:Fin 12,wf (Z3P ms hn p hv a)=wf a:=by
 have h1:p.length=ms.length:=by
  simp only[Z3O,qA,qBi] at hv;exact hv.1.1
 have h3:∀ j∈p,j < ms.length:=by
  simp only[Z3O,qA,qE,qD] at hv;exact hv.2
 intro a;by_cases ha:a∈ms
 · obtain ⟨i,haeq,hpi,hea⟩:=Q8 ms hn p h1 h3 ha
   have v0:i.val < (ms.map wf).length:=by simp
   have v2:p.getD i.val 0 < (ms.map wf).length:=by simpa[getD_eq_getElem?_getD] using hpi
   simp only[Z3q,qE,qR,qBi] at hw;have v1:=hw i.val v0;rw[getD_eq_getElem?_getD,List.getElem?_eq_getElem v0,qt,
    getD_eq_getElem?_getD,List.getElem?_eq_getElem v2,qt,
    ql,ql] at v1
   have v3:Z3P ms hn p hv a=ms[p.getD i.val 0]'hpi:=hea;rw[v3,← haeq,v1]
 · rw[Ya ms hn p hv ha]
def Z4Y:Nat->Nat
 | 1=>5|2=>6|3=>6|4=>5|5=>6|6=>7|7=>6|8=>7
 | 9=>6|10=>7|11=>6|12=>6|13=>5|14=>7|16=>5|17=>6
 | 18=>4|20=>6|22=>5|24=>7|25=>3|26=>6|27=>6|28=>5
 | 29=>6|30=>5|31=>6|32=>4|_=>0
def Z3Q:Nat->LN
 | 1=>[7,11,23]|2=>[7,57,58,60]|3=>[7,15,23,56]|4=>[7,25]
 | 5=>[7,57,58]|6=>[7,15,23,39,71]|7=>[15,23,27,39,43,51]
 | 8=>[15,23,39,71]|9=>[7,15,23,39]|10=>[7,15,23,104]
 | 11=>[7,15,56]|12=>[15,23,39]|13=>[7,27,29]|14=>[7,121,122,124]
 | 16=>[15,23,27]|17=>[7,56]|18=>[7,11]|20=>[7,57]
 | 22=>[7,27]|24=>[7,120]|25=>[7]|26=>[15,23,47]
 | 27=>[15,31,47]|28=>[15,23]|29=>[31,47]|30=>[15,31]
 | 31=>[15,51]|32=>[15]|_=>[]
def Z5g (F:SS):Prop:=
 ∃ a∈F,∃ b∈F,∃ c∈F,a≠b∧a≠c∧b≠c∧
  a.card=3∧b.card=3∧c.card=3∧(a∪b∪c).card≤ 5
def Z5h (F:SS):Prop:=
 ∃ a∈F,∃ b∈F,∃ c∈F,∃ d∈F,
  a≠b∧a≠c∧a≠d∧b≠c∧b≠d∧c≠d∧
  a.card=3∧b.card=3∧c.card=3∧d.card=3∧(a∪b∪c∪d).card≤ 6
def Z5s (t:Nat) (F:SS):Prop:=
 Z4Y t≠0∧∃ ms:LF,ms.Nodup∧ms.length=Z4Y t∧
  ∀ g∈Z3Q t,Z3L ms g∈F
def Z3r (t:Nat) (F:SS):Prop:=
 if t=34 then Z5g F else if t=35 then Z5h F else Z5s t F
lemma Z1M (e:Equiv.Perm (Fin 12)) {F:SS}:
 Z5g (F.image (Finset.image e))->Z5g F:=by
 rintro ⟨a,ha,b,hb,c,hc,hab,hac,hbc,ha3,hb3,hc3,hu⟩;obtain ⟨a',ha',rfl⟩:=qI.mp ha;obtain ⟨b',hb',rfl⟩:=qI.mp hb;obtain ⟨c',hc',rfl⟩:=qI.mp hc;refine ⟨a',ha',b',hb',c',hc',fun h=>hab (by rw[h]),fun h=>hac (by rw[h]),
  fun h=>hbc (by rw[h]),?_,?_,?_,?_⟩
 · simpa[qK _ e.injective] using ha3
 · simpa[qK _ e.injective] using hb3
 · simpa[qK _ e.injective] using hc3
 · have v0:(a'.image e∪b'.image e∪c'.image e)=(a'∪b'∪c').image e:=by
    simp[image_union]
   rwa[v0,qK _ e.injective] at hu
lemma Z1N (e:Equiv.Perm (Fin 12)) {F:SS}:
 Z5h (F.image (Finset.image e))->Z5h F:=by
 rintro ⟨a,ha,b,hb,c,hc,d,hd,hab,hac,had,hbc,hbd,hcd,ha3,hb3,hc3,hd3,hu⟩;obtain ⟨a',ha',rfl⟩:=qI.mp ha;obtain ⟨b',hb',rfl⟩:=qI.mp hb;obtain ⟨c',hc',rfl⟩:=qI.mp hc;obtain ⟨d',hd',rfl⟩:=qI.mp hd;refine ⟨a',ha',b',hb',c',hc',d',hd',fun h=>hab (by rw[h]),fun h=>hac (by rw[h]),
  fun h=>had (by rw[h]),fun h=>hbc (by rw[h]),fun h=>hbd (by rw[h]),
  fun h=>hcd (by rw[h]),?_,?_,?_,?_,?_⟩
 · simpa[qK _ e.injective] using ha3
 · simpa[qK _ e.injective] using hb3
 · simpa[qK _ e.injective] using hc3
 · simpa[qK _ e.injective] using hd3
 · have v0:(a'.image e∪b'.image e∪c'.image e∪d'.image e)=(a'∪b'∪c'∪d').image e:=by
    simp[image_union]
   rwa[v0,qK _ e.injective] at hu
lemma Z3s (e:Equiv.Perm (Fin 12)) {t:Nat} {F:SS}:
 Z5s t (F.image (Finset.image e))->Z5s t F:=by
 rintro ⟨hrt,ms,hn,hlen,hg⟩;refine ⟨hrt,ms.map e.symm,hn.map e.symm.injective,by simpa using hlen,?_⟩;intro g hgg;obtain ⟨X,hXF,hXeq⟩:=qI.mp (hg g hgg);rw[Q6,← hXeq]
 have v0:(X.image e).image e.symm=X:=by ext x;simp
 rwa[v0]
lemma Yj (e:Equiv.Perm (Fin 12)) {t:Nat} {F:SS}:
 Z3r t (F.image (Finset.image e))->Z3r t F:=by
 dsimp[Z3r];split_ifs
 · exact Z1M e
 · exact Z1N e
 · exact Z3s e
def Z3R (n t:Nat) (ws:LN):LN:=
 let v0:=Z4X n;let v1:=Z5r n;let v2:=Z5p
 match t,ws with
 | 1,[w0,w1,w2]=>
  Z1K n (v1 w0 w1)++Z1K n (v0 w0 w1)++
   Z1K n (v0 w1 w0)++Z1K n (v0 w2 (v2 w0 w1))
 | 2,[w0,w1,w2,w3]=>
  Z1K n (v1 w0 w1)++Z1K n (v1 w0 w2)++
   Z1K n (v1 w0 w3)++Z1K n (v0 w1 w0)
 | 3,[w0,w1,w2,w3]=>
  let d1:=v0 w1 w0;let d2:=v0 w2 w0
  Z1K n w0++Z1K n d1++Z1K n d2++Z1K n (v0 w3 (v2 d1 d2))
 | 4,[w0,w1]=>
  let p:=v1 w0 w1
  Z1K n p++Z1K n (v0 w0 p)++Z1K n (v0 w1 p)
 | 5,[w0,w1,w2]=>
  let p1:=v1 w0 w1;let p2:=v1 w0 w2
  Z1K n p1++Z1K n p2++Z1K n (v0 w0 (v2 p1 p2))++Z1K n (v0 w1 p1)
 | 6,[w0,w1,w2,w3,w4]=>
  Z1K n w0++Z1K n (v0 w1 w0)++Z1K n (v0 w2 w0)++
   Z1K n (v0 w3 w0)++Z1K n (v0 w4 w0)
 | 7,w0 :: w1 :: _=>
  let p:=v1 w0 w1;let u:=v2 w0 w1
  Z1K n p++Z1K n (v0 u p)
 | 8,[w0,w1,w2,w3]=>
  let tl:=v1 w0 w1
  Z1K n tl++Z1K n (v0 w0 tl)++Z1K n (v0 w1 tl)++
   Z1K n (v0 w2 tl)++Z1K n (v0 w3 tl)
 | 9,[w0,w1,w2,w3]=>Z1K n w0++Z1K n (v0 w1 w0)++Z1K n (v0 w2 w0)++Z1K n (v0 w3 w0)
 | 10,[w0,w1,w2,w3]=>
  let d1:=v0 w1 w0;let d2:=v0 w2 w0
  Z1K n w0++Z1K n d1++Z1K n d2++Z1K n (v0 w3 d1)
 | 11,[w0,w1,w2]=>
  let d:=v0 w1 w0
  Z1K n w0++Z1K n d++Z1K n (v0 w2 d)
 | 12,[w0,w1,w2]=>
  let tl:=v1 w0 w1
  Z1K n tl++Z1K n (v0 w0 tl)++Z1K n (v0 w1 tl)++Z1K n (v0 w2 tl)
 | 13,[w0,w1,w2]=>
  let p:=v1 (v1 w0 w1) w2
  Z1K n p++Z1K n (v0 (v1 w0 w1) p)++Z1K n (v0 (v1 w0 w2) p)++
   Z1K n (v0 w1 (v1 w0 w1))
 | 14,[w0,w1,w2,w3]=>
  Z1K n (v1 w0 w1)++Z1K n (v1 w0 w2)++Z1K n (v1 w0 w3)++
   Z1K n (v0 w1 w0)
 | 16,[w0,w1,w2]=>
  let u:=v2 w0 w1;let c:=v1 (v1 w0 w1) w2
  Z1K n c++Z1K n (v0 u w2)++Z1K n (v0 u w1)++Z1K n (v0 u w0)
 | 17,[w0,w1]=>Z1K n w0++Z1K n w1
 | 18,[w0,w1]=>let p:=v1 w0 w1;Z1K n p++Z1K n (v0 w0 p)++Z1K n (v0 w1 p)
 | 20,[w0,w1]=>let p:=v1 w0 w1;Z1K n p++Z1K n (v0 w0 p)++Z1K n (v0 w1 p)
 | 22,[w0,w1]=>let p:=v1 w0 w1;Z1K n p++Z1K n (v0 w0 p)++Z1K n (v0 w1 p)
 | 24,[w0,w1]=>Z1K n w0++Z1K n w1
 | 25,[w0]=>Z1K n w0
 | 26,[w0,w1,w2]=>
  let p:=v1 w0 w1
  Z1K n p++Z1K n (v0 w0 p)++Z1K n (v0 w1 p)++Z1K n (v0 w2 w0)
 | 27,[w0,w1,w2]=>Z1K n w0++Z1K n (v0 w1 w0)++Z1K n (v0 w2 w0)
 | 28,[w0,w1]=>let p:=v1 w0 w1;Z1K n p++Z1K n (v0 w0 p)++Z1K n (v0 w1 p)
 | 29,[w0,w1]=>let p:=v1 w0 w1;Z1K n p++Z1K n (v0 w0 p)++Z1K n (v0 w1 p)
 | 30,[w0,w1]=>Z1K n w0++Z1K n (v0 w1 w0)
 | 31,[w0,w1]=>let p:=v1 w0 w1;Z1K n p++Z1K n (v0 w0 p)++Z1K n (v0 w1 p)
 | 32,[w0]=>Z1K n w0
 | _,_=>[]
def Yk (n rj:Nat) (idxs ws gS:LN):Bool:=
 rj != 0&&idxs.length==rj&&idxs.Nodup&&idxs.all (· < n)&&
  gS.all (fun g=>ws.contains (Z1J idxs g))
def Z3t (r k:Nat) (gS Gs:LN) (idx:Nat):Option Nat:=
 if idx < gS.length then gS[idx]?
 else (Gs[idx-gS.length]?).map (fun a=>a+(2 ^ k-1)*2 ^ r)
def Z1O (r k:Nat) (gS Gs:LN):LN->Option (LN)
 | []=>some []
 | idx :: rest=>
  match Z3t r k gS Gs idx,Z1O r k gS Gs rest with
  | some w,some ws=>some (w :: ws)
  | _,_=>none
def VL (r k mS:Nat) (gS Gs:LN) (t:Nat) (wi:LN):Bool:=
 if t==0 then
  match wi with
  | [idx]=>
   if gS.length≤ idx then
    match Gs[idx-gS.length]? with
    | some a=>!(k==0&&a==0)&&k+Z5o r a < mS
    | none=>false
   else false
  | _=>false
 else
  match Z1O r k gS Gs wi with
  | none=>false
  | some ws=>
   let n:=r+k
   if t==34 then
    match ws with
    | [w0,w1,w2]=>
     w0 != w1&&w0 != w2&&w1 != w2&&
      Z5o n w0==3&&Z5o n w1==3&&Z5o n w2==3&&
      Z5o n (Z5p (Z5p w0 w1) w2)≤ 5
    | _=>false
   else if t==35 then
    match ws with
    | [w0,w1,w2,w3]=>
     w0 != w1&&w0 != w2&&w0 != w3&&w1 != w2&&w1 != w3&&w2 != w3&&
      Z5o n w0==3&&Z5o n w1==3&&Z5o n w2==3&&Z5o n w3==3&&
      Z5o n (Z5p (Z5p (Z5p w0 w1) w2) w3)≤ 6
    | _=>false
   else
    let v0:=Z3R n t ws
    Yk n (Z4Y t) v0 ws (Z3Q t)
lemma Yl {F:SS} {ms ks:LF}
 {gS Gs:LN}
 (hg_lt:∀ g∈gS,g < 2 ^ ms.length)
 (hgF:∀ g∈gS,Z3L ms g∈F)
 (hGs_lt:∀ a∈Gs,a < 2 ^ ms.length)
 (hGsF:∀ a∈Gs,Z3L ms a∪ks.toFinset∈F)
 {idx w:Nat} (hlook:Z3t ms.length ks.length gS Gs idx=some w):
 w < 2 ^ (ms++ks).length∧Z3L (ms++ks) w∈F:=by
 dsimp[Z3t] at hlook;have v5:1≤ 2 ^ ks.length:=Nat.one_le_pow _ _ (by omega)
 have v0:2 ^ (ms++ks).length=2 ^ ms.length*2 ^ ks.length:=by simp[pow_add]
 split_ifs at hlook with hlt
 · have hg:w∈gS:=by
    have v4:=qd hlt;rw[List.getElem?_eq_getElem hlt,Option.some.injEq] at hlook;exact hlook ▸ v4
   have v1:=hg_lt w hg
   have v2:2 ^ ms.length≤ 2 ^ (ms++ks).length:=by
    rw[v0];exact Nat.le_mul_of_pos_right _ v5
   refine ⟨qLt v1 v2,?_⟩;rw[Z_ ms ks w v1];exact hgF w hg
 · cases hG:Gs[idx-gS.length]? with
   | none=>simp[hG] at hlook
   | some a=>
    simp only[hG,Option.map_some,Option.some.injEq] at hlook;have ha:a∈Gs:=mem_of_getElem? hG;have v3:=hGs_lt a ha;rw[← hlook];refine ⟨?_,?_⟩
    · rw[v0];have h1:a+(2 ^ ks.length-1)*2 ^ ms.length <
       2 ^ ms.length+(2 ^ ks.length-1)*2 ^ ms.length:=by omega
      have h2:2 ^ ms.length+(2 ^ ks.length-1)*2 ^ ms.length=
       2 ^ ms.length*2 ^ ks.length:=by
       calc 2 ^ ms.length+(2 ^ ks.length-1)*2 ^ ms.length
        = 1*2 ^ ms.length+(2 ^ ks.length-1)*2 ^ ms.length:=by rw[qZ]
        _=(1+(2 ^ ks.length-1))*2 ^ ms.length:=by rw[← Nat.add_mul]
        _=2 ^ ks.length*2 ^ ms.length:=by rw[show 1+(2 ^ ks.length-1)=2 ^ ks.length by omega]
        _=2 ^ ms.length*2 ^ ks.length:=qY _ _
      omega
    · rw[Zv ms ks v3];exact hGsF a ha
lemma Yb {F:SS} {ms ks:LF}
 {gS Gs:LN}
 (hg_lt:∀ g∈gS,g < 2 ^ ms.length)
 (hgF:∀ g∈gS,Z3L ms g∈F)
 (hGs_lt:∀ a∈Gs,a < 2 ^ ms.length)
 (hGsF:∀ a∈Gs,Z3L ms a∪ks.toFinset∈F):
 ∀ {wi ws:LN},Z1O ms.length ks.length gS Gs wi=some ws->
  ∀ w∈ws,w < 2 ^ (ms++ks).length∧Z3L (ms++ks) w∈F
 | [],_,h=>by simp[Z1O] at h;subst h;intro w hw;simp at hw
 | idx :: rest,ws,h=>by
  dsimp[Z1O] at h;cases hl1:Z3t ms.length ks.length gS Gs idx with
  | none=>simp[hl1] at h
  | some w0=>
   cases hl2:Z1O ms.length ks.length gS Gs rest with
   | none=>simp[hl1,hl2] at h
   | some ws'=>
    simp only[hl1,hl2,Option.some.injEq] at h;subst h;intro w hw;rcases qC.mp hw with rfl|hw'
    · exact Yl hg_lt hgF hGs_lt hGsF hl1
    · exact Yb hg_lt hgF hGs_lt hGsF hl2 w hw'
lemma Zj {l:LF} (hn:l.Nodup):l.length≤ 12:=by have h1:=qT hn;have h2:l.toFinset.card≤ Fintype.card (Fin 12):=card_le_univ _;simpa using h1 ▸ h2
lemma Y0 {F:SS} {ms ks:LF}
 (hn:(ms++ks).Nodup) {gS Gs:LN} {mS t:Nat} {wi:LN}
 (hg_lt:∀ g∈gS,g < 2 ^ ms.length)
 (hgF:∀ g∈gS,Z3L ms g∈F)
 (hGs_lt:∀ a∈Gs,a < 2 ^ ms.length)
 (hGsF:∀ a∈Gs,Z3L ms a∪ks.toFinset∈F)
 (hlow:∀ X∈F,X.Nonempty->mS≤ X.card)
 (jA:VL ms.length ks.length mS gS Gs t wi=true):
 t≠0∧Z3r t F:=by
 have v7:ms.Nodup:=(qV.mp hn).1
 have v1:2 ^ (ms++ks).length≤ 4096:=by
  have hle:=Zj hn;simpa using qPl (by omega:0 < 2) hle
 by_cases ht0:t=0
 · subst ht0;exfalso;simp only[VL,qBs,↓reduceIte] at jA
   rcases wi with _|⟨idx,_|_⟩<;>simp at jA
   have ⟨_,jA'⟩:=jA;cases hG:Gs[idx-gS.length]? with
   | none=>simp[hG] at jA'
   | some a=>
    simp only[hG,qA,qOr,Bool.not_eq_true',
     beq_eq_false_iff_ne,ne_eq,qD] at jA'
    have ha:a∈Gs:=mem_of_getElem? hG;have v9:a < 2 ^ ms.length:=hGs_lt a ha;have hXF:Z3L ms a∪ks.toFinset∈F:=hGsF a ha
    have v8:(Z3L ms a∪ks.toFinset).card=ks.length+Z5o ms.length a:=by
     have:=ZJ hn v9;rw[Zv ms ks v9] at this;simpa[Xs ms v7 a] using this
    have hne:(Z3L ms a∪ks.toFinset).Nonempty:=by
     by_cases hk0:ks.length=0
     · have ha0:a≠0:=by
        rcases jA'.1 with h|h;exact False.elim (h hk0);exact h
       rw[← qr,v8,hk0,zero_add];rw[← Xs ms v7 a,qr,qNe];intro he;apply ha0;exact Q2 ms v7 v9 (two_pow_pos _) (he.trans (Xr ms).symm)
     · rw[← qr,v8];omega
    have hge:=hlow _ hXF hne;omega
 · refine ⟨ht0,?_⟩
   have htb:(t==0)=false:=beq_false_of_ne ht0;simp only[VL,htb,qFl,↓reduceIte] at jA;cases hlook:Z1O ms.length ks.length gS Gs wi with
   | none=>simp[hlook] at jA
   | some ws=>
    simp only[hlook] at jA;have hws:=Yb hg_lt hgF hGs_lt hGsF hlook;have v0:(ms++ks).length=ms.length+ks.length:=List.length_append;by_cases ht34:t=34
    · subst ht34;simp only[qBs,↓reduceIte] at jA
      rcases ws with _|⟨w0,_|⟨w1,_|⟨w2,_|_⟩⟩⟩<;>try (simp at jA;done)
      simp only[qA,bne_iff_ne,ne_eq,qBi,qD] at jA;have ⟨h0l,h0F⟩:=hws w0 (by simp);have ⟨h1l,h1F⟩:=hws w1 (by simp);have ⟨h2l,h2F⟩:=hws w2 (by simp);have v4:w0 < 4096:=qLt h0l v1;have v3:w1 < 4096:=qLt h1l v1;have v5:w2 < 4096:=qLt h2l v1;have v2:w0|||w1 < 4096:=q5 (n:=12) v4 v3
      have v6:Z5p (Z5p w0 w1) w2=w0|||w1|||w2:=by rw[Z1I v4 v3,Z1I v2 v5]
      refine (if_pos rfl).mpr ?_;refine ⟨Z3L (ms++ks) w0,h0F,Z3L (ms++ks) w1,h1F,
       Z3L (ms++ks) w2,h2F,?_,?_,?_,?_,?_,?_,?_⟩
      · intro heq;exact jA.1.1.1.1.1.1 (Q2 _ hn h0l h1l heq)
      · intro heq;exact jA.1.1.1.1.1.2 (Q2 _ hn h0l h2l heq)
      · intro heq;exact jA.1.1.1.1.2 (Q2 _ hn h1l h2l heq)
      · rw[Xs _ hn w0,v0];exact jA.1.1.1.2
      · rw[Xs _ hn w1,v0];exact jA.1.1.2
      · rw[Xs _ hn w2,v0];exact jA.1.2
      · rw[← Q3,← Q3,Xs _ hn,v0,← v6];exact jA.2
    · by_cases ht35:t=35
      · subst ht35;simp only[show (35==34)=false by decide,qFl,↓reduceIte,
         qBs] at jA
        rcases ws with _|⟨w0,_|⟨w1,_|⟨w2,_|⟨w3,_|_⟩⟩⟩⟩<;>try (simp at jA;done)
        simp only[qA,bne_iff_ne,ne_eq,qBi,qD] at jA;have ⟨h0l,h0F⟩:=hws w0 (by simp);have ⟨h1l,h1F⟩:=hws w1 (by simp);have ⟨h2l,h2F⟩:=hws w2 (by simp);have ⟨h3l,h3F⟩:=hws w3 (by simp);have v4:w0 < 4096:=qLt h0l v1;have v3:w1 < 4096:=qLt h1l v1;have v5:w2 < 4096:=qLt h2l v1;have v13:w3 < 4096:=qLt h3l v1;have v2:w0|||w1 < 4096:=q5 (n:=12) v4 v3;have v10:w0|||w1|||w2 < 4096:=q5 (n:=12) v2 v5
        have v6:Z5p (Z5p (Z5p w0 w1) w2) w3=w0|||w1|||w2|||w3:=by rw[Z1I v4 v3,Z1I v2 v5,Z1I v10 v13]
        rw[Z3r,if_neg (by omega),if_pos rfl];refine ⟨Z3L (ms++ks) w0,h0F,Z3L (ms++ks) w1,h1F,
         Z3L (ms++ks) w2,h2F,Z3L (ms++ks) w3,h3F,
         ?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
        · intro heq;exact jA.1.1.1.1.1.1.1.1.1.1 (Q2 _ hn h0l h1l heq)
        · intro heq;exact jA.1.1.1.1.1.1.1.1.1.2 (Q2 _ hn h0l h2l heq)
        · intro heq;exact jA.1.1.1.1.1.1.1.1.2 (Q2 _ hn h0l h3l heq)
        · intro heq;exact jA.1.1.1.1.1.1.1.2 (Q2 _ hn h1l h2l heq)
        · intro heq;exact jA.1.1.1.1.1.1.2 (Q2 _ hn h1l h3l heq)
        · intro heq;exact jA.1.1.1.1.1.2 (Q2 _ hn h2l h3l heq)
        · rw[Xs _ hn w0,v0];exact jA.1.1.1.1.2
        · rw[Xs _ hn w1,v0];exact jA.1.1.1.2
        · rw[Xs _ hn w2,v0];exact jA.1.1.2
        · rw[Xs _ hn w3,v0];exact jA.1.2
        · rw[← Q3,← Q3,← Q3,Xs _ hn,
           v0,← v6]
          exact jA.2
      · have v16:(t==34)=false:=beq_false_of_ne ht34;have v19:(t==35)=false:=beq_false_of_ne ht35;simp only[v16,v19,qFl,↓reduceIte,Yk,
         qA,bne_iff_ne,ne_eq,qBi,qE,
         qD,qCm] at jA
        rw[Z3r,if_neg ht34,if_neg ht35];set idxs:=Z3R (ms.length+ks.length) t ws;have hlt:∀ i∈idxs,i < (ms++ks).length:=fun i hi=>v0 ▸ jA.1.2 i hi;let ms':=idxs.map (fun i=>(ms++ks).getD i 0)
        have v20:ms'.Nodup:=by
         rw[qN];intro a b hab
         have ha:a.val < idxs.length:=by simpa[ms'] using a.isLt
         have hb:b.val < idxs.length:=by simpa[ms'] using b.isLt
         have hai:idxs[a.val]< (ms++ks).length:=hlt _ (qd ha);have hbi:idxs[b.val]< (ms++ks).length:=hlt _ (qd hb);simp only[ms',ql,getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hai,List.getElem?_eq_getElem hbi,qt] at hab
         have v18:idxs[a.val]=idxs[b.val]:=
          Fin.val_eq_of_eq ((qN.mp hn)
           (a₁:=⟨idxs[a.val],hai⟩) (a₂:=⟨idxs[b.val],hbi⟩) hab)
         have v17:=Fin.val_eq_of_eq ((qN.mp jA.1.1.2)
          (a₁:=⟨a.val,ha⟩) (a₂:=⟨b.val,hb⟩) v18)
         exact Fin.ext v17
        refine ⟨jA.1.1.1.1,ms',v20,by simp[ms',jA.1.1.1.2],?_⟩;intro g hg;have v12:Z1J idxs g∈ws:=jA.2 g hg;rw[Zu (ms++ks) idxs hlt g];exact (hws _ v12).2
def Z4Z (k wo:Nat) (ws:LN) (x:Nat):Nat:=
 2*(k*wo+Z5f ws x)
structure Z4_ where
 G:Nat
 Gs:LN
 cP:Nat
 cC:Nat
 rM:Nat
 rS:Nat
lemma Z5o_zero:∀ n,Z5o n 0=0
 | 0=>rfl
 | n+1=>by simp[Z5o,Z5o_zero n]
lemma Z5f_zero:∀ ws,Z5f ws 0=0
 | []=>rfl
 | _ :: ws=>by simp[Z5f,Z5f_zero ws]
lemma Z5f_le_sum:∀ (ws:LN) (x:Nat),Z5f ws x≤ ws.sum
 | [],_=>by simp[Z5f]
 | w :: ws,x=>by have:=Z5f_le_sum ws (x/2);simp[Z5f];split_ifs<;>omega
def zOo:Nat->Nat->Nat
 | 0,_=>0
 | _+1,0=>0
 | n+1,x+1=>land (x+1) 1+zOo n (sr (x+1) 1)
lemma z5o:∀ n x,zOo n x=Z5o n x
 | 0,0=>rfl
 | 0,x+1=>rfl
 | n+1,0=>by simp[zOo,Z5o_zero]
 | n+1,x+1=>by
  dsimp[zOo,Z5o];rw[z5o n ((x+1)>>> 1)];rw[and_one_is_mod,qSr,pow_one]
def zFf:LN->Nat->Nat
 | [],_=>0
 | _ :: _,0=>0
 | w :: ws,x+1=>
  let r:=zFf ws (sr (x+1) 1)
  if beq (land (x+1) 1) 1 then w+r else r
lemma z5f:∀ ws x,zFf ws x=Z5f ws x
 | [],0=>rfl
 | [],x+1=>rfl
 | w :: ws,0=>by simp[zFf,Z5f_zero]
 | w :: ws,x+1=>by
  dsimp only[zFf,Z5f];rw[z5f ws _]
  have h1:sr (x+1) 1=(x+1)/2:=by change (x+1)>>> 1=_;rw[qSr,pow_one]
  have h2:land (x+1) 1=(x+1)% 2:=and_one_is_mod (x+1);rw[h1];simp only[h2]
  cases h:(x+1)% 2 with
  | zero=>rw[show beq 0 1=false from rfl];simp
  | succ k=>
   have hk:k=0:=by have:=mod_lt (x+1) (by omega:0 < 2);omega
   subst hk;rw[show beq 1 1=true from rfl];simp
def zZf (k wo:Nat) (ws:LN) (x:Nat):Nat:=2*(k*wo+zFf ws x)
lemma z4e (k wo:Nat) (ws:LN) (x:Nat):zZf k wo ws x=Z4Z k wo ws x:=by simp[zZf,Z4Z,z5f]
def mkPv (k wo:Nat) (ws:LN):Nat->Nat
 | 0=>0
 | n+1=>lor (mkPv k wo ws n) (sl (zZf k wo ws n) (sl n 4))
lemma mkPv_eq_rec (k wo:Nat) (ws:LN):∀ n:Nat,
 mkPv k wo ws n=Nat.rec 0 (fun m acc=>lor acc (sl (Z4Z k wo ws m) (16*m))) n
 | 0=>rfl
 | n+1=>by
  dsimp[mkPv];rw[mkPv_eq_rec k wo ws n,z4e];congr 2;change n <<< 4=16*n;rw[qSl];omega
lemma mPt (f:Nat->Nat) (hf:∀ i,f i < 65536):
 ∀ (n:Nat),(Nat.rec 0 (fun m acc=>lor acc (sl (f m) (16*m))) n:Nat)< 2 ^ (16*n):=by
 intro n;induction n with
 | zero=>simp
 | succ n ih=>
  dsimp;apply q5
  · exact qLt ih (qPl (by omega) (by omega))
  · change (f n)<<< (16*n)< 2 ^ (16*(n+1));rw[qSl,Nat.mul_add,pow_add,Nat.mul_one,qY (2 ^ (16*n)) (2 ^ 16)];exact Nat.mul_lt_mul_of_pos_right (hf n) (two_pow_pos _)
lemma mPL (f:Nat->Nat) (hf:∀ i,f i < 65536):
 ∀ (n u:Nat),u < n->
 let tab:=Nat.rec 0 (fun m acc=>lor acc (sl (f m) (16*m))) n
 land (sr tab (sl u 4)) 0xffff=f u:=by
 intro n;induction n with
 | zero=>intro u hu;omega
 | succ n ih=>
  intro u hu;apply q8;intro i;dsimp;change (((Nat.rec 0 (fun m acc=>acc|||f m <<< (16*m)) n|||f n <<< (16*n))>>> (u <<< 4))&&& 0xffff).testBit i=(f u).testBit i;rw[testBit_land,testBit_shiftRight,testBit_lor,testBit_shiftLeft]
  have hshift:u <<< 4=16*u:=by rw[qSl];omega
  rw[hshift];by_cases hi:i < 16
  · have hmask:Nat.testBit 0xffff i=true:=by
     have:(0xffff:Nat)=2 ^ 16-1:=rfl
     rw[this,Nat.testBit_two_pow_sub_one];simp[hi]
    rw[hmask,Bool.and_true];rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hu) with hun|rfl
    · have hlt:¬ (16*n≤ 16*u+i):=by omega
      simp only[hlt,decide_false,Bool.false_and,Bool.or_false]
      have:=ih u hun;have tb:=congrArg (fun x=>Nat.testBit x i) this
      change ((Nat.rec 0 (fun m acc=>acc|||f m <<< (16*m)) n >>> (u <<< 4))&&& 0xffff).testBit i=(f u).testBit i at tb;simpa[testBit_land,testBit_shiftRight,hshift,hmask] using tb
    · have hprev:=mPt f hf u
      have hp1:(Nat.rec 0 (fun m acc=>acc|||f m <<< (16*m)) u:Nat).testBit (16*u+i)=false:=
       qg (qLt hprev (qPl (by omega) (by omega)))
      have hle:16*u≤ 16*u+i:=by omega
      simp[hp1,hle]
  · have h16:16≤ i:=by omega
    have hmask:Nat.testBit 0xffff i=false:=
     qg (qLt (by decide:0xffff < 2 ^ 16) (qPl (by omega) h16))
    have hfi:Nat.testBit (f u) i=false:=
     qg (qLt (hf u) ((by rfl:65536=2 ^ 16)▸ qPl (by omega) h16))
    simp[hmask,hfi]
def zO4 (r k wo:Nat) (ws:LN) (pV:Nat):Prop:=
 ∀ u < 2 ^ r,land (sr pV (sl u 4)) 0xffff=Z4Z k wo ws u
lemma mPo (r k wo:Nat) (ws:LN) (hlt:2*(k*wo+ws.sum)< 65536):
 zO4 r k wo ws (mkPv k wo ws (sl 1 r)):=by
 intro u hu;rw[mkPv_eq_rec];apply mPL (Z4Z k wo ws) (fun i=>by have:=Z5f_le_sum ws i;dsimp[Z4Z];omega)
 change u < 1 <<< r;rw[qSl,qZ];exact hu
def z5a (W pV:Nat) (s:Z4_) (u p:Nat):Z4_:=
 let pv:=land (sr pV (sl u 4)) 0xffff
 if beq (land s.rM p) 0 then ⟨lor s.G p,u :: s.Gs,s.cP+pv,s.cC+1,s.rM,s.rS⟩
 else ⟨lor s.G p,u :: s.Gs,s.cP+pv,s.cC+1,Nat.xor s.rM p,s.rS-(W-pv)⟩
def Z50 (W pV:Nat) (s:Z4_) (u:Nat):Z4_:=
 let p:=sl 1 u
 if beq (land s.G p) 0 then z5a W pV s u p else s
def Z4s (W pV:Nat) (x:Nat):LN->Z4_->Z4_
 | [],s=>s
 | y :: ys,s=>
  let u:=lor x y;let p:=sl 1 u
  if beq (land s.G p) 0 then Z4s W pV x ys (z5a W pV s u p)
  else Z4s W pV x ys s
lemma z4c (W pV x y:Nat) (ys:LN) (s:Z4_):
 Z4s W pV x (y :: ys) s=Z4s W pV x ys (Z50 W pV s (lor x y)):=by
 dsimp[Z4s,Z50];cases beq (land s.G (sl 1 (lor x y))) 0 <;> rfl
def Xy (W pV:Nat) (cg:LN) (s:Z4_) (x:Nat):Z4_:=
 let p:=sl 1 x
 if beq (land s.G p) 0 then
  let s0:=z5a W pV s x p;let s1:=Z4s W pV x cg s0
  Z4s W pV x s.Gs s1
 else s
def Z51 (W pV:Nat) (s:Z4_) (x:Nat):Z4_:=
 let p:=sl 1 x
 if beq (land s.rM p) 0 then s
 else
  let pv:=land (sr pV (sl x 4)) 0xffff
  ⟨s.G,s.Gs,s.cP,s.cC,Nat.xor s.rM p,s.rS-(W-pv)⟩
def Z4t (W pV:Nat):Z4_->LN->Z4_
 | s,[]=>s
 | s,x :: xs=>Z4t W pV (Z51 W pV s x) xs
def Z1P (gS cur:LN):LN:=
 let c1:=cur.foldl (fun acc z=>gS.foldl (fun acc2 g=>
  let u:=or7 z g;if acc2.contains u then acc2 else acc2++[u]) acc) cur
 c1.foldl (fun acc z=>c1.foldl (fun acc2 w=>
  let u:=or7 z w;if acc2.contains u then acc2 else acc2++[u]) acc) c1
def Z4u (gS:LN):LN:=
 let c0:=gS.foldl (fun acc g=>if acc.contains g then acc else acc++[g]) []
 Z1P gS (Z1P gS c0)
def Z4v (r:Nat) (gS cg:LN):Bool:=
 r≤ 7&&cg.all (· < 2 ^ r)&&gS.all (cg.contains ·)&&
  cg.all (fun a=>cg.all (fun b=>cg.contains (or7 a b)))
lemma VM {r:Nat} {gS cg:LN} (h:Z4v r gS cg=true):
 r≤ 7∧(∀ a∈cg,a < 2 ^ r)∧(∀ g∈gS,g∈cg)∧
  (∀ a∈cg,∀ b∈cg,(a|||b)∈cg):=by
 simp only[Z4v,qA,qD,qE,
  qCm] at h
 refine ⟨h.1.1.1,h.1.1.2,h.1.2,?_⟩;intro a ha b hb
 have v0:2 ^ r < 256:=by
  have:2 ^ r≤ 2 ^ 7:=qPl (by omega) h.1.1.1;omega
 have v1:a < 256:=lt_trans (h.1.1.2 a ha) v0;have v2:b < 256:=lt_trans (h.1.1.2 b hb) v0;simpa[Z3m v1 v2] using h.2 a ha b hb
structure Z4d (r k wo W:Nat) (ws:LN) (ms:LF)
 (H:SS) (es:LN) (rP:Nat->Bool)
 (s:Z4_):Prop where
 nd:s.Gs.Nodup
 lt:∀ a∈s.Gs,a < 2 ^ r
 bit:∀ a,s.G.testBit a=true↔a∈s.Gs
 memH:∀ a∈s.Gs,Z3L ms a∈H
 curP_eq:s.cP=(s.Gs.map (Z4Z k wo ws)).sum
 curCnt_eq:s.cC=s.Gs.length
 rem_lt:∀ a,s.rM.testBit a=true->a < 2 ^ r
 rem_spec:∀ a,s.rM.testBit a=true↔(rP a=true∧a∉s.Gs∧a∉es)
 rem_neg:∀ a,rP a=true->Z4Z k wo ws a < W
 remSum_eq:s.rS=
  ∑ a∈(Finset.range (2 ^ r)).filter (fun a=>s.rM.testBit a),(W-Z4Z k wo ws a)
lemma lp0 (M u:Nat):beq (M &&& (1 <<< u)) 0 = !(M.testBit u):=by
 rw[qSl,qZ]
 by_cases h:M.testBit u=true
 · have hne:(M &&& 2 ^ u)≠0:=fun hz=>by
    have ht:(M &&& 2 ^ u).testBit u=true:=by rw[Nat.testBit_and,h,qk];simp
    rw[hz] at ht;simp at ht
   cases hb:(M &&& 2 ^ u).beq 0 with
   | false=>simp[h]
   | true=>exact False.elim (hne (beq_eq.mp hb))
 · have hff:M.testBit u=false:=qEf.mpr h
   have heq:(M &&& 2 ^ u)=0:=q8 fun i=>by
    rw[Nat.testBit_and,qk,zero_testBit];by_cases hi:u=i
    · subst hi;simp[hff]
    · simp[hi]
   simp[hff,heq]
lemma lp1 (M u:Nat):beq (land M (sl 1 u)) 0=!(M.testBit u):=lp0 M u
lemma Z1Q {r k wo W pV:Nat} {ws:LN} {ms:LF}
 {H:SS} {es:LN} {rP:Nat->Bool}
 {s:Z4_} {u:Nat} (hi:Z4d r k wo W ws ms H es rP s)
 (hu_lt:u < 2 ^ r) (huH:Z3L ms u∈H)
 (hpv:land (sr pV (sl u 4)) 0xffff=Z4Z k wo ws u):
 let s':=Z50 W pV s u
 Z4d r k wo W ws ms H es rP s'∧(∀ a∈s.Gs,a∈s'.Gs)∧u∈s'.Gs:=by
 intro s';dsimp only[s',Z50,z5a];simp only[lp1];cases hGb:s.G.testBit u with
 | true=>simp only[qNt,qFl,↓reduceIte];exact ⟨hi,fun _ h=>h,(hi.bit u).mp hGb⟩
 | false=>
  simp only[qNf,↓reduceIte];have v7:u∉s.Gs:=fun h=>false_ne_true (hGb ▸ (hi.bit u).mpr h);rw[hpv]
  have v5:∀ a,(lor s.G (sl 1 u)).testBit a=true↔a∈u :: s.Gs:=by
   intro a;change (s.G|||1 <<< u).testBit a=true↔_
   rw[testBit_lor,qSl,qZ,qk,qOr,qD,hi.bit a,qC];by_cases ha:a=u
   · subst ha;simp
   · simp[ha,Ne.symm ha]
  by_cases hru:s.rM.testBit u=true
  · simp only[hru,qNt,qFl,↓reduceIte]
    have v0:∀ a,(Nat.xor s.rM (sl 1 u)).testBit a=true↔decide (a≠u)=true∧s.rM.testBit a=true:=by
     intro a;change (s.rM ^^^ 1 <<< u).testBit a=true↔_
     rw[Nat.testBit_xor,qSl,qZ,qk];by_cases ha:a=u
     · subst ha;simp[hru]
     · simp[ha,Ne.symm ha]
    have v3:∀ a,(Nat.xor s.rM (sl 1 u)).testBit a=true->a < 2 ^ r:=fun a ha=>
     hi.rem_lt a ((v0 a).mp ha).2
    have v1:∀ a,(Nat.xor s.rM (sl 1 u)).testBit a=true↔(rP a=true∧a∉u :: s.Gs∧a∉es):=by
     intro a;rw[v0 a,qD,hi.rem_spec a,qC,not_or];tauto
    have v2:s.rS-(W-Z4Z k wo ws u)=
     ∑ a∈(Finset.range (2 ^ r)).filter (fun a=>(Nat.xor s.rM (sl 1 u)).testBit a),(W-Z4Z k wo ws a):=by
     let S:=(Finset.range (2 ^ r)).filter (fun a=>s.rM.testBit a);let S':=(Finset.range (2 ^ r)).filter (fun a=>(Nat.xor s.rM (sl 1 u)).testBit a)
     have v8:S'=S.erase u:=by ext a;simp only[S',S,qF,mem_erase,qMr,v0,qD];tauto
     change _=∑ a∈S',(W-Z4Z k wo ws a);rw[v8,hi.remSum_eq];have v4:u∈S:=qF.mpr ⟨qMr.mpr hu_lt,hru⟩;have v6:=add_sum_erase S (fun a=>W-Z4Z k wo ws a) v4;dsimp only[S] at v6 ⊢;omega
    refine ⟨⟨q4.mpr ⟨v7,hi.nd⟩,?_,v5,?_,?_,?_,v3,v1,hi.rem_neg,v2⟩,
     fun _ ha=>qO u ha,qG⟩
    · intro a ha;rcases qC.mp ha with rfl|ha';exact hu_lt;exact hi.lt a ha'
    · intro a ha;rcases qC.mp ha with rfl|ha';exact huH;exact hi.memH a ha'
    · simp[hi.curP_eq,Nat.add_comm]
    · simp[hi.curCnt_eq]
  · have hrf:s.rM.testBit u=false:=qEf.mpr hru;simp only[hrf,qNf,↓reduceIte]
    have v1:∀ a,s.rM.testBit a=true↔(rP a=true∧a∉u :: s.Gs∧a∉es):=by
     intro a;rw[hi.rem_spec a,qC,not_or];constructor
     · intro h;refine ⟨h.1,⟨?_,h.2.1⟩,h.2.2⟩;rintro rfl;exact hru ((hi.rem_spec a).mpr h)
     · exact fun h=>⟨h.1,h.2.1.2,h.2.2⟩
    refine ⟨⟨q4.mpr ⟨v7,hi.nd⟩,?_,v5,?_,?_,?_,hi.rem_lt,v1,hi.rem_neg,hi.remSum_eq⟩,
     fun _ ha=>qO u ha,qG⟩
    · intro a ha;rcases qC.mp ha with rfl|ha';exact hu_lt;exact hi.lt a ha'
    · intro a ha;rcases qC.mp ha with rfl|ha';exact huH;exact hi.memH a ha'
    · simp[hi.curP_eq,Nat.add_comm]
    · simp[hi.curCnt_eq]
lemma VN {r k wo W pV:Nat} {ws:LN} {ms:LF}
 {H:SS} {es:LN} {rP:Nat->Bool}
 (hpv:zO4 r k wo ws pV) {x:Nat} (hx_lt:x < 2 ^ r):
 ∀ (ys:LN) (s:Z4_),
  (∀ y∈ys,y < 2 ^ r∧Z3L ms (x|||y)∈H)->
  Z4d r k wo W ws ms H es rP s->
  let res:=Z4s W pV x ys s
  Z4d r k wo W ws ms H es rP res∧
   (∀ a∈s.Gs,a∈res.Gs)∧(∀ y∈ys,(x|||y)∈res.Gs)
 | [],s,_,hi=>⟨hi,fun _ h=>h,fun _ h=>by simp at h⟩
 | y :: ys,s,hyH,hi=>by
  have hy:=hyH y qG;have v2:lor x y < 2 ^ r:=q5 hx_lt hy.1;have hstep:=Z1Q hi v2 hy.2 (hpv _ v2);have ih:=VN hpv hx_lt ys (Z50 W pV s (lor x y)) (fun z hz=>hyH z (qO y hz)) hstep.1
  rw[z4c];refine ⟨ih.1,fun a ha=>ih.2.1 a (hstep.2.1 a ha),fun z hz=>?_⟩;rcases qC.mp hz with rfl|hz'
  · exact ih.2.1 _ hstep.2.2
  · exact ih.2.2 z hz'
lemma Z4e (x:Nat):x|||x=x:=
 q8 fun i=>by simp
lemma Z4f (x y z:Nat):(x|||y)|||(x|||z)=x|||(y|||z):=
 q8 fun i=>by simp;cases x.testBit i<;>simp
lemma ZL {r k wo W pV:Nat} {ws cg:LN} {ms:LF}
 {H:SS} {es:LN} {rP:Nat->Bool}
 (hpv:zO4 r k wo ws pV) (hc:∀ A∈H,∀ B∈H,A∪B∈H)
 (hcg_lt:∀ g∈cg,g < 2 ^ r)
 (hcg_uc:∀ a∈cg,∀ b∈cg,(a|||b)∈cg)
 (hcg_op:∀ g∈cg,∀ A∈H,A∪Z3L ms g∈H)
 {s:Z4_} {x:Nat} (hi:Z4d r k wo W ws ms H es rP s)
 (hs_cg:∀ a∈s.Gs,∀ g∈cg,(a|||g)∈s.Gs)
 (hs_uc:∀ a∈s.Gs,∀ b∈s.Gs,(a|||b)∈s.Gs)
 (hx_lt:x < 2 ^ r) (hxH:Z3L ms x∈H):
 let s':=Xy W pV cg s x
 Z4d r k wo W ws ms H es rP s'∧
  (∀ a∈s'.Gs,∀ g∈cg,(a|||g)∈s'.Gs)∧
  (∀ a∈s'.Gs,∀ b∈s'.Gs,(a|||b)∈s'.Gs)∧
  (∀ a∈s.Gs,a∈s'.Gs)∧x∈s'.Gs:=by
 intro s';dsimp only[s',Xy];simp only[lp1];cases hxG:s.G.testBit x with
 | true=>simp only[qNt,qFl,↓reduceIte];exact ⟨hi,hs_cg,hs_uc,fun _ h=>h,(hi.bit x).mp hxG⟩
 | false=>
  simp only[qNf,↓reduceIte];have h0:=Z1Q hi hx_lt hxH (hpv x hx_lt);dsimp only[Z50] at h0;rw[lp1,hxG,qNf,if_pos rfl] at h0;set s0:=z5a W pV s x (sl 1 x);have v12:∀ g∈cg,g < 2 ^ r∧Z3L ms (x|||g)∈H:=fun g hg=>⟨hcg_lt g hg,by rw[Q3];exact hcg_op g hg _ hxH⟩;have h1:=VN hpv hx_lt cg s0 v12 h0.1;set s1:=Z4s W pV x cg s0;have hsH:∀ y∈s.Gs,y < 2 ^ r∧Z3L ms (x|||y)∈H:=fun y hy=>⟨hi.lt y hy,by rw[Q3];exact hc _ hxH _ (hi.memH y hy)⟩;have h2:=VN hpv hx_lt s.Gs s1 hsH h1.1;set s2:=Z4s W pV x s.Gs s1;have v5:∀ a∈s.Gs,a∈s2.Gs:=fun a ha=>h2.2.1 a (h1.2.1 a (h0.2.1 a ha));have v6:x∈s2.Gs:=h2.2.1 x (h1.2.1 x h0.2.2);have v2:∀ g∈cg,(x|||g)∈s2.Gs:=fun g hg=>h2.2.1 _ (h1.2.2 g hg);have v0:∀ y∈s.Gs,(x|||y)∈s2.Gs:=h2.2.2
  have v1:∀ a∈s2.Gs,a∈s.Gs∨a=x∨(∃ g∈cg,a=x|||g)∨(∃ y∈s.Gs,a=x|||y):=by
   intro a ha
   have hs0:∀ z∈s0.Gs,z=x∨z∈s.Gs:=by
    intro z hz;dsimp[s0,z5a] at hz;split_ifs at hz<;>exact qC.mp hz
   have v3:∀ {ys:LN} {st:Z4_} {u:Nat},
    (u∈(Z4s W pV x ys st).Gs->u∈st.Gs∨∃ y∈ys,u=lor x y):=by
    intro ys st u hu;induction ys generalizing st with
    | nil=>exact Or.inl hu
    | cons w ws' ihf=>
     rw[z4c] at hu;rcases ihf (st:=Z50 W pV st (lor x w)) hu with hst|⟨y,hy,rfl⟩
     · dsimp only[Z50,z5a] at hst;split_ifs at hst <;>
        first | exact Or.inl hst | (rcases qC.mp hst with rfl|hst';exact Or.inr ⟨w,qG,rfl⟩;exact Or.inl hst')
     · exact Or.inr ⟨y,qO w hy,rfl⟩
   rcases v3 ha with ha1|⟨y,hy,rfl⟩
   · rcases v3 ha1 with ha0|⟨g,hg,rfl⟩
     · rcases hs0 a ha0 with rfl|has;exact Or.inr (Or.inl rfl);exact Or.inl has
     · exact Or.inr (Or.inr (Or.inl ⟨g,hg,rfl⟩))
   · exact Or.inr (Or.inr (Or.inr ⟨y,hy,rfl⟩))
  have v7:∀ a∈s2.Gs,∀ g∈cg,(a|||g)∈s2.Gs:=by
   intro a ha g hg;rcases v1 a ha with has|rfl|⟨g1,hg1,rfl⟩|⟨y,hy,rfl⟩
   · exact v5 _ (hs_cg a has g hg)
   · exact v2 g hg
   · rw[lor_assoc];exact v2 _ (hcg_uc g1 hg1 g hg)
   · rw[lor_assoc];exact v0 _ (hs_cg y hy g hg)
  have v8:∀ a∈s2.Gs,∀ b∈s2.Gs,(a|||b)∈s2.Gs:=by
   intro a ha b hb;rcases v1 a ha with has|rfl|⟨g1,hg1,rfl⟩|⟨y1,hy1,rfl⟩
   · rcases v1 b hb with hbs|rfl|⟨g2,hg2,rfl⟩|⟨y2,hy2,rfl⟩
     · exact v5 _ (hs_uc a has b hbs)
     · rw[lor_comm];exact v0 a has
     · rw[← lor_assoc,lor_comm a x,lor_assoc];exact v0 _ (hs_cg a has g2 hg2)
     · rw[← lor_assoc,lor_comm a x,lor_assoc];exact v0 _ (hs_uc a has y2 hy2)
   · rcases v1 b hb with hbs|rfl|⟨g2,hg2,rfl⟩|⟨y2,hy2,rfl⟩
     · exact v0 b hbs
     · rw[Z4e];exact v6
     · rw[← lor_assoc,Z4e];exact v2 g2 hg2
     · rw[← lor_assoc,Z4e];exact v0 y2 hy2
   · rcases v1 b hb with hbs|rfl|⟨g2,hg2,rfl⟩|⟨y2,hy2,rfl⟩
     · rw[lor_assoc,lor_comm g1 b];exact v0 _ (hs_cg b hbs g1 hg1)
     · rw[lor_comm,← lor_assoc,Z4e];exact v2 g1 hg1
     · rw[Z4f];exact v2 _ (hcg_uc g1 hg1 g2 hg2)
     · rw[Z4f,lor_comm g1 y2];exact v0 _ (hs_cg y2 hy2 g1 hg1)
   · rcases v1 b hb with hbs|rfl|⟨g2,hg2,rfl⟩|⟨y2,hy2,rfl⟩
     · rw[lor_assoc];exact v0 _ (hs_uc y1 hy1 b hbs)
     · rw[lor_comm,← lor_assoc,Z4e];exact v0 y1 hy1
     · rw[Z4f];exact v0 _ (hs_cg y1 hy1 g2 hg2)
     · rw[Z4f];exact v0 _ (hs_uc y1 hy1 y2 hy2)
  exact ⟨h2.1,v7,v8,v5,v6⟩
lemma Z1R {r k wo W pV:Nat} {ws:LN} {ms:LF}
 {H:SS} {es:LN} {rP:Nat->Bool}
 {s:Z4_} (hi:Z4d r k wo W ws ms H es rP s)
 {x:Nat} (hx_lt:x < 2 ^ r)
 (hpv:land (sr pV (sl x 4)) 0xffff=Z4Z k wo ws x):
 Z4d r k wo W ws ms H (x :: es) rP (Z51 W pV s x):=by
 dsimp only[Z51];simp only[lp1];cases hrx:s.rM.testBit x with
 | false=>
  simp only[qNf,↓reduceIte];refine ⟨hi.nd,hi.lt,hi.bit,hi.memH,hi.curP_eq,hi.curCnt_eq,hi.rem_lt,?_,
   hi.rem_neg,hi.remSum_eq⟩
  intro a;rw[hi.rem_spec a,qC,not_or];constructor
  · intro h;refine ⟨h.1,h.2.1,?_,h.2.2⟩;rintro rfl;have:s.rM.testBit a=true:=(hi.rem_spec a).mpr h;simp[hrx] at this
  · exact fun h=>⟨h.1,h.2.1,h.2.2.2⟩
 | true=>
  simp only[qNt,qFl,↓reduceIte,hpv]
  have v0:∀ a,(Nat.xor s.rM (sl 1 x)).testBit a=true↔decide (a≠x)=true∧s.rM.testBit a=true:=by
   intro a;change (s.rM ^^^ 1 <<< x).testBit a=true↔_
   rw[Nat.testBit_xor,qSl,qZ,qk];by_cases ha:a=x
   · subst ha;simp[hrx]
   · simp[ha,Ne.symm ha]
  have v6:∀ a,(Nat.xor s.rM (sl 1 x)).testBit a=true->a < 2 ^ r:=fun a ha=>
   hi.rem_lt a ((v0 a).mp ha).2
  have v1:∀ a,(Nat.xor s.rM (sl 1 x)).testBit a=true↔(rP a=true∧a∉s.Gs∧a∉x :: es):=by
   intro a;rw[v0 a,qD,hi.rem_spec a,qC,not_or];tauto
  have v2:s.rS-(W-Z4Z k wo ws x)=
   ∑ a∈(Finset.range (2 ^ r)).filter (fun a=>(Nat.xor s.rM (sl 1 x)).testBit a),(W-Z4Z k wo ws a):=by
   let S:=(Finset.range (2 ^ r)).filter (fun a=>s.rM.testBit a);let S':=(Finset.range (2 ^ r)).filter (fun a=>(Nat.xor s.rM (sl 1 x)).testBit a)
   have v5:S'=S.erase x:=by ext a;simp only[S',S,qF,mem_erase,qMr,v0,qD];tauto
   have v4:x∈S:=qF.mpr ⟨qMr.mpr hx_lt,hrx⟩;change _=∑ a∈S',(W-Z4Z k wo ws a);rw[v5,hi.remSum_eq];have v3:=add_sum_erase S (fun a=>W-Z4Z k wo ws a) v4;dsimp only[S] at v3 ⊢;omega
  exact ⟨hi.nd,hi.lt,hi.bit,hi.memH,hi.curP_eq,hi.curCnt_eq,v6,v1,hi.rem_neg,v2⟩
lemma VO {r k wo W pV:Nat} {ws:LN} {ms:LF}
 {H:SS} {rP:Nat->Bool} (hpv:zO4 r k wo ws pV):
 ∀ (xs es:LN) (s:Z4_),
  (∀ x∈xs,x < 2 ^ r)->
  Z4d r k wo W ws ms H es rP s->
  Z4d r k wo W ws ms H (xs++es) rP (Z4t W pV s xs)
 | [],_,s,_,hi=>hi
 | x :: xs,es,s,hlt,hi=>by
  have hx:=hlt x qG;have h1:=Z1R hi hx (hpv x hx);have h2:=VO hpv xs (x :: es) (Z51 W pV s x)
   (fun y hy=>hlt y (qO x hy)) h1
  change Z4d r k wo W ws ms H ((x :: xs)++es) rP (Z4t W pV (Z51 W pV s x) xs);refine ⟨h2.nd,h2.lt,h2.bit,h2.memH,h2.curP_eq,h2.curCnt_eq,h2.rem_lt,?_,h2.rem_neg,h2.remSum_eq⟩;intro a;rw[h2.rem_spec a];simp only[mem_append,qC];tauto
def Z3S (G rM:Nat):List (Nat × Nat)->Nat × LN × Nat
 | []=>(0,[],0)
 | (ax,defc):: xs=>
  let (g1,c1,c1s):=Z3S G rM xs;let g':=if beq (land G ax) 0 then g1 else g1+1
  if ble 1 defc&&!(beq (land rM ax) 0) then (g',defc :: c1,c1s+defc) else (g',c1,c1s)
def t3s (m1 m2 m3 a:Nat):Nat × Nat × Nat:=
 if ble m1 a then (a,m1,m2) else if ble m2 a then (m1,a,m2) else if ble m3 a then (m1,m2,a) else (m1,m2,m3)
def z3Lp (G rM:Nat):List (Nat × Nat)->Nat->Nat->Nat->Nat->Nat->Nat->Nat × Nat × Nat × Nat × Nat × Nat
 | [],g1,ln,sm,m1,m2,m3=>(g1,ln,sm,m1,m2,m3)
 | (ax,defc):: xs,g1,ln,sm,m1,m2,m3=>
  let g':=if beq (land G ax) 0 then g1 else g1+1
  if ble 1 defc&&!(beq (land rM ax) 0) then
   let tp:=t3s m1 m2 m3 defc
   z3Lp G rM xs g' (ln+1) (sm+defc) tp.1 tp.2.1 tp.2.2
  else z3Lp G rM xs g' ln sm m1 m2 m3
def t3v (v m1 m2 m3:Nat):Nat:=
 if beq v 0 then 0 else if beq v 1 then m1 else if beq v 2 then m1+m2 else m1+m2+m3
def Z3T (W uC tgtPos tgtNeg:Nat) (sings:List (Nat × Nat)) (st:Z4_):Bool:=
 let lhs:=tgtPos+st.cC*W;let rhs:=st.cP+tgtNeg
 if ble (lhs+st.rS) rhs then true
 else if beq uC 0 then false
 else
  let (g1,ln,c1Sum,m1,m2,m3):=z3Lp st.G st.rM sings 0 0 0 0 0 0;let v1:=(if beq uC 2 then 3 else 2)-g1
  if ble ln v1 then false
  else ble (lhs+(st.rS-c1Sum)+t3v v1 m1 m2 m3) rhs
lemma Y1 {α:Type*} {a:α} {l₂ as:List α} (hs:Subperm l₂ (a :: as)):
 Subperm l₂ as∨∃ l₂',Perm l₂ (a :: l₂')∧Subperm l₂' as:=by
 obtain ⟨l₃,hp,hsub⟩:=hs;cases hsub with
 | cons _ hsub'=>exact Or.inl ⟨l₃,hp,hsub'⟩
 | cons_cons _ hsub'=>exact Or.inr ⟨_,hp.symm,⟨_,Perm.refl _,hsub'⟩⟩
def t3I (m1 m2 m3:Nat) (seen:LN):Prop:=
 m3≤ m2∧m2≤ m1∧∀ (l:LN) (v:Nat),v≤ 3->l.Subperm seen->l.length≤ v->l.sum≤ t3v v m1 m2 m3
lemma t3S {m1 m2 m3 a:Nat} {seen:LN} (hinv:t3I m1 m2 m3 seen):
 let (n1,n2,n3):=t3s m1 m2 m3 a;t3I n1 n2 n3 (a :: seen):=by
 rcases hinv with ⟨h32,h21,hbd⟩
 have step_case:∀ n1 n2 n3:Nat,n3≤ n2->n2≤ n1->
  (∀ v≤ 3,t3v v m1 m2 m3≤ t3v v n1 n2 n3)->
  (∀ v≤ 2,a+t3v v m1 m2 m3≤ t3v (v+1) n1 n2 n3)->
  t3I n1 n2 n3 (a :: seen):=by
  intro n1 n2 n3 hn32 hn21 hno ha;refine ⟨hn32,hn21,fun l v hv hsub hlen=>?_⟩
  rcases Y1 hsub with h_in|⟨l',hp,hsub'⟩
  · exact le_trans (hbd l v hv h_in hlen) (hno v hv)
  · have hl'v:l'.length+1≤ v:=by have hlp:=hp.length_eq;rw[List.length_cons] at hlp;omega
    cases v with
    | zero=>omega
    | succ v'=>rw[hp.sum_eq,List.sum_cons];exact le_trans (Nat.add_le_add_left (hbd l' v' (by omega) hsub' (by omega)) a) (ha v' (by omega))
 dsimp[t3s];split_ifs with h1 h2 h3
 · have hm1:=ble_eq.mp h1;exact step_case a m1 m2 h21 hm1 (fun v _=>by rcases v with _|_|_|_|_ <;> first | omega | (simp[t3v];try omega)) (fun v _=>by rcases v with _|_|_|_ <;> first | omega | (simp[t3v];try omega))
 · have hm2:=ble_eq.mp h2;have:a < m1:=by by_contra h;exact h1 (ble_eq.mpr (by omega))
   exact step_case m1 a m2 hm2 (by omega) (fun v _=>by rcases v with _|_|_|_|_ <;> first | omega | (simp[t3v];try omega)) (fun v _=>by rcases v with _|_|_|_ <;> first | omega | (simp[t3v];try omega))
 · have hm3:=ble_eq.mp h3;have:a < m2:=by by_contra h;exact h2 (ble_eq.mpr (by omega))
   exact step_case m1 m2 a (by omega) h21 (fun v _=>by rcases v with _|_|_|_|_ <;> first | omega | (simp[t3v];try omega)) (fun v _=>by rcases v with _|_|_|_ <;> first | omega | (simp[t3v];try omega))
 · have:a < m3:=by by_contra h;exact h3 (ble_eq.mpr (by omega))
   exact step_case m1 m2 m3 h32 h21 (fun _ _=>le_rfl) (fun v _=>by rcases v with _|_|_|_ <;> first | omega | (simp[t3v];try omega))
lemma z3Ls (G rM:Nat):∀ xs g1 ln sm m1 m2 m3 seen,
 t3I m1 m2 m3 seen->
 let z:=Z3S G rM xs;let r:=z3Lp G rM xs g1 ln sm m1 m2 m3
 r.1=g1+z.1∧r.2.1=ln+z.2.1.length∧r.2.2.1=sm+z.2.2∧
 (∀ (l:LN) (v:Nat),v≤ 3->l.Subperm (z.2.1++seen)->l.length≤ v->l.sum≤ t3v v r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2)
 | [],g1,ln,sm,m1,m2,m3,seen,hinv=>⟨rfl,rfl,rfl,fun l v hv hsub hlen=>hinv.2.2 l v hv (by simpa[Z3S] using hsub) hlen⟩
 | (ax,defc):: xs,g1,ln,sm,m1,m2,m3,seen,hinv=>by
  dsimp[Z3S,z3Lp];rcases hzs:Z3S G rM xs with ⟨g0,c0,s0⟩;cases hG:beq (land G ax) 0 with
  | true=>
   simp only[↓reduceIte];split_ifs with hact
   · have hinv':=t3S (a:=defc) hinv;have ih:=z3Ls G rM xs g1 (ln+1) (sm+defc) (t3s m1 m2 m3 defc).1 (t3s m1 m2 m3 defc).2.1 (t3s m1 m2 m3 defc).2.2 (defc :: seen) hinv'
     rcases ih with ⟨h_1,h_2,h_3,h_4⟩;simp only[hzs] at h_1 h_2 h_3 h_4 ⊢
     refine ⟨h_1,by simp[h_2];omega,by omega,fun l v hv hsub hlen=>?_⟩;exact h_4 l v hv (hsub.trans (List.perm_middle.symm.subperm)) hlen
   · rcases z3Ls G rM xs g1 ln sm m1 m2 m3 seen hinv with ⟨h_1,h_2,h_3,h_4⟩
     simp only[hzs] at h_1 h_2 h_3 h_4 ⊢;exact ⟨h_1,h_2,h_3,h_4⟩
  | false=>
   simp only[qFl,↓reduceIte];split_ifs with hact
   · have hinv':=t3S (a:=defc) hinv;have ih:=z3Ls G rM xs (g1+1) (ln+1) (sm+defc) (t3s m1 m2 m3 defc).1 (t3s m1 m2 m3 defc).2.1 (t3s m1 m2 m3 defc).2.2 (defc :: seen) hinv'
     rcases ih with ⟨h_1,h_2,h_3,h_4⟩;simp only[hzs] at h_1 h_2 h_3 h_4 ⊢
     refine ⟨by omega,by simp[h_2];omega,by omega,fun l v hv hsub hlen=>?_⟩;exact h_4 l v hv (hsub.trans (List.perm_middle.symm.subperm)) hlen
   · rcases z3Ls G rM xs (g1+1) ln sm m1 m2 m3 seen hinv with ⟨h_1,h_2,h_3,h_4⟩
     simp only[hzs] at h_1 h_2 h_3 h_4 ⊢;exact ⟨by omega,h_2,h_3,h_4⟩
def Z4h (k wo W mS:Nat) (ws:LN) (b:Nat):Nat × Nat:=
 let a:=sl 1 b;let p:=zZf k wo ws a;let d:=if ble mS (k+1)&&!(ble W p) then W-p else 0
 (sl 1 a,d)
def Z4i (k wo W mS:Nat) (ws:LN) (bs:LN):List (Nat × Nat):=
 bs.map (Z4h k wo W mS ws)
lemma Xz (k wo W mS:Nat) (ws:LN) {G rM:Nat}:
 ∀ (bs:LN),
  let res:=Z3S G rM (Z4i k wo W mS ws bs)
  res.1=(bs.filter (fun b=>G.testBit (2 ^ b))).length∧
  res.2.2=res.2.1.sum∧
  Perm res.2.1
   ((bs.filter (fun b=>
    mS≤ k+1&&Z4Z k wo ws (2 ^ b)< W&&rM.testBit (2 ^ b))).map
    (fun b=>W-Z4Z k wo ws (2 ^ b)))
 | []=>by simp[Z4i,Z3S]
 | b :: bs=>by
  have ih:=Xz k wo W mS ws (G:=G) (rM:=rM) bs;have v1:Z4i k wo W mS ws (b :: bs)=Z4h k wo W mS ws b :: Z4i k wo W mS ws bs:=rfl;change let res:=Z3S G rM (Z4i k wo W mS ws (b :: bs));_;rw[v1];dsimp only[Z3S]
  have hsh:sl 1 b=2 ^ b:=by change 1 <<< b=2 ^ b;rw[qSl,qZ]
  have hblf (a b0:Nat):(ble a b0=false)↔b0 < a:=by rw[← Bool.not_eq_true,ble_eq];omega
  have hce:(ble mS (k+1)&&!(ble W (Z4Z k wo ws (2 ^ b))))=decide (mS≤ k+1∧Z4Z k wo ws (2 ^ b)< W):=by
   rw[Bool.eq_iff_iff];simp only[qA,Bool.not_eq_true',ble_eq,hblf,qD]
  have hdp:Z4h k wo W mS ws b=(sl 1 (2 ^ b),if mS≤ k+1∧Z4Z k wo ws (2 ^ b)< W then W-Z4Z k wo ws (2 ^ b) else 0):=by
   dsimp only[Z4h];rw[hsh];simp only[z4e,hce,qD]
  have v3:(Z4h k wo W mS ws b).1=sl 1 (2 ^ b):=by rw[hdp]
  rw[v3,lp1,lp1];by_cases hcond:mS≤ k+1∧Z4Z k wo ws (2 ^ b)< W
  · have hd:(Z4h k wo W mS ws b).2=W-Z4Z k wo ws (2 ^ b):=by rw[hdp,if_pos hcond]
    have hb1:ble 1 (W-Z4Z k wo ws (2 ^ b))=true:=ble_eq.mpr (by omega)
    have v0:(mS≤ k+1&&Z4Z k wo ws (2 ^ b)< W)=true:=by simp[hcond]
    rw[hd,hb1]
    cases hGb:G.testBit (2 ^ b)<;>cases hRb:rM.testBit (2 ^ b)<;>
     simp only[v0,hGb,hRb,qNf,qNt,Bool.and_true,Bool.and_false,
      qFl,↓reduceIte,List.filter_cons,List.map_cons,List.length_cons,
      List.sum_cons,ih.1,ih.2.1,Nat.add_comm,true_and]
    · exact ih.2.2
    · exact Perm.cons _ ih.2.2
    · exact ih.2.2
    · exact Perm.cons _ ih.2.2
  · have v0:(mS≤ k+1&&Z4Z k wo ws (2 ^ b)< W)=false:=
     Bool.and_eq_false_iff.mpr (by
      by_cases h1:mS≤ k+1
      · exact Or.inr (by simp[show ¬(Z4Z k wo ws (2 ^ b)< W) from fun h=>hcond ⟨h1,h⟩])
      · exact Or.inl (by simp[h1]))
    have hd:(Z4h k wo W mS ws b).2=0:=by rw[hdp,if_neg hcond]
    rw[hd];cases hGb:G.testBit (2 ^ b)<;>
     simp[v0,hGb,ih.1,ih.2.1,ih.2.2,Nat.add_comm,show ble 1 0=false from rfl]
lemma Ym:∀ (r a:Nat),a < 2 ^ r->(Z5o r a=0↔a=0)
 | 0,a,ha=>by simp at ha;simp[ha,Z5o]
 | r+1,a,ha=>by
  have v0:a/2 < 2 ^ r:=by rw[qW,qY] at ha;exact div_lt_of_lt_mul ha
  have ih:=Ym r (a/2) v0;dsimp[Z5o]
  cases hm:qn a<;>omega
lemma YL:∀ (r a:Nat),a < 2 ^ r->(Z5o r a=1↔∃ b < r,a=2 ^ b)
 | 0,a,ha=>by
  simp at ha;subst ha;simp[Z5o]
 | r+1,a,ha=>by
  have v1:a/2 < 2 ^ r:=by rw[qW,qY] at ha;exact div_lt_of_lt_mul ha
  have ih:=YL r (a/2) v1;have h0:=Ym r (a/2) v1;dsimp[Z5o];constructor
  · intro hp
    cases hm:qn a
    · have v4:Z5o r (a/2)=1:=by omega
      obtain ⟨b,hb,v0⟩:=ih.mp v4;refine ⟨b+1,by omega,?_⟩;rw[qW,qY];omega
    · have v3:Z5o r (a/2)=0:=by omega
      have haz:a/2=0:=h0.mp v3;refine ⟨0,by omega,?_⟩;omega
  · rintro ⟨b,hb,rfl⟩
    cases b with
    | zero=>simp only[Nat.pow_zero];have:Z5o r (1/2)=0:=h0.mpr rfl;omega
    | succ b=>
     rw[qW,qY]
     have v2:(2*2 ^ b)% 2=0:=by omega
     have v0:(2*2 ^ b)/2=2 ^ b:=by omega
     rw[v2,v0,zero_add];exact (YL r (2 ^ b) (pow_lt_pow_right (by omega) (by omega))).mpr
      ⟨b,by omega,rfl⟩
lemma Z1S:∀ {b1 b2:Nat},2 ^ b1=2 ^ b2->b1=b2:=by
 intro b1 b2 h;rcases Nat.lt_trichotomy b1 b2 with hlt|heq|hgt
 · have:2 ^ b1 < 2 ^ b2:=pow_lt_pow_right (by omega) hlt;omega
 · exact heq
 · have:2 ^ b2 < 2 ^ b1:=pow_lt_pow_right (by omega) hgt;omega
lemma Yd {α:Type*} [DecidableEq α] {f:α->Nat} {S T:Finset α}
 (hsub:S⊆T):∑ x∈S,f x≤ ∑ x∈T,f x:=by
 rw[← sum_sdiff hsub];omega
lemma YM {ms:LF} (hn:ms.Nodup) {r k wo W mS uC tP tgtNeg:Nat}
 (hr:ms.length=r) {wf:WF}
 {H:SS} (hHM:∀ A∈H,A⊆ms.toFinset)
 {es:LN} {rP:Nat->Bool} {st:Z4_}
 (hinv:Z4d r k wo W (ms.map wf) ms H es rP st)
 (hrem1:∀ a < 2 ^ r,Z5o r a=1->rP a=true->mS≤ k+1)
 (hexH:∀ y∈es,Z3L ms y∉H)
 (hcomp:∀ A∈H,Z4Z k wo (ms.map wf) (Z3M ms A)< W->
  rP (Z3M ms A)=true)
 (hcp:uC≠0->
  (H.filter (fun A=>A.card=1)).card≤ (if uC=2 then 3 else 2))
 (hok:Z3T W uC tP tgtNeg
  (Z4i k wo W mS (ms.map wf) (List.range r)) st=true):
 (tP:Int)-(tgtNeg:Int)≤
  ∑ A∈H,(2*((k*wo+∑ i∈A,wf i:Nat):Int)-(W:Int)):=by
 let ws:=ms.map wf;have v33:∀ {A:SF},A⊆ms.toFinset->
  (2*((k*wo+∑ i∈A,wf i:Nat):Int)-(W:Int))=
   ((Z4Z k wo ws (Z3M ms A):Int)-(W:Int)):=by
  intro A hA
  have hsm:∑ i∈A,wf i=Z5f ws (Z3M ms A):=by
   conv_lhs=>rw[← ZH ms hn hA]
   exact Q4 wf ms hn _
  simp[Z4Z,ws,hsm]
 have v36:(∑ A∈H,(2*((k*wo+∑ i∈A,wf i:Nat):Int)-(W:Int)))=
  ∑ A∈H,((Z4Z k wo ws (Z3M ms A):Int)-(W:Int)):=
  qh rfl (fun A hA=>v33 (hHM A hA))
 rw[v36];let SG:SS:=st.Gs.toFinset.image (Z3L ms)
 have v15:SG⊆H:=by
  intro A hA;obtain ⟨a,ha,rfl⟩:=qI.mp hA;exact hinv.memH a (qM.mp ha)
 have v12:Set.InjOn (Z3L ms) (st.Gs.toFinset:Set Nat):=by
  intro a ha b hb heq;exact Q2 ms hn (hr ▸ hinv.lt a (qM.mp ha))
   (hr ▸ hinv.lt b (qM.mp hb)) heq
 have v24:SG.card=st.cC:=by
  dsimp[SG];rw[card_image_of_injOn v12,qT hinv.nd,hinv.curCnt_eq]
 have v31:∑ A∈SG,((Z4Z k wo ws (Z3M ms A):Int)-(W:Int))=
  (st.cP:Int)-(st.cC*W:Int):=by
  rw[sum_sub_distrib,sum_const];simp only[v24]
  have hp:(∑ A∈SG,(Z4Z k wo ws (Z3M ms A):Int))=(st.cP:Int):=by
   dsimp[SG];rw[sum_image v12];have v7:∑ a∈st.Gs.toFinset,(Z4Z k wo ws (Z3M ms (Z3L ms a)):Int)=
    ∑ a∈st.Gs.toFinset,(Z4Z k wo ws a:Int):=by
    apply qh rfl;intro a ha;rw[ZI ms hn (hr ▸ hinv.lt a (qM.mp ha))]
   have hmc:∀ l:LN,(l.map (fun a=>(Z4Z k wo ws a:Int))).sum=((l.map (Z4Z k wo ws)).sum:Int):=fun l=>by induction l with | nil=>simp | cons a t ih=>simp[ih]
   have v40:∑ a∈st.Gs.toFinset,(Z4Z k wo ws a:Int)=(st.cP:Int):=by rw[List.sum_toFinset _ hinv.nd,hmc,← hinv.curP_eq]
   rw[v7,v40]
  rw[hp,nsmul_eq_mul]
 rw[← sum_sdiff v15,v31];let Hrem:=(H \ SG).filter (fun A=>st.rM.testBit (Z3M ms A));let Hpos:=(H \ SG)\ Hrem;have v0:Hrem⊆H \ SG:=qFs _ _
 have v14:0≤ ∑ A∈Hpos,((Z4Z k wo ws (Z3M ms A):Int)-(W:Int)):=by
  apply sum_nonneg;intro A hA;obtain ⟨hAS,hAnR⟩:=qSd.mp hA;obtain ⟨hAH,hAnSG⟩:=qSd.mp hAS
  have hnb:st.rM.testBit (Z3M ms A)=false:=by
   cases hb:st.rM.testBit (Z3M ms A)
   · rfl
   · exact False.elim (hAnR (qF.mpr ⟨hAS,hb⟩))
  have v46:Z3M ms A∉st.Gs:=by
   intro hg;apply hAnSG;exact qI.mpr ⟨Z3M ms A,qM.mpr hg,
    ZH ms hn (hHM A hAH)⟩
  have v47:Z3M ms A∉es:=by
   intro hex;apply hexH _ hex;rwa[ZH ms hn (hHM A hAH)]
  have hge:W≤ Z4Z k wo ws (Z3M ms A):=by
   by_contra v9;push Not at v9;have hp:=hcomp A hAH v9;have v3:=(hinv.rem_spec (Z3M ms A)).mpr ⟨hp,v46,v47⟩;simp[hnb] at v3
  omega
 have v18:∀ A∈Hrem,Z4Z k wo ws (Z3M ms A)< W:=by
  intro A hA;have v3:=(qF.mp hA).2;exact hinv.rem_neg _ ((hinv.rem_spec _).mp v3).1
 have v19:∑ A∈Hrem,((Z4Z k wo ws (Z3M ms A):Int)-(W:Int))=
  -((∑ A∈Hrem,(W-Z4Z k wo ws (Z3M ms A)):Nat):Int):=by
  have v7:∑ A∈Hrem,((Z4Z k wo ws (Z3M ms A):Int)-(W:Int))=
   ∑ A∈Hrem,-((W-Z4Z k wo ws (Z3M ms A):Nat):Int):=by
   apply qh rfl;intro A hA;have v9:=v18 A hA;omega
  rw[v7,sum_neg_distrib];congr 1;induction Hrem using Finset.induction with
  | empty=>simp
  | insert a S ha ih=>simp only[sum_insert ha,Nat.cast_add,ih]
 rw[← sum_sdiff v0,v19]
 refine le_trans ?_ (add_le_add (le_add_of_nonneg_left (by dsimp only[Hpos] at v14;convert v14)) le_rfl)
 have v4:∀ {T:SS},T⊆Hrem->
  Set.InjOn (Z3M ms) (T:Set (SF)):=by
  intro T hT A hA B hB heq;have hAM:=hHM A (qSd.mp (v0 (hT hA))).1;have hBM:=hHM B (qSd.mp (v0 (hT hB))).1
  calc A=Z3L ms (Z3M ms A):=(ZH ms hn hAM).symm
   _=Z3L ms (Z3M ms B):=by rw[heq]
   _=B:=ZH ms hn hBM
 let Srem:=(Finset.range (2 ^ r)).filter (fun a=>st.rM.testBit a);by_cases huc0:uC=0
 · subst huc0;dsimp[Z3T] at hok
   by_cases hfast:tP+st.cC*W+st.rS≤ st.cP+tgtNeg
   · have v35:Hrem.image (Z3M ms)⊆Srem:=fun x hx=>by obtain ⟨A,hA,rfl⟩:=qI.mp hx;exact qF.mpr ⟨qMr.mpr (hr ▸ VK ms A),(qF.mp hA).2⟩
     have hle:∑ A∈Hrem,(W-Z4Z k wo ws (Z3M ms A))≤ st.rS:=by
      rw[hinv.remSum_eq]
      calc _=∑ a∈Hrem.image (Z3M ms),(W-Z4Z k wo ws a):=(sum_image (f:=fun a=>W-Z4Z k wo ws a) (v4 Subset.rfl)).symm
      _≤ _:=Yd v35
     omega
   rw[if_neg (by simp only[ble_eq];exact hfast)] at hok;simp at hok
 · dsimp[Z3T] at hok
   by_cases hfast:tP+st.cC*W+st.rS≤ st.cP+tgtNeg
   · have v35:Hrem.image (Z3M ms)⊆Srem:=by
      intro x hx;obtain ⟨A,hA,rfl⟩:=qI.mp hx;exact qF.mpr ⟨qMr.mpr (hr ▸ VK ms A),(qF.mp hA).2⟩
     have hle:∑ A∈Hrem,(W-Z4Z k wo ws (Z3M ms A))≤ st.rS:=by
      rw[hinv.remSum_eq]
      calc ∑ A∈Hrem,(W-Z4Z k wo ws (Z3M ms A))
       = ∑ a∈Hrem.image (Z3M ms),(W-Z4Z k wo ws a):=(sum_image (f:=fun a=>W-Z4Z k wo ws a) (v4 Subset.rfl)).symm
       _≤ ∑ a∈Srem,(W-Z4Z k wo ws a):=Yd v35
     omega
   rw[if_neg (by simp only[ble_eq];exact hfast),if_neg (by simp only[beq_eq];exact huc0)] at hok;set rp:=z3Lp st.G st.rM (Z4i k wo W mS ws (List.range r)) 0 0 0 0 0 0;have hzsp:=z3Ls st.G st.rM (Z4i k wo W mS ws (List.range r)) 0 0 0 0 0 0 []
     ⟨le_rfl,le_rfl,fun l v _ hsub _=>by obtain rfl:=List.subperm_nil.mp hsub;simp⟩
   dsimp only at hzsp;change rp.1=_∧rp.2.1=_∧rp.2.2.1=_∧_ at hzsp
   have hc1_not:¬ ble rp.2.1 ((if beq uC 2 then 3 else 2)-rp.1)=true:=by
     intro hc1;rw[if_pos hc1] at hok;simp at hok
   rw[if_neg hc1_not,ble_eq] at hok;have hsings:=Xz k wo W mS ws (G:=st.G) (rM:=st.rM) (List.range r);set res:=Z3S st.G st.rM (Z4i k wo W mS ws (List.range r));let H1:=Hrem.filter (fun A=>A.card=1);let Hoth:=Hrem \ H1;let S1:=Srem.filter (fun a=>Z5o r a=1);have v11:S1⊆Srem:=qFs _ _;have v2:H1⊆Hrem:=qFs _ _
   have v8:res.2.2=∑ a∈S1,(W-Z4Z k wo ws a):=by
     rw[hsings.2.1,hsings.2.2.sum_eq];let fbs:=(List.range r).filter (fun b=>
      mS≤ k+1&&Z4Z k wo ws (2 ^ b)< W&&st.rM.testBit (2 ^ b))
     have v30:fbs.Nodup:=List.nodup_range.filter _;have v23:Set.InjOn (fun b:Nat=>2 ^ b) (fbs.toFinset:Set Nat):=
      fun _ _ _ _ heq=>Z1S heq
     have v44:fbs.toFinset.image (fun b=>2 ^ b)=S1:=by
      ext a;simp only[qI,qM,fbs,qB,qR,
       qA,qD,S1,Srem,qF,qMr]
      constructor
      · rintro ⟨b,⟨hbr,⟨⟨_,_⟩,v3⟩⟩,rfl⟩
        refine ⟨⟨pow_lt_pow_right (by omega) hbr,v3⟩,?_⟩;exact (YL r (2 ^ b) (pow_lt_pow_right (by omega) hbr)).mpr
         ⟨b,hbr,rfl⟩
      · rintro ⟨⟨har,v3⟩,v5⟩
        obtain ⟨b,hbr,rfl⟩:=(YL r a har).mp v5;have hremP:=(hinv.rem_spec (2 ^ b)).mp v3;have v25:mS≤ k+1:=hrem1 (2 ^ b) har v5 hremP.1;have v9:Z4Z k wo ws (2 ^ b)< W:=hinv.rem_neg _ hremP.1;exact ⟨b,⟨hbr,⟨⟨v25,v9⟩,v3⟩⟩,rfl⟩
     rw[← v44,sum_image v23,← List.sum_toFinset _ v30]
   have hc1Sum_le:res.2.2≤ st.rS:=by
     rw[v8,hinv.remSum_eq];exact Yd v11
   have hoth_le:∑ A∈Hoth,(W-Z4Z k wo ws (Z3M ms A))≤ st.rS-res.2.2:=by
     have v34:Hoth.image (Z3M ms)⊆Srem \ S1:=by
      intro x hx;obtain ⟨A,hA,rfl⟩:=qI.mp hx;obtain ⟨hAR,hAn1⟩:=qSd.mp hA;have hmS:Z3M ms A∈Srem:=
       qF.mpr ⟨qMr.mpr (hr ▸ VK ms A),(qF.mp hAR).2⟩
      have v42:A.card≠1:=fun hc1=>hAn1 (qF.mpr ⟨hAR,hc1⟩)
      have v5:Z5o r (Z3M ms A)≠1:=by
       have hAM:=hHM A (qSd.mp (v0 hAR)).1;rw[← hr,← Xs ms hn (Z3M ms A),ZH ms hn hAM];exact v42
      exact qSd.mpr ⟨hmS,fun hs1=>v5 (qF.mp hs1).2⟩
     have v37:∑ a∈Srem \ S1,(W-Z4Z k wo ws a)=st.rS-res.2.2:=by
      have hs:=sum_sdiff v11 (f:=fun a=>W-Z4Z k wo ws a);rw[← hinv.remSum_eq,← v8] at hs;omega
     rw[← v37]
     calc ∑ A∈Hoth,(W-Z4Z k wo ws (Z3M ms A))
      = ∑ a∈Hoth.image (Z3M ms),(W-Z4Z k wo ws a):=
       (sum_image (f:=fun a=>W-Z4Z k wo ws a)
        (v4 (sdiff_subset (s:=Hrem) (t:=H1)))).symm
      _≤ ∑ a∈Srem \ S1,(W-Z4Z k wo ws a):=Yd v34
   have hg1_le:res.1≤ (SG.filter (fun A=>A.card=1)).card:=by
     rw[hsings.1];let Bs:=((List.range r).filter (fun b=>st.G.testBit (2 ^ b))).toFinset;have hBs:Bs.card=((List.range r).filter (fun b=>st.G.testBit (2 ^ b))).length:=
      qT (List.nodup_range.filter _)
     rw[← hBs];apply card_le_card_of_injOn (fun b=>Z3L ms (2 ^ b))
     · intro b hb;obtain ⟨hbr,hgb⟩:=qB.mp (qM.mp hb);rw[qR,← hr] at hbr;have hbG:2 ^ b∈st.Gs:=(hinv.bit _).mp hgb;refine qF.mpr ⟨qI.mpr ⟨2 ^ b,qM.mpr hbG,rfl⟩,?_⟩;dsimp only;rw[Xu ms hbr,qw]
     · intro b1 hb1 b2 hb2 heq;have h1:=qR.mp (qB.mp (qM.mp hb1)).1;have h2:=qR.mp (qB.mp (qM.mp hb2)).1;rw[← hr] at h1 h2;dsimp only at heq;rw[Xu ms h1,Xu ms h2,singleton_inj] at heq;exact Fin.val_eq_of_eq ((List.nodup_iff_injective_get.mp hn) (a₁:=⟨b1,h1⟩) (a₂:=⟨b2,h2⟩) heq)
   have v32:Disjoint (SG.filter (fun A=>A.card=1)) H1:=by
     rw[disjoint_left];intro A hAS v16;exact (qSd.mp (v0 (v2 v16))).2 (qF.mp hAS).1
   have v28:(SG.filter (fun A=>A.card=1))∪H1⊆H.filter (fun A=>A.card=1):=by
     intro A hA;rcases mem_union.mp hA with h1|h2
     · exact qF.mpr ⟨v15 (qF.mp h1).1,(qF.mp h1).2⟩
     · exact qF.mpr ⟨(qSd.mp (v0 (v2 h2))).1,(qF.mp h2).2⟩
   let v6:=if uC=2 then 3 else 2;let v1:=v6-res.1
   have v21:H1.card≤ v1:=by
     have h1:=qL v28;rw[qCu v32] at h1;have hlim:=hcp huc0;dsimp[v1,v6];omega
   let l₂:=(H1.toList.map (Z3M ms)).map (fun a=>W-Z4Z k wo ws a)
   have v41:Subperm l₂ res.2.1:=by
     apply Subperm.trans _ hsings.2.2.symm.subperm;let fbs:=(List.range r).filter (fun b=>
      mS≤ k+1&&Z4Z k wo ws (2 ^ b)< W&&st.rM.testBit (2 ^ b))
     have v39:(H1.toList.map (Z3M ms)).Nodup:=
      List.Nodup.map_on (fun x hx y hy=>
       v4 v2 (qp.mp hx) (qp.mp hy)) H1.nodup_toList
     have v27:Subperm (H1.toList.map (Z3M ms)) (fbs.map (fun b=>2 ^ b)):=by
      apply List.Nodup.subperm v39;intro a ha;obtain ⟨A,hA,rfl⟩:=List.mem_map.mp ha;have v16:=qp.mp hA;have hAR:=v2 v16;have hAc:A.card=1:=(qF.mp v16).2;have har:Z3M ms A < 2 ^ r:=hr ▸ VK ms A;have v3:st.rM.testBit (Z3M ms A)=true:=(qF.mp hAR).2
      have v5:Z5o r (Z3M ms A)=1:=by
       have hAM:=hHM A (qSd.mp (v0 hAR)).1;rw[← hr,← Xs ms hn (Z3M ms A),ZH ms hn hAM];exact hAc
      obtain ⟨b,hbr,hpow⟩:=(YL r _ har).mp v5;have hremP:=(hinv.rem_spec (Z3M ms A)).mp v3;have v25:=hrem1 _ har v5 hremP.1;have v9':Z4Z k wo ws (Z3M ms A)< W:=hinv.rem_neg _ hremP.1;rw[List.mem_map];refine ⟨b,qB.mpr ⟨qR.mpr hbr,?_⟩,hpow.symm⟩;rw[← hpow];simp[v25,v9',v3]
     obtain ⟨l',hp',hsub'⟩:=v27;have v22:=hsub'.map (fun a=>W-Z4Z k wo ws a);dsimp only[fbs] at v22;rw[List.map_map] at v22;exact ⟨l'.map (fun a=>W-Z4Z k wo ws a),hp'.map _,v22⟩
   have hl₂_len:l₂.length≤ v1:=by simpa[l₂,q3] using v21
   have hv1_le3:v1≤ 3:=by dsimp[v1,v6];split_ifs <;> omega
   have v26:l₂.sum≤ t3v v1 rp.2.2.2.1 rp.2.2.2.2.1 rp.2.2.2.2.2:=hzsp.2.2.2 l₂ v1 hv1_le3 (by simpa using v41) hl₂_len
   have hl₂_sum:l₂.sum=∑ A∈H1,(W-Z4Z k wo ws (Z3M ms A)):=by
     dsimp[l₂];rw[List.map_map];simp
   have v10:∑ A∈Hrem,(W-Z4Z k wo ws (Z3M ms A))=
      (∑ A∈Hoth,(W-Z4Z k wo ws (Z3M ms A)))+
      ∑ A∈H1,(W-Z4Z k wo ws (Z3M ms A)):=by
     rw[← sum_sdiff v2]
   have vr1:rp.1=res.1:=by simpa[res] using hzsp.1
   have vr22:rp.2.2.1=res.2.2:=by simpa[res] using hzsp.2.2.1
   have v29:(if beq uC 2 then 3 else 2)-rp.1=v1:=by
     rw[vr1];dsimp[v1,v6];cases uC<;>simp
   have hdef_le:∑ A∈Hrem,(W-Z4Z k wo ws (Z3M ms A))≤
      (st.rS-rp.2.2.1)+t3v ((if beq uC 2 then 3 else 2)-rp.1) rp.2.2.2.1 rp.2.2.2.2.1 rp.2.2.2.2.2:=by
     rw[v29,vr22,v10,← hl₂_sum];omega
   have hadd:tP+st.cC*W+((st.rS-rp.2.2.1)+t3v ((if beq uC 2 then 3 else 2)-rp.1) rp.2.2.2.1 rp.2.2.2.2.1 rp.2.2.2.2.2)≤ st.cP+tgtNeg:=by simpa[Nat.add_assoc] using hok
   have htot:tP+st.cC*W+∑ A∈Hrem,(W-Z4Z k wo ws (Z3M ms A))≤ tP+st.cC*W+((st.rS-rp.2.2.1)+t3v ((if beq uC 2 then 3 else 2)-rp.1) rp.2.2.2.1 rp.2.2.2.2.1 rp.2.2.2.2.2):=Nat.add_le_add_left hdef_le _
   have:=le_trans htot hadd;omega
structure Z4w where
 r:Nat
 wo:Nat
 W:Nat
 ws:LN
 gS:LN
 pS:LN
 pB:Nat
structure Cfg where
 ba:Z4w
 k:Nat
 tg:LN
 tB:Nat
 mS:Nat
 uC:Nat
 fE:Bool:=false
 fN:Bool:=false
abbrev Cfg.r (c:Cfg):=c.ba.r
abbrev Cfg.W (c:Cfg):=c.ba.W
abbrev Cfg.wo (c:Cfg):=c.ba.wo
abbrev Cfg.ws (c:Cfg):=c.ba.ws
abbrev Cfg.gS (c:Cfg):=c.ba.gS
abbrev Cfg.pS (c:Cfg):=c.ba.pS
abbrev Cfg.pB (c:Cfg):=c.ba.pB
def zJf:LN->Nat->Nat
 | [],_=>0 | _ :: _,0=>0
 | i :: is,g+1=>let r:=zJf is (sr (g+1) 1);if beq (land (g+1) 1) 1 then lor (sl 1 i) r else r
lemma zJ0:∀ is,Z1J is 0=0 | []=>rfl | _ :: is=>by simp[Z1J,zJ0 is]
lemma zJe:∀ is g,zJf is g=Z1J is g
 | [],0=>rfl | [],g+1=>rfl | i :: is,0=>by simp[zJf,zJ0]
 | i :: is,g+1=>by
  dsimp only[zJf,Z1J];rw[zJe is _]
  have h1:sr (g+1) 1=(g+1)/2:=by change (g+1)>>> 1=_;rw[qSr,pow_one]
  have hm:land (g+1) 1=(g+1)% 2:=and_one_is_mod (g+1);rw[h1];simp only[hm]
  cases h:(g+1)% 2 with
  | zero=>rw[show beq 0 1=false from rfl];simp
  | succ k=>
   have hk:k=0:=by have:=mod_lt (g+1) (by omega:0 < 2);omega
   subst hk;rw[show beq 1 1=true from rfl];simp[qSl]
def qBf (gS p:LN):Bool:=gS.all (fun g=>gS.contains (zJf p g))
def Qb (gS p:LN):Bool:=gS.all (fun g=>gS.contains (Z1J p g))
lemma qBe (gS p:LN):qBf gS p=Qb gS p:=List.all_congr rfl fun g=>by rw[zJe]
def zOf (r:Nat) (p:LN):Bool:=beq p.length r&&p.Nodup&&p.all (fun i=>ble (i+1) r)
lemma zOe (r:Nat) (p:LN):zOf r p=Z3O r p:=by
 dsimp[zOf,Z3O]
 have h1:beq p.length r=(p.length==r):=by rw[Bool.eq_iff_iff];simp[beq_eq]
 have hlt (a b:Nat):(a+1≤ b)=(a < b):=propext Nat.succ_le_iff
 have h2:p.all (fun i=>ble (i+1) r)=p.all (· < r):=List.all_congr rfl fun i=>by rw[Bool.eq_iff_iff];simp[ble_eq,hlt]
 rw[h1,h2]
def zqf (ws p:LN):Bool:=(List.range ws.length).all (fun i=>beq (ws.getD i 0) (ws.getD (p.getD i 0) 0))
lemma zqe (ws p:LN):zqf ws p=Z3q ws p:=List.all_congr rfl fun i=>by rw[Bool.eq_iff_iff];simp[beq_eq]
def Z3U (b:Z4w):Bool:=
 ble b.r 7&&beq b.ws.length b.r&&b.gS.all (fun g=>ble (g+1) (sl 1 b.r))&&
  b.pS.all (fun c=>let p:=Z3p b.r c;zOf b.r p&&zqf b.ws p&&qBf b.gS p)
inductive P4 (α:Type)
 | leaf (v:α)
 | node4 (a b c d:P4 α)
 | empty
def P4.gA {α:Type}:Nat->P4 α->Nat->Option α
 | _,.leaf v,_=>some v
 | _,.empty,_=>none
 | sh+2,.node4 a b c d,i=>
  match land (sr i sh) 3 with
  | 0=>P4.gA sh a i
  | 1=>P4.gA sh b i
  | 2=>P4.gA sh c i
  | _=>P4.gA sh d i
 | _,.node4 _ _ _ _,_=>none
structure PTab (α:Type) where
 len:Nat
 sh:Nat
 tree:P4 α
abbrev PT:=PTab (Nat × Nat)
def PTab.get? {α:Type} (t:PTab α) (i:Nat):Option α:=
 if ble t.len i then none else P4.gA t.sh t.tree i
def p4 {α:Type}:List (P4 α)->List (P4 α)
 | a :: b :: c :: d :: rest=>.node4 a b c d :: p4 rest
 | [a,b,c]=>[.node4 a b c .empty]
 | [a,b]=>[.node4 a b .empty .empty]
 | [a]=>[.node4 a .empty .empty .empty]
 | []=>[]
def mP4 {α:Type}:Nat->Nat->List (P4 α)->Nat × P4 α
 | _,sh,[t]=>(sh,t)
 | fuel+1,sh,ts=>mP4 fuel (sh+2) (p4 ts)
 | _,sh,_=>(sh,.empty)
def mPT {α:Type} (xs:List α):PTab α:=
 let (sh,t):=mP4 6 0 (xs.map P4.leaf);⟨xs.length,sh,t⟩
def mL (pp:LN):Nat->Nat
 | 0=>0
 | i+1=>lor (mL pp i) (sl (Z3o pp i) (sl i 3))
def mH (pp:LN):Nat->Nat
 | 0=>0
 | i+1=>lor (mH pp i) (sl (Z3o pp (sl i 4)) (sl i 3))
def mNP (r:Nat) (pS:LN):PT:=
 mPT (pS.map (fun c=>let pp:=(Z3p r c).map (fun i=>sl 1 i);(mL pp 16,mH pp 8)))
def nO (r c lo hi:Nat):Bool:=
 let pp:=(Z3p r c).map (fun i=>sl 1 i);beq lo (mL pp 16)&&beq hi (mH pp 8)
def bOk (b:Z4w) (cg:LN):Bool:=
 Z3U b&&(cg==Z4u b.gS)&&Z4v b.r b.gS cg
def cO (cf:Cfg):Bool:=
 let b:=cf.ba;(cf.mS != 0||cf.tg.isEmpty)&&(2*(cf.k*b.wo+b.ws.sum)< 65536)
def lN (loTab hiTab g:Nat):Nat:=
 land (sr loTab (sl (land g 15) 3)) 0x7f+
  land (sr hiTab (sl (sr g 4) 3)) 0x7f
def VPF (lo hi M:Nat):LN->Bool
 | []=>true
 | x :: xs=>if beq (land (sr M (lN lo hi x)) 1) 1 then VPF lo hi M xs else false
def aV (M1:Nat) (e1:LN) (M2:Nat) (e2:LN):List (Nat × Nat)->Bool
 | []=>true
 | (lo,hi):: rest=>if VPF lo hi M1 e1 then (if VPF lo hi M2 e2 then aV M1 e1 M2 e2 rest else false) else false
def mF (x:Nat):LN->Bool
 | []=>false
 | y :: ys=>if beq x y then true else mF x ys
def nF:LN->Bool
 | []=>true
 | x :: xs=>if mF x xs then false else nF xs
def YkF (n rj:Nat) (idxs ws gS:LN):Bool:=
 !(beq rj 0)&&beq idxs.length rj&&nF idxs&&idxs.all (fun i=>ble (i+1) n)&&gS.all (fun g=>mF (zJf idxs g) ws)
def Z3tF (mask:Nat) (gS Gs:LN) (idx:Nat):Option Nat:=
 if ble (idx+1) gS.length then gS[idx]? else (Gs[idx-gS.length]?).map (fun a=>a+mask)
def Z1OF (mask:Nat) (gS Gs:LN):LN->Option (LN)
 | []=>some []
 | idx :: rest=>match Z3tF mask gS Gs idx,Z1OF mask gS Gs rest with | some w,some ws=>some (w :: ws) | _,_=>none
def VLF (r k mS mask:Nat) (gS Gs:LN) (t:Nat) (wi:LN):Bool:=
 if beq t 0 then
  match wi with
  | [idx]=>if ble gS.length idx then match Gs[idx-gS.length]? with
   | some a=>!(beq k 0&&beq a 0)&&ble (k+zOo r a+1) mS | none=>false else false
  | _=>false
 else match Z1OF mask gS Gs wi with
  | none=>false
  | some ws=>let n:=r+k
   if beq t 34 then match ws with
    | [w0,w1,w2]=>!(beq w0 w1)&&!(beq w0 w2)&&!(beq w1 w2)&&beq (zOo n w0) 3&&beq (zOo n w1) 3&&beq (zOo n w2) 3&&ble (zOo n (Z5p (Z5p w0 w1) w2)) 5
    | _=>false
   else if beq t 35 then match ws with
    | [w0,w1,w2,w3]=>!(beq w0 w1)&&!(beq w0 w2)&&!(beq w0 w3)&&!(beq w1 w2)&&!(beq w1 w3)&&!(beq w2 w3)&&beq (zOo n w0) 3&&beq (zOo n w1) 3&&beq (zOo n w2) 3&&beq (zOo n w3) 3&&ble (zOo n (Z5p (Z5p (Z5p w0 w1) w2) w3)) 6
    | _=>false
   else YkF n (Z4Y t) (Z3R n t ws) ws (Z3Q t)
def Z4x (M y:Nat):Nat:=lor M (sl 1 y)
def VQ (n:Nat):Nat->bS->LN × bS
 | 0,bs=>([],bs)
 | m+1,bs=>let (v,bs1):=bs.rB n;let (vs,bs2):=VQ n m bs1;(v :: vs,bs2)
def Z4y:Nat->Nat
 | 0=>1|34=>3|35=>4|1=>3|2=>4|3=>4|4=>2|5=>3|6=>5|7=>6|8=>4|9=>4|10=>4|11=>3|12=>3|13=>3|14=>4|16=>3|17=>2|18=>2|20=>2|22=>2|24=>2|25=>1|26=>3|27=>3|28=>2|29=>2|30=>2|31=>2|32=>1|_=>0
def gPN (pt:PT):LN->Option (List (Nat × Nat))
 | []=>some []
 | pi :: pis=>match pt.get? pi,gPN pt pis with | some p,some ps=>some (p :: ps) | _,_=>none
def VR (cf:Cfg) (cg:LN) (sings:List (Nat × Nat)) (pt:PT) (pV mask:Nat):
 Nat->bS->Z4_->LN->Nat->LN->Nat->Nat->Option bS
 | 0,_,_,_,_,_,_,_=>none
 | fuel+1,bs,st,bx,ex,es,tP,tN=>
  let b:=cf.ba;let (b0,bs1):=bs.rB1
  match b0 with
  | 0=>if Z3T b.W cf.uC tP tN sings st then some bs1 else none
  | _=>let (b1,bs2):=bs1.rB1
   match b1 with
   | 0=>let (x,bs3):=bs2.rB b.r
    if beq (land (sr st.rM x) 1) 0 then none
    else match VR cf cg sings pt pV mask fuel bs3 (Xy b.W pV cg st x) (x :: bx) ex es tP tN with
     | none=>none
     | some bs4=>VR cf cg sings pt pV mask fuel bs4 (Z51 b.W pV st x) bx (Z4x ex x) (x :: es) tP tN
   | _=>let (b2,bs3):=bs2.rB1
    match b2 with
    | 0=>let (rep,bs4):=bs3.rB b.r
     if beq (land (sr st.rM rep) 1) 0 then none
     else let (bm,bs4a):=bs4.rB1;let (m,bs5):=if beq bm 0 then (1,bs4a) else bs4a.rB 6
      if beq m 0 then none
      else let (pis,bs6):=VQ b.pB m bs5
       match gPN pt pis with
       | none=>none
       | some pps=>if !(aV st.G bx ex es pps) then none
        else match VR cf cg sings pt pV mask fuel bs6 (Xy b.W pV cg st rep) (rep :: bx) ex es tP tN with
         | none=>none
         | some bs7=>let xs:=rep :: pps.map (fun pr=>lN pr.1 pr.2 rep)
          VR cf cg sings pt pV mask fuel bs7 (Z4t b.W pV st xs) bx (xs.foldl Z4x ex) (xs++es) tP tN
    | _=>let (b3,bs4):=bs3.rB1
     match b3 with
     | 0=>let (x,bs5):=bs4.rB b.r;let (tIdx,bs6):=bs5.rB cf.tB
      match cf.tg[tIdx]? with
      | some t=>if beq (land (sr st.rM x) 1) 0 then none
       else let st1:=Xy b.W pV cg st x;let wb:=Z3n (b.gS.length+st1.Gs.length);let (wi,bs7):=VQ wb (Z4y t) bs6
        if VLF b.r cf.k cf.mS mask b.gS st1.Gs t wi then
         VR cf cg sings pt pV mask fuel bs7 (Z51 b.W pV st x) bx (Z4x ex x) (x :: es) tP tN else none
      | none=>none
     | _=>let (tIdx,bs5):=bs4.rB cf.tB
      match cf.tg[tIdx]? with
      | none=>none
      | some t=>let wb:=Z3n (b.gS.length+st.Gs.length);let (wi,bs6):=VQ wb (Z4y t) bs5
       if VLF b.r cf.k cf.mS mask b.gS st.Gs t wi then some bs6 else none
def Z4z (r k wo W mS:Nat) (fN:Bool) (ws:LN):Nat × Nat:=
 (List.range (2 ^ r)).foldl (fun (m,sm) a=>let p:=zZf k wo ws a
  if (!fN||a != 0)&&(if k==0&&a==0 then true else mS≤ k+zOo r a)&&p < W then (m+2 ^ a,sm+(W-p)) else (m,sm)) (0,0)
def Z3V (r k wo W mS:Nat) (ws:LN):List (Nat × Nat):=Z4i k wo W mS ws (List.range r)
def Z3W (cf:Cfg) (cg:LN) (pV:Nat):Z4_ × LN:=
 let b:=cf.ba;let (rm0,rs0):=Z4z b.r cf.k b.wo b.W cf.mS cf.fN b.ws;let v0:Z4_:=⟨0,[],0,0,rm0,rs0⟩
 if cf.mS==0 then (v0,[])
 else if cf.k==0||cf.fE then (Xy b.W pV cg v0 0,[0])
 else if cf.k==12-b.r then let top:=sl 1 b.r - 1;(Xy b.W pV cg v0 top,[top])
 else (v0,[])
def Z3X (cf:Cfg) (cg:LN) (pt:PT) (words:LN) (tP tN:Nat):Bool:=
 let b:=cf.ba
 cO cf&&
  let pV:=mkPv cf.k b.wo b.ws (sl 1 b.r);let mask:=sl (sl 1 cf.k - 1) b.r;let (st0,bxs0):=Z3W cf cg pV
  (VR cf cg (Z3V b.r cf.k b.wo b.W cf.mS b.ws) pt pV mask 64 (bS.init words) st0 bxs0 0 [] tP tN).isSome
inductive Skel
 | leaf (idx:Nat)
 | branch (x:Nat) (s1 s0:Skel)
 | orbit (rep:Nat) (pis:LN) (s1 s0:Skel)
 | elim (x t:Nat) (wi:LN) (s0:Skel)
def hIn (lo hi:Nat):Skel->Bool
 | .leaf j=>ble lo j&&ble (j+1) hi
 | .branch _ s1 s0=>hIn lo hi s1||hIn lo hi s0
 | .orbit _ _ s1 s0=>hIn lo hi s1||hIn lo hi s0
 | .elim _ _ _ s0=>hIn lo hi s0
inductive ASk
 | empty
 | leaf (idx:Nat)
 | branch (x:Nat) (s1 s0:ASk)
 | orbit (rep:Nat) (pis:LN) (s1 s0:ASk)
 | elim (x t:Nat) (wi:LN) (s0:ASk)
def mAS (lo hi:Nat):Skel->ASk
 | .leaf j=>if ble lo j&&ble (j+1) hi then .leaf j else .empty
 | .branch x s1 s0=>
  match mAS lo hi s1,mAS lo hi s0 with
  | .empty,.empty=>.empty
  | a1,a0=>.branch x a1 a0
 | .orbit rep pis s1 s0=>
  match mAS lo hi s1,mAS lo hi s0 with
  | .empty,.empty=>.empty
  | a1,a0=>.orbit rep pis a1 a0
 | .elim x t wi s0=>
  match mAS lo hi s0 with
  | .empty=>.empty
  | a0=>.elim x t wi a0
def ZTG (cf:Cfg) (cg:LN) (sings:List (Nat × Nat)) (pt:PT) (pV mask tP tN lo:Nat) (wss:List (LN)):
 ASk->Z4_->LN->Nat->LN->Bool
 | .empty,_,_,_,_=>true
 | .leaf j,st,bx,ex,es=>
  match wss[j-lo]? with | none=>false | some ws=>(VR cf cg sings pt pV mask 64 (bS.init ws) st bx ex es tP tN).isSome
 | .branch x a1 a0,st,bx,ex,es=>
  if beq (land (sr st.rM x) 1) 0 then false
  else ZTG cf cg sings pt pV mask tP tN lo wss a1 (Xy cf.W pV cg st x) (x :: bx) ex es&&
   ZTG cf cg sings pt pV mask tP tN lo wss a0 (Z51 cf.W pV st x) bx (Z4x ex x) (x :: es)
 | .orbit rep pis a1 a0,st,bx,ex,es=>
  if beq (land (sr st.rM rep) 1) 0||pis.isEmpty then false
  else match gPN pt pis with
   | none=>false
   | some pps=>if !(aV st.G bx ex es pps) then false
    else ZTG cf cg sings pt pV mask tP tN lo wss a1 (Xy cf.W pV cg st rep) (rep :: bx) ex es&&
     match a0 with
     | .empty=>true
     | _=>let xs:=rep :: pps.map (fun pr=>lN pr.1 pr.2 rep)
      ZTG cf cg sings pt pV mask tP tN lo wss a0 (Z4t cf.W pV st xs) bx (xs.foldl Z4x ex) (xs++es)
 | .elim x t wi a0,st,bx,ex,es=>
  if beq (land (sr st.rM x) 1) 0||!(cf.tg.contains t) then false
  else let st1:=Xy cf.W pV cg st x
   if VLF cf.r cf.k cf.mS mask cf.gS st1.Gs t wi then
    ZTG cf cg sings pt pV mask tP tN lo wss a0 (Z51 cf.W pV st x) bx (Z4x ex x) (x :: es) else false
def ZT (cf:Cfg) (cg:LN) (pt:PT) (sk:Skel) (lo:Nat) (wss:List (LN)) (tP tN:Nat):Bool:=
 let b:=cf.ba
 cO cf&&
  let pV:=mkPv cf.k b.wo b.ws (sl 1 b.r);let mask:=sl (sl 1 cf.k - 1) b.r;let (st0,bxs0):=Z3W cf cg pV;let sings:=Z3V b.r cf.k b.wo b.W cf.mS b.ws
  ZTG cf cg sings pt pV mask tP tN lo wss (mAS lo (lo+wss.length) sk) st0 bxs0 0 []
def Z1T:Skel->LN
 | .leaf i=>[i]
 | .branch _ s1 s0=>Z1T s1++Z1T s0
 | .orbit _ _ s1 s0=>Z1T s1++Z1T s0
 | .elim _ _ _ s0=>Z1T s0
def pF (F:SS) (M K:SF):
 SS:=
 (F.filter (fun X=>X \ M=K)).image (fun X=>X∩M)
lemma pFS (F:SS) (M K:SF):
 ∀ A∈pF F M K,A⊆M:=by
 intro A hA;obtain ⟨X,_,rfl⟩:=qI.mp hA;exact inter_subset_right
lemma projFiber_op {F:SS} (hc:∀ X∈F,∀ Y∈F,X∪Y∈F)
 {M V:SF} (hVF:V∈F) (hVM:V⊆M) (K:SF):
 ∀ A∈pF F M K,A∪V∈pF F M K:=by
 intro A hA;obtain ⟨X,hXf,rfl⟩:=qI.mp hA;obtain ⟨hXF,hXK⟩:=qF.mp hXf;refine qI.mpr ⟨X∪V,qF.mpr ⟨hc X hXF V hVF,?_⟩,?_⟩
 · rw[union_sdiff_distrib,hXK,qi.mpr hVM,union_empty]
 · rw[qq,inter_eq_left.mpr hVM]
lemma ZB {e:Equiv.Perm (Fin 12)} {M K:SF}
 (he_out:∀ a∉M,e a=a) (F:SS):
 pF (F.image (Finset.image e.symm)) M K=
  (pF F M K).image (Finset.image e.symm):=by
 have v0:∀ a∉M,e.symm a=a:=fun a ha=>
  (e.symm_apply_eq).mpr (he_out a ha).symm
 have v1:∀ a∈M,e.symm a∈M:=by
  intro a ha;by_contra hnot;have:=he_out (e.symm a) hnot;rw[e.apply_symm_apply] at this;exact hnot (this ▸ ha)
 have v2:∀ X:SF,(X.image e.symm)\ M=X \ M:=by
  intro X;ext a;simp only[qSd,qI];constructor
  · rintro ⟨⟨b,hb,rfl⟩,hna⟩
    have v5:b∉M:=fun hm=>hna (v1 b hm);rw[v0 b v5];exact ⟨hb,v5⟩
  · rintro ⟨haX,hna⟩;exact ⟨⟨a,haX,v0 a hna⟩,hna⟩
 have v3:∀ X:SF,(X.image e.symm)∩M=(X∩M).image e.symm:=by
  intro X;ext a;simp only[mem_inter,qI];constructor
  · rintro ⟨⟨b,hb,rfl⟩,haM⟩
    have v4:b∈M:=by by_contra hnb;rw[v0 b hnb] at haM;exact hnb haM
    exact ⟨b,⟨hb,v4⟩,rfl⟩
  · rintro ⟨b,⟨hbX,v4⟩,rfl⟩;exact ⟨⟨b,hbX,rfl⟩,v1 b v4⟩
 ext A;simp only[pF,qI,qF];constructor
 · rintro ⟨Y,⟨⟨X,hXF,rfl⟩,hYK⟩,rfl⟩
   rw[v2] at hYK;rw[v3];exact ⟨X∩M,⟨X,⟨hXF,hYK⟩,rfl⟩,rfl⟩
 · rintro ⟨B,⟨⟨X,⟨hXF,hXK⟩,rfl⟩,rfl⟩⟩
   exact ⟨X.image e.symm,⟨⟨X,hXF,rfl⟩,by rw[v2,hXK]⟩,v3 X⟩
structure Z3Z (cf:Cfg) (ms ks:LF) (wf:WF)
 (F H:SS):Prop where
 hnF:(ms++ks).Nodup
 hr:ms.length=cf.r
 hk:ks.length=cf.k
 hws:cf.ws=ms.map wf
 hF_uc:∀ X∈F,∀ Y∈F,X∪Y∈F
 hFl:cf.mS≠0->∀ X∈F,X.Nonempty->cf.mS≤ X.card
 hFp:∀ t∈cf.tg,t≠0->¬ Z3r t F
 hgf:cf.mS≠0->∀ g∈cf.gS,Z3L ms g∈F
 hHe:H=pF F ms.toFinset ks.toFinset
 hHo:∀ g∈cf.gS,∀ A∈H,A∪Z3L ms g∈H
 hH_allowed:cf.mS≠0->∀ A∈H,
  (cf.k=0∧A=∅)∨cf.mS≤ cf.k+A.card
 hcp:cf.uC≠0->
  (H.filter (fun A=>A.card=1)).card≤ (if cf.uC=2 then 3 else 2)
 hno0:cf.fN=true->∅∉H
lemma XC {cf:Cfg} {ms ks:LF} {wf:WF}
 {F H:SS} (hs:Z3Z cf ms ks wf F H)
 {p:LN} (hv:Z3O cf.r p=true)
 (hg:Qb cf.gS p=true):
 let v0:ms.Nodup:=(qV.mp hs.hnF).1;let e:=Z3P ms v0 p (hs.hr ▸ hv)
 Z3Z cf ms ks wf (F.image (Finset.image e.symm)) (H.image (Finset.image e.symm)):=by
 intro v0 e;have v3:∀ a∉ms.toFinset,e a=a:=fun a ha=>
  Ya ms v0 p (hs.hr ▸ hv) (fun hm=>ha (qM.mpr hm))
 refine ⟨hs.hnF,hs.hr,hs.hk,hs.hws,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
 · intro X' hX' Y' hY';obtain ⟨X,hXF,rfl⟩:=qI.mp hX';obtain ⟨Y,hYF,rfl⟩:=qI.mp hY';rw[← image_union];exact qI.mpr ⟨X∪Y,hs.hF_uc X hXF Y hYF,rfl⟩
 · intro hms X' hX' hne;obtain ⟨X,hXF,rfl⟩:=qI.mp hX';rw[qK _ e.symm.injective];exact hs.hFl hms X hXF (by simpa using hne)
 · intro t ht htn hp;exact hs.hFp t ht htn (Yj e.symm hp)
 · intro hms g hgg
   have v4:Z1J p g∈cf.gS:=by simpa[qCm] using (qE.mp hg) g hgg
   have v5:Z3L ms (Z1J p g)∈F:=hs.hgf hms _ v4;have v1:(Z3L ms g).image e=Z3L ms (Z1J p g):=
    ZK ms v0 p (hs.hr ▸ hv) g
   have v2:((Z3L ms g).image e).image e.symm=Z3L ms g:=by ext x;simp
   rw[← v2,v1];exact qI.mpr ⟨_,v5,rfl⟩
 · rw[hs.hHe,ZB v3]
 · intro g hgg A' hA';obtain ⟨A,hAH,rfl⟩:=qI.mp hA'
   have v4:Z1J p g∈cf.gS:=by simpa[qCm] using (qE.mp hg) g hgg
   have v1:(Z3L ms g).image e=Z3L ms (Z1J p g):=
    ZK ms v0 p (hs.hr ▸ hv) g
   have v2:((Z3L ms g).image e).image e.symm=Z3L ms g:=by ext x;simp
   have hU:A∪Z3L ms (Z1J p g)∈H:=hs.hHo _ v4 A hAH;rw[← v2,v1,← image_union];exact qI.mpr ⟨_,hU,rfl⟩
 · intro hms A' hA';obtain ⟨A,hAH,rfl⟩:=qI.mp hA';rw[qK _ e.symm.injective,image_eq_empty];exact hs.hH_allowed hms A hAH
 · intro huc;have v6:(H.image (Finset.image e.symm)).filter (fun A=>A.card=1)=
    (H.filter (fun A=>A.card=1)).image (Finset.image e.symm):=by
    ext A;simp only[qF,qI];constructor
    · rintro ⟨⟨B,hBH,rfl⟩,hc1⟩
      rw[qK _ e.symm.injective] at hc1;exact ⟨B,⟨hBH,hc1⟩,rfl⟩
    · rintro ⟨B,⟨hBH,hc1⟩,rfl⟩
      exact ⟨⟨B,hBH,rfl⟩,by rw[qK _ e.symm.injective];exact hc1⟩
   rw[v6,qK _ (image_injective e.symm.injective)];exact hs.hcp huc
 · intro hne h0;obtain ⟨A,hAH,hAe⟩:=qI.mp h0;exact hs.hno0 hne ((image_eq_empty.mp hAe)▸ hAH)
def Z3_ (r k wo W mS:Nat) (fN:Bool) (ws:LN) (a:Nat):Bool:=
 a < 2 ^ r&&(!fN||a != 0)&&
  (if k==0&&a==0 then true else mS≤ k+Z5o r a)&&Z4Z k wo ws a < W
lemma Ye (P:Nat->Bool) (f:Nat->Nat):
 ∀ (l:LN) (m sm:Nat),
  l.Nodup->(∀ a∈l,m.testBit a=false)->
  let res:=l.foldl (fun (m,sm) a=>
   if P a then (m+2 ^ a,sm+f a) else (m,sm)) (m,sm)
  (∀ x,res.1.testBit x=true↔m.testBit x=true∨(x∈l∧P x=true))∧
  res.2=sm+∑ x∈l.toFinset.filter (fun a=>P a=true),f x
 | [],_,_,_,_=>by simp
 | a :: as,m,sm,hnd,hfresh=>by
  rw[q4] at hnd;have v3:m.testBit a=false:=hfresh a qG;dsimp only[List.foldl_cons];by_cases hPa:P a=true
  · simp only[hPa,↓reduceIte]
    have v2:∀ y∈as,(m+2 ^ a).testBit y=false:=by
     intro y hy;rw[ZF a m y v3];have v5:y≠a:=fun h=>hnd.1 (h ▸ hy);simp[v5,hfresh y (qO a hy)]
    have ih:=Ye P f as (m+2 ^ a) (sm+f a) hnd.2 v2;refine ⟨fun x=>?_,?_⟩
    · rw[ih.1 x,ZF a m x v3]
      by_cases hxa:x=a
      · subst hxa;simp[hPa]
      · simp only[qOr,qD,qC,hxa,false_or]
    · have v0:(a :: as).toFinset.filter (fun x=>P x=true)=
       insert a (as.toFinset.filter (fun x=>P x=true)):=by
       ext y;simp only[qF,qM,qC,qo];constructor
       · rintro ⟨rfl|hy,hPy⟩;left;rfl;right;exact ⟨hy,hPy⟩
       · rintro (rfl|⟨hy,hPy⟩);exact ⟨Or.inl rfl,hPa⟩;exact ⟨Or.inr hy,hPy⟩
      have v4:a∉as.toFinset.filter (fun x=>P x=true):=fun h=>
       hnd.1 (qM.mp (qF.mp h).1)
      rw[ih.2,v0,sum_insert v4];omega
  · have v1:P a=false:=qEf.mpr hPa;simp only[v1,qFl,↓reduceIte];have ih:=Ye P f as m sm hnd.2
     (fun y hy=>hfresh y (qO a hy))
    refine ⟨fun x=>?_,?_⟩
    · rw[ih.1 x,qC];constructor
      · rintro (hm|⟨hx,hPx⟩);exact Or.inl hm;exact Or.inr ⟨Or.inr hx,hPx⟩
      · rintro (hm|⟨rfl|hx,hPx⟩)
        · exact Or.inl hm
        · exact False.elim (false_ne_true (v1 ▸ hPx))
        · exact Or.inr ⟨hx,hPx⟩
    · have v0:(a :: as).toFinset.filter (fun x=>P x=true)=
       as.toFinset.filter (fun x=>P x=true):=by
       ext y;simp only[qF,qM,qC];constructor
       · rintro ⟨rfl|hy,hPy⟩
         · exact False.elim (false_ne_true (v1 ▸ hPy))
         · exact ⟨hy,hPy⟩
       · rintro ⟨hy,hPy⟩;exact ⟨Or.inr hy,hPy⟩
      rw[ih.2,v0]
lemma VT (r k wo W mS:Nat) (fN:Bool) (ws:LN):
 let rm:=Z4z r k wo W mS fN ws
 (∀ a,rm.1.testBit a=true↔Z3_ r k wo W mS fN ws a=true)∧
 rm.2=∑ a∈(Finset.range (2 ^ r)).filter (fun a=>rm.1.testBit a),
  (W-Z4Z k wo ws a):=by
 let P:=fun a=>(!fN||a != 0)&&
  (if k==0&&a==0 then true else mS≤ k+Z5o r a)&&Z4Z k wo ws a < W
 have h:=Ye P (fun a=>W-Z4Z k wo ws a)
  (List.range (2 ^ r)) 0 0 List.nodup_range (fun _ _=>zero_testBit _)
 have v0:Z4z r k wo W mS fN ws=
  (List.range (2 ^ r)).foldl (fun (m,sm) a=>
   if P a then (m+2 ^ a,sm+(W-Z4Z k wo ws a)) else (m,sm)) (0,0):=by
  dsimp[Z4z];simp only[z4e,z5o,P]
 change let rm:=Z4z r k wo W mS fN ws;_;refine ⟨fun a=>?_,?_⟩
 · rw[v0,h.1 a];simp only[zero_testBit,qFl,false_or,qR,Z3_,P,
    qA,qD]
   tauto
 · rw[v0,h.2,zero_add]
   congr 1;ext a;simp only[qF,qM,qR,qMr];have h1:=h.1 a;simp only[zero_testBit,qFl,false_or,qR] at h1;rw[h1];tauto
lemma Z40:∀ r,Z5o r 0=0
 | 0=>rfl
 | r+1=>by simp[Z5o,Z40 r]
lemma Z3w {r k wo W mS:Nat} {fne:Bool} {ws:LN} {a:Nat}
 (h:Z3_ r k wo W mS fne ws a=true):a < 2 ^ r:=by
 simp only[Z3_,qA,qD] at h;exact h.1.1.1
lemma Z1U {r k wo W mS:Nat} {fne:Bool} {ws:LN} {a:Nat}
 (h:Z3_ r k wo W mS fne ws a=true):Z4Z k wo ws a < W:=by
 simp only[Z3_,qA,qD] at h;exact h.2
lemma VU {r k wo W mS:Nat} {fne:Bool} {ws:LN} {a:Nat}
 (hpop:Z5o r a=1) (h:Z3_ r k wo W mS fne ws a=true):mS≤ k+1:=by
 have v1:a≠0:=by intro h0;subst h0;simp[Z40] at hpop
 simp only[Z3_,qA,qD] at h;have h1:=h.1.2
 have v0:¬ ((k==0)=true∧(a==0)=true):=by simp[v1]
 rw[if_neg v0,qD] at h1;omega
lemma VV {cf:Cfg} {ms ks:LF} {wf:WF}
 {F H:SS} (hs:Z3Z cf ms ks wf F H)
 {A:SF} (hAH:A∈H)
 (hlt:Z4Z cf.k cf.wo (ms.map wf) (Z3M ms A)< cf.W):
 Z3_ cf.r cf.k cf.wo cf.W cf.mS cf.fN cf.ws
  (Z3M ms A)=true:=by
 have v0:ms.Nodup:=(qV.mp hs.hnF).1;have v2:A⊆ms.toFinset:=pFS F ms.toFinset ks.toFinset A (hs.hHe ▸ hAH);have v3:Z3M ms A < 2 ^ cf.r:=hs.hr ▸ VK ms A;simp only[Z3_,qA,qD];refine ⟨⟨⟨v3,?_⟩,?_⟩,hs.hws ▸ hlt⟩
 · cases hne:cf.fN
   · simp
   · have v4:A≠∅:=fun hAe=>hs.hno0 hne (hAe ▸ hAH)
     have v1:Z3M ms A≠0:=fun hm=>v4 (by
      rw[← ZH ms v0 v2,hm,Xr])
     simp[v1]
 · by_cases hms:cf.mS=0
   · split_ifs
     · rfl
     · rw[qD,hms];exact zero_le _
   · have v5:=hs.hH_allowed hms A hAH
     have hcard:Z5o cf.r (Z3M ms A)=A.card:=by rw[← hs.hr,← Xs ms v0,ZH ms v0 v2]
     rcases v5 with ⟨hk0,hAe⟩|hle
     · have v1:Z3M ms A=0:=by
        rw[hAe];simpa[Xr] using ZI ms v0 (two_pow_pos _)
       simp[hk0,v1]
     · split_ifs
       · rfl
       · rw[qD];omega
lemma Y2 {cf:Cfg} {ms ks:LF} {wf:WF}
 {F H:SS} (hs:Z3Z cf ms ks wf F H):
 ∀ A∈H,∀ B∈H,A∪B∈H:=by
 intro A hA B hB;rw[hs.hHe] at hA hB ⊢;obtain ⟨X,hXf,rfl⟩:=qI.mp hA;obtain ⟨Y,hYf,rfl⟩:=qI.mp hB;obtain ⟨hXF,hXK⟩:=qF.mp hXf;obtain ⟨hYF,hYK⟩:=qF.mp hYf;refine qI.mpr ⟨X∪Y,qF.mpr ⟨hs.hF_uc X hXF Y hYF,?_⟩,?_⟩
 · rw[union_sdiff_distrib,hXK,hYK,union_idempotent]
 · exact qq X Y ms.toFinset
structure Z4m (cf:Cfg) (ms:LF) (H:SS) (cg:LN) (st:Z4_) (bx:LN) (ex:Nat) (es:LN):Prop where
 core:Z4d cf.r cf.k cf.wo cf.W cf.ws ms H es
  (Z3_ cf.r cf.k cf.wo cf.W cf.mS cf.fN cf.ws) st
 s_cg:∀ a∈st.Gs,∀ g∈cg,(a|||g)∈st.Gs
 s_uc:∀ a∈st.Gs,∀ b∈st.Gs,(a|||b)∈st.Gs
 bL:∀ y∈bx,y < 2 ^ cf.r
 bG:∀ (p Ms:LN),Z3O cf.r p=true->Qb cf.gS p=true->
  (∀ a∈Ms,∀ g∈cg,(a|||g)∈Ms)->(∀ a∈Ms,∀ b∈Ms,(a|||b)∈Ms)->
  (∀ y∈bx,Z1J p y∈Ms)->∀ a∈st.Gs,Z1J p a∈Ms
 eL:∀ y∈es,y < 2 ^ cf.r
 eB:∀ a,ex.testBit a=true↔a∈es
 eH:∀ y∈es,Z3L ms y∉H
lemma YN (M y a:Nat):(Z4x M y).testBit a=true↔M.testBit a=true∨a=y:=by
 dsimp[Z4x];change (M|||1 <<< y).testBit a=true↔_;rw[testBit_lor,qSl,qZ,qk];by_cases ha:a=y
 · subst ha;simp
 · simp[ha,Ne.symm ha]
lemma Qd (xs:LN) (ex a:Nat):(xs.foldl Z4x ex).testBit a=true↔ex.testBit a=true∨a∈xs:=by
 induction xs generalizing ex with | nil=>simp | cons x xs ih=>simp only[List.foldl_cons,qC];rw[ih (Z4x ex x),YN];tauto
lemma XA:∀ {r:Nat} {p:LN} {x:Nat},(∀ j∈p,j < r)->Z1J p x < 2 ^ r
 | _,[],_,_=>by dsimp[Z1J];exact two_pow_pos _
 | r,j :: js,x,hp=>by
  have hj:j < r:=hp j qG;have v0:=XA (r:=r) (p:=js) (x:=x/2) (fun w hw=>hp w (qO j hw));dsimp[Z1J];apply q5 _ v0;split_ifs
  · exact pow_lt_pow_right (by omega) hj
  · exact two_pow_pos _
lemma zJl:∀ (p:LN) (u v:Nat),Z1J p (u|||v)=Z1J p u|||Z1J p v
 | [],u,v=>by simp[Z1J]
 | i :: is,u,v=>by
  dsimp[Z1J]
  have hd:(u|||v)/2=u/2|||v/2:=q8 fun j=>by change ((u|||v)>>> 1).testBit j=(u >>> 1|||v >>> 1).testBit j;simp[testBit_shiftRight]
  have hm:(u|||v)% 2=1↔(u % 2=1∨v % 2=1):=by
   have tb:∀ a:Nat,a % 2=1↔a.testBit 0=true:=fun a=>by rw[testBit_zero];cases qn a with | inl h=>simp[h] | inr h=>simp[h]
   rw[tb,tb,tb,testBit_lor,qOr]
  rw[hd,zJl is];by_cases hu:u % 2=1 <;> by_cases hv:v % 2=1
  · have huv:(u|||v)% 2=1:=hm.mpr (Or.inl hu);simp only[hu,hv,huv,↓reduceIte];apply q8;intro j;simp only[testBit_lor];cases (2 ^ i).testBit j <;> cases (Z1J is (u/2)).testBit j <;> cases (Z1J is (v/2)).testBit j <;> rfl
  · have huv:(u|||v)% 2=1:=hm.mpr (Or.inl hu);simp only[hu,hv,huv,↓reduceIte];apply q8;intro j;simp only[testBit_lor,zero_testBit];cases (2 ^ i).testBit j <;> cases (Z1J is (u/2)).testBit j <;> cases (Z1J is (v/2)).testBit j <;> rfl
  · have huv:(u|||v)% 2=1:=hm.mpr (Or.inr hv);simp only[hu,hv,huv,↓reduceIte];apply q8;intro j;simp only[testBit_lor,zero_testBit];cases (2 ^ i).testBit j <;> cases (Z1J is (u/2)).testBit j <;> cases (Z1J is (v/2)).testBit j <;> rfl
  · have huv:¬((u|||v)% 2=1):=fun h=>by rcases hm.mp h with h1|h1<;>contradiction
    simp only[hu,hv,huv,↓reduceIte];apply q8;intro j;simp only[testBit_lor,zero_testBit];rfl
lemma Z3v {b:Z4w} (hv:Z3U b=true):b.r≤ 7:=by dsimp[Z3U] at hv;simp only[qA,ble_eq] at hv;exact hv.1.1.1
lemma Qe {b:Z4w} (hv:Z3U b=true):∀ g∈b.gS,g < 2 ^ b.r:=by dsimp[Z3U] at hv;simp only[qA,qE,ble_eq] at hv;intro g hg;have:=hv.1.2 g hg;rw[qSl,qZ] at this;omega
lemma XB {b:Z4w} (hv:Z3U b=true) {c:Nat} (hc:c∈b.pS):let p:=Z3p b.r c;Z3O b.r p=true∧Z3q b.ws p=true∧Qb b.gS p=true:=by dsimp[Z3U] at hv;simp only[qA,qE,zOe,zqe,qBe] at hv;have h:=hv.2 c hc;exact ⟨h.1.1,h.1.2,h.2⟩
lemma ZN {cf:Cfg} (ht:(cf.mS != 0||cf.tg.isEmpty)=true) (hms:cf.mS=0):cf.tg=[]:=by simp only[qOr,bne_iff_ne,ne_eq,List.isEmpty_iff] at ht;exact ht.resolve_left (fun h=>h hms)
lemma ZO {α β:Type*} (P:β->Prop) (f:List β->α->List β) (l₀:List α) (hf:∀ acc x,x∈l₀->(∀ y∈acc,P y)->∀ y∈f acc x,P y):
 ∀ (l:List α) (acc:List β),(∀ x∈l,x∈l₀)->(∀ y∈acc,P y)->∀ y∈l.foldl f acc,P y
 | [],_, _,h=>h
 | a :: as,acc,hl,h=>ZO P f l₀ hf as (f acc a) (fun x hx=>hl x (qO a hx)) (hf acc a (hl a qG) h)
lemma zJz {r:Nat} {gS cg:LN} {p:LN} (hg_lt:∀ g∈gS,g < 2 ^ r) (_hp:Z3O r p=true) (hqb:Qb gS p=true) (hcg:Z4v r gS cg=true):
 ∀ g∈Z4u gS,Z1J p g∈cg:=by
 have huc:=VM hcg;let P:=fun g=>g < 2 ^ r∧Z1J p g∈cg;have v3:2 ^ r < 256:=by have:2 ^ r≤ 2 ^ 7:=qPl (by omega) huc.1;omega
 have v2:∀ a b,P a->P b->P (or7 a b):=fun a b ha hb=>by rw[Z3m (lt_trans ha.1 v3) (lt_trans hb.1 v3)];refine ⟨q5 ha.1 hb.1,?_⟩;rw[zJl];exact huc.2.2.2 _ ha.2 _ hb.2
 have vbase:∀ g∈gS,P g:=fun g hg=>⟨hg_lt g hg,huc.2.2.1 _ (by simpa[qCm] using (qE.mp hqb) g hg)⟩
 have v0:∀ (acc:LN) u,P u->(∀ y∈acc,P y)->∀ y∈(if acc.contains u then acc else acc++[u]),P y:=fun acc u hu hacc y hy=>by
  split_ifs at hy
  · exact hacc y hy
  · rcases mem_append.mp hy with hy'|hy'
    · exact hacc y hy'
    · simp only[List.mem_singleton] at hy';exact hy' ▸ hu
 have v1:∀ (cur:LN),(∀ z∈cur,P z)->∀ y∈Z1P gS cur,P y:=fun cur hcur=>by
  let f1:=fun acc z=>gS.foldl (fun acc2 g=>let u:=or7 z g;if acc2.contains u then acc2 else acc2++[u]) acc;let c1:=cur.foldl f1 cur;have v4:∀ y∈c1,P y:=ZO P f1 cur (fun acc z hz hacc=>ZO P _ gS (fun acc2 g hg hacc2=>v0 acc2 (or7 z g) (v2 z g (hcur z hz) (vbase g hg)) hacc2) gS acc (fun _ h=>h) hacc) cur cur (fun _ h=>h) hcur;exact ZO P _ c1 (fun acc z hz hacc=>ZO P _ c1 (fun acc2 w hw hacc2=>v0 acc2 (or7 z w) (v2 z w (v4 z hz) (v4 w hw)) hacc2) c1 acc (fun _ h=>h) hacc) c1 c1 (fun _ h=>h) v4
 let c0:=gS.foldl (fun acc g=>if acc.contains g then acc else acc++[g]) []
 have v6:∀ y∈c0,P y:=ZO P _ gS (fun acc g hg hacc=>v0 acc g (vbase g hg) hacc) gS [] (fun _ h=>h) (fun _ h=>by simp at h)
 intro g hg;exact (v1 _ (v1 c0 v6) g hg).2
lemma Z3x {r:Nat} (hr:r≤ 7) {ms:LF} {H:SS} {gS:LN} (hg_lt:∀ g∈gS,g < 2 ^ r) (hg_op:∀ g∈gS,∀ A∈H,A∪Z3L ms g∈H):
 ∀ g∈Z4u gS,∀ A∈H,A∪Z3L ms g∈H:=by
 let P:=fun g=>g < 2 ^ r∧∀ A∈H,A∪Z3L ms g∈H;have v3:2 ^ r < 256:=by have:2 ^ r≤ 2 ^ 7:=qPl (by omega) hr;omega
 have v2:∀ a b,P a->P b->P (or7 a b):=fun a b ha hb=>by rw[Z3m (lt_trans ha.1 v3) (lt_trans hb.1 v3)];refine ⟨q5 ha.1 hb.1,fun A hA=>?_⟩;rw[Q3,← union_assoc];exact hb.2 _ (ha.2 A hA)
 have v0:∀ (acc:LN) u,P u->(∀ y∈acc,P y)->∀ y∈(if acc.contains u then acc else acc++[u]),P y:=fun acc u hu hacc y hy=>by
  split_ifs at hy
  · exact hacc y hy
  · rcases mem_append.mp hy with hy'|hy'
    · exact hacc y hy'
    · simp only[List.mem_singleton] at hy';exact hy' ▸ hu
 have v1:∀ (cur:LN),(∀ z∈cur,P z)->∀ y∈Z1P gS cur,P y:=fun cur hcur=>by
  let f1:=fun acc z=>gS.foldl (fun acc2 g=>let u:=or7 z g;if acc2.contains u then acc2 else acc2++[u]) acc;let c1:=cur.foldl f1 cur;have v4:∀ y∈c1,P y:=ZO P f1 cur (fun acc z hz hacc=>ZO P _ gS (fun acc2 g hg hacc2=>v0 acc2 (or7 z g) (v2 z g (hcur z hz) ⟨hg_lt g hg,hg_op g hg⟩) hacc2) gS acc (fun _ h=>h) hacc) cur cur (fun _ h=>h) hcur;exact ZO P _ c1 (fun acc z hz hacc=>ZO P _ c1 (fun acc2 w hw hacc2=>v0 acc2 (or7 z w) (v2 z w (v4 z hz) (v4 w hw)) hacc2) c1 acc (fun _ h=>h) hacc) c1 c1 (fun _ h=>h) v4
 let c0:=gS.foldl (fun acc g=>if acc.contains g then acc else acc++[g]) []
 have v6:∀ y∈c0,P y:=ZO P _ gS (fun acc g hg hacc=>v0 acc g ⟨hg_lt g hg,hg_op g hg⟩ hacc) gS [] (fun _ h=>h) (fun _ h=>by simp at h)
 intro g hg A hA;exact (v1 _ (v1 c0 v6) g hg).2 A hA
def Z3oO:LN->Nat->Nat | [],_=>0 | p :: ps,g=>(if g % 2==1 then p else 0)+Z3oO ps (g/2)
lemma Z3oO_z:∀ pp,Z3oO pp 0=0 | []=>rfl | _ :: pp=>by simp[Z3oO,Z3oO_z pp]
lemma Z3o_O:∀ ps g,Z3o ps g=Z3oO ps g
 | [],0=>rfl | [],g+1=>rfl | p :: ps,0=>by rw[Z3o_eq_orig,Z3oO_z];cases ps <;> rfl
 | p :: ps,g+1=>by rw[Z3o_eq_orig];dsimp[Z3oO];rw[Z3o_O ps ((g+1)/2)]
lemma zOp:∀ (k:Nat) (pp:LN) (a b:Nat),a < 2 ^ k->Z3oO pp (a+2 ^ k*b)=Z3oO pp a+Z3oO pp (2 ^ k*b)
 | 0,pp,a,b,ha=>by have:a=0:=(by omega);subst this;simp[Z3oO_z]
 | k+1,[],_,_,_=>rfl
 | k+1,p :: ps,a,b,ha=>by
  dsimp[Z3oO];have hm:(a+2 ^ (k+1)*b)% 2=a % 2:=by rw[qW,qY _ 2,Nat.mul_assoc];omega
  have hm0:(2 ^ (k+1)*b)% 2=0:=by rw[qW,qY _ 2,Nat.mul_assoc];omega
  have hd1:(a+2 ^ (k+1)*b)/2=a/2+2 ^ k*b:=by rw[qW,qY _ 2,Nat.mul_assoc];omega
  have hd2:(2 ^ (k+1)*b)/2=2 ^ k*b:=by rw[qW,qY _ 2,Nat.mul_assoc];omega
  rw[hm,hm0,hd1,hd2,zOp k ps (a/2) b (by omega)];simp;omega
lemma mT8_lt (f:Nat->Nat) (hf:∀ i,f i < 128):∀ (n:Nat),(Nat.rec 0 (fun m acc=>lor acc (sl (f m) (8*m))) n:Nat)< 2 ^ (8*n):=by
 intro n;induction n with | zero=>simp | succ n ih=>
  dsimp;apply q5;· exact qLt ih (qPl (by omega) (by omega))
  · change (f n)<<< (8*n)< 2 ^ (8*(n+1));rw[qSl,Nat.mul_add,pow_add,Nat.mul_one,qY (2 ^ (8*n)) (2 ^ 8)];exact Nat.mul_lt_mul_of_pos_right (lt_trans (hf n) (by decide:128 < 256)) (two_pow_pos _)
lemma mT8_lu (f:Nat->Nat) (hf:∀ i,f i < 128):∀ (n u:Nat),u < n->
 land (sr (Nat.rec 0 (fun m acc=>lor acc (sl (f m) (8*m))) n) (sl u 3)) 0x7f=f u:=by
 intro n;induction n with | zero=>intro u hu;omega | succ n ih=>
  intro u hu;apply q8;intro i;dsimp;change (((Nat.rec 0 (fun m acc=>acc|||f m <<< (8*m)) n|||f n <<< (8*n))>>> (u <<< 3))&&& 0x7f).testBit i=(f u).testBit i;rw[testBit_land,testBit_shiftRight,testBit_lor,testBit_shiftLeft]
  have hshift:u <<< 3=8*u:=by rw[qSl];omega
  rw[hshift];by_cases hi:i < 7
  · have hmask:Nat.testBit 0x7f i=true:=by have:(0x7f:Nat)=2 ^ 7-1:=rfl;rw[this,Nat.testBit_two_pow_sub_one];simp[hi]
    rw[hmask,Bool.and_true];rcases Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp hu) with hun|rfl
    · have hlt:¬ (8*n≤ 8*u+i):=by omega
      simp only[hlt,decide_false,Bool.false_and,Bool.or_false];have:=ih u hun;have tb:=congrArg (fun x=>Nat.testBit x i) this;change ((Nat.rec 0 (fun m acc=>acc|||f m <<< (8*m)) n >>> (u <<< 3))&&& 0x7f).testBit i=(f u).testBit i at tb;simpa[testBit_land,testBit_shiftRight,hshift,hmask] using tb
    · have hp1:(Nat.rec 0 (fun m acc=>acc|||f m <<< (8*m)) u:Nat).testBit (8*u+i)=false:=
       qg (qLt (mT8_lt f hf u) (qPl (by omega) (by omega)))
      have hle:8*u≤ 8*u+i:=by omega
      simp[hp1,hle]
  · have h7:7≤ i:=by omega
    have hmask:Nat.testBit 0x7f i=false:=qg (qLt (by decide:0x7f < 2 ^ 7) (qPl (by omega) h7));have hfi:Nat.testBit (f u) i=false:=qg (qLt (hf u) ((by rfl:128=2 ^ 7)▸ qPl (by omega) h7));simp[hmask,hfi]
lemma mLo_r (pp:LN):∀ i,mL pp i=Nat.rec 0 (fun m acc=>lor acc (sl (Z3o pp m) (8*m))) i
 | 0=>rfl
 | i+1=>by
  dsimp[mL];rw[mLo_r pp i];change _||| _ <<< (i <<< 3)=_||| _ <<< (8*i)
  have h:i <<< 3=8*i:=by rw[qSl];omega
  rw[h];rfl
lemma mHi_r (pp:LN):∀ i,mH pp i=Nat.rec 0 (fun m acc=>lor acc (sl (Z3o pp (16*m)) (8*m))) i
 | 0=>rfl
 | i+1=>by
  dsimp[mH];rw[mHi_r pp i];change _|||Z3o pp (i <<< 4) <<< (i <<< 3)=_|||Z3o pp (16*i) <<< (8*i)
  have h1:i <<< 4=16*i:=by rw[qSl];omega
  have h2:i <<< 3=8*i:=by rw[qSl];omega
  rw[h1,h2];rfl
lemma NOkS {r c lo hi:Nat} (hr:r≤ 7) (hp:Z3O r (Z3p r c)=true) (hn:nO r c lo hi=true):∀ x < 2 ^ r,lN lo hi x=Z1J (Z3p r c) x:=by
 simp only[nO,qA,beq_eq] at hn;let p:=Z3p r c;let pp:=p.map (fun i=>sl 1 i);have hp':Z3O r p=true:=hp;simp only[Z3O,qA,qD,qE] at hp'
 have hpp_eq:pp=p.map (fun i=>2 ^ i):=map_congr_left (fun i _=>by change 1 <<< i=2 ^ i;rw[qSl,qZ])
 have hbd:∀ g,Z3o pp g < 128:=fun g=>by rw[hpp_eq,Z3 p hp'.1.2 g];exact qLt (XA hp'.2) (qPl (by omega) hr)
 intro x hx;have hlo_lt:land x 15 < 16:=Nat.and_lt_two_pow x (by decide:15 < 2 ^ 4)
 have hhi_lt:sr x 4 < 8:=by have:=qLt hx (qPl (by omega) hr);change x >>> 4 < 8;rw[qSr];omega
 have hlo_ok:=mT8_lu (Z3o pp) hbd 16 (land x 15) hlo_lt;have hhi_ok:=mT8_lu (fun m=>Z3o pp (16*m)) (fun m=>hbd (16*m)) 8 (sr x 4) hhi_lt;rw[← mLo_r] at hlo_ok;rw[← mHi_r] at hhi_ok;rw[hn.1,hn.2];change lN (mL pp 16) (mH pp 8) x=Z1J p x;unfold lN;rw[hlo_ok,hhi_ok]
 have hdec:x=land x 15+16*(sr x 4):=by
  change x=(x &&& 15)+16*(x >>> 4);rw[qSr];have:x &&& 15=x % 16:=by have:(15:Nat)=2^4-1:=rfl;rw[this,qAm]
  omega
 have h16:(16:Nat)=2 ^ 4:=rfl
 have hsp:Z3o pp x=Z3o pp (land x 15)+Z3o pp (16*(sr x 4)):=by
  rw[Z3o_O,Z3o_O,Z3o_O];conv_lhs=>rw[hdec]
  simpa only [h16] using zOp 4 pp (land x 15) (sr x 4) hlo_lt
 rw[← hsp,hpp_eq,Z3 p hp'.1.2 x]
lemma p4l {α:Type}:∀ (ts:List (P4 α)),ts.length≤ 4*(p4 ts).length
 | _ :: _ :: _ :: _ :: rest=>by have:=p4l rest;dsimp[p4];omega
 | [_,_,_]=>by simp[p4] | [_,_]=>by simp[p4] | [_]=>by simp[p4] | []=>by simp[p4]
lemma p4g {α:Type} (sh:Nat) (xs:List α):
 ∀ (ts:List (P4 α)) (off:Nat),
  (∀ k i v,P4.gA sh (ts.getD k .empty) i=some v->xs[off+k*2 ^ sh+i % 2 ^ sh]?=some v)->
  ∀ k i v,P4.gA (sh+2) ((p4 ts).getD k .empty) i=some v->
   xs[off+k*2 ^ (sh+2)+i % 2 ^ (sh+2)]?=some v:=by
 intro ts off hts k
 have hq:∀ i,land (sr i sh) 3=(i / 2 ^ sh)% 4:=fun i=>by
  change (i >>> sh)&&& (2 ^ 2-1)=_;rw[qSr,qAm]
 have hi2:∀ i,i % 2 ^ (sh+2)=((i / 2 ^ sh)% 4)*2 ^ sh+i % 2 ^ sh:=fun i=>by
  have h1:=div_add_mod (i / 2 ^ sh) 4;have h2:=div_add_mod i (2 ^ sh);have hm1:i % 2 ^ sh < 2 ^ sh:=mod_lt _ (two_pow_pos _);have hm2:(i / 2 ^ sh)% 4 < 4:=mod_lt _ (by decide)
  have hpow:2 ^ (sh+2)=4*2 ^ sh:=by rw[pow_add];omega
  have h3:i=2 ^ (sh+2)*(i / 2 ^ sh / 4)+(((i / 2 ^ sh)% 4)*2 ^ sh+i % 2 ^ sh):=by
   calc i=2 ^ sh*(i / 2 ^ sh)+i % 2 ^ sh:=h2.symm
    _=2 ^ sh*(4*(i / 2 ^ sh / 4)+(i / 2 ^ sh)% 4)+i % 2 ^ sh:=by conv_lhs=>rw[← h1]
    _=2 ^ (sh+2)*(i / 2 ^ sh / 4)+(((i / 2 ^ sh)% 4)*2 ^ sh+i % 2 ^ sh):=by rw[hpow,Nat.mul_add];ac_rfl
  have hlt:((i / 2 ^ sh)% 4)*2 ^ sh+i % 2 ^ sh < 2 ^ (sh+2):=by
   rw[hpow];calc ((i / 2 ^ sh)% 4)*2 ^ sh+i % 2 ^ sh < ((i / 2 ^ sh)% 4)*2 ^ sh+2 ^ sh:=Nat.add_lt_add_left hm1 _
    _=((i / 2 ^ sh)% 4+1)*2 ^ sh:=by rw[Nat.add_mul,qZ]
    _≤ 4*2 ^ sh:=mul_le_mul_right _ hm2
  conv_lhs=>rw[h3,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt hlt]
 induction ts using p4.induct generalizing off k with
 | case1 a b c d rest ih=>
  intro i v hg;cases k with
  | zero=>
   dsimp only[p4,List.getD_cons_zero] at hg;have h0:=mod_lt (i / 2 ^ sh) (by decide:0 < 4)
   change (match land (sr i sh) 3 with | 0=>P4.gA sh a i | 1=>P4.gA sh b i | 2=>P4.gA sh c i | _=>P4.gA sh d i)=some v at hg
   rw[hq] at hg;rcases (by omega:(i / 2 ^ sh)% 4=0∨(i / 2 ^ sh)% 4=1∨(i / 2 ^ sh)% 4=2∨(i / 2 ^ sh)% 4=3) with hm|hm|hm|hm <;> rw[hm] at hg
   · simpa[hi2 i,hm,Nat.add_assoc] using hts 0 i v hg
   · simpa[hi2 i,hm,Nat.add_assoc] using hts 1 i v hg
   · simpa[hi2 i,hm,Nat.add_assoc] using hts 2 i v hg
   · simpa[hi2 i,hm,Nat.add_assoc] using hts 3 i v hg
  | succ k=>
   dsimp only[p4,List.getD_cons_succ] at hg
   have:=ih (off+4*2 ^ sh) (fun k' i' v' h'=>by have h'':=hts (k'+4) i' v' (by simpa[List.getD] using h');rwa[show off+4*2 ^ sh+k'*2 ^ sh+i' % 2 ^ sh=off+(k'+4)*2 ^ sh+i' % 2 ^ sh from by rw[Nat.add_mul];ac_rfl]) k i v hg
   rwa[show off+(k+1)*2 ^ (sh+2)+i % 2 ^ (sh+2)=off+4*2 ^ sh+k*2 ^ (sh+2)+i % 2 ^ (sh+2) from by rw[pow_add,show (2:Nat)^ 2=4 from rfl,Nat.add_mul,qZ,qY (2 ^ sh) 4];ac_rfl]
 | case2 a b c=>
  intro i v hg;cases k with
  | zero=>
   dsimp only[p4,List.getD_cons_zero] at hg
   change (match land (sr i sh) 3 with | 0=>P4.gA sh a i | 1=>P4.gA sh b i | 2=>P4.gA sh c i | _=>P4.gA sh .empty i)=some v at hg
   rw[hq] at hg;have h0:=mod_lt (i / 2 ^ sh) (by decide:0 < 4)
   rcases (by omega:(i / 2 ^ sh)% 4=0∨(i / 2 ^ sh)% 4=1∨(i / 2 ^ sh)% 4=2∨(i / 2 ^ sh)% 4=3) with hm|hm|hm|hm <;> rw[hm] at hg
   · simpa[hi2 i,hm,Nat.add_assoc] using hts 0 i v hg
   · simpa[hi2 i,hm,Nat.add_assoc] using hts 1 i v hg
   · simpa[hi2 i,hm,Nat.add_assoc] using hts 2 i v hg
   · simp[P4.gA] at hg
  | succ k=>simp[p4,P4.gA] at hg
 | case3 a b=>
  intro i v hg;cases k with
  | zero=>
   dsimp only[p4,List.getD_cons_zero] at hg
   change (match land (sr i sh) 3 with | 0=>P4.gA sh a i | 1=>P4.gA sh b i | 2=>P4.gA sh .empty i | _=>P4.gA sh .empty i)=some v at hg
   rw[hq] at hg;have h0:=mod_lt (i / 2 ^ sh) (by decide:0 < 4)
   rcases (by omega:(i / 2 ^ sh)% 4=0∨(i / 2 ^ sh)% 4=1∨(i / 2 ^ sh)% 4=2∨(i / 2 ^ sh)% 4=3) with hm|hm|hm|hm <;> rw[hm] at hg
   · simpa[hi2 i,hm,Nat.add_assoc] using hts 0 i v hg
   · simpa[hi2 i,hm,Nat.add_assoc] using hts 1 i v hg
   · simp[P4.gA] at hg
   · simp[P4.gA] at hg
  | succ k=>simp[p4,P4.gA] at hg
 | case4 a=>
  intro i v hg;cases k with
  | zero=>
   dsimp only[p4,List.getD_cons_zero] at hg
   change (match land (sr i sh) 3 with | 0=>P4.gA sh a i | 1=>P4.gA sh .empty i | 2=>P4.gA sh .empty i | _=>P4.gA sh .empty i)=some v at hg
   rw[hq] at hg;have h0:=mod_lt (i / 2 ^ sh) (by decide:0 < 4)
   rcases (by omega:(i / 2 ^ sh)% 4=0∨(i / 2 ^ sh)% 4=1∨(i / 2 ^ sh)% 4=2∨(i / 2 ^ sh)% 4=3) with hm|hm|hm|hm <;> rw[hm] at hg
   · simpa[hi2 i,hm,Nat.add_assoc] using hts 0 i v hg
   · simp[P4.gA] at hg
   · simp[P4.gA] at hg
   · simp[P4.gA] at hg
  | succ k=>simp[p4,P4.gA] at hg
 | case5=>intro i v hg;simp[p4,P4.gA] at hg
lemma mPg {α:Type} (xs:List α):
 ∀ fuel sh ts sh' t,
  (∀ k i v,P4.gA sh (ts.getD k .empty) i=some v->xs[k*2 ^ sh+i % 2 ^ sh]?=some v)->
  mP4 fuel sh ts=(sh',t)->
  ∀ i v,i < ts.length*2 ^ sh->P4.gA sh' t i=some v->xs[i]?=some v:=by
 intro fuel;induction fuel with
 | zero=>
  intro sh ts sh' t hts hm i v hi hg;rcases ts with _|⟨a,r⟩
  · simp[mP4] at hm;rcases hm with ⟨rfl,rfl⟩;simp[P4.gA] at hg
  · rcases r with _|⟨b,r2⟩
    · simp[mP4] at hm;rcases hm with ⟨rfl,rfl⟩;have hi':i < 2 ^ sh:=by simpa using hi
      have:=hts 0 i v (by simpa using hg);simpa[Nat.mod_eq_of_lt hi'] using this
    · simp[mP4] at hm;rcases hm with ⟨rfl,rfl⟩;simp[P4.gA] at hg
 | succ fuel ih=>
  intro sh ts sh' t hts hm i v hi hg;rcases ts with _|⟨a,r⟩
  · simp at hi
  · rcases r with _|⟨b,r2⟩
    · dsimp[mP4] at hm;rcases hm with ⟨rfl,rfl⟩;have hi':i < 2 ^ sh:=by simpa using hi
      have:=hts 0 i v (by simpa using hg);simpa[Nat.mod_eq_of_lt hi'] using this
    · have hi':i < (p4 (a :: b :: r2)).length*2 ^ (sh+2):=by
       have hlen:=p4l (a :: b :: r2);rw[pow_add]
       calc i < (a :: b :: r2).length*2 ^ sh:=hi
        _≤ (4*(p4 (a :: b :: r2)).length)*2 ^ sh:=mul_le_mul_right _ hlen
        _=(p4 (a :: b :: r2)).length*(2 ^ sh*2 ^ 2):=by rw[show (2:Nat)^ 2=4 from rfl];ac_rfl
      exact ih (sh+2) (p4 (a :: b :: r2)) sh' t (by simpa using p4g sh xs (a :: b :: r2) 0 (by simpa using hts)) hm i v hi' hg
lemma mTg {α:Type} (xs:List α) (i:Nat) (v:α) (h:(mPT xs).get? i=some v):xs[i]?=some v:=by
 dsimp[PTab.get?,mPT] at h;cases hble:ble xs.length i with
 | true=>simp[hble] at h
 | false=>
  simp only[hble,qFl,↓reduceIte] at h
  have hi:i < xs.length:=by by_contra hge;exact false_ne_true (hble ▸ ble_eq.mpr (by omega))
  have h0:∀ k j w,P4.gA 0 ((xs.map P4.leaf).getD k .empty) j=some w->xs[k*2 ^ 0+j % 2 ^ 0]?=some w:=by
   intro k j w hk;rw[getD_eq_getElem?_getD] at hk;cases hk_lt:ble xs.length k with
   | true=>have hk':xs.length≤ k:=ble_eq.mp hk_lt;rw[List.getElem?_eq_none (by simp[hk'])] at hk;simp[P4.gA] at hk
   | false=>
    have hk':k < xs.length:=by by_contra hge;exact false_ne_true (hk_lt ▸ ble_eq.mpr (by omega))
    rw[List.getElem?_eq_getElem (by simp[hk']),ql] at hk;simp only[qt,P4.gA,Option.some.injEq] at hk;subst hk;simp[Nat.mod_one,List.getElem?_eq_getElem hk']
  exact mPg xs 6 0 (xs.map P4.leaf) (mP4 6 0 (xs.map P4.leaf)).1 (mP4 6 0 (xs.map P4.leaf)).2 h0 rfl i v (by simpa using hi) h
lemma POkS {b:Z4w} (hvc:Z3U b=true) {pi lo hi:Nat} (hget:(mNP b.r b.pS).get? pi=some (lo,hi)):
 ∃ c∈b.pS,∀ x < 2 ^ b.r,lN lo hi x=Z1J (Z3p b.r c) x:=by
 have hm:=mTg _ pi (lo,hi) hget;rw[List.getElem?_map] at hm
 cases hc:b.pS[pi]? with
 | none=>simp[hc] at hm
 | some c=>
  rw[hc] at hm;simp only[Option.map_some,Option.some.injEq,Prod.mk.injEq] at hm;have hno:nO b.r c lo hi=true:=(qA _ _).mpr ⟨beq_eq.mpr hm.1.symm,beq_eq.mpr hm.2.symm⟩;exact ⟨c,mem_of_getElem? hc,NOkS (Z3v hvc) (XB hvc (mem_of_getElem? hc)).1 hno⟩
lemma gPNS {b:Z4w} (hvc:Z3U b=true):
 ∀ (pis:LN) (pps:List (Nat × Nat)),gPN (mNP b.r b.pS) pis=some pps->∀ pr∈pps,∃ c∈b.pS,∀ x < 2 ^ b.r,lN pr.1 pr.2 x=Z1J (Z3p b.r c) x
 | [],pps,h=>by simp[gPN] at h;subst h;intro pr hp;simp at hp
 | pi :: pis,pps,h=>by
  dsimp[gPN] at h;cases hg:(mNP b.r b.pS).get? pi with
  | none=>simp[hg] at h
  | some pr0=>cases hr:gPN (mNP b.r b.pS) pis with
   | none=>simp[hg,hr] at h
   | some pps'=>
    simp[hg,hr] at h;subst h;intro pr hp;rcases qC.mp hp with rfl|hp'
    · exact POkS hvc hg
    · exact gPNS hvc pis pps' hr pr hp'
lemma mFe (x:Nat):∀ ys:LN,mF x ys=ys.contains x
 | []=>rfl
 | y :: ys=>by
  dsimp[mF];rw[mFe x ys,Bool.eq_iff_iff];simp only[qCm,qC]
  cases h:beq x y with
  | true=>simp[beq_eq.mp h]
  | false=>have hne:x≠y:=fun he=>false_ne_true (h ▸ beq_eq.mpr he);simp[hne]
lemma nFe:∀ xs:LN,nF xs=decide xs.Nodup
 | []=>rfl
 | x :: xs=>by
  dsimp[nF];rw[mFe,nFe xs,Bool.eq_iff_iff];simp only[qCm,q4]
  cases hx:xs.contains x with
  | false=>have hnx:x∉xs:=(by simpa[qCm] using hx);simp[hnx]
  | true=>have hix:x∈xs:=(by simpa[qCm] using hx);simp[hix]
lemma yKF (n rj:Nat) (idxs ws gS:LN):YkF n rj idxs ws gS=Yk n rj idxs ws gS:=by
 dsimp[YkF,Yk]
 have ha:idxs.all (fun i=>ble (i+1) n)=idxs.all (· < n):=List.all_congr rfl fun i=>by rw[Bool.eq_iff_iff];simp[ble_eq]
 have hb:gS.all (fun g=>mF (zJf idxs g) ws)=gS.all (fun g=>ws.contains (Z1J idxs g)):=List.all_congr rfl fun g=>by rw[mFe,zJe]
 have hc:(!(beq rj 0))=(rj != 0):=by cases rj <;> rfl
 have hd:beq idxs.length rj=(idxs.length == rj):=by rw[Bool.eq_iff_iff];simp[beq_eq]
 rw[ha,hb,hc,hd,nFe]
lemma z3F (r k:Nat) (gS Gs:LN) (idx:Nat):Z3tF ((1 <<< k - 1) <<< r) gS Gs idx=Z3t r k gS Gs idx:=by
 dsimp[Z3tF,Z3t];have hm:(1 <<< k - 1) <<< r=(2 ^ k - 1) * 2 ^ r:=by rw[qSl,qSl,qZ]
 by_cases h:idx < gS.length
 · simp[h,ble_eq.mpr h]
 · have hb:ble (idx+1) gS.length=false:=qEf.mpr (mt ble_eq.mp (by omega));simp[h,hb,hm]
lemma z1F (r k:Nat) (gS Gs:LN):∀ wi,Z1OF ((1 <<< k - 1) <<< r) gS Gs wi=Z1O r k gS Gs wi
 | []=>rfl | idx :: rest=>by dsimp[Z1OF,Z1O];rw[z3F,z1F r k gS Gs rest]
lemma vLF (r k mS:Nat) (gS Gs:LN) (t:Nat) (wi:LN):
 VLF r k mS ((1 <<< k - 1) <<< r) gS Gs t wi=VL r k mS gS Gs t wi:=by
 dsimp[VLF,VL]
 have beq_nat (x y:Nat):beq x y=(x == y):=by rw[Bool.eq_iff_iff];simp[beq_eq]
 have ble_nat (x y:Nat):ble x y=decide (x≤ y):=by rw[Bool.eq_iff_iff];simp[ble_eq]
 have bne_nat (x y:Nat):(!(x == y))=(x != y):=rfl
 by_cases ht0:t=0
 · subst ht0;simp only[↓reduceIte,qBs,beq_eq]
   cases wi with | nil=>rfl | cons idx rest=>cases rest with | cons _ _=>rfl | nil=>
    by_cases h1:gS.length≤ idx
    · simp only[h1,ble_eq.mpr h1,↓reduceIte];cases Gs[idx-gS.length]? with | none=>rfl | some a=>
       have hlt:decide (k+Z5o r a+1≤ mS)=decide (k+Z5o r a < mS):=by rw[decide_eq_decide];omega
       simp only[z5o,beq_nat,ble_nat,hlt]
    · have hb:ble gS.length idx=false:=qEf.mpr (mt ble_eq.mp h1);simp only[h1,hb,qFl,↓reduceIte]
 · have hb0:beq t 0=false:=qEf.mpr (mt beq_eq.mp ht0);have he0:(t==0)=false:=beq_false_of_ne ht0
   simp only[hb0,he0,qFl,↓reduceIte];rw[z1F];cases Z1O r k gS Gs wi with | none=>rfl | some ws=>
    by_cases h34:t=34;· subst h34;simp[beq_nat,ble_nat,z5o,bne_nat]
    · by_cases h35:t=35;· subst h35;simp[beq_nat,ble_nat,z5o,bne_nat]
      · have hb34:beq t 34=false:=qEf.mpr (mt beq_eq.mp h34);have hb35:beq t 35=false:=qEf.mpr (mt beq_eq.mp h35);simp[h34,h35,hb34,hb35,yKF]
lemma bt0 {M x:Nat} (h:beq (land (sr M x) 1) 0=false):M.testBit x=true:=by
 change beq (M >>> x &&& 1) 0=false at h
 have:=bTe M x;unfold bT at this;have hbt:(M >>> x &&& 1) < 2:=Nat.and_lt_two_pow (M >>> x) (by omega:1 < 2^1)
 cases hv:(M >>> x &&& 1) with
 | zero=>rw[hv] at h;simp at h
 | succ k=>
  have hk:k=0:=by omega
  subst hk;have h1:beq (M >>> x &&& 1) 1=true:=by rw[hv];rfl
  rw[← this];exact h1
lemma YQ {cf:Cfg} {ms ks:LF} {wf:WF} {F H:SS} {pV:Nat}
 (hs:Z3Z cf ms ks wf F H) (hvc:Z3U cf.ba=true) (hcg:Z4v cf.r cf.gS (Z4u cf.gS)=true)
 (hpv:zO4 cf.r cf.k cf.wo cf.ws pV) (hcg_op:∀ g∈Z4u cf.gS,∀ A∈H,A∪Z3L ms g∈H)
 {st:Z4_} {bx:LN} {ex:Nat} {es:LN} (hi:Z4m cf ms H (Z4u cf.gS) st bx ex es)
 {x:Nat} (hx_lt:x < 2 ^ cf.r) (hxH:Z3L ms x∈H):
 Z4m cf ms H (Z4u cf.gS) (Xy cf.W pV (Z4u cf.gS) st x) (x :: bx) ex es:=by
 have hcks:=VM hcg;have hcl:=ZL hpv (Y2 hs) hcks.2.1 hcks.2.2.2 hcg_op hi.core hi.s_cg hi.s_uc hx_lt hxH;refine ⟨hcl.1,hcl.2.1,hcl.2.2.1,?_,?_,hi.eL,hi.eB,hi.eH⟩
 · intro y hy;rcases qC.mp hy with rfl|hy';exact hx_lt;exact hi.bL y hy'
 · intro p Ms hp hqb hMcg hMuc hbx a ha;dsimp[Xy] at ha;simp only[lp0] at ha;cases hxG:st.G.testBit x with
   | true=>simp only[hxG,qNt,qFl,↓reduceIte] at ha;exact hi.bG p Ms hp hqb hMcg hMuc (fun y hy=>hbx y (qO x hy)) a ha
   | false=>
    have hs0:∀ z∈(z5a cf.W pV st x (sl 1 x)).Gs,z=x∨z∈st.Gs:=fun z hz=>by
     dsimp[z5a] at hz;split_ifs at hz<;>exact qC.mp hz
    have v3:∀ {ys:LN} {st0:Z4_} {u:Nat},(u∈(Z4s cf.W pV x ys st0).Gs->u∈st0.Gs∨∃ y∈ys,u=lor x y):=by
     intro ys st0 u hu;induction ys generalizing st0 with | nil=>exact Or.inl hu | cons w ws' ihf=>
      rw[z4c] at hu;rcases ihf (st0:=Z50 cf.W pV st0 (lor x w)) hu with hst|⟨y,hy,rfl⟩
      · dsimp[Z50,z5a] at hst;split_ifs at hst <;>
         first | exact Or.inl hst | (rcases qC.mp hst with rfl|hst';exact Or.inr ⟨w,qG,rfl⟩;exact Or.inl hst')
      · exact Or.inr ⟨y,qO w hy,rfl⟩
    simp only[hxG,qNf,↓reduceIte] at ha
    rcases v3 ha with ha1|⟨y,hy,rfl⟩
    · rcases v3 ha1 with ha0|⟨g,hg,rfl⟩
      · rcases hs0 a ha0 with hax|has
        · rw[hax];exact hbx x qG
        · exact hi.bG p Ms hp hqb hMcg hMuc (fun y hy=>hbx y (qO x hy)) a has
      · change Z1J p (x ||| g)∈Ms;rw[zJl];exact hMcg _ (hbx x qG) _ (zJz (Qe hvc) hp hqb hcg g hg)
    · change Z1J p (x ||| y)∈Ms;rw[zJl];exact hMuc _ (hbx x qG) _ (hi.bG p Ms hp hqb hMcg hMuc (fun z hz=>hbx z (qO x hz)) y hy)
lemma Z41 {W pV:Nat} (s:Z4_) (x:Nat):(Z51 W pV s x).Gs=s.Gs:=by dsimp[Z51];split_ifs<;>rfl
lemma Z3y {W pV:Nat}:∀ (xs:LN) (s:Z4_),(Z4t W pV s xs).Gs=s.Gs | [],_=>rfl | x :: xs,s=>by dsimp[Z4t];rw[Z3y xs,Z41]
lemma YR {cf:Cfg} {ms:LF} {H:SS} {cg:LN} {pV:Nat} {st:Z4_} {bx:LN} {ex:Nat} {es:LN}
 (hpv:zO4 cf.r cf.k cf.wo cf.ws pV) (hi:Z4m cf ms H cg st bx ex es) {x:Nat} (hx_lt:x < 2 ^ cf.r) (hxH:Z3L ms x∉H):
 Z4m cf ms H cg (Z51 cf.W pV st x) bx (Z4x ex x) (x :: es):=by
 have hr:=Z1R hi.core hx_lt (hpv x hx_lt);have v0:(Z51 cf.W pV st x).Gs=st.Gs:=Z41 st x;refine ⟨hr,v0 ▸ hi.s_cg,v0 ▸ hi.s_uc,hi.bL,v0 ▸ hi.bG,?_,?_,?_⟩
 · intro y hy;rcases qC.mp hy with rfl|hy';exact hx_lt;exact hi.eL y hy'
 · intro a;rw[YN,hi.eB a,qC,eq_comm (a:=a) (b:=x)];tauto
 · intro y hy;rcases qC.mp hy with rfl|hy';exact hxH;exact hi.eH y hy'
lemma Yo {cf:Cfg} {ms:LF} {H:SS} {cg:LN} {pV:Nat} {st:Z4_} {bx:LN} {ex:Nat} {es:LN}
 (hpv:zO4 cf.r cf.k cf.wo cf.ws pV) (hi:Z4m cf ms H cg st bx ex es) {xs:LN} (hxs:∀ y∈xs,y < 2 ^ cf.r∧Z3L ms y∉H):
 Z4m cf ms H cg (Z4t cf.W pV st xs) bx (xs.foldl Z4x ex) (xs++es):=by
 have hr:=VO hpv xs es st (fun y hy=>(hxs y hy).1) hi.core;have v0:(Z4t cf.W pV st xs).Gs=st.Gs:=Z3y xs st;refine ⟨hr,v0 ▸ hi.s_cg,v0 ▸ hi.s_uc,hi.bL,v0 ▸ hi.bG,?_,?_,?_⟩
 · intro y hy;rcases mem_append.mp hy with hy1|hy2;exact (hxs y hy1).1;exact hi.eL y hy2
 · intro a;rw[Qd,hi.eB a,mem_append];tauto
 · intro y hy;rcases mem_append.mp hy with hy1|hy2;exact (hxs y hy1).2;exact hi.eH y hy2
lemma Z5 {cf:Cfg} {ms ks:LF} {wf:WF} {F H:SS} (hs:Z3Z cf ms ks wf F H)
 (hvc:Z3U cf.ba=true) (ht:(cf.mS != 0||cf.tg.isEmpty)=true) {Gs:LN} (hG_lt:∀ a∈Gs,a < 2 ^ cf.r)
 (hG_H:∀ a∈Gs,Z3L ms a∈H) {t:Nat} (ht_mem:t∈cf.tg) {wi:LN} (jA:VL cf.r cf.k cf.mS cf.gS Gs t wi=true):False:=by
 by_cases hms:cf.mS=0
 · rw[ZN ht hms] at ht_mem;simp at ht_mem
 · have v0:=Qe hvc
   have v1:∀ a∈Gs,Z3L ms a∪ks.toFinset∈F:=fun a ha=>qI.mp (hs.hHe ▸ hG_H a ha)|> fun ⟨X,hXf,hXeq⟩=>by
    obtain ⟨hXF,hXK⟩:=qF.mp hXf;have v2:X∩ms.toFinset∪X \ ms.toFinset=X:=by rw[union_comm,qSu]
    rwa[← hXeq,← hXK,v2]
   have hbw:=Y0 hs.hnF (fun g hg=>hs.hr ▸ v0 g hg) (hs.hgf hms) (fun a ha=>hs.hr ▸ hG_lt a ha) v1 (hs.hFl hms) (hs.hr ▸ hs.hk ▸ jA);exact hs.hFp t ht_mem hbw.1 hbw.2
lemma XD {cf:Cfg} {ms ks:LF} {wf:WF} {F H:SS} {cg:LN} {st:Z4_} {bx:LN} {ex:Nat} {es:LN}
 {tP tN:Nat} (hs:Z3Z cf ms ks wf F H) (hi:Z4m cf ms H cg st bx ex es)
 (hok:Z3T cf.W cf.uC tP tN (Z3V cf.r cf.k cf.wo cf.W cf.mS cf.ws) st=true):
 (tP:Int)-(tN:Int)≤ ∑ A∈H,(2*((cf.k*cf.wo+∑ i∈A,wf i:Nat):Int)-(cf.W:Int)):=by
 have v1:ms.Nodup:=(qV.mp hs.hnF).1;have v2:∀ A∈H,Z4Z cf.k cf.wo (ms.map wf) (Z3M ms A)< cf.W->Z3_ cf.r cf.k cf.wo cf.W cf.mS cf.fN (ms.map wf) (Z3M ms A)=true:=fun A hAH hlt=>hs.hws ▸ VV hs hAH hlt;exact YM v1 hs.hr (fun A hA=>pFS F ms.toFinset ks.toFinset A (hs.hHe ▸ hA)) (hs.hws ▸ hi.core) (fun _ _ hpop hr=>VU hpop hr) hi.eH v2 hs.hcp (by simpa[Z3V,hs.hws] using hok)
lemma Qf {cf:Cfg} {ms ks:LF} {wf:WF} {F H:SS} {pV:Nat} (hs:Z3Z cf ms ks wf F H)
 (hvc:Z3U cf.ba=true) (hcg:Z4v cf.r cf.gS (Z4u cf.gS)=true) (hpv:zO4 cf.r cf.k cf.wo cf.ws pV)
 (hbot:cf.mS≠0->(cf.k=0∨cf.fE=true)->∅∈H) (htop:cf.mS≠0->cf.k=12-cf.r->ms.toFinset∈H):
 let init:=Z3W cf (Z4u cf.gS) pV;Z4m cf ms H (Z4u cf.gS) init.1 init.2 0 []:=by
 let b:=cf.ba;let cg:=Z4u b.gS;have v2:=Z3x (Z3v hvc) (Qe hvc) hs.hHo;have hrm:=VT b.r cf.k b.wo b.W cf.mS cf.fN b.ws;let v0:Z4_:=⟨0,[],0,0,(Z4z b.r cf.k b.wo b.W cf.mS cf.fN b.ws).1,(Z4z b.r cf.k b.wo b.W cf.mS cf.fN b.ws).2⟩
 have v3:Z4d b.r cf.k b.wo b.W b.ws ms H [] (Z3_ b.r cf.k b.wo b.W cf.mS cf.fN b.ws) v0:=
  ⟨nodup_nil,fun _ h=>by simp[v0] at h,fun _=>by simp[v0],fun _ h=>by simp[v0] at h,rfl,rfl,fun a ha=>Z3w ((hrm.1 a).mp ha),fun a=>by dsimp only[v0];rw[hrm.1 a];simp,fun _ ha=>Z1U ha,hrm.2⟩
 have v1:Z4m cf ms H cg v0 [] 0 []:=⟨v3,fun _ h=>by simp[v0] at h,fun _ h=>by simp[v0] at h,fun _ h=>by simp at h,fun _ _ _ _ _ _ _ _ ha=>by simp[v0] at ha,fun _ h=>by simp at h,fun _=>by simp,fun _ h=>by simp at h⟩
 dsimp only[Z3W];change Z4m cf ms H cg (if cf.mS==0 then (v0,[]) else if cf.k==0||cf.fE then (Xy b.W pV cg v0 0,[0]) else if cf.k==12-b.r then let top:=sl 1 b.r - 1;(Xy b.W pV cg v0 top,[top]) else (v0,[])).1 _ 0 []
 split_ifs with hm0 hke hkt
 · exact v1
 · exact YQ hs hvc hcg hpv v2 v1 (two_pow_pos _) (by rw[Xr];exact hbot (by simpa using hm0) (by simpa[qOr,qBi] using hke))
 · have hk:cf.k=12-b.r:=by simpa using hkt
   have htop_lt:sl 1 b.r - 1 < 2 ^ b.r:=by change 1 <<< b.r - 1 < _;rw[qSl,qZ];exact Nat.sub_lt (two_pow_pos _) (by omega)
   have htop_eq:sl 1 b.r - 1 = 2 ^ b.r - 1:=by change 1 <<< b.r - 1 = _;rw[qSl,qZ]
   exact YQ hs hvc hcg hpv v2 v1 htop_lt (by have hr':ms.length=b.r:=hs.hr;rw[htop_eq,← hr',Xv];exact htop (by simpa using hm0) hk)
 · exact v1
lemma VPFS (lo hi M:Nat) (elems:LN):VPF lo hi M elems=true↔∀ x∈elems,M.testBit (lN lo hi x)=true:=by
 induction elems with | nil=>simp[VPF] | cons x xs ih=>
  unfold VPF;show (if bT M (lN lo hi x) then VPF lo hi M xs else false)=true↔_;rw[bTe M (lN lo hi x)]
  cases hm:M.testBit (lN lo hi x) <;> simp[hm,ih]
lemma aVPFS (M1:Nat) (e1:LN) (M2:Nat) (e2:LN):∀ (pps:List (Nat × Nat)),
 aV M1 e1 M2 e2 pps=true↔∀ pr∈pps,VPF pr.1 pr.2 M1 e1=true∧VPF pr.1 pr.2 M2 e2=true
 | []=>by simp[aV]
 | (lo,hi):: rest=>by unfold aV;cases h1:VPF lo hi M1 e1 <;> cases h2:VPF lo hi M2 e2 <;> simp[h1,h2,aVPFS M1 e1 M2 e2 rest]
lemma Zc {e:Equiv.Perm (Fin 12)} (wf:WF) (hwf:∀ a:Fin 12,wf (e a)=wf a) (H:SS) (k wo W:Nat):
 (∑ A∈H.image (Finset.image e.symm),(2*((k*wo+∑ i∈A,wf i:Nat):Int)-(W:Int)))=∑ A∈H,(2*((k*wo+∑ i∈A,wf i:Nat):Int)-(W:Int)):=by
 rw[sum_image (fun A _ B _ heq=>image_injective e.symm.injective heq)];apply qh rfl;intro A _
 have v0:∑ i∈A.image e.symm,wf i=∑ i∈A,wf i:=by rw[sum_image (fun a _ b _ heq=>e.symm.injective heq)];apply qh rfl;intro a _;have h:=hwf (e.symm a);rw[e.apply_symm_apply] at h;exact h.symm
 rw[v0]
lemma XE {cf:Cfg} {ms ks:LF} {wf:WF} {F H:SS} {pV:Nat}
 (hs:Z3Z cf ms ks wf F H) (hvc:Z3U cf.ba=true) (hcg:Z4v cf.r cf.gS (Z4u cf.gS)=true)
 (hpv:zO4 cf.r cf.k cf.wo cf.ws pV) {st:Z4_} {bx:LN} {ex:Nat} {es:LN}
 (hi:Z4m cf ms H (Z4u cf.gS) st bx ex es) {rep:Nat} (hrL:rep < 2 ^ cf.r)
 {c lo hiN:Nat} (hc:c∈cf.pS) (hnib:∀ x < 2 ^ cf.r,lN lo hiN x=Z1J (Z3p cf.r c) x)
 (hfG:VPF lo hiN st.G bx=true) (hfE:VPF lo hiN ex es=true) (hpM:Z3L ms (Z1J (Z3p cf.r c) rep)∈H):
 let v0:ms.Nodup:=(qV.mp hs.hnF).1;let p:=Z3p cf.r c;let hvp:=(XB hvc hc).1;let e:=Z3P ms v0 p (hs.hr ▸ hvp);let F':=F.image (Finset.image e.symm);let H':=H.image (Finset.image e.symm)
 Z3Z cf ms ks wf F' H'∧Z4m cf ms H' (Z4u cf.gS) (Xy cf.W pV (Z4u cf.gS) st rep) (rep :: bx) ex es∧∀ a:Fin 12,wf (e a)=wf a:=by
 intro v0 p hvp e F' H';have ⟨_,hwp,hgp⟩:=XB hvc hc;have hs':=XC hs hvp hgp
 have hbxG:∀ y∈bx,Z1J p y∈st.Gs:=fun y hy=>by have hb:=((VPFS lo hiN st.G bx).mp hfG) y hy;rw[hnib y (hi.bL y hy)] at hb;exact (hi.core.bit _).mp hb
 have hGf:∀ a∈st.Gs,Z1J p a∈st.Gs:=hi.bG p st.Gs hvp hgp hi.s_cg hi.s_uc hbxG
 have hEf:∀ y∈es,Z1J p y∈es:=fun y hy=>by have hb:=((VPFS lo hiN ex es).mp hfE) y hy;rw[hnib y (hi.eL y hy)] at hb;exact (hi.eB _).mp hb
 have v8:Z3L ms rep∈H':=by
  have v2:(Z3L ms rep).image e=Z3L ms (Z1J p rep):=ZK ms v0 p (hs.hr ▸ hvp) rep;have v1:((Z3L ms rep).image e).image e.symm=Z3L ms rep:=by ext z;simp
  rw[← v1,v2];exact qI.mpr ⟨_,hpM,rfl⟩
 have v12:∀ a∈st.Gs,Z3L ms a∈H':=fun a ha=>by
  have v10:Z3L ms (Z1J p a)∈H:=hi.core.memH _ (hGf a ha);have v2:(Z3L ms a).image e=Z3L ms (Z1J p a):=ZK ms v0 p (hs.hr ▸ hvp) a;have v1:((Z3L ms a).image e).image e.symm=Z3L ms a:=by ext z;simp
  rw[← v1,v2];exact qI.mpr ⟨_,v10,rfl⟩
 have v9:∀ y∈es,Z3L ms y∉H':=fun y hy hyH'=>by
  have hnH:Z3L ms (Z1J p y)∉H:=hi.eH _ (hEf y hy);obtain ⟨B,hBH,hBeq⟩:=qI.mp hyH';have v1:(B.image e.symm).image e=B:=by ext z;simp
  have v2:(Z3L ms y).image e=Z3L ms (Z1J p y):=ZK ms v0 p (hs.hr ▸ hvp) y;rw[← v2,← hBeq,v1] at hnH;exact hnH hBH
 have v7:Z4d cf.r cf.k cf.wo cf.W cf.ws ms H' es (Z3_ cf.r cf.k cf.wo cf.W cf.mS cf.fN cf.ws) st:=
  ⟨hi.core.nd,hi.core.lt,hi.core.bit,v12,hi.core.curP_eq,hi.core.curCnt_eq,hi.core.rem_lt,hi.core.rem_spec,hi.core.rem_neg,hi.core.remSum_eq⟩
 exact ⟨hs',YQ hs' hvc hcg hpv (Z3x (Z3v hvc) (Qe hvc) hs'.hHo) ⟨v7,hi.s_cg,hi.s_uc,hi.bL,hi.bG,hi.eL,hi.eB,v9⟩ hrL v8,Yi ms v0 wf p (hs.hr ▸ hvp) (hs.hws ▸ hwp)⟩
lemma Yf {cf:Cfg} {ms:LF} {H:SS} (hvc:Z3U cf.ba=true)
 {rep:Nat} (hrL:rep < 2 ^ cf.r) (hnR:Z3L ms rep∉H) {pis:LN} {pps:List (Nat × Nat)} (hmap:gPN (mNP cf.r cf.pS) pis=some pps)
 (hnone:¬ ∃ pr∈pps,Z3L ms (lN pr.1 pr.2 rep)∈H):
 ∀ y∈(rep :: pps.map (fun pr=>lN pr.1 pr.2 rep)),y < 2 ^ cf.r∧Z3L ms y∉H:=by
 intro y hy;rcases qC.mp hy with rfl|hy'
 · exact ⟨hrL,hnR⟩
 · obtain ⟨pr,hpr,rfl⟩:=List.mem_map.mp hy';obtain ⟨c,hc,hnib⟩:=gPNS hvc pis pps hmap pr hpr;have hvp:=(XB hvc hc).1;simp only[Z3O,qA,qD,qE] at hvp;rw[hnib rep hrL];exact ⟨XA hvp.2,fun hm=>hnone ⟨pr,hpr,by rw[hnib rep hrL];exact hm⟩⟩
theorem Y3 (cf:Cfg) (hvc:Z3U cf.ba=true)
 (ht:(cf.mS != 0||cf.tg.isEmpty)=true) (hcg:Z4v cf.r cf.gS (Z4u cf.gS)=true)
 (pV:Nat) (hpv:zO4 cf.r cf.k cf.wo cf.ws pV) (tP tN:Nat):
 ∀ (fuel:Nat) (bs:bS) (ms ks:LF) (wf:WF) (F H:SS) (st:Z4_) (bx:LN) (ex:Nat) (es:LN) (bsO:bS),
  Z3Z cf ms ks wf F H->Z4m cf ms H (Z4u cf.gS) st bx ex es->
  VR cf (Z4u cf.gS) (Z3V cf.r cf.k cf.wo cf.W cf.mS cf.ws) (mNP cf.r cf.pS) pV ((1 <<< cf.k - 1) <<< cf.r) fuel bs st bx ex es tP tN=some bsO->
  (tP:Int)-(tN:Int)≤ ∑ A∈H,(2*((cf.k*cf.wo+∑ i∈A,wf i:Nat):Int)-(cf.W:Int)):=by
 intro fuel;induction fuel with
 | zero=>intro _ _ _ _ _ _ _ _ _ _ _ _ _ jB;simp[VR] at jB
 | succ fuel ih=>
  intro bs ms ks wf F H st bx ex es bsO hs hi jB;have v3:=Z3x (Z3v hvc) (Qe hvc) hs.hHo;dsimp only[VR] at jB;cases hb0:bs.rB1.1 with
  | zero=>
   simp only[hb0] at jB;cases hle:Z3T cf.W cf.uC tP tN (Z3V cf.r cf.k cf.wo cf.W cf.mS cf.ws) st with
   | false=>simp only[hle,qFl,↓reduceIte] at jB;simp at jB
   | true=>exact XD hs hi hle
  | succ _=>
   simp only[hb0] at jB;cases hb1:bs.rB1.2.rB1.1 with
   | zero=>
    simp only[hb1] at jB;set r2:=bs.rB1.2.rB1.2.rB cf.r;set x:=r2.1
    cases hnx:beq (land (sr st.rM x) 1) 0 with
    | true=>simp only[hnx,↓reduceIte] at jB;simp at jB
    | false=>
     simp only[hnx,qFl,↓reduceIte] at jB;have v1:x < 2 ^ cf.r:=hi.core.rem_lt x (bt0 hnx)
     cases hbr1:VR cf (Z4u cf.gS) (Z3V cf.r cf.k cf.wo cf.W cf.mS cf.ws) (mNP cf.r cf.pS) pV ((1 <<< cf.k - 1) <<< cf.r) fuel r2.2 (Xy cf.W pV (Z4u cf.gS) st x) (x :: bx) ex es tP tN with
     | none=>simp only[hbr1] at jB;simp at jB
     | some bs4=>
      simp only[hbr1] at jB;by_cases v4:Z3L ms x∈H
      · exact ih r2.2 ms ks wf F H _ (x :: bx) ex es bs4 hs (YQ hs hvc hcg hpv v3 hi v1 v4) hbr1
      · exact ih bs4 ms ks wf F H _ bx (Z4x ex x) (x :: es) bsO hs (YR hpv hi v1 v4) jB
   | succ _=>
    simp only[hb1] at jB;set r2:=bs.rB1.2.rB1.2.rB1;cases hb2:r2.1 with
    | zero=>
     simp only[hb2] at jB;set r3:=r2.2.rB cf.r;set v0:=r3.1
     cases hnr:beq (land (sr st.rM v0) 1) 0 with
     | true=>simp only[hnr,↓reduceIte] at jB;simp at jB
     | false=>
      simp only[hnr,qFl,↓reduceIte] at jB
      set bm:=r3.2.rB1;set r4:=if beq bm.1 0 then (1,bm.2) else bm.2.rB 6;cases hm0:beq r4.1 0 with
      | true=>simp only[hm0,↓reduceIte] at jB;simp at jB
      | false=>
       simp only[hm0,qFl,↓reduceIte] at jB;set r5:=VQ cf.pB r4.1 r4.2;cases hmap:gPN (mNP cf.r cf.pS) r5.1 with
       | none=>simp only[hmap] at jB;simp at jB
       | some pps=>
        simp only[hmap] at jB;cases hfix:aV st.G bx ex es pps with
        | false=>simp only[hfix,qNf,↓reduceIte] at jB;simp at jB
        | true=>
         simp only[hfix,qNt,qFl,↓reduceIte] at jB;have v2:v0 < 2 ^ cf.r:=hi.core.rem_lt v0 (bt0 hnr);have v5:=(aVPFS st.G bx ex es pps).mp hfix
         cases hbr1:VR cf (Z4u cf.gS) (Z3V cf.r cf.k cf.wo cf.W cf.mS cf.ws) (mNP cf.r cf.pS) pV ((1 <<< cf.k - 1) <<< cf.r) fuel r5.2 (Xy cf.W pV (Z4u cf.gS) st v0) (v0 :: bx) ex es tP tN with
         | none=>simp only[hbr1] at jB;simp at jB
         | some bs7=>
          simp only[hbr1] at jB;by_cases hrepH:Z3L ms v0∈H
          · exact ih r5.2 ms ks wf F H _ (v0 :: bx) ex es bs7 hs (YQ hs hvc hcg hpv v3 hi v2 hrepH) hbr1
          · by_cases hex:∃ pr∈pps,Z3L ms (lN pr.1 pr.2 v0)∈H
            · obtain ⟨pr,hpr,hpM⟩:=hex;obtain ⟨c,hc,hnib⟩:=gPNS hvc r5.1 pps hmap pr hpr;obtain ⟨hfg,hfex⟩:=v5 pr hpr;have hstep:=XE hs hvc hcg hpv hi v2 hc hnib hfg hfex (by rwa[← hnib v0 v2]);have v6:=ih r5.2 ms ks wf _ _ _ (v0 :: bx) ex es bs7 hstep.1 hstep.2.1 hbr1;rwa[Zc wf hstep.2.2 H cf.k cf.wo cf.W] at v6
            · exact ih bs7 ms ks wf F H _ bx _ _ bsO hs (Yo hpv hi (Yf hvc v2 hrepH hmap hex)) jB
    | succ _=>
     simp only[hb2] at jB;set r3:=r2.2.rB1;cases hb3:r3.1 with
     | zero=>
      simp only[hb3] at jB;set r4:=r3.2.rB cf.r;set x:=r4.1;set r5:=r4.2.rB cf.tB;cases htag:cf.tg[r5.1]? with
      | none=>simp only[htag] at jB;simp at jB
      | some t=>
       simp only[htag] at jB;cases hnx:beq (land (sr st.rM x) 1) 0 with
       | true=>simp only[hnx,↓reduceIte] at jB;simp at jB
       | false=>
        simp only[hnx,qFl,↓reduceIte] at jB
        cases jA:VLF cf.r cf.k cf.mS ((1 <<< cf.k - 1) <<< cf.r) cf.gS (Xy cf.W pV (Z4u cf.gS) st x).Gs t (VQ (Z3n (cf.gS.length+(Xy cf.W pV (Z4u cf.gS) st x).Gs.length)) (Z4y t) r5.2).1 with
        | false=>simp only[jA,qFl,↓reduceIte] at jB;simp at jB
        | true=>
         simp only[jA,↓reduceIte] at jB;have v1:x < 2 ^ cf.r:=hi.core.rem_lt x (bt0 hnx)
         have jA':VL cf.r cf.k cf.mS cf.gS (Xy cf.W pV (Z4u cf.gS) st x).Gs t (VQ (Z3n (cf.gS.length+(Xy cf.W pV (Z4u cf.gS) st x).Gs.length)) (Z4y t) r5.2).1=true:=by rw[← vLF];exact jA
         have v4:Z3L ms x∉H:=fun hx_in=>Z5 hs hvc ht (YQ hs hvc hcg hpv v3 hi v1 hx_in).core.lt (YQ hs hvc hcg hpv v3 hi v1 hx_in).core.memH (mem_of_getElem? htag) jA';exact ih _ ms ks wf F H _ bx (Z4x ex x) (x :: es) bsO hs (YR hpv hi v1 v4) jB
     | succ _=>
      simp only[hb3] at jB;set r5:=r3.2.rB cf.tB;cases htag:cf.tg[r5.1]? with
      | none=>simp only[htag] at jB;simp at jB
      | some t=>
       simp only[htag] at jB;cases jA:VLF cf.r cf.k cf.mS ((1 <<< cf.k - 1) <<< cf.r) cf.gS st.Gs t (VQ (Z3n (cf.gS.length+st.Gs.length)) (Z4y t) r5.2).1 with
       | false=>simp only[jA,qFl,↓reduceIte] at jB;simp at jB
       | true=>exact False.elim (Z5 hs hvc ht hi.core.lt hi.core.memH (mem_of_getElem? htag) (by rw[← vLF];exact jA))
theorem YS (cf:Cfg) (cg:LN) (pt:PT) (hbase:bOk cf.ba cg=true) (hpt:pt=mNP cf.r cf.pS) (words:LN) (tP tN:Nat)
 (hcheck:Z3X cf cg pt words tP tN=true) (ms ks:LF) (wf:WF) (F H:SS) (hs:Z3Z cf ms ks wf F H)
 (hbot:cf.mS≠0->(cf.k=0∨cf.fE=true)->∅∈H) (htop:cf.mS≠0->cf.k=12-cf.r->ms.toFinset∈H):
 (tP:Int)-(tN:Int)≤ ∑ A∈H,(2*((cf.k*cf.wo+∑ i∈A,wf i:Nat):Int)-(cf.W:Int)):=by
 dsimp[bOk] at hbase;simp only[qA,qBi] at hbase;have hvc:=hbase.1.1;have hcg_eq:cg=Z4u cf.gS:=hbase.1.2;have hcg:Z4v cf.r cf.gS (Z4u cf.gS)=true:=hcg_eq ▸ hbase.2;dsimp[Z3X,cO] at hcheck;simp only[qA,qD] at hcheck;have hpv:=mPo cf.r cf.k cf.wo cf.ws hcheck.1.2;obtain ⟨bsO,hsome⟩:=qc.mp (hcg_eq ▸ hcheck.2);exact Y3 cf hvc hcheck.1.1 hcg (mkPv cf.k cf.wo cf.ws (sl 1 cf.r)) hpv tP tN 64 (bS.init words) ms ks wf F H _ _ 0 [] bsO hs (Qf hs hvc hcg hpv hbot htop) (hpt ▸ hsome)
structure ZC where
 cf:Cfg
 pt:PT
 pv:Nat
 tp:Nat
 tn:Nat
abbrev ZC.cg (c:ZC):LN:=Z4u c.cf.gS
abbrev ZC.msk (c:ZC):Nat:=(1 <<< c.cf.k - 1) <<< c.cf.r
abbrev ZC.xy (c:ZC) (st:Z4_) (x:Nat):=Xy c.cf.W c.pv c.cg st x
abbrev ZC.e (c:ZC) (st:Z4_) (x:Nat):=Z51 c.cf.W c.pv st x
abbrev ZC.et (c:ZC) (st:Z4_) (xs:LN):=Z4t c.cf.W c.pv st xs
lemma z1ne:∀ sk:Skel,∃ j,j∈Z1T sk
 | .leaf i=>⟨i,by simp[Z1T]⟩
 | .branch _ s1 _=>by obtain ⟨i,hi⟩:=z1ne s1;exact ⟨i,by simp[Z1T,hi]⟩
 | .orbit _ _ s1 _=>by obtain ⟨i,hi⟩:=z1ne s1;exact ⟨i,by simp[Z1T,hi]⟩
 | .elim _ _ _ s0=>z1ne s0
def zP (c:ZC) (lo hi:Nat):Skel->Z4_->LN->Nat->LN->Prop
 | .leaf j,st,bx,ex,es=>lo≤ j->j < hi->
  ∃ ws,(VR c.cf c.cg (Z3V c.cf.r c.cf.k c.cf.wo c.cf.W c.cf.mS c.cf.ws) c.pt c.pv c.msk 64 (bS.init ws) st bx ex es c.tp c.tn).isSome=tt
 | .branch x s1 s0,st,bx,ex,es=>
  hIn lo hi (.branch x s1 s0)=tt->beq (land (sr st.rM x) 1) 0=ff∧
  zP c lo hi s1 (c.xy st x) (x :: bx) ex es∧zP c lo hi s0 (c.e st x) bx (Z4x ex x) (x :: es)
 | .orbit rep pis s1 s0,st,bx,ex,es=>
  hIn lo hi (.orbit rep pis s1 s0)=tt->(beq (land (sr st.rM rep) 1) 0||pis.isEmpty)=ff∧
  ∃ pps,gPN c.pt pis=some pps∧aV st.G bx ex es pps=tt∧
  zP c lo hi s1 (c.xy st rep) (rep :: bx) ex es∧
  let xs:=rep :: pps.map (fun pr=>lN pr.1 pr.2 rep)
  zP c lo hi s0 (c.et st xs) bx (xs.foldl Z4x ex) (xs++es)
 | .elim x t wi s0,st,bx,ex,es=>
  hIn lo hi (.elim x t wi s0)=tt->(beq (land (sr st.rM x) 1) 0||!(c.cf.tg.contains t))=ff∧
  VLF c.cf.r c.cf.k c.cf.mS c.msk c.cf.gS (c.xy st x).Gs t wi=tt∧
  zP c lo hi s0 (c.e st x) bx (Z4x ex x) (x :: es)
lemma hIS (lo mid hi:Nat):∀ sk,lo≤ mid->mid≤ hi->hIn lo hi sk=tt->hIn lo mid sk=tt∨hIn mid hi sk=tt
 | .leaf _,_,_,hj=>by simp only[hIn,qA,ble_eq] at *;omega
 | .branch _ s1 s0,h1,h2,hj=>by simp only[hIn,qOr] at *;rcases hj with a|b;rcases hIS lo mid hi s1 h1 h2 a with c|d;exact .inl (.inl c);exact .inr (.inl d);rcases hIS lo mid hi s0 h1 h2 b with c|d;exact .inl (.inr c);exact .inr (.inr d)
 | .orbit _ _ s1 s0,h1,h2,hj=>by simp only[hIn,qOr] at *;rcases hj with a|b;rcases hIS lo mid hi s1 h1 h2 a with c|d;exact .inl (.inl c);exact .inr (.inl d);rcases hIS lo mid hi s0 h1 h2 b with c|d;exact .inl (.inr c);exact .inr (.inr d)
 | .elim _ _ _ s0,h1,h2,hj=>hIS lo mid hi s0 h1 h2 hj
lemma hIM (lo hi:Nat):∀ sk j,j∈Z1T sk->lo≤ j->j < hi->hIn lo hi sk=tt
 | .leaf i,j,hj,h1,_=>by simp only[Z1T,List.mem_singleton] at hj;subst hj;simp[hIn,ble_eq,h1];omega
 | .branch _ s1 s0,j,hj,h1,h2=>by simp only[Z1T,mem_append] at hj;simp only[hIn,qOr];rcases hj with h|h;exact .inl (hIM lo hi s1 j h h1 h2);exact .inr (hIM lo hi s0 j h h1 h2)
 | .orbit _ _ s1 s0,j,hj,h1,h2=>by simp only[Z1T,mem_append] at hj;simp only[hIn,qOr];rcases hj with h|h;exact .inl (hIM lo hi s1 j h h1 h2);exact .inr (hIM lo hi s0 j h h1 h2)
 | .elim _ _ _ s0,j,hj,h1,h2=>hIM lo hi s0 j hj h1 h2
lemma zPV (c:ZC) (lo hi:Nat):∀ sk st bx ex es,hIn lo hi sk=ff->zP c lo hi sk st bx ex es
 | .leaf j,_,_,_,_,hf=>fun hj1 _=>by have ht:hIn lo hi (.leaf j)=tt:=(by simp[hIn,ble_eq,hj1];omega);rw[hf] at ht;cases ht
 | .branch _ _ _,_,_,_,_,hf=>fun ht=>by rw[hf] at ht;cases ht
 | .orbit _ _ _ _,_,_,_,_,hf=>fun ht=>by rw[hf] at ht;cases ht
 | .elim _ _ _ _,_,_,_,_,hf=>fun ht=>by rw[hf] at ht;cases ht
lemma mAe (lo hi:Nat):∀ sk,(mAS lo hi sk=.empty)↔(hIn lo hi sk=ff)
 | .leaf j=>by dsimp[mAS,hIn];split_ifs with h <;> simp[h]
 | .branch _ s1 s0=>by
  dsimp[mAS,hIn];have ih1:=mAe lo hi s1;have ih0:=mAe lo hi s0
  cases h1:mAS lo hi s1 <;> cases h0:mAS lo hi s0 <;> simp_all
 | .orbit _ _ s1 s0=>by
  dsimp[mAS,hIn];have ih1:=mAe lo hi s1;have ih0:=mAe lo hi s0
  cases h1:mAS lo hi s1 <;> cases h0:mAS lo hi s0 <;> simp_all
 | .elim _ _ _ s0=>by
  dsimp[mAS,hIn];have ih0:=mAe lo hi s0
  cases h0:mAS lo hi s0 <;> simp_all
lemma zGP (c:ZC) (lo hi:Nat) (wss:List (LN)):
 ∀ sk st bx ex es,ZTG c.cf c.cg (Z3V c.cf.r c.cf.k c.cf.wo c.cf.W c.cf.mS c.cf.ws) c.pt c.pv c.msk c.tp c.tn lo wss (mAS lo hi sk) st bx ex es=tt->
  zP c lo hi sk st bx ex es
 | .leaf j,st,bx,ex,es,h=>fun hj1 hj2=>by
  dsimp[mAS] at h;rw[if_pos (by simp[ble_eq,hj1];omega)] at h;dsimp[ZTG] at h
  cases hw:wss[j-lo]? with | none=>rw[hw] at h;simp at h | some ws=>rw[hw] at h;exact ⟨ws,h⟩
 | .branch x s1 s0,st,bx,ex,es,h=>fun hin=>by
  have h1:=zGP c lo hi wss s1 (c.xy st x) (x :: bx) ex es;have h0:=zGP c lo hi wss s0 (c.e st x) bx (Z4x ex x) (x :: es);dsimp only[mAS] at h
  cases hm1:mAS lo hi s1 <;> cases hm0:mAS lo hi s0 <;> rw[hm1,hm0] at h <;> dsimp only at h
  · have hf1:hIn lo hi s1=ff:=(mAe lo hi s1).mp hm1;have hf0:hIn lo hi s0=ff:=(mAe lo hi s0).mp hm0;simp[hIn,hf1,hf0] at hin
  all_goals
    dsimp only[ZTG] at h;cases hnx:beq (land (sr st.rM x) 1) 0 with
    | true=>simp only[hnx,↓reduceIte] at h;cases h
    | false=>
     simp only[hnx,qFl,↓reduceIte,qA] at h
     refine ⟨rfl,h1 (by rw[hm1];first | exact h.1 | rfl),h0 (by rw[hm0];first | exact h.2 | rfl)⟩
 | .orbit rep pis s1 s0,st,bx,ex,es,h=>fun hin=>by
  have h1:=zGP c lo hi wss s1 (c.xy st rep) (rep :: bx) ex es;dsimp only[mAS] at h
  cases hm1:mAS lo hi s1 <;> cases hm0:mAS lo hi s0 <;> rw[hm1,hm0] at h <;> dsimp only at h
  · have hf1:hIn lo hi s1=ff:=(mAe lo hi s1).mp hm1;have hf0:hIn lo hi s0=ff:=(mAe lo hi s0).mp hm0;simp[hIn,hf1,hf0] at hin
  all_goals
    dsimp only[ZTG] at h;cases jA:(beq (land (sr st.rM rep) 1) 0||pis.isEmpty) with
    | true=>simp only[jA,↓reduceIte] at h;cases h
    | false=>
     simp only[jA,qFl,↓reduceIte] at h;cases hmap:gPN c.pt pis with
     | none=>simp[hmap] at h
     | some pps=>
      simp only[hmap] at h;cases hfix:aV st.G bx ex es pps with
      | false=>simp only[hfix,qNf,↓reduceIte] at h;cases h
      | true=>
       simp only[hfix,qNt,qFl,↓reduceIte,qA] at h
       refine ⟨rfl,pps,rfl,hfix,h1 (by rw[hm1];first | exact h.1 | rfl),?_⟩
       exact zGP c lo hi wss s0 _ _ _ _ (by rw[hm0];first | exact h.2 | rfl)
 | .elim x t wi s0,st,bx,ex,es,h=>fun hin=>by
  dsimp only[mAS] at h;cases hm0:mAS lo hi s0 <;> rw[hm0] at h <;> dsimp only at h
  · have hf0:hIn lo hi s0=ff:=(mAe lo hi s0).mp hm0;simp[hIn,hf0] at hin
  all_goals
    dsimp only[ZTG] at h;cases jA:(beq (land (sr st.rM x) 1) 0||!(c.cf.tg.contains t)) with
    | true=>simp only[jA,↓reduceIte] at h;cases h
    | false=>
     simp only[jA,qFl,↓reduceIte] at h
     cases hvl:VLF c.cf.r c.cf.k c.cf.mS c.msk c.cf.gS (c.xy st x).Gs t wi with
     | false=>simp only[hvl,qFl,↓reduceIte] at h
     | true=>simp only[hvl,↓reduceIte] at h;exact ⟨rfl,rfl,zGP c lo hi wss s0 _ _ _ _ (by rw[hm0];exact h)⟩
lemma zb1 {c lo hi x s1 s0 st bx ex es} (h:zP c lo hi (.branch x s1 s0) st bx ex es):
 zP c lo hi s1 (c.xy st x) (x :: bx) ex es:=by
 by_cases hs:hIn lo hi s1=tt
 · exact (h (by simp[hIn,hs])).2.1
 · exact zPV c lo hi s1 _ _ _ _ (qEf.mpr hs)
lemma zb0 {c lo hi x s1 s0 st bx ex es} (h:zP c lo hi (.branch x s1 s0) st bx ex es):
 zP c lo hi s0 (c.e st x) bx (Z4x ex x) (x :: es):=by
 by_cases hs:hIn lo hi s0=tt
 · exact (h (by simp[hIn,hs])).2.2
 · exact zPV c lo hi s0 _ _ _ _ (qEf.mpr hs)
lemma zo1 {c lo hi rep pis s1 s0 st bx ex es} (h:zP c lo hi (.orbit rep pis s1 s0) st bx ex es):
 zP c lo hi s1 (c.xy st rep) (rep :: bx) ex es:=by
 by_cases hs:hIn lo hi s1=tt
 · obtain ⟨_,_,_,_,hs1,_⟩:=h (by simp[hIn,hs]);exact hs1
 · exact zPV c lo hi s1 _ _ _ _ (qEf.mpr hs)
lemma zo0 {c lo hi rep pis s1 s0 st bx ex es pps} (hm:gPN c.pt pis=some pps) (h:zP c lo hi (.orbit rep pis s1 s0) st bx ex es):
 let xs:=rep :: pps.map (fun pr=>lN pr.1 pr.2 rep)
 zP c lo hi s0 (c.et st xs) bx (xs.foldl Z4x ex) (xs++es):=by
 by_cases hs:hIn lo hi s0=tt
 · obtain ⟨_,pps1,hm1,_,_,hs0⟩:=h (by simp[hIn,hs]);rw[hm] at hm1;cases hm1;exact hs0
 · exact zPV c lo hi s0 _ _ _ _ (qEf.mpr hs)
lemma ze0 {c lo hi x t wi s0 st bx ex es} (h:zP c lo hi (.elim x t wi s0) st bx ex es):
 zP c lo hi s0 (c.e st x) bx (Z4x ex x) (x :: es):=by
 by_cases hs:hIn lo hi s0=tt
 · exact (h hs).2.2
 · exact zPV c lo hi s0 _ _ _ _ (qEf.mpr hs)
lemma zPM (c:ZC) (lo mid hi:Nat) (hlm:lo≤ mid) (hmh:mid≤ hi):
 ∀ sk {st bx ex es},zP c lo mid sk st bx ex es->zP c mid hi sk st bx ex es->zP c lo hi sk st bx ex es
 | .leaf j,_,_,_,_,h1,h2=>fun hj1 hj2=>by
  by_cases hm:j < mid
  · exact h1 hj1 hm
  · exact h2 (by omega) hj2
 | .branch x s1 s0,st,_,_,_,h1,h2=>fun hin=>by
  have hnx:beq (land (sr st.rM x) 1) 0=ff:=by rcases hIS lo mid hi (.branch x s1 s0) hlm hmh hin with a|b;exact (h1 a).1;exact (h2 b).1
  exact ⟨hnx,zPM c lo mid hi hlm hmh s1 (zb1 h1) (zb1 h2),zPM c lo mid hi hlm hmh s0 (zb0 h1) (zb0 h2)⟩
 | .orbit rep pis s1 s0,st,bx,ex,es,h1,h2=>fun hin=>by
  have ⟨hb,pps,hm,hf⟩:(beq (land (sr st.rM rep) 1) 0||pis.isEmpty)=ff∧∃ pps,gPN c.pt pis=some pps∧aV st.G bx ex es pps=tt:=by
   rcases hIS lo mid hi (.orbit rep pis s1 s0) hlm hmh hin with a|b
   · obtain ⟨hb,pps,hm,hf,_,_⟩:=h1 a;exact ⟨hb,pps,hm,hf⟩
   · obtain ⟨hb,pps,hm,hf,_,_⟩:=h2 b;exact ⟨hb,pps,hm,hf⟩
  exact ⟨hb,pps,hm,hf,zPM c lo mid hi hlm hmh s1 (zo1 h1) (zo1 h2),zPM c lo mid hi hlm hmh s0 (zo0 hm h1) (zo0 hm h2)⟩
 | .elim x t wi s0,st,bx,ex,es,h1,h2=>fun hin=>by
  have ⟨hb,hv⟩:(beq (land (sr st.rM x) 1) 0||!(c.cf.tg.contains t))=ff∧VLF c.cf.r c.cf.k c.cf.mS c.msk c.cf.gS (c.xy st x).Gs t wi=tt:=by
   rcases hIS lo mid hi (.elim x t wi s0) hlm hmh hin with a|b
   · obtain ⟨hb,hv,_⟩:=h1 a;exact ⟨hb,hv⟩
   · obtain ⟨hb,hv,_⟩:=h2 b;exact ⟨hb,hv⟩
  exact ⟨hb,hv,zPM c lo mid hi hlm hmh s0 (ze0 h1) (ze0 h2)⟩
theorem zOk (c:ZC) (hvc:Z3U c.cf.ba=true) (hpt:c.pt=mNP c.cf.r c.cf.pS)
 (ht:(c.cf.mS != 0||c.cf.tg.isEmpty)=true) (hcg:Z4v c.cf.r c.cf.gS c.cg=true)
 (hpv:zO4 c.cf.r c.cf.k c.cf.wo c.cf.ws c.pv) (m:Nat):
 ∀ (sk:Skel) (ms ks:LF) (wf:WF) (F H:SS) (st:Z4_) (bx:LN) (ex:Nat) (es:LN),
  (Z1T sk).all (fun j=>ble (j+1) m)=tt->Z3Z c.cf ms ks wf F H->Z4m c.cf ms H c.cg st bx ex es->
  zP c 0 m sk st bx ex es->
  (c.tp:Int)-(c.tn:Int)≤ ∑ A∈H,(2*((c.cf.k*c.cf.wo+∑ i∈A,wf i:Nat):Int)-(c.cf.W:Int)):=by
 intro sk;induction sk with
 | leaf j=>
  intro ms ks wf F H st bx ex es hbd hs hi jB;dsimp only[Z1T] at hbd;have ⟨ws,hws⟩:=jB (zero_le _) (ble_eq.mp (by simpa using hbd));obtain ⟨bsO,hsome⟩:=qc.mp hws;exact Y3 c.cf hvc ht hcg c.pv hpv c.tp c.tn 64 (bS.init ws) ms ks wf F H st bx ex es bsO hs hi (hpt ▸ hsome)
 | branch x s1 s0 ih1 ih0=>
  intro ms ks wf F H st bx ex es hbd hs hi jB
  have hin:hIn 0 m (.branch x s1 s0)=tt:=by obtain ⟨j,hj⟩:=z1ne (.branch x s1 s0);exact hIM 0 m _ j hj (zero_le _) (ble_eq.mp (qE.mp hbd j hj))
  dsimp only[Z1T] at hbd;simp only[all_append,qA] at hbd;obtain ⟨hnx,hp1,hp0⟩:=jB hin;have v2:x < 2 ^ c.cf.r:=hi.core.rem_lt x (bt0 hnx);have v1:=Z3x (Z3v hvc) (Qe hvc) hs.hHo
  by_cases v7:Z3L ms x∈H
  · exact ih1 ms ks wf F H _ (x :: bx) ex es hbd.1 hs (YQ hs hvc hcg hpv v1 hi v2 v7) hp1
  · exact ih0 ms ks wf F H _ bx (Z4x ex x) (x :: es) hbd.2 hs (YR hpv hi v2 v7) hp0
 | orbit rep pis s1 s0 ih1 ih0=>
  intro ms ks wf F H st bx ex es hbd hs hi jB
  have hin:hIn 0 m (.orbit rep pis s1 s0)=tt:=by obtain ⟨j,hj⟩:=z1ne (.orbit rep pis s1 s0);exact hIM 0 m _ j hj (zero_le _) (ble_eq.mp (qE.mp hbd j hj))
  dsimp only[Z1T] at hbd;simp only[all_append,qA] at hbd;obtain ⟨jA,pps,hmap,hfix,hp1,hp0⟩:=jB hin
  have hnr:st.rM.testBit rep=true:=by simp only[or_eq_false_iff] at jA;exact bt0 jA.1
  have v3:rep < 2 ^ c.cf.r:=hi.core.rem_lt rep hnr;have v8:=(aVPFS st.G bx ex es pps).mp hfix
  by_cases hrepH:Z3L ms rep∈H
  · exact ih1 ms ks wf F H _ (rep :: bx) ex es hbd.1 hs (YQ hs hvc hcg hpv (Z3x (Z3v hvc) (Qe hvc) hs.hHo) hi v3 hrepH) hp1
  · by_cases hex:∃ pr∈pps,Z3L ms (lN pr.1 pr.2 rep)∈H
    · obtain ⟨pr,hpr,hpM⟩:=hex;obtain ⟨_,hc,hnib⟩:=gPNS hvc pis pps (hpt ▸ hmap) pr hpr;obtain ⟨hfg,hfex⟩:=v8 pr hpr;have hstep:=XE hs hvc hcg hpv hi v3 hc hnib hfg hfex (by rwa[← hnib rep v3]);have v9:=ih1 ms ks wf _ _ _ (rep :: bx) ex es hbd.1 hstep.1 hstep.2.1 hp1;rwa[Zc wf hstep.2.2 H c.cf.k c.cf.wo c.cf.W] at v9
    · exact ih0 ms ks wf F H _ bx _ _ hbd.2 hs (Yo hpv hi (Yf hvc v3 hrepH (hpt ▸ hmap) hex)) hp0
 | elim x t wi s0 ih0=>
  intro ms ks wf F H st bx ex es hbd hs hi jB
  have hin:hIn 0 m (.elim x t wi s0)=tt:=by obtain ⟨j,hj⟩:=z1ne (.elim x t wi s0);exact hIM 0 m _ j hj (zero_le _) (ble_eq.mp (qE.mp hbd j hj))
  obtain ⟨jA,hvl,hp0⟩:=jB hin
  have hnx:st.rM.testBit x=true:=by simp only[or_eq_false_iff] at jA;exact bt0 jA.1
  have htc:t∈c.cf.tg:=by simp only[or_eq_false_iff,Bool.not_eq_false',qCm,qD] at jA;exact jA.2
  have v2:x < 2 ^ c.cf.r:=hi.core.rem_lt x hnx;have v1:=Z3x (Z3v hvc) (Qe hvc) hs.hHo
  have hvl':VL c.cf.r c.cf.k c.cf.mS c.cf.gS (c.xy st x).Gs t wi=true:=by rw[← vLF];exact hvl
  have v7:Z3L ms x∉H:=fun hx_in=>Z5 hs hvc ht (YQ hs hvc hcg hpv v1 hi v2 hx_in).core.lt (YQ hs hvc hcg hpv v1 hi v2 hx_in).core.memH htc hvl';exact ih0 ms ks wf F H _ bx (Z4x ex x) (x :: es) hbd hs (YR hpv hi v2 v7) hp0
def FBO (cf:Cfg) (tP tN:Nat):Prop:=
 ∀ (ms ks:LF) (wf:WF) (F H:SS),Z3Z cf ms ks wf F H->
  (cf.mS≠0->(cf.k=0∨cf.fE=true)->∅∈H)->(cf.mS≠0->cf.k=12-cf.r->ms.toFinset∈H)->
  (tP:Int)-(tN:Int)≤ ∑ A∈H,(2*((cf.k*cf.wo+∑ i∈A,wf i:Nat):Int)-(cf.W:Int))
abbrev VW:=FBO
abbrev mPV (cf:Cfg):=mkPv cf.k cf.wo cf.ws (1 <<< cf.r)
abbrev mC0 (cf:Cfg) (pt:PT) (p n:Nat):ZC:=⟨cf,pt,mPV cf,p,n⟩
def LC (cf:Cfg) (cg:LN) (pt:PT) (sk:Skel) (p n lo hi:Nat):Prop:=
 cO cf=tt∧cg=Z4u cf.gS∧zP (mC0 cf pt p n) lo hi sk (Z3W cf (Z4u cf.gS) (mPV cf)).1 (Z3W cf (Z4u cf.gS) (mPV cf)).2 0 []
lemma Tc {b:Z4w} {cf:Cfg} {cg:LN} {pt:PT} {sk:Skel} {lo p n:Nat}
 (hb:bOk b cg=tt) (wss:List (LN)) (h:ZT cf cg pt sk lo wss p n=tt:=by decide+kernel) (hcb:cf.ba=b:=by rfl):LC cf cg pt sk p n lo (lo+wss.length):=by
 dsimp[bOk] at hb;simp only[qA,qBi] at hb;have hcg:cg=Z4u cf.gS:=by dsimp only[Cfg.gS] at *;exact hcb ▸ hb.1.2
 dsimp[ZT] at h;simp only[qA] at h;refine ⟨h.1,hcg,?_⟩;have hz:=h.2;rw[hcg] at hz;exact zGP (mC0 cf pt p n) lo (lo+wss.length) wss sk _ _ 0 [] hz
lemma Tm {cf:Cfg} {cg:LN} {pt:PT} {sk:Skel} {lo mid hi p n:Nat}
 (h1:LC cf cg pt sk p n lo mid) (h2:LC cf cg pt sk p n mid hi) (hlm:lo≤ mid:=by decide) (hmh:mid≤ hi:=by decide):LC cf cg pt sk p n lo hi:=
 ⟨h1.1,h1.2.1,zPM (mC0 cf pt p n) lo mid hi hlm hmh sk h1.2.2 h2.2.2⟩
theorem Tz {cf:Cfg} {cg:LN} {pt:PT} {sk:Skel} {m p n:Nat}
 (hb:bOk cf.ba cg=tt) (h:LC cf cg pt sk p n 0 m) (hbd:(Z1T sk).all (fun j=>ble (j+1) m)=tt:=by decide) (hpt:pt=mNP cf.r cf.pS:=by rfl):FBO cf p n:=by
 dsimp[bOk] at hb;simp only[qA,qBi] at hb;have hvc:=hb.1.1;have hcg_eq:cg=Z4u cf.gS:=hb.1.2;have hcg:Z4v cf.r cf.gS (Z4u cf.gS)=true:=hcg_eq ▸ hb.2;obtain ⟨hcfg,_,hz⟩:=h;dsimp[cO] at hcfg;simp only[qA,qD] at hcfg;have hpv:=mPo cf.r cf.k cf.wo cf.ws hcfg.2;intro ms ks wf F H hs hbot htop;exact zOk (mC0 cf pt p n) hvc hpt hcfg.1 hcg hpv m sk ms ks wf F H _ _ 0 [] hbd hs (Qf hs hvc hcg hpv hbot htop) hz
abbrev C (b:Z4w) (k:Nat) (tg:LN) (f:Nat):Cfg:=
 ⟨b,k,tg,if tg.length≤ 2 then 1 else if tg.length≤ 4 then 2 else 3,
  if beq f 0 then 4 else if beq f 17 then 0 else 3,
  if beq f 0||beq f 17 then 0 else (f-1)% 4,
  if beq f 0||beq f 17 then false else beq (((f-1)/4)% 2) 1,
  if beq f 0||beq f 17 then false else beq ((f-1)/8) 1⟩
def cK (b:Z4w) (cg:LN) (pt:PT) (xs:List (Nat × LN × LN × Nat)):Bool:=
 xs.all (fun x=>Z3X (C b (x.1 % 32) x.2.1 (x.1 / 32)) cg pt x.2.2.1 (x.2.2.2 % 65536) (x.2.2.2 / 65536))
lemma gK {b:Z4w} {cg:LN} {pt:PT} {xs} {kf:Nat} {tg:LN} {ws:LN} {pn:Nat}
 (hb:bOk b cg=tt) (hall:cK b cg pt xs=tt) (i:Nat) (hi:xs[i]?=some (kf,tg,ws,pn)) (hpt:pt=mNP b.r b.pS:=by rfl):
 FBO (C b (kf % 32) tg (kf / 32)) (pn % 65536) (pn / 65536):=
 YS (C b (kf % 32) tg (kf / 32)) cg pt hb hpt ws (pn % 65536) (pn / 65536) (qE.mp hall _ (mem_of_getElem? hi))
def cQ (xs:List (Z4w × LN × PT × LN)):Bool:=
 xs.all (fun x=>Z3X (C x.1 0 [] 17) x.2.1 x.2.2.1 x.2.2.2 0 0)
lemma gQ {xs} {b cg pt ws} (hb:bOk b cg=tt) (hall:cQ xs=tt) (i:Nat) (hi:xs[i]?=some (b,cg,pt,ws):=by rfl) (hpt:pt=mNP b.r b.pS:=by rfl):FBO (C b 0 [] 17) 0 0:=
 YS (C b 0 [] 17) cg pt hb hpt ws 0 0 (qE.mp hall _ (mem_of_getElem? hi))
def cB (xs:List (Z4w × LN)):Bool:=xs.all (fun x=>bOk x.1 x.2)
lemma gB {xs:List (Z4w × LN)} (hall:cB xs=tt) {b:Z4w} {cg:LN}
 (i:Nat) (hi:xs[i]?=some (b,cg):=by rfl):bOk b cg=tt:=qE.mp hall _ (mem_of_getElem? hi)
abbrev mP (b:Z4w):=mNP b.r b.pS
abbrev I:=Skel.branch
abbrev J:=Skel.leaf
abbrev N:=Skel.orbit
abbrev O:=Skel.elim
abbrev KOk b cg pt xs:=bOk b cg=tt∧cK b cg pt xs=tt
abbrev Ob s g:=bOk s g=tt
abbrev uN (k:ℕ) (F:SS):=¬ Z5s k F
end UC
namespace UCC
open UC
def hx0:=0x2c688
def hx1:=0x2c681
def hx2:=0x25681
def hx3:=0x25688
def hx4:=0x2c650
def hx5:=0x2b888
def hx6:=0x2c642
def hx7:=0x2c611
def hx8:=0x2c60a
def hx9:=0x2b881
def hx10:=0x23a88
def hx11:=0x1d888
def hx12:=0x1ca88
def hx13:=0x25650
def hx14:=0x2b850
def hx15:=0x23a81
def hx16:=0x1d881
def hx17:=0x1ca81
def hx18:=0x2560a
def hx19:=0x25611
def hx20:=0x25642
def B0:Z4w:=⟨4,0,4,[1,1,1,1],[7,11,13],[0x688,0x650,0x458,0x4c8,0x2d0,0x298],3⟩
def G0:=[7,11,13,15]
def P0:=mP B0
def B1:Z4w:=⟨5,0,12,[3,3,2,2,2],[7,11,19],[0x4688,0x4681,0x44c1,0x44c8,0x28c8,0x28c1,0x2701,0x2708,0x3881,0x3888,0x3508,0x3501],4⟩
def G1:=[7,11,19,15,23,27,31]
def P1:=mP B1
def B2:Z4w:=⟨5,0,14,[4,3,3,2,2],[7,11,21],[0x4688,0x3850],1⟩
def G2:=[7,11,21,15,23,31]
def P2:=mP B2
def B3:Z4w:=⟨5,0,9,[2,2,2,2,1],[7,11,28],[0x4688,0x4681,0x44c1,0x44c8],2⟩
def G3:=[7,11,28,15,31]
def P3:=mP B3
def B5:Z4w:=⟨6,0,6,[1,1,1,1,1,1],[7,11,52,56],[hx0,hx1,0x2c4c1,0x2c4c8,0x254c8,0x254c1,hx2,hx3,0x84e5,0x84ec,0x86ac,0x86a5,0x16a5,0x16ac,0x14ec,0x14e5],4⟩
def G5:=[7,11,52,56,15,55,63,59,60]
def P5:=mP B5
def B6:Z4w:=⟨6,0,6,[1,1,1,1,1,1],[7,25,42,52],[hx0,0x294e0,0x2a318,hx14,0x204e9,0x22159,0x23a11,hx2,0xd4c4,0xaa1c,0xb154,0x86ac,0x1086b,0x1414b,0x11a23,0x15303,0x1d842,0x1ca0a,0x19162,0x1832a,0x3315,0x44cd,0x16a5,0x285d],5⟩
def G6:=[7,25,42,52,31,47,55,59,61,62,63]
def P6:=mP B6
lemma b0:cB [(B0,G0),(B1,G1),(B2,G2),(B3,G3),(B5,G5),(B6,G6)]=tt:=by decide+kernel
lemma o0:Ob B0 G0:=gB b0 0
lemma o1:Ob B1 G1:=gB b0 1
lemma o2:Ob B2 G2:=gB b0 2
lemma o3:Ob B3 G3:=gB b0 3
lemma o5:Ob B5 G5:=gB b0 4
lemma o6:Ob B6 G6:=gB b0 5
lemma kQ:cQ [(B0,G0,P0,[0x28110b2344293]),(B1,G1,P1,[0x90158cce4622cac0420b008412310e56043158a2e08614c92d840a2c4824d463985330983243105b10523]),(B2,G2,P2,[0x32c20a92d2981663010c82a08641992e08190c2549310224811142a4914205015091c21109488502e102b10c98864c429258291430613]),(B3,G3,P3,[0xc4350528c820461510206a18308cc464902a2c22214502920124a1836872b00b1984308c4806298514628a2751843a8e498ac241a32920d63349423124b211388e0a0b]),(B5,G5,P5,[0xe2e688c478ac0c10d0121308c0130cc60904612186609422c1098468498452148842320cc2819212908524251898448891685210901243128e61d46284b308c18320d90984662924c0890a454206c2cd18719a240896609090460848c438ac630204444b04484923052250d2321308c50b904d0838910e0b,0x3100a01b060c036420241195043a2c2139461286419728c0490cdcc3032021486485c8b04a8501724]),(B6,G6,P6,[0x2288298c011c935b2644a82511865c3604430e1b043301b023108861e261cc3084e5184210889c930e458e49988144cad90b204e3c5702312225a23188108861e27110c2119c8308861c27443204160b])]=tt:=by decide+kernel
theorem Z42:FBO (C B0 0 [] 17) 0 0:=gQ o0 kQ 0
theorem Z43:FBO (C B1 0 [] 17) 0 0:=gQ o1 kQ 1
theorem Z44:FBO (C B2 0 [] 17) 0 0:=gQ o2 kQ 2
theorem Z45:FBO (C B3 0 [] 17) 0 0:=gQ o3 kQ 3
theorem Z46:FBO (C B5 0 [] 17) 0 0:=gQ o5 kQ 4
theorem Z47:FBO (C B6 0 [] 17) 0 0:=gQ o6 kQ 5
def B7:Z4w:=⟨6,1,32,[5,5,4,4,4,4],[15,23,27,39,43,51],[hx0,hx1,0x2c4c1,0x2c4c8,0x2a8c8,0x2a8c1,0x2a701,0x2a708,hx9,hx5,0x2b508,0x2b501,0x22ac1,0x22ac8,0x22748,0x22741,hx10,hx15,0x23541,0x23548,0x254c8,0x254c1,hx2,hx3,0x14ac8,0x14ac1,0x14741,0x14748,0x13948,0x13941,0x13b01,0x13b08,0x158c1,0x158c8,0x15708,0x15701,0x1d501,0x1d508,hx11,hx16,0x1c548,0x1c541,hx17,hx12,0x1a941,0x1a948,0x1ab08,0x1ab01],6⟩
def G7:=[15,23,27,39,43,51,31,47,63,55,59]
def P7:=mP B7
def B8:Z4w:=⟨7,2,58,[8,8,8,6,6,6,6],[15,23,39,71],[0x1ac688,0x1ac681,0x1ac642,0x1ac650,0x1ac611,0x1ac60a,0x1ab881,0x1ab888,0x1ab80a,0x1ab811,0x1ab850,0x1ab842,0x1a3a42,0x1a3a50,0x1a3a11,0x1a3a0a,0x1a3a88,0x1a3a81,0x1a560a,0x1a5611,0x1a5650,0x1a5642,0x1a5681,0x1a5688,0x19d888,0x19d881,0x19d842,0x19d850,0x19d811,0x19d80a,0x19ca50,0x19ca42,0x19ca81,0x19ca88,0x19ca0a,0x19ca11,0xee888,0xee881,0xee842,0xee850,0xee811,0xee80a,0xecc50,0xecc42,0xecc81,0xecc88,0xecc0a,0xecc11,0xe5c88,0xe5c81,0xe5c42,0xe5c50,0xe5c11,0xe5c0a,0xe6a81,0xe6a88,0xe6a0a,0xe6a11,0xe6a50,0xe6a42,0xf580a,0xf5811,0xf5850,0xf5842,0xf5881,0xf5888,0xf4a42,0xf4a50,0xf4a11,0xf4a0a,0xf4a88,0xf4a81,0x11ea42,0x11ea50,0x11ea11,0x11ea0a,0x11ea88,0x11ea81,0x11dc50,0x11dc42,0x11dc81,0x11dc88,0x11dc0a,0x11dc11,0x133a81,0x133a88,0x133a0a,0x133a11,0x133a50,0x133a42,0x135688,0x135681,0x135642,0x135650,0x135611,0x13560a,0x12bc42,0x12bc50,0x12bc11,0x12bc0a,0x12bc88,0x12bc81,0x12e60a,0x12e611,0x12e650,0x12e642,0x12e681,0x12e688,0x15e881,0x15e888,0x15e80a,0x15e811,0x15e850,0x15e842,0x15cc88,0x15cc81,0x15cc42,0x15cc50,0x15cc11,0x15cc0a,0x174650,0x174642,0x174681,0x174688,0x17460a,0x174611,0x173842,0x173850,0x173811,0x17380a,0x173888,0x173881,0x163c0a,0x163c11,0x163c50,0x163c42,0x163c81,0x163c88,0x166642,0x166650,0x166611,0x16660a,0x166688,0x166681],8⟩
def G8:=[15,23,39,71,31,47,79,55,87,103,63,95,111,119,127]
def P8:=mP B8
def B9:Z4w:=⟨6,2,66,[10,10,10,8,8,8],[15,23,39],[hx0,hx1,hx6,hx4,hx7,hx8,hx9,hx5,0x2b80a,0x2b811,hx14,0x2b842,0x23a42,0x23a50,0x23a11,0x23a0a,hx10,hx15,hx18,hx19,hx13,hx20,hx2,hx3,hx11,hx16,0x1d842,0x1d850,0x1d811,0x1d80a,0x1ca50,0x1ca42,hx17,hx12,0x1ca0a,0x1ca11],6⟩
def G9:=[15,23,39,31,47,55,63]
def P9:=mP B9
def Ba:Z4w:=⟨5,2,56,[9,9,8,8,8],[15,23,27],[0x4688,0x4681,0x44c1,0x44c8,0x28c8,0x28c1,0x2701,0x2708,0x3881,0x3888,0x3508,0x3501],4⟩
def Ga:=[15,23,27,31]
def Pa:=mP Ba
def Bb:Z4w:=⟨6,2,46,[6,6,6,6,6,4],[15,23,47],[hx0,hx1,hx6,hx4,hx7,hx8],3⟩
def Gb:=[15,23,47,31,63]
def Pb:=mP Bb
def Bc:Z4w:=⟨6,1,18,[2,2,2,2,2,2],[15,31,47],[hx0,hx1,hx6,hx4,hx7,hx8,0x2c40b,0x2c419,0x2c458,0x2c443,0x2c4c1,0x2c4c8,0x2c2d0,0x2c2c2,0x2c283,0x2c298,0x2c21a,0x2c213,0x2c053,0x2c05a,0x2c099,0x2c08b,0x2c0ca,0x2c0d1,0x25443,0x25458,0x25419,0x2540b,0x254c8,0x254c1,0x252c2,0x252d0,0x25213,0x2521a,0x25298,0x25283,0x2508b,0x25099,0x2505a,0x25053,0x250d1,0x250ca,hx18,hx19,hx13,hx20,hx2,hx3],6⟩
def Gc:=[15,31,47,63]
def Pc:=mP Bc
def Bd:Z4w:=⟨5,1,20,[3,3,3,2,2],[15,23],[0x4688,0x4681,0x4642,0x4650,0x4611,0x460a,0x3881,0x3888,0x380a,0x3811,0x3850,0x3842],4⟩
def Gd:=[15,23,31]
def Pd:=mP Bd
def Be:Z4w:=⟨6,1,24,[3,3,3,3,3,3],[31,47],[hx0,hx1,hx6,hx4,hx7,hx8,0x2c40b,0x2c419,0x2c458,0x2c443,0x2c4c1,0x2c4c8,0x2c2d0,0x2c2c2,0x2c283,0x2c298,0x2c21a,0x2c213,0x2c053,0x2c05a,0x2c099,0x2c08b,0x2c0ca,0x2c0d1,0x25443,0x25458,0x25419,0x2540b,0x254c8,0x254c1,0x252c2,0x252d0,0x25213,0x2521a,0x25298,0x25283,0x2508b,0x25099,0x2505a,0x25053,0x250d1,0x250ca,hx18,hx19,hx13,hx20,hx2,hx3],6⟩
def Ge:=[31,47,63]
def Pe:=mP Be
def Bf:Z4w:=⟨5,1,22,[3,3,3,3,3],[15,31],[0x4688,0x4681,0x4642,0x4650,0x4611,0x460a,0x440b,0x4419,0x4458,0x4443,0x44c1,0x44c8,0x42d0,0x42c2,0x4283,0x4298,0x421a,0x4213,0x4053,0x405a,0x4099,0x408b,0x40ca,0x40d1],5⟩
def Gf:=[15,31]
def Pf:=mP Bf
def Bg:Z4w:=⟨6,1,24,[3,3,3,3,3,3],[15,51],[hx0,hx1,0x2c4c1,0x2c4c8,0x254c8,0x254c1,hx2,hx3,0x13948,0x13941,0x13b01,0x13b08,0x1a941,0x1a948,0x1ab08,0x1ab01],4⟩
def Gg:=[15,51,63]
def Pg:=mP Bg
def Bh:Z4w:=⟨4,2,36,[5,5,5,5],[15],[0x688,0x681,0x642,0x650,0x611,0x60a,0x40b,0x419,0x458,0x443,0x4c1,0x4c8,0x2d0,0x2c2,0x283,0x298,0x21a,0x213,0x53,0x5a,0x99,0x8b,0xca,0xd1],5⟩
def Gh:=[15]
def Ph:=mP Bh
lemma b1:cB [(B7,G7),(B8,G8),(B9,G9),(Ba,Ga),(Bb,Gb),(Bc,Gc),(Bd,Gd),(Be,Ge),(Bf,Gf),(Bg,Gg),(Bh,Gh)]=tt:=by decide+kernel
lemma o7:Ob B7 G7:=gB b1 0
lemma o8:Ob B8 G8:=gB b1 1
lemma o9:Ob B9 G9:=gB b1 2
lemma oa:Ob Ba Ga:=gB b1 3
lemma ob:Ob Bb Gb:=gB b1 4
lemma oc:Ob Bc Gc:=gB b1 5
lemma od:Ob Bd Gd:=gB b1 6
lemma oe:Ob Be Ge:=gB b1 7
lemma of:Ob Bf Gf:=gB b1 8
lemma og:Ob Bg Gg:=gB b1 9
lemma oh:Ob Bh Gh:=gB b1 10
lemma k0:KOk B7 G7 P7 [(0,[0],[0x0],0),(1,[0],[0x312181dc628b861d56eb861a8a0288412097358e1820e3b],0),(2,[0],[0x312181dc675c30d45014420904b9ac10a1a8b041d46e1880840b318344090a53068915c9321522b91681214961225a44246389034324ac60692a581239a29225c28255c930c85214c8a64b2390a465722c950e6402b0cf3861c20c11e2b],0),(3,[0],[0x1890c0ee3386202102cc60d020593201586008163041646a106810148670c10711881214a64090a4b0280a254342cc805618b92604a45728c5c93d10250aa148ae458b91619c1089110912b180509254306614091229c888121496049724d024298c45020904592c6605720d024290cf3861c20c11e2b],0),(4,[0],[0x34e1880840b318e1820e23008102c9900ac300812048950d720d024290cf3861c20c11e2b],0),(5,[0],[0x69c31010816631e70c3841823c5638608388c02040b],0),(6,[0],[0x205804e1880840b318e1820e23],0)]:=⟨o7,by decide+kernel⟩
lemma k1:KOk B8 G8 P8 [(0,[7],[0xd100a0703172d8f478c0ed8c6c6034400c5da64c4a48909492dcd8da04025dcb],100),(1,[7],[0x4a4c906aa9167220740ea941ae8434ac62a2eb0c7a0d67a2563d06bd081d1c40ee85e88d8f470f2207561385a17a266358ab0721aaa2d670c32ac270b59a303ad09c2717a6160e52503bc10d36103a34e841cc541ab43911ac558656b347857a2c62ea4d6d69e9ec045b165c54581c182010140c08045c5b,0x7185c65c543281de08657081d1a81d70562077c21964a2ea8c171561c45c658354c45c4dc340eb22c2a1a1351a1340eb8662194c961562135916146a134c903b8506b91388ba8b02e26f426881d3881d4a8a91a81d3863229471868352a4693256203ae103ab1614aa0d40ee840eaa40eb240ea66a203ba1,0x6be08021ac34b42b08b0b808732d69e82b463d11b382d081db0bd3d808752da85829363d9330caf64ac0e81d3281d92bd91b1ec8d9eca5f047b2367b266705ec95e841ca6294b82077420e64a3d92b3d91bb0bd9c36a6b161701165582e38c1a8b8b305c59c941aa4ae08b8ab0e29481de081d928b89b05c,0xd81dc31e1ec0c3ba63c3d818774c1da180e818d3705457f78070ea5904f60e1d4b036260b0d30b18b0d2e08b2c303a38b822c92c0eb82589a22ca2c349c2e0b422ca8c823161a608b1a08d18b2937f82787b0a07031ea99918981312923031308d0c8c0607068100a332c0b0b8087b2c2cb0d69e82b86008,0x7841d131292242524b7363681009772c3cbd3c01008b72c60302d864890],0),(4,[7],[0x28ccb1812300c060b30c54180c1c430040804141b1a050291668140a418023d90308431c1bd830742da1ac505c0c5926565854181c1a100c0e04025c4b0ccc09c9185906c6034400cb9a600c09ad3c0560cbab4f0f6062d931ec85809405ec819ecd1b02c8b12e0b4358a0b818b24ca8341c38860402140b,0x1224360770c6462604c4a48c0c4c2343230181c1a040],0),(5,[7],[0x1224360770c0804141b1812300c060b30c54180c1c431a0502906565854181c1a100c0e04025c4b0040402140b],58)]:=⟨o8,by decide+kernel⟩
def J7:=C B8 2 [7] 0
def S0:=(N 9 [1,2,7,6,8,13,14,12,42,44,43] (N 18 [3,23,20,107,104] (N 33 [6,123,131] (I 66 (J 0) (N 72 [33] (J 1) (J 2))) (J 3)) (N 3 [3] (J 4) (J 5))) (J 6))
abbrev t0:=LC J7 G8 P8 S0 0 15
lemma c0:t0 0 7:=Tc o8 [[0x998150521832c64182b0530660f2203489485410c415e060cd198b5908730c6b116485ac518d622e823588b448d622c06b58a35080d285216b34614290b335828722d222249141406d040680d30c85ace181901aa10140da4406c14069434102a28e040c80d308a3210c42988931187116b3066242801c63,0x18a6418770c6b1566242801c731896320ca198b5908738c830a60360c15806d04830a60ac1419832261085308429c140ab0544878c139b0a1141e2b0364c2844178af13930a1045cc4850038a6832562ae041a1a82a4290c068e45901a7102a19833060a406c840680d82a860c9],[0x1a034c205452034618280de08c101a611880d0a406984068c70203406a84068a406854068c68203406a8406d040680dc098622d100d030a68880d0a682034614880d185414480d01a6141414d05420185b0181b01aa081853053116080606c068185305311e084230c069824218ca080d609224214f0251,0x40698429a0a4414942034c20348a03461c09812868203541185120a78203406d04068c583110520360a03431a080d50542035414480d1852201b4101a910c5821085b01a4214c068c26090863c0d440685203682506220a70203406d054203541445120a58150522034068a4068530501aa085406c458271,0x80da08290530508916435a0834c2114610a80d1ca3203662054338901a035828280d0a7020342901a89a095406b02508c20a68203512035823101a037022280d604c201b81608310a6839101ac08520348a0a6820a406e04c20348901a2960ac40680d5080dc080d22815604520a5816080d0a406e04c20c,0x34068a414c14068520360ac101a1482bc108a074520a42a0540a9141a0ce040680d308450a81502a6182a62054328901d608a1148290c819033810680d0390d45305065128a8a1988290ad0406],[0x2a1880d28b04853184214c0690ac308429a840680d309426090863a8c340684214c195080d01a89214a6114843584214ea25884230c2a034a1214c6034c1284847184214c069424230ca2108c31824214c210a6a18884514406a2422c440680d30a840680d308a2c108884143996108530541691210c741,0x3184214c069824218caa03406b040aa24069431101a1480d60a44847184230c609086306205582115224214ca3050842984214f42064152158622505211c61085341442b0ca20345101a03542610a282b04068c3a108b6101a30f0484318229085310ac314260908c38882901aa102a8902a509840694251,0x34a11880d5880d304a12880d18403542c14883118722034c1286a21146101aa1306224294c0680d448890ca62588e2034c10a80d68b22034c12846218406b04068c5220348930406a84a21145101aa13062242b0c214a60341544484618451620cb040c8c2150c311210a6034292244501a6101a88b0484,0x61c4444815148910682918462034aa034c11862203406b04e20c4068a406c44a24292c210a62880d214c6108538880d284847180d01a6122406a840680d30b048431d24210a65080d284c1211861148901aa1304843184214c4218f43510842988531884718a218406b04843184214e234501a0351222432,0x54210d65883444908e301a1085308429835425101a448892880d01aa101a14432893080a8640a5220d01544964ce1c40c22e894641a51455824218c0548429829210c7a101a5080d3080d2880d0c5824298c210c6114a1210a6034a130484],[0xc196301b0668c3080dc080d1ec8dc8583060ac050b60541445815184140dc18630c203462034a20358122a46820342911406e0406b02c105260c8414a42c0984068c329032909c40680d30b02036425101a034c2034a24848bc10522880d48d843080d2880d1880d604524182b4185348d062306f60c1d43,0xd840688a054c29101a035820346248c8406a42488292280d1846381a880d01ac11821908a908c40a863c108a0358203642911220540d60ac2909440682a0c862488a381302034c203582034a39101ac0982034c228cc40680d6080d4880d18703518690662c830a78105306c2c833060d01b064ad064ccc0,0xd84150e20d06406944068c40686291948169145895238984228b11c4c2290521502a055820d0c23101a30a440680d308640680d3094642484308a40a64245052308540aac40a81590834608c23101a7101ad100d3080d9086406852309829100d3088a0364251c080d01a6101a510c2310c21900d30f0418,0xa8150c41a075a10540a834a2034510c78203406b0431a280d0c451c280d304619880d144068c6320340a8e22901a054c514945454c5a17043203406b040680d314326149406cc54951406e85c14881903415244510c6c21140d0643101a5101a91c480d0a40698406862c10c2195840680d14947220a414,0x3461064c60343102a61064a60306303053c080c0ac0683063b080c14c61f080d1442901a4501a6106686f648c7b2561880d7b2c60c5eca9815034317b3860c418855ec8d8f646c293d9533d9c32880d0a40698406b02317b3460351122229384037025101a1491406a22c0985ec918330b03ad082918831,0x928845384620e4310680db0c1bd830754c7b296035ece18f646c623d91b288334320dec183a563d91b060c603461837b060eb1e047b296065eca98617b3460c5252c5ecc58190c41498a92945617b386184f670f423d91b0a4613d9c3c08f646c7b2378101af670f820c0ac060c61140a944182980c14e22,0x41bd830752d06f60c1d2b0522882906c1bd830758c1c82],[0xc852311758606529033a1544b13453103271032066423100c2980d898545d458f642c1abd9531eca18647b2160a5eca98f642c338103214bd9a3242f64ac7b2167b2a67103206642358d3c0bd9631ec859eca98d62e148bc08523100c29819485e1ec0c3aa61ec85b4358a0b818b34f021517506b4f61583,0x2ea4c0a8622ea2c0c8191482a188bac305d4985c718630502e2ad69ec2b265a7b0ad19ac5c29c7217b286d62e14c305c4582e22c620a45c7182e22e4a0b8abe08310a45d5182e26c428b88b0c6420b88b10a188b8c38281502a6102a0550b2103231175266841ab42290520a543051c4148c219032828540,0x3d8564c17586b4f6158b1ec8d9eca5815032317b3863d91bd082e2ac314140a8bac37b216d62e148b1ac5c29165a7b0ad18f642dac5c29c7c11ec8d8157b2960540c8c5ece1b123d91bc28f646c31e08f652c31d096103215152b08c40af040ae840ad140ac947b25618c15ec8582e38c17166310baa302a,0x2d],[0x1a0bd96301c2d81ca986101ca9d04308641d218194840cd04520385b03a5305a0c83953039630320658229828295040cc84e2185814840cd04620646103321a88193040c9840c943419880e54c0c8a4148c62af642c787b030e8d9e0e1829185e1ec0c3b26064615040cb05e1ec0c3aa79103626d028148b,0x8296892158c34070b60641d298851881aa14428c4520a5a20a5624ac140e8290c80e16c298281938aa298819688195881950414b04623c0538ae05e1ec0c3a363d9331ec998c4148620c429a082918432f650c0ca42c0bd92b0320a414867020646118bd91b03230b0206642f668c0c8c20664206702064a,0x81948562064a14846201853a881a9330203381a081903341148e105a0cb040c819608a60a305414846206521505a2065413066228581a881a5378216052192c5250336152529033c103218e840c819188a11496268d040c819508a118831032c1148196882958c840a432688e25888518e1414819d081998,0x829188290cc840a682184320646385029a081d324b11c582184320646381787b030ea980634c0c8503818716c0ca0ac08503818754c141660a0b30c80c4d80c2d819033260640ca9816e0419031a60e90c0cac20199318819c081960682032c10c6420d40cf04318281853032066420640ca860a4158114,0x2064293081918702b117506bab4f0f6062d9300616c1da18f64cc18a42f660c0c2980614f0a1ec99818d36840c40c29bc1c30c80634c140e061c5b1ecc181853c0829584608c41486414863210320654218d040c85218e05e1ec0c3b261c4308c5610c219033c103218e843483514832064634105a148296,0x431175860a5212845d5181d072291620a74238984148c45d4981d06a290d248452c1052508c414b459117516142e08b8c3484148bac30c82eb0c508a1188a10c8b8c386834984628d2a114a4854229142074a91a4c20d4538105230b44149427105260a54148c39105260942c08c414a4250829308640c98,0x6698640b8b3030a6034a6075610c5211417030e698282e061cd30c819018d3032f0f6061d531ec99b020614c5141ad3c0560c7b236065ece1829584191eca9c85eca181d584148c41486414c847b2a7417b3063d91b032f670ca0862f660f02d0d6282e062c9b0622845c7182e26f820b89b0c642284508a,0x1eca5831485eca1b4358a0b818b34c686b1417031669f04030a60c4505c0c39a6b4f0158b031787b030ea9b40a052cc686b1417031],[0x10d20385be083b431820e94c168696081d1c438f04695080e8e23483943a083a43787b030e8d8f0f6061d1b1e1ec0c3a360ed0c30a42c0861a0bfc13c3d8503818f54c32413d838752c0ed0cd0ac201a530a815c0981a08f664cf658e4304f60e1d43030366462604c4a48c0c4c2343230181c1a04028ccb,0xa081b13282908189b7f78070ea182d1c4c931416e840b543610d205aa130c8416b42b0a42c11435118230643c10c3192421c58385242485834905a0b4a53082d05a34986420b4a505a34c858238e043486990921c098130321609620b72268d0416a42286821d7f82787b0a07031ea980e16c0e92c070b78,0x1224360770c0804141b024a0df9e0183a8604020a0d9812300c060b30c6a6b16170116558020ad69e82b065c54581c182010140c08045c5b00d8981da180634d817f78070ea58f652c281c0c38b6018d300c2dc84031a6c100c2d80616e438100c2d80616d82031a74105a6081d]]
theorem Z29:FBO J7 0 15:=Tz o8 c0
def J8:=C B8 3 [7] 0
def S1:=(N 9 [1,2,7,6,8,13,14,12,42,44,43] (J 0) (J 1))
abbrev t1:=LC J8 G8 P8 S1 0 0
lemma c1:t1 0 2:=Tc o8 [[0x204847184210c02908c3a884214c04908c3588d622c06904a102281088841438b691210c7090842184216c8210ac30484210c410888114241044842984214caa284028528110209055110448461841204847180d02402a04c118404904843180604c029023c42061c5328c060dec183a16d0d6282e062c93,0x108432884210e230d08461811210a602441210c628c14210a61085302a222882201441210c7410c260805285812084118841488150624102b8124412024811062201481a8805204e2084096880d02404a046101241088050440882404a04a24290c21586288110228100b11102512108604441214c6014a1,0x2432188098880910422024a20c90dec8184214c5100a209086300a4298c28841210c6214c6d0824210c7490820490a4b08421881210a61085328482224c101a104528121186110052048421d44210a620811211871100a025020a4228890a5308429822210c74500a05412488a2188290890ac3009210c6,0x908f650cf648e82f660c180580c14c208302b01805e04062860341829844048220cd0c06087110122083263018158236100a03422014c2024068521120b4201702b080988830630182980d060c70d00a488a2188220c94c01418a1805060560300b0880d0441829809060c70105240482034069041202522,0xd20e0406862037034101a3094120a421101a0888311837b060ea18f658cf652cf654c08bd9c31ec8de8402442084823d91b88bd9231ec91f047b2478901218841088292880988ac20240490642026a2f650c7b236048097b286024217b2478102a488a2054620a42088422b080d02702044218881560411,0x5d61a0a908290445d4182e22c11808181b005175060b88b0342980832175460ba830882ea0c620694c17136908520c4290445d4182e34c0d0c42905c45846020b8d398a2a0686de081b40a0520c837b060ea581815906f60c1d4b08906f60c1d4bc080c0ac0680c0ac820c10dec91815034311449101b210,0xa0b818726c282e061cd300c6980654c0634c0a0c8a2830282e061cd30885d61a4201411175060604c340a052cc0a1417030e4d80cc98321417030e6982e30c088b88b03027010120640a014220140288411808090460a282e061e9300a188229085d618050445d41811808185305d4585c7182a0b8d3188,0x2802bd94303626014031a72100c2dc1402a82908185300a06c4c5081a5301a1b782163d98302af642c0a862a0a42f650c7b21781030363d94b1ec8d8c408bd9c300a0185308a82f660d856840a862018530195308a0aa0bd90b1eca58227b2178106a0c82a1888508a82017020460a3d96390bd94303026,0x2af642d81030363d9c300a90bd90b03626d028148b1ac5c29163d90b022f650dac5c29860b8e34841417030e6984569ec2b860b88b0505c0c39a6114842eb0c7b286015ec858ba835a7b0ac18181300c29819787b030ec9831787b030ea980614f02065e1ec0c3a366040cbc3d818764c0ca42f0f6061d53,0x34358a0b818b34c1934358a0b818b26cb4f0158b2ead3c3d818b64c0b8c3030a60185314506b4f0158317569e1ec0c5b260502e34d69ec2b060606c787b030e8d9e1ec0c3aa6c08f0f6061d1b3c3d818754c0a014031a72100a9081853782163d9430],[0xf0f408042d1b02010506c0a0b818734c30383420181c08048c9608880303808b92c10082836f040d9848290654180c1c43104f60e1d4b3330272461641b180d10032e698140e061c5b03b432420540c0d8114040c09bfbc038750c0c8229081180809c0bfc13c3d8503818f54cc09184603459860402140b,0x141b1224360770c7e78060ea19812300c060b30c5c54581c182010140c08045c5b0281c0c38b67f78070ea59fe09e1ec281c0c7aa6018d3484c16047f82030e2dd05fde01c3a86030366462604c4a48c0c4c2343230181c1a04028ccb199a1a84850581008893609098a01008ba2d69e02b0604020a0d8f8,0x804]]
theorem Z2a:FBO J8 0 0:=Tz o8 c1
lemma k2:KOk B9 G9 P9 [(0,[8],[0x0],0),(1,[8],[0xe10a1c30f5369960c38d08122cb0162cb2e087559c6204143081112dd108077],0),(2,[8],[0x6e8a3056114506d329558a95a2c9708c31830a66191034a231195308a9118638d0541a197ab15987e4de914e6299688532206b881836915119433305988bea2c38570d03419894ca54aa350aac6130ca184e3034c2897081b82d184631e8430e5b05542c17a10c394d44642d45c30e9330e348187081224b,0x342048b2cc138c408286102225b1961140116cb1020a1b158394a1e6e62063ac618629b14a1660629e08621b2650a8b861d36285430c6406a986419a63a860cb0542d10c614314c0cd0868da845989b9485eb059c2bae45976a8c29cc5c285767050c7cbd8614f42b9862e458321518ae61e0860d8b35450,0x1c20ca1b06056183a862870c3d4da65830e],0),(3,[8],[0xe930143861ea70b82191d4314462851470431a12870c394c154289206454a50a38c660944623a86183648832911c53284718c344f1372903a8418042b58c3054613144a148518d0acb821d162cb821d16042bc124415488245a858250985820a16b14789b9481f1372883de4d48470c130810a0b3060a43,0x84324cc15086299030e1022c960689862912870c394c2042c2c9124410ac0a16021586291050b19431020a1b036c1a8062da70aa1160c530614c30c6a2e187499871a40c384091258312e51a280c3822c96042b1020a1b8148830a15cc30c53142a18632060d8314f045142a4512488c4a342489470545c3,0x42b0c642c51a030531880e14c62e5190ab91680e149608560c31838c60a162c518ca1b080561848a2545c30e932141a26a11661c69030e10244961030e1022c9619430750c2042c2d8302b0c44304c204282c1630c314c204292d821020a1b18218a650b04324cc150860d8b12658a30d13493502045a2c2,0x384d32c1871a10245961020a1b0408286d8302b0cc1060d81836a1160c858a23286a2e187499871a40c3840912585ca30718d42b9262e51e09a8143862ca61724cd40a1c316530344c5170c3a4c750d83],0),(4,[8],[0xc8e1110443286c201586182610214162845814c101018a6020c8314e041540860da8418b91608ae6180b820280a22c10160405a104615720c304c01088090844421510108645c23016008242232860c058180b41088c2180a30c70202908861204888124184630304d44642d45c30e9330e348187081224b,0x708040160c0ac3004c18290c20414360],0),(5,[8],[0x408286cc1815863060a431420cc38d2061c204892c020b906182604a0545c30e933470a430810a0b],0),(6,[8],[0x1871a40c384091258c18290c020810a0b],0)]:=⟨o9,by decide+kernel⟩
lemma k3:KOk Ba Ga Pa [(0,[12],[0x0],0),(1,[12],[0x712a4488b6b],0),(2,[12],[0x2405630d0364a6494f086a3d9645f21437925b39188b2b],0),(3,[12],[0xd2405632496ce4622cac730a6618cc9299a8d242b1882c1a0d518910e9606c92c1aa325324a78765827105832a24621cac315a48a2f65907d9609f65817821b10523],0),(4,[12],[0x3490158cce4622cac04490ac6494dcc299882c022496492c484a264a605844160349460d412310e560431984824d46098220b06330a05129228b821b10523],0),(5,[12],[0x90158cce4622cacc4148c04490ac620b],0),(6,[12],[0x20b01310523],0),(7,[12],[0x1],0)]:=⟨oa,by decide+kernel⟩
lemma k4:KOk Bb Gb Pb [(0,[12,16],[0x1ba6885e585cb430dce861b5e20b5b298f67531eaf105cda08277],0),(1,[12,16],[0x934bc9264cf14165bd4e88724d2d25d2ed412e3b504aae8202739aa2826a7924ba5dc92d37410139d2504d72d392670ee498e3b505a6ed4165bb485a7206aba0a1a6eb281c9c5e4932a7924c99e282d37c9b1193689c7a9da71da77a4b4dce304e7494135d8b704998bc12652fac799e549971058dc08077,0x249933d4e8b58f93c54752f04992bf3a537c51549a594d2664f349953c4e4caf33c2c6139dd025b91ac691a564c939354762f2c771d8c6b3aa9aa3a97963b8f4e955d8c2739ab9cf93fc2717a73b4ee6359e106aba6b9cf53fc2697a73b4ec4969bb984e78409ae5a1a8b4d2390135d0504b739492664f03,0xa96e8562fd0aa5f5d33394adc4974e2f72cb1f5d353952ce2f9662ff2ca5f5d33394af842a5db9f27b73e2e9a162edcf53db9e97fb726e5a38b58f539685b628a8ec5f58f53c1264afce92de942d4cf0b18d67741a6e4ab1c471596b1f27631ace9a6a8e95e58ee3b18d67741a6eaa2a935351d93c0e4d2f,0x1c2442b2d1054d8ca59326c4d669a21716329652c7e1e9d2cbe28b2cd3398d67841aaec9b345051dc3fcb2a7b1269c4aad93442d2c531acec834dc95612af842a5e88aa4d136c4b1706139e0c26bc414b6643317953d4e54b3a1993b54edd58bdbaa97953cce52b0],0),(4,[12,16],[0x842085682a10856412101110a4b110a4b411048854590a8444215845842108444c30a108470582610484c21904a2208a0882112130b04c0488a8442c9308409110cb0482c5381054154892415290954232020642a12a148a08190a84b0522412102544b608128204d0812412111084210908b0b44d10a0b,0xc2c150904428108510a8b19264110a21616209a2688525902324c41629a216160210b052220886044110484c250b88286c314c306d04c93210118a70a10e],0),(5,[12,16],[0x18582a122151644292d1050d90442442c2d020120510a0b],0),(6,[12,16],[0x60a8488585904428100910a0b],46)]:=⟨ob,by decide+kernel⟩
def Qx:=C Bb 2 [12,16] 0
def S2:=(N 33 [1,2] (J 0) (J 1))
abbrev t2:=LC Qx Gb Pb S2 0 3
lemma c2:t2 0 2:=Tc ob [[0x564b84d162b25c262ab9231d46ce5127928c19ca66a3b079a8ea1e446a4b49ca4297ace49f04496a4bc1deb38a7a12868b3927a2ce29c6429658714e33062183c18824ea224b2c3927198310a1d882547831029cc41924aac35275ce2063eda70ce53a6a183e9a850f22c390789fed88bfdb097fb60aec1b,0x30e49ead406729c134592c5255c2c962b44a4d170b258ad51c53989c2d16498ad164b84c64a30a719192622949c818f969c538ca886251a30e29ead406749a2d0c1e84a952b84e1386b1664b15c354b192c552a570b5470cea268b258ae172d051daa38673129552e12c54aa970a8aae494731928c19d24c,0xf462123cd6744f14968be0b14ce12c5c2a270aa4b154b854524d170952e14912544c4e1649a2c97098962e118a8c16824e5254b84a958b8544c968b85cb414731724c49dc930a7192c552a5255c2a952ac524b170aa54ad51c93a89c2b15494ab154b85464a312719152a24949c828f969c938c988a231a,0x24925b0e9230d16824e3224b6e512719a2ce61e8461924ba1e8b3927a2ce19e2419249874d4a87cb1089e449144a864d498782ce49d4470e2513d98728ec93b350a1ecd4187924919cc68c3897451a2b16134563359cc39284b2516c3a48c36720938ca6f4987939049d456720c3d5a712f461a3398cd675,0x496eb3a87917ace89d8824c7191a2b18959c944e32917acea1e0c40c77ace25d84708c8c5461c63929eb2cc7b39025d842530c9c918f16a033c884a3130e5a848f56a033c4b4e42479acb89eef4987b39031eeb2c97a15128564974392942a2b352a1e8b3897310c44ba6a143c8c18744ed492c3c1870ce9,0x5a722f461a33a8cd6760f462123cd6744f14964bd0b24cc9315c2c9689298ae164b47dd24bd098ae168b24b170b449970b44a564ab44b164b6e9a1e24e1364c9562b25a2e189728ea1da930973138558b235a2c564b862a30c7a25c94750f251d13c899270b45924a70b459344124bd09a2c9709a2c564b8,0x5c94760f251d13c895270ac5528a70ac55344128be0962a970962a554b8516eb3b07917ace89d882547191a2b18959c944e32917acec1e0c41477ace45d84308c833459cc3e08c3249783d1670cf120c9874d4b07cb1089e4566a183d9a830f249233a8d18722e4a2c5a2c258b466b398745184656720c3d,0x3079a8e91e6a3a27f6392f421aa68a354d472517250d5325aa4945f04364d15aa2f07aa4925e85a72183e9c850f461b23b44d8464a9295c2a958a294ae154ac7dd28be094ae158aa4d170ac49970ac4a564aac4a968b6e9c1e24e1354c9552aa562e189728ec1da931175138554b23562a554b862a3147a4,0x2e158a94d158b0cd6850f251d23b44edcf83a28d931b266a9b08d53346c99364cd532652ad1b61c1325c2d1629a2b1619ad0c1e4a3a47689db9e87fb722e4a1aa68a364e283117252c552e12c552a570a29a2c962b86eb41172561c991da26354c68d9aa64b351d23cd4744fec745f046c98d1b364d168b4,0x9332ae162b46cb14cb45b2790cc1e8468962c2c5d8962c968b14a96649935254e89a2a9c53258ad1b12c592d162d294acb114af8721983e43287c8648ed131b266a98d1b364cb16a9e08d1b364cb16a9d3a707a10a57259d83c96750f46a523b44d846a98d93354d846c99a364c9b266a99329568db0d095,0x13252b85b2662b45c2c96a994a52b85b26364dc33268a64999570a95a3668a6562d53c1314c570b54c6a9b8664b14c],[0xc2b152c14728ec93125cb394731924c45e072467215842b6a8c51dcb392772ce45d8451052b51310c66c4147b24b49c916324d059ca398e58722f859a3390ad682587a1033420cc125d0ec250c96730f751833a4893062143c18830e62518718f433620c3cd8824ea3459c8bc50494f459c2b912f0620a1b,0xeb49863fba4a72258d932354ad162bd4728ec932c54ad162932e168b258aa2c39293bd4718ec538a4c45e293097f748ce42b052b512652b2620a3d525a4e48b30d4947649e18722f759a3390ad8a30c76ace29dab3897a161054b512a54ac498a3c0e4a4e48b0a9614ac54b51458728f659a93922cc46a99,0x23532e164b458af51c63b14c99648a5cb38c7518a4c25fdd23390ac95255a2324ab46ca30672906452a228a2d494719931029cc60825279ace25e6b3857245d0858b0a562c5a8854b162dd4ea3989a2c962a54a54ab258a62b498a3fba52724591ac962a54c558a652a8d68a49329564b15ea392751974a2,0xd0c45ed4e53912c6c99a3654a95328d7094ae1364ce168d9aa6a2c93235c2d164b14e1629c2c56a99c2d1b364cc4d162ac532e164b94718ea3041893b14f5d48beba897b538ce42b0a562c59a22958b16624ca55a2c962ad2618fee929c89614ac58b0a962958b16624cb260c38c7aacd29c896a2346cd93,0x31e6b38a7a130b38a7a118bd8730f06a0a3bd8722f82c9344292c295858b14ad442958b16152c58b14ad44c48d52a54994aaa5c2a551385a2a54a992c554a9532955131b53a4e48b34592c5255a2e164b14c4e164a558a68b85329564b14c544d164b151a46a55c2c551325a2c57092ad164b858aa26293,0x149863b14ed8ec3a28d1b1aa668db08d53346e9d2c3d08d1b1b266a99a37430412c3a288b359d43cd6730f462063b14f048d315628d68b09a2c54aa37dd2c3a298a9946b442a58b16295a2d3a587291a3664b858a52d51cc3b12622ea2562cc570b460a3147a45c94730f1498539889568a29466b3987a31,0x46d848d588b162a594a52bc8630f6ea51d9264c9a366a9ecb187d9628fb2c49f046c99a364c9aa66c99a36c2364cd1bb84b0f82162c52b9b10c1e4b39879b1051d92742885458d931aa66c99a36c24c9a366c9ec3187a134452b162f61943ec3187c7518ec531b2668d8d53364cd1ba13252a8d68cd6850f,0x5a20a9b4414b6442e2c6c9a2169614adc31058d8885c5910b4b441636c244153688296c6a9a2169614ac54b882c6c88296c885a5a20b1b61c1220a5b441536364d10b8b0a562c5c416364414b6442e2d1058db086a9a21696442b2d1054da20a5b0a96295c416374e961f06846c99aa668d94a99354cd933,0x3848856]]
theorem Js:FBO Qx 0 3:=Tz ob c2
def Qy:=C Bb 3 [12,16] 0
def S3:=(N 1 [1,2] (J 0) (J 1))
abbrev t3:=LC Qy Gb Pb S3 0 0
lemma c3:t3 0 2:=Tc ob [[0x322d13183648b44d842288a4ad1304ad13c108ad1360d08d13611902b1244c8891689a8860c8c480354d14570583722d13511924494c230864a291a1649815892264448b44cc4286462401b264a2b42c1b91689988c9228a50a8922c20ca452461249443231225432382c53f9620ff2c21fe5823fcb02781,0x225844bc130448ba19109429191144a2a0c8545225c10642a4922b068449228925224914942912e08924560d0c8912291285225c104515c11489644c1a1512249245288924528d08128ad09248a519128704c431147045118d0a4584a17d0c41fa1843f430476098c1306858360a84b8222b068425609834,0xc946845185147059261890a2a193082a8a42a88329202ac1b1922984c9391064625148e0b44fa18839084522585214a289245252158052b152d24651485624914896a2014ac58b291925215944291284aa248b31144312890ac5118922e845118a845118a84856c2184856a11454244bc10c248b114a261,0x89542c1b8502a1a51025150d19064c54250e086218d0c2b14c51214543261054948531064a405583632253098a7220c9446291a1689a084530b14c1505684a161055428ac1b01a366c998b14c548ac1b18a60a91583742306ca1629b08c86162982a6122b06e1419314c1560de08150d188228a868c832a2,0x8a8584310ca85258a628592650b14f04610c8c2a164988a612486382c53850c4492912452320c8945231c10648a4928b0684c15084aa164988a5124b058a72218b045118d0a4585a261859260a984152560d80d1b354d459262a2560d8c93611919260ab06e8450b24c6112a8583782508646150b24c1530,0x184646150b24ca122942a21],[0x2600885a5a8b24e44916d13442c2c6462615090ac310aa448971050da0860b14d10a4b06125c118582c5305244b18984619160b44d10b0b18a66498625148b44d10a8b06250b0a16a2144a172248b0850b0a172382245a2600885c598b14e44896d13442c2c64a2616090ac510aa449171050dfdb9072181,0xa26228c322c162986291649a2149628644c230a454248b18492451848b2248e0912c61094c2c93144924530b14c611298a782309158248b24e848571050d850b24d10a8b06145a118542c9309248b28984619150b44d10b0b19266298a23148b44d10a4b0a250b0a16620c4a172248b0850b0a172342245a,0x8a6450c8c24548b05a26309146122c892382c1b145820c94624a45c8b24d10b0b0c93442a2c649862a1629a2149618a688525e085118912d42c1062c530ca858242b88286c19324c3162982ac1b0c522215b44d10b0b41210c1a1304c1a13054322d13442c2c344d10b0b61142d1324542c93442a2c22b05,0xb24c512491491c162982a12e088ac1a109425c111583432248b0b06d10b0b061649a21516c130684c13058a6885258c2c10857421885542c1225c41436324c4a191844a9150b44c61128c225912468583618a841918c4944b91629a21616826098260b24d10a8b042ba10856c2c11442aa160922e20a1b1,0xe1221716442d2d1058d9858260d094288545982649a2149609174210ad84225e0c4143614322d133091468992864255]]
theorem Jt:FBO Qy 0 0:=Tz ob c3
lemma k5:KOk Bc Gc Pc [(0,[16,26],[0x546f8ea8fe9cdd7cbb29b6728b043ead0188102179b130dce261b5c4c35b898677230bce46175c8c2db918577],1179648),(1,[16,26],[0xb8bbb5e37546b8ea9369cdd6cbc2996728b043aac386e4f61a6375e8e6ebc9cdd7339bada7b0b31c2f47385e4e70bb1ce16d3f09326ebd1cdd7639bada7375acf61c654b2c78765ee4e72da5d51ee3e319a754dacf619670bc5ce171b9c2d5728b043cae0698a1e7101881022e9b3c4e73c4d73c4b73c477,0xe1bc39c37472030b93182043e2c8d1c614d93cb2237058b2c4e18d375e4e6ebc5ca68cb1657e8ecb5c9ce1],0),(2,[16,26],[0x59d22aab8d4698f2254ac4d23570994443ba391c8d8e443ab3910eaae47227391c89ae622415e1c8a8747241569c90559722a159c8a8557828831d853e38b8d46e0e58274ba0ebd0e9f195c6a3647f8444e91f4dd23e5b9cd194e36224ba47c77050b375a4e6eb45cdd6339bac5772e283a8d0188102161b,0x4e351e4bd0808d6054b0265895569722ab8dc95559722ab4dc744cd7bb0c29c69a477044b2ad3e1d2a393a5471749d7a1d22ae39188b0e91559d22aab9cab98f82023595375e087658944e9722698dc944d9722694dc7344d7b2cc29c689c77044ba8460e951b1d0656874a8cce95195d22ae3a0ccb0e915,0xaba434e74869ae622c411ad1a058b324a2c10f2b5a8f0eb15d1d25ed3a4bd97479ace8f355e18c63b08d2a968a558a62ac4f4cce13d935f8d2eb1f8dd39ecb8d26b0e8fd4dcf5a6b9c2cc7e7414e6db1dc112c709b02358162c8d2c935a23962b25d7010eab1a4729564a65d7010ecb228f61ce16638d479,0x8fc6e9f155d23e9ba7c4d7399531d23e5b9cd194e36224bfc206728b0438acdd7139bae17375a4e6eb45f04588235b44046b8d011af843958b451ae104cb2349ae134994152c3534aa5c2a53282c58d27154ac54a54b28d2a9351a78414ac8d7091ae104cb194152c0b164c8295abcf47486d8e8d159d1a2,0x53b0cb2f34d79961b2696d95d1af1bb2e627386c2e96d55d1ae9bb2e527386a2e74b35d51a639ad4b754b94e6eb25e94c33945821c5614d1811ac046b283b2c46aa9389a5c2a532bae5d7945823d56228021f1602c5880b608d69205071d880b640b32099bae4d0945823d566258658e365e18769a7c6574,0x4cb54a059a546534a55046cb8d35c59a099bae4d0945823d5616d1952e5e587599526932a95cbcb0eab450043e2cc42cb3588b68ca970969986ae1529695962c92c59259662c96998b68ca52d2b314b6e2e8d78dd973139c36174b6b2e96d55e94c93a35cb746b8eeeb8087458a9b2f0c3b4d8ae12958a0d,0x562e134bb7161d66549a5c2145b0aa5a853a3a3a477171a8d91d7e6e3acfd971b5361d3a2b3a4753776e2c3a8ce17839c2e17385a4e4061626c3cd3230408f4580b1632ac51ac9326947134cc94a65c52f38d79972aeb975e51608f5587170dd7821d5664a958aa9baf043b2ca68c236e26d240a0e3b1a40,0x4608d668a35625076388d562e152945821e5692dc9d1a78b9c3707496b4e8d365ce1ac3a4b567469aae70d51c80c2a4c3080a3b0334c18b60d537d9b0c205ace58d83a53e974a7cae94f8dd1eacbb2dd8747aaaecb751d1ea9bb2dd27851d38c5b462c3b2a43ab13898aca2d70bb7161d5632a94e2a91c8b,0xb68c80c2e4c0cd306c99840559840617267216d18b2cc5a564061636294316d8a3486c994a2d0d1b3080a3b0364ce10d1b2951ae10c5b0b68cb2c90d53295c2a946b24334cc202ccc2030b1b0334cc202acc0cd33080b330316c19a6610147692de1d25ba3a4b727469b2e8d355d1a69be091ab114d185b,0x60810f8b2460c1c76234a2c10eab0132ca68c2da3046b2340b165076582d95361c61e8dd865945821e57034c50f3880c4081174d814d190185c98c1021f1648c1838ec29a302358a0ecb11c8d45a6528b043aacb0e35869ac16d619651608795c0d3143ce203102045d3782],0),(3,[16,26],[0x2960a15125866148624a1e19b08c30a30e08c229892c2b2c28d60a6b0c32d2365f7080c5a4c06899840519a5b70746bc2e70d81d2dac3a5b5474b6a4e8d725d1ae2ba35c376483122a172e283a8d2db13a35e17386c0e96d49d1ae8b9c35074b694e8d725ce1a43a5b46746b8ae70d11c80c284c60810e0b,0x182043a2c2030b130b28c5a4640615263040878580a16028594518310c53018a661014664ac109624258528b0438ac050b0c54208561e8982259491a03102042c360a2c10e2b40620408586d29f43a53e474a7c4e94f85d1eac3a3d54747aa4e8f545e05820c10b611658561615e0901850d86242b04b28c,0x182428edc587519018589b0f34c8c1023d1610b791651608715851608715e08a1044b60808972250894c20a16e5c50751a03102042c360c128a32030a93],0),(4,[16,26],[0x60804c10640805879a6460811e8b102e10640b97141d4680c40810b0d8b0833080a330b0ad024096198b48d97dc2031693179165160871590240945821c56e1061084375e08745808968110dc41b04a08c0c5044411044b108220a168172e283a8c80c284c60810e0b],0),(5,[16,26],[0x608300860810e0b],0),(6,[16,26],[0x608300860810e0b],18)]:=⟨oc,by decide+kernel⟩
lemma k6:KOk Bd Gd Pd [(0,[16,26,27],[0x0],1310720),(1,[16,26,27],[0x1925c73699085cb40b6740b5740b37642e7642d7642b7],0),(2,[16,26,27],[0x610da642172cc284146c369984c90d6d3a1c597325b0e64931d49a33994d0a461d4aa63a954a78a439b2ea5561cc968ba14cc785214e84d19cc922b986c436b8e87965cc96a3992467b520aec63324b0e64945cc9253992437349c33908b4b],0),(3,[16,26,27],[0xf1f98f1f94e42152cc284146c30d94eec3b264c753b92e653045662a2693210b1621051b436a8e86d49d0da8ba1ccc743994e87325e0b10c51492898e1a730ea661435a4e87345d0d653a1cc974358ce87315cc9623984c349a1ad87439a2e64b41d0d663a1aca74398ae64b11d0e61b992c2772190850b,0xc2420a3645186c6319a4e19c845a591fb],0),(4,[16,26,27],[0xc262180865314de43c102310cd270ce422d2c84280e613104c2609349c2140772190850b],0),(5,[16,26,27],[0x18404c4310850b],0),(6,[16,26,27],[0x42142cc4301],0),(7,[16,26,27],[0xc4301],20)]:=⟨od,by decide+kernel⟩
lemma k7:KOk Be Ge Pe [(0,[27],[0x0],0),(1,[27],[0x2a46e84a71d0a0d39921975261ae5160875594a993a9531732546e85269d0a4cba130e74261ae6482dca0ec52c64e85659d094739920d7b05b708c91a39922c732434e64859cc906bd871949dc3a96b2732552e84c71d0b0b39920d7b0cb32462e6488dcc90ab99207728b043cae0698a1e7101881022e9b,0x2030b93182043e2c1020a5b48c1838ec058b19232732462e53461c8b68c11aca4cd1d4a593992b176],0),(2,[27],[0x5e85c8d0b868d908cb1dcd4e3b9a8d73116d18b4ad0ac164754f072a1d92933a9b1a732530ea7259d4d85b9928975390ee18a639ab47410cb1dcd52bc8894c2a6ec9cc9583b242a740d4a1d4dd1b992a1753a2cea7439dcf063906714ea741dc344cc90a39921273240ae6480dcc2028cd879a6460811e8b,0xb90185898a9ac5d0d94ba1e15743c26e4a993119870cd30d588c4b862d9c90c3f0818b684c61d0944bd084a2d3086a99521c39c6a50e87a65c82398743d2ae87a4dd8bc4be0965e18769a1ba9763950e87a65d8bcc3a1e95743d26e41184bc285a2550985c8d8386c986a6112b845a208cc1c823187208a2,0xb23732542e87265d4a8c3a1c95752a28e86c2dcc944ba1b0773250ae40614363b7161d5676e2c3acca143768e87ac5cc9523aa41c754e32e5120c3a1b96743d26eedc587518c6ad1ce431c76352cea2a143d62e86e95cc9523aa719738a061d0f49ba1b8d7288e25d0dc3b961599230732442e64849cc901,0x58b4ac587686ac9d0e18b992b0762a42e86a69d0e0cb9929874352ce87055cc94a39018549818b60d1b7090d9c3a1e31742660ec5c85d0f0aba1e13761184354c8562330e19a643664e878c5cc9583b1721754734e87865cc98c3a1b16743c2ae64a51c324cc202ccc2cb316d18b4cc5a56872c5d4a983a1,0x162cc4046b29a30c51aa54ca5431c175cbaf28b047aacb2f0c3b4d6196e106c9b14b2f0c3b4f050d52ba1ca374352ae8724dd0d46ba930c743916ea5429cc944b945821c5680c40810b0d8406172660984055986101566721840559a1c9974392ae8724de142cab62342e406163660a141a366101476023,0xc10c1021f1648c1838ec28b043aac5346046b141d960b651608795c0d3143ce203102045d36],0),(3,[27],[0xb22ec9825d4ec1b96159603612d85191360a61e89d8619691b2fb84062d261018589818a60d133080a3343560e87285cc9503a1a98743528e86a49d0e44ba1c85743906ec90630522a172e283a8d0d513a1ca1732540e86a49d0e48b99290743514e87225cc9443a1a8674390ae64a11c80c284c60810e0b,0xcd8218a614896246112c2945821c56509420a16308c54208561e198f44c112ca48d0188102161b051608715a03102042c3686ca1d0d923a1b22743642e87261d0e4a3a1c92743922f02c106304c2028cc87085d0e08ba1c0974380ae4061436429826244a15825946188a58285449619852c144baea1753,0x4d879a6460811e8b085bc8b28b0438ac28b0438af0460a15d7010e8b312843c3350822580897820225c89423112984142dcb8a0ea340620408586c8fb078f9878f9478f927182043a2c2030b1329db0775d30eeba51d4ec8b90185498c1021e160c4142cebac1d930c3a9d92753b22e514630895820512ca,0xc121476e2c3a8c80c2c],0),(4,[27],[0x36818401ec20d60a65a46cbee1018b498bc93096f22ca2c10e2b0142c31810c4522540945821c56e10610b04609084085258622912886ebc10e8b304628102258840a17710650460122c44c231044112c3810a2b21044420a16c1010ae44042ba1010ac044b1110c0b97141d4708401c80c284c60810e0b,0x62f24d79165160871580a1686200f02148950251608715b841819042b188820896910112c0857020c8541541050b72e283a8d0188102161b304b08b0629984051982030a1b810314cc2028ce10803b241982851886312068c44a852c2b0b0af18803c0912853089462812ca31451261128c50a2940961996,0x60804016083204409018549808edc587519018589b0f34c8c1023d1],0),(5,[27],[0xc1009820c0161e699182047a2c72e283a8d0188102161b0c2028cc2c2b40b2fb84062d2620451608715b841842baf043a2c21b8832823045022172e283a8c80c284c60810e0b],0),(6,[27],[0x60810e0b],0)]:=⟨oe,by decide+kernel⟩
lemma k8:KOk Bf Gf Pf [(0,[28,29],[0x0],1310720),(1,[28,29],[0x47a74797476747578190410b9b66e766d766b76677],0),(2,[28,29],[0x2b61eb51eb49cc20878b14a3cd27cd17cca7cc97cc67cc578190410b1b],0),(3,[28,29],[0x4157c3d7a3d79398410f1629479e4f9e2f9d4f9d2f9ccf9caf0320821636478bc74bc72ba06146cebc3bae8f162f146e81859330bae8eeb93b258ec953c52bc51bb1014cf341f321f311f309cc20870b],0),(4,[28,29],[0x4118410f161030b2661043c581028b20a9610e56049608ad4a38190410b1b0b15a06146c5a8cb15a06164cc28a194c349b1014cf3c1f3a1f391f389cc20870b],0),(5,[28,29],[0x4101082a11a06144cc20870b],0),(6,[28,29],[0x20808c20870b],0),(7,[28,29],[0xc20870b01],20)]:=⟨of,by decide+kernel⟩
lemma k9:KOk Bg Gg Pg [(0,[30],[0x0],1572864),(1,[30],[0x23103b8c9b47244ae99c72432e996754672311eab4593a2c5d946ec9376073b035e016f0077],0),(2,[30],[0x1a95519c8c47aac0d7f08765a85668e48c1c9123ac71c90c3ac59d62ae4831d1883a8cc1149cb339365214ee69852e65899939a3073544e6e69c98b3931372414ee498ddc39b3073650e4c71c98d3931973524e4629dcc37d2b922472542ef9572428e4a45d61ae98c72412eb0774c339203798ab2311e2b,0x6a60439acc15473aa35e063037318f1881dc66098e33137d8378a20e3b0340d2538e4a39c946bf0c67418fcb],0),(3,[30],[0xd40c64620ea309425728c2912b91648a244ae499429144a15cc398ab2311e2b0e49c5987199c61b8534730ea37d0bbe45df12ef857581ba609c40b18c30a44aa16710e8b7d2392a077ca3929075863920875833ac15c9013920178a20e23],0),(4,[30],[0x1a818c02c803881608168c41d46028d413920170100412e5181a6200e12e4581a3114895c930148c09cd40b80b98731564623c560896210a44a728c30cce519088160816c618320d0145212250248542ce21d16027f8438ac1ae30c048817c2180a0d0142503fc21c967f08715d0b107d8078a20e23],0),(5,[30],[0xd40c60108164620ea30120331564623c560081221102cce21d160816e10d8838a20e23],0),(6,[30],[0x102c020098838a20e23],24)]:=⟨og,by decide+kernel⟩
lemma k10:KOk Bh Gh Ph [(0,[30,31],[0x0],2097152),(1,[30,31],[0x473a35d16e877],0),(2,[30,31],[0x238f1a78cbc59e2af137],0),(3,[30,31],[0x6a6a5843ab8190410b3606a6c40566e97290ee57288ee37284e610438b],0),(4,[30,31],[0x210a88d030a4f40e610438b],0),(5,[30,31],[0x21446818526610438b],0),(6,[30,31],[0x30821c581],0),(7,[30,31],[0x1],0),(8,[30,31],[0x0],32)]:=⟨oh,by decide+kernel⟩
def Bi:Z4w:=⟨5,2,110,[24,24,18,18,12],[7,11,23],[0x4688,0x4681],1⟩
def Gi:=[7,11,23,15,31]
def Pi:=mP Bi
def Bj:Z4w:=⟨6,2,114,[24,24,24,10,10,10],[7,57,58,60],[hx0,hx1,hx6,hx4,hx7,hx8,hx9,hx5,0x2b80a,0x2b811,hx14,0x2b842,0x23a42,0x23a50,0x23a11,0x23a0a,hx10,hx15,hx18,hx19,hx13,hx20,hx2,hx3,hx11,hx16,0x1d842,0x1d850,0x1d811,0x1d80a,0x1ca50,0x1ca42,hx17,hx12,0x1ca0a,0x1ca11],6⟩
def Gj:=[7,57,58,60,63,59,61,62]
def Pj:=mP Bj
def Bk:Z4w:=⟨6,1,48,[6,6,6,9,9,6],[7,15,23,56],[hx0,hx1,hx6,hx4,hx7,hx8,hx9,hx5,0x2b80a,0x2b811,hx14,0x2b842],4⟩
def Gk:=[7,15,23,56,63,31]
def Pk:=mP Bk
def Bm:Z4w:=⟨5,1,46,[11,7,7,7,7],[7,25],[0x4688,0x4650,0x14e0,0x1518,0x22e0,0x2318,0x3888,0x3850],3⟩
def Gm:=[7,25,31]
def Pm:=mP Bm
def Bn:Z4w:=⟨6,1,34,[6,6,4,4,4,4],[7,57,58],[hx0,hx1,hx9,hx5,hx10,hx15,hx2,hx3,hx11,hx16,hx17,hx12],4⟩
def Gn:=[7,57,58,63,59]
def Pn:=mP Bn
def Bo:Z4w:=⟨7,1,36,[5,5,5,4,4,4,4],[7,15,23,39,71],[0x1ac688,0x1ac681,0x1ac642,0x1ac650,0x1ac611,0x1ac60a,0x1ab881,0x1ab888,0x1ab80a,0x1ab811,0x1ab850,0x1ab842,0x1a3a42,0x1a3a50,0x1a3a11,0x1a3a0a,0x1a3a88,0x1a3a81,0x1a560a,0x1a5611,0x1a5650,0x1a5642,0x1a5681,0x1a5688,0x19d888,0x19d881,0x19d842,0x19d850,0x19d811,0x19d80a,0x19ca50,0x19ca42,0x19ca81,0x19ca88,0x19ca0a,0x19ca11,0xee888,0xee881,0xee842,0xee850,0xee811,0xee80a,0xecc50,0xecc42,0xecc81,0xecc88,0xecc0a,0xecc11,0xe5c88,0xe5c81,0xe5c42,0xe5c50,0xe5c11,0xe5c0a,0xe6a81,0xe6a88,0xe6a0a,0xe6a11,0xe6a50,0xe6a42,0xf580a,0xf5811,0xf5850,0xf5842,0xf5881,0xf5888,0xf4a42,0xf4a50,0xf4a11,0xf4a0a,0xf4a88,0xf4a81,0x11ea42,0x11ea50,0x11ea11,0x11ea0a,0x11ea88,0x11ea81,0x11dc50,0x11dc42,0x11dc81,0x11dc88,0x11dc0a,0x11dc11,0x133a81,0x133a88,0x133a0a,0x133a11,0x133a50,0x133a42,0x135688,0x135681,0x135642,0x135650,0x135611,0x13560a,0x12bc42,0x12bc50,0x12bc11,0x12bc0a,0x12bc88,0x12bc81,0x12e60a,0x12e611,0x12e650,0x12e642,0x12e681,0x12e688,0x15e881,0x15e888,0x15e80a,0x15e811,0x15e850,0x15e842,0x15cc88,0x15cc81,0x15cc42,0x15cc50,0x15cc11,0x15cc0a,0x174650,0x174642,0x174681,0x174688,0x17460a,0x174611,0x173842,0x173850,0x173811,0x17380a,0x173888,0x173881,0x163c0a,0x163c11,0x163c50,0x163c42,0x163c81,0x163c88,0x166642,0x166650,0x166611,0x16660a,0x166688,0x166681],8⟩
def Go:=[7,15,23,39,71,31,47,79,55,87,103,63,95,111,119,127]
def Po:=mP Bo
lemma b2:cB [(Bi,Gi),(Bj,Gj),(Bk,Gk),(Bm,Gm),(Bn,Gn),(Bo,Go)]=tt:=by decide+kernel
lemma oi:Ob Bi Gi:=gB b2 0
lemma oj:Ob Bj Gj:=gB b2 1
lemma ok:Ob Bk Gk:=gB b2 2
lemma om:Ob Bm Gm:=gB b2 3
lemma on:Ob Bn Gn:=gB b2 4
lemma oo:Ob Bo Go:=gB b2 5
lemma k11:KOk Bi Gi Pi [(32,[34,35],[0xc41c741069d0419731059cc4157],120),(33,[34,35],[0x7161515174831f1053e2097e40cfc815e04037],0),(66,[34,35],[0x713161512110c120d28850e44a222832598468a324844492a4a294524a92c462368b10a0834c648a494c6280d6233048432970c566118688358c1a4121e90047a4009e0b],0),(291,[34,35],[0x1c4c5854525908860924c4868b28b1a21618ac4221a2c8aca2d0a4b824428a122318a0491c2109131920904a88aa104b09292425091088ca49158963060b],0),(163,[34,35],[0x14509108e182c92621091317113459158a2d0a4b220904a88aa104b0928352425091088ca4915896305c1],6291456),(36,[34,35],[0xc585452590925c11290d16218ac92c430489842345892d15a122b22b51685259182046204d10268825450910498c5021131c20848825881921158904a88c8aa102096129252484a1221091490963060b],0),(37,[34,35],[0xc525a2b61515164221822122516457040824c52514138412212263060b],0),(38,[34,35],[0x4968acc585454590a08880905860b],0),(39,[34,35],[0x62c2a2a2c8443044244820451625842213060b],110),(165,[34,35],[0x2898944c412a2848c1608c178421221091134591588ad45a14964412095142096104a12211096305c1],60),(166,[34,35],[0x250910490d182c0982f0844a2268b092d15a8b4244314221123109212305c1],116)]:=⟨oi,by decide+kernel⟩
lemma k12:KOk Bj Gj Pj [(32,[34,35],[0x1d4b20c470e93941d1d272b2749cac5ce502c73940a5ca1c30f53394071ce501a769960c38d08122cb],60),(33,[34,35],[0x10217961020a1b70850e187a9b4cb061c68409165840c38408ba5810217171415838ca1b060561982508b30545c30ed30354e4c33079b4ea1e6d3a178aca45d430c8acec1f2d4a4719430c85cda730ed380a3b0c022ea2e18749eb80c7d7014f8c019f1802be3003730e348187081224b],0),(66,[34,35],[0x44a40d811140d29d10a4a38a148141b51148a458522b16620c1581a7119533156271010ac32c68a30a60a0d8a42853148b1863c1194301a30c6068c4315118539103509c63d0861da6a22c41b44b05658ac7188aa308a614a242951144141b91034a252149462586118c642d45c30e9330e348187081224b,0x2943861ea60c1b508bc1010acb1c62e4182c581ac5589c50ab91602159620c042b58e332562711738e15722f04508b1422f04c4314e85430c185338860ac0d194b0340d450291652c9064506d4ac230c60681aa214988ca981a069881a31296881b8a32c60c15c081aa938b242a51585440d589c59203515,0x4354c0cd32288a310c53850654a0c9c4334c0c8669a282a1836324162c08160d38810acc938a281b4a528306c0c1b45310c530340d290a5140d149886a98f421876991445188629c2e08a2e187699420c5c830d931720c306c0c86698306c1b2685508b1420cb1066a4e2a2e187698306c0cd31c4d24269c,0x32c314c5ccb0d9300810a0b0c9886298306c0c5350cbc10306d82a106060d81a18a60629e0a15422ca53880d29311c4628a18d485362388526218a281b6218d4e081a310a7061545c30ed30306c0d38866983a968a06914364c7102158162cc9629c51445a50306c8a0686c99886298d238948528a228a4c,0x708408286c10214163060a431823286c1815860669818361d4b610306c710c6938b258a50e187a985286a9b08304c320c9c4334d8a0c1b054e238b4834364c0c130334e04191c4334c710c1837823a86d32c1871a1024596060db84060d9897],0),(291,[34,35],[0x4462120c3181231180bc11844109014a4180bc1111943044c1180b910602c290a41405310148a9118848621a0481544291918430602cc2028c2988c080a02c23181222148520a02988054191244621a028344d442c159638c1462511064424050170405026050446110c642d45c30e9330e348187081224b,0x620280a220298e0822c1b10e20a02e0982220298d08609818a6088609c281905014314c05114b1388280a22b986029886098b9c6310c1b81508300911180b0340d050e20a31090240aa202e880a0284e280a09b10140551a900ac20a419630ca5848c05a0b1405a91118430a42905014c5a202e287105015,0x106c9889732c050144704304c0506298221826a116028421202e0852c111015830aa2e187698050c530314f04050d5301582608629d080a028629c288a31114440508e0823620ab04234208b0614304d430c05014314c028629e09821aa60280b8202b04314e841c41464828890b155202d281a62aa54a0a,0x4360c0ac33041020a1b50a46181020a1b194340a441983052180a8120461110c132040501704304c750cc1508c11d4341044710306c1aa62282a50140d08a0d080a06845040508d0e08609819a60d930304c19a7820c1b162a52870c3d4c320c9c4334c183683023886d32c1871a10245960280a4202e082,0x1020a1b708204282c19],0),(163,[34,35],[0x211c50602c05014240531015440902888c21e08ca18221c48a22948350409310c80aa204809180b41111843810602c2901444050144424090241544610e4409026118c2901a8b12209882941910b056d158829c4629109014050142605440902704052114e050446110c642d45c30e9330e348187081224b,0x620480a23821aa66080ac101444304c0d608446218a742062982218270a0609819a6228320a02888609a8618306c15069738c22310c5381508301230c60142405316480b4a0241544450194b09180b41110140511d10c4238a048122362288c40911a9184301452029442409310840509148880a0288e881,0x9a683023886d32c1871a10245960420d9311629732c304c08860981826a197820882382a2e18769818a60629e0818360c53a10c422028470411b130423421826a1860629818a7421486a9822c130684304c0c1385508b00a3088860980a1b2606a94e229414440d93310c530314c050144405310c13c1044,0x408286d8302b0c50a461832868148833060a43204052870c3d4c8104405c10c131d430306c1aa60669d0819a6a1c10306c50e187a9818360d930334f04750d040c1b06c9819a782060d808561],5701632),(36,[34,35],[0x218a7421c41405111880a11c1016c4c108d08609818270a008314c05088609c0a84183016048141c4142405315280aa20202809180b4111184300a29010040b821880b821202985822232860081230160c0588c0802208c05c880201452025101462130886016130c44642d45c30e9330e348187081224b,0x160982926a0408b65802044304c0c13c1022182742102141691860088187081174b18202328600c0a44198305218426080802a116008420d93112e65823825c8b0c131820260888030aa2e18769818a600e08021aa60080218a742008314e1431088238208b068411850c1350c30140c5360808021aa6608,0x2041436e100802102141600b4cb061c6840916580200b04650d8302b0c0],0),(37,[34,35],[0xe1008204282cd32c1871a10245960ca1b06056180200a85230c194340a44198305218420629808225c8b0c1300545c30ed300401a1045421826a18600a8405508609a1401815083002301600b04650d02008c85a4545c30e9330e348187081224b],0),(38,[34,35],[0x1c269960c38d08122cb0408505804194360c0ac30926a0408b65808a10148c30650d02910660c14860629805822e659722d82182600a8b861da60314c04a10c1350c3018a602508609a1502a1060c05802328691408642d45c30e9330e348187081224b],114),(165,[34,35],[0x4c028609e0982a2e18769818a60629d0822c101684304d430c0c5350822a10c1342a845818a60280a221826060982218a7820886a9818a602b04304e840c138500a182702a1060c058301622048c318658c32a60282405110602f04650c180b0c29c0830172204a118c642d45c30e9330e348187081224b,0xd32c1871a10245961030e1022e96608ca1b06056181021716c10304d24d408116cb02042d2d8260d0a461840c38408ba598232868148833060a430314c1880ac506c988909732c3],112)]:=⟨oj,by decide+kernel⟩
lemma k13:KOk Bk Gk Pk [(32,[2,34,35],[0x3a82b3ba82abba829bba8273ba826bc53210b2d9471ba3a8e372785371751c0d8ea381a9e14c259e14d55e14d4de14139d26026ba4c04b786721174b721326772132577213237],12),(33,[2,34,35],[0x61328686721174b0e9082c6ca10a5714c842cb6539872de31b83e31b43eb8323eb8313e31ac39085858ce21cd614afe0191e090313c120617c216187c50467c50457420a1b0d1b19268240c8ee38d49cd13b63707c73687d83617b63587b63517c704c7c704a7c70467d80457d8043786721164b],0),(66,[2,34,35],[0x8e30a749550a40dc1185f498642e8b4214ca88ad9e50614e9232248c2498512664714e03ca0c85d1429509e3ca0c29d2519e50642e8a322a149248ae30109dc6020b8888a228ae881a45b10349245cb4e00a7310c1b0c1ba122b4d40c29d268d38085e44814c29d3100247fb103117842d44d1386721164b,0x24642e8a14a8501c48642e8a14e08c8a9a36115853186b614685230a782ca188ac1508ca18ca3582b0640d15bb4e3117850a4291599185b59c642e8a148cca868d8a50b269c022ea22a36b2ce0147522d0b769c014e6264983a990d4c21a98704340dbace3217450d4453086c9671853a481a4922ca88aaa,0x922852320ce08a852c10a464290c8ad085219d11848a228c83343559c014e62228a42919b118435290a464290c8a833d61c014e63a824622f0a309144529114522ad2cc00a73199306cc1304a40d99036aa30c85d140d22ca88b7620014e622288a521a8a705a598014e623218b4a38031ca43114e081be7,0x16c19750e2b38089e4450b420a1b0c5b0c5b1d1d4b38e6316d1445c1114051826316f068445326c6c9864d8c5b30b0461a119064d53184364c6a98e8c9b18b61936316c662c38c45e14316c316e84c1062de0d08ccc83ac12283b4222a846419bb90311785935200c7314c35148528a14e085214a2b04642,0x8ba5982a18a642165b182ca18ea18a568416360e21e0814609ba8671cd32610e838e782ea19a361c8769cc3d4d4e61cb6338873582358ce21cd782ca18ea18a5736a4048e6899085858ce21e966710e6b185943184320cba862158750c42b9106419750c52b18435052b89750c30ba86320c8c219750c547,0xc21d409843108505902610e8c21e0884282d9432846c98d5330874610ee0c3390],0),(291,[2,34,35],[0xc08e2982a41710e64750c450c9e60f0c81d05c43950422459050a1090605c63a3520047304c115c4b811d43151c4b055d43191848a9524845811502a12a1e48640e820a9049232e218e25882e21c88e2588a41710f4c30009c442122812a2184849208a2812a30258896002384813222941718cd13210a0b,0x8151d4341710cc1b060db8870a1837320666d48c41dc4302ada460620ee2198370238960c8553295710cd1b0642a0c855051a0ac2a54413105664410a82a323181083421a8d39872982159943048b11432215a34650c215a35058431c4b05482e21c28e25864c238962a249144519114322afae78620ee21,0x1843a81328640b08630868416361a261a26e219085858215a052214ac20b886285a1050d88219064c534c832314e0415208c50a99054830260d83215409446264981a41064541549289a3620854151918a44a2689c33908b258415088232e21],0),(163,[2,34,35],[0x24146092414214503464e243207210541090840541951049332116049202a25046424909142112a08833208604054119151148262114840284a0c884521163070005c2409458100b0292049d44b0009c140589024950444a12c02a082119287901843a0c0805211c3870011c15064681351a730e53210b0b,0x598002e123086922268dc33908b25868d87acc320741054c882320c9a36e2182a209141915710cc1b0547acc3207410c8322ae218e21c89a26389619104c1369921903a082a6441950d9a48620f020a994aa288222b6a1c1883c08cb88638960c9053245710c54710cea1c88e259d43830c001711304c209,0x4322098362098a702054c1b18a732108641915036053251084c4c931248aa11248a32248648a2a10b0542108c8322a820c91419150342ab1e48610e83020a82a833222905026210a0544324c8219270261830c001711304c290c8322a209152a0c904542460acc95a483209249883209510a43206a0882f,0xca18215a0508286c750c198102a61530310781710c190aba8660d902650c193a86215bda900239826421416042b610c750c2a1d4310ac24750dcc40009c4440b420b1b082c1106841441508c882a110454c1b0642a0aa08c4c531],1966080),(36,[2,34,35],[0x651a854a8c4190ac09421a8d398729841610c20b8862158215b286055c43851c4b0a984450c85482e21c0815710e6420b8872a08968520a05c631024186721164b21058d94e61ca70a61084292d0aea188982638a6151c53191042a994a82a92208cb886388722025c433a8622409140941718cd13210a0b,0x1843420b1b1c430d1301210b0b042b32868148815710c50b420a1b0320285004c5305482314298361837320c8c1b18a7020c8550a81324c20808c49268d819010a8c522689c33908b25841710c320cba860c85415750cc1b060db8870a18373213282e2186420b88660dc08e2583215710cd1b032150150a,0x1843a650cc21a048101],0),(37,[2,34,35],[0x1d309082c6cca1a04c2190202009085858c21a04285a1050d84218a60220983600c08426498d1b004d1386721164b004ea18ea19836850c1b810042a4140d3987298e219a3605482e219d431c43812044481718cc1300441710ce31844d13210a0b],0),(38,[2,34,35],[0x3286610d02408086899c43210b0b042b40850b420a1b00460d8c5342860dc08026498d1386721164b032e218e2198361836ea1a140120d398729860da9cc394e0420b886750d021138c66098e21844d13210a0b],48),(165,[2,34,35],[0x18a61837024099270ce422c96105c430c832ea18e21854ea198360c8e219837020c854214140d398729841610d0238868110ac10ad9432044481618cc13210a0b04430861211102c411042409116710e4b420b1b1c431a36191c43306c710cd131c4338961548844c131042a028c8c52211a730e53210b0b,0x1943042b420a1b108286e0419104c1b],30)]:=⟨ok,by decide+kernel⟩
lemma k14:KOk Bm Gm Pm [(32,[3,34,35],[0x643c7643a764367642e7],393216),(33,[3,34,35],[0x530773219bb2e1e5418bca8297c8267ec2574c871b420b879510a8f082c9e1058bc202c784052f08099e1012bc20237508753],0),(66,[3,34,35],[0x990e366143305274c6a10ea626438d94c6a10ea614c2c4b0b25127153906f8a65149c631868cd456a22a9849e9858382a40c7043712e28760df10e10123c202174c8713],0),(291,[3,34,35],[0x52199321c6ca635087530281714cc53612211c4b02a8a4e318a2b0a05a6351086cc215140a52626438d82c1a23c434c8713],0),(163,[3,34,35],[0xc2866625a6438d94c6a2a10ea61562592714c938c606b0d19a8acc2934c6a232de41f10c192823829c8174c8713],786432),(36,[3,34,35],[0x1486630a1981312d321c6c53181508753314c0ce1150a05c5302308100e299108e258250a920718c3085a3351581698d440ac28a29302c1a23c434c8713],0),(37,[3,34,35],[0x5219809421d4c02c53009163194c60541a23c434c8713],0),(38,[3,34,35],[0xa433012843a982204a23c434c8713],0),(39,[3,34,35],[0x1430a198502508753008048b18ca23c434c8713],36),(165,[3,34,35],[0xc286650875330b14cc5322c6302a98c29341a23c434c8713],12),(166,[3,34,35],[0x1850cc22511e21a6438994c605a23508753],24)]:=⟨om,by decide+kernel⟩
lemma k15:KOk Bn Gn Pn [(32,[1,2,3,4,34],[0x420a5b4b0499e5824af0a12379608b3cb0455e14226ee810e763085baa1188b35a9081f1c084d70ec0f4740793a03c5d81d8e80ea74074bb0371d01b4e80d97],4),(33,[1,2,3,4,34],[0x709508c459ad30a822d9611887a5c20571930a822d96840ae352193c38690815a6840acb0d63840ae340812ba04055d0201af08106784081b8856118873589636ba4c1dbe458e78c2a73c614bb4f871cdb034e6d8197250f198cf8cc57b561bc20561f0e47e1c4fc385f86a3f0d27e1a2fc331f8653f0c97,0x0],0),(66,[1,2,3,4,34],[0x889609161a32215c88a1190343322001038512e6322488c9821a2a1284b22d1c48051749244082e918e0417489729042b0c603c900a4e245aa7940191e2450b628c258c1a91034329110ac15488a16bf230759f143cda99039a0a0a3a74049d3a022e654018e91c0a748e04bb106841487c311f8613f0c17,0x31c01448514e2258245868c88578255880149c48b0126c231c0a3e514e22581a14bc8960149c48bc132a300a2e92024de4638126f225ca4612486800c2408c70081a2453889609161a3206a238800a2e92068ce0885742091601c9a4638126e229c44b12400e2448c700712244b9480081cc8c7005127453,0xa488a0312e8c70189744b9482c584c6e8300a4e245892020f28c70149a45388960083da31c041ed14e2258028fc8c70189f4538896c2001448514e4ac20107f4538083fa25cc728200a4e245868c885600c4ba31c072e114e225852e22580527122c0189d46380c4ea25ca4610d095f38800a2e920020702,0x4924330a149244919428a90a490c8322b120681b0a428126ca25ca4250a616240d0a40d89142d242944924642944924491915c1a10349285448928544d0892854490a8924d0e081259a29c0824912e62ce21d1649880149c48b1240624918e039668a7112c0107544b9880083e225cc515843425aa8c028b,0x92b080107b45392b086a48c81a0189644b9480149a45392b080107b45392b086a48524919151242b0a0c856242c495841a0189444b948029328a7112c0107b45388961a921492464292486614290c9250a2a42924320c8ac4e086892b0834049aa897290d161020d8453889600c4d229c44b0d490a492321,0x388960d00b46114e2258370684c15081469229c0a34912e620106aa29c941a068c81a049ac8a701c9444b9881a190146da29c0826512e63820686406a3c8a7028bb44b9883231c1a110ad8c30d15892b08340d0189044b94868b080a49a29c44b0b168b08083aa29c44b0d491841a0189444b9480149a453,0xe22586e09820e9a8a7074d44b988738ca4738c153d14e4a1ce3291ce30107045392868738c0524914e2258738c041cd14e225868c8638c6431c6321a031208a7053f44b988029268a7250681a3201c9545380c3a225cc70442b1a2b1020d0453889600c49229c44b0d162041a68a7112c1b821ce302d1645,0xa15138260982e49d0ddc80129cc5cc3032c2aa8c026394853051805174942a24190a455872405174942a27044979c90131ca50a892149288e24026394863138342065cc379a80131ca485c30e028bb92722e51aa1188b258c718e7182a5a29c44b18e3344e71821ea29c44b0d0e7182a7229c44b0041c514,0x34a429190a42919150343215c10541ce319150d60fd30129cc4290aa14850ae0983561c04a731722c20ac48582a8942e0983559804a731724c451481a92248c89219151142a49850549245890a492852146419428a9415c4e08e458a4320c8a8e458a43215c10642a89428485882bc1724e844524a151224,0xe12a1188b35a615045b2d0815c64205718690815c64205718690815c60d1910ac39c6338876598e31910ac18e31910ac3410ad22c51a1053192260a4494324491350c42b1458208574228c890c7081586068638c],131072),(291,[1,2,3,4,34],[0x1c8b1104424091505412e718221a3926093181720c411480d14b4444054921084c21c3480088e0a42d141090641362029240d028480b63820644405c1045821342088261402908a421099101a0a290140682864845222014840531015142604a02c09064a1c3804170911014050991a10e25ca354231164b,0xa020b848130a22e6198202d08c4215088b44058902615c9300a19211842409c1044134202a850a9204b0625ce30658260d09422a02b042a02d08480a09713045206d5c80105c240d04d08880a19608334260a8424c4068280b422a7940111c14274431048441b0a0ab050a028c426c405088c56312015c93,0x118c3d1182a1102d8e309431886221580d60bab1c0109c40b042ba111042bd1042bb101a2210ae05883042b26e40088e12a168ac440b012205e08205c880d11085702c51a1052182a0a8481382049880a3104b9163917a20492514041709210170409722c4405508541550848130a0c824c405d10654292c,0xe1068442158222058205c205718c518e5188168414c608561148896301a09102c863840ac3042b1886210ad8c30e61c5880109c40b1],0),(163,[1,2,3,4,34],[0x42ba148b146149250a891250a89a11251224d0e089322ce21d1606442b0358d14541a06b1a28a834644506a4804b1a4891632215804b1a489163221586949188725a44314c50b3052260a4444b0a432c1488856248a51228592860856035c8b0c8a4214dc9354231164b81620d08290c1d3504e0e9a81711,0x42a0c855c93430a531ca30c8a451724d0c298c05d0a904e205c0b10684148618a3420a631c8b392648b946a84622c96050b218c854490a89514891887258215844b0c582916710e8b250e102b0c0a49439c631c6522258c88560738ca49439c66898e329112c6442b0d042bc1042b608215d0b1860856c10,0xc8aa151291314cd10692452852146419428aa2485448642a448642a629e0a44d430358c55441a06b18aa8834649200d630d191551492942a2419149250a89c11250a29448922944e0d08528991318c0e56904e2058290853724d508c4592c1a10ac6710e8b1c93112c290c88568414c6420571834321506,0x149250a891251382609c93a131730c2924a151242a26848950e0a45ca3020d04138816124524621c960d488329110ac91142c1488960d60a4489488a1642b05222159286089614829112c1a322158215e08225982215d08215c891244c88a164318e2358c1a19064550a8948962588686b18e2358c352432,0x24190ae0d0942c1512151244d09438262916710e8b1ce31ce30d1ce3344e718694839c61a52320e7186948645429068642b8206839c639c61a322a52c1310550a0ae08c5c8b21512c118b926228a4320c8a8321549054930a24c4852850c8549289c10642a428642ae4582a0c855c8bc10550a8960b92742,0x8648b14650b0522ce21d168414c60a82a722d0c292c153916724d0c294c190a82a854498960aa15126298520a8a5c8b02ae45e090a8960b9266a1c20561982722ce49912c150b98618a691244d43728d0c298c152d04e205982310c582215982a118982a110ad8c328522c518321542a24850aa2704850aa,0x724d508c4592c39268614962158892310e4b0c4b10ac60b388745982215928708158631],262144),(36,[1,2,3,4,34],[0x939862202845c9301202e7180a04a4405ca354231164b0058210aca10856c618c61989820816c61888205e8809102d8e3005420284854620488b38874582058024a180262028c442b042b0641220588803a20817620084450b012205820588842b81620c0108560c82542205a44102e0411142d8a3420a43,0xe106842b08840b0440401840ae3040b00a10531802250c220816431c2056183101391618825cc3007440],0),(37,[1,2,3,4,34],[0x8561100840b00508298c11840ac3004e61844e51aa1188b258c61844016710e8b0050211620c102d8a3420a43],0),(38,[1,2,3,4,34],[0x10ac22102c0208168414c600845508c4592c102c230815861c8b102cc61844102c22c4198a3420a43],34),(165,[1,2,3,4,34],[0x10ac10ae102b0c840ac311024e619c8b1c8b113926a84622c9602440b60842b284215b1866098c31102422ce21d16088205928610ac285a05883420a43304c6198a3012205a0588302522816710e8b420a63],40)]:=⟨on,by decide+kernel⟩
lemma k16:KOk Bo Go Po [(32,[1,4,5],[0x1292242524b7363681009772c622dc1c612da1ca0723940e27281c2e2096b0e50351ca0693940d1728198e50329ca064b84a023384a022b84a021b88259c3940b4728164e502c5ca0563940aa728152e12804ce12804ae128046e50271ca04d394099709401670940157094013711400e711400d711400b7,0x60342d9649c15c749c15971b180d100317699cc09e39cc09d393],118),(33,[1,4,5],[0x8ae402a8ed382a2e2ca4c165861d0584dc356704b1d6704a5dfe09e1ec281c0c7aa76c11c7b608d39918981312923031308d0c8c0607068100a332d0e6c0e853507419a43e8311f4184fa0c1732998398cca1f4148fa0a27d050b90cc61f4128fa0927d048be8231f4114fa08970d400670d400570d40037,0x7841d1224360770c5c54581c182010140c08045c5b1fde01c3a960a07030e2d80d899e09980e16de1ec0c3a360b06b0b2c30b28b0b0b305ad402a2e2ca8c169c22c8ac169],0),(36,[1,4,5],[0x8d62e148b0117b206d62e14c300bc10228085d41ad3d8560c0c0980102200c1bd830750c7b286045ecc1809c08300b00208801060c68084106486064a6f640c108630088561a220248521a0a10843108c38080110863a086242801c6384c1bd830742da1ac505c0c5926565854181c1a100c0e04025c4b,0x11224360770c009812300c060b30c7f78070ea19918981312923031308d0c8c0607068100a332c66120a419506030710c0804141b104f60e1d433330272461641b180d10032e6981008502c02969e02b0668140a4580500a030a6f040da050290600c0d901018537820603626d0281483],0),(37,[1,4,5],[0x4890d81dc31812300c060b30c54180c1c431a1ac505c0c592668140a4195961506070684030381009712c0102010506c1ec81b58b8520ca8b43440281c0c78a60402140b],36)]:=⟨oo,by decide+kernel⟩
def KT:=C Bo 2 [1,4,5] 2
def S4:=(O 1 4 [0,21] (O 2 4 [0,21] (O 4 4 [0,21] (N 9 [1,2,7,6,8,13,14,12,42,44,43] (O 10 5 [0,6,15] (O 12 5 [0,6,15] (N 18 [3,23,20,107,104] (J 0) (N 17 [20,104] (N 42 [3,7,10,123,120,130,127] (J 1) (J 2)) (J 3))))) (J 4)))))
abbrev t4:=LC KT Go Po S4 0 4
lemma c4:t4 0 5:=Tc oo [[0x84e8920505e2218406d049960511d1240a0bc2406a82a170406a82c100d4248461e06a201a6101b41286014474080282f09384034c3810c203682a101a0368284b04e22840698406c149120505e1203461c080d28415a080d60d0284ea120505e22d121486e40248ee40244f06f60c1d0b69c114769c1117,0x618843980d98a32034338101a60a0a037025501ac08c260e448284216f0230982b114205b05608a10c9324a8c10720ce041a0346a03662034aa0362a03562034c10a80dc8d04312860c42de04548354c41ac131186034c455819504c1184c41580d1856203461c8a04014178480d2846160406d04c154d02,0xd80d08439b0406864846180d210d61085ba8962108c30a80d284853180d284847184230d6300a0bc4682504a0a840680d6082a42b0c068c24298c0698250908e300d21187510a121186b14ca0288e9940505e120640cc140c8540af040ae24054c20560a057820d3820680d828320ab04211960b41503484,0xb01a50908c3a881502a6102a0d0c31101b5101a5501a71214961085b10a63108e34468a03406a8450864d12c55101a30c44852984238c210b7110c24298d5186806b0450865514c40c854b11c4d164450c44856184216c0690ac301a4298c0cb8254962065c10682a4230c5501a60908e34ca0288f050842,0xc06c192b419330c30658c06b0203583060ac7130206c19a31212218691a08d070c9160448b04069832101ac0a42610c34501a30f04068c329032909c448d84305a0619060ad234188c1bd830750c210b61085b0a821186152c41a03406b048471806908c3d08a118485318421cc4238e922844230e221085,0xa9101b61a880d01ac11821901bc10c260a440ae4430cc406d461a30454ac2614a430854b102a055820d265511c430864608c29101a48b47020b416e04548a9c0984b10c2156440a815c0834068e406c6406a6406d44c0b440698230a4460891308640680dc09c6424185b20c2de040ec1b0b20cc1835061c,0xa10c21501560b420d02a06f04035838501a035834501a30cc40680d30c64ba64881e058c083ac9100878080a984714c525705a10c80d01ac101a034c50c985254c5c1685220346101ac102a19c89c105a150341924712074d12c47106a0d06415246c22c40ed84152c20d1c419246521840d01a1502a1901,0x163d91b3d94b0c2f668d8968438962d0bd98b1eca5e141c8e21843294a4ad0ac2f670c7b2367b2a6309ece1e047b2363d91bc09ece1f04181580c1cc6101a0c54c061971101a0cc2c0c8c20c98c068c28883253222062a60619630e04060d60641815b03610880d80dc080d889c230833437b246314b11c5,0x360dec183ac60e5610360dec183aa603406984e15860dec183a563d91b3d95301af670cf658c19a1906f60c1d2b41bd830754c06c1bd830758f023d92b3d95301af670cf646c06bd9a3066],[0x4b2504c1184320640cb040c983050351ec99ca5820cd041a034c118722034c118662034c11856221406d040680d90b04e22146106a0d066a2184190320d01b4901a718a8610640c83406d2406964069c52a03406a8482a14710325081b4101a9080d82832c10a81434c0a0b661051630c2056421406da381,0x9a0a623882a85068d630cd670c90b05c11ac61983415880d01aa101b4101a035426101a03642c1c88a103406d040680d60c8406d2442cc5a2358d3358e32420b432c11ac69819608546b15660815428352b0503a214c203b0502d1a60a85a0816a140b50a34c14550e435608618686902d82a16920b40eb0,0x80d48782034a101b2101a15a090460c06a1693911ac698196b3863589b032d634cd62ad42358d3a8921285ac7194119234c84908640cd25514c4716096105a0cd050d13549454550d531032715450a358d3359c3304a12142a358ab1ac55a846b16615142d638c066820ab598b035908710c82ac12c20d41,0x562186620352168819036a201b418a8190352a03406b0442d042b8502a0556106a62035a20370a03406a84068540a86682034a1a880d01b4101a1501a0ac85514c582074b103560834710640c8578210ac300d30c84210b6908540d41a0c82b4101b3145406d450b0d01a0a80d6080d054c22146190885b0,0x234d0471428c118432064c12842a0540aa15c102a05682c1032710680d304615880d01b4100da0b052a0540ad040d68c84308610a81521682485410680d504e20b434d049083406854712c58218406b04b203541184c10c861284c1a880d4854168e240e8321a419a08aa0646a064e2066924840cd041a18,0x80ab05a2066a20568a066920540ab06c20540ab064a06415e08346086142861068610c8e20642ba105a4282a1841aa880d6880d388c1184332903a1a5420b46903ba1608e21c5a11a50a0b4a10a815214c10680d184c10c80d01ac14a86130562034a168d04074c205a615082d4a4694c582074e21840e99,0x2d2c471345615451505a9505a92962688e2b0a14308691c582b086442b489010784f1810f0105a3881d42833c1032065820650b490d2065421c41960a92066c22164ae08540550a064156081598],[0x282d06543050339100c2da540e8390d42d828d218432c88e38107486f0f6061d1b015827b070ea581da180e92d0503b437b216413d838752f020647103215705a102b6102b896140ac940c8196082b41032066820ae041a8320d419c08e20ac846280e1ad82260ab2606b42b223882b05827b070ea18181b,0x50839506838710f02d060cc061c15191643907286039430c8194c8a28320a0626c0e702134320634c388610c8185b07486f042c7b21618430c8460c14168c2192082d82d20835a082dc1608858334100c69e4609ec1c3a8606c4c039430cac2074960641da180e16e0a038730386bc0819032852820ca844,0x2580e92c0c698070e619018d3c081c8b2184320e50c0634e0a065a158505033810a07030e2d8141670505061864070e602061c80e38a3081cc18508386838510cc3816081230e407782062851880e40c2881c8185083838430a187203bc1031628c4072461440e48c2841c1c218741c61480e38c2881c918,0x185b076860503818716f020e40626c0616c0eb0a03136030b7410e2b0a820634c2c872c29e09980c4d80c2d80c69c8430a423fc1018716e821901430e1070708678207217f3060ed05190e4991642c8640626c0616c90818d3c0bfbc038750c0d070b],[0x3ac530a52a887298e040eb0250c346094230b44c0982509c43081dc081d485829524230943911c2384c250b0218582150156082d0570205642055420540aa84c2191421a4c2187021842a18432b102a054c2057420540ac85420b8ab0320a8b8c3c0815185a2184a138815185620d17506bab4f0f6062d93,0x6982b10c2d10c25082d908640c98295242509821502a30e445d4580b8ab508150c8b8c302a308baa305c55f04054a11718721032064c22ea4c0a8159081548542688ba8b01560921508150c8e2689622eb0c1a07434b043482d1a5826103b310c3850c23903aa28d262b0a94aa298a840e8695082d2a4690,0x21a4612845d518c118a34a85914c5511c4d12c45d618c10baa305c4dc84508bac30a82e26c0b89b50b822e30d2102a2eb0c3203aa103ad098a612c48d0c3910c239142284c21502a509c4508c219175260b89b0b8d302a2eb0c0a81550b4228432c88b8c38682d242a10d21c46990b0434cc434c5450c341,0x62ae1af650c38b42068610c80db09a15842a0370a0368a7040d0641590974c9103ac9101079522010f0101a0ac347b2a60682a7b2c7417b3063d94b01af670c308320a815068e2f650ca081a03432389620abd983c0b4358a0b818b26c171560e45c7185c4da520b8c3e083a0b89b8c8c103a2e34c2e38e4,0x5c0c39a6191e0c5b0a16439c09e09980c2d8323d933031a648581065e1ec0c3aa628a0d69e02b0605c59ad3d8570c1718617586b4f6158b1ac5c2967c105c71a42175866045d41ad3d8560c0c0d8f670c151eca58347b257c101ab0bd91b1eca5e140c82a0541ae080db080da280d94819032610540d908d,0x242f650da1ac505c0c59a634358a0b818b34f8203a282e061cd35a780ac58f0f6061d5368140a598320185b3c1330640e83290bc3d818754eac3021da05029060185b03a030b628b0c030b628a2c171860694c588e2e0b42b0a42282e061cd300c2d850],[0x32471644d1308a1187122841c9846a28434b42615882e26c171372114a3495298992688b8c306a075422e38f02305211826106a30a84b10c981484a11842a02b21242a10159081905543813420c8391a419c082a6102ac08d40a815308150cac41a2ea0d6d69e9ec045b165c54581c182010140c08045c5b,0x90864171364845c618541754603215171c6e082e26c2e32e420d14207471308610c82a0541a2ea2c1719628415171870d06ad0a62688e2c8962a88356841a284328a8190a8bac301d308c19081d5852150861c88a118432064614842a02a6102b2102a90a841a2ea4c329a1908650cb215081d4683968531,0x39972103a308b0b80872ac17136028ac012560119601156010d62cb0c01496165860d0585c0439970d05c4d80d4845c6185d618082b1e9ec043a963d3d808752f02010d6068a1185e9ec043a563d91b3d943010562ca0d69e82b060b8b303a2e38c2e2ac0e8b89b0c22ea8d1505c4d85c6585c71c84171c6,0x8f658e4304f60e1d43030366462604c4a48c0c4c2343230181c1a04028ccb00292d69e82b860682c2e021ccb0b2c35a7a0ad18f4f6021d4b6a160a4d880b248103aa06043bd1436a160a418f652c06bd9c301a034c290bd9436a6b161701165587b286d62e14c324217586b4f615c30105600a4b0585c04,0x3c04908696090452e8206c4c031a61d7f78070ea18fef00e1d4303b430c82c38c2cb0c161872105961b04349822c92c60f04909822ca2c609422ca8c1d0c290921608b2932421a7021a434c85821a4e29896218722688b2830c260a42a0865fe09e1ec281c0c7aa602b04f60e1d4b032b080634c2ac0815a,0x4890d81dc31506030710cc0819a181d3047e30624a0df9e0183a866048c030182cc302010506c3d1c3031a6c281da1b023140634d817f78070ea5904f60e1d4b03626315610e20634dc1382031a72101c21a42c118a48582031a7411823064231490b0682031a78100c69d628103d20704]]
theorem Z2Q:FBO KT 0 4:=Tz oo c4
def KU:=C Bo 3 [1,4,5] 9
def S5:=(N 1 [1,2] (J 0) (J 1))
abbrev t5:=LC KU Go Po S5 0 6
lemma c5:t5 0 2:=Tc oo [[0x42817b26622481085ec918f640c62205ecb1e047b28648410c05097b2063d903388f640ca2205ecd18f640c62c89017b246205ecb1e847b226485eca186242410c0521144317b2063d9030c8f650f2240480a05ec99881405ecb183108501485ec91e25ac5c2906545a1a20140e063c53b981047b981027,0x85ec898317b2879105c498320845c5185d5182e24c62086820c40a8860a06431b08190c69206431949410c64a0c5418c8510c61a18449244510c60206501086220841924451444319082148491145110c6120852140662f640c7b28608410c0410c85ec818f640ce23d9030c82101b0103321145ec89901,0x7127210422ea8c171260c45c61c241712731092288622eb0c248a2188ba931eca18617b226188217b246288ba835a7b0ac18f670c10862f642c0c8a218a82f660c0644282a8288bd92306282a22a0bd963032289222446282a8288a12f644c448322892218a820860a0c6120c6429883188bd9431ec91842,0x1c3aa60ca09ec1c3ac606c4da0502906541a0e1c431ac5c29465a7b0ac582e28d69ec2b863d92303284bd9136447b227a1625ac5c2926358b8528f823d90b03218bd9130a218a42f650c7b287c11eca1e24189120c54284a42f648c7b2867b247a11ec899eca1e45ac5c29861422e24c108b8a305c49c441,0x5d5a787b0316c98140e061c5b03b4300c0de0406a02c0bfc13c3d8503818f54ca0832018d3067020185b01953018d3066420341c28e6810191b0189b0185b0199301953018d30660220541605214040c0d80606d818c901604190352620440c0480e040d0d92101b010640d29bfbc038750c0768620609ec,0x6148609ec1c3a8666604e48c2c836301a20065cd30282e061c9b1e1ec0c3aa628a0d69e02b060bac30ba83],[0x9ac4408824218c210a6550824238c2118651808809086308429c4480b02036824052240491e080d404a2405a24044188841c89084300d21487518686242801c6310203406c05acc18816b14635883a8932035acd18d620d226242801c4384c1bd830742da1ac505c0c5926565854181c1a100c0e04025c4b,0x92180c14c148306301815c440c98e1af640c2242083444a4406944d121086114852584214e2210863a484214ea2034c10c48561806a0431214a6034069043124420c447114485219111444218e8a108530824218c4238c5182840908530551108a4218c51a084210c60908c308a204824214c210a7510842,0x2b20dec183a5781019018159041821bd9231ec8d9ec918330b052188a248a420a7020a7220a712606c20a6a20a58194861604510c6820a461106220a5216061b06f60c1d4301829b02066860a410904183180c14e22104193180c14c0c18e020302b03063b080d08b010c419298290524103491444510c41,0xb0297b28601a217b216c880d7b2c606c4c1417030e6980616d05064514182822c282e061c9b064282e061cd38082e38d010ba83030a6085010a5050c4505c0c3d260b8e30bac34842ea0d01030360ba8305c69c04190c40d2982e34c068522ea0c808baa34c40d0dbc10368140a41906f60c1d531ec8d830,0x746c7b21606c4da050291634358a0b818b26c1417030e4d85141ad3c0560c322d3d8564cb4f6158b24217506b4f615830303601853052f0f6061d93062f0f6061d531e1ec0c3aa6191e1ec0c3aa6030a78100c2da424840c2980d4980d29bc10b1eca1905485ec85b42c08181b01aa0a4282b02f0f6061d1,0xb60a0b818726c282e061cd30c0e0d08060702012325bc10366120a419506030710c0585c0439561650704f40c1d433024641810166182010506c686b1417031669969e02b16686b141703164d97569e1ec0c5b260a0b818726c030a628a0c282e061e935a780ac18f0f6061d53604030a6f042c82bc3d818,0x770c6462604c4a48c0c4c2343230181c1a04028ccb1fa01fde5e9e020181c0804ba9609098a01008ba2c24a0df9e0183a866048c030182cc3169e82b065c54581c182010140c08045c5b199a1a84850581008893609098a01008ba2d69e02b063f403fbcbd3c04030381009752d810383040202818100888,0x1224360]]
theorem Z2R:FBO KU 0 6:=Tz oo c5
def X5:=C Bo 3 [1,4,5] 5
def S6:=(N 9 [1,2,7,6,8,13,14,12,42,44,43] (N 18 [3,23,20,107,104] (N 40 [6,123,131] (J 0) (J 1)) (J 2)) (J 3))
abbrev t6:=LC X5 Go Po S6 0 33
lemma c6:t6 0 4:=Tc oo [[0x12148d100102728280405c2271808d622c85282016428c91a2cb0a204810270290a0ac05156b10635883588d630c323588ba89016b34621532504723588350a0204e9920405c2201411405ac7181140541485116b1463588b00a90a02d620c6b10741488cc20c0490280b335828722c666b050e45d046309,0x5514c4d12c511244b140409d628080b84410944048c23102271a08091840d314049120a90420a340a81520a322c98a29083910133101220c4404882b1082609540498230864108c35108214a64208523900a04882910c220b880102758a0202e1100a60812308823100a0886262b44028423086201452510,0x34068121cb2298962889220c862689c400813a6381017088e228c841840101704904b11c415065112443104451b081114431524d10130500a710234500b8901202e040480bc101208c84088a361a8804a42414c4d12c47106491144048c5510831101aa140409d11c080b8465200a29214c5064151543964,0x340813a038101708809c88092a809688093880928c1401502c08624ca0204e80e0405c22688e20a4a2017234501a048c202482c4a8a68b82288e331012c098202482024c2c49a2024a20268a01782024e31102218805045020471204632204e20478220505288410c411c08091072202441988091046188c,0x8231062d1013a10138501a04c94108531905230a05010273470202e111223ca0204e60e0405c228ca2ac2a4ad09c4030a6054e28082398401017030268ab0a92b425100a428a208863490092088a1882228e04029222886208f040488262a922a9a238b8228e440290a2886208923890126091202462c496,0xc82a41012910],[0x750a0202e1101220ac404b44029027100a08954408c251808089051515408922189630101280b4440a027101210e44048833101282b028094402442208c311042189c3518686299061c6300ac086258b0204ea120405c225884188805204a2016a203722045a204532014414898a6418710e1306f60c1d0b,0x34a2015634901208862388a381042188e270b42c0d44024422882218f0440b021882228d8404822288625882188aa298e2404822c08094896210622c8805a8ca4208f1c080b824b1a0409d01c080b84404d4404b44049c4550125182809444910c4111468a024293840a83404a44208c404d4420b070102,0x461064c60302b030530440c58c0c18e020440c0ac0c18ec2030631c56101815c440c98e1a44491144310441929bd9030b1c080b8247120409cc1c080b84410b44025027104391083310d24082398401017030268ab229894404823a101a048a385012188a325084218c22088b110f2408139c40101708a22,0xd98b022f654c0a822f670c3890204e6900405c22f668c7b38608e04208a2b09c288b02f648c7b246209ece1e4418218093d9c3082f648c02bd9a3066161638101704822025ec918e27b3460cd0c40a0204e8140405c22c0819858e2024192580904419a1804830438880690461495c168581444183180910,0x1480411d270409c180580c0af023d94b3d9633],[0x82e38c1503431046020614c9080503429175060345c5985c7182e26c327100204ec180405c220b89b8c82e34c720145d5182ea0c629881a5305c69a420b89b1881114805034110a431175060b88b034110a42e38c150c602015210c4150a45d5182ea0c09988282e061c9b018538a81a1b78206d0281483,0x5044505c0c39a70105c5585c7182a175861750690a0a0b8d3808181b00a0aac234880b0081381411808112680558805024119080508722064090541182805086a201409404e20150148472045014147102321068a0b8187a4c175260885d4585c7186217586175460b8e3829810c411175060b89b0c4119,0x5034f654c04822f642c08bd91b00a14a0a0c822f650c7b2867b216c08c47b2167b2879100ac0a8290bd963036264840c8a0b818734c8280cc9832032a6031a628a0c17116175861750690b080104750c0202e0604c340a0530cd02814b3019930283258700411d21401017030261c80c2d8051417030e4d8,0x604c4490202e09044191c4028c55103526f050c05452a2a4ab0a82e0a920242990811d08090a60a0470a3d9a38681504702f0f6061d1b02218a4ab0962e0809046820241182811c289180411ce20080b82662205010273880202e118688100405c1208c8418823a103208ca40a81a1882381787b030ea980,0x4842ea0c2eb0ce2808239840101703026015210348140409d028080b84402e4402d44029c4028123100b311417030f49ad3c0560c0185b0181b7830601af660da16040c298f64ccf642d8570581684e28082398401017030260185b4840634c0aa420606cc0a829081853062c0a8290b08010474080202e0,0x1a1ac505c0c5936358b8522d270411d060405c0c0987b2160614c06a42f0f6061d531eca19ecb19c5010475181017030263d90b0443103626d02814c30505c0c39360bac3030a60181b01853145060b88b034360b88b0ba83034a60b88b],[0x1b0041582010586df9e0183a860185b604a0a42a1c0411d230080b818131218010478140202e0604c0626c0616c0664c0654e0202281604d12a5312c40d2980ca04156054148408c040c0d80ac040d04419036262040d325854c404e05914540d0dbf403fbcbd3c04030381009752d9848290654180c1c43,0x24e0823a0c080b818133231302625246062611a19180c0e0d0201466581e1ec0c3a3628a0d69e02b06a40208ea40204e0402140b008042e167c787a0402168d8030b69080c69ac8010475900204e0402140b0043580415a02080414]]
theorem XR:FBO X5 0 33:=Tz oo c6
def Bp:Z4w:=⟨6,1,32,[5,5,4,4,4,4],[15,23,27,39,43,51],[hx0,hx1,0x2c4c1,0x2c4c8,0x2a8c8,0x2a8c1,0x2a701,0x2a708,hx9,hx5,0x2b508,0x2b501,0x22ac1,0x22ac8,0x22748,0x22741,hx10,hx15,0x23541,0x23548,0x254c8,0x254c1,hx2,hx3,0x14ac8,0x14ac1,0x14741,0x14748,0x13948,0x13941,0x13b01,0x13b08,0x158c1,0x158c8,0x15708,0x15701,0x1d501,0x1d508,hx11,hx16,0x1c548,0x1c541,hx17,hx12,0x1a941,0x1a948,0x1ab08,0x1ab01],6⟩
def Gp:=[15,23,27,39,43,51,31,47,63,55,59]
def Pp:=mP Bp
def Bt:Z4w:=⟨7,2,75,[11,11,11,8,8,8,8],[15,23,39,71],[0x1ac688,0x1ac681,0x1ac642,0x1ac650,0x1ac611,0x1ac60a,0x1ab881,0x1ab888,0x1ab80a,0x1ab811,0x1ab850,0x1ab842,0x1a3a42,0x1a3a50,0x1a3a11,0x1a3a0a,0x1a3a88,0x1a3a81,0x1a560a,0x1a5611,0x1a5650,0x1a5642,0x1a5681,0x1a5688,0x19d888,0x19d881,0x19d842,0x19d850,0x19d811,0x19d80a,0x19ca50,0x19ca42,0x19ca81,0x19ca88,0x19ca0a,0x19ca11,0xee888,0xee881,0xee842,0xee850,0xee811,0xee80a,0xecc50,0xecc42,0xecc81,0xecc88,0xecc0a,0xecc11,0xe5c88,0xe5c81,0xe5c42,0xe5c50,0xe5c11,0xe5c0a,0xe6a81,0xe6a88,0xe6a0a,0xe6a11,0xe6a50,0xe6a42,0xf580a,0xf5811,0xf5850,0xf5842,0xf5881,0xf5888,0xf4a42,0xf4a50,0xf4a11,0xf4a0a,0xf4a88,0xf4a81,0x11ea42,0x11ea50,0x11ea11,0x11ea0a,0x11ea88,0x11ea81,0x11dc50,0x11dc42,0x11dc81,0x11dc88,0x11dc0a,0x11dc11,0x133a81,0x133a88,0x133a0a,0x133a11,0x133a50,0x133a42,0x135688,0x135681,0x135642,0x135650,0x135611,0x13560a,0x12bc42,0x12bc50,0x12bc11,0x12bc0a,0x12bc88,0x12bc81,0x12e60a,0x12e611,0x12e650,0x12e642,0x12e681,0x12e688,0x15e881,0x15e888,0x15e80a,0x15e811,0x15e850,0x15e842,0x15cc88,0x15cc81,0x15cc42,0x15cc50,0x15cc11,0x15cc0a,0x174650,0x174642,0x174681,0x174688,0x17460a,0x174611,0x173842,0x173850,0x173811,0x17380a,0x173888,0x173881,0x163c0a,0x163c11,0x163c50,0x163c42,0x163c81,0x163c88,0x166642,0x166650,0x166611,0x16660a,0x166688,0x166681],8⟩
def Gt:=[15,23,39,71,31,47,79,55,87,103,63,95,111,119,127]
def Pt:=mP Bt
def Bu:Z4w:=⟨6,2,66,[10,10,10,8,8,8],[7,15,23,39],[hx0,hx1,hx6,hx4,hx7,hx8,hx9,hx5,0x2b80a,0x2b811,hx14,0x2b842,0x23a42,0x23a50,0x23a11,0x23a0a,hx10,hx15,hx18,hx19,hx13,hx20,hx2,hx3,hx11,hx16,0x1d842,0x1d850,0x1d811,0x1d80a,0x1ca50,0x1ca42,hx17,hx12,0x1ca0a,0x1ca11],6⟩
def Gu:=[7,15,23,39,31,47,55,63]
def Pu:=mP Bu
def Bv:Z4w:=⟨7,1,34,[5,5,5,5,3,3,3],[7,15,23,104],[0x1ac688,0x1ac681,0x1ac642,0x1ac650,0x1ac611,0x1ac60a,0x174650,0x174642,0x174681,0x174688,0x17460a,0x174611],4⟩
def Gv:=[7,15,23,104,111,31,127]
def Pv:=mP Bv
def Bw:Z4w:=⟨6,2,62,[8,8,8,14,6,6],[7,15,56],[hx0,hx1,hx6,hx4,hx7,hx8,hx18,hx19,hx13,hx20,hx2,hx3],4⟩
def Gw:=[7,15,56,63]
def Pw:=mP Bw
def Bx:Z4w:=⟨6,2,66,[10,10,10,8,8,8],[15,23,39],[hx0,hx1,hx6,hx4,hx7,hx8,hx9,hx5,0x2b80a,0x2b811,hx14,0x2b842,0x23a42,0x23a50,0x23a11,0x23a0a,hx10,hx15,hx18,hx19,hx13,hx20,hx2,hx3,hx11,hx16,0x1d842,0x1d850,0x1d811,0x1d80a,0x1ca50,0x1ca42,hx17,hx12,0x1ca0a,0x1ca11],6⟩
def Gx:=[15,23,39,31,47,55,63]
def Px:=mP Bx
lemma b3:cB [(Bp,Gp),(Bt,Gt),(Bu,Gu),(Bv,Gv),(Bw,Gw),(Bx,Gx)]=tt:=by decide+kernel
lemma op:Ob Bp Gp:=gB b3 0
lemma ot:Ob Bt Gt:=gB b3 1
lemma ou:Ob Bu Gu:=gB b3 2
lemma ov:Ob Bv Gv:=gB b3 3
lemma ow:Ob Bw Gw:=gB b3 4
lemma ox:Ob Bx Gx:=gB b3 5
lemma k17:KOk Bp Gp Pp [(32,[6,34,35],[0xa1c9d8a3b8bb1686c75a8ed4eb51d99d6a49a8df854942e3a5075a741cca6e941d39d07325ba0e64775170c3acc5a907b275a0eccea3998dc954d493bc3ad487475a90e2eb521b1d6a434bb1696574a0cb8e941969d2832cba5065674a0ca6e941939d28325ba5064775170c3aadd70c3514051082412e6b,0x68b7520c8ef925a4ee4eb4198dd68329bad064b75a0c8ee72a49de1d493b8bad486c75a90b8e1b46649283393a506637992927727524ecce94198df14b521c9d6a49ec5d6a4333a906637a929267275a8ee2eb51da9d493333a926637d135897475a8ee4ec51dc5d6a3b53b1686675a4cc6f6262d0e8ec5,0x20e653741cc96e30414762927351ba84d927331ba8e653749cc96e10769419e1d2833a388405b1b12181dc620e64e7509b20e663741cca6e839939d07325b861d89399c9d27331ba4e653751cc9cea3992ddc7c30e3bc5325493b8bb1696c74a0ca6ea49d39d28325ba50647750e3148331ba9065375a9],40),(33,[6,34,35],[0xeaae1075184ac6918312d0f062589dca3ac3c1895475c9349ca687d394c8f062189e4e52c3e9ca5478310a4f83462131e8c4233d5a94374090a5301b463b6281dc712a12635066275093c1ab50d0f56a191eef530bd5a8587ab50a8f77a945e6b3263d1874a7a30e8cf67250dd024292cf3861c20c11e2b,0x87a586cdca7079b94d0f372991e2c42c3a8b041d46e1880840b31932015964f3228022d963268b84b9a65ccb9ad2c8f35a551e4a4233a048531aad3b23d5a7547ab4e98f461919c34104821e9632bace8ce1ad3948cf96a50de440d0cc5a87079392c8e4a87462151e8c4263cc805618b150e9cb6478312b,0x70c1071d9890c0ee3145c30eb328b861d56eb861a8a02884120973583409a32c5a2e1554597083047aac1a2aa2cb841823d562aa2cb841823d561b820265814ac412087a584120],0),(66,[6,34,35],[0x1c6d2060c20e9205f02438c40fdd470e300b8285e54be50c20e924b9ba7943023c883188b1c9227a1f3c72009e07aa4e206017050b492d78a1c6207e683471805e14c213471881fcad01c6017050b4991204baa15c91841f270e246047519e340b1821c818eb14f0465722c950e6402b0cf3861c20c11e2b,0xae1cc518911262921254444dcc1a40c08ea2c92c82d8cd1c6207e682871805e149706a84c246107c9c4491811d452648112c608731299110a92688d1a2454b1821cc614a414d8b2258c08ea203188b1c9227a1d3c72009e07aa53206017050b29b645081841d46b9cc246087cdd6091811cc4112d2644563,0x34642e51948b9662e51b8c2058c10e524a19c13043291245440ce09821284a3352a7163023a8c898ae499120c626145118a490a5118948692c8e4c45118c48625171338b1841d24d1589c4a24c96648133c60873129c1044f1e39012f1be80e480bd621c0b9440c20f833205903023a8826e18d52595c69,0x61c09c102de58d206107497183891821c914e138b20604751246340a652a255312a5b846514912c490c88a524ac612b1864248c8e1245312b1a89231c48d8660c8e12453514492318528914464958e141942a2485228a23228c49225819548b12512a2428a29242889854945312453910a429250a429250d,0x5a2a228c498852310c54645724c146249944a49231a052a0cf092a4a960c862924ac6224894924638184ce1805e14e10954c48e70b2a14300bc290a4906544914e45722d024292c0d034709231a492298e1191c2321a385449562aa54a997098a4932950c4954c9954a5491cdc2254b0276d718703754d28,0x45b2e44187083045cac209043d2e4584608aa808755c8a8618aa8087558681aaa80876590a1a8b041d46e1880840b31812052048521b84256348cc8057192332015a648cc80565932015c61a2e518b9461a48ae71889246312b1848c722b92681214a60a522b9460a522b9461a06d19124494a881b4658b8,0x2058e1820e230681a1080b63624303b8c0da328b861d560d75c30d45014420904b9ac09a306b040d60aaa2cb841823d56104821cd6209043d2c1a228104822cd69e64500],262144),(35,[6,34,35],[0x2463090347584cb1801c14914ceb099e300384848a712220492b181a12b18cc2848a60991034910509523eb1e30038284808163240da460c00e0a490c8a53c4ca63003848892a190b8b9e3003848b9165c9304a04853194c8f9c300382058c8124090a5381b58e1801c4605720d024290cf3861c20c11e2b,0xb9161229a45728d024298c04244b0484ac619428489722022e499722c5ca30925439900ac30b9460a225728c240d2e718121950ae6181a02a2425422e49c8ae518081a02312710501512a212e1026c5a206d084909910055ca309855c8b0b9861201425722c068286412b947820c8489640dac68c00e0a89,0x34c4860771804081628b041d46040b70c40420598c9900ac3020580205e0808a206d21801c102c6082c8c040b8184ce1801e05420d020290ce1820e231024294c5c8b4090a4b0],0),(36,[6,34,35],[0x34e1880840b318e1820e23008102c9900ac300812048950d720d024290cf3861c20c11e2b],0),(37,[6,34,35],[0x69c31010816631e70c3841823c5638608388c02040b],0),(38,[6,34,35],[0xf3861c20c11e2b386202102cc6040b1c3041c4601],32)]:=⟨op,by decide+kernel⟩
lemma k18:KOk Bt Gt Pt [(32,[1,4,5,6,7,34],[0xe83192e3394467418b17418a9711ca133a0c4d381b13314e17314d47314d27314cc7314ca7314c57314c37314b47314b27314ac7314aa7314a57314a37290967098a0ab84c504dca4239c06281ae03140b73231302625246062611a19180c0e0d0201466588245c1c4022d0e101158708089c38c41011877,0x17030f699c501b93019d3784282e061ed38c95071a5ca740b2e941ad17524f64b9cc4ac5cc4299dfde01c3a967840c0e021f4b2a0e2d394e8165d2835a2e941ac97394c672a0e1d394e80e5d283562e941aa97394a674a0d4e3818d30c535ec3bc651ce472ad02e3950b165cab4078e542c397311c6831a2,0x42524b7363681009772c7856d69e9ec045b962d3c0572c175a617596f0aead3c3d818b74cc5251ce021aca4319ca4315c053086e5214ce5214ae0298237290967290957014c09b97151607060804050302011716c787b030ee98281c0c3ea6019d301ad3784140e061f53114c233bc13300dc980674fc214,0x1b180d100317699312922],240),(33,[1,4,5,6,7,34],[0xb9574125f0f4d82e5a2c3172ae814be1e9a85cb4582ae5a2c13720148739574035eac3518e55d00b7ab0d453e60aa15f305506ed028148b40e2a33c92623c92613a051499e49291e49289d018a2cf24928f24924f4590ce565854181c1a100c0e04025c4b328581cc61507308521c8613072084a1c421187,0x82ea8c2eb0d6d69e9ec045b16581c4a729e024ba46b515cb03854e53c0297489692b9607069ca78032e90ad1574f6039d1bc0d78a0d4638185302eb0d69ec2b16575c4972ddc21b95d70a5cb77046e575c1972ddc09b91b6035eee2d18f66928a7259a03be1e6a15c0c0d806c4c07686f0f6061d1b2d1628,0x3258c22b90d610dc96304ae4358237258c0ab90d604dc96301ae43580b7b1894338082b04020a0d87b2a6d0d6282e062cd3075c10514580d29ad3c0562c7b316585c17b2a6d0d6282e062c9b3827045c7185d519911c45d499312c4d16445d45945615311c551344b16445d61aead3c3d818b64c5a7a0ad1,0x894949722615a231585524c2ca4525acc5c94b11c591253512933108931b47822cb0dfe09e1ec281c0c7aa66462604c4a48c0c4c2343230181c1a04028ccb01751704f60e1d4b31302524656419181110012e65822200c0e022e4b1e9ec043a560607010e358c0805b0c9131b03b86060342d864892da1dc,0xa0b818726c92b0aa2871d08c51c6c2587820634ca28e264471b081b137f78070ea582c8adc12624c5c2e08b0e3262e08b18b162629a2e08b24b162989a21c531347822ca2c62a526892970b822ca8c58b0a38a6268b222ca4c92b12a299238871628c51c69252471c29a138662615a1342e158985684e1a,0x7844c4a48909492dcd8da04025dcb074180c0b619224360770c5c54581c182010140c08045c5b1e09980d898281c0c38b6787b030e8d9c1018d301b133c3d818746c1da180686dc10a28b],0),(36,[1,4,5,6,7,34],[0x20e020145d41ad3d8560c0c098011ec918300b00a0240208a8288c1bd830750c08801060c68880c02e0204409064860441929bd90300a0124218c0288885618010024121486a28098280110863a084210c02908c3108638086242801c6384c1bd830742da1ac505c0c5926565854181c1a100c0e04025c4b,0x70ea19918981312923031308d0c8c0607068100a332c66120a419506030710c0102010506c0c804c13d838750cccc09c9185906c6034400cb9a60402140b00a01569e02b06015a0502916008053c10b00c0db020100280801030a64040c0d80d29bc10368140a418189ec859017b286d62e148300a0882e,0x4890d81dc31812300c060b30c7f78],0),(37,[1,4,5,6,7,34],[0x4890d81dc31918981312923031308d0c8c0607068100a332c7e78060ea19812300c060b30c66120a419506030710c68140a418f640da1ac505c0c5926565854181c1a100c0e04025c4b0042c10060e2189131b03b860804141b0d62e148b022025ec81b58b8520ca8b43440281c0c78a60402140b],75)]:=⟨ot,by decide+kernel⟩
def Z05:=C Bt 2 [1,4,5,6,7,34] 2
def S7:=(N 9 [1,2,7,6,8,13,14,12,42,44,43] (N 18 [3,23,20,107,104] (N 33 [6,123,131] (N 72 [33] (I 20 (J 0) (I 52 (J 1) (I 28 (J 2) (J 3)))) (I 66 (J 4) (I 80 (J 5) (I 65 (J 6) (J 7))))) (N 40 [6,123,131] (I 80 (J 8) (J 9)) (J 10))) (N 17 [20,104] (N 33 [120] (J 11) (N 35 [3,123,120] (J 12) (J 13))) (N 50 [3,123,120,90,93] (J 14) (J 15)))) (J 16))
abbrev t7:=LC Z05 Gt Pt S7 0 11
lemma c7:t7 0 11:=Tc ot [[0x4030371138430a8406f0430862c1034260f10818716c0606c069820614c0680d308620181b6894d1008e03c440d09e04068c2828158480de080dc882406cc14146203511aaf2e303c82eccf151415a075080d308638101a035eab32342b20e6120aa101a91018158c6821a8531221a81bc09a8c38881913,0xc0d80d5040c2980606d420c40ca980606c0614d820a406d040d8980614f820c406d],[0x4068c21900d6082a035222901a1480d8cc4d9008c4398463810c2848614480d01a8901b095080d224e23e543880edcd0c081d09712083ae2e240877a686004ed0b89005c2203406b041901a911486101aa1112290a80d0a48918d0406942848451480d01b814482901aa1226820a406e0406c2418a24c311,0x680d5080d224c203406b04520346101a298280d1871203406986a20340698429e08c101bdccc9e2310e6101a89704621882b28444984068c29108a318480d6b3409943482ea101b0901a4498],[0x3406d0406c44068630901ab101aa9053c101a82b8414a120c80d88e04068520a68203541888150c612a101aa0845c09411880dc884588a240691214829c080d01b81a084584a441880d1482924682034292460a03406d07220358101b410a80d054068c4918494122406c2622c1],[0x498e0f08d03e058203406e043130a46120342901aa101a9101a5098406b8406d14069424891406a121488a034c38101a228c38930203612034c20348a8901a149420355a53a442380f8101a9162406a268211406c24308a40680d30a27821142902a8901a03702310524480d18d0406b021882948c258311,0x31501a067023511250cc4a080dc0f96b288ac0b854b4e8b101dfa322103a1321c1075e643810ea8d08009e1b440143302e1131116035412846111245384c11880d0c4a12240ae0406862c1a88190c54102a4501a189840c862c1588190c4069840a914068634101a0a862c1c880d284311140ad040680d7,0x1211887509851916439065121085301a42723c41f09053c2667c404605c1aa922bc2425104829e2b644242302e0d80c46893a122876e7468908c83b048ad981a121a4176a848888816307686060708d03af52344190b053c35c40384621cc4a1a248461a322c8720ce040c94299032c0a544480dc0954037,0x1a0a41c837020a41485954c143c60a910509283c560a89850920bc56088284621de2a26142304e6214d1945459c0834396092a1aa626230c06982622ac0680dc0a82608c1309882b00d6080d10939212b42c06f0591e101181782f051916439e643891188714a8406942190c4298c4e8d13002460f0158d,0x48901a14d05823101a03542037020348a035811480dc4829708a1604296080d0a48901a14e04c20c40698429e080d18406a24068c40698229a0a440686203429a080d50542c480d50512034614880d0c78250491054068c5821140680d229085301a0361ae2e3c2310e6101ac1210c781a88c103506989c3,0x858229829324a8b20346a8c8720ca241494203583310321481a415125501a03452065131501af2e3880ed1091081e26cb041e45c7021f570c009ec649005c2203406b04895880d1140ca244480d14b042a03406b042901a89c8d0406b025088a28747d9444621cc2604a1a0861e080d504614480d505c20a,0xa322c8720ce0499032950680d18406b046a002c2c8aeec6512868a1f05cf204609c1a0c14c7f22a5542c22e61e6a3c911817069015a512582430f01896121181722915b232a243450eeda8d10882c22ee90930e1182786d0c8708c0b83488a0d10ec2c50f1149a10bc2c22ee940c0e1190786b898708c439,0xc64069120545219c080d6042901a4501ac0985c111214b072203406e048901a453840680dc09840680dc0852c1588a11c58f204701f28dd4091628782e0416a52549894a4a982b046094219045c080ee241c839c4c1582284322903250a640c9829503241419608427230420090c3c26680404605c8a2970,0x6c541480d508640680d308540680d30cc4116084216c4294c16b28dd5c91a2878281a0a908c301a421cc069d572be50f143c1747d32c4621cc20d41a835dd934048d143c15822c8451842a034724c9085301a608c33102a1481a5538b0e203b8b0e103be4c5c1078961c08770808804f3aa3002e1101a14,0xc2064520a42a05429e08190336bc91a2302e450336bc91a2b02e1502a0574959344605c8a298281502a610671202b6bc9142302e450320a9842282b6bc9142302f050320af041a03406984148540681530c14394c40a865120342901a8901b052a80d01a8901ae08a4068530525406954068e4068d406c64,0x64],[0x820374203451306820356101a19415415080d504c128622034c1287224238c0688a414c2b0b42035c2035a2187823588b1851108a51a086141541445820a46101a515840a8c341448d622c06b0406a0bdbab9e2b10e6101bc101b4554422d84308a3415080a82c88a0a0a22c0511642b0c05117414890863,0x345609c32065324214c0348429885618152848461c4421186034a1210a610853a084214e22304a1215865104214d305180d224c1211861085b0a24214d4351131ac84399614505211861085314682034c11448561ac44488a034c2226821146150889284a20540698406c4406945824298c06a0a4481960b,0x421cc215869870c0680d50819055820340cb041582a2a035324230c06815a084502b415084501b610352282b410e68713344609d1201b4101a1508a4a8aa1a82b0546515164396080d224c12868713],[0x942e78ac83b0484618540691203582035424298c829126080d50908e30842980d224c1b6164f15907211861085350944304846184230d420545130406a848429c44308a20351211622c880d7080d01be3eb9e2310e611454203406ed534788c8398451445820340698406c4430c15220350501b116890863,0x1085308429c144490a5301a0360a41512224320a52924a0d01a14c14199db4cd11907608894c908c301a034c20360a421ac0348429d44f2c5880f22c5840ef2c5820f9ac5810f3a64004f1284802e11085299540348461ac4210a6214a7150843980d08439e],[0x2114aa054a1a8908531ec8d80d5080d6080698512034a188829c8908e301a488911482944ac2035c2035a2287820342944582034292440aa2759a0444605c8a03406b05a101bc112288a2406e24c24218c210b6034210b7ac0b9e2b20ec12118603406a4488b0484318153051108a9102bc102b91210a651,0x4232d1101a4298cd0819e0962687189c344605c1a0aa224230c211875108461954034c2035a12c7189c344605c8a68406d8444864b1608c1187189c345605c2a114618880d1872],[0xc229825090863a8c3406832034194480d067820346a0361a03419c480d2aa2a064c10a889a880d28662034c15880d284e20a406a85a211489284c11880d18430b0406f04069823101a714882902a8901a48b040694231c880606cc128430815508191306206c4ca21145101aa1052897040a862c18890ac3,0x532c4681d4203462c101b454880d184c1147220c4a101ac101a91a8831184a12240a9440ab06224294c0b0ab02ba12c48429806b0484718451126111208a2948b0414e84843184216c44815609085302a4292d45684a21086308a4214c069424230e222844506261052510a218b04853184214c069424230,0x113880d01a6108a3101b91142035822906203453a101a30943112890a4b34210a4b0682a211c6214c6108532880d01a6101ac111251644843184216c289085388d1403542034228551203662034e2224a10c80d285a2184c12846201a6101ac1588068c48901ac101a18a84a203406a84068626101a03656,0x101aa108471b04846184214fc21148901aa124406b04843184214c0690863d0d440c8194484548845244520a4610a815185a20326108b63a9962302e1502a30a440ab441a034291146101ac11884501a29182312a80d01aa111406b0450986220340698414a84068c23101ab1a88a101ac10529164406943,0x841a510531908b1540582034c118742034c1f09086302a108730684214ca2284847180d01a6128406b048431d240680d5080d449c203431284c2035a203489284a20349101a310c2516080d01a61f090a6308431815284842984214c8a10853288a1211c60543102aa13049121187110842984214d420345,0x8c23e6a9a388c138645248eac4e82c48fad2794f0d053cee22408c23867964e2a416117bdf6091190730855122240cab4cd27a12227ea53491188714a8454a48191cc16247e6a80c1c5845f88cb184621d425123a4a03448f64448e2340f99e51118b053f731c388c43a870aa04871611744daeac488c839,0x1230711827448641a0340a942c80e589143dd22c388d03e8816388c13a24327d498422240afaa26102304e19eb1688344845c1bb42b122310e4214d226102d0a815032ae5348e84891c2bb427922310ea1148008042817748b102340e91c2064811907121162938a9c5583448e19123ab11a0b123cee2238,0x9de507005e020542883406a440a8190692bea11a0b123855ad8e1278b08b8345352a8942310ea101a0547d7d27923450fec8b1140b08bcea9a388c23f96a2388c0b855220d288511a2c248121c5829ca3b42e922310ea10ca328940406c54c2054548340681508a0d14a440a8890c8d130aa048712117c,0x10a7a101a0354206468834112191485582d0908e30842984214d4228406a246b6364982c22e0d132799c44262422fe5a8102302e0d58a3215210a723099a2320ec121186f0a2ad09440680d4880d2448a034148640a915120340a81aa102a2328ab841a8928a260b081ee791041d8507021da589011ea68d,0x151620d01d448890c839112190d41a03562034210a60cb042a8a908c30842d8c12],[0x1ac0c187301a03583064ac90c193301a034c2037030658c830a791044068c20370203406c8582c8c182b20c29a0c159c414829c08320641a0ac19a301465b02054c1604144581930581050370618c0680d3080d1898a034e28a80d18406c84a2034c10c406853812290618c06c182b01a90c185388c1923,0x1061ad0662c830a78108a0d45306c2c90c191b121833060d],[0x21cc214a44a3210621480d4880d0a702034296058203712605a2034310a4c19080d0a43101bb4eda22310f210538130829604c1a2831304069865203406b058101b213882901b2101a149847101a90917820346101a9102a2901a30e0589052035832101b292883101a2901a1901a035825105222a46c311,0x7961c4078961c207d224c107c627851d887c1e3c027c1518017088f654cf670cc1186c759445621c62034450a406b0406853b4f1a22310e614880d01b8108bacd11e2b10e3102a03703acd11e2310e290535101ac0b44320640ce041502a9102a0d3880654c18ed3c678ac438185302a0606c037fc2c3c46,0x4c1184454880d0a406a440691406855a2018532440c9140c854188354528e04228c52a68655344621cc218445c081a9840e88b81a1954d11887148292a8299882918562187223d91b304610a8f646c0ab0405583814c4b10681502b81034720a406b06320342901a14e0532034c101b81a882902b81035a2,0x3414a440a81506b0545685c1584a2034c101a6114662034c101a3102a91a8c343083514829228290a815c88151c815988615880a9161a0a6321141506ab082ac1069e5ca101db507081ef791041df507021ec6ce009f0589005c220a5320a4c1184620a406986a205445034e21840a9140a834710c80d0a,0x2a620d5a1069a2588e21142a0543203522034611880d244a3610522880d0a80d184620368a0540a984320a431e080d3070a03431c48510c65203406b044501a229852948806b045106491b0d44068320640d05582034e203406dcfa6688c4398406b0462034150c7820340698406b05c1585220346130722,0x18462034332901a0348a0641502a3883582034068290a9446281558da849c2c28e31c2158911887148651530861c880d1864a03461c2829186620a4618c829187420340698692117c2034c1a29c547081f07d1041e0547021de5c9011ee74f009f15c9005e0203445c48311465214445e0a4414b2294b12c,0x4805708ac910103bea96083aa88e043c0b18013ca91000bc0403462304d102a7114b0a0364a01a31015608a585494a20c68a037c28080da48299880d0a74203431e08641482a0a415228b1068e2034620c4a2034338901a30829608150c8e2e080d01a2928829a2e44149a2117820a8c106962988e2034a2,0x3344621cc23105218d241883130b4215182588e21146292815d0834055820686345052388712282a06863c10621835368962310e311482a3041aa4a8a92b42e09441482a06861189a2034a385052228296080d0a4c2034a33101a034c205452184a2034c11880d0a7831901a288622e2601471de500c715c,0xc52c52534471053a101d608628a665d],[0x538880d0a445184198580d0c42911461064c60a406984228c4a90531101ae1064a6030530320c0ad1108a8883063b080c0ac837b060e95c440c32c068a20c18c6101a228c20c14f020302b184068a2c08305320dec183aa711f080d4442901a5101ac091406b14068527101ae100dc08528898419a1bd923,0x61c28712c585545314a54951525685ecc581908a31052c4b0a51525295453149406e85451ec8dd85ece18f646c29184453d9a301a18bd9c301af662f023d91b1ec8de047b2363101af658cc0bd98b30228862f670f820c0ac3081903261060c60340691406b84069c20c4e10a94406d2591060a603063030,0x33430627b316035ecb180d0c5eca98317b2360b4388a47b237610e20d0c5ece18f658cf652cf654c06bd9c32882901a613023101b617b3460cc2c035ecc98457b2c603406985eca581903251252928c5eca98f652c31c482908a311925494a61545317b3463d94bf08f646c311ec8d987423d91b1147b236,0x8a034e128831b080da8c1bd83074ac2880a46c620c41a036920364a0366203431b08298c80d0c6528080d86831c8c1bd830754c837b060e95a0dec183aa63d91b3d9c3060c6034291860dec183ac781302035ece18f652c627b2363d91bc880d7b2660a4617b2c63d91b604f670ca20a414e0414835ecd18,0x41bd830752c060c6f670c837b060ea5834f646c308e12884506ac306f60c1d6301a034]]
lemma c8:t7 11 17:=Tc ot [[0x9c88150a40adb23c688c0b83406e8406a4214b04068620c68248452a101a03682d101a1880d90aa418831308320a815deea0f118170683114e0662108d303406908e31420c819d6c98c118170a9520577ba8384605c1a6890a4302a828159080d05702688a41480d6080d5054218429c08c62a282e061e93,0x864a8aa1a9a2588e20ac167798344605c1a03406b0406852a11434101a60c8414e846080d50e3444888c0bc140a815a081a14e046210ac301a6090a4320a608c406a42608a42118618853a10842d80d2148603521188c148452a1a880d284c09840680d60c8406aa4909c406a42a08c406862036420c7022,0x61c31085b0c92a4192d28698d6421cd3039065acc18a414b44509c414a540c85255032148d4211a614ac4119de60d1181782842b0c0c8a541604a0c8414c167798344605c2a032a103206543412c414833a101950a821506a0d4520a4323882b811420c83534419c09623882b210d62cd420a4590e4196b3,0x2b02e1101a5501a0b89bc080d148c41482990e7548808c0b8545d418171c60614c0c45d41e54c6608c0b8181b8a81a1b08525819214a603341211a61085b5881928484718a10842d88469e04508640caa495154351c4b1344852181d0e3410e219033a1035608332106a324b1908e20ce040ca42d11480ca,0xa0b89b0bac31882e2ac2e38c17516311482e26d210bac3aa16cc118170a82e38c171c70505c5585d618c4175161758615aa16cc118170682e38c2901a2e34e62324692a40cdf340608c0b83406819c08a406ac406a54068d414cc406852d10320685271012eb05880f4283840eba42820fba83810fad9308,0x2648c5c14c4171572905c55c94148320a8622eb0c3882a188ba8b05d4582a171c618c84171560a85c718630520a06702053810c21990819588199882968819484e24c747880f6aa3840ee262820fe2a3810f3aa3804e110325520a908c4032a6908545d41c4ca6688c0b8181b05c6982e34ea85b304605e0,0xba8b0322e34c0b8ab908a417136171a6304533bcc1a2302f0505c4d982175863114206582066422e38c1417030e4d8191417030e69cc434923c99a389183db23c388c0bc1702073811482928432065320a419648194a8191a819388192a829988a16882958822064c1284622ea0c0d2982e2ac0a8b8e31a,0x8726c5096bcc1a40b143d91ba388c0bc17020b89b548a10c86a68962388a0b818734c341c2c860b89b0b8e300cc98c5c10322ea2c0c8622eb0c17156171c618c8417136171c618d7138888c0bc1460832066d91e2c4605e0a0d54c6c2048b183e3444408c0bc1419c08aa389626880626ca1188ba83030a6,0x3162d80e16c0e92c0e58c0c83b4301c2dcef30788c0bc146c6034400c59a60640a0c30c819141671b4a122302f0501c39943e50ec890c3b04d2859148b303d30287902c30f43ec8e2302f05464590e41ca180e50c320653228a0c0604c0645d418199305c598185b03206682324d1ae270b11817828a0b81,0xd070b25a0a0bac30d100a070],[0x5a15840ad040a80d60c85ecb18f654c06bd9631ecc18a7230d05234a520a4325040cc841a034aa0346a01aa1388220a7220a6a2034299880d0a5a203406b040c8a562034a101b4124214b0406d24620185301a532420d01b0d4a80d1c46901ad1032b18a80d01b2101a03642c101a0364203429a0a842b81,0x8c101b410622952722284068c4068634101a29688150a40a83406f040a85206d052a03406d040680d18b046902a308a563210521a4324841a034e2c8aa29880d68806d05620880d01b2101aa0a84620352a2c62a30490a842b851ec958f64af42034068c40c8632124a90855157b2860a52102b417b3460a,0x36469162302e15052508c41a034a10a7220543103429588150a40a83406e852a034a101a310a5a341032306820b434d041686542064c1284620640cd8ba4608c43a840cd8ba4608c438c4a0862c11481903341304a10a819032a11436469162302e15182508c4508290c819ca960c118170a819284634106,0xe4406862d1c2820f19c2810ed1c2802f0101a034521882bc10521a41a18432034620642ba101a034c26880d5886130462037238901a034155080d284620356203431d080dc8d240a8150680d0c582036a2185620a5a2034150c78203723290320b4196081928462064c10323114819304a10a819032c114,0x14864d1032b1454608194c542150a18da389118170aaa21a6620a5a21c4694c562057c20d02a054520541a58d840a8151481506d140a8151481506c940680d1480db],[0xa81918ac33102a0558206463292c20a863850e2067820a86325035148320a419608e20a81918d047b3263d9830c9ecd19ecb182a3d933d5f6901188718c85eca18f64cc3102aa0862f660c14bd9a302a60bd963032066420a419a08e206562066a2065a2065211880634d21d2b950158170abd943c08181b,0x54f2206c4c7b2c67b2a6055eca581503231585ece18f652f223d9330c78202af670c31d08f652c0abd9c3c48f652c31c2815032317040ae840ad840ae240a8535102a18d240a8638502a18d147b2667b2a67b2c618d05ecc18191c40ccceae588c0b85406582315140ae840a863c10320a8636118218e240,0x98f64cf02184308a4820b614d0414865eca18f670c14bd9831882902990a847105219052317b3260a414d0490829a0b04149c414982308c40e98259052608c2197b2a6064610334105381032a0c85ecd18c11840cc840c8c3810520670341033517b2c6018533c1c303230bc3d818764c0c8c260bc3d8187,0x5ac1182294c4711423105219032b1346820b430a84308a416a52348354c452c105271142308c414b298e203ccb96083ae88a043c088a00b844148c21903230ac460b4642053410c2191c5492c4508c40ccc40cb440cd470a0534105294992c152430865312c47103351142308c40cb4702f0f6061d531ec9,0x31a482905a14a84310664218416a84508a4190523100c29b46821a419242293440c8c70a05aa10a414864d11c431c0bc3d818764c1486118a620a5a20a64a0b429b08a1a8861062c10c8291c4190c7820640cb0431a48193059407041e0385021d83c6005e020a4148e2c106431d08292c2c10c231066520,0xd9431ec81e8585930a083ed85021e4c2802e0604c030a60185b0620614de0c180616c188c20614c030a7211fe080c38b6030a74178286190267943b02430f217f307410e519264590640626c0616c90818d37f78070ea18f64ccf670ca0862f660c0c29e04148e2284620a6c20a43206429d08190c782064,0x616c030b76103ac280c4d80c2dd04b0a820634c132ea082b30ef184882b20eb8e4002e0e10cf040e82f060c1de08b21cb0a7826603136030b6031a7217f78070ea18f64cc18a42f650c7b267a1342b080626c6290831a0bd9830317b30785030a63d94b062909aa0e103b],[0x310c2a10520a4c3810520a70218b042a28414b0418831149850d05385062308538105230982155881505c69e052102a3102a90a84057020540aeada458ac43c85426102a05542c08a4320540a9840ae8591032066420aa840641517186175478105230b440a982509c40a98250b023102a30b02b1068ba83,0xce181078c9440270282e26c169523481d62a522e30d5103aa8a8a628a40e955154c7020a58105298a861a0a521184a168829604c1284e20a581242c103b311c52a0a4a11856447101d6447041e754b021e54c9005c220a52105261052a1c88e105a70984268a414a841482930b043085381188610c229052,0x180a8b8c3e082e26c2e34c310b8e39081902a0c984311752605490a840a94231345911751602ac1242a102a191c4508c40ab440aac40ae445d6183460854b04c20d4d21c86198861c2862b041ae85514c452075451a4c54a430835ad94cd11887908a44d0e5514c5420845a62810ea14ce184078c9442074,0x170482928521688292862407021e13c6005c220a414a8414c8414e84320640cc8414b052a0a40cc840ca84c10a83128429c88ba8b05c65815171a617136054c1175460a41905431175860540a8c40a862a102b3102b1902a18e8450a421905250d440ae445c61c34171c605419142314945c618292845d5,0xa4720a461c8829052c17042a086018e101e018e081e018e041e018e009c0a0a6650b021e3448005c220a40aa84e20a450985c10521518829284610c8ba931420d32160869388c1242a106ba114829f9da203c041c103f8cc041c0a0a4a198829305620a4a18a82948414a8414b04622843180e1808780e18,0x105c4d82e2ac2e26d8203ac1171a60b8cb18829171c7210520a4c290829508baa303a074695081aa8452988e2a8829284620a5a20a5628cb222eb0c171360b89b608291754630642e08c12845d618540b89b148152a5252c5c1171860b8c3908152845d618641496150829684c5344c20a6620a5620a51a0,0x2e2ac622845c71821171360b8c3e08290142d8c4683028733200c3a06ea3010e2e20c171c7a6980870482e30e320b8d3db8e043c04171c7d4c0407d19a103e8cd041f466804e0505c61f1e7021f6e3002e1],[0x140a81a18d14168351481a188320ac840a862b244040eaa23820f2223810f2a44002f0101a035422842b0d1ec8d8197b2a6069ecb18620ad05ecc18293d95301a14bd9c30620c4520a4320a42a0547b2c7210680d484e2f650c14829a08290680d0c80d3892a5880d504620342af660f02d0d6282e062c9b,0xa835a7b0ac18181b1ec958317b3863d92b0c8f670c2a3d94b02af670c1a3d94b0c782705a1585ec8d8f652c06bd9c3c29a1064150e20d51406863c10538501a148636102a1881b29062148320a8150680d38c846b316035ac71c35eca19a1052310620d0521901bc101a18d8406c540cb82d0ac21501a18e,0x8a0b818734c323c18b0e5853c133169e02b1668140a4187268140a59e040616c191ec99818d302d908d62cf020cbc3d818754c7b2660c8f64cf027b2c6188185314506b4f01583169ec2b163d94b062f670c171669085d61bd9436b170a6182e2cc17166314840a8bac302a2ea2c7b2a6358b852cf02188b,0x2eb0d69ec2b877714087bb8a00b818131a0502986052f650da1ac505c0c59a61900c2d8390185b145860185b145160ba8b4842eb0c0c2982e30c148bac303a2ea2c0d2982ea2e903840f481c107ec0e043f607005c0c098351c5c16842cb423151418d8531052548e218c84505c0c39a605c598185306290,0xc3aa6d02814c3074030a6034a60c5211417030e69ad3c0562c030a661232c072c561439571061de0818290c521787b030ea9d165021da05029061eca1b4358a0b818b34c686b1417031669f06e67080f7338207b99c083814030a6185e1ec0c3aa601853018d300c29c840694de0a1b40a052cc6b170a618,0x3d94b686b1417031669b820185b3728308c43bd943030a601853e09a158405296311ac69c85e1ec0],[0x41c222ca0c308616082d90861c0861b0861e0869184c1a0865fe09e1ec281c0c7aa602b04f60e1d4b209ec1c3a97810157b3860ed0c0c8e20ab82d0815b081594a4a064070d6c105702032c103381056823d92b3d9933d9633d9a30564304f60e1d43030366462604c4a48c0c4c2343230181c1a04028ccb,0x23914260c343498250cc45082d1c4696087430a4207582b105ac0983190c29092160a640e942286421852160e4434921316142076082d1c46935718207c0ae88e203da06041c0a284d0b0450c852a18581303214c5a205a62e3040f8105a6296262e2840ec11c57446101d7446041c12185a507101da5070,0x505a71164392653105ad105b91165260b06b0b0e305869c8416869608b2c30e82c26cc10b2c30882c1ac2c38c2c62c16586c1869c1685610c2bb144075d8a043c8458058e105a628d2a105a7082d2946950c846294a3482d314a51a643811427105a348a51a7022946914a34e0642a88e2c10c2609643098,0xc7b2960ed0c0c098030b69080d898fe60e82fef00e1d430c82c1ac161c62105871b04608b24b05871f04108b0ab0422c26c608c1108b28b0d21a4422c2cc1696238ac2e082dd0a52205b33010f21161060b06b0b0d3306020b4a148490b0416f0430e8459518e148490a8450b04591586905b2105a90b058,0x8b061c83481c2079bcc043c04584c218642585216085a0b416c841686990b06822c81b130c2a080616d8319342b0a82c0981908189b2420b40c69941036261d00c2d80c6980d89d205081e902810e057f78070ea180e16c0e92c070b78105ae083b430d27054203943a083a43787b030e8d838c13d838752,0x1c0c38b60385b413d838752c0d8980ed0de099839073610e20634c031a7c15141c98ae080c69c841aa420616c030b699072b0871031a6030b60e40616c0634e42c12425918a316420384328b216080c2d8c1031a78130260642604c0c85824c8b21c871031a6030b74100c698aba0c0e55d04872d1618396,0x890d81dc330260419a19213040f2437e30624a0df9e0183a866048c030182cc302010506c0086b5a7a0ae1804159a9ac585c0459560b0b80872ac020ac7a7b010e958b2835a7a0ac197151607060804050302011716c3d9c3031a6c281c3980634c1da1b023141c818d3705817f78070ea581abd9c360428,0x402140b1506030710c0c060a2180cd0c60302d864]]
theorem Z32:FBO Z05 0 11:=Tz ot (Tm c7 c8)
def Z06:=C Bt 3 [1,4,5,6,7,34] 9
def S8:=(N 9 [1,2,7,6,8,13,14,12,42,44,43] (N 18 [3,23,20,107,104] (J 0) (J 1)) (J 2))
abbrev t8:=LC Z06 Gt Pt S8 0 20
lemma c9:t8 0 3:=Tc ot [[0x4248908e300521086024846184210d421084370946021894300a6b3066242801c6300a03444c04316b1064140682b01064316b30635983588d620cd622cd660c223588335983a8805304a140402a05ac51802b5983358a34c88104408c05acd18d620cd660cd628c6b10741489890a00710e1306f60c1d0b,0x4198841485414880901281505212880960541485a218481012418881102209107224210c210a6014a12048421d461a014049040d00a0250206a224230c4080d208456080588b224214c210860148461d440488461ac421086208842988461844028120150230805209824218c04822024843195402822409,0x8e300a4218c211861108421884619440148421c468208521904208240481520a224214c208846184408812608c2024824218c211860248431d44048228880948b224238c04809210c6550092118610484299460a5042090863085219442090a630122118711012027020244090422047820128104682024,0x4c410224230e22014089024210da1a8809244510c4048451121586102090c42084404a459100b5108311214a600a410820900a3164402ac420a440488311012408821100a40d44049027101208b4402812015025121486082090544238c04908630821100a5108421c468a1084300a015024230c1510a631,0x4402d4402a02510127106486032430220460210411a0809c8a320c10c06087110520348280a420c18c048c2208326386bd9030090880528805d0809214c60c4208411882404a4404e8402805409440281504b44408a12080d60b421100a20e448421805024048445121496014210861100a4090863a48421,0x23810139101202e240282349464182180918408422415252568402e05c1060c604404830430220c14e220246101241144193180c14c0c0ac1103063b080c50c0c0ac3083053018218440c1cc710820c18e0201414c049114431042114441929841082090820d2c404a45190e4d1012190123101311012208,0x2016320240590809016c21040500a090c7020144102722024050c712014090c652084090149114431a080901541486a20246100504905c168561605414842202402d0420844028238100b910133100b51868110220900a4100a611454188c1bd830750c06056030530880506686012452442084402f04028,0x340c0ac3084408e04060a6c0819a1bd9230227b2460cc2c7b296045ece18217b346027220224102261013117b246024f648f42024f648f0a024113d923c08113d923e0811042f648f120c02c1880a0c412024320252],[0x8e847b216405eca18f640c223d9030a9ecb1e15ac5c290601402844028c4028ba9308a2e38c17186171170105c458232100a108baa305c418811718608c14171060445c61cc422a0a0a862088bac308a016420a862088ba8b0057b286085ec85b22015ecd18e20a805088057b2c6188ba835a7b0ac181813,0x9080d0c429175060145d51a2a9881a1b78206d02814831ac5c291604569ec2b8604408bd90b02a08bd94364408e85ac5c29860c408bd9c300d0882a0460240462046c292bd90306280bd96302a0a422054628280580bd90b0427b217910320a82218811808118281190b2298bd9431ec85815485eca18620,0x2c10bd91b00b9104202bd96303626414028a0b818734c0640a03326032a6031a628a0c072030b621340a052cc0a1417030e4d832033261417030e69c0402a4217506808185300a0160201452a88e20322182805188a0b8187a4c0a8629085d6181517506808181b05d4182980832171c6175461881a5301a,0xa835a7b0ac18181b00c29829787b030ec9831787b030ea980614c323c14301853c0981032f0f6061d9303290bc3d818754c0a01402c84030b705282908185300a06a4c5081a53782163d90b28290bd9431ec85e85851ec85e040c0d8068154100b216850500b81787b030e8d806bd9430420500aa0a42f64,0x34358a0b818b34cb4f0158b2ead3c3d818b64c145061417030f49ad3c0560c7b306d0d6282e062c9b1e1ec0c3aa6c080614de085829787b030e8d80d89b40a0522c08428a0d69e02b061917569e1ec0c5b260185300c298a2830a0b8187a4d69e02b06050f650cf642dac5c29160c5210b],[0x8c96f040d9848290654180c1c4301650704f40c1d433024641810166182010506c413d838754cccc09c9185906c6034400cb9a60181300c0983b4302280bfc13c3d8503818f54c030360640606c514180d0d8114042ea0c0c09881024111417030f498090440d29bfbc038750cc09184603459860402140b,0x1224360770c7e78060ea19812300c060b30c7f82787b0a07031ea9921305417f78070ea19918981312923031308d0c8c0607068100a332c5a7a0ac197151607060804050302011716c5a780ac1828a0d716d69e5e9e008048b163f403fbcbd3c04030381009752d811010a0b818734c30383420181c0804]]
theorem Z33:FBO Z06 0 20:=Tz ot c9
def X6:=C Bt 3 [1,4,5,6,7,34] 5
def S9:=(N 9 [1,2,7,6,8,13,14,12,42,44,43] (N 18 [3,23,20,107,104] (N 40 [6,123,131] (I 66 (J 0) (J 1)) (J 2)) (J 3)) (J 4))
abbrev t9:=LC X6 Gt Pt S9 0 20
lemma c10:t9 0 5:=Tc ot [[0x15435056022062ad620c405ac41ac4085216b106191ac6190b5128242a64a090a3900a80a82d668c6b1066b306405ac61ac21100a08a02a0ac2d638c068c280a8201642016c2017220862298b58a30056b1866b1c6a0a8a6054148501415ac41a440290b6610605516a08816054148404c0599ac14391631,0x2149090a8a91ac2b58c300ad62cc02b020a90542802a24850564200a290570a08632084b23598b01a759346f18877db3c8f98275090c118ec0ba0402a35ac618569c88a94d03a848383c7621d3a31a1a3304e05210a685042d62cc95],[0x455082290c805304029848d314208a6a200a41034c50822900a8d544554c8029040d314208a402a3402d44551c8c102441185220840950441304610880d504093046101241188050a44500a2084402b140288231688111849100a8900ac500a408c4028222928802904028a4c52648d00a9108204844e301,0x21143082402a2404b1402c64049640a9020d01242a52015128c8b22041a8a92a1a82a4108a0141520a322ca340a90a0548a628bce951f19a079d5347f98879d5347f98270280542a2a4a86a0a90519164520140910722014091066203409104618880518409105620148130511314b12a805084614a402a2,0x480b8902202f040480a22863810120886248c840886228805489a3610054082248ca6a2121048848d00b2900ac5105210a68500b1900a9501a5901a35042190821501b1501a991025510a3900b51012b164402c4402a4402cc402b44109823084402982429442088a6280990805948c40142288805489c68,0x2034069040548209165911553146404ac404a6404c4404882910123901a0486404b4404882310c2048821101271012089464241404a420ab0a414649916591344b124531064710e404a42510823103220c440488201702a2b82b0846520445124549012310138500ad100b0d01240c14015027101240d140,0x4d14049c4068125198804885813049915439012c0904048226100b8900ad1102c094440d140480bc1012c09c622064048448d34404e251901a1884108a328106208f0440a0a7110242a0ad0944024822886208e040488260e44048c220cc440882308a31186860412414c4d1054b106511244110c4511c6c,0x1e08091140d2443100a11264d11c451c0805024c131402812413447100a5100bc1c8805214b11c4190c451244208471203409225c162404a4404882310139101255012308821101260b440681271102609460a2058105491012313447101240844049025100a04e468a0340960461624d10120890402f040,0xb02e8104a328a98404e1404c9404e8422031049040691236b20570c83b2a1c46cc43bac24674c0ba0412114651561525684e201485244110c6920620614c0549110802b046232a9e46cc83bedaa778c0ba04dae895c340ecaa791b320ed2c813bb02e21088118c818134558552525684a201485244510c41,0x10a29054821c8050a43200a4148809012411881882a41455a2034090c742034090c70a034090c64a084290c6320247d944bd9a077d944bd988779840ad5817049051910a678fc340f1aa893d320f2ae997e302e0910b041491a668fd320f1a668fd310f430919f],[0x460202ab082420b02110220a9220a4622a9630104280b4402502809c410883910c2209c33105282a02c0ac25104230882228a311042189c238b4258d461a00a6299061c63302448323884118962104810880d106224048128805206a201441c880d405a2034114c805105814898a6418710e1306f60c1d0b,0x4408cc712045817040894404ac420a4404883110239110351948410a4068c4208620901a04882110135101a04b440681271012550125182809054910c4116453114404c468a0244508a290131108a8883402d440488291012208c404882b101222852208c21101210b440490271012088625501230852709,0x2c88fb302e8110811708215881813455914c4a2024110c742024911c451c28090c4d11c4519284210c61104451462203431444d100a7104251082b1a4809044314c4b1344711470208431344e11c4b100b8100ba1a8829244310445144782225810c41114511646c20449158408944b10223101210c4408d,0x2b0305303163573be9fcc83d73be9fcc43cf1b67f4c13cf1b67f4c0b8440c1cc04830631c602444910302b0440c18ec20220c14c808306301821c4404832638680d06491144110c511064a6f640c0543120a2a2a8049040491404b84220843168881244e202421c8809106620eb2a15cb20f0bac1deb08ed,0xf220c10c049ece18a27b236024417b246025ecd18330b0f646c12089ecb18a2024417b24600a117b3460cd0c3edae7e4c83b6ba65dcc43b8c2865ec1384439345910138106016388090661602411064960242904419a180c10c0c14e2201a4118585525256858101311465c1060c60244118451064c6030,0x60a6f648d9120dec183ac78102218b0306f60c1d530a27b2c67b236045ecc58117b2a605431045ece18f646cf670c11c085138561605ecd1841144e131561445817b2463d91b3d923144f67],[0x18734e620694c171a68282a0b8e30682e26c0918811484520140d04429154390d4b11c4150c45d4182e34c2985f4cbc9887a676d3e98479635cfd982785f4cbc981780805485052a4028c402ca404854029a4028e4028a45d518068ba830a409988282e061c9b0181b05d41818538a81a1b78206d0281483,0x5f4c43b96eacdca611e99db2fa609e99db2fa605e020614c171369081a0ba8b1485c5992c6993b380f4ceb9bd310f5d2c9fe302e090a455134353440d0545d41809171c60ba830cadadf4fe701e58d72f6621e99db3fa609e58d72f6605c220222ea0e320222ea0c720152141415175460242ea0c620a0b8,0x518421a880550521404e2015014144d54402c85911c811605051c56d6c9bf310ed9a222d1d847a67549e9827ae95cbf1817808190541190834505c0c3d26034110ba930b8e30ba8b05d458c5250222eb0c171371900a2ea8c171c608c1406b020c82a188222ea0c171360c82a171c6188232105c45d33b6,0x676cbe9827a676cbe9817808181b00a0a9523491a8e164fd18878e164fd182785f5cdc9817089f755370621e795d578611e17d73f2609df755370605e024056d6ea7f380f4cec9fd310f3cab9bc304f2c6a97b302e112680540562014692c4a9064150464201421487220640964469344b12a4150460a054,0xa190e40664c0646c0626c0616c0654c0634c51419050ba830bac36574cba988775b5cfb98476574cba981703026340a0522c282e061c9b0640664c282e061cd36574cba988785f6d3c984785f6d3c98276574cba9817808190b8e30542ea2c2eb0d2100a088ba8305c55c154ced97d310ec9824290d847a,0x10ef30a197b04e11028f64af0a1c8057b2a6035ec8d8090a40484515545ec858050a50503459344990e55106402845eca18f650cf642cf654c7b21781615a1188f670cf642cf650f220240550581485a17b2c606c4c0a0b344f2c78981710872030b6064505c0c3936415211417030e698cae7935310e050,0xa8222902385043190228d0135100a048238100c0dc540d0dbc14302218aa2026c20264a036320356204782046920242904682024110c4b18280a82411c2809304a1988110c4b17061a02a0903431046420341905431047423d963064310465200982a840d064150c411c0bc3d818754c3d92b088eae99773,0xa82e0a92027420260a86b0a04702f0f6061d1b20a0c80c2d819031a60185b019930640634e42018d38c905505210303605431605414840c2981905411584310234161408c94028238102a08c140a8232103026024290348d164d1064068121101299012710123900a048c40303751035260240d324048c40,0x872201421a8805024e2015414846201411988a0b8187a4d69e02b0600c6980c0dbc1831ec85b42c08185300aa0a0a01702017420170af0f6061d931ec99862045ece1b82450307e6c43c0f2c6e2c0b84431505ecc181105431415417b216014f642c31c08f64ccf642c11d08f642c11c28181301514a4ab0,0x45eca18f642f420604c7b216088627b3467b2c606c4da050298600c29815030368c8a0c302a908a0b818734c171160686c032a6031a60c80c0d80c298a28305d41862171c60694c0886290a0a9881117586034050c41117506054310445d458181300a90a0a34a2a4696226821068051c80508461088050,0x1ec8d9ec858181368140a458310b8e3414048bac35d5a787b0316c987b2160614c02a42f0f6061d9301a18a42f0f6061d531ec859ecd19ecb1b82c28150c521],[0x4a0c80d8980cc980ca980c69c040aa8290a020606c02a82688d2068e20694c608c103602016628a81a1b2020a81ac8aa2989a23881a9300a08b0238b82988c104602014119080505411b080506415046821ac4dd04150464a01501486a20604dfde01c3a866462604c4a48c0c4c2343230181c1a04028ccb,0x342bf4e03b6d2a5dcd03aeb223d4c43c713a9ecc238181302010a05890830585c043956165060804141b0041582010586df9e0183a866048c030182cc30281c0c38b60181b30280818137820601a11605c15250d00a0881a38c05fe09e1ec281c0c7aa601953019930189b0185b0320634c0281b1300616d,0x202818100858b61214f]]
theorem XS:FBO X6 0 20:=Tz ot c10
lemma k19:KOk Bu Gu Pu [(32,[1,4,5,6,34],[0x10a2e1d00e8e807274038ba01b1d00d4e806971401338a0095c50046e805c7402d3a0165c5002ce28015714009b920039c9001ae4800b7],78),(33,[1,4,5,6,34],[0x3842870c3d4e14138f0a09a769960c38d08122cb0162cb2e087559c6204143081112db5960ece543c0191e00c4f0061747261e00a8f005278028bc0131e0094f00497b321063bd9908319ecc8418af66420c37],0),(66,[1,4,5,6,34],[0xb2562a5182b060af84184330c881a19488ca992219638d05aa9610b454aab146982b10d034e532308c81ba206986449171194301b4255588190d034338206cc81b2a551a81a2ab184c30354309c6c38148ec38144e32174c0947a6048ba8b861d274a08c7a504539871a40c38409125e0111f0084f80417,0xd4e30a30d885287a250e187a983a960b4d219c14a964aa3558b44e23a861a36a116206892821d720c0eb18a8754c3a96855c8b0322a8d68b8592c55882b520ad281c6b450ac28355cd32e718645170c3b4c5685730c0cae45854b9c62a4d259a12a8e46ad1589c485190334d422ab987821836068652c0cb,0x30f02164914395320c3c0868df4a821d420c9a54207a650838e2186119143861cb60cd3850a21420e4281612c8e4498a207498a1071c430e39e08c3321053081da52021d420c7250b378c38518461c11906419852a864d90a190c5b06a2d8538864334c750c714e087414096532711846419324d219612a8,0x96609c6204143081112d80810b4b60819a610217169186494584085a6c20a18408596d7a460eb3c2878b1120748833060a431961140116cb061c10f4b010ac650d8402b0c408286c0334e841aa6a186c528598a2e18769e08b9665cd30d9328545c30e9b142a1863206684190d9306a9819a6572850e5538,0xe10650d8302b0c1d43143861ea6d32c1871a10245],131072),(355,[1,4,5,6,34],[0x8334c0d533d0861da70a3a8642b054218a6a11628b861da6c106218a6a150c31910ab91618a1542b9862e41e28a15c8bc10c1b0614c6118631143161182b0614e04182be1034654c18430c29c88c215068c5225119432114c290614e26130c4160986118c7a10c394d44642d45c30e9330e348187081224b,0x1c269960c38d08122cb30605618910660c14860810a0b1961140116cb1020a1b145c30ed360814a12054218a6a1062e61b0c0423aca040b8609850e187a99020d9306a9],0),(227,[1,4,5,6,34],[0xa1c30f5369960c38d08122cb30442ae45b04314c0cd090aa10c1b284364c8518b054218a6508c4354d430c194b4888161488c31830a7c2148ca988a31288c858c23094865223098944650d45c30e9330e348187081224b],3735552),(36,[1,4,5,6,34],[0xe130605618c18290c021020a1b019436100ac370860984085058a116050141836a106204150c1b204314d420c04053054202e14480b0a02984a231815170c3a4c5ca3045722c3108a85730c5c8be11722c2382088c58202c4b852202d08052108c0908c611855c830c1330e348187081224b],0),(37,[1,4,5,6,34],[0x81050d98302b0c60c148628419871a40c38409125804045720cd40a1c316530810a0b],0),(38,[1,4,5,6,34],[0xc1815863060a431420cc38d2061c204892c2041436010d40a1c316530810a0b],66),(165,[1,4,5,6,34],[0x1021417421020a1b48c303a86088650c304c204282c042b40881050da441983052181836c11722c115cc36086099421430c320b0240860d81a810c53014223160a05421826a1060c058050908a44a23086024602e0411048c858820918844650d45c30e9330e348187081224b],112)]:=⟨ou,by decide+kernel⟩
lemma k20:KOk Bv Gv Pv [(32,[1,4,5,8,9,34],[0x4e9de18845b967042e2c2aad881aa6f4d0842d9b70391dc0e2770385c85958770351dc0d2770345dc0cc770329dc0c9740820919d020824574082090dc859387702d1dc0b27702c5dc0ac7702a9dc0a9740820899d020822574082088dd409c750269d40997150059c54015715004dd4c8e753235d4c8b7,0x19416c76505a9c842e962a0636395031a9ca818d2fc128e05d1d4702e4e8194707210bc59c1420b8d9c11ad31b9351c09e3a8e],4),(33,[1,4,5,8,9,34],[0x816477200b0b9b133126200b13e159192c09a3b4c3469ccc9ace0551d6702a4ec40d31759c68cb9085a2f18ee07c63b21d4ec38753b0b1d4ec2a753b0a5d8a1c19a0f60623d8184f6060bc1960f60523d8144f6050ba3d18780251e0092780245e408c790229e40897921081de8842067a210815e8842037,0x13475980993a8a3465c4c5a10526c1256e084c5c14348ddc81a16e84161b18ab08c8d9ea0238ed40119731a66a00a63a8a0525cd298c5584c4d9c171c691bbd0342dcd0d90d4c4714648cd862b0268ef48131759468d3999359c0b23ace0589c842e161a1b189b18d3191b0c698d0d8c8d8c4df042c8e2f4,0x70292e694c70ac3040d0b732363436412b416392c0aa3b8e3469cd49acc3545dc90268ee48132759868cbbc3108b62d4ec70753b191d4ec62753b185f0235204d1da90264e42158b4a9a62ed4811c76a408d3908532ce084c5acc342dd082a36704664d670298eb3814a7210b25824ac292c1257c1382e48,0x8240b23bd00585cd899054d046d04ad04cd058c4c92a9896238c160591da802c4f0c2e0902a8ee38d1a73527b06a8be38268f8e0993db1a32ef0c422d8b1082936210526d8e18694c634c626d670258eb3812a77862116a58292c22ac232c28ade81a86ee38d0b7a6842168d9611953189b18d33500531d8,0x61615c90238e634cc2bd204b1dc80252e654c70ac2c2bd0342dcc8d8b11c5857200a63b4e0525cd298d0d899465a1343612c3852c2626cc2b920471cc69a4b0258ef40129732a638561820685b991b30b15014c771c0a4b9a532c3248d2378a0685b9a1be0925254b14650d4c4714542ca6238a328a96361,0x526d8e18634c626c31a63136c70f5c1647d70589c842e16584694c626c634c31a6313634a7c12c2e0b500591d4502c2e6c4f5c12c7d704a9de18845a96584292c22ac232c28ac149611561457c12328a9c2b08e158782c3816475140b138b0b9ac6a1bfb9a16f4d0842d1b24a8cb42686c2c2961614c4d9,0x3c2210bc590828b6d09a1e09c1b70471edc11a7210a65822adc1420a4d9612c3c1382d4811c76a408d3908532ce0a1],0),(36,[1,4,5,8,9,34],[0xa842089040a822e100ac08226100a08d84108839102ac0823c10234500a08d04c098644c01181b022604c02402624e0a08401014150341082419144310821135261913104322601064009853042606c0a98208882604c0081228822624e02400b4183402b04400c08b200594480168246413426f0c422d0b,0xc98c49908502c8910ec5a0c1a10506e02c40c32261088a1913028051913208644c321913704664c3227810c89c840201401104d8982110581484613036181b004644e8a01581114c1104d130a6104011913181ba081080461604190a4d100251624028c5450034100391312600a2104581022c1344089440,0x4624d4118531b13210a45841088b185215050828360c0d90408882604c302761022209853042089993011302630a6b08cc9e04044c09b02044c29c840484208b029080928862624c22822608826c4c30363126302741210a05805004614c624c02822604c08981b210b458f0c422d8b108522c63066930e,0x45104208905c149c330261893181318535158c58416052102a08882604c068120898936286045250c41145270d262cd8981918936040a981b5143037410a210822604ca0822614c069b1363060246104404e043134404945895254564404d05516930ec9908502c20884289690842158b60402006820cc98,0x801504624c614c842916c50c332620942c0a82104425042131261993604624d4100821004d898208054130a6408b004d49bc3108b62c10561116c08585a0d1820af82082b8386104222e0a1820ac2160541830612421605418910ec5a10506c208c29b0ae0841c0841145813126604624d8e18156041118,0x1a170461604c70c4108420842c60c6386312618936306c0908522c3126630642170b0c2988231261853630642144b084289618531893210a45842148bc08624c842e16108512d411085c2d8c180410882210b85841210a25842144b50442170b0],0),(37,[1,4,5,8,9,34],[0x291604242148b00801a0821105082836004842d161040898130c09e052101202482624d451b131a93504842816108502e02c40c108c8980a01482104644c02004d8980130a60844130360068a00a01084c49805006820858130411105413026104013526004604e0a01401181380801400b3426f0c422d0b,0x2210b85842148b6286108522c42144b5058c1981504624de18845b160130220821111682860860c1a2443b1684141b0c0d821208c29b02104c4982111581044413026181b18136386084604d8c5841181318936286045250c41362608581504624c089813630608409504116930ec9908502c1088208484,0x685c131c318441082c60c2088420e04108c498216306c0908522c2098c19085c2c31262098c1908512c128c29b02185320a82108213126f0c422d8b0c210882104842896210b458211893210a45b1430821893210a45b],34)]:=⟨ov,by decide+kernel⟩
def Wn:=C Bv 2 [1,4,5,8,9,34] 2
def S10:=(O 1 4 [0,11] (O 2 4 [0,11] (O 4 4 [0,11] (O 8 4 [3,9] (O 32 4 [3,11] (O 64 4 [3,11] (N 33 [1,2,6,8,7] (O 9 5 [3,7,15] (O 34 5 [0,7,15] (O 36 5 [0,7,15] (O 65 5 [3,11,19] (N 66 [3] (J 0) (N 67 [3] (J 1) (N 82 [3] (J 2) (I 70 (J 3) (I 80 (J 4) (N 18 [3] (J 5) (N 3 [3] (J 6) (J 7)))))))))))) (N 35 [2,4,8,6,10] (N 69 [1] (J 8) (N 81 [1] (J 9) (I 80 (J 10) (I 67 (J 11) (J 12))))) (N 49 [1,2,6,8,7] (N 3 [3] (I 84 (J 13) (I 80 (J 14) (J 15))) (N 82 [3] (J 16) (N 10 [3] (J 17) (N 98 [3] (J 18) (J 19))))) (N 41 [1,2,6,8,7] (J 20) (J 21)))))))))))
abbrev t10:=LC Wn Gv Pv S10 0 0
lemma c11:t10 0 12:=Tc ov [[0x26640cbe89032cc180449cc180445ca22846119450c0224e48a0222e5130219033d10c2998056408b402b41333880d184650c215142328a143541ca1434c1cc2034610ae043082aa902a508c219834601a40c1aa0e48e1a30f060f2212406e44692643086406aa60b1890c02b413318906690288f240d0a7,0x2e08c3068c805683268316312015a0c5a0c9944805683267109ac8aa2069a20c82a2886278e1aa0e8101a30f060c9090243541cd1834c1cc24aa2a34aa610218370a80d68ba21872203461a88c19880d30562184e2184629140228e8100224f022c0684d0348183541c91c3461e0c180d284658256034a18,0x4193418b7040cb8300ac815680566114],[0x40cc947121aa0e50a1a60e61092308e22c833210a861524c9163008a39428088b9246901b8901a3086406ca428aa7221854932458c0228e50a0222e494a4991a424864a958840c0224e45154150645134406d4531644b11481548419163008a39630088b9240ce240ac640aa64069a5292a583c0429c6241,0x480d5480de880d8c80d125a2034614c8a11852a4840d164d134861124c9a8861124c93880d1858930801127245011172880d484c9125192a4699885900228e40a0222e4958450c1aa0e48a1a60e6101b250e280451ca180445c922cc862a184515447109228c8428ca428aa422cc432034a1584691945086,0x1a60e6101a908c2c88150c80d588616887921aa0e60c1a30ec106452187a228461a88193053300429c623046138a24808a392406a426892a3480da880d8a80d9880d3880d1872206461a173c760dc2a03461065621e486a8398306983984d1054520354150c010a718a04008a39e3808939143080d9080d9,0x553140d704068a4148646485206832c1032e09821501a909a2149340cb82609e4808538c490862068520c82ad30d307a080d3054106549324e218306983d040d0a551054313280d305c10a549195c9142c91420aa2406983d04a230415344310655118251348310a40d14419054f203541dc7],[0x882290589644208c40c7020d928c0905454c525224869839e3868c3d041888a06c842a03521195292a52501ab10839102a90e2490a0386a83a03868c3b0432104c1385251953101b9101ab1203808a3a03808939150240431c5230406702c49040c9820d01aa085460b12929523101a20a04008638a63271,0x80d3291240451cf1c0449c8a034494070d5074480d1876080d0a38101a22c8406a439101a9901a90e24037032501a22ca40370319242a920a45008538c424a42c48d1c0451cd1c0449c8a12445188451841a60422c85314a428e24508c20d01a90a6406a4294932c48c490862a9208c111406a42c495241c,0x34411846520386a83a65068c3b0662034452c55101a22aa38108bd10839130230b46521914290b123291243541d22834c1cc2186623065220486a83a45868c3b06320540d4848921aa0e9141a60e6101b3101b29c080d48461464652a529c8806904c138452e301127820088b94406a82289a24070d50730,0xc230461068610355101ad174406855312c406e4482034c111453190a120aa216206a83dcba04b50ec154702037a2034411480d3460d50744a0d3073080d104c1c894128429185a2142412c46902ad108b511a306a839e406983987120540ae045502a0d01bd1183510839128230b440688a6880da8e26420,0x6b0329208413044514d442488ac88d2328450a9810690203541cf1c34c1cc2184156243083406ac430e443082a32a4a05652055620546106e04c0b22a92080d104456446514b44a0982068f183541d01c34c1cc23280d1480d386011272284503415624a90a48331092229a22a8450a8d183541cf2034c1c,0x5081a95c0861284690c20d0c3892a5320344508a06e0406a5406c9406964991480d605891949908a2908a06c84c0c942a1240d0a562410922282a48415624a9209211841a1044514f44a09823085238601127229210342920e442488ac482a0541a3860d5074490d307309810359101b8901b2530222c840,0x73870d18760a4a328152680d4c80d2c962054f1c0449c8a2909ac28aa116421364a116521852a13521167121152115552384a11852906840a1aa0e40a1a60e6108143541c81434c1cc389164229541440d507a132076a1c7183461d822c8ab2108a2cb122ac942289a2aca426a422aaa47094230a520d09a,0x9a90b12284921256212532124ca6186a83b4e34c1cc2284612c941184aa0c381484992c5860224e45182a08c232854c09c24c8d232815908e183541d02034c1cc20d0923460d50],[0x4c22982606ce38d50771c69839845088a068c2664c3088aa0982f4010c730a6064664c0a981b1a5301a654c06a426c4c06b06808639853208c10540a835d10822901a710827900214e3100d20b44c69981644a901b8974406b448121aa0e8121a60e6101a71082311829120218e294080114779c088b9893,0x3136a0b8269c6a83b046e],[0x64713454300451e080222e624c134823492a388b22a9a20c8a2c89b130492088a26832688a238b22b9c0218e614c508a2148ca14432064e2144d2064496880ce06520324158981144d1154199098106521a5a40a645c2a02a411241954e010a71884512429066620c449484190a722606da61a60ee38d187,0x194824c8dc98b2104c8d82c904cc984132a628521313610445344c69841114d298626d8119930c85948495194550],[0x5810640d9080d6041994f4406a4260922834c1cc23c7010c714861b080d94861065212a4294a4839101a30a423292a948610c8610a80de89816880d48415148415888961a30ec13880d187221055300429c634501a20b2270912034c1cc203501c0431c5218415e080d1071203461a2cc5e90228ed381117,0x650200429c638901a308610341520815036c21853201a0a904520346192815184290364218441588151840d19459948a118429484320344130522c0429c6203521284610c5a38101a60b821480db080d30415c080d307123064a185810364218581949c4068c2b095203712104620551280431c526064a05,0x6942411949971406aa430d84068c3850c20682bc101a30b82190c183461d820c80de09322901a30b820cc940698220ac406b82508c214b440a8c2e0815148610680d5880d185a2034610cc843081ac280de080d68962034332901a30882609c29160214e3101a30ac2929321864218432185a2105620],[0x845c4841588a1184320646191c3ca645c2a0c24134459154b10521903374c99ac8b8570202b8132429067a2105810658950d010a718815605890642998815184c906429c8d8428419208aa688e1c34c1cc206677cf259170a819184d10564248461388411850280429c6202a4148461c880ae04291866345,0x32b1242a9a0214e313032902a90e44c0cc5c71a60e61029c08b1c34c1cc2e89320a52a0a4e2053816884192829184d10c819186470e259170a80a904615880a9041944b010a7188411841994829184d10c4b1052190336ca918c8b856420a4610652162529c88151842906663c10c2e08aa94829c282938,0x4c51c46902ae102b290320a9940c94214d10265b0ae45c0815604c111662054c102b81745c97140ce44c0cefa65b0ae453026930265908a10542902b851420c82b8102bd102a50e24c0c9414b020c82b2130290ac40ab0290ae7808538c40ab020cca40ab020ccc45083290e44820a419604d10552530321,0x320a88ac48d20a419055820a419055c2054c1948190c41532815307a244d1c4b0ae4506792064310578a06445307224ec244b50ec132],[0x92981688c138819e8a6258b22417a4086398530c2228dc98ca984532366042cc84991b93191b195320832a641191b0c841184593441933262852134468c1a60e613136114413441934a61144116419155917440cb4531362608a90904556247106591344c698413244d255312c471644d14cb010c730a745,0x5624b190981114991665211581585210c819605214a525625a2064c162561484e208a41065214a525e881930441495614a7220644111662634cc0a423081922845c8981689813884d115210678260445066c21158148419345e71a30ec10323098222f440cb02229833108ae083211419c09320658190819,0xc4d942332619c085560521264d1064b132a64130260832e089a7186983985d1032c091422b024a9a20c904d2984d06521704d103290b04608336103290bd034c1cc2064c19886106521644d12284d254591556148419344b1644826c4c70482c2841b0932192415870210712105819284510562105811145,0x4f0219932c8664cc10c861604c4dc84268c2229322c8aa1344590ba2115a2114326e4cb08c4d859189be0932164626f0a154a132367064a185c1614d13326284664d6149432704646c626c228c2664c1990855584d148419372675e82360ea1584626c6e4c990aa646c372632363137210aa309a29099930,0x646d82e09661a60e610c8dc9432365938232a6323645142228c26899930c8d8c2b08654c646c8a2c861114cc9e04228c2e0ac211461c0989b0c2c0b82184cc98626ec2190c8d8c2184cc98664c8a191b11466],[0x99946316605851948183541d8c19216258508a1501a9082a8c8b38101a996286318b02ac50cc54c3211451064d101b914c4b150d010c760a6301b09250e1aa0ec60d2240431d2240429c4a41180d8f280451ce240445d84980d1152300431d0280425d829806904256266305331a30cb8e3541dc71a60e61,0x3053301b70406b1c371406942c62c06942e0832f4811476126305371808a3b8c0449c8a034490547100228e68e0224e4508a3101aa180218e2924480863a2400853894129421969c6a83b183180d806e04d203541d8c180d504e240451cb180445d84],[0x81aa0e7941a60e6101a30964035422440d5073480d3073080d2ce14508a26903250a05008a39830088b9240c81a03692035c22850d5073890d3073080d144d21853300451cd180445c9203449384b3810e280451ca180445c92064c183541d8216306a83b05c22440d5073ca0d30730819184e12cc364215,0x218e70c0214e258680d032509040c9c40c964209a4808638a420962808639a3808538941884a14832e1019208a329142288326901a5094a44a011473460111724994064821489331032068523490280451cc180445c9325c080d604d14a4990921901b0d2c50d50740a0d30730860c1aa0ec152406b8448,0x429de90212e31032148b140431cd1c0429c4a064a12c50d5076084909419708c11465206429142808639838085389424b8420ca70a1a306a83b0451344d2284491a286a83b04ca304291246998858a1aa0ec11a4008639630084b8a4691a4008a39630088b9264a16286a83b047120218e291a52519468a,0x642034c1128c118712095814843230521348c118652104c14090109714bd20449d860222e5100dc0b0a3060d5073880d3073080d9281986822e058506495265892a4820324118525a480d019c09052501b0d01aa501aa96480d3044194819305213c801147346011172480d304d1434a90832101b2934bd2,0x34c11349501a68c0222e4901b0d744037022ca1a0c92a589324101a20e44208c35101a20cc42089298a1ad169c084b8a42284a2c92a037120361a035520353203461a4806e042564861284d180445c9230521348492846901b210c8069042506652104c1435313c801097149c406b02648ca8680d5480d60,0x40d18430992a490420894069a28088b926621140d00dc0c84484822508b0d302953029901bd1082b10839101ac0d442281ad108331348a1124c0a42410839104a90b84069a386a839e48698398412b0230d44248833118290aa26904a90a6294a1a34f442494294a1a4090d5073870d3073080d34b44320,0x2c8aca0445c9203521092a101ab101aa901bd101a24d44068c29901a908aa035215080d589215480de880d126a21853381142a889143541ca1834c1cc30d0c224a9254b12d1242249322a80da880d68a1a58894037024c8b21296268aa32901a309524c94a485420344a950c26489212b12949539120822e,0x284455450d08ad108a95142593029083406a8a3541d871a60e6130230a1a5508a648aa26aa268a1a2501a228c2948b20344b910c290aa2129a],[0x358161499194508c445580d28551344691c406e4531142317a408a3b900449c44580690449134556450d28680893a250088b9453148b010c78240853884b00d5084ac88250c8250670a124ca0a431094991941286702604499880d60429928250358500d509c38104b0d04258664220ada61a60ee38d187,0x4a5858581a098b0b0b094b434820b0b098b1880d10431125648431034511196],[0x69820344c589a145a70218ec3010a71096284513044158212c20ada71a60e61032068a20a88cb04558c2129603449580d119606461105603542c0431d2240429c425904068c2688e234819188610a80d449010c71291240431cf1c0425c52f3811477180893888b]]
lemma c12:t10 12 21:=Tc ov [[0x4068c2c901bc93826901ae09a300863894068c20c82b2101a3082b2502a209a3008639e40084b8a40688329c880d185c1094068c38101a690838901a3082b8508270c0218e8920212e299880d18406e05c902a1902a8120218e2501a30e24c09a4c0ca40aa4500863a040084b8a6a2d3811476180893888b,0x246901b8901a7101a50e1406f4460a660084b8c4e0a8600863a248084b8a4068c25085642284192c471744068322501a30b4450c94068c295032509e50084b8c434419209e4808639a38084b8a40c942069a21894300431d1240425c532101a3083212863290c21294252a4a908570203461614a929406d8,0x26889406b83250c250bd40425c621a4068c3b05c17a40863b4e0425c52184190a43134712034a1094d11830084b8a406ac48140214e7100212e31c2819185c15840ce240cb82a10c38501b250a8a1094c9065891e4008639c38084b8a7a2034617041501ad11e400853a458084b8c47174652064a1034957,0x4a580d11961858110560358114964853280431d42c0429c425d4406942129a2284a2144e1c0425c52184510c80d14652284510a4199080d0952106722064a14854340429d0240425c62094610640ca852949406c842a03415094191a429a880d2842505419988b0b2080d284d1255c901a711420cf040cb8,0xac262e6208ab2840d0b8b01a24ac1157919080d704510c45258a15840688ab01a252c06892b0c206c8413173101a288a4bc08c9145210a3812c5296453148b010c78240853884b04a3083206782e2819705427054a14652064a1c8825184a10670206581988616064a184a106406e064220ac3084c584958,0x8a145819081928581625856080d605213281960521495c2034a160521720698398406a42c283214419c0d84309c294ac29281990f14c09c2b0932084b0c80d94a620364a1446190f0460a42708ca64912834c1cc2034d35110561ca34c1cc2098b508a1e080d1444a580d1445c5861284495861098bc8822,0xd661a60e6101ae0b0a6892a7240853b500425c622ca3461d82688638101ac0ac21494406b82c0862034a32101ac0b8228ca4068a2128520364292a53910a2c08533111963040d08ab01a2c2cd38d3073080d1716604611316034c17a00863bd00429c42580d4842911975103228b0a06451c0ba206792285,0xb610a2c0b0460cc5870218eb3010a710960b0b1443101a24ad3104958585c84068a2292c50a4222ac06a4228bd20431da70214e212f826040d0945901b9101a55025c081b21182d4010a76a0084b8c41281b3130212a42511716084b70410978101a24ac1097310425b032101a908a2188b0b382c08a2292,0x125613160689a092bb08511496034c11156144262c292c22af02034c10c56101a511616092b098b04c5e04069822c2c12564d18222ae42035811459101],[0x328415080ae04e1834c1e820551203541cf1834c1cc329051209620571205652105419084192841347010a740a0109718828904710832102b25015208640a9a380853a050084b8c702a902a50b12183808a39428088b924a1c08153870d3073870d187a094109562504a19281928422e04308540aac64269,0xca9294a1859205461a481518432184d180451cc140445c938104a908b2648610a8153c9011472c50111724981186920558148432a1302c8a92988f1c34c1d1243461e82105627920218e68e0212e290c1834c1e821284190815928515290243541ce1c34c1cc21246158819484314c5250921550e2420862,0xa8c2128ca92815648155292118432054612c601147514088b9240a8c2128cbc90320aa4230d240a8c2128],[0x651a40cb440c9c38084b8a406702a9019c0cc40c8a3293020c8a268a840670224a8700853a668084b8c40a7020c84a5094a32854c08a2688aa04b8150963c0429d5380425c62095810c8192842b2102a508920c94a057123491200431d1200425c5254a539102a9089212b12548d214ac5a51a60f148d187,0x9451064],[0xe614a40aaa40ac940aa940a9a4f280429d1300425c634504a0c82a5494a3460d307308191841590819185210554205461e88156046168815604c180449cc180445ca2144a1186620552118425589211840aa85252a4e2144a1184a544b010a744b010971892128425494a94a40aa940a9e3869839872349,0x808a39628088b9264b91019c084a688d206722064c1434c1cc206461154d1646420338112662064611256203381184e200449cc180445ca260429095211842a064611645564424c840ccc40cb449140224e70c0222e5103230855420544948424a840a9e40084b8a40a9a40aca40aaa4e20544928478c1a6,0x8c3c902a0c9a40a8c26900228e92011172481518449066c2054411855206451164c90c2150a36102a8960228e5080222e495080570241325311c4808a39220088b9240a8936152841284592a4a502a70c1a60e6102a6902a8940228e60a0222e4990815304411c46918652104a12a470c1a60e6102a691e4,0x30ac29294a185421504a0a8c20c942929528140224e60c0222e5103224862688d1834c1cc20644934542105620646150d011274090111728841284610ac840c8a20a8d1834c1cc20545150841548515286144b011472c50111724845144d331c09c10a460c0218e60c0214e254c40ab2428983069839840a,0xd200451d450222e490a230f240a8a224a940a942e09a40a88230e24288c238901147285011172495234e16620941915458c1a60e617440caa40ca940c9c40c9a4808539c50084b8c4128c20cd840c8c224b44208c329019208c3250920c862b08b2064aa948199281968a840c8c224ac2928d2b10520c84a,0x40a8920cac2a908224ca7a2064490c4551c469205808939c48088b9442088a1508228e2422b822882aa1142e08a20ab0a34c1cc202a41184491a562064491848960214e8140212e31225808939e48088b944208540aac70a054a1184196247900228e60a0222e49e8c840a8c212845e08151454210552184,0x815124e240429cd200425c621444958e14410088b925c11540cd847940214e7940212e31032710620ce2420ca40648325032e0892d108100445c92b09a218e1412832e0a05008939830088b94424832e0b12b0a4a0670a155081518429065c91a4b301147490088b924054832502a288920ca840a8c250e2,0x432064610ad840c82a30ac2189a2388011273060111728e2405482308623c90112734701117288e329015208c2c48e23890112734801117288f240429ce200425c63251460222e51184c91a4008a3a480445c92e48d205712056521064ab1032308aab081968a4a06652348011272c60111728819094610a,0xc8c23481968b92065520654a064e2065880224ea30111728819125a90214ee5010971881938425194c28d3073094a1504a308a2388250c902c0429cf280425c62094191842bc10c2288aa3893340429d2300425c6214],[0x115551162808939e48088b94412b02d190825284612a52504a22c87220a4a105228e0420a05008538966210521494691e306a83a240698398562094c1644b1494a904ac0a84e21903228b120670a1172203381033210339103290892a12080c905859484112589528191064a104d154c920429e490212e31,0xa301127811609a40c1aa0e48e1a30f060d054c8208a411451280429e025e442688a308d180445ca238901147598088b92424a42c2a6211652127221164a1355241082288a41148224a65808538960b1825184295452928a0449cb180445ca2187a2094a1544a9182808939a30088b94702604a1185a2094a,0x3289a48426a438108b2520865485860222e4908ac096424a4255083d108224d4420892d1828640cb605050dc60224ee3011172890c2d8108224c143083054ce2104a11432114389142c3811172484112652504aa1044954841e8845a8981688493891200449d01c0445ca304810a7809609b050c6920228e,0x10430a8c0449e04582290455861610426a8c0449e045a055e048117d108232a4a2c8ab054c11482c0a4a5494b068c3088a],[0xc5e80224ed3011172880c904591540cb4c0445c921064a0324152819e8962065a23893280449cf180445ca345032608a2409011473460111724819b08a158521514821064b91302608c2408011273c701117288196054520cc42088ac28aa268b20c9a228b2298962e30d30779c68c3d06090218ef401097,0x24b82114a1585c90648210652032415280c90561c481912561142b08aa2c83241c0819124229420c9040cca70a10445155891642088a26e040648385908196040cb02419280c90581624a5033850332568819605855840cc85253881930441585255880c90561294b108321497a2064c1605212],[0x24610c8411244ad1032608c22481948482b108a28482128b22aba2688320672258b0a34c1dc71a30f4103260a82308e180445c921242506483310492084a0943294819a28411264203241988453860d3073860d187a08411264a71032309420664294a624070d3074890d187a086192c100449da50222e51,0x451854515430aca0445c9230722124612c8a30d187608922504a22892c88b22ac84228c224c942498290a4ab0864c2ac212542155521254a12561128a10968a11425948a1094a51545990825284591564a094a14843206521c89041288a908322841948483d108a248c212521284821],[0x158168845604b2115811244a114a11545951422a8b811438508ac0b4424b026889412cc482094c112461142c090432114c11042558841114591544d34425065851a60ee38d187a094111422942a29042089420867a21058106470c1a60e70c1a30f410834538819605410940cd16080224ee301117289a53,0x6044a7042504b8104b8504ac0c8424c94b1208c1105c172412d843211441124550822508219a2845104610654503225688411242549412867a21044d34425065a61a60ef40d187a081960521615451e3869839e3868c3d04e206581485418200893b4a0445ca2654c26892228491170212445a28491170a1,0x84e10abc1294713442504ae0a8430e14128c34504a309421904a0c942f38d3078a468c3d0412a820c9a3250c2a084a68a8a0943238c840ca8290943d10c21294259469839e4868c3d0412943210c32504aa0864a0f440ca8271032a0b4702f481147594088b989308ac0892c29819084558845929812c849,0x1646e4e424108270a42b0864208c2106422844a094b2e8825688250c99930c20c84a0941950819185a20664a064a190989b142b08aaa282590ba20964a09432064e2065a2634f0210521082a10822c8dc9e0420b025099930a1208cc989490b0250989b08ac09421298d31423326195946983b4e3461e821,0x1a28459298d30626c8270b82b08626e8a0946133262cc3461d82634c309b930c8611142504a22999304a50b0aa2825284cc9904128cc99642084a6e4c208cc986430942c2a8a626c2088a129a20c98d390861114251b9304b4504b2504a22c843726509642c84ab082558542094dc98a1a282592825284a5,0x56c252989b08a58482104cc98b2154c4da8413482508aa689b93142704e0a84823136104a13326284dc9894208cc98664d42184c4d8664c4b450dc988a128a15854520841184cc9825284c4de14128cc9a8a2c82528412999320825372609461313725082e0ac22c84a095420970a095a2094e2097a2094a,0x184b0914a5164228c2664c308b2d0ac268561e094a185c1344cc99042a8c2157821],[0x10cca40688260a8315010a7698084b8c406982c2ac292943034c1d0203461e82034c1908c1949c469c68c3b040d01a151e4869839c4068c3d0406c9402b812081b21006e048329e886130406a424101b6101b2924486983a24068c3d0722501b105c101a9141aa0e8101a30f460e62f48114769c088b9893,0x182e0ac2e280d618084b8a460e1406b82190252082a0541a0ce0469c68c3b040d01b610671205581035899280d304415880d604190560a1a60ee40d187a0825704156143870d5073c80d1876082b8101520e2420ac430b020d0c2c0866421e486a83b4e3461d820a8150680dc281282a4103702035620358,0xc422b03210320ab0290984067020aa42c8f040ab82c081590a4a5895340429d1240425c6205652487220566241082c08324cc010a73c801097188410a81598815c8d840ca42c0b120642a0556250c010a73860109718815c881598b8c3461d82105210543101520e040acc40ae464b1a60f048d187a0981b,0xac210702097120964a10562094c1116420958194825604c10c841117a209581065e91a60ec30d187a084130541388c110541c8819304419898d3032c08c222b22e88e2116c206662605e61a30ec1032c0a4298a4a588e2c8904114820cc9434c1e081a30f417a40863aca0425cc29815604e1644c09140ac,0x61e8206521184c158460914608329090420bce34c1de71a30f41362606581504f40d50760ba27186a83b8c34c1cc20658122845604b164419209a5303260b82b0819c881992819988193045915561c084130712065818286983b903461e82064c17059103260e0420e2642064c1033817459194989b04a60,0x1953305614945938232a64518222a4a2ce046088a6e4c32a6c09821904ac08654c8a094dc98b2114332104a39468c3b0412e15250c2190326e4c60ac237269283381182c08dc983321182c099532084109420e04129b9304a654c32a6196a06983b0e34]]
lemma c13:t10 21 22:=Tc ov [[0xe222e0a1822ac3170515810c769c0853884b0425e4410961196e08455a8412832e0ac20654220ac44b011473470112711161196104415c8411561096b08212c22ad42084b90819484a110578104a28832065424cd010a73c901097188192842a06449c8819144a1056422c2e0a1aa0ed38d187830684141b,0x469c8ace0451d250224e222c1096e0845585c58212ec2084bc888960228ed3811271116115781052248a2188b0b0c29b020cac206451362620ae0e1820ad8102a2c2c0a88cb0415f041056c0c84308a22e2c16161057610425b021616084b9081948581105641032e0b020aba2c898190bd20451d860224,0x48b6286082b1859102a232c1096c880c9844159040644158212c20ac820545111978102a308152881905451208b0b1a90218ea3010a71096094455829144585981064415f0406702388aae8b220338128830832410a8b8b03218b82e48e2067527298970a815c48190570a057a2094190c47105702015c09,0xb503461e820956134e34c1dc81a30f4116412989bc08f50d50759868c3b1831649306626e4260541484c698255045524c1c85d11c4dc99814849961a60e9141a30f41744719b00863c540425cc2981484a4158412c848121a60e7901a30f4104bd122480853a658084b8c4909c4d89b920451dc90224e421,0x634c30c140431da70212e614c60a423626691010c750b0109730a6410d898c29b4e34c1da71a30f41210b858e4810c77240853884b08ab0425d84f50d3076a068c3d0459468c3b0541c0825305613d034c1de81a30f4116163d43541d661a30f060d8124c18b0b90a10526c12b82b08c4d8626f0a7a86983,0x8114761c088b9893382c08c4da6c0228ef4011173126124d89bd23541d861a30ec60f5c10c7d70429c842896184210a65e04210a65c8431068c3b04210a65e04210a65c8482105881a60eb38d187a0841605aa3d6cc3c84209b93082634cf48d30772068c3d05c90218ee4810a7210a258c158436272104a,0x451f1c1127210a4586c4c450d89b1c31649386634c3726638631a636264118920a4e1989b0829386f48114769c088b98930823136362692c08a3b8e0445cc49b4e3541d861a30ec60c842e16189b0c4db8241082634c18d3208c4de04114826e4ce0b02313631a6c70c2288293866c4ce0b02938638b22e4,0x42f16c70c8208cb08ab7041157070d082936108532c638641210526f02108532c210a65b82410455a10526c20e0760d507b63461d8c19c5164626da13423137c1382634cb0b82313631a6c70c93866e4ce08c4d8626ec2372631a6f50d50761c68c3b1830c4d98e18c698626da71aa0ed38d187630781c70,0x3c2d0b8230861638631c3210bc58634cc70c842996108532dc168431a642178b0842996e088]]
theorem Z0i:FBO Wn 0 0:=Tz ov (Tm (Tm c11 c12) c13)
def Wo:=C Bv 3 [1,4,5,8,9,34] 11
def S11:=(N 33 [1,2,6,8,7] (N 66 [3] (J 0) (N 67 [3] (J 1) (N 82 [3] (J 2) (I 65 (J 3) (J 4))))) (N 35 [2,4,8,6,10] (J 5) (N 49 [1,2,6,8,7] (J 6) (J 7))))
abbrev t11:=LC Wo Gv Pv S11 0 0
lemma c14:t11 0 8:=Tc ov [[0x1064d062c06c04b0255081ae0c1230324882588c02b2015a09198406942488c3068c8056832683163120919c482868246512a26884a094c206862148320a8a24880d88c18309203642128493082a03452a880d304a2504c14880d3880d504c18884918c08b],[0x1bc101a2904a19032908540691231019908194482a06922c104a0951209642068320a80d48d0406912036424890460a82489a448912e088960889a0944035820640da080d4482a034a2035226101a034c203642184a2505221842a03452189140694203642488913080d1280d1484501b41288193046249,0xc509412a440d],[0x68981124c0b044541406a44522244950406b046101a45c884902ac11140a9840a834298c8456054101ac14c901027818080b8440698211702114c2034c190806e0406b060a1900dc088a035120c80d829c40680dc08c20368222806e05823101a035829080d22702035813080d148c11880d01ac11860a51,0x411138111321302490821270261082127022504ae3010170488904a614848a094491146182845305410a80ae04c15044548815504c19881502b814149102a610680d6044541406986a250406e04069146108b05],[0x191b0c8d84ac11826c4c36266104a3626450d898640c8c222999338248a826088a30991303248819448c2626c0c81960922634c4888aa0889608c2606c0692222a8203582309853142035120c922224c268862034521913289893],[0x2d100d608c251c080d1444501b8101b21184c0b046203406e046101b210545101a91a288914445484610c244b0545c8851114c108b8101a610a662604229842a83425064068a406854c094406b447164430a4431a0845224069842506406a4422944068c521c3481d5283421e020358114406984298c9893,0x980d304c69c642280d4484a034893080dc280d187820364a03562114610c86111406b0522034459480d01ac1704911480d224a1185a203461115c101a9101a2906642114c1244e2034a118521247120348901a44b04a101a6101bc108b212880d28406a2406912610a40688b2101a60a44069c4228c2190c,0xa619930c819114d898256044504a610649132260540ae0461244c0d981112c1034069149130a7410c8d8d898c2191b22832064453326313606461504c1114c89861114c6981911541304c2989111541112c1184c0db8a3481e281a10f01282504c898644d82304c0d8606cc260406d04cc980d11541304c2,0x880aa8431112913140a922c1142489170202aa102a9102ac11838130245908190328903206513810540ac840ca47820540aa240ac840ae040aa440a8c6c2064897041508b810c40ac84c0a440ae44c20540ae04612468a606c128c209461c082504b8122825323632a609412e04cc98253136094c6982534,0x92081938889484913081924461a282504a61065212448a6c4c128329092206491c09c206782066c2245a206521c89212440ce04c206521033812448a115819883104a454841288b810649160981032c1a298530320a8194898ac2815c48a12448a0548970815328159881903289032a10549160819114c1c,0x99164204a644cc10c8254844518412a4419332609412a241903261484c4de041283248819c098160819e0889308196048a694c30825448892282504ac1c082560642094c1488c168845304329898d32423092122832114cc98d298c4d8c69819032c12446132274509a6284a48a42e083268819484916081,0x114c18a40823b4a0405cc09812b046104a664c332645189b908c519262a84250cc9a4412c8450922c1104509224512222f0422922613226189b04a644c3226c10c4dc843137c104a3099930c8646c3236b0b042504a610c8dac212914129223098222991304a60ac600823bca0405cc0986104a6099130c8,0xc8d8646d8560ac2191b12961097822c8646d610c8d89412f04c2191b0943237c15858522825285c1114613326094a1704613136],[0xb1880d18430e0406944311116034c114449109606406b040ce04415d0406b822889203682035816088a114c228ac50841c08a12284530861068c11280d3880d01b811849250406b043203406e0406b0452034c18200813bce0405c226062a03406b0406e0406c84a203406e040698449188c1605210a8a8b,0x2581910570d04c59821096064415b8a3481e281a10f0101a034c203542124a206462144521471203451c284994819184a10a861284105649146420346112722034612842501a510932103215c080d125819880d12581a880d14521c3481d5283421e021461a222c1316098bc080d1616098b2880d1156098,0x131628f0406a422880d608b0b0455b8228a420b0b1458228451131781045584c5b82908c1c085116166101ae0a422880d01ac1c088cb01a608c2161613175101a18a423080d2880d18451c0a6203581e080d4845160582a8884b032508a290851c081960582034c130851b081960782186a220ac13166084,0x3103406b0406944068a2262c131660c841156],[0x5451c48491470a0540a925c1145421144998815114491440aa86420545118449c88490640c984a1092510c298542289321c081502b812846102a51a2981284611469205581144a150a0d2074c90d08780819033811440cc840c8c4248540ab0228a843089391302b1a08151240ae040aa840a8a589a8981b,0x89a931820654206782c4b0a0640cb0449c0819032c160642604c1188196064a304e21158168819305620640ce0449a28c19884530722124a11169206449032c103381484a20640cb0449146491a40ef30d087808a112424914253443106451a0845126a2614c24b82064c2064621242a05461124a2055620,0x8611244a115c71a40ef40d0878084558825124c10c819114496886112430915913442506682504c19880cb054138825306060204f34810170881918541289b132055a185b021858181161060d192118430914498286114491282538825988255882518581288491172230412e0432186680204f34010170,0x822389a530aab09c2114c218782c29a2184a21444a0968a14432065c114542094190326128451a08452840cd04519086128412d0412c841914702145415881950662624c508c21848a1953128320640ce04cc98193136064c6981903381144c49c503481e281a10f0118250841228a13085518492124459,0x128420984509142089682284451841288b41332628461504c4d825114a1504c69e043136608c2187021864231a60958133261993a08646088a9084108ac1c0841128250c819688e260445a09953032508c29081918702c2a8a18683248104781c080b9813082508c222861117021044a094326040c98445a,0x3326a1142308626c8a3327850c22284133272508ae09c150b0aa2841332625082e09c122a8a6884a09542634cd0b0a104c20b2612284150841114cc98c4d84131a6199312d0450841308a12284512861114cc9825184451993a08613136504c69c8420a8a508a130861514a1228412844a2c825184459084,0x228cc98626c664c82108664da81a10e810cc98143136228cc9d1420b82514c27048a3136],[0x29834130a6094190544502b8102b2102bc102b6102a90b026102a90b02c102a30b0260d04c0d80d01a45382c101a29624068650102a2280a9158206e0422ca42280d6080dc0c8406a4260845c080d0c80d0ad0406a82609c4c0a82608c406982a080dc0a425101a22a8260e44a036a307313126f0c422d4b,0x5e91a40ed38d087808191140ce04c134a6114c1605213136094c104b8104b21064c698191140ce04c18a40823b4a0405cc098654c610ca991432a62504a22e0422845c084ac104a626c2298d308a694c604c308668210425065c1484610c2c10c24503260d04d8983106521033817040c98490914c0b042,0x892908a205702222e0a1831184a1092212c508c220ac054445c843084258415e040a8c2289422c2c1056a141a40e9921a10f0104258415820ae0a1d060c1a10506c32a67084ae0825309c10ca998425608654c250ca9f05612286130445909c118430b0419536091432a660c870211461604c10c8654c413,0x614c511056c88212c20acc2082be08212c0c882b041598702055c11840a944585820ad81a346a03b8e3421e081819032490540af040a892516240ae15910920a8a38102ac0b4886a03a8586843c9031116084b092222c10978104a2c2c30a6c0882b83861440c882b1841057810c2288b0b20e18415c840a,0x2560412b02624c31274104aa09853ab46a03c103421d88182905249095240c12c9c31441484aa08a3260cd8983136c10c4df0561183410626d82a0e043137158d2077206843c043136e0b032104aa098d304ac0a82614c1282560a826c4c1096a085858212f0290862108512ca2624d8a1908522c084b288,0x1426c4d8c1908512c12b82638631c3109c131c3029270e090208ee381017302631c3c2822ac1156d0985c1094510a3270d85312618d3189b094c70c9386624f020840518130958518d30aa7084ae0825308a2624c189b3084a49c33127410c4d84aa09413127816306095c16045104b270cc0a83260cc298,0xc91a40ec38d0878086c4c610c698d89b043627210c6986c4d8341210b8582c2d8150521420a4db1430c4d8626cc2e0831184c298614d8e1861062614cc70f020c46149c336261b1318539b06a03b0a3421d881861062614d210c230a781052634c148c26c4d8a19c10c4da85210c4d943810c4dd04509853,0x11098130241504420a4da8221630631c36043136a0b183f70411fdc1027210a05841108502d419ac6a03fb9a10ec40c31a618d3e084136261b13308634c6c4d8e18c4d98818626c615046c4d8c19085c2cb08c27042098582304842996108532c30b0702185819084214cb185810c2c1a084214cb108502d,0x342e08c2210a6598e18c70c82420a4d884149bc08c70d8]]
theorem Z0j:FBO Wo 0 0:=Tz ov c14
def Yr:=C Bv 3 [1,4,5,8,9,34] 7
def S12:=(N 33 [1,2,6,8,7] (N 66 [3] (J 0) (N 67 [3] (J 1) (J 2))) (N 49 [1,2,6,8,7] (J 3) (J 4)))
abbrev t12:=LC Yr Gv Pv S12 0 19
lemma c15:t12 0 5:=Tc ov [[0x402b4193418b18480565105212b82308a3048c0a92230c1a3032036420a80d308a203522185388c08b01a034c2c880d1482aa880d0c9a2034a21892288c183],[0x542911291324c502a44944448a3c101a6902a488a24501a48912289840a942488c228924248194482a054a203452c8806e052203462c104a2482590832148190a815124a20672230462064611252341],[0x481cc1c3421e02034c158845604610c80d4840aa24069842982861114c101b414880d504c19880d60461416a211406e0406985056880d01b8111406d0406b0462034611154101a44b072211406b040aa243101a298c80d01ac124422a25053880d3048901a22e04068a4228c460b026101a608c305289a93,0x406a4406984c49c64189b60819308c1362605541304c0d80d504c130a601ac131a611406a841901a613326055c12444502b4102a48b040680d60984713226034a102a89244069843101a2901ad10c89944c49c140680d44845908451484501a6108b2108a29c080d11406c871203406e053211406a24b183,0x4901ac101a45144c2982906406c8415144d89825184068c38106406854d10c406944913227410c2064d89815304c0d941304c298a1184cc9815244611140ad040a8c2c13226034a102a8901a610c406a4422944d13126d28d2077186843c0430a6055413226181b308606c644d8231a603541332611406e0,0x1a2901a1901a22c84069823101a22982911827101a30b47023040aa24252840698406f04035832101a0358230e04a203406e046101b210a45101a91a280d224451446101a30b0545c880d114c101b81185c198989330a908634c626c313721c08626c32184cc981502b81303601b8101a6106415144c498,0x1b0815184456886111662344310a41905406c84916080d18406c8491a29b1301a5081544832034893080dc280d01ac114861032890578203461928c15880d1844501ac148861116521844570406a441990889484a1185a20348918445304620344501ac1484e205406a84069852124712034a102a8911261,0x6c2054a102b8101b210c49160815604c13880d0641501b8101b21244c2604069841501b210c491e0991301a0c922247022448a035813080d01a4501b812458203406e0491e080d304e2694cc08626e423326054c0d84530a6305211849132274502a0c862488152280d1164203489244c205521247821149,0xc2280d5080d3080de0815149a203462664c22b82304c0d80d114c130a6114c6980d115c101a613327210c20c8d8c4da841960ac205445304c0d84531a603461114c130a6064614c60981b90806b0406a840698406c84cc9e040c8190a9220548a1881524445c080d11406e06420558168891605c20349160,0x626c0cb04323631360c9843137850336102a2298230981b0c4db0ab08323037c101a03582e098d30320ab823088a03582614],[0x86138801027388010170880d8c80d4a80d4c981a880d605a21166230562604e2034a118430e04a211406a842901a251885101aa10a406897226a4c068920354212406a8702066a2034b183501cc1c3421d0206406d0462505810a8c14c80d02b4102b8101aa128806d04611272205406e0449589414a9a1b,0x18449304620340698406a85a71a40ec30d087808493056203449184a16882503406c8406892a106415644d10c682114c150662034069240698406a8406c84068c341289b130c2608153036034d8980d304c2980d604cc980d184510a381312719218580d809601b8101a4982860951a035810c94101b810a,0xa6605211840aa84c0d806e04069841901aa101a250c2153025101ad10c4c49d043136189bc0819508cc9819032c130a660461303601b8101a6105406a84513126144c8dbd03481da61a10f01032064920641ab080d125424c849a2819468491842a307220364a0344901aa10564203406e052a03406b04e2,0x34321842a0370a0540d70542035320352a03445704a19080d2846168819034069841501aa101b2134702034c1604e2035c148461285812880d18406b0406e0406c84626052118406a8451a2806b0461605620346160662624c12921c0981508250c8c698d29819033813326064ca98c8d812e04129141930,0x90995303206582e0819908614870211462928e2065a258861a2985304a0cb82064c20646218530a815c280a985c15081511461908190546128521c09811868a606c0c8c2065420ab0a0346190861287021868a646c06942e082aa280d11406a8702115a20352a5880d30462034e2694c1281a034c2037820,0x250c4d865610c4d833c10c4d832189be0a8450e140cc945098d338230942664c12ac2189b0c8626c19508c698193327810c4db82189b508193326064664f03210c4d819c0921508cc9d140c81960819c0819],[0x56084b082b608212c20acc2082b30642084b082be08212c0c882b48410961056c1c09c14845101a6102a28b045858617040aa840a892516240ae14288932102b9102a508a290e04c0cc4445820ac222e1a082b088b6946903b8c3421e02088b6042c2c06982212c0cb0220ae823053318314574d0842d1b,0x4c130a74101a0ab829080d3080d4848a036c20540d4858203406b06826c4c22b82035c160b0ac480d1140348ac1c080d44b0d20769c6843c0406ca406982037032101ac09823101ae080d909216084501b21c08634101aa098271182a080dc0a425101a22a8260e44a036a307313126f0c422d4b04258511,0x1861032455840cf040a8c222981b0c4dac2e08323036c101a0ab823088a6098530320648a114c2981918536081518445304c0de040c8c298614d82114c13036064614c0a981bc0c8430a63036c08606d82e48d2075146843c04068c2c088a03582694ce08626e42189bc0831378160815304c0d80d34a660,0x210a25d04210526f021893210a25bd03481da61a10f012c250a423103a0825144920741312609451504c2983114541362642170b06230b82508491444258222e4270521184a110560c461052212c20af0205461144a14845858212c20ad3283481d2243421e0208ab084b082b04258415c143a0a10506d8c,0x2170b6286704420a4da84b0b825854218451312642148b3825854230a60a451312642144b0842916e0842148b508614c624c842897210624c842916210a65ac20c49908522d42088b420a4d8626c614c624c842896108522c30a642144b90e0490842148b509210842996a1c0822ad082936189b18531893,0x842144b108532c84149b0842897c1108293781303212c290b02094c298212d81312642148b0842916c0b923481d451a10f0104258a20644158c2084b082bc0822ac20ae420552114581111684141b03236260644530a6313605461114c0d8614c606e42181b61c6903a8a3421e0203406984454845131264,0x3220ac28888b420a0d842144b210526c105684141bc0c163501d451a10ec40c308634c19228c4d819114d8981970461114c29825064157040a984054c2453036189b1b131853181b6386185302a606dc91a80ea28d087620602a4502a0d644190c40688b270c8961a80ed38d0879206181b289893210b85,0x678231a6065c16386065c149c330a603261055c149c33036034e0884b01a20ac1057070c10565104158c4c49908522c1853210a258614c842996420a4d842140b638618d3189b31c324e198530425a0e19893210a458511840c8a220ad070c248a29386222d082837810842916210a659082936108512f82,0xc698c29908512c109684149b0614deb0208ef581027210a05f04210a058614c842896c70c0a44258614c191056082b30b82082b838684141b059128c4d8626c320]]
theorem X9:FBO Yr 0 19:=Tz ov c15
lemma k21:KOk Bw Gw Pw [(32,[4,5,10,34],[0x420b9b503475032750317502c7502a750297412677512667512657512637501c7501a750197412577512567512557512537420e7420d7420b7],2228224),(33,[4,5,10,34],[0x709082e6d82842f07842e87630d4c0b8f4c0b4e070930ecf0422d9641874c0e8f4c0e4e070960e42171630a8459308956a607478407270384b07162c830c620999e0b394255714af1c98dda29085a6f8247e089f8217e051f8127e045f00c7c029f0097548877588867588857588837],0),(66,[4,5,10,34],[0xc688560a601b0c89452b68a42169b0c9b0c9bc10c9b19064d930c9b99065a8026398a60c85419064570415a106588025398832a1d105664c1b035a21906454152935004a731346ca2cd455b44590cd056317a00c8ed30929cd13c72617b60547b60527a5249767821168be881fa107c821f8047e009f8017,0x3843ac13186a604c7a604a7210a4b20c31b26314c842e2c112c2c586298326c98856089618a6215d1868414360684ab03458b04ab8d15698131e54129c44b064250ce081b420c],0),(355,[4,5,10,34],[0x60518941cd2c24878120c084f405e0a8ab2868c30d284c23086d166248521b425845a20a7054206b096430e08c81a4a30e8d0563103a2930e094261151054201030981d04422b229201030981d88302061303c10620602238818084e4214162a922191542c6415a1c11498541b03544ba28cd1367821168b,0xb0521aa1112f0422068a5612b258a628c9840da116452255098425308ce0a6442b2852a592a984412aa84c21a251484aa1308c94261094645614162d824698461c110ac0d14acc1112c1509436154414ac2258225868811489705426110ac0d184561744112c10af050a6264984230a4a0427a02c1d30d15,0x5308c84a610c8a82b420a9885225649842519094322a0ad082a63821286419158d094320c8ab082507820490f0212b24c2a11846744c10acc84a610cca965586419b30da21b26830c54b2aca4630a60d83a102c610d0344ab284c230868b160a435422258205c6902309c80427102c8146a84c21a308344a,0x870421508c9b0e4128390a8464de082a90941d861243c0982e40111e90105cc13284c2326c25308c9bc119066643104c0e938921e0830840a304e0c3128c305984a61326c820c64d8cc283a26b09544aa1186146119689b263084a61c1184650a6298b2c907684aa31148941dd1284c23268d84ac530b242,0x5319314629867040508ac83144b19364c42b044b044bc109458b0c53608857461a1050d82558454c088f2a084e205822102c102c340d12af050209571a649854218a84c21ad1162c1486a840d50e0889640a60d14acd16498425308c8338a06d0992c55098425308ce084a198d4c8856d14842d3610864d8,0x7598490f041db0223db02139085058609a08308383061946198a642149620c305531303ca9243c106304c055906d1096cc3364cb20da2b30cc53210b8b218111d90109c40b3922607598490f4418102c84b40109d68020b888122259461303a8c2487a20f040908ac83688b161826820d8a590662990418c,0x1d10b04c61b1c981e94921d88320c3392260],0),(36,[4,5,10,34],[0xc280a0c80884c930558221085450a60d80a4280944d93004649cc80a108640421306c0508404c9381005828528a04c5301415288081a4268d83215014841510e0a350a0c854430210a0544c199086540110b04218111004826200a0744c1300412986044340580221a0ac01a28c010870444d1367821168b,0xb8b0840110ad08286c6080a042140a1050db1060cb04c1306c306e0c318a6364c210870421609836108c1b81084d9318a704184210ac2108442b042b81a20c10ae8c318946188582225107a260990850582208808222158021084813820488b4440b00452b022205842215c0b45210b4d80a10b04320200,0x10852598c310b04630c040121],0),(37,[4,5,10,34],[0xc618842e2c42c100908286c4080b106183640c106046883304c84282c050840460d8030208a04c13004d1367821168b],0),(38,[4,5,10,34],[0x10b0402420a1b08402c418306c046098609c106421416108142101408026098d1367821168b],62),(165,[4,5,10,34],[0x3186210b8b608215a1050d842196082a60da0c3084226098d93210a0b108286c2118360a844c131b26421416084282c84421716420a1b81620c211836324d0a183702364c1510b042281304ca0acd1367821168b],52)]:=⟨ow,by decide+kernel⟩
def Ys:=C Bw 3 [4,5,10,34] 7
def S13:=(N 1 [1,2] (J 0) (J 1))
abbrev t13:=LC Ys Gw Pw S13 0 10
lemma c16:t13 0 2:=Tc ow [[0x2918862c206d08523130a846429189854230a846454150cc4862610c8322b0a308c5344a1544830e4434435144a29189854218985423218985421915284c2190645624165586c4a29134225148c43161284c23250984322b0a18a68942a89029a0c391c18b30e93068da07068d907046b887860447860427,0xa36364c346c6c992868d8d930c9b1a36364c958461a118a61b261b264a61508c5319c10941b27820d93c12511661d36459874d92e0d0c186314c830c6614d1128a46218b0a843130a846461508c530c531915055661c29a225148c43161508c2a11928462986454190a83215b30e1704c1b822c34435144a,0xcd655964dacb359564a59665966b2ac94a4625936b2acb2ac9452311922cc3a6c4a1898a6128c5319152843215b30cb26d659acab2cb359564a596659564a52312cab2cab25148c4648b30e9b128c530c5319150642b661e098361b261b264a1a36364c346c6c992b08c342314c364c364c94c2a118a6321,0x10598d93459874d90598d93459874d9286262986c9a2cc3a6c364d1661d364a314c64364c364c9542314c314c660c320b31b268b30e9b20b31b268b30e9b250c4c530d93459874d86c9a2cc3a6c946298c86c9868d8d9325508c530cc187825936b2],[0x225a28c86298629a2a8992782215a1050d81b261b26c28b8206c986c9b0a2e0d080d93a10d930d93a16145c12518a630a846298c8c2a1284641915306c2518a84320c8aa44d13004ab0d8945c1226844561114a48925188523150984643150984611915185442950944b91324c842c2e9c981dd0921d883,0x130a84315088969230a8492a224582c58c4c2a108960b160b16626150844b513444a2918862c2a1052b189854250889692509254448bc118542314c61508c5345084292ca118a68a32128c4c2a10a44a3130a8514a1289650844b45192846298c2314d1544c93284629942314d1445190c4c2a10c4c2a145,0x5611844b42314c6150942225944c93210a8b1082a6c84163621054d9082c6d8421058db0d086c986c9b0a84629908525868d8d930d1b1b264a1a36364c326c68d8d93256106c9b08364d8496846298c2a128444b289926421517820b163130a8422582c582c59898542112d44d1128a462148c585420b163,0xd930d93250d930d932561508c532846298c86c986c99286c9868d8d932561508c530c5319c10c530cc283215428321542e0983608568528821582b0a51c1324ca24d415a8a3344d9e0845a2c84210b8b0842e2d841085c5b0d086c986c9b0a84629908525868d8d930d1b1b264a1a36364c326c68d8d932,0x6c6299085258421716a10d93508c53210a4b630c1b2642171668a42169b0d93459874d8c53210a4b1082a6c841636a10d93508c53210a4b630f04162d5621d565588755989659acab2ac43aaca4622258225d186558875595621d56625956291888960897461e084a314c32830c314c32830f0442b420a1b,0xb2ac43aacc431112d46195621d56310c444b518782128c530ca0c30c530ca0c3c110ad08286c61508c530c531918542314c314c6704314c330a508641915429421906454b30e1704c1b044b06442b4290aa208960c88560c85614a3826499425833415a8a3344d9e0845a2c210b8b345210b4d86c9a2cc3a,0x68a42169b22cc3a6c6299085258421716a10c53210a4b630c68a42169b22cc3a6c6299085258841636a10c53210a4b630f04ab10ea]]
theorem Xa:FBO Ys 0 10:=Tz ow c16
lemma k22:KOk Bx Gx Px [(32,[4,8,9,34],[0xcd7589b543874326743257431674315738c408286102225b19099f84ca7f0eca7e2ea64ce3a964a0df0e8397c5d072f4bb2133a0e5dc70cd320e5f8741cbe2e941ba5d4c99dd9371d94f69dd9355d94f4ddd9335ca1c30e5b5434754327542c7542a7542575423743167430e769960c38d08122cb2103877,0x2506e37653ce7653],54),(33,[4,8,9,34],[0xc314c986ab8787599c70cd3628326c1a3634b14e2b10d53314e2d15886c9ec3743ec3663ec3653a86181a3670943861ea7d2bd0f059f85f1cf61fa5731fa5729d422cc962b87e97a1e0b370bfd2ec3c166d17e94cc7d83ca7fa5c570c1ba5307b6247b6227b6147b6127b606730e348187081224ba210477,0x63886698e2b10d530658c364c8187081174b01aa730dd38f30dd34e926a0408b658408296c728f39c759c909975170c3b4c2042e2c046b1c5a20b16928b0810b4dd3a7838ca1e4833e482be481bb0605618a2e18769942cc1b2670a8b861d362c4db84e102a5ac718b9c60b1658b458ae1597043aaf1d731,0x38471881050c20444b60ea58a1c30e5b1662cb1c650e187a9b4cb061c684091659c264208ce64208ae2041436081058d88286102165b0346c193],0),(355,[4,8,9,34],[0x429020cd30334e14323a8642943861ea60cb0542850c53508b10ab91618a1542b9862e45e28a15c8bc10c1b0614c61182b0506c281b148b68b2562a518630614e04182be1034654c18430c29c88c215068c5225119432114c290614e26130c4160986118c7a10c394d44642d45c30e9330e348187081224b,0x384d32c1871a102459660c0ac31220cc18290c102141632c228022d96204143628b861da6c10294240a84314d420c5cc30c13018a6a18632],0),(227,[4,8,9,34],[0xcd3143861ea68a3897823a860d13224a23148943861ca61021616144293118704392c18704392e4418943861ca60040c38408ba5a8864998824586299030e1022c963291042b0718c142c18822583118704392f0408560a9446291050b19431020a1b4a0d1a074a0d18474a0d18274a0d181748833060a43,0x91618362e458628550ae618629842ae4586298850c5350a8618c80a2e18769c2a845d0a86186418362e618c4314f040a94864613100708aa2b0860d9886298ca88625185186449128c485289488c4a342448c52251c15170c3a4d2834611d2834609c204282c50982a10c930c582a10c532061c204592c00,0x53185c932e51a0385318b92644a45728c8948a15722d01c292c10ac9124410ac0951410ad2230c60e258718c142c3102159628c650d8402b0d2834611c304c204282c304314ca16086498b12658a30d13493502045a2c0215ac618a29144a143128d0acb821d1602159223128acb821d17822041436142b,0x2e618629818a7820c318642c31288ca1a8b861d2661c69030e10244960306d8342b0c50ae618c2a15ca322491448e318a342b9262e499728f04d40a1c316530b94644ae499a8143862ca6214a1c30e5306898a2e187498ea1b0685618c85c8b45018704592c42acb821d160285ac51a03],983040),(36,[4,8,9,34],[0xc8e1110443286c201586182610214162845814c101018a6020c8314e041540860da8418b91608ae6180b820280a22c10160405a104615720c304c01088090844421510108645c23016008242232860c058180b41088c2180a30c70202908861204888124184630304d44642d45c30e9330e348187081224b,0x708040160c0ac3004c18290c20414360],0),(37,[4,8,9,34],[0x408286cc1815863060a431420cc38d2061c204892c020b906182604a0545c30e933470a430810a0b],0),(38,[4,8,9,34],[0x18302b0c60c148628419871a40c384091258408286c021720cd40a1c316530810a0b],66),(165,[4,8,9,34],[0x1021417421020a1b48c303a86088650c304c204282c042b40881050da441983052181836c11722c115cc36086099421430c320b0240860d81a810c53014223160a05421826a1060c058050908a44a23086024602e0411048c858820918844650d45c30e9330e348187081224b],98)]:=⟨ox,by decide+kernel⟩
def WA:=C Bx 2 [4,8,9,34] 2
def S14:=(N 9 [1,2,7,6,8,13,14,12] (N 18 [3,23,20] (J 0) (J 1)) (J 2))
abbrev t14:=LC WA Gx Px S14 0 6
lemma c17:t14 0 3:=Tc ox [[0x86f0b048702e8a22c4e881a7502465176ce1c49075148833130a6790d0ff8b4c94fc728710ec206a660d1da1e354a1221ca4da458ed0ec1e40940f126d22c5687754347627650243a079148b162343be916228bbc8941c83ccc1a3253c6a941c43b081a898953875878543465177d22c490751c18463190b,0xa421bc2c12240b8a8321589d184c31e8430e5b50912a18453035129112c64a784e203887a17d644b707d4586517c3d4490784c35139351515f5140e05c352206fe2d4a53e9882443d0bf669915ff66990df9350e05d1419328142b43ae7101d03c8916240d48a8512a206a248951e10351b458a8af23660c,0x3226471145dd4071129dc3c60e09e16060e05c3532952a8c399132388a2eea038894ee1e30704f0b030702e1a992c9547230d67d23474a779130643770f28482719065c6248950b89883483fe232443c0b882c0b888520cc4d891214865d50a1241f07f669d45e05ce210df9351205c540d46d16328bcae1,0xf961c704e33b9248a2fa8a0702e1a06aa81a6a422dbd0391a1faf30e21ca48531446878121038876c9103827294ca54b2551c8d7f640e05c340d19b3524517ab103907c103542e275e61c43e587221be1661c138c29864ac8581c45176ce1838278171838170dab0e4707a2cc3a07f40e44a7ebcc3887194,0x57b35038170d2132ec4aa0cb935190df5141205c54157133ca467b3524437ab103827892250b0796c4fa8a0904e330b07948afb924886fa8a0702e8a4ae1e5a8bc0b94321bfaa8240b8acc90b058ea2f02e50c86feaa0902e2aaa0c916c6114c0d44a86138ca12846419db526687c28c388729285a6a0894,0xf1b448710e534828740f8206c2c1c3a63c2c1c3a53f68a1c43b0c883230860d98302e68eb0f13279298fda28910e18a606a164d1dc1de58a1241d14fae588e0f0b268ca2ef2c50720f23658898f1b450710ec29de38758799d3464c791b2c488729915119432132dda3d6a2f66a0902e2acc166517d45874,0x2f55a64a7dc943887611505415dc9244a7d4503887610a6c4cb0e4517c2cc3907f54e44a7ed0c3887615885704340d768b32c3ea281c4394cc81a06a2e885214e081a15fd9a74a7e4d44887611911583eac56b0fc9bd294f7728910e6214864191505415c10d71035fb30c98fc9a4710e524503533a60c98,0x2b13862830b659841928833c7a8710ec230c65dea2a1bd5a81c138c91415fc9a94c7d350488761054ea050ab0ed9c40720e8aa20cf08338a30a7222a514ab506707928a3907454a8b58a62d4a8c19241e051a592a8e46b5620710ec222d88820d72c40e41d17070f59961eac40e21ca429d4486887110a58,0x120e21f2929119f0820e09c314f9338e05c3421994aa359346a48a2f3620720ea206b6a083483fa432443c0b88340bc081a19b103599248a2f88a0720ea34a2346745841918852a3c230566288a2a0a82bc2d16286ac4e206ace51545e8c40e41d85442911a2ac2320a0d81a52b8464522c0d158b3119530,0xe8b40e05d140d148c7440d0e62a30e41f0f4150decd30e05d153295648c44c3907ed0c381745d38c3887b2ce4437aa8c382718530c95b24644cea271c0b8696790b08e134698720fb920a86f9818702e8a9564e1882a53d9461c4398895198d24b31131e2a28e11c6419dbcc44c7d38a3887293d229131fb,0xc40d6540d5271c4394b24c40db103694693d882a33b5461c23988403606a074a30e21e4f39119e2e30e11cc532956494ac54aa20a5463428881c44839075108a66eb40e09c64a4929045478a4e38471928c30e11f0a30e09c658898720f569c88cf4618708ea281d24e38872931067252a8d58a96cd5150d,0x40d308cb1830e71a255444aa88680a05d9e71c83a8ddc71c4394ac54a3b430e21f0d30e09ca6ae38e41d4562a5b28c38170d4503724090a05a5592b12cf31145eae28e41d452ac95886a96cd51529e8b40e21d84459937251529f3040e21d86350206e8b84618cc9329c451672233cd461c13e1e61c0b869,0x3d563e81e6a19261de819241c610c22040b1aa2964614c30e6192b3885583248bc523248382845034390710ef590704e30a6186b610c9592a55187338868520d194b0378],[0xf8b0cb0ff8b0c94fc724710e634389b94c2f582ce8af161c702eb9162e658545ccb3136d49929f0a30e21e84320cf2ea240b8abf169da1e048e2129f6d48e21cc5730c290a464f2ce4587ea8c3887290cd0833620cb883288f2845879933884a784e243887a131cd166617e5dc9457b45038175c8bc10c1b,0x2695298ae65853a20ce48b99631e10c714190668f38e05c5419bb5464a7a28e3887310578415c90571429b105463520a8c69415ece0a4c7cbd864a7b3123887a15cc30c2320cb8995a0c94f6414710ec2620ce8833920cd8863520c8c7843498ca869318d064e231c5065627118d286302629a562308c9c5,0x4721ce486704aa355886ae2d17ecc3343fecc32c3f2691c4398da2a1c0bc286298c9389a461191d4328419c13136d51961f0a38e21e85f8b94d0fb6a8cb0f851c710e622c9547235388646382520c832620c94e88320ce08626129b10620ce08629ca868da8458b9565c832e4d832b9c60a8e232b9a60a95,0x219a63a86308642d389a43382b11926961184656271a3d03817850a34f44a1c30f532a4e2308c83366a8cb0f351c710e620ce48334a0c8c78461b10670f19221f1319205e0419d12a54ab13886463820d4e382208ce1ec32c3f2705263d5891c43d089a0cf0b24e4ce4687b20c3907dc8c38875cc32e5993,0xcb60cd3184641846532591c4306098a1c30e5b0669c5881c0bc28818a0a3887614c96472205e819241c710c6a864a070571c839079a883887614c871cf041936206192c1daa19281d420c7250b3a2ca388778c3064dc9a61c0bc28c2064de08c90a190c5b0670f19221f1319205c304c2d1c6d130e05e143,0x710e62d10a6c5730c364c0d930314f040c5306c9b05da45698fda45694f66a8910f42a186549c54ae160a8545c30ed3191556271528316119648335218f0a0419c5469a8b94b0f351c710e62c3d88587c3d884c79a8e388729388526119a11a4d3545587c2d03887a1290a464191498e0a8b861d36143861,0x876982818b60cd306a99c2b35235873150c50324438629a84183150c9032443ae6186098991030691102ea10699820a3887a12c8e418260c5b50c31c545c30ed306b77accd0f4620710eb986310c53c11738cb9a660988d22e419734ce3251c710f420d706ef621a1e4a38e21ca5a93d4d0f8835094f35a0,0x315170c3b4ce973887a106a9ab0729a1e6e62131fa5ce21c314d430c0c5350a85985cc30c530314f140c53e10c542a2e1],[0x61819a6810e2198a0cd31d4b1024102b0b1419a60290241028e218334f04750ca1162a534d0b09c5a2529a4e38250e187a98304da65830e342048b2c597043b2c046b02a5a85630c61597043aac5cc3058b1630ca1597043b2f04e31020a18408896c658450045b2c187043d2c042b19436100ac31020a1b,0x38410214163060a430610c102141624418204282c0810a0b1830521e08ca1b0605]]
theorem Z0v:FBO WA 0 6:=Tz ox c17
def By:Z4w:=⟨5,2,66,[12,12,12,8,8],[7,27,29],[0x4688,0x4650,0x3888,0x3850],2⟩
def Gy:=[7,27,29,31]
def Py:=mP By
def Bz:Z4w:=⟨7,1,32,[5,5,5,3,3,3,3],[7,121,122,124],[0x1ac688,0x1ac681,0x1ac642,0x1ac650,0x1ac611,0x1ac60a,0x1ab881,0x1ab888,0x1ab80a,0x1ab811,0x1ab850,0x1ab842,0x1a3a42,0x1a3a50,0x1a3a11,0x1a3a0a,0x1a3a88,0x1a3a81,0x1a560a,0x1a5611,0x1a5650,0x1a5642,0x1a5681,0x1a5688,0x19d888,0x19d881,0x19d842,0x19d850,0x19d811,0x19d80a,0x19ca50,0x19ca42,0x19ca81,0x19ca88,0x19ca0a,0x19ca11,0xee888,0xee881,0xee842,0xee850,0xee811,0xee80a,0xecc50,0xecc42,0xecc81,0xecc88,0xecc0a,0xecc11,0xe5c88,0xe5c81,0xe5c42,0xe5c50,0xe5c11,0xe5c0a,0xe6a81,0xe6a88,0xe6a0a,0xe6a11,0xe6a50,0xe6a42,0xf580a,0xf5811,0xf5850,0xf5842,0xf5881,0xf5888,0xf4a42,0xf4a50,0xf4a11,0xf4a0a,0xf4a88,0xf4a81,0x11ea42,0x11ea50,0x11ea11,0x11ea0a,0x11ea88,0x11ea81,0x11dc50,0x11dc42,0x11dc81,0x11dc88,0x11dc0a,0x11dc11,0x133a81,0x133a88,0x133a0a,0x133a11,0x133a50,0x133a42,0x135688,0x135681,0x135642,0x135650,0x135611,0x13560a,0x12bc42,0x12bc50,0x12bc11,0x12bc0a,0x12bc88,0x12bc81,0x12e60a,0x12e611,0x12e650,0x12e642,0x12e681,0x12e688,0x15e881,0x15e888,0x15e80a,0x15e811,0x15e850,0x15e842,0x15cc88,0x15cc81,0x15cc42,0x15cc50,0x15cc11,0x15cc0a,0x174650,0x174642,0x174681,0x174688,0x17460a,0x174611,0x173842,0x173850,0x173811,0x17380a,0x173888,0x173881,0x163c0a,0x163c11,0x163c50,0x163c42,0x163c81,0x163c88,0x166642,0x166650,0x166611,0x16660a,0x166688,0x166681],8⟩
def Gz:=[7,121,122,124,127,123,125,126]
def Pz:=mP Bz
def BA:Z4w:=⟨6,1,24,[3,3,3,3,3,3],[7,56],[hx0,hx1,hx6,hx4,hx7,hx8,hx9,hx5,0x2b80a,0x2b811,hx14,0x2b842,0x23a42,0x23a50,0x23a11,0x23a0a,hx10,hx15,hx18,hx19,hx13,hx20,hx2,hx3,0xa11d,0xa12b,0xa0ec,0xa0e5,0xa163,0xa15c,0x852b,0x851d,0x855c,0x8563,0x84e5,0x84ec,0x10363,0x1035c,0x1031d,0x1032b,0x102ec,0x102e5,0x1115c,0x11163,0x110e5,0x110ec,0x1112b,0x1111d,hx11,hx16,0x1d842,0x1d850,0x1d811,0x1d80a,0x1ca50,0x1ca42,hx17,hx12,0x1ca0a,0x1ca11,0x14ec,0x14e5,0x1563,0x155c,0x151d,0x152b,0x235c,0x2363,0x22e5,0x22ec,0x232b,0x231d],7⟩
def GA:=[7,56,63]
def PA:=mP BA
def BB:Z4w:=⟨4,1,24,[4,4,4,4],[7,11],[0x688,0x681,0x4c1,0x4c8],2⟩
def GB:=[7,11,15]
def PB:=mP BB
def BC:Z4w:=⟨6,2,42,[6,6,6,4,4,4],[7,57],[hx0,hx4,hx5,hx14,0x23a50,hx10,hx13,hx3,hx11,0x1d850,0x1ca50,hx12],4⟩
def GC:=[7,57,63]
def PC:=mP BC
def BD:Z4w:=⟨5,2,54,[10,10,8,6,6],[7,27],[0x4688,0x4681,0x3881,0x3888],2⟩
def GD:=[7,27,31]
def PD:=mP BD
def BE:Z4w:=⟨7,1,22,[3,3,3,2,2,2,2],[7,120],[0x1ac688,0x1ac681,0x1ac642,0x1ac650,0x1ac611,0x1ac60a,0x1ab881,0x1ab888,0x1ab80a,0x1ab811,0x1ab850,0x1ab842,0x1a3a42,0x1a3a50,0x1a3a11,0x1a3a0a,0x1a3a88,0x1a3a81,0x1a560a,0x1a5611,0x1a5650,0x1a5642,0x1a5681,0x1a5688,0x19d888,0x19d881,0x19d842,0x19d850,0x19d811,0x19d80a,0x19ca50,0x19ca42,0x19ca81,0x19ca88,0x19ca0a,0x19ca11,0xee888,0xee881,0xee842,0xee850,0xee811,0xee80a,0xecc50,0xecc42,0xecc81,0xecc88,0xecc0a,0xecc11,0xe5c88,0xe5c81,0xe5c42,0xe5c50,0xe5c11,0xe5c0a,0xe6a81,0xe6a88,0xe6a0a,0xe6a11,0xe6a50,0xe6a42,0xf580a,0xf5811,0xf5850,0xf5842,0xf5881,0xf5888,0xf4a42,0xf4a50,0xf4a11,0xf4a0a,0xf4a88,0xf4a81,0x11ea42,0x11ea50,0x11ea11,0x11ea0a,0x11ea88,0x11ea81,0x11dc50,0x11dc42,0x11dc81,0x11dc88,0x11dc0a,0x11dc11,0x133a81,0x133a88,0x133a0a,0x133a11,0x133a50,0x133a42,0x135688,0x135681,0x135642,0x135650,0x135611,0x13560a,0x12bc42,0x12bc50,0x12bc11,0x12bc0a,0x12bc88,0x12bc81,0x12e60a,0x12e611,0x12e650,0x12e642,0x12e681,0x12e688,0x15e881,0x15e888,0x15e80a,0x15e811,0x15e850,0x15e842,0x15cc88,0x15cc81,0x15cc42,0x15cc50,0x15cc11,0x15cc0a,0x174650,0x174642,0x174681,0x174688,0x17460a,0x174611,0x173842,0x173850,0x173811,0x17380a,0x173888,0x173881,0x163c0a,0x163c11,0x163c50,0x163c42,0x163c81,0x163c88,0x166642,0x166650,0x166611,0x16660a,0x166688,0x166681],8⟩
def GE:=[7,120,127]
def PE:=mP BE
def BF:Z4w:=⟨3,1,18,[3,3,3],[7],[0x88,0x81,0x42,0x50,0x11,0xa],3⟩
def GF:=[7]
def PF:=mP BF
lemma b4:cB [(By,Gy),(Bz,Gz),(BA,GA),(BB,GB),(BC,GC),(BD,GD),(BE,GE),(BF,GF)]=tt:=by decide+kernel
lemma oy:Ob By Gy:=gB b4 0
lemma oz:Ob Bz Gz:=gB b4 1
lemma oA:Ob BA GA:=gB b4 2
lemma oB:Ob BB GB:=gB b4 3
lemma oC:Ob BC GC:=gB b4 4
lemma oD:Ob BD GD:=gB b4 5
lemma oE:Ob BE GE:=gB b4 6
lemma oF:Ob BF GF:=gB b4 7
lemma k23:KOk By Gy Py [(32,[4,5,11],[0x239b90eb66071cc0d398197],6),(33,[4,5,11],[0x194b4c86d87028f8127e08be031f014fc09746a67],0),(66,[4,5,11],[0x329698cb090da259251654163ca8297e43a9886d2c0d1e1418ba93023d47047a4e08f45e081c4c703894e07125e21e011f004fc017],0),(323,[4,5,11],[0x6486c1484d8510c43712c12128942220a82250d8a61ba3c8753],0),(195,[4,5,11],[0x2545e43a9864322a86d148a62a4c43645150d1262868aa50352d1069910d886d2b1e43a9c188607111c0e21381c417],131072),(36,[4,5,11],[0x1921b610521302385098100c4b04828442215140f21d4c293021c87530a0608436442a22140b240b140a23040b4509c43],0),(37,[4,5,11],[0x1841484dc87530144b14990509c43],0),(38,[4,5,11],[0x112dc8753610521301443],0),(39,[4,5,11],[0x610521301443],66),(165,[4,5,11],[0x11610a84d12c0bc8753044221509a294980a84e0c43],46),(166,[4,5,11],[0xc211610a84d12dc875301509949a0c43],90)]:=⟨oy,by decide+kernel⟩
lemma k24:KOk Bz Gz Pz [(32,[1,4,5,11,12,13,34],[0xd6d69e9ec045b966381e8731c0ec3a0c0d19d06068ae938343731c0dc3a0c0c99d06064ae938323741818b3a0c0c55d270626ec81873b2061ae5c54581c182010140c08045c5b50391d40e2750385d40d4750349d40d1750331d40ca750325d40b47502c9d40b17502b1d40aa7502a5d409c750269d40997,0xe54de2e72a6e973940ae39ca0569c68646030383408048d9604030381008bd2d482ee0ea417687010eee38087769c043bb2e301816c30466f1c119ba70466e5c9121b03b8674402e2c165c6b4f415e320867e1c0433e8e0219f27010cf8bf04e085d699682de0e82815c739196d38bacb41409e39c89ae9,0xe502b8e72815971b180d100317699ca04f1ce50274e4c4a48909492dcd8da04025dcb],18),(33,[1,4,5,11,12,13,34],[0x9eb65381b1359c0aa3ace0549d67c592e24262804022e8b34d43439953161eac46a0f772b487924b98380a96b1c054b54e02a5a977e78060ea1fb1c0e09ace3826b34e09accbfa830cfea0c2bfa8306e6048c030182cc390311e40c2790305e40a4790289e40a1790251e4092790245e408c790229e40897,0x1382f468ce0b1004d1de8c9acb8b49dc80298ee401497034a692cab1759c0963ace04a9dfa01fde5e9e020181c0804ba9601008562c0804161b004c5a8c0a59d46052aea35e8b71214160402164d8282e061c9b7a40a63bd20529c08042c967040694d161e70793511a3c9a88c5c0cc99c802c8ee4016176,0x4b8bc1d8a3492ee412387d0d84a29882470fc128dbbc1e082470fa130ae0946ede0ec51a49792091c3e86c2c4013470332641993345853104961f8251b7783c1048e1f42b38154759c0a8b81a931a2a4aa2a294551b7743f04a299268946edd0ee622547628d293b988945f83615180b23a8c0585c0d899c,0xc60402d864898d81dc350910dd42423750904dd4240b7950c19e54305704020a0d80402170b20b1bc1c19a1810140c08042c5b0100828b682cef0706686f070c0607010e35946bde0e0cd0d25054ce9282a577c787a0402168d9454940686c9280d0df040343692daf0762091c3e849280d0d98a3ca2fc12,0xec181c047a9624715263bd963322c2b8611163bd95330aaa26492fa5162c7517d553bd94bd2cf22be967895f4b3c2aea3028e70607010e358b6b4f4f6022d8b7988915fcc444aea302967f31106bb5358b0b808b2adca3c98ef5a24a77ad124bd9478b1eeb4454f75a229706687359e1c7a3110d3d188865,0x8ae2ea2d050298e724eca71110060701172580e54cc2a0b8aa9deb441ae0e52cc4b0b86222a7b28d14b8396330a5494a0e98cc295252962b3014c7074a6625852a4b16180a63a89ab29e6f4c52f37a60d707497359e1c7496b4d38c8c0888008b32c7a7b010e95931625854a525bacf163a4b9aa9e0e09e9,0x20c8c0888009732c016167a7b010e95802c2e4d4c98f16220e78b1106bc13d030758cc8b0aa2b12a4a6292a52c3012c761ab553c1c13d3d8303808f52d870234ec381197302464181016718302014e35547915eaa3c4af551e157414147388880303808b1ac171c617526552326176180aa3a899b49e2e44,0xb0da70258ec3012977f82787b0a07031ea9eb8238fae08d39918981312923031308d0c8c0607068100a332c25244d4c6c6d011ee5b69e457da7895f69e157850a39cb0b44440181c0478d603873624f64acf64ccc4de4c925e6e441af04f60e1d4b0594585925b0b5aa5e09ec1c3aa76df4d39898129232b,0xc0549d6602a2e2ca8ce0b900531da70294fa7220d7dbd305b8b24b1a2c4b22c2b2f4c1cf97a60b794a0c4494fc6220d7eb5305bc9537a64a7830d24bcc4c2a5292a62f5a25477ad1293b526945f82705251a7078a4b28b8b2a349469c1d4308951e292ca2e2ca4e2d4c98ef59e4a77acf24be86eb3c70e2c,0xf041da1cda7961de0e19c151468c5d25052cea3029571417030e4daab3c62f76a6157bb5309b8a28b343559638714586585a702c8ec3016170362736a6497931106bc98882ddfde01c3a962d004d1d260264f75a2157b28f09b8b18b058c5f058622317c3110abe18884dc59459c15180a8b8b29330ae0ac,0x1e1131292242524b7363681009772c6a160a4d9a9ac585c0459572a1473ca851ae5c54581c182010140c08045c5b010140c08042c5b180c0b619224360770c070e6782660362603873950a99e542a57787b030e8d9c13c3d818746c1da18140e061c5b00d899893cc8ec49e627624f30b],0),(323,[1,4,5,11,12,13,34],[0xa419a1bd92301ad0862035a10c582034c12880d306c294a4a0a41498522034510c4c1a082901815b0541c0941052c1606421862306f60c1d43089144846186130484318852580d144312158688a128284218e82034510a43160406d048521c1bd830742da1ac505c0c5926565854181c1a100c0e04025c4b,0x8a0303603461030a628a2c508293088a0360a282e061e931e1ec0c3b26030a6018537821601853c086160521787b030ea98f642c30bd9430303628a0d69e02b060140d830630334301815bd9c300d30c1bd830752c837b060ea5e04068a218b0306f60c1d5308a0c4c2b0b0306f60c1d6301831861060a60,0xa690bc14301a0350a0346282a42f0f6061d5368140a6182e32c2eb0c908b88b062035424280d908b8c305c61c14068c22ea4c148c22ea2c780a62ea8d7569e1ec0c5b260181b0a2c300c0d80d030a6908a0c300c0d8a1030a60181b908a08b01a035420350a03462908a0b818734c030a60181b14187050,0x85fa01fde5e9e020181c0804ba966048c030182cc31a05029965a780ac58d62e14cb030a60181b018533c10b68140a458f654c7b2a6313d94b3d90b686b141703166980606c28b0c030a62822c0690a188a0b818734d69e02b8602a7b2060606cf062cf052c030a6f070c030a6f042c031a6030360543103,0x140b1506030710c2c10060e2182010506c4890d81dc300c0d9e0e180606dfde01c3a967f82787b0a07031ea99918981312923031308d0c8c0607068100a332c04020a0d9e0e180402170b484010560804141b7e78060ea180634c031a6c102a0606c030374100c0d9838101a531a1ac0c39a6686b030ec9c,0x402],131072),(195,[1,4,5,11,12,13,34],[0xa20368a0a4c1a080dc28299280d30541c083150712034c1c880d305810c6420346150662034c160652604c1808291862306f60c1d43084318a221586a8a92a2885318852988525a8203429605412148680a2284a0b06f60c1d0b686b141703164995961506070684030381009712c13584704d609c135817,0xd2848a18521428610a70a2ea0c0a5e0a1b0203461782163c01bc28baa35d5a787b0316c980c18c0cd0cf670c06c1bd830752c837b060ea5e0420b0306f60c1d6301831bd9030a218ac2c0c1bd830754c7b296189ece18330b20dec183aa6837b060ea5e44060a60668688b02f648c6086228ac26880d48a,0x9a614186141170500ca980c2980c6980c0d8a28b1e08580c29b0206521787b030ea98f642c0c6980abd9430303628a0d69e02b060b8cb0bac301a50a422e30c06942b0a42588b88305c61c040694242b820a64280a62948b88b05c4585c61c1430862228ba930c21888a348e22ea2c068c218a0a38861c08,0x1d533c10b68140a458d090403036f070d8500c0dbc18b00c29bc14b00c0dbc10300c0d80c29bc10b00c0d815030a680b0aa2a4a82a42f050c06ac218962d0a0a90bc3d818754da05029860181b00d030a62830c030a6908a08300c0dc04030a642a42034a62822c2290a18ac290a52282e061cd30505c0c3,0x5817f82787b0a07031ea98c10181b01b1300c0de040303660d04030370101a6081a9300c0dc946080c0dc84035a8c181a537f78070ea19918981312923031308d0c8c0607068100a332c68140a659a05029063d9533d94b3d9c3686b141703166980606c282e061cd35a780ac580606cf070cf052cf0f606,0x10082836092837e78060ea19812300c060b30c0181b3c1c307086782060181b7f78070ea580d58],983040),(36,[1,4,5,11,12,13,34],[0x9a420045141a02f040da05029060300b018318040cd0d06f60c1d4b002f670d06f60c1d5341bd830758c00e0400bd9230126080908922a0b0290c1bd830750c024020242284a0ac0a8290c1bd830742c0241805801060c6b0a22c081921a0206416f640da1ac505c0c5926565854181c1a100c0e04025c4b,0xe30c2ea2d055d5a787b0316c982830c171860604c088a0b818734c00c1428a2c0302628a0c028a0b8187a4d69e02b063421881813002f070cf0f6061d9300c09bc18300c2981103026f050c030278500c099e0a1e04009820142290bc3d818754c029eca181b13242030a60141103026f042c030260040c2,0x81c0c7aa60024150402982088181300206a4d250032100203027011a80581a537f78070ea19918981312923031308d0c8c0607068100a332c1081103026340a0522c02004f642da1ac505c0c59a600408818135a780ae18010220604c03026f050c03026f042c04bc3d818754da05029860042e22c008222,0x804141b0040402140b1224360770c3c10366120a419506030710c06086783860020c10de08182420c0804141b00224a0c00c05f9e0183a866048c030182cc30020040c098413c1c36041c218070860604d017820608411405fe09e1ec2],0),(37,[1,4,5,11,12,13,34],[0x25a780ae1801686b141703164980604cf0f6061d133c10368140a4195961506070684030381009712c0608600408818130806070201162580104030381008b12de0818030260402140b50521003017e78060ea18010020e10d0101a1300a208503818714c681060e90de5e9e008045a166048c030182cc3,0x2010506c0101008502c4890d81dc300166120a419506030710c0280c098],32)]:=⟨oz,by decide+kernel⟩
def WP:=C Bz 2 [1,4,5,11,12,13,34] 2
def S15:=(O 1 4 [0,9] (O 2 4 [0,9] (O 4 4 [0,9] (N 8 [6,12,42] (O 9 11 [13,4,0] (O 10 11 [13,4,0] (O 12 11 [13,4,0] (N 16 [18,102] (J 0) (N 48 [120,90] (J 1) (J 2)))))) (N 24 [12,24,96,36,48] (J 3) (J 4))))))
abbrev t15:=LC WP Gz Pz S15 0 0
lemma c18:t15 0 5:=Tc oz [[0x1d3181d2981d2594570561076874c2c482e80e050cea16050ae0606c0a07030ea98281c0c3ca60503818794c3282ad6cf905d6280a19da380a15c0c0de04e1c0288ee1c0282e0684d32c0491d32c0489de5e9e008045a167a2c5073ae8243e1ebd01cf45860e75d0287c3d790380a9651c054b24e02a5917,0xd8303808f52d87050cec38285704020a0d8f070c03326032a603526034a6fd00fef2f4f0100c0e04025d4b209e8183ac65860e09e9ec181c047a96914050ce914050ae0804141bc0806c4cc8ac2140e061d5300cc980ca980d8983b43382140e061e5300d8981da1961684281c0c3aa60a07030f29865050,0xe16010085c2c19a180402170b008042e160cd0de0e19a1584b0b420654cd0ac20664cc2b827074206a4cb081b131e8b19e98581a537e807f797a7808060702012ea5802c2c0cd0c06686f470ce0b42b080585c13d030758ca2b2298b12c2a52929314a525e09454a5257074264589615c1383a1b0c1c13d3,0x8042],[0xd9a4cc0e7963c90ee1c5442ea119168642c09432b68c42e910050ceb18050ae0606d7349941d838a845c50618190341522485244f9c2c90f8369448f4a85c44f4a85c42f8102b19c54c0f3a47448f11a4c44f2a06442ea185732507690161878d93a147898361171417030e49bd20511de90284e0402160b,0x1390803627210cb6a9710bbec9f02bbec9f01b8a08b00c6980ca980d8983242a96d1885d4280a19d6300a15c0c0dae893303c984921db449845c5141806a4c0654c06c4c034a603526032a6036272100d4980d8980654c06c4e4219006a4e420ca14032a6035260cae68b243be89310be041417030f49832,0x242d2280a19d2280a15c1008283706161875d3321475d3321275d332117125060a2c30a0b818734c282e061e93051618505c0c39a6684505c0c3d27210505c0c39a61417030f49828b0c282e061cd30a0b8187a4e421905d5185d6182e32c2ea8cc8b422eb0e4278e050ce914050ae0606c036260195301b,0x14cb90bc1431999da0484c500804899666686a1214160402224dc125921e892c50f8100c6980d2980d8980634c06c4e42da04cc0f65922877d4362477d43622702010a858f4f6021d4b2440129648c840149690be613123a84d983490ef983450f2a46448f812433a85cc0f01a2450f4ac6c48f2224444e0,0x4985951991685c1165860b24b0b2a3382d08b2c306985685617050240a19d0240a0dc581582ca8c0d0b02b90d9848a1df54d891d93c7885c0c89b944861eb15c28f58ae127121314020116458034a6f2f4f004022d4b1e1ec0c3aa60402170b00804299602010b8580634c08042c96010085c2c031a60402,0x5c1d0989615c1686c2545495152949492f04a2b83a130ae0b436150ac81310b9c381433a048142b8181b00cc980c6980ca980d4980d8980634c0654c06a4c06c4c320a0b8187a4c1417030f498650a018d301b1301a9300d49865a2c7885d42615c1684a1815322174480286750b02857030372105925859,0x65840c69961032a66840d2980d8980d4980664c0634c0654c0694c06c4c06a4c32382282e061cd300c6980d298a2c30a0b8187a4c1417030e69851618505c0c3d2619429a1584e081993382d0ac20634c06c4c0694c06a4c033265840c6980d2980d8980d49866483442ea1312c2aa2a4a8a49551e094951,0x8042a960195302010b85b9878a1e422430c16546704585c0439960094b008cb165861617010f4582ca8c2cb0c2c2e021ccb0b0b8087a2e42705a1584d0ac20252c0292c02c2c02a2c16546014966840292c59618585c043d16a13420151601296016169a04c50f2116186c38286761c142b82010506c0332,0x3018d301b1312131402011745824b0c032a624262804022ccb00c6980ca980d8989098a01008ba2e42584b080ca981008552c032a60402164b00d29810085c2c03526034a6036260402168b04850581008593602010b259a101008592c4961806a4c06c4c0694c484c5008045d16a134202010b45806a4c0,0x694c484c500804599601008552c031a6040214cb1258601a5],[0x64961658651529495c1383a1382d0d841654616526165161649662585705a116586a11618670e050ce70e050ae0d44470512c88a1c586181a889112850240a19d3300a0dc5815c84c960288ec960284f334640af4387406e2c82e290248f1481217787b030e89ace0451d670224eccced02426280402448b,0x49806a4c330246482f1aa7c0af1aa7c06ef042e2d3c30f21782860b2933822cb0cc2aa2a4949d0985686c268561e082ca2c2c92c2ca8c2ca4ca4b12c8b0a0b293d0991687822cb0d422c30c70b42b0b8264585322c2b85a1343612c3c1309856856170498a4ac8b0ad09a1b0961e09854260e050ce2c0ac1,0x764c03626610cbcb1910bc1498b12c2a5292929497824a5257074262585705a1b0949515914c58961529494a8a6294a4bc1292a2a5292951e0e8492b22c4b0a49782615c1d0d84c30b29482eca25442ed302867409028570303601b13382f0f6061d931e1ec0c3b261924401433ac60142b8181b00d8980d,0x52603626034a668561342b0818d33820664c06a4c06c4c0694cc21900ca9961031a6034a6036260352601a5325298b82282e061cd300ca980c6980d298a2c30a0b8187a4cc20195301993018d301a5301b1301a931c11417030e6980694c51618505c0c3d26610ca14686b030ec9806c4c0664cc23435818,0x2a65840c6980d2980d8980d499841417030e69851618505c0c3d26018d3019930195301a5301b1301a9330865d651905d850c815d850c80dde0859612c20634ce08199301a9301b133820694ce0b42686c2705a15840c699a1585c103326685c1035265840d89985644a8f040d29984d0ac2031a60332603,0x925547824a525707423d94b3d963382f668ec2f670ce0b427b2c67b346685ecc99c1685ecc5929705a17b2a661529495c1383a17b29654549515294959162585292a2a5292aa3c12a2a4a8a94a4a54783a11eca99a17b296685ecb19a1705ecd1d85ece198545050cec382857030360a2c30a0b8187a4c03,0x6c2545a134361e0bc3d818764cc23c18b3c14b01b1300c6980d89bc1c3382d0ac2f0f6061d53292d0ac2e0bc3d818764cd09e0c59e0a580d899612c20634c06c4de0e19c168561787b030ea998954549684d0d84b0f05e1ec0c3b26610c8f658cf668cf664cf662cd0bd95324ae0b42f652c94a4ac8b12c2,0x14962cb0cc2b82d08b0b8087a2dc8050cee40285704020a0dc1ca921de0a1b3090530c7829603626018d301b137838668561787b030ea9951525a1343612c3c1787b030ec98f062cf052c06c4cd0ac25840c6980d89bc1c3262e09c1d09c1686c2f0f6061d5330aa2b22a8a92515515274262585644a4e8,0x5840d898f458c0d29bcbd3c01008b52c7a3467a2c6016166856100b0b7a386705a1585e9ec043b16515314a52524bc124ae0e8492b82d0d85e9ec043a96a302867518142b82010506c02010ac5808042c9601008562c0402164b1258601a9301a530199301b131213140201174580262c2ca8c0292c01316,0x282e061e935c5b5a797a78020122c58b4f415a31eca99eca5b5358b0b808b32c1617010e658f4f6021d4b16586b4f415c305d5185d4985d45985705a117586b6b4f4f6022d8b4141433a0a0a15c10082836010085c2c02010b85bc1c300cc980d8980d49bcbd3c01008b62cb09a1032a65840cc99a103526,0x66686a1214160402224d824262804022ccb1e5e9e008045a9624b0d69e02b860a2c3342b08a0b818734c],[0xa15c0c0d806c4c0664c0362619125300c3b260ce07ec34a0f09c4460ec246442eca66c0aeca66c06e2822ce08320682a4490a4889a0ae85cf891e550c889e348a885f031a04ca0f1a04c60f2a45c28f2225422e282e061c937a40a23bd20509c08042c17772a487ab11063d588829eac4412efcf00c1d43,0xa5301b1300d89864912050cea16050ae0606d940a981da44b891da44b889c08042a17961e307db930a3edc9849f6e4c22e24a0c03326704505c0c3d260a0b8187a4c3201a530199301b1300d8986553ca981c514181a20140e062e530657349981e0349941d8230502464c0f5a05460e2ea0cf1c0a19d228,0x18122e22748a879510bc07130a3f566849c585c0439160c0805b0c22200c0e022e4ba2d1123d589889eac4c42fd5a2147f313093f989845d82c38286761c142b82010506c7e68601a5301b137e807f020116c585c5458949098dce0d808045c5bc090704021d8b6050240a19d0240a15c100828360199301,0x5c0c3d26181c1a100c0e0402464b7291123b948889dca4442f7522147ba91093dd48845d8200a4b005258b2c33422c2e021e8b00465804c580545805858052582c2e021ccb0b2c30b0b8087a2d222c28c98b12c2a5292929497824a5257074262585705a1b082ca4c2ca2c2c92ce0b422cb0d12615a1585c,0x244ef2f4f004022d0b008042c9601008592c496180694c0664c06c4c484c5008045d16685612c20634ce08199301a9301b133820694c704505c0c39a6018d301a53145861417030f49a1416496165461652664585685c116586d245c48eb9e4442e0644f4d4c28fa6a6127121314020116458301816c3050,0x93b4a15033b6a9701bc247c1169920284f112a500a23a6400a13c4c1b08bc0b1702bbea9501bc144d58626ac30696138802867388028374d056426550c815e44cb80dd3445a150d909ea409845df48b819de44a80dd344981484ed4c9849ee50a845d3451e078f4c18fb7220970a07030e29ace0491d670,0xae1704e0d84b0e84324c529495c1383a1382d0d8566050ce0d26292b82b0b42b30286761c141b854074967041da180e92c0ed0c2b26220674cd2603724931705a1343611c2e0b42b0867ec3424ed20540aec9e4c06e45029a1814c4c14d0c32705612c602867307028570a03701a3424f1a04c22e5136a97,0xaf37aa0370709641bd038758d06f40e1d5320de81c3a96837a070ea9a0de81c3ac78120de81c3ac641bd038752d06f40e1d63c0834074960768603a6303a4b03b43c0b0e0a19ce240a0dde8159f54b845de50a815df54b80dc1c25b900511dc80282e0684ca8a6292925e0925706c270561d092949494a4,0x9fe09e1ec281c0c7aa61982e04072c6074c6074a60749652545704e0d841da180e58c0e98c0e94c0e92ca4a8ae0ac20ed0f0358b24175141433b0e0a15c0c0d80634c0664c06c4c06a4c0694c031a6032a6033260362603526034a61912561925300c3b2624ac324a6018764c3381b49b20bc187845e6f54,0x2c4bc080e92c036260ed0cb0b42140e061d53382140e061e5301d2581da19a10a07030ea98281c0c3ca6191fe09e1ec281c0c7aa63fc13c3d8503818f54c330501d25806c4c1da18281c0c3aa6704281c0c3ca603a4b03b430503818754c140e061e530c8fef00e1d4b3fc13c3d8503818f54c7f78070ea5,0x1c0c7aa63fbc038752cff04f0f6140e063d530c9147b2c67b3467b3267b31652545705617b386a1e4c22ec302867720142b8181b20dec183a96837b060ea9a0dec183ac641bd830752d06f60c1d63068f668cf662cf670ce200a19cf240a0dc1815c28150a3f9a7845c0c49e9c9831f4e4c14e100c0e0402,0x384030381008b12c343230383a36080a0604022e2d892b0c9298061d933231304f504e08060702012ea58066866098f41dc313161989828288303808f52d46050cea30285704020a0d8f062c031a6f070cf0f6061d532c2f0f6061d931e0c59e0e19e1ec0c3aa6787b030ec98647f78070ea59fe09e1ec28,0xdc8a3d9c341bd830752cd0ac306f60c1d531c2e0b42686c306f60c1d63019a19ece1a0dec183aa6705a15860dec183a96385c1585a1837b060eb18347b3267b2a67b2c67b2967b346705ecc594562591614a2f04a2b83a11ecd1d85ece1a8c0a19d460506e0c0af0c4428f549611703127351e0c79a8f05,0xc92b82d0bd94b30aa4a8a98a52929294978249531707423d94b3d9a3342f658ec2f670d25050cea3028570303603b4301da1bc1c300d89bfbc038752c98a52c8929e0991706c270561d0bfc13c3d8503818f54c0768678386018d301b137f78070ea592970561685fe09e1ec281c0c7aa6196a9102bb5488,0xb0b827a060eb1929495c1684d0d860e09e9ec181c047a968282867414142b82010506c7829603626018d301b1378386705a134361787b030ec99314a494f0494b8361382b0e85e1ec0c3aa63c14b01b1300c6980d89bc1c32c2f0f6061d93382b0b42f0f6061d530c8f668cf664cf662cf658ce0b42f654,0x3c1c300ca980cc980d4980d8980d29bf403fbcbd3c04030381009752c7a3860],[0x5ecc5991615c1685617b3868282867498141b8302b088307018505ca60330b033435181433a8c0a15c7030283688bd923085318856184294c42b0c3288a132b28c82f040124779c0913f208815fb14c06f06f60c1d0b69c08a3b0c0445da1ac505c0c5927ae0863eb8214e565854181c1a100c0e04025c4b,0xf6140e063d5301da19e0e180634c06c4dfde01c3a96385c1585a17f82787b0a07031ea9866af5c82f57ae217931102bc98880dda05029163d9c341bd830752cb0c1bd830754c70b42b0c1bd830758c7b386837b060ea99a15860dec183a96385c1585a1837b060eb18347b3267b2a67b2967b2c67b34670,0xf615a305d4585d51ad3d8564c171c61754617526175163d94b3d9a3342f658c5d61ad3d8570e142857030362d3c0562c7b2a6d0d6282e062cd3051618505c0c39a6b4f015c305d4585d4985d519c16845d61aead3c3d818b64e142857850a0dc3203b433c1c300c6980d89bfbc038752cc8b82b0b42ff04f,0x6460444004b99601d258c8c0888008b32c83827a7b0607011ea5819a18c0805b0c9131b03b872a1433ca850ae0804141b169e02b165a780ae18f654cf658cb0bd9c3686b141703166982ea4c2ea2c2ea8cc8b820baa3d08bac35d5a787b0316c98d62e14cb358b8538cd62e14d305d45ad3d8562c17516b4,0x1e117151607060804050302011716c4890d81dc301da19e0e180634c06c4dfde01c3a960b24b3422cb0dfe09e1ec281c0c7aa66462604c4a48c0c4c2343230181c1a04028ccb0c09190604059c6413d838752d04f60e1d63413d838754cc4c094919590]]
theorem Z0K:FBO WP 0 0:=Tz oz c18
lemma k25:KOk BA GA PA [(32,[5,11,34],[0x217470217270217170216c70216a70216971306671306571306370215c70215a70215971305671305571305371304e71304d71304b7],1572864),(33,[5,11,34],[0x302015c61738c5cb38512578511572240307022cd6071ccc4052e1d5326525092bb988ab871ac3964a8c02a7410052e1d639501c77301a762c0890022d9791787580707580687840a472fb1bca8513ca850bac02c3c204a397d4de54249e54245e10231cbe96f2a114f2a112fd8867ec42b9a3070202161b,0x1234e200d39c401977151022ae810435d2ab0c1e5629462089bbd8a7ccba18955b40c50b96c208034e410065ca1c6288068e5100c9f140ca98a2089b94410b78d28824ae510435ca156510499ca208b3994a30f8616739169c344ed38251ca17061d272a342f2a322f2a118f2a114e3070d1018382024496,0x2cd4408aba0410d79561c246ee4216e657142e715831e9b0c844dd2ab0c1cb6649645659d2a5561839ac810069d0200cba538cc95294a6a288064f8a6294410d755129566100a5ea4c55498401a7308032ee2408226e81042de3548459d5a50c1ce62cac4510459e64720499ca208b39c8e20193a060317d,0xb962e043aae5448de5444dd12834793181c30820487040a0c101232d864730e46a2b1acb99664e030e5b018b606c9d30933b988739956503acc391a86b8a62a9086baa8aac4062f922a8e5880a5ea4c954a4a01a76201977116552a300c9d04018be8872c9598054e7100a5ec47158a06116740c21cf3214,0xc0760162c02c59638ca968ac654071dcc069cb17021d960a58c9280b1c52a64ca0802c77302a714a5d3092bb9886],0),(66,[5,11,34],[0x30d03704c119a1152e6184aa3532320a52c291b052c614a985296148d8c8a8a06c2551a991905296148d829630a54c294b0a46c64545036c2064540c8ab08c2308ce08a50e2909239728d870913b0e112761c018e3480a0e0c594cbec2e04ac0e5f5170255072fa4b812a43ca8423ca8413983464101160b,0xd0b9662e558b9c61726c5cb3172ac5ce30dc1a1234e2554ab45621ab255299469c4aa9568ac434554aac48d389552ab10dc10b9561726c5ce3172ac340dc1a119234e25968a65624a8e58aa5469c4b2d14cac4345958a648d3896562990dc1235a2b131552a54ca35a2b10d03704642e5985c9b1738c5cb,0xb93652a651a5ce30d190b9962e4d8b9c62e5985cab1732c5c9b1738c5cb30d0b9662e718b9361732c5cb31726c5ce30d19c1150d51a592aa55327168ac4c554a94723546964aa954c9c5a2b10d234b25568a553271588723546964aad14aa64e2b10dc10b9662e558b9c61ab4435689726c5cb3172ac5ce3,0xb9962e698b9662e4d8b9562e7198ac9688b9962e698b96668a34b93646972ac5ce30d0b9662e4d8b9562e7185cd3172cc5c9b172ac5ce30dc1190b9a62e558b9962e4d8b9662e71992c5688b9a62e558b99668a34b9362e598b9c61a1734c5ccb172cc5c9b1738cc5688b9562e698b9964c972cc954ca34,0x689726c5ce3172cc992e558c08057188070a73100e14d7821726c5ce3172ad8232142e0c3a6c0d93142cd82608c8a8750c1836c06856185cd31732c5c9b172ac5cb31738c3564b15a22e699a25ccb344b9362e558b9662e718685cd31732c5c9b172ac5cb31738cd11734c5ccb1726c5cab172cc5ce30dc1,0xb830e9b06870a7333603480316d30b9662e558d2028383165bc101b26285c187699a250b830e9b19b01a4018b698690141c18b2de08c8750c7125438b60ea583aa60e398b2990e3583ac60716c1d4b071ac1d530758c64141c1872d83a960e399a2283830f530507061cb60ea58507061ea6322a1734c35,0xa0e0c596c3438539980d0acb03a960e3983ac6cd80d200c5b4c172ac5c9b1a40507062cb660342b2c0ea583ac6cd80d200c5b4c645418360752c0d1b0334c1c731553295141c1872d962d1141c187a981d4b0346c0cd30a0e0c396c283830f53190e450b30316c0d931c5a250b830ed3234723568a652a5,0x2b2c343853985cb3172ac690141c18b2d81c730758d9b01a4018b6983438539980d0acb0b9362e558d2028383165b33603480316d31908070a5b30201596201c29cc2e558b966403853581c6b071cd8100ad303aa6c08057182e4d900e14b660402b2c2e55900e14d60754d8100ad3302015c6320b936348,0x8a0e0c394c2509522d40489da800a3942e0c3a4c40a0485cb9164090491cc1401172e51a881227510224f050031d86004b99380c394c3460031cd1800a70404292c0629b0470c01239c30214e0d1340a0485d6500a3aca0127618212e4899404045a2cc8661d434a9008715b020158668c1c0808586c6034,0x5b8504060e0808ba58283830f53851903a960eb1838e6080e143d2c65460123a080217068980d930354c0d1b01aa6320cb4e02470689bd21217594222e1c4b3154ad14cac4d14aac51a994502a96064ad14641944a0445e140a46c650ac28045d4445614042e81208a3c8b0e1227490224ed40031d45004b,0x8018f08012e3480a0e0c594c08562554915860e0479ac4aa922b0c1c08f35c8804ab0162c052b0152c050b494248ee6228e915060e6315966565595a6656958955860e6b2556183cad25224ca25a70923b9001275651b0e1217490222ec38031d240053860e04392c0ea58507061ea60a0e0c3d4c283830e,0xe14e660342b2c0eb1b3603480316d31931603070d04048b2c6428598a17061da64c942e0c3a6c06c98a17061d36285c187698cb921217724222e343852585cab1726c5ccb172cc5ce302b16245c2874d89170a1d963258a3532064ac664b090b9722c0a46c650b048491d85008b9728d670913ace112751,0x51ca17061d272a242f2a222f2a018f2a014e3070d1018382024496112018381166b03ac6c581120045b2c2c4d80b162c5c087558b17021d970a248f0a228e403053185ccb1734c5c9b172cc5ce3172ac0cb183256f48489cb92644b4e124769c024e5ca3b71217b711179500c77300a72240307022c960d,0x301d858b810ecb162e043aad12834793181c30820487040a0c101232d8655940eb3195c50b9c560c7a6c9169c244ed38],0),(67,[5,11,34],[0x8ac2b2b0ccac632b28ca17061d276e240f6e220e3438521ca8023ca8013983464101160b0042b12a4021c56c0805619a3070202161b0c866608b98664e030e1b00856010acb1862b18cb91664e030e5312ab0c1c564aac30731942e0c3a4c60e1a203070404892cbec0e5f5072fa4387d11c3e84e1f41701,0x18381010b0d864e030e1b0b1862e4599380c394c4aac30731942e0c3a4c60e1a203070404892c1422c6870a4b05c8b201c292c18360c8321d4303a860c1b60342b0c311730c892e4990a31449722c5ca31a40507062ca6190cc15608ac2b2e6199380c386c190a8c415189730c5615958c65c8b327018729,0x60402b0cd],0),(36,[5,11,34],[0xc8661730cc9c061c360750d02060d9420c6870a430042b1620c8060a43030860215b020158630181586220c133068c82022c16008c866008b98664e030e1b0045cc31722cc9c061ca6188642a2e618b916111585656119720cc9c061c2625561838ac9423255618398d2250b830e9318386880c1c101224b,0x8c0805619a3070202161b018360306d80d0ac30],0),(37,[5,11,34],[0x23460e04042c36008c1c344060e08091258021420c6870a4305c83201c290c18261720c690141c18b29983464101160b],0),(38,[5,11,34],[0x20d0e14860609983464101160b],24)]:=⟨oA,by decide+kernel⟩
lemma k26:KOk BB GB PB [(32,[4,5,14,17,34],[0x0],1048576),(33,[4,5,14,17,34],[0x1a4c7844a7844978446784457a4437],0),(66,[4,5,14,17,34],[0x311acc9c7a8967b43ab81c3c2d1e804f4017],0),(67,[4,5,14,17,34],[0x188d2188c858485623348a59626a14b687574307],0),(36,[4,5,14,17,34],[0x1118110d320227c8d0b],0),(37,[4,5,14,17,34],[0x88c8581],0),(38,[4,5,14,17,34],[0x88c8581],0),(39,[4,5,14,17,34],[0x88c8581],0),(40,[4,5,14,17,34],[0x1],24)]:=⟨oB,by decide+kernel⟩
lemma k27:KOk BC GC PC [(32,[4,12,17,18],[0x1905f1c5d305d3840af3097312b625ad8c575e611445b6d0b87403474032760c5d00b1d00a9d82976399d0395d038dd0071d0069d81976359d0355d034dd8ce740cd740cb7],2359296),(33,[4,12,17,18],[0x8a2a9e82ae3d8d62aa36472353d8b6169a72353c6947238baa926134ba4c24b7358986f0f341571eccb1553415d1e261b33ca8aad30d99e36261353b8e35c771c69af238d2dec73820aacf04154dd993258e611445b4e8b07a2a1e8247a089e8217a261e8147a049e8117a031e80a7a025e0c67a315e8c37,0x5129bac85a82894dd55238da9e26125b9c926134bbd044e7498496e6b041571d8cb189b0d6672273b0b76e6d4f6e6d2fee6b8fee6b2fc231562ac8e44e7616c2d8986f0f239165dc72273bd054d7638c2d1a9a6134bc8e36676984c6f2ab1c6d4f238d71e471a6bd4c24b7394984b2f238d59d471aabb137,0x4dd544d6a08b2ed4112dcd43210e5b51044e7a20896f531415e1e0722cbb8dc332bd3ab1be29c84f0f6659550309a9d8612cbd8b62ac9046a7920896f6398aa394cb904597720896f6358723550c26a7a1849cf241135cb6271bc3c90459771824cacff0aa6f924a59cc6acec4da082b53fba273b0b616a0,0x271b53b4e359789c69ce5a8d4caa8722d2c955238d59d369cd8de5459310565749448eeaa1cc4c35674d13666e1165ee112dcd4126d030939dc8226b88b61ac9044e7920896f53f0af0fce8b2ee22c8e50c4b2f038d59d35038da9ed8965e071a739685be21ca882353b8c2597a2089ce5b325208b2ea411,0xcbf08aa4d8d0b49ad51955e5891de542d2a9366486b1352a55134d435a73637991546bce6a6eb210d770cccf4eac6ff0cacfceaa6f9264fc23c3c12559771d964e7c854b7254c8d235648dd635674d1360933539cb9cda9e58965f9cd39cb43944e36a76184b2f138d39cb7c439169649b3232a6933539ca,0x1053982e99c24398174d8b310829cf1494b840acb0d58a1ab9661afdbb1bd3123bb9361a366208a6f8ae5589a992a98832abd3229be2a292a9bf3123bc689b2b908d2f9089aee65a29908b2d8ca994a8b2e73597e121cc4d4ca352b4c69ce42d98a49ce42decb3c3e42acbb88aad635674d0e60932e3f3a2,0xe50e85d3708c59a],0),(67,[4,12,17,18],[0x206b05c8303582e71983a20c8324a0c868540d310344a31c10344a06e08c6840dd158b98610860d034942115094c42518e084ac118d0b4421b1408e6189625c930943270868544112d09c4415098892a118e08c36206c0b440d8901ae49c2b9161836229896e14281ac1350cb12cd13728d14c84594e8807,0x864252c328a81082685212c1511484b106c620c4a12e084a12e0a1588b188b191c83055c8b106c943840ac30641a10870a10862a0692a6429296110340d45429096069144a109782128a8440d193892863036622c9639845116d30340d0c92b258a10b9a61081a4a62108324a734c540d732c190a834638,0x384320508260ca1052182a520a43106c210c20dc20565838464858a0a104cc6582a20d988306420db1168414960288430c84218661419252c19104c052],0),(36,[4,12,17,18],[0x384320500908292c20d802520a4b104c212c4a184a188270815863040408360ac6198211015cc3104c010826c4584a184258943104c20da050ac41a10521805010880382008440ae6180205724c0108b916094240a1144a1502e418304c0502350dca3453211653],0),(37,[4,12,17,18],[0x14841496010826840ac304133106841486009c83453211653],0),(38,[4,12,17,18],[0x15081586010826009883420a43],42)]:=⟨oC,by decide+kernel⟩
def Va:=C BC 2 [4,12,17,18] 2
def S16:=(O 1 4 [0,5] (O 2 4 [0,5] (O 4 4 [0,5] (O 8 17 [0,5] (O 16 17 [0,5] (O 32 17 [0,5] (N 10 [1,2,3,5,4] (N 20 [7] (J 0) (N 17 [7] (J 1) (J 2))) (J 3))))))))
abbrev t16:=LC Va GC PC S16 0 0
lemma c19:t16 0 4:=Tc oC [[0x68b1524c9ba0ca4e8b449519c5415325671a2ba2e967527c24a8ce1a22e1a7467c34e8af22828cc8f951949f4b3a33e54643789064f49145f6a2a33bd24437153858ca2ff51519e1307437499b4ec8f051189e14197d66467306e0a2b23c145627930ec2f659949ecb328be0d586587ab0c98f561925cd43,0x6492a93b104457620886e8b351961e492a63989661044677a088ae60dae71ac3d104467bace8ae631b4a32c3c546517d28c98f259d15de8221b98970a48aca3323e525587b28c8ae6218c966647850c70c3ac3a288bc61d61f6b326392d9a6527bb8e8cf66990dcd1318a9264d126527451928b849149c64,0x354c6b18a9a2b154b24c554a9786082a2b989a2b154b24c962f086a58d531ac62b440d31d86493293c0e4467306cc958b84c954ac4b154f08c952c958962a5e18a088ce2a54b256262ac786662233a8c44570d32552b131563c264aa5a2b131562a5e115aa088cf54110dd24352c6a98d630d4b1aa6358c6,0x358ca964ac4a5e13844a58c843d4d24c630d531ac7038d49d871a638c86a58d531ac61a96358c6a98cb0e352781c698ec258b25c21a96],[0xbcd45437151c4b13892b6c3a4b8aedc8467d34e86f1239c619728cc4f249525e8b3a2bd1674378502a98c94bb40d19f2a2a2b8836fb0a8cf09c3a1bc4acc3b13ed87457db0e86f0b859525cc4a568ac4e268ac4e21a38f586437191c43396190dc55a92b13b525617d35298f751925e85c92ac3bd46527c1,0x92c58ac938b46a92293d5244670d1c5a2649c58ad149325c3c5a149c664a2a1b8a9671856ca3293d946467bace86f12389c232689c7ed4233a4b544627b3908af569d0de164932c3cd474c7924c92f4252b44e2b132552a5689c5624a52b44e2b18a0692e1a38ac4a538aa5624b75150dc64a5588668b324,0xa562d131562a5e115aa088cf54110dd266a32c3c925497311a2c2ba08b0e4ab2ce92e2ae350b0fa59925cc6ac3293d586467b34e86f122c58470b08c8d158b0e54646789654662791c6b0f951919d24724f4b32c398c165497934e8af269d0de14b1649c5a252b258ab138b45247164b44c968f0e1885271,0x64a952b24e2b16886a8d4ca558aa56498b5254b85c5a2b16181c6a4ec38d25e071a3386962a56894ad1649a2b1e1192a592c552b4563541519d24c564a95a2b12a5a2c95894ad158f08cc0e3527617a8c92ed4110dc54154c2c99c2154c2c98c94ad164952a5e199848cf141115c41b32552d13454bc264a,0x1927158b44a962a95927158b4524c554a95927158b449510e621ace238929664b14e24a98963492531552a5649c2e2d158db1a93fb1a4bb08e2b164b44c958b4784a538aa562c9688e2c954b4563c24a38a9552c958b44a952b2562d1e199c692ec3249949c],[0x62a95a2b12509531296258e89324bb08a962d15494bc264aa562d131562a5e1158208b0f251925cc4a952b44e2b131552a5689c5624a38a9562549c54ab12515294b1528ae165497316206b0f8264b156271688e2c5688a865252ce2258c258c5706081ac3d5a84c79acc92f43062189fa9919fa990ddc93,0x952b4563c23264aa58aa568ac6672233868a91a954c91a954cb2aa54ad138ac4592aa5532a952b44e2b10d1c552a558dd65437192a4e2a5588e2a952ac434a558ed454371915c1ea6687ea64c7d95497730c254c4a58963194e23892a638b1494b12c6c264b154aa938b4563ee6b0e4a12a6252c4b1992a9,0xce3518692e1a3996738c734ce6594ae7192d104437191518cb2959c43b4c632ca56710ed3191ce339a6732c632ca56710ed315a1c68ce20dc52449731c11958ac9549c2e2649c695a2b13154ac954b456264aa54ad158f08c92a9938b154a38e498a71a968ac608223386992a962a95a2b129592a968ac4a,0xce21da62b8a48ce20de42a4b989a2734cd1732ce7186a726ce599cab68952d1734c9554a95a2e659ce3251cb3689cd3295a2e659ce30e46a726ce599cab68952d1734c994aaa54ad1732ce7192868e699ccb39c63956d1399654b9a6738c9629221b8c8e699ccb39c63966d139a652b996738c94734ce659,0xa2e65e29a3386992c5689a2e699c2e71952b152b45ccb31592d1315a3c270b9c658aa4b1e1734ca952b25a252b4563c2e658ccb121b928a8c6585932c55252f0b3887699c2632c2c9962d164aa4a952f0b3887698c9a2c9709c2e71952e1734cd16494bc2e658ce21d36e13196164cd164ac55258aa54bc2,0x2b25a254b45cd332552a568b99658b85ce31cab62b25a262b25a3c264b44d1e1732cc954b44a968f0b9a654ac4a9e1738c6472cce4d9cab62b25a264aa5a2e6998aa952b25a2e65992b12c785ce3c534670d25344e699ce3295a2e659a2e1385cd3385ce3325a258f0b9963264b15a268b9a670b9c658a95,0x62b44d1734ca568b99670b9c664b45c270b9a668b85ccb2c5c2e718c992c5689a2e6994ac968b99658b85ce3a634670d1cab6],[0x154ac954b4563c232f59d85d88228bb525457212c72cce55b1592d1344d2c564b9c664b44c9738c646710e9b0b260b26322a468e46a994aac4e238e296271c9688e2c564b44668c430bc946457722c520a732905358d2254e142b8c850ae319114c84596c322ad49985ea9328be0c946497250c41b840ac3,0x6c439886b6538871632c9639845116d30e2258e611445b4c669d585f9d545f0721525c9431c44a58e24a9952c9258ce11296254c4b18c84359c44a598a71254cc9258c71709c24a5895312c6330a12966899087a984a58c843d4c65882b0b8a9329538b154a38e498a71a92a744c9b11c58aa564aa5a2b13,0x2551785212c116d8a6710e9b0b261a86acac919715627168b388769872990936116c28d822de294ac5588aa646a652ac5589c44d32c4e2d1164c6710e9b0b2654b4562716710ed385622c164c7162b25a2ce21da66285531c44d30b260b2668b388769c2b11632210539914c84596c9510b621cc43592a21,0x4c94b19087a98cc2822d849b0a36c531694c5529c44d31c5a22c98e2b1688aa60a36c55298aa5e11c5c226985930aa63210e6146c6421cb60a36c5252c7112962699927158b44c843d4c3210e5b0c84396f84e1252ce138494b134cd13210f531945049b6284d31c5622a99a22c99c27089a6154c2c98cb1,0xb44d1e1734ca958953c2e718ce4222b88361296134cd13210f533844a584a589a67099087a98cfdbb0bfdba2bfdba1bb116841496190872d8e226982699296629c562d13210f53384e1134ce109a64a59a26421ea63210e63210e5b194e226998a3889a64a58e2b16899087a986421cb6e13844d3384e113,0x142b2c254e142b4c258c4a9c285718c90815961296258e611445b4ce142056584a5896312a7308a22da6322a20d98a6710e9b2958cb1ccb164ca938b4562ce21da6338874d8ce21d37c252b858cb1ccb164cd158963c2ce21da63264b15a268b9a654a95a2e65962c954b9c662b25a264b4784d170b99654,0x420a7370914c84596d0815961296258e611445b4c45321165b094b840acb094b12a6258e611445b4c64850ad3094b850acb094b12a70a15c670a]]
theorem Z15:FBO Va 0 0:=Tz oC c19
lemma k28:KOk BD GD PD [(32,[4,14,17,20,34],[0x45b2984b3b204aba9849ba10473a1045bda1dad01c74069d0197],1048576),(33,[4,14,17,20,34],[0x5a1dac371f1e07a781e5e058731d1e8127a045cc6c7a029e80973199cc657],0),(66,[4,14,17,20,34],[0x1c4b2c8ad84360747a1c9e871735c1e06c7a1a9e869735a1e00473589cd617],0),(67,[4,14,17,20,34],[0x710d22b6146322a8da1d2c456a23151516148a689258a300a9d8da1d2c328ae0c438191e8627a185e8407],0),(36,[4,14,17,20,34],[0x22b611146323181184c36c8044e44082731a0b02844c2251408068da1d2c5161259122b5128b0211046d0e964560608a4622452c2e59c044e4413141324621271430022723041922134505c43],0),(37,[4,14,17,20,34],[0x1844518c041282d6874b008060c43],0),(38,[4,14,17,20,34],[0x463611120b01443],0),(39,[4,14,17,20,34],[0x611120b01443],54)]:=⟨oD,by decide+kernel⟩
lemma k29:KOk BE GE PE [(32,[4,17,20,34],[0xd02e8e8172740b8bb0f0740b63a05a9d02d2ec3a1d00c8e806274030ba0571d02b4e8159761b0e8054740293a0145d0098e804a74024b8a519c528ae29437409e3a04e9d0272ec2e1d0068e803274018ba00b1d0054e80297149338a495c5246e801c7400d3a0065c522ce291571489b8a439c521ae290b7,0x595a09e8183ab60a2b30a25b83827a7b0607011eb59a19181413123130320e0d0c07060802012336],1310720),(33,[4,17,20,34],[0x6740e0ae81c0dc8561bfbd850746da9ac585c0459565c54581c182010140c08045c5ba2c8f4589e8b0bd0e07a2a8f4549e8a8bd0d07a298f4529e8a4bd0c873688e6d09cda0bd1347a264f44c5e8583d12c7a254f44a5e85439b2473644e6c85e88e3d11a7a232f4261cd8a39b1273622e6c31cd8539b097,0x4d0c8c828398f64cec2265197047b267610a686a2c19d0382ba070377b38610ae310ad310acb4550d46486a3271c15ce381bb84b8ad2b29715a56526a328aa1a4350382ba07037709087308565a328aa1a64ce1ca20615ca2060dc3238470908734960ce82415ce381be848c919708e1d08421cda1e0a8b0,0x821e88db50b0526f423d91b705a1010d62cb0e560cf2b0577381bad3d0570c0a6c60a6a60a6967b396745c56c5a56a4f672c2839814d4cf672d4830aea418370c96574571164b28e461030ae610306e197f7b0a0ee9814d2c14b4c14d4d197b2663d9d33d9cb1fdec283ba7c13d9334960ce82415dce06e1,0x3d91b6b170a4dac5c1d8c30cea41837010560d42eb2c2eb4c2eb8c1c86a46a1a2e26c175a6175c62350d17136a418370c82eb8c2e26d05833ba40df820bacb21a2e26ca9b83b98619d88306e155b5a7a7b0116e582c26c16137c105c4d82e26f82021ac1c86a0e435e08b0b8087b2c01696435e88d8f446f,0xcf081857030363d02b1b180d10031769931292242524b7363681009772c03343180c0b61806b4c140e061f53382705a1ac0c3ba60ed0c68646030383408048d972b0679582bcac0dc9121b03b862d3d0578c5a7b0af18086b00435ba40df8200b8b1ecf18086b39c0df827a236d42c149b169ec2bc63d9e3,0x1d785d8c33f630ae0804141b1cc30],0),(67,[4,17,20,34],[0x3860cc2c06982b082a0ca82c0862288c190a0294c1bd830750c0cb02a098290c1bd830758c03452d08320aac228862c0a42a0a5298a1282c1bd830742c837b060ea1a0dec183a179100c0ac703029860c060b21830182c16f648da1ac505c0c5926565854181c1a100c0e04025c4ba208f4409e880bd0807,0xc50a422e20d0101a5090a908b88b05c45b44171863105c4585c61c14171873101a308622ea4c3088a188ba8b01a609422e38c068c222b0242b0a989a2588e2188ba831e0298baa35d5a787b0316c980cd0c0c0acf670d06f60c1d4b1ece18306320dec183a978101815bd9030a218b0306f60c1d530527b,0x30a628a2c7828678216c0b0a3c10b0c8f642c0c298f642c0c0d8a2835a780ac180c904156040abd9c301af652c711ece18c406b02f662c18bd90302ac0bd95308a0a862c0a42f650c0a81a8288ac086290bd90b142428320aa42c0a821880d82bd9830311418614506f658da1ac505c0c59a60b8cb1422e3,0x9ece18185300c0de14d0ac20c80c0d80c29a42f050c0c80c0d80c29bc1030516180c0d80c29a42f042da05029160a2c3032908a0c303250a422820c141870114a508320a2c342a4a06642808a08b015171862845c45a020606c14186141170505c4185c4582a1145d61a020b88b828620614c3088a030360,0x18533c10368140a41828b0c0606c0614d69e02b163420c9040cbc1c36140a9ece18181b00c0dbc18b03203036f052c034f662c827b2967b386188185300c0d80c29bc103051458516180c0d80c29a42f050da0502986382d0832065e0e18384301da19ece18181b03203036fef00e1d4b02a7b3167b29618,0x51460d05011820634c60a820606c030372500606de0c1c849098206c4dfde01c3a860b0c30b02b0b2830b2930b0e3484d10b24b0b2a37f82787b0a07031ea99918981312923031308d0c8c0607068100a332c68140a6580c0d80606d69e02b86358b8532cb4f615c3030a63c14b3c1c30181b1eca59ece18,0x81981066866040cd0de0e180cd0c020acf470c1008283609083092c318224a0d010594182010506c04020a0dc85f9e0183a866048c030182cc3007686416041c219e08198103b43783860540ed0cf670c0c0d81503b433d9c3031a6189b038710c0d8981901b13018d36040606dfde01c3a963056106581,0x804141b01008283654180c1c43060302d8604020a0d9224360770c10418219e],0),(36,[4,17,20,34],[0x140606c0614cf050c089eca181813002f042c00a0203026f040da05029060a0c3002408a0830181b05041c04171060614c171862045c41818131e08180c098a2835a780ac1806016010440c18c00c1bd830750c06016f640c0081280c1bd830742cf648da1ac505c0c5926565854181c1a100c0e04025c4b,0x3010182182010506de08182420c030260402140b00804281624a0c02010a05c8401016165060804141b0020181302010a05c05f9e0183a866048c030182cc300606c025a780ae180c298010181b018533c14368140a618013c10b018533c14368140a45801358b8530c7b216d62e148b00211030261e0e18,0x2010506c011224360770c03036030260402140b00204020a0d80606cb4f015c30220604c080428161e0e180c0981008502c0804141b00280bc10366120a419506030710c00400904182180c10c10082836038436040ed0cf070c070860606c06086088181302010a0580c10c07086030260402140b00],0),(37,[4,17,20,34],[0x10366120a419506030710c004182180e10c0604c080428160040402140b782060022420c030260402140b7e78060ea19812300c060b30c0080168140a6180168140a45801030260040604cf040da05029060042820c0604d69e02b063d90341bd830750da1ac505c0c5926565854181c1a100c0e04025c4b,0x4030260402140b0020181302010a0580402140b3c],20)]:=⟨oE,by decide+kernel⟩
def Vp:=C BE 2 [4,17,20,34] 2
def S17:=(O 1 4 [0,5] (O 2 4 [0,5] (O 4 4 [0,5] (O 8 20 [5,1] (O 9 20 [0,5] (O 10 20 [0,5] (O 12 20 [0,5] (O 16 20 [5,1] (O 17 20 [0,5] (O 18 20 [0,5] (O 20 20 [0,5] (O 32 20 [5,1] (O 33 20 [0,5] (O 34 20 [0,5] (O 36 20 [0,5] (O 64 20 [5,1] (O 65 20 [0,5] (O 66 20 [0,5] (O 68 20 [0,5] (N 25 [1,2,13,14,12,24,25,26,97,98,96,36,37,38,48,49,50] (N 42 [3,7,10,123,120,130,127] (J 0) (J 1)) (J 2)))))))))))))))))))))
abbrev t17:=LC Vp GE PE S17 0 0
lemma c20:t17 0 3:=Tc oE [[0x1ac5c480d242c143406a5406964068e406c6460a640a81b2902a06a52d101a3086160867023f81b3f96302a0696203432fe60c0364258b270a2ca8c5e780ad192106406f0406e140ab459a297859e059a60b02b0b0e301a2ca2c068b22b434068b2931e0a59e0699e04d83205581780362ca0d79e02b0731,0x2435154068e4069c58a0352170581234b2185812832101ac9242c5589214a52543519254068d40695406a42192427124259242392429901a90ac582504a0c8406d25a22c8ace0b4246a4a6498a4a8150640d9080d0552115525435820540d30652034154852568806b04c549406b472201ac12c52901ad10,0x42c0a82c10a815035c11354901b4501a5918206d052a0540d28381302a0b05622840d01ac0d0406d24c0a82a4b04e20540d604037034101b49688b24b1420c80d6068205581035859080d4852a4852506592485294948d13430867820352150532284a54a406b2450f04e2035810c34101ac91c80d065255,0x22c0ac069822c38f022ca0c0501b1a0e0b61a1a908594585949981484556250d6145941b446b1a6069c103416b8206d0406a64068e406a42196b1867040d0654903206e040b7020c81b412820cc35acc18c17058562460e04b2034c162585183812a80d604a0b04a0941608b2a11a941704a0a8450a83811,0x4585580d160d603458598192840d2943916056034c1161c721032069926286a4680d2a8190342a1a4190341590869035210641560921054c1868c1064150371203521305895880d30521624554c8c1685211652a3041903435054b1c280d484c125589614e205869c842c2cc2c26c0d0b06b01a2c2ac0698,0x182e08aa1a9321c8b0c300d5080d608b02b182e08b0b301ad085a4a8aa1c86a30432034c10a8c12c8b2c30320698a0a815035824ab122ca2c0682a608726292ac4932c28b29305815858c59830d142d0ac2035a1585820370a3068a306920361a2c38c16136165260685a03],[0xa420ab22388aa05521608185b8c9216251901bc101b150328d0324d243912429901a909c406a82392820cb822d302a080d908540c81a3882ac8b1406a42c096406a42a0a5406a42e0b025501a90b824689a628b23501d2581a504190541d2180e16d320385b4a921070e603521070d6c103436fef00e1d43,0x82a9093406a4260e440698290a4a7118206a42929546081a9091a5902d608320682a38d14155823489a1c86a168320642a3041a0372201ac138d040d899210e5c1032c502a908181b242a081b1302a908191b242c08189b006c4c1d2180e1cc0c0d80c8d80d03136c10329082ac88aa3880d485820634c30,0x582388185b1820cb821a8e20a8181b928783178128ac0981a0bc183182990c2390c21858219032c096460a820646c60832c08189b182e092a2c8aa1c8e20c818d3182e086a0c8e20616c60b820c92a1c8b22a8193886a0642a0606e420b419034150e43501b2501ac50d20c82a06c843482a9081a0cb0460,0x614390d46086460d1416ac2608338105a0c982c0d0460a8271031a6305c1033a11836118295182551820c9c460ac23500c2d982d0ac2150320a9838505a0c82a60d14d08320a9821ab0b412c20c82a6086aa2a83810303603341032a0e04c0a821cb040cb02591820646c0cb020626c0e582388320634c06,0x2a605c1055456443507496f0f6061d1b342b08721843203b43264190e582305612c8193070a314193068a30419685450323630419585855140c4d83968419032c10189b614990191ba08c1065610d5850334503260d040c2d8c5064c10e4990191b5140c8185b1640185b6083341032a08189bc0816b0561,0x15450320ae040c0d8030b781018d30181b928610181b018d38c81903525054c55147103626fef00e1d4b01ca582a3880d0540e52f0205581070b60385b0394bc88156041c3980d06581070d658419704593021501a0ae44c09540a8e40c8d41da180e16c0ed0c0e52e1a0385b0394b03b438c80e52c0ed0e,0xb0ee18f670c1c3981b130320a8e205742c2869064151c5ece18f670f120341501af670c4d16455c08193d9c362722140e061c5b00c0d81c3980c6980634c0606c1da181503b430362602a61585810a07030e2dbc133032b0b0aa2819031360640c2d8c50640626c0616f023141960471031a60b419584156,0x6040e1cc0c82a0606c0c82a070e60634c067020640c6987260415030360ed0cc0981076865841c3981503b430303603b430540e1cc0c69bc1c30c4158c47180ed0c1564471314d7],[0x301a0c0e021c6b434028adf1e1e810085a36092c302010516c010d6010560804141b302608020ac1008283624a0c092835a780ac18100828b604020a0dc84608041580435804958020ae820082bc080d0082b90890a0b02010b26c010d6010566080d1617010e5582010586df9e0183a866048c030182cc3,0x1e102010506c04020a0d9224360770c010560082b5a7a0ae18fef6141d1b3d9c36a6b161701165597151607060804050302011716c0668603343783860082b0334300415bd1c304020a0d8020ada100415bd1c300415e04202818100858b60082b0334]]
theorem Z1k:FBO Vp 0 0:=Tz oE c20
lemma k30:KOk BF GF PF [(32,[4,5,17,18,22,24],[0x0],1179648),(33,[4,5,17,18,22,24],[0x21e7875e1b7],0),(66,[4,5,17,18,22,24],[0x899e257811e237809e017],0),(67,[4,5,17,18,22,24],[0x440c78814e8852e107],0),(36,[4,5,17,18,22,24],[0x8b268852e287],0),(37,[4,5,17,18,22,24],[0x8c9a214b],0),(38,[4,5,17,18,22,24],[0x1],0),(39,[4,5,17,18,22,24],[0x1],0),(40,[4,5,17,18,22,24],[0x1],0),(41,[4,5,17,18,22,24],[0x0],18)]:=⟨oF,by decide+kernel⟩
end UCC
namespace UP
open Finset UnionClosed UC
open List (not_mem_nil nodup_cons getElem_mem mem_of_getElem contains_eq_mem getElem_map)
open Option (getD_some isSome_iff_exists)
def mkWf (ms:LF) (ws:LN) (wo:Nat) (a:Fin 12):Nat:=
 match Z3N ms a with
 | none=>wo
 | some i=>ws.getD i 0
lemma Z1y (ms:LF) (ws:LN) (wo:Nat) {a:Fin 12} (ha:a∉ms):
 mkWf ms ws wo a=wo:=by
 rw[mkWf,(Xw ms a).mpr ha]
lemma Z3d (ms:LF) (hn:ms.Nodup) (ws:LN) (hlen:ws.length=ms.length)
 (wo:Nat):ms.map (mkWf ms ws wo)=ws:=by
 apply List.ext_getElem (by simp[hlen]);intro i h1 h2
 have v0:i < ms.length:=by simpa using h1
 have v1:i < ws.length:=by simpa[hlen] using v0
 simp only[ql,mkWf,Q7 ms hn i v0];simp[List.getD_eq_getElem?_getD,v1]
lemma Zy (f:WF):
 ∀ (l:LF),l.Nodup->∑ a∈l.toFinset,f a=(l.map f).sum
 | [],_=>by simp
 | x :: xs,hnd=>by
  rw[q4] at hnd
  have hx:x∉xs.toFinset:=by simpa[qM] using hnd.1
  simp only[List.toFinset_cons,sum_insert hx,List.map_cons,List.sum_cons];rw[Zy f xs hnd.2]
lemma Z4n (ms:LF) (hn:ms.Nodup) (ws:LN) (hlen:ws.length=ms.length)
 (wo:Nat):(∑ a:Fin 12,mkWf ms ws wo a)=ws.sum+(12-ms.length)*wo:=by
 have v0:ms.toFinset.card=ms.length:=qT hn
 have v1:ms.toFinsetᶜ.card=12-ms.length:=by rw[qu,qCf,v0]
 have v4:Disjoint ms.toFinset ms.toFinsetᶜ:=disjoint_compl_right
 have v3:ms.toFinset∪ms.toFinsetᶜ=univ:=by
  ext x;simp
 rw[← v3,sum_union v4]
 have v5:∑ a∈ms.toFinset,mkWf ms ws wo a=ws.sum:=by rw[Zy (mkWf ms ws wo) ms hn,Z3d ms hn ws hlen wo]
 have v6:∑ a∈ms.toFinsetᶜ,mkWf ms ws wo a=(12-ms.length)*wo:=by
  have v2:∑ a∈ms.toFinsetᶜ,mkWf ms ws wo a=∑ _a∈ms.toFinsetᶜ,wo:=
   qh rfl (fun a ha=>Z1y ms ws wo (fun hm=>
    (mem_compl.mp ha) (qM.mpr hm)))
  rw[v2,sum_const,smul_eq_mul,v1]
 rw[v5,v6]
lemma VD (ms:LF) (wf:WF) (wo:Nat)
 (hwo:∀ a∉ms,wf a=wo) (X:SF):
 (∑ i∈X,wf i)=(X \ ms.toFinset).card*wo+∑ i∈X∩ms.toFinset,wf i:=by
 have v0:X=(X \ ms.toFinset)∪(X∩ms.toFinset):=(qSu X ms.toFinset).symm
 conv_lhs=>rw[v0]
 rw[sum_union (disjoint_sdiff_inter X ms.toFinset)];congr 1;have v1:∑ i∈X \ ms.toFinset,wf i=∑ _i∈X \ ms.toFinset,wo:=
  qh rfl (fun i hi=>hwo i (fun hm=>(qSd.mp hi).2 (qM.mpr hm)))
 rw[v1,sum_const,smul_eq_mul]
lemma ZR (F:SS) (ms:LF)
 (wf:WF) (wo W:Nat) (hwo:∀ a∉ms,wf a=wo):
 (∑ X∈F,(2*((∑ i∈X,wf i:Nat):Int)-(W:Int)))=
  ∑ K∈ms.toFinsetᶜ.powerset,∑ A∈pF F ms.toFinset K,
   (2*((K.card*wo+∑ i∈A,wf i:Nat):Int)-(W:Int)):=by
 have v1:∀ X∈F,X \ ms.toFinset∈ms.toFinsetᶜ.powerset:=fun X _=>
  q7.mpr (fun i hi=>mem_compl.mpr (qSd.mp hi).2)
 rw[show (∑ X∈F,(2*((∑ i∈X,wf i:Nat):Int)-(W:Int)))=
  ∑ X∈F,(2*(((X \ ms.toFinset).card*wo+∑ i∈X∩ms.toFinset,wf i:Nat):Int)-
   (W:Int)) from qh rfl (fun X _=>by rw[VD ms wf wo hwo X])]
 rw[← qj v1];apply qh rfl;intro K _;have v0:Set.InjOn (fun X:SF=>X∩ms.toFinset)
  (F.filter (fun X=>X \ ms.toFinset=K):Set (SF)):=by
  intro X₁ hX₁ X₂ hX₂ heq;dsimp only at heq;have hK₁:X₁ \ ms.toFinset=K:=(qF.mp hX₁).2;have hK₂:X₂ \ ms.toFinset=K:=(qF.mp hX₂).2
  calc X₁=(X₁ \ ms.toFinset)∪(X₁∩ms.toFinset):=(qSu X₁ _).symm
   _=K∪(X₂∩ms.toFinset):=by rw[hK₁,heq]
   _=(X₂ \ ms.toFinset)∪(X₂∩ms.toFinset):=by rw[hK₂]
   _=X₂:=qSu X₂ _
 dsimp[pF];rw[sum_image v0];exact qh rfl (fun X hX=>by rw[(qF.mp hX).2])
lemma fIS (F:SS) (w:WF)
 (hsh:(0:Int)≤ ∑ X∈F,(2*((∑ i∈X,w i:Nat):Int)-((∑ i,w i:Nat):Int))):
 F.card*(∑ i,w i)≤ 2*(∑ X∈F,∑ i∈X,w i):=by
 have v0:(∑ X∈F,(2*((∑ i∈X,w i:Nat):Int)-((∑ i,w i:Nat):Int)))=
  2*((∑ X∈F,∑ i∈X,w i:Nat):Int)-((F.card*(∑ i,w i):Nat):Int):=by
  rw[sum_sub_distrib,← mul_sum];simp[sum_const,Nat.cast_sum,Nat.cast_mul]
 rw[v0] at hsh;omega
lemma mPF {F:SS} {M X:SF} (hXF:X∈F):
 X∩M∈pF F M (X \ M):=
 qI.mpr ⟨X,qF.mpr ⟨hXF,rfl⟩,rfl⟩
lemma Z4 {F:SS} (h0:∅∈F) (M:SF):
 ∅∈pF F M ∅:=by
 simpa using mPF h0 (M:=M)
lemma Z2 {F:SS} {M K:SF}
 (hK:K∈F) (hKM:K⊆Mᶜ):∅∈pF F M K:=by
 have v0:Disjoint K M:=disjoint_left.mpr (fun a haK haM=>(mem_compl.mp (hKM haK)) haM);have h1:K \ M=K:=sdiff_eq_left.mpr v0;have h2:K∩M=∅:=disjoint_iff_inter_eq_empty.mp v0;simpa[h1,h2] using mPF hK (M:=M)
lemma Z6 {F:SS} (huniv:univ∈F)
 (M:SF):M∈pF F M Mᶜ:=by
 have h1:(univ:SF)\ M=Mᶜ:=by ext x;simp
 have h2:(univ:SF)∩M=M:=univ_inter M;simpa[h1,h2] using mPF huniv (M:=M)
lemma XV {cf:Cfg} {tP tN:Nat}
 (hok:VW cf tP tN)
 {ms:LF} (hn:ms.Nodup) (hr:ms.length=cf.r)
 (hwl:cf.ws.length=cf.r)
 {F:SS} (huc:iUC F)
 (hlow:cf.mS≠0->∀ X∈F,X.Nonempty->cf.mS≤ X.card)
 (jC:∀ t∈cf.tg,t≠0->¬ Z3r t F)
 (hgF:∀ g∈cf.gS,Z3L ms g∈F)
 {K:SF} (hK:K⊆ms.toFinsetᶜ) (hk:K.card=cf.k)
 (hcp:cf.uC≠0->
  ((pF F ms.toFinset K).filter (fun A=>A.card=1)).card≤
   (if cf.uC=2 then 3 else 2))
 (hbot:cf.mS≠0->(cf.k=0∨cf.fE=true)->∅∈pF F ms.toFinset K)
 (htop:cf.mS≠0->cf.k=12-cf.r->ms.toFinset∈pF F ms.toFinset K)
 (hno0:cf.fN=true->∅∉pF F ms.toFinset K):
 (tP:Int)-(tN:Int)≤ ∑ A∈pF F ms.toFinset K,
  (2*((K.card*cf.wo+∑ i∈A,mkWf ms cf.ws cf.wo i:Nat):Int)-
   (cf.W:Int)):=by
 let wf:=mkWf ms cf.ws cf.wo
 have v0:(ms++K.toList).Nodup:=by
  rw[qV];refine ⟨hn,K.nodup_toList,fun a ha b hb heq=>?_⟩;subst heq;exact (mem_compl.mp (hK (qp.mp hb))) (qM.mpr ha)
 have v1:K.toList.toFinset=K:=by ext x;simp
 have v2:Z3Z cf ms K.toList wf F (pF F ms.toFinset K):=by
  refine ⟨v0,hr,?_,?_,huc,hlow,jC,fun _=>hgF,?_,?_,?_,?_,?_⟩
  · rw[q3,hk]
  · exact (Z3d ms hn cf.ws (hr ▸ hwl) cf.wo).symm
  · simp
  · intro g hg A hA;exact projFiber_op huc (hgF g hg) (Yg ms g) K A hA
  · intro hms A hA
    obtain ⟨X,hXf,rfl⟩:=qI.mp hA;obtain ⟨hXF,hXK⟩:=qF.mp hXf;by_cases hXe:X=∅
    · subst hXe;left
      have v4:K=∅:=by simpa using hXK.symm
      exact ⟨by rw[← hk,v4,card_empty],by simp⟩
    · right
      have hcardX:X.card=K.card+(X∩ms.toFinset).card:=by
       have h1:=(qSu X ms.toFinset).symm;have h2:=disjoint_sdiff_inter X ms.toFinset
       calc X.card=((X \ ms.toFinset)∪(X∩ms.toFinset)).card:=congrArg card h1
        _=(X \ ms.toFinset).card+(X∩ms.toFinset).card:=qCu h2
        _=K.card+(X∩ms.toFinset).card:=by rw[hXK]
      have:=hlow hms X hXF (qNe.mpr hXe);omega
  · simpa[v1] using hcp
  · exact hno0
 have v3:=hok ms K.toList wf F (pF F ms.toFinset K)
  v2 hbot (by simpa[v1] using htop)
 simpa[hk] using v3
lemma ZD {F:SS} {M:SF}
 (hFM:∀ A∈F,A⊆M):pF F M ∅=F:=by
 ext A;simp only[pF,qI,qF];constructor
 · rintro ⟨X,⟨hXF,_⟩,rfl⟩
   rwa[inter_eq_left.mpr (hFM X hXF)]
 · intro hAF;refine ⟨A,⟨hAF,qi.mpr (hFM A hAF)⟩,inter_eq_left.mpr (hFM A hAF)⟩
lemma VE {cf:Cfg} (hok:VW cf 0 0)
 (hm0:cf.mS=0) (hk0:cf.k=0) (ht:cf.tg=[]) (huc0:cf.uC=0)
 (hfne:cf.fN=false) (hwo0:cf.wo=0)
 {ms:LF} (hn:ms.Nodup) (hr:ms.length=cf.r)
 (hwl:cf.ws.length=cf.r)
 {F:SS} (huc:iUC F)
 (hgF:∀ g∈cf.gS,Z3L ms g∈F)
 (K:SF):
 (0:Int)≤ ∑ A∈pF F ms.toFinset K,
  (2*((K.card*cf.wo+∑ i∈A,mkWf ms cf.ws cf.wo i:Nat):Int)-
   (cf.W:Int)):=by
 let wf:=mkWf ms cf.ws cf.wo;let FK:=pF F ms.toFinset K;have v3:iUC FK:=fun A hA B hB=>by
  obtain ⟨X,hXf,rfl⟩:=qI.mp hA;obtain ⟨Y,hYf,rfl⟩:=qI.mp hB;obtain ⟨hXF,hXK⟩:=qF.mp hXf;obtain ⟨hYF,hYK⟩:=qF.mp hYf;refine qI.mpr ⟨X∪Y,qF.mpr ⟨huc X hXF Y hYF,?_⟩,?_⟩
  · rw[union_sdiff_distrib,hXK,hYK,union_idempotent]
  · exact qq X Y ms.toFinset
 have v1:(ms++([]:LF)).Nodup:=by simpa using hn
 have v2:∀ A∈FK,A⊆ms.toFinset:=pFS F ms.toFinset K
 have v4:Z3Z cf ms [] wf FK FK:=by
  refine ⟨v1,hr,?_,?_,v3,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp[hk0]
  · exact (Z3d ms hn cf.ws (hr ▸ hwl) cf.wo).symm
  · intro hms;exact False.elim (hms hm0)
  · intro t htm;rw[ht] at htm;simp at htm
  · intro hms;exact False.elim (hms hm0)
  · simp only[List.toFinset_nil];exact (ZD v2).symm
  · intro g hg A hA;exact projFiber_op huc (hgF g hg) (Yg ms g) K A hA
  · intro hms;exact False.elim (hms hm0)
  · intro hu;exact False.elim (hu huc0)
  · intro hf;rw[hfne] at hf;simp at hf
 have v0:=hok ms [] wf FK FK v4
  (fun hms=>False.elim (hms hm0)) (fun hms=>False.elim (hms hm0))
 dsimp only[FK,wf] at v0;simp only[CharP.cast_eq_zero,sub_zero,hwo0,mul_zero,zero_add] at v0 ⊢;exact v0
lemma ZS {F:SS} {M K A:SF}
 (hA:A∈pF F M K):A∪K∈F:=by
 obtain ⟨X,hXf,rfl⟩:=qI.mp hA;obtain ⟨hXF,hXK⟩:=qF.mp hXf
 have v0:(X∩M)∪K=X:=by rw[← hXK,union_comm,qSu]
 rwa[v0]
lemma Zd {α:Type*} [DecidableEq α] {S:Finset α} (h3:3≤ S.card):
 ∃ x y z,x∈S∧y∈S∧z∈S∧x≠y∧x≠z∧y≠z:=by
 obtain ⟨T,hTS,hTc⟩:=exists_subset_card_eq h3;have hnd:=T.nodup_toList
 have v0:T.toList.length=3:=by rw[q3,hTc]
 rcases hL:T.toList with _|⟨x,_|⟨y,_|⟨z,_|_⟩⟩⟩<;>simp[hL] at v0
 rw[hL] at hnd;simp only[q4,qC,qNm,qs,not_or,
  not_false_eq_true,List.nodup_nil,and_true] at hnd
 refine ⟨x,y,z,hTS (qp.mp (hL ▸ qG)),
  hTS (qp.mp (hL ▸ by simp)),hTS (qp.mp (hL ▸ by simp)),
  hnd.1.1,hnd.1.2,hnd.2⟩
lemma Zq {α:Type*} [DecidableEq α] {S:Finset α} (h4:4≤ S.card):
 ∃ x y z w,x∈S∧y∈S∧z∈S∧w∈S∧
  x≠y∧x≠z∧x≠w∧y≠z∧y≠w∧z≠w:=by
 obtain ⟨T,hTS,hTc⟩:=exists_subset_card_eq h4;have hnd:=T.nodup_toList
 have v0:T.toList.length=4:=by rw[q3,hTc]
 rcases hL:T.toList with _|⟨x,_|⟨y,_|⟨z,_|⟨w,_|_⟩⟩⟩⟩<;>simp[hL] at v0
 rw[hL] at hnd;simp only[q4,qC,qNm,qs,not_or,
  not_false_eq_true,List.nodup_nil,and_true] at hnd
 refine ⟨x,y,z,w,hTS (qp.mp (hL ▸ qG)),
  hTS (qp.mp (hL ▸ by simp)),hTS (qp.mp (hL ▸ by simp)),
  hTS (qp.mp (hL ▸ by simp)),
  hnd.1.1,hnd.1.2.1,hnd.1.2.2,hnd.2.1.1,hnd.2.1.2,hnd.2.2⟩
lemma Xi {F:SS} (hq3:¬ Z5g F)
 {M K:SF} (hK:K⊆Mᶜ) (hk2:K.card=2):
 ((pF F M K).filter (fun A=>A.card=1)).card≤ 2:=by
 by_contra hgt;obtain ⟨A1,A2,A3,h1,h2,h3,h12,h13,h23⟩:=
  Zd (S:=(pF F M K).filter (fun A=>A.card=1)) (by omega)
 obtain ⟨h1p,h1c⟩:=qF.mp h1;obtain ⟨h2p,h2c⟩:=qF.mp h2;obtain ⟨h3p,h3c⟩:=qF.mp h3;obtain ⟨x1,rfl⟩:=qC1.mp h1c;obtain ⟨x2,rfl⟩:=qC1.mp h2c;obtain ⟨x3,rfl⟩:=qC1.mp h3c;have v7:x1≠x2:=fun h=>h12 (by rw[h]);have v2:x1≠x3:=fun h=>h13 (by rw[h]);have v3:x2≠x3:=fun h=>h23 (by rw[h]);have hm1:x1∈M:=(pFS F M K _ h1p) (qMs _);have hm2:x2∈M:=(pFS F M K _ h2p) (qMs _);have hm3:x3∈M:=(pFS F M K _ h3p) (qMs _);have v0:x1∉K:=fun h=>(mem_compl.mp (hK h)) hm1;have v1:x2∉K:=fun h=>(mem_compl.mp (hK h)) hm2;have v5:x3∉K:=fun h=>(mem_compl.mp (hK h)) hm3
 have hX1:insert x1 K∈F:=by simpa[singleton_union] using ZS h1p
 have hX2:insert x2 K∈F:=by simpa[singleton_union] using ZS h2p
 have hX3:insert x3 K∈F:=by simpa[singleton_union] using ZS h3p
 have hc1:(insert x1 K).card=3:=by rw[card_insert_of_notMem v0,hk2]
 have hc2:(insert x2 K).card=3:=by rw[card_insert_of_notMem v1,hk2]
 have hc3:(insert x3 K).card=3:=by rw[card_insert_of_notMem v5,hk2]
 have v8:insert x1 K≠insert x2 K:=fun heq=>v0 (by
  have:=mem_insert_self x1 K;rw[heq] at this;exact (qo.mp this).resolve_left v7)
 have v9:insert x1 K≠insert x3 K:=fun heq=>v0 (by
  have:=mem_insert_self x1 K;rw[heq] at this;exact (qo.mp this).resolve_left v2)
 have v4:insert x2 K≠insert x3 K:=fun heq=>v1 (by
  have:=mem_insert_self x2 K;rw[heq] at this;exact (qo.mp this).resolve_left v3)
 have hu:(insert x1 K∪insert x2 K∪insert x3 K).card≤ 5:=by
  have v6:insert x1 K∪insert x2 K∪insert x3 K⊆insert x1 (insert x2 (insert x3 K)):=by
   intro a ha;simp only[mem_union,qo] at ha ⊢;tauto
  have hc:=(qL v6).trans (card_insert_le _ _);have hc':=hc.trans (Nat.add_le_add_right (card_insert_le _ _) 1);have hc'':=hc'.trans (Nat.add_le_add_right (Nat.add_le_add_right (card_insert_le _ _) 1) 1);omega
 exact hq3 ⟨_,hX1,_,hX2,_,hX3,v8,v9,v4,hc1,hc2,hc3,hu⟩
lemma YA {F:SS} (hf12:uN 12 F)
 {M K:SF} (hK:K⊆Mᶜ) (hk3:K.card=3):
 ((pF F M K).filter (fun A=>A.card=1)).card≤ 2:=by
 by_contra hgt;obtain ⟨A1,A2,A3,h1,h2,h3,h12,h13,h23⟩:=
  Zd (S:=(pF F M K).filter (fun A=>A.card=1)) (by omega)
 obtain ⟨h1p,h1c⟩:=qF.mp h1;obtain ⟨h2p,h2c⟩:=qF.mp h2;obtain ⟨h3p,h3c⟩:=qF.mp h3;obtain ⟨x1,rfl⟩:=qC1.mp h1c;obtain ⟨x2,rfl⟩:=qC1.mp h2c;obtain ⟨x3,rfl⟩:=qC1.mp h3c;have hm1:x1∈M:=(pFS F M K _ h1p) (qMs _);have hm2:x2∈M:=(pFS F M K _ h2p) (qMs _);have hm3:x3∈M:=(pFS F M K _ h3p) (qMs _);rcases hKL:K.toList with _|⟨k0,_|⟨k1,_|⟨k2,_|_⟩⟩⟩
 · have:=K.length_toList;rw[hKL] at this;simp[hk3] at this
 · have:=K.length_toList;rw[hKL] at this;simp[hk3] at this
 · have:=K.length_toList;rw[hKL] at this;simp[hk3] at this
 swap
 · have:=K.length_toList;rw[hKL] at this;simp[hk3] at this
 have v3:=K.nodup_toList;rw[hKL] at v3;have v2:∀ z∈[k0,k1,k2],z∈K:=fun z hz=>qp.mp (hKL ▸ hz);have v8:x1≠x2:=fun h=>h12 (by rw[h]);have v7:x1≠x3:=fun h=>h13 (by rw[h]);have v4:x2≠x3:=fun h=>h23 (by rw[h]);let ms':=[k0,k1,k2,x1,x2,x3]
 have v5:ms'.Nodup:=by
   rw[show ms'=[k0,k1,k2]++[x1,x2,x3] from rfl,qV];refine ⟨v3,by simp[v8,v7,v4],fun a ha b hb v0=>?_⟩;subst v0;have v9:a∈K:=v2 a ha
   have hbM:a∈M:=by
    simp only[qC,qNm,qs] at hb
    rcases hb with rfl|rfl|rfl<;>assumption
   exact (mem_compl.mp (hK v9)) hbM
 have v6:({k0,k1,k2}:SF)=K:=by
   ext a;simp only[qo,qb];have:=qp (a:=a) (s:=K);rw[hKL] at this;simpa[qC] using this
 have v1:∀ n:Nat,n % 8=7->Z3L [k0,k1,k2] n=K:=by
   intro n hn7
   have h1:n % 2=1:=by omega
   have h2:(n/2)% 2=1:=by omega
   have h3:(n/2/2)% 2=1:=by omega
   simp only[Z3L,h1,h2,h3,↓reduceIte];simpa[Z3L] using v6
 apply hf12 ⟨by decide,ms',v5,by simp[ms',Z4Y],fun g hg=>?_⟩;simp only[Z3Q,qC,qNm,qs] at hg;rcases hg with rfl|rfl|rfl
 · have v0:Z3L ms' 15={x1}∪K:=by
    rw[show ms'=[k0,k1,k2]++[x1,x2,x3] from rfl,Yh,v1 15 rfl];simp[Z3L,union_comm]
   rw[v0];exact ZS h1p
 · have v0:Z3L ms' 23={x2}∪K:=by
    rw[show ms'=[k0,k1,k2]++[x1,x2,x3] from rfl,Yh,v1 23 rfl];simp[Z3L,union_comm]
   rw[v0];exact ZS h2p
 · have v0:Z3L ms' 39={x3}∪K:=by
    rw[show ms'=[k0,k1,k2]++[x1,x2,x3] from rfl,Yh,v1 39 rfl];simp[Z3L,union_comm]
   rw[v0];exact ZS h3p
lemma Xj {F:SS} (hf8:uN 8 F)
 {M K:SF} (hK:K⊆Mᶜ) (hk3:K.card=3):
 ((pF F M K).filter (fun A=>A.card=1)).card≤ 3:=by
 by_contra hgt;obtain ⟨A1,A2,A3,A4,h1,h2,h3,h4,h12,h13,h14,h23,h24,h34⟩:=
  Zq (S:=(pF F M K).filter (fun A=>A.card=1)) (by omega)
 obtain ⟨h1p,h1c⟩:=qF.mp h1;obtain ⟨h2p,h2c⟩:=qF.mp h2;obtain ⟨h3p,h3c⟩:=qF.mp h3;obtain ⟨h4p,h4c⟩:=qF.mp h4;obtain ⟨x1,rfl⟩:=qC1.mp h1c;obtain ⟨x2,rfl⟩:=qC1.mp h2c;obtain ⟨x3,rfl⟩:=qC1.mp h3c;obtain ⟨x4,rfl⟩:=qC1.mp h4c;have hm1:x1∈M:=(pFS F M K _ h1p) (qMs _);have hm2:x2∈M:=(pFS F M K _ h2p) (qMs _);have hm3:x3∈M:=(pFS F M K _ h3p) (qMs _);have hm4:x4∈M:=(pFS F M K _ h4p) (qMs _);rcases hKL:K.toList with _|⟨k0,_|⟨k1,_|⟨k2,_|_⟩⟩⟩
 · have:=K.length_toList;rw[hKL] at this;simp[hk3] at this
 · have:=K.length_toList;rw[hKL] at this;simp[hk3] at this
 · have:=K.length_toList;rw[hKL] at this;simp[hk3] at this
 swap
 · have:=K.length_toList;rw[hKL] at this;simp[hk3] at this
 have v3:=K.nodup_toList;rw[hKL] at v3;have v2:∀ z∈[k0,k1,k2],z∈K:=fun z hz=>qp.mp (hKL ▸ hz);have v11:x1≠x2:=fun h=>h12 (by rw[h]);have v10:x1≠x3:=fun h=>h13 (by rw[h]);have v8:x1≠x4:=fun h=>h14 (by rw[h]);have v6:x2≠x3:=fun h=>h23 (by rw[h]);have v4:x2≠x4:=fun h=>h24 (by rw[h]);have v5:x3≠x4:=fun h=>h34 (by rw[h]);let ms':=[k0,k1,k2,x1,x2,x3,x4]
 have v7:ms'.Nodup:=by
   rw[show ms'=[k0,k1,k2]++[x1,x2,x3,x4] from rfl,qV];refine ⟨v3,by simp[v11,v10,v8,v6,v4,v5],fun a ha b hb v0=>?_⟩;subst v0;have haK:a∈K:=v2 a ha
   have hbM:a∈M:=by
    simp only[qC,qNm,qs] at hb
    rcases hb with rfl|rfl|rfl|rfl<;>assumption
   exact (mem_compl.mp (hK haK)) hbM
 have v9:({k0,k1,k2}:SF)=K:=by
   ext a;simp only[qo,qb];have:=qp (a:=a) (s:=K);rw[hKL] at this;simpa[qC] using this
 have v1:∀ n:Nat,n % 8=7->Z3L [k0,k1,k2] n=K:=by
   intro n hn7
   have h1:n % 2=1:=by omega
   have h2:(n/2)% 2=1:=by omega
   have h3:(n/2/2)% 2=1:=by omega
   simp only[Z3L,h1,h2,h3,↓reduceIte];simpa[Z3L] using v9
 apply hf8 ⟨by decide,ms',v7,by simp[ms',Z4Y],fun g hg=>?_⟩;simp only[Z3Q,qC,qNm,qs] at hg;rcases hg with rfl|rfl|rfl|rfl
 · have v0:Z3L ms' 15={x1}∪K:=by
    rw[show ms'=[k0,k1,k2]++[x1,x2,x3,x4] from rfl,Yh,v1 15 rfl];simp[Z3L,union_comm]
   rw[v0];exact ZS h1p
 · have v0:Z3L ms' 23={x2}∪K:=by
    rw[show ms'=[k0,k1,k2]++[x1,x2,x3,x4] from rfl,Yh,v1 23 rfl];simp[Z3L,union_comm]
   rw[v0];exact ZS h2p
 · have v0:Z3L ms' 39={x3}∪K:=by
    rw[show ms'=[k0,k1,k2]++[x1,x2,x3,x4] from rfl,Yh,v1 39 rfl];simp[Z3L,union_comm]
   rw[v0];exact ZS h3p
 · have v0:Z3L ms' 71={x4}∪K:=by
    rw[show ms'=[k0,k1,k2]++[x1,x2,x3,x4] from rfl,Yh,v1 71 rfl];simp[Z3L,union_comm]
   rw[v0];exact ZS h4p
end UP
namespace UP
open Finset UnionClosed UC UCC
open List (not_mem_nil nodup_cons getElem_mem mem_of_getElem contains_eq_mem getElem_map)
open Option (getD_some isSome_iff_exists)
lemma YB {cf:Cfg} (hok:VW cf 0 0)
 (hm0:cf.mS=0) (hk0:cf.k=0) (ht:cf.tg=[]) (huc0:cf.uC=0)
 (hfne:cf.fN=false) (hwo0:cf.wo=0)
 (hwl:cf.ws.length=cf.r) (hW_pos:0 < cf.W)
 (hW_sum:cf.ws.sum=cf.W)
 {ms:LF} (hn:ms.Nodup) (hr:ms.length=cf.r)
 {F:SS} (huc:iUC F)
 (hgF:∀ g∈cf.gS,Z3L ms g∈F):
 ∃ w:WF,0 < ∑ i,w i∧
  F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i):=by
 let wf:=mkWf ms cf.ws 0
 have hsum:(∑ i:Fin 12,wf i)=cf.W:=by
  have:=Z4n ms hn cf.ws (hr ▸ hwl) 0;simpa[wf,hW_sum] using this
 refine ⟨wf,hW_pos.trans_eq hsum.symm,fIS F wf ?_⟩;have v0:∀ a∉ms,wf a=0:=fun a ha=>Z1y ms cf.ws 0 ha;rw[hsum,ZR F ms wf 0 cf.W v0];apply sum_nonneg;intro K _;have v1:=VE hok hm0 hk0 ht huc0 hfne hwo0 hn hr hwl huc hgF K;simpa[hwo0] using v1
lemma YC {cf:Cfg} (hok:VW cf 0 0)
 (hm0:cf.mS=0) (hk0:cf.k=0) (ht:cf.tg=[]) (huc0:cf.uC=0)
 (hfne:cf.fN=false) (hwo0:cf.wo=0)
 (hwl:cf.ws.length=cf.r) (hW_pos:0 < cf.W)
 (hW_sum:cf.ws.sum=cf.W)
 {F:SS} (huc:iUC F)
 {ms0:LF} (hn0:ms0.Nodup) (hr0:ms0.length=cf.r)
 {p:LN} (hpLen:p.length=cf.r) (hpNd:p.Nodup) (hpLt:∀ j∈p,j < cf.r)
 (hgF:∀ g∈cf.gS,Z3L ms0 (Z1J p g)∈F):
 ∃ w:WF,0 < ∑ i,w i∧
  F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i):=by
 let ms:=p.map (fun j=>ms0.getD j 0);have v0:∀ j∈p,j < ms0.length:=fun j hj=>hr0 ▸ hpLt j hj
 have hn:ms.Nodup:=by
  rw[qN];intro a b hab
  have ha:a.val < p.length:=by simpa[ms] using a.isLt
  have hb:b.val < p.length:=by simpa[ms] using b.isLt
  have v2:p[a.val]< ms0.length:=v0 _ (qd ha);have v1:p[b.val]< ms0.length:=v0 _ (qd hb);simp only[ms,ql,List.getD_eq_getElem?_getD,
   List.getElem?_eq_getElem v2,List.getElem?_eq_getElem v1,qt] at hab
  have v3:p[a.val]=p[b.val]:=
   Fin.val_eq_of_eq ((qN.mp hn0)
    (a₁:=⟨p[a.val],v2⟩) (a₂:=⟨p[b.val],v1⟩) hab)
  exact Fin.ext (congrArg (Fin.val:Fin p.length->Nat) ((qN.mp hpNd)
   (a₁:=⟨a.val,ha⟩) (a₂:=⟨b.val,hb⟩) v3))
 have hr:ms.length=cf.r:=by simp[ms,hpLen]
 refine YB hok hm0 hk0 ht huc0 hfne hwo0 hwl hW_pos hW_sum hn hr huc ?_;intro g hgg;rw[show ms=p.map (fun j=>ms0.getD j 0) from rfl,Zu ms0 p v0 g];exact hgF g hgg
def Z4o:List (LN):=
 let s:=[0,1,2,3]
 s.flatMap fun a=>(s.erase a).flatMap fun b=>
 ((s.erase a).erase b).flatMap fun c=>
 (((s.erase a).erase b).erase c).map fun d=>[a,b,c,d]
def Z4p:List (LN):=
 let s:=[0,1,2,3,4]
 s.flatMap fun a=>(s.erase a).flatMap fun b=>
 ((s.erase a).erase b).flatMap fun c=>
 (((s.erase a).erase b).erase c).flatMap fun d=>
 ((((s.erase a).erase b).erase c).erase d).map fun e=>[a,b,c,d,e]
def Xk (pS:List (LN)) (r:Nat) (gs ws:LN):Option (LN):=
 pS.find? (fun p=>p.length==r&&p.Nodup&&p.all (· < r)&&
  gs.all (fun g=>ws.contains (Z1J p g)))
def Z3e (m0 m1 m2:Nat):Nat × LN:=
 let ws:=[m0,m1,m2]
 match Xk Z4p 5 [7,11,19] ws with
 | some p=>(1,p)
 | none=>
  match Xk Z4p 5 [7,11,21] ws with
  | some p=>(2,p)
  | none=>
   match Xk Z4p 5 [7,11,28] ws with
   | some p=>(3,p)
   | none=>(0,[])
def Y5 (x:Nat):LN->Option (Nat × Nat)
 | []=>none
 | y :: ys=>if Z5o 6 (Z5r 6 x y)==2 then some (x,y) else Y5 x ys
def Xl:LN->Option (Nat × Nat)
 | []=>none
 | x :: xs=>
  match Y5 x xs with
  | some pr=>some pr
  | none=>Xl xs
def Z3F (m0 m1 m2 m3:Nat):Nat × LN:=
 let ws:=[m0,m1,m2,m3]
 match Xl ws with
 | some (x,y)=>
  let p:=Z1K 6 (Z5r 6 x y)++Z1K 6 (Z4X 6 x y)++
   Z1K 6 (Z4X 6 y x)++Z1K 6 (Z4X 6 63 (or7 x y))
  if p.length==6&&p.Nodup&&p.all (· < 6)&&
   [7,11,52,56].all (fun g=>ws.contains (Z1J p g)) then
   (0,p)
  else (2,[])
 | none=>
  let a0:=Z1K 6 (Z5r 6 m0 m1);let rx:=Z1K 6 (Z4X 6 m0 m1);let ry:=Z1K 6 (Z4X 6 m1 m0);let rz:=Z1K 6 (Z4X 6 63 (or7 m0 m1))
  match rx,ry with
  | [x0,x1],[y0,y1]=>
   let cands:=[a0++[x0,x1,y0,y1]++rz,a0++[x1,x0,y0,y1]++rz,
    a0++[x0,x1,y1,y0]++rz,a0++[x1,x0,y1,y0]++rz]
   match cands.find? (fun p=>p.length==6&&p.Nodup&&p.all (· < 6)&&
    [7,25,42,52].all (fun g=>ws.contains (Z1J p g))) with
   | some p=>(1,p)
   | none=>(2,[])
  | _,_=>(2,[])
lemma XW:
 let s3:=(List.range 16).filter (fun m=>Z5o 4 m==3)
 s3.all (fun m0=>
  let s1:=s3.filter (m0 < ·)
  s1.all (fun m1=>
   let s2:=s1.filter (m1 < ·)
   s2.all (fun m2=>
    (Xk Z4o 4 [7,11,13] [m0,m1,m2]).isSome)))=true:=by
 decide+kernel
lemma XX:
 let s3:=(List.range 32).filter (fun m=>Z5o 5 m==3)
 s3.all (fun m0=>
  let s1:=s3.filter (m0 < ·)
  s1.all (fun m1=>
   let s2:=s1.filter (m1 < ·)
   s2.all (fun m2=>
    !(Z5o 5 (or7 (or7 m0 m1) m2)==5)||
    let res:=Z3e m0 m1 m2;let gs:=if res.1==1 then [7,11,19] else if res.1==2 then [7,11,21] else [7,11,28]
    (res.1==1||res.1==2||res.1==3)&&
     res.2.length==5&&res.2.Nodup&&res.2.all (· < 5)&&
     gs.all (fun g=>[m0,m1,m2].contains (Z1J res.2 g)))))=true:=by
 decide+kernel
lemma XY:
 let s3:=(List.range 64).filter (fun m=>Z5o 6 m==3)
 s3.all (fun m0=>
  let s1:=s3.filter (m0 < ·)
  s1.all (fun m1=>
   let s2:=s1.filter (m1 < ·)
   s2.all (fun m2=>
    !(Z5o 6 (or7 (or7 m0 m1) m2)==6)||
    let s4:=s2.filter (m2 < ·)
    s4.all (fun m3=>
     !(Z5o 6 (or7 (or7 m0 m1) m3)==6&&
      Z5o 6 (or7 (or7 m0 m2) m3)==6&&Z5o 6 (or7 (or7 m1 m2) m3)==6)||
     let res:=Z3F m0 m1 m2 m3;let gs:=if res.1==0 then [7,11,52,56] else [7,25,42,52]
     (res.1==0||res.1==1)&&
      res.2.length==6&&res.2.Nodup&&res.2.all (· < 6)&&
      gs.all (fun g=>[m0,m1,m2,m3].contains (Z1J res.2 g))))))=true:=by
 decide+kernel
def Z5d (x:Nat):LN->LN
 | []=>[x]
 | y :: ys=>if x≤ y then x :: y :: ys else y :: Z5d x ys
def Z4U:LN->LN
 | []=>[]
 | x :: xs=>Z5d x (Z4U xs)
lemma Z3G (x z:Nat):∀ xs:LN,z∈Z5d x xs↔z=x∨z∈xs
 | []=>by simp[Z5d]
 | y :: ys=>by
  dsimp[Z5d];split_ifs
  · simp
  · simp only[qC,Z3G x z ys];tauto
lemma Z3f (z:Nat):∀ xs:LN,z∈Z4U xs↔z∈xs
 | []=>by simp[Z4U]
 | x :: xs=>by
  simp only[Z4U,Z3G,qC,Z3f z xs]
lemma VF (x:Nat):∀ xs:LN,(Z5d x xs).length=xs.length+1
 | []=>by simp[Z5d]
 | y :: ys=>by dsimp[Z5d];split_ifs<;>simp[VF x ys]
lemma XZ:∀ xs:LN,(Z4U xs).length=xs.length
 | []=>rfl
 | x :: xs=>by simp[Z4U,VF,XZ xs]
lemma Z1z (x:Nat):∀ {xs:LN},xs.Nodup->x∉xs->(Z5d x xs).Nodup
 | [],_,_=>List.nodup_singleton x
 | y :: ys,hnd,hnx=>by
  rw[q4] at hnd;simp only[qC,not_or] at hnx;dsimp[Z5d];split_ifs
  · exact q4.mpr ⟨by simp[hnx],q4.mpr hnd⟩
  · refine q4.mpr ⟨fun hmem=>?_,Z1z x hnd.2 hnx.2⟩
    rw[Z3G] at hmem;rcases hmem with rfl|hy
    · exact hnx.1 rfl
    · exact hnd.1 hy
lemma VG:∀ {xs:LN},xs.Nodup->(Z4U xs).Nodup
 | [],_=>List.nodup_nil
 | x :: xs,hnd=>by
  rw[q4] at hnd;exact Z1z x (VG hnd.2) (fun h=>hnd.1 ((Z3f x xs).mp h))
lemma Xm (x:Nat):∀ {xs:LN},xs.Pairwise (·≤ ·)->(Z5d x xs).Pairwise (·≤ ·)
 | [],_=>List.pairwise_singleton _ _
 | y :: ys,hp=>by
  rw[qJ] at hp;dsimp[Z5d]
  split_ifs with hxy
  · exact qJ.mpr ⟨fun z hz=>by
     rcases qC.mp hz with rfl|hzy
     · exact hxy
     · exact le_trans hxy (hp.1 z hzy),qJ.mpr hp⟩
  · refine qJ.mpr ⟨fun z hz=>?_,Xm x hp.2⟩
    rw[Z3G] at hz;rcases hz with rfl|hzy
    · omega
    · exact hp.1 z hzy
lemma YD:∀ xs:LN,(Z4U xs).Pairwise (·≤ ·)
 | []=>List.Pairwise.nil
 | x :: xs=>Xm x (YD xs)
lemma X_ {xs:LN} (hnd:xs.Nodup):(Z4U xs).Pairwise (· < ·):=by
 have hp:=YD xs;have hnd':=VG hnd;clear hnd
 generalize Z4U xs=l at hp hnd' ⊢;induction l with
 | nil=>exact List.Pairwise.nil
 | cons a as ih=>
  rw[qJ] at hp ⊢;rw[q4] at hnd';refine ⟨fun z hz=>?_,ih hp.2 hnd'.2⟩;have hle:=hp.1 z hz;have hne:a≠z:=fun h=>hnd'.1 (h ▸ hz);omega
lemma ZT {α:Type*} {l:List α} {p q:α->Bool}
 (hall:(l.filter p).all q=true) {x:α} (hx:x∈l) (hpx:p x=true):q x=true:=
 qE.mp hall x (qB.mpr ⟨hx,hpx⟩)
lemma Z3H {F:SS} (huc:iUC F) (hq3:Z5g F):
 ∃ w:WF,0 < ∑ i,w i∧
  F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i):=by
 obtain ⟨a,ha,b,hb,c,hc,hab,hac,hbc,ha3,hb3,hc3,hu⟩:=hq3;let U:=a∪b∪c;have haU:a⊆U:=qU.trans qU;have hbU:b⊆U:=qUr.trans qU;have hcU:c⊆U:=qUr;have hU3:3≤ U.card:=ha3 ▸ qL haU
 have hUne3:U.card≠3:=by
  intro heq;have h1:a=U:=qS haU (by omega);have h2:b=U:=qS hbU (by omega);exact hab (h1.trans h2.symm)
 let ms0:=U.toList;have v3:ms0.Nodup:=U.nodup_toList;have hlenU:ms0.length=U.card:=q3 _
 have v19:ms0.toFinset=U:=by ext x;simp[ms0]
 let ma:=Z3M ms0 a;let mb:=Z3M ms0 b;let mc:=Z3M ms0 c;have v8:Z3L ms0 ma=a:=ZH ms0 v3 (v19 ▸ haU);have v7:Z3L ms0 mb=b:=ZH ms0 v3 (v19 ▸ hbU);have v9:Z3L ms0 mc=c:=ZH ms0 v3 (v19 ▸ hcU);have v5:ma < 2 ^ U.card:=hlenU ▸ VK ms0 a;have v2:mb < 2 ^ U.card:=hlenU ▸ VK ms0 b;have v4:mc < 2 ^ U.card:=hlenU ▸ VK ms0 c;have v38:ma≠mb:=fun h=>hab (by rw[← v8,← v7,h]);have v41:ma≠mc:=fun h=>hac (by rw[← v8,← v9,h]);have v39:mb≠mc:=fun h=>hbc (by rw[← v7,← v9,h])
 have v40:[ma,mb,mc].Nodup:=by simp[v38,v41,v39]
 have v12:∀ m∈[ma,mb,mc],Z5o U.card m=3:=by
  intro m hm;rw[← hlenU,← Xs ms0 v3 m];rcases qC.mp hm with rfl|hm
  · rw[v8,ha3]
  rcases qC.mp hm with rfl|hm
  · rw[v7,hb3]
  rcases qC.mp hm with rfl|hm
  · rw[v9,hc3]
  simp at hm
 have v1:∀ m∈[ma,mb,mc],Z3L ms0 m∈F:=by
  intro m hm
  rcases qC.mp hm with rfl|hm;· rw[v8];exact ha
  rcases qC.mp hm with rfl|hm;· rw[v7];exact hb
  rcases qC.mp hm with rfl|hm;· rw[v9];exact hc
  simp at hm
 have v24:=XZ [ma,mb,mc]
 rcases hsL:Z4U [ma,mb,mc] with _|⟨m0,_|⟨m1,_|⟨m2,_|_⟩⟩⟩<;>
  simp[hsL] at v24
 have hst:=X_ v40;rw[hsL] at hst;simp only[qJ,qC,qNm,qs,
  List.Pairwise.nil,and_true] at hst
 have hm01:m0 < m1:=hst.1 m1 (Or.inl rfl);have v13:m1 < m2:=hst.2.1 m2 rfl;have hm_mem:∀ z∈[m0,m1,m2],z∈[ma,mb,mc]:=fun z hz=>
  (Z3f z [ma,mb,mc]).mp (hsL ▸ hz)
 have v6:∀ z∈[ma,mb,mc],z∈[m0,m1,m2]:=fun z hz=>
  hsL ▸ (Z3f z [ma,mb,mc]).mpr hz
 have v28:U.card=4∨U.card=5:=by change U.card≤ 5 at hu;omega
 rcases v28 with h4|h5
 · rw[h4] at v5 v2 v4
   have v0:∀ m∈[m0,m1,m2],m < 16:=fun m hm=>by
    rcases qC.mp (hm_mem m hm) with rfl|hm'
    · exact v5
    rcases qC.mp hm' with rfl|hm''
    · exact v2
    rcases qC.mp hm'' with rfl|hm'''
    · exact v4
    simp at hm'''
   have hp3:∀ m∈[m0,m1,m2],Z5o 4 m=3:=fun m hm=>h4 ▸ v12 m (hm_mem m hm);have hcl:=XW;dsimp only at hcl;have v17:m0∈(List.range 16).filter (fun m=>Z5o 4 m==3):=
    qB.mpr ⟨qR.mpr (v0 m0 (by simp)),by simp[hp3 m0 (by simp)]⟩
   have v16:m1∈((List.range 16).filter (fun m=>Z5o 4 m==3)).filter (m0 < ·):=
    qB.mpr ⟨qB.mpr ⟨qR.mpr (v0 m1 (by simp)),
     by simp[hp3 m1 (by simp)]⟩,by simp[hm01]⟩
   have v18:m2∈(((List.range 16).filter (fun m=>Z5o 4 m==3)).filter (m0 < ·)).filter (m1 < ·):=
    qB.mpr ⟨qB.mpr ⟨qB.mpr ⟨qR.mpr (v0 m2 (by simp)),
     by simp[hp3 m2 (by simp)]⟩,by simp[hm01.trans v13]⟩,by simp[v13]⟩
   have v42:=qE.mp (qE.mp (qE.mp hcl m0 v17) m1 v16) m2 v18;obtain ⟨p,hp_some⟩:=qc.mp v42;dsimp[Xk] at hp_some;have hpf:=List.find?_some hp_some;simp only[qA,qBi,qD,qE,
    qCm] at hpf
   obtain ⟨⟨⟨hlenp,hndp⟩,hltp⟩,hmemp⟩:=hpf;refine YC Z42 rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
    huc v3 (hlenU.trans h4) hlenp hndp (fun j hj=>hltp j hj) ?_
   intro g hg;change g∈[7,11,13] at hg;simp only[qC,qNm,qs] at hg;rcases hg with rfl|rfl|rfl
   · exact v1 _ (hm_mem _ hmemp.1)
   · exact v1 _ (hm_mem _ hmemp.2.1)
   · exact v1 _ (hm_mem _ hmemp.2.2.1)
 · rw[h5] at v5 v2 v4
   have v0:∀ m∈[m0,m1,m2],m < 32:=fun m hm=>by
    rcases qC.mp (hm_mem m hm) with rfl|hm'
    · exact v5
    rcases qC.mp hm' with rfl|hm''
    · exact v2
    rcases qC.mp hm'' with rfl|hm'''
    · exact v4
    simp at hm'''
   have hp3:∀ m∈[m0,m1,m2],Z5o 5 m=3:=fun m hm=>h5 ▸ v12 m (hm_mem m hm)
   have v29:Z3L ms0 (or7 (or7 m0 m1) m2)=U:=by
    have v21:=v0 m0 (by simp);have v20:=v0 m1 (by simp);have v26:=v0 m2 (by simp);have v22:m0|||m1 < 256:=lt_trans (q5 (n:=5) v21 v20) (by omega);rw[Z3m (lt_trans v21 (by omega)) (lt_trans v20 (by omega)),
     Z3m v22 (lt_trans v26 (by omega)),Q3,Q3]
    ext x;have ha':=v6 ma (by simp);have hb':=v6 mb (by simp);have hc':=v6 mc (by simp);have h0':=hm_mem m0 (by simp);have h1':=hm_mem m1 (by simp);have h2':=hm_mem m2 (by simp);simp only[qC,qNm,qs] at ha' hb' hc' h0' h1' h2';simp only[U,mem_union];constructor
    · intro hx
      rcases hx with (hx|hx)|hx
      · rcases h0' with rfl|rfl|rfl
        · left;left;rwa[v8] at hx
        · left;right;rwa[v7] at hx
        · right;rwa[v9] at hx
      · rcases h1' with rfl|rfl|rfl
        · left;left;rwa[v8] at hx
        · left;right;rwa[v7] at hx
        · right;rwa[v9] at hx
      · rcases h2' with rfl|rfl|rfl
        · left;left;rwa[v8] at hx
        · left;right;rwa[v7] at hx
        · right;rwa[v9] at hx
    · intro hx
      rcases hx with (hx|hx)|hx
      · rw[← v8] at hx
        rcases ha' with rfl|rfl|rfl;exact Or.inl (Or.inl hx);exact Or.inl (Or.inr hx);exact Or.inr hx
      · rw[← v7] at hx
        rcases hb' with rfl|rfl|rfl;exact Or.inl (Or.inl hx);exact Or.inl (Or.inr hx);exact Or.inr hx
      · rw[← v9] at hx
        rcases hc' with rfl|rfl|rfl;exact Or.inl (Or.inl hx);exact Or.inl (Or.inr hx);exact Or.inr hx
   have v10:ms0.length=5:=hlenU.trans h5
   have v27:Z5o 5 (or7 (or7 m0 m1) m2)=5:=by
    have hc:=Xs ms0 v3 (or7 (or7 m0 m1) m2);rw[v29,h5,v10] at hc;exact hc.symm
   have hcl:=XX;dsimp only at hcl;have v17:m0∈(List.range 32).filter (fun m=>Z5o 5 m==3):=
    qB.mpr ⟨qR.mpr (v0 m0 (by simp)),by simp[hp3 m0 (by simp)]⟩
   have v16:m1∈((List.range 32).filter (fun m=>Z5o 5 m==3)).filter (m0 < ·):=
    qB.mpr ⟨qB.mpr ⟨qR.mpr (v0 m1 (by simp)),
     by simp[hp3 m1 (by simp)]⟩,by simp[hm01]⟩
   have v18:m2∈(((List.range 32).filter (fun m=>Z5o 5 m==3)).filter (m0 < ·)).filter (m1 < ·):=
    qB.mpr ⟨qB.mpr ⟨qB.mpr ⟨qR.mpr (v0 m2 (by simp)),
     by simp[hp3 m2 (by simp)]⟩,by simp[hm01.trans v13]⟩,by simp[v13]⟩
   have v23:=qE.mp (qE.mp (qE.mp hcl m0 v17) m1 v16) m2 v18;simp only[v27,qBs,qNt,Bool.false_or,qA,
    qOr,qBi,qD,qE,qCm] at v23
   obtain ⟨⟨⟨⟨hcase,hlenp⟩,hndp⟩,hltp⟩,hmemp⟩:=v23;rcases hcase with (h1|h1)|h1
   · refine YC Z43 rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
      huc v3 v10 hlenp hndp (fun j hj=>hltp j hj) ?_
     intro g hg;have hg':g∈[7,11,19]:=hg;have hm:g∈(if (Z3e m0 m1 m2).1=1 then [7,11,19] else
      if (Z3e m0 m1 m2).1=2 then [7,11,21] else [7,11,28]):=by
      simpa[h1] using hg'
     exact v1 _ (hm_mem _ (hmemp g hm))
   · refine YC Z44 rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
      huc v3 v10 hlenp hndp (fun j hj=>hltp j hj) ?_
     intro g hg;have hg':g∈[7,11,21]:=hg;have hm:g∈(if (Z3e m0 m1 m2).1=1 then [7,11,19] else
      if (Z3e m0 m1 m2).1=2 then [7,11,21] else [7,11,28]):=by
      simpa[h1] using hg'
     exact v1 _ (hm_mem _ (hmemp g hm))
   · refine YC Z45 rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
      huc v3 v10 hlenp hndp (fun j hj=>hltp j hj) ?_
     intro g hg;have hg':g∈[7,11,28]:=hg;have hm:g∈(if (Z3e m0 m1 m2).1=1 then [7,11,19] else
      if (Z3e m0 m1 m2).1=2 then [7,11,21] else [7,11,28]):=by
      simpa[h1] using hg'
     exact v1 _ (hm_mem _ (hmemp g hm))
lemma Z3I {F:SS} (huc:iUC F) (hq3:¬ Z5g F)
 (hq4:Z5h F):
 ∃ w:WF,0 < ∑ i,w i∧
  F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i):=by
 obtain ⟨a,ha,b,hb,c,hc,d,hd,hab,hac,had,hbc,hbd,hcd,ha3,hb3,hc3,hd3,hu⟩:=hq4;let U:=a∪b∪c∪d;have haU:a⊆U:=qU.trans (qU.trans qU);have hbU:b⊆U:=qUr.trans (qU.trans qU);have hcU:c⊆U:=qUr.trans qU;have hdU:d⊆U:=qUr
 have v3:U.card=6:=by
  have h6:6≤ (a∪b∪c).card:=by
   by_contra! v1;exact hq3 ⟨a,ha,b,hb,c,hc,hab,hac,hbc,ha3,hb3,hc3,by omega⟩
  have hle:(a∪b∪c).card≤ U.card:=qL qU;change U.card≤ 6 at hu;omega
 let ms0:=U.toList;have v2:ms0.Nodup:=U.nodup_toList;have hlenU:ms0.length=U.card:=q3 _
 have v11:ms0.toFinset=U:=by ext x;simp[ms0]
 let ma:=Z3M ms0 a;let mb:=Z3M ms0 b;let mc:=Z3M ms0 c;let md:=Z3M ms0 d;have hsa:Z3L ms0 ma=a:=ZH ms0 v2 (v11 ▸ haU);have hsb:Z3L ms0 mb=b:=ZH ms0 v2 (v11 ▸ hbU);have hsc:Z3L ms0 mc=c:=ZH ms0 v2 (v11 ▸ hcU);have hsd:Z3L ms0 md=d:=ZH ms0 v2 (v11 ▸ hdU)
 have v23:ma < 64:=by simpa[hlenU,v3] using VK ms0 a
 have v21:mb < 64:=by simpa[hlenU,v3] using VK ms0 b
 have v22:mc < 64:=by simpa[hlenU,v3] using VK ms0 c
 have v25:md < 64:=by simpa[hlenU,v3] using VK ms0 d
 have v32:[ma,mb,mc,md].Nodup:=by
  have h12:ma≠mb:=fun h=>hab (by rw[← hsa,← hsb,h]);have h13:ma≠mc:=fun h=>hac (by rw[← hsa,← hsc,h]);have h14:ma≠md:=fun h=>had (by rw[← hsa,← hsd,h]);have h23:mb≠mc:=fun h=>hbc (by rw[← hsb,← hsc,h]);have h24:mb≠md:=fun h=>hbd (by rw[← hsb,← hsd,h]);have h34:mc≠md:=fun h=>hcd (by rw[← hsc,← hsd,h]);simp[h12,h13,h14,h23,h24,h34]
 have v4:∀ m∈[ma,mb,mc,md],Z3L ms0 m∈F:=by
  intro m hm
  rcases qC.mp hm with rfl|hm;· rw[hsa];exact ha
  rcases qC.mp hm with rfl|hm;· rw[hsb];exact hb
  rcases qC.mp hm with rfl|hm;· rw[hsc];exact hc
  rcases qC.mp hm with rfl|hm;· rw[hsd];exact hd
  simp at hm
 have v5:∀ m∈[ma,mb,mc,md],(Z3L ms0 m).card=3:=by
  intro m hm
  rcases qC.mp hm with rfl|hm;· rw[hsa,ha3]
  rcases qC.mp hm with rfl|hm;· rw[hsb,hb3]
  rcases qC.mp hm with rfl|hm;· rw[hsc,hc3]
  rcases qC.mp hm with rfl|hm;· rw[hsd,hd3]
  simp at hm
 have v24:=XZ [ma,mb,mc,md]
 rcases hsL:Z4U [ma,mb,mc,md] with _|⟨m0,_|⟨m1,_|⟨m2,_|⟨m3,_|_⟩⟩⟩⟩<;>
  simp[hsL] at v24
 have hst:=X_ v32;rw[hsL] at hst;simp only[qJ,qC,qNm,qs,
  List.Pairwise.nil,and_true] at hst
 have hm01:m0 < m1:=hst.1 m1 (Or.inl rfl);have hm12:m1 < m2:=hst.2.1 m2 (Or.inl rfl);have v8:m2 < m3:=hst.2.2.1 m3 rfl;have hm_mem:∀ z∈[m0,m1,m2,m3],z∈[ma,mb,mc,md]:=fun z hz=>
  (Z3f z [ma,mb,mc,md]).mp (hsL ▸ hz)
 have v1:∀ m∈[m0,m1,m2,m3],m < 64:=fun m hm=>by
  rcases qC.mp (hm_mem m hm) with rfl|hm'
  · exact v23
  rcases qC.mp hm' with rfl|hm''
  · exact v21
  rcases qC.mp hm'' with rfl|hm'''
  · exact v22
  rcases qC.mp hm''' with rfl|hm''''
  · exact v25
  simp at hm''''
 have hp3:∀ m∈[m0,m1,m2,m3],Z5o 6 m=3:=fun m hm=>by
  rw[← v3,← hlenU,← Xs ms0 v2 m];exact v5 m (hm_mem m hm)
 have v0:∀ x∈[m0,m1,m2,m3],∀ y∈[m0,m1,m2,m3],∀ z∈[m0,m1,m2,m3],
  x < y->y < z->Z5o 6 (or7 (or7 x y) z)=6:=by
  intro x hx y hy z hz hxy hyz;have v7:=v1 x hx;have v6:=v1 y hy;have v10:=v1 z hz;have v29:x|||y < 256:=lt_trans (q5 (n:=6) v7 v6) (by omega);rw[Z3m (lt_trans v7 (by omega)) (lt_trans v6 (by omega)),
   Z3m v29 (lt_trans v10 (by omega)),← v3,← hlenU,
   ← Xs ms0 v2 _,Q3,Q3]
  have v7':x < 2 ^ ms0.length:=by rw[hlenU,v3];exact v7
  have v6':y < 2 ^ ms0.length:=by rw[hlenU,v3];exact v6
  have v10':z < 2 ^ ms0.length:=by rw[hlenU,v3];exact v10
  have v41:Z3L ms0 x≠Z3L ms0 y:=fun h=>by
   have:=Q2 ms0 v2 v7' v6' h;omega
  have v42:Z3L ms0 x≠Z3L ms0 z:=fun h=>by
   have:=Q2 ms0 v2 v7' v10' h;omega
  have v38:Z3L ms0 y≠Z3L ms0 z:=fun h=>by
   have:=Q2 ms0 v2 v6' v10' h;omega
  have hge6:6≤ (Z3L ms0 x∪Z3L ms0 y∪Z3L ms0 z).card:=by
   by_contra! hlt6;exact hq3 ⟨_,v4 x (hm_mem x hx),_,v4 y (hm_mem y hy),_,v4 z (hm_mem z hz),
    v41,v42,v38,v5 x (hm_mem x hx),v5 y (hm_mem y hy),v5 z (hm_mem z hz),
    by omega⟩
  have v28:Z3L ms0 x∪Z3L ms0 y∪Z3L ms0 z⊆U:=by
   rw[← v11];exact qUs (qUs (Yg _ _) (Yg _ _))
    (Yg _ _)
  have hle6:(Z3L ms0 x∪Z3L ms0 y∪Z3L ms0 z).card≤ U.card:=qL v28;omega
 have hcl:=XY;dsimp only at hcl;have v36:m0∈(List.range 64).filter (fun m=>Z5o 6 m==3):=
  qB.mpr ⟨qR.mpr (v1 m0 (by simp)),by simp[hp3 m0 (by simp)]⟩
 have v31:m1∈((List.range 64).filter (fun m=>Z5o 6 m==3)).filter (m0 < ·):=
  qB.mpr ⟨qB.mpr ⟨qR.mpr (v1 m1 (by simp)),
   by simp[hp3 m1 (by simp)]⟩,by simp[hm01]⟩
 have v40:m2∈(((List.range 64).filter (fun m=>Z5o 6 m==3)).filter (m0 < ·)).filter (m1 < ·):=
  qB.mpr ⟨qB.mpr ⟨qB.mpr ⟨qR.mpr (v1 m2 (by simp)),
   by simp[hp3 m2 (by simp)]⟩,by simp[hm01.trans hm12]⟩,by simp[hm12]⟩
 have v33:m3∈((((List.range 64).filter (fun m=>Z5o 6 m==3)).filter (m0 < ·)).filter (m1 < ·)).filter (m2 < ·):=
  qB.mpr ⟨qB.mpr ⟨qB.mpr
   ⟨qB.mpr ⟨qR.mpr (v1 m3 (by simp)),by simp[hp3 m3 (by simp)]⟩,
    by simp[hm01.trans (hm12.trans v8)]⟩,by simp[hm12.trans v8]⟩,by simp[v8]⟩
 have v9:=qE.mp (qE.mp (qE.mp hcl m0 v36) m1 v31) m2 v40;have v35:Z5o 6 (or7 (or7 m0 m1) m2)=6:=v0 m0 (by simp) m1 (by simp) m2 (by simp) hm01 hm12;have v39:Z5o 6 (or7 (or7 m0 m1) m3)=6:=
  v0 m0 (by simp) m1 (by simp) m3 (by simp) hm01 (hm12.trans v8)
 have v34:Z5o 6 (or7 (or7 m0 m2) m3)=6:=
  v0 m0 (by simp) m2 (by simp) m3 (by simp) (hm01.trans hm12) v8
 have v37:Z5o 6 (or7 (or7 m1 m2) m3)=6:=
  v0 m1 (by simp) m2 (by simp) m3 (by simp) hm12 v8
 simp only[v35,qBs,qNt,Bool.false_or] at v9;have v18:=qE.mp v9 m3 v33;simp only[v39,v34,v37,qBs,Bool.and_self,qNt,Bool.false_or,
  qA,qOr,qBi,qD,qE,
  qCm] at v18
 obtain ⟨⟨⟨⟨hcase,hlenp⟩,hndp⟩,hltp⟩,hmemp⟩:=v18;rcases hcase with h0|h1
 · refine YC Z46 rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
    huc v2 (hlenU.trans v3) hlenp hndp (fun j hj=>hltp j hj) ?_
   intro g hg;have hg':g∈[7,11,52,56]:=hg
   have hm:g∈(if (Z3F m0 m1 m2 m3).1=0 then [7,11,52,56] else [7,25,42,52]):=by simpa[h0] using hg'
   exact v4 _ (hm_mem _ (hmemp g hm))
 · refine YC Z47 rfl rfl rfl rfl rfl rfl (by decide) (by decide) (by decide)
    huc v2 (hlenU.trans v3) hlenp hndp (fun j hj=>hltp j hj) ?_
   intro g hg;have hg':g∈[7,25,42,52]:=hg
   have hm:g∈(if (Z3F m0 m1 m2 m3).1=0 then [7,11,52,56] else [7,25,42,52]):=by simpa[h1] using hg'
   exact v4 _ (hm_mem _ (hmemp g hm))
end UP
namespace UP
open Finset UnionClosed UC UCC
open List (not_mem_nil nodup_cons getElem_mem mem_of_getElem contains_eq_mem getElem_map)
open Option (getD_some isSome_iff_exists)
lemma Zz {r:ℕ} (M:SF) (hM:M.card=r)
 (f:SF->ℤ) (t:ℕ->ℤ)
 (hk:∀ K⊆Mᶜ,t K.card≤ f K)
 (hsum:(0:ℤ)≤ ∑ k∈range (12-r+1),((12-r).choose k:ℤ)*t k):
 (0:ℤ)≤ ∑ K∈Mᶜ.powerset,f K:=by
 have v0:Mᶜ.card=12-r:=by rw[qu,qCf,hM]
 have v2:∀ K∈Mᶜ.powerset,K.card∈range (12-r+1):=fun K hK=>
  qMr.mpr (Nat.lt_succ_of_le (v0 ▸ qL (q7.mp hK)))
 rw[← qj v2];refine hsum.trans (sum_le_sum fun k _=>?_)
 have v1:Mᶜ.powerset.filter (fun K=>K.card=k)=Mᶜ.powersetCard k:=by
  ext K;simp
 have hc:(Mᶜ.powerset.filter (fun K=>K.card=k)).card=(12-r).choose k:=by rw[v1,qCp,v0]
 calc ((12-r).choose k:ℤ)*t k
  = ∑ _K∈Mᶜ.powerset.filter (fun K=>K.card=k),t k:=by rw[sum_const,nsmul_eq_mul,hc]
  _≤ ∑ K∈Mᶜ.powerset.filter (fun K=>K.card=k),f K:=by
   apply sum_le_sum;intro K hK;have hKm:=qF.mp hK;rw[← hKm.2];exact hk K (q7.mp hKm.1)
lemma Z7 {r:ℕ} {ms:LF} (hn:ms.Nodup) (hr:ms.length=r)
 {ws:LN} (hlen:ws.length=r) {wo W:ℕ} (hW:ws.sum+(12-r)*wo=W)
 (hWpos:0 < W) {F:SS}
 (hnonneg:(0:ℤ)≤ ∑ K∈ms.toFinsetᶜ.powerset,∑ A∈pF F ms.toFinset K,
  (2*((K.card*wo+∑ i∈A,mkWf ms ws wo i:ℕ):ℤ)-(W:ℤ))):
 ∃ w:WF,0 < ∑ i,w i∧
  F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i):=by
 let wf:=mkWf ms ws wo
 have hsum:(∑ i:Fin 12,wf i)=W:=by
  have:=Z4n ms hn ws (hr ▸ hlen) wo;simpa[wf,hr,hW] using this
 refine ⟨wf,hWpos.trans_eq hsum.symm,fIS F wf ?_⟩;have v0:∀ a∉ms,wf a=wo:=fun a ha=>Z1y ms ws wo ha;rw[hsum,ZR F ms wf wo W v0];exact hnonneg
structure Z5j (b:Z4w) (mS:ℕ) (tg:LN) (k:ℕ) (tgt:ℤ) where
 cf:Cfg
 p:ℕ
 n:ℕ
 hb:cf.ba=b
 hk:cf.k=k
 hm:cf.mS=mS
 ht:cf.tg=tg
 huc0:cf.uC=0
 hfe:cf.fE=false
 hfne:cf.fN=false
 htgt:(p:ℤ)-(n:ℤ)=tgt
 hok:VW cf p n
lemma Z4q {b:Z4w} {mS:ℕ} {tg:LN} {k:ℕ} {tgt:ℤ}
 (c:Z5j b mS tg k tgt) (_hms:mS≠0)
 {ms:LF} (hn:ms.Nodup) (hr:ms.length=b.r) (hws:b.ws.length=b.r)
 {F:SS} (huc:iUC F) (h0:∅∈F) (h1:univ∈F)
 (hlow:∀ X∈F,X.Nonempty->mS≤ X.card)
 (jC:∀ t∈tg,t≠0->¬ Z3r t F)
 (hgF:∀ g∈b.gS,Z3L ms g∈F)
 {K:SF} (hK:K⊆ms.toFinsetᶜ) (hk:K.card=k):
 tgt≤ ∑ A∈pF F ms.toFinset K,
  (2*((K.card*b.wo+∑ i∈A,mkWf ms b.ws b.wo i:ℕ):ℤ)-(b.W:ℤ)):=by
 obtain ⟨cf,p,n,hb,hk',hm,ht,huc0,hfe,hfne,htgt,hok⟩:=c;rw[← hb] at hr hws hgF ⊢;rw[← hk'] at hk;rw[← hm] at hlow;rw[← ht] at jC;rw[← htgt];refine XV hok hn hr hws huc (fun _=>hlow) jC hgF hK hk
  (fun h=>False.elim (h huc0)) ?_ ?_ (fun h=>by simp[hfne] at h)
 · intro _ hko
   rcases hko with hk0|hfet
   · have v2:K=∅:=qa.mp (hk.trans hk0);subst v2;exact Z4 h0 _
   · simp[hfe] at hfet
 · intro _ hkt
   have v0:ms.toFinsetᶜ.card=12-cf.r:=by rw[qu,qCf,qT hn,hr]
   have v1:K=ms.toFinsetᶜ:=qS hK (by rw[hk,hkt,v0]);subst v1;exact Z6 h1 _
lemma Xn {b:Z4w} (tag:ℕ)
 {F:SS}
 (hno:¬ ∃ w:WF,0 < ∑ i,w i∧F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i))
 (jE:Z4Y tag=b.r) (jD:Z3Q tag=b.gS)
 (hws:b.ws.length=b.r) (hWpos:0 < b.W) (hWsum:b.ws.sum+(12-b.r)*b.wo=b.W)
 (tfn:ℕ->ℤ)
 (hfib:∀ (ms:LF) (K:SF),ms.Nodup->ms.length=b.r->
  (∀ g∈b.gS,Z3L ms g∈F)->K⊆ms.toFinsetᶜ->
  tfn K.card≤ ∑ A∈pF F ms.toFinset K,
   (2*((K.card*b.wo+∑ i∈A,mkWf ms b.ws b.wo i:ℕ):ℤ)-(b.W:ℤ)))
 (hsum:(0:ℤ)≤ ∑ k∈range (12-b.r+1),((12-b.r).choose k:ℤ)*tfn k):
 uN tag F:=by
 intro ⟨_,ms,hn,hlen,hg⟩;have hr:ms.length=b.r:=hlen.trans jE;have v0:∀ g∈b.gS,Z3L ms g∈F:=fun g hgg=>hg g (jD ▸ hgg);apply hno;refine Z7 hn hr hws hWsum hWpos ?_;exact Zz ms.toFinset ((qT hn).trans hr) _ tfn
  (fun K hK=>hfib ms K hn hr v0 hK) hsum
lemma Z48 {b:Z4w} (tag mS:ℕ) (tg:LN) (r:ℕ)
 (tfn:ℕ->ℤ) (hc:∀ k≤ 12-r,Z5j b mS tg k (tfn k))
 (hsum:0≤ ∑ k∈range (12-r+1),((12-r).choose k:ℤ)*tfn k)
 {F:SS} (hno:¬ ∃ w:WF,0 < ∑ i,w i∧
  F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i))
 (huc:iUC F) (h0:∅∈F) (h1:univ∈F)
 (hlow:∀ X∈F,X.Nonempty->mS≤ X.card)
 (jC:∀ x∈tg,x≠0->¬ Z3r x F)
 (hbr:b.r=r) (hws:b.ws.length=r) (hWpos:0 < b.W)
 (hWsum:b.ws.sum+(12-r)*b.wo=b.W) (jE:Z4Y tag=r)
 (jD:Z3Q tag=b.gS) (hms:mS≠0):uN tag F:=by
 refine Xn tag hno (jE.trans hbr.symm)
  jD (hws.trans hbr.symm) hWpos (by rw[hbr];exact hWsum) tfn ?_ (by rw[hbr];exact hsum)
 intro ms K hn hr hgF hK;have v0:K.card≤ 12-r:=
  (by rw[qu,qCf,qT hn,hr,hbr]:
   ms.toFinsetᶜ.card=12-r)▸ qL hK
 exact Z4q (hc K.card v0) hms hn hr (hws.trans hbr.symm) huc h0 h1 hlow jC hgF hK rfl
lemma Z5k {b:Z4w} (tag mS:ℕ) (tg:LN) {t0 t1 t2 t3 t4 t5:ℤ}
 (c0:Z5j b mS tg 0 t0) (c1:Z5j b mS tg 1 t1) (c2:Z5j b mS tg 2 t2)
 (c3:Z5j b mS tg 3 t3) (c4:Z5j b mS tg 4 t4) (c5:Z5j b mS tg 5 t5)
 (hsum:0≤ t0+5*t1+10*t2+10*t3+5*t4+t5)
 {F:SS} (hno:¬ ∃ w:WF,0 < ∑ i,w i∧
  F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i))
 (huc:iUC F) (h0:∅∈F) (h1:univ∈F)
 (hlow:∀ X∈F,X.Nonempty->mS≤ X.card) (jC:∀ x∈tg,x≠0->¬ Z3r x F)
 (hbr:b.r=7:=by rfl) (hws:b.ws.length=7:=by rfl) (hWpos:0 < b.W:=by decide)
 (hWsum:b.ws.sum+5*b.wo=b.W:=by rfl) (jE:Z4Y tag=7:=by rfl)
 (jD:Z3Q tag=b.gS:=by rfl) (hms:mS≠0:=by decide):
 uN tag F:=
 Z48 tag mS tg 7 (fun k=>match k with|0=>t0|1=>t1|2=>t2|3=>t3|4=>t4|_=>t5)
  (fun k hk=>by rcases k with _|_|_|_|_|_|n;exacts[c0,c1,c2,c3,c4,c5,by omega])
  (by simpa[qSg,Nat.choose] using hsum) hno huc h0 h1 hlow jC hbr hws hWpos hWsum jE jD hms
lemma Z5l {b:Z4w} (tag mS:ℕ) (tg:LN) {t0 t1 t2 t3 t4 t5 t6:ℤ}
 (c0:Z5j b mS tg 0 t0) (c1:Z5j b mS tg 1 t1) (c2:Z5j b mS tg 2 t2)
 (c3:Z5j b mS tg 3 t3) (c4:Z5j b mS tg 4 t4) (c5:Z5j b mS tg 5 t5)
 (c6:Z5j b mS tg 6 t6) (hsum:0≤ t0+6*t1+15*t2+20*t3+15*t4+6*t5+t6)
 {F:SS} (hno:¬ ∃ w:WF,0 < ∑ i,w i∧
  F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i))
 (huc:iUC F) (h0:∅∈F) (h1:univ∈F)
 (hlow:∀ X∈F,X.Nonempty->mS≤ X.card) (jC:∀ x∈tg,x≠0->¬ Z3r x F)
 (hbr:b.r=6:=by rfl) (hws:b.ws.length=6:=by rfl) (hWpos:0 < b.W:=by decide)
 (hWsum:b.ws.sum+6*b.wo=b.W:=by rfl) (jE:Z4Y tag=6:=by rfl)
 (jD:Z3Q tag=b.gS:=by rfl) (hms:mS≠0:=by decide):
 uN tag F:=
 Z48 tag mS tg 6 (fun k=>match k with|0=>t0|1=>t1|2=>t2|3=>t3|4=>t4|5=>t5|_=>t6)
  (fun k hk=>by rcases k with _|_|_|_|_|_|_|n;exacts[c0,c1,c2,c3,c4,c5,c6,by omega])
  (by simpa[qSg,Nat.choose] using hsum) hno huc h0 h1 hlow jC hbr hws hWpos hWsum jE jD hms
lemma Z5m {b:Z4w} (tag mS:ℕ) (tg:LN) {t0 t1 t2 t3 t4 t5 t6 t7:ℤ}
 (c0:Z5j b mS tg 0 t0) (c1:Z5j b mS tg 1 t1) (c2:Z5j b mS tg 2 t2)
 (c3:Z5j b mS tg 3 t3) (c4:Z5j b mS tg 4 t4) (c5:Z5j b mS tg 5 t5)
 (c6:Z5j b mS tg 6 t6) (c7:Z5j b mS tg 7 t7)
 (hsum:0≤ t0+7*t1+21*t2+35*t3+35*t4+21*t5+7*t6+t7)
 {F:SS} (hno:¬ ∃ w:WF,0 < ∑ i,w i∧
  F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i))
 (huc:iUC F) (h0:∅∈F) (h1:univ∈F)
 (hlow:∀ X∈F,X.Nonempty->mS≤ X.card) (jC:∀ x∈tg,x≠0->¬ Z3r x F)
 (hbr:b.r=5:=by rfl) (hws:b.ws.length=5:=by rfl) (hWpos:0 < b.W:=by decide)
 (hWsum:b.ws.sum+7*b.wo=b.W:=by rfl) (jE:Z4Y tag=5:=by rfl)
 (jD:Z3Q tag=b.gS:=by rfl) (hms:mS≠0:=by decide):
 uN tag F:=
 Z48 tag mS tg 5 (fun k=>match k with|0=>t0|1=>t1|2=>t2|3=>t3|4=>t4|5=>t5|6=>t6|_=>t7)
  (fun k hk=>by rcases k with _|_|_|_|_|_|_|_|n;exacts[c0,c1,c2,c3,c4,c5,c6,c7,by omega])
  (by simpa[qSg,Nat.choose] using hsum) hno huc h0 h1 hlow jC hbr hws hWpos hWsum jE jD hms
lemma Z5n {b:Z4w} (tag mS:ℕ) (tg:LN) {t0 t1 t2 t3 t4 t5 t6 t7 t8:ℤ}
 (c0:Z5j b mS tg 0 t0) (c1:Z5j b mS tg 1 t1) (c2:Z5j b mS tg 2 t2)
 (c3:Z5j b mS tg 3 t3) (c4:Z5j b mS tg 4 t4) (c5:Z5j b mS tg 5 t5)
 (c6:Z5j b mS tg 6 t6) (c7:Z5j b mS tg 7 t7) (c8:Z5j b mS tg 8 t8)
 (hsum:0≤ t0+8*t1+28*t2+56*t3+70*t4+56*t5+28*t6+8*t7+t8)
 {F:SS} (hno:¬ ∃ w:WF,0 < ∑ i,w i∧
  F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i))
 (huc:iUC F) (h0:∅∈F) (h1:univ∈F)
 (hlow:∀ X∈F,X.Nonempty->mS≤ X.card) (jC:∀ x∈tg,x≠0->¬ Z3r x F)
 (hbr:b.r=4:=by rfl) (hws:b.ws.length=4:=by rfl) (hWpos:0 < b.W:=by decide)
 (hWsum:b.ws.sum+8*b.wo=b.W:=by rfl) (jE:Z4Y tag=4:=by rfl)
 (jD:Z3Q tag=b.gS:=by rfl) (hms:mS≠0:=by decide):
 uN tag F:=
 Z48 tag mS tg 4 (fun k=>match k with|0=>t0|1=>t1|2=>t2|3=>t3|4=>t4|5=>t5|6=>t6|7=>t7|_=>t8)
  (fun k hk=>by rcases k with _|_|_|_|_|_|_|_|_|n;exacts[c0,c1,c2,c3,c4,c5,c6,c7,c8,by omega])
  (by simpa[qSg,Nat.choose] using hsum) hno huc h0 h1 hlow jC hbr hws hWpos hWsum jE jD hms
def ck2 {b:Z4w} {tg:LN} {k p n:ℕ} {cf:Cfg} (hok:VW cf p n)
 (hc:cf=⟨b,k,tg,cf.tB,4,0,false,false⟩):Z5j b 4 tg k ((p:ℤ)-(n:ℤ)):=
 ⟨cf,p,n,congrArg Cfg.ba hc,congrArg Cfg.k hc,congrArg Cfg.mS hc,congrArg Cfg.tg hc,
  congrArg Cfg.uC hc,congrArg Cfg.fE hc,congrArg Cfg.fN hc,rfl,hok⟩
def u2 {b cg pt xs tg ws} {kf pn:ℕ} (hk:KOk b cg pt xs) (i:ℕ)
 (hi:xs[i]?=some (kf,tg,ws,pn):=by rfl)
 (hpt:pt=mNP b.r b.pS:=by rfl)
 (hc:C b (kf % 32) tg (kf / 32)=⟨b,kf % 32,tg,(C b (kf % 32) tg (kf / 32)).tB,4,0,false,false⟩:=by rfl):
 Z5j b 4 tg (kf % 32) (((pn % 65536:ℕ):ℤ)-((pn / 65536:ℕ):ℤ)):=ck2 (gK hk.1 hk.2 i hi hpt) hc
abbrev NG (F:SS):Prop:=¬ ∃ w:WF,0 < ∑ i,w i∧F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i)
structure H2C (F:SS):Prop where
 hno:NG F
 cl:iUC F
 emp:∅∈F
 full:univ∈F
 low:∀ S∈F,S.Nonempty->4≤ S.card
lemma pm1 {P:ℕ->Prop} {a:ℕ} (ha:P a):∀ x∈[a],x≠0->P x:=fun x hx _=>by simp only[qC,qNm,qs] at hx;subst hx;exact ha
lemma pm2 {P:ℕ->Prop} {a b:ℕ} (ha:P a) (hb:P b):∀ x∈[a,b],x≠0->P x:=fun x hx _=>by simp only[qC,qNm,qs] at hx;rcases hx with rfl|rfl<;>[exact ha;exact hb]
lemma pm3 {P:ℕ->Prop} {a b c:ℕ} (ha:P a) (hb:P b) (hc:P c):∀ x∈[a,b,c],x≠0->P x:=fun x hx _=>by simp only[qC,qNm,qs] at hx;rcases hx with rfl|rfl|rfl<;>[exact ha;exact hb;exact hc]
lemma h2_a {F:SS} (c:H2C F):uN 12 F∧uN 16 F∧uN 26 F∧uN 27 F:=by
 have nf7:=Z5l 7 4 [0] (u2 k0 0) (u2 k0 1) (u2 k0 2) (u2 k0 3) (u2 k0 4) (u2 k0 5) (u2 k0 6) (by decide) c.hno c.cl c.emp c.full c.low ((fun x hx hne=>by simp at hx;exact False.elim (hne hx)))
 have nf8:=Z5k 8 4 [7] (u2 k1 0) (u2 k1 1) (ck2 Z29 rfl) (ck2 Z2a rfl) (u2 k1 2) (u2 k1 3) (by decide) c.hno c.cl c.emp c.full c.low (pm1 nf7);have v2:=Z5l 12 4 [8] (u2 k2 0) (u2 k2 1) (u2 k2 2) (u2 k2 3) (u2 k2 4) (u2 k2 5) (u2 k2 6) (by decide) c.hno c.cl c.emp c.full c.low (pm1 nf8);have v0:=Z5m 16 4 [12] (u2 k3 0) (u2 k3 1) (u2 k3 2) (u2 k3 3) (u2 k3 4) (u2 k3 5) (u2 k3 6) (u2 k3 7) (by decide) c.hno c.cl c.emp c.full c.low (pm1 v2);have v3:=Z5l 26 4 [12,16] (u2 k4 0) (u2 k4 1) (ck2 Js rfl) (ck2 Jt rfl) (u2 k4 2) (u2 k4 3) (u2 k4 4) (by decide) c.hno c.cl c.emp c.full c.low (pm2 v2 v0);have v1:=Z5l 27 4 [16,26] (u2 k5 0) (u2 k5 1) (u2 k5 2) (u2 k5 3) (u2 k5 4) (u2 k5 5) (u2 k5 6) (by decide) c.hno c.cl c.emp c.full c.low (pm2 v0 v3);exact ⟨v2,v0,v3,v1⟩
lemma h2_b {F:SS} (c:H2C F) (v0:uN 16 F) (v3:uN 26 F) (v1:uN 27 F):uN 32 F:=by
 have v7:=Z5m 28 4 [16,26,27] (u2 k6 0) (u2 k6 1) (u2 k6 2) (u2 k6 3) (u2 k6 4) (u2 k6 5) (u2 k6 6) (u2 k6 7) (by decide) c.hno c.cl c.emp c.full c.low (pm3 v0 v3 v1);have v8:=Z5l 29 4 [27] (u2 k7 0) (u2 k7 1) (u2 k7 2) (u2 k7 3) (u2 k7 4) (u2 k7 5) (u2 k7 6) (by decide) c.hno c.cl c.emp c.full c.low (pm1 v1);have v4:=Z5m 30 4 [28,29] (u2 k8 0) (u2 k8 1) (u2 k8 2) (u2 k8 3) (u2 k8 4) (u2 k8 5) (u2 k8 6) (u2 k8 7) (by decide) c.hno c.cl c.emp c.full c.low (pm2 v7 v8);have v9:=Z5l 31 4 [30] (u2 k9 0) (u2 k9 1) (u2 k9 2) (u2 k9 3) (u2 k9 4) (u2 k9 5) (u2 k9 6) (by decide) c.hno c.cl c.emp c.full c.low (pm1 v4);exact Z5n 32 4 [30,31] (u2 k10 0) (u2 k10 1) (u2 k10 2) (u2 k10 3) (u2 k10 4) (u2 k10 5) (u2 k10 6) (u2 k10 7) (u2 k10 8) (by decide) c.hno c.cl c.emp c.full c.low (pm2 v4 v9)
lemma h2_main:∀ F:SS,iUC F->∅∈F->univ∈F->(∃ S∈F,S.card=4)->(∀ S∈F,S.Nonempty->4≤ S.card)->
 ∃ w:WF,0 < ∑ i,w i∧F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i):=by
 intro F closed empty full ⟨S,hSF,hSc⟩ low;by_contra hno;let c:H2C F:=⟨hno,closed,empty,full,low⟩;obtain ⟨_,v0,v3,v1⟩:=h2_a c;apply h2_b c v0 v3 v1;refine ⟨by decide,S.toList,S.nodup_toList,by rw[q3,hSc];rfl,fun g hg=>?_⟩;simp only[Z3Q,qC,qNm,qs] at hg;subst hg
 have v6:S.toList.length=4:=by rw[q3,hSc]
 have h15:15=2 ^ S.toList.length-1:=by rw[v6];decide
 rw[h15,Xv];simpa using hSF
end UP
namespace UP
open Finset UnionClosed UC
open List (not_mem_nil nodup_cons getElem_mem mem_of_getElem contains_eq_mem getElem_map)
open Option (getD_some isSome_iff_exists)
lemma Q0 {ks:LF} (_hn:ks.Nodup) (_hk:ks.length=7)
 {F:SS} (huc:iUC F) (nq3:¬ Z5g F) (nq4:¬ Z5h F):
 let K3F:=(ks.toFinset.powersetCard 3).filter (fun K=>K∈F);let K5F:=(ks.toFinset.powersetCard 5).filter (fun K=>K∈F);let K6F:=(ks.toFinset.powersetCard 6).filter (fun K=>K∈F)
 230-96*(K3F.card:ℤ)+60*(K5F.card:ℤ)+116*(K6F.card:ℤ)≥0∧
 30-12*(K3F.card:ℤ)+12*(K5F.card:ℤ)+24*(K6F.card:ℤ)≥0∧
 72-2*(K3F.card:ℤ)+46*(K5F.card:ℤ)+90*(K6F.card:ℤ)≥0:=by
 intro K3F K5F K6F;have v0:∀ A∈K3F,A⊆ks.toFinset∧A∈F∧A.card=3:=fun A hA=>by
  obtain ⟨hAp,hAF⟩:=qF.mp hA;obtain ⟨hAs,hAc⟩:=qP.mp hAp;exact ⟨hAs,hAF,hAc⟩
 have h46:∀ {A B:SF},A∈K3F->B∈K3F->A≠B->
  4≤ (A∪B).card∧(A∪B).card≤ 6:=by
  intro A B hA hB hne;have hA':=v0 A hA;have hB':=v0 B hB;have v22:(A∪B).card≤ 6:=(card_union_le A B).trans (by omega)
  have v5:4≤ (A∪B).card:=by
   by_contra! hlt4;exact hne ((qS qU (by omega)).trans
    (qS qUr (by omega)).symm)
  exact ⟨v5,v22⟩
 set D4:=K3F.offDiag.filter (fun p=>(p.1∪p.2).card=4);set D56:=K3F.offDiag.filter (fun p=>5≤ (p.1∪p.2).card)
 have hD_part:D4.card+D56.card=K3F.card*K3F.card-K3F.card:=by
  have v11:D56=K3F.offDiag.filter (fun p=>¬ (p.1∪p.2).card=4):=by
   refine filter_congr fun p hp=>?_;obtain ⟨h1,h2,hne⟩:=mem_offDiag.mp hp;have h4:=(h46 h1 h2 hne).1;omega
  rw[v11,card_filter_add_card_filter_not,offDiag_card]
 have hD4_le:D4.card≤ K3F.card:=by
  have v24:Set.InjOn Prod.fst (D4:Set (SF× SF)):=by
   rintro ⟨A,B₁⟩ h1 ⟨A',B₂⟩ h2 heq;dsimp only at heq;subst heq;simp only[mem_coe,D4,qF,mem_offDiag] at h1 h2;obtain ⟨⟨hA,hB1,hAB1⟩,h1c⟩:=h1;obtain ⟨⟨_,hB2,hAB2⟩,h2c⟩:=h2;by_contra hne;have v23:B₁≠B₂:=fun h=>hne (by subst h;rfl);have hA':=v0 A hA;have hB1':=v0 B₁ hB1;have hB2':=v0 B₂ hB2
   have v17:(A∩B₂).card=2:=by have:=qCa A B₂;omega
   have hle_i:2≤ ((A∪B₁)∩B₂).card:=
    v17 ▸ qL (inter_subset_inter_right qU)
   have hu:=qCa (A∪B₁) B₂;exact nq3 ⟨A,hA'.2.1,B₁,hB1'.2.1,B₂,hB2'.2.1,hAB1,hAB2,v23,
    hA'.2.2,hB1'.2.2,hB2'.2.2,by omega⟩
  have v1:D4.image Prod.fst⊆K3F:=fun A hA=>by
   obtain ⟨p,hp,rfl⟩:=qI.mp hA;exact (mem_offDiag.mp (qF.mp hp).1).1
  calc D4.card=(D4.image Prod.fst).card:=(card_image_of_injOn v24).symm
   _≤ K3F.card:=qL v1
 have hD56_le:D56.card≤ 2*(K5F.card+K6F.card):=by
  have v25:∀ p∈D56,p.1∪p.2∈K5F∪K6F:=fun p hp=>by
   obtain ⟨hpo,h5⟩:=qF.mp hp;obtain ⟨h1,h2,hne⟩:=mem_offDiag.mp hpo;have h1':=v0 p.1 h1;have h2':=v0 p.2 h2;have h6:=(h46 h1 h2 hne).2;have huF:p.1∪p.2∈F:=huc _ h1'.2.1 _ h2'.2.1;have v7:p.1∪p.2⊆ks.toFinset:=qUs h1'.1 h2'.1;by_cases h5eq:(p.1∪p.2).card=5
   · exact mem_union_left _ (qF.mpr ⟨qP.mpr ⟨v7,h5eq⟩,huF⟩)
   · exact mem_union_right _ (qF.mpr ⟨qP.mpr ⟨v7,by omega⟩,huF⟩)
  have v6:D56.card=∑ U∈K5F∪K6F,(D56.filter (fun p=>p.1∪p.2=U)).card:=by
   rw[card_eq_sum_ones,← qj v25];refine qh rfl fun U _=>?_;rw[card_eq_sum_ones]
  have v8:∀ U∈K5F∪K6F,(D56.filter (fun p=>p.1∪p.2=U)).card≤ 2:=by
   intro U hU;set S:=D56.filter (fun p=>p.1∪p.2=U);by_cases hS:S.Nonempty
   · obtain ⟨⟨A,B⟩,hAB⟩:=hS;simp only[S,D56,qF,mem_offDiag] at hAB;obtain ⟨⟨⟨hA,hB,hABne⟩,_⟩,hUeq⟩:=hAB;have hA':=v0 A hA;have hB':=v0 B hB
     have v26:U.card=5∨U.card=6:=by
      rcases mem_union.mp hU with hU5|hU6
      · exact Or.inl (qP.mp (qF.mp hU5).1).2
      · exact Or.inr (qP.mp (qF.mp hU6).1).2
     have v1:S⊆({(A,B),(B,A)}:Finset (SF× SF)):=by
      rintro ⟨C,D⟩ hCD;simp only[S,D56,qF,mem_offDiag] at hCD;obtain ⟨⟨⟨hC,hD,hCDne⟩,_⟩,hUCD⟩:=hCD;have v2:∀ {X Y:SF},X∈K3F->Y∈K3F->X≠Y->
       X∪Y=U->X=A∨X=B:=fun {X Y} hX hY hXYne hXYU=>by
       have hX':=v0 X hX;have hY':=v0 Y hY
       by_contra! hnot;rcases v26 with hU5|hU6
       · have v4:A∪B∪X⊆U:=qUs hUeq.subset (qU.trans hXYU.subset);exact nq3 ⟨A,hA'.2.1,B,hB'.2.1,X,hX'.2.1,hABne,Ne.symm hnot.1,Ne.symm hnot.2,
          hA'.2.2,hB'.2.2,hX'.2.2,(qL v4).trans_eq hU5⟩
       · by_cases hYA:Y=A
         · have hXA:X∪A=U:=hYA ▸ hXYU
           have v13:X⊆B:=fun x hx=>by
            have hxU:x∈A∪B:=hUeq ▸ (hXA ▸ mem_union_left A hx);have v27:x∉A:=fun hxA=>by
             have v9:Disjoint X A:=by
              have:=qCa X A;rw[hXA,hU6,hX'.2.2,hA'.2.2] at this;exact disjoint_iff_inter_eq_empty.mpr (qa.mp (by omega))
             exact disjoint_left.mp v9 hx hxA
            exact (mem_union.mp hxU).resolve_left v27
           exact hnot.2 (qS v13 (by omega))
         · by_cases hYB:Y=B
           · have hXB:X∪B=U:=hYB ▸ hXYU
             have v14:X⊆A:=fun x hx=>by
              have hxU:x∈A∪B:=hUeq ▸ (hXB ▸ mem_union_left B hx);have v28:x∉B:=fun hxB=>by
               have v10:Disjoint X B:=by
                have:=qCa X B;rw[hXB,hU6,hX'.2.2,hB'.2.2] at this;exact disjoint_iff_inter_eq_empty.mpr (qa.mp (by omega))
               exact disjoint_left.mp v10 hx hxB
              exact (mem_union.mp hxU).resolve_right v28
             exact hnot.1 (qS v14 (by omega))
           · have v4:A∪B∪X∪Y⊆U:=qUs
              (qUs hUeq.subset (qU.trans hXYU.subset))
              (qUr.trans hXYU.subset)
             exact nq4 ⟨A,hA'.2.1,B,hB'.2.1,X,hX'.2.1,Y,hY'.2.1,
              hABne,Ne.symm hnot.1,Ne.symm hYA,Ne.symm hnot.2,Ne.symm hYB,hXYne,
              hA'.2.2,hB'.2.2,hX'.2.2,hY'.2.2,(qL v4).trans_eq hU6⟩
      have v15:=v2 hC hD hCDne hUCD;have v16:=v2 hD hC hCDne.symm (union_comm D C ▸ hUCD)
      rcases v15 with hCA|hCB<;>rcases v16 with hDA|hDB
      · exact False.elim (hCDne (hCA.trans hDA.symm))
      · subst hCA hDB;exact mem_insert_self _ _
      · subst hCB hDA;exact mem_insert_of_mem (qMs _)
      · exact False.elim (hCDne (hCB.trans hDB.symm))
     exact (qL v1).trans ((card_insert_le _ _).trans (by simp))
   · rw[not_nonempty_iff_eq_empty.mp hS];simp
  calc D56.card=∑ U∈K5F∪K6F,(D56.filter (fun p=>p.1∪p.2=U)).card:=v6
   _≤ ∑ _U∈K5F∪K6F,2:=sum_le_sum v8
   _=2*(K5F∪K6F).card:=by rw[sum_const,smul_eq_mul,mul_comm]
   _≤ 2*(K5F.card+K6F.card):=Nat.mul_le_mul_left 2 (card_union_le K5F K6F)
 have v3:K3F.card*(K3F.card-2)≤ 2*(K5F.card+K6F.card):=by
  by_cases hm2:K3F.card≤ 1
  · rw[Nat.sub_eq_zero_of_le (by omega),mul_zero];exact Nat.zero_le _
  · have h1:K3F.card*(K3F.card-2)+K3F.card=K3F.card*K3F.card-K3F.card:=by
     have ha:K3F.card-2+1=K3F.card-1:=by omega
     calc K3F.card*(K3F.card-2)+K3F.card
      = K3F.card*(K3F.card-2+1):=by rw[mul_add,mul_one]
      _=K3F.card*(K3F.card-1):=by rw[ha]
      _=K3F.card*K3F.card-K3F.card:=by rw[Nat.mul_sub,mul_one]
    omega
 generalize K3F.card=m at v3 ⊢
 rcases m with _|_|_|_|_|_|m<;>try omega
 have v5:4≤ m+6-2:=by omega
 have h4m:4*(m+6)≤ 2*(K5F.card+K6F.card):=
  (qY 4 (m+6)▸ Nat.mul_le_mul_left (m+6) v5).trans v3
 have h2m:2*(m+6)≤ K5F.card+K6F.card:=by omega
 omega
end UP
namespace UP
open Finset UnionClosed UC UCC UCC UCC
open List (not_mem_nil nodup_cons getElem_mem mem_of_getElem contains_eq_mem getElem_map)
open Option (getD_some isSome_iff_exists)
structure Z5e (b:Z4w) (tg:LN) (k uc:ℕ) (fe fne:Bool) (tgt:ℤ) where
 cf:Cfg
 p:ℕ
 n:ℕ
 hb:cf.ba=b
 hk:cf.k=k
 hm:cf.mS=3
 ht:cf.tg=tg
 huc:cf.uC=uc
 hfe:cf.fE=fe
 hfne:cf.fN=fne
 htgt:(p:ℤ)-(n:ℤ)=tgt
 hok:VW cf p n
def ck1 {b:Z4w} {tg:LN} {k uc p n:ℕ} {fe fne:Bool} {cf:Cfg} (hok:VW cf p n)
 (hc:cf=⟨b,k,tg,cf.tB,3,uc,fe,fne⟩):Z5e b tg k uc fe fne ((p:ℤ)-(n:ℤ)):=
 ⟨cf,p,n,congrArg Cfg.ba hc,congrArg Cfg.k hc,congrArg Cfg.mS hc,congrArg Cfg.tg hc,
  congrArg Cfg.uC hc,congrArg Cfg.fE hc,congrArg Cfg.fN hc,rfl,hok⟩
def u1 {b cg pt xs tg ws} {kf pn k uc:ℕ} {fe fne:Bool} (hk:KOk b cg pt xs) (i:ℕ)
 (hi:xs[i]?=some (kf,tg,ws,pn):=by rfl)
 (hpt:pt=mNP b.r b.pS:=by rfl)
 (hc:C b (kf % 32) tg (kf / 32)=⟨b,k,tg,(C b (kf % 32) tg (kf / 32)).tB,3,uc,fe,fne⟩:=by rfl):
 Z5e b tg k uc fe fne (((pn % 65536:ℕ):ℤ)-((pn / 65536:ℕ):ℤ)):=ck1 (gK hk.1 hk.2 i hi hpt) hc
structure Z5t (F:SS):Prop where
 hno:¬ ∃ w:WF,0 < ∑ i,w i∧F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i)
 huc:iUC F
 h0:∅∈F
 h1:univ∈F
 hlow:∀ X∈F,X.Nonempty->3≤ X.card
 nq3:¬ Z5g F
 nq4:¬ Z5h F
lemma pn {F:SS}:∀ x∈([]:LN),x≠0->¬ Z3r x F:=by simp
lemma pq3 {F:SS} (nq3:¬ Z5g F):
 ∀ x∈[34],x≠0->¬ Z3r x F:=fun x hx _=>by
 simp only[qC,qNm,qs] at hx;subst hx;simpa[Z3r] using nq3
lemma Z5u {F:SS} (nq3:¬ Z5g F) (nq4:¬ Z5h F):
 ∀ x∈[34,35],x≠0->¬ Z3r x F:=fun x hx _=>by
 simp only[qC,qNm,qs] at hx
 rcases hx with rfl|rfl<;>simpa[Z3r]
lemma pc {F:SS} {a:ℕ} {t:LN}
 (ha:uN a F) (ht:∀ x∈t,x≠0->¬ Z3r x F)
 (h34:a≠34:=by decide) (h35:a≠35:=by decide):
 ∀ x∈a :: t,x≠0->¬ Z3r x F:=fun x hx h0=>by
 rcases qC.mp hx with rfl|hxt
 · simp[Z3r,h34,h35,ha]
 · exact ht x hxt h0
lemma Zf {F:SS} {M K:SF}
 (hnK:K∉F):∅∉pF F M K:=fun h0=>hnK (by simpa using ZS h0)
lemma Z49 {b:Z4w} {tg:LN} {k uc:ℕ} {fe fne:Bool} {tgt:ℤ}
 (c:Z5e b tg k uc fe fne tgt)
 {ms:LF} (hn:ms.Nodup) (hr:ms.length=b.r) (hws:b.ws.length=b.r)
 {F:SS} (hucF:iUC F) (h0:∅∈F) (h1:univ∈F)
 (hlow:∀ X∈F,X.Nonempty->3≤ X.card) (jC:∀ t∈tg,t≠0->¬ Z3r t F)
 (hgF:∀ g∈b.gS,Z3L ms g∈F) {K:SF} (hK:K⊆ms.toFinsetᶜ) (hk:K.card=k)
 (hcp:uc≠0->((pF F ms.toFinset K).filter (fun A=>A.card=1)).card≤ (if uc=2 then 3 else 2))
 (hfe_mem:fe=true->K∈F) (hfne_nmem:fne=true->K∉F):
 tgt≤ ∑ A∈pF F ms.toFinset K,
  (2*((K.card*b.wo+∑ i∈A,mkWf ms b.ws b.wo i:ℕ):ℤ)-(b.W:ℤ)):=by
 obtain ⟨cf,p,n,hb,hk',hm,ht,huc,hfe,hfne,htgt,hok⟩:=c;rw[← hb] at hr hws hgF ⊢;rw[← hk'] at hk;rw[← hm] at hlow;rw[← ht] at jC;rw[← huc] at hcp;rw[← hfe] at hfe_mem;rw[← hfne] at hfne_nmem;rw[← htgt];refine XV hok hn hr hws hucF (fun _=>hlow) jC hgF hK hk hcp ?_ ?_
  (fun h=>Zf (hfne_nmem h))
 · intro _ hko;rcases hko with hk0|hfet
   · have v2:K=∅:=qa.mp (hk.trans hk0);subst v2;exact Z4 h0 _
   · exact Z2 (hfe_mem hfet) hK
 · intro _ hkt
   have v0:ms.toFinsetᶜ.card=12-cf.r:=by rw[qu,qCf,qT hn,hr]
   have v1:K=ms.toFinsetᶜ:=qS hK (by rw[hk,hkt,v0]);subst v1;exact Z6 h1 _
lemma Y6 {r:ℕ} (M:SF) (hM:M.card=r) (f:SF->ℤ):
 (∑ K∈Mᶜ.powerset,f K)=∑ k∈range (12-r+1),∑ K∈Mᶜ.powersetCard k,f K:=by
 have v1:Mᶜ.card=12-r:=by rw[qu,qCf,hM]
 have v0:∀ K∈Mᶜ.powerset,K.card∈range (12-r+1):=fun K hK=>
  qMr.mpr (Nat.lt_succ_of_le (v1 ▸ qL (q7.mp hK)))
 rw[← qj v0];refine qh rfl fun k _=>?_;congr 1;ext K;simp
lemma Z4V {F:SS} {k uc:ℕ}
 (hs:(k=2∧¬ Z5g F)∨(k=3∧((uc=1∧uN 12 F)∨(uc=2∧uN 8 F)))∨uc=0):
 ∀ {M K:SF},K⊆Mᶜ->K.card=k->uc≠0->
  ((pF F M K).filter (fun A=>A.card=1)).card≤ (if uc=2 then 3 else 2):=by
 intro M K hKM hKc huc0;rcases hs with ⟨rfl,hq3⟩|⟨rfl,⟨rfl,hf12⟩|⟨rfl,hf8⟩⟩|rfl
 · exact (Xi hq3 hKM hKc).trans (by split_ifs<;>omega)
 · exact YA hf12 hKM hKc
 · exact Xj hf8 hKM hKc
 · exact False.elim (huc0 rfl)
lemma Z4a {r:ℕ} {b:Z4w} {tg:LN} {k uc:ℕ} {tgt:ℤ}
 (c:Z5e b tg k uc false false tgt) {ms:LF} (hn:ms.Nodup) (hr:ms.length=b.r)
 (hbr:b.r=r) (hws:b.ws.length=b.r) {F:SS} (ctx:Z5t F)
 (jC:∀ t∈tg,t≠0->¬ Z3r t F) (hgF:∀ g∈b.gS,Z3L ms g∈F)
 (hcp:∀ K⊆ms.toFinsetᶜ,K.card=k->uc≠0->
  ((pF F ms.toFinset K).filter (fun A=>A.card=1)).card≤ (if uc=2 then 3 else 2)):
 ((12-r).choose k:ℤ)*tgt≤ ∑ K∈ms.toFinsetᶜ.powersetCard k,∑ A∈pF F ms.toFinset K,
  (2*((K.card*b.wo+∑ i∈A,mkWf ms b.ws b.wo i:ℕ):ℤ)-(b.W:ℤ)):=by
 have hc:(ms.toFinsetᶜ.powersetCard k).card=(12-r).choose k:=by rw[qCp,qu,qCf,qT hn,hr,hbr]
 rw[← hc,← nsmul_eq_mul,← sum_const];refine sum_le_sum fun K hK=>?_;obtain ⟨hKM,hKc⟩:=qP.mp hK;exact Z49 c hn hr hws ctx.huc ctx.h0 ctx.h1 ctx.hlow jC hgF hKM hKc (hcp K hKM hKc) (by simp) (by simp)
lemma Z1A {r:ℕ} {b:Z4w} {tg:LN} {k uc:ℕ} {fne0:Bool} {t0 t1:ℤ}
 (c0:Z5e b tg k uc false fne0 t0) (c1:Z5e b tg k uc true false t1)
 {ms:LF} (hn:ms.Nodup) (hr:ms.length=b.r) (hbr:b.r=r) (hws:b.ws.length=b.r)
 {F:SS} (ctx:Z5t F) (jC:∀ t∈tg,t≠0->¬ Z3r t F)
 (hgF:∀ g∈b.gS,Z3L ms g∈F)
 (hcp:∀ K⊆ms.toFinsetᶜ,K.card=k->uc≠0->
  ((pF F ms.toFinset K).filter (fun A=>A.card=1)).card≤ (if uc=2 then 3 else 2)):
 let KkF:=(ms.toFinsetᶜ.powersetCard k).filter (fun K=>K∈F)
 ((12-r).choose k-KkF.card:ℤ)*t0+(KkF.card:ℤ)*t1≤
  ∑ K∈ms.toFinsetᶜ.powersetCard k,∑ A∈pF F ms.toFinset K,
   (2*((K.card*b.wo+∑ i∈A,mkWf ms b.ws b.wo i:ℕ):ℤ)-(b.W:ℤ)):=by
 intro KkF
 have v0:(ms.toFinsetᶜ.powersetCard k).card=(12-r).choose k:=by rw[qCp,qu,qCf,qT hn,hr,hbr]
 have v1:KkF⊆ms.toFinsetᶜ.powersetCard k:=qFs _ _
 have v2:(ms.toFinsetᶜ.powersetCard k \ KkF).card=(12-r).choose k-KkF.card:=by rw[qe v1,v0]
 have hle_tot:KkF.card≤ (12-r).choose k:=v0 ▸ qL v1;rw[← sum_sdiff v1];refine add_le_add ?_ ?_
 · have v3:((12-r).choose k-KkF.card:ℤ)=((ms.toFinsetᶜ.powersetCard k \ KkF).card:ℤ):=by
    rw[v2];omega
   rw[v3,← nsmul_eq_mul,← sum_const];refine sum_le_sum fun K hK=>?_;obtain ⟨hKp,hKn⟩:=qSd.mp hK;obtain ⟨hKM,hKc⟩:=qP.mp hKp;exact Z49 c0 hn hr hws ctx.huc ctx.h0 ctx.h1 ctx.hlow jC hgF hKM hKc (hcp K hKM hKc) (by simp)
    (fun _ hKF=>hKn (qF.mpr ⟨hKp,hKF⟩))
 · rw[← nsmul_eq_mul,← sum_const];refine sum_le_sum fun K hK=>?_;obtain ⟨hKp,hKF⟩:=qF.mp hK;obtain ⟨hKM,hKc⟩:=qP.mp hKp;exact Z49 c1 hn hr hws ctx.huc ctx.h0 ctx.h1 ctx.hlow jC hgF hKM hKc (hcp K hKM hKc) (fun _=>hKF) (by simp)
lemma Z3g {b:Z4w} (tag:ℕ) (tg:LN) {uc3:ℕ} {fne3:Bool}
 {t0 t1 t2 t3_0 t3_1 t4 t5:ℤ}
 (c0:Z5e b tg 0 0 false false t0) (c1:Z5e b tg 1 0 false false t1)
 (c2:Z5e b tg 2 1 false false t2)
 (c3_0:Z5e b tg 3 uc3 false fne3 t3_0) (c3_1:Z5e b tg 3 uc3 true false t3_1)
 (c4:Z5e b tg 4 0 false false t4) (c5:Z5e b tg 5 0 false false t5)
 (hsum:∀ n1:ℕ,n1≤ 2->0≤ t0+5*t1+10*t2+(10-n1:ℤ)*t3_0+(n1:ℤ)*t3_1+5*t4+t5)
 {F:SS} (ctx:Z5t F)
 (hcap3:uc3=0∨(uc3=1∧uN 12 F)∨(uc3=2∧uN 8 F))
 (jC:∀ x∈tg,x≠0->¬ Z3r x F)
 (hbr:b.r=7:=by rfl) (hws:b.ws.length=7:=by rfl) (hWpos:0 < b.W:=by decide)
 (hWsum:b.ws.sum+5*b.wo=b.W:=by rfl) (jE:Z4Y tag=7:=by rfl)
 (jD:Z3Q tag=b.gS:=by rfl):uN tag F:=by
 intro ⟨_,ms,hn,hlen,hg⟩;have hr:ms.length=b.r:=hlen.trans jE|>.trans hbr.symm;have hM:ms.toFinset.card=7:=(qT hn).trans (hr.trans hbr)
 have v3:ms.toFinsetᶜ.card=5:=by rw[qu,qCf,hM]
 have v1:∀ g∈b.gS,Z3L ms g∈F:=fun g hgg=>hg g (jD ▸ hgg);have v0:b.ws.length=b.r:=hws.trans hbr.symm;apply ctx.hno;refine Z7 hn (hr.trans hbr) hws hWsum hWpos ?_;rw[Y6 ms.toFinset hM];simp only[show 12-7+1=6 from rfl,qSg,sum_range_zero,zero_add];have v7:=Z4a c0 hn hr hbr v0 ctx jC v1 (fun K hK=>Z4V (Or.inr (Or.inr rfl)) hK);have v5:=Z4a c1 hn hr hbr v0 ctx jC v1 (fun K hK=>Z4V (Or.inr (Or.inr rfl)) hK);have v4:=Z4a c2 hn hr hbr v0 ctx jC v1 (fun K hK=>Z4V (Or.inl ⟨rfl,ctx.nq3⟩) hK);have v2:=Z1A c3_0 c3_1 hn hr hbr v0 ctx jC v1 (fun K hK=>by
  rcases hcap3 with rfl|⟨rfl,h⟩|⟨rfl,h⟩
  · exact Z4V (Or.inr (Or.inr rfl)) hK
  · exact Z4V (Or.inr (Or.inl ⟨rfl,Or.inl ⟨rfl,h⟩⟩)) hK
  · exact Z4V (Or.inr (Or.inl ⟨rfl,Or.inr ⟨rfl,h⟩⟩)) hK)
 have v9:=Z4a c4 hn hr hbr v0 ctx jC v1 (fun K hK=>Z4V (Or.inr (Or.inr rfl)) hK);have v8:=Z4a c5 hn hr hbr v0 ctx jC v1 (fun K hK=>Z4V (Or.inr (Or.inr rfl)) hK);dsimp only at v2
 have v6:((ms.toFinsetᶜ.powersetCard 3).filter (fun K=>K∈F)).card≤ 2:=by
  by_contra! hgt;obtain ⟨A,B,C,hA,hB,hC,hAB,hAC,hBC⟩:=Zd hgt;obtain ⟨hAp,hAF⟩:=qF.mp hA;obtain ⟨hBp,hBF⟩:=qF.mp hB;obtain ⟨hCp,hCF⟩:=qF.mp hC;obtain ⟨hAM,hAc⟩:=qP.mp hAp;obtain ⟨hBM,hBc⟩:=qP.mp hBp;obtain ⟨hCM,hCc⟩:=qP.mp hCp;exact ctx.nq3 ⟨A,hAF,B,hBF,C,hCF,hAB,hAC,hBC,hAc,hBc,hCc,
   v3 ▸ qL (qUs (qUs hAM hBM) hCM)⟩
 have hcomb:=hsum _ v6;simp only[show (12-7:ℕ).choose 0=1 from rfl,show (12-7:ℕ).choose 1=5 from rfl,
  show (12-7:ℕ).choose 2=10 from rfl,show (12-7:ℕ).choose 3=10 from rfl,
  show (12-7:ℕ).choose 4=5 from rfl,show (12-7:ℕ).choose 5=1 from rfl,
  q2,q1] at v7 v5 v4 v2 v9 v8
 omega
lemma Z1 {M A B C:SF} (hM:M.card=6)
 (hAM:A⊆M) (hBM:B⊆M) (hCM:C⊆M) (hAc:A.card=3) (hBc:B.card=3) (hCc:C.card=3)
 (hAB:A≠B) (hAC:A≠C) (hBC:B≠C) (hnu:¬ (A∪B∪C).card≤ 5):
 (A∪B).card=5∨(A∪C).card=5∨(B∪C).card=5:=by
 by_contra! hno5;have v2:∀ X Y:SF,X≠Y->X.card=3->Y.card=3->(X∪Y).card≠5->
  (X∩Y).card=0∨(X∩Y).card=2:=fun X Y hne hX hY h5=>by
  have hcu:=qCa X Y
  have hlt3:(X∩Y).card < 3:=by
   by_contra! hge3;have v1:X∩Y=X:=qS inter_subset_left (by omega);exact hne (qS (v1 ▸ inter_subset_right) (by omega))
  omega
 have h12:=v2 A B hAB hAc hBc hno5.1;have h13:=v2 A C hAC hAc hCc hno5.2.1;have v6:=v2 B C hBC hBc hCc hno5.2.2;have v0:∀ X Y Z:SF,X⊆M->Y⊆M->Z⊆M->X.card=3->Y.card=3->Z.card=3->
  (Z∩X).card=0∨(Z∩X).card=2->(Z∩Y).card=0∨(Z∩Y).card=2->(X∩Y).card≠0:=by
  intro X Y Z hXM hYM hZM hXc hYc hZc hZX hZY hXY0;have v3:Disjoint X Y:=disjoint_iff_inter_eq_empty.mpr (qa.mp hXY0);have v5:X∪Y=M:=qS (qUs hXM hYM) (by rw[qCu v3,hXc,hYc];omega)
  have v8:Z=(Z∩X)∪(Z∩Y):=by rw[← inter_union_distrib_left,v5,inter_eq_left.mpr hZM]
  have v4:Disjoint (Z∩X) (Z∩Y):=
   disjoint_left.mpr fun a ha1 ha2=>disjoint_left.mp v3 (mem_inter.mp ha1).2 (mem_inter.mp ha2).2
  have hZc':Z.card=(Z∩X).card+(Z∩Y).card:=by conv_lhs=>rw[v8,qCu v4]
  omega
 have ha12:(A∩B).card=2:=h12.resolve_left (v0 A B C hAM hBM hCM hAc hBc hCc
  (by rw[inter_comm];exact h13) (by rw[inter_comm];exact v6))
 have v7:(A∩C).card=2:=h13.resolve_left (v0 A C B hAM hCM hBM hAc hCc hBc
  (by rw[inter_comm];exact h12) v6)
 have hAB4:(A∪B).card=4:=by have:=qCa A B;omega
 have hle_inter:2≤ ((A∪B)∩C).card:=v7 ▸ qL (inter_subset_inter_right qU);have hABC:=qCa (A∪B) C;omega
lemma Z1B {b:Z4w} (tag:ℕ) (tg:LN) {uc3:ℕ}
 {t0 t1 t2 t3_0 t3_1 t4 t5 d5 t6:ℤ}
 (c0:Z5e b tg 0 0 false false t0) (c1:Z5e b tg 1 0 false false t1)
 (c2:Z5e b tg 2 1 false false t2)
 (c3_0:Z5e b tg 3 uc3 false true t3_0) (c3_1:Z5e b tg 3 uc3 true false t3_1)
 (c4:Z5e b tg 4 0 false false t4) (c5:Z5e b tg 5 0 false false t5)
 (c5_l1:Z5e b tg 5 0 true false d5) (c6:Z5e b tg 6 0 false false t6)
 (hsum2:∀ n1:ℕ,n1≤ 2->
  0≤ t0+6*t1+15*t2+(20-n1:ℤ)*t3_0+(n1:ℤ)*t3_1+15*t4+6*t5+t6)
 (hsum3:0≤ t0+6*t1+15*t2+17*t3_0+3*t3_1+15*t4+5*t5+d5+t6)
 (hd5:t5≤ d5) {F:SS} (ctx:Z5t F)
 (hcap3:uc3=0∨(uc3=1∧uN 12 F)∨(uc3=2∧uN 8 F))
 (jC:∀ x∈tg,x≠0->¬ Z3r x F)
 (hbr:b.r=6:=by rfl) (hws:b.ws.length=6:=by rfl) (hWpos:0 < b.W:=by decide)
 (hWsum:b.ws.sum+6*b.wo=b.W:=by rfl) (jE:Z4Y tag=6:=by rfl)
 (jD:Z3Q tag=b.gS:=by rfl):uN tag F:=by
 intro ⟨_,ms,hn,hlen,hg⟩;have hr:ms.length=b.r:=hlen.trans jE|>.trans hbr.symm;have hM:ms.toFinset.card=6:=(qT hn).trans (hr.trans hbr)
 have v6:ms.toFinsetᶜ.card=6:=by rw[qu,qCf,hM]
 have v1:∀ g∈b.gS,Z3L ms g∈F:=fun g hgg=>hg g (jD ▸ hgg);have v0:b.ws.length=b.r:=hws.trans hbr.symm;have v11:∀ K⊆ms.toFinsetᶜ,K.card=3->uc3≠0->
  ((pF F ms.toFinset K).filter (fun A=>A.card=1)).card≤ (if uc3=2 then 3 else 2):=
  fun K hK=>by
   rcases hcap3 with rfl|⟨rfl,h⟩|⟨rfl,h⟩
   · exact Z4V (Or.inr (Or.inr rfl)) hK
   · exact Z4V (Or.inr (Or.inl ⟨rfl,Or.inl ⟨rfl,h⟩⟩)) hK
   · exact Z4V (Or.inr (Or.inl ⟨rfl,Or.inr ⟨rfl,h⟩⟩)) hK
 apply ctx.hno;refine Z7 hn (hr.trans hbr) hws hWsum hWpos ?_;rw[Y6 ms.toFinset hM];simp only[show 12-6+1=7 from rfl,qSg,sum_range_zero,zero_add];have hk0:=Z4a c0 hn hr hbr v0 ctx jC v1 (fun K hK=>Z4V (Or.inr (Or.inr rfl)) hK);have hk1:=Z4a c1 hn hr hbr v0 ctx jC v1 (fun K hK=>Z4V (Or.inr (Or.inr rfl)) hK);have hk2:=Z4a c2 hn hr hbr v0 ctx jC v1 (fun K hK=>Z4V (Or.inl ⟨rfl,ctx.nq3⟩) hK);have v5:=Z1A c3_0 c3_1 hn hr hbr v0 ctx jC v1 v11;have hk4:=Z4a c4 hn hr hbr v0 ctx jC v1 (fun K hK=>Z4V (Or.inr (Or.inr rfl)) hK);have v3:=Z4a c5 hn hr hbr v0 ctx jC v1 (fun K hK=>Z4V (Or.inr (Or.inr rfl)) hK);have v2:=Z1A c5 c5_l1 hn hr hbr v0 ctx jC v1 (fun K hK=>Z4V (Or.inr (Or.inr rfl)) hK);have hk6:=Z4a c6 hn hr hbr v0 ctx jC v1 (fun K hK=>Z4V (Or.inr (Or.inr rfl)) hK);dsimp only at v5 v2;simp only[show (12-6:ℕ).choose 0=1 from rfl,show (12-6:ℕ).choose 1=6 from rfl,
  show (12-6:ℕ).choose 2=15 from rfl,show (12-6:ℕ).choose 3=20 from rfl,
  show (12-6:ℕ).choose 4=15 from rfl,show (12-6:ℕ).choose 5=6 from rfl,
  show (12-6:ℕ).choose 6=1 from rfl,q2,q1] at hk0 hk1 hk2 v5 hk4 v3 v2 hk6
 set K3F:=(ms.toFinsetᶜ.powersetCard 3).filter (fun K=>K∈F)
 have hK3_le:K3F.card≤ 3:=by
  by_contra! hgt;obtain ⟨A,B,C,D,hA,hB,hC,hD,hAB,hAC,hAD,hBC,hBD,hCD⟩:=Zq hgt;obtain ⟨hAp,hAF⟩:=qF.mp hA;obtain ⟨hBp,hBF⟩:=qF.mp hB;obtain ⟨hCp,hCF⟩:=qF.mp hC;obtain ⟨hDp,hDF⟩:=qF.mp hD;obtain ⟨hAM,hAc⟩:=qP.mp hAp;obtain ⟨hBM,hBc⟩:=qP.mp hBp;obtain ⟨hCM,hCc⟩:=qP.mp hCp;obtain ⟨hDM,hDc⟩:=qP.mp hDp;exact ctx.nq4 ⟨A,hAF,B,hBF,C,hCF,D,hDF,hAB,hAC,hAD,hBC,hBD,hCD,hAc,hBc,hCc,hDc,
   v6 ▸ qL (qUs (qUs (qUs hAM hBM) hCM) hDM)⟩
 by_cases hle2:K3F.card≤ 2
 · have v8:=hsum2 K3F.card hle2;omega
 · have v7:K3F.card=3:=by omega
   obtain ⟨A,B,C,hA,hB,hC,hAB,hAC,hBC⟩:=Zd (by omega:3≤ K3F.card);obtain ⟨hAp,hAF⟩:=qF.mp hA;obtain ⟨hBp,hBF⟩:=qF.mp hB;obtain ⟨hCp,hCF⟩:=qF.mp hC;obtain ⟨hAM,hAc⟩:=qP.mp hAp;obtain ⟨hBM,hBc⟩:=qP.mp hBp;obtain ⟨hCM,hCc⟩:=qP.mp hCp;have hnu:¬ (A∪B∪C).card≤ 5:=fun hu=>ctx.nq3 ⟨A,hAF,B,hBF,C,hCF,hAB,hAC,hBC,hAc,hBc,hCc,hu⟩
   have v10:∃ U∈ms.toFinsetᶜ.powersetCard 5,U∈F:=by
    rcases Z1 v6 hAM hBM hCM hAc hBc hCc hAB hAC hBC hnu with h|h|h
    · exact ⟨A∪B,qP.mpr ⟨qUs hAM hBM,h⟩,ctx.huc A hAF B hBF⟩
    · exact ⟨A∪C,qP.mpr ⟨qUs hAM hCM,h⟩,ctx.huc A hAF C hCF⟩
    · exact ⟨B∪C,qP.mpr ⟨qUs hBM hCM,h⟩,ctx.huc B hBF C hCF⟩
   obtain ⟨U,hUp,hUF⟩:=v10;set K5F:=(ms.toFinsetᶜ.powersetCard 5).filter (fun K=>K∈F);have v9:1≤ K5F.card:=qr.mpr ⟨U,qF.mpr ⟨hUp,hUF⟩⟩
   have h5_mul:d5-t5≤ (K5F.card:ℤ)*d5-(K5F.card:ℤ)*t5:=by
    simpa[mul_sub,one_mul] using
     mul_le_mul_of_nonneg_right (by exact_mod_cast v9:(1:ℤ)≤ K5F.card) (sub_nonneg.mpr hd5)
   have v4:(K3F.card:ℤ)=3:=by exact_mod_cast v7
   rw[v4] at v5;rw[sub_mul] at v2;have v8:=hsum3;omega
lemma Z4b {b:Z4w} (tag:ℕ) (tg:LN) {uc3:ℕ}
 {t0 t1 t2 t3_0 t3_1 t4 t5 d5 t6 d6 t7:ℤ}
 (c0:Z5e b tg 0 0 false false t0) (c1:Z5e b tg 1 0 false false t1)
 (c2:Z5e b tg 2 1 false false t2)
 (c3_0:Z5e b tg 3 uc3 false true t3_0) (c3_1:Z5e b tg 3 uc3 true false t3_1)
 (c4:Z5e b tg 4 0 false false t4)
 (c5:Z5e b tg 5 0 false false t5) (c5_l1:Z5e b tg 5 0 true false d5)
 (c6:Z5e b tg 6 0 false false t6) (c6_l1:Z5e b tg 6 0 true false d6)
 (c7:Z5e b tg 7 0 false false t7)
 (hsum:∀ m p5 p6:ℤ,
  (230-96*m+60*p5+116*p6≥0∧30-12*m+12*p5+24*p6≥0∧
   72-2*m+46*p5+90*p6≥0)->
  0≤ t0+7*t1+21*t2+(35-m)*t3_0+m*t3_1+35*t4+
   (21-p5)*t5+p5*d5+(7-p6)*t6+p6*d6+t7)
 {F:SS} (ctx:Z5t F)
 (hcap3:uc3=0∨(uc3=1∧uN 12 F)∨(uc3=2∧uN 8 F))
 (jC:∀ x∈tg,x≠0->¬ Z3r x F)
 (hbr:b.r=5:=by rfl) (hws:b.ws.length=5:=by rfl) (hWpos:0 < b.W:=by decide)
 (hWsum:b.ws.sum+7*b.wo=b.W:=by rfl) (jE:Z4Y tag=5:=by rfl)
 (jD:Z3Q tag=b.gS:=by rfl):uN tag F:=by
 intro ⟨_,ms,hn,hlen,hg⟩;have hr:ms.length=b.r:=hlen.trans jE|>.trans hbr.symm;have hM:ms.toFinset.card=5:=(qT hn).trans (hr.trans hbr)
 have v9:ms.toFinsetᶜ.card=7:=by rw[qu,qCf,hM]
 have v1:∀ g∈b.gS,Z3L ms g∈F:=fun g hgg=>hg g (jD ▸ hgg);have v0:b.ws.length=b.r:=hws.trans hbr.symm;have v10:∀ K⊆ms.toFinsetᶜ,K.card=3->uc3≠0->
  ((pF F ms.toFinset K).filter (fun A=>A.card=1)).card≤ (if uc3=2 then 3 else 2):=
  fun K hK=>by
   rcases hcap3 with rfl|⟨rfl,h⟩|⟨rfl,h⟩
   · exact Z4V (Or.inr (Or.inr rfl)) hK
   · exact Z4V (Or.inr (Or.inl ⟨rfl,Or.inl ⟨rfl,h⟩⟩)) hK
   · exact Z4V (Or.inr (Or.inl ⟨rfl,Or.inr ⟨rfl,h⟩⟩)) hK
 apply ctx.hno;refine Z7 hn (hr.trans hbr) hws hWsum hWpos ?_;rw[Y6 ms.toFinset hM];simp only[show 12-5+1=8 from rfl,qSg,sum_range_zero,zero_add];have hk0:=Z4a c0 hn hr hbr v0 ctx jC v1 (fun K hK=>Z4V (Or.inr (Or.inr rfl)) hK);have hk1:=Z4a c1 hn hr hbr v0 ctx jC v1 (fun K hK=>Z4V (Or.inr (Or.inr rfl)) hK);have hk2:=Z4a c2 hn hr hbr v0 ctx jC v1 (fun K hK=>Z4V (Or.inl ⟨rfl,ctx.nq3⟩) hK);have v6:=Z1A c3_0 c3_1 hn hr hbr v0 ctx jC v1 v10;have hk4:=Z4a c4 hn hr hbr v0 ctx jC v1 (fun K hK=>Z4V (Or.inr (Or.inr rfl)) hK);have v8:=Z1A c5 c5_l1 hn hr hbr v0 ctx jC v1 (fun K hK=>Z4V (Or.inr (Or.inr rfl)) hK);have v7:=Z1A c6 c6_l1 hn hr hbr v0 ctx jC v1 (fun K hK=>Z4V (Or.inr (Or.inr rfl)) hK);have hk7:=Z4a c7 hn hr hbr v0 ctx jC v1 (fun K hK=>Z4V (Or.inr (Or.inr rfl)) hK);dsimp only at v6 v8 v7;simp only[show (12-5:ℕ).choose 0=1 from rfl,show (12-5:ℕ).choose 1=7 from rfl,
  show (12-5:ℕ).choose 2=21 from rfl,show (12-5:ℕ).choose 3=35 from rfl,
  show (12-5:ℕ).choose 4=35 from rfl,show (12-5:ℕ).choose 5=21 from rfl,
  show (12-5:ℕ).choose 6=7 from rfl,show (12-5:ℕ).choose 7=1 from rfl,
  q2,q1] at hk0 hk1 hk2 v6 hk4 v8 v7 hk7
 set K3F:=(ms.toFinsetᶜ.powersetCard 3).filter (fun K=>K∈F);set K5F:=(ms.toFinsetᶜ.powersetCard 5).filter (fun K=>K∈F);set K6F:=(ms.toFinsetᶜ.powersetCard 6).filter (fun K=>K∈F);let ks:=ms.toFinsetᶜ.toList;have v5:ks.Nodup:=qv _
 have v4:ks.length=7:=by rw[q3,v9]
 have v3:ks.toFinset=ms.toFinsetᶜ:=by ext x;simp[ks]
 have v2:=Q0 v5 v4 ctx.huc ctx.nq3 ctx.nq4;dsimp only at v2;rw[v3] at v2;have hcomb:=hsum K3F.card K5F.card K6F.card v2;omega
lemma YE {b:Z4w} (tag:ℕ) {F:SS}
 (ctx:Z5t F) (jE:Z4Y tag=b.r)
 (jD:Z3Q tag=b.gS) (hws:b.ws.length=b.r) (hWpos:0 < b.W)
 (hWsum:b.ws.sum+(12-b.r)*b.wo=b.W) (tfn:ℕ->ℤ)
 (hfib:∀ (ms:LF) (K:SF),ms.Nodup->ms.length=b.r->
  (∀ g∈b.gS,Z3L ms g∈F)->K⊆ms.toFinsetᶜ->
  tfn K.card≤ ∑ A∈pF F ms.toFinset K,
   (2*((K.card*b.wo+∑ i∈A,mkWf ms b.ws b.wo i:ℕ):ℤ)-(b.W:ℤ)))
 (hsum:(0:ℤ)≤ ∑ k∈range (12-b.r+1),((12-b.r).choose k:ℤ)*tfn k):uN tag F:=by
 intro ⟨_,ms,hn,hlen,hg⟩;have hr:ms.length=b.r:=hlen.trans jE;have v0:∀ g∈b.gS,Z3L ms g∈F:=fun g hgg=>hg g (jD ▸ hgg);apply ctx.hno;refine Z7 hn hr hws hWsum hWpos ?_;exact Zz ms.toFinset ((qT hn).trans hr) _ tfn
  (fun K hK=>hfib ms K hn hr v0 hK) hsum
lemma Z4c {b:Z4w} (tag:ℕ) (tg:LN) (r:ℕ) {uc3:ℕ}
 (tfn:ℕ->ℤ)
 (hc:∀ k≤ 12-r,Z5e b tg k (if k=2 then 1 else if k=3 then uc3 else 0) false false (tfn k))
 (hsum:0≤ ∑ k∈range (12-r+1),((12-r).choose k:ℤ)*tfn k)
 {F:SS} (ctx:Z5t F) (hcap3:uc3=0∨(uc3=1∧uN 12 F))
 (jC:∀ x∈tg,x≠0->¬ Z3r x F) (hbr:b.r=r:=by rfl) (hws:b.ws.length=r:=by rfl)
 (hWpos:0 < b.W:=by decide) (hWsum:b.ws.sum+(12-r)*b.wo=b.W:=by rfl)
 (jE:Z4Y tag=r:=by rfl) (jD:Z3Q tag=b.gS:=by rfl):uN tag F:=by
 refine YE tag ctx (jE.trans hbr.symm) jD (hws.trans hbr.symm)
  hWpos (by rw[hbr];exact hWsum) tfn ?_ (by rw[hbr];exact hsum)
 intro ms K hn hr hgF hK;have v0:K.card≤ 12-r:=(by rw[qu,qCf,qT hn,hr,hbr]:ms.toFinsetᶜ.card=12-r)▸ qL hK;refine Z49 (hc K.card v0) hn hr (hws.trans hbr.symm) ctx.huc ctx.h0 ctx.h1 ctx.hlow jC hgF hK rfl ?_ (by simp) (by simp);intro huc0;by_cases hk2:K.card=2
 · have h:=Z4V (Or.inl ⟨rfl,ctx.nq3⟩) hK hk2 huc0;simpa[hk2] using h
 · by_cases hk3:K.card=3
   · rcases hcap3 with rfl|⟨rfl,h12⟩
     · simp[hk3] at huc0
     · have h:=Z4V (Or.inr (Or.inl ⟨rfl,Or.inl ⟨rfl,h12⟩⟩)) hK hk3 (by simp);simpa[hk3] using h
   · simp[hk2,hk3] at huc0
lemma Z1C {b:Z4w} (tag:ℕ) (tg:LN) {uc3:ℕ} {t0 t1 t2 t3 t4 t5:ℤ}
 (c0:Z5e b tg 0 0 false false t0) (c1:Z5e b tg 1 0 false false t1)
 (c2:Z5e b tg 2 1 false false t2) (c3:Z5e b tg 3 uc3 false false t3)
 (c4:Z5e b tg 4 0 false false t4) (c5:Z5e b tg 5 0 false false t5)
 (hsum:0≤ t0+5*t1+10*t2+10*t3+5*t4+t5)
 {F:SS} (ctx:Z5t F) (hcap3:uc3=0∨(uc3=1∧uN 12 F))
 (jC:∀ x∈tg,x≠0->¬ Z3r x F) (hbr:b.r=7:=by rfl) (hws:b.ws.length=7:=by rfl)
 (hWpos:0 < b.W:=by decide) (hWsum:b.ws.sum+5*b.wo=b.W:=by rfl)
 (jE:Z4Y tag=7:=by rfl) (jD:Z3Q tag=b.gS:=by rfl):uN tag F:=
 Z4c tag tg 7 (fun k=>match k with|0=>t0|1=>t1|2=>t2|3=>t3|4=>t4|_=>t5)
  (fun k hk=>by rcases k with _|_|_|_|_|_|n;exacts[c0,c1,c2,c3,c4,c5,by omega])
  (by simpa[qSg,Nat.choose] using hsum) ctx hcap3 jC hbr hws hWpos hWsum jE jD
lemma Z1D {b:Z4w} (tag:ℕ) (tg:LN) {uc3:ℕ} {t0 t1 t2 t3 t4 t5 t6:ℤ}
 (c0:Z5e b tg 0 0 false false t0) (c1:Z5e b tg 1 0 false false t1)
 (c2:Z5e b tg 2 1 false false t2) (c3:Z5e b tg 3 uc3 false false t3)
 (c4:Z5e b tg 4 0 false false t4) (c5:Z5e b tg 5 0 false false t5) (c6:Z5e b tg 6 0 false false t6)
 (hsum:0≤ t0+6*t1+15*t2+20*t3+15*t4+6*t5+t6)
 {F:SS} (ctx:Z5t F) (hcap3:uc3=0∨(uc3=1∧uN 12 F))
 (jC:∀ x∈tg,x≠0->¬ Z3r x F) (hbr:b.r=6:=by rfl) (hws:b.ws.length=6:=by rfl)
 (hWpos:0 < b.W:=by decide) (hWsum:b.ws.sum+6*b.wo=b.W:=by rfl)
 (jE:Z4Y tag=6:=by rfl) (jD:Z3Q tag=b.gS:=by rfl):uN tag F:=
 Z4c tag tg 6 (fun k=>match k with|0=>t0|1=>t1|2=>t2|3=>t3|4=>t4|5=>t5|_=>t6)
  (fun k hk=>by rcases k with _|_|_|_|_|_|_|n;exacts[c0,c1,c2,c3,c4,c5,c6,by omega])
  (by simpa[qSg,Nat.choose] using hsum) ctx hcap3 jC hbr hws hWpos hWsum jE jD
lemma Z1E {b:Z4w} (tag:ℕ) (tg:LN) {uc3:ℕ} {t0 t1 t2 t3 t4 t5 t6 t7:ℤ}
 (c0:Z5e b tg 0 0 false false t0) (c1:Z5e b tg 1 0 false false t1)
 (c2:Z5e b tg 2 1 false false t2) (c3:Z5e b tg 3 uc3 false false t3)
 (c4:Z5e b tg 4 0 false false t4) (c5:Z5e b tg 5 0 false false t5)
 (c6:Z5e b tg 6 0 false false t6) (c7:Z5e b tg 7 0 false false t7)
 (hsum:0≤ t0+7*t1+21*t2+35*t3+35*t4+21*t5+7*t6+t7)
 {F:SS} (ctx:Z5t F) (hcap3:uc3=0∨(uc3=1∧uN 12 F))
 (jC:∀ x∈tg,x≠0->¬ Z3r x F) (hbr:b.r=5:=by rfl) (hws:b.ws.length=5:=by rfl)
 (hWpos:0 < b.W:=by decide) (hWsum:b.ws.sum+7*b.wo=b.W:=by rfl)
 (jE:Z4Y tag=5:=by rfl) (jD:Z3Q tag=b.gS:=by rfl):uN tag F:=
 Z4c tag tg 5 (fun k=>match k with|0=>t0|1=>t1|2=>t2|3=>t3|4=>t4|5=>t5|6=>t6|_=>t7)
  (fun k hk=>by rcases k with _|_|_|_|_|_|_|_|n;exacts[c0,c1,c2,c3,c4,c5,c6,c7,by omega])
  (by simpa[qSg,Nat.choose] using hsum) ctx hcap3 jC hbr hws hWpos hWsum jE jD
lemma Z1F {b:Z4w} (tag:ℕ) (tg:LN) {uc3:ℕ} {t0 t1 t2 t3 t4 t5 t6 t7 t8:ℤ}
 (c0:Z5e b tg 0 0 false false t0) (c1:Z5e b tg 1 0 false false t1)
 (c2:Z5e b tg 2 1 false false t2) (c3:Z5e b tg 3 uc3 false false t3)
 (c4:Z5e b tg 4 0 false false t4) (c5:Z5e b tg 5 0 false false t5)
 (c6:Z5e b tg 6 0 false false t6) (c7:Z5e b tg 7 0 false false t7) (c8:Z5e b tg 8 0 false false t8)
 (hsum:0≤ t0+8*t1+28*t2+56*t3+70*t4+56*t5+28*t6+8*t7+t8)
 {F:SS} (ctx:Z5t F) (hcap3:uc3=0∨(uc3=1∧uN 12 F))
 (jC:∀ x∈tg,x≠0->¬ Z3r x F) (hbr:b.r=4:=by rfl) (hws:b.ws.length=4:=by rfl)
 (hWpos:0 < b.W:=by decide) (hWsum:b.ws.sum+8*b.wo=b.W:=by rfl)
 (jE:Z4Y tag=4:=by rfl) (jD:Z3Q tag=b.gS:=by rfl):uN tag F:=
 Z4c tag tg 4 (fun k=>match k with|0=>t0|1=>t1|2=>t2|3=>t3|4=>t4|5=>t5|6=>t6|7=>t7|_=>t8)
  (fun k hk=>by rcases k with _|_|_|_|_|_|_|_|_|n;exacts[c0,c1,c2,c3,c4,c5,c6,c7,c8,by omega])
  (by simpa[qSg,Nat.choose] using hsum) ctx hcap3 jC hbr hws hWpos hWsum jE jD
lemma Z1G {b:Z4w} (tag:ℕ) (tg:LN) {uc3:ℕ} {t0 t1 t2 t3 t4 t5 t6 t7 t8 t9:ℤ}
 (c0:Z5e b tg 0 0 false false t0) (c1:Z5e b tg 1 0 false false t1)
 (c2:Z5e b tg 2 1 false false t2) (c3:Z5e b tg 3 uc3 false false t3)
 (c4:Z5e b tg 4 0 false false t4) (c5:Z5e b tg 5 0 false false t5)
 (c6:Z5e b tg 6 0 false false t6) (c7:Z5e b tg 7 0 false false t7)
 (c8:Z5e b tg 8 0 false false t8) (c9:Z5e b tg 9 0 false false t9)
 (hsum:0≤ t0+9*t1+36*t2+84*t3+126*t4+126*t5+84*t6+36*t7+9*t8+t9)
 {F:SS} (ctx:Z5t F) (hcap3:uc3=0∨(uc3=1∧uN 12 F))
 (jC:∀ x∈tg,x≠0->¬ Z3r x F) (hbr:b.r=3:=by rfl) (hws:b.ws.length=3:=by rfl)
 (hWpos:0 < b.W:=by decide) (hWsum:b.ws.sum+9*b.wo=b.W:=by rfl)
 (jE:Z4Y tag=3:=by rfl) (jD:Z3Q tag=b.gS:=by rfl):uN tag F:=
 Z4c tag tg 3 (fun k=>match k with|0=>t0|1=>t1|2=>t2|3=>t3|4=>t4|5=>t5|6=>t6|7=>t7|8=>t8|_=>t9)
  (fun k hk=>by rcases k with _|_|_|_|_|_|_|_|_|_|n;exacts[c0,c1,c2,c3,c4,c5,c6,c7,c8,c9,by omega])
  (by simpa[qSg,Nat.choose] using hsum) ctx hcap3 jC hbr hws hWpos hWsum jE jD
lemma h1_a {F:SS} (v1:Z5t F):uN 1 F∧uN 2 F∧uN 4 F∧uN 5 F:=by
 have v0:=Z4b 1 [34,35] (u1 k11 0) (u1 k11 1) (u1 k11 2) (u1 k11 3) (u1 k11 4) (u1 k11 5) (u1 k11 6) (u1 k11 9) (u1 k11 7) (u1 k11 10) (u1 k11 8) (fun m p5 p6 ⟨h1,_,_⟩=>by omega) v1 (Or.inl rfl) (Z5u v1.nq3 v1.nq4)
 have v4:=Z1B 2 [34,35] (u1 k12 0) (u1 k12 1) (u1 k12 2) (u1 k12 3) (u1 k12 4) (u1 k12 5) (u1 k12 6) (u1 k12 8) (u1 k12 7) (fun _ _=>by omega) (by decide) (by decide) v1 (Or.inl rfl) (Z5u v1.nq3 v1.nq4)
 have nf3:=Z1B 3 [2,34,35] (u1 k13 0) (u1 k13 1) (u1 k13 2) (u1 k13 3) (u1 k13 4) (u1 k13 5) (u1 k13 6) (u1 k13 8) (u1 k13 7) (fun _ _=>by omega) (by decide) (by decide) v1 (Or.inl rfl) (pc v4 (Z5u v1.nq3 v1.nq4))
 have v2:=Z4b 4 [3,34,35] (u1 k14 0) (u1 k14 1) (u1 k14 2) (u1 k14 3) (u1 k14 4) (u1 k14 5) (u1 k14 6) (u1 k14 9) (u1 k14 7) (u1 k14 10) (u1 k14 8) (fun m p5 p6 ⟨_,h2,_⟩=>by omega) v1 (Or.inl rfl) (pc nf3 (Z5u v1.nq3 v1.nq4))
 have v5:=Z1B 5 [1,2,3,4,34] (u1 k15 0) (u1 k15 1) (u1 k15 2) (u1 k15 3) (u1 k15 4) (u1 k15 5) (u1 k15 6) (u1 k15 8) (u1 k15 7) (fun _ _=>by omega) (by decide) (by decide) v1 (Or.inl rfl) (pc v0 (pc v4 (pc nf3 (pc v2 (pq3 v1.nq3)))))
 exact ⟨v0,v4,v2,v5⟩
lemma h1_b {F:SS} (v1:Z5t F) (v0:uN 1 F) (v2:uN 4 F) (v5:uN 5 F):uN 6 F∧uN 8 F∧uN 9 F∧uN 10 F:=by
 have nf6:=Z3g 6 [1,4,5] (u1 k16 0) (u1 k16 1) (ck1 Z2Q rfl) (ck1 Z2R rfl) (ck1 XR rfl) (u1 k16 2) (u1 k16 3) (fun _ _=>by omega) v1 (Or.inl rfl) (pc v0 (pc v2 (pc v5 pn)))
 have nf7:=Z1D 7 [6,34,35] (u1 k17 0) (u1 k17 1) (u1 k17 2) (u1 k17 3) (u1 k17 4) (u1 k17 5) (u1 k17 6) (by decide) v1 (Or.inl rfl) (pc nf6 (Z5u v1.nq3 v1.nq4))
 have v7:=Z3g 8 [1,4,5,6,7,34] (u1 k18 0) (u1 k18 1) (ck1 Z32 rfl) (ck1 Z33 rfl) (ck1 XS rfl) (u1 k18 2) (u1 k18 3) (fun _ _=>by omega) v1 (Or.inl rfl) (pc v0 (pc v2 (pc v5 (pc nf6 (pc nf7 (pq3 v1.nq3))))))
 have nf9:=Z1B 9 [1,4,5,6,34] (u1 k19 0) (u1 k19 1) (u1 k19 2) (u1 k19 3) (u1 k19 4) (u1 k19 5) (u1 k19 6) (u1 k19 8) (u1 k19 7) (fun _ _=>by omega) (by decide) (by decide) v1 (Or.inr (Or.inr ⟨rfl,v7⟩)) (pc v0 (pc v2 (pc v5 (pc nf6 (pq3 v1.nq3)))))
 have v16:=Z3g 10 [1,4,5,8,9,34] (u1 k20 0) (u1 k20 1) (ck1 Z0i rfl) (ck1 Z0j rfl) (ck1 X9 rfl) (u1 k20 2) (u1 k20 3) (fun _ _=>by omega) v1 (Or.inr (Or.inr ⟨rfl,v7⟩)) (pc v0 (pc v2 (pc v5 (pc v7 (pc nf9 (pq3 v1.nq3))))))
 exact ⟨nf6,v7,nf9,v16⟩
lemma h1_c {F:SS} (v1:Z5t F) (v0:uN 1 F) (v2:uN 4 F) (v5:uN 5 F) (v7:uN 8 F) (nf9:uN 9 F) (v16:uN 10 F):uN 12 F∧uN 14 F∧uN 17 F:=by
 have v8:=Z1B 11 [4,5,10,34] (u1 k21 0) (u1 k21 1) (u1 k21 2) (u1 k21 3) (ck1 Xa rfl) (u1 k21 4) (u1 k21 5) (u1 k21 7) (u1 k21 6) (fun _ _=>by omega) (by decide) (by decide) v1 (Or.inr (Or.inr ⟨rfl,v7⟩)) (pc v2 (pc v5 (pc v16 (pq3 v1.nq3))))
 have v3:=Z1B 12 [4,8,9,34] (u1 k22 0) (u1 k22 1) (ck1 Z0v rfl) (u1 k22 2) (u1 k22 3) (u1 k22 4) (u1 k22 5) (u1 k22 7) (u1 k22 6) (fun _ _=>by omega) (by decide) (by decide) v1 (Or.inr (Or.inr ⟨rfl,v7⟩)) (pc v2 (pc v7 (pc nf9 (pq3 v1.nq3))))
 have v17:=Z4b 13 [4,5,11] (u1 k23 0) (u1 k23 1) (u1 k23 2) (u1 k23 3) (u1 k23 4) (u1 k23 5) (u1 k23 6) (u1 k23 9) (u1 k23 7) (u1 k23 10) (u1 k23 8) (fun m p5 p6 ⟨_,_,h3⟩=>by omega) v1 (Or.inr (Or.inl ⟨rfl,v3⟩)) (pc v2 (pc v5 (pc v8 pn)))
 have v10:=Z3g 14 [1,4,5,11,12,13,34] (u1 k24 0) (u1 k24 1) (ck1 Z0K rfl) (u1 k24 2) (u1 k24 3) (u1 k24 4) (u1 k24 5) (fun _ _=>by omega) v1 (Or.inr (Or.inl ⟨rfl,v3⟩)) (pc v0 (pc v2 (pc v5 (pc v8 (pc v3 (pc v17 (pq3 v1.nq3)))))))
 have v6:=Z1D 17 [5,11,34] (u1 k25 0) (u1 k25 1) (u1 k25 2) (u1 k25 3) (u1 k25 4) (u1 k25 5) (u1 k25 6) (by decide) v1 (Or.inr ⟨rfl,v3⟩) (pc v5 (pc v8 (pq3 v1.nq3)));exact ⟨v3,v10,v6⟩
lemma h1_d {F:SS} (v1:Z5t F) (v2:uN 4 F) (v5:uN 5 F) (v3:uN 12 F) (v10:uN 14 F) (v6:uN 17 F):uN 25 F:=by
 have v9:=Z1F 18 [4,5,14,17,34] (u1 k26 0) (u1 k26 1) (u1 k26 2) (u1 k26 3) (u1 k26 4) (u1 k26 5) (u1 k26 6) (u1 k26 7) (u1 k26 8) (by decide) v1 (Or.inr ⟨rfl,v3⟩) (pc v2 (pc v5 (pc v10 (pc v6 (pq3 v1.nq3)))));have v12:=Z1D 20 [4,12,17,18] (u1 k27 0) (u1 k27 1) (ck1 Z15 rfl) (u1 k27 2) (u1 k27 3) (u1 k27 4) (u1 k27 5) (by decide) v1 (Or.inr ⟨rfl,v3⟩) (pc v2 (pc v3 (pc v6 (pc v9 pn))));have v15:=Z1E 22 [4,14,17,20,34] (u1 k28 0) (u1 k28 1) (u1 k28 2) (u1 k28 3) (u1 k28 4) (u1 k28 5) (u1 k28 6) (u1 k28 7) (by decide) v1 (Or.inr ⟨rfl,v3⟩) (pc v2 (pc v10 (pc v6 (pc v12 (pq3 v1.nq3)))));have v18:=Z1C 24 [4,17,20,34] (u1 k29 0) (u1 k29 1) (ck1 Z1k rfl) (u1 k29 2) (u1 k29 3) (u1 k29 4) (by decide) v1 (Or.inr ⟨rfl,v3⟩) (pc v2 (pc v6 (pc v12 (pq3 v1.nq3))));exact Z1G 25 [4,5,17,18,22,24] (u1 k30 0) (u1 k30 1) (u1 k30 2) (u1 k30 3) (u1 k30 4) (u1 k30 5) (u1 k30 6) (u1 k30 7) (u1 k30 8) (u1 k30 9) (by decide) v1 (Or.inr ⟨rfl,v3⟩) (pc v2 (pc v5 (pc v6 (pc v9 (pc v15 (pc v18 pn))))))
lemma h1_main:∀ F:SS,iUC F->∅∈F->univ∈F->(∃ S∈F,S.card=3)->(∀ S∈F,S.Nonempty->3≤ S.card)->
 ∃ w:WF,0 < ∑ i,w i∧F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i):=by
 intro F closed empty full ⟨S,hSF,hSc⟩ low;by_contra hno;have nq3:¬ Z5g F:=fun hq=>hno (Z3H closed hq);have nq4:¬ Z5h F:=fun hq=>hno (Z3I closed nq3 hq);let v1:Z5t F:=⟨hno,closed,empty,full,low,nq3,nq4⟩;obtain ⟨v0,v4,v2,v5⟩:=h1_a v1;obtain ⟨nf6,v7,nf9,v16⟩:=h1_b v1 v0 v2 v5;obtain ⟨v3,v10,v6⟩:=h1_c v1 v0 v2 v5 v7 nf9 v16;apply h1_d v1 v2 v5 v3 v10 v6;refine ⟨by decide,S.toList,S.nodup_toList,by rw[q3,hSc];rfl,fun g hg=>?_⟩;simp only[Z3Q,qC,qNm,qs] at hg;subst hg
 have v19:S.toList.length=3:=by rw[q3,hSc]
 have h7:7=2 ^ S.toList.length-1:=by rw[v19];decide
 rw[h7,Xv];simpa using hSF
end UP
namespace UH
open Finset UnionClosed UC
open List (not_mem_nil nodup_cons getElem_mem mem_of_getElem contains_eq_mem getElem_map)
open Option (getD_some isSome_iff_exists)
open scoped Classical
abbrev SS:=UC.SS
abbrev SF:=UC.SF
def ly {α:Type*} (G:Finset (Finset α)) (r:ℕ):Finset (Finset α):=
 G.filter (fun A=>A.card=r)
lemma ZU {α:Type*} [DecidableEq α] (s:Finset α) (p:α->Prop)
 [DecidablePred p] [DecidablePred (fun x=>¬ p x)]:
 (s.filter p).card+(s.filter (fun x=>¬ p x)).card=s.card:=by
 have v1:s.filter p⊆s:=qFs p s
 have v0:s \ s.filter p=s.filter (fun x=>¬ p x):=by
  ext x;simp only[qSd,qF];tauto
 rw[← v0,add_comm];exact card_sdiff_add_card_eq_card v1
lemma mLy {α:Type*} {G:Finset (Finset α)} {r:ℕ} {A:Finset α}:
 A∈ly G r↔A∈G∧A.card=r:=by
 simp[ly]
lemma Zg {α:Type*} [DecidableEq α] {M:Finset α}
 {G:Finset (Finset α)} (hGM:G⊆M.powerset) (r:ℕ):
 ly G r⊆M.powersetCard r:=by
 intro A hA;obtain ⟨hAG,hAr⟩:=mLy.mp hA;exact qP.mpr ⟨q7.mp (hGM hAG),hAr⟩
lemma Z3h {α:Type*} [DecidableEq α] {M:Finset α}
 {G:Finset (Finset α)} (hGM:G⊆M.powerset) (r:ℕ):
 (ly G r).card≤ M.card.choose r:=
 (qL (Zg hGM r)).trans_eq (qCp r M)
lemma Z3J {α:Type*} [DecidableEq α] {M:Finset α}
 {G:Finset (Finset α)} (hGM:G⊆M.powerset) (f:ℕ->ℤ):
 (∑ A∈G,f A.card)=∑ r∈range (M.card+1),((ly G r).card:ℤ)*f r:=by
 have v1:∀ A∈G,A.card∈range (M.card+1):=by
  intro A hA;exact qMr.mpr (Nat.lt_succ_of_le (qL (q7.mp (hGM hA))))
 rw[← qj v1];apply qh rfl;intro r _;change (∑ A∈ly G r,f A.card)=((ly G r).card:ℤ)*f r;have v0:∑ A∈ly G r,f A.card=∑ _A∈ly G r,f r:=
  qh rfl (fun A hA=>by rw[(mLy.mp hA).2])
 rw[v0,sum_const,nsmul_eq_mul]
lemma YF {α:Type*} [DecidableEq α] {M e:Finset α}
 (heM:e⊆M) {r:ℕ} (her:e.card=r) (s:ℕ):
 ((M.powersetCard s).filter (fun T=>e⊆T)).card≤ (M.card-r).choose (s-r):=by
 have v0:((M \ e).powersetCard (s-r)).card=(M.card-r).choose (s-r):=by rw[qCp,qe heM,her]
 rw[← v0];apply card_le_card_of_injOn (fun T=>T \ e)
 · intro T hT;obtain ⟨hTm,heT⟩:=qF.mp hT;obtain ⟨hTM,hTs⟩:=qP.mp hTm;dsimp only;rw[mem_coe,qP];refine ⟨sdiff_subset_sdiff hTM Subset.rfl,?_⟩;rw[qe heT,hTs,her]
 · intro T₁ hT₁ T₂ hT₂ heq;dsimp only at heq;have heT₁:e⊆T₁:=(qF.mp hT₁).2;have heT₂:e⊆T₂:=(qF.mp hT₂).2
   calc T₁=(T₁ \ e)∪e:=(sdiff_union_of_subset heT₁).symm
    _=(T₂ \ e)∪e:=by rw[heq]
    _=T₂:=sdiff_union_of_subset heT₂
lemma ZE {α:Type*} [DecidableEq α] {M e:Finset α}
 {G:Finset (Finset α)} (hGM:G⊆M.powerset) (heM:e⊆M)
 {r:ℕ} (her:e.card=r) (s:ℕ) (heG:∀ A∈G,e⊆A):
 (ly G s).card≤ (M.card-r).choose (s-r):=by
 have v0:ly G s⊆(M.powersetCard s).filter (fun T=>e⊆T):=by
  intro A hA;exact qF.mpr ⟨Zg hGM s hA,heG A (mLy.mp hA).1⟩
 exact (qL v0).trans (YF heM her s)
lemma Zh {α:Type*} [DecidableEq α] {M:Finset α}
 {G:Finset (Finset α)} (hGM:G⊆M.powerset) (r s a b:ℕ)
 (ha:∀ Q∈M.powersetCard s \ ly G s,
  a≤ ((M.powersetCard r \ ly G r).filter (fun e=>e⊆Q)).card)
 (hb:∀ e∈M.powersetCard r \ ly G r,
  ((M.powersetCard s \ ly G s).filter (fun Q=>e⊆Q)).card≤ b):
 a*(M.card.choose s-(ly G s).card)≤ b*(M.card.choose r-(ly G r).card):=by
 let Cr:=M.powersetCard r \ ly G r;let Cs:=M.powersetCard s \ ly G s
 have v1:Cr.card=M.card.choose r-(ly G r).card:=by
  dsimp[Cr];rw[qe (Zg hGM r),qCp]
 have v0:Cs.card=M.card.choose s-(ly G s).card:=by
  dsimp[Cs];rw[qe (Zg hGM s),qCp]
 rw[← v1,← v0]
 have h1:a*Cs.card≤ ∑ Q∈Cs,(Cr.filter (fun e=>e⊆Q)).card:=by
  have:=sum_le_sum (s:=Cs) (fun Q hQ=>ha Q hQ);simpa[nsmul_eq_mul,qY] using this
 have h2:(∑ Q∈Cs,(Cr.filter (fun e=>e⊆Q)).card)=
  ∑ e∈Cr,(Cs.filter (fun Q=>e⊆Q)).card:=by
  simp only[card_filter];exact sum_comm
 have h3:(∑ e∈Cr,(Cs.filter (fun Q=>e⊆Q)).card)≤ b*Cr.card:=by
  have:=sum_le_sum (s:=Cr) (fun e he=>hb e he);simpa[nsmul_eq_mul,qY] using this
 exact h1.trans (h2.trans_le h3)
lemma ZV {α:Type*} [DecidableEq α] {M:Finset α}
 {G:Finset (Finset α)} (hGM:G⊆M.powerset) (hc:iUC G)
 (r:ℕ) (hr:1≤ r):
 (r.choose (r-1)-1)*(M.card.choose r-(ly G r).card)≤
  (M.card-(r-1))*(M.card.choose (r-1)-(ly G (r-1)).card):=by
 apply Zh hGM (r-1) r (r.choose (r-1)-1) (M.card-(r-1))
 · intro Q hQ;obtain ⟨hQm,hQnot⟩:=qSd.mp hQ;obtain ⟨hQM,hQr⟩:=qP.mp hQm;have v6:Q∉G:=fun h=>hQnot (mLy.mpr ⟨h,hQr⟩);let P:=Q.powersetCard (r-1)
   have hPcard:P.card=r.choose (r-1):=by rw[qCp,hQr]
   have hI:(P.filter (fun e=>e∈ly G (r-1))).card≤ 1:=by
    refine card_le_one.mpr ?_;intro A hA B hB;by_contra hne;obtain ⟨hAP,hAL⟩:=qF.mp hA;obtain ⟨hBP,hBL⟩:=qF.mp hB;obtain ⟨hAQ,hAc⟩:=qP.mp hAP;obtain ⟨hBQ,hBc⟩:=qP.mp hBP;have v3:A ⊂ A∪B:=Finset.ssubset_iff_subset_ne.mpr ⟨qU,fun heq=>by
     have v5:B⊆A:=qUr.trans_eq heq.symm;exact hne (qS v5 (by omega)).symm⟩
    have hlt:=card_lt_card v3;have v1:=qL (qUs hAQ hBQ);have v4:A∪B=Q:=qS (qUs hAQ hBQ) (by omega);exact v6 (v4 ▸ hc A (mLy.mp hAL).1 B (mLy.mp hBL).1)
   have hpart:=ZU P (fun e=>e∈ly G (r-1));have v0:P.filter (fun e=>e∉ly G (r-1))⊆
    (M.powersetCard (r-1)\ ly G (r-1)).filter (fun e=>e⊆Q):=by
    intro e he;obtain ⟨heP,henot⟩:=qF.mp he;obtain ⟨heQ,hec⟩:=qP.mp heP;exact qF.mpr ⟨qSd.mpr ⟨qP.mpr ⟨heQ.trans hQM,hec⟩,henot⟩,heQ⟩
   have v1:=qL v0;omega
 · intro e he;obtain ⟨hem,_⟩:=qSd.mp he;obtain ⟨heM,her⟩:=qP.mp hem;have v0:(M.powersetCard r \ ly G r).filter (fun Q=>e⊆Q)⊆
    (M.powersetCard r).filter (fun Q=>e⊆Q):=
    filter_subset_filter _ sdiff_subset
   have v1:=(qL v0).trans (YF heM her r)
   have v2:r-(r-1)=1:=by omega
   simpa[v2,Nat.choose_one_right] using v1
lemma ZW {α:Type*} [DecidableEq α] {M:Finset α}
 {G:Finset (Finset α)} (hGM:G⊆M.powerset) (hc:iUC G):
 3*(M.card.choose 4-(ly G 4).card)≤
  ((M.card-2).choose 2)*(M.card.choose 2-(ly G 2).card):=by
 apply Zh hGM 2 4 3 ((M.card-2).choose 2)
 · intro Q hQ;obtain ⟨hQm,hQnot⟩:=qSd.mp hQ;obtain ⟨hQM,hQr⟩:=qP.mp hQm;have v3:Q∉G:=fun h=>hQnot (mLy.mpr ⟨h,hQr⟩);let P:=Q.powersetCard 2
   have hPcard:P.card=6:=by rw[qCp,hQr];decide
   have hI:(P.filter (fun e=>e∈ly G 2)).card≤
    (P.filter (fun e=>e∉ly G 2)).card:=by
    apply card_le_card_of_injOn (fun A=>Q \ A)
    · intro A hA;obtain ⟨hAP,hAL⟩:=qF.mp hA;obtain ⟨hAQ,hAc⟩:=qP.mp hAP
      have v1:Q \ A∈P:=by
       rw[qP];refine ⟨sdiff_subset,?_⟩;rw[qe hAQ,hQr,hAc]
      refine mem_coe.mpr (qF.mpr ⟨v1,fun hcompL=>?_⟩);have v2:A∪(Q \ A)∈G:=hc A (mLy.mp hAL).1 (Q \ A) (mLy.mp hcompL).1;rw[union_sdiff_of_subset hAQ] at v2;exact v3 v2
    · intro A₁ hA₁ A₂ hA₂ heq;dsimp only at heq;have hAQ₁:A₁⊆Q:=(qP.mp (qF.mp hA₁).1).1;have hAQ₂:A₂⊆Q:=(qP.mp (qF.mp hA₂).1).1
      calc A₁=Q \ (Q \ A₁):=(Finset.sdiff_sdiff_eq_self hAQ₁).symm
       _=Q \ (Q \ A₂):=by rw[heq]
       _=A₂:=Finset.sdiff_sdiff_eq_self hAQ₂
   have hpart:=ZU P (fun e=>e∈ly G 2);have v0:P.filter (fun e=>e∉ly G 2)⊆
    (M.powersetCard 2 \ ly G 2).filter (fun e=>e⊆Q):=by
    intro e he;obtain ⟨heP,henot⟩:=qF.mp he;obtain ⟨heQ,hec⟩:=qP.mp heP;exact qF.mpr ⟨qSd.mpr ⟨qP.mpr ⟨heQ.trans hQM,hec⟩,henot⟩,heQ⟩
   have hle:=qL v0;omega
 · intro e he;obtain ⟨hem,_⟩:=qSd.mp he;obtain ⟨heM,her⟩:=qP.mp hem;have v0:(M.powersetCard 4 \ ly G 4).filter (fun Q=>e⊆Q)⊆
    (M.powersetCard 4).filter (fun Q=>e⊆Q):=
    filter_subset_filter _ sdiff_subset
   exact (qL v0).trans (YF heM her 4)
lemma ZA {α:Type*} [DecidableEq α] {M:Finset α}
 {G:Finset (Finset α)} (hc:iUC G) {B:Finset α}
 (hne:B.Nonempty) (hB:B⊆M.filter (fun x=>{x}∈G)):B∈G:=by
 induction B using Finset.induction_on with
 | empty=>exact (not_nonempty_empty hne).elim
 | @insert x s hx ih=>
  have v0:{x}∈G:=(qF.mp (hB (mem_insert_self x s))).2;by_cases hs:s.Nonempty
  · have v1:s∈G:=ih hs (fun y hy=>hB (mem_insert_of_mem hy));have hu:{x}∪s=insert x s:=singleton_union x s;exact hu ▸ hc {x} v0 s v1
  · rw[not_nonempty_iff_eq_empty.mp hs];exact v0
lemma Xo {α:Type*} [DecidableEq α] {M:Finset α}
 {G:Finset (Finset α)} (hGM:G⊆M.powerset):
 (M.filter (fun x=>{x}∈G)).card=(ly G 1).card:=by
 have v1:ly G 1=(M.filter (fun x=>{x}∈G)).image (fun x=>{x}):=by
  ext A;constructor
  · intro hA;obtain ⟨hAG,hAc⟩:=mLy.mp hA;obtain ⟨x,rfl⟩:=qC1.mp hAc;have v0:x∈M:=qf.mp (q7.mp (hGM hAG));exact qI.mpr ⟨x,qF.mpr ⟨v0,hAG⟩,rfl⟩
  · intro hA;obtain ⟨x,hx,rfl⟩:=qI.mp hA;exact mLy.mpr ⟨(qF.mp hx).2,qw x⟩
 rw[v1,qK _ singleton_injective]
lemma Xp {α:Type*} [DecidableEq α] {M:Finset α}
 {G:Finset (Finset α)} (hGM:G⊆M.powerset) (hc:iUC G)
 (r:ℕ) (hr:1≤ r):
 ((ly G 1).card).choose r≤ (ly G r).card:=by
 let U1:=M.filter (fun x=>{x}∈G);rw[← Xo hGM,← qCp r U1];apply qL;intro B hB;obtain ⟨hBU,hBr⟩:=qP.mp hB;have v0:B.Nonempty:=qr.mp (by omega);exact mLy.mpr ⟨ZA hc v0 hBU,hBr⟩
lemma Zi {α:Type*} [DecidableEq α] {M:Finset α}
 {G:Finset (Finset α)} (hGM:G⊆M.powerset) (hc:iUC G)
 (h1:1≤ (ly G 1).card):
 (ly G 2).card≤ (ly G 3).card+(M.card-1):=by
 obtain ⟨X,hX⟩:=qr.mp (by omega:0 < (ly G 1).card);obtain ⟨hXG,hXc⟩:=mLy.mp hX;obtain ⟨a,rfl⟩:=qC1.mp hXc;have v2:{a}⊆M:=q7.mp (hGM hXG);have hpart:=ZU (ly G 2) (fun B=>a∈B)
 have hwith:((ly G 2).filter (fun B=>a∈B)).card≤ M.card-1:=by
  have v0:(ly G 2).filter (fun B=>a∈B)⊆
   (M.powersetCard 2).filter (fun B=>{a}⊆B):=by
   intro B hB;obtain ⟨hBL,haB⟩:=qF.mp hB;exact qF.mpr ⟨Zg hGM 2 hBL,qf.mpr haB⟩
  have v1:=(qL v0).trans (YF v2 (qw a) 2);simpa[Nat.choose_one_right] using v1
 have hwithout:((ly G 2).filter (fun B=>a∉B)).card≤ (ly G 3).card:=by
  apply card_le_card_of_injOn (fun B=>{a}∪B)
  · intro B hB;obtain ⟨hBL,hnaB⟩:=qF.mp hB;obtain ⟨hBG,hBc⟩:=mLy.mp hBL;dsimp only;rw[mem_coe,mLy];refine ⟨hc {a} hXG B hBG,?_⟩;rw[singleton_union,card_insert_of_notMem hnaB,hBc]
  · intro B₁ hB₁ B₂ hB₂ heq;dsimp only at heq;have hn₁:a∉B₁:=(qF.mp hB₁).2;have hn₂:a∉B₂:=(qF.mp hB₂).2;rw[singleton_union,singleton_union] at heq
    calc B₁=(insert a B₁).erase a:=(erase_insert hn₁).symm
     _=(insert a B₂).erase a:=by rw[heq]
     _=B₂:=erase_insert hn₂
 omega
lemma ZX {α:Type*} [DecidableEq α] {G:Finset (Finset α)}
 (hc:iUC G) (h2:4≤ (ly G 2).card):
 1≤ (ly G 4).card:=by
 obtain ⟨A,hA⟩:=qr.mp (by omega:0 < (ly G 2).card);obtain ⟨hAG,hAc⟩:=mLy.mp hA;let R:=(ly G 2).erase A
 have hRcard:3≤ R.card:=by
  have:=card_erase_add_one hA;dsimp[R];omega
 by_cases h4:∃ B∈R,(A∪B).card=4
 · obtain ⟨B,hBR,hABc⟩:=h4;have v7:B∈G:=(mLy.mp (qMe hBR)).1;exact qr.mpr ⟨A∪B,mLy.mpr ⟨hc A hAG B v7,hABc⟩⟩
 · simp only[not_exists,not_and] at h4
   have h3:∀ B∈R,(A∪B).card=3:=by
    intro B hBR;obtain ⟨v7,hBc⟩:=mLy.mp (qMe hBR);have v3:B≠A:=ne_of_mem_erase hBR;have v1:A ⊂ A∪B:=Finset.ssubset_iff_subset_ne.mpr ⟨qU,fun heq=>by
     have v9:B⊆A:=qUr.trans_eq heq.symm;exact v3 (qS v9 (by omega))⟩
    have v8:=card_lt_card v1;have hle:=card_union_le A B;have hneq:=h4 B hBR;omega
   obtain ⟨B₁,hB₁⟩:=qr.mp (by omega:0 < R.card);let T₁:=A∪B₁;have hT₁c:T₁.card=3:=h3 B₁ hB₁
   have v0:¬ ∀ B∈R,A∪B=T₁:=by
    intro hall
    have v2:R⊆(T₁.powersetCard 2).erase A:=by
     intro B hB;have hBT₁:B⊆T₁:=qUr.trans_eq (hall B hB);exact mem_erase.mpr ⟨ne_of_mem_erase hB,
      qP.mpr ⟨hBT₁,(mLy.mp (qMe hB)).2⟩⟩
    have hAT₁:A∈T₁.powersetCard 2:=qP.mpr ⟨qU,hAc⟩
    have hPcard:((T₁.powersetCard 2).erase A).card=2:=by
     rw[card_erase_of_mem hAT₁,qCp,hT₁c];decide
    have:=qL v2;omega
   simp only[not_forall] at v0;obtain ⟨B₂,hB₂,hneT⟩:=v0;let T₂:=A∪B₂;have hT₂c:T₂.card=3:=h3 B₂ hB₂;have hT₁G:T₁∈G:=hc A hAG B₁ (mLy.mp (qMe hB₁)).1;have hT₂G:T₂∈G:=hc A hAG B₂ (mLy.mp (qMe hB₂)).1;have v1:T₁ ⊂ T₁∪T₂:=Finset.ssubset_iff_subset_ne.mpr ⟨qU,fun heq=>by
    have v6:T₂⊆T₁:=qUr.trans_eq heq.symm;exact hneT (qS v6 (by rw[hT₁c,hT₂c]))⟩
   have v8:=card_lt_card v1
   have hinter:2≤ (T₁∩T₂).card:=by
    have v5:A⊆T₁∩T₂:=subset_inter qU qU;exact hAc ▸ qL v5
   have hsum:=qCa T₁ T₂
   have v4:(T₁∪T₂).card=4:=by omega
   exact qr.mpr ⟨T₁∪T₂,mLy.mpr ⟨hc T₁ hT₁G T₂ hT₂G,v4⟩⟩
lemma Z0 {α:Type*} [DecidableEq α] {M:Finset α}
 {G:Finset (Finset α)} (hGM:G⊆M.powerset) (hc:iUC G)
 (h1:(ly G 1).card=4) (h2:7≤ (ly G 2).card):
 2≤ (ly G 4).card:=by
 let U1:=M.filter (fun x=>{x}∈G);have v3:U1.card=4:=(Xo hGM).trans h1;have v10:U1∈G:=ZA hc (qr.mp (by omega)) Subset.rfl;have v9:U1∈ly G 4:=mLy.mpr ⟨v10,v3⟩
 have v1:¬ ly G 2⊆U1.powersetCard 2:=by
  intro hsub;have hle:=qL hsub;rw[qCp,v3] at hle
  have:Nat.choose 4 2=6:=by decide
  omega
 obtain ⟨B,hBL,hBnP⟩:=not_subset.mp v1;obtain ⟨hBG,hBc⟩:=mLy.mp hBL;have v0:¬ B⊆U1:=fun hsub=>hBnP (qP.mpr ⟨hsub,hBc⟩)
 have v4:2≤ (U1 \ B).card:=by
  have hpart:=card_sdiff_add_card_inter U1 B;have hinter:(U1∩B).card≤ 2:=hBc ▸ qL inter_subset_right;omega
 obtain ⟨C,hCU1B,hCc⟩:=exists_subset_card_eq v4;have hCG:C∈G:=ZA hc (qr.mp (by omega)) (hCU1B.trans sdiff_subset);have v6:Disjoint B C:=disjoint_of_subset_right hCU1B disjoint_sdiff_self_right
 have v7:(B∪C).card=4:=by rw[qCu v6,hBc,hCc]
 have v8:B∪C∈ly G 4:=mLy.mpr ⟨hc B hBG C hCG,v7⟩;have hne:B∪C≠U1:=fun heq=>v0 (qU.trans_eq heq)
 have v5:({U1,B∪C}:Finset (Finset α))⊆ly G 4:=by
  intro X hX;rcases qo.mp hX with rfl|hX2
  · exact v9
  · rw[qb.mp hX2];exact v8
 have v2:({U1,B∪C}:Finset (Finset α)).card=2:=card_pair hne.symm;exact v2 ▸ qL v5
lemma VH {n1 n2:ℕ} (h1:n1≤ 5) (hs2:n1.choose 2≤ n2):
 n1≤ 1∨(n1=2∧1≤ n2)∨(n1=3∧3≤ n2)∨(n1=4∧6≤ n2)∨(n1=5∧10≤ n2):=by
 interval_cases n1<;>simp only[Nat.choose] at hs2<;>omega
lemma VI {n1 n2 n3 n4:ℕ} (h1:n1≤ 6)
 (hs2:n1.choose 2≤ n2) (hs3:n1.choose 3≤ n3) (hs4:n1.choose 4≤ n4):
 n1≤ 1∨(n1=2∧1≤ n2)∨(n1=3∧3≤ n2∧1≤ n3)∨
  (n1=4∧6≤ n2∧4≤ n3∧1≤ n4)∨
  (n1=5∧10≤ n2∧10≤ n3∧5≤ n4)∨
  (n1=6∧15≤ n2∧20≤ n3∧15≤ n4):=by
 interval_cases n1<;>simp only[Nat.choose] at hs2 hs3 hs4<;>omega
abbrev s2 (n0 n1 n2 n3 n4 n5 k:ℕ):ℤ:=
 (((((n0:ℤ)*(2*((k:ℤ)+2*0)-17)+(n1:ℤ)*(2*((k:ℤ)+2*1)-17))+(n2:ℤ)*(2*((k:ℤ)+2*2)-17))+
  (n3:ℤ)*(2*((k:ℤ)+2*3)-17))+(n4:ℤ)*(2*((k:ℤ)+2*4)-17))+(n5:ℤ)*(2*((k:ℤ)+2*5)-17)
lemma zIa (n0 n1 n2 n3 n4 n5 k:ℕ)
 (hk1:1≤ k) (hk6:k≤ 6) (hn5:1≤ n5) (ub0:n0≤ 1) (v1:n1≤ 5) (ub2:n2≤ 10)
 (ub3:n3≤ 10) (ub4:n4≤ 5) (ub5:n5≤ 1) (hl23:2*(10-n3)≤ 3*(10-n2))
 (hl34:3*(5-n4)≤ 2*(10-n3)) (hl24:3*(5-n4)≤ 3*(10-n2))
 (he1:4≤ n2->1≤ n4) (h123:1≤ n1->n2≤ n3+4) (v3:n1.choose 2≤ n2)
 (hz0:k < 5->n0=0) (hz1:k < 4->n1=0) (hz2:k < 3->n2=0) (hz3:k < 2->n3=0) (hk4:k=4->n1≤ 1):
 (0:ℤ)≤ s2 n0 n1 n2 n3 n4 n5 k:=by
 dsimp only[s2]
 interval_cases k <;> (try have:=hz0 (by omega)) <;> (try have:=hz1 (by omega)) <;> (try have:=hz2 (by omega)) <;> (try have:=hz3 (by omega)) <;> (try have:=hk4 rfl) <;>
  (try (have hcc:=VH v1 v3;rcases hcc with h|⟨rfl,h⟩|⟨rfl,h⟩|⟨rfl,h⟩|⟨rfl,h⟩)) <;> omega
abbrev s3 (n0 n1 n2 n3 n4 n5 n6 k:ℕ):ℤ:=
 ((((((n0:ℤ)*(2*((k:ℤ)+3*0)-24)+(n1:ℤ)*(2*((k:ℤ)+3*1)-24))+(n2:ℤ)*(2*((k:ℤ)+3*2)-24))+
  (n3:ℤ)*(2*((k:ℤ)+3*3)-24))+(n4:ℤ)*(2*((k:ℤ)+3*4)-24))+(n5:ℤ)*(2*((k:ℤ)+3*5)-24))+(n6:ℤ)*(2*((k:ℤ)+3*6)-24)
lemma j1 (n0 n1 n2 n3 n4 n5 n6 k:ℕ)
 (hk1:1≤ k) (hk6:k≤ 6) (hn6:1≤ n6) (hn5:2≤ n5)
 (ub0:n0≤ 1) (ub1:n1≤ 6) (ub2:n2≤ 15) (ub3:n3≤ 20) (ub4:n4≤ 15)
 (hl23:2*(20-n3)≤ 4*(15-n2)) (hl34:3*(15-n4)≤ 3*(20-n3)) (hl24:3*(15-n4)≤ 6*(15-n2))
 (he1:4≤ n2->1≤ n4) (he2:n1=4->7≤ n2->2≤ n4)
 (hs2:n1.choose 2≤ n2) (hs3:n1.choose 3≤ n3) (hs4:n1.choose 4≤ n4)
 (hz0:k < 5->n0=0) (hz1:k < 4->n1=0) (hz2:k < 3->n2=0) (hz3:k < 2->n3=0):
 (0:ℤ)≤ s3 n0 n1 n2 n3 n4 n5 n6 k:=by
 dsimp only[s3];have hcc:=VI ub1 hs2 hs3 hs4
 rcases hcc with h|⟨rfl,h⟩|⟨rfl,h1,h2⟩|⟨rfl,h1,h2,h3⟩|⟨rfl,h1,h2,h3⟩|⟨rfl,h1,h2,h3⟩ <;>
  (interval_cases k <;> (try have:=hz0 (by omega)) <;> (try have:=hz1 (by omega)) <;> (try have:=hz2 (by omega)) <;> (try have:=hz3 (by omega)) <;> omega)
lemma j2 (n0 n1 n2 n3 n4 n5 n6 k:ℕ)
 (hk1:1≤ k) (hk6:k≤ 6) (hn6:1≤ n6) (hn5:1≤ n5)
 (b0:n0=0) (b1:n1≤ 1) (b2:n2≤ 5) (b3:n3≤ 10)
 (hz1:k < 4->n1=0) (hz2:k < 3->n2=0) (hz3:k < 2->n3=0):
 (0:ℤ)≤ s3 n0 n1 n2 n3 n4 n5 n6 k:=by
 dsimp only[s3];interval_cases k <;> (try have:=hz1 (by omega)) <;> (try have:=hz2 (by omega)) <;> (try have:=hz3 (by omega)) <;> omega
lemma j3 (n0 n1 n2 n3 n4 n5 n6 k:ℕ)
 (hk1:1≤ k) (hk6:k≤ 6) (hn6:1≤ n6) (b0:n0=0) (b1:n1=0) (b2:n2≤ 1) (b3:n3≤ 4)
 (hz2:k < 3->n2=0) (hz3:k < 2->n3=0):
 (0:ℤ)≤ s3 n0 n1 n2 n3 n4 n5 n6 k:=by
 dsimp only[s3];interval_cases k <;> (try have:=hz2 (by omega)) <;> (try have:=hz3 (by omega)) <;> omega
lemma Z3i {M:SF} (hM:M.card=5)
 {G:SS} (hGM:G⊆M.powerset) (hc:iUC G)
 (hS:G.Nonempty->M∈G) (k:ℕ) (hk1:1≤ k) (hk6:k≤ 6)
 (hlow:∀ A∈G,5≤ k+A.card)
 (hk4:k=4->(ly G 1).card≤ 1):
 (0:ℤ)≤ ∑ A∈G,(2*((k:ℤ)+2*(A.card:ℤ))-17):=by
 by_cases hne:G.Nonempty
 · have v2:M∈G:=hS hne;have hn5:1≤ (ly G 5).card:=qr.mpr ⟨M,mLy.mpr ⟨v2,hM⟩⟩
   have ub0:(ly G 0).card≤ 1:=by have h:=Z3h hGM 0;simp only[hM,Nat.choose] at h;omega
   have v1:(ly G 1).card≤ 5:=by have h:=Z3h hGM 1;simp only[hM,Nat.choose] at h;omega
   have ub2:(ly G 2).card≤ 10:=by have h:=Z3h hGM 2;simp only[hM,Nat.choose] at h;omega
   have ub3:(ly G 3).card≤ 10:=by have h:=Z3h hGM 3;simp only[hM,Nat.choose] at h;omega
   have ub4:(ly G 4).card≤ 5:=by have h:=Z3h hGM 4;simp only[hM,Nat.choose] at h;omega
   have ub5:(ly G 5).card≤ 1:=by have h:=Z3h hGM 5;simp only[hM,Nat.choose] at h;omega
   have v0:∀ r < 5-k,(ly G r).card=0:=by
    intro r hr;rw[qa,qEm];intro A hA;obtain ⟨hAG,hAr⟩:=mLy.mp hA;have:=hlow A hAG;omega
   have hl23:2*(10-(ly G 3).card)≤ 3*(10-(ly G 2).card):=by
    have h:=ZV hGM hc 3 (by omega);simp only[hM,Nat.choose] at h;omega
   have hl34:3*(5-(ly G 4).card)≤ 2*(10-(ly G 3).card):=by
    have h:=ZV hGM hc 4 (by omega);simp only[hM,Nat.choose] at h;omega
   have hl24:3*(5-(ly G 4).card)≤ 3*(10-(ly G 2).card):=by
    have h:=ZW hGM hc;simp only[hM,Nat.choose] at h;omega
   have he1:4≤ (ly G 2).card->1≤ (ly G 4).card:=ZX hc
   have h123:1≤ (ly G 1).card->(ly G 2).card≤ (ly G 3).card+4:=by
    intro h1;simpa[hM] using Zi hGM hc h1
   have v3:=Xp hGM hc 2 (by omega);rw[Z3J hGM (fun r=>2*((k:ℤ)+2*(r:ℤ))-17),hM];simp only[qSg,sum_range_zero,zero_add];simpa only [s2,q0,q1,q2] using zIa (ly G 0).card (ly G 1).card (ly G 2).card (ly G 3).card (ly G 4).card (ly G 5).card k hk1 hk6 hn5 ub0 v1 ub2 ub3 ub4 ub5 hl23 hl34 hl24 he1 h123 v3 (fun hk=>v0 0 (by omega)) (fun hk=>v0 1 (by omega)) (fun hk=>v0 2 (by omega)) (fun hk=>v0 3 (by omega)) hk4
 · rw[not_nonempty_iff_eq_empty.mp hne];simp
def cL (G:SS) (i:ℕ):ℕ:=(ly G i).card
lemma Z3j {M S T:SF} (hM:M.card=6)
 (hSU:S∪T=M) (hSc:S.card=5) (hTc:T.card=5) (hST:S≠T)
 {G:SS} (hGM:G⊆M.powerset) (hc:iUC G)
 (hopS:∀ A∈G,A∪S∈G) (hopT:∀ A∈G,A∪T∈G)
 (k:ℕ) (hk6:k≤ 6)
 (hk0:k=0->∅∈G∧S∈G∧T∈G∧M∈G)
 (hlow:∀ A∈G,(k=0∧A=∅)∨5≤ k+A.card):
 (0:ℤ)≤ ∑ A∈G,(2*((k:ℤ)+3*(A.card:ℤ))-24):=by
 have hSM:S⊆M:=hSU ▸ qU;have hTM:T⊆M:=hSU ▸ qUr;by_cases hkzero:k=0
 · subst hkzero;obtain ⟨heG,hSG,hTG,hMG⟩:=hk0 rfl
   have hn5:2≤ (ly G 5).card:=by
    have v9:({S,T}:SS)⊆ly G 5:=by
     intro X hX;rcases qo.mp hX with rfl|hX2
     · exact mLy.mpr ⟨hSG,hSc⟩
     · rw[qb.mp hX2];exact mLy.mpr ⟨hTG,hTc⟩
    exact (card_pair hST)▸ qL v9
   have hn6:1≤ (ly G 6).card:=qr.mpr ⟨M,mLy.mpr ⟨hMG,hM⟩⟩
   have ub0:(ly G 0).card≤ 1:=by simpa[hM] using Z3h hGM 0
   have z1:(ly G 1).card=0:=by
    rw[qa,qEm];intro A hA;obtain ⟨hAG,hAc⟩:=mLy.mp hA;rcases hlow A hAG with ⟨_,rfl⟩|hge
    · simp at hAc
    · omega
   have z2:(ly G 2).card=0:=by
    rw[qa,qEm];intro A hA;obtain ⟨hAG,hAc⟩:=mLy.mp hA;rcases hlow A hAG with ⟨_,rfl⟩|hge
    · simp at hAc
    · omega
   have z3:(ly G 3).card=0:=by
    rw[qa,qEm];intro A hA;obtain ⟨hAG,hAc⟩:=mLy.mp hA;rcases hlow A hAG with ⟨_,rfl⟩|hge
    · simp at hAc
    · omega
   have z4:(ly G 4).card=0:=by
    rw[qa,qEm];intro A hA;obtain ⟨hAG,hAc⟩:=mLy.mp hA;rcases hlow A hAG with ⟨_,rfl⟩|hge
    · simp at hAc
    · omega
   rw[Z3J hGM (fun r=>2*(((0:ℕ):ℤ)+3*(r:ℤ))-24),hM];simp only[qSg,sum_range_zero,zero_add];omega
 have hk1:1≤ k:=by omega
 by_cases hne:G.Nonempty
 · obtain ⟨A₀,hA₀⟩:=hne
   have hMG:M∈G:=by
    have h1:=hopT (A₀∪S) (hopS A₀ hA₀)
    have heq:(A₀∪S)∪T=M:=by rw[union_assoc,hSU,union_eq_right.mpr (q7.mp (hGM hA₀))]
    exact heq ▸ h1
   have hn6:1≤ (ly G 6).card:=qr.mpr ⟨M,mLy.mpr ⟨hMG,hM⟩⟩
   have v0:∀ r < 5-k,(ly G r).card=0:=by
    intro r hr;rw[qa,qEm];intro A hA;obtain ⟨hAG,hAr⟩:=mLy.mp hA;rcases hlow A hAG with ⟨hkz,_⟩|hge
    · exact (hkzero hkz).elim
    · omega
   have v8:(M \ S).card=1:=by rw[qe hSM,hM,hSc]
   have v7:(M \ T).card=1:=by rw[qe hTM,hM,hTc]
   obtain ⟨b,hb⟩:=qC1.mp v8;obtain ⟨a,ha⟩:=qC1.mp v7;have hbM:{b}⊆M:=hb ▸ sdiff_subset;have haM:{a}⊆M:=ha ▸ sdiff_subset
   have v2:a≠b:=by
    intro heq;apply hST
    calc S=M \ (M \ S):=(Finset.sdiff_sdiff_eq_self hSM).symm
     _=M \ (M \ T):=by rw[hb,ha,heq]
     _=T:=Finset.sdiff_sdiff_eq_self hTM
   have v6:S∉G->∀ A∈G,{b}⊆A:=by
    intro hSnG A hAG;rw[qf];by_contra hbnA
    have hAS:A⊆S:=by
     intro x hxA;have v3:x∈M:=q7.mp (hGM hAG) hxA;by_contra hxnS;have v17:x∈M \ S:=qSd.mpr ⟨v3,hxnS⟩;rw[hb,qb] at v17;exact hbnA (v17 ▸ hxA)
    have:A∪S=S:=union_eq_right.mpr hAS;exact hSnG (this ▸ hopS A hAG)
   have v5:T∉G->∀ A∈G,{a}⊆A:=by
    intro hTnG A hAG;rw[qf];by_contra hanA
    have hAT:A⊆T:=by
     intro x hxA;have v3:x∈M:=q7.mp (hGM hAG) hxA;by_contra hxnT;have v13:x∈M \ T:=qSd.mpr ⟨v3,hxnT⟩;rw[ha,qb] at v13;exact hanA (v13 ▸ hxA)
    have:A∪T=T:=union_eq_right.mpr hAT;exact hTnG (this ▸ hopT A hAG)
   rw[Z3J hGM (fun r=>2*((k:ℤ)+3*(r:ℤ))-24),hM];simp only[qSg,sum_range_zero,zero_add];let c0:=cL G 0;let c1:=cL G 1;let c2:=cL G 2;let c3:=cL G 3;let c4:=cL G 4;let c5:=cL G 5;let c6:=cL G 6;by_cases hSG:S∈G
   · by_cases hTG:T∈G
     ·
      have hn5:2≤ (ly G 5).card:=by
       have v9:({S,T}:SS)⊆ly G 5:=by
        intro X hX;rcases qo.mp hX with rfl|hX2
        · exact mLy.mpr ⟨hSG,hSc⟩
        · rw[qb.mp hX2];exact mLy.mpr ⟨hTG,hTc⟩
       exact (card_pair hST)▸ qL v9
      have ub0:(ly G 0).card≤ 1:=by have h:=Z3h hGM 0;simp only[hM,Nat.choose] at h;omega
      have ub1:(ly G 1).card≤ 6:=by have h:=Z3h hGM 1;simp only[hM,Nat.choose] at h;omega
      have ub2:(ly G 2).card≤ 15:=by have h:=Z3h hGM 2;simp only[hM,Nat.choose] at h;omega
      have ub3:(ly G 3).card≤ 20:=by have h:=Z3h hGM 3;simp only[hM,Nat.choose] at h;omega
      have ub4:(ly G 4).card≤ 15:=by have h:=Z3h hGM 4;simp only[hM,Nat.choose] at h;omega
      have hl23:2*(20-(ly G 3).card)≤ 4*(15-(ly G 2).card):=by
       have h:=ZV hGM hc 3 (by omega);simp only[hM,Nat.choose] at h;omega
      have hl34:3*(15-(ly G 4).card)≤ 3*(20-(ly G 3).card):=by
       have h:=ZV hGM hc 4 (by omega);simp only[hM,Nat.choose] at h;omega
      have hl24:3*(15-(ly G 4).card)≤ 6*(15-(ly G 2).card):=by
       have h:=ZW hGM hc;simp only[hM,Nat.choose] at h;omega
      have he1:4≤ (ly G 2).card->1≤ (ly G 4).card:=ZX hc;have he2:(ly G 1).card=4->7≤ (ly G 2).card->2≤ (ly G 4).card:=
       Z0 hGM hc
      have hs2:=Xp hGM hc 2 (by omega);have hs3:=Xp hGM hc 3 (by omega);have hs4:=Xp hGM hc 4 (by omega);simpa only [c0,c1,c2,c3,c4,c5,c6,cL,s3,q0,q1,q2] using j1 c0 c1 c2 c3 c4 c5 c6 k hk1 hk6 hn6 hn5 ub0 ub1 ub2 ub3 ub4 hl23 hl34 hl24 he1 he2 hs2 hs3 hs4 (fun hk=>v0 0 (by omega)) (fun hk=>v0 1 (by omega)) (fun hk=>v0 2 (by omega)) (fun hk=>v0 3 (by omega))
     ·
      have v1:∀ A∈G,{a}⊆A:=v5 hTG;have hn5:1≤ (ly G 5).card:=qr.mpr ⟨S,mLy.mpr ⟨hSG,hSc⟩⟩
      have b0:(ly G 0).card=0:=by
       rw[qa,qEm];intro A hA;have:=v1 A (mLy.mp hA).1;have hcA:=(mLy.mp hA).2;have:=qL this;simp[hcA] at this
      have b1:(ly G 1).card≤ 1:=by simpa[hM] using ZE hGM haM (qw a) 1 v1
      have b2:(ly G 2).card≤ 5:=by simpa[hM] using ZE hGM haM (qw a) 2 v1
      have b3:(ly G 3).card≤ 10:=by
       have h:=ZE hGM haM (qw a) 3 v1;simp only[hM,Nat.choose] at h;omega
      simpa only [c0,c1,c2,c3,c4,c5,c6,cL,s3,q0,q1,q2] using j2 c0 c1 c2 c3 c4 c5 c6 k hk1 hk6 hn6 hn5 b0 b1 b2 b3 (fun hk=>v0 1 (by omega)) (fun hk=>v0 2 (by omega)) (fun hk=>v0 3 (by omega))
   · by_cases hTG:T∈G
     ·
      have v1:∀ A∈G,{b}⊆A:=v6 hSG;have hn5:1≤ (ly G 5).card:=qr.mpr ⟨T,mLy.mpr ⟨hTG,hTc⟩⟩
      have b0:(ly G 0).card=0:=by
       rw[qa,qEm];intro A hA;have:=v1 A (mLy.mp hA).1;have hcA:=(mLy.mp hA).2;have:=qL this;simp[hcA] at this
      have b1:(ly G 1).card≤ 1:=by simpa[hM] using ZE hGM hbM (qw b) 1 v1
      have b2:(ly G 2).card≤ 5:=by simpa[hM] using ZE hGM hbM (qw b) 2 v1
      have b3:(ly G 3).card≤ 10:=by
       have h:=ZE hGM hbM (qw b) 3 v1;simp only[hM,Nat.choose] at h;omega
      simpa only [c0,c1,c2,c3,c4,c5,c6,cL,s3,q0,q1,q2] using j2 c0 c1 c2 c3 c4 c5 c6 k hk1 hk6 hn6 hn5 b0 b1 b2 b3 (fun hk=>v0 1 (by omega)) (fun hk=>v0 2 (by omega)) (fun hk=>v0 3 (by omega))
     ·
      have v1:∀ A∈G,({a,b}:SF)⊆A:=by
       intro A hAG x hx;rcases qo.mp hx with rfl|hxb
       · exact qf.mp (v5 hTG A hAG)
       · rw[qb.mp hxb];exact qf.mp (v6 hSG A hAG)
      have v19:({a,b}:SF)⊆M:=by
       intro x hx;rcases qo.mp hx with rfl|hxb
       · exact qf.mp haM
       · rw[qb.mp hxb];exact qf.mp hbM
      have v4:({a,b}:SF).card=2:=card_pair v2
      have b0:(ly G 0).card=0:=by
       rw[qa,qEm];intro A hA;have hle:=qL (v1 A (mLy.mp hA).1);rw[v4,(mLy.mp hA).2] at hle;omega
      have b1:(ly G 1).card=0:=by
       rw[qa,qEm];intro A hA;have hle:=qL (v1 A (mLy.mp hA).1);rw[v4,(mLy.mp hA).2] at hle;omega
      have b2:(ly G 2).card≤ 1:=by simpa[hM] using ZE hGM v19 v4 2 v1
      have b3:(ly G 3).card≤ 4:=by simpa[hM] using ZE hGM v19 v4 3 v1
      simpa only [c0,c1,c2,c3,c4,c5,c6,cL,s3,q0,q1,q2] using j3 c0 c1 c2 c3 c4 c5 c6 k hk1 hk6 hn6 b0 b1 b2 b3 (fun hk=>v0 2 (by omega)) (fun hk=>v0 3 (by omega))
 · rw[not_nonempty_iff_eq_empty.mp hne];simp
def pF (F:SS) (M K:SF):
 SS:=
 (F.filter (fun X=>X \ M=K)).image (fun X=>X∩M)
lemma pFS (F:SS) (M K:SF):
 pF F M K⊆M.powerset:=by
 intro A hA;obtain ⟨X,_,rfl⟩:=qI.mp hA;exact q7.mpr inter_subset_right
lemma YG {F:SS} (hc:iUC F)
 (M K:SF):iUC (pF F M K):=by
 intro A hA B hB;obtain ⟨X,hXf,rfl⟩:=qI.mp hA;obtain ⟨Y,hYf,rfl⟩:=qI.mp hB;obtain ⟨hXF,hXK⟩:=qF.mp hXf;obtain ⟨hYF,hYK⟩:=qF.mp hYf;refine qI.mpr ⟨X∪Y,qF.mpr ⟨hc X hXF Y hYF,?_⟩,?_⟩
 · rw[union_sdiff_distrib,hXK,hYK,union_idempotent]
 · exact qq X Y M
lemma projFiber_op {F:SS} (hc:iUC F)
 {M V:SF} (hVF:V∈F) (hVM:V⊆M) (K:SF):
 ∀ A∈pF F M K,A∪V∈pF F M K:=by
 intro A hA;obtain ⟨X,hXf,rfl⟩:=qI.mp hA;obtain ⟨hXF,hXK⟩:=qF.mp hXf;refine qI.mpr ⟨X∪V,qF.mpr ⟨hc X hXF V hVF,?_⟩,?_⟩
 · rw[union_sdiff_distrib,hXK,qi.mpr hVM,union_empty]
 · rw[qq,inter_eq_left.mpr hVM]
lemma mPF {F:SS} {M X:SF}
 (hXF:X∈F):X∩M∈pF F M (X \ M):=
 qI.mpr ⟨X,qF.mpr ⟨hXF,rfl⟩,rfl⟩
lemma Z1H (M:SF) (a:ℕ):
 (∑ i:Fin 12,if i∈M then a else 1)=a*M.card+(12-M.card):=by
 have hpart:=ZU (univ:SF) (·∈M)
 have hm:(univ.filter (·∈M)).card=M.card:=by
  have:univ.filter (·∈M)=M:=by ext i;simp
  rw[this]
 have v0:(univ.filter (·∉M)).card=12-M.card:=by
  have hcard12:(univ:SF).card=12:=by simp
  omega
 calc (∑ i:Fin 12,if i∈M then a else 1)
  = (∑ i∈univ.filter (·∈M),a)+∑ i∈univ.filter (·∉M),1:=by rw[← sum_ite]
  _=(univ.filter (·∈M)).card*a+(univ.filter (·∉M)).card*1:=by simp[sum_const]
  _=a*M.card+(12-M.card):=by rw[hm,v0,qY,Nat.mul_one]
lemma Z3K (M X:SF) (a:ℕ):
 (∑ i∈X,if i∈M then a else 1)=(X \ M).card+a*(X∩M).card:=by
 have v0:X=(X \ M)∪(X∩M):=(qSu X M).symm;have v1:Disjoint (X \ M) (X∩M):=disjoint_sdiff_inter X M
 conv_lhs=>rw[v0]
 rw[sum_union v1]
 have v2:(∑ i∈X \ M,if i∈M then a else 1)=(X \ M).card:=by
  have:(∑ i∈X \ M,if i∈M then a else 1)=∑ _i∈X \ M,1:=
   qh rfl (fun i hi=>if_neg (qSd.mp hi).2)
  simp[this]
 have v3:(∑ i∈X∩M,if i∈M then a else 1)=a*(X∩M).card:=by
  have:(∑ i∈X∩M,if i∈M then a else 1)=∑ _i∈X∩M,a:=
   qh rfl (fun i hi=>if_pos (mem_inter.mp hi).2)
  simp[this,qY]
 rw[v2,v3]
lemma YH (F:SS) (M:SF) (a W:ℕ):
 (∑ X∈F,(2*(((X \ M).card+a*(X∩M).card:ℕ):ℤ)-(W:ℤ)))=
  ∑ K∈Mᶜ.powerset,∑ A∈pF F M K,
   (2*((K.card:ℤ)+(a:ℤ)*(A.card:ℤ))-(W:ℤ)):=by
 have v1:∀ X∈F,X \ M∈Mᶜ.powerset:=by
  intro X _;rw[q7];intro i hi;exact mem_compl.mpr (qSd.mp hi).2
 rw[← qj v1];apply qh rfl;intro K _;have v0:Set.InjOn (fun X:SF=>X∩M)
  (F.filter (fun X=>X \ M=K):Set (SF)):=by
  intro X₁ hX₁ X₂ hX₂ heq;dsimp only at heq;have hK₁:X₁ \ M=K:=(qF.mp hX₁).2;have hK₂:X₂ \ M=K:=(qF.mp hX₂).2
  calc X₁=(X₁ \ M)∪(X₁∩M):=(qSu X₁ M).symm
   _=K∪(X₂∩M):=by rw[hK₁,heq]
   _=(X₂ \ M)∪(X₂∩M):=by rw[hK₂]
   _=X₂:=qSu X₂ M
 dsimp[pF];rw[sum_image v0];apply qh rfl;intro X hX;have v2:X \ M=K:=(qF.mp hX).2;rw[v2]
abbrev fIS:=@UP.fIS
lemma ZY {α:Type*} [DecidableEq α] (K A₁ A₂:Finset α):
 (K∪A₁)∪(K∪A₂)=K∪(A₁∪A₂):=by
 ext x;simp only[mem_union];tauto
lemma cr29 {F:SS} (closed:iUC F) (empty:∅∈F)
 (low:∀ S∈F,S.Nonempty->5≤ S.card)
 {S T:SF} (hSF:S∈F) (hTF:T∈F) (hST:S≠T)
 (hSc:S.card=5) (hTc:T.card=5) (hUc:(S∪T).card=6):
 ∃ w:WF,0 < ∑ i,w i∧
  F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i):=by
 let U:=S∪T;have v0:U.card=6:=hUc;let w:WF:=fun i=>if i∈U then 3 else 1
 have hW:(∑ i:Fin 12,w i)=24:=by
  have v5:=Z1H U 3;rw[v0] at v5;dsimp[w];omega
 refine ⟨w,by omega,fIS F w ?_⟩;have v3:(∑ X∈F,(2*((∑ i∈X,w i:ℕ):ℤ)-((∑ i,w i:ℕ):ℤ)))=
  ∑ X∈F,(2*(((X \ U).card+3*(X∩U).card:ℕ):ℤ)-((24:ℕ):ℤ)):=by
  rw[hW];exact qh rfl (fun X _=>by rw[Z3K U X 3])
 rw[v3,YH F U 3 24];apply sum_nonneg;intro K hK
 have v2:K.card≤ 6:=by
  have v7:K⊆Uᶜ:=q7.mp hK
  have v6:Uᶜ.card=6:=by rw[qu,qCf,hUc]
  exact v6 ▸ qL v7
 apply Z3j hUc rfl hSc hTc hST (pFS F U K)
  (YG closed U K)
  (projFiber_op closed hSF qU K)
  (projFiber_op closed hTF qUr K)
  K.card v2
 · intro hk0;have hKe:K=∅:=qa.mp hk0;subst hKe;have hUF:U∈F:=closed S hSF T hTF;refine ⟨?_,?_,?_,?_⟩
   · simpa using mPF empty (M:=U)
   · have hS1:S \ U=∅:=qi.mpr qU;have hS2:S∩U=S:=inter_eq_left.mpr qU;simpa[hS1,hS2] using mPF hSF (M:=U)
   · have hT1:T \ U=∅:=qi.mpr qUr;have v9:T∩U=T:=inter_eq_left.mpr qUr;simpa[hT1,v9] using mPF hTF (M:=U)
   · have v8:U \ U=∅:=sdiff_self;have hU2:U∩U=U:=inter_self U;simpa[v8,hU2] using mPF hUF (M:=U)
 · intro A hA
   obtain ⟨X,hXf,rfl⟩:=qI.mp hA;obtain ⟨hXF,hXK⟩:=qF.mp hXf;by_cases hXe:X=∅
   · subst hXe;left;simp[← hXK]
   · right
     have hcardX:X.card=K.card+(X∩U).card:=by
      have v1:=(qSu X U).symm;have v4:=disjoint_sdiff_inter X U
      calc X.card=((X \ U)∪(X∩U)).card:=congrArg card v1
       _=(X \ U).card+(X∩U).card:=qCu v4
       _=K.card+(X∩U).card:=by rw[hXK]
     have:=low X hXF (qNe.mpr hXe);omega
lemma cr33 {F:SS} (closed:iUC F) (empty:∅∈F)
 (full:univ∈F) (low:∀ S∈F,S.Nonempty->5≤ S.card)
 (hpair6:¬∃ S∈F,∃ T∈F,S≠T∧S.card=5∧T.card=5∧(S∪T).card=6)
 {S₀:SF} (hS₀F:S₀∈F) (hS₀c:S₀.card=5):
 ∃ w:WF,0 < ∑ i,w i∧
  F.card*(∑ i,w i)≤ 2*(∑ S∈F,∑ i∈S,w i):=by
 let S:=S₀;have hSF:S∈F:=hS₀F;have v0:S.card=5:=hS₀c;let w:WF:=fun i=>if i∈S then 2 else 1
 have hW:(∑ i:Fin 12,w i)=17:=by
  have v25:=Z1H S 2;rw[v0] at v25;dsimp[w];omega
 refine ⟨w,by omega,fIS F w ?_⟩;have v8:(∑ X∈F,(2*((∑ i∈X,w i:ℕ):ℤ)-((∑ i,w i:ℕ):ℤ)))=
  ∑ X∈F,(2*(((X \ S).card+2*(X∩S).card:ℕ):ℤ)-((17:ℕ):ℤ)):=by
  rw[hW];exact qh rfl (fun X _=>by rw[Z3K S X 2])
 rw[v8,YH F S 2 17]
 have v3:Sᶜ.card=7:=by rw[qu,qCf,v0]
 have heP:(∅:SF)∈Sᶜ.powerset:=empty_mem_powerset _;have v15:Sᶜ∈Sᶜ.powerset:=mem_powerset_self _
 have hne_etop:(∅:SF)≠Sᶜ:=by
  intro heq;have:=congrArg card heq;simp[v3] at this
 let v2:=(Sᶜ.powerset.erase ∅).erase Sᶜ
 have v6:Sᶜ.powerset=insert ∅ (insert Sᶜ v2):=by
  dsimp[v2];rw[insert_erase (mem_erase.mpr ⟨hne_etop.symm,v15⟩),insert_erase heP]
 have hn0:(∅:SF)∉insert Sᶜ v2:=by simp[v2,hne_etop]
 have v12:Sᶜ∉v2:=notMem_erase _ _;rw[v6,sum_insert hn0,sum_insert v12];have hbot:(-14:ℤ)≤ ∑ A∈pF F S ∅,
  (2*(((∅:SF).card:ℤ)+(2:ℤ)*(A.card:ℤ))-17):=by
  have heG:∅∈pF F S ∅:=by simpa using mPF empty (M:=S)
  have v9:S∈pF F S ∅:=by
   have h1:S \ S=∅:=sdiff_self;have h2:S∩S=S:=inter_self S;simpa[h1,h2] using mPF hSF (M:=S)
  have v29:pF F S ∅={∅,S}:=by
   ext A;constructor
   · intro hA
     obtain ⟨X,hXf,rfl⟩:=qI.mp hA;obtain ⟨hXF,hXK⟩:=qF.mp hXf;by_cases v5:X=∅
     · subst v5;simp
     · have hXS:X⊆S:=qi.mp hXK;have hge:=low X hXF (qNe.mpr v5);have hle:=qL hXS;have v24:X=S:=qS hXS (by omega)
       have hIS:X∩S=S:=by rw[v24,inter_self]
       simp[hIS]
   · intro hA
     rcases qo.mp hA with rfl|hA2
     · exact heG
     · rw[qb.mp hA2];exact v9
  have v16:(∅:SF)≠S:=by
   intro heq;have:=congrArg card heq;simp[v0] at this
  rw[v29,sum_pair v16];simp only[card_empty,v0];omega
 have htop:(14:ℤ)≤ ∑ A∈pF F S Sᶜ,
  (2*((Sᶜ.card:ℤ)+(2:ℤ)*(A.card:ℤ))-17):=by
  have v9:S∈pF F S Sᶜ:=by
   have h1:(univ:SF)\ S=Sᶜ:=by ext i;simp
   have h2:(univ:SF)∩S=S:=univ_inter S;simpa[h1,h2] using mPF full (M:=S)
  have hGM:=pFS F S Sᶜ;rw[Z3J hGM (fun r=>2*((Sᶜ.card:ℤ)+(2:ℤ)*(r:ℤ))-17),v3,v0]
  have ub0:(ly (pF F S Sᶜ) 0).card≤ 1:=by
   have h:=Z3h hGM 0;simp only[v0,Nat.choose] at h;omega
  have hn5:1≤ (ly (pF F S Sᶜ) 5).card:=
   qr.mpr ⟨S,mLy.mpr ⟨v9,v0⟩⟩
  simp only[qSg,sum_range_zero,zero_add];omega
 have hmid:(0:ℤ)≤ ∑ K∈v2,∑ A∈pF F S K,
  (2*((K.card:ℤ)+(2:ℤ)*(A.card:ℤ))-17):=by
  apply sum_nonneg;intro K hK;have hK1:K≠Sᶜ:=(mem_erase.mp hK).1;have hK2:K≠∅:=(mem_erase.mp (qMe hK)).1;have v7:K⊆Sᶜ:=q7.mp (qMe (qMe hK));have v10:1≤ K.card:=qr.mpr (qNe.mpr hK2)
  have hk_lt:K.card < 7:=by
   have v18:K ⊂ Sᶜ:=Finset.ssubset_iff_subset_ne.mpr ⟨v7,hK1⟩;exact v3 ▸ card_lt_card v18
  apply Z3i v0 (pFS F S K) (YG closed S K)
   (fun ⟨A,hA⟩=>by
    have:=projFiber_op closed hSF Subset.rfl K A hA;have hAS:A⊆S:=q7.mp (pFS F S K hA)
    rwa[union_eq_right.mpr hAS] at this)
   K.card v10 (by omega)
  · intro A hA;obtain ⟨X,hXf,rfl⟩:=qI.mp hA;obtain ⟨hXF,hXK⟩:=qF.mp hXf
    have v5:X≠∅:=by
     intro heq;subst heq;simp at hXK;exact hK2 hXK.symm
    have hcardX:X.card=K.card+(X∩S).card:=by
     have v1:=(qSu X S).symm;have v14:=disjoint_sdiff_inter X S
     calc X.card=((X \ S)∪(X∩S)).card:=congrArg card v1
      _=(X \ S).card+(X∩S).card:=qCu v14
      _=K.card+(X∩S).card:=by rw[hXK]
    have:=low X hXF (qNe.mpr v5);omega
  · intro hk4;refine card_le_one.mpr ?_;intro A₁ hA₁ A₂ hA₂;by_contra hneA;obtain ⟨hA₁p,hA₁c⟩:=mLy.mp hA₁;obtain ⟨hA₂p,hA₂c⟩:=mLy.mp hA₂;obtain ⟨X₁,hX₁f,hX₁i⟩:=qI.mp hA₁p;obtain ⟨X₂,hX₂f,hX₂i⟩:=qI.mp hA₂p;obtain ⟨hX₁F,hX₁K⟩:=qF.mp hX₁f;obtain ⟨hX₂F,hX₂K⟩:=qF.mp hX₂f
    have hX₁eq:X₁=K∪A₁:=by
     calc X₁=(X₁ \ S)∪(X₁∩S):=(qSu X₁ S).symm
      _=K∪A₁:=by rw[hX₁K,hX₁i]
    have hX₂eq:X₂=K∪A₂:=by
     calc X₂=(X₂ \ S)∪(X₂∩S):=(qSu X₂ S).symm
      _=K∪A₂:=by rw[hX₂K,hX₂i]
    have hA₁S:A₁⊆S:=hX₁i ▸ inter_subset_right;have hA₂S:A₂⊆S:=hX₂i ▸ inter_subset_right;have v4:Disjoint K A₁:=
     disjoint_of_subset_left v7 (disjoint_of_subset_right hA₁S disjoint_compl_left)
    have hd2:Disjoint K A₂:=
     disjoint_of_subset_left v7 (disjoint_of_subset_right hA₂S disjoint_compl_left)
    have hX₁c:X₁.card=5:=by rw[hX₁eq,qCu v4,hk4,hA₁c]
    have hX₂c:X₂.card=5:=by rw[hX₂eq,qCu hd2,hk4,hA₂c]
    have v27:X₁≠X₂:=fun heq=>hneA (by rw[← hX₁i,← hX₂i,heq])
    have v13:(A₁∪A₂).card=2:=by
     obtain ⟨x₁,rfl⟩:=qC1.mp hA₁c;obtain ⟨x₂,rfl⟩:=qC1.mp hA₂c;have v26:x₁≠x₂:=fun h=>hneA (by rw[h]);rw[singleton_union];exact card_pair v26
    have v28:Disjoint K (A₁∪A₂):=disjoint_union_right.mpr ⟨v4,hd2⟩
    have v11:X₁∪X₂=K∪(A₁∪A₂):=by
     rw[hX₁eq,hX₂eq];exact ZY K A₁ A₂
    have v17:(X₁∪X₂).card=6:=by rw[v11,qCu v28,hk4,v13]
    exact hpair6 ⟨X₁,hX₁F,X₂,hX₂F,v27,hX₁c,hX₂c,v17⟩
 simp only[q2];linarith
end UH
theorem UH.h3_main:OMA.R_UnionClosed_union_closed_variants_univ_card_R1.H3:=by
 intro F closed empty full ⟨S₀,hS₀F,T₀,hT₀F,_,hS₀c,_⟩ low;by_cases hpair6:∃ S∈F,∃ T∈F,S≠T∧S.card=5∧T.card=5∧(S∪T).card=6
 · obtain ⟨S,hSF,T,hTF,hST,hSc,hTc,hUc⟩:=hpair6;exact UH.cr29 closed empty low hSF hTF hST hSc hTc hUc
 · exact UH.cr33 closed empty full low hpair6 hS₀F hS₀c
theorem OMA.solution : type_of% @UnionClosed.union_closed.variants.univ_card :=
  OMA.R_UnionClosed_union_closed_variants_univ_card_R1.main
    UP.h1_main UP.h2_main UH.h3_main
