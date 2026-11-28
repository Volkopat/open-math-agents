import FormalConjectures.ErdosProblems.«65»
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
noncomputable section
namespace Erdos65LM
open Classical SimpleGraph Finset
open scoped Finset
open Real (log exp sqrt rpow_add rpow_mul add_one_le_exp rpow_def_of_pos log_exp exp_log exp_nat_mul rpow_pos_of_pos exp_add log_mul exp_lt_exp sq_sqrt one_le_exp)
open Nat (floor ceil mod_lt factorial ceil_lt_add_one find find_spec find_min' add_mod_right)
open Filter (atTop)
open Fin (lastCases snoc_castSucc snoc_last lastCases_castSucc lastCases_last)
open Function (Injective update_of_ne)
open SimpleGraph.Walk (support_copy take_spec support_cons support_concat support_reverse length_cons support_append eq_of_length_eq_zero support_nil length_bypass_le_length support_takeUntil_subset_support cons_tail_support length_nil length_concat)
open List (nodup_cons getElem_append_left mem_append length_pos_of_ne_nil concat_eq_append mem_reverse getElem_mem length_dropLast dropLast_append_getLast toFinset_card_le getElem_of_mem getLast_eq_getElem nodup_append)
abbrev O:=ℝ
abbrev FS:=Finset
abbrev SG:=SimpleGraph
lemma lT {α} [Preorder α] {a b c:α} (h1:a<=b) (h2:b<=c):a<=c:=le_trans h1 h2
lemma lL2 {α} [Preorder α] {a b c:α} (h1:a<b) (h2:b<=c):a<c:=lt_of_lt_of_le h1 h2
lemma lL3 {α} [Preorder α] {a b c:α} (h1:a<=b) (h2:b<c):a<c:=lt_of_le_of_lt h1 h2
lemma lOf {α} [Preorder α] {a b:α} (h:a<b):a<=b:=le_of_lt h
lemma mS {α} [DecidableEq α] {a:α} {s t:FS α}:a∈s \ t↔a∈s/\a∉t:=Finset.mem_sdiff
lemma pS {α} [DecidableEq α] {a:α} {s t:FS α} (h:a∈s \ t):a∈s/\a∉t:=Finset.mem_sdiff.mp h
lemma rS {α} [DecidableEq α] {a:α} {s t:FS α} (h:a∈s/\a∉t):a∈s \ t:=Finset.mem_sdiff.mpr h
lemma mUl {α} [DecidableEq α] {a:α} {s:FS α} (t:FS α) (h:a∈s):a∈s∪t:=Finset.mem_union_left t h
lemma mUr {α} [DecidableEq α] {a:α} (s:FS α) {t:FS α} (h:a∈t):a∈s∪t:=Finset.mem_union_right s h
lemma dL {α} {s t:FS α}:Disjoint s t↔∀⦃a⦄,a∈s->a∉t:=Finset.disjoint_left
lemma pD {α} {s t:FS α} (h:Disjoint s t):∀⦃a⦄,a∈s->a∉t:=Finset.disjoint_left.mp h
lemma rD {α} {s t:FS α} (h:∀⦃a⦄,a∈s->a∉t):Disjoint s t:=Finset.disjoint_left.mpr h
lemma dR {α} {s t:FS α}:Disjoint s t↔∀⦃a⦄,a∈t->a∉s:=Finset.disjoint_right
lemma mU {α} [DecidableEq α] {a:α} {s t:FS α}:a∈s∪t↔a∈s\/a∈t:=Finset.mem_union
lemma pU {α} [DecidableEq α] {a:α} {s t:FS α} (h:a∈s∪t):a∈s\/a∈t:=Finset.mem_union.mp h
lemma sS {α} [DecidableEq α] {s t:FS α}:s \ t⊆s:=Finset.sdiff_subset
lemma cL {α} {s t:FS α} (h:s⊆t):s.card<=t.card:=Finset.card_le_card h
lemma mF {α} {s:FS α} {p:α->Prop} [DecidablePred p] {a:α}:a∈s.filter p↔a∈s/\p a:=Finset.mem_filter
lemma pF {α} {s:FS α} {p:α->Prop} [DecidablePred p] {a:α} (h:a∈s.filter p):a∈s/\p a:=Finset.mem_filter.mp h
lemma rF {α} {s:FS α} {p:α->Prop} [DecidablePred p] {a:α} (h:a∈s/\p a):a∈s.filter p:=Finset.mem_filter.mpr h
lemma mI {α} [DecidableEq α] {a:α} {s t:FS α}:a∈s∩t↔a∈s/\a∈t:=Finset.mem_inter
lemma pI {α} [DecidableEq α] {a:α} {s t:FS α} (h:a∈s∩t):a∈s/\a∈t:=Finset.mem_inter.mp h
lemma rI {α} [DecidableEq α] {a:α} {s t:FS α} (h:a∈s/\a∈t):a∈s∩t:=Finset.mem_inter.mpr h
lemma cUl {α} [DecidableEq α] (s t:FS α):(s∪t).card<=s.card+t.card:=Finset.card_union_le s t
lemma cBu {α β} [DecidableEq β] {s:FS α} {t:α->FS β}:(s.biUnion t).card<=∑ a∈s,(t a).card:=Finset.card_biUnion_le
lemma mB {α β} [DecidableEq β] {s:FS α} {t:α->FS β} {b:β}:b∈s.biUnion t↔∃a∈s,b∈t a:=Finset.mem_biUnion
lemma mSg {α} {a b:α}:a∈({b}:FS α)↔a=b:=Finset.mem_singleton
lemma pSg {α} {a b:α} (h:a∈({b}:FS α)):a=b:=Finset.mem_singleton.mp h
lemma nSg {α} {a b:α}:a∉({b}:FS α)↔a≠b:=Finset.notMem_singleton
lemma rG {α} {a b:α} (h:a≠b):a∉({b}:FS α):=Finset.notMem_singleton.mpr h
lemma sSm {α} {a:α} {s:FS α} (h:a∈s):({a}:FS α)⊆s:=Finset.singleton_subset_iff.mpr h
lemma sUl {α} [DecidableEq α] {s t:FS α}:s⊆s∪t:=Finset.subset_union_left
lemma sUr {α} [DecidableEq α] {s t:FS α}:t⊆s∪t:=Finset.subset_union_right
lemma uS {α} [DecidableEq α] {s1 s2 t:FS α} (h1:s1⊆t) (h2:s2⊆t):s1∪s2⊆t:=Finset.union_subset h1 h2
lemma sSs {α} [DecidableEq α] {s1 s2 t1 t2:FS α} (h1:s1⊆s2) (h2:t2⊆t1):s1 \ t1⊆s2 \ t2:=Finset.sdiff_subset_sdiff h1 h2
lemma mT {α} [DecidableEq α] {a:α} {l:List α}:a∈l.toFinset↔a∈l:=List.mem_toFinset
lemma pTf {α} [DecidableEq α] {a:α} {l:List α} (h:a∈l.toFinset):a∈l:=List.mem_toFinset.mp h
lemma rT {α} [DecidableEq α] {a:α} {l:List α} (h:a∈l):a∈l.toFinset:=List.mem_toFinset.mpr h
lemma mlL {a b c:O} (h:b<=c) (ha:0<=a):a*b<=a*c:=mul_le_mul_of_nonneg_left h ha
lemma mlR {a b c:O} (h:a<=b) (hc:0<=c):a*c<=b*c:=mul_le_mul_of_nonneg_right h hc
lemma pLl {a b:O} (ha:0<=a) (h:a<=b) (n:ℕ):a^n<=b^n:=pow_le_pow_left₀ ha h n
lemma pLr {a:O} (ha:1<=a) {m n:ℕ} (h:m<=n):a^m<=a^n:=pow_le_pow_right₀ ha h
lemma lLl {x y:O} (hx:0<x) (h:x<=y):log x<=log y:=Real.log_le_log hx h
lemma lNn {x:O} (hx:1<=x):0<=log x:=Real.log_nonneg hx
lemma lPs {x:O} (hx:1<x):0<log x:=Real.log_pos hx
lemma lIe {x y:O} (hy:0<y):x<=log y↔exp x<=y:=Real.le_log_iff_exp_le hy
lemma lIt {x y:O} (hy:0<y):x<log y↔exp x<y:=Real.lt_log_iff_exp_lt hy
lemma eGe {α} [Preorder α] (a:α):∀ᶠ x in atTop,a<=x:=Filter.eventually_ge_atTop a
lemma tL:Filter.Tendsto log atTop atTop:=Real.tendsto_log_atTop
lemma lGe (a:O):∀ᶠ x in atTop,a<=log x:=Real.tendsto_log_atTop.eventually_ge_atTop a
lemma eAt {α} [SemilatticeSup α] [Nonempty α] {p:α->Prop}:(∀ᶠ x in atTop,p x)↔∃a,∀b ≥ a,p b:=Filter.eventually_atTop
lemma nCn {α} [Semiring α] [PartialOrder α] [IsOrderedRing α] (n:ℕ):(0:α)<=(n:α):=Nat.cast_nonneg n
lemma nFl {a:O} (ha:0<=a):(floor a:O)<=a:=Nat.floor_le ha
lemma nLf {a:O} {n:ℕ} (h:(n:O)<=a):n<=floor a:=Nat.le_floor h
lemma nL1 (a:O):a<(floor a:O)+1:=Nat.lt_floor_add_one a
lemma nLc (a:O):a<=(ceil a:O):=Nat.le_ceil a
lemma oLp {a:O} (ha:1<=a) {n:ℕ}:1<=a^n:=one_le_pow₀ ha
lemma eLe {a b:O}:exp a<=exp b↔a<=b:=Real.exp_le_exp
lemma ePp (a:O):0<exp a:=Real.exp_pos a
lemma rNn {a:O} (ha:0<=a) (b:O):0<=a^b:=Real.rpow_nonneg ha b
lemma rLl {x y z:O} (hx:0<=x) (hxy:x<=y) (hz:0<=z):x^z<=y^z:=Real.rpow_le_rpow hx hxy hz
lemma rLe {x y z:O} (hx:1<=x) (hyz:y<=z):x^y<=x^z:=Real.rpow_le_rpow_of_exponent_le hx hyz
lemma dLr {a b c:O} (h:a<=b) (hc:0<=c):a / c<=b / c:=div_le_div_of_nonneg_right h hc
lemma dLl {a b c:O} (ha:0<=a) (hc:0<c) (h:c<=b):a / b<=a / c:=div_le_div_of_nonneg_left ha hc h
lemma mLm {a b c d:O} (h1:a<=b) (h2:c<=d) (hc:0<=c) (hb:0<=b):a*c<=b*d:=mul_le_mul h1 h2 hc hb
lemma wLa {V} {G:SG V} {u v w:V} (p:G.Walk u v) (q:G.Walk v w):(p.append q).length=p.length+q.length:=Walk.length_append p q
lemma wLr {V} {G:SG V} {u v:V} (p:G.Walk u v):p.reverse.length=p.length:=Walk.length_reverse p
lemma wSa {V} {G:SG V} {u v w x:V} {p:G.Walk u v} {q:G.Walk v w}:x∈(p.append q).support↔x∈p.support\/x∈q.support:=Walk.mem_support_append_iff p q
lemma wSm {V} {G:SG V} {u v:V} (p:G.Walk u v):u∈p.support:=Walk.start_mem_support p
lemma wEm {V} {G:SG V} {u v:V} (p:G.Walk u v):v∈p.support:=Walk.end_mem_support p
lemma wSn {V} {G:SG V} {u v:V} (p:G.Walk u v):p.support≠[] :=Walk.support_ne_nil p
lemma wLs {V} {G:SG V} {u v:V} (p:G.Walk u v):p.support.length=p.length+1:=Walk.length_support p
lemma wIp {V} {G:SG V} {u v:V} {p:G.Walk u v}:p.IsPath↔p.support.Nodup:=Walk.isPath_def p
lemma wGl {V} {G:SG V} {u v:V} (p:G.Walk u v):p.support.getLast (Walk.support_ne_nil p)=v:=Walk.getLast_support p
lemma cSd {α} [DecidableEq α] (s t:FS α):(s \ t).card+(s∩t).card=s.card:=Finset.card_sdiff_add_card_inter s t
lemma mSs {α} (a:α):a∈({a}:FS α):=Finset.mem_singleton_self a
lemma mUv {α} [Fintype α] (a:α):a∈(Finset.univ:FS α):=Finset.mem_univ a
lemma sR {α} {s:FS α}:s⊆s:=Finset.Subset.rfl
lemma lMl {α} [LinearOrder α] (a b:α):a<=max a b:=le_max_left a b
lemma lMr {α} [LinearOrder α] (a b:α):b<=max a b:=le_max_right a b
lemma lDi {a b c:O} (hc:0<c):a<=b / c↔a*c<=b:=le_div_iff₀ hc
lemma dLi {a b c:O} (hb:0<b):a / b<=c↔a<=c*b:=div_le_iff₀ hb
lemma dLs {a b:O} (ha:0<=a) (hb:1<=b):a / b<=a:=div_le_self ha hb
lemma nSl (n m:ℕ):n - m<=n:=Nat.sub_le n m
lemma nMo {a b:ℕ} (h:a<b):a % b=a:=Nat.mod_eq_of_lt h
lemma nMm {a b c d:ℕ} (h1:a<=b) (h2:c<=d):a*c<=b*d:=Nat.mul_le_mul h1 h2
lemma nMl (a:ℕ) {b c:ℕ} (h:b<=c):a*b<=a*c:=Nat.mul_le_mul_left a h
lemma nMr (c:ℕ) {a b:ℕ} (h:a<=b):a*c<=b*c:=Nat.mul_le_mul_right c h
lemma nPl {a b:ℕ} (h:a<=b) (n:ℕ):a^n<=b^n:=Nat.pow_le_pow_left h n
lemma nAa {a b c d:ℕ} (h1:a<=b) (h2:c<=d):a+c<=b+d:=Nat.add_le_add h1 h2
lemma r1 (x:O):x^(1:O)=x:=Real.rpow_one x
lemma rN (x:O) (n:ℕ):x^(n:O)=x^n:=Real.rpow_natCast x n
lemma lP (x:O) (n:ℕ):log (x^n)=n*log x:=Real.log_pow x n
lemma e1l:exp 1<2.7182818286:=Real.exp_one_lt_d9
lemma e1g:2.7182818283<exp 1:=Real.exp_one_gt_d9
def q3 {V:Type*} (G:SG V) (S:FS V):SG V where
 Adj u v:=G.Adj u v/\u∈S/\v∈S
 symm:=⟨λ _ _ h=>⟨h.1.symm,h.2.2,h.2.1⟩⟩
 loopless:=⟨λ _ h=>G.loopless.irrefl _ h.1⟩
lemma q4 {V:Type*} {G H:SG V} (h:H<=G) : H.cycleLengths⊆G.cycleLengths:=by rintro m ⟨a,w,hw,rfl⟩;exact ⟨a,w.mapLe h,hw.mapLe h,by simp⟩
lemma q5 {V:Type*} [Fintype V] (G:SG V) {m:ℕ} (hm:m∈G.cycleLengths):m<=Fintype.card V:=by
 obtain ⟨a,w,hw,rfl⟩:=hm;have h1:=hw.support_nodup
 have h2:w.support.tail.length=w.length:=by
  rw[List.length_tail,wLs];simp
 rw[<- h2];exact h1.length_le_card
def CF {V:Type*} [Fintype V] (G:SG V):FS ℕ :=
 (range (Fintype.card V+1)).filter (·∈G.cycleLengths)
lemma q6 {V:Type*} [Fintype V] (G:SG V) : (CF G:Set ℕ)=G.cycleLengths:=by
 ext m
 simp only[CF,coe_filter,mem_range,Set.mem_ofPred_eq];constructor
 . rintro ⟨_,h⟩;exact h
 . intro h;exact ⟨Nat.lt_succ_of_le (q5 G h),h⟩
def W {V:Type*} [Fintype V] (G:SG V):O :=
 ∑ a∈CF G,(1:O)/a
lemma q7 {V:Type*} [Fintype V] (G:SG V) : (∑ᶠ a∈G.cycleLengths,(1:O)/a)=W G:=by rw[<- q6,finsum_mem_coe_finset];rfl
def dS {V:Type*} (G:SG V) (S:FS V) (v:V):ℕ :=
 #(S.filter (G.Adj v))
lemma q8 {V:Type*} (G:SG V) (S:FS V) {v:V} (hv:v∈S) : ∑ u∈S,dS G S u=∑ u∈S.erase v,dS G (S.erase v) u+2*dS G S v:=by
 rw[<- add_sum_erase S _ hv]
 have key:∀ u∈S.erase v,dS G S u=dS G (S.erase v) u+if G.Adj u v then 1 else 0:=by
  intro u _;unfold dS;have hS:S=insert v (S.erase v):=(insert_erase hv).symm
  conv_lhs=>rw[hS]
  rw[filter_insert]
  split_ifs
  . rw[card_insert_of_notMem (by simp)]
  . rfl
 rw[sum_congr rfl key,sum_add_distrib]
 have h2:∑ u∈S.erase v,(if G.Adj u v then 1 else 0)=dS G S v:=by
  rw[sum_boole];unfold dS;simp only[Nat.cast_id];congr 1;ext u;simp only[mem_filter,mem_erase];constructor
  . rintro ⟨⟨_,hu⟩,hadj⟩;exact ⟨hu,hadj.symm⟩
  . rintro ⟨hu,hadj⟩;exact ⟨⟨λ h=>G.loopless.irrefl _ (h ▸ hadj),hu⟩,hadj.symm⟩
 rw[h2];ring
lemma q9 {V:Type*} [Fintype V] (G:SG V) : (∑ u∈(univ:FS V),(dS G univ u:O))=2*(G.edgeSet.ncard:O):=by
 have h1:∀ u:V,dS G univ u=G.degree u:=by
  intro u;unfold dS;rw[<- G.card_neighborFinset_eq_degree];congr 1;ext x;simp
 simp_rw[h1];have h2:=G.sum_degrees_eq_twice_card_edges
 have h3:(G.edgeFinset.card:O)=(G.edgeSet.ncard:O):=by
  rw[Set.ncard_eq_toFinset_card' G.edgeSet];simp [SimpleGraph.edgeFinset]
 rw[<- Nat.cast_sum,h2];push_cast;rw[h3]
lemma qa {V:Type*} {G:SG V} {x y:V} (p:G.Walk x y) (hp:p.IsPath) (h0:2<=p.length) (h5:G.Adj y x) : p.length+1∈G.cycleLengths:=by
 refine ⟨y,Walk.cons h5 p,?_,by simp⟩;rw[Walk.cons_isCycle_iff];refine ⟨hp,?_⟩;intro h3;have hne:x≠y:=λ h=>G.loopless.irrefl _ (h ▸ h5)
 cases p with
 | nil=>simp at h0
 | @cons _ z _ hxz p' =>
  have hzy:z≠y:=by
   intro h;subst h;simp at h0
   cases p' with
   | nil=>simp at h0
   | cons h1 p'' =>
    have h2:=hp.support_nodup;simp only[support_cons,nodup_cons] at h2;exact h2.2.1 (wEm p'')
  simp only[Walk.edges_cons,List.mem_cons] at h3
  rcases h3 with h6 | hmem'
  .
   rw[Sym2.eq_iff] at h6
   rcases h6 with ⟨h1,_⟩ | ⟨h1,_⟩
   . exact hne h1.symm
   . exact hzy h1.symm
  . have h4:=Walk.snd_mem_support_of_mem_edges p' hmem';have h2:=hp.support_nodup;simp only[support_cons,nodup_cons] at h2;exact h2.1 h4
def qb {V:Type*} (G:SG V) (S:FS V) (col:V->Bool) (v:V):ℕ :=
 #(S.filter (λ u=>G.Adj v u/\col u≠col v))
def qc {V:Type*} (G:SG V) (S:FS V) (col:V->Bool) (v:V):ℕ :=
 #(S.filter (λ u=>G.Adj v u/\col u=col v))
lemma qd {V:Type*} (G:SG V) (S:FS V) (h0:V->Bool) (v:V) : qb G S h0 v+qc G S h0 v=dS G S v:=by
 unfold qb qc dS;rw[<- card_union_of_disjoint]
 . congr 1;ext u;simp only[mem_union,mem_filter];tauto
 . rw[dL];intro u h1 h2;simp only[mem_filter] at h1 h2;exact h1.2.2 h2.2.2
lemma qe {V:Type*} (G:SG V) (S:FS V) (h0:V->Bool) (v:V) : qb G S (Function.update h0 v (!h0 v)) v=qc G S h0 v:=by
 unfold qb qc;congr 1;ext u;simp only[mem_filter,Function.update_self];constructor
 .
  rintro ⟨hu,hadj,hc⟩;have h3:u≠v:=λ h=>G.loopless.irrefl _ (h ▸ hadj)
  rw[update_of_ne h3] at hc;refine ⟨hu,hadj,?_⟩
  cases h1:h0 u <;> cases h2:h0 v <;> simp_all
 .
  rintro ⟨hu,hadj,hc⟩;have h3:u≠v:=λ h=>G.loopless.irrefl _ (h ▸ hadj)
  rw[update_of_ne h3];refine ⟨hu,hadj,?_⟩
  cases h1:h0 u <;> cases h2:h0 v <;> simp_all
lemma qf {V:Type*} (S:FS V) (v:V) (P:V->Prop) [DecidablePred P] : #(S.filter P)=#((S.erase v).filter P)+(if v∈S/\P v then 1 else 0):=by
 by_cases hv:v∈S
 .
  have hS:S=insert v (S.erase v):=(insert_erase hv).symm
  conv_lhs=>rw[hS]
  rw[filter_insert]
  by_cases hP:P v
  . rw[if_pos hP,card_insert_of_notMem (by simp),if_pos ⟨hv,hP⟩]
  . rw[if_neg hP,if_neg (λ h=>hP h.2)];simp
 . rw[Finset.erase_eq_of_notMem hv];simp [hv]
lemma qg {V:Type*} (G:SG V) (S:FS V) (h0:V->Bool) (v w:V) (hw:w≠v) : (qb G S (Function.update h0 v (!h0 v)) w:ℤ)=qb G S h0 w + (if v∈S/\G.Adj w v/\h0 v=h0 w then 1 else 0) - (if v∈S/\G.Adj w v/\h0 v≠h0 w then 1 else 0):=by
 unfold qb;rw[qf S v,qf S v]
 have h3:((S.erase v).filter (λ u=>G.Adj w u/\Function.update h0 v (!h0 v) u ≠
   Function.update h0 v (!h0 v) w))=((S.erase v).filter (λ u=>G.Adj w u/\h0 u≠h0 w)):=by
  ext u;simp only[mem_filter,mem_erase]
  constructor
  . rintro ⟨⟨huv,hu⟩,h⟩;rw[update_of_ne huv,update_of_ne hw] at h;exact ⟨⟨huv,hu⟩,h⟩
  . rintro ⟨⟨huv,hu⟩,h⟩;rw[update_of_ne huv,update_of_ne hw];exact ⟨⟨huv,hu⟩,h⟩
 rw[h3];simp only[Function.update_self,update_of_ne hw]
 by_cases hv:v∈S <;> by_cases ha:G.Adj w v <;> cases h1:h0 v <;> cases h2:h0 w <;>
  simp [hv,ha]
lemma qh {V:Type*} [Fintype V] (G:SG V) (S:FS V) : ∃ col:V->Bool,∀ v∈S,dS G S v<=2*qb G S col v:=by
 obtain ⟨col,-,h5⟩:=exists_max_image (univ:FS (V->Bool))
  (λ col=>∑ w∈S,qb G S col w) Finset.univ_nonempty
 refine ⟨col,λ v hv=>?_⟩
 by_contra h6
 push Not at h6
 have hcs:=qd G S col v;set h0:=Function.update col v (!col v);have h1:=h5 h0 (mUv _)
 have h4:(∑ w∈S,(qb G S h0 w:ℤ)) =
   ∑ w∈S,(qb G S col w:ℤ)+2*((qc G S col v:ℤ) - qb G S col v):=by
  rw[<- add_sum_erase S _ hv,<- add_sum_erase S (λ w=>(qb G S col w:ℤ)) hv]
  rw[qe];rw[sum_congr rfl (λ w hw=>qg G S col v w (Finset.ne_of_mem_erase hw))]
  rw[Finset.sum_sub_distrib,sum_add_distrib]
  have e1:∑ w∈S.erase v,(if v∈S/\G.Adj w v/\col v=col w then (1:ℤ) else 0) =
    qc G S col v:=by
   rw[sum_boole];unfold qc;congr 1;congr 1;ext u;simp only[mem_filter,mem_erase];constructor
   . rintro ⟨⟨_,hu⟩,-,h2,h3⟩;exact ⟨hu,h2.symm,h3.symm⟩
   . rintro ⟨hu,h2,h3⟩;exact ⟨⟨λ h=>G.loopless.irrefl _ (h ▸ h2),hu⟩,hv,h2.symm,h3.symm⟩
  have e2:∑ w∈S.erase v,(if v∈S/\G.Adj w v/\col v≠col w then (1:ℤ) else 0) =
    qb G S col v:=by
   rw[sum_boole];unfold qb;congr 1;congr 1;ext u;simp only[mem_filter,mem_erase];constructor
   . rintro ⟨⟨_,hu⟩,-,h2,h3⟩;exact ⟨hu,h2.symm,Ne.symm h3⟩
   . rintro ⟨hu,h2,h3⟩;exact ⟨⟨λ h=>G.loopless.irrefl _ (h ▸ h2),hu⟩,hv,h2.symm,Ne.symm h3⟩
  rw[e1,e2];ring
 have h7:((∑ w∈S,qb G S h0 w:ℕ):ℤ)<=((∑ w∈S,qb G S col w:ℕ):ℤ):=by
  exact_mod_cast h1
 push_cast at h7;rw[h4] at h7
 have:(qc G S col v:ℤ) > qb G S col v:=by
  have:(dS G S v:ℤ)=qb G S col v+qc G S col v:=by exact_mod_cast hcs.symm
  have h2:(2*qb G S col v:ℤ) < dS G S v:=by exact_mod_cast h6
  linarith
 linarith
def bip {V:Type*} (G:SG V) (col:V->Bool):SG V where
 Adj u v:=G.Adj u v/\col u≠col v
 symm:=⟨λ _ _ h=>⟨h.1.symm,Ne.symm h.2⟩⟩
 loopless:=⟨λ _ h=>G.loopless.irrefl _ h.1⟩
lemma qi {V:Type*} (G:SG V) (col:V->Bool):bip G col<=G :=
 λ _ _ h=>h.1
lemma qj {V:Type*} (G:SG V) (S:FS V) (h0:V->Bool) (v:V) : dS (bip G h0) S v=qb G S h0 v:=by
 unfold dS qb;congr 1;ext u;simp only[mF];constructor
 . rintro ⟨hu,h⟩;exact ⟨hu,h.1,Ne.symm h.2⟩
 . rintro ⟨hu,h1,h2⟩;exact ⟨hu,h1,Ne.symm h2⟩
def qk {V:Type*} (G:SG V) (col:V->Bool):Prop :=
 ∀ u v,G.Adj u v->col u≠col v
lemma ql {V:Type*} (G:SG V) (col:V->Bool) :
 qk (bip G col) col:=λ _ _ h=>h.2
lemma qm {V:Type*} {G:SG V} {h0:V->Bool} (h1:qk G h0) {u v:V} (p:G.Walk u v) : Even p.length↔h0 u=h0 v:=by
 induction p with
 | nil=>simp
 | @cons a b c hab p' ih =>
  have hne:h0 a≠h0 b:=h1 a b hab;simp only[length_cons,Nat.even_add_one,ih]
  cases ha:h0 a <;> cases hb:h0 b <;> cases hc:h0 c <;> simp_all
def qn {V:Type*} (G:SG V) (S X:FS V):FS V :=
 (S \ X).filter (λ v=>∃ u∈X,G.Adj u v)
lemma qo {V:Type*} (G:SG V) (S X:FS V) (v:V) : v∈qn G S X↔v∈S/\v ∉ X/\∃ u∈X,G.Adj u v:=by simp only[qn,mem_filter,mem_sdiff,and_assoc]
lemma qq {V:Type*} (G:SG V) (S X:FS V) :
 qn G S X⊆S:=λ _ hv=>(qo G S X _).mp hv |>.1
lemma qr {V:Type*} (G:SG V) (S X:FS V) : Disjoint X (qn G S X):=by rw[dL];intro v hvX hvN;exact ((qo G S X v).mp hvN).2.1 hvX
def qs {V:Type*} (G:SG V) (S:FS V):ℕ->FS V->FS V
 | 0,X=>X∩S
 | r+1,X=>qs G S r X∪qn G S (qs G S r X)
lemma qt {V:Type*} (G:SG V) (S:FS V) (r:ℕ) (X:FS V) : qs G S r X⊆S:=by
 induction r with
 | zero=>exact inter_subset_right
 | succ r ih=>exact uS ih (qq G S _)
lemma qu {V:Type*} (G:SG V) (S:FS V) {r₁ r2:ℕ} (h:r₁<=r2) (X:FS V):qs G S r₁ X⊆qs G S r2 X:=by
 induction h with
 | refl=>exact sR
 | step _ ih=>exact ih.trans sUl
lemma qv {V:Type*} (G:SG V) (S:FS V) (r:ℕ) {X Y:FS V} (hXY:X⊆Y):qs G S r X⊆qs G S r Y:=by
 induction r with
 | zero=>exact inter_subset_inter_right hXY
 | succ r ih =>
  intro v hv
  rcases mem_union.mp hv with h1 | h2
  . exact mUl _ (ih h1)
  .
   by_cases h0:v∈qs G S r Y
   . exact mUl _ h0
   . obtain ⟨hvS,_,u,hu,huv⟩:=(qo G S _ v).mp h2;exact mUr _ ((qo G S _ v).mpr ⟨hvS,h0,u,ih hu,huv⟩)
lemma qw {V:Type*} (G:SG V) {S T:FS V} (h3:S⊆T) (r:ℕ) (X:FS V):qs G S r X⊆qs G T r X:=by
 induction r with
 | zero=>exact inter_subset_inter_left h3
 | succ r ih =>
  intro v hv
  rcases mem_union.mp hv with h1 | h2
  . exact mUl _ (ih h1)
  .
   by_cases h0:v∈qs G T r X
   . exact mUl _ h0
   . obtain ⟨hvS,_,u,hu,huv⟩:=(qo G S _ v).mp h2;exact mUr _ ((qo G T _ v).mpr ⟨h3 hvS,h0,u,ih hu,huv⟩)
lemma qx {V:Type*} (G:SG V) (S:FS V) (r:ℕ) (X:FS V) :
  #(qs G S (r+1) X)=#(qs G S r X)+#(qn G S (qs G S r X)) :=
 card_union_of_disjoint (qr G S _)
lemma qy {V:Type*} (G:SG V) (S:FS V) (r₁ r2:ℕ) (X:FS V) : qs G S (r₁+r2) X=qs G S r2 (qs G S r₁ X):=by
 induction r2 with
 | zero =>
  simp only[Nat.add_zero,qs];exact (inter_eq_left.mpr (qt G S r₁ X)).symm
 | succ r2 ih =>
  rw[<- Nat.add_assoc];simp only[qs,ih]
lemma qz {V ι:Type*} (G:SG V) (S:FS V) (r:ℕ) (I:FS ι) (f:ι->FS V) : qs G S r (I.biUnion f)=I.biUnion (λ i=>qs G S r (f i)):=by
 induction r with
 | zero =>
  ext v;simp only[qs,mem_inter,mB]
  exact ⟨λ⟨⟨i,hi,hv⟩,hvS⟩=>⟨i,hi,hv,hvS⟩,λ⟨i,hi,hv,hvS⟩=>⟨⟨i,hi,hv⟩,hvS⟩⟩
 | succ r ih =>
  ext v
  simp only[qs,mem_union,ih,mB,qo];constructor
  .
   rintro (⟨i,hi,hv⟩ | ⟨hvS,hnot,u,⟨i,hi,hu⟩,huv⟩)
   . exact ⟨i,hi,Or.inl hv⟩
   . exact ⟨i,hi,Or.inr ⟨hvS,λ h=>hnot ⟨i,hi,h⟩,u,hu,huv⟩⟩
  .
   rintro ⟨i,hi,hv | ⟨hvS,_,u,hu,huv⟩⟩
   . exact Or.inl ⟨i,hi,hv⟩
   .
    by_cases h0:∃ j∈I,v∈qs G S r (f j)
    . exact Or.inl h0
    . exact Or.inr ⟨hvS,h0,u,⟨i,hi,hu⟩,huv⟩
lemma qA {V:Type*} {G:SG V} {S X:FS V} {u v:V} (h0:u∈X) (h2:u∈S) (p:(q3 G S).Walk u v) : v∈qs G S p.length X:=by
 induction p generalizing X with
 | nil=>exact rI ⟨h0,h2⟩
 | @cons a b c hab p' ih =>
  have h4:b∈S:=hab.2.2
  have hb1:b∈qs G S 1 X:=by
   by_cases h5:b∈X∩S
   . exact mUl _ h5
   .
    exact mUr _ ((qo G S _ b).mpr
     ⟨h4,h5,a,rI ⟨h0,h2⟩,hab.1⟩)
  have h1:=qv G S p'.length (sSm hb1);have hc:c∈qs G S p'.length {b}:=ih (mSs b) h4;have h3:=h1 hc;rw[<- qy] at h3;simpa [Nat.add_comm] using h3
lemma qB {V:Type*} {G:SG V} {S X:FS V} {r:ℕ} {v:V} (hv:v∈qs G S r X) : ∃ u∈X∩S,∃ p:(q3 G S).Walk u v,p.IsPath/\p.length<=r /\ ∀ w∈p.support,w∈qs G S r X:=by
 induction r generalizing v with
 | zero =>
  exact ⟨v,hv,Walk.nil,Walk.IsPath.nil,le_rfl,λ w hw=>by
   simp only[support_nil,List.mem_singleton] at hw;subst hw;exact hv⟩
 | succ r ih =>
  rcases mem_union.mp hv with hv0 | h6
  . obtain ⟨u,hu,p,hp,h4,h1⟩:=ih hv0;exact ⟨u,hu,p,hp,by omega,λ w hw=>mUl _ (h1 w hw)⟩
  .
   obtain ⟨hvS,h3,w,hw,hwv⟩:=(qo G S _ v).mp h6;obtain ⟨u,hu,p,hp,h4,h1⟩:=ih hw;have hwS:w∈S:=qt G S r X hw;have h5:(q3 G S).Adj w v:=⟨hwv,hwS,hvS⟩;let q:(q3 G S).Walk u v:=p.concat h5;have h0:v ∉ p.support:=λ hm=>h3 (h1 v hm)
   have h2:q.IsPath:=by
    rw[wIp,support_concat,<- concat_eq_append];exact hp.support_nodup.concat h0
   refine ⟨u,hu,q,h2,by simp [q];omega,λ z hz=>?_⟩
   rw[support_concat,mem_append,List.mem_singleton] at hz
   rcases hz with hz1 | rfl
   . exact mUl _ (h1 z hz1)
   . exact mUr _ h6
lemma qC {V:Type*} (G:SG V) (S Y X:FS V) (r:ℕ) (h0:Disjoint (qs G S r X) Y) : qs G (S \ Y) r X=qs G S r X:=by
 induction r with
 | zero =>
  ext v;simp only[qs,mem_inter,mem_sdiff]
  constructor
  . rintro ⟨hvX,hvS,_⟩;exact ⟨hvX,hvS⟩
  . rintro ⟨hvX,hvS⟩;exact ⟨hvX,hvS,pD h0 (mem_inter.mpr ⟨hvX,hvS⟩)⟩
 | succ r ih =>
  have h2:Disjoint (qs G S r X) Y :=
   h0.mono_left (qu G S (Nat.le_succ r) X)
  have ihr:=ih h2
  ext v
  simp only[qs,ihr,mem_union,qo,mem_sdiff];constructor
  .
   rintro (h1 | ⟨⟨hvS,_⟩,hnot,u,hu,huv⟩)
   . exact Or.inl h1
   . exact Or.inr ⟨hvS,hnot,u,hu,huv⟩
  .
   rintro (h1 | ⟨hvS,hnot,u,hu,huv⟩)
   . exact Or.inl h1
   . refine Or.inr ⟨⟨hvS,?_⟩,hnot,u,hu,huv⟩;exact pD h0 (mUr _ ((qo G S _ v).mpr ⟨hvS,hnot,u,hu,huv⟩))
lemma qD {V:Type*} (G:SG V) (S X:FS V) (D_:ℕ) (hD_:∀ v∈S,dS G S v<=D_) (r:ℕ) : #(qs G S r X)<=(D_+1)^r*#(X∩S):=by
 induction r with
 | zero=>simp [qs]
 | succ r ih =>
  rw[qx]
  have hnb:#(qn G S (qs G S r X))<=D_*#(qs G S r X):=by
   have h0:qn G S (qs G S r X)⊆(qs G S r X).biUnion (λ u=>S.filter (G.Adj u)):=by
    intro v hv;obtain ⟨hvS,_,u,hu,huv⟩:=(qo G S _ v).mp hv;exact mB.mpr ⟨u,hu,mem_filter.mpr ⟨hvS,huv⟩⟩
   calc
    #(qn G S (qs G S r X))
     <= #((qs G S r X).biUnion (λ u=>S.filter (G.Adj u))):=cL h0
    _<=∑ u∈qs G S r X,#(S.filter (G.Adj u)):=cBu
    _<=∑ _u∈qs G S r X,D_:=sum_le_sum λ u hu=>hD_ u (qt G S r X hu)
    _=#(qs G S r X)*D_:=by simp
    _=D_*#(qs G S r X):=mul_comm _ _
  calc
   #(qs G S r X)+#(qn G S (qs G S r X))
    <= (D_+1)*#(qs G S r X):=by rw[Nat.add_mul,one_mul];omega
   _<=(D_+1)*((D_+1)^r*#(X∩S)):=nMl _ ih
   _=(D_+1)^(r+1)*#(X∩S):=by rw[pow_succ'];ring
lemma qE {V:Type*} {G:SG V} {S A B:FS V} {r:ℕ} (_hAS:A⊆S) (_hBS:B⊆S) (j2:∃ a∈A,∃ b∈B,∃ p:(q3 G S).Walk a b,p.length<=r) : ∃ (a:V) (b:V) (_:a∈A) (_:b∈B) (p:(q3 G S).Walk a b), p.IsPath/\p.length<=r /\ (∀ w∈p.support,w∈A->w=a) /\ (∀ w∈p.support,w∈B->w=b) /\ (∀ (a':V) (b':V),a'∈A->b'∈B->∀ q:(q3 G S).Walk a' b',p.length<=q.length):=by
 let P:ℕ->Prop:=λ L=>∃ a∈A,∃ b∈B,∃ p:(q3 G S).Walk a b,p.length=L
 have hP:∃ L,P L:=by
  obtain ⟨a,ha,b,hb,p,_⟩:=j2;exact ⟨p.length,a,ha,b,hb,p,rfl⟩
 let h6:=find hP;have h8:P h6:=find_spec hP
 have h3:h6<=r:=by
  obtain ⟨a,ha,b,hb,p,j1⟩:=j2;exact (find_min' hP ⟨a,ha,b,hb,p,rfl⟩).trans j1
 obtain ⟨a,ha,b,hb,p0,h7⟩:=h8;let p:=p0.bypass;have h4:p.IsPath:=p0.bypass_isPath;have h0:p.length<=h6:=(length_bypass_le_length p0).trans_eq h7
 have h5:∀ a' b',a'∈A->b'∈B->∀ q:(q3 G S).Walk a' b',p.length<=q.length:=by
  intro a' b' ha' hb' q;exact h0.trans (find_min' hP ⟨a',ha',b',hb',q,rfl⟩)
 refine ⟨a,b,ha,hb,p,h4,h0.trans h3,?_,?_,h5⟩
 .
  intro w hw hwA;by_contra hwa;let q:=p.dropUntil w hw
  have j0:q.length < p.length:=by
   have h1:=take_spec p hw
   have h2:(p.takeUntil w hw).length+q.length=p.length:=by
    rw[<- wLa,h1]
   have h9:0 < (p.takeUntil w hw).length:=by
    cases ht:p.takeUntil w hw with
    | nil=>exact absurd rfl hwa
    | cons _ _=>simp
   omega
  exact absurd (h5 w b hwA hb q) (not_le.mpr j0)
 .
  intro w hw hwB;by_contra hwb;let q:=p.takeUntil w hw
  have j0:q.length < p.length:=by
   have h1:=take_spec p hw
   have h2:q.length+(p.dropUntil w hw).length=p.length:=by
    rw[<- wLa,h1]
   have h9:0 < (p.dropUntil w hw).length:=by
    cases hd:p.dropUntil w hw with
    | nil=>exact absurd rfl hwb
    | cons _ _=>simp
   omega
  exact absurd (h5 a w ha hwB q) (not_le.mpr j0)
lemma qF {V:Type*} {G:SG V} {S A B:FS V} {r₁ r2:ℕ} (h0:(qs G S r₁ A∩qs G S r2 B).Nonempty) : ∃ a∈A,∃ b∈B,∃ p:(q3 G S).Walk a b,p.length<=r₁+r2:=by
 obtain ⟨w,hw⟩:=h0;obtain ⟨hw1,hw2⟩:=mem_inter.mp hw;obtain ⟨a,ha,p1,_,hlen1,_⟩:=qB hw1;obtain ⟨b,hb,p2,_,hlen2,_⟩:=qB hw2
 exact ⟨a,(mem_inter.mp ha).1,b,(mem_inter.mp hb).1,p1.append p2.reverse,
  by rw[wLa,wLr];omega⟩
lemma qG {V:Type*} [Fintype V] (G:SG V) {L:O} (hL:exp 2000000<=L) (ja:∀ m:ℕ,Even m->(log L)^8<=(m:O)->(m:O)<=L->m∈G.cycleLengths) : (1/2:O)*(log L - 8*log (log L) - 5)<=W G:=by
 have h3:0 < L:=lL2 (ePp 2000000) hL
 have h9:2000000<=log L:=by
  have:=lLl (ePp 2000000) hL
  rwa [log_exp] at this
 have hlogL_pos:0 < log L:=by linarith
 let a:ℕ:=ceil ((log L)^8/2);let b:ℕ:=floor (L/2)
 have h4:1<=a:=by
  apply Nat.one_le_iff_ne_zero.mpr;intro h0;have hle:(log L)^8/2<=(a:O):=nLc _;rw[h0,Nat.cast_zero] at hle
  have:(0:O) < (log L)^8/2:=by positivity
  linarith
 have j3:(a:O)<=(log L)^8:=by
  have h1:(a:O) < (log L)^8/2+1:=ceil_lt_add_one (by positivity)
  have h2:(2:O)<=(log L)^8:=by
   calc
    (2:O)<=2000000^8:=by norm_num
    _<=(log L)^8:=pLl (by norm_num) h9 8
  linarith
 have j1:L/2<=(b:O)+1:=(nL1 (L/2)).le
 have hlog8_le_L:(log L)^8<=L/4:=by
  set t:=log L;have heq:L=exp t:=(exp_log h3).symm;rw[heq]
  have j6:t^9/(factorial 9:O)<=exp t:=by
   have h:=Real.sum_le_exp_of_nonneg (x:=t) (by linarith) 10
   have h7:t^9/(factorial 9:O)<=∑ i∈range 10,t^i/(factorial i:O) :=
    Finset.single_le_sum (f:=λ i=>t^i/(factorial i:O))
     (λ _ _=>by positivity) (mem_range.mpr (by omega))
   exact h7.trans h
  have j8:(factorial 9:O)=362880:=by norm_num [factorial]
  rw[j8] at j6
  have h4t:4*t^8<=t^9/362880:=by
   rw[lDi (by norm_num:(0:O) < 362880)]
   have h1:4*362880<=t:=by linarith
   calc
    4*t^8*362880=(4*362880)*t^8:=by ring
    _<=t*t^8:=mlR h1 (by positivity)
    _=t^9:=by ring
  linarith
 have hab:a<=b:=by
  have hR:(a:O) < (b:O)+1:=by linarith
  have hN:a < b+1:=by exact_mod_cast hR
  omega
 let J:FS ℕ:=Finset.Icc a b;let M:FS ℕ:=J.image (λ j=>2*j)
 have jb:M⊆CF G:=by
  intro m hm;obtain ⟨j,hj,rfl⟩:=mem_image.mp hm;obtain ⟨haj,hjb⟩:=Finset.mem_Icc.mp hj
  have h8:2*j∈G.cycleLengths:=by
   apply ja (2*j) ⟨j,by ring⟩
   .
    have h1:(log L)^8/2<=(a:O):=nLc _
    have h2:(a:O)<=(j:O):=by exact_mod_cast haj
    push_cast;linarith
   .
    have h1:(j:O)<=(b:O):=by exact_mod_cast hjb
    have h2:(b:O)<=L/2:=nFl (by positivity);push_cast;linarith
  rw[<- q6 G] at h8;exact h8
 have j4:∑ j∈J,(1:O)/((2*j:ℕ):O)<=W G:=by
  calc
   ∑ j∈J,(1:O)/((2*j:ℕ):O)
    = ∑ m∈M,(1:O)/(m:O):=by
     rw[Finset.sum_image (λ x _ y _ h=>by omega)]
   _<=∑ m∈CF G,(1:O)/(m:O) :=
     sum_le_sum_of_subset_of_nonneg jb (λ _ _ _=>by positivity)
 have h6:∀ j∈J,(1/2:O)*(log ((j+1:ℕ):O) - log (j:O)) <=
   (1:O)/((2*j:ℕ):O):=by
  intro j hj;have hj1:1<=j:=lT h4 (Finset.mem_Icc.mp hj).1
  have j0:(0:O) < (j:O):=by exact_mod_cast (show 0 < j by omega)
  have j7:log ((j+1:ℕ):O) - log (j:O)<=1/(j:O):=by
   rw[<- Real.log_div (by positivity) j0.ne']
   have j9:((j+1:ℕ):O)/(j:O)=1+1/(j:O):=by push_cast;field_simp
   rw[j9];exact (Real.log_le_sub_one_of_pos (by positivity)).trans (by linarith)
  have j5:(1:O)/((2*j:ℕ):O)=(1/2:O)*(1/(j:O)):=by push_cast;ring
  rw[j5];exact mlL j7 (by norm_num)
 have h5:∑ j∈J,(log ((j+1:ℕ):O) - log (j:O)) =
   log ((b+1:ℕ):O) - log (a:O):=by
  have jc:J=Finset.Ico a (b+1):=rfl;rw[jc];have h:=Finset.sum_Ico_sub (f:=λ k:ℕ=>log (k:O)) (by omega:a<=b+1)
  exact h
 have hsum_lb:(1/2:O)*(log ((b+1:ℕ):O) - log (a:O))<=W G:=by
  calc
   (1/2:O)*(log ((b+1:ℕ):O) - log (a:O))
    = ∑ j∈J,(1/2:O)*(log ((j+1:ℕ):O) - log (j:O)):=by
     rw[<- Finset.mul_sum,h5]
   _<=∑ j∈J,(1:O)/((2*j:ℕ):O):=sum_le_sum h6
   _<=W G:=j4
 have hlogb:log L - 1<=log ((b+1:ℕ):O):=by
  have h1:log (L/2)<=log ((b+1:ℕ):O):=by
   apply lLl (by positivity);push_cast;exact j1
  rw[Real.log_div h3.ne' (by norm_num:(2:O)≠0)] at h1
  have hlog2:log 2<=1:=by
   rw[Real.log_le_iff_le_exp (by norm_num)];linarith [add_one_le_exp (1:O)]
  linarith
 have hloga:log (a:O)<=8*log (log L):=by
  have j2:(0:O) < (a:O):=by exact_mod_cast (show 0 < a by omega)
  have h1:=lLl j2 j3;rw[lP] at h1;exact h1
 linarith
def qH {V:Type*} (G:SG V) (S:FS V) (r:ℕ):Prop :=
 ∃ (A:FS V) (mid:Sym2 V->V),
  A⊆S/\#A=r /\
  (∀ u∈A,∀ v∈A,u≠v ->
   mid s(u,v)∈S/\mid s(u,v) ∉ A/\G.Adj u (mid s(u,v))/\G.Adj v (mid s(u,v))) /\
  (∀ u1∈A,∀ v1∈A,u1≠v1->∀ u2∈A,∀ v2∈A,u2≠v2 ->
   mid s(u1,v1)=mid s(u2,v2)->s(u1,v1)=s(u2,v2))
lemma qI {V:Type*} {G:SG V} {S:FS V} {r:ℕ} (ji:qH G S r) (_hr:3<=r) : ∀ m:ℕ,Even m->6<=m->m<=2*r->m∈G.cycleLengths:=by
 obtain ⟨A,jg,_,jc,j9,h8⟩:=ji;intro m ⟨t,hm⟩ hm6 hmr;subst hm
 have ht3:3<=t:=by omega
 have htr:t<=r:=by omega
 obtain ⟨B,hBA,jb⟩:=exists_subset_card_eq (jc ▸ htr);let e:Fin t ≃ B:=(Fintype.equivFinOfCardEq (by simp [jb])).symm;let a:Fin t->V:=λ i=>(e i).1
 have h5:∀ i,a i∈A:=λ i=>hBA (e i).2
 have h0:Injective a:=λ i j h=>e.injective (Subtype.ext h)
 have jd:∀ k (hk:k < t),
   ∃ p:G.Walk (a ⟨0,by omega⟩) (a ⟨k,hk⟩),
    p.IsPath/\p.length=2*k /\
    (∀ v∈p.support,
     (∃ i:Fin t,i.val<=k/\v=a i) \/
     (∃ i:Fin t,∃ hi:i.val < k,v=jg s(a i,a ⟨i.val+1,lL3 hi hk⟩))):=by
  intro k
  induction k with
  | zero =>
   intro hk;refine ⟨Walk.nil,Walk.IsPath.nil,rfl,λ v hv=>?_⟩
   simp only[support_nil,List.mem_singleton] at hv;exact Or.inl ⟨⟨0,hk⟩,le_rfl,hv⟩
  | succ k ih =>
   intro hk;obtain ⟨p,hp,ja,h6⟩:=ih (by omega);let i0:Fin t:=⟨k,by omega⟩;let i1:Fin t:=⟨k+1,hk⟩
   have j8:a i0≠a i1:=λ h=>by
    have:=h0 h;exact absurd (congrArg Fin.val this) (by simp [i0,i1])
   let w:=jg s(a i0,a i1);have hw:=j9 (a i0) (h5 i0) (a i1) (h5 i1) j8
   have h4:w ∉ p.support:=by
    intro j5
    rcases h6 w j5 with ⟨j,_,hj⟩ | ⟨j,je,hj⟩
    . exact hw.2.1 (by dsimp only[w] at hj;rw[hj];exact h5 j)
    .
     have h7:a j≠a ⟨j.val+1,by omega⟩:=λ h=>by
      have:=h0 h;exact absurd (congrArg Fin.val this) (by simp)
     have jf:=h8 (a i0) (h5 i0) (a i1) (h5 i1) j8
      (a j) (h5 j) (a ⟨j.val+1,by omega⟩) (h5 _) h7 hj
     rw[Sym2.eq_iff] at jf
     rcases jf with ⟨h1,h2⟩ | ⟨h1,h2⟩
     . have:=congrArg Fin.val (h0 h1);simp [i0] at this;omega
     . have:=congrArg Fin.val (h0 h2);simp [i1] at this;omega
   have j2:a i1 ∉ p.support:=by
    intro j5
    rcases h6 (a i1) j5 with ⟨j,je,hj⟩ | ⟨j,je,hj⟩
    . have:=congrArg Fin.val (h0 hj);simp [i1] at this;omega
    .
     have h7:a j≠a ⟨j.val+1,by omega⟩:=λ h=>by
      have:=h0 h;exact absurd (congrArg Fin.val this) (by simp)
     exact (j9 (a j) (h5 j) (a ⟨j.val+1,by omega⟩) (h5 _) h7).2.1 (by rw[<- hj];exact h5 i1)
   have jh:w≠a i1:=λ h=>hw.2.1 (by dsimp only[w] at h;rw[h];exact h5 i1)
   let p1:G.Walk (a ⟨0,by omega⟩) w:=p.concat hw.2.2.1;let p2:G.Walk (a ⟨0,by omega⟩) (a i1):=p1.concat hw.2.2.2.symm
   have j4:p1.IsPath:=by
    rw[wIp,support_concat,<- concat_eq_append];exact hp.support_nodup.concat h4
   have h9:a i1 ∉ p1.support:=by
    rw[support_concat,mem_append,List.mem_singleton];rintro (h | h)
    . exact j2 h
    . exact jh h.symm
   have j3:p2.IsPath:=by
    rw[wIp,support_concat,<- concat_eq_append];exact j4.support_nodup.concat h9
   refine ⟨p2,j3,by simp [p2,p1,ja];omega,λ v hv=>?_⟩
   rw[support_concat,mem_append,List.mem_singleton,support_concat,
    mem_append,List.mem_singleton] at hv
   rcases hv with (hv | rfl) | rfl
   .
    rcases h6 v hv with ⟨j,je,hj⟩ | ⟨j,je,hj⟩
    . exact Or.inl ⟨j,by omega,hj⟩
    . exact Or.inr ⟨j,by omega,hj⟩
   . exact Or.inr ⟨i0,by simp [i0],rfl⟩
   . exact Or.inl ⟨i1,le_rfl,rfl⟩
 obtain ⟨p,hp,ja,h6⟩:=jd (t - 1) (by omega);let i0:Fin t:=⟨0,by omega⟩;let h3:Fin t:=⟨t - 1,by omega⟩
 have j1:a h3≠a i0:=λ h=>by
  have:=h0 h;have:=congrArg Fin.val this;simp [h3,i0] at this;omega
 let j0:=jg s(a h3,a i0);have hw:=j9 (a h3) (h5 h3) (a i0) (h5 i0) j1
 have h4:j0 ∉ p.support:=by
  intro j5
  rcases h6 j0 j5 with ⟨j,_,hj⟩ | ⟨j,je,hj⟩
  . exact hw.2.1 (by dsimp only[j0] at hj;rw[hj];exact h5 j)
  .
   have h7:a j≠a ⟨j.val+1,by omega⟩:=λ h=>by
    have:=h0 h;exact absurd (congrArg Fin.val this) (by simp)
   have jf:=h8 (a h3) (h5 h3) (a i0) (h5 i0) j1
    (a j) (h5 j) (a ⟨j.val+1,by omega⟩) (h5 _) h7 hj
   rw[Sym2.eq_iff] at jf
   rcases jf with ⟨h1,h2⟩ | ⟨h1,h2⟩
   . have:=congrArg Fin.val (h0 h1);simp [h3] at this;omega
   . have h1':=congrArg Fin.val (h0 h1);have h2':=congrArg Fin.val (h0 h2);simp [h3,i0] at h1' h2';omega
 let q:G.Walk (a i0) j0:=p.concat hw.2.2.1
 have j6:q.IsPath:=by
  rw[wIp,support_concat,<- concat_eq_append];exact hp.support_nodup.concat h4
 have hq_len:q.length=2*t - 1:=by simp [q,ja];omega
 have jj:=qa q j6 (by omega) hw.2.2.2.symm
 have j7:q.length+1=t+t:=by omega
 rwa [j7] at jj
lemma qJ {V:Type*} {G:SG V} {S U W:FS V} {r:ℕ} (hUS:U⊆S) (hWS:W⊆S) (jl:Disjoint U W) (jn:U.Nonempty) (jm:#W^2<=#U) (js:∀ u∈U,r<=#(W.filter (G.Adj u))) : qH G S r:=by
 let h0:FS (Sym2 V):=W.offDiag.image (λ p=>s(p.1,p.2))
 let j0:FS (Sym2 V)->Prop:=λ I =>
  I⊆h0/\∃ f:Sym2 V->V,
   Set.InjOn f (I:Set (Sym2 V)) /\
   ∀ e∈I,f e∈U/\∀ x∈e,G.Adj (f e) x
 have h5:j0 ∅:=⟨empty_subset _,λ _=>jn.choose,by simp,by simp⟩
 have j5:(h0.powerset.filter j0).Nonempty :=
  ⟨∅,rF ⟨mem_powerset.mpr (empty_subset _),h5⟩⟩
 obtain ⟨I,jd,je⟩:=exists_max_image (h0.powerset.filter j0) Finset.card j5;have jf:j0 I:=(pF jd).2;obtain ⟨h3,f,j9,h6⟩:=jf
 have h9:#I < #U:=by
  have h7:h0.card<=#W*(#W - 1)/2:=by
   by_cases hW:#W=0
   .
    have:W=∅:=Finset.card_eq_zero.mp hW
    subst this;simp [h0]
   .
    have h2:2*h0.card<=W.offDiag.card:=by
     have jc:∀ e∈h0,2<=#(W.offDiag.filter (λ p=>s(p.1,p.2)=e)):=by
      intro e he;obtain ⟨⟨x,y⟩,ji,rfl⟩:=mem_image.mp he;obtain ⟨hx,hy,j5⟩:=Finset.mem_offDiag.mp ji
      have h1:(x,y)∈W.offDiag.filter (λ p=>s(p.1,p.2)=s(x,y)) :=
       rF ⟨ji,rfl⟩
      have h2:(y,x)∈W.offDiag.filter (λ p=>s(p.1,p.2)=s(x,y)) :=
       rF ⟨Finset.mem_offDiag.mpr ⟨hy,hx,j5.symm⟩,Sym2.eq_swap⟩
      have jk:(x,y)≠(y,x):=λ h=>j5 (congrArg Prod.fst h)
      exact (Finset.card_pair jk).symm.le.trans
       (cL (Finset.insert_subset h1 (sSm h2)))
     have jp:=Finset.card_eq_sum_card_fiberwise (f:=λ p:V × V=>s(p.1,p.2))
      (s:=W.offDiag) (t:=h0) (λ p hp=>mem_image.mpr ⟨p,hp,rfl⟩)
     calc
      2*h0.card=∑ _e∈h0,2:=by simp [mul_comm]
      _<=∑ e∈h0,#(W.offDiag.filter (λ p=>s(p.1,p.2)=e)):=sum_le_sum jc
      _=W.offDiag.card:=jp.symm
    rw[Finset.offDiag_card] at h2
    have jr:#W*#W - #W=#W*(#W - 1):=by
     rw[Nat.mul_sub_left_distrib,mul_one]
    rw[jr] at h2;exact (Nat.le_div_iff_mul_le (by norm_num)).mpr (by omega)
  by_cases hW0:#W=0
  . have j7:W=∅:=Finset.card_eq_zero.mp hW0;subst j7;have hI0:#I=0:=Finset.card_eq_zero.mpr (Finset.subset_empty.mp (by simpa [h0] using h3));have hUpos:0 < #U:=jn.card_pos;omega
  .
   have:#W*(#W - 1)/2 < #W^2:=by
    have hlt1:#W - 1 < #W:=by omega
    have h1:#W*(#W - 1) < 2*#W^2:=by
     rw[sq];nlinarith
    omega
   exact (cL h3).trans_lt (h7.trans_lt (this.trans_le jm))
 have himg_card:#(I.image f) < #U:=(card_image_le).trans_lt h9
 have j3:(U \ I.image f).Nonempty:=by
  rw[<- card_pos]
  have jq:I.image f⊆U:=by
   intro x hx;obtain ⟨e,he,rfl⟩:=mem_image.mp hx;exact (h6 e he).1
  rw[card_sdiff_of_subset jq];omega
 obtain ⟨u0,hu0⟩:=j3;obtain ⟨jj,j1⟩:=pS hu0;let A0:FS V:=W.filter (G.Adj u0);have ju:A0⊆W:=filter_subset _ _;have jt:r<=#A0:=js u0 jj;obtain ⟨A,jh,jg⟩:=exists_subset_card_eq jt;have jo:A⊆W:=jh.trans ju
 have h4:∀ x∈A,∀ y∈A,x≠y->s(x,y)∈I:=by
  intro x hx y hy ji;by_contra h8;let I':=insert s(x,y) I
  have j2:s(x,y)∈h0 :=
   mem_image.mpr ⟨(x,y),Finset.mem_offDiag.mpr ⟨jo hx,jo hy,ji⟩,rfl⟩
  let f':Sym2 V->V:=Function.update f s(x,y) u0
  have j4:j0 I':=by
   refine ⟨Finset.insert_subset j2 h3,f',?_,?_⟩
   .
    intro e1 he1 e2 he2 j6;dsimp only[f'] at j6
    rcases mem_insert.mp he1 with rfl | he1' <;> rcases mem_insert.mp he2 with rfl | he2'
    . rfl
    .
     have ja:e2≠s(x,y):=λ h=>h8 (h ▸ he2')
     rw[Function.update_self,update_of_ne ja] at j6;exact absurd (mem_image.mpr ⟨e2,he2',j6.symm⟩) j1
    .
     have jb:e1≠s(x,y):=λ h=>h8 (h ▸ he1')
     rw[update_of_ne jb,Function.update_self] at j6;exact absurd (mem_image.mpr ⟨e1,he1',j6⟩) j1
    .
     have jb:e1≠s(x,y):=λ h=>h8 (h ▸ he1')
     have ja:e2≠s(x,y):=λ h=>h8 (h ▸ he2')
     rw[update_of_ne jb,update_of_ne ja] at j6;exact j9 he1' he2' j6
   .
    intro e he;dsimp only[f']
    rcases mem_insert.mp he with rfl | he'
    .
     rw[Function.update_self];refine ⟨jj,λ z hz=>?_⟩
     rcases Sym2.mem_iff.mp hz with rfl | rfl
     . exact (pF (jh hx)).2
     . exact (pF (jh hy)).2
    .
     have j5:e≠s(x,y):=λ h=>h8 (h ▸ he')
     rw[update_of_ne j5];exact h6 e he'
  have j8:I'∈h0.powerset.filter j0 :=
   rF ⟨mem_powerset.mpr j4.1,j4⟩
  have hle:=je I' j8;rw[card_insert_of_notMem h8] at hle;omega
 refine ⟨A,f,jo.trans hWS,jg,?_,?_⟩
 .
  intro x hx y hy ji;have heI:=h4 x hx y hy ji;have hp:=h6 s(x,y) heI;refine ⟨hUS hp.1,λ hmem=>pD jl hp.1 (jo hmem),?_,?_⟩
  . exact (hp.2 x (Sym2.mem_mk_left x y)).symm
  . exact (hp.2 y (Sym2.mem_mk_right x y)).symm
 . intro u1 hu1 v1 hv1 j5₁ u2 hu2 v2 hv2 j5₂ j6;exact j9 (h4 u1 hu1 v1 hv1 j5₁) (h4 u2 hu2 v2 hv2 j5₂) j6
def qK (e1 k x:O):O :=
 if x < k/5 then 0 else e1/(log (15*x/k))^2
lemma qL {e1 k x:O} (hx:k/5<=x) : qK e1 k x=e1/(log (15*x/k))^2:=by unfold qK;rw[if_neg (not_lt.mpr hx)]
lemma qM:(2:O) < log (15/2):=by
 rw[lIt (by norm_num)]
 have he:exp 1 < 2.72:=by linarith [e1l]
 calc
  exp 2=exp 1*exp 1:=by rw[<- exp_add];norm_num
  _ < 2.72*2.72:=mul_lt_mul he he.le (ePp 1) (by norm_num)
  _ < 15/2:=by norm_num
lemma qN:(1/3:O) < log (8/5):=by
 rw[lIt (by norm_num)]
 have hpow:(exp (1/3))^3 < (8/5:O)^3:=by
  rw[<- exp_nat_mul]
  have h3:((3:ℕ):O)*(1/3:O)=1:=by norm_num
  rw[h3];linarith [e1l]
 nlinarith [ePp (1/3),sq_nonneg (exp (1/3) - 8/5)]
lemma qO {e1 k x y:O} (hε:0<=e1) (hk:0 < k) (hx:k/5<=x) (hxy:x<=y) : qK e1 k y<=qK e1 k x:=by
 rw[qL hx,qL (hx.trans hxy)]
 have h1:(1:O) < 15*x/k:=by
  rw[lt_div_iff₀ hk];linarith
 have h2:0 < log (15*x/k):=lPs h1
 have h0:log (15*x/k)<=log (15*y/k) :=
  lLl (by positivity) (dLr (by linarith) hk.le)
 exact dLl hε (sq_pos_of_pos h2) (pLl h2.le h0 2)
lemma qP {e1 k x y:O} (hε:0<=e1) (hk:0 < k) (hx:k/2<=x) (hxy:x<=y) : x*qK e1 k x<=y*qK e1 k y:=by
 rw[qL (by linarith:k/5<=x),qL (by linarith:k/5<=y)]
 have h0:0 < x:=by linarith
 have hy_pos:0 < y:=by linarith
 have h8:15/2<=15*x/k:=by rw[div_le_div_iff₀ (by norm_num) hk];linarith
 have hux:2 < log (15*x/k) :=
  qM.trans_le (lLl (by norm_num) h8)
 have huy:log (15*x/k)<=log (15*y/k) :=
  lLl (by positivity) (dLr (by linarith) hk.le)
 have huy2:2 < log (15*y/k):=hux.trans_le huy
 have hsq:log (15*y/k)<=log (15*x/k)*sqrt (y/x):=by
  have h7:15*y/k=(15*x/k)*(y/x):=by field_simp
  rw[h7,log_mul (by positivity) (by positivity)];set t:=sqrt (y/x)
  have ht1:1<=t:=by
   rw[Real.le_sqrt (by norm_num) (by positivity),one_pow];exact (one_le_div h0).mpr hxy
  have h5:t^2=y/x:=sq_sqrt (by positivity)
  have hlog_yx:log (y/x)<=2*(t - 1):=by
   rw[<- h5,lP];push_cast
   have:=Real.log_le_sub_one_of_pos (by linarith:0 < t)
   linarith
  nlinarith
 have h6:(log (15*y/k))^2<=(log (15*x/k))^2*(y/x):=by
  have h1:=pLl (by linarith) hsq 2;rw[mul_pow,sq_sqrt (by positivity)] at h1;exact h1
 have h4:x/(log (15*x/k))^2<=y/(log (15*y/k))^2:=by
  rw[div_le_div_iff₀ (by positivity) (by positivity)];have h2:=mlL h6 h0.le
  have h3:x*((log (15*x/k))^2*(y/x))=y*(log (15*x/k))^2:=by
   field_simp
  linarith
 have hL:x*(e1/(log (15*x/k))^2)=e1*(x/(log (15*x/k))^2):=by ring
 have hR:y*(e1/(log (15*y/k))^2)=e1*(y/(log (15*y/k))^2):=by ring
 rw[hL,hR];exact mlL h4 hε
def qQ {V:Type*} (G:SG V) (S:FS V) (e1 k:O):Prop :=
 ∀ X⊆S,k/2<=(#X:O)->2*#X<=#S ->
  qK e1 k (#X:O)*(#X:O)<=(#(qn G S X):O)
lemma qR {k x y m:O} (hk:0 < k) (hx:k/2<=x)
  (hy0:0<=y) (hm:2*x<=m)
  (hy:y < (1/100:O)/(log (15*x/k))^2*x) :
  let g:O->O:=λ z =>
   if z < k/5 then 1 - 1/(4*log 3)
   else 1 - 1/(4*log (15*z/k))
  g (x+y)*(x+y)+g (m - x)*(m - x)<=g m*m:=by
 intro g
 have h0:0 < x:=by linarith
 have j6:15/2<=15*x/k:=by rw[div_le_div_iff₀ (by norm_num) hk];linarith
 set u:O:=log (15*x/k);have hu2:2 < u:=qM.trans_le (lLl (by norm_num) j6)
 have hy_lt_x4:y < x/4:=by
  have hu4:(4:O) < u^2:=by nlinarith
  have h1:(1/100:O)/u^2 < 1/4:=by rw[div_lt_iff₀ (by positivity)];linarith
  have h2:=mul_lt_mul_of_pos_right h1 h0;linarith
 have h7:1 < log 3:=by
  rw[lIt (by norm_num)];linarith [e1l]
 have h8:g (m - x)<=g m:=by
  have hm_ge:k/5<=m:=by linarith
  dsimp only[g]
  split_ifs with h1 h2 h2
  . exact le_rfl
  .
   have j1:3<=15*m/k:=by rw[lDi hk];linarith
   have j3:log 3<=log (15*m/k):=lLl (by norm_num) j1
   have j4:1/(4*log (15*m/k))<=1/(4*log 3) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
   linarith
  . linarith
  .
   push Not at h1
   have j1:3<=15*(m - x)/k:=by rw[lDi hk];linarith
   have hlog1:1 < log (15*(m - x)/k):=h7.trans_le (lLl (by norm_num) j1)
   have j3:log (15*(m - x)/k)<=log (15*m/k) :=
    lLl (by positivity) (dLr (by linarith) hk.le)
   have j4:1/(4*log (15*m/k))<=1/(4*log (15*(m - x)/k)) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
   linarith
 have hg_xy_le1:g (x+y)<=1:=by
  dsimp only[g];rw[if_neg (not_lt.mpr (by linarith:k/5<=x+y))]
  have j1:3<=15*(x+y)/k:=by rw[lDi hk];linarith
  have:1 < log (15*(x+y)/k):=h7.trans_le (lLl (by norm_num) j1)
  have:0<=1/(4*log (15*(x+y)/k)):=by positivity
  linarith
 have h5:1/(48*u^2)<=g m - g (x+y):=by
  have j0:g (x+y)=1 - 1/(4*log (15*(x+y)/k)):=by
   dsimp only[g];rw[if_neg (not_lt.mpr (by linarith:k/5<=x+y))]
  have j5:g m=1 - 1/(4*log (15*m/k)):=by
   dsimp only[g];rw[if_neg (not_lt.mpr (by linarith:k/5<=m))]
  rw[j0,j5];set t:=log (15*(x+y)/k);set s:=log (15*m/k)
  have h6:u<=t :=
   lLl (by positivity) (dLr (by linarith) hk.le)
  have ht2:2 < t:=hu2.trans_le h6
  have h3:8/5<=m/(x+y):=by
   rw[div_le_div_iff₀ (by norm_num) (by linarith)];linarith
  have hst:t+1/3<=s:=by
   have h9:15*m/k=(15*(x+y)/k)*(m/(x+y)):=by
    have:0 < x+y:=by linarith
    field_simp
   have hs_eq:s=t+log (m/(x+y)):=by
    dsimp only[s,t];rw[h9,log_mul (by positivity) (by positivity)]
   have hlog_ge:1/3 < log (m/(x+y)) :=
    qN.trans_le (lLl (by norm_num) h3)
   linarith
  have hs_pos:0 < s:=by linarith
  have h54:t<=5/4*u:=by
   have hxy_le:(x+y)/x<=5/4:=by rw[div_le_div_iff₀ h0 (by norm_num)];linarith
   have h9:15*(x+y)/k=(15*x/k)*((x+y)/x):=by field_simp
   have ht_eq:t=u+log ((x+y)/x):=by
    dsimp only[t,u];rw[h9,log_mul (by positivity) (by positivity)]
   have hlog_le:log ((x+y)/x)<=1/4:=by
    have h1:=Real.log_le_sub_one_of_pos (by positivity:0 < (x+y)/x);linarith
   linarith
  have h4:1 - 1/(4*s) - (1 - 1/(4*t))=(s - t)/(4*t*s):=by
   field_simp;ring
  rw[h4]
  by_cases j2:2*t<=s
  .
   have h1:1/(8*t)<=(s - t)/(4*t*s):=by
    rw[div_le_div_iff₀ (by positivity) (by positivity)];nlinarith
   have h2:1/(48*u^2)<=1/(8*t):=by
    apply one_div_le_one_div_of_le (by positivity);nlinarith
   exact h2.trans h1
  .
   push Not at j2
   have h1:1/(24*t^2)<=(s - t)/(4*t*s):=by
    rw[div_le_div_iff₀ (by positivity) (by positivity)];nlinarith
   have h2:1/(48*u^2)<=1/(24*t^2):=by
    apply one_div_le_one_div_of_le (by positivity);nlinarith
   exact h2.trans h1
 have hy_small:y < x*(1/(48*u^2)):=by
  have:(1/100:O)/u^2 < 1/(48*u^2):=by
   rw[div_lt_div_iff₀ (by positivity) (by positivity)];nlinarith
  nlinarith
 have h1:g (m - x)*(m - x)<=g m*(m - x):=mlR h8 (by linarith)
 have h2:x*(1/(48*u^2))<=x*(g m - g (x+y)) :=
  mlL h5 h0.le
 nlinarith
lemma qU {V:Type*} (G:SG V) (S0:FS V) {d0 k:O} (k2:0 < d0) (hk:0 < k) (hS0:S0.Nonempty) (jv:d0*(#S0:O)<=∑ u∈S0,(dS G S0 u:O)) : ∃ S⊆S0,S.Nonempty /\ qQ G S (1/100) k /\ (∀ v∈S,d0/4<=(dS G S v:O)):=by
 let g:O->O:=λ x =>
  if x < k/5 then 1 - 1/(4*log 3)
  else 1 - 1/(4*log (15*x/k))
 have jb:1 < log 3:=by
  rw[lIt (by norm_num)];linarith [e1l]
 have h4:∀ x:O,3/4<=g x/\g x<=1:=by
  intro x;dsimp only[g];split_ifs with h
  .
   constructor
   .
    have:1/(4*log 3)<=1/4:=by
     apply one_div_le_one_div_of_le (by norm_num);linarith
    linarith
   .
    have:0<=1/(4*log 3):=by positivity
    linarith
  .
   push Not at h
   have jn:3<=15*x/k:=by rw[lDi hk];linarith
   have jj:1 < log (15*x/k):=jb.trans_le (lLl (by norm_num) jn);constructor
   .
    have:1/(4*log (15*x/k))<=1/4:=by
     apply one_div_le_one_div_of_le (by norm_num);linarith
    linarith
   .
    have:0<=1/(4*log (15*x/k)):=by positivity
    linarith
 have j5:∀ x y:O,x<=y->g x<=g y:=by
  intro x y hxy;dsimp only[g];split_ifs with hx hy hy
  . exact le_rfl
  .
   push Not at hy
   have jn:3<=15*y/k:=by rw[lDi hk];linarith
   have jt:log 3<=log (15*y/k):=lLl (by norm_num) jn
   have ju:1/(4*log (15*y/k))<=1/(4*log 3) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
   linarith
  . linarith
  .
   push Not at hx hy
   have jn:3<=15*x/k:=by rw[lDi hk];linarith
   have jj:1 < log (15*x/k):=jb.trans_le (lLl (by norm_num) jn)
   have jt:log (15*x/k)<=log (15*y/k) :=
    lLl (by positivity) (dLr (by linarith) hk.le)
   have ju:1/(4*log (15*y/k))<=1/(4*log (15*x/k)) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
   linarith
 let h8:FS V->Prop:=λ S =>
  S.Nonempty/\d0*g (#S:O)*(#S:O)<=∑ u∈S,(dS G S u:O)
 have j4:h8 S0:=by
  refine ⟨hS0,?_⟩;have hg1:=(h4 (#S0:O)).2
  calc
   d0*g (#S0:O)*(#S0:O)<=d0*1*(#S0:O):=by gcongr
   _=d0*(#S0:O):=by ring
   _<=∑ u∈S0,(dS G S0 u:O):=jv
 have hne:(S0.powerset.filter h8).Nonempty :=
  ⟨S0,rF ⟨mem_powerset.mpr sR,j4⟩⟩
 obtain ⟨S,j3,h7⟩:=Finset.exists_min_image (S0.powerset.filter h8) Finset.card hne;have j6:S⊆S0:=mem_powerset.mp (pF j3).1;have h3:h8 S:=(pF j3).2;refine ⟨S,j6,h3.1,?_,?_⟩
 .
  intro X jo hXk hX2;by_contra js
  push Not at js
  have h9:(0:O) < (#X:O):=by linarith
  have jm:X.Nonempty:=card_pos.mp (by exact_mod_cast h9)
  have jy:15/2<=15*(#X:O)/k:=by rw[div_le_div_iff₀ (by norm_num) hk];linarith
  have hu2:2 < log (15*(#X:O)/k) :=
   qM.trans_le (lLl (by norm_num) jy)
  rw[qL (by linarith:k/5<=(#X:O))] at js
  have hy_lt_x4:(#(qn G S X):O) < (#X:O)/4:=by
   have hu4:(4:O) < (log (15*(#X:O)/k))^2:=by nlinarith
   have h1:(1/100:O)/(log (15*(#X:O)/k))^2 < 1/4:=by
    rw[div_lt_iff₀ (by positivity)];linarith
   have h2:=mul_lt_mul_of_pos_right h1 h9;linarith
  let S1:FS V:=X∪qn G S X;let S2:FS V:=S \ X;have jx:S1⊆S:=uS jo (qq G S X);have jw:S2⊆S:=sS
  have j9:(#S1:O)=(#X:O)+(#(qn G S X):O):=by
   rw[card_union_of_disjoint (qr G S X)];push_cast;rfl
  have j7:(#S2:O)=(#S:O) - (#X:O):=by
   rw[card_sdiff_of_subset jo,Nat.cast_sub (cL jo)]
  have jr:2*(#X:O)<=(#S:O):=by exact_mod_cast hX2
  have ji:#S1 < #S:=by
   have hR:(#S1:O) < (#S:O):=by linarith
   exact_mod_cast hR
  have jg:#S2 < #S:=by
   have hR:(#S2:O) < (#S:O):=by linarith
   exact_mod_cast hR
  have jh:S1.Nonempty:=jm.mono sUl
  have jf:S2.Nonempty:=card_pos.mp (by
   rw[card_sdiff_of_subset jo];have:=jm.card_pos;omega)
  have ja:∑ w∈S1,(dS G S1 w:O) < d0*g (#S1:O)*(#S1:O):=by
   by_contra jd;push Not at jd
   have j0:S1∈S0.powerset.filter h8 :=
    rF ⟨mem_powerset.mpr (jx.trans j6),jh,jd⟩
   exact absurd (h7 S1 j0) (not_le.mpr ji)
  have j8:∑ w∈S2,(dS G S2 w:O) < d0*g (#S2:O)*(#S2:O):=by
   by_contra jd;push Not at jd
   have j0:S2∈S0.powerset.filter h8 :=
    rF ⟨mem_powerset.mpr (jw.trans j6),jf,jd⟩
   exact absurd (h7 S2 j0) (not_le.mpr jg)
  have h6:∑ w∈S,dS G S w<=∑ w∈S1,dS G S1 w+∑ w∈S2,dS G S2 w:=by
   have h5:∀ T:FS V,∑ w∈T,dS G T w =
     #((T ×ˢ T).filter (λ p=>G.Adj p.1 p.2)):=λ T=>by
    rw[card_filter,Finset.sum_product];refine sum_congr rfl λ w _=>?_
    rw[<- card_filter];rfl
   rw[h5 S,h5 S1,h5 S2]
   have jq:(S ×ˢ S).filter (λ p=>G.Adj p.1 p.2) ⊆
     (S1 ×ˢ S1).filter (λ p=>G.Adj p.1 p.2) ∪
     (S2 ×ˢ S2).filter (λ p=>G.Adj p.1 p.2):=by
    intro p hp;obtain ⟨hpS,j2⟩:=pF hp;obtain ⟨k0,jz⟩:=Finset.mem_product.mp hpS
    by_cases h1:p.1∈X
    .
     refine mUl _ (mem_filter.mpr ⟨mem_product.mpr ⟨mUl _ h1,?_⟩,j2⟩)
     by_cases h2:p.2∈X
     . exact mUl _ h2
     . exact mUr _ ((qo G S X p.2).mpr ⟨jz,h2,p.1,h1,j2⟩)
    .
     by_cases h2:p.2∈X
     . refine mUl _ (mem_filter.mpr ⟨mem_product.mpr ⟨?_,mUl _ h2⟩,j2⟩);exact mUr _ ((qo G S X p.1).mpr ⟨k0,h1,p.2,h2,j2.symm⟩)
     .
      exact mUr _ (mem_filter.mpr ⟨mem_product.mpr
       ⟨rS ⟨k0,h1⟩,rS ⟨jz,h2⟩⟩,j2⟩)
   exact (cL jq).trans (cUl _ _)
  have hedge_R:(∑ w∈S,(dS G S w:O)) <=
    ∑ w∈S1,(dS G S1 w:O)+∑ w∈S2,(dS G S2 w:O):=by exact_mod_cast h6
  have hpot:g (#S:O)*(#S:O) <
    g ((#X:O)+(#(qn G S X):O))*((#X:O)+(#(qn G S X):O)) +
    g ((#S:O) - (#X:O))*((#S:O) - (#X:O)):=by
   rw[j9] at ja;rw[j7] at j8
   have jl:d0*(g (#S:O)*(#S:O)) <
     d0*(g ((#X:O)+(#(qn G S X):O))*((#X:O)+(#(qn G S X):O)) +
      g ((#S:O) - (#X:O))*((#S:O) - (#X:O))):=by linarith [h3.2]
   exact lt_of_mul_lt_mul_left jl k2.le
  have hcontra:=qR hk hXk (nCn _) jr js;linarith
 .
  intro v hv;have jp:=q8 G S hv
  have hcast:(∑ u∈S,(dS G S u:O)) =
    ∑ u∈S.erase v,(dS G (S.erase v) u:O)+2*(dS G S v:O):=by exact_mod_cast jp
  by_cases k1:(S.erase v).Nonempty
  .
   have hlt_er:∑ u∈S.erase v,(dS G (S.erase v) u:O) <
     d0*g (#(S.erase v):O)*(#(S.erase v):O):=by
    by_contra jd;push Not at jd
    have j0:S.erase v∈S0.powerset.filter h8 :=
     rF ⟨mem_powerset.mpr ((Finset.erase_subset v S).trans j6),k1,jd⟩
    have hle:=h7 (S.erase v) j0;rw[card_erase_of_mem hv] at hle;have hpos:0 < #S:=h3.1.card_pos;omega
   have hc:(#(S.erase v):O)=(#S:O) - 1:=by
    rw[card_erase_of_mem hv,Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr h3.1.card_pos.ne')];simp
   have je:g (#(S.erase v):O)<=g (#S:O):=j5 _ _ (by linarith);have jk:3/4<=g (#S:O):=(h4 (#S:O)).1
   have j1:0<=(#S:O) - 1:=by
    have:1<=#S:=h3.1.card_pos
    have:(1:O)<=(#S:O):=by exact_mod_cast this
    linarith
   have h1:d0*g (#(S.erase v):O)*(#(S.erase v):O) <=
     d0*g (#S:O)*((#S:O) - 1):=by
    rw[hc] at je ⊢;exact mlR (mlL je k2.le) j1
   nlinarith [h3.2]
  .
   have he:S.erase v=∅:=not_nonempty_iff_eq_empty.mp k1
   have hS1:S={v}:=by
    have:=insert_erase hv
    rw[he] at this;exact this.symm
   have jc:=h3.2;rw[hS1] at jc
   have h0:dS G {v} v=0:=by
    unfold dS;rw[Finset.filter_singleton,if_neg (G.loopless.irrefl v)];rfl
   rw[Finset.sum_singleton,card_singleton,h0,Nat.cast_zero,Nat.cast_one,mul_one] at jc;have jk:=(h4 1).1;nlinarith
lemma qV {V:Type*} [Fintype V] (G:SG V) (S0:FS V) {d:ℕ} {e2:O} (hd:1<=d) (he2:0 < e2) (hS0:S0.Nonempty) (havg:8*(d:O)*(#S0:O)<=∑ u∈S0,(dS G S0 u:O)) : ∃ (H:SG V) (S:FS V) (h0:V->Bool), H<=G/\S⊆S0/\S.Nonempty /\ qk H h0 /\ qQ H S (1/100) (e2*(d:O)) /\ (∀ v∈S,d<=dS H S v):=by
 obtain ⟨h0,h6⟩:=qh G S0;let B:=bip G h0
 have h3:4*(d:O)*(#S0:O)<=∑ u∈S0,(dS B S0 u:O):=by
  have hsum_le:∑ u∈S0,(dS G S0 u:O)<=2*∑ u∈S0,(dS B S0 u:O):=by
   rw[Finset.mul_sum];refine sum_le_sum λ u hu=>?_
   have h1:dS G S0 u<=2*dS B S0 u:=by rw[qj];exact h6 u hu
   exact_mod_cast h1
  linarith
 have hd_pos:(0:O) < (d:O):=by exact_mod_cast (show 0 < d by omega)
 obtain ⟨S,h8,h7,h4,h5⟩ :=
  qU B S0 (d0:=4*(d:O)) (k:=e2*(d:O)) (by positivity) (by positivity) hS0 h3
 refine ⟨B,S,h0,qi G h0,h8,h7,ql G h0,h4,λ v hv=>?_⟩
 have h1:=h5 v hv
 have h2:(d:O)<=(dS B S v:O):=by linarith
 exact_mod_cast h2
lemma qW {t:O} (ht0:0<=t) (ht1:t<=1) : exp (t/2)<=1+t:=by
 have h1:1 - t/2<=exp (-(t/2)):=by linarith [add_one_le_exp (-(t/2))]
 have h2:(1:O)<=(1+t)*exp (-(t/2)):=by nlinarith
 rwa [Real.exp_neg,<- div_eq_mul_inv,one_le_div (ePp _)] at h2
lemma qX {α:O} (hα:1<=α):(log α)^5<=3125*α:=by
 have hlog_nn:0<=log α:=lNn hα
 have h1:log α/5<=exp (log α/5):=by
  linarith [add_one_le_exp (log α/5)]
 have h2:=pLl (by positivity) h1 5;rw[<- exp_nat_mul] at h2
 have h5:((5:ℕ):O)*(log α/5)=log α:=by norm_num;ring
 rw[h5,exp_log (by linarith:0 < α),div_pow] at h2
 have h55:(5:O)^5=3125:=by norm_num
 rw[h55,dLi (by norm_num:(0:O) < 3125)] at h2;linarith
lemma qY {t:O} (ht0:0<=t) (ht1:t<=1) : exp t - 1<=2*t:=by
 have h0:exp t<=(1 - t)*exp 0+t*exp 1:=by
  have h:=convexOn_exp.2 (Set.mem_univ (0:O)) (Set.mem_univ (1:O)) (by linarith:0<=1 - t) ht0 (by ring);simpa using h
 rw[Real.exp_zero] at h0
 have he:exp 1<=3:=by linarith [e1l]
 nlinarith
lemma qZ {x y:O} (hx:exp 10<=x) (h6:x<=y) : x/(log x)^10<=y/(log y)^10:=by
 have h0:0 < x:=lL2 (ePp 10) hx;have h4:0 < y:=lL2 h0 h6
 have ha:10<=log x:=by
  have:=lLl (ePp 10) hx;rwa [log_exp] at this
 have hlogx_pos:0 < log x:=by linarith
 have hab:log x<=log y:=lLl h0 h6
 have hlogy_pos:0 < log y:=by linarith
 have h5:log y/log x<=exp ((log y - log x)/10):=by
  have h1:log y/log x=1+(log y - log x)/log x:=by
   field_simp;ring
  have h2:(log y - log x)/log x<=(log y - log x)/10 :=
   dLl (by linarith) (by norm_num) ha
  linarith [add_one_le_exp ((log y - log x)/10)]
 have h3:=pLl (by positivity) h5 10;rw[<- exp_nat_mul] at h3
 have h10:((10:ℕ):O)*((log y - log x)/10)=log y - log x:=by
  norm_num;ring
 rw[h10,Real.exp_sub,exp_log h4,exp_log h0,div_pow] at h3;rw[div_le_div_iff₀ (by positivity) (by positivity)] at h3 ⊢;nlinarith
lemma q00 {C α β:O} (hβ:0 < β) : ∀ᶠ x:O in atTop,C*(log x)^α<=x^β:=by
 have hlo:=isLittleO_log_rpow_rpow_atTop α hβ;have hbd:=hlo.bound (show (0:O) < (max |C| 1)⁻¹ by positivity)
 filter_upwards [hbd,eGe (1:O)] with x hx hx1
 rw[Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg (rNn (lNn hx1) _),
  abs_of_nonneg (rNn (by linarith) _)] at hx
 have hC:C<=max |C| 1:=(le_abs_self C).trans (lMl _ _);have h0:0 < max |C| 1:=lL2 (by norm_num) (lMr _ _)
 calc
  C*(log x)^α<=max |C| 1*(log x)^α :=
   mlR hC (rNn (lNn hx1) _)
  _<=max |C| 1*((max |C| 1)⁻¹*x^β):=mlL hx h0.le
  _=x^β:=by field_simp
lemma q01 {C:O} (a:ℕ) {β:O} (hβ:0 < β) : ∀ᶠ x:O in atTop,C*(log x)^a<=x^β:=by
 filter_upwards [q00 (C:=C) (α:=(a:O)) hβ,
  eGe (1:O)] with x hx _
 rwa [rN] at hx
lemma q02 {C:O} (a:ℕ) {β:O} (hβ:0 < β) :
  ∀ᶠ n:O in atTop,C*(log (log n))^a<=(log n)^β :=
 tL.eventually (q01 (C:=C) a hβ)
lemma q03 {C:O} (a:ℕ) {β:O} (hβ:0 < β) : ∀ᶠ n:O in atTop,exp (C*(log (log n))^a)<=n^β:=by
 filter_upwards [q02 (C:=C/β) a (β:=1) (by norm_num),
  eGe (1:O)] with n hn hn1
 rw[r1] at hn;rw[rpow_def_of_pos (by linarith:0 < n)];apply eLe.mpr
 have h1:C*(log (log n))^a<=β*log n:=by
  have:=mlL hn hβ.le
  have heq:β*(C/β*(log (log n))^a)=C*(log (log n))^a:=by field_simp
  linarith
 linarith
lemma q04 {C K:O} : ∀ᶠ n:O in atTop,C*(log n)^K<=exp ((log (log n))^2):=by
 have h2:Filter.Tendsto (λ n:O=>log (log n)) atTop atTop :=
  tL.comp tL
 filter_upwards [h2.eventually_ge_atTop (max (|K| + 2) (log (max C 1)+2)),
  lGe 1] with n hn hln
 set t:=log (log n);have ht1:|K| + 2<=t:=lT (lMl _ _) hn;have ht2:log (max C 1)+2<=t:=lT (lMr _ _) hn
 have h1:0 < t:=by linarith [abs_nonneg K]
 have h3:max C 1*(log n)^K<=exp (t^2):=by
  have h0:max C 1*(log n)^K=exp (log (max C 1)+K*t):=by
   rw[exp_add,exp_log (lL2 (by norm_num) (lMr C 1)),
    rpow_def_of_pos (by linarith:0 < log n)]
   congr 1;dsimp only[t];ring
  rw[h0];apply eLe.mpr;have hKt:K*t <= |K| * t:=mlR (le_abs_self K) h1.le;nlinarith
 have hC:C<=max C 1:=lMl _ _
 calc
  C*(log n)^K<=max C 1*(log n)^K :=
    mlR hC (rNn (by linarith) _)
  _<=exp (t^2):=h3
lemma q05 {V:Type*} (U:FS V) (s:ℕ) : #(U.powerset.filter (λ Z=>#Z<=s))<=(#U+1)^s:=by
 let f:(Fin s->Option U)->FS V:=λ g =>
  (univ:FS (Fin s)).biUnion (λ i =>
   match g i with
   | none=>∅
   | some x=>{x.1})
 have h2:U.powerset.filter (λ Z=>#Z<=s)⊆(univ:FS (Fin s->Option U)).image f:=by
  intro Z hZ;obtain ⟨hZU,hZs⟩:=pF hZ;have h0:Z⊆U:=mem_powerset.mp hZU;let e:Fin #Z ≃ Z:=(Fintype.equivFinOfCardEq (by simp)).symm
  let g:Fin s->Option U:=λ i =>
   if hi:i.val < #Z then some ⟨(e ⟨i.val,hi⟩).1,h0 (e ⟨i.val,hi⟩).2⟩ else none
  refine mem_image.mpr ⟨g,mUv g,?_⟩
  ext v
  simp only[f,mB,mUv,true_and];constructor
  .
   rintro ⟨i,hv⟩;dsimp only[g] at hv
   split_ifs at hv with hi
   . simp only[mSg] at hv;subst hv;exact (e ⟨i.val,hi⟩).2
   . simp at hv
  . intro hv;let h1:=e.symm ⟨v,hv⟩;refine ⟨⟨h1.val,lL2 h1.isLt hZs⟩,?_⟩;dsimp only[g];rw[dif_pos h1.isLt];simp [h1]
 calc
  #(U.powerset.filter (λ Z=>#Z<=s))
   <= #((univ:FS (Fin s->Option U)).image f):=cL h2
  _<=#(univ:FS (Fin s->Option U)):=card_image_le
  _=(#U+1)^s:=by simp [Fintype.card_pi,Fintype.card_option]
def q06 {V:Type*} (H:SG V) (S A Z:FS V) (k:ℕ):Prop :=
 ∀ i:ℕ,1<=i->#(qn H S (qs H (S \ Z) (i - 1) A)∩Z)<=k*i
def q07 {V:Type*} (H:SG V) (S A Y Z:FS V) (k:ℕ):Prop :=
 ∀ i:ℕ,1<=i->#(qn H S (qs H (S \ (Y∪Z)) (i - 1) A)∩Z)<=k*i
lemma q08 {V:Type*} (H:SG V) (S Z:FS V) {B B':FS V} (h0:B⊆B') (h1:Disjoint B' Z) : qn H S B∩Z⊆qn H S B'∩Z:=by
 intro v hv;obtain ⟨hvN,h2⟩:=pI hv;obtain ⟨hvS,_,u,huB,huv⟩:=(qo H S B v).mp hvN
 exact rI ⟨(qo H S B' v).mpr
  ⟨hvS,dR.mp h1 h2,u,h0 huB,huv⟩,h2⟩
lemma q09 {V:Type*} {H:SG V} {S A Y Z:FS V} {k:ℕ} (h:q06 H S A Z k):q07 H S A Y Z k:=by
 intro i hi
 have h3:S \ (Y∪Z)⊆S \ Z:=λ v hv=>by
  obtain ⟨h1,h2⟩:=pS hv;exact rS ⟨h1,λ hz=>h2 (mUr _ hz)⟩
 have h0:Disjoint (qs H (S \ Z) (i - 1) A) Z :=
  rD λ v hv hz=>(pS (qt H (S \ Z) (i - 1) A hv)).2 hz
 exact (cL (q08 H S Z (qw H h3 (i - 1) A) h0)).trans (h i hi)
lemma q0a {V:Type*} (H:SG V) (S A:FS V) (k:ℕ) :
 q06 H S A ∅ k:=λ _ _=>by simp
lemma q0b {e1 e2:O} {k:ℕ}
  (j1:0 < e1) (he11:e1 < 1) (he20:0 < e2) (hk:1<=k) :
  ∃ d0:ℕ,100<=d0/\∀ n d:ℕ,d0<=d->d<=n ->
   let M:O:=18/e1*(log (n:O))^3
   let L:O:=(log (log (n:O)))^5
   (15/e2<=(d:O)) /\
   (4*(k:O)<=e1*e2*(d:O)/(2*(log (15/2))^2)) /\
   ((k:O)*(50000*15/(e2*(d:O)*e1^2))<=1/4) /\
   (2<=log (log (n:O)))/\(4<=M) /\
   (log (15*M^(400*k)/(e2*(d:O))) <=
    (sqrt e1/2)*(log (log (n:O)))^(3/2:O)) /\
   (M^(400*k) < exp ((L - 1)/(2*(log (log (n:O)))^3))) /\
   (4*(k:O)*M^(300*k+1)<=M^(400*k)) /\
   (L<=M/4) /\
   (e1/(4*(log (n:O))^2)<=1) /\
   (1/M<=e1/(log (n:O))^2) /\
   ((n:O)/2 < exp (e1*(M - 1 - L)/(8*(log (n:O))^2))) /\
   (M^(400*k) < (n:O)/2):=by
 have j0:Filter.Tendsto (λ x:O=>log (log x)) atTop atTop :=
  tL.comp tL
 have h1:∀ᶠ x:O in atTop,15/e2<=x:=eGe (15/e2)
 have h2:∀ᶠ x:O in atTop,4*(k:O)<=e1*e2*x/(2*(log (15/2))^2):=by
  filter_upwards [eGe (4*(k:O)*(2*(log (15/2))^2)/(e1*e2))] with x hx
  rw[lDi (by have:=qM;positivity)]
  have:=mlL hx (by positivity:(0:O)<=e1*e2)
  have j7:e1*e2*(4*(k:O)*(2*(log (15/2))^2)/(e1*e2)) =
    4*(k:O)*(2*(log (15/2))^2):=by field_simp
  linarith
 have h3:∀ᶠ x:O in atTop,(k:O)*(50000*15/(e2*x*e1^2))<=1/4:=by
  filter_upwards [eGe (4*(k:O)*50000*15/(e2*e1^2)+1)] with x hx
  have hxpos:0 < x:=lL2 (by positivity) hx;rw[mul_div_assoc',div_le_div_iff₀ (by positivity) (by norm_num)]
  have:=mlL hx (by positivity:(0:O)<=e2*e1^2)
  have j7:e2*e1^2*(4*(k:O)*50000*15/(e2*e1^2)+1) =
    4*(k:O)*50000*15+e2*e1^2:=by field_simp
  nlinarith
 have h4:∀ᶠ x:O in atTop,2<=log (log x)/\4<=18/e1*(log x)^3:=by
  filter_upwards [j0.eventually_ge_atTop 2,lGe 2] with x hll hl
  refine ⟨hll,?_⟩
  have:18<=18/e1:=by rw[lDi j1];linarith
  have hl3:(8:O)<=(log x)^3:=by
   calc
    (8:O)=2^3:=by norm_num
    _<=(log x)^3:=pLl (by norm_num) hl 3
  nlinarith
 have h5:∀ᶠ x:O in atTop,
   log (15*(18/e1*(log x)^3)^(400*k)/(e2*1)) <=
    (sqrt e1/2)*(log (log x))^(3/2:O):=by
  let h0:O:=max (log (15/e2*(18/e1)^(400*k))) 0+1200*(k:O)+1
  filter_upwards [j0.eventually_ge_atTop (max 4 ((2*max h0 1/sqrt e1)^2+1)),
   lGe 2] with x hll hl
  set t:=log (log x);have ht4:4<=t:=lT (lMl _ _) hll
  have j4:15*(18/e1*(log x)^3)^(400*k)/(e2*1) =
    (15/e2*(18/e1)^(400*k))*(log x)^(1200*k):=by
   rw[mul_pow,<- pow_mul,mul_one];ring
  rw[j4,log_mul (by positivity) (by positivity),lP]
  have hlhs_le:log (15/e2*(18/e1)^(400*k))+((1200*k:ℕ):O)*t<=max h0 1*t:=by
   have hlm:log (15/e2*(18/e1)^(400*k))<=max (log (15/e2*(18/e1)^(400*k))) 0 :=
    lMl _ _
   have hlm0:0<=max (log (15/e2*(18/e1)^(400*k))) 0:=lMr _ _
   have:log (15/e2*(18/e1)^(400*k))+((1200*k:ℕ):O)*t<=h0*t:=by
    push_cast;dsimp only[h0];nlinarith
   exact this.trans (mlR (lMl _ _) (by linarith))
  have hsq:2*max h0 1/sqrt e1<=sqrt t:=by
   rw[Real.le_sqrt (by positivity) (by linarith)];linarith [lMr (4:O) ((2*max h0 1/sqrt e1)^2+1)]
  have j5:t^(3/2:O)=t*sqrt t:=by
   rw[Real.sqrt_eq_rpow,<- Real.rpow_one_add' (by linarith) (by norm_num)];norm_num
  rw[j5];have jc:=mlL hsq (show (0:O)<=sqrt e1/2*t by positivity)
  have j7:sqrt e1/2*t*(2*max h0 1/sqrt e1)=max h0 1*t:=by
   have:sqrt e1≠0:=(Real.sqrt_pos.mpr j1).ne'
   field_simp
  linarith
 have h6:∀ᶠ x:O in atTop,
   (18/e1*(log x)^3)^(400*k) <
    exp (((log (log x))^5 - 1)/(2*(log (log x))^3)):=by
  let C0:=(18/e1)^(400*k)
  filter_upwards [j0.eventually_ge_atTop (max 4 (4*(log (max C0 1)+1200*(k:O)+4))),
   lGe 2] with x hll hl
  set t:=log (log x);have ht4:4<=t:=lT (lMl _ _) hll;have ht_big:4*(log (max C0 1)+1200*(k:O)+4)<=t:=lT (lMr _ _) hll
  have jd:(18/e1*(log x)^3)^(400*k) <=
    exp (log (max C0 1)+1200*(k:O)*t):=by
   rw[mul_pow,<- pow_mul]
   calc
    (18/e1)^(400*k)*(log x)^(3*(400*k))
     <= max C0 1*(log x)^(3*(400*k)) :=
      mlR (lMl _ _) (by positivity)
    _=exp (log (max C0 1)+1200*(k:O)*t):=by
      rw[exp_add,exp_log (lL2 (by norm_num) (lMr C0 1))];congr 1
      rw[show (3*(400*k):ℕ)=1200*k by ring,<- rN,
       rpow_def_of_pos (by linarith:0 < log x)]
      push_cast;dsimp only[t];ring_nf
  refine lL3 jd (exp_lt_exp.mpr ?_);rw[lt_div_iff₀ (by positivity)];have hlc:0<=log (max C0 1):=lNn (lMr _ _)
  have ht1:log (max C0 1)+1200*(k:O)*t<=(log (max C0 1)+1200*(k:O))*t:=by nlinarith
  have j6:2*(log (max C0 1)+1200*(k:O))+8<=t/2:=by linarith
  have ht4_pos:1<=t^4:=oLp (by linarith)
  have ht3_eq:t*(2*t^3)=2*t^4:=by ring
  have ht5_eq:t*t^4=t^5:=by ring
  have h1:(log (max C0 1)+1200*(k:O)*t)*(2*t^3) <=
    2*(log (max C0 1)+1200*(k:O))*t^4:=by
   have:=mlR ht1 (show (0:O)<=2*t^3 by positivity)
   linarith [show (log (max C0 1)+1200*(k:O))*t*(2*t^3) =
     2*(log (max C0 1)+1200*(k:O))*t^4 by ring]
  have h2:(2*(log (max C0 1)+1200*(k:O))+8)*t^4<=(t/2)*t^4 :=
   mlR j6 (by positivity)
  have ht5_nn:0<=t^5:=by positivity
  linarith [show (t/2)*t^4=t^5/2 by ring,show (1:O) < 8*t^4 by linarith]
 have h7:∀ᶠ x:O in atTop,
   4*(k:O)*(18/e1*(log x)^3)^(300*k+1)<=(18/e1*(log x)^3)^(400*k):=by
  filter_upwards [lGe (4*(k:O)+2)] with x hl
  set M:=18/e1*(log x)^3
  have j9:4*(k:O)<=M:=by
   have:18<=18/e1:=by rw[lDi j1];linarith
   have h1:1<=log x:=by linarith [show (0:O)<=(k:O) by positivity]
   have h2:4*(k:O)<=(log x)^3:=by
    calc
     4*(k:O)<=log x:=by linarith
     _<=log x*(log x)^2:=by nlinarith
     _=(log x)^3:=by ring
   nlinarith
  have hM1:1<=M:=by
   have hk1:(1:O)<=(k:O):=by exact_mod_cast hk
   linarith
  calc
   4*(k:O)*M^(300*k+1)<=M*M^(300*k+1):=mlR j9 (by positivity)
   _=M^(300*k+2):=by rw[<- pow_succ']
   _<=M^(400*k):=pLr hM1 (by omega)
 have h8:∀ᶠ x:O in atTop,
   (log (log x))^5<=18/e1*(log x)^3/4 /\
   e1/(4*(log x)^2)<=1 /\
   1/(18/e1*(log x)^3)<=e1/(log x)^2 /\
   x/2 < exp (e1*(18/e1*(log x)^3 - 1 - (log (log x))^5)/(8*(log x)^2)):=by
  filter_upwards [q02 (C:=1) 5 (β:=3) (by norm_num),
   lGe 4,eGe (2:O)] with x hn hl hx2
  rw[one_mul,Real.rpow_ofNat] at hn
  have h18:18<=18/e1:=by rw[lDi j1];linarith
  have hL:(log (log x))^5<=18/e1*(log x)^3/4:=by
   have:4<=18/e1/4:=by linarith
   nlinarith [show (0:O)<=(log x)^3 by positivity]
  refine ⟨hL,?_,?_,?_⟩
  . rw[div_le_one (by positivity)];nlinarith
  .
   rw[div_le_div_iff₀ (by positivity) (by positivity)]
   have:18/e1*(log x)^3*e1=18*(log x)^3:=by field_simp
   nlinarith
  .
   have hl64:(64:O)<=(log x)^3:=by
    calc
     (64:O)=4^3:=by norm_num
     _<=(log x)^3:=pLl (by norm_num) hl 3
   have h4:1<=18/e1*(log x)^3/4:=by nlinarith
   have jb:9/e1*(log x)^3<=18/e1*(log x)^3 - 1 - (log (log x))^5:=by
    have:9/e1*(log x)^3=18/e1*(log x)^3 - 18/e1*(log x)^3/4 -
      18/e1*(log x)^3/4:=by ring
    linarith
   have j3:log x <=
     e1*(18/e1*(log x)^3 - 1 - (log (log x))^5)/(8*(log x)^2):=by
    rw[lDi (by positivity)];have jc:=mlL jb j1.le
    have j7:e1*(9/e1*(log x)^3)=9*(log x)^3:=by field_simp
    nlinarith [show (0:O)<=(log x)^3 by positivity]
   calc
    x/2 < x:=by linarith
    _=exp (log x):=(exp_log (by linarith)).symm
    _<=_:=eLe.mpr j3
 have h9:∀ᶠ x:O in atTop,(18/e1*(log x)^3)^(400*k) < x/2:=by
  filter_upwards [q01 (C:=3*(18/e1)^(400*k)) (1200*k) (β:=1) (by norm_num),
   lGe 2,eGe (2:O)] with x hx hl hx2
  rw[r1] at hx
  have j7:(18/e1*(log x)^3)^(400*k) =
    (18/e1)^(400*k)*(log x)^(1200*k):=by
   rw[mul_pow,<- pow_mul];congr 2;ring
  rw[j7]
  have hpos:0 < (18/e1)^(400*k)*(log x)^(1200*k):=by positivity
  linarith
 have j8:=(eGe (100:O)).and
  (h1.and (h2.and (h3.and (h4.and (h5.and (h6.and (h7.and (h8.and h9))))))))
 rw[eAt] at j8;obtain ⟨B,hB⟩:=j8;refine ⟨max 100 (ceil B),lMl _ _,λ n d hd hdn=>?_⟩
 have je:B<=(d:O):=(nLc B).trans (by exact_mod_cast (lMr 100 (ceil B)).trans hd);have hnR:B<=(n:O):=je.trans (by exact_mod_cast hdn);have ja:=hB (d:O) je;have j2:=hB (n:O) hnR
 have hd1:(1:O)<=(d:O):=by have:=ja.1;linarith
 refine ⟨ja.2.1,ja.2.2.1,ja.2.2.2.1,j2.2.2.2.2.1.1,j2.2.2.2.2.1.2,?_,
  j2.2.2.2.2.2.2.1,j2.2.2.2.2.2.2.2.1,j2.2.2.2.2.2.2.2.2.1.1,
  j2.2.2.2.2.2.2.2.2.1.2.1,j2.2.2.2.2.2.2.2.2.1.2.2.1,j2.2.2.2.2.2.2.2.2.1.2.2.2,
  j2.2.2.2.2.2.2.2.2.2⟩
 have hMpos:0 < 18/e1*(log (n:O))^3:=by linarith [j2.2.2.2.2.1.2]
 refine (lLl (by positivity) ?_).trans j2.2.2.2.2.2.1;exact dLl (by positivity) (by positivity) (by nlinarith)
lemma q0c {e1 e2 d b r:O} (h8:0 < e1) (he11:e1 < 1) (he20:0 < e2) (hd:0 < d) (hr:1<=r) (hb:e2*d/2<=b) (h2:(1+qK e1 (e2*d) b/4)^r<=b/(e2*d/2)) : r+1<=(50000*15/(e2*d*e1^2))*(b*qK e1 (e2*d) b):=by
 have h0:0 < e2*d:=by positivity
 set α:=15*b/(e2*d)
 have hα:15/2<=α:=by rw[div_le_div_iff₀ (by norm_num) h0];linarith
 have hα1:1<=α:=by linarith
 have hα_pos:0 < α:=by linarith
 have hlog2:2 < log α:=qM.trans_le (lLl (by norm_num) hα)
 have hlog_pos:0 < log α:=by linarith
 have hks:qK e1 (e2*d) b=e1/(log α)^2 :=
  qL (by linarith:e2*d/5<=b)
 rw[hks] at h2 ⊢
 have ht0:0<=e1/(4*(log α)^2):=by positivity
 have ht1:e1/(4*(log α)^2)<=1:=by
  rw[div_le_one (by positivity)];nlinarith
 have h5:exp (e1/(8*(log α)^2))<=1+e1/(log α)^2/4:=by
  have h:=qW ht0 ht1
  have h7:e1/(4*(log α)^2)/2=e1/(8*(log α)^2):=by ring
  have h6:e1/(4*(log α)^2)=e1/(log α)^2/4:=by ring
  rwa [h7,h6] at h
 have h3:exp (r*(e1/(8*(log α)^2)))<=α:=by
  have h1:(exp (e1/(8*(log α)^2)))^r<=(1+e1/(log α)^2/4)^r :=
   rLl (ePp _).le h5 (by linarith)
  rw[<- Real.exp_mul,mul_comm] at h1
  have hba:b/(e2*d/2)<=α:=by
   dsimp only[α];rw[div_le_div_iff₀ (by positivity) h0];nlinarith
  exact h1.trans (h2.trans hba)
 have h4:r*(e1/(8*(log α)^2))<=log α:=by
  have:=lLl (ePp _) h3
  rwa [log_exp] at this
 have hr_ub:r<=8*(log α)^3/e1:=by
  rw[lDi h8]
  have:=mlR h4 (show (0:O)<=8*(log α)^2 by positivity)
  have heq:r*(e1/(8*(log α)^2))*(8*(log α)^2)=r*e1:=by field_simp
  linarith [show log α*(8*(log α)^2)=8*(log α)^3 by ring]
 have hlog5:(log α)^5<=3125*α:=qX hα1
 have hr1:r+1<=2*r:=by linarith
 have hstep1:2*r<=16*(log α)^5/(e1*(log α)^2):=by
  have:16*(log α)^5/(e1*(log α)^2)=2*(8*(log α)^3/e1):=by
   field_simp;ring
  linarith
 have hstep2:16*(log α)^5/(e1*(log α)^2)<=50000*α/(e1*(log α)^2):=by
  apply dLr _ (by positivity);linarith
 have hstep3:50000*α/(e1*(log α)^2) =
   (50000*15/(e2*d*e1^2))*(b*(e1/(log α)^2)):=by
  dsimp only[α];field_simp
 linarith
lemma q0d {V:Type*} {e1 e2:O} {k:ℕ} (j5:0 < e1) (k9:e1 < 1) (jw:0 < e2) (_hk:1<=k) (H:SG V) (S A X Y Z:FS V) (d:ℕ) (hd:100<=d) (k8:qQ H S e1 (e2*(d:O))) (hAS:A⊆S) (hXS:X⊆S \ A) (hZS:Z⊆S \ A) (h7:e2*(d:O)/2<=(#A:O)) (hXcard:(#X:O)<=(#A:O)*qK e1 (e2*(d:O)) (#A:O)/4) (jl:Disjoint (qs H (S \ (X∪Z)) (floor ((log (log (#S:O)))^5)) A) Y) (kb:q07 H S A Y Z k) (ke:15/e2<=(d:O)) (h4k:4*(k:O)<=e1*e2*(d:O)/(2*(log (15/2))^2)) (kd:(k:O)*(50000*15/(e2*(d:O)*e1^2))<=1/4) (k5:2<=log (log (#S:O))) (jt:log (15*(18/e1*(log (#S:O))^3)^(400*k)/(e2*(d:O))) <= (sqrt e1/2)*(log (log (#S:O)))^(3/2:O)) (hM_exp:(18/e1*(log (#S:O))^3)^(400*k) < exp (((log (log (#S:O)))^5 - 1)/(2*(log (log (#S:O)))^3))) (hMn2:(18/e1*(log (#S:O))^3)^(400*k) < (#S:O)/2) : (18/e1*(log (#S:O))^3)^(400*k) < (#(qs H (S \ (X∪Y∪Z)) (floor ((log (log (#S:O)))^5)) A):O):=by
 set n:O:=(#S:O);set M:O:=18/e1*(log n)^3;set L:O:=(log (log n))^5;set l0:=floor L
 have jj:(0:O) < (d:O):=by exact_mod_cast (show 0 < d by omega)
 have h5:0 < e2*(d:O):=by positivity
 have hA1:(1:O)<=(#A:O):=by
  have:15<=e2*(d:O):=by rw[dLi jw] at ke;linarith
  linarith
 have jz:S \ (X∪Y∪Z)=(S \ (X∪Z)) \ Y:=by
  ext v;simp only[mS,mU];tauto
 have h6:∀ r ≤ l0,qs H (S \ (X∪Y∪Z)) r A=qs H (S \ (X∪Z)) r A:=λ r hr=>by
  rw[jz];exact qC H (S \ (X∪Z)) Y A r (jl.mono_left (qu H _ hr A))
 rw[h6 l0 le_rfl];by_contra k6
 push Not at k6
 let F:FS V:=S \ (X∪Z)
 have kc:A⊆F:=λ v hv=>rS ⟨hAS hv,λ h=>by
  rcases pU h with hx | hz
  . exact (pS (hXS hx)).2 hv
  . exact (pS (hZS hz)).2 hv⟩
 have j0:S \ (X∪Y∪Z)⊆S \ (Y∪Z):=λ v hv=>by
  obtain ⟨h1,h2⟩:=pS hv;refine rS ⟨h1,λ h=>h2 ?_⟩
  rcases pU h with hy | hz
  . exact mUl _ (mUr _ hy)
  . exact mUr _ hz
 have h4:∀ r,A⊆qs H F r A:=λ r=>by
  have h0:qs H F 0 A=A:=inter_eq_left.mpr kc
  calc
   A=qs H F 0 A:=h0.symm
   _⊆qs H F r A:=qu H F (Nat.zero_le r) A
 have jp:∀ r ≤ l0,
   (#(qs H F r A):O)*qK e1 (e2*(d:O)) (#(qs H F r A):O) <=
    (#(qn H S (qs H F r A)):O):=λ r hr=>by
  rw[mul_comm];apply k8 (qs H F r A) ((qt H F r A).trans sS)
  .
   have jh:(#A:O)<=(#(qs H F r A):O):=by
    exact_mod_cast cL (h4 r)
   exact h7.trans jh
  .
   have hr_le:(#(qs H F r A):O)<=(#(qs H F l0 A):O):=by
    exact_mod_cast cL (qu H F hr A)
   have hR:((2*#(qs H F r A):ℕ):O)<=(#S:O):=by
    push_cast;dsimp only[n] at *;linarith
   exact_mod_cast hR
 have j2:∀ r ≤ l0,#(qn H S (qs H F r A)) <=
   #(qn H F (qs H F r A))+#X+k*(r+1):=λ r hr=>by
  have k3:qn H S (qs H F r A) ⊆
    qn H F (qs H F r A)∪X∪(qn H S (qs H F r A)∩Z):=by
   intro v hv;obtain ⟨hvS,jq,u,hu,huv⟩:=(qo H S _ v).mp hv
   by_cases kf:v∈F
   . exact mUl _ (mUl _ ((qo H F _ v).mpr ⟨kf,jq,u,hu,huv⟩))
   .
    have k2:v∈X∪Z:=by
     by_contra h;exact kf (rS ⟨hvS,h⟩)
    rcases pU k2 with hx | hz
    . exact mUl _ (mUr _ hx)
    . exact mUr _ (rI ⟨hv,hz⟩)
  have hZbd:#(qn H S (qs H F r A)∩Z)<=k*(r+1):=by
   have jo:qs H F r A⊆qs H (S \ (Y∪Z)) r A:=by
    rw[<- h6 r hr];exact qw H j0 r A
   have jx:Disjoint (qs H (S \ (Y∪Z)) r A) Z :=
    rD λ v hv hz =>
     (pS (qt H (S \ (Y∪Z)) r A hv)).2 (mUr _ hz)
   have js:=q08 H S Z jo jx;have kg:=kb (r+1) (by omega);simp only[Nat.add_sub_cancel] at kg;exact (cL js).trans kg
  calc
   #(qn H S (qs H F r A))
    <= #(qn H F (qs H F r A)∪X∪(qn H S (qs H F r A)∩Z)):=cL k3
   _<=#(qn H F (qs H F r A)∪X)+#(qn H S (qs H F r A)∩Z):=cUl _ _
   _<=#(qn H F (qs H F r A))+#X+#(qn H S (qs H F r A)∩Z):=by
     linarith [cUl (qn H F (qs H F r A)) X]
   _<=_:=by omega
 have jk:∀ r,r < l0 ->
   (1/4:O)*(#(qs H F r A):O)*qK e1 (e2*(d:O)) (#(qs H F r A):O) <=
    (#(qn H F (qs H F r A)):O):=by
  intro r
  induction r using Nat.strong_induction_on with
  | _ r ih =>
   intro hr
   have h9:(#A:O)<=(#(qs H F r A):O):=by
    exact_mod_cast cL (h4 r)
   have h8:e2*(d:O)/2<=(#(qs H F r A):O):=h7.trans h9
   have hX_le:(#X:O) <=
     (#(qs H F r A):O)*qK e1 (e2*(d:O)) (#(qs H F r A):O)/4:=by
    have hm:=qP j5.le h5 h7 h9;linarith
   have hZ_le:(k:O)*((r+1:ℕ):O) <=
     (#(qs H F r A):O)*qK e1 (e2*(d:O)) (#(qs H F r A):O)/4:=by
    rcases Nat.eq_zero_or_pos r with rfl | jr
    .
     simp only[zero_add,Nat.cast_one,mul_one];have hm:=qP j5.le h5 (le_refl (e2*(d:O)/2)) h8
     have ja:qK e1 (e2*(d:O)) (e2*(d:O)/2)=e1/(log (15/2))^2:=by
      rw[qL (by linarith:e2*(d:O)/5<=e2*(d:O)/2)];congr 2;field_simp
     rw[ja] at hm
     have heq:e2*(d:O)/2*(e1/(log (15/2))^2) =
       e1*e2*(d:O)/(2*(log (15/2))^2):=by ring
     linarith
    .
     have j3:∀ j ≤ r,
       (#A:O)*(1+qK e1 (e2*(d:O)) (#(qs H F r A):O)/4)^j <=
        (#(qs H F j A):O):=by
      intro j
      induction j with
      | zero =>
       intro _;dsimp only[qs];rw[pow_zero,mul_one,inter_eq_left.mpr kc]
      | succ j ihj =>
       intro hjr
       have k7:j < r:=by omega
       have hstep:=ih j k7 (by omega)
       have jd:(#A:O)<=(#(qs H F j A):O):=by
        exact_mod_cast cL (h4 j)
       have j7:(#(qs H F j A):O)<=(#(qs H F r A):O):=by
        exact_mod_cast cL (qu H F (by omega) A)
       have jb:=qO j5.le h5 (by linarith:e2*(d:O)/5<=(#(qs H F j A):O)) j7
       have jg:(#(qs H F (j+1) A):O) =
         (#(qs H F j A):O)+(#(qn H F (qs H F j A)):O):=by
        exact_mod_cast qx H F j A
       have h1:(#(qs H F j A):O) *
         (1+qK e1 (e2*(d:O)) (#(qs H F r A):O)/4) <=
         (#(qs H F (j+1) A):O):=by
        have k4:=mlL jb (nCn #(qs H F j A));linarith
       have j9:0<=qK e1 (e2*(d:O)) (#(qs H F r A):O):=by
        rw[qL (by linarith:e2*(d:O)/5<=(#(qs H F r A):O))];positivity
       calc
        (#A:O)*(1+qK e1 (e2*(d:O)) (#(qs H F r A):O)/4)^(j+1)
         = (#A:O)*(1+qK e1 (e2*(d:O)) (#(qs H F r A):O)/4)^j *
           (1+qK e1 (e2*(d:O)) (#(qs H F r A):O)/4):=by rw[pow_succ];ring
        _<=(#(qs H F j A):O) *
           (1+qK e1 (e2*(d:O)) (#(qs H F r A):O)/4) :=
          mlR (ihj (by omega)) (by linarith)
        _<=(#(qs H F (j+1) A):O):=h1
     have hgr:=j3 r le_rfl
     have jc:(1+qK e1 (e2*(d:O)) (#(qs H F r A):O)/4)^(r:O) <=
       (#(qs H F r A):O)/(e2*(d:O)/2):=by
      rw[rN,lDi (by positivity)]
      have k1:(0:O) < (#A:O):=by linarith
      have h1:(1+qK e1 (e2*(d:O)) (#(qs H F r A):O)/4)^r <=
        (#(qs H F r A):O)/(#A:O):=by
       rw[lDi k1];linarith
      have h2:(#(qs H F r A):O)/(#A:O) <=
        (#(qs H F r A):O)/(e2*(d:O)/2) :=
       dLl (nCn _) (by positivity) h7
      have h3:=h1.trans h2
      rwa [lDi (by positivity)] at h3
     have hr1:(1:O)<=(r:O):=by exact_mod_cast jr
     have jy:=q0c j5 k9 jw jj hr1 h8 jc
     have j9:0<=(#(qs H F r A):O)*qK e1 (e2*(d:O)) (#(qs H F r A):O):=by
      rw[qL (by linarith:e2*(d:O)/5<=(#(qs H F r A):O))];positivity
     calc
      (k:O)*((r+1:ℕ):O)
       = (k:O)*((r:O)+1):=by push_cast;rfl
      _<=(k:O)*((50000*15/(e2*(d:O)*e1^2)) *
         ((#(qs H F r A):O)*qK e1 (e2*(d:O)) (#(qs H F r A):O))) :=
        mlL jy (nCn k)
      _=((k:O)*(50000*15/(e2*(d:O)*e1^2))) *
         ((#(qs H F r A):O)*qK e1 (e2*(d:O)) (#(qs H F r A):O)):=by ring
      _<=(1/4:O) *
         ((#(qs H F r A):O)*qK e1 (e2*(d:O)) (#(qs H F r A):O)) :=
        mlR kd j9
      _=_:=by ring
   have hnbR:(#(qn H S (qs H F r A)):O) <=
     (#(qn H F (qs H F r A)):O)+(#X:O)+(k:O)*((r+1:ℕ):O):=by
    exact_mod_cast j2 r (by omega)
   have hexpR:=jp r (by omega);linarith
 have je:(#A:O)<=(#(qs H F l0 A):O):=by
  exact_mod_cast cL (h4 l0)
 have hM_ge_kd:e2*(d:O)/2<=M^(400*k):=h7.trans (je.trans k6)
 have ju:4/(log (log n))^3<=qK e1 (e2*(d:O)) (M^(400*k)):=by
  rw[qL (by linarith:e2*(d:O)/5<=M^(400*k))]
  have ka:15/2<=15*M^(400*k)/(e2*(d:O)):=by
   rw[div_le_div_iff₀ (by norm_num) h5];linarith
  have j8:0 < log (15*M^(400*k)/(e2*(d:O))) :=
   lt_trans (by norm_num) (qM.trans_le (lLl (by norm_num) ka))
  have hsq:(log (15*M^(400*k)/(e2*(d:O))))^2 <=
    (e1/4)*(log (log n))^3:=by
   have h1:=pLl j8.le jt 2
   have hrhs:((sqrt e1/2)*(log (log n))^(3/2:O))^2 =
     (e1/4)*(log (log n))^3:=by
    rw[mul_pow,div_pow,sq_sqrt j5.le,
     <- rN ((log (log n))^(3/2:O)) 2,
     <- rpow_mul (by linarith:0<=log (log n))]
    norm_num
   linarith
  rw[div_le_div_iff₀ (by positivity) (by positivity)];linarith
 have j1:∀ j ≤ l0,
   (#A:O)*(exp (1/(2*(log (log n))^3)))^j <=
    (#(qs H F j A):O):=by
  intro j
  induction j with
  | zero =>
   intro _;dsimp only[qs];rw[pow_zero,mul_one,inter_eq_left.mpr kc]
  | succ j ihj =>
   intro hj;have hcl:=jk j (by omega)
   have jd:(#A:O)<=(#(qs H F j A):O):=by
    exact_mod_cast cL (h4 j)
   have j6:(#(qs H F j A):O)<=(#(qs H F l0 A):O):=by
    exact_mod_cast cL (qu H F (by omega) A)
   have jn:e2*(d:O)/5<=(#(qs H F j A):O):=by linarith
   have jm:(#(qs H F j A):O)<=M^(400*k):=j6.trans k6
   have ji:4/(log (log n))^3<=qK e1 (e2*(d:O)) (#(qs H F j A):O) :=
    ju.trans (qO j5.le h5 jn jm)
   have j4:exp (1/(2*(log (log n))^3)) <=
     1+1/(log (log n))^3:=by
    have ht1:1/(log (log n))^3<=1:=by
     rw[div_le_one (by positivity)]
     calc
      (1:O)<=2^3:=by norm_num
      _<=(log (log n))^3:=pLl (by norm_num) k5 3
    have h:=qW (by positivity) ht1
    rwa [show 1/(log (log n))^3/2=1/(2*(log (log n))^3) by ring] at h
   have jg:(#(qs H F (j+1) A):O) =
     (#(qs H F j A):O)+(#(qn H F (qs H F j A)):O):=by
    exact_mod_cast qx H F j A
   have h1:(#(qs H F j A):O)*(1+1/(log (log n))^3) <=
     (#(qs H F (j+1) A):O):=by
    have k4:=mlL ji (nCn #(qs H F j A))
    have hq:(1/4:O)*(#(qs H F j A):O)*(4/(log (log n))^3) =
      (#(qs H F j A):O)*(1/(log (log n))^3):=by ring
    linarith
   calc
    (#A:O)*(exp (1/(2*(log (log n))^3)))^(j+1)
     = (#A:O)*(exp (1/(2*(log (log n))^3)))^j *
       exp (1/(2*(log (log n))^3)):=by rw[pow_succ];ring
    _<=(#(qs H F j A):O)*exp (1/(2*(log (log n))^3)) :=
      mlR (ihj (by omega)) (ePp _).le
    _<=(#(qs H F j A):O)*(1+1/(log (log n))^3) :=
      mlL j4 (nCn _)
    _<=(#(qs H F (j+1) A):O):=h1
 have jv:=j1 l0 le_rfl;rw[<- exp_nat_mul] at jv
 have k0:L - 1<=(l0:O):=by linarith [nL1 L]
 have jf:exp ((L - 1)/(2*(log (log n))^3)) <=
   exp ((l0:O)*(1/(2*(log (log n))^3))):=by
  apply eLe.mpr;rw[mul_one_div];exact dLr k0 (by positivity)
 have hfin2:exp ((L - 1)/(2*(log (log n))^3))<=(#(qs H F l0 A):O):=by
  calc
   exp ((L - 1)/(2*(log (log n))^3))
    <= 1*exp ((l0:O)*(1/(2*(log (log n))^3))):=by rw[one_mul];exact jf
   _<=(#A:O)*exp ((l0:O)*(1/(2*(log (log n))^3))) :=
     mlR hA1 (ePp _).le
   _<=(#(qs H F l0 A):O):=jv
 linarith
lemma q0e {V:Type*} {e1 e2:O} {k:ℕ} (jl:0 < e1) (jr:0 < e2) (hk:1<=k) (H:SG V) (S A X Y Z:FS V) (d:ℕ) (hd:100<=d) (hdn:d<=#S) (jq:qQ H S e1 (e2*(d:O))) (hAS:A⊆S) (hXS:X⊆S \ A) (hYS:Y⊆S \ A) (hZS:Z⊆S \ A) (j8:e2*(d:O)/2<=(#A:O)) (hXcard:(#X:O)<=(#A:O)*qK e1 (e2*(d:O)) (#A:O)/4) (hYcard:(#Y:O)<=(18/e1*(log (#S:O))^3)^(300*k)) (js:q07 H S A Y Z k) (ju:15/e2<=(d:O)) (hll2:2<=log (log (#S:O))) (hM4:4<=18/e1*(log (#S:O))^3) (h4kM:4*(k:O)*(18/e1*(log (#S:O))^3)^(300*k+1) <= (18/e1*(log (#S:O))^3)^(400*k)) (hLM4:(log (log (#S:O)))^5<=18/e1*(log (#S:O))^3/4) (he1:e1/(4*(log (#S:O))^2)<=1) (h1M:1/(18/e1*(log (#S:O))^3)<=e1/(log (#S:O))^2) (je:(#S:O)/2 < exp (e1*(18/e1*(log (#S:O))^3 - 1 - (log (log (#S:O)))^5)/(8*(log (#S:O))^2))) (jd:(18/e1*(log (#S:O))^3)^(400*k) < (#(qs H (S \ (X∪Y∪Z)) (floor ((log (log (#S:O)))^5)) A):O)) : #S < 2*#(qs H (S \ (X∪Y∪Z)) (floor (18/e1*(log (#S:O))^3)) A):=by
 set n:O:=(#S:O);set M:O:=18/e1*(log n)^3;set L:O:=(log (log n))^5;set m:=floor M;set l0:=floor L
 have hd_pos:(0:O) < (d:O):=by exact_mod_cast (show 0 < d by omega)
 have h5:0 < e2*(d:O):=by positivity
 have hlogn_pos:0 < log n:=by
  have hn100:(100:O)<=n:=by dsimp only[n];exact_mod_cast (show 100<=#S by omega)
  exact lPs (by linarith)
 by_contra j2
 push Not at j2
 let F':FS V:=S \ (X∪Y∪Z)
 have jt:A⊆F':=λ v hv=>rS ⟨hAS hv,λ h=>by
  rcases pU h with jo | hz
  .
   rcases pU jo with hx | hy
   . exact (pS (hXS hx)).2 hv
   . exact (pS (hYS hy)).2 hv
  . exact (pS (hZS hz)).2 hv⟩
 have h6:F'⊆S \ (Y∪Z):=λ v hv=>by
  obtain ⟨h1,h2⟩:=pS hv;refine rS ⟨h1,λ h=>h2 ?_⟩
  rcases pU h with hy | hz
  . exact mUl _ (mUr _ hy)
  . exact mUr _ hz
 have j3:l0<=m:=Nat.floor_mono (by linarith)
 have j5:∀ j,l0+j<=m ->
   (#(qs H F' l0 A):O)*(exp (e1/(8*(log n)^2)))^j <=
    (#(qs H F' (l0+j) A):O):=by
  intro j
  induction j with
  | zero=>intro _;simp
  | succ j ihj =>
   intro hj;set r:=l0+j;set Ar:=qs H F' r A
   have j0:M^(400*k) < (#Ar:O):=by
    have jp:(#(qs H F' l0 A):O)<=(#Ar:O):=by
     exact_mod_cast cL (qu H F' (by omega) A)
    exact lL2 jd jp
   have h7:(#A:O)<=(#Ar:O):=by
    have h0:qs H F' 0 A=A:=inter_eq_left.mpr jt
    have jc:A⊆Ar:=calc A=qs H F' 0 A:=h0.symm
     _⊆Ar:=qu H F' (Nat.zero_le r) A
    exact_mod_cast cL jc
   have j7:2*#Ar<=#S :=
    (nMl 2 (cL (qu H F' (by omega) A))).trans j2
   have j6:(#Ar:O)<=n:=by
    have:#Ar<=#S:=cL ((qt H F' r A).trans sS)
    dsimp only[n];exact_mod_cast this
   have j4:e1/(log n)^2<=qK e1 (e2*(d:O)) (#Ar:O):=by
    rw[qL (by linarith:e2*(d:O)/5<=(#Ar:O))]
    have jg:15/2<=15*(#Ar:O)/(e2*(d:O)):=by
     rw[div_le_div_iff₀ (by norm_num) h5];linarith
    have jf:15*(#Ar:O)/(e2*(d:O))<=n:=by
     rw[dLi h5]
     have:15<=e2*(d:O):=by rw[dLi jr] at ju;linarith
     calc
      15*(#Ar:O)<=(e2*(d:O))*(#Ar:O):=mlR this (nCn _)
      _<=(e2*(d:O))*n:=mlL j6 h5.le
      _=n*(e2*(d:O)):=mul_comm _ _
    have j1:0 < log (15*(#Ar:O)/(e2*(d:O))) :=
     lt_trans (by norm_num) (qM.trans_le (lLl (by norm_num) jg))
    have ja:log (15*(#Ar:O)/(e2*(d:O)))<=log n :=
     lLl (by positivity) jf
    exact dLl jl.le (by positivity) (pLl j1.le ja 2)
   have hquart:(k:O)*M^(300*k)<=(#Ar:O)*qK e1 (e2*(d:O)) (#Ar:O)/4:=by
    have h1:1/M<=qK e1 (e2*(d:O)) (#Ar:O):=h1M.trans j4
    have h2:M^(400*k)/M<=(#Ar:O)*qK e1 (e2*(d:O)) (#Ar:O):=by
     rw[div_eq_mul_one_div];exact mLm j0.le h1 (by positivity) (by positivity)
    have h3:(k:O)*M^(300*k)<=M^(400*k)/(4*M):=by
     rw[lDi (by positivity)]
     have:(k:O)*M^(300*k)*(4*M)=4*(k:O)*M^(300*k+1):=by
      rw[pow_succ];ring
     linarith
    have h4:M^(400*k)/(4*M)=M^(400*k)/M/4:=by ring
    linarith
   have hX_bd:(#X:O)<=(#Ar:O)*qK e1 (e2*(d:O)) (#Ar:O)/4:=by
    linarith [qP jl.le h5 j8 h7]
   have hY_bd:(#Y:O)<=(#Ar:O)*qK e1 (e2*(d:O)) (#Ar:O)/4:=by
    have hk1:(1:O)<=(k:O):=by exact_mod_cast hk
    have:M^(300*k)<=(k:O)*M^(300*k):=by nlinarith [show (0:O)<=M^(300*k) by positivity]
    linarith
   have hZ_bd:(#(qn H S Ar∩Z):O)<=(#Ar:O)*qK e1 (e2*(d:O)) (#Ar:O)/4:=by
    have jm:Disjoint (qs H (S \ (Y∪Z)) r A) Z :=
     rD λ v hv hz =>
      (pS (qt H (S \ (Y∪Z)) r A hv)).2 (mUr _ hz)
    have jj:=q08 H S Z (qw H h6 r A) jm;have jv:=js (r+1) (by omega);simp only[Nat.add_sub_cancel] at jv
    have hZ1:(#(qn H S Ar∩Z):O)<=(k:O)*((r+1:ℕ):O):=by
     exact_mod_cast (cL jj).trans jv
    have hrM:((r+1:ℕ):O)<=M :=
     (by exact_mod_cast (show r+1<=m by omega):((r+1:ℕ):O)<=(m:O)).trans
      (nFl (by positivity))
    have jn:M<=M^(300*k):=by
     calc
      M=M^1:=(pow_one M).symm
      _<=M^(300*k):=pLr (by linarith) (by omega)
    have hZ2:(k:O)*((r+1:ℕ):O)<=(k:O)*M^(300*k) :=
     mlL (hrM.trans jn) (nCn k)
    linarith
   have h8:#(qn H S Ar) <=
     #(qn H F' Ar)+#X+#Y+#(qn H S Ar∩Z):=by
    have jc:qn H S Ar⊆qn H F' Ar∪X∪Y∪(qn H S Ar∩Z):=by
     intro v hv;obtain ⟨hvS,jh,u,hu,huv⟩:=(qo H S _ v).mp hv
     by_cases hvF':v∈F'
     .
      exact mUl _ (mUl _ (mUl _
       ((qo H F' _ v).mpr ⟨hvF',jh,u,hu,huv⟩)))
     .
      have ji:v∈X∪Y∪Z:=by
       by_contra h;exact hvF' (rS ⟨hvS,h⟩)
      rcases pU ji with jo | hz
      .
       rcases pU jo with hx | hy
       . exact mUl _ (mUl _ (mUr _ hx))
       . exact mUl _ (mUr _ hy)
      . exact mUr _ (rI ⟨hv,hz⟩)
    calc
     #(qn H S Ar)
      <= #(qn H F' Ar∪X∪Y∪(qn H S Ar∩Z)):=cL jc
     _<=#(qn H F' Ar∪X∪Y)+#(qn H S Ar∩Z):=cUl _ _
     _<=#(qn H F' Ar∪X)+#Y+#(qn H S Ar∩Z):=by
       linarith [cUl (qn H F' Ar∪X) Y]
     _<=#(qn H F' Ar)+#X+#Y+#(qn H S Ar∩Z):=by
       linarith [cUl (qn H F' Ar) X]
   have hexpAr:(#Ar:O)*qK e1 (e2*(d:O)) (#Ar:O)<=(#(qn H S Ar):O):=by
    rw[mul_comm];exact jq Ar ((qt H F' r A).trans sS) (j8.trans h7) j7
   have hnbR:(#(qn H S Ar):O) <=
     (#(qn H F' Ar):O)+(#X:O)+(#Y:O)+(#(qn H S Ar∩Z):O):=by
    exact_mod_cast h8
   have hstep_nb:(#Ar:O)*(e1/(4*(log n)^2))<=(#(qn H F' Ar):O):=by
    have h1:(#Ar:O)*qK e1 (e2*(d:O)) (#Ar:O)/4<=(#(qn H F' Ar):O):=by
     linarith
    have h2:=mlL j4 (nCn #Ar)
    have h3:(#Ar:O)*(e1/(4*(log n)^2))=(#Ar:O)*(e1/(log n)^2)/4:=by ring
    linarith
   have hcard_s:(#(qs H F' (l0+(j+1)) A):O) =
     (#Ar:O)+(#(qn H F' Ar):O):=by
    rw[show l0+(j+1)=r+1 by omega];exact_mod_cast qx H F' r A
   have h9:exp (e1/(8*(log n)^2))<=1+e1/(4*(log n)^2):=by
    have h:=qW (by positivity) he1
    rwa [show e1/(4*(log n)^2)/2=e1/(8*(log n)^2) by ring] at h
   calc
    (#(qs H F' l0 A):O)*(exp (e1/(8*(log n)^2)))^(j+1)
     = (#(qs H F' l0 A):O)*(exp (e1/(8*(log n)^2)))^j *
       exp (e1/(8*(log n)^2)):=by rw[pow_succ];ring
    _<=(#Ar:O)*exp (e1/(8*(log n)^2)) :=
      mlR (ihj (by omega)) (ePp _).le
    _<=(#Ar:O)*(1+e1/(4*(log n)^2)) :=
      mlL h9 (nCn _)
    _<=(#(qs H F' (l0+(j+1)) A):O):=by linarith
 have jk:=j5 (m - l0) (by omega);rw[show l0+(m - l0)=m by omega,<- exp_nat_mul] at jk
 have hml:M - 1 - L<=((m - l0:ℕ):O):=by
  rw[Nat.cast_sub j3]
  have hm1:M - 1 < (m:O):=by linarith [nL1 M]
  have hl1:(l0:O)<=L:=nFl (pow_nonneg (by linarith) 5);linarith
 have j9:(1:O)<=(#(qs H F' l0 A):O):=by
  have:(1:O)<=M^(400*k):=oLp (by linarith)
  linarith
 have jb:exp (e1*(M - 1 - L)/(8*(log n)^2)) <=
   exp (((m - l0:ℕ):O)*(e1/(8*(log n)^2))):=by
  apply eLe.mpr
  have heq:e1*(M - 1 - L)/(8*(log n)^2)=(M - 1 - L)*(e1/(8*(log n)^2)):=by ring
  rw[heq];exact mlR hml (by positivity)
 have hbm_gt:n/2 < (#(qs H F' m A):O):=by
  calc
   n/2 < exp (e1*(M - 1 - L)/(8*(log n)^2)):=je
   _<=1*exp (((m - l0:ℕ):O)*(e1/(8*(log n)^2))):=by rw[one_mul];exact jb
   _<=(#(qs H F' l0 A):O)*exp (((m - l0:ℕ):O)*(e1/(8*(log n)^2))) :=
     mlR j9 (ePp _).le
   _<=(#(qs H F' m A):O):=jk
 have hbm_le:2*(#(qs H F' m A):O)<=n:=by dsimp only[n];exact_mod_cast j2
 linarith
lemma q0f {e1 e2:O} {k:ℕ} (h3:0 < e1) (h8:e1 < 1)
  (h2:0 < e2) (_he21:e2 < 1) (hk:1<=k) :
  ∃ d0:ℕ,100<=d0/\∀ {V:Type*} (H:SG V) (S A X Y Z:FS V) (d:ℕ),
   d0<=d->d<=#S ->
   qQ H S e1 (e2*(d:O)) ->
   A⊆S->X⊆S \ A->Y⊆S \ A->Z⊆S \ A ->
   e2*(d:O)/2<=(#A:O) ->
   (#X:O)<=(#A:O)*qK e1 (e2*(d:O)) (#A:O)/4 ->
   Disjoint (qs H (S \ (X∪Z)) (floor ((log (log (#S:O)))^5)) A) Y ->
   (#Y:O)<=(18/e1*(log (#S:O))^3)^(300*k) ->
   q07 H S A Y Z k ->
   let m:=floor (18/e1*(log (#S:O))^3)
   let l0:=floor ((log (log (#S:O)))^5)
   (18/e1*(log (#S:O))^3)^(400*k) < (#(qs H (S \ (X∪Y∪Z)) l0 A):O) /\
   #S < 2*#(qs H (S \ (X∪Y∪Z)) m A):=by
 obtain ⟨d0,h0,j0⟩:=q0b h3 h8 h2 hk;refine ⟨d0,h0,λ{V} H S A X Y Z d hd hdn hexp hAS hXS hYS hZS hAcard hXcard hYdisj hYcard hZlc=>?_⟩
 obtain ⟨h9,h4k,j3,h7,hM4,h6,h4,j4,j2,he1,h1M,h5,j1⟩:=j0 #S d hd hdn
 have h1:=q0d h3 h8 h2 hk H S A X Y Z d (h0.trans hd) hexp
  hAS hXS hZS hAcard hXcard hYdisj hZlc h9 h4k j3 h7 h6 h4 j1
 exact ⟨h1,q0e h3 h2 hk H S A X Y Z d (h0.trans hd) hdn hexp
  hAS hXS hYS hZS hAcard hXcard hYcard hZlc h9 h7 hM4 j4 j2 he1 h1M h5 h1⟩
lemma q0g {e1 e2:O} (j3:0 < e1) (jz:e1 < 1) (jn:0 < e2) (jy:e2 < 1) : ∃ d0:ℕ,100<=d0/\∀ {V:Type*} (H:SG V) (S A B W:FS V) (d:ℕ) (x:O), d0<=d->d<=#S -> qQ H S e1 (e2*(d:O)) -> (∀ v∈S,d - 1<=dS H S v) -> A⊆S->B⊆S->W⊆S \ (A∪B) -> 1<=x->x<=(#A:O)->x<=(#B:O) -> (#W:O)*(log (#S:O))^3<=10*x -> ∃ (a:V) (b:V) (_:a∈A) (_:b∈B) (p:(q3 H (S \ W)).Walk a b), p.IsPath/\(p.length:O)<=40/e1*(log (#S:O))^3 /\ (∀ w∈p.support,w∈A->w=a) /\ (∀ w∈p.support,w∈B->w=b):=by
 obtain ⟨d1,j4,k6⟩:=q0f j3 jz jn jy (k:=1) le_rfl
 have jw:∃ d2:ℕ,100<=d2/\∀ n d:ℕ,d2<=d->d<=n ->
   15/e2<=(d:O) /\
   40/e1<=log (n:O) /\
   2<=4/e1*(log (n:O))^3 /\
   10/(log (n:O))^3<=1/4 /\
   (d:O)/2<=(d:O) - 1 - (d:O)/4:=by
  have h1:=eGe (max 100 (15/e2));have h2:=lGe (max (40/e1) 4);have jo:=h1.and h2;rw[eAt] at jo;obtain ⟨B,hB⟩:=jo;refine ⟨max 100 (ceil B),lMl _ _,λ n d hd hdn=>?_⟩
  have k7:B<=(d:O):=(nLc B).trans (by exact_mod_cast (lMr 100 (ceil B)).trans hd);have hnR:B<=(n:O):=k7.trans (by exact_mod_cast hdn);have ka:=hB (d:O) k7;have k9:=hB (n:O) hnR;have jx:4<=log (n:O):=lT (lMr _ _) k9.2;have h5:40/e1<=log (n:O):=lT (lMl _ _) k9.2
  have hl64:(64:O)<=(log (n:O))^3:=by
   calc
    (64:O)=4^3:=by norm_num
    _<=(log (n:O))^3:=pLl (by norm_num) jx 3
  refine ⟨lT (lMr _ _) ka.1,h5,?_,?_,?_⟩
  .
   have:4<=4/e1:=by rw[lDi j3];linarith
   nlinarith
  . rw[div_le_div_iff₀ (by positivity) (by norm_num)];nlinarith
  . have hd100:(100:O)<=(d:O):=lT (lMl _ _) ka.1;linarith
 obtain ⟨d2,_,jk⟩:=jw
 refine ⟨max d1 d2,lT j4 (lMl _ _),
  λ{V} H S A B W d x hd hdn hexp hmindeg hAS hBS hWS hx1 hxA hxB hW=>?_⟩
 have k8:d1<=d:=lT (lMl _ _) hd;have hd2:d2<=d:=lT (lMr _ _) hd;obtain ⟨k4,h5,h2_4,h10_4,hd_half⟩:=jk #S d hd2 hdn;set n:O:=(#S:O);set m:=floor (18/e1*(log n)^3);have hln_pos:0 < log n:=lL2 (by positivity) h5
 have h6:0 < e2*(d:O):=by
  have:0 < (d:O):=by exact_mod_cast (show 0 < d by omega)
  positivity
 have h0:∀ A' B':FS V,A'⊆S->B'⊆S->W⊆S \ (A'∪B') ->
   e2*(d:O)/2<=(#A':O)->e2*(d:O)/2<=(#B':O) ->
   (#W:O)*(log n)^3<=10*(#A':O) ->
   (#W:O)*(log n)^3<=10*(#B':O) ->
   ∃ a'∈A',∃ b'∈B',∃ p:(q3 H (S \ W)).Walk a' b',p.length<=2*m:=by
  intro A' B' ju js jv j6 j5 hWA' hWB'
  have j7:∀ C:FS V,C⊆S->e2*(d:O)/2<=(#C:O) ->
    (#W:O)*(log n)^3<=10*(#C:O) ->
    (#W:O)<=(#C:O)*qK e1 (e2*(d:O)) (#C:O)/4:=by
   intro C hCS hCd hWC
   have hCn:(#C:O)<=n:=by dsimp only[n];exact_mod_cast cL hCS
   have hks:e1/(log n)^2<=qK e1 (e2*(d:O)) (#C:O):=by
    rw[qL (by linarith:e2*(d:O)/5<=(#C:O))]
    have jj:15/2<=15*(#C:O)/(e2*(d:O)):=by
     rw[div_le_div_iff₀ (by norm_num) h6];linarith
    have ji:15*(#C:O)/(e2*(d:O))<=n:=by
     rw[dLi h6]
     have:15<=e2*(d:O):=by rw[dLi jn] at k4;linarith
     nlinarith
    have h9:0 < log (15*(#C:O)/(e2*(d:O))) :=
     lt_trans (by norm_num) (qM.trans_le (lLl (by norm_num) jj))
    exact dLl j3.le (by positivity)
     (pLl h9.le (lLl (by positivity) ji) 2)
   have h10:10/(log n)^3<=e1/(4*(log n)^2):=by
    rw[div_le_div_iff₀ (by positivity) (by positivity)]
    have:40<=e1*log n:=by rw[dLi j3] at h5;linarith
    nlinarith [show (0:O)<=(log n)^2 by positivity]
   have jh:(#W:O)<=(#C:O)*(10/(log n)^3):=by
    rw[mul_div_assoc',lDi (by positivity)];linarith
   calc
    (#W:O)<=(#C:O)*(10/(log n)^3):=jh
    _<=(#C:O)*(e1/(4*(log n)^2)):=mlL h10 (nCn _)
    _<=(#C:O)*qK e1 (e2*(d:O)) (#C:O)/4:=by
      have h1:=mlL hks (nCn #C)
      have h2:(#C:O)*(e1/(4*(log n)^2)) =
        (#C:O)*(e1/(log n)^2)/4:=by ring
      linarith
  have h8:W⊆S \ A':=λ v hv=>by
   obtain ⟨h1,h2⟩:=pS (jv hv);exact rS ⟨h1,λ h=>h2 (mUl _ h)⟩
  have h7:W⊆S \ B':=λ v hv=>by
   obtain ⟨h1,h2⟩:=pS (jv hv);exact rS ⟨h1,λ h=>h2 (mUr _ h)⟩
  have jr:=(k6 H S A' W ∅ ∅ d k8 hdn hexp ju h8 (empty_subset _) (empty_subset _)
   j6 (j7 A' ju j6 hWA') (Finset.disjoint_empty_right _) (by simp;positivity)
   (q09 (q0a H S A' 1))).2
  have jq:=(k6 H S B' W ∅ ∅ d k8 hdn hexp js h7 (empty_subset _) (empty_subset _)
   j5 (j7 B' js j5 hWB') (Finset.disjoint_empty_right _) (by simp;positivity)
   (q09 (q0a H S B' 1))).2
  simp only[union_empty] at jr jq;change #S < 2*#(qs H (S \ W) m A') at jr;change #S < 2*#(qs H (S \ W) m B') at jq
  have jc:(qs H (S \ W) m A'∩qs H (S \ W) m B').Nonempty:=by
   rw[Finset.nonempty_iff_ne_empty];intro jd;have hun:=Finset.card_union_add_card_inter (qs H (S \ W) m A') (qs H (S \ W) m B');rw[jd,card_empty,add_zero] at hun
   have jl:qs H (S \ W) m A'∪qs H (S \ W) m B'⊆S :=
    uS ((qt H (S \ W) m A').trans sS)
     ((qt H (S \ W) m B').trans sS)
   have hle:=cL jl;omega
  obtain ⟨a',ha',b',hb',p,hp⟩:=qF jc;exact ⟨a',ha',b',hb',p,by omega⟩
 have k3:((2*m+2:ℕ):O)<=40/e1*(log n)^3:=by
  have hm_le:(m:O)<=18/e1*(log n)^3:=nFl (by positivity)
  have h40:2*(18/e1*(log n)^3)+4/e1*(log n)^3=40/e1*(log n)^3:=by ring
  push_cast;linarith
 have jt:A⊆S \ W:=λ v hv =>
  rS ⟨hAS hv,λ hw=>(pS (hWS hw)).2 (mUl _ hv)⟩
 have jp:B⊆S \ W:=λ v hv =>
  rS ⟨hBS hv,λ hw=>(pS (hWS hw)).2 (mUr _ hv)⟩
 have hex:∃ a∈A,∃ b∈B,∃ p:(q3 H (S \ W)).Walk a b,p.length<=2*m+2:=by
  by_cases h4:e2*(d:O)/2<=x
  .
   obtain ⟨a,ha,b,hb,p,hlen⟩:=h0 A B hAS hBS hWS
    (h4.trans hxA) (h4.trans hxB) (by linarith) (by linarith)
   exact ⟨a,ha,b,hb,p,by omega⟩
  .
   push Not at h4
   let A':=qs H (S \ W) 1 A;let B':=qs H (S \ W) 1 B
   have hW_le_d4:(#W:O)<=(d:O)/4:=by
    have h1:(#W:O)<=10/(log n)^3*x:=by
     rw[div_mul_eq_mul_div,lDi (by positivity)];linarith
    have h2:x<=(d:O):=by
     have:e2*(d:O)/2<=(d:O):=by
      have:0<=(d:O):=nCn d;nlinarith
     linarith
    nlinarith
   have h3:∀ C:FS V,C⊆S \ W->C.Nonempty ->
     e2*(d:O)/2<=(#(qs H (S \ W) 1 C):O):=by
    intro C hCSW ⟨c,hc⟩;have hcS:c∈S:=(pS (hCSW hc)).1
    have j2:(S.filter (H.Adj c)) \ W⊆qs H (S \ W) 1 C:=by
     intro v hv;obtain ⟨hv1,hvW⟩:=pS hv;obtain ⟨hvS,hcv⟩:=pF hv1
     by_cases k5:v∈C∩(S \ W)
     . exact mUl _ k5
     .
      exact mUr _ ((qo H (S \ W) _ v).mpr
       ⟨rS ⟨hvS,hvW⟩,k5,c,rI ⟨hc,hCSW hc⟩,hcv⟩)
    have j0:d - 1<=#(S.filter (H.Adj c)):=hmindeg c hcS
    have jg:#(S.filter (H.Adj c)) - #W<=#((S.filter (H.Adj c)) \ W):=by
     have:=cSd (S.filter (H.Adj c)) W
     have:=cL (inter_subset_right (s₁:=S.filter (H.Adj c)) (s₂:=W))
     omega
    have jf:#((S.filter (H.Adj c)) \ W)<=#(qs H (S \ W) 1 C) :=
     cL j2
    have hR:(d:O) - 1 - (#W:O)<=(#(qs H (S \ W) 1 C):O):=by
     by_cases k0:#W<=#(S.filter (H.Adj c))
     .
      have jl:(d:O) - 1<=(#(S.filter (H.Adj c)):O):=by
       have je:1<=d:=by omega
       have hcs:((d - 1:ℕ):O)=(d:O) - 1:=by rw[Nat.cast_sub je,Nat.cast_one]
       have h1':((d - 1:ℕ):O)<=(#(S.filter (H.Adj c)):O):=by exact_mod_cast j0
       linarith
      have h2':(#(S.filter (H.Adj c)):O) - (#W:O) <=
        (#((S.filter (H.Adj c)) \ W):O):=by
       rw[<- Nat.cast_sub k0];exact_mod_cast jg
      have h3':(#((S.filter (H.Adj c)) \ W):O)<=(#(qs H (S \ W) 1 C):O):=by
       exact_mod_cast jf
      linarith
     .
      push Not at k0
      have h1':(d:O) - 1<=(#(S.filter (H.Adj c)):O):=by
       have je:1<=d:=by omega
       have hcs:((d - 1:ℕ):O)=(d:O) - 1:=by rw[Nat.cast_sub je,Nat.cast_one]
       have h1'':((d - 1:ℕ):O)<=(#(S.filter (H.Adj c)):O):=by exact_mod_cast j0
       linarith
      have:(#(S.filter (H.Adj c)):O) < (#W:O):=by exact_mod_cast k0
      have:(0:O)<=(#(qs H (S \ W) 1 C):O):=nCn _
      linarith
    have he2d:e2*(d:O)/2<=(d:O)/2:=by
     have:0<=(d:O):=nCn d;nlinarith
    linarith
   have k2:A.Nonempty:=card_pos.mp (by exact_mod_cast (show (0:O) < (#A:O) by linarith));have k1:B.Nonempty:=card_pos.mp (by exact_mod_cast (show (0:O) < (#B:O) by linarith));have j6:=h3 A jt k2;have j5:=h3 B jp k1;have j9:A'⊆S \ W:=qt H (S \ W) 1 A;have j8:B'⊆S \ W:=qt H (S \ W) 1 B
   have jv:W⊆S \ (A'∪B'):=λ v hv=>rS
    ⟨(pS (hWS hv)).1,λ h=>by
     rcases pU h with ha' | hb'
     . exact (pS (j9 ha')).2 hv
     . exact (pS (j8 hb')).2 hv⟩
   obtain ⟨a',ha',b',hb',q,hqlen⟩:=h0 A' B'
    (j9.trans sS) (j8.trans sS) jv
    j6 j5 (by linarith) (by linarith)
   obtain ⟨a,ha,pa,_,hpalen,_⟩:=qB ha';obtain ⟨b,hb,pb,_,hpblen,_⟩:=qB hb'
   exact ⟨a,(pI ha).1,b,(pI hb).1,
    (pa.append q).append pb.reverse,
    by rw[wLa,wLa,wLr];omega⟩
 obtain ⟨a,b,ha,hb,p,j1,jm,jb,ja,_⟩ :=
  qE jt jp hex
 exact ⟨a,b,ha,hb,p,j1,(by exact_mod_cast jm:(p.length:O)<=((2*m+2:ℕ):O)).trans k3,
  jb,ja⟩
lemma q0h {e1 e2:O} (j0:0 < e1) (jg:0 < e2) :
  ∃ d0:ℕ,100<=d0/\∀ n d:ℕ,d0<=d->d<=n ->
   let D:O:=exp ((log (log (n:O)))^2)
   (15/e2<=(d:O)) /\
   (4<=log (log (n:O))) /\
   (2*D^3+2*D<=(n:O)^(1/8:O)/2) /\
   (4*D^3<=(n:O)) /\
   (2*D^3<=exp (4*(log (log (n:O)))^2)) /\
   (1/D < e1/(32*(log (log (n:O)))^4)) /\
   (5*(10:O)^10/(log (log (n:O)))^10 <
    e1/(32*(log (log (n:O)))^4)) /\
   (2*(log (n:O))^(1/10:O)*((log (n:O))^(1/10:O)+1) *
    (n:O)^(1/9:O)<=(n:O)^(1/8:O)/2) /\
   ((log (n:O))^(1/5:O)/e2<=(log (n:O))^(1/4:O)) /\
   ((D+1)^((log (n:O))^(1/4:O))<=(n:O)^(1/100:O)) /\
   ((log (n:O))^(1/5:O)*(n:O)^(1/100:O)<=(n:O)^(1/9:O)) /\
   (2*(log (n:O))^(3/10:O)<=(n:O)) /\
   (∀ r:O,e2*(d:O)<=r ->
    1/(e2*r) < e1/(18*(log r)^2) /\
    5/(log r)^10 < e1/(18*(log r)^2)):=by
 have h9:Filter.Tendsto (λ x:O=>log (log x)) atTop atTop :=
  tL.comp tL
 have h1:∀ᶠ x:O in atTop,15/e2<=x/\4<=log (log x) :=
  (eGe (15/e2)).and (h9.eventually_ge_atTop 4)
 have h2:∀ᶠ x:O in atTop,
   let D:=exp ((log (log x))^2)
   2*D^3+2*D<=x^(1/8:O)/2 /\
   4*D^3<=x /\
   2*D^3<=exp (4*(log (log x))^2):=by
  filter_upwards [q03 (C:=3) 2 (β:=1/16) (by norm_num),
   h9.eventually_ge_atTop 2,eGe ((8:O)^(16:ℕ))] with x hD3 hll hx
  set D:=exp ((log (log x))^2);have jk:1<=D:=one_le_exp (by positivity)
  have j2:D^3=exp (3*(log (log x))^2):=by
   rw[<- exp_nat_mul,Nat.cast_ofNat]
  rw[<- j2] at hD3;have j7:0 < x:=lL2 (by positivity) hx
  have je:8<=x^(1/16:O):=by
   have h1:=rLl (by positivity) hx (show (0:O)<=1/16 by norm_num);rw[<- rN,<- rpow_mul (by norm_num)] at h1;norm_num at h1;exact h1
  have j4:x^(1/8:O)=x^(1/16:O)*x^(1/16:O):=by
   rw[<- rpow_add j7];norm_num
  have hD3_le:D<=D^3:=by
   calc
    D=D^1:=(pow_one D).symm
    _<=D^3:=pLr jk (by omega)
  have h8D3:8*D^3<=x^(1/8:O):=by
   rw[j4];exact mLm je hD3 (by positivity) (by positivity)
  have hx18_le_x:x^(1/8:O)<=x:=by
   calc
    x^(1/8:O)<=x^(1:O):=rLe (by linarith [show (1:O)<=(8:O)^(16:ℕ) by norm_num]) (by norm_num)
    _=x:=r1 x
  refine ⟨by linarith,by linarith,?_⟩
  have jd:(2:O)<=exp ((log (log x))^2):=by
   have:(1:O)<=(log (log x))^2:=by nlinarith
   linarith [add_one_le_exp ((log (log x))^2)]
  rw[show 4*(log (log x))^2=(log (log x))^2+3*(log (log x))^2 by ring,
   exp_add,<- j2]
  exact mlR jd (by positivity)
 have h3:∀ᶠ x:O in atTop,
   1/exp ((log (log x))^2) < e1/(32*(log (log x))^4) /\
   5*(10:O)^10/(log (log x))^10 < e1/(32*(log (log x))^4):=by
  let B0:=max (192/e1+2) (5*(10:O)^10*32/e1+2)
  filter_upwards [h9.eventually_ge_atTop B0] with x hll
  set t:=log (log x);have ht1:192/e1+2<=t:=lT (lMl _ _) hll;have ht2:5*(10:O)^10*32/e1+2<=t:=lT (lMr _ _) hll
  have ht_ge2:2<=t:=by linarith [show (0:O) < 192/e1 by positivity]
  constructor
  .
   rw[div_lt_div_iff₀ (ePp _) (by positivity),one_mul]
   have jb:(t^2)^3/(factorial 3:O)<=exp (t^2):=by
    have h:=Real.sum_le_exp_of_nonneg (x:=t^2) (by positivity) 4
    have hs:(t^2)^3/(factorial 3:O)<=∑ i∈range 4,(t^2)^i/(factorial i:O) :=
     Finset.single_le_sum (f:=λ i=>(t^2)^i/(factorial i:O))
      (λ _ _=>by positivity) (mem_range.mpr (by omega))
    exact hs.trans h
   have ja:(factorial 3:O)=6:=by norm_num [factorial]
   rw[ja] at jb
   have jf:192/e1 < t^2:=by nlinarith
   have h0:192 < e1*t^2:=by
    have:=mul_lt_mul_of_pos_left jf j0
    rwa [mul_div_cancel₀ _ j0.ne'] at this
   have h32:32*t^4 < e1*(t^6/6):=by
    have:192*t^4 < e1*t^2*t^4:=mul_lt_mul_of_pos_right h0 (by positivity)
    linarith [show e1*t^2*t^4=e1*t^6 by ring]
   have:(t^2)^3/6=t^6/6:=by ring
   nlinarith
  .
   rw[div_lt_div_iff₀ (by positivity) (by positivity)]
   have jf:5*(10:O)^10*32/e1 < t^6:=by
    have:t<=t^6:=by
     calc
      t=t^1:=(pow_one t).symm
      _<=t^6:=pLr (by linarith) (by omega)
    linarith
   have h0:5*(10:O)^10*32 < e1*t^6:=by
    have:=mul_lt_mul_of_pos_left jf j0
    rwa [mul_div_cancel₀ _ j0.ne'] at this
   have hmul4:5*(10:O)^10*32*t^4 < e1*t^6*t^4 :=
    mul_lt_mul_of_pos_right h0 (by positivity)
   linarith [show e1*t^6*t^4=e1*t^10 by ring]
 have h4:∀ᶠ x:O in atTop,
   2*(log x)^(1/10:O)*((log x)^(1/10:O)+1)*x^(1/9:O) <=
    x^(1/8:O)/2:=by
  filter_upwards [q00 (C:=8) (α:=1/5) (β:=1/72) (by norm_num),
   lGe 1,eGe (1:O)] with x h8 hl hx1
  have hlog1:(1:O)<=(log x)^(1/10:O):=Real.one_le_rpow hl (by norm_num)
  have hsq:(log x)^(1/10:O)*(log x)^(1/10:O)=(log x)^(1/5:O):=by
   rw[<- rpow_add (by linarith)];norm_num
  have j8:x^(1/8:O)=x^(1/72:O)*x^(1/9:O):=by
   rw[<- rpow_add (by linarith)];norm_num
  have h1:2*(log x)^(1/10:O)*((log x)^(1/10:O)+1) <=
    4*(log x)^(1/5:O):=by nlinarith
  rw[j8]
  have h2:4*(log x)^(1/5:O)<=x^(1/72:O)/2:=by linarith
  have h3':=mlR (h1.trans h2) (rNn (show (0:O)<=x by linarith) (1/9:O));linarith
 have h5:∀ᶠ x:O in atTop,
   (log x)^(1/5:O)/e2<=(log x)^(1/4:O):=by
  filter_upwards [lGe ((max (1/e2) 1)^(20:ℕ))] with x hl
  have j1:0 < log x:=lL2 (by positivity) hl
  have h20:1/e2<=(log x)^(1/20:O):=by
   have h1:=rLl (by positivity) hl (show (0:O)<=1/20 by norm_num);rw[<- rN,<- rpow_mul (by positivity)] at h1;norm_num at h1;rw[one_div];exact h1.1
  have h0:=mlL h20 (rNn j1.le (1/5:O));rw[<- rpow_add j1] at h0;norm_num at h0
  rwa [<- div_eq_mul_inv] at h0
 have h6:∀ᶠ x:O in atTop,
   (exp ((log (log x))^2)+1)^((log x)^(1/4:O))<=x^(1/100:O):=by
  filter_upwards [q02 (C:=200) 2 (β:=3/4) (by norm_num),
   h9.eventually_ge_atTop 1,lGe 1,
   eGe (1:O)] with x h200 hll hl hx1
  set t:=log (log x);have jk:1<=exp (t^2):=one_le_exp (by positivity)
  have h2e:(2:O)<=exp (t^2):=by
   have:1<=t^2:=by nlinarith
   linarith [add_one_le_exp (t^2)]
  have ji:exp (t^2)+1<=exp (2*t^2):=by
   rw[show 2*t^2=t^2+t^2 by ring,exp_add];nlinarith
  have j9:=rLl (by positivity) ji (rNn (show (0:O)<=log x by linarith) (1/4:O))
  have j5:(exp (2*t^2))^((log x)^(1/4:O)) =
    exp (2*t^2*(log x)^(1/4:O)):=by
   rw[rpow_def_of_pos (ePp _),log_exp]
  rw[j5] at j9;rw[rpow_def_of_pos (by linarith:0 < x)];refine j9.trans (eLe.mpr ?_);have h0:=mlR h200 (rNn (show (0:O)<=log x by linarith) (1/4:O));rw[<- rpow_add (by linarith:0 < log x)] at h0;norm_num at h0;linarith
 have h7:∀ᶠ x:O in atTop,
   (log x)^(1/5:O)*x^(1/100:O)<=x^(1/9:O) /\
   2*(log x)^(3/10:O)<=x:=by
  filter_upwards [q00 (C:=1) (α:=1/5) (β:=91/900) (by norm_num),
   q00 (C:=2) (α:=3/10) (β:=1) (by norm_num),
   eGe (1:O)] with x h1 h2 hx1
  rw[one_mul] at h1;rw[r1] at h2;refine ⟨?_,h2⟩;have h0:=mlR h1 (rNn (by linarith) (1/100:O));rw[<- rpow_add (by linarith:0 < x)] at h0;norm_num at h0;exact h0
 have j6:∀ᶠ r:O in atTop,
   1/(e2*r) < e1/(18*(log r)^2) /\
   5/(log r)^10 < e1/(18*(log r)^2):=by
  filter_upwards [q01 (C:=20/(e1*e2)) 2 (β:=1) (by norm_num),
   lGe (100/e1+2),
   eGe (2:O)] with r h1 h2 hr2
  rw[r1] at h1
  have hlr2:2<=log r:=by linarith [show (0:O) < 100/e1 by positivity]
  constructor
  .
   rw[div_lt_div_iff₀ (by positivity) (by positivity),one_mul];have h0:=mlL h1 (show (0:O)<=e1*e2 by positivity)
   have heq:e1*e2*(20/(e1*e2)*(log r)^2)=20*(log r)^2:=by field_simp
   rw[heq] at h0;nlinarith [show (4:O)<=(log r)^2 by nlinarith]
  .
   rw[div_lt_div_iff₀ (by positivity) (by positivity)]
   have j9:log r<=(log r)^8:=by
    calc
     log r=(log r)^1:=(pow_one _).symm
     _<=(log r)^8:=pLr (by linarith) (by omega)
   have h90:90/e1 < (log r)^8:=by
    have:90/e1 < 100/e1:=div_lt_div_of_pos_right (by norm_num) j0
    linarith
   have h0:=mul_lt_mul_of_pos_left h90 j0;rw[mul_div_cancel₀ _ j0.ne'] at h0;have hmul2:=mul_lt_mul_of_pos_right h0 (show (0:O) < (log r)^2 by positivity);linarith [show e1*(log r)^8*(log r)^2=e1*(log r)^10 by ring]
 rw[eAt] at j6;obtain ⟨R0,hR0⟩:=j6
 have jc:=(eGe (max 100 (R0/e2))).and
  (h1.and (h2.and (h3.and (h4.and (h5.and (h6.and h7))))))
 rw[eAt] at jc;obtain ⟨B,hB⟩:=jc;refine ⟨max 100 (ceil B),lMl _ _,λ n d hd hdn=>?_⟩
 have jj:B<=(d:O):=(nLc B).trans (by exact_mod_cast (lMr 100 (ceil B)).trans hd);have hnR:B<=(n:O):=jj.trans (by exact_mod_cast hdn);have jl:=hB (d:O) jj;have j3:=hB (n:O) hnR
 refine ⟨jl.2.1.1,j3.2.1.2,j3.2.2.1.1,j3.2.2.1.2.1,j3.2.2.1.2.2,
  j3.2.2.2.1.1,j3.2.2.2.1.2,j3.2.2.2.2.1,j3.2.2.2.2.2.1,j3.2.2.2.2.2.2.1,
  j3.2.2.2.2.2.2.2.1,j3.2.2.2.2.2.2.2.2,λ r hr=>hR0 r ?_⟩
 have jh:R0/e2<=(d:O):=lT (lMr _ _) jl.1
 have:=(dLi jg).mp jh
 linarith
lemma q0i {V ι:Type*} {e1 e2:O} (jo:0 < e1) (jn:0 < e2) (H:SG V) (S U:FS V) (d:ℕ) (I1:FS ι) (Vs:ι->FS V) (hd:100<=d) (hdn:d<=#S) (jm:qQ H S e1 (e2*(d:O))) (jr:15/e2<=(d:O)) (hll4:4<=log (log (#S:O))) (hD3_n18:2*(exp ((log (log (#S:O)))^2))^3 + 2*exp ((log (log (#S:O)))^2)<=(#S:O)^(1/8:O)/2) (h4D3_n:4*(exp ((log (log (#S:O)))^2))^3<=(#S:O)) (j3:2*(exp ((log (log (#S:O)))^2))^3 <= exp (4*(log (log (#S:O)))^2)) (h1D_lt:1/exp ((log (log (#S:O)))^2) < e1/(32*(log (log (#S:O)))^4)) (h510_lt:5*(10:O)^10/(log (log (#S:O)))^10 < e1/(32*(log (log (#S:O)))^4)) (hUcard:(#U:O)<=exp ((log (log (#S:O)))^2)) (jj:∀ i∈I1,Vs i⊆S \ U) (jh:∀ i∈I1,∀ j∈I1,i≠j->Disjoint (Vs i) (Vs j)) (h5:∀ i∈I1,e2*(d:O)<=(#(Vs i):O) /\ (#(Vs i):O)<=exp ((log (log (#S:O)))^2)) (jq:∀ i∈I1,(#(qn H (S \ U) (Vs i)):O) <= 5*(#(Vs i):O)/(log (#(Vs i):O))^10) (jb:∀ i∈I1,(log (#S:O))^(1/10:O)<=(#(Vs i):O)) (hcase1:(#S:O)^(1/8:O)/2<=(#(I1.biUnion Vs):O)):False:=by
 set n:O:=(#S:O);set D:O:=exp ((log (log n))^2)
 have hd_pos:(0:O) < (d:O):=by exact_mod_cast (show 0 < d by omega)
 have h6:0 < e2*(d:O):=by positivity
 have h15_le_kd:15<=e2*(d:O):=by rw[dLi jn] at jr;linarith
 have hD1:1<=D:=one_le_exp (by positivity)
 have hln_pos:1 < log n:=by
  have hn100:(100:O)<=n:=by dsimp only[n];exact_mod_cast (show 100<=#S by omega)
  rw[lIt (by linarith)];linarith [e1l]
 have hI1_sum:(#(I1.biUnion Vs):O)<=(#I1:O)*D:=by
  calc
   (#(I1.biUnion Vs):O)
    <= ∑ i∈I1,(#(Vs i):O):=by exact_mod_cast cBu
   _<=∑ _i∈I1,D:=sum_le_sum λ i hi=>(h5 i hi).2
   _=(#I1:O)*D:=by simp
 let t0:ℕ:=ceil (D^2)
 have h7:t0<=#I1:=by
  have jc:(t0:O) < D^2+1:=ceil_lt_add_one (by positivity)
  have hR:(t0:O)<=(#I1:O):=by
   have h1:(t0:O)*D<=2*D^3+2*D:=by nlinarith
   have h2:(t0:O)*D<=(#I1:O)*D:=by linarith
   exact le_of_mul_le_mul_right h2 (by positivity)
  exact_mod_cast hR
 obtain ⟨I0,h0,h4⟩:=exists_subset_card_eq h7;let W:=I0.biUnion Vs
 have h3:#W=∑ i∈I0,#(Vs i) :=
  card_biUnion (λ i hi j hj hij=>jh i (h0 hi) j (h0 hj) hij)
 have hW_ge_D2:D^2<=(#W:O):=by
  have h1:(#I0:O)<=(#W:O):=by
   rw[h3];push_cast
   calc
    (#I0:O)=∑ _i∈I0,(1:O):=by simp
    _<=∑ i∈I0,(#(Vs i):O):=sum_le_sum λ i hi=>by
      linarith [(h5 i (h0 hi)).1]
  have h2:D^2<=(t0:O):=nLc _;rw[h4] at h1;linarith
 have h8:(#W:O)<=2*D^3:=by
  have h1:(#W:O)<=(#I0:O)*D:=by
   rw[h3];push_cast
   calc
    ∑ i∈I0,(#(Vs i):O)<=∑ _i∈I0,D:=sum_le_sum λ i hi=>(h5 i (h0 hi)).2
    _=(#I0:O)*D:=by simp
  have jc:(t0:O)<=D^2+1:=(ceil_lt_add_one (by positivity)).le
  have hD2_ge1:(1:O)<=D^2:=by nlinarith
  rw[h4] at h1;nlinarith
 have j2:e2*(d:O)/2<=(#W:O):=by
  have j4:(0:O) < (t0:O):=lL2 (by positivity) (nLc (D^2));have hne:I0.Nonempty:=card_pos.mp (by rw[h4];exact_mod_cast j4);obtain ⟨i0,jf⟩:=hne;have jk:Vs i0⊆W:=Finset.subset_biUnion_of_mem Vs jf
  have h1:(#(Vs i0):O)<=(#W:O):=by exact_mod_cast cL jk
  linarith [(h5 i0 (h0 jf)).1]
 have ja:2*#W<=#S:=by
  have hR:((2*#W:ℕ):O)<=(#S:O):=by push_cast;dsimp only[n] at *;linarith
  exact_mod_cast hR
 have j0:W⊆S:=biUnion_subset.mpr λ i hi=>(jj i (h0 hi)).trans sS
 have j5:qn H S W⊆U∪I0.biUnion (λ i=>qn H (S \ U) (Vs i)):=by
  intro v hv;obtain ⟨hvS,hvW,u,huW,huv⟩:=(qo H S W v).mp hv
  by_cases js:v∈U
  . exact mUl _ js
  .
   obtain ⟨i,jf,hui⟩:=mB.mp huW
   refine mUr _ (mB.mpr ⟨i,jf,(qo H (S \ U) (Vs i) v).mpr
    ⟨rS ⟨hvS,js⟩,λ hvi=>hvW (mB.mpr ⟨i,jf,hvi⟩),u,hui,huv⟩⟩)
 have hnb_ub:(#(qn H S W):O) <=
   D+(5*(10:O)^10/(log (log n))^10)*(#W:O):=by
  have h1:#(qn H S W)<=#U+∑ i∈I0,#(qn H (S \ U) (Vs i)) :=
   (cL j5).trans ((cUl _ _).trans (Nat.add_le_add_left cBu _))
  have h1R:(#(qn H S W):O)<=(#U:O)+∑ i∈I0,(#(qn H (S \ U) (Vs i)):O):=by
   exact_mod_cast h1
  have hsum_le:∑ i∈I0,(#(qn H (S \ U) (Vs i)):O) <=
    (5*(10:O)^10/(log (log n))^10)*(#W:O):=by
   rw[h3,Nat.cast_sum,Finset.mul_sum];refine sum_le_sum λ i jf=>?_
   have jt:=h0 jf;have jg:=jb i jt
   have j7:log (log n)/10<=log (#(Vs i):O):=by
    have h:=lLl (rpow_pos_of_pos (by linarith) _) jg;rw[Real.log_rpow (by linarith)] at h;linarith
   have jd:(log (log n))^10/(10:O)^10<=(log (#(Vs i):O))^10:=by
    rw[<- div_pow];exact pLl (by positivity) j7 10
   have jl:=jq i jt
   have jp:5*(#(Vs i):O)/(log (#(Vs i):O))^10 <=
     5*(10:O)^10/(log (log n))^10*(#(Vs i):O):=by
    have ji:=one_div_le_one_div_of_le (by positivity) jd;rw[one_div_div] at ji;have hmul:=mlL ji (show (0:O)<=5*(#(Vs i):O) by positivity)
    linarith [show 5*(#(Vs i):O)*(1/(log (#(Vs i):O))^10) =
      5*(#(Vs i):O)/(log (#(Vs i):O))^10 by ring,
     show 5*(#(Vs i):O)*((10:O)^10/(log (log n))^10) =
      5*(10:O)^10/(log (log n))^10*(#(Vs i):O) by ring]
   exact jl.trans jp
  linarith
 have je:e1/(16*(log (log n))^4)<=qK e1 (e2*(d:O)) (#W:O):=by
  rw[qL (by linarith:e2*(d:O)/5<=(#W:O))]
  have j9:15/2<=15*(#W:O)/(e2*(d:O)):=by
   rw[div_le_div_iff₀ (by norm_num) h6];linarith
  have j8:15*(#W:O)/(e2*(d:O))<=exp (4*(log (log n))^2):=by
   have h1:15*(#W:O)/(e2*(d:O))<=(#W:O):=by
    rw[dLi h6];nlinarith
   exact h1.trans (h8.trans j3)
  have h9:0 < log (15*(#W:O)/(e2*(d:O))) :=
   lt_trans (by norm_num) (qM.trans_le (lLl (by norm_num) j9))
  have j6:log (15*(#W:O)/(e2*(d:O)))<=4*(log (log n))^2:=by
   have:=lLl (by positivity) j8;rwa [log_exp] at this
  have hsq:(log (15*(#W:O)/(e2*(d:O))))^2<=16*(log (log n))^4:=by
   have:=pLl h9.le j6 2
   linarith [show (4*(log (log n))^2)^2=16*(log (log n))^4 by ring]
  exact dLl jo.le (by positivity) hsq
 have hD_le_W:D<=(1/D)*(#W:O):=by
  rw[one_div_mul_eq_div,lDi (by positivity)];nlinarith
 have hexpW:=jm W j0 j2 ja
 have j1:(0:O) < (#W:O):=by linarith
 have hstrict:(1/D+5*(10:O)^10/(log (log n))^10)*(#W:O) <
   (e1/(16*(log (log n))^4))*(#W:O):=by
  have hsum_eps:e1/(32*(log (log n))^4)+e1/(32*(log (log n))^4) =
    e1/(16*(log (log n))^4):=by ring
  apply mul_lt_mul_of_pos_right _ j1;linarith
 have hks_mul:=mlL je j1.le;linarith
lemma q0j {V ι:Type*} {e1 e2:O} (kf:0 < e1) (jq:0 < e2) (H:SG V) (S U:FS V) (d:ℕ) (I2:FS ι) (Vs:ι->FS V) (hd:100<=d) (hdn:d<=#S) (ke:qQ H S e1 (e2*(d:O))) (kk:15/e2<=(d:O)) (hpig1:2*(log (#S:O))^(1/10:O)*((log (#S:O))^(1/10:O)+1) * (#S:O)^(1/9:O)<=(#S:O)^(1/8:O)/2) (jx:(log (#S:O))^(1/5:O)/e2<=(log (#S:O))^(1/4:O)) (kh:(exp ((log (log (#S:O)))^2)+1)^((log (#S:O))^(1/4:O)) <= (#S:O)^(1/100:O)) (hpig2:(log (#S:O))^(1/5:O)*(#S:O)^(1/100:O)<=(#S:O)^(1/9:O)) (h310_n:2*(log (#S:O))^(3/10:O)<=(#S:O)) (k1:∀ r:O,e2*(d:O)<=r -> 1/(e2*r) < e1/(18*(log r)^2)/\5/(log r)^10 < e1/(18*(log r)^2)) (hUcard:(#U:O)<=exp ((log (log (#S:O)))^2)) (k4:∀ i∈I2,Vs i⊆S \ U) (ju:∀ i∈I2,∀ j∈I2,i≠j->Disjoint (Vs i) (Vs j)) (jt:∀ i∈I2,e2*(d:O)<=(#(Vs i):O)) (kg:∀ i∈I2,(#(qn H (S \ U) (Vs i)):O) <= 5*(#(Vs i):O)/(log (#(Vs i):O))^10) (k5:∀ i∈I2,∀ v∈Vs i,(#(U.filter (H.Adj v)):O)<=(d:O)/2) (jj:∀ i∈I2,(#(Vs i):O) < (log (#S:O))^(1/10:O)) (hcase2:(#S:O)^(1/8:O)/2<=(#(I2.biUnion Vs):O)):False:=by
 set n:O:=(#S:O);set D:O:=exp ((log (log n))^2)
 have hd_pos:(0:O) < (d:O):=by exact_mod_cast (show 0 < d by omega)
 have j2:0 < e2*(d:O):=by positivity
 have j4:15<=e2*(d:O):=by rw[dLi jq] at kk;linarith
 have hD1:1<=D:=one_le_exp (by positivity)
 have h8:0 < n:=by dsimp only[n];exact_mod_cast (show 0 < #S by omega)
 have hln_pos:1 < log n:=by
  have hn100:(100:O)<=n:=by dsimp only[n];exact_mod_cast (show 100<=#S by omega)
  rw[lIt h8];linarith [e1l]
 let R:ℕ:=floor ((log n)^(1/10:O));have jc:∀ i∈I2,#(Vs i)<=R:=λ i hi=>nLf (jj i hi).le
 have hI2_card_ge:(#(I2.biUnion Vs):O)<=(#I2:O)*(log n)^(1/10:O):=by
  calc
   (#(I2.biUnion Vs):O)
    <= ∑ i∈I2,(#(Vs i):O):=by exact_mod_cast cBu
   _<=∑ _i∈I2,(log n)^(1/10:O):=sum_le_sum λ i hi =>
     (by exact_mod_cast jc i hi:(#(Vs i):O)<=(R:O)).trans (nFl (by positivity))
   _=(#I2:O)*(log n)^(1/10:O):=by simp
 have jk:∑ r∈range (R+1),#(I2.filter (λ i=>#(Vs i)=r))=#I2:=by
  rw[<- card_biUnion]
  . congr 1;ext i;simp only[mB,mem_range,mF];exact ⟨λ⟨_,_,hi,_⟩=>hi,λ hi=>⟨#(Vs i),Nat.lt_succ_of_le (jc i hi),hi,rfl⟩⟩
  . intro r₁ _ r2 _ k3;rw[Function.onFun,dL];intro i h1 h2;exact k3 ((pF h1).2.symm.trans (pF h2).2)
 obtain ⟨r,jm,jn⟩:=exists_max_image (range (R+1))
  (λ r=>#(I2.filter (λ i=>#(Vs i)=r))) ⟨0,mem_range.mpr (Nat.zero_lt_succ R)⟩
 let I3:=I2.filter (λ i=>#(Vs i)=r)
 have jw:n^(1/9:O)<=(#I3:O):=by
  have h1:#I2<=(R+1)*#I3:=by
   calc
    #I2=∑ r'∈range (R+1),#(I2.filter (λ i=>#(Vs i)=r')):=jk.symm
    _<=∑ _r'∈range (R+1),#I3:=sum_le_sum λ r' hr'=>jn r' hr'
    _=(R+1)*#I3:=by simp
  have kj:(#I2:O)<=((R:O)+1)*(#I3:O):=by exact_mod_cast h1
  have hR_le:(R:O)<=(log n)^(1/10:O):=nFl (by positivity)
  have ki:(#I2:O)<=((log n)^(1/10:O)+1)*(#I3:O) :=
   kj.trans (mlR (by linarith) (nCn _))
  have hcomb:(#(I2.biUnion Vs):O) <=
    (log n)^(1/10:O)*((log n)^(1/10:O)+1)*(#I3:O):=by
   have hm:=mlR ki (rNn (by linarith:0<=log n) (1/10:O))
   linarith [show ((log n)^(1/10:O)+1)*(#I3:O)*(log n)^(1/10:O) =
     (log n)^(1/10:O)*((log n)^(1/10:O)+1)*(#I3:O) by ring]
  have k2:0 < (log n)^(1/10:O)*((log n)^(1/10:O)+1):=by positivity
  by_contra k7;push Not at k7
  have:=mul_lt_mul_of_pos_left k7 k2
  linarith
 have jv:I3.Nonempty:=card_pos.mp (by
  exact_mod_cast (lL2 (rpow_pos_of_pos h8 _) jw))
 obtain ⟨k8,jp⟩:=jv
 have j6:e2*(d:O)<=(r:O):=by
  have h1:=jt k8 (pF jp).1
  rwa [(pF jp).2] at h1
 have h4:(r:O)<=(log n)^(1/10:O) :=
  (by exact_mod_cast (Nat.lt_succ_iff.mp (mem_range.mp jm)):(r:O)<=(R:O)).trans
   (nFl (by positivity))
 have j5:1<=r:=by
  have:(1:O)<=(r:O):=by linarith
  exact_mod_cast this
 let s:ℕ:=floor ((log n)^(1/4:O));let f:ι->FS V:=λ i=>qn H S (Vs i)∩U
 let h5:=U.powerset.filter (λ Z=>#Z<=s)
 have h6:∀ i∈I3,(#(f i):O)<=(r:O)^2/e2:=λ i hi=>by
  have hi2:i∈I2:=(pF hi).1;have hri:#(Vs i)=r:=(pF hi).2
  have k9:f i⊆(Vs i).biUnion (λ v=>U.filter (H.Adj v)):=by
   intro u hu;obtain ⟨huN,huU⟩:=pI hu;obtain ⟨_,_,v,hv,hvu⟩:=(qo H S (Vs i) u).mp huN;exact mB.mpr ⟨v,hv,rF ⟨huU,hvu⟩⟩
  have h1:(#(f i):O)<=∑ v∈Vs i,(#(U.filter (H.Adj v)):O):=by
   exact_mod_cast (cL k9).trans cBu
  have h2:∑ v∈Vs i,(#(U.filter (H.Adj v)):O)<=(r:O)*((d:O)/2):=by
   calc
    ∑ v∈Vs i,(#(U.filter (H.Adj v)):O)
     <= ∑ _v∈Vs i,((d:O)/2):=sum_le_sum λ v hv=>k5 i hi2 v hv
    _=(r:O)*((d:O)/2):=by rw[sum_const,nsmul_eq_mul,hri]
  have jf:(d:O)<=(r:O)/e2:=(lDi jq).mpr (by linarith)
  have h3:(r:O)*((d:O)/2)<=(r:O)^2/e2:=by
   have:=mlL jf (nCn r)
   linarith [show (r:O)*((r:O)/e2)=(r:O)^2/e2 by ring,
    show (0:O)<=(r:O)*(d:O) by positivity]
  exact h1.trans (h2.trans h3)
 have j9:∀ i∈I3,f i∈h5:=λ i hi=>by
  refine rF ⟨mem_powerset.mpr inter_subset_right,?_⟩;apply nLf;have h1:=h6 i hi
  have ka:(r:O)^2<=(log n)^(1/5:O):=by
   have h:=pLl (nCn r) h4 2;rw[<- rN ((log n)^(1/10:O)),<- rpow_mul (by linarith:0<=log n)] at h;norm_num at h;exact h
  exact h1.trans ((dLr ka jq.le).trans jx)
 have jd:h5.Nonempty:=⟨f k8,j9 k8 jp⟩
 have hFams_card:(h5.card:O)<=n^(1/100:O):=by
  have h1:(h5.card:O)<=((#U:O)+1)^s:=by
   exact_mod_cast q05 U s
  have h2:((#U:O)+1)^s<=(D+1)^((log n)^(1/4:O)):=by
   calc
    ((#U:O)+1)^s<=(D+1)^s:=pLl (by positivity) (by linarith) s
    _=(D+1)^(s:O):=(rN _ _).symm
    _<=(D+1)^((log n)^(1/4:O)) :=
      rLe (by linarith) (nFl (by positivity))
  exact h1.trans (h2.trans kh)
 have jl:∑ Z∈h5,#(I3.filter (λ i=>f i=Z))=#I3:=by
  rw[<- card_biUnion]
  . congr 1;ext i;simp only[mB,mF];exact ⟨λ⟨_,_,hi,_⟩=>hi,λ hi=>⟨f i,j9 i hi,hi,rfl⟩⟩
  . intro Z1 _ Z2 _ k3;rw[Function.onFun,dL];intro i h1 h2;exact k3 ((pF h1).2.symm.trans (pF h2).2)
 obtain ⟨Z,_,jr⟩:=exists_max_image h5 (λ Z=>#(I3.filter (λ i=>f i=Z))) jd
 let IZ:=I3.filter (λ i=>f i=Z)
 have j3:r^2<=#IZ:=by
  have h1:#I3<=h5.card*#IZ:=by
   calc
    #I3=∑ Z'∈h5,#(I3.filter (λ i=>f i=Z')):=jl.symm
    _<=∑ _Z'∈h5,#IZ:=sum_le_sum λ Z' hZ'=>jr Z' hZ'
    _=h5.card*#IZ:=by simp
  have kj:(#I3:O)<=(h5.card:O)*(#IZ:O):=by exact_mod_cast h1
  have jo:((r^2:ℕ):O)<=(log n)^(1/5:O):=by
   push_cast;have h:=pLl (nCn r) h4 2;rw[<- rN ((log n)^(1/10:O)),<- rpow_mul (by linarith:0<=log n)] at h;norm_num at h;exact h
  have hR:((r^2:ℕ):O)<=(#IZ:O):=by
   by_contra k7;push Not at k7
   have hmul:(h5.card:O)*(#IZ:O) < n^(1/100:O)*((r^2:ℕ):O):=by
    have hIZ_nn:(0:O)<=(#IZ:O):=nCn _;have hF_nn:(0:O)<=(h5.card:O):=nCn _;have k2:(0:O) < n^(1/100:O):=rpow_pos_of_pos h8 _;nlinarith
   have hle2:n^(1/100:O)*((r^2:ℕ):O)<=(log n)^(1/5:O)*n^(1/100:O):=by
    rw[mul_comm];exact mlR jo (rNn h8.le _)
   linarith
  exact_mod_cast hR
 obtain ⟨I4,h9,h7⟩:=exists_subset_card_eq j3;have j0:I4⊆I3:=h9.trans (filter_subset _ _);have j1:I4⊆I2:=λ i hi=>(pF (j0 hi)).1
 let Y:=I4.biUnion Vs
 have h0:#Y=r^3:=by
  rw[card_biUnion (λ i hi j hj hij=>ju i (j1 hi) j (j1 hj) hij)]
  have k0:∑ i∈I4,#(Vs i)=∑ _i∈I4,r :=
   sum_congr rfl λ i hi=>(pF (j0 hi)).2
  rw[k0,sum_const,smul_eq_mul,h7];ring
 have ja:Y⊆S:=biUnion_subset.mpr λ i hi=>(k4 i (j1 hi)).trans sS
 have jb:e2*(d:O)/2<=(#Y:O):=by
  rw[h0];push_cast
  have:(r:O)<=(r:O)^3:=by
   have k6:(1:O)<=(r:O):=by exact_mod_cast j5
   calc
    (r:O)=(r:O)^1:=(pow_one _).symm
    _<=(r:O)^3:=pLr k6 (by omega)
  linarith
 have ji:2*#Y<=#S:=by
  have hr3:(r:O)^3<=(log n)^(3/10:O):=by
   have h:=pLl (nCn r) h4 3;rw[<- rN ((log n)^(1/10:O)),<- rpow_mul (by linarith:0<=log n)] at h;norm_num at h;exact h
  have hR:((2*#Y:ℕ):O)<=(#S:O):=by
   rw[h0];push_cast;dsimp only[n] at *;linarith
  exact_mod_cast hR
 have hZ_card:(#Z:O)<=(r:O)^2/e2:=by
  have k3:I4.Nonempty:=card_pos.mp (by rw[h7];positivity);obtain ⟨i0,kp⟩:=k3;have kd:f i0=Z:=(pF (h9 kp)).2;rw[<- kd];exact h6 i0 (j0 kp)
 have j7:qn H S Y⊆Z∪I4.biUnion (λ i=>qn H (S \ U) (Vs i)):=by
  intro v hv;obtain ⟨km,hvY,u,huY,kn⟩:=(qo H S Y v).mp hv;obtain ⟨i,kc,ko⟩:=mB.mp huY;have jz:v ∉ Vs i:=λ h=>hvY (mB.mpr ⟨i,kc,h⟩)
  by_cases kl:v∈U
  . have jy:v∈f i:=rI ⟨(qo H S (Vs i) v).mpr ⟨km,jz,u,ko,kn⟩,kl⟩;rw[(pF (h9 kc)).2] at jy;exact mUl _ jy
  .
   exact mUr _ (mB.mpr ⟨i,kc,(qo H (S \ U) (Vs i) v).mpr
    ⟨rS ⟨km,kl⟩,jz,u,ko,kn⟩⟩)
 have hnbY_ub:(#(qn H S Y):O) <=
   (r:O)^2/e2+(r:O)^2*(5*(r:O)/(log (r:O))^10):=by
  have h1:#(qn H S Y)<=#Z+∑ i∈I4,#(qn H (S \ U) (Vs i)) :=
   (cL j7).trans ((cUl _ _).trans (Nat.add_le_add_left cBu _))
  have kj:(#(qn H S Y):O)<=(#Z:O)+∑ i∈I4,(#(qn H (S \ U) (Vs i)):O):=by
   exact_mod_cast h1
  have k0:∑ i∈I4,(#(qn H (S \ U) (Vs i)):O) <=
    (r:O)^2*(5*(r:O)/(log (r:O))^10):=by
   calc
    ∑ i∈I4,(#(qn H (S \ U) (Vs i)):O)
     <= ∑ i∈I4,(5*(r:O)/(log (r:O))^10):=sum_le_sum λ i hi=>by
       have:=kg i (j1 hi);rwa [(pF (j0 hi)).2] at this
    _=(#I4:O)*(5*(r:O)/(log (r:O))^10):=by simp
    _=(r:O)^2*(5*(r:O)/(log (r:O))^10):=by rw[h7];push_cast;rfl
  linarith
 have kb:e1/(9*(log (r:O))^2)<=qK e1 (e2*(d:O)) (#Y:O):=by
  rw[qL (by linarith:e2*(d:O)/5<=(#Y:O)),h0];push_cast
  have hr3_ge:(r:O)<=(r:O)^3:=by
   have k6:(1:O)<=(r:O):=by exact_mod_cast j5
   calc
    (r:O)=(r:O)^1:=(pow_one _).symm
    _<=(r:O)^3:=pLr k6 (by omega)
  have jh:15/2<=15*(r:O)^3/(e2*(d:O)):=by
   rw[div_le_div_iff₀ (by norm_num) j2];linarith
  have jg:15*(r:O)^3/(e2*(d:O))<=(r:O)^3:=by
   rw[dLi j2]
   calc
    15*(r:O)^3<=(e2*(d:O))*(r:O)^3:=mlR j4 (by positivity)
    _=(r:O)^3*(e2*(d:O)):=mul_comm _ _
  have j8:0 < log (15*(r:O)^3/(e2*(d:O))) :=
   lt_trans (by norm_num) (qM.trans_le (lLl (by norm_num) jh))
  have je:log (15*(r:O)^3/(e2*(d:O)))<=3*log (r:O):=by
   have h1:=lLl (by positivity) jg
   rwa [lP,Nat.cast_ofNat] at h1
  have ka:(log (15*(r:O)^3/(e2*(d:O))))^2<=9*(log (r:O))^2:=by
   have h1:=pLl j8.le je 2;linarith [show (3*log (r:O))^2=9*(log (r:O))^2 by ring]
  exact dLl kf.le (by positivity) ka
 obtain ⟨k6,hr2⟩:=k1 (r:O) j6;have hexpY:=ke Y ja jb ji
 have js:(0:O) < (r:O)^3:=by positivity
 have h1:(r:O)^2/e2+(r:O)^2*(5*(r:O)/(log (r:O))^10) =
   (r:O)^3*(1/(e2*(r:O))+5/(log (r:O))^10):=by
  have:(r:O)≠0:=by positivity
  field_simp
 have hstrict:(r:O)^3*(1/(e2*(r:O))+5/(log (r:O))^10) <
   (r:O)^3*(e1/(9*(log (r:O))^2)):=by
  have hsum18:e1/(18*(log (r:O))^2)+e1/(18*(log (r:O))^2) =
    e1/(9*(log (r:O))^2):=by ring
  exact mul_lt_mul_of_pos_left (by linarith) js
 have hks_mul:(r:O)^3*(e1/(9*(log (r:O))^2)) <=
   qK e1 (e2*(d:O)) (#Y:O)*(#Y:O):=by
  rw[h0];push_cast;rw[mul_comm ((r:O)^3)];exact mlR (by simpa [h0] using kb) (by positivity)
 linarith
lemma q0k {e1 e2:O} (h9:0 < e1) (_he11:e1 < 1) (h8:0 < e2) (_he21:e2 < 1) : ∃ d0:ℕ,100<=d0/\∀ {V ι:Type*} (H:SG V) (S U:FS V) (d:ℕ) (I:FS ι) (Vs:ι->FS V), d0<=d->d<=#S -> qQ H S e1 (e2*(d:O)) -> U⊆S->(#U:O)<=exp ((log (log (#S:O)))^2) -> (∀ i∈I,Vs i⊆S \ U) -> (∀ i∈I,∀ j∈I,i≠j->Disjoint (Vs i) (Vs j)) -> (∀ i∈I,e2*(d:O)<=(#(Vs i):O) /\ (#(Vs i):O)<=exp ((log (log (#S:O)))^2)) -> (∀ i∈I,(#(qn H (S \ U) (Vs i)):O) <= 5*(#(Vs i):O)/(log (#(Vs i):O))^10) -> (∀ i∈I,∀ v∈Vs i,(#(U.filter (H.Adj v)):O)<=(d:O)/2) -> ((#(I.biUnion Vs):O) < (#S:O)^(1/8:O)):=by
 obtain ⟨d0,h3,ja⟩:=q0h h9 h8;refine ⟨d0,h3,λ{V ι} H S U d I Vs hd hdn hexp _ hUcard hVsub hVdisj hVsize hVnb hVdeg=>?_⟩
 obtain ⟨j9,jb,h6,j1,h5,j3,h7,j7,j4,jc,j6,j2,j5⟩ :=
  ja #S d hd hdn
 by_contra hge
 push Not at hge
 let I1:=I.filter (λ i=>(log (#S:O))^(1/10:O)<=(#(Vs i):O))
 let I2:=I \ I1;have h2:I1⊆I:=filter_subset _ _;have h0:I2⊆I:=sS
 have h4:#(I.biUnion Vs)=#(I1.biUnion Vs)+#(I2.biUnion Vs):=by
  have h1:I.biUnion Vs=I1.biUnion Vs∪I2.biUnion Vs:=by
   ext v;simp only[mB,mU,I2,mS]
   constructor
   .
    rintro ⟨i,hi,hv⟩
    by_cases h:i∈I1
    . exact Or.inl ⟨i,h,hv⟩
    . exact Or.inr ⟨i,⟨hi,h⟩,hv⟩
   .
    rintro (⟨i,hi,hv⟩ | ⟨i,⟨hi,_⟩,hv⟩)
    . exact ⟨i,h2 hi,hv⟩
    . exact ⟨i,hi,hv⟩
  rw[h1];apply card_union_of_disjoint;rw[dL];intro v hv1 hv2;obtain ⟨i,je,hvi⟩:=mB.mp hv1;obtain ⟨j,jd,hvj⟩:=mB.mp hv2
  have j8:i≠j:=λ h=>by subst h;exact (pS jd).2 je
  exact pD (hVdisj i (h2 je) j (h0 jd) j8) hvi hvj
 have hR:(#(I.biUnion Vs):O)=(#(I1.biUnion Vs):O)+(#(I2.biUnion Vs):O):=by
  exact_mod_cast h4
 by_cases j0:(#S:O)^(1/8:O)/2<=(#(I1.biUnion Vs):O)
 .
  exact q0i h9 h8 H S U d I1 Vs (h3.trans hd) hdn hexp
   j9 jb h6 j1 h5 j3 h7 hUcard
   (λ i hi=>hVsub i (h2 hi)) (λ i hi j hj j8=>hVdisj i (h2 hi) j (h2 hj) j8)
   (λ i hi=>hVsize i (h2 hi)) (λ i hi=>hVnb i (h2 hi))
   (λ i hi=>(pF hi).2) j0
 .
  exact q0j h9 h8 H S U d I2 Vs (h3.trans hd) hdn hexp
   j9 j7 j4 jc j6 j2 j5 hUcard
   (λ i hi=>hVsub i (h0 hi)) (λ i hi j hj j8=>hVdisj i (h0 hi) j (h0 hj) j8)
   (λ i hi=>(hVsize i (h0 hi)).1) (λ i hi=>hVnb i (h0 hi))
   (λ i hi=>hVdeg i (h0 hi))
   (λ i hi=>by
    have hnot:¬ ((log (#S:O))^(1/10:O)<=(#(Vs i):O)):=λ h =>
     (pS hi).2 (rF ⟨h0 hi,h⟩)
    linarith)
   (by linarith)
lemma q0l (i:ℕ) {l:O} (hℓ:1<=l) : l^((1/2:O)^i) - (l - 1)^((1/2:O)^i)<=l^(-1+(1/2:O)^i):=by
 induction i with
 | zero=>simp
 | succ i ih =>
  set p:O:=(1/2:O)^(i+1)
  have h3:0 < p:=by positivity
  have h9:p+p=(1/2:O)^i:=by
   dsimp only[p];rw[pow_succ];ring
  set a:=l^p;set b:=(l - 1)^p;have h4:0 < a:=rpow_pos_of_pos (by linarith) p;have hb_nn:0<=b:=rNn (by linarith) p;have hba:b<=a:=rLl (by linarith) (by linarith) h3.le
  have ha2:a*a=l^((1/2:O)^i):=by
   dsimp only[a];rw[<- rpow_add (by linarith),h9]
  have hb2:b*b=(l - 1)^((1/2:O)^i):=by
   rcases eq_or_lt_of_le (show (0:O)<=l - 1 by linarith) with h0 | h7
   . have hl1:l - 1=0:=h0.symm;dsimp only[b];rw[hl1,Real.zero_rpow h3.ne',Real.zero_rpow (by positivity),mul_zero]
   . dsimp only[b];rw[<- rpow_add h7,h9]
  have h5:a*(a - b)<=l^(-1+(1/2:O)^i):=by
   have h1:a*(a - b)<=(a+b)*(a - b):=by nlinarith
   have h2:(a+b)*(a - b)=a*a - b*b:=by ring
   linarith
  have h8:a - b<=l^(-1+(1/2:O)^i)/a:=(le_div_iff₀' h4).mpr h5
  have h6:l^(-1+(1/2:O)^i)/a=l^(-1+p):=by
   dsimp only[a];rw[<- Real.rpow_sub (by linarith)];congr 1;linarith
  rwa [h6] at h8
lemma q0m {e2:O} {k:ℕ} (he20:0 < e2) (he21:e2 < 1/5) : ∃ d2:ℕ,100<=d2/\(exp 10<=(d2:O)) /\ (∀ x:O,(d2:O)<=x -> 4*((log x)^16+1)<=x/(log x)^10 /\ (10:O)<=(log x)^10) /\ (∀ n d:ℕ,d2<=d->d<=n -> (log (n:O))^k < exp (((floor ((log (log (n:O)))^20):ℕ):O)^(1/16:O)) /\ (log (n:O))^k<=exp ((log (log (n:O)))^2) /\ 1<=floor ((log (log (n:O)))^20) /\ e2*(d:O)<=(d:O) - (d:O)/2 - e2*(d:O)/10 - 4):=by
 have h0:Filter.Tendsto (λ x:O=>log (log x)) atTop atTop :=
  tL.comp tL
 have h6:∀ᶠ x:O in atTop,
   4*((log x)^16+1)<=x/(log x)^10 /\
   (10:O)<=(log x)^10 /\
   exp 10<=x:=by
  filter_upwards [q01 (C:=8) 26 (β:=1) (by norm_num),
   lGe 2,eGe (exp 10)] with x h26 hl hexp
  rw[r1] at h26;have hl16:1<=(log x)^16:=oLp (by linarith)
  have j4:10<=(log x)^10:=by
   calc
    (10:O)<=2^10:=by norm_num
    _<=(log x)^10:=pLl (by norm_num) hl 10
  refine ⟨?_,j4,hexp⟩;rw[lDi (by positivity)]
  have:4*((log x)^16+1)*(log x)^10<=8*(log x)^26:=by
   have j3:=mlR (show 4*((log x)^16+1)<=8*(log x)^16 by linarith)
    (show (0:O)<=(log x)^10 by positivity)
   linarith [show 8*(log x)^16*(log x)^10=8*(log x)^26 by ring]
  linarith
 have h7:∀ᶠ x:O in atTop,
   (log x)^k < exp (((log (log x))^20 - 1)^(1/16:O)) /\
   (log x)^k<=exp ((log (log x))^2) /\
   (2:O)<=(log (log x))^20 /\
   e2*x<=x - x/2 - e2*x/10 - 4:=by
  have h3:∀ᶠ x:O in atTop,
    2*((k:O)+1)*log (log x) < ((log (log x))^20/2)^(1/16:O):=by
   filter_upwards [h0.eventually_ge_atTop (max 4 ((4*((k:O)+1))^(4:ℕ)))] with x hll
   set t:=log (log x);have ht4:4<=t:=lT (lMl _ _) hll;have htk:(4*((k:O)+1))^(4:ℕ)<=t:=lT (lMr _ _) hll
   have j1:4*((k:O)+1)<=t^(1/4:O):=by
    have h:=rLl (by positivity) htk (show (0:O)<=1/4 by norm_num);rw[<- rN,<- rpow_mul (by positivity)] at h;norm_num at h;exact h
   have hhalf:(1/2:O) < (1/2:O)^(1/16:O):=by
    calc
     (1/2:O)=(1/2:O)^(1:O):=(r1 _).symm
     _ < (1/2:O)^(1/16:O) :=
       Real.rpow_lt_rpow_of_exponent_gt (by norm_num) (by norm_num) (by norm_num)
   have h5:(t^20/2)^(1/16:O)=(1/2:O)^(1/16:O)*(t*t^(1/4:O)):=by
    have j0:(t^(20:ℕ))^(1/16:O)=t*t^(1/4:O):=by
     rw[<- rN t 20,<- rpow_mul (by linarith)];rw[<- Real.rpow_one_add' (by linarith:0<=t) (by norm_num)];norm_num
    rw[div_eq_mul_inv,Real.mul_rpow (by positivity) (by positivity),mul_comm,j0,<- one_div]
   rw[h5]
   have h1:4*((k:O)+1)*t<=t*t^(1/4:O):=by
    rw[mul_comm t];exact mlR j1 (by linarith)
   have hpos:(0:O) < ((k:O)+1)*t:=by positivity
   nlinarith
  filter_upwards [h3,q04 (C:=1) (K:=(k:O)),
   h0.eventually_ge_atTop 2,lGe 2,
   eGe (100/(1/2 - 11/10*e2)+1)] with x hbig hpoly hll hl hxd
  rw[one_mul,rN] at hpoly
  have h20:(2:O)<=(log (log x))^20:=by
   calc
    (2:O)<=2^20:=by norm_num
    _<=(log (log x))^20:=pLl (by norm_num) hll 20
  refine ⟨?_,hpoly,h20,?_⟩
  .
   have h2:(log x)^k=exp ((k:O)*log (log x)):=by
    rw[<- rN,rpow_def_of_pos (by linarith:0 < log x),mul_comm]
   rw[h2];apply exp_lt_exp.mpr
   have j2:(log (log x))^20/2<=(log (log x))^20 - 1:=by linarith
   have hrpow:=rLl (by positivity) j2 (show (0:O)<=1/16 by norm_num)
   have:(k:O)*log (log x)<=2*((k:O)+1)*log (log x):=by nlinarith
   linarith
  .
   have h4:0 < 1/2 - 11/10*e2:=by linarith
   have hne:(1/2 - 11/10*e2:O)≠0:=h4.ne'
   have h1:100<=(1/2 - 11/10*e2)*x:=by
    have j3:=mlL hxd h4.le
    have heq:(1/2 - 11/10*e2)*(100/(1/2 - 11/10*e2)+1) =
      100+(1/2 - 11/10*e2):=by
     rw[mul_add,mul_div_cancel₀ _ hne,mul_one]
    linarith
   linarith
 have h8:=h6.and h7;rw[eAt] at h8;obtain ⟨B,hB⟩:=h8;refine ⟨max 100 (ceil B),lMl _ _,?_,?_,?_⟩
 .
  have hB0:B<=((max 100 (ceil B):ℕ):O) :=
   (nLc B).trans (by exact_mod_cast lMr 100 (ceil B))
  exact (hB _ hB0).1.2.2
 . intro x hx;have j6:B<=x:=((nLc B).trans (by exact_mod_cast lMr 100 (ceil B))).trans hx;exact ⟨(hB x j6).1.1,(hB x j6).1.2.1⟩
 .
  intro n d hd hdn;have j5:B<=(d:O):=(nLc B).trans (by exact_mod_cast (lMr 100 (ceil B)).trans hd);have hnR:B<=(n:O):=j5.trans (by exact_mod_cast hdn);have h9:=(hB (n:O) hnR).2;have hBd:=(hB (d:O) j5).2;refine ⟨?_,h9.2.1,?_,hBd.2.2.2⟩
  . refine lL2 h9.1 (eLe.mpr (rLl (by linarith [h9.2.2.1]) ?_ (by norm_num)));linarith [nL1 ((log (log (n:O)))^20)]
  .
   exact nLf (show ((1:ℕ):O)<=(log (log (n:O)))^20 by
    push_cast;linarith [h9.2.2.1])
lemma q0n {e1 e2:O} {k:ℕ} (kp:0 < e1) (ko:e1 < 1)
  (k9:0 < e2) (kn:e2 < 1/5) :
  ∃ d0:ℕ,100<=d0/\∀ {V ι:Type*} (H:SG V) (S U:FS V) (d:ℕ)
   (I:FS ι) (As Bs Cs:ι->FS V),
   d0<=d->d<=#S ->
   qQ H S e1 (e2*(d:O)) ->
   (∀ v∈S,d<=dS H S v) ->
   U⊆S->(#U:O)<=exp ((log (log (#S:O)))^2) ->
   (#S:O)^(1/8:O)<=(#I:O) ->
   let l0:=floor ((log (log (#S:O)))^20)
   (∀ i∈I,d0<=#(As i)) ->
   (∀ i∈I,As i⊆S \ U/\Bs i⊆S \ U/\Cs i⊆S \ U/\Disjoint (Bs i∪Cs i) (As i)) ->
   (∀ i∈I,(#(Bs i):O)<=(#(As i):O)/(log (#(As i):O))^10) ->
   (∀ i∈I,q06 H (S \ (U∪Bs i)) (As i) (Cs i) 4) ->
   (∀ i∈I,∀ v∈qs H (S \ (U∪Bs i∪Cs i)) l0 (As i),
    (#(U.filter (H.Adj v)):O)<=(d:O)/2) ->
   (∀ i∈I,∀ j∈I,i≠j ->
    Disjoint (qs H (S \ (U∪Bs i∪Cs i)) l0 (As i))
         (qs H (S \ (U∪Bs j∪Cs j)) l0 (As j))) ->
   ∃ i∈I,(log (#S:O))^k<=(#(qs H (S \ (U∪Bs i∪Cs i)) l0 (As i)):O):=by
 obtain ⟨d1,jt,hnb⟩:=q0k kp ko k9 (by linarith:e2 < 1);obtain ⟨d2,_,jg,jv,k7⟩:=q0m (k:=k) k9 kn
 refine ⟨max d1 d2,lT jt (lMl _ _),
  λ{V ι} H S U d I As Bs Cs hd hdn hexp hmindeg hUS hUcard hIcard hA_d0 hABC hB_bd hC_lc hU_deg hBalls_disj=>?_⟩
 set l0:=floor ((log (log (#S:O)))^20);have hd1:d1<=d:=lT (lMl _ _) hd;have hd2:d2<=d:=lT (lMr _ _) hd;obtain ⟨j0,js,jf,hdeg_e2⟩:=k7 #S d hd2 hdn;by_contra je
 push Not at je
 let P:ι->ℕ->Prop:=λ i l =>
  1<=l/\(#(qs H (S \ (U∪Bs i∪Cs i)) l (As i)):O)<=exp ((l:O)^(1/16:O))
 have j4:∀ i∈I,∃ l,P i l:=λ i hi =>
  ⟨l0,jf,(je i hi).le.trans j0.le⟩
 let l:ι->ℕ:=λ i=>if hi:i∈I then find (j4 i hi) else 1
 let Vs:ι->FS V:=λ i=>qs H (S \ (U∪Bs i∪Cs i)) (l i - 1) (As i)
 have j5:∀ i∈I,1<=l i/\l i<=l0 /\
   (#(qs H (S \ (U∪Bs i∪Cs i)) (l i) (As i)):O)<=exp ((l i:O)^(1/16:O)):=λ i hi=>by
  have kv:=find_spec (j4 i hi);have kh:=find_min' (j4 i hi) ⟨jf,(je i hi).le.trans j0.le⟩;dsimp only[l];rw[dif_pos hi];exact ⟨kv.1,kh,kv.2⟩
 have j8:∀ i∈I,2<=l i:=λ i hi=>by
  obtain ⟨h1,_,kw⟩:=j5 i hi;by_contra ke;push Not at ke
  have km:l i=1:=by omega
  rw[km,Nat.cast_one,Real.one_rpow] at kw
  have k0:As i⊆qs H (S \ (U∪Bs i∪Cs i)) 1 (As i):=by
   have kt:As i⊆S \ (U∪Bs i∪Cs i):=by
    obtain ⟨hA,_,_,h6⟩:=hABC i hi;intro v hv;refine rS ⟨(pS (hA hv)).1,λ h=>?_⟩
    rcases pU h with h1' | hc
    .
     rcases pU h1' with hu | hb
     . exact (pS (hA hv)).2 hu
     . exact pD h6 (mUl _ hb) hv
    . exact pD h6 (mUr _ hc) hv
   have h0:qs H (S \ (U∪Bs i∪Cs i)) 0 (As i)=As i:=inter_eq_left.mpr kt
   calc
    As i=qs H (S \ (U∪Bs i∪Cs i)) 0 (As i):=h0.symm
    _⊆qs H (S \ (U∪Bs i∪Cs i)) 1 (As i):=qu H _ (Nat.zero_le 1) _
  have jd:(#(As i):O)<=(#(qs H (S \ (U∪Bs i∪Cs i)) 1 (As i)):O):=by
   exact_mod_cast cL k0
  have hA_le:(#(As i):O)<=exp 1:=jd.trans kw
  have h7:(d2:O)<=(#(As i):O):=by
   exact_mod_cast (lMr d1 d2).trans (hA_d0 i hi)
  have:exp 1 < exp 10:=exp_lt_exp.mpr (by norm_num)
  linarith
 have ji:∀ i∈I,exp (((l i - 1:ℕ):O)^(1/16:O)) < (#(Vs i):O):=λ i hi=>by
  have h2:=j8 i hi
  have ke:l i - 1 < find (j4 i hi):=by
   have:l i=find (j4 i hi):=dif_pos hi
   omega
  have jy:=Nat.find_min (j4 i hi) ke;dsimp only[P] at jy
  push Not at jy
  exact jy (by omega)
 have h8:∀ i∈I,As i⊆Vs i:=λ i hi=>by
  have kt:As i⊆S \ (U∪Bs i∪Cs i):=by
   obtain ⟨hA,_,_,h6⟩:=hABC i hi;intro v hv;refine rS ⟨(pS (hA hv)).1,λ h=>?_⟩
   rcases pU h with h1' | hc
   .
    rcases pU h1' with hu | hb
    . exact (pS (hA hv)).2 hu
    . exact pD h6 (mUl _ hb) hv
   . exact pD h6 (mUr _ hc) hv
  have h0:qs H (S \ (U∪Bs i∪Cs i)) 0 (As i)=As i:=inter_eq_left.mpr kt;rw[<- h0];exact qu H _ (Nat.zero_le _) _
 have h3:∀ i∈I,Vs i⊆qs H (S \ (U∪Bs i∪Cs i)) l0 (As i):=λ i hi =>
  qu H _ (by have:=(j5 i hi).2.1;omega) _
 have jo:∀ i∈I,Vs i⊆S \ U:=λ i _ =>
  (qt H _ _ _).trans (λ v hv=>by
   obtain ⟨h1,h2⟩:=pS hv
   exact rS ⟨h1,λ hu=>h2 (mUl _ (mUl _ hu))⟩)
 have jp:∀ i∈I,∀ j∈I,i≠j->Disjoint (Vs i) (Vs j):=λ i hi j hj hij =>
  (hBalls_disj i hi j hj hij).mono (h3 i hi) (h3 j hj)
 have jz:∀ i∈I,e2*(d:O)<=(#(Vs i):O) /\
   (#(Vs i):O)<=exp ((log (log (#S:O)))^2):=by
  intro i hi;constructor
  .
   by_cases jq:e2*(d:O)<=(#(As i):O)
   . exact jq.trans (by exact_mod_cast cL (h8 i hi))
   .
    push Not at jq
    have h2:=j8 i hi
    have ju:qs H (S \ (U∪Bs i∪Cs i)) 1 (As i)⊆Vs i :=
     qu H _ (by omega) _
    have kr:(As i).Nonempty:=card_pos.mp (by have:=hA_d0 i hi;omega);obtain ⟨a,ha⟩:=kr;have haV:a∈qs H (S \ (U∪Bs i∪Cs i)) l0 (As i):=h3 i hi (h8 i hi ha);have ky:a∈S:=(pS ((hABC i hi).1 ha)).1
    have j7:(S.filter (H.Adj a)) \ (U∪Bs i∪(qn H (S \ (U∪Bs i)) (As i)∩Cs i)) ⊆
      qs H (S \ (U∪Bs i∪Cs i)) 1 (As i):=by
     intro v hv;obtain ⟨hv1,h9⟩:=pS hv;obtain ⟨k3,kx⟩:=pF hv1;have k2:v ∉ U:=λ h=>h9 (mUl _ (mUl _ h))
     have k1:v ∉ Bs i:=λ h=>h9 (mUl _ (mUr _ h))
     have kd:v ∉ Cs i:=by
      intro hc;have hvA:v ∉ As i:=λ ha'=>pD (hABC i hi).2.2.2 (mUr _ hc) ha'
      have ki:v∈qn H (S \ (U∪Bs i)) (As i)∩Cs i :=
       rI ⟨(qo H (S \ (U∪Bs i)) (As i) v).mpr
        ⟨rS ⟨k3,λ h=>by rcases mem_union.mp h with h' | h';exact k2 h';exact k1 h'⟩,
          hvA,a,ha,kx⟩,hc⟩
      exact h9 (mUr _ ki)
     have hvF:v∈S \ (U∪Bs i∪Cs i):=rS ⟨k3,λ h=>by
      rcases mem_union.mp h with h1' | hc;rcases mem_union.mp h1' with hu | hb
      exact k2 hu;exact k1 hb;exact kd hc⟩
     by_cases k4:v∈As i∩(S \ (U∪Bs i∪Cs i))
     . exact mUl _ k4
     .
      have haF:a∈S \ (U∪Bs i∪Cs i):=by
       obtain ⟨hA,_,_,h6⟩:=hABC i hi;refine rS ⟨ky,λ h=>?_⟩
       rcases mem_union.mp h with h1' | hc
       .
        rcases mem_union.mp h1' with hu | hb
        . exact (pS (hA ha)).2 hu
        . exact pD h6 (mUl _ hb) ha
       . exact pD h6 (mUr _ hc) ha
      exact mUr _ ((qo H (S \ (U∪Bs i∪Cs i)) _ v).mpr
       ⟨hvF,k4,a,rI ⟨ha,haF⟩,kx⟩)
    have kb:#(qn H (S \ (U∪Bs i)) (As i)∩Cs i)<=4:=by
     have k8:=hC_lc i hi 1 le_rfl;simp only[Nat.sub_self,mul_one] at k8
     have kc:qs H ((S \ (U∪Bs i)) \ Cs i) 0 (As i)=As i:=by
      apply inter_eq_left.mpr;intro v hv;obtain ⟨hA,_,_,h6⟩:=hABC i hi;refine rS ⟨rS ⟨(pS (hA hv)).1,λ h=>?_⟩,λ hc=>?_⟩
      .
       rcases mem_union.mp h with hu | hb
       . exact (pS (hA hv)).2 hu
       . exact pD h6 (mUl _ hb) hv
      . exact pD h6 (mUr _ hc) hv
     rwa [kc] at k8
    have hB_le:(#(Bs i):O)<=e2*(d:O)/10:=by
     have ks:(d2:O)<=(#(As i):O):=by exact_mod_cast (lMr d1 d2).trans (hA_d0 i hi)
     have h10:=(jv (#(As i):O) ks).2;have h1:=hB_bd i hi
     have h2:(#(As i):O)/(log (#(As i):O))^10<=(#(As i):O)/10 :=
      dLl (nCn _) (by norm_num) h10
     linarith
    have ja:#(S.filter (H.Adj a)) <=
      #(Vs i)+#(U.filter (H.Adj a))+#(Bs i) +
       #(qn H (S \ (U∪Bs i)) (As i)∩Cs i):=by
     have jx:S.filter (H.Adj a) ⊆
       Vs i∪U.filter (H.Adj a)∪Bs i∪(qn H (S \ (U∪Bs i)) (As i)∩Cs i):=by
      intro v hv
      by_cases h1:v∈U∪Bs i∪(qn H (S \ (U∪Bs i)) (As i)∩Cs i)
      .
       rcases mem_union.mp h1 with h2' | hc
       .
        rcases mem_union.mp h2' with hu | hb
        .
          exact mUl _ (mUl _ (mUr _
           (rF ⟨hu,(pF hv).2⟩)))
        . exact mUl _ (mUr _ hb)
       . exact mUr _ hc
      .
       exact mUl _ (mUl _ (mUl _
        (ju (j7 (rS ⟨hv,h1⟩)))))
     calc
      #(S.filter (H.Adj a))
       <= #(Vs i∪U.filter (H.Adj a)∪Bs i∪(qn H (S \ (U∪Bs i)) (As i)∩Cs i)) :=
        cL jx
      _<=#(Vs i∪U.filter (H.Adj a)∪Bs i)+#(qn H (S \ (U∪Bs i)) (As i)∩Cs i) :=
        cUl _ _
      _<=#(Vs i∪U.filter (H.Adj a))+#(Bs i)+#(qn H (S \ (U∪Bs i)) (As i)∩Cs i):=by
        linarith [cUl (Vs i∪U.filter (H.Adj a)) (Bs i)]
      _<=#(Vs i)+#(U.filter (H.Adj a))+#(Bs i)+#(qn H (S \ (U∪Bs i)) (As i)∩Cs i):=by
        linarith [cUl (Vs i) (U.filter (H.Adj a))]
    have hdegR:(d:O)<=(#(Vs i):O)+(#(U.filter (H.Adj a)):O) +
      (#(Bs i):O)+(#(qn H (S \ (U∪Bs i)) (As i)∩Cs i):O):=by
     exact_mod_cast (hmindeg a ky).trans ja
    have hUa:=hU_deg i hi a haV
    have hCR:(#(qn H (S \ (U∪Bs i)) (As i)∩Cs i):O)<=4:=by exact_mod_cast kb
    linarith
  .
   have h1:(#(Vs i):O)<=(#(qs H (S \ (U∪Bs i∪Cs i)) l0 (As i)):O):=by
    exact_mod_cast cL (h3 i hi)
   exact (h1.trans (je i hi).le).trans js
 have kq:∀ i∈I,(#(qn H (S \ U) (Vs i)):O) <=
   5*(#(Vs i):O)/(log (#(Vs i):O))^10:=by
  intro i hi;have h2:=j8 i hi;have j1:=j5 i hi;have jw:=ji i hi
  have j6:(#(As i):O)<=(#(Vs i):O):=by
   exact_mod_cast cL (h8 i hi)
  have h7:(d2:O)<=(#(As i):O):=by
   exact_mod_cast (lMr d1 d2).trans (hA_d0 i hi)
  have j3:exp 10<=(#(Vs i):O):=jg.trans (h7.trans j6);have jb:(0:O) < (#(Vs i):O):=lL2 (ePp 10) j3
  have hlogV_ge10:10<=log (#(Vs i):O):=by
   have:=lLl (ePp 10) j3;rwa [log_exp] at this
  have hpart1:(#(qn H (S \ (U∪Bs i∪Cs i)) (Vs i)):O) <=
    2*(#(Vs i):O)/(log (#(Vs i):O))^10:=by
   have k5:(#(qs H (S \ (U∪Bs i∪Cs i)) (l i) (As i)):O) =
     (#(Vs i):O)+(#(qn H (S \ (U∪Bs i∪Cs i)) (Vs i)):O):=by
    have h:=qx H (S \ (U∪Bs i∪Cs i)) (l i - 1) (As i);rw[show l i - 1+1=l i by omega] at h;exact_mod_cast h
   have j9:(1:O)<=(l i:O):=by exact_mod_cast (show 1<=l i by omega)
   have hpe:=q0l 4 j9
   have h16:(1/2:O)^(4:ℕ)=1/16:=by norm_num
   rw[h16] at hpe
   have j2:((l i - 1:ℕ):O)=(l i:O) - 1:=by
    rw[Nat.cast_sub (by omega:1<=l i),Nat.cast_one]
   have jm:(l i:O)^(1/16:O) - ((l i - 1:ℕ):O)^(1/16:O) <=
     1/((l i:O)^(1/16:O))^10:=by
    rw[j2]
    have h1:(l i:O)^(-1+1/16:O)<=(l i:O)^(-10/16:O) :=
     rLe j9 (by norm_num)
    have h2:(l i:O)^(-10/16:O)=1/((l i:O)^(1/16:O))^10:=by
     rw[<- rN,<- rpow_mul (by linarith),one_div,<- Real.rpow_neg (by linarith)];congr 1;norm_num
    linarith
   have jl:0<=(l i:O)^(1/16:O) - ((l i - 1:ℕ):O)^(1/16:O):=by
    have kk:((l i - 1:ℕ):O)<=(l i:O):=by rw[j2];linarith
    have:=rLl (nCn _) kk (show (0:O)<=1/16 by norm_num)
    linarith
   have jh:(l i:O)^(1/16:O) - ((l i - 1:ℕ):O)^(1/16:O)<=1:=by
    have h1:(1:O)<=((l i:O)^(1/16:O))^10:=oLp (Real.one_le_rpow j9 (by norm_num))
    have h2:1/((l i:O)^(1/16:O))^10<=1:=by rw[div_le_one (by positivity)];exact h1
    linarith
   have hexp_diff:exp ((l i:O)^(1/16:O))/exp (((l i - 1:ℕ):O)^(1/16:O)) - 1 <=
     2/((l i:O)^(1/16:O))^10:=by
    rw[<- Real.exp_sub]
    have h2:2*((l i:O)^(1/16:O) - ((l i - 1:ℕ):O)^(1/16:O)) <=
      2/((l i:O)^(1/16:O))^10:=by
     have:=mlL jm (by norm_num:(0:O)<=2)
     rwa [mul_one_div] at this
    exact (qY jl jh).trans h2
   have jk:log (#(Vs i):O)<=(l i:O)^(1/16:O):=by
    have jc:(#(Vs i):O)<=exp ((l i:O)^(1/16:O)):=by
     linarith [nCn (α:=O) #(qn H (S \ (U∪Bs i∪Cs i)) (Vs i)),j1.2.2]
    have:=lLl jb jc
    rwa [log_exp] at this
   have k6:(#(qs H (S \ (U∪Bs i∪Cs i)) (l i) (As i)):O)/(#(Vs i):O) - 1 <=
     2/(log (#(Vs i):O))^10:=by
    have h1:(#(qs H (S \ (U∪Bs i∪Cs i)) (l i) (As i)):O)/(#(Vs i):O) <=
      exp ((l i:O)^(1/16:O))/exp (((l i - 1:ℕ):O)^(1/16:O)) :=
     div_le_div₀ (ePp _).le j1.2.2 (ePp _) jw.le
    have h2:2/((l i:O)^(1/16:O))^10<=2/(log (#(Vs i):O))^10 :=
     dLl (by norm_num) (by positivity) (pLl (by linarith) jk 10)
    linarith
   have kg:=mlR k6 jb.le
   have kj:((#(qs H (S \ (U∪Bs i∪Cs i)) (l i) (As i)):O)/(#(Vs i):O) - 1)*(#(Vs i):O) =
     (#(qn H (S \ (U∪Bs i∪Cs i)) (Vs i)):O):=by
    rw[sub_mul,div_mul_cancel₀ _ jb.ne',one_mul,k5];ring
   rw[kj] at kg
   linarith [show 2/(log (#(Vs i):O))^10*(#(Vs i):O) =
     2*(#(Vs i):O)/(log (#(Vs i):O))^10 by ring]
  have hpart2:(#(qn H (S \ (U∪Bs i)) (Vs i)∩Cs i):O) <=
    (#(Vs i):O)/(log (#(Vs i):O))^10:=by
   have jr:(S \ (U∪Bs i)) \ Cs i=S \ (U∪Bs i∪Cs i):=by
    ext v;simp only[mS,mU];tauto
   have k8:=hC_lc i hi (l i) (by omega);rw[jr] at k8
   have kl:(#(qn H (S \ (U∪Bs i)) (Vs i)∩Cs i):O)<=4*(l i:O):=by
    exact_mod_cast k8
   have hl_ub:(l i:O)<=(log (#(Vs i):O))^16+1:=by
    have h1:((l i - 1:ℕ):O)^(1/16:O)<=log (#(Vs i):O):=by
     have:=lLl (ePp _) jw.le;rwa [log_exp] at this
    have h2:=pLl (rNn (nCn _) _) h1 16;rw[<- rN,<- rpow_mul (nCn _)] at h2;norm_num at h2;rw[Nat.cast_sub (by omega:1<=l i),Nat.cast_one] at h2;linarith
   exact kl.trans ((by linarith:4*(l i:O)<=4*((log (#(Vs i):O))^16+1)).trans
    (jv (#(Vs i):O) (h7.trans j6)).1)
  have hpart3:(#(Bs i):O)<=(#(Vs i):O)/(log (#(Vs i):O))^10 :=
   (hB_bd i hi).trans (qZ (jg.trans h7) j6)
  have jx:qn H (S \ U) (Vs i) ⊆
    qn H (S \ (U∪Bs i∪Cs i)) (Vs i)∪Bs i∪(qn H (S \ (U∪Bs i)) (Vs i)∩Cs i):=by
   intro v hv;obtain ⟨kf,h9,u,hu,ku⟩:=(qo H (S \ U) (Vs i) v).mp hv;obtain ⟨k3,k2⟩:=pS kf
   by_cases k1:v∈Bs i
   . exact mUl _ (mUr _ k1)
   .
    by_cases kd:v∈Cs i
    .
     exact mUr _ (rI ⟨(qo H (S \ (U∪Bs i)) (Vs i) v).mpr
      ⟨rS ⟨k3,λ h=>by rcases mem_union.mp h with h' | h';exact k2 h';exact k1 h'⟩,
       h9,u,hu,ku⟩,kd⟩)
    .
     exact mUl _ (mUl _ ((qo H (S \ (U∪Bs i∪Cs i)) (Vs i) v).mpr
      ⟨rS ⟨k3,λ h=>by
       rcases mem_union.mp h with h1' | hc;rcases mem_union.mp h1' with hu' | hb'
       exact k2 hu';exact k1 hb';exact kd hc⟩,h9,u,hu,ku⟩))
  have jn:#(qn H (S \ U) (Vs i)) <=
    #(qn H (S \ (U∪Bs i∪Cs i)) (Vs i))+#(Bs i) +
     #(qn H (S \ (U∪Bs i)) (Vs i)∩Cs i) :=
   (cL jx).trans ((cUl _ _).trans
    (Nat.add_le_add_right (cUl _ _) _))
  have hcardR:(#(qn H (S \ U) (Vs i)):O) <=
    (#(qn H (S \ (U∪Bs i∪Cs i)) (Vs i)):O)+(#(Bs i):O) +
     (#(qn H (S \ (U∪Bs i)) (Vs i)∩Cs i):O):=by exact_mod_cast jn
  have hnn:(0:O)<=(#(Vs i):O)/(log (#(Vs i):O))^10 :=
   div_nonneg (nCn _) (pow_nonneg (by linarith) 10)
  have hsum5:2*(#(Vs i):O)/(log (#(Vs i):O))^10 +
    (#(Vs i):O)/(log (#(Vs i):O))^10 +
    (#(Vs i):O)/(log (#(Vs i):O))^10 <=
    5*(#(Vs i):O)/(log (#(Vs i):O))^10:=by
   have h4:2*(#(Vs i):O)/(log (#(Vs i):O))^10 +
     (#(Vs i):O)/(log (#(Vs i):O))^10 +
     (#(Vs i):O)/(log (#(Vs i):O))^10 =
     4*(#(Vs i):O)/(log (#(Vs i):O))^10:=by ring
   have h5:5*(#(Vs i):O)/(log (#(Vs i):O))^10 =
     4*(#(Vs i):O)/(log (#(Vs i):O))^10 +
     (#(Vs i):O)/(log (#(Vs i):O))^10:=by ring
   linarith
  linarith
 have ka:∀ i∈I,∀ v∈Vs i,(#(U.filter (H.Adj v)):O)<=(d:O)/2:=λ i hi v hv =>
  hU_deg i hi v (h3 i hi hv)
 have ke:=hnb H S U d I Vs hd1 hdn hexp hUS hUcard jo jp jz kq ka
 have jj:#I<=#(I.biUnion Vs):=by
  rw[card_biUnion (λ i hi j hj hij=>jp i hi j hj hij)]
  calc
   #I=∑ _i∈I,1:=by simp
   _<=∑ i∈I,#(Vs i):=sum_le_sum λ i hi =>
     (show 1<=#(As i) by have:=hA_d0 i hi;omega).trans (cL (h8 i hi))
 have hIR:(#I:O)<=(#(I.biUnion Vs):O):=by exact_mod_cast jj
 linarith
lemma q0o {V:Type*} {G:SG V} {T:FS V} {u v:V}
 (h:G.Adj u v) (hu:u∈T) (hv:v∈T):(q3 G T).Adj u v:=⟨h,hu,hv⟩
lemma q0p {V:Type*} {G:SG V} {u v u' v':V} {p:G.Walk u v} (hp:p.IsPath) (hu:u=u') (hv:v=v'):(p.copy hu hv).IsPath:=by rw[wIp,support_copy];exact hp.support_nodup
lemma q0q {V:Type*} {G:SG V} {u v w:V} {p:G.Walk u v} : w∈p.reverse.support↔w∈p.support:=by rw[support_reverse,mem_reverse]
def q0r {V:Type*} {G:SG V} {S T:FS V} {u v:V}
  (p:(q3 G S).Walk u v) (h:∀ w∈p.support,w∈T):(q3 G T).Walk u v :=
 match p with
 | .nil => .nil
 | .cons hadj p' =>
  .cons (q0o hadj.1 (h _ (by simp)) (h _ (by simp)))
   (q0r p' (λ w hw=>h w (by simp [hw])))
lemma q0s {V:Type*} {G:SG V} {S T:FS V} {u v:V} (p:(q3 G S).Walk u v) (h:∀ w∈p.support,w∈T) : (q0r p h).support=p.support:=by
 induction p with
 | nil=>rfl
 | cons hadj p' ih=>simp only[q0r,support_cons];rw[ih]
lemma q0t {V:Type*} {G:SG V} {S T:FS V} {u v:V} (p:(q3 G S).Walk u v) (h:∀ w∈p.support,w∈T) : (q0r p h).length=p.length:=by
 induction p with
 | nil=>rfl
 | cons hadj p' ih=>simp only[q0r,length_cons];rw[ih]
lemma q0u {V:Type*} {G:SG V} {S T:FS V} {u v:V} (p:(q3 G S).Walk u v) (h:∀ w∈p.support,w∈T) : (q0r p h).edges=p.edges:=by
 induction p with
 | nil=>rfl
 | cons hadj p' ih=>simp only[q0r,Walk.edges_cons];rw[ih]
lemma q0v {V:Type*} {G:SG V} {S T:FS V} {u v:V} (p:(q3 G S).Walk u v) (h:∀ w∈p.support,w∈T) (hp:p.IsPath) : (q0r p h).IsPath:=by rw[wIp,q0s];exact hp.support_nodup
lemma q0w {V:Type*} {G:SG V} {S:FS V} {u v:V} (p:(q3 G S).Walk u v) (hu:u∈S) : ∀ w∈p.support,w∈S:=by
 induction p with
 | nil=>intro w hw;simp at hw;subst hw;exact hu
 | cons hadj p' ih =>
  intro w hw;simp only[support_cons,List.mem_cons] at hw
  rcases hw with rfl | hw'
  . exact hadj.2.1
  . exact ih hadj.2.2 w hw'
lemma q0x {V:Type*} {G:SG V} {u v w:V} (p:G.Walk u v) (q:G.Walk v w) (hp:p.IsPath) (hq:q.IsPath) (h2:∀ z∈p.support,z∈q.support->z=v) : (p.append q).IsPath:=by
 rw[wIp,support_append,nodup_append];have h0:q.support=v :: q.support.tail:=(cons_tail_support q).symm;have h1:=hq.support_nodup;rw[h0,nodup_cons] at h1;refine ⟨hp.support_nodup,h1.2,λ a ha b hb hab=>?_⟩
 subst hab;have hav:a=v:=h2 a ha (by rw[h0];exact List.mem_cons_of_mem v hb);exact h1.1 (hav ▸ hb)
lemma q0y {V:Type*} {G:SG V} {u v:V} (p:G.Walk u v):p.support.toFinset.card<=p.length+1:=by
 calc
  p.support.toFinset.card<=p.support.length:=toFinset_card_le _
  _=p.length+1:=wLs p
def q0z {V:Type*} (H:SG V) (S:FS V)
  (v:V) (D m:ℕ) (F:FS V):Prop :=
 F⊆S/\v∈F/\#F=D/\F⊆qs H F m {v}
lemma q0A {V:Type*} {H:SG V} {S S':FS V}
  {v:V} {D m:ℕ} {F:FS V} (h:q0z H S v D m F) (hSS':S⊆S') :
  q0z H S' v D m F :=
 ⟨h.1.trans hSS',h.2.1,h.2.2.1,h.2.2.2⟩
lemma q0B {V:Type*} {H:SG V} {S:FS V}
  {v:V} {D m m':ℕ} {F:FS V} (h:q0z H S v D m F) (hmm':m<=m') :
  q0z H S v D m' F :=
 ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.trans (qu H F hmm' {v})⟩
lemma q0C {V:Type*} {H:SG V} {S:FS V} {v:V} {D m:ℕ} {F:FS V} (h:q0z H S v D m F) {u:V} (hu:u∈F) : ∃ p:(q3 H F).Walk v u,p.IsPath/\p.length<=m:=by obtain ⟨a,ha,p,hp,h0,_⟩:=qB (h.2.2.2 hu);have hav:a=v:=pSg (pI ha).1;subst hav;exact ⟨p,hp,h0⟩
lemma q0D {V:Type*} (H:SG V) (S:FS V) (r:ℕ) {v:V} (hv:v∈S) : q0z H S v #(qs H S r {v}) r (qs H S r {v}):=by
 refine ⟨qt H S r {v},?_,rfl,?_⟩
 . have h0:v∈qs H S 0 {v}:=rI ⟨mSs v,hv⟩;exact qu H S (Nat.zero_le r) {v} h0
 . intro u hu;obtain ⟨a,ha,p,_,h3,h1⟩:=qB hu;have hav:a=v:=pSg (pI ha).1;subst hav;let hq:=q0r p h1;have h2:=qA (mSs a) (h1 a (wSm p)) hq;dsimp only[hq] at h2;rw[q0t] at h2;exact qu H _ h3 _ h2
lemma q0E {V:Type*} {H:SG V} {S:FS V} {v:V} {D m:ℕ} {F:FS V} (h:q0z H S v D m F) {D':ℕ} (hD'1:1<=D') (hD'le:D'<=D) : ∃ F'⊆F,q0z H S v D' m F':=by
 suffices hstep:∀ k:ℕ,∀ F0:FS V,q0z H S v (D'+k) m F0 ->
   ∃ F'⊆F0,q0z H S v D' m F' by
  have hEq:D=D'+(D - D'):=by omega
  rw[hEq] at h;exact hstep (D - D') F h
 intro k
 induction k with
 | zero =>
  intro F0 jd;rw[Nat.add_zero] at jd;exact ⟨F0,sR,jd⟩
 | succ k ih =>
  intro F0 jd;obtain ⟨jg,h5,j2,h7⟩:=jd;have h9:∀ u∈F0,∃ r,u∈qs H F0 r {v}:=λ u hu=>⟨m,h7 hu⟩
  let h3:V->ℕ:=λ u=>if hu:u∈F0 then find (h9 u hu) else 0
  have h2:∀ u∈F0,u∈qs H F0 (h3 u) {v}:=λ u hu=>by
   dsimp only[h3];rw[dif_pos hu];exact find_spec (h9 u hu)
  have h1:∀ u∈F0,∀ r,u∈qs H F0 r {v}->h3 u<=r:=λ u hu r hr=>by
   dsimp only[h3];rw[dif_pos hu];exact find_min' (h9 u hu) hr
  have h6:∀ u∈F0,h3 u<=m:=λ u hu=>h1 u hu m (h7 hu)
  obtain ⟨w,j9,j3⟩:=exists_max_image F0 h3 ⟨v,h5⟩
  have jh:w≠v:=by
   intro heq
   have hcard2:2<=#F0:=by omega
   have j5:(F0.erase v).Nonempty:=card_pos.mp (by rw[card_erase_of_mem h5];omega);obtain ⟨u,hu⟩:=j5;obtain ⟨huv,h8⟩:=mem_erase.mp hu
   have hdu_pos:1<=h3 u:=by
    by_contra h0;push Not at h0
    have jf:h3 u=0:=by omega
    have ji:=h2 u h8;rw[jf] at ji;exact huv (pSg (pI ji).1)
   have hdw0:h3 w=0:=by
    rw[heq];exact Nat.eq_zero_of_le_zero (h1 v h5 0 (rI ⟨mSs v,h5⟩))
   have:=j3 u h8
   omega
  let F1:=F0.erase w
  have j1:q0z H S v (D'+k) m F1:=by
   refine ⟨(Finset.erase_subset w F0).trans jg,mem_erase.mpr ⟨jh.symm,h5⟩,
    by rw[card_erase_of_mem j9,j2];omega,?_⟩
   intro u hu;obtain ⟨huw,h8⟩:=mem_erase.mp hu;obtain ⟨a,ha,p,_,jb,j4⟩:=qB (h2 u h8);have hav:a=v:=pSg (pI ha).1;subst hav
   have h4:w ∉ p.support:=by
    intro j8;let q:=p.takeUntil w j8
    have hqlen:q.length < p.length:=by
     have ja:=take_spec p j8
     have hadd:q.length+(p.dropUntil w j8).length=p.length:=by
      rw[<- wLa,ja]
     have hpos:0 < (p.dropUntil w j8).length:=by
      cases hd:p.dropUntil w j8 with
      | nil=>exact absurd rfl huw.symm
      | cons _ _=>simp
     omega
    have j0:w∈qs H F0 q.length {a} :=
     qA (mSs a) h5 q
    have hdw_le:=h1 w j9 q.length j0
    have:=j3 u h8
    omega
   have je:∀ z∈p.support,z∈F1:=λ z hz =>
    mem_erase.mpr ⟨λ h=>h4 (h ▸ hz),qt H F0 (h3 u) {a} (j4 z hz)⟩
   let q1:=q0r p je;have j6:=qA (mSs a) (mem_erase.mpr ⟨jh.symm,h5⟩) q1;dsimp only[q1] at j6;rw[q0t] at j6;exact qu H F1 (jb.trans (h6 u h8)) {a} j6
  obtain ⟨F',jc,j7⟩:=ih F1 j1;exact ⟨F',jc.trans (Finset.erase_subset w F0),j7⟩
lemma q0F {V:Type*} {H:SG V} {S F:FS V} {v w:V} {m1 m2:ℕ} (p:(q3 H S).Walk v w) (hvS:v∈S) (hp:p.length<=m1) (hFS:F⊆S) (hwF:w∈F) (h2:F⊆qs H F m2 {w}) : q0z H S v #(p.support.toFinset∪F) (m1+m2) (p.support.toFinset∪F):=by
 let T:=p.support.toFinset∪F
 have hTS:T⊆S:=uS
  (λ z hz=>q0w p hvS z (pTf hz)) hFS
 have h4:v∈T:=mUl _ (rT (wSm p));refine ⟨hTS,h4,rfl,λ u hu=>?_⟩
 rcases pU hu with hup | huF
 .
  have h1:u∈p.support:=pTf hup;let q:=p.takeUntil u h1
  have hqT:∀ z∈q.support,z∈T:=λ z hz =>
   mUl _ (rT (support_takeUntil_subset_support p h1 hz))
  have h3:q.length<=p.length:=by
   have hadd:q.length+(p.dropUntil u h1).length=p.length:=by
    rw[<- wLa,take_spec p h1]
   omega
  have h0:=qA (mSs v) h4 (q0r q hqT);rw[q0t] at h0;exact qu H T (by omega) {v} h0
 .
  obtain ⟨a,ha,q,_,h3,_⟩:=qB (h2 huF);have haw:a=w:=pSg (pI ha).1;subst haw;let pT:(q3 H T).Walk v a:=q0r p (λ z hz=>mUl _ (rT hz))
  let qT:(q3 H T).Walk a u:=q0r q (λ z hz=>mUr _ (q0w q hwF z hz))
  have h0:=qA (mSs v) h4 (pT.append qT);rw[wLa,q0t,q0t] at h0;exact qu H T (by omega) {v} h0
def q0G {V:Type*} (H:SG V) (S:FS V)
  (x:V) (c:(q3 H S).Walk x x):Prop :=
 c.IsCycle/\∀ (y:V) (c':(q3 H S).Walk y y),c'.IsCycle->c.length<=c'.length
lemma q0H {V:Type*} {H:SG V} {S T:FS V} {x:V} {c:(q3 H S).Walk x x} (hc:q0G H S x c) (h7:T⊆S) (h2:∀ w∈c.support,w∈T) : q0G H T x (q0r c h2):=by
 have h5:(q0r c h2).IsCycle:=by
  rw[Walk.isCycle_def];refine ⟨?_,?_,?_⟩
  . rw[Walk.isTrail_def,q0u];exact hc.1.edges_nodup
  .
   intro h0
   have h4:c.length=0:=by rw[<- q0t c h2,h0];rfl
   have:=hc.1.three_le_length;omega
  . have h1:=congrArg List.tail (q0s c h2);rw[h1];exact hc.1.support_nodup
 refine ⟨h5,λ y c' hc'=>?_⟩
 have h3:y∈T:=by
  cases c' with
  | nil=>exact absurd rfl hc'.ne_nil
  | cons hadj _=>exact hadj.2.1
 let h9:=q0r c' (λ w hw=>h7 (q0w c' h3 w hw))
 have h6:h9.IsCycle:=by
  rw[Walk.isCycle_def];refine ⟨?_,?_,?_⟩
  . rw[Walk.isTrail_def,q0u];exact hc'.edges_nodup
  .
   intro h0
   have h4:c'.length=0:=by
    rw[<- q0t c' (λ w hw=>h7 (q0w c' h3 w hw))]
    exact congrArg Walk.length h0
   have:=hc'.three_le_length;omega
  .
   have h1:=congrArg List.tail (q0s c' (λ w hw=>h7 (q0w c' h3 w hw)))
   rw[h1];exact hc'.support_nodup
 have h8:=hc.2 y h9 h6;rw[q0t] at h8 ⊢;exact h8
lemma q0I {V:Type*} {G:SG V} {a z:V} (s1 s2:G.Walk a z) (jc:s1.IsPath) (jd:s2.IsPath) (h1:1<=s1.length) (h2:1<=s2.length) (h3:3<=s1.length+s2.length) (h8:∀ w∈s1.support,w∈s2.support->w=a\/w=z) : (s1.append s2.reverse).IsCycle:=by
 have haz:a≠z:=by
  intro j5;subst j5
  cases s1 with
  | nil=>simp at h1
  | cons _ p' =>
   exact (nodup_cons.mp jc.support_nodup).1 (wEm p')
 have h6:(s1.append s2.reverse).support.tail.Nodup:=by
  rw[support_append]
  cases hs1eq:s1 with
  | nil=>simp [hs1eq] at h1
  | @cons _ u1 _ h1' p1' =>
   rw[support_cons,List.cons_append,List.tail_cons,nodup_append]
   have j2:(a :: p1'.support).Nodup:=by rw[<- support_cons h1' p1',<- hs1eq];exact jc.support_nodup
   have je:p1'.support.Nodup:=(nodup_cons.mp j2).2;have h9:a ∉ p1'.support:=(nodup_cons.mp j2).1;have h7:s2.reverse.support=z :: s2.reverse.support.tail:=(cons_tail_support s2.reverse).symm
   have h5:s2.reverse.support.Nodup:=by rw[support_reverse];exact List.nodup_reverse.mpr jd.support_nodup
   rw[h7,nodup_cons] at h5;refine ⟨je,h5.2,λ w hw1 w' hw2 j5=>?_⟩
   subst j5
   have j9:w∈s1.support:=by rw[hs1eq,support_cons];exact List.mem_cons_of_mem a hw1
   have j8:w∈s2.support:=by
    have:w∈s2.reverse.support:=by rw[h7];exact List.mem_cons_of_mem z hw2
    rwa [support_reverse,mem_reverse] at this
   rcases h8 w j9 j8 with rfl | rfl
   . exact h9 hw1
   . exact h5.1 hw2
 have j4:s1.append s2.reverse≠Walk.nil:=by
  intro h;have h0:=congrArg Walk.length h;rw[wLa,wLr] at h0;simp only[length_nil] at h0;omega
 have j0:∀ e∈s1.edges,e ∉ s2.reverse.edges:=by
  intro e j7 j6;rw[Walk.edges_reverse,mem_reverse] at j6;obtain ⟨u,v,huv⟩:∃ u v,e=s(u,v):=Sym2.exists.mp ⟨e,rfl⟩;subst huv;have hu1:u∈s1.support:=Walk.fst_mem_support_of_mem_edges s1 j7;have hv1:v∈s1.support:=Walk.snd_mem_support_of_mem_edges s1 j7;have hu2:u∈s2.support:=Walk.fst_mem_support_of_mem_edges s2 j6;have hv2:v∈s2.support:=Walk.snd_mem_support_of_mem_edges s2 j6;have j1:u≠v:=G.ne_of_adj (Walk.adj_of_mem_edges s1 j7)
  have ja:s(u,v)=s(a,z):=by
   rcases h8 u hu1 hu2 with rfl | rfl <;> rcases h8 v hv1 hv2 with rfl | rfl
   . exact absurd rfl j1
   . rfl
   . exact Sym2.eq_swap
   . exact absurd rfl j1
  have h4:∀ (p:G.Walk a z),p.IsPath->s(a,z)∈p.edges->p.length=1:=by
   intro p hp j3
   cases p with
   | nil=>simp at j3
   | @cons _ w _ hadj p' =>
    simp only[Walk.edges_cons,List.mem_cons] at j3
    rcases j3 with j5 | jf
    .
     have hwz:w=z:=by
      rw[Sym2.eq_iff] at j5
      rcases j5 with ⟨_,h2⟩ | ⟨_,h2⟩
      . exact h2.symm
      . exact absurd h2.symm haz
     subst hwz
     cases p' with
     | nil=>rfl
     | cons _ p'' =>
      exfalso;have hnd:=(nodup_cons.mp hp.support_nodup).2;exact (nodup_cons.mp hnd).1 (wEm p'')
    . exfalso;have jb:a∈p'.support:=Walk.fst_mem_support_of_mem_edges p' jf;exact (nodup_cons.mp hp.support_nodup).1 jb
  rw[ja] at j7 j6;have hl1:=h4 s1 jc j7;have hl2:=h4 s2 jd j6;omega
 rw[Walk.isCycle_def];refine ⟨?_,j4,h6⟩;rw[Walk.isTrail_def,Walk.edges_append,nodup_append]
 exact ⟨jc.edges_nodup,by rw[Walk.edges_reverse];exact List.nodup_reverse.mpr jd.edges_nodup,
  λ e j7 e' j6 j5=>j0 e j7 (j5 ▸ j6)⟩
lemma q0J {V:Type*} {G:SG V} {u v:V} (p1 p2:G.Walk u v) (hp1:p1.IsPath) (hp2:p2.IsPath) (hne:p1≠p2) : ∃ (y:V) (c:G.Walk y y),c.IsCycle/\c.length<=p1.length+p2.length:=by
 suffices h:∀ N:ℕ,∀ (a b:V) (q1 q2:G.Walk a b),
   q1.length+q2.length<=N->q1.IsPath->q2.IsPath->q1≠q2 ->
   ∃ (y:V) (c:G.Walk y y),c.IsCycle/\c.length<=q1.length+q2.length by
  exact h (p1.length+p2.length) u v p1 p2 le_rfl hp1 hp2 hne
 intro N
 induction N using Nat.strong_induction_on with
 | _ N ih =>
  intro a b q1 q2 hN j6 j9 j5
  cases q1 with
  | nil =>
   cases q2 with
   | nil=>exact absurd rfl j5
   | cons _ q2' =>
    exact absurd (wEm q2') (by simpa using (nodup_cons.mp j9.support_nodup).1)
  | @cons _ u1 _ h₁ q1' =>
   cases q2 with
   | nil =>
    exact absurd (wEm q1') (by simpa using (nodup_cons.mp j6.support_nodup).1)
   | @cons _ u2 _ h₂ q2' =>
    by_cases hu:u1=u2
    .
     subst hu;have j7:q1'≠q2':=λ h=>j5 (by rw[h])
     obtain ⟨y,c,hc,hclen⟩:=ih (q1'.length+q2'.length) (by simp at hN;omega) u1 b q1' q2'
      le_rfl j6.of_cons j9.of_cons j7
     exact ⟨y,c,hc,by simp;omega⟩
    .
     have j0:∃ i,∃ hi:i < q1'.support.length,q1'.support[i]∈q2'.support:=by
      obtain ⟨i,hi,heq⟩:=getElem_of_mem (wEm q1');exact ⟨i,hi,by rw[heq];exact wEm q2'⟩
     let i0:=find j0;obtain ⟨hi0,j3⟩:=find_spec j0;let z:=q1'.support[i0];have j1:z∈q1'.support:=getElem_mem hi0;let s1:G.Walk a z:=Walk.cons h₁ (q1'.takeUntil z j1);let s2:G.Walk a z:=Walk.cons h₂ (q2'.takeUntil z j3);have h5:a ∉ q1'.support:=(nodup_cons.mp j6.support_nodup).1;have h4:a ∉ q2'.support:=(nodup_cons.mp j9.support_nodup).1
     have h9:s1.IsPath:=by
      rw[wIp,support_cons,nodup_cons]
      exact ⟨λ h=>h5 (support_takeUntil_subset_support q1' j1 h),
       (j6.of_cons.takeUntil j1).support_nodup⟩
     have h8:s2.IsPath:=by
      rw[wIp,support_cons,nodup_cons]
      exact ⟨λ h=>h4 (support_takeUntil_subset_support q2' j3 h),
       (j9.of_cons.takeUntil j3).support_nodup⟩
     have h7:∀ w∈s1.support,w∈s2.support->w=a\/w=z:=by
      intro w jf je;simp only[s1,s2,support_cons,List.mem_cons] at jf je
      rcases jf with rfl | hw1'
      . exact Or.inl rfl
      .
       rcases je with rfl | hw2'
       . exact Or.inl rfl
       .
        right;by_contra hwz;let L1:=(q1'.takeUntil z j1).support;let L2:=(q1'.dropUntil z j1).support.tail
        have h0:L1 ++ L2=q1'.support:=by
         dsimp only[L1,L2];rw[<- support_append,take_spec q1' j1]
        have hlen_eq:L1.length+L2.length=q1'.support.length:=by
         rw[<- List.length_append,h0]
        have hL1pos:0 < L1.length:=length_pos_of_ne_nil (wSn _)
        have hL1_le:L1.length - 1 < q1'.support.length:=by omega
        have h6:q1'.support[L1.length - 1]'hL1_le=z:=by
         have h1:(L1 ++ L2)[L1.length - 1]'(by rw[h0];exact hL1_le)=L1[L1.length - 1]'(by omega) :=
          getElem_append_left (by omega)
         have h2:L1[L1.length - 1]'(by omega)=z:=by
          dsimp only[L1];rw[<- getLast_eq_getElem (wSn _)];exact wGl _
         have h3:q1'.support[L1.length - 1]'hL1_le=(L1 ++ L2)[L1.length - 1]'(by rw[h0];exact hL1_le):=by
          congr 1;exact h0.symm
         exact h3.trans (h1.trans h2)
        have hi0_eq:i0=L1.length - 1 :=
         (List.Nodup.getElem_inj_iff j6.of_cons.support_nodup).mp h6.symm
        obtain ⟨j,hj,jd⟩:=getElem_of_mem hw1';have hj':j < L1.length:=hj
        have hj_lt_last:j < L1.length - 1:=by
         by_contra hge
         have jb:j=L1.length - 1:=by omega
         have j8:L1[L1.length - 1]'(by omega)=z:=by
          dsimp only[L1];rw[<- getLast_eq_getElem (wSn _)];exact wGl _
         exact hwz (jd.symm.trans (by subst jb;exact j8))
        have hj_q1:j < q1'.support.length:=by omega
        have j4:q1'.support[j]'hj_q1=w:=by
         have jc:(L1 ++ L2)[j]'(by rw[h0];exact hj_q1)=L1[j]'hj':=getElem_append_left hj'
         have h3:q1'.support[j]'hj_q1=(L1 ++ L2)[j]'(by rw[h0];exact hj_q1):=by
          congr 1;exact h0.symm
         exact h3.trans (jc.trans jd)
        exact Nat.find_min j0 (show j < i0 by omega)
         ⟨hj_q1,by rw[j4];exact support_takeUntil_subset_support q2' j3 hw2'⟩
     have hs3:3<=s1.length+s2.length:=by
      by_contra ja;push Not at ja
      have hl1:s1.length=1:=by simp only[s1,s2,length_cons] at ja ⊢;omega
      have hl2:s2.length=1:=by simp only[s1,s2,length_cons] at ja ⊢;omega
      have jc:(q1'.takeUntil z j1).length=0:=by simp only[s1,length_cons] at hl1;omega
      have h2':(q2'.takeUntil z j3).length=0:=by simp only[s2,length_cons] at hl2;omega
      exact hu ((eq_of_length_eq_zero jc).trans (eq_of_length_eq_zero h2').symm)
     have j2:(s1.append s2.reverse).length<=(Walk.cons h₁ q1').length+(Walk.cons h₂ q2').length:=by
      rw[wLa,wLr]
      have hlt1:(q1'.takeUntil z j1).length<=q1'.length:=by
       have h:=congrArg Walk.length (take_spec q1' j1);rw[wLa] at h;exact Nat.le_of_add_right_le h.le
      have hlt2:(q2'.takeUntil z j3).length<=q2'.length:=by
       have h:=congrArg Walk.length (take_spec q2' j3);rw[wLa] at h;exact Nat.le_of_add_right_le h.le
      simp only[s1,s2,length_cons];omega
     exact ⟨a,s1.append s2.reverse,
      q0I s1 s2 h9 h8 (by simp [s1]) (by simp [s2]) hs3 h7,
      j2⟩
lemma q0K {V:Type*} (H:SG V) (S:FS V) (jp:S.Nonempty) (jo:∀ v∈S,2<=dS H S v) : ∃ (x:V) (c:(q3 H S).Walk x x),q0G H S x c:=by
 have h7:∃ L:ℕ,∃ (x:V) (c:(q3 H S).Walk x x),c.IsCycle/\c.length=L:=by
  let P:ℕ->Prop:=λ k=>∃ (u v:V) (_:u∈S) (p:(q3 H S).Walk u v),p.IsPath/\p.length=k
  have hP0:P 0:=by obtain ⟨u,hu⟩:=jp;exact ⟨u,u,hu,Walk.nil,Walk.IsPath.nil,rfl⟩
  have jq:∀ k,P k->k<=#S:=by
   rintro k ⟨u,v,hu,p,hp,rfl⟩
   have j5:p.support.toFinset⊆S:=λ w hw =>
    q0w p hu w (pTf hw)
   have h1:p.support.length=p.support.toFinset.card:=(List.toFinset_card_of_nodup hp.support_nodup).symm;have h2:=wLs p;have h3:=cL j5;omega
  let h9:=(range (#S+1)).filter P;have h5:h9.Nonempty:=⟨0,rF ⟨mem_range.mpr (Nat.zero_lt_succ _),hP0⟩⟩;let j3:=h9.max' h5;have jf:P j3:=(pF (max'_mem h9 h5)).2;obtain ⟨u,v,js,p,j0,je⟩:=jf;have jr:v∈S:=q0w p js v (wEm p);have hdegv:2<=#(S.filter (H.Adj v)):=jo v jr
  have jl:∃ w∈S.filter (H.Adj v),
    ∀ h0:0 < p.length,w≠p.support.reverse[1]'(by rw[List.length_reverse,wLs];omega):=by
   by_cases hp0:p.length=0
   . obtain ⟨w,hw⟩:=card_pos.mp (by omega:0 < #(S.filter (H.Adj v)));exact ⟨w,hw,λ h=>by omega⟩
   .
    have hlen1:1 < p.support.reverse.length:=by rw[List.length_reverse,wLs];omega
    let jc:=p.support.reverse[1]'hlen1
    have hne:((S.filter (H.Adj v)).erase jc).Nonempty:=card_pos.mp (by
     by_cases j7:jc∈S.filter (H.Adj v)
     . rw[card_erase_of_mem j7];omega
     . rw[Finset.erase_eq_of_notMem j7];omega)
    obtain ⟨w,hw⟩:=hne;obtain ⟨ja,ji⟩:=mem_erase.mp hw;exact ⟨w,ji,λ _=>ja⟩
  obtain ⟨w,ji,h8⟩:=jl;obtain ⟨hwS,jj⟩:=pF ji;have j8:(q3 H S).Adj v w:=⟨jj,jr,hwS⟩
  have h4:w∈p.support:=by
   by_contra jd;let q:=p.concat j8
   have j6:q.IsPath:=by
    rw[wIp,support_concat,<- concat_eq_append];exact j0.support_nodup.concat jd
   have jt:P (j3+1):=⟨u,w,js,q,j6,by simp [q,je]⟩;have hle:=jq (j3+1) jt;have j7:j3+1∈h9:=rF ⟨mem_range.mpr (by omega),jt⟩
   have:=le_max' h9 (j3+1) j7
   omega
  let sub:=p.dropUntil w h4;have j2:sub.IsPath:=j0.dropUntil h4
  have hsub_len2:2<=sub.length:=by
   have hwv:w≠v:=(H.ne_of_adj jj).symm;by_contra hlt;push Not at hlt
   rcases (show sub.length=0\/sub.length=1 by omega) with h0 | h1
   . exact hwv (eq_of_length_eq_zero h0)
   .
    cases j5:sub with
    | nil=>simp [j5] at h1
    | @cons _ b _ hwb sub' =>
     cases sub' with
     | nil =>
      have j9:(p.takeUntil w h4).support ++ (p.dropUntil w h4).support.tail=p.support:=by
       rw[<- support_append,take_spec p h4]
      have j1:(p.dropUntil w h4).support.tail=[v]:=by
       change sub.support.tail=[v];rw[j5];rfl
      rw[j1] at j9
      have jb:0 < p.length:=by
       have hdl:(p.dropUntil w h4).length=1:=h1;have jm:=congrArg Walk.length (take_spec p h4);rw[wLa] at jm;omega
      have j4:=wSn (p.takeUntil w h4)
      have h6:(p.takeUntil w h4).support.reverse.head?=some w:=by
       rw[List.head?_reverse,List.getLast?_eq_some_getLast j4,wGl]
      have jk:p.support.reverse=v :: (p.takeUntil w h4).support.reverse:=by
       rw[<- j9,List.reverse_append];rfl
      have jg:p.support.reverse[1]'(by rw[List.length_reverse,wLs];omega)=w:=by
       have hlen_tk:0 < (p.takeUntil w h4).support.reverse.length :=
        length_pos_of_ne_nil (by simp [j4])
       have jn:∀ (M:List V),M=v :: (p.takeUntil w h4).support.reverse->∀ h1:1 < M.length,
         M[1]'h1=(p.takeUntil w h4).support.reverse[0]'hlen_tk:=by
        rintro _ rfl _;rfl
       rw[jn p.support.reverse jk _];have h2':=List.head?_eq_some_iff.mp h6;obtain ⟨tl,htl⟩:=h2';simp [htl]
      exact h8 jb jg.symm
     | cons _ _=>simp [j5] at h1
  let c:=sub.append (Walk.cons j8.symm Walk.nil).reverse
  have hc:c.IsCycle:=by
   have h1:(Walk.cons j8.symm Walk.nil:(q3 H S).Walk w v).IsPath:=by
    rw[wIp];simp [support_cons,(H.ne_of_adj jj).symm]
   exact q0I sub (Walk.cons j8.symm Walk.nil)
    j2 h1 (by omega) (by simp) (by simp;omega)
    (λ z _ hz2=>by simp [support_cons] at hz2;exact hz2)
  exact ⟨c.length,w,c,hc,rfl⟩
 let Lmin:=find h7;obtain ⟨x,c,hc,jh⟩:=find_spec h7;exact ⟨x,c,hc,λ y c' hc'=>jh.symm ▸ find_min' h7 ⟨y,c',hc',rfl⟩⟩
lemma q0L {V:Type*} {H:SG V} {S:FS V} {x:V} {c:(q3 H S).Walk x x} (hc:q0G H S x c) {d':ℕ} (hd':3<=d') (k5:∀ v∈S,d'<=dS H S v) : (c.length:O)<=2*log (#S:O)/log ((d' - 1:ℕ):O)+2:=by
 have jr:x∈S:=by
  cases c with
  | nil=>exact absurd rfl hc.1.ne_nil
  | cons hadj _=>exact hadj.2.1
 let g:=c.length;let r:=(g - 1)/2;have hg3:3<=g:=hc.1.three_le_length
 have h2r_lt:2*r < g:=by omega
 let L:ℕ->FS V:=λ i =>
  if i=0 then {x} else qs H S i {x} \ qs H S (i - 1) {x}
 have h4:∀ i,L i⊆qs H S i {x}:=λ i=>by
  dsimp only[L];split_ifs with h0
  . subst h0;exact sSm (rI ⟨mSs x,jr⟩)
  . exact sS
 have j1:∀ i,L i⊆S:=λ i=>(h4 i).trans (qt H S i {x})
 have h6:∀ i,i < r->∀ u∈qs H S (i+1) {x} \ qs H S i {x},
   #((qs H S i {x}).filter (H.Adj u))<=1:=by
  intro i hi u hu;obtain ⟨jy,j7⟩:=pS hu;have js:u∈S:=qt H S (i+1) {x} jy;by_contra kn;push Not at kn;obtain ⟨y1,hy1,y2,hy2,kb⟩:=one_lt_card.mp kn;obtain ⟨ju,ke⟩:=pF hy1;obtain ⟨jt,kd⟩:=pF hy2;obtain ⟨a1,kk,p1,kg,k4,jj⟩:=qB ju;obtain ⟨a2,kj,p2,kf,k3,ji⟩:=qB jt;have jq:a1=x:=pSg (pI kk).1;have jp:a2=x:=pSg (pI kj).1
  rcases jq.symm with rfl;rcases jp.symm with rfl
  have jc:u ∉ p1.support:=λ hm=>j7 (jj u hm)
  have jb:u ∉ p2.support:=λ hm=>j7 (ji u hm)
  let q1:(q3 H S).Walk x u:=p1.concat (q0o ke.symm (qt H S i {x} ju) js);let q2:(q3 H S).Walk x u:=p2.concat (q0o kd.symm (qt H S i {x} jt) js)
  have h5:q1.IsPath:=by
   dsimp only[q1];rw[wIp,support_concat,<- concat_eq_append];exact kg.support_nodup.concat jc
  have j8:q2.IsPath:=by
   dsimp only[q2];rw[wIp,support_concat,<- concat_eq_append];exact kf.support_nodup.concat jb
  have jl:q1≠q2:=by
   intro ki;have h9:=congrArg (λ w=>w.support.reverse) ki
   have k0:q1.support.reverse=u :: p1.support.reverse:=by
    dsimp only[q1];rw[support_concat,List.reverse_append];rfl
   have jz:q2.support.reverse=u :: p2.support.reverse:=by
    dsimp only[q2];rw[support_concat,List.reverse_append];rfl
   rw[k0,jz] at h9;have jm:=(List.cons.inj h9).2
   have j9:p1.support.reverse.head?=some y1:=by
    rw[List.head?_reverse,List.getLast?_eq_some_getLast (wSn p1),wGl]
   have jn:p2.support.reverse.head?=some y2:=by
    rw[List.head?_reverse,List.getLast?_eq_some_getLast (wSn p2),wGl]
   rw[jm] at j9;exact kb (Option.some.inj (j9.symm.trans jn))
  obtain ⟨y,c',hc',k6⟩:=q0J q1 q2 h5 j8 jl;have kh:=hc.2 y c' hc'
  have k1:q1.length+q2.length<=2*(i+1):=by simp only[q1,q2,length_concat];omega
  omega
 have j0:∀ i,1<=i->i < r->∀ u∈L i,∀ v∈L i,¬ H.Adj u v:=by
  intro i ka hir u hu v hv ja;have km:u∈qs H S i {x}:=h4 i hu;have jx:v∈qs H S i {x}:=h4 i hv;have js:u∈S:=qt H S i {x} km;have jw:v∈S:=qt H S i {x} jx;obtain ⟨a1,kk,p1,kg,k4,_⟩:=qB km;obtain ⟨a2,kj,p2,kf,k3,_⟩:=qB jx;have jq:a1=x:=pSg (pI kk).1;have jp:a2=x:=pSg (pI kj).1
  rcases jq.symm with rfl;rcases jp.symm with rfl
  have h7:v ∉ qs H S (i - 1) {x}:=by
   dsimp only[L] at hv;rw[if_neg (by omega)] at hv;exact (pS hv).2
  have j2:v ∉ p1.support:=by
   intro k9;let q:=p1.takeUntil v k9
   have k1:q.length < p1.length:=by
    have hadd:q.length+(p1.dropUntil v k9).length=p1.length:=by
     rw[<- wLa,take_spec p1 k9]
    have hpos:0 < (p1.dropUntil v k9).length :=
     Nat.pos_of_ne_zero λ h0=>(H.ne_of_adj ja).symm (eq_of_length_eq_zero h0)
    omega
   have jv:=qA (mSs x) jr q;exact h7 (qu H S (by omega) {x} jv)
  have hlen1_eq:p1.length=i:=by
   have h8:u ∉ qs H S (i - 1) {x}:=by
    dsimp only[L] at hu;rw[if_neg (by omega)] at hu;exact (pS hu).2
   by_contra hne
   have hlt:p1.length<=i - 1:=by omega
   exact h8 (qu H S hlt {x} (qA (mSs x) jr p1))
  let q1:(q3 H S).Walk x v:=p1.concat (q0o ja js jw)
  have h5:q1.IsPath:=by
   dsimp only[q1];rw[wIp,support_concat,<- concat_eq_append];exact kg.support_nodup.concat j2
  have jl:q1≠p2:=by
   intro ki;have:=congrArg Walk.length ki;simp only[q1,length_concat] at this;omega
  obtain ⟨y,c',hc',k6⟩:=q0J q1 p2 h5 kf jl;have kh:=hc.2 y c' hc'
  have:q1.length+p2.length<=2*i+1:=by simp only[q1,length_concat];omega
  omega
 have jg:∀ i,1<=i->i<=r->(d' - 1)^i<=#(L i):=by
  intro i
  induction i with
  | zero=>intro h _;omega
  | succ i ih =>
   intro _ hir
   rcases Nat.eq_zero_or_pos i with rfl | ka
   .
    have jk:S.filter (H.Adj x)⊆L 1:=by
     intro v hv;obtain ⟨jw,kl⟩:=pF hv;dsimp only[L];rw[if_neg (by omega)]
     have j4:v ∉ qs H S 0 {x}:=by
      simp only[qs,mI,mSg];intro h;exact H.ne_of_adj kl h.1.symm
     exact rS ⟨mUr _ ((qo H S _ v).mpr
      ⟨jw,j4,x,rI ⟨mSs x,jr⟩,kl⟩),j4⟩
    have h1:d'<=#(S.filter (H.Adj x)):=k5 x jr;have h2:=cL jk;simp only[Nat.zero_add,pow_one];omega
   .
    have k2:=ih ka (by omega);let E:=(L i ×ˢ L (i+1)).filter (λ p=>H.Adj p.1 p.2)
    have k8:#(L i)*(d' - 1)<=#E:=by
     rw[card_filter,Finset.sum_product]
     calc
      #(L i)*(d' - 1)=∑ _u∈L i,(d' - 1):=by simp
      _<=∑ u∈L i,∑ v∈L (i+1),if H.Adj u v then 1 else 0:=by
        refine sum_le_sum λ u hu=>?_
        rw[<- card_filter];have js:u∈S:=j1 i hu
        have je:S.filter (H.Adj u)⊆(qs H S (i - 1) {x}).filter (H.Adj u)∪(L (i+1)).filter (H.Adj u):=by
         intro v hv;obtain ⟨jw,ja⟩:=pF hv
         by_cases jx:v∈qs H S (i - 1) {x}
         . exact mUl _ (rF ⟨jx,ja⟩)
         .
          by_cases jh:v∈qs H S i {x}
          .
           exfalso
           have kc:v∈L i:=by
            dsimp only[L];rw[if_neg (by omega)];exact rS ⟨jh,jx⟩
           exact j0 i ka (by omega) u hu v kc ja
          .
           refine mUr _ (rF ⟨?_,ja⟩);dsimp only[L];rw[if_neg (by omega),Nat.add_sub_cancel]
           exact rS ⟨mUr _ ((qo H S _ v).mpr
            ⟨jw,jh,u,h4 i hu,ja⟩),jh⟩
        have h1:#(S.filter (H.Adj u))<=#((qs H S (i - 1) {x}).filter (H.Adj u)) +
          #((L (i+1)).filter (H.Adj u)) :=
         (cL je).trans (cUl _ _)
        have j6:u∈qs H S ((i - 1)+1) {x} \ qs H S (i - 1) {x}:=by
         rw[Nat.sub_add_cancel ka];dsimp only[L] at hu;rw[if_neg (by omega)] at hu;exact hu
        have h2:=h6 (i - 1) (by omega) u j6;have h3:d'<=#(S.filter (H.Adj u)):=k5 u js;change d' - 1<=#((L (i+1)).filter (H.Adj u));omega
    have k7:#E<=#(L (i+1)):=by
     rw[card_filter,Finset.sum_product_right]
     calc
      ∑ v∈L (i+1),∑ u∈L i,(if H.Adj u v then 1 else 0)
       <= ∑ _v∈L (i+1),1:=sum_le_sum λ v hv=>by
         rw[<- card_filter]
         have j5:v∈qs H S (i+1) {x} \ qs H S i {x}:=by
          dsimp only[L] at hv;rw[if_neg (by omega),Nat.add_sub_cancel] at hv;exact hv
         have jk:(L i).filter (λ u=>H.Adj u v)⊆(qs H S i {x}).filter (H.Adj v):=by
          intro u hu;obtain ⟨huL,ja⟩:=pF hu;exact rF ⟨h4 i huL,ja.symm⟩
         exact (cL jk).trans (h6 i (by omega) v j5)
      _=#(L (i+1)):=by simp
    calc
     (d' - 1)^(i+1)=(d' - 1)^i*(d' - 1):=pow_succ _ _
     _<=#(L i)*(d' - 1):=nMr _ k2
     _<=#(L (i+1)):=k8.trans k7
 have jo:(0:O) < ((d' - 1:ℕ):O):=by exact_mod_cast (show 0 < d' - 1 by omega)
 have j3:0 < log ((d' - 1:ℕ):O):=lPs (by exact_mod_cast (show 1 < d' - 1 by omega))
 rcases Nat.eq_zero_or_pos r with hr0 | hr1
 .
  have hg2:(c.length:O)<=2:=by exact_mod_cast (show g<=2 by omega)
  have hlogS_nn:0<=log (#S:O):=lNn (by exact_mod_cast card_pos.mpr ⟨x,jr⟩)
  have:0<=2*log (#S:O)/log ((d' - 1:ℕ):O):=by positivity
  linarith
 .
  have jd:(((d' - 1:ℕ):O)^r)<=(#S:O):=by
   have h1:(((d' - 1)^r:ℕ):O)<=(#S:O) :=
    by exact_mod_cast (jg r hr1 le_rfl).trans (cL (j1 r))
   rwa [Nat.cast_pow] at h1
  have jf:(r:O)*log ((d' - 1:ℕ):O)<=log (#S:O):=by
   have h:=lLl (pow_pos jo r) jd
   rwa [lP] at h
  have hr_le:(r:O)<=log (#S:O)/log ((d' - 1:ℕ):O) :=
   (lDi j3).mpr jf
  have hg_le:(c.length:O)<=2*(r:O)+2:=by exact_mod_cast (show g<=2*r+2 by omega)
  rw[mul_div_assoc];linarith
lemma q0M {V:Type*} {G:SG V} {u v:V} (q:G.Walk u v) : q.support.IsChain G.Adj:=by
 induction q with
 | nil=>simp
 | cons hadj p ih =>
  rw[support_cons]
  cases p with
  | nil=>simp [hadj]
  | cons hadj' p'=>exact List.IsChain.cons_cons hadj ih
lemma q0N {V:Type*} {G:SG V} {u v:V} (q:G.Walk u v) : q.support[0]'(length_pos_of_ne_nil (wSn q))=u:=by cases q <;> rfl
lemma q0O {V:Type*} {G:SG V} {x:V} (c:G.Walk x x) (hc:c.IsCycle) :
  let g:=c.length
  ∃ a:Fin g->V,
   Injective a /\
   (univ.image a=c.support.toFinset) /\
   (∀ i j:Fin g,i.val < j.val ->
    ∃ (p1 p2:G.Walk (a i) (a j)),
     p1.IsPath/\p2.IsPath /\
     p1.length=j.val - i.val/\p2.length=g - (j.val - i.val) /\
     (∀ w∈p1.support,w∈c.support)/\(∀ w∈p2.support,w∈c.support) /\
     (∀ w∈p1.support,w∈p2.support->w=a i\/w=a j) /\
     (p1.support.toFinset∪p2.support.toFinset=c.support.toFinset)):=by
 intro g;let L:=c.support.dropLast
 have jz:L.length=g:=by
  rw[length_dropLast,wLs];simp [g]
 have k1:L.Nodup:=by
  have jt:c.support.tail.Nodup:=hc.support_nodup;have jp:=wSn c;have jx:c.support=x :: c.support.tail:=(cons_tail_support c).symm;have h6:c.support=L ++ [x]:=(dropLast_append_getLast jp).symm.trans (by rw[wGl c])
  have ju:L.Perm c.support.tail:=by
   have h1:(L ++ [x]).Perm (x :: L):=List.perm_append_singleton x L;rw[<- h6,jx] at h1;exact (List.perm_cons x).mp h1.symm
  exact ju.nodup_iff.mpr jt
 have h9:L.toFinset=c.support.toFinset:=by
  ext v;simp only[mT]
  have jp:=wSn c;have h6:c.support=L ++ [x]:=(dropLast_append_getLast jp).symm.trans (by rw[wGl c]);constructor
  . exact λ hv=>List.dropLast_subset _ hv
  .
   intro hv;rw[h6,mem_append,List.mem_singleton] at hv
   rcases hv with h1 | hvx
   . exact h1
   .
    rw[hvx]
    have h0:0 < L.length:=by rw[jz];have:=hc.three_le_length;omega
    have jy:∀ (M:List V),M=L ++ [x]->∀ hpos:0 < M.length,M[0]'hpos=L[0]'h0:=by
     rintro _ rfl _;exact getElem_append_left h0
    have hx0:L[0]'h0=x:=(jy c.support h6 _).symm.trans (q0N c);rw[<- hx0];exact getElem_mem h0
 let a:Fin g->V:=λ i=>L[i.val]'(by omega)
 have h7:Injective a:=λ i j h=>Fin.ext ((List.Nodup.getElem_inj_iff k1).mp h)
 have j1:univ.image a=c.support.toFinset:=by
  rw[<- h9];ext v;simp only[mem_image,mUv,true_and,mT,a];constructor
  . rintro ⟨i,rfl⟩;exact getElem_mem _
  . intro hv;obtain ⟨i,hi,rfl⟩:=getElem_of_mem hv;exact ⟨⟨i,by omega⟩,rfl⟩
 have j2:∀ k (hk:k < g),G.Adj (a ⟨k,hk⟩) (a ⟨(k+1) % g,mod_lt _ (by omega)⟩):=by
  intro k hk;have jp:=wSn c;have h6:c.support=L ++ [x]:=(dropLast_append_getLast jp).symm.trans (by rw[wGl c]);have jo:c.support.IsChain G.Adj:=q0M c
  have j8:∀ (M:List V),M=L ++ [x]->∀ m (hm:m < M.length),M[m]'hm =
    if h:m < g then a ⟨m,h⟩ else x:=by
   rintro _ rfl m hm
   by_cases k2:m < g
   . rw[dif_pos k2,getElem_append_left (by omega)]
   .
    rw[dif_neg k2,List.getElem_append_right (by omega)]
    have:m - L.length=0:=by rw[List.length_append,List.length_singleton] at hm;omega
    simp [this]
  have jl:∀ m (hm:m < c.support.length),c.support[m]'hm=if h:m < g then a ⟨m,h⟩ else x :=
   j8 c.support h6
  have hkr:k+1 < c.support.length:=by rw[wLs];omega
  have h4:G.Adj (c.support[k]'(by omega)) (c.support[k+1]'hkr) :=
   List.isChain_iff_getElem.mp jo k (by omega)
  rw[jl k (by omega),dif_pos hk,jl (k+1) hkr] at h4
  by_cases k0:k+1 < g
  . rw[dif_pos k0] at h4;have jk:(k+1) % g=k+1:=nMo k0;simpa [jk] using h4
  .
   rw[dif_neg k0] at h4
   have jw:k+1=g:=by omega
   have jk:(k+1) % g=0:=by rw[jw,Nat.mod_self]
   have ha0:a ⟨0,by omega⟩=x:=by
    have h0:=jl 0 (length_pos_of_ne_nil jp);rw[dif_pos (by omega)] at h0;exact h0.symm.trans (q0N c)
   simpa [jk,ha0] using h4
 have j9:∀ d (hd:d < g) (i:Fin g),
   ∃ p:G.Walk (a i) (a ⟨(i.val+d) % g,mod_lt _ (by omega)⟩),
    p.length=d/\p.support=(List.range (d+1)).map (λ t=>a ⟨(i.val+t) % g,mod_lt _ (by omega)⟩):=by
  intro d
  induction d with
  | zero =>
   intro _ i
   have ja:a i=a ⟨(i.val+0) % g,mod_lt _ (by omega)⟩ :=
    congrArg a (Fin.ext (by simp [nMo i.isLt]))
   refine ⟨Walk.copy Walk.nil rfl ja,by simp,?_⟩;simp [List.range_succ,ja]
  | succ d ih =>
   intro hd i;let i1:Fin g:=⟨(i.val+1) % g,mod_lt _ (by omega)⟩;obtain ⟨p',jj,je⟩:=ih (by omega) i1
   have jf:a ⟨(i1.val+d) % g,mod_lt _ (by omega)⟩=a ⟨(i.val+(d+1)) % g,mod_lt _ (by omega)⟩ :=
    congrArg a (Fin.ext (by dsimp only[i1];rw[Nat.mod_add_mod];congr 1;omega))
   let p:G.Walk (a i) (a ⟨(i.val+(d+1)) % g,mod_lt _ (by omega)⟩) :=
    Walk.cons (j2 i.val i.isLt) (Walk.copy p' rfl jf)
   refine ⟨p,by simp [p,jj],?_⟩;dsimp only[p];rw[support_cons,support_copy,je]
   conv_rhs=>rw[List.range_succ_eq_map,List.map_cons,List.map_map]
   refine congrArg₂ List.cons ?_ ?_
   . exact congrArg a (Fin.ext (by simp [nMo i.isLt]))
   . apply List.map_congr_left;intro t _;simp only[Function.comp_apply,i1];exact congrArg a (Fin.ext (by simp only[Nat.mod_add_mod];congr 1;omega))
 refine ⟨a,h7,j1,λ i j hij=>?_⟩
 have hg3:3<=g:=hc.three_le_length;let d1:=j.val - i.val;let d2:=g - d1
 have jn:d1 < g:=by omega
 have jm:d2 < g:=by omega
 obtain ⟨q1,jc,j4⟩:=j9 d1 jn i;obtain ⟨q2,jb,j3⟩:=j9 d2 jm j
 have hm1:a ⟨(i.val+d1) % g,mod_lt _ (by omega)⟩=a j :=
  congrArg a (Fin.ext (by dsimp only[d1];rw[Nat.add_sub_of_le (lOf hij),nMo j.isLt]))
 have hm2:a ⟨(j.val+d2) % g,mod_lt _ (by omega)⟩=a i :=
  congrArg a (Fin.ext (by
   have ja:j.val+d2=i.val+g:=by omega
   dsimp only;rw[ja,add_mod_right,nMo i.isLt]))
 let p1:G.Walk (a i) (a j):=Walk.copy q1 rfl hm1;let jq:G.Walk (a j) (a i):=Walk.copy q2 rfl hm2;let p2:G.Walk (a i) (a j):=jq.reverse
 have jd:p1.length=d1:=by simp [p1,jc]
 have h3:p1.support=(List.range (d1+1)).map (λ t=>a ⟨(i.val+t) % g,mod_lt _ (by omega)⟩):=by
  simp [p1,j4]
 have j5:jq.length=d2:=by simp [jq,jb]
 have h2:jq.support=(List.range (d2+1)).map (λ t=>a ⟨(j.val+t) % g,mod_lt _ (by omega)⟩):=by
  simp [jq,j3]
 have j7:p1.IsPath:=by
  rw[wIp,h3];refine List.Nodup.map_on (λ t1 ji t2 jh ja=>?_) List.nodup_range
  have j0:=congrArg Fin.val (h7 ja);simp only[List.mem_range] at ji jh;have h1:(i.val+t1) % g=(i.val+t2) % g:=j0;rw[nMo (by omega:i.val+t1 < g),nMo (by omega:i.val+t2 < g)] at h1;omega
 have j6:p2.IsPath:=by
  rw[wIp,support_reverse,List.nodup_reverse,h2];refine List.Nodup.map_on (λ t1 ji t2 jh ja=>?_) List.nodup_range
  have j0:=congrArg Fin.val (h7 ja);simp only[List.mem_range] at ji jh;have h1:(j.val+t1) % g=(j.val+t2) % g:=j0
  have h5:∀ t,t < d2+1->g<=j.val+t->(j.val+t) % g=j.val+t - g:=λ t ht hle=>by
   rw[Nat.mod_eq_sub_mod hle,nMo (by omega)]
  by_cases jv:j.val+t1 < g <;> by_cases jg:j.val+t2 < g
  . rw[nMo jv,nMo jg] at h1;omega
  . rw[nMo jv,h5 t2 jh (by omega)] at h1;omega
  . rw[h5 t1 ji (by omega),nMo jg] at h1;omega
  . rw[h5 t1 ji (by omega),h5 t2 jh (by omega)] at h1;omega
 have h8:∀ k:Fin g,a k∈c.support:=λ k =>
  pTf (j1 ▸ mem_image.mpr ⟨k,mUv k,rfl⟩)
 refine ⟨p1,p2,j7,j6,jd,by simp [p2,j5,d2,d1],?_,?_,?_,?_⟩
 . intro w hw;rw[h3,List.mem_map] at hw;obtain ⟨_,_,rfl⟩:=hw;exact h8 _
 . intro w hw;rw[support_reverse,mem_reverse,h2,List.mem_map] at hw;obtain ⟨_,_,rfl⟩:=hw;exact h8 _
 .
  intro w js jr;rw[h3,List.mem_map] at js;rw[support_reverse,mem_reverse,h2,List.mem_map] at jr;obtain ⟨t1,ji,rfl⟩:=js;obtain ⟨t2,jh,ja⟩:=jr;simp only[List.mem_range] at ji jh;have j0:(j.val+t2) % g=(i.val+t1) % g:=congrArg Fin.val (h7 ja);have h1:(i.val+t1) % g=i.val+t1:=nMo (by omega);rw[h1] at j0
  by_cases jg:j.val+t2 < g
  . rw[nMo jg] at j0;right;exact congrArg a (Fin.ext (by dsimp only;rw[h1];omega))
  .
   have h2':(j.val+t2) % g=j.val+t2 - g:=by
    rw[Nat.mod_eq_sub_mod (by omega),nMo (by omega)]
   rw[h2'] at j0;left;exact congrArg a (Fin.ext (by dsimp only;rw[h1];omega))
 .
  rw[<- j1];ext w;simp only[mU,mT,mem_image,mUv,true_and];constructor
  .
   rintro (js | jr)
   . rw[h3,List.mem_map] at js;obtain ⟨t,_,rfl⟩:=js;exact ⟨_,rfl⟩
   . rw[support_reverse,mem_reverse,h2,List.mem_map] at jr;obtain ⟨t,_,rfl⟩:=jr;exact ⟨_,rfl⟩
  .
   rintro ⟨k,rfl⟩
   by_cases hk:i.val<=k.val/\k.val<=j.val
   . left;rw[h3,List.mem_map];refine ⟨k.val - i.val,List.mem_range.mpr (by omega),congrArg a (Fin.ext ?_)⟩;dsimp only;rw[Nat.add_sub_of_le hk.1,nMo k.isLt]
   .
    right;rw[support_reverse,mem_reverse,h2,List.mem_map]
    by_cases hkj:j.val<=k.val
    . refine ⟨k.val - j.val,List.mem_range.mpr (by omega),congrArg a (Fin.ext ?_)⟩;dsimp only;rw[Nat.add_sub_of_le hkj,nMo k.isLt]
    . refine ⟨g - j.val+k.val,List.mem_range.mpr (by omega),congrArg a (Fin.ext ?_)⟩;dsimp only;rw[show j.val+(g - j.val+k.val)=k.val+g by omega,add_mod_right,nMo k.isLt]
lemma q0P {V:Type*} {H:SG V} {S:FS V} {x:V} {c:(q3 H S).Walk x x} (hc:q0G H S x c) (v:V) (l:ℕ) : #(qs H S l {v}∩c.support.toFinset)<=4*l+1:=by
 let g:=c.length;obtain ⟨a,jb,h5,jh⟩:=q0O c hc.1
 let h2:Fin g->Fin g->ℕ:=λ i j =>
  min (if i.val<=j.val then j.val - i.val else i.val - j.val)
    (g - (if i.val<=j.val then j.val - i.val else i.val - j.val))
 have h3:∀ i j,h2 i j=h2 j i:=λ i j=>by
  dsimp only[h2]
  by_cases h:i.val<=j.val
  .
   by_cases js:i.val=j.val
   . simp [js]
   . rw[if_pos h,if_neg (by omega)]
  . rw[if_neg h,if_pos (by omega)]
 have h4:∀ i k j:Fin g,h2 i j<=h2 i k+h2 k j:=by
  intro i k j;dsimp only[h2]
  have h1:∀ x y z:ℕ,x < g->y < g->z < g ->
    min (if x<=z then z - x else x - z) (g - (if x<=z then z - x else x - z)) <=
    min (if x<=y then y - x else x - y) (g - (if x<=y then y - x else x - y)) +
    min (if y<=z then z - y else y - z) (g - (if y<=z then z - y else y - z)):=by
   intro x y z _ _ _
   split_ifs <;> omega
  exact h1 i.val k.val j.val i.isLt k.isLt j.isLt
 have jf:∀ N:ℕ,∀ (i j:Fin g) (p:(q3 H S).Walk (a i) (a j)),
   p.length<=N->h2 i j<=p.length:=by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
   intro i j p jp
   by_cases jx:p.length < h2 i j
   .
    exfalso
    have hij:i≠j:=by
     intro h;subst h;simp [h2] at jx
    let q:=p.bypass;have h6:q.IsPath:=p.bypass_isPath;have hq_le_N:q.length<=N:=(length_bypass_le_length p).trans jp;have h8:q.length < h2 i j:=(length_bypass_le_length p).trans_lt jx
    by_cases j4:∃ w∈q.support,w∈c.support.toFinset/\w≠a i/\w≠a j
    .
     obtain ⟨w,ji,jv,j2,j3⟩:=j4;rw[<- h5,mem_image] at jv;obtain ⟨k,_,rfl⟩:=jv;let q1:=q.takeUntil (a k) ji;let q2:=q.dropUntil (a k) ji
     have hadd:q1.length+q2.length=q.length:=by rw[<- wLa,take_spec q ji]
     have hpos1:0 < q1.length:=Nat.pos_of_ne_zero λ h0=>j2 (eq_of_length_eq_zero h0).symm
     have hpos2:0 < q2.length:=Nat.pos_of_ne_zero λ h0=>j3 (eq_of_length_eq_zero h0)
     have hd1:=ih q1.length (by omega) i k q1 le_rfl;have hd2:=ih q2.length (by omega) k j q2 le_rfl;have htri:=h4 i k j;omega
    .
     push Not at j4
     have j5:∀ (i' j':Fin g) (q':(q3 H S).Walk (a i') (a j')),
       i'.val < j'.val->q'.IsPath->q'.length < h2 i' j' ->
       (∀ w∈q'.support,w∈c.support.toFinset->w=a i'\/w=a j')->False:=by
      intro i' j' q' hij' jd hq'len h9;obtain ⟨r₁,r2,jn,jl,hr1l,hr2l,jo,jm,_,_⟩:=jh i' j' hij'
      have je:1<=q'.length:=Nat.pos_of_ne_zero λ h0 =>
       (Fin.ne_of_lt hij') (jb (eq_of_length_eq_zero h0))
      have jy:h2 i' j'=min (j'.val - i'.val) (g - (j'.val - i'.val)):=by
       dsimp only[h2];rw[if_pos (lOf hij')]
      by_cases j7:j'.val - i'.val<=g - (j'.val - i'.val)
      .
       have ja:h2 i' j'=j'.val - i'.val:=by rw[jy,min_eq_left j7]
       have j9:=q0I q' r₁ jd jn je (by omega) (by omega)
        (λ w j2 j3=>h9 w j2 (rT (jo w j3)))
       have j8:=hc.2 (a i') (q'.append r₁.reverse) j9;rw[wLa,wLr] at j8;omega
      .
       have ja:h2 i' j'=g - (j'.val - i'.val):=by rw[jy,min_eq_right (by omega)]
       have j9:=q0I q' r2 jd jl je (by omega) (by omega)
        (λ w j2 j3=>h9 w j2 (rT (jm w j3)))
       have j8:=hc.2 (a i') (q'.append r2.reverse) j9;rw[wLa,wLr] at j8;omega
     rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hij) with hij' | hji'
     .
      exact j5 i j q hij' h6 h8 (λ w j2 j3=>by
       by_cases h1:w=a i
       . exact Or.inl h1
       . exact Or.inr (j4 w j2 j3 h1))
     .
      exact j5 j i q.reverse hji' h6.reverse (by rw[wLr,h3];exact h8)
       (λ w j2 j3=>by
        rw[support_reverse,mem_reverse] at j2
        by_cases h1:w=a i
        . exact Or.inr h1
        . exact Or.inl (j4 w j2 j3 h1))
   . omega
 by_cases j0:(qs H S l {v}∩c.support.toFinset).Nonempty
 .
  obtain ⟨u0,hu0⟩:=j0;obtain ⟨jj,jc⟩:=pI hu0;rw[<- h5,mem_image] at jc;obtain ⟨i0,_,rfl⟩:=jc
  have jk:qs H S l {v}∩c.support.toFinset ⊆
    ((range (2*l+1)).image (λ t=>a ⟨(i0.val+t) % g,mod_lt _ (by have:=hc.1.three_le_length;omega)⟩)) ∪
    ((range (2*l)).image (λ t=>a ⟨(i0.val+g - (t+1) % g) % g,mod_lt _ (by have:=hc.1.three_le_length;omega)⟩)):=by
   intro u hu;obtain ⟨huB,jw⟩:=pI hu;rw[<- h5,mem_image] at jw;obtain ⟨j,_,rfl⟩:=jw;obtain ⟨b1,hb1,p1,_,hlen1,_⟩:=qB jj;obtain ⟨b2,hb2,p2,_,hlen2,_⟩:=qB huB;have ju:b1=v:=pSg (pI hb1).1;have jt:b2=v:=pSg (pI hb2).1;subst ju;subst jt;let h7:(q3 H S).Walk (a i0) (a j):=p1.reverse.append p2;have j6:=jf h7.length i0 j h7 le_rfl;dsimp only[h7] at j6;rw[wLa,wLr] at j6
   have j1:h2 i0 j<=2*l:=by omega
   have hg3:3<=g:=hc.1.three_le_length;dsimp only[h2] at j1
   by_cases jq:i0.val<=j.val
   .
    rw[if_pos jq] at j1
    rcases min_le_iff.mp j1 with jr | jg
    . refine mUl _ (mem_image.mpr ⟨j.val - i0.val,mem_range.mpr (by omega),congrArg a (Fin.ext ?_)⟩);dsimp only;rw[Nat.add_sub_of_le jq,nMo j.isLt]
    .
     refine mUr _ (mem_image.mpr ⟨g - (j.val - i0.val) - 1,mem_range.mpr (by omega),congrArg a (Fin.ext ?_)⟩);dsimp only;rw[show g - (j.val - i0.val) - 1+1=g - (j.val - i0.val) by omega]
     by_cases js:j.val=i0.val
     . simp only[js,Nat.sub_self,Nat.sub_zero,Nat.mod_self,add_mod_right];exact nMo i0.isLt
     .
      rw[nMo (by omega:g - (j.val - i0.val) < g),
       show i0.val+g - (g - (j.val - i0.val))=j.val by omega,nMo j.isLt]
   .
    rw[if_neg jq] at j1
    rcases min_le_iff.mp j1 with jg | jr
    .
     refine mUr _ (mem_image.mpr ⟨i0.val - j.val - 1,mem_range.mpr (by omega),congrArg a (Fin.ext ?_)⟩);dsimp only
     rw[show i0.val - j.val - 1+1=i0.val - j.val by omega,
      nMo (by omega:i0.val - j.val < g),
      show i0.val+g - (i0.val - j.val)=j.val+g by omega,add_mod_right,nMo j.isLt]
    . refine mUl _ (mem_image.mpr ⟨g - (i0.val - j.val),mem_range.mpr (by omega),congrArg a (Fin.ext ?_)⟩);dsimp only;rw[show i0.val+(g - (i0.val - j.val))=j.val+g by omega,add_mod_right,nMo j.isLt]
  calc
   #(qs H S l {v}∩c.support.toFinset)
    <= #(((range (2*l+1)).image _)∪((range (2*l)).image _)):=cL jk
   _<=#((range (2*l+1)).image _)+#((range (2*l)).image _):=cUl _ _
   _<=#(range (2*l+1))+#(range (2*l)):=nAa card_image_le card_image_le
   _=4*l+1:=by simp;omega
 . rw[not_nonempty_iff_eq_empty.mp j0];simp
lemma q0Q {V:Type*} {G:SG V} {u v:V} (p:G.Walk u v) (E:FS V) (l:ℕ) (h:∀ (w:V) (hw:w∈p.support),w∈E->(p.takeUntil w hw).length<=l) : #(E∩p.support.toFinset)<=l+1:=by
 have h6:E∩p.support.toFinset⊆(p.support.take (l+1)).toFinset:=by
  intro w hw;obtain ⟨hwE,hwp⟩:=pI hw;have h0:w∈p.support:=pTf hwp;have hlen:=h w h0 hwE;let L1:=(p.takeUntil w h0).support;let L2:=(p.dropUntil w h0).support.tail
  have h4:L1 ++ L2=p.support:=by
   dsimp only[L1,L2];rw[<- support_append,take_spec p h0]
  have hlen_eq:L1.length+L2.length=p.support.length:=by
   rw[<- List.length_append,h4]
  have hL1len:L1.length=(p.takeUntil w h0).length+1:=wLs _
  have hidx_lt:(p.takeUntil w h0).length < p.support.length:=by omega
  have h7:p.support[(p.takeUntil w h0).length]'hidx_lt=w:=by
   have h1:(L1 ++ L2)[(p.takeUntil w h0).length]'(by rw[h4];exact hidx_lt) =
     L1[(p.takeUntil w h0).length]'(by omega):=getElem_append_left (by omega)
   have h2:L1[(p.takeUntil w h0).length]'(by omega)=w:=by
    have h2a:L1[(p.takeUntil w h0).length]'(by omega)=L1[L1.length - 1]'(by omega):=by congr 1;omega
    have h2b:L1[L1.length - 1]'(by omega)=w:=by
     dsimp only[L1];rw[<- getLast_eq_getElem (wSn _)];exact wGl _
    exact h2a.trans h2b
   have h3:p.support[(p.takeUntil w h0).length]'hidx_lt=(L1 ++ L2)[(p.takeUntil w h0).length]'(by rw[h4];exact hidx_lt):=by
    congr 1;exact h4.symm
   exact h3.trans (h1.trans h2)
  rw[mT]
  have hlt_take:(p.takeUntil w h0).length < (p.support.take (l+1)).length:=by
   rw[List.length_take];omega
  have h5:(p.support.take (l+1))[(p.takeUntil w h0).length]'hlt_take=w:=by
   rw[List.getElem_take];exact h7
  exact h5 ▸ getElem_mem hlt_take
 calc
  #(E∩p.support.toFinset)
   <= (p.support.take (l+1)).toFinset.card:=cL h6
  _<=(p.support.take (l+1)).length:=toFinset_card_le _
  _<=l+1:=List.length_take_le _ _
def q0R {V:Type*} (H:SG V) (S_in C X:FS V)
  (s r':ℕ) (T:Fin r'->FS V) (m3 q L:ℕ):Prop :=
 ∃ (st:Fin q->V) (tg:Fin q->Fin r') (en:Fin q->V)
  (p:∀ a:Fin q,(q3 H S_in).Walk (st a) (en a)),
  (∀ a,st a∈X)/\(∀ a,en a∈T (tg a))/\Injective tg /\
  (∀ a,(p a).IsPath/\(p a).length<=m3) /\
  (∀ a,∀ w∈(p a).support,w∈C∪X->w=st a) /\
  (∀ a,∀ j:Fin r',∀ w∈(p a).support,w∈T j->j=tg a/\w=en a) /\
  (∀ a b,a≠b->∀ w∈(p a).support,w∈(p b).support->w=st a/\w=st b) /\
  (∀ x∈X,#(univ.filter (λ a=>st a=x))<=s) /\
  (∑ a:Fin q,(p a).length=L)
lemma q0S {V:Type*} (H:SG V) (S_in C X:FS V) (s r' m3 q:ℕ) (T:Fin r'->FS V) (st:Fin q->V) (tg:Fin q->Fin r') (en:Fin q->V) (p:∀ a:Fin q,(q3 H S_in).Walk (st a) (en a)) (hst:∀ a,st a∈X) (hen:∀ a,en a∈T (tg a)) (h9:Injective tg) (h4:∀ a,(p a).IsPath/\(p a).length<=m3) (j7:∀ a,∀ w∈(p a).support,w∈C∪X->w=st a) (jb:∀ a,∀ j:Fin r',∀ w∈(p a).support,w∈T j->j=tg a/\w=en a) (j1:∀ a b,a≠b->∀ w∈(p a).support,w∈(p b).support->w=st a/\w=st b) (jc:∀ x∈X,#(univ.filter (λ a=>st a=x))<=s) (a:Fin q) (x':V) (hxX:x'∈X) (hx_cnt:#(univ.filter (λ b=>st b=x')) < s) (h0:(q3 H S_in).Walk x' (en a)) (j0:h0.IsPath) (h8:h0.length < (p a).length) (j6:∀ z∈h0.support,z∈C∪X->z=x') (ja:∀ j:Fin r',∀ z∈h0.support,z∈T j->j=tg a/\z=en a) (h5:∀ b,b≠a->∀ z∈h0.support,z∈(p b).support->z=x'/\z=st b) : ∃ L' < ∑ b:Fin q,(p b).length,q0R H S_in C X s r' T m3 q L':=by
 let h6:Fin q->V:=Function.update st a x'
 let p':∀ b:Fin q,(q3 H S_in).Walk (h6 b) (en b):=λ b =>
  if h:b=a then h0.copy (by simp [h6,h]) (by simp [h])
  else (p b).copy (by simp [h6,h]) rfl
 have h7:∀ b,(p' b).length=if b=a then h0.length else (p b).length:=λ b=>by
  dsimp only[p'];split_ifs with h <;> simp
 have h3:∀ b,(p' b).support=if b=a then h0.support else (p b).support:=λ b=>by
  dsimp only[p'];split_ifs with h <;> simp
 refine ⟨∑ b:Fin q,(p' b).length,?_,h6,tg,en,p',?_,hen,h9,?_,?_,?_,?_,?_,rfl⟩
 .
  refine Finset.sum_lt_sum (λ b _=>?_) ⟨a,mUv a,?_⟩
  . rw[h7];split_ifs with h;exact h ▸ h8.le;exact le_rfl
  . rw[h7,if_pos rfl];exact h8
 . intro b;dsimp only[h6];by_cases h:b=a <;> simp [h,hxX,hst b]
 .
  intro b;dsimp only[p'];split_ifs with h
  . exact ⟨q0p j0 _ _,by simp;have:=(h4 a).2;omega⟩
  . exact ⟨q0p (h4 b).1 _ _,by simp;exact (h4 b).2⟩
 .
  intro b z hz j5;rw[h3] at hz;split_ifs at hz with h
  . subst h;simp only[h6,Function.update_self];exact j6 z hz j5
  . simp only[h6,update_of_ne h];exact j7 b z hz j5
 .
  intro b j z hz jd;rw[h3] at hz;split_ifs at hz with h
  . subst h;exact ja j z hz jd
  . exact jb b j z hz jd
 .
  intro b1 b2 hne' z j4 j2;rw[h3] at j4 j2
  by_cases h1:b1=a
  . subst h1;rw[if_pos rfl] at j4;rw[if_neg hne'.symm] at j2;simp only[h6,Function.update_self,update_of_ne hne'.symm];exact h5 b2 hne'.symm z j4 j2
  .
   rw[if_neg h1] at j4
   by_cases h2:b2=a
   . subst h2;rw[if_pos rfl] at j2;simp only[h6,Function.update_self,update_of_ne h1];have hm:=h5 b1 h1 z j2 j4;exact ⟨hm.2,hm.1⟩
   . rw[if_neg h2] at j2;simp only[h6,update_of_ne h1,update_of_ne h2];exact j1 b1 b2 hne' z j4 j2
 .
  intro y hyX
  by_cases je:y=x'
  .
   subst je
   have j3:univ.filter (λ b:Fin q=>h6 b=y) ⊆
     insert a (univ.filter (λ b:Fin q=>st b=y)):=by
    intro b hb;obtain ⟨_,j8⟩:=pF hb
    by_cases j9:b=a
    . subst j9;exact mem_insert_self _ _
    .
     exact mem_insert_of_mem (rF ⟨mUv b,by
      simpa [h6,j9] using j8⟩)
   have hle:=(cL j3).trans (card_insert_le _ _);omega
  .
   have j3:univ.filter (λ b:Fin q=>h6 b=y) ⊆
     univ.filter (λ b:Fin q=>st b=y):=by
    intro b hb;obtain ⟨_,j8⟩:=pF hb
    by_cases j9:b=a
    . subst j9;simp [h6] at j8;exact absurd j8.symm je
    . exact rF ⟨mUv b,by simpa [h6,j9] using j8⟩
   exact (cL j3).trans (jc y hyX)
lemma q0T {V:Type*} {H:SG V} {S_in T_pre:FS V} {u_st x u w e:V} {l:ℕ} (p:(q3 H S_in).Walk u_st e) (h6:(q3 H T_pre).Walk x u) (hq_len:h6.length<=l - 1) (j0:∀ z∈h6.support,z∈S_in) (huw:H.Adj u w) (h9:u∈S_in) (h8:w∈S_in) (h7:w∈p.support) (hgt:l+1<=(p.takeUntil w h7).length) (hl1:1<=l) : ∃ q_new:(q3 H S_in).Walk x e, q_new.IsPath/\q_new.length < p.length /\ ∀ z∈q_new.support,z∈h6.support\/z∈(p.dropUntil w h7).support:=by
 let h5:(q3 H S_in).Walk x w:=(q0r h6 j0).concat (q0o huw h9 h8);let h0:(q3 H S_in).Walk x e:=h5.append (p.dropUntil w h7);refine ⟨h0.bypass,h0.bypass_isPath,?_,?_⟩
 .
  have h1:h0.bypass.length<=h0.length:=length_bypass_le_length h0;have h2:h0.length=h5.length+(p.dropUntil w h7).length:=wLa _ _
  have h3:h5.length=h6.length+1:=by simp [h5,q0t]
  have h4:(p.takeUntil w h7).length+(p.dropUntil w h7).length=p.length:=by
   rw[<- wLa,take_spec p h7]
  omega
 .
  intro z hz;have j2:z∈h0.support:=Walk.support_bypass_subset_support h0 hz;rw[wSa] at j2
  rcases j2 with h1 | h2
  .
   dsimp only[h5] at h1;rw[support_concat,q0s,mem_append,List.mem_singleton] at h1
   rcases h1 with j1 | rfl
   . exact Or.inl j1
   . exact Or.inr (wSm _)
  . exact Or.inr h2
lemma q0U {V:Type*} (H:SG V) (S S_in C X:FS V)
  (s r' m3 q:ℕ) (T:Fin r'->FS V)
  (k1:X⊆S_in)
  (st:Fin q->V) (tg:Fin q->Fin r') (en:Fin q->V)
  (p:∀ a:Fin q,(q3 H S_in).Walk (st a) (en a))
  (jy:∀ a,st a∈X) (hen:∀ a,en a∈T (tg a)) (jb:Injective tg)
  (j2:∀ a,(p a).IsPath/\(p a).length<=m3)
  (j8:∀ a,∀ w∈(p a).support,w∈C∪X->w=st a)
  (jm:∀ a,∀ j:Fin r',∀ w∈(p a).support,w∈T j->j=tg a/\w=en a)
  (j3:∀ a b,a≠b->∀ w∈(p a).support,w∈(p b).support->w=st a/\w=st b)
  (jv:∀ x∈X,#(univ.filter (λ a=>st a=x))<=s)
  (ju:∀ L' < ∑ a:Fin q,(p a).length,¬ q0R H S_in C X s r' T m3 q L')
  (x:V) (jw:x∈X) (jd:#(univ.filter (λ a=>st a=x)) < s) :
  let U:FS V:=((S \ S_in)∪X∪(univ.biUnion (λ a=>(p a).support.toFinset))∪C) \ {x}
  let V_tg:FS V:=univ.biUnion T
  ∀ a:Fin q,∀ l:ℕ,1<=l ->
   #(qn H S (qs H (S \ (V_tg∪U)) (l - 1) {x})∩(p a).support.toFinset)<=l+1:=by
 intro U V_tg a l hl1;apply q0Q (p a) _ l;intro w j6 hwN;by_contra k0;push Not at k0;obtain ⟨_,_,u,jx,huw⟩:=(qo H S _ w).mp hwN;obtain ⟨x',hx',j0,_,h8,h0⟩:=qB jx;have ji:x'=x:=pSg (pI hx').1
 rcases ji.symm with rfl
 have j4:S \ (V_tg∪U)⊆S_in:=by
  intro z hz;obtain ⟨hzS,jr⟩:=pS hz;by_contra jn
  by_cases j9:z=x
  . subst j9;exact jn (k1 jw)
  .
   exact jr (mUr _ (rS ⟨mUl _
    (mUl _ (mUl _ (rS ⟨hzS,jn⟩))),
    rG j9⟩))
 have je:w∈S_in:=q0w (p a) (k1 (jy a)) w j6;have jf:u∈S_in:=j4 (qt H (S \ (V_tg∪U)) (l - 1) {x} jx)
 have h9:∀ z∈j0.support,z∈S_in:=λ z hz =>
  j4 (qt H (S \ (V_tg∪U)) (l - 1) {x} (h0 z hz))
 have h4:∀ z∈j0.support,z ∉ U:=λ z hz hzu =>
  (pS (qt H (S \ (V_tg∪U)) (l - 1) {x} (h0 z hz))).2
   (mUr _ hzu)
 have h5:∀ z∈j0.support,z ∉ V_tg:=λ z hz hzv =>
  (pS (qt H (S \ (V_tg∪U)) (l - 1) {x} (h0 z hz))).2
   (mUl _ hzv)
 obtain ⟨j1,h7,jc,h2⟩ :=
  q0T (p a) j0 h8 h9 huw jf je j6 k0 hl1
 have j5:w≠st a:=by
  intro h;subst h
  have jg:∀ {u v:V} (q:(q3 H S_in).Walk u v) (h:u∈q.support),(q.takeUntil u h).length=0:=by
   intro u v q h;cases q <;> simp [Walk.takeUntil]
  have:=jg (p a) j6
  omega
 have h3:st a ∉ ((p a).dropUntil w j6).support:=by
  intro jo
  have jk:((p a).takeUntil w j6).support ++ ((p a).dropUntil w j6).support.tail=(p a).support:=by
   rw[<- support_append,take_spec (p a) j6]
  have jz:=(j2 a).1.support_nodup;rw[<- jk,nodup_append] at jz
  have jp:((p a).dropUntil w j6).support=w :: ((p a).dropUntil w j6).support.tail :=
   (cons_tail_support _).symm
  rw[jp,List.mem_cons] at jo
  rcases jo with jh | jj
  . exact j5 jh.symm
  . exact jz.2.2 (st a) (wSm _) (st a) jj rfl
 have jl:∀ z∈j1.support,z∈C∪X->z=x:=λ z hz hzCX=>by
  rcases h2 z hz with h6 | ja
  .
   by_contra j9
   have js:z∈U:=rS ⟨by
    rcases pU hzCX with hzC | hzX
    . exact mUr _ hzC
    . exact mUl _ (mUl _ (mUr _ hzX)),
    rG j9⟩
   exact h4 z h6 js
  . have hza:z=st a:=j8 a z (Walk.support_dropUntil_subset_support (p a) j6 ja) hzCX;rw[hza] at ja;exact absurd ja h3
 have jt:∀ j:Fin r',∀ z∈j1.support,z∈T j->j=tg a/\z=en a:=λ j z hz hzT=>by
  rcases h2 z hz with h6 | ja
  . exact absurd (mB.mpr ⟨j,mUv j,hzT⟩) (h5 z h6)
  . exact jm a j z (Walk.support_dropUntil_subset_support (p a) j6 ja) hzT
 have j7:∀ b:Fin q,b≠a->∀ z∈j1.support,z∈(p b).support->z=x/\z=st b:=λ b hba z hzq hzb=>by
  rcases h2 z hzq with h6 | ja
  .
   have j9:z=x:=by
    by_contra j9
    have js:z∈U:=rS ⟨mUl _ (mUr _
     (mB.mpr ⟨b,mUv b,rT hzb⟩)),
     rG j9⟩
    exact h4 z h6 js
   exact ⟨j9,j8 b z hzb (mUr _ (by rwa [j9]))⟩
  . have h1:=j3 a b hba.symm z (Walk.support_dropUntil_subset_support (p a) j6 ja) hzb;rw[h1.1] at ja;exact absurd ja h3
 obtain ⟨L',jq,hValid'⟩:=q0S H S_in C X s r' m3 q T st tg en p jy hen jb
  j2 j8 jm j3 jv a x jw jd j1 h7 jc jl jt j7
 exact ju L' jq hValid'
lemma q0V {V:Type*} (H:SG V) (S_in C X:FS V) (s r' m3 q:ℕ) (T:Fin r'->FS V) (st:Fin q->V) (tg:Fin q->Fin r') (en:Fin q->V) (p:∀ a:Fin q,(q3 H S_in).Walk (st a) (en a)) (hst:∀ a,st a∈X) (hen:∀ a,en a∈T (tg a)) (h8:Injective tg) (h1:∀ a,(p a).IsPath/\(p a).length<=m3) (j7:∀ a,∀ w∈(p a).support,w∈C∪X->w=st a) (j9:∀ a,∀ j:Fin r',∀ w∈(p a).support,w∈T j->j=tg a/\w=en a) (h9:∀ a b,a≠b->∀ w∈(p a).support,w∈(p b).support->w=st a/\w=st b) (ja:∀ x∈X,#(univ.filter (λ a=>st a=x))<=s) (x:V) (hxX:x∈X) (hx_cnt:#(univ.filter (λ a=>st a=x)) < s) (j0:Fin r') (jb:∀ a,tg a≠j0) (e0:V) (he0:e0∈T j0) (p0:(q3 H S_in).Walk x e0) (h4:p0.IsPath) (j1:p0.length<=m3) (j5:∀ w∈p0.support,w∈C∪X->w=x) (j8:∀ j:Fin r',∀ w∈p0.support,w∈T j->j=j0/\w=e0) (h0:∀ a,∀ w∈p0.support,w∈(p a).support->w=x/\w=st a) : ∃ L,q0R H S_in C X s r' T m3 (q+1) L:=by
 let h2:Fin (q+1)->V:=Fin.snoc st x;let j2:Fin (q+1)->Fin r':=Fin.snoc tg j0;let j3:Fin (q+1)->V:=Fin.snoc en e0
 let p1:∀ a:Fin (q+1),(q3 H S_in).Walk (h2 a) (j3 a) :=
  lastCases (p0.copy (by simp [h2]) (by simp [j3]))
   (λ b=>(p b).copy (by simp [h2]) (by simp [j3]))
 refine ⟨∑ a:Fin (q+1),(p1 a).length,h2,j2,j3,p1,?_,?_,?_,?_,?_,?_,?_,?_,rfl⟩
 .
  intro a;refine lastCases ?_ ?_ a
  . simp [h2,hxX]
  . intro b;simp [h2,hst b]
 .
  intro a;refine lastCases ?_ ?_ a
  . simp [j2,j3,he0]
  . intro b;simp [j2,j3,hen b]
 .
  intro a1 a2 h7;revert h7;refine lastCases ?_ ?_ a1 <;> refine lastCases ?_ ?_ a2
  . intro _;rfl
  . intro b h7;simp [j2] at h7;exact absurd h7.symm (jb b)
  . intro b h7;simp [j2] at h7;exact absurd h7 (jb b)
  . intro b1 b2 h7;simp [j2] at h7;exact congrArg Fin.castSucc (h8 h7)
 .
  intro a;refine lastCases ?_ ?_ a
  . simp only[p1,lastCases_last];exact ⟨q0p h4 _ _,by simp [j1]⟩
  . intro b;simp only[p1,lastCases_castSucc];exact ⟨q0p (h1 b).1 _ _,by simp [(h1 b).2]⟩
 .
  intro a w hw h3;revert hw h3;refine lastCases ?_ ?_ a
  . intro hw h3;simp only[p1,lastCases_last,support_copy,h2,snoc_last] at hw ⊢;exact j5 w hw h3
  . intro b hw h3;simp only[p1,lastCases_castSucc,support_copy,h2,snoc_castSucc] at hw ⊢;exact j7 b w hw h3
 .
  intro a j w hw j6;revert hw j6;refine lastCases ?_ ?_ a
  . intro hw j6;simp only[p1,lastCases_last,support_copy,j2,j3,snoc_last] at hw ⊢;exact j8 j w hw j6
  . intro b hw j6;simp only[p1,lastCases_castSucc,support_copy,j2,j3,snoc_castSucc] at hw ⊢;exact j9 b j w hw j6
 .
  intro a1 a2 hne' w h6 h5;revert hne' h6 h5;refine lastCases ?_ ?_ a1 <;> refine lastCases ?_ ?_ a2
  . intro h;exact absurd rfl h
  . intro b _ h6 h5;simp only[p1,lastCases_last,lastCases_castSucc,support_copy,h2,snoc_last,snoc_castSucc] at h6 h5 ⊢;exact h0 b w h6 h5
  . intro b _ h6 h5;simp only[p1,lastCases_last,lastCases_castSucc,support_copy,h2,snoc_last,snoc_castSucc] at h6 h5 ⊢;have h:=h0 b w h5 h6;exact ⟨h.2,h.1⟩
  . intro b1 b2 hne' h6 h5;simp only[p1,lastCases_castSucc,support_copy,h2,snoc_castSucc] at h6 h5 ⊢;exact h9 b2 b1 (λ h=>hne' (by rw[h])) w h6 h5
 .
  intro y hyX
  have j4:#(univ.filter (λ a:Fin (q+1)=>h2 a=y)) =
    #(univ.filter (λ b:Fin q=>st b=y))+(if x=y then 1 else 0):=by
   simp only[card_filter,Fin.sum_univ_castSucc,h2,snoc_castSucc,snoc_last]
  rw[j4]
  split_ifs with hxy
  . subst hxy;omega
  . have:=ja y hyX;omega
lemma q0W {V:Type*} (H:SG V) (S S_in C X:FS V)
  (s:ℕ) (r':ℕ) (T:Fin r'->FS V) (m3:ℕ)
  (hS_in:S_in⊆S) (hXS:X⊆S_in) (hr':r'=#X*s)
  (hTsub:∀ j:Fin r',T j⊆S_in \ (C∪X))
  (hTdisj:∀ j1 j2:Fin r',j1≠j2->Disjoint (T j1) (T j2))
  (ja:∀ (q:ℕ) (hq:q < r') (st:Fin q->V) (tg:Fin q->Fin r') (en:Fin q->V)
   (p:∀ a:Fin q,(q3 H S_in).Walk (st a) (en a)),
   (∀ a,st a∈X)->(∀ a,en a∈T (tg a))->Injective tg ->
   (∀ a,(p a).IsPath/\(p a).length<=m3) ->
   (∀ a,∀ w∈(p a).support,w∈C∪X->w=st a) ->
   (∀ a,∀ j:Fin r',∀ w∈(p a).support,w∈T j->j=tg a/\w=en a) ->
   (∀ a b,a≠b->∀ w∈(p a).support,w∈(p b).support->w=st a/\w=st b) ->
   (∀ x∈X,#(univ.filter (λ a=>st a=x))<=s) ->
   ∀ x∈X,#(univ.filter (λ a=>st a=x)) < s ->
   ∀ j0:Fin r',(∀ a,tg a≠j0) ->
   let U:FS V:=((S \ S_in)∪X∪(univ.biUnion (λ a=>(p a).support.toFinset))∪C) \ {x}
   let V_tg:FS V:=univ.biUnion T
   (∀ a,∀ l:ℕ,1<=l ->
    #(qn H S (qs H (S \ (V_tg∪U)) (l - 1) {x})∩(p a).support.toFinset)<=l+1) ->
   ∃ (e0:V) (_:e0∈T j0) (p0:(q3 H S_in).Walk x e0),
    p0.IsPath/\p0.length<=m3 /\
    (∀ w∈p0.support,w∈C∪X->w=x) /\
    (∀ j:Fin r',∀ w∈p0.support,w∈T j->j=j0/\w=e0) /\
    (∀ a,∀ w∈p0.support,w∈(p a).support->w=x/\w=st a)) :
  ∃ (st:Fin r'->V) (tg:Fin r'->Fin r') (en:Fin r'->V)
   (p:∀ a:Fin r',(q3 H S_in).Walk (st a) (en a)),
   (∀ a,st a∈X)/\(∀ a,en a∈T (tg a))/\Injective tg /\
   (∀ a,(p a).IsPath/\(p a).length<=m3) /\
   (∀ a,∀ w∈(p a).support,w∈C∪X->w=st a) /\
   (∀ a,∀ j:Fin r',∀ w∈(p a).support,w∈T j->j=tg a/\w=en a) /\
   (∀ a b,a≠b->∀ w∈(p a).support,w∈(p b).support->w=st a/\w=st b) /\
   (∀ x∈X,#(univ.filter (λ a=>st a=x))=s):=by
 have hV0:∃ L,q0R H S_in C X s r' T m3 0 L :=
  ⟨0,Fin.elim0,Fin.elim0,Fin.elim0,λ a=>a.elim0,
   λ a=>a.elim0,λ a=>a.elim0,λ a=>a.elim0,λ a=>a.elim0,
   λ a=>a.elim0,λ a=>a.elim0,λ a=>a.elim0,λ _ _=>by simp,by simp⟩
 let Qs:=(range (r'+1)).filter (λ q=>∃ L,q0R H S_in C X s r' T m3 q L)
 have j7:Qs.Nonempty:=⟨0,rF ⟨mem_range.mpr (Nat.zero_lt_succ _),hV0⟩⟩;let q:=Qs.max' j7;have j3:q∈Qs:=max'_mem Qs j7;have jk:q<=r':=Nat.lt_succ_iff.mp (mem_range.mp (pF j3).1);have jf:∃ L,q0R H S_in C X s r' T m3 q L:=(pF j3).2;obtain ⟨st,tg,en,p,ji,jr,h0,h3,h7,j8,h4,j6,jj⟩:=find_spec jf
 have jl:q=r':=by
  by_contra js;have je:q < r':=lt_of_le_of_ne jk js
  have jo:∃ x∈X,#(univ.filter (λ a:Fin q=>st a=x)) < s:=by
   by_contra jq;push Not at jq
   have h5:∑ x∈X,#(univ.filter (λ a:Fin q=>st a=x))=q:=by
    rw[<- card_biUnion]
    .
     have jt:X.biUnion (λ x=>univ.filter (λ a:Fin q=>st a=x))=univ:=by
      ext a;simp only[mB,mF,mUv,true_and,iff_true]
      exact ⟨st a,ji a,rfl⟩
     rw[jt];simp
    . intro x1 _ x2 _ hne';rw[Function.onFun,dL];intro a h1 h2;exact hne' ((pF h1).2.symm.trans (pF h2).2)
   have hge:#X*s<=q:=by
    calc
     #X*s=∑ _x∈X,s:=by simp
     _<=∑ x∈X,#(univ.filter (λ a:Fin q=>st a=x)):=sum_le_sum jq
     _=q:=h5
   omega
  obtain ⟨x,jh,h6⟩:=jo
  have jp:∃ j0:Fin r',∀ a:Fin q,tg a≠j0:=by
   have h9:#(univ.image tg) < #(univ:FS (Fin r')):=by
    calc
     #(univ.image tg)<=#(univ:FS (Fin q)):=card_image_le
     _=q:=by simp
     _ < r':=je
     _=#(univ:FS (Fin r')):=by simp
   obtain ⟨j0,_,jc⟩:=exists_mem_notMem_of_card_lt_card h9;exact ⟨j0,λ a h=>jc (mem_image.mpr ⟨a,mUv a,h⟩)⟩
  obtain ⟨j0,ju⟩:=jp
  have jn:=q0U H S S_in C X s r' m3 q T hXS st tg en p ji jr h0
   h3 h7 j8 h4 j6 (λ L' hL'=>Nat.find_min jf (jj ▸ hL')) x jh h6
  obtain ⟨e0,he0,p0,j4,j9,jg,jm,j5⟩ :=
   ja q je st tg en p ji jr h0 h3 h7 j8 h4 j6 x jh h6 j0 ju jn
  have jd:=q0V H S_in C X s r' m3 q T st tg en p ji jr h0
   h3 h7 j8 h4 j6 x jh h6 j0 ju e0 he0 p0 j4 j9 jg jm j5
  have h8:q+1∈Qs:=rF ⟨mem_range.mpr (by omega),jd⟩
  have:=le_max' Qs (q+1) h8
  omega
 clear_value q
 subst jl;refine ⟨st,tg,en,p,ji,jr,h0,h3,h7,j8,h4,λ x jh=>?_⟩
 by_contra js;have hlt:#(univ.filter (λ a:Fin q=>st a=x)) < s:=lt_of_le_of_ne (j6 x jh) js
 have h5:∑ y∈X,#(univ.filter (λ a:Fin q=>st a=y))=q:=by
  rw[<- card_biUnion]
  .
   have jt:X.biUnion (λ y=>univ.filter (λ a:Fin q=>st a=y))=univ:=by
    ext a;simp only[mB,mF,mUv,true_and,iff_true]
    exact ⟨st a,ji a,rfl⟩
   rw[jt];simp
  . intro x1 _ x2 _ hne';rw[Function.onFun,dL];intro a h1 h2;exact hne' ((pF h1).2.symm.trans (pF h2).2)
 have jb:∑ y∈X,#(univ.filter (λ a:Fin q=>st a=y)) < ∑ _y∈X,s :=
  Finset.sum_lt_sum (λ y hy=>j6 y hy) ⟨x,jh,hlt⟩
 simp only[sum_const,smul_eq_mul] at jb;omega
lemma q0X {e1 e2:O} {t s K:ℕ}
  (j3:0 < e1) (he11:e1 < 1) (he20:0 < e2) (ht:1<=t) (hs:1<=s) (hK:10<=K) :
  let r:=t*s
  let k_big:=max (2*(10*r+10)) (K+10)
  let C_u:O:=(3*r+t+r*(120/e1+1)+4:O)
  ∀ᶠ x:O in atTop,
   (15/e2<=x/\(2*(10*r+10+1)+2:O)<=x /\
    2*(r:O)<=(e2*x/2)*(e1/(log (15/2))^2)/4 /\
    (4:O)<=log x/\(10:O)<=x - 2/\(1:O) < log (x - 2)) /\
   ((10:O)<=4/e1*(log x)^3 /\
    2*(log (log x))^5+4<=40/e1*(log x)^3 /\
    4*C_u*(log x)^4<=(log x)^(2*K) /\
    C_u*(log x)^6<=(e1/4)*(log x)^(2*K) /\
    2*(r:O)*((log x)^K+1)<=(log x)^(2*K)/2 /\
    (r:O)*((log x)^K+1)^2<=(18/e1*(log x)^3)^(300*k_big)) /\
   ((((log x)^K+1)^2+1)^(20*(log (log x))^5+20) *
     ((r+t:O)+2*log x+3) < x/2 /\
    (2*r:O)+2*log x+3 < x/2):=by
 intro r k_big C_u;have hr1:1<=r:=Nat.mul_pos ht hs
 have h1:∀ᶠ x:O in atTop,
   15/e2<=x/\(2*(10*r+10+1)+2:O)<=x /\
   2*(r:O)<=(e2*x/2)*(e1/(log (15/2))^2)/4 /\
   (4:O)<=log x/\(10:O)<=x - 2/\(1:O) < log (x - 2):=by
  let B1:=max (15/e2) (max (2*(10*r+10+1)+2:O)
   (max (16*(r:O)*(log (15/2))^2/(e1*e2)) 100))
  filter_upwards [eGe B1,lGe 4] with x hx hl
  have h15:15/e2<=x:=lT (lMl _ _) hx;have h2r:(2*(10*r+10+1)+2:O)<=x:=lT (lMl _ _) (lT (lMr _ _) hx)
  have jb:16*(r:O)*(log (15/2))^2/(e1*e2)<=x :=
   lT (lMl _ _) (lT (lMr _ _) (lT (lMr _ _) hx))
  have hx100:(100:O)<=x :=
   lT (lMr _ _) (lT (lMr _ _) (lT (lMr _ _) hx))
  have hlog15:0 < log (15/2):=lPs (by norm_num)
  have j4:2*(r:O)<=(e2*x/2)*(e1/(log (15/2))^2)/4:=by
   rw[dLi (by positivity)] at jb;have j6:=mlR jb (show (0:O)<=1/(8*(log (15/2))^2) by positivity)
   have hlhs:16*(r:O)*(log (15/2))^2*(1/(8*(log (15/2))^2))=2*(r:O):=by
     field_simp;ring
   have hrhs:x*(e1*e2)*(1/(8*(log (15/2))^2)) =
      (e2*x/2)*(e1/(log (15/2))^2)/4:=by field_simp;ring
   linarith
  refine ⟨h15,h2r,j4,hl,by linarith,?_⟩;rw[lIt (by linarith)];linarith [e1l]
 have h2:∀ᶠ x:O in atTop,
   (10:O)<=4/e1*(log x)^3 /\
   2*(log (log x))^5+4<=40/e1*(log x)^3 /\
   4*C_u*(log x)^4<=(log x)^(2*K) /\
   C_u*(log x)^6<=(e1/4)*(log x)^(2*K) /\
   2*(r:O)*((log x)^K+1)<=(log x)^(2*K)/2 /\
   (r:O)*((log x)^K+1)^2<=(18/e1*(log x)^3)^(300*k_big):=by
  filter_upwards [lGe (max 4 (max (4*C_u+1) (max (4*C_u/e1+1) (4*(r:O)+4)))),
   q02 (C:=1) 5 (β:=3) (by norm_num)] with x hl hll
  rw[one_mul,Real.rpow_ofNat] at hll;have hl4:4<=log x:=lT (lMl _ _) hl;have h4Cu:4*C_u+1<=log x:=lT (lMl _ _) (lT (lMr _ _) hl)
  have j8:4*C_u/e1+1<=log x :=
   lT (lMl _ _) (lT (lMr _ _) (lT (lMr _ _) hl))
  have h4r0:4*(r:O)+4<=log x :=
   lT (lMr _ _) (lT (lMr _ _) (lT (lMr _ _) hl))
  have hl3:(64:O)<=(log x)^3:=calc (64:O)=4^3:=by norm_num
   _<=(log x)^3:=pLl (by norm_num) hl4 3
  have h4e:4<=4/e1:=by rw[lDi j3];linarith
  have h18e:18<=18/e1:=by rw[lDi j3];linarith
  have h40e:40<=40/e1:=by rw[lDi j3];linarith
  have h0:1<=log x:=by linarith
  refine ⟨by nlinarith,by nlinarith,?_,?_,?_,?_⟩
  .
   calc 4*C_u*(log x)^4<=log x*(log x)^4 :=
       mlR (by linarith) (by positivity)
     _=(log x)^5:=by rw[<- pow_succ']
     _<=(log x)^(2*K):=pLr h0 (by omega)
  .
   have h6:C_u<=(e1/4)*log x:=by
     have:=mlL j8 (show (0:O)<=e1/4 by positivity)
     have heq:e1/4*(4*C_u/e1+1)=C_u+e1/4:=by field_simp
     linarith
   calc
     C_u*(log x)^6<=((e1/4)*log x)*(log x)^6 :=
       mlR h6 (by positivity)
     _=(e1/4)*(log x)^7:=by ring
     _<=(e1/4)*(log x)^(2*K):=mlL (pLr h0 (by omega)) (by positivity)
  .
   have h6:(log x)^K+1<=2*(log x)^K:=by
     have:(1:O)<=(log x)^K:=oLp h0;linarith
   have j5:4*(r:O)<=(log x)^K/2:=by
     calc
      4*(r:O)<=log x:=by linarith
      _<=(log x)^2/2:=by nlinarith
      _<=(log x)^K/2:=dLr (pLr h0 (by omega)) (by norm_num)
   calc
     2*(r:O)*((log x)^K+1)<=2*(r:O)*(2*(log x)^K) :=
       mlL h6 (by positivity)
     _=(4*(r:O))*(log x)^K:=by ring
     _<=((log x)^K/2)*(log x)^K:=mlR j5 (by positivity)
     _=(log x)^(2*K)/2:=by rw[two_mul,pow_add];ring
  .
   have h6:(log x)^K+1<=2*(log x)^K:=by
     have:(1:O)<=(log x)^K:=oLp h0;linarith
   have ja:((log x)^K+1)^2<=4*(log x)^(2*K):=by
     have h:=pLl (by positivity) h6 2;rw[mul_pow,<- pow_mul,mul_comm K 2] at h;norm_num at h;exact h
   have h4r:4*(r:O)<=(log x)^2:=by nlinarith
   have j0:(log x)^(2*K+2)<=(18/e1*(log x)^3)^(300*k_big):=by
     have h9:log x<=18/e1*(log x)^3:=by nlinarith
     calc
      (log x)^(2*K+2)<=(log x)^(300*k_big) :=
        pLr h0 (by have:K+10<=k_big:=lMr _ _;omega)
      _<=(18/e1*(log x)^3)^(300*k_big):=pLl (by positivity) h9 _
   calc
     (r:O)*((log x)^K+1)^2<=(r:O)*(4*(log x)^(2*K)) :=
       mlL ja (nCn r)
     _=(4*(r:O))*(log x)^(2*K):=by ring
     _<=(log x)^2*(log x)^(2*K):=mlR h4r (by positivity)
     _=(log x)^(2*K+2):=by rw[<- pow_add,add_comm]
     _<=(18/e1*(log x)^3)^(300*k_big):=j0
 have h3:∀ᶠ x:O in atTop,
   (((log x)^K+1)^2+1)^(20*(log (log x))^5+20) *
     ((r+t:O)+2*log x+3) < x/2 /\
   (2*r:O)+2*log x+3 < x/2:=by
  have j1:Filter.Tendsto (λ x:O=>log (log x)) atTop atTop :=
   tL.comp tL
  filter_upwards [q03 (C:=(40*(2*K+4):O)) 6 (β:=1/2) (by norm_num),
   q01 (C:=(2*(r+t+6):O)) 1 (β:=1/4) (by norm_num),
   j1.eventually_ge_atTop 4,lGe 4,
   eGe (1000:O)] with x hexp6 hlin hll hl hx
  rw[pow_one] at hlin
  have h7:0 < log x:=by linarith
  have h0:1<=log x:=by linarith
  have h4:0 < x:=by linarith
  have h9:((log x)^K+1)^2+1<=(log x)^(2*K+3):=by
   have h6:(log x)^K+1<=2*(log x)^K:=by
     have:(1:O)<=(log x)^K:=oLp h0;linarith
   have ja:((log x)^K+1)^2<=4*(log x)^(2*K):=by
     have h:=pLl (by positivity) h6 2;rw[mul_pow,<- pow_mul,mul_comm K 2] at h;norm_num at h;exact h
   have h5:(5:O)<=(log x)^3:=by
     calc
      (5:O)<=4^3:=by norm_num
      _<=(log x)^3:=pLl (by norm_num) hl 3
   have h1k:(1:O)<=(log x)^(2*K):=oLp h0
   calc
     ((log x)^K+1)^2+1<=5*(log x)^(2*K):=by linarith
     _<=(log x)^3*(log x)^(2*K):=mlR h5 (by positivity)
     _=(log x)^(2*K+3):=by rw[<- pow_add,add_comm]
  have j2:(((log x)^K+1)^2+1)^(20*(log (log x))^5+20) <=
     x^(1/2:O):=by
   have h6:=rLl (by positivity) h9 (show (0:O)<=20*(log (log x))^5+20 by positivity);rw[<- rN (log x) (2*K+3),<- rpow_mul h7.le,rpow_def_of_pos h7] at h6;refine h6.trans ((eLe.mpr ?_).trans hexp6);have hll5:(1:O)<=(log (log x))^5:=oLp (by linarith)
   have h20:20*(log (log x))^5+20<=40*(log (log x))^5:=by linarith
   have j6:((2*K+3:ℕ):O)*(20*(log (log x))^5+20) <=
      (40*(2*K+4):O)*(log (log x))^5:=by
     push_cast;nlinarith
   have hmul2:=mlL j6 (show (0:O)<=log (log x) by linarith)
   linarith [show log (log x)*((40*(2*K+4):O)*(log (log x))^5) =
      (40*(2*K+4):O)*(log (log x))^6 by ring,
     show log (log x)*(((2*K+3:ℕ):O)*(20*(log (log x))^5+20)) =
      log (log x)*(((2*K+3:ℕ):O)*(20*(log (log x))^5+20)) by ring]
  have j7:(r+t:O)+2*log x+3<=x^(1/4:O):=by
   have h6:(r+t:O)+2*log x+3<=(2*(r+t+6):O)*log x:=by nlinarith
   exact h6.trans hlin
  have j9:x^(3/4:O) < x/2:=by
   have hx14:4<=x^(1/4:O):=by
     have h6:(4:O)^(4:ℕ)<=x:=by norm_num;linarith
     have j5:=rLl (by positivity) h6 (show (0:O)<=1/4 by norm_num);rw[<- rN,<- rpow_mul (by norm_num)] at j5;norm_num at j5;exact j5
   have hsp:x=x^(3/4:O)*x^(1/4:O):=by
     rw[<- rpow_add h4];norm_num
   have hpos34:0 < x^(3/4:O):=rpow_pos_of_pos h4 _;nlinarith
  have h8:x^(1/2:O)*x^(1/4:O)=x^(3/4:O):=by
   rw[<- rpow_add h4];norm_num
  refine ⟨?_,?_⟩
  .
   calc (((log x)^K+1)^2+1)^(20*(log (log x))^5+20) *
       ((r+t:O)+2*log x+3)
      <= x^(1/2:O)*x^(1/4:O):=mLm j2 j7 (by positivity) (by positivity)
     _=x^(3/4:O):=h8
     _ < x/2:=j9
  .
   have h6:(2*r:O)+2*log x+3<=(2*(r+t+6):O)*log x:=by nlinarith
   have j5:x^(1/4:O)<=x^(3/4:O):=rLe (by linarith) (by norm_num);linarith
 exact h1.and (h2.and h3)
lemma q0Y {e1 e2:O} {t s K:ℕ}
  (jl:0 < e1) (jk:e1 < 1) (ju:0 < e2) (ht:1<=t) (hs:1<=s) (hK:10<=K) :
  let r:=t*s
  let k_lc:=2*(10*r+10)
  let k_big:=max k_lc (K+10)
  ∃ d0:ℕ,100<=d0/\∀ n d:ℕ,d0<=d->d<=n ->
   let m:=floor (40/e1*(log (n:O))^3)
   let m_lc:=floor (18/e1*(log (n:O))^3)
   let l0_lc:=floor ((log (log (n:O)))^5)
   let l0:=2*l0_lc+2
   let D_big:=ceil ((log (n:O))^K)
   let D_:=D_big^2
   let Umax:=3*r+t+r*(3*m+1)+ceil (2*log (n:O)/log ((d - 1 - 1:ℕ):O)+2)
   (15/e2<=(d:O)) /\
   (10*r+10+1<=d/2) /\
   (2*(r:O)<=(e2*(d:O)/2)*(e1/(log (15/2))^2)/4) /\
   (2*m_lc+2<=3*m) /\
   (m_lc+m+2<=3*m) /\
   (3*m+2*l0_lc+2<=5*m) /\
   (2*Umax<=D_) /\
   ((Umax:O)*(log (n:O))^3<=10*((D_ - Umax:ℕ):O)) /\
   ((Umax:O)<=(D_:O)*(e1/(log (n:O))^2)/4) /\
   (Umax+2*r*D_big<=D_) /\
   (((r*D_:ℕ):O)<=(18/e1*(log (n:O))^3)^(300*k_big)) /\
   ((D_:O)<=(18/e1*(log (n:O))^3)^(400*k_big)) /\
   (1<=D_big) /\
   ((D_+1)^(10*l0)*(r+t+ceil (2*log (n:O)/log ((d - 1 - 1:ℕ):O)+2)) <
    n - 2*r - ceil (2*log (n:O)/log ((d - 1 - 1:ℕ):O)+2)) /\
   (2*r+ceil (2*log (n:O)/log ((d - 1 - 1:ℕ):O)+2) < n):=by
 intro r k_lc k_big;have hr1:1<=r:=Nat.mul_pos ht hs;have jn:=q0X (t:=t) (s:=s) (K:=K) jl jk ju ht hs hK;rw[eAt] at jn;obtain ⟨B,hB⟩:=jn;refine ⟨max 100 (ceil B),lMl _ _,λ n d hd hdn=>?_⟩
 have k1:B<=(d:O):=(nLc B).trans (by exact_mod_cast (lMr 100 (ceil B)).trans hd);have hnR:B<=(n:O):=k1.trans (by exact_mod_cast hdn);have jp:=hB (d:O) k1;have j0:=hB (n:O) hnR;intro m m_lc l0_lc l0 D_big D_ Umax;have jz:15/e2<=(d:O):=jp.1.1
 have jc:10*r+10+1<=d/2:=by
  have:(2*(10*r+10+1)+2:O)<=(d:O):=jp.1.2.1
  have hN:2*(10*r+10+1)+2<=d:=by exact_mod_cast this
  omega
 have je:2*(r:O)<=(e2*(d:O)/2)*(e1/(log (15/2))^2)/4:=jp.1.2.2.1;have hl4:4<=log (n:O):=j0.1.2.2.2.1;have hll_nn:0<=log (log (n:O)):=lNn (by linarith)
 have ja:1 < log ((d - 1 - 1:ℕ):O):=by
  have hd2:2<=d:=by omega
  have jm:((d - 1 - 1:ℕ):O)=(d:O) - 2:=by
   rw[show d - 1 - 1=d - 2 by omega,Nat.cast_sub hd2,Nat.cast_ofNat]
  rw[jm];exact jp.1.2.2.2.2.2
 have h9:((ceil (2*log (n:O)/log ((d - 1 - 1:ℕ):O)+2):ℕ):O) <=
   2*log (n:O)+3:=by
  have j4:2*log (n:O)/log ((d - 1 - 1:ℕ):O)<=2*log (n:O) :=
   dLs (by positivity) ja.le
  have jh:=ceil_lt_add_one (show (0:O)<=2*log (n:O)/log ((d - 1 - 1:ℕ):O)+2 by positivity);linarith
 have j7:(m:O)<=40/e1*(log (n:O))^3:=nFl (by positivity)
 have j2:40/e1*(log (n:O))^3 - 1 < (m:O):=by linarith [nL1 (40/e1*(log (n:O))^3)]
 have h8:(m_lc:O)<=18/e1*(log (n:O))^3:=nFl (by positivity);have j3:(l0_lc:O)<=(log (log (n:O)))^5:=nFl (by positivity);have j9:(log (n:O))^K<=(D_big:O):=nLc _;have j8:(D_big:O)<=(log (n:O))^K+1:=(ceil_lt_add_one (by positivity)).le
 have h3:(log (n:O))^(2*K)<=(D_:O):=by
  dsimp only[D_];push_cast
  calc
   (log (n:O))^(2*K)=((log (n:O))^K)^2:=by rw[<- pow_mul,mul_comm]
   _<=(D_big:O)^2:=pLl (by positivity) j9 2
 have h7:(D_:O)<=((log (n:O))^K+1)^2:=by
  dsimp only[D_];push_cast;exact pLl (nCn _) j8 2
 let h5:O:=(3*r+t+r*(120/e1+1)+4:O)
 have h1:(Umax:O)<=h5*(log (n:O))^3:=by
  dsimp only[Umax];push_cast;have jg:(1:O)<=(log (n:O))^3:=oLp (by linarith)
  have jb:log (n:O)<=(log (n:O))^3:=by
   calc
    log (n:O)=(log (n:O))^1:=(pow_one _).symm
    _<=(log (n:O))^3:=pLr (by linarith) (by omega)
  have jr:(r:O)*(3*(m:O)+1)<=(r:O)*(120/e1+1)*(log (n:O))^3:=by
   have j4:3*(m:O)+1<=(120/e1+1)*(log (n:O))^3:=by
    have jx:3*(40/e1*(log (n:O))^3)=120/e1*(log (n:O))^3:=by ring
    have jy:(120/e1+1)*(log (n:O))^3=120/e1*(log (n:O))^3+(log (n:O))^3:=by ring
    linarith only[j7,jg,jx,jy]
   have jh:=mlL j4 (nCn r)
   linarith only[jh,show (r:O)*((120/e1+1)*(log (n:O))^3) =
     (r:O)*(120/e1+1)*(log (n:O))^3 by ring]
  have jw:(3*(r:O)+(t:O))<=(3*(r:O)+(t:O))*(log (n:O))^3 :=
   le_mul_of_one_le_right (by positivity) jg
  have jt:(16:O)<=(log (n:O))^3 :=
   calc
    (16:O)<=4^3:=by norm_num
    _<=(log (n:O))^3:=pLl (by norm_num) hl4 3
  have hc4:2*log (n:O)+3<=4*(log (n:O))^3:=by linarith only[jb,jt]
  have jo:h5*(log (n:O))^3=(3*(r:O)+(t:O))*(log (n:O))^3 +
    (r:O)*(120/e1+1)*(log (n:O))^3+4*(log (n:O))^3:=by dsimp only[h5];ring
  linarith only[h9,jr,jw,hc4,jo]
 have h0:2*Umax<=D_:=by
  have j4:2*(Umax:O)<=(D_:O):=by
   have h4:=j0.2.1.2.2.1;have jg:(log (n:O))^3<=(log (n:O))^4:=pLr (by linarith) (by omega)
   have hCu_nn:0<=h5:=by positivity
   have j1:=mlL jg (show (0:O)<=4*h5 by positivity)
   linarith only[h1,h3,h4,j1,
    show 4*h5*(log (n:O))^3=4*(h5*(log (n:O))^3) by ring,
    show 0<=(Umax:O) from nCn _]
  exact_mod_cast j4
 have j6:2*(18/e1*(log (n:O))^3)+4/e1*(log (n:O))^3 =
   40/e1*(log (n:O))^3:=by ring
 have h18_40:18/e1*(log (n:O))^3+40/e1*(log (n:O))^3 +
   22/e1*(log (n:O))^3=80/e1*(log (n:O))^3:=by ring
 have h4_le_22:4/e1*(log (n:O))^3<=22/e1*(log (n:O))^3:=by
  have ji:0<=(log (n:O))^3/e1:=by positivity
  linarith only[ji,show 4/e1*(log (n:O))^3=4*((log (n:O))^3/e1) by ring,
   show 22/e1*(log (n:O))^3=22*((log (n:O))^3/e1) by ring]
 refine ⟨jz,jc,je,?_,?_,?_,h0,?_,?_,?_,?_,?_,?_,?_,?_⟩
 .
  have hR:((2*m_lc+2:ℕ):O)<=((3*m:ℕ):O):=by
   push_cast;linarith only[h8,j2,j6,j0.2.1.1]
  exact_mod_cast hR
 .
  have hR:((m_lc+m+2:ℕ):O)<=((3*m:ℕ):O):=by
   have h62:4/e1*(log (n:O))^3<=62/e1*(log (n:O))^3:=by
    have ji:0<=(log (n:O))^3/e1:=by positivity
    linarith only[ji,show 4/e1*(log (n:O))^3=4*((log (n:O))^3/e1) by ring,
     show 62/e1*(log (n:O))^3=62*((log (n:O))^3/e1) by ring]
   have jf:18/e1*(log (n:O))^3+62/e1*(log (n:O))^3 =
     2*(40/e1*(log (n:O))^3):=by ring
   push_cast;linarith only[h8,j2,jf,h62,j0.2.1.1]
  exact_mod_cast hR
 .
  have hR:((3*m+2*l0_lc+2:ℕ):O)<=((5*m:ℕ):O):=by
   push_cast;linarith only[j7,j2,j3,j0.2.1.2.1]
  exact_mod_cast hR
 .
  rw[Nat.cast_sub (by omega:Umax<=D_)]
  have j4:(Umax:O)*(log (n:O))^3<=h5*(log (n:O))^6:=by
   have:=mlR h1 (show (0:O)<=(log (n:O))^3 by positivity)
   linarith only[this,show h5*(log (n:O))^3*(log (n:O))^3=h5*(log (n:O))^6 by ring]
  have jh:h5*(log (n:O))^6<=(log (n:O))^(2*K):=by
   have h6:=j0.2.1.2.2.2.1
   have ji:0<=(log (n:O))^(2*K):=by positivity
   have hε:(e1/4)*(log (n:O))^(2*K)<=(log (n:O))^(2*K):=by nlinarith only[jk,ji]
   linarith only[h6,hε]
  have jv:2*(Umax:O)<=(D_:O):=by exact_mod_cast h0
  linarith only[j4,jh,h3,jv]
 .
  have j4:(Umax:O)*(log (n:O))^2<=h5*(log (n:O))^6:=by
   have hsq:(log (n:O))^2<=(log (n:O))^3:=pLr (by linarith) (by omega);have j1:=mlR h1 (show (0:O)<=(log (n:O))^2 by positivity);have jj:=mlL hsq (show (0:O)<=h5*(log (n:O))^3 by positivity);linarith only[j1,jj,show h5*(log (n:O))^3*(log (n:O))^3=h5*(log (n:O))^6 by ring]
  have jh:h5*(log (n:O))^6<=(e1/4)*(D_:O) :=
   j0.2.1.2.2.2.1.trans (mlL h3 (by positivity))
  have h3':(Umax:O)*(log (n:O))^2<=(e1/4)*(D_:O):=j4.trans jh
  have jq:(D_:O)*(e1/(log (n:O))^2)/4=(e1/4)*(D_:O)/(log (n:O))^2:=by ring
  rw[jq,lDi (by positivity)];exact h3'
 .
  have hR:((Umax+2*r*D_big:ℕ):O)<=(D_:O):=by
   push_cast
   have jv:2*(Umax:O)<=(D_:O):=by exact_mod_cast h0
   have hrD:2*(r:O)*(D_big:O)<=(log (n:O))^(2*K)/2 :=
    (mlL j8 (by positivity)).trans j0.2.1.2.2.2.2.1
   linarith only[jv,hrD,h3]
  exact_mod_cast hR
 . push_cast;exact (mlL h7 (nCn r)).trans j0.2.1.2.2.2.2.2
 .
  have j4:(D_:O)<=(r:O)*((log (n:O))^K+1)^2:=by
   have hrR:(1:O)<=(r:O):=by exact_mod_cast hr1
   calc
    (D_:O)<=1*((log (n:O))^K+1)^2:=by linarith only[h7]
    _<=(r:O)*((log (n:O))^K+1)^2:=mlR hrR (by positivity)
  have jd:(1:O)<=18/e1*(log (n:O))^3:=by
   have h18:18<=18/e1:=by rw[lDi jl];linarith
   have jg:(1:O)<=(log (n:O))^3:=oLp (by linarith);nlinarith only[h18,jg]
  exact j4.trans (j0.2.1.2.2.2.2.2.trans (pLr jd (by omega)))
 .
  have:(1:O)<=(D_big:O):=(oLp (by linarith:(1:O)<=log (n:O))).trans j9
  exact_mod_cast this
 .
  have h2:(2*(r:O)+((ceil (2*log (n:O)/log ((d - 1 - 1:ℕ):O)+2):ℕ):O)) < (n:O)/2:=by
   linarith only[h9,j0.2.2.2]
  have hR:(((D_+1)^(10*l0)*(r+t+ceil (2*log (n:O)/log ((d - 1 - 1:ℕ):O)+2)):ℕ):O) <
    (n:O) - (2*(r:O)+((ceil (2*log (n:O)/log ((d - 1 - 1:ℕ):O)+2):ℕ):O)):=by
   push_cast
   have k0:((10*l0:ℕ):O)<=20*(log (log (n:O)))^5+20:=by
    dsimp only[l0];push_cast;linarith only[j3]
   have js:((D_:O)+1)^(10*l0) <=
     (((log (n:O))^K+1)^2+1)^(20*(log (log (n:O)))^5+20):=by
    calc
     ((D_:O)+1)^(10*l0)
      <= (((log (n:O))^K+1)^2+1)^(10*l0):=pLl (by positivity) (by linarith only[h7]) _
     _=(((log (n:O))^K+1)^2+1)^((10*l0:ℕ):O):=(rN _ _).symm
     _<=_:=rLe (by linarith [show (0:O)<=((log (n:O))^K+1)^2 by positivity]) k0
   have j1:=mLm js (show (r:O)+(t:O)+((ceil (2*log (n:O)/log ((d - 1 - 1:ℕ):O)+2):ℕ):O) <=
     (r+t:O)+2*log (n:O)+3 by linarith only[h9]) (by positivity) (by positivity)
   linarith only[j1,j0.2.2.1,h2]
  have j5:2*r+ceil (2*log (n:O)/log ((d - 1 - 1:ℕ):O)+2)<=n:=by
   have:((2*r+ceil (2*log (n:O)/log ((d - 1 - 1:ℕ):O)+2):ℕ):O) < (n:O):=by
    push_cast;linarith only[h2,show (0:O) < (n:O) by exact_mod_cast (show 0 < n by omega)]
   exact_mod_cast this.le
  have hR2:(((D_+1)^(10*l0)*(r+t+ceil (2*log (n:O)/log ((d - 1 - 1:ℕ):O)+2)):ℕ):O) <
    ((n - 2*r - ceil (2*log (n:O)/log ((d - 1 - 1:ℕ):O)+2):ℕ):O):=by
   rw[show n - 2*r - ceil (2*log (n:O)/log ((d - 1 - 1:ℕ):O)+2) =
     n - (2*r+ceil (2*log (n:O)/log ((d - 1 - 1:ℕ):O)+2)) by omega,
    Nat.cast_sub j5]
   push_cast at hR ⊢;exact hR
  exact_mod_cast hR2
 .
  have:((2*r+ceil (2*log (n:O)/log ((d - 1 - 1:ℕ):O)+2):ℕ):O) < (n:O):=by
   push_cast;linarith only[h9,j0.2.2.2,show (0:O) < (n:O) by exact_mod_cast (show 0 < n by omega)]
  exact_mod_cast this
lemma q0Z {V:Type*} (m D:ℕ) (S_:Fin m->FS V) (Forb:FS V) (h9:∀ i:Fin m,#Forb+m*D<=#(S_ i)) : ∃ A:Fin m->FS V, (∀ i,A i⊆S_ i \ Forb) /\ (∀ i,#(A i)=D) /\ (∀ i j,i≠j->Disjoint (A i) (A j)):=by
 suffices h:∀ k (hk:k<=m),
   ∃ A:Fin k->FS V,
    (∀ i:Fin k,A i⊆S_ ⟨i.val,by omega⟩ \ Forb) /\
    (∀ i:Fin k,#(A i)=D) /\
    (∀ i j:Fin k,i≠j->Disjoint (A i) (A j)) by
  exact h m le_rfl
 intro k
 induction k with
 | zero=>intro _;exact ⟨Fin.elim0,λ i=>i.elim0,λ i=>i.elim0,λ i=>i.elim0⟩
 | succ k ih =>
  intro hk;obtain ⟨A,j0,h6,h8⟩:=ih (by omega);let h7:=Forb∪univ.biUnion A
  have hUsed:h7.card<=#Forb+k*D:=by
   calc
    h7.card<=#Forb+#(univ.biUnion A):=cUl _ _
    _<=#Forb+∑ i:Fin k,#(A i):=Nat.add_le_add_left cBu _
    _=#Forb+k*D:=by simp [h6]
  have j3:D<=#(S_ ⟨k,by omega⟩ \ h7):=by
   have h1:=h9 ⟨k,by omega⟩;have h2:=cSd (S_ ⟨k,by omega⟩) h7;have h3:=cL (inter_subset_right (s₁:=S_ ⟨k,by omega⟩) (s₂:=h7));have h4:(k+1)*D<=m*D:=nMr D hk;rw[Nat.add_mul,one_mul] at h4;omega
  obtain ⟨Ak,h0,h5⟩:=exists_subset_card_eq j3;let A':Fin (k+1)->FS V:=Fin.snoc A Ak;refine ⟨A',?_,?_,?_⟩
  .
   intro i;refine lastCases ?_ ?_ i
   . simp only[A',snoc_last];intro v hv;obtain ⟨h1,h2⟩:=pS (h0 hv);exact rS ⟨h1,λ hf=>h2 (mUl _ hf)⟩
   . intro j;simp only[A',snoc_castSucc];exact j0 j
  .
   intro i;refine lastCases ?_ ?_ i
   . simp [A',h5]
   . intro j;simp [A',h6 j]
  .
   intro i1 i2 hne;revert hne;refine lastCases ?_ ?_ i1 <;> refine lastCases ?_ ?_ i2
   . intro h;exact absurd rfl h
   .
    intro j _;simp only[A',snoc_last,snoc_castSucc]
    exact rD λ v hv1 hv2 =>
     (pS (h0 hv1)).2 (mUr _ (mB.mpr ⟨j,mUv j,hv2⟩))
   .
    intro j _;simp only[A',snoc_last,snoc_castSucc]
    exact dR.mpr λ v hv1 hv2 =>
     (pS (h0 hv1)).2 (mUr _ (mB.mpr ⟨j,mUv j,hv2⟩))
   . intro j1 j2 hne';simp only[A',snoc_castSucc];exact h8 _ _ (by intro h;apply hne';rw[h])
lemma q10 {V:Type*} {H:SG V} {S Forb X:FS V} {s D m5:ℕ} {r':ℕ} (st:Fin r'->V) (Exp:Fin r'->FS V) (hst:∀ a,st a∈X) (j0:∀ x∈X,#(univ.filter (λ a=>st a=x))=s) (j3:∀ a,q0z H S (st a) D m5 (Exp a)) (h8:∀ a,Disjoint (Exp a \ {st a}) Forb) (h2:∀ a b,a≠b->Disjoint (Exp a \ {st a}) (Exp b \ {st b})) : ∃ F:V->Fin s->FS V, (∀ x∈X,∀ j:Fin s,q0z H S x D m5 (F x j)) /\ (∀ x∈X,∀ j:Fin s,Disjoint (F x j \ {x}) Forb) /\ (∀ x1∈X,∀ j1:Fin s,∀ x2∈X,∀ j2:Fin s, (x1,j1)≠(x2,j2)->Disjoint (F x1 j1 \ {x1}) (F x2 j2 \ {x2})):=by
 let h4:(x:V)->x∈X->Fin s ≃ {a:Fin r' // a∈univ.filter (λ a=>st a=x)} :=
  λ x hx=>(Fintype.equivFinOfCardEq (by simp only[Fintype.card_coe];exact j0 x hx)).symm
 let F:V->Fin s->FS V:=λ x j =>
  if hx:x∈X then Exp (h4 x hx j).1 else ∅
 have h0:∀ x (hx:x∈X) (j:Fin s),st (h4 x hx j).1=x:=λ x hx j =>
  (pF (h4 x hx j).2).2
 refine ⟨F,?_,?_,?_⟩
 .
  intro x hx j;dsimp only[F];rw[dif_pos hx]
  have:=j3 (h4 x hx j).1;rwa [h0 x hx j] at this
 .
  intro x hx j;dsimp only[F];rw[dif_pos hx]
  have:=h8 (h4 x hx j).1;rwa [h0 x hx j] at this
 .
  intro x1 h6 j1 x2 h9 j2 hne;dsimp only[F];rw[dif_pos h6,dif_pos h9]
  have h3:(h4 x1 h6 j1).1≠(h4 x2 h9 j2).1:=by
   intro j4;have h5:x1=x2:=(h0 x1 h6 j1).symm.trans (j4 ▸ h0 x2 h9 j2);subst h5;have h7:j1=j2:=(h4 x1 h6).injective (Subtype.ext j4);exact hne (by rw[h7])
  have h1:=h2 _ _ h3
  rwa [h0 x1 h6 j1,h0 x2 h9 j2] at h1
lemma q11 {V:Type*} {H:SG V} {S F:FS V} {v u:V} {D m:ℕ} (h:q0z H S v D m F) (hu:u∈F) : F⊆qs H F (2*m) {u}:=by intro w hw;obtain ⟨p1,_,hp1⟩:=q0C h hu;obtain ⟨p2,_,hp2⟩:=q0C h hw;have h0:=qA (mSs u) hu (p1.reverse.append p2);rw[wLa,wLr] at h0;exact qu H F (by omega) {u} h0
lemma q12 {e1 e2:O} {d n:ℕ} {x:O} (h5:0 < e1) (h4:0 < e2) (h3:15/e2<=(d:O)) (hn:100<=n) (hx_lb:e2*(d:O)/2<=x) (hx_ub:x<=(n:O)) : e1/(log (n:O))^2<=qK e1 (e2*(d:O)) x:=by
 have hd_pos:(0:O) < (d:O):=lL2 (by positivity) h3
 have h15:15<=e2*(d:O):=by rw[dLi h4] at h3;linarith
 have hlogn:0 < log (n:O):=lPs (by exact_mod_cast (show 1 < n by omega))
 have h1:1 < 15*x/(e2*(d:O)):=by
  rw[one_lt_div (by positivity)];linarith
 have h0:0 < log (15*x/(e2*(d:O))):=lPs h1;rw[qL (by linarith [show 0 < e2*(d:O) by positivity])];apply dLl h5.le (pow_pos h0 2)
 have h2:15*x/(e2*(d:O))<=(n:O):=by
  rw[dLi (by positivity)];nlinarith
 exact pLl h0.le (lLl (by linarith) h2) 2
lemma q13 {V:Type*} {G:SG V} {x y:V} (q:G.Walk x y) (T:FS V) (hy:y∈T) : ∃ (e0:V) (_:e0∈T) (p:G.Walk x e0), p.IsPath/\p.length<=q.length/\(∀ w∈p.support,w∈q.support) /\ (∀ w∈p.support,w∈T->w=e0):=by
 let qp:=q.bypass;have h4:qp.IsPath:=q.bypass_isPath;have hqp_len:qp.length<=q.length:=length_bypass_le_length q;have h5:∀ w∈qp.support,w∈q.support:=λ w hw=>Walk.support_bypass_subset q hw
 have j0:∃ i,∃ hi:i < qp.support.length,qp.support[i]∈T:=by
  obtain ⟨i,hi,heq⟩:=getElem_of_mem (wEm qp);exact ⟨i,hi,by rw[heq];exact hy⟩
 let i0:=find j0;obtain ⟨hi0,j1⟩:=find_spec j0;let e0:=qp.support[i0];have h0:e0∈qp.support:=getElem_mem hi0;let p:=qp.takeUntil e0 h0
 refine ⟨e0,j1,p,h4.takeUntil h0,?_,
  λ w hw=>h5 w (support_takeUntil_subset_support qp h0 hw),?_⟩
 .
  have hadd:p.length+(qp.dropUntil e0 h0).length=qp.length:=by
   rw[<- wLa,take_spec qp h0]
  omega
 .
  intro w hwp hwT;by_contra hne;let L1:=p.support;let L2:=(qp.dropUntil e0 h0).support.tail
  have h3:L1 ++ L2=qp.support:=by
   dsimp only[L1,L2,p];rw[<- support_append,take_spec qp h0]
  have hlen_eq:L1.length+L2.length=qp.support.length:=by
   rw[<- List.length_append,h3]
  have hL1pos:0 < L1.length:=length_pos_of_ne_nil (wSn _)
  have hL1_lt:L1.length - 1 < qp.support.length:=by omega
  have h6:qp.support[L1.length - 1]'hL1_lt=e0:=by
   have h1:(L1 ++ L2)[L1.length - 1]'(by rw[h3];exact hL1_lt)=L1[L1.length - 1]'(by omega) :=
    getElem_append_left (by omega)
   have h2:L1[L1.length - 1]'(by omega)=e0:=by
    dsimp only[L1];rw[<- getLast_eq_getElem (wSn _)];exact wGl _
   exact (show qp.support[L1.length - 1]'hL1_lt=(L1 ++ L2)[L1.length - 1]'(by rw[h3];exact hL1_lt) by
    congr 1;exact h3.symm).trans (h1.trans h2)
  have hi0_eq:i0=L1.length - 1 :=
   (List.Nodup.getElem_inj_iff h4.support_nodup).mp h6.symm
  obtain ⟨j,hj,j2⟩:=getElem_of_mem hwp;have hj':j < L1.length:=hj
  have hj_lt_last:j < L1.length - 1:=by
   by_contra hge
   have h9:j=L1.length - 1:=by omega
   have h8:L1[L1.length - 1]'(by omega)=e0:=by
    dsimp only[L1];rw[<- getLast_eq_getElem (wSn _)];exact wGl _
   exact hne (j2.symm.trans (by subst h9;exact h8))
  have hj_lt:j < qp.support.length:=by omega
  have h7:qp.support[j]'hj_lt=w:=by
   have h1:(L1 ++ L2)[j]'(by rw[h3];exact hj_lt)=L1[j]'hj':=getElem_append_left hj'
   exact (show qp.support[j]'hj_lt=(L1 ++ L2)[j]'(by rw[h3];exact hj_lt) by
    congr 1;exact h3.symm).trans (h1.trans j2)
  exact Nat.find_min j0 (show j < i0 by omega) ⟨hj_lt,by rw[h7];exact hwT⟩
lemma q14 {V:Type*} {S A B:FS V} (hAS:A⊆S) (hBS:B⊆S) (hA:#S < 2*#A) (hB:#S < 2*#B) : (A∩B).Nonempty:=by by_contra h0;rw[not_nonempty_iff_eq_empty] at h0;have h1:=Finset.card_union_add_card_inter A B;rw[h0,card_empty,add_zero] at h1;have h2:#(A∪B)<=#S:=cL (uS hAS hBS);omega
lemma q15 {V:Type*} {e1 e2:O} {t s K:ℕ}
  (he10:0 < e1) (he20:0 < e2) (he21:e2 < 1)
  (ht:1<=t) (hs:1<=s)
  (H:SG V) (S X Vset:FS V) (d r':ℕ) (x0:V) (c:(q3 H S).Walk x0 x0)
  (hd100:100<=d) (hdn:d<=#S)
  (jw:∀ v∈S,d - 1<=dS H S v)
  (w3:q0G H S x0 c) (km:X⊆S) (hXt:#X<=t)
  (j6:r'<=t*s) (h9:#Vset=r')
  (eV:Fin r' ≃ Vset)
  (hlc:∀ A Xa Ya Z:FS V,
   A⊆S->Xa⊆S \ A->Ya⊆S \ A->Z⊆S \ A ->
   e2*(d:O)/2<=(#A:O) ->
   (#Xa:O)<=(#A:O)*qK e1 (e2*(d:O)) (#A:O)/4 ->
   Disjoint (qs H (S \ (Xa∪Z)) (floor ((log (log (#S:O)))^5)) A) Ya ->
   (#Ya:O)<=(18/e1*(log (#S:O))^3)^(300*max (2*(10*(t*s)+10)) (K+10)) ->
   q07 H S A Ya Z (max (2*(10*(t*s)+10)) (K+10)) ->
   (18/e1*(log (#S:O))^3)^(400*max (2*(10*(t*s)+10)) (K+10)) <
    (#(qs H (S \ (Xa∪Ya∪Z)) (floor ((log (log (#S:O)))^5)) A):O) /\
   #S < 2*#(qs H (S \ (Xa∪Ya∪Z)) (floor (18/e1*(log (#S:O))^3)) A))
  (hnc:∀ A B W:FS V,∀ x:O,
   A⊆S->B⊆S->W⊆S \ (A∪B) ->
   1<=x->x<=(#A:O)->x<=(#B:O) ->
   (#W:O)*(log (#S:O))^3<=10*x ->
   ∃ (a:V) (b:V) (_:a∈A) (_:b∈B) (p:(q3 H (S \ W)).Walk a b),
    p.IsPath/\(p.length:O)<=40/e1*(log (#S:O))^3 /\
    (∀ w∈p.support,w∈A->w=a)/\(∀ w∈p.support,w∈B->w=b))
  (jq:c.support.toFinset⊆S)
  (hC_card:c.support.toFinset.card<=ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2))
  (hd_big:10*(t*s)+10+1<=d/2)
  (hmlc_m:floor (18/e1*(log (#S:O))^3)+floor (40/e1*(log (#S:O))^3)+2 <=
   3*floor (40/e1*(log (#S:O))^3))
  (k9:2*(3*(t*s)+t+(t*s)*(3*floor (40/e1*(log (#S:O))^3)+1) +
    ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2)) <=
   (ceil ((log (#S:O))^K))^2)
  (kp:((3*(t*s)+t+(t*s)*(3*floor (40/e1*(log (#S:O))^3)+1) +
    ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2):ℕ):O)*(log (#S:O))^3 <=
   10*((((ceil ((log (#S:O))^K))^2 -
    (3*(t*s)+t+(t*s)*(3*floor (40/e1*(log (#S:O))^3)+1) +
    ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2)):ℕ):O)))
  (j9:2*(ceil ((log (#S:O))^K))^2 < #S)
  (h7:∀ j:Fin r',(eV j).1∈S.filter (λ v=>(ceil ((log (#S:O))^K))^2<=dS H S v))
  (jk:∀ j:Fin r',(eV j).1 ∉ c.support.toFinset)
  (j5:∀ j:Fin r',(eV j).1 ∉ X)
  (q:ℕ) (hq:q < r') (st:Fin q->V) (tg:Fin q->Fin r') (en:Fin q->V)
  (p:∀ a:Fin q,(q3 H S).Walk (st a) (en a))
  (hst:∀ a,st a∈X) (ju:∀ a,(p a).IsPath/\(p a).length<=3*floor (40/e1*(log (#S:O))^3))
  (kk:∀ a,∀ w∈(p a).support,w∈c.support.toFinset∪X->w=st a)
  (w1:∀ a,∀ j:Fin r',∀ w∈(p a).support,w∈({(eV j).1}:FS V)->j=tg a/\w=en a)
  (x:V) (kd:x∈X) (j0:Fin r') (hj0:∀ a,tg a≠j0) :
  let U:FS V:=((S \ S)∪X∪(univ.biUnion (λ a=>(p a).support.toFinset))∪c.support.toFinset) \ {x}
  let V_tg:FS V:=univ.biUnion (λ j:Fin r'=>({(eV j).1}:FS V))
  (∀ a,∀ l:ℕ,1<=l ->
   #(qn H S (qs H (S \ (V_tg∪U)) (l - 1) {x})∩(p a).support.toFinset)<=l+1) ->
  ∃ (e0:V) (_:e0∈({(eV j0).1}:FS V)) (p0:(q3 H S).Walk x e0),
   p0.IsPath/\p0.length<=3*floor (40/e1*(log (#S:O))^3) /\
   (∀ w∈p0.support,w∈c.support.toFinset∪X->w=x) /\
   (∀ j:Fin r',∀ w∈p0.support,w∈({(eV j).1}:FS V)->j=j0/\w=e0) /\
   (∀ a,∀ w∈p0.support,w∈(p a).support->w=x/\w=st a):=by
 intro U V_tg kl;let r:=t*s;let k1:=max (2*(10*r+10)) (K+10);set n:O:=(#S:O);set m:=floor (40/e1*(log n)^3);set js:=floor (18/e1*(log n)^3);set kq:=ceil ((log n)^K);set D_:=kq^2;set C:=c.support.toFinset;set w7:=ceil (2*log n/log ((d - 1 - 1:ℕ):O)+2);set h0:=3*r+t+r*(3*m+1)+w7;let v:Fin r'->V:=λ j=>(eV j).1
 have k5:Injective v:=λ j1 j2 h=>eV.injective (Subtype.ext h)
 have h5:V_tg=Vset:=by
  ext z;simp only[V_tg,mB,mUv,true_and,mSg]
  exact ⟨λ⟨j,hj⟩=>hj ▸ (eV j).2,λ hz=>⟨eV.symm ⟨z,hz⟩,by simp⟩⟩
 let W:=V_tg∪U
 have j8:W⊆S:=by
  refine uS (h5 ▸ λ z hz=>by simpa using (pF (h7 (eV.symm ⟨z,hz⟩))).1) ?_
  refine sS.trans (uS (uS (uS (by simp) km) ?_) jq)
  exact biUnion_subset.mpr λ a _ z hz =>
   q0w (p a) (km (hst a)) z (pTf hz)
 have j4:x ∉ W:=by
  intro hxW;rcases pU hxW with wb | hxu
  . rw[h5] at wb;exact j5 (eV.symm ⟨x,wb⟩) (by simpa using kd)
  . exact (pS hxu).2 (mSs x)
 have jx:#W<=h0:=by
  have jy:#(univ.biUnion (λ a:Fin q=>(p a).support.toFinset))<=r*(3*m+1):=by
   calc
    _<=∑ a:Fin q,(p a).support.toFinset.card:=cBu
    _<=∑ _a:Fin q,(3*m+1):=sum_le_sum λ a _ =>
      (q0y (p a)).trans (Nat.add_le_add_right (ju a).2 1)
    _=q*(3*m+1):=by simp
    _<=r*(3*m+1):=nMr _ (by omega)
  have hU_le:#U<=#X+r*(3*m+1)+#C:=by
   have jl:U⊆X∪univ.biUnion (λ a=>(p a).support.toFinset)∪C:=by
    dsimp only[U];rw[Finset.sdiff_self,empty_union];exact sS
   exact (cL jl).trans ((cUl _ _).trans
    (Nat.add_le_add_right ((cUl _ _).trans (Nat.add_le_add_left jy _)) _))
  have ko:#V_tg<=r:=by rw[h5,h9];exact j6
  calc
   #W<=#V_tg+#U:=cUl _ _
   _<=h0:=by dsimp only[h0];omega
 have k2:q07 H S {x} ∅ W (10*r+10):=by
  intro l wg;simp only[empty_union]
  have jl:qn H S (qs H (S \ W) (l - 1) {x})∩W ⊆
    V_tg∪X∪(univ.biUnion (λ a:Fin q =>
     qn H S (qs H (S \ W) (l - 1) {x})∩(p a).support.toFinset)) ∪
    (qs H S l {x}∩C):=by
   intro z hz;obtain ⟨w9,kt⟩:=pI hz
   rcases pU kt with hzV | hzU
   . exact mUl _ (mUl _ (mUl _ hzV))
   .
    have kc:=(pS hzU).1;rw[Finset.sdiff_self,empty_union] at kc
    rcases pU kc with h1' | hzC
    .
     rcases pU h1' with hzX | hzP
     . exact mUl _ (mUl _ (mUr _ hzX))
     .
      obtain ⟨a,_,ks⟩:=mB.mp hzP
      exact mUl _ (mUr _
       (mB.mpr ⟨a,mUv a,rI ⟨w9,ks⟩⟩))
    .
     refine mUr _ (rI ⟨?_,hzC⟩);obtain ⟨kr,_,u,huB,huz⟩:=(qo H S _ z).mp w9;have w0:=qw H sS (l - 1) {x} huB
     have kb:z∈qs H S ((l - 1)+1) {x}:=by
      by_cases w8:z∈qs H S (l - 1) {x}
      . exact mUl _ w8
      . exact mUr _ ((qo H S _ z).mpr ⟨kr,w8,u,w0,huz⟩)
     rwa [Nat.sub_add_cancel wg] at kb
  have hPsum:(univ.biUnion (λ a:Fin q =>
    qn H S (qs H (S \ W) (l - 1) {x})∩(p a).support.toFinset)).card<=r*(l+1):=by
   calc
    _<=∑ a:Fin q,#(qn H S (qs H (S \ W) (l - 1) {x})∩(p a).support.toFinset) :=
      cBu
    _<=∑ _a:Fin q,(l+1):=sum_le_sum λ a _=>kl a l wg
    _=q*(l+1):=by simp
    _<=r*(l+1):=nMr _ (by omega)
  have hC_bd:=q0P w3 x l;have h1:=cL jl
  have h2:=cUl (V_tg∪X∪univ.biUnion (λ a:Fin q =>
    qn H S (qs H (S \ W) (l - 1) {x})∩(p a).support.toFinset)) (qs H S l {x}∩C)
  have h3:=cUl (V_tg∪X) (univ.biUnion (λ a:Fin q =>
    qn H S (qs H (S \ W) (l - 1) {x})∩(p a).support.toFinset))
  have h4:=cUl V_tg X
  have ko:#V_tg<=r:=by rw[h5,h9];exact j6
  have ht_le_r:t<=r:=Nat.le_mul_of_pos_right t hs;nlinarith
 let Ax:=qs H (S \ W) 1 {x};have jd:Ax⊆S \ W:=qt H (S \ W) 1 {x}
 have jr:e2*(d:O)/2<=(#Ax:O):=by
  have jl:(S.filter (H.Adj x)) \ (qn H S (qs H (S \ W) 0 {x})∩W)⊆Ax:=by
   intro z hz;obtain ⟨ku,ka⟩:=pS hz;obtain ⟨kr,kv⟩:=pF ku
   have wc:x∈qs H (S \ W) 0 {x} :=
    rI ⟨mSs x,rS ⟨km kd,j4⟩⟩
   have ji:z ∉ W:=by
    intro kt
    have k3:z ∉ qs H (S \ W) 0 {x}:=λ h =>
     (H.ne_of_adj kv).symm (pSg (pI h).1)
    exact ka (rI ⟨(qo H S _ z).mpr ⟨kr,k3,x,wc,kv⟩,kt⟩)
   by_cases wa:z∈qs H (S \ W) 0 {x}
   . exact mUl _ wa
   .
    exact mUr _ ((qo H (S \ W) _ z).mpr
     ⟨rS ⟨kr,ji⟩,wa,x,wc,kv⟩)
  have hW1:#(qn H S (qs H (S \ W) 0 {x})∩W)<=10*r+10:=by
   simpa using k2 1 le_rfl
  have w2:=jw x (km kd);have hsdiff:=cSd (S.filter (H.Adj x)) (qn H S (qs H (S \ W) 0 {x})∩W);have hinter:=cL (inter_subset_right (s₁:=S.filter (H.Adj x)) (s₂:=qn H S (qs H (S \ W) 0 {x})∩W))
  have jg:d<=2*#Ax:=by
   have:=cL jl;unfold dS at w2;omega
  have hR:(d:O)<=2*(#Ax:O):=by exact_mod_cast jg
  nlinarith [show (0:O)<=(d:O) by positivity]
 have k7:q07 H S Ax ∅ W k1:=by
  intro i hi1;simp only[empty_union]
  have w4:qs H (S \ W) (i - 1) Ax=qs H (S \ W) i {x}:=by
   dsimp only[Ax];rw[<- qy,show 1+(i - 1)=i by omega]
  rw[w4];have h1:=k2 (i+1) (by omega);simp only[empty_union,Nat.add_sub_cancel] at h1;have hk_ge:2*(10*r+10)<=k1:=lMl _ _;nlinarith
 have ja:W⊆S \ Ax:=λ z hz =>
  rS ⟨j8 hz,λ ks=>(pS (jd ks)).2 hz⟩
 have jz:#S < 2*#(qs H (S \ W) (js+1) {x}):=by
  have h:=(hlc Ax ∅ ∅ W (jd.trans sS) (by simp) (by simp) ja jr
   (by simp;exact div_nonneg (mul_nonneg (nCn _) (by
    unfold qK;split_ifs <;> positivity)) (by norm_num))
   (by simp) (by simp;positivity) k7).2
  simpa only[empty_union,Ax,<- qy,add_comm 1 js] using h
 let Bx:=qs H (S \ W) (js+1) {x};let vj:=v j0;let Nv:=(S.filter (H.Adj vj)) \ W;have jc:Bx⊆S \ W:=qt H (S \ W) (js+1) {x}
 have h6:Nv⊆S \ W:=λ z hz =>
  rS ⟨(pF (pS hz).1).1,(pS hz).2⟩
 have j7:W⊆S \ (Bx∪Nv):=λ z hz=>rS ⟨j8 hz,λ h=>by
  rcases pU h with h1 | h2
  . exact (pS (jc h1)).2 hz
  . exact (pS (h6 h2)).2 hz⟩
 have jp:D_ - h0<=#Nv:=by
  have hdv:D_<=#(S.filter (H.Adj vj)):=(pF (h7 j0)).2;have h1:=cSd (S.filter (H.Adj vj)) W;have h2:=cL (inter_subset_right (s₁:=S.filter (H.Adj vj)) (s₂:=W));dsimp only[Nv];omega
 have jh:D_ - h0<=#Bx:=by
  have hBx_big':#S < 2*#Bx:=jz;have hD__half:2*D_ < #S:=j9;omega
 have k0:(1:O)<=((D_ - h0:ℕ):O):=by
  have h2U:2*h0<=D_:=k9
  have:1<=h0:=by dsimp only[h0];have:1<=r:=Nat.mul_pos ht hs;omega
  exact_mod_cast (show 1<=D_ - h0 by omega)
 have kn:(#W:O)*(log n)^3<=10*((D_ - h0:ℕ):O):=by
  have h1:(#W:O)<=(h0:O):=by exact_mod_cast jx
  have h2:=mlR h1 (show (0:O)<=(log n)^3 by
   exact pow_nonneg (lNn (by dsimp only[n];exact_mod_cast (show 1<=#S by omega))) 3)
  exact h2.trans kp
 obtain ⟨a,b,w5,k8,je,jt,k6,kj,_⟩ :=
  hnc Bx Nv W ((D_ - h0:ℕ):O) (jc.trans sS)
   (h6.trans sS) j7 k0
   (by exact_mod_cast jh) (by exact_mod_cast jp) kn
 obtain ⟨a0,ha0,q1,jn,hq1_len,jm⟩:=qB w5;have w6:a0=x:=pSg (pI ha0).1;subst w6
 have jf:(q1.append je).IsPath :=
  q0x q1 je jn jt (λ z ku hz2=>kj z hz2 (jm z ku))
 have h8:∀ w∈(q1.append je).support,w∈S \ W:=λ w hw =>
  q0w (q1.append je) (rS ⟨km kd,j4⟩) w hw
 have ki:vj∈S:=(pF (h7 j0)).1;have kh:vj∈W:=mUl _ (mB.mpr ⟨j0,mUv j0,mSs vj⟩)
 have jb:(q3 H S).Adj b vj :=
  ⟨(pF (pS k8).1).2.symm,(pS (h6 k8)).1,ki⟩
 let p0:(q3 H S).Walk a0 vj :=
  (q0r (q1.append je) (λ w hw=>(pS (h8 w hw)).1)).append (Walk.cons jb .nil)
 have jo:p0.IsPath:=by
  apply q0x _ _ (q0v _ _ jf)
   (Walk.IsPath.cons Walk.IsPath.nil (by simp [H.ne_of_adj jb.1]))
  intro w wf we;rw[q0s] at wf;simp only[support_cons,support_nil,List.mem_cons,List.not_mem_nil,or_false] at we
  rcases we with rfl | rfl
  . rfl
  . exact absurd kh (pS (h8 vj wf)).2
 have jv:p0.length<=3*m:=by
  have hql:je.length<=m:=nLf k6;dsimp only[p0];rw[wLa,q0t,wLa];simp only[length_cons,length_nil];omega
 have j3:∀ w∈p0.support,w∈S \ W\/w=vj:=by
  intro w hw;dsimp only[p0] at hw;rw[wSa,q0s] at hw
  rcases hw with h1 | h2
  . exact Or.inl (h8 w h1)
  .
   simp only[support_cons,support_nil,List.mem_cons,List.not_mem_nil,or_false] at h2
   rcases h2 with rfl | rfl
   . exact Or.inl (h6 k8)
   . exact Or.inr rfl
 refine ⟨vj,mSs vj,p0,jo,jv,?_,?_,?_⟩
 .
  intro w kf kg
  rcases j3 w kf with jj | rfl
  .
   by_contra kw
   have ky:w∈U:=rS ⟨by
    rcases pU kg with kz | kx
    . exact mUr _ kz
    . exact mUl _ (mUl _ (mUr _ kx)),
    λ h=>kw (pSg h)⟩
   exact (pS jj).2 (mUr _ ky)
  .
   rcases pU kg with kz | kx
   . exact absurd kz (jk j0)
   . exact absurd kx (j5 j0)
 .
  intro j w kf wd;have hwv:w=v j:=pSg wd
  rcases j3 w kf with jj | ke
  .
   exfalso
   exact (pS jj).2 (mUl _
    (mB.mpr ⟨j,mUv j,wd⟩))
  . exact ⟨k5 (hwv.symm.trans ke),ke⟩
 .
  intro a w kf k4
  rcases j3 w kf with jj | rfl
  .
   have kw:w=a0:=by
    by_contra hne
    have ky:w∈U:=rS
     ⟨mUl _ (mUr _
      (mB.mpr ⟨a,mUv a,rT k4⟩)),
     λ h=>hne (pSg h)⟩
    exact (pS jj).2 (mUr _ ky)
   subst kw;exact ⟨rfl,kk a w k4 (mUr _ kd)⟩
  .
   exfalso
   have:=(w1 a j0 vj k4 (mSs vj)).1
   exact hj0 a this.symm
lemma q16 {V:Type*} {e1 e2:O} {t s K:ℕ}
  (kk:0 < e1) (kj:0 < e2) (ki:e2 < 1)
  (ht:1<=t) (hs:1<=s)
  (H:SG V) (S X:FS V) (d D:ℕ) (x0:V) (c:(q3 H S).Walk x0 x0)
  (k6:100<=d) (hdn:d<=#S)
  (hexp:qQ H S e1 (e2*(d:O))) (ji:∀ v∈S,d - 1<=dS H S v)
  (kl:q0G H S x0 c) (kd:X⊆S) (ks:#X<=t)
  (hD1:1<=D)
  (hlc:∀ A Xa Ya Z:FS V,
   A⊆S->Xa⊆S \ A->Ya⊆S \ A->Z⊆S \ A ->
   e2*(d:O)/2<=(#A:O) ->
   (#Xa:O)<=(#A:O)*qK e1 (e2*(d:O)) (#A:O)/4 ->
   Disjoint (qs H (S \ (Xa∪Z)) (floor ((log (log (#S:O)))^5)) A) Ya ->
   (#Ya:O)<=(18/e1*(log (#S:O))^3)^(300*max (2*(10*(t*s)+10)) (K+10)) ->
   q07 H S A Ya Z (max (2*(10*(t*s)+10)) (K+10)) ->
   (18/e1*(log (#S:O))^3)^(400*max (2*(10*(t*s)+10)) (K+10)) <
    (#(qs H (S \ (Xa∪Ya∪Z)) (floor ((log (log (#S:O)))^5)) A):O) /\
   #S < 2*#(qs H (S \ (Xa∪Ya∪Z)) (floor (18/e1*(log (#S:O))^3)) A))
  (hnc:∀ A B W:FS V,∀ x:O,
   A⊆S->B⊆S->W⊆S \ (A∪B) ->
   1<=x->x<=(#A:O)->x<=(#B:O) ->
   (#W:O)*(log (#S:O))^3<=10*x ->
   ∃ (a:V) (b:V) (_:a∈A) (_:b∈B) (p:(q3 H (S \ W)).Walk a b),
    p.IsPath/\(p.length:O)<=40/e1*(log (#S:O))^3 /\
    (∀ w∈p.support,w∈A->w=a)/\(∀ w∈p.support,w∈B->w=b))
  (jg:c.support.toFinset⊆S)
  (jb:c.support.toFinset.card<=ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2))
  (ja:D<=ceil ((log (#S:O))^K))
  (js:10*(t*s)+10+1<=d/2)
  (jp:floor (18/e1*(log (#S:O))^3)+floor (40/e1*(log (#S:O))^3)+2 <=
   3*floor (40/e1*(log (#S:O))^3))
  (jw:2*(3*(t*s)+t+(t*s)*(3*floor (40/e1*(log (#S:O))^3)+1) +
    ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2)) <=
   (ceil ((log (#S:O))^K))^2)
  (k8:((3*(t*s)+t+(t*s)*(3*floor (40/e1*(log (#S:O))^3)+1) +
    ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2):ℕ):O)*(log (#S:O))^3 <=
   10*((((ceil ((log (#S:O))^K))^2 -
    (3*(t*s)+t+(t*s)*(3*floor (40/e1*(log (#S:O))^3)+1) +
    ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2)):ℕ):O)))
  (kn:(3*(t*s)+t+(t*s)*(3*floor (40/e1*(log (#S:O))^3)+1) +
    ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2)) +
    2*(t*s)*ceil ((log (#S:O))^K) <=
   (ceil ((log (#S:O))^K))^2)
  (j8:2*(ceil ((log (#S:O))^K))^2 < #S)
  (jt:2*(t*s)<=#(S.filter (λ v=>(ceil ((log (#S:O))^K))^2<=dS H S v) \ c.support.toFinset)) :
  let m:=floor (40/e1*(log (#S:O))^3)
  ∃ F:V->Fin s->FS V,
   (∀ x∈X,∀ j:Fin s,q0z H S x D (5*m) (F x j)) /\
   (∀ x∈X,∀ j:Fin s,Disjoint (F x j \ {x}) (c.support.toFinset∪X)) /\
   (∀ x1∈X,∀ j1:Fin s,∀ x2∈X,∀ j2:Fin s,
    (x1,j1)≠(x2,j2)->Disjoint (F x1 j1 \ {x1}) (F x2 j2 \ {x2})):=by
 let r:=t*s;set n:O:=(#S:O);set m:=floor (40/e1*(log n)^3);set j6:=ceil ((log n)^K);set D_:=j6^2;set C:=c.support.toFinset;set kb:=ceil (2*log n/log ((d - 1 - 1:ℕ):O)+2);set jx:=3*r+t+r*(3*m+1)+kb;let L:=S.filter (λ v=>D_<=dS H S v)
 obtain ⟨Vall,j5,hVall_card⟩:=exists_subset_card_eq jt;let r':=#X*s;have h8:r'<=r:=nMr s ks;have ht_le_r:t<=r:=Nat.le_mul_of_pos_right t hs
 have k7:r'<=#(Vall \ X):=by
  have h1:=cSd Vall X;have h2:=cL (inter_subset_right (s₁:=Vall) (s₂:=X));omega
 obtain ⟨Vset,h0,h9⟩:=exists_subset_card_eq k7;let eV:Fin r' ≃ Vset:=(Fintype.equivFinOfCardEq (by simp [h9])).symm;let v:Fin r'->V:=λ j=>(eV j).1
 let T:Fin r'->FS V:=λ j=>{v j}
 have h7:∀ j,v j∈L:=λ j =>
  (pS (j5 (pS (h0 (eV j).2)).1)).1
 have h6:∀ j,v j ∉ C:=λ j =>
  (pS (j5 (pS (h0 (eV j).2)).1)).2
 have h5:∀ j,v j ∉ X:=λ j=>(pS (h0 (eV j).2)).2
 have jo:Injective v:=λ j1 j2 h=>eV.injective (Subtype.ext h)
 obtain ⟨st,tg,en,p,k3,kq,htg_inj,h4,je,k4,jh,km⟩ :=
  q0W H S S C X s r' T (3*m) sR kd rfl
   (λ j=>sSm (rS
    ⟨(pF (h7 j)).1,λ h=>by
     rcases pU h with hc' | hx';exact h6 j hc';exact h5 j hx'⟩))
   (λ j1 j2 hne=>Finset.disjoint_singleton.mpr (λ h=>hne (jo h)))
   (λ q hq st tg en p k3 _ _ h4 je k4 _ _ x hxX _ j0 hj0 =>
    q15 kk kj ki ht hs H S X Vset d r' x0 c k6 hdn ji kl kd ks
     h8 h9 eV hlc hnc jg jb js jp jw k8 j8
     h7 h6 h5 q hq st tg en p k3 h4 je k4 x hxX j0 hj0)
 let jy:=C∪X∪Vset∪univ.biUnion (λ a:Fin r'=>(p a).support.toFinset)
 have hForb_card:jy.card<=jx:=by
  have hP:#(univ.biUnion (λ a:Fin r'=>(p a).support.toFinset))<=r*(3*m+1):=by
   calc
    _<=∑ a:Fin r',(p a).support.toFinset.card:=cBu
    _<=∑ _a:Fin r',(3*m+1):=sum_le_sum λ a _ =>
      (q0y (p a)).trans (Nat.add_le_add_right (h4 a).2 1)
    _=r'*(3*m+1):=by simp
    _<=r*(3*m+1):=nMr _ h8
  have h1:=cUl (C∪X∪Vset) (univ.biUnion (λ a:Fin r'=>(p a).support.toFinset))
  have h2:=cUl (C∪X) Vset;have h3:=cUl C X;have hC_le:#C<=kb:=jb;dsimp only[jy,jx];omega
 obtain ⟨A,j9,jv,ju⟩ :=
  q0Z r' D (λ a=>S.filter (H.Adj (en a))) jy (λ a=>by
   have k5:en a=v (tg a):=pSg (kq a);have hdeg:D_<=#(S.filter (H.Adj (en a))):=k5 ▸ (pF (h7 (tg a))).2;have hmul:r'*D<=r*j6:=nMm h8 ja;have hmul2:r*j6<=2*r*j6:=nMr j6 (by omega);have hUrD':jx+2*r*j6<=D_:=kn
   omega)
 have jj:∀ a:Fin r',∃ E⊆(p a).support.toFinset∪({en a}∪A a),
   q0z H S (st a) D (5*m) E:=by
  intro a;let j3:={en a}∪A a
  have jf:j3⊆S:=uS
   (sSm (q0w (p a) (kd (k3 a)) (en a) (wEm _)))
   (λ z hz=>(pF (pS (j9 a hz)).1).1)
  have j7:j3⊆qs H j3 1 {en a}:=by
   intro z hz
   have jr:en a∈qs H j3 0 {en a} :=
    rI ⟨mSs _,mUl _ (mSs _)⟩
   rcases pU hz with h1 | h2
   . exact mUl _ (pSg h1 ▸ jr)
   .
    by_cases kc:z=en a
    . exact mUl _ (kc ▸ jr)
    .
     refine mUr _ ((qo H j3 _ z).mpr
      ⟨mUr _ h2,λ h=>kc (pSg (pI h).1),
       en a,jr,(pF (pS (j9 a h2)).1).2⟩)
  have jq:=q0F (p a) (kd (k3 a)) (h4 a).2 jf
   (mUl _ (mSs _)) j7
  have jl:D<=#((p a).support.toFinset∪j3):=by
   calc
    D=#(A a):=(jv a).symm
    _<=#((p a).support.toFinset∪j3):=cL
      (sUr.trans sUr)
  obtain ⟨E,k9,ka⟩:=q0E jq hD1 jl;exact ⟨E,k9,q0B ka (by omega)⟩
 choose Exp hExp_sub hExp_is using jj
 have jk:∀ a,Disjoint (Exp a \ {st a}) (C∪X):=by
  intro a;rw[dL];intro z hz jn;obtain ⟨hzE,ke⟩:=pS hz;have jz:z≠st a:=nSg.mp ke
  rcases pU (hExp_sub a hzE) with hzp | hzf
  . exact jz (je a z (pTf hzp) jn)
  .
   rcases pU hzf with kc | kh
   .
    have k0:z=v (tg a):=(pSg kc).trans (pSg (kq a))
    rcases pU jn with hC | hX
    . exact h6 (tg a) (k0 ▸ hC)
    . exact h5 (tg a) (k0 ▸ hX)
   . exact (pS (j9 a kh)).2 (mUl _ (mUl _ jn))
 have jc:∀ a b,a≠b->Disjoint (Exp a \ {st a}) (Exp b \ {st b}):=by
  intro a b kr;rw[dL];intro z kh hzb;obtain ⟨kg,k2⟩:=pS kh;obtain ⟨kf,k1⟩:=pS hzb;have jd:z≠st a:=nSg.mp k2;have jm:z≠st b:=nSg.mp k1
  have j4:∀ c,z∈(p c).support.toFinset∪({en c}∪A c)->z≠st c ->
    z∈(p c).support\/z∈A c:=λ c hzc _=>by
   rcases pU hzc with h1 | h2
   . exact Or.inl (pTf h1)
   .
    rcases pU h2 with h21 | h22
    . exact Or.inl ((pSg h21) ▸ wEm (p c))
    . exact Or.inr h22
  rcases j4 a (hExp_sub a kg) jd with kp | ku <;>
  rcases j4 b (hExp_sub b kf) jm with ko | kt
  . exact jd (jh a b kr z kp ko).1
  .
   exact (pS (j9 b kt)).2 (mUr _
    (mB.mpr ⟨a,mUv a,rT kp⟩))
  .
   exact (pS (j9 a ku)).2 (mUr _
    (mB.mpr ⟨b,mUv b,rT ko⟩))
  . exact pD (ju a b kr) ku kt
 exact q10 st Exp k3 km hExp_is jk jc
lemma q17 {V:Type*} {e1 e2:O} {t s K:ℕ}
  (z4:0 < e1) (z3:0 < e2) (wf:e2 < 1)
  (ht:1<=t) (hs:1<=s)
  (H:SG V) (S X L:FS V) (d r':ℕ) (x0:V) (c:(q3 H S).Walk x0 x0)
  (k8:L=S.filter (λ v=>(ceil ((log (#S:O))^K))^2<=dS H S v))
  (hd100:100<=d) (hdn:d<=#S)
  (jp:∀ v∈S,d - 1<=dS H S v)
  (z6:q0G H S x0 c) (wn:X⊆S) (ze:#X<=t)
  (k1:r'<=t*s)
  (zb:∀ A Xa Ya Z:FS V,
    A⊆S->Xa⊆S \ A->Ya⊆S \ A->Z⊆S \ A ->
    e2*(d:O)/2<=(#A:O) ->
    (#Xa:O)<=(#A:O)*qK e1 (e2*(d:O)) (#A:O)/4 ->
    Disjoint (qs H (S \ (Xa∪Z)) (floor ((log (log (#S:O)))^5)) A) Ya ->
    (#Ya:O)<=(18/e1*(log (#S:O))^3)^(300*max (2*(10*(t*s)+10)) (K+10)) ->
    q07 H S A Ya Z (max (2*(10*(t*s)+10)) (K+10)) ->
    (18/e1*(log (#S:O))^3)^(400*max (2*(10*(t*s)+10)) (K+10)) <
     (#(qs H (S \ (Xa∪Ya∪Z)) (floor ((log (log (#S:O)))^5)) A):O) /\
    #S < 2*#(qs H (S \ (Xa∪Ya∪Z)) (floor (18/e1*(log (#S:O))^3)) A))
  (k9:c.support.toFinset⊆S)
  (kh:c.support.toFinset.card<=ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2))
  (z9:15/e2<=(d:O))
  (hd_big:10*(t*s)+10+1<=d/2)
  (wi:2*floor (18/e1*(log (#S:O))^3)+2<=3*floor (40/e1*(log (#S:O))^3))
  (wh:((3*(t*s)+t+(t*s)*(3*floor (40/e1*(log (#S:O))^3)+1) +
     ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2):ℕ):O) <=
    (((ceil ((log (#S:O))^K))^2:ℕ):O)*(e1/(log (#S:O))^2)/4)
  (k0:(((t*s)*(ceil ((log (#S:O))^K))^2:ℕ):O) <=
    (18/e1*(log (#S:O))^3)^(300*max (2*(10*(t*s)+10)) (K+10)))
  (kx:#(L \ c.support.toFinset) < 2*(t*s))
  (w:Fin r'->V) (T:Fin r'->FS V)
  (kb:∀ j,w j∈S \ L)
  (w7:∀ j,Disjoint (qs H (S \ L) (5*(2*floor ((log (log (#S:O)))^5)+2)) {w j})
    ((X \ L)∪(c.support.toFinset \ L)))
  (jy:∀ j1 j2,j1≠j2 ->
    Disjoint (qs H (S \ L) (5*(2*floor ((log (log (#S:O)))^5)+2)) {w j1})
     (qs H (S \ L) (5*(2*floor ((log (log (#S:O)))^5)+2)) {w j2}))
  (jc:∀ j,T j⊆qs H ((S \ L) \ c.support.toFinset) (floor ((log (log (#S:O)))^5)+1) {w j})
  (j6:∀ j,q0z H ((S \ L) \ c.support.toFinset)
    (w j) ((ceil ((log (#S:O))^K))^2) (floor ((log (log (#S:O)))^5)+1) (T j))
  (q:ℕ) (hq:q < r') (st:Fin q->V) (tg:Fin q->Fin r') (en:Fin q->V)
  (p:∀ a:Fin q,(q3 H (S \ L)).Walk (st a) (en a))
  (hst:∀ a,st a∈X \ L)
  (kd:∀ a,(p a).IsPath/\(p a).length<=3*floor (40/e1*(log (#S:O))^3))
  (wa:∀ a,∀ u∈(p a).support,u∈c.support.toFinset∪(X \ L)->u=st a)
  (z1:∀ a,∀ j:Fin r',∀ u∈(p a).support,u∈T j->j=tg a/\u=en a)
  (x:V) (jl:x∈X \ L)
  (j0:Fin r') (hj0:∀ a,tg a≠j0) :
  let S':=S \ L
  let X':=X \ L
  let U:FS V:=((S \ S')∪X'∪(univ.biUnion (λ a=>(p a).support.toFinset))∪c.support.toFinset) \ {x}
  let V_tg:FS V:=univ.biUnion T
  (∀ a,∀ l:ℕ,1<=l ->
    #(qn H S (qs H (S \ (V_tg∪U)) (l - 1) {x})∩(p a).support.toFinset)<=l+1) ->
  ∃ (e0:V) (_:e0∈T j0) (p₀:(q3 H S').Walk x e0),
    p₀.IsPath/\p₀.length<=3*floor (40/e1*(log (#S:O))^3) /\
    (∀ u∈p₀.support,u∈c.support.toFinset∪X'->u=x) /\
    (∀ j:Fin r',∀ u∈p₀.support,u∈T j->j=j0/\u=e0) /\
    (∀ a,∀ u∈p₀.support,u∈(p a).support->u=x/\u=st a):=by
 intro S' X' U V_tg wd;let r:=t*s;let jf:=max (2*(10*r+10)) (K+10);let n:O:=(#S:O);let m:=floor (40/e1*(log n)^3);let je:=floor (18/e1*(log n)^3);let h7:=floor ((log (log n))^5);let l0:=2*h7+2;let wj:=ceil ((log n)^K);let D_:=wj^2;let C:=c.support.toFinset;let wk:=ceil (2*log n/log ((d - 1 - 1:ℕ):O)+2);let kk:=3*r+t+r*(3*m+1)+wk
 have k7:L⊆S:=by rw[k8];exact filter_subset _ _
 have kw:#(L \ C) < 2*r:=kx;have hC_le:#C<=wk:=kh;have ky:2*je+2<=3*m:=wi;have k5:(kk:O)<=(D_:O)*(e1/(log n)^2)/4:=wh;have j8:((r*D_:ℕ):O)<=(18/e1*(log n)^3)^(300*jf):=k0;have kc:t<=r:=Nat.le_mul_of_pos_right t hs;have h8:X'⊆S':=sSs wn sR
 have h9:∀ j,T j⊆qs H S' (5*l0) {w j}:=λ j =>
  (jc j).trans ((qw H sS (h7+1) {w j}).trans
    (qu H S' (by dsimp only[l0];omega) {w j}))
 have h5:S \ S'=L:=by
  ext z;simp only[S',mS];exact ⟨λ⟨_,h⟩=>by by_contra hn;exact h ⟨by assumption,hn⟩,λ h=>⟨k7 h,λ⟨_,hn⟩=>hn h⟩⟩
 have jx:x ∉ L:=(pS jl).2
 have k6:L⊆U:=λ z hz=>rS
  ⟨mUl _ (mUl _ (mUl _ (h5.symm ▸ hz))),
   λ h=>jx ((pSg h) ▸ hz)⟩
 have h6:S \ U⊆S':=λ z hz =>
  rS ⟨(pS hz).1,λ ko=>(pS hz).2 (k6 ko)⟩
 have jh:U⊆S:=sS.trans (uS (uS (uS
  sS (h8.trans sS))
  (biUnion_subset.mpr λ a _ z hz =>
    sS (q0w (p a) (h8 (hst a)) z (pTf hz))))
  k9)
 have kg:#U<=kk:=by
  have hP:#(univ.biUnion (λ a:Fin q=>(p a).support.toFinset))<=r*(3*m+1):=by
    calc
     _<=∑ a:Fin q,(p a).support.toFinset.card:=cBu
     _<=∑ _a:Fin q,(3*m+1):=sum_le_sum λ a _ =>
       (q0y (p a)).trans (Nat.add_le_add_right (kd a).2 1)
     _=q*(3*m+1):=by simp
     _<=r*(3*m+1):=nMr _ (by omega)
  have jz:U⊆(L \ C)∪X'∪univ.biUnion (λ a=>(p a).support.toFinset)∪C:=by
    intro z hz;have jv:=(pS hz).1;rw[h5] at jv
    rcases pU jv with h1 | w5
    .
     rcases pU h1 with h2 | w4
     .
      rcases pU h2 with ko | hzX
      .
       by_cases hC:z∈C
       . exact mUr _ hC
       . exact mUl _ (mUl _ (mUl _ (rS ⟨ko,hC⟩)))
      . exact mUl _ (mUl _ (mUr _ hzX))
     . exact mUl _ (mUr _ w4)
    . exact mUr _ w5
  have h1:=cL jz;have h2:=cUl ((L \ C)∪X'∪univ.biUnion (λ a=>(p a).support.toFinset)) C
  have h3:=cUl ((L \ C)∪X') (univ.biUnion (λ a=>(p a).support.toFinset))
  have h4:=cUl (L \ C) X';have z8:#X'<=t:=(cL sS).trans ze;dsimp only[kk];omega
 have j9:#V_tg<=r*D_:=by
  calc
    #V_tg<=∑ j:Fin r',#(T j):=cBu
    _=r'*D_:=by
      simp only[λ j=>(j6 j).2.2.1,sum_const,card_univ,Fintype.card_fin,smul_eq_mul];rfl
    _<=r*D_:=nMr D_ k1
 have j3:V_tg⊆S:=biUnion_subset.mpr λ j _ =>
  (j6 j).1.trans (sS.trans sS)
 have h0:Disjoint (qs H S' (h7+1) {x}) V_tg:=by
  rw[dL];intro z hzx wo;obtain ⟨j,_,wl⟩:=mB.mp wo;obtain ⟨a1,wg,p1,_,hp1,_⟩:=qB hzx;have kt:a1=x:=pSg (pI wg).1;subst kt;obtain ⟨a2,ha2,p2,_,hp2,_⟩:=qB (qw H sS _ _ (jc j wl));have z7:a2=w j:=pSg (pI ha2).1;subst z7
  have w6:a1∈qs H S' (5*l0) {w j}:=by
    have wc:=qA (mSs _) (kb j) (p2.append p1.reverse);rw[wLa,wLr] at wc;exact qu H S' (by dsimp only[l0,h7,n] at hp1 ⊢;omega) _ wc
  exact pD (w7 j) w6 (mUl _ jl)
 have j5:Disjoint (qs H S' h7 (T j0)) (V_tg \ T j0):=by
  rw[dL];intro z jv wr;obtain ⟨wo,jk⟩:=pS wr;obtain ⟨j,_,wl⟩:=mB.mp wo;have z2:j≠j0:=λ h=>jk (h ▸ wl)
  have ju:z∈qs H S' (5*l0) {w j0}:=by
    have h1:=qv H S' h7 (λ u hu=>qw H sS _ _ (jc j0 hu)) jv
    rw[<- qy] at h1;exact qu H S' (by dsimp only[l0,h7,n];omega) _ h1
  exact pD (jy j0 j z2.symm) ju (h9 j wl)
 have jw:x ∉ V_tg:=λ hxV =>
  pD h0 (qu H S' (Nat.zero_le _) _
    (rI ⟨mSs x,h8 jl⟩)) hxV
 have jg:x ∉ U:=λ hxU=>(pS hxU).2 (mSs x)
 have kl:q07 H S {x} V_tg U (10*r+10):=by
  intro l wm
  have jz:qn H S (qs H (S \ (V_tg∪U)) (l - 1) {x})∩U ⊆
     (L \ C)∪X'∪(univ.biUnion (λ a:Fin q =>
      qn H S (qs H (S \ (V_tg∪U)) (l - 1) {x})∩(p a).support.toFinset)) ∪
     (qs H S l {x}∩C):=by
    intro z hz;obtain ⟨wq,wp⟩:=pI hz;have w3:=(pS wp).1;rw[h5] at w3
    rcases pU w3 with h1 | w5
    .
     rcases pU h1 with h2 | w4
     .
      rcases pU h2 with ko | hzX'
      .
       by_cases hC:z∈C
       .
        refine mUr _ (rI ⟨?_,hC⟩);obtain ⟨kz,_,u,wz,wu⟩:=(qo H S _ z).mp wq;have kp:=qw H sS (l - 1) {x} wz
        have km:z∈qs H S ((l - 1)+1) {x}:=by
         by_cases w2:z∈qs H S (l - 1) {x}
         . exact mUl _ w2
         . exact mUr _ ((qo H S _ z).mpr ⟨kz,w2,u,kp,wu⟩)
        rwa [Nat.sub_add_cancel wm] at km
       . exact mUl _ (mUl _ (mUl _ (rS ⟨ko,hC⟩)))
      . exact mUl _ (mUl _ (mUr _ hzX'))
     .
      obtain ⟨a,_,kn⟩:=mB.mp w4
      exact mUl _ (mUr _
       (mB.mpr ⟨a,mUv a,rI ⟨wq,kn⟩⟩))
    .
     refine mUr _ (rI ⟨?_,w5⟩);obtain ⟨kz,_,u,wz,wu⟩:=(qo H S _ z).mp wq;have kp:=qw H sS (l - 1) {x} wz
     have km:z∈qs H S ((l - 1)+1) {x}:=by
      by_cases w2:z∈qs H S (l - 1) {x}
      . exact mUl _ w2
      . exact mUr _ ((qo H S _ z).mpr ⟨kz,w2,u,kp,wu⟩)
     rwa [Nat.sub_add_cancel wm] at km
  have hPsum:(univ.biUnion (λ a:Fin q =>
     qn H S (qs H (S \ (V_tg∪U)) (l - 1) {x})∩(p a).support.toFinset)).card<=r*(l+1):=by
    calc
     _<=∑ a:Fin q,#(qn H S (qs H (S \ (V_tg∪U)) (l - 1) {x})∩(p a).support.toFinset) :=
       cBu
     _<=∑ _a:Fin q,(l+1):=sum_le_sum λ a _=>wd a l wm
     _=q*(l+1):=by simp
     _<=r*(l+1):=nMr _ (by omega)
  have hC_bd:=q0P z6 x l;have h1:=cL jz
  have h2:=cUl ((L \ C)∪X'∪univ.biUnion (λ a:Fin q =>
     qn H S (qs H (S \ (V_tg∪U)) (l - 1) {x})∩(p a).support.toFinset)) (qs H S l {x}∩C)
  have h3:=cUl ((L \ C)∪X') (univ.biUnion (λ a:Fin q =>
     qn H S (qs H (S \ (V_tg∪U)) (l - 1) {x})∩(p a).support.toFinset))
  have h4:=cUl (L \ C) X';have z8:#X'<=t:=(cL sS).trans ze
  have h10:2*r+t+r*(l+1)+(4*l+1)<=(10*r+10)*l:=by nlinarith only[ht,hs,kc,wm]
  dsimp only[C] at h1 h2 h3 h4 kw ⊢;omega
 let Ax:=qs H (S \ (V_tg∪U)) 1 {x};have jd:Ax⊆S \ (V_tg∪U):=qt H _ 1 {x}
 have jj:Ax=qs H (S \ U) 1 {x}:=by
  have z0:S \ (V_tg∪U)=(S \ U) \ V_tg:=by
    ext z;simp only[mS,mU];tauto
  dsimp only[Ax];rw[z0]
  exact qC H (S \ U) V_tg {x} 1 (disjoint_of_subset_left
    ((qw H h6 1 {x}).trans (qu H S' (by omega) {x})) h0)
 have ka:e2*(d:O)/2<=(#Ax:O):=by
  have jz:(S.filter (H.Adj x)) \ (qn H S (qs H (S \ (V_tg∪U)) 0 {x})∩U)⊆qs H (S \ U) 1 {x}:=by
    intro z hz;obtain ⟨jv,w1⟩:=pS hz;obtain ⟨kz,ws⟩:=pF jv
    have hx0:x∈qs H (S \ (V_tg∪U)) 0 {x} :=
     rI ⟨mSs x,rS ⟨wn (pS jl).1,
      λ h=>by rcases pU h with h1 | h2;exact jw h1;exact jg h2⟩⟩
    have wt:x∈qs H (S \ U) 0 {x} :=
     rI ⟨mSs x,rS ⟨wn (pS jl).1,jg⟩⟩
    have jt:z ∉ U:=λ wp=>by
     have jk:z ∉ qs H (S \ (V_tg∪U)) 0 {x}:=λ h =>
      (H.ne_of_adj ws).symm (pSg (pI h).1)
     exact w1 (rI ⟨(qo H S _ z).mpr ⟨kz,jk,x,hx0,ws⟩,wp⟩)
    by_cases za:z∈qs H (S \ U) 0 {x}
    . exact mUl _ za
    .
     exact mUr _ ((qo H (S \ U) _ z).mpr
      ⟨rS ⟨kz,jt⟩,za,x,wt,ws⟩)
  have hU1:#(qn H S (qs H (S \ (V_tg∪U)) 0 {x})∩U)<=10*r+10:=by
    simpa using kl 1 le_rfl
  have hdx:=jp x (wn (pS jl).1);have hsdiff:=cSd (S.filter (H.Adj x)) (qn H S (qs H (S \ (V_tg∪U)) 0 {x})∩U);have hinter:=cL (inter_subset_right (s₁:=S.filter (H.Adj x)) (s₂:=qn H S (qs H (S \ (V_tg∪U)) 0 {x})∩U))
  have js:d<=2*#Ax:=by
    have:=cL jz;rw[<- jj] at this;unfold dS at hdx;omega
  have hR:(d:O)<=2*(#Ax:O):=by exact_mod_cast js
  nlinarith only[hR,wf,show (0:O)<=(d:O) from nCn d]
 have kq:q07 H S Ax V_tg U jf:=by
  intro i hi1
  have ks:qs H (S \ (V_tg∪U)) (i - 1) Ax=qs H (S \ (V_tg∪U)) i {x}:=by
    dsimp only[Ax];rw[<- qy,show 1+(i - 1)=i by omega]
  rw[ks];have h1:=kl (i+1) (by omega);simp only[Nat.add_sub_cancel] at h1;have we:2*(10*r+10)<=jf:=lMl _ _;nlinarith only[h1,we,hi1]
 have kj:#S < 2*#(qs H (S \ (V_tg∪U)) (je+1) {x}):=by
  have ku:Disjoint (qs H (S \ (∅∪U)) h7 Ax) V_tg:=by
    rw[empty_union,jj,<- qy,add_comm 1 h7];exact disjoint_of_subset_left (qw H h6 (h7+1) {x}) h0
  have jm:(#V_tg:O)<=(18/e1*(log n)^3)^(300*jf) :=
    ((by exact_mod_cast j9:(#V_tg:O)<=((r*D_:ℕ):O))).trans j8
  have kr:(#(∅:FS V):O)<=(#Ax:O)*qK e1 (e2*(d:O)) (#Ax:O)/4:=by
    rw[card_empty,Nat.cast_zero];exact div_nonneg (mul_nonneg (nCn _) (by unfold qK;split_ifs <;> positivity)) (by norm_num)
  have h:=(zb Ax ∅ V_tg U (jd.trans sS) (empty_subset _)
    (λ z hz=>rS ⟨j3 hz,λ kn=>(pS (jd kn)).2 (mUl _ hz)⟩)
    (λ z hz=>rS ⟨jh hz,λ kn=>(pS (jd kn)).2 (mUr _ hz)⟩)
    ka kr ku jm kq).2
  rw[empty_union] at h
  have ks:qs H (S \ (V_tg∪U)) je Ax=qs H (S \ (V_tg∪U)) (je+1) {x}:=by
    dsimp only[Ax];rw[<- qy,add_comm 1 je]
  rwa [ks] at h
 have k3:d<=D_:=by
  have hdw:=jp (w j0) (pS (kb j0)).1
  have hlt:dS H S (w j0) < D_:=by
    by_contra zd;push Not at zd;exact (pS (kb j0)).2 (k8 ▸ rF ⟨(pS (kb j0)).1,zd⟩)
  omega
 have j4:T j0⊆S:=(j6 j0).1.trans (sS.trans sS);have ja:#(T j0)=D_:=(j6 j0).2.2.1
 have ji:U⊆S \ T j0:=λ z hz=>rS ⟨jh hz,λ hzt=>by
  have jv:=(pS hz).1;rw[h5] at jv;have w0:=(j6 j0).1 hzt
  rcases pU jv with h1 | w5
  .
    rcases pU h1 with h2 | w4
    .
     rcases pU h2 with ko | hzX'
     . exact (pS (pS w0).1).2 ko
     . exact pD (w7 j0) (h9 j0 hzt) (mUl _ hzX')
    . obtain ⟨a,_,kn⟩:=mB.mp w4;exact hj0 a (z1 a j0 z (pTf kn) hzt).1.symm
  . exact (pS w0).2 w5⟩
 have ki:#S < 2*#(qs H (S \ (U∪(V_tg \ T j0))) je (T j0)):=by
  have jq:e2*(d:O)/2<=(#(T j0):O):=by
    rw[ja];have:(d:O)<=(D_:O):=by exact_mod_cast k3
    nlinarith only[this,wf,show (0:O)<=(d:O) from nCn d]
  have kv:(#U:O)<=(#(T j0):O)*qK e1 (e2*(d:O)) (#(T j0):O)/4:=by
    have h1:(#U:O)<=(kk:O):=by exact_mod_cast kg
    have h2:=q12 (n:=#S) z4 z3 z9 (by omega) jq
     (by exact_mod_cast cL j4)
    have h3:=mlL h2 (nCn #(T j0));rw[ja] at h3 ⊢;linarith only[h1,h3,k5]
  have kf:Disjoint (qs H (S \ (U∪∅)) h7 (T j0)) (V_tg \ T j0):=by
    rw[union_empty];exact disjoint_of_subset_left (qw H h6 h7 (T j0)) j5
  have k4:(#(V_tg \ T j0):O)<=(18/e1*(log n)^3)^(300*jf) :=
    ((by exact_mod_cast (cL sS).trans j9 :
     (#(V_tg \ T j0):O)<=((r*D_:ℕ):O))).trans j8
  have h:=(zb (T j0) U (V_tg \ T j0) ∅ j4 ji
    (λ z hz=>rS ⟨j3 (pS hz).1,(pS hz).2⟩)
    (by simp) jq kv kf k4 (λ _ _=>by simp)).2
  simpa only[union_empty] using h
 obtain ⟨z,hz⟩:=q14
  ((qt H _ _ _).trans sS)
  ((qt H _ _ _).trans sS) kj ki
 obtain ⟨jv,wr⟩:=pI hz;obtain ⟨a1,wg,q1,_,hq1_len,_⟩:=qB jv;have kt:a1=x:=pSg (pI wg).1;subst kt;obtain ⟨t0,ht0,q2,_,hq2_len,_⟩:=qB wr
 have j7:S \ (V_tg∪U)⊆S \ (U∪(V_tg \ T j0)):=λ u hu=>by
  obtain ⟨hS,wb⟩:=pS hu;refine rS ⟨hS,λ h=>?_⟩
  rcases pU h with hu' | hv'
  . exact wb (mUr _ hu')
  . exact wb (mUl _ (pS hv').1)
 have jn:S \ (U∪(V_tg \ T j0))⊆S':=λ u hu =>
  h6 (rS ⟨(pS hu).1,λ hu'=>(pS hu).2 (mUl _ hu')⟩)
 let jo:(q3 H (S \ (U∪(V_tg \ T j0)))).Walk a1 t0 :=
  (q0r q1 (λ u hu=>j7 (q0w q1 (pI wg).2 u hu))).append q2.reverse
 obtain ⟨e0,z5,p0,k2,hp0_len,ke,jr⟩:=q13 jo (T j0) (pI ht0).1
 have jb:∀ u∈p0.support,u∈S \ (U∪(V_tg \ T j0)):=λ u hu =>
  q0w jo (j7 (pI wg).2) u (ke u hu)
 let p₀:=q0r p0 (λ u hu=>jn (jb u hu))
 refine ⟨e0,z5,p₀,q0v _ _ k2,?_,?_,?_,?_⟩
 .
  rw[q0t]
  have hql:jo.length<=2*je+1:=by
    dsimp only[jo];rw[wLa,q0t,wLr];omega
  dsimp only[m,je,n] at ky hql ⊢;omega
 .
  intro u hu wy;rw[q0s] at hu;by_contra wv
  have ww:u∈U:=rS ⟨by
    rcases pU wy with huC | huX'
    . exact mUr _ huC
    . exact mUl _ (mUl _ (mUr _ huX')),
    λ h=>wv (pSg h)⟩
  exact (pS (jb u hu)).2 (mUl _ ww)
 .
  intro j u hu wx;rw[q0s] at hu
  by_cases zc:j=j0
  . subst zc;exact ⟨rfl,jr u hu wx⟩
  .
    exfalso;have w9:u ∉ T j0:=pD (Disjoint.mono (h9 j) (h9 j0) (jy j j0 zc)) wx
    exact (pS (jb u hu)).2 (mUr _
     (rS ⟨mB.mpr ⟨j,mUv j,wx⟩,w9⟩))
 .
  intro a u hu w8;rw[q0s] at hu
  have wv:u=a1:=by
    by_contra hne
    have ww:u∈U:=rS
     ⟨mUl _ (mUr _
      (mB.mpr ⟨a,mUv a,rT w8⟩)),
     λ h=>hne (pSg h)⟩
    exact (pS (jb u hu)).2 (mUl _ ww)
  subst wv;exact ⟨rfl,wa a u w8 (mUr _ jl)⟩
lemma q18 {V:Type*} {e1 e2:O} {t s K:ℕ}
  (w0:0 < e1) (zc:0 < e2) (zb:e2 < 1)
  (ht:1<=t) (hs:1<=s)
  (H:SG V) (S X:FS V) (d D:ℕ) (x0:V) (c:(q3 H S).Walk x0 x0)
  (wk:100<=d) (hdn:d<=#S)
  (hexp:qQ H S e1 (e2*(d:O))) (jv:∀ v∈S,d - 1<=dS H S v)
  (w2:q0G H S x0 c) (wy:X⊆S) (wx:#X<=t) (hD1:1<=D)
  (zs:∀ A Xa Ya Z:FS V,
   A⊆S->Xa⊆S \ A->Ya⊆S \ A->Z⊆S \ A ->
   e2*(d:O)/2<=(#A:O) ->
   (#Xa:O)<=(#A:O)*qK e1 (e2*(d:O)) (#A:O)/4 ->
   Disjoint (qs H (S \ (Xa∪Z)) (floor ((log (log (#S:O)))^5)) A) Ya ->
   (#Ya:O)<=(18/e1*(log (#S:O))^3)^(300*max (2*(10*(t*s)+10)) (K+10)) ->
   q07 H S A Ya Z (max (2*(10*(t*s)+10)) (K+10)) ->
   (18/e1*(log (#S:O))^3)^(400*max (2*(10*(t*s)+10)) (K+10)) <
     (#(qs H (S \ (Xa∪Ya∪Z)) (floor ((log (log (#S:O)))^5)) A):O) /\
   #S < 2*#(qs H (S \ (Xa∪Ya∪Z)) (floor (18/e1*(log (#S:O))^3)) A))
  (j5:c.support.toFinset⊆S)
  (jc:c.support.toFinset.card<=ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2))
  (j9:D<=ceil ((log (#S:O))^K))
  (zh:15/e2<=(d:O))
  (w1:10*(t*s)+10+1<=d/2)
  (w9:2*((t*s:ℕ):O)<=(e2*(d:O)/2)*(e1/(log (15/2))^2)/4)
  (wr:2*floor (18/e1*(log (#S:O))^3)+2<=3*floor (40/e1*(log (#S:O))^3))
  (h3m5m:3*floor (40/e1*(log (#S:O))^3)+2*floor ((log (log (#S:O)))^5)+2 <=
   5*floor (40/e1*(log (#S:O))^3))
  (wm:((3*(t*s)+t+(t*s)*(3*floor (40/e1*(log (#S:O))^3)+1) +
     ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2):ℕ):O) <=
   (((ceil ((log (#S:O))^K))^2:ℕ):O)*(e1/(log (#S:O))^2)/4)
  (zg:(3*(t*s)+t+(t*s)*(3*floor (40/e1*(log (#S:O))^3)+1) +
     ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2)) +
     2*(t*s)*ceil ((log (#S:O))^K) <=
   (ceil ((log (#S:O))^K))^2)
  (k4:(((t*s)*(ceil ((log (#S:O))^K))^2:ℕ):O) <=
   (18/e1*(log (#S:O))^3)^(300*max (2*(10*(t*s)+10)) (K+10)))
  (km:(((ceil ((log (#S:O))^K))^2:ℕ):O) <=
   (18/e1*(log (#S:O))^3)^(400*max (2*(10*(t*s)+10)) (K+10)))
  (hDbig1:1<=ceil ((log (#S:O))^K))
  (k7:((ceil ((log (#S:O))^K))^2+1)^(10*(2*floor ((log (log (#S:O)))^5)+2)) *
     ((t*s)+t+ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2)) <
   #S - 2*(t*s) - ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2))
  (h2rC_lt:2*(t*s)+ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2) < #S)
  (kd:#(S.filter (λ v=>(ceil ((log (#S:O))^K))^2<=dS H S v) \ c.support.toFinset) < 2*(t*s)) :
  let m:=floor (40/e1*(log (#S:O))^3)
  ∃ F:V->Fin s->FS V,
   (∀ x∈X,∀ j:Fin s,q0z H S x D (5*m) (F x j)) /\
   (∀ x∈X,∀ j:Fin s,Disjoint (F x j \ {x}) (c.support.toFinset∪X)) /\
   (∀ x1∈X,∀ j1:Fin s,∀ x2∈X,∀ j2:Fin s,
     (x1,j1)≠(x2,j2)->Disjoint (F x1 j1 \ {x1}) (F x2 j2 \ {x2})):=by
 let r:=t*s;let k0:=max (2*(10*r+10)) (K+10);set n:O:=(#S:O);set m:=floor (40/e1*(log n)^3);set m_lc:=floor (18/e1*(log n)^3);set h9:=floor ((log (log n))^5);set l0:=2*h9+2;set j7:=ceil ((log n)^K);set D_:=j7^2;set C:=c.support.toFinset;set jf:=ceil (2*log n/log ((d - 1 - 1:ℕ):O)+2);set zi:=3*r+t+r*(3*m+1)+jf;let L:=S.filter (λ v=>D_<=dS H S v)
 let S':=S \ L;let X':=X \ L;let r':=#X'*s;have w6:#(L \ C) < 2*r:=kd;have kt:#C<=jf:=jc;have jj:r'<=r:=nMr s ((cL sS).trans wx);have ht_le_r:t<=r:=Nat.le_mul_of_pos_right t hs
 have k8:#S - 2*r - jf<=#S':=by
  have hL_le:#L<=#(L \ C)+#C:=by
   have k3:L⊆(L \ C)∪C:=λ z hz=>by
     by_cases kq:z∈C
     . exact mUr _ kq
     . exact mUl _ (rS ⟨hz,kq⟩)
   exact (cL k3).trans (cUl _ _)
  have h1:=cSd S L;have h2:=cL (inter_subset_right (s₁:=S) (s₂:=L));dsimp only[S'];omega
 have jq:∀ v∈S',dS H S' v<=D_:=λ v hv=>by
  have kx:v ∉ L:=(pS hv).2
  have hlt:dS H S v < D_:=by
   by_contra zt;push Not at zt;exact kx (rF ⟨(pS hv).1,zt⟩)
  have hle:dS H S' v<=dS H S v:=cL (filter_subset_filter _ sS);omega
 have h0:X'⊆S':=sSs wy sR
 have we:∃ w:Fin r'->V,
   (∀ j,w j∈S') /\
   (∀ j,Disjoint (qs H S' (5*l0) {w j}) (X'∪(C \ L))) /\
   (∀ j1 j2,j1≠j2->Disjoint (qs H S' (5*l0) {w j1}) (qs H S' (5*l0) {w j2})):=by
  suffices h:∀ k (hk:k<=r'),∃ w:Fin k->V,
     (∀ j,w j∈S') /\
     (∀ j,Disjoint (qs H S' (5*l0) {w j}) (X'∪(C \ L))) /\
     (∀ j1 j2,j1≠j2->Disjoint (qs H S' (5*l0) {w j1}) (qs H S' (5*l0) {w j2})) by
   exact h r' le_rfl
  intro k
  induction k with
  | zero=>intro _;exact ⟨Fin.elim0,λ j=>j.elim0,λ j=>j.elim0,λ j=>j.elim0⟩
  | succ k ih =>
   intro hk;obtain ⟨w,hwS',jw,j8⟩:=ih (by omega);let j4:=(univ.image w)∪X'∪(C \ L)
   have hSeed_S':j4⊆S':=uS (uS
     (image_subset_iff.mpr λ j _=>hwS' j) h0)
     (sSs j5 sR)
   have jp:j4.card<=r+t+jf:=by
     have h1:=cUl ((univ.image w)∪X') (C \ L);have h2:=cUl (univ.image w) X';have h3:#(univ.image w)<=k:=(card_image_le).trans (by simp);have h4:#X'<=t:=(cL sS).trans wx;have h5:#(C \ L)<=jf:=(cL sS).trans kt
     have hk_le_r:k<=r:=by omega
     dsimp only[j4];omega
   have hB_lt:#(qs H S' (10*l0) j4) < #S':=by
     calc
       #(qs H S' (10*l0) j4)
        <= (D_+1)^(10*l0)*#(j4∩S'):=qD H S' j4 D_ jq (10*l0)
       _<=(D_+1)^(10*l0)*j4.card:=nMl _ (cL inter_subset_left)
       _<=(D_+1)^(10*l0)*(r+t+jf):=nMl _ jp
       _ < #S - 2*r - jf:=k7
       _<=#S':=k8
   have za:(S' \ qs H S' (10*l0) j4).Nonempty:=card_pos.mp (by
     have h1:=cSd S' (qs H S' (10*l0) j4);have h2:=cL (inter_subset_right (s₁:=S') (s₂:=qs H S' (10*l0) j4))
     omega)
   obtain ⟨z,hz⟩:=za;obtain ⟨k2,kv⟩:=pS hz
   have j3:Disjoint (qs H S' (5*l0) {z}) (qs H S' (5*l0) j4):=by
     rw[dL];intro u z6 hus;obtain ⟨a1,ha1,p1,_,hp1,_⟩:=qB z6;have zf:a1=z:=pSg (pI ha1).1;subst zf;obtain ⟨a2,zv,p2,_,hp2,_⟩:=qB hus;have wi:=qA (pI zv).1 (pI zv).2 (p2.append p1.reverse);rw[wLa,wLr] at wi;exact kv (qu H S' (by omega) j4 wi)
   let w':Fin (k+1)->V:=Fin.snoc w z;refine ⟨w',?_,?_,?_⟩
   .
     intro j;refine lastCases ?_ ?_ j
     . simp [w',k2]
     . intro j0;simp [w',hwS' j0]
   .
     intro j;refine lastCases ?_ ?_ j
     .
       simp only[w',snoc_last];refine disjoint_of_subset_right ?_ j3;intro u hu
       have z7:u∈S':=by
        rcases pU hu with h1 | h2
        . exact h0 h1
        . exact (sSs j5 sR) h2
       have ky:u∈j4:=by
        rcases pU hu with h1 | h2
        . exact mUl _ (mUr _ h1)
        . exact mUr _ h2
       exact qu H S' (Nat.zero_le _) j4 (rI ⟨ky,z7⟩)
     . intro j0;simp only[w',snoc_castSucc];exact jw j0
   .
     intro j1 j2 kr;revert kr;refine lastCases ?_ ?_ j1 <;> refine lastCases ?_ ?_ j2
     . intro h;exact absurd rfl h
     . intro j0 _;simp only[w',snoc_last,snoc_castSucc];refine disjoint_of_subset_right (qv H S' (5*l0) ?_) j3;exact sSm (mUl _ (mUl _ (mem_image_of_mem w (mUv j0))))
     . intro j0 _;simp only[w',snoc_last,snoc_castSucc];refine (disjoint_of_subset_right (qv H S' (5*l0) ?_) j3).symm;exact sSm (mUl _ (mUl _ (mem_image_of_mem w (mUv j0))))
     . intro j1' j2' hne';simp only[w',snoc_castSucc];exact j8 _ _ (by intro h;apply hne';rw[h])
 obtain ⟨w,hwS',jw,j8⟩:=we
 have wn:∀ j:Fin r',∃ Tj⊆qs H (S' \ C) (h9+1) {w j},
   q0z H (S' \ C) (w j) D_ (h9+1) Tj:=by
  intro j
  have ji:w j ∉ C:=λ hC =>
   pD (jw j)
     (qu H S' (Nat.zero_le _) _ (rI ⟨mSs _,hwS' j⟩))
     (mUr _ (rS ⟨hC,(pS (hwS' j)).2⟩))
  let Aw:=qs H (S' \ C) 1 {w j};have jd:Aw⊆S' \ C:=qt H (S' \ C) 1 {w j}
  have jm:e2*(d:O)/2<=(#Aw:O):=by
   have k3:(S.filter (H.Adj (w j))) \ ((L \ C)∪(qs H S 1 {w j}∩C))⊆Aw:=by
     intro z hz;obtain ⟨wd,ko⟩:=pS hz;obtain ⟨wt,zo⟩:=pF wd
     have hw0:w j∈qs H (S' \ C) 0 {w j} :=
       rI ⟨mSs _,rS ⟨hwS' j,ji⟩⟩
     have jg:z ∉ C:=λ kq=>by
       have hzB:z∈qs H S 1 {w j}:=by
        by_cases zj:z=w j
        . rw[zj];exact qu H S (Nat.zero_le 1) _ (rI ⟨mSs _,(pS (hwS' j)).1⟩)
        .
         exact mUr _ ((qo H S _ z).mpr
          ⟨wt,λ h=>zj (pSg (pI h).1),
           w j,rI ⟨mSs _,(pS (hwS' j)).1⟩,zo⟩)
       exact ko (mUr _ (rI ⟨hzB,kq⟩))
     have k1:z ∉ L:=λ hzL=>ko (mUl _ (rS ⟨hzL,jg⟩))
     by_cases zm:z∈qs H (S' \ C) 0 {w j}
     . exact mUl _ zm
     .
       exact mUr _ ((qo H (S' \ C) _ z).mpr
        ⟨rS ⟨rS ⟨wt,k1⟩,jg⟩,zm,w j,hw0,zo⟩)
   have hC1:#(qs H S 1 {w j}∩C)<=5:=by simpa using q0P w2 (w j) 1
   have hdw:=jv (w j) (pS (hwS' j)).1;have hsdiff:=cSd (S.filter (H.Adj (w j))) ((L \ C)∪(qs H S 1 {w j}∩C));have hinter:=cL (inter_subset_right (s₁:=S.filter (H.Adj (w j))) (s₂:=(L \ C)∪(qs H S 1 {w j}∩C)));have hun:=cUl (L \ C) (qs H S 1 {w j}∩C)
   have jx:d<=2*#Aw:=by
     have:=cL k3;unfold dS at hdw;omega
   have hR:(d:O)<=2*(#Aw:O):=by exact_mod_cast jx
   nlinarith [show (0:O)<=(d:O) by positivity]
  have w7:(#(L \ C):O)<=(#Aw:O)*qK e1 (e2*(d:O)) (#Aw:O)/4:=by
   have h1:(#(L \ C):O)<=2*(r:O):=by exact_mod_cast w6.le
   have ks:=qP (k:=e2*(d:O)) (x:=e2*(d:O)/2) (y:=(#Aw:O))
     w0.le (by positivity) (by linarith [show 0 < e2*(d:O) by positivity]) jm
   have ki:qK e1 (e2*(d:O)) (e2*(d:O)/2)=e1/(log (15/2))^2:=by
     have hd_pos:(0:O) < (d:O):=by exact_mod_cast (show 0 < d by omega)
     rw[qL (by linarith [show 0 < e2*(d:O) by positivity])]
     have kr:e2*(d:O)≠0:=by positivity
     exact congrArg (λ u=>e1/(log u)^2) (by field_simp [kr])
   rw[ki] at ks;linarith only[h1,ks,w9]
  have kz:q07 H S Aw ∅ C k0:=by
   intro i hi1;simp only[empty_union]
   have k3:qn H S (qs H (S \ C) (i - 1) Aw)∩C⊆qs H S (i+1) {w j}∩C:=by
     intro z hz;obtain ⟨hzN,kq⟩:=pI hz;refine rI ⟨?_,kq⟩;obtain ⟨wt,_,u,huB,z6⟩:=(qo H S _ z).mp hzN;have wq:Aw⊆qs H S 1 {w j}:=qw H (sS.trans sS) 1 _
     have zp:u∈qs H S (i - 1) (qs H S 1 {w j}) :=
       qv H S (i - 1) wq (qw H sS (i - 1) Aw huB)
     rw[<- qy,show 1+(i - 1)=i by omega] at zp
     by_cases zk:z∈qs H S i {w j}
     . exact mUl _ zk
     . exact mUr _ ((qo H S _ z).mpr ⟨wt,zk,u,zp,z6⟩)
   have hbd:=(cL k3).trans (q0P w2 (w j) (i+1));have wj:2*(10*r+10)<=k0:=lMl _ _;nlinarith only[hbd,wj,hi1]
  have k9:L \ C⊆S \ Aw:=λ z hz=>rS
   ⟨(pF (pS hz).1).1,
    λ wc=>(pS (pS (jd wc)).1).2 (pS hz).1⟩
  have kn:C⊆S \ Aw:=λ z hz=>rS
   ⟨j5 hz,λ wc=>(pS (jd wc)).2 hz⟩
  have kf:S \ ((L \ C)∪∅∪C)=S' \ C:=by
   ext z;simp only[S',mS,mU,Finset.notMem_empty,or_false];tauto
  have w4:(#(∅:FS V):O)<=(18/e1*(log n)^3)^(300*k0):=by
   rw[card_empty,Nat.cast_zero];exact pow_nonneg (mul_nonneg (div_nonneg (by norm_num) w0.le) (pow_nonneg (lNn (by dsimp only[n];exact_mod_cast (show 1<=#S by omega))) 3)) _
  have w3:=(zs Aw (L \ C) ∅ C (jd.trans (sS.trans sS))
   k9 (empty_subset _) kn jm w7 (Finset.disjoint_empty_right _) w4 kz).1
  rw[kf] at w3
  have ze:qs H (S' \ C) h9 Aw=qs H (S' \ C) (h9+1) {w j}:=by
   dsimp only[Aw];rw[<- qy,add_comm 1 h9]
  rw[ze] at w3
  have w8:D_<=#(qs H (S' \ C) (h9+1) {w j}):=by
   have:(D_:O) < (#(qs H (S' \ C) (h9+1) {w j}):O):=lL3 km w3
   exact_mod_cast this.le
  have kl:1<=D_:=by dsimp only[D_];nlinarith
  exact q0E (q0D H (S' \ C) (h9+1) (rS ⟨hwS' j,ji⟩)) kl w8
 choose T hT_ball hT_exp using wn
 have h7:∀ j,T j⊆qs H S' (5*l0) {w j}:=λ j =>
  (hT_ball j).trans ((qw H sS (h9+1) {w j}).trans
   (qu H S' (by dsimp only[l0];omega) {w j}))
 obtain ⟨st,tg,en,p,wa,zu,ja,jb,k6,kh,kg,zd⟩ :=
  q0W H S S' C X' s r' T (3*m) sS h0 rfl
   (λ j=>λ z hz=>by
     have h1:=(hT_exp j).1 hz;obtain ⟨k2,ku⟩:=pS h1;refine rS ⟨k2,λ hCX=>?_⟩
     rcases pU hCX with kq | hzX'
     . exact ku kq
     . exact pD (jw j) (h7 j hz) (mUl _ hzX'))
   (λ j1 j2 kr=>Disjoint.mono (h7 j1) (h7 j2) (j8 j1 j2 kr))
   (λ q hq st tg en p wa _ _ jb k6 kh _ _ x hxX' _ j₀ hj0 =>
     q17 w0 zc zb ht hs H S X L d r' x0 c rfl wk hdn jv w2 wy wx jj
       zs j5 jc zh w1 wr wm k4 kd w T hwS' jw j8 hT_ball hT_exp
       q hq st tg en p wa jb k6 kh x hxX' j₀ hj0)
 have jl:∀ a:Fin r',∃ E⊆(p a).support.toFinset∪T (tg a),
   q0z H S (st a) D (5*m) E:=by
  intro a;have w5:=q11 (hT_exp (tg a)) (zu a)
  let k5:(q3 H S).Walk (st a) (en a) :=
   q0r (p a) (λ z hz=>sS (q0w (p a) (h0 (wa a)) z hz))
  have jo:=q0F (m1:=3*m) k5 (wy (pS (wa a)).1)
   (by dsimp only[k5];rw[q0t];exact (jb a).2)
   ((hT_exp (tg a)).1.trans (sS.trans sS)) (zu a) w5
  dsimp only[k5] at jo;rw[q0s] at jo
  have kk:D<=#((p a).support.toFinset∪T (tg a)):=by
   have:D<=D_:=j9.trans (by dsimp only[D_];exact Nat.le_self_pow (by omega) j7)
   calc
     D<=#(T (tg a)):=by rw[(hT_exp (tg a)).2.2.1];exact this
     _<=_:=cL sUr
  obtain ⟨E,wo,wp⟩:=q0E jo hD1 kk;exact ⟨E,wo,q0B wp (by omega)⟩
 choose ExpL hExpL_sub hExpL_is using jl
 have kc:∀ a,Disjoint (ExpL a \ {st a}) (C∪X):=by
  intro a;rw[dL];intro z hz kw;obtain ⟨zl,z1⟩:=pS hz
  have k2:z∈S':=by
   rcases pU (hExpL_sub a zl) with z0 | ws
   . exact q0w (p a) (h0 (wa a)) z (pTf z0)
   . exact sS ((hT_exp (tg a)).1 ws)
  have kp:z∈C∪X':=by
   rcases pU kw with hC | hX
   . exact mUl _ hC
   . exact mUr _ (rS ⟨hX,(pS k2).2⟩)
  rcases pU (hExpL_sub a zl) with z0 | ws
  . exact z1 (mSg.mpr (k6 a z (pTf z0) kp))
  .
   rcases pU kp with hC | hX'
   . exact (pS ((hT_exp (tg a)).1 ws)).2 hC
   . exact pD (jw (tg a)) (h7 (tg a) ws) (mUl _ hX')
 have jr:∀ a b,a≠b->Disjoint (ExpL a \ {st a}) (ExpL b \ {st b}):=by
  intro a b ww;rw[dL];intro z wc hzb;obtain ⟨z3,wb⟩:=pS wc;obtain ⟨z2,hzbne⟩:=pS hzb
  rcases pU (hExpL_sub a z3) with zr | zx <;>
  rcases pU (hExpL_sub b z2) with zq | zw
  . exact wb (mSg.mpr (kg a b ww z (pTf zr) (pTf zq)).1)
  . exact ww (ja (kh a (tg b) z (pTf zr) zw).1).symm
  . exact ww (ja (kh b (tg a) z (pTf zq) zx).1)
  .
   exact pD (Disjoint.mono (h7 (tg a)) (h7 (tg b))
     (j8 (tg a) (tg b) (λ h=>ww (ja h)))) zx zw
 obtain ⟨F_low,ka,jk,kb⟩ :=
  q10 (Forb:=C∪X) (X:=X') st ExpL wa zd hExpL_is kc jr
 let j6:=X∩L;let je:=C∪X∪(X'.biUnion λ x=>univ.biUnion λ j:Fin s=>F_low x j)
 have hForb_hi_card:je.card<=jf+t+r*j7:=by
  have h1:=cUl (C∪X) (X'.biUnion λ x=>univ.biUnion λ j:Fin s=>F_low x j)
  have h2:=cUl C X;have kt:#C<=jf:=jc
  have h3:#(X'.biUnion λ x=>univ.biUnion λ j:Fin s=>F_low x j)<=r*j7:=by
   calc
     _<=∑ x∈X',#(univ.biUnion λ j:Fin s=>F_low x j):=cBu
     _<=∑ x∈X',∑ j:Fin s,#(F_low x j):=sum_le_sum λ x _=>cBu
     _=∑ _x∈X',∑ _j:Fin s,D:=sum_congr rfl λ x hx=>sum_congr rfl λ j _=>(ka x hx j).2.2.1
     _=r'*D:=by simp only[sum_const,card_univ,Fintype.card_fin,smul_eq_mul,r'];ring
     _<=r*j7:=nMm jj j9
  dsimp only[je];omega
 let jn:Fin (j6.card*s) ≃ j6 × Fin s :=
  (Fintype.equivFinOfCardEq (by simp [Fintype.card_prod])).symm
 let js:Fin (j6.card*s)->V:=λ a=>(jn a).1.1
 obtain ⟨A_hi,h8,jz,jy⟩ :=
  q0Z (j6.card*s) (D - 1) (λ a=>S.filter (H.Adj (js a))) je (λ a=>by
   have hdeg:D_<=#(S.filter (H.Adj (js a))):=(pF (pI (jn a).1.2).2).2;have z9:j6.card*s<=r:=nMr s ((cL inter_subset_left).trans wx);have hmul:j6.card*s*(D - 1)<=r*j7:=nMm z9 (by omega)
   have hmul2:r*j7+r*j7=2*(t*s)*j7:=by dsimp only[r];ring
   dsimp only[zi] at zg;omega)
 let ke:V->Fin s->FS V:=λ x j =>
  if hx:x∈j6 then {x}∪A_hi (jn.symm (⟨x,hx⟩,j)) else ∅
 let F:V->Fin s->FS V:=λ x j=>if x∈X' then F_low x j else ke x j
 have kj:∀ x (hx:x∈j6) (j:Fin s),q0z H S x D (5*m) (ke x j):=by
  intro x hx j;dsimp only[ke];rw[dif_pos hx];let a:=jn.symm (⟨x,hx⟩,j)
  have z8:js a=x:=by simp [js,a]
  have jh:x ∉ A_hi a:=λ h =>
   (pS (h8 a h)).2 (mUl _ (mUr _ (pI hx).1))
  have wf:{x}∪A_hi a⊆S:=uS
   (sSm (wy (pI hx).1))
   (λ z hz=>(pF (pS (h8 a hz)).1).1)
  have wl:#({x}∪A_hi a)=D:=by
   rw[card_union_of_disjoint (disjoint_singleton_left.mpr jh),card_singleton,jz a];omega
  refine q0B (m:=1) ⟨wf,mUl _ (mSs x),wl,?_⟩ (by
   have:1<=3*m:=by omega
   omega)
  intro z hz
  have zn:x∈qs H ({x}∪A_hi a) 0 {x} :=
   rI ⟨mSs x,mUl _ (mSs x)⟩
  rcases pU hz with h1 | h2
  . have wz:z=x:=pSg h1;subst wz;exact mUl _ zn
  .
   have wz:z≠x:=λ h=>jh (h ▸ h2)
   exact mUr _ ((qo H ({x}∪A_hi a) _ z).mpr
     ⟨mUr _ h2,λ h=>wz (pSg (pI h).1),
      x,zn,z8 ▸ (pF (pS (h8 a h2)).1).2⟩)
 have h6:∀ x (hx:x∈j6) (j:Fin s),ke x j \ {x}⊆A_hi (jn.symm (⟨x,hx⟩,j)):=by
  intro x hx j z hz;dsimp only[ke] at hz;rw[dif_pos hx] at hz;obtain ⟨h1,h2⟩:=pS hz
  rcases pU h1 with h11 | h12
  . exact absurd h11 h2
  . exact h12
 refine ⟨F,?_,?_,?_⟩
 .
  intro x hx j;dsimp only[F];split_ifs with hx'
  . exact ka x hx' j
  .
   exact kj x (rI ⟨hx,by
     by_contra wg;exact hx' (rS ⟨hx,wg⟩)⟩) j
 .
  intro x hx j;dsimp only[F];split_ifs with hx'
  . exact jk x hx' j
  . have z5:x∈j6:=rI ⟨hx,by by_contra h;exact hx' (rS ⟨hx,h⟩)⟩;rw[dL];intro z hz kw;exact (pS (h8 _ (h6 x z5 j hz))).2 (mUl _ kw)
 .
  intro x1 wv j1 x2 wu j2 kr;dsimp only[F];split_ifs with h1 h2 h2
  . exact kb x1 h1 j1 x2 h2 j2 kr
  .
   have jt:x2∈j6:=rI ⟨wu,by by_contra h;exact h2 (rS ⟨wu,h⟩)⟩;rw[dL];intro z wd z4
   exact (pS (h8 _ (h6 x2 jt j2 z4))).2 (mUr _
     (mB.mpr ⟨x1,h1,mB.mpr ⟨j1,mUv j1,(pS wd).1⟩⟩))
  .
   have ju:x1∈j6:=rI ⟨wv,by by_contra h;exact h1 (rS ⟨wv,h⟩)⟩;rw[dL];intro z wd z4
   exact (pS (h8 _ (h6 x1 ju j1 wd))).2 (mUr _
     (mB.mpr ⟨x2,h2,mB.mpr ⟨j2,mUv j2,(pS z4).1⟩⟩))
  .
   have ju:x1∈j6:=rI ⟨wv,by by_contra h;exact h1 (rS ⟨wv,h⟩)⟩;have jt:x2∈j6:=rI ⟨wu,by by_contra h;exact h2 (rS ⟨wu,h⟩)⟩
   have wh:jn.symm (⟨x1,ju⟩,j1)≠jn.symm (⟨x2,jt⟩,j2):=λ heq=>by
     have:=jn.symm.injective heq
     exact kr (by cases this;rfl)
   exact Disjoint.mono (h6 x1 ju j1) (h6 x2 jt j2) (jy _ _ wh)
lemma q19 {e1 e2:O} {t s K:ℕ}
  (j7:0 < e1) (jf:e1 < 1) (j6:0 < e2) (ja:e2 < 1)
  (ht:1<=t) (hs:1<=s) (hK:10<=K) :
  ∃ d0:ℕ,100<=d0/\∀ {V:Type*} (H:SG V) (S X:FS V) (d D:ℕ)
   (x0:V) (c:(q3 H S).Walk x0 x0),
   d0<=d->d<=#S ->
   qQ H S e1 (e2*(d:O)) ->
   (∀ v∈S,d - 1<=dS H S v) ->
   q0G H S x0 c ->
   X⊆S->1<=#X->#X<=t ->
   1<=D->(D:O)<=(log (#S:O))^K ->
   let m:=floor (40/e1*(log (#S:O))^3)
   ∃ F:V->Fin s->FS V,
    (∀ x∈X,∀ j:Fin s,q0z H S x D (5*m) (F x j)) /\
    (∀ x∈X,∀ j:Fin s,Disjoint (F x j \ {x}) (c.support.toFinset∪X)) /\
    (∀ x1∈X,∀ j1:Fin s,∀ x2∈X,∀ j2:Fin s,
     (x1,j1)≠(x2,j2)->Disjoint (F x1 j1 \ {x1}) (F x2 j2 \ {x2})):=by
 let r:=t*s;let jk:=max (2*(10*r+10)) (K+10);obtain ⟨d1,j0,js⟩:=q0Y (t:=t) (s:=s) (K:=K) j7 jf j6 ht hs hK;obtain ⟨d2,hd2_100,jv⟩:=q0f j7 jf j6 ja (k:=jk) (by omega);obtain ⟨d3,hd3_100,hnc⟩:=q0g j7 jf j6 ja
 refine ⟨max d1 (max d2 d3),lT j0 (lMl _ _),
  λ{V} H S X d D x0 c hd hdn hexp hmindeg hcyc hXS _hX1 hXt hD1 hDK=>?_⟩
 have jx:d1<=d:=lT (lMl _ _) hd;have jw:d2<=d:=lT (lMl _ _) (lT (lMr _ _) hd);have hd3:d3<=d:=lT (lMr _ _) (lT (lMr _ _) hd);have jd:100<=d:=j0.trans jx
 obtain ⟨ju,j8,ji,jq,je,jp,jj,jn,jo,jm,j5,jb,jh,j9,jc⟩ :=
  js #S d jx hdn
 have h5:D<=ceil ((log (#S:O))^K):=by
  exact_mod_cast hDK.trans (nLc _)
 have h7:c.support.toFinset⊆S:=by
  have jr:x0∈S:=by
   cases c with
   | nil=>exact absurd rfl hcyc.1.ne_nil
   | cons hadj _=>exact hadj.2.1
  intro w hw;exact q0w c jr w (pTf hw)
 have j3:c.support.toFinset.card<=ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2):=by
  have jg:=q0L hcyc (by omega) hmindeg
  have h8:c.support.toFinset.card<=c.length:=by
   have hne:=wSn c
   have j4:c.support=c.support.dropLast ++ [x0] :=
    (dropLast_append_getLast hne).symm.trans (by rw[wGl c])
   have jt:c.support.toFinset⊆c.support.dropLast.toFinset:=by
    intro w hw;rw[mT] at hw ⊢;rw[j4,mem_append,List.mem_singleton] at hw
    rcases hw with h1 | hwx
    . exact h1
    .
     rw[hwx]
     have h0:0 < c.support.dropLast.length:=by
      rw[length_dropLast,wLs];have:=hcyc.1.three_le_length;omega
     have jl:∀ (M:List V),M=c.support.dropLast ++ [x0]->∀ hpos:0 < M.length,
       M[0]'hpos=c.support.dropLast[0]'h0:=by
      rintro _ rfl _;exact getElem_append_left h0
     have hx0:c.support.dropLast[0]'h0=x0:=(jl c.support j4 _).symm.trans (q0N c)
     exact (show ∀ y,y=c.support.dropLast[0]'h0->y∈c.support.dropLast from
      λ _ hy=>hy ▸ getElem_mem h0) x0 hx0.symm
   calc
    c.support.toFinset.card<=c.support.dropLast.toFinset.card:=cL jt
    _<=c.support.dropLast.length:=toFinset_card_le _
    _=c.length:=by rw[length_dropLast,wLs];simp
  exact_mod_cast (by exact_mod_cast h8:(c.support.toFinset.card:O)<=(c.length:O)).trans (jg.trans (nLc _))
 have h6:2*(ceil ((log (#S:O))^K))^2 < #S:=by
  have h1:1<=(ceil ((log (#S:O))^K))^2+1:=by omega
  have h2:(ceil ((log (#S:O))^K))^2+1 <=
    ((ceil ((log (#S:O))^K))^2+1)^(10*(2*floor ((log (log (#S:O)))^5)+2)) :=
   Nat.le_self_pow (by omega) _
  have h3:2<=t*s+t+ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2):=by
   have:1<=t*s:=Nat.mul_pos ht hs;omega
  have h4:2*((ceil ((log (#S:O))^K))^2+1) <=
    ((ceil ((log (#S:O))^K))^2+1)^(10*(2*floor ((log (log (#S:O)))^5)+2)) *
    (t*s+t+ceil (2*log (#S:O)/log ((d - 1 - 1:ℕ):O)+2)):=by
   calc
    2*((ceil ((log (#S:O))^K))^2+1)
     = ((ceil ((log (#S:O))^K))^2+1)*2:=Nat.mul_comm _ _
    _<=_:=nMm h2 h3
  omega
 by_cases h9:2*r<=#(S.filter (λ v=>(ceil ((log (#S:O))^K))^2<=dS H S v) \ c.support.toFinset)
 .
  exact q16 j7 j6 ja ht hs H S X d D x0 c jd hdn hexp hmindeg hcyc hXS hXt hD1
   (λ A Xa Ya Z=>jv H S A Xa Ya Z d jw hdn hexp)
   (λ A B W x=>hnc H S A B W d x hd3 hdn hexp hmindeg)
   h7 j3 h5 j8 je jj jn jm h6 h9
 .
  push Not at h9
  exact q18 j7 j6 ja ht hs H S X d D x0 c jd hdn hexp hmindeg hcyc hXS hXt hD1
   (λ A Xa Ya Z=>jv H S A Xa Ya Z d jw hdn hexp)
   h7 j3 h5 ju j8 ji jq jp jo jm j5 jb jh j9 jc h9
lemma q1a {V:Type*} {e1 e2:O} (jx:0 < e1) (jp:0 < e2) (jh:e2<=1/25) (H:SG V) (S W U:FS V) (d r:ℕ) (hdn:d<=#S) (jw:qQ H S e1 (e2*(d:O))) (hWS:W⊆S) (k1:15/e2<=(d:O)) (h6:(1000:O)<=(#S:O)) (hln4:4<=log (#S:O)) (ji:(#W:O)<=e1*(#S:O)/(100*(log (#S:O))^2)) (jz:U⊆S \ W) (hge2:1 < #U) (jj:(#U:O)<=1+(#S:O)/(10*(4:O)^r)) (h7:(#S:O)/25<=(#(qs H (S \ W) (ceil (30/e1*(log (#S:O))^2)*r) U):O)) : ∃ U'⊆S \ W,(#U':O)<=1+(#S:O)/(10*(4:O)^(r+1)) /\ (#S:O)/25<=(#(qs H (S \ W) (ceil (30/e1*(log (#S:O))^2)*(r+1)) U'):O):=by
 let n:O:=(#S:O);let l0:=ceil (30/e1*(log n)^2);let S':=S \ W;let A:=qs H S' (l0*r) U
 have hlogn_pos:0 < log n:=by linarith
 have j8:A⊆S':=qt H S' (l0*r) U
 have jd:n/2<=(#(qs H S' l0 A):O):=by
  by_contra ju;push Not at ju
  have jn:∀ j ≤ l0,(#A:O)*(1+(j:O)*(e1/(2*(log n)^2))) <=
    (#(qs H S' j A):O):=by
   intro j
   induction j with
   | zero =>
    intro _
    have hb0:qs H S' 0 A=A:=by
     ext z;simp only[qs,mI,and_iff_left_iff_imp];exact λ h=>j8 h
    simp [hb0]
   | succ j ih =>
    intro hj;let Bj:=qs H S' j A;have h9:Bj⊆S':=qt H S' j A
    have j6:(#Bj:O) < n/2 :=
     lL3 (by exact_mod_cast cL (qu H S' (by omega) A)) ju
    have h5:(#A:O)<=(#Bj:O):=by
     have h0:A⊆qs H S' 0 A:=λ z hz=>rI ⟨hz,j8 hz⟩
     exact_mod_cast cL (h0.trans (qu H S' (Nat.zero_le j) A))
    have j7:e2*(d:O)/2<=(#Bj:O):=by
     have jb:(d:O)<=n:=by dsimp only[n];exact_mod_cast hdn
     nlinarith only[jh,jp,jb,h7,h5,show (0:O)<=(d:O) from nCn d]
    have jm:100<=#S:=by exact_mod_cast (by linarith only[h6]:(100:O)<=(#S:O))
    have hks:=q12 jx jp k1 jm
     j7 (by exact_mod_cast cL (h9.trans sS))
    have j1:2*#Bj<=#S:=by
     exact_mod_cast (by dsimp only[n] at j6;linarith only[j6]:2*(#Bj:O)<=(#S:O))
    have j4:=jw Bj (h9.trans sS) j7 j1
    have ja:qn H S Bj⊆qn H S' Bj∪W:=by
     intro z hz;obtain ⟨hzS,jt,u,huB,huz⟩:=(qo H S Bj z).mp hz
     by_cases k2:z∈W
     . exact mUr _ k2
     . exact mUl _ ((qo H S' Bj z).mpr ⟨rS ⟨hzS,k2⟩,jt,u,huB,huz⟩)
    have j3:(#(qn H S Bj):O)<=(#(qn H S' Bj):O)+(#W:O):=by
     exact_mod_cast (cL ja).trans (cUl _ _)
    have jr:(#W:O)<=(#Bj:O)*(e1/(4*(log n)^2)):=by
     have h1:e1*n/(100*(log n)^2)=(n/25)*(e1/(4*(log n)^2)):=by ring
     have h2:=mlR (h7.trans h5) (show (0:O)<=e1/(4*(log n)^2) by positivity);linarith only[ji,h1,h2]
    have je:(#Bj:O)*(e1/(2*(log n)^2))<=(#(qn H S' Bj):O):=by
     have h1:=mlL hks (nCn #Bj);rw[mul_comm (qK _ _ _)] at j4
     have h2:(#Bj:O)*(e1/(log n)^2) =
       (#Bj:O)*(e1/(2*(log n)^2))+2*((#Bj:O)*(e1/(4*(log n)^2))):=by ring
     linarith only[h1,j4,j3,jr,h2]
    have jk:(#(qs H S' (j+1) A):O)=(#Bj:O)+(#(qn H S' Bj):O):=by
     exact_mod_cast qx H S' j A
    have hih:=ih (by omega)
    have jl:(#A:O)*(1+((j+1:ℕ):O)*(e1/(2*(log n)^2))) <=
      (#Bj:O)*(1+e1/(2*(log n)^2)):=by
     push_cast;have h1:=mlR hih (show (0:O)<=1+e1/(2*(log n)^2) by positivity)
     have h2:0<=(#A:O)*((j:O)*(e1/(2*(log n)^2))^2):=by positivity
     linarith only[h1,h2,show (#A:O)*(1+(j:O)*(e1/(2*(log n)^2)))*(1+e1/(2*(log n)^2)) =
      (#A:O)*(1+((j:O)+1)*(e1/(2*(log n)^2))) +
      (#A:O)*((j:O)*(e1/(2*(log n)^2))^2) by ring]
    linarith only[jk,je,jl,
     show (#Bj:O)*(1+e1/(2*(log n)^2))=(#Bj:O)+(#Bj:O)*(e1/(2*(log n)^2)) by ring]
  have jv:=jn l0 le_rfl;have jf:30/e1*(log n)^2<=(l0:O):=nLc _
  have h16:(16:O)<=1+(l0:O)*(e1/(2*(log n)^2)):=by
   have h1:=mlR jf (show (0:O)<=e1/(2*(log n)^2) by positivity)
   have h2:30/e1*(log n)^2*(e1/(2*(log n)^2))=15:=by field_simp;norm_num
   linarith only[h1,h2]
  have k0:(n/25)*16<=(#A:O)*(1+(l0:O)*(e1/(2*(log n)^2))) :=
   mLm h7 h16 (by norm_num) (nCn #A)
  linarith only[jv,k0,ju,h6]
 let eU:Fin #U ≃ U:=(Fintype.equivFinOfCardEq (Fintype.card_coe U)).symm
 let Uq:Fin 12->FS V:=λ q =>
  ((univ:FS (Fin #U)).filter (λ i=>i.val % 12=q.val)).image (λ i=>(eU i).1)
 have js:U=univ.biUnion Uq:=by
  ext z;simp only[Uq,mB,mUv,true_and,mem_image,mF]
  constructor
  . intro hz;refine ⟨⟨(eU.symm ⟨z,hz⟩).val % 12,mod_lt _ (by omega)⟩,eU.symm ⟨z,hz⟩,rfl,by simp⟩
  . rintro ⟨_,i,_,rfl⟩;exact (eU i).2
 have jc:∀ q,Uq q⊆S':=λ q z hz=>by
  obtain ⟨i,_,rfl⟩:=mem_image.mp hz;exact jz (eU i).2
 have j5:∀ q,#(Uq q)<=1+(#U - 1)/12:=by
  intro q
  calc
   #(Uq q)<=#((univ:FS (Fin #U)).filter (λ i=>i.val % 12=q.val)) :=
     card_image_le
   _<=1+(#U - 1)/12:=by
    let f:{i:Fin #U // i.val % 12=q.val}->Fin (1+(#U - 1)/12):=λ i =>
     ⟨i.1.val/12,by have:=i.1.isLt;omega⟩
    have jg:Injective f:=λ a b hab=>by
     have hdiv:a.1.val/12=b.1.val/12:=congrArg Fin.val hab;have hmod:a.1.val % 12=b.1.val % 12:=a.2.trans b.2.symm;exact Subtype.ext (Fin.ext (by omega))
    have h1:=Fintype.card_le_of_injective f jg;simpa only[Fintype.card_subtype,Fintype.card_fin] using h1
 have j0:n/2<=∑ q:Fin 12,(#(qs H S' (l0*(r+1)) (Uq q)):O):=by
  have jy:qs H S' (l0*(r+1)) U=univ.biUnion (λ q=>qs H S' (l0*(r+1)) (Uq q)):=by
   conv_lhs=>rw[js];rw[qz]
  have h1:#(qs H S' (l0*(r+1)) U)<=∑ q:Fin 12,#(qs H S' (l0*(r+1)) (Uq q)):=by
   rw[jy];exact cBu
  have h2:qs H S' (l0*(r+1)) U=qs H S' l0 A:=by
   dsimp only[A];rw[mul_add,mul_one,qy]
  rw[h2] at h1;exact jd.trans (by exact_mod_cast h1)
 have jo:∃ q:Fin 12,n/25<=(#(qs H S' (l0*(r+1)) (Uq q)):O):=by
  by_contra jq;push Not at jq
  have h8:∑ q:Fin 12,(#(qs H S' (l0*(r+1)) (Uq q)):O) < ∑ _q:Fin 12,(n/25) :=
   Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (λ q _=>jq q)
  simp only[sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] at h8;linarith only[j0,h8,h6]
 obtain ⟨q,j9⟩:=jo
 have j2:(#(Uq q):O)<=1+n/(10*(4:O)^(r+1)):=by
  have h1:(#(Uq q):O)<=1+(((#U - 1)/12:ℕ):O):=by exact_mod_cast j5 q
  have h2:12*(((#U - 1)/12:ℕ):O)<=((#U - 1:ℕ):O):=by
   exact_mod_cast Nat.mul_div_le (#U - 1) 12
  have h3:((#U - 1:ℕ):O)=(#U:O) - 1:=by rw[Nat.cast_sub (by omega),Nat.cast_one]
  have h4:(n/(10*(4:O)^r))/12<=n/(10*(4:O)^(r+1)):=by
   rw[pow_succ,div_div,show 10*(4:O)^r*12=3*(10*((4:O)^r*4)) by ring]
   exact dLl (by positivity) (by positivity)
    (by nlinarith [pow_pos (by norm_num:(0:O) < 4) r])
  linarith only[h1,h2,h3,h4,jj]
 exact ⟨Uq q,jc q,j2,j9⟩
lemma q1b {e1 e2:O} (j9:0 < e1) (he11:e1 < 1)
  (ji:0 < e2) (j7:e2<=1/25) :
  ∃ d0:ℕ,100<=d0/\∀ {V:Type*} (H:SG V) (S W:FS V) (d:ℕ),
   d0<=d->d<=#S ->
   qQ H S e1 (e2*(d:O)) ->
   W⊆S->(#W:O)<=e1*(#S:O)/(100*(log (#S:O))^2) ->
   let m:=floor (40/e1*(log (#S:O))^3)
   ∃ (v:V) (B:FS V),B⊆S \ W/\(#S:O)/25<=(#B:O) /\
    q0z H (S \ W) v #B m B:=by
 have jo:∀ᶠ x:O in atTop,
   15/e2<=x/\(1000:O)<=x/\(4:O)<=log x /\
   (30/e1*(log x)^2+1)*log x<=40/e1*(log x)^3 - 1 /\
   x/10 < (4:O)^(floor (log x)):=by
  have jc:∀ᶠ x:O in atTop,x/10 < (4:O)^(floor (log x)):=by
   filter_upwards [eGe (exp 20)] with x hx
   have h7:0 < x:=lL2 (ePp _) hx
   have hlx:20<=log x:=by rw[lIe h7];exact hx
   have j8:(13/10:O) < log 4:=by
    have h1:(4:O)=2^2:=by norm_num
    have h2:(65/100:O) < log 2:=by linarith [Real.log_two_gt_d9]
    rw[h1,lP];push_cast;linarith
   have hfl:log x - 1 < (floor (log x):O):=by linarith [nL1 (log x)]
   have j5:x < exp ((floor (log x):O)*log 4):=by
    conv_lhs=>rw[<- exp_log h7]
    apply exp_lt_exp.mpr;have hm1:=mul_lt_mul_of_pos_right hfl (by linarith:(0:O) < log 4);have hm2:=mul_lt_mul_of_pos_left j8 (by linarith:(0:O) < log x - 1)
    calc
     log x < 13/10*log x - 13/10:=by linarith only[hlx]
     _=(log x - 1)*(13/10):=by ring
     _ < (log x - 1)*log 4:=hm2
     _ < (floor (log x):O)*log 4:=hm1
   rw[mul_comm (floor (log x):O) (log 4),
     <- rpow_def_of_pos (by norm_num:(0:O) < 4),rN] at j5
   linarith
  filter_upwards [eGe (max (15/e2) 1000),
   lGe (max 4 (2*e1+1)),jc] with x hx hl h4
  have h15:15/e2<=x:=lT (lMl _ _) hx;have j2:(1000:O)<=x:=lT (lMr _ _) hx;have hl4:4<=log x:=lT (lMl _ _) hl;have hl_eps:2*e1+1<=log x:=lT (lMr _ _) hl;refine ⟨h15,j2,hl4,?_,h4⟩
  have h1:log x+1<=10/e1*(log x)^3:=by
   have h10:10<=10/e1:=by rw[lDi j9];linarith
   have h3:(log x)<=(log x)^3:=by
    calc
     log x=(log x)^1:=(pow_one _).symm
     _<=(log x)^3:=pLr (by linarith) (by omega)
   nlinarith
  nlinarith [show (30/e1*(log x)^2+1)*log x =
    30/e1*(log x)^3+log x by ring,
   show 40/e1*(log x)^3=30/e1*(log x)^3+10/e1*(log x)^3 by ring]
 rw[eAt] at jo;obtain ⟨B0,jq⟩:=jo;refine ⟨max 100 (ceil B0),lMl _ _,λ{V} H S W d hd hdn j5 hWS hWcard=>?_⟩
 have jp:B0<=(d:O):=(nLc B0).trans (by exact_mod_cast (lMr 100 (ceil B0)).trans hd);have hnB:B0<=(#S:O):=jp.trans (by exact_mod_cast hdn);have jm:15/e2<=(d:O):=(jq (d:O) jp).1;obtain ⟨_,j3,jh,hrad_le,h4R⟩:=jq (#S:O) hnB;set n:O:=(#S:O);set m:=floor (40/e1*(log n)^3);set l0:=ceil (30/e1*(log n)^2);set R:=floor (log n);let S':=S \ W
 have hlogn_pos:0 < log n:=by linarith
 have hS'_card:n/2<=(#S':O):=by
  have h1:#S'=#S - #W:=by
   dsimp only[S'];have ha:=cSd S W;rw[Finset.inter_eq_right.mpr hWS] at ha;omega
  have hWle:(#W:O)<=n/2:=by
   have hden:(100*(log n)^2)>=2:=by nlinarith
   have h2:e1*n/(100*(log n)^2)<=n/2:=by
    rw[div_le_div_iff₀ (by positivity) (by norm_num)];nlinarith
   exact hWcard.trans h2
  have jb:#W<=#S:=cL hWS;rw[h1,Nat.cast_sub jb];linarith
 let P:ℕ->Prop:=λ r=>∃ U⊆S',(#U:O)<=1+n/(10*(4:O)^r) /\
   n/25<=(#(qs H S' (l0*r) U):O)
 have hP0:P 0:=by
  have ja:ceil (n/25)<=#S':=by
   have h1:(ceil (n/25):O) < n/25+1:=ceil_lt_add_one (by positivity);exact_mod_cast (show (ceil (n/25):O)<=(#S':O) by linarith)
  obtain ⟨U0,hU0S',h6⟩:=exists_subset_card_eq ja;refine ⟨U0,hU0S',?_,?_⟩
  . rw[pow_zero,mul_one,h6];have h1:(ceil (n/25):O) < n/25+1:=ceil_lt_add_one (by positivity);linarith
  .
   simp only[mul_zero]
   have jj:qs H S' 0 U0=U0:=by
    ext z;simp only[qs,mI,and_iff_left_iff_imp];exact λ h=>hU0S' h
   rw[jj,h6];exact nLc _
 let Rs:=(range (R+1)).filter P;have j0:Rs.Nonempty:=⟨0,rF ⟨mem_range.mpr (by omega),hP0⟩⟩;let r:=Rs.max' j0;have h8:r∈Rs:=max'_mem Rs j0;have h5:r<=R:=Nat.lt_succ_iff.mp (mem_range.mp (pF h8).1);obtain ⟨U,hUS',h9,h0⟩:=(pF h8).2
 have hU_le_1:#U<=1:=by
  by_contra j4;push Not at j4
  have hr_lt_R:r < R:=by
   by_contra jn;push Not at jn;have je:r=R:=le_antisymm h5 jn;rw[je] at h9
   have hfrac:n/(10*(4:O)^R) < 1:=by rw[div_lt_one (by positivity)];linarith
   have hU2:(2:O)<=(#U:O):=by exact_mod_cast j4
   linarith
  have jl:P (r+1):=q1a j9 ji j7 H S W U d r hdn j5 hWS jm j3 jh hWcard hUS' j4 h9 h0;have jg:r+1∈Rs:=rF ⟨mem_range.mpr (by omega),jl⟩
  have:=le_max' Rs (r+1) jg
  omega
 have jk:U.Nonempty:=by
  by_contra j6;rw[not_nonempty_iff_eq_empty] at j6
  have jj:qs H S' (l0*r) ∅=∅:=by
   clear j6 h0
   induction (l0*r) with
   | zero=>simp [qs]
   | succ k ih =>
    simp only[qs,ih,empty_union]
    ext z;simp [qo]
  rw[j6,jj,card_empty,Nat.cast_zero] at h0;linarith
 obtain ⟨v,jd⟩:=jk
 have j1:U={v}:=Finset.eq_singleton_iff_unique_mem.mpr ⟨jd,λ u hu=>by
  by_contra huv;have h2:2<=#U:=one_lt_card.mpr ⟨u,hu,v,jd,huv⟩
  omega⟩
 rw[j1] at h0
 have jf:l0*r<=m:=by
  have h1:(l0:O)<=30/e1*(log n)^2+1:=(ceil_lt_add_one (by positivity)).le;have h2:(r:O)<=log n:=(by exact_mod_cast h5:(r:O)<=(R:O)).trans (nFl (by linarith))
  have h3:((l0*r:ℕ):O)<=(m:O):=by
   push_cast;have hprod:=mLm h1 h2 (nCn r) (by positivity)
   have hm_lb:40/e1*(log n)^3 - 1 < (m:O):=by linarith [nL1 (40/e1*(log n)^3)]
   linarith
  exact_mod_cast h3
 exact ⟨v,qs H S' (l0*r) {v},qt H S' _ _,h0,
  q0B (q0D H S' (l0*r) (hUS' jd)) jf⟩
def q1c {V:Type*} (H:SG V) (S A:FS V) (m:ℕ)
  (v:Fin 4->V) (F:Fin 4->FS V) (B:Fin (100*m)->FS V) (t:ℕ):Prop :=
 let N:=25*m
 ∃ (ord:Fin t->Fin 4) (k_idx:Fin t->Fin N->Fin (100*m))
  (en:Fin t->Fin N->V) (P:∀ a j,(q3 H (S \ A)).Walk (v (ord a)) (en a j)),
  Injective ord /\
  Injective (λ p:Fin t × Fin N=>k_idx p.1 p.2) /\
  (∀ a j,en a j∈B (k_idx a j)) /\
  (∀ a j,(P a j).IsPath/\(P a j).length<=2*m) /\
  (∀ a1 j1 a2 j2,a1≠a2->Disjoint (P a1 j1).support.toFinset (P a2 j2).support.toFinset) /\
  (∀ a j1 j2,j1≠j2->Disjoint ((P a j1).support.toFinset \ F (ord a)) ((P a j2).support.toFinset \ F (ord a))) /\
  (∀ a j (i':Fin 4),(∀ b:Fin t,b<=a->ord b≠i')->Disjoint (P a j).support.toFinset (F i'))
lemma q1d {V:Type*} {e1:O} (he10:0 < e1) (H:SG V) (S A:FS V) (D m sz:ℕ) (v:Fin 4->V) (F:Fin 4->FS V) (cB:Fin (100*m)->V) (B:Fin (100*m)->FS V) (hAS:A⊆S) (ky:4<=log (#S:O)) (w4:(log (#S:O))^10<=(D:O)) (wd:100/e1*(log (#S:O))^3<=(m:O)) (kw:(m:O)<=3000/e1*(log (#S:O))^3) (w2:(100:O)*(3000/e1*(log (#S:O))^3)*(2*(3000/e1*(log (#S:O))^3)+1)<=(log (#S:O))^7) (kk:(#A:O)<=(D:O)/(log (#S:O))^3) (jf:2*D<=sz) (h0:∀ i,q0z H (S \ A) (v i) D m (F i)) (jy:∀ i j,i≠j->Disjoint (F i) (F j)) (jz:∀ k,q0z H (S \ (A∪univ.biUnion F)) (cB k) sz (floor (40/e1*(log (#S:O))^3)) (B k)) (hnc:∀ A_nc B_nc Wq:FS V,∀ x:O, A_nc⊆S->B_nc⊆S->Wq⊆S \ (A_nc∪B_nc) -> 1<=x->x<=(#A_nc:O)->x<=(#B_nc:O) -> (#Wq:O)*(log (#S:O))^3<=10*x -> ∃ (a:V) (b:V) (_:a∈A_nc) (_:b∈B_nc) (p:(q3 H (S \ Wq)).Walk a b), p.IsPath/\(p.length:O)<=40/e1*(log (#S:O))^3 /\ (∀ w∈p.support,w∈A_nc->w=a)/\(∀ w∈p.support,w∈B_nc->w=b)) (t:ℕ) (ht:t < 4) (hG:q1c H S A m v F B t) : q1c H S A m v F B (t+1):=by
 let n:O:=(#S:O);let N:=25*m;obtain ⟨kp,jc,en,P,j6,jt,hen,jw,j4,j3,k9⟩:=hG;let J:=(univ:FS (Fin 4)).filter (λ i=>∀ a:Fin t,kp a≠i)
 let w7:=(univ:FS (Fin t × Fin N)).image (λ p=>jc p.1 p.2)
 let h6:=(univ:FS (Fin (100*m))) \ w7
 have je:#J=4 - t:=by
  have kg:J=univ \ univ.image kp:=by ext i;simp [J]
  rw[kg,card_sdiff_of_subset (Finset.subset_univ _),card_image_of_injective _ j6];simp
 have j0:h6.card=N*#J:=by
  dsimp only[h6];rw[card_sdiff_of_subset (Finset.subset_univ _),card_image_of_injective _ jt];simp only[card_univ,Fintype.card_fin,Fintype.card_prod,je]
  have ku:(4 - t)*N+t*N=100*m:=by
   rw[<- Nat.add_mul,Nat.sub_add_cancel (by omega)];dsimp only[N];ring
  rw[mul_comm N (4 - t),<- ku,Nat.add_sub_cancel]
 let W':=A∪univ.biUnion (λ p:Fin t × Fin N=>(P p.1 p.2).support.toFinset)
 have k7:W'⊆S:=uS hAS (biUnion_subset.mpr λ p _ z hz =>
  sS (q0w (P p.1 p.2) ((h0 (kp p.1)).1 (h0 (kp p.1)).2.1) z (pTf hz)))
 have h5:∀ i∈J,Disjoint W' (F i):=λ i hi=>by
  rw[dL];intro z hzW k0
  rcases pU hzW with hzA | w9
  . exact (pS ((h0 i).1 k0)).2 hzA
  . obtain ⟨p,_,hzp⟩:=mB.mp w9;exact pD (k9 p.1 p.2 i (λ b _=>(pF hi).2 b)) hzp k0
 let eK:Fin h6.card ≃ h6:=(Fintype.equivFinOfCardEq (Fintype.card_coe h6)).symm;let FJ:=J.biUnion F
 have w1:∀ q (hq:q<=h6.card),∃ (jk kl:Fin q->V)
   (Q:∀ c:Fin q,(q3 H (S \ W')).Walk (jk c) (kl c)),
   (∀ c,jk c∈FJ)/\(∀ c,kl c∈B (eK ⟨c.val,by have:=c.isLt;omega⟩).1) /\
   (∀ c,(Q c).IsPath/\(Q c).length<=m) /\
   (∀ c,∀ w∈(Q c).support,w∈FJ->w=jk c) /\
   (∀ c1 c2,c1≠c2->Disjoint (Q c1).support.toFinset (Q c2).support.toFinset):=by
  intro q
  induction q with
  | zero=>intro _;exact ⟨Fin.elim0,Fin.elim0,λ c=>c.elim0,λ c=>c.elim0,λ c=>c.elim0,λ c=>c.elim0,λ c=>c.elim0,λ c=>c.elim0⟩
  | succ q ih =>
   intro hq;obtain ⟨jk,kl,Q,jp,kf,jg,k8,jb⟩:=ih (by omega);let kq:=(eK ⟨q,by omega⟩).1;let ka:=univ.biUnion (λ c:Fin q=>(Q c).support.toFinset)
   let Wq:=W'∪ka
   have k6:Wq⊆S:=uS k7 (biUnion_subset.mpr λ c _ z hz =>
    sS (q0w (Q c) (rS
     ⟨sS (by obtain ⟨i,_,jl⟩:=mB.mp (jp c);exact (h0 i).1 jl),
      λ h=>by obtain ⟨i,hi,jl⟩:=mB.mp (jp c);exact pD (h5 i hi) h jl⟩)
     z (pTf hz)))
   have hP_Q_card:#(univ.biUnion (λ p:Fin t × Fin N=>(P p.1 p.2).support.toFinset))+ka.card <=
     100*m*(2*m+1):=by
    have h1:#(univ.biUnion (λ p:Fin t × Fin N=>(P p.1 p.2).support.toFinset))<=t*N*(2*m+1):=by
     calc
       _<=∑ p:Fin t × Fin N,(P p.1 p.2).support.toFinset.card:=cBu
       _<=∑ _p:Fin t × Fin N,(2*m+1):=sum_le_sum λ p _ =>
         (q0y (P p.1 p.2)).trans (Nat.add_le_add_right (jw p.1 p.2).2 1)
       _=t*N*(2*m+1):=by simp
    have h2:ka.card<=q*(2*m+1):=by
     calc
       _<=∑ c:Fin q,(Q c).support.toFinset.card:=cBu
       _<=∑ _c:Fin q,(2*m+1):=sum_le_sum λ c _ =>
         (q0y (Q c)).trans (by have:=(jg c).2;omega)
       _=q*(2*m+1):=by simp
    have h3:t*N+q<=100*m:=by
     have ku:t*N+h6.card=100*m:=by
       rw[j0,je,mul_comm N (4 - t),<- Nat.add_mul,Nat.add_sub_cancel' (by omega)];dsimp only[N];ring
     omega
    calc
     _<=t*N*(2*m+1)+q*(2*m+1):=nAa h1 h2
     _=(t*N+q)*(2*m+1):=by ring
     _<=100*m*(2*m+1):=nMr _ h3
   have jx:((100*m*(2*m+1):ℕ):O)<=(D:O)/(log n)^3:=by
    have h1:((100*m*(2*m+1):ℕ):O)<=(log n)^7:=by
     push_cast
     have h2:=mLm (mlL kw (by norm_num:(0:O)<=100))
       (show 2*(m:O)+1<=2*(3000/e1*(log n)^3)+1 by linarith only[kw]) (by positivity) (by positivity)
     exact h2.trans w2
    have h2:(log n)^7<=(D:O)/(log n)^3:=by
     rw[lDi (by positivity)];linarith only[w4,show (log n)^7*(log n)^3=(log n)^10 by ring]
    exact h1.trans h2
   have j9:(#Wq:O)<=2*((D:O)/(log n)^3):=by
    have h1:#Wq<=#A+100*m*(2*m+1):=by
     have h2:=cUl W' ka;have h3:=cUl A (univ.biUnion (λ p:Fin t × Fin N=>(P p.1 p.2).support.toFinset))
     dsimp only[Wq,W'] at h2 ⊢;omega
    have w6:(#Wq:O)<=(#A:O)+((100*m*(2*m+1):ℕ):O):=by exact_mod_cast h1
    linarith only[w6,kk,jx]
   let A_nc:=FJ \ Wq;let B_nc:=B kq \ Wq
   have h8:(#Wq:O)<=(D:O)/2:=by
    have kx:(4:O)<=(log n)^3:=by
     calc
       (4:O)<=4^3:=by norm_num
       _<=(log n)^3:=pLl (by norm_num) ky 3
    have wf:(D:O)/(log n)^3<=(D:O)/4 :=
     dLl (nCn D) (by norm_num) kx
    linarith only[j9,wf]
   have ji:(D:O)/2<=(#A_nc:O):=by
    have wh:J.Nonempty:=card_pos.mp (by omega);obtain ⟨i0,kb⟩:=wh;have ki:D<=#FJ:=(h0 i0).2.2.1 ▸ cL (Finset.subset_biUnion_of_mem F kb);have h1:=cSd FJ Wq;have h2:=cL (inter_subset_right (s₁:=FJ) (s₂:=Wq))
    have w6:(#A_nc:O)+(#(FJ∩Wq):O)=(#FJ:O):=by exact_mod_cast h1
    have wk:(#(FJ∩Wq):O)<=(#Wq:O):=by exact_mod_cast h2
    have wi:(D:O)<=(#FJ:O):=by exact_mod_cast ki
    linarith only[w6,wk,wi,h8]
   have jh:(D:O)/2<=(#B_nc:O):=by
    have h1:=cSd (B kq) Wq;have h2:=cL (inter_subset_right (s₁:=B kq) (s₂:=Wq))
    have w6:(#B_nc:O)+(#(B kq∩Wq):O)=(sz:O):=by
     rw[<- (jz kq).2.2.1];exact_mod_cast h1
    have wk:(#(B kq∩Wq):O)<=(#Wq:O):=by exact_mod_cast h2
    have wc:2*(D:O)<=(sz:O):=by exact_mod_cast jf
    linarith only[w6,wk,wc,h8]
   have kh:(#Wq:O)*(log n)^3<=10*((D:O)/2):=by
    have h:=mlR j9 (show (0:O)<=(log n)^3 by positivity)
    have kn:2*((D:O)/(log n)^3)*(log n)^3=2*(D:O):=by
     rw[mul_assoc,div_mul_cancel₀ _ (by positivity)]
    linarith only[h,kn,show (0:O)<=(D:O) from nCn D]
   obtain ⟨a0,b0,k5,hb0,q0,jq,k4,kv,_⟩ :=
    hnc A_nc B_nc Wq ((D:O)/2)
     (sS.trans (biUnion_subset.mpr λ i _=>(h0 i).1.trans sS))
     (sS.trans ((jz kq).1.trans sS))
     (λ z hz=>rS ⟨k6 hz,λ h=>by
       rcases pU h with h1 | h2
       . exact (pS h1).2 hz
       . exact (pS h2).2 hz⟩)
     (by
        have h2:(2:O)<=(log n)^10:=by
         calc
          (2:O)<=4^10:=by norm_num
          _<=(log n)^10:=pLl (by norm_num) ky 10
        linarith only[h2,w4])
     ji jh kh
   have ja:∀ w∈q0.support,w∈S \ W':=λ w hw=>by
    have h1:=q0w q0
     (rS ⟨sS (by obtain ⟨i,_,jl⟩:=mB.mp (pS k5).1;exact (h0 i).1 jl),
       (pS k5).2⟩) w hw
    exact rS ⟨(pS h1).1,λ h=>(pS h1).2 (mUl _ h)⟩
   let w8:(q3 H (S \ W')).Walk a0 b0:=q0r q0 ja
   have jr:w8.length<=m:=by
    rw[q0t]
    have hnn:0<=(log n)^3/e1:=by positivity
    have hle:(q0.length:O)<=(m:O):=by
     linarith only[k4,wd,hnn,
       show 40/e1*(log n)^3=40*((log n)^3/e1) by ring,
       show 100/e1*(log n)^3=100*((log n)^3/e1) by ring]
    exact_mod_cast hle
   let j5:Fin (q+1)->V:=Fin.snoc jk a0;let jj:Fin (q+1)->V:=Fin.snoc kl b0
   let Q1:∀ c:Fin (q+1),(q3 H (S \ W')).Walk (j5 c) (jj c) :=
    lastCases (w8.copy (by simp [j5]) (by simp [jj]))
     (λ c0=>(Q c0).copy (by simp [j5]) (by simp [jj]))
   refine ⟨j5,jj,Q1,?_,?_,?_,?_,?_⟩
   .
    intro c;refine lastCases ?_ ?_ c
    . simpa [j5] using (pS k5).1
    . intro c0;simpa [j5] using jp c0
   .
    intro c;refine lastCases ?_ ?_ c
    . simpa [jj,kq] using (pS hb0).1
    . intro c0;simpa [jj] using kf c0
   .
    intro c;refine lastCases ?_ ?_ c
    . simp only[Q1,lastCases_last];exact ⟨q0p (q0v _ _ jq) _ _,by simp [jr]⟩
    . intro c0;simp only[Q1,lastCases_castSucc];exact ⟨q0p (jg c0).1 _ _,by simp [(jg c0).2]⟩
   .
    intro c w hw jo;revert hw jo;refine lastCases ?_ ?_ c
    .
     intro hw jo;simp only[Q1,lastCases_last,support_copy,j5,snoc_last] at hw ⊢
     have wn:w∈q0.support:=by rwa [q0s] at hw
     have kt:w ∉ Wq:=(pS (q0w q0
       (rS ⟨sS (by obtain ⟨i,_,jl⟩:=mB.mp (pS k5).1;exact (h0 i).1 jl),
        (pS k5).2⟩) w wn)).2
     exact kv w wn (rS ⟨jo,kt⟩)
    . intro c0 hw jo;simp only[Q1,lastCases_castSucc,support_copy,j5,snoc_castSucc] at hw ⊢;exact k8 c0 w hw jo
   .
    intro c1 c2 km;revert km;refine lastCases ?_ ?_ c1 <;> refine lastCases ?_ ?_ c2
    . intro h;exact absurd rfl h
    .
     intro c0 _;simp only[Q1,lastCases_last,lastCases_castSucc,support_copy];rw[dL];intro z k3 jn
     have kc:z∈q0.support:=by simpa [w8,q0s] using pTf k3
     exact (pS (q0w q0
       (rS ⟨sS (by obtain ⟨i,_,jl⟩:=mB.mp (pS k5).1;exact (h0 i).1 jl),
        (pS k5).2⟩) z kc)).2
       (mUr _ (mB.mpr ⟨c0,mUv c0,jn⟩))
    .
     intro c0 _;simp only[Q1,lastCases_last,lastCases_castSucc,support_copy];rw[dR];intro z k3 jn
     have kc:z∈q0.support:=by simpa [w8,q0s] using pTf k3
     exact (pS (q0w q0
       (rS ⟨sS (by obtain ⟨i,_,jl⟩:=mB.mp (pS k5).1;exact (h0 i).1 jl),
        (pS k5).2⟩) z kc)).2
       (mUr _ (mB.mpr ⟨c0,mUv c0,jn⟩))
    . intro c1' c2' hne';simp only[Q1,lastCases_castSucc,support_copy];exact jb _ _ (by intro h;apply hne';rw[h])
 obtain ⟨jk,kl,Q,jp,kf,jg,k8,jb⟩:=w1 h6.card le_rfl
 have ke:∃ i'∈J,N<=#(univ.filter (λ c:Fin h6.card=>jk c∈F i')):=by
  by_contra w0;push Not at w0
  have wg:(univ:FS (Fin h6.card))=J.biUnion (λ i=>univ.filter (λ c=>jk c∈F i)):=by
   ext c;simp only[mUv,mB,mF,true_and,true_iff]
   exact mB.mp (jp c)
  have j8:h6.card < ∑ _i∈J,N:=by
   have h1:h6.card<=∑ i∈J,#(univ.filter (λ c:Fin h6.card=>jk c∈F i)):=by
    have:=cBu (s:=J) (t:=λ i=>univ.filter (λ c:Fin h6.card=>jk c∈F i))
    rw[<- wg] at this;simpa using this
   have h2:∑ i∈J,#(univ.filter (λ c:Fin h6.card=>jk c∈F i)) < ∑ _i∈J,N :=
    Finset.sum_lt_sum_of_nonempty (card_pos.mp (by omega)) (λ i hi=>w0 i hi)
   omega
  simp only[sum_const,smul_eq_mul] at j8;rw[j0,mul_comm] at j8;omega
 obtain ⟨i',j7,kz⟩:=ke;obtain ⟨Csub,w5,kj⟩:=exists_subset_card_eq kz;let eC:Fin N ≃ Csub:=(Fintype.equivFinOfCardEq (by simp [kj])).symm;let cj:Fin N->Fin h6.card:=λ j=>(eC j).1
 have jd:Injective cj:=λ j1 j2 h=>eC.injective (Subtype.ext h)
 have h4:∀ j,jk (cj j)∈F i':=λ j=>(pF (w5 (eC j).2)).2
 have jv:∀ j:Fin N,∃ p:(q3 H (S \ A)).Walk (v i') (kl (cj j)),
   p.IsPath/\p.length<=2*m/\p.support.toFinset⊆F i'∪(Q (cj j)).support.toFinset:=by
  intro j;obtain ⟨p1,js,hp1_len⟩:=q0C (h0 i') (h4 j)
  have kd:∀ w∈p1.support,w∈S \ A:=λ w hw =>
   (h0 i').1 (q0w p1 (h0 i').2.1 w hw)
  have w3:∀ w∈(Q (cj j)).support,w∈S \ A:=λ w hw=>by
   have h1:=q0w (Q (cj j))
    (rS ⟨sS ((h0 i').1 (h4 j)),
     λ h=>pD (h5 i' j7) h (h4 j)⟩) w hw
   exact rS ⟨(pS h1).1,λ hA=>(pS h1).2 (mUl _ hA)⟩
  let p:=(q0r p1 kd).append (q0r (Q (cj j)) w3);refine ⟨p,?_,?_,?_⟩
  . apply q0x _ _ (q0v _ _ js) (q0v _ _ (jg (cj j)).1);intro w wm wl;rw[q0s] at wm wl;exact k8 (cj j) w wl (mB.mpr ⟨i',j7,q0w p1 (h0 i').2.1 w wm⟩)
  .
   dsimp only[p];rw[wLa,q0t,q0t]
   have:=(jg (cj j)).2;omega
  .
   intro w hw;dsimp only[p] at hw;rw[mT,wSa,q0s,q0s] at hw
   rcases hw with h1 | h2
   . exact mUl _ (q0w p1 (h0 i').2.1 w h1)
   . exact mUr _ (rT h2)
 choose Pnew hPn_path hPn_len hPn_sub using jv
 let h9:Fin (t+1)->Fin 4:=Fin.snoc kp i';let h7:Fin (t+1)->Fin N->Fin (100*m):=Fin.snoc jc (λ j=>(eK (cj j)).1)
 let ko:Fin (t+1)->Fin N->V:=Fin.snoc en (λ j=>kl (cj j))
 let P':∀ a:Fin (t+1),∀ j:Fin N,(q3 H (S \ A)).Walk (v (h9 a)) (ko a j) :=
  lastCases (λ j=>(Pnew j).copy (by simp [h9]) (by simp [ko]))
   (λ a0 j=>(P a0 j).copy (by simp [h9]) (by simp [ko]))
 refine ⟨h9,h7,ko,P',?_,?_,?_,?_,?_,?_,?_⟩
 .
  intro a1 a2 kn;revert kn;refine lastCases ?_ ?_ a1 <;> refine lastCases ?_ ?_ a2
  . intro _;rfl
  . intro a0 h;simp [h9] at h;exact absurd h.symm ((pF j7).2 a0)
  . intro a0 h;simp [h9] at h;exact absurd h ((pF j7).2 a0)
  . intro a1' a2' h;simp [h9] at h;exact congrArg Fin.castSucc (j6 h)
 .
  rintro ⟨a1,j1⟩ ⟨a2,j2⟩ kn;dsimp only at kn;revert kn;refine lastCases ?_ ?_ a1 <;> refine lastCases ?_ ?_ a2
  .
   intro h;simp only[h7,snoc_last] at h
   have:=jd (eK.injective (Subtype.ext h));subst this;rfl
  .
   intro a0 h;simp only[h7,snoc_last,snoc_castSucc] at h
   exact absurd (h ▸ mem_image_of_mem (λ p:Fin t × Fin N=>jc p.1 p.2) (mUv (a0,j2)))
    (pS (eK (cj j1)).2).2
  .
   intro a0 h;simp only[h7,snoc_last,snoc_castSucc] at h
   exact absurd (h.symm ▸ mem_image_of_mem (λ p:Fin t × Fin N=>jc p.1 p.2) (mUv (a0,j1)))
    (pS (eK (cj j2)).2).2
  . intro a2' a1' h;simp only[h7,snoc_castSucc] at h;have wj:(a1',j1)=(a2',j2):=jt h;simp only[Prod.mk.injEq] at wj;rw[wj.1,wj.2]
 .
  intro a j;refine lastCases ?_ ?_ a
  . simpa [h7,ko] using kf (cj j)
  . intro a0;simpa [h7,ko] using hen a0 j
 .
  intro a j;refine lastCases ?_ ?_ a
  . simp only[P',lastCases_last];exact ⟨q0p (hPn_path j) _ _,by simp [hPn_len j]⟩
  . intro a0;simp only[P',lastCases_castSucc];exact ⟨q0p (jw a0 j).1 _ _,by simp [(jw a0 j).2]⟩
 .
  intro a1 j1 a2 j2 km;revert km;refine lastCases ?_ ?_ a1 <;> refine lastCases ?_ ?_ a2
  . intro h;exact absurd rfl h
  .
   intro a0 _;simp only[P',lastCases_last,lastCases_castSucc,support_copy];rw[dL];intro z k3 jn
   rcases pU (hPn_sub j1 k3) with k0 | ks
   . exact pD (k9 a0 j2 i' (λ b _=>(pF j7).2 b)) jn k0
   .
    have jm:=q0w (Q (cj j1))
     (rS ⟨sS ((h0 i').1 (h4 j1)),
       λ h=>pD (h5 i' j7) h (h4 j1)⟩) z (pTf ks)
    exact (pS jm).2 (mUr _ (mB.mpr ⟨(a0,j2),mUv _,jn⟩))
  .
   intro a0 _;simp only[P',lastCases_last,lastCases_castSucc,support_copy];rw[dR];intro z k3 jn
   rcases pU (hPn_sub j2 k3) with k0 | ks
   . exact pD (k9 a0 j1 i' (λ b _=>(pF j7).2 b)) jn k0
   .
    have jm:=q0w (Q (cj j2))
     (rS ⟨sS ((h0 i').1 (h4 j2)),
       λ h=>pD (h5 i' j7) h (h4 j2)⟩) z (pTf ks)
    exact (pS jm).2 (mUr _ (mB.mpr ⟨(a0,j1),mUv _,jn⟩))
  . intro a1' a2' hne';simp only[P',lastCases_castSucc,support_copy];exact j4 _ j1 _ j2 (by intro h;apply hne';rw[h])
 .
  intro a j1 j2 km;refine lastCases ?_ ?_ a
  . simp only[P',lastCases_last,support_copy,h9,snoc_last];rw[dL];intro z k3 jn;obtain ⟨wb,k2⟩:=pS k3;obtain ⟨wa,k1⟩:=pS jn;have hq1:z∈(Q (cj j1)).support.toFinset:=(pU (hPn_sub j1 wb)).resolve_left k2;have hq2:z∈(Q (cj j2)).support.toFinset:=(pU (hPn_sub j2 wa)).resolve_left k1;exact pD (jb (cj j1) (cj j2) (λ h=>km (jd h))) hq1 hq2
  . intro a0;simp only[P',lastCases_castSucc,support_copy,h9,snoc_castSucc];exact j3 a0 j1 j2 km
 .
  intro a j i0 kb;revert kb;refine lastCases ?_ ?_ a
  .
   intro kb;simp only[P',lastCases_last,support_copy];rw[dL];intro z w9 k0
   have ju:i'≠i0:=by simpa [h9] using kb (Fin.last t) le_rfl
   have we:i0∈J:=rF ⟨mUv i0,λ b=>by
    simpa [h9] using kb b.castSucc (Fin.le_last _)⟩
   rcases pU (hPn_sub j w9) with hzFi' | ks
   . exact pD (jy i' i0 ju) hzFi' k0
   . have kr:=k8 (cj j) z (pTf ks) (mB.mpr ⟨i0,we,k0⟩);exact pD (jy i' i0 ju) (kr ▸ h4 j) k0
  .
   intro a0 kb;simp only[P',lastCases_castSucc,support_copy]
   exact k9 a0 j i0 (λ b hba=>by
    simpa [h9] using kb b.castSucc (Fin.castSucc_le_castSucc_iff.mpr hba))
lemma q1e {e1 e2:O} (j3:0 < e1) (kf:e1 < 1) (ke:0 < e2) (k4:e2<=1/25) : ∃ d0:ℕ,100<=d0/\∀ {V:Type*} (H:SG V) (S A:FS V) (d D m:ℕ) (v:Fin 4->V) (F:Fin 4->FS V), d0<=d->d<=#S -> qQ H S e1 (e2*(d:O)) -> (∀ u∈S,d<=dS H S u) -> (log (#S:O))^10<=(D:O)->(D:O)<=(#S:O)/(log (#S:O))^10 -> 100/e1*(log (#S:O))^3<=(m:O)->(m:O)<=3000/e1*(log (#S:O))^3 -> A⊆S->(#A:O)<=(D:O)/(log (#S:O))^3 -> (∀ i,q0z H (S \ A) (v i) D m (F i)) -> (∀ i j,i≠j->Disjoint (F i) (F j)) -> ∃ F':Fin 4->FS V, (∀ i,q0z H (S \ A) (v i) (#S/(m^2)) (3*m) (F' i)) /\ (∀ i j,i≠j->Disjoint (F' i) (F' j)):=by
 have ky:e2 < 1:=by linarith
 obtain ⟨d1,js,kx⟩:=q1b j3 kf ke k4;obtain ⟨d2,hd2_100,hnc⟩:=q0g j3 kf ke ky
 have w2:∀ᶠ x:O in atTop,
   (1000:O)<=x/\(4:O)<=log x /\
   (13:O)<=100/e1*(log x)^3 /\
   5*x/(log x)^10+e1*x/(log x)^3<=e1*x/(100*(log x)^2) /\
   (100:O)*(3000/e1*(log x)^3)*(2*(3000/e1*(log x)^3)+1)<=(log x)^7 /\
   (3000/e1*(log x)^3)^2<=(log x)^10/2 /\
   (log x)^10<=x/25:=by
  let C:=3000/e1
  filter_upwards [eGe (1000:O),
   lGe (max 4 (max (1000/e1) (max (200*C*(2*C+1)+1) (2*C^2+1)))),
   q01 (C:=25) 10 (β:=1) (by norm_num)] with x hx hl hlog10
  rw[r1] at hlog10;have hl4:4<=log x:=lT (lMl _ _) hl;have k0:1000/e1<=log x:=lT (lMl _ _) (lT (lMr _ _) hl)
  have hl_C1:200*C*(2*C+1)+1<=log x :=
   lT (lMl _ _) (lT (lMr _ _) (lT (lMr _ _) hl))
  have hl_C2:2*C^2+1<=log x :=
   lT (lMr _ _) (lT (lMr _ _) (lT (lMr _ _) hl))
  have kl:1<=log x:=by linarith
  have hC1:1<=C:=by dsimp only[C];rw[lDi j3];linarith
  refine ⟨hx,hl4,?_,?_,?_,?_,by linarith⟩
  .
   have h100:100<=100/e1:=by rw[lDi j3];linarith
   have h3:(1:O)<=(log x)^3:=oLp kl;nlinarith
  .
   have h1:5*x/(log x)^10<=e1*x/(200*(log x)^2):=by
    rw[div_le_div_iff₀ (by positivity) (by positivity)]
    have h1000:1000<=e1*log x:=by
     have:=mlL k0 j3.le
     rwa [mul_div_cancel₀ _ j3.ne'] at this
    have h7:(log x)^1<=(log x)^7:=pLr kl (by omega);rw[pow_one] at h7
    have h2:1000*(log x)^2<=e1*(log x)^10:=by
     have:(log x)^10=log x*(log x)^7*(log x)^2:=by ring
     nlinarith [show 1000<=e1*(log x*(log x)^7) by nlinarith]
    nlinarith [show 5*x*(200*(log x)^2)=x*(1000*(log x)^2) by ring,
     show e1*x*(log x)^10=x*(e1*(log x)^10) by ring]
   have h2:e1*x/(log x)^3<=e1*x/(200*(log x)^2):=by
    rw[div_le_div_iff₀ (by positivity) (by positivity)]
    have h200:200<=log x:=by linarith [show 1000<=1000/e1 by rw[lDi j3];linarith]
    exact mlL (by nlinarith [show 0<=(log x)^2 by positivity]) (by positivity)
   have h3:e1*x/(200*(log x)^2)+e1*x/(200*(log x)^2) =
     e1*x/(100*(log x)^2):=by ring
   linarith
  .
   have h1:2*(C*(log x)^3)+1<=(2*C+1)*(log x)^3:=by
    have:(1:O)<=(log x)^3:=oLp kl;nlinarith
   have h2:100*(C*(log x)^3)*(2*(C*(log x)^3)+1) <=
     (100*C*(2*C+1))*(log x)^6:=by
    have:=mlL h1 (show (0:O)<=100*(C*(log x)^3) by positivity)
    linarith [show 100*(C*(log x)^3)*((2*C+1)*(log x)^3) =
      (100*C*(2*C+1))*(log x)^6 by ring]
   have h3:(100*C*(2*C+1))*(log x)^6<=log x*(log x)^6 :=
    mlR (by linarith [show 0<=C*(2*C+1) by positivity]) (by positivity)
   linarith [show log x*(log x)^6=(log x)^7 by ring]
  .
   rw[mul_pow,<- pow_mul]
   have h1:2*C^2<=(log x)^4:=by
    calc
     2*C^2<=log x:=by linarith
     _=(log x)^1:=(pow_one _).symm
     _<=(log x)^4:=pLr kl (by omega)
   have h2:=mlR h1 (show (0:O)<=(log x)^6 by positivity);linarith [show (log x)^4*(log x)^6=(log x)^10 by ring]
 rw[eAt] at w2;obtain ⟨B0,hB0⟩:=w2
 refine ⟨max (max d1 d2) (ceil B0),lT (lT js (lMl _ _)) (lMl _ _),
  λ{V} H S A d D m v F hd hdn hexp hmindeg hDlb hDub hmlb hmub hAS hAcard hFexp hFdisj=>?_⟩
 have hd1:d1<=d:=lT (lMl _ _) (lT (lMl _ _) hd);have hd2:d2<=d:=lT (lMr _ _) (lT (lMl _ _) hd)
 have hnB:B0<=(#S:O) :=
  (nLc B0).trans (by exact_mod_cast ((lMr _ _).trans hd).trans hdn)
 obtain ⟨hn1000,kq,ko,hW_egg_bd,kg,jz,hlog10_n25⟩:=hB0 (#S:O) hnB;set n:O:=(#S:O);set sz:=#S/(m^2)
 have hm_ge13:13<=m:=by exact_mod_cast ko.trans hmlb
 have hm_pos:0 < m:=by omega
 have jj:2*D<=sz:=by
  have h1:(2*D:O)*((m:O)^2)<=n:=by
   have hm2:(m:O)^2<=(log n)^10/2 :=
    (pLl (nCn m) hmub 2).trans jz
   have hprod:=mLm hDub hm2 (by positivity) (by positivity)
   have w3:n/(log n)^10*((log n)^10/2)=n/2:=by field_simp
   linarith
  have hN:2*D*m^2<=#S:=by dsimp only[n] at h1;exact_mod_cast h1
  exact (Nat.le_div_iff_mul_le (by positivity)).mpr hN
 have hD_pos:1<=D:=by
  have:(1:O)<=(log n)^10:=oLp (by linarith)
  exact_mod_cast this.trans hDlb
 have jc:1<=sz:=by omega
 have j7:(sz:O)<=n/25:=by
  have h1:(sz:O)*((m:O)^2)<=n:=by dsimp only[n,sz];exact_mod_cast Nat.div_mul_le_self #S (m^2)
  have hm2_25:(25:O)<=(m:O)^2:=by
   have:(5:O)<=(m:O):=by exact_mod_cast (show 5<=m by omega)
   nlinarith
  nlinarith [show (0:O)<=(sz:O) by positivity]
 let W0:=A∪univ.biUnion F
 have hW0_card:(#W0:O)<=5*n/(log n)^10:=by
  have h1:#W0<=#A+4*D:=by
   calc
    #W0<=#A+#(univ.biUnion F):=cUl _ _
    _<=#A+∑ i:Fin 4,#(F i):=Nat.add_le_add_left cBu _
    _=#A+4*D:=by simp [λ i=>(hFexp i).2.2.1]
  have hA_le_D:(#A:O)<=(D:O):=hAcard.trans (dLs (nCn D) (oLp (by linarith)))
  have h1R:(#W0:O)<=(#A:O)+4*(D:O):=by exact_mod_cast h1
  rw[mul_div_assoc];linarith
 have kj:∃ (cB:Fin (100*m)->V) (B:Fin (100*m)->FS V),
   (∀ k,q0z H (S \ W0) (cB k) sz (floor (40/e1*(log n)^3)) (B k)) /\
   (∀ k1 k2,k1≠k2->Disjoint (B k1) (B k2)):=by
  suffices h:∀ t (ht:t<=100*m),∃ (cB:Fin t->V) (B:Fin t->FS V),
    (∀ k,q0z H (S \ W0) (cB k) sz (floor (40/e1*(log n)^3)) (B k)) /\
    (∀ k1 k2,k1≠k2->Disjoint (B k1) (B k2)) by
   exact h (100*m) le_rfl
  intro t
  induction t with
  | zero=>intro _;exact ⟨Fin.elim0,Fin.elim0,λ k=>k.elim0,λ k=>k.elim0⟩
  | succ t ih =>
   intro ht;obtain ⟨cB,B,w1,ka⟩:=ih (by omega);let Wt:=W0∪univ.biUnion B
   have ju:Wt⊆S:=uS
    (uS hAS (biUnion_subset.mpr λ i _=>(hFexp i).1.trans sS))
    (biUnion_subset.mpr λ k _=>(w1 k).1.trans sS)
   have jn:(#Wt:O)<=e1*n/(100*(log n)^2):=by
    have h1:#(univ.biUnion B)<=100*m*sz:=by
     calc
      _<=∑ k:Fin t,#(B k):=cBu
      _=t*sz:=by simp [λ k=>(w1 k).2.2.1]
      _<=100*m*sz:=nMr sz (by omega)
    have h2:((100*m*sz:ℕ):O)<=e1*n/(log n)^3:=by
     have j8:(sz:O)<=n/((m:O)^2):=by
      rw[lDi (by positivity)];dsimp only[n,sz];exact_mod_cast Nat.div_mul_le_self #S (m^2)
     have h3:(100:O)*(m:O)*(sz:O)<=100*n/(m:O):=by
      have:=mlL j8 (show (0:O)<=100*(m:O) by positivity)
      have w3:100*(m:O)*(n/(m:O)^2)=100*n/(m:O):=by field_simp
      linarith
     have h4:100*n/(m:O)<=e1*n/(log n)^3:=by
      rw[div_le_div_iff₀ (by positivity) (by positivity)];have hmul:=mlL hmlb (show (0:O)<=e1*n by positivity)
      have w3:e1*n*(100/e1*(log n)^3)=100*n*(log n)^3:=by field_simp
      linarith
     push_cast;linarith
    have h3:(#Wt:O)<=(#W0:O)+(#(univ.biUnion B):O):=by
     exact_mod_cast cUl W0 (univ.biUnion B)
    have h4:(#(univ.biUnion B):O)<=((100*m*sz:ℕ):O):=by exact_mod_cast h1
    linarith
   obtain ⟨v0,B0,jg,jp,jw⟩:=kx H S Wt d hd1 hdn hexp ju jn
   have ji:sz<=#B0:=by exact_mod_cast j7.trans jp
   obtain ⟨Bk,je,jv⟩:=q0E jw jc ji;have jo:S \ Wt⊆S \ W0:=sSs sR sUl;refine ⟨Fin.snoc cB v0,Fin.snoc B Bk,?_,?_⟩
   .
    intro k;refine lastCases ?_ ?_ k
    . simpa using q0A jv jo
    . intro j;simpa using w1 j
   .
    intro k1 k2 kn;revert kn;refine lastCases ?_ ?_ k1 <;> refine lastCases ?_ ?_ k2
    . intro h;exact absurd rfl h
    .
     intro j _;simp only[snoc_last,snoc_castSucc]
     exact rD λ z hz1 hz2 =>
      (pS (jg (je hz1))).2 (mUr _ (mB.mpr ⟨j,mUv j,hz2⟩))
    .
     intro j _;simp only[snoc_last,snoc_castSucc]
     exact dR.mpr λ z hz1 hz2 =>
      (pS (jg (je hz1))).2 (mUr _ (mB.mpr ⟨j,mUv j,hz2⟩))
    . intro j1 j2 jy;simp only[snoc_castSucc];exact ka _ _ (by intro h;apply jy;rw[h])
 obtain ⟨cB,B,j0,jf⟩:=kj
 have j5:∀ k,∀ u∈B k,B k⊆qs H (B k) m {u}:=λ k u hu=>by
  have h1:=q11 (j0 k) hu
  have h2:2*floor (40/e1*(log n)^3)<=m:=by
   have hf:(floor (40/e1*(log n)^3):O)<=40/e1*(log n)^3:=nFl (by positivity)
   have hnn:0<=(log n)^3/e1:=by positivity
   have:(2*floor (40/e1*(log n)^3):O)<=(m:O):=by
    push_cast
    linarith only[hf,hmlb,hnn,
     show 2*(40/e1*(log n)^3)=80*((log n)^3/e1) by ring,
     show 100/e1*(log n)^3=100*((log n)^3/e1) by ring]
   exact_mod_cast this
  exact h1.trans (qu H (B k) h2 {u})
 let N:=25*m
 have h5:∀ t < 4,q1c H S A m v F B t->q1c H S A m v F B (t+1) :=
  λ t ht hG=>q1d j3 H S A D m sz v F cB B hAS kq hDlb hmlb hmub kg hAcard jj hFexp hFdisj j0
   (λ A_nc B_nc Wq x=>hnc H S A_nc B_nc Wq d x hd2 hdn hexp (λ u hu=>Nat.le_trans (nSl d 1) (hmindeg u hu))) t ht hG
 have k8:q1c H S A m v F B 0:=⟨Fin.elim0,Fin.elim0,Fin.elim0,λ a=>a.elim0,
  λ a=>a.elim0,λ p=>p.1.elim0,λ a=>a.elim0,λ a=>a.elim0,
  λ a=>a.elim0,λ a=>a.elim0,λ a=>a.elim0⟩
 have k7:q1c H S A m v F B 4 :=
  h5 3 (by omega) (h5 2 (by omega) (h5 1 (by omega) (h5 0 (by omega) k8)))
 obtain ⟨kb,h0,en,P,jl,jm,w4,jx,h9,_,_⟩:=k7
 let jr:Fin 4->Fin 4->FS (Fin 4->Fin N):=λ a b =>
  univ.filter (λ f=>¬ Disjoint (P a (f a)).support.toFinset (B (h0 b (f b))))
 have jk:∀ a b:Fin 4,a≠b->#(jr a b)<=(2*m+1)*N^3:=by
  intro a b jt;let j6:(Fin 4->Fin N)->({c:Fin 4 // c≠b}->Fin N):=λ f c=>f c.1
  have kt:∀ g:{c:Fin 4 // c≠b}->Fin N,
    #((jr a b).filter (λ f=>j6 f=g))<=2*m+1:=by
   intro g;let ja:=g ⟨a,jt⟩
   have j9:#(univ.filter (λ jb:Fin N=>¬ Disjoint (P a ja).support.toFinset (B (h0 b jb)))) <=
     (P a ja).support.toFinset.card:=by
    let jq:=univ.filter (λ jb:Fin N=>¬ Disjoint (P a ja).support.toFinset (B (h0 b jb)))
    have kd:∀ jb∈jq,∃ z∈(P a ja).support.toFinset,z∈B (h0 b jb):=λ jb kr =>
     Finset.not_disjoint_iff.mp (pF kr).2
    choose wit hwitP hwitB using kd
    have k5:jq.card=#(jq.attach.image (λ x=>wit x.1 x.2)) :=
     (Finset.card_attach (s:=jq)).symm.trans
      (card_image_of_injective jq.attach (λ x y hxy=>by
       by_contra kn;have jy:x.1≠y.1:=λ h=>kn (Subtype.ext h)
       have kc:h0 b x.1≠h0 b y.1:=λ h=>jy (by
        have w0:(b,x.1)=(b,y.1):=jm h;exact (Prod.mk.inj w0).2)
       exact pD (jf _ _ kc) (hwitB x.1 x.2) (hxy ▸ hwitB y.1 y.2))).symm
    rw[k5];exact cL (image_subset_iff.mpr λ x _=>hwitP x.1 x.2)
   have ks:∀ f1∈(jr a b).filter (λ f=>j6 f=g),
     ∀ f2∈(jr a b).filter (λ f=>j6 f=g),f1 b=f2 b->f1=f2:=by
    intro f1 kv f2 ku kw
    funext c;by_cases kz:c=b
    . exact kz ▸ kw
    . exact (congrFun (pF kv).2 ⟨c,kz⟩).trans (congrFun (pF ku).2 ⟨c,kz⟩).symm
   calc
    #((jr a b).filter (λ f=>j6 f=g))
     = #(((jr a b).filter (λ f=>j6 f=g)).image (λ f=>f b)) :=
      (Finset.card_image_of_injOn (λ f1 kv f2 ku h=>ks f1 kv f2 ku h)).symm
    _<=#(univ.filter (λ jb:Fin N=>¬ Disjoint (P a ja).support.toFinset (B (h0 b jb)))):=by
      apply cL;intro jb kr;obtain ⟨f,hf,rfl⟩:=mem_image.mp kr;obtain ⟨hfB,hfg⟩:=pF hf;have hfa:f a=ja:=congrFun hfg ⟨a,jt⟩;exact rF ⟨mUv _,hfa ▸ (pF hfB).2⟩
    _<=(P a ja).support.toFinset.card:=j9
    _<=2*m+1:=(q0y (P a ja)).trans (Nat.add_le_add_right (jx a ja).2 1)
  have km:=Finset.card_eq_sum_card_fiberwise (f:=j6) (s:=jr a b) (t:=univ) (λ _ _=>mUv _)
  calc
   #(jr a b)=∑ g:{c:Fin 4 // c≠b}->Fin N,#((jr a b).filter (λ f=>j6 f=g)):=km
   _<=∑ _g:{c:Fin 4 // c≠b}->Fin N,(2*m+1):=sum_le_sum λ g _=>kt g
   _=(2*m+1)*N^3:=by
    simp only[sum_const,card_univ,Fintype.card_pi,Fintype.card_fin,Finset.prod_const]
    have h3:Fintype.card {c:Fin 4 // c≠b}=3:=by fin_cases b <;> decide
    rw[h3,smul_eq_mul,mul_comm]
 let jh:=(univ:FS (Fin 4 × Fin 4)).filter (λ p=>p.1≠p.2)
 have j4:jh.card=12:=by decide
 let h8:=jh.biUnion (λ p=>jr p.1 p.2)
 have hAllBad_lt:h8.card < #(univ:FS (Fin 4->Fin N)):=by
  have h1:h8.card<=12*((2*m+1)*N^3):=by
   calc
    h8.card<=∑ p∈jh,#(jr p.1 p.2):=cBu
    _<=∑ _p∈jh,((2*m+1)*N^3):=sum_le_sum λ p hp=>jk p.1 p.2 (pF hp).2
    _=12*((2*m+1)*N^3):=by simp [j4]
  have h2:#(univ:FS (Fin 4->Fin N))=N^4:=by simp
  rw[h2]
  have k6:0 < N^3:=by dsimp only[N];positivity
  have kp:12*(2*m+1) < N:=by dsimp only[N];omega
  calc
   h8.card<=(12*(2*m+1))*N^3:=by linarith
   _ < N*N^3:=Nat.mul_lt_mul_of_pos_right kp k6
   _=N^4:=by ring
 obtain ⟨f,hf⟩:=card_pos.mp (show 0 < #((univ:FS (Fin 4->Fin N)) \ h8) by
  rw[card_sdiff_of_subset (Finset.subset_univ _)];omega)
 have jd:∀ a b:Fin 4,a≠b->Disjoint (P a (f a)).support.toFinset (B (h0 b (f b))):=by
  intro a b jt;by_contra hnd
  exact (pS hf).2 (mB.mpr ⟨(a,b),
   rF ⟨mUv _,jt⟩,rF ⟨mUv _,hnd⟩⟩)
 let h6:Fin 4 ≃ Fin 4:=Equiv.ofBijective kb (Finite.injective_iff_bijective.mp jl)
 have k9:∀ a:Fin 4,∃ E⊆(P a (f a)).support.toFinset∪B (h0 a (f a)),
   q0z H (S \ A) (v (kb a)) sz (3*m) E:=by
  intro a
  have kk:B (h0 a (f a))⊆S \ A :=
   (j0 (h0 a (f a))).1.trans (sSs sR sUl)
  have k3:=q0F (P a (f a)) ((hFexp (kb a)).1 (hFexp (kb a)).2.1)
   (jx a (f a)).2 kk (w4 a (f a)) (j5 (h0 a (f a)) (en a (f a)) (w4 a (f a)))
  have j8:sz<=#((P a (f a)).support.toFinset∪B (h0 a (f a))):=by
   rw[<- (j0 (h0 a (f a))).2.2.1];exact cL sUr
  obtain ⟨E,kh,ki⟩:=q0E k3 jc j8;exact ⟨E,kh,q0B ki (by omega)⟩
 choose F_ord hFord_sub hFord_exp using k9
 refine ⟨λ i=>F_ord (h6.symm i),?_,?_⟩
 .
  intro i;have h1:=hFord_exp (h6.symm i);have h2:kb (h6.symm i)=i:=h6.apply_symm_apply i
  rwa [h2] at h1
 .
  intro i j hij;have jt:h6.symm i≠h6.symm j:=λ h=>hij (h6.symm.injective h)
  refine Disjoint.mono (hFord_sub (h6.symm i)) (hFord_sub (h6.symm j)) ?_
  refine disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨h9 _ _ _ _ jt,jd _ _ jt⟩,
   disjoint_union_right.mpr ⟨(jd _ _ jt.symm).symm,jf _ _ (λ h=>jt (by
    have w0:(h6.symm i,f (h6.symm i))=(h6.symm j,f (h6.symm j)):=jm h
    exact (Prod.mk.inj w0).1))⟩⟩
lemma q1f {e1 e2:O} (kh:0 < e1) (wc:e1 < 1) (wb:0 < e2) (w1:e2<=1/25) : ∃ d0:ℕ,100<=d0/\∀ {V:Type*} (H:SG V) (S W F1 F2:FS V) (d D m l:ℕ) (v1 v2:V), d0<=d->d<=#S -> qQ H S e1 (e2*(d:O)) -> (∀ u∈S,d<=dS H S u) -> (log (#S:O))^7<=(D:O)->(D:O)<=(#S:O)/(log (#S:O))^4 -> 100/e1*(log (#S:O))^3<=(m:O)->(m:O)<=3000/e1*(log (#S:O))^3 -> W⊆S->(#W:O)<=(D:O)/(log (#S:O))^3 -> q0z H (S \ W) v1 D m F1->q0z H (S \ W) v2 D m F2 -> Disjoint F1 F2 -> (l:O)<=(D:O)/(log (#S:O))^3 -> ∃ p:(q3 H (S \ W)).Walk v1 v2,p.IsPath/\l<=p.length/\p.length<=l+5*m:=by
 have wr:e2 < 1:=by linarith
 obtain ⟨d1,ki,wq⟩:=q1b kh wc wb w1;obtain ⟨d2,hd2_100,wy⟩:=q0g kh wc wb wr
 have z0:∀ᶠ x:O in atTop,
   (1000:O)<=x/\(4:O)<=log x /\
   5*(x/(log x)^4)+2<=e1*x/(100*(log x)^2) /\
   2*(3000/e1*(log x)^3)+2<=(log x)^4 /\
   (log x)^4>=25:=by
  filter_upwards [eGe (1000:O),
   lGe (max 4 (max (1000/e1) (6000/e1+2))),
   q01 (C:=2) 4 (β:=1) (by norm_num)] with x hx hl hlog4
  rw[r1] at hlog4;have wj:4<=log x:=lT (lMl _ _) hl;have w0:1000/e1<=log x:=lT (lMl _ _) (lT (lMr _ _) hl);have kg:6000/e1+2<=log x:=lT (lMr _ _) (lT (lMr _ _) hl)
  refine ⟨hx,wj,?_,?_,by
   calc
    (25:O)<=4^4:=by norm_num
    _<=(log x)^4:=pLl (by norm_num) wj 4⟩
  .
   have wh:1000<=e1*log x:=by
    have:=mlL w0 kh.le
    rwa [mul_div_cancel₀ _ kh.ne'] at this
   have h1:6*(x/(log x)^4)<=e1*x/(100*(log x)^2):=by
    rw[show 6*(x/(log x)^4)=6*x/(log x)^4 by ring];rw[div_le_div_iff₀ (by positivity) (by positivity)]
    have h2:600<=e1*(log x)^2:=by
      have hm:=mlR wh (by linarith only[wj]:(0:O)<=log x);nlinarith only[wj,hm,show e1*log x*log x=e1*(log x)^2 by ring]
    have hm:=mlL h2 (show (0:O)<=x*(log x)^2 by positivity)
    linarith only[hm,show 6*x*(100*(log x)^2)=x*(log x)^2*600 by ring,
      show e1*x*(log x)^4=x*(log x)^2*(e1*(log x)^2) by ring]
   have h2:(2:O)<=x/(log x)^4:=by
    rw[lDi (by positivity)];linarith
   linarith
  .
   have h1:(1:O)<=(log x)^3:=oLp (by linarith)
   have h2:2*(3000/e1*(log x)^3)+2<=(6000/e1+2)*(log x)^3:=by
    linarith only[h1,
      show 2*(3000/e1*(log x)^3)=6000/e1*(log x)^3 by ring,
      show (6000/e1+2)*(log x)^3=6000/e1*(log x)^3+2*(log x)^3 by ring]
   have h3:=mlR kg (show (0:O)<=(log x)^3 by positivity);linarith only[h2,h3,show log x*(log x)^3=(log x)^4 by ring]
 rw[eAt] at z0;obtain ⟨B0,hB0⟩:=z0
 refine ⟨max (max d1 d2) (ceil B0),lT (lT ki (lMl _ _)) (lMl _ _),
  λ{V} H S W F1 F2 d D m l v1 v2 hd hdn hexp hmindeg hDlb hDub hmlb hmub hWS hWcard hF1 hF2 hFdisj hlub=>?_⟩
 have hd1:d1<=d:=lT (lMl _ _) (lT (lMl _ _) hd);have z1:d2<=d:=lT (lMr _ _) (lT (lMl _ _) hd)
 have hnB:B0<=(#S:O) :=
  (nLc B0).trans (by exact_mod_cast ((lMr _ _).trans hd).trans hdn)
 obtain ⟨hn1000,w9,k5,w6,kf⟩:=hB0 (#S:O) hnB;set n:O:=(#S:O)
 have jj:1<=D:=by
  have:(1:O)<=(log n)^7:=oLp (by linarith)
  exact_mod_cast this.trans hDlb
 let km:ℕ->Prop:=λ L=>∃ (v3 v4:V) (F3 F4:FS V)
   (p1:(q3 H (S \ W)).Walk v1 v3) (p2:(q3 H (S \ W)).Walk v2 v4),
   p1.IsPath/\p2.IsPath/\p1.length+p2.length=L/\L<=l+2*m /\
   q0z H (S \ W) v3 D m F3/\q0z H (S \ W) v4 D m F4 /\
   (∀ w∈p1.support,w∈F3->w=v3)/\(∀ w∈p2.support,w∈F4->w=v4) /\
   Disjoint (p1.support.toFinset∪F3) (p2.support.toFinset∪F4)
 have w4:km 0:=⟨v1,v2,F1,F2,.nil,.nil,Walk.IsPath.nil,Walk.IsPath.nil,rfl,Nat.zero_le _,
  hF1,hF2,λ w hw _=>by simpa using hw,λ w hw _=>by simpa using hw,
  by
   have h1:(Walk.nil (u:=v1) (G:=q3 H (S \ W))).support.toFinset∪F1=F1:=by
    ext z;simp only[support_nil,List.toFinset_cons,List.toFinset_nil,
      mU,mem_insert,Finset.notMem_empty,or_false,or_iff_right_iff_imp];rintro rfl;exact hF1.2.1
   have h2:(Walk.nil (u:=v2) (G:=q3 H (S \ W))).support.toFinset∪F2=F2:=by
    ext z;simp only[support_nil,List.toFinset_cons,List.toFinset_nil,
      mU,mem_insert,Finset.notMem_empty,or_false,or_iff_right_iff_imp];rintro rfl;exact hF2.2.1
   rw[h1,h2];exact hFdisj⟩
 let Ls:=(range (l+2*m+1)).filter km;have k6:Ls.Nonempty:=⟨0,rF ⟨mem_range.mpr (by omega),w4⟩⟩;let L:=Ls.max' k6
 obtain ⟨v3,v4,F3,F4,p1,p2,wo,wn,hL_eq,wf,h9,j2,jm,jl,h6⟩ :=
  (pF (max'_mem Ls k6)).2
 have h2m_le_D:(2*m+2:O)<=(D:O)/(log n)^3:=by
  have h1:(2*m+2:O)<=(log n)^4:=by
   have:2*(m:O)+2<=2*(3000/e1*(log n)^3)+2:=by linarith
   exact this.trans w6
  have h2:(log n)^4<=(D:O)/(log n)^3:=by
   rw[lDi (by positivity)];linarith [show (log n)^4*(log n)^3=(log n)^7 by ring]
  exact h1.trans h2
 have jn:(#(W∪(p1.support.toFinset \ {v3})∪(p2.support.toFinset \ {v4})):O)*(log n)^3 <=
   10*(D:O):=by
  have h1:#(W∪(p1.support.toFinset \ {v3})∪(p2.support.toFinset \ {v4}))<=#W+L+2:=by
   have h2:=cUl (W∪(p1.support.toFinset \ {v3})) (p2.support.toFinset \ {v4});have h3:=cUl W (p1.support.toFinset \ {v3})
   have hp1c:#(p1.support.toFinset \ {v3})<=p1.length+1 :=
    (cL sS).trans (q0y p1)
   have hp2c:#(p2.support.toFinset \ {v4})<=p2.length+1 :=
    (cL sS).trans (q0y p2)
   omega
  have wv:(#(W∪(p1.support.toFinset \ {v3})∪(p2.support.toFinset \ {v4})):O) <=
    (#W:O)+(l:O)+2*(m:O)+2:=by
   have hLR:(L:O)<=(l:O)+2*(m:O):=by exact_mod_cast wf
   have:(#(W∪(p1.support.toFinset \ {v3})∪(p2.support.toFinset \ {v4})):O)<=(#W:O)+(L:O)+2:=by
    exact_mod_cast h1
   linarith
  have wm:(#W:O)+(l:O)+2*(m:O)+2<=3*((D:O)/(log n)^3):=by linarith
  have wp:=mlR (wv.trans wm) (show (0:O)<=(log n)^3 by positivity)
  have heq:3*((D:O)/(log n)^3)*(log n)^3=3*(D:O):=by
   rw[mul_assoc,div_mul_cancel₀ _ (by positivity)]
  linarith only[wp,heq,show (0:O)<=(D:O) from nCn D]
 let wi:=W∪(p1.support.toFinset \ {v3})∪(p2.support.toFinset \ {v4})
 have j5:wi⊆S:=uS (uS hWS
  (sS.trans λ z hz=>sS (q0w p1 (hF1.1 hF1.2.1) z (pTf hz))))
  (sS.trans λ z hz=>sS (q0w p2 (hF2.1 hF2.2.1) z (pTf hz)))
 have h0:Disjoint wi (F3∪F4):=by
  rw[dL];intro z wk wl
  rcases pU wk with h1 | k8
  .
   rcases pU h1 with hzW' | k9
   .
    rcases pU wl with h3 | h4
    . exact (pS (h9.1 h3)).2 hzW'
    . exact (pS (j2.1 h4)).2 hzW'
   .
    obtain ⟨jq,ks⟩:=pS k9
    rcases pU wl with h3 | h4
    . exact ks (mSg.mpr (jm z (pTf jq) h3))
    . exact pD h6 (mUl _ jq) (mUr _ h4)
  .
   obtain ⟨jb,ks⟩:=pS k8
   rcases pU wl with h3 | h4
   . exact pD h6 (mUr _ h3) (mUl _ jb)
   . exact ks (mSg.mpr (jl z (pTf jb) h4))
 have hl_le_L:l<=L:=by
  by_contra wz;push Not at wz;let jg:=W∪F3∪F4∪p1.support.toFinset∪p2.support.toFinset
  have ju:jg⊆S:=uS (uS (uS (uS hWS
   (h9.1.trans sS)) (j2.1.trans sS))
   (λ z hz=>sS (q0w p1 (hF1.1 hF1.2.1) z (pTf hz))))
   (λ z hz=>sS (q0w p2 (hF2.1 hF2.2.1) z (pTf hz)))
  have jh:(jg.card:O)<=e1*n/(100*(log n)^2):=by
   have h1:jg.card<=#W+D+D+(p1.length+1)+(p2.length+1):=by
    have:=cUl (W∪F3∪F4∪p1.support.toFinset) p2.support.toFinset
    have:=cUl (W∪F3∪F4) p1.support.toFinset
    have:=cUl (W∪F3) F4
    have:=cUl W F3
    have:=q0y p1;have:=q0y p2
    dsimp only[jg];rw[h9.2.2.1,j2.2.2.1] at *;omega
   have wv:(jg.card:O)<=(#W:O)+2*(D:O)+(l:O)+2:=by
    have h1':(jg.card:O)<=(#W:O)+(D:O)+(D:O)+((L:O)+2):=by
      have:jg.card<=#W+D+D+(L+2):=by omega
      exact_mod_cast this
    have hLl:(L:O)<=(l:O):=by exact_mod_cast wz.le
    linarith only[h1',hLl]
   have wd:(#W:O)<=(D:O):=hWcard.trans (dLs (nCn D) (oLp (by linarith only[w9])));have wa:(l:O)<=(D:O):=hlub.trans (dLs (nCn D) (oLp (by linarith only[w9])));linarith only[wv,wd,wa,hDub,k5]
  obtain ⟨b0,B,h5,hB_card,w5⟩:=wq H S jg d hd1 hdn hexp ju jh
  have jo:(D:O)<=(#B:O):=by
   have h1:n/(log n)^4<=n/25:=dLl (by linarith) (by norm_num) kf;linarith
  have jx:(D:O)<=(#(F3∪F4):O):=by
   have:D<=#(F3∪F4):=h9.2.2.1 ▸ cL sUl
   exact_mod_cast this
  have jd:Disjoint wi B:=by
   rw[dL];intro z wk kv;have jz:=(pS (h5 kv)).2
   rcases pU wk with h1 | k8
   .
    rcases pU h1 with hzW' | k9
    . exact jz (mUl _ (mUl _ (mUl _ (mUl _ hzW'))))
    . exact jz (mUl _ (mUr _ (pS k9).1))
   . exact jz (mUr _ (pS k8).1)
  obtain ⟨a,b,ko,ws,q',jc,ke,j8,kn⟩ :=
   wy H S (F3∪F4) B wi d (D:O) z1 hdn hexp (λ u hu=>Nat.le_trans (nSl d 1) (hmindeg u hu))
    (uS (h9.1.trans sS) (j2.1.trans sS))
    (h5.trans sS)
    (λ z hz=>rS ⟨j5 hz,λ h=>by
      rcases pU h with h1 | h2
      . exact pD h0 hz h1
      . exact pD jd hz h2⟩)
    (by exact_mod_cast jj) jx jo jn
  have hq'_pos:1<=q'.length:=by
   cases q' with
   | nil =>
    exfalso;have:=(pS (h5 ws)).2
    rcases pU ko with h3 | h4
    . exact this (mUl _ (mUl _ (mUl _ (mUr _ h3))))
    . exact this (mUl _ (mUl _ (mUr _ h4)))
   | cons _ _=>simp
  have hq'_len_m:q'.length<=m:=by
   have w8:0<=(log n)^3/e1:=by positivity
   exact_mod_cast (show (q'.length:O)<=(m:O) by
    linarith only[ke,hmlb,w8,
      show 40/e1*(log n)^3=40*((log n)^3/e1) by ring,
      show 100/e1*(log n)^3=100*((log n)^3/e1) by ring])
  have jf:B⊆qs H B m {b}:=by
   have h1:=q11 w5 ws
   have h2:2*floor (40/e1*(log n)^3)<=m:=by
    have hf:(floor (40/e1*(log n)^3):O)<=40/e1*(log n)^3:=nFl (by positivity)
    have w8:0<=(log n)^3/e1:=by positivity
    exact_mod_cast (show (2*floor (40/e1*(log n)^3):O)<=(m:O) by
      push_cast
      linarith only[hf,hmlb,w8,
       show 2*(40/e1*(log n)^3)=80*((log n)^3/e1) by ring,
       show 100/e1*(log n)^3=100*((log n)^3/e1) by ring])
   exact h1.trans (qu H B h2 {b})
  have wg:B⊆S \ W:=h5.trans (sSs sR
   (sUl.trans (sUl.trans (sUl.trans sUl))))
  obtain ⟨F_new,h7,j9⟩ :=
   q0E (show q0z H (S \ W) b #B m B from ⟨wg,ws,rfl,jf⟩) jj (by exact_mod_cast jo)
  have k4:∀ w∈q'.support,w∈S \ W:=λ w hw=>by
   have h1:=q0w q' (rS
    ⟨sS (by rcases pU ko with h3 | h4;exact h9.1 h3;exact j2.1 h4),
     λ h=>pD h0 h ko⟩) w hw
   exact rS ⟨(pS h1).1,λ hW=>(pS h1).2 (mUl _ (mUl _ hW))⟩
  have j4:∀ w∈q'.support,w∈p1.support->w=v3:=λ w hw hwp1=>by
   by_contra kz
   have h1:=q0w q' (rS
    ⟨sS (by rcases pU ko with h3 | h4;exact h9.1 h3;exact j2.1 h4),
     λ h=>pD h0 h ko⟩) w hw
   exact (pS h1).2 (mUl _ (mUr _
    (rS ⟨rT hwp1,λ h=>kz (pSg h)⟩)))
  have j3:∀ w∈q'.support,w∈p2.support->w=v4:=λ w hw hwp2=>by
   by_contra kz
   have h1:=q0w q' (rS
    ⟨sS (by rcases pU ko with h3 | h4;exact h9.1 h3;exact j2.1 h4),
     λ h=>pD h0 h ko⟩) w hw
   exact (pS h1).2 (mUr _
    (rS ⟨rT hwp2,λ h=>kz (pSg h)⟩))
  rcases pU ko with wu | wt
  .
   obtain ⟨s1,k1,hs1_len⟩:=q0C h9 wu
   let Q:(q3 H (S \ W)).Walk v3 b :=
    (q0r s1 (λ w hw=>h9.1 (q0w s1 h9.2.1 w hw))).append (q0r q' k4)
   have ja:Q.IsPath:=by
    apply q0x _ _ (q0v _ _ k1) (q0v _ _ jc);intro w j7 j1;rw[q0s] at j7 j1;exact j8 w j1 (mUl _ (q0w s1 h9.2.1 w j7))
   have w3:1<=Q.length/\Q.length<=2*m:=by
    dsimp only[Q];rw[wLa,q0t,q0t];omega
   let wx:=p1.append Q
   have jt:wx.IsPath:=by
    apply q0x p1 Q wo ja;intro w j7 j1;dsimp only[Q] at j1;rw[wSa,q0s,q0s] at j1
    rcases j1 with h1 | h2
    . exact jm w j7 (q0w s1 h9.2.1 w h1)
    . exact j4 w h2 j7
   have j0:km (L+Q.length):=by
    refine ⟨b,v4,F_new,F4,wx,p2,jt,wn,by rw[wLa];omega,by omega,
      j9,j2,?_,jl,?_⟩
    .
      intro w hw kw;have kx:w∈B:=h7 kw;rw[wSa] at hw
      rcases hw with h1 | h2
      .
       exfalso;exact (pS (h5 kx)).2
        (mUl _ (mUr _ (rT h1)))
      .
       dsimp only[Q] at h2;rw[wSa,q0s,q0s] at h2
       rcases h2 with kl | jy
       .
        exfalso;exact (pS (h5 kx)).2 (mUl _
         (mUl _ (mUl _ (mUr _ (q0w s1 h9.2.1 w kl)))))
       . exact kn w jy kx
    .
      rw[dL];intro z k9 k8
      rcases pU k9 with hzp1' | ku
      .
       rw[mT,wSa] at hzp1'
       rcases hzp1' with h1 | h2
       . exact pD h6 (mUl _ (rT h1)) k8
       .
        dsimp only[Q] at h2;rw[wSa,q0s,q0s] at h2
        rcases h2 with kl | jy
        . exact pD h6 (mUr _ (q0w s1 h9.2.1 z kl)) k8
        .
         rcases pU k8 with jb | jr
         . have ka:=j3 z jy (pTf jb);have kt:=j8 z jy (mUr _ (ka ▸ j2.2.1));exact pD h6 (mUr _ (kt ▸ wu)) (mUr _ (ka ▸ j2.2.1))
         . have kt:=j8 z jy (mUr _ jr);exact pD h6 (mUr _ (kt ▸ wu)) (mUr _ jr)
      .
       have kv:=h7 ku
       rcases pU k8 with jb | jr
       . exact (pS (h5 kv)).2 (mUr _ jb)
       . exact (pS (h5 kv)).2 (mUl _ (mUl _ (mUr _ jr)))
   have:=le_max' Ls (L+Q.length) (rF ⟨mem_range.mpr (by omega),j0⟩)
   omega
  .
   obtain ⟨s2,k0,hs2_len⟩:=q0C j2 wt
   let Q:(q3 H (S \ W)).Walk v4 b :=
    (q0r s2 (λ w hw=>j2.1 (q0w s2 j2.2.1 w hw))).append (q0r q' k4)
   have ja:Q.IsPath:=by
    apply q0x _ _ (q0v _ _ k0) (q0v _ _ jc);intro w j7 j1;rw[q0s] at j7 j1;exact j8 w j1 (mUr _ (q0w s2 j2.2.1 w j7))
   have w3:1<=Q.length/\Q.length<=2*m:=by
    dsimp only[Q];rw[wLa,q0t,q0t];omega
   let ww:=p2.append Q
   have js:ww.IsPath:=by
    apply q0x p2 Q wn ja;intro w j7 j1;dsimp only[Q] at j1;rw[wSa,q0s,q0s] at j1
    rcases j1 with h1 | h2
    . exact jl w j7 (q0w s2 j2.2.1 w h1)
    . exact j3 w h2 j7
   have j0:km (L+Q.length):=by
    refine ⟨v3,b,F3,F_new,p1,ww,wo,js,by rw[wLa];omega,by omega,
      h9,j9,jm,?_,?_⟩
    .
      intro w hw kw;have kx:w∈B:=h7 kw;rw[wSa] at hw
      rcases hw with h1 | h2
      . exfalso;exact (pS (h5 kx)).2 (mUr _ (rT h1))
      .
       dsimp only[Q] at h2;rw[wSa,q0s,q0s] at h2
       rcases h2 with kl | jy
       .
        exfalso;exact (pS (h5 kx)).2 (mUl _
         (mUl _ (mUr _ (q0w s2 j2.2.1 w kl))))
       . exact kn w jy kx
    .
      rw[dR];intro z k8 k9
      rcases pU k8 with hzp2' | ku
      .
       rw[mT,wSa] at hzp2'
       rcases hzp2' with h1 | h2
       . exact pD h6 k9 (mUl _ (rT h1))
       .
        dsimp only[Q] at h2;rw[wSa,q0s,q0s] at h2
        rcases h2 with kl | jy
        . exact pD h6 k9 (mUr _ (q0w s2 j2.2.1 z kl))
        .
         rcases pU k9 with jq | kc
         . have kb:=j4 z jy (pTf jq);have kt:=j8 z jy (mUl _ (kb ▸ h9.2.1));exact pD h6 (mUr _ (kb ▸ h9.2.1)) (mUr _ (kt ▸ wt))
         . have kt:=j8 z jy (mUl _ kc);exact pD h6 (mUr _ kc) (mUr _ (kt ▸ wt))
      .
       have kv:=h7 ku
       rcases pU k9 with jq | kc
       . exact (pS (h5 kv)).2 (mUl _ (mUr _ jq))
       . exact (pS (h5 kv)).2 (mUl _ (mUl _ (mUl _ (mUr _ kc))))
   have:=le_max' Ls (L+Q.length) (rF ⟨mem_range.mpr (by omega),j0⟩)
   omega
 obtain ⟨r₁,r2,ky,hr2,R,kj,w2,kq,kp⟩ :=
  wy H S F3 F4 wi d (D:O) z1 hdn hexp (λ u hu=>Nat.le_trans (nSl d 1) (hmindeg u hu))
   (h9.1.trans sS) (j2.1.trans sS)
   (λ z hz=>rS ⟨j5 hz,λ h=>pD h0 hz h⟩)
   (by exact_mod_cast jj) (by rw[h9.2.2.1]) (by rw[j2.2.2.1]) jn
 obtain ⟨q1,k3,hq1_len⟩:=q0C h9 ky;obtain ⟨q2,k2,hq2_len⟩:=q0C j2 hr2
 have we:∀ w∈R.support,w∈S \ W:=λ w hw=>by
  have h1:=q0w R (rS ⟨sS (h9.1 ky),
   λ h=>pD h0 h (mUl _ ky)⟩) w hw
  exact rS ⟨(pS h1).1,λ hW=>(pS h1).2 (mUl _ (mUl _ hW))⟩
 have jw:∀ w∈R.support,w∈p1.support->w=v3:=λ w hw hwp1=>by
  by_contra kz
  have h1:=q0w R (rS ⟨sS (h9.1 ky),
   λ h=>pD h0 h (mUl _ ky)⟩) w hw
  exact (pS h1).2 (mUl _ (mUr _
   (rS ⟨rT hwp1,λ h=>kz (pSg h)⟩)))
 have jv:∀ w∈R.support,w∈p2.support->w=v4:=λ w hw hwp2=>by
  by_contra kz
  have h1:=q0w R (rS ⟨sS (h9.1 ky),
   λ h=>pD h0 h (mUl _ ky)⟩) w hw
  exact (pS h1).2 (mUr _
   (rS ⟨rT hwp2,λ h=>kz (pSg h)⟩))
 let kr:=q0r q1 (λ w hw=>h9.1 (q0w q1 h9.2.1 w hw))
 let w7:=q0r q2 (λ w hw=>j2.1 (q0w q2 j2.2.1 w hw))
 let R':=q0r R we;let h8:=p1.append kr;let j6:=w7.reverse.append p2.reverse
 have kk:h8.IsPath:=q0x p1 kr wo (q0v _ _ k3)
  (λ w j7 j1=>jm w j7 (q0w q1 h9.2.1 w (by simpa [kr,q0s] using j1)))
 have je:j6.IsPath:=q0x w7.reverse p2.reverse
  (q0v _ _ k2).reverse wn.reverse (λ w j7 j1=>by
   rw[q0q] at j7 j1
   exact jl w j1 (q0w q2 j2.2.1 w (by simpa [w7,q0s] using j7)))
 have k7:(h8.append R').IsPath:=q0x h8 R' kk (q0v _ _ kj)
  (λ w j7 j1=>by
   rw[q0s] at j1;rw[wSa] at j7
   rcases j7 with h1 | h2
   . have kb:=jw w j1 h1;exact kq w j1 (kb ▸ h9.2.1)
   . exact kq w j1 (q0w q1 h9.2.1 w (by simpa [kr,q0s] using h2)))
 let jp:=(h8.append R').append j6
 have ji:jp.IsPath:=q0x (h8.append R') j6 k7 je
  (λ w j7 j1=>by
   have jk:w∈p2.support.toFinset∪F4:=by
    rw[wSa,q0q,q0q] at j1
    rcases j1 with kl | jy
    . exact mUr _ (q0w q2 j2.2.1 w (by simpa [w7,q0s] using kl))
    . exact mUl _ (rT jy)
   rw[wSa] at j7
   rcases j7 with hL | hR
   .
    exfalso
    have kd:w∈p1.support.toFinset∪F3:=by
      rw[wSa] at hL
      rcases hL with h11 | h12
      . exact mUl _ (rT h11)
      . exact mUr _ (q0w q1 h9.2.1 w (by simpa [kr,q0s] using h12))
    exact pD h6 kd jk
   .
    rw[q0s] at hR
    rcases pU jk with jb | jr
    . have ka:=jv w hR (pTf jb);exact kp w hR (ka ▸ j2.2.1)
    . exact kp w hR jr)
 have hRlen_m:R.length<=m:=by
  have w8:0<=(log n)^3/e1:=by positivity
  exact_mod_cast (show (R.length:O)<=(m:O) by
   linarith only[w2,hmlb,w8,
    show 40/e1*(log n)^3=40*((log n)^3/e1) by ring,
    show 100/e1*(log n)^3=100*((log n)^3/e1) by ring])
 refine ⟨jp,ji,?_,?_⟩
 . dsimp only[jp,h8,j6,kr,w7,R'];simp only[wLa,wLr,q0t];omega
 . dsimp only[jp,h8,j6,kr,w7,R'];simp only[wLa,wLr,q0t];omega
lemma q1g {e1 e2:O} (jv:0 < e1) (kg:e1 < 1) (kf:0 < e2) (jl:e2<=1/25) : ∃ d0:ℕ,100<=d0/\∀ {V:Type*} (H:SG V) (S A:FS V) (d D m l:ℕ) (v:Fin 4->V) (F:Fin 4->FS V), d0<=d->d<=#S -> qQ H S e1 (e2*(d:O)) -> (∀ u∈S,d<=dS H S u) -> (log (#S:O))^10<=(D:O)->(D:O)<=(#S:O)/(log (#S:O))^10 -> 100/e1*(log (#S:O))^3<=(m:O)->(m:O)<=1000/e1*(log (#S:O))^3 -> (l:O)<=(#S:O)/(log (#S:O))^12 -> A⊆S->(#A:O)<=(D:O)/(log (#S:O))^3 -> (∀ i,q0z H (S \ A) (v i) D m (F i)) -> (∀ i j,i≠j->Disjoint (F i) (F j)) -> ∃ (i1 i2:Fin 2) (j1 j2:Fin 2),i1≠i2/\j1≠j2 /\ ∃ (P:(q3 H (S \ A)).Walk (v ⟨i1.val,by omega⟩) (v ⟨j1.val+2,by omega⟩)) (Q:(q3 H (S \ A)).Walk (v ⟨i2.val,by omega⟩) (v ⟨j2.val+2,by omega⟩)), P.IsPath/\Q.IsPath/\Disjoint P.support.toFinset Q.support.toFinset /\ l<=P.length+Q.length/\P.length+Q.length<=l+22*m:=by
 have w1:e2 < 1:=by linarith
 obtain ⟨d1,jw,hle⟩:=q1e jv kg kf jl;obtain ⟨d2,hd2_100,hce⟩:=q1f jv kg kf jl;obtain ⟨d3,hd3_100,hnc⟩:=q0g jv kg kf w1
 have w8:∀ᶠ x:O in atTop,
    (1000:O)<=x/\(4:O)<=log x /\
    (log x)^4<=(100/e1*(log x)^3)^2 /\
    (1000/e1*(log x)^3)^2<=(log x)^7 /\
    4*(log x)^14<=x /\
    7*(1000/e1*(log x)^3)+1<=(log x)^4:=by
  let C:=1000/e1
  filter_upwards [eGe (1000:O),
    lGe (max 4 (max (C^2) (7*C+1))),
    q01 (C:=4) 14 (β:=1) (by norm_num)] with x hx hl hlog14
  rw[r1] at hlog14;have w7:4<=log x:=lT (lMl _ _) hl;have kz:C^2<=log x:=lT (lMl _ _) (lT (lMr _ _) hl);have w0:7*C+1<=log x:=lT (lMr _ _) (lT (lMr _ _) hl);refine ⟨hx,w7,?_,?_,hlog14,?_⟩
  .
    rw[mul_pow,<- pow_mul]
    have w5:(1:O)<=(100/e1)^2:=by
     have:1<=100/e1:=by rw[lDi jv];linarith
     nlinarith
    have h46:(log x)^4<=(log x)^6:=pLr (by linarith only[w7]) (by omega);nlinarith only[mLm w5 h46 (by positivity) (by positivity)]
  . rw[mul_pow,<- pow_mul];have h1:=mlR kz (show (0:O)<=(log x)^6 by positivity);linarith [show log x*(log x)^6=(log x)^7 by ring]
  . have h1:(1:O)<=(log x)^3:=oLp (by linarith);have h2:=mlR w0 (show (0:O)<=(log x)^3 by positivity);linarith [show log x*(log x)^3=(log x)^4 by ring]
 rw[eAt] at w8;obtain ⟨B0,hB0⟩:=w8
 refine ⟨max (max d1 (max d2 d3)) (ceil B0),
  lT (lT jw (lMl _ _)) (lMl _ _),
  λ{V} H S A d D m l v F hd hdn hexp hmindeg hDlb hDub hmlb hmub hlub hAS hAcard hFexp hFdisj=>?_⟩
 have hd1:d1<=d:=lT (lMl _ _) (lT (lMl _ _) hd);have hd2:d2<=d:=lT (lMl _ _) (lT (lMr _ _) (lT (lMl _ _) hd));have hd3:d3<=d:=lT (lMr _ _) (lT (lMr _ _) (lT (lMl _ _) hd))
 have hnB:B0<=(#S:O) :=
  (nLc B0).trans (by exact_mod_cast ((lMr _ _).trans hd).trans hdn)
 obtain ⟨ka,jt,kc,kb,jc,kn⟩:=hB0 (#S:O) hnB;set n:O:=(#S:O);set D':=#S/(m^2)
 have kq:(m:O)<=3000/e1*(log n)^3:=by
  have kx:0<=(log n)^3/e1:=by positivity
  linarith only[hmub,kx,
    show 1000/e1*(log n)^3=1000*((log n)^3/e1) by ring,
    show 3000/e1*(log n)^3=3000*((log n)^3/e1) by ring]
 obtain ⟨F',h5,j3⟩:=hle H S A d D m v F hd1 hdn hexp hmindeg hDlb hDub hmlb kq hAS hAcard hFexp hFdisj
 have km:n/(log n)^7 - 1<=(D':O):=by
  have ky:(m:O)^2<=(log n)^7:=(pLl (nCn m) hmub 2).trans kb
  have h1:n/(log n)^7<=n/((m:O)^2) :=
    dLl (by linarith only[ka]) (by have:0 < (m:O):=lL2 (by positivity) hmlb;positivity) ky
  have h2:n/((m:O)^2) - 1 < (D':O):=by
    have jg:0 < m^2:=by
     have:0 < (m:O):=lL2 (by positivity) hmlb
     have:0 < m:=by exact_mod_cast this
     positivity
    have jm:#S < (D'+1)*(m^2):=by
     have hdm:=Nat.div_add_mod #S (m^2);have hml:=mod_lt #S jg;dsimp only[D'];nlinarith only[hdm,hml]
    have kr:n < ((D':O)+1)*((m:O)^2):=by dsimp only[n,D'];exact_mod_cast jm
    rw[sub_lt_iff_lt_add,div_lt_iff₀ (by exact_mod_cast jg)];exact kr
  linarith only[h1,h2]
 have j4:n/(2*(log n)^7)<=(D':O):=by
  have h1:(2:O)<=n/(log n)^7:=by
    rw[lDi (by positivity)];have h7:(log n)^7<=(log n)^14:=pLr (by linarith only[jt]) (by omega);linarith only[h7,jc,show (0:O)<=(log n)^14 by positivity]
  have jm:n/(2*(log n)^7)=(n/(log n)^7)/2:=by ring
  linarith only[km,h1,jm]
 have j6:(log n)^7<=(D':O):=by
  have:(log n)^7<=n/(2*(log n)^7):=by
    rw[lDi (by positivity)]
    linarith only[jc,show (0:O)<=(log n)^14 by positivity,
     show (log n)^7*(2*(log n)^7)=2*(log n)^14 by ring]
  exact this.trans j4
 have kl:(D':O)<=n/(log n)^4:=by
  have ky:(log n)^4<=(m:O)^2:=kc.trans (pLl (by positivity) hmlb 2)
  have h1:(D':O)*((m:O)^2)<=n:=by dsimp only[n,D'];exact_mod_cast Nat.div_mul_le_self #S (m^2)
  rw[lDi (by positivity)];exact (mlL ky (nCn D')).trans h1
 have hD_le_D':(D:O)<=(D':O):=by
  have h1:n/(log n)^10<=n/(2*(log n)^7):=by
    rw[div_le_div_iff₀ (by positivity) (by positivity)]
    have h3:(2:O)<=(log n)^3:=by
     calc
      (2:O)<=4^3:=by norm_num
      _<=(log n)^3:=pLl (by norm_num) jt 3
    have jj:=mlL h3 (show (0:O)<=n*(log n)^7 by positivity)
    linarith only[jj,
     show n*(2*(log n)^7)=n*(log n)^7*2 by ring,
     show n*(log n)^10=n*(log n)^7*(log n)^3 by ring]
  exact hDub.trans (h1.trans j4)
 let kv:=F' 0∪F' 1;let ku:=F' 2∪F' 3
 have ks:(#A:O)*(log n)^3<=10*(D':O):=by
  have h1:=mlR hAcard (show (0:O)<=(log n)^3 by positivity);rw[div_mul_cancel₀ _ (by positivity)] at h1;linarith
 obtain ⟨a,b,w3,w2,P',jo,jz,jq,jp⟩ :=
  hnc H S kv ku A d (D':O) hd3 hdn hexp (λ u hu=>Nat.le_trans (nSl d 1) (hmindeg u hu))
    (uS ((h5 0).1.trans sS) ((h5 1).1.trans sS))
    (uS ((h5 2).1.trans sS) ((h5 3).1.trans sS))
    (λ z hz=>rS ⟨hAS hz,λ h=>by
     rcases pU h with h1 | h2
     .
      rcases pU h1 with h0 | kt
      . exact (pS ((h5 0).1 h0)).2 hz
      . exact (pS ((h5 1).1 kt)).2 hz
     .
      rcases pU h2 with w4 | h3'
      . exact (pS ((h5 2).1 w4)).2 hz
      . exact (pS ((h5 3).1 h3')).2 hz⟩)
    ((oLp (by linarith)).trans j6)
    (by
      have:D'<=kv.card:=by
       dsimp only[D'];rw[<- (h5 0).2.2.1];exact cL sUl
      exact_mod_cast this)
    (by
      have:D'<=ku.card:=by
       dsimp only[D'];rw[<- (h5 2).2.2.1];exact cL sUl
      exact_mod_cast this)
    ks
 have ke:∃ i1:Fin 2,a∈F' ⟨i1.val,by omega⟩:=by
  rcases pU w3 with h0 | h1
  . exact ⟨0,h0⟩
  . exact ⟨1,h1⟩
 have kd:∃ j1:Fin 2,b∈F' ⟨j1.val+2,by omega⟩:=by
  rcases pU w2 with h2 | h3
  . exact ⟨0,h2⟩
  . exact ⟨1,h3⟩
 obtain ⟨i1,k7⟩:=ke;obtain ⟨j1,k6⟩:=kd;let i2:Fin 2:=⟨1 - i1.val,by omega⟩;let j2:Fin 2:=⟨1 - j1.val,by omega⟩
 have k5:i1≠i2:=λ h=>by have:=congrArg Fin.val h;dsimp only[i2] at this;omega
 have k4:j1≠j2:=λ h=>by have:=congrArg Fin.val h;dsimp only[j2] at this;omega
 let h9:Fin 4:=⟨i1.val,by omega⟩;let h8:Fin 4:=⟨i2.val,by omega⟩;let j0:Fin 4:=⟨j1.val+2,by omega⟩;let h6:Fin 4:=⟨j2.val+2,by omega⟩;obtain ⟨pa,ji,hpa_len⟩:=q0C (h5 h9) k7;obtain ⟨pb,jh,hpb_len⟩:=q0C (h5 j0) k6;let jr:=q0r pa (λ w hw=>(h5 h9).1 (q0w pa (h5 h9).2.1 w hw))
 let ko:=q0r pb (λ w hw=>(h5 j0).1 (q0w pb (h5 j0).2.1 w hw))
 have jd:(jr.append P').IsPath:=q0x jr P' (q0v _ _ ji) jo
  (λ w k3 hw2=>by
    have j7:w∈F' h9:=q0w pa (h5 h9).2.1 w (by simpa [jr,q0s] using k3)
    have k9:w∈kv:=by
     fin_cases i1
     . exact mUl _ j7
     . exact mUr _ j7
    exact jq w hw2 k9)
 let P:=(jr.append P').append ko.reverse
 have jy:P.IsPath:=q0x (jr.append P') ko.reverse jd
  (q0v _ _ jh).reverse (λ w k3 hw2=>by
    rw[q0q,q0s] at hw2;have j7:w∈F' j0:=q0w pb (h5 j0).2.1 w hw2
    have k8:w∈ku:=by
     fin_cases j1
     . exact mUl _ j7
     . exact mUr _ j7
    rw[wSa] at k3
    rcases k3 with h1 | h2
    . exfalso;have kp:w∈F' h9:=q0w pa (h5 h9).2.1 w (by simpa [jr,q0s] using h1);exact pD (j3 h9 j0 (by intro h;have:=congrArg Fin.val h;dsimp only[h9,j0] at this;omega)) kp j7
    . exact jp w h2 k8)
 have hP_len:P.length<=7*m:=by
  have hP'm:P'.length<=m:=by
    have kx:0<=(log n)^3/e1:=by positivity
    exact_mod_cast (show (P'.length:O)<=(m:O) by
     linarith only[jz,hmlb,kx,
      show 40/e1*(log n)^3=40*((log n)^3/e1) by ring,
      show 100/e1*(log n)^3=100*((log n)^3/e1) by ring])
  dsimp only[P,jr,ko];simp only[wLa,wLr,q0t];omega
 have jf:Disjoint P.support.toFinset (F' h8):=by
  rw[dL];intro w js j7
  have k9:w∈kv:=by
    fin_cases i1
    . dsimp only[h8,i2] at j7;exact mUr _ j7
    . dsimp only[h8,i2] at j7;exact mUl _ j7
  have ja:h9≠h8:=λ h=>by
    have hv:=congrArg Fin.val h;dsimp only[h9,h8] at hv;exact k5 (Fin.ext hv)
  dsimp only[P] at js;rw[mT,wSa,wSa] at js
  rcases js with (h1 | h2) | h3
  . have k3:=q0w pa (h5 h9).2.1 w (by simpa [jr,q0s] using h1);exact pD (j3 h9 h8 ja) k3 j7
  . have hwa:=jq w h2 k9;exact pD (j3 h9 h8 ja) (hwa ▸ k7) j7
  . rw[q0q] at h3;have kw:=q0w pb (h5 j0).2.1 w (by simpa [ko,q0s] using h3);exact pD (j3 j0 h8 (by intro h;have:=congrArg Fin.val h;dsimp only[j0,h8] at this;omega)) kw j7
 have je:Disjoint P.support.toFinset (F' h6):=by
  rw[dL];intro w js j7
  have k8:w∈ku:=by
    fin_cases j1
    . dsimp only[h6,j2] at j7;exact mUr _ j7
    . dsimp only[h6,j2] at j7;exact mUl _ j7
  have j9:j0≠h6:=λ h=>by
    have hv:=congrArg Fin.val h;dsimp only[j0,h6] at hv;exact k4 (Fin.ext (by omega))
  dsimp only[P] at js;rw[mT,wSa,wSa] at js
  rcases js with (h1 | h2) | h3
  . have k3:=q0w pa (h5 h9).2.1 w (by simpa [jr,q0s] using h1);exact pD (j3 h9 h6 (by intro h;have:=congrArg Fin.val h;dsimp only[h9,h6] at this;omega)) k3 j7
  . have hwb:=jp w h2 k8;exact pD (j3 j0 h6 j9) (hwb ▸ k6) j7
  . rw[q0q] at h3;have kw:=q0w pb (h5 j0).2.1 w (by simpa [ko,q0s] using h3);exact pD (j3 j0 h6 j9) kw j7
 let W:=A∪P.support.toFinset
 have kh:W⊆S:=uS hAS (λ z hz =>
  sS (q0w P ((h5 h9).1 (h5 h9).2.1) z (pTf hz)))
 have jb:(7*m+1:O)<=(D':O)/(2*(log n)^3):=by
  have h1:(7*m+1:O)<=(log n)^4:=by
    have:7*(m:O)+1<=7*(1000/e1*(log n)^3)+1:=by linarith
    exact this.trans kn
  have h2:(log n)^4<=(D':O)/(2*(log n)^3):=by
    rw[lDi (by positivity)]
    have h3:2*(log n)^7<=n/(2*(log n)^7):=by
     rw[lDi (by positivity)];linarith [show 2*(log n)^7*(2*(log n)^7)=4*(log n)^14 by ring]
    linarith [show (log n)^4*(2*(log n)^3)=2*(log n)^7 by ring]
  exact h1.trans h2
 have jx:(#W:O)<=(D':O)/(log n)^3:=by
  have h1:#W<=#A+7*m+1:=by
    have h2:=cUl A P.support.toFinset;have h3:=q0y P;dsimp only[W];omega
  have h1R:(#W:O)<=(#A:O)+(7*(m:O)+1):=by exact_mod_cast h1
  have k2:(#A:O)<=(D':O)/(2*(log n)^3):=by
    have k1:(D:O)<=(D':O)/2:=by
     have kt:n/(log n)^10<=n/(4*(log n)^7):=by
      rw[div_le_div_iff₀ (by positivity) (by positivity)]
      have h4:(4:O)<=(log n)^3:=by
       calc
        (4:O)<=4^3:=by norm_num
        _<=(log n)^3:=pLl (by norm_num) jt 3
      have jj:=mlL h4 (show (0:O)<=n*(log n)^7 by positivity)
      linarith only[jj,
       show n*(4*(log n)^7)=n*(log n)^7*4 by ring,
       show n*(log n)^10=n*(log n)^7*(log n)^3 by ring]
     have jm:n/(4*(log n)^7)=(n/(2*(log n)^7))/2:=by ring
     linarith only[hDub,kt,jm,j4]
    calc
     (#A:O)<=(D:O)/(log n)^3:=hAcard
     _<=((D':O)/2)/(log n)^3:=dLr k1 (by positivity)
     _=(D':O)/(2*(log n)^3):=by ring
  linarith only[h1R,k2,jb,
    show (D':O)/(2*(log n)^3)+(D':O)/(2*(log n)^3)=(D':O)/(log n)^3 by ring]
 let j8:=l+7*m - P.length
 have jk:(j8:O)<=(D':O)/(log n)^3:=by
  have h1:(j8:O)<=(l:O)+(7*(m:O)+1):=by
    have:j8<=l+7*m+1:=by omega
    exact_mod_cast this
  have ju:(l:O)<=(D':O)/(2*(log n)^3):=by
    have kt:n/(log n)^12<=(n/(2*(log n)^7))/(2*(log n)^3):=by
     rw[show (n/(2*(log n)^7))/(2*(log n)^3)=n/(4*(log n)^10) by ring];rw[div_le_div_iff₀ (by positivity) (by positivity)]
     have h4:(4:O)<=(log n)^2:=by
      calc
       (4:O)<=4^2:=by norm_num
       _<=(log n)^2:=pLl (by norm_num) jt 2
     have jj:=mlL h4 (show (0:O)<=n*(log n)^10 by positivity)
     linarith only[jj,
      show n*(4*(log n)^10)=n*(log n)^10*4 by ring,
      show n*(log n)^12=n*(log n)^10*(log n)^2 by ring]
    have w4:=dLr j4 (show (0:O)<=2*(log n)^3 by positivity);linarith only[hlub,kt,w4]
  linarith only[h1,ju,jb,
    show (D':O)/(2*(log n)^3)+(D':O)/(2*(log n)^3)=(D':O)/(log n)^3 by ring]
 have j5:q0z H (S \ W) (v h8) D' (3*m) (F' h8) :=
  ⟨λ z hz=>rS ⟨(pS ((h5 h8).1 hz)).1,λ hW=>by
    rcases pU hW with hA | hP
    . exact (pS ((h5 h8).1 hz)).2 hA
    . exact pD jf hP hz⟩,
   (h5 h8).2.1,(h5 h8).2.2.1,(h5 h8).2.2.2⟩
 have k0:q0z H (S \ W) (v h6) D' (3*m) (F' h6) :=
  ⟨λ z hz=>rS ⟨(pS ((h5 h6).1 hz)).1,λ hW=>by
    rcases pU hW with hA | hP
    . exact (pS ((h5 h6).1 hz)).2 hA
    . exact pD je hP hz⟩,
   (h5 h6).2.1,(h5 h6).2.2.1,(h5 h6).2.2.2⟩
 obtain ⟨Q0,jn,kj,ki⟩ :=
  hce H S W (F' h8) (F' h6) d D' (3*m) j8 (v h8) (v h6)
    hd2 hdn hexp hmindeg j6 kl
    (by push_cast;linarith only[hmlb,show (0:O)<=(m:O) from nCn m])
    (by push_cast;linarith only[hmub,show 3*(1000/e1*(log n)^3)=3000/e1*(log n)^3 by ring])
    kh jx j5 k0
    (j3 h8 h6 (by intro h;have:=congrArg Fin.val h;dsimp only[h8,h6] at this;omega))
    jk
 have kk:∀ w∈Q0.support,w∈S \ A:=λ w hw=>by
  have h1:=q0w Q0 (j5.1 j5.2.1) w hw;exact rS ⟨(pS h1).1,λ hA=>(pS h1).2 (mUl _ hA)⟩
 let Q:=q0r Q0 kk;refine ⟨i1,i2,j1,j2,k5,k4,P,Q,jy,q0v _ _ jn,?_,?_,?_⟩
 . rw[dR];intro w w6 js;rw[mT,q0s] at w6;exact (pS (q0w Q0 (j5.1 j5.2.1) w w6)).2 (mUr _ js)
 . rw[q0t];dsimp only[j8] at kj;omega
 . rw[q0t];dsimp only[j8] at ki;omega
def q1h {V:Type*} (H:SG V) (S:FS V)
  (D m k:ℕ) (v1:V) (F1:FS V) (v2:V) (F2:FS V) (A:FS V) (l:ℕ):Prop :=
 A⊆S/\Disjoint A F1/\Disjoint A F2/\Disjoint F1 F2 /\
 q0z H S v1 D m F1/\q0z H S v2 D m F2 /\
 #A<=10*m*k /\
 ∀ i ≤ k,∃ p:(q3 H (A∪{v1,v2})).Walk v1 v2,p.IsPath/\p.length=l+2*i
lemma q1i {V:Type*} {H:SG V} {S:FS V} {D m k l:ℕ} {v1 v2:V} {F1 F2 A:FS V} (h:q1h H S D m k v1 F1 v2 F2 A l) : q1h H S D m k v2 F2 v1 F1 A l:=by
 refine ⟨h.1,h.2.2.1,h.2.1,h.2.2.2.1.symm,h.2.2.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.2.1,λ i hi=>?_⟩
 obtain ⟨p,hp,h0⟩:=h.2.2.2.2.2.2.2 i hi
 have heq:A∪{v2,v1}=A∪{v1,v2}:=by
  ext z;simp only[mU,mem_insert,mSg];tauto
 refine ⟨q0r p.reverse (λ w hw=>heq.symm ▸ q0w p
  (mUr _ (mem_insert_self v1 {v2})) w (q0q.mp hw)),
  q0v _ _ hp.reverse,by rw[q0t,wLr,h0]⟩
lemma q1j {V:Type*} {H:SG V} {S S':FS V}
   {D m k l:ℕ} {v1 v2:V} {F1 F2 A:FS V}
   (h:q1h H S D m k v1 F1 v2 F2 A l) (hSS':S⊆S') :
   q1h H S' D m k v1 F1 v2 F2 A l :=
 ⟨h.1.trans hSS',h.2.1,h.2.2.1,h.2.2.2.1,q0A h.2.2.2.2.1 hSS',
  q0A h.2.2.2.2.2.1 hSS',h.2.2.2.2.2.2.1,h.2.2.2.2.2.2.2⟩
lemma q1k {V:Type*} {H:SG V} {S:FS V}
   {D m m' k l:ℕ} {v1 v2:V} {F1 F2 A:FS V}
   (h:q1h H S D m k v1 F1 v2 F2 A l) (hmm':m<=m') :
   q1h H S D m' k v1 F1 v2 F2 A l :=
 ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,q0B h.2.2.2.2.1 hmm',
  q0B h.2.2.2.2.2.1 hmm',
  h.2.2.2.2.2.2.1.trans (nMr k (nMl 10 hmm')),
  h.2.2.2.2.2.2.2⟩
lemma q1l {V:Type*} {H:SG V} {S:FS V} {D m k l:ℕ} {v1 v2:V} {F1 F2 A:FS V} (h:q1h H S D m k v1 F1 v2 F2 A l):l<=#A+1:=by
 obtain ⟨p,hp,hlen⟩:=h.2.2.2.2.2.2.2 0 (Nat.zero_le k)
 have h0:p.support.toFinset⊆A∪{v1,v2}:=λ w hw =>
  q0w p (mUr _ (mem_insert_self v1 {v2})) w (pTf hw)
 have h1:p.length+1=p.support.toFinset.card:=by
  rw[List.toFinset_card_of_nodup hp.support_nodup,wLs]
 have h2:#(A∪{v1,v2})<=#A+2:=(cUl _ _).trans (Nat.add_le_add_left (card_le_two) _);have h3:=cL h0;omega
lemma q1m {V:Type*} {H1 H2:SG V} {S:FS V} {D m k l:ℕ} {v1 v2:V} {F1 F2 A:FS V} (h9:H1<=H2) (h:q1h H1 S D m k v1 F1 v2 F2 A l) : q1h H2 S D m k v1 F1 v2 F2 A l:=by
 have h3:∀ (T X:FS V) (r:ℕ),qs H1 T r X⊆qs H2 T r X:=by
  intro T X r;induction r with
  | zero=>exact sR
  | succ r ih =>
   intro z hz;rcases pU hz with h1 | h2
   . exact mUl _ (ih h1)
   .
    obtain ⟨hzT,_,u,hu,huz⟩:=(qo H1 T _ z).mp h2
    by_cases h8:z∈qs H2 T r X
    . exact mUl _ h8
    . exact mUr _ ((qo H2 T _ z).mpr ⟨hzT,h8,u,ih hu,h9 huz⟩)
 have h0:∀ v F,q0z H1 S v D m F->q0z H2 S v D m F:=λ v F hE =>
  ⟨hE.1,hE.2.1,hE.2.2.1,hE.2.2.2.trans (h3 F {v} m)⟩
 have h6:∀ (T:FS V) {u v:V} (p:(q3 H1 T).Walk u v),
   ∃ q:(q3 H2 T).Walk u v,q.support=p.support/\q.length=p.length:=by
  intro T u v p;induction p with
  | nil=>exact ⟨.nil,rfl,rfl⟩
  | cons hadj p' ih =>
   obtain ⟨q',h4,h5⟩:=ih;exact ⟨.cons (q0o (h9 hadj.1) hadj.2.1 hadj.2.2) q',by simp [h4],by simp [h5]⟩
 refine ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h0 v1 F1 h.2.2.2.2.1,
  h0 v2 F2 h.2.2.2.2.2.1,h.2.2.2.2.2.2.1,λ i hi=>?_⟩
 obtain ⟨p,hp,h7⟩:=h.2.2.2.2.2.2.2 i hi;obtain ⟨q,hqs,hql⟩:=h6 (A∪{v1,v2}) p;exact ⟨q,by rw[wIp,hqs];exact hp.support_nodup,hql.trans h7⟩
lemma q1n {e1 e2:O} {K:ℕ}
  (wx:0 < e1) (ze:e1 < 1) (zd:0 < e2) (zc:e2 < 1) (hK:1<=K) :
  ∃ d0:ℕ,100<=d0/\∀ {V:Type*} (H:SG V) (S:FS V) (col:V->Bool)
   (d D:ℕ) (x0:V) (c:(q3 H S).Walk x0 x0) (x1 x2:V),
   d0<=d->d<=#S ->
   qk H col ->
   qQ H S e1 (e2*(d:O)) ->
   (∀ v∈S,d - 1<=dS H S v) ->
   q0G H S x0 c ->
   x1∈S->x2∈S->x1≠x2->x1 ∉ c.support.toFinset->x2 ∉ c.support.toFinset ->
   1<=D->(D:O)<=(log (#S:O))^K ->
   let m:=floor (200/e1*(log (#S:O))^3)
   ∃ (F1 F2 A:FS V) (l:ℕ),
    q1h H S D m 1 x1 F1 x2 F2 A l/\c.support.toFinset⊆A:=by
 obtain ⟨d1,jq,kq⟩:=q19 (t:=4) (s:=2) (K:=K+10) wx ze zd zc (by omega) (by omega) (by omega);obtain ⟨d2,hd2_100,hnc⟩:=q0g wx ze zd zc
 have hev:∀ᶠ x:O in atTop,
   (100:O)<=x/\(4:O)<=log x/\(1:O) < log (x - 2) /\
   2*log x+3<=200/e1*(log x)^3 - 1 /\
   (200/e1*(log x)^3)^3*(log x)^K<=(log x)^(K+10) /\
   (10:O)*(log x)^3<=200/e1*(log x)^3 - 1:=by
  filter_upwards [eGe (100:O),
   lGe (max 4 ((200/e1)^3+1))] with x hx hl
  have hl4:4<=log x:=lT (lMl _ _) hl;have hlC:(200/e1)^3+1<=log x:=lT (lMr _ _) hl
  have h200:200<=200/e1:=by rw[lDi wx];linarith
  have hl1:1<=log x:=by linarith
  have hl3:(64:O)<=(log x)^3:=calc (64:O)=4^3:=by norm_num
   _<=(log x)^3:=pLl (by norm_num) hl4 3
  refine ⟨hx,hl4,?_,?_,?_,by nlinarith⟩
  . rw[lIt (by linarith)];linarith [e1l]
  .
   have:log x<=(log x)^3:=by
    calc
     log x=(log x)^1:=(pow_one _).symm
     _<=(log x)^3:=pLr hl1 (by omega)
   nlinarith
  .
   rw[mul_pow,<- pow_mul]
   have h1:=mlR (show (200/e1)^3<=log x by linarith)
    (show (0:O)<=(log x)^9*(log x)^K by positivity)
   have zn:log x*((log x)^9*(log x)^K)=(log x)^(K+10):=by
    rw[<- mul_assoc,<- pow_succ',<- pow_add];congr 1;omega
   linarith [show (200/e1)^3*(log x)^(3*3)*(log x)^K =
     (200/e1)^3*((log x)^9*(log x)^K) by ring]
 rw[eAt] at hev;obtain ⟨B0,hB0⟩:=hev
 refine ⟨max (max d1 d2) (ceil B0),lT (lT jq (lMl _ _)) (lMl _ _),
  λ{V} H S col d D x0 c x1 x2 hd hdn hbip hexp hmindeg hcyc hx1S hx2S hx12 hx1C hx2C hD1 hDK=>?_⟩
 have zw:d1<=d:=lT (lMl _ _) (lT (lMl _ _) hd);have hd2:d2<=d:=lT (lMr _ _) (lT (lMl _ _) hd);have hdB:B0<=(d:O):=(nLc B0).trans (by exact_mod_cast (lMr _ _).trans hd);have hnB:B0<=(#S:O):=hdB.trans (by exact_mod_cast hdn)
 have ww:1 < log ((d - 1 - 1:ℕ):O):=by
  have hd100:100<=d:=jq.trans zw
  have zg:((d - 1 - 1:ℕ):O)=(d:O) - 2:=by
   rw[show d - 1 - 1=d - 2 by omega,Nat.cast_sub (by omega),Nat.cast_ofNat]
  rw[zg];exact (hB0 (d:O) hdB).2.2.1
 obtain ⟨hn100,hln4,_,hC_le_m,k1,h10log_m⟩:=hB0 (#S:O) hnB;set n:O:=(#S:O);set m:=floor (200/e1*(log n)^3);set m0:=floor (40/e1*(log n)^3);set C:=c.support.toFinset
 have j4:5*m0<=m:=by
  have h1:(m0:O)<=40/e1*(log n)^3:=nFl (by positivity)
  have hnn:0<=(log n)^3/e1:=by positivity
  exact nLf (by
   push_cast
   linarith only[h1,hnn,
    show 5*(40/e1*(log n)^3)=200*((log n)^3/e1) by ring,
    show 200/e1*(log n)^3=200*((log n)^3/e1) by ring])
 have j8:10*(log n)^3<=(m:O):=by
  have:200/e1*(log n)^3 - 1 < (m:O):=by linarith [nL1 (200/e1*(log n)^3)]
  linarith
 have jg:10<=m:=by
  have:(10:O)<=10*(log n)^3:=by
   have:(1:O)<=(log n)^3:=oLp (by linarith);nlinarith
  exact_mod_cast this.trans j8
 have jv:c.length<=m:=by
  have h1:=q0L hcyc (by have:100<=d:=jq.trans zw;omega) hmindeg
  have h2:2*log n/log ((d - 1 - 1:ℕ):O)<=2*log n :=
   dLs (by positivity) ww.le
  have hm_lb:200/e1*(log n)^3 - 1 < (m:O):=by linarith [nL1 (200/e1*(log n)^3)]
  exact_mod_cast (show (c.length:O)<=(m:O) by linarith)
 have hC_card_le_m:#C<=m:=by
  have wv:=wSn c
  have jx:c.support=c.support.dropLast ++ [x0]:=by
   simpa [wGl c] using (dropLast_append_getLast wv).symm
  have zr:C⊆c.support.dropLast.toFinset:=by
   intro w hw;rw[mT] at hw ⊢;rw[jx,mem_append,List.mem_singleton] at hw
   rcases hw with h1 | hwx
   . exact h1
   .
    rw[hwx]
    have h0:0 < c.support.dropLast.length:=by rw[length_dropLast,wLs];have:=hcyc.1.three_le_length;omega
    have hx0:c.support.dropLast[0]'h0=x0:=by
     have h1:(c.support.dropLast ++ [x0])[0]'(by rw[<- jx];exact length_pos_of_ne_nil wv)=c.support.dropLast[0]'h0:=getElem_append_left h0
     have h2:∀ M:List V,(hm:M=c.support)->M[0]'(hm ▸ length_pos_of_ne_nil wv)=x0:=by
      rintro _ rfl;exact q0N c
     exact h1.symm.trans (h2 _ jx.symm)
    have zt:=getElem_mem h0
    rwa [hx0] at zt
  calc
   #C<=c.support.dropLast.toFinset.card:=cL zr
   _<=c.support.dropLast.length:=toFinset_card_le _
   _=c.length:=by rw[length_dropLast,wLs];simp
   _<=m:=jv
 have k0:Even c.length:=by
  have zh:qk (q3 H S) col:=λ u v hadj=>hbip u v hadj.1
  exact (qm zh c).mpr rfl
 obtain ⟨l0,hclen_eq⟩:=k0
 have hl0_ge2:2<=l0:=by have:=hcyc.1.three_le_length;omega
 obtain ⟨a,wy,kr,zj⟩:=q0O c hcyc.1;let i0:Fin c.length:=⟨0,by omega⟩;let j0:Fin c.length:=⟨l0 - 1,by omega⟩;obtain ⟨R1,R2,kt,ks,wf,wd,we,wc,hR_inter,hR_union⟩:=zj i0 j0 (by dsimp [i0,j0];omega);let x3:=a i0;let x4:=a j0
 have z7:x3≠x4:=λ h=>by have:=congrArg Fin.val (wy h);dsimp [i0,j0] at this;omega
 have jp:x3∈C:=by dsimp only[C];rw[<- kr];exact mem_image_of_mem a (mUv i0)
 have jh:x4∈C:=by dsimp only[C];rw[<- kr];exact mem_image_of_mem a (mUv j0)
 have j9:C⊆S:=by
  have zq:x0∈S:=by cases c with | nil=>exact absurd rfl hcyc.1.ne_nil | cons hadj _=>exact hadj.2.1
  intro w hw;exact q0w c zq w (pTf hw)
 let X:FS V:={x1,x2,x3,x4};let D1:=m^3*D;let D2:=m^2*D
 have ji:1000<=m^3:=by
  calc
   1000=10^3:=by norm_num
   _<=m^3:=nPl jg 3
 have jn:100<=m^2:=by
  calc
   100=10^2:=by norm_num
   _<=m^2:=nPl jg 2
 have k8:2<=D1:=by dsimp only[D1];nlinarith only[ji,hD1]
 have k7:2<=D2:=by dsimp only[D2];nlinarith only[jn,hD1]
 have z4:(D1:O)<=(log n)^(K+10):=by
  have zb:(m:O)<=200/e1*(log n)^3:=nFl (by positivity);dsimp only[D1];push_cast;exact (mLm (pLl (nCn m) zb 3) hDK (nCn D) (by positivity)).trans k1
 obtain ⟨F_all,j3,h6,h7⟩ :=
  kq H S X d D1 x0 c zw hdn hexp hmindeg hcyc
   (by
     intro z hz;simp only[X,mem_insert,mSg] at hz
     rcases hz with rfl | rfl | rfl | rfl;exact hx1S;exact hx2S;exact j9 jp;exact j9 jh)
   (card_pos.mpr ⟨x1,by simp [X]⟩)
   (by
     have h1:=card_insert_le x1 ({x2,x3,x4}:FS V);have h2:=card_insert_le x2 ({x3,x4}:FS V);have h3:=card_le_two (a:=x3) (b:=x4)
     dsimp only[X];omega)
   (by omega) z4
 have h8:x1∈X/\x2∈X/\x3∈X/\x4∈X:=by simp [X]
 have ju:D<=D1:=by dsimp only[D1];nlinarith only[ji,hD1]
 have jo:D2<=D1:=by
  dsimp only[D1,D2]
  calc
   m^2*D=1*(m^2*D):=by ring
   _<=m*(m^2*D):=nMr _ (by omega)
   _=m^3*D:=by ring
 obtain ⟨F1,j7,jf⟩:=q0E (q0B (j3 x1 h8.1 0) j4) hD1 ju;obtain ⟨F2,j6,ja⟩:=q0E (q0B (j3 x2 h8.2.1 0) j4) hD1 ju;obtain ⟨F2',j1,jm⟩:=q0E (q0B (j3 x2 h8.2.1 1) j4) (by omega) jo;obtain ⟨F4',h9,jl⟩:=q0E (q0B (j3 x4 h8.2.2.2 0) j4) (by omega) jo;let F1':=F_all x1 1;let F3':=F_all x3 0;have w0:q0z H S x1 D1 m F1':=q0B (j3 x1 h8.1 1) j4;have kz:q0z H S x3 D1 m F3':=q0B (j3 x3 h8.2.2.1 0) j4
 have je:∀ (xa xb:V) (Fa Fb Wf:FS V) (Da:ℕ),
   q0z H S xa Da m Fa->q0z H S xb Da m Fb ->
   xa≠xb->2<=Da->Wf⊆S ->
   Disjoint (Fa \ {xa}) Wf->Disjoint (Fb \ {xb}) Wf->Disjoint Fa Fb ->
   (#Wf:O)*(log n)^3<=10*((Da - 1:ℕ):O) ->
   ∃ p:(q3 H S).Walk xa xb,p.IsPath/\p.length<=3*m /\
    (∀ w∈p.support,w∈Wf->w=xa\/w=xb):=by
  intro xa xb Fa Fb Wf Da ki wk _hab hDa2 zz w8 zf zv wz
  have ky:((Da - 1:ℕ):O)<=(#(Fa \ {xa}):O):=by
   have:#(Fa \ {xa})=Da - 1:=by
    rw[card_sdiff_of_subset (sSm ki.2.1),card_singleton,ki.2.2.1]
   exact_mod_cast this.ge
  have kx:((Da - 1:ℕ):O)<=(#(Fb \ {xb}):O):=by
   have:#(Fb \ {xb})=Da - 1:=by
    rw[card_sdiff_of_subset (sSm wk.2.1),card_singleton,wk.2.2.1]
   exact_mod_cast this.ge
  obtain ⟨a0,b0,zl,hb0,q,hq_path,wt,_,_⟩ :=
   hnc H S (Fa \ {xa}) (Fb \ {xb}) Wf d ((Da - 1:ℕ):O) hd2 hdn hexp hmindeg
    (sS.trans ki.1) (sS.trans wk.1)
    (λ z hz=>rS ⟨zz hz,λ h=>by
     rcases pU h with h1 | h2
     . exact pD w8 h1 hz
     . exact pD zf h2 hz⟩)
    (by exact_mod_cast (show 1<=Da - 1 by omega)) ky kx wz
  have zs:∀ w∈q.support,w∈S:=λ w hw =>
   sS (q0w q (rS ⟨ki.1 (pS zl).1,
    λ h=>pD w8 zl h⟩) w hw)
  have k9:∀ w∈q.support,w ∉ Wf:=λ w hw =>
   (pS (q0w q (rS ⟨ki.1 (pS zl).1,
    λ h=>pD w8 zl h⟩) w hw)).2
  let qS:=q0r q zs;obtain ⟨a1,zk,q1r,hq1r_path,ko,kn,jy⟩:=q13 qS.reverse Fa (pS zl).1;let q1:=q1r.reverse;obtain ⟨wl,kc,hpa1_len⟩:=q0C ki zk
  have kp:∀ w∈q1.support,w∈q.support:=λ w hw=>by
   have:=kn w (q0q.mp hw)
   rwa [q0q,q0s] at this
  obtain ⟨b1,zi,q2,kl,w7,k5,ka⟩:=q13 q1 Fb (pS hb0).1;obtain ⟨zm,kb,hpb1_len⟩:=q0C wk zi;have km:∀ w∈q2.support,w∈q.support:=λ w hw=>kp w (k5 w hw)
  have wu:∀ w∈q2.support,w∈Fa->w=a1:=λ w hw hwFa =>
   jy w (q0q.mp (k5 w hw)) hwFa
  let wm:=((q0r wl (λ w hw=>ki.1 (q0w wl ki.2.1 w hw))).append q2).append
   (q0r zm (λ w hw=>wk.1 (q0w zm wk.2.1 w hw))).reverse
  have wj:((q0r wl (λ w hw=>ki.1 (q0w wl ki.2.1 w hw))).append q2).IsPath :=
   q0x _ _ (q0v _ _ kc) kl (λ w ws w5 =>
    wu w w5 (q0w wl ki.2.1 w (by simpa [q0s] using ws)))
  refine ⟨wm,?_,?_,?_⟩
  .
   apply q0x _ _ wj (q0v _ _ kb).reverse;intro w ws w5;rw[q0q,q0s] at w5;have z9:=q0w zm wk.2.1 w w5;rw[wSa] at ws
   rcases ws with z5 | h2'
   . exact (pD zv (q0w wl ki.2.1 w (by simpa [q0s] using z5)) z9).elim
   . exact ka w h2' z9
  .
   have hqm:q.length<=m:=by
    have:(q.length:O)<=200/e1*(log n)^3:=wt.trans (by
     have:0<=(log n)^3/e1:=by positivity
     nlinarith [show 40/e1*(log n)^3=40*((log n)^3/e1) by ring,
      show 200/e1*(log n)^3=200*((log n)^3/e1) by ring])
    exact nLf this
   dsimp only[wm];simp only[wLa,wLr,q0t];have hq2l:q2.length<=q.length:=w7.trans (by rw[wLr];exact ko.trans (by rw[wLr,q0t]));omega
  .
   intro w hw wr;dsimp only[wm] at hw
   rw[wSa,wSa,q0q,
    q0s,q0s] at hw
   rcases hw with (z5 | h2') | h3'
   . left;by_contra wv;exact pD w8 (rS ⟨q0w wl ki.2.1 w z5,rG wv⟩) wr
   . exact absurd wr (k9 w (km w h2'))
   . right;by_contra wv;exact pD zf (rS ⟨q0w zm wk.2.1 w h3',rG wv⟩) wr
 let W1:=C∪F1∪F2∪F2'∪F4';have wa:W1⊆S:=uS (uS (uS (uS j9 jf.1) ja.1) jm.1) jl.1
 have z1:(#W1:O)*(log n)^3<=10*((D1 - 1:ℕ):O):=by
  have h1:#W1<=m+D+D+D2+D2:=by
   have hc1:=cUl (C∪F1∪F2∪F2') F4';have zy:=cUl (C∪F1∪F2) F2';have zx:=cUl (C∪F1) F2;have hc4:=cUl C F1;rw[jl.2.2.1] at hc1;rw[jm.2.2.1] at zy;rw[ja.2.2.1] at zx;rw[jf.2.2.1] at hc4;dsimp only[W1];omega
  have z5:#W1<=5*D2:=by
   have hm_le_D2:m<=D2:=by
    dsimp only[D2]
    calc
     m=m*1:=by ring
     _<=m*(m*D):=nMl m (by nlinarith only[jg,hD1])
     _=m^2*D:=by ring
   have hD_le_D2:D<=D2:=by dsimp only[D2];nlinarith only[jn,hD1]
   omega
  have h1R:(#W1:O)<=5*(D2:O):=by exact_mod_cast z5
  have h2:5*(D2:O)*(log n)^3<=5*(D1:O)/10:=by
   have jz:=mlL j8 (show (0:O)<=5*(D2:O) by positivity)
   have zn:(D1:O)=(m:O)*(D2:O):=by dsimp only[D1,D2];push_cast;ring
   linarith only[jz,zn,show 5*(D2:O)*(10*(log n)^3)=10*(5*(D2:O)*(log n)^3) by ring,
    show 5*(D2:O)*(m:O)=5*((m:O)*(D2:O)) by ring]
  have h3:(D1:O) - 1=((D1 - 1:ℕ):O):=by rw[Nat.cast_sub (by omega),Nat.cast_one]
  have w2:(2:O)<=(D1:O):=by exact_mod_cast k8
  have jz:=mlR h1R (show (0:O)<=(log n)^3 by positivity);linarith only[jz,h2,h3,w2]
 have kg:Disjoint (F1' \ {x1}) W1:=by
  rw[dL];intro z jw wp
  rcases pU wp with h1 | h4'
  .
   rcases pU h1 with h2 | h2'
   .
    rcases pU h2 with h3 | z2
    .
     rcases pU h3 with js | z3
     . exact pD (h6 x1 h8.1 1) jw (mUl _ js)
     .
      have wn:z≠x1:=(pS jw).2 ∘ mSg.mpr
      exact pD (h7 x1 h8.1 1 x1 h8.1 0 (by simp)) jw
       (rS ⟨j7 z3,rG wn⟩)
    .
     by_cases j2:z=x2
     . exact pD (h6 x1 h8.1 1) jw (mUr _ (j2 ▸ h8.2.1))
     .
      exact pD (h7 x1 h8.1 1 x2 h8.2.1 0 (by simp [hx12])) jw
       (rS ⟨j6 z2,rG j2⟩)
   .
    by_cases j2:z=x2
    . exact pD (h6 x1 h8.1 1) jw (mUr _ (j2 ▸ h8.2.1))
    .
     exact pD (h7 x1 h8.1 1 x2 h8.2.1 1 (by simp [hx12])) jw
      (rS ⟨j1 h2',rG j2⟩)
  .
   by_cases jr:z=x4
   . exact pD (h6 x1 h8.1 1) jw (mUr _ (jr ▸ h8.2.2.2))
   .
    exact pD (h7 x1 h8.1 1 x4 h8.2.2.2 0 (by intro h;exact hx1C ((Prod.mk.inj h).1 ▸ jh))) jw
     (rS ⟨h9 h4',rG jr⟩)
 have ke:Disjoint (F3' \ {x3}) W1:=by
  rw[dL];intro z kj wp
  rcases pU wp with h1 | h4'
  .
   rcases pU h1 with h2 | h2'
   .
    rcases pU h2 with h3 | z2
    .
     rcases pU h3 with js | z3
     . exact pD (h6 x3 h8.2.2.1 0) kj (mUl _ js)
     .
      by_cases j5:z=x1
      . exact pD (h6 x3 h8.2.2.1 0) kj (mUr _ (j5 ▸ h8.1))
      .
       exact pD (h7 x3 h8.2.2.1 0 x1 h8.1 0 (by intro h;exact hx1C ((Prod.mk.inj h).1.symm ▸ jp))) kj
        (rS ⟨j7 z3,rG j5⟩)
    .
     by_cases j2:z=x2
     . exact pD (h6 x3 h8.2.2.1 0) kj (mUr _ (j2 ▸ h8.2.1))
     .
      exact pD (h7 x3 h8.2.2.1 0 x2 h8.2.1 0 (by intro h;exact hx2C ((Prod.mk.inj h).1.symm ▸ jp))) kj
       (rS ⟨j6 z2,rG j2⟩)
   .
    by_cases j2:z=x2
    . exact pD (h6 x3 h8.2.2.1 0) kj (mUr _ (j2 ▸ h8.2.1))
    .
     exact pD (h7 x3 h8.2.2.1 0 x2 h8.2.1 1 (by simp)) kj
      (rS ⟨j1 h2',rG j2⟩)
  .
   by_cases jr:z=x4
   . exact pD (h6 x3 h8.2.2.1 0) kj (mUr _ (jr ▸ h8.2.2.2))
   .
    exact pD (h7 x3 h8.2.2.1 0 x4 h8.2.2.2 0 (by simp [z7])) kj
     (rS ⟨h9 h4',rG jr⟩)
 obtain ⟨P,wh,hP_len,jk⟩ :=
  je x1 x3 F1' F3' W1 D1 w0 kz (λ h=>hx1C (h ▸ jp))
   k8 wa kg ke
   (rD λ z jw kj=>by
    by_cases j5:z=x1
    . exact pD (h6 x3 h8.2.2.1 0) (rS ⟨kj,λ h=>hx1C ((j5.symm.trans (pSg h)) ▸ jp)⟩) (mUr _ (j5 ▸ h8.1))
    .
     by_cases z6:z=x3
     . exact pD (h6 x1 h8.1 1) (rS ⟨jw,rG j5⟩) (mUl _ (z6 ▸ jp))
     .
      exact pD (h7 x1 h8.1 1 x3 h8.2.2.1 0 (by simp))
       (rS ⟨jw,rG j5⟩) (rS ⟨kj,rG z6⟩))
   z1
 let W2:=C∪F1∪F2∪P.support.toFinset
 have w9:W2⊆S:=uS (uS (uS j9 jf.1) ja.1)
  (λ z hz=>q0w P hx1S z (pTf hz))
 have z0:(#W2:O)*(log n)^3<=10*((D2 - 1:ℕ):O):=by
  have h1:#W2<=m+D+D+(3*m+1):=by
   have hc1:=cUl (C∪F1∪F2) P.support.toFinset;have zy:=cUl (C∪F1) F2;have zx:=cUl C F1;have hc4:=q0y P;rw[ja.2.2.1] at zy;rw[jf.2.2.1] at zx;dsimp only[W2];omega
  have z5:#W2<=5*m*D:=by nlinarith only[h1,jg,hD1]
  have h1R:(#W2:O)<=5*(m:O)*(D:O):=by exact_mod_cast z5
  have h2:5*(m:O)*(D:O)*(log n)^3<=5*(D2:O)/10:=by
   have jz:=mlL j8 (show (0:O)<=5*(m:O)*(D:O) by positivity)
   have zn:(D2:O)=(m:O)*((m:O)*(D:O)):=by dsimp only[D2];push_cast;ring
   linarith only[jz,zn,
    show 5*(m:O)*(D:O)*(10*(log n)^3)=10*(5*(m:O)*(D:O)*(log n)^3) by ring,
    show 5*(m:O)*(D:O)*(m:O)=5*((m:O)*((m:O)*(D:O))) by ring]
  have h3:(D2:O) - 1=((D2 - 1:ℕ):O):=by rw[Nat.cast_sub (by omega),Nat.cast_one]
  have w1:(2:O)<=(D2:O):=by exact_mod_cast k7
  have jz:=mlR h1R (show (0:O)<=(log n)^3 by positivity);linarith only[jz,h2,h3,w1]
 have kf:Disjoint (F2' \ {x2}) W2:=by
  rw[dL];intro z k4 wp
  rcases pU wp with h1 | wq
  .
   rcases pU h1 with h2 | z2
   .
    rcases pU h2 with js | z3
    . exact pD (h6 x2 h8.2.1 1) (sSs j1 sR k4) (mUl _ js)
    .
     by_cases j5:z=x1
     . exact pD (h6 x2 h8.2.1 1) (sSs j1 sR k4) (mUr _ (j5 ▸ h8.1))
     .
      exact pD (h7 x2 h8.2.1 1 x1 h8.1 0 (by simp))
       (sSs j1 sR k4) (rS ⟨j7 z3,rG j5⟩)
   .
    have wn:=(pS k4).2 ∘ mSg.mpr
    exact pD (h7 x2 h8.2.1 1 x2 h8.2.1 0 (by simp))
     (sSs j1 sR k4) (rS ⟨j6 z2,rG wn⟩)
  .
   have wo:z∈W1:=mUl _ (mUr _ (pS k4).1)
   rcases jk z (pTf wq) wo with rfl | rfl
   . exact pD (h6 x2 h8.2.1 1) (sSs j1 sR k4) (mUr _ h8.1)
   . exact pD (h6 x2 h8.2.1 1) (sSs j1 sR k4) (mUr _ h8.2.2.1)
 have kd:Disjoint (F4' \ {x4}) W2:=by
  rw[dL];intro z kk wp
  rcases pU wp with h1 | wq
  .
   rcases pU h1 with h2 | z2
   .
    rcases pU h2 with js | z3
    . exact pD (h6 x4 h8.2.2.2 0) (sSs h9 sR kk) (mUl _ js)
    .
     by_cases j5:z=x1
     . exact pD (h6 x4 h8.2.2.2 0) (sSs h9 sR kk) (mUr _ (j5 ▸ h8.1))
     .
      exact pD (h7 x4 h8.2.2.2 0 x1 h8.1 0 (by intro h;exact hx1C ((Prod.mk.inj h).1.symm ▸ jh)))
       (sSs h9 sR kk) (rS ⟨j7 z3,rG j5⟩)
   .
    by_cases j2:z=x2
    . exact pD (h6 x4 h8.2.2.2 0) (sSs h9 sR kk) (mUr _ (j2 ▸ h8.2.1))
    .
     exact pD (h7 x4 h8.2.2.2 0 x2 h8.2.1 0 (by intro h;exact hx2C ((Prod.mk.inj h).1.symm ▸ jh)))
      (sSs h9 sR kk) (rS ⟨j6 z2,rG j2⟩)
  .
   have wo:z∈W1:=mUr _ (pS kk).1
   rcases jk z (pTf wq) wo with rfl | rfl
   . exact pD (h6 x4 h8.2.2.2 0) (sSs h9 sR kk) (mUr _ h8.1)
   . exact pD (h6 x4 h8.2.2.2 0) (sSs h9 sR kk) (mUr _ h8.2.2.1)
 obtain ⟨Q,wg,hQ_len,k6⟩ :=
  je x2 x4 F2' F4' W2 D2 jm jl (λ h=>hx2C (h ▸ jh))
   k7 w9 kf kd
   (rD λ z k4 kk=>by
    by_cases j2:z=x2
    . exact pD (h6 x4 h8.2.2.2 0) (rS ⟨h9 kk,λ h=>hx2C ((j2.symm.trans (pSg h)) ▸ jh)⟩) (mUr _ (j2 ▸ h8.2.1))
    .
     by_cases jr:z=x4
     . exact pD (h6 x2 h8.2.1 1) (rS ⟨j1 k4,rG j2⟩) (mUl _ (jr ▸ jh))
     .
      exact pD (h7 x2 h8.2.1 1 x4 h8.2.2.2 0 (by simp))
       (rS ⟨j1 k4,rG j2⟩) (rS ⟨h9 kk,rG jr⟩))
   z0
 let A:=(P.support.toFinset∪Q.support.toFinset∪C) \ {x1,x2}
 have w3:C⊆A:=λ z hz=>rS
  ⟨mUr _ hz,λ h=>by simp only[mem_insert,mSg] at h;rcases h with rfl | rfl;exact hx1C hz;exact hx2C hz⟩
 have w4:A⊆S:=sS.trans (uS (uS
  (λ z hz=>q0w P hx1S z (pTf hz))
  (λ z hz=>q0w Q hx2S z (pTf hz))) j9)
 have jc:Disjoint F1 C:=rD λ z hzF js=>by
  by_cases j5:z=x1
  . exact hx1C (j5 ▸ js)
  . exact pD (h6 x1 h8.1 0) (rS ⟨j7 hzF,rG j5⟩) (mUl _ js)
 have jb:Disjoint F2 C:=rD λ z hzF js=>by
  by_cases j2:z=x2
  . exact hx2C (j2 ▸ js)
  . exact pD (h6 x2 h8.2.1 0) (rS ⟨j6 hzF,rG j2⟩) (mUl _ js)
 have jt:Disjoint F1 F2:=rD λ z jw k4=>by
  by_cases j5:z=x1
  . subst j5;exact pD (h6 x2 h8.2.1 0) (rS ⟨j6 k4,rG hx12⟩) (mUr _ h8.1)
  .
   by_cases j2:z=x2
   . subst j2;exact pD (h6 x1 h8.1 0) (rS ⟨j7 jw,rG hx12.symm⟩) (mUr _ h8.2.1)
   .
    exact pD (h7 x1 h8.1 0 x2 h8.2.1 0 (by simp [hx12]))
     (rS ⟨j7 jw,rG j5⟩)
     (rS ⟨j6 k4,rG j2⟩)
 have k3:Disjoint A F1:=rD λ z hzA hzF1=>by
  obtain ⟨zo,jd⟩:=pS hzA;have j5:z≠x1:=λ h=>jd (by rw[h];exact mem_insert_self x1 {x2})
  have j2:z≠x2:=λ h=>jd (by rw[h];exact mem_insert_of_mem (mSs x2))
  rcases pU zo with h1 | js
  .
   rcases pU h1 with wq | zp
   .
    rcases jk z (pTf wq) (mUl _ (mUl _ (mUl _ (mUr _ hzF1)))) with rfl | rfl
    . exact j5 rfl
    . exact pD jc hzF1 jp
   .
    rcases k6 z (pTf zp) (mUl _ (mUl _ (mUr _ hzF1))) with rfl | rfl
    . exact j2 rfl
    . exact pD jc hzF1 jh
  . exact pD jc hzF1 js
 have k2:Disjoint A F2:=rD λ z hzA hzF2=>by
  obtain ⟨zo,jd⟩:=pS hzA;have j5:z≠x1:=λ h=>jd (by rw[h];exact mem_insert_self x1 {x2})
  have j2:z≠x2:=λ h=>jd (by rw[h];exact mem_insert_of_mem (mSs x2))
  rcases pU zo with h1 | js
  .
   rcases pU h1 with wq | zp
   .
    rcases jk z (pTf wq) (mUl _ (mUl _ (mUr _ hzF2))) with rfl | rfl
    . exact j5 rfl
    . exact pD jb hzF2 jp
   .
    rcases k6 z (pTf zp) (mUl _ (mUr _ hzF2)) with rfl | rfl
    . exact j2 rfl
    . exact pD jb hzF2 jh
  . exact pD jb hzF2 js
 have wi:#A<=10*m*1:=by
  have h1:#A<=#(P.support.toFinset∪Q.support.toFinset∪C):=cL sS;have h2:=cUl (P.support.toFinset∪Q.support.toFinset) C;have h3:=cUl P.support.toFinset Q.support.toFinset;have h4:=q0y P;have h5:=q0y Q;omega
 have kw:∀ w∈P.support,w∈Q.support->False:=λ w w6 hwQ=>by
  rcases k6 w hwQ (mUr _ (rT w6)) with w5 | hw4
  .
   rw[w5] at w6
   rcases jk x2 w6 (mUl _ (mUl _ (mUr _ ja.2.1))) with h | h
   . exact hx12 h.symm
   . exact hx2C (h ▸ jp)
  .
   rw[hw4] at w6
   rcases jk x4 w6 (mUl _ (mUl _ (mUl _ (mUl _ jh)))) with h | h
   . exact hx1C (h ▸ jh)
   . exact z7 h.symm
 have kv:∀ (R:(q3 H S).Walk x3 x4),R.IsPath->(∀ w∈R.support,w∈c.support) ->
   ∃ p:(q3 H (A∪{x1,x2})).Walk x1 x2,p.IsPath/\p.length=P.length+R.length+Q.length:=by
  intro R wb jj
  have ku:(P.append R).IsPath:=q0x P R wh wb λ w w6 z8=>by
   rcases jk w w6 (mUl _ (mUl _ (mUl _ (mUl _ (rT (jj w z8)))))) with rfl | rfl
   . exact absurd (rT (jj w z8)) hx1C
   . rfl
  have kh:((P.append R).append Q.reverse).IsPath:=q0x (P.append R) Q.reverse ku wg.reverse λ w ws w5=>by
   rw[q0q] at w5;rw[wSa] at ws
   rcases ws with w6 | z8
   . exact (kw w w6 w5).elim
   .
    rcases k6 w w5 (mUl _ (mUl _ (mUl _ (rT (jj w z8))))) with rfl | rfl
    . exact absurd (rT (jj w z8)) hx2C
    . rfl
  have za:∀ w∈((P.append R).append Q.reverse).support,w∈A∪{x1,x2}:=λ w hw=>by
   by_cases h12:w∈({x1,x2}:FS V)
   . exact mUr _ h12
   .
    refine mUl _ (rS ⟨?_,h12⟩);rw[wSa,wSa,q0q] at hw
    rcases hw with (hP | hR) | hQ
    . exact mUl _ (mUl _ (rT hP))
    . exact mUr _ (rT (jj w hR))
    . exact mUl _ (mUr _ (rT hQ))
  refine ⟨q0r ((P.append R).append Q.reverse) za,q0v _ _ kh,?_⟩;rw[q0t,wLa,wLa,wLr]
 refine ⟨F1,F2,A,P.length+R1.length+Q.length,
  ⟨w4,k3,k2,jt,jf,ja,wi,λ i hi=>?_⟩,w3⟩
 rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hi with rfl | rfl
 . obtain ⟨p,hp,zu⟩:=kv R1 kt we;exact ⟨p,hp,by omega⟩
 .
  obtain ⟨p,hp,zu⟩:=kv R2 ks wc
  have hR2_eq:R2.length=R1.length+2:=by dsimp [i0,j0] at wf wd;omega
  exact ⟨p,hp,by omega⟩
def q1o {V:Type*} (H:SG V) (S U U1 L:FS V)
  (m_rob m_min l0 q:ℕ)
  (v1 v2:Fin q->V) (F1 F2 A:Fin q->FS V) (mA lA:Fin q->ℕ):Prop :=
 (∀ i,m_min<=mA i/\mA i<=m_rob) /\
 (∀ i,q1h H (S \ U) (mA i^2) (mA i) 1 (v1 i) (F1 i) (v2 i) (F2 i) (A i) (lA i)) /\
 (∀ i,F1 i∪F2 i⊆S \ L) /\
 (∀ i,Disjoint (qs H (S \ L) (10*l0) (F1 i∪F2 i)) (U1 \ L)) /\
 (∀ i j,i≠j->Disjoint (qs H (S \ L) (5*l0) (F1 i∪F2 i)) (qs H (S \ L) (5*l0) (F1 j∪F2 j)))
lemma q1p {V:Type*} {H:SG V} {S0 S1 A1 A2 Targ C0:FS V} {a b:V} (P:(q3 H S0).Walk a b) (h9:S1⊆S0) (hA2:A2⊆S1) (hb:b∈Targ) (hC0:C0⊆P.support.toFinset) (h7:∀ a'∈A1∪A2,∀ b'∈Targ,∀ q:(q3 H S0).Walk a' b',P.length<=q.length) : q06 H S1 A2 C0 4:=by
 intro l hl1;let E:=qn H S1 (qs H (S1 \ C0) (l - 1) A2);have h6:E∩C0⊆E∩P.support.toFinset:=inter_subset_inter_left hC0
 have h3:=q0Q P E l (λ w hw hwE=>by
  obtain ⟨h5,_,u,j0,huw⟩:=(qo H S1 _ w).mp hwE;obtain ⟨a0,ha0,q0,_,hq0len,_⟩:=qB (qw H sS (l - 1) A2 j0);have h4:a0∈A2:=(pI ha0).1;have h2:∀ z∈q0.support,z∈S0:=λ z hz=>h9 (q0w q0 (hA2 h4) z hz)
  have h8:(q3 H S0).Adj u w:=q0o huw (h9 (qt H S1 (l - 1) A2 (qw H sS _ _ j0))) (h9 h5);let h0:(q3 H S0).Walk a0 w:=(q0r q0 h2).concat h8;let h1:=h0.append (P.dropUntil w hw);have hle:=h7 a0 (mUr _ h4) b hb h1
  have hspec:(P.takeUntil w hw).length+(P.dropUntil w hw).length=P.length:=by
   rw[<- wLa,take_spec P hw]
  have hq_len:h0.length<=l:=by dsimp only[h0];rw[length_concat,q0t];omega
  rw[wLa] at hle;omega)
 exact (cL h6).trans (h3.trans (by omega))
lemma q1q {V:Type*} {H:SG V} {S U Forb:FS V} {v x:V} {D m_rob:ℕ} (hD1:1<=D) (hUS:U⊆S) (j1:v∈S \ U) (P:(q3 H (S \ U)).Walk v x) (j3:P.length+1<=2*m_rob) (hdeg:#Forb+D<=#(S.filter (H.Adj x))) (h7:U⊆Forb) (hP_Forb:P.support.toFinset⊆Forb) : ∃ F:FS V,q0z H (S \ U) v D (2*m_rob) F/\Disjoint F (Forb \ P.support.toFinset):=by
 have jc:D<=#((S.filter (H.Adj x)) \ Forb):=by
  have h1:=cSd (S.filter (H.Adj x)) Forb;have h2:=cL (inter_subset_right (s₁:=S.filter (H.Adj x)) (s₂:=Forb));omega
 obtain ⟨X,h6,j0⟩:=exists_subset_card_eq jc
 have j2:X⊆S \ U:=λ z hz=>by
  obtain ⟨hzN,h8⟩:=pS (h6 hz);exact rS ⟨(pF hzN).1,λ hU=>h8 (h7 hU)⟩
 let h0:={x}∪X;have ja:x∈S \ U:=q0w P j1 x (wEm P);have h5:h0⊆S \ U:=uS (sSm ja) j2
 have h3:h0⊆qs H h0 1 {x}:=λ z hz=>by
  have jb:x∈qs H h0 0 {x}:=rI ⟨mSs x,mUl _ (mSs x)⟩
  rcases pU hz with h1 | h2
  . exact mUl _ (pSg h1 ▸ jb)
  .
   by_cases j7:z=x
   . exact mUl _ (j7 ▸ jb)
   .
    exact mUr _ ((qo H h0 _ z).mpr
     ⟨mUr _ h2,λ h=>j7 (pSg (pI h).1),
      x,jb,(pF (pS (h6 h2)).1).2⟩)
 have h9:=q0F P j1 le_rfl h5 (mUl _ (mSs x)) h3
 have j6:D<=#(P.support.toFinset∪h0) :=
  j0 ▸ cL (sUr.trans sUr)
 obtain ⟨F,j4,j5⟩:=q0E h9 hD1 j6;refine ⟨F,q0B j5 j3,rD λ z hzF hzForb=>?_⟩
 obtain ⟨j9,h4⟩:=pS hzForb
 rcases pU (j4 hzF) with hzp | hzf
 . exact h4 hzp
 .
  rcases pU hzf with j7 | hzX
  . have j8:z=x:=pSg j7;rw[j8] at h4;exact h4 (rT (wEm P))
  . exact (pS (h6 hzX)).2 j9
lemma q1s {V:Type*} [Fintype V] {e2:O} {K:ℕ} (z7:0 < e2) (he21:e2 < 1) (H:SG V) (S U U1:FS V) (wv:V->Bool) (d D m_min q:ℕ) (v1 v2:Fin q->V) (F1 F2 A:Fin q->FS V) (mA lA:Fin q->ℕ) (kv:1000<=d) (zm:d<=#S) (za:qk H wv) (hmindeg:∀ v∈S,d<=dS H S v) (zo:U⊆S) (hUcard:#U<=10*D) (kl:U1⊆S) (k7:#U1<=200*D^2) (jt:(#S:O)*(d:O)/4<=∑ v∈S \ U,(dS H (S \ U) v:O)) (zp:1<=D) (kg:¬ ∃ u1 G1 u2 G2 A0 l0,q1h H (S \ U) D (2*floor (21000*(log (#S:O))^3)) 1 u1 G1 u2 G2 A0 l0) (z3:∀ (H':SG V) (S':FS V) (d' D':ℕ) (x0:V) (c:(q3 H' S').Walk x0 x0) (x1 x2:V), d/64<=d'->d'<=#S'->qk H' wv->qQ H' S' (99/10000) (e2*(d':O)) -> (∀ v∈S',d' - 1<=dS H' S' v)->q0G H' S' x0 c -> x1∈S'->x2∈S'->x1≠x2->x1 ∉ c.support.toFinset->x2 ∉ c.support.toFinset -> 1<=D'->(D':O)<=(log (#S':O))^7 -> ∃ G1 G2 A0 l0,q1h H' S' D' (floor (200/(99/10000:O)*(log (#S':O))^3)) 1 x1 G1 x2 G2 A0 l0/\c.support.toFinset⊆A0) (z2:∀ (H':SG V) (S':FS V) (d':ℕ) (x0:V) (c:(q3 H' S').Walk x0 x0) (x1 x2:V), d/64<=d'->d'<=#S'->qk H' wv->qQ H' S' (1/100) (e2*(d':O)) -> (∀ v∈S',d' - 1<=dS H' S' v)->q0G H' S' x0 c -> x1∈S'->x2∈S'->x1≠x2->x1 ∉ c.support.toFinset->x2 ∉ c.support.toFinset -> ∃ G1 G2 A0 l0,q1h H' S' 1 (floor (200/(1/100:O)*(log (#S':O))^3)) 1 x1 G1 x2 G2 A0 l0/\c.support.toFinset⊆A0) (jb:((200*D^2+q*(3*(floor (21000*(log (#S:O))^3))^2)) * ((200*floor (21000*(log (#S:O))^3)*D+1)^(10*floor ((log (log (#S:O)))^20))):O) * (200*floor (21000*(log (#S:O))^3)*D:O)<=(#S:O)*(d:O)/16) (jy:1<=(1/100:O)*(e2*((d/64:ℕ):O)/2)*((1/100:O)/(log (15/2))^2)) (j5:m_min<=floor (200/(99/10000:O)*(log ((d/64 - 1:ℕ):O))^3) /\ ∀ k:ℕ,d/64 - 1<=k->k<=#S -> ((floor (200/(99/10000:O)*(log (k:O))^3):O)^2<=(log (k:O))^7) /\ (floor (200/(99/10000:O)*(log (k:O))^3)<=floor (21000*(log (#S:O))^3)) /\ (2*log (k:O)/log ((d/64 - 1 - 1:ℕ):O)+6 < (k:O))) (hthr_case2:10*D+10*floor (21000*(log (#S:O))^3)+2+2*D <= 200*floor (21000*(log (#S:O))^3)*D) (jc:q1o H S U U1 (S.filter (λ v=>200*floor (21000*(log (#S:O))^3)*D<=dS H S v)) (floor (21000*(log (#S:O))^3)) m_min (floor ((log (log (#S:O)))^20)) q v1 v2 F1 F2 A mA lA) (z4:¬ ∃ v1' v2' F1' F2' A' mA' lA', q1o H S U U1 (S.filter (λ v=>200*floor (21000*(log (#S:O))^3)*D<=dS H S v)) (floor (21000*(log (#S:O))^3)) m_min (floor ((log (log (#S:O)))^20)) (q+1) v1' v2' F1' F2' A' mA' lA'):False:=by
 set n:O:=(#S:O);set m_rob:=floor (21000*(log n)^3);set D_:=200*m_rob*D;set l0:=floor ((log (log n))^20);let L:=S.filter (λ v=>D_<=dS H S v)
 let S':=S \ L;let W:=(U1∪univ.biUnion (λ i:Fin q=>F1 i∪F2 i∪A i)) \ L
 let W':=qs H S' (10*l0) W
 have kp:∀ v∈S',dS H S' v<=D_:=λ v hv=>by
  have wu:dS H S v < D_:=by by_contra zl;push Not at zl;exact (pS hv).2 (rF ⟨(pS hv).1,zl⟩)
  exact (cL (filter_subset_filter _ sS)).trans wu.le
 have jh:∀ v∈S',dS H S v<=D_:=λ v hv=>by
  by_contra zk;push Not at zk;exact (pS hv).2 (rF ⟨(pS hv).1,zk.le⟩)
 have hm_rob_ge1:1<=m_rob:=by
  have h1:=(j5.2 (#S) (by omega) le_rfl).2.1
  have h2:(1:O)<=(log (#S:O)):=by
   have:(1000:O)<=(#S:O):=by exact_mod_cast (kv.trans zm)
   rw[lIe (by linarith)];linarith [e1l]
  have h3:1<=floor (200/(99/10000:O)*(log (#S:O))^3) :=
   nLf (by push_cast;have:(1:O)<=(log (#S:O))^3:=oLp h2;linarith)
  omega
 have kk:#W<=200*D^2+q*(3*m_rob^2):=by
  have h1:#(univ.biUnion (λ i:Fin q=>F1 i∪F2 i∪A i))<=q*(3*m_rob^2):=by
   calc
     _<=∑ i:Fin q,#(F1 i∪F2 i∪A i):=cBu
     _<=∑ _i:Fin q,(3*m_rob^2):=sum_le_sum λ i _=>by
        have:=cUl (F1 i∪F2 i) (A i);have:=cUl (F1 i) (F2 i)
        have hi:=jc.2.1 i;have hm:=(jc.1 i).2
        rw[hi.2.2.2.2.1.2.2.1,hi.2.2.2.2.2.1.2.2.1] at *
        have hA:=hi.2.2.2.2.2.2.1;have hsq:mA i^2<=m_rob^2:=nPl hm 2
        have hm10:10<=m_rob:=by
         have w9:=(j5.2 (#S) (by omega) le_rfl).2.1
         have zg:(1:O)<=(log (#S:O)):=by
          have:(1000:O)<=(#S:O):=by exact_mod_cast (kv.trans zm)
          rw[lIe (by linarith)];linarith [e1l]
         have h3':10<=floor (200/(99/10000:O)*(log (#S:O))^3) :=
          nLf (by push_cast;have:(1:O)<=(log (#S:O))^3:=oLp zg;linarith)
         omega
        nlinarith
     _=q*(3*m_rob^2):=by simp
  exact (cL sS).trans ((cUl _ _).trans (nAa k7 h1))
 have k6:#W'<=(D_+1)^(10*l0)*(200*D^2+q*(3*m_rob^2)):=by
  calc
   #W'<=(D_+1)^(10*l0)*#(W∩S'):=qD H S' W D_ kp (10*l0)
   _<=(D_+1)^(10*l0)*#W:=nMl _ (cL inter_subset_left)
   _<=_:=nMl _ kk
 let S0:=S \ (U∪W')
 have ju:(#S:O)*(d:O)/8<=∑ v∈S0,(dS H S0 v:O):=by
  have wn:∑ v∈S \ U,dS H (S \ U) v<=(∑ v∈S0,dS H S0 v)+2*#W'*D_:=by
   have j8:S \ U=S0∪((S \ U)∩W'):=by
     ext z;simp only[S0,mS,mU,mI];tauto
   have wm:Disjoint S0 ((S \ U)∩W'):=rD λ z wb wa =>
     (pS wb).2 (mUr _ (pI wa).2)
   rw[sum_congr j8 (λ _ _=>rfl),Finset.sum_union wm]
   have h1:∑ v∈S0,dS H (S \ U) v<=(∑ v∈S0,dS H S0 v)+∑ v∈S0,#(W'.filter (H.Adj v)):=by
     rw[<- sum_add_distrib];refine sum_le_sum λ v _=>?_
     have jz:(S \ U).filter (H.Adj v)⊆S0.filter (H.Adj v)∪W'.filter (H.Adj v):=by
       intro u hu;obtain ⟨wd,zi⟩:=pF hu
       by_cases zj:u∈W'
       . exact mUr _ (rF ⟨zj,zi⟩)
       .
        exact mUl _ (rF ⟨rS ⟨(pS wd).1,
         λ h=>by rcases pU h with hU | hW;exact (pS wd).2 hU;exact zj hW⟩,zi⟩)
     exact (cL jz).trans (cUl _ _)
   have h2:∑ v∈S0,#(W'.filter (H.Adj v))<=#W'*D_:=by
     have we:∑ v∈S0,#(W'.filter (H.Adj v))=∑ u∈W',#(S0.filter (H.Adj u)):=by
       simp_rw[card_filter];rw[sum_comm]
       exact sum_congr rfl λ u _=>sum_congr rfl λ v _=>by simp only[H.adj_comm]
     rw[we]
     calc
       ∑ u∈W',#(S0.filter (H.Adj u))<=∑ u∈W',dS H S u :=
         sum_le_sum λ u _=>cL (filter_subset_filter _ sS)
       _<=∑ _u∈W',D_:=sum_le_sum λ u hu=>jh u (qt H S' (10*l0) W hu)
       _=#W'*D_:=by simp
   have h3:∑ v∈(S \ U)∩W',dS H (S \ U) v<=#W'*D_:=by
     calc
       _<=∑ v∈W',dS H S v:=sum_le_sum_of_subset_of_nonneg inter_subset_right (λ _ _ _=>Nat.zero_le _) |>.trans
         (sum_le_sum λ v _=>cL (filter_subset_filter _ sS))
       _<=∑ _v∈W',D_:=sum_le_sum λ v hv=>jh v (qt H S' (10*l0) W hv)
       _=#W'*D_:=by simp
   have h2w:#W'*D_+#W'*D_=2*#W'*D_:=by ring
   linarith only[h1,h2,h3,h2w]
  have w4:∑ v∈S \ U,(dS H (S \ U) v:O)<=(∑ v∈S0,(dS H S0 v:O))+2*(#W':O)*(D_:O):=by
   exact_mod_cast wn
  have zf:(#W':O)*(D_:O)<=(#S:O)*(d:O)/16:=by
   have h1:(#W':O)<=((200*D^2+q*(3*m_rob^2))*((D_+1)^(10*l0)):O):=by
     have:#W'<=(200*D^2+q*(3*m_rob^2))*(D_+1)^(10*l0):=by rw[mul_comm];exact k6
     exact_mod_cast this
   have w1:=mlR h1 (nCn D_);dsimp only[D_,n] at w1 jb ⊢;push_cast at w1 jb ⊢;exact w1.trans jb
  linarith only[jt,w4,zf]
 have w7:S0.Nonempty:=by
  by_contra wk;rw[not_nonempty_iff_eq_empty] at wk;rw[wk,sum_empty] at ju
  have:(0:O) < (#S:O)*(d:O)/8:=by
   have:0 < #S:=by omega
   have:0 < d:=by omega
   positivity
  linarith
 let h4:=d/64
 have ko:8*(h4:O)*(#S0:O)<=∑ v∈S0,(dS H S0 v:O):=by
  have h1:8*(h4:O)<=(d:O)/8:=by
   have:64*h4<=d:=Nat.mul_div_le d 64
   have:64*(h4:O)<=(d:O):=by exact_mod_cast this
   linarith
  have h2:(#S0:O)<=(#S:O):=by exact_mod_cast cL sS
  have h3:8*(h4:O)*(#S0:O)<=(#S:O)*(d:O)/8:=by nlinarith
  linarith
 obtain ⟨H1,S1,_,w8,j9,jd,_,jo,j3⟩ :=
  qV H S0 (d:=h4) (e2:=e2) (by dsimp only[h4];omega) z7 w7 ko
 have jp:qk H1 wv:=λ u v z1=>za u v (w8 z1)
 have j7:h4<=#S1:=by
  obtain ⟨u,hu⟩:=jd;exact (j3 u hu).trans (cL (filter_subset _ _))
 obtain ⟨x0,c,k4⟩:=q0K H1 S1 jd (λ v hv=>by have:=j3 v hv;dsimp only[h4] at *;omega)
 let C:=c.support.toFinset
 have jv:C⊆S1:=by
  have wc:x0∈S1:=by cases c with | nil=>exact absurd rfl k4.1.ne_nil | cons hadj _=>exact hadj.2.1
  intro w hw;exact q0w c wc w (pTf hw)
 have ja:(#C:O)<=2*log (#S1:O)/log ((h4 - 1:ℕ):O)+2:=by
  have z5:=q0L k4 (by dsimp only[h4];omega) j3
  have hce:#C<=c.length:=by
   have wg:=wSn c
   have j8:c.support=c.support.dropLast ++ [x0]:=by simpa [wGl c] using (dropLast_append_getLast wg).symm
   have jz:C⊆c.support.dropLast.toFinset:=λ w hw=>by
     rw[mT] at hw ⊢;rw[j8,mem_append,List.mem_singleton] at hw
     rcases hw with h1 | hwx
     . exact h1
     .
       have h0:0 < c.support.dropLast.length:=by rw[length_dropLast,wLs];have:=k4.1.three_le_length;omega
       have hx0:c.support.dropLast[0]'h0=x0:=by
        have h1:(c.support.dropLast ++ [x0])[0]'(by rw[<- j8];exact length_pos_of_ne_nil wg)=c.support.dropLast[0]'h0:=getElem_append_left h0
        have h2:∀ M:List V,(hm:M=c.support)->M[0]'(hm ▸ length_pos_of_ne_nil wg)=x0:=by
         rintro _ rfl;exact q0N c
        exact h1.symm.trans (h2 _ j8.symm)
       rw[hwx];exact List.mem_iff_getElem.mpr ⟨0,h0,hx0⟩
   calc
     #C<=c.support.dropLast.toFinset.card:=cL jz
     _<=c.support.dropLast.length:=toFinset_card_le _
     _=c.length:=by rw[length_dropLast,wLs];simp
  exact (by exact_mod_cast hce:(#C:O)<=(c.length:O)).trans z5
 by_cases jl:#((S1 \ C)∩L)<=1
 .
  let h7:=S1 \ ((S1 \ C)∩L);have h6:h7⊆S1:=sS
  have h5:h4 - 1<=h7.card:=by
   have h1:=cSd S1 ((S1 \ C)∩L);have h2:=cL (inter_subset_right (s₁:=S1) (s₂:=(S1 \ C)∩L));dsimp only[h7];omega
  have j6:h7.card<=#S:=cL (h6.trans (j9.trans sS))
  have jg:∀ v∈h7,h4 - 1<=dS H1 h7 v:=λ v hv=>by
   have z8:=j3 v (h6 hv)
   have jz:S1.filter (H1.Adj v)⊆h7.filter (H1.Adj v)∪((S1 \ C)∩L):=λ u hu=>by
     obtain ⟨hu1,z1⟩:=pF hu
     by_cases h:u∈(S1 \ C)∩L
     . exact mUr _ h
     . exact mUl _ (rF ⟨rS ⟨hu1,h⟩,z1⟩)
   have h1:=(cL jz).trans (cUl _ _);unfold dS at z8 ⊢;omega
  have k8:qQ H1 h7 (99/10000) (e2*(h4:O)):=by
   intro X hXS1' wq ze;have wr:X⊆S1:=hXS1'.trans h6;have wp:2*#X<=#S1:=ze.trans (cL h6);have wj:=jo X wr wq wp
   have kh:qn H1 S1 X⊆qn H1 h7 X∪((S1 \ C)∩L):=λ z hz=>by
     obtain ⟨ke,ww,u,huX,huz⟩:=(qo H1 S1 X z).mp hz
     by_cases h:z∈(S1 \ C)∩L
     . exact mUr _ h
     . exact mUl _ ((qo H1 h7 X z).mpr ⟨rS ⟨ke,h⟩,ww,u,huX,huz⟩)
   have k0:(#(qn H1 S1 X):O)<=(#(qn H1 h7 X):O)+1:=by
     have h1:#(qn H1 S1 X)<=#(qn H1 h7 X)+1 :=
       (cL kh).trans ((cUl _ _).trans (Nat.add_le_add_left jl _))
     exact_mod_cast h1
   have js:qK (99/10000) (e2*(h4:O)) (#X:O) =
       (99/100:O)*qK (1/100) (e2*(h4:O)) (#X:O):=by
     unfold qK;split_ifs <;> ring
   have k3:1<=(1/100:O)*(qK (1/100) (e2*(h4:O)) (#X:O)*(#X:O)):=by
     have hd_bar_pos:(0:O) < (h4:O):=by exact_mod_cast (show 0 < h4 by dsimp only[h4];omega)
     have ku:=qP (e1:=1/100) (k:=e2*(h4:O)) (x:=e2*(h4:O)/2) (y:=(#X:O))
       (by norm_num) (by positivity) (by linarith only[show 0 < e2*(h4:O) by positivity]) wq
     have kj:qK (1/100) (e2*(h4:O)) (e2*(h4:O)/2)=(1/100:O)/(log (15/2))^2:=by
       rw[qL (by linarith only[show 0 < e2*(h4:O) by positivity])]
       have zb:15*(e2*(h4:O)/2)/(e2*(h4:O))=15/2:=by
        have wg:e2*(h4:O)≠0:=by positivity
        field_simp [wg]
       rw[zb]
     rw[kj] at ku
     linarith only[ku,jy,
       show (1/100:O)*(e2*(h4:O)/2)*((1/100:O)/(log (15/2))^2) =
        (1/100:O)*((1/100:O)/(log (15/2))^2*(e2*(h4:O)/2)) by ring]
   rw[js]
   linarith only[wj,k0,k3,
     show (99/100:O)*qK (1/100) (e2*(h4:O)) (#X:O)*(#X:O) +
       (1/100:O)*(qK (1/100) (e2*(h4:O)) (#X:O)*(#X:O)) =
       qK (1/100) (e2*(h4:O)) (#X:O)*(#X:O) by ring]
  have k5:∀ w∈c.support,w∈h7:=λ w hw =>
   rS ⟨jv (rT hw),λ h=>(pS (pI h).1).2 (rT hw)⟩
  have wo:=q0H k4 h6 k5
  have hrem2:2<=#(h7 \ C):=by
   have h1:(#C:O)+2 < (h7.card:O):=by
     have wu:=(j5.2 h7.card h5 j6).2.2
     have ws:(#S1:O)<=(h7.card:O)+1:=by
       have z9:=cSd S1 ((S1 \ C)∩L);have zn:=cL (inter_subset_right (s₁:=S1) (s₂:=(S1 \ C)∩L));exact_mod_cast (show #S1<=h7.card+1 by dsimp only[h7];omega)
     have jn:log (#S1:O)<=log (h7.card:O)+1:=by
       have km:(0:O) < (h7.card:O):=by exact_mod_cast (show 0 < h7.card by dsimp only[h4] at h5;omega)
       have z6:(#S1:O)<=2*(h7.card:O):=by
        have w9:(1:O)<=(h7.card:O):=by exact_mod_cast (show 1<=h7.card by dsimp only[h4] at h5;omega)
        linarith only[ws,w9]
       have wi:log 2<=1:=by rw[Real.log_le_iff_le_exp (by norm_num)];linarith only[e1g]
       calc
        log (#S1:O)<=log (2*(h7.card:O)):=lLl (by positivity) z6
        _=log 2+log (h7.card:O):=log_mul (by norm_num) km.ne'
        _<=log (h7.card:O)+1:=by linarith only[wi]
     have wh:log ((h4 - 1 - 1:ℕ):O)<=log ((h4 - 1:ℕ):O) :=
       lLl (by exact_mod_cast (show 0 < h4 - 1 - 1 by dsimp only[h4];omega)) (by exact_mod_cast (show h4 - 1 - 1<=h4 - 1 by omega))
     have k2:(1:O) < log ((h4 - 1 - 1:ℕ):O):=by
       rw[lIt (by exact_mod_cast (show 0 < h4 - 1 - 1 by dsimp only[h4];omega))]
       have zh:(10:O)<=((h4 - 1 - 1:ℕ):O):=by exact_mod_cast (show 10<=h4 - 1 - 1 by dsimp only[h4];omega)
       linarith only[zh,e1l]
     have wl:2*log (#S1:O)/log ((h4 - 1:ℕ):O) <=
        2*log (h7.card:O)/log ((h4 - 1 - 1:ℕ):O)+2:=by
       have ki:0<=log (#S1:O):=lNn (by exact_mod_cast (show 1<=#S1 by dsimp only[h4] at j7;omega))
       have w9:2*log (#S1:O)/log ((h4 - 1:ℕ):O) <=
         2*(log (h7.card:O)+1)/log ((h4 - 1 - 1:ℕ):O) :=
        div_le_div₀ (by linarith only[ki,jn]) (by linarith only[jn]) (by linarith only[k2]) wh
       have zg:2/log ((h4 - 1 - 1:ℕ):O)<=2:=dLs (by norm_num) k2.le
       have heq:2*(log (h7.card:O)+1)/log ((h4 - 1 - 1:ℕ):O) =
         2*log (h7.card:O)/log ((h4 - 1 - 1:ℕ):O)+2/log ((h4 - 1 - 1:ℕ):O):=by ring
       linarith only[w9,zg,heq]
     dsimp only[h4] at ja wl;linarith only[ja,wl,wu]
   have h1N:#C+2<=h7.card:=by exact_mod_cast h1.le
   have h2:=cSd h7 C;have h3:=cL (inter_subset_right (s₁:=h7) (s₂:=C));omega
  obtain ⟨x1,z0,x2,wy,kf⟩:=one_lt_card.mp (by omega:1 < #(h7 \ C));obtain ⟨hx1S1',w0⟩:=pS z0;obtain ⟨hx2S1',ky⟩:=pS wy;let m1:=floor (200/(99/10000:O)*(log (h7.card:O))^3)
  have w3:m_min<=m1:=j5.1.trans (Nat.floor_mono (mlL
   (pLl (lNn (by exact_mod_cast (show 1<=h4 - 1 by dsimp only[h4];omega)))
     (lLl (by exact_mod_cast (show 0 < h4 - 1 by dsimp only[h4];omega)) (by exact_mod_cast h5)) 3) (by positivity)))
  have w2:m1<=m_rob:=(j5.2 h7.card h5 j6).2.1
  have hm1_ge1:1<=m1:=by
   have w9:(1:O)<=log (h7.card:O):=by
     rw[lIe (by exact_mod_cast (show 0 < h7.card by dsimp only[h4] at h5;omega))]
     have zh:(10:O)<=(h7.card:O):=by exact_mod_cast (show 10<=h7.card by dsimp only[h4] at h5;omega)
     linarith only[zh,e1l]
   exact nLf (by push_cast;have h3:(1:O)<=(log (h7.card:O))^3:=oLp w9;linarith only[h3])
  have jf:h4<=h7.card:=by
   have z8:=jg x1 hx1S1'
   have wu:#(h7.filter (H1.Adj x1)) < h7.card:=card_lt_card
     ⟨filter_subset _ _,λ h=>H1.loopless.irrefl x1 (pF (h hx1S1')).2⟩
   unfold dS at z8;omega
  obtain ⟨G1,G2,A_new,jm,h8,j2⟩ :=
   z3 H1 h7 h4 (m1^2) x0 (q0r c k5) x1 x2 le_rfl jf jp k8 jg wo
     hx1S1' hx2S1' kf (by simpa [q0s,C] using w0) (by simpa [q0s,C] using ky)
     (Nat.one_le_pow 2 m1 (by omega)) (by push_cast;exact (j5.2 h7.card h5 j6).1)
  rw[q0s] at j2;have j4:G1∪G2⊆h7:=uS h8.2.2.2.2.1.1 h8.2.2.2.2.2.1.1
  have jk:G1∪G2⊆S':=λ z hz=>by
   have kr:=j4 hz
   have kw:z ∉ C:=λ hzC=>by
     rcases pU hz with h1 | h2
     . exact pD h8.2.1 (j2 hzC) h1
     . exact pD h8.2.2.1 (j2 hzC) h2
   have ke:=h6 kr;refine rS ⟨sS (j9 ke),λ hzL=>?_⟩
   exact (pS kr).2 (rI ⟨rS ⟨ke,kw⟩,hzL⟩)
  have j1:Disjoint (G1∪G2) W':=rD λ z hzG hzW' =>
   (pS (j9 (h6 (j4 hzG)))).2 (mUr _ hzW')
  have kn:h7⊆S \ U:=h6.trans (j9.trans (sSs sR sUl))
  have h9:q1h H (S \ U) (m1^2) m1 1 x1 G1 x2 G2 A_new jm :=
   q1m w8 (q1j h8 kn)
  refine z4 ⟨Fin.snoc v1 x1,Fin.snoc v2 x2,Fin.snoc F1 G1,Fin.snoc F2 G2,Fin.snoc A A_new,
   Fin.snoc mA m1,Fin.snoc lA jm,?_,?_,?_,?_,?_⟩
  .
   intro i;refine lastCases ?_ ?_ i
   . simp [w3,w2]
   . intro j;simpa using jc.1 j
  .
   intro i;refine lastCases ?_ ?_ i
   . simpa using h9
   . intro j;simpa using jc.2.1 j
  .
   intro i;refine lastCases ?_ ?_ i
   . simpa using jk
   . intro j;simpa using jc.2.2.1 j
  .
   intro i;refine lastCases ?_ ?_ i
   .
     simp only[snoc_last];rw[dL];intro z hzB kd;obtain ⟨a,ha,p,_,wf,_⟩:=qB hzB;have hzW:z∈W:=rS ⟨mUl _ (pS kd).1,(pS kd).2⟩
     have zc:a∈W':=qu H S' (by rw[wLr];exact wf) W
       (qA hzW (rS ⟨kl (pS kd).1,(pS kd).2⟩) p.reverse)
     exact pD j1 (pI ha).1 zc
   . intro j;simpa using jc.2.2.2.1 j
  .
   intro i j hij;revert hij;refine lastCases ?_ ?_ i <;> refine lastCases ?_ ?_ j
   . intro h;exact absurd rfl h
   .
     intro j0 _;simp only[snoc_last,snoc_castSucc];rw[dL];intro z wb wa;obtain ⟨a1,zd,p1,_,hp1,_⟩:=qB wb;obtain ⟨a2,w6,p2,_,hp2,_⟩:=qB wa
     have w5:a2∈W:=rS ⟨mUr _ (mB.mpr ⟨j0,mUv j0,mUl _ (pI w6).1⟩),
       (pS (jc.2.2.1 j0 (pI w6).1)).2⟩
     have k1:=qA w5 (pI w6).2 (p2.append p1.reverse);rw[wLa,wLr] at k1;exact pD j1 (pI zd).1 (qu H S' (by omega) W k1)
   .
     intro j0 _;simp only[snoc_last,snoc_castSucc];rw[dR];intro z wb wa;obtain ⟨a1,zd,p1,_,hp1,_⟩:=qB wb;obtain ⟨a2,w6,p2,_,hp2,_⟩:=qB wa
     have w5:a2∈W:=rS ⟨mUr _ (mB.mpr ⟨j0,mUv j0,mUl _ (pI w6).1⟩),
       (pS (jc.2.2.1 j0 (pI w6).1)).2⟩
     have k1:=qA w5 (pI w6).2 (p2.append p1.reverse);rw[wLa,wLr] at k1;exact pD j1 (pI zd).1 (qu H S' (by omega) W k1)
   . intro j' i' hne';simp only[snoc_castSucc];exact jc.2.2.2.2 i' j' (λ h=>hne' (congrArg Fin.castSucc h))
 .
  push Not at jl
  obtain ⟨x1,z0,x2,wy,kf⟩:=one_lt_card.mp jl;obtain ⟨kz,wz⟩:=pI z0;obtain ⟨kx,wx⟩:=pI wy;obtain ⟨kt,w0⟩:=pS kz;obtain ⟨ks,ky⟩:=pS kx
  obtain ⟨_,_,A_new,jm,h8,_⟩ :=
   z2 H1 S1 h4 x0 c x1 x2 le_rfl j7 jp jo
     (λ v hv=>Nat.le_trans (nSl h4 1) (j3 v hv)) k4 kt ks kf w0 ky
  have je:S1⊆S \ U:=j9.trans (sSs sR sUl);have h9:=q1m w8 (q1j h8 je)
  have hm1_le_mrob:floor (200/(1/100:O)*(log (#S1:O))^3)<=m_rob:=by
   apply Nat.floor_mono
   have h1:log (#S1:O)<=log n:=lLl (by exact_mod_cast (card_pos.mpr jd))
     (by dsimp only[n];exact_mod_cast cL (je.trans sS))
   have h2:=pLl (lNn (by exact_mod_cast (card_pos.mpr jd))) h1 3
   have wt:(200/(1/100:O))=20000:=by norm_num
   have hnn:(0:O)<=(log n)^3:=by positivity
   linarith only[h2,wt,hnn,show 200/(1/100:O)*(log (#S1:O))^3=20000*(log (#S1:O))^3 by rw[wt]]
  have hA_card:#A_new<=10*m_rob:=by have:=h9.2.2.2.2.2.2.1;omega
  let kc:=U∪A_new∪{x1,x2}
  have ka:kc.card+D<=#(S.filter (H.Adj x1)):=by
   have h1:=(pF wz).2;have z9:=cUl (U∪A_new) {x1,x2};have zn:=cUl U A_new;have hc3:=card_le_two (a:=x1) (b:=x2);unfold dS at h1;dsimp only[kc] at ⊢;omega
  obtain ⟨G1,jq,jj⟩:=q1q (m_rob:=m_rob) zp zo (je kt)
   (Walk.nil:(q3 H (S \ U)).Walk x1 x1) (by simp only[length_nil];omega) ka
   (sUl.trans sUl) (by simp [kc])
  let kb:=U∪A_new∪{x1,x2}∪G1
  have k9:kb.card+D<=#(S.filter (H.Adj x2)):=by
   have h1:=(pF wx).2;have z9:=cUl (U∪A_new∪{x1,x2}) G1;have zn:=cUl (U∪A_new) {x1,x2};have hc3:=cUl U A_new;have hc4:=card_le_two (a:=x1) (b:=x2);rw[jq.2.2.1] at z9;unfold dS at h1;dsimp only[kb] at ⊢;omega
  obtain ⟨G2,kq,ji⟩:=q1q (m_rob:=m_rob) zp zo (je ks)
   (Walk.nil:(q3 H (S \ U)).Walk x2 x2) (by simp only[length_nil];omega) k9
   (sUl.trans (sUl.trans sUl)) (by simp [kb])
  have jx:x1 ∉ A_new:=λ h=>pD h9.2.1 h h9.2.2.2.2.1.2.1
  have jw:x2 ∉ A_new:=λ h=>pD h9.2.2.1 h h9.2.2.2.2.2.1.2.1
  have jr:x2 ∉ G1:=λ h=>pD jj h
   (rS ⟨mUr _ (by simp),by simp [kf.symm]⟩)
  exact kg ⟨x1,G1,x2,G2,A_new,jm,
   ⟨h9.1,
    dR.mpr λ z hzG1 hzA=>pD jj hzG1
      (rS ⟨mUl _ (mUr _ hzA),by simp;intro h;exact jx (h ▸ hzA)⟩),
    dR.mpr λ z hzG2 hzA=>pD ji hzG2
      (rS ⟨mUl _ (mUl _ (mUr _ hzA)),by simp;intro h;exact jw (h ▸ hzA)⟩),
    dR.mpr λ z hzG2 hzG1=>pD ji hzG2
      (rS ⟨mUr _ hzG1,by simp;intro h;exact jr (h ▸ hzG1)⟩),
    jq,kq,by omega,h9.2.2.2.2.2.2.2⟩⟩
lemma q1t {e2:O} {K:ℕ} (jp:0 < e2) (hK:1<=K) (d_tp1 d_tp2 h8:ℕ) : ∃ (M0 B0:O), (∀ x:O,M0<=x->(h8:O)<=x^2/\exp 11<=x^2/\20*x<=x^2/(log (x^2))^10) /\ (∀ x:O,B0<=x -> ((64*(max d_tp1 d_tp2:O)+128:O)<=x /\ (1000:O)<=x /\ 1<=(1/100:O)*(e2*(x/64 - 1)/2)*((1/100:O)/(log (15/2))^2) /\ ((max 100 (ceil M0):ℕ):O)+1<=200/(99/10000:O)*(log (x/64 - 2))^3 /\ (exp 2:O)<=x/64 - 3) /\ ((4:O)<=log x /\ (200/(99/10000:O)*(log x)^3)^2<=(log x)^7 /\ 2*log x+6 < x /\ 200*(log x)^(2*K)<=x/2 /\ 10*(log x)^K<=exp ((log (log x))^2) /\ (10*(log (log x))^20+2<=21000*(log x)^3 - 2) /\ (10*(21000*(log x)^3)^2*(log x)^K<=(log x)^(K+10)) /\ ((log x)^(K+10)<=x/25) /\ ((200*(log x)^(2*K)+x^(1/4:O)*(3*(21000*(log x)^3)^2)) * (200*(21000*(log x)^3)*(log x)^K+1)^(10*(log (log x))^20) * (200*(21000*(log x)^3)*(log x)^K)<=x/16) /\ ((10*(log x)^K+x^(1/4:O)*(3*(21000*(log x)^3)^2) * (1+(200*(21000*(log x)^3)*(log x)^K+1)^((log (log x))^20))) <= (1/100:O)*x/(100*(log x)^2)) /\ (x^(1/8:O)<=x^(1/4:O)/4))):=by
 have ja:∀ᶠ x:O in atTop,
   (h8:O)<=x^2/\exp 11<=x^2/\20*x<=x^2/(log (x^2))^10:=by
  filter_upwards [eGe (max (sqrt (h8:O)+1) (exp 6)),
   q01 (C:=20*2^10) 10 (β:=1) (by norm_num)] with x hx hlog10
  rw[r1] at hlog10;have jv:sqrt (h8:O)+1<=x:=lT (lMl _ _) hx;have j2:exp 6<=x:=lT (lMr _ _) hx;have h0:0 < x:=lL2 (ePp 6) j2
  have hlogx_pos:0 < log x:=by
   have:(6:O)<=log x:=by rw[lIe h0];exact j2
   linarith only[this]
  refine ⟨?_,?_,?_⟩
  .
   have h1:sqrt (h8:O)<=x:=by linarith only[jv]
   calc
     (h8:O)=(sqrt (h8:O))^2:=(sq_sqrt (nCn h8)).symm
     _<=x^2:=pLl (Real.sqrt_nonneg _) h1 2
  .
   calc exp 11<=exp 12:=eLe.mpr (by norm_num)
     _=(exp 6)^2:=by rw[<- exp_nat_mul];norm_num
     _<=x^2:=pLl (ePp 6).le j2 2
  .
   have jm:log (x^2)=2*log x:=by rw[lP];ring
   rw[jm,mul_pow,lDi (by positivity)]
   have h1:20*(2^10*(log x)^10)<=x:=by
     linarith only[hlog10,show 20*2^10*(log x)^10=20*(2^10*(log x)^10) by ring]
   have h2:=mlL h1 h0.le
   linarith only[h2,show x*(20*(2^10*(log x)^10))=20*x*(2^10*(log x)^10) by ring,
     show x*x=x^2 by ring]
 rw[eAt] at ja;obtain ⟨M0,hM0⟩:=ja;let h6:=max 100 (ceil M0)
 have j9:Filter.Tendsto (λ x:O=>log (log x)) atTop atTop :=
  tL.comp tL
 have jo:∀ᶠ x:O in atTop,
   (64*(max d_tp1 d_tp2:O)+128:O)<=x /\
   (1000:O)<=x /\
   1<=(1/100:O)*(e2*(x/64 - 1)/2)*((1/100:O)/(log (15/2))^2) /\
   (h6:O)+1<=200/(99/10000:O)*(log (x/64 - 2))^3 /\
   (exp 2:O)<=x/64 - 3:=by
  have h9:Filter.Tendsto (λ x:O=>log (x/64 - 2)) atTop atTop :=
   tL.comp (Filter.Tendsto.atTop_add (Filter.Tendsto.atTop_div_const (by norm_num) Filter.tendsto_id) tendsto_const_nhds)
  let C1:=100000*(log (15/2))^2/e2+1000
  filter_upwards [eGe (max (64*(max d_tp1 d_tp2:O)+128) (max (64*C1+1000) (64*exp 2+1000))),
   h9.eventually_ge_atTop (h6+2:O)] with x hx hl
  have h1:64*(max d_tp1 d_tp2:O)+128<=x:=lT (lMl _ _) hx;have k5:64*C1+1000<=x:=lT (lMl _ _) (lT (lMr _ _) hx);have k4:64*exp 2+1000<=x:=lT (lMr _ _) (lT (lMr _ _) hx);refine ⟨h1,by linarith only[k4,ePp 2],?_,?_,by linarith only[k4]⟩
  .
   have hlog15:0 < log (15/2):=lPs (by norm_num)
   have jw:100000*(log (15/2))^2/e2<=x/64 - 1:=by dsimp only[C1] at k5;linarith only[k5]
   have j8:=mlL jw jp.le;rw[mul_div_cancel₀ _ jp.ne'] at j8;have k1:=dLr j8 (show (0:O)<=20000*(log (15/2))^2 by positivity)
   have jz:100000*(log (15/2))^2/(20000*(log (15/2))^2)=5:=by field_simp;ring
   have jb:e2*(x/64 - 1)/(20000*(log (15/2))^2) =
       (1/100:O)*(e2*(x/64 - 1)/2)*((1/100:O)/(log (15/2))^2):=by field_simp;ring
   linarith only[k1,jz,jb]
  .
   have j1:(1:O)<=log (x/64 - 2):=by linarith only[hl,show (0:O)<=(h6:O) from nCn h6]
   have h1':(h6:O)+1<=(log (x/64 - 2))^3:=by
     calc
       (h6:O)+1<=log (x/64 - 2):=by linarith only[hl]
       _=(log (x/64 - 2))^1:=(pow_one _).symm
       _<=(log (x/64 - 2))^3:=pLr j1 (by omega)
   have j7:(0:O)<=(log (x/64 - 2))^3:=pow_nonneg (by linarith only[j1]) 3;linarith only[h1',j7]
 have jd:∀ᶠ x:O in atTop,
   (4:O)<=log x/\(200/(99/10000:O)*(log x)^3)^2<=(log x)^7 /\
   2*log x+6 < x/\200*(log x)^(2*K)<=x/2 /\
   10*(log x)^K<=exp ((log (log x))^2) /\
   10*(log (log x))^20+2<=21000*(log x)^3 - 2 /\
   10*(21000*(log x)^3)^2*(log x)^K<=(log x)^(K+10) /\
   (log x)^(K+10)<=x/25/\x^(1/8:O)<=x^(1/4:O)/4:=by
  filter_upwards [lGe (max 4 ((200/(99/10000:O))^2+10*21000^2+1)),
   q01 (C:=400) (2*K) (β:=1) (by norm_num),
   q01 (C:=25) (K+10) (β:=1) (by norm_num),
   q01 (C:=4) 1 (β:=1) (by norm_num),
   q04 (C:=10) (K:=(K:O)),
   q02 (C:=1) 20 (β:=3) (by norm_num),
   eGe ((4:O)^(8:ℕ))] with x hl h400 h25 h4 hpoly hll20 hx48
  rw[r1] at h400 h25 h4;rw[pow_one] at h4;rw[one_mul,Real.rpow_ofNat] at hll20;rw[rN] at hpoly;have jh:4<=log x:=lT (lMl _ _) hl;have ju:(200/(99/10000:O))^2+10*21000^2+1<=log x:=lT (lMr _ _) hl
  have j1:1<=log x:=by linarith only[jh]
  have h0:0 < x:=lL2 (by positivity) hx48;refine ⟨jh,?_,by linarith only[h4,hx48,show (100:O)<=(4:O)^(8:ℕ) by norm_num],by linarith only[h400],hpoly,?_,?_,by linarith only[h25],?_⟩
  .
   rw[mul_pow,<- pow_mul]
   have h1:=mlR (show (200/(99/10000:O))^2<=log x by linarith only[ju])
     (show (0:O)<=(log x)^6 by positivity)
   linarith only[h1,show log x*(log x)^6=(log x)^7 by ring]
  . have h3:(1:O)<=(log x)^3:=oLp j1;linarith only[hll20,h3]
  .
   rw[mul_pow,<- pow_mul]
   have h1:10*21000^2<=(log x)^4:=by
     calc
       10*21000^2<=log x:=by linarith only[ju]
       _=(log x)^1:=(pow_one _).symm
       _<=(log x)^4:=pLr j1 (by omega)
   have h2:=mlR h1 (show (0:O)<=(log x)^6*(log x)^K by positivity)
   have je:(log x)^4*((log x)^6*(log x)^K)=(log x)^(K+10):=by
     rw[<- mul_assoc,<- pow_add,<- pow_add];congr 1;omega
   linarith only[h2,je,show 10*(21000^2*(log x)^(3*2))*(log x)^K =
       10*21000^2*((log x)^6*(log x)^K) by ring]
  .
   have jy:4<=x^(1/8:O):=by
     have h1:=rLl (by positivity) hx48 (show (0:O)<=1/8 by norm_num);rw[<- rN,<- rpow_mul (by norm_num)] at h1;norm_num at h1;exact h1
   have ji:x^(1/4:O)=x^(1/8:O)*x^(1/8:O):=by rw[<- rpow_add h0];norm_num
   rw[ji];nlinarith only[jy,rpow_pos_of_pos h0 (1/8:O)]
 have jc:∀ᶠ x:O in atTop,
   ((200*(log x)^(2*K)+x^(1/4:O)*(3*(21000*(log x)^3)^2)) *
     (200*(21000*(log x)^3)*(log x)^K+1)^(10*(log (log x))^20) *
     (200*(21000*(log x)^3)*(log x)^K)<=x/16) /\
   ((10*(log x)^K+x^(1/4:O)*(3*(21000*(log x)^3)^2) *
     (1+(200*(21000*(log x)^3)*(log x)^K+1)^((log (log x))^20))) <=
     (1/100:O)*x/(100*(log x)^2)):=by
  let E1:=10*(K+5:O)
  filter_upwards [q03 (C:=E1) 21 (β:=1/4) (by norm_num),
   q01 (C:=10^16) (2*K+10) (β:=1/4) (by norm_num),
   j9.eventually_ge_atTop 2,lGe (max 4 (200*21000+2)),
   eGe ((10^6:O)^(4:ℕ))] with x hexp21 hlogbig hll hl hxbig
  have jh:4<=log x:=lT (lMl _ _) hl;have ju:200*21000+2<=log x:=lT (lMr _ _) hl
  have j1:1<=log x:=by linarith only[jh]
  have hl0:0<=log x:=by linarith only[jh]
  have hll0:0<=log (log x):=by linarith only[hll]
  have h0:0 < x:=lL2 (by positivity) hxbig
  have jf:200*(21000*(log x)^3)*(log x)^K+1<=(log x)^(K+5):=by
   have h1:(1:O)<=(log x)^3*(log x)^K :=
     one_le_mul_of_one_le_of_one_le (oLp j1) (oLp j1)
   have h2:(200*21000+1)*((log x)^3*(log x)^K)<=log x*((log x)^3*(log x)^K) :=
     mlR (by linarith only[ju]) (by positivity)
   have h3:log x*((log x)^3*(log x)^K)<=(log x)^(K+5):=by
     have je:log x*((log x)^3*(log x)^K)=(log x)^(K+4):=by
       rw[<- mul_assoc,<- pow_succ',<- pow_add];congr 1;omega
     rw[je];exact pLr j1 (by omega)
   linarith only[h1,h2,h3,
     show 200*(21000*(log x)^3)*(log x)^K=(200*21000)*((log x)^3*(log x)^K) by ring]
  have j0:(200*(21000*(log x)^3)*(log x)^K+1)^(10*(log (log x))^20)<=x^(1/4:O):=by
   have h1:=rLl (by positivity) jf (show (0:O)<=10*(log (log x))^20 by positivity)
   have jb:((log x)^(K+5))^(10*(log (log x))^20) =
       exp (log (log x)*(((K:O)+5)*(10*(log (log x))^20))):=by
     rw[<- rN (log x) (K+5),<- rpow_mul hl0,rpow_def_of_pos (by linarith only[jh])];push_cast;rfl
   rw[jb] at h1;refine h1.trans ((eLe.mpr ?_).trans hexp21);dsimp only[E1]
   linarith only[show log (log x)*(((K:O)+5)*(10*(log (log x))^20)) =
       10*((K:O)+5)*(log (log x))^21 by ring]
  have j3:(200*(21000*(log x)^3)*(log x)^K+1)^((log (log x))^20)<=x^(1/4:O):=by
   have jr:(1:O)<=200*(21000*(log x)^3)*(log x)^K+1:=by
     linarith only[show (0:O)<=200*(21000*(log x)^3)*(log x)^K by positivity]
   have k0:(log (log x))^20<=10*(log (log x))^20:=by
     linarith only[show (0:O)<=(log (log x))^20 by positivity]
   exact (rLe jr k0).trans j0
  have h7:(10^6:O)<=x^(1/4:O):=by
   have h1:=rLl (by positivity) hxbig (show (0:O)<=1/4 by norm_num);rw[<- rN,<- rpow_mul (by positivity)] at h1;rw[show ((4:ℕ):O)*(1/4:O)=1 by norm_num,r1] at h1;exact h1
  have jx:x^(3/4:O)=x^(1/4:O)*x^(1/4:O)*x^(1/4:O):=by
   rw[<- rpow_add h0,<- rpow_add h0];norm_num
  have k3:x=x^(3/4:O)*x^(1/4:O):=by rw[<- rpow_add h0];norm_num
  have jn:(200*(log x)^(2*K)+x^(1/4:O)*(3*(21000*(log x)^3)^2)) *
     (200*(21000*(log x)^3)*(log x)^K)<=x^(1/2:O):=by
   have h1:200*(log x)^(2*K)<=x^(1/4:O):=by
     have j4:=pLr j1 (show 2*K<=2*K+10 by omega)
     have j7:(0:O)<=(log x)^(2*K+10):=by positivity
     linarith only[j4,hlogbig,j7]
   have h2:(3*(21000*(log x)^3)^2+1)*(200*(21000*(log x)^3)*(log x)^K) <=
       (10^16:O)*(log x)^(2*K+10):=by
     have jk:(log x)^9*(log x)^K<=(log x)^(2*K+10):=by
       rw[<- pow_add];exact pLr j1 (by omega)
     have jj:(log x)^3*(log x)^K<=(log x)^(2*K+10):=by
       rw[<- pow_add];exact pLr j1 (by omega)
     have j5:(3*(21000*(log x)^3)^2+1)*(200*(21000*(log x)^3)*(log x)^K) =
         (3*200*21000^3:O)*((log x)^9*(log x)^K) +
         (200*21000:O)*((log x)^3*(log x)^K):=by ring
     have hm1:=mlL jk (by norm_num:(0:O)<=3*200*21000^3);have hm2:=mlL jj (by norm_num:(0:O)<=200*21000)
     have j7:(0:O)<=(log x)^(2*K+10):=by positivity
     have jq:=mlR (show (3*200*21000^3:O)+200*21000<=10^16 by norm_num) j7
     linarith only[j5,hm1,hm2,jq,
       show ((3*200*21000^3:O)+200*21000)*(log x)^(2*K+10) =
         (3*200*21000^3:O)*(log x)^(2*K+10)+(200*21000:O)*(log x)^(2*K+10) by ring]
   have ji:x^(1/2:O)=x^(1/4:O)*x^(1/4:O):=by rw[<- rpow_add h0];norm_num
   rw[ji]
   calc
     _<=(x^(1/4:O)*(3*(21000*(log x)^3)^2+1))*(200*(21000*(log x)^3)*(log x)^K) :=
         mlR (by linarith only[h1,show x^(1/4:O)*(3*(21000*(log x)^3)^2+1)=x^(1/4:O)*(3*(21000*(log x)^3)^2)+x^(1/4:O) by ring]) (by positivity)
     _=x^(1/4:O)*((3*(21000*(log x)^3)^2+1)*(200*(21000*(log x)^3)*(log x)^K)):=by ring
     _<=x^(1/4:O)*x^(1/4:O):=mlL (h2.trans hlogbig) (by positivity)
  constructor
  .
   have j8:=mLm jn j0 (by positivity) (by positivity)
   have ji:x^(1/2:O)*x^(1/4:O)=x^(3/4:O):=by rw[<- rpow_add h0];norm_num
   have jt:(16:O)<=x^(1/4:O):=lT (by norm_num) h7
   have h16:x^(3/4:O)<=x/16:=by
     conv_rhs=>rw[k3]
     have hm:=mlL jt (rNn h0.le (3/4:O));linarith only[hm]
   linarith only[j8,ji,h16,show (200*(log x)^(2*K)+x^(1/4:O)*(3*(21000*(log x)^3)^2)) *
       (200*(21000*(log x)^3)*(log x)^K+1)^(10*(log (log x))^20) *
       (200*(21000*(log x)^3)*(log x)^K) =
       ((200*(log x)^(2*K)+x^(1/4:O)*(3*(21000*(log x)^3)^2)) *
       (200*(21000*(log x)^3)*(log x)^K)) *
       (200*(21000*(log x)^3)*(log x)^K+1)^(10*(log (log x))^20) by ring]
  .
   rw[lDi (by positivity)]
   have h2:100*(log x)^2*(3*(21000*(log x)^3)^2)*2 <=
       (10^16:O)*(log x)^(2*K+10):=by
     have j4:(log x)^8<=(log x)^(2*K+10):=pLr j1 (by omega)
     have je:100*(log x)^2*(3*(21000*(log x)^3)^2)*2 =
         (600*21000^2:O)*(log x)^8:=by ring
     have hm:=mlL j4 (by norm_num:(0:O)<=600*21000^2)
     have j7:(0:O)<=(log x)^(2*K+10):=by positivity
     linarith only[je,hm,j7]
   have h3:100*(log x)^2*(10*(log x)^K)<=x^(1/4:O):=by
     have j4:(log x)^(K+2)<=(log x)^(2*K+10):=pLr j1 (by omega)
     have je:100*(log x)^2*(10*(log x)^K)=1000*(log x)^(K+2):=by
       rw[pow_add];ring
     have hm:=mlL j4 (by norm_num:(0:O)<=1000)
     have j7:(0:O)<=(log x)^(2*K+10):=by positivity
     linarith only[je,hm,hlogbig,j7]
   have h4:1+(200*(21000*(log x)^3)*(log x)^K+1)^((log (log x))^20) <=
       2*x^(1/4:O):=by linarith only[j3,h7]
   have h5:(x^(1/4:O)*(3*(21000*(log x)^3)^2) *
       (1+(200*(21000*(log x)^3)*(log x)^K+1)^((log (log x))^20)))*(100*(log x)^2) <=
       x^(3/4:O):=by
     have jl:(3*(21000*(log x)^3)^2)*(100*(log x)^2)*2<=x^(1/4:O):=by
       linarith only[h2,hlogbig,
         show (3*(21000*(log x)^3)^2)*(100*(log x)^2)*2 =
          100*(log x)^2*(3*(21000*(log x)^3)^2)*2 by ring]
     rw[jx]
     calc
       _<=x^(1/4:O)*(3*(21000*(log x)^3)^2)*(2*x^(1/4:O))*(100*(log x)^2) :=
          mlR (mlL h4 (by positivity)) (by positivity)
       _=x^(1/4:O)*x^(1/4:O)*((3*(21000*(log x)^3)^2)*(100*(log x)^2)*2):=by ring
       _<=x^(1/4:O)*x^(1/4:O)*x^(1/4:O):=mlL jl (by positivity)
   have j6:x^(1/4:O)<=x^(3/4:O):=rLe (by linarith only[hxbig]) (by norm_num);have jg:(200:O)<=x^(1/4:O):=lT (by norm_num) h7
   have k2:2*x^(3/4:O)<=(1/100:O)*x:=by
     conv_rhs=>rw[k3]
     have hm:=mlL jg (rNn h0.le (3/4:O));linarith only[hm]
   have j5:(10*(log x)^K+x^(1/4:O)*(3*(21000*(log x)^3)^2) *
       (1+(200*(21000*(log x)^3)*(log x)^K+1)^((log (log x))^20)))*(100*(log x)^2) =
       100*(log x)^2*(10*(log x)^K)+(x^(1/4:O)*(3*(21000*(log x)^3)^2) *
       (1+(200*(21000*(log x)^3)*(log x)^K+1)^((log (log x))^20)))*(100*(log x)^2):=by ring
   linarith only[j5,h3,h5,j6,k2]
 have js:∀ᶠ x:O in atTop,
   ((64*(max d_tp1 d_tp2:O)+128:O)<=x /\
    (1000:O)<=x /\
    1<=(1/100:O)*(e2*(x/64 - 1)/2)*((1/100:O)/(log (15/2))^2) /\
    (h6:O)+1<=200/(99/10000:O)*(log (x/64 - 2))^3 /\
    (exp 2:O)<=x/64 - 3) /\
   ((4:O)<=log x /\
    (200/(99/10000:O)*(log x)^3)^2<=(log x)^7 /\
    2*log x+6 < x /\
    200*(log x)^(2*K)<=x/2 /\
    10*(log x)^K<=exp ((log (log x))^2) /\
    (10*(log (log x))^20+2<=21000*(log x)^3 - 2) /\
    (10*(21000*(log x)^3)^2*(log x)^K<=(log x)^(K+10)) /\
    ((log x)^(K+10)<=x/25) /\
    ((200*(log x)^(2*K)+x^(1/4:O)*(3*(21000*(log x)^3)^2)) *
      (200*(21000*(log x)^3)*(log x)^K+1)^(10*(log (log x))^20) *
      (200*(21000*(log x)^3)*(log x)^K)<=x/16) /\
    ((10*(log x)^K+x^(1/4:O)*(3*(21000*(log x)^3)^2) *
      (1+(200*(21000*(log x)^3)*(log x)^K+1)^((log (log x))^20))) <=
      (1/100:O)*x/(100*(log x)^2)) /\
    (x^(1/8:O)<=x^(1/4:O)/4)):=by
  filter_upwards [jo,jd,jc] with x hd hA hB
  exact ⟨hd,hA.1,hA.2.1,hA.2.2.1,hA.2.2.2.1,hA.2.2.2.2.1,hA.2.2.2.2.2.1,hA.2.2.2.2.2.2.1,hA.2.2.2.2.2.2.2.1,hB.1,hB.2,hA.2.2.2.2.2.2.2.2⟩
 rw[eAt] at js;obtain ⟨B0,hB0⟩:=js;exact ⟨M0,B0,hM0,hB0⟩
lemma q1u {V:Type*}
  (H:SG V) (S U L:FS V) (D m_rob l0 mA_i lA_i:ℕ)
  (va vb a x:V) (Fa Fb A_i:FS V)
  (Q:(q3 H Fa).Walk va a) (P':(q3 H (S \ (U∪A_i))).Walk a x)
  (QP:(q3 H (S \ U)).Walk va x)
  (js:U⊆S) (hUcard:#U<=10*D) (ji:1<=D)
  (h4:10<=m_rob) (h5:10*l0+2<=m_rob) (hmA_le:mA_i<=m_rob)
  (j5:∀ z∈L,z∈S/\200*m_rob*D<=dS H S z)
  (j8:¬ ∃ u1 G1 u2 G2 A0 lA0,q1h H (S \ U) D (2*m_rob) 1 u1 G1 u2 G2 A0 lA0)
  (h0:q1h H (S \ U) (mA_i^2) mA_i 1 va Fa vb Fb A_i lA_i)
  (j6:Fb⊆S \ L) (jp:x∈L)
  (hQPl:QP.length<=mA_i+l0)
  (je:QP.support.toFinset⊆(A_i∪Q.support.toFinset∪{x})∪(P'.support.toFinset \ ((A_i∪Q.support.toFinset∪{x})∪Fb)))
  (j1:Disjoint QP.support.toFinset A_i) :
  let Bs_i:=A_i∪Q.support.toFinset∪{x}
  let Cs_i:=P'.support.toFinset \ (Bs_i∪Fb)
  Disjoint (qs H (S \ (U∪Bs_i∪Cs_i)) l0 Fb) L:=by
 intro Bs_i Cs_i;rw[dL];intro y hyB hyL;obtain ⟨b0,jr,R,_,hR_len,_⟩:=qB hyB;have jn:b0∈Fb:=(pI jr).1
 have h2:∀ w∈R.support,w∈S \ (U∪Bs_i∪Cs_i):=λ w hw =>
  q0w R (pI jr).2 w hw
 have jh:∀ w∈R.support,w∈S \ U:=λ w hw =>
  rS ⟨(pS (h2 w hw)).1,λ hU =>
    (pS (h2 w hw)).2 (mUl _ (mUl _ hU))⟩
 obtain ⟨b1,jm,R1r,_,j4,j3,_⟩ :=
  q13 (q0r R jh).reverse Fb jn
 let R1:=R1r.reverse;obtain ⟨s2,_,hs2_len⟩:=q0C h0.2.2.2.2.2.1 jm
 let R':(q3 H (S \ U)).Walk vb y :=
  (q0r s2 (λ w hw=>h0.2.2.2.2.2.1.1 (q0w s2 h0.2.2.2.2.2.1.2.1 w hw))).append R1
 have hR'_len:R'.length<=mA_i+l0:=by
  dsimp only[R',R1];rw[wLa,q0t,wLr]
  have:R1r.length<=R.length:=j4.trans (by rw[wLr,q0t])
  omega
 have h3:Disjoint R'.support.toFinset (Bs_i∪Cs_i):=by
  rw[dL];intro w hwR' jg;dsimp only[R',R1] at hwR';rw[mT,wSa,q0s,q0q] at hwR'
  rcases hwR' with jj | jf
  .
    have j7:w∈Fb:=q0w s2 h0.2.2.2.2.2.1.2.1 w jj
    rcases pU jg with jl | jk
    .
      rcases pU jl with h1 | hwx
      .
       rcases pU h1 with hwA | hwQ
       . exact pD h0.2.2.1 hwA j7
       . exact pD h0.2.2.2.1 (q0w Q h0.2.2.2.2.1.2.1 w (pTf hwQ)) j7
      . exact (pS (j6 j7)).2 (pSg hwx ▸ jp)
    . exact (pS jk).2 (mUr _ j7)
  .
    have jq:w∈R.support:=by
      have:=j3 w jf;rwa [q0q,q0s] at this
    rcases pU jg with jl | jk
    . exact (pS (h2 w jq)).2 (mUl _ (mUr _ jl))
    . exact (pS (h2 w jq)).2 (mUr _ jk)
 let jd:=U∪A_i∪QP.support.toFinset∪R'.support.toFinset
 have jb:jd.card+D<=#(S.filter (H.Adj x)):=by
  have hdx:=(j5 x jp).2;have hc1:=cUl (U∪A_i∪QP.support.toFinset) R'.support.toFinset;have hc2:=cUl (U∪A_i) QP.support.toFinset;have hc3:=cUl U A_i;have hc4:=q0y QP;have hc5:=q0y R';have hA:=h0.2.2.2.2.2.2.1
  have jo:10*D+12*m_rob+2*l0+2+D<=200*m_rob*D:=by
    nlinarith only[ji,h4,h5]
  unfold dS at hdx;dsimp only[jd] at ⊢;omega
 obtain ⟨G1,j2,h9⟩:=q1q (m_rob:=m_rob) ji js (h0.2.2.2.2.1.1 h0.2.2.2.2.1.2.1)
  QP (by omega) jb
  (sUl.trans (sUl.trans sUl))
  (sUr.trans sUl)
 let jc:=U∪A_i∪QP.support.toFinset∪R'.support.toFinset∪G1
 have ja:jc.card+D<=#(S.filter (H.Adj y)):=by
  have hdy:=(j5 y hyL).2;have hc0:=cUl (U∪A_i∪QP.support.toFinset∪R'.support.toFinset) G1;have hc1:=cUl (U∪A_i∪QP.support.toFinset) R'.support.toFinset;have hc2:=cUl (U∪A_i) QP.support.toFinset;have hc3:=cUl U A_i;have hc4:=q0y QP;have hc5:=q0y R';have hA:=h0.2.2.2.2.2.2.1;rw[j2.2.2.1] at hc0
  have jo:10*D+12*m_rob+2*l0+2+2*D<=200*m_rob*D:=by
    nlinarith only[ji,h4,h5]
  unfold dS at hdy;dsimp only[jc] at ⊢;omega
 obtain ⟨G2,j9,h7⟩:=q1q (m_rob:=m_rob) ji js (h0.2.2.2.2.2.1.1 h0.2.2.2.2.2.1.2.1)
  R' (by omega) ja
  (sUl.trans (sUl.trans (sUl.trans sUl)))
  (sUr.trans sUl)
 have j0:Disjoint R'.support.toFinset A_i :=
  disjoint_of_subset_right (sUl.trans (sUl.trans sUl)) h3
 have h6:Disjoint R'.support.toFinset QP.support.toFinset :=
  disjoint_of_subset_right je h3
 have h8:Disjoint G1 R'.support.toFinset:=rD λ z hz1 hzR =>
  pD h9 hz1 (rS ⟨mUr _ hzR,λ h=>pD h6 hzR h⟩)
 exact j8 ⟨va,G1,vb,G2,A_i,lA_i,
  ⟨h0.1,
   dR.mpr λ z hz1 hzA=>pD h9 hz1
     (rS ⟨mUl _ (mUl _ (mUr _ hzA)),λ h=>pD j1 h hzA⟩),
   dR.mpr λ z hz2 hzA=>pD h7 hz2
     (rS ⟨mUl _ (mUl _ (mUl _ (mUr _ hzA))),λ h=>pD j0 h hzA⟩),
   dR.mpr λ z hz2 hz1=>pD h7 hz2
     (rS ⟨mUr _ hz1,λ h=>pD h8 hz1 h⟩),
   j2,j9,by have:=h0.2.2.2.2.2.2.1;omega,h0.2.2.2.2.2.2.2⟩⟩
lemma q1v {V:Type*} {K:ℕ} (H:SG V) (S U L:FS V) (D m_rob l0 mA_j lA_j:ℕ) (va vb a x:V) (Fa Fb A_j:FS V) (Q:(q3 H Fa).Walk va a) (P':(q3 H (S \ (U∪A_j))).Walk a x) (QP:(q3 H (S \ U)).Walk va x) (hUS:U⊆S) (hUcard:#U<=10*D) (jl:1<=D) (hDK:(D:O)<=(log (#S:O))^K) (jk:4<=log (#S:O)) (h7:10<=m_rob) (j1:10*l0+2<=m_rob) (hmA_le:mA_j<=m_rob) (jc:∀ z∈L,z∈S/\200*m_rob*D<=dS H S z) (j4:¬ ∃ u1 G1 u2 G2 A0 lA0,q1h H (S \ U) D (2*m_rob) 1 u1 G1 u2 G2 A0 lA0) (h3:q1h H (S \ U) (mA_j^2) mA_j 1 va Fa vb Fb A_j lA_j) (j2:Fb⊆S \ L) (jm:x∈L) (hQPl:QP.length<=mA_j+l0) (jb:QP.support.toFinset⊆(A_j∪Q.support.toFinset∪{x})∪(P'.support.toFinset \ ((A_j∪Q.support.toFinset∪{x})∪Fb))) (h8:Disjoint QP.support.toFinset A_j) (ja:(log (#S:O))^(K+10) <= (#(qs H (S \ (U∪(A_j∪Q.support.toFinset∪{x})∪(P'.support.toFinset \ ((A_j∪Q.support.toFinset∪{x})∪Fb)))) l0 Fb):O)) : False:=by
 let j7:=A_j∪Q.support.toFinset∪{x};let jg:=P'.support.toFinset \ (j7∪Fb);let h0:=S \ (U∪j7∪jg)
 have j0:Fb⊆h0:=λ z hz=>rS
  ⟨sS (h3.2.2.2.2.2.1.1 hz),λ h=>by
    rcases pU h with h1 | hC
    .
      rcases pU h1 with hU | hB
      . exact (pS (h3.2.2.2.2.2.1.1 hz)).2 hU
      .
       rcases pU hB with h2 | hzx
       .
        rcases pU h2 with jh | hzQ
        . exact pD h3.2.2.1 jh hz
        . exact pD h3.2.2.2.1 (q0w Q h3.2.2.2.2.1.2.1 z (pTf hzQ)) hz
       . exact (pS (j2 hz)).2 (pSg hzx ▸ jm)
    . exact (pS hC).2 (mUr _ hz)⟩
 have j3:D<=#(qs H h0 (mA_j+l0) {vb}):=by
  have jj:qs H h0 l0 Fb⊆qs H h0 (mA_j+l0) {vb}:=by
    rw[qy];exact qv H h0 l0 (h3.2.2.2.2.2.1.2.2.2.trans (qw H j0 mA_j {vb}))
  have jf:(D:O)<=(log (#S:O))^(K+10):=hDK.trans (pLr (by linarith only[jk]) (by omega))
  have j9:(#(qs H h0 l0 Fb):O)<=(#(qs H h0 (mA_j+l0) {vb}):O):=by
    exact_mod_cast cL jj
  dsimp only[h0,j7,jg] at j9;exact_mod_cast (jf.trans (ja.trans j9))
 obtain ⟨G2,j5,h9⟩:=q0E (q0D H h0 (mA_j+l0) (j0 h3.2.2.2.2.2.1.2.1)) jl j3
 have jd:q0z H (S \ U) vb D (2*m_rob) G2 :=
  q0B (q0A h9 (λ z hz=>rS ⟨(pS hz).1,λ hU=>(pS hz).2 (mUl _ (mUl _ hU))⟩))
    (by omega)
 let ji:=U∪A_j∪G2∪QP.support.toFinset
 have je:ji.card+D<=#(S.filter (H.Adj x)):=by
  have hdx:=(jc x jm).2;have hc1:=cUl (U∪A_j∪G2) QP.support.toFinset;have hc2:=cUl (U∪A_j) G2;have hc3:=cUl U A_j;have hc4:=q0y QP;have hA:=h3.2.2.2.2.2.2.1;rw[h9.2.2.1] at hc2
  have h10D:10*D+11*m_rob+l0+1+2*D<=200*m_rob*D:=by
    nlinarith only[jl,h7,j1]
  unfold dS at hdx;dsimp only[ji] at ⊢;omega
 obtain ⟨G1,j6,h6⟩:=q1q (m_rob:=m_rob) jl hUS (h3.2.2.2.2.1.1 h3.2.2.2.2.1.2.1)
  QP (by omega) je
  (sUl.trans (sUl.trans sUl))
  sUr
 have h4:Disjoint G2 (j7∪jg):=rD λ z hz2 hzBC=>by
  have j8:=qt H h0 _ _ (j5 hz2)
  rcases pU hzBC with hB | hC
  . exact (pS j8).2 (mUl _ (mUr _ hB))
  . exact (pS j8).2 (mUr _ hC)
 have h5:Disjoint G2 QP.support.toFinset:=disjoint_of_subset_right jb h4
 exact j4 ⟨va,G1,vb,G2,A_j,lA_j,
  ⟨h3.1,
   dR.mpr λ z hz1 jh=>pD h6 hz1
     (rS ⟨mUl _ (mUl _ (mUr _ jh)),λ h=>pD h8 h jh⟩),
   dR.mpr λ z hz2 jh=>pD h4 hz2
     (mUl _ (mUl _ (mUl _ jh))),
   rD λ z hz1 hz2=>pD h6 hz1
     (rS ⟨mUl _ (mUr _ hz2),λ h=>pD h5 hz2 h⟩),
   j6,jd,by have:=h3.2.2.2.2.2.2.1;omega,h3.2.2.2.2.2.2.2⟩⟩
lemma q1w {V:Type*} {e2:O} {K:ℕ}
  (H:SG V) (S U U0 U1 L:FS V) (d D m_rob m_min l0 d_nb q:ℕ)
  (v1 v2:Fin q->V) (F1 F2 A:Fin q->FS V) (mA lA:Fin q->ℕ)
  (ja:U0=(S \ U).filter (λ v=>d/2<=#(U.filter (H.Adj v))))
  (j9:U1=U∪U0)
  (jh:L=S.filter (λ v=>200*m_rob*D<=dS H S v))
  (ka:U⊆S) (j5:#U<=10*D)
  (kc:1<=D) (hDK:(D:O)<=(log (#S:O))^K) (k2:4<=log (#S:O))
  (hm_min1:1<=m_min)
  (j1:¬ ∃ u1 G1 u2 G2 A0 lA0,q1h H (S \ U) D (2*m_rob) 1 u1 G1 u2 G2 A0 lA0)
  (hnb:∀ {ι:Type} (I:FS ι) (As Bs Cs:ι->FS V),
   (#S:O)^(1/8:O)<=(#I:O) ->
   (∀ i∈I,d_nb<=#(As i)) ->
   (∀ i∈I,As i⊆S \ U/\Bs i⊆S \ U/\Cs i⊆S \ U/\Disjoint (Bs i∪Cs i) (As i)) ->
   (∀ i∈I,(#(Bs i):O)<=(#(As i):O)/(log (#(As i):O))^10) ->
   (∀ i∈I,q06 H (S \ (U∪Bs i)) (As i) (Cs i) 4) ->
   (∀ i∈I,∀ v∈qs H (S \ (U∪Bs i∪Cs i)) l0 (As i),
     (#(U.filter (H.Adj v)):O)<=(d:O)/2) ->
   (∀ i∈I,∀ j∈I,i≠j ->
     Disjoint (qs H (S \ (U∪Bs i∪Cs i)) l0 (As i))
      (qs H (S \ (U∪Bs j∪Cs j)) l0 (As j))) ->
   ∃ i∈I,(log (#S:O))^(K+10) <=
     (#(qs H (S \ (U∪Bs i∪Cs i)) l0 (As i)):O))
  (h6:10<=m_rob)
  (h7:10*l0+2<=m_rob)
  (j4:∀ i:Fin q,d_nb<=(mA i)^2 /\
   (20*(mA i:O)<=((mA i^2:ℕ):O)/(log ((mA i^2:ℕ):O))^10) /\
   exp 11<=((mA i^2:ℕ):O))
  (h3:q1o H S U U1 L m_rob m_min l0 q v1 v2 F1 F2 A mA lA) :
  let HasLPath:Fin q->Prop:=λ i =>
   ∃ a∈F1 i∪F2 i,∃ x∈L \ U,∃ p:(q3 H (S \ (U∪A i))).Walk a x,p.length<=l0
  (#((univ:FS (Fin q)).filter HasLPath):O) < (#S:O)^(1/8:O):=by
 intro HasLPath;let S':=S \ L;let j7:=(univ:FS (Fin q)).filter HasLPath
 have h8:∀ z∈L,z∈S/\200*m_rob*D<=dS H S z:=λ z hz=>by
  rw[jh] at hz;exact pF hz
 have je:∀ v∈S \ U,v ∉ U0->#(U.filter (H.Adj v)) < d/2:=λ v hv hv0=>by
  by_contra hge';push Not at hge';exact hv0 (ja ▸ rF ⟨hv,hge'⟩)
 by_contra k6;push Not at k6
 have jj:∀ i∈j7,∃ (va vb a x:V) (Fa Fb:FS V)
   (P':(q3 H (S \ (U∪A i))).Walk a x) (Q:(q3 H Fa).Walk va a),
   q1h H (S \ U) (mA i^2) (mA i) 1 va Fa vb Fb (A i) (lA i) /\
   Fa∪Fb=F1 i∪F2 i/\a∈Fa/\x∈(L \ U) \ A i /\
   P'.IsPath/\P'.length<=l0/\Q.IsPath/\Q.length<=mA i /\
   (∀ w∈P'.support,w∈Fa∪Fb->w=a) /\
   (∀ a'∈Fa∪Fb,∀ x'∈(L \ U) \ A i,∀ r:(q3 H (S \ (U∪A i))).Walk a' x',P'.length<=r.length):=by
  intro i hi;obtain ⟨a0,k9,x0,hx0,p0,ju⟩:=(pF hi).2
  have h9:F1 i∪F2 i⊆S \ (U∪A i):=λ z hz=>rS
   ⟨sS (by rcases pU hz with h1 | h2;exact (h3.2.1 i).2.2.2.2.1.1 h1;exact (h3.2.1 i).2.2.2.2.2.1.1 h2),
    λ h=>by
     rcases pU h with hU | hA
     .
      rcases pU hz with h1 | h2
      . exact (pS ((h3.2.1 i).2.2.2.2.1.1 h1)).2 hU
      . exact (pS ((h3.2.1 i).2.2.2.2.2.1.1 h2)).2 hU
     .
      rcases pU hz with h1 | h2
      . exact pD (h3.2.1 i).2.1 hA h1
      . exact pD (h3.2.1 i).2.2.1 hA h2⟩
  have jb:x0∈(L \ U) \ A i:=rS ⟨hx0,λ hA =>
   (pS (q0w p0 (h9 k9) x0 (wEm p0))).2 (mUr _ hA)⟩
  obtain ⟨a,x,ha,hx,P',jl,jm,jn,_,j6⟩ :=
   qE h9 (λ z hz=>rS
     ⟨(h8 z (pS (pS hz).1).1).1,λ h=>by
      rcases pU h with hU | hA
      . exact (pS (pS hz).1).2 hU
      . exact (pS hz).2 hA⟩) ⟨a0,k9,x0,jb,p0,ju⟩
  rcases pU ha with k8 | k7
  .
   obtain ⟨Q,k3,k4⟩:=q0C (h3.2.1 i).2.2.2.2.1 k8
   exact ⟨v1 i,v2 i,a,x,F1 i,F2 i,P',Q,h3.2.1 i,rfl,k8,hx,jl,jm,k3,k4,jn,
     λ a' ha' b' hb'=>j6 a' b' ha' hb'⟩
  .
   obtain ⟨Q,k3,k4⟩:=q0C (h3.2.1 i).2.2.2.2.2.1 k7
   exact ⟨v2 i,v1 i,a,x,F2 i,F1 i,P',Q,q1i (h3.2.1 i),union_comm _ _,k7,hx,jl,jm,k3,k4,
     λ w hw h=>jn w hw (by rwa [union_comm]),
     λ a' ha' b' hb'=>j6 a' b' (by rwa [union_comm]) hb'⟩
 let ι:={i:Fin q // i∈j7}
 choose va vb a x Fa Fb P' Q hadj_i hFeq_i ha_i hx_i hP'p_i hP'l_i hQp_i hQl_i hP'A_i hP'min_i using λ i:ι=>jj i.1 i.2
 let As:ι->FS V:=λ i=>Fb i
 let Bs:ι->FS V:=λ i=>A i.1∪(Q i).support.toFinset∪{x i}
 let Cs:ι->FS V:=λ i=>(P' i).support.toFinset \ (Bs i∪As i)
 have kb:∀ i:ι,∃ p:(q3 H (S \ U)).Walk (va i) (x i),
   p.IsPath/\p.length<=mA i.1+l0/\p.support.toFinset⊆Bs i∪Cs i /\
   Disjoint p.support.toFinset (A i.1):=λ i=>by
  have jk:∀ w∈(Q i).support,w∈S \ U:=λ w hw =>
   (hadj_i i).2.2.2.2.1.1 (q0w (Q i) (hadj_i i).2.2.2.2.1.2.1 w hw)
  have jg:∀ w∈(P' i).support,w∈S \ U:=λ w hw=>by
   have h1:=q0w (P' i) (rS
     ⟨sS ((hadj_i i).2.2.2.2.1.1 (ha_i i)),λ h=>by
      rcases pU h with hU | hA
      . exact (pS ((hadj_i i).2.2.2.2.1.1 (ha_i i))).2 hU
      . exact pD (hadj_i i).2.1 hA (ha_i i)⟩) w hw
   exact rS ⟨(pS h1).1,λ hU=>(pS h1).2 (mUl _ hU)⟩
  let p:=(q0r (Q i) jk).append (q0r (P' i) jg)
  refine ⟨p,q0x _ _ (q0v _ _ (hQp_i i)) (q0v _ _ (hP'p_i i))
   (λ w hw1 hw2=>hP'A_i i w (by simpa [q0s] using hw2)
     (mUl _ (q0w (Q i) (hadj_i i).2.2.2.2.1.2.1 w (by simpa [q0s] using hw1)))),
   by dsimp only[p];rw[wLa,q0t,q0t];exact nAa (hQl_i i) (hP'l_i i),λ w hw=>?_,?_⟩
  .
   dsimp only[p] at hw;rw[mT,wSa,q0s,q0s] at hw
   rcases hw with js | jo
   . exact mUl _ (mUl _ (mUr _ (rT js)))
   .
     by_cases hB:w∈Bs i
     . exact mUl _ hB
     .
      refine mUr _ (rS ⟨rT jo,λ h=>?_⟩)
      rcases pU h with h1 | h2
      . exact hB h1
      . exact pD (hadj_i i).2.2.2.1 (ha_i i) (hP'A_i i w jo (mUr _ h2) ▸ h2)
  .
   rw[dL];intro w hw k5;dsimp only[p] at hw;rw[mT,wSa,q0s,q0s] at hw
   rcases hw with js | jo
   . exact pD (hadj_i i).2.1 k5 (q0w (Q i) (hadj_i i).2.2.2.2.1.2.1 w js)
   .
     exact (pS (q0w (P' i) (rS
      ⟨sS ((hadj_i i).2.2.2.2.1.1 (ha_i i)),λ h=>by
       rcases pU h with hU | hA'
       . exact (pS ((hadj_i i).2.2.2.2.1.1 (ha_i i))).2 hU
       . exact pD (hadj_i i).2.1 hA' (ha_i i)⟩) w jo)).2 (mUr _ k5)
 have h5:∀ i:ι,Fb i⊆S \ L:=λ i w hw =>
  h3.2.2.1 i.1 (hFeq_i i ▸ mUr _ hw)
 have h0:∀ i:ι,qs H (S \ (U∪Bs i∪Cs i)) l0 (As i)⊆qs H S' l0 (Fb i):=by
  intro i;obtain ⟨QP,_,jf,j0,h4⟩:=kb i
  have j8:=q1u H S U L D m_rob l0 (mA i.1) (lA i.1) (va i) (vb i) (a i) (x i)
   (Fa i) (Fb i) (A i.1) (Q i) (P' i) QP ka j5 kc h6 h7 (h3.1 i.1).2
   h8 j1 (hadj_i i) (h5 i) (pS (pS (hx_i i)).1).1 jf j0 h4
  rw[<- qC H (S \ (U∪Bs i∪Cs i)) L (As i) l0 j8];exact qw H (λ z hz=>rS ⟨(pS (pS hz).1).1,(pS hz).2⟩) l0 (As i)
 have k1:(#S:O)^(1/8:O)<=(#(univ:FS ι):O):=by simpa [ι] using k6
 have k0:∀ i∈(univ:FS ι),d_nb<=#(As i):=λ i _=>by
  rw[(hadj_i i).2.2.2.2.2.1.2.2.1];exact (j4 i.1).1
 have jz:∀ i∈(univ:FS ι),
   As i⊆S \ U/\Bs i⊆S \ U/\Cs i⊆S \ U/\Disjoint (Bs i∪Cs i) (As i):=λ i _ =>
  ⟨(hadj_i i).2.2.2.2.2.1.1,
   uS (uS (hadj_i i).1 (λ z hz=>(hadj_i i).2.2.2.2.1.1 (q0w (Q i) (hadj_i i).2.2.2.2.1.2.1 z (pTf hz))))
     (sSm (rS ⟨(h8 (x i) (pS (pS (hx_i i)).1).1).1,(pS (pS (hx_i i)).1).2⟩)),
   sS.trans (λ z hz=>by
     have h1:=q0w (P' i) (rS
      ⟨sS ((hadj_i i).2.2.2.2.1.1 (ha_i i)),λ h=>by
       rcases pU h with hU | hA
       . exact (pS ((hadj_i i).2.2.2.2.1.1 (ha_i i))).2 hU
       . exact pD (hadj_i i).2.1 hA (ha_i i)⟩) z (pTf hz)
     exact rS ⟨(pS h1).1,λ hU=>(pS h1).2 (mUl _ hU)⟩),
   rD λ z hzBC ji=>by
     rcases pU hzBC with hzB | hzC
     .
      rcases pU hzB with h1 | jp
      .
       rcases pU h1 with jr | jq
       . exact pD (hadj_i i).2.2.1 jr ji
       . exact pD (hadj_i i).2.2.2.1 (q0w (Q i) (hadj_i i).2.2.2.2.1.2.1 z (pTf jq)) ji
      . exact (pS (h5 i ji)).2 (pSg jp ▸ (pS (pS (hx_i i)).1).1)
     . exact (pS hzC).2 (mUr _ ji)⟩
 have jy:∀ i∈(univ:FS ι),(#(Bs i):O)<=(#(As i):O)/(log (#(As i):O))^10:=λ i _=>by
  rw[(hadj_i i).2.2.2.2.2.1.2.2.1]
  have hBc:#(Bs i)<=20*mA i.1:=by
   have hc1:=cUl (A i.1∪(Q i).support.toFinset) {x i};rw[card_singleton] at hc1;have hc2:=cUl (A i.1) (Q i).support.toFinset;have hc3:=q0y (Q i);have hA:=(hadj_i i).2.2.2.2.2.2.1
   have hQ:=hQl_i i;have hm1:1<=mA i.1:=by have:=(h3.1 i.1).1;omega
   dsimp only[Bs];omega
  exact (by exact_mod_cast hBc:(#(Bs i):O)<=20*(mA i.1:O)).trans (j4 i.1).2.1
 have jx:∀ i∈(univ:FS ι),q06 H (S \ (U∪Bs i)) (As i) (Cs i) 4:=λ i _ =>
  q1p (P' i) (sSs sR (union_subset_union_right (sUl.trans sUl)))
   (λ z hz=>rS ⟨sS ((hadj_i i).2.2.2.2.2.1.1 hz),λ h=>by
     rcases pU h with hU | hB
     . exact (pS ((hadj_i i).2.2.2.2.2.1.1 hz)).2 hU
     .
      rcases pU hB with h1 | jp
      .
       rcases pU h1 with ji | jq
       . exact pD (hadj_i i).2.2.1 ji hz
       . exact pD (hadj_i i).2.2.2.1 (q0w (Q i) (hadj_i i).2.2.2.2.1.2.1 z (pTf jq)) hz
      . exact (pS (h5 i hz)).2 (pSg jp ▸ (pS (pS (hx_i i)).1).1)⟩)
   (hx_i i) sS (hP'min_i i)
 have jw:∀ i∈(univ:FS ι),∀ v∈qs H (S \ (U∪Bs i∪Cs i)) l0 (As i),
   (#(U.filter (H.Adj v)):O)<=(d:O)/2:=λ i _ v hv=>by
  have jc:=h0 i hv
  have j2:v ∉ U1 \ L:=pD (h3.2.2.2.1 i.1)
   (qu H S' (show l0<=10*l0 by omega) _ (qv H S' l0 (hFeq_i i ▸ sUr) jc))
  have j3:v ∉ U0:=λ hv0=>j2 (rS ⟨j9 ▸ mUr _ hv0,(pS (qt H S' l0 _ jc)).2⟩)
  have jt:v∈S \ U:=rS ⟨(pS (qt H S' l0 _ jc)).1,λ hU =>
   (pS (qt H _ l0 _ hv)).2 (mUl _ (mUl _ hU))⟩
  have hlt:#(U.filter (H.Adj v)) < d/2:=je v jt j3
  have h1:(#(U.filter (H.Adj v)):O)<=((d/2:ℕ):O):=by exact_mod_cast hlt.le
  have h2:((d/2:ℕ):O)<=(d:O)/2:=by
   have:2*((d/2:ℕ):O)<=(d:O):=by exact_mod_cast Nat.mul_div_le d 2
   linarith only[this]
  linarith only[h1,h2]
 have jv:∀ i∈(univ:FS ι),∀ j'∈(univ:FS ι),i≠j' ->
   Disjoint (qs H (S \ (U∪Bs i∪Cs i)) l0 (As i)) (qs H (S \ (U∪Bs j'∪Cs j')) l0 (As j')):=λ i _ j' _ hij =>
  rD λ v hv1 hv2 =>
   pD (h3.2.2.2.2 i.1 j'.1 (λ h=>hij (Subtype.ext h)))
     (qu H S' (show l0<=5*l0 by omega) _ (qv H S' l0 (hFeq_i i ▸ sUr) (h0 i hv1)))
     (qu H S' (show l0<=5*l0 by omega) _ (qv H S' l0 (hFeq_i j' ▸ sUr) (h0 j' hv2)))
 obtain ⟨j,_,jd⟩:=hnb (univ:FS ι) As Bs Cs k1 k0 jz jy jx jw jv;obtain ⟨QP,_,jf,j0,h4⟩:=kb j
 exact q1v (K:=K) H S U L D m_rob l0 (mA j.1) (lA j.1) (va j) (vb j) (a j) (x j)
  (Fa j) (Fb j) (A j.1) (Q j) (P' j) QP ka j5 kc hDK k2 h6 h7 (h3.1 j.1).2
  h8 j1 (hadj_i j) (h5 j) (pS (pS (hx_i j)).1).1 jf j0 h4 jd
lemma q1x {V:Type*} {K:ℕ} (H:SG V) (S U Z:FS V) (D m_rob l0 mA_j lA_j:ℕ) (va vb a z:V) (Fa Fb A_j:FS V) (P:(q3 H (S \ (U∪A_j))).Walk a z) (Q:(q3 H Fa).Walk va a) (jw:1<=D) (jv:(D:O)<=(log (#S:O))^K) (jn:4<=log (#S:O)) (j3:(log (#S:O))^(K+10)<=(#S:O)/25) (h10l_le_m:10*l0+2<=m_rob) (hmA_le:mA_j<=m_rob) (j8:¬ ∃ u1 G1 u2 G2 A0 lA0,q1h H (S \ U) D (2*m_rob) 1 u1 G1 u2 G2 A0 lA0) (h0:q1h H (S \ U) (mA_j^2) mA_j 1 va Fa vb Fb A_j lA_j) (ha:a∈Fa) (hz:z∈Z) (hPl:P.length<=m_rob/2) (hQl:Q.length<=mA_j) (hPA:∀ w∈P.support,w∈Fa∪Fb->w=a) (jo:Z⊆S \ U) (j0:Disjoint Z A_j) (ja:(#S:O)/25<=(#Z:O)) (j9:∀ u∈Z,Z⊆qs H Z (m_rob/2) {u}) (h8:Disjoint (qs H (S \ (U∪(A_j∪Q.support.toFinset)∪(P.support.toFinset \ ((A_j∪Q.support.toFinset)∪Fb)))) l0 Fb) Z) (ji:(log (#S:O))^(K+10) <= (#(qs H (S \ (U∪(A_j∪Q.support.toFinset)∪(P.support.toFinset \ ((A_j∪Q.support.toFinset)∪Fb)))) l0 Fb):O)) : False:=by
 let jl:=A_j∪Q.support.toFinset;let ju:=P.support.toFinset \ (jl∪Fb);let j6:=S \ (U∪jl∪ju)
 have j5:D<=#(qs H j6 l0 Fb):=by
  have jk:(D:O)<=(log (#S:O))^(K+10):=jv.trans (pLr (by linarith only[jn]) (by omega));exact_mod_cast jk.trans ji
 have h3:Fb⊆j6:=λ w hw=>rS ⟨sS (h0.2.2.2.2.2.1.1 hw),λ h=>by
  rcases pU h with h1 | hC
  .
    rcases pU h1 with hU | hB
    . exact (pS (h0.2.2.2.2.2.1.1 hw)).2 hU
    .
      rcases pU hB with j7 | jm
      . exact pD h0.2.2.1 j7 hw
      . exact pD h0.2.2.2.1 (q0w Q h0.2.2.2.2.1.2.1 w (pTf jm)) hw
  . exact (pS hC).2 (mUr _ hw)⟩
 have jf:q0z H (S \ U) vb #(qs H j6 l0 Fb) (2*m_rob) (qs H j6 l0 Fb):=by
  have jj:j6⊆S \ U:=λ w hw=>rS ⟨(pS hw).1,λ hU=>(pS hw).2 (mUl _ (mUl _ hU))⟩
  refine ⟨(qt H j6 l0 Fb).trans jj,
    qu H j6 (Nat.zero_le l0) Fb (rI ⟨h0.2.2.2.2.2.1.2.1,h3 h0.2.2.2.2.2.1.2.1⟩),rfl,?_⟩
  intro u hu;obtain ⟨b0,hb0,q0,_,hq0l,jt⟩:=qB hu;obtain ⟨s2,_,hs2l⟩:=q0C h0.2.2.2.2.2.1 (pI hb0).1
  have h4:Fb⊆qs H j6 l0 Fb:=λ w hw =>
    qu H j6 (Nat.zero_le l0) Fb (rI ⟨hw,h3 hw⟩)
  let j1:=(q0r s2 (λ w hw=>h4 (q0w s2 h0.2.2.2.2.2.1.2.1 w hw))).append (q0r q0 jt)
  have jh:=qA (mSs vb) (h4 h0.2.2.2.2.2.1.2.1) j1;dsimp only[j1] at jh;rw[wLa,q0t,q0t] at jh;exact qu H _ (by omega) _ jh
 obtain ⟨G2,h5,jb⟩:=q0E jf jw j5
 have jp:∀ w∈Q.support,w∈S \ U:=λ w hw =>
  h0.2.2.2.2.1.1 (q0w Q h0.2.2.2.2.1.2.1 w hw)
 have jq:∀ w∈P.support,w∈S \ U:=λ w hw=>by
  have h1:=q0w P (rS
    ⟨sS (h0.2.2.2.2.1.1 ha),λ h=>by
      rcases pU h with hU | hA
      . exact (pS (h0.2.2.2.2.1.1 ha)).2 hU
      . exact pD h0.2.1 hA ha⟩) w hw
  exact rS ⟨(pS h1).1,λ hU=>(pS h1).2 (mUl _ hU)⟩
 let QP:=(q0r Q jp).append (q0r P jq)
 have jd:=q0F (m1:=mA_j+m_rob/2) QP (h0.2.2.2.2.1.1 h0.2.2.2.2.1.2.1)
  (by dsimp only[QP];rw[wLa,q0t,q0t];exact nAa hQl hPl)
  jo hz (j9 z hz)
 have je:D<=#(QP.support.toFinset∪Z):=by
  have h1:(D:O)<=(#Z:O):=(jv.trans ((pLr (by linarith only[jn]) (by omega:K<=K+10)).trans j3)).trans ja;exact (by exact_mod_cast h1:D<=#Z).trans (cL sUr)
 obtain ⟨G1,h9,jc⟩:=q0E jd jw je;have j4:q0z H (S \ U) va D (2*m_rob) G1:=q0B jc (by omega)
 have j2:∀ w∈QP.support,w ∉ A_j:=λ w hw j7=>by
  dsimp only[QP] at hw;rw[wSa,q0s,q0s] at hw
  rcases hw with jm | jr
  . exact pD h0.2.1 j7 (q0w Q h0.2.2.2.2.1.2.1 w jm)
  .
    exact (pS (q0w P (rS
      ⟨sS (h0.2.2.2.2.1.1 ha),λ h=>by
       rcases pU h with hU | hA
       . exact (pS (h0.2.2.2.2.1.1 ha)).2 hU
       . exact pD h0.2.1 hA ha⟩) w jr)).2 (mUr _ j7)
 have h6:Disjoint QP.support.toFinset G2:=rD λ w h7 hwG2=>by
  have jg:=qt H j6 l0 Fb (h5 hwG2);dsimp only[QP] at h7;rw[mT,wSa,q0s,q0s] at h7
  rcases h7 with jm | jr
  . exact (pS jg).2 (mUl _ (mUr _ (mUr _ (rT jm))))
  .
    by_cases hB:w∈jl
    . exact (pS jg).2 (mUl _ (mUr _ hB))
    .
      by_cases hF:w∈Fb
      . exact pD h0.2.2.2.1 ha (hPA w jr (mUr _ hF) ▸ hF)
      .
       exact (pS jg).2 (mUr _ (rS ⟨rT jr,λ h=>by
        rcases pU h with h1 | h2;exact hB h1;exact hF h2⟩))
 exact j8 ⟨va,G1,vb,G2,A_j,lA_j,
  ⟨h0.1,
   dR.mpr λ w hw1 j7=>by
     rcases pU (h9 hw1) with h7 | js
     . exact j2 w (pTf h7) j7
     . exact pD j0 js j7,
   dR.mpr λ w hw2 j7 =>
     (pS (qt H j6 l0 Fb (h5 hw2))).2 (mUl _ (mUr _ (mUl _ j7))),
   rD λ w hw1 hw2=>by
     rcases pU (h9 hw1) with h7 | js
     . exact pD h6 h7 hw2
     . exact pD h8 (h5 hw2) js,
   j4,jb,by have:=h0.2.2.2.2.2.2.1;omega,h0.2.2.2.2.2.2.2⟩⟩
lemma q1y {V:Type*} {e2:O} {K:ℕ}
  (H:SG V) (S U U0 U1 L Z:FS V) (d D m_rob m_min l0 d_nb q:ℕ)
  (v1 v2:Fin q->V) (F1 F2 A:Fin q->FS V) (mA lA:Fin q->ℕ)
  (A1':FS (Fin q))
  (ja:U0=(S \ U).filter (λ v=>d/2<=#(U.filter (H.Adj v))))
  (j9:U1=U∪U0)
  (hD1:1<=D) (hDK:(D:O)<=(log (#S:O))^K) (jw:4<=log (#S:O))
  (j3:(log (#S:O))^(K+10)<=(#S:O)/25)
  (hm_min1:1<=m_min)
  (j6:¬ ∃ u1 G1 u2 G2 A0 lA0,q1h H (S \ U) D (2*m_rob) 1 u1 G1 u2 G2 A0 lA0)
  (hnb:∀ {ι:Type} (I:FS ι) (As Bs Cs:ι->FS V),
   (#S:O)^(1/8:O)<=(#I:O) ->
   (∀ i∈I,d_nb<=#(As i)) ->
   (∀ i∈I,As i⊆S \ U/\Bs i⊆S \ U/\Cs i⊆S \ U/\Disjoint (Bs i∪Cs i) (As i)) ->
   (∀ i∈I,(#(Bs i):O)<=(#(As i):O)/(log (#(As i):O))^10) ->
   (∀ i∈I,q06 H (S \ (U∪Bs i)) (As i) (Cs i) 4) ->
   (∀ i∈I,∀ v∈qs H (S \ (U∪Bs i∪Cs i)) l0 (As i),
     (#(U.filter (H.Adj v)):O)<=(d:O)/2) ->
   (∀ i∈I,∀ j∈I,i≠j ->
     Disjoint (qs H (S \ (U∪Bs i∪Cs i)) l0 (As i))
      (qs H (S \ (U∪Bs j∪Cs j)) l0 (As j))) ->
   ∃ i∈I,(log (#S:O))^(K+10) <=
     (#(qs H (S \ (U∪Bs i∪Cs i)) l0 (As i)):O))
  (j0:10*l0+2<=m_rob)
  (j1:∀ i:Fin q,d_nb<=(mA i)^2 /\
   (20*(mA i:O)<=((mA i^2:ℕ):O)/(log ((mA i^2:ℕ):O))^10) /\
   exp 11<=((mA i^2:ℕ):O))
  (h0:q1o H S U U1 L m_rob m_min l0 q v1 v2 F1 F2 A mA lA)
  (h4:Z⊆S \ (U∪A1'.biUnion (λ i=>F1 i∪F2 i∪A i) ∪
   qs H (S \ L) l0 ((A1'.biUnion (λ i=>F1 i∪F2 i∪A i)) \ L)))
  (j8:(#S:O)/25<=(#Z:O))
  (j7:∀ z∈Z,Z⊆qs H Z (m_rob/2) {z})
  (h5:∀ i∈A1',∀ (X0 E0:FS V),X0⊆F1 i∪F2 i->E0⊆S \ (U∪A i) ->
   qs H E0 l0 X0⊆qs H (S \ L) l0 X0) :
  let HasZPath:Fin q->Prop:=λ i =>
   ∃ a∈F1 i∪F2 i,∃ z∈Z,∃ p:(q3 H (S \ (U∪A i))).Walk a z,p.length<=m_rob/2
  (#(A1'.filter HasZPath):O) < (#S:O)^(1/8:O):=by
 intro HasZPath;let S':=S \ L;let ji:=A1'.biUnion (λ i=>F1 i∪F2 i∪A i)
 let j5:=A1'.filter HasZPath
 have jg:∀ v∈S \ U,v ∉ U0->#(U.filter (H.Adj v)) < d/2:=λ v hv hv0=>by
  by_contra hge';push Not at hge';exact hv0 (ja ▸ rF ⟨hv,hge'⟩)
 by_contra jz;push Not at jz
 have jf:∀ i∈j5,∃ (va vb a z:V) (Fa Fb:FS V)
   (P:(q3 H (S \ (U∪A i))).Walk a z) (Q:(q3 H Fa).Walk va a),
   q1h H (S \ U) (mA i^2) (mA i) 1 va Fa vb Fb (A i) (lA i) /\
   Fa∪Fb=F1 i∪F2 i/\a∈Fa/\z∈Z /\
   P.IsPath/\P.length<=m_rob/2/\Q.IsPath/\Q.length<=mA i /\
   (∀ w∈P.support,w∈Fa∪Fb->w=a) /\
   (∀ a'∈Fa∪Fb,∀ z'∈Z,∀ r:(q3 H (S \ (U∪A i))).Walk a' z',P.length<=r.length):=by
  intro i hi;obtain ⟨hiA1',hex⟩:=pF hi
  have j4:F1 i∪F2 i⊆S \ (U∪A i):=λ z hz=>rS
   ⟨sS (by rcases pU hz with h1 | h2;exact (h0.2.1 i).2.2.2.2.1.1 h1;exact (h0.2.1 i).2.2.2.2.2.1.1 h2),
    λ h=>by
     rcases pU h with hU | hA
     .
      rcases pU hz with h1 | h2
      . exact (pS ((h0.2.1 i).2.2.2.2.1.1 h1)).2 hU
      . exact (pS ((h0.2.1 i).2.2.2.2.2.1.1 h2)).2 hU
     .
      rcases pU hz with h1 | h2
      . exact pD (h0.2.1 i).2.1 hA h1
      . exact pD (h0.2.1 i).2.2.1 hA h2⟩
  have j2:Z⊆S \ (U∪A i):=λ z hz=>rS
   ⟨(pS (h4 hz)).1,λ h=>by
     rcases pU h with hU | hA
     . exact (pS (h4 hz)).2 (mUl _ (mUl _ hU))
     .
      exact (pS (h4 hz)).2 (mUl _ (mUr _
       (mB.mpr ⟨i,hiA1',mUr _ hA⟩)))⟩
  obtain ⟨a,z,ha,hz,P,k2,k3,k4,_,jb⟩:=qE j4 j2 hex
  rcases pU ha with k1 | k0
  .
   obtain ⟨Q,jx,jy⟩:=q0C (h0.2.1 i).2.2.2.2.1 k1
   exact ⟨v1 i,v2 i,a,z,F1 i,F2 i,P,Q,h0.2.1 i,rfl,k1,hz,k2,k3,jx,jy,k4,
     λ a' ha' b' hb'=>jb a' b' ha' hb'⟩
  .
   obtain ⟨Q,jx,jy⟩:=q0C (h0.2.1 i).2.2.2.2.2.1 k0
   exact ⟨v2 i,v1 i,a,z,F2 i,F1 i,P,Q,q1i (h0.2.1 i),union_comm _ _,k0,hz,k2,k3,jx,jy,
     λ w hw h=>k4 w hw (by rwa [union_comm]),
     λ a' ha' b' hb'=>jb a' b' (by rwa [union_comm]) hb'⟩
 let ι2:={i:Fin q // i∈j5}
 choose va vb a z Fa Fb P Q hadj_i hFeq_i ha_i hz_i hPp_i hPl_i hQp_i hQl_i hPA_i hPmin_i using λ i:ι2=>jf i.1 i.2
 let As:ι2->FS V:=λ i=>Fb i
 let Bs:ι2->FS V:=λ i=>A i.1∪(Q i).support.toFinset
 let Cs:ι2->FS V:=λ i=>(P i).support.toFinset \ (Bs i∪As i)
 have h3:∀ i:ι2,qs H (S \ (U∪Bs i∪Cs i)) l0 (As i)⊆qs H S' l0 (Fb i):=λ i =>
  h5 i.1 (pF i.2).1 (Fb i) (S \ (U∪Bs i∪Cs i))
   (hFeq_i i ▸ sUr)
   (sSs sR (uS
     (sUl.trans sUl)
     (sUl.trans (sUr.trans sUl))))
 have jv:(#S:O)^(1/8:O)<=(#(univ:FS ι2):O):=by simpa [ι2] using jz
 have ju:∀ i∈(univ:FS ι2),d_nb<=#(As i):=λ i _=>by
  rw[(hadj_i i).2.2.2.2.2.1.2.2.1];exact (j1 i.1).1
 have jt:∀ i∈(univ:FS ι2),
   As i⊆S \ U/\Bs i⊆S \ U/\Cs i⊆S \ U/\Disjoint (Bs i∪Cs i) (As i):=λ i _ =>
  ⟨(hadj_i i).2.2.2.2.2.1.1,
   uS (hadj_i i).1 (λ w hw=>(hadj_i i).2.2.2.2.1.1 (q0w (Q i) (hadj_i i).2.2.2.2.1.2.1 w (pTf hw))),
   sS.trans (λ w hw=>by
     have h1:=q0w (P i) (rS
      ⟨sS ((hadj_i i).2.2.2.2.1.1 (ha_i i)),λ h=>by
       rcases pU h with hU | hA
       . exact (pS ((hadj_i i).2.2.2.2.1.1 (ha_i i))).2 hU
       . exact pD (hadj_i i).2.1 hA (ha_i i)⟩) w (pTf hw)
     exact rS ⟨(pS h1).1,λ hU=>(pS h1).2 (mUl _ hU)⟩),
   rD λ w hwBC jc=>by
     rcases pU hwBC with jm | hwC
     .
      rcases pU jm with jn | jl
      . exact pD (hadj_i i).2.2.1 jn jc
      . exact pD (hadj_i i).2.2.2.1 (q0w (Q i) (hadj_i i).2.2.2.2.1.2.1 w (pTf jl)) jc
     . exact (pS hwC).2 (mUr _ jc)⟩
 have js:∀ i∈(univ:FS ι2),(#(Bs i):O)<=(#(As i):O)/(log (#(As i):O))^10:=λ i _=>by
  rw[(hadj_i i).2.2.2.2.2.1.2.2.1]
  have hBc:#(Bs i)<=20*mA i.1:=by
   have hc1:=cUl (A i.1) (Q i).support.toFinset;have hc2:=q0y (Q i);have hA:=(hadj_i i).2.2.2.2.2.2.1;have hQ:=hQl_i i
   have hm1:1<=mA i.1:=by have:=(h0.1 i.1).1;omega
   dsimp only[Bs];omega
  exact (by exact_mod_cast hBc:(#(Bs i):O)<=20*(mA i.1:O)).trans (j1 i.1).2.1
 have jr:∀ i∈(univ:FS ι2),q06 H (S \ (U∪Bs i)) (As i) (Cs i) 4:=λ i _ =>
  q1p (P i) (sSs sR (union_subset_union_right sUl))
   (λ w hw=>rS ⟨sS ((hadj_i i).2.2.2.2.2.1.1 hw),λ h=>by
     rcases pU h with hU | hB
     . exact (pS ((hadj_i i).2.2.2.2.2.1.1 hw)).2 hU
     .
      rcases pU hB with jc | jl
      . exact pD (hadj_i i).2.2.1 jc hw
      . exact pD (hadj_i i).2.2.2.1 (q0w (Q i) (hadj_i i).2.2.2.2.1.2.1 w (pTf jl)) hw⟩)
   (hz_i i) sS (hPmin_i i)
 have jq:∀ i∈(univ:FS ι2),∀ v∈qs H (S \ (U∪Bs i∪Cs i)) l0 (As i),
   (#(U.filter (H.Adj v)):O)<=(d:O)/2:=λ i _ v hv=>by
  have jd:=h3 i hv
  have h7:v ∉ U1 \ L:=pD (h0.2.2.2.1 i.1)
   (qu H S' (show l0<=10*l0 by omega) _ (qv H S' l0 (hFeq_i i ▸ sUr) jd))
  have h8:v ∉ U0:=λ hv0=>h7 (rS ⟨j9 ▸ mUr _ hv0,(pS (qt H S' l0 _ jd)).2⟩)
  have jo:v∈S \ U:=rS ⟨(pS (qt H S' l0 _ jd)).1,λ hU =>
   (pS (qt H _ l0 _ hv)).2 (mUl _ (mUl _ hU))⟩
  have hlt:#(U.filter (H.Adj v)) < d/2:=jg v jo h8
  have h1:(#(U.filter (H.Adj v)):O)<=((d/2:ℕ):O):=by exact_mod_cast hlt.le
  have h2:((d/2:ℕ):O)<=(d:O)/2:=by
   have:2*((d/2:ℕ):O)<=(d:O):=by exact_mod_cast Nat.mul_div_le d 2
   linarith only[this]
  linarith only[h1,h2]
 have jp:∀ i∈(univ:FS ι2),∀ j'∈(univ:FS ι2),i≠j' ->
   Disjoint (qs H (S \ (U∪Bs i∪Cs i)) l0 (As i)) (qs H (S \ (U∪Bs j'∪Cs j')) l0 (As j')):=λ i _ j' _ hij =>
  rD λ v hv1 hv2 =>
   pD (h0.2.2.2.2 i.1 j'.1 (λ h=>hij (Subtype.ext h)))
     (qu H S' (show l0<=5*l0 by omega) _ (qv H S' l0 (hFeq_i i ▸ sUr) (h3 i hv1)))
     (qu H S' (show l0<=5*l0 by omega) _ (qv H S' l0 (hFeq_i j' ▸ sUr) (h3 j' hv2)))
 obtain ⟨j,_,je⟩:=hnb (univ:FS ι2) As Bs Cs jv ju jt js jr jq jp
 have h6:Disjoint (qs H (S \ (U∪Bs j∪Cs j)) l0 (As j)) Z:=rD λ w jm hwZ=>by
  have jk:=h3 j jm
  have jj:qs H S' l0 (Fb j)⊆qs H S' l0 (ji \ L):=qv H S' l0 (λ u hu =>
   rS ⟨mB.mpr ⟨j.1,(pF j.2).1,
     mUl _ (hFeq_i j ▸ mUr _ hu)⟩,
     (pS (h0.2.2.1 j.1 (hFeq_i j ▸ mUr _ hu))).2⟩)
  exact (pS (h4 hwZ)).2 (mUr _ (jj jk))
 have jh:Z⊆S \ U:=h4.trans (sSs sR (sUl.trans sUl))
 have h9:Disjoint Z (A j.1):=rD λ w hwZ jc =>
  (pS (h4 hwZ)).2 (mUl _ (mUr _
   (mB.mpr ⟨j.1,(pF j.2).1,mUr _ jc⟩)))
 exact q1x (K:=K) H S U Z D m_rob l0 (mA j.1) (lA j.1) (va j) (vb j) (a j) (z j)
  (Fa j) (Fb j) (A j.1) (P j) (Q j) hD1 hDK jw j3 j0 (h0.1 j.1).2
  j6 (hadj_i j) (ha_i j) (hz_i j) (hPl_i j) (hQl_i j) (hPA_i j) jh h9 j8 j7 h6 je
lemma q1z {V:Type*} [Fintype V] {e2:O} {K:ℕ} (jx:0 < e2) (jq:e2 < 1) (H:SG V) (S U U1:FS V) (jz:V->Bool) (d D h6 q d_tp1 d_tp2:ℕ) (B0:O) (v1 v2:Fin q->V) (F1 F2 A:Fin q->FS V) (mA lA:Fin q->ℕ) (js:1000<=d) (hdn:d<=#S) (k8:qk H jz) (jd:∀ v∈S,d<=dS H S v) (hUS:U⊆S) (ju:#U<=10*D) (jg:U1⊆S) (j9:#U1<=200*D^2) (j2:(#S:O)*(d:O)/4<=∑ v∈S \ U,(dS H (S \ U) v:O)) (kb:1<=D) (ka:(D:O)<=(log (#S:O))^K) (jf:ceil B0<=d/64 - 1) (k4:4<=log (#S:O)) (jh:(64*(max d_tp1 d_tp2:O)+128:O)<=(d:O)) (h3:1<=(1/100:O)*(e2*((d:O)/64 - 1)/2)*((1/100:O)/(log (15/2))^2)) (j0:(h6:O)+1<=200/(99/10000:O)*(log ((d:O)/64 - 2))^3) (h5:exp 2<=(d:O)/64 - 3) (jt:((200*(log (#S:O))^(2*K)+(#S:O)^(1/4:O)*(3*(21000*(log (#S:O))^3)^2)) * (200*(21000*(log (#S:O))^3)*(log (#S:O))^K+1)^(10*(log (log (#S:O)))^20) * (200*(21000*(log (#S:O))^3)*(log (#S:O))^K)<=(#S:O)/16)) (jy:∀ x:O,B0<=x -> (4:O)<=log x /\ (200/(99/10000:O)*(log x)^3)^2<=(log x)^7 /\ 2*log x+6 < x) (jc:¬ ∃ u1 G1 u2 G2 A0 l0,q1h H (S \ U) D (2*floor (21000*(log (#S:O))^3)) 1 u1 G1 u2 G2 A0 l0) (k1:∀ (H':SG V) (S':FS V) (d' D':ℕ) (x0:V) (c:(q3 H' S').Walk x0 x0) (x1 x2:V), d_tp1<=d'->d'<=#S'->qk H' jz->qQ H' S' (99/10000) (e2*(d':O)) -> (∀ v∈S',d' - 1<=dS H' S' v)->q0G H' S' x0 c -> x1∈S'->x2∈S'->x1≠x2->x1 ∉ c.support.toFinset->x2 ∉ c.support.toFinset -> 1<=D'->(D':O)<=(log (#S':O))^7 -> ∃ G1 G2 A0 l0,q1h H' S' D' (floor (200/(99/10000:O)*(log (#S':O))^3)) 1 x1 G1 x2 G2 A0 l0/\c.support.toFinset⊆A0) (k0:∀ (H':SG V) (S':FS V) (d':ℕ) (x0:V) (c:(q3 H' S').Walk x0 x0) (x1 x2:V), d_tp2<=d'->d'<=#S'->qk H' jz->qQ H' S' (1/100) (e2*(d':O)) -> (∀ v∈S',d' - 1<=dS H' S' v)->q0G H' S' x0 c -> x1∈S'->x2∈S'->x1≠x2->x1 ∉ c.support.toFinset->x2 ∉ c.support.toFinset -> ∃ G1 G2 A0 l0,q1h H' S' 1 (floor (200/(1/100:O)*(log (#S':O))^3)) 1 x1 G1 x2 G2 A0 l0/\c.support.toFinset⊆A0) (k5:q1o H S U U1 (S.filter (λ v=>200*floor (21000*(log (#S:O))^3)*D<=dS H S v)) (floor (21000*(log (#S:O))^3)) h6 (floor ((log (log (#S:O)))^20)) q v1 v2 F1 F2 A mA lA) (ji:¬ ∃ v1' v2' F1' F2' A' mA' lA', q1o H S U U1 (S.filter (λ v=>200*floor (21000*(log (#S:O))^3)*D<=dS H S v)) (floor (21000*(log (#S:O))^3)) h6 (floor ((log (log (#S:O)))^20)) (q+1) v1' v2' F1' F2' A' mA' lA') : (#S:O)^(1/4:O)<=(q:O):=by
 set n:O:=(#S:O);set h0:=floor (21000*(log n)^3);set D_:=200*h0*D;set l0:=floor ((log (log n))^20);by_contra k9;push Not at k9
 have j8:d_tp1<=d/64:=by
  have:(64*(d_tp1:O)+128:O)<=(d:O):=lT (by gcongr;exact lMl _ _) jh
  have:64*d_tp1+128<=d:=by exact_mod_cast this
  omega
 have j7:d_tp2<=d/64:=by
  have:(64*(d_tp2:O)+128:O)<=(d:O):=lT (by gcongr;exact lMr _ _) jh
  have:64*d_tp2+128<=d:=by exact_mod_cast this
  omega
 have h7:(h0:O)<=21000*(log n)^3:=nFl (by positivity);have jm:(l0:O)<=(log (log n))^20:=nFl (by positivity)
 have h4:((200*D^2+q*(3*h0^2))*((D_+1)^(10*l0)):O)*(D_:O)<=n*(d:O)/16:=by
  have h1:(200*(D:O)^2+(q:O)*(3*(h0:O)^2)) <=
    200*(log n)^(2*K)+n^(1/4:O)*(3*(21000*(log n)^3)^2):=by
   have hD2:(D:O)^2<=(log n)^(2*K):=by rw[mul_comm,pow_mul];exact pLl (nCn D) ka 2
   have hm2:(h0:O)^2<=(21000*(log n)^3)^2:=pLl (nCn h0) h7 2;have hqm:=mLm k9.le (show 3*(h0:O)^2<=3*(21000*(log n)^3)^2 by linarith only[hm2]) (by positivity) (by positivity);linarith only[hD2,hqm]
  have ja:(D_:O)<=200*(21000*(log n)^3)*(log n)^K:=by
   dsimp only[D_];push_cast;have h:=mLm h7 ka (nCn D) (by positivity);linarith only[h,show 200*(21000*(log n)^3)*(log n)^K=200*((21000*(log n)^3)*(log n)^K) by ring]
  have jb:((D_:O)+1)^(10*l0) <=
    (200*(21000*(log n)^3)*(log n)^K+1)^(10*(log (log n))^20):=by
   have j5:(0:O)<=200*(21000*(log n)^3)*(log n)^K:=by positivity
   calc
    ((D_:O)+1)^(10*l0)
     <= (200*(21000*(log n)^3)*(log n)^K+1)^(10*l0):=pLl (by positivity) (by linarith only[ja]) _
    _=(200*(21000*(log n)^3)*(log n)^K+1)^((10*l0:ℕ):O):=(rN _ _).symm
    _<=_:=rLe (by linarith only[j5]) (by push_cast;linarith only[jm])
  have jv:=mLm (mLm h1 jb (by positivity) (by positivity)) ja (nCn D_) (by positivity)
  have hd1:(1:O)<=(d:O):=by exact_mod_cast (show 1<=d by omega)
  have k2:n/16<=n*(d:O)/16:=by
   have hm:=mlL hd1 (show (0:O)<=n by positivity);linarith only[hm]
  have jj:((200*D^2+q*(3*h0^2))*((D_+1)^(10*l0)):O)*(D_:O) <=
    ((200*(log n)^(2*K)+n^(1/4:O)*(3*(21000*(log n)^3)^2)) *
     (200*(21000*(log n)^3)*(log n)^K+1)^(10*(log (log n))^20)) *
     (200*(21000*(log n)^3)*(log n)^K):=by
   push_cast;exact jv
  exact jj.trans (jt.trans k2)
 have j4:1<=(1/100:O)*(e2*((d/64:ℕ):O)/2)*((1/100:O)/(log (15/2))^2):=by
  have k7:(d:O)/64 - 1<=((d/64:ℕ):O):=by
   have h1:(d:O)<=64*((d/64:ℕ):O)+64:=by exact_mod_cast (show d<=64*(d/64)+64 by omega)
   linarith only[h1]
  have k3:=mlR (mlL (mlL k7 jx.le) (by norm_num:(0:O)<=1/200))
   (show (0:O)<=(1/100:O)/(log (15/2))^2 by positivity)
  linarith only[k3,h3,
   show (1/100:O)*(e2*((d:O)/64 - 1)/2)*((1/100:O)/(log (15/2))^2) =
    (1/200:O)*(e2*((d:O)/64 - 1))*((1/100:O)/(log (15/2))^2) by ring,
   show (1/100:O)*(e2*((d/64:ℕ):O)/2)*((1/100:O)/(log (15/2))^2) =
    (1/200:O)*(e2*((d/64:ℕ):O))*((1/100:O)/(log (15/2))^2) by ring]
 have h9:h6<=floor (200/(99/10000:O)*(log ((d/64 - 1:ℕ):O))^3):=by
  apply nLf
  have jr:(d:O)/64 - 2<=((d/64 - 1:ℕ):O):=by
   have h1:(d:O)<=64*((d/64 - 1:ℕ):O)+128:=by
    have:d<=64*(d/64 - 1)+128:=by omega
    exact_mod_cast this
   linarith only[h1]
  have j1:=lLl (by linarith only[h5,ePp 2]) jr;have jk:=pLl (lNn (by linarith only[h5,e1g,eLe.mpr (show (1:O)<=2 by norm_num)])) j1 3;linarith only[j0,jk]
 have j3:∀ k:ℕ,d/64 - 1<=k->k<=#S ->
   ((floor (200/(99/10000:O)*(log (k:O))^3):O)^2<=(log (k:O))^7) /\
   (floor (200/(99/10000:O)*(log (k:O))^3)<=h0) /\
   (2*log (k:O)/log ((d/64 - 1 - 1:ℕ):O)+6 < (k:O)):=by
  intro k hk1 hk2;have hkB:B0<=(k:O):=(nLc B0).trans (by exact_mod_cast jf.trans hk1);obtain ⟨jo,jw,jp⟩:=jy (k:O) hkB
  have jl:1 < log ((d/64 - 1 - 1:ℕ):O):=by
   rw[lIt (by exact_mod_cast (show 0 < d/64 - 1 - 1 by omega))]
   have h1:(d:O)/64 - 3<=((d/64 - 1 - 1:ℕ):O):=by
    have h1':(d:O)<=64*((d/64 - 1 - 1:ℕ):O)+192:=by
     exact_mod_cast (show d<=64*(d/64 - 1 - 1)+192 by omega)
    linarith only[h1']
   linarith only[h1,h5,exp_lt_exp.mpr (show (1:O) < 2 by norm_num)]
  have j6:0<=log (k:O):=by linarith only[jo]
  refine ⟨?_,?_,?_⟩
  .
   have hfl:(floor (200/(99/10000:O)*(log (k:O))^3):O)<=200/(99/10000:O)*(log (k:O))^3 :=
    nFl (by positivity)
   exact (pLl (nCn _) hfl 2).trans jw
  .
   apply Nat.floor_mono
   have jn:(0:O) < (k:O):=by exact_mod_cast (show 0 < k by omega)
   have je:log (k:O)<=log n:=lLl jn (by dsimp only[n];exact_mod_cast hk2);have jk:=pLl j6 je 3
   have hnn:(0:O)<=(log n)^3:=by positivity
   linarith only[jk,hnn]
  .
   have k6:2*log (k:O)/log ((d/64 - 1 - 1:ℕ):O)<=2*log (k:O) :=
    dLs (by positivity) jl.le
   linarith only[k6,jp]
 have h8:10<=h0:=by
  have h1:21000*(log n)^3 - 1 < (h0:O):=by linarith only[nL1 (21000*(log n)^3)]
  have h2:(1:O)<=(log n)^3:=oLp (by linarith only[k4]);exact_mod_cast (show (10:O)<=(h0:O) by linarith only[h1,h2])
 dsimp only[D_,h0,l0,n] at h4 j3 h8;push_cast at h4
 exact q1s (K:=K) jx jq H S U U1 jz d D h6 q v1 v2 F1 F2 A mA lA
  js hdn k8 jd hUS ju jg j9 j2 kb jc
  (λ H' S' d' D' x0 c x1 x2 hd'=>k1 H' S' d' D' x0 c x1 x2 (j8.trans hd'))
  (λ H' S' d' x0 c x1 x2 hd'=>k0 H' S' d' x0 c x1 x2 (j7.trans hd'))
  h4 j4 ⟨h9,j3⟩ (by nlinarith only[h8,kb]) k5 ji
lemma q1A {V:Type*} {e2:O} {K:ℕ} (H:SG V) (S U U0 U1 L Z:FS V) (d D m_rob m_min l0 d_nb q:ℕ) (v1 v2:Fin q->V) (F1 F2 A:Fin q->FS V) (mA lA:Fin q->ℕ) (A1':FS (Fin q)) (j9:U0=(S \ U).filter (λ v=>d/2<=#(U.filter (H.Adj v)))) (j8:U1=U∪U0) (hUS:U⊆S) (hUcard:#U<=10*D) (hD1:1<=D) (kf:(D:O)<=(log (#S:O))^K) (ji:4<=log (#S:O)) (j6:10*(21000*(log (#S:O))^3)^2*(log (#S:O))^K<=(log (#S:O))^(K+10)) (j1:(log (#S:O))^(K+10)<=(#S:O)/25) (jg:(#S:O)^(1/8:O)<=(#S:O)^(1/4:O)/4) (je:10*l0+2<=m_rob) (h7:m_rob=floor (21000*(log (#S:O))^3)) (jp:1<=m_min) (jo:¬ ∃ u1 G1 u2 G2 A0 lA0,q1h H (S \ U) D (2*m_rob) 1 u1 G1 u2 G2 A0 lA0) (h9:∀ i:Fin q,d_nb<=(mA i)^2 /\ (20*(mA i:O)<=((mA i^2:ℕ):O)/(log ((mA i^2:ℕ):O))^10) /\ exp 11<=((mA i^2:ℕ):O)) (h0:q1o H S U U1 L m_rob m_min l0 q v1 v2 F1 F2 A mA lA) (jt:(#S:O)^(1/4:O)/2<=(#A1':O)) (j0:Z⊆S \ (U∪A1'.biUnion (λ i=>F1 i∪F2 i∪A i) ∪ qs H (S \ L) l0 ((A1'.biUnion (λ i=>F1 i∪F2 i∪A i)) \ L))) (j7:(#S:O)/25<=(#Z:O)) (jq:∀ z∈Z,Z⊆qs H Z (m_rob/2) {z}) (h3:∀ i∈A1',∀ (X0 E0:FS V),X0⊆F1 i∪F2 i->E0⊆S \ (U∪A i) -> qs H E0 l0 X0⊆qs H (S \ L) l0 X0) (ke:∀ {ι:Type} (I:FS ι) (As Bs Cs:ι->FS V), (#S:O)^(1/8:O)<=(#I:O) -> (∀ i∈I,d_nb<=#(As i)) -> (∀ i∈I,As i⊆S \ U/\Bs i⊆S \ U/\Cs i⊆S \ U/\Disjoint (Bs i∪Cs i) (As i)) -> (∀ i∈I,(#(Bs i):O)<=(#(As i):O)/(log (#(As i):O))^10) -> (∀ i∈I,q06 H (S \ (U∪Bs i)) (As i) (Cs i) 4) -> (∀ i∈I,∀ v∈qs H (S \ (U∪Bs i∪Cs i)) l0 (As i), (#(U.filter (H.Adj v)):O)<=(d:O)/2) -> (∀ i∈I,∀ j∈I,i≠j -> Disjoint (qs H (S \ (U∪Bs i∪Cs i)) l0 (As i)) (qs H (S \ (U∪Bs j∪Cs j)) l0 (As j))) -> ∃ i∈I,(log (#S:O))^(K+10) <= (#(qs H (S \ (U∪Bs i∪Cs i)) l0 (As i)):O)) (hnc:∀ (A_nc B_nc W_nc:FS V) (h8:O), A_nc⊆S->B_nc⊆S->W_nc⊆S \ (A_nc∪B_nc) -> 1<=h8->h8<=(#A_nc:O)->h8<=(#B_nc:O) -> (#W_nc:O)*(log (#S:O))^3<=10*h8 -> ∃ (a b:V) (_:a∈A_nc) (_:b∈B_nc) (p:(q3 H (S \ W_nc)).Walk a b), p.IsPath/\(p.length:O)<=40/(1/100:O)*(log (#S:O))^3 /\ (∀ w∈p.support,w∈A_nc->w=a)/\(∀ w∈p.support,w∈B_nc->w=b)) : False:=by
 let n:O:=(#S:O);let S':=S \ L
 let h6:Fin q->Prop:=λ i =>
  ∃ a∈F1 i∪F2 i,∃ z∈Z,∃ p:(q3 H (S \ (U∪A i))).Walk a z,p.length<=m_rob/2
 let h5:=A1'.filter h6;let A2:=A1'.filter (λ i=>¬ h6 i)
 have jd:(h5.card:O) < n^(1/8:O) :=
  q1y (e2:=e2) (K:=K) H S U U0 U1 L Z d D m_rob m_min l0 d_nb q v1 v2 F1 F2 A mA lA A1'
   j9 j8 hD1 kf ji j1 jp jo ke je h9 h0 j0 j7 jq h3
 have jx:n^(1/8:O)<=(#A2:O):=by
  have jw:#A1'=h5.card+#A2:=by
   rw[<- card_union_of_disjoint (rD λ z h1 h2=>by
    dsimp only[h5,A2] at h1 h2;exact (pF h2).2 (pF h1).2)]
   congr 1;ext z;simp only[h5,A2,mU,mF]
   by_cases h:h6 z <;> simp [h]
  have jn:(#A1':O)=(h5.card:O)+(#A2:O):=by exact_mod_cast jw
  linarith only[jn,jt,jd,jg]
 let j2:Fin q->FS V:=λ i=>F1 i∪F2 i
 let jl:Fin q->FS V:=λ i=>A i
 let jk:Fin q->FS V:=λ _=>∅
 have h4:∀ i∈A2,qs H (S \ (U∪jl i∪jk i)) l0 (j2 i)⊆qs H S' l0 (j2 i):=λ i hi=>by
  dsimp only[jl,jk];rw[union_empty];exact h3 i (pF hi).1 (j2 i) (S \ (U∪A i)) sR sR
 have k8:∀ i∈A2,d_nb<=#(j2 i):=λ i _=>by
  have ju:#(j2 i)=2*(mA i)^2:=by
   rw[card_union_of_disjoint (h0.2.1 i).2.2.2.1,(h0.2.1 i).2.2.2.2.1.2.2.1,(h0.2.1 i).2.2.2.2.2.1.2.2.1];ring
  have:=(h9 i).1;omega
 have k7:∀ i∈A2,j2 i⊆S \ U/\jl i⊆S \ U/\jk i⊆S \ U/\Disjoint (jl i∪jk i) (j2 i):=λ i _ =>
  ⟨uS (h0.2.1 i).2.2.2.2.1.1 (h0.2.1 i).2.2.2.2.2.1.1,(h0.2.1 i).1,empty_subset _,
   by dsimp only[jl,jk];rw[union_empty];exact disjoint_union_right.mpr ⟨(h0.2.1 i).2.1,(h0.2.1 i).2.2.1⟩⟩
 have k6:∀ i∈A2,(#(jl i):O)<=(#(j2 i):O)/(log (#(j2 i):O))^10:=λ i _=>by
  have ju:#(j2 i)=2*(mA i)^2:=by
   rw[card_union_of_disjoint (h0.2.1 i).2.2.2.1,(h0.2.1 i).2.2.2.2.1.2.2.1,(h0.2.1 i).2.2.2.2.2.1.2.2.1];ring
  have hAc:(#(A i):O)<=20*(mA i:O):=by
   have:=(h0.2.1 i).2.2.2.2.2.2.1;exact_mod_cast (show #(A i)<=20*mA i by omega)
  have jz:=qZ (y:=(#(j2 i):O)) ((eLe.mpr (by norm_num)).trans (h9 i).2.2)
   (by rw[ju];push_cast;linarith only[show (0:O)<=(mA i:O)^2 from sq_nonneg _])
  exact hAc.trans ((h9 i).2.1.trans jz)
 have k5:∀ i∈A2,q06 H (S \ (U∪jl i)) (j2 i) (jk i) 4:=λ _ _ _ _=>by simp [jk]
 have k4:∀ i∈A2,∀ v∈qs H (S \ (U∪jl i∪jk i)) l0 (j2 i),(#(U.filter (H.Adj v)):O)<=(d:O)/2:=λ i hi v hv=>by
  have jv:=h4 i hi hv;have ja:v ∉ U1 \ L:=pD (h0.2.2.2.1 i) (qu H S' (show l0<=10*l0 by omega) _ jv);have jb:v ∉ U0:=λ hv0=>ja (rS ⟨j8 ▸ mUr _ hv0,(pS (qt H S' l0 _ jv)).2⟩)
  have k2:v∈S \ U:=rS ⟨(pS (qt H S' l0 _ jv)).1,λ hU =>
   (pS (qt H _ l0 _ hv)).2 (mUl _ (mUl _ hU))⟩
  have hlt:#(U.filter (H.Adj v)) < d/2:=by
   by_contra hge';push Not at hge';exact jb (j9 ▸ rF ⟨k2,hge'⟩)
  have h1:(#(U.filter (H.Adj v)):O)<=((d/2:ℕ):O):=by exact_mod_cast hlt.le
  have h2:((d/2:ℕ):O)<=(d:O)/2:=by
   have:2*((d/2:ℕ):O)<=(d:O):=by exact_mod_cast Nat.mul_div_le d 2
   linarith only[this]
  linarith only[h1,h2]
 have k3:∀ i∈A2,∀ j'∈A2,i≠j' ->
   Disjoint (qs H (S \ (U∪jl i∪jk i)) l0 (j2 i)) (qs H (S \ (U∪jl j'∪jk j')) l0 (j2 j')):=λ i hi j' hj' hij =>
  rD λ v hv1 hv2 =>
   pD (h0.2.2.2.2 i j' hij)
    (qu H S' (show l0<=5*l0 by omega) _ (h4 i hi hv1))
    (qu H S' (show l0<=5*l0 by omega) _ (h4 j' hj' hv2))
 obtain ⟨j,k1,jj⟩:=ke A2 j2 jl jk jx k8 k7 k6 k5 k4 k3;rw[union_empty] at jj;let Bj:=qs H (S \ (U∪A j)) l0 (F1 j∪F2 j);let h8:O:=(log n)^(K+10);have j3:h8<=(#Z:O):=j1.trans j7
 have jh:(m_rob:O)<=21000*(log n)^3:=by rw[h7];exact nFl (by positivity)
 have k0:21000*(log n)^3 - 1 < (m_rob:O):=by rw[h7];linarith only[nL1 (21000*(log n)^3)]
 have jr:(#(U∪A j):O)*(log n)^3<=10*h8:=by
  have h1:#(U∪A j)<=10*D+10*m_rob:=by
   have hc:=cUl U (A j);have hA:=(h0.2.1 j).2.2.2.2.2.2.1;have hm:=(h0.1 j).2;omega
  have h1R:(#(U∪A j):O)<=10*(D:O)+10*(m_rob:O):=by exact_mod_cast h1
  have h2:(10*(D:O)+10*(m_rob:O))*(log n)^3<=10*(10*(21000*(log n)^3)^2*(log n)^K):=by
   have ka:(1:O)<=(log n)^3:=oLp (by linarith only[ji]);have hlK:(1:O)<=(log n)^K:=oLp (by linarith only[ji])
   have hm1:(1:O)<=21000*(log n)^3:=by linarith only[ka]
   have j5:(D:O)<=21000*(log n)^3*(log n)^K:=by
    have:=mlR hm1 (show (0:O)<=(log n)^K by positivity)
    linarith only[kf,this]
   have j4:21000*(log n)^3<=21000*(log n)^3*(log n)^K:=by
    have:=mlL hlK (show (0:O)<=21000*(log n)^3 by positivity)
    linarith only[this]
   have jm:10*(D:O)+10*(m_rob:O)<=20*(21000*(log n)^3*(log n)^K):=by
    linarith only[jh,j5,j4]
   have jy:=mlR jm (show (0:O)<=(log n)^3 by positivity)
   have hnn:(0:O)<=(log n)^3*(log n)^3*(log n)^K:=by positivity
   linarith only[jy,hnn,
    show 20*(21000*(log n)^3*(log n)^K)*(log n)^3 =
     (20*21000:O)*((log n)^3*(log n)^3*(log n)^K) by ring,
    show 10*(10*(21000*(log n)^3)^2*(log n)^K) =
     (100*21000^2:O)*((log n)^3*(log n)^3*(log n)^K) by ring]
  have k9:=mlR h1R (show (0:O)<=(log n)^3 by positivity);dsimp only[h8];linarith only[k9,h2,j6]
 have jc:U∪A j⊆S \ (Bj∪Z):=λ w hw=>rS
  ⟨(uS hUS ((h0.2.1 j).1.trans sS)) hw,λ h=>by
   rcases pU h with hB | hZ
   . exact (pS (qt H (S \ (U∪A j)) l0 _ hB)).2 hw
   .
    rcases pU hw with hU | hA
    . exact (pS (j0 hZ)).2 (mUl _ (mUl _ hU))
    .
     exact (pS (j0 hZ)).2 (mUl _ (mUr _
      (mB.mpr ⟨j,(pF k1).1,mUr _ hA⟩)))⟩
 obtain ⟨b,z,kb,hzZ,Pz,_,js,_,_⟩ :=
  hnc Bj Z (U∪A j) h8 ((qt H _ _ _).trans sS) (j0.trans sS) jc
   (oLp (by linarith only[ji])) jj j3 jr
 obtain ⟨a0,ha0,q0,_,hq0l,_⟩:=qB kb
 have jf:(q0.append Pz).length<=m_rob/2:=by
  rw[wLa];have kd:Pz.length<=floor (40/(1/100:O)*(log n)^3):=nLf js
  have hf:(floor (40/(1/100:O)*(log n)^3):O)<=4000*(log n)^3:=by
   have hf0:=nFl (show (0:O)<=40/(1/100:O)*(log n)^3 by positivity);linarith only[hf0,show 40/(1/100:O)*(log n)^3=4000*(log n)^3 by ring]
  have h1:((2*(l0+Pz.length)+1:ℕ):O)<=(m_rob:O):=by
   have hl0:(l0:O)<=(m_rob:O)/10:=by
    have h10:(10*l0:O)<=(m_rob:O):=by exact_mod_cast (show 10*l0<=m_rob by omega)
    linarith only[h10]
   have kc:(Pz.length:O)<=4000*(log n)^3:=(by exact_mod_cast kd:(Pz.length:O)<=_).trans hf;have ka:(1:O)<=(log n)^3:=oLp (by linarith only[ji]);push_cast;linarith only[hl0,kc,k0,ka]
  have h1N:2*(l0+Pz.length)+1<=m_rob:=by exact_mod_cast h1
  omega
 exact (pF k1).2 ⟨a0,(pI ha0).1,z,hzZ,q0.append Pz,jf⟩
set_option maxHeartbeats 400000 in
lemma q1B {e2:O} {K:ℕ}
  (jd:0 < e2) (kl:e2<=1/25) (hK:1<=K) :
  ∃ d0:ℕ,100<=d0/\∀ {V:Type*} [Fintype V] (H:SG V) (S U:FS V) (wa:V->Bool)
   (d D:ℕ),
   d0<=d->d<=#S ->
   qk H wa ->
   qQ H S (1/100) (e2*(d:O)) ->
   (∀ v∈S,d<=dS H S v) ->
   ¬ qH H S (d/2) ->
   1<=D->(D:O)<=(log (#S:O))^K ->
   U⊆S->#U<=10*D ->
   let m_rob:=floor (21000*(log (#S:O))^3)
   ∃ (v1:V) (F1:FS V) (v2:V) (F2 A:FS V) (l:ℕ),
    q1h H (S \ U) D (2*m_rob) 1 v1 F1 v2 F2 A l:=by
 have k5:(0:O) < 1/100:=by norm_num
 have k4:(1/100:O) < 1:=by norm_num
 have wm:e2 < 1/5:=by linarith
 have j6:e2 < 1:=by linarith
 obtain ⟨kg,_,we⟩:=q1n (e1:=99/10000) (e2:=e2) (K:=7) (by norm_num) (by norm_num) jd j6 (by omega);obtain ⟨kf,h9,wd⟩:=q1n (e1:=1/100) (e2:=e2) (K:=1) k5 k4 jd j6 (by omega);obtain ⟨jp,_,wv⟩:=q0n (e1:=1/100) (e2:=e2) (k:=K+10) k5 k4 jd wm;obtain ⟨kh,_,wl⟩:=q1b k5 k4 jd kl;obtain ⟨w8,_,hnc⟩:=q0g k5 k4 jd j6;obtain ⟨M0,B0,hM0,wp⟩:=q1t jd hK kg kf jp;let ji:=max 100 (ceil M0);let w9:=max (max (max jp kh) w8) (64*ceil B0+192)
 refine ⟨max 1000 w9,lT (by omega) (lMl _ _),
  λ{V} _ H S U wa d D hd hdn hbip hexp hmindeg hnoK2 hD1 hDK hUS hUcard=>?_⟩
 have j9:jp<=d:=lT (lMl _ _) (lT (lMl _ _) (lT (lMl _ _) ((lMr _ _).trans hd)));have jm:kh<=d:=lT (lMr _ _) (lT (lMl _ _) (lT (lMl _ _) ((lMr _ _).trans hd)));have js:w8<=d:=lT (lMr _ _) (lT (lMl _ _) ((lMr _ _).trans hd))
 have k7:ceil B0<=d/64 - 1:=by
  have:64*ceil B0+192<=d:=(lMr _ _).trans ((lMr _ _).trans hd)
  omega
 have wx:B0<=(d:O):=(nLc B0).trans (by exact_mod_cast (by omega:ceil B0<=d));have hnB:B0<=(#S:O):=wx.trans (by exact_mod_cast hdn);obtain ⟨w4,_,j4,jl,k6⟩:=(wp (d:O) wx).1;obtain ⟨h6,_,_,k0,ks,kx,jh,jy,kr,kq,h7⟩:=(wp (#S:O) hnB).2;have kn:1000<=d:=lT (lMl _ _) hd;set n:O:=(#S:O);set m_rob:=floor (21000*(log n)^3);set D_:=200*m_rob*D;set l0:=floor ((log (log n))^20);let L:=S.filter (λ v=>D_<=dS H S v)
 let S':=S \ L;by_contra j5;let U0:=(S \ U).filter (λ v=>d/2<=#(U.filter (H.Adj v)))
 have hU0_card:#U0 < 100*D^2:=by
  by_contra kk;push Not at kk;have hU2:#U^2<=#U0:=(nPl hUcard 2).trans (by nlinarith);have kt:U0.Nonempty:=card_pos.mp (by nlinarith)
  exact hnoK2 (qJ (filter_subset _ _ |>.trans sS) hUS
   (rD λ z hz1 hz2=>(pS (pF hz1).1).2 hz2)
   kt hU2 (λ u hu=>(pF hu).2))
 let U1:=U∪U0;have j7:U1⊆S:=uS hUS (filter_subset _ _ |>.trans sS)
 have ja:#U1<=200*D^2:=by have:=cUl U U0;nlinarith
 have jn:n*(d:O)/4<=∑ v∈S \ U,(dS H (S \ U) v:O):=by
  have jw:(#U1:O)<=n/2:=by
   have w7:(#U1:O)<=200*(D:O)^2:=by exact_mod_cast ja
   have h2':(D:O)^2<=(log n)^(2*K):=by
    rw[mul_comm,pow_mul];exact pLl (nCn D) hDK 2
   linarith only[w7,h2',k0]
  have jv:#U1<=#S:=cL j7
  have jj:n/2<=(#S:O) - (#U1:O):=by dsimp only[n];linarith only[jw]
  have w7:(#S - #U1)*(d - (d/2 - 1))<=∑ v∈S \ U,dS H (S \ U) v:=by
   have wg:S \ U1⊆S \ U:=sSs sR sUl
   calc
    (#S - #U1)*(d - (d/2 - 1))=#(S \ U1)*(d - (d/2 - 1)):=by rw[card_sdiff_of_subset j7]
    _=∑ _v∈S \ U1,(d - (d/2 - 1)):=by simp
    _<=∑ v∈S \ U1,dS H (S \ U) v:=sum_le_sum λ v hv=>by
      obtain ⟨wt,jq⟩:=pS hv;have wc:v∈S \ U:=rS ⟨wt,λ h=>jq (mUl _ h)⟩
      have ww:#(U.filter (H.Adj v)) < d/2:=by
       by_contra kk;push Not at kk;exact jq (mUr _ (rF ⟨wc,kk⟩))
      have hdv:=hmindeg v wt
      have jc:S.filter (H.Adj v)⊆(S \ U).filter (H.Adj v)∪U.filter (H.Adj v):=λ u hu=>by
       obtain ⟨huS,ws⟩:=pF hu
       by_cases wu:u∈U
       . exact mUr _ (rF ⟨wu,ws⟩)
       . exact mUl _ (rF ⟨rS ⟨huS,wu⟩,ws⟩)
      have h2:=(cL jc).trans (cUl _ _);unfold dS at hdv ⊢;omega
    _<=∑ v∈S \ U,dS H (S \ U) v:=sum_le_sum_of_subset_of_nonneg wg (λ _ _ _=>Nat.zero_le _)
  have w6:((#S - #U1:ℕ):O)*((d - (d/2 - 1):ℕ):O)<=∑ v∈S \ U,(dS H (S \ U) v:O):=by exact_mod_cast w7
  rw[Nat.cast_sub jv] at w6
  have je:(d:O)/2<=((d - (d/2 - 1):ℕ):O):=by
   have:d<=2*(d - (d/2 - 1)):=by omega
   have:(d:O)<=2*((d - (d/2 - 1):ℕ):O):=by exact_mod_cast this
   linarith only[this]
  have wj:=mLm jj je (div_nonneg (nCn d) (by norm_num)) (by linarith only[jj,show (0:O)<=n from nCn #S]);linarith only[wj,w6,show n/2*((d:O)/2)=n*(d:O)/4 by ring]
 let jk:ℕ->Prop:=λ q=>∃ v1 v2 F1 F2 A mA lA,q1o H S U U1 L m_rob ji l0 q v1 v2 F1 F2 A mA lA
 have ku:jk 0:=⟨Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,Fin.elim0,
  λ i=>i.elim0,λ i=>i.elim0,λ i=>i.elim0,λ i=>i.elim0,λ i=>i.elim0⟩
 have jg:∀ q,jk q->q<=#S:=by
  rintro q ⟨v1,v2,F1,F2,A,mA,lA,h4⟩
  have wk:Injective v1:=λ i j hij=>by
   by_contra hne
   have h1:v1 i∈qs H S' (5*l0) (F1 i∪F2 i):=qu H S' (Nat.zero_le _) _
    (rI ⟨mUl _ (h4.2.1 i).2.2.2.2.1.2.1,h4.2.2.1 i (mUl _ (h4.2.1 i).2.2.2.2.1.2.1)⟩)
   have h2:v1 j∈qs H S' (5*l0) (F1 j∪F2 j):=qu H S' (Nat.zero_le _) _
    (rI ⟨mUl _ (h4.2.1 j).2.2.2.2.1.2.1,h4.2.2.1 j (mUl _ (h4.2.1 j).2.2.2.2.1.2.1)⟩)
   exact pD (h4.2.2.2.2 i j hne) h1 (hij ▸ h2)
  calc
   q=#(univ.image v1):=by rw[card_image_of_injective _ wk];simp
   _<=#S:=cL (image_subset_iff.mpr λ i _=>sS ((h4.2.1 i).2.2.2.2.1.1 (h4.2.1 i).2.2.2.2.1.2.1))
 let Qs:=(range (#S+1)).filter jk;have jx:Qs.Nonempty:=⟨0,rF ⟨mem_range.mpr (by omega),ku⟩⟩;let q:=Qs.max' jx;obtain ⟨v1,v2,F1,F2,A,mA,lA,h4⟩:=(pF (max'_mem Qs jx)).2
 have ki:¬ jk (q+1):=λ h=>by
  have hle:=jg (q+1) h
  have:=le_max' Qs (q+1) (rF ⟨mem_range.mpr (by omega),h⟩)
  omega
 have w0:n^(1/4:O)<=(q:O) :=
  q1z (K:=K) jd j6 H S U U1 wa d D ji q kg kf B0 v1 v2 F1 F2 A mA lA
   kn hdn hbip hmindeg hUS hUcard j7 ja jn hD1 hDK k7 h6 w4 j4 jl
   k6 kr (λ x hx=>let h:=(wp x hx).2;⟨h.1,h.2.1,h.2.2.1⟩) j5
   (λ H' S' d' D' x0 c x1 x2=>we H' S' wa d' D' x0 c x1 x2)
   (λ H' S' d' x0 c x1 x2 hd' hdn' hbip' hexp' hdeg' hcyc' hx1' hx2' hne' h1c h2c =>
    wd H' S' wa d' 1 x0 c x1 x2 hd' hdn' hbip' hexp' hdeg' hcyc' hx1' hx2' hne' h1c h2c le_rfl
     (by
       rw[pow_one,Nat.cast_one,lIe (by exact_mod_cast (show 0 < #S' by have:=h9.trans (hd'.trans hdn');omega))]
       have wq:(100:O)<=(#S':O):=by exact_mod_cast (h9.trans (hd'.trans hdn'))
       linarith only[wq,e1l]))
   h4 ki
 have h8:10<=m_rob:=by
  have h1:21000*(log n)^3 - 1 < (m_rob:O):=by linarith only[nL1 (21000*(log n)^3)]
  have h2:(1:O)<=(log n)^3:=oLp (by linarith only[h6]);exact_mod_cast (show (10:O)<=(m_rob:O) by linarith only[h1,h2])
 have j3:10*l0+2<=m_rob:=by
  have h1:(l0:O)<=(log (log n))^20:=nFl (pow_nonneg (lNn (by linarith only[h6])) 20)
  have h2:21000*(log n)^3 - 1 < (m_rob:O):=by linarith only[nL1 (21000*(log n)^3)]
  exact_mod_cast (show ((10*l0+2:ℕ):O)<=(m_rob:O) by push_cast;linarith only[h1,h2,kx])
 have j1:(#U:O)<=exp ((log (log n))^2):=by
  have h1:(#U:O)<=10*(D:O):=by exact_mod_cast hUcard
  linarith only[h1,hDK,ks]
 have jr:∀ i:Fin q,jp<=(mA i)^2 /\
   (20*(mA i:O)<=((mA i^2:ℕ):O)/(log ((mA i^2:ℕ):O))^10) /\
   exp 11<=((mA i^2:ℕ):O):=λ i=>by
  have hmi:M0<=(mA i:O):=(nLc M0).trans (by exact_mod_cast (lMr 100 (ceil M0)).trans (h4.1 i).1);obtain ⟨h1,h2,h3⟩:=hM0 (mA i:O) hmi;exact ⟨by exact_mod_cast h1,by push_cast;exact h3,by push_cast;exact h2⟩
 let j0:Fin q->Prop:=λ i =>
  ∃ a∈F1 i∪F2 i,∃ x∈L \ U,∃ p:(q3 H (S \ (U∪A i))).Walk a x,p.length<=l0
 let h5:=(univ:FS (Fin q)).filter j0;let A1:=(univ:FS (Fin q)).filter (λ i=>¬ j0 i)
 have jo:(h5.card:O) < n^(1/8:O) :=
  q1w (e2:=e2) (K:=K) H S U U0 U1 L d D m_rob ji l0 jp q v1 v2 F1 F2 A mA lA
   rfl rfl rfl hUS hUcard hD1 hDK h6 (lT (by omega) (lMl 100 _)) j5
   (λ{ι:Type} I As Bs Cs=>wv H S U d I As Bs Cs j9 hdn hexp hmindeg hUS j1)
   h8 j3 jr h4
 have kw:n^(1/4:O)/2<=(#A1:O):=by
  have jc:q=h5.card+#A1:=by
   have hu:(univ:FS (Fin q))=h5∪A1:=by
    ext z;simp only[h5,A1,mUv,mU,mF,true_and];tauto
   have ke:=congrArg Finset.card hu
   rw[card_univ,Fintype.card_fin,card_union_of_disjoint
    (rD λ z h1 h2=>by
     dsimp only[h5,A1] at h1 h2;exact (pF h2).2 (pF h1).2)] at ke
   exact ke
  have k2:(q:O)=(h5.card:O)+(#A1:O):=by exact_mod_cast jc
  linarith only[k2,w0,jo,h7]
 have kd:ceil (n^(1/4:O)/2)<=#A1:=by exact_mod_cast Nat.ceil_le.mpr kw
 obtain ⟨A1',jz,j2⟩:=exists_subset_card_eq kd
 have kc:(#A1':O)<=n^(1/4:O):=by
  rw[j2]
  have h1:(ceil (n^(1/4:O)/2):O) < n^(1/4:O)/2+1 :=
   ceil_lt_add_one (div_nonneg (rNn (nCn #S) _) (by norm_num))
  have h2:(4:O)<=n^(1/4:O):=by
   have h18:(1:O)<=n^(1/8:O):=Real.one_le_rpow (by dsimp only[n];exact_mod_cast (show 1<=#S by omega)) (by norm_num);linarith only[h18,h7]
  linarith only[h1,h2]
 let h0:=A1'.biUnion (λ i=>F1 i∪F2 i∪A i)
 let ky:=U∪h0∪qs H S' l0 (h0 \ L)
 have ka:ky⊆S:=uS (uS hUS
  (biUnion_subset.mpr λ i _=>uS (uS
   ((h4.2.1 i).2.2.2.2.1.1.trans sS) ((h4.2.1 i).2.2.2.2.2.1.1.trans sS))
   ((h4.2.1 i).1.trans sS)))
  ((qt H S' l0 _).trans sS)
 have jt:(ky.card:O)<=(1/100:O)*n/(100*(log n)^2):=by
  have kb:∀ v∈S',dS H S' v<=D_:=λ v hv=>by
   have ww:dS H S v < D_:=by by_contra kk;push Not at kk;exact (pS hv).2 (rF ⟨(pS hv).1,kk⟩)
   exact (cL (filter_subset_filter _ sS)).trans ww.le
  have ju:h0.card<=#A1'*(3*m_rob^2):=by
   calc
    _<=∑ i∈A1',#(F1 i∪F2 i∪A i):=cBu
    _<=∑ _i∈A1',(3*m_rob^2):=sum_le_sum λ i _=>by
      have wn:=cUl (F1 i∪F2 i) (A i);have wb:=cUl (F1 i) (F2 i);have hi:=h4.2.1 i;have hm:=(h4.1 i).2;rw[hi.2.2.2.2.1.2.2.1,hi.2.2.2.2.2.1.2.2.1] at wb;have hA:=hi.2.2.2.2.2.2.1;have hsq:mA i^2<=m_rob^2:=nPl hm 2;nlinarith only[wn,wb,hA,hsq,hm,h8]
    _=#A1'*(3*m_rob^2):=by simp
  have jf:#(qs H S' l0 (h0 \ L))<=(D_+1)^l0*h0.card :=
   (qD H S' (h0 \ L) D_ kb l0).trans (nMl _ (cL (inter_subset_left.trans sS)))
  have wf:ky.card<=10*D+h0.card*(1+(D_+1)^l0):=by
   have wn:=cUl (U∪h0) (qs H S' l0 (h0 \ L));have wb:=cUl U h0;dsimp only[ky];nlinarith only[wn,wb,hUcard,jf]
  have j8:(m_rob:O)<=21000*(log n)^3:=nFl (mul_nonneg (by norm_num) (pow_nonneg (by linarith only[h6]) 3));have kj:(l0:O)<=(log (log n))^20:=nFl (pow_nonneg (lNn (by linarith only[h6])) 20)
  have kv:(D_:O)<=200*(21000*(log n)^3)*(log n)^K:=by
   dsimp only[D_];push_cast;have h:=mLm j8 hDK (nCn D) (mul_nonneg (by norm_num) (pow_nonneg (by linarith only[h6]) 3));linarith only[h,show 200*(21000*(log n)^3)*(log n)^K=200*((21000*(log n)^3)*(log n)^K) by ring]
  have k3:((D_:O)+1)^l0<=(200*(21000*(log n)^3)*(log n)^K+1)^((log (log n))^20):=by
   have w2:(0:O)<=200*(21000*(log n)^3)*(log n)^K :=
    mul_nonneg (mul_nonneg (by norm_num) (mul_nonneg (by norm_num) (pow_nonneg (by linarith only[h6]) 3))) (pow_nonneg (by linarith only[h6]) K)
   calc
    ((D_:O)+1)^l0<=(200*(21000*(log n)^3)*(log n)^K+1)^l0 :=
      pLl (add_nonneg (nCn D_) zero_le_one) (by linarith only[kv]) _
    _=(200*(21000*(log n)^3)*(log n)^K+1)^(l0:O):=(rN _ _).symm
    _<=_:=rLe (by linarith only[w2]) kj
  have w5:(h0.card:O)<=n^(1/4:O)*(3*(21000*(log n)^3)^2):=by
   have h1:(h0.card:O)<=(#A1':O)*(3*(m_rob:O)^2):=by exact_mod_cast ju
   have hm2:(m_rob:O)^2<=(21000*(log n)^3)^2:=pLl (nCn m_rob) j8 2;exact h1.trans (mLm kc (by linarith only[hm2]) (mul_nonneg (by norm_num) (sq_nonneg _)) (rNn (nCn #S) _))
  have kz:(ky.card:O)<=10*(D:O)+(h0.card:O)*(1+((D_:O)+1)^l0):=by exact_mod_cast wf
  have w1:=mLm w5 (show 1+((D_:O)+1)^l0<=1+(200*(21000*(log n)^3)*(log n)^K+1)^((log (log n))^20) by linarith only[k3])
   (add_nonneg zero_le_one (pow_nonneg (add_nonneg (nCn D_) zero_le_one) l0))
   (mul_nonneg (rNn (nCn #S) _) (mul_nonneg (by norm_num) (sq_nonneg _)))
  linarith only[kz,w1,hDK,kq]
 obtain ⟨_,Z,ko,k9,kp⟩:=wl H S ky d jm hdn hexp ka jt
 have k8:∀ z∈Z,Z⊆qs H Z (m_rob/2) {z}:=λ z hz=>by
  have h1:=q11 kp hz
  have h2:2*floor (40/(1/100:O)*(log n)^3)<=m_rob/2:=by
   have hf:(floor (40/(1/100:O)*(log n)^3):O)<=4000*(log n)^3:=by
    have hf0:=nFl (mul_nonneg (by norm_num:(0:O)<=40/(1/100:O)) (pow_nonneg (by linarith only[h6]) 3));linarith only[hf0,show 40/(1/100:O)*(log n)^3=4000*(log n)^3 by ring]
   have w3:21000*(log n)^3 - 1 < (m_rob:O):=by linarith only[nL1 (21000*(log n)^3)]
   have h3:((4*floor (40/(1/100:O)*(log n)^3)+1:ℕ):O)<=(m_rob:O):=by
    push_cast;have w7:(1:O)<=(log n)^3:=oLp (by linarith only[h6]);linarith only[hf,w3,w7]
   have h3N:4*floor (40/(1/100:O)*(log n)^3)+1<=m_rob:=by exact_mod_cast h3
   omega
  exact h1.trans (qu H Z h2 {z})
 have jb:∀ i∈A1,∀ (X0 E0:FS V),X0⊆F1 i∪F2 i->E0⊆S \ (U∪A i) ->
   qs H E0 l0 X0⊆qs H S' l0 X0:=by
  intro i hi X0 E0 hX0 wo;have wi:¬ j0 i:=(pF hi).2
  have km:Disjoint (qs H E0 l0 X0) L:=by
   rw[dL];intro z wr hzL;obtain ⟨a0,wy,p0,_,wh,_⟩:=qB wr;have k1:z ∉ U:=λ hU=>(pS (wo (qt H E0 l0 X0 wr))).2 (mUl _ hU)
   exact wi ⟨a0,hX0 (pI wy).1,z,rS ⟨hzL,k1⟩,
    q0r p0 (λ w hw=>wo (q0w p0 (pI wy).2 w hw)),
    by rw[q0t];exact wh⟩
  rw[<- qC H E0 L X0 l0 km];exact qw H (λ z hz=>rS ⟨(pS (wo (pS hz).1)).1,(pS hz).2⟩) l0 X0
 exact q1A (e2:=e2) (K:=K) H S U U0 U1 L Z d D m_rob ji l0 jp q v1 v2 F1 F2 A mA lA A1'
  rfl rfl hUS hUcard hD1 hDK h6 jh jy h7 j3 rfl
  (lT (by omega) (lMl 100 _)) j5 jr h4
  (by rw[j2];exact nLc _) ko k9 k8 (λ i hi=>jb i (jz hi))
  (λ{ι:Type} I As Bs Cs=>wv H S U d I As Bs Cs j9 hdn hexp hmindeg hUS j1)
  (λ A_nc B_nc W_nc x_nc=>hnc H S A_nc B_nc W_nc d x_nc js hdn hexp (λ v hv=>Nat.le_trans (nSl d 1) (hmindeg v hv)))
lemma q1C {e2:O} {K:ℕ}
  (kx:0 < e2) (kh:e2<=1/25) (hK:10<=K) :
  ∃ d0:ℕ,100<=d0/\∀ {V:Type*} [Fintype V] (H:SG V) (S U:FS V) (w6:V->Bool)
    (d D r:ℕ),
    d0<=d->d<=#S ->
    qk H w6 ->
    qQ H S (1/100) (e2*(d:O)) ->
    (∀ v∈S,d<=dS H S v) ->
    ¬ qH H S (d/2) ->
    (log (#S:O))^10<=(D:O)->(D:O)<=(log (#S:O))^K ->
    let m_rob:=floor (21000*(log (#S:O))^3)
    let m:=4*m_rob
    1<=r->r<=30*m ->
    U⊆S->#U<=4*D ->
    ∃ (v1 v2:V) (F1 F2 A:FS V) (l:ℕ),
     q1h H (S \ U) D m r v1 F1 v2 F2 A l:=by
 have wc:(0:O) < 1/100:=by norm_num
 have wb:(1/100:O) < 1:=by norm_num
 have wa:e2 < 1:=by linarith
 obtain ⟨d1,k3,kw⟩:=q1B (K:=K+5) kx kh (by omega);obtain ⟨d2,hd2_100,hnc⟩:=q0g wc wb kx wa
 have wj:∀ᶠ x:O in atTop,
    (1000:O)<=x/\(4:O)<=log x /\
    (log x)^K*((log x)^4+1)<=(log x)^(K+5) /\
    300*(4*(21000*(log x)^3))^2+100*(21000*(log x)^3)<=(log x)^10 /\
    (10:O)<=21000*(log x)^3 - 1:=by
  let C:O:=300*(4*21000)^2+100*21000
  filter_upwards [eGe (1000:O),
    lGe (max 4 (C+2))] with x hx hl
  have hl4:4<=log x:=lT (lMl _ _) hl;have hlC:C+2<=log x:=lT (lMr _ _) hl
  have w5:1<=log x:=by linarith
  refine ⟨hx,hl4,?_,?_,by
    have:(1:O)<=(log x)^3:=oLp w5;linarith⟩
  .
    have h1:(log x)^4+1<=(log x)^5:=by
     have h4:(1:O)<=(log x)^4:=oLp w5
     have:(log x)^5=log x*(log x)^4:=by ring
     nlinarith
    calc
     (log x)^K*((log x)^4+1)
      <= (log x)^K*(log x)^5:=mlL h1 (by positivity)
     _=(log x)^(K+5):=(pow_add _ _ _).symm
  .
    have h36:(log x)^3<=(log x)^6:=pLr w5 (by omega)
    have h7:C*(log x)^6<=(log x)^10:=by
     calc
      C*(log x)^6<=log x*(log x)^6:=mlR (by linarith) (by positivity)
      _=(log x)^7:=by ring
      _<=(log x)^10:=pLr w5 (by omega)
    have heq:300*(4*(21000*(log x)^3))^2=300*(4*21000)^2*(log x)^6:=by ring
    dsimp only[C] at h7;nlinarith
 rw[eAt] at wj;obtain ⟨B0,hB0⟩:=wj
 refine ⟨max (max d1 d2) (ceil B0),lT (lT k3 (lMl _ _)) (lMl _ _),
  λ{V} _ H S U w6 d D r hd hdn hbip hexp hmindeg hnoK2 hDlb hDub hr1 hr30 hUS hUcard=>?_⟩
 have wk:d1<=d:=lT (lMl _ _) (lT (lMl _ _) hd);have hd2:d2<=d:=lT (lMr _ _) (lT (lMl _ _) hd);have hnB:B0<=(#S:O):=(nLc B0).trans (by exact_mod_cast ((lMr _ _).trans hd).trans hdn);obtain ⟨hn1000,hln4,jy,hm2_D,hmrob_10⟩:=hB0 (#S:O) hnB;set n:O:=(#S:O);set m_rob:=floor (21000*(log n)^3);set m:=4*m_rob;set f4:=ceil ((log n)^4);set D':=D*f4
 have k2:1<=f4:=by
  have:(1:O)<=(log n)^4:=oLp (by linarith)
  exact_mod_cast this.trans (nLc _)
 have jx:1<=D:=by
  have:(1:O)<=(log n)^10:=oLp (by linarith)
  exact_mod_cast this.trans hDlb
 have jh:D<=D':=Nat.le_mul_of_pos_right D k2
 have jz:(D':O)<=(log n)^(K+5):=by
  dsimp only[D'];push_cast;have kg:(f4:O)<=(log n)^4+1:=(ceil_lt_add_one (by positivity)).le;exact (mLm hDub kg (nCn f4) (by positivity)).trans jy
 have hmrob_ge10:10<=m_rob:=by
  have:21000*(log n)^3 - 1 < (m_rob:O):=by linarith [nL1 (21000*(log n)^3)]
  exact_mod_cast (show (10:O)<=(m_rob:O) by linarith)
 have hm2_le_D:300*m^2+100*m_rob<=D:=by
  have hmrob_ub:(m_rob:O)<=21000*(log n)^3:=nFl (by positivity)
  have hR:((300*m^2+100*m_rob:ℕ):O)<=(D:O):=by
    dsimp only[m];push_cast
    have hsq:(4*(m_rob:O))^2<=(4*(21000*(log n)^3))^2 :=
     pLl (by positivity) (by linarith) 2
    linarith
  exact_mod_cast hR
 have w9:∀ j,1<=j->j<=r->∃ (v1 v2:V) (F1 F2 A:FS V) (l:ℕ),
    q1h H (S \ U) D' m j v1 F1 v2 F2 A l:=by
  intro j
  induction j with
  | zero=>intro h _;omega
  | succ j ih =>
    intro _ hjr
    rcases Nat.eq_zero_or_pos j with rfl | hj1
    .
     obtain ⟨v1,F1,v2,F2,A,l,j7⟩ :=
      kw H S U w6 d D' wk hdn hbip hexp hmindeg hnoK2 (by omega) jz hUS (by omega)
     exact ⟨v1,v2,F1,F2,A,l,q1k j7 (by dsimp only[m,m_rob,n];omega)⟩
    .
     obtain ⟨v1,v2,F1,F2,A1,l1,h5⟩:=ih hj1 (by omega);let U':=U∪A1∪F1∪F2
     have k5:U'⊆S:=uS (uS (uS hUS
      (h5.1.trans sS)) (h5.2.2.2.2.1.1.trans sS))
      (h5.2.2.2.2.2.1.1.trans sS)
     have js:#U'<=10*D':=by
      have we:=cUl (U∪A1∪F1) F2;have wd:=cUl (U∪A1) F1;have hc3:=cUl U A1;have wp:=h5.2.2.2.2.2.2.1
      have w3:10*m*j<=300*m^2:=by
       have:j<=30*m:=by omega
       calc
         10*m*j<=10*m*(30*m):=nMl _ this
         _=300*m^2:=by ring
      rw[h5.2.2.2.2.2.1.2.2.1] at we;rw[h5.2.2.2.2.1.2.2.1] at wd;dsimp only[U'];omega
     obtain ⟨v3,F3,v4,F4,A2,l2,h8⟩ :=
      kw H S U' w6 d D' wk hdn hbip hexp hmindeg hnoK2 (by omega) jz k5 js
     let W:=U∪A1∪A2
     have kj:W⊆S:=uS (uS hUS (h5.1.trans sS))
      (h8.1.trans sS)
     have kz:(#W:O)*(log n)^3<=10*(D':O):=by
      have w0:#W<=5*D:=by
       have we:=cUl (U∪A1) A2;have wd:=cUl U A1;have wp:=h5.2.2.2.2.2.2.1;have wi:=h8.2.2.2.2.2.2.1
       have w3:10*m*j<=300*m^2:=by
         have:j<=30*m:=by omega
         calc
          10*m*j<=10*m*(30*m):=nMl _ this
          _=300*m^2:=by ring
       dsimp only[W,m,m_rob,n] at *;omega
      have h1:(#W:O)*(log n)^3<=5*(D:O)*(log n)^4:=by
       have k1:(log n)^3<=(log n)^4:=pLr (by linarith) (by omega)
       have hWR:(#W:O)<=5*(D:O):=by exact_mod_cast w0
       have w8:=mLm hWR k1 (by positivity) (by positivity);linarith
      have hD'ge:(D:O)*(log n)^4<=(D':O):=by
       dsimp only[D'];push_cast;exact mlL (nLc _) (nCn D)
      linarith
     have h0:Disjoint (F3∪F4) U':=rD λ z hzF hzU'=>by
      rcases pU hzF with h3 | h4
      . exact (pS (h8.2.2.2.2.1.1 h3)).2 hzU'
      . exact (pS (h8.2.2.2.2.2.1.1 h4)).2 hzU'
     have h6:Disjoint A2 U':=rD λ z hzA hzU' =>
      (pS (h8.1 hzA)).2 hzU'
     have jc:W⊆S \ ((F1∪F2)∪(F3∪F4)):=λ z hzW=>rS ⟨kj hzW,λ hF=>by
      rcases pU hF with ka | k1
      .
       rcases pU hzW with kk | ji
       .
         rcases pU kk with w4 | jk
         .
          rcases pU ka with h1 | h2
          . exact (pS (h5.2.2.2.2.1.1 h1)).2 w4
          . exact (pS (h5.2.2.2.2.2.1.1 h2)).2 w4
         .
          rcases pU ka with h1 | h2
          . exact pD h5.2.1 jk h1
          . exact pD h5.2.2.1 jk h2
       .
         rcases pU ka with h1 | h2
         . exact pD h6 ji (mUl _ (mUr _ h1))
         . exact pD h6 ji (mUr _ h2)
      .
       rcases pU hzW with kk | ji
       .
         rcases pU kk with w4 | jk
         . exact pD h0 k1 (mUl _ (mUl _ (mUl _ w4)))
         . exact pD h0 k1 (mUl _ (mUl _ (mUr _ jk)))
       .
         rcases pU k1 with h3 | h4
         . exact pD h8.2.1 ji h3
         . exact pD h8.2.2.1 ji h4⟩
     obtain ⟨a,b,ki,wf,P,k9,kn,kd,kc⟩ :=
      hnc H S (F1∪F2) (F3∪F4) W d (D':O) hd2 hdn hexp (λ u hu=>Nat.le_trans (nSl d 1) (hmindeg u hu))
       (uS (h5.2.2.2.2.1.1.trans sS) (h5.2.2.2.2.2.1.1.trans sS))
       (uS (h8.2.2.2.2.1.1.trans sS) (h8.2.2.2.2.2.1.1.trans sS))
       jc (by exact_mod_cast (show 1<=D' by omega))
       (by have:D'<=#(F1∪F2):=h5.2.2.2.2.1.2.2.1 ▸ cL sUl;exact_mod_cast this)
       (by have:D'<=#(F3∪F4):=h8.2.2.2.2.1.2.2.1 ▸ cL sUl;exact_mod_cast this)
       kz
     have jb:∀ (u1 u2 u3 u4:V) (G1 G2 G3 G4:FS V),
       q1h H (S \ U) D' m j u1 G1 u2 G2 A1 l1 ->
       q1h H (S \ U') D' (2*m_rob) 1 u3 G3 u4 G4 A2 l2 ->
       G1∪G2=F1∪F2->G3∪G4=F3∪F4->a∈G1->b∈G3 ->
       ∃ (v1' v2':V) (F1' F2' A':FS V) (l':ℕ),
         q1h H (S \ U) D' m (j+1) v1' F1' v2' F2' A' l':=by
      intro u1 u2 u3 u4 G1 G2 G3 G4 h1 h2 j1 j0 k4 ky;obtain ⟨p1,jr,hp1_len⟩:=q0C h1.2.2.2.2.1 k4;obtain ⟨p3,jq,hp3_len⟩:=q0C h2.2.2.2.2.1 ky
      have j3:S \ U'⊆S \ U:=sSs sR
       (sUl.trans (sUl.trans sUl))
      have w2:∀ w∈P.support,w∈S \ U:=λ w hw=>by
       have jp:=q0w P (rS
         ⟨sS (h1.2.2.2.2.1.1 k4),λ h=>(pS (jc h)).2 (mUl _ ki)⟩) w hw
       exact rS ⟨(pS jp).1,λ hU=>(pS jp).2 (mUl _ (mUl _ hU))⟩
      have j6:∀ w∈P.support,w ∉ A1/\w ∉ A2:=λ w hw=>by
       have jp:=q0w P (rS
         ⟨sS (h1.2.2.2.2.1.1 k4),λ h=>(pS (jc h)).2 (mUl _ ki)⟩) w hw
       exact ⟨λ h=>(pS jp).2 (mUl _ (mUr _ h)),
            λ h=>(pS jp).2 (mUr _ h)⟩
      let kb:=q0r p1 (λ w hw=>h1.2.2.2.2.1.1 (q0w p1 h1.2.2.2.2.1.2.1 w hw))
      let ks:=q0r p3 (λ w hw=>j3 (h2.2.2.2.2.1.1 (q0w p3 h2.2.2.2.2.1.2.1 w hw)))
      let P':=q0r P w2
      have je:Disjoint G1 G3:=rD λ z hz1 hz3 =>
       pD h0 (j0 ▸ mUl _ hz3) (by
         have ja:z∈F1∪F2:=j1 ▸ mUl _ hz1
         rcases pU ja with jo | jn
         . exact mUl _ (mUr _ jo)
         . exact mUr _ jn)
      have jm:(kb.append P').IsPath:=q0x kb P' (q0v _ _ jr)
       (q0v _ _ k9) (λ w hw1 hw2=>kd w (by simpa [P',q0s] using hw2)
         (j1 ▸ mUl _ (q0w p1 h1.2.2.2.2.1.2.1 w (by simpa [kb,q0s] using hw1))))
      let Q:=(kb.append P').append ks.reverse
      have k8:Q.IsPath:=q0x (kb.append P') ks.reverse jm
       (q0v _ _ jq).reverse (λ w hw1 hw2=>by
         rw[q0q] at hw2;have ku:w∈G3:=q0w p3 h2.2.2.2.2.1.2.1 w (by simpa [ks,q0s] using hw2);rw[wSa] at hw1
         rcases hw1 with jp | kq
         . exact (pD je (q0w p1 h1.2.2.2.2.1.2.1 w (by simpa [kb,q0s] using jp)) ku).elim
         . exact kc w (by simpa [P',q0s] using kq) (j0 ▸ mUl _ ku))
      have hQ_len:Q.length<=2*m:=by
       have hPm:P.length<=m_rob:=by
         have hle:(P.length:O)<=21000*(log n)^3:=kn.trans (by
          dsimp only[n]
          have hnn:0<=(log (#S:O))^3:=by positivity
          linarith only[hnn,show 40/(1/100:O)*(log (#S:O))^3=4000*(log (#S:O))^3 by ring])
         exact nLf hle
       dsimp only[Q,kb,ks,P'];simp only[wLa,wLr,q0t];dsimp only[m];omega
      have h9:∀ w∈Q.support,w∈G1\/w∈P.support\/w∈G3:=λ w hw=>by
       dsimp only[Q] at hw;rw[wSa,wSa,q0q] at hw
       rcases hw with (jp | kq) | h3'
       . exact Or.inl (q0w p1 h1.2.2.2.2.1.2.1 w (by simpa [kb,q0s] using jp))
       . exact Or.inr (Or.inl (by simpa [P',q0s] using kq))
       . exact Or.inr (Or.inr (q0w p3 h2.2.2.2.2.1.2.1 w (by simpa [ks,q0s] using h3')))
      let j2:=A1∪A2∪Q.support.toFinset
      have k0:j2⊆S \ U:=uS (uS h1.1 (h2.1.trans j3))
       (λ w hw=>q0w Q (h1.2.2.2.2.1.1 h1.2.2.2.2.1.2.1) w (pTf hw))
      have jd:Disjoint G2 G4:=rD λ z hz2 hz4 =>
       pD h0 (j0 ▸ mUr _ hz4) (by
         have ja:z∈F1∪F2:=j1 ▸ mUr _ hz2
         rcases pU ja with jo | jn
         . exact mUl _ (mUr _ jo)
         . exact mUr _ jn)
      have j5:Disjoint Q.support.toFinset G2:=rD λ w hwQ hwG2=>by
       rcases h9 w (pTf hwQ) with kp | hP | ko
       . exact pD h1.2.2.2.1 kp hwG2
       . exact pD h1.2.2.2.1 (kd w hP (j1 ▸ mUr _ hwG2) ▸ k4) hwG2
       .
         exact pD h0 (j0 ▸ mUl _ ko) (by
          have ja:w∈F1∪F2:=j1 ▸ mUr _ hwG2
          rcases pU ja with jo | jn
          . exact mUl _ (mUr _ jo)
          . exact mUr _ jn)
      have j4:Disjoint Q.support.toFinset G4:=rD λ w hwQ hwG4=>by
       rcases h9 w (pTf hwQ) with kp | hP | ko
       .
         exact pD h0 (j0 ▸ mUr _ hwG4) (by
          have ja:w∈F1∪F2:=j1 ▸ mUl _ kp
          rcases pU ja with jo | jn
          . exact mUl _ (mUr _ jo)
          . exact mUr _ jn)
       . exact pD h2.2.2.2.1 (kc w hP (j0 ▸ mUr _ hwG4) ▸ ky) hwG4
       . exact pD h2.2.2.2.1 ko hwG4
      have j9:Disjoint j2 G2:=disjoint_union_left.mpr
       ⟨disjoint_union_left.mpr ⟨h1.2.2.1,rD λ z ji hzG2 =>
         pD h6 ji (by
          have ja:z∈F1∪F2:=j1 ▸ mUr _ hzG2
          rcases pU ja with jo | jn
          . exact mUl _ (mUr _ jo)
          . exact mUr _ jn)⟩,j5⟩
      have j8:Disjoint j2 G4:=disjoint_union_left.mpr
       ⟨disjoint_union_left.mpr ⟨rD λ z jk hzG4 =>
         pD h0 (j0 ▸ mUr _ hzG4)
          (mUl _ (mUl _ (mUr _ jk))),
         h2.2.2.1⟩,j4⟩
      have jj:j2.card<=10*m*(j+1):=by
       have we:=cUl (A1∪A2) Q.support.toFinset;have wd:=cUl A1 A2;have hc3:=q0y Q;have wp:=h1.2.2.2.2.2.2.1;have wi:=h2.2.2.2.2.2.2.1
       have w8:10*m*(j+1)=10*m*j+10*m:=by ring
       dsimp only[j2,m,m_rob,n] at *;omega
      refine ⟨u2,u4,G2,G4,j2,l1+Q.length+l2,
       ⟨k0,j9,j8,jd,h1.2.2.2.2.2.1,
        q0B (q0A h2.2.2.2.2.2.1 j3) (by dsimp only[m,m_rob,n];omega),
        jj,λ i hi=>?_⟩⟩
      let i1:=min i j;let i2:=i - i1;have hi1:i1<=j:=min_le_right i j
      have hi2:i2<=1:=by omega
      have hi_sum:i1+i2=i:=by omega
      obtain ⟨R1,ju,hR1_len⟩:=h1.2.2.2.2.2.2.2 i1 hi1;obtain ⟨R2,jt,hR2_len⟩:=h2.2.2.2.2.2.2.2 i2 hi2
      have k7:∀ w∈R1.support,w∈j2∪{u2,u4}:=λ w hw=>by
       have h:=q0w R1 (mUr _ (mem_insert_self u1 {u2})) w hw
       rcases pU h with hA | ka
       . exact mUl _ (mUl _ (mUl _ hA))
       .
         simp only[mem_insert,mSg] at ka
         rcases ka with rfl | rfl
         . exact mUl _ (mUr _ (rT (wSm Q)))
         . exact mUr _ (mem_insert_self w {u4})
      have k6:∀ w∈R2.support,w∈j2∪{u2,u4}:=λ w hw=>by
       have h:=q0w R2 (mUr _ (mem_insert_self u3 {u4})) w hw
       rcases pU h with hA | k1
       . exact mUl _ (mUl _ (mUr _ hA))
       .
         simp only[mem_insert,mSg] at k1
         rcases k1 with rfl | rfl
         . exact mUl _ (mUr _ (rT (wEm Q)))
         . exact mUr _ (mem_insert_of_mem (mSs w))
      have km:∀ w∈Q.support,w∈j2∪{u2,u4}:=λ w hw =>
       mUl _ (mUr _ (rT hw))
      let kr:=(q0r R1 k7).reverse;let Q':=q0r Q km;let w7:=q0r R2 k6
      have wg:(kr.append Q').IsPath:=q0x kr Q' (q0v _ _ ju).reverse
       (q0v _ _ k8) (λ w hw1 hw2=>by
         rw[q0q,q0s] at hw1;rw[q0s] at hw2;have jp:=q0w R1 (mUr _ (mem_insert_self u1 {u2})) w hw1
         rcases pU jp with kf | jl
         .
          exfalso;rcases h9 w hw2 with kp | hP | ko
          . exact pD h1.2.1 kf kp
          . exact (j6 w hP).1 kf
          .
           exact pD h0 (j0 ▸ mUl _ ko)
             (mUl _ (mUl _ (mUr _ kf)))
         .
          simp only[mem_insert,mSg] at jl
          rcases jl with rfl | rfl
          . rfl
          . exact absurd h1.2.2.2.2.2.1.2.1 (pD j5 (rT hw2)))
      have kl:((kr.append Q').append w7).IsPath:=q0x (kr.append Q') w7 wg
       (q0v _ _ jt) (λ w hw1 hw2=>by
         rw[q0s] at hw2;have kq:=q0w R2 (mUr _ (mem_insert_self u3 {u4})) w hw2;rw[wSa] at hw1
         rcases hw1 with w1 | wh
         .
          exfalso;rw[q0q,q0s] at w1;have jp:=q0w R1 (mUr _ (mem_insert_self u1 {u2})) w w1
          have kt:w∈U':=by
           rcases pU jp with hA | ka
           . exact mUl _ (mUl _ (mUr _ hA))
           .
             simp only[mem_insert,mSg] at ka;have jl:w∈F1∪F2:=j1 ▸ (by rcases ka with rfl | rfl;exact mUl _ h1.2.2.2.2.1.2.1;exact mUr _ h1.2.2.2.2.2.1.2.1)
             rcases pU jl with jo | jn
             . exact mUl _ (mUr _ jo)
             . exact mUr _ jn
          rcases pU kq with wi | k1
          . exact pD h6 wi kt
          . simp only[mem_insert,mSg] at k1;exact pD h0 (j0 ▸ (by rcases k1 with rfl | rfl;exact mUl _ h2.2.2.2.2.1.2.1;exact mUr _ h2.2.2.2.2.2.1.2.1)) kt
         .
          rw[q0s] at wh
          rcases pU kq with ke | kv
          .
           exfalso;rcases h9 w wh with kp | hP | ko
           .
             exact pD h6 ke (by
              have jl:w∈F1∪F2:=j1 ▸ mUl _ kp
              rcases pU jl with jo | jn
              . exact mUl _ (mUr _ jo)
              . exact mUr _ jn)
           . exact (j6 w hP).2 ke
           . exact pD h2.2.1 ke ko
          .
           simp only[mem_insert,mSg] at kv
           rcases kv with rfl | rfl
           . rfl
           . exact absurd h2.2.2.2.2.2.1.2.1 (pD j4 (rT wh)))
      refine ⟨(kr.append Q').append w7,kl,?_⟩;dsimp only[kr,Q',w7];simp only[wLa,wLr,q0t];omega
     rcases pU ki with wo | wn <;> rcases pU wf with wm | wl
     . exact jb v1 v2 v3 v4 F1 F2 F3 F4 h5 h8 rfl rfl wo wm
     . exact jb v1 v2 v4 v3 F1 F2 F4 F3 h5 (q1i h8) rfl (union_comm _ _) wo wl
     . exact jb v2 v1 v3 v4 F2 F1 F3 F4 (q1i h5) h8 (union_comm _ _) rfl wn wm
     . exact jb v2 v1 v4 v3 F2 F1 F4 F3 (q1i h5) (q1i h8) (union_comm _ _) (union_comm _ _) wn wl
 obtain ⟨v1,v2,F1,F2,A,l,j7⟩:=w9 r hr1 le_rfl;obtain ⟨F1',jg,jw⟩:=q0E j7.2.2.2.2.1 jx jh;obtain ⟨F2',jf,jv⟩:=q0E j7.2.2.2.2.2.1 jx jh
 exact ⟨v1,v2,F1',F2',A,l,
  ⟨j7.1,disjoint_of_subset_right jg j7.2.1,
   disjoint_of_subset_right jf j7.2.2.1,
   Disjoint.mono jg jf j7.2.2.2.1,
   jw,jv,j7.2.2.2.2.2.2.1,j7.2.2.2.2.2.2.2⟩⟩
lemma q1D {e2:O} {K:ℕ}
  (k1:0 < e2) (jd:e2<=1/25) (hK:10<=K) :
  ∃ d0:ℕ,100<=d0/\∀ {V:Type*} [Fintype V] (H:SG V) (S U F1 F2:FS V) (jj:V->Bool)
   (d D l:ℕ) (v1 v2:V),
   d0<=d->d<=#S ->
   qk H jj ->
   qQ H S (1/100) (e2*(d:O)) ->
   (∀ v∈S,d<=dS H S v) ->
   ¬ qH H S (d/2) ->
   (log (#S:O))^10<=(D:O)->(D:O)<=(log (#S:O))^K ->
   U⊆S->(#U:O)<=(D:O)/(2*(log (#S:O))^3) ->
   let m:=4*floor (21000*(log (#S:O))^3)
   q0z H (S \ U) v1 D m F1->q0z H (S \ U) v2 D m F2->Disjoint F1 F2 ->
   (log (#S:O))^7<=(l:O)->(l:O)<=(#S:O)/(log (#S:O))^12 ->
   (Even l↔jj v1=jj v2) ->
   ∃ p:(q3 H (S \ U)).Walk v1 v2,p.IsPath/\p.length=l:=by
 have k8:(0:O) < 1/100:=by norm_num
 have k7:(1/100:O) < 1:=by norm_num
 obtain ⟨d1,jk,jr⟩:=q1C (K:=K) k1 jd hK;obtain ⟨d2,hd2_100,k5⟩:=q1g k8 k7 k1 jd
 have kg:∀ᶠ x:O in atTop,
   (1000:O)<=x/\(4:O)<=log x /\
   (log x)^K<=x/(log x)^10 /\
   100/(1/100:O)*(log x)^3<=4*(21000*(log x)^3 - 1) /\
   220*(4*21000*(log x)^3)^2+22*(4*21000*(log x)^3)+1<=(log x)^7/2:=by
  let C:O:=220*(4*21000)^2+22*(4*21000)+1
  filter_upwards [eGe (1000:O),
   lGe (max 4 (2*C+1)),
   q01 (C:=1) (K+10) (β:=1) (by norm_num)] with x hx hl hlogK
  rw[one_mul,r1] at hlogK;have hl4:4<=log x:=lT (lMl _ _) hl;have hlC:2*C+1<=log x:=lT (lMr _ _) hl
  have k6:1<=log x:=by linarith
  refine ⟨hx,hl4,?_,?_,?_⟩
  . rw[lDi (by positivity),<- pow_add];exact hlogK
  . have:(1:O)<=(log x)^3:=oLp k6;linarith
  .
   have h36:(log x)^3<=(log x)^6:=pLr k6 (by omega);have h16:(1:O)<=(log x)^6:=oLp k6
   have hbd:220*(4*21000*(log x)^3)^2+22*(4*21000*(log x)^3)+1 <=
      C*(log x)^6:=by
     have heq:220*(4*21000*(log x)^3)^2=220*(4*21000)^2*(log x)^6:=by ring
     dsimp only[C];nlinarith
   have h2:=mlR (show 2*C<=log x by linarith) (show (0:O)<=(log x)^6 by positivity);linarith [show log x*(log x)^6=(log x)^7 by ring]
 rw[eAt] at kg;obtain ⟨B0,hB0⟩:=kg
 refine ⟨max (max d1 d2) (ceil B0),lT (lT jk (lMl _ _)) (lMl _ _),
  λ{V} _ H S U F1 F2 jj d D l v1 v2 hd hdn hbip hexp hmindeg hnoK2 hDlb hDub hUS hUcard hF1 hF2 hFdisj hllb hlub hpar=>?_⟩
 have hd1:d1<=d:=lT (lMl _ _) (lT (lMl _ _) hd);have hd2:d2<=d:=lT (lMr _ _) (lT (lMl _ _) hd);have hnB:B0<=(#S:O):=(nLc B0).trans (by exact_mod_cast ((lMr _ _).trans hd).trans hdn);obtain ⟨hn1000,hln4,jv,hm_lb_ev,h220m2⟩:=hB0 (#S:O) hnB;set n:O:=(#S:O);set h4:=floor (21000*(log n)^3);set m:=4*h4
 have hm_pos:1<=m:=by
  have:21000*(log n)^3 - 1 < (h4:O):=by linarith [nL1 (21000*(log n)^3)]
  have h1:(1:O)<=(log n)^3:=oLp (by linarith)
  have:(1:O)<=(h4:O):=by linarith
  have:1<=h4:=by exact_mod_cast this
  omega
 let U':=U∪F1∪F2;have jl:U'⊆S:=uS (uS hUS (hF1.1.trans sS)) (hF2.1.trans sS)
 have je:#U'<=4*D:=by
  have hUleD:#U<=D:=by
   have h1:(#U:O)<=(D:O):=hUcard.trans (dLs (nCn D) (by
     have:(1:O)<=(log n)^3:=oLp (by linarith);linarith))
   exact_mod_cast h1
  have ka:=cUl (U∪F1) F2;have k9:=cUl U F1;rw[hF2.2.2.1] at ka;rw[hF1.2.2.1] at k9;dsimp only[U'];omega
 obtain ⟨v3,v₄,F3,F₄,A,jb,h0⟩ :=
  jr H S U' jj d D (22*m) hd1 hdn hbip hexp hmindeg hnoK2 hDlb hDub (by omega) (by dsimp only[m,h4,n];omega) jl je
 have hA_card_bd:(220*m^2+22*m+1:O)<=(log n)^7/2:=by
  have jc:(m:O)<=4*21000*(log n)^3:=by
   have:(h4:O)<=21000*(log n)^3:=nFl (by positivity)
   dsimp only[m];push_cast;linarith
  have hsq:(m:O)^2<=(4*21000*(log n)^3)^2:=pLl (nCn m) jc 2;linarith
 have hlA_le:jb<=220*m^2+1:=by
  have h1:=q1l h0;have h2:=h0.2.2.2.2.2.2.1
  have k4:10*m*(22*m)=220*m^2:=by ring
  dsimp only[m,h4,n] at h2 k4 ⊢;omega
 have h22_le_l:22*m+jb<=l:=by
  have h1:((22*m+jb:ℕ):O)<=(l:O):=by
   have h2:((22*m+jb:ℕ):O)<=220*(m:O)^2+22*(m:O)+1:=by
     have:22*m+jb<=220*m^2+22*m+1:=by omega
     exact_mod_cast this
   linarith
  exact_mod_cast h1
 let j7:=U∪A;let h9:=l - 22*m - jb;have ji:j7⊆S:=uS hUS (h0.1.trans sS)
 have ja:(j7.card:O)<=(D:O)/(log n)^3:=by
  have hA_le:(#A:O)<=(D:O)/(2*(log n)^3):=by
   have hA1:(#A:O)<=220*(m:O)^2:=by
     have h2:=h0.2.2.2.2.2.2.1
     have:10*m*(22*m)=220*m^2:=by ring
     exact_mod_cast h2.trans_eq this
   have hlog7:(log n)^7/2<=(D:O)/(2*(log n)^3):=by
     rw[div_le_div_iff₀ (by norm_num) (by positivity)];linarith [show (log n)^7*(2*(log n)^3)=2*(log n)^10 by ring]
   linarith
  have h1:(j7.card:O)<=(#U:O)+(#A:O):=by exact_mod_cast cUl U A
  linarith [show (D:O)/(2*(log n)^3)+(D:O)/(2*(log n)^3)=(D:O)/(log n)^3 by ring]
 let v4:Fin 4->V := ![v1,v2,v3,v₄];let F4:Fin 4->FS V := ![F1,F2,F3,F₄]
 have h3:∀ i:Fin 4,q0z H (S \ j7) (v4 i) D m (F4 i):=by
  intro i;fin_cases i
  .
   refine ⟨λ z hz=>rS ⟨(pS (hF1.1 hz)).1,λ h=>by
     rcases pU h with hU | hA
     . exact (pS (hF1.1 hz)).2 hU
     . exact (pS (h0.1 hA)).2 (mUl _ (mUr _ hz))⟩,
    hF1.2.1,hF1.2.2.1,hF1.2.2.2⟩
  .
   refine ⟨λ z hz=>rS ⟨(pS (hF2.1 hz)).1,λ h=>by
     rcases pU h with hU | hA
     . exact (pS (hF2.1 hz)).2 hU
     . exact (pS (h0.1 hA)).2 (mUr _ hz)⟩,
    hF2.2.1,hF2.2.2.1,hF2.2.2.2⟩
  .
   refine ⟨λ z hz=>rS ⟨(pS (h0.2.2.2.2.1.1 hz)).1,λ h=>by
     rcases pU h with hU | hA
     . exact (pS (h0.2.2.2.2.1.1 hz)).2 (mUl _ (mUl _ hU))
     . exact pD h0.2.1 hA hz⟩,
    h0.2.2.2.2.1.2.1,h0.2.2.2.2.1.2.2.1,h0.2.2.2.2.1.2.2.2⟩
  .
   refine ⟨λ z hz=>rS ⟨(pS (h0.2.2.2.2.2.1.1 hz)).1,λ h=>by
     rcases pU h with hU | hA
     . exact (pS (h0.2.2.2.2.2.1.1 hz)).2 (mUl _ (mUl _ hU))
     . exact pD h0.2.2.1 hA hz⟩,
    h0.2.2.2.2.2.1.2.1,h0.2.2.2.2.2.1.2.2.1,h0.2.2.2.2.2.1.2.2.2⟩
 have jh:∀ i j:Fin 4,i≠j->Disjoint (F4 i) (F4 j):=by
  intro i j hij;fin_cases i <;> fin_cases j <;> (try exact absurd rfl hij) <;> dsimp only[F4,Matrix.cons_val_zero,Matrix.cons_val_succ,Matrix.head_cons]
  . exact hFdisj
  . exact dR.mpr λ z hz3 hz1=>(pS (h0.2.2.2.2.1.1 hz3)).2 (mUl _ (mUr _ hz1))
  . exact dR.mpr λ z hz4 hz1=>(pS (h0.2.2.2.2.2.1.1 hz4)).2 (mUl _ (mUr _ hz1))
  . exact hFdisj.symm
  . exact dR.mpr λ z hz3 hz2=>(pS (h0.2.2.2.2.1.1 hz3)).2 (mUr _ hz2)
  . exact dR.mpr λ z hz4 hz2=>(pS (h0.2.2.2.2.2.1.1 hz4)).2 (mUr _ hz2)
  . exact rD λ z hz3 hz1=>(pS (h0.2.2.2.2.1.1 hz3)).2 (mUl _ (mUr _ hz1))
  . exact rD λ z hz3 hz2=>(pS (h0.2.2.2.2.1.1 hz3)).2 (mUr _ hz2)
  . exact h0.2.2.2.1
  . exact rD λ z hz4 hz1=>(pS (h0.2.2.2.2.2.1.1 hz4)).2 (mUl _ (mUr _ hz1))
  . exact rD λ z hz4 hz2=>(pS (h0.2.2.2.2.2.1.1 hz4)).2 (mUr _ hz2)
  . exact h0.2.2.2.1.symm
 have jx:100/(1/100:O)*(log n)^3<=(m:O):=by
  have:21000*(log n)^3 - 1 < (h4:O):=by linarith [nL1 (21000*(log n)^3)]
  dsimp only[m];push_cast;linarith
 have jc:(m:O)<=1000/(1/100:O)*(log n)^3:=by
  have:(h4:O)<=21000*(log n)^3:=nFl (by positivity)
  dsimp only[m];push_cast;linarith
 obtain ⟨i1,i2,j1,j2,jz,jy,P,Q,h8,h7,h6,j5,j4⟩ :=
  k5 H S j7 d D m h9 v4 F4 hd2 hdn hexp hmindeg hDlb (hDub.trans jv) jx jc
   ((by exact_mod_cast (show h9<=l by omega):(h9:O)<=(l:O)).trans hlub)
   ji ja h3 jh
 have h5:∀ (u3 u4:V) (G3 G4:FS V),
   q1h H (S \ U') D m (22*m) u3 G3 u4 G4 A jb ->
   ∀ (P1:(q3 H (S \ j7)).Walk v1 u3) (Q1:(q3 H (S \ j7)).Walk v2 u4),
   P1.IsPath->Q1.IsPath->Disjoint P1.support.toFinset Q1.support.toFinset ->
   h9<=P1.length+Q1.length->P1.length+Q1.length<=h9+22*m ->
   ∃ p:(q3 H (S \ U)).Walk v1 v2,p.IsPath/\p.length=l:=by
  intro u3 u4 G3 G4 hA' P1 Q1 hP1 hQ1 j0 kf ke
  have hdiff_le:l - P1.length - Q1.length - jb<=22*m:=by dsimp only[h9] at kf ke;omega
  have hdiff_eq:P1.length+Q1.length+jb+(l - P1.length - Q1.length - jb)=l:=by dsimp only[h9] at kf ke;omega
  obtain ⟨R0,_,jn⟩:=hA'.2.2.2.2.2.2.2 0 (Nat.zero_le _);have j6:qk (q3 H (S \ j7)) jj:=λ x y h=>hbip x y h.1
  have js:qk (q3 H (A∪{u3,u4})) jj:=λ x y h=>hbip x y h.1
  have jp:=qm j6 P1;have jo:=qm j6 Q1;have j9:=qm js R0;rw[jn,mul_zero,add_zero] at j9
  have j8:Even (l - P1.length - Q1.length - jb):=by
   cases ka:jj v1 <;> cases k9:jj v2 <;> cases hc3:jj u3 <;> cases hc4:jj u4 <;>
     simp [ka,k9,hc3,hc4,Nat.even_iff] at hpar jp jo j9 ⊢ <;> omega
  obtain ⟨i,hi_eq⟩:=j8
  have k0:i<=22*m:=by omega
  obtain ⟨R,jm,hR_len⟩:=hA'.2.2.2.2.2.2.2 i k0
  have ju:∀ w∈P1.support,w∈S \ U:=λ w hw=>by
   have h:=q0w P1 (h3 0 |>.1 (h3 0 |>.2.1)) w hw;exact rS ⟨(pS h).1,λ hU=>(pS h).2 (mUl _ hU)⟩
  have jt:∀ w∈Q1.support,w∈S \ U:=λ w hw=>by
   have h:=q0w Q1 (h3 1 |>.1 (h3 1 |>.2.1)) w hw;exact rS ⟨(pS h).1,λ hU=>(pS h).2 (mUl _ hU)⟩
  have jg:∀ w∈P1.support,w ∉ A:=λ w hw hA =>
   (pS (q0w P1 (h3 0 |>.1 (h3 0 |>.2.1)) w hw)).2 (mUr _ hA)
  have jf:∀ w∈Q1.support,w ∉ A:=λ w hw hA =>
   (pS (q0w Q1 (h3 1 |>.1 (h3 1 |>.2.1)) w hw)).2 (mUr _ hA)
  have k2:∀ w∈R.support,w∈S \ U:=λ w hw=>by
   have h:=q0w R (mUr _ (mem_insert_self u3 {u4})) w hw;have j3:S \ U'⊆S \ U:=sSs sR (sUl.trans sUl)
   rcases pU h with hA | jq
   . exact j3 (hA'.1 hA)
   .
     simp only[mem_insert,mSg] at jq
     rcases jq with rfl | rfl
     . exact j3 (hA'.2.2.2.2.1.1 hA'.2.2.2.2.1.2.1)
     . exact j3 (hA'.2.2.2.2.2.1.1 hA'.2.2.2.2.2.1.2.1)
  let jw:=q0r P1 ju;let R':=q0r R k2;let k3:=q0r Q1 jt
  have hPR:(jw.append R').IsPath:=q0x jw R' (q0v _ _ hP1)
   (q0v _ _ jm) (λ w hw1 hw2=>by
     rw[q0s] at hw1 hw2;have h:=q0w R (mUr _ (mem_insert_self u3 {u4})) w hw2
     rcases pU h with hA | jq
     . exact absurd hA (jg w hw1)
     .
      simp only[mem_insert,mSg] at jq
      rcases jq with rfl | rfl
      . rfl
      . exact absurd (wEm Q1) (pD j0 (rT hw1) ∘ rT))
  have kb:((jw.append R').append k3.reverse).IsPath:=q0x (jw.append R') k3.reverse hPR
   (q0v _ _ hQ1).reverse (λ w hw1 hw2=>by
     rw[q0q,q0s] at hw2;rw[wSa] at hw1
     rcases hw1 with kd | kc
     . rw[q0s] at kd;exact absurd (rT hw2) (pD j0 (rT kd))
     .
      rw[q0s] at kc;have h:=q0w R (mUr _ (mem_insert_self u3 {u4})) w kc
      rcases pU h with hA | jq
      . exact absurd hA (jf w hw2)
      .
       simp only[mem_insert,mSg] at jq
       rcases jq with rfl | rfl
       . exact absurd (rT hw2) (pD j0 (rT (wEm P1)))
       . rfl)
  refine ⟨(jw.append R').append k3.reverse,kb,?_⟩;dsimp only[jw,R',k3];simp only[wLa,wLr,q0t];omega
 fin_cases i1 <;> fin_cases i2 <;> fin_cases j1 <;> fin_cases j2
 all_goals try exact absurd rfl jz
 all_goals try exact absurd rfl jy
 . exact h5 v3 v₄ F3 F₄ h0 P Q h8 h7 h6 j5 j4
 . exact h5 v₄ v3 F₄ F3 (q1i h0) P Q h8 h7 h6 j5 j4
 . exact h5 v₄ v3 F₄ F3 (q1i h0) Q P h7 h8 h6.symm (by rw[add_comm];exact j5) (by rw[add_comm];exact j4)
 . exact h5 v3 v₄ F3 F₄ h0 Q P h7 h8 h6.symm (by rw[add_comm];exact j5) (by rw[add_comm];exact j4)
lemma q1E : ∃ d0:ℕ,100<=d0/\∀ {V:Type*} [Fintype V] (H:SG V) (S:FS V) (j8:V->Bool) (d l:ℕ) (x y:V), d0<=d->d<=#S -> qk H j8 -> qQ H S (1/100) ((1/50:O)*(d:O)) -> (∀ v∈S,d<=dS H S v) -> ¬ qH H S (d/2) -> x∈S->y∈S->x≠y -> (log (#S:O))^7<=(l:O)->(l:O)<=(#S:O)/(log (#S:O))^12 -> (Even l↔j8 x=j8 y) -> ∃ p:(q3 H S).Walk x y,p.IsPath/\p.length=l:=by
 have ja:(0:O) < 1/100:=by norm_num
 have j9:(1/100:O) < 1:=by norm_num
 have j6:(0:O) < 1/50:=by norm_num
 have j3:(1/50:O)<=1/25:=by norm_num
 obtain ⟨d1,h4,h5⟩:=q19 (t:=2) (s:=1) (K:=11) ja j9 j6 (by norm_num) (by omega) (by omega) (by omega);obtain ⟨d2,hd2_100,hfc⟩:=q1D (K:=11) j6 j3 (by omega)
 have je:∀ᶠ z:O in atTop,
   (4:O)<=log z /\
   (log z)^10+1<=(log z)^11 /\
   5*(40/(1/100:O)*(log z)^3)<=4*(21000*(log z)^3 - 1):=by
  filter_upwards [lGe 4] with z hl
  have jd:1<=log z:=by linarith
  have hl3:(1:O)<=(log z)^3:=oLp jd;have hl10:(1:O)<=(log z)^10:=oLp jd;refine ⟨hl,?_,by linarith⟩
  have:(log z)^11=log z*(log z)^10:=by ring
  nlinarith
 rw[eAt] at je;obtain ⟨B0,hB0⟩:=je
 refine ⟨max (max d1 d2) (ceil B0),lT (lT h4 (lMl _ _)) (lMl _ _),
  λ{V} _ H S j8 d l x y hd hdn hbip hexp hmindeg hnoK2 hxS hyS hxy hllb hlub hpar=>?_⟩
 have jf:d1<=d:=lT (lMl _ _) (lT (lMl _ _) hd);have hd2:d2<=d:=lT (lMr _ _) (lT (lMl _ _) hd);have hnB:B0<=(#S:O):=(nLc B0).trans (by exact_mod_cast ((lMr _ _).trans hd).trans hdn);obtain ⟨hln4,j5,h5m_le⟩:=hB0 (#S:O) hnB;obtain ⟨x0,c,jb⟩:=q0K H S ⟨x,hxS⟩ (λ v hv=>by have:=hmindeg v hv;have:=h4.trans jf;omega)
 set n:O:=(#S:O);set D:=ceil ((log n)^10);set m:=4*floor (21000*(log n)^3);have j1:(log n)^10<=(D:O):=nLc _;have j0:(D:O)<=(log n)^11:=((ceil_lt_add_one (by positivity)).le).trans j5
 have hD1:1<=D:=by
  have:(1:O)<=(log n)^10:=oLp (by linarith)
  exact_mod_cast this.trans j1
 obtain ⟨F,h9,j7,j4⟩:=h5 H S {x,y} d D x0 c jf hdn hexp
  (λ v hv=>Nat.le_trans (nSl d 1) (hmindeg v hv)) jb
  (by intro z hz;simp only[mem_insert,mSg] at hz;rcases hz with rfl | rfl;exact hxS;exact hyS)
  (card_pos.mpr ⟨x,by simp⟩) card_le_two hD1 j0
 have h3:5*floor (40/(1/100:O)*(log n)^3)<=m:=by
  have h1:(floor (40/(1/100:O)*(log n)^3):O)<=40/(1/100:O)*(log n)^3:=nFl (by positivity)
  have h2:21000*(log n)^3 - 1 < (floor (21000*(log n)^3):O):=by linarith [nL1 (21000*(log n)^3)]
  exact_mod_cast (show (5*floor (40/(1/100:O)*(log n)^3):O)<=(m:O) by dsimp only[m];push_cast;linarith)
 have h7:x∈({x,y}:FS V):=by simp
 have h6:y∈({x,y}:FS V):=by simp
 have h0:Disjoint (F x 0) (F y 0):=rD λ z hzx hzy=>by
  by_cases h1:z=x
  . subst h1;exact pD (j7 y h6 0) (rS ⟨hzy,rG hxy⟩) (mUr _ h7)
  .
   by_cases h2:z=y
   . subst h2;exact pD (j7 x h7 0) (rS ⟨hzx,rG hxy.symm⟩) (mUr _ h6)
   .
    exact pD (j4 x h7 0 y h6 0 (by simp [hxy]))
     (rS ⟨hzx,rG h1⟩) (rS ⟨hzy,rG h2⟩)
 have jc:S \ ∅=S:=sdiff_empty
 obtain ⟨p,h8,j2⟩ :=
  hfc H S ∅ (F x 0) (F y 0) j8 d D l x y hd2 hdn hbip hexp hmindeg hnoK2 j1 j0
   (empty_subset _) (by simp;positivity)
   (jc.symm ▸ q0B (h9 x h7 0) h3)
   (jc.symm ▸ q0B (h9 y h6 0) h3)
   h0 hllb hlub hpar
 exact ⟨q0r p (λ w hw=>sS (q0w p (jc.symm ▸ hxS) w hw)),
  q0v _ _ h8,by rw[q0t,j2]⟩
lemma q1F : ∀ x y:O,exp 13<=x->x<=y->x/(log x)^12<=y/(log y)^12:=by
 intro x y hx h8
 have h3:∀ z∈Set.Icc x y,HasDerivAt (λ t:O=>t/(log t)^12)
   ((log z - 12)/(log z)^13) z:=by
  intro z hz;have h0:0 < z:=lL2 (ePp 13) (hx.trans hz.1)
  have h4:13<=log z:=by rw[lIe h0];exact hx.trans hz.1
  have h2:log z≠0:=by linarith
  have h1:=(hasDerivAt_id z).div ((Real.hasDerivAt_log h0.ne').pow 12) (pow_ne_zero 12 h2);refine h1.congr_deriv ?_;simp only[Pi.pow_apply,id_eq,Nat.cast_ofNat,Nat.reduceSub,one_mul]
  have h9:z*(12*(log z)^11*z⁻¹)=12*(log z)^11:=by
   rw[mul_comm (12*(log z)^11) z⁻¹,<- mul_assoc,mul_inv_cancel₀ h0.ne',one_mul]
  rw[h9];have h5:(log z)^12≠0:=pow_ne_zero 12 h2;rw[div_eq_div_iff (pow_ne_zero 2 h5) (pow_ne_zero 13 h2)];ring
 have h6:MonotoneOn (λ t:O=>t/(log t)^12) (Set.Icc x y):=by
  apply monotoneOn_of_deriv_nonneg (convex_Icc x y)
  . exact λ z hz=>(h3 z hz).continuousAt.continuousWithinAt
  . exact λ z hz=>(h3 z (interior_subset hz)).differentiableAt.differentiableWithinAt
  .
   intro z hz;have h7:=interior_subset hz;have h0:0 < z:=lL2 (ePp 13) (hx.trans h7.1)
   have h4:13<=log z:=by rw[lIe h0];exact hx.trans h7.1
   rw[(h3 z h7).deriv];exact div_nonneg (by linarith) (by positivity)
 exact h6 ⟨le_rfl,h8⟩ ⟨h8,le_rfl⟩ h8
lemma q1G : ∃ d0:ℕ,100<=d0/\∀ {V:Type*} [Fintype V] (G:SG V) (S0:FS V) (d:ℕ), d0<=d->S0.Nonempty -> 8*(d:O)*(#S0:O)<=∑ u∈S0,(dS G S0 u:O) -> ∃ L:O,(d:O)/(log (d:O))^13<=L /\ ∀ m:ℕ,Even m->(log L)^8<=(m:O)->(m:O)<=L->m∈G.cycleLengths:=by
 obtain ⟨d1,h0,jg⟩:=q1E
 have jw:∀ᶠ x:O in atTop,
   exp 2000000<=x /\
   (1000:O)<=log x /\
   x/(log x)^13<=x - 2 /\
   (log x)^12<=x^(1/2:O) /\
   (6:O)<=(log (x - 2))^8:=by
  filter_upwards [eGe (exp 2000000),
   q01 (C:=1) 12 (β:=1/2) (by norm_num)] with x hx hlog12
  rw[one_mul] at hlog12;have j0:0 < x:=lL2 (ePp _) hx
  have hlx:2000000<=log x:=by rw[lIe j0];exact hx
  have jc:(2:O)<=(log x)^13:=by
   calc
    (2:O)<=2000000^13:=by norm_num
    _<=(log x)^13:=pLl (by norm_num) hlx 13
  have hx4:(4:O)<=x:=by linarith [add_one_le_exp (2000000:O)]
  have jq:(2:O)<=log (x - 2):=by
   rw[lIe (by linarith)]
   have:exp 2<=exp 2000000/2:=by
    have h1:(2:O)<=exp 100:=by linarith [add_one_le_exp (100:O)]
    have h2:exp 2*2<=exp 2*exp 100:=mlL h1 (ePp _).le;rw[<- exp_add] at h2;have h3:exp (2+100)<=exp 2000000:=eLe.mpr (by norm_num);linarith
   linarith
  refine ⟨hx,by linarith,?_,hlog12,?_⟩
  . have h1:x/(log x)^13<=x/2:=dLl j0.le (by norm_num) jc;linarith
  .
   calc (6:O)<=2^8:=by norm_num
    _<=(log (x - 2))^8:=pLl (by norm_num) jq 8
 rw[eAt] at jw;obtain ⟨B0,jz⟩:=jw
 refine ⟨max d1 (ceil B0),lT h0 (lMl _ _),
  λ{V} _ G S0 d hd hS0 havg=>?_⟩
 have jm:d1<=d:=lT (lMl _ _) hd;have jx:B0<=(d:O):=(nLc B0).trans (by exact_mod_cast (lMr _ _).trans hd);obtain ⟨je,hlogd_1000,hd_sub2,_,jf⟩:=jz (d:O) jx
 obtain ⟨H,S,jl,ju,_,jj,ji,jr,jd⟩ :=
  qV G S0 (d:=d) (e2:=1/50) (by have:=h0.trans jm;omega) (by norm_num) hS0 havg
 have js:d<=#S:=by
  obtain ⟨u,hu⟩:=jj;exact (jd u hu).trans (cL (filter_subset _ _))
 by_cases jy:qH H S (d/2)
 .
  refine ⟨2*((d/2:ℕ):O),?_,λ m hm hmlb hmub=>?_⟩
  .
   have h1:(d:O) - 2<=2*((d/2:ℕ):O):=by
    have:d<=2*(d/2)+1:=by omega
    have:(d:O)<=2*((d/2:ℕ):O)+1:=by exact_mod_cast this
    linarith
   linarith
  .
   have hm6:6<=m:=by
    have h1:(d:O) - 2<=2*((d/2:ℕ):O):=by
     have:d<=2*(d/2)+1:=by omega
     have:(d:O)<=2*((d/2:ℕ):O)+1:=by exact_mod_cast this
     linarith
    have h2:=lLl (by linarith [add_one_le_exp (2000000:O)]) h1
    have h3:(6:O)<=(log (2*((d/2:ℕ):O)))^8 :=
     jf.trans (pLl (lNn (by linarith [add_one_le_exp (2000000:O)])) h2 8)
    exact_mod_cast h3.trans hmlb
   have hmr:m<=2*(d/2):=by exact_mod_cast hmub
   exact q4 ju (qI jy (by have:=h0.trans jm;omega) m hm hm6 hmr)
 .
  set n:O:=(#S:O);set L:O:=n/(log n)^12;have hnB:B0<=n:=jx.trans (by dsimp only[n];exact_mod_cast js);obtain ⟨j9,h7,_,h6,_⟩:=jz n hnB
  have jk:(d:O)/(log (d:O))^13<=L:=by
   have h1:(d:O)/(log (d:O))^13<=(d:O)/(log (d:O))^12:=by
    apply dLl (nCn d) (by positivity);exact pLr (by linarith) (by omega)
   have h2:=q1F (d:O) n ((eLe.mpr (by norm_num)).trans je) (by dsimp only[n];exact_mod_cast js);exact h1.trans h2
  refine ⟨L,jk,λ m hm hmlb hmub=>?_⟩
  have h5:0 < n:=lL2 (ePp _) j9
  have h8:n^(1/2:O)<=L:=by
   dsimp only[L];rw[lDi (by positivity)]
   have hsq:n^(1/2:O)*n^(1/2:O)=n:=by rw[<- rpow_add h5];norm_num
   have hmul:=mlL h6 (rNn h5.le (1/2:O));linarith
  have j2:log n/2<=log L:=by
   have h1:=lLl (rpow_pos_of_pos h5 _) h8;rw[Real.log_rpow h5] at h1;linarith
  have hm_ge_log7:(log n)^7+1<=(m:O):=by
   have h1:(log n/2)^8<=(log L)^8:=pLl (by linarith) j2 8
   have h2:(log n/2)^8=(log n/256)*(log n)^7:=by ring
   have h3:(2:O)<=log n/256:=by linarith
   have h4:(1:O)<=(log n)^7:=oLp (by linarith);nlinarith
  have hm_ge4:4<=m:=by
   have:(4:O)<=(log n)^7:=by
    calc
     (4:O)<=1000^7:=by norm_num
     _<=(log n)^7:=pLl (by norm_num) h7 7
   exact_mod_cast (show (4:O)<=(m:O) by linarith)
  obtain ⟨u,jv⟩:=jj;have j8:(S.filter (H.Adj u)).Nonempty:=card_pos.mp (by have:=jd u jv;have:=h0.trans jm;unfold dS at *;omega);obtain ⟨v,hv⟩:=j8;obtain ⟨hvS,jn⟩:=pF hv;have j6:u≠v:=H.ne_of_adj jn;have j5:jl u≠jl v:=ji u v jn
  have j3:Even (m - 1)↔jl u=jl v:=by
   obtain ⟨t,ht⟩:=hm
   have h9:¬ Even (m - 1):=by intro ⟨s,hs⟩;omega
   exact ⟨λ h=>absurd h h9,λ h=>absurd h j5⟩
  have jb:(log n)^7<=((m - 1:ℕ):O):=by
   rw[Nat.cast_sub (by omega),Nat.cast_one];linarith
  have ja:((m - 1:ℕ):O)<=n/(log n)^12:=by
   rw[Nat.cast_sub (by omega),Nat.cast_one];linarith
  obtain ⟨p,j4,j7⟩:=jg H S jl d (m - 1) u v jm js ji jr jd jy jv hvS j6 jb ja j3
  have jh:∀ {a b:V} (q:(q3 H S).Walk a b),∃ q':G.Walk a b,q'.support=q.support/\q'.length=q.length:=by
   intro a b q;induction q with
   | nil=>exact ⟨.nil,rfl,rfl⟩
   | cons hadj q' ih=>obtain ⟨r,hrs,hrl⟩:=ih;exact ⟨.cons (ju hadj.1) r,by simp [hrs],by simp [hrl]⟩
  obtain ⟨pG,jo,jp⟩:=jh p
  have j1:pG.IsPath:=by rw[wIp,jo];exact j4.support_nodup
  have jt:=qa pG j1 (by omega) (ju jn.symm)
  rwa [jp,j7,Nat.sub_add_cancel (by omega)] at jt
lemma q1H : ∀ x y:O,exp 9<=x->x<=y -> log x - 8*log (log x)<=log y - 8*log (log y):=by
 intro x y hx h8
 have h4:∀ z∈Set.Icc x y,HasDerivAt (λ t:O=>log t - 8*log (log t))
   (1/z - 8/(z*log z)) z:=by
  intro z hz;have h0:0 < z:=lL2 (ePp 9) (hx.trans hz.1)
  have h5:9<=log z:=by rw[lIe h0];exact hx.trans hz.1
  have h1:=Real.hasDerivAt_log h0.ne';have h2:=(Real.hasDerivAt_log (show log z≠0 by linarith)).comp z h1;have h3:=h1.sub (h2.const_mul 8);refine h3.congr_deriv ?_;simp only[div_eq_mul_inv,mul_inv];ring
 have h6:MonotoneOn (λ t:O=>log t - 8*log (log t)) (Set.Icc x y):=by
  apply monotoneOn_of_deriv_nonneg (convex_Icc x y)
  . exact λ z hz=>(h4 z hz).continuousAt.continuousWithinAt
  . exact λ z hz=>(h4 z (interior_subset hz)).differentiableAt.differentiableWithinAt
  .
   intro z hz;have h7:=interior_subset hz;have h0:0 < z:=lL2 (ePp 9) (hx.trans h7.1)
   have h5:9<=log z:=by rw[lIe h0];exact hx.trans h7.1
   rw[(h4 z h7).deriv];rw[sub_nonneg,div_le_div_iff₀ (by positivity) h0];nlinarith
 exact h6 ⟨le_rfl,h8⟩ ⟨h8,le_rfl⟩ h8
lemma q1I : ∀ e > (0:O),∀ᶠ k:O in atTop, ∀ (n:ℕ) (V:Type) [Fintype V] (G:SG V), 0 < n->Fintype.card V=n->(G.edgeSet.ncard:O)=k*n -> (∑ᶠ a∈G.cycleLengths,(1:O)/a)>=(1/2 - e)*log k:=by
 obtain ⟨d0,j3,hmd⟩:=q1G;intro e hε
 have hll_inf:Filter.Tendsto (λ x:O=>log (log x)) atTop atTop :=
  tL.comp tL
 filter_upwards [eGe (max (4*(d0:O)+8) (exp 4000010)),
  q01 (C:=8) 13 (β:=1/2) (by norm_num),
  q02 (C:=22/e) 1 (β:=1) (by norm_num),
  lGe (max 4000010 (10/e))] with k hk hlog13 hll_eps hlk
 rw[pow_one,r1] at hll_eps;have hk_d0:4*(d0:O)+8<=k:=lT (lMl _ _) hk;have j5:exp 4000010<=k:=lT (lMr _ _) hk;have hlk_big:4000010<=log k:=lT (lMl _ _) hlk;have j2:10/e<=log k:=lT (lMr _ _) hlk;have h4:0 < k:=lL2 (ePp _) j5;intro n V _ G hn j4 j8;let d:=floor (k/4);have h6:d0<=d:=nLf (by linarith);have hd_le_k4:(d:O)<=k/4:=nFl (by positivity)
 have j1:k/8<=(d:O):=by
  have:k/4 - 1 < (d:O):=by linarith [nL1 (k/4)]
  have:(8:O)<=k:=by linarith
  linarith
 have j6:(univ:FS V).Nonempty:=card_pos.mp (by rw[card_univ,j4];exact hn)
 have jb:8*(d:O)*(#(univ:FS V):O)<=∑ u∈(univ:FS V),(dS G univ u:O):=by
  have ja:∑ u∈(univ:FS V),(dS G univ u:O)=2*(G.edgeSet.ncard:O):=by
   exact_mod_cast q9 G
  rw[ja,j8,card_univ,j4];nlinarith [show (0:O)<=(n:O) by positivity]
 obtain ⟨L,j9,j7⟩:=hmd G univ d h6 j6 jb;let L0:O:=k/(8*(log k)^13)
 have h7:L0<=L:=by
  have j0:(0:O) < (d:O):=by linarith
  have h9:log (d:O)<=log k:=lLl j0 (by linarith);have h5:0 < log (d:O):=lPs (by exact_mod_cast (show 1 < d by have:=j3.trans h6;omega))
  have h1:k/(8*(log k)^13)<=(d:O)/(log k)^13:=by
   rw[show k/(8*(log k)^13)=(k/8)/(log k)^13 by ring];exact dLr j1 (by positivity)
  have h2:(d:O)/(log k)^13<=(d:O)/(log (d:O))^13 :=
   dLl j0.le (pow_pos h5 13) (pLl h5.le h9 13)
  exact (h1.trans h2).trans j9
 have h0:exp 2000000<=L0:=by
  have h1:k^(1/2:O)<=L0:=by
   dsimp only[L0];rw[lDi (by positivity)]
   have hsq:k^(1/2:O)*k^(1/2:O)=k:=by rw[<- rpow_add h4];norm_num
   have hmul:=mlL hlog13 (rNn h4.le (1/2:O));linarith
  have h2:exp 2000000<=k^(1/2:O):=by
   rw[rpow_def_of_pos h4];exact eLe.mpr (by linarith)
  exact h2.trans h1
 have hW_ge:=qG G (h0.trans h7) j7;rw[q7];have hmono_L:=q1H L0 L ((eLe.mpr (by norm_num)).trans h0) h7;have h8:0 < L0:=lL2 (ePp _) h0
 have hlogL0:log L0=log k - log 8 - 13*log (log k):=by
  dsimp only[L0];rw[Real.log_div h4.ne' (by positivity),log_mul (by norm_num) (by positivity),lP];ring
 have h3:log L0<=log k:=by
  apply lLl h8
  dsimp only[L0];exact dLs h4.le (by
   have:(1:O)<=(log k)^13:=oLp (by linarith);linarith)
 have hll_L0:log (log L0)<=log (log k) :=
  lLl (by rw[lIt h8];exact lL2 (exp_lt_exp.mpr (by norm_num)) h0) h3
 have hlog8:log 8<=3:=by
  have h1:(8:O)<=exp 3:=by
   have:=Real.sum_le_exp_of_nonneg (x:=(3:O)) (by norm_num) 4
   have hfin:∑ i∈range 4,(3:O)^i/(factorial i:O)=13:=by
    simp [sum_range_succ,factorial];norm_num
   linarith
  exact (lLl (by norm_num) h1).trans (by rw[log_exp])
 have h21ll:21*log (log k)<=e*log k:=by
  have h1:=mlL hll_eps hε.le;rw[<- mul_assoc,mul_div_cancel₀ _ hε.ne'] at h1;have hll_nn:0<=log (log k):=lNn (by linarith);linarith
 have h8_le_eps:(8:O)<=e*log k:=by
  have h1:=mlL j2 hε.le;rw[mul_div_cancel₀ _ hε.ne'] at h1;linarith
 linarith
end Erdos65LM
theorem OMA.solution : type_of% @Erdos65.erdos_65.variants.liu_montgomery :=
  Erdos65LM.q1I
end
