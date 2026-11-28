import FormalConjectures.ErdosProblems.«272»
import Mathlib.NumberTheory.Bertrand
/-! Credit: @gdyan2022 (the owner of the agent is credited as the solver). -/
namespace Szabo272
open Finset Filter Asymptotics
open Real (log)
private abbrev Zt:=Erdos272.IsArithInterSet
private abbrev Zf:=Finset
private theorem Za {α:Type*} {s:Finset α} {p:α->Prop} [DecidablePred p] {a:α}:a∈s.filter p↔a∈s/\p a:=Finset.mem_filter
private theorem Zb {α:Type*} [Preorder α] [LocallyFiniteOrder α] {a b x:α}:x∈Finset.Icc a b↔a≤ x/\x≤ b:=Finset.mem_Icc
private theorem Zc {α:Type*} {a:α} {s:Finset α}:a∈(s:Set α)↔a∈s:=Finset.mem_coe
private theorem Zd {α:Type*} [DecidableEq α] {a:α} {s t:Finset α}:a∈s∪t↔a∈s\/a∈t:=Finset.mem_union
private theorem Ze {α:Type*} [DecidableEq α] {a:α} {s:Finset α} (t:Finset α):a∈s->a∈s∪t:=Finset.mem_union_left t
private theorem Zg {α:Type*} [DecidableEq α] {a:α} (s:Finset α) {t:Finset α}:a∈t->a∈s∪t:=Finset.mem_union_right s
private theorem Zh {α β:Type*} {s:Finset α} {t:Finset β} {p:α × β}:p∈s ×ˢ t↔p.1∈s/\p.2∈t:=Finset.mem_product
private theorem Zi {α β:Type*} [DecidableEq β] {f:α->β} {s:Finset α} {b:β}:b∈s.image f↔∃ a∈s,f a=b:=Finset.mem_image
private theorem Zj {α:Type*} {a b:α}:a∈({b}:Finset α)↔a=b:=Finset.mem_singleton
private theorem Zk {α:Type*} {s t:Finset α}:Disjoint s t↔∀ ⦃a⦄,a∈s->a∉t:=Finset.disjoint_left
private theorem Zl {α:Type*} (p:α->Prop) [DecidablePred p] (s:Finset α):s.filter p⊆s:=Finset.filter_subset p s
private theorem Zm {α:Type*} {s t:Finset α} (h:s⊆t):s.card≤ t.card:=Finset.card_le_card h
private theorem Zn {α:Type*} [DecidableEq α] {a:α} {s t:Finset α}:a∈s∩t↔a∈s/\a∈t:=Finset.mem_inter
private theorem Zo {a b c:ℝ} (h:a≤ b) (hc:0≤ c):a*c≤ b*c:=mul_le_mul_of_nonneg_right h hc
private theorem Zp {a b c:ℝ} (h:b≤ c) (ha:0≤ a):a*b≤ a*c:=mul_le_mul_of_nonneg_left h ha
private theorem Zq {α:Type*} [DecidableEq α] {s t:Finset α} (h:Disjoint s t):(s∪t).card=s.card+t.card:=Finset.card_union_of_disjoint h
private theorem Zr {α:Type*} [DecidableEq α] {s₁ s₂:Finset α}:s₁⊆s₁∪s₂:=Finset.subset_union_left
private theorem Zs {α:Type*} [DecidableEq α] {s₁ s₂:Finset α}:s₂⊆s₁∪s₂:=Finset.subset_union_right
private theorem Zu {α:Type*} [DecidableEq α] {s₁ s₂ s₃:Finset α}:s₁⊆s₃->s₂⊆s₃->s₁∪s₂⊆s₃:=Finset.union_subset
private theorem Zw {α:Type*} [DecidableEq α] {a b:α} {s:Finset α}:a∈s.erase b↔a≠b/\a∈s:=Finset.mem_erase
private theorem Zx {α:Type*} [DecidableEq α] {a b:α} {s:Finset α}:a∈insert b s↔a=b\/a∈s:=Finset.mem_insert
private theorem Zy {α:Type*} {s t:Finset α}:s∈t.powerset↔s⊆t:=Finset.mem_powerset
private theorem Zz {α:Type*} {s t:Finset α} {n:ℕ}:s∈t.powersetCard n↔s⊆t/\s.card=n:=Finset.mem_powersetCard
private theorem Yb {α:Type*} [DecidableEq α] {s t:Finset α} (h:s⊆t):(t \ s).card+s.card=t.card:=Finset.card_sdiff_add_card_eq_card h
private theorem Yc {a b:ℕ} (k:ℕ) (h:a≤ b):a*k≤ b*k:=Nat.mul_le_mul_right k h
private theorem Yd (k:ℕ) {a b:ℕ} (h:a≤ b):k*a≤ k*b:=Nat.mul_le_mul_left k h
private theorem Ye {α:Type*} [DecidableEq α] {a:α} {s t:Finset α}:a∈s \ t↔a∈s/\a∉t:=Finset.mem_sdiff
private theorem Yf {α:Type*} [DecidableEq α] {s₁ s₂:Finset α}:s₁∩s₂⊆s₁:=Finset.inter_subset_left
private theorem Yg {α:Type*} [DecidableEq α] {s₁ s₂:Finset α}:s₁∩s₂⊆s₂:=Finset.inter_subset_right
private theorem Yh {α:Type*} [DecidableEq α] (s t:Finset α):(s∪t).card≤ s.card+t.card:=Finset.card_union_le s t
private theorem Yi {α:Type*} [LinearOrder α] {a b:α} (h:a≤ b):max a b=b:=max_eq_right h
private theorem Yj {α:Type*} [LinearOrder α] {a b:α} (h:b≤ a):min a b=b:=min_eq_right h
private theorem Yk {α:Type*} [LinearOrder α] {a b:α} (h:b≤ a):max a b=a:=max_eq_left h
private theorem Yl {α:Type*} [LinearOrder α] {a b:α} (h:a≤ b):min a b=a:=min_eq_left h
private theorem Ym {α:Type*} [LinearOrder α] (a b:α):a≤ max a b:=le_max_left a b
private theorem Yn {α:Type*} [LinearOrder α] (a b:α):b≤ max a b:=le_max_right a b
private theorem Yp {α:Type*} [LinearOrder α] (a b:α):min a b≤ a:=min_le_left a b
private theorem Yq {α:Type*} [LinearOrder α] (a b:α):min a b≤ b:=min_le_right a b
def IsAP (X:Zf ℕ):Prop :=∃ a d k:ℕ,0< k/\(1< k->0< d)/\∀ x,x∈X↔∃ i< k,x=a+i*d
lemma Qn (X:Zf ℕ) (l:ℕ∞) (hl:0< l)
  (h:(SetLike.coe X).IsAPOfLength l):IsAP X:=by
 obtain⟨a,d,-,hX⟩:=h
 rcases Nat.eq_zero_or_pos d with rfl|hd
 ·refine⟨a,0,1,by omega,by omega,fun x=>?_⟩
  have hx:x∈X↔x∈(SetLike.coe X:Set ℕ):=Iff.rfl;rw[hx,hX]
  constructor
  ·rintro⟨n,-,rfl⟩
   exact⟨0,by omega,by simp⟩
  ·rintro⟨i,hi,rfl⟩
   have h0:((0:ℕ):ℕ∞)< l:=by exact_mod_cast hl
   exact⟨0,h0,by simp⟩
 ·have hfin:l≠⊤:=by
   intro htop;subst htop
   have hinj:Function.Injective (fun n:ℕ=>a+n*d):=fun m n hmn =>
    Nat.eq_of_mul_eq_mul_right hd (Nat.add_left_cancel hmn)
   have hsub:Set.range (fun n:ℕ=>a+n*d)⊆(X:Set ℕ):=by
    rintro _ ⟨n,rfl⟩
    rw[hX]
    exact⟨n,WithTop.coe_lt_top n,by simp[smul_eq_mul]⟩
   exact Set.infinite_range_of_injective hinj (X.finite_toSet.subset hsub)
  obtain⟨k,rfl⟩:∃ k:ℕ,l=(k:ℕ∞):=⟨l.toNat,(ENat.natCast_toNat hfin).symm⟩
  have hk:0< k:=by exact_mod_cast hl
  refine⟨a,d,k,hk,fun _=>hd,fun x=>?_⟩
  have hx:x∈X↔x∈(SetLike.coe X:Set ℕ):=Iff.rfl;rw[hx,hX]
  constructor
  ·rintro⟨n,hn,rfl⟩
   exact⟨n,by exact_mod_cast hn,by simp[smul_eq_mul]⟩
  ·rintro⟨i,hi,rfl⟩
   exact⟨i,by exact_mod_cast hi,by simp[smul_eq_mul]⟩
lemma Qo {X:Zf ℕ} {a d k:ℕ} (hk:0< k) (hd:1< k->0< d)
  (hX:∀ x,x∈X↔∃ i< k,x=a+i*d):X.card=k:=by
 have heq:X=(range k).image (fun i=>a+i*d):=by
  ext x;simp only[Zi,mem_range,hX]
  exact⟨fun ⟨i,hi,hx⟩=>⟨i,hi,hx.symm⟩,fun ⟨i,hi,hx⟩=>⟨i,hi,hx.symm⟩⟩
 rw[heq]
 rcases Nat.eq_or_lt_of_le hk with rfl|hk1
 ·simp
 ·have hd':0< d:=hd hk1
  rw[card_image_of_injective _ (fun i j hij =>
   Nat.eq_of_mul_eq_mul_right hd' (by omega)),card_range]
lemma W4 {X:Zf ℕ} (hne:X.Nonempty) (h2:X.card≤2):IsAP X:=by
 have h1:1≤ X.card:=card_pos.mpr hne
 rcases Nat.eq_or_lt_of_le h1 with hcard1|hcard2
 ·obtain⟨a,rfl⟩:=card_eq_one.mp hcard1.symm
  refine⟨a,0,1,by omega,by omega,fun x=>?_⟩
  simp
 ·have hc2:X.card=2:=by omega
  obtain⟨a,b,hab,rfl⟩:=card_eq_two.mp hc2
  rcases lt_or_gt_of_ne hab with hlt|hgt
  ·refine⟨a,b-a,2,by omega,fun _=>by omega,fun x=>?_⟩
   simp only[Zx,Zj]
   constructor
   ·rintro (rfl|rfl)
    ·exact⟨0,by omega,by simp⟩
    ·exact⟨1,by omega,by omega⟩
   ·rintro⟨i,hi,rfl⟩
    interval_cases i
    ·simp
    ·simp;omega
  ·refine⟨b,a-b,2,by omega,fun _=>by omega,fun x=>?_⟩
   simp only[Zx,Zj]
   constructor
   ·rintro (rfl|rfl)
    ·exact⟨1,by omega,by omega⟩
    ·exact⟨0,by omega,by simp⟩
   ·rintro⟨i,hi,rfl⟩
    interval_cases i
    ·simp
    ·simp;omega
lemma Wk {X:Zf ℕ} (hne:X.Nonempty) (hnot:¬ IsAP X) :3≤ X.card:=by
 by_contra h
 exact hnot (W4 hne (by omega))
lemma Wa {X:Zf ℕ} {a d k:ℕ} (hk:0< k) (_hd:1< k->0< d)
  (hX:∀ x,x∈X↔∃ i< k,x=a+i*d) :
  a∈X/\a+(k-1)*d∈X/\∀ x∈X,a≤ x/\x≤ a+(k-1)*d:=by
 refine⟨(hX a).mpr ⟨0,hk,by simp⟩,(hX _).mpr ⟨k-1,by omega,rfl⟩,?_⟩
 intro x hx;obtain⟨i,hi,rfl⟩:=(hX x).mp hx
 exact⟨Nat.le_add_right _ _,Nat.add_le_add_left (Yc d (by omega)) a⟩
def Qf (S:Zf ℕ) (z d:ℕ):Zf ℕ :=S.filter (fun x=>x % d=z % d ∧
  ∀ y∈Icc (min z x) (max z x),y % d=z % d->y∈S)
lemma Qu (S:Zf ℕ) (z d x:ℕ) :x∈Qf S z d↔x∈S/\x % d=z % d ∧
   ∀ y,min z x≤ y->y≤ max z x->y % d=z % d->y∈S:=by
 unfold Qf;rw[Za]
 constructor
 ·rintro⟨h1,h2,h3⟩
  exact⟨h1,h2,fun y hy1 hy2 hy3=>h3 y (Zb.mpr ⟨hy1,hy2⟩) hy3⟩
 ·rintro⟨h1,h2,h3⟩
  exact⟨h1,h2,fun y hy hy3=>h3 y (Zb.mp hy).1 (Zb.mp hy).2 hy3⟩
lemma Qz (S:Zf ℕ) (z d:ℕ):Qf S z d⊆S :=Zl _ _
lemma Q4 {S:Zf ℕ} {z:ℕ} (hz:z∈S) (d:ℕ):z∈Qf S z d:=by
 rw[Qu]
 refine⟨hz,rfl,fun y hy1 hy2 _=>?_⟩
 have hyz:y=z:=by omega
 rwa[hyz]
lemma Wh {S:Zf ℕ} {z d:ℕ} (hd:0< d) (hz:z∈S) :IsAP (Qf S z d):=by
 have hne:(Qf S z d).Nonempty:=⟨z,Q4 hz d⟩;set a:=(Qf S z d).min' hne;set b:=(Qf S z d).max' hne;have ha:a∈Qf S z d:=min'_mem _ hne;have hb:b∈Qf S z d:=max'_mem _ hne;have hab:a≤ b:=min'_le _ b hb;have hamod:a % d=z % d:=((Qu S z d a).mp ha).2.1;have hbmod:b % d=z % d:=((Qu S z d b).mp hb).2.1;have hdvd:d ∣ b-a:=(Nat.modEq_iff_dvd' hab).mp (hamod.trans hbmod.symm);obtain⟨m,hm⟩:=hdvd
 have hba:b=a+m*d:=by rw[Nat.mul_comm];omega
 refine⟨a,d,m+1,by omega,fun _=>hd,fun x=>?_⟩
 constructor
 ·intro hx
  have hx1:a≤ x:=min'_le _ x hx;have hx2:x≤ b:=le_max' _ x hx;have hxmod:x % d=a % d:=(((Qu S z d x).mp hx).2.1).trans hamod.symm;obtain⟨i,hi⟩:=(Nat.modEq_iff_dvd' hx1).mp hxmod.symm
  have hxi:x=a+i*d:=by rw[Nat.mul_comm];omega
  have hi_le:i≤ m:=Nat.le_of_mul_le_mul_right (by omega:i*d≤ m*d) hd
  exact⟨i,by omega,hxi⟩
 ·rintro⟨i,hi,rfl⟩
  have hle:a+i*d≤ b:=by rw[hba];exact Nat.add_le_add_left (Yc d (by omega)) a
  have hmod:(a+i*d) % d=z % d:=by rw[Nat.add_mul_mod_self_right,hamod]
  have haS:=(Qu S z d a).mp ha;have hbS:=(Qu S z d b).mp hb;have hza:a≤ z:=min'_le _ z (Q4 hz d);have hzb:z≤ b:=le_max' _ z (Q4 hz d)
  have hmemS:∀ y,a≤ y->y≤ b->y % d=z % d->y∈S:=by
   intro y hy1 hy2 hym
   rcases le_total y z with hyz|hzy
   ·exact haS.2.2 y (by omega) (by omega) hym
   ·exact hbS.2.2 y (by omega) (by omega) hym
  rw[Qu]
  refine⟨hmemS (a+i*d) (Nat.le_add_right _ _) hle hmod,hmod,fun y hy1 hy2 hym=>?_⟩
  exact hmemS y (by omega) (by omega) hym
lemma Qv {S A:Zf ℕ} {a d k z:ℕ} (hAS:A⊆S) (hd:0< d)
  (hA:∀ x,x∈A↔∃ i< k,x=a+i*d) (hz:z∈A):A⊆Qf S z d:=by
 intro x hx;obtain⟨iz,hiz,hzeq⟩:=(hA z).mp hz;obtain⟨ix,hix,hxeq⟩:=(hA x).mp hx;rw[Qu]
 refine⟨hAS hx,?_,?_⟩
 ·rw[hxeq,hzeq,Nat.add_mul_mod_self_right,Nat.add_mul_mod_self_right]
 ·intro y hy1 hy2 hymod
  have hay:a≤ y:=by omega
  have hmoda:a % d=y % d:=by rw[hymod,hzeq,Nat.add_mul_mod_self_right]
  obtain⟨iy,hiy⟩:=(Nat.modEq_iff_dvd' hay).mp hmoda
  have hyeq:y=a+iy*d:=by rw[Nat.mul_comm];omega
  have hiy_lt:iy< k:=by
   have hmax:iy*d≤ max iz ix*d:=by
    rcases le_total iz ix with hle|hle
    ·have:z≤ x:=by rw[hzeq,hxeq];exact Nat.add_le_add_left (Yc d hle) a
     have:max iz ix=ix:=Yi hle
     rw[this];omega
    ·have:x≤ z:=by rw[hzeq,hxeq];exact Nat.add_le_add_left (Yc d hle) a
     have:max iz ix=iz:=Yk hle
     rw[this];omega
   have hle':iy≤ max iz ix:=Nat.le_of_mul_le_mul_right hmax hd;exact lt_of_le_of_lt hle' (max_lt hiz hix)
  exact hAS ((hA y).mpr ⟨iy,hiy_lt,hyeq⟩)
lemma Kp {S A:Zf ℕ} {a d k z u:ℕ} (hAS:A⊆S)
  (hA:∀ x,x∈A↔∃ i< k,x=a+i*d) (hz:z∈A) (hu:u∈A) (hzu:z≠u)
  (hadj:∀ w∈S,¬ (min z u< w/\w< max z u)) :
  0< d/\max z u-min z u=d:=by
 obtain⟨iz,hiz,hzeq⟩:=(hA z).mp hz;obtain⟨iu,hiu,hueq⟩:=(hA u).mp hu
 have hd:0< d:=by
  rcases Nat.eq_zero_or_pos d with rfl|hpos
  ·exfalso;apply hzu;simp[hzeq,hueq]
  ·exact hpos
 refine⟨hd,?_⟩
 rcases lt_trichotomy iz iu with hlt|heq|hgt
 ·obtain⟨t,ht⟩:=Nat.exists_eq_add_of_lt hlt
  have hu':u=z+t*d+d:=by rw[hzeq,hueq,ht];ring
  rcases Nat.eq_zero_or_pos t with rfl|htpos
  ·omega
  ·exfalso
   have hw:a+(iz+1)*d∈A:=(hA _).mpr ⟨iz+1,by omega,rfl⟩
   have htd:d≤ t*d:=Nat.le_mul_of_pos_left d htpos
   have hweq:a+(iz+1)*d=z+d:=by rw[hzeq];ring
   exact hadj (a+(iz+1)*d) (hAS hw) ⟨by omega,by omega⟩
 ·exfalso;exact hzu (by rw[hzeq,hueq,heq])
 ·obtain⟨t,ht⟩:=Nat.exists_eq_add_of_lt hgt
  have hz':z=u+t*d+d:=by rw[hzeq,hueq,ht];ring
  rcases Nat.eq_zero_or_pos t with rfl|htpos
  ·omega
  ·exfalso
   have hw:a+(iu+1)*d∈A:=(hA _).mpr ⟨iu+1,by omega,rfl⟩
   have htd:d≤ t*d:=Nat.le_mul_of_pos_left d htpos
   have hweq:a+(iu+1)*d=u+d:=by rw[hueq];ring
   exact hadj (a+(iu+1)*d) (hAS hw) ⟨by omega,by omega⟩
def Qk (S:Zf ℕ) (t:Zf ℕ):Prop :=t.card=3/\t⊆S/\∀ A:Zf ℕ,IsAP A->A⊆S->¬ (t⊆A)
lemma Wp {S:Zf ℕ} {z u v:ℕ} (hz:z∈S) (hu:u∈S) (hv:v∈S)
  (hzu:z≠u) (hadj:∀ w∈S,¬ (min z u< w/\w< max z u))
  (hvR:v∉Qf S z (max z u-min z u)) :
  Qk S {z,u,v}:=by
 have hzv:z≠v:=by intro h;subst h;exact hvR (Q4 hz _)
 have huv:u≠v:=by
  intro h;subst h
  set g:=max z u-min z u with hg_def
  have hgpos:0< g:=by omega
  have hmod_mm:min z u % g=max z u % g:=by have h1:g ∣ max z u-min z u:=dvd_refl g;exact (Nat.modEq_iff_dvd' (min_le_max:min z u≤ max z u)).mpr h1
  have humod:u % g=z % g:=by
   rcases le_total z u with hle|hge
   ·rw[Yl hle,Yi hle] at hmod_mm;exact hmod_mm.symm
   ·rw[Yj hge,Yk hge] at hmod_mm;exact hmod_mm
  apply hvR;rw[Qu]
  refine⟨hu,humod,fun y hy1 hy2 hym=>?_⟩
  rcases eq_or_lt_of_le hy1 with rfl|hlt1
  ·rcases le_total z u with hle|hge
   ·rw[Yl hle];exact hz
   ·rw[Yj hge];exact hu
  ·rcases eq_or_lt_of_le hy2 with rfl|hlt2
   ·rcases le_total z u with hle|hge
    ·rw[Yi hle];exact hu
    ·rw[Yk hge];exact hz
   ·exfalso
    have hmy:min z u % g=y % g:=by
     rcases le_total z u with hle|hge
     ·rw[Yl hle,hym]
     ·rw[Yj hge,humod,hym]
    have hdvd:g ∣ y-min z u:=(Nat.modEq_iff_dvd' (le_of_lt hlt1)).mp hmy
    have hle':=Nat.le_of_dvd (by omega:0< y-min z u) hdvd
    omega
 have hcard:({z,u,v}:Zf ℕ).card=3:=by
  rw[card_insert_of_notMem,card_insert_of_notMem,card_singleton]
  ·simp[huv]
  ·simp[hzu,hzv]
 refine⟨hcard,?_,?_⟩
 ·intro x hx
  simp only[Zx,Zj] at hx
  rcases hx with rfl|rfl|rfl <;> assumption
 ·intro A ⟨a,d,k,hk,hdk,hA⟩ hAS hsub
  have hzA:z∈A:=hsub (by simp)
  have huA:u∈A:=hsub (by simp)
  have hvA:v∈A:=hsub (by simp)
  obtain⟨hd,hgap⟩:=Kp hAS hA hzA huA hzu hadj;rw[hgap] at hvR;exact hvR (Qv hAS hd hA hzA hvA)
lemma We {N:ℕ} {F:Zf (Zf ℕ)} (hF:Zt N F)
  {S T t:Zf ℕ} (hS:S∈F) (hT:T∈F) (hST:S≠T) (hbad:Qk S t) :
  ¬ (t⊆T):=by
 intro htT;obtain⟨l,hl,hl'⟩:=hF.2 (Zc.mpr hS) (Zc.mpr hT) hST;have hAP:=Qn (S∩T) l hl hl';exact hbad.2.2 (S∩T) hAP Yf (Finset.subset_inter hbad.2.1 htT)
lemma Kk (N:ℕ) (hN:1≤ N):N.choose 2+1≤ Erdos272.maxArithInterCard N:=by
 let U:=(Icc 2 N).powersetCard 2
 let star:Zf (Zf ℕ) :=insert ({1}:Zf ℕ) ((Icc 2 N).image (fun x=>({1,x}:Zf ℕ)) ∪
   U.image (fun p=>insert 1 p))
 have h1_mem:1∈Icc 1 N:=Zb.mpr ⟨le_rfl,hN⟩
 have hstar_adm:Zt N star:=by
  refine⟨?_,?_⟩
  ·intro S hS
   rw[Zy];simp only[star,Zx,Zd,Zi,U,Zz] at hS
   rcases hS with rfl|⟨x,hx,rfl⟩|⟨p,⟨hp,-⟩,rfl⟩
   ·exact singleton_subset_iff.mpr h1_mem
   ·intro y hy
    simp only[Zx,Zj] at hy
    rcases hy with rfl|rfl
    ·exact h1_mem
    ·exact Zb.mpr ⟨by have:=(Zb.mp hx).1;omega,(Zb.mp hx).2⟩
   ·intro y hy
    rcases Zx.mp hy with rfl|hyp
    ·exact h1_mem
    ·have hx:=Zb.mp (hp hyp)
     exact Zb.mpr ⟨by omega,hx.2⟩
  ·intro S hS T hT hST
   have hS':S∈star:=Zc.mp hS;have hT':T∈star:=Zc.mp hT
   have h1S:1∈S:=by
    simp only[star,Zx,Zd,Zi] at hS'
    rcases hS' with rfl|⟨x,_,rfl⟩|⟨p,_,rfl⟩ <;> simp
   have h1T:1∈T:=by
    simp only[star,Zx,Zd,Zi] at hT'
    rcases hT' with rfl|⟨x,_,rfl⟩|⟨p,_,rfl⟩ <;> simp
   have hScard:S.card≤3:=by
    simp only[star,Zx,Zd,Zi,U,Zz] at hS'
    rcases hS' with rfl|⟨x,_,rfl⟩|⟨p,⟨-,hpc⟩,rfl⟩
    ·simp
    ·exact (card_insert_le _ _).trans (by simp)
    ·exact (card_insert_le _ _).trans (by omega)
   have hTcard:T.card≤3:=by
    simp only[star,Zx,Zd,Zi,U,Zz] at hT'
    rcases hT' with rfl|⟨x,_,rfl⟩|⟨p,⟨-,hpc⟩,rfl⟩
    ·simp
    ·exact (card_insert_le _ _).trans (by simp)
    ·exact (card_insert_le _ _).trans (by omega)
   have hle2:(S∩T).card≤2:=by
    by_contra hgt
    have h3:3≤(S∩T).card:=by omega
    have hSsub:S∩T⊆S:=Yf;have hTsub:S∩T⊆T:=Yg
    have heq1:S∩T=S:=eq_of_subset_of_card_le hSsub (by omega)
    have heq2:S∩T=T:=eq_of_subset_of_card_le hTsub (by omega)
    exact hST (heq1.symm.trans heq2)
   have hne:(S∩T).Nonempty:=⟨1,Zn.mpr ⟨h1S,h1T⟩⟩;obtain⟨a,d,k,hk,hdk,hAP⟩:=W4 hne hle2
   refine⟨(k:ℕ∞),by exact_mod_cast hk,a,d,?_,?_⟩
   ·rw[ENat.card_coe_set_eq,Set.encard_coe_eq_coe_finsetCard,Qo hk hdk hAP]
   ·ext x
    simp only[Zc,Set.mem_ofPred_eq,smul_eq_mul];rw[hAP x]
    constructor
    ·rintro⟨i,hi,rfl⟩;exact⟨i,by exact_mod_cast hi,rfl⟩
    ·rintro⟨i,hi,rfl⟩;exact⟨i,by exact_mod_cast hi,rfl⟩
 have hstar_card:star.card=N.choose 2+1:=by
  let A1:=(Icc 2 N).image (fun x=>({1,x}:Zf ℕ))
  let A2:=U.image (fun p=>insert 1 p)
  have hdisj12:Disjoint A1 A2:=by
   rw[Zk];intro S hS1 hS2;obtain⟨x,hx,rfl⟩:=Zi.mp hS1;obtain⟨p,hp,hpeq⟩:=Zi.mp hS2;have hx2:=(Zb.mp hx).1
   have h1p:1∉p:=fun h=>by
    have:=(Zb.mp ((Zz.mp hp).1 h)).1;omega
   have hc1:({1,x}:Zf ℕ).card=2:=by
    rw[card_insert_of_notMem (by simp;omega),card_singleton]
   have hc2:(insert 1 p).card=3:=by rw[card_insert_of_notMem h1p,(Zz.mp hp).2]
   rw[←hpeq] at hc1;omega
  have h1not:({1}:Zf ℕ)∉A1∪A2:=by
   simp only[Zd,A1,A2,Zi,not_or]
   refine⟨?_,?_⟩
   ·rintro⟨x,hx,heq⟩
    have hx2:=(Zb.mp hx).1
    have:x∈({1}:Zf ℕ):=by rw[←heq];simp
    simp at this;omega
   ·rintro⟨p,hp,heq⟩
    have h1p:1∉p:=fun h=>by
     have:=(Zb.mp ((Zz.mp hp).1 h)).1;omega
    have hc2:(insert 1 p).card=3:=by rw[card_insert_of_notMem h1p,(Zz.mp hp).2]
    rw[heq] at hc2;simp at hc2
  have hcardA1:A1.card=N-1:=by
   rw[card_image_of_injOn]
   ·rw[Nat.card_Icc];omega
   ·intro x hx y hy hxy
    have hx2:=(Zb.mp (Zc.mp hx)).1;have hy2:=(Zb.mp (Zc.mp hy)).1;have hxy':({1,x}:Zf ℕ)={1,y}:=hxy
    have:x∈({1,y}:Zf ℕ):=by rw[←hxy'];simp
    simp at this;omega
  have hcardA2:A2.card=(N-1).choose 2:=by
   rw[card_image_of_injOn]
   ·rw[card_powersetCard,Nat.card_Icc]
    have:N+1-2=N-1:=by omega
    rw[this]
   ·intro p hp q hq hpq
    have h1p:1∉p:=fun h=>by
     have:=(Zb.mp ((Zz.mp (Zc.mp hp)).1 h)).1;omega
    have h1q:1∉q:=fun h=>by
     have:=(Zb.mp ((Zz.mp (Zc.mp hq)).1 h)).1;omega
    have:=congrArg (fun s=>erase s 1) hpq
    simpa [erase_insert h1p,erase_insert h1q] using this
  show (insert ({1}:Zf ℕ) (A1∪A2)).card=N.choose 2+1
  rw[card_insert_of_notMem h1not,Zq hdisj12,hcardA1,hcardA2]
  rcases Nat.eq_or_lt_of_le hN with rfl|hN2
  ·simp
  ·obtain⟨M,rfl⟩:∃ M,N=M+1:=⟨N-1,by omega⟩
   simp only[Nat.add_sub_cancel,Nat.choose_succ_succ,Nat.choose_one_right]
 have hbdd:BddAbove {(#A:ℕ)|(A:Zf (Zf ℕ)) (_:Zt N A)}:=by
  refine⟨((Icc 1 N).powerset).card,?_⟩
  rintro _ ⟨A,hA,rfl⟩
  exact Zm hA.1
 unfold Erdos272.maxArithInterCard;rw[←hstar_card];exact le_csSup hbdd ⟨star,hstar_adm,rfl⟩
lemma Q0 (N:ℕ) (hN:1≤ N) :∑ d∈Icc 1 N,(1:ℝ)/(d:ℝ)≤ log (N:ℝ)+1:=by
 induction N,hN using Nat.le_induction with
 | base=>simp
 | succ k hk ih =>
  rw[sum_Icc_succ_top (by omega)]
  have hkpos:(0:ℝ)<(k:ℝ):=by exact_mod_cast hk
  have hstep:(1:ℝ)/((k+1:ℕ):ℝ)≤ log ((k+1:ℕ):ℝ)-log (k:ℝ):=by
   have h1:1-(k:ℝ)/((k+1:ℕ):ℝ)=(1:ℝ)/((k+1:ℕ):ℝ):=by push_cast;field_simp;ring
   have h2:=Real.one_sub_inv_le_log_of_pos (div_pos (by positivity:(0:ℝ)<((k+1:ℕ):ℝ)) hkpos)
   rw[inv_div,h1,Real.log_div (by positivity) hkpos.ne'] at h2
   exact h2
  linarith
lemma Vc (a b:ℕ) (ha:1≤ a) :∑ d∈Icc (a+1) b,(1:ℝ)/(d:ℝ)^2≤1/(a:ℝ):=by
 rcases lt_or_ge b (a+1) with hlt|hge
 ·rw[Icc_eq_empty (by omega),Finset.sum_empty]
  positivity
 ·have hstep:∀ d∈Icc (a+1) b,(1:ℝ)/(d:ℝ)^2≤1/((d-1:ℕ):ℝ)-1/(d:ℝ):=by
   intro d hd;have hd1:=(Zb.mp hd).1
   have hdm:((d-1:ℕ):ℝ)=(d:ℝ)-1:=by rw[Nat.cast_sub (by omega)];simp
   rw[hdm]
   have hdpos:(0:ℝ)<(d:ℝ):=by exact_mod_cast (by omega:0< d)
   have hdmpos:(0:ℝ)<(d:ℝ)-1:=by
    have:(2:ℝ)≤(d:ℝ):=by exact_mod_cast (by omega:2≤ d)
    linarith
   rw[div_sub_div _ _ hdmpos.ne' hdpos.ne',one_mul,mul_one,sub_sub_cancel]
   exact div_le_div_of_nonneg_left zero_le_one (mul_pos hdmpos hdpos) (by nlinarith)
  calc ∑ d∈Icc (a+1) b,(1:ℝ)/(d:ℝ)^2
      ≤ ∑ d∈Icc (a+1) b,(1/((d-1:ℕ):ℝ)-1/(d:ℝ)) :=Finset.sum_le_sum hstep
    _=1/(a:ℝ)-1/(b:ℝ):=by
        clear hstep
        induction b,hge using Nat.le_induction with
        | base=>simp
        | succ k hk ih =>
          rw[sum_Icc_succ_top (by omega),ih]
          simp only[Nat.add_sub_cancel];ring
    _≤1/(a:ℝ):=sub_le_self _ (by positivity)
lemma Xq (a b:ℕ) (ha:1≤ a) :∑ t∈Icc a b,(1:ℝ)/(2*(t:ℝ)+1)^2≤1/(2*(2*(a:ℝ)-1)):=by
 rcases lt_or_ge b a with hlt|hge
 ·rw[Icc_eq_empty (by omega),Finset.sum_empty]
  have ha1:(1:ℝ)≤(a:ℝ):=by exact_mod_cast ha
  have hpos:(0:ℝ)<2*(2*(a:ℝ)-1):=by linarith
  positivity
 ·have hstep:∀ t∈Icc a b,(1:ℝ)/(2*(t:ℝ)+1)^2 ≤1/(2*(2*(t:ℝ)-1))-1/(2*(2*(t:ℝ)+1)):=by
   intro t ht
   have ht1:(1:ℝ)≤(t:ℝ):=by exact_mod_cast (le_trans ha (Zb.mp ht).1)
   have hp1:(0:ℝ)<2*(t:ℝ)-1:=by linarith
   have hp2:(0:ℝ)<2*(t:ℝ)+1:=by linarith
   have hrhs:1/(2*(2*(t:ℝ)-1))-1/(2*(2*(t:ℝ)+1)) =1/((2*(t:ℝ)-1)*(2*(t:ℝ)+1)):=by field_simp;ring
   rw[hrhs]
   exact div_le_div_of_nonneg_left zero_le_one (mul_pos hp1 hp2) (by nlinarith)
  calc ∑ t∈Icc a b,(1:ℝ)/(2*(t:ℝ)+1)^2
      ≤ ∑ t∈Icc a b,(1/(2*(2*(t:ℝ)-1))-1/(2*(2*(t:ℝ)+1))) :=Finset.sum_le_sum hstep
    _=1/(2*(2*(a:ℝ)-1))-1/(2*(2*(b:ℝ)+1)):=by
        clear hstep
        induction b,hge using Nat.le_induction with
        | base=>simp
        | succ k hk ih =>
          rw[sum_Icc_succ_top (by omega),ih]
          push_cast
          have:2*((k:ℝ)+1)-1=2*(k:ℝ)+1:=by ring
          rw[this];ring
    _≤1/(2*(2*(a:ℝ)-1)):=sub_le_self _ (by positivity)
lemma V0 (N:ℕ) :∑ d∈Icc 3 N,(1:ℝ)/(4*(d:ℝ)^2)≤1/10:=by
 have hdisj:Disjoint (Icc (3:ℕ) 10) (Icc (11:ℕ) N):=by
  rw[Zk];intro d h1 h2
  have:=(Zb.mp h1).2;have:=(Zb.mp h2).1;omega
 have hsub:Icc 3 N⊆Icc (3:ℕ) 10∪Icc (11:ℕ) N:=by intro d hd;simp only[Zb,Zd] at hd ⊢;omega
 have hfac:∀ s:Zf ℕ,∑ d∈s,(1:ℝ)/(4*(d:ℝ)^2) =(1/4:ℝ)*∑ d∈s,(1:ℝ)/(d:ℝ)^2:=by
  intro s;rw[Finset.mul_sum];refine Finset.sum_congr rfl fun d _=>?_;ring
 rw[hfac]
 have hfin:∑ d∈Icc (3:ℕ) 10,(1:ℝ)/(d:ℝ)^2 =1/9+1/16+1/25+1/36+1/49+1/64+1/81+1/100:=by simp[sum_Icc_succ_top];norm_num
 have htail:=Vc 10 N (by omega)
 have h1:∑ d∈Icc 3 N,(1:ℝ)/(d:ℝ)^2 ≤(∑ d∈Icc (3:ℕ) 10,(1:ℝ)/(d:ℝ)^2) +∑ d∈Icc (11:ℕ) N,(1:ℝ)/(d:ℝ)^2:=by
  rw[←Finset.sum_union hdisj]
  exact sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>by positivity)
 rw[hfin] at h1;norm_num at h1 htail ⊢;linarith
lemma Vo (a b:ℕ) (ha:1≤ a) :∑ d∈Icc (a+1) b,(1:ℝ)/(d:ℝ)^2≤1/((a:ℝ)+1/2):=by
 have hstep:∀ d∈Icc (a+1) b,(1:ℝ)/(d:ℝ)^2≤1/((d:ℝ)-1/2)-1/((d:ℝ)+1/2):=by
  intro d hd
  have hd1:(2:ℝ)≤(d:ℝ):=by exact_mod_cast (by have:=(Zb.mp hd).1;omega:2≤ d)
  have hp1:(0:ℝ)<(d:ℝ)-1/2:=by linarith
  have hp2:(0:ℝ)<(d:ℝ)+1/2:=by linarith
  have hp3:(0:ℝ)<(d:ℝ)^2:=by positivity
  rw[div_sub_div _ _ hp1.ne' hp2.ne',div_le_div_iff₀ hp3 (mul_pos hp1 hp2)];nlinarith
 have htel:∀ n:ℕ,∑ k∈range n,(1/((a+1+k:ℝ)-1/2)-1/((a+1+k:ℝ)+1/2)) =1/((a:ℝ)+1/2)-1/((a+n:ℝ)+1/2):=by
  intro n
  induction n with
  | zero=>simp
  | succ k ih =>
   rw[sum_range_succ,ih];push_cast;ring
 rcases lt_or_ge b (a+1) with hlt|hle
 ·have hemp:Icc (a+1) b=∅:=Icc_eq_empty (by omega)
  rw[hemp,Finset.sum_empty];positivity
 ·have hsum_le:=Finset.sum_le_sum hstep
  have hshift:∑ d∈Icc (a+1) b,(1/((d:ℝ)-1/2)-1/((d:ℝ)+1/2)) =∑ k∈range (b-a),(1/((a+1+k:ℝ)-1/2)-1/((a+1+k:ℝ)+1/2)):=by
   refine sum_nbij (fun d=>d-(a+1)) ?_ ?_ ?_ ?_
   ·intro d hd;simp only[Zb,mem_range] at hd ⊢;omega
   ·intro d₁ h₁ d₂ h₂ heq;simp only[Zc,Zb] at h₁ h₂;dsimp only at heq;omega
   ·intro k hk;simp only[Zc,mem_range] at hk
    exact⟨a+1+k,Zb.mpr ⟨by omega,by omega⟩,by dsimp only;omega⟩
   ·intro d hd
    have hd1:=(Zb.mp hd).1
    have heq:(a+1+(d-(a+1)):ℕ)=d:=by omega
    have heqR:(a:ℝ)+1+((d-(a+1):ℕ):ℝ)=(d:ℝ):=by exact_mod_cast heq
    rw[heqR]
  rw[hshift,htel] at hsum_le
  have hpos:(0:ℝ)≤1/((a:ℝ)+((b-a:ℕ):ℝ)+1/2):=by positivity
  linarith
lemma W3 (N:ℕ) :∑ d∈Icc 1 N,(1:ℝ)/(d:ℝ)^2≤1645/1000:=by
 have hdisj:Disjoint (Icc (1:ℕ) 11) (Icc (12:ℕ) N):=by
  rw[Zk];intro d h1 h2
  have:=(Zb.mp h1).2;have:=(Zb.mp h2).1;omega
 have hsub:Icc 1 N⊆Icc (1:ℕ) 11∪Icc (12:ℕ) N:=by intro d hd;simp only[Zb,Zd] at hd ⊢;omega
 have hfin:∑ d∈Icc (1:ℕ) 11,(1:ℝ)/(d:ℝ)^2 =1/1+1/4+1/9+1/16+1/25+1/36+1/49+1/64+1/81+1/100+1/121:=by simp[sum_Icc_succ_top];norm_num
 have htail:=Vo 11 N (by omega)
 calc ∑ d∈Icc 1 N,(1:ℝ)/(d:ℝ)^2
     ≤ ∑ d∈Icc (1:ℕ) 11∪Icc (12:ℕ) N,(1:ℝ)/(d:ℝ)^2 :=sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>by positivity)
   _=(∑ d∈Icc (1:ℕ) 11,(1:ℝ)/(d:ℝ)^2) +
         ∑ d∈Icc (12:ℕ) N,(1:ℝ)/(d:ℝ)^2 :=
       Finset.sum_union hdisj
   _≤1645/1000:=by rw[hfin];norm_num at htail ⊢;linarith
lemma Xa (N:ℕ) :∑ d∈(Icc 1 N).filter Odd,(1:ℝ)/(d:ℝ)^2≤1235/1000:=by
 have hsub:(Icc 1 N).filter Odd ⊆
   (Icc (0:ℕ) N).image (fun t:ℕ=>2*t+1):=by
  intro d hd;obtain⟨hdI,⟨t,rfl⟩⟩:=Za.mp hd
  refine Zi.mpr ⟨t,Zb.mpr ⟨Nat.zero_le _,?_⟩,rfl⟩
  have:=(Zb.mp hdI).2;omega
 have hdisj:Disjoint (Icc (0:ℕ) 11) (Icc (12:ℕ) N):=by
  rw[Zk];intro t h1 h2
  have:=(Zb.mp h1).2;have:=(Zb.mp h2).1;omega
 have hsub2:Icc (0:ℕ) N⊆Icc (0:ℕ) 11∪Icc (12:ℕ) N:=by intro t ht;simp only[Zb,Zd] at ht ⊢;omega
 have hfin:∑ t∈Icc (0:ℕ) 11,(1:ℝ)/(2*(t:ℝ)+1)^2 =1/1+1/9+1/25+1/49+1/81+1/121+1/169+1/225+1/289+1/361 +1/441+1/529:=by simp[sum_Icc_succ_top];norm_num
 have htail:=Xq 12 N (by omega)
 calc ∑ d∈(Icc 1 N).filter Odd,(1:ℝ)/(d:ℝ)^2
     ≤ ∑ d∈(Icc (0:ℕ) N).image (fun t:ℕ=>2*t+1),(1:ℝ)/(d:ℝ)^2 :=sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>by positivity)
   _=∑ t∈Icc (0:ℕ) N,(1:ℝ)/(2*(t:ℝ)+1)^2:=by
       rw[sum_image (fun a _ b _ hab=>by omega)]
       refine Finset.sum_congr rfl fun t _=>?_;push_cast;ring
   _≤∑ t∈Icc (0:ℕ) 11∪Icc (12:ℕ) N,(1:ℝ)/(2*(t:ℝ)+1)^2 :=
       sum_le_sum_of_subset_of_nonneg hsub2 (fun _ _ _=>by positivity)
   _=(∑ t∈Icc (0:ℕ) 11,(1:ℝ)/(2*(t:ℝ)+1)^2) +
         ∑ t∈Icc (12:ℕ) N,(1:ℝ)/(2*(t:ℝ)+1)^2 :=
       Finset.sum_union hdisj
   _≤1235/1000:=by rw[hfin];norm_num at htail ⊢;linarith
lemma Xw (e:ℕ):(e+1)^5≤512*2^e:=by
 induction e with
 | zero=>norm_num
 | succ k ih =>
  rcases lt_or_ge k 10 with hk|hk
  ·interval_cases k <;> norm_num
  ·have h2:(k+2)^5≤2*(k+1)^5:=by
    have hz:((k+2:ℤ)^5)≤2*(k+1:ℤ)^5:=by
     have hk':(10:ℤ)≤(k:ℤ):=by exact_mod_cast hk
     have hfact:2*(k+1:ℤ)^5-(k+2:ℤ)^5 =(k-10:ℤ)*(k^4+10*k^3+80*k^2+740*k+7330)+73270:=by ring
     have hpos:(0:ℤ)≤(k:ℤ)^4+10*(k:ℤ)^3+80*(k:ℤ)^2+740*(k:ℤ)+7330:=by positivity
     nlinarith
    exact_mod_cast hz
   calc (k+1+1)^5=(k+2)^5:=rfl
     _≤2*(k+1)^5:=h2
     _≤2*(512*2^k):=Yd 2 ih
     _=512*2^(k+1):=by ring
lemma Ka (e:ℕ):e+1≤2^e:=by
 induction e with
 | zero=>norm_num
 | succ k ih =>
  have:1≤2^k:=Nat.one_le_two_pow
  rw[pow_succ];omega
lemma X4 (L:ℕ) (hL:1≤ L) :L.divisors.card^5≤512^11*L:=by
 have hL0:L≠0:=by omega
 have hcard:L.divisors.card=∏ p∈L.primeFactors,(L.factorization p+1):=by rw[Nat.card_divisors hL0]
 rw[hcard,←Finset.prod_pow]
 have hsmall_card:(L.primeFactors.filter (fun p=>p<32)).card≤11:=by
  have hsub:L.primeFactors.filter (fun p=>p<32) ⊆
    ({2,3,5,7,11,13,17,19,23,29,31}:Zf ℕ):=by
   intro p hp;obtain⟨hpf,hlt⟩:=Za.mp hp;have hpr:=Nat.prime_of_mem_primeFactors hpf
   interval_cases p <;> first|exact absurd hpr (by decide)|simp
  exact (Zm hsub).trans (by decide)
 have hLprod:L=∏ p∈L.primeFactors,p^L.factorization p :=Nat.prod_primeFactors_pow_factorization hL0
 have hsplit:∏ p∈L.primeFactors,(L.factorization p+1)^5 =(∏ p∈L.primeFactors.filter (fun p=>p<32),(L.factorization p+1)^5) *(∏ p∈L.primeFactors.filter (fun p=>¬ (p<32)),(L.factorization p+1)^5) :=(prod_filter_mul_prod_filter_not L.primeFactors (fun p=>p<32) _).symm
 have hsplitL:L =(∏ p∈L.primeFactors.filter (fun p=>p<32),p^L.factorization p) *(∏ p∈L.primeFactors.filter (fun p=>¬ (p<32)),p^L.factorization p):=by
  conv_lhs=>rw[hLprod]
  exact (prod_filter_mul_prod_filter_not L.primeFactors (fun p=>p<32) _).symm
 have h1:∏ p∈L.primeFactors.filter (fun p=>p<32),(L.factorization p+1)^5 ≤512^11*∏ p∈L.primeFactors.filter (fun p=>p<32),p^L.factorization p:=by
  calc ∏ p∈L.primeFactors.filter (fun p=>p<32),(L.factorization p+1)^5
      ≤ ∏ p∈L.primeFactors.filter (fun p=>p<32),(512*p^L.factorization p):=by
        refine prod_le_prod' fun p hp=>?_
        have hpr:=Nat.prime_of_mem_primeFactors (Za.mp hp).1
        exact (Xw _).trans
          (Yd 512 (Nat.pow_le_pow_left hpr.two_le _))
    _=512^(L.primeFactors.filter (fun p=>p<32)).card *
          ∏ p∈L.primeFactors.filter (fun p=>p<32),p^L.factorization p:=by
        rw[Finset.prod_mul_distrib,Finset.prod_const]
    _≤512^11*∏ p∈L.primeFactors.filter (fun p=>p<32),p^L.factorization p :=
        Yc _ (Nat.pow_le_pow_right (by omega) hsmall_card)
 have h2:∏ p∈L.primeFactors.filter (fun p=>¬ (p<32)),(L.factorization p+1)^5 ≤∏ p∈L.primeFactors.filter (fun p=>¬ (p<32)),p^L.factorization p:=by
  refine prod_le_prod' fun p hp=>?_
  have hp32:32≤ p:=by have:=(Za.mp hp).2;omega
  calc (L.factorization p+1)^5
      ≤ (2^L.factorization p)^5:=Nat.pow_le_pow_left (Ka _) 5
    _=(2^5)^L.factorization p:=by rw[←pow_mul,mul_comm,pow_mul]
    _=32^L.factorization p:=by norm_num
    _≤ p^L.factorization p:=Nat.pow_le_pow_left hp32 _
 calc ∏ p∈L.primeFactors,(L.factorization p+1)^5
     = (∏ p∈L.primeFactors.filter (fun p=>p<32),(L.factorization p+1)^5) *(∏ p∈L.primeFactors.filter (fun p=>¬ (p<32)),(L.factorization p+1)^5):=hsplit
   _≤(512^11*∏ p∈L.primeFactors.filter (fun p=>p<32),p^L.factorization p) *
         ∏ p∈L.primeFactors.filter (fun p=>¬ (p<32)),p^L.factorization p :=
       Nat.mul_le_mul h1 h2
   _=512^11*((∏ p∈L.primeFactors.filter (fun p=>p<32),p^L.factorization p) *
         ∏ p∈L.primeFactors.filter (fun p=>¬ (p<32)),p^L.factorization p):=by ring
   _=512^11*L:=by rw[←hsplitL]
lemma Xj (L:ℕ) (hL:1≤ L) :(L.divisors.card:ℝ)≤(512^3:ℝ)*(L:ℝ)^((1:ℝ)/5):=by
 have h5:((L.divisors.card:ℝ))^(5:ℕ)≤((512^11:ℕ):ℝ)*(L:ℝ):=by exact_mod_cast X4 L hL
 have h5':((L.divisors.card:ℝ))^(5:ℕ)≤((512^3:ℝ)*(L:ℝ)^((1:ℝ)/5))^(5:ℕ):=by
  rw[mul_pow,←Real.rpow_natCast ((L:ℝ)^((1:ℝ)/5)) 5,←Real.rpow_mul (Nat.cast_nonneg L)];norm_num
  have h11:((512^11:ℕ):ℝ)≤(512:ℝ)^15:=by norm_num
  nlinarith[Nat.cast_nonneg (α:=ℝ) L]
 exact le_of_pow_le_pow_left₀ (by omega) (by positivity) h5'
lemma X1 (L:ℕ) (hL:1≤ L) :L.primeFactors.card≤ Nat.log 2 L:=by
 have hpow:2^L.primeFactors.card≤ L:=by
  calc 2^L.primeFactors.card=∏ _p∈L.primeFactors,2:=by rw[Finset.prod_const]
    _≤∏ p∈L.primeFactors,p :=
      prod_le_prod' fun p hp=>(Nat.prime_of_mem_primeFactors hp).two_le
    _≤ L:=Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd L)
 exact Nat.le_log_of_pow_le (by omega) hpow
lemma Vr (k:ℕ) (hk:16≤ k):k^4≤2^k:=by
 induction k,hk using Nat.le_induction with
 | base=>norm_num
 | succ m hm ih =>
  have hstep:(m+1)^4≤2*m^4:=by nlinarith[sq_nonneg m,mul_self_nonneg (m^2)]
  rw[pow_succ' 2 m];exact hstep.trans (Yd 2 ih)
lemma Vq (M:ℕ) (hM:1000000≤ M) :M≤3*((Ioc M (2*M)).filter Nat.Prime).card*(Nat.log 2 (2*M)+1):=by
 have hM2:2< M:=by omega
 have hMpos:0< M:=by omega
 have h2Mpos:1≤2*M:=by omega
 let P:=(Ioc M (2*M)).filter Nat.Prime
 have hcb_le:M.centralBinom ≤(2*M)^Nat.sqrt (2*M)*4^(2*M/3)*(2*M)^P.card:=by
  let f:ℕ->ℕ:=fun p=>p^M.centralBinom.factorization p
  have hprod:=M.prod_pow_factorization_centralBinom
  let R:=range (2*M+1)
  let S1:=(range (2*M/3+1)).filter Nat.Prime
  have hzero:∀ p∈R,p∉S1->p∉P->f p=1:=by
   intro p hp hnot1 hnotP;have hp_le:p≤2*M:=Nat.lt_succ_iff.mp (mem_range.mp hp)
   by_cases hpr:p.Prime
   ·rcases le_or_gt p (2*M/3) with hle1|hgt1
    ·exact absurd (Za.mpr ⟨mem_range.mpr (by omega),hpr⟩) hnot1
    ·rcases le_or_gt p M with hle2|hgt2
     ·dsimp only[f]
      have h3:2*M<3*p:=by omega
      rw[Nat.factorization_centralBinom_of_two_mul_self_lt_three_mul hM2 hle2 h3,pow_zero]
     ·exact absurd (Za.mpr ⟨mem_Ioc.mpr ⟨hgt2,hp_le⟩,hpr⟩) hnotP
   ·dsimp only[f]
    rw[Nat.factorization_eq_zero_of_not_prime M.centralBinom hpr,pow_zero]
  have hdisj:Disjoint S1 P:=by rw[Zk];intro p hp1 hpP;have h1:=mem_range.mp (Za.mp hp1).1;have h2:=(mem_Ioc.mp (Za.mp hpP).1).1;omega
  have hsub:S1∪P⊆R:=by
   intro p hp
   rcases Zd.mp hp with hp1|hpP
   ·have:=mem_range.mp (Za.mp hp1).1
    exact mem_range.mpr (by omega)
   ·have:=(mem_Ioc.mp (Za.mp hpP).1).2
    exact mem_range.mpr (by omega)
  have hcb_eq:M.centralBinom=(∏ p∈S1,f p)*(∏ p∈P,f p):=by
   rw[←hprod,←Finset.prod_union hdisj]
   exact (prod_subset hsub (fun p hp hnot=>by
    rw[Zd,not_or] at hnot;exact hzero p hp hnot.1 hnot.2)).symm
  rw[hcb_eq]
  refine Nat.mul_le_mul ?_ ?_
  ·
   rw[←prod_filter_mul_prod_filter_not S1 (·≤ Nat.sqrt (2*M))]
   refine Nat.mul_le_mul ?_ ?_
   ·refine (prod_le_prod' fun p _ =>
      Nat.pow_factorization_choose_le (mul_pos two_pos hMpos)).trans ?_
    rw[Finset.prod_const]
    refine Nat.pow_le_pow_right h2Mpos ?_
    have hsub':S1.filter (·≤ Nat.sqrt (2*M))⊆Icc 1 (Nat.sqrt (2*M)):=by intro p hp;obtain⟨hp1,hple⟩:=Za.mp hp;exact Zb.mpr ⟨(Za.mp hp1).2.one_lt.le,hple⟩
    exact (Zm hsub').trans (by rw[Nat.card_Icc];omega)
   ·refine le_trans ?_ (primorial_le_four_pow (2*M/3))
    refine (prod_le_prod' fun p hp=>(?_:f p≤ p)).trans ?_
    ·obtain⟨h1,h2⟩:=Za.mp hp
     refine (Nat.pow_le_pow_right (Za.mp h1).2.one_lt.le ?_).trans (pow_one p).le
     exact Nat.factorization_choose_le_one (Nat.sqrt_lt'.mp (not_le.mp h2))
    ·refine prod_le_prod_of_subset_of_one_le' (Zl _ _)
      (fun p hp _=>(Za.mp hp).2.one_lt.le)
  ·
   refine (prod_le_prod' fun p _ =>
     Nat.pow_factorization_choose_le (mul_pos two_pos hMpos)).trans ?_
   rw[Finset.prod_const]
 have h4M:4^M< M*M.centralBinom:=Nat.four_pow_lt_mul_centralBinom M (by omega)
 have hcomb:4^M< M*(2*M)^Nat.sqrt (2*M)*4^(2*M/3)*(2*M)^P.card:=by
  calc 4^M< M*M.centralBinom:=h4M
    _≤ M*((2*M)^Nat.sqrt (2*M)*4^(2*M/3)*(2*M)^P.card) :=
      Yd M hcb_le
    _=M*(2*M)^Nat.sqrt (2*M)*4^(2*M/3)*(2*M)^P.card:=by ring
 set L:=Nat.log 2 (2*M)
 have hL16:16≤ L:=Nat.le_log_of_pow_le (by omega) (by omega)
 have h2M_lt:2*M<2^(L+1):=Nat.lt_pow_succ_log_self (by omega) (2*M)
 have hL4:L^4≤2*M:=(Vr L hL16).trans (Nat.pow_log_le_self 2 (by omega))
 have hsq_le:Nat.sqrt (2*M)*Nat.sqrt (2*M)≤2*M:=Nat.sqrt_le (2*M)
 have hprod_le:(Nat.sqrt (2*M)+1)*(L+1)≤ M/3:=by
  have hs1:Nat.sqrt (2*M)≥1000:=Nat.le_sqrt.mpr (by omega)
  have h1:(Nat.sqrt (2*M)+1)^2≤2*(2*M):=by nlinarith
  have h2:(L+1)^4≤2*L^4:=by nlinarith[sq_nonneg L,mul_self_nonneg (L^2)]
  have h3':((Nat.sqrt (2*M)+1)*(L+1))^4≤(M/3)^4:=by
   have h1sq:(Nat.sqrt (2*M)+1)^4≤(4*M)^2:=by
    calc (Nat.sqrt (2*M)+1)^4=((Nat.sqrt (2*M)+1)^2)^2:=by ring
      _≤(2*(2*M))^2:=Nat.pow_le_pow_left h1 2
      _=(4*M)^2:=by ring
   have h64:((Nat.sqrt (2*M)+1)*(L+1))^4≤64*M^3:=by
    calc ((Nat.sqrt (2*M)+1)*(L+1))^4
        = (Nat.sqrt (2*M)+1)^4*(L+1)^4:=by ring
      _≤(4*M)^2*(2*(2*M)):=Nat.mul_le_mul h1sq (h2.trans (Yd 2 hL4))
      _=64*M^3:=by ring
   have hM3:3*(M/3)+2≥M:=by omega
   have hM3_lo:M/3≥333333:=by omega
   have hM3_pow:64*M^3≤(M/3)^4:=by
    have hMle:M≤4*(M/3):=by omega
    have hM3_cube:M^3≤64*(M/3)^3:=by
     calc M^3≤(4*(M/3))^3:=Nat.pow_le_pow_left hMle 3
       _=64*(M/3)^3:=by ring
    calc 64*M^3≤64*(64*(M/3)^3):=Yd 64 hM3_cube
      _=4096*(M/3)^3:=by ring
      _≤(M/3)*(M/3)^3:=Yc _ (by omega)
      _=(M/3)^4:=by ring
   exact h64.trans hM3_pow
  exact le_of_pow_le_pow_left₀ (by omega) (Nat.zero_le _) h3'
 have hleft:M*(2*M)^Nat.sqrt (2*M)≤2^(M/3):=by
  calc M*(2*M)^Nat.sqrt (2*M)
      ≤ (2*M)*(2*M)^Nat.sqrt (2*M):=Yc _ (by omega)
    _=(2*M)^(Nat.sqrt (2*M)+1):=by rw[pow_succ']
    _≤(2^(L+1))^(Nat.sqrt (2*M)+1):=Nat.pow_le_pow_left h2M_lt.le _
    _=2^((L+1)*(Nat.sqrt (2*M)+1)):=by rw[←pow_mul]
    _≤2^(M/3):=Nat.pow_le_pow_right (by omega) (by rw[mul_comm];exact hprod_le)
 have hPpow:(2*M)^P.card≤2^((L+1)*P.card):=by
  calc (2*M)^P.card≤(2^(L+1))^P.card:=Nat.pow_le_pow_left h2M_lt.le _
    _=2^((L+1)*P.card):=by rw[←pow_mul]
 have h4eq:∀ t,4^t=2^(2*t):=fun t=>by
  calc 4^t=(2^2)^t:=by norm_num
    _=2^(2*t):=by rw[←pow_mul]
 have hexp:2^(2*M)<2^(M/3+2*(2*M/3)+(L+1)*P.card):=by
  calc 2^(2*M)=4^M:=(h4eq M).symm
    _< M*(2*M)^Nat.sqrt (2*M)*4^(2*M/3)*(2*M)^P.card:=hcomb
    _≤2^(M/3)*2^(2*(2*M/3))*2^((L+1)*P.card):=by
      rw[h4eq (2*M/3)];exact Nat.mul_le_mul (Yc _ hleft) hPpow
    _=2^(M/3+2*(2*M/3)+(L+1)*P.card):=by rw[pow_add,pow_add]
 have hlt:2*M< M/3+2*(2*M/3)+(L+1)*P.card :=(Nat.pow_lt_pow_iff_right (by omega:1<2)).mp hexp
 have hdiv:M/3+2*(2*M/3)≤5*M/3:=by omega
 have h3P:M≤3*((L+1)*P.card):=by omega
 calc M≤3*((L+1)*P.card):=h3P
   _=3*P.card*(L+1):=by ring
lemma Va (a L q r:ℕ) (hq:1≤ q) :((Icc (a+1) (a+L)).filter (fun x=>x % q=r)).card≤ L/q+1:=by
 rcases Nat.eq_zero_or_pos L with rfl|hLpos
 ·simp
 ·set S:=(Icc (a+1) (a+L)).filter (fun x=>x % q=r)
  rcases S.eq_empty_or_nonempty with hSe|hSne
  ·rw[hSe];simp
  ·let m:=S.min' hSne
   have hmS:m∈S:=min'_mem S hSne;have hmI:m∈Icc (a+1) (a+L):=(Za.mp hmS).1;have hmr:m % q=r:=(Za.mp hmS).2
   have hinj:Set.InjOn (fun x=>(x-m)/q) (S:Set ℕ):=by
    intro x hx y hy hxy;have hxS:=Zc.mp hx;have hyS:=Zc.mp hy;have hxm:m≤ x:=min'_le S x hxS;have hym:m≤ y:=min'_le S y hyS;have hxr:x % q=m % q:=((Za.mp hxS).2).trans hmr.symm;have hyr:y % q=m % q:=((Za.mp hyS).2).trans hmr.symm;obtain⟨kx,hkx⟩:=(Nat.modEq_iff_dvd' hxm).mp hxr.symm;obtain⟨ky,hky⟩:=(Nat.modEq_iff_dvd' hym).mp hyr.symm
    have hdx:(x-m)/q=kx:=by rw[hkx,Nat.mul_div_cancel_left _ (by omega)]
    have hdy:(y-m)/q=ky:=by rw[hky,Nat.mul_div_cancel_left _ (by omega)]
    have hkeq:kx=ky:=by rw[←hdx,←hdy];exact hxy
    rw[hkeq] at hkx;omega
   have hmaps:Set.MapsTo (fun x=>(x-m)/q) (S:Set ℕ) (range (L/q+1):Set ℕ):=by
    intro x hx;have hxS:=Zc.mp hx;have hxI:=Zb.mp (Za.mp hxS).1;have hmI':=Zb.mp hmI
    refine Zc.mpr (mem_range.mpr ?_)
    exact Nat.lt_succ_of_le (Nat.div_le_div_right (by omega:x-m≤ L))
   exact (card_le_card_of_injOn _ hmaps hinj).trans (by rw[card_range])
lemma Wt (N a L b M:ℕ) (hN:1≤ N)
  (haL:a+L≤ N) (hbM:b+M≤ N) :
  ((((Icc (a+1) (a+L)) ×ˢ (Icc (b+1) (b+M))).filter
   (fun p=>1< Nat.gcd p.1 p.2)).card:ℝ) ≤
   (43/100:ℝ)*(L:ℝ)*(M:ℝ)+50*(N:ℝ)*(log (N:ℝ)+2):=by
 let I:=Icc (a+1) (a+L)
 let J:=Icc (b+1) (b+M)
 let Bad:=(I ×ˢ J).filter (fun p=>1< Nat.gcd p.1 p.2)
 let B2:=(I ×ˢ J).filter (fun p=>2 ∣ p.1/\2 ∣ p.2)
 let B3:=(I ×ˢ J).filter (fun p=>3 ∣ p.1/\3 ∣ p.2/\¬ (2 ∣ p.1/\2 ∣ p.2))
 let B5:=(I ×ˢ J).filter (fun p=>5 ∣ p.1/\5 ∣ p.2/\¬ (2 ∣ p.1/\2 ∣ p.2)/\¬ (3 ∣ p.1/\3 ∣ p.2))
 let B7:=(I ×ˢ J).filter (fun p=>7 ∣ p.1/\7 ∣ p.2)
 let Thi:=(Icc 5 N).filter (fun t=>t≠7/\t≠10)
 let Bhi:=Thi.biUnion (fun t =>
  (I ×ˢ J).filter (fun p=>(2*t+1) ∣ p.1/\(2*t+1) ∣ p.2))
 have hcover:Bad⊆B2∪B3∪B5∪B7∪Bhi:=by
  intro p hp;obtain⟨hpIJ,hgcd⟩:=Za.mp hp
  have hminP:(Nat.gcd p.1 p.2).minFac.Prime:=Nat.minFac_prime (by omega)
  set q:=(Nat.gcd p.1 p.2).minFac;have hq1:q ∣ p.1:=(Nat.minFac_dvd _).trans (Nat.gcd_dvd_left _ _);have hq2:q ∣ p.2:=(Nat.minFac_dvd _).trans (Nat.gcd_dvd_right _ _)
  by_cases h2:2 ∣ p.1/\2 ∣ p.2
  ·exact Ze _ (Ze _ (Ze _
    (Ze _ (Za.mpr ⟨hpIJ,h2⟩))))
  by_cases h3:3 ∣ p.1/\3 ∣ p.2
  ·exact Ze _ (Ze _ (Ze _
    (Zg _ (Za.mpr ⟨hpIJ,h3.1,h3.2,h2⟩))))
  by_cases h5:5 ∣ p.1/\5 ∣ p.2
  ·exact Ze _ (Ze _ (Zg _
    (Za.mpr ⟨hpIJ,h5.1,h5.2,h2,h3⟩)))
  by_cases h7:7 ∣ p.1/\7 ∣ p.2
  ·exact Ze _ (Zg _
    (Za.mpr ⟨hpIJ,h7⟩))
  refine Zg _ ?_
  have hq11:11≤ q:=by
   have hqne2:q≠2:=fun h=>h2 ⟨h ▸ hq1,h ▸ hq2⟩
   have hqne3:q≠3:=fun h=>h3 ⟨h ▸ hq1,h ▸ hq2⟩
   have hqne5:q≠5:=fun h=>h5 ⟨h ▸ hq1,h ▸ hq2⟩
   have hqne7:q≠7:=fun h=>h7 ⟨h ▸ hq1,h ▸ hq2⟩
   by_contra hlt
   interval_cases q <;> first|omega|exact absurd hminP (by decide)
  have hqodd:Odd q:=hminP.odd_of_ne_two (by omega)
  obtain⟨t,hqt⟩:=hqodd
  have ht7:t≠7:=by intro h;rw[h] at hqt;exact absurd (hqt ▸ hminP) (by decide)
  have ht10:t≠10:=by intro h;rw[h] at hqt;exact absurd (hqt ▸ hminP) (by decide)
  have hp1N:p.1≤ N:=le_trans (Zb.mp (Zh.mp hpIJ).1).2 haL
  have hp1pos:0< p.1:=by have:=(Zb.mp (Zh.mp hpIJ).1).1;omega
  have hqN:q≤ N:=(Nat.le_of_dvd hp1pos hq1).trans hp1N
  refine mem_biUnion.mpr ⟨t,Za.mpr ⟨Zb.mpr ⟨by omega,by omega⟩,ht7,ht10⟩,?_⟩
  rw[←hqt];exact Za.mpr ⟨hpIJ,hq1,hq2⟩
 have hbox_mod:∀ q r1 r2:ℕ,1≤ q →
   (((I ×ˢ J).filter (fun p=>p.1 % q=r1/\p.2 % q=r2)).card:ℝ) ≤((L:ℝ)/(q:ℝ)+1)*((M:ℝ)/(q:ℝ)+1):=by
  intro q r1 r2 hq
  have heq:(I ×ˢ J).filter (fun p=>p.1 % q=r1/\p.2 % q=r2) =(I.filter (fun x=>x % q=r1)) ×ˢ (J.filter (fun y=>y % q=r2)):=by ext p;simp[and_assoc,and_left_comm]
  rw[heq,card_product,Nat.cast_mul]
  have h1:((I.filter (fun x=>x % q=r1)).card:ℝ)≤(L:ℝ)/(q:ℝ)+1:=by
   have hc:(I.filter (fun x=>x % q=r1)).card≤ L/q+1:=Va a L q r1 hq
   calc ((I.filter (fun x=>x % q=r1)).card:ℝ)≤((L/q+1:ℕ):ℝ):=by exact_mod_cast hc
     _=((L/q:ℕ):ℝ)+1:=by push_cast;rfl
     _≤(L:ℝ)/(q:ℝ)+1:=by linarith[Nat.cast_div_le (m:=L) (n:=q) (α:=ℝ)]
  have h2:((J.filter (fun y=>y % q=r2)).card:ℝ)≤(M:ℝ)/(q:ℝ)+1:=by
   have hc:(J.filter (fun y=>y % q=r2)).card≤ M/q+1:=Va b M q r2 hq
   calc ((J.filter (fun y=>y % q=r2)).card:ℝ)≤((M/q+1:ℕ):ℝ):=by exact_mod_cast hc
     _=((M/q:ℕ):ℝ)+1:=by push_cast;rfl
     _≤(M:ℝ)/(q:ℝ)+1:=by linarith[Nat.cast_div_le (m:=M) (n:=q) (α:=ℝ)]
  exact mul_le_mul h1 h2 (Nat.cast_nonneg _) (by positivity)
 have hLN:(L:ℝ)≤(N:ℝ):=by exact_mod_cast (by omega:L≤ N)
 have hMN:(M:ℝ)≤(N:ℝ):=by exact_mod_cast (by omega:M≤ N)
 have hN1:(1:ℝ)≤(N:ℝ):=by exact_mod_cast hN
 have hB2:(B2.card:ℝ)≤(1/4:ℝ)*(L:ℝ)*(M:ℝ)+2*(N:ℝ):=by
  have heq:B2=(I ×ˢ J).filter (fun p=>p.1 % 2=0/\p.2 % 2=0):=by ext p;simp[B2,Nat.dvd_iff_mod_eq_zero]
  rw[heq]
  have h:=hbox_mod 2 0 0 (by omega)
  push_cast at h;nlinarith
 have hB3:(B3.card:ℝ)≤(1/12:ℝ)*(L:ℝ)*(M:ℝ)+4*(N:ℝ):=by
  let R3:Zf (ℕ × ℕ):={(0,3),(3,0),(3,3)}
  have hsub3:B3⊆R3.biUnion (fun r=>(I ×ˢ J).filter (fun p=>p.1 % 6=r.1/\p.2 % 6=r.2)):=by
   intro p hp;obtain⟨hpIJ,h31,h32,hnot2⟩:=Za.mp hp
   refine mem_biUnion.mpr ⟨(p.1 % 6,p.2 % 6),?_,Za.mpr ⟨hpIJ,rfl,rfl⟩⟩
   simp only[R3,Zx,Zj,Prod.mk.injEq];omega
  have hcard3:(B3.card:ℝ)≤∑ r∈R3,(((I ×ˢ J).filter (fun p=>p.1 % 6=r.1/\p.2 % 6=r.2)).card:ℝ):=by
   have:=(Zm hsub3).trans card_biUnion_le
   exact_mod_cast this
  calc (B3.card:ℝ)
      ≤ ∑ _r∈R3,(((L:ℝ)/6+1)*((M:ℝ)/6+1)) :=hcard3.trans (Finset.sum_le_sum fun r _=>by simpa using hbox_mod 6 r.1 r.2 (by omega))
    _=3*(((L:ℝ)/6+1)*((M:ℝ)/6+1)):=by
        rw[Finset.sum_const];have:R3.card=3:=by decide
        rw[this,nsmul_eq_mul];norm_num
    _≤(1/12:ℝ)*(L:ℝ)*(M:ℝ)+4*(N:ℝ):=by nlinarith
 have hB5:(B5.card:ℝ)≤(2/75:ℝ)*(L:ℝ)*(M:ℝ)+26*(N:ℝ):=by
  let R5:Zf (ℕ × ℕ) :=((range 30) ×ˢ (range 30)).filter (fun r =>
    5 ∣ r.1/\5 ∣ r.2/\¬ (2 ∣ r.1/\2 ∣ r.2)/\¬ (3 ∣ r.1/\3 ∣ r.2))
  have hR5card:R5.card=24:=by decide
  have hsub5:B5⊆R5.biUnion (fun r=>(I ×ˢ J).filter (fun p=>p.1 % 30=r.1/\p.2 % 30=r.2)):=by
   intro p hp;obtain⟨hpIJ,h51,h52,hnot2,hnot3⟩:=Za.mp hp
   refine mem_biUnion.mpr ⟨(p.1 % 30,p.2 % 30),?_,Za.mpr ⟨hpIJ,rfl,rfl⟩⟩
   simp only[R5,Za,Zh,mem_range]
   refine⟨⟨Nat.mod_lt _ (by omega),Nat.mod_lt _ (by omega)⟩,?_,?_,?_,?_⟩
   ·omega
   ·omega
   ·intro ⟨h21,h22⟩;exact hnot2 ⟨by omega,by omega⟩
   ·intro ⟨h31,h32⟩;exact hnot3 ⟨by omega,by omega⟩
  have hcard5:(B5.card:ℝ)≤∑ r∈R5,(((I ×ˢ J).filter (fun p=>p.1 % 30=r.1/\p.2 % 30=r.2)).card:ℝ):=by
   have:=(Zm hsub5).trans card_biUnion_le
   exact_mod_cast this
  calc (B5.card:ℝ)
      ≤ ∑ _r∈R5,(((L:ℝ)/30+1)*((M:ℝ)/30+1)) :=hcard5.trans (Finset.sum_le_sum fun r _=>by simpa using hbox_mod 30 r.1 r.2 (by omega))
    _=24*(((L:ℝ)/30+1)*((M:ℝ)/30+1)):=by
        rw[Finset.sum_const,hR5card,nsmul_eq_mul];norm_num
    _≤(2/75:ℝ)*(L:ℝ)*(M:ℝ)+26*(N:ℝ):=by nlinarith
 have hB7:(B7.card:ℝ)≤(1/49:ℝ)*(L:ℝ)*(M:ℝ)+2*(N:ℝ):=by
  have heq:B7=(I ×ˢ J).filter (fun p=>p.1 % 7=0/\p.2 % 7=0):=by ext p;simp[B7,Nat.dvd_iff_mod_eq_zero]
  rw[heq]
  have h:=hbox_mod 7 0 0 (by omega)
  push_cast at h;nlinarith
 have hBhi:(Bhi.card:ℝ)≤(45/1000:ℝ)*(L:ℝ)*(M:ℝ)+2*(N:ℝ)*(log (N:ℝ)+2):=by
  have h1:(Bhi.card:ℝ)≤∑ t∈Thi,(((I ×ˢ J).filter (fun p=>(2*t+1) ∣ p.1/\(2*t+1) ∣ p.2)).card:ℝ):=by exact_mod_cast card_biUnion_le
  have h2:∀ t∈Thi,(((I ×ˢ J).filter (fun p=>(2*t+1) ∣ p.1/\(2*t+1) ∣ p.2)).card:ℝ) ≤(L:ℝ)*(M:ℝ)/(2*(t:ℝ)+1)^2+((L:ℝ)+(M:ℝ))/(2*(t:ℝ)+1)+1:=by
   intro t ht
   have heq:(I ×ˢ J).filter (fun p=>(2*t+1) ∣ p.1/\(2*t+1) ∣ p.2) =(I ×ˢ J).filter (fun p=>p.1 % (2*t+1)=0/\p.2 % (2*t+1)=0):=by ext p;simp[Nat.dvd_iff_mod_eq_zero]
   rw[heq]
   have h:=hbox_mod (2*t+1) 0 0 (by omega)
   push_cast at h
   have hring:((L:ℝ)/(2*(t:ℝ)+1)+1)*((M:ℝ)/(2*(t:ℝ)+1)+1) =(L:ℝ)*(M:ℝ)/(2*(t:ℝ)+1)^2+((L:ℝ)+(M:ℝ))/(2*(t:ℝ)+1)+1:=by
    have hpos:(2*(t:ℝ)+1)≠0:=by positivity
    field_simp;ring
   linarith
  have hsum1:∑ t∈Thi,(L:ℝ)*(M:ℝ)/(2*(t:ℝ)+1)^2 ≤(45/1000:ℝ)*(L:ℝ)*(M:ℝ):=by
   have heq:∑ t∈Thi,(L:ℝ)*(M:ℝ)/(2*(t:ℝ)+1)^2 =(L:ℝ)*(M:ℝ)*∑ t∈Thi,(1:ℝ)/(2*(t:ℝ)+1)^2:=by
    rw[Finset.mul_sum];refine Finset.sum_congr rfl fun t _=>?_;ring
   rw[heq]
   have hsubT:Thi⊆({5,6,8,9}:Zf ℕ)∪Icc 11 N:=by
    intro t ht;obtain⟨htI,h7,h10⟩:=Za.mp ht
    have:=Zb.mp htI
    simp only[Zd,Zx,Zj,Zb];omega
   have hdisjT:Disjoint ({5,6,8,9}:Zf ℕ) (Icc 11 N):=by
    rw[Zk];intro t h1 h2;simp only[Zx,Zj] at h1
    have:=(Zb.mp h2).1;omega
   have htail:=Xq 11 N (by omega)
   have hsumT:∑ t∈Thi,(1:ℝ)/(2*(t:ℝ)+1)^2≤45/1000:=by
    calc ∑ t∈Thi,(1:ℝ)/(2*(t:ℝ)+1)^2
        ≤ ∑ t∈({5,6,8,9}:Zf ℕ)∪Icc 11 N,(1:ℝ)/(2*(t:ℝ)+1)^2 :=sum_le_sum_of_subset_of_nonneg hsubT (fun _ _ _=>by positivity)
      _=(∑ t∈({5,6,8,9}:Zf ℕ),(1:ℝ)/(2*(t:ℝ)+1)^2) +
            ∑ t∈Icc 11 N,(1:ℝ)/(2*(t:ℝ)+1)^2:=Finset.sum_union hdisjT
      _≤45/1000:=by
          have h4:∑ t∈({5,6,8,9}:Zf ℕ),(1:ℝ)/(2*(t:ℝ)+1)^2 =1/121+1/169+1/289+1/361:=by norm_num
          rw[h4];norm_num at htail ⊢;linarith
   nlinarith[mul_nonneg (Nat.cast_nonneg (α:=ℝ) L) (Nat.cast_nonneg (α:=ℝ) M)]
  have hsum2:∑ t∈Thi,((L:ℝ)+(M:ℝ))/(2*(t:ℝ)+1) ≤2*(N:ℝ)*(log (N:ℝ)+1):=by
   have hstep:∀ t∈Thi,((L:ℝ)+(M:ℝ))/(2*(t:ℝ)+1)≤(2*(N:ℝ))*((1:ℝ)/(t:ℝ)):=by
    intro t ht
    have htpos:(0:ℝ)<(t:ℝ):=by
     exact_mod_cast (by have:=(Zb.mp (Za.mp ht).1).1;omega:0< t)
    have hnum:(L:ℝ)+(M:ℝ)≤2*(N:ℝ):=by linarith
    calc ((L:ℝ)+(M:ℝ))/(2*(t:ℝ)+1)
        ≤ (2*(N:ℝ))/(2*(t:ℝ)+1):=div_le_div_of_nonneg_right hnum (by positivity)
      _≤(2*(N:ℝ))/(t:ℝ):=div_le_div_of_nonneg_left (by positivity) htpos (by linarith)
      _=(2*(N:ℝ))*((1:ℝ)/(t:ℝ)):=by ring
   calc ∑ t∈Thi,((L:ℝ)+(M:ℝ))/(2*(t:ℝ)+1)
       ≤ ∑ t∈Thi,(2*(N:ℝ))*((1:ℝ)/(t:ℝ)):=Finset.sum_le_sum hstep
     _=2*(N:ℝ)*∑ t∈Thi,(1:ℝ)/(t:ℝ):=(Finset.mul_sum _ _ _).symm
     _≤2*(N:ℝ)*∑ t∈Icc 1 N,(1:ℝ)/(t:ℝ):=by
         refine Zp ?_ (by positivity)
         exact sum_le_sum_of_subset_of_nonneg
           (fun t ht=>by
             have h:=Zb.mp (Za.mp ht).1
             exact Zb.mpr ⟨by omega,h.2⟩)
           (fun _ _ _=>by positivity)
     _≤2*(N:ℝ)*(log (N:ℝ)+1) :=
         Zp (Q0 N hN) (by positivity)
  have hsum3:∑ _t∈Thi,(1:ℝ)≤(N:ℝ):=by
   rw[Finset.sum_const,nsmul_eq_mul,mul_one];have hcard:Thi.card≤(Icc 5 N).card:=Zm (Zl _ _);rw[Nat.card_Icc] at hcard
   exact_mod_cast (by omega:Thi.card≤ N)
  calc (Bhi.card:ℝ)
      ≤ ∑ t∈Thi,((L:ℝ)*(M:ℝ)/(2*(t:ℝ)+1)^2+((L:ℝ)+(M:ℝ))/(2*(t:ℝ)+1)+1) :=h1.trans (Finset.sum_le_sum h2)
    _=(∑ t∈Thi,(L:ℝ)*(M:ℝ)/(2*(t:ℝ)+1)^2) +
        (∑ t∈Thi,((L:ℝ)+(M:ℝ))/(2*(t:ℝ)+1)) +
        ∑ _t∈Thi,(1:ℝ):=by
        rw[Finset.sum_add_distrib,Finset.sum_add_distrib]
    _≤(45/1000:ℝ)*(L:ℝ)*(M:ℝ)+2*(N:ℝ)*(log (N:ℝ)+1)+(N:ℝ):=by
        linarith
    _≤(45/1000:ℝ)*(L:ℝ)*(M:ℝ)+2*(N:ℝ)*(log (N:ℝ)+2):=by
        linarith
 have htot:(Bad.card:ℝ)≤(B2.card:ℝ)+(B3.card:ℝ)+(B5.card:ℝ)+(B7.card:ℝ)+(Bhi.card:ℝ):=by
  have h1:=Zm hcover;have h2:=Yh (B2∪B3∪B5∪B7) Bhi;have h3:=Yh (B2∪B3∪B5) B7;have h4:=Yh (B2∪B3) B5;have h5:=Yh B2 B3
  have hall:Bad.card≤ B2.card+B3.card+B5.card+B7.card+Bhi.card:=by omega
  exact_mod_cast hall
 have hlog_nonneg:0≤ log (N:ℝ):=Real.log_nonneg hN1
 have hLM_nonneg:0≤(L:ℝ)*(M:ℝ):=by positivity
 nlinarith
lemma Xt (N a L b M:ℕ) (hN:1≤ N) (haL:a+L≤ N) (hbM:b+M≤ N) :(57/100:ℝ)*(L:ℝ)*(M:ℝ)-50*(N:ℝ)*(log (N:ℝ)+2) ≤((((Icc (a+1) (a+L)) ×ˢ (Icc (b+1) (b+M))).filter
    (fun p=>Nat.gcd p.1 p.2=1)).card:ℝ):=by
 let S:=(Icc (a+1) (a+L)) ×ˢ (Icc (b+1) (b+M))
 have hpart:(S.filter (fun p=>Nat.gcd p.1 p.2=1)).card +(S.filter (fun p=>1< Nat.gcd p.1 p.2)).card=S.card:=by
  have heq:S.filter (fun p=>1< Nat.gcd p.1 p.2) =S.filter (fun p=>¬ (Nat.gcd p.1 p.2=1)):=by
   refine filter_congr fun p hp=>?_
   have hp1:0< p.1:=by have:=(Zb.mp (Zh.mp hp).1).1;omega
   have hg:0< Nat.gcd p.1 p.2:=Nat.gcd_pos_of_pos_left p.2 hp1;omega
  rw[heq];exact card_filter_add_card_filter_not _
 have hScard:(S.card:ℝ)=(L:ℝ)*(M:ℝ):=by
  rw[card_product,Nat.card_Icc,Nat.card_Icc]
  have h1:a+L+1-(a+1)=L:=by omega
  have h2:b+M+1-(b+1)=M:=by omega
  rw[h1,h2,Nat.cast_mul]
 have hpartR:((S.filter (fun p=>Nat.gcd p.1 p.2=1)).card:ℝ) +((S.filter (fun p=>1< Nat.gcd p.1 p.2)).card:ℝ)=(L:ℝ)*(M:ℝ):=by rw[←hScard];exact_mod_cast hpart
 linarith[Wt N a L b M hN haL hbM]
lemma W5 (N a L:ℕ) (hN:1≤ N) (haL:a+L≤ N) :(285/1000:ℝ)*(L:ℝ)^2-26*(N:ℝ)*(log (N:ℝ)+2) ≤((((Icc (a+1) (a+L)) ×ˢ (Icc (a+1) (a+L))).filter
    (fun p=>p.1< p.2/\Nat.gcd p.1 p.2=1)).card:ℝ):=by
 let I:=Icc (a+1) (a+L)
 let Cop:=(I ×ˢ I).filter (fun p=>Nat.gcd p.1 p.2=1)
 let Tri:=(I ×ˢ I).filter (fun p=>p.1< p.2/\Nat.gcd p.1 p.2=1)
 let Tri':=(I ×ˢ I).filter (fun p=>p.2< p.1/\Nat.gcd p.1 p.2=1)
 let Diag:=(I ×ˢ I).filter (fun p=>p.1=p.2/\Nat.gcd p.1 p.2=1)
 have hcard_eq:Tri'.card=Tri.card:=by
  refine card_bij (fun p _=>(p.2,p.1)) ?_ ?_ ?_
  ·intro p hp
   obtain⟨hpI,hlt,hg⟩:=Za.mp hp;obtain⟨h1,h2⟩:=Zh.mp hpI
   exact Za.mpr ⟨Zh.mpr ⟨h2,h1⟩,hlt,by rw[Nat.gcd_comm];exact hg⟩
  ·intro p _ q _ h;ext <;> [exact congrArg Prod.snd h;exact congrArg Prod.fst h]
  ·intro p hp
   obtain⟨hpI,hlt,hg⟩:=Za.mp hp;obtain⟨h1,h2⟩:=Zh.mp hpI
   exact⟨(p.2,p.1),Za.mpr ⟨Zh.mpr ⟨h2,h1⟩,hlt,by rw[Nat.gcd_comm];exact hg⟩,rfl⟩
 have hdiag:Diag.card≤1:=by
  have hsub:Diag⊆{(1,1)}:=by
   rintro⟨x,y⟩ hp
   obtain⟨-,heq,hg⟩:=Za.mp hp;simp only at heq hg;rw[heq,Nat.gcd_self] at hg;simp[heq.trans hg,hg]
  exact (Zm hsub).trans (by simp)
 have hcover:Cop⊆Tri∪Tri'∪Diag:=by
  intro p hp;obtain⟨hpI,hg⟩:=Za.mp hp
  rcases lt_trichotomy p.1 p.2 with hlt|heq|hgt
  ·exact Ze _ (Ze _ (Za.mpr ⟨hpI,hlt,hg⟩))
  ·exact Zg _ (Za.mpr ⟨hpI,heq,hg⟩)
  ·exact Ze _ (Zg _ (Za.mpr ⟨hpI,hgt,hg⟩))
 have hle:Cop.card≤2*Tri.card+1:=by have h1:=Zm hcover;have h2:=Yh (Tri∪Tri') Diag;have h3:=Yh Tri Tri';omega
 have hleR:(Cop.card:ℝ)≤2*(Tri.card:ℝ)+1:=by exact_mod_cast hle
 have hbox:=Xt N a L a L hN haL haL
 have hN1:(1:ℝ)≤(N:ℝ):=by exact_mod_cast hN
 have hlog_nonneg:0≤ log (N:ℝ):=Real.log_nonneg hN1;nlinarith
noncomputable def fInt (L m:ℝ):ℝ :=if L< m then 0 else if 2*m≤ L then L^2/4-m^2/2 else (L-m)^2/2
lemma Vf (L m:ℝ) (hm:0≤ m):0≤ fInt L m:=by
 unfold fInt
 split_ifs with h1 h2
 ·exact le_rfl
 ·nlinarith
 ·positivity
lemma Wf {L₁ L₂ m:ℝ} (h0:0≤ L₁) (h12:L₁≤ L₂) (hm:0≤ m) :fInt L₁ m≤ fInt L₂ m:=by
 unfold fInt
 split_ifs with h1 h2 h3 h4 h5 h6
 ·exact le_rfl
 ·nlinarith
 ·positivity
 ·linarith
 ·nlinarith
 ·linarith
 ·linarith
 ·nlinarith
 ·nlinarith
lemma Xr (L m:ℝ) (hL:0≤ L) (hm:0≤ m) :fInt L m≤ L^2/4:=by
 unfold fInt
 split_ifs with h1 h2
 ·positivity
 ·nlinarith
 ·nlinarith
lemma Xm (p q m:ℕ) :((((Icc 0 p) ×ˢ (Icc 0 q)).filter (fun z=>m≤ z.1+z.2)).card:ℝ) ≤ fInt ((p+q:ℕ):ℝ) (m:ℝ)+3*((p+q:ℕ):ℝ)+2:=by
 suffices hsym:∀ a b:ℕ,a≤ b →
   ((((Icc 0 a) ×ˢ (Icc 0 b)).filter (fun z=>m≤ z.1+z.2)).card:ℝ) ≤ fInt ((a+b:ℕ):ℝ) (m:ℝ)+3*((a+b:ℕ):ℝ)+2 by
  rcases le_total p q with hpq|hqp
  ·exact hsym p q hpq
  ·have heq:(((Icc 0 p) ×ˢ (Icc 0 q)).filter (fun z=>m≤ z.1+z.2)).card =(((Icc 0 q) ×ˢ (Icc 0 p)).filter (fun z=>m≤ z.1+z.2)).card:=by
    refine card_bij (fun z _=>(z.2,z.1)) ?_ ?_ ?_
    ·intro z hz
     obtain⟨hzP,hzm⟩:=Za.mp hz;obtain⟨h1,h2⟩:=Zh.mp hzP
     exact Za.mpr ⟨Zh.mpr ⟨h2,h1⟩,by omega⟩
    ·intro z _ w _ h;ext <;> [exact congrArg Prod.snd h;exact congrArg Prod.fst h]
    ·intro z hz
     obtain⟨hzP,hzm⟩:=Za.mp hz;obtain⟨h1,h2⟩:=Zh.mp hzP
     exact⟨(z.2,z.1),Za.mpr ⟨Zh.mpr ⟨h2,h1⟩,by omega⟩,rfl⟩
   rw[heq,add_comm p q];exact hsym q p hqp
 intro a b hab;set L:=a+b
 set S:=((Icc 0 a) ×ˢ (Icc 0 b)).filter (fun z=>m≤ z.1+z.2)
 rcases lt_or_ge L m with hLm|hmL
 ·have hSe:S=∅:=by
   rw[eq_empty_iff_forall_notMem];intro z hz;obtain⟨hzP,hzm⟩:=Za.mp hz;have h1:=(Zb.mp (Zh.mp hzP).1).2;have h2:=(Zb.mp (Zh.mp hzP).2).2;omega
  rw[hSe,card_empty,Nat.cast_zero]
  have:=Vf (L:ℝ) (m:ℝ) (Nat.cast_nonneg m)
  positivity
 ·
  have hL_ge:(m:ℝ)≤(L:ℝ):=by exact_mod_cast hmL
  rcases le_or_gt m a with hma|ham
  ·
   set E:=((Icc 0 a) ×ˢ (Icc 0 b)).filter (fun z=>z.1+z.2< m)
   have hpart:S.card+E.card=(a+1)*(b+1):=by
    have heq:E=((Icc 0 a) ×ˢ (Icc 0 b)).filter (fun z=>¬ (m≤ z.1+z.2)):=by
     refine filter_congr fun _ _=>by omega
    rw[heq]
    simpa [S,card_product,Nat.card_Icc] using
     card_filter_add_card_filter_not (s:=(Icc 0 a) ×ˢ (Icc 0 b))
      (p:=fun z=>m≤ z.1+z.2)
   have hE_ge:m*m≤2*E.card:=by
    have hsub:(range m).sigma (fun x=>range (m-x)) ⊆
      E.map ⟨fun z=>⟨z.1,z.2⟩,fun ⟨x₁,y₁⟩ ⟨x₂,y₂⟩ h=>by simp at h;ext <;> simp[h]⟩:=by
     intro ⟨x,y⟩ hxy;obtain⟨hx,hy⟩:=mem_sigma.mp hxy;dsimp only at hx hy;rw[mem_range] at hx hy;rw[Finset.mem_map]
     exact⟨(x,y),Za.mpr ⟨Zh.mpr
      ⟨Zb.mpr ⟨Nat.zero_le _,by omega⟩,Zb.mpr ⟨Nat.zero_le _,by omega⟩⟩,
      by omega⟩,rfl⟩
    have hsig:((range m).sigma (fun x=>range (m-x))).card =∑ x∈range m,(m-x):=by
     rw[card_sigma];refine Finset.sum_congr rfl fun x _=>card_range _
    have hsum_ge:∀ n:ℕ,n*n≤2*∑ x∈range n,(n-x):=by
     intro n
     induction n with
     | zero=>simp
     | succ k ih =>
      have h1:∑ x∈range (k+1),(k+1-x) =(k+1)+∑ x∈range k,(k-x):=by rw[sum_range_succ'];simp only[Nat.sub_zero,Nat.succ_sub_succ_eq_sub];omega
      rw[h1];nlinarith
    have hcardE:∑ x∈range m,(m-x)≤ E.card:=by
     rw[←hsig]
     exact (Zm hsub).trans (by rw[card_map])
    have:=hsum_ge m
    omega
   have hpartR:(S.card:ℝ)+(E.card:ℝ)=((a:ℝ)+1)*((b:ℝ)+1):=by exact_mod_cast hpart
   have hER:(m:ℝ)^2/2≤(E.card:ℝ):=by
    have:(m:ℝ)*(m:ℝ)≤2*(E.card:ℝ):=by exact_mod_cast hE_ge
    nlinarith
   have hf:fInt (L:ℝ) (m:ℝ)=(L:ℝ)^2/4-(m:ℝ)^2/2:=by
    unfold fInt
    rw[if_neg (by linarith),if_pos (by exact_mod_cast (by omega:2*m≤ L))]
   rw[hf]
   have hLab:(L:ℝ)=(a:ℝ)+(b:ℝ):=by exact_mod_cast rfl
   nlinarith[sq_nonneg ((a:ℝ)-(b:ℝ))]
  ·rcases le_or_gt m b with hmb|hbm
   ·
    have hsub:S⊆(Icc 0 a).biUnion (fun x =>
      (Icc (m-x) b).image (fun y=>(x,y))):=by
     intro ⟨x,y⟩ hxy;obtain⟨hP,hzm⟩:=Za.mp hxy;obtain⟨hx,hy⟩:=Zh.mp hP
     refine mem_biUnion.mpr ⟨x,hx,Zi.mpr ⟨y,?_,rfl⟩⟩
     exact Zb.mpr ⟨by omega,(Zb.mp hy).2⟩
    have hScard:S.card≤∑ x∈Icc 0 a,(b+1-(m-x)):=by
     calc S.card≤((Icc 0 a).biUnion (fun x =>
             (Icc (m-x) b).image (fun y=>(x,y)))).card:=Zm hsub
       _≤∑ x∈Icc 0 a,((Icc (m-x) b).image (fun y=>(x,y))).card :=
           card_biUnion_le
       _≤∑ x∈Icc 0 a,(Icc (m-x) b).card :=
           Finset.sum_le_sum fun _ _=>card_image_le
       _=∑ x∈Icc 0 a,(b+1-(m-x)) :=
           Finset.sum_congr rfl fun _ _=>Nat.card_Icc _ _
    have hsum_eq:2*∑ x∈Icc 0 a,(b+1-(m-x)) =(a+1)*(2*b+2-2*m+a):=by
     have hterm:∀ x∈Icc 0 a,b+1-(m-x)=(b+1-m)+x:=by intro x hx;have:=(Zb.mp hx).2;omega
     rw[Finset.sum_congr rfl hterm,Finset.sum_add_distrib,Finset.sum_const,Nat.card_Icc]
     have hsumx:∀ n:ℕ,2*∑ x∈Icc 0 n,x=n*(n+1):=by
      intro n
      induction n with
      | zero=>simp
      | succ k ih =>
       rw[sum_Icc_succ_top (Nat.zero_le _)];nlinarith
     simp only[Nat.sub_zero,smul_eq_mul];have h2x:=hsumx a
     have hmul2:2*(b+1-m)=2*b+2-2*m:=by omega
     calc 2*((a+1)*(b+1-m)+∑ x∈Icc 0 a,x)
         = (a+1)*(2*(b+1-m))+2*∑ x∈Icc 0 a,x:=by ring
       _=(a+1)*(2*b+2-2*m)+a*(a+1):=by rw[hmul2,h2x]
       _=(a+1)*(2*b+2-2*m+a):=by ring
    have hSR:2*(S.card:ℝ)≤((a:ℝ)+1)*(2*(b:ℝ)+2-2*(m:ℝ)+(a:ℝ)):=by
     have h1:2*S.card≤(a+1)*(2*b+2-2*m+a):=by omega
     have h1R:(2*S.card:ℝ)≤((a+1:ℕ):ℝ)*((2*b+2-2*m+a:ℕ):ℝ):=by exact_mod_cast h1
     have hcast:((2*b+2-2*m+a:ℕ):ℝ)=2*(b:ℝ)+2-2*(m:ℝ)+(a:ℝ):=by
      have hle:2*m≤2*b+2:=by omega
      have:2*b+2-2*m+a=(2*b+2+a)-2*m:=by omega
      rw[this,Nat.cast_sub (by omega)]
      push_cast;ring
     rw[hcast] at h1R;push_cast at h1R;linarith
    have hLab:(L:ℝ)=(a:ℝ)+(b:ℝ):=by exact_mod_cast rfl
    have ha_lt_m:(a:ℝ)≤(m:ℝ):=by exact_mod_cast (le_of_lt ham)
    have ha_nn:(0:ℝ)≤(a:ℝ):=Nat.cast_nonneg a;have hm_nn:(0:ℝ)≤(m:ℝ):=Nat.cast_nonneg m;unfold fInt
    rw[if_neg (by linarith)]
    split_ifs with h2m
    ·
     nlinarith[sq_nonneg ((L:ℝ)-2*(m:ℝ)),mul_nonneg (sub_nonneg.mpr ha_lt_m)
      (show 0≤2*(L:ℝ)-3*(m:ℝ)-(a:ℝ) by linarith)]
    ·
     nlinarith[sq_nonneg ((L:ℝ)-(m:ℝ)-(a:ℝ))]
   ·
    set r:=L-m
    have hsub:S⊆(Icc 0 r).biUnion (fun u =>
      (Icc 0 (r-u)).image (fun v=>(a-u,b-v))):=by
     intro ⟨x,y⟩ hxy;obtain⟨hP,hzm⟩:=Za.mp hxy;have hx:=(Zb.mp (Zh.mp hP).1).2;have hy:=(Zb.mp (Zh.mp hP).2).2
     refine mem_biUnion.mpr ⟨a-x,Zb.mpr ⟨Nat.zero_le _,by omega⟩,Zi.mpr ⟨b-y,Zb.mpr ⟨Nat.zero_le _,by omega⟩,?_⟩⟩
     ext <;> dsimp <;> omega
    have hScard:S.card≤∑ u∈Icc 0 r,(r-u+1):=by
     calc S.card≤((Icc 0 r).biUnion (fun u =>
             (Icc 0 (r-u)).image (fun v=>(a-u,b-v)))).card :=
           Zm hsub
       _≤∑ u∈Icc 0 r,((Icc 0 (r-u)).image (fun v=>(a-u,b-v))).card :=
           card_biUnion_le
       _≤∑ u∈Icc 0 r,(Icc 0 (r-u)).card :=
           Finset.sum_le_sum fun _ _=>card_image_le
       _=∑ u∈Icc 0 r,(r-u+1) :=
           Finset.sum_congr rfl fun _ _=>by rw[Nat.card_Icc];omega
    have htri:∀ n:ℕ,2*∑ u∈Icc 0 n,(n-u+1)=(n+1)*(n+2):=by
     intro n
     induction n with
     | zero=>simp
     | succ k ih =>
      have h1:∑ u∈Icc 0 (k+1),(k+1-u+1) =(k+2)+∑ u∈Icc 0 k,(k-u+1):=by
       have hshift:∑ u∈Icc 0 (k+1),(k+1-u+1) =∑ u∈range (k+2),(k+1-u+1):=by congr 1;ext u;simp only[Zb,mem_range];omega
       have hshift2:∑ u∈Icc 0 k,(k-u+1) =∑ u∈range (k+1),(k-u+1):=by congr 1;ext u;simp only[Zb,mem_range];omega
       rw[hshift,hshift2,sum_range_succ'];simp only[Nat.sub_zero,Nat.succ_sub_succ_eq_sub];omega
      rw[h1];nlinarith
    have hSR:2*(S.card:ℝ)≤((r:ℝ)+1)*((r:ℝ)+2):=by
     have:=htri r
     have:2*S.card≤(r+1)*(r+2):=by omega
     exact_mod_cast this
    have hr_eq:(r:ℝ)=(L:ℝ)-(m:ℝ):=by rw[Nat.cast_sub hmL]
    have hf:fInt (L:ℝ) (m:ℝ)=((L:ℝ)-(m:ℝ))^2/2:=by
     unfold fInt
     rw[if_neg (by linarith),if_neg (by
      have:(L:ℝ)<2*(m:ℝ):=by exact_mod_cast (by omega:L<2*m)
      linarith)]
    rw[hf]
    have hr_le:(r:ℝ)≤(L:ℝ):=by exact_mod_cast (Nat.sub_le L m)
    nlinarith
lemma Vt (L m p:ℕ) (hp:p≤ L) :((((Icc 0 L) ×ˢ (Icc 0 L)).filter
   (fun z=>z.1≤ p/\p≤ z.2/\m≤ z.2-z.1+1)).card:ℝ) ≤
   fInt (L:ℝ) (m:ℝ)+4*(L:ℝ)+4:=by
 let S:=((Icc 0 L) ×ˢ (Icc 0 L)).filter
  (fun z=>z.1≤ p/\p≤ z.2/\m≤ z.2-z.1+1)
 let T1:=((Icc 0 p) ×ˢ (Icc 0 (L-p))).filter (fun z=>m≤ z.1+z.2)
 let T2:=((Icc 0 p) ×ˢ (Icc 0 (L-p))).filter (fun z=>z.1+z.2+1=m)
 have hmaps:Set.MapsTo (fun z:ℕ × ℕ=>(p-z.1,z.2-p)) (S:Set (ℕ × ℕ)) ((T1∪T2:Zf (ℕ × ℕ)):Set (ℕ × ℕ)):=by
  intro ⟨x,y⟩ hxy;obtain⟨hP,hx,hy,hlen⟩:=Za.mp (Zc.mp hxy);have hyL:=(Zb.mp (Zh.mp hP).2).2
  have hmemP:(p-x,y-p)∈(Icc 0 p) ×ˢ (Icc 0 (L-p)) :=Zh.mpr ⟨Zb.mpr ⟨Nat.zero_le _,by omega⟩,Zb.mpr ⟨Nat.zero_le _,by omega⟩⟩
  rw[Zc,Zd]
  rcases le_or_gt m ((p-x)+(y-p)) with hge|hlt
  ·exact Or.inl (Za.mpr ⟨hmemP,by dsimp;omega⟩)
  ·exact Or.inr (Za.mpr ⟨hmemP,by dsimp;omega⟩)
 have hinj:Set.InjOn (fun z:ℕ × ℕ=>(p-z.1,z.2-p)) (S:Set (ℕ × ℕ)):=by
  intro ⟨x₁,y₁⟩ h1 ⟨x₂,y₂⟩ h2 heq;have h1':=(Za.mp (Zc.mp h1)).2;have h2':=(Za.mp (Zc.mp h2)).2;have e1:p-x₁=p-x₂:=congrArg Prod.fst heq;have e2:y₁-p=y₂-p:=congrArg Prod.snd heq
  ext <;> dsimp <;> omega
 have hT2:T2.card≤ p+1:=by
  have hinj2:Set.InjOn Prod.fst (T2:Set (ℕ × ℕ)):=by
   intro ⟨x₁,y₁⟩ h1 ⟨x₂,y₂⟩ h2 heq;have e1:=(Za.mp (Zc.mp h1)).2;have e2:=(Za.mp (Zc.mp h2)).2
   dsimp at heq;ext <;> dsimp <;> omega
  have hmaps2:Set.MapsTo Prod.fst (T2:Set (ℕ × ℕ)) ((Icc 0 p:Zf ℕ):Set ℕ):=by intro z hz;exact Zc.mpr (Zh.mp (Za.mp (Zc.mp hz)).1).1
  exact (card_le_card_of_injOn _ hmaps2 hinj2).trans (by rw[Nat.card_Icc];omega)
 have hcard:S.card≤ T1.card+(L+1):=by have h1:=(card_le_card_of_injOn _ hmaps hinj).trans (Yh T1 T2);omega
 have hcardR:(S.card:ℝ)≤(T1.card:ℝ)+(L:ℝ)+1:=by exact_mod_cast hcard
 have hT1:=Xm p (L-p) m
 have hpq:p+(L-p)=L:=by omega
 rw[hpq] at hT1;linarith
lemma Ws (a b d m:ℕ) (hd:1≤ d) (hab:a≤ b)
  (F:Zf (Zf ℕ))
  (hsub:∀ A∈F,A⊆Icc a b)
  (hstep:∀ A∈F,∃ x₀ k,2≤ k/\m≤ k/\∀ x,x∈A↔∃ i< k,x=x₀+i*d)
  (hmeet:∀ A∈F,∀ B∈F,A≠B->(A∩B).Nonempty) :
  (F.card:ℝ)≤ fInt (((b-a:ℕ):ℝ)/(d:ℝ)) (m:ℝ)+4*(((b-a:ℕ):ℝ)/(d:ℝ))+4:=by
 rcases F.eq_empty_or_nonempty with rfl|hFne
 ·simp only[card_empty,Nat.cast_zero]
  have:=Vf (((b-a:ℕ):ℝ)/(d:ℝ)) (m:ℝ) (Nat.cast_nonneg m)
  positivity
 obtain⟨A₀,hA₀⟩:=hFne;obtain⟨x₀,k₀,hk₀,-,hA₀_eq⟩:=hstep A₀ hA₀
 have hmod_all:∀ A∈F,∀ x∈A,x % d=x₀ % d:=by
  intro A hA x hx;obtain⟨xA,kA,hkA,-,hA_eq⟩:=hstep A hA;obtain⟨ix,-,rfl⟩:=(hA_eq x).mp hx
  by_cases heq:A=A₀
  ·subst heq
   obtain⟨j,-,hj⟩:=(hA₀_eq (xA+ix*d)).mp hx;rw[hj,Nat.add_mul_mod_self_right]
  ·obtain⟨w,hw⟩:=hmeet A hA A₀ hA₀ heq
   obtain⟨iw,-,hwA⟩:=(hA_eq w).mp (Zn.mp hw).1;obtain⟨jw,-,hw₀⟩:=(hA₀_eq w).mp (Zn.mp hw).2
   have hm1:w % d=xA % d:=by rw[hwA,Nat.add_mul_mod_self_right]
   have hm2:w % d=x₀ % d:=by rw[hw₀,Nat.add_mul_mod_self_right]
   rw[Nat.add_mul_mod_self_right,←hm1,hm2]
 set L:=(b-a)/d
 have hlo:∀ A:Zf ℕ,∃ lo hi:ℕ,A∈F →
   lo∈A/\hi∈A/\(∀ x∈A,lo≤ x/\x≤ hi) ∧
   m≤(hi-a)/d-(lo-a)/d+1:=by
  intro A
  by_cases hA:A∈F
  ·obtain⟨xA,kA,hkA,hmA,hA_eq⟩:=hstep A hA
   have hmm:=Wa (by omega) (fun _=>hd) hA_eq
   have hxa:a≤ xA:=(Zb.mp (hsub A hA hmm.1)).1
   have hhi_sub:(xA+(kA-1)*d-a)/d=(xA-a)/d+(kA-1):=by
    have:xA+(kA-1)*d-a=(xA-a)+(kA-1)*d:=by omega
    rw[this,Nat.add_mul_div_right _ _ hd]
   exact⟨xA,xA+(kA-1)*d,fun _=>⟨hmm.1,hmm.2.1,hmm.2.2,by omega⟩⟩
  ·exact⟨0,0,fun h=>absurd h hA⟩
 choose lo hi hlh using hlo
 obtain⟨A_max,hA_max,hp_max⟩:=exists_max_image F (fun A=>(lo A-a)/d) ⟨A₀,hA₀⟩
 set p:=(lo A_max-a)/d
 have hp_le_L:p≤ L:=by
  have h1:=Zb.mp (hsub A_max hA_max (hlh A_max hA_max).1)
  exact Nat.div_le_div_right (by omega:lo A_max-a≤ b-a)
 let Box:=((Icc 0 L) ×ˢ (Icc 0 L)).filter
  (fun z=>z.1≤ p/\p≤ z.2/\m≤ z.2-z.1+1)
 have hmaps:Set.MapsTo (fun A=>((lo A-a)/d,(hi A-a)/d)) (F:Set (Zf ℕ)) (Box:Set (ℕ × ℕ)):=by
  intro A hA';have hA:=Zc.mp hA';obtain⟨hloA,hhiA,hbA,hmA⟩:=hlh A hA;have hloI:=Zb.mp (hsub A hA hloA);have hhiI:=Zb.mp (hsub A hA hhiA)
  have h1:(lo A-a)/d≤ L:=Nat.div_le_div_right (by omega)
  have h2:(hi A-a)/d≤ L:=Nat.div_le_div_right (by omega)
  have h3:(lo A-a)/d≤ p:=hp_max A hA
  have h4:p≤(hi A-a)/d:=by
   by_cases heq:A=A_max
   ·subst heq
    exact Nat.div_le_div_right (by have:=(hbA (hi A) hhiA).1;omega)
   ·obtain⟨w,hw⟩:=hmeet A hA A_max hA_max heq
    have hwA:=(hbA w (Zn.mp hw).1).2;have hwM:=((hlh A_max hA_max).2.2.1 w (Zn.mp hw).2).1
    exact Nat.div_le_div_right (by omega:lo A_max-a≤ hi A-a)
  exact Zc.mpr (Za.mpr ⟨Zh.mpr
   ⟨Zb.mpr ⟨Nat.zero_le _,h1⟩,Zb.mpr ⟨Nat.zero_le _,h2⟩⟩,h3,h4,hmA⟩)
 have hinj:Set.InjOn (fun A=>((lo A-a)/d,(hi A-a)/d)) (F:Set (Zf ℕ)):=by
  intro A hA' B hB' heq;have hA:=Zc.mp hA';have hB:=Zc.mp hB';obtain⟨hloA,hhiA,hbA,-⟩:=hlh A hA;obtain⟨hloB,hhiB,hbB,-⟩:=hlh B hB;have hq_lo:(lo A-a)/d=(lo B-a)/d:=congrArg Prod.fst heq;have hq_hi:(hi A-a)/d=(hi B-a)/d:=congrArg Prod.snd heq
  have hlo_eq:lo A=lo B:=by
   have h1:=(Zb.mp (hsub A hA hloA)).1;have h2:=(Zb.mp (hsub B hB hloB)).1;have hm1:lo A % d=lo B % d:=(hmod_all A hA _ hloA).trans (hmod_all B hB _ hloB).symm
   have hdm:(lo A-a) % d=(lo B-a) % d:=by
    rcases le_total (lo A) (lo B) with hle|hge
    ·have hdvd:d ∣ (lo B-a)-(lo A-a):=by
      have:(lo B-a)-(lo A-a)=lo B-lo A:=by omega
      rw[this];exact (Nat.modEq_iff_dvd' hle).mp hm1
     exact (Nat.modEq_iff_dvd' (by omega)).mpr hdvd
    ·have hdvd:d ∣ (lo A-a)-(lo B-a):=by
      have:(lo A-a)-(lo B-a)=lo A-lo B:=by omega
      rw[this];exact (Nat.modEq_iff_dvd' hge).mp hm1.symm
     exact ((Nat.modEq_iff_dvd' (by omega)).mpr hdvd).symm
   have e1:=Nat.div_add_mod (lo A-a) d;have e2:=Nat.div_add_mod (lo B-a) d;rw[hq_lo,hdm] at e1;omega
  have hhi_eq:hi A=hi B:=by
   have h1:=(Zb.mp (hsub A hA hhiA)).1;have h2:=(Zb.mp (hsub B hB hhiB)).1;have hm1:hi A % d=hi B % d:=(hmod_all A hA _ hhiA).trans (hmod_all B hB _ hhiB).symm
   have hdm:(hi A-a) % d=(hi B-a) % d:=by
    rcases le_total (hi A) (hi B) with hle|hge
    ·have hdvd:d ∣ (hi B-a)-(hi A-a):=by
      have:(hi B-a)-(hi A-a)=hi B-hi A:=by omega
      rw[this];exact (Nat.modEq_iff_dvd' hle).mp hm1
     exact (Nat.modEq_iff_dvd' (by omega)).mpr hdvd
    ·have hdvd:d ∣ (hi A-a)-(hi B-a):=by
      have:(hi A-a)-(hi B-a)=hi A-hi B:=by omega
      rw[this];exact (Nat.modEq_iff_dvd' hge).mp hm1.symm
     exact ((Nat.modEq_iff_dvd' (by omega)).mpr hdvd).symm
   have e1:=Nat.div_add_mod (hi A-a) d;have e2:=Nat.div_add_mod (hi B-a) d;rw[hq_hi,hdm] at e1;omega
  obtain⟨xA,kA,hkA,-,hA_eq⟩:=hstep A hA;obtain⟨xB,kB,hkB,-,hB_eq⟩:=hstep B hB
  have hmA:=Wa (by omega) (fun _=>hd) hA_eq
  have hmB:=Wa (by omega) (fun _=>hd) hB_eq
  have hxA:xA=lo A:=le_antisymm (hmA.2.2 _ hloA).1 (hbA _ hmA.1).1;have hxB:xB=lo B:=le_antisymm (hmB.2.2 _ hloB).1 (hbB _ hmB.1).1;have htopA:xA+(kA-1)*d=hi A:=le_antisymm (hbA _ hmA.2.1).2 (hmA.2.2 _ hhiA).2;have htopB:xB+(kB-1)*d=hi B:=le_antisymm (hbB _ hmB.2.1).2 (hmB.2.2 _ hhiB).2
  have hxAB:xA=xB:=by omega
  have hkAB:kA=kB:=by
   have:(kA-1)*d=(kB-1)*d:=by omega
   have:=Nat.eq_of_mul_eq_mul_right hd this
   omega
  ext x;rw[hA_eq,hB_eq,hxAB,hkAB]
 have hcardF:(F.card:ℝ)≤(Box.card:ℝ):=by exact_mod_cast card_le_card_of_injOn _ hmaps hinj
 have hBox:=Vt L m p hp_le_L;have hL_le:(L:ℝ)≤((b-a:ℕ):ℝ)/(d:ℝ):=Nat.cast_div_le;have hf_le:=Wf (Nat.cast_nonneg L) hL_le (Nat.cast_nonneg m);linarith
lemma Kh (N:ℕ) (F:Zf (Zf ℕ)) (hsub:∀ S∈F,S⊆Icc 1 N)
  (hsmall:∀ S∈F,S.card≤1):F.card≤ N+1:=by
 have hsubset:F⊆insert ∅ ((Icc 1 N).image (fun x=>({x}:Zf ℕ))):=by
  intro S hS
  rcases Nat.eq_zero_or_pos S.card with h0|hpos
  ·rw[card_eq_zero.mp h0];exact mem_insert_self _ _
  ·have h1:S.card=1:=by have:=hsmall S hS;omega
   obtain⟨x,hx⟩:=card_eq_one.mp h1
   refine mem_insert_of_mem (Zi.mpr ⟨x,?_,hx.symm⟩)
   exact hsub S hS (by rw[hx];exact mem_singleton_self x)
 calc F.card≤(insert ∅ ((Icc 1 N).image (fun x=>({x}:Zf ℕ)))).card :=
       Zm hsubset
   _≤((Icc 1 N).image (fun x=>({x}:Zf ℕ))).card+1:=card_insert_le _ _
   _≤(Icc 1 N).card+1:=Nat.add_le_add_right card_image_le 1
   _=N+1:=by rw[Nat.card_Icc];simp
lemma X9 (N:ℕ) (hN:1≤ N) (P:Zf (Zf ℕ))
  (hP:Zt N P)
  (hAP:∀ A∈P,IsAP A/\2≤ A.card) :
  (P.card:ℝ)≤(4125/10000:ℝ)*(N:ℝ)^2+12*(N:ℝ)*(log (N:ℝ)+2):=by
 have hsub:∀ A∈P,A⊆Icc 1 N:=fun A hA=>Zy.mp (hP.1 hA)
 have hmeet:∀ A∈P,∀ B∈P,A≠B->(A∩B).Nonempty:=by
  intro A hA B hB hAB;obtain⟨l,hl,hl'⟩:=hP.2 (Zc.mpr hA) (Zc.mpr hB) hAB;obtain⟨a,d,k,hk,-,hX⟩:=Qn (A∩B) l hl hl'
  exact⟨a,(hX a).mpr ⟨0,hk,by simp⟩⟩
 have hstep_ex:∀ A∈P,∃ d:ℕ,1≤ d/\d≤ N/\∃ x₀ k,2≤ k/\∀ x,x∈A↔∃ i< k,x=x₀+i*d:=by
  intro A hA;obtain⟨⟨a,d,k,hk,hdk,hX⟩,h2⟩:=hAP A hA
  have hk2:2≤ k:=by rwa[Qo hk hdk hX] at h2
  have hd1:1≤ d:=hdk (by omega)
  have hmm:=Wa hk hdk hX;have ha1:=Zb.mp (hsub A hA hmm.1);have hb1:=Zb.mp (hsub A hA hmm.2.1)
  have hdN:d≤ N:=by
   have:d≤(k-1)*d:=Nat.le_mul_of_pos_left d (by omega)
   omega
  exact⟨d,hd1,hdN,a,k,hk2,hX⟩
 let step:Zf ℕ->ℕ:=fun A=>if hA:A∈P then (hstep_ex A hA).choose else 0
 have hstep:∀ A∈P,1≤ step A/\step A≤ N/\∃ x₀ k,2≤ k/\∀ x,x∈A↔∃ i< k,x=x₀+i*step A:=by intro A hA;simpa [step,dif_pos hA] using (hstep_ex A hA).choose_spec
 have hpart:P.card=∑ d∈Icc 1 N,(P.filter (fun A=>step A=d)).card:=by
  rw[←card_biUnion]
  ·congr 1;ext A
   simp only[mem_biUnion,Zb,Za]
   constructor
   ·intro hA;obtain⟨h1,h2,-⟩:=hstep A hA;exact⟨step A,⟨h1,h2⟩,hA,rfl⟩
   ·rintro⟨_,_,hA,_⟩;exact hA
  ·intro d₁ _ d₂ _ hne
   simp only[Function.onFun];rw[Zk];intro A h1 h2;exact hne ((Za.mp h1).2.symm.trans (Za.mp h2).2)
 have hper_d:∀ d∈Icc 1 N,((P.filter (fun A=>step A=d)).card:ℝ) ≤(N:ℝ)^2/(4*(d:ℝ)^2)+4*(N:ℝ)/(d:ℝ)+4:=by
  intro d hd;have hd1:=(Zb.mp hd).1
  have hbd:=Ws 1 N d 0 hd1 hN (P.filter (fun A=>step A=d))
   (fun A hA=>hsub A (Za.mp hA).1)
   (fun A hA=>by
    obtain⟨hAP',heq⟩:=Za.mp hA;obtain⟨-,-,x₀,k,hk2,hX⟩:=hstep A hAP';rw[heq] at hX;exact⟨x₀,k,hk2,Nat.zero_le _,hX⟩)
   (fun A hA B hB hAB=>hmeet A (Za.mp hA).1 B (Za.mp hB).1 hAB)
  have hN1:(((N-1:ℕ):ℝ)/(d:ℝ))≤(N:ℝ)/(d:ℝ) :=div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le N 1) (by positivity)
  have hf1:=Xr (((N-1:ℕ):ℝ)/(d:ℝ)) 0 (by positivity) le_rfl
  have hsq:(((N-1:ℕ):ℝ)/(d:ℝ))^2/4≤(N:ℝ)^2/(4*(d:ℝ)^2):=by
   have h1:(((N-1:ℕ):ℝ)/(d:ℝ))^2≤((N:ℝ)/(d:ℝ))^2 :=pow_le_pow_left₀ (by positivity) hN1 2
   have h2:((N:ℝ)/(d:ℝ))^2/4=(N:ℝ)^2/(4*(d:ℝ)^2):=by ring
   linarith
  have h4:4*((N:ℝ)/(d:ℝ))=4*(N:ℝ)/(d:ℝ):=by ring
  linarith
 have hsum_main:∑ d∈Icc 1 N,(N:ℝ)^2/(4*(d:ℝ)^2) ≤(4125/10000:ℝ)*(N:ℝ)^2:=by
  have hsub:Icc 1 N⊆({1,2}:Zf ℕ)∪Icc 3 N:=by intro d hd;simp only[Zb,Zd,Zx,Zj] at hd ⊢;omega
  have hdisj:Disjoint ({1,2}:Zf ℕ) (Icc 3 N):=by
   rw[Zk];intro d h1 h2;simp only[Zx,Zj] at h1
   have:=(Zb.mp h2).1;omega
  have hge3:=V0 N
  have h3N:∑ d∈Icc 3 N,(N:ℝ)^2/(4*(d:ℝ)^2) =(N:ℝ)^2*∑ d∈Icc 3 N,(1:ℝ)/(4*(d:ℝ)^2):=by
   rw[Finset.mul_sum];refine Finset.sum_congr rfl fun d _=>?_;ring
  calc ∑ d∈Icc 1 N,(N:ℝ)^2/(4*(d:ℝ)^2)
      ≤ ∑ d∈({1,2}:Zf ℕ)∪Icc 3 N,(N:ℝ)^2/(4*(d:ℝ)^2) :=sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _=>by positivity)
    _=(∑ d∈({1,2}:Zf ℕ),(N:ℝ)^2/(4*(d:ℝ)^2)) +
          ∑ d∈Icc 3 N,(N:ℝ)^2/(4*(d:ℝ)^2):=Finset.sum_union hdisj
    _≤(4125/10000:ℝ)*(N:ℝ)^2:=by
        rw[sum_pair (by omega),h3N]
        nlinarith[sq_nonneg (N:ℝ)]
 have hsum_err1:∑ d∈Icc 1 N,4*(N:ℝ)/(d:ℝ)≤4*(N:ℝ)*(log (N:ℝ)+1):=by
  have heq:∑ d∈Icc 1 N,4*(N:ℝ)/(d:ℝ) =4*(N:ℝ)*∑ d∈Icc 1 N,(1:ℝ)/(d:ℝ):=by
   rw[Finset.mul_sum];refine Finset.sum_congr rfl fun d _=>?_;ring
  rw[heq]
  exact Zp (Q0 N hN) (by positivity)
 have hsum_err2:∑ _d∈Icc 1 N,(4:ℝ)=4*(N:ℝ):=by rw[Finset.sum_const,Nat.card_Icc,nsmul_eq_mul];simp;ring
 have hpartR:(P.card:ℝ)=∑ d∈Icc 1 N,((P.filter (fun A=>step A=d)).card:ℝ):=by exact_mod_cast hpart
 have hlog_nn:0≤ log (N:ℝ):=Real.log_nonneg (by exact_mod_cast hN)
 calc (P.card:ℝ)
     = ∑ d∈Icc 1 N,((P.filter (fun A=>step A=d)).card:ℝ):=hpartR
   _≤∑ d∈Icc 1 N,((N:ℝ)^2/(4*(d:ℝ)^2)+4*(N:ℝ)/(d:ℝ)+4) :=
       Finset.sum_le_sum hper_d
   _=(∑ d∈Icc 1 N,(N:ℝ)^2/(4*(d:ℝ)^2)) +
       (∑ d∈Icc 1 N,4*(N:ℝ)/(d:ℝ)) +
       ∑ _d∈Icc 1 N,(4:ℝ):=by
       rw[Finset.sum_add_distrib,Finset.sum_add_distrib]
   _≤(4125/10000:ℝ)*(N:ℝ)^2+12*(N:ℝ)*(log (N:ℝ)+2):=by
       nlinarith
noncomputable def Qb (S:Zf ℕ):Zf (Zf ℕ) :=letI:=Classical.propDecidable
 (S.powersetCard 3).filter (fun t=>∀ A∈S.powerset,IsAP A->¬ (t⊆A))
lemma Qh (S t:Zf ℕ):t∈Qb S↔Qk S t:=by
 classical
 unfold Qb Qk;simp only[Za,Zz,Zy]
 constructor
 ·rintro⟨⟨hsub,hcard⟩,hno⟩
  exact⟨hcard,hsub,fun A hAP hAS=>hno A hAS hAP⟩
 ·rintro⟨hcard,hsub,hno⟩
  exact⟨⟨hsub,hcard⟩,fun A hAS hAP=>hno A hAP hAS⟩
noncomputable def Qc (S:Zf ℕ):ℕ :=letI:=Classical.propDecidable
 ((S.powerset.filter IsAP).image card).max.unbotD 0
lemma Wo (S:Zf ℕ) (hne:S.Nonempty) :∃ P⊆S,IsAP P/\P.card=Qc S/\∀ A⊆S,IsAP A->A.card≤ Qc S:=by
 classical
 let APs:=S.powerset.filter IsAP
 have hAPne:APs.Nonempty:=by
  obtain⟨x,hx⟩:=hne
  exact⟨{x},Za.mpr ⟨Zy.mpr (singleton_subset_iff.mpr hx),W4 ⟨x,mem_singleton_self x⟩ (by simp)⟩⟩
 obtain⟨P,hP,hPmax⟩:=exists_max_image APs card hAPne
 have hmax_eq:(APs.image card).max=(P.card:WithBot ℕ):=by
  refine le_antisymm ?_ ?_
  ·rw[Finset.max_le_iff]
   intro c hc;obtain⟨A,hA,rfl⟩:=Zi.mp hc;exact WithBot.coe_le_coe.mpr (hPmax A hA)
  ·exact Finset.le_max (mem_image_of_mem card hP)
 have hdef:Qc S=P.card:=by
  have h1:WithBot.unbotD 0 (APs.image card).max=P.card:=by rw[hmax_eq];rfl
  rw[←h1];unfold Qc;congr 2;ext x;simp[APs]
 obtain⟨hPsub,hPAP⟩:=Za.mp hP
 refine⟨P,Zy.mp hPsub,hPAP,hdef.symm,fun A hAS hAAP=>?_⟩
 rw[hdef];exact hPmax A (Za.mpr ⟨Zy.mpr hAS,hAAP⟩)
lemma Vu (S:Zf ℕ) (h2:2≤ S.card) :(S.card-1)*(S.card-Qc S)≤2*(Qb S).card:=by
 set m:=S.card;set p:=Qc S
 let e:Fin m ↪o ℕ:=S.orderEmbOfFin rfl
 have he_mem:∀ i:Fin m,e i∈S:=fun i=>orderEmbOfFin_mem S rfl i
 have he_adj:∀ i:Fin (m-1),∀ w∈S,¬ (min (e ⟨i.1,by omega⟩) (e ⟨i.1+1,by omega⟩)< w ∧
    w< max (e ⟨i.1,by omega⟩) (e ⟨i.1+1,by omega⟩)):=by
  intro i w hw hbtw
  have hlt:e ⟨i.1,by omega⟩< e ⟨i.1+1,by omega⟩:=e.strictMono (by simp[Fin.lt_def])
  rw[Yl hlt.le,Yi hlt.le] at hbtw
  obtain⟨j,hj⟩:∃ j:Fin m,e j=w:=by
   have:w∈Set.range e:=by rw[range_orderEmbOfFin];exact hw
   exact this
  rw[←hj] at hbtw
  have h1:(⟨i.1,by omega⟩:Fin m)< j:=e.lt_iff_lt.mp hbtw.1
  have h2':j<(⟨i.1+1,by omega⟩:Fin m):=e.lt_iff_lt.mp hbtw.2
  simp only[Fin.lt_def] at h1 h2';omega
 let Pairs:=(univ:Zf (Fin (m-1))).biUnion (fun i =>
  let z:=e ⟨i.1,by omega⟩
  let u:=e ⟨i.1+1,by omega⟩
  (S \ Qf S z (u-z)).image (fun v=>(i,({z,u,v}:Zf ℕ))))
 have hPairs_ge:(m-1)*(m-p)≤ Pairs.card:=by
  rw[card_biUnion]
  ·calc (m-1)*(m-p)=∑ _i:Fin (m-1),(m-p):=by
          rw[Finset.sum_const,card_fin,smul_eq_mul]
      _≤∑ i:Fin (m-1),
            ((S \ Qf S (e ⟨i.1,by omega⟩) (e ⟨i.1+1,by omega⟩-e ⟨i.1,by omega⟩)).image
              (fun v=>(i,({e ⟨i.1,by omega⟩,e ⟨i.1+1,by omega⟩,v}:Zf ℕ)))).card:=by
          refine Finset.sum_le_sum fun i _=>?_
          set z:=e ⟨i.1,by omega⟩
          set u:=e ⟨i.1+1,by omega⟩
          have hzS:z∈S:=he_mem ⟨i.1,by omega⟩
          have huS:u∈S:=he_mem ⟨i.1+1,by omega⟩
          have hlt:z< u:=e.strictMono (by simp[Fin.lt_def])
          have hR_ap:IsAP (Qf S z (u-z)):=Wh (by omega) hzS
          have hR_le:(Qf S z (u-z)).card≤ p:=by obtain⟨-,-,-,-,hmax⟩:=Wo S ⟨z,hzS⟩;exact hmax _ (Qz S z (u-z)) hR_ap
          have hsdiff:(S \ Qf S z (u-z)).card≥m-p:=by have h1:=Yb (Qz S z (u-z));omega
          rw[card_image_of_injOn]
          · exact hsdiff
          · intro v₁ hv₁ v₂ hv₂ hpair
            have heqt:({z,u,v₁}:Zf ℕ)={z,u,v₂}:=congrArg Prod.snd hpair;have hv₁_not:v₁∉Qf S z (u-z):=(Ye.mp (Zc.mp hv₁)).2;have hv₂_not:v₂∉Qf S z (u-z):=(Ye.mp (Zc.mp hv₂)).2
            have hne_z1:v₁≠z:=fun h=>hv₁_not (h ▸ Q4 hzS _)
            have hne_u1:v₁≠u:=by
              intro h;subst h;have hbad:=Wp hzS huS huS (ne_of_lt hlt) (he_adj i);rw[Yl hlt.le,Yi hlt.le] at hbad;have hc:=(hbad hv₁_not).1
              have:({z,u,u}:Zf ℕ)={z,u}:=by ext x;simp
              rw[this] at hc
              have:({z,u}:Zf ℕ).card≤2:=(card_insert_le _ _).trans (by simp)
              omega
            have hv1_in:v₁∈({z,u,v₂}:Zf ℕ):=by rw[←heqt];simp
            simp only[Zx,Zj] at hv1_in
            rcases hv1_in with rfl|rfl|rfl
            · exact absurd rfl hne_z1
            · exact absurd rfl hne_u1
            · rfl
  ·intro i₁ _ i₂ _ hne
   simp only[Function.onFun];rw[Zk];intro p hp1 hp2;obtain⟨_,_,rfl⟩:=Zi.mp hp1;obtain⟨_,_,hpair⟩:=Zi.mp hp2;exact hne (congrArg Prod.fst hpair).symm
 have hPairs_le:Pairs.card≤2*(Qb S).card:=by
  have hsubP:Pairs⊆(Qb S).biUnion (fun t =>
    ((univ:Zf (Fin (m-1))).filter
     (fun i=>e ⟨i.1,by omega⟩∈t/\e ⟨i.1+1,by omega⟩∈t)).image (fun i=>(i,t))):=by
   intro ⟨i,t⟩ hit;obtain⟨j,-,ht⟩:=mem_biUnion.mp hit;obtain⟨v,hv,hpair⟩:=Zi.mp ht
   rcases Prod.mk.inj hpair with ⟨rfl,rfl⟩
   set z:=e ⟨j.1,by omega⟩
   set u:=e ⟨j.1+1,by omega⟩
   have hlt:z< u:=e.strictMono (by simp[Fin.lt_def])
   obtain⟨hvS,hvR⟩:=Ye.mp hv
   have hbad:Qk S {z,u,v}:=by
    have h:=Wp (he_mem ⟨j.1,by omega⟩) (he_mem ⟨j.1+1,by omega⟩)
     hvS (ne_of_lt hlt) (he_adj j)
    rw[Yl hlt.le,Yi hlt.le] at h;exact h hvR
   refine mem_biUnion.mpr ⟨{z,u,v},(Qh S _).mpr hbad,Zi.mpr ⟨j,Za.mpr ⟨mem_univ _,by simp[z],by simp[u]⟩,rfl⟩⟩
  calc Pairs.card≤((Qb S).biUnion (fun t =>
          ((univ:Zf (Fin (m-1))).filter
            (fun i=>e ⟨i.1,by omega⟩∈t/\e ⟨i.1+1,by omega⟩∈t)).image (fun i=>(i,t)))).card :=
        Zm hsubP
    _≤∑ t∈Qb S,(((univ:Zf (Fin (m-1))).filter
          (fun i=>e ⟨i.1,by omega⟩∈t/\e ⟨i.1+1,by omega⟩∈t)).image (fun i=>(i,t))).card :=
        card_biUnion_le
    _≤∑ t∈Qb S,2:=by
        refine Finset.sum_le_sum fun t ht=>?_
        refine card_image_le.trans ?_
        have ht3:t.card=3:=((Qh S t).mp ht).1
        let I:=(univ:Zf (Fin (m-1))).filter
          (fun i=>e ⟨i.1,by omega⟩∈t/\e ⟨i.1+1,by omega⟩∈t)
        have hne_t:t.Nonempty:=card_pos.mp (by omega)
        have hmaps:Set.MapsTo (fun i:Fin (m-1)=>e ⟨i.1,by omega⟩)
            (I:Set (Fin (m-1))) ((t.erase (t.max' hne_t)):Set ℕ):=by
          intro i hi;obtain⟨-,h1,h2⟩:=Za.mp (Zc.mp hi)
          have hlt:e ⟨i.1,by omega⟩< e ⟨i.1+1,by omega⟩:=e.strictMono (by simp[Fin.lt_def])
          have hle:e ⟨i.1+1,by omega⟩≤ t.max' hne_t:=le_max' t _ h2
          dsimp only
          exact Zc.mpr (Zw.mpr ⟨by omega,h1⟩)
        have hinj:Set.InjOn (fun i:Fin (m-1)=>e ⟨i.1,by omega⟩) (I:Set (Fin (m-1))):=by
          intro i _ j _ heq;have hfin:=e.injective heq;exact Fin.ext (congrArg (Fin.val:Fin m->ℕ) hfin)
        calc I.card≤(t.erase (t.max' hne_t)).card:=card_le_card_of_injOn _ hmaps hinj
          _=2:=by rw[card_erase_of_mem (max'_mem t hne_t),ht3]
    _=2*(Qb S).card:=by rw[Finset.sum_const,smul_eq_mul,mul_comm]
 omega
lemma Xf (A:Zf ℕ) :2*((A ×ˢ A).filter (fun z=>z.1< z.2)).card=A.card*(A.card-1):=by
 set S1:=(A ×ˢ A).filter (fun z=>z.1< z.2)
 set S2:=(A ×ˢ A).filter (fun z=>z.2< z.1)
 have heq':S2.card=S1.card:=by
  refine card_bij (fun z _=>(z.2,z.1)) ?_ ?_ ?_
  ·intro z hz;obtain⟨hP',hlt⟩:=Za.mp hz
   obtain⟨hx,hy⟩:=Zh.mp hP';exact Za.mpr ⟨Zh.mpr ⟨hy,hx⟩,hlt⟩
  ·intro z _ w _ h;ext <;> [exact congrArg Prod.snd h;exact congrArg Prod.fst h]
  ·intro z hz;obtain⟨hP',hlt⟩:=Za.mp hz
   obtain⟨hx,hy⟩:=Zh.mp hP';exact⟨(z.2,z.1),Za.mpr ⟨Zh.mpr ⟨hy,hx⟩,hlt⟩,rfl⟩
 have hdisj:Disjoint S1 S2:=by
  rw[Zk];intro z h1 h2
  have:=(Za.mp h1).2;have:=(Za.mp h2).2;omega
 have hunion:S1∪S2=(A ×ˢ A).filter (fun z=>¬ (z.1=z.2)):=by
  ext z;simp only[S1,S2,Zd,Za];constructor
  ·rintro (⟨h1,h2⟩|⟨h1,h2⟩) <;> exact⟨h1,by omega⟩
  ·rintro⟨h1,h2⟩;rcases lt_or_gt_of_ne h2 with h|h
   ·exact Or.inl ⟨h1,h⟩
   ·exact Or.inr ⟨h1,h⟩
 have hdiag:((A ×ˢ A).filter (fun z=>z.1=z.2)).card=A.card:=by
  refine card_bij (fun z _=>z.1) ?_ ?_ ?_
  ·intro z hz;exact (Zh.mp (Za.mp hz).1).1
  ·intro z hz w hw hzw
   have e1:=(Za.mp hz).2;have e2:=(Za.mp hw).2
   ext <;> omega
  ·intro x hx;exact⟨(x,x),Za.mpr ⟨Zh.mpr ⟨hx,hx⟩,rfl⟩,rfl⟩
 have hpart:=card_filter_add_card_filter_not (s:=A ×ˢ A) (p:=fun z=>z.1=z.2)
 rw[hdiag,card_product,←hunion,Zq hdisj,heq'] at hpart
 have hmul:A.card*(A.card-1)+A.card=A.card*A.card:=by
  rcases Nat.eq_zero_or_pos A.card with h0|hpos
  ·simp[h0]
  ·obtain⟨t,ht⟩:∃ t,A.card=t+1:=⟨A.card-1,by omega⟩
   rw[ht];simp only[Nat.add_sub_cancel];ring
 omega
lemma Wy (r:ℕ) (hr:10≤ r)
  (P:Zf ℕ) (hP:P⊆Icc 2 (r-1))
  (res:ℕ->ℕ) :
  (((range r ×ˢ range r).filter (fun z =>
   z.1< z.2/\∃ p∈P,z.1 % p=res p/\z.2 % p=res p)).card:ℝ) ≤
   (3/8:ℝ)*(r:ℝ)^2+(r:ℝ)*(log (r:ℝ)+2):=by
 set Bad:=(range r ×ˢ range r).filter (fun z =>
  z.1< z.2/\∃ p∈P,z.1 % p=res p/\z.2 % p=res p)
 have hsub:Bad⊆P.biUnion (fun p =>
   (range r ×ˢ range r).filter (fun z=>z.1< z.2/\z.1 % p=res p/\z.2 % p=res p)):=by
  intro z hz;obtain⟨hzR,hlt,p,hp,h1,h2⟩:=Za.mp hz;exact mem_biUnion.mpr ⟨p,hp,Za.mpr ⟨hzR,hlt,h1,h2⟩⟩
 have hper_p:∀ p∈P,((((range r ×ˢ range r).filter
    (fun z=>z.1< z.2/\z.1 % p=res p/\z.2 % p=res p)).card:ℝ)) ≤
    (r:ℝ)^2/(2*(p:ℝ)^2)+(r:ℝ)/(2*(p:ℝ)):=by
  intro p hp;have hp2:2≤ p:=(Zb.mp (hP hp)).1
  set C:=(range r).filter (fun x=>x % p=res p)
  have hC_card:C.card≤ r/p+1:=by
   have hinj:Set.InjOn (fun x=>x/p) (C:Set ℕ):=by intro x hx y hy hxy;dsimp only at hxy;have hm1:=(Za.mp (Zc.mp hx)).2;have hm2:=(Za.mp (Zc.mp hy)).2;have e1:=Nat.div_add_mod x p;have e2:=Nat.div_add_mod y p;rw[hxy,hm1,←hm2] at e1;omega
   have hmaps:Set.MapsTo (fun x=>x/p) (C:Set ℕ) ((range (r/p+1):Zf ℕ):Set ℕ):=by
    intro x hx;have hxr:=mem_range.mp (Za.mp (Zc.mp hx)).1
    exact Zc.mpr (mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right (by omega:x≤ r))))
   exact (card_le_card_of_injOn _ hmaps hinj).trans (by rw[card_range])
  set Tri:=(range r ×ˢ range r).filter (fun z=>z.1< z.2/\z.1 % p=res p/\z.2 % p=res p)
  have hsubC:Tri⊆(C ×ˢ C).filter (fun z=>z.1< z.2):=by
   intro z hz;obtain⟨hP',hlt,m1,m2⟩:=Za.mp hz;obtain⟨hx,hy⟩:=Zh.mp hP'
   exact Za.mpr ⟨Zh.mpr
    ⟨Za.mpr ⟨hx,m1⟩,Za.mpr ⟨hy,m2⟩⟩,hlt⟩
  have h2Tri:2*Tri.card≤ C.card*(C.card-1):=by
   calc 2*Tri.card≤2*((C ×ˢ C).filter (fun z=>z.1< z.2)).card :=
         Yd 2 (Zm hsubC)
     _=C.card*(C.card-1):=Xf C
  have h2Tri':2*Tri.card≤(r/p+1)*(r/p) :=h2Tri.trans (Nat.mul_le_mul hC_card (Nat.sub_le_of_le_add hC_card))
  have hR:2*(Tri.card:ℝ)≤((r:ℝ)/(p:ℝ)+1)*((r:ℝ)/(p:ℝ)):=by
   have hcast:2*(Tri.card:ℝ)≤(((r/p:ℕ):ℝ)+1)*((r/p:ℕ):ℝ):=by exact_mod_cast h2Tri'
   have hdiv:((r/p:ℕ):ℝ)≤(r:ℝ)/(p:ℝ):=Nat.cast_div_le;nlinarith[Nat.cast_nonneg (α:=ℝ) (r/p)]
  have halg:((r:ℝ)/(p:ℝ)+1)*((r:ℝ)/(p:ℝ)) =2*((r:ℝ)^2/(2*(p:ℝ)^2)+(r:ℝ)/(2*(p:ℝ))):=by ring
  linarith
 have hBad_sum:(Bad.card:ℝ)≤∑ p∈Icc 2 (r-1),((r:ℝ)^2/(2*(p:ℝ)^2)+(r:ℝ)/(2*(p:ℝ))):=by
  calc (Bad.card:ℝ)
      ≤ ∑ p∈P,((((range r ×ˢ range r).filter
          (fun z=>z.1< z.2/\z.1 % p=res p/\z.2 % p=res p)).card:ℝ)):=by
        exact_mod_cast (Zm hsub).trans card_biUnion_le
    _≤∑ p∈P,((r:ℝ)^2/(2*(p:ℝ)^2)+(r:ℝ)/(2*(p:ℝ))) :=
        Finset.sum_le_sum hper_p
    _≤∑ p∈Icc 2 (r-1),((r:ℝ)^2/(2*(p:ℝ)^2)+(r:ℝ)/(2*(p:ℝ))) :=
        sum_le_sum_of_subset_of_nonneg hP (fun _ _ _=>by positivity)
 have hsq_sum:∑ p∈Icc 2 (r-1),(1:ℝ)/(p:ℝ)^2≤3/4:=by
  have hdisj:Disjoint ({2}:Zf ℕ) (Icc 3 (r-1)):=by rw[Zk];intro p h1 h2;simp only[Zj] at h1;have:=(Zb.mp h2).1;omega
  have hsub2:Icc 2 (r-1)⊆({2}:Zf ℕ)∪Icc 3 (r-1):=by intro p hp;simp only[Zb,Zd,Zj] at hp ⊢;omega
  have htail:=Vc 2 (r-1) (by omega)
  calc ∑ p∈Icc 2 (r-1),(1:ℝ)/(p:ℝ)^2
      ≤ ∑ p∈({2}:Zf ℕ)∪Icc 3 (r-1),(1:ℝ)/(p:ℝ)^2 :=sum_le_sum_of_subset_of_nonneg hsub2 (fun _ _ _=>by positivity)
    _=(1:ℝ)/(2:ℝ)^2+∑ p∈Icc 3 (r-1),(1:ℝ)/(p:ℝ)^2:=by
        rw[Finset.sum_union hdisj,Finset.sum_singleton];push_cast;rfl
    _≤3/4:=by norm_num at htail ⊢;linarith
 have hharm:∑ p∈Icc 2 (r-1),(1:ℝ)/(p:ℝ)≤ log (r:ℝ)+1:=by
  refine (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _=>by positivity)).trans
   (Q0 r (by omega))
  intro p hp;simp only[Zb] at hp ⊢;omega
 rw[Finset.sum_add_distrib] at hBad_sum
 have hf1:∑ p∈Icc 2 (r-1),(r:ℝ)^2/(2*(p:ℝ)^2) =((r:ℝ)^2/2)*∑ p∈Icc 2 (r-1),(1:ℝ)/(p:ℝ)^2:=by
  rw[Finset.mul_sum];refine Finset.sum_congr rfl fun p _=>?_;ring
 have hf2:∑ p∈Icc 2 (r-1),(r:ℝ)/(2*(p:ℝ)) =((r:ℝ)/2)*∑ p∈Icc 2 (r-1),(1:ℝ)/(p:ℝ):=by
  rw[Finset.mul_sum];refine Finset.sum_congr rfl fun p _=>?_;ring
 rw[hf1,hf2] at hBad_sum;have hr_nn:(0:ℝ)≤(r:ℝ):=Nat.cast_nonneg r
 have hlog_nn:0≤ log (r:ℝ):=Real.log_nonneg (by exact_mod_cast (by omega:1≤ r))
 nlinarith
private lemma Vv {p₀ K i:ℕ} (hp₀:0< p₀) (hdvd:p₀ ∣ K+i) :i % p₀=(p₀-K % p₀) % p₀:=by
 have hsum0:(K+i) % p₀=0:=Nat.mod_eq_zero_of_dvd hdvd
 have h1:(K % p₀+i % p₀) % p₀=0:=by rwa[Nat.add_mod] at hsum0
 have h2:=Nat.mod_lt K hp₀;have h3:=Nat.mod_lt i hp₀
 rcases Nat.eq_zero_or_pos (K % p₀) with hK0|hKpos
 ·rw[hK0] at h1 ⊢
  simp only[Nat.sub_zero,Nat.mod_self,zero_add] at h1 ⊢;rw[Nat.mod_eq_of_lt h3] at h1;exact h1
 ·have hsum_eq:K % p₀+i % p₀=p₀:=by
   have hlt2:K % p₀+i % p₀<2*p₀:=by omega
   have hdiv:=Nat.div_add_mod (K % p₀+i % p₀) p₀;rw[h1,add_zero] at hdiv
   have hq1:(K % p₀+i % p₀)/p₀=1:=by
    rcases lt_trichotomy ((K % p₀+i % p₀)/p₀) 1 with hlt|heq|hgt
    ·rw[Nat.lt_one_iff.mp hlt,mul_zero] at hdiv;omega
    ·exact heq
    ·have:2*p₀≤ p₀*((K % p₀+i % p₀)/p₀):=by nlinarith
     omega
   rw[hq1,mul_one] at hdiv;exact hdiv.symm
  have hsub_lt:p₀-K % p₀< p₀:=Nat.sub_lt hp₀ hKpos;rw[Nat.mod_eq_of_lt hsub_lt];exact Nat.eq_sub_of_add_eq' hsum_eq
private lemma X7 {S P:Zf ℕ} {a d p q w:ℕ}
  (hPS:P⊆S) (hPcard:P.card=p) (hPmax:∀ A⊆S,IsAP A->A.card≤ p)
  (hPeq:∀ x,x∈P↔∃ i< p,x=a+i*d)
  (hm:5100≤ S.card) (hq_def:q=S.card-p) (hq2:100*q< S.card)
  (hd_pos:0< d) (hwS:w∈S) (hwP:w∉P) (hmod:w % d=a % d) :
  S.card^2≤100*((Qb S).filter (fun t=>w∈t/\(t.erase w)⊆P)).card:=by
 set m:=S.card
 have hp_big:5049≤ p:=by omega
 set Q:=S \ P
 have hQcard:Q.card=q:=by have h1:Q.card+P.card=m:=Yb hPS;omega
 have hw_not_in_range:w< a\/a+p*d< w:=by
  by_contra h
  push Not at h
  have hdvd:d ∣ w-a:=(Nat.modEq_iff_dvd' h.1).mp hmod.symm;obtain⟨i,hi⟩:=hdvd
  have hwi:w=a+i*d:=by rw[Nat.mul_comm];omega
  rcases lt_or_ge i p with hilt|hige
  ·exact hwP ((hPeq w).mpr ⟨i,hilt,hwi⟩)
  ·have hip:i=p:=by
    have:i*d≤ p*d:=by omega
    have:=Nat.le_of_mul_le_mul_right this hd_pos
    omega
   have hP1:IsAP (insert w P):=by
    refine⟨a,d,p+1,by omega,fun _=>hd_pos,fun x=>?_⟩
    rw[Zx,hPeq]
    constructor
    ·rintro (rfl|⟨j,hj,rfl⟩)
     ·exact⟨p,by omega,by rw[hwi,hip]⟩
     ·exact⟨j,by omega,rfl⟩
    ·rintro⟨j,hj,rfl⟩
     rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hj) with hjlt|rfl
     ·exact Or.inr ⟨j,hjlt,rfl⟩
     ·exact Or.inl (by rw[hwi,hip])
   have hcard1:(insert w P).card=p+1:=by rw[card_insert_of_notMem hwP,hPcard]
   have hle:=hPmax (insert w P) (insert_subset_iff.mpr ⟨hwS,hPS⟩) hP1;omega
 set Clean:=(range p).filter (fun i =>
  ∀ u∈Q,¬ (a+i*d< u/\u< a+(i+1)*d))
 have hClean_card:p-q≤ Clean.card:=by
  set Dirty:=(range p).filter (fun i =>
   ∃ u∈Q,a+i*d< u/\u< a+(i+1)*d)
  have hDirty_le:Dirty.card≤ Q.card:=by
   have hch:∀ i∈Dirty,∃ u∈Q,a+i*d< u/\u< a+(i+1)*d:=by intro i hi;exact (Za.mp hi).2
   let fu:ℕ->ℕ:=fun i=>if hi:i∈Dirty then (hch i hi).choose else 0
   have hfu:∀ i∈Dirty,fu i∈Q/\a+i*d< fu i/\fu i< a+(i+1)*d:=by intro i hi;simpa [fu,dif_pos hi] using (hch i hi).choose_spec
   refine card_le_card_of_injOn fu (fun i hi=>Zc.mpr (hfu i (Zc.mp hi)).1) ?_
   intro i₁ hi₁ i₂ hi₂ heq;have h1:=hfu i₁ (Zc.mp hi₁);have h2:=hfu i₂ (Zc.mp hi₂);rw[heq] at h1
   have hlt1:i₁*d<(i₂+1)*d:=by omega
   have hlt2:i₂*d<(i₁+1)*d:=by omega
   have hle1:i₁< i₂+1:=Nat.lt_of_mul_lt_mul_right hlt1;have hle2:i₂< i₁+1:=Nat.lt_of_mul_lt_mul_right hlt2;omega
  have heqD:(range p).filter (fun i=>¬ ∀ u∈Q,¬ (a+i*d< u/\u< a+(i+1)*d))=Dirty:=by ext i;simp[Dirty]
  have hpart:Clean.card+Dirty.card=p:=by
   have h0:=card_filter_add_card_filter_not (s:=range p)
    (p:=fun i=>∀ u∈Q,¬ (a+i*d< u/\u< a+(i+1)*d))
   rw[heqD,card_range] at h0;exact h0
  omega
 let K:ℕ:=if a+p*d< w then (w-a)/d else (a-w)/d
 let res:ℕ->ℕ:=fun p₀=>if a+p*d< w then K % p₀ else (p₀-K % p₀) % p₀
 have hK_eq:(a+p*d< w->w=a+K*d/\p< K) ∧
        (w< a->a=w+K*d/\2≤ K):=by
  constructor
  ·intro hgt
   have hKdef:K=(w-a)/d:=if_pos hgt
   obtain⟨t,ht⟩:=(Nat.modEq_iff_dvd' (by omega:a≤ w)).mp hmod.symm
   have ht_eq:K=t:=by rw[hKdef,ht,Nat.mul_div_cancel_left _ hd_pos]
   have ht_gt:p< t:=by
    have:p*d< t*d:=by rw[Nat.mul_comm t d];omega
    exact Nat.lt_of_mul_lt_mul_right this
   exact⟨by rw[ht_eq,Nat.mul_comm];omega,by omega⟩
  ·intro hlt
   have hKdef:K=(a-w)/d:=if_neg (by omega)
   obtain⟨t,ht⟩:=(Nat.modEq_iff_dvd' (by omega:w≤ a)).mp hmod
   have ht_eq:K=t:=by rw[hKdef,ht,Nat.mul_div_cancel_left _ hd_pos]
   have ht2:2≤ t:=by
    by_contra hlt2
    have ht01:t=0\/t=1:=by omega
    rcases ht01 with rfl|rfl
    ·omega
    ·have haw:a=w+d:=by simp only[mul_one] at ht;omega
     have hP1:IsAP (insert w P):=by
      refine⟨w,d,p+1,by omega,fun _=>hd_pos,fun x=>?_⟩
      rw[Zx,hPeq]
      constructor
      ·rintro (rfl|⟨j,hj,rfl⟩)
       ·exact⟨0,by omega,by simp⟩
       ·refine⟨j+1,by omega,?_⟩
        rw[haw];ring
      ·rintro⟨j,hj,rfl⟩
       rcases j with _|j
       ·exact Or.inl (by simp)
       ·refine Or.inr ⟨j,by omega,?_⟩
        rw[haw];ring
     have hcard1:(insert w P).card=p+1:=by rw[card_insert_of_notMem hwP,hPcard]
     have hle:=hPmax (insert w P) (insert_subset_iff.mpr ⟨hwS,hPS⟩) hP1;omega
   exact⟨by rw[ht_eq,Nat.mul_comm];omega,by omega⟩
 have hgood_aligned:∀ i∈Clean,∀ j∈Clean,i< j →
   ¬ Qk S {w,a+i*d,a+j*d} →
   ∃ p₀∈(Icc 2 (p-1)).filter Nat.Prime,i % p₀=res p₀/\j % p₀=res p₀:=by
  intro i hi j hj hij hnotbad;have hiP:i< p:=mem_range.mp (Za.mp hi).1;have hjP:j< p:=mem_range.mp (Za.mp hj).1;have hxi:a+i*d∈S:=hPS ((hPeq _).mpr ⟨i,hiP,rfl⟩);have hxj:a+j*d∈S:=hPS ((hPeq _).mpr ⟨j,hjP,rfl⟩)
  have hne_wi:w≠a+i*d:=fun h=>hwP (h ▸ (hPeq _).mpr ⟨i,hiP,rfl⟩)
  have hne_wj:w≠a+j*d:=fun h=>hwP (h ▸ (hPeq _).mpr ⟨j,hjP,rfl⟩)
  have hne_ij:a+i*d≠a+j*d:=by
   have:i*d< j*d:=Nat.mul_lt_mul_of_pos_right hij hd_pos;omega
  have hcard3:({w,a+i*d,a+j*d}:Zf ℕ).card=3:=by
   rw[card_insert_of_notMem,card_insert_of_notMem,card_singleton]
   ·exact Finset.notMem_singleton.mpr hne_ij
   ·simp[hne_wi,hne_wj]
  have hsub3:({w,a+i*d,a+j*d}:Zf ℕ)⊆S:=by
   intro x hx;simp only[Zx,Zj] at hx
   rcases hx with rfl|rfl|rfl <;> assumption
  unfold Qk at hnotbad
  push Not at hnotbad
  obtain⟨A,⟨aA,δ,kA,hkA,hdA,hAeq⟩,hAS,htA⟩:=hnotbad hcard3 hsub3
  have hwA:w∈A:=htA (by simp)
  have hiA:a+i*d∈A:=htA (by simp)
  have hjA:a+j*d∈A:=htA (by simp)
  have hkA2:2≤ kA:=by
   have:3≤ A.card:=by rw[←hcard3];exact Zm htA
   rw[Qo hkA hdA hAeq] at this;omega
  have hδ_pos:0<δ:=hdA (by omega)
  obtain⟨iw,hiw,hweqA⟩:=(hAeq w).mp hwA;obtain⟨ii,hii,hieqA⟩:=(hAeq (a+i*d)).mp hiA;obtain⟨ij,hijA,hjeqA⟩:=(hAeq (a+j*d)).mp hjA
  have hii_lt_ij:ii< ij:=by
   have:a+i*d< a+j*d:=by
    have:=Nat.mul_lt_mul_of_pos_right hij hd_pos;omega
   have:ii*δ< ij*δ:=by omega
   exact Nat.lt_of_mul_lt_mul_right this
  have hdvd_ij:δ ∣ (j-i)*d:=by
   refine⟨ij-ii,?_⟩
   have:(j-i)*d=(a+j*d)-(a+i*d):=by rw[Nat.sub_mul];omega
   rw[this,hieqA,hjeqA]
   have:(aA+ij*δ)-(aA+ii*δ)=(ij-ii)*δ:=by rw[Nat.sub_mul];omega
   rw[this,mul_comm]
  have hδ'_ex:∃ δ':ℕ,2≤δ'/\δ' ∣ (j-i) ∧
    (a+p*d< w->δ' ∣ K-i)/\(w< a->δ' ∣ K+i):=by
   by_cases hdvd_d:d ∣ δ
   ·obtain⟨c,hc⟩:=hdvd_d
    have hc2:2≤ c:=by
     by_contra hlt2
     have hc1:c=1:=by
      rcases Nat.eq_zero_or_pos c with rfl|hcpos
      ·simp at hc;omega
      ·omega
     rw[hc1,mul_one] at hc
     have hAsubR:A⊆Qf S (a+i*d) d :=Qv hAS hd_pos (by rw[←hc];exact hAeq) hiA
     have hwR:w∈Qf S (a+i*d) d:=hAsubR hwA;have hPsubR:P⊆Qf S (a+i*d) d :=Qv hPS hd_pos hPeq ((hPeq _).mpr ⟨i,hiP,rfl⟩)
     have hcard_gt:p+1≤(Qf S (a+i*d) d).card:=by have h1:insert w P⊆Qf S (a+i*d) d:=insert_subset_iff.mpr ⟨hwR,hPsubR⟩;have h2:=Zm h1;rw[card_insert_of_notMem hwP,hPcard] at h2;exact h2
     have hle:=hPmax (Qf S (a+i*d) d) (Qz _ _ _) (Wh hd_pos hxi);omega
    refine⟨c,hc2,?_,?_,?_⟩
    ·rw[hc] at hdvd_ij
     obtain⟨t,ht⟩:=hdvd_ij
     exact⟨t,Nat.eq_of_mul_eq_mul_left hd_pos (by linarith)⟩
    ·intro hgt
     obtain⟨hwK,hKp⟩:=hK_eq.1 hgt
     have hδw:δ ∣ w-(a+i*d):=by
      have hltw:a+i*d< w:=by
       have:i*d< p*d:=Nat.mul_lt_mul_of_pos_right hiP hd_pos;omega
      have hlt_idx:ii< iw:=Nat.lt_of_mul_lt_mul_right (by omega:ii*δ< iw*δ)
      refine⟨iw-ii,?_⟩
      rw[hweqA,hieqA];have:aA+iw*δ-(aA+ii*δ)=(iw-ii)*δ:=by rw[Nat.sub_mul];omega
      rw[this,mul_comm]
     rw[hc,hwK] at hδw;obtain⟨t,ht⟩:=hδw
     have hsubK:a+K*d-(a+i*d)=(K-i)*d:=by rw[Nat.sub_mul];omega
     rw[hsubK] at ht
     exact⟨t,Nat.eq_of_mul_eq_mul_left hd_pos (by linarith)⟩
    ·intro hlt
     obtain⟨haK,-⟩:=hK_eq.2 hlt
     have hδw:δ ∣ (a+i*d)-w:=by
      have hlt_idx:iw< ii:=Nat.lt_of_mul_lt_mul_right (by omega:iw*δ< ii*δ)
      refine⟨ii-iw,?_⟩
      rw[hweqA,hieqA];have:aA+ii*δ-(aA+iw*δ)=(ii-iw)*δ:=by rw[Nat.sub_mul];omega
      rw[this,mul_comm]
     rw[hc,haK] at hδw;obtain⟨t,ht⟩:=hδw
     have haddK:w+K*d+i*d-w=(K+i)*d:=by rw[Nat.add_mul];omega
     rw[haddK] at ht
     exact⟨t,Nat.eq_of_mul_eq_mul_left hd_pos (by linarith)⟩
   ·have hstep_in:a+i*d+δ∈S:=by
     have hmemA:aA+(ii+1)*δ∈A:=(hAeq _).mpr ⟨ii+1,by omega,rfl⟩
     have heq_step:aA+(ii+1)*δ=a+i*d+δ:=by rw[hieqA];ring
     rw[←heq_step];exact hAS hmemA
    have hstep_notP:a+i*d+δ∉P:=by
     intro hmemP;obtain⟨i',-,hi'⟩:=(hPeq _).mp hmemP
     have hge:i≤ i':=Nat.le_of_mul_le_mul_right (by omega:i*d≤ i'*d) hd_pos
     have:δ=(i'-i)*d:=by rw[Nat.sub_mul];omega
     exact hdvd_d ⟨i'-i,by linarith⟩
    have hstep_inQ:a+i*d+δ∈Q:=Ye.mpr ⟨hstep_in,hstep_notP⟩
    have hδ_gt_d:d<δ:=by
     have hclean:=(Za.mp hi).2 (a+i*d+δ) hstep_inQ
     have hne_d:δ≠d:=fun h=>hdvd_d ⟨1,by omega⟩
     have hmul:a+(i+1)*d=a+i*d+d:=by ring
     rw[hmul] at hclean;omega
    set h:=Nat.gcd d δ;have hh_pos:0< h:=Nat.gcd_pos_of_pos_left δ hd_pos;have hh_le_d:h≤ d:=Nat.le_of_dvd hd_pos (Nat.gcd_dvd_left d δ);set δ':=δ/h;have hδ'h:δ'*h=δ:=Nat.div_mul_cancel (Nat.gcd_dvd_right d δ);have hdh:(d/h)*h=d:=Nat.div_mul_cancel (Nat.gcd_dvd_left d δ)
    have hδ'2:2≤δ':=by
     by_contra hlt2;have hlt2':δ'<2:=Nat.lt_of_not_ge hlt2
     rcases Nat.eq_zero_or_pos δ' with h0|hpos
     ·rw[h0] at hδ'h;omega
     ·have h1:δ'=1:=le_antisymm (Nat.lt_succ_iff.mp hlt2') hpos
      rw[h1,one_mul] at hδ'h;omega
    have hcop:Nat.Coprime δ' (d/h):=by rw[Nat.coprime_comm];exact Nat.coprime_div_gcd_div_gcd hh_pos
    refine⟨δ',hδ'2,?_,?_,?_⟩
    ·obtain⟨t,ht⟩:=hdvd_ij
     have hdvd1:δ' ∣ (j-i)*(d/h):=⟨t,Nat.eq_of_mul_eq_mul_right hh_pos (by
      calc ((j-i)*(d/h))*h=(j-i)*((d/h)*h):=by ring
        _=(j-i)*d:=by rw[hdh]
        _=δ*t:=ht
        _=(δ'*h)*t:=by rw[←hδ'h]
        _=(δ'*t)*h:=by ring)⟩
     exact hcop.dvd_of_dvd_mul_right hdvd1
    ·intro hgt
     obtain⟨hwK,hKp⟩:=hK_eq.1 hgt
     have hδw:δ ∣ (K-i)*d:=by
      have hltw:a+i*d< w:=by
       have:i*d< p*d:=Nat.mul_lt_mul_of_pos_right hiP hd_pos;omega
      have hlt_idx:ii< iw:=Nat.lt_of_mul_lt_mul_right (by omega:ii*δ< iw*δ)
      refine⟨iw-ii,?_⟩
      have h1:(K-i)*d=w-(a+i*d):=by rw[hwK,Nat.sub_mul];omega
      rw[h1,hweqA,hieqA]
      have h2:aA+iw*δ-(aA+ii*δ)=(iw-ii)*δ:=by rw[Nat.sub_mul];omega
      rw[h2,mul_comm]
     obtain⟨t,ht⟩:=hδw
     have hdvd1:δ' ∣ (K-i)*(d/h):=⟨t,Nat.eq_of_mul_eq_mul_right hh_pos (by
      calc ((K-i)*(d/h))*h=(K-i)*((d/h)*h):=by ring
        _=(K-i)*d:=by rw[hdh]
        _=δ*t:=ht
        _=(δ'*h)*t:=by rw[←hδ'h]
        _=(δ'*t)*h:=by ring)⟩
     exact hcop.dvd_of_dvd_mul_right hdvd1
    ·intro hlt
     obtain⟨haK,-⟩:=hK_eq.2 hlt
     have hδw:δ ∣ (K+i)*d:=by
      have hlt_idx:iw< ii:=Nat.lt_of_mul_lt_mul_right (by omega:iw*δ< ii*δ)
      refine⟨ii-iw,?_⟩
      have h1:(K+i)*d=(a+i*d)-w:=by rw[haK,Nat.add_mul];omega
      rw[h1,hweqA,hieqA]
      have h2:aA+ii*δ-(aA+iw*δ)=(ii-iw)*δ:=by rw[Nat.sub_mul];omega
      rw[h2,mul_comm]
     obtain⟨t,ht⟩:=hδw
     have hdvd1:δ' ∣ (K+i)*(d/h):=⟨t,Nat.eq_of_mul_eq_mul_right hh_pos (by
      calc ((K+i)*(d/h))*h=(K+i)*((d/h)*h):=by ring
        _=(K+i)*d:=by rw[hdh]
        _=δ*t:=ht
        _=(δ'*h)*t:=by rw[←hδ'h]
        _=(δ'*t)*h:=by ring)⟩
     exact hcop.dvd_of_dvd_mul_right hdvd1
  obtain⟨δ',hδ'2,hδ'ij,hδ'gt,hδ'lt⟩:=hδ'_ex;set p₀:=δ'.minFac
  have hp₀_pr:p₀.Prime:=Nat.minFac_prime (by omega)
  have hp₀_dvd:p₀ ∣ δ':=Nat.minFac_dvd δ';have hp₀_ij:p₀ ∣ j-i:=hp₀_dvd.trans hδ'ij
  have hp₀_le:p₀≤ p-1:=(Nat.le_of_dvd (by omega:0< j-i) hp₀_ij).trans (by omega)
  have hmod_ij:i % p₀=j % p₀:=(Nat.modEq_iff_dvd' (le_of_lt hij)).mpr hp₀_ij
  have hi_res:i % p₀=res p₀:=by
   rcases hw_not_in_range with hlt|hgt
   ·rw[show res p₀=(p₀-K % p₀) % p₀ from if_neg (by omega)]
    exact Vv hp₀_pr.pos (hp₀_dvd.trans (hδ'lt hlt))
   ·rw[show res p₀=K % p₀ from if_pos hgt]
    obtain⟨-,hKp⟩:=hK_eq.1 hgt
    exact (Nat.modEq_iff_dvd' (by omega:i≤ K)).mpr (hp₀_dvd.trans (hδ'gt hgt))
  exact⟨p₀,Za.mpr ⟨Zb.mpr ⟨hp₀_pr.two_le,hp₀_le⟩,hp₀_pr⟩,hi_res,by rw[←hmod_ij];exact hi_res⟩
 set GoodPairs:=(range p ×ˢ range p).filter (fun z =>
  z.1< z.2/\∃ p₀∈(Icc 2 (p-1)).filter Nat.Prime,z.1 % p₀=res p₀/\z.2 % p₀=res p₀)
 set AllClean:=(Clean ×ˢ Clean).filter (fun z=>z.1< z.2)
 set BadPairs:=AllClean \ GoodPairs;have hAllClean:2*AllClean.card=Clean.card*(Clean.card-1):=Xf Clean
 have hinj_bp:Set.InjOn (fun z:ℕ × ℕ=>({w,a+z.1*d,a+z.2*d}:Zf ℕ))
   (BadPairs:Set (ℕ × ℕ)):=by
  intro ⟨i₁,j₁⟩ h1 ⟨i₂,j₂⟩ h2 heq;have h1':=Za.mp (Ye.mp (Zc.mp h1)).1;have h2':=Za.mp (Ye.mp (Zc.mp h2)).1;dsimp only at h1' h2';have hi1:i₁< p:=mem_range.mp (Za.mp (Zh.mp h1'.1).1).1;have hj1:j₁< p:=mem_range.mp (Za.mp (Zh.mp h1'.1).2).1;have hi2:i₂< p:=mem_range.mp (Za.mp (Zh.mp h2'.1).1).1;have hj2:j₂< p:=mem_range.mp (Za.mp (Zh.mp h2'.1).2).1
  have hlt1:a+i₁*d< a+j₁*d:=by
   have:=Nat.mul_lt_mul_of_pos_right h1'.2 hd_pos;omega
  have hlt2:a+i₂*d< a+j₂*d:=by
   have:=Nat.mul_lt_mul_of_pos_right h2'.2 hd_pos;omega
  have herase:({a+i₁*d,a+j₁*d}:Zf ℕ)={a+i₂*d,a+j₂*d}:=by
   have hnw1:w∉({a+i₁*d,a+j₁*d}:Zf ℕ):=by
    simp only[Zx,Zj,not_or]
    exact⟨fun h=>hwP (h ▸ (hPeq _).mpr ⟨i₁,hi1,rfl⟩),fun h=>hwP (h ▸ (hPeq _).mpr ⟨j₁,hj1,rfl⟩)⟩
   have hnw2:w∉({a+i₂*d,a+j₂*d}:Zf ℕ):=by
    simp only[Zx,Zj,not_or]
    exact⟨fun h=>hwP (h ▸ (hPeq _).mpr ⟨i₂,hi2,rfl⟩),fun h=>hwP (h ▸ (hPeq _).mpr ⟨j₂,hj2,rfl⟩)⟩
   have:=congrArg (fun s=>erase s w) heq
   simpa [erase_insert hnw1,erase_insert hnw2] using this
  have hmin:a+i₁*d=a+i₂*d:=by
   have h1m:a+i₁*d∈({a+i₂*d,a+j₂*d}:Zf ℕ):=by rw[←herase];simp
   have h2m:a+i₂*d∈({a+i₁*d,a+j₁*d}:Zf ℕ):=by rw[herase];simp
   simp only[Zx,Zj] at h1m h2m;omega
  have hmax:a+j₁*d=a+j₂*d:=by
   have h1m:a+j₁*d∈({a+i₂*d,a+j₂*d}:Zf ℕ):=by rw[←herase];simp
   have h2m:a+j₂*d∈({a+i₁*d,a+j₁*d}:Zf ℕ):=by rw[herase];simp
   simp only[Zx,Zj] at h1m h2m;omega
  ext <;> dsimp
  ·exact Nat.eq_of_mul_eq_mul_right hd_pos (by omega)
  ·exact Nat.eq_of_mul_eq_mul_right hd_pos (by omega)
 have hmaps_bp:Set.MapsTo (fun z:ℕ × ℕ=>({w,a+z.1*d,a+z.2*d}:Zf ℕ))
   (BadPairs:Set (ℕ × ℕ)) (((Qb S).filter (fun t=>w∈t/\t.erase w⊆P)):Set (Zf ℕ)):=by
  intro ⟨i,j⟩ hij;obtain⟨hAC,hnotG⟩:=Ye.mp (Zc.mp hij);obtain⟨hCC,hlt⟩:=Za.mp hAC;obtain⟨hiC,hjC⟩:=Zh.mp hCC;have hiP:=mem_range.mp (Za.mp hiC).1;have hjP:=mem_range.mp (Za.mp hjC).1
  have hbad:Qk S {w,a+i*d,a+j*d}:=by
   by_contra hnb;obtain⟨p₀,hp₀,m1,m2⟩:=hgood_aligned i hiC j hjC hlt hnb
   exact hnotG (Za.mpr ⟨Zh.mpr
    ⟨mem_range.mpr hiP,mem_range.mpr hjP⟩,hlt,p₀,hp₀,m1,m2⟩)
  refine Zc.mpr (Za.mpr ⟨(Qh S _).mpr hbad,by simp,?_⟩)
  intro x hx;obtain⟨hxw,hxin⟩:=Zw.mp hx;simp only[Zx,Zj] at hxin
  rcases hxin with rfl|rfl|rfl
  ·exact absurd rfl hxw
  ·exact (hPeq _).mpr ⟨i,hiP,rfl⟩
  ·exact (hPeq _).mpr ⟨j,hjP,rfl⟩
 have hbp_le:BadPairs.card≤((Qb S).filter (fun t=>w∈t/\t.erase w⊆P)).card :=card_le_card_of_injOn _ hmaps_bp hinj_bp
 have hGood_le:(GoodPairs.card:ℝ)≤(3/8:ℝ)*(p:ℝ)^2+(p:ℝ)*(log (p:ℝ)+2) :=Wy p (by omega) ((Icc 2 (p-1)).filter Nat.Prime) (Zl _ _) res
 have hlog_le:log (p:ℝ)≤(p:ℝ)/25-2:=by
  have hpR:(5049:ℝ)≤(p:ℝ):=by exact_mod_cast hp_big
  have hsq_pos:0< Real.sqrt (p:ℝ):=Real.sqrt_pos.mpr (by linarith)
  have hlog_sq:log (p:ℝ)=2*log (Real.sqrt (p:ℝ)):=by
   rw[Real.log_sqrt (by linarith)];ring
  have hle1:log (Real.sqrt (p:ℝ))≤ Real.sqrt (p:ℝ)-1 :=Real.log_le_sub_one_of_pos hsq_pos
  have hsq_le:Real.sqrt (p:ℝ)≤(p:ℝ)/50:=by
   rw[Real.sqrt_le_left (by linarith)];nlinarith
  linarith
 have hBad_ge:(AllClean.card:ℝ)-(GoodPairs.card:ℝ)≤(BadPairs.card:ℝ):=by
  have h1:AllClean.card≤ BadPairs.card+GoodPairs.card:=by have hs:BadPairs.card+(AllClean∩GoodPairs).card=AllClean.card :=card_sdiff_add_card_inter AllClean GoodPairs;have hi:(AllClean∩GoodPairs).card≤ GoodPairs.card :=Zm Yg;omega
  have h1R:(AllClean.card:ℝ)≤(BadPairs.card:ℝ)+(GoodPairs.card:ℝ):=by exact_mod_cast h1
  linarith
 have hAC_ge:((p-q:ℕ):ℝ)*(((p-q:ℕ):ℝ)-1)/2≤(AllClean.card:ℝ):=by
  have h1:(p-q)*(p-q-1)≤2*AllClean.card:=by rw[hAllClean];exact Nat.mul_le_mul hClean_card (Nat.sub_le_sub_right hClean_card 1)
  have h1R:((p-q:ℕ):ℝ)*((p-q-1:ℕ):ℝ)≤2*(AllClean.card:ℝ):=by exact_mod_cast h1
  have hsub1:((p-q-1:ℕ):ℝ)=((p-q:ℕ):ℝ)-1:=by
   rw[Nat.cast_sub (by omega)];simp
  rw[hsub1] at h1R;linarith
 have hp_le_m:p≤ m:=hPcard ▸ Zm hPS
 have hpq_R:((p-q:ℕ):ℝ)=(p:ℝ)-(q:ℝ):=Nat.cast_sub (by omega)
 have hm_eq:(m:ℝ)=(p:ℝ)+(q:ℝ):=by exact_mod_cast (by omega:m=p+q)
 have hq_lt:100*(q:ℝ)<(m:ℝ):=by exact_mod_cast hq2
 have hp_R:(5049:ℝ)≤(p:ℝ):=by exact_mod_cast hp_big
 have hbp_R:(BadPairs.card:ℝ)≤(((Qb S).filter (fun t=>w∈t/\t.erase w⊆P)).card:ℝ):=by exact_mod_cast hbp_le
 have hfinalR:(m:ℝ)^2≤100*(((Qb S).filter (fun t=>w∈t/\t.erase w⊆P)).card:ℝ):=by nlinarith only[hGood_le,hlog_le,hBad_ge,hAC_ge,hpq_R,hm_eq,hq_lt,hp_R,hbp_R,Nat.cast_nonneg (α:=ℝ) q]
 exact_mod_cast hfinalR
private lemma W7 {S P:Zf ℕ} {a d p q w b r:ℕ} {dir:Bool}
  (hPS:P⊆S) (hPcard:P.card=p)
  (hPeq:∀ x,x∈P↔∃ i< p,x=a+i*d)
  (hm:5100≤ S.card) (hq_def:q=S.card-p) (hq2:100*q< S.card)
  (hd_pos:0< d) (hwS:w∈S) (hmod:w % d≠a % d)
  (hr_big:2500≤ r) (_hrp:r≤ p) (hp_le_2r:p≤2*r+1)
  (hmemP:∀ i< r,(if dir then b+i*d else b-i*d)∈P)
  (hwb:if dir then w< b else b< w/\(r-1)*d≤ b)
  (hmodP:∀ i< r,(if dir then b+i*d else b-i*d) % d=a % d) :
  S.card^2≤100*((Qb S).filter (fun t=>w∈t/\t.erase w⊆P)).card:=by
 set m:=S.card;set Q:=S \ P
 have hQcard:Q.card=q:=by have h1:Q.card+P.card=m:=Yb hPS;omega
 let pt:ℕ->ℕ:=fun i=>if dir then b+i*d else b-i*d
 have hdist:∀ i< r,(if dir then pt i-w else w-pt i) =(if dir then b-w else w-b)+i*d:=by
  intro i hi
  cases dir
  ·simp only[pt,Bool.false_eq_true,↓reduceIte] at hwb ⊢
   have:i*d≤ b:=(Yc d (by omega:i≤ r-1)).trans hwb.2
   omega
  ·simp only[pt,↓reduceIte] at hwb ⊢;omega
 set gap0:=if dir then b-w else w-b
 have hgap0_pos:0< gap0:=by cases dir <;> simp[gap0] at hwb ⊢ <;> omega
 have hd_not_dvd:¬ (d ∣ gap0):=by
  intro ⟨t,ht⟩
  have hb0:b % d=a % d:=by simpa [pt] using hmodP 0 (by omega)
  apply hmod;rw[←hb0]
  cases dir
  ·simp only[gap0,Bool.false_eq_true,↓reduceIte] at ht hwb
   exact ((Nat.modEq_iff_dvd' hwb.1.le).mpr ⟨t,ht⟩).symm
  ·simp only[gap0,↓reduceIte] at ht hwb
   exact (Nat.modEq_iff_dvd' hwb.le).mpr ⟨t,ht⟩
 set g:=Nat.gcd d gap0;have hg_pos:0< g:=Nat.gcd_pos_of_pos_left gap0 hd_pos;set d':=d/g;set c₀:=gap0/g;have hd'g:d'*g=d:=Nat.div_mul_cancel (Nat.gcd_dvd_left d gap0);have hc₀g:c₀*g=gap0:=Nat.div_mul_cancel (Nat.gcd_dvd_right d gap0)
 have hcop_cd:Nat.Coprime c₀ d':=by rw[Nat.coprime_comm];exact Nat.coprime_div_gcd_div_gcd hg_pos
 set Clean:=(range r).filter (fun i =>
  ∀ u∈Q,¬ (min (pt i) (pt (i+1))< u/\u< max (pt i) (pt (i+1))))
 have hClean_card:r-q≤ Clean.card:=by
  set Dirty:=(range r).filter (fun i =>
   ∃ u∈Q,min (pt i) (pt (i+1))< u/\u< max (pt i) (pt (i+1)))
  have hDirty_le:Dirty.card≤ Q.card:=by
   have hch:∀ i∈Dirty,∃ u∈Q,min (pt i) (pt (i+1))< u/\u< max (pt i) (pt (i+1)):=by intro i hi;exact (Za.mp hi).2
   let fu:ℕ->ℕ:=fun i=>if hi:i∈Dirty then (hch i hi).choose else 0
   have hfu:∀ i∈Dirty,fu i∈Q/\min (pt i) (pt (i+1))< fu i/\fu i< max (pt i) (pt (i+1)):=by intro i hi;simpa [fu,dif_pos hi] using (hch i hi).choose_spec
   refine card_le_card_of_injOn fu
    (fun i hi=>Zc.mpr (hfu i (Zc.mp hi)).1) ?_
   intro i₁ hi₁ i₂ hi₂ heq;have h1:=hfu i₁ (Zc.mp hi₁);have h2:=hfu i₂ (Zc.mp hi₂);rw[heq] at h1
   cases dir
   ·simp only[pt,Bool.false_eq_true,↓reduceIte] at h1 h2 hwb
    rcases lt_trichotomy i₁ i₂ with hlt|heqi|hgt
    ·exfalso
     have hle1:b-i₂*d≤ b-(i₁+1)*d :=Nat.sub_le_sub_left (Yc d (by omega)) b
     have hmin1:min (b-i₁*d) (b-(i₁+1)*d)=b-(i₁+1)*d :=Yj (Nat.sub_le_sub_left (Yc d (by omega)) b)
     have hmax2:max (b-i₂*d) (b-(i₂+1)*d)=b-i₂*d :=Yk (Nat.sub_le_sub_left (Yc d (by omega)) b)
     rw[hmin1] at h1;rw[hmax2] at h2;omega
    ·exact heqi
    ·exfalso
     have hle1:b-i₁*d≤ b-(i₂+1)*d :=Nat.sub_le_sub_left (Yc d (by omega)) b
     have hmin2:min (b-i₂*d) (b-(i₂+1)*d)=b-(i₂+1)*d :=Yj (Nat.sub_le_sub_left (Yc d (by omega)) b)
     have hmax1:max (b-i₁*d) (b-(i₁+1)*d)=b-i₁*d :=Yk (Nat.sub_le_sub_left (Yc d (by omega)) b)
     rw[hmax1] at h1;rw[hmin2] at h2;omega
   ·simp only[pt,↓reduceIte] at h1 h2
    have hm1:min (b+i₁*d) (b+(i₁+1)*d)=b+i₁*d :=Yl (Nat.add_le_add_left (Yc d (by omega)) b)
    have hM1:max (b+i₁*d) (b+(i₁+1)*d)=b+(i₁+1)*d :=Yi (Nat.add_le_add_left (Yc d (by omega)) b)
    have hm2:min (b+i₂*d) (b+(i₂+1)*d)=b+i₂*d :=Yl (Nat.add_le_add_left (Yc d (by omega)) b)
    have hM2:max (b+i₂*d) (b+(i₂+1)*d)=b+(i₂+1)*d :=Yi (Nat.add_le_add_left (Yc d (by omega)) b)
    rw[hm1,hM1] at h1;rw[hm2,hM2] at h2
    have hlt1:i₁*d<(i₂+1)*d:=by omega
    have hlt2:i₂*d<(i₁+1)*d:=by omega
    have:=Nat.lt_of_mul_lt_mul_right hlt1
    have:=Nat.lt_of_mul_lt_mul_right hlt2
    omega
  have heqD:(range r).filter
    (fun i=>¬ ∀ u∈Q,¬ (min (pt i) (pt (i+1))< u/\u< max (pt i) (pt (i+1))))=Dirty:=by
   ext i;simp only[Dirty,Za,not_forall,not_not,exists_prop]
  have hpart:Clean.card+Dirty.card=r:=by
   have h0:=card_filter_add_card_filter_not (s:=range r)
    (p:=fun i=>∀ u∈Q,¬ (min (pt i) (pt (i+1))< u/\u< max (pt i) (pt (i+1))))
   rw[heqD,card_range] at h0;exact h0
  omega
 set Pset:=(Icc 2 (r-1)).filter (fun p₀=>p₀.Prime/\¬ (p₀ ∣ d'))
 have hres_ex:∀ p₀:ℕ,∃ r₀:ℕ,∀ i:ℕ,p₀∈Pset->p₀ ∣ c₀+i*d'->i % p₀=r₀:=by
  intro p₀
  by_cases hex:∃ i,p₀∈Pset/\p₀ ∣ c₀+i*d'
  ·obtain⟨i₀,hp₀,hdvd₀⟩:=hex
   refine⟨i₀ % p₀,fun i hp₀' hdvd=>?_⟩
   have hp₀_pr:p₀.Prime:=(Za.mp hp₀).2.1;have hndvd:¬ (p₀ ∣ d'):=(Za.mp hp₀).2.2
   rcases le_total i i₀ with hle|hge
   ·have hdiff:p₀ ∣ (i₀-i)*d':=by
     have:(c₀+i₀*d')-(c₀+i*d')=(i₀-i)*d':=by rw[Nat.sub_mul];omega
     rw[←this];exact Nat.dvd_sub hdvd₀ hdvd
    have hdi:p₀ ∣ i₀-i:=(hp₀_pr.dvd_mul.mp hdiff).resolve_right hndvd;exact (Nat.modEq_iff_dvd' hle).mpr hdi
   ·have hdiff:p₀ ∣ (i-i₀)*d':=by
     have:(c₀+i*d')-(c₀+i₀*d')=(i-i₀)*d':=by rw[Nat.sub_mul];omega
     rw[←this];exact Nat.dvd_sub hdvd hdvd₀
    have hdi:p₀ ∣ i-i₀:=(hp₀_pr.dvd_mul.mp hdiff).resolve_right hndvd;exact ((Nat.modEq_iff_dvd' hge).mpr hdi).symm
  ·exact⟨0,fun i hp₀ hdvd=>absurd ⟨i,hp₀,hdvd⟩ hex⟩
 choose res hres using hres_ex
 have hgood_aligned:∀ i∈Clean,∀ j∈Clean,i< j →
   ¬ Qk S {w,pt i,pt j} →
   ∃ p₀∈Pset,i % p₀=res p₀/\j % p₀=res p₀:=by
  intro i hi j hj hij hnotbad;have hiR:=mem_range.mp (Za.mp hi).1;have hjR:=mem_range.mp (Za.mp hj).1;have hxiS:pt i∈S:=hPS (hmemP i hiR);have hxjS:pt j∈S:=hPS (hmemP j hjR)
  have hne_wi:w≠pt i:=fun h=>hmod (by rw[h];exact hmodP i hiR)
  have hne_wj:w≠pt j:=fun h=>hmod (by rw[h];exact hmodP j hjR)
  have hgap_pt:(if dir then pt j-pt i else pt i-pt j)=(j-i)*d:=by
   cases dir
   ·simp only[pt,Bool.false_eq_true,↓reduceIte] at hwb ⊢
    have:j*d≤ b:=(Yc d (by omega:j≤ r-1)).trans hwb.2
    have:i*d≤ j*d:=Yc d (le_of_lt hij)
    rw[Nat.sub_mul];omega
   ·simp only[pt,↓reduceIte];rw[Nat.sub_mul];omega
  have hne_ij:pt i≠pt j:=by
   have hpos:0<(j-i)*d:=Nat.mul_pos (by omega) hd_pos
   cases dir <;> simp only[Bool.false_eq_true,↓reduceIte] at hgap_pt <;> omega
  have hcard3:({w,pt i,pt j}:Zf ℕ).card=3:=by
   rw[card_insert_of_notMem,card_insert_of_notMem,card_singleton]
   ·exact Finset.notMem_singleton.mpr hne_ij
   ·simp[hne_wi,hne_wj]
  have hsub3:({w,pt i,pt j}:Zf ℕ)⊆S:=by
   intro x hx;simp only[Zx,Zj] at hx
   rcases hx with rfl|rfl|rfl <;> assumption
  unfold Qk at hnotbad
  push Not at hnotbad
  obtain⟨A,⟨aA,δ,kA,hkA,hdA,hAeq⟩,hAS,htA⟩:=hnotbad hcard3 hsub3
  have hwA:w∈A:=htA (by simp)
  have hiA:pt i∈A:=htA (by simp)
  have hjA:pt j∈A:=htA (by simp)
  have hkA2:2≤ kA:=by
   have:3≤ A.card:=by rw[←hcard3];exact Zm htA
   rw[Qo hkA hdA hAeq] at this;omega
  have hδ_pos:0<δ:=hdA (by omega)
  obtain⟨iw,hiw,hweqA⟩:=(hAeq w).mp hwA;obtain⟨ii,hii,hieqA⟩:=(hAeq (pt i)).mp hiA;obtain⟨ij,hijA,hjeqA⟩:=(hAeq (pt j)).mp hjA
  have hdvd_ij:δ ∣ (j-i)*d:=by
   cases dir
   ·simp only[Bool.false_eq_true,↓reduceIte] at hgap_pt
    have hlt_pt:pt j< pt i:=by
     have:=Nat.mul_pos (by omega:0< j-i) hd_pos;omega
    have hlt_idx:ij< ii:=Nat.lt_of_mul_lt_mul_right (by omega:ij*δ< ii*δ)
    refine⟨ii-ij,?_⟩
    rw[←hgap_pt,hieqA,hjeqA]
    have:aA+ii*δ-(aA+ij*δ)=(ii-ij)*δ:=by rw[Nat.sub_mul];omega
    rw[this,mul_comm]
   ·simp only[↓reduceIte] at hgap_pt
    have hlt_pt:pt i< pt j:=by
     have:=Nat.mul_pos (by omega:0< j-i) hd_pos;omega
    have hlt_idx:ii< ij:=Nat.lt_of_mul_lt_mul_right (by omega:ii*δ< ij*δ)
    refine⟨ij-ii,?_⟩
    rw[←hgap_pt,hieqA,hjeqA]
    have:aA+ij*δ-(aA+ii*δ)=(ij-ii)*δ:=by rw[Nat.sub_mul];omega
    rw[this,mul_comm]
  have hdvd_wi:δ ∣ gap0+i*d:=by
   have hdi:=hdist i hiR
   cases dir
   ·simp only[Bool.false_eq_true,↓reduceIte] at hdi
    have hlt_pt:pt i< w:=by omega
    have hlt_idx:ii< iw:=Nat.lt_of_mul_lt_mul_right (by omega:ii*δ< iw*δ)
    refine⟨iw-ii,?_⟩
    rw[←hdi,hweqA,hieqA]
    have:aA+iw*δ-(aA+ii*δ)=(iw-ii)*δ:=by rw[Nat.sub_mul];omega
    rw[this,mul_comm]
   ·simp only[↓reduceIte] at hdi
    have hlt_pt:w< pt i:=by omega
    have hlt_idx:iw< ii:=Nat.lt_of_mul_lt_mul_right (by omega:iw*δ< ii*δ)
    refine⟨ii-iw,?_⟩
    rw[←hdi,hweqA,hieqA]
    have:aA+ii*δ-(aA+iw*δ)=(ii-iw)*δ:=by rw[Nat.sub_mul];omega
    rw[this,mul_comm]
  have hndvd_d:¬ (d ∣ δ):=fun hdvd =>
   hd_not_dvd ((Nat.dvd_add_left (dvd_mul_left d i)).mp (hdvd.trans hdvd_wi))
  have hδ_gt_d:d<δ:=by
   have hclean:=(Za.mp hi).2
   have hne_d:δ≠d:=fun h=>hndvd_d ⟨1,by omega⟩
   cases dir
   ·have hlt_pt:pt j< pt i:=by
     simp only[Bool.false_eq_true,↓reduceIte] at hgap_pt
     have:=Nat.mul_pos (by omega:0< j-i) hd_pos;omega
    have hlt_idx:ij< ii:=Nat.lt_of_mul_lt_mul_right (by omega:ij*δ< ii*δ)
    have hmemA:aA+(ii-1)*δ∈A:=(hAeq _).mpr ⟨ii-1,by omega,rfl⟩
    have huS:aA+(ii-1)*δ∈S:=hAS hmemA
    have hu_eq:aA+(ii-1)*δ+δ=pt i:=by
     rw[hieqA];have:(ii-1)*δ+δ=ii*δ:=by
      obtain⟨t,ht⟩:∃ t,ii=t+1:=⟨ii-1,by omega⟩
      rw[ht];simp;ring
     omega
    have hu_notP:aA+(ii-1)*δ∉P:=by
     intro hP'
     have hmodu:(aA+(ii-1)*δ) % d=a % d:=by obtain⟨s,-,hs⟩:=(hPeq _).mp hP';rw[hs,Nat.add_mul_mod_self_right]
     have hmodi:pt i % d=a % d:=hmodP i hiR
     have hdvd:d ∣ δ:=by
      have hd1:=(Nat.modEq_iff_dvd' (by omega:aA+(ii-1)*δ≤ pt i)).mp (hmodu.trans hmodi.symm)
      have hsub:pt i-(aA+(ii-1)*δ)=δ:=by omega
      rwa[hsub] at hd1
     exact hndvd_d hdvd
    have huQ:aA+(ii-1)*δ∈Q:=Ye.mpr ⟨huS,hu_notP⟩;have hc:=hclean (aA+(ii-1)*δ) huQ;simp only[pt,Bool.false_eq_true,↓reduceIte] at hc hu_eq hwb
    have hle_b:(i+1)*d≤ b:=by
     have:i+1≤ r-1:=by omega
     exact (Yc d this).trans hwb.2
    have hmin:min (b-i*d) (b-(i+1)*d)=b-(i+1)*d :=Yj (Nat.sub_le_sub_left (Yc d (by omega)) b)
    have hmax:max (b-i*d) (b-(i+1)*d)=b-i*d :=Yk (Nat.sub_le_sub_left (Yc d (by omega)) b)
    rw[hmin,hmax] at hc
    have hstep_sub:b-i*d-(b-(i+1)*d)=d:=by
     have:(i+1)*d=i*d+d:=by ring
     omega
    omega
   ·have hlt_pt:pt i< pt j:=by
     simp only[↓reduceIte] at hgap_pt
     have:=Nat.mul_pos (by omega:0< j-i) hd_pos;omega
    have hlt_idx:ii< ij:=Nat.lt_of_mul_lt_mul_right (by omega:ii*δ< ij*δ)
    have hmemA:aA+(ii+1)*δ∈A:=(hAeq _).mpr ⟨ii+1,by omega,rfl⟩
    have huS:aA+(ii+1)*δ∈S:=hAS hmemA
    have hu_eq:aA+(ii+1)*δ=pt i+δ:=by rw[hieqA];ring
    have hu_notP:pt i+δ∉P:=by
     intro hP'
     have hmodu:(pt i+δ) % d=a % d:=by obtain⟨s,-,hs⟩:=(hPeq _).mp hP';rw[hs,Nat.add_mul_mod_self_right]
     have hmodi:pt i % d=a % d:=hmodP i hiR
     have hdvd:d ∣ δ:=by
      have:=(Nat.modEq_iff_dvd' (Nat.le_add_right (pt i) δ)).mp (hmodi.trans hmodu.symm)
      simpa using this
     exact hndvd_d hdvd
    have huQ:pt i+δ∈Q:=Ye.mpr ⟨hu_eq ▸ huS,hu_notP⟩;have hc:=hclean (pt i+δ) huQ;simp only[pt,↓reduceIte] at hc
    have hmin:min (b+i*d) (b+(i+1)*d)=b+i*d :=Yl (Nat.add_le_add_left (Yc d (by omega)) b)
    have hmax:max (b+i*d) (b+(i+1)*d)=b+(i+1)*d :=Yi (Nat.add_le_add_left (Yc d (by omega)) b)
    rw[hmin,hmax] at hc
    have hmul:b+(i+1)*d=b+i*d+d:=by ring
    rw[hmul] at hc;omega
  set h:=Nat.gcd d δ;have hh_pos:0< h:=Nat.gcd_pos_of_pos_left δ hd_pos;have hh_le_d:h≤ d:=Nat.le_of_dvd hd_pos (Nat.gcd_dvd_left d δ);set δ':=δ/h;have hδ'h:δ'*h=δ:=Nat.div_mul_cancel (Nat.gcd_dvd_right d δ);have hdh:(d/h)*h=d:=Nat.div_mul_cancel (Nat.gcd_dvd_left d δ)
  have hδ'2:2≤δ':=by
   by_contra hlt2;have hlt2':δ'<2:=Nat.lt_of_not_ge hlt2
   rcases Nat.eq_zero_or_pos δ' with h0|hpos
   ·rw[h0] at hδ'h;omega
   ·have h1:δ'=1:=le_antisymm (Nat.lt_succ_iff.mp hlt2') hpos
    rw[h1,one_mul] at hδ'h;omega
  have hcop_h:Nat.Coprime δ' (d/h):=by rw[Nat.coprime_comm];exact Nat.coprime_div_gcd_div_gcd hh_pos
  have hδ'ij:δ' ∣ j-i:=by
   obtain⟨t,ht⟩:=hdvd_ij
   have hdvd1:δ' ∣ (j-i)*(d/h):=⟨t,Nat.eq_of_mul_eq_mul_right hh_pos (by
    calc ((j-i)*(d/h))*h=(j-i)*((d/h)*h):=by ring
      _=(j-i)*d:=by rw[hdh]
      _=δ*t:=ht
      _=(δ'*h)*t:=by rw[←hδ'h]
      _=(δ'*t)*h:=by ring)⟩
   exact hcop_h.dvd_of_dvd_mul_right hdvd1
  have hh_dvd_g:h ∣ g:=by
   refine Nat.dvd_gcd (Nat.gcd_dvd_left d δ) ?_
   have h1:h ∣ gap0+i*d:=(Nat.gcd_dvd_right d δ).trans hdvd_wi;have h2:h ∣ i*d:=dvd_mul_of_dvd_right (Nat.gcd_dvd_left d δ) i;exact (Nat.dvd_add_left h2).mp h1
  have hgh:(g/h)*h=g:=Nat.div_mul_cancel hh_dvd_g
  have hcop_gh:Nat.Coprime δ' (g/h):=by
   have hgh_dvd:g/h ∣ d/h:=by
    obtain⟨t,ht⟩:=Nat.gcd_dvd_left d gap0
    refine⟨t,Nat.eq_of_mul_eq_mul_right hh_pos ?_⟩
    have hstep1:g*t=((g/h)*h)*t:=congrArg (·*t) hgh.symm
    calc (d/h)*h=d:=hdh
      _=g*t:=ht
      _=((g/h)*h)*t:=hstep1
      _=((g/h)*t)*h:=by ring
   exact hcop_h.coprime_dvd_right hgh_dvd
  have hδ'ci:δ' ∣ c₀+i*d':=by
   obtain⟨t,ht⟩:=hdvd_wi
   have hdvd1:δ' ∣ (c₀+i*d')*(g/h):=⟨t,Nat.eq_of_mul_eq_mul_right hh_pos (by
    calc ((c₀+i*d')*(g/h))*h=(c₀+i*d')*((g/h)*h):=by ring
      _=(c₀+i*d')*g:=by rw[hgh]
      _=c₀*g+i*(d'*g):=by ring
      _=gap0+i*d:=by rw[hc₀g,hd'g]
      _=δ*t:=ht
      _=(δ'*h)*t:=by rw[←hδ'h]
      _=(δ'*t)*h:=by ring)⟩
   exact hcop_gh.dvd_of_dvd_mul_right hdvd1
  set p₀:=δ'.minFac
  have hp₀_pr:p₀.Prime:=Nat.minFac_prime (by omega)
  have hp₀_dvd:p₀ ∣ δ':=Nat.minFac_dvd δ';have hp₀_ij:p₀ ∣ j-i:=hp₀_dvd.trans hδ'ij;have hp₀_ci:p₀ ∣ c₀+i*d':=hp₀_dvd.trans hδ'ci
  have hp₀_ndvd:¬ (p₀ ∣ d'):=by intro hdvd_d';have hc₀_dvd:p₀ ∣ c₀:=(Nat.dvd_add_left (dvd_mul_of_dvd_right hdvd_d' i)).mp hp₀_ci;have h1:p₀ ∣ Nat.gcd c₀ d':=Nat.dvd_gcd hc₀_dvd hdvd_d';rw[hcop_cd.gcd_eq_one] at h1;exact hp₀_pr.not_dvd_one h1
  have hp₀_le:p₀≤ r-1:=(Nat.le_of_dvd (by omega:0< j-i) hp₀_ij).trans (by omega)
  have hp₀_in:p₀∈Pset:=Za.mpr
   ⟨Zb.mpr ⟨hp₀_pr.two_le,hp₀_le⟩,hp₀_pr,hp₀_ndvd⟩
  have hi_mod:i % p₀=res p₀:=hres p₀ i hp₀_in hp₀_ci
  have hj_mod:j % p₀=res p₀:=by rw[←hi_mod];exact ((Nat.modEq_iff_dvd' (le_of_lt hij)).mpr hp₀_ij).symm
  exact⟨p₀,hp₀_in,hi_mod,hj_mod⟩
 set GoodPairs:=(range r ×ˢ range r).filter (fun z =>
  z.1< z.2/\∃ p₀∈Pset,z.1 % p₀=res p₀/\z.2 % p₀=res p₀)
 set AllClean:=(Clean ×ˢ Clean).filter (fun z=>z.1< z.2)
 set BadPairs:=AllClean \ GoodPairs;have hAllClean:2*AllClean.card=Clean.card*(Clean.card-1):=Xf Clean
 have hinj_bp:Set.InjOn (fun z:ℕ × ℕ=>({w,pt z.1,pt z.2}:Zf ℕ))
   (BadPairs:Set (ℕ × ℕ)):=by
  intro ⟨i₁,j₁⟩ h1 ⟨i₂,j₂⟩ h2 heq;have h1':=Za.mp (Ye.mp (Zc.mp h1)).1;have h2':=Za.mp (Ye.mp (Zc.mp h2)).1;dsimp only at h1' h2';have hi1:i₁< r:=mem_range.mp (Za.mp (Zh.mp h1'.1).1).1;have hj1:j₁< r:=mem_range.mp (Za.mp (Zh.mp h1'.1).2).1;have hi2:i₂< r:=mem_range.mp (Za.mp (Zh.mp h2'.1).1).1;have hj2:j₂< r:=mem_range.mp (Za.mp (Zh.mp h2'.1).2).1
  have hnw1:w∉({pt i₁,pt j₁}:Zf ℕ):=by
   simp only[Zx,Zj,not_or]
   exact⟨fun h=>hmod (by rw[h];exact hmodP i₁ hi1),fun h=>hmod (by rw[h];exact hmodP j₁ hj1)⟩
  have hnw2:w∉({pt i₂,pt j₂}:Zf ℕ):=by
   simp only[Zx,Zj,not_or]
   exact⟨fun h=>hmod (by rw[h];exact hmodP i₂ hi2),fun h=>hmod (by rw[h];exact hmodP j₂ hj2)⟩
  have herase:({pt i₁,pt j₁}:Zf ℕ)={pt i₂,pt j₂}:=by
   have:=congrArg (fun s=>erase s w) heq
   simpa [erase_insert hnw1,erase_insert hnw2] using this
  have h1m:pt i₁∈({pt i₂,pt j₂}:Zf ℕ):=by rw[←herase];simp
  have h2m:pt i₂∈({pt i₁,pt j₁}:Zf ℕ):=by rw[herase];simp
  have h3m:pt j₁∈({pt i₂,pt j₂}:Zf ℕ):=by rw[←herase];simp
  have h4m:pt j₂∈({pt i₁,pt j₁}:Zf ℕ):=by rw[herase];simp
  simp only[Zx,Zj] at h1m h2m h3m h4m
  cases dir
  ·simp only[pt,Bool.false_eq_true,↓reduceIte] at h1m h2m h3m h4m hwb
   have hle1:j₁*d≤ b:=(Yc d (by omega:j₁≤ r-1)).trans hwb.2
   have hle2:j₂*d≤ b:=(Yc d (by omega:j₂≤ r-1)).trans hwb.2
   have hlt1:b-j₁*d< b-i₁*d:=by
    have:=Nat.mul_lt_mul_of_pos_right h1'.2 hd_pos;omega
   have hlt2:b-j₂*d< b-i₂*d:=by
    have:=Nat.mul_lt_mul_of_pos_right h2'.2 hd_pos;omega
   have ei:b-i₁*d=b-i₂*d:=by omega
   have ej:b-j₁*d=b-j₂*d:=by omega
   have hi1b:i₁*d≤ b:=(Yc d (by omega:i₁≤ r-1)).trans hwb.2
   have hi2b:i₂*d≤ b:=(Yc d (by omega:i₂≤ r-1)).trans hwb.2
   ext <;> dsimp
   ·exact Nat.eq_of_mul_eq_mul_right hd_pos (by omega)
   ·exact Nat.eq_of_mul_eq_mul_right hd_pos (by omega)
  ·simp only[pt,↓reduceIte] at h1m h2m h3m h4m
   have hlt1:b+i₁*d< b+j₁*d:=by
    have:=Nat.mul_lt_mul_of_pos_right h1'.2 hd_pos;omega
   have hlt2:b+i₂*d< b+j₂*d:=by
    have:=Nat.mul_lt_mul_of_pos_right h2'.2 hd_pos;omega
   have ei:b+i₁*d=b+i₂*d:=by omega
   have ej:b+j₁*d=b+j₂*d:=by omega
   ext <;> dsimp
   ·exact Nat.eq_of_mul_eq_mul_right hd_pos (by omega)
   ·exact Nat.eq_of_mul_eq_mul_right hd_pos (by omega)
 have hmaps_bp:Set.MapsTo (fun z:ℕ × ℕ=>({w,pt z.1,pt z.2}:Zf ℕ))
   (BadPairs:Set (ℕ × ℕ)) (((Qb S).filter (fun t=>w∈t/\t.erase w⊆P)):Set (Zf ℕ)):=by
  intro ⟨i,j⟩ hij;obtain⟨hAC,hnotG⟩:=Ye.mp (Zc.mp hij);obtain⟨hCC,hlt⟩:=Za.mp hAC;obtain⟨hiC,hjC⟩:=Zh.mp hCC;have hiR:=mem_range.mp (Za.mp hiC).1;have hjR:=mem_range.mp (Za.mp hjC).1
  have hbad:Qk S {w,pt i,pt j}:=by
   by_contra hnb;obtain⟨p₀,hp₀,m1,m2⟩:=hgood_aligned i hiC j hjC hlt hnb
   exact hnotG (Za.mpr ⟨Zh.mpr
    ⟨mem_range.mpr hiR,mem_range.mpr hjR⟩,hlt,p₀,hp₀,m1,m2⟩)
  refine Zc.mpr (Za.mpr ⟨(Qh S _).mpr hbad,by simp,?_⟩)
  intro x hx;obtain⟨hxw,hxin⟩:=Zw.mp hx;simp only[Zx,Zj] at hxin
  rcases hxin with rfl|rfl|rfl
  ·exact absurd rfl hxw
  ·exact hmemP i hiR
  ·exact hmemP j hjR
 have hbp_le:BadPairs.card≤((Qb S).filter (fun t=>w∈t/\t.erase w⊆P)).card :=card_le_card_of_injOn _ hmaps_bp hinj_bp
 have hGood_le:(GoodPairs.card:ℝ)≤(3/8:ℝ)*(r:ℝ)^2+(r:ℝ)*(log (r:ℝ)+2) :=Wy r (by omega) Pset (Zl _ _) res
 have hlog_le:log (r:ℝ)≤(r:ℝ)/25-2:=by
  have hrR:(2500:ℝ)≤(r:ℝ):=by exact_mod_cast hr_big
  have hsq_pos:0< Real.sqrt (r:ℝ):=Real.sqrt_pos.mpr (by linarith)
  have hlog_sq:log (r:ℝ)=2*log (Real.sqrt (r:ℝ)):=by
   rw[Real.log_sqrt (by linarith)];ring
  have hle1:log (Real.sqrt (r:ℝ))≤ Real.sqrt (r:ℝ)-1 :=Real.log_le_sub_one_of_pos hsq_pos
  have hsq_le:Real.sqrt (r:ℝ)≤(r:ℝ)/50:=by
   rw[Real.sqrt_le_left (by linarith)];nlinarith
  linarith
 have hBad_ge:(AllClean.card:ℝ)-(GoodPairs.card:ℝ)≤(BadPairs.card:ℝ):=by
  have h1:AllClean.card≤ BadPairs.card+GoodPairs.card:=by have hs:BadPairs.card+(AllClean∩GoodPairs).card=AllClean.card :=card_sdiff_add_card_inter AllClean GoodPairs;have hi:(AllClean∩GoodPairs).card≤ GoodPairs.card :=Zm Yg;omega
  have h1R:(AllClean.card:ℝ)≤(BadPairs.card:ℝ)+(GoodPairs.card:ℝ):=by exact_mod_cast h1
  linarith
 have hAC_ge:((r-q:ℕ):ℝ)*(((r-q:ℕ):ℝ)-1)/2≤(AllClean.card:ℝ):=by
  have h1:(r-q)*(r-q-1)≤2*AllClean.card:=by rw[hAllClean];exact Nat.mul_le_mul hClean_card (Nat.sub_le_sub_right hClean_card 1)
  have h1R:((r-q:ℕ):ℝ)*((r-q-1:ℕ):ℝ)≤2*(AllClean.card:ℝ):=by exact_mod_cast h1
  have hsub1:((r-q-1:ℕ):ℝ)=((r-q:ℕ):ℝ)-1:=by
   rw[Nat.cast_sub (by omega)];simp
  rw[hsub1] at h1R;linarith
 have hp_le_m:p≤ m:=hPcard ▸ Zm hPS
 have hrq_R:((r-q:ℕ):ℝ)=(r:ℝ)-(q:ℝ):=Nat.cast_sub (by omega)
 have hm_eq:(m:ℝ)=(p:ℝ)+(q:ℝ):=by exact_mod_cast (by omega:m=p+q)
 have hq_lt:100*(q:ℝ)<(m:ℝ):=by exact_mod_cast hq2
 have hr_R:(2500:ℝ)≤(r:ℝ):=by exact_mod_cast hr_big
 have h2r:(p:ℝ)≤2*(r:ℝ)+1:=by exact_mod_cast hp_le_2r
 have hbp_R:(BadPairs.card:ℝ)≤(((Qb S).filter (fun t=>w∈t/\t.erase w⊆P)).card:ℝ):=by exact_mod_cast hbp_le
 have hfinalR:(m:ℝ)^2≤100*(((Qb S).filter (fun t=>w∈t/\t.erase w⊆P)).card:ℝ):=by nlinarith only[hGood_le,hlog_le,hBad_ge,hAC_ge,hrq_R,hm_eq,hq_lt,hr_R,h2r,hbp_R,Nat.cast_nonneg (α:=ℝ) q]
 exact_mod_cast hfinalR
lemma Xu (S:Zf ℕ) (hm:5100≤ S.card)
  (hq1:1≤ S.card-Qc S) (hq2:100*(S.card-Qc S)< S.card) :
  (S.card-Qc S)*S.card^2≤100*(Qb S).card:=by
 set m:=S.card;set p:=Qc S;set q:=m-p
 obtain⟨P,hPS,⟨a,d,k,hk,hdk,hPeq⟩,hPcard,hPmax⟩:=Wo S (card_pos.mp (by omega))
 have hk_eq:k=p:=by rw[←Qo hk hdk hPeq,hPcard]
 subst hk_eq
 have hp_big:5049≤ p:=by omega
 have hd_pos:0< d:=hdk (by omega)
 set Q:=S \ P
 have hQcard:Q.card=q:=by have h1:Q.card+P.card=m:=Yb hPS;omega
 have hper_w:∀ w∈Q,m^2≤100*((Qb S).filter (fun t=>w∈t/\(t.erase w)⊆P)).card:=by
  intro w hwQ;obtain⟨hwS,hwP⟩:=Ye.mp hwQ
  by_cases hmod:w % d=a % d
  ·exact X7 hPS hPcard hPmax hPeq hm rfl hq2 hd_pos hwS hwP hmod
  ·set Lset:=(range p).filter (fun i=>a+i*d< w)
   set k0:=Lset.card
   have hk0_le:k0≤ p:=(card_filter_le _ _).trans (by rw[card_range])
   have hsplit_idx:(∀ i< k0,a+i*d< w)/\(∀ i,k0≤ i->i< p->w< a+i*d):=by
    have hdown:∀ i j,j∈Lset->i≤ j->i∈Lset:=by
     intro i j hj hij;obtain⟨hjR,hjwt⟩:=Za.mp hj;rw[mem_range] at hjR
     exact Za.mpr ⟨mem_range.mpr (by omega),lt_of_le_of_lt (Nat.add_le_add_left (Yc d hij) a) hjwt⟩
    have hLeq:Lset=range k0:=by
     ext i
     constructor
     ·intro hi
      rw[mem_range]
      have hsub:range (i+1)⊆Lset:=fun j hj =>
       hdown j i hi (Nat.lt_succ_iff.mp (mem_range.mp hj))
      have hle:i+1≤ k0:=by simpa only [card_range] using Zm hsub
      omega
     ·intro hi
      rw[mem_range] at hi;by_contra hnot
      have hsub:Lset⊆range i:=by
       intro j hj;rw[mem_range]
       by_contra hge;exact hnot (hdown i j hj (by omega))
      have hle:k0≤ i:=by simpa only [card_range] using Zm hsub
      omega
    constructor
    ·intro i hi
     have:i∈Lset:=by rw[hLeq];exact mem_range.mpr hi
     exact (Za.mp this).2
    ·intro i hi1 hi2
     have hnot:i∉Lset:=by rw[hLeq,mem_range];omega
     have hge:w≤ a+i*d:=by
      by_contra hlt;exact hnot (Za.mpr ⟨mem_range.mpr hi2,by omega⟩)
     have hne:w≠a+i*d:=fun h=>hmod (by rw[h,Nat.add_mul_mod_self_right])
     omega
   rcases le_or_gt k0 (p-k0) with hRbig|hLbig
   ·refine W7 (b:=a+k0*d) (r:=p-k0) (dir:=true)
     hPS hPcard hPeq hm rfl hq2 hd_pos hwS hmod (by omega) (by omega) (by omega) ?_ ?_ ?_
    ·intro i hi
     simp only[↓reduceIte]
     refine (hPeq _).mpr ⟨k0+i,by omega,by ring⟩
    ·simp only[↓reduceIte]
     exact hsplit_idx.2 k0 le_rfl (by omega)
    ·intro i _
     simp only[↓reduceIte]
     have:a+k0*d+i*d=a+(k0+i)*d:=by ring
     rw[this,Nat.add_mul_mod_self_right]
   ·refine W7 (b:=a+(k0-1)*d) (r:=k0) (dir:=false)
     hPS hPcard hPeq hm rfl hq2 hd_pos hwS hmod (by omega) (by omega) (by omega) ?_ ?_ ?_
    ·intro i hi
     simp only[Bool.false_eq_true,↓reduceIte]
     refine (hPeq _).mpr ⟨k0-1-i,by omega,?_⟩
     have:(k0-1-i)*d+i*d=(k0-1)*d:=by rw[←Nat.add_mul];congr 1;omega
     omega
    ·simp only[Bool.false_eq_true,↓reduceIte]
     exact⟨hsplit_idx.1 (k0-1) (by omega),by omega⟩
    ·intro i hi
     simp only[Bool.false_eq_true,↓reduceIte]
     have heq:a+(k0-1)*d-i*d=a+(k0-1-i)*d:=by
      have:(k0-1-i)*d+i*d=(k0-1)*d:=by rw[←Nat.add_mul];congr 1;omega
      omega
     rw[heq,Nat.add_mul_mod_self_right]
 have hdisj:Set.PairwiseDisjoint (Q:Set ℕ)
   (fun w=>(Qb S).filter (fun t=>w∈t/\t.erase w⊆P)):=by
  intro w₁ hw₁ w₂ hw₂ hne;simp only[Function.onFun];rw[Zk];intro t ht1 ht2;have h1:=(Za.mp ht1).2;have h2:=(Za.mp ht2).2;have hw2P:w₂∉P:=(Ye.mp (Zc.mp hw₂)).2;have hw2_er:w₂∈t.erase w₁:=Zw.mpr ⟨hne.symm,h2.1⟩;exact hw2P (h1.2 hw2_er)
 have hsub_bt:Q.biUnion (fun w=>(Qb S).filter (fun t=>w∈t/\t.erase w⊆P))⊆Qb S:=by intro t ht;obtain⟨w,-,htw⟩:=mem_biUnion.mp ht;exact (Za.mp htw).1
 calc q*m^2=∑ _w∈Q,m^2:=by rw[Finset.sum_const,hQcard,smul_eq_mul]
   _≤∑ w∈Q,100*((Qb S).filter (fun t=>w∈t/\t.erase w⊆P)).card :=
       Finset.sum_le_sum hper_w
   _=100*∑ w∈Q,((Qb S).filter (fun t=>w∈t/\t.erase w⊆P)).card:=by
       rw[Finset.mul_sum]
   _=100*(Q.biUnion (fun w=>(Qb S).filter (fun t=>w∈t/\t.erase w⊆P))).card:=by
       rw[card_biUnion hdisj]
   _≤100*(Qb S).card:=Yd 100 (Zm hsub_bt)
lemma Qr (N A C:ℕ) (F:Zf (Zf ℕ))
  (hF:Zt N F)
  (hbad:∀ S∈F,A≤ C*(Qb S).card) :
  F.card*A≤ C*N.choose 3:=by
 have hdisj:Set.PairwiseDisjoint (F:Set (Zf ℕ)) Qb:=by
  intro S hS T hT hST;simp only[Function.onFun];rw[Zk];intro t htS htT
  exact We hF (Zc.mp hS) (Zc.mp hT) hST
   ((Qh S t).mp htS) ((Qh T t).mp htT).2.1
 have hsub:F.biUnion Qb⊆(Icc 1 N).powersetCard 3:=by intro t ht;obtain⟨S,hS,htS⟩:=mem_biUnion.mp ht;have hb:=(Qh S t).mp htS;exact Zz.mpr ⟨hb.2.1.trans (Zy.mp (hF.1 hS)),hb.1⟩
 calc F.card*A=∑ _S∈F,A:=by rw[Finset.sum_const,smul_eq_mul]
   _≤∑ S∈F,C*(Qb S).card:=Finset.sum_le_sum hbad
   _=C*∑ S∈F,(Qb S).card:=by rw[Finset.mul_sum]
   _=C*(F.biUnion Qb).card:=by rw[card_biUnion hdisj]
   _≤ C*((Icc 1 N).powersetCard 3).card:=Yd C (Zm hsub)
   _=C*N.choose 3:=by rw[card_powersetCard,Nat.card_Icc];simp
lemma Wq (N:ℕ):6*N.choose 3≤ N^3:=by
 have h:=Nat.descFactorial_eq_factorial_mul_choose N 3
 have hfac:Nat.factorial 3=6:=by decide
 rw[hfac] at h;rw[←h];simp only[Nat.descFactorial_succ,Nat.descFactorial_zero,mul_one,Nat.sub_zero];have h1:N-1≤ N:=Nat.sub_le N 1;have h2:N-2≤ N:=Nat.sub_le N 2
 calc (N-2)*((N-1)*N)≤ N*(N*N):=Nat.mul_le_mul h2 (Yc N h1)
   _=N^3:=by ring
lemma W8 {S:Zf ℕ} (hne:S.Nonempty) (hnot:¬ IsAP S) :Qc S< S.card:=by
 obtain⟨P,hPS,hPAP,hPcard,-⟩:=Wo S hne;have hle:P.card≤ S.card:=Zm hPS
 rcases lt_or_eq_of_le hle with hlt|heq
 ·omega
 ·exfalso
  have hPe:P=S:=eq_of_subset_of_card_le hPS (le_of_eq heq.symm);exact hnot (hPe ▸ hPAP)
lemma Xs (N s:ℕ) (hs:5100≤ s) (Q:Zf (Zf ℕ))
  (hQ:Zt N Q)
  (hnonAP:∀ S∈Q,¬ IsAP S)
  (hsize:∀ S∈Q,s≤ S.card) :
  (Q.card:ℝ)≤70*(N:ℝ)^3/(s:ℝ)^2:=by
 set Q1:=Q.filter (fun S=>S.card≤100*(S.card-Qc S))
 set Q2:=Q.filter (fun S=>¬ (S.card≤100*(S.card-Qc S)))
 have hQpart:Q.card=Q1.card+Q2.card :=(card_filter_add_card_filter_not (s:=Q)
   (p:=fun S=>S.card≤100*(S.card-Qc S))).symm
 have hQ1_sub:Zt N Q1:=by
  refine⟨(Zl _ _).trans hQ.1,?_⟩
  intro S hS T hT hST
  exact hQ.2 (Zc.mpr (Zl _ _ (Zc.mp hS)))
   (Zc.mpr (Zl _ _ (Zc.mp hT))) hST
 have hQ2_sub:Zt N Q2:=by
  refine⟨(Zl _ _).trans hQ.1,?_⟩
  intro S hS T hT hST
  exact hQ.2 (Zc.mpr (Zl _ _ (Zc.mp hS)))
   (Zc.mpr (Zl _ _ (Zc.mp hT))) hST
 have hQ1_bd:Q1.card*(s*(s-1))≤200*N.choose 3:=by
  refine Qr N (s*(s-1)) 200 Q1 hQ1_sub fun S hS=>?_
  obtain⟨hSQ,hcond⟩:=Za.mp hS;have hm:s≤ S.card:=hsize S hSQ
  have hc1:=Vu S (by omega)
  calc s*(s-1)≤ S.card*(S.card-1):=Nat.mul_le_mul hm (Nat.sub_le_sub_right hm 1)
    _≤(100*(S.card-Qc S))*(S.card-1):=Yc _ hcond
    _=100*((S.card-1)*(S.card-Qc S)):=by ring
    _≤100*(2*(Qb S).card):=Yd 100 hc1
    _=200*(Qb S).card:=by ring
 have hQ2_bd:Q2.card*s^2≤100*N.choose 3:=by
  refine Qr N (s^2) 100 Q2 hQ2_sub fun S hS=>?_
  obtain⟨hSQ,hcond⟩:=Za.mp hS;have hm:s≤ S.card:=hsize S hSQ
  have hlt:=W8 (card_pos.mp (by omega)) (hnonAP S hSQ)
  have hc2:=Xu S (by omega) (by omega) (by omega)
  calc s^2≤ S.card^2:=Nat.pow_le_pow_left hm 2
    _=1*S.card^2:=by ring
    _≤(S.card-Qc S)*S.card^2:=Yc _ (by omega)
    _≤100*(Qb S).card:=hc2
 have hch:=Wq N
 have hQ1N:6*(Q1.card*(s*(s-1)))≤200*N^3:=by
  calc 6*(Q1.card*(s*(s-1)))≤6*(200*N.choose 3):=Yd 6 hQ1_bd
    _=200*(6*N.choose 3):=by ring
    _≤200*N^3:=Yd 200 hch
 have hQ2N:6*(Q2.card*s^2)≤100*N^3:=by
  calc 6*(Q2.card*s^2)≤6*(100*N.choose 3):=Yd 6 hQ2_bd
    _=100*(6*N.choose 3):=by ring
    _≤100*N^3:=Yd 100 hch
 have hQ1R:6*(Q1.card:ℝ)*((s:ℝ)*((s:ℝ)-1))≤200*(N:ℝ)^3:=by
  have hcast:((6*(Q1.card*(s*(s-1))):ℕ):ℝ)≤((200*N^3:ℕ):ℝ):=by exact_mod_cast hQ1N
  push_cast [Nat.cast_sub (by omega:1≤ s)] at hcast
  linarith
 have hQ2R:6*((Q2.card:ℝ)*(s:ℝ)^2)≤100*(N:ℝ)^3:=by exact_mod_cast hQ2N
 have hsR:(5100:ℝ)≤(s:ℝ):=by exact_mod_cast hs
 have hQpartR:(Q.card:ℝ)=(Q1.card:ℝ)+(Q2.card:ℝ):=by exact_mod_cast hQpart
 have hQ1_sq:5*((Q1.card:ℝ)*(s:ℝ)^2)≤200*(N:ℝ)^3:=by
  have hs56:5*(s:ℝ)^2≤6*((s:ℝ)*((s:ℝ)-1)):=by nlinarith
  have hmul:5*((Q1.card:ℝ)*(s:ℝ)^2)≤6*(Q1.card:ℝ)*((s:ℝ)*((s:ℝ)-1)):=by nlinarith[Nat.cast_nonneg (α:=ℝ) Q1.card]
  linarith
 rw[le_div_iff₀ (by positivity:(0:ℝ)<(s:ℝ)^2)]
 nlinarith[Nat.cast_nonneg (α:=ℝ) N]
lemma X6 (N T:ℕ) (S:Zf ℕ) (hsub:S⊆Icc 1 N)
  (hT:∀ L∈Icc 1 N,L.divisors.card≤ T)
  (hm_ge:4*T*Qc S+8≤ S.card) :
  S.card*(S.card-1)*S.card≤24*(Qb S).card:=by
 set m:=S.card;set p:=Qc S
 have hm8:8≤ m:=by omega
 let OrdPairs:=(S ×ˢ S).filter (fun z=>z.1≠z.2)
 have hOrd:OrdPairs.card=m*(m-1):=by
  have hdiag:((S ×ˢ S).filter (fun z=>z.1=z.2)).card=m:=by
   refine card_bij (fun z _=>z.1) ?_ ?_ ?_
   ·intro z hz;exact (Zh.mp (Za.mp hz).1).1
   ·intro z hz w hw hzw
    have e1:=(Za.mp hz).2;have e2:=(Za.mp hw).2
    ext <;> omega
   ·intro x hx;exact⟨(x,x),Za.mpr ⟨Zh.mpr ⟨hx,hx⟩,rfl⟩,rfl⟩
  have hpart:=card_filter_add_card_filter_not (s:=S ×ˢ S) (p:=fun z=>z.1=z.2)
  have hcardS:S.card=m:=rfl;rw[hdiag,card_product,hcardS] at hpart
  have hmul:m*(m-1)+m=m*m:=by
   obtain⟨k,hk⟩:∃ k,m=k+1:=⟨m-1,by omega⟩
   rw[hk];simp only[Nat.add_sub_cancel];ring
  have heq:(S ×ˢ S).filter (fun z=>¬ (z.1=z.2))=OrdPairs:=rfl
  rw[heq] at hpart;omega
 let BadTriplesOrd:=OrdPairs.biUnion (fun z =>
  (S \ (((max z.1 z.2-min z.1 z.2).divisors.biUnion (fun δ=>Qf S z.1 δ))∪({z.1,z.2}:Zf ℕ))).image
   (fun v=>(z.1,z.2,v)))
 have hOrd_ge:m*(m-1)*(m/2)≤ BadTriplesOrd.card:=by
  rw[card_biUnion]
  ·calc m*(m-1)*(m/2)=∑ _z∈OrdPairs,(m/2):=by
          rw[Finset.sum_const,hOrd,smul_eq_mul]
      _≤∑ z∈OrdPairs,
            ((S \ (((max z.1 z.2-min z.1 z.2).divisors.biUnion (fun δ=>Qf S z.1 δ))∪{z.1,z.2})).image
              (fun v=>(z.1,z.2,v))).card:=by
          refine Finset.sum_le_sum fun z hz=>?_
          obtain⟨hSS,hne⟩:=Za.mp hz;obtain⟨hxS,huS⟩:=Zh.mp hSS;set diff:=max z.1 z.2-min z.1 z.2
          have hdiff_mem:diff∈Icc 1 N:=by
            have h1:=Zb.mp (hsub hxS);have h2:=Zb.mp (hsub huS)
            refine Zb.mpr ⟨?_,?_⟩
            · rcases lt_or_gt_of_ne hne with hlt|hgt
              · dsimp only[diff];rw[Yi hlt.le,Yl hlt.le];omega
              · dsimp only[diff];rw[Yk hgt.le,Yj hgt.le];omega
            · rcases le_total z.1 z.2 with hle|hge
              · dsimp only[diff];rw[Yi hle,Yl hle];omega
              · dsimp only[diff];rw[Yk hge,Yj hge];omega
          have hU_le:((diff.divisors.biUnion (fun δ=>Qf S z.1 δ))∪({z.1,z.2}:Zf ℕ)).card ≤ T*p+2:=by
            refine (Yh _ _).trans ?_
            have h2:({z.1,z.2}:Zf ℕ).card≤2:=(card_insert_le _ _).trans (by simp)
            have h1:(diff.divisors.biUnion (fun δ=>Qf S z.1 δ)).card≤ T*p:=by
              calc (diff.divisors.biUnion (fun δ=>Qf S z.1 δ)).card
                  ≤ ∑ δ∈diff.divisors,(Qf S z.1 δ).card:=card_biUnion_le
                _≤∑ _δ∈diff.divisors,p:=by
                    refine Finset.sum_le_sum fun δ hδ=>?_
                    have hδ_pos:0<δ:=Nat.pos_of_mem_divisors hδ;obtain⟨-,-,-,-,hmax⟩:=Wo S ⟨z.1,hxS⟩;exact hmax _ (Qz S z.1 δ) (Wh hδ_pos hxS)
                _=diff.divisors.card*p:=by rw[Finset.sum_const,smul_eq_mul]
                _≤ T*p:=Yc p (hT diff hdiff_mem)
            omega
          have hsdiff:m/2≤(S \ ((diff.divisors.biUnion (fun δ=>Qf S z.1 δ))∪{z.1,z.2})).card:=by
            have h1:(S \ ((diff.divisors.biUnion (fun δ=>Qf S z.1 δ))∪{z.1,z.2})).card +(S∩((diff.divisors.biUnion (fun δ=>Qf S z.1 δ))∪{z.1,z.2})).card=m :=card_sdiff_add_card_inter S _
            have h2:=Zm (Yg
              (s₁:=S) (s₂:=(diff.divisors.biUnion (fun δ=>Qf S z.1 δ))∪{z.1,z.2}))
            have hassoc:4*(T*p)=4*T*p:=by ring
            omega
          rw[card_image_of_injOn]
          · exact hsdiff
          · intro v₁ _ v₂ _ heq;exact congrArg (fun t=>t.2.2) heq
  ·intro z₁ _ z₂ _ hne
   simp only[Function.onFun];rw[Zk];intro t ht1 ht2;obtain⟨_,_,rfl⟩:=Zi.mp ht1;obtain⟨_,_,hpair⟩:=Zi.mp ht2
   exact hne (Prod.ext (congrArg Prod.fst hpair).symm (congrArg (fun w=>w.2.1) hpair).symm)
 have hOrd_le:BadTriplesOrd.card≤6*(Qb S).card:=by
  have hsubB:BadTriplesOrd⊆(Qb S).biUnion (fun t =>
    ((t ×ˢ (t ×ˢ t)).filter (fun w=>w.1≠w.2.1/\w.1≠w.2.2/\w.2.1≠w.2.2))):=by
   intro w hw;obtain⟨z,hz,hw_img⟩:=mem_biUnion.mp hw;obtain⟨v,hv',rfl⟩:=Zi.mp hw_img
   rcases z with ⟨x,u⟩
   obtain⟨hSS,hne_xu⟩:=Za.mp hz;obtain⟨hxS,huS⟩:=Zh.mp hSS;obtain⟨hvS,hvNotU⟩:=Ye.mp hv'
   have hne_vx:v≠x:=fun h=>hvNotU (Zg _ (by simp[h]))
   have hne_vu:v≠u:=fun h=>hvNotU (Zg _ (by simp[h]))
   have hbad:Qk S {x,u,v}:=by
    refine⟨?_,?_,?_⟩
    ·rw[card_insert_of_notMem,card_insert_of_notMem,card_singleton]
     ·simp[hne_vu.symm]
     ·simp[hne_xu,hne_vx.symm]
    ·intro y hy;simp only[Zx,Zj] at hy
     rcases hy with rfl|rfl|rfl <;> assumption
    ·rintro A ⟨aA,δ,kA,hkA,hdA,hAeq⟩ hAS hsubA
     have hxA:x∈A:=hsubA (by simp)
     have huA:u∈A:=hsubA (by simp)
     have hvA:v∈A:=hsubA (by simp)
     have hkA2:2≤ kA:=by
      have h3:({x,u,v}:Zf ℕ).card≤ A.card:=Zm hsubA
      have hc3:({x,u,v}:Zf ℕ).card=3:=by
       rw[card_insert_of_notMem,card_insert_of_notMem,card_singleton]
       ·simp[hne_vu.symm]
       ·simp[hne_xu,hne_vx.symm]
      rw[Qo hkA hdA hAeq] at h3;omega
     have hδ_pos:0<δ:=hdA (by omega)
     obtain⟨ix,-,hix⟩:=(hAeq x).mp hxA;obtain⟨iu,-,hiu⟩:=(hAeq u).mp huA
     have hδ_dvd:δ ∣ max x u-min x u:=by
      rcases lt_or_gt_of_ne hne_xu with hlt|hgt
      ·rw[Yi hlt.le,Yl hlt.le]
       have hidx:ix< iu:=Nat.lt_of_mul_lt_mul_right (by omega:ix*δ< iu*δ)
       refine⟨iu-ix,?_⟩
       rw[hix,hiu];have:aA+iu*δ-(aA+ix*δ)=(iu-ix)*δ:=by rw[Nat.sub_mul];omega
       rw[this,mul_comm]
      ·rw[Yk hgt.le,Yj hgt.le]
       have hidx:iu< ix:=Nat.lt_of_mul_lt_mul_right (by omega:iu*δ< ix*δ)
       refine⟨ix-iu,?_⟩
       rw[hix,hiu];have:aA+ix*δ-(aA+iu*δ)=(ix-iu)*δ:=by rw[Nat.sub_mul];omega
       rw[this,mul_comm]
     have hdiff_ne:max x u-min x u≠0:=by
      rcases lt_or_gt_of_ne hne_xu with hlt|hgt
      ·rw[Yi hlt.le,Yl hlt.le];omega
      ·rw[Yk hgt.le,Yj hgt.le];omega
     have hvR:v∈Qf S x δ:=Qv hAS hδ_pos hAeq hxA hvA
     exact hvNotU (Ze _ (mem_biUnion.mpr
      ⟨δ,Nat.mem_divisors.mpr ⟨hδ_dvd,hdiff_ne⟩,hvR⟩))
   refine mem_biUnion.mpr ⟨{x,u,v},(Qh S _).mpr hbad,?_⟩
   refine Za.mpr ⟨Zh.mpr ⟨by simp,Zh.mpr ⟨by simp,by simp⟩⟩,hne_xu,hne_vx.symm,hne_vu.symm⟩
  calc BadTriplesOrd.card
      ≤ ((Qb S).biUnion (fun t =>
          (t ×ˢ (t ×ˢ t)).filter (fun w=>w.1≠w.2.1/\w.1≠w.2.2/\w.2.1≠w.2.2))).card :=
        Zm hsubB
    _≤∑ t∈Qb S,
          ((t ×ˢ (t ×ˢ t)).filter (fun w=>w.1≠w.2.1/\w.1≠w.2.2/\w.2.1≠w.2.2)).card :=
        card_biUnion_le
    _≤∑ _t∈Qb S,6:=by
        refine Finset.sum_le_sum fun t ht=>?_
        have ht3:t.card=3:=((Qh S t).mp ht).1
        have hsub6:(t ×ˢ (t ×ˢ t)).filter (fun w=>w.1≠w.2.1/\w.1≠w.2.2/\w.2.1≠w.2.2) ⊆
            t.biUnion (fun a=>(t.erase a).biUnion (fun b =>
              ((t.erase a).erase b).image (fun c=>(a,b,c)))):=by
          intro ⟨a,b,c⟩ hw;obtain⟨hP',h1,h2,h3⟩:=Za.mp hw;obtain⟨ha,hbc⟩:=Zh.mp hP';obtain⟨hb,hc⟩:=Zh.mp hbc
          refine mem_biUnion.mpr ⟨a,ha,mem_biUnion.mpr ⟨b,Zw.mpr ⟨h1.symm,hb⟩,Zi.mpr ⟨c,Zw.mpr ⟨h3.symm,Zw.mpr ⟨h2.symm,hc⟩⟩,rfl⟩⟩⟩
        calc ((t ×ˢ (t ×ˢ t)).filter (fun w=>w.1≠w.2.1/\w.1≠w.2.2/\w.2.1≠w.2.2)).card
            ≤ (t.biUnion (fun a=>(t.erase a).biUnion (fun b =>
                ((t.erase a).erase b).image (fun c=>(a,b,c))))).card:=Zm hsub6
          _≤∑ a∈t,((t.erase a).biUnion (fun b =>
                ((t.erase a).erase b).image (fun c=>(a,b,c)))).card:=card_biUnion_le
          _≤∑ a∈t,2:=by
              refine Finset.sum_le_sum fun a ha=>?_
              calc ((t.erase a).biUnion (fun b=>((t.erase a).erase b).image (fun c=>(a,b,c)))).card
                  ≤ ∑ b∈t.erase a,(((t.erase a).erase b).image (fun c=>(a,b,c))).card :=card_biUnion_le
                _≤∑ b∈t.erase a,((t.erase a).erase b).card :=
                    Finset.sum_le_sum fun _ _=>card_image_le
                _=∑ _b∈t.erase a,1:=by
                    refine Finset.sum_congr rfl fun b hb=>?_
                    rw[card_erase_of_mem hb,card_erase_of_mem ha,ht3]
                _=2:=by rw[Finset.sum_const,card_erase_of_mem ha,ht3];rfl
          _=6:=by rw[Finset.sum_const,ht3];rfl
    _=6*(Qb S).card:=by rw[Finset.sum_const,smul_eq_mul,mul_comm]
 have hm_half:m≤4*(m/2):=by omega
 calc m*(m-1)*m≤ m*(m-1)*(4*(m/2)):=Yd _ hm_half
   _=4*(m*(m-1)*(m/2)):=by ring
   _≤4*(6*(Qb S).card):=Yd 4 (hOrd_ge.trans hOrd_le)
   _=24*(Qb S).card:=by ring
lemma X5 (N:ℕ) (S:Zf ℕ) (hsub:S⊆Icc 1 N)
  (hp_big:3000000≤ Qc S)
  (hrough:100*Qc S≤99*S.card)
  (hM_log:6*Nat.log 2 N*(Nat.log 2 (2*(Qc S/3))+1)≤ Qc S/3) :
  S.card*Qc S^2≤12000*(Nat.log 2 (2*N)+1)*(Qb S).card:=by
 set m:=S.card;set p:=Qc S;set M:=p/3
 have hM_big:1000000≤ M:=by omega
 obtain⟨P,hPS,⟨a,d,k,hk,hdk,hPeq⟩,hPcard,hPmax⟩:=Wo S (card_pos.mp (by omega))
 have hk_eq:k=p:=by rw[←Qo hk hdk hPeq,hPcard]
 subst hk_eq
 have hd_pos:0< d:=hdk (by omega)
 have hp_le_N:p≤ N:=by have h1:P.card≤(Icc 1 N).card:=Zm (hPS.trans hsub);rw[Nat.card_Icc] at h1;omega
 set Q:=S \ P
 have hQcard:Q.card=m-p:=by have h1:Q.card+P.card=m:=Yb hPS;omega
 set PrimesM:=(Ioc M (2*M)).filter Nat.Prime;have hPrimesM:=Vq M hM_big
 have hper_y:∀ y∈Q,(p/4)*M≤6*(Nat.log 2 (2*M)+1) *((Qb S).filter (fun t=>y∈t/\t.erase y⊆P)).card:=by
  intro y hyQ;obtain⟨hyS,hyP⟩:=Ye.mp hyQ
  have hside_avoid :(∀ t< p/4,d % 2=0->a+t*d∉Qf S y (d/2)) ∨
    (∀ t,3*p/4≤ t->t< p->d % 2=0->a+t*d∉Qf S y (d/2)):=by
   by_contra hboth
   push Not at hboth
   obtain⟨⟨t₁,ht₁,hdeven,hmem1⟩,⟨t₂,ht₂lo,ht₂hi,-,hmem2⟩⟩:=hboth
   have hh_pos:0< d/2:=by omega
   have h2h:2*(d/2)=d:=by omega
   set R:=Qf S y (d/2);have hR_ap:IsAP R:=Wh hh_pos hyS;have hR_le:R.card≤ p:=hPmax R (Qz S y (d/2)) hR_ap;have h1:=(Qu S y (d/2) (a+t₁*d)).mp hmem1;have h2:=(Qu S y (d/2) (a+t₂*d)).mp hmem2
   have hmaps:Set.MapsTo (fun j=>a+t₁*d+j*(d/2))
     ((range (2*(t₂-t₁)+1):Zf ℕ):Set ℕ) (R:Set ℕ):=by
    intro j hj;have hjlt:=mem_range.mp (Zc.mp hj);rw[Zc,Qu S y (d/2)];have hlo:a+t₁*d≤ a+t₁*d+j*(d/2):=Nat.le_add_right _ _
    have hhi:a+t₁*d+j*(d/2)≤ a+t₂*d:=by
     have:j*(d/2)≤2*(t₂-t₁)*(d/2):=Yc _ (by omega)
     have:2*(t₂-t₁)*(d/2)=(t₂-t₁)*d:=by
      calc 2*(t₂-t₁)*(d/2)=(t₂-t₁)*(2*(d/2)):=by ring
        _=(t₂-t₁)*d:=by rw[h2h]
     have:(t₂-t₁)*d+t₁*d=t₂*d:=by rw[←Nat.add_mul];congr 1;omega
     omega
    have hmod_pt:(a+t₁*d+j*(d/2)) % (d/2)=y % (d/2):=by rw[Nat.add_mul_mod_self_right];exact h1.2.1
    have hbetween_in:∀ z,min y (a+t₁*d+j*(d/2))≤ z->z≤ max y (a+t₁*d+j*(d/2)) →
      z % (d/2)=y % (d/2)->z∈S:=by
     intro z hzlo hzhi hzmod
     rcases le_total y (a+t₁*d+j*(d/2)) with hyle|hyge
     ·have hle1:min y (a+t₂*d)≤ z:=by
       rw[Yl (hyle.trans hhi)];rw[Yl hyle] at hzlo;exact hzlo
      have hle2:z≤ max y (a+t₂*d):=by rw[Yi (hyle.trans hhi)];rw[Yi hyle] at hzhi;exact hzhi.trans hhi
      exact h2.2.2 z hle1 hle2 hzmod
     ·have hle1:min y (a+t₁*d)≤ z:=by
       rw[Yj (hlo.trans hyge)];rw[Yj hyge] at hzlo;exact hlo.trans hzlo
      have hle2:z≤ max y (a+t₁*d):=by rw[Yk (hlo.trans hyge)];rw[Yk hyge] at hzhi;exact hzhi
      exact h1.2.2 z hle1 hle2 hzmod
    exact⟨hbetween_in _ (Yq _ _) (Yn _ _) hmod_pt,hmod_pt,hbetween_in⟩
   have hinj:Set.InjOn (fun j=>a+t₁*d+j*(d/2))
     ((range (2*(t₂-t₁)+1):Zf ℕ):Set ℕ):=by
    intro j₁ _ j₂ _ heq;dsimp only at heq
    exact Nat.eq_of_mul_eq_mul_right hh_pos (by omega)
   have hcardR:=card_le_card_of_injOn _ hmaps hinj;rw[card_range] at hcardR;omega
  have hbuild:∀ (IndexSet:Zf ℕ) (goRight:Bool),p/4≤ IndexSet.card →
    (∀ t∈IndexSet,t< p) →
    (∀ t∈IndexSet,d % 2=0->a+t*d∉Qf S y (d/2)) →
    (∀ t∈IndexSet,∀ q∈PrimesM,if goRight then t+q< p else q≤ t) →
    (p/4)*M≤6*(Nat.log 2 (2*M)+1) *((Qb S).filter (fun t=>y∈t/\t.erase y⊆P)).card:=by
   intro IndexSet goRight hIcard hIlt hIavoid hIbound
   let GoodTQ:=IndexSet.biUnion (fun t =>
    (PrimesM.filter (fun q=>¬ (q ∣ max y (a+t*d)-min y (a+t*d)))).image (fun q=>(t,q)))
   have hGoodTQ_ge:6*(Nat.log 2 (2*M)+1)*GoodTQ.card≥(p/4)*M:=by
    have hcardG:GoodTQ.card=∑ t∈IndexSet,(PrimesM.filter (fun q=>¬ (q ∣ max y (a+t*d)-min y (a+t*d)))).card:=by
     rw[card_biUnion]
     ·refine Finset.sum_congr rfl fun t _=>card_image_of_injOn fun q₁ _ q₂ _ h=>congrArg Prod.snd h
     ·intro t₁ _ t₂ _ hne
      simp only[Function.onFun];rw[Zk];intro z hz1 hz2;obtain⟨_,_,rfl⟩:=Zi.mp hz1;obtain⟨_,_,hpair⟩:=Zi.mp hz2;exact hne (congrArg Prod.fst hpair).symm
    have hper_t:∀ t∈IndexSet,M≤6*(Nat.log 2 (2*M)+1) *(PrimesM.filter (fun q=>¬ (q ∣ max y (a+t*d)-min y (a+t*d)))).card:=by
     intro t ht;set diff:=max y (a+t*d)-min y (a+t*d)
     have hne_yt:y≠a+t*d:=fun h=>hyP (h ▸ (hPeq _).mpr ⟨t,hIlt t ht,rfl⟩)
     have hdiff_pos:1≤ diff:=by
      rcases lt_or_gt_of_ne hne_yt with hlt|hgt
      ·rw[show diff=a+t*d-y from by simp[diff,Yi hlt.le,Yl hlt.le]];omega
      ·rw[show diff=y-(a+t*d) from by simp[diff,Yk hgt.le,Yj hgt.le]];omega
     have hdiff_le:diff≤ N:=by
      have hy1:=Zb.mp (hsub hyS);have ht1:=Zb.mp (hsub (hPS ((hPeq _).mpr ⟨t,hIlt t ht,rfl⟩)))
      rcases le_total y (a+t*d) with hle|hge
      ·rw[show diff=a+t*d-y from by simp[diff,Yi hle,Yl hle]];omega
      ·rw[show diff=y-(a+t*d) from by simp[diff,Yk hge,Yj hge]];omega
     have hdiv_card:(PrimesM.filter (fun q=>q ∣ diff)).card≤ Nat.log 2 N:=by
      have hsubP:PrimesM.filter (fun q=>q ∣ diff)⊆diff.primeFactors:=by
       intro q hq;obtain⟨hqM,hqd⟩:=Za.mp hq
       exact Nat.mem_primeFactors.mpr ⟨(Za.mp hqM).2,hqd,by omega⟩
      exact (Zm hsubP).trans ((X1 diff hdiff_pos).trans
       (Nat.log_mono_right hdiff_le))
     have hpart:=card_filter_add_card_filter_not (s:=PrimesM) (p:=fun q=>q ∣ diff)
     have h1:PrimesM.card≤(PrimesM.filter (fun q=>¬ (q ∣ diff))).card+Nat.log 2 N:=by omega
     have hstep:M≤3*(Nat.log 2 (2*M)+1)*(PrimesM.filter (fun q=>¬ (q ∣ diff))).card +3*Nat.log 2 N*(Nat.log 2 (2*M)+1):=by
      calc M≤3*PrimesM.card*(Nat.log 2 (2*M)+1):=hPrimesM
        _≤3*((PrimesM.filter (fun q=>¬ (q ∣ diff))).card+Nat.log 2 N)*(Nat.log 2 (2*M)+1) :=
            Yc _ (Yd 3 h1)
        _=3*(Nat.log 2 (2*M)+1)*(PrimesM.filter (fun q=>¬ (q ∣ diff))).card +
            3*Nat.log 2 N*(Nat.log 2 (2*M)+1):=by ring
     have h2log:2*(3*Nat.log 2 N*(Nat.log 2 (2*M)+1))≤ M:=by
      have heq6:2*(3*Nat.log 2 N*(Nat.log 2 (2*M)+1)) =6*Nat.log 2 N*(Nat.log 2 (2*M)+1):=by ring
      rw[heq6];exact hM_log
     have h2lhs:2*(3*(Nat.log 2 (2*M)+1)*(PrimesM.filter (fun q=>¬ (q ∣ diff))).card) =6*(Nat.log 2 (2*M)+1)*(PrimesM.filter (fun q=>¬ (q ∣ diff))).card:=by ring
     omega
    calc (p/4)*M≤ IndexSet.card*M:=Yc M hIcard
      _=∑ _t∈IndexSet,M:=by rw[Finset.sum_const,smul_eq_mul]
      _≤∑ t∈IndexSet,6*(Nat.log 2 (2*M)+1) *
            (PrimesM.filter (fun q=>¬ (q ∣ max y (a+t*d)-min y (a+t*d)))).card :=
          Finset.sum_le_sum hper_t
      _=6*(Nat.log 2 (2*M)+1)*GoodTQ.card:=by rw[hcardG,Finset.mul_sum]
   let mkTriple:ℕ × ℕ->Zf ℕ:=fun z =>
    {y,a+z.1*d,a+(if goRight then z.1+z.2 else z.1-z.2)*d}
   have hmaps:Set.MapsTo mkTriple (GoodTQ:Set (ℕ × ℕ))
     (((Qb S).filter (fun t=>y∈t/\t.erase y⊆P)):Set (Zf ℕ)):=by
    intro z hztq;obtain⟨t,ht',hzimg⟩:=mem_biUnion.mp (Zc.mp hztq);obtain⟨q,hq',rfl⟩:=Zi.mp hzimg;obtain⟨hqM,hqndvd⟩:=Za.mp hq';obtain⟨hqIoc,hqpr⟩:=Za.mp hqM;obtain⟨hqlo,hqhi⟩:=mem_Ioc.mp hqIoc
    set sIdx:=if goRight then t+q else t-q
    have hsIdx_lt:sIdx< p:=by
     have hb:=hIbound t ht' q hqM
     cases goRight <;> simp only[sIdx,Bool.false_eq_true,↓reduceIte] at hb ⊢
     ·have:=hIlt t ht';omega
     ·exact hb
    have htP:a+t*d∈P:=(hPeq _).mpr ⟨t,hIlt t ht',rfl⟩;have hsP:a+sIdx*d∈P:=(hPeq _).mpr ⟨sIdx,hsIdx_lt,rfl⟩
    have hgap_ts:max (a+t*d) (a+sIdx*d)-min (a+t*d) (a+sIdx*d)=q*d:=by
     have hb:=hIbound t ht' q hqM
     cases goRight <;> simp only[sIdx,Bool.false_eq_true,↓reduceIte] at hb ⊢
     ·have hle:(t-q)*d≤ t*d:=Yc d (Nat.sub_le t q)
      rw[Yk (Nat.add_le_add_left hle a),Yj (Nat.add_le_add_left hle a)]
      have:(t-q)*d+q*d=t*d:=by rw[←Nat.add_mul];congr 1;omega
      omega
     ·have hle:t*d≤(t+q)*d:=Yc d (Nat.le_add_right t q)
      rw[Yi (Nat.add_le_add_left hle a),Yl (Nat.add_le_add_left hle a)];rw[Nat.add_mul];omega
    have hne_yt:y≠a+t*d:=fun h=>hyP (h ▸ htP)
    have hne_ys:y≠a+sIdx*d:=fun h=>hyP (h ▸ hsP)
    have hne_ts:a+t*d≠a+sIdx*d:=by
     have hpos:0< q*d:=Nat.mul_pos (by omega) hd_pos
     intro h;rw[h,max_self,min_self,Nat.sub_self] at hgap_ts;omega
    have hbad:Qk S {y,a+t*d,a+sIdx*d}:=by
     refine⟨?_,?_,?_⟩
     ·rw[card_insert_of_notMem,card_insert_of_notMem,card_singleton]
      ·exact Finset.notMem_singleton.mpr hne_ts
      ·simp[hne_yt,hne_ys]
     ·intro x hx;simp only[Zx,Zj] at hx
      rcases hx with rfl|rfl|rfl
      ·exact hyS
      ·exact hPS htP
      ·exact hPS hsP
     ·rintro A ⟨aA,δ,kA,hkA,hdA,hAeq⟩ hAS hsubA
      have hyA:y∈A:=hsubA (by simp)
      have htA:a+t*d∈A:=hsubA (by simp)
      have hsA:a+sIdx*d∈A:=hsubA (by simp)
      have hkA2:2≤ kA:=by
       have h3:({y,a+t*d,a+sIdx*d}:Zf ℕ).card≤ A.card:=Zm hsubA
       have hc3:({y,a+t*d,a+sIdx*d}:Zf ℕ).card=3:=by
        rw[card_insert_of_notMem,card_insert_of_notMem,card_singleton]
        ·exact Finset.notMem_singleton.mpr hne_ts
        ·simp[hne_yt,hne_ys]
       rw[Qo hkA hdA hAeq] at h3;omega
      have hδ_pos:0<δ:=hdA (by omega)
      obtain⟨iy,-,hiy⟩:=(hAeq y).mp hyA;obtain⟨it,-,hit⟩:=(hAeq (a+t*d)).mp htA;obtain⟨is_,-,his⟩:=(hAeq (a+sIdx*d)).mp hsA
      have hδ_qd:δ ∣ q*d:=by
       rw[←hgap_ts]
       rcases lt_or_gt_of_ne hne_ts with hlt|hgt
       ·rw[Yi hlt.le,Yl hlt.le]
        have hidx:it< is_:=Nat.lt_of_mul_lt_mul_right (by omega:it*δ< is_*δ)
        refine⟨is_-it,?_⟩
        rw[hit,his];have:aA+is_*δ-(aA+it*δ)=(is_-it)*δ:=by rw[Nat.sub_mul];omega
        rw[this,mul_comm]
       ·rw[Yk hgt.le,Yj hgt.le]
        have hidx:is_< it:=Nat.lt_of_mul_lt_mul_right (by omega:is_*δ< it*δ)
        refine⟨it-is_,?_⟩
        rw[hit,his];have:aA+it*δ-(aA+is_*δ)=(it-is_)*δ:=by rw[Nat.sub_mul];omega
        rw[this,mul_comm]
      have hδ_yt:δ ∣ max y (a+t*d)-min y (a+t*d):=by
       rcases lt_or_gt_of_ne hne_yt with hlt|hgt
       ·rw[Yi hlt.le,Yl hlt.le]
        have hidx:iy< it:=Nat.lt_of_mul_lt_mul_right (by omega:iy*δ< it*δ)
        refine⟨it-iy,?_⟩
        rw[hiy,hit];have:aA+it*δ-(aA+iy*δ)=(it-iy)*δ:=by rw[Nat.sub_mul];omega
        rw[this,mul_comm]
       ·rw[Yk hgt.le,Yj hgt.le]
        have hidx:it< iy:=Nat.lt_of_mul_lt_mul_right (by omega:it*δ< iy*δ)
        refine⟨iy-it,?_⟩
        rw[hiy,hit];have:aA+iy*δ-(aA+it*δ)=(iy-it)*δ:=by rw[Nat.sub_mul];omega
        rw[this,mul_comm]
      by_cases hδd:δ ∣ d
      ·obtain⟨c,hc⟩:=hδd
       have hc_pos:0< c:=by
        rcases Nat.eq_zero_or_pos c with rfl|hpos
        ·omega
        ·exact hpos
       rcases lt_or_ge c 3 with hclt3|hcge3
       ·rcases show c=1\/c=2 by omega with rfl|rfl
        ·rw[mul_one] at hc;subst hc
         have hAsubR:=Qv hAS hd_pos hAeq htA;have hPsubR:=Qv hPS hd_pos hPeq htP
         have hcard_gt:p+1≤(Qf S (a+t*d) d).card:=by have h1:=Zm (insert_subset_iff.mpr ⟨hAsubR hyA,hPsubR⟩);rw[card_insert_of_notMem hyP,hPcard] at h1;exact h1
         have hle:=hPmax _ (Qz _ _ _) (Wh hd_pos (hPS htP));omega
        ·have hdeven:d % 2=0:=by omega
         have hδhalf:δ=d/2:=by omega
         subst hδhalf;exact hIavoid t ht' hdeven (Qv hAS hδ_pos hAeq hyA htA)
       ·
        have hspan:q*c≤ max it is_-min it is_:=by
         have hdiffA:(max it is_-min it is_)*δ=q*d:=by
          rw[←hgap_ts]
          rcases lt_or_gt_of_ne hne_ts with hlt|hgt
          ·rw[Yi hlt.le,Yl hlt.le]
           have hidx:it< is_:=Nat.lt_of_mul_lt_mul_right (by omega:it*δ< is_*δ)
           rw[Yi hidx.le,Yl hidx.le,hit,his,Nat.sub_mul];omega
          ·rw[Yk hgt.le,Yj hgt.le]
           have hidx:is_< it:=Nat.lt_of_mul_lt_mul_right (by omega:is_*δ< it*δ)
           rw[Yk hidx.le,Yj hidx.le,hit,his,Nat.sub_mul];omega
         have heqc:(max it is_-min it is_)*δ=(q*c)*δ:=by rw[hdiffA,hc];ring
         exact le_of_eq (Nat.eq_of_mul_eq_mul_right hδ_pos heqc).symm
        have hA_card:A.card=kA:=Qo hkA hdA hAeq;have hA_le:kA≤ p:=hA_card ▸ hPmax A hAS ⟨aA,δ,kA,hkA,hdA,hAeq⟩
        have hmax_lt:max it is_< kA:=by
         obtain⟨it',hit',heq1⟩:=(hAeq (a+t*d)).mp htA;obtain⟨is',his',heq2⟩:=(hAeq (a+sIdx*d)).mp hsA
         have e1:it=it':=Nat.eq_of_mul_eq_mul_right hδ_pos (by omega)
         have e2:is_=is':=Nat.eq_of_mul_eq_mul_right hδ_pos (by omega)
         rw[e1,e2];exact max_lt hit' his'
        have h3q:3*(M+1)≤ q*c:=by
         calc 3*(M+1)≤ c*q:=Nat.mul_le_mul hcge3 (by omega)
           _=q*c:=mul_comm c q
        omega
      ·
       set h:=Nat.gcd d δ;have hh_pos:0< h:=Nat.gcd_pos_of_pos_left δ hd_pos;set δ':=δ/h;have hδ'h:δ'*h=δ:=Nat.div_mul_cancel (Nat.gcd_dvd_right d δ);have hdh:(d/h)*h=d:=Nat.div_mul_cancel (Nat.gcd_dvd_left d δ)
       have hδ'2:2≤δ':=by
        by_contra hlt2;have hlt2':δ'<2:=Nat.lt_of_not_ge hlt2
        rcases Nat.eq_zero_or_pos δ' with h0|hpos
        ·rw[h0] at hδ'h;omega
        ·have h1:δ'=1:=le_antisymm (Nat.lt_succ_iff.mp hlt2') hpos
         rw[h1,one_mul] at hδ'h;exact hδd (hδ'h ▸ Nat.gcd_dvd_left d δ)
       have hcop:Nat.Coprime δ' (d/h):=by rw[Nat.coprime_comm];exact Nat.coprime_div_gcd_div_gcd hh_pos
       have hδ'_q:δ' ∣ q:=by
        obtain⟨u,hu⟩:=hδ_qd
        have hdvd1:δ' ∣ q*(d/h):=⟨u,Nat.eq_of_mul_eq_mul_right hh_pos (by
         calc (q*(d/h))*h=q*((d/h)*h):=by ring
           _=q*d:=by rw[hdh]
           _=δ*u:=hu
           _=(δ'*h)*u:=by rw[←hδ'h]
           _=(δ'*u)*h:=by ring)⟩
        exact hcop.dvd_of_dvd_mul_right hdvd1
       have hδ'_eq_q:δ'=q:=(hqpr.eq_one_or_self_of_dvd δ' hδ'_q).resolve_left (by omega)
       have hq_dvd_δ:q ∣ δ:=⟨h,by rw[←hδ'_eq_q,hδ'h]⟩
       exact hqndvd (hq_dvd_δ.trans hδ_yt)
    refine Zc.mpr (Za.mpr ⟨(Qh S _).mpr hbad,by simp[mkTriple],?_⟩)
    intro x hx;obtain⟨hxy,hxin⟩:=Zw.mp hx;simp only[mkTriple,Zx,Zj] at hxin
    rcases hxin with rfl|rfl|rfl
    ·exact absurd rfl hxy
    ·exact htP
    ·exact hsP
   have hinj:Set.InjOn mkTriple (GoodTQ:Set (ℕ × ℕ)):=by
    intro z₁ h1 z₂ h2 heq;obtain⟨t₁,ht₁',hz1⟩:=mem_biUnion.mp (Zc.mp h1);obtain⟨q₁,hq₁',rfl⟩:=Zi.mp hz1;obtain⟨t₂,ht₂',hz2⟩:=mem_biUnion.mp (Zc.mp h2);obtain⟨q₂,hq₂',rfl⟩:=Zi.mp hz2;have hq1M:=(Za.mp hq₁').1;have hq2M:=(Za.mp hq₂').1
    have hq1pos:0< q₁:=by have:=(mem_Ioc.mp (Za.mp hq1M).1).1;omega
    have hq2pos:0< q₂:=by have:=(mem_Ioc.mp (Za.mp hq2M).1).1;omega
    have hb1:=hIbound t₁ ht₁' q₁ hq1M;have hb2:=hIbound t₂ ht₂' q₂ hq2M
    have hny1:y∉({a+t₁*d,a+(if goRight then t₁+q₁ else t₁-q₁)*d}:Zf ℕ):=by
     simp only[Zx,Zj,not_or]
     refine⟨fun h=>hyP (h ▸ (hPeq _).mpr ⟨t₁,hIlt t₁ ht₁',rfl⟩),fun h=>hyP (h ▸ (hPeq _).mpr ⟨_,?_,rfl⟩)⟩
     cases goRight <;> simp only[Bool.false_eq_true,↓reduceIte] at hb1 ⊢
     ·have:=hIlt t₁ ht₁';omega
     ·exact hb1
    have hny2:y∉({a+t₂*d,a+(if goRight then t₂+q₂ else t₂-q₂)*d}:Zf ℕ):=by
     simp only[Zx,Zj,not_or]
     refine⟨fun h=>hyP (h ▸ (hPeq _).mpr ⟨t₂,hIlt t₂ ht₂',rfl⟩),fun h=>hyP (h ▸ (hPeq _).mpr ⟨_,?_,rfl⟩)⟩
     cases goRight <;> simp only[Bool.false_eq_true,↓reduceIte] at hb2 ⊢
     ·have:=hIlt t₂ ht₂';omega
     ·exact hb2
    have herase:({a+t₁*d,a+(if goRight then t₁+q₁ else t₁-q₁)*d}:Zf ℕ) ={a+t₂*d,a+(if goRight then t₂+q₂ else t₂-q₂)*d}:=by
     have h0:=congrArg (fun s=>erase s y) heq
     dsimp only[mkTriple] at h0;rw[erase_insert hny1,erase_insert hny2] at h0;exact h0
    have h1m:a+t₁*d∈({a+t₂*d,a+(if goRight then t₂+q₂ else t₂-q₂)*d}:Zf ℕ):=by rw[←herase];simp
    have h2m:a+t₂*d∈({a+t₁*d,a+(if goRight then t₁+q₁ else t₁-q₁)*d}:Zf ℕ):=by rw[herase];simp
    have h3m:a+(if goRight then t₁+q₁ else t₁-q₁)*d ∈
      ({a+t₂*d,a+(if goRight then t₂+q₂ else t₂-q₂)*d}:Zf ℕ):=by
     rw[←herase];simp
    have h4m:a+(if goRight then t₂+q₂ else t₂-q₂)*d ∈
      ({a+t₁*d,a+(if goRight then t₁+q₁ else t₁-q₁)*d}:Zf ℕ):=by
     rw[herase];simp
    simp only[Zx,Zj] at h1m h2m h3m h4m
    cases goRight
    ·simp only[Bool.false_eq_true,↓reduceIte] at hb1 hb2 h1m h2m h3m h4m
     have hlt1:a+(t₁-q₁)*d< a+t₁*d:=by
      have:=Nat.mul_lt_mul_of_pos_right (by omega:t₁-q₁< t₁) hd_pos;omega
     have hlt2:a+(t₂-q₂)*d< a+t₂*d:=by
      have:=Nat.mul_lt_mul_of_pos_right (by omega:t₂-q₂< t₂) hd_pos;omega
     have et:t₁=t₂:=Nat.eq_of_mul_eq_mul_right hd_pos (by omega)
     have es:t₁-q₁=t₂-q₂:=Nat.eq_of_mul_eq_mul_right hd_pos (by omega)
     ext <;> dsimp <;> omega
    ·simp only[↓reduceIte] at hb1 hb2 h1m h2m h3m h4m
     have hlt1:a+t₁*d< a+(t₁+q₁)*d:=by
      have:=Nat.mul_lt_mul_of_pos_right (by omega:t₁< t₁+q₁) hd_pos;omega
     have hlt2:a+t₂*d< a+(t₂+q₂)*d:=by
      have:=Nat.mul_lt_mul_of_pos_right (by omega:t₂< t₂+q₂) hd_pos;omega
     have et:t₁=t₂:=Nat.eq_of_mul_eq_mul_right hd_pos (by omega)
     have es:t₁+q₁=t₂+q₂:=Nat.eq_of_mul_eq_mul_right hd_pos (by omega)
     ext <;> dsimp <;> omega
   have hcard_le:=card_le_card_of_injOn mkTriple hmaps hinj;exact hGoodTQ_ge.trans (Yd _ hcard_le)
  rcases hside_avoid with hR|hL
  ·refine hbuild (range (p/4)) true (by rw[card_range])
    (fun t ht=>by rw[mem_range] at ht;omega)
    (fun t ht=>hR t (mem_range.mp ht)) ?_
   intro t ht q hqM;have htlt:=mem_range.mp ht;have hqhi:=(mem_Ioc.mp (Za.mp hqM).1).2;simp only[↓reduceIte];omega
  ·refine hbuild (Ico (3*p/4) p) false (by rw[Nat.card_Ico];omega)
    (fun t ht=>(mem_Ico.mp ht).2)
    (fun t ht=>hL t (mem_Ico.mp ht).1 (mem_Ico.mp ht).2) ?_
   intro t ht q hqM;have htlo:=(mem_Ico.mp ht).1;have hqhi:=(mem_Ioc.mp (Za.mp hqM).1).2;simp only[Bool.false_eq_true,↓reduceIte];omega
 have hdisj:Set.PairwiseDisjoint (Q:Set ℕ)
   (fun y=>(Qb S).filter (fun t=>y∈t/\t.erase y⊆P)):=by
  intro y₁ hy₁ y₂ hy₂ hne;simp only[Function.onFun];rw[Zk];intro t ht1 ht2;have h1:=(Za.mp ht1).2;have h2:=(Za.mp ht2).2;have hy2P:y₂∉P:=(Ye.mp (Zc.mp hy₂)).2;exact hy2P (h1.2 (Zw.mpr ⟨hne.symm,h2.1⟩))
 have hsub_bt:Q.biUnion (fun y=>(Qb S).filter (fun t=>y∈t/\t.erase y⊆P))⊆Qb S:=by intro t ht;obtain⟨y,-,hty⟩:=mem_biUnion.mp ht;exact (Za.mp hty).1
 have hsum:(m-p)*((p/4)*M)≤6*(Nat.log 2 (2*M)+1)*(Qb S).card:=by
  calc (m-p)*((p/4)*M)=∑ _y∈Q,(p/4)*M:=by rw[Finset.sum_const,hQcard,smul_eq_mul]
    _≤∑ y∈Q,6*(Nat.log 2 (2*M)+1) *
          ((Qb S).filter (fun t=>y∈t/\t.erase y⊆P)).card:=Finset.sum_le_sum hper_y
    _=6*(Nat.log 2 (2*M)+1) *
          (Q.biUnion (fun y=>(Qb S).filter (fun t=>y∈t/\t.erase y⊆P))).card:=by
        rw[←Finset.mul_sum,card_biUnion hdisj]
    _≤6*(Nat.log 2 (2*M)+1)*(Qb S).card :=
        Yd _ (Zm hsub_bt)
 have hlog_mono:Nat.log 2 (2*M)≤ Nat.log 2 (2*N):=Nat.log_mono_right (by omega)
 have hp1:p≤5*(p/4):=by omega
 have hp2:p≤4*M:=by omega
 have hmp:m≤100*(m-p):=by omega
 calc m*p^2=m*(p*p):=by ring
   _≤(100*(m-p))*((5*(p/4))*(4*M)) :=
       Nat.mul_le_mul hmp (Nat.mul_le_mul hp1 hp2)
   _=2000*((m-p)*((p/4)*M)):=by ring
   _≤2000*(6*(Nat.log 2 (2*M)+1)*(Qb S).card):=Yd 2000 hsum
   _=12000*(Nat.log 2 (2*M)+1)*(Qb S).card:=by ring
   _≤12000*(Nat.log 2 (2*N)+1)*(Qb S).card :=
       Yc _ (Yd 12000 (Nat.add_le_add_right hlog_mono 1))
lemma Kd (N k s q₀:ℕ) (hN:1≤ N) (hq₀:1≤ q₀) (hk:4*q₀+4≤ k)
  (Q_near:Zf (Zf ℕ)) (hQ:Zt N Q_near)
  (hsize:∀ S∈Q_near,k≤ S.card/\S.card≤ s)
  (hnear:∀ S∈Q_near,1≤ S.card-Qc S/\S.card-Qc S≤ q₀) :
  (Q_near.card:ℝ) ≤8*((q₀:ℝ)+1)*(N:ℝ)^2*(log (N:ℝ)+1)/(k:ℝ) +16*((q₀:ℝ)+1+(s:ℝ))*(N:ℝ)^2/(k:ℝ)^2:=by
 set D:=2*N/k
 have hP_ex:∀ S∈Q_near,∃ (P:Zf ℕ) (a d:ℕ),P⊆S/\P.card=Qc S/\1≤ d/\d≤ D ∧
   (∀ x,x∈P↔∃ i< Qc S,x=a+i*d) ∧
   (∀ A⊆S,IsAP A->A.card≤ Qc S):=by
  intro S hS;have hSz:=hsize S hS;have hNr:=hnear S hS
  obtain⟨P,hPS,⟨a,d,l,hl,hdl,hPeq⟩,hPcard,hPmax⟩:=Wo S (card_pos.mp (by omega))
  have hl_eq:l=Qc S:=by rw[←Qo hl hdl hPeq,hPcard]
  subst hl_eq
  have hd1:1≤ d:=hdl (by omega)
  have hsubS:S⊆Icc 1 N:=Zy.mp (hQ.1 hS);have hmm:=Wa hl hdl hPeq;have ha1:=(Zb.mp (hsubS (hPS hmm.1))).1;have hbN:=(Zb.mp (hsubS (hPS hmm.2.1))).2
  have hkd:k*d≤2*N:=by
   have h1:(Qc S-1)*d≤ N:=by omega
   have h2:k≤2*(Qc S-1):=by omega
   calc k*d≤(2*(Qc S-1))*d:=Yc d h2
     _=2*((Qc S-1)*d):=by ring
     _≤2*N:=Yd 2 h1
  have hdD:d≤ D:=(Nat.le_div_iff_mul_le (by omega:0< k)).mpr (by rw[mul_comm];exact hkd)
  exact⟨P,a,d,hPS,hPcard,hd1,hdD,hPeq,hPmax⟩
 let getP:Zf ℕ->Zf ℕ:=fun S=>if hS:S∈Q_near then (hP_ex S hS).choose else ∅
 let getA:Zf ℕ->ℕ:=fun S=>if hS:S∈Q_near then (hP_ex S hS).choose_spec.choose else 0
 let getD:Zf ℕ->ℕ:=fun S=>if hS:S∈Q_near then (hP_ex S hS).choose_spec.choose_spec.choose else 0
 have hget:∀ S∈Q_near,getP S⊆S/\(getP S).card=Qc S/\1≤ getD S/\getD S≤ D ∧
   (∀ x,x∈getP S↔∃ i< Qc S,x=getA S+i*getD S) ∧
   (∀ A⊆S,IsAP A->A.card≤ Qc S):=by
  intro S hS;simpa only [getP,getA,getD,dif_pos hS] using (hP_ex S hS).choose_spec.choose_spec.choose_spec
 have hclean_triples:∀ S∈Q_near,∀ w∈S \ getP S,k/2≤((Qb S).filter (fun t=>∃ x∈getP S,t={w,x,x+getD S})).card:=by
  intro S hS w hw;obtain⟨hPS,hPcard,hd1,-,hPeq,hPmax⟩:=hget S hS;have hSz:=hsize S hS;have hNr:=hnear S hS;set p:=Qc S;set a:=getA S;set d:=getD S;set R:=S \ getP S
  have hRcard:R.card≤ q₀:=by have h1:R.card+(getP S).card=S.card:=Yb hPS;omega
  obtain⟨hwS,hwP⟩:=Ye.mp hw
  set Clean:=(range (p-1)).filter (fun i =>
   ∀ u∈R,¬ (a+i*d< u/\u< a+(i+1)*d))
  have hClean_ge:k/2≤ Clean.card:=by
   set Dirty:=(range (p-1)).filter (fun i =>
    ∃ u∈R,a+i*d< u/\u< a+(i+1)*d)
   have hDirty_le:Dirty.card≤ R.card:=by
    have hch:∀ i∈Dirty,∃ u∈R,a+i*d< u/\u< a+(i+1)*d:=fun i hi=>(Za.mp hi).2
    let fu:ℕ->ℕ:=fun i=>if hi:i∈Dirty then (hch i hi).choose else 0
    have hfu:∀ i∈Dirty,fu i∈R/\a+i*d< fu i/\fu i< a+(i+1)*d:=by intro i hi;simpa [fu,dif_pos hi] using (hch i hi).choose_spec
    refine card_le_card_of_injOn fu (fun i hi=>Zc.mpr (hfu i (Zc.mp hi)).1) ?_
    intro i₁ hi₁ i₂ hi₂ heq;have h1:=hfu i₁ (Zc.mp hi₁);have h2:=hfu i₂ (Zc.mp hi₂);rw[heq] at h1
    have hlt1:i₁< i₂+1:=Nat.lt_of_mul_lt_mul_right (by omega:i₁*d<(i₂+1)*d)
    have hlt2:i₂< i₁+1:=Nat.lt_of_mul_lt_mul_right (by omega:i₂*d<(i₁+1)*d)
    omega
   have heqD:(range (p-1)).filter (fun i=>¬ ∀ u∈R,¬ (a+i*d< u/\u< a+(i+1)*d))=Dirty:=by ext i;simp only[Dirty,Za,not_forall,not_not,exists_prop]
   have hpart:Clean.card+Dirty.card=p-1:=by
    have h0:=card_filter_add_card_filter_not (s:=range (p-1))
     (p:=fun i=>∀ u∈R,¬ (a+i*d< u/\u< a+(i+1)*d))
    rw[heqD,card_range] at h0;exact h0
   omega
  have hmaps:Set.MapsTo (fun i=>({w,a+i*d,a+i*d+d}:Zf ℕ))
    (Clean:Set ℕ) (((Qb S).filter (fun t=>∃ x∈getP S,t={w,x,x+d})):Set (Zf ℕ)):=by
   intro i hi;obtain⟨hiR,hcl⟩:=Za.mp (Zc.mp hi);have hilt:i< p-1:=mem_range.mp hiR
   have hxP:a+i*d∈getP S:=(hPeq _).mpr ⟨i,by omega,rfl⟩
   have hx1P:a+i*d+d∈getP S:=(hPeq _).mpr ⟨i+1,by omega,by ring⟩
   have hadj:∀ u∈S,¬ (min (a+i*d) (a+i*d+d)< u/\u< max (a+i*d) (a+i*d+d)):=by
    intro u huS hbtw;rw[Yl (Nat.le_add_right _ _),Yi (Nat.le_add_right _ _)] at hbtw
    by_cases huP:u∈getP S
    ·obtain⟨j,-,rfl⟩:=(hPeq u).mp huP
     have h1:i*d< j*d:=by omega
     have h2:j*d<(i+1)*d:=by
      have hmul:(i+1)*d=i*d+d:=by ring
      omega
     have:=Nat.lt_of_mul_lt_mul_right h1
     have:=Nat.lt_of_mul_lt_mul_right h2
     omega
    ·have huR:u∈R:=Ye.mpr ⟨huS,huP⟩
     have:=hcl u huR
     have hmul:a+(i+1)*d=a+i*d+d:=by ring
     rw[hmul] at this;exact this hbtw
   have hw_not_run:w∉Qf S (a+i*d) d:=by
    intro hwrun;have hPsubR:getP S⊆Qf S (a+i*d) d:=Qv hPS hd1 hPeq hxP
    have hgt:p+1≤(Qf S (a+i*d) d).card:=by have h1:=Zm (insert_subset_iff.mpr ⟨hwrun,hPsubR⟩);rw[card_insert_of_notMem hwP,hPcard] at h1;exact h1
    have hle:=hPmax _ (Qz _ _ _) (Wh hd1 (hPS hxP));omega
   have hbad:Qk S {a+i*d,a+i*d+d,w}:=by
    have h:=Wp (hPS hxP) (hPS hx1P) hwS (by omega) hadj
    rw[Yl (Nat.le_add_right _ _),Yi (Nat.le_add_right _ _)] at h
    have hsub:a+i*d+d-(a+i*d)=d:=by omega
    rw[hsub] at h;exact h hw_not_run
   have heqset:({w,a+i*d,a+i*d+d}:Zf ℕ)={a+i*d,a+i*d+d,w}:=by ext z;simp;tauto
   rw[Zc,Za];dsimp only;exact⟨(Qh S _).mpr (heqset ▸ hbad),a+i*d,hxP,rfl⟩
  have hinj:Set.InjOn (fun i=>({w,a+i*d,a+i*d+d}:Zf ℕ)) (Clean:Set ℕ):=by
   intro i₁ h1 i₂ h2 heq;have hi1:=mem_range.mp (Za.mp (Zc.mp h1)).1;have hi2:=mem_range.mp (Za.mp (Zc.mp h2)).1
   have hnw1:w∉({a+i₁*d,a+i₁*d+d}:Zf ℕ):=by
    simp only[Zx,Zj,not_or]
    exact⟨fun h=>hwP (h ▸ (hPeq _).mpr ⟨i₁,by omega,rfl⟩),fun h=>hwP (h ▸ (hPeq _).mpr ⟨i₁+1,by omega,by ring⟩)⟩
   have hnw2:w∉({a+i₂*d,a+i₂*d+d}:Zf ℕ):=by
    simp only[Zx,Zj,not_or]
    exact⟨fun h=>hwP (h ▸ (hPeq _).mpr ⟨i₂,by omega,rfl⟩),fun h=>hwP (h ▸ (hPeq _).mpr ⟨i₂+1,by omega,by ring⟩)⟩
   have herase:({a+i₁*d,a+i₁*d+d}:Zf ℕ)={a+i₂*d,a+i₂*d+d}:=by
    have:=congrArg (fun s=>erase s w) heq
    simpa [erase_insert hnw1,erase_insert hnw2] using this
   have h1m:a+i₁*d∈({a+i₂*d,a+i₂*d+d}:Zf ℕ):=by rw[←herase];simp
   have h2m:a+i₂*d∈({a+i₁*d,a+i₁*d+d}:Zf ℕ):=by rw[herase];simp
   simp only[Zx,Zj] at h1m h2m
   exact Nat.eq_of_mul_eq_mul_right hd1 (by omega)
  exact hClean_ge.trans (card_le_card_of_injOn _ hmaps hinj)
 have hpart:Q_near.card=∑ d∈Icc 1 D,(Q_near.filter (fun S=>getD S=d)).card:=by
  rw[←card_biUnion]
  ·congr 1;ext S
   simp only[mem_biUnion,Zb,Za]
   constructor
   ·intro hS;obtain⟨-,-,h1,h2,-⟩:=hget S hS;exact⟨getD S,⟨h1,h2⟩,hS,rfl⟩
   ·rintro⟨_,_,hS,_⟩;exact hS
  ·intro d₁ _ d₂ _ hne
   simp only[Function.onFun];rw[Zk];intro S h1 h2;exact hne ((Za.mp h1).2.symm.trans (Za.mp h2).2)
 have hper_d:∀ d∈Icc 1 D,(Q_near.filter (fun S=>getD S=d)).card*(k/2) ≤(q₀+1)*N*(N/d+1)+s*N:=by
  intro d hd;have hd1:=(Zb.mp hd).1
  set Gd:=Q_near.filter (fun S=>getD S=d)
  rcases Gd.eq_empty_or_nonempty with hGd0|⟨S₀,hS₀⟩
  ·rw[hGd0,card_empty,zero_mul];exact Nat.zero_le _
  have hS₀Q:=(Za.mp hS₀).1;have hS₀d:=(Za.mp hS₀).2;obtain⟨hP₀S,hP₀card,-,-,hP₀eq,-⟩:=hget S₀ hS₀Q;set Res:=insert (getA S₀ % d) ((S₀ \ getP S₀).image (· % d))
  have hRes_card:Res.card≤ q₀+1:=by
   have h1:(S₀ \ getP S₀).card+(getP S₀).card=S₀.card:=Yb hP₀S;have h2:=(hnear S₀ hS₀Q).2
   calc Res.card≤((S₀ \ getP S₀).image (· % d)).card+1:=card_insert_le _ _
     _≤(S₀ \ getP S₀).card+1:=Nat.add_le_add_right card_image_le 1
     _≤ q₀+1:=by omega
  set Gd1:=Gd.filter (fun S=>getA S % d∈Res)
  set Gd2:=Gd.filter (fun S=>¬ (getA S % d∈Res))
  have hGpart:Gd.card=Gd1.card+Gd2.card :=(card_filter_add_card_filter_not (s:=Gd) (p:=fun S=>getA S % d∈Res)).symm
  have hGd1:Gd1.card*(k/2)≤(q₀+1)*N*(N/d+1):=by
   let W:Zf ℕ->ℕ:=fun S =>
    if hS:S∈Gd1 then
     have hSQ:=(Za.mp (Za.mp hS).1).1
     have hne:(S \ getP S).Nonempty:=by
      have h1:(S \ getP S).card+(getP S).card=S.card:=Yb (hget S hSQ).1
      have:=(hnear S hSQ).1;have:=(hget S hSQ).2.1
      exact card_pos.mp (by omega)
     hne.choose
    else 0
   let B1:Zf ℕ->Zf (Zf ℕ):=fun S =>
    (Qb S).filter (fun t=>∃ x∈getP S,t={W S,x,x+d})
   have hdisj1:Set.PairwiseDisjoint (Gd1:Set (Zf ℕ)) B1:=by
    intro S hS T hT hST;simp only[Function.onFun];rw[Zk];intro t htS htT;have hSQ:=(Za.mp (Za.mp (Zc.mp hS)).1).1;have hTQ:=(Za.mp (Za.mp (Zc.mp hT)).1).1
    exact We hQ hSQ hTQ hST
     ((Qh S t).mp (Za.mp htS).1)
     ((Qh T t).mp (Za.mp htT).1).2.1
   let Pool1:=((Icc 1 N) ×ˢ ((Icc 1 N).filter (fun x=>x % d∈Res))).image
    (fun z=>({z.1,z.2,z.2+d}:Zf ℕ))
   have hsub1:Gd1.biUnion B1⊆Pool1:=by
    intro t ht;obtain⟨S,hS,htB⟩:=mem_biUnion.mp ht;have hSGd:=(Za.mp hS).1;have hSres:=(Za.mp hS).2;have hSQ:=(Za.mp hSGd).1;have hSd:=(Za.mp hSGd).2;obtain⟨x,hxP,rfl⟩:=(Za.mp htB).2
    have hWmem:W S∈S \ getP S:=by simp only[W,dif_pos hS];exact Exists.choose_spec _
    have hsubS:S⊆Icc 1 N:=Zy.mp (hQ.1 hSQ);have hWI:W S∈Icc 1 N:=hsubS (Ye.mp hWmem).1;have hxI:x∈Icc 1 N:=hsubS ((hget S hSQ).1 hxP)
    have hxmod:x % d∈Res:=by obtain⟨i,-,rfl⟩:=((hget S hSQ).2.2.2.2.1 x).mp hxP;rw[hSd,Nat.add_mul_mod_self_right];exact hSres
    exact Zi.mpr ⟨(W S,x),Zh.mpr ⟨hWI,Za.mpr ⟨hxI,hxmod⟩⟩,rfl⟩
   have hPool1_card:Pool1.card≤(q₀+1)*N*(N/d+1):=by
    have hfilt:((Icc 1 N).filter (fun x=>x % d∈Res)).card≤ Res.card*(N/d+1):=by
     have hsubR:(Icc 1 N).filter (fun x=>x % d∈Res) ⊆
       Res.biUnion (fun r=>(Icc 1 N).filter (fun x=>x % d=r)):=by
      intro x hx;obtain⟨hxI,hxr⟩:=Za.mp hx;exact mem_biUnion.mpr ⟨x % d,hxr,Za.mpr ⟨hxI,rfl⟩⟩
     calc ((Icc 1 N).filter (fun x=>x % d∈Res)).card
         ≤ (Res.biUnion (fun r=>(Icc 1 N).filter (fun x=>x % d=r))).card:=Zm hsubR
       _≤∑ r∈Res,((Icc 1 N).filter (fun x=>x % d=r)).card:=card_biUnion_le
       _≤∑ _r∈Res,(N/d+1):=by
           refine Finset.sum_le_sum fun r _=>?_
           have hinj:Set.InjOn (fun x=>x/d) (((Icc 1 N).filter (fun x=>x % d=r)):Set ℕ):=by intro x hx y hy hxy;dsimp only at hxy;have m1:=(Za.mp (Zc.mp hx)).2;have m2:=(Za.mp (Zc.mp hy)).2;have e1:=Nat.div_add_mod x d;have e2:=Nat.div_add_mod y d;rw[hxy,m1,←m2] at e1;omega
           have hmaps:Set.MapsTo (fun x=>x/d) (((Icc 1 N).filter (fun x=>x % d=r)):Set ℕ)
               ((range (N/d+1):Zf ℕ):Set ℕ):=by
             intro x hx;have hxN:=(Zb.mp (Za.mp (Zc.mp hx)).1).2;exact Zc.mpr (mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hxN)))
           exact (card_le_card_of_injOn _ hmaps hinj).trans (by rw[card_range])
       _=Res.card*(N/d+1):=by rw[Finset.sum_const,smul_eq_mul]
    calc Pool1.card≤((Icc 1 N) ×ˢ ((Icc 1 N).filter (fun x=>x % d∈Res))).card:=card_image_le
      _=N*((Icc 1 N).filter (fun x=>x % d∈Res)).card:=by rw[card_product,Nat.card_Icc];simp
      _≤ N*(Res.card*(N/d+1)):=Yd N hfilt
      _=Res.card*N*(N/d+1):=by ring
      _≤(q₀+1)*N*(N/d+1):=Yc _ (Yc N hRes_card)
   calc Gd1.card*(k/2)=∑ _S∈Gd1,(k/2):=by rw[Finset.sum_const,smul_eq_mul]
     _≤∑ S∈Gd1,(B1 S).card:=by
         refine Finset.sum_le_sum fun S hS=>?_
         have hSGd:=(Za.mp hS).1;have hSQ:=(Za.mp hSGd).1;have hSd:=(Za.mp hSGd).2
         have hWmem:W S∈S \ getP S:=by simp only[W,dif_pos hS];exact Exists.choose_spec _
         simpa only [B1,hSd] using hclean_triples S hSQ (W S) hWmem
     _=(Gd1.biUnion B1).card:=(card_biUnion hdisj1).symm
     _≤ Pool1.card:=Zm hsub1
     _≤(q₀+1)*N*(N/d+1):=hPool1_card
  have hGd2:Gd2.card*(k/2)≤ s*N:=by
   have hW2_ex:∀ S∈Gd2,∃ w∈S \ getP S,w∈S₀:=by
    intro S hS;have hSGd:=(Za.mp hS).1;have hSnotRes:=(Za.mp hS).2;have hSQ:=(Za.mp hSGd).1;have hSd:=(Za.mp hSGd).2
    have hneS₀:S≠S₀:=fun h=>hSnotRes (by subst h;exact mem_insert_self _ _)
    obtain⟨l,hl,hl'⟩:=hQ.2 (Zc.mpr hSQ) (Zc.mpr hS₀Q) hneS₀;obtain⟨aI,dI,kI,hkI,-,hIeq⟩:=Qn (S∩S₀) l hl hl'
    have hmemI:aI∈S∩S₀:=(hIeq aI).mpr ⟨0,hkI,by simp⟩
    obtain⟨hS_in,hS₀_in⟩:=Zn.mp hmemI
    have hnotP:aI∉getP S:=by
     intro hP_in;obtain⟨i,-,hi⟩:=((hget S hSQ).2.2.2.2.1 aI).mp hP_in
     have hmodA:aI % d=getA S % d:=by rw[hi,hSd,Nat.add_mul_mod_self_right]
     apply hSnotRes;rw[←hmodA]
     by_cases hP₀_in:aI∈getP S₀
     ·obtain⟨j,-,hj⟩:=(hP₀eq aI).mp hP₀_in
      rw[hj,hS₀d,Nat.add_mul_mod_self_right];exact mem_insert_self _ _
     ·exact mem_insert_of_mem (mem_image_of_mem _ (Ye.mpr ⟨hS₀_in,hP₀_in⟩))
    exact⟨aI,Ye.mpr ⟨hS_in,hnotP⟩,hS₀_in⟩
   let W2:Zf ℕ->ℕ:=fun S=>if hS:S∈Gd2 then (hW2_ex S hS).choose else 0
   let B2:Zf ℕ->Zf (Zf ℕ):=fun S =>
    (Qb S).filter (fun t=>∃ x∈getP S,t={W2 S,x,x+d})
   have hdisj2:Set.PairwiseDisjoint (Gd2:Set (Zf ℕ)) B2:=by
    intro S hS T hT hST;simp only[Function.onFun];rw[Zk];intro t htS htT;have hSQ:=(Za.mp (Za.mp (Zc.mp hS)).1).1;have hTQ:=(Za.mp (Za.mp (Zc.mp hT)).1).1
    exact We hQ hSQ hTQ hST
     ((Qh S t).mp (Za.mp htS).1)
     ((Qh T t).mp (Za.mp htT).1).2.1
   let Pool2:=(S₀ ×ˢ Icc 1 N).image (fun z=>({z.1,z.2,z.2+d}:Zf ℕ))
   have hsub2:Gd2.biUnion B2⊆Pool2:=by
    intro t ht;obtain⟨S,hS,htB⟩:=mem_biUnion.mp ht;have hSQ:=(Za.mp (Za.mp hS).1).1;obtain⟨x,hxP,rfl⟩:=(Za.mp htB).2
    have hW2spec:W2 S∈S \ getP S/\W2 S∈S₀:=by simpa only [W2,dif_pos hS] using (hW2_ex S hS).choose_spec
    have hxI:x∈Icc 1 N:=Zy.mp (hQ.1 hSQ) ((hget S hSQ).1 hxP);exact Zi.mpr ⟨(W2 S,x),Zh.mpr ⟨hW2spec.2,hxI⟩,rfl⟩
   have hPool2_card:Pool2.card≤ s*N:=by
    calc Pool2.card≤(S₀ ×ˢ Icc 1 N).card:=card_image_le
      _=S₀.card*N:=by rw[card_product,Nat.card_Icc];simp
      _≤ s*N:=Yc N (hsize S₀ hS₀Q).2
   calc Gd2.card*(k/2)=∑ _S∈Gd2,(k/2):=by rw[Finset.sum_const,smul_eq_mul]
     _≤∑ S∈Gd2,(B2 S).card:=by
         refine Finset.sum_le_sum fun S hS=>?_
         have hSGd:=(Za.mp hS).1;have hSQ:=(Za.mp hSGd).1;have hSd:=(Za.mp hSGd).2
         have hW2mem:W2 S∈S \ getP S:=by simpa only [W2,dif_pos hS] using (hW2_ex S hS).choose_spec.1
         simpa only [B2,hSd] using hclean_triples S hSQ (W2 S) hW2mem
     _=(Gd2.biUnion B2).card:=(card_biUnion hdisj2).symm
     _≤ Pool2.card:=Zm hsub2
     _≤ s*N:=hPool2_card
  rw[hGpart,add_mul];exact Nat.add_le_add hGd1 hGd2
 have hsum_nat:Q_near.card*(k/2) ≤∑ d∈Icc 1 D,((q₀+1)*N*(N/d+1)+s*N):=by rw[hpart,Finset.sum_mul];exact Finset.sum_le_sum hper_d
 have hsum_R:(Q_near.card:ℝ)*((k/2:ℕ):ℝ) ≤((q₀:ℝ)+1)*(N:ℝ)^2*(log (N:ℝ)+1) +((q₀:ℝ)+1+(s:ℝ))*(N:ℝ)*(D:ℝ):=by
  have hcast:(Q_near.card:ℝ)*((k/2:ℕ):ℝ) ≤∑ d∈Icc 1 D,(((q₀:ℝ)+1)*(N:ℝ)*((N:ℝ)/(d:ℝ)+1)+(s:ℝ)*(N:ℝ)):=by
   calc (Q_near.card:ℝ)*((k/2:ℕ):ℝ)
       ≤ ∑ d∈Icc 1 D,((((q₀+1)*N*(N/d+1)+s*N:ℕ):ℝ)):=by exact_mod_cast hsum_nat
     _≤∑ d∈Icc 1 D,(((q₀:ℝ)+1)*(N:ℝ)*((N:ℝ)/(d:ℝ)+1)+(s:ℝ)*(N:ℝ)):=by
         refine Finset.sum_le_sum fun d _=>?_
         push_cast;have hdiv:((N/d:ℕ):ℝ)≤(N:ℝ)/(d:ℝ):=Nat.cast_div_le
         have hqN:(0:ℝ)≤((q₀:ℝ)+1)*(N:ℝ):=by positivity
         nlinarith
  have hDN:D≤ N:=by
   have:2*N/k≤2*N/4:=Nat.div_le_div_left (by omega) (by omega)
   omega
  have hharm:∑ d∈Icc 1 D,(1:ℝ)/(d:ℝ)≤ log (N:ℝ)+1:=by
   refine (sum_le_sum_of_subset_of_nonneg ?_ (fun _ _ _=>by positivity)).trans (Q0 N hN)
   intro d hd;simp only[Zb] at hd ⊢;omega
  have hrew:∑ d∈Icc 1 D,(((q₀:ℝ)+1)*(N:ℝ)*((N:ℝ)/(d:ℝ)+1)+(s:ℝ)*(N:ℝ)) =((q₀:ℝ)+1)*(N:ℝ)^2*(∑ d∈Icc 1 D,(1:ℝ)/(d:ℝ)) +((q₀:ℝ)+1+(s:ℝ))*(N:ℝ)*(D:ℝ):=by
   have h1:∀ d∈Icc 1 D,((q₀:ℝ)+1)*(N:ℝ)*((N:ℝ)/(d:ℝ)+1)+(s:ℝ)*(N:ℝ) =((q₀:ℝ)+1)*(N:ℝ)^2*((1:ℝ)/(d:ℝ))+((q₀:ℝ)+1+(s:ℝ))*(N:ℝ):=by intro d _;ring
   rw[Finset.sum_congr rfl h1,Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Nat.card_Icc,nsmul_eq_mul];simp only[Nat.add_sub_cancel];ring
  rw[hrew] at hcast
  have hnn:0≤((q₀:ℝ)+1)*(N:ℝ)^2:=by positivity
  nlinarith
 have hk_half:(k:ℝ)≤4*((k/2:ℕ):ℝ):=by exact_mod_cast (by omega:k≤4*(k/2))
 have hD_le:(D:ℝ)≤2*(N:ℝ)/(k:ℝ):=by
  have:((2*N/k:ℕ):ℝ)≤((2*N:ℕ):ℝ)/(k:ℝ):=Nat.cast_div_le
  push_cast at this;exact this
 have hk_pos:(0:ℝ)<(k:ℝ):=by exact_mod_cast (by omega:0< k)
 have hmul:(Q_near.card:ℝ)*(k:ℝ)^2 ≤8*((q₀:ℝ)+1)*(N:ℝ)^2*(log (N:ℝ)+1)*(k:ℝ) +16*((q₀:ℝ)+1+(s:ℝ))*(N:ℝ)^2:=by
  have hD_k:(D:ℝ)*(k:ℝ)≤2*(N:ℝ):=by
   have:=(le_div_iff₀ hk_pos).mp hD_le;linarith
  have h1:(Q_near.card:ℝ)*(k:ℝ)≤4*(((q₀:ℝ)+1)*(N:ℝ)^2*(log (N:ℝ)+1) +((q₀:ℝ)+1+(s:ℝ))*(N:ℝ)*(D:ℝ)):=by nlinarith[Nat.cast_nonneg (α:=ℝ) Q_near.card]
  have h2:(Q_near.card:ℝ)*(k:ℝ)^2 ≤4*((q₀:ℝ)+1)*(N:ℝ)^2*(log (N:ℝ)+1)*(k:ℝ) +4*((q₀:ℝ)+1+(s:ℝ))*(N:ℝ)*((D:ℝ)*(k:ℝ)):=by have hm:=Zo h1 hk_pos.le;linarith
  have h3:4*((q₀:ℝ)+1+(s:ℝ))*(N:ℝ)*((D:ℝ)*(k:ℝ)) ≤8*((q₀:ℝ)+1+(s:ℝ))*(N:ℝ)^2:=by
   have h3a:=Zp hD_k (show (0:ℝ)≤4*((q₀:ℝ)+1+(s:ℝ))*(N:ℝ) by positivity)
   have h3b:4*((q₀:ℝ)+1+(s:ℝ))*(N:ℝ)*(2*(N:ℝ)) =8*((q₀:ℝ)+1+(s:ℝ))*(N:ℝ)^2:=by ring
   linarith
  have h4:(0:ℝ)≤4*((q₀:ℝ)+1)*(N:ℝ)^2*(log (N:ℝ)+1)*(k:ℝ):=by
   have hlog_nn:0≤ log (N:ℝ):=Real.log_nonneg (by exact_mod_cast hN)
   positivity
  have h5:(0:ℝ)≤8*((q₀:ℝ)+1+(s:ℝ))*(N:ℝ)^2:=by positivity
  linarith
 have hgoal:(Q_near.card:ℝ)*(k:ℝ)^2 ≤(8*((q₀:ℝ)+1)*(N:ℝ)^2*(log (N:ℝ)+1)/(k:ℝ) +16*((q₀:ℝ)+1+(s:ℝ))*(N:ℝ)^2/(k:ℝ)^2)*(k:ℝ)^2:=by
  have hrw:(8*((q₀:ℝ)+1)*(N:ℝ)^2*(log (N:ℝ)+1)/(k:ℝ) +16*((q₀:ℝ)+1+(s:ℝ))*(N:ℝ)^2/(k:ℝ)^2)*(k:ℝ)^2 =8*((q₀:ℝ)+1)*(N:ℝ)^2*(log (N:ℝ)+1)*(k:ℝ) +16*((q₀:ℝ)+1+(s:ℝ))*(N:ℝ)^2:=by field_simp
  rw[hrw];exact hmul
 exact le_of_mul_le_mul_right hgoal (by positivity:(0:ℝ)<(k:ℝ)^2)
lemma Vs {S:Zf ℕ} {c:ℕ} (hc:c∈S) (hnot:¬ IsAP S) :∃ x y,x∈S/\y∈S/\x≠c/\y≠c/\x≠y/\Qk S {c,x,y}:=by
 have h3:3≤ S.card:=Wk ⟨c,hc⟩ hnot
 have hne:(S.erase c).Nonempty:=card_pos.mp (by rw[card_erase_of_mem hc];omega)
 obtain⟨x₁,hx₁_er,hx₁_min⟩:=exists_min_image (S.erase c) (fun x=>max x c-min x c) hne
 obtain⟨hne_x1,hx₁S⟩:=Zw.mp hx₁_er;set d₁:=max x₁ c-min x₁ c
 have hd₁_pos:0< d₁:=by
  rcases lt_or_gt_of_ne hne_x1 with hlt|hgt
  ·dsimp only[d₁];rw[Yi hlt.le,Yl hlt.le];omega
  ·dsimp only[d₁];rw[Yk hgt.le,Yj hgt.le];omega
 have hadj:∀ w∈S,¬ (min c x₁< w/\w< max c x₁):=by
  intro w hwS hbtw
  have hne_wc:w≠c:=by
   rcases lt_or_gt_of_ne hne_x1 with hlt|hgt
   ·rw[Yj hlt.le,Yk hlt.le] at hbtw;omega
   ·rw[Yl hgt.le,Yi hgt.le] at hbtw;omega
  have hle:=hx₁_min w (Zw.mpr ⟨hne_wc,hwS⟩);dsimp only[d₁] at hle
  rcases lt_or_gt_of_ne hne_x1 with hlt|hgt
  ·rw[Yj hlt.le,Yk hlt.le] at hbtw
   rw[Yi hlt.le,Yl hlt.le,Yi (le_of_lt hbtw.2),Yl (le_of_lt hbtw.2)] at hle;omega
  ·rw[Yl hgt.le,Yi hgt.le] at hbtw
   rw[Yk hgt.le,Yj hgt.le,Yk (le_of_lt hbtw.1),Yj (le_of_lt hbtw.1)] at hle;omega
 have hne_sdiff:(S \ Qf S c d₁).Nonempty:=by by_contra hemp;rw[not_nonempty_iff_eq_empty,sdiff_eq_empty_iff_subset] at hemp;have heq:S=Qf S c d₁:=Finset.Subset.antisymm hemp (Qz S c d₁);exact hnot (heq ▸ Wh hd₁_pos hc)
 obtain⟨y,hy⟩:=hne_sdiff;obtain⟨hyS,hyR⟩:=Ye.mp hy
 have hne_yc:y≠c:=fun h=>hyR (h ▸ Q4 hc d₁)
 have hx₁R:x₁∈Qf S c d₁:=by
  rw[Qu]
  refine⟨hx₁S,?_,fun w hw1 hw2 hwmod=>?_⟩
  ·rcases lt_or_gt_of_ne hne_x1 with hlt|hgt
   ·have hd1:d₁=c-x₁:=by dsimp only[d₁];rw[Yi hlt.le,Yl hlt.le]
    exact (Nat.modEq_iff_dvd' hlt.le).mpr ⟨1,by omega⟩
   ·have hd1:d₁=x₁-c:=by dsimp only[d₁];rw[Yk hgt.le,Yj hgt.le]
    exact ((Nat.modEq_iff_dvd' hgt.le).mpr ⟨1,by omega⟩).symm
  ·rcases lt_or_gt_of_ne hne_x1 with hlt|hgt
   ·have hd1:d₁=c-x₁:=by dsimp only[d₁];rw[Yi hlt.le,Yl hlt.le]
    rw[Yj hlt.le] at hw1;rw[Yk hlt.le] at hw2
    rcases eq_or_lt_of_le hw1 with rfl|h1
    ·exact hx₁S
    ·rcases eq_or_lt_of_le hw2 with rfl|h2
     ·exact hc
     ·exfalso
      have hdvd:d₁ ∣ c-w:=(Nat.modEq_iff_dvd' hw2).mp hwmod
      have hle:d₁≤ c-w:=Nat.le_of_dvd (by omega) hdvd
      omega
   ·have hd1:d₁=x₁-c:=by dsimp only[d₁];rw[Yk hgt.le,Yj hgt.le]
    rw[Yl hgt.le] at hw1;rw[Yi hgt.le] at hw2
    rcases eq_or_lt_of_le hw1 with rfl|h1
    ·exact hc
    ·rcases eq_or_lt_of_le hw2 with rfl|h2
     ·exact hx₁S
     ·exfalso
      have hdvd:d₁ ∣ w-c:=(Nat.modEq_iff_dvd' hw1).mp hwmod.symm
      have hle:d₁≤ w-c:=Nat.le_of_dvd (by omega) hdvd
      omega
 have hne_yx1:y≠x₁:=fun h=>hyR (h ▸ hx₁R)
 have hd₁_sym:max c x₁-min c x₁=d₁:=by rw[max_comm,min_comm]
 have hbad:=Wp hc hx₁S hyS hne_x1.symm hadj (hd₁_sym.symm ▸ hyR);exact⟨x₁,y,hx₁S,hyS,hne_x1,hne_yc,hne_yx1.symm,hbad⟩
noncomputable def Qs (c:ℕ) (S:Zf ℕ):Zf (Zf ℕ) :=((Qb S).filter (fun t=>c∈t)).image (fun t=>t.erase c)
lemma Wm (c:ℕ) (S e:Zf ℕ) :e∈Qs c S↔c∉e/\e.card=2/\Qk S (insert c e):=by
 unfold Qs;simp only[Zi,Za,Qh]
 constructor
 ·rintro⟨t,⟨hbad,hct⟩,rfl⟩
  refine⟨notMem_erase c t,?_,?_⟩
  ·rw[card_erase_of_mem hct,hbad.1]
  ·rwa[insert_erase hct]
 ·rintro⟨hce,he2,hbad⟩
  exact⟨insert c e,⟨hbad,mem_insert_self c e⟩,erase_insert hce⟩
lemma Wd {N c:ℕ} {S:Zf ℕ} (hsub:S⊆Icc 1 N) :Qs c S⊆((Icc 1 N).erase c).powersetCard 2:=by
 intro e he;obtain⟨hce,he2,hbad⟩:=(Wm c S e).mp he
 refine Zz.mpr ⟨fun x hx=>?_,he2⟩
 exact Zw.mpr ⟨fun h=>hce (h ▸ hx),hsub (hbad.2.1 (mem_insert_of_mem hx))⟩
lemma W6 {N c:ℕ} {F:Zf (Zf ℕ)} (hF:Zt N F)
  {S T:Zf ℕ} (hS:S∈F) (hT:T∈F) (hST:S≠T) (hcT:c∈T) :
  Disjoint (Qs c S) (Qs c T):=by
 rw[Zk];intro e heS heT;have hbS:=((Wm c S e).mp heS).2.2;have hbT:=((Wm c T e).mp heT).2.2
 exact We hF hS hT hST hbS (insert_subset_iff.mpr ⟨hcT,fun x hx =>
  hbT.2.1 (mem_insert_of_mem hx)⟩)
lemma Qt {N c:ℕ} {F:Zf (Zf ℕ)} (hF:Zt N F)
  {S A:Zf ℕ} (hS:S∈F) (hA:A∈F) (hSA:S≠A) (hcA:c∈A)
  {e:Zf ℕ} (he:e∈Qs c S):¬ (e⊆A):=by
 intro heA;have hbS:=((Wm c S e).mp he).2.2;exact We hF hS hA hSA hbS (insert_subset_iff.mpr ⟨hcA,heA⟩)
noncomputable def Qa (c:ℕ) (P:Zf ℕ) (Sc:Zf (Zf ℕ)):Zf (Zf ℕ) :=Sc.filter (fun S=>∃ e∈Qs c S,(e∩P).Nonempty)
lemma Qp (c:ℕ) (P:Zf ℕ) (Sc:Zf (Zf ℕ)) (S:Zf ℕ) :S∈Qa c P Sc↔S∈Sc/\∃ e∈Qs c S,(e∩P).Nonempty:=by
 unfold Qa;exact Za
lemma Qx (c:ℕ) (P:Zf ℕ) (Sc:Zf (Zf ℕ)) :Qa c P Sc⊆Sc:=by
 unfold Qa;exact Zl _ _
def Qj (N c:ℕ) (P:Zf ℕ):Zf (Zf ℕ) :=(((Icc 1 N).erase c).powersetCard 2).filter (fun e=>(e∩P).Nonempty)
lemma Wc (N c:ℕ) (hc:c∈Icc 1 N) (P:Zf ℕ)
  (hP:P⊆(Icc 1 N).erase c) :
  ((Qj N c P).card:ℝ)≤(P.card:ℝ)*(N:ℝ)-(P.card:ℝ)^2/2:=by
 set U:=(Icc 1 N).erase c
 have hUcard:U.card=N-1:=by rw[card_erase_of_mem hc,Nat.card_Icc];simp
 set V:=U \ P
 have hVcard:V.card+P.card=N-1:=by have h1:V.card+P.card=U.card:=Yb hP;omega
 let E1:=P.powersetCard 2
 let E2:=(P ×ˢ V).image (fun z=>({z.1,z.2}:Zf ℕ))
 have hsub:Qj N c P⊆E1∪E2:=by
  intro e he;obtain⟨heU,⟨p,hp⟩⟩:=Za.mp he;obtain⟨heUsub,he2⟩:=Zz.mp heU;obtain⟨hpe,hpP⟩:=Zn.mp hp
  have her1:(e.erase p).card=1:=by rw[card_erase_of_mem hpe,he2]
  obtain⟨x,hx⟩:=card_eq_one.mp her1
  have hxe:x∈e:=(Zw.mp (by rw[hx];exact mem_singleton_self x)).2
  have hne:x≠p:=(Zw.mp (by rw[hx];exact mem_singleton_self x)).1
  have heeq:e={p,x}:=by
   ext z;constructor
   ·intro hz;by_cases hzp:z=p
    ·simp[hzp]
    ·have:z∈e.erase p:=Zw.mpr ⟨hzp,hz⟩
     rw[hx,Zj] at this;simp[this]
   ·intro hz;simp only[Zx,Zj] at hz
    rcases hz with rfl|rfl <;> assumption
  by_cases hxP:x∈P
  ·refine Ze _ (Zz.mpr ⟨?_,he2⟩)
   rw[heeq];intro z hz;simp only[Zx,Zj] at hz
   rcases hz with rfl|rfl <;> assumption
  ·refine Zg _ (Zi.mpr ⟨(p,x),Zh.mpr ⟨hpP,Ye.mpr ⟨heUsub hxe,hxP⟩⟩,heeq.symm⟩)
 have hE1:2*E1.card=P.card*(P.card-1):=by rw[card_powersetCard,Nat.choose_two_right];exact Nat.mul_div_cancel' (Nat.even_mul_pred_self P.card).two_dvd
 have hE2:E2.card≤ P.card*V.card:=card_image_le.trans (by rw[card_product])
 have htot:2*(Qj N c P).card≤ P.card*(P.card-1)+2*(P.card*V.card):=by have h1:=(Zm hsub).trans (Yh E1 E2);omega
 have htotR:2*((Qj N c P).card:ℝ) ≤(P.card:ℝ)*((P.card:ℝ)-1)+2*((P.card:ℝ)*(V.card:ℝ)):=by
  have hcast:2*((Qj N c P).card:ℝ) ≤(P.card:ℝ)*((P.card-1:ℕ):ℝ)+2*((P.card:ℝ)*(V.card:ℝ)):=by exact_mod_cast htot
  rcases Nat.eq_zero_or_pos P.card with h0|hpos
  ·rw[h0] at hcast ⊢;simp at hcast ⊢;linarith
  ·rw[Nat.cast_sub hpos,Nat.cast_one] at hcast;exact hcast
 have hVN:(V.card:ℝ)+(P.card:ℝ)≤(N:ℝ):=by
  have:V.card+P.card≤ N:=by omega
  exact_mod_cast this
 nlinarith[Nat.cast_nonneg (α:=ℝ) P.card]
lemma Qq {N c:ℕ} {P:Zf ℕ} {Sc:Zf (Zf ℕ)}
  (hSc:Zt N Sc) (hc_all:∀ S∈Sc,c∈S)
  {Forbid:Zf (Zf ℕ)} (hF_sub:Forbid⊆Qj N c P)
  (hF_disj:∀ S∈Sc,Disjoint (Qs c S) Forbid) :
  (Qa c P Sc).card+Forbid.card≤(Qj N c P).card:=by
 classical
 have hch:∀ S∈Qa c P Sc,∃ e∈Qs c S,(e∩P).Nonempty:=fun S hS =>
  ((Qp c P Sc S).mp hS).2
 let pick:Zf ℕ->Zf ℕ:=fun S=>if hS:S∈Qa c P Sc then (hch S hS).choose else ∅
 have hpick:∀ S∈Qa c P Sc,pick S∈Qs c S/\(pick S∩P).Nonempty:=by intro S hS;simpa only [pick,dif_pos hS] using (hch S hS).choose_spec
 have hinj:Set.InjOn pick ((Qa c P Sc):Set (Zf ℕ)):=by intro S hS T hT heq;by_contra hST;have hS':=Zc.mp hS;have hT':=Zc.mp hT;have hSSc:=((Qp c P Sc S).mp hS').1;have hTSc:=((Qp c P Sc T).mp hT').1;have hdisj:=W6 hSc hSSc hTSc hST (hc_all T hTSc);exact (Zk.mp hdisj) (hpick S hS').1 (heq ▸ (hpick T hT').1)
 have hsub_img:(Qa c P Sc).image pick⊆Qj N c P:=by intro e he;obtain⟨S,hS,rfl⟩:=Zi.mp he;have hSSc:=((Qp c P Sc S).mp hS).1;have hsubS:S⊆Icc 1 N:=Zy.mp (hSc.1 hSSc);exact Za.mpr ⟨Wd hsubS (hpick S hS).1,(hpick S hS).2⟩
 have hdisj_img:Disjoint ((Qa c P Sc).image pick) Forbid:=by rw[Zk];intro e heI heF;obtain⟨S,hS,rfl⟩:=Zi.mp heI;have hSSc:=((Qp c P Sc S).mp hS).1;exact Zk.mp (hF_disj S hSSc) (hpick S hS).1 heF
 calc (Qa c P Sc).card+Forbid.card
     = ((Qa c P Sc).image pick).card+Forbid.card:=by rw[card_image_of_injOn hinj]
   _=(((Qa c P Sc).image pick)∪Forbid).card:=(Zq hdisj_img).symm
   _≤(Qj N c P).card:=Zm (Zu hsub_img hF_sub)
lemma V9 (N c:ℕ) (Sc:Zf (Zf ℕ)) (P:Zf ℕ)
  (hSc:Zt N Sc)
  (hnonAP:∀ S∈Sc,¬ IsAP S)
  (hc_all:∀ S∈Sc,c∈S)
  (hP_sub:P⊆(Icc 1 N).erase c)
  (hP_hit:∀ S∈Sc,(S∩P).Nonempty) :
  (Sc \ Qa c P Sc).card≤8*∑ L∈Icc 1 N,L.divisors.card^2:=by
 classical
 set E:=Sc \ Qa c P Sc
 let PoolA:Zf (Zf ℕ):=(Icc 1 N).biUnion (fun L =>
  L.divisors.biUnion (fun d₁=>L.divisors.biUnion (fun d₂ =>
   ({{c,c+d₁,c+d₂},{c,c+d₁,c-d₂},{c,c-d₁,c+d₂},{c,c-d₁,c-d₂}}:Zf (Zf ℕ)))))
 let PoolB:Zf (Zf ℕ):=(Icc 1 N).biUnion (fun M =>
  M.divisors.biUnion (fun d₁=>M.divisors.biUnion (fun d₂ =>
   ({{c,c+d₁,c+(M+d₂)},{c,c+d₁,c-(M+d₂)},{c,c-d₁,c+(M+d₂)},{c,c-d₁,c-(M+d₂)}}:Zf (Zf ℕ)))))
 have hPoolA:PoolA.card≤4*∑ L∈Icc 1 N,L.divisors.card^2:=by
  calc PoolA.card
      ≤ ∑ L∈Icc 1 N,(L.divisors.biUnion (fun d₁=>L.divisors.biUnion (fun d₂ =>
          ({{c,c+d₁,c+d₂},{c,c+d₁,c-d₂},{c,c-d₁,c+d₂},{c,c-d₁,c-d₂}}:Zf (Zf ℕ))))).card :=
        card_biUnion_le
    _≤∑ L∈Icc 1 N,4*L.divisors.card^2:=by
        refine Finset.sum_le_sum fun L _=>?_
        calc (L.divisors.biUnion (fun d₁=>L.divisors.biUnion (fun d₂ =>
                ({{c,c+d₁,c+d₂},{c,c+d₁,c-d₂},{c,c-d₁,c+d₂},{c,c-d₁,c-d₂}}:Zf (Zf ℕ))))).card
            ≤ ∑ d₁∈L.divisors,(L.divisors.biUnion (fun d₂ =>
                ({{c,c+d₁,c+d₂},{c,c+d₁,c-d₂},{c,c-d₁,c+d₂},{c,c-d₁,c-d₂}}:Zf (Zf ℕ)))).card :=
              card_biUnion_le
          _≤∑ d₁∈L.divisors,(4*L.divisors.card):=by
              refine Finset.sum_le_sum fun d₁ _=>?_
              calc (L.divisors.biUnion (fun d₂ =>
                      ({{c,c+d₁,c+d₂},{c,c+d₁,c-d₂},{c,c-d₁,c+d₂},{c,c-d₁,c-d₂}}:Zf (Zf ℕ)))).card
                  ≤ ∑ d₂∈L.divisors,({{c,c+d₁,c+d₂},{c,c+d₁,c-d₂},{c,c-d₁,c+d₂},{c,c-d₁,c-d₂}}:Zf (Zf ℕ)).card :=card_biUnion_le
                _≤∑ _d₂∈L.divisors,4:=by
                    refine Finset.sum_le_sum fun _ _=>?_
                    exact (card_insert_le _ _).trans (Nat.add_le_add_right
                      ((card_insert_le _ _).trans (Nat.add_le_add_right
                        ((card_insert_le _ _).trans (by simp)) 1)) 1)
                _=4*L.divisors.card:=by rw[Finset.sum_const,smul_eq_mul,mul_comm]
          _=4*L.divisors.card^2:=by rw[Finset.sum_const,smul_eq_mul];ring
    _=4*∑ L∈Icc 1 N,L.divisors.card^2:=by rw[Finset.mul_sum]
 have hPoolB:PoolB.card≤4*∑ M∈Icc 1 N,M.divisors.card^2:=by
  calc PoolB.card
      ≤ ∑ M∈Icc 1 N,(M.divisors.biUnion (fun d₁=>M.divisors.biUnion (fun d₂ =>
          ({{c,c+d₁,c+(M+d₂)},{c,c+d₁,c-(M+d₂)},{c,c-d₁,c+(M+d₂)},{c,c-d₁,c-(M+d₂)}}:Zf (Zf ℕ))))).card :=
        card_biUnion_le
    _≤∑ M∈Icc 1 N,4*M.divisors.card^2:=by
        refine Finset.sum_le_sum fun M _=>?_
        calc (M.divisors.biUnion (fun d₁=>M.divisors.biUnion (fun d₂ =>
                ({{c,c+d₁,c+(M+d₂)},{c,c+d₁,c-(M+d₂)},{c,c-d₁,c+(M+d₂)},{c,c-d₁,c-(M+d₂)}}:Zf (Zf ℕ))))).card
            ≤ ∑ d₁∈M.divisors,(M.divisors.biUnion (fun d₂ =>
                ({{c,c+d₁,c+(M+d₂)},{c,c+d₁,c-(M+d₂)},{c,c-d₁,c+(M+d₂)},{c,c-d₁,c-(M+d₂)}}:Zf (Zf ℕ)))).card :=
              card_biUnion_le
          _≤∑ d₁∈M.divisors,(4*M.divisors.card):=by
              refine Finset.sum_le_sum fun d₁ _=>?_
              calc (M.divisors.biUnion (fun d₂ =>
                      ({{c,c+d₁,c+(M+d₂)},{c,c+d₁,c-(M+d₂)},{c,c-d₁,c+(M+d₂)},{c,c-d₁,c-(M+d₂)}}:Zf (Zf ℕ)))).card
                  ≤ ∑ d₂∈M.divisors,({{c,c+d₁,c+(M+d₂)},{c,c+d₁,c-(M+d₂)},{c,c-d₁,c+(M+d₂)},{c,c-d₁,c-(M+d₂)}}:Zf (Zf ℕ)).card :=card_biUnion_le
                _≤∑ _d₂∈M.divisors,4:=by
                    refine Finset.sum_le_sum fun _ _=>?_
                    exact (card_insert_le _ _).trans (Nat.add_le_add_right
                      ((card_insert_le _ _).trans (Nat.add_le_add_right
                        ((card_insert_le _ _).trans (by simp)) 1)) 1)
                _=4*M.divisors.card:=by rw[Finset.sum_const,smul_eq_mul,mul_comm]
          _=4*M.divisors.card^2:=by rw[Finset.sum_const,smul_eq_mul];ring
    _=4*∑ M∈Icc 1 N,M.divisors.card^2:=by rw[Finset.mul_sum]
 have hex_bad:∀ S∈E,∃ t∈Qb S,t∈PoolA∪PoolB:=by
  intro S hSE;obtain⟨hSSc,hnotH⟩:=Ye.mp hSE;have hsubS:S⊆Icc 1 N:=Zy.mp (hSc.1 hSSc);have hcS:c∈S:=hc_all S hSSc;have hnotAP:¬ IsAP S:=hnonAP S hSSc;have h3:3≤ S.card:=Wk ⟨c,hcS⟩ hnotAP
  have hno_hit:∀ x p:ℕ,x∈S->p∈S∩P->x≠c->x≠p->¬ Qk S {c,x,p}:=by
   intro x p hxS hpSP hxc hxp hbad;apply hnotH
   refine (Qp c P Sc S).mpr ⟨hSSc,{x,p},?_,⟨p,Zn.mpr ⟨by simp,(Zn.mp hpSP).2⟩⟩⟩
   have hpc:p≠c:=(Zw.mp (hP_sub (Zn.mp hpSP).2)).1;rw[Wm]
   refine⟨by simp[hxc.symm,hpc.symm],?_,hbad⟩
   rw[card_insert_of_notMem (Finset.notMem_singleton.mpr hxp),card_singleton]
  obtain⟨p,hpSP⟩:=hP_hit S hSSc;obtain⟨hpS,hpP⟩:=Zn.mp hpSP;have hpc:p≠c:=(Zw.mp (hP_sub hpP)).1
  have hne_er:(S.erase c).Nonempty:=card_pos.mp (by rw[card_erase_of_mem hcS];omega)
  obtain⟨x₁,hx₁_er,hx₁_min⟩:=exists_min_image (S.erase c) (fun x=>max x c-min x c) hne_er
  obtain⟨hne_x1c,hx₁S⟩:=Zw.mp hx₁_er;set d₁:=max x₁ c-min x₁ c
  have hd₁_pos:0< d₁:=by
   rcases lt_or_gt_of_ne hne_x1c with hlt|hgt
   ·dsimp only[d₁];rw[Yi hlt.le,Yl hlt.le];omega
   ·dsimp only[d₁];rw[Yk hgt.le,Yj hgt.le];omega
  have hx₁_eq:x₁=c+d₁\/x₁=c-d₁:=by
   rcases lt_or_gt_of_ne hne_x1c with hlt|hgt
   ·right;dsimp only[d₁];rw[Yi hlt.le,Yl hlt.le];omega
   ·left;dsimp only[d₁];rw[Yk hgt.le,Yj hgt.le];omega
  have hadj:∀ w∈S,¬ (min c x₁< w/\w< max c x₁):=by
   intro w hwS hbtw
   have hne_wc:w≠c:=by
    rcases lt_or_gt_of_ne hne_x1c with hlt|hgt
    ·rw[Yj hlt.le,Yk hlt.le] at hbtw;omega
    ·rw[Yl hgt.le,Yi hgt.le] at hbtw;omega
   have hle:=hx₁_min w (Zw.mpr ⟨hne_wc,hwS⟩);dsimp only[d₁] at hle
   rcases lt_or_gt_of_ne hne_x1c with hlt|hgt
   ·rw[Yj hlt.le,Yk hlt.le] at hbtw
    rw[Yi hlt.le,Yl hlt.le,Yi (le_of_lt hbtw.2),Yl (le_of_lt hbtw.2)] at hle;omega
   ·rw[Yl hgt.le,Yi hgt.le] at hbtw
    rw[Yk hgt.le,Yj hgt.le,Yk (le_of_lt hbtw.1),Yj (le_of_lt hbtw.1)] at hle;omega
  set Lpc:=max p c-min p c
  have hLpc_mem:Lpc∈Icc 1 N:=by
   have h1:=Zb.mp (hsubS hpS);have h2:=Zb.mp (hsubS hcS)
   refine Zb.mpr ⟨?_,?_⟩
   ·rcases lt_or_gt_of_ne hpc with hlt|hgt
    ·dsimp only[Lpc];rw[Yi hlt.le,Yl hlt.le];omega
    ·dsimp only[Lpc];rw[Yk hgt.le,Yj hgt.le];omega
   ·rcases le_total p c with hle|hge
    ·dsimp only[Lpc];rw[Yi hle,Yl hle];omega
    ·dsimp only[Lpc];rw[Yk hge,Yj hge];omega
  have hp_in_run:p∈Qf S c d₁/\d₁ ∣ Lpc:=by
   by_cases hpx:p=x₁
   ·subst hpx
    refine⟨?_,dvd_refl _⟩
    rw[Qu]
    refine⟨hx₁S,?_,fun w hw1 hw2 hwmod=>?_⟩
    ·rcases lt_or_gt_of_ne hne_x1c with hlt|hgt
     ·have:d₁=c-p:=by dsimp only[d₁];rw[Yi hlt.le,Yl hlt.le]
      exact (Nat.modEq_iff_dvd' hlt.le).mpr ⟨1,by omega⟩
     ·have:d₁=p-c:=by dsimp only[d₁];rw[Yk hgt.le,Yj hgt.le]
      exact ((Nat.modEq_iff_dvd' hgt.le).mpr ⟨1,by omega⟩).symm
    ·rcases lt_or_gt_of_ne hne_x1c with hlt|hgt
     ·have hd1:d₁=c-p:=by dsimp only[d₁];rw[Yi hlt.le,Yl hlt.le]
      rw[Yj hlt.le] at hw1;rw[Yk hlt.le] at hw2
      rcases eq_or_lt_of_le hw1 with rfl|h1;· exact hx₁S
      rcases eq_or_lt_of_le hw2 with rfl|h2;· exact hcS
      exfalso;have:=Nat.le_of_dvd (by omega) ((Nat.modEq_iff_dvd' hw2).mp hwmod);omega
     ·have hd1:d₁=p-c:=by dsimp only[d₁];rw[Yk hgt.le,Yj hgt.le]
      rw[Yl hgt.le] at hw1;rw[Yi hgt.le] at hw2
      rcases eq_or_lt_of_le hw1 with rfl|h1;· exact hcS
      rcases eq_or_lt_of_le hw2 with rfl|h2;· exact hx₁S
      exfalso;have:=Nat.le_of_dvd (by omega) ((Nat.modEq_iff_dvd' hw1).mp hwmod.symm);omega
   ·have hnb:=hno_hit x₁ p hx₁S hpSP hne_x1c (Ne.symm hpx)
    have hc3:({c,x₁,p}:Zf ℕ).card=3:=by
     rw[card_insert_of_notMem,card_insert_of_notMem,card_singleton]
     ·exact Finset.notMem_singleton.mpr (Ne.symm hpx)
     ·simp[hne_x1c.symm,hpc.symm]
    have hsub3:({c,x₁,p}:Zf ℕ)⊆S:=by
     intro z hz;simp only[Zx,Zj] at hz
     rcases hz with rfl|rfl|rfl <;> assumption
    unfold Qk at hnb;push Not at hnb;obtain⟨A,⟨aA,δ,kA,hkA,hdA,hAeq⟩,hAS,htA⟩:=hnb hc3 hsub3
    have hcA:c∈A:=htA (by simp)
    have hx₁A:x₁∈A:=htA (by simp)
    have hpA:p∈A:=htA (by simp)
    have hkA2:2≤ kA:=by
     have:3≤ A.card:=by rw[←hc3];exact Zm htA
     rw[Qo hkA hdA hAeq] at this;omega
    have hδ_pos:0<δ:=hdA (by omega)
    obtain⟨ic,hic,hic_eq⟩:=(hAeq c).mp hcA;obtain⟨ix,hix,hix_eq⟩:=(hAeq x₁).mp hx₁A;obtain⟨ip,hip,hip_eq⟩:=(hAeq p).mp hpA
    have hδ_eq:δ=d₁:=by
     have hδ_dvd:δ ∣ d₁:=by
      rcases lt_or_gt_of_ne hne_x1c with hlt|hgt
      ·have hidx:ix< ic:=Nat.lt_of_mul_lt_mul_right (by omega:ix*δ< ic*δ)
       dsimp only[d₁];rw[Yi hlt.le,Yl hlt.le]
       refine⟨ic-ix,?_⟩
       rw[hic_eq,hix_eq];have:aA+ic*δ-(aA+ix*δ)=(ic-ix)*δ:=by rw[Nat.sub_mul];omega
       rw[this,mul_comm]
      ·have hidx:ic< ix:=Nat.lt_of_mul_lt_mul_right (by omega:ic*δ< ix*δ)
       dsimp only[d₁];rw[Yk hgt.le,Yj hgt.le]
       refine⟨ix-ic,?_⟩
       rw[hic_eq,hix_eq];have:aA+ix*δ-(aA+ic*δ)=(ix-ic)*δ:=by rw[Nat.sub_mul];omega
       rw[this,mul_comm]
     have hδ_le:δ≤ d₁:=Nat.le_of_dvd hd₁_pos hδ_dvd
     rcases lt_or_eq_of_le hδ_le with hlt_δ|heq_δ
     ·exfalso
      rcases lt_or_gt_of_ne hne_x1c with hlt|hgt
      ·have hidx:ix< ic:=Nat.lt_of_mul_lt_mul_right (by omega:ix*δ< ic*δ)
       have hwA:aA+(ix+1)*δ∈A:=(hAeq _).mpr ⟨ix+1,by omega,rfl⟩
       have hstep:aA+(ix+1)*δ=x₁+δ:=by rw[hix_eq];ring
       have hbtw:min c x₁< x₁+δ/\x₁+δ< max c x₁:=by
        rw[Yj hlt.le,Yk hlt.le]
        have:d₁=c-x₁:=by dsimp only[d₁];rw[Yi hlt.le,Yl hlt.le]
        omega
       exact hadj (x₁+δ) (hstep ▸ hAS hwA) hbtw
      ·have hidx:ic< ix:=Nat.lt_of_mul_lt_mul_right (by omega:ic*δ< ix*δ)
       have hwA:aA+(ic+1)*δ∈A:=(hAeq _).mpr ⟨ic+1,by omega,rfl⟩
       have hstep:aA+(ic+1)*δ=c+δ:=by rw[hic_eq];ring
       have hbtw:min c x₁< c+δ/\c+δ< max c x₁:=by
        rw[Yl hgt.le,Yi hgt.le]
        have:d₁=x₁-c:=by dsimp only[d₁];rw[Yk hgt.le,Yj hgt.le]
        omega
       exact hadj (c+δ) (hstep ▸ hAS hwA) hbtw
     ·exact heq_δ
    subst hδ_eq
    refine⟨Qv hAS hd₁_pos hAeq hcA hpA,?_⟩
    rcases lt_or_gt_of_ne hpc with hlt|hgt
    ·have hidx:ip< ic:=Nat.lt_of_mul_lt_mul_right (by omega:ip*d₁< ic*d₁)
     dsimp only[Lpc];rw[Yi hlt.le,Yl hlt.le]
     refine⟨ic-ip,?_⟩
     rw[hic_eq,hip_eq];have:aA+ic*d₁-(aA+ip*d₁)=(ic-ip)*d₁:=by rw[Nat.sub_mul];omega
     rw[this,mul_comm]
    ·have hidx:ic< ip:=Nat.lt_of_mul_lt_mul_right (by omega:ic*d₁< ip*d₁)
     dsimp only[Lpc];rw[Yk hgt.le,Yj hgt.le]
     refine⟨ip-ic,?_⟩
     rw[hic_eq,hip_eq];have:aA+ip*d₁-(aA+ic*d₁)=(ip-ic)*d₁:=by rw[Nat.sub_mul];omega
     rw[this,mul_comm]
  have hne_sdiff:(S \ Qf S c d₁).Nonempty:=by by_contra hemp;rw[not_nonempty_iff_eq_empty,sdiff_eq_empty_iff_subset] at hemp;exact hnotAP ((Finset.Subset.antisymm hemp (Qz S c d₁)) ▸ Wh hd₁_pos hcS)
  obtain⟨y,hy_sd,hy_min⟩:=exists_min_image (S \ Qf S c d₁) (fun z=>max z c-min z c) hne_sdiff
  obtain⟨hyS,hyR⟩:=Ye.mp hy_sd
  have hne_yc:y≠c:=fun h=>hyR (h ▸ Q4 hcS d₁)
  have hne_yp:y≠p:=fun h=>hyR (h ▸ hp_in_run.1)
  have hd₁_sym:max c x₁-min c x₁=d₁:=by rw[max_comm,min_comm]
  have hbad_cxy:Qk S {c,x₁,y} :=Wp hcS hx₁S hyS hne_x1c.symm hadj (hd₁_sym.symm ▸ hyR);have hnb_y:=hno_hit y p hyS hpSP hne_yc hne_yp
  have hc3_y:({c,y,p}:Zf ℕ).card=3:=by
   rw[card_insert_of_notMem,card_insert_of_notMem,card_singleton]
   ·exact Finset.notMem_singleton.mpr hne_yp
   ·simp[hne_yc.symm,hpc.symm]
  have hsub3_y:({c,y,p}:Zf ℕ)⊆S:=by
   intro z hz;simp only[Zx,Zj] at hz
   rcases hz with rfl|rfl|rfl <;> assumption
  unfold Qk at hnb_y;push Not at hnb_y;obtain⟨B,⟨aB,d₂,kB,hkB,hdB,hBeq⟩,hBS,htB⟩:=hnb_y hc3_y hsub3_y
  have hcB:c∈B:=htB (by simp)
  have hyB:y∈B:=htB (by simp)
  have hpB:p∈B:=htB (by simp)
  have hkB2:2≤ kB:=by
   have:3≤ B.card:=by rw[←hc3_y];exact Zm htB
   rw[Qo hkB hdB hBeq] at this;omega
  have hd₂_pos:0< d₂:=hdB (by omega)
  obtain⟨ic,hic,hic_eq⟩:=(hBeq c).mp hcB;obtain⟨iy,hiy,hiy_eq⟩:=(hBeq y).mp hyB;obtain⟨ip,hip,hip_eq⟩:=(hBeq p).mp hpB
  have hd₂_Lpc:d₂ ∣ Lpc:=by
   rcases lt_or_gt_of_ne hpc with hlt|hgt
   ·have hidx:ip< ic:=Nat.lt_of_mul_lt_mul_right (by omega:ip*d₂< ic*d₂)
    dsimp only[Lpc];rw[Yi hlt.le,Yl hlt.le]
    refine⟨ic-ip,?_⟩
    rw[hic_eq,hip_eq];have:aB+ic*d₂-(aB+ip*d₂)=(ic-ip)*d₂:=by rw[Nat.sub_mul];omega
    rw[this,mul_comm]
   ·have hidx:ic< ip:=Nat.lt_of_mul_lt_mul_right (by omega:ic*d₂< ip*d₂)
    dsimp only[Lpc];rw[Yk hgt.le,Yj hgt.le]
    refine⟨ip-ic,?_⟩
    rw[hic_eq,hip_eq];have:aB+ip*d₂-(aB+ic*d₂)=(ip-ic)*d₂:=by rw[Nat.sub_mul];omega
    rw[this,mul_comm]
  set y':=if c< y then aB+(iy-1)*d₂ else aB+(iy+1)*d₂
  have hy'_props:y'∈B/\(c< y->y=y'+d₂/\c≤ y')/\(y< c->y'=y+d₂/\y'≤ c):=by
   rcases lt_or_gt_of_ne hne_yc with hlt|hgt
   ·have hidx:iy< ic:=Nat.lt_of_mul_lt_mul_right (by omega:iy*d₂< ic*d₂)
    have hy'eq:y'=aB+(iy+1)*d₂:=if_neg (by omega)
    refine⟨hy'eq ▸ (hBeq _).mpr ⟨iy+1,by omega,rfl⟩,fun h=>by omega,fun _=>?_⟩
    have hstep:y'=y+d₂:=by rw[hy'eq,hiy_eq];ring
    have hle:y'≤ c:=by
     rw[hy'eq,hic_eq];exact Nat.add_le_add_left (Yc d₂ (by omega)) aB
    exact⟨hstep,hle⟩
   ·have hidx:ic< iy:=Nat.lt_of_mul_lt_mul_right (by omega:ic*d₂< iy*d₂)
    have hy'eq:y'=aB+(iy-1)*d₂:=if_pos hgt
    refine⟨hy'eq ▸ (hBeq _).mpr ⟨iy-1,by omega,rfl⟩,fun _=>?_,fun h=>by omega⟩
    have hstep:y=y'+d₂:=by
     rw[hy'eq,hiy_eq]
     obtain⟨t,ht⟩:∃ t,iy=t+1:=⟨iy-1,by omega⟩
     rw[ht];simp only[Nat.add_sub_cancel];ring
    have hle:c≤ y':=by
     rw[hy'eq,hic_eq];exact Nat.add_le_add_left (Yc d₂ (by omega)) aB
    exact⟨hstep,hle⟩
  have hy'R:y'∈Qf S c d₁:=by
   by_contra hnotR;have hle:=hy_min y' (Ye.mpr ⟨hBS hy'_props.1,hnotR⟩)
   rcases lt_or_gt_of_ne hne_yc with hlt|hgt
   ·obtain⟨hstep,hle_c⟩:=hy'_props.2.2 hlt
    rw[Yi hlt.le,Yl hlt.le,Yi hle_c,Yl hle_c] at hle;omega
   ·obtain⟨hstep,hle_c⟩:=hy'_props.2.1 hgt
    rw[Yk hgt.le,Yj hgt.le,Yk hle_c,Yj hle_c] at hle;omega
  refine⟨{c,x₁,y},(Qh S _).mpr hbad_cxy,?_⟩
  by_cases hy'c:y'=c
  ·
   refine Ze _ ?_
   set L':=Nat.lcm d₁ d₂;have hL'_dvd:L' ∣ Lpc:=Nat.lcm_dvd hp_in_run.2 hd₂_Lpc;have hL'_pos:0< L':=Nat.lcm_pos hd₁_pos hd₂_pos;have hL'_le:L'≤ N:=(Nat.le_of_dvd (Zb.mp hLpc_mem).1 hL'_dvd).trans (Zb.mp hLpc_mem).2
   have hd₁_div:d₁∈L'.divisors:=Nat.mem_divisors.mpr ⟨Nat.dvd_lcm_left d₁ d₂,by omega⟩
   have hd₂_div:d₂∈L'.divisors:=Nat.mem_divisors.mpr ⟨Nat.dvd_lcm_right d₁ d₂,by omega⟩
   have hy_eq:y=c+d₂\/y=c-d₂:=by
    rcases lt_or_gt_of_ne hne_yc with hlt|hgt
    ·right;have:=(hy'_props.2.2 hlt).1;omega
    ·left;have:=(hy'_props.2.1 hgt).1;omega
   refine mem_biUnion.mpr ⟨L',Zb.mpr ⟨hL'_pos,hL'_le⟩,mem_biUnion.mpr ⟨d₁,hd₁_div,mem_biUnion.mpr ⟨d₂,hd₂_div,?_⟩⟩⟩
   rcases hx₁_eq with hx₁_eq|hx₁_eq <;> rcases hy_eq with hy_eq|hy_eq <;> simp[hx₁_eq,hy_eq]
  ·
   refine Zg _ ?_
   set M:=max y' c-min y' c
   have hM_mem:M∈Icc 1 N:=by
    have h1:=Zb.mp (hsubS (hBS hy'_props.1));have h2:=Zb.mp (hsubS hcS)
    refine Zb.mpr ⟨?_,?_⟩
    ·rcases lt_or_gt_of_ne hy'c with hlt|hgt
     ·dsimp only[M];rw[Yi hlt.le,Yl hlt.le];omega
     ·dsimp only[M];rw[Yk hgt.le,Yj hgt.le];omega
    ·rcases le_total y' c with hle|hge
     ·dsimp only[M];rw[Yi hle,Yl hle];omega
     ·dsimp only[M];rw[Yk hge,Yj hge];omega
   have hM_pos:0< M:=(Zb.mp hM_mem).1
   have hd₁_M:d₁∈M.divisors:=by
    refine Nat.mem_divisors.mpr ⟨?_,by omega⟩
    have hmod:=((Qu S c d₁ y').mp hy'R).2.1
    rcases lt_or_gt_of_ne hy'c with hlt|hgt
    ·dsimp only[M];rw[Yi hlt.le,Yl hlt.le]
     exact (Nat.modEq_iff_dvd' hlt.le).mp hmod
    ·dsimp only[M];rw[Yk hgt.le,Yj hgt.le]
     exact (Nat.modEq_iff_dvd' hgt.le).mp hmod.symm
   have hd₂_M:d₂∈M.divisors:=by
    refine Nat.mem_divisors.mpr ⟨?_,by omega⟩
    obtain⟨iy',-,hiy'_eq⟩:=(hBeq y').mp hy'_props.1
    rcases lt_or_gt_of_ne hy'c with hlt|hgt
    ·have hidx:iy'< ic:=Nat.lt_of_mul_lt_mul_right (by omega:iy'*d₂< ic*d₂)
     dsimp only[M];rw[Yi hlt.le,Yl hlt.le]
     refine⟨ic-iy',?_⟩
     rw[hic_eq,hiy'_eq];have:aB+ic*d₂-(aB+iy'*d₂)=(ic-iy')*d₂:=by rw[Nat.sub_mul];omega
     rw[this,mul_comm]
    ·have hidx:ic< iy':=Nat.lt_of_mul_lt_mul_right (by omega:ic*d₂< iy'*d₂)
     dsimp only[M];rw[Yk hgt.le,Yj hgt.le]
     refine⟨iy'-ic,?_⟩
     rw[hic_eq,hiy'_eq];have:aB+iy'*d₂-(aB+ic*d₂)=(iy'-ic)*d₂:=by rw[Nat.sub_mul];omega
     rw[this,mul_comm]
   have hy_eq:y=c+(M+d₂)\/y=c-(M+d₂):=by
    rcases lt_or_gt_of_ne hne_yc with hlt|hgt
    ·right
     obtain⟨hstep,hle_c⟩:=hy'_props.2.2 hlt
     have hM_eq:M=c-y':=by dsimp only[M];rw[Yi hle_c,Yl hle_c]
     omega
    ·left
     obtain⟨hstep,hle_c⟩:=hy'_props.2.1 hgt
     have hM_eq:M=y'-c:=by dsimp only[M];rw[Yk hle_c,Yj hle_c]
     omega
   refine mem_biUnion.mpr ⟨M,hM_mem,mem_biUnion.mpr ⟨d₁,hd₁_M,mem_biUnion.mpr ⟨d₂,hd₂_M,?_⟩⟩⟩
   rcases hx₁_eq with hx₁_eq|hx₁_eq <;> rcases hy_eq with hy_eq|hy_eq <;> simp[hx₁_eq,hy_eq]
 let pickT:Zf ℕ->Zf ℕ:=fun S=>if hS:S∈E then (hex_bad S hS).choose else ∅
 have hpickT:∀ S∈E,pickT S∈Qb S/\pickT S∈PoolA∪PoolB:=by intro S hS;simpa only [pickT,dif_pos hS] using (hex_bad S hS).choose_spec
 have hinj:Set.InjOn pickT (E:Set (Zf ℕ)):=by
  intro S hS T hT heq;by_contra hST;have hS':=Zc.mp hS;have hT':=Zc.mp hT;have hSSc:=(Ye.mp hS').1;have hTSc:=(Ye.mp hT').1
  exact We hSc hSSc hTSc hST
   ((Qh S _).mp (hpickT S hS').1)
   ((Qh T _).mp (heq ▸ (hpickT T hT').1)).2.1
 have hmaps:Set.MapsTo pickT (E:Set (Zf ℕ)) ((PoolA∪PoolB:Zf (Zf ℕ)):Set (Zf ℕ)) :=fun S hS=>Zc.mpr (hpickT S (Zc.mp hS)).2
 calc E.card≤(PoolA∪PoolB).card:=card_le_card_of_injOn pickT hmaps hinj
   _≤ PoolA.card+PoolB.card:=Yh PoolA PoolB
   _≤8*∑ L∈Icc 1 N,L.divisors.card^2:=by omega
lemma Qw (N c:ℕ) (hN:1≤ N) (Sc:Zf (Zf ℕ)) (P:Zf ℕ)
  (hSc:Zt N Sc)
  (hnonAP:∀ S∈Sc,¬ IsAP S)
  (hc_all:∀ S∈Sc,c∈S)
  (hP_sub:P⊆(Icc 1 N).erase c)
  (hP_hit:∀ S∈Sc,(S∩P).Nonempty) :
  ((Sc \ Qa c P Sc).card:ℝ)≤8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5):=by
 have hnat:=V9 N c Sc P hSc hnonAP hc_all hP_sub hP_hit
 have hcast:((Sc \ Qa c P Sc).card:ℝ) ≤8*∑ L∈Icc 1 N,((L.divisors.card:ℝ)^2):=by exact_mod_cast hnat
 have hterm:∀ L∈Icc 1 N,(L.divisors.card:ℝ)^2≤(512:ℝ)^6*(N:ℝ)^((2:ℝ)/5):=by
  intro L hL;have hL1:=(Zb.mp hL).1;have hLN:=(Zb.mp hL).2;have h1:(L.divisors.card:ℝ)≤(512:ℝ)^3*(L:ℝ)^((1:ℝ)/5):=Xj L hL1
  have h2:(L:ℝ)^((1:ℝ)/5)≤(N:ℝ)^((1:ℝ)/5) :=Real.rpow_le_rpow (Nat.cast_nonneg L) (by exact_mod_cast hLN) (by norm_num)
  have h3:(L.divisors.card:ℝ)≤(512:ℝ)^3*(N:ℝ)^((1:ℝ)/5):=by
   have:(0:ℝ)≤(512:ℝ)^3:=by positivity
   nlinarith
  have hsq:=pow_le_pow_left₀ (Nat.cast_nonneg _) h3 2
  have hrpow2:((N:ℝ)^((1:ℝ)/5))^2=(N:ℝ)^((2:ℝ)/5):=by rw[←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg N)];norm_num
  calc (L.divisors.card:ℝ)^2≤((512:ℝ)^3*(N:ℝ)^((1:ℝ)/5))^2:=hsq
    _=(512:ℝ)^6*((N:ℝ)^((1:ℝ)/5))^2:=by ring
    _=(512:ℝ)^6*(N:ℝ)^((2:ℝ)/5):=by rw[hrpow2]
 have hsum:∑ L∈Icc 1 N,(L.divisors.card:ℝ)^2 ≤(N:ℝ)*((512:ℝ)^6*(N:ℝ)^((2:ℝ)/5)):=by
  calc ∑ L∈Icc 1 N,(L.divisors.card:ℝ)^2
      ≤ ∑ _L∈Icc 1 N,((512:ℝ)^6*(N:ℝ)^((2:ℝ)/5)):=Finset.sum_le_sum hterm
    _=(N:ℝ)*((512:ℝ)^6*(N:ℝ)^((2:ℝ)/5)):=by
        rw[Finset.sum_const,Nat.card_Icc,nsmul_eq_mul];simp
 have hNpos:(0:ℝ)<(N:ℝ):=by exact_mod_cast (by omega:0< N)
 have hrpow75:(N:ℝ)*(N:ℝ)^((2:ℝ)/5)=(N:ℝ)^((7:ℝ)/5):=by
  calc (N:ℝ)*(N:ℝ)^((2:ℝ)/5)
      = (N:ℝ)^(1:ℝ)*(N:ℝ)^((2:ℝ)/5):=by rw[Real.rpow_one]
    _=(N:ℝ)^((1:ℝ)+2/5):=(Real.rpow_add hNpos _ _).symm
    _=(N:ℝ)^((7:ℝ)/5):=by norm_num
 calc ((Sc \ Qa c P Sc).card:ℝ)
     ≤ 8*∑ L∈Icc 1 N,(L.divisors.card:ℝ)^2:=hcast
   _≤8*((N:ℝ)*((512:ℝ)^6*(N:ℝ)^((2:ℝ)/5))):=by linarith
   _=8*(512:ℝ)^6*((N:ℝ)*(N:ℝ)^((2:ℝ)/5)):=by ring
   _=8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5):=by rw[hrpow75]
lemma Q6 (N c:ℕ) (hN:1≤ N) (hc:c∈Icc 1 N)
  (Sc:Zf (Zf ℕ)) (P:Zf ℕ)
  (hSc:Zt N Sc)
  (hnonAP:∀ S∈Sc,¬ IsAP S)
  (hc_all:∀ S∈Sc,c∈S)
  (hP_sub:P⊆(Icc 1 N).erase c)
  (hP_hit:∀ S∈Sc,(S∩P).Nonempty) :
  (Sc.card:ℝ)≤(P.card:ℝ)*(N:ℝ)-(P.card:ℝ)^2/2 +8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5):=by
 have hpart:Sc.card=(Qa c P Sc).card+(Sc \ Qa c P Sc).card:=by
  have:=Yb (Qx c P Sc);omega
 have hhit:(Qa c P Sc).card≤(Qj N c P).card:=by
  have h:=Qq (P:=P) hSc hc_all (Forbid:=∅) (Finset.empty_subset _)
   (fun _ _=>Finset.disjoint_empty_right _)
  simpa using h
 have hhitR:((Qa c P Sc).card:ℝ)≤(P.card:ℝ)*(N:ℝ)-(P.card:ℝ)^2/2 :=le_trans (by exact_mod_cast hhit) (Wc N c hc P hP_sub)
 have herr:=Qw N c hN Sc P hSc hnonAP hc_all hP_sub hP_hit
 have hpartR:(Sc.card:ℝ)=((Qa c P Sc).card:ℝ)+((Sc \ Qa c P Sc).card:ℝ):=by exact_mod_cast hpart
 linarith
private lemma Qi {a b C:ℝ} (hab:a< b) :∀ᶠ N:ℕ in Filter.atTop,C*(N:ℝ)^a≤(N:ℝ)^b:=by
 have hdiff:0< b-a:=by linarith
 have htend:Filter.Tendsto (fun N:ℕ=>(N:ℝ)^(b-a)) Filter.atTop Filter.atTop :=(tendsto_rpow_atTop hdiff).comp tendsto_natCast_atTop_atTop
 filter_upwards [htend.eventually (Filter.eventually_ge_atTop (max C 1)),Filter.eventually_ge_atTop 1] with N hN hN1
 have hNpos:(0:ℝ)<(N:ℝ):=by exact_mod_cast hN1
 have hNa_pos:(0:ℝ)≤(N:ℝ)^a:=by positivity
 have hC:C≤(N:ℝ)^(b-a):=(Ym C 1).trans hN
 calc C*(N:ℝ)^a≤(N:ℝ)^(b-a)*(N:ℝ)^a:=Zo hC hNa_pos
   _=(N:ℝ)^((b-a)+a):=(Real.rpow_add hNpos _ _).symm
   _=(N:ℝ)^b:=by ring_nf
private lemma Wr {ε:ℝ} (hε:0<ε) :∀ᶠ N:ℕ in Filter.atTop,log (N:ℝ)+2≤(N:ℝ)^ε:=by
 filter_upwards [Qi (a:=ε/2) (b:=ε) (C:=2/ε+2) (by linarith),Filter.eventually_ge_atTop 1] with N hdom hN1
 have hN1R:(1:ℝ)≤(N:ℝ):=by exact_mod_cast hN1
 have hNpos:(0:ℝ)<(N:ℝ):=by linarith
 have h1:log ((N:ℝ)^(ε/2))≤(N:ℝ)^(ε/2)-1 :=Real.log_le_sub_one_of_pos (by positivity)
 rw[Real.log_rpow hNpos] at h1
 have hlog:log (N:ℝ)≤(2/ε)*(N:ℝ)^(ε/2):=by
  have hmul:=Zp h1 (show (0:ℝ)≤2/ε by positivity)
  have hEq:(2/ε)*(ε/2*log (N:ℝ))=log (N:ℝ):=by field_simp
  have hpos2:(0:ℝ)≤2/ε:=by positivity
  linarith
 have hpow1:(1:ℝ)≤(N:ℝ)^(ε/2):=Real.one_le_rpow hN1R (by linarith)
 linarith
private lemma Xk (N k s₂ q₀:ℕ)
  (hN_big:10^12≤ N)
  (h310:(10^22:ℝ)*(N:ℝ)^((1:ℝ)/10)≤(N:ℝ)^((3:ℝ)/10))
  (hlog100:log (N:ℝ)+2≤(N:ℝ)^((1:ℝ)/100))
  (hs₂_ub:(s₂:ℝ)≤60*(N:ℝ)^((1:ℝ)/2))
  (hk_lb:(N:ℝ)^((1:ℝ)/2)/20000≤(k:ℝ))
  (hk_big:5100≤ k)
  (hq₀_pos:1≤ q₀)
  (hq₀_lb:(N:ℝ)^((1:ℝ)/4)/2≤(q₀:ℝ))
  (hq₀_ub:(q₀:ℝ)≤(N:ℝ)^((1:ℝ)/4))
  (hk_4q₀:4*q₀+4≤ k)
  (Q'':Zf (Zf ℕ))
  (hQ''_sub:Zt N Q'')
  (hQ''_spec:∀ S∈Q'',¬ IsAP S/\k≤ S.card/\S.card< s₂) :
  ((Q''.filter (fun S=>S.card-Qc S≤ q₀)).card:ℝ)≤(5/1000:ℝ)*(N:ℝ)^2 ∧
  ((Q''.filter (fun S=>q₀< S.card-Qc S/\100*(S.card-Qc S)< S.card)).card:ℝ) ≤(5/1000:ℝ)*(N:ℝ)^2:=by
 have hN1:1≤ N:=by omega
 have hN_pos:(0:ℝ)<(N:ℝ):=by exact_mod_cast (by omega:0< N)
 have hN15:(10^22:ℝ)≤(N:ℝ)^((1:ℝ)/5):=by
  have hr1:(N:ℝ)^((3:ℝ)/10)=(N:ℝ)^((1:ℝ)/5)*(N:ℝ)^((1:ℝ)/10):=by rw[←Real.rpow_add hN_pos];norm_num
  rw[hr1] at h310
  exact le_of_mul_le_mul_right h310 (by positivity)
 have hsub_ai:∀ (F:Zf (Zf ℕ)),F⊆Q''->Zt N F:=fun F hF =>
  ⟨hF.trans hQ''_sub.1,fun S hS T' hT' hST =>
   hQ''_sub.2 (Zc.mpr (hF (Zc.mp hS)))
    (Zc.mpr (hF (Zc.mp hT'))) hST⟩
 set Q_near:=Q''.filter (fun S=>S.card-Qc S≤ q₀)
 set Q_mid:=Q''.filter (fun S=>q₀< S.card-Qc S/\100*(S.card-Qc S)< S.card)
 constructor
 ·have h1:=Kd N k s₂ q₀ hN1 hq₀_pos hk_4q₀ Q_near
   (hsub_ai Q_near (Zl _ _))
   (fun S hS=>by
    have hs:=hQ''_spec S (Za.mp hS).1;exact⟨hs.2.1,le_of_lt hs.2.2⟩)
   (fun S hS=>by
    have hs:=hQ''_spec S (Za.mp hS).1
    have hlt:=W8 (card_pos.mp (by omega)) hs.1
    exact⟨by omega,(Za.mp hS).2⟩)
  have hk_posR:(0:ℝ)<(k:ℝ):=by exact_mod_cast (by omega:0< k)
  have ht1:8*((q₀:ℝ)+1)*(N:ℝ)^2*(log (N:ℝ)+1)/(k:ℝ)≤(2/1000:ℝ)*(N:ℝ)^2:=by
   rw[div_le_iff₀ hk_posR]
   have hq1:(q₀:ℝ)+1≤2*(N:ℝ)^((1:ℝ)/4):=by
    have:(1:ℝ)≤(N:ℝ)^((1:ℝ)/4):=Real.one_le_rpow (by exact_mod_cast hN1) (by norm_num)
    linarith
   have hlog:log (N:ℝ)+1≤(N:ℝ)^((1:ℝ)/100):=by linarith
   have hprod:8*((q₀:ℝ)+1)*(log (N:ℝ)+1)≤16*(N:ℝ)^((26:ℝ)/100):=by
    have hr:(N:ℝ)^((1:ℝ)/4)*(N:ℝ)^((1:ℝ)/100)=(N:ℝ)^((26:ℝ)/100):=by rw[←Real.rpow_add hN_pos];norm_num
    have hnn:0≤ log (N:ℝ)+1:=by
     have:=Real.log_nonneg (show (1:ℝ)≤(N:ℝ) by exact_mod_cast hN1);linarith
    calc 8*((q₀:ℝ)+1)*(log (N:ℝ)+1)
        ≤ 8*(2*(N:ℝ)^((1:ℝ)/4))*(N:ℝ)^((1:ℝ)/100):=by nlinarith
      _=16*((N:ℝ)^((1:ℝ)/4)*(N:ℝ)^((1:ℝ)/100)):=by ring
      _=16*(N:ℝ)^((26:ℝ)/100):=by rw[hr]
   have hdom:16*(N:ℝ)^((26:ℝ)/100)≤(2/1000:ℝ)*((N:ℝ)^((1:ℝ)/2)/20000):=by
    have hN24:(10^22:ℝ)≤(N:ℝ)^((24:ℝ)/100) :=hN15.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by norm_num))
    have hr2:(N:ℝ)^((26:ℝ)/100)*(N:ℝ)^((24:ℝ)/100)=(N:ℝ)^((1:ℝ)/2):=by rw[←Real.rpow_add hN_pos];norm_num
    have hle:(10^22:ℝ)*(N:ℝ)^((26:ℝ)/100)≤(N:ℝ)^((1:ℝ)/2):=by
     calc (10^22:ℝ)*(N:ℝ)^((26:ℝ)/100)
         ≤ (N:ℝ)^((24:ℝ)/100)*(N:ℝ)^((26:ℝ)/100) :=Zo hN24 (by positivity)
       _=(N:ℝ)^((1:ℝ)/2):=by rw[mul_comm,hr2]
    linarith
   have hle2:8*((q₀:ℝ)+1)*(log (N:ℝ)+1)≤(2/1000:ℝ)*(k:ℝ):=by linarith
   calc 8*((q₀:ℝ)+1)*(N:ℝ)^2*(log (N:ℝ)+1)
       = (8*((q₀:ℝ)+1)*(log (N:ℝ)+1))*(N:ℝ)^2:=by ring
     _≤((2/1000:ℝ)*(k:ℝ))*(N:ℝ)^2:=Zo hle2 (by positivity)
     _=(2/1000:ℝ)*(N:ℝ)^2*(k:ℝ):=by ring
  have ht2:16*((q₀:ℝ)+1+(s₂:ℝ))*(N:ℝ)^2/(k:ℝ)^2≤(2/1000:ℝ)*(N:ℝ)^2:=by
   rw[div_le_iff₀ (by positivity:(0:ℝ)<(k:ℝ)^2)]
   have hq1s:(q₀:ℝ)+1+(s₂:ℝ)≤62*(N:ℝ)^((1:ℝ)/2):=by
    have h1':(N:ℝ)^((1:ℝ)/4)≤(N:ℝ)^((1:ℝ)/2) :=Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by norm_num)
    have h2':(1:ℝ)≤(N:ℝ)^((1:ℝ)/2):=Real.one_le_rpow (by exact_mod_cast hN1) (by norm_num)
    linarith
   have hk_sq:(N:ℝ)/(4*10^8:ℝ)≤(k:ℝ)^2:=by
    have hsq:=pow_le_pow_left₀ (by positivity) hk_lb 2
    have hr:((N:ℝ)^((1:ℝ)/2))^2=(N:ℝ):=by rw[←Real.rpow_natCast,←Real.rpow_mul hN_pos.le];norm_num
    nlinarith
   have hdom:16*(62*(N:ℝ)^((1:ℝ)/2))≤(2/1000:ℝ)*((N:ℝ)/(4*10^8:ℝ)):=by
    have hN12:(10^22:ℝ)≤(N:ℝ)^((1:ℝ)/2) :=hN15.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by norm_num))
    have hr2:(N:ℝ)^((1:ℝ)/2)*(N:ℝ)^((1:ℝ)/2)=(N:ℝ):=by rw[←Real.rpow_add hN_pos];norm_num
    nlinarith
   have hle2:16*((q₀:ℝ)+1+(s₂:ℝ))≤(2/1000:ℝ)*(k:ℝ)^2:=by linarith
   calc 16*((q₀:ℝ)+1+(s₂:ℝ))*(N:ℝ)^2
       ≤ ((2/1000:ℝ)*(k:ℝ)^2)*(N:ℝ)^2:=Zo hle2 (by positivity)
     _=(2/1000:ℝ)*(N:ℝ)^2*(k:ℝ)^2:=by ring
  linarith
 ·have hnat:=Qr N (q₀*k^2) 100 Q_mid
   (hsub_ai Q_mid (Zl _ _)) fun S hS=>by
    obtain⟨hSQ'',hqgt,hqlt⟩:=Za.mp hS;have hkm:k≤ S.card:=(hQ''_spec S hSQ'').2.1
    have hc2:=Xu S (by omega) (by omega) hqlt
    exact (Nat.mul_le_mul (le_of_lt hqgt) (Nat.pow_le_pow_left hkm 2)).trans hc2
  have hN3:6*(Q_mid.card*(q₀*k^2))≤100*N^3:=by
   calc 6*(Q_mid.card*(q₀*k^2))≤6*(100*N.choose 3):=Yd 6 hnat
     _=100*(6*N.choose 3):=by ring
     _≤100*N^3:=Yd 100 (Wq N)
  have hR:6*(Q_mid.card:ℝ)*((q₀:ℝ)*(k:ℝ)^2)≤100*(N:ℝ)^3:=by
   have:((6*(Q_mid.card*(q₀*k^2)):ℕ):ℝ)≤((100*N^3:ℕ):ℝ):=by exact_mod_cast hN3
   push_cast at this;linarith
  have hqk_lb:(N:ℝ)^((5:ℝ)/4)/(8*10^8:ℝ)≤(q₀:ℝ)*(k:ℝ)^2:=by
   have hk_sq:(N:ℝ)/(4*10^8:ℝ)≤(k:ℝ)^2:=by
    have hsq:=pow_le_pow_left₀ (by positivity) hk_lb 2
    have hr:((N:ℝ)^((1:ℝ)/2))^2=(N:ℝ):=by rw[←Real.rpow_natCast,←Real.rpow_mul hN_pos.le];norm_num
    nlinarith
   have hr54:(N:ℝ)^((1:ℝ)/4)*(N:ℝ)=(N:ℝ)^((5:ℝ)/4):=by
    calc (N:ℝ)^((1:ℝ)/4)*(N:ℝ)
        = (N:ℝ)^((1:ℝ)/4)*(N:ℝ)^(1:ℝ):=by rw[Real.rpow_one]
      _=(N:ℝ)^((1:ℝ)/4+1):=(Real.rpow_add hN_pos _ _).symm
      _=(N:ℝ)^((5:ℝ)/4):=by norm_num
   calc (N:ℝ)^((5:ℝ)/4)/(8*10^8:ℝ)
       = ((N:ℝ)^((1:ℝ)/4)/2)*((N:ℝ)/(4*10^8:ℝ)):=by rw[←hr54];ring
     _≤(q₀:ℝ)*(k:ℝ)^2:=mul_le_mul hq₀_lb hk_sq (by positivity) (by positivity)
  have hdom:100*(N:ℝ)^3≤6*((5/1000:ℝ)*(N:ℝ)^2)*((N:ℝ)^((5:ℝ)/4)/(8*10^8:ℝ)):=by
   have hN14:(10^22:ℝ)≤(N:ℝ)^((1:ℝ)/4) :=hN15.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by norm_num))
   have hr134:(N:ℝ)^2*(N:ℝ)^((5:ℝ)/4)=(N:ℝ)^3*(N:ℝ)^((1:ℝ)/4):=by have h1':(N:ℝ)^2=(N:ℝ)^(2:ℝ):=(Real.rpow_natCast _ 2).symm;have h3':(N:ℝ)^3=(N:ℝ)^(3:ℝ):=(Real.rpow_natCast _ 3).symm;rw[h1',h3',←Real.rpow_add hN_pos,←Real.rpow_add hN_pos];norm_num
   have hle:(10^22:ℝ)*(N:ℝ)^3≤(N:ℝ)^2*(N:ℝ)^((5:ℝ)/4):=by
    rw[hr134,mul_comm];exact Zp hN14 (by positivity)
   have hre:6*((5/1000:ℝ)*(N:ℝ)^2)*((N:ℝ)^((5:ℝ)/4)/(8*10^8:ℝ)) =(3/(8*10^10:ℝ))*((N:ℝ)^2*(N:ℝ)^((5:ℝ)/4)):=by ring
   have hc:(100:ℝ)≤(3/(8*10^10:ℝ))*(10^22:ℝ):=by norm_num
   have hN3nn:(0:ℝ)≤(N:ℝ)^3:=pow_nonneg hN_pos.le 3
   calc 100*(N:ℝ)^3
       ≤ ((3/(8*10^10:ℝ))*(10^22:ℝ))*(N:ℝ)^3:=Zo hc hN3nn
     _=(3/(8*10^10:ℝ))*((10^22:ℝ)*(N:ℝ)^3):=by ring
     _≤(3/(8*10^10:ℝ))*((N:ℝ)^2*(N:ℝ)^((5:ℝ)/4)):=Zp hle (by positivity)
     _=6*((5/1000:ℝ)*(N:ℝ)^2)*((N:ℝ)^((5:ℝ)/4)/(8*10^8:ℝ)):=hre.symm
  have hstep:6*(Q_mid.card:ℝ)*((N:ℝ)^((5:ℝ)/4)/(8*10^8:ℝ)) ≤6*((5/1000:ℝ)*(N:ℝ)^2)*((N:ℝ)^((5:ℝ)/4)/(8*10^8:ℝ)):=by
   have hle1:=Zp hqk_lb (show (0:ℝ)≤6*(Q_mid.card:ℝ) by positivity)
   linarith
  exact le_of_mul_le_mul_right (by linarith:(Q_mid.card:ℝ)*(6*((N:ℝ)^((5:ℝ)/4)/(8*10^8:ℝ))) ≤((5/1000:ℝ)*(N:ℝ)^2)*(6*((N:ℝ)^((5:ℝ)/4)/(8*10^8:ℝ)))) (by positivity)
private lemma Xv (N k T:ℕ)
  (hN_big:10^12≤ N)
  (h310:(10^22:ℝ)*(N:ℝ)^((1:ℝ)/10)≤(N:ℝ)^((3:ℝ)/10))
  (h195:(10^42:ℝ)*(N:ℝ)^((195:ℝ)/100)≤(N:ℝ)^2)
  (hlog20:log (N:ℝ)+2≤(N:ℝ)^((1:ℝ)/20))
  (hk_lb:(N:ℝ)^((1:ℝ)/2)/20000≤(k:ℝ))
  (hk_big:5100≤ k)
  (hT_pos:1≤ T)
  (hT_bd:∀ L∈Icc 1 N,L.divisors.card≤ T)
  (hT_ub:(T:ℝ)≤(512:ℝ)^3*(N:ℝ)^((1:ℝ)/5)+1)
  (Q'':Zf (Zf ℕ))
  (hQ''_sub:Zt N Q'')
  (hQ''_k:∀ S∈Q'',k≤ S.card) :
  ((Q''.filter (fun S=>S.card≤100*(S.card-Qc S)/\4*T*Qc S+8≤ S.card)).card:ℝ) ≤(5/1000:ℝ)*(N:ℝ)^2 ∧
  ((Q''.filter (fun S=>S.card≤100*(S.card-Qc S)/\¬ (4*T*Qc S+8≤ S.card))).card:ℝ) ≤(5/1000:ℝ)*(N:ℝ)^2:=by
 have hN1:1≤ N:=by omega
 have hN_pos:(0:ℝ)<(N:ℝ):=by exact_mod_cast (by omega:0< N)
 have hN15:(10^22:ℝ)≤(N:ℝ)^((1:ℝ)/5):=by
  have hr1:(N:ℝ)^((3:ℝ)/10)=(N:ℝ)^((1:ℝ)/5)*(N:ℝ)^((1:ℝ)/10):=by rw[←Real.rpow_add hN_pos];norm_num
  rw[hr1] at h310
  exact le_of_mul_le_mul_right h310 (by positivity)
 have hsub_ai:∀ (F:Zf (Zf ℕ)),F⊆Q''->Zt N F:=fun F hF =>
  ⟨hF.trans hQ''_sub.1,fun S hS T' hT' hST =>
   hQ''_sub.2 (Zc.mpr (hF (Zc.mp hS)))
    (Zc.mpr (hF (Zc.mp hT'))) hST⟩
 set Q_rA:=Q''.filter (fun S=>S.card≤100*(S.card-Qc S)/\4*T*Qc S+8≤ S.card)
 set Q_rB:=Q''.filter (fun S=>S.card≤100*(S.card-Qc S)/\¬ (4*T*Qc S+8≤ S.card))
 constructor
 ·have hnat:=Qr N (k*(k-1)*k) 24 Q_rA
   (hsub_ai Q_rA (Zl _ _)) fun S hS=>by
    obtain⟨hSQ'',-,hcond⟩:=Za.mp hS;have hkm:k≤ S.card:=hQ''_k S hSQ'';have hsubS:S⊆Icc 1 N:=Zy.mp (hQ''_sub.1 hSQ'');have hrA:=X6 N T S hsubS hT_bd hcond;exact (Nat.mul_le_mul (Nat.mul_le_mul hkm (Nat.sub_le_sub_right hkm 1)) hkm).trans hrA
  have hN3:6*(Q_rA.card*(k*(k-1)*k))≤24*N^3:=by
   calc 6*(Q_rA.card*(k*(k-1)*k))≤6*(24*N.choose 3):=Yd 6 hnat
     _=24*(6*N.choose 3):=by ring
     _≤24*N^3:=Yd 24 (Wq N)
  have hR:6*(Q_rA.card:ℝ)*((k:ℝ)*((k:ℝ)-1)*(k:ℝ))≤24*(N:ℝ)^3:=by
   have:((6*(Q_rA.card*(k*(k-1)*k)):ℕ):ℝ)≤((24*N^3:ℕ):ℝ):=by exact_mod_cast hN3
   push_cast [Nat.cast_sub (by omega:1≤ k)] at this;linarith
  have hk3_lb:(N:ℝ)^((3:ℝ)/2)/(16*10^12:ℝ)≤(k:ℝ)*((k:ℝ)-1)*(k:ℝ):=by
   have hk2:(k:ℝ)/2≤(k:ℝ)-1:=by
    have hk5:(5100:ℝ)≤(k:ℝ):=by exact_mod_cast hk_big
    linarith
   have hk_cube:((N:ℝ)^((1:ℝ)/2)/20000)^3≤(k:ℝ)^3 :=pow_le_pow_left₀ (by positivity) hk_lb 3
   have hr32:((N:ℝ)^((1:ℝ)/2))^3=(N:ℝ)^((3:ℝ)/2):=by rw[←Real.rpow_natCast,←Real.rpow_mul hN_pos.le];norm_num
   have h1:(k:ℝ)^3/2≤(k:ℝ)*((k:ℝ)-1)*(k:ℝ):=by nlinarith[sq_nonneg (k:ℝ)]
   have h2:((N:ℝ)^((1:ℝ)/2)/20000)^3=(N:ℝ)^((3:ℝ)/2)/(8*10^12:ℝ):=by rw[div_pow,hr32];norm_num
   linarith
  have hdom:24*(N:ℝ)^3≤6*((5/1000:ℝ)*(N:ℝ)^2)*((N:ℝ)^((3:ℝ)/2)/(16*10^12:ℝ)):=by
   have hN12:(10^22:ℝ)≤(N:ℝ)^((1:ℝ)/2) :=hN15.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by norm_num))
   have hr72:(N:ℝ)^2*(N:ℝ)^((3:ℝ)/2)=(N:ℝ)^3*(N:ℝ)^((1:ℝ)/2):=by have h2':(N:ℝ)^2=(N:ℝ)^(2:ℝ):=(Real.rpow_natCast _ 2).symm;have h3':(N:ℝ)^3=(N:ℝ)^(3:ℝ):=(Real.rpow_natCast _ 3).symm;rw[h2',h3',←Real.rpow_add hN_pos,←Real.rpow_add hN_pos];norm_num
   have hle:(10^22:ℝ)*(N:ℝ)^3≤(N:ℝ)^2*(N:ℝ)^((3:ℝ)/2):=by
    rw[hr72,mul_comm];exact Zp hN12 (by positivity)
   have hre:6*((5/1000:ℝ)*(N:ℝ)^2)*((N:ℝ)^((3:ℝ)/2)/(16*10^12:ℝ)) =(3/(16*10^14:ℝ))*((N:ℝ)^2*(N:ℝ)^((3:ℝ)/2)):=by ring
   have hc:(24:ℝ)≤(3/(16*10^14:ℝ))*(10^22:ℝ):=by norm_num
   have hN3nn:(0:ℝ)≤(N:ℝ)^3:=pow_nonneg hN_pos.le 3
   calc 24*(N:ℝ)^3
       ≤ ((3/(16*10^14:ℝ))*(10^22:ℝ))*(N:ℝ)^3:=Zo hc hN3nn
     _=(3/(16*10^14:ℝ))*((10^22:ℝ)*(N:ℝ)^3):=by ring
     _≤(3/(16*10^14:ℝ))*((N:ℝ)^2*(N:ℝ)^((3:ℝ)/2)):=Zp hle (by positivity)
     _=6*((5/1000:ℝ)*(N:ℝ)^2)*((N:ℝ)^((3:ℝ)/2)/(16*10^12:ℝ)):=hre.symm
  have hstep:6*(Q_rA.card:ℝ)*((N:ℝ)^((3:ℝ)/2)/(16*10^12:ℝ)) ≤6*((5/1000:ℝ)*(N:ℝ)^2)*((N:ℝ)^((3:ℝ)/2)/(16*10^12:ℝ)):=by
   have hle1:=Zp hk3_lb (show (0:ℝ)≤6*(Q_rA.card:ℝ) by positivity)
   linarith
  exact le_of_mul_le_mul_right (by linarith:(Q_rA.card:ℝ)*(6*((N:ℝ)^((3:ℝ)/2)/(16*10^12:ℝ))) ≤((5/1000:ℝ)*(N:ℝ)^2)*(6*((N:ℝ)^((3:ℝ)/2)/(16*10^12:ℝ)))) (by positivity)
 ·set p_min:=(k-8)/(4*T)
  have hN310_big:(10^22:ℝ)≤(N:ℝ)^((3:ℝ)/10):=by
   have:(1:ℝ)≤(N:ℝ)^((1:ℝ)/10):=Real.one_le_rpow (by exact_mod_cast hN1) (by norm_num)
   nlinarith
  have hp_min_lb:(N:ℝ)^((3:ℝ)/10)/(10^15:ℝ)≤(p_min:ℝ):=by
   have hk8:(N:ℝ)^((1:ℝ)/2)/40000≤((k-8:ℕ):ℝ):=by
    rw[Nat.cast_sub (by omega)]
    have hk5:(5100:ℝ)≤(k:ℝ):=by exact_mod_cast hk_big
    push_cast;linarith
   have hT_le:(4*T:ℝ)≤8*(512:ℝ)^3*(N:ℝ)^((1:ℝ)/5):=by
    have:(1:ℝ)≤(N:ℝ)^((1:ℝ)/5):=Real.one_le_rpow (by exact_mod_cast hN1) (by norm_num)
    linarith
   have hdiv_lb:((k-8:ℕ):ℝ)/(4*T:ℝ)-1≤(p_min:ℝ):=by
    have h1:(k-8)<(p_min+1)*(4*T):=by
     rw[mul_comm];exact Nat.lt_mul_div_succ (k-8) (by omega:0<4*T)
    have h1R:((k-8:ℕ):ℝ)≤((p_min:ℝ)+1)*(4*(T:ℝ)):=by exact_mod_cast le_of_lt h1
    have h4T_pos:(0:ℝ)<4*(T:ℝ):=by positivity
    have:=(div_le_iff₀ h4T_pos).mpr h1R
    linarith
   have hratio:(N:ℝ)^((3:ℝ)/10)/(5*10^14:ℝ)≤((k-8:ℕ):ℝ)/(4*T:ℝ):=by
    rw[div_le_div_iff₀ (by positivity) (by positivity)]
    have hr5:(N:ℝ)^((3:ℝ)/10)*(N:ℝ)^((1:ℝ)/5)=(N:ℝ)^((1:ℝ)/2):=by rw[←Real.rpow_add hN_pos];norm_num
    have hle1:(N:ℝ)^((3:ℝ)/10)*(4*(T:ℝ)) ≤8*(512:ℝ)^3*(N:ℝ)^((1:ℝ)/2):=by
     calc (N:ℝ)^((3:ℝ)/10)*(4*(T:ℝ))
         ≤ (N:ℝ)^((3:ℝ)/10)*(8*(512:ℝ)^3*(N:ℝ)^((1:ℝ)/5)) :=Zp hT_le (by positivity)
       _=8*(512:ℝ)^3*((N:ℝ)^((3:ℝ)/10)*(N:ℝ)^((1:ℝ)/5)):=by ring
       _=8*(512:ℝ)^3*(N:ℝ)^((1:ℝ)/2):=by rw[hr5]
    have h8512:8*(512:ℝ)^3≤(5*10^14:ℝ)/40000:=by norm_num
    nlinarith
   linarith
  have hNlog2_ub:(Nat.log 2 (2*N)+1:ℝ)≤2*(N:ℝ)^((1:ℝ)/20):=by
   have h2le:(2:ℝ)^(Nat.log 2 (2*N))≤(2*N:ℝ):=by
    exact_mod_cast Nat.pow_log_le_self 2 (by omega:2*N≠0)
   have hlog:(Nat.log 2 (2*N):ℝ)*log 2≤ log (2*(N:ℝ)):=by
    have h1:=Real.log_le_log (by positivity) h2le
    rw[Real.log_pow] at h1;exact h1
   have hlog2:(1/2:ℝ)≤ log 2:=by
    have h:=Real.exp_one_lt_d9
    have h2:Real.exp (1/2:ℝ)≤2:=by
     have hsq:(Real.exp (1/2:ℝ))^2=Real.exp 1:=by rw[←Real.exp_nat_mul];norm_num
     nlinarith[Real.exp_pos (1/2:ℝ)]
    have h3:=Real.log_le_log (Real.exp_pos _) h2;rwa[Real.log_exp] at h3
   have hlog2N:log (2*(N:ℝ))=log 2+log (N:ℝ) :=Real.log_mul (by norm_num) (ne_of_gt hN_pos)
   have hlog2_le1:log 2≤1:=by
    have:=Real.log_le_sub_one_of_pos (show (0:ℝ)<2 by norm_num);linarith
   nlinarith
  have hp_min_3M:3000000≤ p_min:=by
   have:(3000000:ℝ)≤(p_min:ℝ):=by linarith
   exact_mod_cast this
  have hnat:=Qr N (k*p_min^2) (12000*(Nat.log 2 (2*N)+1)) Q_rB
   (hsub_ai Q_rB (Zl _ _)) fun S hS=>by
    obtain⟨hSQ'',hrough',hltT⟩:=Za.mp hS;have hkm:k≤ S.card:=hQ''_k S hSQ'';have hsubS:S⊆Icc 1 N:=Zy.mp (hQ''_sub.1 hSQ'')
    have hp_ge_pmin:p_min≤ Qc S:=by
     have h1:k-8<(Qc S)*(4*T):=by
      have:4*T*Qc S=Qc S*(4*T):=mul_comm _ _
      omega
     exact (Nat.div_le_iff_le_mul_add_pred (by omega:0<4*T)).mpr (by omega)
    have hrough_p:100*Qc S≤99*S.card:=by omega
    have hM_log:6*Nat.log 2 N*(Nat.log 2 (2*(Qc S/3))+1)≤ Qc S/3:=by
     have hleN1:Nat.log 2 N≤ Nat.log 2 (2*N):=Nat.log_mono_right (by omega)
     have hleN2:Nat.log 2 (2*(Qc S/3))≤ Nat.log 2 (2*N):=by
      have hpN:Qc S≤ N:=by
       obtain⟨P,hPS,-,hPc,-⟩:=Wo S (card_pos.mp (by omega))
       have:=Zm (hPS.trans hsubS);rw[Nat.card_Icc] at this;omega
      exact Nat.log_mono_right (by omega)
     have hsq:((Nat.log 2 (2*N)+1:ℕ):ℝ)^2≤4*(N:ℝ)^((1:ℝ)/10):=by
      have h1':=pow_le_pow_left₀ (by positivity) hNlog2_ub 2
      have hr:((N:ℝ)^((1:ℝ)/20))^2=(N:ℝ)^((1:ℝ)/10):=by rw[←Real.rpow_natCast,←Real.rpow_mul hN_pos.le];norm_num
      push_cast;nlinarith
     have h2:(p_min:ℝ)/3-1≤((p_min/3:ℕ):ℝ):=by
      have:=Nat.lt_mul_div_succ p_min (show 0<3 by omega)
      have hR':(p_min:ℝ)≤3*(((p_min/3:ℕ):ℝ)+1):=by exact_mod_cast le_of_lt this
      linarith
     have h3:6*((Nat.log 2 (2*N)+1:ℕ):ℝ)^2+1≤(p_min:ℝ)/3:=by
      have:(1:ℝ)≤(N:ℝ)^((1:ℝ)/10):=Real.one_le_rpow (by exact_mod_cast hN1) (by norm_num)
      linarith
     have hnat_log:6*(Nat.log 2 (2*N)+1)^2≤ p_min/3:=by
      have hcast:((6*(Nat.log 2 (2*N)+1)^2:ℕ):ℝ)≤((p_min/3:ℕ):ℝ):=by push_cast at h3 ⊢;linarith
      exact_mod_cast hcast
     calc 6*Nat.log 2 N*(Nat.log 2 (2*(Qc S/3))+1)
         ≤ 6*(Nat.log 2 (2*N)+1)*(Nat.log 2 (2*N)+1) :=Nat.mul_le_mul (Yd 6 (by omega)) (by omega)
       _=6*(Nat.log 2 (2*N)+1)^2:=by ring
       _≤ p_min/3:=hnat_log
       _≤ Qc S/3:=Nat.div_le_div_right hp_ge_pmin
    have hrB:=X5 N S hsubS (by omega) hrough_p hM_log
    exact (Nat.mul_le_mul hkm (Nat.pow_le_pow_left hp_ge_pmin 2)).trans hrB
  have hN3:6*(Q_rB.card*(k*p_min^2))≤12000*(Nat.log 2 (2*N)+1)*N^3:=by
   calc 6*(Q_rB.card*(k*p_min^2))
       ≤ 6*(12000*(Nat.log 2 (2*N)+1)*N.choose 3):=Yd 6 hnat
     _=12000*(Nat.log 2 (2*N)+1)*(6*N.choose 3):=by ring
     _≤12000*(Nat.log 2 (2*N)+1)*N^3:=Yd _ (Wq N)
  have hR:6*(Q_rB.card:ℝ)*((k:ℝ)*(p_min:ℝ)^2) ≤12000*((Nat.log 2 (2*N):ℝ)+1)*(N:ℝ)^3:=by
   have h1:((6*(Q_rB.card*(k*p_min^2)):ℕ):ℝ) ≤((12000*(Nat.log 2 (2*N)+1)*N^3:ℕ):ℝ):=by exact_mod_cast hN3
   push_cast at h1;linarith
  have hkp2_lb:(N:ℝ)^((11:ℝ)/10)/(2*10^34:ℝ)≤(k:ℝ)*(p_min:ℝ)^2:=by
   have hp2:(N:ℝ)^((3:ℝ)/5)/(10^30:ℝ)≤(p_min:ℝ)^2:=by
    have hsq:=pow_le_pow_left₀ (by positivity) hp_min_lb 2
    have hr:((N:ℝ)^((3:ℝ)/10))^2=(N:ℝ)^((3:ℝ)/5):=by rw[←Real.rpow_natCast,←Real.rpow_mul hN_pos.le];norm_num
    rw[div_pow,hr] at hsq
    have h10:((10^15:ℝ))^2=(10^30:ℝ):=by norm_num
    rw[h10] at hsq;exact hsq
   have hr11:(N:ℝ)^((1:ℝ)/2)*(N:ℝ)^((3:ℝ)/5)=(N:ℝ)^((11:ℝ)/10):=by rw[←Real.rpow_add hN_pos];norm_num
   calc (N:ℝ)^((11:ℝ)/10)/(2*10^34:ℝ)
       = ((N:ℝ)^((1:ℝ)/2)/20000)*((N:ℝ)^((3:ℝ)/5)/(10^30:ℝ)):=by rw[←hr11];ring
     _≤(k:ℝ)*(p_min:ℝ)^2:=mul_le_mul hk_lb hp2 (by positivity) (by positivity)
  have hrhs_le:12000*((Nat.log 2 (2*N):ℝ)+1)*(N:ℝ)^3 ≤24000*(N:ℝ)^((61:ℝ)/20):=by
   have hr61:(N:ℝ)^((1:ℝ)/20)*(N:ℝ)^3=(N:ℝ)^((61:ℝ)/20):=by rw[show (N:ℝ)^3=(N:ℝ)^(3:ℝ) from (Real.rpow_natCast _ 3).symm,←Real.rpow_add hN_pos];norm_num
   calc 12000*((Nat.log 2 (2*N):ℝ)+1)*(N:ℝ)^3
       ≤ 12000*(2*(N:ℝ)^((1:ℝ)/20))*(N:ℝ)^3:=by nlinarith[pow_nonneg hN_pos.le 3]
     _=24000*((N:ℝ)^((1:ℝ)/20)*(N:ℝ)^3):=by ring
     _=24000*(N:ℝ)^((61:ℝ)/20):=by rw[hr61]
  have hdom:24000*(N:ℝ)^((61:ℝ)/20) ≤6*((5/1000:ℝ)*(N:ℝ)^2)*((N:ℝ)^((11:ℝ)/10)/(2*10^34:ℝ)):=by
   have hr1:(N:ℝ)^((61:ℝ)/20)=(N:ℝ)^((195:ℝ)/100)*(N:ℝ)^((11:ℝ)/10):=by rw[←Real.rpow_add hN_pos];norm_num
   have hmul:=Zo h195 (show (0:ℝ)≤(N:ℝ)^((11:ℝ)/10) by positivity)
   rw[mul_assoc,←hr1] at hmul
   have hre:6*((5/1000:ℝ)*(N:ℝ)^2)*((N:ℝ)^((11:ℝ)/10)/(2*10^34:ℝ)) =(3/(2*10^36:ℝ))*((N:ℝ)^2*(N:ℝ)^((11:ℝ)/10)):=by ring
   have hc:(24000:ℝ)≤(3/(2*10^36:ℝ))*(10^42:ℝ):=by norm_num
   have hnn:(0:ℝ)≤(N:ℝ)^((61:ℝ)/20):=by positivity
   calc 24000*(N:ℝ)^((61:ℝ)/20)
       ≤ ((3/(2*10^36:ℝ))*(10^42:ℝ))*(N:ℝ)^((61:ℝ)/20):=Zo hc hnn
     _=(3/(2*10^36:ℝ))*((10^42:ℝ)*(N:ℝ)^((61:ℝ)/20)):=by ring
     _≤(3/(2*10^36:ℝ))*((N:ℝ)^2*(N:ℝ)^((11:ℝ)/10)):=Zp hmul (by positivity)
     _=6*((5/1000:ℝ)*(N:ℝ)^2)*((N:ℝ)^((11:ℝ)/10)/(2*10^34:ℝ)):=hre.symm
  have hstep:6*(Q_rB.card:ℝ)*((N:ℝ)^((11:ℝ)/10)/(2*10^34:ℝ)) ≤6*((5/1000:ℝ)*(N:ℝ)^2)*((N:ℝ)^((11:ℝ)/10)/(2*10^34:ℝ)):=by
   have hle1:=Zp hkp2_lb (show (0:ℝ)≤6*(Q_rB.card:ℝ) by positivity)
   linarith only[hle1,hR,hrhs_le,hdom]
  exact le_of_mul_le_mul_right (by linarith only[hstep] :(Q_rB.card:ℝ)*(6*((N:ℝ)^((11:ℝ)/10)/(2*10^34:ℝ))) ≤((5/1000:ℝ)*(N:ℝ)^2)*(6*((N:ℝ)^((11:ℝ)/10)/(2*10^34:ℝ)))) (by positivity)
private lemma Vh (N s₂:ℕ) (hN:1≤ N)
  (h1910a:10000*8*(512:ℝ)^6*(N:ℝ)^((19:ℝ)/10)≤(N:ℝ)^2)
  (hs₂_ub:(s₂:ℝ)≤60*(N:ℝ)^((1:ℝ)/2))
  (Q'':Zf (Zf ℕ)) (S₀:Zf ℕ)
  (hQ''_sub:Zt N Q'')
  (hQ''_nonAP:∀ S∈Q'',¬ IsAP S/\S.card< s₂)
  (hstar:∀ c∈Icc 1 N,∃ S∈Q'',c∉S)
  (hS₀:S₀∈Q'') (hS₀_ne:S₀.Nonempty)
  (hk_small:10000*S₀.card≤ Nat.sqrt N) :
  (Q''.card:ℝ)≤(29/1000:ℝ)*(N:ℝ)^2:=by
 have hN_pos:(0:ℝ)<(N:ℝ):=by exact_mod_cast (by omega:0< N)
 set k:=S₀.card
 have hcov:Q''⊆S₀.biUnion (fun c=>Q''.filter (fun S=>c∈S)):=by
  intro S hS
  by_cases heq:S=S₀
  ·subst heq
   obtain⟨c,hc⟩:=hS₀_ne;exact mem_biUnion.mpr ⟨c,hc,Za.mpr ⟨hS,hc⟩⟩
  ·obtain⟨l,hl,hl'⟩:=hQ''_sub.2 (Zc.mpr hS) (Zc.mpr hS₀) heq
   obtain⟨c,_,_,hk',-,hX⟩:=Qn (S∩S₀) l hl hl'
   have hc:=Zn.mp ((hX c).mpr ⟨0,hk',by simp⟩)
   exact mem_biUnion.mpr ⟨c,hc.2,Za.mpr ⟨hS,hc.1⟩⟩
 have hper_c:∀ c∈S₀,((Q''.filter (fun S=>c∈S)).card:ℝ) ≤60*(N:ℝ)^((3:ℝ)/2)+8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5):=by
  intro c hcS₀;have hcI:c∈Icc 1 N:=Zy.mp (hQ''_sub.1 hS₀) hcS₀;obtain⟨Tc,hTc,hcnotTc⟩:=hstar c hcI
  have hTsub:Tc⊆(Icc 1 N).erase c:=fun x hx =>
   Zw.mpr ⟨fun h=>hcnotTc (h ▸ hx),Zy.mp (hQ''_sub.1 hTc) hx⟩
  have hQc_sub:Zt N (Q''.filter (fun S=>c∈S)) :=⟨(Zl _ _).trans hQ''_sub.1,fun S hS T hT hST =>
    hQ''_sub.2 (Zc.mpr (Zl _ _ (Zc.mp hS)))
     (Zc.mpr (Zl _ _ (Zc.mp hT))) hST⟩
  have hThit:∀ S∈Q''.filter (fun S=>c∈S),(S∩Tc).Nonempty:=by
   intro S hS;obtain⟨hSQ'',hcS⟩:=Za.mp hS
   have hne:S≠Tc:=fun h=>hcnotTc (h ▸ hcS)
   obtain⟨l,hl,hl'⟩:=hQ''_sub.2 (Zc.mpr hSQ'') (Zc.mpr hTc) hne;obtain⟨a,_,_,hk',-,hX⟩:=Qn (S∩Tc) l hl hl'
   exact⟨a,(hX a).mpr ⟨0,hk',by simp⟩⟩
  have hbd:=Q6 N c hN hcI (Q''.filter (fun S=>c∈S)) Tc
   hQc_sub (fun S hS=>(hQ''_nonAP S (Za.mp hS).1).1)
   (fun S hS=>(Za.mp hS).2) hTsub hThit
  have hTlt:(Tc.card:ℝ)≤(s₂:ℝ):=by exact_mod_cast le_of_lt (hQ''_nonAP Tc hTc).2
  have hTN:(Tc.card:ℝ)*(N:ℝ)≤60*(N:ℝ)^((3:ℝ)/2):=by
   have hr:(N:ℝ)^((1:ℝ)/2)*(N:ℝ)=(N:ℝ)^((3:ℝ)/2):=by
    calc (N:ℝ)^((1:ℝ)/2)*(N:ℝ)
        = (N:ℝ)^((1:ℝ)/2)*(N:ℝ)^(1:ℝ):=by rw[Real.rpow_one]
      _=(N:ℝ)^((1:ℝ)/2+1):=(Real.rpow_add hN_pos _ _).symm
      _=(N:ℝ)^((3:ℝ)/2):=by norm_num
   nlinarith
  nlinarith[sq_nonneg (Tc.card:ℝ)]
 have hsum:(Q''.card:ℝ) ≤(k:ℝ)*(60*(N:ℝ)^((3:ℝ)/2)+8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5)):=by
  calc (Q''.card:ℝ)
      ≤ ∑ c∈S₀,((Q''.filter (fun S=>c∈S)).card:ℝ):=by exact_mod_cast (Zm hcov).trans card_biUnion_le
    _≤∑ _c∈S₀,(60*(N:ℝ)^((3:ℝ)/2)+8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5)) :=
        Finset.sum_le_sum hper_c
    _=(k:ℝ)*(60*(N:ℝ)^((3:ℝ)/2)+8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5)):=by
        rw[Finset.sum_const,nsmul_eq_mul]
 have hkR:(k:ℝ)≤(N:ℝ)^((1:ℝ)/2)/10000:=by
  have h1:10000*(k:ℝ)≤(Nat.sqrt N:ℝ):=by exact_mod_cast hk_small
  have h2:(Nat.sqrt N:ℝ)≤(N:ℝ)^((1:ℝ)/2):=by
   rw[←Real.sqrt_eq_rpow (N:ℝ),Real.le_sqrt (by positivity) hN_pos.le]
   exact_mod_cast (by simpa [sq] using Nat.sqrt_le N:(Nat.sqrt N)^2≤ N)
  linarith
 have hr2:(N:ℝ)^((1:ℝ)/2)*(N:ℝ)^((3:ℝ)/2)=(N:ℝ)^2:=by rw[←Real.rpow_add hN_pos];norm_num
 have hr19:(N:ℝ)^((1:ℝ)/2)*(N:ℝ)^((7:ℝ)/5)=(N:ℝ)^((19:ℝ)/10):=by rw[←Real.rpow_add hN_pos];norm_num
 have hterm1:(k:ℝ)*(60*(N:ℝ)^((3:ℝ)/2))≤(6/1000:ℝ)*(N:ℝ)^2:=by
  calc (k:ℝ)*(60*(N:ℝ)^((3:ℝ)/2))
      ≤ ((N:ℝ)^((1:ℝ)/2)/10000)*(60*(N:ℝ)^((3:ℝ)/2)) :=Zo hkR (by positivity)
    _=(6/1000:ℝ)*((N:ℝ)^((1:ℝ)/2)*(N:ℝ)^((3:ℝ)/2)):=by ring
    _=(6/1000:ℝ)*(N:ℝ)^2:=by rw[hr2]
 have hterm2:(k:ℝ)*(8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5))≤(1/1000:ℝ)*(N:ℝ)^2:=by
  have h19:10000*(8*(512:ℝ)^6*(N:ℝ)^((19:ℝ)/10))≤(N:ℝ)^2:=by
   have heq:10000*(8*(512:ℝ)^6*(N:ℝ)^((19:ℝ)/10)) =10000*8*(512:ℝ)^6*(N:ℝ)^((19:ℝ)/10):=by ring
   linarith only[h1910a,heq]
  calc (k:ℝ)*(8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5))
      ≤ ((N:ℝ)^((1:ℝ)/2)/10000)*(8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5)) :=Zo hkR (by positivity)
    _≤8*(512:ℝ)^6*((N:ℝ)^((1:ℝ)/2)*(N:ℝ)^((7:ℝ)/5)):=by
        have:(0:ℝ)≤8*(512:ℝ)^6*((N:ℝ)^((1:ℝ)/2)*(N:ℝ)^((7:ℝ)/5)):=by positivity
        linarith
    _=8*(512:ℝ)^6*(N:ℝ)^((19:ℝ)/10):=by rw[hr19]
    _≤(1/1000:ℝ)*(N:ℝ)^2:=by linarith only[h19,sq_nonneg (N:ℝ)]
 have hdist:(k:ℝ)*(60*(N:ℝ)^((3:ℝ)/2)+8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5)) =(k:ℝ)*(60*(N:ℝ)^((3:ℝ)/2))+(k:ℝ)*(8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5)):=by ring
 linarith only[hsum,hdist,hterm1,hterm2,sq_nonneg (N:ℝ)]
lemma X3 :∀ᶠ N:ℕ in Filter.atTop,∀ (Q_small:Zf (Zf ℕ)),Zt N Q_small →
   (∀ S∈Q_small,¬ IsAP S/\S.card< Nat.ceil ((N:ℝ)^((2:ℝ)/3))) →
   (∀ c∈Icc 1 N,∃ S∈Q_small,c∉S) →
   (Q_small.card:ℝ)≤(5/100:ℝ)*(N:ℝ)^2:=by
 filter_upwards [Filter.eventually_ge_atTop (10^12:ℕ),Qi (a:=(5:ℝ)/3) (b:=2) (C:=10000) (by norm_num),Qi (a:=(7:ℝ)/5) (b:=2) (C:=10000*8*(512:ℝ)^6) (by norm_num),Qi (a:=(19:ℝ)/10) (b:=2) (C:=10000*8*(512:ℝ)^6) (by norm_num),Qi (a:=(1:ℝ)/10) (b:=(3:ℝ)/10) (C:=10^22) (by norm_num),Qi (a:=(195:ℝ)/100) (b:=2) (C:=10^42) (by norm_num),Wr (ε:=(1:ℝ)/100) (by norm_num),Wr (ε:=(1:ℝ)/20) (by norm_num)
 ] with N hN_big h53 h75 h1910a h310 h195 hlog100 hlog20
 intro Q_small hQ hQspec hempty;rw[Real.rpow_two] at h53 h75 h1910a h195
 have hN1:1≤ N:=by omega
 have hN_pos:(0:ℝ)<(N:ℝ):=by exact_mod_cast (by omega:0< N)
 have hN_bigR:((10^12:ℕ):ℝ)≤(N:ℝ):=by exact_mod_cast hN_big
 set s₂:=60*Nat.sqrt N
 have hsqrtN_ge:10^6≤ Nat.sqrt N:=by rw[Nat.le_sqrt];norm_num;omega
 have hs₂_big:5100≤ s₂:=by omega
 have hs₂_lb:(59:ℝ)*(N:ℝ)^((1:ℝ)/2)≤(s₂:ℝ):=by
  have h1:N<(Nat.sqrt N+1)^2:=by simpa [sq] using Nat.lt_succ_sqrt N
  have h1R:(N:ℝ)≤((Nat.sqrt N:ℝ)+1)^2:=by exact_mod_cast le_of_lt h1
  have hsq:Real.sqrt (N:ℝ)≤(Nat.sqrt N:ℝ)+1:=by
   rw[Real.sqrt_le_left (by positivity)];exact h1R
  have hsq_eq:(N:ℝ)^((1:ℝ)/2)=Real.sqrt (N:ℝ):=(Real.sqrt_eq_rpow (N:ℝ)).symm
  have hsqrtR:(10^6:ℝ)≤(Nat.sqrt N:ℝ):=by exact_mod_cast hsqrtN_ge
  rw[hsq_eq];push_cast [s₂];nlinarith
 have hs₂_ub:(s₂:ℝ)≤60*(N:ℝ)^((1:ℝ)/2):=by
  have h1:(Nat.sqrt N)^2≤ N:=by simpa [sq] using Nat.sqrt_le N
  have h1R:((Nat.sqrt N:ℝ))^2≤(N:ℝ):=by exact_mod_cast h1
  have hsq:(Nat.sqrt N:ℝ)≤ Real.sqrt (N:ℝ):=by
   rw[Real.le_sqrt (by positivity) hN_pos.le];exact h1R
  rw[←Real.sqrt_eq_rpow (N:ℝ)];push_cast [s₂];linarith
 set Q_hi:=Q_small.filter (fun S=>s₂≤ S.card)
 set Q'':=Q_small.filter (fun S=>¬ (s₂≤ S.card))
 have hQsplit:Q_small.card=Q_hi.card+Q''.card :=(card_filter_add_card_filter_not (s:=Q_small) (p:=fun S=>s₂≤ S.card)).symm
 have hQhi_sub:Zt N Q_hi :=⟨(Zl _ _).trans hQ.1,fun S hS T hT hST =>
   hQ.2 (Zc.mpr (Zl _ _ (Zc.mp hS)))
    (Zc.mpr (Zl _ _ (Zc.mp hT))) hST⟩
 have hQ''_sub:Zt N Q'' :=⟨(Zl _ _).trans hQ.1,fun S hS T hT hST =>
   hQ.2 (Zc.mpr (Zl _ _ (Zc.mp hS)))
    (Zc.mpr (Zl _ _ (Zc.mp hT))) hST⟩
 have hQhi_bd:(Q_hi.card:ℝ)≤(21/1000:ℝ)*(N:ℝ)^2:=by
  have h1:=Xs N s₂ hs₂_big Q_hi hQhi_sub
   (fun S hS=>(hQspec S (Za.mp hS).1).1)
   (fun S hS=>(Za.mp hS).2)
  have hs₂_sq:3481*(N:ℝ)≤(s₂:ℝ)^2:=by
   have hsq:=pow_le_pow_left₀ (by positivity) hs₂_lb 2
   have hr:((N:ℝ)^((1:ℝ)/2))^2=(N:ℝ):=by rw[←Real.rpow_natCast,←Real.rpow_mul hN_pos.le];norm_num
   nlinarith
  have hdiv:70*(N:ℝ)^3/(s₂:ℝ)^2≤(21/1000:ℝ)*(N:ℝ)^2:=by
   rw[div_le_iff₀ (by positivity:(0:ℝ)<(s₂:ℝ)^2)]
   nlinarith
  exact h1.trans hdiv
 suffices hQ''_bd:(Q''.card:ℝ)≤(29/1000:ℝ)*(N:ℝ)^2 by
  have hspR:(Q_small.card:ℝ)=(Q_hi.card:ℝ)+(Q''.card:ℝ):=by exact_mod_cast hQsplit
  linarith
 by_cases hstar:∃ c∈Icc 1 N,∀ S∈Q'',c∈S
 ·obtain⟨c,hcI,hc_all⟩:=hstar
  obtain⟨T,hTQ,hcnotT⟩:=hempty c hcI
  have hTsub:T⊆(Icc 1 N).erase c:=fun x hx =>
   Zw.mpr ⟨fun h=>hcnotT (h ▸ hx),Zy.mp (hQ.1 hTQ) hx⟩
  have hThit:∀ S∈Q'',(S∩T).Nonempty:=by
   intro S hS;have hSQ:=(Za.mp hS).1
   have hne:S≠T:=fun h=>hcnotT (h ▸ hc_all S hS)
   obtain⟨l,hl,hl'⟩:=hQ.2 (Zc.mpr hSQ) (Zc.mpr hTQ) hne;obtain⟨a,_,_,hk,-,hX⟩:=Qn (S∩T) l hl hl'
   exact⟨a,(hX a).mpr ⟨0,hk,by simp⟩⟩
  have hbd:=Q6 N c hN1 hcI Q'' T hQ''_sub
   (fun S hS=>(hQspec S (Za.mp hS).1).1) hc_all hTsub hThit
  have hTcard:(T.card:ℝ)≤(N:ℝ)^((2:ℝ)/3)+1:=by
   have hlt:T.card< Nat.ceil ((N:ℝ)^((2:ℝ)/3)):=(hQspec T hTQ).2
   have hle:(T.card:ℝ)≤(Nat.ceil ((N:ℝ)^((2:ℝ)/3)):ℝ):=by exact_mod_cast le_of_lt hlt
   have hcl:=Nat.ceil_lt_add_one (show (0:ℝ)≤(N:ℝ)^((2:ℝ)/3) by positivity)
   linarith
  have hTN:(T.card:ℝ)*(N:ℝ)≤(N:ℝ)^((5:ℝ)/3)+(N:ℝ):=by
   have hr:(N:ℝ)^((2:ℝ)/3)*(N:ℝ)=(N:ℝ)^((5:ℝ)/3):=by
    calc (N:ℝ)^((2:ℝ)/3)*(N:ℝ)
        = (N:ℝ)^((2:ℝ)/3)*(N:ℝ)^(1:ℝ):=by rw[Real.rpow_one]
      _=(N:ℝ)^((2:ℝ)/3+1):=(Real.rpow_add hN_pos _ _).symm
      _=(N:ℝ)^((5:ℝ)/3):=by norm_num
   nlinarith
  have hN_le_sq:(N:ℝ)≤(N:ℝ)^2/10000:=by
   have h12:(10^12:ℝ)≤(N:ℝ):=by exact_mod_cast hN_big
   nlinarith only[h12]
  linarith only[hbd,hTN,hN_le_sq,h53,h75,sq_nonneg (T.card:ℝ)]
 ·push Not at hstar
  by_cases hQ''1:Q''.card≤1
  ·have h1:(Q''.card:ℝ)≤1:=by exact_mod_cast hQ''1
   have h12:(10^12:ℝ)≤(N:ℝ):=by exact_mod_cast hN_big
   nlinarith only[h1,h12]
  have hQ''ne:Q''.Nonempty:=card_pos.mp (by omega)
  obtain⟨S₀,hS₀,hS₀_min⟩:=exists_min_image Q'' card hQ''ne
  have hS₀_ne:S₀.Nonempty:=by
   obtain⟨T,hT,hTS₀⟩:=exists_mem_ne (by omega:1< Q''.card) S₀
   obtain⟨l,hl,hl'⟩:=hQ''_sub.2 (Zc.mpr hS₀) (Zc.mpr hT) hTS₀.symm;obtain⟨a,_,_,hk',-,hX⟩:=Qn (S₀∩T) l hl hl'
   exact⟨a,(Zn.mp ((hX a).mpr ⟨0,hk',by simp⟩)).1⟩
  set k:=S₀.card;have hk3:3≤ k:=Wk hS₀_ne (hQspec S₀ (Za.mp hS₀).1).1
  by_cases hk_small:10000*k≤ Nat.sqrt N
  ·exact Vh N s₂ hN1 h1910a hs₂_ub Q'' S₀ hQ''_sub
    (fun S hS=>⟨(hQspec S (Za.mp hS).1).1,by have:=(Za.mp hS).2;omega⟩)
    hstar hS₀ hS₀_ne hk_small
  ·
   push Not at hk_small
   have hk_lb:(N:ℝ)^((1:ℝ)/2)/20000≤(k:ℝ):=by
    have h1:(Nat.sqrt N:ℝ)<10000*(k:ℝ):=by exact_mod_cast hk_small
    have h2:(59/60:ℝ)*(N:ℝ)^((1:ℝ)/2)≤(Nat.sqrt N:ℝ):=by push_cast [s₂] at hs₂_lb;linarith
    linarith
   have hN15:(10^22:ℝ)≤(N:ℝ)^((1:ℝ)/5):=by
    have hr:(N:ℝ)^((3:ℝ)/10)=(N:ℝ)^((1:ℝ)/5)*(N:ℝ)^((1:ℝ)/10):=by rw[←Real.rpow_add hN_pos];norm_num
    rw[hr] at h310
    exact le_of_mul_le_mul_right h310 (by positivity)
   have hk_big:5100≤ k:=by
    have hN12:(10^22:ℝ)≤(N:ℝ)^((1:ℝ)/2) :=hN15.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by norm_num))
    have hkR:(5100:ℝ)≤(k:ℝ):=by linarith
    exact_mod_cast hkR
   set q₀:=Nat.sqrt (Nat.sqrt N)
   have hq₀_lb:(N:ℝ)^((1:ℝ)/4)/2≤(q₀:ℝ):=by
    have h1:N<(Nat.sqrt N+1)^2:=by simpa [sq] using Nat.lt_succ_sqrt N
    have h2:Nat.sqrt N<(q₀+1)^2:=by simpa [sq] using Nat.lt_succ_sqrt (Nat.sqrt N)
    have hq1:10^3≤ q₀:=by
     rw[Nat.le_sqrt];exact le_trans (by norm_num) hsqrtN_ge
    have h2R:(Nat.sqrt N:ℝ)≤((q₀:ℝ)+1)^2:=by exact_mod_cast le_of_lt h2
    have h1R:(N:ℝ)≤(((q₀:ℝ)+1)^2+1)^2:=by
     have h1':(N:ℝ)≤((Nat.sqrt N:ℝ)+1)^2:=by exact_mod_cast le_of_lt h1
     nlinarith[sq_nonneg ((Nat.sqrt N:ℝ)+1)]
    have h4:(((q₀:ℝ)+1)^2+1)^2≤(2*(q₀:ℝ))^4:=by
     have hqR:(10^3:ℝ)≤(q₀:ℝ):=by exact_mod_cast hq1
     have h4a:((q₀:ℝ)+1)^2+1≤(2*(q₀:ℝ))^2:=by nlinarith only[hqR]
     have h4b:(0:ℝ)≤((q₀:ℝ)+1)^2+1:=by positivity
     calc (((q₀:ℝ)+1)^2+1)^2≤((2*(q₀:ℝ))^2)^2:=pow_le_pow_left₀ h4b h4a 2
       _=(2*(q₀:ℝ))^4:=by ring
    have hNle:(N:ℝ)≤(2*(q₀:ℝ))^(4:ℝ):=by
     rw[show (4:ℝ)=((4:ℕ):ℝ) by norm_num,Real.rpow_natCast];linarith
    have hr:=Real.rpow_le_rpow hN_pos.le hNle (show (0:ℝ)≤1/4 by norm_num)
    rw[←Real.rpow_mul (by positivity:(0:ℝ)≤2*(q₀:ℝ))] at hr
    norm_num at hr;linarith
   have hq₀_ub:(q₀:ℝ)≤(N:ℝ)^((1:ℝ)/4):=by
    have h1:q₀^4≤ N:=by
     have a:q₀^2≤ Nat.sqrt N:=by simpa [sq] using Nat.sqrt_le (Nat.sqrt N)
     have b:(Nat.sqrt N)^2≤ N:=by simpa [sq] using Nat.sqrt_le N
     calc q₀^4=(q₀^2)^2:=by ring
       _≤(Nat.sqrt N)^2:=Nat.pow_le_pow_left a 2
       _≤ N:=b
    have h1R:((q₀:ℝ))^(4:ℝ)≤(N:ℝ):=by
     rw[show (4:ℝ)=((4:ℕ):ℝ) by norm_num,Real.rpow_natCast]
     exact_mod_cast h1
    have hr:=Real.rpow_le_rpow (by positivity) h1R (show (0:ℝ)≤1/4 by norm_num)
    rw[←Real.rpow_mul (Nat.cast_nonneg q₀)] at hr;norm_num at hr;exact hr
   have hq₀_pos:1≤ q₀:=by
    have hq1:10^3≤ q₀:=by rw[Nat.le_sqrt];exact le_trans (by norm_num) hsqrtN_ge
    omega
   have hk_4q₀:4*q₀+4≤ k:=by
    have hN14:(10^22:ℝ)≤(N:ℝ)^((1:ℝ)/4) :=hN15.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by norm_num))
    have hsq:(N:ℝ)^((1:ℝ)/4)*(N:ℝ)^((1:ℝ)/4)=(N:ℝ)^((1:ℝ)/2):=by rw[←Real.rpow_add hN_pos];norm_num
    have hN14_le:4*(N:ℝ)^((1:ℝ)/4)+4≤(N:ℝ)^((1:ℝ)/2)/20000:=by nlinarith only[hN14,hsq]
    have:(4*q₀+4:ℝ)≤(k:ℝ):=by linarith
    exact_mod_cast this
   set T:=Nat.ceil ((512:ℝ)^3*(N:ℝ)^((1:ℝ)/5))
   have hT_pos:1≤ T:=by
    have h1:(1:ℝ)≤(512:ℝ)^3*(N:ℝ)^((1:ℝ)/5):=by
     have:(1:ℝ)≤(N:ℝ)^((1:ℝ)/5):=Real.one_le_rpow (by exact_mod_cast hN1) (by norm_num)
     linarith
    have hTc:(512:ℝ)^3*(N:ℝ)^((1:ℝ)/5)≤(T:ℝ):=Nat.le_ceil _
    have h1T:(1:ℝ)≤(T:ℝ):=by linarith
    exact_mod_cast h1T
   have hT_bd:∀ L∈Icc 1 N,L.divisors.card≤ T:=by
    intro L hL;have h1:=Xj L (Zb.mp hL).1
    have h2:(L:ℝ)^((1:ℝ)/5)≤(N:ℝ)^((1:ℝ)/5) :=Real.rpow_le_rpow (Nat.cast_nonneg L) (by exact_mod_cast (Zb.mp hL).2) (by norm_num)
    have h3:(L.divisors.card:ℝ)≤(512:ℝ)^3*(N:ℝ)^((1:ℝ)/5) :=h1.trans (Zp h2 (by positivity))
    have h4:(L.divisors.card:ℝ)≤(T:ℝ):=h3.trans (Nat.le_ceil _);exact_mod_cast h4
   have hT_ub:(T:ℝ)≤(512:ℝ)^3*(N:ℝ)^((1:ℝ)/5)+1 :=le_of_lt (Nat.ceil_lt_add_one (by positivity))
   have hQ''_spec:∀ S∈Q'',¬ IsAP S/\k≤ S.card/\S.card< s₂:=fun S hS =>
    ⟨(hQspec S (Za.mp hS).1).1,hS₀_min S hS,by have:=(Za.mp hS).2;omega⟩
   obtain⟨hQnear_bd,hQmid_bd⟩:=Xk N k s₂ q₀ hN_big h310 hlog100
    hs₂_ub hk_lb hk_big hq₀_pos hq₀_lb hq₀_ub hk_4q₀ Q'' hQ''_sub hQ''_spec
   obtain⟨hQrA_bd,hQrB_bd⟩:=Xv N k T hN_big h310 h195 hlog20
    hk_lb hk_big hT_pos hT_bd hT_ub Q'' hQ''_sub (fun S hS=>hS₀_min S hS)
   set Q_near:=Q''.filter (fun S=>S.card-Qc S≤ q₀)
   set Q_mid:=Q''.filter (fun S=>q₀< S.card-Qc S/\100*(S.card-Qc S)< S.card)
   set Q_rA:=Q''.filter (fun S=>S.card≤100*(S.card-Qc S)/\4*T*Qc S+8≤ S.card)
   set Q_rB:=Q''.filter (fun S=>S.card≤100*(S.card-Qc S)/\¬ (4*T*Qc S+8≤ S.card))
   have hQ''_cov:Q''⊆Q_near∪Q_mid∪Q_rA∪Q_rB:=by
    intro S hS
    by_cases h1:S.card-Qc S≤ q₀
    ·exact Ze _ (Ze _ (Ze _ (Za.mpr ⟨hS,h1⟩)))
    ·by_cases h2:100*(S.card-Qc S)< S.card
     ·exact Ze _ (Ze _ (Zg _
       (Za.mpr ⟨hS,by omega,h2⟩)))
     ·by_cases h3:4*T*Qc S+8≤ S.card
      ·exact Ze _ (Zg _ (Za.mpr ⟨hS,by omega,h3⟩))
      ·exact Zg _ (Za.mpr ⟨hS,by omega,h3⟩)
   have htot:Q''.card≤ Q_near.card+Q_mid.card+Q_rA.card+Q_rB.card:=by have h1:=(Zm hQ''_cov).trans (Yh _ _);have h2:=Yh (Q_near∪Q_mid) Q_rA;have h3:=Yh Q_near Q_mid;omega
   have htotR:(Q''.card:ℝ)≤(Q_near.card:ℝ)+(Q_mid.card:ℝ)+(Q_rA.card:ℝ)+(Q_rB.card:ℝ):=by exact_mod_cast htot
   linarith
private lemma Vk (N c d:ℕ) (hN:1≤ N) (hc:c∈Icc 1 N)
  (hd:d∈Icc 1 N) (Pd:Zf (Zf ℕ))
  (getU getV:Zf ℕ->ℕ)
  (hUV:∀ A∈Pd,getU A*d< c/\c+getV A*d≤ N ∧
   (∀ x,x∈A↔(∃ i≤ getU A,x=c-i*d)\/(∃ j≤ getV A,x=c+j*d))) :
  let Pd1:=Pd.filter (fun A=>1≤ getU A/\1≤ getV A/\Nat.Coprime (getU A) (getV A))
  let E_LR:=Pd1.image (fun A=>({c-getU A*d,c+getV A*d}:Zf ℕ))
  let uMax:=(Pd.image getU).max.unbotD 0
  let vMax:=(Pd.image getV).max.unbotD 0
  let E_L:=(((Icc 1 uMax) ×ˢ (Icc 1 uMax)).filter (fun z=>z.1< z.2/\Nat.Coprime z.1 z.2)).image
   (fun z=>({c-z.1*d,c-z.2*d}:Zf ℕ))
  let E_R:=(((Icc 1 vMax) ×ˢ (Icc 1 vMax)).filter (fun z=>z.1< z.2/\Nat.Coprime z.1 z.2)).image
   (fun z=>({c+z.1*d,c+z.2*d}:Zf ℕ))
  (Pd.card:ℝ)≤(E_LR.card:ℝ)+(E_L.card:ℝ)+(E_R.card:ℝ) +110*((N:ℝ)/(d:ℝ))*(log (N:ℝ)+2):=by
 intro Pd1 E_LR uMax vMax E_L E_R;have hd1:=(Zb.mp hd).1;have hdN:=(Zb.mp hd).2
 rcases Pd.eq_empty_or_nonempty with hPd0|hPdne
 ·rw[hPd0,card_empty,Nat.cast_zero]
  have hlog_nn:0≤ log (N:ℝ):=Real.log_nonneg (by exact_mod_cast hN)
  positivity
 have huMax_ex:1≤ uMax->∃ A∈Pd,getU A=uMax:=by
  intro hu;obtain⟨A,hA,hAmax⟩:=exists_max_image Pd getU hPdne
  have hmax:(Pd.image getU).max=(getU A:WithBot ℕ):=by
   refine le_antisymm ?_ (Finset.le_max (mem_image_of_mem getU hA))
   rw[Finset.max_le_iff];intro x hx;obtain⟨B,hB,rfl⟩:=Zi.mp hx;exact WithBot.coe_le_coe.mpr (hAmax B hB)
  exact⟨A,hA,by simp only[uMax,hmax];rfl⟩
 have hvMax_ex:1≤ vMax->∃ A∈Pd,getV A=vMax:=by
  intro hv;obtain⟨A,hA,hAmax⟩:=exists_max_image Pd getV hPdne
  have hmax:(Pd.image getV).max=(getV A:WithBot ℕ):=by
   refine le_antisymm ?_ (Finset.le_max (mem_image_of_mem getV hA))
   rw[Finset.max_le_iff];intro x hx;obtain⟨B,hB,rfl⟩:=Zi.mp hx;exact WithBot.coe_le_coe.mpr (hAmax B hB)
  exact⟨A,hA,by simp only[vMax,hmax];rfl⟩
 have huMax_le:∀ A∈Pd,getU A≤ uMax:=by
  intro A hA;obtain⟨B,hB,hBmax⟩:=exists_max_image Pd getU hPdne
  have hmax:(Pd.image getU).max=(getU B:WithBot ℕ):=by
   refine le_antisymm ?_ (Finset.le_max (mem_image_of_mem getU hB))
   rw[Finset.max_le_iff];intro x hx;obtain⟨C,hC,rfl⟩:=Zi.mp hx;exact WithBot.coe_le_coe.mpr (hBmax C hC)
  have:uMax=getU B:=by simp only[uMax,hmax];rfl
  rw[this];exact hBmax A hA
 have hvMax_le:∀ A∈Pd,getV A≤ vMax:=by
  intro A hA;obtain⟨B,hB,hBmax⟩:=exists_max_image Pd getV hPdne
  have hmax:(Pd.image getV).max=(getV B:WithBot ℕ):=by
   refine le_antisymm ?_ (Finset.le_max (mem_image_of_mem getV hB))
   rw[Finset.max_le_iff];intro x hx;obtain⟨C,hC,rfl⟩:=Zi.mp hx;exact WithBot.coe_le_coe.mpr (hBmax C hC)
  have:vMax=getV B:=by simp only[vMax,hmax];rfl
  rw[this];exact hBmax A hA
 set Nd:=N/d;have hNd1:1≤ Nd:=Nat.div_pos hdN hd1
 have hu_le_Nd:uMax≤ Nd:=by
  rcases Nat.eq_zero_or_pos uMax with h0|hpos
  ·omega
  ·obtain⟨A,hAPd,hAu⟩:=huMax_ex hpos
   have huc:=(hUV A hAPd).1;rw[hAu] at huc;have hcN:=(Zb.mp hc).2
   exact (Nat.le_div_iff_mul_le hd1).mpr (by omega)
 have hv_le_Nd:vMax≤ Nd:=by
  rcases Nat.eq_zero_or_pos vMax with h0|hpos
  ·omega
  ·obtain⟨A,hAPd,hAv⟩:=hvMax_ex hpos
   have hvN:=(hUV A hAPd).2.1;rw[hAv] at hvN
   exact (Nat.le_div_iff_mul_le hd1).mpr (by omega)
 have hinj_UV:Set.InjOn (fun A=>(getU A,getV A)) (Pd:Set (Zf ℕ)):=by intro A hA B hB heq;have eu:getU A=getU B:=congrArg Prod.fst heq;have ev:getV A=getV B:=congrArg Prod.snd heq;ext x;rw[(hUV A (Zc.mp hA)).2.2 x,(hUV B (Zc.mp hB)).2.2 x,eu,ev]
 have hELR_eq:E_LR.card=Pd1.card:=by
  refine card_image_of_injOn fun A hA B hB heq=>?_
  obtain⟨hAPd,huA,hvA,-⟩:=Za.mp (Zc.mp hA);obtain⟨hBPd,huB,hvB,-⟩:=Za.mp (Zc.mp hB);have hucA:=(hUV A hAPd).1;have hucB:=(hUV B hBPd).1
  have h1:c-getU A*d< c:=by have:=Nat.mul_pos huA hd1;omega
  have h2:c< c+getV A*d:=by have:=Nat.mul_pos hvA hd1;omega
  have h3:c-getU B*d< c:=by have:=Nat.mul_pos huB hd1;omega
  have h4:c< c+getV B*d:=by have:=Nat.mul_pos hvB hd1;omega
  have hm1:c-getU A*d∈({c-getU B*d,c+getV B*d}:Zf ℕ):=by rw[←heq];simp
  have hm2:c+getV A*d∈({c-getU B*d,c+getV B*d}:Zf ℕ):=by rw[←heq];simp
  simp only[Zx,Zj] at hm1 hm2
  have eu:getU A=getU B:=Nat.eq_of_mul_eq_mul_right hd1 (by omega)
  have ev:getV A=getV B:=Nat.eq_of_mul_eq_mul_right hd1 (by omega)
  exact hinj_UV (Zc.mpr hAPd) (Zc.mpr hBPd) (Prod.ext eu ev)
 set Pd0:=Pd.filter (fun A=>getU A=0\/getV A=0)
 set Pd2:=Pd.filter (fun A=>1≤ getU A/\1≤ getV A/\¬ Nat.Coprime (getU A) (getV A))
 have hPd_sub:Pd⊆Pd1∪Pd0∪Pd2:=by
  intro A hA
  by_cases h0:getU A=0\/getV A=0
  ·exact Ze _ (Zg _ (Za.mpr ⟨hA,h0⟩))
  ·by_cases hcop:Nat.Coprime (getU A) (getV A)
   ·exact Ze _ (Ze _ (Za.mpr ⟨hA,by omega,by omega,hcop⟩))
   ·exact Zg _ (Za.mpr ⟨hA,by omega,by omega,hcop⟩)
 have hPd0_le:Pd0.card≤2*(Nd+1):=by
  have hmaps:Set.MapsTo (fun A=>(getU A,getV A)) (Pd0:Set (Zf ℕ))
    ((({0} ×ˢ Icc 0 Nd)∪(Icc 0 Nd ×ˢ {0}):Zf (ℕ × ℕ)):Set (ℕ × ℕ)):=by
   intro A hA;obtain⟨hAPd,h0⟩:=Za.mp (Zc.mp hA);have hu:=(huMax_le A hAPd).trans hu_le_Nd;have hv:=(hvMax_le A hAPd).trans hv_le_Nd;rw[Zc,Zd]
   rcases h0 with hu0|hv0
   ·left;exact Zh.mpr ⟨Zj.mpr hu0,Zb.mpr ⟨Nat.zero_le _,hv⟩⟩
   ·right;exact Zh.mpr ⟨Zb.mpr ⟨Nat.zero_le _,hu⟩,Zj.mpr hv0⟩
  have hinj0:Set.InjOn (fun A=>(getU A,getV A)) (Pd0:Set (Zf ℕ)) :=hinj_UV.mono (Finset.coe_subset.mpr (Zl _ _))
  calc Pd0.card≤(({0} ×ˢ Icc 0 Nd)∪(Icc 0 Nd ×ˢ {0})).card :=
        card_le_card_of_injOn _ hmaps hinj0
    _≤({0} ×ˢ Icc 0 Nd).card+(Icc 0 Nd ×ˢ {0}).card:=Yh _ _
    _=2*(Nd+1):=by simp[Nat.card_Icc];ring
 have hPd2_le:(Pd2.card:ℝ)≤(43/100:ℝ)*(uMax:ℝ)*(vMax:ℝ) +50*(Nd:ℝ)*(log (Nd:ℝ)+2):=by
  rcases Nat.eq_zero_or_pos uMax with hu0|hupos
  ·have hPd2_0:Pd2=∅:=by
    rw[eq_empty_iff_forall_notMem];intro A hA;obtain⟨hAPd,hu1,-⟩:=Za.mp hA
    have:=huMax_le A hAPd;omega
   rw[hPd2_0,card_empty,Nat.cast_zero]
   have:=Real.log_nonneg (show (1:ℝ)≤(Nd:ℝ) by exact_mod_cast hNd1);positivity
  rcases Nat.eq_zero_or_pos vMax with hv0|hvpos
  ·have hPd2_0:Pd2=∅:=by
    rw[eq_empty_iff_forall_notMem];intro A hA;obtain⟨hAPd,-,hv1,-⟩:=Za.mp hA
    have:=hvMax_le A hAPd;omega
   rw[hPd2_0,card_empty,Nat.cast_zero]
   have:=Real.log_nonneg (show (1:ℝ)≤(Nd:ℝ) by exact_mod_cast hNd1);positivity
  let Box:=((Icc 1 uMax) ×ˢ (Icc 1 vMax)).filter (fun z=>¬ Nat.Coprime z.1 z.2)
  have hmaps2:Set.MapsTo (fun A=>(getU A,getV A)) (Pd2:Set (Zf ℕ)) (Box:Set (ℕ × ℕ)):=by
   intro A hA;obtain⟨hAPd,hu1,hv1,hnc⟩:=Za.mp (Zc.mp hA)
   exact Zc.mpr (Za.mpr ⟨Zh.mpr
    ⟨Zb.mpr ⟨hu1,huMax_le A hAPd⟩,Zb.mpr ⟨hv1,hvMax_le A hAPd⟩⟩,hnc⟩)
  have hinj2:Set.InjOn (fun A=>(getU A,getV A)) (Pd2:Set (Zf ℕ)) :=hinj_UV.mono (Finset.coe_subset.mpr (Zl _ _))
  have hle:(Pd2.card:ℝ)≤(Box.card:ℝ):=by exact_mod_cast card_le_card_of_injOn _ hmaps2 hinj2
  have hbox:=Wt Nd 0 uMax 0 vMax hNd1 (by omega) (by omega)
  have heqB:Box=((Icc (0+1) (0+uMax)) ×ˢ (Icc (0+1) (0+vMax))).filter
    (fun z=>1< Nat.gcd z.1 z.2):=by
   ext ⟨x,y⟩;simp only[Box,Za,Zh,Zb,Nat.zero_add,Nat.Coprime]
   constructor
   ·rintro⟨⟨⟨hx1,hxu⟩,⟨hy1,hyv⟩⟩,hne⟩
    have hg:0< Nat.gcd x y:=Nat.gcd_pos_of_pos_left y (by omega)
    exact⟨⟨⟨hx1,hxu⟩,⟨hy1,hyv⟩⟩,by omega⟩
   ·rintro⟨hxy,hgt⟩
    exact⟨hxy,by omega⟩
  rw[heqB] at hle;exact hle.trans hbox
 have hEL_ge:(285/1000:ℝ)*(uMax:ℝ)^2-26*(Nd:ℝ)*(log (Nd:ℝ)+2)≤(E_L.card:ℝ):=by
  rcases Nat.eq_zero_or_pos uMax with hu0|hupos
  ·rw[hu0];norm_num
   have hlog_nn:0≤ log (Nd:ℝ):=Real.log_nonneg (by exact_mod_cast hNd1)
   have h1:(0:ℝ)≤26*(Nd:ℝ)*(log (Nd:ℝ)+2):=by positivity
   have h2:(0:ℝ)≤(E_L.card:ℝ):=Nat.cast_nonneg _;linarith
  have hinjL:Set.InjOn (fun z:ℕ × ℕ=>({c-z.1*d,c-z.2*d}:Zf ℕ))
    ((((Icc 1 uMax) ×ˢ (Icc 1 uMax)).filter (fun z=>z.1< z.2/\Nat.Coprime z.1 z.2)):Set (ℕ × ℕ)):=by
   intro ⟨i₁,j₁⟩ h1 ⟨i₂,j₂⟩ h2 heq;dsimp only at heq;obtain⟨hP1,hlt1,-⟩:=Za.mp (Zc.mp h1);obtain⟨hP2,hlt2,-⟩:=Za.mp (Zc.mp h2);dsimp only at hlt1 hlt2;obtain⟨A,hAPd,hAu⟩:=huMax_ex hupos;have huc:=(hUV A hAPd).1;rw[hAu] at huc;have hj1:j₁*d< c:=lt_of_le_of_lt (Yc d (Zb.mp (Zh.mp hP1).2).2) huc;have hj2:j₂*d< c:=lt_of_le_of_lt (Yc d (Zb.mp (Zh.mp hP2).2).2) huc;have hi1:i₁*d< j₁*d:=Nat.mul_lt_mul_of_pos_right hlt1 hd1;have hi2:i₂*d< j₂*d:=Nat.mul_lt_mul_of_pos_right hlt2 hd1
   have hm1:c-i₁*d∈({c-i₂*d,c-j₂*d}:Zf ℕ):=by rw[←heq];simp
   have hm2:c-j₁*d∈({c-i₂*d,c-j₂*d}:Zf ℕ):=by rw[←heq];simp
   simp only[Zx,Zj] at hm1 hm2
   ext <;> dsimp
   ·exact Nat.eq_of_mul_eq_mul_right hd1 (by omega)
   ·exact Nat.eq_of_mul_eq_mul_right hd1 (by omega)
  have heqL:E_L.card=(((Icc (0+1) (0+uMax)) ×ˢ (Icc (0+1) (0+uMax))).filter
    (fun z=>z.1< z.2/\Nat.gcd z.1 z.2=1)).card:=by
   rw[card_image_of_injOn hinjL];congr 1;ext ⟨x,y⟩;simp only[Za,Zh,Zb,Nat.zero_add,Nat.Coprime]
  rw[heqL];exact W5 Nd 0 uMax hNd1 (by omega)
 have hER_ge:(285/1000:ℝ)*(vMax:ℝ)^2-26*(Nd:ℝ)*(log (Nd:ℝ)+2)≤(E_R.card:ℝ):=by
  rcases Nat.eq_zero_or_pos vMax with hv0|hvpos
  ·rw[hv0];norm_num
   have hlog_nn:0≤ log (Nd:ℝ):=Real.log_nonneg (by exact_mod_cast hNd1)
   have h1:(0:ℝ)≤26*(Nd:ℝ)*(log (Nd:ℝ)+2):=by positivity
   have h2:(0:ℝ)≤(E_R.card:ℝ):=Nat.cast_nonneg _;linarith
  have hinjR:Set.InjOn (fun z:ℕ × ℕ=>({c+z.1*d,c+z.2*d}:Zf ℕ))
    ((((Icc 1 vMax) ×ˢ (Icc 1 vMax)).filter (fun z=>z.1< z.2/\Nat.Coprime z.1 z.2)):Set (ℕ × ℕ)):=by
   intro ⟨i₁,j₁⟩ h1 ⟨i₂,j₂⟩ h2 heq;dsimp only at heq;obtain⟨-,hlt1,-⟩:=Za.mp (Zc.mp h1);obtain⟨-,hlt2,-⟩:=Za.mp (Zc.mp h2);dsimp only at hlt1 hlt2;have hi1:i₁*d< j₁*d:=Nat.mul_lt_mul_of_pos_right hlt1 hd1;have hi2:i₂*d< j₂*d:=Nat.mul_lt_mul_of_pos_right hlt2 hd1
   have hm1:c+i₁*d∈({c+i₂*d,c+j₂*d}:Zf ℕ):=by rw[←heq];simp
   have hm2:c+j₁*d∈({c+i₂*d,c+j₂*d}:Zf ℕ):=by rw[←heq];simp
   simp only[Zx,Zj] at hm1 hm2
   ext <;> dsimp
   ·exact Nat.eq_of_mul_eq_mul_right hd1 (by omega)
   ·exact Nat.eq_of_mul_eq_mul_right hd1 (by omega)
  have heqR:E_R.card=(((Icc (0+1) (0+vMax)) ×ˢ (Icc (0+1) (0+vMax))).filter
    (fun z=>z.1< z.2/\Nat.gcd z.1 z.2=1)).card:=by
   rw[card_image_of_injOn hinjR];congr 1;ext ⟨x,y⟩;simp only[Za,Zh,Zb,Nat.zero_add,Nat.Coprime]
  rw[heqR];exact W5 Nd 0 vMax hNd1 (by omega)
 have hPd_le:Pd.card≤ Pd1.card+Pd0.card+Pd2.card:=by have h1:=(Zm hPd_sub).trans (Yh _ _);have h2:=Yh Pd1 Pd0;omega
 have hPd_R:(Pd.card:ℝ)≤(E_LR.card:ℝ)+(Pd0.card:ℝ)+(Pd2.card:ℝ):=by rw[hELR_eq];exact_mod_cast hPd_le
 have hPd0_R:(Pd0.card:ℝ)≤2*((Nd:ℝ)+1):=by exact_mod_cast hPd0_le
 have hNd_le:(Nd:ℝ)≤(N:ℝ)/(d:ℝ):=Nat.cast_div_le
 have hlog_Nd:log (Nd:ℝ)≤ log (N:ℝ) :=Real.log_le_log (by exact_mod_cast hNd1) (by exact_mod_cast Nat.div_le_self N d)
 have hlog_nn:0≤ log (N:ℝ):=Real.log_nonneg (by exact_mod_cast hN)
 have hNd1R:(1:ℝ)≤(Nd:ℝ):=by exact_mod_cast hNd1
 have hamgm:(44/100:ℝ)*(uMax:ℝ)*(vMax:ℝ) ≤(28/100:ℝ)*(uMax:ℝ)^2+(28/100:ℝ)*(vMax:ℝ)^2:=by nlinarith[sq_nonneg ((uMax:ℝ)-(vMax:ℝ))]
 nlinarith[Zo hNd_le (show (0:ℝ)≤ log (N:ℝ)+2 by linarith),Zp hlog_Nd (show (0:ℝ)≤(Nd:ℝ) by positivity)]
lemma Wx (N c:ℕ) (hN:1≤ N) (hc:c∈Icc 1 N)
  (P_c:Zf (Zf ℕ))
  (hPc_sub:∀ A∈P_c,A⊆Icc 1 N)
  (hPc:∀ A∈P_c,IsAP A/\2≤ A.card/\c∈A) :
  ∃ E_P:Zf (Zf ℕ),E_P⊆((Icc 1 N).erase c).powersetCard 2 ∧
   (∀ e∈E_P,∃ A∈P_c,e⊆A) ∧
   (∀ e∈E_P,∀ x y,e={x,y}->x≠y →
    ∃ A∈P_c,∃ a d k,2≤ k/\1≤ d/\(∀ z,z∈A↔∃ i< k,z=a+i*d) ∧
     Nat.gcd (max c x-min c x) (max c y-min c y)=d) ∧
   (P_c.card:ℝ)≤(E_P.card:ℝ)+200*(N:ℝ)*(log (N:ℝ)+2)^2:=by
 classical
 have hstep_ex:∀ A∈P_c,∃ d:ℕ,1≤ d/\d≤ N ∧
   ∃ x₀ k,2≤ k/\(∀ x,x∈A↔∃ i< k,x=x₀+i*d):=by
  intro A hA;obtain⟨⟨a,d,k,hk,hdk,hX⟩,h2,-⟩:=hPc A hA
  have hk2:2≤ k:=by rwa[Qo hk hdk hX] at h2
  have hd1:1≤ d:=hdk (by omega)
  have hsubA:A⊆Icc 1 N:=hPc_sub A hA;have hmm:=Wa hk hdk hX;have ha1:=(Zb.mp (hsubA hmm.1)).1;have hbN:=(Zb.mp (hsubA hmm.2.1)).2
  have hdN:d≤ N:=by
   have:d≤(k-1)*d:=Nat.le_mul_of_pos_left d (by omega);omega
  exact⟨d,hd1,hdN,a,k,hk2,hX⟩
 let step:Zf ℕ->ℕ:=fun A=>if hA:A∈P_c then (hstep_ex A hA).choose else 0
 have hstep:∀ A∈P_c,1≤ step A/\step A≤ N ∧
   ∃ x₀ k,2≤ k/\∀ x,x∈A↔∃ i< k,x=x₀+i*step A:=by
  intro A hA;simpa only [step,dif_pos hA] using (hstep_ex A hA).choose_spec
 have hspan_ex:∀ A∈P_c,∃ u v:ℕ,u*step A< c/\c+v*step A≤ N ∧
   (∀ x,x∈A↔(∃ i≤ u,x=c-i*step A)\/(∃ j≤ v,x=c+j*step A)):=by
  intro A hA;obtain⟨hd1,-,x₀,k,hk2,hX⟩:=hstep A hA;set d:=step A;have hsubA:A⊆Icc 1 N:=hPc_sub A hA;obtain⟨ic,hic,hic_eq⟩:=(hX c).mp (hPc A hA).2.2
  have hmin_ge1:1≤ x₀:=(Zb.mp (hsubA ((hX x₀).mpr ⟨0,by omega,by simp⟩))).1
  have hmax_leN:x₀+(k-1)*d≤ N:=(Zb.mp (hsubA ((hX _).mpr ⟨k-1,by omega,rfl⟩))).2
  refine⟨ic,k-1-ic,by omega,?_,fun x=>?_⟩
  ·have:ic*d+(k-1-ic)*d=(k-1)*d:=by rw[←Nat.add_mul];congr 1;omega
   omega
  ·rw[hX x];constructor
   ·rintro⟨i,hi,rfl⟩
    rcases le_total i ic with hle|hge
    ·left;refine⟨ic-i,by omega,?_⟩
     have:(ic-i)*d+i*d=ic*d:=by rw[←Nat.add_mul];congr 1;omega
     omega
    ·right;refine⟨i-ic,by omega,?_⟩
     have:ic*d+(i-ic)*d=i*d:=by rw[←Nat.add_mul];congr 1;omega
     omega
   ·rintro (⟨i,hi,rfl⟩|⟨j,hj,rfl⟩)
    ·refine⟨ic-i,by omega,?_⟩
     have:(ic-i)*d+i*d=ic*d:=by rw[←Nat.add_mul];congr 1;omega
     omega
    ·refine⟨ic+j,by omega,?_⟩
     rw[hic_eq,Nat.add_mul];omega
 let getU:Zf ℕ->ℕ:=fun A=>if hA:A∈P_c then (hspan_ex A hA).choose else 0
 let getV:Zf ℕ->ℕ:=fun A=>if hA:A∈P_c then (hspan_ex A hA).choose_spec.choose else 0
 have hgetUV:∀ A∈P_c,getU A*step A< c/\c+getV A*step A≤ N ∧
   (∀ x,x∈A↔(∃ i≤ getU A,x=c-i*step A)\/(∃ j≤ getV A,x=c+j*step A)):=by
  intro A hA;simpa only [getU,getV,dif_pos hA] using (hspan_ex A hA).choose_spec.choose_spec
 let Pd:ℕ->Zf (Zf ℕ):=fun d=>P_c.filter (fun A=>step A=d)
 let Pd1:ℕ->Zf (Zf ℕ):=fun d=>(Pd d).filter (fun A=>1≤ getU A/\1≤ getV A/\Nat.Coprime (getU A) (getV A))
 let E_LR:ℕ->Zf (Zf ℕ):=fun d=>(Pd1 d).image (fun A=>({c-getU A*d,c+getV A*d}:Zf ℕ))
 let uMax:ℕ->ℕ:=fun d=>((Pd d).image getU).max.unbotD 0
 let vMax:ℕ->ℕ:=fun d=>((Pd d).image getV).max.unbotD 0
 let E_L:ℕ->Zf (Zf ℕ):=fun d =>
  (((Icc 1 (uMax d)) ×ˢ (Icc 1 (uMax d))).filter (fun z=>z.1< z.2/\Nat.Coprime z.1 z.2)).image
   (fun z=>({c-z.1*d,c-z.2*d}:Zf ℕ))
 let E_R:ℕ->Zf (Zf ℕ):=fun d =>
  (((Icc 1 (vMax d)) ×ˢ (Icc 1 (vMax d))).filter (fun z=>z.1< z.2/\Nat.Coprime z.1 z.2)).image
   (fun z=>({c+z.1*d,c+z.2*d}:Zf ℕ))
 have huMax_ex:∀ d,1≤ uMax d->∃ A∈Pd d,getU A=uMax d:=by
  intro d hu
  rcases (Pd d).eq_empty_or_nonempty with hemp|hne
  ·exfalso;simp[uMax,hemp] at hu
  ·obtain⟨A,hA,hAmax⟩:=exists_max_image (Pd d) getU hne
   have hmax:((Pd d).image getU).max=(getU A:WithBot ℕ):=by
    refine le_antisymm ?_ (Finset.le_max (mem_image_of_mem getU hA))
    rw[Finset.max_le_iff];intro x hx;obtain⟨B,hB,rfl⟩:=Zi.mp hx;exact WithBot.coe_le_coe.mpr (hAmax B hB)
   exact⟨A,hA,by simp only[uMax,hmax];rfl⟩
 have hvMax_ex:∀ d,1≤ vMax d->∃ A∈Pd d,getV A=vMax d:=by
  intro d hv
  rcases (Pd d).eq_empty_or_nonempty with hemp|hne
  ·exfalso;simp[vMax,hemp] at hv
  ·obtain⟨A,hA,hAmax⟩:=exists_max_image (Pd d) getV hne
   have hmax:((Pd d).image getV).max=(getV A:WithBot ℕ):=by
    refine le_antisymm ?_ (Finset.le_max (mem_image_of_mem getV hA))
    rw[Finset.max_le_iff];intro x hx;obtain⟨B,hB,rfl⟩:=Zi.mp hx;exact WithBot.coe_le_coe.mpr (hAmax B hB)
   exact⟨A,hA,by simp only[vMax,hmax];rfl⟩
 have hELR_prop:∀ d∈Icc 1 N,∀ e∈E_LR d,e∈((Icc 1 N).erase c).powersetCard 2/\(∃ A∈Pd d,e⊆A) ∧
   ∃ x y,e={x,y}/\x< c/\c< y/\Nat.gcd (c-x) (y-c)=d:=by
  intro d hd e he;have hd1:=(Zb.mp hd).1;obtain⟨A,hA1,rfl⟩:=Zi.mp he;obtain⟨hAPd,hu1,hv1,hcop⟩:=Za.mp hA1;obtain⟨hAPc,hAd⟩:=Za.mp hAPd;obtain⟨huc,hvN,hAeq⟩:=hgetUV A hAPc;rw[hAd] at huc hvN hAeq
  have hlt1:c-getU A*d< c:=by have:=Nat.mul_pos hu1 hd1;omega
  have hlt2:c< c+getV A*d:=by have:=Nat.mul_pos hv1 hd1;omega
  have hsubA:({c-getU A*d,c+getV A*d}:Zf ℕ)⊆A:=by
   intro z hz;simp only[Zx,Zj] at hz
   rcases hz with rfl|rfl
   ·exact (hAeq _).mpr (Or.inl ⟨getU A,le_rfl,rfl⟩)
   ·exact (hAeq _).mpr (Or.inr ⟨getV A,le_rfl,rfl⟩)
  refine⟨Zz.mpr ⟨fun z hz=>Zw.mpr
   ⟨by simp only[Zx,Zj] at hz;rcases hz with rfl|rfl <;> omega,hPc_sub A hAPc (hsubA hz)⟩,
   by rw[card_insert_of_notMem (Finset.notMem_singleton.mpr (by omega)),card_singleton]⟩,
   ⟨A,hAPd,hsubA⟩,c-getU A*d,c+getV A*d,rfl,hlt1,hlt2,?_⟩
  have h1:c-(c-getU A*d)=getU A*d:=by omega
  have h2:c+getV A*d-c=getV A*d:=by omega
  rw[h1,h2,Nat.gcd_mul_right,hcop.gcd_eq_one,one_mul]
 have hEL_prop:∀ d∈Icc 1 N,∀ e∈E_L d,e∈((Icc 1 N).erase c).powersetCard 2/\(∃ A∈Pd d,e⊆A) ∧
   ∃ x y,e={x,y}/\x< c/\y< c/\x≠y/\Nat.gcd (c-x) (c-y)=d:=by
  intro d hd e he;have hd1:=(Zb.mp hd).1;obtain⟨⟨i,j⟩,hij,rfl⟩:=Zi.mp he;obtain⟨hijP,hiltj,hcop⟩:=Za.mp hij;dsimp only at hiltj hcop ⊢;obtain⟨hi,hj⟩:=Zh.mp hijP;dsimp only at hi hj;have hi1:=(Zb.mp hi).1;have hj_le:=(Zb.mp hj).2;have hi_le:=(Zb.mp hi).2
  obtain⟨A,hAPd,hAu⟩:=huMax_ex d (by omega)
  obtain⟨hAPc,hAd⟩:=Za.mp hAPd;obtain⟨huc,-,hAeq⟩:=hgetUV A hAPc;rw[hAd,hAu] at huc hAeq;have hi_lt:i*d< c:=lt_of_le_of_lt (Yc d hi_le) huc;have hj_lt:j*d< c:=lt_of_le_of_lt (Yc d hj_le) huc
  have hlt1:c-i*d< c:=by have:=Nat.mul_pos hi1 hd1;omega
  have hlt2:c-j*d< c:=by have:=Nat.mul_pos (by omega:0< j) hd1;omega
  have hne:c-i*d≠c-j*d:=by
   have:=Nat.mul_lt_mul_of_pos_right hiltj hd1;omega
  have hsubA:({c-i*d,c-j*d}:Zf ℕ)⊆A:=by
   intro z hz;simp only[Zx,Zj] at hz
   rcases hz with rfl|rfl
   ·exact (hAeq _).mpr (Or.inl ⟨i,hi_le,rfl⟩)
   ·exact (hAeq _).mpr (Or.inl ⟨j,hj_le,rfl⟩)
  refine⟨Zz.mpr ⟨fun z hz=>Zw.mpr
   ⟨by simp only[Zx,Zj] at hz;rcases hz with rfl|rfl <;> omega,hPc_sub A hAPc (hsubA hz)⟩,
   by rw[card_insert_of_notMem (Finset.notMem_singleton.mpr hne),card_singleton]⟩,
   ⟨A,hAPd,hsubA⟩,c-i*d,c-j*d,rfl,hlt1,hlt2,hne,?_⟩
  have h1:c-(c-i*d)=i*d:=by omega
  have h2:c-(c-j*d)=j*d:=by omega
  rw[h1,h2,Nat.gcd_mul_right,hcop.gcd_eq_one,one_mul]
 have hER_prop:∀ d∈Icc 1 N,∀ e∈E_R d,e∈((Icc 1 N).erase c).powersetCard 2/\(∃ A∈Pd d,e⊆A) ∧
   ∃ x y,e={x,y}/\c< x/\c< y/\x≠y/\Nat.gcd (x-c) (y-c)=d:=by
  intro d hd e he;have hd1:=(Zb.mp hd).1;obtain⟨⟨i,j⟩,hij,rfl⟩:=Zi.mp he;obtain⟨hijP,hiltj,hcop⟩:=Za.mp hij;dsimp only at hiltj hcop ⊢;obtain⟨hi,hj⟩:=Zh.mp hijP;dsimp only at hi hj;have hi1:=(Zb.mp hi).1;have hj_le:=(Zb.mp hj).2;have hi_le:=(Zb.mp hi).2
  obtain⟨A,hAPd,hAv⟩:=hvMax_ex d (by omega)
  obtain⟨hAPc,hAd⟩:=Za.mp hAPd;obtain⟨-,hvN,hAeq⟩:=hgetUV A hAPc;rw[hAd,hAv] at hvN hAeq
  have hlt1:c< c+i*d:=by have:=Nat.mul_pos hi1 hd1;omega
  have hlt2:c< c+j*d:=by have:=Nat.mul_pos (by omega:0< j) hd1;omega
  have hne:c+i*d≠c+j*d:=by
   have:=Nat.mul_lt_mul_of_pos_right hiltj hd1;omega
  have hsubA:({c+i*d,c+j*d}:Zf ℕ)⊆A:=by
   intro z hz;simp only[Zx,Zj] at hz
   rcases hz with rfl|rfl
   ·exact (hAeq _).mpr (Or.inr ⟨i,hi_le,rfl⟩)
   ·exact (hAeq _).mpr (Or.inr ⟨j,hj_le,rfl⟩)
  refine⟨Zz.mpr ⟨fun z hz=>Zw.mpr
   ⟨by simp only[Zx,Zj] at hz;rcases hz with rfl|rfl <;> omega,hPc_sub A hAPc (hsubA hz)⟩,
   by rw[card_insert_of_notMem (Finset.notMem_singleton.mpr hne),card_singleton]⟩,
   ⟨A,hAPd,hsubA⟩,c+i*d,c+j*d,rfl,hlt1,hlt2,hne,?_⟩
  have h1:c+i*d-c=i*d:=by omega
  have h2:c+j*d-c=j*d:=by omega
  rw[h1,h2,Nat.gcd_mul_right,hcop.gcd_eq_one,one_mul]
 let Ed:ℕ->Zf (Zf ℕ):=fun d=>E_LR d∪E_L d∪E_R d
 have hgcd_Ed:∀ d∈Icc 1 N,∀ e∈Ed d,∀ x y,e={x,y}->x≠y->Nat.gcd (max c x-min c x) (max c y-min c y)=d:=by
  intro d hd e he x y hxy hnexy
  rcases Zd.mp he with h12|h3
  ·rcases Zd.mp h12 with h1|h2
   ·obtain⟨-,-,a,b,heq,ha,hb,hg⟩:=hELR_prop d hd e h1
    have hax:a∈({x,y}:Zf ℕ):=by rw[←hxy,heq];simp
    have hbx:b∈({x,y}:Zf ℕ):=by rw[←hxy,heq];simp
    simp only[Zx,Zj] at hax hbx
    rcases hax with rfl|rfl <;> rcases hbx with rfl|rfl
    ·omega
    ·rw[Yk ha.le,Yj ha.le,Yi hb.le,Yl hb.le];exact hg
    ·rw[Yi hb.le,Yl hb.le,Yk ha.le,Yj ha.le,Nat.gcd_comm];exact hg
    ·omega
   ·obtain⟨-,-,a,b,heq,ha,hb,hnab,hg⟩:=hEL_prop d hd e h2
    have hax:a∈({x,y}:Zf ℕ):=by rw[←hxy,heq];simp
    have hbx:b∈({x,y}:Zf ℕ):=by rw[←hxy,heq];simp
    simp only[Zx,Zj] at hax hbx
    rcases hax with rfl|rfl <;> rcases hbx with rfl|rfl
    ·exact absurd rfl hnab
    ·rw[Yk ha.le,Yj ha.le,Yk hb.le,Yj hb.le];exact hg
    ·rw[Yk hb.le,Yj hb.le,Yk ha.le,Yj ha.le,Nat.gcd_comm];exact hg
    ·exact absurd rfl hnab
  ·obtain⟨-,-,a,b,heq,ha,hb,hnab,hg⟩:=hER_prop d hd e h3
   have hax:a∈({x,y}:Zf ℕ):=by rw[←hxy,heq];simp
   have hbx:b∈({x,y}:Zf ℕ):=by rw[←hxy,heq];simp
   simp only[Zx,Zj] at hax hbx
   rcases hax with rfl|rfl <;> rcases hbx with rfl|rfl
   ·exact absurd rfl hnab
   ·rw[Yi ha.le,Yl ha.le,Yi hb.le,Yl hb.le];exact hg
   ·rw[Yi hb.le,Yl hb.le,Yi ha.le,Yl ha.le,Nat.gcd_comm];exact hg
   ·exact absurd rfl hnab
 have hEd_card:∀ d∈Icc 1 N,(Ed d).card=(E_LR d).card+(E_L d).card+(E_R d).card:=by
  intro d hd
  have h12:Disjoint (E_LR d) (E_L d):=by
   rw[Zk];intro e h1 h2;obtain⟨-,-,x₁,y₁,he1,hx1,hy1,-⟩:=hELR_prop d hd e h1;obtain⟨-,-,x₂,y₂,he2,hx2,hy2,-⟩:=hEL_prop d hd e h2
   have:y₁∈({x₂,y₂}:Zf ℕ):=by rw[←he2,he1];simp
   simp only[Zx,Zj] at this;omega
  have h123:Disjoint (E_LR d∪E_L d) (E_R d):=by
   rw[Zk];intro e h12' h3;obtain⟨-,-,x₃,y₃,he3,hx3,hy3,-⟩:=hER_prop d hd e h3
   rcases Zd.mp h12' with h1|h2
   ·obtain⟨-,-,x₁,y₁,he1,hx1,-,-⟩:=hELR_prop d hd e h1
    have:x₁∈({x₃,y₃}:Zf ℕ):=by rw[←he3,he1];simp
    simp only[Zx,Zj] at this;omega
   ·obtain⟨-,-,x₂,y₂,he2,hx2,-,-⟩:=hEL_prop d hd e h2
    have:x₂∈({x₃,y₃}:Zf ℕ):=by rw[←he3,he2];simp
    simp only[Zx,Zj] at this;omega
  rw[Zq h123,Zq h12]
 have hEd_disj:Set.PairwiseDisjoint ((Icc 1 N):Set ℕ) Ed:=by
  intro d₁ hd₁ d₂ hd₂ hne;simp only[Function.onFun];rw[Zk];intro e he1 he2
  have he_mem:e∈((Icc 1 N).erase c).powersetCard 2:=by
   rcases Zd.mp he1 with h12|h3
   ·rcases Zd.mp h12 with h1|h2
    ·exact (hELR_prop d₁ (Zc.mp hd₁) e h1).1
    ·exact (hEL_prop d₁ (Zc.mp hd₁) e h2).1
   ·exact (hER_prop d₁ (Zc.mp hd₁) e h3).1
  obtain⟨x,y,hnexy,hxy⟩:=card_eq_two.mp (Zz.mp he_mem).2
  exact hne ((hgcd_Ed d₁ (Zc.mp hd₁) e he1 x y hxy hnexy).symm.trans
   (hgcd_Ed d₂ (Zc.mp hd₂) e he2 x y hxy hnexy))
 refine⟨(Icc 1 N).biUnion Ed,?_,?_,?_,?_⟩
 ·exact biUnion_subset.mpr fun d hd e he=>by
   rcases Zd.mp he with h12|h3
   ·rcases Zd.mp h12 with h1|h2
    ·exact (hELR_prop d hd e h1).1
    ·exact (hEL_prop d hd e h2).1
   ·exact (hER_prop d hd e h3).1
 ·intro e he
  obtain⟨d,hd,heEd⟩:=mem_biUnion.mp he
  have hexA:∃ A∈Pd d,e⊆A:=by
   rcases Zd.mp heEd with h12|h3
   ·rcases Zd.mp h12 with h1|h2
    ·exact (hELR_prop d hd e h1).2.1
    ·exact (hEL_prop d hd e h2).2.1
   ·exact (hER_prop d hd e h3).2.1
  obtain⟨A,hAPd,hsub⟩:=hexA;exact⟨A,(Za.mp hAPd).1,hsub⟩
 ·intro e he x y hxy hnexy
  obtain⟨d,hd,heEd⟩:=mem_biUnion.mp he
  have hexA:∃ A∈Pd d,e⊆A:=by
   rcases Zd.mp heEd with h12|h3
   ·rcases Zd.mp h12 with h1|h2
    ·exact (hELR_prop d hd e h1).2.1
    ·exact (hEL_prop d hd e h2).2.1
   ·exact (hER_prop d hd e h3).2.1
  obtain⟨A,hAPd,-⟩:=hexA;obtain⟨hAPc,hAd⟩:=Za.mp hAPd;obtain⟨hd1,-,x₀,k,hk2,hX⟩:=hstep A hAPc;rw[hAd] at hd1 hX;exact⟨A,hAPc,x₀,d,k,hk2,hd1,hX,hgcd_Ed d hd e heEd x y hxy hnexy⟩
 ·have hPc_part:P_c.card=∑ d∈Icc 1 N,(Pd d).card:=by
   rw[←card_biUnion]
   ·congr 1;ext A;simp only[Pd,mem_biUnion,Zb,Za]
    constructor
    ·intro hA;obtain⟨h1,h2,-⟩:=hstep A hA;exact⟨step A,⟨h1,h2⟩,hA,rfl⟩
    ·rintro⟨_,_,hA,_⟩;exact hA
   ·intro d₁ _ d₂ _ hne;simp only[Function.onFun];rw[Zk]
    intro A h1 h2;exact hne ((Za.mp h1).2.symm.trans (Za.mp h2).2)
  have hEP_card:((Icc 1 N).biUnion Ed).card =∑ d∈Icc 1 N,((E_LR d).card+(E_L d).card+(E_R d).card):=by rw[card_biUnion hEd_disj,Finset.sum_congr rfl hEd_card]
  have hper_d:∀ d∈Icc 1 N,((Pd d).card:ℝ)≤((E_LR d).card:ℝ)+((E_L d).card:ℝ)+((E_R d).card:ℝ) +110*((N:ℝ)/(d:ℝ))*(log (N:ℝ)+2):=by
   intro d hd
   exact Vk N c d hN hc hd (Pd d) getU getV fun A hA=>by
    obtain⟨hAPc,hAd⟩:=Za.mp hA
    have:=hgetUV A hAPc;rwa[hAd] at this
  have h1:(P_c.card:ℝ)=∑ d∈Icc 1 N,((Pd d).card:ℝ):=by exact_mod_cast hPc_part
  have hEP_R:(((Icc 1 N).biUnion Ed).card:ℝ) =∑ d∈Icc 1 N,(((E_LR d).card:ℝ)+((E_L d).card:ℝ)+((E_R d).card:ℝ)):=by exact_mod_cast hEP_card
  have h2:∑ d∈Icc 1 N,((Pd d).card:ℝ) ≤(∑ d∈Icc 1 N,(((E_LR d).card:ℝ)+((E_L d).card:ℝ)+((E_R d).card:ℝ))) +∑ d∈Icc 1 N,(110*((N:ℝ)/(d:ℝ))*(log (N:ℝ)+2)):=by
   rw[←Finset.sum_add_distrib]
   exact Finset.sum_le_sum fun d hd=>by linarith[hper_d d hd]
  have h3:∑ d∈Icc 1 N,(110*((N:ℝ)/(d:ℝ))*(log (N:ℝ)+2)) =110*(N:ℝ)*(log (N:ℝ)+2)*∑ d∈Icc 1 N,(1:ℝ)/(d:ℝ):=by
   rw[Finset.mul_sum];refine Finset.sum_congr rfl fun d _=>?_;ring
  have hlog_nn:0≤ log (N:ℝ):=Real.log_nonneg (by exact_mod_cast hN)
  have h4:=Zp (Q0 N hN)
   (show (0:ℝ)≤110*(N:ℝ)*(log (N:ℝ)+2) by positivity)
  nlinarith
lemma Vj (N c:ℕ) (hN:1≤ N) (hc:c∈Icc 1 N)
  (P_c Q_c:Zf (Zf ℕ))
  (hF:Zt N (P_c∪Q_c))
  (hdisj:Disjoint P_c Q_c)
  (hPc:∀ A∈P_c,IsAP A/\2≤ A.card/\c∈A)
  (hQc:∀ S∈Q_c,¬ IsAP S/\c∈S) :
  (Q_c.card:ℝ)+(P_c.card:ℝ)≤(N:ℝ)^2/2+200*(N:ℝ)*(log (N:ℝ)+2)^2:=by
 classical
 have hQ_ex:∀ S∈Q_c,∃ e∈Qs c S,True:=by
  intro S hS;obtain⟨x,y,hxS,hyS,hxc,hyc,hxy,hbad⟩:=Vs (hQc S hS).2 (hQc S hS).1
  refine⟨{x,y},(Wm c S {x,y}).mpr ⟨by simp[hxc.symm,hyc.symm],?_,hbad⟩,trivial⟩
  rw[card_insert_of_notMem (Finset.notMem_singleton.mpr hxy),card_singleton]
 let eQ:Zf ℕ->Zf ℕ:=fun S=>if hS:S∈Q_c then (hQ_ex S hS).choose else ∅
 have heQ:∀ S∈Q_c,eQ S∈Qs c S:=by
  intro S hS;exact ((by simpa only [eQ,dif_pos hS] using (hQ_ex S hS).choose_spec):_/\True).1
 set Eq:=Q_c.image eQ
 have hEq_card:Eq.card=Q_c.card:=by
  refine card_image_of_injOn fun S hS T hT heq=>?_
  by_contra hST;have hS':=Zc.mp hS;have hT':=Zc.mp hT;have hdisj_bp:=W6 hF (Zg _ hS') (Zg _ hT') hST (hQc T hT').2;exact Zk.mp hdisj_bp (heQ S hS') (heq ▸ heQ T hT')
 have hEq_sub:Eq⊆((Icc 1 N).erase c).powersetCard 2:=by intro e he;obtain⟨S,hS,rfl⟩:=Zi.mp he;exact Wd (Zy.mp (hF.1 (Zg _ hS))) (heQ S hS)
 obtain⟨E_P,hEP_sub,hEP_ap,-,hPc_bd⟩:=Wx N c hN hc P_c
  (fun A hA=>Zy.mp (hF.1 (Ze _ hA))) hPc
 have hEq_disj_EP:Disjoint Eq E_P:=by
  rw[Zk];intro e heQ' heEP;obtain⟨S,hSQ,rfl⟩:=Zi.mp heQ';obtain⟨A,hAPc,hsubA⟩:=hEP_ap _ heEP
  have hSA:S≠A:=fun h=>Zk.mp hdisj hAPc (h ▸ hSQ)
  exact Qt hF (Zg _ hSQ) (Ze _ hAPc)
   hSA (hPc A hAPc).2.2 (heQ S hSQ) hsubA
 have hpack:Q_c.card+E_P.card≤(N-1).choose 2:=by
  calc Q_c.card+E_P.card=Eq.card+E_P.card:=by rw[hEq_card]
    _=(Eq∪E_P).card:=(Zq hEq_disj_EP).symm
    _≤(((Icc 1 N).erase c).powersetCard 2).card:=Zm (Zu hEq_sub hEP_sub)
    _=(N-1).choose 2:=by rw[card_powersetCard,card_erase_of_mem hc,Nat.card_Icc];simp
 have hpackR:(Q_c.card:ℝ)+(E_P.card:ℝ)≤(N:ℝ)^2/2:=by
  have h1:(Q_c.card:ℝ)+(E_P.card:ℝ)≤(((N-1).choose 2:ℕ):ℝ):=by exact_mod_cast hpack
  have h2:2*(N-1).choose 2≤ N^2:=by
   rw[Nat.choose_two_right,Nat.mul_div_cancel' (Nat.even_mul_pred_self (N-1)).two_dvd]
   calc (N-1)*(N-1-1)≤ N*N:=Nat.mul_le_mul (Nat.sub_le N 1) (by omega)
     _=N^2:=by ring
  have h2R:2*(((N-1).choose 2:ℕ):ℝ)≤(N:ℝ)^2:=by exact_mod_cast h2
  linarith
 linarith
def apStep (A:Zf ℕ):ℕ :=if h:A.Nonempty then (A.max' h-A.min' h)/(A.card-1) else 0
lemma Kf {A:Zf ℕ} {a d k:ℕ} (hk:2≤ k) (hd:1≤ d)
  (hX:∀ x,x∈A↔∃ i< k,x=a+i*d):apStep A=d:=by
 have hk1:1≤ k:=by omega
 have hne:A.Nonempty:=⟨a,(hX a).mpr ⟨0,by omega,by simp⟩⟩
 have hcard:A.card=k:=Qo hk1 (fun _=>hd) hX
 have hmm:=Wa hk1 (fun _=>hd) hX
 have hmin:A.min' hne=a:=le_antisymm (min'_le A a hmm.1)
  (le_min' A hne a (fun x hx=>(hmm.2.2 x hx).1))
 have hmax:A.max' hne=a+(k-1)*d:=le_antisymm
  (max'_le A hne _ (fun x hx=>(hmm.2.2 x hx).2))
  (le_max' A _ hmm.2.1)
 unfold apStep;rw[dif_pos hne,hmin,hmax,hcard]
 have hsub:a+(k-1)*d-a=(k-1)*d:=by omega
 rw[hsub,Nat.mul_div_cancel_left d (by omega:0< k-1)]
lemma Qg {N:ℕ} {A:Zf ℕ} (hsub:A⊆Icc 1 N) (hAP:IsAP A) (h2:2≤ A.card) :1≤ apStep A/\apStep A≤ N ∧
  ∃ a k,2≤ k/\A.card=k/\(∀ x,x∈A↔∃ i< k,x=a+i*apStep A):=by
 obtain⟨a,d,k,hk,hdk,hX⟩:=hAP;have hcard:A.card=k:=Qo hk hdk hX
 have hk2:2≤ k:=by omega
 have hd1:1≤ d:=hdk (by omega)
 have hst:apStep A=d:=Kf hk2 hd1 hX;have hmm:=Wa hk hdk hX;have ha1:=(Zb.mp (hsub hmm.1)).1;have hbN:=(Zb.mp (hsub hmm.2.1)).2
 have hdN:d≤ N:=by
  have:d≤(k-1)*d:=Nat.le_mul_of_pos_left d (by omega);omega
 rw[hst];exact⟨hd1,hdN,a,k,hk2,hcard,hX⟩
lemma W0 {N c:ℕ} {A:Zf ℕ} (hsub:A⊆Icc 1 N)
  (hAP:IsAP A) (h2:2≤ A.card) (hcA:c∈A) :
  ∃ u v:ℕ,u*apStep A< c/\c+v*apStep A≤ N ∧
   (∀ x,x∈A↔(∃ i≤ u,x=c-i*apStep A)\/(∃ j≤ v,x=c+j*apStep A)):=by
 obtain⟨hd1,-,x₀,k,hk2,-,hX⟩:=Qg hsub hAP h2;set d:=apStep A;obtain⟨ic,hic,hic_eq⟩:=(hX c).mp hcA
 have hmin_ge1:1≤ x₀:=(Zb.mp (hsub ((hX x₀).mpr ⟨0,by omega,by simp⟩))).1
 have hmax_leN:x₀+(k-1)*d≤ N:=(Zb.mp (hsub ((hX _).mpr ⟨k-1,by omega,rfl⟩))).2
 refine⟨ic,k-1-ic,by omega,?_,fun x=>?_⟩
 ·have:ic*d+(k-1-ic)*d=(k-1)*d:=by rw[←Nat.add_mul];congr 1;omega
  omega
 ·rw[hX x];constructor
  ·rintro⟨i,hi,rfl⟩
   rcases le_total i ic with hle|hge
   ·left;refine⟨ic-i,by omega,?_⟩
    have:(ic-i)*d+i*d=ic*d:=by rw[←Nat.add_mul];congr 1;omega
    omega
   ·right;refine⟨i-ic,by omega,?_⟩
    have:ic*d+(i-ic)*d=i*d:=by rw[←Nat.add_mul];congr 1;omega
    omega
  ·rintro (⟨i,hi,rfl⟩|⟨j,hj,rfl⟩)
   ·refine⟨ic-i,by omega,?_⟩
    have:(ic-i)*d+i*d=ic*d:=by rw[←Nat.add_mul];congr 1;omega
    omega
   ·refine⟨ic+j,by omega,?_⟩
    rw[hic_eq,Nat.add_mul];omega
lemma Wv (N c q:ℕ) (hN:1≤ N) (hc:c∈Icc 1 N) (hq:2≤ q)
  (P_c Q_c:Zf (Zf ℕ)) (B:Zf ℕ)
  (hF:Zt N (P_c∪Q_c))
  (hdisj:Disjoint P_c Q_c)
  (hPc:∀ A∈P_c,IsAP A/\2≤ A.card/\c∈A)
  (hQc:∀ S∈Q_c,¬ IsAP S/\c∈S)
  (hB_sub:B⊆(Icc 1 N).erase c)
  (hB_mod:∀ x∈B,x % q≠c % q)
  (hPc_hit:∀ A∈P_c,(A∩B).Nonempty)
  (hQc_hit:∀ S∈Q_c,(S∩B).Nonempty) :
  (Q_c.card:ℝ)+(P_c.card:ℝ) ≤(1/2-1/(2*(q:ℝ)^2))*(N:ℝ)^2 +210*(N:ℝ)*(log (N:ℝ)+2)^2 +8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5):=by
 classical
 have hQ_sub:Zt N Q_c :=⟨(Zs (s₁:=P_c)).trans hF.1,fun S hS T hT hST =>
   hF.2 (Zc.mpr (Zg _ (Zc.mp hS)))
    (Zc.mpr (Zg _ (Zc.mp hT))) hST⟩
 set H:=Qa c B Q_c
 have hch:∀ S∈H,∃ e∈Qs c S,(e∩B).Nonempty:=fun S hS =>
  ((Qp c B Q_c S).mp hS).2
 let pick:Zf ℕ->Zf ℕ:=fun S=>if hS:S∈H then (hch S hS).choose else ∅
 have hpick:∀ S∈H,pick S∈Qs c S/\(pick S∩B).Nonempty:=by intro S hS;simpa only [pick,dif_pos hS] using (hch S hS).choose_spec
 set EH:=H.image pick
 have hEH_card:EH.card=H.card:=by
  refine card_image_of_injOn fun S hS T hT heq=>?_
  by_contra hST;have hSQ:=((Qp c B Q_c S).mp (Zc.mp hS)).1;have hTQ:=((Qp c B Q_c T).mp (Zc.mp hT)).1;have hd:=W6 hF (Zg _ hSQ) (Zg _ hTQ) hST (hQc T hTQ).2;exact Zk.mp hd (hpick S (Zc.mp hS)).1 (heq ▸ (hpick T (Zc.mp hT)).1)
 have hEH_sub:EH⊆((Icc 1 N).erase c).powersetCard 2:=by intro e he;obtain⟨S,hS,rfl⟩:=Zi.mp he;have hSQ:=((Qp c B Q_c S).mp hS).1;exact Wd (Zy.mp (hF.1 (Zg _ hSQ))) (hpick S hS).1
 obtain⟨E_P,hEP_sub,hEP_ap,hEP_gcd,hPc_bd⟩:=Wx N c hN hc P_c
  (fun A hA=>Zy.mp (hF.1 (Ze _ hA))) hPc
 have hEH_disj_EP:Disjoint EH E_P:=by
  rw[Zk];intro e heH heP;obtain⟨S,hS,rfl⟩:=Zi.mp heH;have hSQ:=((Qp c B Q_c S).mp hS).1;obtain⟨A,hAPc,hsubA⟩:=hEP_ap _ heP
  have hSA:S≠A:=fun h=>Zk.mp hdisj hAPc (h ▸ hSQ)
  exact Qt hF (Zg _ hSQ) (Ze _ hAPc)
   hSA (hPc A hAPc).2.2 (hpick S hS).1 hsubA
 set Mq:=((Icc 1 N).erase c).filter (fun x=>x % q=c % q)
 have hMq_sub:Mq.powersetCard 2⊆((Icc 1 N).erase c).powersetCard 2 :=powersetCard_mono (Zl _ _)
 have hdisj_Mq:Disjoint (EH∪E_P) (Mq.powersetCard 2):=by
  rw[Zk];intro e heU heM;have heMsub:=(Zz.mp heM).1
  rcases Zd.mp heU with heH|heP
  ·obtain⟨S,hS,rfl⟩:=Zi.mp heH
   obtain⟨b,hb⟩:=(hpick S hS).2;obtain⟨hbe,hbB⟩:=Zn.mp hb;exact hB_mod b hbB (Za.mp (heMsub hbe)).2
  ·obtain⟨x,y,hxy_ne,hxy⟩:=card_eq_two.mp (Zz.mp heM).2
   obtain⟨A,hAPc,a,d,k,hk2,hd1,hAeq,hgcd⟩:=hEP_gcd e heP x y hxy hxy_ne
   have hxM:x % q=c % q:=(Za.mp (heMsub (by rw[hxy];simp))).2
   have hyM:y % q=c % q:=(Za.mp (heMsub (by rw[hxy];simp))).2
   have hqx:q ∣ max c x-min c x:=by
    rcases le_total c x with hle|hge
    ·rw[Yi hle,Yl hle];exact (Nat.modEq_iff_dvd' hle).mp hxM.symm
    ·rw[Yk hge,Yj hge];exact (Nat.modEq_iff_dvd' hge).mp hxM
   have hqy:q ∣ max c y-min c y:=by
    rcases le_total c y with hle|hge
    ·rw[Yi hle,Yl hle];exact (Nat.modEq_iff_dvd' hle).mp hyM.symm
    ·rw[Yk hge,Yj hge];exact (Nat.modEq_iff_dvd' hge).mp hyM
   have hqd:q ∣ d:=hgcd ▸ Nat.dvd_gcd hqx hqy;obtain⟨b,hb⟩:=hPc_hit A hAPc;obtain⟨hbA,hbB⟩:=Zn.mp hb;obtain⟨ic,-,hic_eq⟩:=(hAeq c).mp (hPc A hAPc).2.2;obtain⟨ib,-,hib_eq⟩:=(hAeq b).mp hbA;obtain⟨m,rfl⟩:=hqd
   have hmod:b % q=c % q:=by
    rw[hib_eq,hic_eq]
    have h1:(a+ib*(q*m)) % q=a % q:=by
     rw[show ib*(q*m)=q*(ib*m) by ring,Nat.add_mul_mod_self_left]
    have h2:(a+ic*(q*m)) % q=a % q:=by
     rw[show ic*(q*m)=q*(ic*m) by ring,Nat.add_mul_mod_self_left]
    exact h1.trans h2.symm
   exact hB_mod b hbB hmod
 have hpack:H.card+E_P.card+Mq.card.choose 2≤(N-1).choose 2:=by
  calc H.card+E_P.card+Mq.card.choose 2
      = (EH∪E_P).card+(Mq.powersetCard 2).card:=by rw[Zq hEH_disj_EP,hEH_card,card_powersetCard]
    _=((EH∪E_P)∪Mq.powersetCard 2).card:=(Zq hdisj_Mq).symm
    _≤(((Icc 1 N).erase c).powersetCard 2).card :=
        Zm (Zu (Zu hEH_sub hEP_sub) hMq_sub)
    _=(N-1).choose 2:=by rw[card_powersetCard,card_erase_of_mem hc,Nat.card_Icc];simp
 have hMq_lb:N/q≤ Mq.card+2:=by
  set r:=if c % q=0 then q else c % q
  have hr1:1≤ r:=by dsimp only[r];split_ifs <;> omega
  have hrq:r≤ q:=by dsimp only[r];split_ifs;exact le_rfl;exact le_of_lt (Nat.mod_lt c (by omega))
  have hrmod:r % q=c % q:=by dsimp only[r];split_ifs with h0;simp[h0];exact Nat.mod_mod c q
  let S0:=(Icc 1 N).filter (fun x=>x % q=c % q)
  have hS0_ge:N/q-1≤ S0.card:=by
   let f:ℕ->ℕ:=fun i=>i*q+r
   have hmaps:Set.MapsTo f (range (N/q-1):Set ℕ) (S0:Set ℕ):=by
    intro i hi;dsimp only[f];have hilt:i< N/q-1:=mem_range.mp (Zc.mp hi)
    refine Zc.mpr (Za.mpr ⟨Zb.mpr ⟨by omega,?_⟩,?_⟩)
    ·have h1:(i+1)*q≤(N/q)*q:=Yc q (by omega)
     have h2:(N/q)*q≤ N:=Nat.div_mul_le_self N q
     have h3:(i+1)*q=i*q+q:=by ring
     omega
    ·rw[Nat.mul_comm,Nat.mul_add_mod,hrmod]
   have hinj:Set.InjOn f (range (N/q-1):Set ℕ):=by
    intro i _ j _ heq;dsimp only[f] at heq
    exact Nat.eq_of_mul_eq_mul_right (by omega:0< q) (by omega)
   exact (by rw[card_range]:N/q-1=(range (N/q-1)).card).trans_le
    (card_le_card_of_injOn f hmaps hinj)
  have hS0_le:S0.card≤ Mq.card+1:=by
   have hsub:S0⊆insert c Mq:=by
    intro x hx
    by_cases hxc:x=c
    ·exact hxc ▸ mem_insert_self c Mq
    ·obtain⟨hxI,hxmod⟩:=Za.mp hx
     exact mem_insert_of_mem (Za.mpr ⟨Zw.mpr ⟨hxc,hxI⟩,hxmod⟩)
   exact (Zm hsub).trans (card_insert_le c Mq)
  omega
 have hMq_ch:(N:ℝ)^2/(2*(q:ℝ)^2)-4*(N:ℝ)≤((Mq.card.choose 2:ℕ):ℝ):=by
  have hqpos:(0:ℝ)<(q:ℝ):=by exact_mod_cast (by omega:0< q)
  have hq2:(2:ℝ)≤(q:ℝ):=by exact_mod_cast hq
  by_cases hbig:4≤ N/q
  ·have hMq2:2≤ Mq.card:=by omega
   have hch2:2*Mq.card.choose 2=Mq.card*(Mq.card-1):=by rw[Nat.choose_two_right,Nat.mul_div_cancel' (Nat.even_mul_pred_self Mq.card).two_dvd]
   have hchR:2*((Mq.card.choose 2:ℕ):ℝ)=(Mq.card:ℝ)*((Mq.card:ℝ)-1):=by
    have h1:(2*Mq.card.choose 2:ℝ)=((Mq.card*(Mq.card-1):ℕ):ℝ):=by exact_mod_cast hch2
    rw[Nat.cast_mul,Nat.cast_sub (by omega:1≤ Mq.card),Nat.cast_one] at h1;exact h1
   have hdiv_lb:(N:ℝ)/(q:ℝ)-1≤((N/q:ℕ):ℝ):=by
    have h1:N<(N/q+1)*q:=by rw[mul_comm];exact Nat.lt_mul_div_succ N (by omega)
    have h1R:(N:ℝ)≤(((N/q:ℕ):ℝ)+1)*(q:ℝ):=by exact_mod_cast le_of_lt h1
    have:=(div_le_iff₀ hqpos).mpr h1R;linarith
   have hMq_R:(N:ℝ)/(q:ℝ)-3≤(Mq.card:ℝ):=by
    have:((N/q:ℕ):ℝ)≤(Mq.card:ℝ)+2:=by exact_mod_cast hMq_lb
    linarith
   have hNq4:(4:ℝ)≤(N:ℝ)/(q:ℝ):=by
    have h1:(4:ℝ)≤((N/q:ℕ):ℝ):=by exact_mod_cast hbig
    linarith[Nat.cast_div_le (m:=N) (n:=q) (α:=ℝ)]
   have hNq_le_N:(N:ℝ)/(q:ℝ)≤(N:ℝ):=div_le_self (Nat.cast_nonneg N) (by linarith)
   have hsq_eq:((N:ℝ)/(q:ℝ))^2=(N:ℝ)^2/(q:ℝ)^2:=div_pow _ _ 2
   have h2eq:(N:ℝ)^2/(2*(q:ℝ)^2)=((N:ℝ)/(q:ℝ))^2/2:=by rw[hsq_eq];ring
   rw[h2eq];nlinarith
  ·have hNq_lt:(N:ℝ)/(q:ℝ)≤4:=by
    have h1:N<4*q:=by
     have:N/q<4:=by omega
     have:=Nat.lt_mul_div_succ N (by omega:0< q)
     have h2:q*(N/q+1)≤ q*4:=Yd q (by omega)
     omega
    have h1R:(N:ℝ)≤4*(q:ℝ):=by exact_mod_cast le_of_lt h1
    exact (div_le_iff₀ hqpos).mpr h1R
   have hsq_le:(N:ℝ)^2/(2*(q:ℝ)^2)≤4*(N:ℝ):=by
    have h1:(N:ℝ)/(q:ℝ)≤(N:ℝ):=div_le_self (Nat.cast_nonneg N) (by linarith)
    have h2:(N:ℝ)^2/(2*(q:ℝ)^2)=((N:ℝ)/(q:ℝ))*((N:ℝ)/(q:ℝ))/2:=by ring
    rw[h2];nlinarith[div_nonneg (Nat.cast_nonneg (α:=ℝ) N) hqpos.le]
   have hnn:(0:ℝ)≤((Mq.card.choose 2:ℕ):ℝ):=Nat.cast_nonneg _;linarith
 have hN1_ch:(((N-1).choose 2:ℕ):ℝ)≤(N:ℝ)^2/2:=by
  have h2:2*(N-1).choose 2≤ N^2:=by
   rw[Nat.choose_two_right,Nat.mul_div_cancel' (Nat.even_mul_pred_self (N-1)).two_dvd]
   calc (N-1)*(N-1-1)≤ N*N:=Nat.mul_le_mul (Nat.sub_le N 1) (by omega)
     _=N^2:=by ring
  have h2R:2*(((N-1).choose 2:ℕ):ℝ)≤(N:ℝ)^2:=by exact_mod_cast h2
  linarith
 have hpackR:(H.card:ℝ)+(E_P.card:ℝ)+((Mq.card.choose 2:ℕ):ℝ)≤(((N-1).choose 2:ℕ):ℝ):=by exact_mod_cast hpack
 have hpartQ:(Q_c.card:ℝ)=(H.card:ℝ)+((Q_c \ H).card:ℝ):=by
  have h0:(Q_c \ H).card+H.card=Q_c.card:=Yb (Qx c B Q_c)
  have h1:Q_c.card=H.card+(Q_c \ H).card:=by omega
  exact_mod_cast h1
 have herr:=Qw N c hN Q_c B hQ_sub (fun S hS=>(hQc S hS).1)
  (fun S hS=>(hQc S hS).2) hB_sub hQc_hit
 have hlog_nn:0≤ log (N:ℝ):=Real.log_nonneg (by exact_mod_cast hN)
 have hN_le_log:4*(N:ℝ)≤10*(N:ℝ)*(log (N:ℝ)+2)^2:=by
  have h1:(4:ℝ)≤(log (N:ℝ)+2)^2:=by nlinarith
  nlinarith[Nat.cast_nonneg (α:=ℝ) N]
 have hfrac:(1/2-1/(2*(q:ℝ)^2))*(N:ℝ)^2=(N:ℝ)^2/2-(N:ℝ)^2/(2*(q:ℝ)^2):=by ring
 linarith
lemma Xn (N c:ℕ) (hN:1≤ N) (hc:c∈Icc 1 N)
  (P1_c Q_c:Zf (Zf ℕ)) (B:Zf ℕ)
  (hF:Zt N (P1_c∪Q_c))
  (hdisj:Disjoint P1_c Q_c)
  (hP1:∀ A∈P1_c,IsAP A/\2≤ A.card/\c∈A/\apStep A=1)
  (hQc:∀ S∈Q_c,¬ IsAP S/\c∈S)
  (hB_sub:B⊆(Icc 1 N).erase c) :
  ((Qa c B Q_c).card:ℝ)+(P1_c.card:ℝ) ≤(B.card:ℝ)*(N:ℝ)-(B.card:ℝ)^2/2+((N:ℝ)-(B.card:ℝ))^2/4+2*(N:ℝ):=by
 classical
 have hQ_sub:Zt N Q_c :=⟨(Zs (s₁:=P1_c)).trans hF.1,fun S hS T hT hST =>
   hF.2 (Zc.mpr (Zg _ (Zc.mp hS)))
    (Zc.mpr (Zg _ (Zc.mp hT))) hST⟩
 have hIcc:∀ A∈P1_c,∃ L R:ℕ,1≤ L/\L≤ c/\c≤ R/\R≤ N/\A=Icc L R:=by
  intro A hA;have hsubA:A⊆Icc 1 N:=Zy.mp (hF.1 (Ze _ hA));obtain⟨u,v,huc,hvN,hAeq⟩:=W0 hsubA (hP1 A hA).1 (hP1 A hA).2.1 (hP1 A hA).2.2.1;rw[(hP1 A hA).2.2.2] at huc hvN hAeq;simp only[mul_one] at huc hvN hAeq
  refine⟨c-u,c+v,by omega,by omega,by omega,by omega,?_⟩
  ext x;rw[hAeq x,Zb]
  constructor
  ·rintro (⟨i,hi,rfl⟩|⟨j,hj,rfl⟩) <;> omega
  ·intro ⟨h1,h2⟩
   rcases le_total x c with hle|hge
   ·left;exact⟨c-x,by omega,by omega⟩
   ·right;exact⟨x-c,by omega,by omega⟩
 let getL:Zf ℕ->ℕ:=fun A=>if hA:A∈P1_c then (hIcc A hA).choose else 0
 let getR:Zf ℕ->ℕ:=fun A=>if hA:A∈P1_c then (hIcc A hA).choose_spec.choose else 0
 have hLR:∀ A∈P1_c,1≤ getL A/\getL A≤ c/\c≤ getR A/\getR A≤ N/\A=Icc (getL A) (getR A):=by intro A hA;simpa only [getL,getR,dif_pos hA] using (hIcc A hA).choose_spec.choose_spec
 set P_bdy:=P1_c.filter (fun A=>getL A=c\/getR A=c)
 set P_hit:=P1_c.filter (fun A=>getL A< c/\c< getR A/\(getL A∈B\/getR A∈B))
 set P_free:=P1_c.filter (fun A=>getL A< c/\c< getR A/\getL A∉B/\getR A∉B)
 have hcov:P1_c⊆P_bdy∪P_hit∪P_free:=by
  intro A hA;obtain⟨_,hLc,hcR,_,_⟩:=hLR A hA
  by_cases hb:getL A=c\/getR A=c
  ·exact Ze _ (Ze _ (Za.mpr ⟨hA,hb⟩))
  ·by_cases hh:getL A∈B\/getR A∈B
   ·exact Ze _ (Zg _ (Za.mpr ⟨hA,by omega,by omega,hh⟩))
   ·push Not at hh
    exact Zg _ (Za.mpr ⟨hA,by omega,by omega,hh.1,hh.2⟩)
 have hinj_LR:Set.InjOn (fun A=>(getL A,getR A)) (P1_c:Set (Zf ℕ)):=by intro A hA B' hB' heq;have h1:getL A=getL B':=congrArg Prod.fst heq;have h2:getR A=getR B':=congrArg Prod.snd heq;rw[(hLR A (Zc.mp hA)).2.2.2.2,(hLR B' (Zc.mp hB')).2.2.2.2,h1,h2]
 have hPbdy_le:P_bdy.card≤ N+1:=by
  have hmaps:Set.MapsTo (fun A=>(getL A,getR A)) (P_bdy:Set (Zf ℕ))
    ((({c} ×ˢ Icc c N)∪(Icc 1 c ×ˢ {c}):Zf (ℕ × ℕ)):Set (ℕ × ℕ)):=by
   intro A hA;dsimp only;obtain⟨hAP,hb⟩:=Za.mp (Zc.mp hA);obtain⟨h1,hLc,hcR,hRN,-⟩:=hLR A hAP;rw[Zc,Zd]
   rcases hb with hL|hR
   ·left;exact Zh.mpr ⟨Zj.mpr hL,Zb.mpr ⟨hcR,hRN⟩⟩
   ·right;exact Zh.mpr ⟨Zb.mpr ⟨h1,hLc⟩,Zj.mpr hR⟩
  have hcI:=Zb.mp hc
  calc P_bdy.card≤(({c} ×ˢ Icc c N)∪(Icc 1 c ×ˢ {c})).card :=
        card_le_card_of_injOn _ hmaps (hinj_LR.mono (Finset.coe_subset.mpr (Zl _ _)))
    _≤({c} ×ˢ Icc c N).card+(Icc 1 c ×ˢ {c}).card:=Yh _ _
    _=(N+1-c)+c:=by simp[Nat.card_Icc]
    _=N+1:=by omega
 let Forbid:=P_hit.image (fun A=>({getL A,getR A}:Zf ℕ))
 have hF_card:Forbid.card=P_hit.card:=by
  refine card_image_of_injOn fun A hA A' hA' heq=>?_
  obtain⟨hAP,hLA,hRA,-⟩:=Za.mp (Zc.mp hA);obtain⟨hA'P,hLA',hRA',-⟩:=Za.mp (Zc.mp hA')
  have hm1:getL A∈({getL A',getR A'}:Zf ℕ):=by rw[←heq];simp
  have hm2:getR A∈({getL A',getR A'}:Zf ℕ):=by rw[←heq];simp
  simp only[Zx,Zj] at hm1 hm2
  have hpair:(getL A,getR A)=(getL A',getR A'):=Prod.ext (by omega) (by omega)
  exact hinj_LR (Zc.mpr hAP) (Zc.mpr hA'P) hpair
 have hF_sub:Forbid⊆Qj N c B:=by
  intro e he;obtain⟨A,hA,rfl⟩:=Zi.mp he;obtain⟨hAP,hL,hR,hh⟩:=Za.mp hA;obtain⟨h1,-,-,hRN,-⟩:=hLR A hAP
  refine Za.mpr ⟨Zz.mpr ⟨fun z hz=>?_,?_⟩,?_⟩
  ·simp only[Zx,Zj] at hz
   rcases hz with rfl|rfl <;> exact Zw.mpr ⟨by omega,Zb.mpr ⟨by omega,by omega⟩⟩
  ·rw[card_insert_of_notMem (Finset.notMem_singleton.mpr (by omega)),card_singleton]
  ·rcases hh with hLB|hRB
   ·exact⟨getL A,Zn.mpr ⟨by simp,hLB⟩⟩
   ·exact⟨getR A,Zn.mpr ⟨by simp,hRB⟩⟩
 have hF_disj:∀ S∈Q_c,Disjoint (Qs c S) Forbid:=by
  intro S hSQ;rw[Zk];intro e heS heF;obtain⟨A,hA,rfl⟩:=Zi.mp heF;have hAP:=(Za.mp hA).1;obtain⟨_,hLc,hcR,_,hAeq⟩:=hLR A hAP
  have hsubA:({getL A,getR A}:Zf ℕ)⊆A:=by
   intro z hz;simp only[Zx,Zj] at hz
   rw[hAeq,Zb];rcases hz with rfl|rfl <;> omega
  have hSA:S≠A:=fun h=>Zk.mp hdisj hAP (h ▸ hSQ)
  exact Qt hF (Zg _ hSQ) (Ze _ hAP)
   hSA (hP1 A hAP).2.2.1 heS hsubA
 have hhit_bd:=Qq (P:=B) hQ_sub (fun S hS=>(hQc S hS).2) hF_sub hF_disj
 rw[hF_card] at hhit_bd;set Lset:=(Icc 1 (c-1)) \ B;set Rset:=(Icc (c+1) N) \ B
 have hPfree_le:P_free.card≤ Lset.card*Rset.card:=by
  have hmaps:Set.MapsTo (fun A=>(getL A,getR A)) (P_free:Set (Zf ℕ)) ((Lset ×ˢ Rset:Zf (ℕ × ℕ)):Set (ℕ × ℕ)):=by
   intro A hA;dsimp only;obtain⟨hAP,hL,hR,hLB,hRB⟩:=Za.mp (Zc.mp hA);obtain⟨h1,-,-,hRN,-⟩:=hLR A hAP
   exact Zc.mpr (Zh.mpr
    ⟨Ye.mpr ⟨Zb.mpr ⟨h1,by omega⟩,hLB⟩,Ye.mpr ⟨Zb.mpr ⟨by omega,hRN⟩,hRB⟩⟩)
  exact (card_le_card_of_injOn _ hmaps (hinj_LR.mono (Finset.coe_subset.mpr (Zl _ _)))).trans
   (by rw[card_product])
 have hLR_sum:Lset.card+Rset.card+B.card=N-1:=by
  have hdisj_LR:Disjoint Lset Rset:=by
   rw[Zk];intro x h1 h2
   have:=(Zb.mp (Ye.mp h1).1).2
   have:=(Zb.mp (Ye.mp h2).1).1;omega
  have hunion:Lset∪Rset=((Icc 1 N).erase c) \ B:=by
   ext x;simp only[Lset,Rset,Zd,Ye,Zb,Zw];have hcI:=Zb.mp hc
   by_cases hxB:x∈B <;> simp[hxB];omega
  have h1:=Yb hB_sub;rw[←hunion,Zq hdisj_LR,card_erase_of_mem hc,Nat.card_Icc] at h1;omega
 have hP1_le:P1_c.card≤ P_bdy.card+P_hit.card+P_free.card:=by have h1:=(Zm hcov).trans (Yh _ _);have h2:=Yh P_bdy P_hit;omega
 have hHP_R:((Qa c B Q_c).card:ℝ)+(P_hit.card:ℝ) ≤(B.card:ℝ)*(N:ℝ)-(B.card:ℝ)^2/2 :=(by exact_mod_cast hhit_bd:((Qa c B Q_c).card:ℝ)+(P_hit.card:ℝ)≤((Qj N c B).card:ℝ)).trans
   (Wc N c hc B hB_sub)
 have hPfree_R:(P_free.card:ℝ)≤((N:ℝ)-(B.card:ℝ))^2/4:=by
  have h1:(P_free.card:ℝ)≤(Lset.card:ℝ)*(Rset.card:ℝ):=by exact_mod_cast hPfree_le
  have h2:(Lset.card:ℝ)+(Rset.card:ℝ)≤(N:ℝ)-(B.card:ℝ):=by
   have:Lset.card+Rset.card+B.card≤ N:=by omega
   have hR:(Lset.card:ℝ)+(Rset.card:ℝ)+(B.card:ℝ)≤(N:ℝ):=by exact_mod_cast this
   linarith
  nlinarith[sq_nonneg ((Lset.card:ℝ)-(Rset.card:ℝ))]
 have hPbdy_R:(P_bdy.card:ℝ)≤2*(N:ℝ):=by
  have:P_bdy.card≤2*N:=by omega
  exact_mod_cast this
 have hP1_R:(P1_c.card:ℝ)≤(P_bdy.card:ℝ)+(P_hit.card:ℝ)+(P_free.card:ℝ):=by exact_mod_cast hP1_le
 linarith
lemma Xh (N c R₁:ℕ) (hN:1≤ N) (hc:c∈Icc 1 N) (hR1:R₁< c)
  (P_c:Zf (Zf ℕ))
  (hPc_sub:∀ A∈P_c,A⊆Icc 1 N)
  (hPc:∀ A∈P_c,IsAP A/\2≤ A.card/\c∈A)
  (hPc_left:∀ A∈P_c,∃ z∈A,z≤ R₁) :
  (((P_c.filter (fun A=>apStep A=1)).card:ℝ)≤(R₁:ℝ)*((N-c:ℕ):ℝ)+2*(N:ℝ)) ∧
  (((P_c.filter (fun A=>2≤ apStep A)).card:ℝ) ≤(645/1000:ℝ)*(R₁:ℝ)*((N-c:ℕ):ℝ)+4*(N:ℝ)*(log (N:ℝ)+2)) ∧
  ((∀ A∈P_c,Odd (apStep A)) →
   ((P_c.filter (fun A=>2≤ apStep A)).card:ℝ) ≤(235/1000:ℝ)*(R₁:ℝ)*((N-c:ℕ):ℝ)+4*(N:ℝ)*(log (N:ℝ)+2)):=by
 classical
 have hUV_ex:∀ A∈P_c,∃ u v:ℕ,u*apStep A< c/\c+v*apStep A≤ N ∧
   (∀ x,x∈A↔(∃ i≤ u,x=c-i*apStep A)\/(∃ j≤ v,x=c+j*apStep A)) :=
  fun A hA=>W0 (hPc_sub A hA) (hPc A hA).1 (hPc A hA).2.1 (hPc A hA).2.2
 let getU:Zf ℕ->ℕ:=fun A=>if hA:A∈P_c then (hUV_ex A hA).choose else 0
 let getV:Zf ℕ->ℕ:=fun A=>if hA:A∈P_c then (hUV_ex A hA).choose_spec.choose else 0
 have hUV:∀ A∈P_c,getU A*apStep A< c/\c+getV A*apStep A≤ N ∧
   (∀ x,x∈A↔(∃ i≤ getU A,x=c-i*apStep A)\/(∃ j≤ getV A,x=c+j*apStep A)):=by
  intro A hA;simpa only [getU,getV,dif_pos hA] using (hUV_ex A hA).choose_spec.choose_spec
 have hper_d:∀ d:ℕ,1≤ d →
   (((P_c.filter (fun A=>apStep A=d)).card:ℝ) ≤((R₁:ℝ)/(d:ℝ)+1)*(((N-c:ℕ):ℝ)/(d:ℝ)+1)):=by
  intro d hd1
  set Pd:=P_c.filter (fun A=>apStep A=d)
  set uLo:=(c-R₁+d-1)/d;set uHi:=(c-1)/d;set vHi:=(N-c)/d
  have hmaps:Set.MapsTo (fun A=>(getU A,getV A)) (Pd:Set (Zf ℕ))
    (((Icc uLo uHi) ×ˢ (Icc 0 vHi):Zf (ℕ × ℕ)):Set (ℕ × ℕ)):=by
   intro A hA;obtain⟨hAPc,hAd⟩:=Za.mp (Zc.mp hA);obtain⟨huc,hvN,hAeq⟩:=hUV A hAPc;rw[hAd] at huc hvN hAeq;obtain⟨z,hzA,hzR⟩:=hPc_left A hAPc
   have hu_ge:c-R₁≤ getU A*d:=by
    rcases (hAeq z).mp hzA with ⟨i,hi,rfl⟩|⟨j,-,rfl⟩
    ·have:i*d≤ getU A*d:=Yc d hi;omega
    ·omega
   have hu_lo:uLo≤ getU A:=by
    dsimp only[uLo]
    exact (Nat.div_le_iff_le_mul_add_pred hd1).mpr (by rw[mul_comm];omega)
   have hu_hi:getU A≤ uHi:=(Nat.le_div_iff_mul_le hd1).mpr (by omega)
   have hv_hi:getV A≤ vHi:=(Nat.le_div_iff_mul_le hd1).mpr (by omega)
   exact Zc.mpr (Zh.mpr
    ⟨Zb.mpr ⟨hu_lo,hu_hi⟩,Zb.mpr ⟨Nat.zero_le _,hv_hi⟩⟩)
  have hinj:Set.InjOn (fun A=>(getU A,getV A)) (Pd:Set (Zf ℕ)):=by intro A hA B hB heq;obtain⟨hAPc,hAd⟩:=Za.mp (Zc.mp hA);obtain⟨hBPc,hBd⟩:=Za.mp (Zc.mp hB);have h1:getU A=getU B:=congrArg Prod.fst heq;have h2:getV A=getV B:=congrArg Prod.snd heq;ext x;rw[(hUV A hAPc).2.2 x,(hUV B hBPc).2.2 x,hAd,hBd,h1,h2]
  have hcard:Pd.card≤(Icc uLo uHi).card*(Icc 0 vHi).card:=by
   exact (card_le_card_of_injOn _ hmaps hinj).trans (by rw[card_product])
  have hu_cnt:((Icc uLo uHi).card:ℝ)≤(R₁:ℝ)/(d:ℝ)+1:=by
   rw[Nat.card_Icc]
   by_cases hle:uLo≤ uHi
   ·have hmul:(uHi-uLo)*d≤ R₁:=by
     have h1:uHi*d≤ c-1:=Nat.div_mul_le_self (c-1) d
     have h2:c-R₁≤ uLo*d:=by
      have:=Nat.lt_mul_div_succ (c-R₁+d-1) hd1
      have:c-R₁+d-1<(uLo+1)*d:=by rw[mul_comm];exact this
      have:(uLo+1)*d=uLo*d+d:=by ring
      omega
     rw[Nat.sub_mul];omega
    have hd_pos:(0:ℝ)<(d:ℝ):=by exact_mod_cast hd1
    have hmulR:((uHi-uLo:ℕ):ℝ)*(d:ℝ)≤(R₁:ℝ):=by exact_mod_cast hmul
    have hdiv:((uHi-uLo:ℕ):ℝ)≤(R₁:ℝ)/(d:ℝ):=(le_div_iff₀ hd_pos).mpr hmulR
    have heq:((uHi+1-uLo:ℕ):ℝ)=((uHi-uLo:ℕ):ℝ)+1:=by
     rw[show uHi+1-uLo=(uHi-uLo)+1 by omega];push_cast;rfl
    linarith
   ·have:uHi+1-uLo=0:=by omega
    rw[this,Nat.cast_zero];positivity
  have hv_cnt:((Icc 0 vHi).card:ℝ)≤((N-c:ℕ):ℝ)/(d:ℝ)+1:=by rw[Nat.card_Icc,Nat.sub_zero];push_cast;linarith[Nat.cast_div_le (m:=N-c) (n:=d) (α:=ℝ)]
  have hcardR:(Pd.card:ℝ)≤((Icc uLo uHi).card:ℝ)*((Icc 0 vHi).card:ℝ):=by exact_mod_cast hcard
  exact hcardR.trans (mul_le_mul hu_cnt hv_cnt (Nat.cast_nonneg _) (by positivity))
 have hcN:=(Zb.mp hc).2
 have hR1N:(R₁:ℝ)≤(N:ℝ):=by exact_mod_cast (by omega:R₁≤ N)
 have hNcN:((N-c:ℕ):ℝ)≤(N:ℝ):=by exact_mod_cast (Nat.sub_le N c)
 have hlog_nn:0≤ log (N:ℝ):=Real.log_nonneg (by exact_mod_cast hN)
 have hsum_err:∀ S:Zf ℕ,S⊆Icc 2 N →
   ∑ d∈S,(((R₁:ℝ)+((N-c:ℕ):ℝ))/(d:ℝ)+1)≤4*(N:ℝ)*(log (N:ℝ)+2):=by
  intro S hS
  have h1:∀ d∈S,((R₁:ℝ)+((N-c:ℕ):ℝ))/(d:ℝ)+1 ≤2*(N:ℝ)*((1:ℝ)/(d:ℝ))+1:=by
   intro d hd
   have hdpos:(0:ℝ)<(d:ℝ):=by exact_mod_cast (by have:=(Zb.mp (hS hd)).1;omega:0< d)
   have:((R₁:ℝ)+((N-c:ℕ):ℝ))/(d:ℝ)≤(2*(N:ℝ))/(d:ℝ) :=div_le_div_of_nonneg_right (by linarith) hdpos.le
   linarith[show (2*(N:ℝ))/(d:ℝ)=2*(N:ℝ)*((1:ℝ)/(d:ℝ)) by ring]
  have hsub1:S⊆Icc 1 N:=fun d hd=>by
   have h:=Zb.mp (hS hd);exact Zb.mpr ⟨by omega,h.2⟩
  have hharm:∑ d∈S,(1:ℝ)/(d:ℝ)≤ log (N:ℝ)+1 :=(sum_le_sum_of_subset_of_nonneg hsub1 (fun _ _ _=>by positivity)).trans (Q0 N hN)
  have hScard:(S.card:ℝ)≤(N:ℝ):=by
   have:=Zm hsub1;rw[Nat.card_Icc] at this;exact_mod_cast (by omega:S.card≤ N)
  calc ∑ d∈S,(((R₁:ℝ)+((N-c:ℕ):ℝ))/(d:ℝ)+1)
      ≤ ∑ d∈S,(2*(N:ℝ)*((1:ℝ)/(d:ℝ))+1):=Finset.sum_le_sum h1
    _=2*(N:ℝ)*(∑ d∈S,(1:ℝ)/(d:ℝ))+(S.card:ℝ):=by
        rw[Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,nsmul_eq_mul,mul_one]
    _≤2*(N:ℝ)*(log (N:ℝ)+1)+(N:ℝ):=by nlinarith
    _≤4*(N:ℝ)*(log (N:ℝ)+2):=by nlinarith
 refine⟨?_,?_,?_⟩
 ·have h1:=hper_d 1 (by omega)
  simp only[Nat.cast_one,div_one] at h1
  have hsum1:(R₁:ℝ)+((N-c:ℕ):ℝ)+1≤2*(N:ℝ):=by
   have:R₁+(N-c)+1≤2*N:=by omega
   exact_mod_cast this
  nlinarith
 ·have hpart:(P_c.filter (fun A=>2≤ apStep A)).card =∑ d∈Icc 2 N,(P_c.filter (fun A=>apStep A=d)).card:=by
   rw[←card_biUnion]
   ·congr 1;ext A;simp only[mem_biUnion,Zb,Za]
    constructor
    ·rintro⟨hA,h2⟩
     have hdN:=(Qg (hPc_sub A hA) (hPc A hA).1 (hPc A hA).2.1).2.1;exact⟨apStep A,⟨h2,hdN⟩,hA,rfl⟩
    ·rintro⟨d,⟨h2,-⟩,hA,rfl⟩;exact⟨hA,h2⟩
   ·intro d₁ _ d₂ _ hne;simp only[Function.onFun];rw[Zk]
    intro A h1 h2;exact hne ((Za.mp h1).2.symm.trans (Za.mp h2).2)
  have hsum_inv2:∑ d∈Icc 2 N,(1:ℝ)/(d:ℝ)^2≤645/1000:=by
   have h1:=W3 N
   have hsplit:∑ d∈Icc 1 N,(1:ℝ)/(d:ℝ)^2 =1+∑ d∈Icc 2 N,(1:ℝ)/(d:ℝ)^2:=by
    have hdisj:Disjoint ({1}:Zf ℕ) (Icc 2 N):=by rw[Zk];intro d h1' h2';simp at h1';have:=(Zb.mp h2').1;omega
    have heq:Icc 1 N={1}∪Icc 2 N:=by ext d;simp only[Zb,Zd,Zj];omega
    rw[heq,Finset.sum_union hdisj,Finset.sum_singleton];norm_num
   linarith
  have hcast:((P_c.filter (fun A=>2≤ apStep A)).card:ℝ) =∑ d∈Icc 2 N,((P_c.filter (fun A=>apStep A=d)).card:ℝ):=by exact_mod_cast hpart
  rw[hcast]
  have hstep:∀ d∈Icc 2 N,((P_c.filter (fun A=>apStep A=d)).card:ℝ) ≤(R₁:ℝ)*((N-c:ℕ):ℝ)*((1:ℝ)/(d:ℝ)^2) +(((R₁:ℝ)+((N-c:ℕ):ℝ))/(d:ℝ)+1):=by
   intro d hd
   have h1:=hper_d d (by have:=(Zb.mp hd).1;omega)
   have heq:((R₁:ℝ)/(d:ℝ)+1)*(((N-c:ℕ):ℝ)/(d:ℝ)+1) =(R₁:ℝ)*((N-c:ℕ):ℝ)*((1:ℝ)/(d:ℝ)^2) +(((R₁:ℝ)+((N-c:ℕ):ℝ))/(d:ℝ)+1):=by ring
   linarith
  calc ∑ d∈Icc 2 N,((P_c.filter (fun A=>apStep A=d)).card:ℝ)
      ≤ ∑ d∈Icc 2 N,((R₁:ℝ)*((N-c:ℕ):ℝ)*((1:ℝ)/(d:ℝ)^2) +(((R₁:ℝ)+((N-c:ℕ):ℝ))/(d:ℝ)+1)):=Finset.sum_le_sum hstep
    _=(R₁:ℝ)*((N-c:ℕ):ℝ)*(∑ d∈Icc 2 N,(1:ℝ)/(d:ℝ)^2) +
        ∑ d∈Icc 2 N,(((R₁:ℝ)+((N-c:ℕ):ℝ))/(d:ℝ)+1):=by
        rw[Finset.sum_add_distrib,←Finset.mul_sum]
    _≤(645/1000:ℝ)*(R₁:ℝ)*((N-c:ℕ):ℝ)+4*(N:ℝ)*(log (N:ℝ)+2):=by
        have h1:=Zp hsum_inv2 (by positivity:(0:ℝ)≤(R₁:ℝ)*((N-c:ℕ):ℝ))
        have h2:=hsum_err (Icc 2 N) Subset.rfl;linarith
 ·intro hodd
  set S_odd:=(Icc 2 N).filter Odd
  have hpart:(P_c.filter (fun A=>2≤ apStep A)).card =∑ d∈S_odd,(P_c.filter (fun A=>apStep A=d)).card:=by
   rw[←card_biUnion]
   ·congr 1;ext A;simp only[S_odd,mem_biUnion,Za,Zb]
    constructor
    ·rintro⟨hA,h2⟩
     have hdN:=(Qg (hPc_sub A hA) (hPc A hA).1 (hPc A hA).2.1).2.1;exact⟨apStep A,⟨⟨h2,hdN⟩,hodd A hA⟩,hA,rfl⟩
    ·rintro⟨d,⟨⟨h2,-⟩,-⟩,hA,rfl⟩;exact⟨hA,h2⟩
   ·intro d₁ _ d₂ _ hne;simp only[Function.onFun];rw[Zk]
    intro A h1 h2;exact hne ((Za.mp h1).2.symm.trans (Za.mp h2).2)
  have hsum_inv_odd:∑ d∈S_odd,(1:ℝ)/(d:ℝ)^2≤235/1000:=by
   have h1:=Xa N
   have hsplit:∑ d∈(Icc 1 N).filter Odd,(1:ℝ)/(d:ℝ)^2 =1+∑ d∈S_odd,(1:ℝ)/(d:ℝ)^2:=by
    have hdisj:Disjoint ({1}:Zf ℕ) S_odd:=by
     rw[Zk];intro d h1' h2';simp at h1'
     have:=(Zb.mp (Za.mp h2').1).1;omega
    have heq:(Icc 1 N).filter Odd={1}∪S_odd:=by
     ext d;simp only[S_odd,Za,Zb,Zd,Zj]
     constructor
     ·rintro⟨⟨h1',h2'⟩,ho⟩
      rcases eq_or_lt_of_le h1' with rfl|hgt
      ·left;rfl
      ·right;exact⟨⟨by omega,h2'⟩,ho⟩
     ·rintro (rfl|⟨⟨h1',h2'⟩,ho⟩)
      ·exact⟨⟨le_rfl,hN⟩,⟨0,rfl⟩⟩
      ·exact⟨⟨by omega,h2'⟩,ho⟩
    rw[heq,Finset.sum_union hdisj,Finset.sum_singleton];norm_num
   linarith
  have hcast:((P_c.filter (fun A=>2≤ apStep A)).card:ℝ) =∑ d∈S_odd,((P_c.filter (fun A=>apStep A=d)).card:ℝ):=by exact_mod_cast hpart
  rw[hcast]
  have hstep:∀ d∈S_odd,((P_c.filter (fun A=>apStep A=d)).card:ℝ) ≤(R₁:ℝ)*((N-c:ℕ):ℝ)*((1:ℝ)/(d:ℝ)^2) +(((R₁:ℝ)+((N-c:ℕ):ℝ))/(d:ℝ)+1):=by
   intro d hd
   have h1:=hper_d d (by have:=(Zb.mp (Za.mp hd).1).1;omega)
   have heq:((R₁:ℝ)/(d:ℝ)+1)*(((N-c:ℕ):ℝ)/(d:ℝ)+1) =(R₁:ℝ)*((N-c:ℕ):ℝ)*((1:ℝ)/(d:ℝ)^2) +(((R₁:ℝ)+((N-c:ℕ):ℝ))/(d:ℝ)+1):=by ring
   linarith
  calc ∑ d∈S_odd,((P_c.filter (fun A=>apStep A=d)).card:ℝ)
      ≤ ∑ d∈S_odd,((R₁:ℝ)*((N-c:ℕ):ℝ)*((1:ℝ)/(d:ℝ)^2) +(((R₁:ℝ)+((N-c:ℕ):ℝ))/(d:ℝ)+1)):=Finset.sum_le_sum hstep
    _=(R₁:ℝ)*((N-c:ℕ):ℝ)*(∑ d∈S_odd,(1:ℝ)/(d:ℝ)^2) +
        ∑ d∈S_odd,(((R₁:ℝ)+((N-c:ℕ):ℝ))/(d:ℝ)+1):=by
        rw[Finset.sum_add_distrib,←Finset.mul_sum]
    _≤(235/1000:ℝ)*(R₁:ℝ)*((N-c:ℕ):ℝ)+4*(N:ℝ)*(log (N:ℝ)+2):=by
        have h1:=Zp hsum_inv_odd (by positivity:(0:ℝ)≤(R₁:ℝ)*((N-c:ℕ):ℝ))
        have h2:=hsum_err S_odd (Zl _ _);linarith
private lemma V2 (d₀ N t w y g mb:ℝ) (hd₀:1≤ d₀) (hN:0< N)
  (ht:0≤ t) (hy:0≤ y) (hg:0≤ g) (hw1:w≤1)
  (hw_ge:t/d₀≤ w) (hw_le:w≤ t+1/N) :
  (mb-mb^2/2)+((t-w)*y-w*(g+t)+w^2/2) ≤ max ((mb-mb^2/2)+(max 0 ((d₀-1)*y-g))^2/(4*d₀-2)) (y-y^2-g*y)+1/N:=by
 set w0:ℝ:=t/d₀
 have hw0_nn:0≤ w0:=div_nonneg ht (by linarith)
 have hw0_le_t:w0≤ t:=div_le_self ht hd₀
 have hdec:(t-w)*y-w*(g+t)+w^2/2 ≤(t-w0)*y-w0*(g+t)+w0^2/2+1/N:=by
  have h1:((t-w)*y-w*(g+t)+w^2/2)-((t-w0)*y-w0*(g+t)+w0^2/2) =(w-w0)*((w+w0)/2-(y+g+t)):=by ring
  have hhalf:(1/N)/2=1/(2*N):=by ring
  have h2:(w+w0)/2-(y+g+t)≤1/(2*N):=by linarith
  have h3:0≤ w-w0:=by linarith
  have h4:w-w0≤1:=by linarith
  have h5:(w-w0)*((w+w0)/2-(y+g+t))≤1*(1/(2*N)):=by
   nlinarith[show (0:ℝ)≤1/(2*N) by positivity]
  have h6:1/(2*N)≤1/N:=by linarith[show (0:ℝ)≤1/(2*N) by positivity]
  linarith
 have hpeak:(t-w0)*y-w0*(g+t)+w0^2/2 ≤(max 0 ((d₀-1)*y-g))^2/(4*d₀-2):=by
  set A:=max 0 ((d₀-1)*y-g);have hA_ge:(d₀-1)*y-g≤ A:=Yn _ _
  have ht_eq:t=d₀*w0:=by dsimp only[w0];field_simp
  have h1:(t-w0)*y-w0*(g+t)+w0^2/2 =((d₀-1)*y-g)*w0-((2*d₀-1)/2)*w0^2:=by rw[ht_eq];ring
  rw[h1];have h2:((d₀-1)*y-g)*w0≤ A*w0:=Zo hA_ge hw0_nn
  have hring:A^2/(4*d₀-2)-(A*w0-((2*d₀-1)/2)*w0^2) =((2*d₀-1)/2)*(w0-A/(2*d₀-1))^2:=by
   have hne:(2*d₀-1)≠0:=by linarith
   rw[show 4*d₀-2=2*(2*d₀-1) by ring]
   field_simp;ring
  have hnn2:0≤((2*d₀-1)/2)*(w0-A/(2*d₀-1))^2:=by
   have:0≤(2*d₀-1)/2:=by linarith
   positivity
  linarith
 have hmax1:(mb-mb^2/2)+(max 0 ((d₀-1)*y-g))^2/(4*d₀-2) ≤ max ((mb-mb^2/2)+(max 0 ((d₀-1)*y-g))^2/(4*d₀-2)) (y-y^2-g*y) :=Ym _ _;linarith
private lemma V1 (d₀ N t y g mb:ℝ) (hd₀:1≤ d₀) (hN:0< N)
  (hy:0≤ y) (hmb:0≤ mb) (hmb1:mb≤1)
  (ht_ge:d₀*mb-d₀/N≤ t) (ht_le:t≤1-y-g) :
  (mb-mb^2/2)+((t-mb)*y-mb*(g+t)+mb^2/2) ≤ max ((mb-mb^2/2)+(max 0 ((d₀-1)*y-g))^2/(4*d₀-2)) (y-y^2-g*y)+d₀/N:=by
 by_cases hym:y≤ mb
 ·set t0:ℝ:=d₀*mb
  have hstep:(t-mb)*y-mb*(g+t)+mb^2/2 ≤(t0-mb)*y-mb*(g+t0)+mb^2/2+d₀/N:=by
   have h1:((t-mb)*y-mb*(g+t)+mb^2/2)-((t0-mb)*y-mb*(g+t0)+mb^2/2) =(t0-t)*(mb-y):=by ring
   have h2:(t0-t)*(mb-y)≤(d₀/N)*1:=by
    nlinarith[show (0:ℝ)≤ d₀/N by positivity]
   linarith
  have hpeak:(t0-mb)*y-mb*(g+t0)+mb^2/2 ≤(max 0 ((d₀-1)*y-g))^2/(4*d₀-2):=by
   set A:=max 0 ((d₀-1)*y-g);have hA_ge:(d₀-1)*y-g≤ A:=Yn _ _
   have h1:(t0-mb)*y-mb*(g+t0)+mb^2/2 =((d₀-1)*y-g)*mb-((2*d₀-1)/2)*mb^2:=by dsimp only[t0];ring
   rw[h1];have h2:((d₀-1)*y-g)*mb≤ A*mb:=Zo hA_ge hmb
   have hring:A^2/(4*d₀-2)-(A*mb-((2*d₀-1)/2)*mb^2) =((2*d₀-1)/2)*(mb-A/(2*d₀-1))^2:=by
    have hne:(2*d₀-1)≠0:=by linarith
    rw[show 4*d₀-2=2*(2*d₀-1) by ring]
    field_simp;ring
   have hnn2:0≤((2*d₀-1)/2)*(mb-A/(2*d₀-1))^2:=by
    have:0≤(2*d₀-1)/2:=by linarith
    positivity
   linarith
  have hmax1:(mb-mb^2/2)+(max 0 ((d₀-1)*y-g))^2/(4*d₀-2) ≤ max ((mb-mb^2/2)+(max 0 ((d₀-1)*y-g))^2/(4*d₀-2)) (y-y^2-g*y) :=Ym _ _;linarith
 ·have hstep:(mb-mb^2/2)+((t-mb)*y-mb*(g+t)+mb^2/2)≤ y-y^2-g*y:=by
   have h1:((mb-mb^2/2)+((t-mb)*y-mb*(g+t)+mb^2/2))-(y-y^2-g*y) =(t-(1-y-g))*(y-mb):=by ring
   nlinarith
  have hmax2:y-y^2-g*y ≤ max ((mb-mb^2/2)+(max 0 ((d₀-1)*y-g))^2/(4*d₀-2)) (y-y^2-g*y) :=Yn _ _
  have hdN_nn:0≤ d₀/N:=div_nonneg (by linarith) hN.le
  linarith
private lemma X2 {U B:Zf ℕ} (hBU:B⊆U) :2*((U.powersetCard 2).filter (fun e=>(e∩B).Nonempty)).card =B.card*(B.card-1)+2*B.card*(U.card-B.card):=by
 classical
 set V:=U \ B
 have hVcard:V.card=U.card-B.card:=by have h0:V.card+B.card=U.card:=Yb hBU;omega
 have hU_ch:(U.powersetCard 2).card =((U.powersetCard 2).filter (fun e=>(e∩B).Nonempty)).card+(V.powersetCard 2).card:=by
  have hcompl:(U.powersetCard 2).filter (fun e=>¬ (e∩B).Nonempty)=V.powersetCard 2:=by
   ext e;simp only[Za,Zz,not_nonempty_iff_eq_empty]
   constructor
   ·rintro⟨⟨heU,he2⟩,hemp⟩
    refine⟨fun z hz=>Ye.mpr ⟨heU hz,fun hzB=>?_⟩,he2⟩
    have:z∈e∩B:=Zn.mpr ⟨hz,hzB⟩
    rw[hemp] at this;exact Finset.notMem_empty z this
   ·rintro⟨heV,he2⟩
    refine⟨⟨heV.trans Finset.sdiff_subset,he2⟩,?_⟩
    rw[eq_empty_iff_forall_notMem];intro z hz;obtain⟨hze,hzB⟩:=Zn.mp hz;exact (Ye.mp (heV hze)).2 hzB
  rw[←hcompl];exact (card_filter_add_card_filter_not _).symm
 rw[card_powersetCard,card_powersetCard,hVcard] at hU_ch
 have h1:2*U.card.choose 2=U.card*(U.card-1):=by rw[Nat.choose_two_right,Nat.mul_div_cancel' (Nat.even_mul_pred_self U.card).two_dvd]
 have h2:2*(U.card-B.card).choose 2=(U.card-B.card)*(U.card-B.card-1):=by rw[Nat.choose_two_right,Nat.mul_div_cancel' (Nat.even_mul_pred_self _).two_dvd]
 have hw_le:B.card≤ U.card:=Zm hBU
 have hdiff:U.card*(U.card-1)=(U.card-B.card)*(U.card-B.card-1) +B.card*(B.card-1)+2*B.card*(U.card-B.card):=by
  rcases Nat.eq_zero_or_pos B.card with hw0|hwpos
  ·rw[hw0];simp
  ·rcases eq_or_lt_of_le hw_le with heq|hlt
   ·rw[heq,Nat.sub_self];simp
   ·zify [hw_le,hwpos,(show 1≤ U.card by omega),(show 1≤ U.card-B.card by omega)];ring
 omega
lemma Xd (N c L_s d₀ m_b:ℕ) (hN:1≤ N) (hc:c∈Icc 1 N)
  (hd₀:1≤ d₀) (hmb:1≤ m_b) (hL1:1≤ L_s) (hRc:L_s+(m_b-1)*d₀< c)
  (B_s:Zf ℕ) (hBs_eq:∀ x,x∈B_s↔∃ i< m_b,x=L_s+i*d₀)
  (P1_c Q_c:Zf (Zf ℕ))
  (hF:Zt N (P1_c∪Q_c))
  (hdisj:Disjoint P1_c Q_c)
  (hP1:∀ A∈P1_c,IsAP A/\2≤ A.card/\c∈A/\apStep A=1)
  (hP1_hit:∀ A∈P1_c,(A∩B_s).Nonempty)
  (hQc:∀ S∈Q_c,¬ IsAP S/\c∈S) :
  let R_s:=L_s+(m_b-1)*d₀
  let mb:ℝ:=(m_b:ℝ)/(N:ℝ)
  let g:ℝ:=((c-R_s:ℕ):ℝ)/(N:ℝ)
  let y:ℝ:=((N-c:ℕ):ℝ)/(N:ℝ)
  ((Qa c B_s Q_c).card:ℝ)+(P1_c.card:ℝ) ≤ max ((mb-mb^2/2)+(max 0 (((d₀:ℝ)-1)*y-g))^2/(4*(d₀:ℝ)-2))
     (y-y^2-g*y)*(N:ℝ)^2+12*(d₀:ℝ)*(N:ℝ):=by
 classical
 intro R_s mb g y
 have hN_pos:(0:ℝ)<(N:ℝ):=by exact_mod_cast (by omega:0< N)
 have hcN:=(Zb.mp hc).2;have hRs_lt:R_s< c:=hRc
 have hBs_card:B_s.card=m_b:=Qo hmb (fun _=>hd₀) hBs_eq
 have hBs_sub:B_s⊆(Icc 1 N).erase c:=by
  intro x hx;obtain⟨i,hi,rfl⟩:=(hBs_eq x).mp hx
  have:i*d₀≤(m_b-1)*d₀:=Yc d₀ (by omega)
  exact Zw.mpr ⟨by omega,Zb.mpr ⟨by omega,by omega⟩⟩
 have hQ_sub:Zt N Q_c :=⟨(Zs (s₁:=P1_c)).trans hF.1,fun S hS T hT hST =>
   hF.2 (Zc.mpr (Zg _ (Zc.mp hS)))
    (Zc.mpr (Zg _ (Zc.mp hT))) hST⟩
 have hIcc:∀ A∈P1_c,∃ L R:ℕ,1≤ L/\L≤ R_s/\c≤ R/\R≤ N/\A=Icc L R:=by
  intro A hA;have hsubA:A⊆Icc 1 N:=Zy.mp (hF.1 (Ze _ hA));obtain⟨u,v,huc,hvN,hAeq⟩:=W0 hsubA (hP1 A hA).1 (hP1 A hA).2.1 (hP1 A hA).2.2.1;rw[(hP1 A hA).2.2.2] at huc hvN hAeq;simp only[mul_one] at huc hvN hAeq
  have hEq:A=Icc (c-u) (c+v):=by
   ext x;rw[hAeq x,Zb]
   constructor
   ·rintro (⟨i,hi,rfl⟩|⟨j,hj,rfl⟩) <;> omega
   ·intro ⟨h1,h2⟩
    rcases le_total x c with hle|hge
    ·left;exact⟨c-x,by omega,by omega⟩
    ·right;exact⟨x-c,by omega,by omega⟩
  obtain⟨z,hz⟩:=hP1_hit A hA;obtain⟨hzA,hzB⟩:=Zn.mp hz;obtain⟨i,hi,rfl⟩:=(hBs_eq z).mp hzB
  have hzR:L_s+i*d₀≤ R_s:=by
   have:i*d₀≤(m_b-1)*d₀:=Yc d₀ (by omega);dsimp only[R_s];omega
  have hcu:c-u≤ L_s+i*d₀:=(Zb.mp (hEq ▸ hzA)).1
  exact⟨c-u,c+v,by omega,by omega,by omega,by omega,hEq⟩
 let getL:Zf ℕ->ℕ:=fun A=>if hA:A∈P1_c then (hIcc A hA).choose else 0
 let getR:Zf ℕ->ℕ:=fun A=>if hA:A∈P1_c then (hIcc A hA).choose_spec.choose else 0
 have hLR:∀ A∈P1_c,1≤ getL A/\getL A≤ R_s/\c≤ getR A/\getR A≤ N/\A=Icc (getL A) (getR A):=by intro A hA;simpa only [getL,getR,dif_pos hA] using (hIcc A hA).choose_spec.choose_spec
 have hinj_LR:Set.InjOn (fun A=>(getL A,getR A)) (P1_c:Set (Zf ℕ)):=by intro A hA A' hA' heq;have h1:getL A=getL A':=congrArg Prod.fst heq;have h2:getR A=getR A':=congrArg Prod.snd heq;rw[(hLR A (Zc.mp hA)).2.2.2.2,(hLR A' (Zc.mp hA')).2.2.2.2,h1,h2]
 set P_bdy:=P1_c.filter (fun A=>getR A=c)
 set P_int:=P1_c.filter (fun A=>c< getR A)
 have hP1_split:P1_c.card=P_bdy.card+P_int.card:=by
  have heq:P_int=P1_c.filter (fun A=>¬ (getR A=c)):=by
   refine filter_congr fun A hA=>?_;have:=(hLR A hA).2.2.1;omega
  rw[heq];exact (card_filter_add_card_filter_not _).symm
 have hPbdy_le:P_bdy.card≤ N:=by
  have hmaps:Set.MapsTo (fun A=>(getL A,getR A)) (P_bdy:Set (Zf ℕ))
    (((Icc 1 N) ×ˢ {c}:Zf (ℕ × ℕ)):Set (ℕ × ℕ)):=by
   intro A hA;dsimp only;obtain⟨hAP,hRc'⟩:=Za.mp (Zc.mp hA);obtain⟨h1,hLR',-,-,-⟩:=hLR A hAP
   exact Zc.mpr (Zh.mpr ⟨Zb.mpr ⟨h1,by omega⟩,Zj.mpr hRc'⟩)
  exact (card_le_card_of_injOn _ hmaps (hinj_LR.mono (Finset.coe_subset.mpr (Zl _ _)))).trans
   (by simp[Nat.card_Icc])
 rcases P_int.eq_empty_or_nonempty with hPint0|hPint_ne
 ·have hhit:=Qq (P:=B_s) hQ_sub (fun S hS=>(hQc S hS).2)
   (Forbid:=∅) (Finset.empty_subset _) (fun _ _=>Finset.disjoint_empty_right _)
  simp only[card_empty,add_zero] at hhit
  have hhitR:((Qa c B_s Q_c).card:ℝ)≤(mb-mb^2/2)*(N:ℝ)^2:=by
   have h1:=(by exact_mod_cast hhit:((Qa c B_s Q_c).card:ℝ)≤((Qj N c B_s).card:ℝ)).trans
    (Wc N c hc B_s hBs_sub)
   rw[hBs_card] at h1
   have h2:(m_b:ℝ)*(N:ℝ)-(m_b:ℝ)^2/2=(mb-mb^2/2)*(N:ℝ)^2:=by dsimp only[mb];field_simp
   linarith
  have hP1R:(P1_c.card:ℝ)≤(N:ℝ):=by rw[hP1_split,hPint0,card_empty,add_zero];exact_mod_cast hPbdy_le
  have hnn:(0:ℝ)≤(max 0 (((d₀:ℝ)-1)*y-g))^2/(4*(d₀:ℝ)-2):=by
   have:(1:ℝ)≤(d₀:ℝ):=by exact_mod_cast hd₀
   have:(0:ℝ)<4*(d₀:ℝ)-2:=by linarith
   positivity
  have hmax1:(mb-mb^2/2) ≤ max ((mb-mb^2/2)+(max 0 (((d₀:ℝ)-1)*y-g))^2/(4*(d₀:ℝ)-2)) (y-y^2-g*y) :=le_trans (by linarith) (Ym _ _)
  have hd₀1:(1:ℝ)≤(d₀:ℝ):=by exact_mod_cast hd₀
  nlinarith[sq_nonneg (N:ℝ)]
 obtain⟨A_L,hAL_mem,hAL_min⟩:=exists_min_image P_int getL hPint_ne;have hAL_P1:=(Za.mp hAL_mem).1;obtain⟨hl1,hlR,-,-,hAL_eq⟩:=hLR A_L hAL_P1;set l_min:=getL A_L
 set B_cov:=B_s.filter (fun x=>l_min≤ x)
 set P_hit:=P_int.filter (fun A=>getL A∈B_cov)
 set P_free:=P_int.filter (fun A=>getL A∉B_cov)
 have hPint_split:P_int.card=P_hit.card+P_free.card :=(card_filter_add_card_filter_not _).symm
 let F1:=((Icc l_min (c-1)).powersetCard 2).filter (fun e=>(e∩B_cov).Nonempty)
 let F2:=P_hit.image (fun A=>({getL A,getR A}:Zf ℕ))
 have hF1_sub:F1⊆Qj N c B_s:=by
  intro e he;obtain⟨heI,⟨p,hp⟩⟩:=Za.mp he;obtain⟨heSub,he2⟩:=Zz.mp heI;obtain⟨hpe,hpBc⟩:=Zn.mp hp
  refine Za.mpr ⟨Zz.mpr ⟨fun z hz=>?_,he2⟩,⟨p,Zn.mpr ⟨hpe,(Za.mp hpBc).1⟩⟩⟩
  have hzI:=Zb.mp (heSub hz)
  exact Zw.mpr ⟨by omega,Zb.mpr ⟨by omega,by omega⟩⟩
 have hF2_sub:F2⊆Qj N c B_s:=by
  intro e he;obtain⟨A,hA,rfl⟩:=Zi.mp he;obtain⟨hAint,hLBc⟩:=Za.mp hA;obtain⟨hAP1,hcRA⟩:=Za.mp hAint;obtain⟨h1,hLR',-,hRN,-⟩:=hLR A hAP1
  refine Za.mpr ⟨Zz.mpr ⟨fun z hz=>?_,?_⟩,⟨getL A,Zn.mpr ⟨by simp,(Za.mp hLBc).1⟩⟩⟩
  ·simp only[Zx,Zj] at hz
   rcases hz with rfl|rfl <;> exact Zw.mpr ⟨by omega,Zb.mpr ⟨by omega,by omega⟩⟩
  ·rw[card_insert_of_notMem (Finset.notMem_singleton.mpr (by omega)),card_singleton]
 have hF12_disj:Disjoint F1 F2:=by
  rw[Zk];intro e h1 h2;obtain⟨A,hA,rfl⟩:=Zi.mp h2;have hcRA:=(Za.mp (Za.mp hA).1).2;have hsub:=(Zz.mp (Za.mp h1).1).1
  have hRA_le:=(Zb.mp (hsub (by simp:getR A∈({getL A,getR A}:Zf ℕ)))).2
  omega
 have hF_disj_Q:∀ S∈Q_c,Disjoint (Qs c S) (F1∪F2):=by
  intro S hSQ;rw[Zk];intro e heS heU
  rcases Zd.mp heU with he1|he2
  ·have hsubI:=(Zz.mp (Za.mp he1).1).1
   have hsubAL:e⊆A_L:=by
    intro z hz;have hzI:=Zb.mp (hsubI hz);rw[hAL_eq,Zb]
    have:=(hLR A_L hAL_P1).2.2.1;exact⟨hzI.1,by omega⟩
   have hSA:S≠A_L:=fun h=>Zk.mp hdisj hAL_P1 (h ▸ hSQ)
   exact Qt hF (Zg _ hSQ) (Ze _ hAL_P1)
    hSA (hP1 A_L hAL_P1).2.2.1 heS hsubAL
  ·obtain⟨A,hA,rfl⟩:=Zi.mp he2
   have hAP1:=(Za.mp (Za.mp hA).1).1
   have hsubA:({getL A,getR A}:Zf ℕ)⊆A:=by
    obtain⟨_,hLR',hcR,_,hAeq⟩:=hLR A hAP1;intro z hz;simp only[Zx,Zj] at hz
    rw[hAeq,Zb];rcases hz with rfl|rfl <;> omega
   have hSA:S≠A:=fun h=>Zk.mp hdisj hAP1 (h ▸ hSQ)
   exact Qt hF (Zg _ hSQ) (Ze _ hAP1)
    hSA (hP1 A hAP1).2.2.1 heS hsubA
 have hF2_card:F2.card=P_hit.card:=by
  refine card_image_of_injOn fun A hA A' hA' heq=>?_
  obtain⟨hAP1,hcRA⟩:=Za.mp (Za.mp (Zc.mp hA)).1;obtain⟨hA'P1,hcRA'⟩:=Za.mp (Za.mp (Zc.mp hA')).1;have hLA:=(hLR A hAP1).2.1;have hLA':=(hLR A' hA'P1).2.1
  have hm1:getL A∈({getL A',getR A'}:Zf ℕ):=by rw[←heq];simp
  have hm2:getR A∈({getL A',getR A'}:Zf ℕ):=by rw[←heq];simp
  simp only[Zx,Zj] at hm1 hm2
  have hpair:(getL A,getR A)=(getL A',getR A'):=Prod.ext (by omega) (by omega)
  exact hinj_LR (Zc.mpr hAP1) (Zc.mpr hA'P1) hpair
 set w_nat:=B_cov.card;set span_nat:=c-l_min
 have hBcov_sub:B_cov⊆Icc l_min (c-1):=by
  intro x hx;obtain⟨hxB,hxl⟩:=Za.mp hx;obtain⟨i,hi,rfl⟩:=(hBs_eq x).mp hxB
  have:i*d₀≤(m_b-1)*d₀:=Yc d₀ (by omega)
  exact Zb.mpr ⟨hxl,by omega⟩
 have hF1_card:2*F1.card=w_nat*(w_nat-1)+2*w_nat*(span_nat-w_nat):=by
  have h0:=X2 hBcov_sub
  have hUcard:(Icc l_min (c-1)).card=span_nat:=by rw[Nat.card_Icc];omega
  rwa[hUcard] at h0
 have hPfree_le:P_free.card≤(R_s-l_min+1-w_nat)*(N-c):=by
  set Lf:=(Icc l_min R_s) \ B_cov
  have hBcov_subR:B_cov⊆Icc l_min R_s:=by
   intro x hx;obtain⟨hxB,hxl⟩:=Za.mp hx;obtain⟨i,hi,rfl⟩:=(hBs_eq x).mp hxB
   have:i*d₀≤(m_b-1)*d₀:=Yc d₀ (by omega)
   exact Zb.mpr ⟨hxl,by dsimp only[R_s];omega⟩
  have hLf_card:Lf.card=R_s-l_min+1-w_nat:=by have h1:Lf.card+w_nat=(Icc l_min R_s).card:=Yb hBcov_subR;rw[Nat.card_Icc] at h1;omega
  have hmaps:Set.MapsTo (fun A=>(getL A,getR A)) (P_free:Set (Zf ℕ))
    ((Lf ×ˢ Icc (c+1) N:Zf (ℕ × ℕ)):Set (ℕ × ℕ)):=by
   intro A hA;dsimp only;obtain⟨hAint,hLnot⟩:=Za.mp (Zc.mp hA);obtain⟨hAP1,hcRA⟩:=Za.mp hAint;obtain⟨-,hLR',-,hRN,-⟩:=hLR A hAP1;have hl_le:l_min≤ getL A:=hAL_min A hAint
   exact Zc.mpr (Zh.mpr
    ⟨Ye.mpr ⟨Zb.mpr ⟨hl_le,hLR'⟩,hLnot⟩,Zb.mpr ⟨by omega,hRN⟩⟩)
  calc P_free.card≤(Lf ×ˢ Icc (c+1) N).card :=
        card_le_card_of_injOn _ hmaps
          (hinj_LR.mono (Finset.coe_subset.mpr ((Zl _ _).trans (Zl _ _))))
    _=Lf.card*(Icc (c+1) N).card:=card_product _ _
    _=(R_s-l_min+1-w_nat)*(N-c):=by rw[hLf_card,Nat.card_Icc];congr 1;omega
 have hpack:=Qq (P:=B_s) hQ_sub (fun S hS=>(hQc S hS).2)
  (Zu hF1_sub hF2_sub) hF_disj_Q
 rw[Zq hF12_disj,hF2_card] at hpack
 have hhit_R:((Qa c B_s Q_c).card:ℝ)+(F1.card:ℝ)+(P_hit.card:ℝ) ≤(m_b:ℝ)*(N:ℝ)-(m_b:ℝ)^2/2:=by
  have h1:((Qa c B_s Q_c).card:ℝ)+((F1.card+P_hit.card:ℕ):ℝ) ≤((Qj N c B_s).card:ℝ):=by exact_mod_cast hpack
  have h2:=Wc N c hc B_s hBs_sub;rw[hBs_card] at h2;push_cast at h1;linarith
 set t:ℝ:=((R_s-l_min:ℕ):ℝ)/(N:ℝ);set w:ℝ:=(w_nat:ℝ)/(N:ℝ)
 have hw_le_span:w_nat≤ span_nat:=by have h0:=Zm hBcov_sub;rw[Nat.card_Icc] at h0;change w_nat≤_ at h0;dsimp only[span_nat];omega
 have hw_le_R:w_nat≤ R_s-l_min+1:=by
  have hBcov_subR:B_cov⊆Icc l_min R_s:=by
   intro x hx;obtain⟨hxB,hxl⟩:=Za.mp hx;obtain⟨i,hi,rfl⟩:=(hBs_eq x).mp hxB
   have:i*d₀≤(m_b-1)*d₀:=Yc d₀ (by omega)
   exact Zb.mpr ⟨hxl,by dsimp only[R_s];omega⟩
  have h0:=Zm hBcov_subR;rw[Nat.card_Icc] at h0;change w_nat≤_ at h0;omega
 have hF1_R:(w*(g+t)-w^2/2)*(N:ℝ)^2-(N:ℝ)≤(F1.card:ℝ):=by
  have h1:(2:ℝ)*(F1.card:ℝ)=((w_nat*(w_nat-1):ℕ):ℝ)+2*(w_nat:ℝ)*((span_nat-w_nat:ℕ):ℝ):=by
   have:((2*F1.card:ℕ):ℝ)=((w_nat*(w_nat-1)+2*w_nat*(span_nat-w_nat):ℕ):ℝ):=by exact_mod_cast hF1_card
   rw[Nat.cast_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_mul] at this;simpa using this
  have hw_sub:(w_nat:ℝ)^2-(w_nat:ℝ)≤((w_nat*(w_nat-1):ℕ):ℝ):=by
   rcases Nat.eq_zero_or_pos w_nat with hw0|hwpos
   ·rw[hw0];simp
   ·rw[Nat.cast_mul,Nat.cast_sub hwpos,Nat.cast_one];nlinarith
  have hsp_eq:(span_nat:ℝ)=((c-R_s:ℕ):ℝ)+((R_s-l_min:ℕ):ℝ):=by
   have:span_nat=(c-R_s)+(R_s-l_min):=by omega
   exact_mod_cast this
  have hsw:((span_nat-w_nat:ℕ):ℝ)=(span_nat:ℝ)-(w_nat:ℝ):=by rw[Nat.cast_sub hw_le_span]
  have hw_leN:(w_nat:ℝ)≤(N:ℝ):=by exact_mod_cast (by omega:w_nat≤ N)
  have halg:(w*(g+t)-w^2/2)*(N:ℝ)^2 =(w_nat:ℝ)*(((c-R_s:ℕ):ℝ)+((R_s-l_min:ℕ):ℝ))-(w_nat:ℝ)^2/2:=by dsimp only[w,g,t];field_simp
  rw[hsw,hsp_eq] at h1;linarith
 have hPfree_R:(P_free.card:ℝ)≤(t-w)*y*(N:ℝ)^2+(N:ℝ):=by
  have h1:(P_free.card:ℝ)≤((R_s-l_min+1-w_nat:ℕ):ℝ)*((N-c:ℕ):ℝ):=by exact_mod_cast hPfree_le
  rw[Nat.cast_sub hw_le_R] at h1;push_cast at h1
  have hNc_le:((N-c:ℕ):ℝ)≤(N:ℝ):=by exact_mod_cast (Nat.sub_le N c)
  have halg:(t-w)*y*(N:ℝ)^2=(((R_s-l_min:ℕ):ℝ)-(w_nat:ℝ))*((N-c:ℕ):ℝ):=by dsimp only[t,w,y];field_simp
  linarith
 have hcore_R:((Qa c B_s Q_c).card:ℝ)+(P1_c.card:ℝ) ≤((mb-mb^2/2)+((t-w)*y-w*(g+t)+w^2/2))*(N:ℝ)^2+3*(N:ℝ):=by
  have hPbdy_R:(P_bdy.card:ℝ)≤(N:ℝ):=by exact_mod_cast hPbdy_le
  have hP1_R:(P1_c.card:ℝ)=(P_bdy.card:ℝ)+(P_hit.card:ℝ)+(P_free.card:ℝ):=by
   have:P1_c.card=P_bdy.card+P_hit.card+P_free.card:=by omega
   exact_mod_cast this
  have halg:(mb-mb^2/2)*(N:ℝ)^2=(m_b:ℝ)*(N:ℝ)-(m_b:ℝ)^2/2:=by dsimp only[mb];field_simp
  linarith
 have hd₀_R:(1:ℝ)≤(d₀:ℝ):=by exact_mod_cast hd₀
 have hg_nn:0≤ g:=div_nonneg (Nat.cast_nonneg _) hN_pos.le;have hy_nn:0≤ y:=div_nonneg (Nat.cast_nonneg _) hN_pos.le;have ht_nn:0≤ t:=div_nonneg (Nat.cast_nonneg _) hN_pos.le;have hw_nn:0≤ w:=div_nonneg (Nat.cast_nonneg _) hN_pos.le
 have hw_le_t1:w≤ t+1/(N:ℝ):=by
  have h1:(w_nat:ℝ)≤((R_s-l_min:ℕ):ℝ)+1:=by exact_mod_cast hw_le_R
  dsimp only[w,t];rw[←add_div];exact div_le_div_of_nonneg_right h1 hN_pos.le
 by_cases hLl:L_s≤ l_min
 ·have hw_ge_td:t/(d₀:ℝ)≤ w:=by
   set q:=(R_s-l_min)/d₀
   have hsub_cov:(range (q+1)).image (fun j=>R_s-j*d₀)⊆B_cov:=by
    intro x hx;obtain⟨j,hj,rfl⟩:=Zi.mp hx;have hjle:j≤ q:=Nat.lt_succ_iff.mp (mem_range.mp hj);have hjd:j*d₀≤ R_s-l_min:=(Yc d₀ hjle).trans (Nat.div_mul_le_self _ _)
    have hjm:j≤ m_b-1:=by
     have:j*d₀≤(m_b-1)*d₀:=by dsimp only[R_s] at hjd;omega
     exact Nat.le_of_mul_le_mul_right this (by omega)
    refine Za.mpr ⟨(hBs_eq _).mpr ⟨m_b-1-j,by omega,?_⟩,by omega⟩
    have:(m_b-1-j)*d₀+j*d₀=(m_b-1)*d₀:=by rw[←Nat.add_mul];congr 1;omega
    dsimp only[R_s];omega
   have hinj_j:Set.InjOn (fun j=>R_s-j*d₀) ((range (q+1)):Set ℕ):=by
    intro j₁ h1 j₂ h2 heq;dsimp only at heq;have h1':j₁*d₀≤ R_s-l_min:=(Yc d₀ (Nat.lt_succ_iff.mp (mem_range.mp (Zc.mp h1)))).trans (Nat.div_mul_le_self _ _);have h2':j₂*d₀≤ R_s-l_min:=(Yc d₀ (Nat.lt_succ_iff.mp (mem_range.mp (Zc.mp h2)))).trans (Nat.div_mul_le_self _ _)
    exact Nat.eq_of_mul_eq_mul_right (by omega:0< d₀) (by omega)
   have hcard_ge:q+1≤ w_nat:=by
    have:=Zm hsub_cov
    rwa[card_image_of_injOn hinj_j,card_range] at this
   have hdiv:R_s-l_min<(q+1)*d₀:=by rw[mul_comm];exact Nat.lt_mul_div_succ _ (by omega)
   have h1R:((R_s-l_min:ℕ):ℝ)≤(w_nat:ℝ)*(d₀:ℝ):=by exact_mod_cast (le_of_lt hdiv).trans (Yc d₀ hcard_ge)
   dsimp only[t,w]
   rw[div_div,div_le_div_iff₀ (by positivity) hN_pos]
   nlinarith
  have hw1:w≤1:=(div_le_one hN_pos).mpr (by exact_mod_cast (by omega:w_nat≤ N))
  have halg:=V2 (d₀:ℝ) (N:ℝ) t w y g mb hd₀_R hN_pos ht_nn hy_nn hg_nn hw1 hw_ge_td hw_le_t1;have hmul:=Zo halg (sq_nonneg (N:ℝ))
  have h1N:(1/(N:ℝ))*(N:ℝ)^2=(N:ℝ):=by field_simp
  have herr:4*(N:ℝ)≤12*(d₀:ℝ)*(N:ℝ):=by nlinarith only[hd₀_R,hN_pos]
  rw[add_mul _ (1/(N:ℝ)),h1N] at hmul;linarith only[hcore_R,hmul,herr]
 ·have hBcov_eq:B_cov=B_s:=by
   ext x;simp only[B_cov,Za,and_iff_left_iff_imp];intro hx;obtain⟨i,-,rfl⟩:=(hBs_eq x).mp hx;omega
  have hw_eq:w=mb:=by dsimp only[w,mb,w_nat];rw[hBcov_eq,hBs_card]
  have ht_ge:(d₀:ℝ)*mb-(d₀:ℝ)/(N:ℝ)≤ t:=by
   have h1:(m_b-1)*d₀≤ R_s-l_min:=by dsimp only[R_s];omega
   have h1R:((m_b-1:ℕ):ℝ)*(d₀:ℝ)≤((R_s-l_min:ℕ):ℝ):=by exact_mod_cast h1
   have h2:=div_le_div_of_nonneg_right h1R hN_pos.le;rw[Nat.cast_sub hmb,Nat.cast_one] at h2;dsimp only[t,mb]
   linarith[show ((m_b:ℝ)-1)*(d₀:ℝ)/(N:ℝ)=(d₀:ℝ)*((m_b:ℝ)/(N:ℝ))-(d₀:ℝ)/(N:ℝ) by ring]
  have ht_le:t≤1-y-g:=by
   have h1:(R_s-l_min)+(c-R_s)+(N-c)≤ N:=by omega
   have h1R:((R_s-l_min:ℕ):ℝ)+((c-R_s:ℕ):ℝ)+((N-c:ℕ):ℝ)≤(N:ℝ):=by exact_mod_cast h1
   dsimp only[t,g,y];have h2:=div_le_div_of_nonneg_right h1R hN_pos.le;rw[div_self hN_pos.ne'] at h2;linarith[add_div ((R_s-l_min:ℕ):ℝ) ((c-R_s:ℕ):ℝ) (N:ℝ),add_div (((R_s-l_min:ℕ):ℝ)+((c-R_s:ℕ):ℝ)) ((N-c:ℕ):ℝ) (N:ℝ)]
  have hmb_nn:0≤ mb:=div_nonneg (Nat.cast_nonneg _) hN_pos.le
  have hmb1:mb≤1:=by
   have:m_b≤ N:=by
    have:B_s.card≤(Icc 1 N).card:=Zm (hBs_sub.trans (Finset.erase_subset _ _))
    rw[hBs_card,Nat.card_Icc] at this;omega
   exact (div_le_one hN_pos).mpr (by exact_mod_cast this)
  rw[hw_eq] at hcore_R;have halg:=V1 (d₀:ℝ) (N:ℝ) t y g mb hd₀_R hN_pos hy_nn hmb_nn hmb1 ht_ge ht_le;have hmul:=Zo halg (sq_nonneg (N:ℝ))
  have hdN:((d₀:ℝ)/(N:ℝ))*(N:ℝ)^2=(d₀:ℝ)*(N:ℝ):=by field_simp
  have herr:3*(N:ℝ)+(d₀:ℝ)*(N:ℝ)≤12*(d₀:ℝ)*(N:ℝ):=by nlinarith only[hd₀_R,hN_pos]
  rw[add_mul _ ((d₀:ℝ)/(N:ℝ)),hdN] at hmul;linarith only[hcore_R,hmul,herr]
private lemma Kb (scale w ua v y m1:ℝ) (hsc:0< scale)
  (hw:0≤ w) (hua:0≤ ua) (hv:v≤ y) (hy1:y≤1)
  (hm1:0≤ m1) (hm1_1:m1≤1) (hw1:w≤1)
  (hpos_case:ua=0\/(m1-1/scale≤ w/\ua+w≤1-y+1/scale)) :
  (ua*v+(43/100:ℝ)*w*v-(285/1000:ℝ)*w^2-(57/100:ℝ)*w*ua)*scale^2 ≤ max ((43/100*y)^2/(114/100)) (y-y^2-(57/100)*m1+(57/200)*m1^2)*scale^2 +3*scale:=by
 have hv_sub:ua*v+(43/100:ℝ)*w*v≤ ua*y+(43/100:ℝ)*w*y:=by nlinarith
 rcases hpos_case with hua0|⟨hW_lb,hua_ub⟩
 ·rw[hua0] at hv_sub ⊢
  have h1:(43/100:ℝ)*w*y-(285/1000:ℝ)*w^2≤(43/100*y)^2/(114/100):=by nlinarith[sq_nonneg (w-(43/57:ℝ)*y)]
  have h2:=h1.trans (Ym _ (y-y^2-(57/100)*m1+(57/200)*m1^2))
  have hmul:=Zo (by linarith :0*v+(43/100:ℝ)*w*v-(285/1000:ℝ)*w^2-(57/100:ℝ)*w*0 ≤ max ((43/100*y)^2/(114/100)) (y-y^2-(57/100)*m1+(57/200)*m1^2)) (sq_nonneg scale)
  linarith
 ·by_cases hcase:y≤(57/100:ℝ)*w
  ·have h1:ua*y+(43/100:ℝ)*w*y-(285/1000:ℝ)*w^2-(57/100:ℝ)*w*ua ≤(43/100:ℝ)*w*y-(285/1000:ℝ)*w^2:=by nlinarith
   have h2:(43/100:ℝ)*w*y-(285/1000:ℝ)*w^2≤(43/100*y)^2/(114/100):=by nlinarith[sq_nonneg (w-(43/57:ℝ)*y)]
   have h3:=(h1.trans h2).trans (Ym _ (y-y^2-(57/100)*m1+(57/200)*m1^2))
   have hmul:=Zo (by linarith :ua*v+(43/100:ℝ)*w*v-(285/1000:ℝ)*w^2-(57/100:ℝ)*w*ua ≤ max ((43/100*y)^2/(114/100)) (y-y^2-(57/100)*m1+(57/200)*m1^2)) (sq_nonneg scale)
   linarith
  ·push Not at hcase
   have h1:ua*(y-(57/100:ℝ)*w)≤(1-y-w+1/scale)*(y-(57/100:ℝ)*w):=by nlinarith
   have h2:(1-y-w+1/scale)*(y-(57/100:ℝ)*w)+(43/100:ℝ)*w*y-(285/1000:ℝ)*w^2 =y-y^2-(57/100:ℝ)*w+(57/200:ℝ)*w^2+(1/scale)*(y-(57/100:ℝ)*w):=by ring
   have h3:(-(57/100:ℝ)*w+(57/200:ℝ)*w^2) -
     (-(57/100:ℝ)*m1+(57/200:ℝ)*m1^2)≤2/scale:=by
    have hdiff:(-(57/100:ℝ)*w+(57/200:ℝ)*w^2) -
      (-(57/100:ℝ)*m1+(57/200:ℝ)*m1^2) =
      (57/200:ℝ)*(m1-w)*(2-w-m1):=by ring
    have h2s:2/scale=2*(1/scale):=by ring
    rw[hdiff]
    rcases le_or_gt (m1-w) 0 with hneg|hpos
    ·have:(57/200:ℝ)*(m1-w)*(2-w-m1)≤0:=by nlinarith
     linarith[show (0:ℝ)≤2/scale by positivity]
    ·have hle:(57/200:ℝ)*(m1-w)*(2-w-m1)≤(57/200:ℝ)*(1/scale)*2:=by
      nlinarith[show (0:ℝ)≤1/scale by positivity]
     linarith[show (0:ℝ)≤1/scale by positivity]
   have h4:(1/scale)*(y-(57/100:ℝ)*w)≤1/scale:=by
    nlinarith[show (0:ℝ)≤1/scale by positivity]
   have h3s:3/scale=1/scale+2/scale:=by ring
   have h5:ua*v+(43/100:ℝ)*w*v-(285/1000:ℝ)*w^2-(57/100:ℝ)*w*ua ≤(y-y^2-(57/100:ℝ)*m1+(57/200:ℝ)*m1^2)+3/scale:=by linarith
   have h6:ua*v+(43/100:ℝ)*w*v-(285/1000:ℝ)*w^2-(57/100:ℝ)*w*ua ≤ max ((43/100*y)^2/(114/100)) (y-y^2-(57/100)*m1+(57/200)*m1^2)+3/scale :=h5.trans (add_le_add (Yn _ _) le_rfl);have hmul:=Zo h6 (sq_nonneg scale)
   have h3eq:(3/scale)*scale^2=3*scale:=by field_simp
   linarith
private lemma Xy (N c L₁ R₁ d:ℕ) (hN:1≤ N) (hc:c∈Icc 1 N)
  (hL1:1≤ L₁) (hLR1:L₁≤ R₁) (hR1c:R₁< c) (hd:d∈Icc 1 N)
  (Pd:Zf (Zf ℕ)) (getU getV:Zf ℕ->ℕ)
  (hUV:∀ A∈Pd,getU A*d< c/\c+getV A*d≤ N ∧
   (∀ x,x∈A↔(∃ i≤ getU A,x=c-i*d)\/(∃ j≤ getV A,x=c+j*d)))
  (hPd_hit:∀ A∈Pd,(A∩Icc L₁ R₁).Nonempty) :
  let uMax:=(Pd.image getU).max.unbotD 0
  let A1:=Icc L₁ R₁
  let Pd1_hit:=Pd.filter (fun A=>1≤ getU A/\1≤ getV A/\Nat.Coprime (getU A) (getV A)/\c-getU A*d∈A1)
  let E_LR_hit:=Pd1_hit.image (fun A=>({c-getU A*d,c+getV A*d}:Zf ℕ))
  let E_L_hit:=(((Icc 1 uMax) ×ˢ (Icc 1 uMax)).filter
   (fun z=>z.1< z.2/\Nat.Coprime z.1 z.2/\(c-z.1*d∈A1\/c-z.2*d∈A1))).image
   (fun z=>({c-z.1*d,c-z.2*d}:Zf ℕ))
  let m1:ℝ:=((R₁-L₁+1:ℕ):ℝ)/(N:ℝ)
  let y:ℝ:=((N-c:ℕ):ℝ)/(N:ℝ)
  (Pd.card:ℝ)≤(E_LR_hit.card:ℝ)+(E_L_hit.card:ℝ) +max ((43/100*y)^2/(114/100)) (y-y^2-(57/100)*m1+(57/200)*m1^2) *((N:ℝ)^2/(d:ℝ)^2) +190*((N:ℝ)/(d:ℝ))*(log (N:ℝ)+2):=by
 intro uMax A1 Pd1_hit E_LR_hit E_L_hit m1 y;have hd1:=(Zb.mp hd).1;have hdN:=(Zb.mp hd).2
 have hd_pos:(0:ℝ)<(d:ℝ):=by exact_mod_cast hd1
 have hN_pos:(0:ℝ)<(N:ℝ):=by exact_mod_cast (by omega:0< N)
 have hlog_nn:0≤ log (N:ℝ):=Real.log_nonneg (by exact_mod_cast hN)
 have hmax_nn:0≤ max ((43/100*y)^2/(114/100)) (y-y^2-(57/100)*m1+(57/200)*m1^2) :=le_trans (by positivity) (Ym _ _)
 rcases Pd.eq_empty_or_nonempty with hPd0|hPdne
 ·rw[hPd0,card_empty,Nat.cast_zero];positivity
 have huMax_ex:1≤ uMax->∃ A∈Pd,getU A=uMax:=by
  intro hu;obtain⟨A,hA,hAmax⟩:=exists_max_image Pd getU hPdne
  have hmax:(Pd.image getU).max=(getU A:WithBot ℕ):=by
   refine le_antisymm ?_ (Finset.le_max (mem_image_of_mem getU hA))
   rw[Finset.max_le_iff];intro x hx;obtain⟨B,hB,rfl⟩:=Zi.mp hx;exact WithBot.coe_le_coe.mpr (hAmax B hB)
  exact⟨A,hA,by simp only[uMax,hmax];rfl⟩
 have huMax_le:∀ A∈Pd,getU A≤ uMax:=by
  intro A hA;obtain⟨B,hB,hBmax⟩:=exists_max_image Pd getU hPdne
  have hmax:(Pd.image getU).max=(getU B:WithBot ℕ):=by
   refine le_antisymm ?_ (Finset.le_max (mem_image_of_mem getU hB))
   rw[Finset.max_le_iff];intro x hx;obtain⟨C,hC,rfl⟩:=Zi.mp hx;exact WithBot.coe_le_coe.mpr (hBmax C hC)
  have:uMax=getU B:=by simp only[uMax,hmax];rfl
  rw[this];exact hBmax A hA
 set Nd:=N/d;have hNd1:1≤ Nd:=Nat.div_pos hdN hd1;have hNd_le:(Nd:ℝ)≤(N:ℝ)/(d:ℝ):=Nat.cast_div_le
 have hlog_Nd:log (Nd:ℝ)≤ log (N:ℝ) :=Real.log_le_log (by exact_mod_cast hNd1) (by exact_mod_cast Nat.div_le_self N d)
 have hlog_Nd_nn:0≤ log (Nd:ℝ):=Real.log_nonneg (by exact_mod_cast hNd1)
 have hcN:=(Zb.mp hc).2
 have hgetU_ge:∀ A∈Pd,c-R₁≤ getU A*d/\1≤ getU A:=by
  intro A hA;obtain⟨huc,-,hAeq⟩:=hUV A hA;obtain⟨z,hz⟩:=hPd_hit A hA;obtain⟨hzA,hzA1⟩:=Zn.mp hz;have hzR:=(Zb.mp hzA1).2
  have h1:c-R₁≤ getU A*d:=by
   rcases (hAeq z).mp hzA with ⟨i,hi,rfl⟩|⟨j,-,rfl⟩
   ·have:=Yc d hi;omega
   ·omega
  have h2:1≤ getU A:=by
   rcases Nat.eq_zero_or_pos (getU A) with h0|hpos
   ·rw[h0,zero_mul] at h1;omega
   ·exact hpos
  exact⟨h1,h2⟩
 have huMax_pos:1≤ uMax:=by obtain⟨A,hA⟩:=hPdne;exact (hgetU_ge A hA).2.trans (huMax_le A hA)
 obtain⟨A_u,hAu_mem,hAu_eq⟩:=huMax_ex huMax_pos
 have huMax_c:uMax*d< c:=by have:=(hUV A_u hAu_mem).1;rwa[hAu_eq] at this
 have huMax_Nd:uMax≤ Nd:=(Nat.le_div_iff_mul_le hd1).mpr (by omega)
 set V:=(N-c)/d;have hV_Nd:V≤ Nd:=Nat.div_le_div_right (Nat.sub_le N c)
 have hV_le:(V:ℝ)≤ y*((N:ℝ)/(d:ℝ)):=by
  have h1:(V:ℝ)≤((N-c:ℕ):ℝ)/(d:ℝ):=Nat.cast_div_le
  dsimp only[y];linarith[show ((N-c:ℕ):ℝ)/(N:ℝ)*((N:ℝ)/(d:ℝ))=((N-c:ℕ):ℝ)/(d:ℝ) by field_simp]
 set u_min:=(c-R₁+d-1)/d
 have hu_min_pos:1≤ u_min:=by
  dsimp only[u_min];exact Nat.div_pos (by omega) hd1
 have hu_min_iff:∀ i:ℕ,i*d< c->(c-i*d≤ R₁↔u_min≤ i):=by
  intro i _
  have h1:c-R₁≤ u_min*d:=by
   have:=Nat.lt_mul_div_succ (c-R₁+d-1) hd1
   have:c-R₁+d-1<(u_min+1)*d:=by rw[mul_comm];exact this
   have:(u_min+1)*d=u_min*d+d:=by ring
   omega
  have h2:(u_min-1)*d< c-R₁:=by
   have:u_min*d≤ c-R₁+d-1:=Nat.div_mul_le_self _ d
   have:u_min*d=(u_min-1)*d+d:=by
    have:=Nat.sub_add_cancel hu_min_pos;conv_lhs=>rw[←this];ring
   omega
  constructor
  ·intro hle
   by_contra hlt
   have:i≤ u_min-1:=by omega
   have:=Yc d this;omega
  ·intro hge
   have:=Yc d hge;omega
 have hu_min_le_uMax:u_min≤ uMax:=by
  have:=(hgetU_ge A_u hAu_mem).1;rw[hAu_eq] at this
  exact (hu_min_iff uMax huMax_c).mp (by omega)
 set u_top:=(c-L₁)/d;set u_end:=min uMax u_top
 have hu_top_iff:∀ i:ℕ,i*d< c->(L₁≤ c-i*d↔i≤ u_top):=by intro i _;dsimp only[u_top];rw[Nat.le_div_iff_mul_le hd1];omega
 have hu_min_le_end:u_min≤ u_end:=by
  obtain⟨z,hz⟩:=hPd_hit A_u hAu_mem;obtain⟨hzA,hzA1⟩:=Zn.mp hz;have hzI:=Zb.mp hzA1
  rcases ((hUV A_u hAu_mem).2.2 z).mp hzA with ⟨i,hi,rfl⟩|⟨j,-,rfl⟩
  ·have hic:i*d< c:=lt_of_le_of_lt (Yc d (by rw[hAu_eq] at hi;exact hi)) huMax_c
   have h1:=(hu_min_iff i hic).mp hzI.2;have h2:=(hu_top_iff i hic).mp hzI.1;rw[hAu_eq] at hi;exact le_min (h1.trans hi) (h1.trans h2)
  ·omega
 set W:=u_end+1-u_min;set U_ab:=uMax-u_end;have hu_end_le1:u_end≤ uMax:=Yp _ _;have hu_end_le2:u_end≤ u_top:=Yq _ _
 have hW_eq:u_min-1+W=u_end:=by dsimp only[W];omega
 have hUab_eq:u_end+U_ab=uMax:=by dsimp only[U_ab];omega
 have hW_pos:1≤ W:=by dsimp only[W];omega
 have hW_Nd:u_min-1+W≤ Nd:=by omega
 have hUab_Nd:u_end+U_ab≤ Nd:=by omega
 have hinj_UV:Set.InjOn (fun A=>(getU A,getV A)) (Pd:Set (Zf ℕ)):=by intro A hA B hB heq;have h1:getU A=getU B:=congrArg Prod.fst heq;have h2:getV A=getV B:=congrArg Prod.snd heq;ext x;rw[(hUV A (Zc.mp hA)).2.2 x,(hUV B (Zc.mp hB)).2.2 x,h1,h2]
 have hELR_eq:E_LR_hit.card=Pd1_hit.card:=by
  refine card_image_of_injOn fun A hA B hB heq=>?_
  obtain⟨hAPd,huA,hvA,-,-⟩:=Za.mp (Zc.mp hA);obtain⟨hBPd,huB,hvB,-,-⟩:=Za.mp (Zc.mp hB);have hucA:=(hUV A hAPd).1;have hucB:=(hUV B hBPd).1
  have h1:c-getU A*d< c:=by have:=Nat.mul_pos huA hd1;omega
  have h2:c< c+getV A*d:=by have:=Nat.mul_pos hvA hd1;omega
  have h3:c-getU B*d< c:=by have:=Nat.mul_pos huB hd1;omega
  have h4:c< c+getV B*d:=by have:=Nat.mul_pos hvB hd1;omega
  have hm1:c-getU A*d∈({c-getU B*d,c+getV B*d}:Zf ℕ):=by rw[←heq];simp
  have hm2:c+getV A*d∈({c-getU B*d,c+getV B*d}:Zf ℕ):=by rw[←heq];simp
  simp only[Zx,Zj] at hm1 hm2
  have hu_eq:getU A=getU B:=Nat.eq_of_mul_eq_mul_right hd1 (by omega)
  have hv_eq:getV A=getV B:=Nat.eq_of_mul_eq_mul_right hd1 (by omega)
  exact hinj_UV (Zc.mpr hAPd) (Zc.mpr hBPd) (Prod.ext hu_eq hv_eq)
 set Pd_v0:=Pd.filter (fun A=>getV A=0)
 set Pd_nc:=Pd.filter (fun A=>u_min≤ getU A/\getU A≤ u_end/\1≤ getV A/\¬ Nat.Coprime (getU A) (getV A))
 set Pd_ab:=Pd.filter (fun A=>u_end< getU A/\1≤ getV A)
 have hPd_cov:Pd⊆Pd1_hit∪Pd_v0∪Pd_nc∪Pd_ab:=by
  intro A hA;have hge:=hgetU_ge A hA;have huc:=(hUV A hA).1
  have hu_lo:u_min≤ getU A:=(hu_min_iff (getU A) huc).mp (by omega)
  by_cases hv0:getV A=0
  ·exact Ze _ (Ze _ (Zg _ (Za.mpr ⟨hA,hv0⟩)))
  ·by_cases hab:u_end< getU A
   ·exact Zg _ (Za.mpr ⟨hA,hab,by omega⟩)
   ·by_cases hcop:Nat.Coprime (getU A) (getV A)
    ·refine Ze _ (Ze _ (Ze _
      (Za.mpr ⟨hA,hge.2,by omega,hcop,Zb.mpr ⟨?_,by omega⟩⟩)))
     have:getU A≤ u_top:=by omega
     exact (hu_top_iff (getU A) huc).mpr this
    ·exact Ze _ (Zg _
      (Za.mpr ⟨hA,hu_lo,by omega,by omega,hcop⟩))
 have hPdv0_le:Pd_v0.card≤ Nd+1:=by
  have hmaps:Set.MapsTo (fun A=>(getU A,getV A)) (Pd_v0:Set (Zf ℕ))
    (((Icc 0 Nd) ×ˢ {0}:Zf (ℕ × ℕ)):Set (ℕ × ℕ)):=by
   intro A hA;dsimp only;obtain⟨hAPd,hv0⟩:=Za.mp (Zc.mp hA)
   exact Zc.mpr (Zh.mpr
    ⟨Zb.mpr ⟨Nat.zero_le _,(huMax_le A hAPd).trans huMax_Nd⟩,Zj.mpr hv0⟩)
  exact (card_le_card_of_injOn _ hmaps (hinj_UV.mono (Finset.coe_subset.mpr (Zl _ _)))).trans
   (by simp[Nat.card_Icc])
 have hPdab_le:Pd_ab.card≤ U_ab*V:=by
  have hmaps:Set.MapsTo (fun A=>(getU A,getV A)) (Pd_ab:Set (Zf ℕ))
    (((Icc (u_end+1) uMax) ×ˢ (Icc 1 V):Zf (ℕ × ℕ)):Set (ℕ × ℕ)):=by
   intro A hA;dsimp only;obtain⟨hAPd,hu_gt,hv1⟩:=Za.mp (Zc.mp hA)
   have hv_le:getV A≤ V:=(Nat.le_div_iff_mul_le hd1).mpr (by have:=(hUV A hAPd).2.1;omega)
   exact Zc.mpr (Zh.mpr
    ⟨Zb.mpr ⟨by omega,huMax_le A hAPd⟩,Zb.mpr ⟨hv1,hv_le⟩⟩)
  exact (card_le_card_of_injOn _ hmaps (hinj_UV.mono (Finset.coe_subset.mpr (Zl _ _)))).trans
   (by rw[card_product,Nat.card_Icc,Nat.card_Icc,show uMax+1-(u_end+1)=U_ab by omega];simp)
 have hPdnc_le:(Pd_nc.card:ℝ)≤(43/100:ℝ)*(W:ℝ)*(V:ℝ) +50*(Nd:ℝ)*(log (Nd:ℝ)+2):=by
  let Box:=((Icc ((u_min-1)+1) ((u_min-1)+W)) ×ˢ (Icc (0+1) (0+V))).filter
   (fun z=>1< Nat.gcd z.1 z.2)
  have hmaps:Set.MapsTo (fun A=>(getU A,getV A)) (Pd_nc:Set (Zf ℕ)) (Box:Set (ℕ × ℕ)):=by
   intro A hA;dsimp only;obtain⟨hAPd,hu1,hu2,hv1,hnc⟩:=Za.mp (Zc.mp hA)
   have hv_le:getV A≤ V:=(Nat.le_div_iff_mul_le hd1).mpr (by have:=(hUV A hAPd).2.1;omega)
   have hgpos:0< Nat.gcd (getU A) (getV A):=Nat.gcd_pos_of_pos_left _ (by omega)
   refine Zc.mpr (Za.mpr ⟨Zh.mpr
    ⟨Zb.mpr ⟨by omega,by omega⟩,Zb.mpr ⟨by omega,by omega⟩⟩,?_⟩)
   dsimp only;rw[Nat.Coprime] at hnc;omega
  have hle:(Pd_nc.card:ℝ)≤(Box.card:ℝ):=by exact_mod_cast card_le_card_of_injOn _ hmaps (hinj_UV.mono (Finset.coe_subset.mpr (Zl _ _)))
  exact hle.trans (Wt Nd (u_min-1) W 0 V hNd1 hW_Nd (by omega))
 have hEL_ge:(285/1000:ℝ)*(W:ℝ)^2+(57/100:ℝ)*(W:ℝ)*(U_ab:ℝ) -
   76*(Nd:ℝ)*(log (Nd:ℝ)+2)≤(E_L_hit.card:ℝ):=by
  let S_all:=((Icc 1 uMax) ×ˢ (Icc 1 uMax)).filter
   (fun z=>z.1< z.2/\Nat.Coprime z.1 z.2/\(c-z.1*d∈A1\/c-z.2*d∈A1))
  have hinjL:Set.InjOn (fun z:ℕ × ℕ=>({c-z.1*d,c-z.2*d}:Zf ℕ)) (S_all:Set (ℕ × ℕ)):=by
   intro ⟨i₁,j₁⟩ h1 ⟨i₂,j₂⟩ h2 heq;dsimp only at heq;obtain⟨hP1,hlt1,-⟩:=Za.mp (Zc.mp h1);obtain⟨hP2,hlt2,-⟩:=Za.mp (Zc.mp h2);dsimp only at hlt1 hlt2;have hj1:j₁*d< c:=lt_of_le_of_lt (Yc d (Zb.mp (Zh.mp hP1).2).2) huMax_c;have hj2:j₂*d< c:=lt_of_le_of_lt (Yc d (Zb.mp (Zh.mp hP2).2).2) huMax_c;have hi1:i₁*d< j₁*d:=Nat.mul_lt_mul_of_pos_right hlt1 hd1;have hi2:i₂*d< j₂*d:=Nat.mul_lt_mul_of_pos_right hlt2 hd1
   have hm1:c-i₁*d∈({c-i₂*d,c-j₂*d}:Zf ℕ):=by rw[←heq];simp
   have hm2:c-j₁*d∈({c-i₂*d,c-j₂*d}:Zf ℕ):=by rw[←heq];simp
   simp only[Zx,Zj] at hm1 hm2
   ext <;> dsimp
   ·exact Nat.eq_of_mul_eq_mul_right hd1 (by omega)
   ·exact Nat.eq_of_mul_eq_mul_right hd1 (by omega)
  have hEL_eq:E_L_hit.card=S_all.card:=card_image_of_injOn hinjL
  let T1:=((Icc ((u_min-1)+1) ((u_min-1)+W)) ×ˢ (Icc ((u_min-1)+1) ((u_min-1)+W))).filter
   (fun z=>z.1< z.2/\Nat.gcd z.1 z.2=1)
  let T2:=((Icc ((u_min-1)+1) ((u_min-1)+W)) ×ˢ (Icc (u_end+1) (u_end+U_ab))).filter
   (fun z=>Nat.gcd z.1 z.2=1)
  have hT1_sub:T1⊆S_all:=by
   intro ⟨i,j⟩ hz;obtain⟨hP,hlt,hg⟩:=Za.mp hz;obtain⟨hi,hj⟩:=Zh.mp hP;have hiI:=Zb.mp hi;have hjI:=Zb.mp hj
   have hic:i*d< c:=lt_of_le_of_lt (Yc d (by omega:i≤ uMax)) huMax_c
   have hiA1:c-i*d∈A1:=Zb.mpr
    ⟨(hu_top_iff i hic).mpr (by omega),(hu_min_iff i hic).mpr (by omega)⟩
   exact Za.mpr ⟨Zh.mpr
    ⟨Zb.mpr ⟨by omega,by omega⟩,Zb.mpr ⟨by omega,by omega⟩⟩,hlt,hg,Or.inl hiA1⟩
  have hT2_sub:T2⊆S_all:=by
   intro ⟨i,j⟩ hz;obtain⟨hP,hg⟩:=Za.mp hz;obtain⟨hi,hj⟩:=Zh.mp hP;have hiI:=Zb.mp hi;have hjI:=Zb.mp hj
   have hic:i*d< c:=lt_of_le_of_lt (Yc d (by omega:i≤ uMax)) huMax_c
   have hiA1:c-i*d∈A1:=Zb.mpr
    ⟨(hu_top_iff i hic).mpr (by omega),(hu_min_iff i hic).mpr (by omega)⟩
   exact Za.mpr ⟨Zh.mpr
    ⟨Zb.mpr ⟨by omega,by omega⟩,Zb.mpr ⟨by omega,by omega⟩⟩,by omega,hg,Or.inl hiA1⟩
  have hT12_disj:Disjoint T1 T2:=by rw[Zk];intro ⟨i,j⟩ h1 h2;have h1':=(Zb.mp (Zh.mp (Za.mp h1).1).2).2;have h2':=(Zb.mp (Zh.mp (Za.mp h2).1).2).1;omega
  have hcard_ge:T1.card+T2.card≤ E_L_hit.card:=by rw[hEL_eq,←Zq hT12_disj];exact Zm (Zu hT1_sub hT2_sub)
  have hT1_ge:=W5 Nd (u_min-1) W hNd1 hW_Nd;have hT2_ge:=Xt Nd (u_min-1) W u_end U_ab hNd1 hW_Nd hUab_Nd
  have hcardR:(T1.card:ℝ)+(T2.card:ℝ)≤(E_L_hit.card:ℝ):=by exact_mod_cast hcard_ge
  linarith
 have hPd_nat:Pd.card≤ Pd1_hit.card+Pd_v0.card+Pd_nc.card+Pd_ab.card:=by have h1:=(Zm hPd_cov).trans (Yh _ _);have h2:=Yh (Pd1_hit∪Pd_v0) Pd_nc;have h3:=Yh Pd1_hit Pd_v0;omega
 have hPd_R:(Pd.card:ℝ)≤(E_LR_hit.card:ℝ)+(Pd_v0.card:ℝ)+(Pd_nc.card:ℝ)+(Pd_ab.card:ℝ):=by rw[hELR_eq];exact_mod_cast hPd_nat
 have hPdv0_R:(Pd_v0.card:ℝ)≤(Nd:ℝ)+1:=by exact_mod_cast hPdv0_le
 have hPdab_R:(Pd_ab.card:ℝ)≤(U_ab:ℝ)*(V:ℝ):=by exact_mod_cast hPdab_le
 set scale:ℝ:=(N:ℝ)/(d:ℝ);have hsc_pos:0< scale:=div_pos hN_pos hd_pos;have hsc_sq:scale^2=(N:ℝ)^2/(d:ℝ)^2:=div_pow _ _ 2
 have hquad_bd:(U_ab:ℝ)*(V:ℝ)+(43/100:ℝ)*(W:ℝ)*(V:ℝ) -
   (285/1000:ℝ)*(W:ℝ)^2-(57/100:ℝ)*(W:ℝ)*(U_ab:ℝ) ≤
   max ((43/100*y)^2/(114/100)) (y-y^2-(57/100)*m1+(57/200)*m1^2)*scale^2 +3*scale:=by
  set w:ℝ:=(W:ℝ)/scale;set ua:ℝ:=(U_ab:ℝ)/scale;set v:ℝ:=(V:ℝ)/scale
  have hrew:(U_ab:ℝ)*(V:ℝ)+(43/100:ℝ)*(W:ℝ)*(V:ℝ) -
    (285/1000:ℝ)*(W:ℝ)^2-(57/100:ℝ)*(W:ℝ)*(U_ab:ℝ) =
    (ua*v+(43/100:ℝ)*w*v-(285/1000:ℝ)*w^2-(57/100:ℝ)*w*ua)*scale^2:=by
   dsimp only[w,ua,v];field_simp
  rw[hrew];have hw_nn:0≤ w:=div_nonneg (Nat.cast_nonneg _) hsc_pos.le;have hua_nn:0≤ ua:=div_nonneg (Nat.cast_nonneg _) hsc_pos.le;have hv_le:v≤ y:=(div_le_iff₀ hsc_pos).mpr hV_le
  have hy_le1:y≤1:=(div_le_one hN_pos).mpr (by exact_mod_cast (Nat.sub_le N c))
  have hm1_nn:0≤ m1:=div_nonneg (Nat.cast_nonneg _) hN_pos.le
  have hm1_le1:m1≤1:=(div_le_one hN_pos).mpr (by exact_mod_cast (by omega:R₁-L₁+1≤ N))
  have hw_le1:w≤1:=(div_le_one hsc_pos).mpr ((by exact_mod_cast (by omega:W≤ Nd):(W:ℝ)≤(Nd:ℝ)).trans hNd_le)
  refine Kb scale w ua v y m1 hsc_pos hw_nn hua_nn hv_le hy_le1 hm1_nn hm1_le1 hw_le1 ?_
  rcases Nat.eq_zero_or_pos U_ab with huab0|huab_pos
  ·left;dsimp only[ua];rw[huab0,Nat.cast_zero,zero_div]
  ·right
   have hu_end_eq:u_end=u_top:=by
    dsimp only[u_end]
    exact Yj (by dsimp only[U_ab,u_end] at huab_pos;omega)
   have hWd_ge:R₁-L₁+1≤(W+1)*d:=by
    have h1:(u_min-1)*d< c-R₁:=by
     have:u_min*d≤ c-R₁+d-1:=Nat.div_mul_le_self _ d
     have:u_min*d=(u_min-1)*d+d:=by
      have:=Nat.sub_add_cancel hu_min_pos;conv_lhs=>rw[←this];ring
     omega
    have h2:c-L₁<(u_top+1)*d:=by rw[mul_comm];exact Nat.lt_mul_div_succ (c-L₁) hd1
    have h3:(W+1)*d+(u_min-1)*d=(u_top+1)*d:=by rw[←Nat.add_mul];congr 1;omega
    omega
   have hW_lb:m1-1/scale≤ w:=by
    have h1R:((R₁-L₁+1:ℕ):ℝ)≤((W:ℝ)+1)*(d:ℝ):=by exact_mod_cast hWd_ge
    dsimp only[m1,w,scale];rw[one_div_div,div_div_eq_mul_div,←sub_div]
    exact div_le_div_of_nonneg_right (by linarith only[h1R]) hN_pos.le
   have hua_ub:ua+w≤1-y+1/scale:=by
    have h1:(W+U_ab-1)*d< c:=by
     have heq:W+U_ab-1=uMax-u_min:=by omega
     rw[heq]
     have:(uMax-u_min)*d≤ uMax*d:=Yc d (Nat.sub_le _ _)
     omega
    have h1R:((W:ℝ)+(U_ab:ℝ)-1)*(d:ℝ)≤(c:ℝ):=by
     have:((W+U_ab-1:ℕ):ℝ)*(d:ℝ)≤(c:ℝ):=by exact_mod_cast le_of_lt h1
     rw[Nat.cast_sub (by omega:1≤ W+U_ab),Nat.cast_add,Nat.cast_one] at this;exact this
    have hc_eq:(c:ℝ)/(N:ℝ)=1-y:=by dsimp only[y];rw[Nat.cast_sub hcN,sub_div,div_self hN_pos.ne'];ring
    dsimp only[ua,w,scale];rw[div_div_eq_mul_div,div_div_eq_mul_div,one_div_div];have h2:=div_le_div_of_nonneg_right h1R hN_pos.le
    have h3:((W:ℝ)+(U_ab:ℝ)-1)*(d:ℝ)/(N:ℝ) =(U_ab:ℝ)*(d:ℝ)/(N:ℝ)+(W:ℝ)*(d:ℝ)/(N:ℝ)-(d:ℝ)/(N:ℝ):=by ring
    linarith only[h2,h3,hc_eq]
   exact⟨hW_lb,hua_ub⟩
 have hNd_log:(Nd:ℝ)*(log (Nd:ℝ)+2)≤((N:ℝ)/(d:ℝ))*(log (N:ℝ)+2):=by
  calc (Nd:ℝ)*(log (Nd:ℝ)+2)
      ≤ (Nd:ℝ)*(log (N:ℝ)+2):=Zp (by linarith only[hlog_Nd]) (Nat.cast_nonneg _)
    _≤((N:ℝ)/(d:ℝ))*(log (N:ℝ)+2):=Zo hNd_le (by linarith only[hlog_nn])
 have hNd1R:(1:ℝ)≤(Nd:ℝ):=by exact_mod_cast hNd1
 rw[hsc_sq] at hquad_bd;dsimp only[scale] at hquad_bd
 have herr_N:(Nd:ℝ)+1+3*((N:ℝ)/(d:ℝ))≤5*((N:ℝ)/(d:ℝ))*(log (N:ℝ)+2):=by
  have hlog2:(2:ℝ)≤ log (N:ℝ)+2:=by linarith only[hlog_nn]
  nlinarith only[hNd_le,hNd1R,hlog2]
 have hlog_pos:0≤((N:ℝ)/(d:ℝ))*(log (N:ℝ)+2) :=mul_nonneg (div_nonneg hN_pos.le hd_pos.le) (by linarith only[hlog_nn])
 linarith only[hPd_R,hPdv0_R,hPdnc_le,hPdab_R,hEL_ge,hquad_bd,hNd_log,herr_N,hlog_pos]
lemma Vl (N c L₁ R₁:ℕ) (hN:1≤ N) (hc:c∈Icc 1 N)
  (hL1:1≤ L₁) (hLR1:L₁≤ R₁) (hR1c:R₁< c) (mod2:Bool)
  (P_c Q_c:Zf (Zf ℕ))
  (hF:Zt N (P_c∪Q_c))
  (hdisj:Disjoint P_c Q_c)
  (hPc:∀ A∈P_c,IsAP A/\2≤ A.card/\c∈A)
  (hPc_hit:∀ A∈P_c,(A∩Icc L₁ R₁).Nonempty)
  (hPc_odd:mod2=true->∀ A∈P_c,Odd (apStep A))
  (hQc:∀ S∈Q_c,¬ IsAP S/\c∈S) :
  let A1:=Icc L₁ R₁
  let m1:ℝ:=((R₁-L₁+1:ℕ):ℝ)/(N:ℝ)
  let y:ℝ:=((N-c:ℕ):ℝ)/(N:ℝ)
  let S_pc:ℝ:=if mod2 then 1235/1000 else 1645/1000
  ((Qa c A1 Q_c).card:ℝ)+(P_c.card:ℝ) ≤((m1-m1^2/2) +max ((43/100*y)^2/(114/100)) (y-y^2-(57/100)*m1+(57/200)*m1^2)*S_pc) *(N:ℝ)^2 +250*(N:ℝ)*(log (N:ℝ)+2)^2:=by
 classical
 intro A1 m1 y S_pc
 have hN_pos:(0:ℝ)<(N:ℝ):=by exact_mod_cast (by omega:0< N)
 have hcN:=(Zb.mp hc).2
 have hA1_sub:A1⊆(Icc 1 N).erase c:=fun x hx =>
  Zw.mpr ⟨by have:=(Zb.mp hx).2;omega,Zb.mpr ⟨by have:=(Zb.mp hx).1;omega,by have:=(Zb.mp hx).2;omega⟩⟩
 have hA1_card:A1.card=R₁-L₁+1:=by rw[Nat.card_Icc];omega
 have hQ_sub:Zt N Q_c :=⟨(Zs (s₁:=P_c)).trans hF.1,fun S hS T hT hST =>
   hF.2 (Zc.mpr (Zg _ (Zc.mp hS)))
    (Zc.mpr (Zg _ (Zc.mp hT))) hST⟩
 have hUV_ex:∀ A∈P_c,∃ u v:ℕ,u*apStep A< c/\c+v*apStep A≤ N ∧
   (∀ x,x∈A↔(∃ i≤ u,x=c-i*apStep A)\/(∃ j≤ v,x=c+j*apStep A)) :=
  fun A hA=>W0 (Zy.mp (hF.1 (Ze _ hA)))
   (hPc A hA).1 (hPc A hA).2.1 (hPc A hA).2.2
 let getU:Zf ℕ->ℕ:=fun A=>if hA:A∈P_c then (hUV_ex A hA).choose else 0
 let getV:Zf ℕ->ℕ:=fun A=>if hA:A∈P_c then (hUV_ex A hA).choose_spec.choose else 0
 have hUV:∀ A∈P_c,getU A*apStep A< c/\c+getV A*apStep A≤ N ∧
   (∀ x,x∈A↔(∃ i≤ getU A,x=c-i*apStep A)\/(∃ j≤ getV A,x=c+j*apStep A)):=by
  intro A hA;simpa only [getU,getV,dif_pos hA] using (hUV_ex A hA).choose_spec.choose_spec
 let Pd:ℕ->Zf (Zf ℕ):=fun d=>P_c.filter (fun A=>apStep A=d)
 let uMax:ℕ->ℕ:=fun d=>((Pd d).image getU).max.unbotD 0
 let Pd1_hit:ℕ->Zf (Zf ℕ):=fun d =>
  (Pd d).filter (fun A=>1≤ getU A/\1≤ getV A/\Nat.Coprime (getU A) (getV A)/\c-getU A*d∈A1)
 let E_LR_hit:ℕ->Zf (Zf ℕ):=fun d =>
  (Pd1_hit d).image (fun A=>({c-getU A*d,c+getV A*d}:Zf ℕ))
 let E_L_hit:ℕ->Zf (Zf ℕ):=fun d =>
  (((Icc 1 (uMax d)) ×ˢ (Icc 1 (uMax d))).filter
   (fun z=>z.1< z.2/\Nat.Coprime z.1 z.2/\(c-z.1*d∈A1\/c-z.2*d∈A1))).image
   (fun z=>({c-z.1*d,c-z.2*d}:Zf ℕ))
 let Ed:ℕ->Zf (Zf ℕ):=fun d=>E_LR_hit d∪E_L_hit d
 have huMax_ex:∀ d,1≤ uMax d->∃ A∈Pd d,getU A=uMax d:=by
  intro d hu
  rcases (Pd d).eq_empty_or_nonempty with hemp|hne
  ·exfalso;simp[uMax,hemp] at hu
  ·obtain⟨A,hA,hAmax⟩:=exists_max_image (Pd d) getU hne
   have hmax:((Pd d).image getU).max=(getU A:WithBot ℕ):=by
    refine le_antisymm ?_ (Finset.le_max (mem_image_of_mem getU hA))
    rw[Finset.max_le_iff];intro x hx;obtain⟨B,hB,rfl⟩:=Zi.mp hx;exact WithBot.coe_le_coe.mpr (hAmax B hB)
   exact⟨A,hA,by simp only[uMax,hmax];rfl⟩
 have hELR_prop:∀ d∈Icc 1 N,∀ e∈E_LR_hit d,e∈Qj N c A1/\(∃ A∈Pd d,e⊆A) ∧
   ∃ x y,e={x,y}/\x< c/\c< y/\Nat.gcd (c-x) (y-c)=d:=by
  intro d hd e he;have hd1:=(Zb.mp hd).1;obtain⟨A,hA1,rfl⟩:=Zi.mp he;obtain⟨hAPd,hu1,hv1,hcop,hA1m⟩:=Za.mp hA1;obtain⟨hAPc,hAd⟩:=Za.mp hAPd;obtain⟨huc,hvN,hAeq⟩:=hUV A hAPc;rw[hAd] at huc hvN hAeq
  have hlt1:c-getU A*d< c:=by have:=Nat.mul_pos hu1 hd1;omega
  have hlt2:c< c+getV A*d:=by have:=Nat.mul_pos hv1 hd1;omega
  have hsubA:({c-getU A*d,c+getV A*d}:Zf ℕ)⊆A:=by
   intro z hz;simp only[Zx,Zj] at hz
   rcases hz with rfl|rfl
   ·exact (hAeq _).mpr (Or.inl ⟨getU A,le_rfl,rfl⟩)
   ·exact (hAeq _).mpr (Or.inr ⟨getV A,le_rfl,rfl⟩)
  refine⟨Za.mpr ⟨Zz.mpr ⟨fun z hz=>Zw.mpr
   ⟨by simp only[Zx,Zj] at hz;rcases hz with rfl|rfl <;> omega,Zy.mp (hF.1 (Ze _ hAPc)) (hsubA hz)⟩,
   by rw[card_insert_of_notMem (Finset.notMem_singleton.mpr (by omega)),card_singleton]⟩,
   ⟨c-getU A*d,Zn.mpr ⟨by simp,hA1m⟩⟩⟩,
   ⟨A,hAPd,hsubA⟩,c-getU A*d,c+getV A*d,rfl,hlt1,hlt2,?_⟩
  have h1:c-(c-getU A*d)=getU A*d:=by omega
  have h2:c+getV A*d-c=getV A*d:=by omega
  rw[h1,h2,Nat.gcd_mul_right,hcop.gcd_eq_one,one_mul]
 have hEL_prop:∀ d∈Icc 1 N,∀ e∈E_L_hit d,e∈Qj N c A1/\(∃ A∈Pd d,e⊆A) ∧
   ∃ x y,e={x,y}/\x< c/\y< c/\x≠y/\Nat.gcd (c-x) (c-y)=d:=by
  intro d hd e he;have hd1:=(Zb.mp hd).1;obtain⟨⟨i,j⟩,hij,rfl⟩:=Zi.mp he;obtain⟨hijP,hiltj,hcop,hhitA1⟩:=Za.mp hij;dsimp only at hiltj hcop hhitA1 ⊢;obtain⟨hi,hj⟩:=Zh.mp hijP;dsimp only at hi hj;have hi1:=(Zb.mp hi).1;have hj_le:=(Zb.mp hj).2;have hi_le:=(Zb.mp hi).2
  obtain⟨A,hAPd,hAu⟩:=huMax_ex d (by omega)
  obtain⟨hAPc,hAd⟩:=Za.mp hAPd;obtain⟨huc,-,hAeq⟩:=hUV A hAPc;rw[hAd,hAu] at huc hAeq;have hi_lt:i*d< c:=lt_of_le_of_lt (Yc d hi_le) huc;have hj_lt:j*d< c:=lt_of_le_of_lt (Yc d hj_le) huc
  have hlt1:c-i*d< c:=by have:=Nat.mul_pos hi1 hd1;omega
  have hlt2:c-j*d< c:=by have:=Nat.mul_pos (by omega:0< j) hd1;omega
  have hne:c-i*d≠c-j*d:=by have:=Nat.mul_lt_mul_of_pos_right hiltj hd1;omega
  have hsubA:({c-i*d,c-j*d}:Zf ℕ)⊆A:=by
   intro z hz;simp only[Zx,Zj] at hz
   rcases hz with rfl|rfl
   ·exact (hAeq _).mpr (Or.inl ⟨i,hi_le,rfl⟩)
   ·exact (hAeq _).mpr (Or.inl ⟨j,hj_le,rfl⟩)
  refine⟨Za.mpr ⟨Zz.mpr ⟨fun z hz=>Zw.mpr
   ⟨by simp only[Zx,Zj] at hz;rcases hz with rfl|rfl <;> omega,Zy.mp (hF.1 (Ze _ hAPc)) (hsubA hz)⟩,
   by rw[card_insert_of_notMem (Finset.notMem_singleton.mpr hne),card_singleton]⟩,
   hhitA1.elim (fun h1=>⟨c-i*d,Zn.mpr ⟨by simp,h1⟩⟩)
    (fun h2=>⟨c-j*d,Zn.mpr ⟨by simp,h2⟩⟩)⟩,
   ⟨A,hAPd,hsubA⟩,c-i*d,c-j*d,rfl,hlt1,hlt2,hne,?_⟩
  have h1:c-(c-i*d)=i*d:=by omega
  have h2:c-(c-j*d)=j*d:=by omega
  rw[h1,h2,Nat.gcd_mul_right,hcop.gcd_eq_one,one_mul]
 have hEd_card:∀ d∈Icc 1 N,(Ed d).card=(E_LR_hit d).card+(E_L_hit d).card:=by
  intro d hd
  refine Zq ?_
  rw[Zk];intro e h1 h2;obtain⟨-,-,x₁,y₁,he1,-,hy1,-⟩:=hELR_prop d hd e h1;obtain⟨-,-,x₂,y₂,he2,hx2,hy2,-⟩:=hEL_prop d hd e h2
  have:y₁∈({x₂,y₂}:Zf ℕ):=by rw[←he2,he1];simp
  simp only[Zx,Zj] at this;omega
 have hEd_disj:Set.PairwiseDisjoint ((Icc 1 N):Set ℕ) Ed:=by
  intro d₁ hd₁ d₂ hd₂ hne;simp only[Function.onFun];rw[Zk];intro e he1 he2
  have hgcd:∀ d∈Icc 1 N,e∈Ed d →
    ∀ x y,e={x,y}->x≠y->Nat.gcd (max c x-min c x) (max c y-min c y)=d:=by
   intro d hd he x y hxy _
   rcases Zd.mp he with h1|h2
   ·obtain⟨-,-,a,b,heq,ha,hb,hg⟩:=hELR_prop d hd e h1
    have hax:a∈({x,y}:Zf ℕ):=by rw[←hxy,heq];simp
    have hbx:b∈({x,y}:Zf ℕ):=by rw[←hxy,heq];simp
    simp only[Zx,Zj] at hax hbx
    rcases hax with rfl|rfl <;> rcases hbx with rfl|rfl
    ·omega
    ·rw[Yk ha.le,Yj ha.le,Yi hb.le,Yl hb.le];exact hg
    ·rw[Yi hb.le,Yl hb.le,Yk ha.le,Yj ha.le,Nat.gcd_comm];exact hg
    ·omega
   ·obtain⟨-,-,a,b,heq,ha,hb,hnab,hg⟩:=hEL_prop d hd e h2
    have hax:a∈({x,y}:Zf ℕ):=by rw[←hxy,heq];simp
    have hbx:b∈({x,y}:Zf ℕ):=by rw[←hxy,heq];simp
    simp only[Zx,Zj] at hax hbx
    rcases hax with rfl|rfl <;> rcases hbx with rfl|rfl
    ·exact absurd rfl hnab
    ·rw[Yk ha.le,Yj ha.le,Yk hb.le,Yj hb.le];exact hg
    ·rw[Yk hb.le,Yj hb.le,Yk ha.le,Yj ha.le,Nat.gcd_comm];exact hg
    ·exact absurd rfl hnab
  have he_mem:e∈Qj N c A1:=by
   rcases Zd.mp he1 with h1|h2
   ·exact (hELR_prop d₁ (Zc.mp hd₁) e h1).1
   ·exact (hEL_prop d₁ (Zc.mp hd₁) e h2).1
  obtain⟨x,y,hnexy,hxy⟩:=card_eq_two.mp (Zz.mp (Za.mp he_mem).1).2
  exact hne ((hgcd d₁ (Zc.mp hd₁) he1 x y hxy hnexy).symm.trans
   (hgcd d₂ (Zc.mp hd₂) he2 x y hxy hnexy))
 set Dset:Zf ℕ:=if mod2 then (Icc 1 N).filter Odd else Icc 1 N
 have hDset_sub:Dset⊆Icc 1 N:=by dsimp only[Dset];split_ifs;exact Zl _ _;exact Subset.rfl
 let Forbid:=Dset.biUnion Ed
 have hF_sub:Forbid⊆Qj N c A1:=by
  refine biUnion_subset.mpr fun d hd e he=>?_
  rcases Zd.mp he with h1|h2
  ·exact (hELR_prop d (hDset_sub hd) e h1).1
  ·exact (hEL_prop d (hDset_sub hd) e h2).1
 have hF_disj:∀ S∈Q_c,Disjoint (Qs c S) Forbid:=by
  intro S hSQ;rw[Zk];intro e heS heF;obtain⟨d,hd,heEd⟩:=mem_biUnion.mp heF
  have hexA:∃ A∈Pd d,e⊆A:=by
   rcases Zd.mp heEd with h1|h2
   ·exact (hELR_prop d (hDset_sub hd) e h1).2.1
   ·exact (hEL_prop d (hDset_sub hd) e h2).2.1
  obtain⟨A,hAPd,hsubA⟩:=hexA;have hAPc:=(Za.mp hAPd).1
  have hSA:S≠A:=fun h=>Zk.mp hdisj hAPc (h ▸ hSQ)
  exact Qt hF (Zg _ hSQ) (Ze _ hAPc)
   hSA (hPc A hAPc).2.2 heS hsubA
 have hpack:=Qq (P:=A1) hQ_sub (fun S hS=>(hQc S hS).2) hF_sub hF_disj
 have hForb_card:Forbid.card=∑ d∈Dset,((E_LR_hit d).card+(E_L_hit d).card):=by
  rw[card_biUnion (hEd_disj.subset (Finset.coe_subset.mpr hDset_sub))]
  exact Finset.sum_congr rfl fun d hd=>hEd_card d (hDset_sub hd)
 have hPc_part:P_c.card=∑ d∈Dset,(Pd d).card:=by
  rw[←card_biUnion]
  ·congr 1;ext A;simp only[Pd,mem_biUnion,Za]
   constructor
   ·intro hA
    have hsp:=Qg (Zy.mp (hF.1 (Ze _ hA))) (hPc A hA).1 (hPc A hA).2.1
    refine⟨apStep A,?_,hA,rfl⟩
    dsimp only[Dset];split_ifs with hm
    ·exact Za.mpr ⟨Zb.mpr ⟨hsp.1,hsp.2.1⟩,hPc_odd hm A hA⟩
    ·exact Zb.mpr ⟨hsp.1,hsp.2.1⟩
   ·rintro⟨_,_,hA,_⟩;exact hA
  ·intro d₁ _ d₂ _ hne;simp only[Function.onFun];rw[Zk]
   intro A h1 h2;exact hne ((Za.mp h1).2.symm.trans (Za.mp h2).2)
 set Qcoef:ℝ:=max ((43/100*y)^2/(114/100)) (y-y^2-(57/100)*m1+(57/200)*m1^2)
 have hQcoef_nn:0≤ Qcoef:=le_trans (by positivity) (Ym _ _)
 have hsum_inv:∑ d∈Dset,(1:ℝ)/(d:ℝ)^2≤ S_pc:=by
  dsimp only[Dset,S_pc];split_ifs
  ·exact Xa N
  ·exact W3 N
 have hsum_harm:∑ d∈Dset,(1:ℝ)/(d:ℝ)≤ log (N:ℝ)+1 :=(sum_le_sum_of_subset_of_nonneg hDset_sub (fun _ _ _=>by positivity)).trans (Q0 N hN)
 have hsum_Pc:(P_c.card:ℝ)≤(Forbid.card:ℝ)+Qcoef*S_pc*(N:ℝ)^2 +190*(N:ℝ)*(log (N:ℝ)+2)*(log (N:ℝ)+1):=by
  have h1:(P_c.card:ℝ)=∑ d∈Dset,((Pd d).card:ℝ):=by exact_mod_cast hPc_part
  have h2:(Forbid.card:ℝ)=∑ d∈Dset,(((E_LR_hit d).card:ℝ)+((E_L_hit d).card:ℝ)):=by exact_mod_cast hForb_card
  rw[h1,h2]
  have hper:∀ d∈Dset,((Pd d).card:ℝ)≤(((E_LR_hit d).card:ℝ)+((E_L_hit d).card:ℝ)) +Qcoef*(N:ℝ)^2*((1:ℝ)/(d:ℝ)^2) +190*(N:ℝ)*(log (N:ℝ)+2)*((1:ℝ)/(d:ℝ)):=by
   intro d hd
   have h:=Xy N c L₁ R₁ d hN hc hL1 hLR1 hR1c (hDset_sub hd) (Pd d) getU getV
    (fun A hA=>by obtain⟨hAPc,hAd⟩:=Za.mp hA;have:=hUV A hAPc;rwa[hAd] at this)
    (fun A hA=>hPc_hit A (Za.mp hA).1)
   have h':((Pd d).card:ℝ)≤((E_LR_hit d).card:ℝ)+((E_L_hit d).card:ℝ) +Qcoef*((N:ℝ)^2/(d:ℝ)^2)+190*((N:ℝ)/(d:ℝ))*(log (N:ℝ)+2):=h
   have heq1:Qcoef*((N:ℝ)^2/(d:ℝ)^2)=Qcoef*(N:ℝ)^2*((1:ℝ)/(d:ℝ)^2):=by ring
   have heq2:190*((N:ℝ)/(d:ℝ))*(log (N:ℝ)+2) =190*(N:ℝ)*(log (N:ℝ)+2)*((1:ℝ)/(d:ℝ)):=by ring
   linarith
  have hlog_nn:0≤ log (N:ℝ):=Real.log_nonneg (by exact_mod_cast hN)
  calc ∑ d∈Dset,((Pd d).card:ℝ)
      ≤ ∑ d∈Dset,((((E_LR_hit d).card:ℝ)+((E_L_hit d).card:ℝ)) +Qcoef*(N:ℝ)^2*((1:ℝ)/(d:ℝ)^2) +190*(N:ℝ)*(log (N:ℝ)+2)*((1:ℝ)/(d:ℝ))):=Finset.sum_le_sum hper
    _=(∑ d∈Dset,(((E_LR_hit d).card:ℝ)+((E_L_hit d).card:ℝ))) +
        Qcoef*(N:ℝ)^2*(∑ d∈Dset,(1:ℝ)/(d:ℝ)^2) +
        190*(N:ℝ)*(log (N:ℝ)+2)*(∑ d∈Dset,(1:ℝ)/(d:ℝ)):=by
        simp only[Finset.sum_add_distrib,←Finset.mul_sum]
    _≤(∑ d∈Dset,(((E_LR_hit d).card:ℝ)+((E_L_hit d).card:ℝ))) +
        Qcoef*(N:ℝ)^2*S_pc +
        190*(N:ℝ)*(log (N:ℝ)+2)*(log (N:ℝ)+1):=by
        have ha:=Zp hsum_inv (by positivity:0≤ Qcoef*(N:ℝ)^2)
        have hb:=Zp hsum_harm (by positivity:0≤190*(N:ℝ)*(log (N:ℝ)+2))
        linarith
    _=(∑ d∈Dset,(((E_LR_hit d).card:ℝ)+((E_L_hit d).card:ℝ))) +
        Qcoef*S_pc*(N:ℝ)^2 +
        190*(N:ℝ)*(log (N:ℝ)+2)*(log (N:ℝ)+1):=by ring
 have hhit_R:((Qa c A1 Q_c).card:ℝ)+(Forbid.card:ℝ)≤(m1-m1^2/2)*(N:ℝ)^2:=by
  have h1:((Qa c A1 Q_c).card:ℝ)+(Forbid.card:ℝ)≤((Qj N c A1).card:ℝ):=by exact_mod_cast hpack
  have h2:=Wc N c hc A1 hA1_sub;rw[hA1_card] at h2
  have h3:((R₁-L₁+1:ℕ):ℝ)*(N:ℝ)-((R₁-L₁+1:ℕ):ℝ)^2/2 =(m1-m1^2/2)*(N:ℝ)^2:=by dsimp only[m1];field_simp
  linarith
 have hlog_nn:0≤ log (N:ℝ):=Real.log_nonneg (by exact_mod_cast hN)
 nlinarith
private lemma Kc (N c m₁ h_nat:ℕ) (hN:1≤ N) (hcN:c≤ N) (hh_le_c:h_nat≤ c) :
  let beta:ℝ:=(c:ℝ)/(N:ℝ)
  let y:ℝ:=1-beta
  let m1:ℝ:=(m₁:ℝ)/(N:ℝ)
  let h:ℝ:=(h_nat:ℝ)/(N:ℝ)
  h*y+(if m₁≤ h_nat/\m₁≤ c-h_nat then h*(beta-h)-m1^2/2
     else if h_nat≤ m₁/\m₁≤ c-h_nat then h*(beta-m1)-h^2/2
     else if m₁≤ h_nat/\c-h_nat≤ m₁ then (beta-h)*(beta-m1)-(beta-h)^2/2
     else (max 0 (beta-m1))^2/2) ≤
   max (max (if 2*m1≤ beta then 1/4-m1^2/2 else 0)
        (if 1/2≤ m1 then (1-m1)^2/2 else 1/6))
     (max (y*(1-y)+(max 0 (1-2*y-m1))^2/2)
        (m1*y+(max 0 (1-y-m1))^2/2)):=by
 intro beta y m1 h
 have hN_pos:(0:ℝ)<(N:ℝ):=by exact_mod_cast (by omega:0< N)
 have hbeta_le1:beta≤1:=(div_le_one hN_pos).mpr (by exact_mod_cast hcN)
 have hh_le_beta:h≤ beta:=div_le_div_of_nonneg_right (by exact_mod_cast hh_le_c) hN_pos.le
 have hy_nn:0≤ y:=by dsimp only[y];linarith
 set M:=max (max (if 2*m1≤ beta then 1/4-m1^2/2 else 0)
          (if 1/2≤ m1 then (1-m1)^2/2 else 1/6))
        (max (y*(1-y)+(max 0 (1-2*y-m1))^2/2)
          (m1*y+(max 0 (1-y-m1))^2/2))
 change h*y+_≤ M
 split_ifs with hC1 hC2 hC3
 ·have h2m:2*m1≤ beta:=by
   have:2*m₁≤ c:=by omega
   have h1:(2*m₁:ℝ)≤(c:ℝ):=by exact_mod_cast this
   dsimp only[m1,beta];rw[←mul_div_assoc];exact div_le_div_of_nonneg_right h1 hN_pos.le
  have h1:h*y+(h*(beta-h)-m1^2/2)≤1/4-m1^2/2:=by
   have:y+beta=1:=by dsimp only[y];ring
   nlinarith[sq_nonneg (h-1/2)]
  have h2:(if 2*m1≤ beta then 1/4-m1^2/2 else 0)=1/4-m1^2/2:=if_pos h2m
  exact (h1.trans (le_of_eq h2.symm)).trans ((Ym _ _).trans (Ym _ _))
 ·have hh_le_m1:h≤ m1:=div_le_div_of_nonneg_right (by exact_mod_cast hC2.1) hN_pos.le
  have h1:h*y+(h*(beta-m1)-h^2/2)=h*(1-m1)-h^2/2:=by dsimp only[y];ring
  rw[h1]
  have h2:h*(1-m1)-h^2/2≤ if 1/2≤ m1 then (1-m1)^2/2 else 1/6:=by
   split_ifs with hm
   ·nlinarith[sq_nonneg (h-(1-m1))]
   ·have hle:h*(1-m1)-h^2/2≤ m1*(1-m1)-m1^2/2:=by
     have:(m1*(1-m1)-m1^2/2)-(h*(1-m1)-h^2/2)=(m1-h)*(1-m1-(m1+h)/2):=by ring
     nlinarith
    nlinarith[sq_nonneg (m1-1/3)]
  exact h2.trans ((Yn _ _).trans (Ym _ _))
 ·set t:=beta-h
  have h1:h*y+(t*(beta-m1)-t^2/2)=y*(1-y)+t*(1-2*y-m1)-t^2/2:=by dsimp only[t,y];ring
  rw[h1]
  have h2:t*(1-2*y-m1)-t^2/2≤(max 0 (1-2*y-m1))^2/2:=by
   have ht_nn:0≤ t:=by dsimp only[t];linarith
   have hle:t*(1-2*y-m1)≤ t*max 0 (1-2*y-m1) :=Zp (Yn _ _) ht_nn;nlinarith[sq_nonneg (t-max 0 (1-2*y-m1))]
  exact (by linarith:y*(1-y)+t*(1-2*y-m1)-t^2/2 ≤ y*(1-y)+(max 0 (1-2*y-m1))^2/2).trans ((Ym _ _).trans (Yn _ _))
 ·have hh_lt_m1:h≤ m1:=div_le_div_of_nonneg_right (by exact_mod_cast (by omega:h_nat≤ m₁)) hN_pos.le
  have hby:beta=1-y:=by dsimp only[y];ring
  rw[hby];have h1:h*y≤ m1*y:=Zo hh_lt_m1 hy_nn
  exact (by linarith:h*y+(max 0 (1-y-m1))^2/2 ≤ m1*y+(max 0 (1-y-m1))^2/2).trans ((Yn _ _).trans (Yn _ _))
private lemma Vy (a b k:ℕ) (hka:k≤ a+1) (hkb:k≤ b+1) :k^2≤2*(((Icc 0 a) ×ˢ (Icc 0 b)).filter (fun p=>p.1+p.2< k)).card:=by
 let E:=((Icc 0 a) ×ˢ (Icc 0 b)).filter (fun p=>p.1+p.2< k)
 have hsub:(range k).biUnion (fun u=>(range (k-u)).image (fun v=>(u,v)))⊆E:=by
  intro p hp;obtain⟨u,hu,hp2⟩:=mem_biUnion.mp hp;obtain⟨v,hv,rfl⟩:=Zi.mp hp2;rw[mem_range] at hu hv
  exact Za.mpr ⟨Zh.mpr
   ⟨Zb.mpr ⟨Nat.zero_le _,by omega⟩,Zb.mpr ⟨Nat.zero_le _,by omega⟩⟩,by omega⟩
 have hdisj_u:Set.PairwiseDisjoint (range k:Set ℕ)
   (fun u=>(range (k-u)).image (fun v=>(u,v))):=by
  intro u₁ _ u₂ _ hne;simp only[Function.onFun];rw[Zk];intro p h1 h2;obtain⟨v₁,-,rfl⟩:=Zi.mp h1;obtain⟨v₂,-,heq⟩:=Zi.mp h2;exact hne (congrArg Prod.fst heq).symm
 have hcard_u:∑ u∈range k,(k-u)≤ E.card:=by
  calc ∑ u∈range k,(k-u)
      = ∑ u∈range k,((range (k-u)).image (fun v=>(u,v))).card:=by
        refine Finset.sum_congr rfl fun u _=>?_
        rw[card_image_of_injective _ (fun _ _ h=>congrArg Prod.snd h),card_range]
    _=((range k).biUnion (fun u=>(range (k-u)).image (fun v=>(u,v)))).card :=
        (card_biUnion hdisj_u).symm
    _≤ E.card:=Zm hsub
 have hsum_tri:∀ n:ℕ,2*∑ u∈range n,(n-u)=n*(n+1):=by
  intro n;induction n with
  | zero=>simp
  | succ r ih =>
   rw[sum_range_succ'];simp only[Nat.sub_zero,Nat.succ_sub_succ_eq_sub];nlinarith
 have h2:2*∑ u∈range k,(k-u)=k*(k+1):=hsum_tri k
 have hsq:k^2≤ k*(k+1):=by rw[sq];exact Yd k (Nat.le_succ k)
 dsimp only[E] at hcard_u;omega
private lemma Xo (a b m':ℕ) (ha:a≤ m') (hb:m'≤ b+1) :2*(((Icc 0 a) ×ˢ (Icc 0 b)).filter (fun p=>m'≤ p.1+p.2)).card ≤(a+1)*(2*(b+1-m')+a):=by
 let S:=((Icc 0 a) ×ˢ (Icc 0 b)).filter (fun p=>m'≤ p.1+p.2)
 have hsub:S⊆(Icc 0 a).biUnion (fun u=>(Icc (m'-u) b).image (fun v=>(u,v))):=by
  intro ⟨u,v⟩ hp;obtain⟨hP,hge⟩:=Za.mp hp;obtain⟨hu,hv⟩:=Zh.mp hP
  exact mem_biUnion.mpr ⟨u,hu,Zi.mpr ⟨v,Zb.mpr ⟨by omega,(Zb.mp hv).2⟩,rfl⟩⟩
 have hScard:S.card≤∑ u∈Icc 0 a,(b+1-(m'-u)):=by
  calc S.card≤_:=(Zm hsub).trans card_biUnion_le
    _≤∑ u∈Icc 0 a,(Icc (m'-u) b).card:=Finset.sum_le_sum fun _ _=>card_image_le
    _=∑ u∈Icc 0 a,(b+1-(m'-u)):=Finset.sum_congr rfl fun _ _=>Nat.card_Icc _ _
 have hterm:∀ u∈Icc 0 a,b+1-(m'-u)=(b+1-m')+u:=by intro u hu;have:=(Zb.mp hu).2;omega
 rw[Finset.sum_congr rfl hterm,Finset.sum_add_distrib,Finset.sum_const,Nat.card_Icc,Nat.sub_zero,smul_eq_mul] at hScard
 have hsumu:∀ n:ℕ,2*∑ u∈Icc 0 n,u=n*(n+1):=by
  intro n;induction n with
  | zero=>simp
  | succ k ih=>rw[sum_Icc_succ_top (Nat.zero_le _)];nlinarith
 have hsu:=hsumu a
 have hmul:2*((a+1)*(b+1-m')+∑ u∈Icc 0 a,u)=(a+1)*(2*(b+1-m')+a):=by rw[Nat.mul_add,←Nat.mul_assoc,hsu];ring
 dsimp only[S] at hScard;omega
private lemma V5 (N c m₁ h_nat:ℕ) (hN:1≤ N) (hc1:1≤ c) (hcN:c≤ N)
  (hm1:1≤ m₁) (hh1:1≤ h_nat) (hh_lt_c:h_nat≤ c-1) :
  let a:=h_nat-1
  let b:=c-1-h_nat
  let m':=m₁-1
  let beta:ℝ:=(c:ℝ)/(N:ℝ)
  let y:ℝ:=1-beta
  let m1:ℝ:=(m₁:ℝ)/(N:ℝ)
  let h:ℝ:=(h_nat:ℝ)/(N:ℝ)
  let PairSet:=((Icc 0 a) ×ˢ (Icc 0 b)).filter (fun p=>m'≤ p.1+p.2)
  h*y*(N:ℝ)^2+(PairSet.card:ℝ) ≤ max (max (if 2*m1≤ beta then 1/4-m1^2/2 else 0)
        (if 1/2≤ m1 then (1-m1)^2/2 else 1/6))
     (max (y*(1-y)+(max 0 (1-2*y-m1))^2/2)
        (m1*y+(max 0 (1-y-m1))^2/2))*(N:ℝ)^2 +
   8*(N:ℝ):=by
 intro a b m' beta y m1 h PairSet
 have hN_pos:(0:ℝ)<(N:ℝ):=by exact_mod_cast (by omega:0< N)
 have hh_le_beta:h≤ beta:=div_le_div_of_nonneg_right (by exact_mod_cast (by omega:h_nat≤ c)) hN_pos.le
 have ha_R:(a:ℝ)≤ h*(N:ℝ):=by dsimp only[a,h];field_simp;exact_mod_cast Nat.sub_le h_nat 1
 have hb_R:(b:ℝ)≤(beta-h)*(N:ℝ):=by
  have:(b:ℝ)≤((c-h_nat:ℕ):ℝ):=by exact_mod_cast (by dsimp only[b];omega:b≤ c-h_nat)
  have h2:(beta-h)*(N:ℝ)=((c-h_nat:ℕ):ℝ):=by
   dsimp only[beta,h];rw[Nat.cast_sub (by omega:h_nat≤ c)];field_simp
  linarith only[this,h2]
 have haN:(a:ℝ)≤(N:ℝ):=by exact_mod_cast (by dsimp only[a];omega:a≤ N)
 have hbN:(b:ℝ)≤(N:ℝ):=by exact_mod_cast (by dsimp only[b];omega:b≤ N)
 have hPair_bd:(PairSet.card:ℝ) ≤(if m₁≤ h_nat/\m₁≤ c-h_nat then h*(beta-h)-m1^2/2
    else if h_nat≤ m₁/\m₁≤ c-h_nat then h*(beta-m1)-h^2/2
    else if m₁≤ h_nat/\c-h_nat≤ m₁ then (beta-h)*(beta-m1)-(beta-h)^2/2
    else (max 0 (beta-m1))^2/2)*(N:ℝ)^2+8*(N:ℝ):=by
  split_ifs with hC1 hC2 hC3
  ·have hpart:PairSet.card+(((Icc 0 a) ×ˢ (Icc 0 b)).filter (fun p=>p.1+p.2< m')).card =(a+1)*(b+1):=by
    have hcomp:((Icc 0 a) ×ˢ (Icc 0 b)).filter (fun p=>p.1+p.2< m') =((Icc 0 a) ×ˢ (Icc 0 b)).filter (fun p=>¬ (m'≤ p.1+p.2)) :=filter_congr fun _ _=>by omega
    dsimp only[PairSet];rw[hcomp,card_filter_add_card_filter_not,card_product,Nat.card_Icc,Nat.card_Icc];simp
   have hbelow:=Vy a b m' (by dsimp only[a,m'];omega) (by dsimp only[b,m'];omega)
   have hP_nat:2*PairSet.card+m'^2≤2*((a+1)*(b+1)):=by omega
   have hP_R:2*(PairSet.card:ℝ)+((m₁:ℝ)-1)^2≤2*(((a:ℝ)+1)*((b:ℝ)+1)):=by
    have h1:(2*PairSet.card+m'^2:ℝ)≤(2*((a+1)*(b+1)):ℝ):=by exact_mod_cast hP_nat
    rw[show (m':ℝ)=(m₁:ℝ)-1 by dsimp only[m'];rw[Nat.cast_sub hm1,Nat.cast_one]] at h1;linarith only[h1]
   have hm1N:(m₁:ℝ)≤(N:ℝ):=by exact_mod_cast (by omega:m₁≤ N)
   have hprod:((a:ℝ)+1)*((b:ℝ)+1)≤ h*(beta-h)*(N:ℝ)^2+3*(N:ℝ):=by
    have h1:(a:ℝ)*(b:ℝ)≤ h*(beta-h)*(N:ℝ)^2:=by
     have:h*(beta-h)*(N:ℝ)^2=(h*(N:ℝ))*((beta-h)*(N:ℝ)):=by ring
     rw[this];exact mul_le_mul ha_R hb_R (Nat.cast_nonneg _) (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hN_pos.le) hN_pos.le)
    have h1N:(1:ℝ)≤(N:ℝ):=by exact_mod_cast hN
    nlinarith only[h1,haN,hbN,h1N]
   have hm1_sq:m1^2*(N:ℝ)^2=(m₁:ℝ)^2:=by dsimp only[m1];rw[div_pow,div_mul_cancel₀ _ (pow_ne_zero 2 hN_pos.ne')]
   nlinarith only[hP_R,hprod,hm1_sq,hm1N,hN_pos]
  ·have hsum_le:2*PairSet.card≤(a+1)*(2*(b+1-m')+a) :=Xo a b m' (by dsimp only[a,m'];omega) (by dsimp only[b,m'];omega)
   have hR:2*(PairSet.card:ℝ)≤((a:ℝ)+1)*(2*((b:ℝ)+1-((m₁:ℝ)-1))+(a:ℝ)):=by
    have h1:(2*PairSet.card:ℝ)≤((a+1:ℕ):ℝ)*((2*(b+1-m')+a:ℕ):ℝ):=by exact_mod_cast hsum_le
    have hbm:m'≤ b+1:=by dsimp only[b,m'];omega
    have hm'R:(m':ℝ)=(m₁:ℝ)-1:=by dsimp only[m'];rw[Nat.cast_sub hm1,Nat.cast_one]
    have hcast:((2*(b+1-m')+a:ℕ):ℝ)=2*((b:ℝ)+1-((m₁:ℝ)-1))+(a:ℝ):=by rw[Nat.cast_add,Nat.cast_mul,Nat.cast_sub hbm,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,hm'R]
    rw[hcast,Nat.cast_add,Nat.cast_one] at h1;linarith only[h1]
   have halg:(h*(beta-m1)-h^2/2)*(N:ℝ)^2 =(h*(N:ℝ))*(((c:ℝ)-(m₁:ℝ))-(h*(N:ℝ))/2):=by dsimp only[h,beta,m1];field_simp
   have ha_eq:(a:ℝ)+1=h*(N:ℝ):=by dsimp only[a,h];rw[Nat.cast_sub hh1,Nat.cast_one,div_mul_cancel₀ _ hN_pos.ne'];ring
   have hba:(b:ℝ)+(a:ℝ)+2=(c:ℝ):=by
    have:b+a+2=c:=by dsimp only[a,b];omega
    exact_mod_cast this
   have hb_m:(2*((b:ℝ)+1-((m₁:ℝ)-1))+(a:ℝ))=2*((c:ℝ)-(m₁:ℝ))-((a:ℝ)+1)+1:=by linarith only[hba]
   have hhh:h*(N:ℝ)≤(N:ℝ):=by rw[←ha_eq];exact_mod_cast (by dsimp only[a];omega:a+1≤ N)
   nlinarith only[hR,halg,ha_eq,hb_m,hhh,hN_pos]
  ·have hswap:PairSet.card=(((Icc 0 b) ×ˢ (Icc 0 a)).filter (fun p=>m'≤ p.1+p.2)).card:=by
    refine card_bij (fun p _=>(p.2,p.1)) ?_ ?_ ?_
    ·intro ⟨u,v⟩ hp;simp only[PairSet,Za,Zh] at hp ⊢
     exact⟨⟨hp.1.2,hp.1.1⟩,by omega⟩
    ·intro ⟨u₁,v₁⟩ _ ⟨u₂,v₂⟩ _ heq;simp only[Prod.mk.injEq] at heq;exact Prod.ext heq.2 heq.1
    ·intro ⟨v,u⟩ hp;simp only[Za,Zh] at hp
     exact⟨(u,v),Za.mpr ⟨Zh.mpr ⟨hp.1.2,hp.1.1⟩,by omega⟩,rfl⟩
   have hsum_le:2*PairSet.card≤(b+1)*(2*(a+1-m')+b):=by
    rw[hswap];exact Xo b a m' (by dsimp only[b,m'];omega) (by dsimp only[a,m'];omega)
   have hR:2*(PairSet.card:ℝ)≤((b:ℝ)+1)*(2*((a:ℝ)+1-((m₁:ℝ)-1))+(b:ℝ)):=by
    have h1:(2*PairSet.card:ℝ)≤((b+1:ℕ):ℝ)*((2*(a+1-m')+b:ℕ):ℝ):=by exact_mod_cast hsum_le
    have ham:m'≤ a+1:=by dsimp only[a,m'];omega
    have hm'R:(m':ℝ)=(m₁:ℝ)-1:=by dsimp only[m'];rw[Nat.cast_sub hm1,Nat.cast_one]
    have hcast:((2*(a+1-m')+b:ℕ):ℝ)=2*((a:ℝ)+1-((m₁:ℝ)-1))+(b:ℝ):=by rw[Nat.cast_add,Nat.cast_mul,Nat.cast_sub ham,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat,hm'R]
    rw[hcast,Nat.cast_add,Nat.cast_one] at h1;linarith only[h1]
   have halg:((beta-h)*(beta-m1)-(beta-h)^2/2)*(N:ℝ)^2 =((beta-h)*(N:ℝ))*(((c:ℝ)-(m₁:ℝ))-((beta-h)*(N:ℝ))/2):=by dsimp only[h,beta,m1];field_simp
   have hb_eq:(b:ℝ)+1=(beta-h)*(N:ℝ):=by
    dsimp only[b,beta,h]
    have:c-1-h_nat+1=c-h_nat:=by omega
    rw[show ((c-1-h_nat:ℕ):ℝ)+1=((c-h_nat:ℕ):ℝ) by exact_mod_cast this,Nat.cast_sub (by omega:h_nat≤ c),sub_mul,div_mul_cancel₀ _ hN_pos.ne',div_mul_cancel₀ _ hN_pos.ne']
   have hba:(b:ℝ)+(a:ℝ)+2=(c:ℝ):=by
    have:b+a+2=c:=by dsimp only[a,b];omega
    exact_mod_cast this
   have ha_m:2*((a:ℝ)+1-((m₁:ℝ)-1))+(b:ℝ)=2*((c:ℝ)-(m₁:ℝ))-((b:ℝ)+1)+1:=by linarith only[hba]
   have hbh_le:(beta-h)*(N:ℝ)≤(N:ℝ):=by rw[←hb_eq];exact_mod_cast (by dsimp only[b];omega:b+1≤ N)
   nlinarith only[hR,halg,hb_eq,ha_m,hbh_le,hN_pos]
  ·have h1:=Xm a b m'
   have hf:fInt ((a+b:ℕ):ℝ) (m':ℝ)≤(max 0 (beta-m1))^2/2*(N:ℝ)^2:=by
    have hba:a+b+1≤ c:=by dsimp only[a,b];omega
    have h2m:((a+b:ℕ):ℝ)≤2*(m':ℝ):=by exact_mod_cast (by dsimp only[a,b,m'];omega:a+b≤2*m')
    have hle_diff:((a+b:ℕ):ℝ)-(m':ℝ)≤ max 0 (beta-m1)*(N:ℝ):=by
     have hle1:((a+b:ℕ):ℝ)-(m':ℝ)≤(beta-m1)*(N:ℝ):=by
      have hc':(beta-m1)*(N:ℝ)=(c:ℝ)-(m₁:ℝ):=by dsimp only[beta,m1];rw[sub_mul,div_mul_cancel₀ _ hN_pos.ne',div_mul_cancel₀ _ hN_pos.ne']
      rw[hc',show (m':ℝ)=(m₁:ℝ)-1 by dsimp only[m'];rw[Nat.cast_sub hm1,Nat.cast_one]]
      have hR':((a+b:ℕ):ℝ)+1≤(c:ℝ):=by exact_mod_cast hba
      linarith only[hR']
     exact hle1.trans (Zo (Yn _ _) hN_pos.le)
    unfold fInt
    split_ifs with hlt h2ge
    ·positivity
    ·have heq:((a+b:ℕ):ℝ)=2*(m':ℝ):=le_antisymm h2m h2ge
     have h4:((a+b:ℕ):ℝ)^2/4-(m':ℝ)^2/2=(((a+b:ℕ):ℝ)-(m':ℝ))^2/2:=by rw[heq];ring
     rw[h4]
     have hnn:0≤((a+b:ℕ):ℝ)-(m':ℝ):=by linarith only[hlt]
     have hsq:=pow_le_pow_left₀ hnn hle_diff 2;rw[mul_pow] at hsq;linarith only[hsq]
    ·have hnn:0≤((a+b:ℕ):ℝ)-(m':ℝ):=by linarith only[hlt]
     have hsq:=pow_le_pow_left₀ hnn hle_diff 2;rw[mul_pow] at hsq;linarith only[hsq]
   have habN:((a+b:ℕ):ℝ)≤(N:ℝ):=by exact_mod_cast (by dsimp only[a,b];omega:a+b≤ N)
   have h1N:(1:ℝ)≤(N:ℝ):=by exact_mod_cast hN
   linarith only[h1,hf,habN,h1N]
 have hcomb:=Kc N c m₁ h_nat hN hcN (by omega)
 dsimp only at hcomb;have hmul:=Zo hcomb (sq_nonneg (N:ℝ));rw[add_mul] at hmul;linarith only[hPair_bd,hmul]
lemma V7 (N c m₁:ℕ) (hN:1≤ N) (hc:c∈Icc 1 N) (hm1:1≤ m₁)
  (P1_c P1_nc:Zf (Zf ℕ))
  (hF:Zt N (P1_c∪P1_nc))
  (hP1c:∀ A∈P1_c,IsAP A/\2≤ A.card/\c∈A/\apStep A=1)
  (hP1nc:∀ A∈P1_nc,IsAP A/\2≤ A.card/\A⊆Icc 1 (c-1)/\m₁≤ A.card/\apStep A=1)
  (hne_nc:P1_nc.Nonempty) :
  let beta:ℝ:=(c:ℝ)/(N:ℝ)
  let y:ℝ:=1-beta
  let m1:ℝ:=(m₁:ℝ)/(N:ℝ)
  (P1_c.card:ℝ)+(P1_nc.card:ℝ) ≤ max (max (if 2*m1≤ beta then 1/4-m1^2/2 else 0)
        (if 1/2≤ m1 then (1-m1)^2/2 else 1/6))
     (max (y*(1-y)+(max 0 (1-2*y-m1))^2/2)
        (m1*y+(max 0 (1-y-m1))^2/2))*(N:ℝ)^2 +
   10*(N:ℝ):=by
 classical
 intro beta y m1
 have hN_pos:(0:ℝ)<(N:ℝ):=by exact_mod_cast (by omega:0< N)
 have hc1:=(Zb.mp hc).1;have hcN:=(Zb.mp hc).2;set P1:=P1_c∪P1_nc
 have hIcc:∀ A∈P1,∃ L R:ℕ,1≤ L/\L≤ R/\R≤ N/\A=Icc L R:=by
  intro A hA;have hsubA:A⊆Icc 1 N:=Zy.mp (hF.1 hA)
  have hAP:IsAP A:=by rcases Zd.mp hA with h|h;exact (hP1c A h).1;exact (hP1nc A h).1
  have h2:2≤ A.card:=by rcases Zd.mp hA with h|h;exact (hP1c A h).2.1;exact (hP1nc A h).2.1
  have hst:apStep A=1:=by rcases Zd.mp hA with h|h;exact (hP1c A h).2.2.2;exact (hP1nc A h).2.2.2.2
  obtain⟨-,-,a,k,hk2,-,hX⟩:=Qg hsubA hAP h2;rw[hst] at hX
  have hmm:=Wa (by omega:1≤ k) (fun _=>Nat.zero_lt_one) hX
  have ha1:=(Zb.mp (hsubA hmm.1)).1;have hbN:=(Zb.mp (hsubA hmm.2.1)).2
  refine⟨a,a+(k-1),ha1,by omega,by simpa using hbN,?_⟩
  ext x;rw[hX x,Zb];constructor
  ·rintro⟨i,hi,rfl⟩;simp;omega
  ·intro ⟨h1,h2'⟩;exact⟨x-a,by omega,by simp;omega⟩
 let getL:Zf ℕ->ℕ:=fun A=>if hA:A∈P1 then (hIcc A hA).choose else 0
 let getR:Zf ℕ->ℕ:=fun A=>if hA:A∈P1 then (hIcc A hA).choose_spec.choose else 0
 have hLR:∀ A∈P1,1≤ getL A/\getL A≤ getR A/\getR A≤ N/\A=Icc (getL A) (getR A):=by intro A hA;simpa only [getL,getR,dif_pos hA] using (hIcc A hA).choose_spec.choose_spec
 have hinj_LR:Set.InjOn (fun A=>(getL A,getR A)) (P1:Set (Zf ℕ)):=by intro A hA B hB heq;have h1:getL A=getL B:=congrArg Prod.fst heq;have h2:getR A=getR B:=congrArg Prod.snd heq;rw[(hLR A (Zc.mp hA)).2.2.2,(hLR B (Zc.mp hB)).2.2.2,h1,h2]
 have hP1ne:P1.Nonempty:=hne_nc.mono Zs;obtain⟨A_h,hAh_mem,hAh_max⟩:=exists_max_image P1 getL hP1ne;set h_nat:=getL A_h
 have hh_in_all:∀ A∈P1,getL A≤ h_nat/\h_nat≤ getR A:=by
  intro A hA;have hle:getL A≤ h_nat:=hAh_max A hA
  refine⟨hle,?_⟩
  by_cases heq:A=A_h
  ·rw[heq];exact (hLR A_h hAh_mem).2.1
  ·obtain⟨l,hl,hl'⟩:=hF.2 (Zc.mpr hA) (Zc.mpr hAh_mem) heq
   obtain⟨z,_,_,hk,-,hX⟩:=Qn (A∩A_h) l hl hl'
   obtain⟨hzA,hzAh⟩:=Zn.mp ((hX z).mpr ⟨0,hk,by simp⟩)
   rw[(hLR A hA).2.2.2,Zb] at hzA;rw[(hLR A_h hAh_mem).2.2.2,Zb] at hzAh;omega
 have hh_lt_c:h_nat≤ c-1:=by
  obtain⟨A0,hA0⟩:=hne_nc
  have hR0:getR A0≤ c-1:=by
   have hsub0:=(hP1nc A0 hA0).2.2.1;have hA0P1:=Zg P1_c hA0;set l0:=getL A0;set r0:=getR A0
   have hm:r0∈A0:=by rw[(hLR A0 hA0P1).2.2.2];exact Zb.mpr ⟨(hLR A0 hA0P1).2.1,le_rfl⟩
   exact (Zb.mp (hsub0 hm)).2
  exact (hh_in_all A0 (Zg _ hA0)).2.trans hR0
 have hh1:1≤ h_nat:=(hLR A_h hAh_mem).1
 have hP1c_le:P1_c.card≤ h_nat*(N-c+1):=by
  have hmaps:Set.MapsTo (fun A=>(getL A,getR A)) (P1_c:Set (Zf ℕ))
    (((Icc 1 h_nat) ×ˢ (Icc c N):Zf (ℕ × ℕ)):Set (ℕ × ℕ)):=by
   intro A hA;dsimp only;have hA':=Zc.mp hA;have hAP1:=Ze P1_nc hA';obtain⟨h1,-,hRN,hAeq⟩:=hLR A hAP1;have hcR:c≤ getR A:=(Zb.mp (hAeq ▸ (hP1c A hA').2.2.1)).2
   exact Zc.mpr (Zh.mpr
    ⟨Zb.mpr ⟨h1,(hh_in_all A hAP1).1⟩,Zb.mpr ⟨hcR,hRN⟩⟩)
  exact (card_le_card_of_injOn _ hmaps (hinj_LR.mono (Finset.coe_subset.mpr Zr))).trans
   (by rw[card_product,Nat.card_Icc,Nat.card_Icc];apply Nat.mul_le_mul <;> omega)
 set a:=h_nat-1;set b:=c-1-h_nat;set m':=m₁-1
 let PairSet:=((Icc 0 a) ×ˢ (Icc 0 b)).filter (fun p=>m'≤ p.1+p.2)
 have hP1nc_le:P1_nc.card≤ PairSet.card:=by
  have hmaps:Set.MapsTo (fun A=>(h_nat-getL A,getR A-h_nat)) (P1_nc:Set (Zf ℕ))
    (PairSet:Set (ℕ × ℕ)):=by
   intro A hA;dsimp only;have hA':=Zc.mp hA;have hAP1:=Zg P1_c hA';obtain⟨h1,hLR',-,hAeq⟩:=hLR A hAP1;obtain⟨hLh,hhR⟩:=hh_in_all A hAP1
   have hR_le:getR A≤ c-1:=by
    set rA:=getR A
    have hm:rA∈A:=by rw[hAeq];exact Zb.mpr ⟨hLR',le_rfl⟩
    exact (Zb.mp ((hP1nc A hA').2.2.1 hm)).2
   have hsz:m₁≤ getR A-getL A+1:=by
    have:=(hP1nc A hA').2.2.2.1;rw[hAeq,Nat.card_Icc] at this;omega
   exact Zc.mpr (Za.mpr ⟨Zh.mpr
    ⟨Zb.mpr ⟨Nat.zero_le _,by dsimp only[a];omega⟩,Zb.mpr ⟨Nat.zero_le _,by dsimp only[b];omega⟩⟩,by dsimp only[m'];omega⟩)
  have hinj:Set.InjOn (fun A=>(h_nat-getL A,getR A-h_nat)) (P1_nc:Set (Zf ℕ)):=by
   intro A hA B hB heq;have hAP1:=Zg P1_c (Zc.mp hA);have hBP1:=Zg P1_c (Zc.mp hB);obtain⟨hLA,hRA⟩:=hh_in_all A hAP1;obtain⟨hLB,hRB⟩:=hh_in_all B hBP1;have e1:h_nat-getL A=h_nat-getL B:=congrArg Prod.fst heq;have e2:getR A-h_nat=getR B-h_nat:=congrArg Prod.snd heq
   have hpair:(getL A,getR A)=(getL B,getR B):=Prod.ext (by omega) (by omega)
   exact hinj_LR (Zc.mpr hAP1) (Zc.mpr hBP1) hpair
  exact card_le_card_of_injOn _ hmaps hinj
 set h:ℝ:=(h_nat:ℝ)/(N:ℝ)
 have hy_eq:y=((N-c:ℕ):ℝ)/(N:ℝ):=by dsimp only[y,beta];rw[Nat.cast_sub hcN];field_simp
 have hP1c_R:(P1_c.card:ℝ)≤ h*y*(N:ℝ)^2+(N:ℝ):=by
  have h1:(P1_c.card:ℝ)≤(h_nat:ℝ)*(((N-c:ℕ):ℝ)+1):=by
   have:P1_c.card≤ h_nat*((N-c)+1):=hP1c_le
   exact_mod_cast this
  have hhN:(h_nat:ℝ)≤(N:ℝ):=by exact_mod_cast (by omega:h_nat≤ N)
  have h2:h*y*(N:ℝ)^2=(h_nat:ℝ)*((N-c:ℕ):ℝ):=by rw[hy_eq];dsimp only[h];field_simp
  linarith
 have hP1nc_R:(P1_nc.card:ℝ)≤(PairSet.card:ℝ):=by exact_mod_cast hP1nc_le
 have hmain:=V5 N c m₁ h_nat hN hc1 hcN hm1 hh1 hh_lt_c;dsimp only at hmain
 have hmain':h*y*(N:ℝ)^2+(PairSet.card:ℝ) ≤ max (max (if 2*m1≤ beta then 1/4-m1^2/2 else 0)
        (if 1/2≤ m1 then (1-m1)^2/2 else 1/6))
     (max (y*(1-y)+(max 0 (1-2*y-m1))^2/2)
        (m1*y+(max 0 (1-y-m1))^2/2))*(N:ℝ)^2 +
   8*(N:ℝ):=hmain
 linarith
lemma Wb {L m₁ m₂:ℝ} (h0:0≤ m₁) (h12:m₁≤ m₂) (hL:0≤ L) :fInt L m₂≤ fInt L m₁:=by
 unfold fInt
 split_ifs <;> nlinarith
lemma W9 {L m:ℝ} (hm:0≤ m) (h:L≤ m):fInt L m=0:=by
 unfold fInt
 split_ifs with h1 h2
 ·rfl
 ·have hm0:m=0:=by linarith
  have hL0:L=0:=by linarith
  rw[hm0,hL0];ring
 ·have:L=m:=by linarith
  rw[this];ring
lemma X0 {L m₁ m₂:ℝ} (h12:m₁≤ m₂) (h2:m₂≤1) (hL1:L≤1) :(m₁-m₁^2/2)+fInt L m₁≤(m₂-m₂^2/2)+fInt L m₂:=by
 unfold fInt
 split_ifs <;> nlinarith
noncomputable def pnc3Sum (m:ℝ):ℝ :=∑ d∈Icc (3:ℕ) 11,fInt (1/(d:ℝ)) m
lemma Ki {m₁ m₂:ℝ} (h0:0≤ m₁) (h12:m₁≤ m₂) :pnc3Sum m₂≤ pnc3Sum m₁:=by
 unfold pnc3Sum
 refine Finset.sum_le_sum fun d hd=>Wb h0 h12 (by positivity)
lemma Ww {m:ℝ} (hm:1/3≤ m):pnc3Sum m=0:=by
 unfold pnc3Sum
 refine Finset.sum_eq_zero fun d hd=>W9 (by linarith) ?_
 have hd3:(3:ℝ)≤(d:ℝ):=by exact_mod_cast (Zb.mp hd).1
 have h1:(1:ℝ)/(d:ℝ)≤1/3:=one_div_le_one_div_of_le (by norm_num) hd3
 linarith
lemma Vp :∑ d∈Icc (2:ℕ) 5,fInt (1/(d:ℝ)) (19/100)≤57/1000:=by
 simp only[sum_Icc_succ_top (by decide:2≤3),sum_Icc_succ_top (by decide:2≤4),sum_Icc_succ_top (by decide:2≤5),Icc_self,Finset.sum_singleton]
 unfold fInt;norm_num
lemma Kg :∑ d∈Icc (3:ℕ) 5,fInt (1/(d:ℝ)) (19/100)≤13/1000:=by
 simp only[sum_Icc_succ_top (by decide:3≤4),sum_Icc_succ_top (by decide:3≤5),Icc_self,Finset.sum_singleton]
 unfold fInt;norm_num
lemma Vx {m:ℝ} (h0:0≤ m) (h1:m≤19/100) :(m-m^2/2)+(1-m)^2/4+129/800≤1/2:=by
 nlinarith
lemma Vw (d₀:ℕ) (hd₀:d₀∈Icc 2 5) {mb y g:ℝ}
  (hmb:19/100≤ mb) (hy:0≤ y) (hg:0≤ g)
  (hpack:(d₀:ℝ)*mb+y≤ if d₀=2 then 1 else 101/100) :
  let core:=max ((mb-mb^2/2)+(max 0 (((d₀:ℝ)-1)*y-g))^2/(4*(d₀:ℝ)-2))
          (y-y^2-g*y)
  core+129/800≤1/2 ∨
  (d₀=2/\core+(645/1000)*(1-y)*y+57/1000≤1/2):=by
 intro core
 have hmem:d₀=2\/d₀=3\/d₀=4\/d₀=5:=by have h:=Zb.mp hd₀;omega
 have hy_sub:y-y^2-g*y≤ y-y^2:=by nlinarith
 have hA_le:max 0 (((d₀:ℝ)-1)*y-g)≤((d₀:ℝ)-1)*y:=by
  have:(1:ℝ)≤(d₀:ℝ):=by exact_mod_cast (by have:=(Zb.mp hd₀).1;omega:1≤ d₀)
  exact max_le (by nlinarith) (by linarith)
 have hA_sq:(max 0 (((d₀:ℝ)-1)*y-g))^2≤(((d₀:ℝ)-1)*y)^2 :=pow_le_pow_left₀ (Ym _ _) hA_le 2
 rcases hmem with rfl|rfl|rfl|rfl
 ·norm_num at hpack hA_sq
  have hcore_eq:core=max ((mb-mb^2/2)+(max 0 (y-g))^2/6) (y-y^2-g*y):=by dsimp only[core];norm_num
  by_cases hmb36:mb≤36/100
  ·left
   have h1:(mb-mb^2/2)+(max 0 (y-g))^2/6+129/800≤1/2:=by nlinarith[sq_nonneg (mb-36/100)]
   have h2:(y-y^2-g*y)+129/800≤1/2:=by nlinarith[sq_nonneg (y-1/2)]
   rw[hcore_eq]
   have hmax:max ((mb-mb^2/2)+(max 0 (y-g))^2/6) (y-y^2-g*y)≤1/2-129/800 :=max_le (by linarith) (by linarith)
   linarith
  ·right;refine⟨rfl,?_⟩
   push Not at hmb36
   have h1:(mb-mb^2/2)+(max 0 (y-g))^2/6+(645/1000)*(1-y)*y+57/1000≤1/2:=by nlinarith[sq_nonneg (mb-1/2),sq_nonneg (y-28/100)]
   have h2:(y-y^2-g*y)+(645/1000)*(1-y)*y+57/1000≤1/2:=by nlinarith[sq_nonneg (y-28/100)]
   rw[hcore_eq]
   have hmax:max ((mb-mb^2/2)+(max 0 (y-g))^2/6) (y-y^2-g*y) ≤1/2-((645/1000)*(1-y)*y+57/1000) :=max_le (by linarith) (by linarith)
   linarith
 ·left
  norm_num at hpack hA_sq
  have hcore_eq:core=max ((mb-mb^2/2)+(max 0 (2*y-g))^2/10) (y-y^2-g*y):=by dsimp only[core];norm_num
  have h1:(mb-mb^2/2)+(max 0 (2*y-g))^2/10+129/800≤1/2:=by nlinarith
  have h2:(y-y^2-g*y)+129/800≤1/2:=by nlinarith[sq_nonneg (y-1/2)]
  rw[hcore_eq]
  have:max ((mb-mb^2/2)+(max 0 (2*y-g))^2/10) (y-y^2-g*y)≤1/2-129/800 :=max_le (by linarith) (by linarith)
  linarith
 ·left
  norm_num at hpack hA_sq
  have hcore_eq:core=max ((mb-mb^2/2)+(max 0 (3*y-g))^2/14) (y-y^2-g*y):=by dsimp only[core];norm_num
  have h1:(mb-mb^2/2)+(max 0 (3*y-g))^2/14+129/800≤1/2:=by nlinarith
  have h2:(y-y^2-g*y)+129/800≤1/2:=by nlinarith[sq_nonneg (y-1/2)]
  rw[hcore_eq]
  have:max ((mb-mb^2/2)+(max 0 (3*y-g))^2/14) (y-y^2-g*y)≤1/2-129/800 :=max_le (by linarith) (by linarith)
  linarith
 ·left
  norm_num at hpack hA_sq
  have hcore_eq:core=max ((mb-mb^2/2)+(max 0 (4*y-g))^2/18) (y-y^2-g*y):=by dsimp only[core];norm_num
  have h1:(mb-mb^2/2)+(max 0 (4*y-g))^2/18+129/800≤1/2:=by nlinarith
  have h2:(y-y^2-g*y)+129/800≤1/2:=by nlinarith[sq_nonneg (y-1/2)]
  rw[hcore_eq]
  have:max ((mb-mb^2/2)+(max 0 (4*y-g))^2/18) (y-y^2-g*y)≤1/2-129/800 :=max_le (by linarith) (by linarith)
  linarith
def CaseBBoundOK (mod2:Bool) (m m1 y:ℝ):Prop :=
 let S_pc:ℝ:=if mod2 then 1235/1000 else 1645/1000
 let L2:ℝ:=if mod2 then 1/2 else max (1-y) y/2
 let pnc1:=fInt (1-y) m1
 let pnc2:=fInt L2 m
 let pnc3:=pnc3Sum m
 let pnc:=pnc1+pnc2+pnc3
 let c1:ℝ:=if 2*m1≤1-y then 1/4-m1^2/2 else 0
 let c2:ℝ:=if 1/2≤ m1 then (1-m1)^2/2 else 1/6
 let c3:ℝ:=y*(1-y)+(max 0 (1-2*y-m1))^2/2
 let c4:ℝ:=m1*y+(max 0 (1-y-m1))^2/2
 (mod2=true/\3/8+pnc≤1/2) ∨
 ((m1-m1^2/2) +max ((43/100*y)^2/(114/100)) (y-y^2-(57/100)*m1+(57/200)*m1^2)*S_pc +pnc≤1/2) ∨
 (max (m1-m1^2/2) (y-y^2)+pnc1+129/800≤1/2) ∨
 ((m-m^2/2)+S_pc*y*(1-y)+pnc≤1/2) ∨
 ((1+2*m-m^2)/4+(S_pc-1)*y*(1-y)+pnc≤1/2) ∨
 (min ((1+2*m-m^2)/4) ((m-m^2/2)+y*(1-y))+pnc1+129/800≤1/2) ∨
 ((m-m^2/2)+max (max c1 c2) (max c3 c4)+129/800≤1/2)
private lemma Vi {m1 y d S:ℝ} (hm1:45/100≤ m1) (hy:0≤ y) (hsum:m1+y≤1)
  (hd0:0≤ d) (hd5:d≤5/100) (hS1:1235/1000≤ S) (hS2:S≤1645/1000) :
  (m1-m1^2/2)+(y-y^2-(57/100)*m1+(57/200)*m1^2)*S +fInt (1-y) m1+d^2/2≤1/2:=by
 have hm1_val:(34875/100000:ℝ)≤ m1-m1^2/2:=by nlinarith
 have hlin:(57/100)*m1-(57/200)*m1^2=(57/100)*(m1-m1^2/2):=by ring
 unfold fInt
 split_ifs with hlt h2m
 ·linarith
 ·have hy10:y≤1/10:=by linarith
  have hneg:y-y^2-(57/100)*m1+(57/200)*m1^2≤-(98/1000):=by nlinarith
  have hSneg:(y-y^2-(57/100)*m1+(57/200)*m1^2)*S≤-(98/1000)*(1235/1000):=by nlinarith
  nlinarith[sq_nonneg (m1-1/2)]
 ·have hcore:(m1-m1^2/2)+(1-y-m1)^2/2=1/2-y*(1-m1-y/2):=by ring
  have hy2:y^2/2≤ y*(1-m1-y/2):=by nlinarith
  have hq:y-y^2-(57/100)*m1+(57/200)*m1^2≤ y-y^2-1987875/10000000:=by nlinarith
  have hquad_pos:(S+1/2)*y^2-S*y+(1987875/10000000)*S-d^2/2≥0:=by
   have h4:4*(S+1/2)*((S+1/2)*y^2-S*y+(1987875/10000000)*S-d^2/2) =(2*(S+1/2)*y-S)^2+(4*(S+1/2)*((1987875/10000000)*S-d^2/2)-S^2):=by ring
   have hdisc:0≤4*(S+1/2)*((1987875/10000000)*S-d^2/2)-S^2:=by nlinarith[sq_nonneg (S-14/10),sq_nonneg d]
   nlinarith[sq_nonneg (2*(S+1/2)*y-S)]
  nlinarith
private lemma Km (mod2:Bool) {m m1 y:ℝ}
  (hm:1/2≤ m) (hmm1:m≤ m1) (hy:0≤ y) (hsum:m1+y≤1) :
  CaseBBoundOK mod2 m m1 y:=by
 right;left
 set S:ℝ:=if mod2 then 1235/1000 else 1645/1000
 have hS1:1235/1000≤ S:=by dsimp only[S];split_ifs <;> norm_num
 have hS2:S≤1645/1000:=by dsimp only[S];split_ifs <;> norm_num
 have hp2:fInt (if mod2 then 1/2 else max (1-y) y/2) m=0:=by
  refine W9 (by linarith) ?_
  split_ifs
  ·exact hm
  ·have:max (1-y) y≤1:=max_le (by linarith) (by linarith)
   linarith
 have hp3:pnc3Sum m=0:=Ww (by linarith)
 rw[hp2,hp3,add_zero,add_zero]
 have h1:(m1-m1^2/2)+((43/100*y)^2/(114/100))*S+fInt (1-y) m1≤1/2:=by
  have hp1:fInt (1-y) m1=(1-y-m1)^2/2:=by
   unfold fInt
   split_ifs with h1 h2
   ·linarith
   ·have:y=0/\m1=1/2:=by constructor <;> linarith
    rw[this.1,this.2];norm_num
   ·rfl
  rw[hp1]
  have hS_nn:0≤(43/100*y)^2/(114/100):=by positivity
  have hS_ub:((43/100*y)^2/(114/100))*S≤((43/100*y)^2/(114/100))*(1645/1000) :=Zp hS2 hS_nn;nlinarith
 have h2:=Vi (d:=0) (by linarith) hy hsum le_rfl (by norm_num) hS1 hS2
 have hmax:max ((43/100*y)^2/(114/100)) (y-y^2-(57/100)*m1+(57/200)*m1^2)*S ≤1/2-(m1-m1^2/2)-fInt (1-y) m1:=by
  rw[max_mul_of_nonneg _ _ (by linarith:0≤ S)]
  exact max_le (by linarith) (by linarith)
 linarith
private lemma V6 {m m1 y:ℝ}
  (hm1:45/100≤ m) (hm2:m≤1/2) (hmm1:m≤ m1) (hy:0≤ y) (hsum:m1+y≤1) :
  let d:ℝ:=1/2-m
  ((m1-m1^2/2)+((43/100*y)^2/(114/100))*(1645/1000)+fInt (1-y) m1+d^2/2≤1/2) ∨
  ((m-m^2/2)+(1645/1000)*y*(1-y)+fInt (1-y) m1+d^2/2≤1/2):=by
 intro d
 have hd0:0≤ d:=by dsimp only[d];linarith
 have hd5:d≤5/100:=by dsimp only[d];linarith
 by_cases hC1:m1≤1/2-(3/4)*d
 ·left
  unfold fInt;split_ifs with hlt h2m
  ·linarith only[hlt,hsum]
  ·have hy10:y≤1/10:=by linarith only[hm1,hmm1,h2m]
   nlinarith only[hd0,hd5,hy,hy10,hm1,hmm1,hC1,h2m,sq_nonneg (1/2-m1-(3/4)*d)]
  ·have hy_ge:(3/2)*d≤ y:=by linarith only[hC1,h2m]
   nlinarith only[hd0,hd5,hy,hy_ge,hm1,hmm1,hC1,hsum,sq_nonneg (y-(3/2)*d)]
 push Not at hC1
 by_cases hC2:y≤(1/10)*d
 ·right
  have hp1_le:fInt (1-y) m1≤ fInt (1-y) (1/2-(3/4)*d) :=Wb (by linarith only[hd5]) hC1.le (by linarith only[hm1,hmm1,hsum])
  have hp1_eq:fInt (1-y) (1/2-(3/4)*d)≤(1/2-y+(3/4)*d)^2/2:=by
   unfold fInt;split_ifs with hlt h2m
   ·positivity
   ·nlinarith only[hd0,hd5,hy,hC2,h2m]
   ·nlinarith only[hd0,hd5,hy,hC2]
  have hm_eq:m=1/2-d:=by dsimp only[d];ring
  rw[hm_eq];nlinarith only[hd0,hd5,hy,hC2,hp1_le,hp1_eq]
 push Not at hC2
 by_cases hC4b:(3/2)*d≤ y
 ·left
  unfold fInt;split_ifs with hlt h2m
  ·linarith only[hlt,hsum]
  ·linarith only[hC1,hC4b,h2m]
  ·nlinarith only[hd0,hd5,hy,hC4b,hC1,hsum,sq_nonneg (y-(3/2)*d)]
 push Not at hC4b
 by_cases hC3:72/100≤ m1
 ·right
  have hp1_le:fInt (1-y) m1≤(1-y-m1)^2/2:=by
   unfold fInt;split_ifs with hlt h2m
   ·positivity
   ·linarith only[hC3,hy,h2m]
   ·exact le_rfl
  have hsq:(1-y-m1)^2≤(28/100-y)^2:=by nlinarith only[hC3,hsum]
  have hm_eq:m=1/2-d:=by dsimp only[d];ring
  rw[hm_eq];nlinarith only[hd0,hd5,hy,hC4b,hp1_le,hsq]
 ·push Not at hC3
  left
  have hbox_y:(y-(1/10)*d)*((3/2)*d-y)≥0:=mul_nonneg (by linarith only[hC2]) (by linarith only[hC4b])
  unfold fInt;split_ifs with hlt h2m
  ·linarith only[hlt,hsum]
  ·have hd2:d^2≤(5/100)*(10*y):=by nlinarith only[hd0,hd5,hC2]
   nlinarith only[sq_nonneg (m1-1/2),hd0,hd5,hy,hC4b,hd2]
  ·nlinarith only[hd0,hd5,hy,hC2,hC4b,hC3,hbox_y]
private lemma Kl (mod2:Bool) {m m1 y:ℝ}
  (hm1:45/100≤ m) (hm2:m≤1/2) (hmm1:m≤ m1) (hy:0≤ y) (hsum:m1+y≤1) :
  CaseBBoundOK mod2 m m1 y:=by
 set S:ℝ:=if mod2 then 1235/1000 else 1645/1000
 have hS1:1235/1000≤ S:=by dsimp only[S];split_ifs <;> norm_num
 have hS2:S≤1645/1000:=by dsimp only[S];split_ifs <;> norm_num
 set d:ℝ:=1/2-m
 have hd0:0≤ d:=by dsimp only[d];linarith
 have hd5:d≤5/100:=by dsimp only[d];linarith
 have hp3:pnc3Sum m=0:=Ww (by linarith)
 have hp2:fInt (if mod2 then 1/2 else max (1-y) y/2) m≤ d^2/2:=by
  have hL2:(if mod2 then (1/2:ℝ) else max (1-y) y/2)≤1/2:=by
   split_ifs
   ·exact le_rfl
   ·have:max (1-y) y≤1:=max_le (by linarith) (by linarith)
    linarith
  have hL2_nn:0≤(if mod2 then (1/2:ℝ) else max (1-y) y/2):=by
   split_ifs
   ·norm_num
   ·exact div_nonneg (le_trans hy (Yn _ _)) (by norm_num)
  have h1:=Wf hL2_nn hL2 (by linarith:0≤ m)
  have h2:fInt (1/2) m=d^2/2:=by
   unfold fInt
   split_ifs with hlt h2m
   ·linarith
   ·linarith
   ·dsimp only[d]
  linarith
 have hq2b:=Vi (d:=d) (by linarith) hy hsum hd0 hd5 hS1 hS2
 rcases V6 hm1 hm2 hmm1 hy hsum with hqa|hsm
 ·right;left
  change (m1-m1^2/2)+((43/100*y)^2/(114/100))*(1645/1000)+fInt (1-y) m1+d^2/2≤1/2 at hqa;rw[hp3,add_zero]
  have hS_ub:((43/100*y)^2/(114/100))*S≤((43/100*y)^2/(114/100))*(1645/1000) :=Zp hS2 (by positivity)
  have hmax:max ((43/100*y)^2/(114/100)) (y-y^2-(57/100)*m1+(57/200)*m1^2)*S ≤1/2-(m1-m1^2/2)-fInt (1-y) m1-d^2/2:=by
   rw[max_mul_of_nonneg _ _ (by linarith:0≤ S)]
   exact max_le (by linarith only[hqa,hS_ub]) (by linarith only[hq2b])
  change (m1-m1^2/2) +max ((43/100*y)^2/(114/100)) (y-y^2-(57/100)*m1+(57/200)*m1^2)*S +(fInt (1-y) m1+fInt (if mod2=true then 1/2 else max (1-y) y/2) m)≤1/2
  linarith only[hmax,hp2]
 ·right;right;right;left
  change (m-m^2/2)+(1645/1000)*y*(1-y)+fInt (1-y) m1+d^2/2≤1/2 at hsm;rw[hp3,add_zero]
  have hy1y:0≤ y*(1-y):=mul_nonneg hy (by linarith)
  have hS_ub:S*y*(1-y)≤(1645/1000)*y*(1-y):=by nlinarith
  change (m-m^2/2)+S*y*(1-y) +(fInt (1-y) m1+fInt (if mod2=true then 1/2 else max (1-y) y/2) m)≤1/2
  linarith only[hsm,hS_ub,hp2]
namespace CaseBCert
inductive CTree where
 | L (tag:Nat):CTree
 | N (ax:Nat) (mid:Nat) (l r:CTree):CTree
open CTree
def DD:Nat:=27720
def DD2:Nat:=27720*27720
def fInt4 (a b:Nat):Nat :=if a≤ b then 0
 else if 2*b≤ a then a*a-2*b*b
 else 2*(a-b)*(a-b)
def pnc3_4 (m0:Nat):Nat :=fInt4 9240 m0+fInt4 6930 m0+fInt4 5544 m0+fInt4 4620 m0 +fInt4 3960 m0+fInt4 3465 m0+fInt4 3080 m0+fInt4 2772 m0+fInt4 2520 m0
def c4Term (a b:Nat):Nat :=
 let r:=if DD≤ a+b then 0 else DD-a-b
 4*a*b+2*r*r
def boxCheck (mod2:Bool) (m0 m1_0 y0 m_hi m1_hi y_hi tag:Nat):Bool :=if m0>m1_hi || m1_0+y0>DD then tag == 0
 else
  let m_hi:=min m_hi m1_hi
  let m1_0:=max m1_0 m0
  let m1_hi:=min m1_hi (DD-y0)
  let y_hi:=min y_hi (DD-m1_0)
  if m0>m_hi || m1_0>m1_hi || y0>y_hi then tag == 0
  else
   let S_num:Nat:=if mod2 then 247 else 329
   let L2_hi:Nat:=if mod2 then 13860 else (max (DD-y0) y_hi+1)/2
   let p1:=fInt4 (DD-y0) m1_0
   let p2:=fInt4 L2_hi m0
   let p3:=pnc3_4 m0
   let pnc:=p1+p2+p3
   let ym:=max y0 (min y_hi 13860)
   let y1y:=ym*(DD-ym)
   let m1c:=min m1_hi (DD-y0)
   let g4:=4*DD*m1c-2*m1c*m1c+fInt4 (DD-y0) m1c
   match tag with
   | 1=>mod2 && (2*pnc≤ DD2)
   | 2 =>
    (570000*(g4+p2+p3)+1849*S_num*y_hi*y_hi≤1140000*DD2) &&
    ((20000-57*S_num)*(4*DD*m1c-2*m1c*m1c)+20000*pnc+400*S_num*y1y≤40000*DD2)
   | 3=>(200*g4≤271*DD2) && (200*(4*y1y+p1)≤271*DD2)
   | 4=>200*(4*DD*m_hi-2*m_hi*m_hi+fInt4 L2_hi m_hi+p1+p3)+4*S_num*y1y≤400*DD2
   | 5=>200*(DD2+2*DD*m_hi-m_hi*m_hi+pnc)+4*(S_num-200)*y1y≤400*DD2
   | 6 =>
    let cm:=min (DD2+2*DD*m_hi-m_hi*m_hi) (4*DD*m_hi-2*m_hi*m_hi+4*y1y)
    200*(cm+p1)≤271*DD2
   | 7 =>
    let c1:=if 2*m1_0≤ DD-y0 then DD2-2*m1_0*m1_0 else 0
    let c2:=if DD≤2*m1_0 then 2*(DD-m1_0)*(DD-m1_0) else 512265600
    let r3:=if DD≤2*y0+m1_0 then 0 else DD-2*y0-m1_0
    let c3:=4*y1y+2*r3*r3
    let c4:=max (max (c4Term m1_0 y0) (c4Term m1_0 y_hi)) (max (c4Term m1_hi y0) (c4Term m1_hi y_hi))
    200*(4*DD*m_hi-2*m_hi*m_hi+max (max c1 c2) (max c3 c4))≤271*DD2
   | _=>false
def checkTree (mod2:Bool) (m0 m1_0 y0 m_hi m1_hi y_hi:Nat):CTree->Bool
 | L tag=>boxCheck mod2 m0 m1_0 y0 m_hi m1_hi y_hi tag
 | N ax mid l r =>
  let m_hi:=min m_hi m1_hi
  let m1_0:=max m1_0 m0
  let m1_hi:=min m1_hi (DD-y0)
  let y_hi:=min y_hi (DD-m1_0)
  if ax == 0 then
   checkTree mod2 m0 m1_0 y0 mid m1_hi y_hi l && checkTree mod2 mid m1_0 y0 m_hi m1_hi y_hi r
  else if ax == 1 then
   checkTree mod2 m0 m1_0 y0 m_hi mid y_hi l && checkTree mod2 m0 mid y0 m_hi m1_hi y_hi r
  else
   checkTree mod2 m0 m1_0 y0 m_hi m1_hi mid l && checkTree mod2 m0 m1_0 mid m_hi m1_hi y_hi r
def midsLe:CTree->Bool
 | L _=>true
 | N _ mid l r=>decide (mid≤ DD) && midsLe l && midsLe r
namespace T
private abbrev a:=N 0
private abbrev b:=N 1
private abbrev c:=N 2
private abbrev u:=L 0
private abbrev v:=L 1
private abbrev w:=L 2
private abbrev x:=L 3
private abbrev y:=L 4
private abbrev z:=L 5
private abbrev p:=L 6
private abbrev q:=L 7
def f:CTree:=N 2 16940 (b 19250 (b 13603 (c 11293 (b 6074 (c 7528 (c 5018 (c 1672 (a 4192 (b 4192 w (a 2937 (c 836 y (b 5446 w (c 1393 y (b 5760 w y)))) (b 5133 w (c 836 (c 557 y y) w)))) w) (c 2787 w (a 4819 (c 3530 w (b 4819 x (c 4274 w (a 3146 (c 4646 w (b 5446 x w)) w)))) w))) (c 6691 (c 5854 (c 5296 (c 5110 (c 5048 (b 4819 x w) x) x) x) x) x)) (c 9410 (c 8782 (c 8155 x x) x) (c 10351 (c 9880 x x) x))) (c 7528 (a 7392 (b 11093 (c 5018 (a 5698 (b 7747 (c 1672 (a 4568 (a 3815 (c 557 y (c 928 y (b 7189 (a 3313 (c 1300 y (a 2978 y y)) (c 1300 y (b 6817 w y))) (a 3062 y (c 1300 y y))))) (c 557 y (c 928 y (b 6910 w (c 1300 y (a 4066 y w)))))) (c 1114 (c 371 y (b 6910 w (c 742 y (a 4944 y w)))) w)) (a 4568 (c 3345 (a 3815 (b 7189 (a 3313 (c 2787 (b 6817 (c 2229 (a 2811 (b 6321 w (c 1950 y (a 2560 y w))) w) w) (c 2043 (a 2811 y (a 3145 y w)) (a 2811 (c 2539 (c 2208 y (a 2644 (c 2373 y (b 7065 w q)) w)) w) w))) w) w) (c 2787 (a 3313 (c 2043 (a 2811 y (a 3145 y y)) (a 2978 (c 2291 (a 2755 y y) (a 2755 (c 2621 (a 2532 q (c 2456 y (b 7375 w q))) q) (b 7468 w (c 2539 (c 2456 y y) w)))) (c 2291 (c 2208 y y) w))) (c 2043 (c 1857 y (b 7561 w y)) w)) (a 2811 (a 2560 (b 7468 w q) w) w))) w) (c 4181 w (c 4739 w w))) (c 3345 w w))) (c 1672 (a 4568 (c 557 y (b 9977 (a 3815 (c 1114 y (a 3313 y y)) (c 1300 y (a 4066 y y))) (a 3815 y y))) (c 557 y (c 928 y (b 9977 (b 9233 (b 8737 (a 4944 (c 1424 y (b 8242 w y)) (c 1300 (a 5446 y w) w)) (c 1300 y (a 5133 y (a 5509 y w)))) (c 1424 y (a 4944 y y))) (a 4944 y y))))) (a 4568 (b 9977 (c 3345 (a 3815 (b 9233 (c 2787 (a 3313 (b 8737 (c 2043 (a 2978 y y) (a 2978 (c 2291 y (b 8242 (a 2644 q (c 2539 (a 2866 y y) q)) q)) (c 2291 y (b 8242 (c 2456 (a 3145 y y) (c 2676 (a 3201 (c 2566 y (b 7912 w q)) w) w)) (c 2539 y q))))) (c 2415 (c 2043 y q) q)) (b 8737 (c 2043 (a 3480 y y) (b 8242 (c 2415 (a 3647 (c 2229 y (a 3480 y w)) w) w) (c 2291 (a 3480 y y) (a 3480 (c 2539 y (b 8489 w q)) (c 2539 (c 2415 y (b 8572 w y)) w))))) (c 2043 y (c 2291 y (c 2456 y (a 3480 q (c 2566 y (a 3647 q (b 8985 w (c 2713 y w)))))))))) (a 2811 q (b 8737 (a 3313 (b 8077 w (c 3066 (c 2880 q q) q)) w) (a 3313 q (c 3066 (a 3647 q w) w))))) (c 2787 (a 2811 q (c 2043 y (a 3313 q (c 2415 y (c 2601 y q))))) (c 3066 q q))) (b 9233 (c 2787 (b 8737 (c 2415 (b 8242 (c 1919 (a 4066 y w) w) (a 4066 (c 2043 y (c 2229 y w)) (c 2043 (c 1919 y (a 4400 y w)) w))) w) (c 2043 (a 4317 y y) (a 4066 (c 2291 y (c 2621 (c 2456 y (b 9067 w y)) w)) (c 2415 (a 4400 (c 2229 y (b 9067 w y)) w) w)))) w) (c 2787 (c 2043 y (a 4066 (c 2415 y (c 2663 y (a 3898 y y))) (c 2291 y (b 9481 (a 4317 (c 2539 y w) w) (c 2456 y (a 4400 (c 2621 y (a 4233 y w)) (c 2621 w w))))))) (a 4191 (c 3066 (a 4065 (b 9481 w q) w) w) w)))) (a 3815 (b 9233 (a 3313 (c 4460 (c 4088 (a 2811 q (b 8737 w q)) q) w) w) (c 4460 (a 3313 q (c 3716 q w)) q)) w)) (c 3345 (a 3815 (c 2787 (c 2229 q q) q) (c 2229 y (b 10721 (c 2601 (a 4317 y y) (a 4066 (c 2849 y q) (b 10225 (c 2973 (c 2725 y (a 4317 q w)) w) (c 2849 (a 4400 y y) (c 3179 (a 4400 q w) w))))) (c 2601 y (c 2973 q q))))) (a 3062 q (c 4460 (a 3564 q (c 3902 (a 4066 q (c 3530 w w)) w)) (a 4066 q w))))) (c 3345 (b 9977 (c 2508 (b 8490 w (b 9481 (a 5133 (c 2090 (b 8820 w (c 1881 y (a 4850 y w))) w) w) (a 4944 (c 2090 y (c 2299 y (a 4693 y w))) (c 2090 (c 1881 y (a 5321 y w)) w)))) w) (c 2787 (a 4944 (c 2229 y (c 2508 y (b 10721 (a 4818 (b 10349 (c 2601 w w) y) w) y))) (b 10721 (c 2415 (c 1919 y (c 2084 y (a 5321 (c 2304 y y) w))) w) (c 2043 y (c 2291 y (a 5321 (c 2539 y w) w))))) (a 4944 (a 4693 (b 10721 w (c 3066 y w)) w) w))) w)))) (c 2509 (b 7747 (a 6262 (c 836 (c 418 y w) w) w) (b 9977 (c 1672 (b 9233 (c 1114 (a 6545 (c 557 y (c 835 y (b 8737 w y))) (c 557 (c 371 y y) w)) w) (c 557 y (a 6545 (c 1114 y (a 6262 (c 1486 y w) w)) (c 1114 (c 928 y w) w)))) w) (c 1672 (c 557 y (c 928 y (c 1176 y (a 6262 y (a 7015 (c 1424 y (b 10721 w y)) w))))) (a 6262 (c 2090 (c 1881 y (b 10721 w y)) w) w)))) w)) (a 5698 (b 7747 (a 4568 (c 6273 (a 3815 (b 7189 (a 3313 (c 5436 (a 2644 q w) (b 6817 (b 6321 x (a 2644 q (c 5715 w (b 6569 x (a 2978 q (c 5994 w w)))))) (a 2811 q (c 5854 w (a 3145 q w))))) (c 5645 w (b 6445 x w))) (c 5436 w (a 3313 (a 2978 q (c 5994 w w)) w))) (c 5436 w w)) (b 6910 x (a 3815 (a 2811 q (c 6691 (a 3313 (c 6482 q q) w) (b 7328 x (c 7249 (a 3313 q (c 6970 w w)) x)))) (c 6900 w (b 7328 x w))))) (c 6273 w (c 6900 w w))) (a 4568 (b 9977 (c 6273 (a 3815 (c 5436 w (a 3062 q (b 9233 w w))) w) (a 3062 q (c 6691 w (b 9233 (a 4066 (c 6970 w (b 8737 (a 3731 (a 3396 q (c 7249 w w)) w) w)) w) w)))) (c 6273 (a 3062 q w) (a 3062 q w))) (c 6273 w w))) (c 6273 w w))) (c 5018 (a 5698 (c 1672 (a 4004 y (c 1114 y y)) (a 4568 (c 3345 (a 3439 q (c 2787 (c 2229 y q) q)) (a 3439 q (c 4460 (c 3902 q q) q))) (c 3902 (b 11929 (c 2787 (c 2229 y (c 2415 y (a 5133 y (c 2663 y w)))) (c 3344 (a 5133 (c 3158 (c 2972 y (a 4944 q w)) w) w) w)) (c 2415 y (b 13045 (c 2910 (a 5321 y y) (c 3571 (a 5321 (a 4819 q (c 3240 y w)) w) w)) (c 3158 y (a 5133 q w))))) w))) (c 3345 (c 1672 (c 836 y (b 11929 (c 1393 y (a 6545 y y)) y)) (c 2787 (b 11929 (c 2415 (a 6827 (c 1919 y (a 6262 (c 2249 y w) w)) w) w) (a 6545 (c 2229 y (b 12766 (a 5980 y w) y)) (c 2043 y w))) w)) w)) (a 4851 (a 3157 q (c 6273 (a 3721 q w) w)) w))) (c 5018 (c 2509 (c 1672 (b 10497 (c 836 (b 8944 w (a 9462 (a 8082 (c 418 y (c 627 y (b 9720 w y))) (c 418 (b 9461 w (a 8542 y (b 9979 w (c 209 y w)))) w)) w)) w) (a 10780 (a 8521 (c 557 y (b 12050 (c 1300 (c 804 y (c 969 y (a 7956 (b 11014 w y) w))) w) (c 1300 y (a 7768 y w)))) (c 1114 (b 12050 (c 742 (a 9650 (c 371 y (b 11532 (c 618 (a 9273 y w) w) y)) (c 371 (b 11273 (c 185 (a 10215 y w) w) (a 10215 y (c 185 y (b 11661 w y)))) w)) w) (c 371 y (a 9650 (c 866 y (b 12826 w y)) (c 618 (b 12567 (a 10026 y w) y) w)))) w)) (c 557 (c 371 (b 11721 (c 123 (a 11093 (b 11407 w y) w) w) (b 12348 (c 185 (a 11825 (a 11128 y (c 123 (a 11476 y (b 12139 w y)) w)) w) w) (a 11344 (c 185 y y) (c 247 (b 13184 (a 11720 (c 123 y y) (c 164 (b 12905 (c 109 (a 11971 y (c 72 (b 12719 (c 36 (a 12306 y w) w) y) w)) w) (c 82 y y)) w)) (c 82 y y)) w)))) w) w))) w) w) w)) (a 9086 (b 11093 (a 4568 (b 7747 (c 9410 x x) (c 9410 (b 9977 (a 3815 (a 2811 q (b 9233 (c 8155 (a 3313 q (b 8737 (b 8242 (c 7841 (a 3480 q w) x) (c 7841 w (a 3480 q w))) (c 7841 w w))) (b 8490 x (c 8991 (a 3313 q (c 8712 (a 3480 q (c 8433 w w)) (b 8985 x w))) x))) (c 8155 (a 3313 q w) (a 3145 q (c 8573 w (c 8852 w (a 3591 (a 3368 q (c 9224 w w)) w))))))) (b 9233 (c 8155 (c 7841 w w) (b 8490 x (c 8782 w (b 8737 x w)))) (c 8469 w (c 9096 w w)))) (a 3062 q (c 8155 w (a 3815 (c 8782 w (a 3313 q w)) w)))) (b 9420 x (a 3815 (a 2811 q (c 10665 (b 10256 (c 10037 (b 9838 x (a 3313 (a 3145 q (c 9828 w w)) w)) x) (c 9828 (a 3145 q w) (a 3313 (a 2978 q (c 10386 (c 10200 w w) w)) w))) (b 10535 x (a 3145 p w)))) (c 10665 (c 9828 w w) w))))) (b 7747 (c 9410 x x) (a 6074 (c 9410 (b 9977 (c 8469 w (b 8490 x w)) w) (b 9420 x (c 10665 w w))) (c 9410 w (b 9977 w w))))) (a 5698 (c 9410 (a 4004 (a 3157 q (c 8155 w w)) w) (a 4004 (a 3157 p (c 10351 w w)) w)) w)) w))) (b 9838 x (a 5698 (b 11093 x (a 4004 p (c 14849 w w))) w))) (c 4705 (a 7392 (b 16426 (a 5698 (c 1568 y (a 3439 q (c 2613 y (a 4192 q (c 3310 y (a 4694 q (c 3775 y (a 5028 q (c 4240 (b 14544 w y) w))))))))) (c 1568 y (c 3659 (c 2265 y (c 2729 y (a 6545 (c 3349 y w) w))) w))) (c 1568 y (a 4004 p (c 2613 y (a 5133 q (c 3659 y (a 5886 y (a 6639 (b 17367 w y) w)))))))) (c 3136 (b 16426 (c 2090 (a 10780 (c 696 y (a 8521 (c 1393 y y) (c 1393 (b 14544 (a 9650 y w) y) w))) (c 696 (b 15014 (c 348 y w) y) w)) w) (c 1045 y (a 10780 (c 1742 y (a 8521 y w)) w))) w)) (a 7392 (c 7842 (b 16426 (a 5698 (a 3439 q (c 6273 (a 4192 q (a 5196 (c 5227 q (a 4694 (b 14544 w q) w)) w)) (a 4568 (a 4003 q (b 15485 w (c 7057 (c 6665 q w) w))) w))) w) (a 5698 (a 3439 p (c 6273 (a 4568 q (b 18308 (b 17680 (c 5489 (a 5321 q w) (a 5133 (c 6011 q (a 4944 q w)) w)) (c 5227 y (a 4944 q (c 5575 y (a 5321 (c 6040 z z) w))))) (c 5227 y (a 4944 q (c 5750 z (a 5321 z z)))))) (a 4192 p (b 18308 (b 17680 (a 5196 (c 7057 (a 4861 (a 4415 q (b 16844 w (b 17401 (a 4638 (c 6665 q p) w) (a 4712 p (c 6665 w w))))) w) (a 4694 (b 16844 w p) w)) w) (a 4694 p (c 7057 (a 5196 (c 6665 (a 4945 z z) (a 4945 z w)) w) (a 5028 p w)))) (a 4945 p (c 7057 (a 5447 (c 6665 z (a 5112 z z)) z) (a 5196 p (b 18936 (a 5447 (c 7449 z (b 18726 w z)) w) (c 7318 z (a 5447 z z)))))))))) (c 6273 (b 17838 w (a 6545 (c 5750 (a 6121 (b 18308 w z) w) w) w)) (c 7057 w w)))) (c 12025 (b 16426 (a 5698 (a 3439 p (c 9236 (a 4192 (b 14544 w p) w) (b 14544 w (a 4568 p (c 10165 w w))))) w) (a 4851 p (c 9568 (a 6545 (b 17367 w (b 17994 (a 5415 (c 8705 w (c 9136 w w)) w) (c 8992 (a 5980 (a 5227 p (b 18412 w (c 8608 (a 5729 (b 18970 (a 5478 (a 5352 p (b 18784 w (c 8225 w (c 8416 w w)))) w) (a 5394 p (c 8352 (a 5617 (c 8097 z (a 5505 z z)) w) (a 5617 (b 19156 (a 5505 (c 8480 z (a 5449 z z)) w) (a 5468 z (a 5542 z (c 8458 w w)))) w)))) w) (a 5603 (a 5415 p (b 18878 w (b 18995 w (b 19073 w w)))) w)))) w) (a 5698 (a 5415 p (b 18361 w w)) w)))) w) (a 6121 (c 10431 (a 5274 p w) w) w)))) (a 4851 p w))) (c 10979 (c 7842 w (b 17367 w w)) w)))) (a 7392 (b 24896 (c 4235 (a 4851 p (c 2823 y y)) (a 4004 p (b 22073 (c 6352 (a 5698 (c 5293 y (a 4851 p (c 5999 z z))) (b 21132 (c 4940 (a 6545 y z) (b 20504 (a 6545 (c 5646 z (a 6121 z z)) (c 5646 z w)) (a 6262 z (c 5881 z (a 6827 z z))))) (c 4940 y (a 6827 (c 5881 z z) z)))) (a 5133 p (a 5886 (b 19956 (c 7058 (a 5384 z z) (c 7528 (a 5509 z z) (a 5384 p (c 7842 (a 5635 z z) (b 19668 (c 8051 (a 5635 z z) (a 5635 (b 19528 (c 8190 z (a 5551 (a 5495 z z) z)) z) (c 8330 (a 5760 z (b 19459 w z)) (a 5718 z w)))) (a 5635 z z)))))) (b 20897 (c 6822 z (b 20583 (a 5384 z (b 20269 (c 7293 z (a 5635 z z)) z)) z)) z)) (b 19956 (a 6890 (c 7058 (a 6220 z w) (c 7528 (a 6220 z w) (a 6555 (c 8156 (a 6220 (b 19485 w (c 7737 z (c 8016 (a 6108 z w) w))) w) w) w))) w) (a 6890 (b 20897 (c 7058 (a 6388 z (b 20269 w z)) (a 6555 (a 6109 z (b 20309 (c 7411 z (a 6332 z z)) z)) (b 20309 w z))) (a 6555 z z)) (c 7058 (c 6822 z w) w)))))) (a 6262 (a 5133 y z) z)))) y) (b 24896 (c 4235 (c 1411 y (b 22073 (a 10780 (c 2352 y (a 9650 (c 3293 y (a 8521 z w)) w)) (c 2352 w w)) (c 2352 y (a 9086 z (a 10215 z (c 3607 (b 23484 w (a 11721 z (b 24425 w w))) w)))))) (a 10780 (b 22073 (c 6352 (a 9086 (b 20191 w (c 4940 (b 21132 w z) (a 8521 (b 20818 w (c 5646 z (b 21445 w (a 8144 z w)))) w))) w) (b 20309 w (b 20838 w w))) (a 8521 (c 5176 z z) (c 5176 (c 4862 (a 9650 z w) w) w))) (c 6352 (c 4940 w w) w))) (a 10780 y z)))) x
def t:CTree:=N 2 16940 (b 19250 (b 13603 (c 11293 (b 6074 (c 7528 (c 5018 (c 1672 (a 4192 (b 4192 w (a 2937 (c 1114 y y) (b 5133 w (c 836 y (a 3355 y w))))) w) (a 4192 (b 4192 (c 3345 w x) (c 3345 (c 2229 (c 1857 (a 2937 y w) w) w) (b 4819 x (c 3902 w (a 3564 (c 4274 w (b 5446 x (a 2937 (c 4646 w (c 4894 w w)) w))) w))))) (c 3345 w w))) (c 6691 (c 5854 (c 5296 (c 5110 (c 5048 (a 3564 (c 5028 (c 5021 (b 4819 x (b 5237 w w)) x) x) w) x) x) x) x) x)) (c 9410 (c 8782 (c 8155 x x) x) (c 10351 (c 9880 x x) x))) (c 7528 (a 7392 (b 11093 (c 5018 (a 5698 (b 7747 (c 1672 (a 4568 (a 3815 (c 836 y (a 3313 y y)) (c 836 y (c 1393 y y))) (c 1114 (c 557 y (b 7189 w y)) w)) (a 4568 (c 3345 (a 3815 (b 7189 (c 2787 (a 3313 (c 2043 y (b 6817 (a 2978 (c 2415 y (b 6569 w y)) w) (c 2415 y (a 2978 y w)))) (c 2043 y w)) (a 2811 (b 6817 w (c 3159 y w)) w)) (c 2787 (a 3313 (c 2229 y (a 2978 y y)) (c 2229 y (c 2601 y w))) (a 3313 (a 2644 y (a 3090 (c 3159 y y) w)) w))) (c 2229 (a 4066 (b 7189 w y) w) w)) (a 3815 (b 7189 (c 3902 w (a 3313 (c 4274 w (c 4522 w (a 2811 (c 4852 (b 6445 w q) q) w))) w)) (c 4460 (a 2811 (c 3902 (c 3530 q q) w) w) (a 2811 q w))) (b 7189 w w))) (c 3345 w w))) (c 1672 (a 4568 (c 836 y (a 3815 y y)) (c 836 y (b 8862 (c 1393 y (a 4944 y y)) y))) (a 4568 (b 9977 (c 3345 (a 3815 (b 9233 (c 2787 (a 2811 y (c 2229 y (a 3313 y y))) (a 2811 y (a 3145 y (c 2973 y (a 3480 y (b 8242 w y)))))) (c 2508 y (a 3313 y y))) (b 9233 (c 2787 (c 2043 y (c 2291 y (b 8737 (b 8077 w (c 2539 y (a 4066 y w))) y))) (b 8490 w (a 4317 (c 3066 y (b 8861 w y)) w))) (c 2508 y (c 3066 y (a 4066 y y))))) (a 3815 (b 9233 (c 4460 (a 3313 (c 4088 (a 2811 q (b 8737 (c 3840 (c 3592 (a 3145 y y) q) q) q)) q) (c 4088 (b 8490 w (b 8737 (c 3592 (a 3480 y w) w) (c 3840 (c 3592 y q) q))) w)) (a 3062 q w)) (c 4460 (a 3313 q (c 3902 (c 3530 y y) q)) q)) (c 4181 (b 8862 w (c 3902 (a 4317 (b 9233 w (c 3623 y (b 9605 w y))) w) w)) w))) (c 3345 (a 3062 y (c 2508 y (a 4066 y y))) (a 3062 q (c 4460 (a 3564 q (b 10721 (c 4088 (a 3898 y (c 3716 y (a 4344 y y))) (a 4233 q w)) (c 3902 y (a 4233 y y)))) (a 4066 q w))))) (c 3902 (b 9977 (c 3158 (b 9233 (c 2662 (b 8242 w (a 4944 (c 2332 y (b 8737 w y)) (c 2167 (a 5321 y w) w))) w) (c 2167 y (a 4944 (c 2827 y y) (c 2662 (a 5446 y w) w)))) w) (c 2415 y (c 2910 (a 5321 y y) (a 4944 (c 3406 y (b 10349 w y)) (c 3406 (a 5321 (b 10349 w y) w) w))))) w)))) (c 3345 (b 7747 (a 6262 (c 1115 (c 371 y w) w) w) (b 9977 (c 2230 (b 9233 (c 1486 (a 6545 (c 743 y (c 1114 y (b 8737 w y))) (c 743 (c 495 y y) w)) w) (c 743 y (a 6545 (c 1486 y (c 1858 y w)) (c 1238 y w)))) w) (c 1672 (c 836 y (c 1393 y y)) (c 2787 (a 6827 (c 2043 y (a 6262 (c 2539 y w) w)) w) w)))) w)) (a 5698 (b 7747 (a 4568 (c 6273 (a 3815 (b 7189 (a 3313 (c 5436 (a 2644 q (a 3090 (c 5157 w (b 6631 (b 6352 w w) q)) w)) (b 6817 (b 6321 x (a 2644 q (c 5994 (a 3090 (c 5808 (a 2941 q (b 6569 w w)) q) (c 5808 w w)) (a 3090 q (b 6569 w w))))) (a 2811 q (c 5715 w (a 3062 q (c 6087 w w)))))) (c 5645 w (c 5959 w (b 6817 w w)))) (a 3313 (c 5854 (a 2811 q (c 5436 w (a 3145 q w))) q) (c 5645 w (c 6063 w w)))) (c 5645 w (b 7189 w w))) (b 6910 x (a 3815 (a 2811 q (c 6691 (a 3145 q (a 3591 (b 7328 (a 3442 (c 6551 (b 7119 w w) q) w) (a 3368 q (b 7537 w w))) w)) (b 7328 x (c 7249 (a 3313 q (c 6877 w (a 3647 (c 7001 w (a 3480 q (b 7537 w w))) w))) x)))) (c 6691 w (b 7328 x (c 7249 w w)))))) (c 6273 w (c 6900 w w))) (a 4568 (b 9977 (c 6273 (a 3815 (a 2811 q (b 9233 (b 8737 (c 5436 (a 3145 q w) (a 3145 q (c 5854 w (b 8242 w w)))) (c 5645 w (a 3145 q w))) (c 5645 q q))) (c 5645 w (b 9233 w w))) (a 3062 q (b 9233 (a 4066 (b 8737 (c 6691 (a 3564 (c 6482 q q) w) (a 3731 (a 3285 q (b 8242 (c 7249 (c 6877 w (a 3508 q (b 7912 w w))) (a 3582 q (b 7912 w w))) (c 6970 q (a 3582 q (c 7249 w w))))) (c 6970 w (c 7249 w (b 8242 w w))))) (c 6691 (a 3731 q w) (a 3564 q (c 7249 w w)))) (c 6900 w (b 8490 w w))) (a 4066 (a 3396 q (c 6691 w (c 7109 w (b 9481 w w)))) (c 6691 w w))))) (c 6273 (a 3439 q (a 3815 (c 5436 q w) w)) (a 3439 q (c 6900 w (a 3815 q w))))) (c 5854 w (b 9977 (c 6691 w (b 9233 w w)) w)))) (b 9420 (c 6273 w (b 8304 w w)) w))) (c 5018 (a 5698 (c 1672 (a 4568 y y) (a 4568 (c 3345 (a 3439 y (c 2787 y y)) (a 3439 q (c 4460 (c 3902 y q) q))) (c 2787 y (b 11929 (c 4274 (c 3282 y (c 3612 y (a 5133 (c 3832 y y) w))) w) (c 3530 y (c 4026 y (a 5321 (c 4687 y y) w))))))) (c 1672 (c 1114 y y) (c 3902 (b 11929 (c 3158 (c 2167 y (a 6545 (c 2827 y w) w)) w) (c 2415 y (c 3406 (c 2910 y (a 6545 y w)) w))) w))) (a 5698 (a 4568 (a 3062 q (b 11929 (c 6273 (a 3815 q (c 5436 q w)) (a 3564 q w)) (c 6273 (a 4066 q (c 5645 y (b 13045 w y))) (a 3815 q (a 4191 (b 12766 w z) w))))) (c 5854 (c 5296 w w) w)) w))) (c 5018 (c 2509 (b 10497 (c 1254 (b 8944 w (a 9462 (a 8082 (c 627 y (b 9979 w (a 7737 y y))) (c 627 (b 9461 w (a 8542 y (c 313 (b 9979 w y) w))) w)) w)) w) (a 10780 (a 8521 (c 836 y (c 1951 (b 12567 (c 1207 y (a 8144 (b 11532 (c 1579 y w) y) w)) y) w)) (c 1254 (b 12050 (a 9650 (c 418 y (c 975 (b 11532 (c 696 (a 9273 y w) w) y) w)) (c 627 (c 418 (b 11273 (a 10215 (c 209 y w) w) (a 10403 y (c 209 y w))) w) w)) (c 418 y (a 9274 y (c 836 (c 696 y y) w)))) w)) (c 836 (c 418 (b 11721 (c 139 (c 46 (c 15 (a 11093 (b 11250 w y) w) w) w) w) (b 12348 (c 209 (a 11825 (a 11302 y (c 104 (b 12034 w y) w)) w) w) (a 11344 y (c 278 (b 13184 (a 11720 y (c 139 (b 12905 (a 11971 y (c 69 (b 12626 (a 12138 y w) y) w)) y) w)) y) w)))) w) w))) w) (b 10497 w w))) (a 9086 (b 11093 (a 4568 (b 7747 (c 9410 x x) (c 9410 (b 9977 (a 3815 (a 2811 q (b 9233 (c 8155 (a 3313 q (b 8737 (b 8242 (c 7841 (b 7994 x (a 3564 q (c 7632 w w))) x) (a 3480 q (c 7841 (a 3647 q (b 8489 w w)) (a 3591 q (b 8572 (c 7998 w (b 8352 w w)) w))))) (a 3564 q (c 7737 w (c 7946 w (b 8985 w w)))))) (b 8490 x (c 8991 (a 3313 q (c 8712 (a 3480 q (b 8737 (c 8340 (a 3647 (b 8572 x q) w) x) (c 8433 (a 3591 q (b 8985 (c 8340 w w) w)) (b 8985 (c 8572 (a 3591 q w) x) (a 3647 (a 3563 q (c 8619 w w)) w))))) (c 8805 (b 8985 x (a 3564 q w)) x))) x))) (c 8155 (a 3480 q (c 7841 q (b 9481 w w))) (a 3145 q (c 8573 (a 3591 q (b 9605 (c 8433 w w) w)) (c 9131 (a 3368 q (b 9481 (c 8945 (a 3517 q (a 3715 (c 8697 w (c 8821 w w)) w)) (a 3591 (b 9357 x (c 9038 (a 3442 q w) x)) w)) (c 8945 (a 3517 q (a 3715 (b 9811 (c 8759 w w) w) w)) (a 3666 (a 3467 q (b 9729 (b 9563 w w) w)) w)))) (b 9481 x (a 3368 q (b 9729 (a 3666 (c 9317 (a 3566 (b 9563 x (a 3500 (a 3412 q (c 9193 w (b 9646 (c 9234 w w) w))) w)) w) x) w) (a 3591 (a 3516 (c 9270 (a 3417 z z) z) z) w)))))))))) (b 9233 (c 8155 (b 8737 (b 8242 (c 7841 w x) (c 7841 w w)) (c 7841 w w)) (b 8490 x (c 8991 (c 8712 (a 4191 (c 8340 w (b 8861 (c 8464 w w) w)) w) (b 8861 x w)) x))) (c 8155 (b 9481 w w) (c 8573 (b 9481 w w) (c 8852 w (a 4191 (b 9729 (c 9131 w w) w) w)))))) (a 3062 q (c 8155 (a 3815 (c 7841 q q) w) (a 4066 (c 8573 (a 3564 q (b 10349 w w)) (b 10721 (a 3731 (a 3285 q (c 9131 (a 3433 q (b 10225 (c 8852 w (a 3532 z w)) (c 8852 w (b 10473 w w)))) (a 3508 z z))) (c 8991 w (b 10225 w w))) (a 3731 (a 3396 (c 9131 z z) z) w))) (c 8782 w w))))) (b 9420 x (a 3815 (a 2811 q (c 10665 (b 10256 (c 10037 (b 9838 x (a 3145 q (a 3591 (a 3368 (c 9828 z z) z) z))) x) (a 3480 (a 3145 z z) z)) (b 10256 x z))) (c 10037 (b 10256 (a 4191 (b 9838 x (c 9828 w v)) w) v) v))))) (a 7580 (b 7747 (c 9410 x x) (c 9410 (b 9977 (a 6576 (b 9233 (c 8155 w (a 5572 (b 8490 x (c 8573 w w)) w)) (c 8469 w w)) w) (c 8155 w w)) (b 9420 x v))) v)) (a 4568 (c 9410 (a 3062 q (b 11929 (c 8155 (a 3564 q w) (a 4066 (a 3731 (a 3396 (c 8573 z z) z) z) v)) (a 3815 (c 8155 q z) v))) (a 3439 (a 3062 p z) v)) v)) v))) (a 5698 (b 9838 x (a 3439 p v)) v)) (c 9411 (a 7392 (c 3137 (a 4004 y (c 2091 y (a 5698 y y))) (c 6274 (b 16426 (a 5698 (a 3439 q (c 4182 y (a 4192 q (b 15014 (c 5576 (c 5111 y y) v) v)))) (a 6262 (c 4705 y v) v)) (a 4004 y v)) (a 4004 (b 16426 (a 3157 q (c 7842 z v)) z) v))) (c 3137 (b 16426 (c 2091 (a 10780 (c 1045 y (a 9650 y v)) (b 14544 (c 697 (c 464 y w) v) v)) v) v) v)) v)) (a 5698 (c 4235 y v) v)) x
end T
abbrev treeF:=T.f
abbrev treeT:=T.t
theorem okF:checkTree false 2310 2310 0 12474 27720 27720 treeF=true:=by decide
theorem okT:checkTree true 2310 2310 0 12474 27720 27720 treeT=true:=by decide
theorem midsF:midsLe treeF=true:=by decide
theorem midsT:midsLe treeT=true:=by decide
private lemma Q7 {a b c:ℝ} (hc:0≤ c):max a b/c=max (a/c) (b/c):=by
 rcases le_total a b with h|h
 ·rw[Yi h,Yi (div_le_div_of_nonneg_right h hc)]
 ·rw[Yk h,Yk (div_le_div_of_nonneg_right h hc)]
private lemma Wl {a b c:ℝ} (hc:0≤ c):min a b/c=min (a/c) (b/c):=by
 rcases le_total a b with h|h
 ·rw[Yl h,Yl (div_le_div_of_nonneg_right h hc)]
 ·rw[Yj h,Yj (div_le_div_of_nonneg_right h hc)]
private lemma X8 (a b:Nat) :(fInt4 a b:ℝ)/(4*(DD2:ℝ))=fInt ((a:ℝ)/(DD:ℝ)) ((b:ℝ)/(DD:ℝ)):=by
 have hD:(0:ℝ)<(DD:ℝ):=by norm_num[DD]
 have hD2:(DD2:ℝ)=(DD:ℝ)^2:=by norm_num[DD,DD2]
 rw[hD2];unfold fInt4
 by_cases h1:a≤ b
 ·rw[if_pos h1,Nat.cast_zero,zero_div]
  exact (W9 (div_nonneg (Nat.cast_nonneg _) hD.le)
   (div_le_div_of_nonneg_right (by exact_mod_cast h1) hD.le)).symm
 ·rw[if_neg h1]
  have hlt_b:(b:ℝ)/(DD:ℝ)<(a:ℝ)/(DD:ℝ) :=(div_lt_div_iff_of_pos_right hD).mpr (by exact_mod_cast (by omega:b< a))
  unfold fInt;rw[if_neg (not_lt.mpr hlt_b.le)]
  by_cases h2:2*b≤ a
  ·have h2R:2*((b:ℝ)/(DD:ℝ))≤(a:ℝ)/(DD:ℝ):=by
    rw[←mul_div_assoc];exact div_le_div_of_nonneg_right (by exact_mod_cast h2) hD.le
   rw[if_pos h2,if_pos h2R]
   have hsub:2*b*b≤ a*a:=by nlinarith
   rw[Nat.cast_sub hsub];push_cast;field_simp;ring
  ·have h2R:¬ 2*((b:ℝ)/(DD:ℝ))≤(a:ℝ)/(DD:ℝ):=by
    intro h;apply h2
    have:2*(b:ℝ)≤(a:ℝ):=(div_le_div_iff_of_pos_right hD).mp (by simpa [mul_div_assoc] using h)
    exact_mod_cast this
   rw[if_neg h2,if_neg h2R]
   have hle:b≤ a:=by omega
   rw[Nat.cast_mul,Nat.cast_mul,Nat.cast_sub hle];push_cast;field_simp;ring
private lemma Kq (m0:Nat) :(pnc3_4 m0:ℝ)/(4*(DD2:ℝ))=pnc3Sum ((m0:ℝ)/(DD:ℝ)):=by
 unfold pnc3_4 pnc3Sum
 simp only[sum_Icc_succ_top (by decide:3≤4),sum_Icc_succ_top (by decide:3≤5),sum_Icc_succ_top (by decide:3≤6),sum_Icc_succ_top (by decide:3≤7),sum_Icc_succ_top (by decide:3≤8),sum_Icc_succ_top (by decide:3≤9),sum_Icc_succ_top (by decide:3≤10),sum_Icc_succ_top (by decide:3≤11),Icc_self,Finset.sum_singleton]
 push_cast;simp only[add_div,X8];norm_num[DD]
private lemma Vm {y y0 y1:ℝ} (hy0:y0≤ y) (hy1:y≤ y1) :y*(1-y)≤ max y0 (min y1 (1/2))*(1-max y0 (min y1 (1/2))):=by
 by_cases h1:y1≤1/2
 ·rw[Yl h1,Yi (hy0.trans hy1)];nlinarith
 ·push Not at h1
  rw[Yj h1.le]
  by_cases h2:1/2≤ y0
  ·rw[Yk h2];nlinarith
  ·push Not at h2
   rw[Yi h2.le];nlinarith[sq_nonneg (y-1/2)]
private lemma V8 {a a0 a1 b:ℝ} (ha0:a0≤ a) (ha1:a≤ a1) :a*b+(max 0 (1-a-b))^2/2 ≤ max (a0*b+(max 0 (1-a0-b))^2/2) (a1*b+(max 0 (1-a1-b))^2/2):=by
 rcases eq_or_lt_of_le (ha0.trans ha1) with heq|hlt
 ·have:a=a0:=le_antisymm (ha1.trans heq.symm.le) ha0
  rw[this];exact Ym _ _
 ·set t:ℝ:=(a-a0)/(a1-a0)
  have ht0:0≤ t:=div_nonneg (by linarith) (by linarith)
  have ht1:t≤1:=(div_le_one (by linarith)).mpr (by linarith)
  have ha_eq:a=(1-t)*a0+t*a1:=by dsimp only[t];field_simp[sub_ne_zero.mpr hlt.ne'];ring
  set u:=max 0 (1-a0-b);set v:=max 0 (1-a1-b)
  have hm_le:max 0 (1-a-b)≤(1-t)*u+t*v:=by
   refine max_le (by have hu:0≤ u:=Ym _ _;have hv:0≤ v:=Ym _ _;nlinarith) ?_
   have hu:1-a0-b≤ u:=Yn _ _;have hv:1-a1-b≤ v:=Yn _ _
   have:1-a-b=(1-t)*(1-a0-b)+t*(1-a1-b):=by rw[ha_eq];ring
   nlinarith
  have hsq:(max 0 (1-a-b))^2≤(1-t)*u^2+t*v^2:=by
   have h1:=pow_le_pow_left₀ (Ym _ _) hm_le 2
   have h2:((1-t)*u^2+t*v^2)-((1-t)*u+t*v)^2=t*(1-t)*(u-v)^2:=by ring
   have h3:0≤ t*(1-t)*(u-v)^2:=by positivity
   linarith
  have hconv:a*b+(max 0 (1-a-b))^2/2 ≤(1-t)*(a0*b+u^2/2)+t*(a1*b+v^2/2):=by
   have:a*b=(1-t)*(a0*b)+t*(a1*b):=by rw[ha_eq];ring
   linarith
  have hmax1:a0*b+u^2/2≤ max (a0*b+u^2/2) (a1*b+v^2/2):=Ym _ _;have hmax2:a1*b+v^2/2≤ max (a0*b+u^2/2) (a1*b+v^2/2):=Yn _ _;nlinarith
private lemma Kr {a a0 a1 b b0 b1:ℝ} (ha0:a0≤ a) (ha1:a≤ a1) (hb0:b0≤ b) (hb1:b≤ b1) :a*b+(max 0 (1-a-b))^2/2 ≤ max (max (a0*b0+(max 0 (1-a0-b0))^2/2) (a0*b1+(max 0 (1-a0-b1))^2/2))
     (max (a1*b0+(max 0 (1-a1-b0))^2/2) (a1*b1+(max 0 (1-a1-b1))^2/2)):=by
 have h1:=V8 ha0 ha1 (b:=b)
 have h2a:a0*b+(max 0 (1-a0-b))^2/2 ≤ max (a0*b0+(max 0 (1-a0-b0))^2/2) (a0*b1+(max 0 (1-a0-b1))^2/2):=by
  have h:=V8 hb0 hb1 (b:=a0);have e1:a0*b=b*a0:=mul_comm _ _
  have e2:1-a0-b=1-b-a0:=by ring
  have e3:a0*b0=b0*a0:=mul_comm _ _
  have e4:1-a0-b0=1-b0-a0:=by ring
  have e5:a0*b1=b1*a0:=mul_comm _ _
  have e6:1-a0-b1=1-b1-a0:=by ring
  rwa[e1,e2,e3,e4,e5,e6]
 have h2b:a1*b+(max 0 (1-a1-b))^2/2 ≤ max (a1*b0+(max 0 (1-a1-b0))^2/2) (a1*b1+(max 0 (1-a1-b1))^2/2):=by
  have h:=V8 hb0 hb1 (b:=a1);have e1:a1*b=b*a1:=mul_comm _ _
  have e2:1-a1-b=1-b-a1:=by ring
  have e3:a1*b0=b0*a1:=mul_comm _ _
  have e4:1-a1-b0=1-b0-a1:=by ring
  have e5:a1*b1=b1*a1:=mul_comm _ _
  have e6:1-a1-b1=1-b1-a1:=by ring
  rwa[e1,e2,e3,e4,e5,e6]
 exact h1.trans (max_le (h2a.trans (Ym _ _)) (h2b.trans (Yn _ _)))
private lemma Ve (a b:Nat) :(c4Term a b:ℝ)/(4*(DD2:ℝ)) =((a:ℝ)/(DD:ℝ))*((b:ℝ)/(DD:ℝ)) +(max 0 (1-(a:ℝ)/(DD:ℝ)-(b:ℝ)/(DD:ℝ)))^2/2:=by
 have hD:(0:ℝ)<(DD:ℝ):=by norm_num[DD]
 have hD2:(DD2:ℝ)=(DD:ℝ)^2:=by norm_num[DD,DD2]
 rw[hD2];unfold c4Term;dsimp only
 split_ifs with hle
 ·have hleR:(DD:ℝ)≤(a:ℝ)+(b:ℝ):=by exact_mod_cast hle
  have hneg:1-(a:ℝ)/(DD:ℝ)-(b:ℝ)/(DD:ℝ)≤0:=by
   have:((a:ℝ)+(b:ℝ))/(DD:ℝ)≥1:=(one_le_div hD).mpr hleR
   linarith[add_div (a:ℝ) (b:ℝ) (DD:ℝ)]
  rw[Yk hneg];push_cast;field_simp;ring
 ·have hlt:a+b≤ DD:=by omega
  have hpos:0≤1-(a:ℝ)/(DD:ℝ)-(b:ℝ)/(DD:ℝ):=by
   have:((a:ℝ)+(b:ℝ))/(DD:ℝ)≤1:=(div_le_one hD).mpr (by exact_mod_cast hlt)
   linarith[add_div (a:ℝ) (b:ℝ) (DD:ℝ)]
  rw[Yi hpos]
  have hsub:((DD-a-b:Nat):ℝ)=(DD:ℝ)-(a:ℝ)-(b:ℝ):=by
   rw[Nat.cast_sub (by omega:b≤ DD-a),Nat.cast_sub (by omega:a≤ DD)]
  push_cast;rw[hsub];field_simp;ring
private lemma Vz (x:Nat) (hx:x≤ DD) :((4*DD*x-2*x*x:Nat):ℝ)/(4*(DD2:ℝ)) =((x:ℝ)/(DD:ℝ))-((x:ℝ)/(DD:ℝ))^2/2:=by
 have hD:(0:ℝ)<(DD:ℝ):=by norm_num[DD]
 have hD2:(DD2:ℝ)=(DD:ℝ)^2:=by norm_num[DD,DD2]
 have hsub:2*x*x≤4*DD*x:=by nlinarith
 rw[hD2,Nat.cast_sub hsub];push_cast;field_simp;ring
private lemma Ks (x:Nat) (hx:x≤ DD) :((DD2+2*DD*x-x*x:Nat):ℝ)/(4*(DD2:ℝ)) =(1+2*((x:ℝ)/(DD:ℝ))-((x:ℝ)/(DD:ℝ))^2)/4:=by
 have hD:(0:ℝ)<(DD:ℝ):=by norm_num[DD]
 have hD2:(DD2:ℝ)=(DD:ℝ)^2:=by norm_num[DD,DD2]
 have hsub:x*x≤ DD2+2*DD*x:=by
  have:x*x≤ DD*DD:=Nat.mul_le_mul hx hx
  dsimp only[DD2,DD] at *;omega
 rw[Nat.cast_sub hsub,Nat.cast_add,hD2];push_cast;field_simp
private lemma Kj (m1_0 y0 m1_hi y_hi:Nat) (hy0D:y0≤ DD) (hm1_0D:m1_0≤ DD)
  (_hy_hiD:y_hi≤ DD) (hm1_hiD:m1_hi≤ DD)
  {m1 y:ℝ} (hm1_lo:(m1_0:ℝ)/(DD:ℝ)≤ m1) (hm1_up:m1≤(m1_hi:ℝ)/(DD:ℝ))
  (hy_lo:(y0:ℝ)/(DD:ℝ)≤ y) (hy_up:y≤(y_hi:ℝ)/(DD:ℝ))
  (hy_1y_bd:y*(1-y)≤((max y0 (min y_hi 13860)*(DD-max y0 (min y_hi 13860)):Nat):ℝ)/(DD2:ℝ)) :
  let c1r:ℝ:=if 2*m1≤1-y then 1/4-m1^2/2 else 0
  let c2r:ℝ:=if 1/2≤ m1 then (1-m1)^2/2 else 1/6
  let c3r:ℝ:=y*(1-y)+(max 0 (1-2*y-m1))^2/2
  let c4r:ℝ:=m1*y+(max 0 (1-y-m1))^2/2
  let ym:=max y0 (min y_hi 13860)
  let y1y:=ym*(DD-ym)
  let c1:=if 2*m1_0≤ DD-y0 then DD2-2*m1_0*m1_0 else 0
  let c2:=if DD≤2*m1_0 then 2*(DD-m1_0)*(DD-m1_0) else 512265600
  let r3:=if DD≤2*y0+m1_0 then 0 else DD-2*y0-m1_0
  let c3:=4*y1y+2*r3*r3
  let c4:=max (max (c4Term m1_0 y0) (c4Term m1_0 y_hi)) (max (c4Term m1_hi y0) (c4Term m1_hi y_hi))
  max (max c1r c2r) (max c3r c4r)≤((max (max c1 c2) (max c3 c4):Nat):ℝ)/(4*(DD2:ℝ)):=by
 intro c1r c2r c3r c4r ym y1y c1 c2 r3 c3 c4
 have hD:(0:ℝ)<(DD:ℝ):=by norm_num[DD]
 have hD2:(0:ℝ)<(DD2:ℝ):=by norm_num[DD2]
 have hD2eq:(DD2:ℝ)=(DD:ℝ)^2:=by norm_num[DD,DD2]
 have hm1_nn:0≤ m1:=le_trans (div_nonneg (Nat.cast_nonneg _) hD.le) hm1_lo
 have hc1:c1r≤(c1:ℝ)/(4*(DD2:ℝ)):=by
  dsimp only[c1r,c1]
  split_ifs with h1 h2 h2
  ·have hsub:2*m1_0*m1_0≤ DD2:=by
    have:2*m1_0≤ DD:=by omega
    have:2*m1_0*m1_0≤ DD*DD:=by nlinarith
    exact this
   rw[Nat.cast_sub hsub,hD2eq];push_cast;have hsq:((m1_0:ℝ)/(DD:ℝ))^2≤ m1^2:=pow_le_pow_left₀ (div_nonneg (Nat.cast_nonneg _) hD.le) hm1_lo 2
   have heq:((DD:ℝ)^2-2*(m1_0:ℝ)*(m1_0:ℝ))/(4*(DD:ℝ)^2) =1/4-((m1_0:ℝ)/(DD:ℝ))^2/2:=by field_simp;ring
   linarith
  ·exfalso;apply h2
   have h1':2*((m1_0:ℝ)/(DD:ℝ))≤1-(y0:ℝ)/(DD:ℝ):=by linarith
   have h2':(2*m1_0:ℝ)≤((DD-y0:Nat):ℝ):=by
    rw[Nat.cast_sub hy0D]
    have:=Zo h1' hD.le
    have e1:2*((m1_0:ℝ)/(DD:ℝ))*(DD:ℝ)=2*(m1_0:ℝ):=by field_simp
    have e2:(1-(y0:ℝ)/(DD:ℝ))*(DD:ℝ)=(DD:ℝ)-(y0:ℝ):=by field_simp
    linarith
   exact_mod_cast h2'
  ·positivity
  ·norm_num
 have hc2:c2r≤(c2:ℝ)/(4*(DD2:ℝ)):=by
  dsimp only[c2r,c2]
  split_ifs with h1 h2 h2
  ·have hle1:m1≤1:=by
    have:=hm1_up.trans ((div_le_one hD).mpr (by exact_mod_cast hm1_hiD))
    exact this
   have hsq:(1-m1)^2≤(1-(m1_0:ℝ)/(DD:ℝ))^2 :=pow_le_pow_left₀ (by linarith) (by linarith) 2
   have heq:((2*(DD-m1_0)*(DD-m1_0):Nat):ℝ)/(4*(DD2:ℝ)) =(1-(m1_0:ℝ)/(DD:ℝ))^2/2:=by rw[hD2eq,Nat.cast_mul,Nat.cast_mul,Nat.cast_sub hm1_0D];push_cast;field_simp;ring
   linarith
  ·have h16:(512265600:ℝ)/(4*(DD2:ℝ))=1/6:=by norm_num[DD2]
   have hle1:m1≤1:=hm1_up.trans ((div_le_one hD).mpr (by exact_mod_cast hm1_hiD))
   push_cast;rw[h16];nlinarith
  ·exfalso;apply h1
   have:(1/2:ℝ)≤(m1_0:ℝ)/(DD:ℝ):=by
    have:(DD:ℝ)≤2*(m1_0:ℝ):=by exact_mod_cast h2
    rw[div_le_div_iff₀ (by norm_num) hD];linarith
   linarith
  ·have h16:(512265600:ℝ)/(4*(DD2:ℝ))=1/6:=by norm_num[DD2]
   push_cast;rw[h16]
 have hc3:c3r≤(c3:ℝ)/(4*(DD2:ℝ)):=by
  have hr3_bd:max 0 (1-2*y-m1)≤(r3:ℝ)/(DD:ℝ):=by
   dsimp only[r3]
   split_ifs with hle
   ·have hleR:(DD:ℝ)≤2*(y0:ℝ)+(m1_0:ℝ):=by exact_mod_cast hle
    have hneg:1-2*y-m1≤0:=by
     have:1≤2*((y0:ℝ)/(DD:ℝ))+(m1_0:ℝ)/(DD:ℝ):=by
      have:=(one_le_div hD).mpr hleR
      linarith[add_div (2*(y0:ℝ)) (m1_0:ℝ) (DD:ℝ),mul_div_assoc (2:ℝ) (y0:ℝ) (DD:ℝ)]
     linarith
    rw[Yk hneg];simp
   ·refine max_le (div_nonneg (Nat.cast_nonneg _) hD.le) ?_
    have hsub:((DD-2*y0-m1_0:Nat):ℝ)=(DD:ℝ)-2*(y0:ℝ)-(m1_0:ℝ):=by
     rw[Nat.cast_sub (by omega:m1_0≤ DD-2*y0),Nat.cast_sub (by omega:2*y0≤ DD)];push_cast;rfl
    rw[hsub,sub_div,sub_div,div_self hD.ne',mul_div_assoc];linarith
  have hsq:(max 0 (1-2*y-m1))^2≤((r3:ℝ)/(DD:ℝ))^2 :=pow_le_pow_left₀ (Ym _ _) hr3_bd 2
  have heq:(c3:ℝ)/(4*(DD2:ℝ))=(y1y:ℝ)/(DD2:ℝ)+((r3:ℝ)/(DD:ℝ))^2/2:=by dsimp only[c3];rw[hD2eq];push_cast;field_simp;ring
  dsimp only[c3r];linarith
 have hc4:c4r≤(c4:ℝ)/(4*(DD2:ℝ)):=by
  have h2d:=Kr hm1_lo hm1_up hy_lo hy_up;dsimp only[c4,c4r]
  rw[Nat.cast_max,Nat.cast_max,Nat.cast_max,Q7 (by positivity),Q7 (by positivity),Q7 (by positivity),Ve,Ve,Ve,Ve,show 1-y-m1=1-m1-y by ring]
  exact h2d
 rw[Nat.cast_max,Nat.cast_max,Nat.cast_max,Q7 (by positivity),Q7 (by positivity),Q7 (by positivity)]
 exact max_le (max_le (hc1.trans ((Ym _ _).trans (Ym _ _)))
            (hc2.trans ((Yn _ _).trans (Ym _ _))))
        (max_le (hc3.trans ((Ym _ _).trans (Yn _ _)))
            (hc4.trans ((Yn _ _).trans (Yn _ _))))
private lemma Ke (mod2:Bool) (m0 m1_0 y0 m_hi m1_hi y_hi tag:Nat)
  (hm_hiD:m_hi≤ DD) (hm1_hiD:m1_hi≤ DD) (hy_hiD:y_hi≤ DD)
  (hok:boxCheck mod2 m0 m1_0 y0 m_hi m1_hi y_hi tag=true)
  {m m1 y:ℝ} (hm_lo:(m0:ℝ)/(DD:ℝ)≤ m) (hm_up:m≤(m_hi:ℝ)/(DD:ℝ))
  (hm1_lo:(m1_0:ℝ)/(DD:ℝ)≤ m1) (hm1_up:m1≤(m1_hi:ℝ)/(DD:ℝ))
  (hy_lo:(y0:ℝ)/(DD:ℝ)≤ y) (hy_up:y≤(y_hi:ℝ)/(DD:ℝ))
  (hmm1:m≤ m1) (hy0_nn:0≤ y) (hsum:m1+y≤1) :
  CaseBBoundOK mod2 m m1 y:=by
 have hD:(0:ℝ)<(DD:ℝ):=by norm_num[DD]
 have hD2:(0:ℝ)<(DD2:ℝ):=by norm_num[DD2]
 have hD2eq:(DD2:ℝ)=(DD:ℝ)^2:=by norm_num[DD,DD2]
 have hm0_le_m1hi:m0≤ m1_hi:=by exact_mod_cast (div_le_div_iff_of_pos_right hD).mp (hm_lo.trans (hmm1.trans hm1_up))
 have hm10_y0:m1_0+y0≤ DD:=by
  have h1:((m1_0+y0:Nat):ℝ)/(DD:ℝ)≤1:=by rw[Nat.cast_add,add_div];linarith
  exact_mod_cast (div_le_one hD).mp h1
 unfold boxCheck at hok
 have hc1:(m0>m1_hi || m1_0+y0>DD)=false:=by simp only[Bool.or_eq_false_iff,decide_eq_false_iff_not,not_lt];exact⟨hm0_le_m1hi,hm10_y0⟩
 rw[hc1] at hok;dsimp only at hok;set m_hi':=min m_hi m1_hi;set m1_0':=max m1_0 m0;set m1_hi':=min m1_hi (DD-y0);set y_hi':=min y_hi (DD-m1_0');have hm_hi'D:m_hi'≤ DD:=(Yp _ _).trans hm_hiD;have hm1_hi'D:m1_hi'≤ DD:=(Yp _ _).trans hm1_hiD;have hy_hi'D:y_hi'≤ DD:=(Yp _ _).trans hy_hiD
 have hm_up':m≤(m_hi':ℝ)/(DD:ℝ):=by dsimp only[m_hi'];rw[Nat.cast_min,Wl hD.le];exact le_min hm_up (hmm1.trans hm1_up)
 have hm1_lo':(m1_0':ℝ)/(DD:ℝ)≤ m1:=by dsimp only[m1_0'];rw[Nat.cast_max,Q7 hD.le];exact max_le hm1_lo (hm_lo.trans hmm1)
 have hm1_up':m1≤(m1_hi':ℝ)/(DD:ℝ):=by
  dsimp only[m1_hi'];rw[Nat.cast_min,Wl hD.le]
  refine le_min hm1_up ?_
  rw[Nat.cast_sub (by omega:y0≤ DD),sub_div,div_self hD.ne'];linarith
 have hy_up':y≤(y_hi':ℝ)/(DD:ℝ):=by
  dsimp only[y_hi'];rw[Nat.cast_min,Wl hD.le]
  refine le_min hy_up ?_
  have hm1_0'D:m1_0'≤ DD:=by dsimp only[m1_0'];omega
  rw[Nat.cast_sub hm1_0'D,sub_div,div_self hD.ne'];linarith
 have hm0_le:m0≤ m_hi':=by exact_mod_cast (div_le_div_iff_of_pos_right hD).mp (hm_lo.trans hm_up')
 have hm1_le:m1_0'≤ m1_hi':=by exact_mod_cast (div_le_div_iff_of_pos_right hD).mp (hm1_lo'.trans hm1_up')
 have hy_le:y0≤ y_hi':=by exact_mod_cast (div_le_div_iff_of_pos_right hD).mp (hy_lo.trans hy_up')
 have hc2:(m0>m_hi' || m1_0'>m1_hi' || y0>y_hi')=false:=by simp only[Bool.or_eq_false_iff,decide_eq_false_iff_not,not_lt];exact⟨⟨hm0_le,hm1_le⟩,hy_le⟩
 rw[hc2] at hok;simp only[Bool.false_eq_true,↓reduceIte] at hok
 set S_num:Nat:=if mod2 then 247 else 329
 set L2_hi:Nat:=if mod2 then 13860 else (max (DD-y0) y_hi'+1)/2
 set p1:=fInt4 (DD-y0) m1_0';set p2:=fInt4 L2_hi m0;set p3:=pnc3_4 m0;set pnc:=p1+p2+p3;set ym:=max y0 (min y_hi' 13860);set y1y:=ym*(DD-ym);set m1c:=min m1_hi' (DD-y0);set g4:=4*DD*m1c-2*m1c*m1c+fInt4 (DD-y0) m1c
 set S_pc:ℝ:=if mod2 then 1235/1000 else 1645/1000
 set L2:ℝ:=if mod2 then 1/2 else max (1-y) y/2
 have hS_eq:S_pc=(S_num:ℝ)/200:=by dsimp only[S_pc,S_num];cases mod2 <;> norm_num
 have hS_nn:0≤ S_pc:=by dsimp only[S_pc];cases mod2 <;> norm_num
 have hm_nn:0≤ m:=le_trans (div_nonneg (Nat.cast_nonneg _) hD.le) hm_lo;have hm1_nn:0≤ m1:=le_trans hm_nn hmm1
 have hm_le1:m≤1:=by linarith
 have hm1_le1:m1≤1:=by linarith
 have h1y_ub:1-y≤((DD-y0:Nat):ℝ)/(DD:ℝ):=by
  rw[Nat.cast_sub (by omega:y0≤ DD),sub_div,div_self hD.ne'];linarith
 have hL2_nn:0≤ L2:=by
  dsimp only[L2];cases mod2
  ·exact div_nonneg (le_trans hy0_nn (Yn _ _)) (by norm_num)
  ·norm_num
 have hL2_ub:L2≤(L2_hi:ℝ)/(DD:ℝ):=by
  dsimp only[L2,L2_hi];cases mod2
  ·simp only[Bool.false_eq_true,↓reduceIte]
   have hmax:max (1-y) y≤((max (DD-y0) y_hi':Nat):ℝ)/(DD:ℝ):=by rw[Nat.cast_max,Q7 hD.le];exact max_le (h1y_ub.trans (Ym _ _)) (hy_up'.trans (Yn _ _))
   have hceil:((max (DD-y0) y_hi':Nat):ℝ)≤2*(((max (DD-y0) y_hi'+1)/2:Nat):ℝ):=by
    exact_mod_cast (by omega:max (DD-y0) y_hi'≤2*((max (DD-y0) y_hi'+1)/2))
   have hdiv:=div_le_div_of_nonneg_right hceil hD.le;rw[mul_div_assoc] at hdiv;linarith only[hmax,hdiv]
  ·simp only[↓reduceIte];norm_num[DD]
 have hL2_hiD:L2_hi≤ DD:=by
  dsimp only[L2_hi];cases mod2
  ·simp only[Bool.false_eq_true,↓reduceIte];dsimp only[DD] at *;omega
  ·simp only[↓reduceIte];dsimp only[DD];omega
 have hp1_bd:fInt (1-y) m1≤(p1:ℝ)/(4*(DD2:ℝ)):=by
  rw[show (p1:ℝ)/(4*(DD2:ℝ))=fInt (((DD-y0:Nat):ℝ)/(DD:ℝ)) ((m1_0':ℝ)/(DD:ℝ)) from X8 _ _]
  exact (Wf (by linarith only[hm1_nn,hsum]) h1y_ub hm1_nn).trans
   (Wb (div_nonneg (Nat.cast_nonneg _) hD.le) hm1_lo' (div_nonneg (Nat.cast_nonneg _) hD.le))
 have hp2_bd:fInt L2 m≤(p2:ℝ)/(4*(DD2:ℝ)):=by
  rw[show (p2:ℝ)/(4*(DD2:ℝ))=fInt ((L2_hi:ℝ)/(DD:ℝ)) ((m0:ℝ)/(DD:ℝ)) from X8 _ _]
  exact (Wf hL2_nn hL2_ub hm_nn).trans
   (Wb (div_nonneg (Nat.cast_nonneg _) hD.le) hm_lo (div_nonneg (Nat.cast_nonneg _) hD.le))
 have hp3_bd:pnc3Sum m≤(p3:ℝ)/(4*(DD2:ℝ)):=by rw[show (p3:ℝ)/(4*(DD2:ℝ))=pnc3Sum ((m0:ℝ)/(DD:ℝ)) from Kq _];exact Ki (div_nonneg (Nat.cast_nonneg _) hD.le) hm_lo
 have hpnc_bd:fInt (1-y) m1+fInt L2 m+pnc3Sum m≤(pnc:ℝ)/(4*(DD2:ℝ)):=by dsimp only[pnc];push_cast;simp only[add_div];linarith only[hp1_bd,hp2_bd,hp3_bd]
 have hy1y_bd:y*(1-y)≤(y1y:ℝ)/(DD2:ℝ):=by
  have hmid:=Vm hy_lo hy_up'
  have hhalf:((13860:Nat):ℝ)/(DD:ℝ)=1/2:=by norm_num[DD]
  have hym_eq:max ((y0:ℝ)/(DD:ℝ)) (min ((y_hi':ℝ)/(DD:ℝ)) (1/2))=(ym:ℝ)/(DD:ℝ):=by change max ((y0:ℝ)/(DD:ℝ)) (min ((y_hi':ℝ)/(DD:ℝ)) (1/2)) =((max y0 (min y_hi' 13860):Nat):ℝ)/(DD:ℝ);simp only[←hhalf,Nat.cast_max,Nat.cast_min,Q7 hD.le,Wl hD.le]
  have hymD:ym≤ DD:=by dsimp only[ym];dsimp only[DD] at *;omega
  have hprod:((ym:ℝ)/(DD:ℝ))*(1-(ym:ℝ)/(DD:ℝ))=(y1y:ℝ)/(DD2:ℝ):=by dsimp only[y1y];rw[hD2eq,Nat.cast_mul,Nat.cast_sub hymD];field_simp
  rwa[hym_eq,hprod] at hmid
 have hm1c_eq:m1c=m1_hi':=Yl (Yq _ _)
 have hm1cD:m1c≤ DD:=by omega
 have hg4_bd:(m1-m1^2/2)+fInt (1-y) m1≤(g4:ℝ)/(4*(DD2:ℝ)):=by
  have h1:fInt (1-y) m1≤ fInt (((DD-y0:Nat):ℝ)/(DD:ℝ)) m1 :=Wf (by linarith only[hm1_nn,hsum]) h1y_ub hm1_nn
  have h2:(m1-m1^2/2)+fInt (((DD-y0:Nat):ℝ)/(DD:ℝ)) m1 ≤((m1c:ℝ)/(DD:ℝ)-((m1c:ℝ)/(DD:ℝ))^2/2) +fInt (((DD-y0:Nat):ℝ)/(DD:ℝ)) ((m1c:ℝ)/(DD:ℝ)) :=X0 (by rw[hm1c_eq];exact hm1_up')
    ((div_le_one hD).mpr (by exact_mod_cast hm1cD))
    ((div_le_one hD).mpr (by exact_mod_cast Nat.sub_le DD y0))
  have h3:(g4:ℝ)/(4*(DD2:ℝ)) =((m1c:ℝ)/(DD:ℝ)-((m1c:ℝ)/(DD:ℝ))^2/2) +fInt (((DD-y0:Nat):ℝ)/(DD:ℝ)) ((m1c:ℝ)/(DD:ℝ)):=by dsimp only[g4];rw[Nat.cast_add,add_div,Vz m1c hm1cD,X8]
  linarith only[h1,h2,h3]
 have hhit_m1c:m1-m1^2/2≤((4*DD*m1c-2*m1c*m1c:Nat):ℝ)/(4*(DD2:ℝ)):=by
  rw[Vz m1c hm1cD]
  have hle:m1≤(m1c:ℝ)/(DD:ℝ):=by rw[hm1c_eq];exact hm1_up'
  have hle1:(m1c:ℝ)/(DD:ℝ)≤1:=(div_le_one hD).mpr (by exact_mod_cast hm1cD)
  nlinarith only[hle,hle1]
 have hhit_mhi:m-m^2/2≤((4*DD*m_hi'-2*m_hi'*m_hi':Nat):ℝ)/(4*(DD2:ℝ)):=by
  rw[Vz m_hi' hm_hi'D]
  have hle1:(m_hi':ℝ)/(DD:ℝ)≤1:=(div_le_one hD).mpr (by exact_mod_cast hm_hi'D)
  nlinarith only[hm_up',hle1]
 have hamgm_mhi:(1+2*m-m^2)/4≤((DD2+2*DD*m_hi'-m_hi'*m_hi':Nat):ℝ)/(4*(DD2:ℝ)):=by
  rw[Ks m_hi' hm_hi'D]
  have hle1:(m_hi':ℝ)/(DD:ℝ)≤1:=(div_le_one hD).mpr (by exact_mod_cast hm_hi'D)
  nlinarith only[hm_up',hle1]
 match tag with
 | 1 =>
  simp only[Bool.and_eq_true,decide_eq_true_eq] at hok;left
  refine⟨hok.1,?_⟩
  have hnat:(2:ℝ)*(pnc:ℝ)≤(DD2:ℝ):=by exact_mod_cast hok.2
  have hdiv:(pnc:ℝ)/(4*(DD2:ℝ))≤1/8:=by
   rw[div_le_div_iff₀ (by positivity) (by norm_num)];linarith only[hnat]
  change 3/8+(fInt (1-y) m1+fInt L2 m+pnc3Sum m)≤1/2;linarith only[hpnc_bd,hdiv]
 | 2 =>
  simp only[Bool.and_eq_true,decide_eq_true_eq] at hok;right;left
  have h2a_nat:570000*((g4:ℝ)+(p2:ℝ)+(p3:ℝ))+1849*(S_num:ℝ)*(y_hi':ℝ)*(y_hi':ℝ) ≤1140000*(DD2:ℝ):=by exact_mod_cast hok.1
  have h2b_nat:(20000-57*(S_num:ℝ))*(((4*DD*m1c-2*m1c*m1c:Nat):ℝ)) +20000*(pnc:ℝ)+400*(S_num:ℝ)*(y1y:ℝ)≤40000*(DD2:ℝ):=by
   have hS_lt:57*S_num≤20000:=by dsimp only[S_num];cases mod2 <;> norm_num
   have h0:(((20000-57*S_num)*(4*DD*m1c-2*m1c*m1c)+20000*pnc+400*S_num*y1y:Nat):ℝ) ≤((40000*DD2:Nat):ℝ):=by exact_mod_cast hok.2
   rw[Nat.cast_add,Nat.cast_add,Nat.cast_mul,Nat.cast_sub hS_lt] at h0;push_cast at h0;exact h0
  have hqa:(m1-m1^2/2)+((43/100*y)^2/(114/100))*S_pc +(fInt (1-y) m1+fInt L2 m+pnc3Sum m)≤1/2:=by
   have hy_sq:y^2≤((y_hi':ℝ)/(DD:ℝ))^2:=pow_le_pow_left₀ hy0_nn hy_up' 2
   have hterm:((43/100*y)^2/(114/100))*S_pc ≤(1849*(S_num:ℝ)*(y_hi':ℝ)*(y_hi':ℝ))/(2280000*(DD2:ℝ)):=by
    rw[hS_eq,hD2eq];have hS_nn':(0:ℝ)≤(S_num:ℝ):=Nat.cast_nonneg _
    have heq:((43/100*((y_hi':ℝ)/(DD:ℝ)))^2/(114/100))*((S_num:ℝ)/200) =(1849*(S_num:ℝ)*(y_hi':ℝ)*(y_hi':ℝ))/(2280000*(DD:ℝ)^2):=by field_simp;ring
    have hle:((43/100*y)^2/(114/100))*((S_num:ℝ)/200) ≤((43/100*((y_hi':ℝ)/(DD:ℝ)))^2/(114/100))*((S_num:ℝ)/200):=by
     have:(43/100*y)^2≤(43/100*((y_hi':ℝ)/(DD:ℝ)))^2:=by
      rw[mul_pow,mul_pow];exact Zp hy_sq (by norm_num)
     exact Zo (div_le_div_of_nonneg_right this (by norm_num)) (by positivity)
    linarith only[hle,heq]
   have hsum_le:((g4:ℝ)+(p2:ℝ)+(p3:ℝ))/(4*(DD2:ℝ)) +(1849*(S_num:ℝ)*(y_hi':ℝ)*(y_hi':ℝ))/(2280000*(DD2:ℝ))≤1/2:=by
    have hcomb:((g4:ℝ)+(p2:ℝ)+(p3:ℝ))/(4*(DD2:ℝ)) +(1849*(S_num:ℝ)*(y_hi':ℝ)*(y_hi':ℝ))/(2280000*(DD2:ℝ)) =(570000*((g4:ℝ)+(p2:ℝ)+(p3:ℝ))+1849*(S_num:ℝ)*(y_hi':ℝ)*(y_hi':ℝ)) /(2280000*(DD2:ℝ)):=by field_simp;ring
    rw[hcomb,div_le_div_iff₀ (by positivity) (by norm_num)];linarith only[h2a_nat]
   have hsplit:((g4:ℝ)+(p2:ℝ)+(p3:ℝ))/(4*(DD2:ℝ)) =(g4:ℝ)/(4*(DD2:ℝ))+(p2:ℝ)/(4*(DD2:ℝ))+(p3:ℝ)/(4*(DD2:ℝ)):=by ring
   linarith only[hg4_bd,hp2_bd,hp3_bd,hterm,hsum_le,hsplit]
  have hqb:(m1-m1^2/2)+(y-y^2-(57/100)*m1+(57/200)*m1^2)*S_pc +(fInt (1-y) m1+fInt L2 m+pnc3Sum m)≤1/2:=by
   have hrew:(m1-m1^2/2)+(y-y^2-(57/100)*m1+(57/200)*m1^2)*S_pc =(1-(57/100)*S_pc)*(m1-m1^2/2)+S_pc*(y*(1-y)):=by ring
   have hcoef_nn:0≤1-(57/100)*S_pc:=by dsimp only[S_pc];cases mod2 <;> norm_num
   have h1:=Zp hhit_m1c hcoef_nn;have h2:=Zp hy1y_bd hS_nn
   have hcomb:(1-(57/100)*S_pc)*(((4*DD*m1c-2*m1c*m1c:Nat):ℝ)/(4*(DD2:ℝ))) +S_pc*((y1y:ℝ)/(DD2:ℝ))+(pnc:ℝ)/(4*(DD2:ℝ)) =((20000-57*(S_num:ℝ))*(((4*DD*m1c-2*m1c*m1c:Nat):ℝ)) +20000*(pnc:ℝ)+400*(S_num:ℝ)*(y1y:ℝ))/(80000*(DD2:ℝ)):=by rw[hS_eq];field_simp;ring
   have hle_half:((20000-57*(S_num:ℝ))*(((4*DD*m1c-2*m1c*m1c:Nat):ℝ)) +20000*(pnc:ℝ)+400*(S_num:ℝ)*(y1y:ℝ))/(80000*(DD2:ℝ))≤1/2:=by
    rw[div_le_div_iff₀ (by positivity) (by norm_num)];linarith only[h2b_nat]
   linarith only[hrew,h1,h2,hpnc_bd,hcomb,hle_half]
  have hmax:max ((43/100*y)^2/(114/100)) (y-y^2-(57/100)*m1+(57/200)*m1^2)*S_pc ≤1/2-(m1-m1^2/2)-(fInt (1-y) m1+fInt L2 m+pnc3Sum m):=by
   rw[max_mul_of_nonneg _ _ hS_nn]
   exact max_le (by linarith only[hqa]) (by linarith only[hqb])
  change (m1-m1^2/2) +max ((43/100*y)^2/(114/100)) (y-y^2-(57/100)*m1+(57/200)*m1^2)*S_pc +(fInt (1-y) m1+fInt L2 m+pnc3Sum m)≤1/2;linarith only[hmax]
 | 3 =>
  simp only[Bool.and_eq_true,decide_eq_true_eq] at hok;right;right;left
  have h1:200*(g4:ℝ)≤271*(DD2:ℝ):=by exact_mod_cast hok.1
  have h2:200*(4*(y1y:ℝ)+(p1:ℝ))≤271*(DD2:ℝ):=by exact_mod_cast hok.2
  have hb1:(m1-m1^2/2)+fInt (1-y) m1≤271/800:=by
   have:(g4:ℝ)/(4*(DD2:ℝ))≤271/800:=by
    rw[div_le_div_iff₀ (by positivity) (by norm_num)];linarith only[h1]
   linarith only[hg4_bd,this]
  have hb2:(y-y^2)+fInt (1-y) m1≤271/800:=by
   have heq:(y1y:ℝ)/(DD2:ℝ)+(p1:ℝ)/(4*(DD2:ℝ)) =(4*(y1y:ℝ)+(p1:ℝ))/(4*(DD2:ℝ)):=by ring
   have hdiv:(4*(y1y:ℝ)+(p1:ℝ))/(4*(DD2:ℝ))≤271/800:=by
    rw[div_le_div_iff₀ (by positivity) (by norm_num)];linarith only[h2]
   have hy_eq:y-y^2=y*(1-y):=by ring
   linarith only[hy_eq,hy1y_bd,hp1_bd,heq,hdiv]
  have hmax:max (m1-m1^2/2) (y-y^2)≤271/800-fInt (1-y) m1 :=max_le (by linarith only[hb1]) (by linarith only[hb2])
  linarith only[hmax]
 | 4 =>
  simp only[decide_eq_true_eq] at hok;right;right;right;left
  have hnat:200*(((4*DD*m_hi'-2*m_hi'*m_hi':Nat):ℝ)+(fInt4 L2_hi m_hi':ℝ) +(p1:ℝ)+(p3:ℝ))+4*(S_num:ℝ)*(y1y:ℝ)≤400*(DD2:ℝ):=by exact_mod_cast hok
  have hmf:(m-m^2/2)+fInt L2 m ≤(((4*DD*m_hi'-2*m_hi'*m_hi':Nat):ℝ)+(fInt4 L2_hi m_hi':ℝ))/(4*(DD2:ℝ)):=by
   have h1:fInt L2 m≤ fInt ((L2_hi:ℝ)/(DD:ℝ)) m:=Wf hL2_nn hL2_ub hm_nn
   have h2:=X0 (L:=(L2_hi:ℝ)/(DD:ℝ)) hm_up'
    ((div_le_one hD).mpr (by exact_mod_cast hm_hi'D))
    ((div_le_one hD).mpr (by exact_mod_cast hL2_hiD))
   rw[add_div,Vz m_hi' hm_hi'D,X8];linarith only[h1,h2]
  have hSy:S_pc*y*(1-y)≤(S_num:ℝ)*(y1y:ℝ)/(200*(DD2:ℝ)):=by
   have h1:=Zp hy1y_bd hS_nn
   have heq:S_pc*(y*(1-y))=S_pc*y*(1-y):=by ring
   have heq2:S_pc*((y1y:ℝ)/(DD2:ℝ))=(S_num:ℝ)*(y1y:ℝ)/(200*(DD2:ℝ)):=by rw[hS_eq];ring
   linarith only[h1,heq,heq2]
  have hcomb:(((4*DD*m_hi'-2*m_hi'*m_hi':Nat):ℝ)+(fInt4 L2_hi m_hi':ℝ))/(4*(DD2:ℝ)) +(p1:ℝ)/(4*(DD2:ℝ))+(p3:ℝ)/(4*(DD2:ℝ))+(S_num:ℝ)*(y1y:ℝ)/(200*(DD2:ℝ)) =(200*(((4*DD*m_hi'-2*m_hi'*m_hi':Nat):ℝ)+(fInt4 L2_hi m_hi':ℝ) +(p1:ℝ)+(p3:ℝ))+4*(S_num:ℝ)*(y1y:ℝ))/(800*(DD2:ℝ)):=by field_simp;ring
  have hdiv:(200*(((4*DD*m_hi'-2*m_hi'*m_hi':Nat):ℝ)+(fInt4 L2_hi m_hi':ℝ) +(p1:ℝ)+(p3:ℝ))+4*(S_num:ℝ)*(y1y:ℝ))/(800*(DD2:ℝ))≤1/2:=by
   rw[div_le_div_iff₀ (by positivity) (by norm_num)];linarith only[hnat]
  change (m-m^2/2)+S_pc*y*(1-y)+(fInt (1-y) m1+fInt L2 m+pnc3Sum m)≤1/2;linarith only[hmf,hp1_bd,hp3_bd,hSy,hcomb,hdiv]
 | 5 =>
  simp only[decide_eq_true_eq] at hok;right;right;right;right;left
  have hS200:200≤ S_num:=by dsimp only[S_num];cases mod2 <;> norm_num
  have hnat:200*(((DD2+2*DD*m_hi'-m_hi'*m_hi':Nat):ℝ)+(pnc:ℝ)) +4*((S_num:ℝ)-200)*(y1y:ℝ)≤400*(DD2:ℝ):=by
   have h0:((200*(DD2+2*DD*m_hi'-m_hi'*m_hi'+pnc)+4*(S_num-200)*y1y:Nat):ℝ) ≤((400*DD2:Nat):ℝ):=by exact_mod_cast hok
   rw[Nat.cast_add,Nat.cast_mul,Nat.cast_add,Nat.cast_mul,Nat.cast_mul,Nat.cast_sub hS200] at h0;push_cast at h0;exact h0
  have hSy:(S_pc-1)*y*(1-y)≤((S_num:ℝ)-200)*(y1y:ℝ)/(200*(DD2:ℝ)):=by
   have hS1_nn:0≤ S_pc-1:=by dsimp only[S_pc];cases mod2 <;> norm_num
   have h1:=Zp hy1y_bd hS1_nn
   have heq:(S_pc-1)*(y*(1-y))=(S_pc-1)*y*(1-y):=by ring
   have heq2:(S_pc-1)*((y1y:ℝ)/(DD2:ℝ))=((S_num:ℝ)-200)*(y1y:ℝ)/(200*(DD2:ℝ)):=by rw[hS_eq];ring
   linarith only[h1,heq,heq2]
  have hcomb:((DD2+2*DD*m_hi'-m_hi'*m_hi':Nat):ℝ)/(4*(DD2:ℝ)) +(pnc:ℝ)/(4*(DD2:ℝ))+((S_num:ℝ)-200)*(y1y:ℝ)/(200*(DD2:ℝ)) =(200*(((DD2+2*DD*m_hi'-m_hi'*m_hi':Nat):ℝ)+(pnc:ℝ)) +4*((S_num:ℝ)-200)*(y1y:ℝ))/(800*(DD2:ℝ)):=by field_simp;ring
  have hdiv:(200*(((DD2+2*DD*m_hi'-m_hi'*m_hi':Nat):ℝ)+(pnc:ℝ)) +4*((S_num:ℝ)-200)*(y1y:ℝ))/(800*(DD2:ℝ))≤1/2:=by
   rw[div_le_div_iff₀ (by positivity) (by norm_num)];linarith only[hnat]
  change (1+2*m-m^2)/4+(S_pc-1)*y*(1-y)+(fInt (1-y) m1+fInt L2 m+pnc3Sum m)≤1/2;linarith only[hamgm_mhi,hpnc_bd,hSy,hcomb,hdiv]
 | 6 =>
  simp only[decide_eq_true_eq] at hok;right;right;right;right;right;left;set cm:=min (DD2+2*DD*m_hi'-m_hi'*m_hi') (4*DD*m_hi'-2*m_hi'*m_hi'+4*y1y)
  have hnat:200*((cm:ℝ)+(p1:ℝ))≤271*(DD2:ℝ):=by exact_mod_cast hok
  have hmin_bd:min ((1+2*m-m^2)/4) ((m-m^2/2)+y*(1-y))≤(cm:ℝ)/(4*(DD2:ℝ)):=by
   dsimp only[cm]
   rw[Nat.cast_min,Wl (by positivity)]
   refine le_min ((Yp _ _).trans hamgm_mhi) ((Yq _ _).trans ?_)
   rw[Nat.cast_add,add_div]
   have heq:((4*y1y:Nat):ℝ)/(4*(DD2:ℝ))=(y1y:ℝ)/(DD2:ℝ):=by push_cast;ring
   linarith only[hhit_mhi,hy1y_bd,heq]
  have hdiv:((cm:ℝ)+(p1:ℝ))/(4*(DD2:ℝ))≤271/800:=by
   rw[div_le_div_iff₀ (by positivity) (by norm_num)];linarith only[hnat]
  have hsplit:((cm:ℝ)+(p1:ℝ))/(4*(DD2:ℝ))=(cm:ℝ)/(4*(DD2:ℝ))+(p1:ℝ)/(4*(DD2:ℝ)):=by ring
  linarith only[hmin_bd,hp1_bd,hdiv,hsplit]
 | 7 =>
  simp only[decide_eq_true_eq] at hok;right;right;right;right;right;right
  have hhelly:=Kj m1_0' y0 m1_hi' y_hi' (by omega) (by dsimp only[m1_0'];omega) hy_hi'D hm1_hi'D
   hm1_lo' hm1_up' hy_lo hy_up' hy1y_bd
  dsimp only at hhelly
  set c1:=if 2*m1_0'≤ DD-y0 then DD2-2*m1_0'*m1_0' else 0
  set c2:=if DD≤2*m1_0' then 2*(DD-m1_0')*(DD-m1_0') else 512265600
  set r3:=if DD≤2*y0+m1_0' then 0 else DD-2*y0-m1_0'
  set c3:=4*y1y+2*r3*r3;set c4:=max (max (c4Term m1_0' y0) (c4Term m1_0' y_hi')) (max (c4Term m1_hi' y0) (c4Term m1_hi' y_hi'))
  have hnat:200*(((4*DD*m_hi'-2*m_hi'*m_hi':Nat):ℝ) +((max (max c1 c2) (max c3 c4):Nat):ℝ))≤271*(DD2:ℝ):=by exact_mod_cast hok
  have hdiv:(((4*DD*m_hi'-2*m_hi'*m_hi':Nat):ℝ) +((max (max c1 c2) (max c3 c4):Nat):ℝ))/(4*(DD2:ℝ))≤271/800:=by
   rw[div_le_div_iff₀ (by positivity) (by norm_num)];linarith only[hnat]
  rw[add_div] at hdiv;linarith only[hhit_mhi,hhelly,hdiv]
 | 0=>simp at hok
 | _+8=>simp at hok
private lemma Vd (mod2:Bool) (t:CTree) :∀ (m0 m1_0 y0 m_hi m1_hi y_hi:Nat),m_hi≤ DD->m1_hi≤ DD->y_hi≤ DD →
   midsLe t=true →
   checkTree mod2 m0 m1_0 y0 m_hi m1_hi y_hi t=true →
   ∀ {m m1 y:ℝ},(m0:ℝ)/(DD:ℝ)≤ m->m≤(m_hi:ℝ)/(DD:ℝ) →
    (m1_0:ℝ)/(DD:ℝ)≤ m1->m1≤(m1_hi:ℝ)/(DD:ℝ) →
    (y0:ℝ)/(DD:ℝ)≤ y->y≤(y_hi:ℝ)/(DD:ℝ) →
    m≤ m1->0≤ y->m1+y≤1 →
    CaseBBoundOK mod2 m m1 y:=by
 induction t with
 | L tag =>
  intro m0 m1_0 y0 m_hi m1_hi y_hi hm_hiD hm1_hiD hy_hiD _ hok m m1 y hm_lo hm_up hm1_lo hm1_up hy_lo hy_up hmm1 hy0 hsum
  exact Ke mod2 m0 m1_0 y0 m_hi m1_hi y_hi tag hm_hiD hm1_hiD hy_hiD hok
   hm_lo hm_up hm1_lo hm1_up hy_lo hy_up hmm1 hy0 hsum
 | N ax mid l r ihl ihr =>
  intro m0 m1_0 y0 m_hi m1_hi y_hi hm_hiD hm1_hiD hy_hiD hmids hok m m1 y hm_lo hm_up hm1_lo hm1_up hy_lo hy_up hmm1 hy0 hsum
  have hD:(0:ℝ)<(DD:ℝ):=by norm_num[DD]
  simp only[midsLe,Bool.and_eq_true,decide_eq_true_eq] at hmids;obtain⟨⟨hmidD,hml⟩,hmr⟩:=hmids;unfold checkTree at hok;dsimp only at hok;set m_hi':=min m_hi m1_hi;set m1_0':=max m1_0 m0;set m1_hi':=min m1_hi (DD-y0);set y_hi':=min y_hi (DD-m1_0');have hm_hi'D:m_hi'≤ DD:=(Yp _ _).trans hm_hiD;have hm1_hi'D:m1_hi'≤ DD:=(Yp _ _).trans hm1_hiD;have hy_hi'D:y_hi'≤ DD:=(Yp _ _).trans hy_hiD
  have hm10_y0:m1_0+y0≤ DD:=by
   have h1:((m1_0+y0:Nat):ℝ)/(DD:ℝ)≤1:=by rw[Nat.cast_add,add_div];linarith
   exact_mod_cast (div_le_one hD).mp h1
  have hm0_D:m0≤ DD:=by
   have:(m0:ℝ)/(DD:ℝ)≤1:=by linarith
   exact_mod_cast (div_le_one hD).mp this
  have hm_up':m≤(m_hi':ℝ)/(DD:ℝ):=by dsimp only[m_hi'];rw[Nat.cast_min,Wl hD.le];exact le_min hm_up (hmm1.trans hm1_up)
  have hm1_lo':(m1_0':ℝ)/(DD:ℝ)≤ m1:=by dsimp only[m1_0'];rw[Nat.cast_max,Q7 hD.le];exact max_le hm1_lo (hm_lo.trans hmm1)
  have hm1_up':m1≤(m1_hi':ℝ)/(DD:ℝ):=by
   dsimp only[m1_hi'];rw[Nat.cast_min,Wl hD.le]
   refine le_min hm1_up ?_;rw[Nat.cast_sub (by omega:y0≤ DD),sub_div,div_self hD.ne'];linarith
  have hy_up':y≤(y_hi':ℝ)/(DD:ℝ):=by
   dsimp only[y_hi'];rw[Nat.cast_min,Wl hD.le]
   refine le_min hy_up ?_;rw[Nat.cast_sub (by dsimp only[m1_0'];omega:m1_0'≤ DD),sub_div,div_self hD.ne'];linarith
  split_ifs at hok with hax0 hax1
  ·simp only[Bool.and_eq_true] at hok
   rcases le_total m ((mid:ℝ)/(DD:ℝ)) with hle|hge
   ·exact ihl m0 m1_0' y0 mid m1_hi' y_hi' hmidD hm1_hi'D hy_hi'D hml hok.1 hm_lo hle hm1_lo' hm1_up' hy_lo hy_up' hmm1 hy0 hsum
   ·exact ihr mid m1_0' y0 m_hi' m1_hi' y_hi' hm_hi'D hm1_hi'D hy_hi'D hmr hok.2 hge hm_up' hm1_lo' hm1_up' hy_lo hy_up' hmm1 hy0 hsum
  ·simp only[Bool.and_eq_true] at hok
   rcases le_total m1 ((mid:ℝ)/(DD:ℝ)) with hle|hge
   ·exact ihl m0 m1_0' y0 m_hi' mid y_hi' hm_hi'D hmidD hy_hi'D hml hok.1 hm_lo hm_up' hm1_lo' hle hy_lo hy_up' hmm1 hy0 hsum
   ·exact ihr m0 mid y0 m_hi' m1_hi' y_hi' hm_hi'D hm1_hi'D hy_hi'D hmr hok.2 hm_lo hm_up' hge hm1_up' hy_lo hy_up' hmm1 hy0 hsum
  ·simp only[Bool.and_eq_true] at hok
   rcases le_total y ((mid:ℝ)/(DD:ℝ)) with hle|hge
   ·exact ihl m0 m1_0' y0 m_hi' m1_hi' mid hm_hi'D hm1_hi'D hmidD hml hok.1 hm_lo hm_up' hm1_lo' hm1_up' hy_lo hle hmm1 hy0 hsum
   ·exact ihr m0 m1_0' mid m_hi' m1_hi' y_hi' hm_hi'D hm1_hi'D hy_hi'D hmr hok.2 hm_lo hm_up' hm1_lo' hm1_up' hge hy_up' hmm1 hy0 hsum
end CaseBCert
lemma Ko (mod2:Bool) {m m1 y:ℝ}
  (hm:1/12≤ m) (hmm1:m≤ m1) (hy:0≤ y) (hsum:m1+y≤1) :
  CaseBBoundOK mod2 m m1 y:=by
 by_cases h1:1/2≤ m
 ·exact Km mod2 h1 hmm1 hy hsum
 ·push Not at h1
  by_cases h2:45/100≤ m
  ·exact Kl mod2 h2 h1.le hmm1 hy hsum
  ·push Not at h2
   have hm_lo:((2310:Nat):ℝ)/(CaseBCert.DD:ℝ)≤ m:=by
    have:((2310:Nat):ℝ)/(CaseBCert.DD:ℝ)=1/12:=by norm_num[CaseBCert.DD]
    linarith
   have hm_up:m≤((12474:Nat):ℝ)/(CaseBCert.DD:ℝ):=by
    have:((12474:Nat):ℝ)/(CaseBCert.DD:ℝ)=45/100:=by norm_num[CaseBCert.DD]
    linarith
   have hm1_lo:((2310:Nat):ℝ)/(CaseBCert.DD:ℝ)≤ m1:=hm_lo.trans hmm1
   have hm1_up:m1≤((27720:Nat):ℝ)/(CaseBCert.DD:ℝ):=by
    have:((27720:Nat):ℝ)/(CaseBCert.DD:ℝ)=1:=by norm_num[CaseBCert.DD]
    linarith
   have hy_lo:((0:Nat):ℝ)/(CaseBCert.DD:ℝ)≤ y:=by simpa using hy
   have hy_up:y≤((27720:Nat):ℝ)/(CaseBCert.DD:ℝ):=by
    have:((27720:Nat):ℝ)/(CaseBCert.DD:ℝ)=1:=by norm_num[CaseBCert.DD]
    linarith
   cases mod2
   ·exact CaseBCert.Vd false CaseBCert.treeF 2310 2310 0 12474 27720 27720
     (by decide) (by decide) (by decide) CaseBCert.midsF CaseBCert.okF
     hm_lo hm_up hm1_lo hm1_up hy_lo hy_up hmm1 hy hsum
   ·exact CaseBCert.Vd true CaseBCert.treeT 2310 2310 0 12474 27720 27720
     (by decide) (by decide) (by decide) CaseBCert.midsT CaseBCert.okT
     hm_lo hm_up hm1_lo hm1_up hy_lo hy_up hmm1 hy hsum
private lemma Qd {N:ℕ} {F G:Zf (Zf ℕ)}
  (hF:Zt N F) (hGF:G⊆F):Zt N G :=
 ⟨hGF.trans hF.1,fun _ hS _ hT hST =>
  hF.2 (Zc.mpr (hGF (Zc.mp hS)))
   (Zc.mpr (hGF (Zc.mp hT))) hST⟩
private lemma Qe {N:ℕ} {F:Zf (Zf ℕ)}
  (hF:Zt N F) {A B:Zf ℕ} (hA:A∈F) (hB:B∈F) (hAB:A≠B) :
  (A∩B).Nonempty:=by
 obtain⟨l,hl,hl'⟩:=hF.2 (Zc.mpr hA) (Zc.mpr hB) hAB;obtain⟨a,d,k,hk,-,hX⟩:=Qn (A∩B) l hl hl'
 exact⟨a,(hX a).mpr ⟨0,hk,by simp⟩⟩
private lemma Vn {X:Zf ℕ} (hAP:IsAP X) :∃ l:ℕ∞,0< l/\(SetLike.coe X).IsAPOfLength l:=by
 obtain⟨a,d,k,hk,hdk,hX⟩:=hAP
 refine⟨(k:ℕ∞),by exact_mod_cast hk,a,d,?_,?_⟩
 ·rw[ENat.card_coe_set_eq,Set.encard_coe_eq_coe_finsetCard,Qo hk hdk hX]
 ·ext x
  simp only[Zc,Set.mem_ofPred_eq,smul_eq_mul];rw[hX x]
  constructor
  ·rintro⟨i,hi,rfl⟩;exact⟨i,by exact_mod_cast hi,rfl⟩
  ·rintro⟨i,hi,rfl⟩;exact⟨i,by exact_mod_cast hi,rfl⟩
lemma Wz (N:ℕ) (hN:1≤ N) (P:Zf (Zf ℕ))
  (hP:Zt N P)
  (hAP:∀ A∈P,IsAP A/\2≤ A.card/\2≤ apStep A) :
  (P.card:ℝ)≤(129/800:ℝ)*(N:ℝ)^2+12*(N:ℝ)*(log (N:ℝ)+2):=by
 have hsub:∀ A∈P,A⊆Icc 1 N:=fun A hA=>Zy.mp (hP.1 hA)
 have hpart:P.card=∑ d∈Icc 2 N,(P.filter (fun A=>apStep A=d)).card:=by
  rw[←card_biUnion]
  ·congr 1;ext A
   simp only[mem_biUnion,Zb,Za]
   constructor
   ·intro hA
    have hspec:=Qg (hsub A hA) (hAP A hA).1 (hAP A hA).2.1;exact⟨apStep A,⟨(hAP A hA).2.2,hspec.2.1⟩,hA,rfl⟩
   ·rintro⟨_,_,hA,_⟩;exact hA
  ·intro d₁ _ d₂ _ hne
   simp only[Function.onFun];rw[Zk];intro A h1 h2;exact hne ((Za.mp h1).2.symm.trans (Za.mp h2).2)
 have hper_d:∀ d∈Icc 2 N,((P.filter (fun A=>apStep A=d)).card:ℝ) ≤(N:ℝ)^2/(4*(d:ℝ)^2)+4*(N:ℝ)/(d:ℝ)+4:=by
  intro d hd
  have hd1:1≤ d:=by have:=(Zb.mp hd).1;omega
  have hbd:=Ws 1 N d 0 hd1 hN (P.filter (fun A=>apStep A=d))
   (fun A hA=>hsub A (Za.mp hA).1)
   (fun A hA=>by
    obtain⟨hAP',heq⟩:=Za.mp hA;obtain⟨-,-,x₀,k,hk2,-,hX⟩:=Qg (hsub A hAP') (hAP A hAP').1 (hAP A hAP').2.1;rw[heq] at hX;exact⟨x₀,k,hk2,Nat.zero_le _,hX⟩)
   (fun A hA B hB hAB=>Qe hP (Za.mp hA).1 (Za.mp hB).1 hAB)
  have hN1:(((N-1:ℕ):ℝ)/(d:ℝ))≤(N:ℝ)/(d:ℝ) :=div_le_div_of_nonneg_right (by exact_mod_cast Nat.sub_le N 1) (by positivity)
  have hf1:=Xr (((N-1:ℕ):ℝ)/(d:ℝ)) 0 (by positivity) le_rfl
  have hsq:(((N-1:ℕ):ℝ)/(d:ℝ))^2/4≤(N:ℝ)^2/(4*(d:ℝ)^2):=by
   have h1:(((N-1:ℕ):ℝ)/(d:ℝ))^2≤((N:ℝ)/(d:ℝ))^2 :=pow_le_pow_left₀ (by positivity) hN1 2
   have h2:((N:ℝ)/(d:ℝ))^2/4=(N:ℝ)^2/(4*(d:ℝ)^2):=by ring
   linarith
  have h4:4*((N:ℝ)/(d:ℝ))=4*(N:ℝ)/(d:ℝ):=by ring
  linarith
 have hIcc1:Icc 1 N=insert 1 (Icc 2 N):=by ext x;simp only[Zb,Zx];omega
 have h1not:(1:ℕ)∉Icc 2 N:=by simp
 have hinv_sq:∑ d∈Icc 2 N,(1:ℝ)/(d:ℝ)^2≤645/1000:=by have hfull:=W3 N;rw[hIcc1,Finset.sum_insert h1not] at hfull;simp only[one_div] at hfull ⊢;norm_num at hfull;linarith
 have hsum_main:∑ d∈Icc 2 N,(N:ℝ)^2/(4*(d:ℝ)^2) ≤(129/800:ℝ)*(N:ℝ)^2:=by
  have heq:∑ d∈Icc 2 N,(N:ℝ)^2/(4*(d:ℝ)^2) =((N:ℝ)^2/4)*∑ d∈Icc 2 N,(1:ℝ)/(d:ℝ)^2:=by
   rw[Finset.mul_sum];refine Finset.sum_congr rfl fun d _=>?_;ring
  rw[heq];nlinarith
 have hsum_harm:∑ d∈Icc 2 N,4*(N:ℝ)/(d:ℝ) ≤4*(N:ℝ)*(log (N:ℝ)+1):=by
  have heq:∑ d∈Icc 2 N,4*(N:ℝ)/(d:ℝ) =4*(N:ℝ)*∑ d∈Icc 2 N,(1:ℝ)/(d:ℝ):=by
   rw[Finset.mul_sum];refine Finset.sum_congr rfl fun d _=>?_;ring
  rw[heq]
  have hle:∑ d∈Icc 2 N,(1:ℝ)/(d:ℝ)≤∑ d∈Icc 1 N,(1:ℝ)/(d:ℝ) :=sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc (by omega) le_rfl) (fun _ _ _=>by positivity)
  have hhm:=Q0 N hN
  have hN0:(0:ℝ)≤4*(N:ℝ):=by positivity
  nlinarith
 have hsum_four:∑ _d∈Icc 2 N,(4:ℝ)≤4*(N:ℝ):=by
  rw[Finset.sum_const,Nat.card_Icc,nsmul_eq_mul]
  have:((N+1-2:ℕ):ℝ)≤(N:ℝ):=by exact_mod_cast (by omega:N+1-2≤ N)
  linarith
 have hlog0:0≤ log (N:ℝ):=Real.log_nonneg (by exact_mod_cast hN)
 calc (P.card:ℝ)
     = ∑ d∈Icc 2 N,((P.filter (fun A=>apStep A=d)).card:ℝ):=by exact_mod_cast hpart
   _≤∑ d∈Icc 2 N,((N:ℝ)^2/(4*(d:ℝ)^2)+4*(N:ℝ)/(d:ℝ)+4) :=
       Finset.sum_le_sum hper_d
   _=(∑ d∈Icc 2 N,(N:ℝ)^2/(4*(d:ℝ)^2)) +
       (∑ d∈Icc 2 N,4*(N:ℝ)/(d:ℝ)) +
       (∑ _d∈Icc 2 N,(4:ℝ)):=by simp only[Finset.sum_add_distrib]
   _≤(129/800:ℝ)*(N:ℝ)^2+4*(N:ℝ)*(log (N:ℝ)+1)+4*(N:ℝ):=by linarith
   _≤(129/800:ℝ)*(N:ℝ)^2+12*(N:ℝ)*(log (N:ℝ)+2):=by nlinarith
lemma Kn {L m s:ℝ} (hs:0< s):fInt (L*s) (m*s)=fInt L m*s^2:=by
 unfold fInt;have hlt:L*s< m*s↔L< m:=mul_lt_mul_iff_left₀ hs
 have h2m:2*(m*s)≤ L*s↔2*m≤ L:=by
  have:2*(m*s)=(2*m)*s:=by ring
  rw[this];exact mul_le_mul_iff_left₀ hs
 by_cases h1:L< m
 ·rw[if_pos (hlt.mpr h1),if_pos h1,zero_mul]
 ·rw[if_neg (mt hlt.mp h1),if_neg h1]
  by_cases h2:2*m≤ L
  ·rw[if_pos (h2m.mpr h2),if_pos h2];ring
  ·rw[if_neg (mt h2m.mp h2),if_neg h2];ring
lemma Qy (N a b d m_nat:ℕ) {L:ℝ}
  (hN:1≤ N) (hd:1≤ d) (hL1:L≤1)
  (hba:a≤ b->((b-a:ℕ):ℝ)≤ L*(N:ℝ))
  (F:Zf (Zf ℕ))
  (hsub:∀ A∈F,A⊆Icc a b)
  (hstep:∀ A∈F,∃ x₀ k,2≤ k/\m_nat≤ k/\∀ x,x∈A↔∃ i< k,x=x₀+i*d)
  (hmeet:∀ A∈F,∀ B∈F,A≠B->(A∩B).Nonempty) :
  (F.card:ℝ)≤ fInt (L/(d:ℝ)) ((m_nat:ℝ)/(N:ℝ))*(N:ℝ)^2+8*(N:ℝ):=by
 have hNpos:(0:ℝ)<(N:ℝ):=by exact_mod_cast (by omega:0< N)
 have hdpos:(0:ℝ)<(d:ℝ):=by exact_mod_cast (by omega:0< d)
 rcases le_or_gt a b with hab|hlt
 ·have hbd:=Ws a b d m_nat hd hab F hsub hstep hmeet
  have hL_le:(((b-a:ℕ):ℝ)/(d:ℝ))≤(L/(d:ℝ))*(N:ℝ):=by
   have h1:(((b-a:ℕ):ℝ)/(d:ℝ))≤(L*(N:ℝ))/(d:ℝ) :=div_le_div_of_nonneg_right (hba hab) hdpos.le
   linarith[show (L*(N:ℝ))/(d:ℝ)=(L/(d:ℝ))*(N:ℝ) by ring]
  have hf1:fInt (((b-a:ℕ):ℝ)/(d:ℝ)) (m_nat:ℝ) ≤ fInt ((L/(d:ℝ))*(N:ℝ)) (((m_nat:ℝ)/(N:ℝ))*(N:ℝ)):=by
   rw[div_mul_cancel₀ _ hNpos.ne']
   exact Wf (by positivity) hL_le (by positivity)
  rw[Kn hNpos] at hf1
  have h4:4*(((b-a:ℕ):ℝ)/(d:ℝ))+4≤8*(N:ℝ):=by
   have h1:(L/(d:ℝ))*(N:ℝ)≤(N:ℝ):=by
    have hLd:L/(d:ℝ)≤1:=by
     rw[div_le_one hdpos];exact hL1.trans (by exact_mod_cast hd)
    nlinarith
   have hN1:(1:ℝ)≤(N:ℝ):=by exact_mod_cast hN
   linarith
  linarith
 ·have hF0:F=∅:=by
   rw[eq_empty_iff_forall_notMem];intro A hA;obtain⟨x₀,k,hk2,-,hX⟩:=hstep A hA
   have hx0:x₀∈Icc a b:=hsub A hA ((hX x₀).mpr ⟨0,by omega,by simp⟩)
   have:=Zb.mp hx0;omega
  rw[hF0,card_empty,Nat.cast_zero]
  have hf0:=Vf (L/(d:ℝ)) ((m_nat:ℝ)/(N:ℝ)) (by positivity)
  nlinarith[sq_nonneg (N:ℝ)]
def Qm (N:ℕ) (S:Zf ℕ):Zf ℕ:=S.image (fun x=>N+1-x)
def Ql (N:ℕ) (F:Zf (Zf ℕ)):Zf (Zf ℕ):=F.image (Qm N)
private lemma Xz {N:ℕ} {S:Zf ℕ} (hS:S⊆Icc 1 N) :Qm N S⊆Icc 1 N:=by
 intro y hy;obtain⟨x,hx,rfl⟩:=Zi.mp hy;have hx':=Zb.mp (hS hx)
 exact Zb.mpr ⟨by omega,by omega⟩
private lemma Wn {N:ℕ} {S:Zf ℕ} (hS:S⊆Icc 1 N) :Qm N (Qm N S)=S:=by
 ext y;simp only[Qm,Zi]
 constructor
 ·rintro⟨z,⟨x,hx,rfl⟩,rfl⟩
  have hx':=Zb.mp (hS hx)
  have:N+1-(N+1-x)=x:=by omega
  rwa[this]
 ·intro hy
  have hy':=Zb.mp (hS hy)
  exact⟨N+1-y,⟨y,hy,rfl⟩,by omega⟩
private lemma Q9 {N:ℕ} {S:Zf ℕ} (hS:S⊆Icc 1 N) :(Qm N S).card=S.card:=by
 unfold Qm
 refine card_image_of_injOn fun x hx y hy hxy=>?_
 have hx':=Zb.mp (hS (Zc.mp hx));have hy':=Zb.mp (hS (Zc.mp hy));omega
private lemma Q5 {N:ℕ} {S:Zf ℕ} (hS:S⊆Icc 1 N)
  {x:ℕ} (hx:x∈Icc 1 N) :
  N+1-x∈Qm N S↔x∈S:=by
 have hx':=Zb.mp hx
 constructor
 ·intro h
  obtain⟨z,hz,heq⟩:=Zi.mp h;have hz':=Zb.mp (hS hz)
  have:z=x:=by omega
  rwa[←this]
 ·intro h;exact Zi.mpr ⟨x,h,rfl⟩
private lemma V4 {N:ℕ} {S T:Zf ℕ}
  (hS:S⊆Icc 1 N) (hT:T⊆Icc 1 N) :
  Qm N (S∩T)=Qm N S∩Qm N T:=by
 ext y;simp only[Qm,Zi,Zn]
 constructor
 ·rintro⟨x,⟨hxS,hxT⟩,rfl⟩;exact⟨⟨x,hxS,rfl⟩,⟨x,hxT,rfl⟩⟩
 ·rintro⟨⟨x,hxS,rfl⟩,⟨z,hzT,hxz⟩⟩
  have hx':=Zb.mp (hS hxS);have hz':=Zb.mp (hT hzT)
  have:z=x:=by omega
  exact⟨x,⟨hxS,this ▸ hzT⟩,rfl⟩
private lemma Xl {N a d k:ℕ} {S:Zf ℕ}
  (hS:S⊆Icc 1 N) (hk:1≤ k)
  (hX:∀ x,x∈S↔∃ i< k,x=a+i*d) :
  ∀ y,y∈Qm N S↔∃ j< k,y=(N+1-(a+(k-1)*d))+j*d:=by
 have hmax:a+(k-1)*d≤ N :=(Zb.mp (hS ((hX _).mpr ⟨k-1,by omega,rfl⟩))).2
 intro y;simp only[Qm,Zi]
 constructor
 ·rintro⟨x,hx,rfl⟩
  obtain⟨i,hi,rfl⟩:=(hX x).mp hx
  refine⟨k-1-i,by omega,?_⟩
  have hmul:i*d+(k-1-i)*d=(k-1)*d:=by rw[←Nat.add_mul];congr 1;omega
  omega
 ·rintro⟨j,hj,rfl⟩
  refine⟨a+(k-1-j)*d,(hX _).mpr ⟨k-1-j,by omega,rfl⟩,?_⟩
  have hmul:(k-1-j)*d+j*d=(k-1)*d:=by rw[←Nat.add_mul];congr 1;omega
  omega
private lemma Q8 {N:ℕ} {S:Zf ℕ} (hS:S⊆Icc 1 N) :IsAP (Qm N S)↔IsAP S:=by
 have hfwd:∀ T:Zf ℕ,T⊆Icc 1 N->IsAP T->IsAP (Qm N T):=by intro T hT ⟨a,d,k,hk,hdk,hX⟩;exact⟨N+1-(a+(k-1)*d),d,k,hk,hdk,Xl hT hk hX⟩
 exact⟨fun h=>by rw[←Wn hS];exact hfwd _ (Xz hS) h,hfwd S hS⟩
private lemma Xe {N:ℕ} {S:Zf ℕ}
  (hS:S⊆Icc 1 N) (hAP:IsAP S) (h2:2≤ S.card) :
  apStep (Qm N S)=apStep S:=by
 obtain⟨hd1,-,a,k,hk2,-,hX⟩:=Qg hS hAP h2
 exact Kf hk2 hd1 (Xl hS (by omega) hX)
private lemma Xg {N c:ℕ} {S:Zf ℕ}
  (hc:c∈Icc 1 N) (hR:S⊆Icc (c+1) N) :
  Qm N S⊆Icc 1 ((N+1-c)-1):=by
 have hc':=Zb.mp hc;intro y hy;obtain⟨x,hx,rfl⟩:=Zi.mp hy;have hx':=Zb.mp (hR hx)
 exact Zb.mpr ⟨by omega,by omega⟩
private lemma W1 {N:ℕ} {F:Zf (Zf ℕ)}
  (hF:Zt N F):Zt N (Ql N F):=by
 have hsub:∀ S∈F,S⊆Icc 1 N:=fun S hS=>Zy.mp (hF.1 hS)
 refine⟨?_,?_⟩
 ·intro T hT
  obtain⟨S,hS,rfl⟩:=Zi.mp hT;exact Zy.mpr (Xz (hsub S hS))
 ·intro A hA B hB hAB
  obtain⟨S,hS,rfl⟩:=Zi.mp (Zc.mp hA);obtain⟨T,hT,rfl⟩:=Zi.mp (Zc.mp hB)
  have hST:S≠T:=fun h=>hAB (by rw[h])
  obtain⟨l,hl,hl'⟩:=hF.2 (Zc.mpr hS) (Zc.mpr hT) hST;have hAP_ST:IsAP (S∩T):=Qn (S∩T) l hl hl';rw[←V4 (hsub S hS) (hsub T hT)];exact Vn ((Q8 (Yf.trans (hsub S hS))).mpr hAP_ST)
private lemma Wi {N:ℕ} {F:Zf (Zf ℕ)}
  (hsub:∀ S∈F,S⊆Icc 1 N):(Ql N F).card=F.card:=by
 unfold Ql
 refine card_image_of_injOn fun S hS T hT hST=>?_
 have h1:=Wn (hsub S (Zc.mp hS));have h2:=Wn (hsub T (Zc.mp hT));rw[←h1,←h2,hST]
private lemma Q3 {N:ℕ} {F G:Zf (Zf ℕ)}
  (hF:∀ S∈F,S⊆Icc 1 N) (hG:∀ S∈G,S⊆Icc 1 N)
  (hdisj:Disjoint F G):Disjoint (Ql N F) (Ql N G):=by
 rw[Zk];intro A hAF hAG;obtain⟨S,hS,rfl⟩:=Zi.mp hAF;obtain⟨T,hT,hST⟩:=Zi.mp hAG
 have heq:S=T:=by have h1:=Wn (hF S hS);have h2:=Wn (hG T hT);rw[←h1,←h2,hST]
 exact Zk.mp hdisj hS (heq ▸ hT)
private lemma Xi {N:ℕ} {A:Zf ℕ}
  (hsub:A⊆Icc 1 N) (hAP:IsAP A) (h2:2≤ A.card) :
  ∀ x∈A,∀ y∈A,x % apStep A=y % apStep A:=by
 obtain⟨-,-,a,k,-,-,hX⟩:=Qg hsub hAP h2;intro x hx y hy;obtain⟨i,-,rfl⟩:=(hX x).mp hx;obtain⟨j,-,rfl⟩:=(hX y).mp hy;rw[Nat.add_mul_mod_self_right,Nat.add_mul_mod_self_right]
private lemma Wj {N c:ℕ} {A:Zf ℕ}
  (hsub:A⊆Icc 1 N) (hAP:IsAP A) (h2:2≤ A.card) (hcA:c∉A)
  (hmod:∀ x∈A,x % apStep A=c % apStep A) :
  A⊆Icc 1 (c-1)\/A⊆Icc (c+1) N:=by
 obtain⟨hd1,-,a,k,hk2,-,hX⟩:=Qg hsub hAP h2;set d:=apStep A
 by_cases hca:c< a
 ·right
  intro x hx;obtain⟨i,-,rfl⟩:=(hX x).mp hx;have hxN:=(Zb.mp (hsub hx)).2
  exact Zb.mpr ⟨by omega,hxN⟩
 ·by_cases htop:a+(k-1)*d< c
  ·left
   intro x hx;obtain⟨i,hi,rfl⟩:=(hX x).mp hx;have hx1:=(Zb.mp (hsub hx)).1
   have hmul:i*d≤(k-1)*d:=Yc d (by omega)
   exact Zb.mpr ⟨hx1,by omega⟩
  ·exfalso
   have haA:a∈A:=(hX a).mpr ⟨0,by omega,by simp⟩
   have hamod:a % d=c % d:=hmod a haA;have hda:=Nat.div_add_mod a d;have hdc:=Nat.div_add_mod c d
   have hdiv_le:a/d≤ c/d:=Nat.div_le_div_right (by omega)
   set i:=c/d-a/d
   have hci:c=a+i*d:=by
    have h1:d*(a/d)+i*d=d*(c/d):=by rw[Nat.mul_comm d (a/d),Nat.mul_comm d (c/d),←Nat.add_mul];congr 1;omega
    omega
   have hi_lt:i< k:=by
    have:i*d≤(k-1)*d:=by omega
    have:i≤ k-1:=Nat.le_of_mul_le_mul_right this (by omega)
    omega
   exact hcA ((hX c).mpr ⟨i,hi_lt,hci⟩)
private lemma Wu {N c:ℕ} {F:Zf (Zf ℕ)}
  (hF:Zt N F)
  (hne:∀ A∈F,A.Nonempty)
  (hone:∀ A∈F,A⊆Icc 1 (c-1)\/A⊆Icc (c+1) N) :
  (∀ A∈F,A⊆Icc 1 (c-1))\/(∀ A∈F,A⊆Icc (c+1) N):=by
 by_cases hL:∀ A∈F,A⊆Icc 1 (c-1)
 ·exact Or.inl hL
 ·right
  push Not at hL
  obtain⟨A₀,hA₀,hnotL⟩:=hL;have hA₀R:A₀⊆Icc (c+1) N:=(hone A₀ hA₀).resolve_left hnotL;intro B hB
  rcases hone B hB with hBL|hBR
  ·exfalso
   have hneB:B≠A₀:=by
    rintro rfl
    obtain⟨x,hx⟩:=hne B hB;have h1:=(Zb.mp (hBL hx)).2;have h2:=(Zb.mp (hA₀R hx)).1;omega
   obtain⟨x,hx⟩:=Qe hF hB hA₀ hneB;have h1:=(Zb.mp (hBL (Zn.mp hx).1)).2;have h2:=(Zb.mp (hA₀R (Zn.mp hx).2)).1;omega
  ·exact hBR
private lemma Xp {N m_nat d_max:ℕ} {A:Zf ℕ}
  (hsub:A⊆Icc 1 N) (hAP:IsAP A) (h2:2≤ A.card)
  (hm:m_nat≤ A.card) (hbig:N≤(d_max+1)*(m_nat-1)) :
  apStep A≤ d_max:=by
 obtain⟨-,-,a,k,hk2,hcard,hX⟩:=Qg hsub hAP h2
 have ha1:=(Zb.mp (hsub ((hX a).mpr ⟨0,by omega,by simp⟩))).1
 have hmaxN:=(Zb.mp (hsub ((hX _).mpr ⟨k-1,by omega,rfl⟩))).2
 have hlen:(m_nat-1)*apStep A< N:=by
  have:(m_nat-1)*apStep A≤(k-1)*apStep A:=Yc _ (by omega)
  omega
 by_contra hgt
 have hge:d_max+1≤ apStep A:=by omega
 have:(d_max+1)*(m_nat-1)≤(m_nat-1)*apStep A:=by rw[Nat.mul_comm (m_nat-1)];exact Yc _ hge
 omega
private lemma Xx {N c:ℕ} {A B:Zf ℕ}
  (hsub:A⊆Icc 1 N) (hAP:IsAP A) (h2:2≤ A.card) (hcA:c∈A)
  (hmeet:(A∩B).Nonempty) (hB:∀ x∈B,x % 2≠c % 2) :
  Odd (apStep A):=by
 rw[Nat.odd_iff];by_contra hne
 have hdiv:2 ∣ apStep A:=by omega
 obtain⟨z,hz⟩:=hmeet;have hmodA:=Xi hsub hAP h2 z (Zn.mp hz).1 c hcA
 have hmod2:z % 2=c % 2:=by have h1:=Nat.mod_mod_of_dvd z hdiv;have h2':=Nat.mod_mod_of_dvd c hdiv;rw[←h1,←h2',hmodA]
 exact hB z (Zn.mp hz).2 hmod2
private lemma Wg (N d₁ d₂ m_nat:ℕ) (hN:1≤ N) (hd₁:1≤ d₁)
  (F:Zf (Zf ℕ)) (hF:Zt N F)
  (hAP:∀ A∈F,IsAP A/\2≤ A.card/\m_nat≤ A.card/\apStep A∈Icc d₁ d₂) :
  (F.card:ℝ) ≤(∑ d∈Icc d₁ d₂,fInt (1/(d:ℝ)) ((m_nat:ℝ)/(N:ℝ)))*(N:ℝ)^2 +8*((d₂+1-d₁:ℕ):ℝ)*(N:ℝ):=by
 have hsub:∀ A∈F,A⊆Icc 1 N:=fun A hA=>Zy.mp (hF.1 hA)
 have hpart:F.card=∑ d∈Icc d₁ d₂,(F.filter (fun A=>apStep A=d)).card:=by
  rw[←card_biUnion]
  ·congr 1;ext A
   simp only[mem_biUnion,Za]
   exact⟨fun hA=>⟨apStep A,(hAP A hA).2.2.2,hA,rfl⟩,fun ⟨_,_,hA,_⟩=>hA⟩
  ·intro a _ b _ hab
   simp only[Function.onFun];rw[Zk];intro A h1 h2;exact hab ((Za.mp h1).2.symm.trans (Za.mp h2).2)
 have hper:∀ d∈Icc d₁ d₂,((F.filter (fun A=>apStep A=d)).card:ℝ) ≤ fInt (1/(d:ℝ)) ((m_nat:ℝ)/(N:ℝ))*(N:ℝ)^2+8*(N:ℝ):=by
  intro d hd;have hd1:1≤ d:=le_trans hd₁ (Zb.mp hd).1
  refine Qy N 1 N d m_nat hN hd1 le_rfl
   (fun _=>by rw[one_mul];exact_mod_cast Nat.sub_le N 1)
   (F.filter (fun A=>apStep A=d))
   (fun A hA=>hsub A (Za.mp hA).1)
   (fun A hA=>by
    obtain⟨hAF,hst⟩:=Za.mp hA;obtain⟨-,-,x₀,k,hk2,hcard,hX⟩:=Qg (hsub A hAF) (hAP A hAF).1 (hAP A hAF).2.1;rw[hst] at hX
    exact⟨x₀,k,hk2,by rw[←hcard];exact (hAP A hAF).2.2.1,hX⟩)
   (fun A hA B hB hAB=>Qe hF (Za.mp hA).1 (Za.mp hB).1 hAB)
 calc (F.card:ℝ)
     = ∑ d∈Icc d₁ d₂,((F.filter (fun A=>apStep A=d)).card:ℝ):=by exact_mod_cast hpart
   _≤∑ d∈Icc d₁ d₂,(fInt (1/(d:ℝ)) ((m_nat:ℝ)/(N:ℝ))*(N:ℝ)^2+8*(N:ℝ)) :=
       Finset.sum_le_sum hper
   _=(∑ d∈Icc d₁ d₂,fInt (1/(d:ℝ)) ((m_nat:ℝ)/(N:ℝ)))*(N:ℝ)^2 +
       8*((d₂+1-d₁:ℕ):ℝ)*(N:ℝ):=by
       rw[Finset.sum_add_distrib,←Finset.sum_mul,Finset.sum_const,Nat.card_Icc,nsmul_eq_mul];ring
private lemma V3 (N c m_nat:ℕ) (hN:1≤ N) (hc:c∈Icc 1 N) (mod2:Bool)
  (F:Zf (Zf ℕ)) (hF:Zt N F)
  (hAP:∀ A∈F,IsAP A/\2≤ A.card/\c∉A/\m_nat≤ A.card/\apStep A=2)
  (hmod:mod2=false->∀ A∈F,∀ x∈A,x % 2=c % 2) :
  let y:ℝ:=((N-c:ℕ):ℝ)/(N:ℝ)
  (F.card:ℝ) ≤ fInt (if mod2 then 1/2 else max (1-y) y/2) ((m_nat:ℝ)/(N:ℝ))*(N:ℝ)^2+8*(N:ℝ):=by
 intro y
 have hsub:∀ A∈F,A⊆Icc 1 N:=fun A hA=>Zy.mp (hF.1 hA)
 have hstep2:∀ A∈F,∃ x₀ k,2≤ k/\m_nat≤ k/\∀ x,x∈A↔∃ i< k,x=x₀+i*2:=by
  intro A hA;obtain⟨-,-,x₀,k,hk2,hcard,hX⟩:=Qg (hsub A hA) (hAP A hA).1 (hAP A hA).2.1;rw[(hAP A hA).2.2.2.2] at hX
  exact⟨x₀,k,hk2,by rw[←hcard];exact (hAP A hA).2.2.2.1,hX⟩
 have hmeet:∀ A∈F,∀ B∈F,A≠B->(A∩B).Nonempty:=fun _ hA _ hB hAB=>Qe hF hA hB hAB
 have hNpos:(0:ℝ)<(N:ℝ):=by exact_mod_cast (by omega:0< N)
 have hcN:=(Zb.mp hc).2
 have h1my:1-y=(c:ℝ)/(N:ℝ):=by dsimp only[y];rw[Nat.cast_sub hcN];field_simp;ring
 cases mod2
 ·simp only[Bool.false_eq_true,↓reduceIte]
  have hmod_all:=hmod rfl
  have hone:∀ A∈F,A⊆Icc 1 (c-1)\/A⊆Icc (c+1) N:=fun A hA =>
   Wj (hsub A hA) (hAP A hA).1 (hAP A hA).2.1 (hAP A hA).2.2.1
    (by rw[(hAP A hA).2.2.2.2];exact hmod_all A hA)
  have hne:∀ A∈F,A.Nonempty:=fun A hA=>card_pos.mp (by have:=(hAP A hA).2.1;omega)
  have hL1:max (1-y) y≤1:=by
   refine max_le ?_ ?_
   ·rw[h1my,div_le_one hNpos];exact_mod_cast hcN
   ·dsimp only[y];rw[div_le_one hNpos];exact_mod_cast Nat.sub_le N c
  rcases Wu hF hne hone with hL|hR
  ·have hba:1≤ c-1->(((c-1)-1:ℕ):ℝ)≤ max (1-y) y*(N:ℝ):=by
    intro _
    have h1:(((c-1)-1:ℕ):ℝ)≤(c:ℝ):=by exact_mod_cast (by omega:c-1-1≤ c)
    have h2:(c:ℝ)=(1-y)*(N:ℝ):=by rw[h1my,div_mul_cancel₀ _ hNpos.ne']
    have h3:(1-y)*(N:ℝ)≤ max (1-y) y*(N:ℝ) :=Zo (Ym _ _) hNpos.le;linarith
   simpa only [Nat.cast_ofNat] using
    Qy N 1 (c-1) 2 m_nat hN (by omega) hL1 hba F hL hstep2 hmeet
  ·have hba:c+1≤ N->((N-(c+1):ℕ):ℝ)≤ max (1-y) y*(N:ℝ):=by
    intro _
    have h1:((N-(c+1):ℕ):ℝ)≤((N-c:ℕ):ℝ):=by exact_mod_cast (by omega:N-(c+1)≤ N-c)
    have h2:((N-c:ℕ):ℝ)=y*(N:ℝ):=by dsimp only[y];rw[div_mul_cancel₀ _ hNpos.ne']
    have h3:y*(N:ℝ)≤ max (1-y) y*(N:ℝ) :=Zo (Yn _ _) hNpos.le;linarith
   simpa only [Nat.cast_ofNat] using
    Qy N (c+1) N 2 m_nat hN (by omega) hL1 hba F hR hstep2 hmeet
 ·simp only[↓reduceIte]
  simpa only [Nat.cast_ofNat] using
   Qy N 1 N 2 m_nat hN (by omega) le_rfl
    (fun _=>by rw[one_mul];exact_mod_cast Nat.sub_le N 1) F hsub hstep2 hmeet
private lemma Xc (N c:ℕ) (hN:1000≤ N) (hc:c∈Icc 1 N)
  (Q_c P_c P_nc:Zf (Zf ℕ)) (B:Zf ℕ)
  (hF:Zt N (Q_c∪P_c∪P_nc))
  (hdisjQP:Disjoint Q_c P_c) (_hdisjQN:Disjoint Q_c P_nc) (hdisjPN:Disjoint P_c P_nc)
  (hQc:∀ S∈Q_c,¬ IsAP S/\c∈S)
  (hPc:∀ A∈P_c,IsAP A/\2≤ A.card/\c∈A)
  (hPnc:∀ A∈P_nc,IsAP A/\2≤ A.card/\c∉A ∧
   apStep A∈Icc 2 5/\(19/100:ℝ)*(N:ℝ)≤(A.card:ℝ))
  (hB:B∈P_nc) (hBL:B⊆Icc 1 (c-1)) :
  (Q_c.card:ℝ)+(P_c.card:ℝ)+(P_nc.card:ℝ) ≤(N:ℝ)^2/2+500*(N:ℝ)*(log (N:ℝ)+2)^2 +8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5):=by
 classical
 have hN1:1≤ N:=by omega
 have hNpos:(0:ℝ)<(N:ℝ):=by exact_mod_cast (by omega:0< N)
 have hcN:=(Zb.mp hc).2
 have hlog0:0≤ log (N:ℝ):=Real.log_nonneg (by exact_mod_cast hN1)
 have hlog2_ge:(2:ℝ)≤ log (N:ℝ)+2:=by linarith
 have hLsq:log (N:ℝ)+2≤(log (N:ℝ)+2)^2:=by nlinarith only[hlog2_ge]
 have h1sq:(1:ℝ)≤(log (N:ℝ)+2)^2:=by nlinarith only[hlog2_ge]
 have hsubB:B⊆Icc 1 N:=Zy.mp (hF.1 (Zg _ hB));have hBspec:=hPnc B hB;set d₀:=apStep B;obtain⟨hd₀1,-,L_s,m_b,hmb2,hBcard,hBseq⟩:=Qg hsubB hBspec.1 hBspec.2.1;have hd₀_Icc:d₀∈Icc 2 5:=hBspec.2.2.2.1
 have hL1:1≤ L_s:=(Zb.mp (hBL ((hBseq L_s).mpr ⟨0,by omega,by simp⟩))).1
 have hR_le:L_s+(m_b-1)*d₀≤ c-1 :=(Zb.mp (hBL ((hBseq _).mpr ⟨m_b-1,by omega,rfl⟩))).2
 have hRc:L_s+(m_b-1)*d₀< c:=by omega
 set R_s:=L_s+(m_b-1)*d₀
 set P1_c:=P_c.filter (fun A=>apStep A=1)
 set P2_c:=P_c.filter (fun A=>2≤ apStep A)
 have hPc_part:P_c.card=P1_c.card+P2_c.card:=by
  have hdisj:Disjoint P1_c P2_c:=by
   rw[Zk];intro A h1 h2
   have:=(Za.mp h1).2;have:=(Za.mp h2).2;omega
  rw[←Zq hdisj];congr 1;ext A;simp only[P1_c,P2_c,Zd,Za]
  constructor
  ·intro hA
   have h1:=(Qg (Zy.mp (hF.1 (Ze _ (Zg _ hA))))
    (hPc A hA).1 (hPc A hA).2.1).1
   rcases Nat.eq_or_lt_of_le h1 with h|h
   ·exact Or.inl ⟨hA,h.symm⟩
   ·exact Or.inr ⟨hA,h⟩
  ·rintro (⟨hA,_⟩|⟨hA,_⟩) <;> exact hA
 have hB_erase:B⊆(Icc 1 N).erase c:=fun x hx =>
  Zw.mpr ⟨fun h=>hBspec.2.2.1 (h ▸ hx),hsubB hx⟩
 have hQc_hit:∀ S∈Q_c,(S∩B).Nonempty:=fun S hS =>
  Qe hF (Ze _ (Ze _ hS)) (Zg _ hB)
   (fun h=>hBspec.2.2.1 (h ▸ (hQc S hS).2))
 have hPc_hit:∀ A∈P_c,(A∩B).Nonempty:=fun A hA =>
  Qe hF (Ze _ (Zg _ hA)) (Zg _ hB)
   (fun h=>hBspec.2.2.1 (h ▸ (hPc A hA).2.2))
 have hQ_sub:Zt N Q_c :=Qd hF ((Zr).trans Zr)
 have hP1Q_sub:Zt N (P1_c∪Q_c):=by
  refine Qd hF (Zu ?_ ?_)
  ·exact ((Zl _ _).trans Zs).trans Zr
  ·exact Zr.trans Zr
 have hP1Q_disj:Disjoint P1_c Q_c :=(Finset.disjoint_of_subset_left (Zl _ _) hdisjQP.symm)
 have hstep_bd:=Xd N c L_s d₀ m_b hN1 hc hd₀1 (by omega) hL1 hRc B hBseq
  P1_c Q_c hP1Q_sub hP1Q_disj
  (fun A hA=>by
   obtain⟨hA',h1⟩:=Za.mp hA;exact⟨(hPc A hA').1,(hPc A hA').2.1,(hPc A hA').2.2,h1⟩)
  (fun A hA=>hPc_hit A (Za.mp hA).1) hQc
 have hnonhit:=Qw N c hN1 Q_c B hQ_sub (fun S hS=>(hQc S hS).1)
  (fun S hS=>(hQc S hS).2) hB_erase hQc_hit
 have hQ_split:(Q_c.card:ℝ)=((Qa c B Q_c).card:ℝ)+((Q_c \ Qa c B Q_c).card:ℝ):=by
  have:=Yb (Qx c B Q_c)
  exact_mod_cast (by omega:Q_c.card=(Qa c B Q_c).card+(Q_c \ Qa c B Q_c).card)
 set mb:ℝ:=(m_b:ℝ)/(N:ℝ);set g:ℝ:=((c-R_s:ℕ):ℝ)/(N:ℝ);set y:ℝ:=((N-c:ℕ):ℝ)/(N:ℝ)
 set core:ℝ:=max ((mb-mb^2/2)+(max 0 (((d₀:ℝ)-1)*y-g))^2/(4*(d₀:ℝ)-2))
           (y-y^2-g*y)
 have hQP1:(Q_c.card:ℝ)+(P1_c.card:ℝ) ≤ core*(N:ℝ)^2+12*(d₀:ℝ)*(N:ℝ)+8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5):=by dsimp only[core,mb,g,y,R_s] at hstep_bd ⊢;linarith
 have hmb_ge:19/100≤ mb:=by dsimp only[mb];rw[le_div_iff₀ hNpos,←hBcard];exact hBspec.2.2.2.2
 have hy_nn:0≤ y:=by positivity
 have hg_nn:0≤ g:=by positivity
 have hpack_nat:d₀*m_b+(N-c)≤ N+d₀-2:=by
  have hmul:(m_b-1)*d₀+d₀=m_b*d₀:=by
   have:(m_b-1+1)*d₀=(m_b-1)*d₀+d₀:=by rw[Nat.add_mul,one_mul]
   rw[Nat.sub_add_cancel (by omega:1≤ m_b)] at this;exact this.symm
  have:d₀*m_b=m_b*d₀:=Nat.mul_comm d₀ m_b
  have hd2:=(Zb.mp hd₀_Icc).1;omega
 have hpack:(d₀:ℝ)*mb+y≤ if d₀=2 then 1 else 101/100:=by
  split_ifs with hd2
  ·rw[hd2] at hpack_nat ⊢
   have hle:(2*m_b+(N-c):ℕ)≤ N:=by omega
   have hleR:2*(m_b:ℝ)+((N-c:ℕ):ℝ)≤(N:ℝ):=by exact_mod_cast hle
   dsimp only[mb,y];rw[Nat.cast_ofNat]
   have:(2:ℝ)*((m_b:ℝ)/(N:ℝ))+((N-c:ℕ):ℝ)/(N:ℝ) =(2*(m_b:ℝ)+((N-c:ℕ):ℝ))/(N:ℝ):=by ring
   rw[this,div_le_one hNpos];exact hleR
  ·have hd5:=(Zb.mp hd₀_Icc).2
   have hle:d₀*m_b+(N-c)≤ N+3:=by omega
   have hleR:(d₀:ℝ)*(m_b:ℝ)+((N-c:ℕ):ℝ)≤(N:ℝ)+3:=by exact_mod_cast hle
   have hN1000:(1000:ℝ)≤(N:ℝ):=by exact_mod_cast hN
   dsimp only[mb,y]
   have:(d₀:ℝ)*((m_b:ℝ)/(N:ℝ))+((N-c:ℕ):ℝ)/(N:ℝ) =((d₀:ℝ)*(m_b:ℝ)+((N-c:ℕ):ℝ))/(N:ℝ):=by ring
   rw[this,div_le_iff₀ hNpos];linarith
 have hd0_le5:(d₀:ℝ)≤5:=by exact_mod_cast (Zb.mp hd₀_Icc).2
 rcases Vw d₀ hd₀_Icc hmb_ge hy_nn hg_nn hpack with hineq|⟨-,hineq⟩
 ·have hP2N_disj:Disjoint P2_c P_nc :=Finset.disjoint_of_subset_left (Zl _ _) hdisjPN
  have hP2N_sub:Zt N (P2_c∪P_nc) :=Qd hF (Zu
    (((Zl _ _).trans Zs).trans Zr)
    Zs)
  have hP2N_bd:=Wz N hN1 (P2_c∪P_nc) hP2N_sub (fun A hA=>by
   rcases Zd.mp hA with h1|h2
   ·obtain⟨hA',hst⟩:=Za.mp h1
    exact⟨(hPc A hA').1,(hPc A hA').2.1,hst⟩
   ·exact⟨(hPnc A h2).1,(hPnc A h2).2.1,(Zb.mp (hPnc A h2).2.2.2.1).1⟩)
  rw[Zq hP2N_disj,Nat.cast_add] at hP2N_bd
  have hPcR:(P_c.card:ℝ)=(P1_c.card:ℝ)+(P2_c.card:ℝ):=by exact_mod_cast hPc_part
  have herr:12*(d₀:ℝ)*(N:ℝ)+12*(N:ℝ)*(log (N:ℝ)+2) ≤500*(N:ℝ)*(log (N:ℝ)+2)^2:=by nlinarith only[hNpos,hd0_le5,hLsq,h1sq]
  have hmain:(core+129/800)*(N:ℝ)^2≤(N:ℝ)^2/2:=by
   calc (core+129/800)*(N:ℝ)^2≤(1/2)*(N:ℝ)^2 :=
         Zo hineq (sq_nonneg _)
     _=(N:ℝ)^2/2:=by ring
  linarith only[hPcR,hQP1,hP2N_bd,herr,hmain]
 ·have hPc_left:∀ A∈P_c,∃ z∈A,z≤ R_s:=fun A hA=>by
   obtain⟨z,hz⟩:=hPc_hit A hA;obtain⟨i,hi,rfl⟩:=(hBseq z).mp (Zn.mp hz).2
   have hmul:i*d₀≤(m_b-1)*d₀:=Yc d₀ (by omega)
   exact⟨L_s+i*d₀,(Zn.mp hz).1,by dsimp only[R_s];omega⟩
  have hP2c_bd:=(Xh N c R_s hN1 hc hRc P_c
   (fun A hA=>Zy.mp (hF.1 (Ze _ (Zg _ hA))))
   hPc hPc_left).2.1
  have hP2c_y:(P2_c.card:ℝ)≤(645/1000:ℝ)*(1-y)*y*(N:ℝ)^2 +4*(N:ℝ)*(log (N:ℝ)+2):=by
   have hRc_le:(R_s:ℝ)≤(c:ℝ):=by exact_mod_cast (by omega:R_s≤ c)
   have h1my:(1-y)*y*(N:ℝ)^2=(c:ℝ)*((N-c:ℕ):ℝ):=by dsimp only[y];rw[Nat.cast_sub hcN];field_simp;ring
   have hprod:(R_s:ℝ)*((N-c:ℕ):ℝ)≤(c:ℝ)*((N-c:ℕ):ℝ) :=Zo hRc_le (by positivity)
   linarith only[hP2c_bd,h1my,hprod]
  have hPnc_bd:(P_nc.card:ℝ)≤(57/1000:ℝ)*(N:ℝ)^2+32*(N:ℝ):=by
   set m0:=Nat.ceil ((19/100:ℝ)*(N:ℝ))
   have hm0_le:∀ A∈P_nc,m0≤ A.card:=fun A hA=>Nat.ceil_le.mpr (hPnc A hA).2.2.2.2
   have hraw:=Wg N 2 5 m0 hN1 (by omega) P_nc
    (Qd hF Zs)
    (fun A hA=>⟨(hPnc A hA).1,(hPnc A hA).2.1,hm0_le A hA,(hPnc A hA).2.2.2.1⟩)
   have hm0_ge:(19/100:ℝ)≤(m0:ℝ)/(N:ℝ):=by rw[le_div_iff₀ hNpos];exact Nat.le_ceil _
   have hsum_le:∑ d∈Icc (2:ℕ) 5,fInt (1/(d:ℝ)) ((m0:ℝ)/(N:ℝ))≤57/1000 :=(Finset.sum_le_sum fun d _=>Wb (by norm_num) hm0_ge (by positivity)).trans Vp
   have hcast4:((5+1-2:ℕ):ℝ)=4:=by norm_num
   rw[hcast4] at hraw;have hmul:=Zo hsum_le (sq_nonneg (N:ℝ));linarith only[hraw,hmul]
  have hPcR:(P_c.card:ℝ)=(P1_c.card:ℝ)+(P2_c.card:ℝ):=by exact_mod_cast hPc_part
  have herr:12*(d₀:ℝ)*(N:ℝ)+4*(N:ℝ)*(log (N:ℝ)+2)+32*(N:ℝ) ≤500*(N:ℝ)*(log (N:ℝ)+2)^2:=by nlinarith only[hNpos,hd0_le5,hLsq,h1sq]
  have hmain:(core+(645/1000)*(1-y)*y+57/1000)*(N:ℝ)^2≤(N:ℝ)^2/2:=by
   calc (core+(645/1000)*(1-y)*y+57/1000)*(N:ℝ)^2≤(1/2)*(N:ℝ)^2 :=
         Zo hineq (sq_nonneg _)
     _=(N:ℝ)^2/2:=by ring
  linarith only[hPcR,hQP1,hP2c_y,hPnc_bd,herr,hmain]
private lemma Xb (N c m_nat:ℕ) (hN:1000≤ N) (hc:c∈Icc 1 N)
  (hm_lo:N/12+2≤ m_nat)
  (Q_c P_c P_nc:Zf (Zf ℕ)) (A_min:Zf ℕ)
  (hF:Zt N (Q_c∪P_c∪P_nc))
  (hdisjQP:Disjoint Q_c P_c) (_hdisjQN:Disjoint Q_c P_nc) (hdisjPN:Disjoint P_c P_nc)
  (hQc:∀ S∈Q_c,¬ IsAP S/\c∈S)
  (hPc:∀ A∈P_c,IsAP A/\2≤ A.card/\c∈A)
  (hPnc:∀ A∈P_nc,IsAP A/\2≤ A.card/\c∉A/\m_nat≤ A.card)
  (hAmin:A_min∈P_nc) (hAmin_card:A_min.card=m_nat)
  (hP1_ne:(P_nc.filter (fun A=>apStep A=1)).Nonempty)
  (hP1_L:∀ A∈P_nc.filter (fun A=>apStep A=1),A⊆Icc 1 (c-1)) :
  (Q_c.card:ℝ)+(P_c.card:ℝ)+(P_nc.card:ℝ) ≤(N:ℝ)^2/2+500*(N:ℝ)*(log (N:ℝ)+2)^2 +8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5):=by
 classical
 have hN1:1≤ N:=by omega
 have hNpos:(0:ℝ)<(N:ℝ):=by exact_mod_cast (by omega:0< N)
 have hcN:=(Zb.mp hc).2
 have hlog0:0≤ log (N:ℝ):=Real.log_nonneg (by exact_mod_cast hN1)
 have hlog2_ge:(2:ℝ)≤ log (N:ℝ)+2:=by linarith
 have hLsq:log (N:ℝ)+2≤(log (N:ℝ)+2)^2:=by nlinarith only[hlog2_ge]
 have h1sq:(1:ℝ)≤(log (N:ℝ)+2)^2:=by nlinarith only[hlog2_ge]
 have hsubPnc:∀ A∈P_nc,A⊆Icc 1 N:=fun A hA =>
  Zy.mp (hF.1 (Zg _ hA))
 have hsubPc:∀ A∈P_c,A⊆Icc 1 N:=fun A hA =>
  Zy.mp (hF.1 (Ze _ (Zg _ hA)))
 have hstep11:∀ A∈P_nc,1≤ apStep A/\apStep A≤11:=fun A hA =>
  ⟨(Qg (hsubPnc A hA) (hPnc A hA).1 (hPnc A hA).2.1).1,Xp (hsubPnc A hA) (hPnc A hA).1 (hPnc A hA).2.1 (hPnc A hA).2.2.2 (by omega)⟩
 set P1_nc:=P_nc.filter (fun A=>apStep A=1)
 set P2_nc:=P_nc.filter (fun A=>apStep A=2)
 set P3_nc:=P_nc.filter (fun A=>3≤ apStep A)
 set P1_c:=P_c.filter (fun A=>apStep A=1)
 set P2_c:=P_c.filter (fun A=>2≤ apStep A)
 have hPc_part:(P_c.card:ℝ)=(P1_c.card:ℝ)+(P2_c.card:ℝ):=by
  have hd:Disjoint P1_c P2_c:=by
   rw[Zk];intro A h1 h2
   have:=(Za.mp h1).2;have:=(Za.mp h2).2;omega
  have hu:P_c=P1_c∪P2_c:=by
   ext A;simp only[P1_c,P2_c,Zd,Za]
   constructor
   ·intro hA
    have h1:=(Qg (hsubPc A hA) (hPc A hA).1 (hPc A hA).2.1).1
    rcases Nat.eq_or_lt_of_le h1 with h|h
    ·exact Or.inl ⟨hA,h.symm⟩
    ·exact Or.inr ⟨hA,h⟩
   ·rintro (⟨hA,_⟩|⟨hA,_⟩) <;> exact hA
  rw[hu,Zq hd,Nat.cast_add]
 have hPnc_part:(P_nc.card:ℝ)=(P1_nc.card:ℝ)+(P2_nc.card:ℝ)+(P3_nc.card:ℝ):=by
  have hd12:Disjoint P1_nc P2_nc:=by
   rw[Zk];intro A h1 h2
   have:=(Za.mp h1).2;have:=(Za.mp h2).2;omega
  have hd123:Disjoint (P1_nc∪P2_nc) P3_nc:=by
   rw[Zk];intro A h1 h2;have h3:=(Za.mp h2).2
   rcases Zd.mp h1 with h|h <;> (have:=(Za.mp h).2;omega)
  have hu:P_nc=(P1_nc∪P2_nc)∪P3_nc:=by
   ext A;simp only[P1_nc,P2_nc,P3_nc,Zd,Za]
   constructor
   ·intro hA
    have h1:=(hstep11 A hA).1
    by_cases ha1:apStep A=1
    ·exact Or.inl (Or.inl ⟨hA,ha1⟩)
    ·by_cases ha2:apStep A=2
     ·exact Or.inl (Or.inr ⟨hA,ha2⟩)
     ·exact Or.inr ⟨hA,by omega⟩
   ·rintro ((⟨hA,_⟩|⟨hA,_⟩)|⟨hA,_⟩) <;> exact hA
  rw[hu,Zq hd123,Zq hd12,Nat.cast_add,Nat.cast_add]
 have hImg_ne:(P1_nc.image card).Nonempty:=hP1_ne.image _;set m₁:=(P1_nc.image card).min' hImg_ne;obtain⟨A₁,hA₁_mem,hA₁_card⟩:=Zi.mp (min'_mem _ hImg_ne);change A₁.card=m₁ at hA₁_card
 have hm₁_le:∀ A∈P1_nc,m₁≤ A.card:=fun A hA =>
  min'_le _ _ (Zi.mpr ⟨A,hA,rfl⟩)
 have hA₁_Pnc:A₁∈P_nc:=(Za.mp hA₁_mem).1;have hA₁_st:apStep A₁=1:=(Za.mp hA₁_mem).2;have hA₁_L:A₁⊆Icc 1 (c-1):=hP1_L A₁ hA₁_mem;obtain⟨-,-,L₁,k₁,hk₁2,hk₁_eq,hA₁_X⟩ :=Qg (hsubPnc A₁ hA₁_Pnc) (hPnc A₁ hA₁_Pnc).1 (hPnc A₁ hA₁_Pnc).2.1;rw[hA₁_st] at hA₁_X;set R₁:=L₁+(k₁-1)
 have hA₁_Icc:A₁=Icc L₁ R₁:=by
  ext x;rw[hA₁_X,Zb];simp only[mul_one]
  constructor
  ·rintro⟨i,hi,rfl⟩;exact⟨by omega,by dsimp only[R₁];omega⟩
  ·rintro⟨h1,h2⟩;exact⟨x-L₁,by dsimp only[R₁] at h2;omega,by omega⟩
 have hL₁_1:1≤ L₁:=(Zb.mp (hA₁_L (hA₁_Icc ▸ Zb.mpr ⟨le_rfl,by dsimp only[R₁];omega⟩))).1
 have hLR₁:L₁≤ R₁:=by dsimp only[R₁];omega
 have hR₁_c:R₁< c:=by
  have:=(Zb.mp (hA₁_L (hA₁_Icc ▸ Zb.mpr ⟨hLR₁,le_rfl⟩))).2
  have hc1:=(Zb.mp hc).1
  have:1≤ R₁:=by omega
  omega
 have hm₁_eq:R₁-L₁+1=m₁:=by dsimp only[R₁];omega
 set m:ℝ:=(m_nat:ℝ)/(N:ℝ);set m1:ℝ:=(m₁:ℝ)/(N:ℝ);set y:ℝ:=((N-c:ℕ):ℝ)/(N:ℝ)
 have h1my:1-y=(c:ℝ)/(N:ℝ):=by dsimp only[y];rw[Nat.cast_sub hcN];field_simp;ring
 have hm_ge:(1/12:ℝ)≤ m:=by
  dsimp only[m];rw[div_le_div_iff₀ (by norm_num) hNpos,one_mul]
  exact_mod_cast (by omega:N≤ m_nat*12)
 have hmm1:m≤ m1:=by
  dsimp only[m,m1]
  have hm_m1:m_nat≤ m₁:=by rw[←hA₁_card];exact (hPnc A₁ hA₁_Pnc).2.2.2
  exact div_le_div_of_nonneg_right (by exact_mod_cast hm_m1) hNpos.le
 have hy_nn:0≤ y:=by positivity
 have hsum_le:m1+y≤1:=by
  have h1:m₁+(N-c)≤ N:=by
   have:m₁≤ c-1:=by
    have:=Zm hA₁_L;rw[Nat.card_Icc,hA₁_card] at this;omega
   omega
  have h1R:(m₁:ℝ)+((N-c:ℕ):ℝ)≤(N:ℝ):=by exact_mod_cast h1
  dsimp only[m1,y];rw[←add_div,div_le_one hNpos];exact h1R
 set mod2:Bool:=decide (∃ B∈P_nc,apStep B=2/\∀ x∈B,x % 2≠c % 2)
 set S_pc:ℝ:=if mod2 then 1235/1000 else 1645/1000
 set L2:ℝ:=if mod2 then 1/2 else max (1-y) y/2
 have hPc_odd:mod2=true->∀ A∈P_c,Odd (apStep A):=by
  intro hmod A hA;obtain⟨B₂,hB₂,-,hB₂m⟩:=of_decide_eq_true hmod
  have hmeet:=Qe hF
   (Ze _ (Zg _ hA)) (Zg _ hB₂)
   (fun h=>(hPnc B₂ hB₂).2.2.1 (h ▸ (hPc A hA).2.2))
  exact Xx (hsubPc A hA) (hPc A hA).1 (hPc A hA).2.1 (hPc A hA).2.2 hmeet hB₂m
 have hP1nc_bd:(P1_nc.card:ℝ)≤ fInt (1-y) m1*(N:ℝ)^2+8*(N:ℝ):=by
  have h1:fInt ((1-y)/((1:ℕ):ℝ)) m1=fInt (1-y) m1:=by simp
  rw[←h1]
  refine Qy N 1 (c-1) 1 m₁ hN1 le_rfl (by linarith only[hy_nn])
   (fun _=>by
    rw[h1my,div_mul_cancel₀ _ hNpos.ne']
    exact_mod_cast (by omega:c-1-1≤ c))
   P1_nc hP1_L
   (fun A hA=>by
    obtain⟨hAP,hst⟩:=Za.mp hA;obtain⟨-,-,x₀,k,hk2,hcard,hX⟩:=Qg (hsubPnc A hAP) (hPnc A hAP).1 (hPnc A hAP).2.1;rw[hst] at hX
    exact⟨x₀,k,hk2,by rw[←hcard];exact hm₁_le A hA,hX⟩)
   (fun A hA B hB hAB=>Qe hF
    (Zg _ (Za.mp hA).1)
    (Zg _ (Za.mp hB).1) hAB)
 have hP2nc_bd:(P2_nc.card:ℝ)≤ fInt L2 m*(N:ℝ)^2+8*(N:ℝ):=by
  refine V3 N c m_nat hN1 hc mod2 P2_nc
   (Qd hF ((Zl _ _).trans Zs))
   (fun A hA=>by
    obtain⟨hAP,hst⟩:=Za.mp hA;exact⟨(hPnc A hAP).1,(hPnc A hAP).2.1,(hPnc A hAP).2.2.1,(hPnc A hAP).2.2.2,hst⟩)
   (fun hfalse A hA x hx=>by
    obtain⟨hAP,hst⟩:=Za.mp hA;by_contra hne
    have hall:∀ z∈A,z % 2≠c % 2:=fun z hz=>by
     have:=Xi (hsubPnc A hAP) (hPnc A hAP).1 (hPnc A hAP).2.1 z hz x hx
     rw[hst] at this;omega
    have htrue:mod2=true:=decide_eq_true ⟨A,hAP,hst,hall⟩;rw[hfalse] at htrue;exact Bool.false_ne_true htrue)
 have hP3nc_bd:(P3_nc.card:ℝ)≤ pnc3Sum m*(N:ℝ)^2+72*(N:ℝ):=by
  have hraw:=Wg N 3 11 m_nat hN1 (by omega) P3_nc
   (Qd hF ((Zl _ _).trans Zs))
   (fun A hA=>by
    obtain⟨hAP,h3⟩:=Za.mp hA;exact⟨(hPnc A hAP).1,(hPnc A hAP).2.1,(hPnc A hAP).2.2.2,Zb.mpr ⟨h3,(hstep11 A hAP).2⟩⟩)
  have h9:((11+1-3:ℕ):ℝ)=9:=by norm_num
  rw[h9] at hraw;dsimp only[pnc3Sum,m] at hraw ⊢;linarith only[hraw]
 have hPnc_bd:(P_nc.card:ℝ)≤(fInt (1-y) m1+fInt L2 m+pnc3Sum m)*(N:ℝ)^2+88*(N:ℝ):=by linarith only[hPnc_part,hP1nc_bd,hP2nc_bd,hP3nc_bd]
 have hQ_sub:Zt N Q_c :=Qd hF (Zr.trans Zr)
 have hAmin_erase:A_min⊆(Icc 1 N).erase c:=fun x hx =>
  Zw.mpr ⟨fun h=>(hPnc A_min hAmin).2.2.1 (h ▸ hx),hsubPnc A_min hAmin hx⟩
 have hQc_hit_min:∀ S∈Q_c,(S∩A_min).Nonempty:=fun S hS =>
  Qe hF (Ze _ (Ze _ hS)) (Zg _ hAmin)
   (fun h=>(hPnc A_min hAmin).2.2.1 (h ▸ (hQc S hS).2))
 have hQc_m_bd:(Q_c.card:ℝ)≤(m-m^2/2)*(N:ℝ)^2 +8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5):=by
  have h:=Q6 N c hN1 hc Q_c A_min hQ_sub (fun S hS=>(hQc S hS).1)
   (fun S hS=>(hQc S hS).2) hAmin_erase hQc_hit_min
  rw[hAmin_card] at h
  have heq:(m_nat:ℝ)*(N:ℝ)-(m_nat:ℝ)^2/2=(m-m^2/2)*(N:ℝ)^2:=by dsimp only[m];field_simp
  linarith only[h,heq]
 have hPc_hit_A1:∀ A∈P_c,(A∩Icc L₁ R₁).Nonempty:=fun A hA=>by
  rw[←hA₁_Icc]
  exact Qe hF (Ze _ (Zg _ hA))
   (Zg _ hA₁_Pnc) (fun h=>(hPnc A₁ hA₁_Pnc).2.2.1 (h ▸ (hPc A hA).2.2))
 have hPc_left:∀ A∈P_c,∃ z∈A,z≤ R₁:=fun A hA=>by
  obtain⟨z,hz⟩:=hPc_hit_A1 A hA;exact⟨z,(Zn.mp hz).1,(Zb.mp (Zn.mp hz).2).2⟩
 have hPc_left_all:=Xh N c R₁ hN1 hc hR₁_c P_c hsubPc hPc hPc_left
 have hR1_prod:(R₁:ℝ)*((N-c:ℕ):ℝ)≤ y*(1-y)*(N:ℝ)^2:=by
  have h1:(R₁:ℝ)≤(c:ℝ):=by exact_mod_cast (by omega:R₁≤ c)
  have h2:y*(1-y)*(N:ℝ)^2=(c:ℝ)*((N-c:ℕ):ℝ):=by dsimp only[y];rw[Nat.cast_sub hcN];field_simp;ring
  have h3:(R₁:ℝ)*((N-c:ℕ):ℝ)≤(c:ℝ)*((N-c:ℕ):ℝ) :=Zo h1 (by positivity)
  linarith only[h2,h3]
 have hP1c_y:(P1_c.card:ℝ)≤ y*(1-y)*(N:ℝ)^2+2*(N:ℝ):=by linarith only[hPc_left_all.1,hR1_prod]
 have hP2c_y:(P2_c.card:ℝ)≤(S_pc-1)*y*(1-y)*(N:ℝ)^2 +4*(N:ℝ)*(log (N:ℝ)+2):=by
  cases hmod:mod2
  ·have hS:S_pc-1=645/1000:=by dsimp only[S_pc];rw[hmod];norm_num
   rw[hS];linarith only[hPc_left_all.2.1,hR1_prod]
  ·have hS:S_pc-1=235/1000:=by dsimp only[S_pc];rw[hmod];norm_num
   rw[hS];linarith only[hPc_left_all.2.2 (hPc_odd hmod),hR1_prod]
 have hP2N_bd:(P2_c.card:ℝ)+(P2_nc.card:ℝ)+(P3_nc.card:ℝ) ≤(129/800:ℝ)*(N:ℝ)^2+12*(N:ℝ)*(log (N:ℝ)+2):=by
  set Pge2:=P2_c∪(P2_nc∪P3_nc)
  have hd23:Disjoint P2_nc P3_nc:=by
   rw[Zk];intro A h1 h2
   have:=(Za.mp h1).2;have:=(Za.mp h2).2;omega
  have hd_c_nc:Disjoint P2_c (P2_nc∪P3_nc) :=Finset.disjoint_of_subset_left (Zl _ _)
    (Finset.disjoint_of_subset_right (Zu (Zl _ _) (Zl _ _)) hdisjPN)
  have hsub2:Zt N Pge2 :=Qd hF (Zu
    (((Zl _ _).trans Zs).trans Zr)
    (Zu ((Zl _ _).trans Zs)
     ((Zl _ _).trans Zs)))
  have hbd:=Wz N hN1 Pge2 hsub2 (fun A hA=>by
   rcases Zd.mp hA with h1|h23
   ·obtain⟨hA',h2⟩:=Za.mp h1;exact⟨(hPc A hA').1,(hPc A hA').2.1,h2⟩
   ·rcases Zd.mp h23 with h2|h3
    ·obtain⟨hA',hst⟩:=Za.mp h2;exact⟨(hPnc A hA').1,(hPnc A hA').2.1,by omega⟩
    ·obtain⟨hA',hst⟩:=Za.mp h3;exact⟨(hPnc A hA').1,(hPnc A hA').2.1,by omega⟩)
  dsimp only[Pge2] at hbd;rw[Zq hd_c_nc,Zq hd23,Nat.cast_add,Nat.cast_add] at hbd;linarith only[hbd]
 have hQP1_amgm:(Q_c.card:ℝ)+(P1_c.card:ℝ) ≤((1+2*m-m^2)/4)*(N:ℝ)^2+2*(N:ℝ) +8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5):=by
  have hP1Q_sub:Zt N (P1_c∪Q_c) :=Qd hF (Zu
    (((Zl _ _).trans Zs).trans Zr)
    (Zr.trans Zr))
  have hP1Q_disj:Disjoint P1_c Q_c :=Finset.disjoint_of_subset_left (Zl _ _) hdisjQP.symm
  have ham:=Xn N c hN1 hc P1_c Q_c A_min hP1Q_sub hP1Q_disj
   (fun A hA=>by
    obtain⟨hA',h1⟩:=Za.mp hA;exact⟨(hPc A hA').1,(hPc A hA').2.1,(hPc A hA').2.2,h1⟩)
   hQc hAmin_erase
  have hnh:=Qw N c hN1 Q_c A_min hQ_sub (fun S hS=>(hQc S hS).1)
   (fun S hS=>(hQc S hS).2) hAmin_erase hQc_hit_min
  have hQs:(Q_c.card:ℝ)=((Qa c A_min Q_c).card:ℝ) +((Q_c \ Qa c A_min Q_c).card:ℝ):=by
   have:=Yb (Qx c A_min Q_c)
   exact_mod_cast (by omega:Q_c.card=(Qa c A_min Q_c).card+(Q_c \ Qa c A_min Q_c).card)
  rw[hAmin_card] at ham
  have heq:(m_nat:ℝ)*(N:ℝ)-(m_nat:ℝ)^2/2+((N:ℝ)-(m_nat:ℝ))^2/4 =((1+2*m-m^2)/4)*(N:ℝ)^2:=by dsimp only[m];field_simp;ring
  linarith only[ham,hnh,hQs,heq]
 have hok:=Ko mod2 hm_ge hmm1 hy_nn hsum_le
 rcases hok with ⟨hmodT,hb1⟩|hb2|hb3|hb4|hb5|hb6|hb7
 ·
  obtain⟨B₂,hB₂,-,hB₂m⟩:=of_decide_eq_true hmodT
  have hPQ_sub:Zt N (P_c∪Q_c) :=Qd hF (Zu
    (Zs.trans Zr)
    (Zr.trans Zr))
  have hB₂_erase:B₂⊆(Icc 1 N).erase c:=fun x hx =>
   Zw.mpr ⟨fun h=>(hPnc B₂ hB₂).2.2.1 (h ▸ hx),hsubPnc B₂ hB₂ hx⟩
  have hq2:=Wv N c 2 hN1 hc le_rfl P_c Q_c B₂ hPQ_sub hdisjQP.symm hPc hQc
   hB₂_erase hB₂m
   (fun A hA=>Qe hF (Ze _ (Zg _ hA))
    (Zg _ hB₂) (fun h=>(hPnc B₂ hB₂).2.2.1 (h ▸ (hPc A hA).2.2)))
   (fun S hS=>Qe hF (Ze _ (Ze _ hS))
    (Zg _ hB₂) (fun h=>(hPnc B₂ hB₂).2.2.1 (h ▸ (hQc S hS).2)))
  have h38:(1/2-1/(2*((2:ℕ):ℝ)^2):ℝ)=3/8:=by norm_num
  rw[h38] at hq2
  have hmain:(3/8+(fInt (1-y) m1+fInt L2 m+pnc3Sum m))*(N:ℝ)^2≤(N:ℝ)^2/2:=by
   calc (3/8+(fInt (1-y) m1+fInt L2 m+pnc3Sum m))*(N:ℝ)^2≤(1/2)*(N:ℝ)^2 :=
         Zo hb1 (sq_nonneg _)
     _=(N:ℝ)^2/2:=by ring
  have herr:210*(N:ℝ)*(log (N:ℝ)+2)^2+88*(N:ℝ) ≤500*(N:ℝ)*(log (N:ℝ)+2)^2:=by nlinarith only[hNpos,h1sq]
  linarith only[hq2,hPnc_bd,hmain,herr]
 ·
  have hPQ_sub:Zt N (P_c∪Q_c) :=Qd hF (Zu
    (Zs.trans Zr)
    (Zr.trans Zr))
  have hq:=Vl N c L₁ R₁ hN1 hc hL₁_1 hLR₁ hR₁_c mod2 P_c Q_c
   hPQ_sub hdisjQP.symm hPc hPc_hit_A1 hPc_odd hQc
  dsimp only at hq;rw[hm₁_eq] at hq;change ((Qa c (Icc L₁ R₁) Q_c).card:ℝ)+(P_c.card:ℝ) ≤((m1-m1^2/2) +max ((43/100*y)^2/(114/100)) (y-y^2-(57/100)*m1+(57/200)*m1^2)*S_pc) *(N:ℝ)^2 +250*(N:ℝ)*(log (N:ℝ)+2)^2 at hq
  have hA1_erase:Icc L₁ R₁⊆(Icc 1 N).erase c:=by
   rw[←hA₁_Icc]
   exact fun x hx=>Zw.mpr ⟨fun h=>(hPnc A₁ hA₁_Pnc).2.2.1 (h ▸ hx),hsubPnc A₁ hA₁_Pnc hx⟩
  have hQc_hit_A1:∀ S∈Q_c,(S∩Icc L₁ R₁).Nonempty:=fun S hS=>by
   rw[←hA₁_Icc]
   exact Qe hF (Ze _ (Ze _ hS))
    (Zg _ hA₁_Pnc) (fun h=>(hPnc A₁ hA₁_Pnc).2.2.1 (h ▸ (hQc S hS).2))
  have hnh:=Qw N c hN1 Q_c (Icc L₁ R₁) hQ_sub (fun S hS=>(hQc S hS).1)
   (fun S hS=>(hQc S hS).2) hA1_erase hQc_hit_A1
  have hQs:(Q_c.card:ℝ)=((Qa c (Icc L₁ R₁) Q_c).card:ℝ) +((Q_c \ Qa c (Icc L₁ R₁) Q_c).card:ℝ):=by
   have:=Yb (Qx c (Icc L₁ R₁) Q_c)
   exact_mod_cast (by omega:Q_c.card=(Qa c (Icc L₁ R₁) Q_c).card +(Q_c \ Qa c (Icc L₁ R₁) Q_c).card)
  have hmain:((m1-m1^2/2) +max ((43/100*y)^2/(114/100)) (y-y^2-(57/100)*m1+(57/200)*m1^2)*S_pc +(fInt (1-y) m1+fInt L2 m+pnc3Sum m))*(N:ℝ)^2≤(N:ℝ)^2/2:=by
   calc _≤(1/2)*(N:ℝ)^2:=Zo hb2 (sq_nonneg _)
     _=(N:ℝ)^2/2:=by ring
  have herr:250*(N:ℝ)*(log (N:ℝ)+2)^2+88*(N:ℝ) ≤500*(N:ℝ)*(log (N:ℝ)+2)^2:=by nlinarith only[hNpos,h1sq]
  linarith only[hq,hnh,hQs,hPnc_bd,hmain,herr]
 ·
  have hP1Q_sub:Zt N (P1_c∪Q_c) :=Qd hF (Zu
    (((Zl _ _).trans Zs).trans Zr)
    (Zr.trans Zr))
  have hP1Q_disj:Disjoint P1_c Q_c :=Finset.disjoint_of_subset_left (Zl _ _) hdisjQP.symm
  have hA1_seq1:∀ x,x∈A₁↔∃ i< m₁,x=L₁+i*1:=by rw[←hA₁_card,hk₁_eq];exact hA₁_X
  have hR1_eq:L₁+(m₁-1)*1< c:=by rw[mul_one,←hA₁_card,hk₁_eq];exact hR₁_c
  have hst1:=Xd N c L₁ 1 m₁ hN1 hc le_rfl (by omega) hL₁_1 hR1_eq A₁ hA1_seq1
   P1_c Q_c hP1Q_sub hP1Q_disj
   (fun A hA=>by
    obtain⟨hA',h1⟩:=Za.mp hA;exact⟨(hPc A hA').1,(hPc A hA').2.1,(hPc A hA').2.2,h1⟩)
   (fun A hA=>by rw[hA₁_Icc];exact hPc_hit_A1 A (Za.mp hA).1) hQc
  dsimp only at hst1;simp only[mul_one,Nat.cast_one,sub_self,zero_mul,zero_sub] at hst1
  have hg0:(0:ℝ)≤((c-(L₁+(m₁-1)):ℕ):ℝ)/(N:ℝ):=by positivity
  have hmax_le:max (m1-m1^2/2+max 0 (-(((c-(L₁+(m₁-1)):ℕ):ℝ)/(N:ℝ)))^2/(4-2))
    (y-y^2-((c-(L₁+(m₁-1)):ℕ):ℝ)/(N:ℝ)*y) ≤
    max (m1-m1^2/2) (y-y^2):=by
   have h0:max (0:ℝ) (-(((c-(L₁+(m₁-1)):ℕ):ℝ)/(N:ℝ)))=0 :=Yk (by linarith only[hg0])
   rw[h0,zero_pow two_ne_zero,zero_div,add_zero];exact max_le (Ym _ _) (le_trans (sub_le_self _ (mul_nonneg hg0 hy_nn)) (Yn _ _))
  have hA1_erase:A₁⊆(Icc 1 N).erase c:=fun x hx =>
   Zw.mpr ⟨fun h=>(hPnc A₁ hA₁_Pnc).2.2.1 (h ▸ hx),hsubPnc A₁ hA₁_Pnc hx⟩
  have hQc_hit_A1':∀ S∈Q_c,(S∩A₁).Nonempty:=fun S hS =>
   Qe hF (Ze _ (Ze _ hS))
    (Zg _ hA₁_Pnc) (fun h=>(hPnc A₁ hA₁_Pnc).2.2.1 (h ▸ (hQc S hS).2))
  have hnh:=Qw N c hN1 Q_c A₁ hQ_sub (fun S hS=>(hQc S hS).1)
   (fun S hS=>(hQc S hS).2) hA1_erase hQc_hit_A1'
  have hQs:(Q_c.card:ℝ)=((Qa c A₁ Q_c).card:ℝ) +((Q_c \ Qa c A₁ Q_c).card:ℝ):=by
   have:=Yb (Qx c A₁ Q_c)
   exact_mod_cast (by omega:Q_c.card=(Qa c A₁ Q_c).card+(Q_c \ Qa c A₁ Q_c).card)
  have hst1':(Q_c.card:ℝ)+(P1_c.card:ℝ) ≤ max (m1-m1^2/2) (y-y^2)*(N:ℝ)^2+12*(N:ℝ) +8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5):=by
   have hmul:max (m1-m1^2/2+max 0 (-(((c-(L₁+(m₁-1)):ℕ):ℝ)/(N:ℝ)))^2/(4-2))
     (y-y^2-((c-(L₁+(m₁-1)):ℕ):ℝ)/(N:ℝ)*y)*(N:ℝ)^2 ≤
     max (m1-m1^2/2) (y-y^2)*(N:ℝ)^2 :=
    Zo hmax_le (sq_nonneg _)
   change ((Qa c A₁ Q_c).card:ℝ)+(P1_c.card:ℝ) ≤ max (m1-m1^2/2+max 0 (-(((c-(L₁+(m₁-1)):ℕ):ℝ)/(N:ℝ)))^2/(4-2))
     (y-y^2-((c-(L₁+(m₁-1)):ℕ):ℝ)/(N:ℝ)*y)*(N:ℝ)^2+12*(N:ℝ) at hst1
   linarith only[hst1,hmul,hnh,hQs]
  have hmain:(max (m1-m1^2/2) (y-y^2)+fInt (1-y) m1+129/800)*(N:ℝ)^2 ≤(N:ℝ)^2/2:=by
   calc _≤(1/2)*(N:ℝ)^2:=Zo hb3 (sq_nonneg _)
     _=(N:ℝ)^2/2:=by ring
  have herr:12*(N:ℝ)+8*(N:ℝ)+12*(N:ℝ)*(log (N:ℝ)+2) ≤500*(N:ℝ)*(log (N:ℝ)+2)^2:=by nlinarith only[hNpos,hLsq,h1sq]
  linarith only[hPc_part,hPnc_part,hst1',hP1nc_bd,hP2N_bd,hmain,herr]
 ·
  have hPc_y:(P_c.card:ℝ)≤ S_pc*y*(1-y)*(N:ℝ)^2 +2*(N:ℝ)+4*(N:ℝ)*(log (N:ℝ)+2):=by
   have heq:y*(1-y)*(N:ℝ)^2+(S_pc-1)*y*(1-y)*(N:ℝ)^2 =S_pc*y*(1-y)*(N:ℝ)^2:=by ring
   linarith only[hPc_part,hP1c_y,hP2c_y,heq]
  have hmain:((m-m^2/2)+S_pc*y*(1-y) +(fInt (1-y) m1+fInt L2 m+pnc3Sum m))*(N:ℝ)^2≤(N:ℝ)^2/2:=by
   calc _≤(1/2)*(N:ℝ)^2:=Zo hb4 (sq_nonneg _)
     _=(N:ℝ)^2/2:=by ring
  have herr:2*(N:ℝ)+4*(N:ℝ)*(log (N:ℝ)+2)+88*(N:ℝ) ≤500*(N:ℝ)*(log (N:ℝ)+2)^2:=by nlinarith only[hNpos,hLsq,h1sq]
  linarith only[hQc_m_bd,hPc_y,hPnc_bd,hmain,herr]
 ·
  have hmain:((1+2*m-m^2)/4+(S_pc-1)*y*(1-y) +(fInt (1-y) m1+fInt L2 m+pnc3Sum m))*(N:ℝ)^2≤(N:ℝ)^2/2:=by
   calc _≤(1/2)*(N:ℝ)^2:=Zo hb5 (sq_nonneg _)
     _=(N:ℝ)^2/2:=by ring
  have herr:2*(N:ℝ)+4*(N:ℝ)*(log (N:ℝ)+2)+88*(N:ℝ) ≤500*(N:ℝ)*(log (N:ℝ)+2)^2:=by nlinarith only[hNpos,hLsq,h1sq]
  linarith only[hPc_part,hQP1_amgm,hP2c_y,hPnc_bd,hmain,herr]
 ·
  have hQP1_split:(Q_c.card:ℝ)+(P1_c.card:ℝ) ≤((m-m^2/2)+y*(1-y))*(N:ℝ)^2+2*(N:ℝ) +8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5):=by
   have heq:(m-m^2/2)*(N:ℝ)^2+y*(1-y)*(N:ℝ)^2 =((m-m^2/2)+y*(1-y))*(N:ℝ)^2:=by ring
   linarith only[hQc_m_bd,hP1c_y,heq]
  have hQP1_min:(Q_c.card:ℝ)+(P1_c.card:ℝ) ≤ min ((1+2*m-m^2)/4) ((m-m^2/2)+y*(1-y))*(N:ℝ)^2 +2*(N:ℝ)+8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5):=by
   rcases le_total ((1+2*m-m^2)/4) ((m-m^2/2)+y*(1-y)) with hle|hge
   ·rw[Yl hle];exact hQP1_amgm
   ·rw[Yj hge];exact hQP1_split
  have hmain:(min ((1+2*m-m^2)/4) ((m-m^2/2)+y*(1-y)) +fInt (1-y) m1+129/800)*(N:ℝ)^2≤(N:ℝ)^2/2:=by
   calc _≤(1/2)*(N:ℝ)^2:=Zo hb6 (sq_nonneg _)
     _=(N:ℝ)^2/2:=by ring
  have herr:2*(N:ℝ)+8*(N:ℝ)+12*(N:ℝ)*(log (N:ℝ)+2) ≤500*(N:ℝ)*(log (N:ℝ)+2)^2:=by nlinarith only[hNpos,hLsq,h1sq]
  linarith only[hPc_part,hPnc_part,hQP1_min,hP1nc_bd,hP2N_bd,hmain,herr]
 ·
  have hP1_union_sub:Zt N (P1_c∪P1_nc) :=Qd hF (Zu
    (((Zl _ _).trans Zs).trans Zr)
    ((Zl _ _).trans Zs))
  have hhelly:=V7 N c m₁ hN1 hc (by omega) P1_c P1_nc hP1_union_sub
   (fun A hA=>by
    obtain⟨hA',h1⟩:=Za.mp hA;exact⟨(hPc A hA').1,(hPc A hA').2.1,(hPc A hA').2.2,h1⟩)
   (fun A hA=>by
    obtain⟨hA',h1⟩:=Za.mp hA;exact⟨(hPnc A hA').1,(hPnc A hA').2.1,hP1_L A hA,hm₁_le A hA,h1⟩)
   hP1_ne
  dsimp only at hhelly;have hbeta:(c:ℝ)/(N:ℝ)=1-y:=h1my.symm
  have h1mb:1-(c:ℝ)/(N:ℝ)=y:=by rw[hbeta];ring
  rw[h1mb,hbeta] at hhelly
  have hmain:((m-m^2/2) +max (max (if 2*m1≤1-y then 1/4-m1^2/2 else 0)
         (if 1/2≤ m1 then (1-m1)^2/2 else 1/6))
      (max (y*(1-y)+(max 0 (1-2*y-m1))^2/2)
         (m1*y+(max 0 (1-y-m1))^2/2))+129/800)*(N:ℝ)^2 ≤
    (N:ℝ)^2/2:=by
   calc _≤(1/2)*(N:ℝ)^2:=Zo hb7 (sq_nonneg _)
     _=(N:ℝ)^2/2:=by ring
  have herr:10*(N:ℝ)+12*(N:ℝ)*(log (N:ℝ)+2) ≤500*(N:ℝ)*(log (N:ℝ)+2)^2:=by nlinarith only[hNpos,hLsq,h1sq]
  linarith only[hPc_part,hPnc_part,hQc_m_bd,hhelly,hP2N_bd,hmain,herr]
lemma Vb (N c:ℕ) (hN:1000≤ N) (hc:c∈Icc 1 N)
  (Q_c P_c P_nc:Zf (Zf ℕ))
  (hF:Zt N (Q_c∪P_c∪P_nc))
  (hdisjQP:Disjoint Q_c P_c) (hdisjQN:Disjoint Q_c P_nc) (hdisjPN:Disjoint P_c P_nc)
  (hQc:∀ S∈Q_c,¬ IsAP S/\c∈S)
  (hPc:∀ A∈P_c,IsAP A/\2≤ A.card/\c∈A)
  (hPnc:∀ A∈P_nc,IsAP A/\2≤ A.card/\c∉A) :
  (Q_c.card:ℝ)+(P_c.card:ℝ)+(P_nc.card:ℝ) ≤(N:ℝ)^2/2+500*(N:ℝ)*(log (N:ℝ)+2)^2 +8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5):=by
 classical
 have hN1:1≤ N:=by omega
 have hNpos:(0:ℝ)<(N:ℝ):=by exact_mod_cast (by omega:0< N)
 have hlog0:0≤ log (N:ℝ):=Real.log_nonneg (by exact_mod_cast hN1)
 have hlog2_ge:(2:ℝ)≤ log (N:ℝ)+2:=by linarith
 have hLsq:log (N:ℝ)+2≤(log (N:ℝ)+2)^2:=by nlinarith only[hlog2_ge]
 have h1sq:(1:ℝ)≤(log (N:ℝ)+2)^2:=by nlinarith only[hlog2_ge]
 have hsubQ:∀ S∈Q_c,S⊆Icc 1 N:=fun S hS =>
  Zy.mp (hF.1 (Ze _ (Ze _ hS)))
 have hsubP:∀ A∈P_c,A⊆Icc 1 N:=fun A hA =>
  Zy.mp (hF.1 (Ze _ (Zg _ hA)))
 have hsubN:∀ A∈P_nc,A⊆Icc 1 N:=fun A hA =>
  Zy.mp (hF.1 (Zg _ hA))
 rcases P_nc.eq_empty_or_nonempty with rfl|hPnc_ne
 ·simp only[card_empty,Nat.cast_zero,add_zero]
  have hPQ:Zt N (P_c∪Q_c):=by
   have:P_c∪Q_c=Q_c∪P_c∪∅:=by ext x;simp[or_comm]
   rw[this];exact hF
  have hmx:=Vj N c hN1 hc P_c Q_c hPQ hdisjQP.symm hPc hQc
  have herr:200*(N:ℝ)*(log (N:ℝ)+2)^2 ≤500*(N:ℝ)*(log (N:ℝ)+2)^2+8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5):=by
   have:(0:ℝ)≤8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5):=by positivity
   nlinarith
  linarith only[hmx,herr]
 have hImg_ne:(P_nc.image card).Nonempty:=hPnc_ne.image _;set m_nat:=(P_nc.image card).min' hImg_ne;obtain⟨A_min,hAmin,hAmin_card⟩:=Zi.mp (min'_mem _ hImg_ne)
 have hm_le:∀ A∈P_nc,m_nat≤ A.card:=fun A hA =>
  min'_le _ _ (Zi.mpr ⟨A,hA,rfl⟩)
 by_cases hm_small:m_nat≤ N/12+1
 ·have hQ_sub:Zt N Q_c :=Qd hF (Zr.trans Zr)
  have hAmin_erase:A_min⊆(Icc 1 N).erase c:=fun x hx =>
   Zw.mpr ⟨fun h=>(hPnc A_min hAmin).2.2 (h ▸ hx),hsubN A_min hAmin hx⟩
  have hQc_hit:∀ S∈Q_c,(S∩A_min).Nonempty:=fun S hS =>
   Qe hF (Ze _ (Ze _ hS))
    (Zg _ hAmin) (fun h=>(hPnc A_min hAmin).2.2 (h ▸ (hQc S hS).2))
  have hQbd:=Q6 N c hN1 hc Q_c A_min hQ_sub (fun S hS=>(hQc S hS).1)
   (fun S hS=>(hQc S hS).2) hAmin_erase hQc_hit
  rw[hAmin_card] at hQbd
  have hPN_sub:Zt N (P_c∪P_nc) :=Qd hF (Zu
    (Zs.trans Zr) Zs)
  have hPbd:=X9 N hN1 (P_c∪P_nc) hPN_sub (fun A hA=>by
   rcases Zd.mp hA with h|h
   ·exact⟨(hPc A h).1,(hPc A h).2.1⟩
   ·exact⟨(hPnc A h).1,(hPnc A h).2.1⟩)
  rw[Zq hdisjPN,Nat.cast_add] at hPbd
  have hm_ub:(m_nat:ℝ)≤(85/1000:ℝ)*(N:ℝ):=by
   have h1:1000*m_nat≤85*N:=by omega
   have h1R:1000*(m_nat:ℝ)≤85*(N:ℝ):=by exact_mod_cast h1
   linarith
  have hQmain:(m_nat:ℝ)*(N:ℝ)-(m_nat:ℝ)^2/2≤(85/1000:ℝ)*(N:ℝ)^2:=by nlinarith[sq_nonneg (m_nat:ℝ)]
  have herr:12*(N:ℝ)*(log (N:ℝ)+2)≤500*(N:ℝ)*(log (N:ℝ)+2)^2:=by nlinarith only[hNpos,hLsq]
  have hmain:(85/1000:ℝ)*(N:ℝ)^2+(4125/10000:ℝ)*(N:ℝ)^2≤(N:ℝ)^2/2:=by nlinarith
  linarith only[hQbd,hPbd,hQmain,herr,hmain]
 have hm_ge_nat:N/12+2≤ m_nat:=by omega
 set P1_nc:=P_nc.filter (fun A=>apStep A=1)
 set c':=N+1-c
 have hc':c'∈Icc 1 N:=by
  have:=Zb.mp hc;exact Zb.mpr ⟨by omega,by omega⟩
 have hR_eq:Ql N (Q_c∪P_c∪P_nc) =Ql N Q_c∪Ql N P_c∪Ql N P_nc:=by simp only[Ql,image_union]
 rcases P1_nc.eq_empty_or_nonempty with hP1_empty|hP1_ne
 swap
 ·have hP1_one:∀ A∈P1_nc,A⊆Icc 1 (c-1)\/A⊆Icc (c+1) N:=fun A hA=>by
   obtain⟨hAP,hst⟩:=Za.mp hA
   exact Wj (hsubN A hAP) (hPnc A hAP).1 (hPnc A hAP).2.1 (hPnc A hAP).2.2
    (by rw[hst];intro x _;simp only[Nat.mod_one])
  have hP1_nonempty_elem:∀ A∈P1_nc,A.Nonempty:=fun A hA =>
   card_pos.mp (by have:=(hPnc A (Za.mp hA).1).2.1;omega)
  rcases Wu
    (Qd hF ((Zl _ _).trans Zs))
    hP1_nonempty_elem hP1_one with hL|hR
  ·exact Xb N c m_nat hN hc hm_ge_nat Q_c P_c P_nc A_min
    hF hdisjQP hdisjQN hdisjPN hQc hPc
    (fun A hA=>⟨(hPnc A hA).1,(hPnc A hA).2.1,(hPnc A hA).2.2,hm_le A hA⟩)
    hAmin hAmin_card hP1_ne hL
  ·
   have hF':Zt N (Ql N Q_c∪Ql N P_c∪Ql N P_nc):=by rw[←hR_eq];exact W1 hF
   have hbd':=Xb N c' m_nat hN hc' hm_ge_nat
    (Ql N Q_c) (Ql N P_c) (Ql N P_nc) (Qm N A_min)
    hF' (Q3 hsubQ hsubP hdisjQP)
    (Q3 hsubQ hsubN hdisjQN) (Q3 hsubP hsubN hdisjPN)
    (fun S' hS'=>by
     obtain⟨S,hS,rfl⟩:=Zi.mp hS';exact⟨mt (Q8 (hsubQ S hS)).mp (hQc S hS).1,(Q5 (hsubQ S hS) hc).mpr (hQc S hS).2⟩)
    (fun A' hA'=>by
     obtain⟨A,hA,rfl⟩:=Zi.mp hA'
     exact⟨(Q8 (hsubP A hA)).mpr (hPc A hA).1,
      by rw[Q9 (hsubP A hA)];exact (hPc A hA).2.1,
      (Q5 (hsubP A hA) hc).mpr (hPc A hA).2.2⟩)
    (fun A' hA'=>by
     obtain⟨A,hA,rfl⟩:=Zi.mp hA'
     exact⟨(Q8 (hsubN A hA)).mpr (hPnc A hA).1,
      by rw[Q9 (hsubN A hA)];exact (hPnc A hA).2.1,
      mt (Q5 (hsubN A hA) hc).mp (hPnc A hA).2.2,
      by rw[Q9 (hsubN A hA)];exact hm_le A hA⟩)
    (Zi.mpr ⟨A_min,hAmin,rfl⟩)
    (by rw[Q9 (hsubN A_min hAmin)];exact hAmin_card)
    (by
     obtain⟨A,hA⟩:=hP1_ne;obtain⟨hAP,hst⟩:=Za.mp hA
     refine⟨Qm N A,Za.mpr ⟨Zi.mpr ⟨A,hAP,rfl⟩,?_⟩⟩
     rw[Xe (hsubN A hAP) (hPnc A hAP).1 (hPnc A hAP).2.1,hst])
    (fun A' hA'=>by
     obtain⟨hA'm,hst'⟩:=Za.mp hA';obtain⟨A,hA,rfl⟩:=Zi.mp hA'm;rw[Xe (hsubN A hA) (hPnc A hA).1 (hPnc A hA).2.1] at hst';exact Xg hc (hR A (Za.mpr ⟨hA,hst'⟩)))
   rw[Wi hsubQ,Wi hsubP,Wi hsubN] at hbd';exact hbd'
 have hPnc_ge2:∀ A∈P_nc,2≤ apStep A:=fun A hA=>by
  have h1:=(Qg (hsubN A hA) (hPnc A hA).1 (hPnc A hA).2.1).1
  have hne1:apStep A≠1:=fun h=>by
   have:A∈P1_nc:=Za.mpr ⟨hA,h⟩
   rw[hP1_empty] at this;exact Finset.notMem_empty A this
  omega
 set m:ℝ:=(m_nat:ℝ)/(N:ℝ)
 by_cases hm19:m≤19/100
 ·
  set P1_c:=P_c.filter (fun A=>apStep A=1)
  set P2_c:=P_c.filter (fun A=>2≤ apStep A)
  have hPc_part:(P_c.card:ℝ)=(P1_c.card:ℝ)+(P2_c.card:ℝ):=by
   have hd:Disjoint P1_c P2_c:=by
    rw[Zk];intro A h1 h2
    have:=(Za.mp h1).2;have:=(Za.mp h2).2;omega
   have hu:P_c=P1_c∪P2_c:=by
    ext A;simp only[P1_c,P2_c,Zd,Za]
    constructor
    ·intro hA
     have h1:=(Qg (hsubP A hA) (hPc A hA).1 (hPc A hA).2.1).1
     rcases Nat.eq_or_lt_of_le h1 with h|h
     ·exact Or.inl ⟨hA,h.symm⟩
     ·exact Or.inr ⟨hA,h⟩
    ·rintro (⟨hA,_⟩|⟨hA,_⟩) <;> exact hA
   rw[hu,Zq hd,Nat.cast_add]
  have hP1Q_sub:Zt N (P1_c∪Q_c) :=Qd hF (Zu
    (((Zl _ _).trans Zs).trans Zr)
    (Zr.trans Zr))
  have hP1Q_disj:Disjoint P1_c Q_c :=Finset.disjoint_of_subset_left (Zl _ _) hdisjQP.symm
  have hAmin_erase:A_min⊆(Icc 1 N).erase c:=fun x hx =>
   Zw.mpr ⟨fun h=>(hPnc A_min hAmin).2.2 (h ▸ hx),hsubN A_min hAmin hx⟩
  have hQc_hit:∀ S∈Q_c,(S∩A_min).Nonempty:=fun S hS =>
   Qe hF (Ze _ (Ze _ hS))
    (Zg _ hAmin) (fun h=>(hPnc A_min hAmin).2.2 (h ▸ (hQc S hS).2))
  have ham:=Xn N c hN1 hc P1_c Q_c A_min hP1Q_sub hP1Q_disj
   (fun A hA=>by
    obtain⟨hA',h1⟩:=Za.mp hA;exact⟨(hPc A hA').1,(hPc A hA').2.1,(hPc A hA').2.2,h1⟩)
   hQc hAmin_erase
  have hQ_sub:Zt N Q_c :=Qd hF (Zr.trans Zr)
  have hnh:=Qw N c hN1 Q_c A_min hQ_sub (fun S hS=>(hQc S hS).1)
   (fun S hS=>(hQc S hS).2) hAmin_erase hQc_hit
  have hQs:(Q_c.card:ℝ)=((Qa c A_min Q_c).card:ℝ) +((Q_c \ Qa c A_min Q_c).card:ℝ):=by
   have:=Yb (Qx c A_min Q_c)
   exact_mod_cast (by omega:Q_c.card=(Qa c A_min Q_c).card+(Q_c \ Qa c A_min Q_c).card)
  rw[hAmin_card] at ham;have hP2N_disj:Disjoint P2_c P_nc :=Finset.disjoint_of_subset_left (Zl _ _) hdisjPN
  have hP2N_sub:Zt N (P2_c∪P_nc) :=Qd hF (Zu
    (((Zl _ _).trans Zs).trans Zr)
    Zs)
  have hP2N:=Wz N hN1 (P2_c∪P_nc) hP2N_sub (fun A hA=>by
   rcases Zd.mp hA with h1|h2
   ·obtain⟨hA',hst⟩:=Za.mp h1;exact⟨(hPc A hA').1,(hPc A hA').2.1,hst⟩
   ·exact⟨(hPnc A h2).1,(hPnc A h2).2.1,hPnc_ge2 A h2⟩)
  rw[Zq hP2N_disj,Nat.cast_add] at hP2N
  have heq:(m_nat:ℝ)*(N:ℝ)-(m_nat:ℝ)^2/2+((N:ℝ)-(m_nat:ℝ))^2/4 =((m-m^2/2)+(1-m)^2/4)*(N:ℝ)^2:=by dsimp only[m];field_simp
  have hineq:=Vx (by positivity) hm19
  have hmain:((m-m^2/2)+(1-m)^2/4+129/800)*(N:ℝ)^2≤(N:ℝ)^2/2:=by
   calc _≤(1/2)*(N:ℝ)^2:=Zo hineq (sq_nonneg _)
     _=(N:ℝ)^2/2:=by ring
  have herr:2*(N:ℝ)+12*(N:ℝ)*(log (N:ℝ)+2) ≤500*(N:ℝ)*(log (N:ℝ)+2)^2:=by nlinarith only[hNpos,hLsq,h1sq]
  linarith only[hPc_part,ham,hnh,hQs,hP2N,heq,hmain,herr]
 push Not at hm19
 have h19_nat:19*N<100*m_nat:=by
  have:(19:ℝ)*(N:ℝ)<100*(m_nat:ℝ):=by
   have:=(lt_div_iff₀ hNpos).mp (show (19/100:ℝ)<(m_nat:ℝ)/(N:ℝ) from hm19)
   linarith
  exact_mod_cast this
 have hPnc_Icc5:∀ A∈P_nc,apStep A∈Icc 2 5:=fun A hA =>
  Zb.mpr ⟨hPnc_ge2 A hA,Xp (hsubN A hA) (hPnc A hA).1 (hPnc A hA).2.1 (hm_le A hA) (by omega)⟩
 have hPnc_19:∀ A∈P_nc,(19/100:ℝ)*(N:ℝ)≤(A.card:ℝ):=fun A hA=>by
  have h1:(m_nat:ℝ)≤(A.card:ℝ):=by exact_mod_cast hm_le A hA
  have h2:(19/100:ℝ)*(N:ℝ)<(m_nat:ℝ):=(lt_div_iff₀ hNpos).mp hm19;linarith
 have hPnc_full_prop:∀ A∈P_nc,IsAP A/\2≤ A.card/\c∉A ∧
   apStep A∈Icc 2 5/\(19/100:ℝ)*(N:ℝ)≤(A.card:ℝ):=fun A hA =>
  ⟨(hPnc A hA).1,(hPnc A hA).2.1,(hPnc A hA).2.2,hPnc_Icc5 A hA,hPnc_19 A hA⟩
 have hCaseA_side:∀ B∈P_nc,B⊆Icc 1 (c-1)\/B⊆Icc (c+1) N →
   (Q_c.card:ℝ)+(P_c.card:ℝ)+(P_nc.card:ℝ) ≤(N:ℝ)^2/2+500*(N:ℝ)*(log (N:ℝ)+2)^2 +8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5):=by
  intro B hB hside
  rcases hside with hBL|hBR
  ·exact Xc N c hN hc Q_c P_c P_nc B hF hdisjQP hdisjQN hdisjPN
    hQc hPc hPnc_full_prop hB hBL
  ·have hF':Zt N (Ql N Q_c∪Ql N P_c∪Ql N P_nc):=by
    rw[←hR_eq];exact W1 hF
   have hbd':=Xc N c' hN hc'
    (Ql N Q_c) (Ql N P_c) (Ql N P_nc) (Qm N B)
    hF' (Q3 hsubQ hsubP hdisjQP)
    (Q3 hsubQ hsubN hdisjQN) (Q3 hsubP hsubN hdisjPN)
    (fun S' hS'=>by
     obtain⟨S,hS,rfl⟩:=Zi.mp hS';exact⟨mt (Q8 (hsubQ S hS)).mp (hQc S hS).1,(Q5 (hsubQ S hS) hc).mpr (hQc S hS).2⟩)
    (fun A' hA'=>by
     obtain⟨A,hA,rfl⟩:=Zi.mp hA'
     exact⟨(Q8 (hsubP A hA)).mpr (hPc A hA).1,
      by rw[Q9 (hsubP A hA)];exact (hPc A hA).2.1,
      (Q5 (hsubP A hA) hc).mpr (hPc A hA).2.2⟩)
    (fun A' hA'=>by
     obtain⟨A,hA,rfl⟩:=Zi.mp hA'
     exact⟨(Q8 (hsubN A hA)).mpr (hPnc A hA).1,
      by rw[Q9 (hsubN A hA)];exact (hPnc A hA).2.1,
      mt (Q5 (hsubN A hA) hc).mp (hPnc A hA).2.2,
      by rw[Xe (hsubN A hA) (hPnc A hA).1 (hPnc A hA).2.1];exact hPnc_Icc5 A hA,
      by rw[Q9 (hsubN A hA)];exact hPnc_19 A hA⟩)
    (Zi.mpr ⟨B,hB,rfl⟩) (Xg hc hBR)
   rw[Wi hsubQ,Wi hsubP,Wi hsubN] at hbd';exact hbd'
 by_cases hmod2:∃ B∈P_nc,apStep B=2/\∀ x∈B,x % 2≠c % 2
 ·obtain⟨B,hB,-,hBm⟩:=hmod2
  have hPQ_sub:Zt N (P_c∪Q_c) :=Qd hF (Zu
    (Zs.trans Zr)
    (Zr.trans Zr))
  have hB_erase:B⊆(Icc 1 N).erase c:=fun x hx =>
   Zw.mpr ⟨fun h=>(hPnc B hB).2.2 (h ▸ hx),hsubN B hB hx⟩
  have hq2:=Wv N c 2 hN1 hc le_rfl P_c Q_c B hPQ_sub hdisjQP.symm hPc hQc
   hB_erase hBm
   (fun A hA=>Qe hF (Ze _ (Zg _ hA))
    (Zg _ hB) (fun h=>(hPnc B hB).2.2 (h ▸ (hPc A hA).2.2)))
   (fun S hS=>Qe hF (Ze _ (Ze _ hS))
    (Zg _ hB) (fun h=>(hPnc B hB).2.2 (h ▸ (hQc S hS).2)))
  have hPnc_bd:(P_nc.card:ℝ)≤(57/1000:ℝ)*(N:ℝ)^2+32*(N:ℝ):=by
   have hraw:=Wg N 2 5 m_nat hN1 (by omega) P_nc
    (Qd hF Zs)
    (fun A hA=>⟨(hPnc A hA).1,(hPnc A hA).2.1,hm_le A hA,hPnc_Icc5 A hA⟩)
   have hsum_le:∑ d∈Icc (2:ℕ) 5,fInt (1/(d:ℝ)) m≤57/1000 :=(Finset.sum_le_sum fun d _=>Wb (by norm_num) hm19.le (by positivity)).trans Vp
   have h4:((5+1-2:ℕ):ℝ)=4:=by norm_num
   rw[h4] at hraw;dsimp only[m] at hsum_le;have hmul:=Zo hsum_le (sq_nonneg (N:ℝ));linarith only[hraw,hmul]
  have hmain:(1/2-1/(2*((2:ℕ):ℝ)^2)+57/1000)*(N:ℝ)^2≤(N:ℝ)^2/2:=by norm_num;nlinarith only[sq_nonneg (N:ℝ)]
  have herr:210*(N:ℝ)*(log (N:ℝ)+2)^2+32*(N:ℝ) ≤500*(N:ℝ)*(log (N:ℝ)+2)^2:=by nlinarith only[hNpos,h1sq]
  linarith only[hq2,hPnc_bd,hmain,herr]
 by_cases hst2:∃ B∈P_nc,apStep B=2
 ·obtain⟨B,hB,hB2⟩:=hst2
  have hBm:∀ x∈B,x % apStep B=c % apStep B:=by
   rw[hB2];intro x hx;by_contra hne
   have hall:∀ z∈B,z % 2≠c % 2:=fun z hz=>by
    have:=Xi (hsubN B hB) (hPnc B hB).1 (hPnc B hB).2.1 z hz x hx
    rw[hB2] at this;omega
   exact hmod2 ⟨B,hB,hB2,hall⟩
  exact hCaseA_side B hB (Wj (hsubN B hB) (hPnc B hB).1 (hPnc B hB).2.1 (hPnc B hB).2.2 hBm)
 have hPnc_Icc35:∀ A∈P_nc,apStep A∈Icc 3 5:=fun A hA=>by
  have h:=Zb.mp (hPnc_Icc5 A hA)
  have hne2:apStep A≠2:=fun h2=>hst2 ⟨A,hA,h2⟩
  exact Zb.mpr ⟨by omega,h.2⟩
 obtain⟨B,hB⟩:=hPnc_ne;set d₀:=apStep B;have hd₀35:=Zb.mp (hPnc_Icc35 B hB)
 by_cases hBm:∀ x∈B,x % d₀=c % d₀
 ·exact hCaseA_side B hB (Wj (hsubN B hB) (hPnc B hB).1 (hPnc B hB).2.1 (hPnc B hB).2.2 hBm)
 ·push Not at hBm
  obtain⟨x₀,hx₀,hx₀ne⟩:=hBm
  have hBne:∀ x∈B,x % d₀≠c % d₀:=fun x hx=>by
   have:=Xi (hsubN B hB) (hPnc B hB).1 (hPnc B hB).2.1 x hx x₀ hx₀
   exact fun h=>hx₀ne (this.symm.trans h)
  have hPQ_sub:Zt N (P_c∪Q_c) :=Qd hF (Zu
    (Zs.trans Zr)
    (Zr.trans Zr))
  have hB_erase:B⊆(Icc 1 N).erase c:=fun x hx =>
   Zw.mpr ⟨fun h=>(hPnc B hB).2.2 (h ▸ hx),hsubN B hB hx⟩
  have hqd:=Wv N c d₀ hN1 hc (by omega) P_c Q_c B hPQ_sub hdisjQP.symm hPc hQc
   hB_erase hBne
   (fun A hA=>Qe hF (Ze _ (Zg _ hA))
    (Zg _ hB) (fun h=>(hPnc B hB).2.2 (h ▸ (hPc A hA).2.2)))
   (fun S hS=>Qe hF (Ze _ (Ze _ hS))
    (Zg _ hB) (fun h=>(hPnc B hB).2.2 (h ▸ (hQc S hS).2)))
  have hPnc_bd:(P_nc.card:ℝ)≤(13/1000:ℝ)*(N:ℝ)^2+24*(N:ℝ):=by
   have hraw:=Wg N 3 5 m_nat hN1 (by omega) P_nc
    (Qd hF Zs)
    (fun A hA=>⟨(hPnc A hA).1,(hPnc A hA).2.1,hm_le A hA,hPnc_Icc35 A hA⟩)
   have hsum_le:∑ d∈Icc (3:ℕ) 5,fInt (1/(d:ℝ)) m≤13/1000 :=(Finset.sum_le_sum fun d _=>Wb (by norm_num) hm19.le (by positivity)).trans Kg
   have h3:((5+1-3:ℕ):ℝ)=3:=by norm_num
   rw[h3] at hraw;dsimp only[m] at hsum_le;have hmul:=Zo hsum_le (sq_nonneg (N:ℝ));linarith only[hraw,hmul]
  have hinv:(20/1000:ℝ)≤1/(2*(d₀:ℝ)^2):=by
   have hd5:(d₀:ℝ)≤5:=by exact_mod_cast hd₀35.2
   have hd0pos:(0:ℝ)<(d₀:ℝ):=by exact_mod_cast (by omega:0< d₀)
   have hpos:(0:ℝ)<2*(d₀:ℝ)^2:=by positivity
   rw[le_div_iff₀ hpos];nlinarith only[hd5,hd0pos]
  have hmain:(1/2-1/(2*(d₀:ℝ)^2)+13/1000)*(N:ℝ)^2≤(N:ℝ)^2/2:=by nlinarith only[hinv,sq_nonneg (N:ℝ)]
  have herr:210*(N:ℝ)*(log (N:ℝ)+2)^2+24*(N:ℝ) ≤500*(N:ℝ)*(log (N:ℝ)+2)^2:=by nlinarith only[hNpos,h1sq]
  linarith only[hqd,hPnc_bd,hmain,herr]
private lemma Vg :∀ᶠ N:ℕ in Filter.atTop,(Erdos272.maxArithInterCard N:ℝ)≤(N:ℝ)^2/2+100*(N:ℝ)^((5:ℝ)/3):=by
 classical
 have h1:∀ᶠ N:ℕ in Filter.atTop,1000≤ N:=Filter.eventually_ge_atTop 1000;have h2:∀ᶠ N:ℕ in Filter.atTop,5100^3≤ N:=Filter.eventually_ge_atTop (5100^3);have h3:=X3
 have h4:=Wr (ε:=(1:ℝ)/10) (by norm_num)
 have h5:=Qi (a:=(6:ℝ)/5) (b:=(5:ℝ)/3) (C:=50) (by norm_num)
 have h6:=Qi (a:=(7:ℝ)/5) (b:=(5:ℝ)/3) (C:=8*(512:ℝ)^6/10) (by norm_num)
 have h7:=Qi (a:=(1:ℝ)) (b:=(5:ℝ)/3) (C:=1) (by norm_num)
 have h8:=Qi (a:=(5:ℝ)/3) (b:=(2:ℝ)) (C:=3000) (by norm_num)
 filter_upwards [h1,h2,h3,h4,h5,h6,h7,h8] with N hN1000 hN5100 hempty hlog h65 h75 h15 h532
 have hN1:1≤ N:=by omega
 have hNpos:(0:ℝ)<(N:ℝ):=by exact_mod_cast (by omega:0< N)
 have hneS:{(#A:ℕ)|(A:Zf (Zf ℕ)) (_:Zt N A)}.Nonempty :=⟨0,∅,⟨Finset.empty_subset _,by simp⟩,rfl⟩
 have hbddS:BddAbove {(#A:ℕ)|(A:Zf (Zf ℕ)) (_:Zt N A)}:=by
  refine⟨((Icc 1 N).powerset).card,?_⟩
  rintro _ ⟨A,hA,rfl⟩;exact Zm hA.1
 obtain⟨F,hF,hFcard⟩:=Nat.sSup_mem hneS hbddS;change F.card=Erdos272.maxArithInterCard N at hFcard;rw[←hFcard];set s:=Nat.ceil ((N:ℝ)^((2:ℝ)/3))
 set F_small:=F.filter (fun S=>S.card≤1)
 set P_big:=F.filter (fun S=>2≤ S.card/\IsAP S)
 set Q_small:=F.filter (fun S=>2≤ S.card/\¬ IsAP S/\S.card< s)
 set Q_large:=F.filter (fun S=>2≤ S.card/\¬ IsAP S/\s≤ S.card)
 have hpart:(F.card:ℝ)=(F_small.card:ℝ)+(P_big.card:ℝ)+(Q_small.card:ℝ)+(Q_large.card:ℝ):=by
  have hd12:Disjoint F_small P_big:=by
   rw[Zk];intro S h1 h2
   have:=(Za.mp h1).2;have:=(Za.mp h2).2.1;omega
  have hd123:Disjoint (F_small∪P_big) Q_small:=by
   rw[Zk];intro S h1 h2;have hq:=(Za.mp h2).2
   rcases Zd.mp h1 with h|h
   ·have:=(Za.mp h).2;omega
   ·exact hq.2.1 (Za.mp h).2.2
  have hd1234:Disjoint (F_small∪P_big∪Q_small) Q_large:=by
   rw[Zk];intro S h1 h2;have hq:=(Za.mp h2).2
   rcases Zd.mp h1 with h12|h3
   ·rcases Zd.mp h12 with h1'|h2'
    ·have:=(Za.mp h1').2;omega
    ·exact hq.2.1 (Za.mp h2').2.2
   ·have:=(Za.mp h3).2.2.2;omega
  have hu:F=F_small∪P_big∪Q_small∪Q_large:=by
   ext S;simp only[F_small,P_big,Q_small,Q_large,Zd,Za]
   constructor
   ·intro hS
    by_cases hle1:S.card≤1
    ·exact Or.inl (Or.inl (Or.inl ⟨hS,hle1⟩))
    ·by_cases hap:IsAP S
     ·exact Or.inl (Or.inl (Or.inr ⟨hS,by omega,hap⟩))
     ·by_cases hlt:S.card< s
      ·exact Or.inl (Or.inr ⟨hS,by omega,hap,hlt⟩)
      ·exact Or.inr ⟨hS,by omega,hap,by omega⟩
   ·rintro (((⟨hS,_⟩|⟨hS,_⟩)|⟨hS,_⟩)|⟨hS,_⟩) <;> exact hS
  rw[hu,Zq hd1234,Zq hd123,Zq hd12];push_cast;ring
 have hsmall_bd:(F_small.card:ℝ)≤(N:ℝ)+1:=by
  exact_mod_cast Kh N F_small
   (fun S hS=>Zy.mp (hF.1 (Za.mp hS).1))
   (fun S hS=>(Za.mp hS).2)
 have hs_ge5100:5100≤ s:=by
  refine Nat.le_ceil _ |> le_trans ?_ |> Nat.cast_le.mp
  have h1:((5100:ℝ)^(3:ℕ))≤(N:ℝ):=by exact_mod_cast hN5100
  have h2:(5100:ℝ)=((5100:ℝ)^(3:ℕ))^((1:ℝ)/3):=by
   rw[←Real.rpow_natCast,←Real.rpow_mul (by norm_num)];norm_num
  have h3:(5100:ℝ)≤(N:ℝ)^((1:ℝ)/3):=by
   rw[h2];exact Real.rpow_le_rpow (by positivity) h1 (by norm_num)
  have h4:(N:ℝ)^((1:ℝ)/3)≤(N:ℝ)^((2:ℝ)/3) :=Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN1) (by norm_num)
  linarith
 have hQlarge_bd:(Q_large.card:ℝ)≤70*(N:ℝ)^((5:ℝ)/3):=by
  have hraw:=Xs N s hs_ge5100 Q_large
   (Qd hF (Zl _ _))
   (fun S hS=>(Za.mp hS).2.2.1)
   (fun S hS=>(Za.mp hS).2.2.2)
  have hs_lb:(N:ℝ)^((2:ℝ)/3)≤(s:ℝ):=Nat.le_ceil _
  have hs_sq:(N:ℝ)^((4:ℝ)/3)≤(s:ℝ)^2:=by
   have h1:=pow_le_pow_left₀ (by positivity) hs_lb 2
   have h2:((N:ℝ)^((2:ℝ)/3))^2=(N:ℝ)^((4:ℝ)/3):=by rw[←Real.rpow_natCast,←Real.rpow_mul hNpos.le];norm_num
   linarith
  have hdiv:70*(N:ℝ)^3/(s:ℝ)^2≤70*(N:ℝ)^3/(N:ℝ)^((4:ℝ)/3) :=div_le_div_of_nonneg_left (by positivity) (by positivity) hs_sq
  have hrpow:70*(N:ℝ)^3/(N:ℝ)^((4:ℝ)/3)=70*(N:ℝ)^((5:ℝ)/3):=by have h3:(N:ℝ)^(3:ℕ)=(N:ℝ)^(3:ℝ):=(Real.rpow_natCast _ _).symm;rw[h3,mul_div_assoc,←Real.rpow_sub hNpos];norm_num
  linarith
 have hN53_nn:(0:ℝ)≤(N:ℝ)^((5:ℝ)/3):=by positivity
 have herr_small:(N:ℝ)+1≤10*(N:ℝ)^((5:ℝ)/3):=by
  rw[one_mul,Real.rpow_one] at h15
  have hNge1:(1:ℝ)≤(N:ℝ):=by exact_mod_cast hN1
  linarith only[h15,hNge1,hN53_nn]
 have herr_log:500*(N:ℝ)*(log (N:ℝ)+2)^2≤10*(N:ℝ)^((5:ℝ)/3):=by
  have hlog_nn:0≤ log (N:ℝ)+2:=by
   have:=Real.log_nonneg (by exact_mod_cast hN1:(1:ℝ)≤(N:ℝ));linarith
  have hsq:(log (N:ℝ)+2)^2≤((N:ℝ)^((1:ℝ)/10))^2 :=pow_le_pow_left₀ hlog_nn hlog 2
  have h15':((N:ℝ)^((1:ℝ)/10))^2=(N:ℝ)^((1:ℝ)/5):=by rw[←Real.rpow_natCast,←Real.rpow_mul hNpos.le];norm_num
  have h65':(N:ℝ)*(N:ℝ)^((1:ℝ)/5)=(N:ℝ)^((6:ℝ)/5):=by
   calc (N:ℝ)*(N:ℝ)^((1:ℝ)/5)=(N:ℝ)^(1:ℝ)*(N:ℝ)^((1:ℝ)/5):=by rw[Real.rpow_one]
     _=(N:ℝ)^((1:ℝ)+1/5):=(Real.rpow_add hNpos _ _).symm
     _=(N:ℝ)^((6:ℝ)/5):=by norm_num
  have hmul:(N:ℝ)*(log (N:ℝ)+2)^2≤(N:ℝ)^((6:ℝ)/5):=by
   calc (N:ℝ)*(log (N:ℝ)+2)^2
       ≤ (N:ℝ)*((N:ℝ)^((1:ℝ)/10))^2:=Zp hsq hNpos.le
     _=(N:ℝ)*(N:ℝ)^((1:ℝ)/5):=by rw[h15']
     _=(N:ℝ)^((6:ℝ)/5):=h65'
  linarith
 have herr_75:8*(512:ℝ)^6*(N:ℝ)^((7:ℝ)/5)≤10*(N:ℝ)^((5:ℝ)/3):=by linarith
 by_cases hstar:∃ c∈Icc 1 N,∀ S∈Q_small,c∈S
 ·obtain⟨c,hc,hc_all⟩:=hstar
  set P_c:=P_big.filter (fun A=>c∈A)
  set P_nc:=P_big.filter (fun A=>c∉A)
  have hPbig_part:(P_big.card:ℝ)=(P_c.card:ℝ)+(P_nc.card:ℝ):=by
   have hd:Disjoint P_c P_nc:=by rw[Zk];intro A h1 h2;exact (Za.mp h2).2 (Za.mp h1).2
   have hu:P_big=P_c∪P_nc:=by
    ext A;simp only[P_c,P_nc,Zd,Za]
    by_cases hcA:c∈A <;> simp[hcA]
   rw[hu,Zq hd,Nat.cast_add]
  have hdisjQP:Disjoint Q_small P_c:=by rw[Zk];intro S h1 h2;exact (Za.mp h1).2.2.1 (Za.mp (Za.mp h2).1).2.2
  have hdisjQN:Disjoint Q_small P_nc:=by rw[Zk];intro S h1 h2;exact (Za.mp h1).2.2.1 (Za.mp (Za.mp h2).1).2.2
  have hdisjPN:Disjoint P_c P_nc:=by rw[Zk];intro A h1 h2;exact (Za.mp h2).2 (Za.mp h1).2
  have hsub3:Zt N (Q_small∪P_c∪P_nc) :=Qd hF (Zu
    (Zu (Zl _ _)
     ((Zl _ _).trans (Zl _ _)))
    ((Zl _ _).trans (Zl _ _)))
  have hst:=Vb N c hN1000 hc Q_small P_c P_nc hsub3
   hdisjQP hdisjQN hdisjPN
   (fun S hS=>⟨(Za.mp hS).2.2.1,hc_all S hS⟩)
   (fun A hA=>by
    obtain⟨hA',hcA⟩:=Za.mp hA;exact⟨(Za.mp hA').2.2,(Za.mp hA').2.1,hcA⟩)
   (fun A hA=>by
    obtain⟨hA',hncA⟩:=Za.mp hA;exact⟨(Za.mp hA').2.2,(Za.mp hA').2.1,hncA⟩)
  linarith only[hpart,hPbig_part,hsmall_bd,hQlarge_bd,hst,herr_small,herr_log,herr_75]
 ·push Not at hstar
  have hQsmall_bd:=hempty Q_small (Qd hF (Zl _ _))
   (fun S hS=>⟨(Za.mp hS).2.2.1,(Za.mp hS).2.2.2⟩) hstar
  have hPbig_bd:=X9 N hN1 P_big (Qd hF (Zl _ _))
   (fun A hA=>⟨(Za.mp hA).2.2,(Za.mp hA).2.1⟩)
  have hlog_ge:(1:ℝ)≤ log (N:ℝ)+2:=by
   have:=Real.log_nonneg (by exact_mod_cast hN1:(1:ℝ)≤(N:ℝ));linarith
  have hLsq':log (N:ℝ)+2≤(log (N:ℝ)+2)^2:=by nlinarith only[hlog_ge]
  have h12log:12*(N:ℝ)*(log (N:ℝ)+2)≤10*(N:ℝ)^((5:ℝ)/3):=by
   have:12*(N:ℝ)*(log (N:ℝ)+2)≤500*(N:ℝ)*(log (N:ℝ)+2)^2:=by nlinarith only[hNpos,hLsq']
   linarith only[this,herr_log]
  have h53_le:(N:ℝ)^((5:ℝ)/3)≤(N:ℝ)^2/3000:=by rw[Real.rpow_two] at h532;linarith only[h532]
  linarith only[hpart,hsmall_bd,hPbig_bd,hQsmall_bd,hQlarge_bd,herr_small,h12log,h53_le,hN53_nn]
end Szabo272
theorem OMA.solution:type_of% @Erdos272.erdos_272.variants.szabo:=by
 rw[Asymptotics.isBigO_iff]
 refine⟨100,?_⟩
 have h1:∀ᶠ N:ℕ in Filter.atTop,3≤ N:=Filter.eventually_ge_atTop 3;have h2:=Szabo272.Vg
 have h3:=Szabo272.Qi (a:=(1:ℝ)) (b:=(5:ℝ)/3) (C:=1) (by norm_num)
 filter_upwards [h1,h2,h3] with N hN3 hup h15
 have hN1:1≤ N:=by omega
 have hlow_nat:=Szabo272.Kk N hN1
 have hchoose:2*N.choose 2=N*(N-1):=by
  rw[Nat.choose_two_right]
  have hdvd:2 ∣ N*(N-1):=by
   rcases Nat.even_or_odd N with ⟨k,rfl⟩|⟨k,rfl⟩
   ·exact⟨k*(k+k-1),by ring⟩
   ·exact⟨(2*k+1)*k,by simp;ring⟩
  exact Nat.mul_div_cancel' hdvd
 have hlow:(N:ℝ)^2/2-(N:ℝ)≤(Erdos272.maxArithInterCard N:ℝ):=by
  have h1':((N.choose 2:ℕ):ℝ)≤(Erdos272.maxArithInterCard N:ℝ):=by
   exact_mod_cast (by omega:N.choose 2≤ Erdos272.maxArithInterCard N)
  have h2':2*((N.choose 2:ℕ):ℝ)=(N:ℝ)*((N:ℝ)-1):=by
   have hc:((2*N.choose 2:ℕ):ℝ)=((N*(N-1):ℕ):ℝ):=by exact_mod_cast hchoose
   rw[Nat.cast_mul,Nat.cast_mul,Nat.cast_sub hN1] at hc;simpa using hc
  have hN0:(0:ℝ)≤(N:ℝ):=by positivity
  nlinarith
 have hN_le:(N:ℝ)≤(N:ℝ)^((5:ℝ)/3):=by rw[one_mul,Real.rpow_one] at h15;exact h15
 have hlog1:(1:ℝ)≤ Real.log (N:ℝ):=by
  have he3:Real.exp 1≤(N:ℝ):=by
   have:=Real.exp_one_lt_d9
   have h3R:(3:ℝ)≤(N:ℝ):=by exact_mod_cast hN3
   linarith
  have:=Real.log_le_log (Real.exp_pos 1) he3
  rwa[Real.log_exp] at this
 have hlog3:(1:ℝ)≤(Real.log (N:ℝ))^3:=one_le_pow₀ hlog1
 have hN53_nn:(0:ℝ)≤(N:ℝ)^((5:ℝ)/3):=by positivity
 have hmul:(N:ℝ)^((5:ℝ)/3)≤(N:ℝ)^((5:ℝ)/3)*(Real.log (N:ℝ))^3 :=le_mul_of_one_le_right hN53_nn hlog3
 have hnorm_rhs:‖(N:ℝ)^((5:ℝ)/3)*(Real.log (N:ℝ))^3‖ =(N:ℝ)^((5:ℝ)/3)*(Real.log (N:ℝ))^3 :=Real.norm_of_nonneg (mul_nonneg hN53_nn (by linarith))
 rw[hnorm_rhs,Real.norm_eq_abs,abs_le]
 constructor <;> linarith only[hup,hlow,hN_le,hmul,hN53_nn]
