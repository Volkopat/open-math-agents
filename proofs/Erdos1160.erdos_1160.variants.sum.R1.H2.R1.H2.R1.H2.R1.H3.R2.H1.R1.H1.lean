import OMAReductions.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1_H3_R2_H1_R1
import Mathlib
-- CNT3 (Li-Qiao Thm 6.3 at class 3): the H2Dev library closure of RedABridge in one file; comments stripped,
-- unused declarations pruned, local names shortened (Q*), Mathlib aliases (Z*), whitespace compacted.
open Subgroup renaming closure → ZA, subset_closure → ZC, closure_le → ZD, mem_sup_left → ZJ, mem_sup_right → ZL, mem_top → ZM, closure_mono → ZO
open Nat renaming card → ZB
open Additive renaming ofMul → ZE
open QuotientGroup renaming mk' → ZF
open Set renaming range → ZG, Iio → ZP
open Abelianization renaming of → ZH
open Multiplicative renaming ofAdd → ZI
open QuotientAddGroup renaming mk → ZK
open Finset renaming range → ZQ
open List renaming ofFn → ZR
namespace OMA.SimsLite
universe u v
section NF
variable {G:Type u} [Group G] {H:Type v} [Group H]
def nf:List G→(ℕ→ℕ)→G
  | [],_=>1
  | b::l,e=>nf l (fun k=>e (k+1))*b^(e 0)
@[simp] lemma Qo4 (e:ℕ→ℕ):nf ([]:List G) e=1:=rfl
@[simp] lemma Qo2 (b:G) (l:List G) (e:ℕ→ℕ):
    nf (b::l) e=nf l (fun k=>e (k+1))*b^(e 0):=rfl
end NF
section Suffix
variable {G:Type u} [Group G]
end Suffix
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section Comm
variable {D:Type u} [Group D]
abbrev lcs (D:Type u) [Group D] (n:ℕ):Subgroup D:=(⊤:Subgroup D).lowerCentralSeries n
lemma lcs_zero:lcs D 0=⊤:=rfl
lemma lcs_succ (n:ℕ):lcs D (n+1)=⁅lcs D n,⊤⁆:=rfl
lemma Qhk (n:ℕ):lcs D (n+1)=⁅(⊤:Subgroup D),lcs D n⁆:=by
 rw[lcs_succ,Subgroup.commutator_comm]
lemma Qd {a b:ℕ} (h:a≤b):lcs D b≤lcs D a:=
  Subgroup.lowerCentralSeries_antitone (⊤:Subgroup D) h
lemma Qb {n:ℕ} {x:D} (hx:x∈lcs D n) (g:D):
    ⁅x,g⁆∈lcs D (n+1):=by
 rw[lcs_succ]
 exact Subgroup.commutator_mem_commutator hx (ZM g)
lemma Qj {n:ℕ} (g:D) {x:D} (hx:x∈lcs D n):
    ⁅g,x⁆∈lcs D (n+1):=by
 rw[Qhk]
 exact Subgroup.commutator_mem_commutator (ZM g) hx
def zn (N:Subgroup D) [N.Normal] (x:D):Subgroup D where
  carrier :={g | ⁅x,g⁆∈N}
  one_mem':=by
    show ⁅x,(1:D)⁆∈N
    rw[commutatorElement_one_right]
    exact N.one_mem
  mul_mem':=by
    intro g h hg hh
    show ⁅x,g*h⁆∈N
    have e:⁅x,g*h⁆=⁅x,g⁆*(g*⁅x,h⁆*g⁻¹):=by
     simp only[commutatorElement_def]
     group
    rw[e]
    exact N.mul_mem hg (‹N.Normal›.conj_mem _ hh g)
  inv_mem':=by
    intro g hg
    show ⁅x,g⁻¹⁆∈N
    have e:⁅x,g⁻¹⁆=g⁻¹*⁅x,g⁆⁻¹*g⁻¹⁻¹:=by
     simp only[commutatorElement_def]
     group
    rw[e]
    exact ‹N.Normal›.conj_mem _ (N.inv_mem hg) g⁻¹
lemma Q4p {N:Subgroup D} [N.Normal] {x g:D}:g∈zn N x↔⁅x,g⁆∈N:=Iff.rfl
lemma Qr {N:Subgroup D} {x g:D} (h:⁅x,g⁆∈N):⁅g,x⁆∈N:=by
 rw[← commutatorElement_inv]
 exact N.inv_mem h
lemma Q2o {N:Subgroup D} [N.Normal] {A B:Set D}
    (h:∀ a∈A,∀ b∈B,⁅a,b⁆∈N):
    ⁅ZA A,ZA B⁆≤N:=by
 have hB:∀ a∈A,ZA B≤zn N a:= fun a ha=>
   (ZD (zn N a)).mpr fun b hb=>h a ha b hb
 rw[Subgroup.commutator_le]
 intro x hx y hy
 have hA:ZA A≤zn N y:=
   (ZD (zn N y)).mpr fun a ha=>Qr (hB a ha hy)
 exact Qr (hA hx)
lemma Q1d {K:Subgroup D} {n:ℕ} (h1:lcs D (n+1)≤K) (h2:K≤lcs D n):
    K.Normal:=by
 constructor
 intro k hk g
 have e:g*k*g⁻¹=⁅g,k⁆*k:=by
  simp only[commutatorElement_def]
  group
 rw[e]
 exact K.mul_mem (h1 (Qj g (h2 hk))) hk
lemma Q6r {K:Subgroup D} (h1:lcs D 1≤K):K.Normal:=
  Q1d (n:=0) h1 le_top
lemma Q82 (N:Subgroup D) [N.Normal] {A B C:Subgroup D}
    (h1:⁅⁅B,C⁆,A⁆≤N) (h2:⁅⁅C,A⁆,B⁆≤N):⁅⁅A,B⁆,C⁆≤N:=by
 have key:∀ X Y Z:Subgroup D,⁅⁅X,Y⁆,Z⁆≤N↔
     ⁅⁅X.map (ZF N),Y.map (ZF N)⁆,
       Z.map (ZF N)⁆=⊥:=by
  intro X Y Z
  rw [← Subgroup.map_commutator, ← Subgroup.map_commutator,Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk']
 rw[key]at h1 h2⊢
 exact Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
lemma Qa6:∀ (b a:ℕ),⁅lcs D a,lcs D b⁆≤lcs D (a+b+1)
  | 0,a=>by rw[lcs_zero, ← lcs_succ]
  | b +1,a=>by
    rw[lcs_succ b,Subgroup.commutator_comm]
    have h1:⁅⁅(⊤:Subgroup D),lcs D a⁆,lcs D b⁆≤lcs D (a+(b+1)+1):=by
     rw[← Qhk]
     have:=Qa6 b (a+1)
     rwa[show a+1+b+1=a+(b+1)+1 by omega]at this
    have h2:⁅⁅lcs D a,lcs D b⁆,(⊤:Subgroup D)⁆≤lcs D (a+(b+1)+1):=by
     rw[show a+(b+1)+1=a+b+1+1 by omega,lcs_succ]
     exact Subgroup.commutator_mono (Qa6 b a) le_rfl
    exact Q82 _ h1 h2
lemma Q1c {a b:ℕ} {x y:D} (hx:x∈lcs D a) (hy:y∈lcs D b):
    ⁅x,y⁆∈lcs D (a+b+1):=
  Qa6 b a (Subgroup.commutator_mem_commutator hx hy)
lemma Q33 (x y z:D):⁅x,y *z⁆=⁅x,y⁆*⁅y,⁅x,z⁆⁆*⁅x,z⁆:=by
 simp only[commutatorElement_def]
 group
lemma Q2g (x y z:D):⁅y *z,x⁆=⁅y,⁅z,x⁆⁆*⁅z,x⁆*⁅y,x⁆:=by
 simp only[commutatorElement_def]
 group
lemma Q9c {W:Subgroup D} (hW:lcs D 2≤W) {x y z:D} (hxz:⁅x,z⁆∈W):
    ⁅x,y *z⁆∈W↔⁅x,y⁆∈W:=by
 have h3:⁅y,⁅x,z⁆⁆∈W:=
   hW (Qj y (Qj (n:=0) x (ZM z)))
 rw [Q33,Subgroup.mul_mem_cancel_right W hxz,
   Subgroup.mul_mem_cancel_right W h3]
lemma Qaw {W:Subgroup D} (hW:lcs D 2≤W) {x y z:D} (hyx:⁅y,x⁆∈W):
    ⁅y *z,x⁆∈W↔⁅z,x⁆∈W:=by
 have h3:⁅y,⁅z,x⁆⁆∈W:=
   hW (Qj y (Qj (n:=0) z (ZM x)))
 rw [Q2g,Subgroup.mul_mem_cancel_right W hyx,
   Subgroup.mul_mem_cancel_left W h3]
end Comm
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section Code
abbrev Shape (m:ℕ):Type:=
  (Fin m→Fin (m+1))×(Fin m→Option (Option (Fin m×Fin m)))×
    (Fin m→Option (Fin m))×(Fin m→Fin m)
variable {m:ℕ}
def Shape.lv (s:Shape m) (i:Fin m):ℕ:=s.1 i
def Shape.df (s:Shape m) (i:Fin m):Option (Option (Fin m×Fin m)):=s.2.1 i
def Shape.cidx (s:Shape m) (i:Fin m):Option (Fin m):=s.2.2.1 i
def Shape.st (s:Shape m) (i:Fin m):ℕ:=s.2.2.2 i
noncomputable def Shape.Qkl (s:Shape m):ℕ:=ZB {i:Fin m//(s.cidx i).isSome}
structure Shape.Valid (s:Shape m):Prop where
  mono:∀ i j:Fin m,i≤j→s.lv i≤ s.lv j
  free:∀ i,s.df i=none→s.lv i=0
  pow:∀ i,s.df i=some none→∃ h:0< i.val,
    s.lv ⟨i.val - 1,lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩=s.lv i∧(s.lv i=1→s.st i=s.st ⟨i.val - 1,lt_of_le_of_lt (Nat.sub_le _ _) i.isLt⟩)
  comm : ∀ i a b,s.df i=some (some (a,b))→
    a < i∧b< i∧(s.cidx b).isSome∧s.lv i=s.lv a+1∧
      (s.lv i=1→∃ ka kb:Fin m,s.cidx a=some ka∧s.cidx b=some kb∧ka<kb∧
        kb.val=s.st i)
  core:∀ i (k:Fin m),s.cidx i=some k→s.df i=none∧k.val<s.Qkl
  core_inj:∀ i j (k:Fin m),s.cidx i=some k→s.cidx j=some k→i=j
  steps:∀ β,1≤β→β<s.Qkl→∃ i,s.lv i=1∧s.st i=β
  st_range:∀ i,s.lv i=1→1≤ s.st i∧s.st i<s.Qkl
def Shape.Qnw (s:Shape m):Fin 4×Fin m×Fin m×Fin m→Prop
  | (κ,i,k,j)=>
    (κ.val=0∧k=i∧i<j)∨
    (κ.val=1∧s.lv i=0∧s.lv k=0∧i<k∧1≤ s.lv j)∨
    (κ.val=2∧s.lv i=1∧(∃ c:Fin m,s.cidx k=some c∧c.val≤ s.st i)∧2≤ s.lv j)∨
    (κ.val=3∧2≤ s.lv i∧(s.cidx k).isSome∧s.lv i+1≤ s.lv j)
def Shape.Idx (s:Shape m):Type:={q:Fin 4×Fin m×Fin m×Fin m//s.Qnw q}
instance (s:Shape m):Finite s.Idx:=Subtype.finite
def Code (p m:ℕ):Type:=Σ s:{s:Shape m//s.Valid},(s.1.Idx→Fin p)
instance (p m:ℕ):Finite (Code p m):=by
 unfold Code
 infer_instance
end Code
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section Lie
variable {D:Type u} [Group D]
abbrev Q2m (E:ℕ→ Set D) (l:ℕ):Subgroup D:=ZA (E l)⊔lcs D (l+1)
lemma Q31 {E:ℕ→ Set D} {l:ℕ} {x:D} (h:x∈lcs D (l+1)):
    x∈Q2m E l:=
  ZL h
lemma Qnb {E:ℕ→ Set D} (hcl:∀ w,1≤w→ZA (E w)≤lcs D w)
    {l:ℕ} (hl:1≤l):Q2m E l≤lcs D l:=
  sup_le (hcl l hl) (Qd (Nat.le_succ l))
lemma Qjs {E:ℕ→ Set D} (hcl:∀ w,1≤w→ZA (E w)≤lcs D w)
    {l:ℕ} (hl:1≤l):(Q2m E l).Normal:=
  Q1d (n:=l) le_sup_right (Qnb hcl hl)
lemma Q3s {N:Subgroup D} [N.Normal] {S:Set D} {L:Subgroup D} {g:D}
    (hS:∀ x∈S,⁅x,g⁆∈N) (hL:∀ x∈L,⁅x,g⁆∈N):
    ∀ x∈ZA S⊔L,⁅x,g⁆∈N:=by
 have hle:ZA S⊔L≤zn N g:=
   sup_le ((ZD (zn N g)).mpr fun y hy=>Q4p.mpr (Qr (hS y hy)))
     fun y hy=>Q4p.mpr (Qr (hL y hy))
 intro x hx
 exact Qr (Q4p.mp (hle hx))
lemma Q7v {N:Subgroup D} [N.Normal] {S:Set D} {L:Subgroup D} {x:D}
    (hS:∀ g∈S,⁅x,g⁆∈N) (hL:∀ g∈L,⁅x,g⁆∈N):
    ∀ g∈ZA S⊔L,⁅x,g⁆∈N:= fun g hg=>
  Qr (Q3s (N:=N) (S:=S) (L:=L) (g:=x)
    (fun y hy=>Qr (hS y hy)) (fun y hy=>Qr (hL y hy)) g hg)
lemma Q77 {N:Subgroup D} [N.Normal] {K:Subgroup D} {S:Set D}
    (h:∀ x∈K,∀ s∈S,⁅x,s⁆∈N):⁅K,ZA S⁆≤N:=by
 have h':=Q2o (N:=N) (A:=(K:Set D)) (B:=S)
   (fun x hx s hs=>h x (SetLike.mem_coe.mp hx) s hs)
 rwa[Subgroup.closure_eq]at h'
lemma Q7u (N K K':Subgroup D) [N.Normal] [K.Normal] [K'.Normal] {a b c:D}
    (hbc:⁅b,c⁆∈K) (hKa:∀ z∈K,⁅z,a⁆∈N) (hca:⁅c,a⁆∈K')
    (hK'b:∀ z∈K',⁅z,b⁆∈N):⁅⁅a,b⁆,c⁆∈N:=by
 have hBC:⁅ZA ({b}:Set D),ZA ({c}:Set D)⁆≤K:=
   Q2o fun x hx y hy=>by
     rw[Set.mem_singleton_iff]at hx hy
     rw[hx,hy]
     exact hbc
 have hCA:⁅ZA ({c}:Set D),ZA ({a}:Set D)⁆≤K':=
   Q2o fun x hx y hy=>by
     rw[Set.mem_singleton_iff]at hx hy
     rw[hx,hy]
     exact hca
 have h1:⁅⁅ZA ({b}:Set D),ZA ({c}:Set D)⁆,
     ZA ({a}:Set D)⁆≤N:=
   (Subgroup.commutator_mono hBC le_rfl).trans (Q77 fun z hz s hs=>by
     rw[Set.mem_singleton_iff]at hs
     rw[hs]
     exact hKa z hz)
 have h2:⁅⁅ZA ({c}:Set D),ZA ({a}:Set D)⁆,
     ZA ({b}:Set D)⁆≤N:=
   (Subgroup.commutator_mono hCA le_rfl).trans (Q77 fun z hz s hs=>by
     rw[Set.mem_singleton_iff]at hs
     rw[hs]
     exact hK'b z hz)
 have h3:=Q82 N h1 h2
 exact h3 (Subgroup.commutator_mem_commutator
   (Subgroup.commutator_mem_commutator (ZC (Set.mem_singleton a))
     (ZC (Set.mem_singleton b)))
   (ZC (Set.mem_singleton c)))
lemma Qjn (t:ℕ) (u:ℕ→D) (P:Set (ℕ×ℕ)) (E:ℕ→ Set D)
    (hE1:E 1=(fun ab:ℕ×ℕ=> ⁅u ab.1,u ab.2⁆) '' P)
    (hL2:∀ w,1≤w→∀ x∈E (w+1),∃ y∈ZA (E w),∃ b<t,x =⁅y,u b⁆):
    ∀ w,1≤w→ZA (E w)≤lcs D w:=by
  intro w hw
  induction w,hw using Nat.le_induction with
  | base=>
    refine (ZD (lcs D 1)).mpr ?_
    intro x hx
    rw[hE1]at hx
    obtain ⟨ab, -,rfl⟩:=hx
    exact Qb (n:=0) (ZM (u ab.1)) (u ab.2)
  | succ w hw ih=>
    refine (ZD (lcs D (w+1))).mpr ?_
    intro x hx
    obtain ⟨y,hy,b, -,rfl⟩:=hL2 w hw x hx
    exact Qb (ih hy) (u b)
lemma Qho (t:ℕ) (u:ℕ→D) (H1:Set D) (P:Set (ℕ×ℕ)) (E:ℕ→ Set D)
    (hP:∀ ab∈P,ab.1<ab.2∧ab.2<t)
    (hE1:E 1=(fun ab:ℕ×ℕ=> ⁅u ab.1,u ab.2⁆) '' P)
    (hL2:∀ w,1≤w→∀ x∈E (w+1),∃ y∈ZA (E w),∃ b<t,x =⁅y,u b⁆)
    (hL0:ZA H1⊔lcs D 1=⊤)
    (hH1:∀ x∈H1,∀ y∈H1,⁅x,y⁆∈ZA (E 1)⊔lcs D 2)
    (hH2:∀ ab∈P,∀ k≤ab.2,⁅⁅u ab.1,u ab.2⁆,u k⁆∈ZA (E 2)⊔lcs D 3)
    (hH3:∀ w,2≤w→∀ x∈E w,∀ k<t,
      ⁅x,u k⁆∈ZA (E (w+1))⊔lcs D (w+2)):
    ∀ w,1≤w→lcs D w≤ZA (E w)⊔lcs D (w+1):=by
  have hcl:=Qjn t u P E hE1 hL2
  have hMn:∀ l,1≤l→(Q2m E l).Normal:= fun l hl=>Qjs hcl hl
  have hc1:∀ a b:D,⁅a,b⁆∈lcs D 1:= fun a b=>
    Qb (n:=0) (ZM a) b
  have hg:∀ g:D,g∈ZA H1⊔lcs D 1:= fun g=>by
    rw[hL0]
    exact ZM g
  have hA0:lcs D 1≤Q2m E 1:=by
   have:=hMn 1 le_rfl
   rw[show lcs D 1=⁅(⊤:Subgroup D),⊤⁆ from lcs_succ 0,Subgroup.commutator_le]
   intro x _ g _
   refine Q3s ?_ ?_ x (hg x)
   · intro y hy
     refine Q7v ?_ ?_ g (hg g)
     · intro h hh
       exact hH1 y hy h hh
     · intro h hh
       exact Q31 (Qj y hh)
   · intro y hy
     exact Q31 (Qb hy g)
  have hB1 :∀ k,k<t→∀ x∈Q2m E 1,⁅x,u k⁆∈Q2m E 2:=by
   have:=hMn 1 le_rfl
   have:=hMn 2 (by omega)
   intro k
   induction k using Nat.strong_induction_on with
   | _ k ih =>
     intro hk
     refine Q3s ?_ ?_
     · intro z hz
       rw[hE1]at hz
       obtain ⟨ab,hab,rfl⟩:=hz
       obtain ⟨hab1,hab2⟩:=hP ab hab
       show ⁅⁅u ab.1,u ab.2⁆,u k⁆∈Q2m E 2
       by_cases hkb:k≤ab.2
       · exact hH2 ab hab k hkb
       · exact Q7u (Q2m E 2) (Q2m E 1) (Q2m E 1) (a:=u ab.1) (b:=u ab.2) (c:=u k)
           (hA0 (hc1 _ _)) (ih ab.1 (by omega) (by omega)) (hA0 (hc1 _ _))
           (ih ab.2 (by omega) (by omega))
     · intro z hz
       exact Q31 (Qb hz (u k))
  have hB:∀ l,1≤l→∀ k,k<t→∀ x∈Q2m E l,⁅x,u k⁆∈Q2m E (l+1):=by
   intro l hl k hk
   rcases Nat.lt_or_ge l 2 with h | h
   · have hl1:l=1:=by omega
     subst hl1
     exact hB1 k hk
   · have:=hMn (l+1) (by omega)
     refine Q3s ?_ ?_
     · intro z hz
       exact hH3 l h z hz k hk
     · intro z hz
       exact Q31 (Qb hz (u k))
  have hred:∀ l,1≤l→(∀ x∈E l,∀ h∈H1,⁅x,h⁆∈Q2m E (l+1))→
      ∀ x∈Q2m E l,∀ g:D,⁅x,g⁆∈Q2m E (l+1):=by
   intro l hl hgen x hx g
   have:=hMn (l+1) (by omega)
   refine Q3s ?_ ?_ x hx
   · intro y hy
     refine Q7v ?_ ?_ g (hg g)
     · intro h hh
       exact hgen y hy h hh
     · intro h hh
       exact Q31 (Q1c (hcl l hl (ZC hy)) hh)
   · intro y hy
     exact Q31 (Qb hy g)
  have hA :∀ l,1≤l→∀ x∈Q2m E l,∀ g:D,⁅x,g⁆∈Q2m E (l+1):=by
   intro l hl
   induction l,hl using Nat.le_induction with
   | base=>
     refine hred 1 le_rfl ?_
     have:=hMn 1 le_rfl
     have:=hMn 2 (by omega)
     intro x hx h _
     rw[hE1]at hx
     obtain ⟨ab,hab,rfl⟩:=hx
     obtain ⟨hab1,hab2⟩:=hP ab hab
     exact Q7u (Q2m E 2) (Q2m E 1) (Q2m E 1) (a:=u ab.1) (b:=u ab.2) (c:=h)
       (hA0 (hc1 _ _)) (hB 1 le_rfl ab.1 (by omega)) (hA0 (hc1 _ _)) (hB 1 le_rfl ab.2 hab2)
   | succ j hj ih=>
     refine hred (j+1) (by omega) ?_
     have:=hMn 1 le_rfl
     have:=hMn (j+1) (by omega)
     have:=hMn (j+1+1) (by omega)
     intro x hx h _
     obtain ⟨y,hy,bi,hbi,rfl⟩:=hL2 j hj x hx
     have hyM:y∈Q2m E j:=ZJ hy
     have hyl:y∈lcs D j:=hcl j hj hy
     have h5b:∀ z∈Q2m E 1,⁅z,y⁆∈Q2m E (j+1+1):=by
      refine Q3s ?_ ?_
      · intro z hz
        rw[hE1]at hz
        obtain ⟨cd,hcd,rfl⟩:=hz
        obtain ⟨hcd1,hcd2⟩:=hP cd hcd
        exact Q7u (Q2m E (j+1+1)) (Q2m E (j+1)) (Q2m E (j+1))
          (a:=u cd.1) (b:=u cd.2) (c:=y)
          (Qr (hB j hj cd.2 hcd2 y hyM)) (hB (j+1) (by omega) cd.1 (by omega))
          (hB j hj cd.1 (by omega) y hyM) (hB (j+1) (by omega) cd.2 hcd2)
      · intro z hz
        exact Q31 (Qd (by omega) (Q1c hz hyl))
     exact Q7u (Q2m E (j+1+1)) (Q2m E 1) (Q2m E (j+1)) (a:=y) (b:=u bi) (c:=h)
       (hA0 (hc1 _ _)) h5b (Qr (ih y hyM h)) (hB (j+1) (by omega) bi hbi)
  have hfin:∀ l,1≤l→lcs D l≤Q2m E l:=by
   intro l hl
   induction l,hl using Nat.le_induction with
   | base=>exact hA0
   | succ j hj ih=>
     rw[lcs_succ,Subgroup.commutator_le]
     intro x hx g _
     exact hA j hj x (ih hx) g
  exact hfin
lemma Qgx (t:ℕ) (u:ℕ→D) (H1:Set D) (P:Set (ℕ×ℕ)) (E:ℕ→ Set D)
    (hP:∀ ab∈P,ab.1<ab.2∧ab.2<t)
    (hE1:E 1=(fun ab:ℕ×ℕ=> ⁅u ab.1,u ab.2⁆) '' P)
    (hL2:∀ w,1≤w→∀ x∈E (w+1),∃ y∈ZA (E w),∃ b<t,x =⁅y,u b⁆)
    (hL0:ZA H1⊔lcs D 1=⊤)
    (hH1:∀ x∈H1,∀ y∈H1,⁅x,y⁆∈ZA (E 1)⊔lcs D 2)
    (hH2:∀ ab∈P,∀ k≤ab.2,⁅⁅u ab.1,u ab.2⁆,u k⁆∈ZA (E 2)⊔lcs D 3)
    (hH3:∀ w,2≤w→∀ x∈E w,∀ k<t,
      ⁅x,u k⁆∈ZA (E (w+1))⊔lcs D (w+2))
    (N:ℕ) (hN:lcs D N=⊥):
    ∀ w,1≤w→lcs D w≤ZA (⋃ v∈Set.Ici w,E v):=by
  have hL:=Qho t u H1 P E hP hE1 hL2 hL0 hH1 hH2 hH3
  have key:∀ d w,1≤w→N≤w+d→
      lcs D w≤ZA (⋃ v∈Set.Ici w,E v):=by
   intro d
   induction d with
   | zero=>
     intro w _ hw
     calc lcs D w≤lcs D N:=Qd (by omega)
       _=⊥:=hN
       _≤_:=bot_le
   | succ d ih=>
     intro w hw hwd
     have h1:=ih (w+1) (by omega) (by omega)
     refine (hL w hw).trans (sup_le ?_ (h1.trans ?_))
     · exact ZO (Set.subset_biUnion_of_mem (u:=E) (Set.mem_Ici.mpr le_rfl))
     · refine ZO (Set.biUnion_subset_biUnion_left ?_)
       intro v hv
       rw[Set.mem_Ici]at hv⊢
       omega
  intro w hw
  exact key N w hw (by omega)
end Lie
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section StrictStmt
variable {G:Type u} [Group G]
def Wk (u:ℕ→G) (k:ℕ):Subgroup G:=
  ZA {x | ∃ a b,a<b∧b<k∧x =⁅u a,u b⁆}⊔lcs G 2
def Qea (u:ℕ→G) (t:ℕ):Prop:=∀ k,2≤k→k≤t→ Wk u (k - 1)≠Wk u k
lemma Qea.Q7e {u:ℕ→G} {t:ℕ} (h:Qea u t) {k:ℕ} (hk:1≤k)
    (hkt:k+1≤t):Wk u k≠Wk u (k+1):=by
 have:=h (k+1) (by omega) hkt
 rw[Nat.add_sub_cancel]at this
 exact this
end StrictStmt
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section RigidityAux
lemma Qgp {m:ℕ} {C:Fin m→Prop}
    (h:∀ i:Fin m,(∀ j:Fin m,j.val< i.val→ C j)→ C i):∀ i,C i:=by
 have key:∀ n,∀ i:Fin m,i.val=n→ C i:=by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih=>
    intro i hi
    exact h i (fun j hj=>ih j.val (by omega) j rfl)
 exact fun i=>key _ i rfl
variable {D:Type u} [Group D]
end RigidityAux
section Diag
variable {G G':Type u} [Group G] [Group G'] {m:ℕ}
abbrev diagSub (X:Fin m→G) (X':Fin m→G'):Subgroup (G×G'):=
  ZA (ZG fun i=> (X i,X' i))
def Q2x (X:Fin m→G) (X':Fin m→G') (i:Fin m):diagSub X X':=
  ⟨(X i,X' i),ZC ⟨i,rfl⟩⟩
def Q6i (X:Fin m→G) (X':Fin m→G'):diagSub X X'→*G:=
  (MonoidHom.fst G G').comp (diagSub X X').subtype
def Q6a (X:Fin m→G) (X':Fin m→G'):diagSub X X'→*G':=
  (MonoidHom.snd G G').comp (diagSub X X').subtype
lemma Q5z (X:Fin m→G) (X':Fin m→G') (i:Fin m):
    Q6i X X' (Q2x X X' i)=X i:=rfl
lemma Q5t (X:Fin m→G) (X':Fin m→G') (i:Fin m):
    Q6a X X' (Q2x X X' i)=X' i:=rfl
lemma Qit (X:Fin m→G) (X':Fin m→G') {x y:diagSub X X'}
    (h1:Q6i X X' x =Q6i X X' y) (h2:Q6a X X' x =Q6a X X' y):x =y:=
  Subtype.ext (Prod.ext h1 h2)
lemma Qgd (X:Fin m→G) (X':Fin m→G'):
    ZA (ZG (Q2x X X'))=⊤:=by
 have hpre:ZG (Q2x X X')=
     ((↑):diagSub X X'→G×G') ⁻¹' (ZG fun i=> (X i,X' i)):=by
   ext x
   constructor
   · rintro ⟨i,rfl⟩
     exact Set.mem_preimage.mpr ⟨i,rfl⟩
   · rintro ⟨i,hi⟩
     exact ⟨i,Subtype.ext hi⟩
 rw[hpre]
 exact Subgroup.closure_closure_coe_preimage
lemma Qjp (X:Fin m→G) (X':Fin m→G')
    (hX:ZA (ZG X)=⊤):Function.Surjective (Q6i X X'):=by
 intro y
 have hy:y∈(diagSub X X').map (MonoidHom.fst G G'):=by
  rw[MonoidHom.map_closure, ← Set.range_comp]
  have hr :(⇑(MonoidHom.fst G G')∘fun i=> (X i,X' i))=X:=rfl
  rw[hr,hX]
  exact ZM y
 obtain ⟨z,hz,rfl⟩:=Subgroup.mem_map.mp hy
 exact ⟨⟨z,hz⟩,rfl⟩
lemma Qix (X:Fin m→G) (X':Fin m→G')
    (hX:ZA (ZG X')=⊤):Function.Surjective (Q6a X X'):=by
 intro y
 have hy:y∈(diagSub X X').map (MonoidHom.snd G G'):=by
  rw[MonoidHom.map_closure, ← Set.range_comp]
  have hr :(⇑(MonoidHom.snd G G')∘fun i=> (X i,X' i))=X':=rfl
  rw[hr,hX]
  exact ZM y
 obtain ⟨z,hz,rfl⟩:=Subgroup.mem_map.mp hy
 exact ⟨⟨z,hz⟩,rfl⟩
end Diag
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section CoreFlag
variable {G:Type u} [Group G]
def Q1e (N:Subgroup G) (u:ℕ→G) (k:ℕ):Subgroup G:=
  ZA {x | ∃ a b,a<b∧b<k∧x =⁅u a,u b⁆}⊔N
def Q10 (N:Subgroup G) (u:ℕ→G) (t:ℕ):Prop:=
  ∀ k,2≤k→k≤t→Q1e N u (k - 1)≠Q1e N u k
lemma Q3t (N:Subgroup G) (u:ℕ→G) (k:ℕ):N≤Q1e N u k:=by
 unfold Q1e
 exact le_sup_right
lemma Q2a (N:Subgroup G) (u:ℕ→G) {a b k:ℕ} (hab:a<b) (hbk:b<k):
    ⁅u a,u b⁆∈Q1e N u k:=by
 unfold Q1e
 exact ZJ (ZC ⟨a,b,hab,hbk,rfl⟩)
lemma Q6l (N:Subgroup G) {u:ℕ→G} {k:ℕ} {H:Subgroup G} (h3:N≤H)
    (h:∀ a b,a<b→ b<k→⁅u a,u b⁆∈H):Q1e N u k≤H:=by
 unfold Q1e
 refine sup_le ?_ h3
 rw[ZD]
 rintro _ ⟨a,b,hab,hbk,rfl⟩
 exact h a b hab hbk
lemma Qbv (N:Subgroup G) (u:ℕ→G) {k l:ℕ} (hkl:k≤l):
    Q1e N u k≤Q1e N u l:=
  Q6l N (Q3t N u l) fun a b hab hbk=>Q2a N u hab (by omega)
lemma Q7b (N:Subgroup G) (hN2:N≤lcs G 1) (u:ℕ→G) (k:ℕ):
    Q1e N u k≤lcs G 1:=
  Q6l N hN2 fun a b _ _=>Qb (n:=0) (ZM (u a)) (u b)
lemma Ql7 (N:Subgroup G) (hN3:lcs G 2≤N) (hN2:N≤lcs G 1) (u:ℕ→G)
    (k:ℕ):(Q1e N u k).Normal:=
  Q1d (n:=1) (hN3.trans (Q3t N u k)) (Q7b N hN2 u k)
lemma Qco (N:Subgroup G) {u v:ℕ→G} {k:ℕ} (h:∀ i<k,u i=v i):
    Q1e N u k≤Q1e N v k:=
  Q6l N (Q3t N v k) fun a b hab hbk=>by
    rw[h a (by omega),h b hbk]
    exact Q2a N v hab hbk
lemma Qhq (N:Subgroup G) {u v:ℕ→G} {k:ℕ} (h:∀ i<k,u i=v i):
    Q1e N u k=Q1e N v k:=
  le_antisymm (Qco N h) (Qco N fun i hi=> (h i hi).symm)
lemma Qaj (N:Subgroup G) {u:ℕ→G} {k:ℕ} (h:∀ a<k,⁅u a,u k⁆∈Q1e N u k):
    Q1e N u (k+1)≤Q1e N u k:=by
 refine Q6l N (Q3t N u k) ?_
 intro a b hab hbk
 by_cases hb:b<k
 · exact Q2a N u hab hb
 · rw[show b=k by omega]
   exact h a (by omega)
lemma Q8y (N:Subgroup G) {u:ℕ→G} {k:ℕ}
    (h:Q1e N u k≠Q1e N u (k+1)):∃ a<k,⁅u a,u k⁆∉Q1e N u k:=by
 by_contra hc
 apply h
 refine le_antisymm (Qbv N u (show k≤k+1 by omega)) (Qaj N ?_)
 intro a ha
 by_contra hn
 exact hc ⟨a,ha,hn⟩
lemma Qk4 (N:Subgroup G) (v:ℕ→G) (t:ℕ):
    Q1e N v t≤⁅ZA (v '' ZP t),ZA (v '' ZP t)⁆⊔N:=
  Q6l N le_sup_right fun a b hab hbt=>
    ZJ (Subgroup.commutator_mem_commutator
      (ZC ⟨a,Set.mem_Iio.mpr (by omega),rfl⟩)
      (ZC ⟨b,Set.mem_Iio.mpr hbt,rfl⟩))
lemma Q6v (N:Subgroup G) {u:ℕ→G} {t:ℕ}
    (h:∀ k,1≤k→k+1≤t→Q1e N u k≠Q1e N u (k+1)):Q10 N u t:=by
 intro k hk hkt
 obtain ⟨j,rfl⟩:∃ j,k=j+1:=⟨k - 1,by omega⟩
 rw[Nat.add_sub_cancel]
 exact h j (by omega) hkt
lemma Q10.Q7e {N:Subgroup G} {u:ℕ→G} {t:ℕ} (h:Q10 N u t) {k:ℕ}
    (hk:1≤k) (hkt:k+1≤t):Q1e N u k≠Q1e N u (k+1):=by
 have:=h (k+1) (by omega) hkt
 rw[Nat.add_sub_cancel]at this
 exact this
lemma Qdn (N:Subgroup G) (u:ℕ→G):Q10 N u 0:=by
 intro k hk hkt
 omega
lemma Q60 {A B:Subgroup G} {z:G} (hB:z∈B) (hA:z∉A):A≠B:=by
 rintro rfl
 exact hA hB
lemma Qk3 (N:Subgroup G) {u:ℕ→G} {x y:G} (e0:u 0=x) (e1:u 1=y)
    (hxy:⁅x,y⁆∉N):Q10 N u 2:=by
 apply Q6v
 intro k hk hkt
 rw[show k=1 by omega]
 have hm:⁅u 0,u 1⁆∈Q1e N u (1+1):=Q2a N u (by norm_num) (by norm_num)
 have h1:Q1e N u 1≤N:=Q6l N le_rfl fun a b hab hb=>by
   exfalso
   omega
 rw[e0,e1]at hm
 exact Q60 hm fun h=>hxy (h1 h)
lemma Qh7 (N:Subgroup G) {u u':ℕ→G} {t a:ℕ} {v:G}
    (hu:Q10 N u t) (ha:a<t)
    (e1:∀ i<t,u' i=u i) (e2:u' t=v) (hv:⁅u a,v⁆∉Q1e N u t):
    Q10 N u' (t+1):=by
 have hW:∀ k≤t,Q1e N u' k=Q1e N u k:= fun k hk=>
   Qhq N fun i hi=>e1 i (by omega)
 apply Q6v
 intro k hk hkt
 rcases Nat.lt_or_ge k t with hkt' | hkt'
 · rw[hW k (by omega),hW (k+1) (by omega)]
   exact hu.Q7e hk (by omega)
 · rw[show k=t by omega,hW t le_rfl]
   have hm:⁅u' a,u' t⁆∈Q1e N u' (t+1):=Q2a N u' ha (by omega)
   rw[e1 a ha,e2]at hm
   exact Q60 hm hv
lemma Qeh (N:Subgroup G) {u u':ℕ→G} {s:ℕ} {w y:G}
    (hu:Q10 N u (s+1))
    (hcw:∀ a<s,⁅u a,w⁆∈Q1e N u (s+1))
    (e1:∀ i<s,u' i=u i) (e2:u' s=w) (e3:u' (s+1)=y)
    (hw1:∃ a<s,⁅u a,w⁆∉Q1e N u s) (hw2:⁅w,y⁆∉Q1e N u (s+1)):
    Q10 N u' (s+1+1):=by
 have hW:∀ k≤ s,Q1e N u' k=Q1e N u k:= fun k hk=>
   Qhq N fun i hi=>e1 i (by omega)
 have hle:Q1e N u' (s+1)≤Q1e N u (s+1):=by
  refine Q6l N (Q3t N u (s+1)) ?_
  intro a b hab hb
  by_cases hbs:b<s
  · rw[e1 a (by omega),e1 b hbs]
    exact Q2a N u hab (by omega)
  · rw[show b=s by omega,e1 a (by omega),e2]
    exact hcw a (by omega)
 apply Q6v
 intro k hk hkt
 by_cases hks:k<s
 · rw[hW k (by omega),hW (k+1) (by omega)]
   exact hu.Q7e hk (by omega)
 · by_cases hk':k=s
   · rw[hk']
     obtain ⟨a,ha,hna⟩:=hw1
     have hm:⁅u' a,u' s⁆∈Q1e N u' (s+1):=Q2a N u' ha (by omega)
     rw[e1 a ha,e2]at hm
     rw[hW s le_rfl]
     exact Q60 hm hna
   · rw [show k=s+1 by omega]
     have hm:⁅u' s,u' (s+1)⁆∈Q1e N u' (s+1+1):=
       Q2a N u' (by omega) (by omega)
     rw[e2,e3]at hm
     exact Q60 hm fun h=>hw2 (hle h)
lemma Qal (N:Subgroup G) (hN:lcs G 2≤N) {H:Subgroup G} {u:ℕ→G} {t:ℕ}
    (ht:2≤t) (hu:Q10 N u t) (huH:∀ i<t,u i∈H) {x y:G}
    (hx:x∈H) (hy:y∈H) (hxy:⁅x,y⁆∉Q1e N u t):
    ∃ u':ℕ→G,Q10 N u' (t+1)∧∀ i<t+1,u' i∈H:=by
 by_cases hc:∃ a<t,∃ v∈H,⁅u a,v⁆∉Q1e N u t
 · obtain ⟨a,ha,v,hv,hav⟩:=hc
   refine ⟨fun i=>if i<t then u i else v,?_,?_⟩
   · refine Qh7 N (u':= fun i=>if i<t then u i else v) hu ha ?_ ?_ hav
     · intro i hi
       exact if_pos hi
     · show (if t<t then u t else v)=v
       exact if_neg (lt_irrefl t)
   · intro i hi
     show (if i<t then u i else v)∈H
     by_cases h:i<t
     · rw[if_pos h]
       exact huH i h
     · rw[if_neg h]
       exact hv
 · have hc':∀ a<t,∀ v∈H,⁅u a,v⁆∈Q1e N u t:= fun a ha v hv=>by
     by_contra hn
     exact hc ⟨a,ha,v,hv,hn⟩
   obtain ⟨s,rfl⟩:∃ s,t=s+1:=⟨t - 1,by omega⟩
   obtain ⟨a0,ha0,hna0⟩:=
     Q8y N (hu.Q7e (k:=s) (by omega) le_rfl)
   have hw :∃ w∈H,(∃ a<s,⁅u a,w⁆∉Q1e N u s)∧⁅w,y⁆∉Q1e N u (s+1):=by
    by_cases hx':∃ a<s,⁅u a,x⁆∉Q1e N u s
    · exact ⟨x,hx,hx',hxy⟩
    · refine ⟨u s*x,H.mul_mem (huH s (by omega)) hx,⟨a0,ha0,?_⟩,?_⟩
      · have hax:⁅u a0,x⁆∈Q1e N u s:=by
          by_contra hn
          exact hx' ⟨a0,ha0,hn⟩
        rw[Q9c (hN.trans (Q3t N u s)) hax]
        exact hna0
      · rw[Qaw (hN.trans (Q3t N u (s+1))) (hc' s (by omega) y hy)]
        exact hxy
   obtain ⟨w,hwH,hw1,hw2⟩:=hw
   refine ⟨fun i=>if i<s then u i else if i=s then w else y,?_,?_⟩
   · refine Qeh N (u':= fun i=>if i<s then u i else if i=s then w else y)
       hu (fun a ha=>hc' a (by omega) w hwH) ?_ ?_ ?_ hw1 hw2
     · intro i hi
       exact if_pos hi
     · show (if s<s then u s else if s=s then w else y)=w
       rw[if_neg (lt_irrefl s),if_pos rfl]
     · show (if s+1<s then u (s+1) else if s+1=s then w else y)=y
       rw[if_neg (show ¬ (s+1<s) by omega),if_neg (show ¬ (s+1=s) by omega)]
   · intro i hi
     show (if i<s then u i else if i=s then w else y)∈H
     by_cases h1:i<s
     · rw[if_pos h1]
       exact huH i (by omega)
     · rw [if_neg h1]
       by_cases h2:i=s
       · rw[if_pos h2]
         exact hwH
       · rw[if_neg h2]
         exact hy
lemma Qbx (N M:Subgroup G) (hN3:lcs G 2≤N) (hN2:N≤lcs G 1)
    (hMN:∀ g m:G,m∈M→⁅g,m⁆∈N) (u:ℕ→G) (t:ℕ) (h:Q10 N u t)
    (ht:2≤t):∀ k<t,u k∉ZA (u '' ZP k)⊔M:=by
 intro k hk hmem
 rcases Nat.eq_zero_or_pos k with hk0 | hk0
 · subst hk0
   have hle:ZA (u '' ZP 0)⊔M≤M:=by
    refine sup_le ?_ le_rfl
    rw[ZD]
    rintro _ ⟨i,hi,rfl⟩
    exact absurd (Set.mem_Iio.mp hi) (Nat.not_lt_zero i)
   have h0:u 0∈M:=hle hmem
   refine h.Q7e (k:=1) le_rfl (by omega)
     (le_antisymm (Qbv N u (show 1≤1+1 by omega)) (Qaj N ?_))
   intro a ha
   obtain rfl:a=0:=by omega
   exact Q3t N u 1 (Qr (hMN (u 1) (u 0) h0))
 · haveI :=Ql7 N hN3 hN2 u k
   refine h.Q7e (k:=k) (by omega) (by omega)
     (le_antisymm (Qbv N u (show k≤k+1 by omega)) (Qaj N ?_))
   intro a ha
   have hle:ZA (u '' ZP k)⊔M≤zn (Q1e N u k) (u a):=by
    refine sup_le ?_ ?_
    · rw [ZD]
      rintro _ ⟨b,hb,rfl⟩
      rw[SetLike.mem_coe,Q4p]
      rcases lt_trichotomy a b with hab | hab | hab
      · exact Q2a N u hab (Set.mem_Iio.mp hb)
      · rw[hab,commutatorElement_self]
        exact (Q1e N u k).one_mem
      · exact Qr (Q2a N u hab ha)
    · intro z hz
      exact Q4p.mpr (Q3t N u k (hMN (u a) z hz))
   exact Q4p.mp (hle hmem)
lemma Qjj (a b k k':G):a*k*(b*k')=a*b*(b⁻¹*k*b⁻¹⁻¹*k'):=by
 group
lemma Qiw (a k:G):(a*k)⁻¹=a⁻¹*(a*k⁻¹*a⁻¹):=by
 group
def Qns (K:Subgroup G) [hK:K.Normal] (x:G):Subgroup G where
  carrier :={g | ∃ e:ℤ,∃ k∈K,g=x^e *k}
  one_mem':=by
    show ∃ e:ℤ,∃ k∈K,(1:G)=x^e *k
    exact ⟨0,1,K.one_mem,by simp⟩
  mul_mem':=by
    rintro _ _ ⟨e,k,hk,rfl⟩ ⟨f,k',hk',rfl⟩
    show ∃ e':ℤ,∃ k''∈K,x^e *k*(x^f*k')=x^e'*k''
    refine ⟨e+f,(x^f)⁻¹*k*(x^f)⁻¹⁻¹*k',
      K.mul_mem (hK.conj_mem k hk _) hk',?_⟩
    rw[zpow_add]
    exact Qjj _ _ _ _
  inv_mem':=by
    rintro _ ⟨e,k,hk,rfl⟩
    show ∃ e':ℤ,∃ k''∈K,(x^e *k)⁻¹=x^e'*k''
    refine ⟨-e,x^e *k⁻¹*(x^e)⁻¹,hK.conj_mem _ (K.inv_mem hk) _,?_⟩
    rw[zpow_neg]
    exact Qiw _ _
lemma Qev {K:Subgroup G} [K.Normal] {x g:G}:
    g∈Qns K x↔∃ e:ℤ,∃ k∈K,g=x^e *k:=Iff.rfl
lemma Qah {K:Subgroup G} [K.Normal] {x:G} {p:ℕ} (hp:0<p)
    (hx:x^p∈K) {g:G} (hg:g∈K⊔Subgroup.zpowers x):
    ∃ e:ℕ,e<p∧∃ k∈K,g=x^e *k:=by
 have hle:K⊔Subgroup.zpowers x≤Qns K x:=by
  refine sup_le (fun k hk=>Qev.mpr ⟨0,k,hk,by simp⟩) ?_
  rw[Subgroup.zpowers_le]
  exact Qev.mpr ⟨1,1,K.one_mem,by simp⟩
 obtain ⟨e,k,hk,rfl⟩:=Qev.mp (hle hg)
 have hp':(0:ℤ)<p:=by exact_mod_cast hp
 obtain ⟨r,hr⟩:=Int.eq_ofNat_of_zero_le (Int.emod_nonneg e hp'.ne')
 have hrp:r<p:=by
  have:=Int.emod_lt_of_pos e hp'
  rw[hr]at this
  exact_mod_cast this
 refine ⟨r,hrp,(x^p)^(e/(p:ℤ))*k,K.mul_mem (zpow_mem hx _) hk,?_⟩
 have he:e=(r :ℤ)+(p:ℤ)*(e/(p:ℤ)):=by
  rw[← hr]
  have:=Int.emod_add_mul_ediv e (p:ℤ)
  linarith
 calc x^e *k=x^((r :ℤ)+(p:ℤ)*(e/(p:ℤ)))*k:=by rw[← he]
   _ =x^r*((x^p)^(e/(p:ℤ))*k):=by
     rw[zpow_add,zpow_mul,zpow_natCast,zpow_natCast,mul_assoc]
variable [Finite G]
lemma Q79 {K:Subgroup G} [K.Normal] {x:G} {p:ℕ} (hp:0<p)
    (hx:x^p∈K):ZB (K⊔Subgroup.zpowers x:Subgroup G)≤p*ZB K:=by
 have hmem:∀ q:Fin p×K,x^(q.1:ℕ)*(q.2:G)∈K⊔Subgroup.zpowers x:=
   fun q=>mul_mem (pow_mem (ZL (Subgroup.mem_zpowers x)) _)
     (ZJ q.2.2)
 let f:Fin p×K→(K⊔Subgroup.zpowers x:Subgroup G):= fun q=> ⟨_,hmem q⟩
 have hf:Function.Surjective f:=by
  rintro ⟨g,hg⟩
  obtain ⟨e,he,k,hk,rfl⟩:=Qah hp hx hg
  exact ⟨(⟨e,he⟩,⟨k,hk⟩),rfl⟩
 have h:=Nat.card_le_card_of_surjective f hf
 rwa[Nat.card_prod,(Nat.card_eq_fintype_card:ZB (Fin p)=Fintype.card (Fin p)),
   Fintype.card_fin]at h
variable {p n:ℕ}
lemma Qc1 (hp:p.Prime) (hG:ZB G=p^n) {K L:Subgroup G} (hle:K≤L)
    (hne:K≠L):p*ZB K≤ZB L:=by
 have h2:ZB L∣p^n:=by
  rw[← hG]
  exact Subgroup.card_subgroup_dvd_card L
 have h1:ZB K∣ZB L:=Subgroup.card_dvd_of_le hle
 obtain ⟨b, -,hb⟩:=(Nat.dvd_prime_pow hp).mp h2
 obtain ⟨a, -,ha⟩:=(Nat.dvd_prime_pow hp).mp (h1.trans h2)
 have hab:a≤b:=by
  rw[ha,hb]at h1
  exact (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp h1
 have hab':a≠b:=by
  rintro rfl
  exact hne (Subgroup.eq_of_le_of_card_ge hle (by rw[ha,hb]))
 rw[ha,hb, ← pow_succ']
 exact Nat.pow_le_pow_right hp.pos (by omega)
lemma Q76 (hp:0<p) {M:Subgroup G} (hM2:lcs G 1≤M)
    (hMp:∀ g:G,g^p∈M) (x:ℕ→G):
    ∀ j,ZB (ZA (x '' ZP j)⊔M:Subgroup G)≤p^j*ZB M:=by
 intro j
 induction j with
 | zero=>
   have hle:ZA (x '' ZP 0)⊔M≤M:=by
    refine sup_le ?_ le_rfl
    rw[ZD]
    rintro _ ⟨i,hi,rfl⟩
    exact absurd (Set.mem_Iio.mp hi) (Nat.not_lt_zero i)
   rw[pow_zero,one_mul]
   exact Subgroup.card_le_of_le hle
 | succ j ih=>
   have:(ZA (x '' ZP j)⊔M).Normal:=
     Q6r (hM2.trans le_sup_right)
   have hle:ZA (x '' ZP (j+1))⊔M≤
       (ZA (x '' ZP j)⊔M)⊔Subgroup.zpowers (x j):=by
    refine sup_le ?_ (le_sup_right.trans le_sup_left)
    rw[ZD]
    rintro _ ⟨i,hi,rfl⟩
    have hi':i<j+1:=Set.mem_Iio.mp hi
    by_cases hij:i<j
    · exact ZJ (ZJ
        (ZC ⟨i,Set.mem_Iio.mpr hij,rfl⟩))
    · rw[show i=j by omega]
      exact ZL (Subgroup.mem_zpowers (x j))
   have h1:=Subgroup.card_le_of_le hle
   have h2:=Q79 (K:=ZA (x '' ZP j)⊔M) hp
     (ZL (hMp (x j)))
   have h3:p*ZB (ZA (x '' ZP j)⊔M:Subgroup G)≤
       p*(p^j*ZB M):=Nat.mul_le_mul le_rfl ih
   have e:p*(p^j*ZB M)=p^(j+1)*ZB M:=by
    rw[pow_succ]
    ring
   rw[← e]
   exact h1.trans (h2.trans h3)
lemma Qa2 (hp:p.Prime) (hG:ZB G=p^n) (M:Subgroup G) {v:ℕ→G}:
    ∀ t,(∀ k<t,v k∉ZA (v '' ZP k)⊔M)→
      p^t *ZB M≤ZB (ZA (v '' ZP t)⊔M:Subgroup G):=by
 intro t
 induction t with
 | zero=>
   intro _
   rw[pow_zero,one_mul]
   exact Subgroup.card_le_of_le le_sup_right
 | succ t ih=>
   intro hind
   have h1:=ih fun k hk=>hind k (by omega)
   have hle:ZA (v '' ZP t)⊔M≤ZA (v '' ZP (t+1))⊔M:=
     sup_le_sup_right (ZO
       (Set.image_mono (Set.Iio_subset_Iio (Nat.le_succ t)))) M
   have hne:ZA (v '' ZP t)⊔M≠
       ZA (v '' ZP (t+1))⊔M:=by
    intro h
    apply hind t (Nat.lt_succ_self t)
    rw[h]
    exact ZJ
      (ZC ⟨t,Set.mem_Iio.mpr (Nat.lt_succ_self t),rfl⟩)
   have h2:=Qc1 hp hG hle hne
   have h3:p*(p^t *ZB M)≤
       p*ZB (ZA (v '' ZP t)⊔M:Subgroup G):=Nat.mul_le_mul le_rfl h1
   have e:p*(p^t *ZB M)=p^(t+1)*ZB M:=by
    rw[pow_succ]
    ring
   rw[← e]
   exact h3.trans h2
lemma Qfq (hp:p.Prime) (hG:ZB G=p^n) {M:Subgroup G}
    (hM2:lcs G 1≤M) (hMp:∀ g:G,g^p∈M) (x:ℕ→G) (s:ℕ) {v:ℕ→G} {t:ℕ}
    (hind:∀ k<t,v k∉ZA (v '' ZP k)⊔M)
    (hvH:∀ i<t,v i∈ZA (x '' ZP s)):t≤ s:=by
 have h1:=Qa2 hp hG M t hind
 have h2:ZB (ZA (v '' ZP t)⊔M:Subgroup G)≤
     ZB (ZA (x '' ZP s)⊔M:Subgroup G):=by
  refine Subgroup.card_le_of_le (sup_le ?_ le_sup_right)
  rw[ZD]
  rintro _ ⟨i,hi,rfl⟩
  exact ZJ (hvH i (Set.mem_Iio.mp hi))
 have h3:=Q76 hp.pos hM2 hMp x s
 have hc:0<ZB M:=Nat.card_pos
 by_contra hts
 have h4:p^(s+1)≤p^t:=Nat.pow_le_pow_right hp.pos (by omega)
 have h6:0<p^s:=pow_pos hp.pos s
 rw[pow_succ]at h4
 have h7:p^s*p*ZB M≤p^t *ZB M:=Nat.mul_le_mul h4 le_rfl
 have h8:p^s*2*ZB M≤p^s*p*ZB M:=
   Nat.mul_le_mul (Nat.mul_le_mul le_rfl hp.two_le) le_rfl
 have h9:0<p^s*ZB M:=Nat.mul_pos h6 hc
 linarith
lemma Qg5 (hp:p.Prime) (hG:ZB G=p^n) (N:Subgroup G) {u:ℕ→G}
    {t:ℕ} (hu:Q10 N u t):
    ∀ k,1≤k→k≤t→p^(k - 1)*ZB N≤ZB (Q1e N u k):=by
 intro k
 induction k with
 | zero=>intro hk _; omega
 | succ j ih=>
   intro _ hkt
   rcases Nat.eq_zero_or_pos j with hj | hj
   · subst hj
     rw[show 0+1 - 1=0 by omega,pow_zero,one_mul]
     exact Subgroup.card_le_of_le (Q3t N u 1)
   · obtain ⟨i,rfl⟩:∃ i,j=i+1:=⟨j - 1,by omega⟩
     have h1:=ih (by omega) (by omega)
     rw[show i+1 - 1=i by omega]at h1
     have h2:=Qc1 hp hG (Qbv N u (show i+1≤ i+1+1 by omega))
       (hu.Q7e (k:=i+1) (by omega) hkt)
     rw[show i+1+1 - 1=i+1 by omega,pow_succ']
     have h3:p*(p^i*ZB N)≤p*ZB (Q1e N u (i+1)):=
       Nat.mul_le_mul le_rfl h1
     rw[mul_assoc]
     exact h3.trans h2
omit [Finite G] in
lemma Q4u {N H W:Subgroup G} (hcore:lcs G 1≤⁅H,H⁆⊔N) (hNW:N≤W)
    (hW:¬ lcs G 1≤W):∃ x∈H,∃ y∈H,⁅x,y⁆∉W:=by
 by_contra hc
 apply hW
 refine hcore.trans (sup_le ?_ hNW)
 rw[Subgroup.commutator_le]
 intro x hx y hy
 by_contra hn
 exact hc ⟨x,hx,y,hy,hn⟩
lemma Qlv (hp:p.Prime) (hG:ZB G=p^n) (N M:Subgroup G)
    (hN3:lcs G 2≤N) (hN2:N≤lcs G 1) (hM2:lcs G 1≤M) (hMp:∀ g:G,g^p∈M)
    (hMN:∀ g m:G,m∈M→⁅g,m⁆∈N) (s:ℕ) (x:ℕ→G)
    (hcore:lcs G 1≤
      ⁅ZA (x '' ZP s),ZA (x '' ZP s)⁆⊔N)
    (hmin:∀ t<s,∀ v:ℕ→G,(∀ i<t,v i∈ZA (x '' ZP s))→
      ¬ lcs G 1≤⁅ZA (v '' ZP t),ZA (v '' ZP t)⁆⊔N):
    ∃ u:ℕ→G,(∀ i<s,u i∈ZA (x '' ZP s))∧
      Q10 N u s∧Q1e N u s=lcs G 1∧
      (∀ k<s,u k∉ZA (u '' ZP k)⊔M)∧
      ZA (u '' ZP s)⊔M=ZA (x '' ZP s)⊔M∧
      (∀ k,1≤k→k≤ s→p^(k - 1)*ZB N≤ZB (Q1e N u k)):=by
 have hHH:s≤1→
     ⁅ZA (x '' ZP s),ZA (x '' ZP s)⁆≤N:=by
  intro hs1
  have:=Q1d (n:=1) hN3 hN2
  apply Q2o
  rintro _ ⟨i,hi,rfl⟩ _ ⟨j,hj,rfl⟩
  have hi':i<s:=Set.mem_Iio.mp hi
  have hj':j<s:=Set.mem_Iio.mp hj
  obtain rfl:i=0:=by omega
  obtain rfl:j=0:=by omega
  rw[commutatorElement_self]
  exact N.one_mem
 rcases (show s=0∨s=1∨2≤ s by omega) with hs | hs | hs
 · subst hs
   refine ⟨x,fun i hi=>absurd hi (Nat.not_lt_zero i),Qdn N x,?_,
     fun k hk=>absurd hk (Nat.not_lt_zero k),rfl,fun k hk hks=>absurd hks (by omega)⟩
   exact le_antisymm (Q7b N hN2 x 0)
     (hcore.trans (sup_le ((hHH (by omega)).trans (Q3t N x 0)) (Q3t N x 0)))
 · subst hs
   exfalso
   exact hmin 0 (by omega) x (fun i hi=>absurd hi (Nat.not_lt_zero i))
     ((hcore.trans (sup_le (hHH le_rfl) le_rfl)).trans le_sup_right)
 · have stepA:∀ j,j+2≤ s→∃ u:ℕ→G,Q10 N u (j+2)∧
       ∀ i<j+2,u i∈ZA (x '' ZP s):=by
     intro j
     induction j with
     | zero =>
       intro hs2
       have h0:¬ lcs G 1≤N:= fun h=>
         hmin 0 (by omega) x (fun i hi=>absurd hi (Nat.not_lt_zero i)) (h.trans le_sup_right)
       obtain ⟨a,ha,b,hb,hab⟩:=Q4u hcore le_rfl h0
       refine ⟨fun i=>if i=0 then a else b,?_,?_⟩
       · refine Qk3 N (u:= fun i=>if i=0 then a else b) ?_ ?_ hab
         · show (if (0:ℕ)=0 then a else b)=a
           exact if_pos rfl
         · show (if (1:ℕ)=0 then a else b)=b
           exact if_neg (by norm_num)
       · intro i hi
         show (if i=0 then a else b)∈ZA (x '' ZP s)
         by_cases h:i=0
         · rw[if_pos h]
           exact ha
         · rw[if_neg h]
           exact hb
     | succ j ih=>
       intro hs2
       obtain ⟨u,hu,huH⟩:=ih (by omega)
       have hnc:¬ lcs G 1≤Q1e N u (j+2):= fun h=>
         hmin (j+2) (by omega) u huH (h.trans (Qk4 N u (j+2)))
       obtain ⟨a,ha,b,hb,hab⟩:=Q4u hcore (Q3t N u _) hnc
       obtain ⟨u',hu',hu'H⟩:=Qal N hN3 (by omega) hu huH ha hb hab
       rw[show j+1+2=j+2+1 by omega]
       exact ⟨u',hu',hu'H⟩
   obtain ⟨u,hu,huH⟩:=stepA (s - 2) (by omega)
   rw[show s - 2+2=s by omega]at hu huH
   have hge:lcs G 1≤Q1e N u s:=by
    by_contra hc
    obtain ⟨a,ha,b,hb,hab⟩:=Q4u hcore (Q3t N u s) hc
    obtain ⟨u',hu',hu'H⟩:=Qal N hN3 (by omega) hu huH ha hb hab
    have:=Qfq hp hG hM2 hMp x s
      (Qbx N M hN3 hN2 hMN u' (s+1) hu' (by omega)) hu'H
    omega
   have hind:=Qbx N M hN3 hN2 hMN u s hu (by omega)
   refine ⟨u,huH,hu,le_antisymm (Q7b N hN2 u s) hge,hind,?_,
     Qg5 hp hG N hu⟩
   have hle:ZA (u '' ZP s)⊔M≤ZA (x '' ZP s)⊔M:=by
    refine sup_le ?_ le_sup_right
    rw[ZD]
    rintro _ ⟨i,hi,rfl⟩
    exact ZJ (huH i (Set.mem_Iio.mp hi))
   refine Subgroup.eq_of_le_of_card_ge hle ?_
   exact (Q76 hp.pos hM2 hMp x s).trans (Qa2 hp hG M s hind)
end CoreFlag
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section CommForm
variable {G:Type u} [Group G]
abbrev Qv (p:ℕ) (G:Type u) [Group G]:Subgroup G:=
  ZA (ZG (fun g:G=>g^p))⊔commutator G
abbrev pN (p:ℕ) (G:Type u) [Group G]:Subgroup G:=
  lcs G 2⊔ZA (ZG (fun g:lcs G 1=> (g:G)^p))
lemma Q1s:commutator G=lcs G 1:=by
 rw[commutator_def]
 rfl
lemma Qo (x y:G):⁅x,y⁆∈lcs G 1:=
  Qb (n:=0) (ZM x) y
lemma Q1j (p:ℕ):lcs G 2≤pN p G:=le_sup_left
lemma Q3y (p:ℕ):pN p G≤lcs G 1:=by
 refine sup_le (Qd (by norm_num)) ?_
 rw[ZD]
 rintro _ ⟨g,rfl⟩
 exact Subgroup.pow_mem _ g.2 p
lemma Q7w (p:ℕ):(pN p G).Normal:=
  Q1d (n:=1) (Q1j p) (Q3y p)
lemma Qan (g y:G) (n:ℕ):⁅g^n,y⁆*(⁅g,y⁆^n)⁻¹∈lcs G 2:=by
 induction n with
 | zero=>simp
 | succ n ih=>
   have hc:⁅g,⁅g^n,y⁆⁆∈lcs G 2:=
     Qj (n:=1) g (Qo _ _)
   have e:⁅g^(n+1),y⁆*(⁅g,y⁆^(n+1))⁻¹=
       ⁅g,⁅g^n,y⁆⁆*(⁅g^n,y⁆*(⁅g,y⁆^n)⁻¹):=by
    rw[pow_succ' g n,Q2g,pow_succ]
    group
   rw[e]
   exact Subgroup.mul_mem _ hc ih
lemma Q8q (p:ℕ) (g y:G):⁅g^p,y⁆∈pN p G:=by
 have h1:=Q1j p (Qan g y p)
 have h2:⁅g,y⁆^p∈pN p G:=by
  refine (le_sup_right:_≤pN p G) (ZC ?_)
  exact ⟨⟨⁅g,y⁆,Qo g y⟩,rfl⟩
 have e:⁅g^p,y⁆=⁅g^p,y⁆*(⁅g,y⁆^p)⁻¹*⁅g,y⁆^p:=by group
 rw[e]
 exact Subgroup.mul_mem _ h1 h2
lemma Q8f (p:ℕ) {φ:G} (hφ:φ∈Qv p G) (y:G):⁅φ,y⁆∈pN p G:=by
 haveI:=Q7w (G:=G) p
 suffices h:Qv p G≤zn (pN p G) y from Qr (h hφ)
 refine sup_le ?_ ?_
 · rw[ZD]
   rintro _ ⟨g,rfl⟩
   exact Qr (Q8q p g y)
 · intro c hc
   rw[Q1s]at hc
   exact Q1j p (Qj (n:=1) y hc)
lemma Q8u (p:ℕ) (x x' y:G)
    (h:x'*x⁻¹∈ZA (ZG (fun g:G=>g^p))⊔commutator G):
    ⁅x',y⁆*⁅x,y⁆⁻¹∈
      lcs G 2⊔ZA (ZG (fun g:lcs G 1=> (g:G)^p)):=by
  haveI:=Q7w (G:=G) p
  obtain ⟨φ,hφ,rfl⟩:∃ φ∈Qv p G,x'=φ*x:=⟨x'*x⁻¹,h,by group⟩
  have h1:⁅φ,⁅x,y⁆⁆∈pN p G:=
    Q1j p (Qj (n:=1) φ (Qo _ _))
  have h2:⁅x,y⁆*⁅φ,y⁆*⁅x,y⁆⁻¹∈pN p G:=
    (Q7w (G:=G) p).conj_mem _ (Q8f p hφ y) _
  have e:⁅φ*x,y⁆*⁅x,y⁆⁻¹=⁅φ,⁅x,y⁆⁆*(⁅x,y⁆*⁅φ,y⁆*⁅x,y⁆⁻¹):=by
   rw[Q2g]
   group
  rw[e]
  exact Subgroup.mul_mem _ h1 h2
lemma Qdr (p:ℕ) (x y y':G)
    (h:y'*y⁻¹∈ZA (ZG (fun g:G=>g^p))⊔commutator G):
    ⁅x,y'⁆*⁅x,y⁆⁻¹∈
      lcs G 2⊔ZA (ZG (fun g:lcs G 1=> (g:G)^p)):=by
  have hu:=Q8u p y y' x h
  have e:⁅x,y'⁆*⁅x,y⁆⁻¹=⁅y',x⁆⁻¹*(⁅y',x⁆*⁅y,x⁆⁻¹)⁻¹*⁅y',x⁆⁻¹⁻¹:=by
   rw[← commutatorElement_inv y' x, ← commutatorElement_inv y x]
   group
  rw[e]
  exact (Q7w (G:=G) p).conj_mem _ (Subgroup.inv_mem _ hu) _
lemma Qdt (p:ℕ) (x x' y:G):
    ⁅x *x',y⁆*(⁅x,y⁆*⁅x',y⁆)⁻¹∈
      lcs G 2⊔ZA (ZG (fun g:lcs G 1=> (g:G)^p)):=by
  have h1:⁅x,⁅x',y⁆⁆∈lcs G 2:=
    Qj (n:=1) x (Qo _ _)
  have h2:⁅⁅x',y⁆,⁅x,y⁆⁆∈lcs G 2:=
    Qb (n:=1) (Qo _ _) _
  have e:⁅x*x',y⁆*(⁅x,y⁆*⁅x',y⁆)⁻¹=⁅x,⁅x',y⁆⁆*⁅⁅x',y⁆,⁅x,y⁆⁆:=by
   rw[Q2g]
   simp only[commutatorElement_def]
   group
  rw[e]
  exact Q1j p (Subgroup.mul_mem _ h1 h2)
lemma Qd8 (p:ℕ) (x y y':G):
    ⁅x,y *y'⁆*(⁅x,y⁆*⁅x,y'⁆)⁻¹∈
      lcs G 2⊔ZA (ZG (fun g:lcs G 1=> (g:G)^p)):=by
  have h1:⁅y,⁅x,y'⁆⁆∈lcs G 2:=
    Qj (n:=1) y (Qo _ _)
  have e:⁅x,y *y'⁆*(⁅x,y⁆*⁅x,y'⁆)⁻¹=
      ⁅x,y⁆*⁅y,⁅x,y'⁆⁆*⁅x,y⁆⁻¹:=by
   rw[Q33]
   group
  rw[e]
  exact (Q7w (G:=G) p).conj_mem _ (Q1j p h1) _
lemma Qi2 (p:ℕ):
    lcs G 1≤ZA (ZG (fun xy:G×G=> ⁅xy.1,xy.2⁆))⊔
      (lcs G 2⊔ZA (ZG (fun g:lcs G 1=> (g:G)^p))):=by
  show ⁅lcs G 0,⊤⁆≤_
  rw[Subgroup.commutator_le]
  intro a _ b _
  exact ZJ (ZC ⟨(a,b),rfl⟩)
end CommForm
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section BurnsideGeneral
variable {G:Type u} [Group G]
lemma Q9e {H:Subgroup G} (h:commutator G≤H):H.Normal:=
  ⟨fun n hn g=>by
    have hc:⁅g,n⁆∈H:=h (by
     rw[commutator_def]
     exact Subgroup.commutator_mem_commutator (ZM g) (ZM n))
    have e:g*n*g⁻¹=⁅g,n⁆*n:=by
     rw[commutatorElement_def]
     group
    rw[e]
    exact H.mul_mem hc hn⟩
lemma Qca {M:Subgroup G} [M.Normal] (hM:IsCoatom M) (x:G⧸M):
    x =1∨Subgroup.zpowers x =⊤:=by
 obtain ⟨g,rfl⟩:=QuotientGroup.mk_surjective x
 obtain ⟨K,hK⟩:∃ K:Subgroup G,
     K=Subgroup.comap (ZF M) (Subgroup.zpowers (g:G⧸M)):=⟨_,rfl⟩
 have hMK:M≤K:=by
  intro m hm
  rw[hK,Subgroup.mem_comap,QuotientGroup.mk'_apply,(QuotientGroup.eq_one_iff m).mpr hm]
  exact Subgroup.one_mem _
 have hgK:g∈K:=by
  rw[hK,Subgroup.mem_comap,QuotientGroup.mk'_apply]
  exact Subgroup.mem_zpowers _
 rcases eq_or_lt_of_le hMK with h | h
 · left
   rw[QuotientGroup.eq_one_iff,h]
   exact hgK
 · right
   have hKt:=hM.2 K h
   rw[eq_top_iff]
   intro y _
   obtain ⟨y,rfl⟩:=QuotientGroup.mk_surjective y
   have hy:y∈K:=by
    rw[hKt]
    exact ZM y
   rw[hK,Subgroup.mem_comap,QuotientGroup.mk'_apply]at hy
   exact hy
lemma Q2c (p:ℕ) (y:G):y^p∈Qv p G:=
  ZJ (ZC ⟨y,rfl⟩)
abbrev Qm4 (G:Type u) [Group G]:Subgroup (Abelianization G):=
  (frattini G).map ZH
abbrev Q2r (G:Type u) [Group G]:Type u:=Abelianization G⧸Qm4 G
def Q12 (G:Type u) [Group G]:G→*Q2r G:=
  (ZF (Qm4 G)).comp ZH
lemma Q3f:Function.Surjective (Q12 G):=by
 intro x
 obtain ⟨a,rfl⟩:=QuotientGroup.mk_surjective x
 obtain ⟨g,hg⟩:=QuotientGroup.mk_surjective (a:G⧸commutator G)
 refine ⟨g,?_⟩
 rw[← hg]
 rfl
end BurnsideGeneral
section Burnside
variable {p:ℕ} [hp:Fact p.Prime] {G:Type u} [Group G] [Finite G]
lemma Qid (hG:IsPGroup p G) {M:Subgroup G} (hM:IsCoatom M):M.Normal:=by
 have:=hG.isNilpotent
 exact Subgroup.NormalizerCondition.normal_of_coatom M Group.normalizerCondition_of_isNilpotent hM
lemma Qhc (hG:IsPGroup p G) {M:Subgroup G} (hM:IsCoatom M):
    Qv p G≤M:=by
 have:=Qid hG hM
 have hQ:IsPGroup p (G⧸M):=hG.to_quotient M
 have hnt:ZB (G⧸M)≠1:=by
  intro h1
  apply hM.1
  rw[← Subgroup.index_eq_one]
  exact h1
 have hdvd:p∣ZB (G⧸M):=hQ.card_eq_or_dvd.resolve_left hnt
 obtain ⟨x,hx⟩:=exists_prime_orderOf_dvd_card' p hdvd
 have hx1:x≠1:=by
  intro h
  rw[h,orderOf_one]at hx
  exact hp.out.one_lt.ne hx
 have hxt:Subgroup.zpowers x =⊤:=(Qca hM x).resolve_left hx1
 have hcard:ZB (G⧸M)=p:=by
  rw[← hx, ← Nat.card_zpowers,hxt,Subgroup.card_top]
 have hcomm:∀ a b:G⧸M,a*b=b*a:=by
  intro a b
  have ha:a∈Subgroup.zpowers x:=by
   rw[hxt]
   exact ZM a
  have hb:b∈Subgroup.zpowers x:=by
   rw[hxt]
   exact ZM b
  obtain ⟨i,rfl⟩:=Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨j,rfl⟩:=Subgroup.mem_zpowers_iff.mp hb
  exact (Commute.zpow_zpow_self x i j).eq
 refine sup_le ?_ ?_
 · rw[ZD]
   rintro _ ⟨g,rfl⟩
   rw[SetLike.mem_coe, ← QuotientGroup.eq_one_iff,QuotientGroup.mk_pow, ← hcard]
   exact pow_card_eq_one'
 · rw[commutator_def,Subgroup.commutator_le]
   intro a _ b _
   have e:=map_commutatorElement (ZF M) a b
   simp only[QuotientGroup.mk'_apply]at e
   rw[← QuotientGroup.eq_one_iff,e,commutatorElement_eq_one_iff_mul_comm]
   exact hcomm _ _
lemma Qb9 {g:G} (hg:g∉Qv p G):
    ∃ H:Subgroup G,IsCoatom H∧g∉H:=by
 have:Finite (Subgroup G):=
   Finite.of_injective (fun H:Subgroup G=> (H:Set G)) SetLike.coe_injective
 obtain ⟨H,⟨hPH,hgH⟩,hmax⟩:=(wellFounded_gt (α:=Subgroup G)).has_min
   {H:Subgroup G | Qv p G≤H∧g∉H} ⟨Qv p G,le_rfl,hg⟩
 have key:∀ K:Subgroup G,H<K→ g∈K:=by
  intro K hK
  by_contra hgK
  exact hmax K ⟨hPH.trans hK.le,hgK⟩ hK
 have:H.Normal:=Q9e (le_sup_right.trans hPH)
 refine ⟨H,⟨fun h=>hgH (by rw[h]; exact ZM g),fun K hK=>?_⟩,hgH⟩
 rw[eq_top_iff]
 intro y _
 by_cases hyH:y∈H
 · exact hK.le hyH
 · have hlt:H<H⊔Subgroup.zpowers y:=by
     refine lt_of_le_of_ne le_sup_left (fun h=>hyH ?_)
     rw[h]
     exact ZL (Subgroup.mem_zpowers y)
   have hgs:=key _ hlt
   rw[Subgroup.mem_sup_of_normal_left]at hgs
   obtain ⟨h,hh,z,hz,hhz⟩:=hgs
   obtain ⟨k,rfl⟩:=Subgroup.mem_zpowers_iff.mp hz
   have hgK:=key K hK
   by_cases hpk:(p:ℤ)∣k
   · exfalso
     obtain ⟨m,rfl⟩:=hpk
     apply hgH
     rw[← hhz]
     refine H.mul_mem hh (hPH ?_)
     rw[zpow_mul,zpow_natCast]
     exact Subgroup.zpow_mem _ (Q2c p y) m
   · have hyk:y^k∈K:=by
       have e:y^k=h⁻¹*g:=by
        rw[← hhz]
        group
       rw[e]
       exact K.mul_mem (K.inv_mem (hK.le hh)) hgK
     have hyp:y^(p:ℤ)∈K:=by
      rw[zpow_natCast]
      exact hK.le (hPH (Q2c p y))
     have hcop:Int.gcd k (p:ℤ)=1:=by
      have hnd:¬ p∣k.natAbs:= fun h'=>hpk (Int.ofNat_dvd_left.mpr h')
      have hc:Nat.Coprime p k.natAbs:=(Nat.Prime.coprime_iff_not_dvd hp.out).mpr hnd
      exact hc.symm
     have e:y=(y^k)^(Int.gcdA k (p:ℤ))*(y^(p:ℤ))^(Int.gcdB k (p:ℤ)):=by
      rw[← zpow_mul, ← zpow_mul, ← zpow_add, ← Int.gcd_eq_gcd_ab,hcop,Nat.cast_one,zpow_one]
     rw[e]
     exact K.mul_mem (K.zpow_mem hyk _) (K.zpow_mem hyp _)
lemma Q1n (hG:IsPGroup p G):frattini G=Qv p G:=by
 apply le_antisymm
 · intro g hg
   by_contra hgn
   obtain ⟨H,hH,hgH⟩:=Qb9 hgn
   exact hgH (frattini_le_coatom hH hg)
 · show Qv p G≤ ⨅ a∈{H:Subgroup G | IsCoatom H},a
   exact le_iInf₂ fun M hM=>Qhc hG hM
lemma Qfw (hG:IsPGroup p G):(Q12 G).ker= frattini G:=by
 have hc:commutator G≤frattini G:=by
  rw[Q1n hG]
  exact le_sup_right
 rw [Q12, ← MonoidHom.comap_ker,QuotientGroup.ker_mk',Subgroup.comap_map_eq,
   Abelianization.ker_of,sup_eq_left.mpr hc]
lemma Q25 {s:Set G}
    (h:ZA s⊔frattini G=⊤):ZA s=⊤:=by
 have:Finite (Subgroup G):=
   Finite.of_injective (fun H:Subgroup G=> (H:Set G)) SetLike.coe_injective
 exact frattini_nongenerating h
lemma Q44 (hG:IsPGroup p G):
    ZB (G⧸frattini G)=p^Group.rank G:=by
 classical
 have:NeZero p:=⟨hp.out.ne_zero⟩
 have hker :=Qfw hG
 have hpow:∀ x:Additive (Q2r G),p•x =0:=by
  intro x
  obtain ⟨g,hg⟩:=Q3f (Additive.toMul x)
  have h1:Additive.toMul x^p=1:=by
   rw[← hg, ← map_pow, ← MonoidHom.mem_ker,hker,Q1n hG]
   exact Q2c p g
  show ZE (Additive.toMul x^p)=ZE 1
  rw[h1]
 have:Module (ZMod p) (Additive (Q2r G)):=AddCommGroup.zmodModule hpow
 have:Finite (Q2r G):=Finite.of_surjective (Q12 G) Q3f
 have:Finite (Additive (Q2r G)):=inferInstance
 have:Module.Free (ZMod p) (Additive (Q2r G)):=
   Module.Free.of_divisionRing (ZMod p) (Additive (Q2r G))
 have:Module.Finite (ZMod p) (Additive (Q2r G)):=inferInstance
 have hcardQ:ZB (G⧸frattini G)=ZB (Additive (Q2r G)):=by
  have e:=Nat.card_congr
    (QuotientGroup.quotientKerEquivOfSurjective (Q12 G) Q3f).toEquiv
  rw[hker]at e
  exact e
 have hcard:ZB (Additive (Q2r G))=
     p^Module.finrank (ZMod p) (Additive (Q2r G)):=by
  rw[Module.natCard_eq_pow_finrank (K:=ZMod p) (V:=Additive (Q2r G)),Nat.card_zmod]
 rw[hcardQ,hcard]
 congr 1
 apply le_antisymm
 ·
   obtain ⟨S,hSc,hS⟩:=Group.rank_spec G
   let T:Finset (Additive (Q2r G)):=S.image (fun g=>ZE (Q12 G g))
   have hspan:Submodule.span (ZMod p) (T:Set (Additive (Q2r G)))=⊤:=by
    rw[Submodule.eq_top_iff']
    intro v
    obtain ⟨g,hg⟩:=Q3f (Additive.toMul v)
    let K : Subgroup G:=
      { carrier :={x | ZE (Q12 G x)∈
          Submodule.span (ZMod p) (T:Set (Additive (Q2r G)))}
        mul_mem':= fun {a b} ha hb=>by
          show ZE (Q12 G (a*b))∈
            Submodule.span (ZMod p) (T:Set (Additive (Q2r G)))
          rw[map_mul,ofMul_mul]
          exact Submodule.add_mem _ ha hb
        one_mem':=by
          show ZE (Q12 G 1)∈
            Submodule.span (ZMod p) (T:Set (Additive (Q2r G)))
          rw[map_one,ofMul_one]
          exact Submodule.zero_mem _
        inv_mem':= fun {a} ha=>by
          show ZE (Q12 G a⁻¹)∈
            Submodule.span (ZMod p) (T:Set (Additive (Q2r G)))
          rw[map_inv,ofMul_inv]
          exact Submodule.neg_mem _ ha }
    have hK:ZA (S:Set G)≤K:=by
     rw[ZD]
     intro x hx
     exact Submodule.subset_span (Finset.mem_coe.mpr
       (Finset.mem_image_of_mem (fun g:G=>ZE (Q12 G g)) hx))
    have hgK:g∈K:=hK (by rw[hS]; exact ZM g)
    have hv:v=ZE (Q12 G g):=by rw[hg,ofMul_toMul]
    rw[hv]
    exact hgK
   have h1:(T:Set (Additive (Q2r G))).finrank (ZMod p)≤T.card:=
     finrank_span_finset_le_card T
   unfold Set.finrank at h1
   rw[hspan,finrank_top]at h1
   exact h1.trans (Finset.card_image_le.trans hSc.le)
 ·
   let b:=Module.finBasis (ZMod p) (Additive (Q2r G))
   choose lift hlift using fun i=>Q3f (G:=G) (Additive.toMul (b i))
   let S:Finset G:=Finset.univ.image lift
   have hgen:ZA (S:Set G)=⊤:=by
    apply Q25
    rw[eq_top_iff]
    intro x _
    let W :Submodule (ZMod p) (Additive (Q2r G)):=
      { carrier :={v | ∃ y∈ZA (S:Set G)⊔frattini G,
          ZE (Q12 G y)=v}
        add_mem':=by
          rintro _ _ ⟨y1,h1,rfl⟩ ⟨y2,h2,rfl⟩
          exact ⟨y1*y2,Subgroup.mul_mem _ h1 h2,by rw[map_mul,ofMul_mul]⟩
        zero_mem':=⟨1,Subgroup.one_mem _,by rw[map_one,ofMul_one]⟩
        smul_mem':=by
          rintro c _ ⟨y,hy,rfl⟩
          refine ⟨y^c.val,Subgroup.pow_mem _ hy _,?_⟩
          conv_rhs=>rw[← ZMod.natCast_zmod_val c]
          rw[Nat.cast_smul_eq_nsmul,map_pow,ofMul_pow] }
    have hW:(⊤:Submodule (ZMod p) (Additive (Q2r G)))≤W:=by
     rw[← b.span_eq,Submodule.span_le]
     rintro _ ⟨i,rfl⟩
     show ∃ y∈ZA (S:Set G)⊔frattini G,
       ZE (Q12 G y)=b i
     refine ⟨lift i,ZJ (ZC ?_),?_⟩
     · exact Finset.mem_coe.mpr (Finset.mem_image_of_mem lift (Finset.mem_univ i))
     · rw[hlift i,ofMul_toMul]
    have hmem:∃ y∈ZA (S:Set G)⊔frattini G,
        ZE (Q12 G y)=ZE (Q12 G x):=
      hW (Submodule.mem_top (x:=ZE (Q12 G x)))
    obtain ⟨y,hy,hyx⟩:=hmem
    have hyx':Q12 G y=Q12 G x:=Additive.ofMul.injective hyx
    have hk:y⁻¹*x∈(Q12 G).ker :=by
     rw[MonoidHom.mem_ker,map_mul,map_inv,hyx',inv_mul_cancel]
    rw[hker]at hk
    have e:x =y *(y⁻¹*x):=by group
    rw[e]
    exact Subgroup.mul_mem _ hy (ZL hk)
   calc Group.rank G≤S.card:=Group.rank_le hgen
     _≤(Finset.univ:Finset (Fin (Module.finrank (ZMod p)
           (Additive (Q2r G))))).card:=Finset.card_image_le
     _=_:=by rw[Finset.card_univ,Fintype.card_fin]
lemma Q5j (hG:IsPGroup p G):
    ZB (G⧸Qv p G)=p^Group.rank G:=by
 rw[← Q44 hG,Q1n hG]
end Burnside
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u v
section SProd
variable {D:Type u} [Group D]
def sprod:(n:ℕ)→(Fin n→D)→D
  | 0,_=>1
  | n+1,f=>f 0*sprod n (fun i=>f i.succ)
lemma Qht (K:Subgroup D):∀ (n:ℕ) (f:Fin n→D),(∀ i,f i∈K)→sprod n f∈K
  | 0,_,_=>by
    show (1:D)∈K
    exact K.one_mem
  | n+1,f,h=>by
    show f 0*sprod n (fun i=>f i.succ)∈K
    exact K.mul_mem (h 0) (Qht K n _ (fun i=>h i.succ))
lemma Qhp {E:Type v} [Group E] (φ:D→*E):∀ (n:ℕ) (f:Fin n→D),
    φ (sprod n f)=sprod n (fun i=>φ (f i))
  | 0,_=>by
    show φ 1=1
    exact map_one φ
  | n+1,f=>by
    show φ (f 0*sprod n (fun i=>f i.succ))=φ (f 0)*sprod n (fun i=>φ (f i.succ))
    rw[map_mul,Qhp φ n]
def Q2e {n:ℕ} (X:Fin n→D) (e:Fin n→ℕ):D:=sprod n (fun t=>X t^e t)
lemma Qk9 {E:Type v} [Group E] (φ:D→*E) {n:ℕ} (X:Fin n→D) (e:Fin n→ℕ):
    φ (Q2e X e)=Q2e (fun t=>φ (X t)) e:=by
  unfold Q2e
  rw[Qhp]
  simp only[map_pow]
lemma Q8o {n:ℕ} (X:Fin n→D) (e:Fin n→ℕ) (T:Set (Fin n))
    (h:∀ t,e t≠0→t∈T):Q2e X e∈ZA (X '' T):=by
 unfold Q2e
 apply Qht
 intro t
 show X t^e t∈_
 by_cases ht:e t=0
 · rw[ht,pow_zero]
   exact one_mem _
 · have hmem:X t∈ZA (X '' T):=ZC ⟨t,h t ht,rfl⟩
   exact pow_mem hmem _
lemma Q9j:∀ (n:ℕ) (f:Fin n→D),(∀ i,f i=1)→sprod n f=1
  | 0,_,_=>rfl
  | n+1,f,h=>by
    show f 0*sprod n (fun i=>f i.succ)=1
    rw[h 0,Q9j n _ (fun i=>h i.succ),one_mul]
lemma Qcn:∀ (n:ℕ) (f:Fin n→D) (t:Fin n),(∀ i,i≠t→ f i=1)→
    sprod n f= f t
  | 0,_,t,_=>t.elim0
  | n +1,f,t,h=>by
    show f 0*sprod n (fun i=>f i.succ)= f t
    by_cases ht:t=0
    · rw[Q9j n _ (fun i=>h i.succ (by rw[ht]; exact Fin.succ_ne_zero i)),mul_one,ht]
    · obtain ⟨t',rfl⟩:=Fin.exists_succ_eq.mpr ht
      rw[h 0 (fun h0=>ht h0.symm),one_mul]
      exact Qcn n _ t' (fun i hi=>h i.succ (fun h'=>hi (Fin.succ_injective _ h')))
lemma Qhr :∀ (n:ℕ) (f g:Fin n→D),(∀ i j,f i≠1→ g j≠1→i<j)→
    sprod n f*sprod n g=sprod n (fun i=>f i*g i)
  | 0,_,_,_=>by
    show (1:D)*1=1
    rw[one_mul]
  | n + 1,f,g,h=>by
    show f 0*sprod n (fun i=>f i.succ)*(g 0*sprod n (fun i=>g i.succ))=
      f 0*g 0*sprod n (fun i=>f i.succ*g i.succ)
    by_cases hg:g 0=1
    · rw[hg,one_mul,mul_one,mul_assoc]
      congr 1
      exact Qhr n _ _ (fun i j hi hj=>Fin.succ_lt_succ_iff.mp (h _ _ hi hj))
    · have hf:∀ i,f i=1:=by
        intro i
        by_contra hi
        exact absurd (h i 0 hi hg) (Fin.not_lt_zero i)
      rw[Q9j n _ (fun i=>hf i.succ),hf 0]
      simp only[one_mul]
      congr 1
      congr 1
      funext i
      rw[hf i.succ,one_mul]
lemma Qgv {n:ℕ} (X:Fin n→D) (e1 e2:Fin n→ℕ)
    (h:∀ u v,e1 u≠0→e2 v≠0→u<v):Q2e X e1*Q2e X e2=Q2e X (e1+e2):=by
 unfold Q2e
 rw[Qhr]
 · congr 1
   funext i
   rw[Pi.add_apply,pow_add]
 · intro i j hi hj
   refine h i j (fun h0=>hi ?_) (fun h0=>hj ?_)
   · simp only[h0,pow_zero]
   · simp only[h0,pow_zero]
def delta {n:ℕ} (t:Fin n) (k:ℕ):Fin n→ℕ:= fun u=>if u=t then k else 0
lemma Qhw {n:ℕ} (X:Fin n→D) (t:Fin n) (k:ℕ):Q2e X (delta t k)=X t^k:=by
 unfold Q2e
 rw[Qcn n _ t]
 · show X t^(if t=t then k else 0)=X t^k
   rw[if_pos rfl]
 · intro i hi
   show X i^(if i=t then k else 0)=1
   rw[if_neg hi,pow_zero]
lemma Qms {n:ℕ} (X:Fin n→D):Q2e X (fun _=> 0)=1:=by
  unfold Q2e
  exact Q9j n _ (fun i=>pow_zero _)
end SProd
section CardLe
variable {D:Type u} [Group D]
lemma Q6c (K:Subgroup D) (x:D) (q:ℕ) (hq:0<q)
    (hconj:∀ y∈K,x*y *x⁻¹∈K) (hpow:x^q∈K) (S:Set D)
    (hS:S⊆insert x (K:Set D)):
    ∀ z∈ZA S,∃ y∈K,∃ k:ℕ,z=y *x^k:=by
 have hconjm:∀ m:ℕ,∀ y∈K,x^m*y *(x^m)⁻¹∈K:=by
  intro m
  induction m with
  | zero=>intro y hy; simpa using hy
  | succ m ih=>
    intro y hy
    have:=hconj _ (ih y hy)
    convert this using 1
    group
 intro z hz
 induction hz using Subgroup.closure_induction_left with
 | one=>exact ⟨1,one_mem _,0,by simp⟩
 | mul_left g hg z hz ih=>
   obtain ⟨y,hy,k,rfl⟩:=ih
   rcases Set.mem_insert_iff.mp (hS hg) with rfl | hg'
   · exact ⟨g*y *g⁻¹,hconj y hy,k+1,by group⟩
   · exact ⟨g*y,mul_mem hg' hy,k,by group⟩
 | inv_mul_cancel g hg z hz ih=>
   obtain ⟨y,hy,k,rfl⟩:=ih
   rcases Set.mem_insert_iff.mp (hS hg) with rfl | hg'
   · obtain ⟨q',rfl⟩:∃ q',q=q'+1:=⟨q - 1,by omega⟩
     refine ⟨g^q'*((g^(q'+1))⁻¹*y)*(g^q')⁻¹,
       hconjm q' _ (mul_mem (inv_mem hpow) hy),q'+k,?_⟩
     group
   · exact ⟨g⁻¹*y,mul_mem (inv_mem hg') hy,k,by group⟩
lemma Qc7 [Finite D] (K:Subgroup D) (x:D) (q:ℕ) (hq:0<q)
    (hconj:∀ y∈K,x*y *x⁻¹∈K) (hpow:x^q∈K) (S:Set D)
    (hS:S⊆insert x (K:Set D)):
    ZB (ZA S)≤ZB K*q:=by
 have key:∀ z∈ZA S,∃ yk:K×Fin q,z=(yk.1:D)*x^(yk.2:ℕ):=by
  intro z hz
  obtain ⟨y,hy,k,rfl⟩:=Q6c K x q hq hconj hpow S hS z hz
  refine ⟨(⟨y *(x^q)^(k/q),mul_mem hy (pow_mem hpow _)⟩,⟨k % q,Nat.mod_lt _ hq⟩),?_⟩
  show y *x^k=y *(x^q)^(k/q)*x^(k % q)
  rw[mul_assoc, ← pow_mul, ← pow_add,Nat.div_add_mod]
 choose F hF using key
 have hinj:Function.Injective (fun z:ZA S=>F z.1 z.2):=by
   intro z z' h
   have h':F z.1 z.2=F z'.1 z'.2:=h
   apply Subtype.ext
   calc z.1=((F z.1 z.2).1:D)*x^((F z.1 z.2).2:ℕ):=hF _ _
     _=((F z'.1 z'.2).1:D)*x^((F z'.1 z'.2).2:ℕ):=by rw[h']
     _=z'.1:=(hF _ _).symm
 have hc:=Nat.card_le_card_of_injective _ hinj
 rwa[Nat.card_prod,Nat.card_fin]at hc
lemma Qg7 (T:Set D) (x:D) (h:∀ z∈T,x*z*x⁻¹∈ZA T):
    ∀ y∈ZA T,x*y *x⁻¹∈ZA T:=by
 intro y hy
 have hle:ZA T≤(ZA T).comap (MulAut.conj x).toMonoidHom:=by
  rw[ZD]
  intro z hz
  exact h z hz
 simpa using hle hy
lemma Q9t [Finite D] {n:ℕ} (X:Fin n→D) (q:Fin n→ℕ)
    (hq:∀ t,0<q t) (prec:Fin n→Fin n→Prop)
    (hirr :∀ t,¬ prec t t) (hasymm:∀ t u,prec t u→¬ prec u t)
    (hmin:∀ S:Finset (Fin n),S.Nonempty→∃ t∈S,∀ u∈S,u≠t→prec t u)
    (hpow:∀ t,X t^q t∈ZA (X '' {u | prec t u}))
    (hconj:∀ t u,prec t u→X t *X u*(X t)⁻¹∈ZA (X '' {u | prec t u})):
    ∀ S:Finset (Fin n),(∀ t∈S,∀ u,prec t u→u∈S)→
      ZB (ZA (X '' (S:Set (Fin n))))≤∏ t∈S,q t:=by
  suffices h:∀ k,∀ S:Finset (Fin n),S.card=k→(∀ t∈S,∀ u,prec t u→u∈S)→
      ZB (ZA (X '' (S:Set (Fin n))))≤∏ t∈S,q t from
    fun S hS=>h _ S rfl hS
  intro k
  induction k with
  | zero=>
    intro S hS _
    rw[Finset.card_eq_zero.mp hS]
    simp
  | succ k ih=>
    intro S hS hup
    have hne:S.Nonempty:=Finset.card_pos.mp (by omega)
    obtain ⟨t,htS,htmin⟩:=hmin S hne
    have hup':∀ t'∈S.erase t,∀ u,prec t' u→u∈S.erase t:=by
     intro t' ht' u hu
     have ht'S:=Finset.mem_of_mem_erase ht'
     have ht't:=Finset.ne_of_mem_erase ht'
     refine Finset.mem_erase.mpr ⟨?_,hup t' ht'S u hu⟩
     rintro rfl
     exact hasymm _ _ (htmin t' ht'S ht't) hu
    have hcard:(S.erase t).card=k:=by
     rw[Finset.card_erase_of_mem htS]
     omega
    have hK:=ih (S.erase t) hcard hup'
    have hsucc:ZA (X '' {u | prec t u})≤
        ZA (X '' ((S.erase t:Finset (Fin n)):Set (Fin n))):=by
      apply ZO
      rintro _ ⟨u,hu,rfl⟩
      have hu':prec t u:=hu
      refine ⟨u,?_,rfl⟩
      rw[Finset.mem_coe]
      refine Finset.mem_erase.mpr ⟨?_,hup t htS u hu'⟩
      rintro rfl
      exact hirr _ hu'
    have hconjK:=Qg7 (X '' ((S.erase t:Finset (Fin n)):Set (Fin n))) (X t) (by
     rintro _ ⟨u,hu,rfl⟩
     rw[Finset.mem_coe]at hu
     have hut:=Finset.ne_of_mem_erase hu
     have huS:=Finset.mem_of_mem_erase hu
     exact hsucc (hconj t u (htmin u huS hut)))
    have hS':X '' (S:Set (Fin n))⊆
        insert (X t) ((ZA (X '' ((S.erase t:Finset (Fin n)):Set (Fin n))):
          Subgroup D):Set D):=by
     rintro _ ⟨u,hu,rfl⟩
     rw[Finset.mem_coe]at hu
     by_cases hut:u=t
     · rw[hut]
       exact Set.mem_insert _ _
     · refine Set.mem_insert_of_mem _ (ZC ⟨u,?_,rfl⟩)
       rw[Finset.mem_coe]
       exact Finset.mem_erase.mpr ⟨hut,hu⟩
    have hstep:=Qc7 _ (X t) (q t) (hq t) hconjK (hsucc (hpow t)) _ hS'
    calc ZB (ZA (X '' (S:Set (Fin n))))
        ≤ ZB (ZA (X '' ((S.erase t:Finset (Fin n)):Set (Fin n))))*q t:=
          hstep
      _≤(∏ u∈S.erase t,q u)*q t:=Nat.mul_le_mul_right _ hK
      _=∏ u∈S,q u:=by rw[mul_comm,Finset.mul_prod_erase S q htS]
lemma Qg4 [Finite D] {n:ℕ} (X:Fin n→D) (q:Fin n→ℕ)
    (prec:Fin n→Fin n→Prop) (hasymm:∀ t u,prec t u→¬ prec u t)
    (hmin:∀ S:Finset (Fin n),S.Nonempty→∃ t∈S,∀ u∈S,u≠t→prec t u)
    (hnot:∀ t k,0<k→k<q t→X t^k∉ZA (X '' {u | prec t u})):
    ∀ S:Finset (Fin n),(∀ t∈S,∀ u,prec t u→u∈S)→
      ∏ t∈S,q t≤ZB (ZA (X '' (S:Set (Fin n)))):=by
  suffices h:∀ k,∀ S:Finset (Fin n),S.card=k→(∀ t∈S,∀ u,prec t u→u∈S)→
      ∏ t∈S,q t≤ZB (ZA (X '' (S:Set (Fin n)))) from
    fun S hS=>h _ S rfl hS
  intro k
  induction k with
  | zero=>
    intro S hS _
    rw[Finset.card_eq_zero.mp hS]
    simp
  | succ k ih =>
    intro S hS hup
    have hne:S.Nonempty:=Finset.card_pos.mp (by omega)
    obtain ⟨t,htS,htmin⟩:=hmin S hne
    have hup':∀ t'∈S.erase t,∀ u,prec t' u→u∈S.erase t:=by
     intro t' ht' u hu
     have ht'S:=Finset.mem_of_mem_erase ht'
     have ht't:=Finset.ne_of_mem_erase ht'
     refine Finset.mem_erase.mpr ⟨?_,hup t' ht'S u hu⟩
     rintro rfl
     exact hasymm _ _ (htmin t' ht'S ht't) hu
    have hcard:(S.erase t).card=k:=by
     rw[Finset.card_erase_of_mem htS]
     omega
    have hK:=ih (S.erase t) hcard hup'
    have hKL:ZA (X '' ((S.erase t:Finset (Fin n)):Set (Fin n)))≤
        ZA (X '' (S:Set (Fin n))):=by
     apply ZO
     rintro _ ⟨u,hu,rfl⟩
     exact ⟨u,Finset.mem_coe.mpr (Finset.mem_of_mem_erase (Finset.mem_coe.mp hu)),rfl⟩
    have hKs:ZA (X '' ((S.erase t:Finset (Fin n)):Set (Fin n)))≤
        ZA (X '' {u | prec t u}):=by
      apply ZO
      rintro _ ⟨u,hu,rfl⟩
      have hu':=Finset.mem_coe.mp hu
      exact ⟨u,htmin u (Finset.mem_of_mem_erase hu') (Finset.ne_of_mem_erase hu'),rfl⟩
    have hxL:X t∈ZA (X '' (S:Set (Fin n))):=
      ZC ⟨t,Finset.mem_coe.mpr htS,rfl⟩
    have hinj :Function.Injective
        (fun yk:ZA (X '' ((S.erase t:Finset (Fin n)):Set (Fin n)))×
            Fin (q t)=>
          (⟨(yk.1:D)*X t^(yk.2:ℕ),mul_mem (hKL yk.1.2) (pow_mem hxL _)⟩:
            ZA (X '' (S:Set (Fin n))))):=by
      intro a b h
      have heq:(a.1:D)*X t^(a.2:ℕ)=(b.1:D)*X t^(b.2:ℕ):=
        congrArg Subtype.val h
      have hkk:(a.2:ℕ)=b.2:=by
       by_contra hne
       rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
       · have e1:X t^((b.2:ℕ) - a.2)=(b.1:D)⁻¹*a.1:=by
           rw[pow_sub _ hlt.le,eq_mul_inv_of_mul_eq heq]
           group
         have hmem:X t^((b.2:ℕ) - a.2)∈
             ZA (X '' ((S.erase t:Finset (Fin n)):Set (Fin n))):=by
          rw[e1]
          exact mul_mem (inv_mem b.1.2) a.1.2
         have hb2:=b.2.isLt
         exact hnot t _ (by omega) (by omega) (hKs hmem)
       · have e1:X t^((a.2:ℕ) - b.2)=(a.1:D)⁻¹*b.1:=by
           rw[pow_sub _ hlt.le,eq_mul_inv_of_mul_eq heq.symm]
           group
         have hmem:X t^((a.2:ℕ) - b.2)∈
             ZA (X '' ((S.erase t:Finset (Fin n)):Set (Fin n))):=by
          rw[e1]
          exact mul_mem (inv_mem a.1.2) b.1.2
         have ha2:=a.2.isLt
         exact hnot t _ (by omega) (by omega) (hKs hmem)
      have hy:(a.1:D)=b.1:=by
       rw[hkk]at heq
       exact mul_right_cancel heq
      exact Prod.ext (Subtype.ext hy) (Fin.ext hkk)
    have hc:=Nat.card_le_card_of_injective _ hinj
    rw[Nat.card_prod,Nat.card_fin]at hc
    calc ∏ u∈S,q u=(∏ u∈S.erase t,q u)*q t:=by
          rw[mul_comm,Finset.mul_prod_erase S q htS]
      _ ≤ ZB (ZA (X '' ((S.erase t:Finset (Fin n)):Set (Fin n))))*q t:=
          Nat.mul_le_mul_right _ hK
      _≤_:=hc
end CardLe
section Data
structure Q5 where
  n:ℕ
  s:ℕ
  lv:Fin n→ℕ
  df:Fin n→Fin n×Fin n
  a:Fin n→ℕ
  b:Fin n→Fin n→ℕ
  c:Fin n→Fin n→Fin n→ℕ
namespace Q5
def prec (d:Q5) (t u:Fin d.n):Prop:=
  d.lv t<d.lv u∨(d.lv t=d.lv u∧u.val<t.val)
def Rec (d:Q5) (t k:Fin d.n):Prop:=
  (d.lv t=0∧d.lv k=0∧t<k)∨(d.lv t=1∧k.val≤(d.df t).2.val)∨
    (2≤d.lv t∧k.val<d.s)
structure Struct (d:Q5):Prop where
  mono:∀ t u:Fin d.n,t≤u→d.lv t≤d.lv u
  s_le:d.s≤d.n
  core:∀ t:Fin d.n,t.val<d.s→d.lv t=0
  df_lv:∀ t,1≤d.lv t→d.lv (d.df t).1+1=d.lv t
  df_core:∀ t,1≤d.lv t→(d.df t).2.val<d.s
  df_one:∀ t,d.lv t=1→(d.df t).1< (d.df t).2
structure Valid (d:Q5):Prop extends Struct d where
  b_supp:∀ t u,d.b t u≠0→d.prec t u
  c_supp:∀ t k u,d.c t k u≠0→d.lv t<d.lv u
def Bounded (p:ℕ) (d:Q5):Prop:=
  (∀ t u,d.b t u<p^d.a u)∧(∀ t k u,d.c t k u<p^d.a u)
lemma Qe9 (d:Q5) (t:Fin d.n):¬ d.prec t t:=by
 unfold prec
 omega
lemma Qbr (d:Q5) (t u:Fin d.n) (h:d.prec t u):¬ d.prec u t:=by
 unfold prec at *
 omega
lemma Qem (d:Q5) (S:Finset (Fin d.n)) (hS:S.Nonempty):
    ∃ t∈S,∀ u∈S,u≠t→d.prec t u:=by
 obtain ⟨t0,ht0,hmin0⟩:=Finset.exists_min_image S d.lv hS
 have hT:(S.filter (fun u=>d.lv u=d.lv t0)).Nonempty:=
   ⟨t0,Finset.mem_filter.mpr ⟨ht0,rfl⟩⟩
 obtain ⟨t,htT,hmax⟩:=Finset.exists_max_image _ (fun u:Fin d.n=>u.val) hT
 obtain ⟨htS,htl⟩:=Finset.mem_filter.mp htT
 refine ⟨t,htS,fun u huS hut=>?_⟩
 have h1:=hmin0 u huS
 unfold prec
 by_cases hl:d.lv u=d.lv t0
 · have h2:=hmax u (Finset.mem_filter.mpr ⟨huS,hl⟩)
   have h3:u.val≠t.val:= fun h=>hut (Fin.ext h)
   right
   constructor
   · omega
   · have h2':u.val≤t.val:=h2
     omega
 · left
   omega
end Q5
structure Q2k (p:ℕ) (d:Q5) {G:Type u} [Group G] (X:Fin d.n→G):Prop where
  card:ZB G=p^(∑ t,d.a t)
  gen:ZA (ZG X)=⊤
  dfeq:∀ t,1≤d.lv t→X t=⁅X (d.df t).1,X (d.df t).2⁆
  pow:∀ t,X t^(p^d.a t)=Q2e X (d.b t)
  comm0:∀ t k,d.lv t=0→d.lv k=0→t<k→⁅X t,X k⁆=Q2e X (d.c t k)
  comm1:∀ t k:Fin d.n,d.lv t=1→k.val≤(d.df t).2.val→⁅X t,X k⁆=Q2e X (d.c t k)
  comm2:∀ t k:Fin d.n,2≤d.lv t→k.val<d.s→⁅X t,X k⁆=Q2e X (d.c t k)
end Data
section CardData
variable {D:Type u} [Group D]
abbrev Q2q (d:Q5) (Z:Fin d.n→D) (v:ℕ):Set D:=Z '' {t | d.lv t=v}
def Q3g (d:Q5) (Z:Fin d.n→D) (k:ℕ):D:=if h:k<d.n then Z ⟨k,h⟩ else 1
lemma Qa3 (d:Q5) (Z:Fin d.n→D) {k:ℕ} (h:k<d.n):
    Q3g d Z k=Z ⟨k,h⟩:=by
 unfold Q3g
 rw[dif_pos h]
lemma Qm6 (d:Q5) (Z:Fin d.n→D) (k:Fin d.n):Q3g d Z k.val=Z k:=
  Qa3 d Z k.isLt
def Qfl (d:Q5):Set (ℕ×ℕ):=
  {ab | ∃ t,d.lv t=1∧ab=((d.df t).1.val,(d.df t).2.val)}
lemma Q9i (d:Q5) {ab:ℕ×ℕ}:
    ab∈Qfl d↔∃ t,d.lv t=1∧ab=((d.df t).1.val,(d.df t).2.val):=Iff.rfl
lemma Qlw (d:Q5) (hd:d.Struct) (t:Fin d.n) (ht:1≤d.lv t):
    (d.df t).1.val<t.val:=by
 have h1:=hd.df_lv t ht
 by_contra hcon
 have h2:=hd.mono t (d.df t).1 (Fin.le_def.mpr (by omega))
 omega
lemma Q5f (d:Q5) (hd:d.Struct) (Z:Fin d.n→D)
    (hdf:∀ t,1≤d.lv t→Z t=⁅Z (d.df t).1,Z (d.df t).2⁆):
    ∀ t,Z t∈lcs D (d.lv t):=by
 refine Qgp ?_
 intro t ih
 by_cases h0:d.lv t=0
 · rw[h0,lcs_zero]
   exact ZM _
 · have h1:1≤d.lv t:=by omega
   have hprev:=ih (d.df t).1 (Qlw d hd t h1)
   rw[← hd.df_lv t h1,hdf t h1]
   exact Qb hprev _
lemma Qbz (d:Q5) (hd:d.Struct) (Z:Fin d.n→D)
    (hgen:ZA (ZG Z)=⊤) (hN:∃ N,lcs D N=⊥)
    (hdf:∀ t,1≤d.lv t→Z t=⁅Z (d.df t).1,Z (d.df t).2⁆)
    (hH1':∀ i k,d.lv i=0→d.lv k=0→
      ⁅Z i,Z k⁆∈ZA (Q2q d Z 1)⊔lcs D 2)
    (hH2':∀ t k:Fin d.n,d.lv t=1→k.val≤(d.df t).2.val→
      ⁅Z t,Z k⁆∈ZA (Q2q d Z 2)⊔lcs D 3)
    (hH3':∀ t k:Fin d.n,2≤d.lv t→k.val<d.s→
      ⁅Z t,Z k⁆∈ZA (Q2q d Z (d.lv t+1))⊔lcs D (d.lv t+2)):
    ∀ w,1≤w→lcs D w≤ZA (Z '' {u | w≤d.lv u}):=by
  have hlv:=Q5f d hd Z hdf
  have hu:∀ k:Fin d.n,Q3g d Z k.val=Z k:=Qm6 d Z
  have hP:∀ ab∈Qfl d,ab.1<ab.2∧ab.2<d.s:=by
   intro ab hab
   obtain ⟨t,ht,rfl⟩:=(Q9i d).mp hab
   exact ⟨Fin.lt_def.mp (hd.df_one t ht),hd.df_core t (by omega)⟩
  have hE1:Q2q d Z 1=(fun ab:ℕ×ℕ=> ⁅Q3g d Z ab.1,Q3g d Z ab.2⁆) '' Qfl d:=by
    ext x
    constructor
    · rintro ⟨t,ht,rfl⟩
      have ht':d.lv t=1:=ht
      refine ⟨((d.df t).1.val,(d.df t).2.val),(Q9i d).mpr ⟨t,ht',rfl⟩,?_⟩
      show ⁅Q3g d Z (d.df t).1.val,Q3g d Z (d.df t).2.val⁆=Z t
      rw[hu,hu,hdf t (by omega)]
    · rintro ⟨ab,hab,rfl⟩
      obtain ⟨t,ht,rfl⟩:=(Q9i d).mp hab
      refine ⟨t,ht,?_⟩
      show Z t=⁅Q3g d Z (d.df t).1.val,Q3g d Z (d.df t).2.val⁆
      rw[hu,hu]
      exact hdf t (by omega)
  have hL2:∀ w,1≤w→∀ x∈Q2q d Z (w+1),∃ y∈ZA (Q2q d Z w),
      ∃ b<d.s,x =⁅y,Q3g d Z b⁆:=by
   intro w hw x hx
   obtain ⟨t,ht,rfl⟩:=hx
   have ht':d.lv t=w+1:=ht
   have h1:1≤d.lv t:=by omega
   have ha:d.lv (d.df t).1=w:=by have:=hd.df_lv t h1; omega
   refine ⟨Z (d.df t).1,ZC ⟨(d.df t).1,ha,rfl⟩,(d.df t).2.val,
     hd.df_core t h1,?_⟩
   rw[hu]
   exact hdf t h1
  have hL0:ZA (Q2q d Z 0)⊔lcs D 1=⊤:=by
   rw[eq_top_iff, ← hgen,ZD]
   rintro _ ⟨t,rfl⟩
   by_cases h0:d.lv t=0
   · exact ZJ (ZC ⟨t,h0,rfl⟩)
   · exact ZL (Qd (D:=D) (show 1≤d.lv t by omega) (hlv t))
  have hH1:∀ x∈Q2q d Z 0,∀ y∈Q2q d Z 0,
      ⁅x,y⁆∈ZA (Q2q d Z 1)⊔lcs D 2:=by
   rintro _ ⟨i,hi,rfl⟩ _ ⟨k,hk,rfl⟩
   exact hH1' i k hi hk
  have hH2:∀ ab∈Qfl d,∀ k≤ab.2,⁅⁅Q3g d Z ab.1,Q3g d Z ab.2⁆,Q3g d Z k⁆∈
      ZA (Q2q d Z 2)⊔lcs D 3:=by
   intro ab hab k hk
   obtain ⟨t,ht,rfl⟩:=(Q9i d).mp hab
   have hk':k≤(d.df t).2.val:=hk
   have hks:k<d.n:=by
    have:=hd.df_core t (by omega)
    have:=hd.s_le
    omega
   show ⁅⁅Q3g d Z (d.df t).1.val,Q3g d Z (d.df t).2.val⁆,Q3g d Z k⁆∈_
   rw[hu,hu, ← hdf t (by omega),Qa3 d Z hks]
   exact hH2' t ⟨k,hks⟩ ht hk'
  have hH3:∀ w,2≤w→∀ x∈Q2q d Z w,∀ k<d.s,
      ⁅x,Q3g d Z k⁆∈ZA (Q2q d Z (w+1))⊔lcs D (w+2):=by
   rintro w hw _ ⟨t,ht,rfl⟩ k hk
   have ht':d.lv t=w:=ht
   have hks:k<d.n:=lt_of_lt_of_le hk hd.s_le
   rw[Qa3 d Z hks]
   have hres:=hH3' t ⟨k,hks⟩ (by omega) hk
   rwa[ht']at hres
  obtain ⟨N,hN⟩:=hN
  have htail:=Qgx d.s (Q3g d Z) (Q2q d Z 0) (Qfl d) (Q2q d Z) hP hE1 hL2 hL0 hH1 hH2 hH3 N hN
  intro w hw
  refine le_trans (htail w hw) ?_
  rw[ZD]
  intro x hx
  simp only[Set.mem_iUnion,Set.mem_Ici,exists_prop]at hx
  obtain ⟨v,hv,t,ht,rfl⟩:=hx
  have ht':d.lv t=v:=ht
  exact ZC ⟨t,(show w≤d.lv t by omega),rfl⟩
lemma Qfo [Finite D] {p:ℕ} (hp:0<p) (d:Q5) (hd:d.Valid)
    (Z:Fin d.n→D) (hgen:ZA (ZG Z)=⊤) (hN:∃ N,lcs D N=⊥)
    (hdf:∀ t,1≤d.lv t→Z t=⁅Z (d.df t).1,Z (d.df t).2⁆)
    (hpow:∀ t,Z t^(p^d.a t)∈ZA (Z '' {u | d.prec t u}))
    (hc0:∀ t k,d.lv t=0→d.lv k=0→t<k→
      ⁅Z t,Z k⁆∈ZA (Z '' {u | d.lv t<d.lv u}))
    (hc1:∀ t k:Fin d.n,d.lv t=1→k.val≤(d.df t).2.val→
      ⁅Z t,Z k⁆∈ZA (Z '' {u | d.lv t<d.lv u}))
    (hc2:∀ t k:Fin d.n,2≤d.lv t→k.val<d.s→
      ⁅Z t,Z k⁆∈ZA (Z '' {u | d.lv t<d.lv u})):
    ZB D ≤p^(∑ t,d.a t):=by
  have hlv:=Q5f d hd.toStruct Z hdf
  have hmono:∀ (P Q:Fin d.n→Prop),(∀ u,P u→Q u)→
      ZA (Z '' {u | P u})≤ZA (Z '' {u | Q u}):=
    fun P Q h=>ZO (by rintro _ ⟨u,hu,rfl⟩; exact ⟨u,h u hu,rfl⟩)
  have hdrop:∀ w,1≤w→ZA (Z '' {u | w≤d.lv u})≤
      ZA (Q2q d Z w)⊔lcs D (w+1):=by
    intro w hw
    rw[ZD]
    rintro _ ⟨t,ht,rfl⟩
    have ht':w≤d.lv t:=ht
    rcases Nat.lt_or_ge w (d.lv t) with hlt' | hge
    · exact ZL (Qd (D:=D) (show w+1≤d.lv t by omega) (hlv t))
    · exact ZJ (ZC ⟨t,le_antisymm hge ht',rfl⟩)
  have hH1':∀ i k,d.lv i=0→d.lv k=0→
      ⁅Z i,Z k⁆∈ZA (Q2q d Z 1)⊔lcs D 2:=by
   intro i k hi' hk'
   rcases lt_trichotomy i k with hik | rfl | hki
   · exact hdrop 1 le_rfl (hmono _ _ (fun u hu=>by omega) (hc0 i k hi' hk' hik))
   · rw[commutatorElement_self]
     exact one_mem _
   · rw[← commutatorElement_inv]
     exact inv_mem (hdrop 1 le_rfl (hmono _ _ (fun u hu=>by omega) (hc0 k i hk' hi' hki)))
  have hH2':∀ t k:Fin d.n,d.lv t=1→k.val≤(d.df t).2.val→
      ⁅Z t,Z k⁆∈ZA (Q2q d Z 2)⊔lcs D 3:= fun t k ht hk=>
    hdrop 2 (by omega) (hmono _ _ (fun u hu=>by omega) (hc1 t k ht hk))
  have hH3':∀ t k:Fin d.n,2≤d.lv t→k.val<d.s→
      ⁅Z t,Z k⁆∈ZA (Q2q d Z (d.lv t+1))⊔lcs D (d.lv t+2):=by
   intro t k ht hk
   have hres:=hdrop (d.lv t+1) (by omega)
     (hmono _ _ (fun u hu=>by omega) (hc2 t k ht hk))
   rwa[show d.lv t+1+1=d.lv t+2 by omega]at hres
  have hdeep:=Qbz d hd.toStruct Z hgen hN hdf hH1' hH2' hH3'
  have hconj:∀ t u,d.prec t u→
      Z t *Z u*(Z t)⁻¹∈ZA (Z '' {u | d.prec t u}):=by
    intro t u htu
    have he:Z t *Z u*(Z t)⁻¹=⁅Z t,Z u⁆*Z u:=by
     simp only[commutatorElement_def]
     group
    rw[he]
    refine mul_mem ?_ (ZC ⟨u,htu,rfl⟩)
    have h1:=hdeep (d.lv u+1) (by omega) (Qj (Z t) (hlv u))
    refine hmono _ _ (fun u' hu'=>?_) h1
    have hu'':d.lv u+1≤d.lv u':=hu'
    have htu':d.lv t<d.lv u∨(d.lv t=d.lv u∧u.val<t.val):=htu
    exact Or.inl (by omega)
  have hcard:=Q9t Z (fun t=>p^d.a t) (fun t=>pow_pos hp _) d.prec
    d.Qe9 d.Qbr d.Qem hpow hconj Finset.univ (fun _ _ _ _=>Finset.mem_univ _)
  have hprod:∏ t∈(Finset.univ:Finset (Fin d.n)),(fun t=>p^d.a t) t=
      p^(∑ t,d.a t):=Finset.prod_pow_eq_pow_sum _ _ _
  rw[Finset.coe_univ,Set.image_univ,hgen,Subgroup.card_top]at hcard
  exact hcard.trans (le_of_eq hprod)
end CardData
section Rigid
variable {G G':Type u} [Group G] [Group G']
lemma Qdl [Finite G] [Finite G'] [Group.IsNilpotent G] [Group.IsNilpotent G']
    {p:ℕ} (hp:0<p) (d:Q5) (hd:d.Valid) (X:Fin d.n→G) (X':Fin d.n→G')
    (h:Q2k p d X) (h':Q2k p d X'):
    ZB (diagSub X X')≤p^(∑ t,d.a t):=by
 have hF:∀ e,Q6i X X' (Q2e (Q2x X X') e)=Q2e X e:= fun e=>Qk9 _ _ _
 have hS:∀ e,Q6a X X' (Q2e (Q2x X X') e)=Q2e X' e:= fun e=>Qk9 _ _ _
 have hrel:∀ (x:diagSub X X') (e:Fin d.n→ℕ),Q6i X X' x =Q2e X e→
     Q6a X X' x =Q2e X' e→x =Q2e (Q2x X X') e:=by
  intro x e h1 h2
  apply Qit X X'
  · rw[h1,hF]
  · rw[h2,hS]
 refine Qfo hp d hd (Q2x X X') (Qgd X X') ?_ ?_ ?_ ?_ ?_ ?_
 · exact Subgroup.nilpotent_iff_lowerCentralSeries.mp inferInstance
 · intro t ht
   apply Qit X X'
   · simp only[map_commutatorElement,Q5z]
     exact h.dfeq t ht
   · simp only[map_commutatorElement,Q5t]
     exact h'.dfeq t ht
 · intro t
   rw [hrel (Q2x X X' t^(p^d.a t)) (d.b t) (by simp only[map_pow,Q5z]; exact h.pow t)
     (by simp only[map_pow,Q5t]; exact h'.pow t)]
   exact Q8o _ _ _ (fun u hu=>hd.b_supp t u hu)
 · intro t k ht hk htk
   rw [hrel ⁅Q2x X X' t,Q2x X X' k⁆ (d.c t k) (by simp only[map_commutatorElement,Q5z]; exact h.comm0 t k ht hk htk)
     (by simp only[map_commutatorElement,Q5t]; exact h'.comm0 t k ht hk htk)]
   exact Q8o _ _ _ (fun u hu=>hd.c_supp t k u hu)
 · intro t k ht hk
   rw [hrel ⁅Q2x X X' t,Q2x X X' k⁆ (d.c t k) (by simp only[map_commutatorElement,Q5z]; exact h.comm1 t k ht hk)
     (by simp only[map_commutatorElement,Q5t]; exact h'.comm1 t k ht hk)]
   exact Q8o _ _ _ (fun u hu=>hd.c_supp t k u hu)
 · intro t k ht hk
   rw [hrel ⁅Q2x X X' t,Q2x X X' k⁆ (d.c t k) (by simp only[map_commutatorElement,Q5z]; exact h.comm2 t k ht hk)
     (by simp only[map_commutatorElement,Q5t]; exact h'.comm2 t k ht hk)]
   exact Q8o _ _ _ (fun u hu=>hd.c_supp t k u hu)
lemma Qia {p:ℕ} (hp:p.Prime) [Finite G] [Finite G'] (d:Q5)
    (hd:d.Valid) (X:Fin d.n→G) (X':Fin d.n→G') (h:Q2k p d X)
    (h':Q2k p d X'):Nonempty (G≃*G'):=by
 have:Fact p.Prime:=⟨hp⟩
 have:Group.IsNilpotent G:=(IsPGroup.of_card h.card).isNilpotent
 have:Group.IsNilpotent G':=(IsPGroup.of_card h'.card).isNilpotent
 have hK:=Qdl hp.pos d hd X X' h h'
 have hb1:Function.Bijective (Q6i X X'):=
   (Qjp X X' h.gen).bijective_of_nat_card_le (by rw[h.card]; exact hK)
 have hb2:Function.Bijective (Q6a X X'):=
   (Qix X X' h'.gen).bijective_of_nat_card_le (by rw[h'.card]; exact hK)
 exact ⟨(MulEquiv.ofBijective (Q6i X X') hb1).symm.trans
   (MulEquiv.ofBijective (Q6a X X') hb2)⟩
end Rigid
section Layers
variable {G:Type u} [Group G]
def Q2z (d:Q5) (w j:ℕ):Set (Fin d.n):=
  {u | w<d.lv u∨(w=d.lv u∧u.val<j)}
lemma Q1b (d:Q5) {w j:ℕ} {u:Fin d.n}:
    u∈Q2z d w j↔w<d.lv u∨(w=d.lv u∧u.val<j):=Iff.rfl
noncomputable def Q1q (p:ℕ) (d:Q5) (X:Fin d.n→G) (t:Fin d.n):ℕ:=
  sInf {a:ℕ | X t^(p^a)∈ZA (X '' Q2z d (d.lv t) t.val)}
def Qbw (p:ℕ) (d:Q5) (X:Fin d.n→G) (w j:ℕ):Prop:=
  ∀ z∈ZA (X '' Q2z d w j),∃ e:Fin d.n→ℕ,
    (∀ u,e u≠0→u∈Q2z d w j)∧(∀ u,e u<p^Q1q p d X u)∧z=Q2e X e
variable {p m:ℕ} (d:Q5) (X:Fin d.n→G)
lemma Q5x [Finite G] (hG:ZB G=p^m) (t:Fin d.n):
    X t^(p^Q1q p d X t)∈ZA (X '' Q2z d (d.lv t) t.val):=by
 have hne:{a:ℕ | X t^(p^a)∈ZA (X '' Q2z d (d.lv t) t.val)}.Nonempty:=by
   refine ⟨m,?_⟩
   show X t^(p^m)∈ZA (X '' Q2z d (d.lv t) t.val)
   rw[← hG,pow_card_eq_one']
   exact one_mem _
 exact Nat.sInf_mem hne
lemma Qkw [Finite G] (hp:p.Prime) (hG:ZB G=p^m) (t:Fin d.n) (k:ℕ)
    (hk0:0<k) (hk:k<p^Q1q p d X t):
    X t^k∉ZA (X '' Q2z d (d.lv t) t.val):=by
 intro hmem
 have h2:X t^(p^m)∈ZA (X '' Q2z d (d.lv t) t.val):=by
  rw[← hG,pow_card_eq_one']
  exact one_mem _
 obtain ⟨e, -,he⟩:=(Nat.dvd_prime_pow hp).mp (Nat.gcd_dvd_right k (p^m))
 have h3:X t^(Nat.gcd k (p^m))∈ZA (X '' Q2z d (d.lv t) t.val):=by
  have h4:X t^((Nat.gcd k (p^m):ℕ):ℤ)∈
      ZA (X '' Q2z d (d.lv t) t.val):=by
   rw[Nat.gcd_eq_gcd_ab,zpow_add,zpow_mul,zpow_mul,zpow_natCast,zpow_natCast]
   exact mul_mem (zpow_mem hmem _) (zpow_mem h2 _)
  rwa[zpow_natCast]at h4
 rw[he]at h3
 have hle:Q1q p d X t≤e:=Nat.sInf_le h3
 have hdvd:p^e∣k:=by
  rw[← he]
  exact Nat.gcd_dvd_left k (p^m)
 have h5:p^e≤k:=Nat.le_of_dvd hk0 hdvd
 have h6:p^Q1q p d X t≤p^e:=Nat.pow_le_pow_right hp.pos hle
 exact absurd (lt_of_lt_of_le (lt_of_le_of_lt h5 hk) h6) (lt_irrefl _)
lemma Qdy (hlv:∀ t,X t∈lcs G (d.lv t))
    (hdeep:∀ w,1≤w→lcs G w≤ZA (X '' {u | w≤d.lv u})) (w j:ℕ):
    (ZA (X '' Q2z d w j)).Normal:=by
  refine Q1d (n:=w) ?_ ?_
  · refine (hdeep (w+1) (by omega)).trans (ZO ?_)
    rintro _ ⟨u,hu,rfl⟩
    exact ⟨u,Or.inl hu,rfl⟩
  · rw[ZD]
    rintro _ ⟨u,hu,rfl⟩
    have hu':=(Q1b d).mp hu
    exact Qd (D:=G) (show w≤d.lv u by omega) (hlv u)
lemma Qhm {w j w' j':ℕ} (h:Q2z d w j=Q2z d w' j') (H:Qbw p d X w' j'):
    Qbw p d X w j:=by
 unfold Qbw at *
 rw[h]
 exact H
lemma Qm2 (hp:0<p) {w:ℕ} (j:ℕ) (h:∀ u:Fin d.n,d.lv u<w):
    Qbw p d X w j:=by
 intro z hz
 have hempty:Q2z d w j= ∅ :=by
  ext u
  simp only[Q1b,Set.mem_empty_iff_false,iff_false]
  have:=h u
  omega
 rw[hempty,Set.image_empty,Subgroup.closure_empty,Subgroup.mem_bot]at hz
 refine ⟨fun _=> 0,fun u hu=> (hu rfl).elim,fun u=>pow_pos hp _,?_⟩
 rw[hz,Qms]
lemma Qmi {w:ℕ} (H:Qbw p d X (w+1) d.n):Qbw p d X w 0:=by
 refine Qhm d X ?_ H
 ext u
 simp only[Q1b]
 have:=u.isLt
 constructor
 · intro h
   omega
 · intro h
   omega
lemma Qmz [Finite G] (hp:p.Prime) (hG:ZB G=p^m) (hd:d.Struct)
    (hlv:∀ t,X t∈lcs G (d.lv t))
    (hdeep:∀ w,1≤w→lcs G w≤ZA (X '' {u | w≤d.lv u})) {w j:ℕ}
    (hj:Qbw p d X w j) (h0:Qbw p d X w 0):Qbw p d X w (j+1):=by
  have hlt:∀ u v:Fin d.n,d.lv u<d.lv v→u<v:=by
   intro u v h
   by_contra hc
   have:=hd.mono v u (not_lt.mp hc)
   omega
  by_cases hex:∃ t:Fin d.n,t.val=j∧d.lv t=w
  swap
  · refine Qhm d X ?_ hj
    ext u
    simp only[Q1b]
    constructor
    · rintro (h | ⟨h1,h2⟩)
      · exact Or.inl h
      · refine Or.inr ⟨h1,?_⟩
        rcases Nat.lt_or_ge u.val j with h3 | h3
        · exact h3
        · exact absurd ⟨u,by omega,h1.symm⟩ hex
    · rintro (h | ⟨h1,h2⟩)
      · exact Or.inl h
      · exact Or.inr ⟨h1,by omega⟩
  obtain ⟨t,rfl,rfl⟩:=hex
  intro z hz
  have hq:0<p^Q1q p d X t:=pow_pos hp.pos _
  have hK:=Qdy d X hlv hdeep (d.lv t) t.val
  have hS:X '' Q2z d (d.lv t) (t.val+1)⊆
      insert (X t) ((ZA (X '' Q2z d (d.lv t) t.val):Subgroup G):Set G):=by
   rintro _ ⟨u,hu,rfl⟩
   by_cases hut:u=t
   · rw[hut]
     exact Set.mem_insert _ _
   · refine Set.mem_insert_of_mem _ (ZC ⟨u,?_,rfl⟩)
     have hu':=(Q1b d).mp hu
     have hne:u.val≠t.val:= fun h=>hut (Fin.ext h)
     exact (Q1b d).mpr (by omega)
  obtain ⟨y,hy,k,rfl⟩:=Q6c _ (X t) _ hq (fun y hy=>hK.conj_mem y hy (X t))
    (Q5x d X hG t) _ hS z hz
  obtain ⟨y',hy',k',hk',hyk⟩:∃ y'∈ZA (X '' Q2z d (d.lv t) t.val),
      ∃ k'<p^Q1q p d X t,y *X t^k=y'*X t^k':=
    ⟨y *(X t^(p^Q1q p d X t))^(k/p^Q1q p d X t),
      mul_mem hy (pow_mem (Q5x d X hG t) _),k % p^Q1q p d X t,Nat.mod_lt _ hq,
      by rw[mul_assoc, ← pow_mul, ← pow_add,Nat.div_add_mod]⟩
  rw[hyk]
  obtain ⟨e',he'S,he'b,rfl⟩:=hj y' hy'
  have hsplit:Q2e X e'=Q2e X (fun u=>if d.lv u=d.lv t then e' u else 0)*
      Q2e X (fun u=>if d.lv u=d.lv t then 0 else e' u):=by
    rw[Qgv]
    · congr 1
      funext u
      simp only[Pi.add_apply]
      split_ifs<;>simp
    · intro u v hu hv
      apply hlt
      have hu1:d.lv u=d.lv t:=by
       by_contra hc
       apply hu
       show (if d.lv u=d.lv t then e' u else 0)=0
       rw[if_neg hc]
      have hv1:d.lv v≠d.lv t∧e' v≠0:=by
       by_cases hc:d.lv v=d.lv t
       · exfalso
         apply hv
         show (if d.lv v=d.lv t then 0 else e' v)=0
         rw[if_pos hc]
       · refine ⟨hc,fun h0=>hv ?_⟩
         show (if d.lv v=d.lv t then 0 else e' v)=0
         rw[if_neg hc,h0]
      have:=(Q1b d).mp (he'S v hv1.2)
      omega
  have hHmem:Q2e X (fun u=>if d.lv u=d.lv t then 0 else e' u)∈
      ZA (X '' Q2z d (d.lv t) 0):=by
    refine Q8o X _ _ (fun v hv=>?_)
    have hv1:d.lv v≠d.lv t∧e' v≠0:=by
     by_cases hc:d.lv v=d.lv t
     · exfalso
       apply hv
       show (if d.lv v=d.lv t then 0 else e' v)=0
       rw[if_pos hc]
     · refine ⟨hc,fun h0=>hv ?_⟩
       show (if d.lv v=d.lv t then 0 else e' v)=0
       rw[if_neg hc,h0]
    have:=(Q1b d).mp (he'S v hv1.2)
    exact (Q1b d).mpr (by omega)
  have hh:(X t^k')⁻¹*Q2e X (fun u=>if d.lv u=d.lv t then 0 else e' u)*X t^k'∈
      ZA (X '' Q2z d (d.lv t) 0):=by
    have:=(Qdy d X hlv hdeep (d.lv t) 0).conj_mem _ hHmem (X t^k')⁻¹
    rwa[inv_inv]at this
  obtain ⟨eH,hHS,hHb,hH⟩:=h0 _ hh
  have h1:∀ u v,(fun u=>if d.lv u=d.lv t then e' u else 0) u≠0→delta t k' v≠0→
      u<v:=by
    intro u v hu hv
    have hvt:v=t:=by
     by_contra hc
     apply hv
     show (if v=t then k' else 0)=0
     rw[if_neg hc]
    have hu1:d.lv u=d.lv t∧e' u≠0:=by
     by_cases hc:d.lv u=d.lv t
     · refine ⟨hc,fun h0=>hu ?_⟩
       show (if d.lv u=d.lv t then e' u else 0)=0
       rw[if_pos hc,h0]
     · exfalso
       apply hu
       show (if d.lv u=d.lv t then e' u else 0)=0
       rw[if_neg hc]
    have:=(Q1b d).mp (he'S u hu1.2)
    rw[hvt,Fin.lt_def]
    omega
  have h2:∀ u v,((fun u=>if d.lv u=d.lv t then e' u else 0)+delta t k') u≠0→
      eH v≠0→u<v:=by
    intro u v hu hv
    apply hlt
    have hv':=(Q1b d).mp (hHS v hv)
    have hu':d.lv u=d.lv t:=by
     by_contra hc
     have hut:u≠t:= fun h=>hc (by rw[h])
     apply hu
     simp only[Pi.add_apply,delta,if_neg hc,if_neg hut,add_zero]
    omega
  refine ⟨(fun u=>if d.lv u=d.lv t then e' u else 0)+delta t k'+eH,?_,?_,?_⟩
  · intro u hu
    rw[Q1b]
    by_cases h3:eH u=0
    · by_cases hut:u=t
      · right
        rw[hut]
        exact ⟨rfl,by omega⟩
      · have hL:(if d.lv u=d.lv t then e' u else 0)≠0:=by
          intro h0
          apply hu
          simp only[Pi.add_apply,delta,if_neg hut,h3,add_zero,h0]
        by_cases hc:d.lv u=d.lv t
        · rw[if_pos hc]at hL
          have:=(Q1b d).mp (he'S u hL)
          omega
        · rw[if_neg hc]at hL
          exact absurd rfl hL
    · have:=(Q1b d).mp (hHS u h3)
      omega
  · intro u
    show (if d.lv u=d.lv t then e' u else 0)+delta t k' u+eH u<p^Q1q p d X u
    by_cases hc:d.lv u=d.lv t
    · have hH0:eH u=0:=by
        by_contra hne
        have:=(Q1b d).mp (hHS u hne)
        omega
      by_cases hut:u=t
      · have he0:e' u=0:=by
          by_contra hne
          have:=(Q1b d).mp (he'S u hne)
          rw[hut]at this
          omega
        rw[if_pos hc,he0,hH0,hut]
        simpa[delta] using hk'
      · rw[if_pos hc,hH0]
        simpa[delta,hut] using he'b u
    · have hut:u≠t:= fun h=>hc (by rw[h])
      rw[if_neg hc]
      simpa[delta,hut] using hHb u
  · rw[← Qgv X _ eH h2, ← Qgv X _ (delta t k') h1,Qhw, ← hH,hsplit]
    group
lemma Qgo [Finite G] (hp:p.Prime) (hG:ZB G=p^m) (hd:d.Struct)
    (hlv:∀ t,X t∈lcs G (d.lv t))
    (hdeep:∀ w,1≤w→lcs G w≤ZA (X '' {u | w≤d.lv u})):
    ∀ w j,Qbw p d X w j:=by
  obtain ⟨M,hM⟩:∃ M,∀ u:Fin d.n,d.lv u<M:=
    ⟨Finset.univ.sup d.lv+1,fun u=>Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ u))⟩
  have key:∀ k w,M≤w+k→∀ j,Qbw p d X w j:=by
   intro k
   induction k with
   | zero=>
     intro w hw j
     exact Qm2 d X hp.pos j (fun u=>lt_of_lt_of_le (hM u) (by omega))
   | succ k ih=>
     intro w hw
     have h0:Qbw p d X w 0:=Qmi d X (ih (w+1) (by omega) d.n)
     intro j
     induction j with
     | zero=>exact h0
     | succ j ihj=>exact Qmz d X hp hG hd hlv hdeep ihj h0
  exact fun w j=>key M w (by omega) j
lemma Qhd [Finite G] (hp:p.Prime) (hG:ZB G=p^m)
    (hgen:ZA (ZG X)=⊤) (hlv:∀ t,X t∈lcs G (d.lv t))
    (hdeep:∀ w,1≤w→lcs G w≤ZA (X '' {u | w≤d.lv u})):
    ZB G=p^(∑ t,Q1q p d X t):=by
  have hprod:∏ t∈(Finset.univ:Finset (Fin d.n)),(fun t=>p^Q1q p d X t) t=
      p^(∑ t,Q1q p d X t):=Finset.prod_pow_eq_pow_sum _ _ _
  have hconj:∀ t u,d.prec t u→
      X t *X u*(X t)⁻¹∈ZA (X '' {u | d.prec t u}):=by
    intro t u htu
    have he:X t *X u*(X t)⁻¹=⁅X t,X u⁆*X u:=by
     simp only[commutatorElement_def]
     group
    rw[he]
    refine mul_mem ?_ (ZC ⟨u,htu,rfl⟩)
    have h1:=hdeep (d.lv u+1) (by omega) (Qj (X t) (hlv u))
    refine ZO ?_ h1
    rintro _ ⟨u',hu',rfl⟩
    refine ⟨u',?_,rfl⟩
    have hu'':d.lv u+1≤d.lv u':=hu'
    have htu':d.lv t<d.lv u∨(d.lv t=d.lv u∧u.val<t.val):=htu
    exact Or.inl (by omega)
  have hle:=Q9t X (fun t=>p^Q1q p d X t) (fun t=>pow_pos hp.pos _) d.prec
    d.Qe9 d.Qbr d.Qem (fun t=>Q5x d X hG t) hconj Finset.univ
    (fun _ _ _ _=>Finset.mem_univ _)
  have hge:=Qg4 X (fun t=>p^Q1q p d X t) d.prec d.Qbr d.Qem
    (fun t k hk0 hk=>Qkw d X hp hG t k hk0 hk) Finset.univ
    (fun _ _ _ _=>Finset.mem_univ _)
  rw[Finset.coe_univ,Set.image_univ,hgen,Subgroup.card_top]at hle hge
  rw[← hprod]
  exact le_antisymm hle hge
lemma Qik [Finite G] (hp:p.Prime) (hG:ZB G=p^m) (hd:d.Struct)
    (hgen:ZA (ZG X)=⊤)
    (hdf:∀ t,1≤d.lv t→X t=⁅X (d.df t).1,X (d.df t).2⁆)
    (hdeep:∀ w,1≤w→lcs G w≤ZA (X '' {u | w≤d.lv u})):
    ∃ (b:Fin d.n→Fin d.n→ℕ) (c:Fin d.n→Fin d.n→Fin d.n→ℕ),
      ({ d with a:=Q1q p d X,b:=b,c:= c }:Q5).Valid∧
      ({ d with a:=Q1q p d X,b:=b,c:= c }:Q5).Bounded p∧
      Q2k p ({ d with a:=Q1q p d X,b:=b,c:= c }:Q5) X:=by
  have hlv:=Q5f d hd X hdf
  have hnf:=Qgo d X hp hG hd hlv hdeep
  have hb:∀ t,∃ e:Fin d.n→ℕ,(∀ u,e u≠0→d.prec t u)∧
      (∀ u,e u<p^Q1q p d X u)∧X t^(p^Q1q p d X t)=Q2e X e:=
    fun t=>hnf (d.lv t) t.val _ (Q5x d X hG t)
  have hc:∀ t k,∃ e:Fin d.n→ℕ,(∀ u,e u≠0→d.lv t<d.lv u)∧
      (∀ u,e u<p^Q1q p d X u)∧⁅X t,X k⁆=Q2e X e:=by
   intro t k
   have hmem:⁅X t,X k⁆∈ZA (X '' Q2z d (d.lv t) 0):=by
    have h1:=hdeep (d.lv t+1) (by omega) (Qb (hlv t) (X k))
    refine ZO ?_ h1
    rintro _ ⟨u,hu,rfl⟩
    exact ⟨u,Or.inl hu,rfl⟩
   obtain ⟨e,he1,he2,he3⟩:=hnf _ _ _ hmem
   refine ⟨e,fun u hu=>?_,he2,he3⟩
   have:=(Q1b d).mp (he1 u hu)
   omega
  choose b hb using hb
  choose c hc using hc
  refine ⟨b,c,?_,⟨fun t u=> (hb t).2.1 u,fun t k u=> (hc t k).2.1 u⟩,?_⟩
  · exact ⟨⟨hd.mono,hd.s_le,hd.core,hd.df_lv,hd.df_core,hd.df_one⟩,
      fun t u h=> (hb t).1 u h,fun t k u h=> (hc t k).1 u h⟩
  · exact ⟨Qhd d X hp hG hgen hlv hdeep,hgen,hdf,fun t=> (hb t).2.2,
      fun t k _ _ _=> (hc t k).2.2,fun t k _ _=> (hc t k).2.2,fun t k _ _=> (hc t k).2.2⟩
end Layers
section Frattini
variable {G:Type u} [Group G]
def Qnk (A B:Subgroup G) [B.Normal] (p:ℕ)
    (hc:∀ x∈A,∀ y∈A,ZF B x*ZF B y=
      ZF B y *ZF B x):Subgroup (G⧸B) where
  carrier :={z | ∃ a∈A,z=ZF B a^p}
  mul_mem':=by
    rintro _ _ ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
    show ∃ c∈A,ZF B a^p*ZF B b^p=
      ZF B c^p
    refine ⟨a*b,A.mul_mem ha hb,?_⟩
    rw[map_mul,Commute.mul_pow (hc a ha b hb) p]
  one_mem':=by
    show ∃ c∈A,(1:G⧸B)=ZF B c^p
    exact ⟨1,A.one_mem,by rw[map_one,one_pow]⟩
  inv_mem':=by
    rintro _ ⟨a,ha,rfl⟩
    show ∃ c∈A,(ZF B a^p)⁻¹=ZF B c^p
    exact ⟨a⁻¹,A.inv_mem ha,by rw[map_inv,inv_pow]⟩
lemma Qcc [Finite G] {p m:ℕ} (hp:p.Prime) (hG:ZB G=p^m)
    (A B:Subgroup G) [B.Normal] (hAB:∀ x∈A,∀ y∈A,⁅x,y⁆∈B)
    (h:A≤B⊔ZA (ZG (fun g:A=> (g:G)^p))):A≤B:=by
  classical
  have:Fact p.Prime:=⟨hp⟩
  have:Finite (G⧸B):=Finite.of_surjective _ (QuotientGroup.mk'_surjective B)
  have hker :∀ g:G,ZF B g=1↔g∈B:= fun g=>by
    rw[← MonoidHom.mem_ker,QuotientGroup.ker_mk']
  have hc:∀ x∈A,∀ y∈A,ZF B x*ZF B y=
      ZF B y *ZF B x:=by
   intro x hx y hy
   have h1:ZF B ⁅x,y⁆=1:=(hker _).mpr (hAB x hx y hy)
   rw[map_commutatorElement]at h1
   exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hle:A≤(Qnk A B p hc).comap (ZF B):=by
   refine h.trans (sup_le ?_ ?_)
   · intro b hb
     show ∃ a'∈A,ZF B b=ZF B a' ^p
     exact ⟨1,A.one_mem,by rw[map_one,one_pow,(hker b).mpr hb]⟩
   · rw[ZD]
     rintro _ ⟨g,rfl⟩
     show ∃ a'∈A,ZF B ((g:G)^p)=ZF B a' ^p
     exact ⟨g,g.2,by rw[map_pow]⟩
  have hAQ:∀ a∈A,∃ a'∈A,ZF B a=ZF B a' ^p:=
    fun a ha=>hle ha
  have hsurj:Function.Surjective (fun z:A.map (ZF B)=>
      (⟨(z:G⧸B)^p,pow_mem z.2 p⟩:A.map (ZF B))):=by
    rintro ⟨y,hy⟩
    obtain ⟨a,ha,rfl⟩:=Subgroup.mem_map.mp hy
    obtain ⟨a',ha',he⟩:=hAQ a ha
    exact ⟨⟨ZF B a',Subgroup.mem_map_of_mem _ ha'⟩,Subtype.ext he.symm⟩
  have hinj:=Finite.injective_iff_surjective.mpr hsurj
  intro a ha
  rw[← hker]
  by_contra hne
  obtain ⟨k,hk⟩:=(IsPGroup.of_card hG).to_quotient B (ZF B a)
  have hex:∃ k,ZF B a^p^k=1:=⟨k,hk⟩
  obtain ⟨k0,hspec,hmin⟩:∃ k0,ZF B a^p^k0=1∧
      ∀ j<k0,ZF B a^p^j≠1:=
    ⟨Nat.find hex,Nat.find_spec hex,fun j hj=>Nat.find_min hex hj⟩
  have hk0:k0≠0:=by
   rintro rfl
   rw[pow_zero,pow_one]at hspec
   exact hne hspec
  have hz:(ZF B a^p^(k0 - 1))^p=1:=by
   rw[← pow_mul, ← pow_succ,show k0 - 1+1=k0 by omega,hspec]
  have hzA:ZF B a^p^(k0 - 1)∈A.map (ZF B):=
    pow_mem (Subgroup.mem_map_of_mem _ ha) _
  have heq:(⟨_,hzA⟩:A.map (ZF B))=⟨1,one_mem _⟩:=by
   apply hinj
   apply Subtype.ext
   show (ZF B a^p^(k0 - 1))^p=(1:G⧸B)^p
   rw[hz,one_pow]
  exact hmin (k0 - 1) (by omega) (congrArg Subtype.val heq)
def Q15 (p:ℕ) (G:Type u) [Group G]:ℕ→ Subgroup G
  | 0=>Qv p G
  | w+1=>lcs G (w+2)⊔ZA (ZG (fun g:lcs G (w+1)=> (g:G)^p))
lemma Q16 (p:ℕ):∀ w,lcs G (w+1)≤Q15 p G w
  | 0=>by
    show lcs G 1≤Qv p G
    rw[← Q1s]
    exact le_sup_right
  | _+1=>le_sup_left
lemma Q7l (p:ℕ) (w:ℕ):Q15 p G (w+1)≤lcs G (w+1):=by
 show lcs G (w+2)⊔ZA (ZG (fun g:lcs G (w+1)=> (g:G)^p))≤
   lcs G (w+1)
 refine sup_le (Qd (by omega)) ?_
 rw[ZD]
 rintro _ ⟨g,rfl⟩
 exact pow_mem g.2 p
lemma Q98 (p:ℕ):∀ (w:ℕ) (x:G),x∈lcs G w→x^p∈Q15 p G w
  | 0,x,_=>Q2c p x
  | w+1,x,hx =>ZL (ZC ⟨⟨x,hx⟩,rfl⟩)
lemma Q47 (p:ℕ) (w:ℕ) (T:Set G) (hT:T⊆lcs G w):
    (ZA T⊔Q15 p G w).Normal:=by
 rcases w with _ | w
 · exact Q6r ((Q16 p 0).trans le_sup_right)
 · exact Q1d (n:=w+1) ((Q16 p (w+1)).trans le_sup_right)
     (sup_le ((ZD _).mpr hT) (Q7l p w))
lemma Qbk [Finite G] {p m:ℕ} (hp:p.Prime) (hG:ZB G=p^m) (w:ℕ)
    (T:Set G) (hT:T⊆lcs G (w+1))
    (h:lcs G (w+1)≤ZA T⊔Q15 p G (w+1)):
    lcs G (w+1)≤ZA T⊔lcs G (w+2):=by
 have hN:(ZA T⊔lcs G (w+2)).Normal:=
   Q1d (n:=w+1) le_sup_right
     (sup_le ((ZD _).mpr hT) (Qd (by omega)))
 refine Qcc hp hG (lcs G (w+1)) _ ?_ ?_
 · intro x hx y hy
   have h1:=Q1c hx hy
   exact ZL
     (Qd (D:=G) (show w+2≤w+1+(w+1)+1 by omega) h1)
 · rw[sup_assoc]
   exact h
lemma Q5s [Finite G] {p:ℕ} (hp:0<p) (M:Subgroup G) (x:ℕ→G)
    (hN:∀ j,(ZA (x '' ZP j)⊔M).Normal) (hMp:∀ j,x j^p∈M):
    ∀ j,ZB (ZA (x '' ZP j)⊔M:Subgroup G)≤p^j*ZB M:=by
 intro j
 induction j with
 | zero=>
   have hle:ZA (x '' ZP 0)⊔M≤M:=by
    refine sup_le ?_ le_rfl
    rw[ZD]
    rintro _ ⟨i,hi,rfl⟩
    exact absurd (Set.mem_Iio.mp hi) (Nat.not_lt_zero i)
   rw[pow_zero,one_mul]
   exact Subgroup.card_le_of_le hle
 | succ j ih=>
   have:=hN j
   have hle:ZA (x '' ZP (j+1))⊔M≤
       (ZA (x '' ZP j)⊔M)⊔Subgroup.zpowers (x j):=by
    refine sup_le ?_ (le_sup_right.trans le_sup_left)
    rw[ZD]
    rintro _ ⟨i,hi,rfl⟩
    have hi':i<j+1:=Set.mem_Iio.mp hi
    by_cases hij:i<j
    · exact ZJ (ZJ
        (ZC ⟨i,Set.mem_Iio.mpr hij,rfl⟩))
    · rw[show i=j by omega]
      exact ZL (Subgroup.mem_zpowers (x j))
   have h1:=Subgroup.card_le_of_le hle
   have h2:=Q79 (K:=ZA (x '' ZP j)⊔M) hp
     (ZL (hMp j))
   have h3:p*ZB (ZA (x '' ZP j)⊔M:Subgroup G)≤
       p*(p^j*ZB M):=Nat.mul_le_mul le_rfl ih
   have e:p*(p^j*ZB M)=p^(j+1)*ZB M:=by
    rw[pow_succ]
    ring
   rw[← e]
   exact h1.trans (h2.trans h3)
end Frattini
section Greedy
variable {G:Type u} [Group G]
open Classical in
noncomputable def Qz (c:ℕ→G) (K:Subgroup G):ℕ→Finset ℕ
  | 0=> ∅
  | j +1=>if c j∈ZA (c '' (Qz c K j:Set ℕ))⊔K then Qz c K j
      else insert j (Qz c K j)
lemma Q6z (c:ℕ→G) (K:Subgroup G) (j:ℕ):
    (Qz c K (j+1)=Qz c K j∧
      c j∈ZA (c '' (Qz c K j:Set ℕ))⊔K)∨
    (Qz c K (j+1)=insert j (Qz c K j)∧
      c j∉ZA (c '' (Qz c K j:Set ℕ))⊔K):=by
 by_cases h:c j∈ZA (c '' (Qz c K j:Set ℕ))⊔K
 · left
   refine ⟨?_,h⟩
   simp only[Qz,if_pos h]
 · right
   refine ⟨?_,h⟩
   simp only[Qz,if_neg h]
lemma Q68 (c:ℕ→G) (K:Subgroup G):∀ j,∀ i∈Qz c K j,i<j
  | 0,i,hi=>by simp[Qz]at hi
  | j +1,i,hi=>by
    rcases Q6z c K j with ⟨h, -⟩ | ⟨h, -⟩
    · rw[h]at hi
      exact Nat.lt_succ_of_lt (Q68 c K j i hi)
    · rw[h,Finset.mem_insert]at hi
      rcases hi with rfl | hi
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt (Q68 c K j i hi)
lemma Q6s (c:ℕ→G) (K:Subgroup G):
    ∀ d j i,i<j→(i∈Qz c K (j+d)↔i∈Qz c K j)
  | 0,_,_,_=>Iff.rfl
  | d + 1,j,i,hij=>by
    rw[← Q6s c K d j i hij,show j+(d+1)=j+d+1 by omega]
    rcases Q6z c K (j+d) with ⟨h, -⟩ | ⟨h, -⟩
    · rw[h]
    · rw [h,Finset.mem_insert]
      constructor
      · rintro (h' | h')
        · exact absurd h' (by omega)
        · exact h'
      · exact Or.inr
lemma Qhv (c:ℕ→G) (K:Subgroup G):
    ∀ j,∀ i<j,c i∈ZA (c '' (Qz c K j:Set ℕ))⊔K
  | 0,i,hi=>absurd hi (Nat.not_lt_zero i)
  | j + 1,i,hi=>by
    have hmono:ZA (c '' (Qz c K j:Set ℕ))⊔K≤
        ZA (c '' (Qz c K (j+1):Set ℕ))⊔K:=by
     refine sup_le_sup_right (ZO (Set.image_mono ?_)) K
     intro x hx
     rcases Q6z c K j with ⟨h, -⟩ | ⟨h, -⟩
     · rw[h]
       exact hx
     · rw[h,Finset.coe_insert]
       exact Set.mem_insert_of_mem _ hx
    by_cases hij:i<j
    · exact hmono (Qhv c K j i hij)
    · have hij':i=j:=by omega
      subst hij'
      rcases Q6z c K i with ⟨-,h'⟩ | ⟨h, -⟩
      · exact hmono h'
      · refine ZJ (ZC ⟨i,?_,rfl⟩)
        rw[h,Finset.coe_insert]
        exact Set.mem_insert _ _
lemma Qlb (c:ℕ→G) (K:Subgroup G) {j i:ℕ} (hi:i∈Qz c K j):
    c i∉ZA (c '' (Qz c K i:Set ℕ))⊔K:=by
 have hij:=Q68 c K j i hi
 obtain ⟨d,rfl⟩:∃ d,j=i+1+d:=⟨j - (i+1),by omega⟩
 have h1:i∈Qz c K (i+1):=
   (Q6s c K d (i+1) i (Nat.lt_succ_self i)).mp hi
 rcases Q6z c K i with ⟨h, -⟩ | ⟨-,h'⟩
 · rw[h]at h1
   exact absurd (Q68 c K i i h1) (lt_irrefl i)
 · exact h'
noncomputable def Q1i (S:Finset ℕ) (i:ℕ):ℕ:=
  if h:i<S.card then S.orderEmbOfFin rfl ⟨i,h⟩ else 0
lemma Q9z (S:Finset ℕ) {i:ℕ} (h:i<S.card):Q1i S i∈S:=by
 unfold Q1i
 rw[dif_pos h]
 exact Finset.orderEmbOfFin_mem S rfl _
lemma Qbs (S:Finset ℕ) {i j:ℕ} (hij:i<j) (hj:j<S.card):
    Q1i S i<Q1i S j:=by
 unfold Q1i
 rw[dif_pos (lt_trans hij hj),dif_pos hj]
 exact (S.orderEmbOfFin rfl).strictMono (Fin.mk_lt_mk.mpr hij)
lemma Qmu (S:Finset ℕ) {i j:ℕ} (hij:i≤j) (hj:j<S.card):
    Q1i S i≤Q1i S j:=by
 rcases Nat.lt_or_ge i j with h | h
 · exact (Qbs S h hj).le
 · have hij':i=j:=by omega
   subst hij'
   exact le_rfl
lemma Qmb (S:Finset ℕ) {i j:ℕ} (hi:i<S.card) (hj:j<S.card)
    (h:Q1i S i=Q1i S j):i=j:=by
 rcases lt_trichotomy i j with h' | h' | h'
 · exact absurd h (Qbs S h' hj).ne
 · exact h'
 · exact absurd h (Qbs S h' hi).ne'
lemma Qkj (S:Finset ℕ) {x:ℕ} (hx:x∈S):∃ i<S.card,Q1i S i=x:=by
 have hr :x∈ZG (S.orderEmbOfFin rfl):=by
  rw[Finset.range_orderEmbOfFin]
  exact hx
 obtain ⟨⟨i,hi⟩,rfl⟩:=hr
 refine ⟨i,hi,?_⟩
 unfold Q1i
 rw[dif_pos hi]
structure Q4w (G:Type u) where
  r :ℕ
  x:ℕ→G
  par :ℕ→ℕ
  cor :ℕ→ℕ
noncomputable def Q34 (c:ℕ→G) (K:Subgroup G) (N:ℕ) (pa co:ℕ→ℕ):Q4w G where
  r :=(Qz c K N).card
  x:= fun i=>if i< (Qz c K N).card then c (Q1i (Qz c K N) i) else 1
  par := fun i=>pa (Q1i (Qz c K N) i)
  cor := fun i=>co (Q1i (Qz c K N) i)
variable (c:ℕ→G) (K:Subgroup G) (N:ℕ) (pa co:ℕ→ℕ)
lemma Qcx {i:ℕ} (hi:i< (Qz c K N).card):
    (Q34 c K N pa co).x i= c (Q1i (Qz c K N) i):=if_pos hi
lemma Qjm (i:ℕ):
    (Q34 c K N pa co).x i= c (Q1i (Qz c K N) i)∨(Q34 c K N pa co).x i=1:=by
 by_cases hi:i< (Qz c K N).card
 · exact Or.inl (if_pos hi)
 · exact Or.inr (if_neg hi)
lemma Qcu {i i':ℕ} (hi:i< (Qz c K N).card) (hi':i'< i):
    Q1i (Qz c K N) i'∈Qz c K (Q1i (Qz c K N) i):=by
 have h1:=Qbs (Qz c K N) hi' hi
 have h2:=Q68 c K N _ (Q9z _ hi)
 have h3:=Q9z (Qz c K N) (lt_trans hi' hi)
 have h4:=Q6s c K (N - Q1i (Qz c K N) i) (Q1i (Qz c K N) i) _ h1
 rw[show Q1i (Qz c K N) i+(N - Q1i (Qz c K N) i)=N by omega]at h4
 exact h4.mp h3
lemma Q8n {i:ℕ} (hi:i< (Q34 c K N pa co).r):
    (Q34 c K N pa co).x i∉ZA ((Q34 c K N pa co).x '' ZP i)⊔K:=by
 intro hmem
 have hi':i< (Qz c K N).card:=hi
 rw[Qcx c K N pa co hi']at hmem
 apply Qlb c K (Q9z (Qz c K N) hi')
 refine (sup_le_sup_right (ZO ?_) K) hmem
 rintro _ ⟨i',hi'',rfl⟩
 have hi''':i'< i:=hi''
 refine ⟨Q1i (Qz c K N) i',Qcu c K N hi' hi''',?_⟩
 exact (Qcx c K N pa co (lt_trans hi''' hi')).symm
lemma Qd5 {J:ℕ} (hJ:J≤N) {j:ℕ} (hj:j<J):
    c j∈ZA ((Q34 c K N pa co).x ''
      {i | i< (Qz c K N).card∧Q1i (Qz c K N) i<J})⊔K:=by
  refine (sup_le_sup_right (ZO ?_) K) (Qhv c K J j hj)
  rintro _ ⟨y,hy,rfl⟩
  have hyJ:y<J:=Q68 c K J y hy
  have hyS:y∈Qz c K N:=by
   have h1:=Q6s c K (N - J) J y hyJ
   rw[show J+(N - J)=N by omega]at h1
   exact h1.mpr hy
  obtain ⟨i,hi,rfl⟩:=Qkj _ hyS
  exact ⟨i,⟨hi,hyJ⟩,Qcx c K N pa co hi⟩
lemma Qil {j:ℕ} (hj:j<N):
    c j∈ZA ((Q34 c K N pa co).x '' ZP (Q34 c K N pa co).r)⊔K:=by
 refine (sup_le_sup_right (ZO ?_) K) (Qd5 c K N pa co le_rfl hj)
 rintro _ ⟨i,⟨hi, -⟩,rfl⟩
 exact ⟨i,hi,rfl⟩
end Greedy
section TheoremL
variable {G:Type u} [Group G]
def Q8t (s:ℕ) (u:ℕ→G):ℕ→ Set G
  | 0=> ∅
  | 1=> (fun ab:ℕ×ℕ=> ⁅u ab.1,u ab.2⁆) '' {ab | ab.1<ab.2∧ab.2<s}
  | w+2=> {x | ∃ y∈ZA (Q8t s u (w+1)),∃ b<s,x =⁅y,u b⁆}
lemma Qer (s:ℕ) (u:ℕ→G):∀ w,Q8t s u (w+1)⊆(lcs G (w+1):Set G)
  | 0=>by
    rintro _ ⟨ab, -,rfl⟩
    exact Qo _ _
  | w+1=>by
    rintro _ ⟨y,hy,b, -,rfl⟩
    have hy':y∈lcs G (w+1):=(ZD _).mpr (Qer s u w) hy
    exact Qb hy' _
lemma Qmr (s:ℕ) (u:ℕ→G) (H1:Set G)
    (hL0:ZA H1⊔lcs G 1=⊤)
    (hcore:lcs G 1≤ZA (Q8t s u 1)⊔lcs G 2):
    ∀ w,1≤w→lcs G w≤ZA (Q8t s u w)⊔lcs G (w+1):=by
 refine Qho s u H1 {ab | ab.1<ab.2∧ab.2<s} (Q8t s u) (fun ab hab=>hab) rfl
   ?_ hL0 ?_ ?_ ?_
 · intro w hw x hx
   obtain ⟨w',rfl⟩:∃ w',w=w'+1:=⟨w - 1,by omega⟩
   exact hx
 · intro x _ y _
   exact hcore (Qo x y)
 · intro ab hab k hk
   have hk':k<s:=lt_of_le_of_lt hk hab.2
   refine ZJ (ZC ?_)
   show ⁅⁅u ab.1,u ab.2⁆,u k⁆∈Q8t s u (0+2)
   exact ⟨⁅u ab.1,u ab.2⁆,ZC ⟨ab,hab,rfl⟩,k,hk',rfl⟩
 · intro w hw x hx k hk
   obtain ⟨w',rfl⟩:∃ w',w=w'+1:=⟨w - 1,by omega⟩
   refine ZJ (ZC ?_)
   show ⁅x,u k⁆∈Q8t s u (w'+2)
   exact ⟨x,ZC hx,k,hk,rfl⟩
end TheoremL
section Layers2
variable {G:Type u} [Group G]
def Q20 (s w j:ℕ):ℕ:=if w=0 then j % s else j/s
def Q1x (s w j:ℕ):ℕ:=if w=0 then j/s else j % s
def Q1a (s:ℕ) (u:ℕ→G) (w:ℕ) (L:Q4w G) (j:ℕ):G:=
  if (w=0∧¬ Q20 s w j<Q1x s w j)∨(w=1∧L.cor (Q20 s w j)<Q1x s w j) then 1
  else ⁅L.x (Q20 s w j),u (Q1x s w j)⁆
def cN (s w:ℕ) (L:Q4w G):ℕ:=if w=0 then s*s else L.r*s
lemma Q9g {s j:ℕ}:Q20 s 0 j=j % s:=if_pos rfl
lemma Q7z {s j:ℕ}:Q1x s 0 j=j/s:=if_pos rfl
lemma Qkf {s:ℕ} {L:Q4w G}:cN s 0 L=s*s:=if_pos rfl
lemma Qha {s w j:ℕ} (hw:w≠0):Q20 s w j=j/s:=if_neg hw
lemma Qh0 {s w j:ℕ} (hw:w≠0):Q1x s w j=j % s:=if_neg hw
lemma Qn2 {s w:ℕ} {L:Q4w G} (hw:w≠0):cN s w L=L.r*s:=if_neg hw
lemma Qmg (s:ℕ) (u:ℕ→G) (w:ℕ) (L:Q4w G) (j:ℕ)
    (h:¬ (w=0∧L.cor (j/s)<j % s)):
    Q1a s u (w+1) L j=⁅L.x (j/s),u (j % s)⁆:=by
 unfold Q1a
 have hn:¬ ((w+1=0∧¬ Q20 s (w+1) j<Q1x s (w+1) j)∨
     (w+1=1∧L.cor (Q20 s (w+1) j)<Q1x s (w+1) j)):=by
  rintro (h' | h')
  · exact absurd h'.1 (by omega)
  · rw[Qha (show w+1≠0 by omega),Qh0 (show w+1≠0 by omega)]at h'
    obtain ⟨h1',h2'⟩:=h'
    exact h ⟨by omega,h2'⟩
 rw[if_neg hn,Qha (show w+1≠0 by omega),Qh0 (show w+1≠0 by omega)]
lemma Qfp (s:ℕ) (u:ℕ→G) (L:Q4w G) {j:ℕ} (h:j % s<j/s):
    Q1a s u 0 L j=⁅L.x (j % s),u (j/s)⁆:=by
 unfold Q1a
 have hn:¬ (((0:ℕ)=0∧¬ Q20 s 0 j<Q1x s 0 j)∨
     ((0:ℕ)=1∧L.cor (Q20 s 0 j)<Q1x s 0 j)):=by
  rintro (h' | h')
  · exact h'.2 (by rw[Q9g,Q7z]; exact h)
  · exact Nat.zero_ne_one h'.1
 rw[if_neg hn,Q9g,Q7z]
lemma Qkb {s A a b:ℕ} (ha:a<A) (hb:b<s):a*s+b<A*s:=
  lt_of_lt_of_le (Nat.add_lt_add_left hb _)
    (by rw[← Nat.succ_mul]; exact Nat.mul_le_mul_right _ ha)
lemma Qbg {s a b:ℕ} (hb:b<s):(a*s+b)/s=a:=by
 rw[add_comm,Nat.add_mul_div_right _ _ (by omega:0<s),Nat.div_eq_of_lt hb,zero_add]
lemma Qbt {s a b:ℕ} (hb:b<s):(a*s+b) % s=b:=by
 rw[add_comm,Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hb]
lemma Qi8 (s:ℕ) (u:ℕ→G) (hs:0<s) (w:ℕ) (L:Q4w G)
    (hr :w=0→s≤L.r) (K:Subgroup G) {i:ℕ}
    (hi:i< (Q34 (Q1a s u w L) K (cN s w L) (Q20 s w) (Q1x s w)).r):
    (Q34 (Q1a s u w L) K (cN s w L) (Q20 s w) (Q1x s w)).par i<L.r∧
    (Q34 (Q1a s u w L) K (cN s w L) (Q20 s w) (Q1x s w)).cor i<s∧
    (w =0→(Q34 (Q1a s u w L) K (cN s w L) (Q20 s w) (Q1x s w)).par i<
      (Q34 (Q1a s u w L) K (cN s w L) (Q20 s w) (Q1x s w)).cor i)∧
    (Q34 (Q1a s u w L) K (cN s w L) (Q20 s w) (Q1x s w)).x i=
      ⁅L.x ((Q34 (Q1a s u w L) K (cN s w L) (Q20 s w) (Q1x s w)).par i),
        u ((Q34 (Q1a s u w L) K (cN s w L) (Q20 s w) (Q1x s w)).cor i)⁆:=by
 have hind:=Q8n (Q1a s u w L) K (cN s w L) (Q20 s w) (Q1x s w) hi
 have hi':i< (Qz (Q1a s u w L) K (cN s w L)).card:=hi
 have hj:=Q68 (Q1a s u w L) K (cN s w L) _ (Q9z _ hi')
 have hx:=Qcx (Q1a s u w L) K (cN s w L) (Q20 s w) (Q1x s w) hi'
 have hne:Q1a s u w L (Q1i (Qz (Q1a s u w L) K (cN s w L)) i)≠1:=by
  intro h1
  apply hind
  rw[hx,h1]
  exact one_mem _
 have e1:(Q34 (Q1a s u w L) K (cN s w L) (Q20 s w) (Q1x s w)).par i=
     Q20 s w (Q1i (Qz (Q1a s u w L) K (cN s w L)) i):=rfl
 have e2:(Q34 (Q1a s u w L) K (cN s w L) (Q20 s w) (Q1x s w)).cor i=
     Q1x s w (Q1i (Qz (Q1a s u w L) K (cN s w L)) i):=rfl
 rw[e1,e2,hx]
 generalize Q1i (Qz (Q1a s u w L) K (cN s w L)) i=j at hj hne⊢
 have hcv2:¬ ((w=0∧¬ Q20 s w j<Q1x s w j)∨
     (w=1∧L.cor (Q20 s w j)<Q1x s w j)):=by
  intro hc
  apply hne
  unfold Q1a
  rw[if_pos hc]
 have hcv:¬ (w=0∧¬ Q20 s w j<Q1x s w j):= fun hc=>hcv2 (Or.inl hc)
 have hval:Q1a s u w L j=⁅L.x (Q20 s w j),u (Q1x s w j)⁆:=by
  unfold Q1a
  rw[if_neg hcv2]
 refine ⟨?_,?_,?_,hval⟩
 · by_cases hw:w=0
   · subst hw
     rw[Q9g]
     have h1:j % s<s:=Nat.mod_lt _ hs
     have h2:=hr rfl
     omega
   · rw[Qn2 hw]at hj
     rw[Qha hw]
     exact (Nat.div_lt_iff_lt_mul hs).mpr hj
 · by_cases hw:w=0
   · subst hw
     rw[Qkf]at hj
     rw[Q7z]
     exact (Nat.div_lt_iff_lt_mul hs).mpr hj
   · rw[Qh0 hw]
     exact Nat.mod_lt _ hs
 · intro hw
   by_contra hc
   exact hcv ⟨hw,hc⟩
lemma Qiz (s:ℕ) (u:ℕ→G) (L:Q4w G) (K:Subgroup G) {i:ℕ}
    (hi:i< (Q34 (Q1a s u 1 L) K (cN s 1 L) (Q20 s 1) (Q1x s 1)).r):
    ¬ L.cor ((Q34 (Q1a s u 1 L) K (cN s 1 L) (Q20 s 1) (Q1x s 1)).par i)<
      (Q34 (Q1a s u 1 L) K (cN s 1 L) (Q20 s 1) (Q1x s 1)).cor i:=by
 have hind:=Q8n (Q1a s u 1 L) K (cN s 1 L) (Q20 s 1) (Q1x s 1) hi
 have hi':i< (Qz (Q1a s u 1 L) K (cN s 1 L)).card:=hi
 have hx:=Qcx (Q1a s u 1 L) K (cN s 1 L) (Q20 s 1) (Q1x s 1) hi'
 intro hlt
 apply hind
 rw[hx]
 have hc:((1:ℕ)=0∧¬ Q20 s 1 (Q1i (Qz (Q1a s u 1 L) K (cN s 1 L)) i)<
     Q1x s 1 (Q1i (Qz (Q1a s u 1 L) K (cN s 1 L)) i))∨
     ((1:ℕ)=1∧L.cor (Q20 s 1 (Q1i (Qz (Q1a s u 1 L) K (cN s 1 L)) i))<
       Q1x s 1 (Q1i (Qz (Q1a s u 1 L) K (cN s 1 L)) i)):= Or.inr ⟨rfl,hlt⟩
 have h1:Q1a s u 1 L (Q1i (Qz (Q1a s u 1 L) K (cN s 1 L)) i)=1:=if_pos hc
 rw[h1]
 exact one_mem _
lemma Qab (g y:G) (hg:g∈lcs G 1) (n:ℕ):
    ⁅g^n,y⁆*(⁅g,y⁆^n)⁻¹∈lcs G 3:=by
 induction n with
 | zero=>simp
 | succ n ih=>
   have hc:⁅g,⁅g^n,y⁆⁆∈lcs G 3:=
     Qd (show 3≤1+(1+1)+1 by omega)
       (Q1c hg (Qb (pow_mem hg n) y))
   have e:⁅g^(n+1),y⁆*(⁅g,y⁆^(n+1))⁻¹=
       ⁅g,⁅g^n,y⁆⁆*(⁅g^n,y⁆*(⁅g,y⁆^n)⁻¹):=by
    rw[pow_succ' g n,Q2g,pow_succ]
    group
   rw[e]
   exact Subgroup.mul_mem _ hc ih
lemma Qim (p:ℕ) (z:G) (hz:z∈Q15 p G 1) (g:G):⁅z,g⁆∈Q15 p G 2:=by
 haveI:(Q15 p G 2).Normal:=
   Q1d (n:=2) (Q16 p 2) (Q7l p 1)
 have hle:Q15 p G 1≤zn (Q15 p G 2) g:=by
  show lcs G 2⊔ZA (ZG (fun y:lcs G 1=> (y:G)^p))≤_
  refine sup_le ?_ ?_
  · intro x hx
    exact Q4p.mpr (Q16 p 2 (Qj g hx))
  · rw [ZD]
    rintro _ ⟨y,rfl⟩
    apply Q4p.mpr
    apply Qr
    have h1:=Qab (y:G) g y.2 p
    have h2:⁅(y:G),g⁆^p∈Q15 p G 2:=
      Q98 p 2 _ (Qb y.2 g)
    have e:⁅(y:G)^p,g⁆=⁅(y:G)^p,g⁆*(⁅(y:G),g⁆^p)⁻¹*⁅(y:G),g⁆^p:=by
     group
    rw[e]
    exact Subgroup.mul_mem _ (Q16 p 2 h1) h2
 exact Qr (Q4p.mp (hle hz))
noncomputable def Qm (p s:ℕ) (u:ℕ→G) (L0:Q4w G):ℕ→Q4w G
  | 0=>L0
  | w +1=>Q34 (Q1a s u w (Qm p s u L0 w)) (Q15 p G (w+1)) (cN s w (Qm p s u L0 w))
      (Q20 s w) (Q1x s w)
variable (p s:ℕ) (u:ℕ→G) (L0:Q4w G)
lemma Qa0 (w:ℕ):
    Qm p s u L0 (w+1)=Q34 (Q1a s u w (Qm p s u L0 w)) (Q15 p G (w+1))
      (cN s w (Qm p s u L0 w)) (Q20 s w) (Q1x s w):=rfl
lemma Qec:
    Qm p s u L0 1=Q34 (Q1a s u 0 L0) (Q15 p G 1) (cN s 0 L0) (Q20 s 0) (Q1x s 0):=rfl
lemma Q7i:∀ w i,(Qm p s u L0 w).x i∈lcs G w
  | 0,i=>by
    rw[lcs_zero]
    exact ZM _
  | w + 1,i=>by
    rw[Qa0]
    rcases Qjm (Q1a s u w (Qm p s u L0 w)) (Q15 p G (w+1))
        (cN s w (Qm p s u L0 w)) (Q20 s w) (Q1x s w) i with h | h
    · rw[h]
      unfold Q1a
      split_ifs
      · exact one_mem _
      · exact Qb (Q7i w _) _
    · rw[h]
      exact one_mem _
lemma Qle (w:ℕ) {i:ℕ} (hi:i< (Qm p s u L0 (w+1)).r):
    (Qm p s u L0 (w+1)).x i∉
      ZA ((Qm p s u L0 (w+1)).x '' ZP i)⊔Q15 p G (w+1):=by
 rw[Qa0]at hi⊢
 exact Q8n _ _ _ _ _ hi
lemma Q9a (hs:0<s) (hr0:s≤L0.r) (w:ℕ) {i:ℕ}
    (hi:i< (Qm p s u L0 (w+1)).r):
    (Qm p s u L0 (w+1)).par i< (Qm p s u L0 w).r∧(Qm p s u L0 (w+1)).cor i<s∧
    (w=0→(Qm p s u L0 (w+1)).par i< (Qm p s u L0 (w+1)).cor i)∧
    (Qm p s u L0 (w+1)).x i=⁅(Qm p s u L0 w).x ((Qm p s u L0 (w+1)).par i),
      u ((Qm p s u L0 (w+1)).cor i)⁆:=by
 rw[Qa0]at hi⊢
 exact Qi8 s u hs w (Qm p s u L0 w) (fun hw=>by subst hw; exact hr0) _ hi
lemma Qbb (hs:0<s) (w:ℕ) {a b:ℕ} (ha:a< (Qm p s u L0 (w+1)).r)
    (hb:b<s) (hw:¬ (w=0∧(Qm p s u L0 (w+1)).cor a<b)):
    ⁅(Qm p s u L0 (w+1)).x a,u b⁆∈ZA ((Qm p s u L0 (w+1+1)).x ''
      ZP (Qm p s u L0 (w+1+1)).r)⊔Q15 p G (w+1+1):=by
 have hj:a*s+b<cN s (w+1) (Qm p s u L0 (w+1)):=by
  rw[Qn2 (show w+1≠0 by omega)]
  exact Qkb ha hb
 have hv:Q1a s u (w+1) (Qm p s u L0 (w+1)) (a*s+b)=
     ⁅(Qm p s u L0 (w+1)).x a,u b⁆:=by
  have hw':¬ (w=0∧(Qm p s u L0 (w+1)).cor ((a*s+b)/s)< (a*s+b) % s):=by
   rw[Qbg hb,Qbt hb]
   exact hw
  rw[Qmg s u w _ _ hw',Qbg hb,Qbt hb]
 rw[← hv,Qa0 p s u L0 (w+1)]
 exact Qil _ _ _ _ _ hj
lemma Qne {i:ℕ} (hi:i< (Qm p s u L0 2).r):
    (Qm p s u L0 2).cor i≤(Qm p s u L0 1).cor ((Qm p s u L0 2).par i):=
  not_lt.mp (Qiz s u (Qm p s u L0 1) (Q15 p G 2) (i:=i) hi)
lemma Q62 (hs:0<s) (hx0:∀ a<s,L0.x a=u a) {k:ℕ} (hk:k≤ s)
    {a b:ℕ} (hab:a<b) (hb:b<k):
    ⁅u a,u b⁆∈ZA ((Qm p s u L0 1).x ''
      {i | i< (Qm p s u L0 1).r∧(Qm p s u L0 1).cor i<k})⊔Q15 p G 1:=by
  have hbs:b<s:=lt_of_lt_of_le hb hk
  have has:a<s:=lt_trans hab hbs
  have hJ:k*s≤ cN s 0 L0:=by
   rw[Qkf]
   exact Nat.mul_le_mul_right s hk
  have hj:b*s+a<k*s:=Qkb hb has
  have hv:Q1a s u 0 L0 (b*s+a)=⁅u a,u b⁆:=by
   rw [Qfp s u L0 (j:=b*s+a) (by rw[Qbt has,Qbg has]; exact hab),
     Qbt has,
     Qbg has,hx0 a has]
  rw[← hv,Qec]
  refine (sup_le_sup_right (ZO ?_) _)
    (Qd5 (Q1a s u 0 L0) (Q15 p G 1) (cN s 0 L0) (Q20 s 0) (Q1x s 0) hJ hj)
  rintro _ ⟨i,⟨hi,hik⟩,rfl⟩
  refine ⟨i,⟨hi,?_⟩,rfl⟩
  show Q1x s 0 (Q1i _ i)<k
  rw[Q7z]
  exact (Nat.div_lt_iff_lt_mul hs).mpr hik
lemma Qib (hs:0<s) (hr0:s≤L0.r) (hx0:∀ a<s,L0.x a=u a):
    ∀ b,b<s→∀ a,a< (Qm p s u L0 1).r→⁅(Qm p s u L0 1).x a,u b⁆∈
      ZA ((Qm p s u L0 2).x '' ZP (Qm p s u L0 2).r)⊔Q15 p G 2:=by
 intro b
 induction b using Nat.strong_induction_on with
 | _ b ih =>
   intro hb a ha
   have hN:(ZA ((Qm p s u L0 2).x '' ZP (Qm p s u L0 2).r)⊔
       Q15 p G 2).Normal:=
     Q47 p 2 _ (by rintro _ ⟨i, -,rfl⟩; exact Q7i p s u L0 2 i)
   by_cases hab:(Qm p s u L0 1).cor a<b
   · have hg:=Q9a p s u L0 hs hr0 0 ha
     have hk:(Qm p s u L0 1).cor a<s:=hg.2.1
     have hfk:(Qm p s u L0 1).par a< (Qm p s u L0 1).cor a:=hg.2.2.1 rfl
     have hxa:(Qm p s u L0 1).x a=
         ⁅L0.x ((Qm p s u L0 1).par a),u ((Qm p s u L0 1).cor a)⁆:=hg.2.2.2
     rw[hx0 ((Qm p s u L0 1).par a) (by omega)]at hxa
     rw[hxa]
     have hKn:(ZA ((Qm p s u L0 1).x '' {i | i< (Qm p s u L0 1).r∧
         (Qm p s u L0 1).cor i<b+1})⊔Q15 p G 1).Normal:=
       Q47 p 1 _ (by rintro _ ⟨i, -,rfl⟩; exact Q7i p s u L0 1 i)
     have hKM:∀ c,c<b→∀ z∈ZA ((Qm p s u L0 1).x '' {i |
         i< (Qm p s u L0 1).r∧(Qm p s u L0 1).cor i<b+1})⊔Q15 p G 1,
         ⁅z,u c⁆∈ZA ((Qm p s u L0 2).x '' ZP (Qm p s u L0 2).r)⊔
           Q15 p G 2:=by
       intro c hc
       haveI:=hN
       refine Q3s ?_ ?_
       · rintro _ ⟨i,⟨hi, -⟩,rfl⟩
         exact ih c hc (by omega) i hi
       · intro z hz
         exact ZL (Qim p z hz (u c))
     haveI:=hN
     haveI:=hKn
     exact Q7u _ _ _
       (Q62 p s u L0 hs hx0 (show b+1≤ s by omega) hab (Nat.lt_succ_self b))
       (hKM _ (by omega))
       (Qr (Q62 p s u L0 hs hx0 (show b+1≤ s by omega)
         (show (Qm p s u L0 1).par a<b by omega) (Nat.lt_succ_self b)))
       (hKM _ hab)
   · exact Qbb p s u L0 hs 0 ha hb (fun h=>hab h.2)
lemma Qml [Finite G] {m:ℕ} (hp:p.Prime) (hG:ZB G=p^m) (hs:0<s)
    (hx0:∀ a<s,L0.x a=u a)
    (hL0:ZA (L0.x '' ZP L0.r)⊔lcs G 1=⊤)
    (hcore:lcs G 1≤ZA (Q8t s u 1)⊔lcs G 2) (hr0:s≤L0.r):
    ∀ w,lcs G (w+1)≤ZA ((Qm p s u L0 (w+1)).x ''
      ZP (Qm p s u L0 (w+1)).r)⊔lcs G (w+2):=by
 have hT:=Qmr s u (L0.x '' ZP L0.r) hL0 hcore
 have hsub:∀ w,(Qm p s u L0 (w+1)).x '' ZP (Qm p s u L0 (w+1)).r⊆
     (lcs G (w+1):Set G):=by
  rintro w _ ⟨i, -,rfl⟩
  exact Q7i p s u L0 (w+1) i
 intro w
 induction w with
 | zero=>
   apply Qbk hp hG 0 _ (hsub 0)
   refine (hT 1 le_rfl).trans (sup_le ?_ ((Q16 p 1).trans le_sup_right))
   rw[ZD]
   rintro _ ⟨ab,hab,rfl⟩
   have h1:=Q62 p s u L0 hs hx0 le_rfl hab.1 hab.2
   exact (sup_le_sup_right (ZO (Set.image_mono (fun i hi=>hi.1))) _) h1
 | succ w ih =>
   apply Qbk hp hG (w+1) _ (hsub (w+1))
   have hN:=Q47 p (w+1+1)
     ((Qm p s u L0 (w+1+1)).x '' ZP (Qm p s u L0 (w+1+1)).r) (hsub (w+1))
   refine (hT (w+1+1) (by omega)).trans
     (sup_le ?_ ((Q16 p (w+1+1)).trans le_sup_right))
   rw[ZD]
   rintro _ ⟨y,hy,b,hb,rfl⟩
   have hy1:=ih ((ZD _).mpr (Qer s u w) hy)
   have hle :ZA ((Qm p s u L0 (w+1)).x '' ZP (Qm p s u L0 (w+1)).r)⊔
       lcs G (w+2)≤zn (ZA ((Qm p s u L0 (w+1+1)).x ''
         ZP (Qm p s u L0 (w+1+1)).r)⊔Q15 p G (w+1+1)) (u b):=by
    refine sup_le ?_ ?_
    · rw [ZD]
      rintro _ ⟨a,ha,rfl⟩
      have hspan:⁅(Qm p s u L0 (w+1)).x a,u b⁆∈ZA
          ((Qm p s u L0 (w+1+1)).x '' ZP (Qm p s u L0 (w+1+1)).r)⊔
            Q15 p G (w+1+1):=by
       rcases Nat.eq_zero_or_pos w with hw | hw
       · subst hw
         exact Qib p s u L0 hs hr0 hx0 b hb a ha
       · exact Qbb p s u L0 hs w ha hb (fun h=>by omega)
      exact Q4p.mpr (Qr hspan)
    · intro g hg
      exact Q4p.mpr (ZL
        ((Q16 p (w+1+1)) (Qj (u b) hg)))
   exact Qr (Q4p.mp (hle hy1))
end Layers2
section Layer0
noncomputable def Qfu (G:Type u) [Group G] [Finite G] (j:ℕ):G:=
  if h:j<ZB G then (Finite.equivFin G).symm ⟨j,h⟩ else 1
variable {G:Type u} [Group G] [Finite G]
lemma Qk7 (g:G):∃ j<ZB G,Qfu G j=g:=by
 refine ⟨(Finite.equivFin G g).val,(Finite.equivFin G g).isLt,?_⟩
 unfold Qfu
 rw[dif_pos (Finite.equivFin G g).isLt]
 simp
noncomputable abbrev Q8l (p s:ℕ) (u:ℕ→G):Q4w G:=
  Q34 (Qfu G) (ZA (u '' ZP s)⊔Qv p G) (ZB G) id id
noncomputable def Q2n (p s:ℕ) (u:ℕ→G):Q4w G where
  r :=s+(Q8l p s u).r
  x:= fun i=>if i<s then u i else (Q8l p s u).x (i - s)
  par :=id
  cor :=id
variable (p s:ℕ) (u:ℕ→G)
lemma Q6f {i:ℕ} (h:i<s):(Q2n p s u).x i=u i:=if_pos h
lemma Qcq {i:ℕ} (h:¬ i<s):(Q2n p s u).x i=(Q8l p s u).x (i - s):=if_neg h
lemma Qkn (hu:∀ k<s,u k∉ZA (u '' ZP k)⊔Qv p G) {i:ℕ}
    (hi:i< (Q2n p s u).r):
    (Q2n p s u).x i∉ZA ((Q2n p s u).x '' ZP i)⊔Qv p G:=by
 by_cases his:i<s
 · rw[Q6f p s u his]
   intro hmem
   apply hu i his
   refine (sup_le_sup_right (ZO ?_) _) hmem
   rintro _ ⟨i',hi',rfl⟩
   have hi'':i'< i:=hi'
   exact ⟨i',hi',(Q6f p s u (lt_trans hi'' his)).symm⟩
 · rw [Qcq p s u his]
   intro hmem
   have hi':i - s< (Q8l p s u).r :=by
    have h1:i<s+(Q8l p s u).r :=hi
    omega
   apply Q8n _ _ _ _ _ hi'
   refine (sup_le ?_ ?_:_≤ZA ((Q8l p s u).x '' ZP (i - s))⊔
     (ZA (u '' ZP s)⊔Qv p G)) hmem
   · rw [ZD]
     rintro _ ⟨i',hi'',rfl⟩
     have hi''':i'< i:=hi''
     by_cases h':i'<s
     · rw [Q6f p s u h']
       exact ZL
         (ZJ (ZC ⟨i',h',rfl⟩))
     · rw [Qcq p s u h']
       exact ZJ
         (ZC ⟨i' - s,show i' - s< i - s by omega,rfl⟩)
   · exact le_sup_right.trans le_sup_right
lemma Qlr (g:G):
    g∈ZA ((Q2n p s u).x '' ZP (Q2n p s u).r)⊔Qv p G:=by
 obtain ⟨j,hj,rfl⟩:=Qk7 g
 have h1:=Qd5 (Qfu G) (ZA (u '' ZP s)⊔Qv p G) (ZB G)
   id id le_rfl hj
 refine (sup_le ?_ ?_:_≤ZA ((Q2n p s u).x '' ZP (Q2n p s u).r)⊔
   Qv p G) h1
 · rw [ZD]
   rintro _ ⟨i,⟨hi, -⟩,rfl⟩
   have hi':i< (Q8l p s u).r :=hi
   refine ZJ (ZC ⟨s+i,?_,?_⟩)
   · show s+i<s+(Q8l p s u).r
     omega
   · rw[Qcq p s u (by omega),show s+i - s=i by omega]
 · refine sup_le ?_ le_sup_right
   refine (ZO ?_).trans le_sup_left
   rintro _ ⟨k,hk,rfl⟩
   have hk':k<s:=hk
   exact ⟨k,show k<s+(Q8l p s u).r by omega,Q6f p s u hk'⟩
end Layer0
section Flat
variable {G:Type u} [Group G]
def Q0 (ℓ:ℕ→ℕ):ℕ→ℕ
  | 0=> 0
  | w+1=>Q0 ℓ w+ℓ w
lemma Q19 (ℓ:ℕ→ℕ) (w:ℕ):Q0 ℓ (w+1)=Q0 ℓ w+ℓ w:=rfl
lemma Q2i (ℓ:ℕ→ℕ) {a b:ℕ} (h:a≤b):Q0 ℓ a≤Q0 ℓ b:=by
 induction b with
 | zero=>
   obtain rfl:a=0:=by omega
   exact le_rfl
 | succ b ih=>
   rcases Nat.lt_or_ge a (b+1) with h' | h'
   · rw[Q19]
     exact le_trans (ih (by omega)) (Nat.le_add_right _ _)
   · obtain rfl:a=b+1:=by omega
     exact le_rfl
def Q1o (ℓ:ℕ→ℕ) (L t:ℕ):ℕ:=Nat.findGreatest (fun w=>Q0 ℓ w≤t) L
lemma Qd1 {ℓ:ℕ→ℕ} {L t w:ℕ} (hw:w≤L) (h1:Q0 ℓ w≤t) (h2:t<Q0 ℓ (w+1)):
    Q1o ℓ L t=w:=by
 unfold Q1o
 have hle:=Nat.le_findGreatest (P:= fun w=>Q0 ℓ w≤t) hw h1
 have hspec:Q0 ℓ (Nat.findGreatest (fun w=>Q0 ℓ w≤t) L)≤t:=
   Nat.findGreatest_spec (P:= fun w=>Q0 ℓ w≤t) hw h1
 by_contra hne
 have hgt:w+1≤Nat.findGreatest (fun w=>Q0 ℓ w≤t) L:=by omega
 have:=Q2i ℓ hgt
 omega
lemma Qbm {ℓ:ℕ→ℕ} {L t:ℕ} (ht:t<Q0 ℓ (L+1)):
    Q0 ℓ (Q1o ℓ L t)≤t∧t<Q0 ℓ (Q1o ℓ L t+1)∧Q1o ℓ L t≤L:=by
 have h1:Q0 ℓ (Q1o ℓ L t)≤t:=
   Nat.findGreatest_spec (P:= fun w=>Q0 ℓ w≤t) (Nat.zero_le L) (Nat.zero_le t)
 have h3:Q1o ℓ L t≤L:=Nat.findGreatest_le L
 refine ⟨h1,?_,h3⟩
 by_cases hL:Q1o ℓ L t=L
 · rw[hL]
   exact ht
 · have h4:=Nat.findGreatest_is_greatest (P:= fun w=>Q0 ℓ w≤t)
     (n:=L) (k:=Q1o ℓ L t+1) (by unfold Q1o; omega) (by omega)
   exact not_le.mp h4
lemma Qmt {ℓ:ℕ→ℕ} {L t t':ℕ} (ht':t'<Q0 ℓ (L+1)) (h:t≤t'):
    Q1o ℓ L t≤Q1o ℓ L t':=by
 have ht:t<Q0 ℓ (L+1):=lt_of_le_of_lt h ht'
 obtain ⟨h1, -, -⟩:=Qbm ht
 obtain ⟨-,h2', -⟩:=Qbm ht'
 by_contra hc
 have:=Q2i ℓ (show Q1o ℓ L t'+1≤Q1o ℓ L t by omega)
 omega
def Qgt (n k:ℕ) (dflt:Fin n):Fin n:=if h:k<n then ⟨k,h⟩ else dflt
lemma Qjc {n k:ℕ} (dflt:Fin n) (h:k<n):(Qgt n k dflt).val=k:=by
 unfold Qgt
 rw[dif_pos h]
def Qk (L:ℕ) (r :ℕ→ℕ) (w:ℕ):ℕ:=if w≤L then r w else 0
lemma Q5l {L:ℕ} {r :ℕ→ℕ} {w:ℕ} (h:w≤L):Qk L r w=r w:=if_pos h
lemma Qks {L:ℕ} {r :ℕ→ℕ} {w:ℕ} (h:¬ w≤L):Qk L r w=0:=if_neg h
lemma Q7a (L:ℕ) (r :ℕ→ℕ):Q0 (Qk L r) 1=r 0:=by
 show Q0 (Qk L r) 0+Qk L r 0=r 0
 rw[Q5l (Nat.zero_le L)]
 show 0+r 0=r 0
 omega
lemma Q7d {L:ℕ} {r :ℕ→ℕ} {w i:ℕ} (hw:w≤L) (hi:i< r w):
    Q0 (Qk L r) w+i<Q0 (Qk L r) (L+1):=by
 have h1:Q0 (Qk L r) (w+1)=Q0 (Qk L r) w+r w:=by
  rw[Q19,Q5l hw]
 have h2:=Q2i (Qk L r) (show w+1≤L+1 by omega)
 omega
lemma Q8p {L:ℕ} {r :ℕ→ℕ} {w i:ℕ} (hw:w≤L) (hi:i< r w):
    Q1o (Qk L r) L (Q0 (Qk L r) w+i)=w:=by
 apply Qd1 hw (Nat.le_add_right _ _)
 rw[Q19,Q5l hw]
 omega
lemma Qda {L:ℕ} {r :ℕ→ℕ} {t:ℕ} (ht:t<Q0 (Qk L r) (L+1)):
    Q1o (Qk L r) L t≤L∧Q0 (Qk L r) (Q1o (Qk L r) L t)≤t∧
      t - Q0 (Qk L r) (Q1o (Qk L r) L t)< r (Q1o (Qk L r) L t):=by
 obtain ⟨h1,h2,h3⟩:=Qbm ht
 refine ⟨h3,h1,?_⟩
 rw[Q19,Q5l h3]at h2
 omega
def Q3w (L:ℕ) (r :ℕ→ℕ) (pa co:ℕ→ℕ→ℕ) (t:Fin (Q0 (Qk L r) (L+1))):
    Fin (Q0 (Qk L r) (L+1))×Fin (Q0 (Qk L r) (L+1)):=
  match Q1o (Qk L r) L t.val with
  | 0=> (t,t)
  | w +1=> (Qgt _ (Q0 (Qk L r) w+pa (w+1) (t.val - Q0 (Qk L r) (w+1))) t,
      Qgt _ (co (w+1) (t.val - Q0 (Qk L r) (w+1))) t)
lemma Qjh (L:ℕ) (r :ℕ→ℕ) (pa co:ℕ→ℕ→ℕ) (t:Fin (Q0 (Qk L r) (L+1)))
    {w:ℕ} (h:Q1o (Qk L r) L t.val=w+1):
    Q3w L r pa co t=(Qgt _ (Q0 (Qk L r) w+pa (w+1) (t.val - Q0 (Qk L r) (w+1))) t,
      Qgt _ (co (w+1) (t.val - Q0 (Qk L r) (w+1))) t):=by
 unfold Q3w
 rw[h]
def fX (L:ℕ) (r :ℕ→ℕ) (xs:ℕ→ℕ→G) (t:Fin (Q0 (Qk L r) (L+1))):G:=
  xs (Q1o (Qk L r) L t.val) (t.val - Q0 (Qk L r) (Q1o (Qk L r) L t.val))
lemma Qbq (L:ℕ) (r :ℕ→ℕ) (xs:ℕ→ℕ→G) (t:Fin (Q0 (Qk L r) (L+1))) {w:ℕ}
    (h:Q1o (Qk L r) L t.val=w):fX L r xs t=xs w (t.val - Q0 (Qk L r) w):=by
 unfold fX
 rw[h]
lemma Qf6 {L:ℕ} {r :ℕ→ℕ} (xs:ℕ→ℕ→G) {w i:ℕ} (hw:w≤L) (hi:i< r w):
    fX L r xs ⟨Q0 (Qk L r) w+i,Q7d hw hi⟩=xs w i:=by
 rw[Qbq L r xs ⟨Q0 (Qk L r) w+i,Q7d hw hi⟩ (Q8p hw hi)]
 show xs w (Q0 (Qk L r) w+i - Q0 (Qk L r) w)=xs w i
 rw[Nat.add_sub_cancel_left]
def fData (s L:ℕ) (r :ℕ→ℕ) (pa co:ℕ→ℕ→ℕ):Q5 where
  n:=Q0 (Qk L r) (L+1)
  s:=s
  lv:= fun t=>Q1o (Qk L r) L t.val
  df:=Q3w L r pa co
  a:= fun _=> 0
  b:= fun _ _=> 0
  c:= fun _ _ _=> 0
variable {s L:ℕ} {r :ℕ→ℕ} {xs:ℕ→ℕ→G} {pa co:ℕ→ℕ→ℕ}
lemma Qft (H0:s≤ r 0):s≤Q0 (Qk L r) (L+1):=by
 have h1:=Q7a L r
 have h2:=Q2i (Qk L r) (show 1≤L+1 by omega)
 omega
lemma Q65 (H0:s≤ r 0) (Hpa:∀ w i,i< r (w+1)→pa (w+1) i< r w)
    (Hco:∀ w i,i< r (w+1)→ co (w+1) i<s)
    (t:Fin (Q0 (Qk L r) (L+1))) {w:ℕ} (hw:Q1o (Qk L r) L t.val=w+1):
    w+1≤L∧t.val - Q0 (Qk L r) (w+1)< r (w+1)∧
    ((Q3w L r pa co t).1).val=
      Q0 (Qk L r) w+pa (w+1) (t.val - Q0 (Qk L r) (w+1))∧
    ((Q3w L r pa co t).2).val= co (w+1) (t.val - Q0 (Qk L r) (w+1)):=by
 obtain ⟨hL, -,hi⟩:=Qda (r :=r) t.isLt
 rw[hw]at hL hi
 have hp:=Hpa w _ hi
 have hc:=Hco w _ hi
 refine ⟨hL,hi,?_,?_⟩
 · rw[Qjh L r pa co t hw]
   exact Qjc t (Q7d (show w≤L by omega) hp)
 · rw[Qjh L r pa co t hw]
   exact Qjc t (lt_of_lt_of_le hc (Qft (L:=L) H0))
lemma Q97 (H0:s≤ r 0) (Hpa:∀ w i,i< r (w+1)→pa (w+1) i< r w)
    (Hco:∀ w i,i< r (w+1)→ co (w+1) i<s)
    (H1:∀ i,i< r 1→pa 1 i<co 1 i):(fData s L r pa co).Struct:=by
 refine ⟨?_,Qft H0,?_,?_,?_,?_⟩
 · intro t v htv
   exact Qmt v.isLt (Fin.le_def.mp htv)
 · intro t ht
   have ht':t.val<Q0 (Qk L r) (0+1):=by
    have h1:Q0 (Qk L r) (0+1)=r 0:=Q7a L r
    have h2:t.val<s:=ht
    omega
   exact Qd1 (Nat.zero_le L) (Nat.zero_le _) ht'
 · intro t ht
   obtain ⟨w,hw⟩:∃ w,Q1o (Qk L r) L t.val=w+1:=
     ⟨Q1o (Qk L r) L t.val - 1,by have:1≤Q1o (Qk L r) L t.val:=ht; omega⟩
   obtain ⟨hL,hi,h1, -⟩:=Q65 (pa:=pa) (co:= co) H0 Hpa Hco t hw
   show Q1o (Qk L r) L ((Q3w L r pa co t).1).val+1=Q1o (Qk L r) L t.val
   rw[h1,hw,Q8p (show w≤L by omega) (Hpa w _ hi)]
 · intro t ht
   obtain ⟨w,hw⟩:∃ w,Q1o (Qk L r) L t.val=w+1:=
     ⟨Q1o (Qk L r) L t.val - 1,by have:1≤Q1o (Qk L r) L t.val:=ht; omega⟩
   obtain ⟨-,hi, -,h2⟩:=Q65 (pa:=pa) (co:= co) H0 Hpa Hco t hw
   show ((Q3w L r pa co t).2).val<s
   rw[h2]
   exact Hco w _ hi
 · intro t ht
   have hw:Q1o (Qk L r) L t.val=0+1:=ht
   obtain ⟨-,hi,h1,h2⟩:=Q65 (pa:=pa) (co:= co) H0 Hpa Hco t hw
   show (Q3w L r pa co t).1< (Q3w L r pa co t).2
   rw[Fin.lt_def,h1,h2]
   have h3:pa 1 (t.val - Q0 (Qk L r) (0+1))<co 1 (t.val - Q0 (Qk L r) (0+1)):=
     H1 _ hi
   show 0+pa 1 (t.val - Q0 (Qk L r) (0+1))<co 1 (t.val - Q0 (Qk L r) (0+1))
   omega
lemma Qko (H0:s≤ r 0) (Hpa:∀ w i,i< r (w+1)→pa (w+1) i< r w)
    (Hco:∀ w i,i< r (w+1)→ co (w+1) i<s)
    (Hx:∀ w i,i< r (w+1)→xs (w+1) i=⁅xs w (pa (w+1) i),xs 0 (co (w+1) i)⁆)
    (t:Fin (Q0 (Qk L r) (L+1))) (ht:1≤Q1o (Qk L r) L t.val):
    fX L r xs t=⁅fX L r xs (Q3w L r pa co t).1,fX L r xs (Q3w L r pa co t).2⁆:=by
 obtain ⟨w,hw⟩:∃ w,Q1o (Qk L r) L t.val=w+1:=⟨Q1o (Qk L r) L t.val - 1,by omega⟩
 obtain ⟨hL,hi,h1,h2⟩:=Q65 (pa:=pa) (co:= co) H0 Hpa Hco t hw
 have hp:=Hpa w _ hi
 have hc:=Hco w _ hi
 have e1:Q1o (Qk L r) L ((Q3w L r pa co t).1).val=w:=by
  rw[h1]
  exact Q8p (show w≤L by omega) hp
 have e2:Q1o (Qk L r) L ((Q3w L r pa co t).2).val=0:=by
  rw[h2]
  have h3:Q0 (Qk L r) (0+1)=r 0:=Q7a L r
  exact Qd1 (Nat.zero_le L) (Nat.zero_le _) (by omega)
 have e0:Q0 (Qk L r) 0=0:=rfl
 rw [Qbq L r xs t hw,Qbq L r xs _ e1,Qbq L r xs _ e2,Hx w _ hi,h1,h2,
   Nat.add_sub_cancel_left,e0,Nat.sub_zero]
lemma Qj0 (h0:ZA (xs 0 '' ZP (r 0))=⊤):
    ZA (ZG (fX L r xs))=⊤:=by
 rw[eq_top_iff, ← h0,ZD]
 rintro _ ⟨i,hi,rfl⟩
 exact ZC ⟨⟨_,Q7d (Nat.zero_le L) hi⟩,Qf6 xs (Nat.zero_le L) hi⟩
lemma Qbo
    (HU:∀ w,w+1≤L→lcs G (w+1)≤
      ZA (xs (w+1) '' ZP (r (w+1)))⊔lcs G (w+2))
    (HL:lcs G (L+1)=⊥) (w:ℕ):
    lcs G (w+1)≤ZA (Q2q (fData s L r pa co) (fX L r xs) (w+1))⊔
      lcs G (w+2):=by
 by_cases hw:w+1≤L
 · refine (HU w hw).trans (sup_le_sup_right (ZO ?_) _)
   rintro _ ⟨i,hi,rfl⟩
   exact ⟨⟨_,Q7d hw hi⟩,Q8p hw hi,Qf6 xs hw hi⟩
 · exact ((Qd (D:=G) (show L+1≤w+1 by omega)).trans (le_of_eq HL)).trans
     bot_le
lemma Qln (H0:s≤ r 0) (Hpa:∀ w i,i< r (w+1)→pa (w+1) i< r w)
    (Hco:∀ w i,i< r (w+1)→ co (w+1) i<s)
    (H1:∀ i,i< r 1→pa 1 i<co 1 i)
    (Hx:∀ w i,i< r (w+1)→xs (w+1) i=⁅xs w (pa (w+1) i),xs 0 (co (w+1) i)⁆)
    (h0:ZA (xs 0 '' ZP (r 0))=⊤)
    (HU:∀ w,w+1≤L→lcs G (w+1)≤
      ZA (xs (w+1) '' ZP (r (w+1)))⊔lcs G (w+2))
    (HL:lcs G (L+1)=⊥):
    ∀ w,1≤w→lcs G w≤ZA (fX L r xs '' {v | w≤(fData s L r pa co).lv v}):=by
  have hd:=Q97 (L:=L) H0 Hpa Hco H1
  have hdf:∀ t,1≤(fData s L r pa co).lv t→ fX L r xs t=
      ⁅fX L r xs ((fData s L r pa co).df t).1,fX L r xs ((fData s L r pa co).df t).2⁆:=
    fun t ht=>Qko H0 Hpa Hco Hx t ht
  have hlv:=Q5f (fData s L r pa co) hd (fX L r xs) hdf
  refine Qbz (fData s L r pa co) hd (fX L r xs) (Qj0 h0) ⟨L+1,HL⟩ hdf ?_ ?_ ?_
  · intro i k _ _
    exact Qbo HU HL 0 (Qo _ _)
  · intro t k ht _
    have h1:=Qb (hlv t) (fX L r xs k)
    rw[ht]at h1
    exact Qbo HU HL 1 h1
  · intro t k _ _
    exact Qbo HU HL ((fData s L r pa co).lv t) (Qb (hlv t) _)
lemma Ql2 (p:ℕ)
    (Hind:∀ w i,i< r w→xs w i∉ZA (xs w '' ZP i)⊔Q15 p G w)
    (t:Fin (Q0 (Qk L r) (L+1))):
    fX L r xs t∉ZA (fX L r xs '' {v | (fData s L r pa co).lv v=
      (fData s L r pa co).lv t∧v<t})⊔Q15 p G ((fData s L r pa co).lv t):=by
  obtain ⟨-, -,hi⟩:=Qda (r :=r) t.isLt
  intro hmem
  apply Hind _ _ hi
  rw[← Qbq L r xs t rfl]
  refine (sup_le_sup_right (ZO ?_) _) hmem
  rintro _ ⟨v,⟨hv1,hv2⟩,rfl⟩
  have hv1':Q1o (Qk L r) L v.val=Q1o (Qk L r) L t.val:=hv1
  obtain ⟨-,hv3, -⟩:=Qda (r :=r) v.isLt
  rw[hv1']at hv3
  have hv2':v.val<t.val:=hv2
  refine ⟨v.val - Q0 (Qk L r) (Q1o (Qk L r) L t.val),?_,(Qbq L r xs v hv1').symm⟩
  show v.val - Q0 (Qk L r) (Q1o (Qk L r) L t.val)<
    t.val - Q0 (Qk L r) (Q1o (Qk L r) L t.val)
  omega
lemma Qcv (u:ℕ→G) (H0:s≤ r 0) (Hc0:∀ i<s,xs 0 i=u i)
    (t:Fin (Q0 (Qk L r) (L+1))) (ht:t.val<s):fX L r xs t=u t.val:=by
 have h1:Q0 (Qk L r) (0+1)=r 0:=Q7a L r
 have h0:Q1o (Qk L r) L t.val=0:=
   Qd1 (Nat.zero_le L) (Nat.zero_le _) (by omega)
 rw[Qbq L r xs t h0]
 show xs 0 (t.val - 0)=u t.val
 rw[Nat.sub_zero]
 exact Hc0 _ ht
lemma Q95 (H0:s≤ r 0) (Hpa:∀ w i,i< r (w+1)→pa (w+1) i< r w)
    (Hco:∀ w i,i< r (w+1)→ co (w+1) i<s)
    (t:Fin (Q0 (Qk L r) (L+1))) (ht:Q1o (Qk L r) L t.val=1):
    1 ≤L∧r 0≤t.val∧t.val - r 0< r 1∧
      ((Q3w L r pa co t).1).val=pa 1 (t.val - r 0)∧
      ((Q3w L r pa co t).2).val= co 1 (t.val - r 0):=by
 have hw:Q1o (Qk L r) L t.val=0+1:=ht
 obtain ⟨hL,hi,h1,h2⟩:=Q65 (pa:=pa) (co:= co) H0 Hpa Hco t hw
 obtain ⟨-,h3, -⟩:=Qda (r :=r) t.isLt
 rw[hw]at h3
 have e:Q0 (Qk L r) (0+1)=r 0:=Q7a L r
 rw[e]at hi h1 h2 h3
 refine ⟨hL,h3,hi,?_,h2⟩
 rw[h1]
 show 0+pa 1 (t.val - r 0)=pa 1 (t.val - r 0)
 omega
lemma Qmh (H0:s≤ r 0) (Hpa:∀ w i,i< r (w+1)→pa (w+1) i< r w)
    (Hco:∀ w i,i< r (w+1)→ co (w+1) i<s)
    (Hmono:∀ i i',i≤ i'→i'< r 1→ co 1 i≤ co 1 i')
    (t t':Fin (Q0 (Qk L r) (L+1))) (ht:Q1o (Qk L r) L t.val=1)
    (ht':Q1o (Qk L r) L t'.val=1) (htt:t≤t'):
    (Q3w L r pa co t).2≤(Q3w L r pa co t').2:=by
 obtain ⟨-,h3, -, -,h2⟩:=Q95 (pa:=pa) (co:= co) H0 Hpa Hco t ht
 obtain ⟨-,h3',hi', -,h2'⟩:=Q95 (pa:=pa) (co:= co) H0 Hpa Hco t' ht'
 rw[Fin.le_def,h2,h2']
 have h4:t.val≤t'.val:=Fin.le_def.mp htt
 exact Hmono _ _ (by omega) hi'
lemma Qmp (H0:s≤ r 0) (Hpa:∀ w i,i< r (w+1)→pa (w+1) i< r w)
    (Hco:∀ w i,i< r (w+1)→ co (w+1) i<s)
    (Hinj:∀ i i',i< r 1→i'< r 1→pa 1 i=pa 1 i'→ co 1 i= co 1 i'→i=i')
    (t t':Fin (Q0 (Qk L r) (L+1))) (ht:Q1o (Qk L r) L t.val=1)
    (ht':Q1o (Qk L r) L t'.val=1) (h1:(Q3w L r pa co t).1=(Q3w L r pa co t').1)
    (h2:(Q3w L r pa co t).2=(Q3w L r pa co t').2):t=t':=by
 obtain ⟨-,h3,hi,e1,e2⟩:=Q95 (pa:=pa) (co:= co) H0 Hpa Hco t ht
 obtain ⟨-,h3',hi',e1',e2'⟩:=Q95 (pa:=pa) (co:= co) H0 Hpa Hco t' ht'
 have hp:pa 1 (t.val - r 0)=pa 1 (t'.val - r 0):=by rw[← e1, ← e1',h1]
 have hc:co 1 (t.val - r 0)= co 1 (t'.val - r 0):=by rw[← e2, ← e2',h2]
 have h4:=Hinj _ _ hi hi' hp hc
 exact Fin.ext (by omega)
lemma Qnh (p:ℕ) (u:ℕ→G) (H0:s≤ r 0)
    (Hpa:∀ w i,i< r (w+1)→pa (w+1) i< r w)
    (Hco:∀ w i,i< r (w+1)→ co (w+1) i<s) (H1:∀ i,i< r 1→pa 1 i<co 1 i)
    (Hx:∀ w i,i< r (w+1)→xs (w+1) i=⁅xs w (pa (w+1) i),xs 0 (co (w+1) i)⁆)
    (Hc0:∀ i<s,xs 0 i=u i) (hL1:1≤L)
    (HS1:∀ k≤ s,∀ a b,a<b→ b<k→
      ⁅u a,u b⁆∈ZA (xs 1 '' {i | i< r 1∧co 1 i<k})⊔pN p G)
    {k:ℕ} (hk:k≤ s):
    Q1e (pN p G) u k=ZA (fX L r xs '' {t | (fData s L r pa co).lv t=1∧
      ((fData s L r pa co).df t).2.val<k})⊔pN p G:=by
  apply le_antisymm
  · refine Q6l (pN p G) le_sup_right ?_
    intro a b hab hb
    refine (sup_le_sup_right (ZO ?_) _) (HS1 k hk a b hab hb)
    rintro _ ⟨i,⟨hi,hik⟩,rfl⟩
    have hpos:=Q7d (L:=L) hL1 hi
    have hlv:=Q8p (L:=L) hL1 hi
    refine ⟨⟨_,hpos⟩,⟨hlv,?_⟩,Qf6 xs hL1 hi⟩
    obtain ⟨-, -, -, -,h2⟩:=Q95 (pa:=pa) (co:= co) H0 Hpa Hco ⟨_,hpos⟩ hlv
    show ((Q3w L r pa co ⟨_,hpos⟩).2).val<k
    rw[h2]
    show co 1 (Q0 (Qk L r) 1+i - r 0)<k
    have e:Q0 (Qk L r) 1+i - r 0=i:=by
     rw[Q7a]
     omega
    rw[e]
    exact hik
  · refine sup_le ?_ (Q3t _ u k)
    rw[ZD]
    rintro _ ⟨t,⟨ht1,htk⟩,rfl⟩
    have ht1':Q1o (Qk L r) L t.val=1:=ht1
    have hd:=Q97 (L:=L) H0 Hpa Hco H1
    have hlt:((Q3w L r pa co t).1).val< ((Q3w L r pa co t).2).val:=
      Fin.lt_def.mp (hd.df_one t ht1)
    have hcs:((Q3w L r pa co t).2).val<s:=
      hd.df_core t (show 1≤Q1o (Qk L r) L t.val by omega)
    rw [Qko H0 Hpa Hco Hx t (by omega),Qcv u H0 Hc0 _ (lt_trans hlt hcs),
      Qcv u H0 Hc0 _ hcs]
    exact Q2a _ u hlt htk
lemma Qk1 (p:ℕ) (u:ℕ→G) (hstrict:Q10 (pN p G) u s)
    (hWk:∀ k≤ s,Q1e (pN p G) u k=ZA (fX L r xs '' {t |
      (fData s L r pa co).lv t=1∧((fData s L r pa co).df t).2.val<k})⊔pN p G)
    {k:ℕ} (hk1:1≤k) (hks:k<s):
    ∃ t,(fData s L r pa co).lv t=1∧((fData s L r pa co).df t).2.val=k:=by
  by_contra hno
  push_neg at hno
  have hset:{t:Fin (Q0 (Qk L r) (L+1)) | (fData s L r pa co).lv t=1∧
      ((fData s L r pa co).df t).2.val<k}={t | (fData s L r pa co).lv t=1∧
      ((fData s L r pa co).df t).2.val<k+1}:=by
    ext t
    simp only[Set.mem_setOf_eq]
    constructor
    · rintro ⟨h1,h2⟩
      exact ⟨h1,by omega⟩
    · rintro ⟨h1,h2⟩
      have h3:=hno t h1
      exact ⟨h1,by omega⟩
  apply hstrict (k+1) (by omega) (by omega)
  rw[Nat.add_sub_cancel,hWk k (by omega),hWk (k+1) (by omega),hset]
  rfl
end Flat
section NormalForm
variable {G:Type u} [Group G]
lemma Qji [Finite G] {p m:ℕ} (hp:p.Prime) (hG:ZB G=p^m)
    (d:Q5) (hd:d.Struct) (X:Fin d.n→G)
    (hgen:ZA (ZG X)=⊤) (hlv:∀ t,X t∈lcs G (d.lv t))
    (hdeep:∀ w,1≤w→lcs G w≤ZA (X '' {u | w≤d.lv u})):
    ∀ g:G,∃ e:Fin d.n→ℕ,(∀ t,e t<p^Q1q p d X t)∧g=Q2e X e:=by
  intro g
  have hnf:=Qgo d X hp hG hd hlv hdeep 0 d.n
  have hmem:g∈ZA (X '' Q2z d 0 d.n):=by
   have hle:ZA (ZG X)≤ZA (X '' Q2z d 0 d.n):=by
    apply ZO
    rintro _ ⟨v,rfl⟩
    refine ⟨v,?_,rfl⟩
    rw[Q1b]
    rcases Nat.eq_zero_or_pos (d.lv v) with h | h
    · exact Or.inr ⟨h.symm,v.isLt⟩
    · exact Or.inl h
   rw[hgen]at hle
   exact hle (ZM g)
  obtain ⟨e, -,he,rfl⟩:=hnf g hmem
  exact ⟨e,he,rfl⟩
lemma Qkt [Finite G] {p:ℕ} (d:Q5) (X:Fin d.n→G)
    (hcard:ZB G=p^(∑ t,d.a t))
    (hex:∀ g:G,∃ e:Fin d.n→ℕ,(∀ t,e t<p^d.a t)∧g=Q2e X e)
    (e e':Fin d.n→ℕ) (he:∀ t,e t<p^d.a t) (he':∀ t,e' t<p^d.a t)
    (h:Q2e X e=Q2e X e'):e=e':=by
 have hsurj:Function.Surjective
     (fun f:(t:Fin d.n)→Fin (p^d.a t)=>Q2e X (fun t=> (f t:ℕ))):=by
   intro g
   obtain ⟨e0,he0,rfl⟩:=hex g
   exact ⟨fun t=> ⟨e0 t,he0 t⟩,rfl⟩
 have hc:ZB ((t:Fin d.n)→Fin (p^d.a t))=ZB G:=by
  rw[Nat.card_pi,hcard]
  simp only[Nat.card_fin]
  exact Finset.prod_pow_eq_pow_sum _ _ _
 have hinj:=(hsurj.bijective_of_nat_card_le (le_of_eq hc)).1
 have h2:= @hinj (fun t=> ⟨e t,he t⟩) (fun t=> ⟨e' t,he' t⟩) h
 funext t
 exact congrArg (fun f:(t:Fin d.n)→Fin (p^d.a t)=> ((f t:Fin _):ℕ)) h2
end NormalForm
section SimsCore
variable {G:Type u} [Group G]
noncomputable def Qt (G:Type u) [Group G]:ℕ:=
  sInf {k | ∃ u:Fin k→G,
    lcs G 1≤⁅ZA (ZG u),ZA (ZG u)⁆⊔lcs G 2}
def Qh9 {k:ℕ} (x:Fin k→G) (i:ℕ):G:=if h:i<k then x ⟨i,h⟩ else 1
lemma Qkh {k:ℕ} (x:Fin k→G) {i:ℕ} (h:i<k):Qh9 x i=x ⟨i,h⟩:=dif_pos h
lemma Qgg {k:ℕ} (x:Fin k→G):ZG x =Qh9 x '' ZP k:=by
 ext y
 constructor
 · rintro ⟨i,rfl⟩
   exact ⟨i.val,i.isLt,Qkh x i.isLt⟩
 · rintro ⟨i,hi,rfl⟩
   exact ⟨⟨i,hi⟩,(Qkh x hi).symm⟩
lemma Qmx [Finite G] {p m:ℕ} (hp:p.Prime) (hG:ZB G=p^m) {t:ℕ}
    (ht:t<Qt G) (v:ℕ→G):
    ¬ lcs G 1≤⁅ZA (v '' ZP t),ZA (v '' ZP t)⁆⊔
      pN p G:=by
 intro h
 have hB:(⁅ZA (v '' ZP t),ZA (v '' ZP t)⁆⊔
     lcs G 2).Normal:=by
  refine Q1d (n:=1) le_sup_right (sup_le ?_ (Qd (by omega)))
  exact Subgroup.commutator_le.mpr (fun x _ y _=>Qo x y)
 have h2:lcs G 1≤⁅ZA (v '' ZP t),ZA (v '' ZP t)⁆⊔
     lcs G 2:=by
  refine Qcc hp hG (lcs G 1) _ ?_ ?_
  · intro x hx y hy
    exact ZL
      (Qd (D:=G) (show 2≤1+1+1 by omega) (Q1c hx hy))
  · rw[sup_assoc]
    exact h
 have hle:Qt G≤t:=by
  apply Nat.sInf_le
  refine ⟨fun i=>v i,?_⟩
  have e:ZG (fun i:Fin t=>v i)=v '' ZP t:=by
    ext x
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨i.val,i.isLt,rfl⟩
    · rintro ⟨i,hi,rfl⟩
      exact ⟨⟨i,hi⟩,rfl⟩
  rw[e]
  exact h2
 omega
lemma Qhs [Finite G] {p m:ℕ} (hp:p.Prime) (hG:ZB G=p^m) {s:ℕ}
    {u:ℕ→G} (hW:Q1e (pN p G) u s=lcs G 1):
    lcs G 1≤ZA (Q8t s u 1)⊔lcs G 2:=by
 apply Qbk hp hG 0 (Q8t s u 1) (Qer s u 0)
 refine (le_of_eq hW.symm).trans ?_
 refine Q6l (pN p G) le_sup_right ?_
 intro a b hab hb
 exact ZJ (ZC ⟨(a,b),⟨hab,hb⟩,rfl⟩)
lemma Qjt [Finite G] {p m:ℕ} (hp:p.Prime) (hG:ZB G=p^m)
    (hna:lcs G 1≠⊥):
    2 ≤ Qt G∧∃ u:ℕ→G,Q10 (pN p G) u (Qt G)∧
      Q1e (pN p G) u (Qt G)=lcs G 1∧
      (∀ k<Qt G,u k∉ZA (u '' ZP k)⊔Qv p G)∧
      lcs G 1≤⁅ZA (u '' ZP (Qt G)),
        ZA (u '' ZP (Qt G))⁆⊔lcs G 2:=by
 have:Fact p.Prime:=⟨hp⟩
 have:Group.IsNilpotent G:=(IsPGroup.of_card hG).isNilpotent
 obtain ⟨N,hN⟩:∃ N,lcs G N=⊥:=Subgroup.nilpotent_iff_lowerCentralSeries.mp inferInstance
 let e:Fin (ZB G)→G:=(Finite.equivFin G).symm
 have he:ZG e=Set.univ:=Equiv.range_eq_univ _
 have hne:{k | ∃ u:Fin k→G,
     lcs G 1≤⁅ZA (ZG u),ZA (ZG u)⁆⊔
       lcs G 2}.Nonempty:=by
   refine ⟨ZB G,e,?_⟩
   rw[he,Subgroup.closure_univ]
   exact le_sup_left
 obtain ⟨x,hx⟩:∃ x:Fin (Qt G)→G,
     lcs G 1≤⁅ZA (ZG x),ZA (ZG x)⁆⊔lcs G 2:=
   Nat.sInf_mem hne
 have hs:2≤Qt G:=by
  by_contra hlt
  have hk:Qt G≤1:=by omega
  have hHH:⁅ZA (ZG x),ZA (ZG x)⁆≤⊥:=by
   refine Q2o ?_
   rintro _ ⟨i,rfl⟩ _ ⟨j,rfl⟩
   have hij:i=j:=Fin.ext (by have:=i.isLt; have:=j.isLt; omega)
   rw[hij,commutatorElement_self]
   exact one_mem _
  have h12:lcs G 1≤lcs G 2:=le_trans hx (sup_le (le_trans hHH bot_le) le_rfl)
  have hall:∀ n,lcs G 1≤lcs G (n+1):=by
   intro n
   induction n with
   | zero=>exact le_rfl
   | succ n ih=>
     refine le_trans h12 ?_
     rw[lcs_succ 1,lcs_succ (n+1)]
     exact Subgroup.commutator_mono ih le_rfl
  have hbot:lcs G 1≤⊥:=by
   rw[← hN]
   exact le_trans (hall N) (Qd (by omega))
  exact hna (le_bot_iff.mp hbot)
 have hcore0:lcs G 1≤⁅ZA (Qh9 x '' ZP (Qt G)),
     ZA (Qh9 x '' ZP (Qt G))⁆⊔pN p G:=by
  rw[← Qgg]
  exact hx.trans (sup_le_sup_left (Q1j p) _)
 obtain ⟨u, -,hstrict,hW,hind, -, -⟩:=Qlv hp hG (pN p G) (Qv p G)
   (Q1j p) (Q3y p) (Q16 p 0) (Q2c p)
   (fun g m hm=>Qr (Q8f p hm g)) (Qt G) (Qh9 x) hcore0
   (fun t ht v _=>Qmx hp hG ht v)
 have hcore:=Qhs hp hG hW
 have hcomm:ZA (Q8t (Qt G) u 1)≤
     ⁅ZA (u '' ZP (Qt G)),
       ZA (u '' ZP (Qt G))⁆:=by
  rw[ZD]
  rintro _ ⟨ab,hab,rfl⟩
  exact Subgroup.commutator_mem_commutator
    (ZC ⟨ab.1,lt_trans hab.1 hab.2,rfl⟩)
    (ZC ⟨ab.2,hab.2,rfl⟩)
 exact ⟨hs,u,hstrict,hW,hind,hcore.trans (sup_le_sup_right hcomm _)⟩
end SimsCore
section Q7
variable {G:Type u} [Group G]
structure Q2 (p:ℕ) (u:ℕ→G) (d:Q5) (X:Fin d.n→G) (r :ℕ→ℕ):Prop where
  core:∀ t:Fin d.n,t.val<d.s→X t=u t.val
  valid:d.Valid
  bounded:d.Bounded p
  realizes:Q2k p d X
  a_pos:∀ t,1≤d.a t
  n_le_sum:d.n≤∑ t,d.a t
  layer_iff:∀ (t:Fin d.n) (w:ℕ),d.lv t=w↔Q0 r w≤t.val∧t.val<Q0 r w+r w
  layer_card:∀ w,p^r w*ZB (Q15 p G w)=ZB (lcs G w)
  layer_indep:∀ t,X t∉ZA (X '' {v | d.lv v=d.lv t∧v<t})⊔
    Q15 p G (d.lv t)
  layer_gen:∀ w,lcs G w≤ZA (X '' {t | d.lv t=w})⊔lcs G (w+1)
  block_mono:∀ t t',d.lv t=1→d.lv t'=1→t≤t'→(d.df t).2≤(d.df t').2
  block_inj:∀ t t',d.lv t=1→d.lv t'=1→(d.df t).1=(d.df t').1→
    (d.df t).2=(d.df t').2→t=t'
  flag:∀ k≤d.s,Q1e (pN p G) u k=
    ZA (X '' {t | d.lv t=1∧(d.df t).2.val<k})⊔pN p G
  block_ne:∀ k,1≤k→k<d.s→∃ t,d.lv t=1∧(d.df t).2.val=k
  nf_exists:∀ g:G,∃ e:Fin d.n→ℕ,(∀ t,e t<p^d.a t)∧g=Q2e X e
  nf_unique:∀ e e':Fin d.n→ℕ,(∀ t,e t<p^d.a t)→(∀ t,e' t<p^d.a t)→
    Q2e X e=Q2e X e'→e=e'
  deep:∀ w,1≤w→lcs G w≤ZA (X '' {t | w≤d.lv t})
  nf_sub:∀ (w j:ℕ),∀ z∈ZA (X '' Q2z d w j),∃ e:Fin d.n→ℕ,
    (∀ t,e t≠0→t∈Q2z d w j)∧(∀ t,e t<p^d.a t)∧z=Q2e X e
  n_eq:∃ c,d.n=Q0 r c
  w3:∀ t,d.lv t=2→(d.df t).2.val≤(d.df (d.df t).1).2.val
lemma Qlg [Finite G] {p m:ℕ} (hp:p.Prime) (hG:ZB G=p^m) {s L:ℕ}
    {r :ℕ→ℕ} {xs:ℕ→ℕ→G} {pa co:ℕ→ℕ→ℕ} (u:ℕ→G)
    (H0:s≤ r 0) (Hpa:∀ w i,i< r (w+1)→pa (w+1) i< r w)
    (Hco:∀ w i,i< r (w+1)→ co (w+1) i<s) (H1:∀ i,i< r 1→pa 1 i<co 1 i)
    (Hx:∀ w i,i< r (w+1)→xs (w+1) i=⁅xs w (pa (w+1) i),xs 0 (co (w+1) i)⁆)
    (Hc0:∀ i<s,xs 0 i=u i) (h0:ZA (xs 0 '' ZP (r 0))=⊤)
    (HU:∀ w,w+1≤L→lcs G (w+1)≤
      ZA (xs (w+1) '' ZP (r (w+1)))⊔lcs G (w+2))
    (HL:lcs G (L+1)=⊥) (hL1:1≤L)
    (Hind:∀ w i,i< r w→xs w i∉ZA (xs w '' ZP i)⊔Q15 p G w)
    (Hcard:∀ w≤L,p^r w*ZB (Q15 p G w)=ZB (lcs G w))
    (HS1:∀ k≤ s,∀ a b,a<b→ b<k→
      ⁅u a,u b⁆∈ZA (xs 1 '' {i | i< r 1∧co 1 i<k})⊔pN p G)
    (Hmono:∀ i i',i≤ i'→i'< r 1→ co 1 i≤ co 1 i')
    (Hinj:∀ i i',i< r 1→i'< r 1→pa 1 i=pa 1 i'→ co 1 i= co 1 i'→i=i')
    (hstrict:Q10 (pN p G) u s) (Hw3:∀ i,i< r 2→ co 2 i≤ co 1 (pa 2 i)):
    ∃ (d:Q5) (X:Fin d.n→G),d.s=s∧Q2 p u d X (Qk L r):=by
  have hd:=Q97 (s:=s) (L:=L) H0 Hpa Hco H1
  have hdf:∀ t,1≤(fData s L r pa co).lv t→ fX L r xs t=
      ⁅fX L r xs ((fData s L r pa co).df t).1,fX L r xs ((fData s L r pa co).df t).2⁆:=
    fun t ht=>Qko H0 Hpa Hco Hx t ht
  have hgen:=Qj0 (L:=L) h0
  have hdeep:=Qln (s:=s) (pa:=pa) (co:= co) H0 Hpa Hco H1 Hx h0 HU HL
  have hlv:=Q5f (fData s L r pa co) hd (fX L r xs) hdf
  obtain ⟨b,c,hv,hb,hr⟩:=
    Qik (fData s L r pa co) (fX L r xs) hp hG hd hgen hdf hdeep
  have hind:=Ql2 (s:=s) (L:=L) (pa:=pa) (co:= co) p Hind
  have ha1:∀ t,1≤Q1q p (fData s L r pa co) (fX L r xs) t:=by
   intro t
   by_contra h0'
   have hz:Q1q p (fData s L r pa co) (fX L r xs) t=0:=by omega
   have hmem:=Q5x (fData s L r pa co) (fX L r xs) hG t
   rw[hz,pow_zero,pow_one]at hmem
   apply hind t
   refine (ZD _).mpr ?_ hmem
   rintro _ ⟨v,hv',rfl⟩
   rcases (Q1b (fData s L r pa co)).mp hv' with h | ⟨h1,h2⟩
   · exact ZL (Q16 p _
       (Qd (D:=G) (show (fData s L r pa co).lv t+1≤(fData s L r pa co).lv v
         from h) (hlv v)))
   · exact ZJ (ZC ⟨v,⟨h1.symm,Fin.lt_def.mpr h2⟩,rfl⟩)
  have hWk:∀ k≤ s,Q1e (pN p G) u k=ZA (fX L r xs '' {t |
      (fData s L r pa co).lv t=1∧((fData s L r pa co).df t).2.val<k})⊔pN p G:=
    fun k hk=>Qnh p u H0 Hpa Hco H1 Hx Hc0 hL1 HS1 hk
  have hex:=Qji hp hG (fData s L r pa co) hd (fX L r xs) hgen hlv hdeep
  have hnfp:=Qgo (fData s L r pa co) (fX L r xs) hp hG hd hlv hdeep
  have hw3:∀ t:Fin (fData s L r pa co).n,(fData s L r pa co).lv t=2→
      ((fData s L r pa co).df t).2.val≤
        ((fData s L r pa co).df ((fData s L r pa co).df t).1).2.val:=by
   intro t ht
   have ht':Q1o (Qk L r) L t.val=1+1:=ht
   obtain ⟨-,hi,h1,h2⟩:=Q65 (L:=L) (pa:=pa) (co:= co) H0 Hpa Hco t ht'
   have hl1:(fData s L r pa co).lv ((fData s L r pa co).df t).1+1=
       (fData s L r pa co).lv t:=hd.df_lv t (by omega)
   have ht1:Q1o (Qk L r) L ((Q3w L r pa co t).1).val=0+1:=by
    have e:(fData s L r pa co).lv ((fData s L r pa co).df t).1=1:=by omega
    exact e
   obtain ⟨-, -, -,h4⟩:=Q65 (L:=L) (pa:=pa) (co:= co) H0 Hpa Hco _ ht1
   have h5:((Q3w L r pa co t).1).val - Q0 (Qk L r) (0+1)=
       pa (1+1) (t.val - Q0 (Qk L r) (1+1)):=by
    rw[h1]
    exact Nat.add_sub_cancel_left _ _
   show ((Q3w L r pa co t).2).val≤((Q3w L r pa co (Q3w L r pa co t).1).2).val
   rw[h4,h2,h5]
   exact Hw3 _ hi
  refine ⟨⟨(fData s L r pa co).n,(fData s L r pa co).s,(fData s L r pa co).lv,
    (fData s L r pa co).df,Q1q p (fData s L r pa co) (fX L r xs),b,c⟩,fX L r xs,rfl,?_⟩
  refine
    { core:= fun t ht=>Qcv u H0 Hc0 t ht
      valid:=hv
      bounded:=hb
      realizes:=hr
      a_pos:=ha1
      n_le_sum:=?_
      layer_iff:=?_
      layer_card:=?_
      layer_indep:=hind
      layer_gen:=?_
      block_mono:= fun t t' ht ht' htt=>Qmh H0 Hpa Hco Hmono t t' ht ht' htt
      block_inj:= fun t t' ht ht' h1 h2=>Qmp H0 Hpa Hco Hinj t t' ht ht' h1 h2
      flag:=hWk
      block_ne:= fun k hk1 hks=>Qk1 p u hstrict hWk hk1 hks
      nf_exists:=hex
      nf_unique:= fun e e' he he' h=>Qkt _ (fX L r xs) hr.card hex e e' he he' h
      deep:=hdeep
      nf_sub:= fun w j=>hnfp w j
      n_eq:=⟨L+1,rfl⟩
      w3:=hw3 }
  · calc Q0 (Qk L r) (L+1)=∑ _t:Fin (Q0 (Qk L r) (L+1)),1:=by simp
      _ ≤∑ t,Q1q p (fData s L r pa co) (fX L r xs) t:=
        Finset.sum_le_sum (fun t _=>ha1 t)
  · intro t w
    constructor
    · intro h
      have h':Q1o (Qk L r) L t.val=w:=h
      obtain ⟨h1,h2, -⟩:=Qbm (ℓ:=Qk L r) t.isLt
      rw[h']at h1 h2
      rw[Q19]at h2
      exact ⟨h1,h2⟩
    · rintro ⟨h1,h2⟩
      by_cases hw:w≤L
      · exact Qd1 hw h1 (lt_of_lt_of_eq h2 (Q19 (Qk L r) w).symm)
      · exfalso
        have h3:=Q2i (Qk L r) (show L+1≤w by omega)
        have h4:t.val<Q0 (Qk L r) (L+1):=t.isLt
        omega
  · intro w
    by_cases hw:w≤L
    · rw[Q5l hw]
      exact Hcard w hw
    · rw [Qks hw,pow_zero,one_mul]
      obtain ⟨w',rfl⟩:∃ w',w=w'+1:=⟨w - 1,by omega⟩
      have h1:lcs G (w'+1)=⊥:=le_bot_iff.mp
        ((Qd (D:=G) (show L+1≤w'+1 by omega)).trans (le_of_eq HL))
      have h2:Q15 p G (w'+1)=⊥:=le_bot_iff.mp ((Q7l p w').trans (le_of_eq h1))
      rw[h1,h2]
  · intro w
    rcases w with _ | w
    · rw [lcs_zero, ← h0]
      refine le_sup_of_le_left (ZO ?_)
      rintro _ ⟨i,hi,rfl⟩
      exact ⟨⟨_,Q7d (Nat.zero_le L) hi⟩,Q8p (Nat.zero_le L) hi,
        Qf6 xs (Nat.zero_le L) hi⟩
    · exact Qbo (s:=s) (pa:=pa) (co:= co) HU HL w
noncomputable def gR [Finite G] (p s:ℕ) (u:ℕ→G) (w:ℕ):ℕ:=
  (Qm p s u (Q2n p s u) w).r
noncomputable def Qar [Finite G] (p s:ℕ) (u:ℕ→G) (w i:ℕ):G:=
  (Qm p s u (Q2n p s u) w).x i
noncomputable def Qj7 [Finite G] (p s:ℕ) (u:ℕ→G) (w i:ℕ):ℕ:=
  (Qm p s u (Q2n p s u) w).par i
noncomputable def Qba [Finite G] (p s:ℕ) (u:ℕ→G) (w i:ℕ):ℕ:=
  (Qm p s u (Q2n p s u) w).cor i
lemma Q6n (p s:ℕ) (u:ℕ→G) (L0:Q4w G) (i:ℕ):
    (Qm p s u L0 1).cor i=Q1i (Qz (Q1a s u 0 L0) (Q15 p G 1) (cN s 0 L0)) i/s:=by
 rw[Qec]
 exact Q7z
lemma Qcf (p s:ℕ) (u:ℕ→G) (L0:Q4w G) (i:ℕ):
    (Qm p s u L0 1).par i=Q1i (Qz (Q1a s u 0 L0) (Q15 p G 1) (cN s 0 L0)) i % s:=by
 rw[Qec]
 exact Q9g
lemma Qdi (p s:ℕ) (u:ℕ→G) (L0:Q4w G) {i i':ℕ} (h:i≤ i')
    (hi':i'< (Qm p s u L0 1).r):(Qm p s u L0 1).cor i≤(Qm p s u L0 1).cor i':=by
 rw[Q6n,Q6n]
 have h1:i'< (Qz (Q1a s u 0 L0) (Q15 p G 1) (cN s 0 L0)).card:=hi'
 exact Nat.div_le_div_right (Qmu _ h h1)
lemma Qj3 (p s:ℕ) (u:ℕ→G) (L0:Q4w G) {i i':ℕ}
    (hi:i< (Qm p s u L0 1).r) (hi':i'< (Qm p s u L0 1).r)
    (hp:(Qm p s u L0 1).par i=(Qm p s u L0 1).par i')
    (hc:(Qm p s u L0 1).cor i=(Qm p s u L0 1).cor i'):i=i':=by
 rw[Qcf,Qcf]at hp
 rw[Q6n,Q6n]at hc
 have h1:=Nat.div_add_mod (Q1i (Qz (Q1a s u 0 L0) (Q15 p G 1) (cN s 0 L0)) i) s
 have h2:=Nat.div_add_mod (Q1i (Qz (Q1a s u 0 L0) (Q15 p G 1) (cN s 0 L0)) i') s
 rw[hp,hc]at h1
 exact Qmb _ hi hi' (h1.symm.trans h2)
lemma Qek [Finite G] {p m:ℕ} (hp:p.Prime) (hG:ZB G=p^m) {s:ℕ}
    (hs:2≤ s) (u:ℕ→G) (hstrict:Q10 (pN p G) u s)
    (hW:Q1e (pN p G) u s=lcs G 1)
    (hind:∀ k<s,u k∉ZA (u '' ZP k)⊔Qv p G):
    ∃ (d:Q5) (X:Fin d.n→G) (r :ℕ→ℕ),d.s=s∧d.n≤ m∧
      r 0=Group.rank G∧Q2 p u d X r :=by
 have:Fact p.Prime:=⟨hp⟩
 have hpg:IsPGroup p G:=IsPGroup.of_card hG
 have:Group.IsNilpotent G:=hpg.isNilpotent
 have hs0:0<s:=by omega
 have hx0:∀ a<s,(Q2n p s u).x a=u a:= fun a ha=>Q6f p s u ha
 have hr0:s≤(Q2n p s u).r :=Nat.le_add_right s _
 have hgen0:ZA ((Q2n p s u).x '' ZP (Q2n p s u).r)=⊤:=by
  apply Q25
  rw[Q1n hpg,eq_top_iff]
  intro g _
  exact Qlr p s u g
 have hcore:=Qhs hp hG hW
 have hU:=Qml p s u (Q2n p s u) hp hG hs0 hx0 (by rw[hgen0,top_sup_eq]) hcore hr0
 obtain ⟨N,hN⟩:∃ N,lcs G N=⊥:=Subgroup.nilpotent_iff_lowerCentralSeries.mp inferInstance
 have hL:lcs G (N+1+1)=⊥:=
   le_bot_iff.mp (hN▸Qd (D:=G) (show N≤N+1+1 by omega))
 have Hind:∀ w i,i<gR p s u w→
     Qar p s u w i∉ZA (Qar p s u w '' ZP i)⊔Q15 p G w:=by
  intro w i hi
  rcases w with _ | w
  · exact Qkn p s u hind hi
  · exact Qle p s u (Q2n p s u) w hi
 have Heq:∀ w,ZA (Qar p s u w '' ZP (gR p s u w))⊔Q15 p G w=
     lcs G w:=by
  intro w
  rcases w with _ | w
  · show ZA ((Q2n p s u).x '' ZP (Q2n p s u).r)⊔Qv p G=lcs G 0
    rw[hgen0,top_sup_eq,lcs_zero]
  · apply le_antisymm
    · refine sup_le ?_ (Q7l p w)
      rw[ZD]
      rintro _ ⟨i, -,rfl⟩
      exact Q7i p s u (Q2n p s u) (w+1) i
    · exact (hU w).trans (sup_le_sup_left (Q16 p (w+1)) _)
 have Hcard:∀ w,p^gR p s u w*ZB (Q15 p G w)=ZB (lcs G w):=by
  intro w
  have hmem:∀ i,Qar p s u w i∈lcs G w:= fun i=>Q7i p s u (Q2n p s u) w i
  have hN':∀ j,(ZA (Qar p s u w '' ZP j)⊔Q15 p G w).Normal:=
    fun j=>Q47 p w _ (by rintro _ ⟨i, -,rfl⟩; exact hmem i)
  have h1:=Qa2 hp hG (Q15 p G w) (v:=Qar p s u w) (gR p s u w)
    (fun k hk=>Hind w k hk)
  have h2:=Q5s hp.pos (Q15 p G w) (Qar p s u w) hN'
    (fun j=>Q98 p w _ (hmem j)) (gR p s u w)
  rw[Heq w]at h1 h2
  exact le_antisymm h1 h2
 have Hrank:gR p s u 0=Group.rank G:=by
  have h1:p^gR p s u 0*ZB (Qv p G)=ZB (lcs G 0):=Hcard 0
  have h2:=Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini G)
  rw[Q44 hpg,Q1n hpg]at h2
  have h3:ZB (lcs G 0)=ZB G:=by rw[lcs_zero,Subgroup.card_top]
  have h4:0<ZB (Qv p G):=Nat.card_pos
  have h6:p^gR p s u 0*ZB (Qv p G)=p^Group.rank G*ZB (Qv p G):=by
   rw[← h2, ← h3,h1]
  exact Nat.pow_right_injective hp.two_le (Nat.eq_of_mul_eq_mul_right h4 h6)
 have Hpa:∀ w i,i<gR p s u (w+1)→Qj7 p s u (w+1) i<gR p s u w:=
   fun w i hi=> (Q9a p s u (Q2n p s u) hs0 hr0 w hi).1
 have Hco:∀ w i,i<gR p s u (w+1)→Qba p s u (w+1) i<s:=
   fun w i hi=> (Q9a p s u (Q2n p s u) hs0 hr0 w hi).2.1
 have H1:∀ i,i<gR p s u 1→Qj7 p s u 1 i<Qba p s u 1 i:=
   fun i hi=> (Q9a p s u (Q2n p s u) hs0 hr0 0 hi).2.2.1 rfl
 have Hx:∀ w i,i<gR p s u (w+1)→Qar p s u (w+1) i=
     ⁅Qar p s u w (Qj7 p s u (w+1) i),Qar p s u 0 (Qba p s u (w+1) i)⁆:=by
  intro w i hi
  obtain ⟨-,hc, -,he⟩:=Q9a p s u (Q2n p s u) hs0 hr0 w hi
  have e0:Qar p s u 0 (Qba p s u (w+1) i)=u (Qba p s u (w+1) i):=Q6f p s u hc
  rw[e0]
  exact he
 have HS1:∀ k≤ s,∀ a b,a<b→ b<k→⁅u a,u b⁆∈
     ZA (Qar p s u 1 '' {i | i<gR p s u 1∧Qba p s u 1 i<k})⊔pN p G:=
   fun k hk a b hab hb=>Q62 p s u (Q2n p s u) hs0 hx0 hk hab hb
 have Hmono:∀ i i',i≤ i'→i'<gR p s u 1→Qba p s u 1 i≤Qba p s u 1 i':=
   fun i i' h hi'=>Qdi p s u (Q2n p s u) h hi'
 have Hinj:∀ i i',i<gR p s u 1→i'<gR p s u 1→Qj7 p s u 1 i=Qj7 p s u 1 i'→
     Qba p s u 1 i=Qba p s u 1 i'→i=i':=
   fun i i' hi hi' hp' hc=>Qj3 p s u (Q2n p s u) hi hi' hp' hc
 have Hw3:∀ i,i<gR p s u 2→Qba p s u 2 i≤Qba p s u 1 (Qj7 p s u 2 i):=
   fun i hi=>Qne p s u (Q2n p s u) hi
 obtain ⟨d,X,hds,hspec⟩:=Qlg (L:=N+1) (r :=gR p s u) (xs:=Qar p s u)
   (pa:=Qj7 p s u) (co:=Qba p s u) hp hG u hr0 Hpa Hco H1 Hx hx0 hgen0 (fun w _=>hU w) hL
   (by omega) Hind (fun w _=>Hcard w) HS1 Hmono Hinj hstrict Hw3
 refine ⟨d,X,Qk (N+1) (gR p s u),hds,?_,?_,hspec⟩
 · have h1:=hspec.realizes.card
   rw[hG]at h1
   have h2:=Nat.pow_right_injective hp.two_le h1
   rw[h2]
   exact hspec.n_le_sum
 · rw[Q5l (Nat.zero_le _)]
   exact Hrank
lemma Q6y [Finite G] {p m:ℕ} (hp:p.Prime) (hG:ZB G=p^m)
    (hna:lcs G 1≠⊥):
    ∃ (u :ℕ→G) (d:Q5) (X:Fin d.n→G) (r :ℕ→ℕ),
      2≤Qt G∧d.s=Qt G∧
      lcs G 1≤⁅ZA (u '' ZP d.s),ZA (u '' ZP d.s)⁆⊔
        lcs G 2∧
      Q10 (pN p G) u d.s∧Q1e (pN p G) u d.s=lcs G 1∧
      (∀ k<d.s,u k∉ZA (u '' ZP k)⊔Qv p G)∧
      d.n≤ m∧r 0=Group.rank G∧Q2 p u d X r :=by
 obtain ⟨hs2,u,hstrict,hW,hind,hcore⟩:=Qjt hp hG hna
 obtain ⟨d,X,r,hds,hnm,hrank,hspec⟩:=Qek hp hG hs2 u hstrict hW hind
 refine ⟨u,d,X,r,hs2,hds,?_,?_,?_,?_,hnm,hrank,hspec⟩
 · rw[hds]
   exact hcore
 · rw[hds]
   exact hstrict
 · rw[hds]
   exact hW
 · rw[hds]
   exact hind
end Q7
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
abbrev Q6 (c:ℕ) (r :Fin c→ℕ):Type:=Σ i:Fin c,Fin (r i)
abbrev Q3q (p c:ℕ) (r :Fin c→ℕ) (a:Q6 c r→ℕ):Type:=
  (k:Q6 c r)→(h:Q6 c r)→Fin (p^a h)
section PowerWordCount
variable (p:ℕ) {c:ℕ} {r :Fin c→ℕ} (a:Q6 c r→ℕ)
def Q3l (k h:Q6 c r) (x:ℕ):Prop:=
  k.1<h.1∨(h.1=k.1∧h.2.val<k.2.val∧p∣x)∨x =0
def Q55 (B:Q3q p c r a):Prop:=∀ k h,Q3l p k h (B k h).val
def Qbe (k h:Q6 c r):ℕ:=
  (if k.1<h.1 then a h else 0)+(if h.1=k.1∧h.2.val<k.2.val then a h - 1 else 0)
def sL (i:Fin c):ℕ:=∑ v:Fin (r i),a ⟨i,v⟩
def Q59 (i:Fin c):ℕ:=∑ u∈Finset.univ.filter (fun u=>i<u),sL a u
def Q69:ℕ:=
  ∑ i:Fin c,(r i*Q59 a i+∑ v:Fin (r i),(r i - 1 - v.val)*(a ⟨i,v⟩ - 1))
def Q2y:ℕ:=
  ∑ i:Fin c,(r i*Q59 a i+(r i - 1)*(sL a i - r i))
lemma Qju (k h:Q6 c r):
    ZB {x:Fin (p^a h)//Q3l p k h x.val}≤p^Qbe a k h:=by
 unfold Qbe
 by_cases h1:k.1<h.1
 · have h2:¬ (h.1=k.1∧h.2.val<k.2.val):=by
     intro h'
     rw[h'.1]at h1
     exact lt_irrefl _ h1
   rw[if_pos h1,if_neg h2,add_zero]
   calc ZB {x:Fin (p^a h)//Q3l p k h x.val}≤ZB (Fin (p^a h)):=
         Finite.card_subtype_le _
     _=p^a h:=Nat.card_fin _
 · by_cases h2:h.1=k.1∧h.2.val<k.2.val
   · rw [if_neg h1,if_pos h2,zero_add]
     have hdvd:∀ x:{x:Fin (p^a h)//Q3l p k h x.val},p∣x.1.val:=by
      intro x
      have hx:=x.2
      unfold Q3l at hx
      rcases hx with h' | ⟨_,_,hd⟩ | h0
      · exact absurd h' h1
      · exact hd
      · rw[h0]
        exact dvd_zero p
     have hlt:∀ x:{x:Fin (p^a h)//Q3l p k h x.val},x.1.val/p<p^(a h - 1):=by
      intro x
      have hx:x.1.val<p^a h:=x.1.isLt
      rcases Nat.eq_zero_or_pos (a h) with ha | ha
      · have hp1:p^a h=1:=by rw[ha,pow_zero]
        have hx0:x.1.val=0:=by omega
        have e:a h - 1=0:=by omega
        rw[e,hx0,Nat.zero_div,pow_zero]
        exact Nat.one_pos
      · obtain ⟨n,hn⟩:∃ n,a h=n+1:=⟨a h - 1,by omega⟩
        have hx':x.1.val<p*p^n:=by
         rw[← pow_succ', ← hn]
         exact hx
        have e:a h - 1=n:=by omega
        rw[e]
        exact Nat.div_lt_of_lt_mul hx'
     let f:{x:Fin (p^a h)//Q3l p k h x.val}→Fin (p^(a h - 1)):=
       fun x => ⟨x.1.val/p,hlt x⟩
     have hf:Function.Injective f:=by
      intro x y hxy
      have e:x.1.val/p=y.1.val/p:= congrArg Fin.val hxy
      apply Subtype.ext
      apply Fin.ext
      calc x.1.val=x.1.val/p*p:=(Nat.div_mul_cancel (hdvd x)).symm
        _=y.1.val/p*p:=by rw[e]
        _=y.1.val:=Nat.div_mul_cancel (hdvd y)
     calc ZB {x:Fin (p^a h)//Q3l p k h x.val}≤ZB (Fin (p^(a h - 1))):=
           Nat.card_le_card_of_injective f hf
       _=p^(a h - 1):=Nat.card_fin _
   · rw [if_neg h1,if_neg h2,add_zero,pow_zero]
     have h0:∀ x:{x:Fin (p^a h)//Q3l p k h x.val},x.1.val=0:=by
      intro x
      have hx:=x.2
      unfold Q3l at hx
      rcases hx with h' | ⟨e1,e2,_⟩ | h0
      · exact absurd h' h1
      · exact (h2 ⟨e1,e2⟩).elim
      · exact h0
     have hf:Function.Injective (fun _:{x:Fin (p^a h)//Q3l p k h x.val}=> ()):=by
       intro x y _
       apply Subtype.ext
       apply Fin.ext
       rw[h0 x,h0 y]
     calc ZB {x:Fin (p^a h)//Q3l p k h x.val}≤ZB Unit:=
           Nat.card_le_card_of_injective _ hf
       _=1:=Nat.card_unique
lemma Qdo:
    ZB {B:Q3q p c r a//Q55 p a B}≤p^(∑ k,∑ h,Qbe a k h):=by
 have e1:{B:Q3q p c r a//Q55 p a B}≃
     ((k:Q6 c r)→{row:(h:Q6 c r)→Fin (p^a h)//
       ∀ h,Q3l p k h (row h).val}):=
   @Equiv.subtypePiEquivPi (Q6 c r) (fun _=> (h:Q6 c r)→Fin (p^a h))
     (fun k row=> ∀ h,Q3l p k h (row h).val)
 have e2:∀ k:Q6 c r,{row:(h:Q6 c r)→Fin (p^a h)//
     ∀ h,Q3l p k h (row h).val}≃
     ((h:Q6 c r)→{x:Fin (p^a h)//Q3l p k h x.val}):=
   fun k=> @Equiv.subtypePiEquivPi (Q6 c r) (fun h=>Fin (p^a h))
     (fun h x =>Q3l p k h x.val)
 rw[Nat.card_congr e1,Nat.card_pi]
 calc ∏ k,ZB {row:(h:Q6 c r)→Fin (p^a h)//∀ h,Q3l p k h (row h).val}
       = ∏ k,∏ h,ZB {x:Fin (p^a h)//Q3l p k h x.val}:=by
         refine Finset.prod_congr rfl fun k _=>?_
         rw[Nat.card_congr (e2 k),Nat.card_pi]
   _ ≤ ∏ k,∏ h,p^Qbe a k h:=
         Finset.prod_le_prod' fun k _=>Finset.prod_le_prod' fun h _=>Qju p a k h
   _ = p ^(∑ k,∑ h,Qbe a k h):=by
         simp only[Finset.prod_pow_eq_pow_sum]
lemma Qlm:∑ k,∑ h,Qbe a k h=Q69 a:=by
 unfold Q69
 rw[Fintype.sum_sigma]
 refine Finset.sum_congr rfl fun i _=>?_
 have hA:∑ h:Q6 c r,(if i<h.1 then a h else 0)=Q59 a i:=by
   rw[Fintype.sum_sigma]
   unfold Q59 sL
   rw[Finset.sum_filter]
   refine Finset.sum_congr rfl fun u _=>?_
   by_cases hu:i<u
   · simp[hu]
   · simp[hu]
 have hB:∀ j:Fin (r i),
     ∑ h:Q6 c r,(if h.1=i∧h.2.val<j.val then a h - 1 else 0)=
       ∑ v:Fin (r i),(if v.val<j.val then a ⟨i,v⟩ - 1 else 0):=by
   intro j
   rw[Fintype.sum_sigma,Fintype.sum_eq_single i]
   · simp
   · intro u hu
     simp[hu]
 have hrow:∀ j:Fin (r i),∑ h,Qbe a ⟨i,j⟩ h=
     Q59 a i+∑ v:Fin (r i),(if v.val<j.val then a ⟨i,v⟩ - 1 else 0):=by
   intro j
   rw[← hA, ← hB j, ← Finset.sum_add_distrib]
   rfl
 rw [Finset.sum_congr rfl fun j _=>hrow j,Finset.sum_add_distrib,Finset.sum_const,
   Finset.card_univ,Fintype.card_fin,smul_eq_mul,Finset.sum_comm]
 congr 1
 refine Finset.sum_congr rfl fun v _=>?_
 rw[← Finset.sum_filter,Finset.sum_const,smul_eq_mul]
 congr 1
 rw[← Fin.card_Ioi (a:=v)]
 congr 1
 ext j
 simp
lemma Qbu (ha:∀ k,1≤a k):Q69 a≤Q2y a:=by
 unfold Q69 Q2y
 refine Finset.sum_le_sum fun i _=>?_
 have hs:∑ v:Fin (r i),(a ⟨i,v⟩ - 1)=sL a i - r i:=by
  have h1:∑ v:Fin (r i),(a ⟨i,v⟩ - 1+1)=sL a i:=
    Finset.sum_congr rfl fun v _=>Nat.sub_add_cancel (ha _)
  rw [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,mul_one]at h1
  omega
 have h2:∑ v:Fin (r i),(r i - 1 - v.val)*(a ⟨i,v⟩ - 1)≤
     ∑ v:Fin (r i),(r i - 1)*(a ⟨i,v⟩ - 1):=
   Finset.sum_le_sum fun v _=>Nat.mul_le_mul (Nat.sub_le _ _) le_rfl
 rw[← Finset.mul_sum,hs]at h2
 exact Nat.add_le_add_left h2 _
lemma Qfc:
    ZB {B:Q3q p c r a//Q55 p a B}≤p^Q69 a:=by
 rw[← Qlm]
 exact Qdo p a
end PowerWordCount
section PowerWordGroup
variable {p:ℕ} [hp:Fact p.Prime]
lemma Q8z {Q:Type u} [Group Q] [Finite Q] (hQ:IsPGroup p Q)
    {n:ℕ} (y:Fin n→Q) (hgen:ZA (ZG y)=⊤)
    (hirr :∀ v,ZA (y '' {w | w≠v})≠⊤) (e:Fin n→ℕ)
    (he:(ZR fun v=>y v^e v).prod∈frattini Q) (v:Fin n):p∣e v:=by
  by_contra hv
  have hker :(Q12 Q).ker= frattini Q:=Qfw hQ
  have hprod:∏ w,(Q12 Q) (y w)^e w=1:=by
   have h1:(Q12 Q) (ZR fun v=>y v^e v).prod=1:=by
     rw[← MonoidHom.mem_ker,hker]
     exact he
   rw[map_list_prod,List.map_ofFn,List.prod_ofFn]at h1
   simp only[Function.comp_def,map_pow]at h1
   exact h1
  have hM:(Q12 Q) (y v)^e v∈(ZA (y '' {w | w≠v})).map (Q12 Q):=by
    have h2:(Q12 Q) (y v)^e v*
        ∏ w∈Finset.univ.erase v,(Q12 Q) (y w)^e w=1:=by
     rw [Finset.mul_prod_erase Finset.univ (fun w=> (Q12 Q) (y w)^e w)
       (Finset.mem_univ v)]
     exact hprod
    have h3:∏ w∈Finset.univ.erase v,(Q12 Q) (y w)^e w∈
        (ZA (y '' {w | w≠v})).map (Q12 Q):=by
      refine prod_mem fun w hw=>?_
      have hmem:y w∈y '' {w | w≠v}:=⟨w,Finset.ne_of_mem_erase hw,rfl⟩
      exact pow_mem (Subgroup.mem_map_of_mem (Q12 Q) (ZC hmem)) _
    rw[eq_inv_of_mul_eq_one_left h2]
    exact inv_mem h3
  have hpow1:(Q12 Q) (y v)^p=1:=by
   rw[← map_pow, ← MonoidHom.mem_ker,hker,Q1n hQ]
   exact Q2c p (y v)
  have hcop:Nat.Coprime (e v) p:=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hv)
  have hyM:(Q12 Q) (y v)∈(ZA (y '' {w | w≠v})).map (Q12 Q):=by
    have e1:(Q12 Q) (y v)=((Q12 Q) (y v)^(e v:ℤ))^(Nat.gcdA (e v) p)*
        ((Q12 Q) (y v)^(p:ℤ))^(Nat.gcdB (e v) p):=by
     rw [← zpow_mul, ← zpow_mul, ← zpow_add, ← Nat.gcd_eq_gcd_ab,Nat.Coprime.gcd_eq_one hcop,
       Nat.cast_one,zpow_one]
    rw[e1]
    refine mul_mem (zpow_mem ?_ _) (zpow_mem ?_ _)
    · rw[zpow_natCast]
      exact hM
    · rw[zpow_natCast,hpow1]
      exact one_mem _
  obtain ⟨s,hs,hsy⟩:=Subgroup.mem_map.mp hyM
  have hyK:y v∈ZA (y '' {w | w≠v})⊔frattini Q:=by
    have hk:s⁻¹*y v∈frattini Q:=by
     rw[← hker,MonoidHom.mem_ker,map_mul,map_inv,hsy,inv_mul_cancel]
    have hsplit:y v=s*(s⁻¹*y v):=by group
    rw[hsplit]
    exact Subgroup.mul_mem_sup hs hk
  have htop:ZA (y '' {w | w≠v})⊔frattini Q=⊤:=by
    rw[eq_top_iff, ← hgen,ZD]
    rintro _ ⟨w,rfl⟩
    by_cases hw:w=v
    · rw[hw]
      exact hyK
    · have hmem:y w∈y '' {w | w≠v}:=⟨w,hw,rfl⟩
      exact ZJ (ZC hmem)
  exact hirr v (Q25 htop)
lemma Qaz {H:Type u} [Group H] (N:Subgroup H) [N.Normal]
    [Finite (H⧸N)] (hQ:IsPGroup p (H⧸N)) {n:ℕ} (x:Fin n→H)
    (hgen:ZA (ZG fun v=> (x v:H⧸N))=⊤)
    (hirr :∀ v,ZA ((fun w=> (x w:H⧸N)) '' {w | w≠v})≠⊤)
    (j:Fin n) (A:ℕ) (hA:1≤A) (b:Fin n→ℕ) (z:H) (hz:z∈N)
    (hrel:x j^p^A=(ZR fun v=>x v^b v).prod*z) (v:Fin n):p∣b v:=by
  refine Q8z hQ (fun v=> (x v:H⧸N)) hgen hirr b ?_ v
  show (ZR fun v=> (x v:H⧸N)^b v).prod∈frattini (H⧸N)
  have h1:((x j^p^A:H):H⧸N)=(((ZR fun v=>x v^b v).prod:H):H⧸N):=by
    rw[hrel,QuotientGroup.mk_mul,(QuotientGroup.eq_one_iff z).mpr hz,mul_one]
  have h2:(((ZR fun v=>x v^b v).prod:H):H⧸N)=
      (ZR fun v=> (x v:H⧸N)^b v).prod:=by
    rw[← QuotientGroup.mk'_apply,map_list_prod,List.map_ofFn]
    simp only[Function.comp_def,QuotientGroup.mk'_apply,QuotientGroup.mk_pow]
  rw[← h2, ← h1,QuotientGroup.mk_pow,Q1n hQ]
  obtain ⟨A',rfl⟩:∃ A',A=A'+1:=⟨A - 1,by omega⟩
  rw[show p^(A'+1)=p*p^A' from pow_succ' p A',pow_mul]
  exact pow_mem (Q2c p _) _
abbrev Q1r (G:Type u) [Group G] (i:ℕ):Type u:=
  ↥(lcs G i)⧸(lcs G (i+1)).subgroupOf (lcs G i)
structure Q40 (p:ℕ) {G:Type u} [Group G] {c:ℕ} {r :Fin c→ℕ}
    (a:Q6 c r→ℕ) (g:Q6 c r→G) (B:Q3q p c r a):Prop where
  mem:∀ k,g k∈lcs G k.1
  gen :∀ i:Fin c,ZA (ZG fun v:Fin (r i)=>
      (QuotientGroup.mk (⟨g ⟨i,v⟩,mem ⟨i,v⟩⟩:lcs G i):Q1r G i))=⊤
  irr :∀ (i:Fin c) (v:Fin (r i)),ZA ((fun w:Fin (r i)=>
      (QuotientGroup.mk (⟨g ⟨i,w⟩,mem ⟨i,w⟩⟩:lcs G i):Q1r G i)) '' {w | w≠v})≠⊤
  pos:∀ k,1≤a k
  supp:∀ k h,¬ k.1<h.1→¬ (h.1=k.1∧h.2.val<k.2.val)→(B k h).val=0
  pow : ∀ (i:Fin c) (j:Fin (r i)),g ⟨i,j⟩^p^a ⟨i,j⟩=
      (ZR fun v:Fin (r i)=>g ⟨i,v⟩^(B ⟨i,j⟩ ⟨i,v⟩).val).prod*
      (ZR fun u:Fin c=>if i<u then
        (ZR fun v:Fin (r u)=>g ⟨u,v⟩^(B ⟨i,j⟩ ⟨u,v⟩).val).prod else 1).prod
lemma Q4m {G:Type u} [Group G] {c:ℕ} {r :Fin c→ℕ} (g:Q6 c r→G)
    (hmem:∀ k,g k∈lcs G k.1) (b:Q6 c r→ℕ) (i:Fin c):
    (List.ofFn fun u:Fin c=>if i<u then
      (ZR fun v:Fin (r u)=>g ⟨u,v⟩^b ⟨u,v⟩).prod else 1).prod∈
        lcs G ((i:ℕ)+1):=by
  refine Subgroup.list_prod_mem _ fun x hx =>?_
  rw[List.mem_ofFn']at hx
  obtain ⟨u,rfl⟩:=hx
  dsimp only
  split_ifs with hu
  · refine Subgroup.list_prod_mem _ fun y hy=>?_
    rw[List.mem_ofFn']at hy
    obtain ⟨v,rfl⟩:=hy
    exact Subgroup.pow_mem _ (Qd (Nat.succ_le_of_lt (hu:(i:ℕ)<u))
      (hmem ⟨u,v⟩)) _
  · exact Subgroup.one_mem _
lemma Q40.Qgm {G:Type u} [Group G] [Finite G] (hG:IsPGroup p G)
    {c:ℕ} {r :Fin c→ℕ} {a:Q6 c r→ℕ} {g:Q6 c r→G} {B:Q3q p c r a}
    (hd:Q40 p a g B) (i:Fin c) (j v:Fin (r i)):
    p∣(B ⟨i,j⟩ ⟨i,v⟩).val:=by
 have hQ:IsPGroup p (Q1r G i):=(hG.to_subgroup _).to_quotient _
 have hdeep:=Q4m g hd.mem (fun h=> (B ⟨i,j⟩ h).val) i
 have htail:(ZR fun u:Fin c=>if i<u then
     (ZR fun v:Fin (r u)=>g ⟨u,v⟩^(B ⟨i,j⟩ ⟨u,v⟩).val).prod else 1).prod∈
       lcs G i:=Qd (Nat.le_succ _) hdeep
 have hz:(⟨_,htail⟩:lcs G i)∈(lcs G ((i:ℕ)+1)).subgroupOf (lcs G i):=
   Subgroup.mem_subgroupOf.mpr hdeep
 have hrel:(⟨g ⟨i,j⟩,hd.mem ⟨i,j⟩⟩:lcs G i)^p^a ⟨i,j⟩=
     (ZR fun w:Fin (r i)=>
       (⟨g ⟨i,w⟩,hd.mem ⟨i,w⟩⟩:lcs G i)^(B ⟨i,j⟩ ⟨i,w⟩).val).prod*⟨_,htail⟩:=by
   apply (lcs G i).subtype_injective
   rw[map_mul,map_pow,map_list_prod,List.map_ofFn]
   simp only[Function.comp_def,map_pow,Subgroup.coe_subtype]
   exact hd.pow i j
 exact Qaz ((lcs G ((i:ℕ)+1)).subgroupOf (lcs G i)) hQ
   (fun w=> (⟨g ⟨i,w⟩,hd.mem ⟨i,w⟩⟩:lcs G i)) (hd.gen i) (hd.irr i) j (a ⟨i,j⟩)
   (hd.pos _) (fun w=> (B ⟨i,j⟩ ⟨i,w⟩).val) _ hz hrel v
lemma Q40.Qng {G:Type u} [Group G] [Finite G] (hG:IsPGroup p G)
    {c:ℕ} {r :Fin c→ℕ} {a:Q6 c r→ℕ} {g:Q6 c r→G} {B:Q3q p c r a}
    (hd:Q40 p a g B):Q55 p a B:=by
 rintro ⟨i,j⟩ ⟨u,v⟩
 by_cases h1:i<u
 · exact Or.inl h1
 by_cases h2:u=i∧v.val<j.val
 · obtain ⟨hu,hv⟩:=h2
   subst hu
   exact Or.inr (Or.inl ⟨rfl,hv,hd.Qgm hG _ _ _⟩)
 · exact Or.inr (Or.inr (hd.supp ⟨i,j⟩ ⟨u,v⟩ h1 h2))
def Q48 (p c:ℕ) (r :Fin c→ℕ) (a:Q6 c r→ℕ):Set (Q3q p c r a):=
  {B | ∃ (G:Type) (_:Group G) (_:Finite G) (g:Q6 c r→G),
    IsPGroup p G∧Q40 p a g B}
lemma Qb8 (c:ℕ) (r :Fin c→ℕ) (a:Q6 c r→ℕ):
    (Q48 p c r a).ncard≤p^Q69 a:=by
 have hsub:Q48 p c r a⊆{B | Q55 p a B}:=by
   rintro B ⟨G,_,_,g,hG,hd⟩
   exact hd.Qng hG
 calc (Q48 p c r a).ncard≤{B | Q55 p a B}.ncard:=
       Set.ncard_le_ncard hsub (Set.toFinite _)
   _=ZB {B:Q3q p c r a//Q55 p a B}:=(Nat.card_coe_set_eq _).symm
   _≤p^Q69 a:=Qfc p a
lemma Qgl (c:ℕ) (r :Fin c→ℕ) (a:Q6 c r→ℕ) (ha:∀ k,1≤a k):
    (Q48 p c r a).ncard≤p^Q2y a:=
  (Qb8 c r a).trans
    (Nat.pow_le_pow_right hp.out.pos (Qbu a ha))
lemma Qag {Q:Type u} [Group Q] {n:ℕ} (y:Fin n→Q)
    (hmin:∀ (m:ℕ) (z:Fin m→Q),ZA (ZG z)=⊤→n≤ m)
    (v:Fin n):ZA (y '' {w | w≠v})≠⊤:=by
  intro htop
  obtain ⟨m,rfl⟩:∃ m,n=m+1:=⟨n - 1,by have:=v.isLt; omega⟩
  have hr :ZG (y∘v.succAbove)=y '' {w | w≠v}:=by
    rw[Set.range_comp,Fin.range_succAbove]
    ext w
    simp
  have h:=hmin m (y∘v.succAbove) (by rw[hr]; exact htop)
  omega
lemma Q3i {M:Type*} [Monoid M] (n:ℕ):∀ (f:Fin n→M) (i:Fin n),
    (∀ u,u< i→ f u=1)→
    (ZR f).prod= f i*(ZR fun u=>if i<u then f u else 1).prod:=by
  induction n with
  | zero=>intro f i; exact i.elim0
  | succ n ih=>
    intro f i hf
    rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i',rfl⟩
    · simp[List.ofFn_succ,Fin.succ_pos]
    · have hf0:f 0=1:=hf 0 (Fin.succ_pos i')
      have hrec:=ih (fun u=>f u.succ) i'
        (fun u hu=>hf u.succ (Fin.succ_lt_succ_iff.mpr hu))
      rw[List.ofFn_succ,List.prod_cons,hf0,one_mul,hrec]
      conv_rhs=>rw[List.ofFn_succ,List.prod_cons]
      simp[Fin.succ_lt_succ_iff,Fin.not_lt_zero]
section Bridge
variable {G:Type u} [Group G] {c:ℕ} {r :Fin c→ℕ}
def Qu (g:Q6 c r→G) (e:Q6 c r→ℕ) (u:Fin c):G:=
  (ZR fun v:Fin (r u)=>g ⟨u,v⟩^e ⟨u,v⟩).prod
def Q2w (g:Q6 c r→G) (e:Q6 c r→ℕ):G:=
  (ZR fun u:Fin c=>Qu g e u).prod
def Qay (g:Q6 c r→G) (i:Fin c) (j:ℕ):Subgroup G:=
  ZA {x | ∃ v:Fin (r i),v.val<j∧g ⟨i,v⟩=x}⊔lcs G ((i:ℕ)+1)
def Qe3 (i:Fin c) (j:ℕ) (e:Q6 c r→ℕ):Prop:=
  ∀ h:Q6 c r,(h.1< i∨(h.1=i∧j≤h.2.val))→e h=0
structure Q5k (p:ℕ) (a:Q6 c r→ℕ) (g:Q6 c r→G) where
  coord:G→(h:Q6 c r)→Fin (p^a h)
  uniq:∀ e:(h:Q6 c r)→Fin (p^a h),coord (Q2w g fun h=> (e h).val)=e
  sub :∀ (i:Fin c) (j:ℕ) (x:G),x∈Qay g i j→
    ∃ e:(h:Q6 c r)→Fin (p^a h),
      Qe3 i j (fun h=> (e h).val)∧Q2w g (fun h=> (e h).val)=x
lemma Q5k.Q6p {p:ℕ} {a:Q6 c r→ℕ} {g:Q6 c r→G}
    (nf:Q5k p a g) (i:Fin c) (j:ℕ) (x:G) (hx:x∈Qay g i j):
    Qe3 i j (fun h=> (nf.coord x h).val)∧
      Q2w g (fun h=> (nf.coord x h).val)=x:=by
  obtain ⟨e,he,hprod⟩:=nf.sub i j x hx
  have hc:nf.coord x =e:=by
   rw[← hprod]
   exact nf.uniq e
  rw[hc]
  exact ⟨he,hprod⟩
structure Q7 (p:ℕ) (a:Q6 c r→ℕ) (g:Q6 c r→G) where
  mem:∀ k,g k∈lcs G k.1
  gen :∀ i:Fin c,ZA (ZG fun v:Fin (r i)=>
      (QuotientGroup.mk (⟨g ⟨i,v⟩,mem ⟨i,v⟩⟩:lcs G i):Q1r G i))=⊤
  minimum:∀ (i:Fin c) (n:ℕ) (y:Fin n→Q1r G i),
    ZA (ZG y)=⊤→ r i≤n
  pos:∀ k,1≤a k
  rel:∀ (i:Fin c) (j:Fin (r i)),g ⟨i,j⟩^p^a ⟨i,j⟩∈Qay g i j.val
  nf:Q5k p a g
def Q7.Ql {p:ℕ} {a:Q6 c r→ℕ} {g:Q6 c r→G}
    (S:Q7 p a g):Q3q p c r a:=
  fun k=>S.nf.coord (g k^p^a k)
lemma Q7.Qd3 {p:ℕ} {a:Q6 c r→ℕ} {g:Q6 c r→G}
    (S:Q7 p a g):Q40 p a g S.Ql where
  mem:=S.mem
  gen:=S.gen
  irr := fun i v=>Qag _ (S.minimum i) v
  pos:=S.pos
  supp :=by
    rintro ⟨i,j⟩ ⟨u,v⟩ h1 h2
    have hs:=(S.nf.Q6p i j.val _ (S.rel i j)).1
    refine hs ⟨u,v⟩ ?_
    have h1':u≤ i:=not_lt.mp h1
    rcases lt_or_eq_of_le h1' with hu | hu
    · exact Or.inl hu
    · subst hu
      exact Or.inr ⟨rfl,not_lt.mp fun hv=>h2 ⟨rfl,hv⟩⟩
  pow := by
    intro i j
    obtain ⟨hs,hprod⟩:=S.nf.Q6p i j.val _ (S.rel i j)
    show g ⟨i,j⟩^p^a ⟨i,j⟩=
      (ZR fun v:Fin (r i)=>
        g ⟨i,v⟩^(S.nf.coord (g ⟨i,j⟩^p^a ⟨i,j⟩) ⟨i,v⟩).val).prod*
      (List.ofFn fun u:Fin c=>if i<u then
        (ZR fun v:Fin (r u)=>
          g ⟨u,v⟩^(S.nf.coord (g ⟨i,j⟩^p^a ⟨i,j⟩) ⟨u,v⟩).val).prod else 1).prod
    have hf:∀ u,u< i→
        Qu g (fun h=> (S.nf.coord (g ⟨i,j⟩^p^a ⟨i,j⟩) h).val) u=1:=by
      intro u hu
      unfold Qu
      refine List.prod_eq_one fun x hx =>?_
      rw[List.mem_ofFn']at hx
      obtain ⟨v,rfl⟩:=hx
      have h0:(S.nf.coord (g ⟨i,j⟩^p^a ⟨i,j⟩) ⟨u,v⟩).val=0:=
        hs ⟨u,v⟩ (Or.inl hu)
      show g ⟨u,v⟩^(S.nf.coord (g ⟨i,j⟩^p^a ⟨i,j⟩) ⟨u,v⟩).val=1
      rw[h0,pow_zero]
    have hsplit:=Q3i _
      (fun u=>Qu g (fun h=> (S.nf.coord (g ⟨i,j⟩^p^a ⟨i,j⟩) h).val) u) i hf
    conv_lhs=>rw[← hprod]
    exact hsplit
end Bridge
lemma Q7.Qhe {G:Type} [Group G] [Finite G] (hG:IsPGroup p G)
    {c:ℕ} {r :Fin c→ℕ} {a:Q6 c r→ℕ} {g:Q6 c r→G}
    (S:Q7 p a g):S.Ql∈Q48 p c r a:=
  ⟨G,inferInstance,inferInstance,g,hG,S.Qd3⟩
end PowerWordGroup
end OMA.SimsLite
namespace OMA.SimsLite
section DataCount
lemma Qa5 {α β:Type*} {S:Set α} (D:Finset β) (F:α→β)
    (hF:∀ s∈S,F s∈D) (hinj:Set.InjOn F S):S.ncard≤D.card:=by
 have h:=Set.ncard_le_ncard_of_injOn (t:=(D:Set β)) F
   (fun s hs=>Finset.mem_coe.2 (hF s hs)) hinj D.finite_toSet
 rwa[Set.ncard_coe_finset]at h
lemma Qbh {α β:Type*} {S:Set α} (D:Finset β) (P:α→β→Prop)
    (hex:∀ s∈S,∃ d∈D,P s d)
    (huniq:∀ s₁∈S,∀ s₂∈S,∀ d,P s₁ d→P s₂ d→s₁=s₂):S.ncard≤D.card:=by
 classical
 rcases D.eq_empty_or_nonempty with hD | ⟨d₀, -⟩
 · have hS:S= ∅ :=by
     ext s
     simp only[Set.mem_empty_iff_false,iff_false]
     intro hs
     obtain ⟨d,hd, -⟩:=hex s hs
     simp[hD]at hd
   simp[hS]
 · let F:α→β:= fun s=>if h:∃ d∈D,P s d then h.choose else d₀
   have hF:∀ s∈S,F s∈D ∧P s (F s):=by
    intro s hs
    have h:=hex s hs
    simp only[F,dif_pos h]
    exact h.choose_spec
   refine Qa5 D F (fun s hs=> (hF s hs).1) ?_
   intro s₁ h₁ s₂ h₂ heq
   have h₂':P s₂ (F s₁):=by
    rw[heq]
    exact (hF s₂ h₂).2
   exact huniq s₁ h₁ s₂ h₂ (F s₁) (hF s₁ h₁).2 h₂'
lemma Qc6 {ι α:Type*} {β:ι→Type*} {S:Set α} (I:Finset ι)
    (D:∀ i,Finset (β i)) (P:∀ i,α→β i→Prop)
    (hex:∀ s∈S,∃ i∈I,∃ d∈D i,P i s d)
    (huniq:∀ s₁∈S,∀ s₂∈S,∀ i d,P i s₁ d→P i s₂ d→s₁=s₂):
    S.ncard≤∑ i∈I,(D i).card:=by
 rw[← Finset.card_sigma]
 refine Qbh (I.sigma D) (fun s x =>P x.1 s x.2) ?_ ?_
 · intro s hs
   obtain ⟨i,hi,d,hd,h⟩:=hex s hs
   exact ⟨⟨i,d⟩,Finset.mem_sigma.2 ⟨hi,hd⟩,h⟩
 · rintro s₁ h₁ s₂ h₂ ⟨i,d⟩ hP₁ hP₂
   exact huniq s₁ h₁ s₂ h₂ i d hP₁ hP₂
abbrev Q5a (k n:ℕ):Type:=
  {a:Fin k→Fin (n+1)//(∀ i,0< (a i).val)∧∑ i,(a i).val=n}
def Q5a.toComp {k n:ℕ} (a:Q5a k n):Composition n where
  blocks:=ZR (fun i=> (a.1 i).val)
  blocks_pos:=by
    intro x hx
    rw[List.mem_ofFn]at hx
    obtain ⟨i,rfl⟩:=hx
    exact a.2.1 i
  blocks_sum:=by
    rw[List.sum_ofFn]
    exact a.2.2
lemma Q5a.Q66 (k n:ℕ):Function.Injective (@Q5a.toComp k n):=by
 intro a b h
 have h2:ZR (fun i=> (a.1 i).val)=ZR (fun i=> (b.1 i).val):=
   congrArg Composition.blocks h
 have h3:=List.ofFn_injective h2
 apply Subtype.ext
 funext i
 exact Fin.ext (congrFun h3 i)
lemma Qam (k n:ℕ):Fintype.card (Q5a k n)≤2^(n - 1):=
  (Fintype.card_le_of_injective _ (Q5a.Q66 k n)).trans_eq (composition_card n)
abbrev Q1w (m c:ℕ):Type:=
  {r :Fin c→Fin (m+1)//(∀ i,0< (r i).val)∧∑ i,(r i).val≤ m}
def Q1w.toComp {m c:ℕ} (r :Q1w m c):Composition (m+1) where
  blocks:=ZR (fun i=> (r.1 i).val) ++[m+1 - ∑ i,(r.1 i).val]
  blocks_pos:=by
    intro x hx
    rw[List.mem_append,List.mem_ofFn,List.mem_singleton]at hx
    rcases hx with ⟨i,rfl⟩ | rfl
    · exact r.2.1 i
    · have:=r.2.2
      omega
  blocks_sum:=by
    rw[List.sum_append,List.sum_ofFn,List.sum_singleton]
    have:=r.2.2
    omega
lemma Q1w.Q66 (m c:ℕ):Function.Injective (@Q1w.toComp m c):=by
 intro a b h
 have h2:ZR (fun i=> (a.1 i).val) ++[m+1 - ∑ i,(a.1 i).val]
     =ZR (fun i=> (b.1 i).val) ++[m+1 - ∑ i,(b.1 i).val]:=
   congrArg Composition.blocks h
 have h3:ZR (fun i=> (a.1 i).val)=ZR (fun i=> (b.1 i).val):=
   List.append_inj_left' h2 (by simp)
 have h4:=List.ofFn_injective h3
 apply Subtype.ext
 funext i
 exact Fin.ext (congrFun h4 i)
lemma Qf5 (m c:ℕ):Fintype.card (Q1w m c)≤2^m:=by
 have h:=Fintype.card_le_of_injective _ (Q1w.Q66 m c)
 rw[composition_card,Nat.add_sub_cancel]at h
 exact h
def Q1w.tot {m c:ℕ} (r :Q1w m c):ℕ:=∑ i,(r.1 i).val
def Q1w.r2 {m c:ℕ} (r :Q1w m c):ℕ:=
  ∑ i∈Finset.univ.filter (fun i:Fin c=>i.val=1),(r.1 i).val
def Q1w.r3 {m c:ℕ} (r :Q1w m c):ℕ:=
  ∑ i∈Finset.univ.filter (fun i:Fin c=>2≤ i.val),(r.1 i).val
lemma Q1w.Qjk {m c:ℕ} (r :Q1w m c):r.r2+r.r3≤ m:=by
 have hdisj:Disjoint (Finset.univ.filter (fun i:Fin c=>i.val=1))
     (Finset.univ.filter (fun i:Fin c=>2≤ i.val)):=by
   rw[Finset.disjoint_filter]
   intro i _ h1 h2
   omega
 unfold Q1w.r2 Q1w.r3
 rw[← Finset.sum_union hdisj]
 exact (Finset.sum_le_sum_of_subset (Finset.subset_univ _)).trans r.2.2
lemma Q6u {ι:Type*} [Fintype ι] (f:ι→ℕ) (A B:ℕ)
    (hA:Fintype.card ι≤A) (hB:∀ i,f i≤B):∑ i,f i≤A*B:=by
 calc ∑ i,f i≤∑ _i:ι,B:=Finset.sum_le_sum (fun i _=>hB i)
   _=Fintype.card ι*B:=by simp
   _≤A*B:=Nat.mul_le_mul hA le_rfl
abbrev Qh2 (m s r₂ R₃:ℕ):Type:=(Fin r₂→Fin (s - 1))×(Fin R₃→Fin m×Fin m)
lemma Qir (m s r₂ R₃:ℕ):
    Fintype.card (Qh2 m s r₂ R₃)=(s - 1)^r₂*(m*m)^R₃:=by
 simp only[Fintype.card_prod,Fintype.card_fun,Fintype.card_fin]
lemma Qfe (m s r₂ R₃:ℕ) (hs:s≤ m+1) (hr :r₂+R₃≤ m):
    Fintype.card (Qh2 m s r₂ R₃)≤ m^(2*m):=by
 rw[Qir]
 rcases Nat.eq_zero_or_pos m with rfl | hm
 · have h1:r₂=0:=by omega
   have h2:R₃=0:=by omega
   subst h1
   subst h2
   simp
 · calc (s - 1)^r₂*(m*m)^R₃≤ m^r₂*(m*m)^R₃:=
         Nat.mul_le_mul (Nat.pow_le_pow_left (by omega) _) le_rfl
     _=m^(r₂+2*R₃):=by ring
     _≤ m^(2*m):=Nat.pow_le_pow_right hm (by omega)
lemma Qes (R m:ℕ):Fintype.card (Q5a R m)≤2^(m - 1):=
  Qam R m
abbrev Qg (m:ℕ):Type:=
  Σ c:Fin (m+1),Σ s:Fin (m+1),Σ r :Q1w m c.val,
    Q5a (s.val - 1) r.r2×Qh2 m s.val r.r2 r.r3×Q5a r.tot m
lemma Qgf (m:ℕ):
    Fintype.card (Qg m)≤
      (m+1)*((m+1)*(2^m*(2^(m - 1)*(m^(2*m)*2^(m - 1))))):=by
 rw[Fintype.card_sigma]
 refine Q6u _ _ _ (by simp) (fun c=>?_)
 rw[Fintype.card_sigma]
 refine Q6u _ _ _ (by simp) (fun s=>?_)
 rw[Fintype.card_sigma]
 refine Q6u _ _ _ (Qf5 m c.val) (fun r=>?_)
 have hr :=r.Qjk
 rw[Fintype.card_prod,Fintype.card_prod]
 refine Nat.mul_le_mul ?_ (Nat.mul_le_mul ?_ ?_)
 · exact (Qam _ _).trans (Nat.pow_le_pow_right (by norm_num) (by omega))
 · exact Qfe m s.val r.r2 r.r3 (by omega) hr
 · exact Qes r.tot m
lemma Qc8 (m:ℕ) (hm:1≤ m):
    Fintype.card (Qg m)≤(m+1)^(5*m+2):=by
 refine (Qgf m).trans ?_
 have h1:2^(m - 1)≤2^m:=Nat.pow_le_pow_right (by norm_num) (Nat.sub_le m 1)
 have h2:m^(2*m)≤(m+1)^(2*m):=Nat.pow_le_pow_left (Nat.le_succ m) _
 have h8:(8:ℕ)≤(m+1)^3:=by
  calc (8:ℕ)=2^3:=by norm_num
    _≤(m+1)^3:=Nat.pow_le_pow_left (by omega) 3
 have h3:2^m*2^m*2^m≤(m+1)^(3*m):=by
  calc 2^m*2^m*2^m=(2*2*2)^m:=by rw[mul_pow,mul_pow]
    _=8^m:=by norm_num
    _≤((m+1)^3)^m:=Nat.pow_le_pow_left h8 m
    _=(m+1)^(3*m):=by rw[← pow_mul]
 calc (m +1)*((m+1)*(2^m*(2^(m - 1)*(m^(2*m)*2^(m - 1)))))
     ≤ (m +1)*((m+1)*(2^m*(2^m*((m+1)^(2*m)*2^m)))):=
       Nat.mul_le_mul le_rfl (Nat.mul_le_mul le_rfl
         (Nat.mul_le_mul le_rfl (Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h1))))
   _=(m+1)^2*(2^m*2^m*2^m)*(m+1)^(2*m):=by ring
   _ ≤ (m+1)^2*(m+1)^(3*m)*(m+1)^(2*m):=
       Nat.mul_le_mul (Nat.mul_le_mul le_rfl h3) le_rfl
   _=(m+1)^(5*m+2):=by ring
end DataCount
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section ListProd
lemma Q7q {D:Type u} [Group D]:∀ (n:ℕ) (f:Fin n→D),
    sprod n f=(ZR f).prod
  | 0,f=>by
    show (1:D)=(ZR f).prod
    rw[List.ofFn_zero,List.prod_nil]
  | n+1,f=>by
    show f 0*sprod n (fun i=>f i.succ)=_
    rw[Q7q n,List.ofFn_succ,List.prod_cons]
lemma Qgu {D:Type u} {n n':ℕ} (h:n=n') (F:ℕ→D):
    ZR (fun t:Fin n=>F t.val)=ZR (fun t:Fin n'=>F t.val):=by
  subst h
  rfl
lemma Qb1 {D:Type u} [Monoid D] (r :ℕ→ℕ) (F:ℕ→D):∀ c:ℕ,
    (List.ofFn fun t:Fin (Q0 r c)=>F t.val).prod=
      (ZR fun i:Fin c=>
        (ZR fun v:Fin (r i.val)=>F (Q0 r i.val+v.val)).prod).prod
  | 0 => by
    show (ZR fun t:Fin 0=>F t.val).prod=
      (ZR fun i:Fin 0=>
        (ZR fun v:Fin (r i.val)=>F (Q0 r i.val+v.val)).prod).prod
    rw[List.ofFn_zero,List.ofFn_zero]
  | c + 1 =>by
    have hL:(ZR fun t:Fin (Q0 r c+r c)=>F t.val)=
        (ZR fun t:Fin (Q0 r c)=>F t.val) ++
          (ZR fun v:Fin (r c)=>F (Q0 r c+v.val)):=by
      rw[List.ofFn_add]<;>rfl
    have hR:(ZR fun i:Fin (c+1)=>
        (ZR fun v:Fin (r i.val)=>F (Q0 r i.val+v.val)).prod)=
        (ZR fun i:Fin c=>
          (ZR fun v:Fin (r i.val)=>F (Q0 r i.val+v.val)).prod) ++
          [(ZR fun v:Fin (r c)=>F (Q0 r c+v.val)).prod]:=by
      rw[List.ofFn_add]<;>rfl
    show (ZR fun t:Fin (Q0 r c+r c)=>F t.val).prod=_
    rw[hL,hR,List.prod_append,List.prod_append,Qb1 r F c,List.prod_singleton]
def Q7m {D:Type u} [One D] {n:ℕ} (f:Fin n→D) (k:ℕ):D:=
  if h:k<n then f ⟨k,h⟩ else 1
lemma Qd7 {D:Type u} [One D] {n:ℕ} (f:Fin n→D) (t:Fin n):
    Q7m f t.val= f t:=by
 unfold Q7m
 exact dif_pos t.isLt
end ListProd
section LayerQuot
variable {G:Type u} [Group G]
lemma Qb4 (i:ℕ) {N:ℕ} (x:Fin N→G) (hx:∀ v,x v∈lcs G i)
    (h:lcs G i≤ZA (ZG x)⊔lcs G (i+1)):
    ZA (ZG fun v=>
      (QuotientGroup.mk (⟨x v,hx v⟩:lcs G i):Q1r G i))=⊤:=by
  set Y:=ZA (ZG fun v=>
      (QuotientGroup.mk (⟨x v,hx v⟩:lcs G i):Q1r G i)) with hY
  have hK:lcs G i≤(Y.comap (ZF ((lcs G (i+1)).subgroupOf (lcs G i)))).map
      (lcs G i).subtype:=by
   refine h.trans (sup_le ?_ ?_)
   · rw[ZD]
     rintro _ ⟨v,rfl⟩
     exact ⟨⟨x v,hx v⟩,ZC ⟨v,rfl⟩,rfl⟩
   · intro z hz
     have hz':z∈lcs G i:=Qd (Nat.le_succ i) hz
     refine ⟨⟨z,hz'⟩,?_,rfl⟩
     show ZF ((lcs G (i+1)).subgroupOf (lcs G i)) ⟨z,hz'⟩∈Y
     have h1:ZF ((lcs G (i+1)).subgroupOf (lcs G i)) ⟨z,hz'⟩=1:=
       (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hz)
     rw[h1]
     exact Y.one_mem
  rw[eq_top_iff]
  rintro q -
  obtain ⟨z,rfl⟩:=QuotientGroup.mk_surjective q
  obtain ⟨z',hz',hzz⟩:=hK z.2
  have hz2:z'=z:=Subtype.ext hzz
  rw[hz2]at hz'
  exact hz'
lemma Q86 (i:ℕ) {N:ℕ} (x:Fin N→lcs G i)
    (h:ZA (ZG fun v=> (QuotientGroup.mk (x v):Q1r G i))=⊤):
    lcs G i≤ZA (ZG fun v=> (x v:G))⊔lcs G (i+1):=by
  intro z hz
  set M:=ZA (ZG fun v=> (x v:G))⊔lcs G (i+1) with hM
  have hle:ZA (ZG fun v=> (QuotientGroup.mk (x v):Q1r G i))≤
      (M.subgroupOf (lcs G i)).map
        (ZF ((lcs G (i+1)).subgroupOf (lcs G i))):=by
    rw[ZD]
    rintro _ ⟨v,rfl⟩
    exact ⟨x v,Subgroup.mem_subgroupOf.mpr
      (ZJ (ZC ⟨v,rfl⟩)),rfl⟩
  rw[h]at hle
  obtain ⟨z',hz',hzz⟩:=
    hle (ZM (QuotientGroup.mk (⟨z,hz⟩:lcs G i):Q1r G i))
  have hzz':(QuotientGroup.mk z':Q1r G i)=QuotientGroup.mk ⟨z,hz⟩:=hzz
  have h2:z'⁻¹*⟨z,hz⟩∈(lcs G (i+1)).subgroupOf (lcs G i):=QuotientGroup.eq.mp hzz'
  have h2':((z'⁻¹*⟨z,hz⟩:lcs G i):G)∈lcs G (i+1):=Subgroup.mem_subgroupOf.mp h2
  have hz'':(z':G)∈M:=Subgroup.mem_subgroupOf.mp hz'
  have h3:z=(z':G)*((z'⁻¹*⟨z,hz⟩:lcs G i):G):=by simp
  rw[h3]
  exact M.mul_mem hz'' (ZL h2')
lemma Qih [Finite G] {p:ℕ} (hp:p.Prime) (i R:ℕ)
    (hcard:p^R*ZB (Q15 p G i)=ZB (lcs G i))
    (N:ℕ) (y:Fin N→Q1r G i) (hy:ZA (ZG y)=⊤):R≤N:=by
 choose x hx using fun v=>QuotientGroup.mk_surjective (y v)
 have hy':ZA (ZG fun v=> (QuotientGroup.mk (x v):Q1r G i))=⊤:=by
   have e:(fun v=> (QuotientGroup.mk (x v):Q1r G i))=y:= funext hx
   rw[e]
   exact hy
 have h1:=Q86 i x hy'
 have hxN:∀ j,Q7m (fun v=> (x v:G)) j∈lcs G i:=by
   intro j
   unfold Q7m
   split_ifs
   · exact (x _).2
   · exact one_mem _
 have hrange:ZG (fun v=> (x v:G))⊆Q7m (fun v=> (x v:G)) '' ZP N:=by
   rintro _ ⟨v,rfl⟩
   exact ⟨v.val,v.isLt,Qd7 _ v⟩
 have h2:lcs G i≤ZA (Q7m (fun v=> (x v:G)) '' ZP N)⊔Q15 p G i:=
   h1.trans (sup_le_sup (ZO hrange) (Q16 p i))
 have hN:∀ j,(ZA (Q7m (fun v=> (x v:G)) '' ZP j)⊔
     Q15 p G i).Normal:= fun j=>
   Q47 p i _ (by rintro _ ⟨k, -,rfl⟩; exact hxN k)
 have h3:=Q5s hp.pos (Q15 p G i) (Q7m (fun v=> (x v:G))) hN
   (fun j=>Q98 p i _ (hxN j)) N
 have h4:ZB (lcs G i)≤p^N*ZB (Q15 p G i):=
   (Subgroup.card_le_of_le h2).trans h3
 have h5:0<ZB (Q15 p G i):=Nat.card_pos
 rw[← hcard]at h4
 have h6:p^R≤p^N:=Nat.le_of_mul_le_mul_right h4 h5
 by_contra hRN
 have e3:p^(N+1)≤p^R:=Nat.pow_le_pow_right hp.pos (by omega)
 have e1:p^(N+1)=p^N*p:=pow_succ p N
 have e2:p^N*2≤p^N*p:=Nat.mul_le_mul_left _ hp.two_le
 have e4:0<p^N:=pow_pos hp.pos N
 rw[e1]at e3
 linarith
end LayerQuot
section Reindex
variable {G:Type u} [Group G] {p:ℕ} {u:ℕ→G} {d:Q5} {X:Fin d.n→G}
  {r :ℕ→ℕ}
abbrev Q4y (r :ℕ→ℕ) (c:ℕ):Fin c→ℕ:= fun i=>r i.val
lemma Qjl {n:ℕ} (r :ℕ→ℕ) {c:ℕ} (hn:n=Q0 r c) (i:Fin c)
    (v:Fin (r i.val)):Q0 r i.val+v.val<n:=by
 have h1:=Q2i r (show i.val+1≤ c from i.isLt)
 rw[Q19]at h1
 have h2:=v.isLt
 omega
def Qbn {n:ℕ} (r :ℕ→ℕ) {c:ℕ} (hn:n=Q0 r c) (k:Q6 c (Q4y r c)):Fin n:=
  ⟨Q0 r k.1.val+k.2.val,Qjl r hn k.1 k.2⟩
lemma Q2.Qel (hS:Q2 p u d X r) {c:ℕ} (hn:d.n=Q0 r c)
    (k:Q6 c (Q4y r c)):d.lv (Qbn r hn k)=k.1.val:=
  (hS.layer_iff (Qbn r hn k) k.1.val).mpr
    ⟨Nat.le_add_right _ _,Nat.add_lt_add_left k.2.isLt _⟩
lemma Q2.Qff (hS:Q2 p u d X r) {c:ℕ} (hn:d.n=Q0 r c) (t:Fin d.n):
    d.lv t<c:=by
 by_contra h
 have h1:=Q2i r (not_lt.mp h)
 have h2:=((hS.layer_iff t (d.lv t)).mp rfl).1
 have h3:=t.isLt
 omega
lemma Q2.Qm1 (hS:Q2 p u d X r) {c:ℕ} (hn:d.n=Q0 r c):
    Function.Injective (Qbn r hn):=by
 rintro ⟨i,v⟩ ⟨i',v'⟩ h
 have e1:d.lv (Qbn r hn ⟨i,v⟩)=i.val:=hS.Qel hn ⟨i,v⟩
 have e2:d.lv (Qbn r hn ⟨i',v'⟩)=i'.val:=hS.Qel hn ⟨i',v'⟩
 rw[h]at e1
 have h1:i=i':=Fin.ext (e1.symm.trans e2)
 subst h1
 have h3:Q0 r i.val+v.val=Q0 r i.val+v'.val:= congrArg Fin.val h
 have h2:v=v':=Fin.ext (by omega)
 subst h2
 rfl
lemma Q2.Ql9 (hS:Q2 p u d X r) {c:ℕ} (hn:d.n=Q0 r c):
    Function.Surjective (Qbn r hn):=by
 intro t
 obtain ⟨h1,h2⟩:=(hS.layer_iff t (d.lv t)).mp rfl
 refine ⟨⟨⟨d.lv t,hS.Qff hn t⟩,⟨t.val - Q0 r (d.lv t),
   show t.val - Q0 r (d.lv t)< r (d.lv t) by omega⟩⟩,?_⟩
 apply Fin.ext
 show Q0 r (d.lv t)+(t.val - Q0 r (d.lv t))=t.val
 omega
noncomputable def Q2.Q8 (hS:Q2 p u d X r) {c:ℕ} (hn:d.n=Q0 r c):
    Q6 c (Q4y r c)≃Fin d.n:=
  Equiv.ofBijective (Qbn r hn) ⟨hS.Qm1 hn,hS.Ql9 hn⟩
lemma Q2.Q3h (hS:Q2 p u d X r) {c:ℕ} (hn:d.n=Q0 r c)
    (k:Q6 c (Q4y r c)):d.lv (hS.Q8 hn k)=k.1.val:=
  hS.Qel hn k
lemma Q2.Q7o (hS:Q2 p u d X r) {c:ℕ} (hn:d.n=Q0 r c)
    (k:Q6 c (Q4y r c)):(hS.Q8 hn k).val=Q0 r k.1.val+k.2.val:=rfl
lemma Q2.Qhf (hS:Q2 p u d X r) (t:Fin d.n):X t∈lcs G (d.lv t):=
  Q5f d hS.valid.toStruct X hS.realizes.dfeq t
lemma Q2.Qnq (hS:Q2 p u d X r) {c:ℕ} (hn:d.n=Q0 r c)
    (k:Q6 c (Q4y r c)):X (hS.Q8 hn k)∈lcs G k.1:=by
 have h:=hS.Qhf (hS.Q8 hn k)
 rwa[hS.Q3h hn k]at h
lemma Q2.Q9f (hS:Q2 p u d X r) {c:ℕ} (hn:d.n=Q0 r c)
    (e:Q6 c (Q4y r c)→ℕ):
    Q2w (fun k=>X (hS.Q8 hn k)) e=Q2e X (fun t=>e ((hS.Q8 hn).symm t)):=by
  have h1:Q2e X (fun t=>e ((hS.Q8 hn).symm t))=
      (ZR fun t:Fin d.n=>
        Q7m (fun t=>X t^e ((hS.Q8 hn).symm t)) t.val).prod:=by
    unfold Q2e
    rw[Q7q]
    simp only[Qd7]
  have key:∀ (i:Fin c) (v:Fin (r i.val)),
      Q7m (fun t=>X t^e ((hS.Q8 hn).symm t)) (Q0 r i.val+v.val)=
        X (hS.Q8 hn ⟨i,v⟩)^e ⟨i,v⟩:=by
    intro i v
    have h:=Qd7 (fun t=>X t^e ((hS.Q8 hn).symm t)) (hS.Q8 hn ⟨i,v⟩)
    refine h.trans ?_
    show X (hS.Q8 hn ⟨i,v⟩)^e ((hS.Q8 hn).symm (hS.Q8 hn ⟨i,v⟩))=_
    rw[Equiv.symm_apply_apply]
  rw[h1,Qgu hn,Qb1 r _ c]
  unfold Q2w Qu
  simp only[key]
lemma Q2.Qfr (hS:Q2 p u d X r) {c:ℕ} (hn:d.n=Q0 r c)
    (i:Fin c) (j:ℕ):
    ZA (X '' Q2z d i.val (Q0 r i.val+j))≤
      Qay (fun k=>X (hS.Q8 hn k)) i j:=by
  rw[ZD]
  rintro _ ⟨t,ht,rfl⟩
  rcases (Q1b d).mp ht with h | ⟨h1,h2⟩
  · exact ZL
      (Qd (show i.val+1≤d.lv t by omega) (hS.Qhf t))
  · apply ZJ
    apply ZC
    obtain ⟨⟨i',v'⟩,rfl⟩:=(hS.Q8 hn).surjective t
    have hk:d.lv (hS.Q8 hn ⟨i',v'⟩)=i'.val:=hS.Q3h hn _
    have hii:i'=i:=Fin.ext (by omega)
    subst hii
    have h3:Q0 r i'.val+v'.val<Q0 r i'.val+j:=h2
    exact ⟨v',by omega,rfl⟩
lemma Q2.Qm7 (hS:Q2 p u d X r) {c:ℕ} (hn:d.n=Q0 r c)
    (i:Fin c) (j:ℕ):
    Qay (fun k=>X (hS.Q8 hn k)) i j≤
      ZA (X '' Q2z d i.val (Q0 r i.val+j)):=by
  refine sup_le ?_ ?_
  · rw[ZD]
    rintro _ ⟨v,hv,rfl⟩
    apply ZC
    refine ⟨hS.Q8 hn ⟨i,v⟩,?_,rfl⟩
    refine (Q1b d).mpr (Or.inr ⟨(hS.Q3h hn ⟨i,v⟩).symm,?_⟩)
    show Q0 r i.val+v.val<Q0 r i.val+j
    omega
  · refine (hS.deep (i.val+1) (by omega)).trans (ZO ?_)
    rintro _ ⟨t,ht,rfl⟩
    have ht':i.val+1≤d.lv t:=ht
    exact ⟨t,(Q1b d).mpr (Or.inl (by omega)),rfl⟩
noncomputable def Q2.toNF (hS:Q2 p u d X r) {c:ℕ} (hn:d.n=Q0 r c):
    Q5k p (fun k=>d.a (hS.Q8 hn k)) (fun k=>X (hS.Q8 hn k)) where
  coord x h:=⟨Classical.choose (hS.nf_exists x) (hS.Q8 hn h),
    (Classical.choose_spec (hS.nf_exists x)).1 _⟩
  uniq e:=by
    funext h
    apply Fin.ext
    obtain ⟨hb,hx⟩:=Classical.choose_spec
      (hS.nf_exists (Q2w (fun k=>X (hS.Q8 hn k)) fun h=> (e h).val))
    have hb':∀ t,(e ((hS.Q8 hn).symm t)).val<p^d.a t:=by
     intro t
     have h0:=(e ((hS.Q8 hn).symm t)).isLt
     simpa only[Equiv.apply_symm_apply] using h0
    have h2:=hS.nf_unique _ (fun t=> (e ((hS.Q8 hn).symm t)).val) hb hb'
      (hx.symm.trans (hS.Q9f hn _))
    show Classical.choose (hS.nf_exists (Q2w (fun k=>X (hS.Q8 hn k))
      fun h=> (e h).val)) (hS.Q8 hn h)=(e h).val
    rw[h2]
    show (e ((hS.Q8 hn).symm (hS.Q8 hn h))).val=(e h).val
    rw[Equiv.symm_apply_apply]
  sub := by
    intro i j x hx
    obtain ⟨e0,hsupp,hbd,hx0⟩:=
      hS.nf_sub i.val (Q0 r i.val+j) x (hS.Qm7 hn i j hx)
    refine ⟨fun h=> ⟨e0 (hS.Q8 hn h),hbd (hS.Q8 hn h)⟩,?_,?_⟩
    · rintro ⟨i',v'⟩ hh
      show e0 (hS.Q8 hn ⟨i',v'⟩)=0
      by_contra hne
      have hm:=(Q1b d).mp (hsupp _ hne)
      have hk:d.lv (hS.Q8 hn ⟨i',v'⟩)=i'.val:=hS.Q3h hn _
      have hv:(hS.Q8 hn ⟨i',v'⟩).val=Q0 r i'.val+v'.val:=rfl
      rcases hh with h1 | ⟨h1,h2⟩
      · have h1':i'.val< i.val:=h1
        omega
      · have h1':i'=i:=h1
        subst h1'
        have h2':j≤v'.val:=h2
        omega
    · rw[hS.Q9f hn,hx0]
      refine congrArg (Q2e X) (funext fun t=>?_)
      show e0 (hS.Q8 hn ((hS.Q8 hn).symm t))=e0 t
      rw[Equiv.apply_symm_apply]
noncomputable def Q2.toQ7 [Finite G] (hp:p.Prime) (hS:Q2 p u d X r)
    {c:ℕ} (hn:d.n=Q0 r c):
    Q7 p (fun k=>d.a (hS.Q8 hn k)) (fun k=>X (hS.Q8 hn k)) where
  mem:=hS.Qnq hn
  gen :=by
    intro i
    refine Qb4 i.val (fun v=>X (hS.Q8 hn ⟨i,v⟩))
      (fun v=>hS.Qnq hn ⟨i,v⟩) ?_
    refine (hS.layer_gen i.val).trans (sup_le_sup_right (ZO ?_) _)
    rintro _ ⟨t,ht,rfl⟩
    obtain ⟨⟨i',v'⟩,rfl⟩:=(hS.Q8 hn).surjective t
    have hk:d.lv (hS.Q8 hn ⟨i',v'⟩)=i'.val:=hS.Q3h hn _
    have ht':d.lv (hS.Q8 hn ⟨i',v'⟩)=i.val:=ht
    have hii:i'=i:=Fin.ext (by omega)
    subst hii
    exact ⟨v',rfl⟩
  minimum:= fun i N y hy=>Qih hp i.val (r i.val) (hS.layer_card i.val) N y hy
  pos:= fun k=>hS.a_pos _
  rel:=by
    intro i j
    show X (hS.Q8 hn ⟨i,j⟩)^p^d.a (hS.Q8 hn ⟨i,j⟩)∈_
    rw[hS.realizes.pow (hS.Q8 hn ⟨i,j⟩)]
    refine hS.Qfr hn i j.val (Q8o X _ _ fun t ht=>?_)
    have hpr :=hS.valid.b_supp _ t ht
    have hk:d.lv (hS.Q8 hn ⟨i,j⟩)=i.val:=hS.Q3h hn _
    have hv:(hS.Q8 hn ⟨i,j⟩).val=Q0 r i.val+j.val:=rfl
    unfold Q5.prec at hpr
    refine (Q1b d).mpr ?_
    omega
  nf:=hS.toNF hn
end Reindex
section NatLemmas
lemma Qk8 (r :ℕ→ℕ):∀ c,(∀ w<c,1≤ r w)→ c≤Q0 r c
  | 0,_=>Nat.zero_le _
  | c+1,h=>by
    have h1:=Qk8 r c (fun w hw=>h w (by omega))
    have h2:=h c (by omega)
    rw[Q19]
    omega
lemma Q41 {r r':ℕ→ℕ} {c:ℕ} (h:∀ w<c,r w=r' w):
    ∀ w≤ c,Q0 r w=Q0 r' w
  | 0,_=>rfl
  | w+1,hw=>by
    rw[Q19,Q19,Q41 h w (by omega),h w (by omega)]
lemma Q50 (r :ℕ→ℕ):∀ c,∑ i:Fin c,r i.val=Q0 r c
  | 0=>by
    rw[Fin.sum_univ_zero]
    rfl
  | c+1=>by
    rw[Fin.sum_univ_castSucc]
    simp only[Fin.coe_castSucc,Fin.val_last]
    rw[Q50 r c,Q19]
lemma Q9s (r :ℕ→ℕ) (k:ℕ):∀ c,k≤ c→
    ∑ i:Fin c,(if k≤ i.val then r i.val else 0)=Q0 r c - Q0 r k
  | 0,hk=>by
    rw[Fin.sum_univ_zero]
    have hk0:k=0:=by omega
    subst hk0
    rfl
  | c + 1,hk=>by
    rcases Nat.lt_or_ge k (c+1) with hlt | hge
    · rw[Fin.sum_univ_castSucc]
      simp only[Fin.coe_castSucc,Fin.val_last]
      rw[Q9s r k c (by omega),if_pos (show k≤ c by omega),Q19]
      have:=Q2i r (show k≤ c by omega)
      omega
    · have hk':k= c+1:=by omega
      subst hk'
      have hz:∀ i:Fin (c+1),(if c+1≤ i.val then r i.val else 0)=0:=
        fun i=>if_neg (by have:=i.isLt; omega)
      rw[Finset.sum_eq_zero (fun i _=>hz i),Nat.sub_self]
lemma Q3a (f:ℕ→ℕ) (R:ℕ) (hf:∀ i j,i≤j→j<R→ f i≤f j)
    (k j:ℕ) (hj:j<R):
    f j<k↔j< ((ZQ R).filter (fun i=>f i<k)).card:=by
  constructor
  · intro h
    have hsub:ZQ (j+1)⊆(ZQ R).filter (fun i=>f i<k):=by
      intro i hi
      rw[Finset.mem_range]at hi
      rw[Finset.mem_filter,Finset.mem_range]
      exact ⟨by omega,lt_of_le_of_lt (hf i j (by omega) hj) h⟩
    have h1:=Finset.card_le_card hsub
    rw[Finset.card_range]at h1
    omega
  · intro h
    by_contra hk
    have hk':k≤f j:=not_lt.mp hk
    have hsub:(ZQ R).filter (fun i=>f i<k)⊆ZQ j:=by
      intro i hi
      rw[Finset.mem_filter,Finset.mem_range]at hi
      rw[Finset.mem_range]
      by_contra hij
      have h2:=hf j i (by omega) hi.1
      omega
    have h1:=Finset.card_le_card hsub
    rw[Finset.card_range]at h1
    omega
lemma Q6b (f:ℕ→ℕ) (R k:ℕ):
    ((ZQ R).filter (fun i=>f i<k)).card=
      ∑ b∈ZQ k,((ZQ R).filter (fun i=>f i=b)).card:=by
  have hmaps:∀ i∈(ZQ R).filter (fun i=>f i<k),f i∈ZQ k:=by
    intro i hi
    rw[Finset.mem_filter]at hi
    exact Finset.mem_range.mpr hi.2
  rw[Finset.card_eq_sum_card_fiberwise hmaps]
  refine Finset.sum_congr rfl fun b hb=>?_
  rw[Finset.filter_filter]
  congr 1
  apply Finset.filter_congr
  intro i _
  rw[Finset.mem_range]at hb
  constructor
  · rintro ⟨-,h⟩
    exact h
  · intro h
    exact ⟨by omega,h⟩
lemma Q8r (f g:ℕ→ℕ) (R:ℕ) (hf:∀ i j,i≤j→j<R→ f i≤f j)
    (hg:∀ i j,i≤j→j<R→ g i≤g j)
    (hfib:∀ k,((ZQ R).filter (fun i=>f i=k)).card=
      ((ZQ R).filter (fun i=>g i=k)).card)
    (j:ℕ) (hj:j<R):f j=g j:=by
  have hA:∀ k,((ZQ R).filter (fun i=>f i<k)).card=
      ((ZQ R).filter (fun i=>g i<k)).card:=by
    intro k
    rw[Q6b,Q6b]
    exact Finset.sum_congr rfl fun b _=>hfib b
  have h1:=(Q3a f R hf (f j+1) j hj).mp (Nat.lt_succ_self _)
  rw[hA]at h1
  have h1':=(Q3a g R hg (f j+1) j hj).mpr h1
  have h2:=(Q3a g R hg (g j+1) j hj).mp (Nat.lt_succ_self _)
  rw[← hA]at h2
  have h2':=(Q3a f R hf (g j+1) j hj).mpr h2
  omega
end NatLemmas
section DataBridge
instance Qjg (d:Q5) (t k:Fin d.n):Decidable (d.Rec t k):=by
 unfold Q5.Rec
 infer_instance
def Q5.normalize (d:Q5):Q5 where
  n:=d.n
  s:=d.s
  lv:=d.lv
  df:= fun t=>if 1≤d.lv t then d.df t else (t,t)
  a:=d.a
  b:=d.b
  c:= fun t k v=>if d.Rec t k then d.c t k v else 0
lemma Q5.Qeo {d:Q5} (hd:d.Valid) (t k v:Fin d.n)
    (h:(if d.Rec t k then d.c t k v else 0)≠0):d.lv t<d.lv v:=by
  split_ifs at h with hr
  · exact hd.c_supp t k v h
  · exact absurd rfl h
lemma Q5.Qfj {d:Q5} (hd:d.Valid):d.normalize.Valid where
  mono:=hd.mono
  s_le:=hd.s_le
  core:=hd.core
  df_lv:= fun t ht=>by
    have e:d.normalize.df t=d.df t:=if_pos ht
    rw[e]
    exact hd.df_lv t ht
  df_core:= fun t ht=>by
    have e:d.normalize.df t=d.df t:=if_pos ht
    rw[e]
    exact hd.df_core t ht
  df_one:= fun t ht=>by
    have ht':d.lv t=1:=ht
    have e:d.normalize.df t=d.df t:=if_pos (show 1≤d.lv t by omega)
    rw[e]
    exact hd.df_one t ht
  b_supp:=hd.b_supp
  c_supp:= fun t k v h=>Q5.Qeo hd t k v h
lemma Q5.Q7y {G:Type u} [Group G] {p:ℕ} {d:Q5}
    {X:Fin d.n→G} (h:Q2k p d X):Q2k p d.normalize X where
  card:=h.card
  gen:=h.gen
  dfeq:= fun t ht=>by
    have e:d.normalize.df t=d.df t:=if_pos ht
    rw[e]
    exact h.dfeq t ht
  pow:=h.pow
  comm0:= fun t k ht hk htk=>by
    have hrec:d.Rec t k:= Or.inl ⟨ht,hk,htk⟩
    have e2:d.normalize.c t k=d.c t k:= funext fun v=>if_pos hrec
    rw[e2]
    exact h.comm0 t k ht hk htk
  comm1:= fun t k ht hk=>by
    have ht':d.lv t=1:=ht
    have e:d.normalize.df t=d.df t:=if_pos (show 1≤d.lv t by omega)
    rw[e]at hk
    have hrec:d.Rec t k:= Or.inr (Or.inl ⟨ht,hk⟩)
    have e2:d.normalize.c t k=d.c t k:= funext fun v=>if_pos hrec
    rw[e2]
    exact h.comm1 t k ht hk
  comm2:= fun t k ht hk=>by
    have hrec:d.Rec t k:= Or.inr (Or.inr ⟨ht,hk⟩)
    have e2:d.normalize.c t k=d.c t k:= funext fun v=>if_pos hrec
    rw[e2]
    exact h.comm2 t k ht hk
lemma Q5.normalize_eq {d1 d2:Q5} (hn:d1.n=d2.n) (hs:d1.s=d2.s)
    (hlv:∀ i (h1:i<d1.n) (h2:i<d2.n),d1.lv ⟨i,h1⟩=d2.lv ⟨i,h2⟩)
    (hdf :∀ i (h1:i<d1.n) (h2:i<d2.n),1≤d1.lv ⟨i,h1⟩→
      (d1.df ⟨i,h1⟩).1.val=(d2.df ⟨i,h2⟩).1.val∧
        (d1.df ⟨i,h1⟩).2.val=(d2.df ⟨i,h2⟩).2.val)
    (ha:∀ i (h1:i<d1.n) (h2:i<d2.n),d1.a ⟨i,h1⟩=d2.a ⟨i,h2⟩)
    (hb:∀ i j (h1:i<d1.n) (h1':j<d1.n) (h2:i<d2.n) (h2':j<d2.n),
      d1.b ⟨i,h1⟩ ⟨j,h1'⟩=d2.b ⟨i,h2⟩ ⟨j,h2'⟩)
    (hc :∀ i j k (h1:i<d1.n) (h1':j<d1.n) (h1'':k<d1.n) (h2:i<d2.n)
      (h2':j<d2.n) (h2'':k<d2.n),
      (if d1.Rec ⟨i,h1⟩ ⟨j,h1'⟩ then d1.c ⟨i,h1⟩ ⟨j,h1'⟩ ⟨k,h1''⟩ else 0)=
        (if d2.Rec ⟨i,h2⟩ ⟨j,h2'⟩ then d2.c ⟨i,h2⟩ ⟨j,h2'⟩ ⟨k,h2''⟩ else 0)):
    d1.normalize=d2.normalize:=by
  obtain ⟨n1,s1,lv1,df1,a1,b1,c1⟩:=d1
  obtain ⟨n2,s2,lv2,df2,a2,b2,c2⟩:=d2
  have hn':n1=n2:=hn
  subst hn'
  have hs':s1=s2:=hs
  subst hs'
  have elv:lv1=lv2:= funext fun t=>hlv t.val t.isLt t.isLt
  subst elv
  have ea:a1=a2:= funext fun t=>ha t.val t.isLt t.isLt
  subst ea
  have eb:b1=b2:= funext fun t=>funext fun k=>hb t.val k.val t.isLt k.isLt t.isLt k.isLt
  subst eb
  have edf:(fun t=>if 1≤lv1 t then df1 t else (t,t))=
      (fun t=>if 1≤lv1 t then df2 t else (t,t)):=by
    funext t
    by_cases h:1≤lv1 t
    · rw[if_pos h,if_pos h]
      have h':=hdf t.val t.isLt t.isLt h
      exact Prod.ext (Fin.ext h'.1) (Fin.ext h'.2)
    · rw[if_neg h,if_neg h]
  have ec:(fun t k v=>if Q5.Rec ⟨n1,s1,lv1,df1,a1,b1,c1⟩ t k then c1 t k v
      else 0)=(fun t k v=>if Q5.Rec ⟨n1,s1,lv1,df2,a1,b1,c2⟩ t k then c2 t k v
      else 0):=by
    funext t k v
    exact hc t.val k.val v.val t.isLt k.isLt v.isLt t.isLt k.isLt v.isLt
  show Q5.mk n1 s1 lv1 (fun t=>if 1≤lv1 t then df1 t else (t,t)) a1 b1
      (fun t k v=>if Q5.Rec ⟨n1,s1,lv1,df1,a1,b1,c1⟩ t k then c1 t k v else 0)=
    Q5.mk n1 s1 lv1 (fun t=>if 1≤lv1 t then df2 t else (t,t)) a1 b1
      (fun t k v=>if Q5.Rec ⟨n1,s1,lv1,df2,a1,b1,c2⟩ t k then c2 t k v else 0)
  rw[edf,ec]
lemma Qjz {G H:Type u} [Group G] [Group H] [Finite G] [Finite H] {p:ℕ}
    (hp:p.Prime) (D1 D2:Q5) (e:D1=D2) (hv:D1.Valid) (Y1:Fin D1.n→G)
    (Y2:Fin D2.n→H) (k1:Q2k p D1 Y1) (k2:Q2k p D2 Y2):
    Nonempty (G≃*H):=by
 subst e
 exact Qia hp D1 hv Y1 Y2 k1 k2
def Qn (d:Q5) (r :ℕ→ℕ) (j:ℕ):ℕ:=
  if h:Q0 r 1+j<d.n then (d.df ⟨Q0 r 1+j,h⟩).2.val else 0
def Q8b (d:Q5) (r :ℕ→ℕ) (j:ℕ):ℕ:=
  if h:Q0 r 1+j<d.n then (d.df ⟨Q0 r 1+j,h⟩).1.val else 0
def Q7c (d:Q5) (r :ℕ→ℕ) (j:ℕ):ℕ×ℕ:=
  if h:Q0 r 2+j<d.n then ((d.df ⟨Q0 r 2+j,h⟩).1.val,(d.df ⟨Q0 r 2+j,h⟩).2.val)
  else (0,0)
def Q4l (d:Q5) (j:ℕ):ℕ:=if h:j<d.n then d.a ⟨j,h⟩ else 0
def Q8h (d:Q5) (i j:ℕ):ℕ:=
  if h:i<d.n∧j<d.n then d.b ⟨i,h.1⟩ ⟨j,h.2⟩ else 0
def Q2u (d:Q5) (i j k:ℕ):ℕ:=
  if h:i<d.n∧j<d.n∧k<d.n then
    (if d.Rec ⟨i,h.1⟩ ⟨j,h.2.1⟩ then d.c ⟨i,h.1⟩ ⟨j,h.2.1⟩ ⟨k,h.2.2⟩ else 0)
  else 0
def Q5g (d:Q5) (r :ℕ→ℕ) (k:ℕ):ℕ:=
  ((ZQ (r 1)).filter (fun j=>Qn d r j=k+1)).card
lemma Q3z (d:Q5) (r :ℕ→ℕ) (t:Fin d.n) (j:ℕ) (hj:Q0 r 1+j=t.val):
    Qn d r j=(d.df t).2.val:=by
 have h:Q0 r 1+j<d.n:=by have:=t.isLt; omega
 unfold Qn
 rw[dif_pos h]
 have e:(⟨Q0 r 1+j,h⟩:Fin d.n)=t:=Fin.ext hj
 rw[e]
lemma Q7k (d:Q5) (r :ℕ→ℕ) (t:Fin d.n) (j:ℕ) (hj:Q0 r 1+j=t.val):
    Q8b d r j=(d.df t).1.val:=by
 have h:Q0 r 1+j<d.n:=by have:=t.isLt; omega
 unfold Q8b
 rw[dif_pos h]
 have e:(⟨Q0 r 1+j,h⟩:Fin d.n)=t:=Fin.ext hj
 rw[e]
lemma Qkc (d:Q5) (r :ℕ→ℕ) (t:Fin d.n) (j:ℕ) (hj:Q0 r 2+j=t.val):
    Q7c d r j=((d.df t).1.val,(d.df t).2.val):=by
 have h:Q0 r 2+j<d.n:=by have:=t.isLt; omega
 unfold Q7c
 rw[dif_pos h]
 have e:(⟨Q0 r 2+j,h⟩:Fin d.n)=t:=Fin.ext hj
 rw[e]
lemma Qa1 {d:Q5} {m:ℕ} (hsum:∑ t,d.a t=m) (t:Fin d.n):d.a t≤ m:=by
 rw[← hsum]
 exact Finset.single_le_sum (f:=d.a) (fun t _=>Nat.zero_le _) (Finset.mem_univ t)
lemma Qnn {d:Q5} {m:ℕ} (hsum:∑ t,d.a t=m) (j:ℕ):Q4l d j≤ m:=by
 unfold Q4l
 split_ifs with h
 · exact Qa1 hsum _
 · exact Nat.zero_le _
lemma Qnm {d:Q5} {p m:ℕ} (hp:0<p) (hb:d.Bounded p) (hsum:∑ t,d.a t=m)
    (i j:ℕ):Q8h d i j<p^m:=by
 unfold Q8h
 split_ifs with h
 · exact lt_of_lt_of_le (hb.1 _ _) (Nat.pow_le_pow_right hp (Qa1 hsum _))
 · exact pow_pos hp m
lemma Qni {d:Q5} {p m:ℕ} (hp:0<p) (hb:d.Bounded p) (hsum:∑ t,d.a t=m)
    (i j k:ℕ):Q2u d i j k<p^m:=by
 unfold Q2u
 split_ifs
 · exact lt_of_lt_of_le (hb.2 _ _ _) (Nat.pow_le_pow_right hp (Qa1 hsum _))
 · exact pow_pos hp m
 · exact pow_pos hp m
lemma Qkg (d:Q5) (r :ℕ→ℕ) {m:ℕ} (hnm:d.n≤ m) (hm:0< m) (j:ℕ):
    (Q7c d r j).1< m∧(Q7c d r j).2< m:=by
 unfold Q7c
 split_ifs with h
 · exact ⟨lt_of_lt_of_le (d.df ⟨Q0 r 2+j,h⟩).1.isLt hnm,
     lt_of_lt_of_le (d.df ⟨Q0 r 2+j,h⟩).2.isLt hnm⟩
 · exact ⟨hm,hm⟩
abbrev Qy (p m:ℕ):Type:=
  Σ D:Qg m,(Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m))×
    (Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m))
def Qn3 {p m:ℕ} (D:Qy p m):ℕ:=D.1.1.val
def Qnj {p m:ℕ} (D:Qy p m):ℕ:=D.1.2.1.val
def Qn1 {p m:ℕ} (D:Qy p m) (i:ℕ):ℕ:=
  if h:i<D.1.1.val then (D.1.2.2.1.1 ⟨i,h⟩).val else 0
def Qkm {p m:ℕ} (D:Qy p m) (k:ℕ):ℕ:=
  if h:k<D.1.2.1.val - 1 then (D.1.2.2.2.1.1 ⟨k,h⟩).val else 0
def Qnp {p m:ℕ} (D:Qy p m) (j:ℕ):ℕ:=
  if h:j<D.1.2.2.1.r2 then (D.1.2.2.2.2.1.1 ⟨j,h⟩).val else 0
def Qno {p m:ℕ} (D:Qy p m) (j:ℕ):ℕ×ℕ:=
  if h:j<D.1.2.2.1.r3 then
    ((D.1.2.2.2.2.1.2 ⟨j,h⟩).1.val,(D.1.2.2.2.2.1.2 ⟨j,h⟩).2.val)
  else (0,0)
def Qll {p m:ℕ} (D:Qy p m) (j:ℕ):ℕ:=
  if h:j<D.1.2.2.1.tot then (D.1.2.2.2.2.2.1 ⟨j,h⟩).val else 0
def Qmf {p m:ℕ} (D:Qy p m) (i j:ℕ):ℕ:=
  if h:i<D.1.2.2.1.tot∧j<D.1.2.2.1.tot then (D.2.1 ⟨i,h.1⟩ ⟨j,h.2⟩).val else 0
def Ql1 {p m:ℕ} (D:Qy p m) (i j k:ℕ):ℕ:=
  if h:i<D.1.2.2.1.tot∧j<D.1.2.2.1.tot∧k<D.1.2.2.1.tot then
    (D.2.2 ⟨i,h.1⟩ ⟨j,h.2.1⟩ ⟨k,h.2.2⟩).val
  else 0
variable {G:Type u} [Group G] {p:ℕ} {u:ℕ→G} {d:Q5} {X:Fin d.n→G}
  {r :ℕ→ℕ}
lemma Q2.Ql4 (hS:Q2 p u d X r):∃ c,Q0 r c=d.n:=by
 obtain ⟨c,hc⟩:=hS.n_eq
 exact ⟨c,hc.symm⟩
noncomputable def Q2.nL (hS:Q2 p u d X r):ℕ:=Nat.find hS.Ql4
lemma Q2.Q2j (hS:Q2 p u d X r):Q0 r hS.nL=d.n:=Nat.find_spec hS.Ql4
lemma Q2.Qnl (hS:Q2 p u d X r) {w:ℕ} (hw:w<hS.nL):Q0 r w≠d.n:=
  Nat.find_min hS.Ql4 hw
lemma Q2.Qjb [Finite G] (hp:p.Prime) (hS:Q2 p u d X r):
    ∀ w<hS.nL,0< r w:=by
 intro w hw
 by_contra h0
 have hr0:r w=0:=by omega
 have hlt:Q0 r w<d.n:=by
  have h1:=Q2i r hw.le
  have h2:=hS.Qnl hw
  rw[hS.Q2j]at h1
  omega
 have h4:(⟨Q0 r w,hlt⟩:Fin d.n).val=Q0 r w:=rfl
 have hw0:w<d.lv ⟨Q0 r w,hlt⟩:=by
  obtain ⟨h1,h2⟩:=(hS.layer_iff ⟨Q0 r w,hlt⟩ (d.lv ⟨Q0 r w,hlt⟩)).mp rfl
  by_contra hle
  have hle':d.lv ⟨Q0 r w,hlt⟩≤w:=not_lt.mp hle
  rcases lt_or_eq_of_le hle' with hl | he
  · have h3:=Q2i r (show d.lv ⟨Q0 r w,hlt⟩+1≤w by omega)
    rw[Q19]at h3
    omega
  · rw[he,hr0]at h2
    omega
 have hsub:lcs G w≤lcs G (w+1):=by
  refine (hS.layer_gen w).trans (sup_le ?_ le_rfl)
  rw[ZD]
  rintro _ ⟨t,ht,rfl⟩
  exfalso
  have:=(hS.layer_iff t w).mp ht
  omega
 have hstab:∀ k,lcs G (w+k)=lcs G w:=by
  intro k
  induction k with
  | zero=>rfl
  | succ k ih=>
    rw[show w+(k+1)=(w+k)+1 from rfl,lcs_succ,ih, ← lcs_succ]
    exact le_antisymm (Qd (Nat.le_succ w)) hsub
 have:Fact p.Prime:=⟨hp⟩
 have hpg:IsPGroup p G:=IsPGroup.of_card hS.realizes.card
 have:Group.IsNilpotent G:=hpg.isNilpotent
 obtain ⟨N,hN⟩:∃ N,lcs G N=⊥:=
   Subgroup.nilpotent_iff_lowerCentralSeries.mp inferInstance
 have hbot:lcs G w=⊥:=by
  rw[← hstab N]
  exact le_bot_iff.mp ((Qd (Nat.le_add_left N w)).trans (le_of_eq hN))
 have hX:X ⟨Q0 r w,hlt⟩=1:=by
  have h:=Qd hw0.le (hS.Qhf ⟨Q0 r w,hlt⟩)
  rw[hbot]at h
  exact Subgroup.mem_bot.mp h
 apply hS.layer_indep ⟨Q0 r w,hlt⟩
 rw[hX]
 exact one_mem _
lemma Q2.r_le_n (hS:Q2 p u d X r) (w:ℕ) (hw:w<hS.nL):r w≤d.n:=by
 have h1:=Q2i r (show w+1≤hS.nL from hw)
 rw[Q19,hS.Q2j]at h1
 omega
lemma Q2.Qn6 [Finite G] (hp:p.Prime) (hS:Q2 p u d X r):hS.nL≤d.n:=by
 have h:=Qk8 r hS.nL (fun w hw=>hS.Qjb hp w hw)
 rw[hS.Q2j]at h
 exact h
lemma Q2.Q83 (hS:Q2 p u d X r) (hs2:2≤d.s):1<hS.nL:=by
 obtain ⟨t,ht, -⟩:=hS.block_ne 1 le_rfl (by omega)
 have:=hS.Qff hS.Q2j.symm t
 omega
lemma Q2.Qe2 (hS:Q2 p u d X r) (hs2:2≤d.s):Q0 r 2≤d.n:=by
 have h:=Q2i r (show 2≤hS.nL from hS.Q83 hs2)
 rw[hS.Q2j]at h
 exact h
lemma Q2.Q6g (hS:Q2 p u d X r) (hs2:2≤d.s) (j:ℕ) (hj:j< r 1):
    ∃ h:Q0 r 1+j<d.n,d.lv ⟨Q0 r 1+j,h⟩=1:=by
 have h2:=hS.Qe2 hs2
 have e:Q0 r 2=Q0 r 1+r 1:=Q19 r 1
 exact ⟨by omega,(hS.layer_iff _ 1).mpr ⟨Nat.le_add_right _ _,Nat.add_lt_add_left hj _⟩⟩
lemma Q2.Q3n (hS:Q2 p u d X r) (hs2:2≤d.s) (j:ℕ) (hj:j< r 1):
    1≤Qn d r j∧Qn d r j<d.s:=by
 obtain ⟨h,hl⟩:=hS.Q6g hs2 j hj
 rw[Q3z d r ⟨Q0 r 1+j,h⟩ j rfl]
 have h1:(d.df ⟨Q0 r 1+j,h⟩).1.val< (d.df ⟨Q0 r 1+j,h⟩).2.val:=
   hS.valid.df_one _ hl
 exact ⟨by omega,hS.valid.df_core _ (by omega)⟩
lemma Q2.Qat (hS:Q2 p u d X r) (hs2:2≤d.s) (j:ℕ) (hj:j< r 1):
    Q8b d r j<d.s - 1:=by
 obtain ⟨h,hl⟩:=hS.Q6g hs2 j hj
 rw[Q7k d r ⟨Q0 r 1+j,h⟩ j rfl]
 have h1:(d.df ⟨Q0 r 1+j,h⟩).1.val< (d.df ⟨Q0 r 1+j,h⟩).2.val:=
   hS.valid.df_one _ hl
 have h2:=hS.valid.df_core ⟨Q0 r 1+j,h⟩ (by omega)
 omega
lemma Q2.Q9q (hS:Q2 p u d X r) (hs2:2≤d.s) (i j:ℕ) (hij:i≤j)
    (hj:j< r 1):Qn d r i≤Qn d r j:=by
 obtain ⟨h1,hl1⟩:=hS.Q6g hs2 i (by omega)
 obtain ⟨h2,hl2⟩:=hS.Q6g hs2 j hj
 rw[Q3z d r ⟨Q0 r 1+i,h1⟩ i rfl,Q3z d r ⟨Q0 r 1+j,h2⟩ j rfl]
 exact hS.block_mono _ _ hl1 hl2 (show Q0 r 1+i≤Q0 r 1+j by omega)
lemma Q2.Qly (hS:Q2 p u d X r) (k:ℕ) (hk:k<d.s - 1):
    0<Q5g d r k:=by
 obtain ⟨t,ht,hco⟩:=hS.block_ne (k+1) (by omega) (by omega)
 obtain ⟨a1,a2⟩:=(hS.layer_iff t 1).mp ht
 apply Finset.card_pos.mpr
 refine ⟨t.val - Q0 r 1,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),?_⟩⟩
 rw[Q3z d r t (t.val - Q0 r 1) (by omega)]
 exact hco
lemma Qmk (d:Q5) (r :ℕ→ℕ) (k:ℕ):Q5g d r k≤ r 1:=
  (Finset.card_filter_le _ _).trans (Finset.card_range _).le
lemma Q2.Qlx (hS:Q2 p u d X r) (hs2:2≤d.s):
    ∑ k∈ZQ (d.s - 1),Q5g d r k=r 1:=by
 have hmaps:∀ j∈ZQ (r 1),Qn d r j - 1∈ZQ (d.s - 1):=by
  intro j hj
  rw[Finset.mem_range]at hj⊢
  have:=hS.Q3n hs2 j hj
  omega
 have h:=Finset.card_eq_sum_card_fiberwise hmaps
 rw[Finset.card_range]at h
 rw[h]
 refine Finset.sum_congr rfl fun k _=>?_
 unfold Q5g
 congr 1
 apply Finset.filter_congr
 intro j hj
 have:=hS.Q3n hs2 j (Finset.mem_range.mp hj)
 constructor
 · intro e
   omega
 · intro e
   omega
noncomputable def Q2.Q22 [Finite G] (hp:p.Prime) (hS:Q2 p u d X r) {m:ℕ}
    (hnm:d.n≤ m):Q1w m hS.nL:=
  ⟨fun i=> ⟨r i.val,by have:=hS.r_le_n i.val i.isLt; omega⟩,
    fun i=>hS.Qjb hp i.val i.isLt,by
      show ∑ i:Fin hS.nL,r i.val≤ m
      rw[Q50,hS.Q2j]
      exact hnm⟩
lemma Q2.Q4t [Finite G] (hp:p.Prime) (hS:Q2 p u d X r) {m:ℕ}
    (hnm:d.n≤ m):(hS.Q22 hp hnm).tot=d.n:=by
 unfold Q1w.tot
 show ∑ i:Fin hS.nL,r i.val=d.n
 rw[Q50,hS.Q2j]
lemma Q2.Q5h [Finite G] (hp:p.Prime) (hS:Q2 p u d X r) {m:ℕ}
    (hnm:d.n≤ m) (hs2:2≤d.s):(hS.Q22 hp hnm).r2=r 1:=by
 unfold Q1w.r2
 show ∑ i∈Finset.univ.filter (fun i:Fin hS.nL=>i.val=1),r i.val=r 1
 have hmem:(⟨1,hS.Q83 hs2⟩:Fin hS.nL)∈
     Finset.univ.filter (fun i:Fin hS.nL=>i.val=1):=
   Finset.mem_filter.mpr ⟨Finset.mem_univ _,rfl⟩
 exact Finset.sum_eq_single_of_mem _ hmem
   (fun b hb hne=>absurd (Fin.ext (Finset.mem_filter.mp hb).2) hne)
lemma Q2.Qld [Finite G] (hp:p.Prime) (hS:Q2 p u d X r) {m:ℕ}
    (hnm:d.n≤ m) (hs2:2≤d.s):(hS.Q22 hp hnm).r3=d.n - Q0 r 2:=by
 unfold Q1w.r3
 show ∑ i∈Finset.univ.filter (fun i:Fin hS.nL=>2≤ i.val),r i.val=d.n - Q0 r 2
 rw[Finset.sum_filter,Q9s r 2 hS.nL (hS.Q83 hs2),hS.Q2j]
noncomputable def Q2.Qn8 [Finite G] (hp:p.Prime) (hS:Q2 p u d X r) {m:ℕ}
    (hnm:d.n≤ m) (hs2:2≤d.s):Q5a (d.s - 1) (hS.Q22 hp hnm).r2:=
  ⟨fun k=> ⟨Q5g d r k.val,by
      rw[hS.Q5h hp hnm hs2]
      exact Nat.lt_succ_of_le (Qmk d r k.val)⟩,
    fun k=>hS.Qly k.val k.isLt,by
      show ∑ k:Fin (d.s - 1),Q5g d r k.val=_
      rw[hS.Q5h hp hnm hs2,Fin.sum_univ_eq_sum_range (fun k=>Q5g d r k) (d.s - 1)]
      exact hS.Qlx hs2⟩
noncomputable def Q2.Qo0 [Finite G] (hp:p.Prime) (hS:Q2 p u d X r) {m:ℕ}
    (hnm:d.n≤ m) (hs2:2≤d.s):Fin (hS.Q22 hp hnm).r2→Fin (d.s - 1):=
  fun j=> ⟨Q8b d r j.val,hS.Qat hs2 j.val
    (lt_of_lt_of_eq j.isLt (hS.Q5h hp hnm hs2))⟩
noncomputable def Q2.Qnz [Finite G] (hp:p.Prime) (hS:Q2 p u d X r) {m:ℕ}
    (hnm:d.n≤ m) (hs2:2≤d.s):Fin (hS.Q22 hp hnm).r3→Fin m×Fin m:=
  fun j=> (⟨(Q7c d r j.val).1,(Qkg d r hnm (by have:=hS.valid.s_le; omega) j.val).1⟩,
    ⟨(Q7c d r j.val).2,(Qkg d r hnm (by have:=hS.valid.s_le; omega) j.val).2⟩)
noncomputable def Q2.Qo1 [Finite G] (hp:p.Prime) (hS:Q2 p u d X r) {m:ℕ}
    (hnm:d.n≤ m) (hsum:∑ t,d.a t=m):Q5a (hS.Q22 hp hnm).tot m:=
  ⟨fun j => ⟨Q4l d j.val,Nat.lt_succ_of_le (Qnn hsum j.val)⟩,fun j=>by
      have hj:j.val<d.n:=lt_of_lt_of_eq j.isLt (hS.Q4t hp hnm)
      show 0<Q4l d j.val
      unfold Q4l
      rw[dif_pos hj]
      exact hS.a_pos _,by
      show ∑ j:Fin (hS.Q22 hp hnm).tot,Q4l d j.val=m
      rw [Fin.sum_univ_eq_sum_range (fun j=>Q4l d j),hS.Q4t hp hnm,
        ← Fin.sum_univ_eq_sum_range (fun j=>Q4l d j)]
      have e:∀ t:Fin d.n,Q4l d t.val=d.a t:= fun t=>by
        unfold Q4l
        exact dif_pos t.isLt
      simp only[e]
      exact hsum⟩
noncomputable def Q2.enc [Finite G] (hp:p.Prime) (hS:Q2 p u d X r) (m:ℕ) (hnm:d.n≤ m)
    (hs2:2≤d.s) (hsum:∑ t,d.a t=m):Qy p m:=
  ⟨⟨⟨hS.nL,by have:=hS.Qn6 hp; omega⟩,⟨d.s,by have:=hS.valid.s_le; omega⟩,
      hS.Q22 hp hnm,hS.Qn8 hp hnm hs2,(hS.Qo0 hp hnm hs2,hS.Qnz hp hnm hs2),
      hS.Qo1 hp hnm hsum⟩,
    (fun i j=> ⟨Q8h d i.val j.val,Qnm hp.pos hS.bounded hsum _ _⟩,
      fun i j k=> ⟨Q2u d i.val j.val k.val,Qni hp.pos hS.bounded hsum _ _ _⟩)⟩
section Readback
variable [Finite G] (hp:p.Prime) (hS:Q2 p u d X r) {m:ℕ} (hnm:d.n≤ m)
  (hs2:2≤d.s) (hsum:∑ t,d.a t=m)
lemma Q2.Qhb:Qn3 (hS.enc hp m hnm hs2 hsum)=hS.nL:=rfl
lemma Q2.Qgw:Qnj (hS.enc hp m hnm hs2 hsum)=d.s:=rfl
lemma Q2.Qdd (i:ℕ):
    Qn1 (hS.enc hp m hnm hs2 hsum) i=dite (i<hS.nL) (fun _=>r i) (fun _=> 0):=rfl
lemma Q2.Qd6 (k:ℕ):
    Qkm (hS.enc hp m hnm hs2 hsum) k=
      dite (k<d.s - 1) (fun _=>Q5g d r k) (fun _=> 0):=rfl
lemma Q2.Qgq (j:ℕ):
    Qnp (hS.enc hp m hnm hs2 hsum) j=
      dite (j< (hS.Q22 hp hnm).r2) (fun _=>Q8b d r j) (fun _=> 0):=rfl
lemma Q2.Qke (j:ℕ):Qno (hS.enc hp m hnm hs2 hsum) j=Q7c d r j:=by
 have e:Qno (hS.enc hp m hnm hs2 hsum) j=dite (j< (hS.Q22 hp hnm).r3)
     (fun _=> ((Q7c d r j).1,(Q7c d r j).2)) (fun _=> (0,0)):=rfl
 rw[e,hS.Qld hp hnm hs2]
 have h2:=hS.Qe2 hs2
 split_ifs with h
 · rfl
 · have h':¬ (Q0 r 2+j<d.n):=by omega
   unfold Q7c
   rw[dif_neg h']
lemma Q2.Qde (j:ℕ):Qll (hS.enc hp m hnm hs2 hsum) j=Q4l d j:=by
 have e:Qll (hS.enc hp m hnm hs2 hsum) j=
     dite (j< (hS.Q22 hp hnm).tot) (fun _=>Q4l d j) (fun _=> 0):=rfl
 rw[e,hS.Q4t hp hnm]
 split_ifs with h
 · rfl
 · unfold Q4l
   rw[dif_neg h]
lemma Q2.Qdb (i j:ℕ):Qmf (hS.enc hp m hnm hs2 hsum) i j=Q8h d i j:=by
 have e :Qmf (hS.enc hp m hnm hs2 hsum) i j=
     dite (i< (hS.Q22 hp hnm).tot∧j< (hS.Q22 hp hnm).tot)
       (fun _=>Q8h d i j) (fun _=> 0):=rfl
 rw[e,hS.Q4t hp hnm]
 split_ifs with h
 · rfl
 · unfold Q8h
   rw[dif_neg h]
lemma Q2.Qeq (i j k:ℕ):
    Ql1 (hS.enc hp m hnm hs2 hsum) i j k=Q2u d i j k:=by
 have e :Ql1 (hS.enc hp m hnm hs2 hsum) i j k=
     dite (i< (hS.Q22 hp hnm).tot∧j< (hS.Q22 hp hnm).tot∧
       k< (hS.Q22 hp hnm).tot) (fun _=>Q2u d i j k) (fun _=> 0):=rfl
 rw[e,hS.Q4t hp hnm]
 split_ifs with h
 · rfl
 · unfold Q2u
   rw[dif_neg h]
end Readback
lemma Q2.Qc5 {G₁ G₂:Type u} [Group G₁] [Group G₂] [Finite G₁]
    [Finite G₂] {p m:ℕ} (hp:p.Prime) {u₁:ℕ→G₁} {d₁:Q5} {X₁:Fin d₁.n→G₁}
    {r₁:ℕ→ℕ} {u₂:ℕ→G₂} {d₂:Q5} {X₂:Fin d₂.n→G₂} {r₂:ℕ→ℕ}
    (hS₁:Q2 p u₁ d₁ X₁ r₁) (hS₂:Q2 p u₂ d₂ X₂ r₂)
    (hnm₁:d₁.n≤ m) (hs₁:2≤d₁.s) (hsum₁:∑ t,d₁.a t=m)
    (hnm₂:d₂.n≤ m) (hs₂:2≤d₂.s) (hsum₂:∑ t,d₂.a t=m)
    (heq:hS₁.enc hp m hnm₁ hs₁ hsum₁=hS₂.enc hp m hnm₂ hs₂ hsum₂):
    d₁.normalize=d₂.normalize:=by
 have hc:hS₁.nL=hS₂.nL:=by
  have h:= congrArg Qn3 heq
  rwa[hS₁.Qhb hp hnm₁ hs₁ hsum₁,hS₂.Qhb hp hnm₂ hs₂ hsum₂]at h
 have hs:d₁.s=d₂.s:=by
  have h:= congrArg Qnj heq
  rwa[hS₁.Qgw hp hnm₁ hs₁ hsum₁,hS₂.Qgw hp hnm₂ hs₂ hsum₂]at h
 have hr :∀ i<hS₁.nL,r₁ i=r₂ i:=by
  intro i hi
  have hi2:i<hS₂.nL:=by rw[← hc]; exact hi
  have h:= congrFun (congrArg Qn1 heq) i
  rw [hS₁.Qdd hp hnm₁ hs₁ hsum₁,hS₂.Qdd hp hnm₂ hs₂ hsum₂,dif_pos hi,
    dif_pos hi2]at h
  exact h
 have hfo:∀ w≤hS₁.nL,Q0 r₁ w=Q0 r₂ w:=Q41 hr
 have hn:d₁.n=d₂.n:=by
  rw[← hS₁.Q2j, ← hS₂.Q2j, ← hc]
  exact hfo _ le_rfl
 have h1c:1<hS₁.nL:=hS₁.Q83 hs₁
 have hr1:r₁ 1=r₂ 1:=hr 1 h1c
 have hf1:Q0 r₁ 1=Q0 r₂ 1:=hfo 1 h1c.le
 have hf2:Q0 r₁ 2=Q0 r₂ 2:=hfo 2 h1c
 have hlv:∀ i (h1:i<d₁.n) (h2:i<d₂.n),d₁.lv ⟨i,h1⟩=d₂.lv ⟨i,h2⟩:=by
  intro i h1 h2
  have hw:=hS₁.Qff hS₁.Q2j.symm ⟨i,h1⟩
  obtain ⟨e1,e2⟩:=(hS₁.layer_iff ⟨i,h1⟩ (d₁.lv ⟨i,h1⟩)).mp rfl
  rw[hfo _ hw.le,hr _ hw]at e2
  rw[hfo _ hw.le]at e1
  exact ((hS₂.layer_iff ⟨i,h2⟩ (d₁.lv ⟨i,h1⟩)).mpr ⟨e1,e2⟩).symm
 have hA:Q4l d₁=Q4l d₂:=by
  funext j
  have h:= congrFun (congrArg Qll heq) j
  rwa[hS₁.Qde hp hnm₁ hs₁ hsum₁,hS₂.Qde hp hnm₂ hs₂ hsum₂]at h
 have hB:Q8h d₁=Q8h d₂:=by
  funext i j
  have h:= congrFun (congrFun (congrArg Qmf heq) i) j
  rwa[hS₁.Qdb hp hnm₁ hs₁ hsum₁,hS₂.Qdb hp hnm₂ hs₂ hsum₂]at h
 have hCm:Q2u d₁=Q2u d₂:=by
  funext i j k
  have h:= congrFun (congrFun (congrFun (congrArg Ql1 heq) i) j) k
  rwa[hS₁.Qeq hp hnm₁ hs₁ hsum₁,hS₂.Qeq hp hnm₂ hs₂ hsum₂]at h
 have hP:Q7c d₁ r₁=Q7c d₂ r₂:=by
  funext j
  have h:= congrFun (congrArg Qno heq) j
  rwa[hS₁.Qke hp hnm₁ hs₁ hsum₁,hS₂.Qke hp hnm₂ hs₂ hsum₂]at h
 have hPa:∀ j< r₁ 1,Q8b d₁ r₁ j=Q8b d₂ r₂ j:=by
  intro j hj
  have hj1:j< (hS₁.Q22 hp hnm₁).r2:=by rw[hS₁.Q5h hp hnm₁ hs₁]; exact hj
  have hj2:j< (hS₂.Q22 hp hnm₂).r2:=by rw[hS₂.Q5h hp hnm₂ hs₂, ← hr1]; exact hj
  have h:= congrFun (congrArg Qnp heq) j
  rw [hS₁.Qgq hp hnm₁ hs₁ hsum₁,hS₂.Qgq hp hnm₂ hs₂ hsum₂,dif_pos hj1,
    dif_pos hj2]at h
  exact h
 have hfib:∀ k,((ZQ (r₁ 1)).filter (fun j=>Qn d₁ r₁ j=k)).card=
     ((ZQ (r₁ 1)).filter (fun j=>Qn d₂ r₂ j=k)).card:=by
   intro k
   by_cases hk:1≤k∧k<d₁.s
   · have hk1:k - 1<d₁.s - 1:=by omega
     have hk2:k - 1<d₂.s - 1:=by omega
     have h:= congrFun (congrArg Qkm heq) (k - 1)
     rw [hS₁.Qd6 hp hnm₁ hs₁ hsum₁,hS₂.Qd6 hp hnm₂ hs₂ hsum₂,dif_pos hk1,
       dif_pos hk2]at h
     unfold Q5g at h
     rw[← hr1,show k - 1+1=k by omega]at h
     exact h
   · have e1:(ZQ (r₁ 1)).filter (fun j=>Qn d₁ r₁ j=k)= ∅ :=
       Finset.filter_eq_empty_iff.mpr fun j hj=>by
         have:=hS₁.Q3n hs₁ j (Finset.mem_range.mp hj)
         omega
     have e2:(ZQ (r₁ 1)).filter (fun j=>Qn d₂ r₂ j=k)= ∅ :=
       Finset.filter_eq_empty_iff.mpr fun j hj=>by
         have hj':j< r₂ 1:=by rw[← hr1]; exact Finset.mem_range.mp hj
         have:=hS₂.Q3n hs₂ j hj'
         omega
     rw[e1,e2]
 have hmono₂:∀ i j,i≤j→j< r₁ 1→Qn d₂ r₂ i≤Qn d₂ r₂ j:=
   fun i j hij hj=>hS₂.Q9q hs₂ i j hij (by rw[← hr1]; exact hj)
 have hco:∀ j< r₁ 1,Qn d₁ r₁ j=Qn d₂ r₂ j:= fun j hj=>
   Q8r _ _ _ (fun i j hij hj=>hS₁.Q9q hs₁ i j hij hj) hmono₂ hfib j hj
 have hdf:∀ i (h1:i<d₁.n) (h2:i<d₂.n),1≤d₁.lv ⟨i,h1⟩→
     (d₁.df ⟨i,h1⟩).1.val=(d₂.df ⟨i,h2⟩).1.val∧
       (d₁.df ⟨i,h1⟩).2.val=(d₂.df ⟨i,h2⟩).2.val:=by
  intro i h1 h2 hl
  by_cases hw:d₁.lv ⟨i,h1⟩=1
  · obtain ⟨a1,a2⟩:=(hS₁.layer_iff ⟨i,h1⟩ 1).mp hw
    have a1':Q0 r₁ 1≤ i:=a1
    have a2':i<Q0 r₁ 1+r₁ 1:=a2
    have ej1:Q0 r₁ 1+(i - Q0 r₁ 1)=(⟨i,h1⟩:Fin d₁.n).val:=by
     show Q0 r₁ 1+(i - Q0 r₁ 1)=i
     omega
    have ej2:Q0 r₂ 1+(i - Q0 r₁ 1)=(⟨i,h2⟩:Fin d₂.n).val:=by
     show Q0 r₂ 1+(i - Q0 r₁ 1)=i
     omega
    have hj:i - Q0 r₁ 1< r₁ 1:=by omega
    constructor
    · rw[← Q7k d₁ r₁ ⟨i,h1⟩ _ ej1, ← Q7k d₂ r₂ ⟨i,h2⟩ _ ej2]
      exact hPa _ hj
    · rw[← Q3z d₁ r₁ ⟨i,h1⟩ _ ej1, ← Q3z d₂ r₂ ⟨i,h2⟩ _ ej2]
      exact hco _ hj
  · have hge:2≤d₁.lv ⟨i,h1⟩:=by omega
    have a1:=((hS₁.layer_iff ⟨i,h1⟩ (d₁.lv ⟨i,h1⟩)).mp rfl).1
    have a1':Q0 r₁ (d₁.lv ⟨i,h1⟩)≤ i:=a1
    have a3:=Q2i r₁ hge
    have ej1:Q0 r₁ 2+(i - Q0 r₁ 2)=(⟨i,h1⟩:Fin d₁.n).val:=by
     show Q0 r₁ 2+(i - Q0 r₁ 2)=i
     omega
    have ej2:Q0 r₂ 2+(i - Q0 r₁ 2)=(⟨i,h2⟩:Fin d₂.n).val:=by
     show Q0 r₂ 2+(i - Q0 r₁ 2)=i
     omega
    have e:= congrFun hP (i - Q0 r₁ 2)
    rw[Qkc d₁ r₁ ⟨i,h1⟩ _ ej1,Qkc d₂ r₂ ⟨i,h2⟩ _ ej2]at e
    exact Prod.mk.inj e
 refine Q5.normalize_eq hn hs hlv hdf ?_ ?_ ?_
 · intro i h1 h2
   have e:= congrFun hA i
   unfold Q4l at e
   rwa[dif_pos h1,dif_pos h2]at e
 · intro i j h1 h1' h2 h2'
   have e:= congrFun (congrFun hB i) j
   unfold Q8h at e
   rwa[dif_pos (And.intro h1 h1'),dif_pos (And.intro h2 h2')]at e
 · intro i j k h1 h1' h1'' h2 h2' h2''
   have e:= congrFun (congrFun (congrFun hCm i) j) k
   unfold Q2u at e
   rwa[dif_pos (And.intro h1 (And.intro h1' h1'')),
     dif_pos (And.intro h2 (And.intro h2' h2''))]at e
def Q1t {p:ℕ} (hp:p.Prime) (m:ℕ) (G:Type u) [Group G] [Finite G]
    (D:Qy p m):Prop:=
  ∃ (u:ℕ→G) (d:Q5) (X:Fin d.n→G) (r :ℕ→ℕ) (hS:Q2 p u d X r)
    (hnm:d.n≤ m) (hs2:2≤d.s) (hsum:∑ t,d.a t=m),hS.enc hp m hnm hs2 hsum=D
lemma Qg2 {G:Type u} [Group G] [Finite G] {p m:ℕ} (hp:p.Prime)
    (hG:ZB G=p^m) (hna:lcs G 1≠⊥):∃ D:Qy p m,Q1t hp m G D:=by
 obtain ⟨u,d,X,r,hs2,hds, -, -, -, -,hnm, -,hS⟩:=Q6y hp hG hna
 have hsum:∑ t,d.a t=m:=by
  have h1:=hS.realizes.card
  rw[hG]at h1
  exact (Nat.pow_right_injective hp.two_le h1).symm
 have hs2':2≤d.s:=by rw[hds]; exact hs2
 exact ⟨_,u,d,X,r,hS,hnm,hs2',hsum,rfl⟩
lemma Qas {G H:Type u} [Group G] [Finite G] [Group H] [Finite H] {p m:ℕ}
    (hp:p.Prime) {D:Qy p m} (hG:Q1t hp m G D) (hH:Q1t hp m H D):
    Nonempty (G≃*H):=by
 obtain ⟨u₁,d₁,X₁,r₁,hS₁,hnm₁,hs₁,hsum₁,e₁⟩:=hG
 obtain ⟨u₂,d₂,X₂,r₂,hS₂,hnm₂,hs₂,hsum₂,e₂⟩:=hH
 exact Qjz hp d₁.normalize d₂.normalize
   (Q2.Qc5 hp hS₁ hS₂ hnm₁ hs₁ hsum₁ hnm₂ hs₂ hsum₂ (e₁.trans e₂.symm))
   (Q5.Qfj hS₁.valid) X₁ X₂ (Q5.Q7y hS₁.realizes)
   (Q5.Q7y hS₂.realizes)
end DataBridge
section FiberCount
variable {G:Type u} [Group G] {p:ℕ} {u:ℕ→G} {d:Q5} {X:Fin d.n→G}
  {r :ℕ→ℕ}
lemma Q2.Qad (hS:Q2 p u d X r) {c:ℕ} (hn:d.n=Q0 r c)
    (k:Q6 c (Q4y r c)):Q4l d (Q0 r k.1.val+k.2.val)=d.a (hS.Q8 hn k):=by
 unfold Q4l
 exact dif_pos (hS.Q8 hn k).isLt
lemma Q2.Qe7 (hS:Q2 p u d X r) {c:ℕ} (hn:d.n=Q0 r c)
    (k k':Q6 c (Q4y r c)):
    Q8h d (Q0 r k.1.val+k.2.val) (Q0 r k'.1.val+k'.2.val)=
      d.b (hS.Q8 hn k) (hS.Q8 hn k'):=by
 unfold Q8h
 exact dif_pos ⟨(hS.Q8 hn k).isLt,(hS.Q8 hn k').isLt⟩
lemma Q2.Q5m [Finite G] (hp:p.Prime) (hS:Q2 p u d X r)
    {c:ℕ} (hn:d.n=Q0 r c) (k k':Q6 c (Q4y r c)):
    ((hS.toQ7 hp hn).Ql k k').val=d.b (hS.Q8 hn k) (hS.Q8 hn k'):=by
 have hx:=Classical.choose_spec
   (hS.nf_exists (X (hS.Q8 hn k)^p^d.a (hS.Q8 hn k)))
 have h2:=hS.nf_unique _ (d.b (hS.Q8 hn k)) hx.1 (fun t=>hS.bounded.1 _ t)
   (hx.2.symm.trans (hS.realizes.pow _))
 show Classical.choose (hS.nf_exists (X (hS.Q8 hn k)^p^d.a (hS.Q8 hn k)))
   (hS.Q8 hn k')=_
 rw[h2]
lemma Q2.Qdg [Finite G] (hp:p.Prime) (hS:Q2 p u d X r)
    {c:ℕ} (hn:d.n=Q0 r c) (k k':Q6 c (Q4y r c)):
    Q8h d (hS.Q8 hn k).val (hS.Q8 hn k').val=
      ((hS.toQ7 hp hn).Ql k k').val:=by
 rw[hS.Q5m hp hn]
 exact hS.Qe7 hn k k'
lemma Q88 (r :ℕ→ℕ):∀ c i,i<Q0 r c→∃ w<c,∃ v< r w,i=Q0 r w+v
  | 0,i,h=>absurd h (by show ¬ i<0; omega)
  | c +1,i,h=>by
    by_cases hi:i<Q0 r c
    · obtain ⟨w,hw,v,hv,e⟩:=Q88 r c i hi
      exact ⟨w,by omega,v,hv,e⟩
    · rw[Q19]at h
      exact ⟨c,by omega,i - Q0 r c,by omega,by omega⟩
def Q63 {n q:ℕ} (B:Fin n→Fin n→Fin q) (i j:ℕ):ℕ:=
  if h:i<n∧j<n then (B ⟨i,h.1⟩ ⟨j,h.2⟩).val else 0
lemma Qi0 {n q:ℕ} (B:Fin n→Fin n→Fin q) (i j:Fin n):
    Q63 B i.val j.val=(B i j).val:=by
 unfold Q63
 rw[dif_pos ⟨i.isLt,j.isLt⟩]
def Q9 {m:ℕ} (D:Qg m) (i:ℕ):ℕ:=
  if h:i<D.1.val then (D.2.2.1.1 ⟨i,h⟩).val else 0
def Q6x {m:ℕ} (D:Qg m) (j:ℕ):ℕ:=
  if h:j<D.2.2.1.tot then (D.2.2.2.2.2.1 ⟨j,h⟩).val else 0
abbrev Q4 {m:ℕ} (D:Qg m):Fin D.1.val→ℕ:=Q4y (Q9 D) D.1.val
def Qc {m:ℕ} (D:Qg m):Q6 D.1.val (Q4 D)→ℕ:=
  fun k=>Q6x D (Q0 (Q9 D) k.1.val+k.2.val)
lemma Qj9 {m:ℕ} (D:Qg m):D.2.2.1.tot=Q0 (Q9 D) D.1.val:=by
 unfold Q1w.tot
 rw[← Q50]
 refine Finset.sum_congr rfl fun i _=>?_
 unfold Q9
 rw[dif_pos i.isLt]
lemma Qhx {m:ℕ} (D:Qg m) (k:Q6 D.1.val (Q4 D)):
    Q0 (Q9 D) k.1.val+k.2.val<D.2.2.1.tot:=
  Qjl (Q9 D) (Qj9 D) k.1 k.2
lemma Qhn {m:ℕ} (D:Qg m) (k:Q6 D.1.val (Q4 D)):1≤Qc D k:=by
 show 1≤Q6x D (Q0 (Q9 D) k.1.val+k.2.val)
 unfold Q6x
 rw[dif_pos (Qhx D k)]
 exact D.2.2.2.2.2.2.1 _
def Q58 {m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0}) (D:Qg m):
    Set (Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)):=
  {B | ∃ G∈T,∃ C,Q1t hp m G (⟨D,(B,C)⟩:Qy p m)}
lemma Qgn {m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0})
    (hT:∀ G∈T,ZB G=p^m∧lcs G 1≠⊥):
    (Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) '' T).Finite:=by
 have hsub:∀ D:Qy p m,Set.Subsingleton {s | ∃ G∈T,
     Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) G=s∧
       Q1t hp m G D}:=by
   intro D
   rintro s₁ ⟨G₁,hG₁,rfl,h₁⟩ s₂ ⟨G₂,hG₂,rfl,h₂⟩
   obtain ⟨e⟩:=Qas hp h₁ h₂
   exact Quotient.sound ⟨CategoryTheory.InducedCategory.isoMk (MulEquiv.toGrpIso e)⟩
 refine Set.Finite.subset (Set.finite_iUnion fun D:Qy p m=> (hsub D).finite) ?_
 rintro s ⟨G,hG,rfl⟩
 obtain ⟨D,hD⟩:=Qg2 hp (hT G hG).1 (hT G hG).2
 exact Set.mem_iUnion.mpr ⟨D,G,hG,rfl,hD⟩
lemma Qfx {m:ℕ} (hp:p.Prime) {H:Type u} [Group H] [Finite H] {D:Qg m}
    {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    {C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    (hc:Q1t hp m H (⟨D,(B,C)⟩:Qy p m)):
    ∃ (u :ℕ→H) (d:Q5) (X:Fin d.n→H) (r :ℕ→ℕ) (hS:Q2 p u d X r),
      D.1.val=hS.nL∧(∀ i<hS.nL,Q9 D i=r i)∧(∀ j,Q6x D j=Q4l d j)∧
        D.2.2.1.tot=d.n∧(∀ i j,Q63 B i j=Q8h d i j):=by
 obtain ⟨u,d,X,r,hS,hnm,hs2,hsum,e⟩:=hc
 refine ⟨u,d,X,r,hS,(congrArg Qn3 e).symm,?_,?_,?_,?_⟩
 · intro i hi
   have h:= congrFun (congrArg Qn1 e) i
   rw[hS.Qdd hp hnm hs2 hsum,dif_pos hi]at h
   exact h.symm
 · intro j
   have h:= congrFun (congrArg Qll e) j
   rw[hS.Qde hp hnm hs2 hsum]at h
   exact h.symm
 · have h:(hS.Q22 hp hnm).tot=D.2.2.1.tot:=
     congrArg (fun E:Qy p m=>E.1.2.2.1.tot) e
   exact h.symm.trans (hS.Q4t hp hnm)
 · intro i j
   have h:= congrFun (congrFun (congrArg Qmf e) i) j
   rw[hS.Qdb hp hnm hs2 hsum]at h
   exact h.symm
lemma Qeu {m:ℕ} (hp:p.Prime) {H:Type u} [Group H] [Finite H]
    {D:Qg m} {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    {C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    (hc:Q1t hp m H (⟨D,(B,C)⟩:Qy p m)) (i j:ℕ) (hj:j<D.2.2.1.tot):
    Q63 B i j<p^Q6x D j:=by
 obtain ⟨u,d,X,r,hS, -, -,hA,htot,hB⟩:=Qfx hp hc
 rw[hB,hA]
 rw[htot]at hj
 unfold Q8h Q4l
 rw[dif_pos hj]
 split_ifs with h
 · exact hS.bounded.1 _ _
 · exact pow_pos hp.pos _
def Ql6 {m:ℕ} (hp0:0<p) (D:Qg m)
    (B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)):
    Q3q p D.1.val (Q4 D) (Qc D):=
  fun k h=>if hlt:Q63 B (Q0 (Q9 D) k.1.val+k.2.val)
      (Q0 (Q9 D) h.1.val+h.2.val)<p^Qc D h then ⟨_,hlt⟩
    else ⟨0,pow_pos hp0 _⟩
lemma Q5r {m:ℕ} (hp:p.Prime) {H:Type u} [Group H] [Finite H]
    {D:Qg m} {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    {C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    (hc:Q1t hp m H (⟨D,(B,C)⟩:Qy p m)) (k h:Q6 D.1.val (Q4 D)):
    (Ql6 hp.pos D B k h).val=
      Q63 B (Q0 (Q9 D) k.1.val+k.2.val) (Q0 (Q9 D) h.1.val+h.2.val):=by
 have hlt:Q63 B (Q0 (Q9 D) k.1.val+k.2.val) (Q0 (Q9 D) h.1.val+h.2.val)<
     p^Qc D h:=Qeu hp hc _ _ (Qhx D h)
 simp only[Ql6,dif_pos hlt]
lemma Qf4 {c c':ℕ} {r :Fin c→ℕ} {r':Fin c'→ℕ} {a:Q6 c r→ℕ}
    {a':Q6 c' r'→ℕ} {B:Q3q p c r a} {B':Q3q p c' r' a'} (hc:c= c')
    (hr :∀ i:Fin c,r i=r' (Fin.cast hc i))
    (ha:∀ (i:Fin c) (v:Fin (r i)),a ⟨i,v⟩=a' ⟨Fin.cast hc i,Fin.cast (hr i) v⟩)
    (hB :∀ (i:Fin c) (v:Fin (r i)) (i':Fin c) (v':Fin (r i')),
      (B ⟨i,v⟩ ⟨i',v'⟩).val=
        (B' ⟨Fin.cast hc i,Fin.cast (hr i) v⟩ ⟨Fin.cast hc i',Fin.cast (hr i') v'⟩).val)
    (h:B∈Q48 p c r a):B'∈Q48 p c' r' a':=by
 subst hc
 have er :r=r':= funext hr
 subst er
 have ea:a=a':= funext fun k=>ha k.1 k.2
 subst ea
 have eB:B=B':= funext fun k=>funext fun k'=>Fin.ext (hB k.1 k.2 k'.1 k'.2)
 subst eB
 exact h
lemma Qd2 {m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0}) (D:Qg m):
    (Q58 hp T D).ncard≤(Q48 p D.1.val (Q4 D) (Qc D)).ncard:=by
 have:Fact p.Prime:=⟨hp⟩
 refine Set.ncard_le_ncard_of_injOn (Ql6 hp.pos D) ?_ ?_ (Set.toFinite _)
 · rintro B ⟨G, -,C,hc⟩
   obtain ⟨u,d,X,r,hS,hc1,hR,hA, -,hBf⟩:=Qfx hp hc
   have hn:d.n=Q0 r hS.nL:=hS.Q2j.symm
   have hG:IsPGroup p G:=IsPGroup.of_card hS.realizes.card
   have hmem:=(hS.toQ7 hp hn).Qhe hG
   refine Qf4 hc1.symm ?_ ?_ ?_ hmem
   · intro i
     exact (hR i.val i.isLt).symm
   · intro i v
     show d.a (hS.Q8 hn ⟨i,v⟩)=Q6x D (Q0 (Q9 D) i.val+v.val)
     rw[hA,Q41 hR i.val i.isLt.le]
     exact (hS.Qad hn ⟨i,v⟩).symm
   · intro i v i' v'
     rw[hS.Q5m hp hn,Q5r hp hc]
     show _=Q63 B (Q0 (Q9 D) i.val+v.val) (Q0 (Q9 D) i'.val+v'.val)
     rw[hBf,Q41 hR i.val i.isLt.le,Q41 hR i'.val i'.isLt.le]
     exact (hS.Qe7 hn ⟨i,v⟩ ⟨i',v'⟩).symm
 · rintro B₁ ⟨G₁, -,C₁,hc₁⟩ B₂ ⟨G₂, -,C₂,hc₂⟩ heq
   have hall:∀ k k':Q6 D.1.val (Q4 D),
       Q63 B₁ (Q0 (Q9 D) k.1.val+k.2.val) (Q0 (Q9 D) k'.1.val+k'.2.val)=
         Q63 B₂ (Q0 (Q9 D) k.1.val+k.2.val) (Q0 (Q9 D) k'.1.val+k'.2.val):=by
    intro k k'
    have h:= congrArg Fin.val (congrFun (congrFun heq k) k')
    rw[Q5r hp hc₁,Q5r hp hc₂]at h
    exact h
   funext i j
   apply Fin.ext
   obtain ⟨w,hw,v,hv,ei⟩:=
     Q88 (Q9 D) D.1.val i.val (lt_of_lt_of_eq i.isLt (Qj9 D))
   obtain ⟨w',hw',v',hv',ej⟩:=
     Q88 (Q9 D) D.1.val j.val (lt_of_lt_of_eq j.isLt (Qj9 D))
   have h2:Q63 B₁ (Q0 (Q9 D) w+v) (Q0 (Q9 D) w'+v')=
       Q63 B₂ (Q0 (Q9 D) w+v) (Q0 (Q9 D) w'+v'):=
     hall ⟨⟨w,hw⟩,⟨v,hv⟩⟩ ⟨⟨w',hw'⟩,⟨v',hv'⟩⟩
   rw[← ei, ← ej,Qi0,Qi0]at h2
   exact h2
end FiberCount
end OMA.SimsLite
namespace OMA.SimsLite.Alt2
open Module Matrix
section Defs
variable {F:Type*} [Field F] {R M:ℕ}
def Q1y (A:Matrix (Fin R) (Fin R) F):Prop:=
  (∀ i,A i i=0)∧∀ i j,A j i= -A i j
variable (R) in
abbrev Q7r :Type:={p:Fin R×Fin R//p.1<p.2}
lemma Qk6 (R:ℕ):Fintype.card (Q7r R)=R.choose 2:=by
 have h1:Fintype.card (Q7r R)=
     ∑ j:Fin R,∑ i:Fin R,if i<j then 1 else 0:=by
   rw[Fintype.card_subtype,Finset.card_filter,Fintype.sum_prod_type,Finset.sum_comm]
 have h2:∀ j:Fin R,(∑ i:Fin R,if i<j then 1 else 0)=(j:ℕ):=by
   intro j
   rw[← Finset.card_filter,Finset.filter_gt_eq_Iio,Fin.card_Iio]
 have h3:∑ j:Fin R,(j:ℕ)=∑ i∈ZQ R,i:=
   Fin.sum_univ_eq_sum_range (fun i=>i) R
 rw [h1,Finset.sum_congr rfl (fun j _=>h2 j),h3,Nat.choose_two_right,
   ← Finset.sum_range_id_mul_two,Nat.mul_div_cancel _ (by norm_num)]
def Qfv (x y:Fin R→F):Matrix (Fin R) (Fin R) F→ₗ[F] F where
  toFun A:=x ⬝ᵥ (A*ᵥ y)
  map_add' A B:=by rw[Matrix.add_mulVec,dotProduct_add]
  map_smul' c A:=by rw[Matrix.smul_mulVec,dotProduct_smul,RingHom.id_apply]
lemma Q45 (x y:Fin R→F) (A:Matrix (Fin R) (Fin R) F):
    Qfv x y A=x ⬝ᵥ (A*ᵥ y):=rfl
lemma Ql3 (A:Matrix (Fin R) (Fin R) F) (i j:Fin R):
    Qfv (Pi.single i 1) (Pi.single j 1) A=A i j:=by
 simp[Qfv,dotProduct,Matrix.mulVec,Pi.single_apply]
lemma Q4n {A:Matrix (Fin R) (Fin R) F} (hA:Q1y A) (x:Fin R→F):
    Qfv x x A=0:=by
 rw[Q45,Matrix.dot_mulVec_eq_sum_sum]
 have e:∑ j,∑ i,x i*A i j*x j=∑ p:Fin R×Fin R,x p.2*A p.2 p.1*x p.1:=
   (Fintype.sum_prod_type' (fun j i=>x i*A i j*x j)).symm
 rw[e]
 apply Finset.sum_ninvolution (fun p=> (p.2,p.1))
 · rintro ⟨j,i⟩
   show x i*A i j*x j+x j*A j i*x i=0
   rw[hA.2 i j]
   ring
 · rintro ⟨j,i⟩ hne heq
   have hij:i=j:= congrArg Prod.fst heq
   apply hne
   show x i*A i j*x j=0
   rw[hij,hA.1 j]
   ring
 · intro p
   exact Finset.mem_univ _
 · intro p
   rfl
def vals (β:Fin M→Matrix (Fin R) (Fin R) F) (U:Submodule F (Fin R→F)):
    Set (Fin M→F):=
  {w | ∃ x∈U,∃ y∈U,w= fun k=>Qfv x y (β k)}
def Q1k (β:Fin M→Matrix (Fin R) (Fin R) F) (U:Submodule F (Fin R→F)):Prop:=
  Submodule.span F (vals β U)=⊤
noncomputable def Q2b (β:Fin M→Matrix (Fin R) (Fin R) F):ℕ:=
  sInf {d | ∃ U:Submodule F (Fin R→F),finrank F U=d∧Q1k β U}
end Defs
section Duality
variable {F:Type*} [Field F] {R M:ℕ}
lemma Q90 (β:Fin M→Matrix (Fin R) (Fin R) F) {U:Submodule F (Fin R→F)} {d:ℕ}
    (hU:finrank F U=d) (hg:Q1k β U):Q2b β≤d:=
  Nat.sInf_le ⟨U,hU,hg⟩
lemma Qjw (β:Fin M→Matrix (Fin R) (Fin R) F) (hg:Q1k β ⊤):Q2b β≤R:=
  Q90 β (by rw[finrank_top,Module.finrank_fin_fun]) hg
lemma Qb3 (β:Fin M→Matrix (Fin R) (Fin R) F) (hg:Q1k β ⊤):
    ∃ U:Submodule F (Fin R→F),finrank F U=Q2b β∧Q1k β U:=
  Nat.sInf_mem (s:={d | ∃ U:Submodule F (Fin R→F),finrank F U=d∧Q1k β U})
    ⟨R,⊤,by rw[finrank_top,Module.finrank_fin_fun],hg⟩
end Duality
section N2
open Classical in
noncomputable def N2 (r1 r2 s:ℕ):ℕ:=
  (Finset.univ.filter (fun β:Fin r2→Matrix (Fin r1) (Fin r1) (ZMod 2)=>
    (∀ k,Q1y (β k))∧Q1k β ⊤∧Q2b β=s)).card
lemma Qe4 (r1 r2 s:ℕ):N2 r1 r2 s=
    {β :Fin r2→Matrix (Fin r1) (Fin r1) (ZMod 2) |
      (∀ k,Q1y (β k))∧Q1k β ⊤∧Q2b β=s}.ncard:=by
  classical
  unfold N2
  rw[← Set.ncard_coe_finset]
  congr 1
  ext β
  simp
noncomputable def Qiq (r1 r2 s:ℕ):ℝ:=Real.logb 2 (N2 r1 r2 s)
end N2
section Lemma27
variable {F:Type*} [Field F]
lemma Qcp (n k:ℕ):
    {U :Submodule F (Fin n→F) | finrank F U=k}⊆
      ZG (fun v:Fin k→(Fin n→F)=>Submodule.span F (ZG v)):=by
  intro U hU
  let B:=Module.finBasisOfFinrankEq F U hU
  refine ⟨fun i=> (B i:Fin n→F),?_⟩
  have h:= congrArg (Submodule.map U.subtype) B.span_eq
  rw[Submodule.map_span,Submodule.map_subtype_top, ← Set.range_comp]at h
  exact h
end Lemma27
section Grass
variable {F:Type*} [Field F] {n:ℕ}
end Grass
section Lemma27ii
variable {F:Type*} [Field F] {R:ℕ}
lemma Qmw {A:Matrix (Fin R) (Fin R) F} (hA:Q1y A) (x y:Fin R→F):
    Qfv x y A= -Qfv y x A:=by
 have h:=Q4n hA (x+y)
 have hx:=Q4n hA x
 have hy:=Q4n hA y
 rw[Q45,Matrix.mulVec_add,dotProduct_add,add_dotProduct,add_dotProduct]at h
 rw[Q45]at hx hy
 rw[Q45,Q45]
 linear_combination h - hx - hy
end Lemma27ii
section Lemma81
variable {F:Type*} [Field F] {R:ℕ}
end Lemma81
section SimsBounds
variable {F:Type*} [Field F] {R M:ℕ}
def Q2v (β:Fin M→Matrix (Fin R) (Fin R) F):
    (Fin R→F)→ₗ[F] (Fin R→F)→ₗ[F] (Fin M→F):=
  LinearMap.mk₂ F (fun x y k=>Qfv x y (β k))
    (fun x x' y=>by funext k; simp[Q45,add_dotProduct])
    (fun c x y=>by funext k; simp[Q45,smul_dotProduct])
    (fun x y y'=>by funext k; simp[Q45,Matrix.mulVec_add,dotProduct_add])
    (fun c x y=>by funext k; simp[Q45,Matrix.mulVec_smul,dotProduct_smul])
lemma Qlh (β:Fin M→Matrix (Fin R) (Fin R) F) (x y:Fin R→F):
    Q2v β x y= fun k=>Qfv x y (β k):=rfl
lemma Qig (β:Fin M→Matrix (Fin R) (Fin R) F) {U:Submodule F (Fin R→F)}
    {x y:Fin R→F} (hx:x∈U) (hy:y∈U):Q2v β x y∈vals β U:=
  ⟨x,hx,y,hy,rfl⟩
lemma Qlk (β:Fin M→Matrix (Fin R) (Fin R) F) (hA:∀ k,Q1y (β k))
    (x:Fin R→F):Q2v β x x =0:=by
 funext k
 exact Q4n (hA k) x
lemma Qm0 (β:Fin M→Matrix (Fin R) (Fin R) F) (hA:∀ k,Q1y (β k))
    (x y:Fin R→F):Q2v β y x = -Q2v β x y:=by
 funext k
 exact Qmw (hA k) y x
lemma Qa8 (β:Fin M→Matrix (Fin R) (Fin R) F) (hA:∀ k,Q1y (β k))
    {s:ℕ} (v:Fin s→(Fin R→F)):
    vals β (Submodule.span F (ZG v))⊆
      Submodule.span F (ZG (fun q:Q7r s=>Q2v β (v q.1.1) (v q.1.2))):=by
  set S:=Submodule.span F (ZG (fun q:Q7r s=>Q2v β (v q.1.1) (v q.1.2)))
  have h1:∀ i j,Q2v β (v i) (v j)∈S:=by
   intro i j
   rcases lt_trichotomy i j with h | h | h
   · exact Submodule.subset_span ⟨⟨(i,j),h⟩,rfl⟩
   · rw[h,Qlk β hA]
     exact S.zero_mem
   · rw[Qm0 β hA]
     exact S.neg_mem (Submodule.subset_span ⟨⟨(j,i),h⟩,rfl⟩)
  have h2:∀ j,∀ x∈Submodule.span F (ZG v),Q2v β x (v j)∈S:=by
   intro j x hx
   have hle:Submodule.span F (ZG v)≤S.comap ((Q2v β).flip (v j)):=by
    rw[Submodule.span_le]
    rintro _ ⟨i,rfl⟩
    exact h1 i j
   exact hle hx
  rintro w ⟨x,hx,y,hy,rfl⟩
  have hle:Submodule.span F (ZG v)≤S.comap (Q2v β x):=by
   rw[Submodule.span_le]
   rintro _ ⟨j,rfl⟩
   exact h2 j x hx
  exact hle hy
lemma Qb5 (β:Fin M→Matrix (Fin R) (Fin R) F) (hA:∀ k,Q1y (β k))
    (hg:Q1k β ⊤):M≤(Q2b β).choose 2:=by
 obtain ⟨U,hU,hgU⟩:=Qb3 β hg
 obtain ⟨v,hv⟩:=Qcp (F:=F) R (Q2b β) hU
 have hv':Submodule.span F (ZG v)=U:=hv
 have hsub:=Qa8 β hA v
 rw[hv']at hsub
 have htop:Submodule.span F
     (ZG (fun q:Q7r (Q2b β)=>Q2v β (v q.1.1) (v q.1.2)))=⊤:=by
   apply top_unique
   unfold Q1k at hgU
   rw[← hgU]
   exact Submodule.span_le.2 hsub
 have h1:finrank F (Submodule.span F
     (ZG (fun q:Q7r (Q2b β)=>Q2v β (v q.1.1) (v q.1.2))))≤
     Fintype.card (Q7r (Q2b β)):=
   finrank_range_le_card (fun q:Q7r (Q2b β)=>Q2v β (v q.1.1) (v q.1.2))
 rw[htop,finrank_top,Module.finrank_fin_fun,Qk6]at h1
 exact h1
def Q1f (β:Fin M→Matrix (Fin R) (Fin R) F) (u:ℕ→(Fin R→F)) (k:ℕ):
    Submodule F (Fin M→F):=
  Submodule.span F {w | ∃ a b,a<b∧b<k∧w=Q2v β (u a) (u b)}
def Q3r (β:Fin M→Matrix (Fin R) (Fin R) F) (u:ℕ→(Fin R→F)) (t:ℕ):
    Prop:=
  ∀ k,1≤k→k<t→Q1f β u k≠Q1f β u (k+1)
lemma Q42 (β:Fin M→Matrix (Fin R) (Fin R) F) (u:ℕ→(Fin R→F)) {a b k:ℕ}
    (hab:a<b) (hbk:b<k):Q2v β (u a) (u b)∈Q1f β u k:=
  Submodule.subset_span ⟨a,b,hab,hbk,rfl⟩
lemma Qe6 (β:Fin M→Matrix (Fin R) (Fin R) F) (u:ℕ→(Fin R→F)) {k l:ℕ}
    (hkl:k≤l):Q1f β u k≤Q1f β u l:=by
 apply Submodule.span_mono
 rintro _ ⟨a,b,hab,hbk,rfl⟩
 exact ⟨a,b,hab,by omega,rfl⟩
lemma Q6h (β:Fin M→Matrix (Fin R) (Fin R) F) {u:ℕ→(Fin R→F)} {k:ℕ}
    {S:Submodule F (Fin M→F)} (h:∀ a b,a<b→ b<k→Q2v β (u a) (u b)∈S):
    Q1f β u k≤S:=by
 rw[Q1f,Submodule.span_le]
 rintro _ ⟨a,b,hab,hbk,rfl⟩
 exact h a b hab hbk
lemma Qcj (β:Fin M→Matrix (Fin R) (Fin R) F) {u u':ℕ→(Fin R→F)} {k:ℕ}
    (h:∀ i<k,u i=u' i):Q1f β u k=Q1f β u' k:=by
 apply le_antisymm
 · refine Q6h β fun a b hab hbk=>?_
   rw[h a (by omega),h b hbk]
   exact Q42 β u' hab hbk
 · refine Q6h β fun a b hab hbk=>?_
   rw[← h a (by omega), ← h b hbk]
   exact Q42 β u hab hbk
lemma Qky (β:Fin M→Matrix (Fin R) (Fin R) F) (u:ℕ→(Fin R→F)):
    Q1f β u 1=⊥:=by
 refine le_antisymm ?_ bot_le
 refine Q6h β fun a b hab hb=>?_
 exact absurd hab (by omega)
lemma Qbc (β:Fin M→Matrix (Fin R) (Fin R) F) {u:ℕ→(Fin R→F)}
    {s:ℕ} (h:Q1f β u s≠Q1f β u (s+1)):
    ∃ a<s,Q2v β (u a) (u s)∉Q1f β u s:=by
 by_contra hc
 push_neg at hc
 apply h
 apply le_antisymm (Qe6 β u (Nat.le_succ s))
 refine Q6h β fun a b hab hb=>?_
 by_cases hbs:b<s
 · exact Q42 β u hab hbs
 · rw[show b=s by omega]
   exact hc a (by omega)
lemma Qdm (β:Fin M→Matrix (Fin R) (Fin R) F) {u:ℕ→(Fin R→F)} {t:ℕ}
    (hu:Q3r β u t):∀ k,1≤k→k≤t→k - 1≤finrank F (Q1f β u k):=by
 intro k
 induction k with
 | zero=>intro h; exact absurd h (by norm_num)
 | succ k ih=>
   intro _ hkt
   rcases Nat.eq_zero_or_pos k with hk | hk
   · subst hk
     simp
   · have h1:=ih hk (by omega)
     have hlt:Q1f β u k<Q1f β u (k+1):=
       lt_of_le_of_ne (Qe6 β u (Nat.le_succ k)) (hu k hk (by omega))
     have h2:=Submodule.finrank_lt_finrank_of_lt hlt
     omega
lemma Q92 (β:Fin M→Matrix (Fin R) (Fin R) F) {u:ℕ→(Fin R→F)} {t:ℕ}
    (hu:Q3r β u t) (ht:1≤t):t≤M+1:=by
 have h1:=Qdm β hu t ht le_rfl
 have h2:=Submodule.finrank_le (Q1f β u t)
 rw[Module.finrank_fin_fun]at h2
 omega
lemma Qhh (β:Fin M→Matrix (Fin R) (Fin R) F) {u:ℕ→(Fin R→F)} {t:ℕ}
    (ht:2≤t) (hu:Q3r β u t) {x y:Fin R→F}
    (hxy:Q2v β x y∉Q1f β u t):∃ u':ℕ→(Fin R→F),Q3r β u' (t+1):=by
 by_cases hc:∃ a<t,∃ v,Q2v β (u a) v∉Q1f β u t
 · obtain ⟨a,ha,v,hv⟩:=hc
   set u':ℕ→(Fin R→F):= fun i=>if i<t then u i else v with hu'
   have hW:∀ k≤t,Q1f β u' k=Q1f β u k:= fun k hk=>
     Qcj β fun i hi=> (if_pos (show i<t by omega):u' i=u i)
   refine ⟨u',fun k hk1 hkt=>?_⟩
   rcases Nat.lt_or_ge k t with hk | hk
   · rw[hW k hk.le,hW (k+1) (by omega)]
     exact hu k hk1 hk
   · rw[show k=t by omega,hW t le_rfl]
     intro heq
     apply hv
     have hm:=Q42 β u' ha (show t<t+1 by omega)
     have e1:u' a=u a:=if_pos ha
     have e2:u' t=v:=if_neg (lt_irrefl t)
     rw[e1,e2, ← heq]at hm
     exact hm
 · have hc':∀ a<t,∀ v,Q2v β (u a) v∈Q1f β u t:= fun a ha v=>by
     by_contra hn
     exact hc ⟨a,ha,v,hn⟩
   obtain ⟨s,rfl⟩:∃ s,t=s+1:=⟨t - 1,by omega⟩
   obtain ⟨a0,ha0,hna0⟩:=Qbc β (hu s (by omega) (by omega))
   have hw :∃ w,(∃ a<s,Q2v β (u a) w∉Q1f β u s)∧
       Q2v β w y∉Q1f β u (s+1):=by
    by_cases hx':∃ a<s,Q2v β (u a) x∉Q1f β u s
    · exact ⟨x,hx',hxy⟩
    · push_neg at hx'
      refine ⟨u s+x,⟨a0,ha0,?_⟩,?_⟩
      · rw[map_add,Submodule.add_mem_iff_left _ (hx' a0 ha0)]
        exact hna0
      · rw [map_add,LinearMap.add_apply,
          Submodule.add_mem_iff_right _ (hc' s (by omega) y)]
        exact hxy
   obtain ⟨w,hw1,hw2⟩:=hw
   set u':ℕ→(Fin R→F):= fun i=>if i<s then u i else if i=s then w else y with hu'
   have e1:∀ i<s,u' i=u i:= fun i hi=>if_pos hi
   have e2:u' s=w:=by
    show (if s<s then u s else if s=s then w else y)=w
    rw[if_neg (lt_irrefl s),if_pos rfl]
   have e3:u' (s+1)=y:=by
    show (if s+1<s then u (s+1) else if s+1=s then w else y)=y
    rw[if_neg (show ¬ (s+1<s) by omega),if_neg (show ¬ (s+1=s) by omega)]
   have hW:∀ k≤ s,Q1f β u' k=Q1f β u k:= fun k hk=>
     Qcj β fun i hi=>e1 i (by omega)
   have hle:Q1f β u' (s+1)≤Q1f β u (s+1):=by
    refine Q6h β fun a b hab hb=>?_
    by_cases hbs:b<s
    · rw[e1 a (by omega),e1 b hbs]
      exact Q42 β u hab (by omega)
    · rw[show b=s by omega,e1 a (by omega),e2]
      exact hc' a (by omega) w
   refine ⟨u',fun k hk1 hkt=>?_⟩
   by_cases hks:k<s
   · rw[hW k (by omega),hW (k+1) (by omega)]
     exact hu k hk1 (by omega)
   · by_cases hk':k=s
     · rw[hk',hW s le_rfl]
       obtain ⟨a,ha,hna⟩:=hw1
       intro heq
       apply hna
       have hm:=Q42 β u' ha (show s<s+1 by omega)
       rw[e1 a ha,e2, ← heq]at hm
       exact hm
     · rw[show k=s+1 by omega]
       intro heq
       apply hw2
       have hm:=Q42 β u' (show s<s+1 by omega) (show s+1<s+1+1 by omega)
       rw[e2,e3, ← heq]at hm
       exact hle hm
lemma Q7t (β:Fin M→Matrix (Fin R) (Fin R) F) (hg:Q1k β ⊤)
    {S:Submodule F (Fin M→F)} (hS:S≠⊤):∃ x y,Q2v β x y∉S:=by
 by_contra hc
 push_neg at hc
 apply hS
 apply top_unique
 unfold Q1k at hg
 rw[← hg,Submodule.span_le]
 rintro _ ⟨x, -,y, -,rfl⟩
 exact hc x y
lemma Qdk (β:Fin M→Matrix (Fin R) (Fin R) F) (hg:Q1k β ⊤)
    (hM:1≤M):∃ u:ℕ→(Fin R→F),∃ t,Q3r β u t∧2≤t∧
      Q1f β u t=⊤:=by
 have hne:(⊥:Submodule F (Fin M→F))≠⊤:=by
  intro h
  have hmem:(Pi.single (⟨0,hM⟩:Fin M) (1:F):Fin M→F)∈
      (⊥:Submodule F (Fin M→F)):=by
   rw[h]
   exact Submodule.mem_top
  rw[Submodule.mem_bot]at hmem
  have:= congrFun hmem ⟨0,hM⟩
  simp at this
 obtain ⟨x0,y0,h0⟩:=Q7t β hg hne
 have step:∀ j,∃ u:ℕ→(Fin R→F),∃ t,Q3r β u t∧2≤t∧
     (Q1f β u t=⊤∨j+2≤t):=by
  intro j
  induction j with
  | zero=>
    set u:ℕ→(Fin R→F):= fun i=>if i=0 then x0 else y0 with hu
    refine ⟨u,2,fun k hk1 hk2=>?_,le_rfl,Or.inr (by norm_num)⟩
    rw[show k=1 by omega,Qky]
    intro heq
    apply h0
    have hm:=Q42 β u (show 0<1 by norm_num) (show 1<1+1 by norm_num)
    have e0:u 0=x0:=if_pos rfl
    have e1:u 1=y0:=if_neg (by norm_num)
    rw[e0,e1, ← heq]at hm
    exact hm
  | succ j ih=>
    obtain ⟨u,t,hu,ht,hor⟩:=ih
    by_cases htop:Q1f β u t=⊤
    · exact ⟨u,t,hu,ht,Or.inl htop⟩
    · have hj:j+2≤t:=hor.resolve_left htop
      obtain ⟨x,y,hxy⟩:=Q7t β hg htop
      obtain ⟨u',hu'⟩:=Qhh β ht hu hxy
      exact ⟨u',t+1,hu',by omega,Or.inr (by omega)⟩
 obtain ⟨u,t,hu,ht,hor⟩:=step M
 rcases hor with h | h
 · exact ⟨u,t,hu,ht,h⟩
 · have:=Q92 β hu (by omega)
   omega
lemma Qh3 (β:Fin M→Matrix (Fin R) (Fin R) F) (hg:Q1k β ⊤):
    Q2b β≤M+1:=by
 rcases Nat.eq_zero_or_pos M with hM | hM
 · subst hM
   have hbot:Q1k β ⊥:=by
    unfold Q1k
    apply eq_top_iff.2
    intro w _
    rw[Subsingleton.elim w 0]
    exact Submodule.zero_mem _
   have:=Q90 β (U:=⊥) (d:=0) (by simp) hbot
   omega
 · obtain ⟨u,t,hu,ht,htop⟩:=Qdk β hg hM
   set U:Submodule F (Fin R→F):=Submodule.span F (ZG (fun i:Fin t=>u i))
   have hmemU:∀ i<t,u i∈U:= fun i hi=>
     Submodule.subset_span ⟨⟨i,hi⟩,rfl⟩
   have hgU:Q1k β U:=by
    unfold Q1k
    apply top_unique
    rw[← htop]
    refine Q6h β fun a b hab hb=>?_
    exact Submodule.subset_span (Qig β (hmemU a (by omega)) (hmemU b hb))
   have h1:=Q90 β rfl hgU
   have h2:finrank F U≤Fintype.card (Fin t):=
     finrank_range_le_card (fun i:Fin t=>u i)
   have h3:=Q92 β hu (by omega)
   rw[Fintype.card_fin]at h2
   omega
end SimsBounds
section GrassLower
variable {F:Type*} [Field F] {n k:ℕ}
end GrassLower
section SubgroupCount
variable {G:Type*} [Group G]
end SubgroupCount
section Transport
variable {F V W:Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  {r1 r2:ℕ}
def Q4q (B:V→ₗ[F] V→ₗ[F] W) (U:Submodule F V):Prop:=
  Submodule.span F {w | ∃ x∈U,∃ y∈U,w=B x y}=⊤
noncomputable def Q9r (B:V→ₗ[F] V→ₗ[F] W):ℕ:=
  sInf {d | ∃ U:Submodule F V,finrank F U=d∧Q4q B U}
noncomputable def Q3c (B:V→ₗ[F] V→ₗ[F] W) (bV:Basis (Fin r1) F V) (bW:Basis (Fin r2) F W):
    Fin r2→Matrix (Fin r1) (Fin r1) F:=
  fun k i j=>bW.repr (B (bV i) (bV j)) k
lemma equivFun_symm_single (b:Basis (Fin r1) F V) (i:Fin r1):
    b.equivFun.symm (Pi.single i 1)=b i:=by
 rw[Basis.equivFun_symm_apply]
 simp[Pi.single_apply]
lemma Qc3 (B:V→ₗ[F] V→ₗ[F] W) (bV:Basis (Fin r1) F V)
    (bW:Basis (Fin r2) F W) (x y:Fin r1→F):
    Q2v (Q3c B bV bW) x y=
      bW.equivFun (B (bV.equivFun.symm x) (bV.equivFun.symm y)):=by
 have h :Q2v (Q3c B bV bW)=
     (B.compl₁₂ bV.equivFun.symm.toLinearMap bV.equivFun.symm.toLinearMap).compr₂
       bW.equivFun.toLinearMap:=by
  refine LinearMap.ext_basis (Pi.basisFun F (Fin r1)) (Pi.basisFun F (Fin r1)) fun i j=>?_
  show Q2v (Q3c B bV bW) (Pi.basisFun F (Fin r1) i) (Pi.basisFun F (Fin r1) j)=
    bW.equivFun (B (bV.equivFun.symm (Pi.basisFun F (Fin r1) i))
      (bV.equivFun.symm (Pi.basisFun F (Fin r1) j)))
  rw [Pi.basisFun_apply,Pi.basisFun_apply,equivFun_symm_single,equivFun_symm_single,
    Qlh]
  funext k
  rw[Ql3,Basis.equivFun_apply]
  rfl
 rw[h]
 rfl
lemma Qgz (B:V→ₗ[F] V→ₗ[F] W) (hB:∀ x,B x x =0) (bV:Basis (Fin r1) F V)
    (bW:Basis (Fin r2) F W) (k:Fin r2):Q1y (Q3c B bV bW k):=by
 refine ⟨fun i=>?_,fun i j=>?_⟩
 · show bW.repr (B (bV i) (bV i)) k=0
   rw[hB,map_zero,Finsupp.zero_apply]
 · have h2:B (bV j) (bV i)= -B (bV i) (bV j):=by
     have:=hB (bV i+bV j)
     simp only[map_add,LinearMap.add_apply,hB,zero_add,add_zero]at this
     rw[eq_neg_iff_add_eq_zero]
     first
       | exact this
       | exact (add_comm _ _).trans this
   show bW.repr (B (bV j) (bV i)) k= -bW.repr (B (bV i) (bV j)) k
   rw[h2,map_neg,Finsupp.neg_apply]
lemma Qf1 (bV:Basis (Fin r1) F V) (U:Submodule F V):
    (U.map bV.equivFun.toLinearMap).map bV.equivFun.symm.toLinearMap=U:=by
 rw[← Submodule.map_comp]
 convert Submodule.map_id U
 ext v
 simp
lemma Q4v (B:V→ₗ[F] V→ₗ[F] W) (bV:Basis (Fin r1) F V)
    (bW:Basis (Fin r2) F W) (U:Submodule F (Fin r1→F)):
    Q1k (Q3c B bV bW) U↔Q4q B (U.map bV.equivFun.symm.toLinearMap):=by
 set U':=U.map bV.equivFun.symm.toLinearMap with hU'
 set S:Set W:={w | ∃ x∈U',∃ y∈U',w=B x y} with hS
 have hv:vals (Q3c B bV bW) U=bW.equivFun.toLinearMap '' S:=by
  ext w
  constructor
  · rintro ⟨x,hx,y,hy,rfl⟩
    refine ⟨B (bV.equivFun.symm x) (bV.equivFun.symm y),
      ⟨_,Submodule.mem_map_of_mem hx,_,Submodule.mem_map_of_mem hy,rfl⟩,?_⟩
    exact (Qc3 B bV bW x y).symm
  · rintro ⟨_,⟨x',hx',y',hy',rfl⟩,rfl⟩
    obtain ⟨x,hx,rfl⟩:=Submodule.mem_map.1 hx'
    obtain ⟨y,hy,rfl⟩:=Submodule.mem_map.1 hy'
    exact ⟨x,hx,y,hy,(Qc3 B bV bW x y).symm⟩
 unfold Q1k Q4q
 rw[hv,Submodule.span_image]
 first
   | exact Submodule.map_eq_top_iff
   | rw[Submodule.map_eq_top_iff (LinearEquiv.range _),LinearEquiv.ker,sup_bot_eq]
lemma Qfn (B:V→ₗ[F] V→ₗ[F] W) (bV:Basis (Fin r1) F V)
    (bW:Basis (Fin r2) F W):Q2b (Q3c B bV bW)=Q9r B:=by
 unfold Q2b Q9r
 congr 1
 ext d
 constructor
 · rintro ⟨U,hU,hg⟩
   exact ⟨U.map bV.equivFun.symm.toLinearMap,by rw[LinearEquiv.finrank_map_eq,hU],
     (Q4v B bV bW U).1 hg⟩
 · rintro ⟨U',hU',hg⟩
   refine ⟨U'.map bV.equivFun.toLinearMap,by rw[LinearEquiv.finrank_map_eq,hU'],?_⟩
   rw[Q4v,Qf1]
   exact hg
lemma Q9d (B:V→ₗ[F] V→ₗ[F] W) (bV:Basis (Fin r1) F V)
    (bW:Basis (Fin r2) F W):Q1k (Q3c B bV bW) ⊤↔Q4q B ⊤:=by
 rw[Q4v,Submodule.map_top,LinearEquiv.range]
end Transport
end OMA.SimsLite.Alt2
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section Q32
variable {p:ℕ} {H:Type u} [Group H]
abbrev Qdc (p:ℕ) (H:Type u) [Group H] (K:Subgroup H):Subgroup (Abelianization H):=
  K.map ZH⊔(powMonoidHom p:Abelianization H→*Abelianization H).range
abbrev Q32 (p:ℕ) (H:Type u) [Group H] (K:Subgroup H):Type u:=
  Abelianization H⧸Qdc p H K
def Qav (p:ℕ) (H:Type u) [Group H] (K:Subgroup H):H→*Q32 p H K:=
  (ZF (Qdc p H K)).comp ZH
lemma Q3e (K:Subgroup H):Function.Surjective (Qav p H K):=by
 intro x
 obtain ⟨a,rfl⟩:=QuotientGroup.mk_surjective x
 obtain ⟨g,hg⟩:=QuotientGroup.mk_surjective (a:H⧸commutator H)
 refine ⟨g,?_⟩
 rw[← hg]
 rfl
lemma Qhy (K:Subgroup H) (x:Q32 p H K):x^p=1:=by
 obtain ⟨a,rfl⟩:=QuotientGroup.mk_surjective x
 rw[← QuotientGroup.mk_pow,QuotientGroup.eq_one_iff]
 exact ZL (MonoidHom.mem_range.mpr ⟨a,rfl⟩)
lemma Qbi {K:Subgroup H} (h1:commutator H≤K) (h2:∀ g:H,g^p∈K):
    (Qav p H K).ker=K:=by
 have hle:(powMonoidHom p:Abelianization H→*Abelianization H).range≤
     K.map ZH:=by
  rintro _ ⟨a,rfl⟩
  obtain ⟨g,hg⟩:=QuotientGroup.mk_surjective (a:H⧸commutator H)
  refine Subgroup.mem_map.mpr ⟨g^p,h2 g,?_⟩
  rw[map_pow]
  rw[← hg]
  rfl
 have hK:Qdc p H K=K.map ZH:=sup_eq_left.mpr hle
 rw [Qav, ← MonoidHom.comap_ker,QuotientGroup.ker_mk',hK,Subgroup.comap_map_eq,
   Abelianization.ker_of,sup_eq_left.mpr h1]
lemma Qfd {K:Subgroup H} (h1:commutator H≤K) (h2:∀ g:H,g^p∈K):
    ZB (Q32 p H K)=K.index:=by
 have e:=Nat.card_congr
   (QuotientGroup.quotientKerEquivOfSurjective (Qav p H K) (Q3e K)).toEquiv
 rw[Qbi h1 h2]at e
 exact e.symm
variable [hp:Fact p.Prime]
lemma Qk2 (K:Subgroup H) (x:Additive (Q32 p H K)):p•x =0:=by
 show ZE (Additive.toMul x^p)=ZE 1
 rw[Qhy]
instance Qnr (K:Subgroup H):Module (ZMod p) (Additive (Q32 p H K)):=
  letI:NeZero p:=⟨hp.out.ne_zero⟩
  AddCommGroup.zmodModule (Qk2 K)
lemma Q3v (K:Subgroup H) (c:ZMod p) (x:Additive (Q32 p H K)):
    c•x = c.val•x:=by
 have:NeZero p:=⟨hp.out.ne_zero⟩
 conv_lhs=>rw[← ZMod.natCast_zmod_val c]
 exact Nat.cast_smul_eq_nsmul (ZMod p) c.val x
lemma Q3j [Finite H] (K:Subgroup H):
    ZB (Q32 p H K)=p^Module.finrank (ZMod p) (Additive (Q32 p H K)):=by
 have:Finite (Q32 p H K):=Finite.of_surjective _ (Q3e K)
 have:Finite (Additive (Q32 p H K)):=inferInstance
 have:Module.Free (ZMod p) (Additive (Q32 p H K)):=
   Module.Free.of_divisionRing (ZMod p) (Additive (Q32 p H K))
 have:Module.Finite (ZMod p) (Additive (Q32 p H K)):=inferInstance
 have h:=Module.natCard_eq_pow_finrank (K:=ZMod p) (V:=Additive (Q32 p H K))
 rw[Nat.card_zmod]at h
 exact h
end Q32
section Frame0
variable (p:ℕ) (G:Type u) [Group G]
abbrev VQ:Type u:=Q32 p G (Qv p G)
abbrev WQ:Type u:=Q32 p (lcs G 1) ((pN p G).subgroupOf (lcs G 1))
def Q29:G→*VQ p G:=Qav p G (Qv p G)
def Q3o:lcs G 1→*WQ p G:=Qav p (lcs G 1) ((pN p G).subgroupOf (lcs G 1))
def cw {G:Type u} [Group G] (g h:G):lcs G 1:=⟨⁅g,h⁆,Qo g h⟩
variable {p G}
lemma Q1h:Function.Surjective (Q29 p G):=Q3e _
lemma Q4i:Function.Surjective (Q3o p G):=Q3e _
lemma Q84:commutator G≤Qv p G:=le_sup_right
lemma Q4f:
    commutator (lcs G 1)≤(pN p G).subgroupOf (lcs G 1):=by
 rw[commutator_def,Subgroup.commutator_le]
 intro a _ b _
 rw[Subgroup.mem_subgroupOf]
 show ⁅(a:G),(b:G)⁆∈pN p G
 exact Q1j p (Qb (n:=1) a.2 (b:G))
lemma Q4h (g:lcs G 1):g^p∈(pN p G).subgroupOf (lcs G 1):=by
 rw[Subgroup.mem_subgroupOf]
 have e:((g^p:lcs G 1):G)=(g:G)^p:=map_pow (lcs G 1).subtype g p
 rw[e]
 exact ZL (ZC ⟨g,rfl⟩)
lemma Qka:(Q29 p G).ker=Qv p G:=
  Qbi Q84 (Q2c p)
lemma Qhi:(Q3o p G).ker=(pN p G).subgroupOf (lcs G 1):=
  Qbi Q4f Q4h
lemma Qg1 {g g':G}:Q29 p G g=Q29 p G g'↔g*g'⁻¹∈Qv p G:=by
 rw[← mul_inv_eq_one, ← map_inv, ← map_mul, ← MonoidHom.mem_ker,Qka]
lemma Qck {a b:lcs G 1} (h:(a:G)*(b:G)⁻¹∈pN p G):
    Q3o p G a=Q3o p G b:=by
 have hk:a*b⁻¹∈(Q3o p G).ker :=by
  rw[Qhi,Subgroup.mem_subgroupOf]
  exact h
 rw[MonoidHom.mem_ker,map_mul,map_inv,mul_inv_eq_one]at hk
 exact hk
lemma Q8c {a:lcs G 1} (h:(a:G)∈pN p G):Q3o p G a=1:=by
 rw[← MonoidHom.mem_ker,Qhi,Subgroup.mem_subgroupOf]
 exact h
lemma Qn5 (w:WQ p G):w^p=1:=Qhy _ w
lemma Q9x:ZB (VQ p G)=(Qv p G).index:=
  Qfd Q84 (Q2c p)
lemma Q9k:ZB (WQ p G)=((pN p G).subgroupOf (lcs G 1)).index:=
  Qfd Q4f Q4h
noncomputable def Q61 (v:VQ p G):G:=Function.surjInv Q1h v
lemma Qcr (v:VQ p G):Q29 p G (Q61 v)=v:=Function.surjInv_eq Q1h v
noncomputable def Q4b (v w:VQ p G):WQ p G:=Q3o p G (cw (Q61 v) (Q61 w))
lemma Q5i (g h:G):Q4b (Q29 p G g) (Q29 p G h)=Q3o p G (cw g h):=by
 show Q3o p G (cw (Q61 (Q29 p G g)) (Q61 (Q29 p G h)))=Q3o p G (cw g h)
 apply Qck
 have hg:Q61 (Q29 p G g)*g⁻¹∈Qv p G:=Qg1.mp (Qcr _)
 have hh:Q61 (Q29 p G h)*h⁻¹∈Qv p G:=Qg1.mp (Qcr _)
 have e1:=Q8u p g (Q61 (Q29 p G g)) (Q61 (Q29 p G h)) hg
 have e2:=Qdr p g h (Q61 (Q29 p G h)) hh
 have e3:=Subgroup.mul_mem _ e1 e2
 rw[mul_assoc,inv_mul_cancel_left]at e3
 exact e3
lemma Qio (v v' w:VQ p G):Q4b (v*v') w=Q4b v w*Q4b v' w:=by
 obtain ⟨g,rfl⟩:=Q1h v
 obtain ⟨g',rfl⟩:=Q1h v'
 obtain ⟨h,rfl⟩:=Q1h w
 have e:Q29 p G g*Q29 p G g'=Q29 p G (g*g'):=(map_mul _ _ _).symm
 rw[e,Q5i,Q5i,Q5i, ← map_mul]
 apply Qck
 exact Qdt p g g' h
lemma Qh5 (v w w':VQ p G):Q4b v (w*w')=Q4b v w*Q4b v w':=by
 obtain ⟨g,rfl⟩:=Q1h v
 obtain ⟨h,rfl⟩:=Q1h w
 obtain ⟨h',rfl⟩:=Q1h w'
 have e:Q29 p G h*Q29 p G h'=Q29 p G (h*h'):=(map_mul _ _ _).symm
 rw[e,Q5i,Q5i,Q5i, ← map_mul]
 apply Qck
 exact Qd8 p g h h'
lemma Qme (v:VQ p G):Q4b v v=1:=by
 obtain ⟨g,rfl⟩:=Q1h v
 have e:cw g g=1:=Subtype.ext (commutatorElement_self g)
 rw[Q5i,e,map_one]
lemma Qj5:
    ZA (ZG (fun vw:VQ p G×VQ p G=>Q4b vw.1 vw.2))=⊤:=by
  have h1:ZA (ZG (fun xy:G×G=> ⁅xy.1,xy.2⁆))≤
      ((ZA (ZG (fun vw:VQ p G×VQ p G=>Q4b vw.1 vw.2))).comap
        (Q3o p G)).map (lcs G 1).subtype:=by
    rw[ZD]
    rintro _ ⟨⟨x,y⟩,rfl⟩
    refine Subgroup.mem_map.mpr ⟨cw x y,?_,rfl⟩
    rw[Subgroup.mem_comap, ← Q5i]
    exact ZC ⟨(Q29 p G x,Q29 p G y),rfl⟩
  have h2:pN p G≤
      ((ZA (ZG (fun vw:VQ p G×VQ p G=>Q4b vw.1 vw.2))).comap
        (Q3o p G)).map (lcs G 1).subtype:=by
    intro n hn
    refine Subgroup.mem_map.mpr ⟨⟨n,Q3y p hn⟩,?_,rfl⟩
    rw[Subgroup.mem_comap,Q8c (a:=⟨n,Q3y p hn⟩) hn]
    exact Subgroup.one_mem _
  have h3:=(Qi2 (G:=G) p).trans (sup_le h1 h2)
  rw[eq_top_iff]
  intro w _
  obtain ⟨a,rfl⟩:=Q4i w
  obtain ⟨b,hb,hba⟩:=Subgroup.mem_map.mp (h3 a.2)
  have e:b=a:=Subtype.ext hba
  rw[← e]
  exact hb
section Lin
variable [hp:Fact p.Prime]
noncomputable def Q4g (v w:Additive (VQ p G)):Additive (WQ p G):=
  ZE (Q4b (Additive.toMul v) (Additive.toMul w))
lemma Q9h (v v' w:Additive (VQ p G)):
    Q4g (v+v') w=Q4g v w+Q4g v' w:=by
 show ZE (Q4b (Additive.toMul v*Additive.toMul v') (Additive.toMul w))=
   ZE (Q4b (Additive.toMul v) (Additive.toMul w)*
     Q4b (Additive.toMul v') (Additive.toMul w))
 rw[Qio]
lemma Q93 (v w w':Additive (VQ p G)):
    Q4g v (w+w')=Q4g v w+Q4g v w':=by
 show ZE (Q4b (Additive.toMul v) (Additive.toMul w*Additive.toMul w'))=
   ZE (Q4b (Additive.toMul v) (Additive.toMul w)*
     Q4b (Additive.toMul v) (Additive.toMul w'))
 rw[Qh5]
lemma Qee (c:ZMod p) (v w:Additive (VQ p G)):
    Q4g (c•v) w= c•Q4g v w:=by
 rw[Q3v,Q3v]
 exact map_nsmul (AddMonoidHom.mk' (fun v=>Q4g v w) (fun a b=>Q9h a b w))
   c.val v
lemma Qdj (c:ZMod p) (v w:Additive (VQ p G)):
    Q4g v (c•w)= c•Q4g v w:=by
 rw[Q3v,Q3v]
 exact map_nsmul (AddMonoidHom.mk' (fun w=>Q4g v w) (fun a b=>Q93 v a b))
   c.val w
noncomputable def Q2l:
    Additive (VQ p G)→ₗ[ZMod p] Additive (VQ p G)→ₗ[ZMod p] Additive (WQ p G):=
  LinearMap.mk₂ (ZMod p) Q4g Q9h Qee Q93
    Qdj
lemma Qct (v w:Additive (VQ p G)):
    Q2l v w=ZE (Q4b (Additive.toMul v) (Additive.toMul w)):=rfl
lemma Qd4 (g h:G):
    Q2l (ZE (Q29 p G g)) (ZE (Q29 p G h))=
      ZE (Q3o p G (cw g h)):=by
 rw[Qct]
 exact congrArg ZE (Q5i g h)
lemma Qjq (v:Additive (VQ p G)):Q2l v v=0:=by
 rw[Qct,Qme]
 rfl
lemma Qk0:
    Submodule.span (ZMod p)
      (ZG (fun vw:Additive (VQ p G)×Additive (VQ p G)=>Q2l vw.1 vw.2))=⊤:=by
  let T:Submodule (ZMod p) (Additive (WQ p G)):=Submodule.span (ZMod p)
    (ZG (fun vw:Additive (VQ p G)×Additive (VQ p G)=>Q2l vw.1 vw.2))
  let K :Subgroup (WQ p G):=
    { carrier :={w | ZE w∈T}
      mul_mem':= fun {a b} ha hb=>by
        have ha':ZE a∈T:=ha
        have hb':ZE b∈T:=hb
        exact Submodule.add_mem T ha' hb'
      one_mem':=by
        have h0:(0:Additive (WQ p G))∈T:=Submodule.zero_mem T
        exact h0
      inv_mem':= fun {a} ha=>by
        have ha':ZE a∈T:=ha
        have h1: - ZE a∈T:=Submodule.neg_mem T ha'
        exact h1 }
  have hle:ZA (ZG (fun vw:VQ p G×VQ p G=>Q4b vw.1 vw.2))≤K:=by
    rw[ZD]
    rintro _ ⟨⟨v,w⟩,rfl⟩
    show ZE (Q4b v w)∈Submodule.span (ZMod p)
      (ZG (fun vw:Additive (VQ p G)×Additive (VQ p G)=>Q2l vw.1 vw.2))
    exact Submodule.subset_span ⟨(ZE v,ZE w),rfl⟩
  rw[eq_top_iff]
  intro x _
  have hx:Additive.toMul x∈K:=hle (by rw[Qj5]; exact ZM _)
  exact hx
noncomputable def r2 (p:ℕ) [Fact p.Prime] (G:Type u) [Group G]:ℕ:=
  Module.finrank (ZMod p) (Additive (WQ p G))
end Lin
end Frame0
section Frame
variable {p:ℕ} [hp:Fact p.Prime] {G:Type u} [Group G] [Finite G]
lemma Q4c {a b:ℕ} (hp2:2≤p) (h:p^a≤p^b):a≤b:=by
 by_contra hc
 push_neg at hc
 have h1:p^(b+1)≤p^a:=Nat.pow_le_pow_right (by omega) hc
 have h2:0<p^b:=Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))
 rw[pow_succ]at h1
 nlinarith
lemma Qlq (hG:IsPGroup p G):ZB (VQ p G)=p^Group.rank G:=by
 rw[Q9x]
 exact Q5j hG
lemma Qls (hG:IsPGroup p G):
    Module.finrank (ZMod p) (Additive (VQ p G))=Group.rank G:=by
 have h1:=Q3j (p:=p) (Qv p G)
 rw[Qlq hG]at h1
 exact (Nat.pow_right_injective hp.out.two_le h1).symm
lemma Qlp:ZB (WQ p G)=p^r2 p G:=
  Q3j _
lemma Q9l:ZB (lcs G 1)=ZB (pN p G)*p^r2 p G:=by
 have h1:=Subgroup.card_mul_index ((pN p G).subgroupOf (lcs G 1))
 have h2:=Nat.card_congr (Subgroup.subgroupOfEquivOfLe (Q3y (G:=G) p)).toEquiv
 have h3:((pN p G).subgroupOf (lcs G 1)).index =p^r2 p G:=by
  rw[← Qlp (p:=p) (G:=G)]
  exact Q9k.symm
 rw[h3,h2]at h1
 exact h1.symm
lemma Qcb:
    (Qv p (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1))).comap
      (ZF ((lcs G 2).subgroupOf (lcs G 1)))=(pN p G).subgroupOf (lcs G 1):=by
 have hKN:(lcs G 2).subgroupOf (lcs G 1)≤(pN p G).subgroupOf (lcs G 1):=by
  intro a ha
  rw[Subgroup.mem_subgroupOf]at ha⊢
  exact Q1j p ha
 apply le_antisymm
 · have h1:Qv p (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1))≤
       ((pN p G).subgroupOf (lcs G 1)).map
         (ZF ((lcs G 2).subgroupOf (lcs G 1))):=by
     refine sup_le ?_ ?_
     · rw[ZD]
       rintro _ ⟨q,rfl⟩
       obtain ⟨a,rfl⟩:=QuotientGroup.mk'_surjective ((lcs G 2).subgroupOf (lcs G 1)) q
       exact Subgroup.mem_map.mpr ⟨a^p,Q4h a,map_pow _ a p⟩
     · rw [commutator_def,Subgroup.commutator_le]
       intro q1 _ q2 _
       obtain ⟨a,rfl⟩:=QuotientGroup.mk'_surjective ((lcs G 2).subgroupOf (lcs G 1)) q1
       obtain ⟨b,rfl⟩:=QuotientGroup.mk'_surjective ((lcs G 2).subgroupOf (lcs G 1)) q2
       refine Subgroup.mem_map.mpr ⟨⁅a,b⁆,?_,map_commutatorElement _ a b⟩
       exact Q4f
         (Subgroup.commutator_mem_commutator (ZM a) (ZM b))
   refine (Subgroup.comap_mono h1).trans ?_
   rw[Subgroup.comap_map_eq,QuotientGroup.ker_mk']
   exact sup_le le_rfl hKN
 · intro a ha
   rw[Subgroup.mem_subgroupOf]at ha
   have h2:pN p G≤((Qv p (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1))).comap
       (ZF ((lcs G 2).subgroupOf (lcs G 1)))).map (lcs G 1).subtype:=by
    refine sup_le ?_ ?_
    · intro n hn
      have hn1:n∈lcs G 1:=Qd (by norm_num) hn
      refine Subgroup.mem_map.mpr ⟨⟨n,hn1⟩,?_,rfl⟩
      rw[Subgroup.mem_comap]
      have e:ZF ((lcs G 2).subgroupOf (lcs G 1)) ⟨n,hn1⟩=1:=by
       rw[QuotientGroup.mk'_apply,QuotientGroup.eq_one_iff,Subgroup.mem_subgroupOf]
       exact hn
      rw[e]
      exact Subgroup.one_mem _
    · rw[ZD]
      rintro _ ⟨g,rfl⟩
      refine Subgroup.mem_map.mpr ⟨g^p,?_,map_pow (lcs G 1).subtype g p⟩
      rw[Subgroup.mem_comap,map_pow]
      exact Q2c p _
   obtain ⟨b,hb,hba⟩:=Subgroup.mem_map.mp (h2 ha)
   have e:b=a:=Subtype.ext hba
   rw[← e]
   exact hb
lemma Q4x (hG:IsPGroup p G):
    Group.rank (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1))=r2 p G:=by
 have hQ:IsPGroup p (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1)):=
   (hG.to_subgroup (lcs G 1)).to_quotient _
 have h1:(Qv p (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1))).index =
     p^Group.rank (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1)):=Q5j hQ
 have h2:((pN p G).subgroupOf (lcs G 1)).index =p^r2 p G:=by
  rw[← Q9k,Qlp]
 rw [← Qcb,Subgroup.index_comap_of_surjective _
   (QuotientGroup.mk'_surjective _),h1]at h2
 exact Nat.pow_right_injective hp.out.two_le h2
lemma Qmd (hG:IsPGroup p G):lcs G 1≤frattini G:=by
 rw[Q1n hG, ← Q1s (G:=G)]
 exact le_sup_right
lemma Qis (hG:IsPGroup p G) (H:Subgroup G):
    lcs G 1≤⁅H,H⁆⊔pN p G↔⁅H,H⁆⊔lcs G 2=lcs G 1:=by
 have hHH:⁅H,H⁆≤lcs G 1:=Subgroup.commutator_mono le_top le_top
 have h21:lcs G 2≤lcs G 1:=Qd (by norm_num)
 constructor
 · intro h
   refine le_antisymm (sup_le hHH h21) ?_
   have hP:IsPGroup p (lcs G 1):=hG.to_subgroup (lcs G 1)
   have hS:lcs G 1≤((⁅H,H⁆⊔lcs G 2).subgroupOf (lcs G 1)⊔
       frattini (lcs G 1)).map (lcs G 1).subtype:=by
    rw[Q1n hP]
    refine h.trans (sup_le ?_ (sup_le ?_ ?_))
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨⟨x,hHH hx⟩,ZJ ?_,rfl⟩
      rw[Subgroup.mem_subgroupOf]
      exact ZJ hx
    · intro x hx
      refine Subgroup.mem_map.mpr ⟨⟨x,h21 hx⟩,ZJ ?_,rfl⟩
      rw[Subgroup.mem_subgroupOf]
      exact ZL hx
    · rw [ZD]
      rintro _ ⟨g,rfl⟩
      exact Subgroup.mem_map.mpr ⟨g^p,ZL (Q2c p g),
        map_pow (lcs G 1).subtype g p⟩
   have hL:(⁅H,H⁆⊔lcs G 2).subgroupOf (lcs G 1)⊔frattini (lcs G 1)=⊤:=by
    rw[eq_top_iff]
    intro a _
    obtain ⟨b,hb,hba⟩:=Subgroup.mem_map.mp (hS a.2)
    have e:b=a:=Subtype.ext hba
    rw[← e]
    exact hb
   have hLt:(⁅H,H⁆⊔lcs G 2).subgroupOf (lcs G 1)=⊤:=by
    have h3:=Q25
      (s :=(((⁅H,H⁆⊔lcs G 2).subgroupOf (lcs G 1):Subgroup (lcs G 1)):
        Set (lcs G 1))) (by rw[Subgroup.closure_eq]; exact hL)
    rwa[Subgroup.closure_eq]at h3
   intro x hx
   have hmem:(⟨x,hx⟩:lcs G 1)∈(⁅H,H⁆⊔lcs G 2).subgroupOf (lcs G 1):=by
    rw[hLt]
    exact ZM _
   exact Subgroup.mem_subgroupOf.mp hmem
 · intro h
   calc lcs G 1=⁅H,H⁆⊔lcs G 2:=h.symm
     _≤⁅H,H⁆⊔pN p G:=sup_le_sup_left (Q1j p) _
lemma Qch (T:Finset G):∃ x:ℕ→G,x '' ZP T.card=(T:Set G):=by
 refine ⟨fun i=>if h:i<T.card then ((T.equivFin.symm ⟨i,h⟩:T):G) else 1,?_⟩
 ext y
 constructor
 · rintro ⟨i,hi,rfl⟩
   have hi':i<T.card:=hi
   dsimp only
   rw[dif_pos hi']
   exact (T.equivFin.symm ⟨i,hi'⟩).2
 · intro hy
   have hj:=(T.equivFin ⟨y,hy⟩).2
   refine ⟨(T.equivFin ⟨y,hy⟩:ℕ),hj,?_⟩
   dsimp only
   rw[dif_pos hj,Fin.eta,Equiv.symm_apply_apply]
lemma Qc4 (H:Subgroup G):
    ∃ x:ℕ→G,ZA (x '' ZP (Group.rank H))=H:=by
 classical
 obtain ⟨T,hTc,hTg⟩:=Group.rank_spec H
 have hcard:(T.image Subtype.val).card=Group.rank H:=by
  rw[Finset.card_image_of_injective T Subtype.val_injective,hTc]
 obtain ⟨x,hx⟩:=Qch (T.image Subtype.val)
 refine ⟨x,?_⟩
 rw[← hcard,hx]
 apply le_antisymm
 · rw[ZD]
   intro y hy
   obtain ⟨z, -,rfl⟩:=Finset.mem_image.mp hy
   exact z.2
 · intro h hh
   have h1:ZA (T:Set H)≤
       (ZA ((T.image Subtype.val:Finset G):Set G)).comap H.subtype:=by
    rw[ZD]
    intro z hz
    exact ZC (Finset.mem_coe.mpr (Finset.mem_image_of_mem Subtype.val hz))
   have h2:(⟨h,hh⟩:H)∈ZA (T:Set H):=by
    rw[hTg]
    exact ZM _
   exact h1 h2
lemma Q8k (v:ℕ→G) (t:ℕ):
    Group.rank (ZA (v '' ZP t))≤t:=by
 classical
 have e:v '' ZP t=(((ZQ t).image v:Finset G):Set G):=by
  rw[Finset.coe_image,Finset.coe_range]
 rw[Subgroup.rank_congr (congrArg ZA e)]
 exact (Subgroup.rank_closure_finset_le_card _).trans
   (Finset.card_image_le.trans (Finset.card_range t).le)
noncomputable def s1 (p:ℕ) (G:Type u) [Group G]:ℕ:=Nat.log p (lcs G 1).index
noncomputable def Q3p (p:ℕ) (G:Type u) [Group G] [Finite G]:ℕ:=
  s1 p G - Group.rank G
lemma Q5o (hG:IsPGroup p G):(lcs G 1).index =p^s1 p G:=by
 obtain ⟨n,hn⟩:=IsPGroup.iff_card.mp hG
 have hd:(lcs G 1).index∣p^n:=by
  rw[← hn]
  exact Subgroup.index_dvd_card (lcs G 1)
 obtain ⟨k, -,hk⟩:=(Nat.dvd_prime_pow hp.out).mp hd
 rw[s1,hk,Nat.log_pow hp.out.one_lt]
lemma Qkk (hG:IsPGroup p G):Group.rank G≤ s1 p G:=by
 have hd:(frattini G).index∣(lcs G 1).index:=Subgroup.index_dvd_of_le (Qmd hG)
 have hi:(frattini G).index =p^Group.rank G:=Q44 hG
 rw[hi,Q5o hG]at hd
 exact Q4c hp.out.two_le
   (Nat.le_of_dvd (Nat.pos_of_ne_zero (pow_ne_zero _ hp.out.ne_zero)) hd)
lemma Q4o (hG:IsPGroup p G):
    (lcs G 1).index =p^(Group.rank G+Q3p p G):=by
 rw[Q5o hG,Q3p,Nat.add_sub_of_le (Qkk hG)]
end Frame
end OMA.SimsLite
namespace OMA.SimsLite.Alt2
open Module
universe u
section Bridge
variable {p:ℕ} [hp:Fact p.Prime] {G:Type u} [Group G]
def Qja (H:Subgroup G):AddSubgroup (Additive (VQ p G)) where
  carrier :={x | ∃ h∈H,ZE (Q29 p G h)=x}
  add_mem':=by
    rintro _ _ ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
    exact ⟨a*b,H.mul_mem ha hb,by rw[map_mul]; rfl⟩
  zero_mem':=⟨1,H.one_mem,by rw[map_one]; rfl⟩
  neg_mem':=by
    rintro _ ⟨a,ha,rfl⟩
    exact ⟨a⁻¹,H.inv_mem ha,by rw[map_inv]; rfl⟩
def Qlz (K:Subgroup G):AddSubgroup (Additive (WQ p G)) where
  carrier :={w | ∃ a:lcs G 1,(a:G)∈K∧ZE (Q3o p G a)=w}
  add_mem':=by
    rintro _ _ ⟨a,ha,rfl⟩ ⟨b,hb,rfl⟩
    exact ⟨a*b,K.mul_mem ha hb,by rw[map_mul]; rfl⟩
  zero_mem':=⟨1,K.one_mem,by rw[map_one]; rfl⟩
  neg_mem':=by
    rintro _ ⟨a,ha,rfl⟩
    exact ⟨a⁻¹,K.inv_mem ha,by rw[map_inv]; rfl⟩
def Qnx (U:Submodule (ZMod p) (Additive (VQ p G))):Subgroup G where
  carrier :={g | ZE (Q29 p G g)∈U}
  mul_mem':=by
    intro a b ha hb
    show ZE (Q29 p G (a*b))∈U
    rw[map_mul]
    exact U.add_mem ha hb
  one_mem':=by
    show ZE (Q29 p G 1)∈U
    rw[map_one]
    exact U.zero_mem
  inv_mem':=by
    intro a ha
    show ZE (Q29 p G a⁻¹)∈U
    rw[map_inv]
    exact U.neg_mem ha
def Qny (S:Submodule (ZMod p) (Additive (WQ p G))):Subgroup G where
  carrier :={g | ∃ hg:g∈lcs G 1,ZE (Q3o p G ⟨g,hg⟩)∈S}
  mul_mem':=by
    rintro a b ⟨ha,hSa⟩ ⟨hb,hSb⟩
    refine ⟨(lcs G 1).mul_mem ha hb,?_⟩
    show ZE (Q3o p G (⟨a,ha⟩*⟨b,hb⟩))∈S
    rw[map_mul]
    exact S.add_mem hSa hSb
  one_mem':=by
    refine ⟨(lcs G 1).one_mem,?_⟩
    show ZE (Q3o p G 1)∈S
    rw[map_one]
    exact S.zero_mem
  inv_mem':=by
    rintro a ⟨ha,hSa⟩
    refine ⟨(lcs G 1).inv_mem ha,?_⟩
    show ZE (Q3o p G (⟨a,ha⟩⁻¹))∈S
    rw[map_inv]
    exact S.neg_mem hSa
lemma Qge {k:ℕ} (u:Fin k→G)
    (hcore:lcs G 1≤⁅ZA (ZG u),ZA (ZG u)⁆⊔
      lcs G 2):
    Q4q (Q2l (p:=p) (G:=G))
      (Submodule.span (ZMod p) (ZG (fun i=>ZE (Q29 p G (u i))))):=by
  set U:=Submodule.span (ZMod p) (ZG (fun i=>ZE (Q29 p G (u i))))
  set S:=Submodule.span (ZMod p) {w | ∃ x∈U,∃ y∈U,w=Q2l (p:=p) (G:=G) x y}
  have hHU:ZA (ZG u)≤Qnx U:=by
   rw[ZD]
   rintro _ ⟨i,rfl⟩
   exact Submodule.subset_span ⟨i,rfl⟩
  have hle:⁅ZA (ZG u),ZA (ZG u)⁆⊔lcs G 2≤
      Qny S:=by
   refine sup_le ?_ ?_
   · rw [Subgroup.commutator_le]
     intro g hg h hh
     refine ⟨Qo g h,?_⟩
     show ZE (Q3o p G (cw g h))∈S
     rw[← Qd4]
     exact Submodule.subset_span ⟨ZE (Q29 p G g),hHU hg,
       ZE (Q29 p G h),hHU hh,rfl⟩
   · intro g hg
     have hg1:g∈lcs G 1:=(Q1j p).trans (Q3y p) hg
     refine ⟨hg1,?_⟩
     rw[Q8c (a:=⟨g,hg1⟩) (Q1j p hg)]
     exact S.zero_mem
  show S=⊤
  rw[eq_top_iff]
  intro w _
  obtain ⟨a,ha⟩:=Q4i (p:=p) (G:=G) (Additive.toMul w)
  obtain ⟨h,hS⟩:=hle (hcore a.2)
  have e:w=ZE (Q3o p G a):=by
   rw[ha]
   rfl
  rw[e]
  exact hS
lemma Qaf [Finite G] (hG:IsPGroup p G) {d:ℕ}
    (v:Fin d→ Additive (VQ p G))
    (hU:Q4q (Q2l (p:=p) (G:=G)) (Submodule.span (ZMod p) (ZG v))):
    Qt G≤d:=by
 set U:=Submodule.span (ZMod p) (ZG v)
 set x:Fin d→G:= fun i=>Q61 (Additive.toMul (v i))
 set H:=ZA (ZG x)
 set K:=⁅H,H⁆⊔pN p G
 have hUP:U≤AddSubgroup.toZModSubmodule p (Qja (p:=p) H):=by
  rw[Submodule.span_le]
  rintro _ ⟨i,rfl⟩
  refine ⟨x i,ZC ⟨i,rfl⟩,?_⟩
  show ZE (Q29 p G (Q61 (Additive.toMul (v i))))=v i
  rw[Qcr]
  rfl
 have hT:(⊤:Submodule (ZMod p) (Additive (WQ p G)))≤
     AddSubgroup.toZModSubmodule p (Qlz (p:=p) K):=by
  unfold Q4q at hU
  rw[← hU,Submodule.span_le]
  rintro _ ⟨a,ha,b,hb,rfl⟩
  have ha':a∈Qja (p:=p) H:=hUP ha
  have hb':b∈Qja (p:=p) H:=hUP hb
  obtain ⟨g,hg,rfl⟩:=ha'
  obtain ⟨h,hh,rfl⟩:=hb'
  exact ⟨cw g h,ZJ (Subgroup.commutator_mem_commutator hg hh),
    (Qd4 g h).symm⟩
 have hcore:lcs G 1≤K:=by
  intro g hg
  have hw:ZE (Q3o p G ⟨g,hg⟩)∈Qlz (p:=p) K:=
    hT Submodule.mem_top
  obtain ⟨a,haK,heq⟩:=hw
  have heq':Q3o p G a=Q3o p G ⟨g,hg⟩:= congrArg Additive.toMul heq
  have hk:(⟨g,hg⟩*a⁻¹:lcs G 1)∈(Q3o p G).ker :=by
   rw[MonoidHom.mem_ker,map_mul,map_inv, ← heq',mul_inv_cancel]
  rw[Qhi,Subgroup.mem_subgroupOf]at hk
  have hk':g*(a:G)⁻¹∈pN p G:=hk
  have e:g=g*(a:G)⁻¹*a:=by group
  rw[e]
  exact K.mul_mem (ZL hk') haK
 apply Nat.sInf_le
 exact ⟨x,((Qis hG H).1 hcore).ge⟩
lemma Q80:Q4q (Q2l (p:=p) (G:=G)) ⊤:=by
 have e :ZG (fun vw:Additive (VQ p G)×Additive (VQ p G)=>Q2l vw.1 vw.2)=
     {w | ∃ x∈(⊤:Submodule (ZMod p) (Additive (VQ p G))),
       ∃ y∈(⊤:Submodule (ZMod p) (Additive (VQ p G))),w=Q2l (p:=p) (G:=G) x y}:=by
   ext w
   constructor
   · rintro ⟨⟨x,y⟩,rfl⟩
     exact ⟨x,Submodule.mem_top,y,Submodule.mem_top,rfl⟩
   · rintro ⟨x, -,y, -,rfl⟩
     exact ⟨(x,y),rfl⟩
 have h:=Qk0 (p:=p) (G:=G)
 rw[e]at h
 exact h
lemma Qgk [Finite G] (U:Submodule (ZMod p) (Additive (VQ p G))):
    ∃ v:Fin (finrank (ZMod p) U)→ Additive (VQ p G),Submodule.span (ZMod p) (ZG v)=U:=by
 have:Finite (VQ p G):=Finite.of_surjective _ Q1h
 have:Finite (Additive (VQ p G)):=inferInstance
 have:Finite U:=inferInstance
 have:Module.Finite (ZMod p) U:=inferInstance
 let B:=Module.finBasisOfFinrankEq (ZMod p) U rfl
 refine ⟨fun i=> (B i:Additive (VQ p G)),?_⟩
 have h:= congrArg (Submodule.map U.subtype) B.span_eq
 rw[Submodule.map_span,Submodule.map_subtype_top, ← Set.range_comp]at h
 exact h
lemma Qez [Finite G] (hG:IsPGroup p G):
    Q9r (Q2l (p:=p) (G:=G))=Qt G:=by
 apply le_antisymm
 · have hne:{k | ∃ u:Fin k→G,
       lcs G 1≤⁅ZA (ZG u),ZA (ZG u)⁆⊔
         lcs G 2}.Nonempty:=by
     let e:Fin (ZB G)→G:=(Finite.equivFin G).symm
     have he:ZG e=Set.univ:=Equiv.range_eq_univ _
     refine ⟨ZB G,e,?_⟩
     rw[he,Subgroup.closure_univ]
     exact le_sup_left
   obtain ⟨u,hu⟩:=Nat.sInf_mem hne
   have hg:=Qge (p:=p) u hu
   have h1:Q9r (Q2l (p:=p) (G:=G))≤finrank (ZMod p)
       (Submodule.span (ZMod p) (ZG (fun i=>ZE (Q29 p G (u i))))):=
     Nat.sInf_le ⟨_,rfl,hg⟩
   have h2:finrank (ZMod p)
       (Submodule.span (ZMod p) (ZG (fun i=>ZE (Q29 p G (u i)))))≤
       Fintype.card (Fin (Qt G)):=
     finrank_range_le_card (fun i=>ZE (Q29 p G (u i)))
   rw[Fintype.card_fin]at h2
   exact h1.trans h2
 · have htop:Q4q (Q2l (p:=p) (G:=G)) ⊤:=Q80
   have hne:{d | ∃ U:Submodule (ZMod p) (Additive (VQ p G)),finrank (ZMod p) U=d∧
       Q4q (Q2l (p:=p) (G:=G)) U}.Nonempty:=⟨_,⊤,rfl,htop⟩
   obtain ⟨U,hU,hg⟩:=Nat.sInf_mem hne
   obtain ⟨v,hv⟩:=Qgk (p:=p) U
   rw[← hv]at hg
   have:=Qaf hG v hg
   exact this.trans hU.le
lemma Q75 [Finite G] (hG:IsPGroup p G) {r1 r2:ℕ}
    (bV:Basis (Fin r1) (ZMod p) (Additive (VQ p G)))
    (bW:Basis (Fin r2) (ZMod p) (Additive (WQ p G))):
    (∀ k,Q1y (Q3c (Q2l (p:=p) (G:=G)) bV bW k))∧
      Q1k (Q3c (Q2l (p:=p) (G:=G)) bV bW) ⊤∧
      Q2b (Q3c (Q2l (p:=p) (G:=G)) bV bW)=Qt G:=by
 refine ⟨Qgz _ (fun x =>Qjq (p:=p) (G:=G) x) bV bW,?_,?_⟩
 · rw[Q9d]
   exact Q80
 · rw[Qfn,Qez hG]
lemma Qaq [Finite G] (hG:IsPGroup p G):
    ∃ β:Fin (r2 p G)→Matrix (Fin (Group.rank G)) (Fin (Group.rank G)) (ZMod p),
      (∀ k,Q1y (β k))∧Q1k β ⊤∧Q2b β=Qt G:=by
 have:Finite (VQ p G):=Finite.of_surjective _ Q1h
 have:Finite (Additive (VQ p G)):=inferInstance
 have:Module.Finite (ZMod p) (Additive (VQ p G)):=inferInstance
 have:Finite (WQ p G):=Finite.of_surjective _ Q4i
 have:Finite (Additive (WQ p G)):=inferInstance
 have:Module.Finite (ZMod p) (Additive (WQ p G)):=inferInstance
 let bV:=Module.finBasisOfFinrankEq (ZMod p) (Additive (VQ p G)) (Qls (p:=p) (G:=G) hG)
 let bW:=Module.finBasisOfFinrankEq (ZMod p) (Additive (WQ p G)) (rfl:finrank (ZMod p)
   (Additive (WQ p G))=r2 p G)
 exact ⟨_,Q75 hG bV bW⟩
lemma Qf8 [Finite G] (hG:IsPGroup p G):
    Qt G≤ r2 p G+1∧r2 p G≤(Qt G).choose 2∧Qt G≤Group.rank G:=by
 obtain ⟨β,hA,hg,hs⟩:=Qaq hG
 refine ⟨?_,?_,?_⟩
 · rw[← hs]
   exact Qh3 β hg
 · rw[← hs]
   exact Qb5 β hA hg
 · rw[← hs]
   exact Qjw β hg
end Bridge
end OMA.SimsLite.Alt2
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section BrCount
lemma Qfm {α β:Type*} [Finite β] (S:Set α) (f:α→β) (M:ℕ)
    (hM:∀ b,(S∩f ⁻¹' {b}).ncard≤M):S.ncard≤ZB β *M:=by
 classical
 have:=Fintype.ofFinite β
 rcases S.finite_or_infinite with hS | hS
 · rw [Set.ncard_eq_toFinset_card S hS,
     Finset.card_eq_sum_card_fiberwise (f:= f) (t:=Finset.univ) (by intro x _; simp)]
   calc ∑ b : β,(hS.toFinset.filter (fun a=>f a=b)).card≤∑ _b:β,M:=by
         refine Finset.sum_le_sum fun b _=>?_
         have h1:((hS.toFinset.filter (fun a=>f a=b):Finset α):Set α)=
             S∩f ⁻¹' {b}:=by
           ext a
           simp
         rw[← Set.ncard_coe_finset,h1]
         exact hM b
     _=ZB β *M:=by simp
 · rw[hS.ncard]
   exact Nat.zero_le _
lemma Q2p {α β:Type*} (S:Set α) (f:α→β) (M:ℕ)
    (hM:∀ b,(S∩f ⁻¹' {b}).ncard≤M):S.ncard≤(f '' S).ncard*M:=by
 classical
 rcases S.finite_or_infinite with hS | hS
 · rw [Set.ncard_eq_toFinset_card S hS,Finset.card_eq_sum_card_image f hS.toFinset]
   have himg:(f '' S).ncard=(hS.toFinset.image f).card:=by
    rw[← Set.ncard_coe_finset,Finset.coe_image,Set.Finite.coe_toFinset]
   rw[himg]
   calc ∑ b ∈ hS.toFinset.image f,(hS.toFinset.filter (fun a=>f a=b)).card
       ≤ ∑ _b ∈hS.toFinset.image f,M:=by
         refine Finset.sum_le_sum fun b _=>?_
         have h1:((hS.toFinset.filter (fun a=>f a=b):Finset α):Set α)=
             S∩f ⁻¹' {b}:=by
           ext a
           simp
         rw[← Set.ncard_coe_finset,h1]
         exact hM b
     _=(hS.toFinset.image f).card*M:=by simp
 · rw[hS.ncard]
   exact Nat.zero_le _
lemma Q26 {α β:Type*} [Finite β] (S:Set α) (f:α→β)
    (hf:Set.InjOn f S):S.ncard≤ZB β:=by
 have h:=Set.ncard_le_ncard_of_injOn (t:=(Set.univ:Set β)) f
   (fun _ _=>Set.mem_univ _) hf
 rwa[Set.ncard_univ]at h
lemma Q28 {p a b:ℕ} (hp:1<p) (h:p^a≤p^b):a≤b:=by
 by_contra hc
 push_neg at hc
 have h1:p^(b+1)≤p^a:=Nat.pow_le_pow_right (by omega) hc
 have h2:0<p^b:=Nat.pos_of_ne_zero (pow_ne_zero _ (by omega))
 rw[pow_succ]at h1
 nlinarith
lemma Q8e {p n a c:ℕ} (hp:p.Prime) (ha:a∣p^n) (hc:c∣p^n)
    (hac:a∣c) (hne:a≠c):p*a≤ c:=by
 obtain ⟨i, -,rfl⟩:=(Nat.dvd_prime_pow hp).1 ha
 obtain ⟨j, -,rfl⟩:=(Nat.dvd_prime_pow hp).1 hc
 have hij:i≤j:=(Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hac
 have hij':i≠j:= fun h=>hne (by rw[h])
 rw[← pow_succ']
 exact Nat.pow_le_pow_right hp.pos (by omega)
lemma Qh1 {M N:Type*} [Group M] [Group N] [Finite M] {p s b:ℕ} (hp:p.Prime)
    (f:M→*N) (hM:ZB M=p^s) (hb:p^b≤ZB f.range):
    ZB f.ker≤p^(s - b):=by
 have h1:ZB f.ker*ZB f.range=p^s:=by
  have e:=Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
  rw[← e, ← hM]
  exact Subgroup.card_mul_index f.ker
 obtain ⟨k, -,hk⟩:=(Nat.dvd_prime_pow hp).1 (⟨_,h1.symm⟩:ZB f.ker∣p^s)
 obtain ⟨j, -,hj⟩:=(Nat.dvd_prime_pow hp).1
   (⟨ZB f.ker,by rw[mul_comm]; exact h1.symm⟩:ZB f.range∣p^s)
 rw[hk,hj, ← pow_add]at h1
 have hkj:k+j=s:=Nat.pow_right_injective hp.two_le h1
 rw[hj]at hb
 have hbj:b≤j:=Q28 hp.one_lt hb
 rw[hk]
 exact Nat.pow_le_pow_right hp.pos (by omega)
end BrCount
section BrSub
variable {L:Type*} [CommGroup L]
lemma Q7j [Finite L] (H K:Subgroup L):
    ZB ↥(H⊔K)≤ZB H*ZB K:=by
 rw[← Nat.card_prod]
 refine Nat.card_le_card_of_surjective
   (fun q:H×K=> (⟨(q.1:L)*q.2,Subgroup.mul_mem_sup q.1.2 q.2.2⟩:↥(H⊔K))) ?_
 rintro ⟨x,hx⟩
 obtain ⟨y,hy,z,hz,rfl⟩:=Subgroup.mem_sup.mp hx
 exact ⟨(⟨y,hy⟩,⟨z,hz⟩),rfl⟩
end BrSub
section BrSubCount
lemma Q5w {L:Type*} [Group L] [Finite L]:
    {H:Subgroup L | ZB H=1}.ncard≤1:=by
  have hsub:{H:Subgroup L | ZB H=1}⊆{⊥}:=by
    intro H hH
    exact Subgroup.eq_bot_of_card_eq H hH
  calc _≤({⊥}:Set (Subgroup L)).ncard:=Set.ncard_le_ncard hsub (Set.finite_singleton _)
    _=1:=Set.ncard_singleton _
lemma Q5u {L:Type*} [Group L] [Finite L] {p e b:ℕ} (hp:p.Prime)
    (hL:ZB L=p^e) (hb:e<b):{H:Subgroup L | ZB H=p^b}.ncard=0:=by
  have he:{H:Subgroup L | ZB H=p^b}= ∅ :=by
    ext H
    simp only[Set.mem_setOf_eq,Set.mem_empty_iff_false,iff_false]
    intro hH
    have h:=Subgroup.card_subgroup_dvd_card H
    rw[hH,hL]at h
    have:=(Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 h
    omega
  rw[he,Set.ncard_empty]
lemma Qbp {p:ℕ} (hp:p.Prime) (e:ℕ):
    ∀ (L:Type u) [CommGroup L] [Finite L],ZB L=p^e→∀ b:ℕ,
      {H:Subgroup L | ZB H=p^b}.ncard≤p^(b*(e+1 - b)):=by
  haveI:=Fact.mk hp
  induction e with
  | zero=>
    intro L _ _ hL b
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simpa using Q5w (L:=L)
    · rw[Q5u hp hL hb]
      exact Nat.zero_le _
  | succ e ih=>
    intro L _ _ hL b
    rcases Nat.eq_zero_or_pos b with rfl | hb0
    · simpa using Q5w (L:=L)
    rcases Nat.lt_or_ge (e+1) b with hbe | hbe
    · rw[Q5u hp hL hbe]
      exact Nat.zero_le _
    obtain ⟨c,rfl⟩:∃ c,b= c+1:=⟨b - 1,by omega⟩
    obtain ⟨d,rfl⟩:∃ d,e= c+d:=⟨e - c,by omega⟩
    classical
    haveI:Finite (Subgroup L):=
      Finite.of_injective (fun H:Subgroup L=> (H:Set L)) SetLike.coe_injective
    obtain ⟨M,hM⟩:=Sylow.exists_subgroup_card_pow_prime p
      (show p^(c+d)∣ZB L by rw[hL]; exact pow_dvd_pow p (Nat.le_succ _))
    haveI:Finite (Subgroup M):=
      Finite.of_injective (fun H:Subgroup M=> (H:Set M)) SetLike.coe_injective
    have hMi:M.index =p:=by
     have h:=Subgroup.card_mul_index M
     rw[hM,hL,pow_succ]at h
     exact Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) h
    have hMtop:M≠⊤:=by
     intro h
     rw[h,Subgroup.index_top]at hMi
     exact hp.one_lt.ne hMi
    obtain ⟨t,htM⟩:∃ t,t∉M:=by
     by_contra hne
     push_neg at hne
     exact hMtop (eq_top_iff.2 fun x _=>hne x)
    set S1:={H:Subgroup L | ZB H=p^(c+1)∧H≤M} with hS1
    set S2:={H:Subgroup L | ZB H=p^(c+1)∧¬ H≤M} with hS2
    have hsplit:{H:Subgroup L | ZB H=p^(c+1)}=S1∪S2:=by
      ext H
      simp only[hS1,hS2,Set.mem_union,Set.mem_setOf_eq]
      tauto
    have h1:S1.ncard≤p^((c+1)*(c+d+1 - (c+1))):=by
     refine le_trans ?_ (ih M hM (c+1))
     refine Set.ncard_le_ncard_of_injOn (fun H=>H.subgroupOf M) ?_ ?_ (Set.toFinite _)
     · rintro H ⟨hH,hHM⟩
       show ZB (H.subgroupOf M)=p^(c+1)
       rw[← hH]
       exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHM).toEquiv
     · rintro H ⟨-,hHM⟩ H' ⟨-,hH'M⟩ he
       have:=Subgroup.subgroupOf_inj.1 he
       rwa[inf_of_le_left hHM,inf_of_le_left hH'M]at this
    have hS2card:∀ H∈S2,ZB ↥(M⊓H)=p^c:=by
     rintro H ⟨hH,hHM⟩
     have hdvd:M.relIndex H∣p:=hMi▸Subgroup.relIndex_dvd_index_of_normal (H:=M) (K:=H)
     have hne:M.relIndex H≠1:= fun h1=>hHM (Subgroup.relIndex_eq_one.1 h1)
     have hrel:M.relIndex H=p:=((Nat.dvd_prime hp).1 hdvd).resolve_left hne
     have hc1:=Subgroup.card_mul_index (M⊓H)
     have hc2:=Subgroup.relIndex_mul_index (inf_le_right:M⊓H≤H)
     rw[Subgroup.inf_relIndex_right (H:=M) (K:=H),hrel]at hc2
     have hc3:=Subgroup.card_mul_index H
     rw[hH]at hc3
     rw[← hc2,hL]at hc1
     have hi:H.index≠0:=Subgroup.index_ne_zero_of_finite
     have e1:(ZB ↥(M⊓H)*p)*H.index =(p^c*p)*H.index:=by
      rw[← pow_succ,hc3,hL, ← hc1]
      ring
     have e2:=Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hi) e1
     exact Nat.eq_of_mul_eq_mul_right hp.pos e2
    have hex:∀ H∈S2,∃ y,y∈H∧t⁻¹*y∈M:=by
     rintro H ⟨hH,hHM⟩
     have hle:M≤H⊔M:=le_sup_right
     have hne:M≠H⊔M:= fun h=>hHM (le_sup_left.trans h.symm.le)
     have hcne:ZB M≠ZB ↥(H⊔M):= fun h=>
       hne (Subgroup.eq_of_le_of_card_ge hle h.symm.le)
     have hp1:=Q8e hp (n:= c+d+1)
       (by rw[← hL]; exact Subgroup.card_subgroup_dvd_card _)
       (by rw[← hL]; exact Subgroup.card_subgroup_dvd_card _) (Subgroup.card_dvd_of_le hle) hcne
     have htop:H⊔M=⊤:=by
      refine Subgroup.eq_of_le_of_card_ge le_top ?_
      rw[Subgroup.card_top,hL,pow_succ, ← hM,mul_comm]
      exact hp1
     have ht:t∈H⊔M:=by
      rw[htop]
      exact ZM t
     obtain ⟨y,hy,z,hz,hyz⟩:=Subgroup.mem_sup.1 ht
     refine ⟨y,hy,?_⟩
     have e:t⁻¹*y=z⁻¹:=by
      rw[← hyz]
      group
     rw[e]
     exact inv_mem hz
    let ch:Subgroup L→ L:= fun H=>Classical.epsilon (fun y=>y∈H∧t⁻¹*y∈M)
    have hch:∀ H∈S2,ch H∈H∧t⁻¹*ch H∈M:= fun H hH=>
      Classical.epsilon_spec (hex H hH)
    let f:Subgroup L→ Subgroup M:= fun H=> (M⊓H).subgroupOf M
    have hfib:∀ a:Subgroup M,(S2∩f ⁻¹' {a}).ncard≤p^d:=by
     intro a
     rcases (S2∩f ⁻¹' {a}).eq_empty_or_nonempty with he | ⟨H0,hH0,hH0a⟩
     · rw[he,Set.ncard_empty]
       exact Nat.zero_le _
     obtain ⟨K,hK⟩:∃ K:Subgroup L,K=M⊓H0:=⟨_,rfl⟩
     have hKc:ZB K=p^c:=by
      rw[hK]
      exact hS2card H0 hH0
     have hKM:K≤M:=by
      rw[hK]
      exact inf_le_left
     have hfK:∀ H∈S2∩f ⁻¹' {a},M⊓H=K:=by
      rintro H ⟨-,hHa⟩
      have e:f H= f H0:=(show f H=a from hHa).trans (show f H0=a from hH0a).symm
      have e2:=Subgroup.subgroupOf_inj.1 e
      rw[inf_of_le_left inf_le_left,inf_of_le_left inf_le_left]at e2
      rw[hK]
      exact e2
     have hmap:ZB ↥(M.map (ZF K))=p^d:=by
      have e:=Subgroup.relIndex_ker (K:=M) (f:=ZF K)
      rw[QuotientGroup.ker_mk']at e
      have hc2:=Subgroup.relIndex_mul_index hKM
      rw[e,hMi]at hc2
      have hc1:=Subgroup.card_mul_index K
      rw[hKc, ← hc2,hL]at hc1
      have h3:p^c*(ZB ↥(M.map (ZF K))*p)=p^c*(p^d*p):=by
       rw[hc1]
       ring
      exact Nat.eq_of_mul_eq_mul_right hp.pos (Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos c) h3)
     let Φ:Subgroup L→ L⧸K:= fun H=> ((t⁻¹*ch H:L):L⧸K)
     have hmaps:∀ H∈S2∩f ⁻¹' {a},
         Φ H∈((M.map (ZF K):Subgroup (L⧸K)):Set (L⧸K)):=by
      intro H hH
      exact Subgroup.mem_map.2 ⟨t⁻¹*ch H,(hch H hH.1).2,rfl⟩
     have hinj:Set.InjOn Φ (S2∩f ⁻¹' {a}):=by
      intro H hH H' hH' hΦ
      obtain ⟨hy1, -⟩:=hch H hH.1
      obtain ⟨hy1',hy2'⟩:=hch H' hH'.1
      have hcardH:ZB H=p^(c+1):=hH.1.1
      have hcardH':ZB H'=p^(c+1):=hH'.1.1
      have hKH:K≤H:=by
       rw[← hfK H hH]
       exact inf_le_right
      have hKH':K≤H':=by
       rw[← hfK H' hH']
       exact inf_le_right
      have hq:(ch H)⁻¹*ch H'∈K:=by
       have h0:=QuotientGroup.eq.1 hΦ
       have e:(t⁻¹*ch H)⁻¹*(t⁻¹*ch H')=(ch H)⁻¹*ch H':=by group
       rwa[e]at h0
      have hcH:ch H'∈H:=by
       have e:ch H'= ch H*((ch H)⁻¹*ch H'):=by group
       rw[e]
       exact mul_mem hy1 (hKH hq)
      have hnotK:ch H'∉K:=by
       intro hc
       have hcM:ch H'∈M:=hKM hc
       apply htM
       have e:t= ch H'*(t⁻¹*ch H')⁻¹:=by group
       rw[e]
       exact mul_mem hcM (inv_mem hy2')
      obtain ⟨J,hJ⟩:∃ J:Subgroup L,J=K⊔Subgroup.zpowers (ch H'):=⟨_,rfl⟩
      have hJH:J≤H:=by
       rw[hJ]
       exact sup_le hKH (Subgroup.zpowers_le.2 hcH)
      have hJH':J≤H':=by
       rw[hJ]
       exact sup_le hKH' (Subgroup.zpowers_le.2 hy1')
      have hKJ:K≤J:=by
       rw[hJ]
       exact le_sup_left
      have hKne:ZB K≠ZB J:=by
       intro h
       have h':=Subgroup.eq_of_le_of_card_ge hKJ h.symm.le
       apply hnotK
       rw[h',hJ]
       exact ZL (Subgroup.mem_zpowers _)
      have hpJ:=Q8e hp (n:= c+d+1)
        (by rw[← hL]; exact Subgroup.card_subgroup_dvd_card _)
        (by rw[← hL]; exact Subgroup.card_subgroup_dvd_card _) (Subgroup.card_dvd_of_le hKJ) hKne
      have hJeq:J=H':=by
       refine Subgroup.eq_of_le_of_card_ge hJH' ?_
       rw[hcardH',pow_succ, ← hKc,mul_comm]
       exact hpJ
      have hH'H:H'≤H:=by
       rw[← hJeq]
       exact hJH
      exact (Subgroup.eq_of_le_of_card_ge hH'H (by rw[hcardH,hcardH'])).symm
     calc (S2∩f ⁻¹' {a}).ncard
         ≤ ((M.map (ZF K):Subgroup (L⧸K)):Set (L⧸K)).ncard:=
           Set.ncard_le_ncard_of_injOn Φ hmaps hinj (Set.toFinite _)
       _=p^d:=by rw[← Nat.card_coe_set_eq]; exact hmap
    have himg:(f '' S2).ncard≤p^(c*(c+d+1 - c)):=by
     refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (ih M hM c)
     rintro _ ⟨H,hH,rfl⟩
     show ZB ((M⊓H).subgroupOf M)=p^c
     rw[← hS2card H hH]
     exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have h2:S2.ncard≤(f '' S2).ncard*p^d:=Q2p S2 f _ hfib
    have e1:c+d+1 - (c+1)=d:=by omega
    have e2:c+d+1 - c=d+1:=by omega
    have e3:c+d+1+1 - (c+1)=d+1:=by omega
    rw[e1]at h1
    rw[e2]at himg
    rw[e3,hsplit]
    calc (S1 ∪S2).ncard≤S1.ncard+S2.ncard:=Set.ncard_union_le _ _
      _ ≤ p^((c+1)*d)+p^(c*(d+1))*p^d:=
          Nat.add_le_add h1 (h2.trans (Nat.mul_le_mul_right _ himg))
      _ ≤ p ^(c*d+ c+d)+p^(c*d+ c+d):=by
          refine Nat.add_le_add (Nat.pow_le_pow_right hp.pos ?_) (le_of_eq ?_)
          · rw[add_mul,one_mul]
            omega
          · rw[← pow_add]
            congr 1<;>ring
      _=2*p^(c*d+ c+d):=by ring
      _≤p*p^(c*d+ c+d):=Nat.mul_le_mul_right _ hp.two_le
      _ = p^((c+1)*(d+1)):=by
          rw[← pow_succ']
          congr 1
          ring
end BrSubCount
section BrProp42
variable {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2] [CommGroup L3]
lemma Qcd {X:Type*} [Finite X] (T:Set X) (x0:X) (hx0:x0∈T) (s:ℕ):
    {κ:Fin s→X | ∀ k,κ k∈T}.ncard≤T.ncard^s:=by
  classical
  let F:(Fin s→X)→(Fin s→T):= fun κ k=>if h:κ k∈T then ⟨κ k,h⟩ else ⟨x0,hx0⟩
  have hinj:Set.InjOn F {κ:Fin s→X | ∀ k,κ k∈T}:=by
    intro κ hκ κ' hκ' he
    funext k
    have hk1:κ k∈T:=hκ k
    have hk2:κ' k∈T:=hκ' k
    have e:= congrArg Subtype.val (congrFun he k)
    have e1:((F κ k:T):X)=κ k:=by
     show ((if h:κ k∈T then (⟨κ k,h⟩:T) else ⟨x0,hx0⟩:T):X)=κ k
     rw[dif_pos hk1]
    have e2:((F κ' k:T):X)=κ' k:=by
     show ((if h:κ' k∈T then (⟨κ' k,h⟩:T) else ⟨x0,hx0⟩:T):X)=κ' k
     rw[dif_pos hk2]
    rw[← e1, ← e2]
    exact e
  calc _≤ZB (Fin s→T):=Q26 _ F hinj
    _=T.ncard^s:=by rw[Nat.card_fun,Nat.card_fin,Nat.card_coe_set_eq]
lemma Qbd [Finite L2] [Finite L3] {p s3 n b:ℕ} (hp:p.Prime)
    (hL3:ZB L3=p^s3) (hb:b≤ s3) (y:Fin n→ L2)
    (hy:ZA (ZG y)=⊤):
    {φ:L2→*L3 | ZB φ.range≤p^b}.ncard≤p^(b*(n+s3+1 - b)):=by
  classical
  haveI:=Fact.mk hp
  haveI:Finite (Subgroup L3):=
    Finite.of_injective (fun H:Subgroup L3=> (H:Set L3)) SetLike.coe_injective
  set S:={φ:L2→*L3 | ZB φ.range≤p^b} with hSdef
  have hext:∀ φ∈S,∃ K:Subgroup L3,ZB K=p^b∧φ.range≤K:=by
   intro φ hφ
   have hφ':ZB φ.range≤p^b:=hφ
   obtain ⟨k, -,hk⟩:=(Nat.dvd_prime_pow hp).1
     (show ZB φ.range∣p^s3 by rw[← hL3]; exact Subgroup.card_subgroup_dvd_card _)
   rw[hk]at hφ'
   have hkb:k≤b:=Q28 hp.one_lt hφ'
   exact Sylow.exists_subgroup_card_pow_prime_le p
     (show p^b∣ZB L3 by rw[hL3]; exact pow_dvd_pow p hb) φ.range hk hkb
  let f:(L2→*L3)→ Subgroup L3:= fun φ=>
    Classical.epsilon (fun K:Subgroup L3=>ZB K=p^b∧φ.range≤K)
  have hf:∀ φ∈S,ZB (f φ)=p^b∧φ.range≤f φ:= fun φ hφ=>
    Classical.epsilon_spec (hext φ hφ)
  have hM:∀ K:Subgroup L3,(S∩f ⁻¹' {K}).ncard≤(p^b)^n:=by
   intro K
   rcases (S∩f ⁻¹' {K}).eq_empty_or_nonempty with he | ⟨φ0,hφ0S,hφ0K⟩
   · rw[he,Set.ncard_empty]
     exact Nat.zero_le _
   · have hK:ZB K=p^b:=by
       have h0:=(hf φ0 hφ0S).1
       rwa[show f φ0=K from hφ0K]at h0
     have hmem:∀ φ∈S∩f ⁻¹' {K},∀ i,φ (y i)∈K:=by
      rintro φ ⟨hφS,hφK⟩ i
      have hφK':f φ=K:=hφK
      rw[← hφK']
      exact (hf φ hφS).2 ⟨y i,rfl⟩
     let F:(L2→*L3)→(Fin n→K):= fun φ i=>
       if h:φ (y i)∈K then ⟨φ (y i),h⟩ else 1
     have hinj:Set.InjOn F (S∩f ⁻¹' {K}):=by
      intro φ hφ ψ hψ hFeq
      apply MonoidHom.eq_of_eqOn_dense hy
      rintro _ ⟨i,rfl⟩
      have h1:= congrFun hFeq i
      have h2:((F φ i:K):L3)=φ (y i):=by
       show ((if h:φ (y i)∈K then (⟨φ (y i),h⟩:K) else 1:K):L3)=φ (y i)
       rw[dif_pos (hmem φ hφ i)]
      have h3:((F ψ i:K):L3)=ψ (y i):=by
       show ((if h:ψ (y i)∈K then (⟨ψ (y i),h⟩:K) else 1:K):L3)=ψ (y i)
       rw[dif_pos (hmem ψ hψ i)]
      rw[← h2, ← h3,h1]
     calc (S∩f ⁻¹' {K}).ncard≤ZB (Fin n→K):=Q26 _ F hinj
       _=ZB K^n:=by rw[Nat.card_fun,Nat.card_fin]
       _=(p^b)^n:=by rw[hK]
  have himg:(f '' S).ncard≤p^(b*(s3+1 - b)):=by
   refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) (Qbp hp s3 L3 hL3 b)
   rintro _ ⟨φ,hφ,rfl⟩
   exact (hf φ hφ).1
  calc S.ncard≤(f '' S).ncard*(p^b)^n:=Q2p S f _ hM
    _≤p^(b*(s3+1 - b))*(p^b)^n:=Nat.mul_le_mul_right _ himg
    _ =p^(b*(n+s3+1 - b)):=by
      rw[← pow_mul, ← pow_add]
      congr 1
      obtain ⟨d,rfl⟩:∃ d,s3=b+d:=⟨s3 - b,by omega⟩
      rw[show b+d+1 - b=d+1 by omega,show n+(b+d)+1 - b=n+d+1 by omega]
      ring
lemma Qhl [Finite L2] [Finite L3] {p s3 n b:ℕ} (hp:p.Prime)
    (hL3:ZB L3=p^s3) (hb:b≤ s3) (y:Fin n→ L2)
    (hy:ZA (ZG y)=⊤) (s:ℕ):
    {κ :Fin s→(L2→*L3) | ∀ k,ZB (κ k).range≤p^b}.ncard≤
      p^(s*(b*(n+s3+1 - b))):=by
  haveI:Finite (L2→*L3):=
    Finite.of_injective (fun f:L2→*L3=> (f:L2→ L3)) DFunLike.coe_injective
  have h1:(1:L2→*L3)∈{φ:L2→*L3 | ZB φ.range≤p^b}:=by
    show ZB (1:L2→*L3).range≤p^b
    rw[MonoidHom.range_one,Subgroup.card_bot]
    exact Nat.one_le_pow _ _ hp.pos
  calc _ ≤{φ:L2→*L3 | ZB φ.range≤p^b}.ncard^s:=
        Qcd {φ:L2→*L3 | ZB φ.range≤p^b} 1 h1 s
    _ ≤ (p^(b*(n+s3+1 - b)))^s:=
        Nat.pow_le_pow_left (Qbd hp hL3 hb y hy) s
    _=p^(s*(b*(n+s3+1 - b))):=by rw[← pow_mul,mul_comm]
end BrProp42
section BrBracket
variable {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2] [CommGroup L3]
abbrev Q21 (β:L1→*L1→*L2):Prop:=∀ x,β x x =1
abbrev Q1m (β1:L1→*L1→*L2) (β2:L2→*L1→*L3):Prop:=
  ∀ x y z,β2 (β1 x y) z*β2 (β1 y z) x*β2 (β1 z x) y=1
lemma Q24 {β:L1→*L1→*L2} (hA:Q21 β) (x y:L1):β y x =(β x y)⁻¹:=by
 have h:=hA (x*y)
 simp only[map_mul,MonoidHom.mul_apply,hA x,hA y,one_mul,mul_one]at h
 exact eq_inv_of_mul_eq_one_left h
lemma Q51 (β:L1→*L1→*L2) (x y:L1) (n:ℕ):
    β (x^n) y=(β x y)^n:=by
 have h:=map_pow (β.flip y) x n
 simpa[MonoidHom.flip_apply] using h
lemma Qbl (C:Subgroup L1) {β1 β1':L1→*L1→*L2} {β2 β2':L2→*L1→*L3}
    (hA:Q21 β1) (hA':Q21 β1') (hJ:Q1m β1 β2) (hJ':Q1m β1' β2')
    (hgen:ZA {w | ∃ u∈C,∃ v∈C,β1 u v=w}=⊤)
    (h1:∀ x,∀ u∈C,β1 x u=β1' x u) (h2:∀ z,∀ u∈C,β2 z u=β2' z u):
    β2=β2':=by
  have key:∀ w∈{w | ∃ u∈C,∃ v∈C,β1 u v=w},β2 w=β2' w:=by
    rintro _ ⟨u,hu,v,hv,rfl⟩
    ext x
    have e1:=hJ u v x
    have e2:=hJ' u v x
    have a1:β1 v x =β1' v x:=by
     rw[Q24 hA x v,Q24 hA' x v,h1 x v hv]
    have a2:β2 (β1 v x) u=β2' (β1' v x) u:=by rw[a1,h2 _ u hu]
    have a3:β2 (β1 x u) v=β2' (β1' x u) v:=by rw[h1 x u hu,h2 _ v hv]
    have a4:β1' u v=β1 u v:=(h1 u v hv).symm
    rw[a2,a3]at e1
    rw[a4]at e2
    exact mul_right_cancel (mul_right_cancel (e1.trans e2.symm))
  exact MonoidHom.eq_of_eqOn_dense hgen key
lemma Qei (C:Subgroup L1) {κ:L2→*L1→*L3} {β β0:L1→*L1→*L2}
    {β2 β20:L2→*L1→*L3} (hA:Q21 β) (hA0:Q21 β0) (hJ:Q1m β β2)
    (hJ0:Q1m β0 β20) (hgen:ZA {w | ∃ u∈C,∃ v∈C,β u v=w}=⊤)
    (hκ:∀ z,∀ u∈C,β2 z u=κ z u) (hκ0:∀ z,∀ u∈C,β20 z u=κ z u)
    (hagree:∀ x,∀ u∈C,β x u=β0 x u) {h:L1} (hh:h∈C) (x y:L1):
    κ (β x y) h=κ (β0 x y) h:=by
  have h22:β2=β20:=Qbl C hA hA0 hJ hJ0 hgen hagree
    (fun z u hu=> (hκ z u hu).trans (hκ0 z u hu).symm)
  have e1:=hJ x y h
  have e2:=hJ0 x y h
  have b1:β y h=β0 y h:=hagree y h hh
  have b2:β h x =β0 h x:=by
   rw[Q24 hA x h,Q24 hA0 x h,hagree x h hh]
  rw[b1,b2,h22]at e1
  rw[← hκ _ h hh, ← hκ0 _ h hh,h22]
  exact mul_right_cancel (mul_right_cancel (e1.trans e2.symm))
lemma Qi9 {ι:Type*} {g:ι→ L1} (hg:ZA (ZG g)=⊤)
    {Cidx:Set ι} {β β':L1→*L1→*L2} (hA:Q21 β) (hA':Q21 β')
    (Pc:Finset (ι×ι)) (hcov:∀ i,∀ j∈Cidx,i=j∨(i,j)∈Pc∨(j,i)∈Pc)
    (hP:∀ q∈Pc,β (g q.1) (g q.2)=β' (g q.1) (g q.2)):
    ∀ x,∀ u∈ZA (g '' Cidx),β x u=β' x u:=by
 have hgen:∀ j∈Cidx,β.flip (g j)=β'.flip (g j):=by
  intro j hj
  apply MonoidHom.eq_of_eqOn_dense hg
  rintro _ ⟨i,rfl⟩
  simp only[MonoidHom.flip_apply]
  rcases hcov i j hj with rfl | h | h
  · exact (hA _).trans (hA' _).symm
  · exact hP _ h
  · rw[Q24 hA (g j) (g i),Q24 hA' (g j) (g i),hP _ h]
 intro x u hu
 have hle:ZA (g '' Cidx)≤(β x).eqLocus (β' x):=by
  rw[ZD]
  rintro _ ⟨j,hj,rfl⟩
  show β x (g j)=β' x (g j)
  have:= congrArg (fun φ:L1→*L2=>φ x) (hgen j hj)
  simpa[MonoidHom.flip_apply] using this
 exact hle hu
lemma Qf7 {ι:Type*} {g:ι→ L1} (hg:ZA (ZG g)=⊤)
    {Cidx:Set ι} {β β':L1→*L1→*L2} (hA:Q21 β) (hA':Q21 β')
    (Po:Finset (ι×ι))
    (hcovo:∀ i j,i∉Cidx→j∉Cidx→i=j∨(i,j)∈Po∨(j,i)∈Po)
    (hC:∀ x,∀ u∈ZA (g '' Cidx),β x u=β' x u)
    (hPo:∀ q∈Po,β (g q.1) (g q.2)=β' (g q.1) (g q.2)):β=β':=by
 have hgi:∀ i,β (g i)=β' (g i):=by
  intro i
  apply MonoidHom.eq_of_eqOn_dense hg
  rintro _ ⟨j,rfl⟩
  by_cases hj:j∈Cidx
  · exact hC _ _ (ZC ⟨j,hj,rfl⟩)
  · by_cases hi:i∈Cidx
    · rw [Q24 hA (g j) (g i),Q24 hA' (g j) (g i),
        hC _ _ (ZC ⟨i,hi,rfl⟩)]
    · rcases hcovo i j hi hj with rfl | h | h
      · exact (hA _).trans (hA' _).symm
      · exact hPo _ h
      · rw[Q24 hA (g j) (g i),Q24 hA' (g j) (g i),hPo _ h]
 apply MonoidHom.eq_of_eqOn_dense hg
 rintro _ ⟨i,rfl⟩
 exact hgi i
lemma Qdz {L:Type*} [Group L] {K:Subgroup L} {x:L} [Decidable (x∈K)]
    (h:x∈K):((if hp:x∈K then (⟨x,hp⟩:K) else 1:K):L)=x:=by
  rw[dif_pos h]
lemma Qi6 [Finite L2] {ι:Type*} [DecidableEq ι] (g:ι→ L1)
    (hg:ZA (ZG g)=⊤) (Cidx:Set ι) (κ:L2→*L1→*L3) {h:L1}
    (hh:h∈ZA (g '' Cidx)) (Pc Po D:Finset (ι×ι))
    (hcov:∀ i,∀ j∈Cidx,i=j∨(i,j)∈Pc∨(j,i)∈Pc)
    (hcovo:∀ i j,i∉Cidx→j∉Cidx→i=j∨(i,j)∈Po∨(j,i)∈Po)
    (v:ι×ι→ L2):
    {β1 : L1→*L1→*L2 | Q21 β1∧
        ZA {w | ∃ u∈ZA (g '' Cidx),
          ∃ u'∈ZA (g '' Cidx),β1 u u'=w}=⊤∧
        (∃ β2:L2→*L1→*L3,(∀ z,∀ u∈ZA (g '' Cidx),β2 z u=κ z u)∧
          Q1m β1 β2)∧
        ∀ q∈D,β1 (g q.1) (g q.2)=v q}.ncard≤
      ZB L2^(Pc \ D).card*ZB (κ.flip h).ker^Po.card:=by
  classical
  set C:=ZA (g '' Cidx) with hCdef
  set S :={β1:L1→*L1→*L2 | Q21 β1∧
        ZA {w | ∃ u∈C,∃ u'∈C,β1 u u'=w}=⊤∧
        (∃ β2:L2→*L1→*L3,(∀ z,∀ u∈C,β2 z u=κ z u)∧Q1m β1 β2)∧
        ∀ q∈D,β1 (g q.1) (g q.2)=v q} with hSdef
  let fc:(L1→*L1→*L2)→(↥(Pc \ D)→ L2):= fun β q=>β (g q.1.1) (g q.1.2)
  have hfib :∀ a,(S∩fc ⁻¹' {a}).ncard≤ZB (κ.flip h).ker^Po.card:=by
   intro a
   rcases (S∩fc ⁻¹' {a}).eq_empty_or_nonempty with he | ⟨β0,hβ0S,hβ0a⟩
   · rw[he,Set.ncard_empty]
     exact Nat.zero_le _
   · obtain ⟨hA0, -,⟨β20,hκ0,hJ0⟩,hD0⟩:=hβ0S
     have hβ0a':fc β0=a:=hβ0a
     have hag:∀ β∈S∩fc ⁻¹' {a},∀ x,∀ u∈C,β x u=β0 x u:=by
      rintro β ⟨⟨hA, -, -,hD⟩,hβa⟩
      have hβa':fc β=a:=hβa
      apply Qi9 hg hA hA0 Pc hcov
      intro q hq
      by_cases hqD:q∈D
      · rw[hD q hqD,hD0 q hqD]
      · have hq':q∈Pc \ D:=Finset.mem_sdiff.2 ⟨hq,hqD⟩
        exact congrFun (hβa'.trans hβ0a'.symm) ⟨q,hq'⟩
     have hker :∀ β∈S∩fc ⁻¹' {a},∀ x y,
         β x y/β0 x y∈(κ.flip h).ker :=by
      intro β hβ x y
      obtain ⟨⟨hA,hgen,⟨β2,hκ,hJ⟩, -⟩, -⟩:=id hβ
      rw [MonoidHom.mem_ker,map_div,MonoidHom.flip_apply,MonoidHom.flip_apply,
        Qei C hA hA0 hJ hJ0 hgen hκ hκ0 (hag β hβ) hh x y,div_self']
     let F:(L1→*L1→*L2)→(↥Po→(κ.flip h).ker):= fun β q=>
       if hq:β (g q.1.1) (g q.1.2)/β0 (g q.1.1) (g q.1.2)∈(κ.flip h).ker then
         ⟨_,hq⟩ else 1
     have hv:∀ β∈S∩fc ⁻¹' {a},∀ q:↥Po,((F β q:(κ.flip h).ker):L2)=
         β (g q.1.1) (g q.1.2)/β0 (g q.1.1) (g q.1.2):=by
      intro β hβ q
      exact Qdz (hker β hβ _ _)
     have hinj:Set.InjOn F (S∩fc ⁻¹' {a}):=by
      intro β hβ β' hβ' hF
      have hpo:∀ q∈Po,β (g q.1) (g q.2)=β' (g q.1) (g q.2):=by
       intro q hq
       have e:= congrArg Subtype.val (congrFun hF ⟨q,hq⟩)
       rw[hv β hβ ⟨q,hq⟩,hv β' hβ' ⟨q,hq⟩]at e
       exact div_left_inj.mp e
      obtain ⟨⟨hA, -⟩, -⟩:=id hβ
      obtain ⟨⟨hA', -⟩, -⟩:=id hβ'
      exact Qf7 hg hA hA' Po hcovo
        (fun x u hu=> (hag β hβ x u hu).trans (hag β' hβ' x u hu).symm) hpo
     calc (S∩fc ⁻¹' {a}).ncard≤ZB (↥Po→(κ.flip h).ker):=
           Q26 _ F hinj
       _ = ZB (κ.flip h).ker^Po.card:=by
           rw[Nat.card_fun,Nat.card_eq_fintype_card (α:=↥Po),Fintype.card_coe]
  calc S.ncard≤ZB (↥(Pc \ D)→ L2)*ZB (κ.flip h).ker^Po.card:=
        Qfm S fc _ hfib
    _ = ZB L2^(Pc \ D).card*ZB (κ.flip h).ker^Po.card:=by
        rw[Nat.card_fun,Nat.card_eq_fintype_card (α:=↥(Pc \ D)),Fintype.card_coe]
lemma Qlu [Finite L2] {ι:Type*} [DecidableEq ι] {p s2 b:ℕ} (hp:p.Prime)
    (hL2:ZB L2=p^s2) (g:ι→ L1)
    (hg:ZA (ZG g)=⊤) (Cidx:Set ι) (κ:L2→*L1→*L3) {h:L1}
    (hh:h∈ZA (g '' Cidx)) (hb:p^b≤ZB (κ.flip h).range)
    (Pc Po D:Finset (ι×ι))
    (hcov:∀ i,∀ j∈Cidx,i=j∨(i,j)∈Pc∨(j,i)∈Pc)
    (hcovo:∀ i j,i∉Cidx→j∉Cidx→i=j∨(i,j)∈Po∨(j,i)∈Po)
    (v:ι×ι→ L2):
    {β1 : L1→*L1→*L2 | Q21 β1∧
        ZA {w | ∃ u∈ZA (g '' Cidx),
          ∃ u'∈ZA (g '' Cidx),β1 u u'=w}=⊤∧
        (∃ β2:L2→*L1→*L3,(∀ z,∀ u∈ZA (g '' Cidx),β2 z u=κ z u)∧
          Q1m β1 β2)∧
        ∀ q∈D,β1 (g q.1) (g q.2)=v q}.ncard≤
      p^(s2*(Pc \ D).card+(s2 - b)*Po.card):=by
  refine le_trans (Qi6 g hg Cidx κ hh Pc Po D hcov hcovo v) ?_
  rw[hL2,pow_add,pow_mul,pow_mul]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Qh1 hp _ hL2 hb) _)
lemma Q8g (s:ℕ):∀ r :ℕ,
    ((ZQ r×ˢ ZQ r).filter (fun q:ℕ×ℕ=>q.1<q.2∧s≤q.1)).card=
      (r - s).choose 2
  | 0=>by simp
  | r + 1 =>by
    classical
    have hsplit:(ZQ (r+1)×ˢ ZQ (r+1)).filter
          (fun q:ℕ×ℕ=>q.1<q.2∧s≤q.1)=
        (ZQ r×ˢ ZQ r).filter (fun q:ℕ×ℕ=>q.1<q.2∧s≤q.1)∪
          (Finset.Ico s r).image (fun i=> (i,r)):=by
      ext ⟨i,j⟩
      simp only[Finset.mem_filter,Finset.mem_product,Finset.mem_range,Finset.mem_union,
        Finset.mem_image,Finset.mem_Ico,Prod.mk.injEq]
      constructor
      · rintro ⟨⟨hi,hj⟩,hij,hsi⟩
        by_cases hjr :j< r
        · exact Or.inl ⟨⟨by omega,hjr⟩,hij,hsi⟩
        · exact Or.inr ⟨i,⟨hsi,by omega⟩,rfl,by omega⟩
      · rintro (⟨⟨hi,hj⟩,hij,hsi⟩ | ⟨a,⟨hsa,har⟩,rfl,rfl⟩)
        · exact ⟨⟨by omega,by omega⟩,hij,hsi⟩
        · exact ⟨⟨by omega,by omega⟩,har,hsa⟩
    have hdisj:Disjoint ((ZQ r×ˢ ZQ r).filter
        (fun q:ℕ×ℕ=>q.1<q.2∧s≤q.1)) ((Finset.Ico s r).image (fun i=> (i,r))):=by
      rw[Finset.disjoint_left]
      rintro ⟨i,j⟩ h1 h2
      simp only[Finset.mem_filter,Finset.mem_product,Finset.mem_range,Finset.mem_image,
        Finset.mem_Ico,Prod.mk.injEq]at h1 h2
      obtain ⟨a, -, -,hj⟩:=h2
      omega
    have hinj:Function.Injective (fun i:ℕ=> (i,r)):= fun a b h=> (Prod.mk.inj h).1
    have hu:=Finset.card_union_add_card_inter
      ((ZQ r×ˢ ZQ r).filter (fun q:ℕ×ℕ=>q.1<q.2∧s≤q.1))
      ((Finset.Ico s r).image (fun i=> (i,r)))
    rw[Finset.disjoint_iff_inter_eq_empty.1 hdisj,Finset.card_empty,add_zero]at hu
    rw[hsplit,hu,Q8g s r,Finset.card_image_of_injective _ hinj,Nat.card_Ico]
    rcases Nat.lt_or_ge r s with h | h
    · rw[show r - s=0 by omega,show r+1 - s=0 by omega,Nat.add_zero]
    · rw [show r+1 - s=(r - s)+1 by omega,Nat.choose_succ_succ',Nat.choose_one_right,
        Nat.add_comm]
lemma Q4e (r s:ℕ):
    ((Finset.univ:Finset (Fin r×Fin r)).filter
      (fun q=>q.1<q.2∧¬ (q.1:ℕ)<s)).card=(r - s).choose 2:=by
  classical
  rw[← Q8g s r]
  have hinj:Function.Injective (fun q:Fin r×Fin r=> ((q.1:ℕ),(q.2:ℕ))):=by
    intro q1 q2 h
    simp only[Prod.mk.injEq]at h
    exact Prod.ext (Fin.ext h.1) (Fin.ext h.2)
  rw[← Finset.card_image_of_injective _ hinj]
  congr 1
  ext ⟨i,j⟩
  simp only[Finset.mem_image,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_product,
    Finset.mem_range,Prod.mk.injEq]
  constructor
  · rintro ⟨q,⟨h1,h2⟩,rfl,rfl⟩
    exact ⟨⟨q.1.2,q.2.2⟩,h1,not_lt.1 h2⟩
  · rintro ⟨⟨hi,hj⟩,hij,hsi⟩
    exact ⟨(⟨i,hi⟩,⟨j,hj⟩),⟨hij,not_lt.2 hsi⟩,rfl,rfl⟩
lemma Qi5 [Finite L2] {p r s s2 b:ℕ} (hp:p.Prime)
    (hL2:ZB L2=p^s2) (g:Fin r→ L1)
    (hg:ZA (ZG g)=⊤) (κ:L2→*L1→*L3) {h:L1}
    (hh:h∈ZA (g '' {j | (j:ℕ)<s}))
    (hb:p^b≤ZB (κ.flip h).range) (D:Finset (Fin r×Fin r))
    (hD:∀ q∈D,q.1<q.2∧(q.1:ℕ)<s) (v:Fin r×Fin r→ L2):
    {β1 : L1→*L1→*L2 | Q21 β1∧
        ZA {w | ∃ u∈ZA (g '' {j | (j:ℕ)<s}),
          ∃ u'∈ZA (g '' {j | (j:ℕ)<s}),β1 u u'=w}=⊤∧
        (∃ β2:L2→*L1→*L3,
          (∀ z,∀ u∈ZA (g '' {j | (j:ℕ)<s}),β2 z u=κ z u)∧
          Q1m β1 β2)∧
        ∀ q∈D,β1 (g q.1) (g q.2)=v q}.ncard≤
      p^((r.choose 2 - D.card)*s2 - (r - s).choose 2*b):=by
  classical
  set T:=(Finset.univ:Finset (Fin r×Fin r)).filter (fun q=>q.1<q.2) with hTdef
  set Pc:=T.filter (fun q=> (q.1:ℕ)<s) with hPcdef
  set Po:=T.filter (fun q=> ¬ (q.1:ℕ)<s) with hPodef
  have hcov:∀ i,∀ j∈{j:Fin r | (j:ℕ)<s},i=j∨(i,j)∈Pc∨(j,i)∈Pc:=by
    intro i j hj
    have hj':(j:ℕ)<s:=hj
    rcases lt_trichotomy i j with hij | hij | hij
    · refine Or.inr (Or.inl ?_)
      rw[hPcdef,hTdef,Finset.mem_filter,Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _,hij⟩,Nat.lt_trans (show (i:ℕ)<j from hij) hj'⟩
    · exact Or.inl hij
    · refine Or.inr (Or.inr ?_)
      rw[hPcdef,hTdef,Finset.mem_filter,Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _,hij⟩,hj'⟩
  have hcovo:∀ i j,i∉{j:Fin r | (j:ℕ)<s}→j∉{j:Fin r | (j:ℕ)<s}→
      i=j∨(i,j)∈Po∨(j,i)∈Po:=by
    intro i j hi hj
    have hi':¬ (i:ℕ)<s:=hi
    have hj':¬ (j:ℕ)<s:=hj
    rcases lt_trichotomy i j with hij | hij | hij
    · refine Or.inr (Or.inl ?_)
      rw[hPodef,hTdef,Finset.mem_filter,Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _,hij⟩,hi'⟩
    · exact Or.inl hij
    · refine Or.inr (Or.inr ?_)
      rw[hPodef,hTdef,Finset.mem_filter,Finset.mem_filter]
      exact ⟨⟨Finset.mem_univ _,hij⟩,hj'⟩
  have main:=Qlu hp hL2 g hg {j:Fin r | (j:ℕ)<s} κ hh hb Pc Po D hcov hcovo v
  refine le_trans main (Nat.pow_le_pow_right hp.pos ?_)
  have hTc:T.card=r.choose 2:=by
   have h0:=Q4e r 0
   rw[Nat.sub_zero]at h0
   rw[← h0,hTdef]
   congr 1
   ext q
   simp
  have hT:Pc.card+Po.card=r.choose 2:=by
   rw[hPcdef,hPodef,Finset.card_filter_add_card_filter_not,hTc]
  have hPo:Po.card=(r - s).choose 2:=by
   rw[← Q4e r s,hPodef,hTdef]
   congr 1
   ext q
   simp
  have hDsub:D⊆Pc:=by
   intro q hq
   rw[hPcdef,hTdef,Finset.mem_filter,Finset.mem_filter]
   exact ⟨⟨Finset.mem_univ _,(hD q hq).1⟩,(hD q hq).2⟩
  have hsd:(Pc \ D).card+D.card=Pc.card:=Finset.card_sdiff_add_card_eq_card hDsub
  have hrange:ZB (κ.flip h).range≤ZB L2:=
    Nat.card_le_card_of_surjective _ (κ.flip h).rangeRestrict_surjective
  have hbs:b≤ s2:=Q28 hp.one_lt (hb.trans (hrange.trans hL2.le))
  have key:∀ a o b c:ℕ,(b+ c)*a+ c* o≤(a+ o)*(b+ c) - o*b:=by
   intro a o b c
   have e:(a+ o)*(b+ c)= o*b+((b+ c)*a+ c* o):=by ring
   rw[e,Nat.add_sub_cancel_left]
  have e1:r.choose 2 - D.card=(Pc \ D).card+Po.card:=by omega
  rw[e1, ← hPo]
  obtain ⟨c,hc⟩:∃ c,s2=b+ c:=⟨s2 - b,by omega⟩
  rw[hc,Nat.add_sub_cancel_left]
  exact key _ _ _ _
lemma Qn7 [Finite L1] [Finite L2] [Finite L3] {p r s s2 s3 n b:ℕ} (hp:p.Prime)
    (hsr :s≤ r) (hL2:ZB L2=p^s2) (hL3:ZB L3=p^s3) (y:Fin n→ L2)
    (hy:ZA (ZG y)=⊤) (g:Fin r→ L1)
    (hg:ZA (ZG g)=⊤) (D:Finset (Fin r×Fin r))
    (hD:∀ q∈D,q.1<q.2∧(q.1:ℕ)<s) (v:Fin r×Fin r→ L2):
    {β : (L1→*L1→*L2)×(L2→*L1→*L3) | Q21 β.1∧
        ZA {w | ∃ u∈ZA (g '' {j | (j:ℕ)<s}),
          ∃ u'∈ZA (g '' {j | (j:ℕ)<s}),β.1 u u'=w}=⊤∧
        Q1m β.1 β.2∧
        (∀ j:Fin r,(j:ℕ)<s→ZB (β.2.flip (g j)).range≤p^b)∧
        (∃ h∈ZA (g '' {j | (j:ℕ)<s}),p^b≤ZB (β.2.flip h).range)∧
        ∀ q∈D,β.1 (g q.1) (g q.2)=v q}.ncard≤
      p ^(s*(b*(n+s3+1 - b)))*
        p^((r.choose 2 - D.card)*s2 - (r - s).choose 2*b):=by
  classical
  haveI:Finite (L2→*L3):=
    Finite.of_injective (fun f:L2→*L3=> (f:L2→ L3)) DFunLike.coe_injective
  haveI:Finite (L1→*L2):=
    Finite.of_injective (fun f:L1→*L2=> (f:L1→ L2)) DFunLike.coe_injective
  haveI:Finite (L1→*L1→*L2):=
    Finite.of_injective (fun f:L1→*L1→*L2=> (f:L1→(L1→*L2))) DFunLike.coe_injective
  set C:=ZA (g '' {j | (j:ℕ)<s}) with hCdef
  let c:Fin s→ L1:= fun k=>g (Fin.castLE hsr k)
  set BR :={β:(L1→*L1→*L2)×(L2→*L1→*L3) | Q21 β.1∧
        ZA {w | ∃ u∈C,∃ u'∈C,β.1 u u'=w}=⊤∧
        Q1m β.1 β.2∧
        (∀ j:Fin r,(j:ℕ)<s→ZB (β.2.flip (g j)).range≤p^b)∧
        (∃ h∈C,p^b≤ZB (β.2.flip h).range)∧
        ∀ q∈D,β.1 (g q.1) (g q.2)=v q} with hBR
  rcases BR.eq_empty_or_nonempty with hBe | ⟨β1,hβ1⟩
  · rw[hBe,Set.ncard_empty]
    exact Nat.zero_le _
  have hbs3:b≤ s3:=by
   obtain ⟨-, -, -, -,⟨h1, -,hb1⟩, -⟩:=id hβ1
   have hr :ZB (β1.2.flip h1).range≤ZB L3:=
     Subgroup.card_le_card_group (H:=(β1.2.flip h1).range)
   exact Q28 hp.one_lt (hb1.trans (hr.trans hL3.le))
  let ρ:(L1→*L1→*L2)×(L2→*L1→*L3)→(Fin s→(L2→*L3)):=
    fun β k=>β.2.flip (c k)
  have himg:(ρ '' BR).ncard≤p^(s*(b*(n+s3+1 - b))):=by
   refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
     (Qhl hp hL3 hbs3 y hy s (b:=b))
   rintro _ ⟨β,hβ,rfl⟩ k
   obtain ⟨-, -, -,hsl0, -⟩:=id hβ
   exact hsl0 (Fin.castLE hsr k) (by simp)
  have hfib :∀ a,(BR∩ρ ⁻¹' {a}).ncard≤
      p^((r.choose 2 - D.card)*s2 - (r - s).choose 2*b):=by
   intro a
   rcases (BR∩ρ ⁻¹' {a}).eq_empty_or_nonempty with he | ⟨β0,hβ0,hβ0a⟩
   · rw[he,Set.ncard_empty]
     exact Nat.zero_le _
   · obtain ⟨-, -, -, -,⟨h0,hh0,hb0⟩, -⟩:=id hβ0
     have hβ0a':ρ β0=a:=hβ0a
     have hsl:∀ β∈BR∩ρ ⁻¹' {a},∀ z,∀ u∈C,β.2 z u=β0.2 z u:=by
      rintro β ⟨-,hβa⟩ z u hu
      have hβa':ρ β=a:=hβa
      have hgen:∀ j:Fin r,(j:ℕ)<s→β.2.flip (g j)=β0.2.flip (g j):=by
       intro j hj
       have e:= congrFun (hβa'.trans hβ0a'.symm) ⟨(j:ℕ),hj⟩
       change β.2.flip (c ⟨(j:ℕ),hj⟩)=β0.2.flip (c ⟨(j:ℕ),hj⟩) at e
       have e2:c ⟨(j:ℕ),hj⟩=g j:= congrArg g (Fin.ext rfl)
       rw[e2]at e
       exact e
      have hle:C≤(β.2 z).eqLocus (β0.2 z):=by
       rw[hCdef,ZD]
       rintro _ ⟨j,hj,rfl⟩
       show β.2 z (g j)=β0.2 z (g j)
       have:= congrArg (fun φ:L2→*L3=>φ z) (hgen j hj)
       simpa[MonoidHom.flip_apply] using this
      exact hle hu
     let S43:Set (L1→*L1→*L2):={β1 | Q21 β1∧
       ZA {w | ∃ u∈C,∃ u'∈C,β1 u u'=w}=⊤∧
       (∃ β2:L2→*L1→*L3,(∀ z,∀ u∈C,β2 z u=β0.2 z u)∧Q1m β1 β2)∧
       ∀ q∈D,β1 (g q.1) (g q.2)=v q}
     have hmaps:∀ β∈BR∩ρ ⁻¹' {a},Prod.fst β∈S43:=by
      intro β hβ
      obtain ⟨⟨hA,hgen,hJ, -, -,hDv⟩, -⟩:=id hβ
      exact ⟨hA,hgen,⟨β.2,hsl β hβ,hJ⟩,hDv⟩
     have hinj:Set.InjOn Prod.fst (BR∩ρ ⁻¹' {a}):=by
      intro β hβ β' hβ' h1
      obtain ⟨⟨hA,hgen,hJ, -⟩, -⟩:=id hβ
      obtain ⟨⟨hA', -,hJ', -⟩, -⟩:=id hβ'
      have h1':β.1=β'.1:=h1
      have h2:β.2=β'.2:=Qbl C hA hA' hJ hJ' hgen (fun x u _=>by rw[h1'])
        (fun z u hu=> (hsl β hβ z u hu).trans (hsl β' hβ' z u hu).symm)
      exact Prod.ext h1' h2
     calc (BR∩ρ ⁻¹' {a}).ncard≤S43.ncard:=
           Set.ncard_le_ncard_of_injOn Prod.fst hmaps hinj (Set.toFinite _)
       _≤_:=Qi5 hp hL2 g hg β0.2 hh0 hb0 D hD v
  calc BR.ncard≤(ρ '' BR).ncard*p^((r.choose 2 - D.card)*s2 - (r - s).choose 2*b):=
        Q2p BR ρ _ hfib
    _ ≤ p ^(s*(b*(n+s3+1 - b)))*
          p^((r.choose 2 - D.card)*s2 - (r - s).choose 2*b):=
        Nat.mul_le_mul_right _ himg
lemma Qi1 [Finite L2] {W:Type*} [Group W] {ι:Type*} [DecidableEq ι] (g:ι→ L1)
    (hg:ZA (ZG g)=⊤) (P D:Finset (ι×ι))
    (hcov:∀ i j,i=j∨(i,j)∈P∨(j,i)∈P) (v:ι×ι→ L2) (π:L2→*W)
    (S:Set (L1→*L1→*L2))
    (hS:∀ β∈S,Q21 β∧∀ q∈D,β (g q.1) (g q.2)=v q):
    S.ncard≤((fun β:L1→*L1→*L2=>fun q:↥P=>π (β (g q.1.1) (g q.1.2))) '' S).ncard*
      ZB π.ker^(P \ D).card:=by
  classical
  let R:(L1→*L1→*L2)→(↥P→ W):= fun β q=>π (β (g q.1.1) (g q.1.2))
  refine Q2p S R _ ?_
  intro a
  rcases (S∩R ⁻¹' {a}).eq_empty_or_nonempty with he | ⟨β0,hβ0S,hβ0a⟩
  · rw[he,Set.ncard_empty]
    exact Nat.zero_le _
  · have hβ0a':R β0=a:=hβ0a
    have hker :∀ β∈S∩R ⁻¹' {a},∀ q∈P,
        β (g q.1) (g q.2)/β0 (g q.1) (g q.2)∈π.ker :=by
     rintro β ⟨-,hβa⟩ q hq
     have hβa':R β=a:=hβa
     have e:= congrFun (hβa'.trans hβ0a'.symm) ⟨q,hq⟩
     rw[MonoidHom.mem_ker,map_div]
     exact div_eq_one.mpr e
    let F:(L1→*L1→*L2)→(↥(P \ D)→π.ker):= fun β q=>
      if hq:β (g q.1.1) (g q.1.2)/β0 (g q.1.1) (g q.1.2)∈π.ker then ⟨_,hq⟩ else 1
    have hv:∀ β∈S∩R ⁻¹' {a},∀ q:↥(P \ D),((F β q:π.ker):L2)=
        β (g q.1.1) (g q.1.2)/β0 (g q.1.1) (g q.1.2):=by
     intro β hβ q
     exact Qdz (hker β hβ q.1 (Finset.mem_sdiff.1 q.2).1)
    have hinj:Set.InjOn F (S∩R ⁻¹' {a}):=by
     intro β hβ β' hβ' hF
     obtain ⟨hβS, -⟩:=id hβ
     obtain ⟨hβS', -⟩:=id hβ'
     obtain ⟨hA,hD⟩:=hS β hβS
     obtain ⟨hA',hD'⟩:=hS β' hβS'
     have hP:∀ q∈P,β (g q.1) (g q.2)=β' (g q.1) (g q.2):=by
      intro q hq
      by_cases hqD:q∈D
      · rw[hD q hqD,hD' q hqD]
      · have hq':q∈P \ D:=Finset.mem_sdiff.2 ⟨hq,hqD⟩
        have e:= congrArg Subtype.val (congrFun hF ⟨q,hq'⟩)
        rw[hv β hβ ⟨q,hq'⟩,hv β' hβ' ⟨q,hq'⟩]at e
        exact div_left_inj.mp e
     have hgi:∀ i,β (g i)=β' (g i):=by
      intro i
      apply MonoidHom.eq_of_eqOn_dense hg
      rintro _ ⟨j,rfl⟩
      rcases hcov i j with rfl | h | h
      · exact (hA _).trans (hA' _).symm
      · exact hP _ h
      · rw[Q24 hA (g j) (g i),Q24 hA' (g j) (g i),hP _ h]
     apply MonoidHom.eq_of_eqOn_dense hg
     rintro _ ⟨i,rfl⟩
     exact hgi i
    calc (S∩R ⁻¹' {a}).ncard≤ZB (↥(P \ D)→π.ker):=
          Q26 _ F hinj
      _ = ZB π.ker^(P \ D).card:=by
          rw[Nat.card_fun,Nat.card_eq_fintype_card (α:=↥(P \ D)),Fintype.card_coe]
end BrBracket
section BrBreadth
variable {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2] [CommGroup L3]
noncomputable def Q1p (p:ℕ) (κ:L2→*L1→*L3) (C:Subgroup L1):ℕ:=
  sSup {k | ∃ u∈C,p^k≤ZB (κ.flip u).range}
lemma Q81 [Finite L3] (p:ℕ) (κ:L2→*L1→*L3) (C:Subgroup L1):
    {k | ∃ u∈C,p^k≤ZB (κ.flip u).range}.Nonempty:=
  ⟨0,show ∃ u∈C,p^0≤ZB (κ.flip u).range from
    ⟨1,C.one_mem,by rw[pow_zero]; exact Nat.card_pos⟩⟩
lemma Q87 [Finite L3] {p s3:ℕ} (hp:p.Prime) (hL3:ZB L3=p^s3)
    (κ:L2→*L1→*L3) (C:Subgroup L1):
    ∀ k∈{k | ∃ u∈C,p^k≤ZB (κ.flip u).range},k≤ s3:=by
  rintro k ⟨u, -,hk⟩
  exact Q28 hp.one_lt
    (hk.trans ((Subgroup.card_le_card_group (H:=(κ.flip u).range)).trans hL3.le))
lemma Qao [Finite L3] {p s3:ℕ} (hp:p.Prime) (hL3:ZB L3=p^s3)
    (κ:L2→*L1→*L3) (C:Subgroup L1):
    ∃ h∈C,p^Q1p p κ C≤ZB (κ.flip h).range:=
  Nat.sSup_mem (Q81 p κ C) ⟨s3,Q87 hp hL3 κ C⟩
lemma Q9y [Finite L3] {p s3:ℕ} (hp:p.Prime) (hL3:ZB L3=p^s3)
    (κ:L2→*L1→*L3) (C:Subgroup L1):Q1p p κ C≤ s3:=
  csSup_le (Q81 p κ C) (Q87 hp hL3 κ C)
lemma Q3u [Finite L3] {p s3:ℕ} (hp:p.Prime)
    (hL3:ZB L3=p^s3) (κ:L2→*L1→*L3) (C:Subgroup L1) {u:L1} (hu:u∈C):
    ZB (κ.flip u).range≤p^Q1p p κ C:=by
 obtain ⟨k, -,hk⟩:=(Nat.dvd_prime_pow hp).1
   (show ZB (κ.flip u).range∣p^s3 by
     rw[← hL3]; exact Subgroup.card_subgroup_dvd_card _)
 rw[hk]
 exact Nat.pow_le_pow_right hp.pos
   (le_csSup ⟨s3,Q87 hp hL3 κ C⟩
     (show ∃ v∈C,p^k≤ZB (κ.flip v).range from ⟨u,hu,hk.ge⟩))
lemma Qgj [Finite L2] [Finite L3] {p s2 s3:ℕ} (hp:p.Prime)
    (hL2:ZB L2=p^s2) (hL3:ZB L3=p^s3) (κ:L2→*L1→*L3)
    (C:Subgroup L1):Q1p p κ C≤ s2:=by
 obtain ⟨h, -,hh⟩:=Qao hp hL3 κ C
 have hr :ZB (κ.flip h).range≤ZB L2:=
   Nat.card_le_card_of_surjective _ (κ.flip h).rangeRestrict_surjective
 exact Q28 hp.one_lt (hh.trans (hr.trans hL2.le))
lemma Qb0 {L:Type*} [CommGroup L] [Finite L] {ι:Type*}
    (H:ι→ Subgroup L) (M:ℕ):
    ∀ I:Finset ι,(∀ i∈I,ZB (H i)≤M)→ZB ↥(I.sup H)≤M^I.card:=by
 classical
 intro I
 refine Finset.induction_on I ?_ ?_
 · intro _
   rw[Finset.sup_empty,Subgroup.card_bot,Finset.card_empty,pow_zero]
 · intro a I ha ih hM
   rw[Finset.sup_insert,Finset.card_insert_eq_ite,if_neg ha,pow_succ,mul_comm]
   exact (Q7j _ _).trans (Nat.mul_le_mul (hM a (Finset.mem_insert_self a I))
     (ih fun i hi=>hM i (Finset.mem_insert_of_mem hi)))
lemma Qex [Finite L3] {p r s s3:ℕ} (hp:p.Prime) (hsr :s≤ r)
    (hL3:ZB L3=p^s3) (κ:L2→*L1→*L3) (g:Fin r→ L1)
    (hgen3:ZA
      {w | ∃ z,∃ u∈ZA (g '' {j | (j:ℕ)<s}),κ z u=w}=⊤):
    s3≤ s*Q1p p κ (ZA (g '' {j | (j:ℕ)<s})):=by
  classical
  let c:Fin s→ L1:= fun k=>g (Fin.castLE hsr k)
  have hc:∀ j:Fin r,∀ hj:(j:ℕ)<s,c ⟨(j:ℕ),hj⟩=g j:= fun j hj=>
    congrArg g (Fin.ext rfl)
  have hsup:(⊤:Subgroup L3)≤Finset.univ.sup (fun k=> (κ.flip (c k)).range):=by
    rw[← hgen3,ZD]
    rintro _ ⟨z,u,hu,rfl⟩
    have hle:ZA (g '' {j | (j:ℕ)<s})≤
        (Finset.univ.sup (fun k=> (κ.flip (c k)).range)).comap (κ z):=by
      rw[ZD]
      rintro _ ⟨j,hj,rfl⟩
      rw[SetLike.mem_coe,Subgroup.mem_comap]
      have hj':(j:ℕ)<s:=hj
      have hmem:κ z (g j)∈(κ.flip (c ⟨(j:ℕ),hj'⟩)).range:=by
       rw[hc j hj']
       exact ⟨z,MonoidHom.flip_apply _ _ _⟩
      exact Finset.le_sup (f:= fun k=> (κ.flip (c k)).range) (b:=⟨(j:ℕ),hj'⟩)
        (Finset.mem_univ _) hmem
    exact hle hu
  have hcard:ZB L3≤
      (p^Q1p p κ (ZA (g '' {j | (j:ℕ)<s})))^s:=by
    have h1:=Qb0 (fun k=> (κ.flip (c k)).range)
      (p^Q1p p κ (ZA (g '' {j | (j:ℕ)<s}))) Finset.univ
      (fun k _=>Q3u hp hL3 κ _
        (ZC ⟨Fin.castLE hsr k,by simp,rfl⟩))
    rw[Finset.card_univ,Fintype.card_fin]at h1
    rw[← Subgroup.card_top (G:=L3)]
    exact (Subgroup.card_le_of_le hsup).trans h1
  rw[hL3, ← pow_mul]at hcard
  have h2:=Q28 hp.one_lt hcard
  rw[mul_comm]at h2
  exact h2
lemma Q94 [Finite L2] [Finite L3] {p r s s2 s3:ℕ} (hp:p.Prime) (hsr :s≤ r)
    (hL2:ZB L2=p^s2) (hL3:ZB L3=p^s3) (κ:L2→*L1→*L3)
    (g:Fin r→ L1)
    (hgen3:ZA
      {w | ∃ z,∃ u∈ZA (g '' {j | (j:ℕ)<s}),κ z u=w}=⊤):
    s3 ≤ s*Q1p p κ (ZA (g '' {j | (j:ℕ)<s}))∧
      Q1p p κ (ZA (g '' {j | (j:ℕ)<s}))≤ min s2 s3:=
  ⟨Qex hp hsr hL3 κ g hgen3,
    le_min (Qgj hp hL2 hL3 κ _) (Q9y hp hL3 κ _)⟩
lemma Q49 [Finite L1] [Finite L2] [Finite L3]:
    Finite ((L1→*L1→*L2)×(L2→*L1→*L3)):=by
 haveI:Finite (L1→*L2):=
   Finite.of_injective (fun f:L1→*L2=> (f:L1→ L2)) DFunLike.coe_injective
 haveI:Finite (L1→*L3):=
   Finite.of_injective (fun f:L1→*L3=> (f:L1→ L3)) DFunLike.coe_injective
 haveI:Finite (L1→*L1→*L2):=
   Finite.of_injective (fun f:L1→*L1→*L2=> (f:L1→(L1→*L2))) DFunLike.coe_injective
 haveI:Finite (L2→*L1→*L3):=
   Finite.of_injective (fun f:L2→*L1→*L3=> (f:L2→(L1→*L3))) DFunLike.coe_injective
 infer_instance
lemma Q9o [Finite L1] [Finite L2] [Finite L3] {p r s s2 s3 n b:ℕ}
    (hp:p.Prime) (hsr :s≤ r) (hL2:ZB L2=p^s2) (hL3:ZB L3=p^s3)
    (y:Fin n→ L2) (hy:ZA (ZG y)=⊤) (g:Fin r→ L1)
    (hg:ZA (ZG g)=⊤) (D:Finset (Fin r×Fin r))
    (hD:∀ q∈D,q.1<q.2∧(q.1:ℕ)<s) (v:Fin r×Fin r→ L2):
    {β : (L1→*L1→*L2)×(L2→*L1→*L3) | Q21 β.1∧
        ZA {w | ∃ u∈ZA (g '' {j | (j:ℕ)<s}),
          ∃ u'∈ZA (g '' {j | (j:ℕ)<s}),β.1 u u'=w}=⊤∧
        Q1m β.1 β.2∧
        Q1p p β.2 (ZA (g '' {j | (j:ℕ)<s}))=b∧
        ∀ q∈D,β.1 (g q.1) (g q.2)=v q}.ncard≤
      p ^(s*(b*(n+s3+1 - b)))*
        p^((r.choose 2 - D.card)*s2 - (r - s).choose 2*b):=by
  have:=Q49 (L1:=L1) (L2:=L2) (L3:=L3)
  refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
    (Qn7 hp hsr hL2 hL3 y hy g hg D hD v)
  rintro β ⟨hA,hgen,hJ,hb,hDv⟩
  refine ⟨hA,hgen,hJ,?_,?_,hDv⟩
  · intro j hj
    rw[← hb]
    exact Q3u hp hL3 β.2 _ (ZC ⟨j,hj,rfl⟩)
  · rw[← hb]
    exact Qao hp hL3 β.2 _
lemma Q78 {ι α:Type*} [DecidableEq ι] (I:Finset ι) (T:ι→ Set α):
    (⋃ i∈I,T i).ncard≤∑ i∈I,(T i).ncard:=by
 refine Finset.induction_on I ?_ ?_
 · simp
 · intro a J ha ih
   rw[Finset.set_biUnion_insert,Finset.sum_insert ha]
   exact (Set.ncard_union_le _ _).trans (Nat.add_le_add_left ih _)
lemma Qk5 [Finite L1] [Finite L2] [Finite L3] {p r s s2 s3 n:ℕ}
    (hp:p.Prime) (hsr :s≤ r) (hL2:ZB L2=p^s2) (hL3:ZB L3=p^s3)
    (y:Fin n→ L2) (hy:ZA (ZG y)=⊤) (g:Fin r→ L1)
    (hg:ZA (ZG g)=⊤) (D:Finset (Fin r×Fin r))
    (hD:∀ q∈D,q.1<q.2∧(q.1:ℕ)<s) (v:Fin r×Fin r→ L2):
    {β : (L1→*L1→*L2)×(L2→*L1→*L3) | Q21 β.1∧
        ZA {w | ∃ u∈ZA (g '' {j | (j:ℕ)<s}),
          ∃ u'∈ZA (g '' {j | (j:ℕ)<s}),β.1 u u'=w}=⊤∧
        Q1m β.1 β.2∧
        ZA
          {w | ∃ z,∃ u∈ZA (g '' {j | (j:ℕ)<s}),β.2 z u=w}=⊤∧
        ∀ q∈D,β.1 (g q.1) (g q.2)=v q}.ncard≤
      ∑ b ∈(ZQ (min s2 s3+1)).filter (fun b=>s3≤ s*b),
        p ^(s*(b*(n+s3+1 - b)))*
          p^((r.choose 2 - D.card)*s2 - (r - s).choose 2*b):=by
  classical
  have:=Q49 (L1:=L1) (L2:=L2) (L3:=L3)
  set I:=(ZQ (min s2 s3+1)).filter (fun b=>s3≤ s*b) with hI
  obtain ⟨T,hT⟩:∃ T:ℕ→ Set ((L1→*L1→*L2)×(L2→*L1→*L3)),T= fun b=>
    {β | Q21 β.1∧
        ZA {w | ∃ u∈ZA (g '' {j | (j:ℕ)<s}),
          ∃ u'∈ZA (g '' {j | (j:ℕ)<s}),β.1 u u'=w}=⊤∧
        Q1m β.1 β.2∧
        Q1p p β.2 (ZA (g '' {j | (j:ℕ)<s}))=b∧
        ∀ q∈D,β.1 (g q.1) (g q.2)=v q}:=⟨_,rfl⟩
  have hsub:{β:(L1→*L1→*L2)×(L2→*L1→*L3) | Q21 β.1∧
        ZA {w | ∃ u∈ZA (g '' {j | (j:ℕ)<s}),
          ∃ u'∈ZA (g '' {j | (j:ℕ)<s}),β.1 u u'=w}=⊤∧
        Q1m β.1 β.2∧
        ZA
          {w | ∃ z,∃ u∈ZA (g '' {j | (j:ℕ)<s}),β.2 z u=w}=⊤∧
        ∀ q∈D,β.1 (g q.1) (g q.2)=v q}⊆ ⋃ b∈I,T b:=by
    rintro β ⟨hA,hgen,hJ,hgen3,hDv⟩
    obtain ⟨h51,hmin⟩:=Q94 hp hsr hL2 hL3 β.2 g hgen3
    refine Set.mem_iUnion₂.2 ⟨Q1p p β.2 (ZA (g '' {j | (j:ℕ)<s})),?_,?_⟩
    · rw[hI,Finset.mem_filter,Finset.mem_range]
      exact ⟨Nat.lt_succ_of_le hmin,h51⟩
    · rw[hT]
      exact ⟨hA,hgen,hJ,rfl,hDv⟩
  calc _≤(⋃ b∈I,T b).ncard:=Set.ncard_le_ncard hsub (Set.toFinite _)
    _≤∑ b∈I,(T b).ncard:=Q78 I T
    _ ≤_:=Finset.sum_le_sum fun b _=>by
      rw[hT]
      exact Q9o hp hsr hL2 hL3 y hy g hg D hD v
lemma Qgh {Γ:Type*} [Finite Γ] {ι:Type*} [DecidableEq ι] {p m3:ℕ}
    (hΓ:ZB Γ=p^m3) (P D:Finset (ι×ι)) (hDP:D⊆P) (c0:ι×ι→Γ):
    {c:ι×ι→Γ | ∀ q,q∉P \ D→ c q= c0 q}.ncard≤p^((P.card - D.card)*m3):=by
  classical
  let F:(ι×ι→Γ)→(↥(P \ D)→Γ):= fun c q=>c q.1
  have hinj:Set.InjOn F {c:ι×ι→Γ | ∀ q,q∉P \ D→ c q= c0 q}:=by
    intro c hc c' hc' he
    funext q
    by_cases hq:q∈P \ D
    · exact congrFun he ⟨q,hq⟩
    · rw[hc q hq,hc' q hq]
  have hk:(P \ D).card=P.card - D.card:=by
   have:=Finset.card_sdiff_add_card_eq_card hDP
   omega
  calc _ ≤ZB (↥(P \ D)→Γ):=Q26 _ F hinj
    _ = p^((P.card - D.card)*m3):=by
      rw [Nat.card_fun,Nat.card_eq_fintype_card (α:=↥(P \ D)),Fintype.card_coe,hk,hΓ,
        ← pow_mul]
      ring
lemma Q74 {Γ:Type*} [Finite Γ] {p r m3:ℕ} (hΓ:ZB Γ=p^m3)
    (D:Finset (Fin r×Fin r)) (hD:∀ q∈D,q.1<q.2) (c0:Fin r×Fin r→Γ):
    {c :Fin r×Fin r→Γ | ∀ q,q∉(Finset.univ.filter (fun q:Fin r×Fin r=>q.1<q.2)) \ D→
      c q= c0 q}.ncard≤p^((r.choose 2 - D.card)*m3):=by
  classical
  have hTc:(Finset.univ.filter (fun q:Fin r×Fin r=>q.1<q.2)).card=r.choose 2:=by
    have h0:=Q4e r 0
    rw[Nat.sub_zero]at h0
    rw[← h0]
    congr 1
    ext q
    simp
  have hDP:D⊆Finset.univ.filter (fun q:Fin r×Fin r=>q.1<q.2):=by
    intro q hq
    rw[Finset.mem_filter]
    exact ⟨Finset.mem_univ _,hD q hq⟩
  have h:=Qgh hΓ _ D hDP c0
  rwa[hTc]at h
end BrBreadth
section BrLemma61
variable {L1 L2:Type*} [CommGroup L1] [CommGroup L2]
def Qa9 {A B:Type*} [CommGroup A] [CommGroup B] (γ:A→*A→*B) (S:Subgroup A):
    Subgroup B:=
  ZA {w | ∃ a∈S,∃ b∈S,γ a b=w}
lemma Qc9 {A B:Type*} [CommGroup A] [CommGroup B] [Finite A] [Finite B]
    {p k:ℕ} (hp:p.Prime) (γ:A→*A→*B) (hA:Q21 γ) (hk:ZB A=p^k):
    ZB (ZA {w | ∃ a b:A,γ a b=w})≤p^k.choose 2:=by
  classical
  haveI:=Fintype.ofFinite A
  have main : ∀ T:Finset A,∀ j,ZB (ZA (T:Set A))=p^j→
      ZB (Qa9 γ (ZA (T:Set A)))≤p^j.choose 2:=by
   intro T
   refine Finset.induction_on T ?_ ?_
   · intro j _
     have hbot:Qa9 γ (ZA ((∅ :Finset A):Set A))=⊥:=by
      rw[eq_bot_iff,Qa9,ZD]
      rintro _ ⟨a,ha,b, -,rfl⟩
      simp only[Finset.coe_empty,Subgroup.closure_empty,Subgroup.mem_bot]at ha
      rw[ha,map_one,MonoidHom.one_apply]
      exact Subgroup.one_mem _
     rw[hbot,Subgroup.card_bot]
     exact Nat.one_le_pow _ _ hp.pos
   · intro x T _ ih j hj
     set S':=ZA (T:Set A) with hS'def
     set S:=ZA ((insert x T:Finset A):Set A) with hSdef
     have hS:S=ZA {x}⊔S':=by
      rw[hSdef,Finset.coe_insert,Set.insert_eq,Subgroup.closure_union]
     have hdS':ZB S'∣p^k:=by
      rw[← hk]
      exact Subgroup.card_subgroup_dvd_card S'
     obtain ⟨j', -,hj'⟩:=(Nat.dvd_prime_pow hp).1 hdS'
     have IH:=ih j' hj'
     have hle:S'≤S:=by rw[hS]; exact le_sup_right
     by_cases heq:S'=S
     · rw[← heq,hj']at hj
       have hjj:j'=j:=Nat.pow_right_injective hp.two_le hj
       rw[← heq, ← hjj]
       exact IH
     · have hne:ZB S'≠ZB S:= fun h'=>
         heq (Subgroup.eq_of_le_of_card_ge hle h'.symm.le)
       have hdvd:=Subgroup.card_dvd_of_le hle
       rw[hj',hj]at hdvd
       rw[hj',hj]at hne
       have h1:j'≤j:=(Nat.pow_dvd_pow_iff_le_right hp.one_lt).1 hdvd
       have h2:j'≠j:= fun h'=>hne (by rw[h'])
       have hlt:j'+1≤j:=by omega
       let R:=S'.map (γ.flip x)
       set Qs:=Qa9 γ S'⊔R with hQs
       have f1:∀ b∈S,γ x b∈Qs:=by
        have hc:S≤Qs.comap (γ x):=by
         rw[hS]
         refine sup_le ?_ ?_
         · rw[ZD,Set.singleton_subset_iff]
           show γ x x∈Qs
           rw[hA x]
           exact Subgroup.one_mem _
         · intro b' hb'
           show γ x b'∈Qs
           rw[Q24 hA b' x]
           exact ZL (Subgroup.inv_mem _
             (Subgroup.mem_map.2 ⟨b',hb',MonoidHom.flip_apply _ _ _⟩))
        exact fun b hb=>hc hb
       have f2:∀ a'∈S',∀ b∈S,γ a' b∈Qs:=by
        intro a' ha'
        have hc:S≤Qs.comap (γ a'):=by
         rw[hS]
         refine sup_le ?_ ?_
         · rw [ZD,Set.singleton_subset_iff]
           show γ a' x∈Qs
           exact ZL
             (Subgroup.mem_map.2 ⟨a',ha',MonoidHom.flip_apply _ _ _⟩)
         · intro b' hb'
           show γ a' b'∈Qs
           exact ZJ (ZC ⟨a',ha',b',hb',rfl⟩)
        exact fun b hb=>hc hb
       have f3:∀ b∈S,S≤Qs.comap (γ.flip b):=by
        intro b hb
        rw[hS]
        refine sup_le ?_ ?_
        · rw[ZD,Set.singleton_subset_iff]
          show γ.flip b x∈Qs
          rw[MonoidHom.flip_apply]
          exact f1 b hb
        · intro a' ha'
          show γ.flip b a'∈Qs
          rw[MonoidHom.flip_apply]
          exact f2 a' ha' b hb
       have hsub:Qa9 γ S≤Qs:=by
        rw[Qa9,ZD]
        rintro _ ⟨a,ha,b,hb,rfl⟩
        have:= f3 b hb ha
        rw[Subgroup.mem_comap,MonoidHom.flip_apply]at this
        exact this
       have hR:ZB R≤ZB S':=
         Nat.card_le_card_of_surjective _ (MonoidHom.subgroupMap_surjective (γ.flip x) S')
       calc ZB (Qa9 γ S)≤ZB ↥Qs:=Subgroup.card_le_of_le hsub
         _≤ZB (Qa9 γ S')*ZB R:=Q7j _ _
         _≤p^j'.choose 2*p^j':=Nat.mul_le_mul IH (hR.trans hj'.le)
         _ = p^(j'+1).choose 2:=by
             rw[Nat.choose_succ_succ',Nat.choose_one_right,pow_add,mul_comm]
         _≤p^j.choose 2:=Nat.pow_le_pow_right hp.pos (Nat.choose_le_choose 2 hlt)
  have key:=main Finset.univ k (by rw[Finset.coe_univ,Subgroup.closure_univ,
    Subgroup.card_top,hk])
  have e:Qa9 γ (ZA ((Finset.univ:Finset A):Set A))=
      ZA {w | ∃ a b:A,γ a b=w}:=by
    rw[Finset.coe_univ,Subgroup.closure_univ,Qa9]
    congr 1
    ext w
    simp
  rw[← e]
  exact key
lemma Ql8 [Finite L1] [Finite L2] {p δ:ℕ} (hp:p.Prime) (β:L1→*L1→*L2)
    (hA:Q21 β) (hgen:ZA (ZG (fun q:L1×L1=>β q.1 q.2))=⊤)
    (hd:ZB (powMonoidHom p:L1→*L1).range=p^δ):
    ZB (powMonoidHom p:L2→*L2).range≤p^δ.choose 2:=by
  classical
  set P:=(powMonoidHom p:L1→*L1).range with hP
  have hroot:∀ a:P,∃ x:L1,x^p=(a:L1):= fun a=>by
    obtain ⟨x,hx⟩:=MonoidHom.mem_range.1 a.2
    exact ⟨x,hx⟩
  let r :P→ L1:= fun a=>Classical.choose (hroot a)
  have hr :∀ a,r a^p=(a:L1):= fun a=>Classical.choose_spec (hroot a)
  have hvan:∀ k:L1,k^p=1→∀ b:P,β k (b:L1)=1:=by
   intro k hk b
   obtain ⟨y,hy⟩:=hroot b
   rw[← hy,map_pow, ← Q51,hk,map_one,MonoidHom.one_apply]
  let γ:P→*P→*L2:=MonoidHom.mk' (fun a=> (β (r a)).comp P.subtype) (by
    intro a a'
    ext b
    simp only[MonoidHom.comp_apply,Subgroup.coe_subtype,MonoidHom.mul_apply]
    have hk:(r (a*a')*(r a*r a')⁻¹)^p=1:=by
     rw[mul_pow,inv_pow,mul_pow,hr,hr,hr]
     simp
    have h0:=hvan _ hk b
    simp only[map_mul,map_inv,MonoidHom.mul_apply,MonoidHom.inv_apply]at h0
    exact mul_inv_eq_one.mp h0)
  have hγ:∀ a b:P,γ a b=β (r a) (b:L1):= fun a b=>rfl
  have hAγ:Q21 γ:=by
   intro a
   rw[hγ]
   conv_lhs=>rw[← hr a]
   rw[map_pow,hA (r a),one_pow]
  have hQ:(powMonoidHom p:L2→*L2).range≤ZA {w | ∃ a b:P,γ a b=w}:=by
    have h1:ZA (ZG (fun q:L1×L1=>β q.1 q.2))≤
        (ZA {w | ∃ a b:P,γ a b=w}).comap (powMonoidHom p):=by
      rw[ZD]
      rintro _ ⟨⟨x,y⟩,rfl⟩
      show powMonoidHom p (β x y)∈ZA {w | ∃ a b:P,γ a b=w}
      rw[powMonoidHom_apply]
      apply ZC
      let ax:P:=⟨x^p,x,rfl⟩
      let ay:P:=⟨y^p,y,rfl⟩
      refine ⟨ax,ay,?_⟩
      have e1:r ax^p=x^p:=hr ax
      calc γ ax ay=β (r ax) (y^p):=rfl
        _=(β (r ax) y)^p:=map_pow _ _ _
        _=β (r ax^p) y:=(Q51 β _ y p).symm
        _=β (x^p) y:=by rw[e1]
        _=(β x y)^p:=Q51 β x y p
    rw[hgen]at h1
    rintro _ ⟨z,rfl⟩
    exact h1 (ZM z)
  calc ZB (powMonoidHom p:L2→*L2).range
      ≤ZB (ZA {w | ∃ a b:P,γ a b=w}):=Subgroup.card_le_of_le hQ
    _≤p^δ.choose 2:=Qc9 hp γ hAγ hd
lemma Qdp {L:Type*} [CommGroup L] [Finite L] {n:ℕ} (hn:0<n)
    (hexp:∀ z:L,z^n=1) (T:Finset L) (hT:ZA (T:Set L)=⊤):
    ZB L≤n^T.card:=by
 classical
 have main:∀ T:Finset L,ZB (ZA (T:Set L))≤n^T.card:=by
  intro T
  refine Finset.induction_on T ?_ ?_
  · simp
  · intro x T hx ih
    rw [Finset.coe_insert,Set.insert_eq,Subgroup.closure_union,Finset.card_insert_eq_ite,
      if_neg hx,pow_succ,mul_comm]
    refine le_trans (Q7j _ _) (Nat.mul_le_mul ?_ ih)
    rw[← Subgroup.zpowers_eq_closure,Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hn (hexp x)
 have h:=main T
 rwa[hT,Subgroup.card_top]at h
lemma Qmn [Finite L1] [Finite L2] {p δ:ℕ} (hp:p.Prime) (β:L1→*L1→*L2)
    (hgen:ZA (ZG (fun q:L1×L1=>β q.1 q.2))=⊤)
    (hd:ZB (powMonoidHom p:L1→*L1).range=p^δ) (T:Finset L2)
    (hT:ZA (T:Set L2)=⊤):
    ZB L2≤p^((δ+1)*T.card):=by
  have hx:∀ x:L1,x^(p^(δ+1))=1:=by
   intro x
   have h1:(⟨x^p,x,rfl⟩:(powMonoidHom p:L1→*L1).range)^
       ZB (powMonoidHom p:L1→*L1).range=1:=pow_card_eq_one'
   rw[hd]at h1
   have h2:= congrArg Subtype.val h1
   simp only[SubgroupClass.coe_pow,OneMemClass.coe_one]at h2
   rw[pow_succ',pow_mul]
   exact h2
  have hz:∀ z:L2,z^(p^(δ+1))=1:=by
   have hle:ZA (ZG (fun q:L1×L1=>β q.1 q.2))≤
       (powMonoidHom (p^(δ+1)):L2→*L2).ker :=by
     rw[ZD]
     rintro _ ⟨⟨x,y⟩,rfl⟩
     show (β x y)^(p^(δ+1))=1
     rw[← Q51,hx,map_one,MonoidHom.one_apply]
   rw[hgen]at hle
   intro z
   exact (MonoidHom.mem_ker).1 (hle (ZM z))
  have h:=Qdp (Nat.pos_of_ne_zero (pow_ne_zero _ hp.ne_zero)) hz T hT
  rwa[← pow_mul]at h
end BrLemma61
section BrGroup
variable {G:Type u} [Group G]
lemma Q9v {H:Type*} [Group H] (N:Subgroup H) [N.Normal] {x y:H}
    (h:x*y⁻¹∈N):ZF N x =ZF N y:=by
 have h1:ZF N (x*y⁻¹)=1:=by
  rw[← MonoidHom.mem_ker,QuotientGroup.ker_mk']
  exact h
 rw[map_mul,map_inv]at h1
 exact mul_inv_eq_one.mp h1
lemma Qcg {A B:Subgroup G} [(B.subgroupOf A).Normal]
    (h:∀ x∈A,∀ y∈A,⁅x,y⁆∈B) (a b:A⧸B.subgroupOf A):a*b=b*a:=by
 obtain ⟨x,rfl⟩:=QuotientGroup.mk'_surjective (B.subgroupOf A) a
 obtain ⟨y,rfl⟩:=QuotientGroup.mk'_surjective (B.subgroupOf A) b
 rw[← map_mul, ← map_mul]
 apply Q9v
 rw[Subgroup.mem_subgroupOf]
 show (x:G)*(y:G)*((y:G)*(x:G))⁻¹∈B
 have e:(x:G)*(y:G)*((y:G)*(x:G))⁻¹=⁅(x:G),(y:G)⁆:=by
  simp only[commutatorElement_def]
  group
 rw[e]
 exact h _ x.2 _ y.2
variable (G) in
def Q2f:Type u:=lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1)
variable (G) in
def Q5p:Type u:=lcs G 2⧸(lcs G 3).subgroupOf (lcs G 2)
noncomputable instance Q2f.instCommGroup:CommGroup (Q2f G):=
  { (inferInstance:Group (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1))) with
    mul_comm:=Qcg (A:=lcs G 1) (B:=lcs G 2) (fun x hx y hy=>
      Qd (by norm_num) (Q1c hx hy)) }
noncomputable instance Q5p.instCommGroup:CommGroup (Q5p G):=
  { (inferInstance:Group (lcs G 2⧸(lcs G 3).subgroupOf (lcs G 2))) with
    mul_comm:=Qcg (A:=lcs G 2) (B:=lcs G 3) (fun x hx y hy=>
      Qd (by norm_num) (Q1c hx hy)) }
instance Q2f.instFinite [Finite G]:Finite (Q2f G):=
  inferInstanceAs (Finite (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1)))
instance Q5p.instFinite [Finite G]:Finite (Q5p G):=
  inferInstanceAs (Finite (lcs G 2⧸(lcs G 3).subgroupOf (lcs G 2)))
variable (G) in
noncomputable def Q1z:lcs G 1→*Q2f G:=ZF ((lcs G 2).subgroupOf (lcs G 1))
variable (G) in
noncomputable def Q36:lcs G 2→*Q5p G:=ZF ((lcs G 3).subgroupOf (lcs G 2))
lemma Q4z:Function.Surjective (Q1z G):=
  QuotientGroup.mk'_surjective ((lcs G 2).subgroupOf (lcs G 1))
lemma Q3b (w:lcs G 1):Q1z G w=1↔(w:G)∈lcs G 2:=by
 have hk:(Q1z G).ker=(lcs G 2).subgroupOf (lcs G 1):=
   QuotientGroup.ker_mk' ((lcs G 2).subgroupOf (lcs G 1))
 rw[← MonoidHom.mem_ker,hk,Subgroup.mem_subgroupOf]
lemma Q38 (w:lcs G 2):Q36 G w=1↔(w:G)∈lcs G 3:=by
 have hk:(Q36 G).ker=(lcs G 3).subgroupOf (lcs G 2):=
   QuotientGroup.ker_mk' ((lcs G 3).subgroupOf (lcs G 2))
 rw[← MonoidHom.mem_ker,hk,Subgroup.mem_subgroupOf]
lemma Qgc {a b:lcs G 1} (h:(a:G)*(b:G)⁻¹∈lcs G 2):
    Q1z G a=Q1z G b:=by
 have h1:Q1z G (a*b⁻¹)=1:=(Q3b _).2 h
 rw[map_mul,map_inv]at h1
 exact mul_inv_eq_one.mp h1
lemma Qfa {a b:lcs G 2} (h:(a:G)*(b:G)⁻¹∈lcs G 3):
    Q36 G a=Q36 G b:=by
 have h1:Q36 G (a*b⁻¹)=1:=(Q38 _).2 h
 rw[map_mul,map_inv]at h1
 exact mul_inv_eq_one.mp h1
def Q7s (w:lcs G 1) (y:G):lcs G 2:=⟨⁅(w:G),y⁆,Qb w.2 y⟩
lemma Qdh (x y z:G):
    Q1z G (cw x (y *z))=Q1z G (cw x y)*Q1z G (cw x z):=by
 rw[← map_mul]
 apply Qgc
 show ⁅x,y *z⁆*(⁅x,y⁆*⁅x,z⁆)⁻¹∈lcs G 2
 rw[Q33]
 have hc:⁅y,⁅x,z⁆⁆∈lcs G 2:=
   Qj y (Qj (n:=0) x (ZM z))
 have e:⁅x,y⁆*⁅y,⁅x,z⁆⁆*⁅x,z⁆*(⁅x,y⁆*⁅x,z⁆)⁻¹=
     ⁅x,y⁆*⁅y,⁅x,z⁆⁆*⁅x,y⁆⁻¹:=by group
 rw[e]
 exact Subgroup.Normal.conj_mem inferInstance _ hc _
lemma Qep (x x' y:G):
    Q1z G (cw (x*x') y)=Q1z G (cw x y)*Q1z G (cw x' y):=by
 rw[mul_comm (Q1z G (cw x y)), ← map_mul]
 apply Qgc
 show ⁅x*x',y⁆*(⁅x',y⁆*⁅x,y⁆)⁻¹∈lcs G 2
 rw[Q2g]
 have e:⁅x,⁅x',y⁆⁆*⁅x',y⁆*⁅x,y⁆*(⁅x',y⁆*⁅x,y⁆)⁻¹=⁅x,⁅x',y⁆⁆:=by group
 rw[e]
 exact Qj x (Qj (n:=0) x' (ZM y))
lemma Qcs (w:lcs G 1) (y z:G):
    Q36 G (Q7s w (y *z))=Q36 G (Q7s w y)*Q36 G (Q7s w z):=by
 rw[← map_mul]
 apply Qfa
 show ⁅(w:G),y *z⁆*(⁅(w:G),y⁆*⁅(w:G),z⁆)⁻¹∈lcs G 3
 rw[Q33]
 have hc:⁅y,⁅(w:G),z⁆⁆∈lcs G 3:=
   Qj y (Qb w.2 z)
 have e:⁅(w:G),y⁆*⁅y,⁅(w:G),z⁆⁆*⁅(w:G),z⁆*(⁅(w:G),y⁆*⁅(w:G),z⁆)⁻¹=
     ⁅(w:G),y⁆*⁅y,⁅(w:G),z⁆⁆*⁅(w:G),y⁆⁻¹:=by group
 rw[e]
 exact Subgroup.Normal.conj_mem inferInstance _ hc _
lemma Qdq (w w':lcs G 1) (y:G):
    Q36 G (Q7s (w*w') y)=Q36 G (Q7s w y)*Q36 G (Q7s w' y):=by
 rw[mul_comm (Q36 G (Q7s w y)), ← map_mul]
 apply Qfa
 show ⁅(w:G)*(w':G),y⁆*(⁅(w':G),y⁆*⁅(w:G),y⁆)⁻¹∈lcs G 3
 rw[Q2g]
 have e:⁅(w:G),⁅(w':G),y⁆⁆*⁅(w':G),y⁆*⁅(w:G),y⁆*
     (⁅(w':G),y⁆*⁅(w:G),y⁆)⁻¹=⁅(w:G),⁅(w':G),y⁆⁆:=by group
 rw[e]
 exact Qj (w:G) (Qb w'.2 y)
noncomputable def Q96 (x:G):G→*Q2f G:=
  MonoidHom.mk' (fun y=>Q1z G (cw x y)) (fun y z=>Qdh x y z)
noncomputable def Q8x (w:lcs G 1):G→*Q5p G:=
  MonoidHom.mk' (fun y=>Q36 G (Q7s w y)) (fun y z=>Qcs w y z)
lemma Qli (x x':G):Q96 (x*x')=Q96 x*Q96 x':=by
 ext y
 rw[MonoidHom.mul_apply]
 exact Qep x x' y
lemma Qki (w w':lcs G 1):Q8x (w*w')=Q8x w*Q8x w':=by
 ext y
 rw[MonoidHom.mul_apply]
 exact Qdq w w' y
lemma Qe0 {A:Type*} [CommGroup A] (f f':G→*A):
    Abelianization.lift (f*f')=Abelianization.lift f*Abelianization.lift f':=by
 apply Abelianization.hom_ext
 ext y
 simp only[MonoidHom.comp_apply,MonoidHom.mul_apply,Abelianization.lift_apply_of]
variable (G) in
noncomputable def Qbj:Abelianization G→*Abelianization G→*Q2f G:=
  Abelianization.lift (MonoidHom.mk' (fun x =>Abelianization.lift (Q96 x))
    (fun x x'=>by
      show Abelianization.lift (Q96 (x*x'))=
        Abelianization.lift (Q96 x)*Abelianization.lift (Q96 x')
      rw[Qli,Qe0]))
variable (G) in
noncomputable def Qew:Q2f G→*Abelianization G→*Q5p G:=
  QuotientGroup.lift ((lcs G 2).subgroupOf (lcs G 1))
    (MonoidHom.mk' (fun w=>Abelianization.lift (Q8x w))
      (fun w w'=>by
        show Abelianization.lift (Q8x (w*w'))=
          Abelianization.lift (Q8x w)*Abelianization.lift (Q8x w')
        rw[Qki,Qe0]))
    (by
      intro w hw
      rw[MonoidHom.mem_ker]
      apply Abelianization.hom_ext
      ext y
      show Q36 G (Q7s w y)=1
      rw[Q38]
      rw[Subgroup.mem_subgroupOf]at hw
      exact Qb hw y)
lemma Qap (x y:G):
    Qbj G (ZH x) (ZH y)=Q1z G (cw x y):=rfl
lemma Q6k (w:lcs G 1) (z:G):
    Qew G (Q1z G w) (ZH z)=Q36 G (Q7s w z):=rfl
lemma Q30:Function.Surjective (ZH:G→*Abelianization G):=
  fun a=>QuotientGroup.induction_on a fun x => ⟨x,rfl⟩
instance Qnc [Finite G]:Finite (Abelianization G):=
  Finite.of_surjective _ Q30
lemma Qiv:Q21 (Qbj G):=by
 intro a
 obtain ⟨x,rfl⟩:=Q30 a
 rw[Qap,Q3b]
 show ⁅x,x⁆∈lcs G 2
 rw[commutatorElement_self]
 exact Subgroup.one_mem _
lemma Qcm:
    ZA (ZG (fun q:Abelianization G×Abelianization G=>
      Qbj G q.1 q.2))=⊤:=by
  set K:=ZA (ZG (fun q:Abelianization G×Abelianization G=>
      Qbj G q.1 q.2)) with hK
  have hcw:∀ a b:G,cw a b∈K.comap (Q1z G):=by
   intro a b
   rw[Subgroup.mem_comap]
   exact ZC ⟨(ZH a,ZH b),rfl⟩
  have hle:commutator G≤(K.comap (Q1z G)).map (lcs G 1).subtype:=by
   rw[commutator_eq_closure,ZD]
   rintro _ ⟨a,b,rfl⟩
   exact Subgroup.mem_map.2 ⟨cw a b,hcw a b,rfl⟩
  rw[eq_top_iff]
  intro q _
  obtain ⟨w,rfl⟩:=Q4z q
  have hw:(w:G)∈commutator G:=by
   rw[Q1s]
   exact w.2
  obtain ⟨w',hw',hww⟩:=Subgroup.mem_map.1 (hle hw)
  have:w'=w:=Subtype.ext hww
  rw[← this]
  exact hw'
lemma Qj2 (a b c:G):
    ⁅⁅a,b⁆,b*c*b⁻¹⁆*⁅⁅b,c⁆,c*a*c⁻¹⁆*⁅⁅c,a⁆,a*b*a⁻¹⁆=1:=by
 simp only[commutatorElement_def]
 group
lemma Q64 {w:G} (hw:w∈lcs G 1) (y z:G):
    ⁅w,z⁆*⁅w,y *z*y⁻¹⁆⁻¹∈lcs G 3:=by
 have e:y *z*y⁻¹=⁅y,z⁆*z:=by
  simp only[commutatorElement_def]
  group
 rw[e,Q33]
 have h1:⁅w,⁅y,z⁆⁆∈lcs G 3:=
   Q1c (a:=1) (b:=1) hw (Qo y z)
 have h2:⁅⁅y,z⁆,⁅w,z⁆⁆∈lcs G 3:=
   Qd (show 3≤1+2+1 by norm_num) (Q1c (a:=1) (b:=2)
     (Qo y z) (Qb hw z))
 have e2:⁅w,z⁆*(⁅w,⁅y,z⁆⁆*⁅⁅y,z⁆,⁅w,z⁆⁆*⁅w,z⁆)⁻¹=
     ⁅⁅y,z⁆,⁅w,z⁆⁆⁻¹*⁅w,⁅y,z⁆⁆⁻¹:=by group
 rw[e2]
 exact mul_mem (inv_mem h2) (inv_mem h1)
lemma Qkz:Q1m (Qbj G) (Qew G):=by
 intro a b c
 obtain ⟨x,rfl⟩:=Q30 a
 obtain ⟨y,rfl⟩:=Q30 b
 obtain ⟨z,rfl⟩:=Q30 c
 rw [Qap,Qap,Qap,Q6k,Q6k,Q6k, ← map_mul, ← map_mul,
   Q38]
 show ⁅⁅x,y⁆,z⁆*⁅⁅y,z⁆,x⁆*⁅⁅z,x⁆,y⁆∈lcs G 3
 have h1:=Q64 (Qo x y) y z
 have h2:=Q64 (Qo y z) z x
 have h3:=Q64 (Qo z x) x y
 have key:ZF (lcs G 3) (⁅⁅x,y⁆,z⁆*⁅⁅y,z⁆,x⁆*⁅⁅z,x⁆,y⁆)=1:=by
  rw [map_mul,map_mul,Q9v _ h1,Q9v _ h2,Q9v _ h3, ← map_mul, ← map_mul,
    Qj2,map_one]
 rwa[← MonoidHom.mem_ker,QuotientGroup.ker_mk']at key
variable {p:ℕ} [hp:Fact p.Prime] [Finite G]
lemma Q9m:ZB (lcs G 1)=ZB (lcs G 2)*ZB (Q2f G):=by
 have h1:=Subgroup.card_mul_index ((lcs G 2).subgroupOf (lcs G 1))
 have h2:=Nat.card_congr (Subgroup.subgroupOfEquivOfLe
   (Qd (D:=G) (show 1≤2 by norm_num))).toEquiv
 rw[h2]at h1
 exact h1.symm
lemma Qku (hG:IsPGroup p G):
    ZB (powMonoidHom p:Q2f G→*Q2f G).range *p^r2 p G=ZB (Q2f G):=by
 have hQ:IsPGroup p (Q2f G):=(hG.to_subgroup (lcs G 1)).to_quotient _
 have h1:(Qv p (Q2f G)).index =p^Group.rank (Q2f G):=Q5j hQ
 have h2:Group.rank (Q2f G)=r2 p G:=Q4x hG
 have h3:Qv p (Q2f G)=(powMonoidHom p:Q2f G→*Q2f G).range:=by
  apply le_antisymm
  · refine sup_le ?_ ?_
    · rw[ZD]
      rintro _ ⟨g,rfl⟩
      exact ⟨g,rfl⟩
    · rw[commutator_def,Subgroup.commutator_le]
      intro g1 _ g2 _
      rw[commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm g1 g2)]
      exact Subgroup.one_mem _
  · rintro _ ⟨g,rfl⟩
    exact ZJ (ZC ⟨g,rfl⟩)
 rw[h3,h2]at h1
 rw[← h1]
 exact Subgroup.card_mul_index _
lemma Qdx (hG:IsPGroup p G):
    ZB (powMonoidHom p:Abelianization G→*Abelianization G).range=
      p^Q3p p G:=by
 have hK:Qdc p G (Qv p G)=(powMonoidHom p:Abelianization G→*Abelianization G).range:=by
  apply le_antisymm _ le_sup_right
  refine sup_le ?_ le_rfl
  rw[Subgroup.map_sup]
  refine sup_le ?_ ?_
  · rw[MonoidHom.map_closure,ZD]
    rintro _ ⟨_,⟨g,rfl⟩,rfl⟩
    exact ⟨ZH g,(map_pow ZH g p).symm⟩
  · rw[Subgroup.map_le_iff_le_comap]
    intro x hx
    rw[Subgroup.mem_comap]
    have h1:ZH x =1:=by
     rw[← MonoidHom.mem_ker,Abelianization.ker_of]
     exact hx
    rw[h1]
    exact Subgroup.one_mem _
 have hV:(Qdc p G (Qv p G)).index =p^Group.rank G:=Qlq hG
 have hAb:ZB (Abelianization G)=p^(Group.rank G+Q3p p G):=by
  rw[← Q4o hG, ← Q1s]
  rfl
 have h1:=Subgroup.card_mul_index (Qdc p G (Qv p G))
 rw[hV,hAb,hK,pow_add,mul_comm (p^Group.rank G)]at h1
 exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero (pow_ne_zero _ hp.out.ne_zero)) h1
lemma Qeg (hG:IsPGroup p G):
    ZB (lcs G 1)≤ZB (lcs G 2)*p^(r2 p G+(Q3p p G).choose 2):=by
 have h61:=Ql8 hp.out (Qbj G) Qiv Qcm (Qdx hG)
 rw[Q9m, ← Qku hG,pow_add,mul_comm (p^r2 p G)]
 exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ h61)
lemma Qgy (hG:IsPGroup p G):
    ZB (lcs G 1)≤ZB (lcs G 2)*p^(r2 p G*(Q3p p G+1)):=by
 obtain ⟨T,hTc,hT⟩:=Group.rank_spec (Q2f G)
 have h:=Qmn hp.out (Qbj G) Qcm (Qdx hG) T hT
 have hr :Group.rank (Q2f G)=r2 p G:=Q4x hG
 rw[hTc,hr,mul_comm]at h
 rw[Q9m]
 exact Nat.mul_le_mul_left _ h
end BrGroup
section BrTransport
variable {G:Type u} [Group G] {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2] [CommGroup L3]
noncomputable def Q4a (e1:Abelianization G≃*L1) (e2:Q2f G≃*L2):L1→*L1→*L2:=
  MonoidHom.mk' (fun x => (e2.toMonoidHom.comp (Qbj G (e1.symm x))).comp e1.symm.toMonoidHom)
    (fun x x'=>by
      ext z
      simp[MonoidHom.comp_apply,MonoidHom.mul_apply,map_mul])
noncomputable def Q4j (e1:Abelianization G≃*L1) (e2:Q2f G≃*L2) (e3:Q5p G≃*L3):
    L2→*L1→*L3:=
  MonoidHom.mk' (fun x => (e3.toMonoidHom.comp (Qew G (e2.symm x))).comp e1.symm.toMonoidHom)
    (fun x x'=>by
      ext z
      simp[MonoidHom.comp_apply,MonoidHom.mul_apply,map_mul])
variable (e1:Abelianization G≃*L1) (e2:Q2f G≃*L2) (e3:Q5p G≃*L3)
lemma Q6t (x y:L1):Q4a e1 e2 x y=e2 (Qbj G (e1.symm x) (e1.symm y)):=rfl
lemma Q70 (z:L2) (x:L1):Q4j e1 e2 e3 z x =e3 (Qew G (e2.symm z) (e1.symm x)):=
  rfl
lemma Qak (a b:G):
    Q4a e1 e2 (e1 (ZH a)) (e1 (ZH b))=e2 (Q1z G (cw a b)):=by
 rw[Q6t,MulEquiv.symm_apply_apply,MulEquiv.symm_apply_apply,Qap]
lemma Qgr (w:lcs G 1) (c:G):
    Q4j e1 e2 e3 (e2 (Q1z G w)) (e1 (ZH c))=e3 (Q36 G (Q7s w c)):=by
 rw[Q70,MulEquiv.symm_apply_apply,MulEquiv.symm_apply_apply,Q6k]
lemma Qmy:Q21 (Q4a e1 e2):=by
 intro x
 rw[Q6t,Qiv,map_one]
lemma Qg6:Q1m (Q4a e1 e2) (Q4j e1 e2 e3):=by
 intro x y z
 rw [Q6t,Q6t,Q6t,Q70,Q70,Q70,
   MulEquiv.symm_apply_apply,MulEquiv.symm_apply_apply,MulEquiv.symm_apply_apply,
   ← map_mul e3, ← map_mul e3,Qkz (G:=G) (e1.symm x) (e1.symm y) (e1.symm z),map_one]
lemma Qif {G':Type u} [Group G'] (e1':Abelianization G'≃*L1)
    (e2':Q2f G'≃*L2) (hT:Q4a e1 e2=Q4a e1' e2') {ι:Type*} (a:ι→G) (a':ι→G')
    (ha:∀ i,e1 (ZH (a i))=e1' (ZH (a' i))) (j k:ι):
    e2 (Q1z G (cw (a j) (a k)))=e2' (Q1z G' (cw (a' j) (a' k))):=by
 rw[← Qak e1 e2, ← Qak e1' e2',hT,ha j,ha k]
lemma Qip {G':Type u} [Group G'] (e1':Abelianization G'≃*L1)
    (e2':Q2f G'≃*L2) (e3':Q5p G'≃*L3) (hT:Q4j e1 e2 e3=Q4j e1' e2' e3')
    (w:lcs G 1) (w':lcs G' 1) (hw:e2 (Q1z G w)=e2' (Q1z G' w')) (c:G) (c':G')
    (hc:e1 (ZH c)=e1' (ZH c')):
    e3 (Q36 G (Q7s w c))=e3' (Q36 G' (Q7s w' c')):=by
 rw[← Qgr e1 e2 e3, ← Qgr e1' e2' e3',hT,hw,hc]
end BrTransport
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section CNT3Defs
def Q1g (m r1 r2 s lam m2 m3 r3:ℕ):Set FiniteGrp.{0}:=
  {G | ZB G=2^m∧
    (⊤:Subgroup G).lowerCentralSeries 2≠⊥∧
    (⊤:Subgroup G).lowerCentralSeries 3=⊥∧
    Group.rank G=r1∧
    Group.rank ((⊤:Subgroup G).lowerCentralSeries 1⧸
      ((⊤:Subgroup G).lowerCentralSeries 2).subgroupOf
        ((⊤:Subgroup G).lowerCentralSeries 1))=r2∧
    sInf {k | ∃ H:Subgroup G,(⊤:Subgroup G).lowerCentralSeries 1=
      ⁅H,H⁆⊔(⊤:Subgroup G).lowerCentralSeries 2∧Group.rank H=k}=s∧
    ((⊤:Subgroup G).lowerCentralSeries 1).index =2^(r1+lam)∧
    ZB ((⊤:Subgroup G).lowerCentralSeries 1)=2^m2∧
    ZB ((⊤:Subgroup G).lowerCentralSeries 2)=2^m3∧
    Group.rank ((⊤:Subgroup G).lowerCentralSeries 2)=r3}
def Q2d (m r1 r2 s lam m2 m3 r3:ℕ):
    Set (Quotient (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0})):=
  Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) '' Q1g m r1 r2 s lam m2 m3 r3
def Q46 (r1 r2 r3 lam m2 m3:ℕ):ℕ:=
  (r1*m2+(r1 - 1)*lam)+(r2*m3+(r2 - 1)*(m2 - m3 - r2))+(r3 - 1)*(m3 - r3)
noncomputable def Q9p (r1 r2 s m2 m3 b2:ℕ):ℝ:=
  ((r1.choose 2:ℝ) - r2)*m2+
    (b2:ℝ)*((s:ℝ)*((r2:ℝ)+m3 - b2+1) - ((r1 - s).choose 2:ℝ))
noncomputable def Q8i (r1 r2 s m2 m3 b2:ℕ):ℝ:=
  Alt2.Qiq r1 r2 s+((r1.choose 2:ℝ) - r2)*((m2:ℝ) - m3 - r2)+
    ((r1.choose 2:ℝ) - r2)*m3+(s:ℝ)*b2*((r2:ℝ)+m3 - b2+1)
def Qmm : Prop:=
  ∃ C : ℝ, ∀ m r1 r2 s lam m2 m3 r3:ℕ,(Q1g m r1 r2 s lam m2 m3 r3).Nonempty→
    ∃ b2 : ℕ,m3≤ s*b2∧b2≤ m2 - m3∧b2≤ m3∧
      Real.logb 2 ((Q2d m r1 r2 s lam m2 m3 r3).ncard:ℝ)≤
        C *(m:ℝ)*((Nat.log 2 m:ℝ)+1)+(Q46 r1 r2 r3 lam m2 m3:ℝ)+
          min (Q9p r1 r2 s m2 m3 b2) (Q8i r1 r2 s m2 m3 b2)
def Q9u (r1 r2 s lam m2 m3:ℕ):Prop:=
  2 ≤ s∧s≤ r1∧s - 1≤ r2∧r2≤ s.choose 2∧m2 - m3 - r2≤lam.choose 2∧
    m2 - m3≤ r2*(lam+1)
def Qhu:Prop:=
  ∀ m r1 r2 s lam m2 m3 r3:ℕ,¬ Q9u r1 r2 s lam m2 m3→
    Q2d m r1 r2 s lam m2 m3 r3= ∅
end CNT3Defs
section CNT3Bridge
variable (G:Type u) [Group G] [Finite G]
noncomputable def Qac:ℕ:=
  sInf {k | ∃ H:Subgroup G,lcs G 1=⁅H,H⁆⊔lcs G 2∧Group.rank H=k}
lemma Qf0 (H:Subgroup G):⁅H,H⁆⊔lcs G 2≤lcs G 1:=by
 refine sup_le ?_ (Qd (by norm_num))
 rw[← Q1s,commutator_def]
 exact Subgroup.commutator_mono le_top le_top
lemma Qb2:Qac G=Qt G:=by
 apply le_antisymm
 · have hne:{k | ∃ u:Fin k→G,
       lcs G 1≤⁅ZA (ZG u),ZA (ZG u)⁆⊔
         lcs G 2}.Nonempty:=by
     let e:Fin (ZB G)→G:=(Finite.equivFin G).symm
     have he:ZG e=Set.univ:=Equiv.range_eq_univ _
     refine ⟨ZB G,e,?_⟩
     rw[he,Subgroup.closure_univ]
     exact le_sup_left
   obtain ⟨u,hu⟩:=Nat.sInf_mem hne
   have hmem:Group.rank (ZA (ZG u))∈
       {k | ∃ H:Subgroup G,lcs G 1=⁅H,H⁆⊔lcs G 2∧Group.rank H=k}:=
     ⟨_,le_antisymm hu (Qf0 G _),rfl⟩
   have h1:=Nat.sInf_le hmem
   have h2:=(Subgroup.rank_congr (congrArg ZA (Qgg u))).le.trans
     (Q8k (Qh9 u) _)
   unfold Qac Qt
   exact h1.trans h2
 · have hneA:{k | ∃ H:Subgroup G,lcs G 1=⁅H,H⁆⊔lcs G 2∧Group.rank H=k}.Nonempty:=
     ⟨_,⊤,(sup_eq_left.mpr (Qd (by norm_num):lcs G 2≤lcs G 1)).symm,rfl⟩
   obtain ⟨H,hH,hk⟩:=Nat.sInf_mem hneA
   obtain ⟨x,hx⟩:=Qc4 H
   unfold Qac Qt
   apply Nat.sInf_le
   refine ⟨fun i=>x i.val,?_⟩
   have e:ZG (fun i:Fin (sInf {k | ∃ H:Subgroup G,
       lcs G 1=⁅H,H⁆⊔lcs G 2∧Group.rank H=k})=>x i.val)=
       x '' ZP (Group.rank H):=by
     rw[hk]
     ext y
     constructor
     · rintro ⟨i,rfl⟩
       exact ⟨i.val,i.isLt,rfl⟩
     · rintro ⟨i,hi,rfl⟩
       exact ⟨⟨i,hi⟩,rfl⟩
   rw[e,hx]
   exact hH.le
variable {G}
lemma Qax [Fact (Nat.Prime 2)] (hG:IsPGroup 2 G):
    Group.rank (lcs G 1⧸(lcs G 2).subgroupOf (lcs G 1))=r2 2 G:=
  Q4x hG
lemma Q9b [Fact (Nat.Prime 2)] (hG:IsPGroup 2 G) (lam:ℕ):
    (lcs G 1).index =2^(Group.rank G+lam)↔Q3p 2 G=lam:=by
 constructor
 · intro h
   have h':=(Q4o hG).symm.trans h
   have:=Nat.pow_right_injective (le_refl 2) h'
   omega
 · rintro rfl
   exact Q4o hG
end CNT3Bridge
section CNT3Mem
variable {m r1 r2 s lam m2 m3 r3:ℕ}
lemma Q43 [Fact (Nat.Prime 2)] (G:FiniteGrp.{0}):
    G ∈ Q1g m r1 r2 s lam m2 m3 r3↔
      ZB G=2^m∧lcs G 2≠⊥∧lcs G 3=⊥∧Group.rank G=r1∧OMA.SimsLite.r2 2 G=r2∧
        Qt G=s∧Q3p 2 G=lam∧ZB (lcs G 1)=2^m2∧
        ZB (lcs G 2)=2^m3∧Group.rank (lcs G 2)=r3:=by
 unfold Q1g
 constructor
 · rintro ⟨hc,h3,h4,hr1,hr2,hs,hidx,hm2,hm3,hr3⟩
   have hp:IsPGroup 2 G:=IsPGroup.of_card hc
   refine ⟨hc,h3,h4,hr1,(Qax hp).symm.trans hr2,
     (Qb2 G).symm.trans hs,?_,hm2,hm3,hr3⟩
   have h:(lcs G 1).index =2^(Group.rank G+lam):=by
    rw[hr1]
    exact hidx
   exact (Q9b hp lam).mp h
 · rintro ⟨hc,h3,h4,hr1,hr2,hs,hl,hm2,hm3,hr3⟩
   have hp:IsPGroup 2 G:=IsPGroup.of_card hc
   refine ⟨hc,h3,h4,hr1,(Qax hp).trans hr2,(Qb2 G).trans hs,?_,
     hm2,hm3,hr3⟩
   have h:=(Q9b hp lam).mpr hl
   rw[hr1]at h
   exact h
lemma Qcl {G:FiniteGrp.{0}} (hG:G∈Q1g m r1 r2 s lam m2 m3 r3):
    m=r1+lam+m2:=by
 obtain ⟨hc, -, -, -, -, -,hidx,hm2, -, -⟩:=hG
 have h:=Subgroup.card_mul_index ((⊤:Subgroup G).lowerCentralSeries 1)
 rw[hidx,hm2,hc, ← pow_add]at h
 have:=Nat.pow_right_injective (le_refl 2) h
 omega
lemma Qcy:(Q2d m r1 r2 s lam m2 m3 r3).Finite:=by
 unfold Q2d
 refine Qgn (m:=m) Nat.prime_two _ ?_
 intro G hG
 refine ⟨hG.1,?_⟩
 intro h
 apply hG.2.1
 rw[eq_bot_iff, ← h]
 exact Qd (by norm_num)
end CNT3Mem
section Qhu
lemma Qae [Fact (Nat.Prime 2)] {G:Type u} [Group G] [Finite G] {m:ℕ}
    (hcard:ZB G=2^m) (h3:lcs G 2≠⊥):
    2 ≤Qt G∧Qt G≤Group.rank G∧Qt G - 1≤ r2 2 G∧
      r2 2 G≤(Qt G).choose 2∧
      ZB (lcs G 1)≤ZB (lcs G 2)*2^(r2 2 G+(Q3p 2 G).choose 2)∧
      ZB (lcs G 1)≤ZB (lcs G 2)*2^(r2 2 G*(Q3p 2 G+1)):=by
 have hG:IsPGroup 2 G:=IsPGroup.of_card hcard
 have hna:lcs G 1≠⊥:=by
  intro h
  apply h3
  rw[eq_bot_iff, ← h]
  exact Qd (by norm_num)
 obtain ⟨u,d,X,r,hs2, -⟩:=Q6y Nat.prime_two hcard hna
 obtain ⟨h1,h2,h3'⟩:=Alt2.Qf8 (p:=2) hG
 exact ⟨hs2,h3',by omega,h2,Qeg hG,Qgy hG⟩
variable {m r1 r2 s lam m2 m3 r3:ℕ}
lemma Q5n {G:FiniteGrp.{0}} (hG:G∈Q1g m r1 r2 s lam m2 m3 r3):
    Q9u r1 r2 s lam m2 m3:=by
 have:Fact (Nat.Prime 2):=⟨Nat.prime_two⟩
 have hG':=(Q43 G).mp hG
 obtain ⟨hc,h3, -,hr1,hr2,hs,hl,hm2,hm3, -⟩:=hG'
 obtain ⟨c1,c2,c3,c4,c5,c6⟩:=Qae hc h3
 rw[hs]at c1 c2 c3 c4
 rw[hr1]at c2
 rw[hr2]at c3 c4 c5 c6
 rw[hl]at c5 c6
 rw[hm2,hm3, ← pow_add]at c5 c6
 have e5:= OMA.SimsLite.Q4c (p:=2) (le_refl 2) c5
 have e6:= OMA.SimsLite.Q4c (p:=2) (le_refl 2) c6
 refine ⟨c1,c2,c3,c4,?_,?_⟩<;>omega
end Qhu
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section NSer
variable {G:Type u} [Group G]
structure Qo3 (F:ℕ→ Subgroup G):Prop where
  normal:∀ i,(F i).Normal
  succ_le:∀ i,F (i+1)≤F i
  comm_le:∀ a b,⁅F a,F b⁆≤F (a+b+1)
variable {F:ℕ→ Subgroup G}
lemma Qiu (g:G):g∈lcs G 0:=by
 rw[lcs_zero]
 exact ZM g
abbrev Qn4 (F:ℕ→ Subgroup G) (i:ℕ):Subgroup (F i):=(F (i+1)).subgroupOf (F i)
abbrev Qo5 (F:ℕ→ Subgroup G) (i:ℕ):Type u:=Additive (Q32 0 (F i) (Qn4 F i))
instance Qnu [Finite G] (F:ℕ→ Subgroup G) (i:ℕ):Finite (Qo5 F i):=by
 have:Finite (Q32 0 (F i) (Qn4 F i)):=
   Finite.of_surjective _ (Q3e (p:=0) (Qn4 F i))
 exact inferInstanceAs (Finite (Additive (Q32 0 (F i) (Qn4 F i))))
section Remark26
variable {p:ℕ}
end Remark26
lemma Q7.Q73 {p c:ℕ} {r :Fin c→ℕ}
    {a:Q6 c r→ℕ} {g:Q6 c r→G} (S:Q7 p a g) (i:Fin c)
    (j v:Fin (r i)) (h:j.val≤v.val):(S.Ql ⟨i,j⟩ ⟨i,v⟩).val=0:=
  S.Qd3.supp ⟨i,j⟩ ⟨i,v⟩ (lt_irrefl _) (fun h'=> (not_lt.mpr h) h'.2)
lemma Q7g {i n:ℕ} (X:Fin n→G) (hX:∀ v,X v∈lcs G i)
    (hgen:ZA (ZG fun v=>
      (QuotientGroup.mk (⟨X v,hX v⟩:lcs G i):Q1r G i))=⊤):
    lcs G i≤ZA (ZG X)⊔lcs G (i+1):=by
  intro x hx
  have hmap:(ZA (ZG fun v=> (⟨X v,hX v⟩:lcs G i))).map
      (ZF ((lcs G (i+1)).subgroupOf (lcs G i)))=⊤:=by
    rw[MonoidHom.map_closure, ← Set.range_comp]
    exact hgen
  have hmem:ZF ((lcs G (i+1)).subgroupOf (lcs G i)) (⟨x,hx⟩:lcs G i)∈
      (ZA (ZG fun v=> (⟨X v,hX v⟩:lcs G i))).map
        (ZF ((lcs G (i+1)).subgroupOf (lcs G i))):=by
    rw[hmap]
    exact ZM _
  obtain ⟨y,hy,hyx⟩:=Subgroup.mem_map.mp hmem
  rw [QuotientGroup.mk'_apply,QuotientGroup.mk'_apply,QuotientGroup.eq,
    Subgroup.mem_subgroupOf]at hyx
  have hle:(ZA (ZG fun v=> (⟨X v,hX v⟩:lcs G i))).map
      (lcs G i).subtype≤ZA (ZG X):=by
    rw[MonoidHom.map_closure,ZD]
    rintro _ ⟨_,⟨v,rfl⟩,rfl⟩
    exact ZC ⟨v,rfl⟩
  have hyc:(y:G)∈ZA (ZG X):=hle ⟨y,hy,rfl⟩
  have e:x =(y:G)*((y⁻¹*⟨x,hx⟩:lcs G i):G):=by simp
  rw[e]
  exact Subgroup.mul_mem_sup hyc hyx
end NSer
section Breadth
variable {C M N:Type*} [AddCommGroup M] [AddCommGroup N]
end Breadth
section GrBreadth
variable {G:Type u} [Group G] {F:ℕ→ Subgroup G}
end GrBreadth
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section LfRecover
variable {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2] [CommGroup L3]
end LfRecover
section LfCore
variable {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2] [CommGroup L3]
lemma Ql0 {β1:L1→*L1→*L2} {β2:L2→*L1→*L3} (hJ:Q1m β1 β2)
    (C:Subgroup L1) (hgen2:ZA {w | ∃ u∈C,∃ v∈C,β1 u v=w}=⊤)
    (hgen3:ZA {w | ∃ z x,β2 z x =w}=⊤):
    ZA {w | ∃ z,∃ u∈C,β2 z u=w}=⊤:=by
  set K:=ZA {w | ∃ z,∃ u∈C,β2 z u=w} with hK
  have hx:∀ x:L1,∀ z:L2,β2 z x∈K:=by
   intro x
   have hle:ZA {w | ∃ u∈C,∃ v∈C,β1 u v=w}≤K.comap (β2.flip x):=by
     rw[ZD]
     rintro _ ⟨u,hu,v,hv,rfl⟩
     rw[SetLike.mem_coe,Subgroup.mem_comap,MonoidHom.flip_apply]
     have e:=hJ u v x
     have hA:β2 (β1 v x) u∈K:=ZC ⟨_,u,hu,rfl⟩
     have hB:β2 (β1 x u) v∈K:=ZC ⟨_,v,hv,rfl⟩
     have e':β2 (β1 u v) x =(β2 (β1 v x) u*β2 (β1 x u) v)⁻¹:=by
      rw[mul_assoc]at e
      exact eq_inv_of_mul_eq_one_left e
     rw[e']
     exact K.inv_mem (K.mul_mem hA hB)
   rw[hgen2]at hle
   intro z
   have h:=hle (ZM z)
   rwa[Subgroup.mem_comap,MonoidHom.flip_apply]at h
  rw[eq_top_iff, ← hgen3,ZD]
  rintro _ ⟨z,x,rfl⟩
  exact hx x z
lemma Q5b (G:Type u) [Group G]:Function.Surjective (Q36 G):=
  QuotientGroup.mk'_surjective ((lcs G 3).subgroupOf (lcs G 2))
lemma Qg8 (G:Type u) [Group G]:
    ZA {w | ∃ z x,Qew G z x =w}=⊤:=by
  set K:=ZA {w | ∃ z x,Qew G z x =w} with hK
  have hle:⁅lcs G 1,(⊤:Subgroup G)⁆≤(K.comap (Q36 G)).map (lcs G 2).subtype:=by
   rw[Subgroup.commutator_def,ZD]
   rintro _ ⟨w,hw,y, -,rfl⟩
   refine Subgroup.mem_map.2 ⟨Q7s ⟨w,hw⟩ y,?_,rfl⟩
   rw[Subgroup.mem_comap, ← Q6k]
   exact ZC ⟨_,_,rfl⟩
  rw[eq_top_iff]
  intro q _
  obtain ⟨w,rfl⟩:=Q5b G q
  obtain ⟨w',hw',hww⟩:=Subgroup.mem_map.1 (hle w.2)
  have:w'=w:=Subtype.ext hww
  rw[← this]
  exact hw'
end LfCore
section LfTransport
lemma Qe5 {G:Type u} [Group G] {L1:Type*} [CommGroup L1]
    (e1:Abelianization G≃*L1) {r s:ℕ} (X:Fin r→G) {a:G}
    (ha:a∈ZA (X '' {j | (j:ℕ)<s})):
    e1 (ZH a)∈
      ZA ((fun j=>e1 (ZH (X j))) '' {j | (j:ℕ)<s}):=by
  have hle:ZA (X '' {j | (j:ℕ)<s})≤
      (ZA ((fun j=>e1 (ZH (X j))) '' {j | (j:ℕ)<s})).comap
        (e1.toMonoidHom.comp ZH):=by
    rw[ZD]
    rintro _ ⟨j,hj,rfl⟩
    rw[SetLike.mem_coe,Subgroup.mem_comap]
    exact ZC ⟨j,hj,rfl⟩
  exact Subgroup.mem_comap.mp (hle ha)
lemma Qcz {G:Type u} [Group G] {L1 L2:Type*} [CommGroup L1] [CommGroup L2]
    (e1:Abelianization G≃*L1) (e2:Q2f G≃*L2) {r s:ℕ} (X:Fin r→G)
    (hcore:lcs G 1≤⁅ZA (X '' {j | (j:ℕ)<s}),
      ZA (X '' {j | (j:ℕ)<s})⁆⊔lcs G 2):
    Subgroup.closure {w | ∃ u∈ZA
        ((fun j=>e1 (ZH (X j))) '' {j | (j:ℕ)<s}),
      ∃ u'∈ZA ((fun j=>e1 (ZH (X j))) '' {j | (j:ℕ)<s}),
        Q4a e1 e2 u u'=w}=⊤:=by
  set K :=ZA {w | ∃ u∈ZA
        ((fun j=>e1 (ZH (X j))) '' {j | (j:ℕ)<s}),
      ∃ u'∈ZA ((fun j=>e1 (ZH (X j))) '' {j | (j:ℕ)<s}),
        Q4a e1 e2 u u'=w} with hK
  have hM :lcs G 1≤(K.comap (e2.toMonoidHom.comp (Q1z G))).map (lcs G 1).subtype:=by
   refine hcore.trans (sup_le ?_ ?_)
   · rw [Subgroup.commutator_le]
     intro a ha b hb
     refine Subgroup.mem_map.2 ⟨cw a b,?_,rfl⟩
     rw[Subgroup.mem_comap,MonoidHom.comp_apply]
     have e:e2.toMonoidHom (Q1z G (cw a b))=
         Q4a e1 e2 (e1 (ZH a)) (e1 (ZH b)):=
       (Qak e1 e2 a b).symm
     rw[e]
     exact ZC ⟨_,Qe5 e1 X ha,_,Qe5 e1 X hb,rfl⟩
   · intro x hx
     have hx1:x∈lcs G 1:=Qd (by norm_num) hx
     refine Subgroup.mem_map.2 ⟨⟨x,hx1⟩,?_,rfl⟩
     rw[Subgroup.mem_comap,MonoidHom.comp_apply]
     have h1:Q1z G ⟨x,hx1⟩=1:=(Q3b _).2 hx
     rw[h1,map_one]
     exact K.one_mem
  rw[eq_top_iff]
  intro q _
  obtain ⟨w,hw⟩:=Q4z (e2.symm q)
  obtain ⟨w',hw',hww⟩:=Subgroup.mem_map.1 (hM w.2)
  have hw'w:w'=w:=Subtype.ext hww
  rw[hw'w,Subgroup.mem_comap,MonoidHom.comp_apply,hw]at hw'
  simpa using hw'
lemma Qiy {G:Type u} [Group G] {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2]
    [CommGroup L3] (e1:Abelianization G≃*L1) (e2:Q2f G≃*L2) (e3:Q5p G≃*L3):
    ZA {w | ∃ z x,Q4j e1 e2 e3 z x =w}=⊤:=by
  have hle:ZA {w | ∃ z x,Qew G z x =w}≤
      (ZA {w | ∃ z x,Q4j e1 e2 e3 z x =w}).comap e3.toMonoidHom:=by
    rw[ZD]
    rintro _ ⟨z,x,rfl⟩
    rw[SetLike.mem_coe,Subgroup.mem_comap]
    refine ZC ⟨e2 z,e1 x,?_⟩
    simp[Q70]
  rw[Qg8 G]at hle
  rw[eq_top_iff]
  intro q _
  have h:=hle (ZM (e3.symm q))
  rw[Subgroup.mem_comap]at h
  simpa using h
lemma Qj4 {G:Type u} [Group G] {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2]
    [CommGroup L3] (e1:Abelianization G≃*L1) (e2:Q2f G≃*L2) (e3:Q5p G≃*L3)
    {r s:ℕ} (X:Fin r→G)
    (hcore:lcs G 1≤⁅ZA (X '' {j | (j:ℕ)<s}),
      ZA (X '' {j | (j:ℕ)<s})⁆⊔lcs G 2):
    Subgroup.closure {w | ∃ z,∃ u∈ZA
        ((fun j=>e1 (ZH (X j))) '' {j | (j:ℕ)<s}),
      Q4j e1 e2 e3 z u=w}=⊤:=
  Ql0 (Qg6 e1 e2 e3) _ (Qcz e1 e2 X hcore) (Qiy e1 e2 e3)
def Qb7 {L1 L2:Type*} [CommGroup L1] [CommGroup L2] (L3:Type*) [CommGroup L3] {r :ℕ}
    (s:ℕ) (g:Fin r→ L1) (D:Finset (Fin r×Fin r)) (v:Fin r×Fin r→ L2):
    Set ((L1→*L1→*L2)×(L2→*L1→*L3)):=
  {β | Q21 β.1∧
    ZA {w | ∃ u∈ZA (g '' {j | (j:ℕ)<s}),
      ∃ u'∈ZA (g '' {j | (j:ℕ)<s}),β.1 u u'=w}=⊤∧
    Q1m β.1 β.2∧
    ZA
      {w | ∃ z,∃ u∈ZA (g '' {j | (j:ℕ)<s}),β.2 z u=w}=⊤∧
    ∀ q∈D,β.1 (g q.1) (g q.2)=v q}
lemma Qgi {G:Type u} [Group G] {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2]
    [CommGroup L3] (e1:Abelianization G≃*L1) (e2:Q2f G≃*L2) (e3:Q5p G≃*L3)
    {r s:ℕ} (X:Fin r→G) (g:Fin r→ L1) (hg:∀ j,e1 (ZH (X j))=g j)
    (hcore:lcs G 1≤⁅ZA (X '' {j | (j:ℕ)<s}),
      ZA (X '' {j | (j:ℕ)<s})⁆⊔lcs G 2)
    (D:Finset (Fin r×Fin r)) (v:Fin r×Fin r→ L2)
    (hv:∀ q∈D,e2 (Q1z G (cw (X q.1) (X q.2)))=v q):
    (Q4a e1 e2,Q4j e1 e2 e3)∈Qb7 L3 s g D v:=by
  have hgX:g= fun j=>e1 (ZH (X j)):= funext fun j=> (hg j).symm
  subst hgX
  rw[Qb7,Set.mem_setOf_eq]
  refine ⟨Qmy e1 e2,Qcz e1 e2 X hcore,Qg6 e1 e2 e3,
    Qj4 e1 e2 e3 X hcore,fun q hq=>?_⟩
  show Q4a e1 e2 (e1 (ZH (X q.1))) (e1 (ZH (X q.2)))=v q
  rw[Qak]
  exact hv q hq
end LfTransport
section LfPresent
def Q3k {n:ℕ} (p:ℕ) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ) (j:Fin n):Fin n→ℤ:=
  fun i=>if i=j then (p:ℤ)^a j else if i<j then -(b j i:ℤ) else 0
def Q1u {n:ℕ} (p:ℕ) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ):AddSubgroup (Fin n→ℤ):=
  AddSubgroup.closure (ZG (Q3k p a b))
lemma Qkx {n p:ℕ} (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ) (j:Fin n):
    Q3k p a b j j=(p:ℤ)^a j:=by
 unfold Q3k
 rw[if_pos rfl]
lemma Qjv {n p:ℕ} (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ) {i j:Fin n} (h:j< i):
    Q3k p a b j i=0:=by
 unfold Q3k
 rw[if_neg h.ne',if_neg (not_lt.mpr h.le)]
lemma Qm8 {n p:ℕ} (hp:0<p) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ)
    (x :Fin n→ℤ):∃ w:Fin n→ℤ,(∀ j,0≤w j∧w j< (p:ℤ)^a j)∧
      x - w∈Q1u p a b:=by
 have key : ∀ k:ℕ,∃ w:Fin n→ℤ,
     (∀ j:Fin n,n≤(j:ℕ)+k→0≤w j∧w j< (p:ℤ)^a j)∧
       x - w∈Q1u p a b:=by
  intro k
  induction k with
  | zero=>
    refine ⟨x,fun j hj=>absurd hj (by have:=j.isLt; omega),?_⟩
    rw[sub_self]
    exact (Q1u p a b).zero_mem
  | succ k ih=>
    obtain ⟨w,hw,hx⟩:=ih
    by_cases hk:k<n
    · obtain ⟨jk,hjkv⟩:∃ jk:Fin n,(jk:ℕ)=n - 1 - k:=⟨⟨n - 1 - k,by omega⟩,rfl⟩
      have hPpos:(0:ℤ)< (p:ℤ)^a jk:=pow_pos (by exact_mod_cast hp) _
      obtain ⟨q,hq⟩:∃ q:ℤ,q=w jk/(p:ℤ)^a jk:=⟨_,rfl⟩
      refine ⟨w - q•Q3k p a b jk,fun j hj=>?_,?_⟩
      · by_cases hjj:j=jk
        · rw[hjj]
          have e:(w - q•Q3k p a b jk) jk=w jk % (p:ℤ)^a jk:=by
           rw[Pi.sub_apply,Pi.smul_apply,Qkx,smul_eq_mul,hq]
           have h:=Int.mul_ediv_add_emod (w jk) ((p:ℤ)^a jk)
           linear_combination -h
          rw[e]
          exact ⟨Int.emod_nonneg _ hPpos.ne',Int.emod_lt_of_pos _ hPpos⟩
        · have hne:(j:ℕ)≠n - 1 - k:= fun h=>hjj (Fin.ext (h.trans hjkv.symm))
          have hlt:jk<j:=Fin.lt_def.mpr (by omega)
          have h0:(w - q•Q3k p a b jk) j=w j:=by
           rw[Pi.sub_apply,Pi.smul_apply,Qjv a b hlt,smul_zero,sub_zero]
          rw[h0]
          exact hw j (by omega)
      · have e:x - (w - q•Q3k p a b jk)=(x - w)+q•Q3k p a b jk:=by abel
        rw[e]
        have hmem:Q3k p a b jk∈Q1u p a b:=AddSubgroup.subset_closure ⟨jk,rfl⟩
        exact (Q1u p a b).add_mem hx (zsmul_mem hmem q)
    · exact ⟨w,fun j hj=>hw j (by omega),hx⟩
 obtain ⟨w,hw,hx⟩:=key n
 exact ⟨w,fun j=>hw j (by omega),hx⟩
lemma Qe1 {n p:ℕ} (hp:0<p) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ):
    Function.Surjective (fun e:(j:Fin n)→Fin (p^a j)=>
      (ZK (fun j=> ((e j:ℕ):ℤ)):(Fin n→ℤ)⧸Q1u p a b)):=by
    intro q
    obtain ⟨x,rfl⟩:=QuotientAddGroup.mk_surjective q
    obtain ⟨w,hw,hxw⟩:=Qm8 hp a b x
    have hnat:∀ j,((w j).toNat:ℤ)=w j:= fun j=>Int.toNat_of_nonneg (hw j).1
    have hlt:∀ j,(w j).toNat<p^a j:=by
     intro j
     have h1:((w j).toNat:ℤ)< ((p^a j:ℕ):ℤ):=by
      rw[hnat j,Nat.cast_pow]
      exact (hw j).2
     exact_mod_cast h1
    refine ⟨fun j=> ⟨(w j).toNat,hlt j⟩,?_⟩
    have hfun:(fun j=> (((w j).toNat:ℕ):ℤ))=w:= funext hnat
    show ZK (fun j=> (((w j).toNat:ℕ):ℤ))=ZK x
    rw[hfun,QuotientAddGroup.eq]
    have e: -w+x =x - w:=by abel
    rw[e]
    exact hxw
lemma Q7n {n p:ℕ} (a:Fin n→ℕ):
    ZB ((j:Fin n)→Fin (p^a j))=p^∑ j,a j:=by
 rw[Nat.card_eq_fintype_card,Fintype.card_pi]
 simp only[Fintype.card_fin]
 rw[Finset.prod_pow_eq_pow_sum]
lemma Q11 {n p:ℕ} (hp:0<p) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ):
    Finite ((Fin n→ℤ)⧸Q1u p a b)∧
      ZB ((Fin n→ℤ)⧸Q1u p a b)≤p^∑ j,a j:=by
 have hsurj:=Qe1 hp a b
 refine ⟨Finite.of_surjective _ hsurj,?_⟩
 rw[← Q7n (p:=p) a]
 exact Nat.card_le_card_of_surjective _ hsurj
variable {L:Type*} [CommGroup L]
def Q39 {n:ℕ} (y:Fin n→ L):(Fin n→ℤ)→+Additive L where
  toFun x:=∑ j,x j•ZE (y j)
  map_zero':=by simp
  map_add' x x':=by simp only[Pi.add_apply,add_smul,Finset.sum_add_distrib]
lemma Qai {n:ℕ} (y:Fin n→ L) (x:Fin n→ℤ):
    Q39 y x =∑ j,x j•ZE (y j):=rfl
lemma Q71 {n:ℕ} (y:Fin n→ L) (j:Fin n):
    Q39 y (Pi.single j 1)=ZE (y j):=by
 rw[Qai,Finset.sum_eq_single j]
 · simp
 · intro i _ hi
   simp[hi]
 · intro h
   exact absurd (Finset.mem_univ j) h
lemma Qmc {n p:ℕ} (y:Fin n→ L) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ) (j:Fin n):
    Q39 y (Q3k p a b j)=((p:ℤ)^a j)•ZE (y j) -
      ∑ i∈Finset.univ.filter (fun i=>i<j),(b j i:ℤ)•ZE (y i):=by
  have hpt:∀ i,Q3k p a b j i•ZE (y i)=
      (if i=j then ((p:ℤ)^a i)•ZE (y i) else 0) -
        (if i<j then (b j i:ℤ)•ZE (y i) else 0):=by
    intro i
    unfold Q3k
    by_cases h1:i=j
    · subst h1
      simp
    · by_cases h2:i<j
      · simp[h1,h2]
      · simp[h1,h2]
  rw [Qai,Finset.sum_congr rfl (fun i _=>hpt i),Finset.sum_sub_distrib,
    Finset.sum_ite_eq',if_pos (Finset.mem_univ j),Finset.sum_filter]
lemma Qdw {n p:ℕ} (y:Fin n→ L) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ)
    (j :Fin n) (hrel:(p^a j)•ZE (y j)=
      ∑ i∈Finset.univ.filter (fun i=>i<j),b j i•ZE (y i)):
    Q39 y (Q3k p a b j)=0:=by
  rw[Qmc, ← Nat.cast_pow,natCast_zsmul]
  simp only[natCast_zsmul]
  rw[hrel,sub_self]
lemma Qi7 [Finite L] {n p:ℕ} (hp:0<p) (a:Fin n→ℕ)
    (b:Fin n→Fin n→ℕ) (y:Fin n→ L) (hy:ZA (ZG y)=⊤)
    (hL:ZB L=p^∑ j,a j) (hrel:∀ j,Q39 y (Q3k p a b j)=0):
    ∃ φ :((Fin n→ℤ)⧸Q1u p a b)≃+Additive L,
      (∀ j,φ (ZK (Pi.single j 1))=ZE (y j))∧
        ∀ x,φ (ZK x)=Q39 y x:=by
 have hle:Q1u p a b≤(Q39 y).ker :=by
  rw[Q1u,AddSubgroup.closure_le]
  rintro _ ⟨j,rfl⟩
  exact AddMonoidHom.mem_ker.2 (hrel j)
 let φ:=QuotientAddGroup.lift (Q1u p a b) (Q39 y) hle
 have hs :∀ z:L,∃ x,Q39 y x =ZE z:=by
  let T :Subgroup L:=
    { carrier :={z | ∃ x,Q39 y x =ZE z}
      mul_mem':=by
        rintro z z' ⟨x,hx⟩ ⟨x',hx'⟩
        exact ⟨x+x',by rw[map_add,hx,hx',ofMul_mul]⟩
      one_mem':=⟨0,by rw[map_zero,ofMul_one]⟩
      inv_mem':=by
        rintro z ⟨x,hx⟩
        exact ⟨-x,by rw[map_neg,hx,ofMul_inv]⟩ }
  have hT:ZA (ZG y)≤T:=by
   rw[ZD]
   rintro _ ⟨j,rfl⟩
   exact ⟨Pi.single j 1,Q71 y j⟩
  rw[hy]at hT
  intro z
  obtain ⟨x,hx⟩:=hT (ZM z)
  exact ⟨x,hx⟩
 have hsurj:Function.Surjective φ:=by
  intro z
  obtain ⟨x,hx⟩:=hs (Additive.toMul z)
  exact ⟨ZK x,hx⟩
 obtain ⟨hfin,hcard⟩:=Q11 hp a b
 have hLA:ZB L=ZB (Additive L):=Nat.card_congr ZE
 have hbij:Function.Bijective φ:=by
  refine (Nat.bijective_iff_surjective_and_card φ).2 ⟨hsurj,le_antisymm ?_ ?_⟩
  · rw[← hLA,hL]
    exact hcard
  · exact Nat.card_le_card_of_surjective φ hsurj
 refine ⟨AddEquiv.ofBijective φ hbij,fun j=>?_,fun x =>rfl⟩
 have h1:φ (ZK (Pi.single j 1))=Q39 y (Pi.single j 1):=rfl
 show φ (ZK (Pi.single j 1))=ZE (y j)
 rw[h1,Q71]
lemma Qg3 {n p:ℕ} (hp:0<p) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ)
    (φ:((Fin n→ℤ)⧸Q1u p a b)≃+Additive L) (hL:ZB L=p^∑ j,a j)
    (e e':Fin n→ℕ) (he:∀ j,e j<p^a j) (he':∀ j,e' j<p^a j)
    (h :(ZK (fun j=> (e j:ℤ)):(Fin n→ℤ)⧸Q1u p a b)=
      ZK (fun j=> (e' j:ℤ))):e=e':=by
  have hcard:ZB ((j:Fin n)→Fin (p^a j))=
      ZB ((Fin n→ℤ)⧸Q1u p a b):=by
   rw[Q7n, ← hL]
   exact (Nat.card_congr (ZE:L≃ Additive L)).trans
     (Nat.card_congr φ.toEquiv).symm
  have hbij:=(Nat.bijective_iff_surjective_and_card _).2 ⟨Qe1 hp a b,hcard⟩
  have key:(fun j=> (⟨e j,he j⟩:Fin (p^a j)))= fun j=> ⟨e' j,he' j⟩:=hbij.1 h
  funext j
  exact congrArg Fin.val (congrFun key j)
end LfPresent
section LfSimsLift
variable {G:Type u} [Group G] {p c:ℕ} {r :Fin c→ℕ} {a:Q6 c r→ℕ}
  {g:Q6 c r→G}
lemma Q7.Q89 (S:Q7 p a g) (i:Fin c) {x:G}
    (hx:x∈lcs G i):x∈Qay g i (r i):=by
 have h:=Q7g (fun v:Fin (r i)=>g ⟨i,v⟩)
   (fun v=>S.mem ⟨i,v⟩) (S.gen i) hx
 have hmono:ZA (ZG fun v:Fin (r i)=>g ⟨i,v⟩)≤
     ZA {x | ∃ v:Fin (r i),v.val< r i∧g ⟨i,v⟩=x}:=by
   apply ZO
   rintro _ ⟨v,rfl⟩
   exact ⟨v,v.isLt,rfl⟩
 exact sup_le_sup_right hmono (lcs G ((i:ℕ)+1)) h
lemma Q7.Q54 (S:Q7 p a g) (i:Fin c) {x:G}
    (hx:x∈lcs G i):
    x = Qu g (fun h=> (S.nf.coord x h).val) i*
      (ZR fun u:Fin c=>
        if i<u then Qu g (fun h=> (S.nf.coord x h).val) u else 1).prod:=by
  obtain ⟨hsupp,hprod⟩:=S.nf.Q6p i (r i) x (S.Q89 i hx)
  refine hprod.symm.trans
    (Q3i c (Qu g fun h=> (S.nf.coord x h).val) i fun u hu=>?_)
  unfold Qu
  refine List.prod_eq_one fun z hz=>?_
  rw[List.mem_ofFn']at hz
  obtain ⟨v,rfl⟩:=hz
  have h0:(S.nf.coord x ⟨u,v⟩).val=0:=hsupp ⟨u,v⟩ (Or.inl hu)
  show g ⟨u,v⟩^(S.nf.coord x ⟨u,v⟩).val=1
  rw[h0,pow_zero]
def Q8s (hp:0<p) (i:Fin c) (e:Fin (r i)→ℕ) (he:∀ v,e v<p^a ⟨i,v⟩)
    (dc:(h:Q6 c r)→Fin (p^a h)):(h:Q6 c r)→Fin (p^a h)
  | ⟨i',v⟩=>if hh:i'=i then ⟨e (hh▸v),by subst hh; exact he v⟩
      else if i< i' then dc ⟨i',v⟩ else ⟨0,pow_pos hp _⟩
lemma Qjx (hp:0<p) (i:Fin c) (e:Fin (r i)→ℕ) (he:∀ v,e v<p^a ⟨i,v⟩)
    (dc:(h:Q6 c r)→Fin (p^a h)) (v:Fin (r i)):
    (Q8s hp i e he dc ⟨i,v⟩).val=e v:=by
 rw[Q8s,dif_pos rfl]
 try rfl
lemma Qm5 (hp:0<p) (i:Fin c) (e:Fin (r i)→ℕ) (he:∀ v,e v<p^a ⟨i,v⟩)
    (dc:(h:Q6 c r)→Fin (p^a h)) {u:Fin c} (hu:u< i) (v:Fin (r u)):
    (Q8s hp i e he dc ⟨u,v⟩).val=0:=by
 rw[Q8s,dif_neg hu.ne,if_neg (not_lt.mpr hu.le)]
lemma Qm9 (hp:0<p) (i:Fin c) (e:Fin (r i)→ℕ) (he:∀ v,e v<p^a ⟨i,v⟩)
    (dc:(h:Q6 c r)→Fin (p^a h)) {u:Fin c} (hu:i<u) (v:Fin (r u)):
    Q8s hp i e he dc ⟨u,v⟩=dc ⟨u,v⟩:=by
 rw[Q8s,dif_neg hu.ne',if_pos hu]
lemma Q7.Qb6 (S:Q7 p a g) (hp:0<p) (i:Fin c)
    (e:Fin (r i)→ℕ) (he:∀ v,e v<p^a ⟨i,v⟩) {d:G} (hd:d∈lcs G ((i:ℕ)+1))
    (hlast:(i:ℕ)+1<c∨lcs G ((i:ℕ)+1)=⊥) (v:Fin (r i)):
    (S.nf.coord ((ZR fun w=>g ⟨i,w⟩^e w).prod*d) ⟨i,v⟩).val=e v:=by
  have hdi:d∈lcs G i:=Qd (Nat.le_succ _) hd
  have hdprod:Q2w g (fun h=> (S.nf.coord d h).val)=d:=
    (S.nf.Q6p i (r i) d (S.Q89 i hdi)).2
  have hdc:∀ h:Q6 c r,h.1≤ i→(S.nf.coord d h).val=0:=by
   rcases hlast with h1 | hbot
   · intro h hh
     have hsup:=(S.nf.Q6p ⟨(i:ℕ)+1,h1⟩ (r ⟨(i:ℕ)+1,h1⟩) d
       (S.Q89 ⟨(i:ℕ)+1,h1⟩ hd)).1
     exact hsup h (Or.inl (Fin.lt_def.mpr (Nat.lt_succ_of_le (Fin.le_def.mp hh))))
   · have hd1:d=1:=by
       rw[hbot]at hd
       exact Subgroup.mem_bot.mp hd
     intro h _
     have hZ:Q2w g (fun h=> ((⟨0,pow_pos hp _⟩:Fin (p^a h)):ℕ))=1:=by
       unfold Q2w
       refine List.prod_eq_one fun z hz=>?_
       rw[List.mem_ofFn']at hz
       obtain ⟨u,rfl⟩:=hz
       unfold Qu
       refine List.prod_eq_one fun z hz=>?_
       rw[List.mem_ofFn']at hz
       obtain ⟨w,rfl⟩:=hz
       exact pow_zero _
     have hu:S.nf.coord (Q2w g (fun h=> ((⟨0,pow_pos hp _⟩:Fin (p^a h)):ℕ)))=
         fun h=> ⟨0,pow_pos hp _⟩:=S.nf.uniq _
     rw[hZ, ← hd1]at hu
     rw[hu]
  obtain ⟨E,hE⟩:∃ E,E=Q8s hp i e he (S.nf.coord d):=⟨_,rfl⟩
  have hEi:∀ w,(E ⟨i,w⟩).val=e w:=by
   intro w
   rw[hE]
   exact Qjx hp i e he _ w
  have hElt:∀ u,u< i→∀ w,(E ⟨u,w⟩).val=0:=by
   intro u hu w
   rw[hE]
   exact Qm5 hp i e he _ hu w
  have hEgt:∀ u,i<u→∀ w,E ⟨u,w⟩=S.nf.coord d ⟨u,w⟩:=by
   intro u hu w
   rw[hE]
   exact Qm9 hp i e he _ hu w
  have hs:=Q3i c (Qu g fun h=> (E h).val) i fun u hu=>by
    unfold Qu
    refine List.prod_eq_one fun z hz=>?_
    rw[List.mem_ofFn']at hz
    obtain ⟨w,rfl⟩:=hz
    show g ⟨u,w⟩^(E ⟨u,w⟩).val=1
    rw[hElt u hu w,pow_zero]
  have hd':=Q3i c (Qu g fun h=> (S.nf.coord d h).val) i fun u hu=>by
    unfold Qu
    refine List.prod_eq_one fun z hz=>?_
    rw[List.mem_ofFn']at hz
    obtain ⟨w,rfl⟩:=hz
    show g ⟨u,w⟩^(S.nf.coord d ⟨u,w⟩).val=1
    rw[hdc ⟨u,w⟩ hu.le,pow_zero]
  have hb1:Qu g (fun h=> (S.nf.coord d h).val) i=1:=by
    unfold Qu
    refine List.prod_eq_one fun z hz=>?_
    rw[List.mem_ofFn']at hz
    obtain ⟨w,rfl⟩:=hz
    show g ⟨i,w⟩^(S.nf.coord d ⟨i,w⟩).val=1
    rw[hdc ⟨i,w⟩ le_rfl,pow_zero]
  have hbi:Qu g (fun h=> (E h).val) i=(ZR fun w=>g ⟨i,w⟩^e w).prod:=by
    simp only[Qu,hEi]
  have hdeep:(ZR fun u:Fin c=>
        if i<u then Qu g (fun h=> (E h).val) u else 1).prod=
      (ZR fun u:Fin c=>
        if i<u then Qu g (fun h=> (S.nf.coord d h).val) u else 1).prod:=by
    congr 2
    funext u
    by_cases hu:i<u
    · rw[if_pos hu,if_pos hu]
      simp only[Qu,hEgt u hu]
    · rw[if_neg hu,if_neg hu]
  have hdd:d=(ZR fun u:Fin c=>
        if i<u then Qu g (fun h=> (S.nf.coord d h).val) u else 1).prod:=by
    have h2:=hdprod.symm.trans hd'
    rwa[hb1,one_mul]at h2
  have hfull:Q2w g (fun h=> (E h).val)=(ZR fun w=>g ⟨i,w⟩^e w).prod*d:=by
    calc Q2w g (fun h=> (E h).val)
        = Qu g (fun h=> (E h).val) i*(ZR fun u:Fin c=>
          if i<u then Qu g (fun h=> (E h).val) u else 1).prod:=hs
      _=_:=by rw[hbi,hdeep, ← hdd]
  have hu:=S.nf.uniq E
  rw[hfull]at hu
  rw[hu]
  exact hEi v
lemma Q7.Qc2 (S:Q7 p a g) (hp:0<p) (i:Fin c)
    (hlast:(i:ℕ)+1<c∨lcs G ((i:ℕ)+1)=⊥):
    ZB (Q1r G i)=p^∑ v:Fin (r i),a ⟨i,v⟩:=by
 have hB:∀ e:(v:Fin (r i))→Fin (p^a ⟨i,v⟩),
     (ZR fun w=>g ⟨i,w⟩^(e w).val).prod∈lcs G i:= fun e=>
   Subgroup.list_prod_mem _ fun z hz=>by
     rw[List.mem_ofFn']at hz
     obtain ⟨w,rfl⟩:=hz
     exact Subgroup.pow_mem _ (S.mem ⟨i,w⟩) _
 let β:((v:Fin (r i))→Fin (p^a ⟨i,v⟩))→Q1r G i:= fun e=>
   QuotientGroup.mk (⟨(ZR fun w=>g ⟨i,w⟩^(e w).val).prod,hB e⟩:lcs G i)
 have hinj:Function.Injective β:=by
  intro e e' hee
  have hee':(QuotientGroup.mk (⟨(ZR fun w=>g ⟨i,w⟩^(e w).val).prod,hB e⟩:
      lcs G i):Q1r G i)=
      QuotientGroup.mk (⟨(ZR fun w=>g ⟨i,w⟩^(e' w).val).prod,hB e'⟩:
        lcs G i):=hee
  have h1:=Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hee')
  have hd:((ZR fun w=>g ⟨i,w⟩^(e w).val).prod)⁻¹*
      (ZR fun w=>g ⟨i,w⟩^(e' w).val).prod∈lcs G ((i:ℕ)+1):=h1
  funext v
  apply Fin.ext
  have hc1:=S.Qb6 hp i (fun w=> (e w).val) (fun w=> (e w).isLt) hd hlast v
  have hc2:=S.Qb6 hp i (fun w=> (e' w).val) (fun w=> (e' w).isLt)
    (Subgroup.one_mem _) hlast v
  beta_reduce at hc1 hc2
  rw[mul_one]at hc2
  rw[mul_inv_cancel_left]at hc1
  exact hc1.symm.trans hc2
 have hsurj :Function.Surjective β:=by
  intro q
  obtain ⟨⟨x,hx⟩,rfl⟩:=QuotientGroup.mk_surjective q
  refine ⟨fun w=>S.nf.coord x ⟨i,w⟩,?_⟩
  show (QuotientGroup.mk _:Q1r G i)=QuotientGroup.mk _
  rw[QuotientGroup.eq,Subgroup.mem_subgroupOf]
  have hl:=S.Q54 i hx
  have hdeep:=Q4m g S.mem (fun h=> (S.nf.coord x h).val) i
  show (Qu g (fun h=> (S.nf.coord x h).val) i)⁻¹*x∈lcs G ((i:ℕ)+1)
  have e1 : (Qu g (fun h=> (S.nf.coord x h).val) i)⁻¹*x =
      (ZR fun u:Fin c=>if i<u then
        Qu g (fun h=> (S.nf.coord x h).val) u else 1).prod:=by
    calc _ = (Qu g (fun h=> (S.nf.coord x h).val) i)⁻¹*
          (Qu g (fun h=> (S.nf.coord x h).val) i*(ZR fun u:Fin c=>
            if i<u then Qu g (fun h=> (S.nf.coord x h).val) u else 1).prod):=by
          rw[← hl]
      _=_:=inv_mul_cancel_left _ _
  rw[e1]
  exact hdeep
 rw [← Nat.card_congr (Equiv.ofBijective β ⟨hinj,hsurj⟩),Nat.card_eq_fintype_card,
   Fintype.card_pi]
 simp only[Fintype.card_fin]
 rw[Finset.prod_pow_eq_pow_sum]
lemma Qen {K:Subgroup G} {M:Type*} [Monoid M] (π:K→*M) {n:ℕ}
    (f:Fin n→G) (hf:∀ v,f v∈K) (h:(ZR f).prod∈K):
    π ⟨(ZR f).prod,h⟩=(ZR fun v=>π ⟨f v,hf v⟩).prod:=by
  have e:(⟨(ZR f).prod,h⟩:K)=(ZR fun v=> (⟨f v,hf v⟩:K)).prod:=by
    apply Subtype.ext
    rw[SubmonoidClass.coe_list_prod,List.map_ofFn]
    try rfl
  rw[e,map_list_prod,List.map_ofFn]
  try rfl
lemma Q7.Q5v (S:Q7 p a g) (i:Fin c) {L:Type*} [CommGroup L]
    (π:lcs G i→*L) (hker :∀ x:lcs G i,(x:G)∈lcs G ((i:ℕ)+1)→π x =1)
    (e:Fin (r i)→ℕ) {d:G} (hd:d∈lcs G ((i:ℕ)+1)) {x:G} (hx:x∈lcs G i)
    (hxe:x =(ZR fun v=>g ⟨i,v⟩^e v).prod*d):
    π ⟨x,hx⟩=∏ v,π ⟨g ⟨i,v⟩,S.mem ⟨i,v⟩⟩^e v:=by
  have hf:∀ v,g ⟨i,v⟩^e v∈lcs G i:= fun v=>Subgroup.pow_mem _ (S.mem ⟨i,v⟩) _
  have hB:(ZR fun v=>g ⟨i,v⟩^e v).prod∈lcs G i:=
    Subgroup.list_prod_mem _ fun z hz=>by
      rw[List.mem_ofFn']at hz
      obtain ⟨v,rfl⟩:=hz
      exact hf v
  have hdi:d∈lcs G i:=Qd (Nat.le_succ _) hd
  have e1:(⟨x,hx⟩:lcs G i)=⟨_,hB⟩*⟨d,hdi⟩:=Subtype.ext hxe
  rw[e1,map_mul,hker ⟨d,hdi⟩ hd,mul_one,Qen π _ hf hB,List.prod_ofFn]
  refine Finset.prod_congr rfl fun v _=>?_
  rw[← map_pow]
  exact congrArg π (Subtype.ext (by simp))
lemma Q7.Qm3 (S:Q7 p a g) (i:Fin c) {L:Type*} [CommGroup L]
    (π:lcs G i→*L) (hker :∀ x:lcs G i,(x:G)∈lcs G ((i:ℕ)+1)→π x =1)
    (j:Fin (r i)):
    π ⟨g ⟨i,j⟩,S.mem ⟨i,j⟩⟩^(p^a ⟨i,j⟩)=
      ∏ v∈Finset.univ.filter (fun v:Fin (r i)=>v<j),
        π ⟨g ⟨i,v⟩,S.mem ⟨i,v⟩⟩^(S.Ql ⟨i,j⟩ ⟨i,v⟩).val:=by
  have hpow:=S.Qd3.pow i j
  have hdeep:=Q4m g S.mem (fun h=> (S.Ql ⟨i,j⟩ h).val) i
  have hmem:g ⟨i,j⟩^p^a ⟨i,j⟩∈lcs G i:=Subgroup.pow_mem _ (S.mem ⟨i,j⟩) _
  have hb:=S.Q5v i π hker (fun v=> (S.Ql ⟨i,j⟩ ⟨i,v⟩).val) hdeep hmem hpow
  rw[← map_pow]
  have e1:(⟨g ⟨i,j⟩,S.mem ⟨i,j⟩⟩:lcs G i)^(p^a ⟨i,j⟩)=⟨_,hmem⟩:=
    Subtype.ext (SubgroupClass.coe_pow _ _)
  rw[e1,hb,Finset.prod_filter]
  refine Finset.prod_congr rfl fun v _=>?_
  by_cases hv:v<j
  · rw[if_pos hv]
  · rw[if_neg hv,S.Q73 i j v (not_lt.mp hv),pow_zero]
lemma Q7.Q8d (S:Q7 p a g) (hp:0<p) (i:Fin c)
    (hlast:(i:ℕ)+1<c∨lcs G ((i:ℕ)+1)=⊥) {L:Type*} [CommGroup L]
    (π:lcs G i→*L) (hπ:Function.Surjective π)
    (hker :∀ x:lcs G i,π x =1↔(x:G)∈lcs G ((i:ℕ)+1)):
    ZB L=p^∑ v:Fin (r i),a ⟨i,v⟩:=by
 have hkereq:π.ker=(lcs G ((i:ℕ)+1)).subgroupOf (lcs G i):=by
  ext x
  rw[MonoidHom.mem_ker,Subgroup.mem_subgroupOf,hker]
 rw[← S.Qc2 hp i hlast]
 exact (Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hkereq).symm.trans
   (QuotientGroup.quotientKerEquivOfSurjective π hπ)).toEquiv).symm
lemma Q7.Q7f (S:Q7 p a g) (hp:0<p) (i:Fin c)
    (hlast:(i:ℕ)+1<c∨lcs G ((i:ℕ)+1)=⊥) {L:Type*} [CommGroup L] [Finite L]
    (π:lcs G i→*L) (hπ:Function.Surjective π)
    (hker :∀ x:lcs G i,π x =1↔(x:G)∈lcs G ((i:ℕ)+1))
    (b:Fin (r i)→Fin (r i)→ℕ) (hb:∀ j v,(S.Ql ⟨i,j⟩ ⟨i,v⟩).val=b j v):
    ∃ φ :((Fin (r i)→ℤ)⧸Q1u p (fun v=>a ⟨i,v⟩) b)≃+Additive L,
      ∀ x:Fin (r i)→ℤ,φ (ZK x)=
        Q39 (fun v=>π ⟨g ⟨i,v⟩,S.mem ⟨i,v⟩⟩) x:=by
  have hker1:∀ x:lcs G i,(x:G)∈lcs G ((i:ℕ)+1)→π x =1:=
    fun x hx => (hker x).2 hx
  have hgen:ZA (ZG fun v=>π ⟨g ⟨i,v⟩,S.mem ⟨i,v⟩⟩)=⊤:=by
    rw[eq_top_iff]
    intro z _
    obtain ⟨⟨x,hx⟩,rfl⟩:=hπ z
    rw [S.Q5v i π hker1 (fun v=> (S.nf.coord x ⟨i,v⟩).val)
      (Q4m g S.mem (fun h=> (S.nf.coord x h).val) i) hx (S.Q54 i hx)]
    exact Subgroup.prod_mem _ fun v _=>
      Subgroup.pow_mem _ (ZC (Set.mem_range_self v)) _
  have hcard:=S.Q8d hp i hlast π hπ hker
  have hrel:∀ j,Q39 (fun v=>π ⟨g ⟨i,v⟩,S.mem ⟨i,v⟩⟩)
      (Q3k p (fun v=>a ⟨i,v⟩) b j)=0:=by
    intro j
    apply Qdw
    beta_reduce
    rw[← ofMul_pow,S.Qm3 i π hker1 j,ofMul_prod]
    simp only[ofMul_pow,hb]
  obtain ⟨φ, -,hφ⟩:=Qi7 hp _ b _ hgen hcard hrel
  exact ⟨φ,hφ⟩
lemma Q7.Q6w (S:Q7 p a g) (i:Fin c) {L:Type*}
    [CommGroup L] (π:lcs G i→*L)
    (hker :∀ x:lcs G i,(x:G)∈lcs G ((i:ℕ)+1)→π x =1)
    (b:Fin (r i)→Fin (r i)→ℕ)
    (φ:((Fin (r i)→ℤ)⧸Q1u p (fun v=>a ⟨i,v⟩) b)≃+Additive L)
    (hφ:∀ x:Fin (r i)→ℤ,φ (ZK x)=
      Q39 (fun v=>π ⟨g ⟨i,v⟩,S.mem ⟨i,v⟩⟩) x) {x:G} (hx:x∈lcs G i):
    φ (ZK (fun v=> ((S.nf.coord x ⟨i,v⟩:ℕ):ℤ)))=
      ZE (π ⟨x,hx⟩):=by
  rw [hφ,Qai,S.Q5v i π hker (fun v=> (S.nf.coord x ⟨i,v⟩).val)
    (Q4m g S.mem (fun h=> (S.nf.coord x h).val) i) hx (S.Q54 i hx),ofMul_prod]
  simp only[ofMul_pow,natCast_zsmul]
lemma Q7.Qin [Finite G] (S:Q7 p a g) (hp:0<p) (h0:0<c)
    (hlast:1<c∨lcs G 1=⊥) (b:Fin (r ⟨0,h0⟩)→Fin (r ⟨0,h0⟩)→ℕ)
    (hb:∀ j v,(S.Ql ⟨⟨0,h0⟩,j⟩ ⟨⟨0,h0⟩,v⟩).val=b j v):
    ∃ φ :((Fin (r ⟨0,h0⟩)→ℤ)⧸Q1u p (fun v=>a ⟨⟨0,h0⟩,v⟩) b)≃+
        Additive (Abelianization G),
      ∀ x,φ (ZK x)=Q39 (fun v=>
        (Abelianization.of.comp (lcs G 0).subtype) ⟨g ⟨⟨0,h0⟩,v⟩,S.mem ⟨⟨0,h0⟩,v⟩⟩) x:=by
  refine S.Q7f hp ⟨0,h0⟩ hlast (Abelianization.of.comp (lcs G 0).subtype)
    ?_ ?_ b hb
  · intro z
    obtain ⟨x,rfl⟩:=Q30 z
    exact ⟨⟨x,Qiu x⟩,rfl⟩
  · intro x
    rw [MonoidHom.comp_apply,Subgroup.coe_subtype, ← MonoidHom.mem_ker,Abelianization.ker_of,
      Q1s]
    try exact Iff.rfl
lemma Q7.Qi4 [Finite G] (S:Q7 p a g) (hp:0<p) (h1:1<c)
    (hlast:2<c∨lcs G 2=⊥) (b:Fin (r ⟨1,h1⟩)→Fin (r ⟨1,h1⟩)→ℕ)
    (hb:∀ j v,(S.Ql ⟨⟨1,h1⟩,j⟩ ⟨⟨1,h1⟩,v⟩).val=b j v):
    ∃ φ :((Fin (r ⟨1,h1⟩)→ℤ)⧸Q1u p (fun v=>a ⟨⟨1,h1⟩,v⟩) b)≃+Additive (Q2f G),
      ∀ x,φ (ZK x)=
        Q39 (fun v=>Q1z G ⟨g ⟨⟨1,h1⟩,v⟩,S.mem ⟨⟨1,h1⟩,v⟩⟩) x:=
  S.Q7f hp ⟨1,h1⟩ hlast (Q1z G) Q4z (fun x =>Q3b x) b hb
lemma Q7.Qic [Finite G] (S:Q7 p a g) (hp:0<p) (h2:2<c)
    (hlast:3<c∨lcs G 3=⊥) (b:Fin (r ⟨2,h2⟩)→Fin (r ⟨2,h2⟩)→ℕ)
    (hb:∀ j v,(S.Ql ⟨⟨2,h2⟩,j⟩ ⟨⟨2,h2⟩,v⟩).val=b j v):
    ∃ φ :((Fin (r ⟨2,h2⟩)→ℤ)⧸Q1u p (fun v=>a ⟨⟨2,h2⟩,v⟩) b)≃+Additive (Q5p G),
      ∀ x,φ (ZK x)=
        Q39 (fun v=>Q36 G ⟨g ⟨⟨2,h2⟩,v⟩,S.mem ⟨⟨2,h2⟩,v⟩⟩) x:=
  S.Q7f hp ⟨2,h2⟩ hlast (Q36 G) (Q5b G) (fun x =>Q38 x)
    b hb
end LfSimsLift
section LfFiber
variable {p:ℕ}
def Qw {m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0}) (D:Qg m)
    (B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)):
    Set (Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)):=
  {C | ∃ G∈T,Q1t hp m G (⟨D,(B,C)⟩:Qy p m)}
lemma Q85 {m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0})
    (I:Finset (Qg m)) (hI:∀ G∈T,∃ D:Qy p m,Q1t hp m G D ∧D.1∈I):
    (Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) '' T).ncard≤
      ∑ x∈I.sigma (fun D => (Set.toFinite (Q58 hp T D)).toFinset),
        (Qw hp T x.1 x.2).ncard:=by
  refine (Qc6 (I.sigma fun D => (Set.toFinite (Q58 hp T D)).toFinset)
    (fun x => (Set.toFinite (Qw hp T x.1 x.2)).toFinset)
    (fun x s C=> ∃ G∈T,
      Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) G=s∧
        Q1t hp m G (⟨x.1,(x.2,C)⟩:Qy p m)) ?_ ?_).trans_eq
    (Finset.sum_congr rfl fun x _=>?_)
  · rintro s ⟨G,hG,rfl⟩
    obtain ⟨⟨D,B,C⟩,hD,hDI⟩:=hI G hG
    refine ⟨⟨D,B⟩,Finset.mem_sigma.2 ⟨hDI,((Set.toFinite _).mem_toFinset).2 ⟨G,hG,C,hD⟩⟩,
      C,((Set.toFinite _).mem_toFinset).2 ⟨G,hG,hD⟩,G,hG,rfl,hD⟩
  · rintro s₁ - s₂ - x C ⟨G₁,hG₁,rfl,h₁⟩ ⟨G₂,hG₂,rfl,h₂⟩
    obtain ⟨e⟩:=Qas hp h₁ h₂
    exact Quotient.sound ⟨CategoryTheory.InducedCategory.isoMk (MulEquiv.toGrpIso e)⟩
  · exact (Set.ncard_eq_toFinset_card _ (Set.toFinite _)).symm
lemma Q72 {m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0})
    (I:Finset (Qg m)) (hI:∀ G∈T,∃ D:Qy p m,Q1t hp m G D ∧D.1∈I)
    (M:Qg m→ℕ)
    (hM:∀ D∈I,∀ B∈Q58 hp T D,(Qw hp T D B).ncard≤M D):
    (Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) '' T).ncard≤
      ∑ D∈I,p^Q2y (Qc D)*M D:=by
 have:Fact p.Prime:=⟨hp⟩
 refine (Q85 hp T I hI).trans ?_
 rw[Finset.sum_sigma]
 refine Finset.sum_le_sum fun D hD =>?_
 calc ∑ B ∈(Set.toFinite (Q58 hp T D)).toFinset,(Qw hp T D B).ncard
     ≤ ∑ B∈(Set.toFinite (Q58 hp T D)).toFinset,M D:=
       Finset.sum_le_sum fun B hB=>hM D hD B ((Set.toFinite _).mem_toFinset.1 hB)
   _ = (Q58 hp T D).ncard*M D:=by
       rw[Finset.sum_const,smul_eq_mul, ← Set.ncard_eq_toFinset_card]
   _ ≤ p ^Q2y (Qc D)*M D:=
       Nat.mul_le_mul_right _ ((Qd2 hp T D).trans
         (Qgl D.1.val (Q4 D) (Qc D) (Qhn D)))
end LfFiber
section LfLead
def Qe {Q L:Type*} [AddCommGroup Q] [CommGroup L] (φ:Q≃+Additive L):
    L≃*Multiplicative Q where
  toFun x:=ZI (φ.symm (ZE x))
  invFun y:=Additive.toMul (φ (Multiplicative.toAdd y))
  left_inv x:=by simp
  right_inv y:=by simp
  map_mul' x y:=by
    show ZI (φ.symm (ZE x+ZE y))=_
    exact (congrArg ZI (map_add φ.symm _ _)).trans (ofAdd_add _ _)
lemma Qjd {Q L:Type*} [AddCommGroup Q] [CommGroup L] (φ:Q≃+Additive L) (x:L):
    Qe φ x =ZI (φ.symm (ZE x)):=rfl
lemma Q9n {Q L:Type*} [AddCommGroup Q] [CommGroup L] (φ:Q≃+Additive L) {x:L}
    {q:Q} (h:φ q=ZE x):Qe φ x =ZI q:=by
 rw[Qjd, ← h,AddEquiv.symm_apply_apply]
abbrev Q17 {n:ℕ} (p:ℕ) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ):Type:=
  (Fin n→ℤ)⧸Q1u p a b
lemma Qgs {n:ℕ} (x:Fin n→ℤ) (j:Fin n):
    Pi.single j (x j)=x j•(Pi.single j (1:ℤ):Fin n→ℤ):=by
 funext i
 by_cases h:i=j
 · subst h
   simp
 · simp[Pi.single_apply,h]
lemma Q5q {n:ℕ} (p:ℕ) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ):
    ZA (ZG fun j:Fin n=>
      ZI (ZK (Pi.single j (1:ℤ)):Q17 p a b))=⊤:=by
  rw[eq_top_iff]
  rintro z -
  obtain ⟨x,hx⟩:=QuotientAddGroup.mk_surjective (Multiplicative.toAdd z)
  have hz:z=ZI (ZK x:Q17 p a b):=by
   rw[hx]
   rfl
  rw[hz]
  have key:∀ s:Finset (Fin n),ZI
      (ZK (∑ j∈s,Pi.single j (x j)):Q17 p a b)∈
      ZA (ZG fun j:Fin n=>
        ZI (ZK (Pi.single j (1:ℤ)):Q17 p a b)):=by
    intro s
    refine Finset.induction_on s ?_ ?_
    · rw[Finset.sum_empty,QuotientAddGroup.mk_zero,ofAdd_zero]
      exact Subgroup.one_mem _
    · intro j s hj ih
      rw[Finset.sum_insert hj,QuotientAddGroup.mk_add,ofAdd_add]
      refine Subgroup.mul_mem _ ?_ ih
      rw[Qgs x j,QuotientAddGroup.mk_zsmul,ofAdd_zsmul]
      exact Subgroup.zpow_mem _ (ZC (Set.mem_range_self j)) _
  have h:=key Finset.univ
  rwa[Finset.univ_sum_single]at h
lemma Q37 {n p:ℕ} {a:Fin n→ℕ} {b:Fin n→Fin n→ℕ} {L:Type*} [CommGroup L]
    (φ:Q17 p a b≃+Additive L) {N:ℕ} (hL:ZB L=N):
    ZB (Multiplicative (Q17 p a b))=N:=by
 rw [← hL,Nat.card_congr (Multiplicative.toAdd:Multiplicative (Q17 p a b)≃_),
   Nat.card_congr φ.toEquiv]
 exact Nat.card_congr Additive.toMul
abbrev Q1 {c:ℕ} (h2:2<c):Fin c:=⟨0,by omega⟩
abbrev Q3 {c:ℕ} (h2:2<c):Fin c:=⟨1,by omega⟩
abbrev Qa {c:ℕ} (h2:2<c):Fin c:=⟨2,h2⟩
variable {G:Type u} [Group G] {p c:ℕ} {r :Fin c→ℕ} {a:Q6 c r→ℕ}
  {g:Q6 c r→G}
def Q7.Q14 (S:Q7 p a g) (h2:2<c):
    Fin (r (Q1 h2))→Fin (r (Q1 h2))→Fin (r (Q3 h2))→ℕ:=
  fun j k v=> (S.nf.coord ⁅g ⟨Q1 h2,j⟩,g ⟨Q1 h2,k⟩⁆ ⟨Q3 h2,v⟩).val
def Q7.Q1v (S:Q7 p a g) (h2:2<c):
    Fin (r (Q3 h2))→Fin (r (Q1 h2))→Fin (r (Qa h2))→ℕ:=
  fun j k v=> (S.nf.coord ⁅g ⟨Q3 h2,j⟩,g ⟨Q1 h2,k⟩⁆ ⟨Qa h2,v⟩).val
structure Q7.Q27 (S:Q7 p a g) (h2:2<c)
    (b0:Fin (r (Q1 h2))→Fin (r (Q1 h2))→ℕ)
    (b1:Fin (r (Q3 h2))→Fin (r (Q3 h2))→ℕ)
    (b2:Fin (r (Qa h2))→Fin (r (Qa h2))→ℕ) where
  φ1:Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0≃+Additive (Abelianization G)
  φ2:Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1≃+Additive (Q2f G)
  φ3:Q17 p (fun v=>a ⟨Qa h2,v⟩) b2≃+Additive (Q5p G)
  spec1:∀ x,φ1 (ZK x)=Q39 (fun v=>
    (Abelianization.of.comp (lcs G 0).subtype) ⟨g ⟨Q1 h2,v⟩,S.mem ⟨Q1 h2,v⟩⟩) x
  spec2:∀ x,φ2 (ZK x)=
    Q39 (fun v=>Q1z G ⟨g ⟨Q3 h2,v⟩,S.mem ⟨Q3 h2,v⟩⟩) x
  spec3:∀ x,φ3 (ZK x)=
    Q39 (fun v=>Q36 G ⟨g ⟨Qa h2,v⟩,S.mem ⟨Qa h2,v⟩⟩) x
  card2:ZB (Q2f G)=p^∑ v,a ⟨Q3 h2,v⟩
  card3:ZB (Q5p G)=p^∑ v,a ⟨Qa h2,v⟩
lemma Q7.Q2t [Finite G] (S:Q7 p a g) (hp:0<p)
    (h2:2<c) (hlast:3<c∨lcs G 3=⊥)
    (b0:Fin (r (Q1 h2))→Fin (r (Q1 h2))→ℕ)
    (b1:Fin (r (Q3 h2))→Fin (r (Q3 h2))→ℕ)
    (b2:Fin (r (Qa h2))→Fin (r (Qa h2))→ℕ)
    (hb0:∀ j v,(S.Ql ⟨Q1 h2,j⟩ ⟨Q1 h2,v⟩).val=b0 j v)
    (hb1:∀ j v,(S.Ql ⟨Q3 h2,j⟩ ⟨Q3 h2,v⟩).val=b1 j v)
    (hb2:∀ j v,(S.Ql ⟨Qa h2,j⟩ ⟨Qa h2,v⟩).val=b2 j v):
    Nonempty (S.Q27 h2 b0 b1 b2):=by
 obtain ⟨φ1,h1⟩:=S.Qin hp (by omega) (Or.inl (by omega)) b0 hb0
 obtain ⟨φ2,h2'⟩:=S.Qi4 hp (by omega) (Or.inl h2) b1 hb1
 obtain ⟨φ3,h3⟩:=S.Qic hp h2 hlast b2 hb2
 have c2:=S.Q8d hp (Q3 h2) (Or.inl (show (1:ℕ)+1<c by omega)) (Q1z G)
   Q4z (fun x =>Q3b x)
 have c3:=S.Q8d hp (Qa h2) hlast (Q36 G) (Q5b G)
   (fun x =>Q38 x)
 exact ⟨⟨φ1,φ2,φ3,h1,h2',h3,c2,c3⟩⟩
variable {S:Q7 p a g} {h2:2<c} {b0:Fin (r (Q1 h2))→Fin (r (Q1 h2))→ℕ}
  {b1:Fin (r (Q3 h2))→Fin (r (Q3 h2))→ℕ} {b2:Fin (r (Qa h2))→Fin (r (Qa h2))→ℕ}
lemma Q7.Q27.Q99 (I:S.Q27 h2 b0 b1 b2) (v:Fin (r (Q1 h2))):
    Qe I.φ1 (ZH (g ⟨Q1 h2,v⟩))=
      ZI (ZK (Pi.single v (1:ℤ))):=
  Q9n _ ((I.spec1 _).trans (Q71 _ v))
lemma Q7.Q27.Qj6 (I:S.Q27 h2 b0 b1 b2) (v:Fin (r (Q3 h2))):
    Qe I.φ2 (Q1z G ⟨g ⟨Q3 h2,v⟩,S.mem ⟨Q3 h2,v⟩⟩)=
      ZI (ZK (Pi.single v (1:ℤ))):=
  Q9n _ ((I.spec2 _).trans (Q71 _ v))
lemma Q7.Q27.Q91 (I:S.Q27 h2 b0 b1 b2) {x:G} (hx:x∈lcs G 1):
    Qe I.φ2 (Q1z G ⟨x,hx⟩)=ZI
      (ZK (fun v=> ((S.nf.coord x ⟨Q3 h2,v⟩:ℕ):ℤ))):=
  Q9n _ (S.Q6w (Q3 h2) (Q1z G) (fun y hy=> (Q3b y).2 hy)
    b1 I.φ2 I.spec2 hx)
lemma Q7.Q27.Qej (I:S.Q27 h2 b0 b1 b2) {x:G} (hx:x∈lcs G 2):
    Qe I.φ3 (Q36 G ⟨x,hx⟩)=ZI
      (ZK (fun v=> ((S.nf.coord x ⟨Qa h2,v⟩:ℕ):ℤ))):=
  Q9n _ (S.Q6w (Qa h2) (Q36 G) (fun y hy=> (Q38 y).2 hy)
    b2 I.φ3 I.spec3 hx)
variable {G':Type u} [Group G'] {g':Q6 c r→G'} {S':Q7 p a g'}
lemma Q7.Qfy (hp:0<p) (I:S.Q27 h2 b0 b1 b2)
    (I':S'.Q27 h2 b0 b1 b2)
    (hT1:Q4a (Qe I.φ1) (Qe I.φ2)=Q4a (Qe I'.φ1) (Qe I'.φ2))
    (hT2:Q4j (Qe I.φ1) (Qe I.φ2) (Qe I.φ3)=
      Q4j (Qe I'.φ1) (Qe I'.φ2) (Qe I'.φ3)):
    S.Q14 h2=S'.Q14 h2∧S.Q1v h2=S'.Q1v h2:=by
 have ha:∀ i,Qe I.φ1 (ZH (g ⟨Q1 h2,i⟩))=
     Qe I'.φ1 (ZH (g' ⟨Q1 h2,i⟩)):= fun i=>
   (I.Q99 i).trans (I'.Q99 i).symm
 constructor
 · funext j k
   have hc:=Qif (Qe I.φ1) (Qe I.φ2) (Qe I'.φ1) (Qe I'.φ2) hT1
     (fun i=>g ⟨Q1 h2,i⟩) (fun i=>g' ⟨Q1 h2,i⟩) ha j k
   have hc':=((I.Q91 (cw (g ⟨Q1 h2,j⟩) (g ⟨Q1 h2,k⟩)).2).symm.trans hc).trans
     (I'.Q91 (cw (g' ⟨Q1 h2,j⟩) (g' ⟨Q1 h2,k⟩)).2)
   exact Qg3 hp _ b1 I.φ2 I.card2 (S.Q14 h2 j k) (S'.Q14 h2 j k)
     (fun v=> (S.nf.coord ⁅g ⟨Q1 h2,j⟩,g ⟨Q1 h2,k⟩⁆ ⟨Q3 h2,v⟩).isLt)
     (fun v=> (S'.nf.coord ⁅g' ⟨Q1 h2,j⟩,g' ⟨Q1 h2,k⟩⁆ ⟨Q3 h2,v⟩).isLt)
     (Multiplicative.ofAdd.injective hc')
 · funext j k
   have hw:Qe I.φ2 (Q1z G ⟨g ⟨Q3 h2,j⟩,S.mem ⟨Q3 h2,j⟩⟩)=
       Qe I'.φ2 (Q1z G' ⟨g' ⟨Q3 h2,j⟩,S'.mem ⟨Q3 h2,j⟩⟩):=
     (I.Qj6 j).trans (I'.Qj6 j).symm
   have hc:=Qip (Qe I.φ1) (Qe I.φ2) (Qe I.φ3) (Qe I'.φ1)
     (Qe I'.φ2) (Qe I'.φ3) hT2 _ _ hw (g ⟨Q1 h2,k⟩) (g' ⟨Q1 h2,k⟩) (ha k)
   have hc':=((I.Qej (Q7s ⟨g ⟨Q3 h2,j⟩,S.mem ⟨Q3 h2,j⟩⟩
       (g ⟨Q1 h2,k⟩)).2).symm.trans hc).trans
     (I'.Qej (Q7s ⟨g' ⟨Q3 h2,j⟩,S'.mem ⟨Q3 h2,j⟩⟩ (g' ⟨Q1 h2,k⟩)).2)
   exact Qg3 hp _ b2 I.φ3 I.card3 (S.Q1v h2 j k) (S'.Q1v h2 j k)
     (fun v=> (S.nf.coord ⁅g ⟨Q3 h2,j⟩,g ⟨Q1 h2,k⟩⁆ ⟨Qa h2,v⟩).isLt)
     (fun v=> (S'.nf.coord ⁅g' ⟨Q3 h2,j⟩,g' ⟨Q1 h2,k⟩⁆ ⟨Qa h2,v⟩).isLt)
     (Multiplicative.ofAdd.injective hc')
end LfLead
section LfLeadCount
variable {p c:ℕ} {r :Fin c→ℕ} {a:Q6 c r→ℕ}
lemma Qed (hp:p.Prime) (h2:2<c)
    (b0:Fin (r (Q1 h2))→Fin (r (Q1 h2))→ℕ)
    (b1:Fin (r (Q3 h2))→Fin (r (Q3 h2))→ℕ)
    (b2:Fin (r (Qa h2))→Fin (r (Qa h2))→ℕ) {s:ℕ} (hs:s≤ r (Q1 h2))
    (D:Finset (Fin (r (Q1 h2))×Fin (r (Q1 h2))))
    (hD:∀ q∈D,q.1<q.2∧(q.1:ℕ)<s)
    (w:Fin (r (Q1 h2))×Fin (r (Q1 h2))→Fin (r (Q3 h2))→ℕ)
    (Λ :Set ((Fin (r (Q1 h2))→Fin (r (Q1 h2))→Fin (r (Q3 h2))→ℕ)×
      (Fin (r (Q3 h2))→Fin (r (Q1 h2))→Fin (r (Qa h2))→ℕ)))
    (hΛ :∀ x∈Λ,∃ (G:Type u) (_:Group G) (_:Finite G) (g:Q6 c r→G)
      (S:Q7 p a g),
      (∀ j v,(S.Ql ⟨Q1 h2,j⟩ ⟨Q1 h2,v⟩).val=b0 j v)∧
      (∀ j v,(S.Ql ⟨Q3 h2,j⟩ ⟨Q3 h2,v⟩).val=b1 j v)∧
      (∀ j v,(S.Ql ⟨Qa h2,j⟩ ⟨Qa h2,v⟩).val=b2 j v)∧
      (3<c∨lcs G 3=⊥)∧
      lcs G 1≤⁅ZA ((fun j=>g ⟨Q1 h2,j⟩) '' {j | (j:ℕ)<s}),
        ZA ((fun j=>g ⟨Q1 h2,j⟩) '' {j | (j:ℕ)<s})⁆⊔lcs G 2∧
      (∀ q∈D,S.Q14 h2 q.1 q.2=w q)∧
      x =(S.Q14 h2,S.Q1v h2)):
    Λ.ncard≤∑ β∈(ZQ (min (∑ v,a ⟨Q3 h2,v⟩) (∑ v,a ⟨Qa h2,v⟩)+1)).filter
        (fun β=> (∑ v,a ⟨Qa h2,v⟩)≤ s*β),
      p ^ (s*(β *(r (Q3 h2)+(∑ v,a ⟨Qa h2,v⟩)+1 - β)))*
        p ^(((r (Q1 h2)).choose 2 - D.card)*(∑ v,a ⟨Q3 h2,v⟩) -
          (r (Q1 h2) - s).choose 2*β):=by
  classical
  have hp0:=hp.pos
  have:Finite (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0):=(Q11 hp0 _ b0).1
  have:Finite (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1):=(Q11 hp0 _ b1).1
  have:Finite (Q17 p (fun v=>a ⟨Qa h2,v⟩) b2):=(Q11 hp0 _ b2).1
  have:Finite (Multiplicative (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0)):=
    Finite.of_equiv _ ZI
  have:Finite (Multiplicative (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1)):=
    Finite.of_equiv _ ZI
  have:Finite (Multiplicative (Q17 p (fun v=>a ⟨Qa h2,v⟩) b2)):=
    Finite.of_equiv _ ZI
  rcases Λ.eq_empty_or_nonempty with hE | ⟨x0,hx0⟩
  · rw[hE,Set.ncard_empty]
    exact Nat.zero_le _
  obtain ⟨G0,_,_,g0,S0,hb0,hb1,hb2,hl, -, -, -⟩:=hΛ x0 hx0
  obtain ⟨I0⟩:=S0.Q2t hp0 h2 hl b0 b1 b2 hb0 hb1 hb2
  have hL2:=Q37 I0.φ2 I0.card2
  have hL3:=Q37 I0.φ3 I0.card3
  have:=Q49 (L1:=Multiplicative (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0))
    (L2:=Multiplicative (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1))
    (L3:=Multiplicative (Q17 p (fun v=>a ⟨Qa h2,v⟩) b2))
  let gg:Fin (r (Q1 h2))→Multiplicative (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0):=
    fun j=>ZI (ZK (Pi.single j (1:ℤ)))
  let yy:Fin (r (Q3 h2))→Multiplicative (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1):=
    fun j=>ZI (ZK (Pi.single j (1:ℤ)))
  let vv:Fin (r (Q1 h2))×Fin (r (Q1 h2))→
      Multiplicative (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1):=
    fun q=>ZI (ZK (fun v=> ((w q v:ℕ):ℤ)))
  obtain ⟨R, hR⟩:∃ R:((Fin (r (Q1 h2))→Fin (r (Q1 h2))→Fin (r (Q3 h2))→ℕ)×
      (Fin (r (Q3 h2))→Fin (r (Q1 h2))→Fin (r (Qa h2))→ℕ))→
      ((Multiplicative (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0)→*
          Multiplicative (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0)→*
            Multiplicative (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1))×
        (Multiplicative (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1)→*
          Multiplicative (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0)→*
            Multiplicative (Q17 p (fun v=>a ⟨Qa h2,v⟩) b2)))→Prop,R=
    fun x β=> ∃ (G:Type u) (_:Group G) (g:Q6 c r→G) (S:Q7 p a g)
      (I :S.Q27 h2 b0 b1 b2),x =(S.Q14 h2,S.Q1v h2)∧
        β=(Q4a (Qe I.φ1) (Qe I.φ2),Q4j (Qe I.φ1) (Qe I.φ2) (Qe I.φ3)):=
    ⟨_,rfl⟩
  have hfun:∀ x x' β,R x β→R x' β→x =x':=by
   intro x x' β h h'
   rw[hR]at h h'
   obtain ⟨G,_,g,S,I,rfl,rfl⟩:=h
   obtain ⟨G',_,g',S',I',rfl,hβ⟩:=h'
   obtain ⟨h1,h2'⟩:=Prod.mk.inj hβ
   obtain ⟨e1,e2⟩:=Q7.Qfy hp0 I I' h1 h2'
   rw[e1,e2]
  have hex:∀ x∈Λ,∃ β,β∈Qb7 (Multiplicative (Q17 p (fun v=>a ⟨Qa h2,v⟩) b2))
      s gg D vv∧R x β:=by
    intro x hx
    obtain ⟨G,_,_,g,S,hb0,hb1,hb2,hl,hcore,hDw,rfl⟩:=hΛ x hx
    obtain ⟨I⟩:=S.Q2t hp0 h2 hl b0 b1 b2 hb0 hb1 hb2
    refine ⟨_,Qgi (Qe I.φ1) (Qe I.φ2) (Qe I.φ3)
      (fun j=>g ⟨Q1 h2,j⟩) gg (fun j=>I.Q99 j) hcore D vv (fun q hq=>?_),?_⟩
    swap
    · rw[hR]
      exact ⟨G,inferInstance,g,S,I,rfl,rfl⟩
    refine (I.Q91 (cw (g ⟨Q1 h2,q.1⟩) (g ⟨Q1 h2,q.2⟩)).2).trans ?_
    show _=ZI (ZK (fun v=> ((w q v:ℕ):ℤ)))
    rw[← hDw q hq]
    rfl
  let F:= fun x =>if h:x∈Λ then Classical.choose (hex x h) else 1
  have hF:∀ x (h:x∈Λ),F x =Classical.choose (hex x h):= fun x h=>dif_pos h
  have hmaps:∀ x∈Λ,F x∈Qb7 (Multiplicative (Q17 p (fun v=>a ⟨Qa h2,v⟩) b2))
      s gg D vv:= fun x h=>by
    rw[hF x h]
    exact (Classical.choose_spec (hex x h)).1
  have hinj:Set.InjOn F Λ:=by
   intro x hx x' hx' he
   refine hfun x x' (F x) ?_ ?_
   · rw[hF x hx]
     exact (Classical.choose_spec (hex x hx)).2
   · rw[he,hF x' hx']
     exact (Classical.choose_spec (hex x' hx')).2
  refine (Set.ncard_le_ncard_of_injOn F hmaps hinj (Set.toFinite _)).trans ?_
  exact Qk5 hp hs hL2 hL3 yy (Q5q p _ b1) gg (Q5q p _ b0)
    D hD vv
end LfLeadCount
section LfFlat
variable {G:Type u} [Group G] {p:ℕ} {u:ℕ→G} {d:Q5} {X:Fin d.n→G}
  {r :ℕ→ℕ}
lemma Q2.Qij [Finite G] (hp:p.Prime) (hS:Q2 p u d X r) {c:ℕ}
    (hn:d.n=Q0 r c) (t k:Fin d.n) (hrec:d.Rec t k) (k':Q6 c (Q4y r c)):
    ((hS.toQ7 hp hn).nf.coord ⁅X t,X k⁆ k').val=d.c t k (hS.Q8 hn k'):=by
 have hcomm:⁅X t,X k⁆=Q2e X (d.c t k):=by
  rcases hrec with ⟨h1,h2,h3⟩ | ⟨h1,h2⟩ | ⟨h1,h2⟩
  · exact hS.realizes.comm0 t k h1 h2 h3
  · exact hS.realizes.comm1 t k h1 h2
  · exact hS.realizes.comm2 t k h1 h2
 have hx:=Classical.choose_spec (hS.nf_exists ⁅X t,X k⁆)
 have h2:=hS.nf_unique _ (d.c t k) hx.1 (fun v=>hS.bounded.2 t k v) (hx.2.symm.trans hcomm)
 show Classical.choose (hS.nf_exists ⁅X t,X k⁆) (hS.Q8 hn k')=_
 rw[h2]
lemma Q2.Q8w [Finite G] (hp:p.Prime) (hS:Q2 p u d X r) {c:ℕ}
    (hn:d.n=Q0 r c) (k1 k2 k3:Q6 c (Q4y r c))
    (hrec:d.Rec (hS.Q8 hn k1) (hS.Q8 hn k2)):
    Q2u d (hS.Q8 hn k1).val (hS.Q8 hn k2).val (hS.Q8 hn k3).val=
      ((hS.toQ7 hp hn).nf.coord
        ⁅X (hS.Q8 hn k1),X (hS.Q8 hn k2)⁆ k3).val:=by
 unfold Q2u
 rw [dif_pos (show _∧_∧_ from
   ⟨(hS.Q8 hn k1).isLt,(hS.Q8 hn k2).isLt,(hS.Q8 hn k3).isLt⟩)]
 refine (if_pos ?_).trans ?_
 · exact hrec
 · exact (hS.Qij hp hn _ _ hrec k3).symm
lemma Q2.Qhg (hS:Q2 p u d X r) {c:ℕ} (hn:d.n=Q0 r c) (h0:0<c)
    (hcore:lcs G 1≤⁅ZA (u '' ZP d.s),
      ZA (u '' ZP d.s)⁆⊔lcs G 2):
    d.s ≤ r 0∧lcs G 1≤⁅ZA ((fun j:Fin (Q4y r c ⟨0,h0⟩)=>
        X (hS.Q8 hn ⟨⟨0,h0⟩,j⟩)) '' {j | (j:ℕ)<d.s}),
      ZA ((fun j:Fin (Q4y r c ⟨0,h0⟩)=>
        X (hS.Q8 hn ⟨⟨0,h0⟩,j⟩)) '' {j | (j:ℕ)<d.s})⁆⊔lcs G 2:=by
  have e0:Q0 r 0=0:=rfl
  have hsn:=hS.valid.s_le
  have hsr :d.s≤ r 0:=by
   rcases Nat.eq_zero_or_pos d.s with h | h
   · omega
   · have hl:=hS.valid.core ⟨d.s - 1,by omega⟩ (show d.s - 1<d.s by omega)
     have:=((hS.layer_iff ⟨d.s - 1,by omega⟩ 0).mp hl).2
     rw[e0]at this
     show d.s≤ r 0
     have h':d.s - 1< r 0:=by simpa using this
     omega
  have hX:∀ (k:ℕ) (hk:k<d.s) (hkr :k<Q4y r c ⟨0,h0⟩),
      X (hS.Q8 hn ⟨⟨0,h0⟩,⟨k,hkr⟩⟩)=u k:=by
   intro k hk hkr
   have hv:hS.Q8 hn ⟨⟨0,h0⟩,⟨k,hkr⟩⟩=⟨k,by omega⟩:=by
     apply Fin.ext
     rw[hS.Q7o hn]
     show Q0 r 0+k=k
     rw[e0,zero_add]
   rw[hv]
   exact hS.core ⟨k,by omega⟩ hk
  have hset:u '' ZP d.s=(fun j:Fin (Q4y r c ⟨0,h0⟩)=>
      X (hS.Q8 hn ⟨⟨0,h0⟩,j⟩)) '' {j | (j:ℕ)<d.s}:=by
    ext z
    constructor
    · rintro ⟨k,hk,rfl⟩
      have hk':k<d.s:=hk
      exact ⟨⟨k,show k< r 0 by omega⟩,hk',hX k hk' _⟩
    · rintro ⟨j,hj,rfl⟩
      have hj':(j:ℕ)<d.s:=hj
      exact ⟨j.val,hj',(hX j.val hj' j.isLt).symm⟩
  rw[hset]at hcore
  exact ⟨hsr,hcore⟩
lemma Q2.Qef [Finite G] (hp:p.Prime) (hS:Q2 p u d X r) {c:ℕ}
    (hn:d.n=Q0 r c) (h2:2<c) (j k:Fin (Q4y r c (Q1 h2))) (hjk:j<k)
    (v:Fin (Q4y r c (Q3 h2))):
    Q2u d (hS.Q8 hn ⟨Q1 h2,j⟩).val (hS.Q8 hn ⟨Q1 h2,k⟩).val
        (hS.Q8 hn ⟨Q3 h2,v⟩).val=(hS.toQ7 hp hn).Q14 h2 j k v:=
  hS.Q8w hp hn _ _ _ (Or.inl ⟨hS.Q3h hn _,hS.Q3h hn _,by
    rw[Fin.lt_def,hS.Q7o hn,hS.Q7o hn]
    exact Nat.add_lt_add_left hjk _⟩)
lemma Q2.Qf2 [Finite G] (hp:p.Prime) (hS:Q2 p u d X r) {c:ℕ}
    (hn:d.n=Q0 r c) (h2:2<c) (j:Fin (Q4y r c (Q3 h2)))
    (k:Fin (Q4y r c (Q1 h2)))
    (hk:(k:ℕ)≤(d.df (hS.Q8 hn ⟨Q3 h2,j⟩)).2.val) (v:Fin (Q4y r c (Qa h2))):
    Q2u d (hS.Q8 hn ⟨Q3 h2,j⟩).val (hS.Q8 hn ⟨Q1 h2,k⟩).val
        (hS.Q8 hn ⟨Qa h2,v⟩).val=(hS.toQ7 hp hn).Q1v h2 j k v:=
  hS.Q8w hp hn _ _ _ (Or.inr (Or.inl ⟨hS.Q3h hn _,by
    rw[hS.Q7o hn]
    show 0+(k:ℕ)≤_
    omega⟩))
end LfFlat
section LfCBGen
lemma Qjr (d:Q5) (t k w:Fin d.n) (hrec:d.Rec t k):
    Q2u d t.val k.val w.val=d.c t k w:=by
 unfold Q2u
 rw[dif_pos ⟨t.isLt,k.isLt,w.isLt⟩]
 exact if_pos hrec
lemma Qkr {p:ℕ} (hp0:0<p) {d:Q5} (hb:d.Bounded p) (i j k:ℕ):
    Q2u d i j k<p^Q4l d k:=by
 unfold Q2u Q4l
 by_cases h:i<d.n∧j<d.n∧k<d.n
 · rw[dif_pos h,dif_pos h.2.2]
   split_ifs
   · exact hb.2 _ _ _
   · exact pow_pos hp0 _
 · rw[dif_neg h]
   exact pow_pos hp0 _
end LfCBGen
section LfCBGroup
variable {G:Type u} [Group G] {p:ℕ} {u:ℕ→G} {d:Q5} {X:Fin d.n→G}
  {r :ℕ→ℕ}
lemma Q2.Qbf (hS:Q2 p u d X r):
    lcs G 1≤⁅ZA (u '' ZP d.s),ZA (u '' ZP d.s)⁆⊔
      lcs G 2:=by
 refine (hS.layer_gen 1).trans (sup_le_sup_right ?_ _)
 rw[ZD]
 rintro _ ⟨t,ht,rfl⟩
 have ht':d.lv t=1:=ht
 have hdf:=hS.realizes.dfeq t (by omega)
 have h1:(d.df t).1< (d.df t).2:=hS.valid.df_one t ht'
 have h2:((d.df t).2:ℕ)<d.s:=hS.valid.df_core t (by omega)
 have hf:((d.df t).1:ℕ)<d.s:=lt_trans (Fin.lt_def.mp h1) h2
 rw[SetLike.mem_coe,hdf,hS.core _ hf,hS.core _ h2]
 exact Subgroup.commutator_mem_commutator (ZC ⟨_,hf,rfl⟩)
   (ZC ⟨_,h2,rfl⟩)
lemma Q2.Qga (hS:Q2 p u d X r) {c:ℕ} (hn:d.n=Q0 r c)
    (hc:1≤ c):lcs G c=⊥:=by
 rw[eq_bot_iff]
 refine (hS.deep c hc).trans ?_
 rw[ZD]
 rintro _ ⟨t,ht,rfl⟩
 exfalso
 have h1:=hS.Qff hn t
 have h2:c≤d.lv t:=ht
 omega
lemma Q2.Q8j (hS:Q2 p u d X r) (hn:d.n=Q0 r 3) {i j k:ℕ}
    (h:Q2u d i j k≠0):
    (i < j∧j<Q0 r 1∧Q0 r 1≤k∧k<Q0 r 3)∨
      (Q0 r 1≤ i∧i<Q0 r 2∧j<Q0 r 1∧j≤Qn d r (i - Q0 r 1)∧
        Q0 r 2≤k∧k<Q0 r 3):=by
 unfold Q2u at h
 by_cases hr :i<d.n∧j<d.n∧k<d.n
 swap
 · rw[dif_neg hr]at h
   exact absurd rfl h
 rw[dif_pos hr]at h
 by_cases hrec:d.Rec ⟨i,hr.1⟩ ⟨j,hr.2.1⟩
 swap
 · rw[if_neg hrec]at h
   exact absurd rfl h
 rw[if_pos hrec]at h
 have hsupp:=hS.valid.c_supp _ _ _ h
 have hk3:=hS.Qff hn ⟨k,hr.2.2⟩
 obtain ⟨ki1, -⟩:=(hS.layer_iff ⟨k,hr.2.2⟩ (d.lv ⟨k,hr.2.2⟩)).mp rfl
 have ki1':Q0 r (d.lv ⟨k,hr.2.2⟩)≤k:=ki1
 have e01:Q0 r 1=Q0 r 0+r 0:=Q19 r 0
 have e12:Q0 r 2=Q0 r 1+r 1:=Q19 r 1
 have e0:Q0 r 0=0:=rfl
 have hkn:k<Q0 r 3:=by rw[← hn]; exact hr.2.2
 rcases hrec with ⟨h1,h2,h3⟩ | ⟨h1,h2⟩ | ⟨h1, -⟩
 · left
   obtain ⟨-,j2⟩:=(hS.layer_iff ⟨j,hr.2.1⟩ 0).mp h2
   have j2':j<Q0 r 0+r 0:=j2
   have hk1:Q0 r 1≤Q0 r (d.lv ⟨k,hr.2.2⟩):=Q2i r (by omega)
   have h3':i<j:=h3
   exact ⟨h3',by omega,by omega,hkn⟩
 · right
   obtain ⟨i1,i2⟩:=(hS.layer_iff ⟨i,hr.1⟩ 1).mp h1
   have i1':Q0 r 1≤ i:=i1
   have i2':i<Q0 r 1+r 1:=i2
   have hlk:d.lv ⟨k,hr.2.2⟩=2:=by omega
   rw[hlk]at ki1'
   have hco:=Q3z d r ⟨i,hr.1⟩ (i - Q0 r 1)
     (by show Q0 r 1+(i - Q0 r 1)=i; omega)
   have hcs:=hS.valid.df_core ⟨i,hr.1⟩ (by omega)
   have hc0:=hS.valid.core (d.df ⟨i,hr.1⟩).2 hcs
   obtain ⟨-,c2⟩:=(hS.layer_iff _ 0).mp hc0
   have c2':((d.df ⟨i,hr.1⟩).2:ℕ)<Q0 r 0+r 0:= c2
   have h2':j≤((d.df ⟨i,hr.1⟩).2:ℕ):=h2
   refine ⟨i1',by omega,by omega,?_,ki1',hkn⟩
   rw[hco]
   exact h2'
 · exfalso
   omega
lemma Q2.Qj1 (hp:p.Prime) (hS:Q2 p u d X r) (t:Fin d.n)
    (hl:d.lv t=1) (k:ℕ):
    Q2u d (d.df t).1.val (d.df t).2.val k=if k=t.val then 1 else 0:=by
  have hlt:(d.df t).1< (d.df t).2:=hS.valid.df_one t hl
  have hcs:((d.df t).2:ℕ)<d.s:=hS.valid.df_core t (by omega)
  have hl0:d.lv (d.df t).1=0:=by
   have:=hS.valid.df_lv t (by omega)
   omega
  have hl0':d.lv (d.df t).2=0:=hS.valid.core _ hcs
  have hcomm:=hS.realizes.comm0 _ _ hl0 hl0' hlt
  have hdf:=hS.realizes.dfeq t (by omega)
  have hbd:∀ v,delta t 1 v<p^d.a v:=by
   intro v
   unfold delta
   split_ifs
   · exact one_lt_pow' hp.one_lt (by have:=hS.a_pos v; omega)
   · exact pow_pos hp.pos _
  have heq:=hS.nf_unique (d.c (d.df t).1 (d.df t).2) (delta t 1)
    (fun v=>hS.bounded.2 _ _ v) hbd
    (hcomm.symm.trans (hdf.symm.trans (by rw[Qhw,pow_one])))
  by_cases hk:k<d.n
  · show Q2u d (d.df t).1.val (d.df t).2.val (⟨k,hk⟩:Fin d.n).val=_
    rw[Qjr d (d.df t).1 (d.df t).2 ⟨k,hk⟩ (Or.inl ⟨hl0,hl0',hlt⟩),heq]
    show (if (⟨k,hk⟩:Fin d.n)=t then 1 else 0)=_
    by_cases hkt:k=t.val
    · rw[if_pos (Fin.ext hkt:(⟨k,hk⟩:Fin d.n)=t),if_pos hkt]
    · rw[if_neg (fun h'=>hkt (congrArg Fin.val h')),if_neg hkt]
  · have h1:Q2u d (d.df t).1.val (d.df t).2.val k=0:=by
      unfold Q2u
      rw[dif_neg (fun h'=>hk h'.2.2)]
    rw[h1,if_neg (by have:=t.isLt; omega)]
lemma Q2.Qfi (hp:p.Prime) (hS:Q2 p u d X r) (hs2:2≤d.s) {j:ℕ}
    (hj:j< r 1) (k:ℕ):
    Q2u d (Q8b d r j) (Qn d r j) k=if k=Q0 r 1+j then 1 else 0:=by
  obtain ⟨h,hl⟩:=hS.Q6g hs2 j hj
  rw[Q7k d r ⟨Q0 r 1+j,h⟩ j rfl,Q3z d r ⟨Q0 r 1+j,h⟩ j rfl]
  exact hS.Qj1 hp ⟨Q0 r 1+j,h⟩ hl k
lemma Q2.Q6q (hS:Q2 p u d X r) (hs2:2≤d.s) {j:ℕ}
    (hj:j< r 1):Q8b d r j<Qn d r j:=by
 obtain ⟨h,hl⟩:=hS.Q6g hs2 j hj
 rw[Q7k d r ⟨Q0 r 1+j,h⟩ j rfl,Q3z d r ⟨Q0 r 1+j,h⟩ j rfl]
 exact hS.valid.df_one _ hl
lemma Q2.Qa7 (hS:Q2 p u d X r) (hs2:2≤d.s) {j j':ℕ}
    (hj:j< r 1) (hj':j'< r 1) (h1:Q8b d r j=Q8b d r j')
    (h2:Qn d r j=Qn d r j'):j=j':=by
 obtain ⟨h,hl⟩:=hS.Q6g hs2 j hj
 obtain ⟨h',hl'⟩:=hS.Q6g hs2 j' hj'
 rw[Q7k d r ⟨Q0 r 1+j,h⟩ j rfl,Q7k d r ⟨Q0 r 1+j',h'⟩ j' rfl]at h1
 rw[Q3z d r ⟨Q0 r 1+j,h⟩ j rfl,Q3z d r ⟨Q0 r 1+j',h'⟩ j' rfl]at h2
 have e:=hS.block_inj _ _ hl hl' (Fin.ext h1) (Fin.ext h2)
 have e':Q0 r 1+j=Q0 r 1+j':= congrArg Fin.val e
 omega
lemma Q2.Qfk [Finite G] (hp:p.Prime) (hS:Q2 p u d X r) {c:ℕ}
    (hn:d.n=Q0 r c) (h2:2<c) (r':Fin c→ℕ) (hr :∀ i:Fin c,r i.val=r' i)
    (a':Q6 c r'→ℕ) (ha:∀ k:Q6 c r',a' k=Q4l d (Q0 r k.1.val+k.2.val)):
    ∃ (g':Q6 c r'→G) (S:Q7 p a' g'),
      (∀ (i:Fin c) (j v:Fin (r' i)),(S.Ql ⟨i,j⟩ ⟨i,v⟩).val=
        Q8h d (Q0 r i.val+j.val) (Q0 r i.val+v.val))∧
      (∀ (j k:Fin (r' (Q1 h2))) (v:Fin (r' (Q3 h2))),j<k→
        S.Q14 h2 j k v=Q2u d (Q0 r 0+j.val) (Q0 r 0+k.val) (Q0 r 1+v.val))∧
      (∀ (j:Fin (r' (Q3 h2))) (k:Fin (r' (Q1 h2))) (v:Fin (r' (Qa h2))),
        k.val≤Qn d r j.val→
        S.Q1v h2 j k v=Q2u d (Q0 r 1+j.val) (Q0 r 0+k.val) (Q0 r 2+v.val))∧
      lcs G 1≤⁅ZA ((fun j=>g' ⟨Q1 h2,j⟩) '' {j | (j:ℕ)<d.s}),
        ZA ((fun j=>g' ⟨Q1 h2,j⟩) '' {j | (j:ℕ)<d.s})⁆⊔lcs G 2:=by
  have hr':Q4y r c=r':= funext hr
  subst hr'
  have ha':a'= fun k=>d.a (hS.Q8 hn k):=
    funext fun k=> (ha k).trans (hS.Qad hn k)
  subst ha'
  refine ⟨fun k=>X (hS.Q8 hn k),hS.toQ7 hp hn,fun i j v=>?_,
    fun j k v hjk=>?_,fun j k v hk=>?_,?_⟩
  · exact (hS.Qdg hp hn ⟨i,j⟩ ⟨i,v⟩).symm
  · exact (hS.Qef hp hn h2 j k hjk v).symm
  · have hk':(k:ℕ)≤(d.df (hS.Q8 hn ⟨Q3 h2,j⟩)).2.val:=by
      rw[← Q3z d r (hS.Q8 hn ⟨Q3 h2,j⟩) j.val rfl]
      exact hk
    exact (hS.Qf2 hp hn h2 j k hk' v).symm
  · exact (hS.Qhg hn (by omega) hS.Qbf).2
end LfCBGroup
section LfCBCount
def Q3x {p m:ℕ} (D:Qg m)
    (C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)) (i j k:ℕ):ℕ:=
  if h:i<D.2.2.1.tot∧j<D.2.2.1.tot∧k<D.2.2.1.tot then
    (C ⟨i,h.1⟩ ⟨j,h.2.1⟩ ⟨k,h.2.2⟩).val
  else 0
def Qnt {p m:ℕ} (D:Qg m) (B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m))
    (i j:ℕ):ℕ:=
  if h:i<D.2.2.1.tot∧j<D.2.2.1.tot then (B ⟨i,h.1⟩ ⟨j,h.2⟩).val else 0
def Qnv {m:ℕ} (D:Qg m) (k:ℕ):ℕ:=
  if h:k<D.2.1.val - 1 then (D.2.2.2.1.1 ⟨k,h⟩).val else 0
def Q13 {m:ℕ} (D:Qg m) (j:ℕ):ℕ:=
  if h:j<D.2.2.1.r2 then (D.2.2.2.2.1.1 ⟨j,h⟩).val else 0
lemma Qjo {p m:ℕ} (D:Qg m)
    (C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m))
    (i j k:Fin D.2.2.1.tot):Q3x D C i.val j.val k.val=(C i j k).val:=by
 unfold Q3x
 rw[dif_pos ⟨i.isLt,j.isLt,k.isLt⟩]
lemma Q2.Q6d {G:Type u} [Group G] {p:ℕ} {u:ℕ→G} {d:Q5}
    {X:Fin d.n→G} {r :ℕ→ℕ} [Finite G] (hp:p.Prime) (hS:Q2 p u d X r) {m:ℕ}
    (hnm:d.n≤ m) (hs2:2≤d.s) (hsum:∑ t,d.a t=m) {D:Qg m}
    {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    {C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    (e:hS.enc hp m hnm hs2 hsum=⟨D,(B,C)⟩):
    hS.nL=D.1.val∧d.s=D.2.1.val∧(∀ i<hS.nL,r i=Q9 D i)∧Q4l d=Q6x D ∧
      Q3x D C=Q2u d∧Qnt D B=Q8h d∧(∀ k<d.s - 1,Q5g d r k=Qnv D k)∧
      (∀ j< r 1,Q8b d r j=Q13 D j):=by
 refine ⟨(hS.Qhb hp hnm hs2 hsum).symm.trans (congrArg Qn3 e),
   (hS.Qgw hp hnm hs2 hsum).symm.trans (congrArg Qnj e),fun i hi=>?_,?_,?_,?_,
   fun k hk=>?_,fun j hj=>?_⟩
 · have h:= congrFun (congrArg Qn1 e) i
   rw[hS.Qdd hp hnm hs2 hsum,dif_pos hi]at h
   exact h
 · funext j
   exact (hS.Qde hp hnm hs2 hsum j).symm.trans (congrFun (congrArg Qll e) j)
 · funext i j k
   exact ((hS.Qeq hp hnm hs2 hsum i j k).symm.trans
     (congrFun (congrFun (congrFun (congrArg Ql1 e) i) j) k)).symm
 · funext i j
   exact ((hS.Qdb hp hnm hs2 hsum i j).symm.trans
     (congrFun (congrFun (congrArg Qmf e) i) j)).symm
 · have h:= congrFun (congrArg Qkm e) k
   rw[hS.Qd6 hp hnm hs2 hsum,dif_pos hk]at h
   exact h
 · have h:= congrFun (congrArg Qnp e) j
   rw [hS.Qgq hp hnm hs2 hsum,dif_pos (show j< (hS.Q22 hp hnm).r2 by
     rw[hS.Q5h hp hnm hs2]; exact hj)]at h
   exact h
lemma Qau {G₁ G₂:Type u} [Group G₁] [Group G₂] {p:ℕ} {u₁:ℕ→G₁}
    {d₁:Q5} {X₁:Fin d₁.n→G₁} {r₁:ℕ→ℕ} {u₂:ℕ→G₂} {d₂:Q5}
    {X₂:Fin d₂.n→G₂} {r₂:ℕ→ℕ} (hS₁:Q2 p u₁ d₁ X₁ r₁)
    (hS₂:Q2 p u₂ d₂ X₂ r₂) (hs₁:2≤d₁.s) (hs:d₁.s=d₂.s) (hr1:r₁ 1=r₂ 1)
    (hfib:∀ k<d₁.s - 1,Q5g d₁ r₁ k=Q5g d₂ r₂ k):
    ∀ j< r₁ 1,Qn d₁ r₁ j=Qn d₂ r₂ j:=by
 have hs₂:2≤d₂.s:=by omega
 have hfib':∀ k,((ZQ (r₁ 1)).filter (fun j=>Qn d₁ r₁ j=k)).card=
     ((ZQ (r₁ 1)).filter (fun j=>Qn d₂ r₂ j=k)).card:=by
   intro k
   by_cases hk:1≤k∧k<d₁.s
   · have h:=hfib (k - 1) (by omega)
     unfold Q5g at h
     rw[← hr1,show k - 1+1=k by omega]at h
     exact h
   · have e1:(ZQ (r₁ 1)).filter (fun j=>Qn d₁ r₁ j=k)= ∅ :=
       Finset.filter_eq_empty_iff.mpr fun j hj=>by
         have:=hS₁.Q3n hs₁ j (Finset.mem_range.mp hj)
         omega
     have e2:(ZQ (r₁ 1)).filter (fun j=>Qn d₂ r₂ j=k)= ∅ :=
       Finset.filter_eq_empty_iff.mpr fun j hj=>by
         have hj':j< r₂ 1:=by rw[← hr1]; exact Finset.mem_range.mp hj
         have:=hS₂.Q3n hs₂ j hj'
         omega
     rw[e1,e2]
 intro j hj
 exact Q8r _ _ _ (fun i j hij hj=>hS₁.Q9q hs₁ i j hij hj)
   (fun i j hij hj=>hS₂.Q9q hs₂ i j hij (by rw[← hr1]; exact hj)) hfib' j hj
abbrev Q5e {m:ℕ} (D:Qg m) (h2:2<D.1.val):Type:=
  (Fin (Q4 D (Q1 h2))→Fin (Q4 D (Q1 h2))→Fin (Q4 D (Q3 h2))→ℕ)×
    (Fin (Q4 D (Q3 h2))→Fin (Q4 D (Q1 h2))→Fin (Q4 D (Qa h2))→ℕ)
abbrev Qdf (p:ℕ) {m:ℕ} (D:Qg m) (h2:2<D.1.val):Type:=
  (v:Fin (Q4 D (Qa h2)))→Fin (p^Qc D ⟨Qa h2,v⟩)
def Q3d {p m:ℕ} (D:Qg m) (h2:2<D.1.val)
    (C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)):Q5e D h2:=
  (fun j k v=>Q3x D C (Q0 (Q9 D) 0+j.val) (Q0 (Q9 D) 0+k.val)
      (Q0 (Q9 D) 1+v.val),
    fun j k v=>Q3x D C (Q0 (Q9 D) 1+j.val) (Q0 (Q9 D) 0+k.val)
      (Q0 (Q9 D) 2+v.val))
def Q6o {p m:ℕ} (hp0:0<p) (D:Qg m) (h2:2<D.1.val)
    (C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)):
    Fin (Q4 D (Q1 h2))×Fin (Q4 D (Q1 h2))→Qdf p D h2:=
  fun q v=> ⟨Q3x D C (Q0 (Q9 D) 0+q.1.val) (Q0 (Q9 D) 0+q.2.val)
      (Q0 (Q9 D) 2+v.val) % p^Qc D ⟨Qa h2,v⟩,Nat.mod_lt _ (pow_pos hp0 _)⟩
def Q4s {m:ℕ} (D:Qg m) (h2:2<D.1.val) (co:ℕ→ℕ) (x:Q5e D h2):
    Q5e D h2:=
  (fun j k v=>if j<k then x.1 j k v else 0,
    fun j k v=>if k.val≤ co j.val then x.2 j k v else 0)
def Q2h {m:ℕ} (D:Qg m) (h2:2<D.1.val) (f co:ℕ→ℕ):
    Finset (Fin (Q4 D (Q1 h2))×Fin (Q4 D (Q1 h2))):=
  Finset.univ.filter (fun q=> ∃ j:Fin (Q4 D (Q3 h2)),q.1.val= f j.val∧q.2.val= co j.val)
def Q9w {m:ℕ} (D:Qg m) (h2:2<D.1.val) (f co:ℕ→ℕ)
    (q:Fin (Q4 D (Q1 h2))×Fin (Q4 D (Q1 h2))) (v:Fin (Q4 D (Q3 h2))):ℕ:=
  if q.1.val= f v.val∧q.2.val= co v.val then 1 else 0
def Q18 {p m:ℕ} (D:Qg m) (B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m))
    (i:Fin D.1.val) (j v:Fin (Q4 D i)):ℕ:=
  Qnt D B (Q0 (Q9 D) i.val+j.val) (Q0 (Q9 D) i.val+v.val)
def Q8m (p:ℕ) {m:ℕ} (D:Qg m) (h2:2<D.1.val)
    (b0:Fin (Q4 D (Q1 h2))→Fin (Q4 D (Q1 h2))→ℕ)
    (b1:Fin (Q4 D (Q3 h2))→Fin (Q4 D (Q3 h2))→ℕ)
    (b2:Fin (Q4 D (Qa h2))→Fin (Q4 D (Qa h2))→ℕ)
    (Dp:Finset (Fin (Q4 D (Q1 h2))×Fin (Q4 D (Q1 h2))))
    (w:Fin (Q4 D (Q1 h2))×Fin (Q4 D (Q1 h2))→Fin (Q4 D (Q3 h2))→ℕ):
    Set (Q5e D h2):=
  {x | (∃ (G:Type) (_:Group G) (_:Finite G) (g:Q6 D.1.val (Q4 D)→G)
      (S:Q7 p (Qc D) g),
      (∀ j v,(S.Ql ⟨Q1 h2,j⟩ ⟨Q1 h2,v⟩).val=b0 j v)∧
      (∀ j v,(S.Ql ⟨Q3 h2,j⟩ ⟨Q3 h2,v⟩).val=b1 j v)∧
      (∀ j v,(S.Ql ⟨Qa h2,j⟩ ⟨Qa h2,v⟩).val=b2 j v)∧
      (3<D.1.val∨lcs G 3=⊥)∧
      lcs G 1≤⁅ZA ((fun j=>g ⟨Q1 h2,j⟩) '' {j | (j:ℕ)<D.2.1.val}),
        ZA ((fun j=>g ⟨Q1 h2,j⟩) '' {j | (j:ℕ)<D.2.1.val})⁆⊔lcs G 2∧
      (∀ q∈Dp,S.Q14 h2 q.1 q.2=w q)∧
      x =(S.Q14 h2,S.Q1v h2))∧
    (∀ j k v,x.1 j k v<p^Qc D ⟨Q3 h2,v⟩)∧
    (∀ j k v,x.2 j k v<p^Qc D ⟨Qa h2,v⟩)}
def Q5y (p:ℕ) {m:ℕ} (hp0:0<p) (D:Qg m) (h2:2<D.1.val)
    (Dp:Finset (Fin (Q4 D (Q1 h2))×Fin (Q4 D (Q1 h2)))):
    Set (Fin (Q4 D (Q1 h2))×Fin (Q4 D (Q1 h2))→Qdf p D h2):=
  {c | ∀ q,q∉(Finset.univ.filter
      (fun q:Fin (Q4 D (Q1 h2))×Fin (Q4 D (Q1 h2))=>q.1<q.2)) \ Dp→
    c q= fun _=> ⟨0,pow_pos hp0 _⟩}
structure Qd9 (p:ℕ) {m:ℕ} (hp0:0<p) (D:Qg m) (h2:2<D.1.val)
    (B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)) (co:ℕ→ℕ)
    (C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)):Prop where
  zero : ∀ i j k,Q3x D C i j k≠0→
    (i < j∧j<Q0 (Q9 D) 1∧Q0 (Q9 D) 1≤k∧k<Q0 (Q9 D) 3)∨
      (Q0 (Q9 D) 1≤ i∧i<Q0 (Q9 D) 2∧j<Q0 (Q9 D) 1∧
        Q0 (Q9 D) 2≤k∧k<Q0 (Q9 D) 3)
  bd:∀ i j k,Q3x D C i j k<p^Q6x D k
  lead :∃ x∈Q8m p D h2 (Q18 D B (Q1 h2)) (Q18 D B (Q3 h2)) (Q18 D B (Qa h2))
      (Q2h D h2 (Q13 D) co) (Q9w D h2 (Q13 D) co),Q3d D h2 C=Q4s D h2 co x
  deep:Q6o hp0 D h2 C∈Q5y p hp0 D h2 (Q2h D h2 (Q13 D) co)
lemma Q2.Qkd {G:Type} [Group G] [Finite G] {p:ℕ} {u:ℕ→G} {d:Q5}
    {X:Fin d.n→G} {r :ℕ→ℕ} (hp:p.Prime) (hS:Q2 p u d X r) {m:ℕ}
    (hnm:d.n≤ m) (hs2:2≤d.s) (hsum:∑ t,d.a t=m) {D:Qg m}
    {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    {C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    (e:hS.enc hp m hnm hs2 hsum=⟨D,(B,C)⟩) (h2:2<D.1.val) (h3:D.1.val=3)
    (co:ℕ→ℕ) (hco:∀ j< r 1,Qn d r j= co j):
    Qd9 p hp.pos D h2 B co C:=by
 obtain ⟨cf1,cf2,cf3,cf4,cf5,cf6, -,cf8⟩:=hS.Q6d hp hnm hs2 hsum e
 have hn:d.n=Q0 r D.1.val:=by rw[← cf1]; exact hS.Q2j.symm
 have hfo:∀ w≤D.1.val,Q0 r w=Q0 (Q9 D) w:=
   Q41 (fun w hw=>cf3 w (by rw[cf1]; exact hw))
 have hn3:d.n=Q0 r 3:=by rw[hn,h3]
 have f1:=hfo 1 (by omega)
 have f2:=hfo 2 (by omega)
 have f3:=hfo 3 (by omega)
 have e0:Q0 r 0=0:=rfl
 have e0':Q0 (Q9 D) 0=0:=rfl
 have e01:Q0 r 1=Q0 r 0+r 0:=Q19 r 0
 have e12:Q0 r 2=Q0 r 1+r 1:=Q19 r 1
 have hr0:r 0=Q9 D 0:= cf3 0 (by rw[cf1]; omega)
 have hr1:r 1=Q9 D 1:= cf3 1 (by rw[cf1]; omega)
 obtain ⟨g',S,hpw,hl1,hl2,hcore⟩:=hS.Qfk hp hn h2 (Q4 D)
   (fun i=>cf3 i.val (by rw[cf1]; exact i.isLt)) (Qc D) (fun k=>by
     show Q6x D (Q0 (Q9 D) k.1.val+k.2.val)=_
     rw[cf4,hfo _ k.1.isLt.le])
 have hpwB:∀ (i:Fin D.1.val) (j v:Fin (Q4 D i)),
     (S.Ql ⟨i,j⟩ ⟨i,v⟩).val=Q18 D B i j v:=by
  intro i j v
  rw[hpw, ← cf6]
  unfold Q18
  rw[hfo _ i.isLt.le]
 refine ⟨fun i j k h=>?_,fun i j k=>?_,
   ⟨(S.Q14 h2,S.Q1v h2),⟨⟨G,inferInstance,inferInstance,g',S,hpwB (Q1 h2),
     hpwB (Q3 h2),hpwB (Qa h2),?_,?_,?_,rfl⟩,fun j k v=>Fin.isLt _,
     fun j k v=>Fin.isLt _⟩,?_⟩,?_⟩
 ·
   rw[cf5]at h
   have hz:=hS.Q8j hn3 h
   rw[f1,f2,f3]at hz
   rcases hz with ⟨a1,a2,a3,a4⟩ | ⟨b1,b2,b3, -,b5,b6⟩
   · exact Or.inl ⟨a1,a2,a3,a4⟩
   · exact Or.inr ⟨b1,b2,b3,b5,b6⟩
 ·
   rw[cf5, ← cf4]
   exact Qkr hp.pos hS.bounded i j k
 ·
   have hb:=hS.Qga hn (by omega)
   rw[h3]at hb
   exact Or.inr hb
 ·
   rw[← cf2]
   exact hcore
 ·
   intro q hq
   obtain ⟨j,hj1,hj2⟩:=(Finset.mem_filter.mp hq).2
   have hjr :j.val< r 1:=by
    have:j.val<Q9 D 1:=j.isLt
    omega
   rw[← cf8 _ hjr]at hj1
   rw[← hco _ hjr]at hj2
   have hlt:q.1<q.2:=by
    show q.1.val<q.2.val
    rw[hj1,hj2]
    exact hS.Q6q hs2 hjr
   funext v
   have hv:v.val< r 1:=by
    have:v.val<Q9 D 1:=v.isLt
    omega
   rw [hl1 q.1 q.2 v hlt,e0,Nat.zero_add,Nat.zero_add,hj1,hj2,
     hS.Qfi hp hs2 hjr]
   unfold Q9w
   rw[hj1,hj2, ← cf8 _ hv, ← hco _ hv]
   by_cases hvj:v.val=j.val
   · rw[if_pos (by omega),if_pos ⟨by rw[hvj],by rw[hvj]⟩]
   · rw[if_neg (by omega),if_neg]
     rintro ⟨h1',h2'⟩
     exact hvj (hS.Qa7 hs2 hv hjr h1'.symm h2'.symm)
 ·
   refine Prod.ext (funext fun j=>funext fun k=>funext fun v=>?_)
     (funext fun j=>funext fun k=>funext fun v=>?_)
   · show Q3x D C (Q0 (Q9 D) 0+j.val) (Q0 (Q9 D) 0+k.val)
         (Q0 (Q9 D) 1+v.val)=if j<k then S.Q14 h2 j k v else 0
     rw[cf5,e0', ← f1]
     split_ifs with hjk
     · rw[hl1 j k v hjk,e0]
     · by_contra hne
       have hj0:j.val<Q9 D 0:=j.isLt
       rcases hS.Q8j hn3 hne with ⟨a1, -⟩ | ⟨b1, -⟩
       · exact hjk (by show j.val<k.val; omega)
       · omega
   · show Q3x D C (Q0 (Q9 D) 1+j.val) (Q0 (Q9 D) 0+k.val)
         (Q0 (Q9 D) 2+v.val)=if k.val≤ co j.val then S.Q1v h2 j k v else 0
     have hj1:j.val< r 1:=by
      have:j.val<Q9 D 1:=j.isLt
      omega
     rw[cf5,e0', ← f1, ← f2, ← hco j.val hj1]
     split_ifs with hk
     · rw[hl2 j k v hk,e0]
     · by_contra hne
       have hk0:k.val<Q9 D 0:=k.isLt
       rcases hS.Q8j hn3 hne with ⟨a1,a2, -, -⟩ | ⟨-, -, -,b4, -, -⟩
       · omega
       · rw[Nat.add_sub_cancel_left]at b4
         exact hk (by omega)
 ·
   simp only[Q5y,Set.mem_ofPred_eq]
   intro q hq
   funext v
   apply Fin.ext
   have hz:Q2u d q.1.val q.2.val (Q0 r 2+v.val)=0:=by
    by_cases hlt:q.1<q.2
    · have hqD:q∈Q2h D h2 (Q13 D) co:=by
        by_contra hc
        exact hq (Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,hlt⟩,hc⟩)
      obtain ⟨j,hj1,hj2⟩:=(Finset.mem_filter.mp hqD).2
      have hjr :j.val< r 1:=by
       have:j.val<Q9 D 1:=j.isLt
       omega
      rw[hj1,hj2, ← cf8 _ hjr, ← hco _ hjr,hS.Qfi hp hs2 hjr,if_neg (by omega)]
    · by_contra hne
      have hq0:q.1.val<Q9 D 0:=q.1.isLt
      rcases hS.Q8j hn3 hne with ⟨a1, -⟩ | ⟨b1, -⟩
      · exact hlt a1
      · omega
   show Q3x D C (Q0 (Q9 D) 0+q.1.val) (Q0 (Q9 D) 0+q.2.val)
       (Q0 (Q9 D) 2+v.val) % p^Qc D ⟨Qa h2,v⟩=0
   rw[cf5,e0',Nat.zero_add,Nat.zero_add, ← f2,hz,Nat.zero_mod]
lemma Qfz {p m:ℕ} (hp0:0<p) {D:Qg m} (h2:2<D.1.val)
    {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)} {co:ℕ→ℕ}
    {C C':Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    (hC:Qd9 p hp0 D h2 B co C) (hC':Qd9 p hp0 D h2 B co C')
    (h1:Q3d D h2 C=Q3d D h2 C') (h3:Q6o hp0 D h2 C=Q6o hp0 D h2 C'):
    C=C':=by
 have e0:Q0 (Q9 D) 0=0:=rfl
 have e01:Q0 (Q9 D) 1=Q0 (Q9 D) 0+Q9 D 0:=Q19 _ 0
 have e12:Q0 (Q9 D) 2=Q0 (Q9 D) 1+Q9 D 1:=Q19 _ 1
 have e23:Q0 (Q9 D) 3=Q0 (Q9 D) 2+Q9 D 2:=Q19 _ 2
 have K1:∀ j0 k0 v (hj:j0<Q9 D 0) (hk:k0<Q9 D 0) (hv:v<Q9 D 1),
     Q3x D C (Q0 (Q9 D) 0+j0) (Q0 (Q9 D) 0+k0) (Q0 (Q9 D) 1+v)=
       Q3x D C' (Q0 (Q9 D) 0+j0) (Q0 (Q9 D) 0+k0) (Q0 (Q9 D) 1+v):=
   fun j0 k0 v hj hk hv=>congrFun (congrFun (congrFun (congrArg Prod.fst h1)
     (⟨j0,hj⟩:Fin (Q4 D (Q1 h2)))) (⟨k0,hk⟩:Fin (Q4 D (Q1 h2))))
     (⟨v,hv⟩:Fin (Q4 D (Q3 h2)))
 have K2:∀ j0 k0 v (hj:j0<Q9 D 1) (hk:k0<Q9 D 0) (hv:v<Q9 D 2),
     Q3x D C (Q0 (Q9 D) 1+j0) (Q0 (Q9 D) 0+k0) (Q0 (Q9 D) 2+v)=
       Q3x D C' (Q0 (Q9 D) 1+j0) (Q0 (Q9 D) 0+k0) (Q0 (Q9 D) 2+v):=
   fun j0 k0 v hj hk hv=>congrFun (congrFun (congrFun (congrArg Prod.snd h1)
     (⟨j0,hj⟩:Fin (Q4 D (Q3 h2)))) (⟨k0,hk⟩:Fin (Q4 D (Q1 h2))))
     (⟨v,hv⟩:Fin (Q4 D (Qa h2)))
 have K3 :∀ j0 k0 v (hj:j0<Q9 D 0) (hk:k0<Q9 D 0) (hv:v<Q9 D 2),
     Q3x D C (Q0 (Q9 D) 0+j0) (Q0 (Q9 D) 0+k0) (Q0 (Q9 D) 2+v) %
         p^Q6x D (Q0 (Q9 D) 2+v)=
       Q3x D C' (Q0 (Q9 D) 0+j0) (Q0 (Q9 D) 0+k0) (Q0 (Q9 D) 2+v) %
         p^Q6x D (Q0 (Q9 D) 2+v):=
   fun j0 k0 v hj hk hv=>congrArg Fin.val (congrFun (congrFun h3
     ((⟨j0,hj⟩:Fin (Q4 D (Q1 h2))),(⟨k0,hk⟩:Fin (Q4 D (Q1 h2)))))
     (⟨v,hv⟩:Fin (Q4 D (Qa h2))))
 have key:∀ i j k,Q3x D C i j k=Q3x D C' i j k:=by
  intro i j k
  by_cases h0:Q3x D C i j k=0∧Q3x D C' i j k=0
  · rw[h0.1,h0.2]
  have hz:(i<j∧j<Q0 (Q9 D) 1∧Q0 (Q9 D) 1≤k∧k<Q0 (Q9 D) 3)∨
      (Q0 (Q9 D) 1≤ i∧i<Q0 (Q9 D) 2∧j<Q0 (Q9 D) 1∧
        Q0 (Q9 D) 2≤k∧k<Q0 (Q9 D) 3):=by
   rcases not_and_or.mp h0 with h | h
   · exact hC.zero i j k h
   · exact hC'.zero i j k h
  rcases hz with ⟨a1,a2,a3,a4⟩ | ⟨b1,b2,b3,b4,b5⟩
  · by_cases hk:k<Q0 (Q9 D) 2
    · have:=K1 i j (k - Q0 (Q9 D) 1) (by omega) (by omega) (by omega)
      rwa[e0,Nat.zero_add,Nat.zero_add,Nat.add_sub_of_le a3]at this
    · have:=K3 i j (k - Q0 (Q9 D) 2) (by omega) (by omega) (by omega)
      rw [e0,Nat.zero_add,Nat.zero_add,
        Nat.add_sub_of_le (show Q0 (Q9 D) 2≤k by omega)]at this
      rwa[Nat.mod_eq_of_lt (hC.bd i j k),Nat.mod_eq_of_lt (hC'.bd i j k)]at this
  · have:=K2 (i - Q0 (Q9 D) 1) j (k - Q0 (Q9 D) 2) (by omega) (by omega) (by omega)
    rwa[e0,Nat.zero_add,Nat.add_sub_of_le b1,Nat.add_sub_of_le b4]at this
 funext i j k
 apply Fin.ext
 rw[← Qjo D C i j k, ← Qjo D C' i j k]
 exact key _ _ _
lemma Qa4 {p m:ℕ} (hp:p.Prime) (T:Set FiniteGrp.{0})
    (D:Qg m) (h2:2<D.1.val) (h3:D.1.val=3)
    (B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)):
    (Qw hp T D B).ncard≤
      (∑ β ∈(ZQ (min (∑ v,Qc D ⟨Q3 h2,v⟩)
          (∑ v,Qc D ⟨Qa h2,v⟩)+1)).filter
          (fun β=> (∑ v,Qc D ⟨Qa h2,v⟩)≤D.2.1.val*β),
        p ^(D.2.1.val*(β *(Q4 D (Q3 h2)+(∑ v,Qc D ⟨Qa h2,v⟩)+1 - β)))*
          p ^ (((Q4 D (Q1 h2)).choose 2 - Q4 D (Q3 h2))*
              (∑ v,Qc D ⟨Q3 h2,v⟩) - (Q4 D (Q1 h2) - D.2.1.val).choose 2*β))*
        p ^(((Q4 D (Q1 h2)).choose 2 - Q4 D (Q3 h2))*
          ∑ v,Qc D ⟨Qa h2,v⟩):=by
  rcases (Qw hp T D B).eq_empty_or_nonempty with hE | ⟨C0,hC0⟩
  · rw[hE,Set.ncard_empty]
    exact Nat.zero_le _
  obtain ⟨G0, -,u0,d0,X0,r0,hS0,hnm0,hs0,hsum0,e0⟩:=hC0
  obtain ⟨c1,c2,c3, -, -, -,c7,c8⟩:=hS0.Q6d hp hnm0 hs0 hsum0 e0
  have hn0:d0.n=Q0 r0 D.1.val:=by rw[← c1]; exact hS0.Q2j.symm
  have hr00:r0 0=Q9 D 0:= c3 0 (by rw[c1]; omega)
  have hr01:r0 1=Q9 D 1:= c3 1 (by rw[c1]; omega)
  have hsr0:=(hS0.Qhg hn0 (by omega) hS0.Qbf).1
  have hgood:∀ C∈Qw hp T D B,Qd9 p hp.pos D h2 B (Qn d0 r0) C:=by
   rintro C ⟨G, -,u,d,X,r,hS,hnm,hs2,hsum,e⟩
   obtain ⟨g1,g2,g3, -, -, -,g7, -⟩:=hS.Q6d hp hnm hs2 hsum e
   refine hS.Qkd hp hnm hs2 hsum e h2 h3 _
     (Qau hS hS0 hs2 (g2.trans c2.symm) ?_ ?_)
   · rw[g3 1 (by rw[g1]; omega),hr01]
   · intro k hk
     rw[g7 k hk,c7 k (by rw[c2, ← g2]; exact hk)]
  have hjr :∀ j:Fin (Q4 D (Q3 h2)),j.val< r0 1:= fun j=>by
    have:j.val<Q9 D 1:=j.isLt
    omega
  have hDp:∀ q∈Q2h D h2 (Q13 D) (Qn d0 r0),q.1<q.2∧(q.1:ℕ)<D.2.1.val:=by
   intro q hq
   obtain ⟨j,hj1,hj2⟩:=(Finset.mem_filter.mp hq).2
   rw[← c8 _ (hjr j)]at hj1
   refine ⟨?_,?_⟩
   · show q.1.val<q.2.val
     rw[hj1,hj2]
     exact hS0.Q6q hs0 (hjr j)
   · rw[hj1, ← c2]
     have:=hS0.Qat hs0 j.val (hjr j)
     omega
  have hb1:∀ j:Fin (Q4 D (Q3 h2)),Q13 D j.val<Q4 D (Q1 h2):=by
   intro j
   show Q13 D j.val<Q9 D 0
   rw[← c8 _ (hjr j), ← hr00]
   have:=hS0.Qat hs0 j.val (hjr j)
   omega
  have hb2:∀ j:Fin (Q4 D (Q3 h2)),Qn d0 r0 j.val<Q4 D (Q1 h2):=by
   intro j
   show Qn d0 r0 j.val<Q9 D 0
   rw[← hr00]
   have:=hS0.Q3n hs0 j.val (hjr j)
   omega
  obtain ⟨F,hF⟩:∃ F:Fin (Q4 D (Q3 h2))→
      Fin (Q4 D (Q1 h2))×Fin (Q4 D (Q1 h2)),
      ∀ j,(F j).1.val=Q13 D j.val∧(F j).2.val=Qn d0 r0 j.val:=
    ⟨fun j=> (⟨_,hb1 j⟩,⟨_,hb2 j⟩),fun j=> ⟨rfl,rfl⟩⟩
  have hFinj:Function.Injective F:=by
   intro j j' hjj
   have e1:Q13 D j.val=Q13 D j'.val:=by rw[← (hF j).1, ← (hF j').1,hjj]
   have e2:Qn d0 r0 j.val=Qn d0 r0 j'.val:=by rw[← (hF j).2, ← (hF j').2,hjj]
   rw[← c8 _ (hjr j), ← c8 _ (hjr j')]at e1
   exact Fin.ext (hS0.Qa7 hs0 (hjr j) (hjr j') e1 e2)
  have himg:Q2h D h2 (Q13 D) (Qn d0 r0)=Finset.univ.image F:=by
   ext q
   simp only[Q2h,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
   constructor
   · rintro ⟨j,h1,h2'⟩
     exact ⟨j,Prod.ext (Fin.ext ((hF j).1.trans h1.symm)) (Fin.ext ((hF j).2.trans h2'.symm))⟩
   · rintro ⟨j,rfl⟩
     exact ⟨j,(hF j).1,(hF j).2⟩
  have hDcard:(Q2h D h2 (Q13 D) (Qn d0 r0)).card=Q4 D (Q3 h2):=by
   rw[himg,Finset.card_image_of_injective _ hFinj,Finset.card_univ,Fintype.card_fin]
  have hLead:=Qed (p:=p) (c:=D.1.val) (r :=Q4 D) (a:=Qc D) hp h2
    (Q18 D B (Q1 h2)) (Q18 D B (Q3 h2)) (Q18 D B (Qa h2)) (s:=D.2.1.val)
    (by show D.2.1.val≤Q9 D 0; rw[← c2, ← hr00]; exact hsr0)
    (Q2h D h2 (Q13 D) (Qn d0 r0)) hDp (Q9w D h2 (Q13 D) (Qn d0 r0))
    (Q8m p D h2 (Q18 D B (Q1 h2)) (Q18 D B (Q3 h2)) (Q18 D B (Qa h2))
      (Q2h D h2 (Q13 D) (Qn d0 r0)) (Q9w D h2 (Q13 D) (Qn d0 r0))) (fun x hx =>hx.1)
  rw[hDcard]at hLead
  have hDeep:=Q74 (Γ:=Qdf p D h2)
    (Q7n (p:=p) (fun v:Fin (Q4 D (Qa h2))=>Qc D ⟨Qa h2,v⟩))
    (Q2h D h2 (Q13 D) (Qn d0 r0)) (fun q hq=> (hDp q hq).1)
    (fun _ _=> ⟨0,pow_pos hp.pos _⟩)
  rw[hDcard]at hDeep
  have hΛfin:(Q8m p D h2 (Q18 D B (Q1 h2)) (Q18 D B (Q3 h2)) (Q18 D B (Qa h2))
      (Q2h D h2 (Q13 D) (Qn d0 r0)) (Q9w D h2 (Q13 D) (Qn d0 r0))).Finite:=by
   refine (Set.finite_range (fun y:(Fin (Q4 D (Q1 h2))→Fin (Q4 D (Q1 h2))→
       (v:Fin (Q4 D (Q3 h2)))→Fin (p^Qc D ⟨Q3 h2,v⟩))×
       (Fin (Q4 D (Q3 h2))→Fin (Q4 D (Q1 h2))→
         (v:Fin (Q4 D (Qa h2)))→Fin (p^Qc D ⟨Qa h2,v⟩))=>
       ((fun j k v=> (y.1 j k v).val,fun j k v=> (y.2 j k v).val):Q5e D h2))).subset ?_
   rintro x ⟨-,hx1,hx2⟩
   exact ⟨(fun j k v=> ⟨x.1 j k v,hx1 j k v⟩,fun j k v=> ⟨x.2 j k v,hx2 j k v⟩),rfl⟩
  have hinj:Set.InjOn (fun C=> (Q3d D h2 C,Q6o hp.pos D h2 C))
      (Qw hp T D B):=by
    intro C hC C' hC' he
    exact Qfz hp.pos h2 (hgood C hC) (hgood C' hC') (congrArg Prod.fst he)
      (congrArg Prod.snd he)
  have hmaps:∀ C∈Qw hp T D B,(fun C=> (Q3d D h2 C,Q6o hp.pos D h2 C)) C∈
      (Q4s D h2 (Qn d0 r0) '' Q8m p D h2 (Q18 D B (Q1 h2)) (Q18 D B (Q3 h2))
        (Q18 D B (Qa h2)) (Q2h D h2 (Q13 D) (Qn d0 r0))
        (Q9w D h2 (Q13 D) (Qn d0 r0)))×ˢ
        Q5y p hp.pos D h2 (Q2h D h2 (Q13 D) (Qn d0 r0)):=by
    intro C hC
    obtain ⟨x,hx,hxe⟩:=(hgood C hC).lead
    show (Q3d D h2 C,Q6o hp.pos D h2 C)∈_
    exact Set.mk_mem_prod ⟨x,hx,hxe.symm⟩ (hgood C hC).deep
  calc (Qw hp T D B).ncard
      ≤ ((Q4s D h2 (Qn d0 r0) '' Q8m p D h2 (Q18 D B (Q1 h2)) (Q18 D B (Q3 h2))
          (Q18 D B (Qa h2)) (Q2h D h2 (Q13 D) (Qn d0 r0))
          (Q9w D h2 (Q13 D) (Qn d0 r0)))×ˢ
          Q5y p hp.pos D h2 (Q2h D h2 (Q13 D) (Qn d0 r0))).ncard:=
        Set.ncard_le_ncard_of_injOn _ hmaps hinj
          ((hΛfin.image (Q4s D h2 (Qn d0 r0))).prod (Set.toFinite _))
    _=(Q4s D h2 (Qn d0 r0) '' Q8m p D h2 (Q18 D B (Q1 h2)) (Q18 D B (Q3 h2))
          (Q18 D B (Qa h2)) (Q2h D h2 (Q13 D) (Qn d0 r0))
          (Q9w D h2 (Q13 D) (Qn d0 r0))).ncard*
          (Q5y p hp.pos D h2 (Q2h D h2 (Q13 D) (Qn d0 r0))).ncard:=Set.ncard_prod
    _ ≤ (Q8m p D h2 (Q18 D B (Q1 h2)) (Q18 D B (Q3 h2))
          (Q18 D B (Qa h2)) (Q2h D h2 (Q13 D) (Qn d0 r0))
          (Q9w D h2 (Q13 D) (Qn d0 r0))).ncard*
          (Q5y p hp.pos D h2 (Q2h D h2 (Q13 D) (Qn d0 r0))).ncard:=
        Nat.mul_le_mul_right _ (Set.ncard_image_le hΛfin)
    _≤_:=Nat.mul_le_mul hLead hDeep
end LfCBCount
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section LfsTransport
variable {G:Type u} [Group G] {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2] [CommGroup L3]
end LfsTransport
section LfsIdent
variable {G:Type u} [Group G] {p c:ℕ} {r :Fin c→ℕ} {a:Q6 c r→ℕ}
  {g:Q6 c r→G} {S:Q7 p a g} {h2:2<c}
  {b0:Fin (r (Q1 h2))→Fin (r (Q1 h2))→ℕ}
  {b1:Fin (r (Q3 h2))→Fin (r (Q3 h2))→ℕ} {b2:Fin (r (Qa h2))→Fin (r (Qa h2))→ℕ}
end LfsIdent
section LfsLeadCount
variable {p c:ℕ} {r :Fin c→ℕ} {a:Q6 c r→ℕ}
end LfsLeadCount
section LfsGroup
variable {G:Type u} [Group G] {p:ℕ} {u:ℕ→G} {d:Q5} {X:Fin d.n→G}
  {r :ℕ→ℕ}
end LfsGroup
section LfsCount
end LfsCount
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
section CNT3MainDefs
def Q5d {m:ℕ} (r1 r2 s m2 m3:ℕ) (D:Qg m):Prop:=
  ∃ h2:2<D.1.val,D.1.val=3∧D.2.1.val=s∧Q4 D (Q1 h2)=r1∧
    Q4 D (Q3 h2)=r2∧(∑ v,Qc D ⟨Q3 h2,v⟩)=m2 - m3∧
    (∑ v,Qc D ⟨Qa h2,v⟩)=m3
def Q4r (s m2 m3:ℕ):Finset ℕ:=
  (ZQ (min (m2 - m3) m3+1)).filter (fun β=>m3≤ s*β)
def Q35 (r1 r2 s m2 m3 b2:ℕ):ℕ:=
  2 ^ (s*(b2*(r2+m3+1 - b2)))*
    2 ^((r1.choose 2 - r2)*(m2 - m3) - (r1 - s).choose 2*b2)*
      2^((r1.choose 2 - r2)*m3)
noncomputable def Q3m (r1 r2 s m2 m3 b2:ℕ):ℕ:=
  Alt2.N2 r1 r2 s*2^((r1.choose 2 - r2)*(m2 - m3 - r2))*2^((r1.choose 2 - r2)*m3)*
    2^(s*(b2*(r2+m3+1 - b2)))
def Qlf:Prop:=
  ∀ m r1 r2 s lam m2 m3 r3:ℕ,∀ G∈Q1g m r1 r2 s lam m2 m3 r3,
    ∃ D:Qy 2 m,Q1t Nat.prime_two m G D ∧Q5d r1 r2 s m2 m3 D.1∧
      Q2y (Qc D.1)≤Q46 r1 r2 r3 lam m2 m3
def Qnd:Prop:=
  ∃ C0:ℝ,∀ m:ℕ,1≤ m→
    (Fintype.card (Qg m):ℝ)≤(2:ℝ)^(C0*m*((Nat.log 2 m:ℝ)+1))
end CNT3MainDefs
section CNT3MainArith
lemma Qe8 {s m2 m3 β:ℕ}:
    β∈Q4r s m2 m3↔β≤ min (m2 - m3) m3∧m3≤ s*β:=by
 unfold Q4r
 rw[Finset.mem_filter,Finset.mem_range,Nat.lt_add_one_iff]
lemma Qg0 (s m2 m3:ℕ):(Q4r s m2 m3).card≤ min (m2 - m3) m3+1:=
  (Finset.card_filter_le _ _).trans (Finset.card_range _).le
lemma Q6m (n:ℕ):(n+1).choose 2=n+n.choose 2:=by
 have h:=Nat.choose_succ_succ' n 1
 rw[Nat.choose_one_right]at h
 exact h
lemma Qaa (a b:ℕ):a.choose 2+b.choose 2≤(a+b).choose 2:=by
 induction b with
 | zero=>rw[Nat.add_zero,Nat.choose_eq_zero_of_lt (by norm_num:0<2),Nat.add_zero]
 | succ b ih=>
   rw[← Nat.add_assoc,Q6m (a+b),Q6m b]
   omega
lemma Q4d (e:ℕ):((2^e:ℕ):ℝ)=(2:ℝ)^(e:ℝ):=by
 rw[Real.rpow_natCast]
 norm_cast
lemma Qhj {r1 r2 s m2 m3 β:ℕ} (hsr :s≤ r1) (hr2:r2≤ s.choose 2)
    (h32:m3≤ m2) (hb2:β≤ m2 - m3) (hb3:β≤ m3):
    (Q35 r1 r2 s m2 m3 β:ℝ)=(2:ℝ)^(Q9p r1 r2 s m2 m3 β):=by
 have hK:(r1 - s).choose 2+s.choose 2≤ r1.choose 2:=by
  have:=Qaa (r1 - s) s
  rwa[Nat.sub_add_cancel hsr]at this
 have hC:r2≤ r1.choose 2:=by omega
 have hKb:(r1 - s).choose 2*β≤(r1.choose 2 - r2)*(m2 - m3):=
   Nat.mul_le_mul (by omega) hb2
 have hb1:β≤ r2+m3+1:=by omega
 have e :Q35 r1 r2 s m2 m3 β=2^(s*(β *(r2+m3+1 - β))+
     ((r1.choose 2 - r2)*(m2 - m3) - (r1 - s).choose 2*β)+
       (r1.choose 2 - r2)*m3):=by
  unfold Q35
  rw[pow_add,pow_add]
 rw[e,Q4d]
 congr 1
 unfold Q9p
 push_cast[Nat.cast_sub hKb,Nat.cast_sub hC,Nat.cast_sub h32,Nat.cast_sub hb1]
 ring
lemma Qje {r1 r2 s m2 m3 β:ℕ} (hsr :s≤ r1) (hr2:r2≤ s.choose 2)
    (h32:m3≤ m2) (hr2s:r2≤ m2 - m3) (hb3:β≤ m3):
    (Q3m r1 r2 s m2 m3 β:ℝ)≤(2:ℝ)^(Q8i r1 r2 s m2 m3 β):=by
 have hC:r2≤ r1.choose 2:=le_trans hr2 (Nat.choose_le_choose 2 hsr)
 have hb1:β≤ r2+m3+1:=by omega
 have e:Q3m r1 r2 s m2 m3 β=Alt2.N2 r1 r2 s*2^((r1.choose 2 - r2)*(m2 - m3 - r2)+
     (r1.choose 2 - r2)*m3+s*(β *(r2+m3+1 - β))):=by
  unfold Q3m
  rw[pow_add,pow_add]
  ring
 rw[e]
 rcases Nat.eq_zero_or_pos (Alt2.N2 r1 r2 s) with h0 | hpos
 · rw[h0,zero_mul,Nat.cast_zero]
   positivity
 · rw[Nat.cast_mul,Q4d]
   have hN:(Alt2.N2 r1 r2 s:ℝ)=(2:ℝ)^(Alt2.Qiq r1 r2 s):=by
    unfold Alt2.Qiq
    rw[Real.rpow_logb (by norm_num) (by norm_num) (by exact_mod_cast hpos)]
   rw[hN, ← Real.rpow_add (by norm_num)]
   apply le_of_eq
   congr 1
   unfold Q8i
   push_cast[Nat.cast_sub hC,Nat.cast_sub hr2s,Nat.cast_sub h32,Nat.cast_sub hb1]
   ring
lemma Qeb {I:Finset ℕ} {n:ℕ} (hI:I.card≤n+1) (g e:ℕ→ℝ) (b:ℕ)
    (hg:∀ β∈I,g β≤(2:ℝ)^(e β)) (hb:∀ β∈I,e β≤e b):
    ∑ β∈I,g β≤((n:ℝ)+1)*(2:ℝ)^(e b):=by
 calc ∑ β∈I,g β≤∑ _β∈I,(2:ℝ)^(e b):=Finset.sum_le_sum fun β h=>
       (hg β h).trans (Real.rpow_le_rpow_of_exponent_le (by norm_num) (hb β h))
   _=(I.card:ℝ)*(2:ℝ)^(e b):=by rw[Finset.sum_const,nsmul_eq_mul]
   _ ≤ ((n:ℝ)+1)*(2:ℝ)^(e b):=by
       gcongr
       exact_mod_cast hI
lemma Ql5 {N m n PW:ℕ} {C0 E:ℝ}
    (hD:∀ m:ℕ,1≤ m→
      (Fintype.card (Qg m):ℝ)≤(2:ℝ)^(C0*m*((Nat.log 2 m:ℝ)+1)))
    (hm:1≤ m) (hn:n≤ m) (hN:1≤N)
    (h:(N:ℝ)≤(Fintype.card (Qg m):ℝ)*2^PW*(((n:ℝ)+1)*(2:ℝ)^E)):
    Real.logb 2 (N:ℝ)≤(C0+1)*(m:ℝ)*((Nat.log 2 m:ℝ)+1)+(PW:ℝ)+E:=by
 have h1:=hD m hm
 have h2n:n+1≤2^(Nat.log 2 m+1):=by
  have h':m<2^(Nat.log 2 m+1):=Nat.lt_pow_succ_log_self (by norm_num) m
  omega
 have hL:(n:ℝ)+1≤(2:ℝ)^((Nat.log 2 m:ℝ)+1):=by
  have h':((n+1:ℕ):ℝ)≤((2^(Nat.log 2 m+1):ℕ):ℝ):=by exact_mod_cast h2n
  rw[Q4d]at h'
  push_cast at h'
  exact h'
 have hPWr :(2:ℝ)^PW=(2:ℝ)^(PW:ℝ):=(Real.rpow_natCast 2 PW).symm
 have hNpos:(0:ℝ)<N:=by exact_mod_cast hN
 have hm':(1:ℝ)≤ m:=by exact_mod_cast hm
 have hL0:(0:ℝ)≤(Nat.log 2 m:ℝ):=Nat.cast_nonneg _
 rw[Real.logb_le_iff_le_rpow (by norm_num) hNpos]
 calc (N :ℝ)≤(Fintype.card (Qg m):ℝ)*2^PW*(((n:ℝ)+1)*(2:ℝ)^E):=h
   _ ≤ (2 :ℝ)^(C0*m*((Nat.log 2 m:ℝ)+1))*(2:ℝ)^(PW:ℝ)*
         ((2:ℝ)^((Nat.log 2 m:ℝ)+1)*(2:ℝ)^E):=by
       rw[hPWr]
       gcongr
   _ = (2 :ℝ)^(C0*m*((Nat.log 2 m:ℝ)+1)+(PW:ℝ)+
         (((Nat.log 2 m:ℝ)+1)+E)):=by
       rw [← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num),
         ← Real.rpow_add (by norm_num)]
   _ ≤ (2:ℝ)^((C0+1)*(m:ℝ)*((Nat.log 2 m:ℝ)+1)+(PW:ℝ)+E):=by
       apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
       nlinarith[mul_nonneg (sub_nonneg.mpr hm') hL0]
lemma Qna:Qnd:=by
 refine ⟨7,fun m hm=>?_⟩
 have h1:=Qc8 m hm
 have hlt:m<2^(Nat.log 2 m+1):=Nat.lt_pow_succ_log_self (by norm_num) m
 have h2:(m+1)^(5*m+2)≤2^((Nat.log 2 m+1)*(5*m+2)):=by
  rw[pow_mul]
  exact Nat.pow_le_pow_left (by omega) _
 have h3:(Nat.log 2 m+1)*(5*m+2)≤7*m*(Nat.log 2 m+1):=by
  rw[Nat.mul_comm (Nat.log 2 m+1)]
  exact Nat.mul_le_mul_right _ (by omega)
 have h4:Fintype.card (Qg m)≤2^(7*m*(Nat.log 2 m+1)):=
   h1.trans (h2.trans (Nat.pow_le_pow_right (by norm_num) h3))
 calc (Fintype.card (Qg m):ℝ)≤((2^(7*m*(Nat.log 2 m+1)):ℕ):ℝ):=by
       exact_mod_cast h4
   _ = (2:ℝ)^((7:ℝ)*m*((Nat.log 2 m:ℝ)+1)):=by
       rw[Q4d]
       congr 1
       norm_num
end CNT3MainArith
section CNT3MainCount
variable {m r1 r2 s lam m2 m3 r3:ℕ}
lemma Qh6 (D:Qg m) (hL:Q5d r1 r2 s m2 m3 D)
    (B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (2^m)):
    (Qw Nat.prime_two (Q1g m r1 r2 s lam m2 m3 r3) D B).ncard≤
      ∑ β∈Q4r s m2 m3,Q35 r1 r2 s m2 m3 β:=by
 obtain ⟨h2,h3,hs,hr1,hr2,hs2,hs3⟩:=hL
 have h:=Qa4 Nat.prime_two (Q1g m r1 r2 s lam m2 m3 r3) D h2 h3 B
 rw[hs2,hs3,hr1,hr2]at h
 refine h.trans (le_of_eq ?_)
 rw[hs,Finset.sum_mul]
 rfl
lemma Qfs (hPW:Qlf) (hne:(Q1g m r1 r2 s lam m2 m3 r3).Nonempty):
    1 ≤ m∧s≤ r1∧r2≤ s.choose 2∧m3≤ m2∧r2≤ m2 - m3∧
      (Q4r s m2 m3).Nonempty∧1≤(Q2d m r1 r2 s lam m2 m3 r3).ncard:=by
 obtain ⟨G,hG⟩:=hne
 have hm:=Qcl hG
 obtain ⟨c1,c2, -,c4, -, -⟩:=Q5n hG
 have:Fact (Nat.Prime 2):=⟨Nat.prime_two⟩
 obtain ⟨-, -, -, -, -, -, -,hm2,hm3, -⟩:=(Q43 G).mp hG
 have h32:m3≤ m2:=by
  have hle:ZB (lcs G 2)≤ZB (lcs G 1):=
    Subgroup.card_le_of_le (Qd (by norm_num))
  rw[hm2,hm3]at hle
  exact Q4c (p:=2) (le_refl 2) hle
 obtain ⟨Df,hcode,hL, -⟩:=hPW m r1 r2 s lam m2 m3 r3 G hG
 have hr2s2:r2≤ m2 - m3:=by
  obtain ⟨h2, -, -, -,hr2,hs2, -⟩:=hL
  have hsum:∑ _v:Fin (Q4 Df.1 (Q3 h2)),1≤∑ v,Qc Df.1 ⟨Q3 h2,v⟩:=
    Finset.sum_le_sum fun v _=>Qhn Df.1 _
  have hcard:∑ _v:Fin (Q4 Df.1 (Q3 h2)),(1:ℕ)=Q4 Df.1 (Q3 h2):=by
   rw[Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,mul_one]
  omega
 have hC:Df.2.2∈Qw Nat.prime_two (Q1g m r1 r2 s lam m2 m3 r3) Df.1 Df.2.1:=
   ⟨G,hG,hcode⟩
 have hA:=Qh6 (lam:=lam) (r3:=r3) Df.1 hL Df.2.1
 have hpos:0<
     (Qw Nat.prime_two (Q1g m r1 r2 s lam m2 m3 r3) Df.1 Df.2.1).ncard:=
   (Set.ncard_pos (Set.toFinite _)).mpr ⟨Df.2.2,hC⟩
 have hadm:(Q4r s m2 m3).Nonempty:=by
  rcases Finset.eq_empty_or_nonempty (Q4r s m2 m3) with h | h
  · rw[h,Finset.sum_empty]at hA
    omega
  · exact h
 have hcl:1≤(Q2d m r1 r2 s lam m2 m3 r3).ncard:=
   (Set.ncard_pos Qcy).mpr ⟨_,G,hG,rfl⟩
 exact ⟨by omega,c2,c4,h32,hr2s2,hadm,hcl⟩
lemma Qii (hPW:Qlf) (M:ℝ) (hM0:0≤M)
    (hM :∀ D:Qg m,Q5d r1 r2 s m2 m3 D→
      ∀ B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (2^m),
        ((Qw Nat.prime_two (Q1g m r1 r2 s lam m2 m3 r3) D B).ncard:ℝ)≤M):
    ((Q2d m r1 r2 s lam m2 m3 r3).ncard:ℝ)≤
      (Fintype.card (Qg m):ℝ)*2^Q46 r1 r2 r3 lam m2 m3*M:=by
 classical
 let I:Finset (Qg m):=Finset.univ.filter (fun D =>Q5d r1 r2 s m2 m3 D ∧
   Q2y (Qc D)≤Q46 r1 r2 r3 lam m2 m3)
 have hI:∀ G∈Q1g m r1 r2 s lam m2 m3 r3,∃ D:Qy 2 m,
     Q1t Nat.prime_two m G D ∧D.1∈I:=by
  intro G hG
  obtain ⟨D,hc,hL,hpw⟩:=hPW m r1 r2 s lam m2 m3 r3 G hG
  exact ⟨D,hc,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hL,hpw⟩⟩
 have h:=Q72 Nat.prime_two (Q1g m r1 r2 s lam m2 m3 r3) I hI
   (fun _=> ⌊M⌋₊) (fun D hD B _=>Nat.le_floor (hM D (Finset.mem_filter.mp hD).2.1 B))
 have h2 : ∑ D∈I,2^Q2y (Qc D)* ⌊M⌋₊ ≤
     Fintype.card (Qg m)*(2^Q46 r1 r2 r3 lam m2 m3* ⌊M⌋₊):=by
  calc ∑ D ∈I,2^Q2y (Qc D)* ⌊M⌋₊
      ≤ ∑ _D∈I,2^Q46 r1 r2 r3 lam m2 m3* ⌊M⌋₊ :=
        Finset.sum_le_sum fun D hD =>Nat.mul_le_mul_right _
          (Nat.pow_le_pow_right (by norm_num) (Finset.mem_filter.mp hD).2.2)
    _ = I.card*(2^Q46 r1 r2 r3 lam m2 m3* ⌊M⌋₊):=by
        rw[Finset.sum_const,smul_eq_mul]
    _≤_:=Nat.mul_le_mul_right _ (Finset.card_le_univ I)
 have h3:(Q2d m r1 r2 s lam m2 m3 r3).ncard≤
     Fintype.card (Qg m)*(2^Q46 r1 r2 r3 lam m2 m3* ⌊M⌋₊):=by
  unfold Q2d
  exact h.trans h2
 calc ((Q2d m r1 r2 s lam m2 m3 r3).ncard:ℝ)
     ≤ ((Fintype.card (Qg m)*(2^Q46 r1 r2 r3 lam m2 m3* ⌊M⌋₊):ℕ):ℝ):=by
       exact_mod_cast h3
   _ = (Fintype.card (Qg m):ℝ)*2^Q46 r1 r2 r3 lam m2 m3*(⌊M⌋₊ :ℝ):=by
       push_cast
       ring
   _ ≤ (Fintype.card (Qg m):ℝ)*2^Q46 r1 r2 r3 lam m2 m3*M:=by
       gcongr
       exact Nat.floor_le hM0
end CNT3MainCount
section CNT3MainThm
end CNT3MainThm
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
universe u
section C3PWArith
lemma Qdu {c:ℕ} {r :Fin c→ℕ} (a:Q6 c r→ℕ) (hc:c=3)
    (R0 R1 R2 S0 S1 S2:ℕ)
    (hr :∀ i:Fin c,r i=if i.val=0 then R0 else if i.val=1 then R1 else R2)
    (hs:∀ i:Fin c,sL a i=if i.val=0 then S0 else if i.val=1 then S1 else S2):
    Q2y a=(R0*(S1+S2)+(R0 - 1)*(S0 - R0))+(R1*S2+(R1 - 1)*(S1 - R1))+
      (R2 - 1)*(S2 - R2):=by
  subst hc
  have hr0:r 0=R0:=by simp +decide [hr]
  have hr1:r 1=R1:=by simp +decide [hr]
  have hr2:r 2=R2:=by simp +decide [hr]
  have hs0:sL a 0=S0:=by simp +decide [hs]
  have hs1:sL a 1=S1:=by simp +decide [hs]
  have hs2:sL a 2=S2:=by simp +decide [hs]
  have hm0:Q59 a 0=S1+S2:=by
   unfold Q59
   rw[Finset.sum_filter,Fin.sum_univ_three]
   simp +decide [hs1,hs2]
  have hm1:Q59 a 1=S2:=by
   unfold Q59
   rw[Finset.sum_filter,Fin.sum_univ_three]
   simp +decide [hs2]
  have hm2:Q59 a 2=0:=by
   unfold Q59
   rw[Finset.sum_filter,Fin.sum_univ_three]
   simp +decide
  unfold Q2y
  simp only[Fin.sum_univ_three,hm0,hm1,hm2,hs0,hs1,hs2,hr0,hr1,hr2]
  ring
end C3PWArith
section C3Layer
lemma Q5c {H:Type u} [Group H] (i:ℕ):
    ZB (Q1r H i)*ZB (lcs H (i+1))=ZB (lcs H i):=by
 have h1:=Subgroup.card_mul_index ((lcs H (i+1)).subgroupOf (lcs H i))
 have h2:=Nat.card_congr (Subgroup.subgroupOfEquivOfLe
   (Qd (Nat.le_succ i):lcs H (i+1)≤lcs H i)).toEquiv
 rw[h2]at h1
 rw[mul_comm]
 exact h1
lemma Q53 {p m:ℕ} (hp:p.Prime) {H:Type u} [Group H] [Finite H]
    {D:Qg m} {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    {C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    (hc:Q1t hp m H (⟨D,(B,C)⟩:Qy p m)) (i:Fin D.1.val)
    (hlast:i.val+1<D.1.val∨lcs H (i.val+1)=⊥):
    ZB (Q1r H i.val)=p^sL (Qc D) i:=by
 obtain ⟨u,d,X,r,hS,hnm,hs2,hsum,e⟩:=hc
 obtain ⟨c1, -,c3,c4, -⟩:=hS.Q6d hp hnm hs2 hsum e
 have hn:d.n=Q0 r hS.nL:=hS.Q2j.symm
 have hi:i.val<hS.nL:=by rw[c1]; exact i.isLt
 have hl:i.val+1<hS.nL∨lcs H (i.val+1)=⊥:=by rw[c1]; exact hlast
 have h:=(hS.toQ7 hp hn).Qc2 hp.pos ⟨i.val,hi⟩ hl
 refine h.trans ?_
 congr 1
 show ∑ v:Fin (r i.val),d.a (hS.Q8 hn ⟨⟨i.val,hi⟩,v⟩)=
   ∑ v:Fin (Q9 D i.val),Q6x D (Q0 (Q9 D) i.val+v.val)
 have e1:∑ v:Fin (r i.val),d.a (hS.Q8 hn ⟨⟨i.val,hi⟩,v⟩)=
     ∑ v:Fin (r i.val),Q4l d (Q0 r i.val+v.val):=
   Finset.sum_congr rfl (fun v _=> (hS.Qad hn ⟨⟨i.val,hi⟩,v⟩).symm)
 rw [e1,Fin.sum_univ_eq_sum_range (fun v=>Q4l d (Q0 r i.val+v)) (r i.val),
   Fin.sum_univ_eq_sum_range (fun v=>Q6x D (Q0 (Q9 D) i.val+v)) (Q9 D i.val),
   c3 i.val hi,Q41 (c:=i.val) (fun w hw=>c3 w (by omega)) i.val le_rfl,c4]
end C3Layer
section C3Ranks
variable {G:Type u} [Group G] [Finite G] {p:ℕ} {u:ℕ→G} {d:Q5}
  {X:Fin d.n→G} {r :ℕ→ℕ}
lemma Q2.Qmj (hp:p.Prime) (hS:Q2 p u d X r) (hs2:2≤d.s)
    (h3:lcs G 2≠⊥) (h4:lcs G 3=⊥):hS.nL=3:=by
 have h1:=hS.Q83 hs2
 rcases Nat.lt_or_ge hS.nL 4 with hlt | hge
 · rcases (show hS.nL=2∨hS.nL=3 by omega) with h | h
   · exfalso
     have hb:=hS.Qga hS.Q2j.symm (by omega)
     rw[h]at hb
     exact h3 hb
   · exact h
 · exfalso
   have hpos:=hS.Qjb hp 3 (by omega)
   have hcard:=hS.layer_card 3
   rw[h4,Subgroup.card_bot]at hcard
   have hK:1≤ZB (Q15 p G 3):=Nat.card_pos
   have hP:p≤p^r 3:=by
    calc p=p^1:=(pow_one p).symm
      _≤p^r 3:=Nat.pow_le_pow_right hp.pos hpos
   have hm:=Nat.mul_le_mul hP hK
   rw[mul_one,hcard]at hm
   have:=hp.two_le
   omega
lemma Q2.Qn0 (hp:p.Prime) (hS:Q2 p u d X r):r 0=Group.rank G:=by
 have:Fact p.Prime:=⟨hp⟩
 have hpg:IsPGroup p G:=IsPGroup.of_card hS.realizes.card
 have h1:p^r 0*ZB (Qv p G)=ZB (lcs G 0):=hS.layer_card 0
 have h2:=Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini G)
 rw[Q44 hpg,Q1n hpg]at h2
 have h3:ZB (lcs G 0)=ZB G:=by rw[lcs_zero,Subgroup.card_top]
 have h4:0<ZB (Qv p G):=Nat.card_pos
 have h6:p^r 0*ZB (Qv p G)=p^Group.rank G*ZB (Qv p G):=by
  rw[← h2, ← h3,h1]
 exact Nat.pow_right_injective hp.two_le (Nat.eq_of_mul_eq_mul_right h4 h6)
lemma Q2.Qmv [hp:Fact p.Prime] (hS:Q2 p u d X r):r 1=r2 p G:=by
 have h1:p^r 1*ZB (pN p G)=ZB (lcs G 1):=hS.layer_card 1
 have h2:ZB (lcs G 1)=ZB (pN p G)*p^r2 p G:=Q9l
 have h4:0<ZB (pN p G):=Nat.card_pos
 have h6:p^r 1*ZB (pN p G)=p^r2 p G*ZB (pN p G):=by
  rw[h1,h2,mul_comm]
 exact Nat.pow_right_injective hp.out.two_le (Nat.eq_of_mul_eq_mul_right h4 h6)
omit [Finite G] in
lemma Q7h (h4:lcs G 3=⊥):commutator (lcs G 2)=⊥:=by
 rw[eq_bot_iff,commutator_def,Subgroup.commutator_le]
 intro x _ y _
 rw[Subgroup.mem_bot]
 have h:⁅(x:G),(y:G)⁆∈lcs G 3:=Qb x.2 (y:G)
 rw[h4,Subgroup.mem_bot]at h
 have e:((⁅x,y⁆:lcs G 2):G)=⁅(x:G),(y:G)⁆:=by
  simp only[commutatorElement_def,Subgroup.coe_mul,Subgroup.coe_inv]
 exact Subtype.ext (e.trans h)
lemma Q2.Qmo (hp:p.Prime) (hS:Q2 p u d X r) (h4:lcs G 3=⊥):
    r 2=Group.rank (lcs G 2):=by
 have:Fact p.Prime:=⟨hp⟩
 have hpg:IsPGroup p G:=IsPGroup.of_card hS.realizes.card
 have hK:IsPGroup p (lcs G 2):=hpg.to_subgroup _
 have hcomm:=Q7h h4
 have hmap:(Qv p (lcs G 2)).map (lcs G 2).subtype=Q15 p G 2:=by
  show (ZA (ZG (fun g:lcs G 2=>g^p))⊔
      commutator (lcs G 2)).map (lcs G 2).subtype=
    lcs G 3⊔ZA (ZG (fun g:lcs G 2=> (g:G)^p))
  rw[hcomm,sup_bot_eq,h4,bot_sup_eq,MonoidHom.map_closure, ← Set.range_comp]
  refine congrArg ZA (congrArg ZG ?_)
  funext g
  exact map_pow (lcs G 2).subtype g p
 have hc1:ZB ((Qv p (lcs G 2)).map (lcs G 2).subtype)=
     ZB (Qv p (lcs G 2)):=
   (Nat.card_congr (Subgroup.equivMapOfInjective _ _ (lcs G 2).subtype_injective).toEquiv).symm
 rw[hmap]at hc1
 have h1:p^r 2*ZB (Q15 p G 2)=ZB (lcs G 2):=hS.layer_card 2
 have h2:=Subgroup.card_mul_index (Qv p (lcs G 2))
 have h3:(Qv p (lcs G 2)).index =p^Group.rank (lcs G 2):=Q5j hK
 rw[h3]at h2
 have h5:0<ZB (Qv p (lcs G 2)):=Nat.card_pos
 have h6:p^r 2*ZB (Qv p (lcs G 2))=
     p^Group.rank (lcs G 2)*ZB (Qv p (lcs G 2)):=
   calc p^r 2*ZB (Qv p (lcs G 2))=p^r 2*ZB (Q15 p G 2):=by rw[hc1]
     _=ZB (lcs G 2):=h1
     _=ZB (Qv p (lcs G 2))*p^Group.rank (lcs G 2):=h2.symm
     _=p^Group.rank (lcs G 2)*ZB (Qv p (lcs G 2)):=mul_comm _ _
 exact Nat.pow_right_injective hp.two_le (Nat.eq_of_mul_eq_mul_right h5 h6)
omit [Finite G] in
lemma Q2.Qh4 (hS:Q2 p u d X r):Qt G≤d.s:=by
 unfold Qt
 apply Nat.sInf_le
 refine ⟨fun i:Fin d.s=>u i.val,?_⟩
 have e:ZG (fun i:Fin d.s=>u i.val)=u '' ZP d.s:=by
   ext y
   constructor
   · rintro ⟨i,rfl⟩
     exact ⟨i.val,i.isLt,rfl⟩
   · rintro ⟨i,hi,rfl⟩
     exact ⟨⟨i,hi⟩,rfl⟩
 rw[e]
 exact hS.Qbf
end C3Ranks
section CNT3Codes
variable {m r1 r2 s lam m2 m3 r3:ℕ}
noncomputable def Q52 (m r1 r2 s lam m2 m3 r3:ℕ):Finset (Qg m):=by
 classical
 exact Finset.univ.filter (fun D =>D.2.1.val=s∧∃ G∈Q1g m r1 r2 s lam m2 m3 r3,
   ∃ x:(Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (2^m))×
     (Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (2^m)),
     Q1t Nat.prime_two m G (⟨D,x⟩:Qy 2 m))
lemma Qby {D:Qg m}:
    D ∈ Q52 m r1 r2 s lam m2 m3 r3↔D.2.1.val=s∧∃ G∈Q1g m r1 r2 s lam m2 m3 r3,
      ∃ x:(Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (2^m))×
        (Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (2^m)),
        Q1t Nat.prime_two m G (⟨D,x⟩:Qy 2 m):=by
 simp only[Q52,Finset.mem_filter,Finset.mem_univ,true_and]
lemma Qnf:∀ G∈Q1g m r1 r2 s lam m2 m3 r3,∃ D:Qy 2 m,
    Q1t Nat.prime_two m G D ∧D.1∈Q52 m r1 r2 s lam m2 m3 r3:=by
 intro G hG
 have:Fact (Nat.Prime 2):=⟨Nat.prime_two⟩
 have hsG:Qt G=s:=((Q43 G).mp hG).2.2.2.2.2.1
 have hna:lcs G 1≠⊥:=by
  intro h
  apply hG.2.1
  rw[eq_bot_iff, ← h]
  exact Qd (by norm_num)
 obtain ⟨u,d,X,r,hs2,hds, -, -, -, -,hnm, -,hS⟩:=Q6y Nat.prime_two hG.1 hna
 have hsum:∑ t,d.a t=m:=by
  have h1:=hS.realizes.card
  rw[hG.1]at h1
  exact (Nat.pow_right_injective (le_refl 2) h1).symm
 have hs2':2≤d.s:=by rw[hds]; exact hs2
 have hc:Q1t Nat.prime_two m G (hS.enc Nat.prime_two m hnm hs2' hsum):=
   ⟨u,d,X,r,hS,hnm,hs2',hsum,rfl⟩
 have hDs:(hS.enc Nat.prime_two m hnm hs2' hsum).1.2.1.val=s:=hds.trans hsG
 exact ⟨_,hc,Qby.mpr ⟨hDs,G,hG,(hS.enc Nat.prime_two m hnm hs2' hsum).2,hc⟩⟩
lemma Qgb {G:FiniteGrp.{0}} (hG:G∈Q1g m r1 r2 s lam m2 m3 r3)
    {D:Qg m} {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (2^m)}
    {C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (2^m)}
    (hc:Q1t Nat.prime_two m G (⟨D,(B,C)⟩:Qy 2 m)):
    D.1.val=3∧Q9 D 0=r1∧Q9 D 1=r2∧Q9 D 2=r3∧s≤D.2.1.val∧m3≤ m2∧
      (∀ h:0<D.1.val,sL (Qc D) ⟨0,h⟩=r1+lam)∧
      (∀ h:1<D.1.val,sL (Qc D) ⟨1,h⟩=m2 - m3)∧
      (∀ h:2<D.1.val,sL (Qc D) ⟨2,h⟩=m3):=by
 have:Fact (Nat.Prime 2):=⟨Nat.prime_two⟩
 obtain ⟨hcard,h3,h4,hr1,hr2,hs, -,hm2,hm3,hr3⟩:=(Q43 G).mp hG
 have hm:=Qcl hG
 have hc':=hc
 obtain ⟨u,d,X,r,hS,hnm,hs2,hsum,e⟩:=hc
 obtain ⟨c1,c2,c3, -⟩:=hS.Q6d Nat.prime_two hnm hs2 hsum e
 have hnL:=hS.Qmj Nat.prime_two hs2 h3 h4
 have hD3:D.1.val=3:= c1.symm.trans hnL
 have L1:∀ h:1<D.1.val,sL (Qc D) ⟨1,h⟩+m3=m2:=by
  intro h
  have a1:ZB (Q1r G 1)=2^sL (Qc D) ⟨1,h⟩:=
    Q53 Nat.prime_two hc' ⟨1,h⟩ (Or.inl (show 1+1<D.1.val by omega))
  have a2:ZB (Q1r G 1)*ZB (lcs G 2)=ZB (lcs G 1):=
    Q5c 1
  rw[a1,hm2,hm3, ← pow_add]at a2
  exact Nat.pow_right_injective (le_refl 2) a2
 have h1D:1<D.1.val:=by omega
 have hm32:m3≤ m2:=by
  have:=L1 h1D
  omega
 refine ⟨hD3,?_,?_,?_,?_,hm32,?_,?_,?_⟩
 · rw[← c3 0 (by omega),hS.Qn0 Nat.prime_two,hr1]
 · rw[← c3 1 (by omega),hS.Qmv,hr2]
 · rw[← c3 2 (by omega),hS.Qmo Nat.prime_two h4,hr3]
 · rw[← c2, ← hs]
   exact hS.Qh4
 · intro h
   have a1:ZB (Q1r G 0)=2^sL (Qc D) ⟨0,h⟩:=
     Q53 Nat.prime_two hc' ⟨0,h⟩ (Or.inl (show 0+1<D.1.val by omega))
   have a2:ZB (Q1r G 0)*ZB (lcs G 1)=ZB (lcs G 0):=
     Q5c 0
   rw[a1,hm2,lcs_zero,Subgroup.card_top,hcard, ← pow_add]at a2
   have:=Nat.pow_right_injective (le_refl 2) a2
   omega
 · intro h
   have:=L1 h
   omega
 · intro h
   have a1:ZB (Q1r G 2)=2^sL (Qc D) ⟨2,h⟩:=
     Q53 Nat.prime_two hc' ⟨2,h⟩ (Or.inr h4)
   have a2:ZB (Q1r G 2)*ZB (lcs G 3)=ZB (lcs G 2):=
     Q5c 2
   rw[a1,h4,Subgroup.card_bot,mul_one,hm3]at a2
   exact Nat.pow_right_injective (le_refl 2) a2
lemma Q67 {D:Qg m} (hD:D∈Q52 m r1 r2 s lam m2 m3 r3):
    D.1.val=3∧Q9 D 0=r1∧Q9 D 1=r2∧Q9 D 2=r3∧D.2.1.val=s∧m3≤ m2∧
      (∀ h:0<D.1.val,sL (Qc D) ⟨0,h⟩=r1+lam)∧
      (∀ h:1<D.1.val,sL (Qc D) ⟨1,h⟩=m2 - m3)∧
      (∀ h:2<D.1.val,sL (Qc D) ⟨2,h⟩=m3):=by
 obtain ⟨hDs,G,hG,⟨B,C⟩,hc⟩:=Qby.mp hD
 obtain ⟨a1,a2,a3,a4, -,a6⟩:=Qgb hG hc
 exact ⟨a1,a2,a3,a4,hDs,a6⟩
lemma Qi3 {D:Qg m} (hD:D∈Q52 m r1 r2 s lam m2 m3 r3)
    (h2:2<D.1.val):
    Q4 D (Q1 h2)=r1∧Q4 D (Q3 h2)=r2∧Q4 D (Qa h2)=r3∧
      D.2.1.val=s∧m3≤ m2∧
      ∑ v,Qc D ⟨Q1 h2,v⟩=r1+lam∧∑ v,Qc D ⟨Q3 h2,v⟩=m2 - m3∧
      ∑ v,Qc D ⟨Qa h2,v⟩=m3:=by
 obtain ⟨-,hR0,hR1,hR2,hs,hm,hS0,hS1,hS2⟩:=Q67 hD
 exact ⟨hR0,hR1,hR2,hs,hm,hS0 (by omega),hS1 (by omega),hS2 h2⟩
lemma Qkp {D:Qg m} (hD:D∈Q52 m r1 r2 s lam m2 m3 r3):
    Q2y (Qc D)=Q46 r1 r2 r3 lam m2 m3:=by
 obtain ⟨h3,hR0,hR1,hR2, -,hm,hS0,hS1,hS2⟩:=Q67 hD
 rw[Qdu (Qc D) h3 r1 r2 r3 (r1+lam) (m2 - m3) m3 ?_ ?_]
 · unfold Q46
   rw[Nat.sub_add_cancel hm,Nat.add_sub_cancel_left]
 · rintro ⟨i,hi⟩
   have:i<3:=by omega
   interval_cases i
   · show Q9 D 0=_
     simp[hR0]
   · show Q9 D 1=_
     simp[hR1]
   · show Q9 D 2=_
     simp[hR2]
 · rintro ⟨i,hi⟩
   have:i<3:=by omega
   interval_cases i
   · rw[hS0 hi]
     simp
   · rw[hS1 hi]
     simp
   · rw[hS2 hi]
     simp
lemma Qkq {D:Qg m} (hD:D∈Q52 m r1 r2 s lam m2 m3 r3):
    Q2y (Qc D)≤Q46 r1 r2 r3 lam m2 m3:=
  (Qkp hD).le
end CNT3Codes
section CNT3Data
end CNT3Data
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
open Module
universe u
section CbtAbstract
variable {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2] [CommGroup L3]
abbrev Q8a (r :ℕ):Finset (Fin r×Fin r):=Finset.univ.filter (fun q=>q.1<q.2)
lemma Qlc (r :ℕ):(Q8a r).card=r.choose 2:=by
 have h0:=Q4e r 0
 rw[Nat.sub_zero]at h0
 rw[← h0]
 congr 1
 ext q
 simp
lemma Qn9 (r :ℕ) (i j:Fin r):i=j∨(i,j)∈Q8a r∨(j,i)∈Q8a r :=by
 rcases lt_trichotomy i j with h | h | h
 · exact Or.inr (Or.inl (Finset.mem_filter.2 ⟨Finset.mem_univ _,h⟩))
 · exact Or.inl h
 · exact Or.inr (Or.inr (Finset.mem_filter.2 ⟨Finset.mem_univ _,h⟩))
def Qfb {r :ℕ} {W:Type*} [Group W] (π:L2→*W) (g:Fin r→ L1)
    (β1:L1→*L1→*L2):↥(Q8a r)→ W:=
  fun q=>π (β1 (g q.1.1) (g q.1.2))
lemma Qds [Finite L1] [Finite L2] [Finite L3] {W:Type*} [Group W] [Finite W]
    {p r s s3 n b k:ℕ} (hp:p.Prime) (hsr :s≤ r) (hL3:ZB L3=p^s3)
    (y:Fin n→ L2) (hy:ZA (ZG y)=⊤) (g:Fin r→ L1)
    (hg:ZA (ZG g)=⊤) (D:Finset (Fin r×Fin r))
    (hD:∀ q∈D,q.1<q.2) (v:Fin r×Fin r→ L2)
    (π:L2→*W) (hk:ZB π.ker≤p^k) (Z:Set (↥(Q8a r)→ W))
    (S:Set ((L1→*L1→*L2)×(L2→*L1→*L3)))
    (hS : ∀ β∈S,Q21 β.1∧Q1m β.1 β.2∧
        ZA {w | ∃ u∈ZA (g '' {j | (j:ℕ)<s}),
          ∃ u'∈ZA (g '' {j | (j:ℕ)<s}),β.1 u u'=w}=⊤∧
        Q1p p β.2 (ZA (g '' {j | (j:ℕ)<s}))=b∧
        (∀ q∈D,β.1 (g q.1) (g q.2)=v q)∧Qfb π g β.1∈Z):
    S.ncard≤p^(s*(b*(n+s3+1 - b)))*(Z.ncard*p^(k*(r.choose 2 - D.card))):=by
  have:=Q49 (L1:=L1) (L2:=L2) (L3:=L3)
  haveI:Finite (L2→*L3):=
    Finite.of_injective (fun f:L2→*L3=> (f:L2→ L3)) DFunLike.coe_injective
  haveI:Finite (L1→*L2):=
    Finite.of_injective (fun f:L1→*L2=> (f:L1→ L2)) DFunLike.coe_injective
  haveI:Finite (L1→*L1→*L2):=
    Finite.of_injective (fun f:L1→*L1→*L2=> (f:L1→(L1→*L2))) DFunLike.coe_injective
  set C:=ZA (g '' {j | (j:ℕ)<s}) with hCdef
  let c:Fin s→ L1:= fun i=>g (Fin.castLE hsr i)
  rcases S.eq_empty_or_nonempty with hSe | ⟨β1,hβ1⟩
  · rw[hSe,Set.ncard_empty]
    exact Nat.zero_le _
  have hbs3:b≤ s3:=by
   obtain ⟨-, -, -,hb, -⟩:=hS β1 hβ1
   rw[← hb]
   exact Q9y hp hL3 β1.2 _
  let ρ:(L1→*L1→*L2)×(L2→*L1→*L3)→(Fin s→(L2→*L3)):=
    fun β i=>β.2.flip (c i)
  have himg:(ρ '' S).ncard≤p^(s*(b*(n+s3+1 - b))):=by
   refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _))
     (Qhl hp hL3 hbs3 y hy s (b:=b))
   rintro _ ⟨β,hβ,rfl⟩ i
   obtain ⟨-, -, -,hb, -⟩:=hS β hβ
   have hmem:c i∈C:=ZC ⟨Fin.castLE hsr i,by simp,rfl⟩
   have h:=Q3u hp hL3 β.2 C hmem
   rw[hb]at h
   exact h
  have hfib :∀ a,(S∩ρ ⁻¹' {a}).ncard≤Z.ncard*p^(k*(r.choose 2 - D.card)):=by
   intro a
   rcases (S∩ρ ⁻¹' {a}).eq_empty_or_nonempty with he | ⟨β0,hβ0,hβ0a⟩
   · rw[he,Set.ncard_empty]
     exact Nat.zero_le _
   have hβ0a':ρ β0=a:=hβ0a
   have hsl:∀ β∈S∩ρ ⁻¹' {a},∀ z,∀ u∈C,β.2 z u=β0.2 z u:=by
    rintro β ⟨-,hβa⟩ z u hu
    have hβa':ρ β=a:=hβa
    have hgen:∀ j:Fin r,(j:ℕ)<s→β.2.flip (g j)=β0.2.flip (g j):=by
     intro j hj
     have e:= congrFun (hβa'.trans hβ0a'.symm) ⟨(j:ℕ),hj⟩
     change β.2.flip (c ⟨(j:ℕ),hj⟩)=β0.2.flip (c ⟨(j:ℕ),hj⟩) at e
     have e2:c ⟨(j:ℕ),hj⟩=g j:= congrArg g (Fin.ext rfl)
     rw[e2]at e
     exact e
    have hle:C≤(β.2 z).eqLocus (β0.2 z):=by
     rw[hCdef,ZD]
     rintro _ ⟨j,hj,rfl⟩
     show β.2 z (g j)=β0.2 z (g j)
     have:= congrArg (fun φ:L2→*L3=>φ z) (hgen j hj)
     simpa[MonoidHom.flip_apply] using this
    exact hle hu
   have hinj:Set.InjOn Prod.fst (S∩ρ ⁻¹' {a}):=by
    intro β hβ β' hβ' h1
    obtain ⟨hA,hJ,hgen, -⟩:=hS β hβ.1
    obtain ⟨hA',hJ', -⟩:=hS β' hβ'.1
    have h1':β.1=β'.1:=h1
    have h2:β.2=β'.2:=Qbl C hA hA' hJ hJ' hgen (fun x u _=>by rw[h1'])
      (fun z u hu=> (hsl β hβ z u hu).trans (hsl β' hβ' z u hu).symm)
    exact Prod.ext h1' h2
   have hF1:∀ β1∈Prod.fst '' (S∩ρ ⁻¹' {a}),
       Q21 β1∧∀ q∈D,β1 (g q.1) (g q.2)=v q:=by
    rintro _ ⟨β,hβ,rfl⟩
    obtain ⟨hA, -, -, -,hDv, -⟩:=hS β hβ.1
    exact ⟨hA,hDv⟩
   have hrem:=Qi1 g hg (Q8a r) D (Qn9 r) v π
     (Prod.fst '' (S∩ρ ⁻¹' {a})) hF1
   have hZsub:(fun β:L1→*L1→*L2=>fun q:↥(Q8a r)=>π (β (g q.1.1) (g q.1.2))) ''
       (Prod.fst '' (S∩ρ ⁻¹' {a}))⊆Z:=by
     rintro _ ⟨_,⟨β,hβ,rfl⟩,rfl⟩
     exact (hS β hβ.1).2.2.2.2.2
   have hsd:(Q8a r \ D).card=r.choose 2 - D.card:=by
    have hDP:D⊆Q8a r := fun q hq=>Finset.mem_filter.2 ⟨Finset.mem_univ _,hD q hq⟩
    have h:=Finset.card_sdiff_add_card_eq_card hDP
    rw[Qlc]at h
    omega
   calc (S ∩ρ ⁻¹' {a}).ncard≤(Prod.fst '' (S∩ρ ⁻¹' {a})).ncard:=
         Set.ncard_le_ncard_of_injOn Prod.fst (fun β hβ=> ⟨β,hβ,rfl⟩) hinj (Set.toFinite _)
     _≤_:=hrem
     _ ≤ Z.ncard*p^(k*(r.choose 2 - D.card)):=by
         rw[hsd,pow_mul]
         exact Nat.mul_le_mul (Set.ncard_le_ncard hZsub (Set.toFinite Z))
           (Nat.pow_le_pow_left hk _)
  calc S.ncard≤(ρ '' S).ncard*(Z.ncard*p^(k*(r.choose 2 - D.card))):=
        Q2p S ρ _ hfib
    _≤_:=Nat.mul_le_mul_right _ himg
end CbtAbstract
section CbtRed
def Q7p (n p:ℕ):(Fin n→ℤ)→+(Fin n→ZMod p) where
  toFun x v:=(x v:ZMod p)
  map_zero':=by
    funext v
    simp
  map_add' x y:=by
    funext v
    simp
lemma Qg9 {n:ℕ} (p:ℕ) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ)
    (ha:∀ j,1≤a j) (hb:∀ j v,p∣b j v):Q1u p a b≤(Q7p n p).ker :=by
 rw[Q1u,AddSubgroup.closure_le]
 rintro _ ⟨j,rfl⟩
 refine AddMonoidHom.mem_ker.2 (funext fun i=>?_)
 show ((Q3k p a b j i:ℤ):ZMod p)=0
 unfold Q3k
 split_ifs with h1 h2
 · rw [Int.cast_pow,Int.cast_natCast,CharP.cast_eq_zero (ZMod p) p,
     zero_pow (by have:=ha j; omega)]
 · rw [Int.cast_neg,Int.cast_natCast,(CharP.cast_eq_zero_iff (ZMod p) p _).2 (hb j i),
     neg_zero]
 · exact Int.cast_zero
def Q6e {n:ℕ} (p:ℕ) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ)
    (hs:Q1u p a b≤(Q7p n p).ker):Q17 p a b→+(Fin n→ZMod p):=
  QuotientAddGroup.lift (Q1u p a b) (Q7p n p) hs
lemma Qfh {n p:ℕ} (hp:p.Prime) (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ)
    (hs:Q1u p a b≤(Q7p n p).ker) {s2:ℕ}
    (hL:ZB (Multiplicative (Q17 p a b))=p^s2):
    ZB (AddMonoidHom.toMultiplicative (Q6e p a b hs)).ker≤p^(s2 - n):=by
 haveI:NeZero p:=⟨hp.ne_zero⟩
 haveI:Finite (Multiplicative (Q17 p a b)):=
   Nat.finite_of_card_ne_zero (by rw[hL]; exact (pow_pos hp.pos _).ne')
 have hsurj:Function.Surjective (AddMonoidHom.toMultiplicative (Q6e p a b hs)):=by
  intro f
  refine ⟨ZI (ZK
    (fun v=> ((Multiplicative.toAdd f v).val:ℤ))),?_⟩
  apply Multiplicative.toAdd.injective
  funext v
  show (((Multiplicative.toAdd f v).val:ℤ):ZMod p)=Multiplicative.toAdd f v
  rw[Int.cast_natCast,ZMod.natCast_zmod_val]
 have hW:ZB (Multiplicative (Fin n→ZMod p))=p^n:=by
  rw [Nat.card_congr Multiplicative.toAdd,Nat.card_fun,Nat.card_eq_fintype_card (α:=ZMod p),
    ZMod.card,Nat.card_fin]
 have h1:=Subgroup.card_mul_index (AddMonoidHom.toMultiplicative (Q6e p a b hs)).ker
 have h2:(AddMonoidHom.toMultiplicative (Q6e p a b hs)).ker.index =p^n:=by
  rw[← hW]
  exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv
 rw[h2,hL]at h1
 have hpos:0<ZB (AddMonoidHom.toMultiplicative (Q6e p a b hs)).ker :=
   Nat.card_pos
 have hn:n≤ s2:=by
  refine Q28 hp.one_lt ?_
  calc p^n=1*p^n:=(one_mul _).symm
    _≤_:=Nat.mul_le_mul_right _ hpos
    _=p^s2:=h1
 have e:p^s2=p^(s2 - n)*p^n:=by rw[← pow_add,Nat.sub_add_cancel hn]
 rw[e]at h1
 exact (Nat.eq_of_mul_eq_mul_right (pow_pos hp.pos n) h1).le
end CbtRed
section CbtTup
def Q4k {r n:ℕ} {M:Type*} [Neg M] [Zero M] (y:Fin r→Fin r→Fin n→M):
    Fin n→Matrix (Fin r) (Fin r) M:=
  fun v j k=>if j<k then y j k v else if k<j then -y k j v else 0
def Q57 (p:ℕ) {r n:ℕ} (x:Fin r→Fin r→Fin n→ℕ):
    Fin n→Matrix (Fin r) (Fin r) (ZMod p):=
  Q4k (fun j k v=> (x j k v:ZMod p))
def Qf3 {r n:ℕ} {M:Type*} [Zero M] (z:↥(Q8a r)→Multiplicative (Fin n→M)):
    Fin r→Fin r→Fin n→M:=
  fun j k v=>if h:j<k then
    Multiplicative.toAdd (z ⟨(j,k),Finset.mem_filter.2 ⟨Finset.mem_univ _,h⟩⟩) v else 0
lemma Qc0 {r n:ℕ} {M:Type*} [Neg M] [Zero M] {y y':Fin r→Fin r→Fin n→M}
    (h:∀ j k,j<k→∀ v,y j k v=y' j k v):Q4k y=Q4k y':=by
 funext v
 ext j k
 show (if j<k then y j k v else if k<j then -y k j v else 0)=
   (if j<k then y' j k v else if k<j then -y' k j v else 0)
 split_ifs with h1 h2
 · exact h j k h1 v
 · rw[h k j h2 v]
 · rfl
lemma Qdv {F:Type*} [Field F] {r n:ℕ} (y:Fin r→Fin r→Fin n→F)
    (M:Fin n→Matrix (Fin r) (Fin r) F) (hA:∀ v,Alt2.Q1y (M v))
    (h:∀ j k,j<k→∀ v,M v j k=y j k v):Q4k y=M:=by
 funext v
 ext j k
 show (if j<k then y j k v else if k<j then -y k j v else 0)=M v j k
 split_ifs with h1 h2
 · exact (h j k h1 v).symm
 · rw[(hA v).2 k j,h k j h2 v]
 · have hjk:j=k:=le_antisymm (not_lt.1 h2) (not_lt.1 h1)
   subst hjk
   exact ((hA v).1 _).symm
lemma Qjy {r n:ℕ} {M:Type*} [AddGroup M]
    {z z':↥(Q8a r)→Multiplicative (Fin n→M)}
    (h:Q4k (Qf3 z)=Q4k (Qf3 z')):z=z':=by
 funext q
 have hq:q.1.1<q.1.2:=(Finset.mem_filter.1 q.2).2
 apply Multiplicative.toAdd.injective
 funext v
 have e:= congrFun (congrFun (congrFun h v) q.1.1) q.1.2
 simp only[Q4k,Qf3,if_pos hq,dif_pos hq]at e
 exact e
lemma Qie (p:ℕ) {m:ℕ} (D:Qg m) (h2:2<D.1.val) (co:ℕ→ℕ)
    (x:Q5e D h2):Q57 p (Q4s D h2 co x).1=Q57 p x.1:=
  Qc0 fun j k hjk v=>by
    show (((if j<k then x.1 j k v else 0:ℕ)):ZMod p)=_
    rw[if_pos hjk]
end CbtTup
section CbtLead
variable {p c:ℕ} {r :Fin c→ℕ} {a:Q6 c r→ℕ}
end CbtLead
section CbtBasis
variable {G:Type u} [Group G] {p c:ℕ} {r :Fin c→ℕ} {a:Q6 c r→ℕ}
  {g:Q6 c r→G}
lemma Q7.Qlj [hp:Fact p.Prime] [Finite G] (S:Q7 p a g)
    (h1:1<c) (hr1:p^r ⟨1,h1⟩*ZB (pN p G)=ZB (lcs G 1)):
    ∃ bW : Basis (Fin (r ⟨1,h1⟩)) (ZMod p) (Additive (WQ p G)),
      ∀ (x :G) (hx:x∈lcs G 1) (v:Fin (r ⟨1,h1⟩)),
        bW.repr (ZE (Q3o p G ⟨x,hx⟩)) v=
          ((S.nf.coord x ⟨⟨1,h1⟩,v⟩:ℕ):ZMod p):=by
 have:Finite (WQ p G):=Finite.of_surjective _ Q4i
 have:Finite (Additive (WQ p G)):=inferInstance
 have:Module.Finite (ZMod p) (Additive (WQ p G)):=inferInstance
 let w:Fin (r ⟨1,h1⟩)→ Additive (WQ p G):= fun v=>
   ZE (Q3o p G ⟨g ⟨⟨1,h1⟩,v⟩,S.mem ⟨⟨1,h1⟩,v⟩⟩)
 have key :∀ (x:G) (hx:x∈lcs G 1),ZE (Q3o p G ⟨x,hx⟩)=
     ∑ v,((S.nf.coord x ⟨⟨1,h1⟩,v⟩:ℕ):ZMod p)•w v:=by
  intro x hx
  have hb:=S.Q5v ⟨1,h1⟩ (Q3o p G) (fun y hy=>Q8c (Q1j p hy))
    (fun v=> (S.nf.coord x ⟨⟨1,h1⟩,v⟩).val)
    (Q4m g S.mem (fun h=> (S.nf.coord x h).val) ⟨1,h1⟩) hx
    (S.Q54 ⟨1,h1⟩ hx)
  calc Additive.ofMul (Q3o p G ⟨x,hx⟩)=ZE (∏ v:Fin (r ⟨1,h1⟩),
        Q3o p G ⟨g ⟨⟨1,h1⟩,v⟩,S.mem ⟨⟨1,h1⟩,v⟩⟩^(S.nf.coord x ⟨⟨1,h1⟩,v⟩).val):=
        congrArg ZE hb
    _ = ∑ v,((S.nf.coord x ⟨⟨1,h1⟩,v⟩:ℕ):ZMod p)•w v:=by
        rw[ofMul_prod]
        exact Finset.sum_congr rfl fun v _=>
          (ofMul_pow _ _).trans (Nat.cast_smul_eq_nsmul (ZMod p) _ _).symm
 have hspan:⊤≤Submodule.span (ZMod p) (ZG w):=by
  intro y _
  obtain ⟨⟨x,hxm⟩,hx⟩:=Q4i (p:=p) (G:=G) (Additive.toMul y)
  have e:y=ZE (Q3o p G ⟨x,hxm⟩):=by
   rw[hx]
   rfl
  rw[e,key x hxm]
  exact sum_mem fun v _=>Submodule.smul_mem _ _ (Submodule.subset_span ⟨v,rfl⟩)
 have hcard:Fintype.card (Fin (r ⟨1,h1⟩))=Module.finrank (ZMod p) (Additive (WQ p G)):=by
  rw[Fintype.card_fin]
  have h:=Q9l (p:=p) (G:=G)
  rw[← hr1,mul_comm (p^r ⟨1,h1⟩)]at h
  have hpos:0<ZB (pN p G):=Nat.card_pos
  exact Nat.pow_right_injective hp.out.two_le (Nat.eq_of_mul_eq_mul_left hpos h)
 have hbw:∀ v,basisOfTopLeSpanOfCardEqFinrank w hspan hcard v=w v:= fun v=>by
   rw[coe_basisOfTopLeSpanOfCardEqFinrank]
 refine ⟨basisOfTopLeSpanOfCardEqFinrank w hspan hcard,fun x hx v=>?_⟩
 have hs:(∑ v,((S.nf.coord x ⟨⟨1,h1⟩,v⟩:ℕ):ZMod p)•w v)=
     ∑ v,((S.nf.coord x ⟨⟨1,h1⟩,v⟩:ℕ):ZMod p)•
       basisOfTopLeSpanOfCardEqFinrank w hspan hcard v:=
   Finset.sum_congr rfl fun v _=>by rw[hbw v]
 rw[key x hx,hs,Basis.repr_sum_self]
lemma Q7.Qkv [hp:Fact p.Prime] [Finite G] (S:Q7 p a g)
    (h0:0<c) (hr0:p^r ⟨0,h0⟩*ZB (Qv p G)=ZB G):
    ∃ bV:Basis (Fin (r ⟨0,h0⟩)) (ZMod p) (Additive (VQ p G)),
      ∀ j,bV j=ZE (Q29 p G (g ⟨⟨0,h0⟩,j⟩)):=by
 have:Finite (VQ p G):=Finite.of_surjective _ Q1h
 have:Finite (Additive (VQ p G)):=inferInstance
 have:Module.Finite (ZMod p) (Additive (VQ p G)):=inferInstance
 let w:Fin (r ⟨0,h0⟩)→ Additive (VQ p G):= fun j=>
   ZE (Q29 p G (g ⟨⟨0,h0⟩,j⟩))
 have key : ∀ x:G,ZE (Q29 p G x)∈Submodule.span (ZMod p) (ZG w):=by
  intro x
  have hx:x∈lcs G ((⟨0,h0⟩:Fin c):ℕ):=ZM x
  have hb:=S.Q5v ⟨0,h0⟩ ((Q29 p G).comp (lcs G ((⟨0,h0⟩:Fin c):ℕ)).subtype)
    (fun y hy=>by
      show Q29 p G (y:G)=1
      refine (MonoidHom.mem_ker).1 ?_
      rw[Qka]
      exact Q16 p 0 hy)
    (fun v=> (S.nf.coord x ⟨⟨0,h0⟩,v⟩).val)
    (Q4m g S.mem (fun h=> (S.nf.coord x h).val) ⟨0,h0⟩) hx
    (S.Q54 ⟨0,h0⟩ hx)
  have e : ZE (Q29 p G x)=∑ v,(S.nf.coord x ⟨⟨0,h0⟩,v⟩).val•w v:=by
   calc Additive.ofMul (Q29 p G x)=ZE
         ((Q29 p G).comp (lcs G ((⟨0,h0⟩:Fin c):ℕ)).subtype ⟨x,hx⟩):=rfl
     _ = ZE (∏ v:Fin (r ⟨0,h0⟩),
         (Q29 p G).comp (lcs G ((⟨0,h0⟩:Fin c):ℕ)).subtype
           ⟨g ⟨⟨0,h0⟩,v⟩,S.mem ⟨⟨0,h0⟩,v⟩⟩^(S.nf.coord x ⟨⟨0,h0⟩,v⟩).val):=
         congrArg ZE hb
     _ = _:=by
         rw[ofMul_prod]
         exact Finset.sum_congr rfl fun v _=>ofMul_pow _ _
  rw[e]
  exact sum_mem fun v _=>nsmul_mem (Submodule.subset_span (Set.mem_range_self (f:=w) v):
    w v∈Submodule.span (ZMod p) (ZG w)) _
 have hspan:⊤≤Submodule.span (ZMod p) (ZG w):=by
  intro y _
  obtain ⟨x,hx⟩:=Q1h (p:=p) (G:=G) (Additive.toMul y)
  have e:y=ZE (Q29 p G x):=by
   rw[hx]
   rfl
  rw[e]
  exact key x
 have hcard:Fintype.card (Fin (r ⟨0,h0⟩))=Module.finrank (ZMod p) (Additive (VQ p G)):=by
  rw[Fintype.card_fin]
  have h1:=Q3j (p:=p) (Qv p G)
  rw[Q9x (p:=p) (G:=G)]at h1
  have h3:=Subgroup.card_mul_index (Qv p G)
  rw[h1, ← hr0,mul_comm (p^r ⟨0,h0⟩)]at h3
  have hpos:0<ZB (Qv p G):=Nat.card_pos
  exact (Nat.pow_right_injective hp.out.two_le (Nat.eq_of_mul_eq_mul_left hpos h3)).symm
 refine ⟨basisOfTopLeSpanOfCardEqFinrank w hspan hcard,fun j=>?_⟩
 rw[coe_basisOfTopLeSpanOfCardEqFinrank]
end CbtBasis
section CbtTuple
variable {G:Type} [Group G] [Finite G] {p:ℕ} {u:ℕ→G} {d:Q5} {X:Fin d.n→G}
  {r :ℕ→ℕ}
lemma Q2.Qhz [Fact p.Prime] (hp:p.Prime) (hS:Q2 p u d X r) {m:ℕ}
    (hnm:d.n≤ m) (hs2:2≤d.s) (hsum:∑ t,d.a t=m) {D:Qg m}
    {B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    {C:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)}
    (e:hS.enc hp m hnm hs2 hsum=⟨D,(B,C)⟩) (h2:2<D.1.val) (hG:IsPGroup p G):
    ((∀ k,Alt2.Q1y (Q57 p (Q3d D h2 C).1 k))∧
      Alt2.Q1k (Q57 p (Q3d D h2 C).1) ⊤∧
      Alt2.Q2b (Q57 p (Q3d D h2 C).1)=Qt G)∧
    ∀ j v,p∣Q18 D B (Q3 h2) j v:=by
 obtain ⟨cf1, -,cf3,cf4,cf5,cf6, -, -⟩:=hS.Q6d hp hnm hs2 hsum e
 have hn:d.n=Q0 r D.1.val:=by rw[← cf1]; exact hS.Q2j.symm
 have hfo:∀ w≤D.1.val,Q0 r w=Q0 (Q9 D) w:=
   Q41 (fun w hw=>cf3 w (by rw[cf1]; exact hw))
 have f1:=hfo 1 (by omega)
 have e0:Q0 r 0=0:=rfl
 have e0':Q0 (Q9 D) 0=0:=rfl
 obtain ⟨g',S,hpw,hl1, -, -⟩:=hS.Qfk hp hn h2 (Q4 D)
   (fun i=>cf3 i.val (by rw[cf1]; exact i.isLt)) (Qc D) (fun k=>by
     show Q6x D (Q0 (Q9 D) k.1.val+k.2.val)=_
     rw[cf4,hfo _ k.1.isLt.le])
 have hpwB:∀ (i:Fin D.1.val) (j v:Fin (Q4 D i)),
     (S.Ql ⟨i,j⟩ ⟨i,v⟩).val=Q18 D B i j v:=by
  intro i j v
  rw[hpw, ← cf6]
  unfold Q18
  rw[hfo _ i.isLt.le]
 have hr0:p^Q4 D ⟨0,by omega⟩*ZB (Qv p G)=ZB G:=by
   have h:=hS.layer_card 0
   rw[cf3 0 (by rw[cf1]; omega),lcs_zero,Subgroup.card_top]at h
   exact h
 have hr1:p^Q4 D ⟨1,by omega⟩*ZB (pN p G)=ZB (lcs G 1):=by
   have h:=hS.layer_card 1
   rw[cf3 1 (by rw[cf1]; omega)]at h
   exact h
 obtain ⟨bW,hbW⟩:=S.Qlj (by omega) hr1
 obtain ⟨bV,hbV⟩:=S.Qkv (by omega) hr0
 have hlead:∀ j k:Fin (Q4 D (Q1 h2)),j<k→∀ v:Fin (Q4 D (Q3 h2)),
     (Q3d D h2 C).1 j k v=S.Q14 h2 j k v:=by
  intro j k hjk v
  rw[hl1 j k v hjk]
  show Q3x D C (Q0 (Q9 D) 0+j.val) (Q0 (Q9 D) 0+k.val)
    (Q0 (Q9 D) 1+v.val)=_
  rw[cf5,e0', ← f1,e0]
 have hM:=Alt2.Q75 hG bV bW
 have heq:Q57 p (Q3d D h2 C).1=Alt2.Q3c (Q2l (p:=p) (G:=G)) bV bW:=by
  refine Qdv _ _ hM.1 fun j k hjk v=>?_
  show bW.repr (Q2l (bV j) (bV k)) v=(((Q3d D h2 C).1 j k v:ℕ):ZMod p)
  rw[hbV j,hbV k,Qd4]
  refine (hbW _ (cw (g' ⟨Q1 h2,j⟩) (g' ⟨Q1 h2,k⟩)).2 v).trans ?_
  rw[hlead j k hjk v]
  rfl
 refine ⟨by rw[heq]; exact hM,fun j v=>?_⟩
 have hmem:g' ⟨Q3 h2,j⟩^p^Qc D ⟨Q3 h2,j⟩∈lcs G 1:=
   Subgroup.pow_mem _ (S.mem ⟨Q3 h2,j⟩) _
 have hone:Q3o p G ⟨g' ⟨Q3 h2,j⟩^p^Qc D ⟨Q3 h2,j⟩,hmem⟩=1:=by
  have e1:(⟨g' ⟨Q3 h2,j⟩^p^Qc D ⟨Q3 h2,j⟩,hmem⟩:lcs G 1)=
      (⟨g' ⟨Q3 h2,j⟩,S.mem ⟨Q3 h2,j⟩⟩:lcs G 1)^(p^Qc D ⟨Q3 h2,j⟩):=
    Subtype.ext (SubgroupClass.coe_pow
      (⟨g' ⟨Q3 h2,j⟩,S.mem ⟨Q3 h2,j⟩⟩:lcs G 1) (p^Qc D ⟨Q3 h2,j⟩)).symm
  obtain ⟨t,ht⟩:∃ t,Qc D ⟨Q3 h2,j⟩=t+1:=
    ⟨Qc D ⟨Q3 h2,j⟩ - 1,by have:=S.pos ⟨Q3 h2,j⟩; omega⟩
  rw[e1,map_pow,ht,pow_succ,pow_mul,Qn5]
 have h:=hbW _ hmem v
 rw[hone]at h
 simp only[ofMul_one,map_zero,Finsupp.coe_zero,Pi.zero_apply]at h
 rw[← hpwB (Q3 h2) j v]
 exact (CharP.cast_eq_zero_iff (ZMod p) p _).1 h.symm
end CbtTuple
section CbtBrDef
variable {L1 L2 L3:Type*} [CommGroup L1] [CommGroup L2] [CommGroup L3]
open Classical in
noncomputable def Qj8 (p s:ℕ) {r n:ℕ} (g:Fin r→ L1) (y:Fin n→ L2)
    (t:Fin n→Fin r→ L3):ℕ:=
  if h:∃ κ:L2→*L1→*L3,∀ j k,κ (y j) (g k)=t j k then
    Q1p p (Classical.choose h) (ZA (g '' {j | (j:ℕ)<s}))
  else 0
lemma Qce (p s:ℕ) {r n:ℕ} {g:Fin r→ L1} {y:Fin n→ L2}
    (hg:ZA (ZG g)=⊤) (hy:ZA (ZG y)=⊤)
    (t:Fin n→Fin r→ L3) (κ:L2→*L1→*L3) (hκ:∀ j k,κ (y j) (g k)=t j k):
    Qj8 p s g y t=Q1p p κ (ZA (g '' {j | (j:ℕ)<s})):=by
  have h:∃ κ:L2→*L1→*L3,∀ j k,κ (y j) (g k)=t j k:=⟨κ,hκ⟩
  have he:Classical.choose h=κ:=by
   refine MonoidHom.eq_of_eqOn_dense hy ?_
   rintro _ ⟨j,rfl⟩
   refine MonoidHom.eq_of_eqOn_dense hg ?_
   rintro _ ⟨k,rfl⟩
   exact (Classical.choose_spec h j k).trans (hκ j k).symm
  unfold Qj8
  rw[dif_pos h]
  exact congrArg (fun κ'=>Q1p p κ' (ZA (g '' {j | (j:ℕ)<s}))) he
end CbtBrDef
def Q1l (p:ℕ) {n:ℕ} (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ) (j:Fin n):
    Multiplicative (Q17 p a b):=
  ZI (ZK (Pi.single j (1:ℤ)))
def Q56 (p:ℕ) {n:ℕ} (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ) (x:Fin n→ℕ):
    Multiplicative (Q17 p a b):=
  ZI (ZK (fun v=> ((x v:ℕ):ℤ)))
lemma Q23 (p:ℕ) {n:ℕ} (a:Fin n→ℕ) (b:Fin n→Fin n→ℕ):
    ZA (ZG (Q1l p a b))=⊤:=
  Q5q p a b
noncomputable def Q8v (p s:ℕ) {r0 r1 r2:ℕ} (a0:Fin r0→ℕ) (b0:Fin r0→Fin r0→ℕ)
    (a1:Fin r1→ℕ) (b1:Fin r1→Fin r1→ℕ) (a2:Fin r2→ℕ) (b2:Fin r2→Fin r2→ℕ)
    (x2:Fin r1→Fin r0→Fin r2→ℕ):ℕ:=
  Qj8 p s (Q1l p a0 b0) (Q1l p a1 b1) (fun j k=>Q56 p a2 b2 (x2 j k))
section CbtReal
variable {G:Type u} [Group G] {p c:ℕ} {r :Fin c→ℕ} {a:Q6 c r→ℕ}
  {g:Q6 c r→G} {S:Q7 p a g} {h2:2<c}
  {b0:Fin (r (Q1 h2))→Fin (r (Q1 h2))→ℕ}
  {b1:Fin (r (Q3 h2))→Fin (r (Q3 h2))→ℕ}
  {b2:Fin (r (Qa h2))→Fin (r (Qa h2))→ℕ}
lemma Q7.Q27.Qmq (I:S.Q27 h2 b0 b1 b2) (j k:Fin (r (Q1 h2))):
    Q4a (Qe I.φ1) (Qe I.φ2) (Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0 j)
      (Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0 k)=
      Q56 p (fun v=>a ⟨Q3 h2,v⟩) b1 (S.Q14 h2 j k):=by
  have e1:Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0 j=
      Qe I.φ1 (ZH (g ⟨Q1 h2,j⟩)):=(I.Q99 j).symm
  have e2:Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0 k=
      Qe I.φ1 (ZH (g ⟨Q1 h2,k⟩)):=(I.Q99 k).symm
  rw[e1,e2,Qak]
  exact I.Q91 (cw (g ⟨Q1 h2,j⟩) (g ⟨Q1 h2,k⟩)).2
lemma Q7.Q27.Qet (I:S.Q27 h2 b0 b1 b2) (j:Fin (r (Q3 h2)))
    (k:Fin (r (Q1 h2))):
    Q4j (Qe I.φ1) (Qe I.φ2) (Qe I.φ3) (Q1l p (fun v=>a ⟨Q3 h2,v⟩) b1 j)
      (Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0 k)=
      Q56 p (fun v=>a ⟨Qa h2,v⟩) b2 (S.Q1v h2 j k):=by
  have e1:Q1l p (fun v=>a ⟨Q3 h2,v⟩) b1 j=
      Qe I.φ2 (Q1z G ⟨g ⟨Q3 h2,j⟩,S.mem ⟨Q3 h2,j⟩⟩):=(I.Qj6 j).symm
  have e2:Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0 k=
      Qe I.φ1 (ZH (g ⟨Q1 h2,k⟩)):=(I.Q99 k).symm
  rw[e1,e2,Qgr]
  exact I.Qej (Q7s ⟨g ⟨Q3 h2,j⟩,S.mem ⟨Q3 h2,j⟩⟩ (g ⟨Q1 h2,k⟩)).2
lemma Q7.Q27.Qh8 {s:ℕ} (I:S.Q27 h2 b0 b1 b2)
    (hcore:lcs G 1≤⁅ZA ((fun j=>g ⟨Q1 h2,j⟩) '' {j | (j:ℕ)<s}),
        ZA ((fun j=>g ⟨Q1 h2,j⟩) '' {j | (j:ℕ)<s})⁆⊔lcs G 2)
    (D:Finset (Fin (r (Q1 h2))×Fin (r (Q1 h2))))
    (w:Fin (r (Q1 h2))×Fin (r (Q1 h2))→Fin (r (Q3 h2))→ℕ)
    (hDw:∀ q∈D,S.Q14 h2 q.1 q.2=w q):
    (Q4a (Qe I.φ1) (Qe I.φ2),Q4j (Qe I.φ1) (Qe I.φ2) (Qe I.φ3))∈
      Qb7 (Multiplicative (Q17 p (fun v=>a ⟨Qa h2,v⟩) b2)) s
        (Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0) D
        (fun q=>Q56 p (fun v=>a ⟨Q3 h2,v⟩) b1 (w q)):=
  Qgi (Qe I.φ1) (Qe I.φ2) (Qe I.φ3) (fun j=>g ⟨Q1 h2,j⟩)
    (Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0) (fun j=>I.Q99 j) hcore D
    (fun q=>Q56 p (fun v=>a ⟨Q3 h2,v⟩) b1 (w q)) (fun q hq=>by
      refine (I.Q91 (cw (g ⟨Q1 h2,q.1⟩) (g ⟨Q1 h2,q.2⟩)).2).trans ?_
      show _=ZI (ZK (fun v=> ((w q v:ℕ):ℤ)))
      rw[← hDw q hq]
      rfl)
end CbtReal
section CbtLeadBreadth
variable {p c:ℕ} {r :Fin c→ℕ} {a:Q6 c r→ℕ}
lemma Qcw (hp0:0<p) (h2:2<c)
    (b0:Fin (r (Q1 h2))→Fin (r (Q1 h2))→ℕ)
    (b1:Fin (r (Q3 h2))→Fin (r (Q3 h2))→ℕ)
    (b2:Fin (r (Qa h2))→Fin (r (Qa h2))→ℕ) {s:ℕ}
    (D:Finset (Fin (r (Q1 h2))×Fin (r (Q1 h2))))
    (w:Fin (r (Q1 h2))×Fin (r (Q1 h2))→Fin (r (Q3 h2))→ℕ)
    (Λ :Set ((Fin (r (Q1 h2))→Fin (r (Q1 h2))→Fin (r (Q3 h2))→ℕ)×
      (Fin (r (Q3 h2))→Fin (r (Q1 h2))→Fin (r (Qa h2))→ℕ)))
    (hΛ :∀ x∈Λ,∃ (G:Type u) (_:Group G) (_:Finite G) (g:Q6 c r→G)
      (S:Q7 p a g),
      (∀ j v,(S.Ql ⟨Q1 h2,j⟩ ⟨Q1 h2,v⟩).val=b0 j v)∧
      (∀ j v,(S.Ql ⟨Q3 h2,j⟩ ⟨Q3 h2,v⟩).val=b1 j v)∧
      (∀ j v,(S.Ql ⟨Qa h2,j⟩ ⟨Qa h2,v⟩).val=b2 j v)∧
      (3<c∨lcs G 3=⊥)∧
      lcs G 1≤⁅ZA ((fun j=>g ⟨Q1 h2,j⟩) '' {j | (j:ℕ)<s}),
        ZA ((fun j=>g ⟨Q1 h2,j⟩) '' {j | (j:ℕ)<s})⁆⊔lcs G 2∧
      (∀ q∈D,S.Q14 h2 q.1 q.2=w q)∧
      x =(S.Q14 h2,S.Q1v h2))
    (Sβ : Set ((Multiplicative (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0)→*
          Multiplicative (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0)→*
            Multiplicative (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1))×
        (Multiplicative (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1)→*
          Multiplicative (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0)→*
            Multiplicative (Q17 p (fun v=>a ⟨Qa h2,v⟩) b2))))
    (hSβ :∀ (G:Type u) (_:Group G) (g:Q6 c r→G) (S:Q7 p a g)
      (I:S.Q27 h2 b0 b1 b2),
      lcs G 1≤⁅ZA ((fun j=>g ⟨Q1 h2,j⟩) '' {j | (j:ℕ)<s}),
        ZA ((fun j=>g ⟨Q1 h2,j⟩) '' {j | (j:ℕ)<s})⁆⊔lcs G 2→
      (∀ q∈D,S.Q14 h2 q.1 q.2=w q)→(S.Q14 h2,S.Q1v h2)∈Λ→
      (Q4a (Qe I.φ1) (Qe I.φ2),Q4j (Qe I.φ1) (Qe I.φ2) (Qe I.φ3))∈Sβ):
    Λ.ncard≤Sβ.ncard:=by
  classical
  have:Finite (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0):=(Q11 hp0 _ b0).1
  have:Finite (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1):=(Q11 hp0 _ b1).1
  have:Finite (Q17 p (fun v=>a ⟨Qa h2,v⟩) b2):=(Q11 hp0 _ b2).1
  have:Finite (Multiplicative (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0)):=
    Finite.of_equiv _ ZI
  have:Finite (Multiplicative (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1)):=
    Finite.of_equiv _ ZI
  have:Finite (Multiplicative (Q17 p (fun v=>a ⟨Qa h2,v⟩) b2)):=
    Finite.of_equiv _ ZI
  have:=Q49 (L1:=Multiplicative (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0))
    (L2:=Multiplicative (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1))
    (L3:=Multiplicative (Q17 p (fun v=>a ⟨Qa h2,v⟩) b2))
  obtain ⟨R, hR⟩:∃ R:((Fin (r (Q1 h2))→Fin (r (Q1 h2))→Fin (r (Q3 h2))→ℕ)×
      (Fin (r (Q3 h2))→Fin (r (Q1 h2))→Fin (r (Qa h2))→ℕ))→
      ((Multiplicative (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0)→*
          Multiplicative (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0)→*
            Multiplicative (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1))×
        (Multiplicative (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1)→*
          Multiplicative (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0)→*
            Multiplicative (Q17 p (fun v=>a ⟨Qa h2,v⟩) b2)))→Prop,R=
    fun x β=> ∃ (G:Type u) (_:Group G) (g:Q6 c r→G) (S:Q7 p a g)
      (I :S.Q27 h2 b0 b1 b2),x =(S.Q14 h2,S.Q1v h2)∧
        β=(Q4a (Qe I.φ1) (Qe I.φ2),Q4j (Qe I.φ1) (Qe I.φ2) (Qe I.φ3)):=
    ⟨_,rfl⟩
  have hfun:∀ x x' β,R x β→R x' β→x =x':=by
   intro x x' β h h'
   rw[hR]at h h'
   obtain ⟨G,_,g,S,I,rfl,rfl⟩:=h
   obtain ⟨G',_,g',S',I',rfl,hβ⟩:=h'
   obtain ⟨h1,h2'⟩:=Prod.mk.inj hβ
   obtain ⟨e1,e2⟩:=Q7.Qfy hp0 I I' h1 h2'
   rw[e1,e2]
  have hex:∀ x∈Λ,∃ β,β∈Sβ∧R x β:=by
   intro x hx
   obtain ⟨G,_,_,g,S,hb0,hb1,hb2,hl,hcore,hDw,rfl⟩:=hΛ x hx
   obtain ⟨I⟩:=S.Q2t hp0 h2 hl b0 b1 b2 hb0 hb1 hb2
   refine ⟨_,hSβ G inferInstance g S I hcore hDw hx,?_⟩
   rw[hR]
   exact ⟨G,inferInstance,g,S,I,rfl,rfl⟩
  let F:= fun x =>if h:x∈Λ then Classical.choose (hex x h) else 1
  have hF:∀ x (h:x∈Λ),F x =Classical.choose (hex x h):= fun x h=>dif_pos h
  have hmaps:∀ x∈Λ,F x∈Sβ:= fun x h=>by
    rw[hF x h]
    exact (Classical.choose_spec (hex x h)).1
  have hinj:Set.InjOn F Λ:=by
   intro x hx x' hx' he
   refine hfun x x' (F x) ?_ ?_
   · rw[hF x hx]
     exact (Classical.choose_spec (hex x hx)).2
   · rw[he,hF x' hx']
     exact (Classical.choose_spec (hex x' hx')).2
  exact Set.ncard_le_ncard_of_injOn F hmaps hinj (Set.toFinite _)
lemma Qjf (hp:p.Prime) (h2:2<c)
    (b0:Fin (r (Q1 h2))→Fin (r (Q1 h2))→ℕ)
    (b1:Fin (r (Q3 h2))→Fin (r (Q3 h2))→ℕ)
    (b2:Fin (r (Qa h2))→Fin (r (Qa h2))→ℕ) {s:ℕ} (hs:s≤ r (Q1 h2))
    (D:Finset (Fin (r (Q1 h2))×Fin (r (Q1 h2))))
    (w:Fin (r (Q1 h2))×Fin (r (Q1 h2))→Fin (r (Q3 h2))→ℕ)
    (x :(Fin (r (Q1 h2))→Fin (r (Q1 h2))→Fin (r (Q3 h2))→ℕ)×
      (Fin (r (Q3 h2))→Fin (r (Q1 h2))→Fin (r (Qa h2))→ℕ))
    (hx :∃ (G:Type u) (_:Group G) (_:Finite G) (g:Q6 c r→G)
      (S:Q7 p a g),
      (∀ j v,(S.Ql ⟨Q1 h2,j⟩ ⟨Q1 h2,v⟩).val=b0 j v)∧
      (∀ j v,(S.Ql ⟨Q3 h2,j⟩ ⟨Q3 h2,v⟩).val=b1 j v)∧
      (∀ j v,(S.Ql ⟨Qa h2,j⟩ ⟨Qa h2,v⟩).val=b2 j v)∧
      (3<c∨lcs G 3=⊥)∧
      lcs G 1≤⁅ZA ((fun j=>g ⟨Q1 h2,j⟩) '' {j | (j:ℕ)<s}),
        ZA ((fun j=>g ⟨Q1 h2,j⟩) '' {j | (j:ℕ)<s})⁆⊔lcs G 2∧
      (∀ q∈D,S.Q14 h2 q.1 q.2=w q)∧
      x =(S.Q14 h2,S.Q1v h2)):
    Q8v p s (fun v=>a ⟨Q1 h2,v⟩) b0 (fun v=>a ⟨Q3 h2,v⟩) b1
        (fun v=>a ⟨Qa h2,v⟩) b2 x.2∈
      (ZQ (min (∑ v,a ⟨Q3 h2,v⟩) (∑ v,a ⟨Qa h2,v⟩)+1)).filter
        (fun β=> (∑ v,a ⟨Qa h2,v⟩)≤ s*β):=by
  have hp0:=hp.pos
  obtain ⟨G,_,_,g,S,hb0,hb1,hb2,hl,hcore,hDw,rfl⟩:=hx
  obtain ⟨I⟩:=S.Q2t hp0 h2 hl b0 b1 b2 hb0 hb1 hb2
  have:Finite (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1):=(Q11 hp0 _ b1).1
  have:Finite (Q17 p (fun v=>a ⟨Qa h2,v⟩) b2):=(Q11 hp0 _ b2).1
  have:Finite (Multiplicative (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1)):=
    Finite.of_equiv _ ZI
  have:Finite (Multiplicative (Q17 p (fun v=>a ⟨Qa h2,v⟩) b2)):=
    Finite.of_equiv _ ZI
  have hL2:=Q37 I.φ2 I.card2
  have hL3:=Q37 I.φ3 I.card3
  obtain ⟨-, -, -,hgen3, -⟩:=I.Qh8 hcore D w hDw
  obtain ⟨h51,hmin⟩:=Q94 hp hs hL2 hL3 _
    (Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0) hgen3
  have he:Q8v p s (fun v=>a ⟨Q1 h2,v⟩) b0 (fun v=>a ⟨Q3 h2,v⟩) b1
      (fun v=>a ⟨Qa h2,v⟩) b2 (S.Q14 h2,S.Q1v h2).2=
      Q1p p (Q4j (Qe I.φ1) (Qe I.φ2) (Qe I.φ3))
        (ZA (Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0 '' {j | (j:ℕ)<s})):=
    Qce p s (Q23 p _ b0) (Q23 p _ b1)
      (fun j k=>Q56 p (fun v=>a ⟨Qa h2,v⟩) b2 (S.Q1v h2 j k))
      (Q4j (Qe I.φ1) (Qe I.φ2) (Qe I.φ3)) I.Qet
  rw[he,Finset.mem_filter,Finset.mem_range]
  exact ⟨Nat.lt_succ_of_le hmin,h51⟩
lemma Qd0 (hp:p.Prime) (h2:2<c)
    (b0:Fin (r (Q1 h2))→Fin (r (Q1 h2))→ℕ)
    (b1:Fin (r (Q3 h2))→Fin (r (Q3 h2))→ℕ)
    (b2:Fin (r (Qa h2))→Fin (r (Qa h2))→ℕ) {s:ℕ} (hs:s≤ r (Q1 h2))
    (D:Finset (Fin (r (Q1 h2))×Fin (r (Q1 h2))))
    (hD:∀ q∈D,q.1<q.2∧(q.1:ℕ)<s)
    (w:Fin (r (Q1 h2))×Fin (r (Q1 h2))→Fin (r (Q3 h2))→ℕ)
    (Λ :Set ((Fin (r (Q1 h2))→Fin (r (Q1 h2))→Fin (r (Q3 h2))→ℕ)×
      (Fin (r (Q3 h2))→Fin (r (Q1 h2))→Fin (r (Qa h2))→ℕ)))
    (hΛ :∀ x∈Λ,∃ (G:Type u) (_:Group G) (_:Finite G) (g:Q6 c r→G)
      (S:Q7 p a g),
      (∀ j v,(S.Ql ⟨Q1 h2,j⟩ ⟨Q1 h2,v⟩).val=b0 j v)∧
      (∀ j v,(S.Ql ⟨Q3 h2,j⟩ ⟨Q3 h2,v⟩).val=b1 j v)∧
      (∀ j v,(S.Ql ⟨Qa h2,j⟩ ⟨Qa h2,v⟩).val=b2 j v)∧
      (3<c∨lcs G 3=⊥)∧
      lcs G 1≤⁅ZA ((fun j=>g ⟨Q1 h2,j⟩) '' {j | (j:ℕ)<s}),
        ZA ((fun j=>g ⟨Q1 h2,j⟩) '' {j | (j:ℕ)<s})⁆⊔lcs G 2∧
      (∀ q∈D,S.Q14 h2 q.1 q.2=w q)∧
      x =(S.Q14 h2,S.Q1v h2))
    (b :ℕ) (hΛb:∀ x∈Λ,Q8v p s (fun v=>a ⟨Q1 h2,v⟩) b0 (fun v=>a ⟨Q3 h2,v⟩) b1
      (fun v=>a ⟨Qa h2,v⟩) b2 x.2=b):
    Λ.ncard≤p^(s*(b*(r (Q3 h2)+(∑ v,a ⟨Qa h2,v⟩)+1 - b)))*
        p ^(((r (Q1 h2)).choose 2 - D.card)*(∑ v,a ⟨Q3 h2,v⟩) -
          (r (Q1 h2) - s).choose 2*b):=by
  classical
  have hp0:=hp.pos
  have:Finite (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0):=(Q11 hp0 _ b0).1
  have:Finite (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1):=(Q11 hp0 _ b1).1
  have:Finite (Q17 p (fun v=>a ⟨Qa h2,v⟩) b2):=(Q11 hp0 _ b2).1
  have:Finite (Multiplicative (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0)):=
    Finite.of_equiv _ ZI
  have:Finite (Multiplicative (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1)):=
    Finite.of_equiv _ ZI
  have:Finite (Multiplicative (Q17 p (fun v=>a ⟨Qa h2,v⟩) b2)):=
    Finite.of_equiv _ ZI
  rcases Λ.eq_empty_or_nonempty with hE | ⟨x0,hx0⟩
  · rw[hE,Set.ncard_empty]
    exact Nat.zero_le _
  obtain ⟨G0,_,_,g0,S0,hb0,hb1,hb2,hl, -, -, -⟩:=hΛ x0 hx0
  obtain ⟨I0⟩:=S0.Q2t hp0 h2 hl b0 b1 b2 hb0 hb1 hb2
  have hL2:=Q37 I0.φ2 I0.card2
  have hL3:=Q37 I0.φ3 I0.card3
  refine le_trans (Qcw hp0 h2 b0 b1 b2 (s:=s) D w Λ hΛ _ ?_)
    (Q9o hp hs hL2 hL3 (Q1l p (fun v=>a ⟨Q3 h2,v⟩) b1)
      (Q23 p _ b1) (Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0) (Q23 p _ b0)
      D hD (fun q=>Q56 p (fun v=>a ⟨Q3 h2,v⟩) b1 (w q)) (b:=b))
  intro G _ g S I hcore hDw hx
  obtain ⟨hA,hgen,hJ, -,hDv⟩:=I.Qh8 hcore D w hDw
  refine ⟨hA,hgen,hJ,?_,hDv⟩
  rw[← hΛb _ hx]
  exact (Qce p s (Q23 p _ b0) (Q23 p _ b1)
    (fun j k=>Q56 p (fun v=>a ⟨Qa h2,v⟩) b2 (S.Q1v h2 j k))
    (Q4j (Qe I.φ1) (Qe I.φ2) (Qe I.φ3)) I.Qet).symm
lemma Qci (hp:p.Prime) (h2:2<c)
    (b0:Fin (r (Q1 h2))→Fin (r (Q1 h2))→ℕ)
    (b1:Fin (r (Q3 h2))→Fin (r (Q3 h2))→ℕ)
    (b2:Fin (r (Qa h2))→Fin (r (Qa h2))→ℕ) (hb1:∀ j v,p∣b1 j v)
    {s:ℕ} (hs:s≤ r (Q1 h2))
    (D:Finset (Fin (r (Q1 h2))×Fin (r (Q1 h2))))
    (hD:∀ q∈D,q.1<q.2∧(q.1:ℕ)<s)
    (w:Fin (r (Q1 h2))×Fin (r (Q1 h2))→Fin (r (Q3 h2))→ℕ)
    (Z':Set (Fin (r (Q3 h2))→Matrix (Fin (r (Q1 h2))) (Fin (r (Q1 h2))) (ZMod p)))
    (Λ :Set ((Fin (r (Q1 h2))→Fin (r (Q1 h2))→Fin (r (Q3 h2))→ℕ)×
      (Fin (r (Q3 h2))→Fin (r (Q1 h2))→Fin (r (Qa h2))→ℕ)))
    (hΛ :∀ x∈Λ,∃ (G:Type u) (_:Group G) (_:Finite G) (g:Q6 c r→G)
      (S:Q7 p a g),
      (∀ j v,(S.Ql ⟨Q1 h2,j⟩ ⟨Q1 h2,v⟩).val=b0 j v)∧
      (∀ j v,(S.Ql ⟨Q3 h2,j⟩ ⟨Q3 h2,v⟩).val=b1 j v)∧
      (∀ j v,(S.Ql ⟨Qa h2,j⟩ ⟨Qa h2,v⟩).val=b2 j v)∧
      (3<c∨lcs G 3=⊥)∧
      lcs G 1≤⁅ZA ((fun j=>g ⟨Q1 h2,j⟩) '' {j | (j:ℕ)<s}),
        ZA ((fun j=>g ⟨Q1 h2,j⟩) '' {j | (j:ℕ)<s})⁆⊔lcs G 2∧
      (∀ q∈D,S.Q14 h2 q.1 q.2=w q)∧
      x =(S.Q14 h2,S.Q1v h2))
    (hΛZ:∀ x∈Λ,Q57 p x.1∈Z')
    (b :ℕ) (hΛb:∀ x∈Λ,Q8v p s (fun v=>a ⟨Q1 h2,v⟩) b0 (fun v=>a ⟨Q3 h2,v⟩) b1
      (fun v=>a ⟨Qa h2,v⟩) b2 x.2=b):
    Λ.ncard≤p^(s*(b*(r (Q3 h2)+(∑ v,a ⟨Qa h2,v⟩)+1 - b)))*
        (Z'.ncard*p^(((∑ v,a ⟨Q3 h2,v⟩) - r (Q3 h2))*
          ((r (Q1 h2)).choose 2 - D.card))):=by
  classical
  have hp0:=hp.pos
  haveI:NeZero p:=⟨hp.ne_zero⟩
  have:Finite (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0):=(Q11 hp0 _ b0).1
  have:Finite (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1):=(Q11 hp0 _ b1).1
  have:Finite (Q17 p (fun v=>a ⟨Qa h2,v⟩) b2):=(Q11 hp0 _ b2).1
  have:Finite (Multiplicative (Q17 p (fun v=>a ⟨Q1 h2,v⟩) b0)):=
    Finite.of_equiv _ ZI
  have:Finite (Multiplicative (Q17 p (fun v=>a ⟨Q3 h2,v⟩) b1)):=
    Finite.of_equiv _ ZI
  have:Finite (Multiplicative (Q17 p (fun v=>a ⟨Qa h2,v⟩) b2)):=
    Finite.of_equiv _ ZI
  rcases Λ.eq_empty_or_nonempty with hE | ⟨x0,hx0⟩
  · rw[hE,Set.ncard_empty]
    exact Nat.zero_le _
  obtain ⟨G0,_,_,g0,S0,hb0,hb1',hb2,hl, -, -, -⟩:=hΛ x0 hx0
  obtain ⟨I0⟩:=S0.Q2t hp0 h2 hl b0 b1 b2 hb0 hb1' hb2
  have hL2:=Q37 I0.φ2 I0.card2
  have hL3:=Q37 I0.φ3 I0.card3
  have hspan:=Qg9 p (fun v=>a ⟨Q3 h2,v⟩) b1 (fun v=>S0.pos _) hb1
  let π:=AddMonoidHom.toMultiplicative (Q6e p (fun v=>a ⟨Q3 h2,v⟩) b1 hspan)
  have hk:ZB π.ker≤p^((∑ v,a ⟨Q3 h2,v⟩) - r (Q3 h2)):=
    Qfh hp _ b1 hspan hL2
  obtain ⟨Z,hZ⟩:∃ Z:Set (↥(Q8a (r (Q1 h2)))→Multiplicative (Fin (r (Q3 h2))→ZMod p)),
      Z={z | Q4k (Qf3 z)∈Z'}:=⟨_,rfl⟩
  have hZcard:Z.ncard≤Z'.ncard:=by
   refine Set.ncard_le_ncard_of_injOn (fun z=>Q4k (Qf3 z)) ?_ ?_ (Set.toFinite _)
   · intro z hz
     rw[hZ]at hz
     exact hz
   · intro z _ z' _ he
     exact Qjy he
  have hmain:=Qds hp hs hL3 (Q1l p (fun v=>a ⟨Q3 h2,v⟩) b1)
    (Q23 p _ b1) (Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0) (Q23 p _ b0)
    D (fun q hq=> (hD q hq).1) (fun q=>Q56 p (fun v=>a ⟨Q3 h2,v⟩) b1 (w q)) π hk Z
    {β | Q21 β.1∧Q1m β.1 β.2∧
      Subgroup.closure {z | ∃ u∈ZA
          (Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0 '' {j | (j:ℕ)<s}),
        ∃ u'∈ZA (Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0 '' {j | (j:ℕ)<s}),
          β.1 u u'=z}=⊤∧
      Q1p p β.2
        (ZA (Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0 '' {j | (j:ℕ)<s}))=b∧
      (∀ q ∈D,β.1 (Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0 q.1)
        (Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0 q.2)=
          Q56 p (fun v=>a ⟨Q3 h2,v⟩) b1 (w q))∧
      Qfb π (Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0) β.1∈Z} (fun β hβ=>hβ)
  refine le_trans (Qcw hp0 h2 b0 b1 b2 (s:=s) D w Λ hΛ _ ?_)
    (hmain.trans (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hZcard)))
  intro G _ g S I hcore hDw hx
  obtain ⟨hA,hgen,hJ, -,hDv⟩:=I.Qh8 hcore D w hDw
  refine ⟨hA,hJ,hgen,?_,hDv,?_⟩
  · rw [← hΛb _ hx]
    exact (Qce p s (Q23 p _ b0) (Q23 p _ b1)
      (fun j k=>Q56 p (fun v=>a ⟨Qa h2,v⟩) b2 (S.Q1v h2 j k))
      (Q4j (Qe I.φ1) (Qe I.φ2) (Qe I.φ3)) I.Qet).symm
  · rw [hZ]
    show Q4k (Qf3 (Qfb π (Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0)
      (Q4a (Qe I.φ1) (Qe I.φ2))))∈Z'
    have he:Q4k (Qf3 (Qfb π (Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0)
        (Q4a (Qe I.φ1) (Qe I.φ2))))=Q57 p (S.Q14 h2):=by
      refine Qc0 fun j k hjk v=>?_
      show (if h:j<k then Multiplicative.toAdd (π (Q4a (Qe I.φ1) (Qe I.φ2)
        (Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0 j) (Q1l p (fun v=>a ⟨Q1 h2,v⟩) b0 k))) v
          else 0)=((S.Q14 h2 j k v:ℕ):ZMod p)
      rw[dif_pos hjk,I.Qmq j k]
      show (((S.Q14 h2 j k v:ℕ):ℤ):ZMod p)=_
      exact Int.cast_natCast _
    rw[he]
    exact hΛZ _ hx
end CbtLeadBreadth
section CbtCount
lemma Q7x {p m :ℕ} [Fact p.Prime] (hp:p.Prime)
    (T:Set FiniteGrp.{0}) (D:Qg m) (h2:2<D.1.val) (h3:D.1.val=3)
    (B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (p^m)) (s0:ℕ)
    (hT:∀ G∈T,IsPGroup p G∧Qt G=s0):
    (Qw hp T D B).ncard≤
      (∑ β ∈ (ZQ (min (∑ v,Qc D ⟨Q3 h2,v⟩)
          (∑ v,Qc D ⟨Qa h2,v⟩)+1)).filter
          (fun β=> (∑ v,Qc D ⟨Qa h2,v⟩)≤D.2.1.val*β),
        min (p ^ (D.2.1.val*(β *(Q4 D (Q3 h2)+(∑ v,Qc D ⟨Qa h2,v⟩)+1 - β)))*
            p ^(((Q4 D (Q1 h2)).choose 2 - Q4 D (Q3 h2))*
              (∑ v,Qc D ⟨Q3 h2,v⟩) - (Q4 D (Q1 h2) - D.2.1.val).choose 2*β))
          (p ^ (D.2.1.val*(β *(Q4 D (Q3 h2)+(∑ v,Qc D ⟨Qa h2,v⟩)+1 - β)))*
            ({t :Fin (Q4 D (Q3 h2))→
                Matrix (Fin (Q4 D (Q1 h2))) (Fin (Q4 D (Q1 h2))) (ZMod p) |
                (∀ k,Alt2.Q1y (t k))∧Alt2.Q1k t ⊤∧Alt2.Q2b t=s0}.ncard*
              p ^(((∑ v,Qc D ⟨Q3 h2,v⟩) - Q4 D (Q3 h2))*
                ((Q4 D (Q1 h2)).choose 2 - Q4 D (Q3 h2))))))*
        p ^(((Q4 D (Q1 h2)).choose 2 - Q4 D (Q3 h2))*
          ∑ v,Qc D ⟨Qa h2,v⟩):=by
  rcases (Qw hp T D B).eq_empty_or_nonempty with hE | ⟨C0,hC0⟩
  · rw[hE,Set.ncard_empty]
    exact Nat.zero_le _
  obtain ⟨G0,hG0T,u0,d0,X0,r0,hS0,hnm0,hs0,hsum0,e0⟩:=hC0
  obtain ⟨c1,c2,c3, -, -, -,c7,c8⟩:=hS0.Q6d hp hnm0 hs0 hsum0 e0
  have hn0:d0.n=Q0 r0 D.1.val:=by rw[← c1]; exact hS0.Q2j.symm
  have hr00:r0 0=Q9 D 0:= c3 0 (by rw[c1]; omega)
  have hr01:r0 1=Q9 D 1:= c3 1 (by rw[c1]; omega)
  have hsr0:=(hS0.Qhg hn0 (by omega) hS0.Qbf).1
  have hsr :D.2.1.val≤Q4 D (Q1 h2):=by
   show D.2.1.val≤Q9 D 0
   rw[← c2, ← hr00]
   exact hsr0
  have hgood:∀ C∈Qw hp T D B,Qd9 p hp.pos D h2 B (Qn d0 r0) C:=by
   rintro C ⟨G, -,u,d,X,r,hS,hnm,hs2,hsum,e⟩
   obtain ⟨g1,g2,g3, -, -, -,g7, -⟩:=hS.Q6d hp hnm hs2 hsum e
   refine hS.Qkd hp hnm hs2 hsum e h2 h3 _
     (Qau hS hS0 hs2 (g2.trans c2.symm) ?_ ?_)
   · rw[g3 1 (by rw[g1]; omega),hr01]
   · intro k hk
     rw[g7 k hk,c7 k (by rw[c2, ← g2]; exact hk)]
  have htup:∀ C∈Qw hp T D B,Q57 p (Q3d D h2 C).1∈
      {t :Fin (Q4 D (Q3 h2))→
        Matrix (Fin (Q4 D (Q1 h2))) (Fin (Q4 D (Q1 h2))) (ZMod p) |
        (∀ k,Alt2.Q1y (t k))∧Alt2.Q1k t ⊤∧Alt2.Q2b t=s0}:=by
    rintro C ⟨G,hGT,u,d,X,r,hS,hnm,hs2,hsum,e⟩
    obtain ⟨hpG,hsG⟩:=hT G hGT
    obtain ⟨⟨t1,t2,t3⟩, -⟩:=hS.Qhz hp hnm hs2 hsum e h2 hpG
    exact ⟨t1,t2,t3.trans hsG⟩
  have hb1div:∀ j v,p∣Q18 D B (Q3 h2) j v:=
    (hS0.Qhz hp hnm0 hs0 hsum0 e0 h2 (hT G0 hG0T).1).2
  have hjr :∀ j:Fin (Q4 D (Q3 h2)),j.val< r0 1:= fun j=>by
    have:j.val<Q9 D 1:=j.isLt
    omega
  have hDp:∀ q∈Q2h D h2 (Q13 D) (Qn d0 r0),q.1<q.2∧(q.1:ℕ)<D.2.1.val:=by
   intro q hq
   obtain ⟨j,hj1,hj2⟩:=(Finset.mem_filter.mp hq).2
   rw[← c8 _ (hjr j)]at hj1
   refine ⟨?_,?_⟩
   · show q.1.val<q.2.val
     rw[hj1,hj2]
     exact hS0.Q6q hs0 (hjr j)
   · rw[hj1, ← c2]
     have:=hS0.Qat hs0 j.val (hjr j)
     omega
  have hb1:∀ j:Fin (Q4 D (Q3 h2)),Q13 D j.val<Q4 D (Q1 h2):=by
   intro j
   show Q13 D j.val<Q9 D 0
   rw[← c8 _ (hjr j), ← hr00]
   have:=hS0.Qat hs0 j.val (hjr j)
   omega
  have hb2:∀ j:Fin (Q4 D (Q3 h2)),Qn d0 r0 j.val<Q4 D (Q1 h2):=by
   intro j
   show Qn d0 r0 j.val<Q9 D 0
   rw[← hr00]
   have:=hS0.Q3n hs0 j.val (hjr j)
   omega
  obtain ⟨F,hF⟩:∃ F:Fin (Q4 D (Q3 h2))→
      Fin (Q4 D (Q1 h2))×Fin (Q4 D (Q1 h2)),
      ∀ j,(F j).1.val=Q13 D j.val∧(F j).2.val=Qn d0 r0 j.val:=
    ⟨fun j=> (⟨_,hb1 j⟩,⟨_,hb2 j⟩),fun j=> ⟨rfl,rfl⟩⟩
  have hFinj:Function.Injective F:=by
   intro j j' hjj
   have e1:Q13 D j.val=Q13 D j'.val:=by rw[← (hF j).1, ← (hF j').1,hjj]
   have e2:Qn d0 r0 j.val=Qn d0 r0 j'.val:=by rw[← (hF j).2, ← (hF j').2,hjj]
   rw[← c8 _ (hjr j), ← c8 _ (hjr j')]at e1
   exact Fin.ext (hS0.Qa7 hs0 (hjr j) (hjr j') e1 e2)
  have himg:Q2h D h2 (Q13 D) (Qn d0 r0)=Finset.univ.image F:=by
   ext q
   simp only[Q2h,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_image]
   constructor
   · rintro ⟨j,h1,h2'⟩
     exact ⟨j,Prod.ext (Fin.ext ((hF j).1.trans h1.symm)) (Fin.ext ((hF j).2.trans h2'.symm))⟩
   · rintro ⟨j,rfl⟩
     exact ⟨j,(hF j).1,(hF j).2⟩
  have hDcard:(Q2h D h2 (Q13 D) (Qn d0 r0)).card=Q4 D (Q3 h2):=by
   rw[himg,Finset.card_image_of_injective _ hFinj,Finset.card_univ,Fintype.card_fin]
  obtain ⟨ΛB,hΛB⟩:∃ Λ:Set (Q5e D h2),Λ=
      {x | x∈Q8m p D h2 (Q18 D B (Q1 h2)) (Q18 D B (Q3 h2)) (Q18 D B (Qa h2))
        (Q2h D h2 (Q13 D) (Qn d0 r0)) (Q9w D h2 (Q13 D) (Qn d0 r0))∧
        Q57 p x.1∈{t:Fin (Q4 D (Q3 h2))→
          Matrix (Fin (Q4 D (Q1 h2))) (Fin (Q4 D (Q1 h2))) (ZMod p) |
          (∀ k,Alt2.Q1y (t k))∧Alt2.Q1k t ⊤∧Alt2.Q2b t=s0}}:=⟨_,rfl⟩
  have hΛsub:∀ x∈ΛB,x∈Q8m p D h2 (Q18 D B (Q1 h2)) (Q18 D B (Q3 h2))
      (Q18 D B (Qa h2)) (Q2h D h2 (Q13 D) (Qn d0 r0)) (Q9w D h2 (Q13 D) (Qn d0 r0))∧
      Q57 p x.1∈{t:Fin (Q4 D (Q3 h2))→
        Matrix (Fin (Q4 D (Q1 h2))) (Fin (Q4 D (Q1 h2))) (ZMod p) |
        (∀ k,Alt2.Q1y (t k))∧Alt2.Q1k t ⊤∧Alt2.Q2b t=s0}:=by
    intro x hx
    rw[hΛB]at hx
    exact hx
  have hΛfin:ΛB.Finite:=by
   refine (Set.finite_range (fun y:(Fin (Q4 D (Q1 h2))→Fin (Q4 D (Q1 h2))→
       (v:Fin (Q4 D (Q3 h2)))→Fin (p^Qc D ⟨Q3 h2,v⟩))×
       (Fin (Q4 D (Q3 h2))→Fin (Q4 D (Q1 h2))→
         (v:Fin (Q4 D (Qa h2)))→Fin (p^Qc D ⟨Qa h2,v⟩))=>
       ((fun j k v=> (y.1 j k v).val,fun j k v=> (y.2 j k v).val):Q5e D h2))).subset ?_
   intro x hx
   obtain ⟨⟨-,hx1,hx2⟩, -⟩:=hΛsub x hx
   exact ⟨(fun j k v=> ⟨x.1 j k v,hx1 j k v⟩,fun j k v=> ⟨x.2 j k v,hx2 j k v⟩),rfl⟩
  obtain ⟨Λb,hΛb⟩:∃ Λb:ℕ→ Set (Q5e D h2),∀ b,Λb b={x | x∈ΛB∧
      Q8v p D.2.1.val (fun v=>Qc D ⟨Q1 h2,v⟩) (Q18 D B (Q1 h2))
        (fun v=>Qc D ⟨Q3 h2,v⟩) (Q18 D B (Q3 h2))
        (fun v=>Qc D ⟨Qa h2,v⟩) (Q18 D B (Qa h2)) x.2=b}:=
    ⟨fun b=> {x | x∈ΛB∧
      Q8v p D.2.1.val (fun v=>Qc D ⟨Q1 h2,v⟩) (Q18 D B (Q1 h2))
        (fun v=>Qc D ⟨Q3 h2,v⟩) (Q18 D B (Q3 h2))
        (fun v=>Qc D ⟨Qa h2,v⟩) (Q18 D B (Qa h2)) x.2=b},fun b=>rfl⟩
  have hmemb:∀ b x,x∈Λb b→x∈ΛB∧
      Q8v p D.2.1.val (fun v=>Qc D ⟨Q1 h2,v⟩) (Q18 D B (Q1 h2))
        (fun v=>Qc D ⟨Q3 h2,v⟩) (Q18 D B (Q3 h2))
        (fun v=>Qc D ⟨Qa h2,v⟩) (Q18 D B (Qa h2)) x.2=b:=by
    intro b x hx
    rw[hΛb b]at hx
    exact hx
  have hsub:ΛB⊆ ⋃ b∈(ZQ (min (∑ v,Qc D ⟨Q3 h2,v⟩)
      (∑ v,Qc D ⟨Qa h2,v⟩)+1)).filter
      (fun β=> (∑ v,Qc D ⟨Qa h2,v⟩)≤D.2.1.val*β),Λb b:=by
    intro x hx
    refine Set.mem_iUnion₂.2 ⟨_,Qjf (p:=p) (c:=D.1.val) (r :=Q4 D)
      (a:=Qc D) hp h2 (Q18 D B (Q1 h2)) (Q18 D B (Q3 h2)) (Q18 D B (Qa h2)) hsr
      (Q2h D h2 (Q13 D) (Qn d0 r0)) (Q9w D h2 (Q13 D) (Qn d0 r0)) x
      (hΛsub x hx).1.1,?_⟩
    rw[hΛb]
    exact ⟨hx,rfl⟩
  have hunfin:(⋃ b∈(ZQ (min (∑ v,Qc D ⟨Q3 h2,v⟩)
      (∑ v,Qc D ⟨Qa h2,v⟩)+1)).filter
      (fun β=> (∑ v,Qc D ⟨Qa h2,v⟩)≤D.2.1.val*β),Λb b).Finite:=
    hΛfin.subset (Set.iUnion₂_subset fun b _ x hx => (hmemb b x hx).1)
  have hLead : ΛB.ncard≤∑ β∈(ZQ (min (∑ v,Qc D ⟨Q3 h2,v⟩)
          (∑ v,Qc D ⟨Qa h2,v⟩)+1)).filter
          (fun β=> (∑ v,Qc D ⟨Qa h2,v⟩)≤D.2.1.val*β),
        min (p ^ (D.2.1.val*(β *(Q4 D (Q3 h2)+(∑ v,Qc D ⟨Qa h2,v⟩)+1 - β)))*
            p ^(((Q4 D (Q1 h2)).choose 2 - Q4 D (Q3 h2))*
              (∑ v,Qc D ⟨Q3 h2,v⟩) - (Q4 D (Q1 h2) - D.2.1.val).choose 2*β))
          (p ^ (D.2.1.val*(β *(Q4 D (Q3 h2)+(∑ v,Qc D ⟨Qa h2,v⟩)+1 - β)))*
            ({t :Fin (Q4 D (Q3 h2))→
                Matrix (Fin (Q4 D (Q1 h2))) (Fin (Q4 D (Q1 h2))) (ZMod p) |
                (∀ k,Alt2.Q1y (t k))∧Alt2.Q1k t ⊤∧Alt2.Q2b t=s0}.ncard*
              p ^(((∑ v,Qc D ⟨Q3 h2,v⟩) - Q4 D (Q3 h2))*
                ((Q4 D (Q1 h2)).choose 2 - Q4 D (Q3 h2))))):=by
    refine (Set.ncard_le_ncard hsub hunfin).trans ((Q78 _ Λb).trans ?_)
    refine Finset.sum_le_sum fun b _=>le_min ?_ ?_
    · have h:=Qd0 (p:=p) (c:=D.1.val) (r :=Q4 D) (a:=Qc D) hp h2
        (Q18 D B (Q1 h2)) (Q18 D B (Q3 h2)) (Q18 D B (Qa h2)) hsr
        (Q2h D h2 (Q13 D) (Qn d0 r0)) hDp (Q9w D h2 (Q13 D) (Qn d0 r0)) (Λb b)
        (fun x hx => ((hΛsub x (hmemb b x hx).1).1).1) b (fun x hx => (hmemb b x hx).2)
      rw[hDcard]at h
      exact h
    · have h:=Qci (p:=p) (c:=D.1.val) (r :=Q4 D) (a:=Qc D) hp h2
        (Q18 D B (Q1 h2)) (Q18 D B (Q3 h2)) (Q18 D B (Qa h2)) hb1div hsr
        (Q2h D h2 (Q13 D) (Qn d0 r0)) hDp (Q9w D h2 (Q13 D) (Qn d0 r0))
        {t :Fin (Q4 D (Q3 h2))→
          Matrix (Fin (Q4 D (Q1 h2))) (Fin (Q4 D (Q1 h2))) (ZMod p) |
          (∀ k,Alt2.Q1y (t k))∧Alt2.Q1k t ⊤∧Alt2.Q2b t=s0} (Λb b)
        (fun x hx => ((hΛsub x (hmemb b x hx).1).1).1)
        (fun x hx => (hΛsub x (hmemb b x hx).1).2) b (fun x hx => (hmemb b x hx).2)
      rw[hDcard]at h
      exact h
  have hDeep:=Q74 (Γ:=Qdf p D h2)
    (Q7n (p:=p) (fun v:Fin (Q4 D (Qa h2))=>Qc D ⟨Qa h2,v⟩))
    (Q2h D h2 (Q13 D) (Qn d0 r0)) (fun q hq=> (hDp q hq).1)
    (fun _ _=> ⟨0,pow_pos hp.pos _⟩)
  rw[hDcard]at hDeep
  have hinj:Set.InjOn (fun C=> (Q3d D h2 C,Q6o hp.pos D h2 C))
      (Qw hp T D B):=by
    intro C hC C' hC' he
    exact Qfz hp.pos h2 (hgood C hC) (hgood C' hC') (congrArg Prod.fst he)
      (congrArg Prod.snd he)
  have hmaps:∀ C∈Qw hp T D B,(fun C=> (Q3d D h2 C,Q6o hp.pos D h2 C)) C∈
      (Q4s D h2 (Qn d0 r0) '' ΛB)×ˢ
        Q5y p hp.pos D h2 (Q2h D h2 (Q13 D) (Qn d0 r0)):=by
    intro C hC
    obtain ⟨x,hx,hxe⟩:=(hgood C hC).lead
    have hxB:x∈ΛB:=by
     rw[hΛB]
     refine ⟨hx,?_⟩
     have h:=htup C hC
     rw[hxe,Qie]at h
     exact h
    show (Q3d D h2 C,Q6o hp.pos D h2 C)∈_
    exact Set.mk_mem_prod ⟨x,hxB,hxe.symm⟩ (hgood C hC).deep
  calc (Qw hp T D B).ncard
      ≤ ((Q4s D h2 (Qn d0 r0) '' ΛB)×ˢ
          Q5y p hp.pos D h2 (Q2h D h2 (Q13 D) (Qn d0 r0))).ncard:=
        Set.ncard_le_ncard_of_injOn _ hmaps hinj
          ((hΛfin.image (Q4s D h2 (Qn d0 r0))).prod (Set.toFinite _))
    _=(Q4s D h2 (Qn d0 r0) '' ΛB).ncard*
          (Q5y p hp.pos D h2 (Q2h D h2 (Q13 D) (Qn d0 r0))).ncard:=Set.ncard_prod
    _ ≤ ΛB.ncard*(Q5y p hp.pos D h2 (Q2h D h2 (Q13 D) (Qn d0 r0))).ncard:=
        Nat.mul_le_mul_right _ (Set.ncard_image_le hΛfin)
    _≤_:=Nat.mul_le_mul hLead hDeep
lemma Q6j {m : ℕ} (T:Set FiniteGrp.{0})
    (D:Qg m) (h2:2<D.1.val) (h3:D.1.val=3)
    (B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (2^m)) (s0:ℕ)
    (hT:∀ G∈T,IsPGroup 2 G∧Qt G=s0):
    (Qw Nat.prime_two T D B).ncard≤
      (∑ β ∈ (ZQ (min (∑ v,Qc D ⟨Q3 h2,v⟩)
          (∑ v,Qc D ⟨Qa h2,v⟩)+1)).filter
          (fun β=> (∑ v,Qc D ⟨Qa h2,v⟩)≤D.2.1.val*β),
        min (2 ^ (D.2.1.val*(β *(Q4 D (Q3 h2)+(∑ v,Qc D ⟨Qa h2,v⟩)+1 - β)))*
            2 ^(((Q4 D (Q1 h2)).choose 2 - Q4 D (Q3 h2))*
              (∑ v,Qc D ⟨Q3 h2,v⟩) - (Q4 D (Q1 h2) - D.2.1.val).choose 2*β))
          (2 ^ (D.2.1.val*(β *(Q4 D (Q3 h2)+(∑ v,Qc D ⟨Qa h2,v⟩)+1 - β)))*
            (Alt2.N2 (Q4 D (Q1 h2)) (Q4 D (Q3 h2)) s0*
              2 ^(((∑ v,Qc D ⟨Q3 h2,v⟩) - Q4 D (Q3 h2))*
                ((Q4 D (Q1 h2)).choose 2 - Q4 D (Q3 h2))))))*
        2 ^(((Q4 D (Q1 h2)).choose 2 - Q4 D (Q3 h2))*
          ∑ v,Qc D ⟨Qa h2,v⟩):=by
  rw[Alt2.Qe4]
  exact Q7x Nat.prime_two T D h2 h3 B s0 hT
end CbtCount
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
section CNT3Final
lemma Qla:Qlf:=by
 intro m r1 r2 s lam m2 m3 r3 G hG
 obtain ⟨D,hc,hD⟩:=Qnf G hG
 have h3:D.1.1.val=3:=(Q67 hD).1
 have h2:2<D.1.1.val:=by omega
 obtain ⟨hr1,hr2, -,hs, -, -,hs2,hs3⟩:=Qi3 hD h2
 exact ⟨D,hc,⟨h2,h3,hs,hr1,hr2,hs2,hs3⟩,Qkq hD⟩
variable {m r1 r2 s lam m2 m3 r3:ℕ}
lemma Qf9 (a b c:ℕ):min a b*c≤ min (a*c) (b*c):=
  le_min (Nat.mul_le_mul_right _ (min_le_left _ _)) (Nat.mul_le_mul_right _ (min_le_right _ _))
lemma Qey (D:Qg m) (hL:Q5d r1 r2 s m2 m3 D)
    (B:Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (2^m)):
    (Qw Nat.prime_two (Q1g m r1 r2 s lam m2 m3 r3) D B).ncard≤
      ∑ β∈Q4r s m2 m3,
        min (Q35 r1 r2 s m2 m3 β) (Q3m r1 r2 s m2 m3 β):=by
 have:Fact (Nat.Prime 2):=⟨Nat.prime_two⟩
 obtain ⟨h2,h3,hs,hr1,hr2,hs2,hs3⟩:=hL
 have hT:∀ G∈Q1g m r1 r2 s lam m2 m3 r3,IsPGroup 2 G∧Qt G=s:=by
  intro G hG
  have hG':=(Q43 G).mp hG
  exact ⟨IsPGroup.of_card hG'.1,hG'.2.2.2.2.2.1⟩
 have h:=Q6j (Q1g m r1 r2 s lam m2 m3 r3) D h2 h3 B s hT
 rw[hs2,hs3,hr1,hr2]at h
 refine h.trans ?_
 rw[hs,Finset.sum_mul]
 apply Finset.sum_le_sum
 intro β _
 refine (Qf9 _ _ _).trans (min_le_min (le_of_eq ?_) (le_of_eq ?_))
 · unfold Q35
   ring
 · unfold Q3m
   rw[Nat.mul_comm (m2 - m3 - r2)]
   ring
lemma Qma:Qmm:=by
 obtain ⟨C0,hC0⟩:=Qna
 refine ⟨C0+1,fun m r1 r2 s lam m2 m3 r3 hne=>?_⟩
 obtain ⟨hm,hsr,hr2C,h32,hr2s2,hadm,hN⟩:=Qfs Qla hne
 obtain ⟨b2,hb2,hmax⟩:=Finset.exists_max_image (Q4r s m2 m3)
   (fun β=>min (Q9p r1 r2 s m2 m3 β) (Q8i r1 r2 s m2 m3 β)) hadm
 obtain ⟨hb2a,hb2b⟩:=Qe8.mp hb2
 refine ⟨b2,hb2b,(le_min_iff.mp hb2a).1,(le_min_iff.mp hb2a).2,?_⟩
 set n:=min (m2 - m3) m3 with hn
 have hcard:=Qg0 s m2 m3
 have hM :∀ D:Qg m,Q5d r1 r2 s m2 m3 D→
     ∀ B :Fin D.2.2.1.tot→Fin D.2.2.1.tot→Fin (2^m),
       ((Qw Nat.prime_two (Q1g m r1 r2 s lam m2 m3 r3) D B).ncard:ℝ)≤
         ((n:ℝ)+1)*(2:ℝ)^(min (Q9p r1 r2 s m2 m3 b2) (Q8i r1 r2 s m2 m3 b2)):=by
  intro D hL B
  have h1:=Qey (lam:=lam) (r3:=r3) D hL B
  have h1':((Qw Nat.prime_two (Q1g m r1 r2 s lam m2 m3 r3) D B).ncard:ℝ)≤
      ∑ β∈Q4r s m2 m3,
        ((min (Q35 r1 r2 s m2 m3 β) (Q3m r1 r2 s m2 m3 β):ℕ):ℝ):=by
   exact_mod_cast h1
  refine h1'.trans (Qeb hcard _
    (fun β=>min (Q9p r1 r2 s m2 m3 β) (Q8i r1 r2 s m2 m3 β)) b2 (fun β hβ=>?_) hmax)
  obtain ⟨hβa, -⟩:=Qe8.mp hβ
  have eA:=Qhj (β:=β) hsr hr2C h32 (le_min_iff.mp hβa).1 (le_min_iff.mp hβa).2
  have eB:=Qje (β:=β) hsr hr2C h32 hr2s2 (le_min_iff.mp hβa).2
  have hSA':((min (Q35 r1 r2 s m2 m3 β) (Q3m r1 r2 s m2 m3 β):ℕ):ℝ)≤
      (Q35 r1 r2 s m2 m3 β:ℝ):=by exact_mod_cast min_le_left _ _
  have hSB':((min (Q35 r1 r2 s m2 m3 β) (Q3m r1 r2 s m2 m3 β):ℕ):ℝ)≤
      (Q3m r1 r2 s m2 m3 β:ℝ):=by exact_mod_cast min_le_right _ _
  show ((min (Q35 r1 r2 s m2 m3 β) (Q3m r1 r2 s m2 m3 β):ℕ):ℝ)≤
    (2:ℝ)^(min (Q9p r1 r2 s m2 m3 β) (Q8i r1 r2 s m2 m3 β))
  rcases le_total (Q9p r1 r2 s m2 m3 β) (Q8i r1 r2 s m2 m3 β) with hle | hle
  · rw[min_eq_left hle, ← eA]
    exact hSA'
  · rw[min_eq_right hle]
    exact hSB'.trans eB
 have hcount:=Qii Qla _ (by positivity) hM
 have hnm:n≤ m:=by
  have:=Qcl hne.some_mem
  omega
 exact Ql5 hC0 hm hnm hN hcount
end CNT3Final
end OMA.SimsLite
namespace OMA.SimsLite
open scoped commutatorElement
lemma redA_H1:
    OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1_H3_R2_H1_R1.H1:=by
 obtain ⟨C,hC⟩:=Qma
 refine ⟨C,fun m r1 r2 s s1 m2 m3 r3 S hS hne=>?_⟩
 have:Fact (Nat.Prime 2):=⟨Nat.prime_two⟩
 obtain ⟨G,hG⟩:=hne
 have hle:r1≤ s1:=by
  have hG':=hG
  rw[hS]at hG'
  obtain ⟨hc, -, -,hr1, -, -,hi, -⟩:=hG'
  have hp:IsPGroup 2 G:=IsPGroup.of_card hc
  have h:=hi.symm.trans (Q4o hp)
  have h':=Nat.pow_right_injective (le_refl 2) h
  omega
 have hSeq:S=Q1g m r1 r2 s (s1 - r1) m2 m3 r3:=by
  rw[hS,Q1g,Nat.add_sub_of_le hle]
 have hne:(Q1g m r1 r2 s (s1 - r1) m2 m3 r3).Nonempty:=⟨G,hSeq▸hG⟩
 obtain ⟨c1,c2,c3,c4,c5,c6⟩:=Q5n hne.some_mem
 obtain ⟨-, -, -, -,hr2s2, -, -⟩:=Qfs Qla hne
 refine ⟨⟨hle,c1,c2,c3,c4,hr2s2,c5,c6⟩,?_⟩
 obtain ⟨b2,h1,h2,h3,hlog⟩:=hC m r1 r2 s (s1 - r1) m2 m3 r3 hne
 refine ⟨b2,h1,h2,h3,?_⟩
 have e1:Q2d m r1 r2 s (s1 - r1) m2 m3 r3=
     Quotient.mk (CategoryTheory.isIsomorphicSetoid FiniteGrp.{0}) '' S:=by
  unfold Q2d
  rw[hSeq]
 rw[e1,Q8i,Alt2.Qiq,Alt2.Qe4]at hlog
 exact hlog
end OMA.SimsLite
theorem OMA.solution:OMA.R_Erdos1160_erdos_1160_variants_sum_R1_H2_R1_H2_R1_H2_R1_H3_R2_H1_R1.H1:= OMA.SimsLite.redA_H1
