import OMAReductions.R_Erdos186_erdos_186_R1
/-!
Shared definitions for the Pham-Zakharov and Conlon-Fox-Pham proof of Erdős Problem 186 (H2).
-/
open Finset Filter Topology
open scoped Pointwise
namespace E186
abbrev ZV (d : ℕ) := Fin d → ℤ
abbrev RV (d : ℕ) := Fin d → ℝ
def zR {d : ℕ} (v : ZV d) : RV d := fun i => (v i : ℝ)
lemma zR0 (d : ℕ) : zR (0 : ZV d) = 0 := by
  ext i; simp [zR]
lemma zRa {d : ℕ} (u v : ZV d) : zR (u + v) = zR u + zR v := by
  ext i; simp [zR]
lemma zRs {d : ℕ} (u v : ZV d) : zR (u - v) = zR u - zR v := by
  ext i; simp [zR]
lemma zRn {d : ℕ} (u : ZV d) : zR (-u) = -zR u := by
  ext i; simp [zR]
lemma zRm {d : ℕ} (c : ℤ) (u : ZV d) : zR (c • u) = (c : ℝ) • zR u := by
  ext i; simp [zR]
lemma zRu {d : ℕ} {ι : Type*} (s : Finset ι) (f : ι → ZV d) :
    zR (∑ i ∈ s, f i) = ∑ i ∈ s, zR (f i) := by
  ext j; simp [zR]
lemma zRi (d : ℕ) : Function.Injective (@zR d) := by
  intro u v h
  ext i
  exact Int.cast_injective (congrFun h i)
structure ZB (d : ℕ) where
  lo : Fin d → ℤ
  hi : Fin d → ℤ
  hle : ∀ i, lo i ≤ hi i
def ZB.tF {d : ℕ} (B : ZB d) : Finset (ZV d) :=
  Fintype.piFinset (fun i => Finset.Icc (B.lo i) (B.hi i))
def ZB.width {d : ℕ} (B : ZB d) (i : Fin d) : ℕ :=
  (B.hi i - B.lo i + 1).toNat
def ZB.vol {d : ℕ} (B : ZB d) : ℕ :=
  ∏ i : Fin d, B.width i
lemma ZB.mTF {d : ℕ} (B : ZB d) (x : ZV d) :
    x ∈ B.tF ↔ ∀ i, B.lo i ≤ x i ∧ x i ≤ B.hi i := by
  simp [ZB.tF]
lemma ZB.wP {d : ℕ} (B : ZB d) (i : Fin d) : 0 < B.width i := by
  have := B.hle i
  unfold ZB.width
  omega
lemma ZB.vP {d : ℕ} (B : ZB d) : 0 < B.vol :=
  Finset.prod_pos (fun i _ => B.wP i)
lemma ZB.cTF {d : ℕ} (B : ZB d) : B.tF.card = B.vol := by
  unfold ZB.tF ZB.vol ZB.width
  rw [Fintype.card_piFinset]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  rw [Int.card_Icc]
  have := B.hle i
  omega
def ZB.symm {d : ℕ} (w : Fin d → ℕ) : ZB d where
  lo := fun i => -(w i : ℤ)
  hi := fun i => (w i : ℤ)
  hle := fun i => by omega
lemma ZB.zMS {d : ℕ} (w : Fin d → ℕ) : (0 : ZV d) ∈ (ZB.symm w).tF := by
  rw [ZB.mTF]
  intro i
  simp [ZB.symm]
structure GAP (G : Type*) [AddCommGroup G] (d : ℕ) where
  base : G
  step : Fin d → G
  lo : Fin d → ℤ
  hi : Fin d → ℤ
  hle : ∀ i, lo i ≤ hi i
def GAP.eval {G : Type*} [AddCommGroup G] {d : ℕ} (P : GAP G d) (n : ZV d) : G :=
  P.base + ∑ i : Fin d, n i • P.step i
def GAP.cB {G : Type*} [AddCommGroup G] {d : ℕ} (P : GAP G d) : ZB d :=
  ⟨P.lo, P.hi, P.hle⟩
def GAP.tF {G : Type*} [AddCommGroup G] [DecidableEq G] {d : ℕ} (P : GAP G d) : Finset G :=
  P.cB.tF.image P.eval
def GAP.width {G : Type*} [AddCommGroup G] {d : ℕ} (P : GAP G d) (i : Fin d) : ℕ :=
  P.cB.width i
def GAP.vol {G : Type*} [AddCommGroup G] {d : ℕ} (P : GAP G d) : ℕ :=
  P.cB.vol
def GAP.iP {G : Type*} [AddCommGroup G] {d : ℕ} (P : GAP G d) : Prop :=
  Set.InjOn P.eval (P.cB.tF : Set (ZV d))
def GAP.iC {G : Type*} [AddCommGroup G] {d : ℕ} (P : GAP G d) : Prop :=
  P.base = 0 ∧ ∀ i, P.lo i ≤ 0 ∧ 0 ≤ P.hi i
def GAP.iS {G : Type*} [AddCommGroup G] {d : ℕ} (P : GAP G d) : Prop :=
  P.base = 0 ∧ ∀ i, P.lo i = -P.hi i
def GAP.nS {G : Type*} [AddCommGroup G] {d : ℕ} (P : GAP G d) (k : ℕ) : GAP G d where
  base := (k : ℤ) • P.base
  step := P.step
  lo := fun i => (k : ℤ) * P.lo i
  hi := fun i => (k : ℤ) * P.hi i
  hle := fun i => mul_le_mul_of_nonneg_left (P.hle i) (Nat.cast_nonneg k)
def GAP.iSP {G : Type*} [AddCommGroup G] {d : ℕ} (s : ℕ) (P : GAP G d) : Prop :=
  (P.nS s).iP
noncomputable def GAP.rS {G : Type*} [AddCommGroup G] {d : ℕ}
    (P : GAP G d) (c : ℝ) (hc : 0 ≤ c) (hcent : P.iC) : GAP G d where
  base := 0
  step := P.step
  lo := fun i => ⌈c * (P.lo i : ℝ)⌉
  hi := fun i => ⌊c * (P.hi i : ℝ)⌋
  hle := fun i => by
    have h1 : c * (P.lo i : ℝ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hc (by exact_mod_cast (hcent.2 i).1)
    have h2 : 0 ≤ c * (P.hi i : ℝ) :=
      mul_nonneg hc (by exact_mod_cast (hcent.2 i).2)
    have h1' : ⌈c * (P.lo i : ℝ)⌉ ≤ 0 := Int.ceil_le.mpr (by simpa using h1)
    have h2' : 0 ≤ ⌊c * (P.hi i : ℝ)⌋ := Int.le_floor.mpr (by simpa using h2)
    omega
lemma GAP.cLV {G : Type*} [AddCommGroup G] [DecidableEq G] {d : ℕ}
    (P : GAP G d) : P.tF.card ≤ P.vol := by
  calc P.tF.card ≤ P.cB.tF.card := Finset.card_image_le
    _ = P.vol := P.cB.cTF
lemma GAP.cEV {G : Type*} [AddCommGroup G] [DecidableEq G] {d : ℕ}
    {P : GAP G d} (hp : P.iP) : P.tF.card = P.vol := by
  rw [GAP.tF, Finset.card_image_of_injOn hp, P.cB.cTF]
  rfl
lemma GAP.sIC {G : Type*} [AddCommGroup G] {d : ℕ}
    {P : GAP G d} (hs : P.iS) : P.iC := by
  refine ⟨hs.1, fun i => ?_⟩
  have h1 := P.hle i
  have h2 := hs.2 i
  omega
lemma GAP.vP {G : Type*} [AddCommGroup G] {d : ℕ} (P : GAP G d) : 0 < P.vol :=
  P.cB.vP
lemma GAP.zMC {G : Type*} [AddCommGroup G] [DecidableEq G] {d : ℕ}
    {P : GAP G d} (hcent : P.iC) : (0 : G) ∈ P.tF := by
  rw [GAP.tF, Finset.mem_image]
  refine ⟨0, ?_, by simp [GAP.eval, hcent.1]⟩
  rw [ZB.mTF]
  intro i
  exact hcent.2 i
def iSm {G : Type*} [AddCommMonoid G] [DecidableEq G] : ℕ → Finset G → Finset G
  | 0, _ => {0}
  | k + 1, A => iSm k A + A
lemma zMI {G : Type*} [AddCommMonoid G] [DecidableEq G] {A : Finset G}
    (h0 : 0 ∈ A) : ∀ k : ℕ, 0 ∈ iSm k A
  | 0 => by simp [iSm]
  | k + 1 => by
      simpa [iSm] using Finset.add_mem_add (zMI h0 k) h0
lemma iSM {G : Type*} [AddCommMonoid G] [DecidableEq G] {A B : Finset G}
    (h : A ⊆ B) : ∀ k : ℕ, iSm k A ⊆ iSm k B
  | 0 => Subset.rfl
  | k + 1 => Finset.add_subset_add (iSM h k) h
lemma iSA {G : Type*} [AddCommMonoid G] [DecidableEq G] (A : Finset G) (m : ℕ) :
    ∀ n : ℕ, iSm (m + n) A = iSm m A + iSm n A
  | 0 => by
      simp only [add_zero, iSm]
      ext x
      simp [Finset.mem_add]
  | n + 1 => by
      rw [← add_assoc, iSm, iSA A m n, iSm, add_assoc]
lemma iSS {G : Type*} [AddCommMonoid G] [DecidableEq G] {A : Finset G}
    (h0 : 0 ∈ A) {m n : ℕ} (hmn : m ≤ n) : iSm m A ⊆ iSm n A := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
  rw [iSA]
  intro x hx
  have := Finset.add_mem_add hx (zMI h0 k)
  simpa using this
def sS {G : Type*} [AddCommMonoid G] [DecidableEq G] (A : Finset G) : Finset G :=
  A.powerset.image (fun S => ∑ x ∈ S, x)
lemma zMSu {G : Type*} [AddCommMonoid G] [DecidableEq G] (A : Finset G) :
    (0 : G) ∈ sS A :=
  Finset.mem_image.mpr ⟨∅, Finset.empty_mem_powerset A, by simp⟩
lemma sUD {G : Type*} [AddCommMonoid G] [DecidableEq G] {A B : Finset G}
    (hd : Disjoint A B) : sS (A ∪ B) = sS A + sS B := by
  ext x
  simp only [sS, Finset.mem_image, Finset.mem_powerset, Finset.mem_add]
  constructor
  · rintro ⟨S, hS, rfl⟩
    refine ⟨∑ a ∈ S ∩ A, a, ⟨S ∩ A, inter_subset_right, rfl⟩,
            ∑ b ∈ S ∩ B, b, ⟨S ∩ B, inter_subset_right, rfl⟩, ?_⟩
    rw [← Finset.sum_union (hd.mono inter_subset_right inter_subset_right)]
    congr 1
    ext y
    simp only [mem_union, mem_inter]
    constructor
    · intro h; rcases h with ⟨hy, _⟩ | ⟨hy, _⟩ <;> exact hy
    · intro hy
      rcases mem_union.mp (hS hy) with hA | hB
      · exact Or.inl ⟨hy, hA⟩
      · exact Or.inr ⟨hy, hB⟩
  · rintro ⟨_, ⟨SA, hSA, rfl⟩, _, ⟨SB, hSB, rfl⟩, rfl⟩
    refine ⟨SA ∪ SB, Finset.union_subset_union hSA hSB, ?_⟩
    exact Finset.sum_union (hd.mono hSA hSB)
def NonAvg {G : Type*} [AddCommGroup G] [DecidableEq G] (A : Finset G) : Prop :=
  ∀ a ∈ A, ∀ T ⊆ A.erase a, 2 ≤ T.card → (∑ x ∈ T, x) ≠ (T.card : ℤ) • a
lemma NonAvg.subset {G : Type*} [AddCommGroup G] [DecidableEq G] {A B : Finset G}
    (hB : NonAvg B) (hAB : A ⊆ B) : NonAvg A := by
  intro a ha T hT hc
  exact hB a (hAB ha) T (hT.trans (Finset.erase_subset_erase a hAB)) hc
lemma NonAvg.translate {G : Type*} [AddCommGroup G] [DecidableEq G] {A : Finset G}
    (hA : NonAvg A) (t : G) : NonAvg (A.image (fun x => x + t)) := by
  intro b hb T hT hc heq
  obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hb
  have hTsub : T ⊆ A.image (fun x => x + t) := fun x hx => (Finset.mem_erase.mp (hT hx)).2
  obtain ⟨S, hSA, rfl⟩ := Finset.subset_image_iff.mp hTsub
  have hinj : Function.Injective (fun x : G => x + t) := add_left_injective t
  have hScard : (S.image (fun x => x + t)).card = S.card :=
    Finset.card_image_of_injective S hinj
  have hSerase : S ⊆ A.erase a := by
    intro x hx
    have hx' := Finset.mem_erase.mp (hT (Finset.mem_image_of_mem _ hx))
    exact Finset.mem_erase.mpr ⟨fun h => hx'.1 (congrArg (fun y => y + t) h), hSA hx⟩
  rw [hScard] at hc heq
  rw [Finset.sum_image (fun _ _ _ _ h => hinj h), Finset.sum_add_distrib,
    Finset.sum_const] at heq
  have hsum : ∑ x ∈ S, x = (S.card : ℤ) • a := by
    have h1 : (S.card : ℤ) • (a + t) = (S.card : ℤ) • a + (S.card : ℤ) • t := smul_add _ _ _
    rw [h1] at heq
    have h2 : (S.card : ℕ) • t = (S.card : ℤ) • t := by simp
    rw [h2] at heq
    exact add_right_cancel heq
  exact hA a ha S hSerase hc hsum
def DCP {d : ℕ} (δ : ℝ) (A : Finset (ZV d)) : Prop :=
  ∀ a ∈ A, ∃ u : RV d, u ≠ 0 ∧
    ((A.filter (fun x => (0 : ℝ) ≤ ∑ i : Fin d, u i * ((x i - a i : ℤ) : ℝ))).card : ℝ) ≤
      δ * (A.card : ℝ)
end E186
namespace E186
section
open Fin Submodule
open Nat (le_of_succ_le lt_succ_self le_succ one_le_pow pow_le_pow_right floor_le lt_floor_add_one)
def m1z (d:ℕ):ZV d →+ RV d:=⟨⟨zR,zR0 d⟩,zRa⟩
abbrev m1V {d:ℕ} (Γ:AddSubgroup (ZV d)) (B:Set (RV d)):=span ℝ (zR '' {x:ZV d|x ∈ Γ/\zR x ∈ B})
lemma m1d {d:ℕ} (G:AddSubgroup (ZV d)) (f:ZV d →+ ℤ) {x₀:ZV d} (hx:x₀ ∈ G) (h0:0 < f x₀):∃ u ∈ G,0 < f u/\∀ x ∈ G,f u∣f x:=by
 classical
 have hE:∃ n:ℕ,0 < n/\∃ u ∈ G,f u=n:=⟨(f x₀).toNat,by omega,x₀,hx,by omega⟩
 let m:=Nat.find hE;have ⟨hd,u,hu,hfu⟩:=Nat.find_spec hE
 refine ⟨u,hu,by omega,λ x hx=>⟨f x/m,?_⟩⟩
 have dz:(0:ℤ) < m:=by omega
 have rn:=Int.emod_nonneg (f x) dz.ne';have rl:=Int.emod_lt_of_pos (f x) dz
 have r0:f x % m=0:=by by_contra hn;refine Nat.find_min hE (show (f x % m).toNat < m by omega) ⟨by omega,x - (f x/m)•u,G.sub_mem hx (G.zsmul_mem hu _),?_⟩;rw [map_sub,map_zsmul,hfu,zsmul_eq_mul,Int.cast_id,Int.toNat_of_nonneg rn];linarith [Int.mul_ediv_add_emod (f x) m]
 rw [hfu];linarith [Int.mul_ediv_add_emod (f x) m]
theorem qpe {D:ℕ} (c:ZV (D+1)) (hc:c≠0):∃ (π:ZV (D+1) →+ ZV D) (c₀:ZV (D+1)),c₀≠0/\(∃ m:ℤ,m≠0/\m•c₀=c)/\Function.Surjective π/\(∀ x:ZV (D+1),π x=0↔∃ t:ℤ,t•c₀=x):=by
 let N:Submodule ℤ (ZV (D+1)):=span ℤ {c};obtain ⟨n,s⟩:=N.smithNormalForm (Pi.basisFun ℤ (Fin (D+1)))
 have h1:LinearIndependent ℤ (λ _:Unit=>c):=Fintype.linearIndependent_iff.mpr λ g hg _=>by rw [Fintype.sum_unique] at hg;exact (smul_eq_zero.mp hg).resolve_right hc
 obtain rfl:n=1:=by simpa using Fintype.card_congr (s.bN.indexEquiv ((Module.Basis.span h1).map (LinearEquiv.ofEq _ _ (by simp [N]))))
 let B:=s.bM;let i:=s.f 0;let u:=B i;let sa:=i.succAbove;let c':N:=⟨c,subset_span rfl⟩;let π:ZV (D+1) →+ ZV D:=⟨⟨λ x j=>B.repr x (sa j),by ext;simp⟩,λ _ _=>by ext;simp⟩
 have he:(s.bN.repr c' 0*s.a 0)•u=c:=by have h2:=congrArg Subtype.val (s.bN.sum_repr c');rw [sum_univ_one] at h2;simpa [s.snf 0,mul_smul,u,i,B,c'] using h2
 refine ⟨π,u,B.ne_zero i,⟨_,λ h0=>hc (by rw [← he,h0,zero_smul]),he⟩,λ y=>⟨∑ j:Fin D,y j•B (sa j),by ext j;dsimp [π];rw [map_sum,Finsupp.finsetSum_apply];simp only [map_zsmul];simp [Finsupp.single_apply,sa,succAbove_right_injective.eq_iff]⟩,λ x=>⟨λ hπ=>⟨B.repr x i,B.repr.injective (by
  ext k;rw [map_zsmul];by_cases hk:k=i
  · subst hk;simp [u]
  obtain ⟨j,rfl⟩:=exists_succAbove_eq hk;simpa [π,u,sa] using (congrFun hπ j).symm)⟩,
  λ ⟨t,h⟩=>by subst h;ext j;dsimp [π];rw [map_zsmul];simp [u,sa]⟩⟩
lemma m1q {m M:ℕ} (θ:Fin m->ℝ) (hM:1<=M):∃ (t:ℕ) (q:Fin m->ℤ),1<=t/\t<=M^m/\∀ j,|(t:ℝ)*θ j - q j| < 1/M:=by
 have hP:(0:ℝ) < M:=Nat.cast_pos.mpr hM
 let f:Fin (M^m+1)->Fin m->Fin M:=λ n j=>⟨⌊(M:ℝ)*Int.fract (n.1*θ j)⌋₊,by rw [Nat.floor_lt (mul_nonneg hP.le (Int.fract_nonneg _))];nlinarith [Int.fract_lt_one ((n.1:ℝ)*θ j)]⟩
 obtain ⟨a,b,h,hf⟩:=Fintype.exists_ne_map_eq_of_card_lt f (by simp [Fintype.card_pi])
 obtain ⟨x,y,hxy,he⟩:∃ x y,x.1 < y.1/\f x=f y:=(lt_or_gt_of_ne (val_ne_of_ne h)).elim (λ h=>⟨a,b,h,hf⟩) (λ h=>⟨b,a,h,hf.symm⟩)
 refine ⟨y.1 - x.1,λ j=>⌊(y.1:ℝ)*θ j⌋ - ⌊(x.1:ℝ)*θ j⌋,by omega,by omega,λ j=>?_⟩
 let F (n:ℕ):=(M:ℝ)*Int.fract (n*θ j);have hl:⌊F x.1⌋₊=⌊F y.1⌋₊:=by simpa [f,F] using congrArg (λ g=>(g j).1) he
 have Fn:∀ n,0<=F n:=λ _=>mul_nonneg hP.le (Int.fract_nonneg _)
 have hd:|F y.1 - F x.1| < 1:=by have q1:=floor_le (Fn y.1);have q2:=lt_floor_add_one (F y.1);rw [← hl] at q1 q2;rw [abs_lt];constructor <;> linarith [floor_le (Fn x.1),lt_floor_add_one (F x.1)]
 rw [show ((y.1 - x.1:ℕ):ℝ)*θ j - ((⌊(y.1:ℝ)*θ j⌋ - ⌊(x.1:ℝ)*θ j⌋:ℤ):ℝ)=Int.fract (y.1*θ j) - Int.fract (x.1*θ j) by rw [Nat.cast_sub hxy.le,Int.cast_sub,← Int.self_sub_floor,← Int.self_sub_floor];ring,lt_div_iff₀ hP];dsimp [F] at hd;rw [← mul_sub,abs_mul,abs_of_pos hP] at hd;linarith
lemma m12 (n:ℕ):∑ j:Fin n,(2:ℝ)^j.1=2^n - 1:=by rw [sum_univ_eq_sum_range (λ r=>(2:ℝ)^r),geom_sum_eq (by norm_num:(2:ℝ)≠1) n];norm_num
def m1S {d k:ℕ} (v:Fin k->ZV d) (m:ℕ):Submodule ℝ (RV d):=span ℝ ((λ j=>zR (v j)) '' {j:Fin k|j.1 < m})
lemma m1L {d m:ℕ} (v':Fin m->ZV d) (vm:ZV d) {r:ℕ} (hr:r<=m):m1S (snoc v' vm) r=m1S v' r:=by unfold m1S;congr 1;ext y;simp only [Set.mem_image,Set.mem_ofPred_eq];exact ⟨λ ⟨j,hj,h⟩=>h ▸ lastCases (λ h=>absurd h (not_lt_of_ge hr)) (λ j' hj'=>⟨j',hj',by simp⟩) j hj,λ ⟨j,hj,h⟩=>⟨j.castSucc,hj,by simpa using h⟩⟩
section
variable {d k:ℕ} (v:Fin k->ZV d)
lemma m1M {a b:ℕ} (h:a<=b):m1S v a<=m1S v b:=span_mono (Set.image_mono λ _ hj=>lt_of_lt_of_le hj h)
lemma m1F:m1S v k=span ℝ (Set.range λ j:Fin k=>zR (v j)):=by unfold m1S;congr 1;ext;simp
lemma m1Z {j:Fin k} {m:ℕ} (h:j.1 < m):zR (v j) ∈ m1S v m:=subset_span ⟨j,h,rfl⟩
lemma m1N (hli:LinearIndependent ℝ (λ i=>zR (v i))) (i:Fin k):zR (v i) ∉ m1S v i.1:=λ h=>(linearIndependent_iff_notMem_span.mp hli) i (span_mono (Set.image_mono λ j hj=>show j ∈ Set.univ \ {i} from ⟨trivial,λ he=>Nat.lt_irrefl _ (Set.mem_singleton_iff.mp he ▸ hj)⟩) h)
lemma m1I (hn:∀ i,zR (v i) ∉ m1S v i.1):LinearIndependent ℝ (λ i=>zR (v i)):=by
 classical
 rw [Fintype.linearIndependent_iff];intro g hg;by_contra hne;push Not at hne
 let S:=univ.filter (g ·≠0);have hS:S.Nonempty:=let ⟨i,hi⟩:=hne;⟨i,by simp [S,hi]⟩
 let i:=S.max' hS;have hgi:g i≠0:=(mem_filter.mp (max'_mem S hS)).2
 rw [show ∑ j,g j•zR (v j)=g i•zR (v i)+∑ j ∈ univ.filter (· < i),g j•zR (v j) by rw [← sum_subset (filter_subset (·<=i) univ) λ j _ h=>by simp [show g j=0 from by_contra λ h0=>not_le_of_gt (not_le.mp λ h1=>h (mem_filter.mpr ⟨mem_univ j,h1⟩)) (le_max' S j (mem_filter.mpr ⟨mem_univ j,h0⟩))],show univ.filter (·<=i)=insert i (univ.filter (· < i)) by ext j;simp [le_iff_eq_or_lt],sum_insert (by simp)]] at hg
 refine hn i ?_;rw [show zR (v i)=(g i)⁻¹•-(∑ j ∈ univ.filter (· < i),g j•zR (v j)) by rw [← eq_neg_of_add_eq_zero_left hg,inv_smul_smul₀ hgi]]
 exact smul_mem _ _ (neg_mem (sum_mem λ j hj=>smul_mem _ _ (m1Z v (mem_filter.mp hj).2)))
lemma m1f {m:ℕ} (hm:m+1<=k) (hli:LinearIndependent ℝ (λ i=>zR (v i))):∃ ψ:ZV d →+ ℤ,0 < ψ (v ⟨m,hm⟩)/\∀ x,zR x ∈ m1S v (m+1)->(ψ x=0↔zR x ∈ m1S v m):=by
 let zq (x:ZV d):Fin d->ℚ:=λ r=>(x r:ℚ);let qr (y:Fin d->ℚ):RV d:=λ r=>(y r:ℝ);let p:=span ℚ ((λ j=>zq (v j)) '' {j:Fin k|j.1 < m})
 have hqr:∀ x,qr (zq x)=zR x:=λ _=>by ext;simp [qr,zq,zR]
 have hnm:zq (v ⟨m,hm⟩) ∉ p:=λ h=>m1N v hli ⟨m,hm⟩ (hqr _ ▸ span_induction (p:=λ y _=>qr y ∈ m1S v m) (λ _ hy=>by obtain ⟨j,hj,rfl⟩:=hy;rw [hqr];exact m1Z v hj) ((show qr 0=0 by ext;simp [qr]) ▸ Submodule.zero_mem _) (λ x y _ _ a b=>(show qr (x+y)=qr x+qr y by ext;simp [qr]) ▸ add_mem a b) (λ c x _ b=>(show qr (c•x)=(c:ℝ)•qr x by ext;simp [qr]) ▸ smul_mem _ (c:ℝ) b) h)
 obtain ⟨φ,hφp,hφ1⟩:=LinearMap.exists_extend_of_notMem (0:p →ₗ[ℚ] ℚ) hnm 1
 let q (r:Fin d):=φ (Pi.single r 1);let D:ℕ:=∏ r,(q r).den;have hD:0 < D:=prod_pos λ r _=>(q r).den_pos
 let a:ZV d:=λ r=>((D/(q r).den:ℕ):ℤ)*(q r).num;let ψ:ZV d →+ ℤ:=⟨⟨λ x=>∑ r,x r*a r,by simp⟩,λ _ _=>by simp [add_mul,sum_add_distrib]⟩
 let ψR:=Fintype.linearCombination ℝ λ r=>(a r:ℝ);have hc:∀ x,(ψ x:ℝ)=ψR (zR x):=λ _=>by simp [ψ,ψR,Fintype.linearCombination_apply,zR]
 have hd:∀ x,ψR (zR x)=D*(φ (zq x):ℝ):=λ x=>by
  have h1:∑ r:Fin d,(x r:ℚ)*a r=D*φ (zq x):=by
   rw [show zq x=∑ r,(x r:ℚ)•Pi.single r 1 by ext r;simp [zq,Pi.single_apply],map_sum,mul_sum]
   refine sum_congr rfl λ r _=>?_;let kr:ℕ:=D/(q r).den;have hm:(kr:ℚ)*(q r).den=D:=by exact_mod_cast Nat.div_mul_cancel (dvd_prod_of_mem _ (mem_univ r))
   rw [map_smul,smul_eq_mul];change (x r:ℚ)*((kr:ℤ)*(q r).num:ℤ)=D*((x r:ℚ)*q r);push_cast;rw [← Rat.mul_den_eq_num];linear_combination ((x r:ℚ)*q r)*hm
  simpa [ψR,Fintype.linearCombination_apply,zR] using congrArg ((↑):ℚ->ℝ) h1
 have hp:∀ y ∈ m1S v m,ψR y=0:=λ y hy=>span_induction (λ _ ⟨j,hj,h⟩=>by rw [← h];dsimp;rw [hd,show φ (zq (v j))=0 by simpa using LinearMap.congr_fun hφp ⟨_,subset_span ⟨j,hj,rfl⟩⟩];simp) (by simp) (λ _ _ _ _ a b=>by simp [a,b]) (λ _ _ _ a=>by simp [a]) hy
 refine ⟨ψ,by exact_mod_cast (show (0:ℝ) < ψ (v ⟨m,hm⟩) by rw [hc,hd,hφ1];simp;exact_mod_cast hD),λ x hx=>⟨λ h0=>?_,λ hx'=>by exact_mod_cast (by rw [hc];exact hp _ hx':(ψ x:ℝ)=0)⟩⟩
 have hsp:m1S v (m+1)<=m1S v m ⊔ span ℝ {zR (v ⟨m,hm⟩)}:=span_le.mpr λ _ ⟨j,hj,h⟩=>by
  rw [← h];dsimp;change j.1 < m+1 at hj;by_cases h1:j.1 < m
  · exact mem_sup_left (m1Z v h1)
  exact mem_sup_right (subset_span (show zR (v j)=zR (v ⟨m,hm⟩) by congr 2;ext;dsimp;omega))
 obtain ⟨y,hy,z,hz,he⟩:=mem_sup.mp (hsp hx);obtain ⟨t,rfl⟩:=mem_span_singleton.mp hz;have h1:ψR (zR x)=0:=by rw [← hc,h0];simp
 rw [← he,map_add,map_smul,hp y hy,zero_add,smul_eq_mul,hd,hφ1] at h1
 rw [← he,(mul_eq_zero.mp (by simpa using h1:t*D=0)).resolve_right (Nat.cast_ne_zero.mpr hD.ne'),zero_smul,add_zero];exact hy
end
section
variable {d:ℕ} {B:Set (RV d)}
lemma m1c (hcv:Convex ℝ B) {r s:ℝ} {x y:RV d} (hr:0 < r) (hs:0 < s) (hx:x ∈ r•B) (hy:y ∈ s•B):x+y ∈ (r+s)•B:=by obtain ⟨a,ha,rfl⟩:=hx;obtain ⟨b,hb,rfl⟩:=hy;have hrs:=add_pos hr hs;exact ⟨(r/(r+s))•a+(s/(r+s))•b,hcv ha hb (div_nonneg hr.le hrs.le) (div_nonneg hs.le hrs.le) (by rw [← add_div,div_self hrs.ne']),by dsimp;rw [smul_add,smul_smul,smul_smul,mul_div_cancel₀ _ hrs.ne',mul_div_cancel₀ _ hrs.ne']⟩
lemma m1g (hsy:∀ x ∈ B,-x ∈ B) (a:ℝ) (x:RV d):gauge B (a•x)=|a| *gauge B x:=(le_total 0 a).elim (λ ha=>by rw [abs_of_nonneg ha];exact gauge_smul_of_nonneg ha x) λ ha=>by rw [abs_of_nonpos ha,show a•x=(-a)•(-x) by rw [smul_neg,neg_smul,neg_neg],gauge_smul_of_nonneg (neg_nonneg.mpr ha),gauge_neg hsy];rfl
variable (h0:(0:RV d) ∈ B) (hcv:Convex ℝ B)
section
include h0 hcv
lemma m1m {x:RV d} (ha:∃ r:ℝ,0 < r/\x ∈ r•B) {t:ℝ} (ht:gauge B x < t):x ∈ t•B:=by obtain ⟨r,⟨hr,b,hb,rfl⟩,hrt⟩:=exists_lt_of_csInf_lt ha ht;have ht0:=hr.trans hrt;exact ⟨(r/t)•b+(1 - r/t)•0,hcv hb h0 (div_nonneg hr.le ht0.le) (sub_nonneg.mpr ((div_le_one ht0).mpr hrt.le)) (by ring),by simp [smul_smul,mul_div_cancel₀ _ ht0.ne']⟩
lemma m1a {x y:RV d} (hx:∃ r:ℝ,0 < r/\x ∈ r•B) (hy:∃ r:ℝ,0 < r/\y ∈ r•B):gauge B (x+y)<=gauge B x+gauge B y:=le_of_forall_pos_le_add λ ε hε=>by
 have hr:0 < gauge B x+ε/2:=by linarith [gauge_nonneg (s:=B) x]
 have hs:0 < gauge B y+ε/2:=by linarith [gauge_nonneg (s:=B) y]
 linarith [gauge_le_of_mem (add_pos hr hs).le (m1c hcv hr hs (m1m h0 hcv hx (by linarith:gauge B x < gauge B x+ε/2)) (m1m h0 hcv hy (by linarith:gauge B y < gauge B y+ε/2)))]
lemma m1u (Γ:AddSubgroup (ZV d)) {C:ℝ} (hC:B ⊆ Metric.closedBall 0 C) (hVa:∀ y ∈ m1V Γ B,∃ r:ℝ,0 < r/\y ∈ r•B):let L:=Γ ⊓ (m1V Γ B).toAddSubgroup.comap (m1z d);∀ m ≤ Module.finrank ℝ (m1V Γ B),∃ v:Fin m->ZV d,(∀ i,v i ∈ L)/\(∀ i,zR (v i) ∉ m1S v i.1)/\∀ i,∀ x ∈ L,zR x ∉ m1S v i.1->gauge B (zR (v i))<=gauge B (zR x):=by
 classical
 intro L;let g (x:ZV d):=gauge B (zR x);let K:=⌈2*max C 0⌉₊
 have hK:∀ x,(∃ r:ℝ,0 < r/\zR x ∈ r•B)->g x<=1->x ∈ (ZB.symm λ _=>K).tF:=λ x ha hg=>(ZB.mTF _ _).mpr λ i=>abs_le.mp (by
  obtain ⟨b,hb,he⟩:=m1m h0 hcv ha (by dsimp [g] at hg;linarith:gauge B (zR x) < 2)
  have hn:‖zR x‖<=2*max C 0:=by dsimp at he;rw [← he,norm_smul,Real.norm_of_nonneg (by norm_num)];linarith [le_trans (mem_closedBall_zero_iff.mp (hC hb)) (le_max_left C 0)]
  have h2:=norm_le_pi_norm (zR x) i;simp [zR] at h2;exact_mod_cast (by rw [Int.cast_abs,Int.cast_natCast];dsimp [K];linarith [Nat.le_ceil (2*max C 0)]:((|x i|:ℤ):ℝ)<=((K:ℤ):ℝ)))
 intro m;induction m with
 | zero=>exact λ _=>⟨elim0,λ i=>i.elim0,λ i=>i.elim0,λ i=>i.elim0⟩
 | succ m ih =>
 intro hm;obtain ⟨v',vL,vn,vm⟩:=ih (le_of_succ_le hm);let W:=m1S v' m
 obtain ⟨x₀,x1,x2,xW⟩:∃ x,x ∈ Γ/\zR x ∈ B/\zR x ∉ W:=by
  by_contra ha;push Not at ha;have h1:Module.finrank ℝ (m1V Γ B)<=Module.finrank ℝ W:=finrank_mono (span_le.mpr (by rintro _ ⟨x,⟨h1,h2⟩,rfl⟩;exact ha x h1 h2))
  have h2:Module.finrank ℝ W<=m:=by rw [show W=span ℝ (Set.range λ j:Fin m=>zR (v' j)) from m1F v'];exact (finrank_span_le_card _).trans (by simpa using card_image_le (s:=univ) (f:=λ j:Fin m=>zR (v' j)))
  omega
 have xL:x₀ ∈ L:=⟨x1,subset_span ⟨x₀,⟨x1,x2⟩,rfl⟩⟩;let F:=(ZB.symm λ _:Fin d=>K).tF.filter (λ x=>x ∈ L/\zR x ∉ W/\g x<=1)
 obtain ⟨u,uF,uM⟩:=F.exists_min_image g ⟨x₀,mem_filter.mpr ⟨hK x₀ (hVa _ xL.2) (gauge_le_one_of_mem x2),xL,xW,gauge_le_one_of_mem x2⟩⟩
 have up:=(mem_filter.mp uF).2;let v:Fin (m+1)->ZV d:=snoc v' u;have pl:∀ r ≤ m,m1S v r=m1S v' r:=λ _ hr=>m1L v' u hr
 refine ⟨v,lastCases (by simpa [v] using up.1) λ j=>by simpa [v] using vL j,lastCases (by rw [val_last,pl m le_rfl];simpa [v] using up.2.1) λ j=>by rw [val_castSucc,pl j.1 j.2.le];simpa [v] using vn j,lastCases (λ x hL hn=>by
  rw [val_last,pl m le_rfl] at hn;simp [v];by_cases hg:g x<=1
  · exact uM x (mem_filter.mpr ⟨hK x (hVa _ hL.2) hg,hL,hn,hg⟩)
  exact le_trans up.2.2 (le_of_not_ge hg)) λ j x hL hn=>by rw [val_castSucc,pl j.1 j.2.le] at hn;simpa [v] using vm j x hL hn⟩
end
variable (hsy:∀ x ∈ B,-x ∈ B)
include h0 hcv hsy
lemma m1l {V:Submodule ℝ (RV d)} (hV:∀ x ∈ V,∃ r:ℝ,0 < r/\x ∈ r•B) {ι:Type*} (s:Finset ι) (a:ι->ℝ) (f:ι->RV d) (hf:∀ i ∈ s,f i ∈ V):gauge B (∑ i ∈ s,a i•f i)<=∑ i ∈ s,|a i| *gauge B (f i):=by
 classical
 induction s using Finset.induction_on with
 | empty=>simp [gauge_zero]
 | insert x s hx ih =>
 rw [sum_insert hx,sum_insert hx];have hfs:=λ i hi=>hf i (mem_insert_of_mem hi);have h1:=m1a h0 hcv (hV _ (smul_mem V (a x) (hf x (mem_insert_self x s)))) (hV _ (sum_mem λ i hi=>smul_mem V (a i) (hfs i hi)));rw [m1g hsy] at h1;linarith [ih hfs]
lemma m1b {k:ℕ} (L:AddSubgroup (ZV d)) {V:Submodule ℝ (RV d)} (hVa:∀ y ∈ V,∃ r:ℝ,0 < r/\y ∈ r•B) (hLV:∀ x ∈ L,zR x ∈ V) (v:Fin k->ZV d) (hvL:∀ i,v i ∈ L)
 (hvli:LinearIndependent ℝ (λ i=>zR (v i))) (hvm:∀ i j:Fin k,i<=j->gauge B (zR (v i))<=gauge B (zR (v j))):
 ∀ m (hm:m<=k),∃ b:Fin m->ZV d,(∀ i,b i ∈ L)/\LinearIndependent ℝ (λ i=>zR (b i))/\(∀ r ≤ m,m1S b r=m1S v r)/\(∀ x ∈ L,zR x ∈ m1S v m->∃ c:ZV m,∑ i,c i•b i=x)/\∀ i:Fin m,gauge B (zR (b i))<=(2:ℝ)^i.1*gauge B (zR (v ⟨i.1,lt_of_lt_of_le i.2 hm⟩)):=by
 classical
 let g (x:ZV d):=gauge B (zR x);intro m;induction m with
 | zero=>exact λ _=>⟨elim0,λ i=>i.elim0,linearIndependent_empty_type,λ r hr=>by rw [Nat.eq_zero_of_le_zero hr];simp [m1S],λ x _ hx=>by simp [m1S] at hx;exact ⟨elim0,by simp [zRi d (hx.trans (zR0 d).symm)]⟩,λ i=>i.elim0⟩
 | succ m ih =>
 intro hm;obtain ⟨b',hL,hbl,hs,hg,hd⟩:=ih (le_of_succ_le hm);let w:=v ⟨m,hm⟩;have h0s:=hs m le_rfl;have hwL:=hvL ⟨m,hm⟩;have hwS:=m1Z v (j:=⟨m,hm⟩) (lt_succ_self m);have hbj:∀ j:Fin m,zR (b' j) ∈ m1S v m:=λ j=>h0s ▸ m1Z b' j.2
 obtain ⟨ψ,h0',hk0⟩:=m1f v hm hvli
 have hk:∀ x y (t:ℤ),zR x ∈ m1S v (m+1)->zR y ∈ m1S v (m+1)->ψ x=t*ψ y->zR (x - t•y) ∈ m1S v m:=λ x y t hx hy h=>(hk0 _ (by rw [zRs,zRm];exact sub_mem hx (smul_mem _ _ hy))).mp (by rw [map_sub,map_zsmul,zsmul_eq_mul,Int.cast_id];linarith)
 obtain ⟨u,⟨h1,h2⟩,hu0,hdv⟩:=m1d (L ⊓ (m1S v (m+1)).toAddSubgroup.comap (m1z d)) ψ ⟨hwL,hwS⟩ h0'
 obtain ⟨q,hq⟩:=hdv w ⟨hwL,hwS⟩;have hq0:0 < q:=by nlinarith
 obtain ⟨a,ha⟩:=hg (w - q•u) (L.sub_mem hwL (L.zsmul_mem h1 q)) (hk w u q hwS h2 (by linarith))
 obtain ⟨bm,hbL,hbS,hψb,hbg⟩:∃ bm,bm ∈ L/\zR bm ∈ m1S v (m+1)/\ψ bm=ψ u/\g bm<=(2:ℝ)^m*g w:=by
  by_cases hq1:q=1
  · refine ⟨w,hwL,hwS,by rw [hq,hq1,mul_one],?_⟩;have:(1:ℝ)<=2^m:=one_le_pow₀ (by norm_num);dsimp [g];nlinarith [gauge_nonneg (s:=B) (zR w)]
  let θ (j:Fin m):ℝ:=-(a j:ℝ)/q;let r j:=round (θ j);let w':=u - ∑ j,r j•b' j
  refine ⟨w',L.sub_mem h1 (L.sum_mem λ j _=>L.zsmul_mem (hL j) _),by rw [zRs,zRu];exact Submodule.sub_mem _ h2 (sum_mem λ j _=>by rw [zRm];exact smul_mem _ _ (m1M v (le_succ m) (hbj j))),by rw [map_sub,map_sum,sum_eq_zero λ j _=>by rw [map_zsmul,zsmul_eq_mul,(hk0 _ (m1M v (le_succ m) (hbj j))).mpr (hbj j),mul_zero],sub_zero],?_⟩
  have hq2:(2:ℝ)<=q:=by exact_mod_cast (show (2:ℤ)<=q by omega)
  have hqp:(0:ℝ) < q:=by linarith
  have hdc:zR w'=(q:ℝ)⁻¹•zR w+∑ j,(θ j - r j)•zR (b' j):=by
   have h3:∑ j,(a j:ℝ)•zR (b' j)=zR w - (q:ℝ)•zR u:=by have h:=congrArg zR ha;rw [zRu,zRs,zRm] at h;simp only [zRm] at h;exact h
   have h4:∑ j,(q:ℝ)•((θ j - r j)•zR (b' j))=-(∑ j,(a j:ℝ)•zR (b' j)) - ∑ j,(q:ℝ)•((r j:ℝ)•zR (b' j)):=by rw [← sum_neg_distrib,← sum_sub_distrib];exact sum_congr rfl λ j _=>by rw [smul_smul,smul_smul,← neg_smul,← sub_smul];congr 1;dsimp [θ];field_simp [hqp.ne']
   exact smul_right_injective _ hqp.ne' (by dsimp;rw [smul_add,smul_smul,mul_inv_cancel₀ hqp.ne',one_smul,smul_sum,h4,h3];dsimp [w'];rw [zRs,zRu,smul_sub,smul_sum];simp only [zRm];abel)
  dsimp [g];rw [hdc];refine le_trans (le_trans (m1a h0 hcv (hVa _ (smul_mem V _ (hLV w hwL))) (hVa _ (sum_mem λ j _=>smul_mem V _ (hLV _ (hL j))))) (add_le_add le_rfl (m1l h0 hcv hsy hVa _ _ _ λ j _=>hLV _ (hL j)))) ?_
  have t1:gauge B ((q:ℝ)⁻¹•zR w)<=(1/2)*g w:=by rw [m1g hsy,abs_of_pos (inv_pos.mpr hqp),← one_div];exact mul_le_mul_of_nonneg_right (by gcongr) (gauge_nonneg _)
  have t2:∑ j:Fin m,|θ j - r j| *g (b' j)<=((1/2)*((2:ℝ)^m - 1))*g w:=calc
   _<=∑ j:Fin m,(1/2)*((2:ℝ)^j.1*g w):=sum_le_sum λ j _=>mul_le_mul (abs_sub_round _) ((hd j).trans (by gcongr;exact hvm _ ⟨m,hm⟩ (mk_le_mk.mpr j.2.le))) (gauge_nonneg _) (by norm_num)
   _=(1/2)*(∑ j:Fin m,(2:ℝ)^j.1)*g w:=by simp [mul_sum,sum_mul,mul_assoc]
   _=_:=by rw [m12]
  dsimp [g] at t1 t2;nlinarith [gauge_nonneg (s:=B) (zR w),(by positivity:(0:ℝ)<=2^m)]
 let b:Fin (m+1)->ZV d:=snoc b' bm;have e0:=m1L b' bm le_rfl
 refine ⟨b,lastCases (by simpa [b] using hbL) λ j=>by simpa [b] using hL j,m1I b (lastCases (by rw [val_last,e0,h0s];simpa [b] using λ h=>hu0.ne' (hψb ▸ (hk0 _ hbS).mpr h)) λ j=>by rw [val_castSucc,m1L b' bm j.2.le];simpa [b] using m1N b' hbl j),?_,?_,lastCases (by simpa [b,w] using hbg) λ j=>by simpa [b] using hd j⟩
 · intro r hr;by_cases h:r<=m
   · rw [m1L b' bm h,hs r h]
   obtain rfl:r=m+1:=by omega
   refine le_antisymm (span_le.mpr ?_) (span_le.mpr ?_)
   · rintro _ ⟨j,_,rfl⟩;exact lastCases (by simpa [b] using hbS) (λ j'=>by simp [b];exact m1M v (le_succ m) (hbj j')) j
   rintro _ ⟨j,hj,rfl⟩;change j.1 < m+1 at hj;by_cases hl:j.1 < m
   · exact m1M b (le_succ m) (e0 ▸ h0s.symm ▸ m1Z v hl)
   obtain rfl:j=⟨m,hm⟩:=Fin.ext (by dsimp;omega);have h3:=hk w bm q hwS hbS (by rw [hψb];linarith)
   dsimp;rw [show zR (v ⟨m,hm⟩)=zR (w - q•bm)+(q:ℝ)•zR bm by rw [zRs,zRm,sub_add_cancel]]
   exact add_mem (m1M b (le_succ m) (e0 ▸ h0s ▸ h3)) (smul_mem _ _ (by simpa [b] using m1Z b (j:=last m) (lt_succ_self m)))
 intro x xL xS;obtain ⟨t,ht⟩:=hdv x ⟨xL,xS⟩;obtain ⟨c',hc'⟩:=hg _ (L.sub_mem xL (L.zsmul_mem hbL t)) (hk x bm t xS hbS (by rw [hψb];linarith));exact ⟨snoc c' t,by rw [sum_univ_castSucc];simp only [b,snoc_castSucc,snoc_last,hc',sub_add_cancel]⟩
end
def jC (d:ℕ):ℕ:=(2*(d+1)*2^(d^2+d))^(d+1)
lemma johnConst_pos (d:ℕ):1<=jC d:=Nat.succ_le_of_lt (by dsimp [jC];positivity)
theorem djs {d:ℕ} (Γ:AddSubgroup (ZV d)) (B:Set (RV d)) (h0:(0:RV d) ∈ B) (hconv:Convex ℝ B) (hsymm:∀ x ∈ B,-x ∈ B) (hbdd:Bornology.IsBounded B):
 ∃ (k:ℕ) (_:k<=d) (w:Fin k->ZV d) (N:Fin k->ℕ),(∀ i,w i ∈ Γ)/\(∀ i,1<=N i)/\LinearIndependent ℝ (λ i=>zR (w i))/\(∀ c:ZV k,(∀ i,|c i| < (N i:ℤ))->zR (∑ i,c i•w i) ∈ B)/\(∀ x:ZV d,x ∈ Γ->zR x ∈ B->∃ c:ZV k,(∀ i,|c i| < (jC d*N i:ℤ))/\∑ i,c i•w i=x):=by
 classical
 let V:=m1V Γ B;let k:=Module.finrank ℝ V;have hkd:k<=d:=le_trans (finrank_le V) (by simp)
 by_cases hk0:k=0
 · refine ⟨0,by omega,elim0,elim0,λ i=>i.elim0,λ i=>i.elim0,linearIndependent_empty_type,λ _ _=>by simpa [zR0] using h0,λ x h1 h2=>?_⟩
   have h3:zR x ∈ V:=subset_span ⟨x,⟨h1,h2⟩,rfl⟩;rw [finrank_eq_zero.mp hk0,Submodule.mem_bot] at h3;exact ⟨elim0,λ i=>i.elim0,by simp [zRi d (h3.trans (zR0 d).symm)]⟩
 have hkR:(0:ℝ) < k:=by exact_mod_cast (show 1<=k by omega)
 let L:=Γ ⊓ V.toAddSubgroup.comap (m1z d);let g (x:ZV d):=gauge B (zR x)
 have hV:∀ x ∈ V,∃ r:ℝ,0 < r/\x ∈ r•B:=λ _ hx=>span_induction (λ _ ⟨_,⟨_,h⟩,he⟩=>⟨1,zero_lt_one,by simpa [← he] using h⟩) ⟨1,zero_lt_one,by simpa using h0⟩ (λ _ _ _ _ ⟨r,hr,hy⟩ ⟨s,hs,hz⟩=>⟨r+s,add_pos hr hs,m1c hconv hr hs hy hz⟩) (λ a _ _ ⟨r,hr,hy⟩=>by
  obtain ⟨b,hb,rfl⟩:=Set.mem_smul_set.mp hy;rcases lt_trichotomy a 0 with ha|rfl|ha
  · exact ⟨(-a)*r,mul_pos (neg_pos.mpr ha) hr,⟨-b,hsymm b hb,by dsimp;rw [smul_neg,← neg_smul,neg_mul,neg_neg,mul_smul]⟩⟩
  · exact ⟨1,zero_lt_one,by simpa using h0⟩
  exact ⟨a*r,mul_pos ha hr,⟨b,hb,by dsimp;rw [mul_smul]⟩⟩) hx
 have hL:∀ x ∈ L,zR x ∈ V:=λ _ h=>h.2;obtain ⟨C,hC⟩:=hbdd.subset_closedBall (0:RV d)
 obtain ⟨v,vL,vn,vm⟩:=m1u h0 hconv Γ hC hV k le_rfl;have vi:=m1I v vn
 have vo:∀ i j:Fin k,i<=j->g (v i)<=g (v j):=λ i j h=>vm i (v j) (vL j) λ hm=>vn j (m1M v h hm)
 have vV:m1S v k=V:=eq_of_le_of_finrank_eq (span_le.mpr λ _ ⟨j,_,hy⟩=>hy ▸ hL (v j) (vL j)) (by rw [m1F,finrank_span_eq_card vi,Fintype.card_fin])
 obtain ⟨b,bL,bi,bs,bg,bd⟩:=m1b h0 hconv hsymm L hV hL v vL vi vo k le_rfl
 have Ls:∀ (s:Finset (Fin k)) (a:ZV k),∑ j ∈ s,a j•b j ∈ L:=λ _ _=>L.sum_mem λ _ _=>L.zsmul_mem (bL _) _
 have lp:∀ i:Fin k,0 < g (v i):=λ i=>by let C':=max C 1;have hC':0 < C':=lt_max_of_lt_right zero_lt_one;refine lt_of_lt_of_le (div_pos (norm_pos_iff.mpr λ hz:zR (v i)=0=>vn i (hz ▸ Submodule.zero_mem _)) hC') (le_csInf (hV _ (hL (v i) (vL i))) ?_);rintro r ⟨hr,y,hy,hyE⟩;have h1:‖y‖<=C':=le_trans (mem_closedBall_zero_iff.mp (hC hy)) (le_max_left _ _);rw [← hyE,norm_smul,Real.norm_of_nonneg hr.le,div_le_iff₀ hC'];nlinarith
 let s (i:Fin k):ℝ:=2*(k:ℝ)*(2:ℝ)^i.1*g (v i);let ρ i:=1/s i;let N i:=⌊ρ i⌋₊+1;have sp:∀ i,0 < s i:=λ i=>by have:=lp i;dsimp [s];positivity
 refine ⟨k,hkd,b,N,λ i=>(bL i).1,λ _=>Nat.succ_pos _,bi,?_,?_⟩
 · intro c hc;have hlt:g (∑ i,c i•b i) < 1:=by
    dsimp [g];rw [zRu];simp only [zRm];calc
     gauge B (∑ i,(c i:ℝ)•zR (b i))<=∑ i,|(c i:ℝ)| *g (b i):=m1l h0 hconv hsymm hV _ _ _ λ i _=>hL _ (bL i)
     _<=∑ _i:Fin k,(1/(2*(k:ℝ))):=sum_le_sum λ i _=>by
      have ci:|(c i:ℝ)|<=ρ i:=le_trans (by rw [← Int.cast_abs];exact_mod_cast (show |c i|<=⌊ρ i⌋₊ by have:=hc i;dsimp [N] at this;omega)) (floor_le (div_nonneg zero_le_one (sp i).le))
      calc |(c i:ℝ)| *g (b i)<=ρ i*((2:ℝ)^i.1*g (v i)):=mul_le_mul ci (bd i) (gauge_nonneg _) (div_nonneg zero_le_one (sp i).le)
       _=1/(2*(k:ℝ)):=by dsimp [ρ,s];field_simp [(by positivity:((2:ℝ)^i.1)≠0),(lp i).ne']
     _=1/2:=by rw [Fin.sum_const,nsmul_eq_mul];field_simp [hkR.ne']
     _ < 1:=by norm_num
   simpa using m1m h0 hconv (hV _ (hL _ (Ls univ c))) hlt
 intro x h1 h2;have hV':zR x ∈ V:=subset_span ⟨x,⟨h1,h2⟩,rfl⟩;obtain ⟨c,hc⟩:=bg x ⟨h1,hV'⟩ (vV.symm ▸ hV');let R:=2*(k+1)*2^(k^2+k)
 have R1:(1:ℝ)<=R:=by exact_mod_cast (Nat.succ_le_of_lt (by positivity):1<=R)
 have bk:∀ r (i:Fin k),k - 1 - i.1<=r->|(c i:ℝ)| *g (v i)<=(R:ℝ)^(r+1):=by
  intro r;induction r using Nat.strong_induction_on with
  | h r ihr =>
  intro i hi;by_cases c0:c i=0
  · simp [c0]
  let G:ℝ:=((k+1:ℕ):ℝ)*(2:ℝ)^k*(R:ℝ)^r;let S:=univ.filter (i < ·);let y:=∑ j ∈ univ.filter (·<=i),c j•b j
  have sp':y=x - ∑ j ∈ S,c j•b j:=eq_sub_of_add_eq (by rw [← sum_union (disjoint_filter.mpr λ _ _ a b=>not_lt_of_ge a b),← hc];congr 1;ext j;simp [le_or_gt])
  have bG:g y<=G:=by
   dsimp [g];rw [sp',zRs,sub_eq_add_neg];have f1:=m1a h0 hconv (hV _ hV') (hV _ (neg_mem (hL _ (Ls S c))));rw [gauge_neg hsymm,zRu] at f1;simp only [zRm] at f1
   have f2:=m1l h0 hconv hsymm hV S (λ j=>(c j:ℝ)) (λ j=>zR (b j)) λ j _=>hL _ (bL j)
   have sl:∑ j ∈ S,|(c j:ℝ)| *g (b j)<=(k:ℝ)*((2:ℝ)^k*(R:ℝ)^r):=calc
    _<=∑ _j ∈ S,(2:ℝ)^k*(R:ℝ)^r:=sum_le_sum λ j hj=>by
     have:i.1 < j.1:=(mem_filter.mp hj).2;have cj:=(ihr (k - 1 - j.1) (by omega) j le_rfl).trans (pow_le_pow_right₀ R1 (by omega:_<=r));have:0<=g (v j):=gauge_nonneg _
     calc |(c j:ℝ)| *g (b j)<=|(c j:ℝ)| *((2:ℝ)^j.1*g (v j)):=by gcongr;exact bd j
      _=(2:ℝ)^j.1*(|(c j:ℝ)| *g (v j)):=by ring
      _<=(2:ℝ)^k*(R:ℝ)^r:=by gcongr;norm_num;exact j.2.le
    _<=(k:ℝ)*((2:ℝ)^k*(R:ℝ)^r):=by rw [Finset.sum_const,nsmul_eq_mul];gcongr;exact_mod_cast (card_filter_le _ _).trans_eq (by simp)
   dsimp [g] at sl;rw [zRu];simp only [zRm];dsimp [G];push_cast;nlinarith [gauge_le_one_of_mem h2,(one_le_pow₀ (by norm_num):(1:ℝ)<=2^k),(one_le_pow₀ R1:(1:ℝ)<=(R:ℝ)^r)]
  have z0:(c i:ℝ)≠0:=by exact_mod_cast c0
  let fi (j:Fin i.1):Fin k:=⟨j.1,lt_trans j.2 i.2⟩;let w j:=b (fi j);let θ (j:Fin i.1):ℝ:=(c (fi j):ℝ)/c i
  obtain ⟨t,q,t1,tl,ha⟩:=m1q θ (one_le_pow k 2 (by decide));let u:=(t:ℤ)•b i+∑ j:Fin i.1,q j•w j
  have hn:zR u ∉ m1S v i.1:=by
   rw [← bs i.1 i.2.le];intro h
   have f1:(t:ℝ)•zR (b i) ∈ m1S b i.1:=by rw [show (t:ℝ)•zR (b i)=zR u - ∑ j:Fin i.1,(q j:ℝ)•zR (w j) by dsimp only [u];rw [zRa,zRm,zRu];simp only [zRm,Int.cast_natCast,add_sub_cancel_right]];exact sub_mem h (sum_mem λ j _=>smul_mem _ _ (m1Z b j.2))
   exact m1N b bi i (by simpa [inv_smul_smul₀ (Nat.cast_ne_zero.mpr (by omega):(t:ℝ)≠0)] using smul_mem _ (t:ℝ)⁻¹ f1)
  have hl:g (v i)<=g u:=vm i u (L.add_mem (L.zsmul_mem (bL i) _) (L.sum_mem λ _ _=>L.zsmul_mem (bL _) _)) hn
  have hy:zR y=(c i:ℝ)•zR (b i)+∑ j:Fin i.1,(c (fi j):ℝ)•zR (w j):=by dsimp only [y];rw [zRu,show univ.filter (·<=i)=insert i (univ.filter (· < i)) by ext j;simp [le_iff_eq_or_lt],sum_insert (by simp),zRm];congr 1;exact (sum_bij (λ j _=>fi j) (λ j _=>mem_filter.mpr ⟨mem_univ _,j.2⟩) (λ _ _ _ _ h=>Fin.ext (congrArg (Fin.val:Fin k->ℕ) h)) (λ j hj=>⟨⟨j.1,(mem_filter.mp hj).2⟩,mem_univ _,by ext;rfl⟩) (λ _ _=>by rw [zRm])).symm
  have hu:zR u=((t:ℝ)/c i)•zR y+∑ j:Fin i.1,((q j:ℝ) - t*θ j)•zR (w j):=by rw [hy,smul_add,smul_smul,smul_sum,div_mul_cancel₀ _ z0,add_assoc,← sum_add_distrib];dsimp only [u];rw [zRa,zRm,zRu];simp only [Int.cast_natCast];congr 1;exact sum_congr rfl λ _ _=>by rw [zRm,smul_smul,← add_smul];congr 1;dsimp [θ];ring
  have hg:g u<=((t:ℝ)/|(c i:ℝ)|)*G+(1/2)*g (v i):=by
   dsimp [g];rw [hu];refine le_trans (le_trans (m1a h0 hconv (hV _ (smul_mem V _ (hL y (Ls _ c)))) (hV _ (sum_mem λ _ _=>smul_mem V _ (hL _ (bL _))))) (add_le_add le_rfl (m1l h0 hconv hsymm hV _ _ _ λ _ _=>hL _ (bL _)))) (add_le_add ?_ ?_)
   · rw [m1g hsymm,abs_div,abs_of_nonneg (Nat.cast_nonneg t)];gcongr
   calc ∑ j:Fin i.1,|(q j:ℝ) - t*θ j| *g (w j)
    _<=∑ j:Fin i.1,((2:ℝ)^k)⁻¹*((2:ℝ)^j.1*g (v i)):=sum_le_sum λ j _=>mul_le_mul (by rw [abs_sub_comm,← one_div];simpa using (ha j).le) ((bd _).trans (by gcongr;exact vo _ i (mk_le_mk.mpr j.2.le))) (gauge_nonneg _) (by positivity)
    _=((2:ℝ)^k)⁻¹*(∑ j:Fin i.1,(2:ℝ)^j.1)*g (v i):=by simp [mul_sum,sum_mul,mul_assoc]
    _<=(1/2)*g (v i):=mul_le_mul_of_nonneg_right (by rw [m12,inv_mul_le_iff₀ (by positivity)];linarith [show 2*(2:ℝ)^i.1<=2^k by rw [mul_comm,← pow_succ];exact pow_le_pow_right₀ (by norm_num) i.2]) (gauge_nonneg _)
  have hp:0 < |(c i:ℝ)|:=abs_pos.mpr z0;have hm:=mul_le_mul_of_nonneg_left (by linarith:(1/2:ℝ)*g (v i)<=((t:ℝ)/|(c i:ℝ)|)*G) hp.le;rw [show |(c i:ℝ)| *(((t:ℝ)/|(c i:ℝ)|)*G)=t*G by field_simp [hp.ne']] at hm
  have hb:(t:ℝ)<=(2:ℝ)^(k^2):=by exact_mod_cast tl.trans (by rw [← pow_mul,sq];gcongr;norm_num;exact i.2.le)
  have he:2*(2:ℝ)^(k^2)*G=(R:ℝ)^(r+1):=by dsimp [G,R];rw [pow_succ'];push_cast;rw [pow_add];ring
  nlinarith [(by positivity:0<=G)]
 refine ⟨c,λ i=>?_,hc⟩;have ib:|(c i:ℝ)| *g (v i)<=(R:ℝ)^k:=(show k - 1+1=k by omega) ▸ bk (k - 1) i (by omega)
 have cl:|(c i:ℝ)| < (R:ℝ)^k*(2*(k:ℝ)*(2:ℝ)^i.1)*N i:=lt_of_mul_lt_mul_right (calc
  |(c i:ℝ)| *g (v i)<=(R:ℝ)^k*1:=by linarith
  _ < (R:ℝ)^k*((N i:ℝ)*s i):=by gcongr;exact (div_lt_iff₀ (sp i)).mp (by dsimp [N];push_cast;exact lt_floor_add_one _)
  _=(R:ℝ)^k*(2*(k:ℝ)*(2:ℝ)^i.1)*N i*g (v i):=by dsimp [s];ring) (lp i).le
 have hL':(R:ℝ)^k*(2*(k:ℝ)*(2:ℝ)^i.1)<=jC d:=by
  have f1:R^k*(2*k*2^i.1)<=R^(k+1):=by rw [pow_succ];dsimp [R];gcongr <;> omega
  have f2:R^(k+1)<=jC d:=(by dsimp [R];gcongr;norm_num:R^(k+1)<=(2*(d+1)*2^(d^2+d))^(k+1)).trans (pow_le_pow_right (Nat.succ_le_of_lt (by positivity)) (by omega))
  exact_mod_cast le_trans f1 f2
 exact_mod_cast (by simpa [Int.cast_abs] using cl.trans_le (by gcongr):((|c i|:ℤ):ℝ) < ((jC d*N i:ℤ):ℝ))
end
end E186
namespace E186
def fSm {G:Type*} [AddCommMonoid G] [DecidableEq G]:∀ {n:ℕ},(Fin n->Finset G)->Finset G
 | 0,_=>{0}
 | _+1,A=>fSm (λ i=>A i.castSucc)+A (Fin.last _)
section
open AddSubgroup (closure_le zmultiples mem_zmultiples mem_zmultiples_iff mem_top)
open Fintype (piFinset mem_piFinset)
open Int (ediv_mul_cancel toNat_of_nonneg mul_ediv_add_emod)
open Nat (le_ceil lt_div_mul_add div_pos cast_nonneg)
open Pi (single)
abbrev m2C {G:Type*} [AddGroup G] (s:Set G):=AddSubgroup.closure s
abbrev m2D {G:Type*} [AddCommGroup G] [DecidableEq G] (s:Finset G):=m2C ((s - s:Finset G):Set G)
lemma m2E {a:ℕ} (h:0 < a):(0:ℝ) < a:=Nat.cast_pos.mpr h
lemma m2R {a b:ℕ} (h:a<=b):(a:ℝ)<=b:=Nat.cast_le.mpr h
lemma m2K {a b:ℕ} (h:a<=b):(a:ℤ)<=b:=Nat.cast_le.mpr h
lemma m2P {α:Type*} {s:Finset α} {c x:ℝ} (hc:0 < c) (hx:0 < x) (h:c*x<=#s):s.Nonempty:=card_pos.mp (by exact_mod_cast (mul_pos hc hx).trans_le h)
lemma m2L {a b:ℝ} (ha:0 < a) {n:ℕ} (h:⌈b/a⌉₊<=n):b<=a*n:=by have:=(div_le_iff₀ ha).mp ((le_ceil (b/a)).trans (m2R h));linarith
lemma m2S {G:Type*} [AddGroup G] {s:Finset G} {x:G} (h:x∈s):x∈m2C (s:Set G):=AddSubgroup.subset_closure (mem_coe.mpr h)
lemma m2I {α β:Type*} [DecidableEq β] {s:Finset α} {f:α->β} {y:β}:y∈s.image f->∃ x∈s,f x=y:=mem_image.mp
lemma m2J {α:Type*} [Preorder α] [LocallyFiniteOrder α] {a b x:α}:x∈Icc a b->a<=x/\x<=b:=mem_Icc.mp
lemma m2Z (z:ℤ) (n:ℕ):((z:ZMod n)=0)->(n:ℤ)∣z:=(ZMod.intCast_zmod_eq_zero_iff_dvd z n).mp
section
variable {G:Type*} [AddCommMonoid G] [DecidableEq G]
lemma m2a:∀ {n} (A:Fin n->Finset G) (x:G),x∈fSm A<->∃ f:Fin n->G,(∀ i,f i∈A i)/\∑ i,f i=x
 | 0,_,_=>by simp[fSm,eq_comm]
 | n+1,A,x=>by
  simp only[fSm,Finset.mem_add,m2a];constructor
  . rintro⟨_,⟨g,hg,rfl⟩,z,hz,rfl⟩;exact⟨Fin.snoc g z,λ i=>Fin.lastCases (by simpa using hz) (λ j=>by simpa using hg j) i,by rw[Fin.sum_univ_castSucc];simp⟩
  . rintro⟨f,hf,rfl⟩;exact⟨_,⟨λ i=>f i.castSucc,λ i=>hf _,rfl⟩,f (Fin.last n),hf _,(Fin.sum_univ_castSucc f).symm⟩
lemma m2b (A:Finset G):∀ n,fSm (λ _:Fin n=>A)=iSm n A
 | 0=>rfl
 | n+1=>by rw[fSm,iSm,m2b]
lemma m2c {n} {A B:Fin n->Finset G} (h:∀ i,A i⊆B i):fSm A⊆fSm B:=λ _ x=>by rw[m2a] at x ⊢;obtain⟨f,hf,rfl⟩:=x;exact⟨f,λ i=>h i (hf i),rfl⟩
lemma m2d {n} {A:Fin n->Finset G} (h:∀ i,(A i).Nonempty):(fSm A).Nonempty:=by choose f hf using h;exact⟨_,(m2a A _).mpr ⟨f,hf,rfl⟩⟩
lemma m2e {H:Type*} [AddCommMonoid H] [DecidableEq H] {n} (f:G →+ H) (A:Fin n->Finset G):(fSm A).image f=fSm (λ i=>(A i).image f):=by
 ext y;simp only[mem_image,m2a];constructor
 . rintro⟨_,⟨g,hg,rfl⟩,rfl⟩;exact⟨λ i=>f (g i),λ i=>⟨g i,hg i,rfl⟩,(map_sum f _ _).symm⟩
 . rintro⟨g,hg,rfl⟩;choose u h1 h2 using hg;exact⟨∑ i,u i,⟨u,h1,rfl⟩,by simp[map_sum,h2]⟩
lemma m2f {m n} (h:m=n) (A:Fin m->Finset G) (B:Fin n->Finset G) (e:∀ i,A i=B ⟨i.1,by omega⟩):fSm A=fSm B:=by subst h;congr 1;exact funext e
lemma m2g {a}:∀ {b} (A:Fin (a+b)->Finset G),fSm A=fSm (λ i:Fin a=>A ⟨i.1,by omega⟩)+fSm (λ j:Fin b=>A ⟨a+j.1,by omega⟩)
 | 0,A=>by ext x;simp[fSm,Finset.mem_add]
 | b+1,A=>by change fSm (λ i:Fin (a+b)=>A i.castSucc)+A (Fin.last _)=_;rw[m2g (b:=b) (λ i=>A i.castSucc),fSm,add_assoc];rfl
lemma m2h {s}:∀ {M} (A:Fin (M*s)->Finset G),fSm A=fSm (λ b:Fin M=>fSm (λ u:Fin s=>A ⟨b.1*s+u.1,by nlinarith[b.2,u.2]⟩))
 | 0,A=>by rw[m2f (Nat.zero_mul s) A Fin.elim0 (λ i=>by have:=i.2;simp at this)];rfl
 | M+1,A=>by rw[m2f (Nat.succ_mul M s) A (λ i=>A ⟨i.1,by rw[Nat.succ_mul];exact i.2⟩) (λ _=>rfl),m2g,fSm,m2h (M:=M)];rfl
lemma m2i {k n} (h:k<=n) (A:Fin n->Finset G) (hn:∀ i,(A i).Nonempty):∃ r,(fSm (λ i:Fin k=>A ⟨i.1,by omega⟩)).image (·+r)⊆fSm A:=by
 rw[m2f (Nat.add_sub_of_le h).symm A (λ i=>A ⟨i.1,by omega⟩) (λ _=>rfl),m2g];let⟨r,hr⟩:=m2d (λ j:Fin (n - k)=>hn ⟨k+j.1,by omega⟩);exact⟨r,λ _ y=>by obtain⟨_,x,rfl⟩:=m2I y;exact add_mem_add x hr⟩
end
lemma m2j {α β:Type*} [DecidableEq β] (s:Finset α) (t:Finset β) (ht:t.Nonempty) (f:α->β) (hf:∀ a∈s,f a∈t):∃ b∈t,#s<=#t*#(s.filter (λ a=>f a=b)):=by
 let⟨b,hb,hm⟩:=exists_max_image t (λ b=>#(s.filter (λ a=>f a=b))) ht;exact⟨b,hb,by rw[card_eq_sum_card_fiberwise hf];exact (sum_le_sum hm).trans (by rw[sum_const,smul_eq_mul])⟩
lemma m2k {n} {q:ℤ} {S:Fin n->Finset ℤ} (h:∀ i,S i⊆Icc 0 q) {z} (hz:z∈fSm S):0<=z/\z<=n*q:=by
 obtain⟨f,hf,rfl⟩:=(m2a S z).mp hz;exact⟨sum_nonneg λ i _=>(m2J (h i (hf i))).1,(sum_le_sum λ i _=>(m2J (h i (hf i))).2).trans (by simp)⟩
lemma m2l {d l} (A:Fin l->Finset (ZV d)) (lo:ZV d):fSm (λ t=>(A t).image (· - lo))=(fSm A).image (·+-(l•lo)):=by
 ext y;simp only[mem_image,m2a];constructor
 . rintro⟨g,hg,rfl⟩;choose f h1 h2 using hg;exact⟨∑ i,f i,⟨f,h1,rfl⟩,by simp[<- h2,sub_eq_add_neg,sum_add_distrib]⟩
 . rintro⟨_,⟨f,hf,rfl⟩,rfl⟩;exact⟨λ i=>f i - lo,λ i=>⟨f i,hf i,rfl⟩,by simp[sub_eq_add_neg,sum_add_distrib]⟩
lemma m2m {d} (Q:ZB d) {A:Finset (ZV d)} (h:A⊆Q.tF):(∀ x∈A.image (· - Q.lo),∀ i,0<=x i/\x i<=↑(Q.width i) - 1)/\#(A.image (· - Q.lo))=#A:=
 ⟨λ _ y i=>by obtain⟨x,hx,rfl⟩:=m2I y;have:=(ZB.mTF Q x).mp (h hx) i;have:↑(Q.width i)=Q.hi i - Q.lo i+1:=(by unfold ZB.width;omega);rw[Pi.sub_apply];omega,card_image_of_injective _ sub_left_injective⟩
lemma m2n {d V} (v:Fin d->ℕ) [∀ i,NeZero (v i)] (hv:∀ i,1<=v i/\v i<=V) :
 ∃ p:ZV d →+ (∀ i,ZMod (v i)),Function.Surjective p/\Fintype.card (∀ i,ZMod (v i))<=V^d/\∀ r z,p r=p z->∀ i,r i+((z i - r i)/v i)*v i=z i/\|(z i - r i)/v i|<=|z i|+|r i|:=by
 refine⟨⟨⟨λ x i=>(x i:ZMod (v i)),by ext i;exact Int.cast_zero⟩,λ _ _=>by ext i;exact Int.cast_add _ _⟩,λ x=>by choose f hf using λ i=>ZMod.intCast_surjective (x i);exact⟨f,funext hf⟩,
  by rw[Fintype.card_pi];simp only[ZMod.card];exact (prod_le_prod (λ _ _=>Nat.zero_le _) λ i _=>(hv i).2).trans (by simp),λ r z e i=>?_⟩
 have he:=ediv_mul_cancel (m2Z (z i - r i) (v i) (by have:=congrFun e i;dsimp at this;rw[Int.cast_sub,this,sub_self]))
 have h1:|(z i - r i)/v i| * |(v i:ℤ)|=|z i - r i|:=by rw[<- abs_mul];exact congrArg abs he
 have h2:(1:ℤ)<=|(v i:ℤ)|:=by rw[abs_of_nonneg (cast_nonneg _)];exact m2K (hv i).1
 exact⟨by linarith,(by nlinarith[h1,h2,abs_nonneg ((z i - r i)/v i)]:|(z i - r i)/v i|<=|z i - r i|).trans (abs_sub _ _)⟩
section
variable {G:Type*} [AddCommGroup G] [DecidableEq G]
lemma m2o {H:Type*} [AddCommGroup H] [DecidableEq H] (f:G →+ H) (hf:Function.Surjective f) {S:Finset G} (hS:m2D S=⊤):m2D (S.image f)=⊤:=
 eq_top_iff.mpr λ g _=>by obtain⟨z,rfl⟩:=hf g;exact ((closure_le ((m2D (S.image f)).comap f)).mpr λ _ u=>by obtain⟨a,ha,b,hb,rfl⟩:=Finset.mem_sub.mp (mem_coe.mp u);exact show f (a - b)∈m2D (S.image f) by rw[map_sub];exact m2S (sub_mem_sub (mem_image_of_mem f ha) (mem_image_of_mem f hb))) (by change z∈m2D S;rw[hS];trivial)
lemma m2p [Fintype G] (A:Fin (Fintype.card G)->Finset G) (hn:∀ i,(A i).Nonempty) (hg:∀ i,m2D (A i)=⊤):fSm A=univ:=by
 have hi:∀ k (hk:k<=Fintype.card G),min (Fintype.card G) (k+1)<=#(fSm λ i:Fin k=>A ⟨i.1,by omega⟩):=by
  intro k;induction k with
  | zero=>intro _;simp[fSm]
  | succ k ih=>
   intro hk;set T:=fSm λ i:Fin k=>A ⟨i.1,by omega⟩;set B:=A ⟨k,by omega⟩;have hih:min (Fintype.card G) (k+1)<=#T:=ih (by omega);change min (Fintype.card G) (k+1+1)<=#(T+B)
   have sb:∀ b∈B,b+ᵥ T⊆T+B:=λ b hb _ x=>by obtain⟨t,ht,rfl⟩:=mem_vadd_finset.mp x;rw[vadd_eq_add,add_comm b t];exact add_mem_add ht hb
   by_cases tu:T=univ
   . let⟨b,hb⟩:=hn ⟨k,by omega⟩;exact (min_le_left _ _).trans (by rw[<- card_univ,<- tu,<- card_vadd_finset b T];exact card_le_card (sb b hb))
   . have hlt:#T < #(T+B):=by
      by_contra hl;push Not at hl;have te:∀ b∈B,b+ᵥ T=T+B:=λ b hb=>eq_of_subset_of_card_le (sb b hb) (by rwa[card_vadd_finset])
      have tp:(⊤:AddSubgroup G)<=AddAction.stabilizer G T:=by rw[<- hg ⟨k,by omega⟩,closure_le];intro _ z;obtain⟨a,ha,b,hb,rfl⟩:=Finset.mem_sub.mp (mem_coe.mp z);change (a - b)+ᵥ T=T;rw[sub_eq_add_neg,add_comm,add_vadd,te a ha,<- te b hb,neg_vadd_vadd]
      let⟨t,ht⟩:=m2d (λ i:Fin k=>hn ⟨i.1,by omega⟩);exact tu (eq_univ_iff_forall.mpr λ g=>by rw[<- (tp (mem_top (g - t)):(g - t)+ᵥ T=T)];exact mem_vadd_finset.mpr ⟨t,ht,by simp⟩)
     have:=lt_of_le_of_ne (card_le_univ T) λ h=>tu (eq_univ_of_card T h);omega
 exact eq_univ_of_card _ (le_antisymm (card_le_univ _) (by have:=hi (Fintype.card G) le_rfl;rwa[min_eq_left (Nat.le_succ _)] at this))
lemma m2q (A:Finset G):∀ m {x},x∈iSm m A->x∈m2C (A:Set G)
 | 0,_,x=>by rw[iSm,mem_singleton] at x;rw[x];exact zero_mem _
 | m+1,_,x=>by obtain⟨_,y,_,a,rfl⟩:=Finset.mem_add.mp x;exact add_mem (m2q A m y) (m2S a)
end
lemma m2r (H:AddSubgroup ℤ):∃ v:ℕ,H=zmultiples ↑v:=by
 classical
 by_cases h:∃ n:ℕ,0 < n/\(n:ℤ)∈H
 . let v:=Nat.find h;let⟨hv0,vm⟩:=Nat.find_spec h;refine⟨v,le_antisymm (λ x hx=>mem_zmultiples_iff.mpr ⟨x/v,?_⟩) (AddSubgroup.zmultiples_le.mpr vm)⟩
   have r0:=Int.emod_nonneg x (by omega:↑v≠(0:ℤ));have rl:=Int.emod_lt_of_pos x (by omega:(0:ℤ) < v);have dv:=mul_ediv_add_emod x v
   have rm:x % v∈H:=(by rw[Int.emod_def,mul_comm,<- smul_eq_mul];exact H.sub_mem hx (H.zsmul_mem vm _))
   have rz:x % v=0:=(by by_contra hn;exact Nat.find_min h (by omega:(x % v).toNat < v) ⟨by omega,by rwa[toNat_of_nonneg r0]⟩);rw[smul_eq_mul];linarith
 . refine⟨0,le_antisymm (λ x hx=>?_) (by simp)⟩;have:x=0:=by by_contra hn;exact h ⟨x.natAbs,Int.natAbs_pos.mpr hn,by rcases Int.natAbs_eq x with e | e <;> [exact e▸hx;exact (show ↑x.natAbs=-x by linarith)▸H.neg_mem hx]⟩
   simp[this]
lemma m2s {p r:ℕ} [NeZero p] (hp:p.Prime) {e:ℝ} (he:0 < e) (pe:2/e<=p) (hr:2/e<=r) (F:Fin r->Finset (ZMod p)) (hF:∀ i,e*p<=#(F i)):fSm F=univ:=by
 have hn:=λ i=>m2P he (m2E hp.pos) (hF i);have h1:(1:ℝ)<=e/2*p:=by have:=(div_le_iff₀ he).mp pe;linarith
 have hi:∀ t (ht:t<=r),min ↑p (t*(e/2*p))<=#(fSm λ i:Fin t=>F ⟨i.1,by omega⟩):=by
  intro t;induction t with
  | zero=>intro _;simp[fSm]
  | succ t ih=>
   intro ht;set T:=fSm λ i:Fin t=>F ⟨i.1,by omega⟩;set B:=F ⟨t,by omega⟩;have hih:min ↑p (t*(e/2*p))<=#T:=ih (by omega)
   have cd:=ZMod.cauchy_davenport hp (m2d (λ i:Fin t=>hn ⟨i.1,by omega⟩)) (hn ⟨t,by omega⟩);change min p (#T+#B - 1)<=#(T+B) at cd
   have:=hF ⟨t,by omega⟩;have:=card_pos.mpr (hn ⟨t,by omega⟩);change min ↑p (((t+1:ℕ):ℝ)*(e/2*p))<=#(T+B)
   rcases le_total p (#T+#B - 1) with h | h
   . rw[min_eq_left h] at cd;exact (min_le_left _ _).trans (m2R cd)
   . rw[min_eq_right h] at cd;have hR:(#T:ℝ)+#B<=#(T+B)+1:=(by exact_mod_cast show #T+#B<=#(T+B)+1 by omega)
     rcases le_total ↑p (t*(e/2*p)) with h2 | h2 <;> [rw[min_eq_left h2] at hih;rw[min_eq_right h2] at hih]
     . exact (min_le_left _ _).trans (by linarith)
     . exact (min_le_right _ _).trans (by push_cast;linarith)
 have hf:=hi r le_rfl;have hm:(p:ℝ)<=r*(e/2*p):=by have:=mul_le_mul_of_nonneg_right hr (show 0<=e/2*p by positivity);have:2/e*(e/2*p)=p:=(by field_simp[ne_of_gt he]);linarith
 rw[min_eq_left hm] at hf;exact eq_univ_of_card _ (le_antisymm (card_le_univ _) (by rw[ZMod.card];exact_mod_cast hf))
lemma m2t {U V:Finset ℤ} (hU:U.Nonempty) (hV:V.Nonempty):#U+#V - 1<=#(U+V):=by
 let a:=U.max' hU;let b:=V.min' hV;let X:=U.image (·+b);let Y:=V.image (a+·)
 have xy:X ∩ Y⊆{a+b}:=λ _ z=>by obtain⟨u,hu,rfl⟩:=m2I (mem_inter.mp z).1;obtain⟨v,hv,e⟩:=m2I (mem_inter.mp z).2;have:=U.le_max' u hu;have:=V.min'_le v hv;dsimp[a,b] at*;exact mem_singleton.mpr (by omega)
 have:#X=#U:=card_image_of_injective U (add_left_injective b);have:#Y=#V:=card_image_of_injective V (add_right_injective a)
 have hX:X⊆U+V:=λ _ z=>by obtain⟨u,hu,rfl⟩:=m2I z;exact add_mem_add hu (V.min'_mem hV)
 have hY:Y⊆U+V:=λ _ z=>by obtain⟨v,hv,rfl⟩:=m2I z;exact add_mem_add (U.max'_mem hU) hv
 have:=card_le_card (union_subset hX hY)
 have:=(card_le_card xy).trans (by simp:#({a+b}:Finset ℤ)<=1);have:=card_union_add_card_inter X Y;omega
lemma m2u (s:ℤ) {M} (B:Fin M->Finset ℤ) (J:Finset (Fin M)) (x:Fin M->ℤ) (hx:∀ b,x b∈B b) (hJ:∀ b∈J,x b+s∈B b) (j:ℤ) (h0:0<=j) (h1:j<=#J):(∑ b,x b)+j*s∈fSm B:=by
 let⟨S,sj,sc⟩:=exists_subset_card_eq (by omega:j.toNat<=#J);rw[m2a]
 refine⟨λ b=>x b+if b∈S then s else 0,λ b=>by dsimp only;split_ifs with h <;> [exact hJ b (sj h);simpa using hx b],?_⟩
 rw[sum_add_distrib,sum_ite,sum_const,sum_const_zero,add_zero,filter_mem_eq_inter,univ_inter,sc,nsmul_eq_mul,toNat_of_nonneg h0]
lemma m2v {n u:ℕ} (hu:1<=u) {B:Finset ℤ} (hB:B.Nonempty) (hBs:B⊆Icc 0 ↑n) (hBg:m2D B=zmultiples ↑u) :
 let a:=B.min' hB;let S:=B.image (λ x=>(x - a)/u);(∀ x∈B,(u:ℤ)∣(x - a))/\S⊆Icc 0 ↑(n/u)/\#S=#B/\m2D S=⊤:=by
 intro a S;have dv:∀ x∈B,(u:ℤ)∣(x - a):=λ x hx=>by let⟨k,hk⟩:=mem_zmultiples_iff.mp (by rw[<- hBg];exact m2S (sub_mem_sub hx (min'_mem B hB)):x - a∈zmultiples (u:ℤ));rw[smul_eq_mul] at hk;exact⟨k,by linarith⟩
 refine⟨dv,λ _ y=>?_,card_image_of_injOn λ x hx y hy e=>?_,?_⟩
 . obtain⟨x,hx,rfl⟩:=m2I y;have:a<=x:=min'_le B x hx;have:=m2J (hBs hx);have:=m2J (hBs (min'_mem B hB))
   exact mem_Icc.mpr ⟨Int.ediv_nonneg (by omega) (by omega),by rw[Int.natCast_ediv];exact Int.ediv_le_ediv (by omega) (by omega)⟩
 . have e1:=ediv_mul_cancel (dv x hx);have e2:=ediv_mul_cancel (dv y hy);rw[e] at e1;linarith
 . let H:=m2D S;let f:=AddMonoidHom.mulLeft (u:ℤ)
   have hle:zmultiples (u:ℤ)<=H.map f:=by rw[<- hBg,closure_le];intro _ z;obtain⟨x,hx,y,hy,rfl⟩:=Finset.mem_sub.mp (mem_coe.mp z);refine⟨(x - a)/u - (y - a)/u,m2S (sub_mem_sub (mem_image_of_mem _ hx) (mem_image_of_mem _ hy)),?_⟩;have:=ediv_mul_cancel (dv x hx);have:=ediv_mul_cancel (dv y hy);dsimp[f];linarith
   let⟨t,htH,htE⟩:=hle (mem_zmultiples (u:ℤ));have ht1:t=1:=(by have:=m2K hu;dsimp[f] at htE;nlinarith)
   rw[eq_top_iff];intro z _;rw[<- mul_one z,<- ht1,<- smul_eq_mul];exact H.zsmul_mem htH z
lemma m2w {c:ℝ} (hc:0 < c) :
 ∃ (c':ℝ) (L N:ℕ),0 < c'/\∀ (q l:ℕ),N<=q->L<=l->∀ (S:Fin l->Finset ℤ),(∀ i,S i⊆Icc 0 ↑q)->(∀ i,c*q<=#(S i))->(∀ i,m2D (S i)=⊤)->∃ x0:ℤ,(Icc 0 ⌊c'*l*q⌋).image (λ k=>x0+k)⊆fSm S:=by
 let r:=⌈4/c⌉₊+1;have r0:1<=r:=by omega
 let s:=r+r;let R:=⌈8*r/c⌉₊;let B:=R+s;let c':ℝ:=1/(32*(r:ℝ)^2);refine⟨c',32*r^2*B+32*r^2,B+4,by positivity,?_⟩;intro q l hq hl S ss sc sg
 have sn:=λ i=>m2P hc (m2E (show 0 < q by omega)) (sc i);let⟨p,hp,q0,pq⟩:=Nat.bertrand q (by omega);have:NeZero p:=⟨hp.ne_zero⟩
 have qz:(q:ℤ) < p:=by exact_mod_cast q0
 have pz:(0:ℤ) < p:=by exact_mod_cast hp.pos
 let f:=Int.castAddHom (ZMod p)
 have pi:Set.InjOn f (Icc 0 (q:ℤ):Set ℤ):=λ x hx y hy e=>by have hx':=m2J (mem_coe.mp hx);have hy':=m2J (mem_coe.mp hy);let⟨t,ht⟩:=m2Z (x - y) p (by rw[Int.cast_sub];exact sub_eq_zero.mpr e);have t0:t=0:=(by nlinarith only[ht,hx'.1,hx'.2,hy'.1,hy'.2,qz]);subst t0;omega
 have qR:8*r/c<=q:=(le_ceil (8*r/c)).trans (m2R (by omega))
 have cov:∀ (t:ℕ) (e:ℝ) (F:Fin t->Finset ℤ),0 < e->2/e<=q->2/e<=t->(∀ i,F i⊆Icc 0 ↑q)->(∀ i,2*e*q<=#(F i))->(fSm F).image f=univ:=λ t e F he hqe ht hs hf=>by
  rw[m2e f];refine m2s hp he (hqe.trans (m2R (le_of_lt q0))) ht _ λ j=>?_;rw[card_image_of_injOn (pi.mono (coe_subset.mpr (hs j)))];have:(p:ℝ)<=2*q:=(by exact_mod_cast pq);nlinarith only[hf j,this,he]
 have c0:∀ g:Fin r->Fin l,p<=#(fSm λ u=>S (g u)):=λ g=>by
  have:=card_image_le (f:=f) (s:=fSm λ u=>S (g u))
  rw[cov r (c/2) (λ j=>S (g j)) (by positivity) (by have:(1:ℝ)<=r:=(by exact_mod_cast r0);have:4/c<=8*r/c:=div_le_div_of_nonneg_right (by linarith) hc.le;linarith[show 2/(c/2)=4/c by ring])
   (by rw[show 2/(c/2)=4/c by ring];exact (le_ceil (4/c)).trans (m2R (Nat.le_succ _))) (λ _=>ss _) (λ j=>by rw[show 2*(c/2)*q=c*q by ring];exact sc (g j)),card_univ,ZMod.card] at this;exact this
 let a:=l/2;let M:=a/s;have m2:M*s<=a:=Nat.div_mul_le_self a s;have bi:∀ (b:Fin M) (u:Fin s),b.1*s+u.1 < l:=λ b u=>by have:b.1*s+u.1 < M*s:=(by nlinarith only[b.2,u.2]);omega
 let D:=λ b:Fin M=>fSm λ u:Fin s=>S ⟨b.1*s+u.1,bi b u⟩
 have pr:∀ b,∃ k∈Icc 1 s,∃ x∈D b,x+k*p∈D b:=λ b=>by
  let bk:=λ u:Fin s=>S ⟨b.1*s+u.1,bi b u⟩;have sp:D b=fSm (λ u:Fin r=>bk ⟨u.1,by omega⟩)+fSm (λ u:Fin r=>bk ⟨r+u.1,by omega⟩):=m2g bk
  set U:=fSm λ u:Fin r=>bk ⟨u.1,by omega⟩;set V:=fSm λ u:Fin r=>bk ⟨r+u.1,by omega⟩
  have uc:p<=#U:=c0 λ u=>⟨b.1*s+u.1,bi b ⟨u.1,by omega⟩⟩;have vc:p<=#V:=c0 λ u=>⟨b.1*s+(r+u.1),bi b ⟨r+u.1,by omega⟩⟩
  have uv:p < #(U+V):=by have:=m2t (card_pos.mp (lt_of_lt_of_le hp.pos uc)) (card_pos.mp (lt_of_lt_of_le hp.pos vc));have:=hp.two_le;omega
  let⟨⟨x1,h1⟩,⟨x2,h2⟩,hn,hm⟩:=Fintype.exists_ne_map_eq_of_card_lt (λ z:↥(U+V)=>f z.1) (by rw[Fintype.card_coe,ZMod.card];exact uv)
  have ⟨y1,y2,ha,hd,hl,hmd⟩:∃ y1 y2,y1∈U+V/\y2∈U+V/\y1 < y2/\(y1:ZMod p)=y2:=by rcases lt_or_gt_of_ne (λ h=>hn (Subtype.ext h)) with h | h <;> [exact⟨x1,x2,h1,h2,h,hm⟩;exact⟨x2,x1,h2,h1,h,hm.symm⟩]
  let⟨z,hz⟩:=m2Z (y2 - y1) p (by rw[Int.cast_sub,hmd,sub_self]);have ba:=m2k (λ _=>ss _) (sp▸ha);have bd:=m2k (λ _=>ss _) (sp▸hd)
  have kp:1<=z:=by nlinarith only[hz,hl,pz]
  have kl:z<=s:=by have:(s:ℤ)*q<=s*p:=mul_le_mul_of_nonneg_left qz.le (cast_nonneg _);nlinarith only[hz,ba.1,bd.2,this,pz]
  exact⟨z.toNat,mem_Icc.mpr ⟨by omega,by omega⟩,y1,sp▸ha,by rw[sp,show y1+z.toNat*p=y2 by rw[toNat_of_nonneg (by omega)];linarith];exact hd⟩
 choose kf km x x0 x1 using pr;let⟨k,km',ml⟩:=m2j univ (Icc 1 s) ⟨1,mem_Icc.mpr ⟨le_rfl,by omega⟩⟩ kf λ _ _=>km _
 let⟨k1,kl⟩:=m2J km';let J:=univ.filter (λ b:Fin M=>kf b=k);rw[card_univ,Fintype.card_fin,Nat.card_Icc,add_tsub_cancel_right] at ml;change M<=s*#J at ml
 have:NeZero k:=⟨by omega⟩;have cp:Nat.Coprime k p:=(hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) (by omega))).symm
 have bl:2*B+4<=l:=by have:1<=r^2:=(by nlinarith only[r0]);nlinarith only[hl,this]
 have tt:M*s+(R+Fintype.card (ZMod k))<=l:=by rw[ZMod.card];dsimp[B,a] at bl m2 ⊢;omega
 let h:=Int.castAddHom (ZMod k);let U:=λ j:Fin R=>S ⟨M*s+j.1,by omega⟩;let e0:=c/(4*r)
 have fb:∀ j,∃ y:ZMod k,2*e0*q<=#((U j).filter (λ z=>h z=y)):=λ j=>by
  let⟨y,_,hl'⟩:=m2j (U j) univ ⟨0,mem_univ _⟩ h λ _ _=>mem_univ _;refine⟨y,?_⟩;rw[card_univ,ZMod.card] at hl'
  have h1:(#(U j):ℝ)<=2*r*#((U j).filter (λ z=>h z=y)):=by exact_mod_cast hl'.trans (Nat.mul_le_mul_right _ (by dsimp[s] at kl;omega))
  have:=m2E r0;rw[show 2*e0*q=c*q/(2*r) by dsimp[e0];ring,div_le_iff₀ (by positivity)];linarith[sc ⟨M*s+j.1,by omega⟩]
 choose y fc using fb;let F:=λ j=>(U j).filter (λ z=>h z=y j);let W:=fSm F;have ws:W⊆fSm U:=m2c λ _=>filter_subset _ _
 have e2:2/e0=8*r/c:=by dsimp[e0];field_simp;ring
 have wp:W.image f=univ:=cov R e0 F (by dsimp[e0];positivity) (e2▸qR) (e2▸le_ceil _) (λ _=>(filter_subset _ _).trans (ss _)) fc
 have wk:∀ w∈W,h w=∑ j,y j:=λ w hw=>by obtain⟨g,hg,rfl⟩:=(m2a F w).mp hw;rw[map_sum];exact sum_congr rfl λ j _=>(mem_filter.mp (hg j)).2
 let T0:=λ t:Fin (Fintype.card (ZMod k))=>S ⟨M*s+(R+t.1),by have:=t.2;omega⟩;let T:=fSm T0
 have tk:T.image h=univ:=by rw[m2e h];exact m2p _ (λ _=>(sn _).image h) λ _=>m2o h ZMod.intCast_surjective (sg _)
 let⟨rr,h0⟩:=m2i tt S sn;let P:ℤ:=↑(k*p);refine⟨(∑ b,x b)+B*P+rr,λ _ y'=>?_⟩;obtain⟨u,hs,rfl⟩:=m2I y';let⟨s0,sh⟩:=m2J hs
 have jg:2*B<=#J/\l<=16*r^2*#J:=by
  have r4:4*r<=l:=(by nlinarith only[hl,r0]);have m1:1<=M:=div_pos (by dsimp[a,s];omega) (by dsimp[s];omega)
  have lm:a < M*s+s:=lt_div_mul_add (a:=a) (show 0 < s by omega);dsimp[s] at lm ml
  have lJ:l<=16*r^2*#J:=(by have:l<=2*a+1:=(by omega);nlinarith only[this,m1,lm,ml]);exact⟨by nlinarith only[lJ,hl,show 0 < 16*r^2 by positivity],lJ⟩
 have qp:q<=k*p:=by nlinarith only[q0,k1]
 have sl:u<=↑(#J - B)*P:=by
  have h1:l<=32*r^2*(#J - B):=by have:#J<=2*(#J - B):=(by omega);nlinarith only[jg.2,this]
  have h2:(l:ℝ)*q<=32*r^2*(↑(#J - B)*P):=by dsimp[P];exact_mod_cast (Nat.mul_le_mul h1 qp).trans_eq (by ring)
  exact sh.trans (Int.floor_le_iff.mpr (by dsimp[c'];rw[one_div_mul_eq_div,div_mul_eq_mul_div,div_lt_iff₀ (by positivity)];push_cast at h2 ⊢;nlinarith only[h2,show (0:ℝ) < 32*(r:ℝ)^2 by positivity]))
 let g:ℤ:=B*P+u;let⟨t,t0,te⟩:=m2I (tk.symm▸mem_univ (h g - ∑ j,y j));let⟨w,w0,we⟩:=m2I (wp.symm▸mem_univ (f (g - t)));let z:=g - (w+t)
 have d1:(k:ℤ)∣z:=m2Z z k (by change h (g - (w+t))=0;rw[map_sub h g (w+t),map_add h w t,wk w w0,te];ring)
 have d2:(p:ℤ)∣z:=m2Z z p (by change f (g - (w+t))=0;rw[map_sub f g (w+t),map_add f w t,we,map_sub f g t];ring)
 let⟨j,jq⟩:=Int.ofNat_dvd_left.mpr (cp.mul_dvd_of_dvd_of_dvd (Int.ofNat_dvd_left.mp d1) (Int.ofNat_dvd_left.mp d2));have je:z=P*j:=by simpa[P,Nat.cast_mul] using jq
 have wt:0<=w+t/\w+t<=B*P:=by have wb:=m2k (λ _=>ss _) (ws w0);have tb:=m2k (λ _=>ss _) t0;rw[ZMod.card] at tb;have:((R:ℤ)+k)*q<=B*P:=mul_le_mul (by dsimp[B];omega) (by dsimp[P];exact m2K qp) (cast_nonneg _) (cast_nonneg _);exact⟨by omega,by linarith only[wb.2,tb.2,this]⟩
 have jb:0<=j/\j<=#J:=by
  have kp:0 < P:=(by dsimp[P];exact_mod_cast Nat.mul_pos (by omega:0 < k) hp.pos);have h2:(↑(#J - B):ℤ)+B=#J:=by have:=jg.1;omega
  have h1:P*j<=#J*P:=(by dsimp[z,g] at je;nlinarith only[je,wt.1,sl,h2,kp]);exact⟨by dsimp[z,g] at je;nlinarith only[je,wt.2,s0,kp],by nlinarith only[h1,kp]⟩
 apply h0;refine mem_image.mpr ⟨(∑ b,x b)+g,?_,by dsimp[g];ring⟩;rw[m2g,m2h,m2g]
 convert add_mem_add (m2u P D J x x0 (λ b hb=>by simpa[(mem_filter.mp hb).2,P,Nat.cast_mul] using x1 b) j jb.1 jb.2) (add_mem_add (ws w0) t0) using 1
 dsimp[z] at je;linarith
lemma m2x (d:ℕ) (hd:1<=d) {c:ℝ} (hc:0 < c) :
 ∃ (cd:ℝ) (V L W:ℕ),0 < cd/\1<=V/\∀ (Q:ZB d),(∀ i,W<=Q.width i)->∀ (l:ℕ),L<=l->∀ (A:Fin l->Finset (ZV d)),(∀ t,∀ x∈A t,∀ i,0<=x i/\x i<=↑(Q.width i) - 1)->(∀ t,c*Q.vol<=#(A t))->
  ∃ (v:Fin d->ℕ) (t0:ZV d),(∀ i,1<=v i/\v i<=V)/\(piFinset (λ i=>Icc 0 ⌊cd*l*Q.width i⌋)).image (λ b=>t0+λ i=>b i*(v i:ℤ))⊆fSm A:=by
 let⟨c1,L1,N1,cp,hb⟩:=m2w (show 0 < c/2 by positivity);let V:=⌈2/c⌉₊;have vp:1<=V:=Nat.ceil_pos.mpr (by positivity)
 let cd:ℝ:=c1/(8*d*V^2);have dp:=m2E hd;have vr:=m2E vp;refine⟨cd,V,d*(V*(L1+1)+2),V*(N1+2)+4,by positivity,vp,?_⟩
 intro Q hq l hl A as ac;let w:=Q.width;have n1:=λ t=>m2P hc (m2E Q.vP) (ac t);let m:=l/d
 have dm:d*m<=l:=Nat.mul_div_le l d;have mv:V*(L1+1)+2<=m:=(Nat.le_div_iff_mul_le hd).mpr (by rw[mul_comm];exact hl);have mp:0 < m:=by omega
 have lm:l<=2*d*m:=by have:l < m*d+d:=lt_div_mul_add (a:=l) hd;nlinarith only[this,mp]
 have bk:∀ k:Fin d,∃ (vk:ℕ) (zk:ZV d),1<=vk/\vk<=V/\∀ b∈Icc 0 ⌊cd*l*w k⌋,zk+single k (b*vk)∈fSm (λ j:Fin m=>A ⟨k.1*m+j.1,by nlinarith only[k.2,j.2,dm]⟩):=λ k=>by
  have nw:=hq k;let X:=λ j:Fin m=>A ⟨k.1*m+j.1,by nlinarith only[k.2,j.2,dm]⟩;let F:=λ j y=>(X j).filter (λ x=>Function.update x k 0=y)
  let Q0:=piFinset λ i=>if i=k then {0} else Icc 0 ((w i:ℤ) - 1)
  have qo:#Q0*w k=Q.vol:=by rw[Fintype.card_piFinset,ZB.vol,<- mul_prod_erase univ w (mem_univ k),mul_comm];congr 1;rw[<- mul_prod_erase univ _ (mem_univ k),if_pos rfl,card_singleton,one_mul];exact prod_congr rfl λ i hi=>by rw[if_neg (mem_erase.mp hi).1,Int.card_Icc];have:=Q.wP i;omega
  have fb:∀ j,∃ y,y k=0/\c*w k<=#((F j y).image (λ x=>x k)):=λ j=>by
   have q1:Q0.Nonempty:=card_pos.mp (by have:=Q.vP;nlinarith only[this,qo])
   let⟨y,hy,hl'⟩:=m2j (X j) Q0 q1 (λ x=>Function.update x k 0) λ x hx=>mem_piFinset.mpr λ i=>by by_cases h:i=k <;> [(subst h;simp);(rw[if_neg h,Function.update_of_ne h,mem_Icc];exact as _ x hx i)]
   have cg:c*w k<=#(F j y):=by have r1:(#(X j):ℝ)<=#Q0*#(F j y):=(by exact_mod_cast hl');have r2:(#Q0:ℝ)*w k=Q.vol:=(by exact_mod_cast qo);have q2:=m2E (card_pos.mpr q1);have h2:c*(#Q0*w k)<=#(X j):=(by rw[r2];exact ac _);nlinarith only[r1,h2,q2]
   have ij:Set.InjOn (λ x:ZV d=>x k) (F j y:Set (ZV d)):=λ _ h1 _ h2 e=>funext λ i=>by by_cases ik:i=k <;> [(subst ik;exact e);simpa[ik] using congrFun ((mem_filter.mp h1).2.trans (mem_filter.mp h2).2.symm) i]
   exact⟨y,by simpa using mem_piFinset.mp hy k,by rw[card_image_of_injOn ij];exact cg⟩
  choose y yk bc using fb;let B:=λ j=>(F j (y j)).image (λ x=>x k)
  have bs:∀ j,B j⊆Icc 0 ↑(w k - 1):=λ j _ hu=>by obtain⟨x,hx,rfl⟩:=m2I hu;have h1:=as _ x (mem_filter.mp hx).1 k;have:=Q.wP k;exact mem_Icc.mpr ⟨h1.1,by dsimp[w] at*;omega⟩
  have bm:∀ j,∀ u∈B j,y j+single k u∈X j:=λ j _ hu=>by obtain⟨x,hx,rfl⟩:=m2I hu;have hf:=mem_filter.mp hx;rw[show y j+single k (x k)=x by ext i;by_cases ik:i=k <;> [(subst ik;simp[yk j]);simp[ik,<- congrFun hf.2 i]]];exact hf.1
  have bn:=λ j=>m2P hc (m2E (Q.wP k)) (bc j)
  have hv:∀ j,∃ u∈Icc 1 V,m2D (B j)=zmultiples ↑u:=λ j=>by
   let⟨u,ve⟩:=m2r (m2D (B j));have l2:(2:ℝ)<=c*w k:=m2L hc (by have:V<=w k:=(by nlinarith only[nw]);omega);have g2:2<=#(B j):=by exact_mod_cast l2.trans (bc j)
   have u1:1<=u:=by by_contra h0;have hv0:u=0:=(by omega);subst hv0;let⟨a,ha,b,hb,hab⟩:=one_lt_card.mp (by omega:1 < #(B j));exact hab (sub_eq_zero.mp (by simpa using (by rw[<- Nat.cast_zero,<- ve];exact m2S (sub_mem_sub ha hb):a - b∈zmultiples (0:ℤ))))
   have vl:u<=V:=by
    let⟨_,hs,hc',_⟩:=m2v u1 (bn j) (bs j) ve;have cl:#(B j)<=(w k - 1)/u+1:=hc'▸(card_le_card hs).trans (by rw[Int.card_Icc];simp)
    have h1:((#(B j):ℝ) - 1)*u<=w k:=by have:=m2R (((Nat.le_div_iff_mul_le u1).mp (Nat.sub_le_of_le_add cl)).trans (Nat.sub_le _ _));rw[Nat.cast_mul,Nat.cast_sub (by omega),Nat.cast_one] at this;exact this
    have wp:=m2E (Q.wP k);have vr:(u:ℝ)<=2/c:=(by rw[le_div_iff₀ hc];nlinarith only[bc j,l2,h1,wp,hc]);exact_mod_cast vr.trans (le_ceil _)
   exact⟨u,mem_Icc.mpr ⟨u1,vl⟩,ve⟩
  choose f vm vq using hv;let⟨v,vk,jc⟩:=m2j univ (Icc 1 V) ⟨1,mem_Icc.mpr ⟨le_rfl,vp⟩⟩ f λ _ _=>vm _;let⟨v1,vV⟩:=m2J vk;let J:=univ.filter (λ j:Fin m=>f j=v)
  rw[card_univ,Fintype.card_fin,Nat.card_Icc,add_tsub_cancel_right] at jc;change m<=V*#J at jc
  let e:Fin #J ≃ J:=(Fintype.equivFinOfCardEq (Fintype.card_coe J)).symm;let a:=λ j=>(B j).min' (bn j);let S:=λ i=>(B (e i).1).image (λ x=>(x - a (e i).1)/v)
  have hd:=λ i=>m2v v1 (bn (e i).1) (bs (e i).1) (by rw[<- (mem_filter.mp (e i).2).2];exact vq (e i).1);let q:=(w k - 1)/v
  have hN:N1+2<=q:=by have h0:V*(N1+2)<=w k - 1:=(by dsimp[w] at*;omega);exact (Nat.le_div_iff_mul_le v1).mpr (by nlinarith only[vV,h0])
  let⟨y0,yh⟩:=hb q #J (by omega) (by nlinarith only[jc,mv,vp]) S (λ i=>(hd i).2.1) (λ i=>by rw[(hd i).2.2.1];have:=m2R ((Nat.div_le_self (w k - 1) v).trans (Nat.sub_le (w k) 1));nlinarith only[bc (e i).1,this,hc]) (λ i=>(hd i).2.2.2)
  have h':cd*l*w k<=c1*#J*q:=by
   have h1:w k<=q*v+v+1:=(by have:w k - 1 < q*v+v:=lt_div_mul_add (a:=w k - 1) v1;have:=Q.wP k;dsimp[w] at*;omega)
   have h2:w k<=4*V*q:=(by nlinarith only[h1,hN,vV,vp])
   have h4:(l:ℝ)*w k<=8*d*V^2*#J*q:=(by exact_mod_cast show l*w k<=8*d*V^2*#J*q by have:=Nat.mul_le_mul (show l<=2*d*V*#J by nlinarith only[lm,jc]) h2;nlinarith only[this])
   dsimp[cd];rw[div_mul_eq_mul_div,div_mul_eq_mul_div,div_le_iff₀ (by positivity)];nlinarith only[h4,cp]
  refine⟨v,(∑ j,y j)+single k ((∑ j,a j)+y0*v),v1,vV,λ b hb=>?_⟩
  let⟨u,hu,hus⟩:=(m2a S _).mp (yh (mem_image_of_mem _ (mem_Icc.mpr ⟨(m2J hb).1,(m2J hb).2.trans (Int.floor_mono h')⟩)))
  let g:=λ j=>a j+if hj:j∈J then u (e.symm ⟨j,hj⟩)*v else 0
  have gs:∑ j,g j=(∑ j,a j)+y0*v+b*v:=by
   rw[sum_add_distrib,<- sum_subset (subset_univ J) (λ j _ hj=>dif_neg hj),<- sum_coe_sort J,<- Equiv.sum_comp e]
   have h1:∑ i,(if hj:(e i).1∈J then u (e.symm ⟨(e i).1,hj⟩)*(v:ℤ) else 0)=∑ i,u i*v:=sum_congr rfl λ i _=>by simp[(e i).2]
   rw[h1,<- sum_mul,hus];ring
  rw[m2a];refine⟨λ j=>y j+single k (g j),λ j=>bm j (g j) (by
   dsimp[g];split_ifs with hj
   . let i:=e.symm ⟨j,hj⟩;let⟨x,hx,hu⟩:=m2I (hu i);have h1:=ediv_mul_cancel ((hd i).1 x hx);rw[hu] at h1
     have ej:(e i).1=j:=congrArg Subtype.val (e.apply_symm_apply ⟨j,hj⟩);rw[ej] at hx h1;rw[show a j+u i*v=x by linarith only[h1]];exact hx
   . simpa using min'_mem (B j) (bn j)),?_⟩
  ext i;simp only[sum_add_distrib,Pi.add_apply,Finset.sum_apply];by_cases ik:i=k <;> [(subst ik;simp only[Pi.single_eq_same];rw[gs];ring);simp[ik]]
 choose v z v1 vV hz using bk;let⟨rr,hp⟩:=m2i dm A n1;refine⟨v,(∑ k,z k)+rr,λ i=>⟨v1 i,vV i⟩,λ _ hx=>?_⟩;obtain⟨b,hb,rfl⟩:=m2I hx
 rw[show ((∑ k,z k)+rr)+(λ i=>b i*(v i:ℤ))=((∑ k,z k)+(λ i=>b i*(v i:ℤ)))+rr by abel];apply hp;refine mem_image_of_mem _ ?_;rw[m2h,m2a]
 refine⟨λ k=>z k+single k (b k*v k),λ k=>hz k (b k) ((mem_piFinset.mp hb) k),?_⟩;rw[sum_add_distrib];congr 1;ext i;simp[Finset.sum_apply,Pi.single_apply]
theorem leb (d:ℕ) (hd:1<=d) {c:ℝ} (hc0:0 < c) (hc1:c<=1) :
 ∃ (γ:ℝ) (L₀ W₀:ℕ),0 < γ/\∀ (Q:ZB d),(∀ i,W₀<=Q.width i)->∀ (ℓ:ℕ),L₀<=ℓ->
 ∀ (A:Fin ℓ->Finset (ZV d)),(∀ t,A t⊆Q.tF)->(∀ t,c*(Q.vol:ℝ)<=((A t).card:ℝ))->
 (∀ t,AddSubgroup.closure ((A t - A t:Finset (ZV d)):Set (ZV d))=⊤)->
 ∃ x₀:ZV d,(ZB.symm (λ i=>⌊γ*(ℓ:ℝ)*(Q.width i:ℝ)⌋₊)).tF.image (·+x₀)⊆fSm A:=by
 have _:=hc1;let⟨cd,V,L2,W2,cp,_,h0⟩:=m2x d hd hc0;let g:ℝ:=cd/16;let N:=V^d;refine⟨g,2*L2+2*N+⌈32*(N:ℝ)/cd⌉₊+4,W2+⌈32/cd⌉₊+4,by positivity,?_⟩
 intro Q hq l hl A as ac ag;let w:=Q.width;let B:=λ t=>(A t).image (· - Q.lo);have a1:=λ t=>(m2m Q (as t)).1;have c1:∀ t,c*Q.vol<=#(B t):=λ t=>by rw[(m2m Q (as t)).2];exact ac t
 have g1:∀ t,m2D (B t)=⊤:=λ t=>by
  have hd:B t - B t=A t - A t:=by ext z;simp only[B,Finset.mem_sub,mem_image];exact⟨λ⟨_,⟨x,hx,rfl⟩,_,⟨y,hy,rfl⟩,h⟩=>⟨x,hx,y,hy,by rw[<- h];abel⟩,λ⟨x,hx,y,hy,h⟩=>⟨x - Q.lo,⟨x,hx,rfl⟩,y - Q.lo,⟨y,hy,rfl⟩,by rw[<- h];abel⟩⟩
  rw[m2D,hd];exact ag t
 have n1:=λ t=>m2P hc0 (m2E Q.vP) (c1 t);let k:=l/2;have l3:(l:ℝ)<=3*k:=by exact_mod_cast show l<=3*k by omega
 let⟨v,t,hv,bx⟩:=h0 Q (λ i=>by have:=hq i;omega) k (by omega) (λ j:Fin k=>B ⟨j.1,by omega⟩) (λ _=>a1 _) (λ _=>c1 _)
 have:∀ i,NeZero (v i):=λ i=>⟨Nat.ne_of_gt (hv i).1⟩;let G:=∀ i,ZMod (v i);let⟨p,hs,g0,d0⟩:=m2n v hv;change Fintype.card G<=N at g0;have tt:k+Fintype.card G<=l:=by omega
 let S:=fSm (λ j:Fin (Fintype.card G)=>B ⟨k+j.1,by omega⟩);have gc:S.image p=univ:=by rw[m2e p];exact m2p _ (λ _=>(n1 _).image p) λ _=>m2o p hs (g1 _)
 have sb:∀ r∈S,∀ i,0<=r i/\r i<=N*w i:=λ r hr i=>by
  obtain⟨f,hf,rfl⟩:=(m2a _ r).mp hr;rw[Finset.sum_apply];refine⟨sum_nonneg λ j _=>(a1 _ (f j) (hf j) i).1,?_⟩
  exact (sum_le_sum (g:=λ _=>↑(w i)) λ j _=>by have:=(a1 _ (f j) (hf j) i).2;dsimp[w];omega).trans (by rw[sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul];exact mul_le_mul_of_nonneg_right (m2K g0) (cast_nonneg _))
 let M:=λ i=>⌊cd*k*w i⌋;let m:=λ i=>M i/2;let⟨rr,hp⟩:=m2i tt B n1;refine⟨t+(λ i=>m i*v i)+rr+l•Q.lo,λ _ hy=>?_⟩
 obtain⟨z,hz,rfl⟩:=m2I hy;let⟨r,hr,rz⟩:=m2I (gc.symm▸mem_univ (p z));have db:=d0 r z rz;let a:=λ i=>(z i - r i)/v i
 have bm:∀ i,m i+a i∈Icc 0 (M i):=λ i=>by
  let⟨r0,rh⟩:=sb r hr i;have zb:|z i|<=⌊g*l*w i⌋₊:=abs_le.mpr (by simpa[ZB.symm] using (ZB.mTF _ z).mp hz i)
  have h4:(|z i|:ℝ)<=g*l*w i:=(by exact_mod_cast zb:(|z i|:ℝ)<=⌊g*l*w i⌋₊).trans (Nat.floor_le (by positivity))
  have h12:(|a i|:ℝ)<=|z i|+N*w i:=(by exact_mod_cast (db i).2.trans (add_le_add le_rfl (abs_le.mpr ⟨by omega,rh⟩)))
  have w3:32<=cd*w i:=m2L cp (by have:=hq i;dsimp[w];omega);have mm:32*(N:ℝ)<=cd*l:=m2L cp (by omega)
  have h1:(1:ℝ)<=l:=(by exact_mod_cast show 1<=l by omega);have wp:=m2E (Q.wP i);have fl:=Int.sub_one_lt_floor (cd*k*w i)
  have h2:cd*l*w i<=3*(cd*k*w i):=(by have:0<=cd*w i:=(by positivity);nlinarith only[l3,this]);have lp:(32:ℝ)<=cd*l*w i:=(by nlinarith only[w3,h1])
  have hZ:2*|a i|+2<=M i:=(by exact_mod_cast show ((2*|a i|+2:ℤ):ℝ)<=M i by dsimp[M,g] at h4 ⊢;push_cast at h12 ⊢;nlinarith only[h12,h4,fl,h2,mm,wp,lp])
  let⟨_,_⟩:=abs_le.mp (le_rfl:|a i|<=|a i|);exact mem_Icc.mpr ⟨by dsimp[m];omega,by dsimp[m];omega⟩
 have m1:=bx (mem_image.mpr ⟨λ i=>m i+a i,mem_piFinset.mpr bm,rfl⟩);have ma:(t+(λ i=>(m i+a i)*v i)+r)+rr∈fSm B:=hp (mem_image_of_mem _ (by rw[m2g];exact add_mem_add m1 hr))
 rw[m2l] at ma;let⟨u,hA,ue⟩:=m2I ma
 rwa[show z+(t+(λ i=>m i*v i)+rr+l•Q.lo)=u by have h1:u=(u+-(l•Q.lo))+l•Q.lo:=(by abel);rw[h1,ue];ext i;have:=(db i).1;simp only[Pi.add_apply];linarith[add_mul (m i) (a i) ↑(v i)]]
lemma m2y {d} (A:Finset (ZV d)) (l0) (v w:Fin d->ℕ) (t0:ZV d) (hb:∀ b:ZV d,(∀ i,0<=b i/\b i<=w i)->t0+(λ i=>b i*v i)∈iSm l0 A) :
 ∀ (k:ℕ) (b:ZV d),(∀ i,0<=b i/\b i<=(k:ℤ)*w i)->(k:ℤ)•t0+(λ i=>b i*v i)∈iSm (k*l0) A
 | 0,b,h=>by have:b=0:=funext λ i=>by have:=h i;simp at this ⊢;omega
             subst this;rw[show (λ i:Fin d=>(0:ZV d) i*v i)=0 by ext i;simp];simp[iSm]
 | k+1,b,h=>by
  let c:=λ i=>min (b i) ↑(w i);let e:=λ i=>b i - c i
  have h1:=m2y A l0 v w t0 hb k e λ i=>by let⟨hl,hh⟩:=h i;dsimp[e,c];push_cast at hh;rcases le_total (b i) ↑(w i) with h | h <;> [rw[min_eq_left h,sub_self];rw[min_eq_right h]];exact⟨le_rfl,by positivity⟩;exact⟨by omega,by linarith⟩
  have ha:=add_mem_add h1 (hb c λ i=>⟨le_min (h i).1 (cast_nonneg _),min_le_right _ _⟩);rw[<- iSA,show k*l0+l0=(k+1)*l0 by ring] at ha
  rwa[show ((k:ℤ)•t0+(λ i=>e i*v i))+(t0+(λ i=>c i*v i))=((k+1:ℕ):ℤ)•t0+(λ i=>b i*v i) by ext i;simp only[Pi.add_apply,Pi.smul_apply,smul_eq_mul,e];push_cast;ring] at ha
lemma m2z {d} (A:Finset (ZV d)) (w:Fin d->ℕ) (hA:∀ a∈A,∀ i,|a i|<=w i):∀ (m:ℕ) {r:ZV d},r∈iSm m A->∀ i,|r i|<=m*w i
 | 0,_,r,_=>by rw[iSm,mem_singleton] at r;subst r;simp
 | m+1,_,r,i=>by obtain⟨y,hy,a,ha,rfl⟩:=Finset.mem_add.mp r;have:=m2z A w hA m hy i;have:=hA a ha i;have:=abs_add_le (y i) (a i);rw[Pi.add_apply];push_cast;linarith[add_mul (m:ℤ) 1 ↑(w i)]
lemma m2A:∀ (d:ℕ) (G:AddSubgroup (ZV d)) (v:Fin d->ℕ),(∀ i,1<=v i)->(∀ i,single i ↑(v i)∈G)->
 ∃ p:Fin d->ZV d,(∀ j,p j∈G)/\(∀ j i,i < j->p j i=0)/\(∀ j,1<=p j j)/\(∀ j i,0<=p j i/\p j i<=v i)/\(∀ x∈G,∃! n:ZV d,∑ j,n j•p j=x)
 | 0,_,_,_,_=>⟨Fin.elim0,λ j=>j.elim0,λ j=>j.elim0,λ j=>j.elim0,λ j=>j.elim0,λ _ _=>⟨Fin.elim0,by ext i;exact i.elim0,λ _ _=>by ext i;exact i.elim0⟩⟩
 | d+1,G,v,v1,vs=>by
  let q:ZV (d+1) →+ ℤ:=Pi.evalAddMonoidHom (λ _=>ℤ) 0;let⟨g,hg⟩:=m2r (G.map q)
  let⟨k0,hk0⟩:=mem_zmultiples_iff.mp (by rw[<- hg];exact⟨single 0 ↑(v 0),vs 0,by simp[q]⟩:(v 0:ℤ)∈zmultiples ↑g);rw[smul_eq_mul] at hk0
  have gp:1<=g:=by by_contra h;have:g=0:=(by omega);subst this;have:=v1 0;simp at hk0;omega
  have gl:(g:ℤ)<=v 0:=by have:=v1 0;have:1<=k0:=(by nlinarith);nlinarith
  obtain⟨a,qg,q1⟩:(g:ℤ)∈G.map q:=by rw[hg];exact mem_zmultiples _
  change a 0=g at q1;let e:ZV d →+ ZV (d+1):=⟨⟨λ y=>Fin.cons 0 y,by ext i;cases i using Fin.cases <;> rfl⟩,λ _ _=>by ext i;cases i using Fin.cases <;> simp⟩
  let⟨t,pm,pu,pd,po,pb⟩:=m2A d (G.comap e) (λ i=>v i.succ) (λ i=>v1 i.succ) λ i=>by rw[AddSubgroup.mem_comap,show e (single i ↑(v i.succ))=single i.succ ↑(v i.succ) by ext j;exact Fin.cases (by simp[e]) (λ _=>by simp[e,Pi.single_apply]) j];exact vs i.succ
  let b:ZV (d+1):=Fin.cons ↑g (λ i=>a i.succ % v i.succ)
  have pg:b∈G:=by rw[show b=a - ∑ i:Fin d,(a i.succ/v i.succ)•(single i.succ ↑(v i.succ):ZV (d+1)) by ext j;cases j using Fin.cases with | zero=>simp[b,q1] | succ i=>simp only[b,Fin.cons_succ,Pi.sub_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul];rw[sum_eq_single i (λ _ _ h=>by simp[Fin.succ_inj.ne.mpr h]) (by simp)];simp;have:=mul_ediv_add_emod (a i.succ) (v i.succ);linarith];exact G.sub_mem qg (G.sum_mem λ i _=>G.zsmul_mem (vs i.succ) _)
  have ps:∀ i:Fin d,0<=b i.succ/\b i.succ<=v i.succ:=λ i=>by have h3:(0:ℤ) < v i.succ:=(by have:=v1 i.succ;omega);exact⟨Int.emod_nonneg _ (ne_of_gt h3),le_of_lt (Int.emod_lt_of_pos _ h3)⟩
  let p:Fin (d+1)->ZV (d+1):=Fin.cons b (λ j=>e (t j))
  refine⟨p,Fin.cases pg pm,Fin.cases (λ i h=>(Fin.not_lt_zero i h).elim) (λ j'=>Fin.cases (λ _=>rfl) (λ i' h=>pu j' i' (Fin.succ_lt_succ_iff.mp h))),
   Fin.cases (by simp[p,b];exact gp) pd,Fin.cases (Fin.cases (by simp[p,b];exact_mod_cast gl) ps) (λ j'=>Fin.cases ⟨le_rfl,cast_nonneg _⟩ (po j')),?_⟩
  intro x hG;let⟨n,h0⟩:=mem_zmultiples_iff.mp (by rw[<- hg];exact⟨x,hG,rfl⟩:x 0∈zmultiples ↑g);rw[smul_eq_mul] at h0
  let x':=x - n•b;let y:ZV d:=λ i=>x' i.succ;have ey:e y=x':=by ext i;exact Fin.cases (by simp[e,x',b];linarith) (λ _=>rfl) i
  let⟨m,me,mu⟩:=pb y (by rw[AddSubgroup.mem_comap,ey];exact G.sub_mem hG (G.zsmul_mem pg n));refine⟨Fin.cons n m,?_,?_⟩
  . dsimp only;rw[Fin.sum_univ_succ];simp only[Fin.cons_zero,Fin.cons_succ,p];rw[show ∑ j,m j•e (t j)=e (∑ j,m j•t j) by simp only[map_sum,map_zsmul],me,ey];dsimp[x'];abel
  . intro n' hn'
    have e0:n' 0=n:=by have:=congrFun hn' 0;rw[Fin.sum_univ_succ] at this;simp only[Pi.add_apply,Pi.smul_apply,smul_eq_mul,p,b,Fin.cons_zero,Fin.cons_succ] at this;have t0:(∑ j,n' j.succ•e (t j)) 0=0:=(by rw[Finset.sum_apply];exact sum_eq_zero λ j _=>by simp[e]);rw[t0,add_zero] at this;nlinarith
    have m1:(λ j:Fin d=>n' j.succ)=m:=mu _ (by ext i;have hi:=congrFun hn' i.succ;rw[Fin.sum_univ_succ] at hi;simp only[Pi.add_apply,Pi.smul_apply,smul_eq_mul,p,Fin.cons_zero,Fin.cons_succ,Finset.sum_apply,e0] at hi ⊢;dsimp[e,y,x'] at hi ⊢;simp only[Fin.cons_succ] at hi;linarith)
    exact funext (Fin.cases e0 (congrFun m1))
lemma m2B {d} (V:ℕ) (w:Fin d->ℕ) (hw:Monotone w) (p:Fin d->ZV d) (hu:∀ j i,i < j->p j i=0) (hd:∀ j,1<=p j j) (ho:∀ j i,0<=p j i/\p j i<=V) (m y:ZV d) (hs:∑ j,m j•p j=y) (hy:∀ k,|y k|<=w k):∀ k,|m k|<=((d:ℤ)*V+1)^k.1*w k:=by
 have bd:∀ k,|m k|<=|y k|+∑ j∈univ.filter (· < k),|m j*p j k|:=λ k=>by
  let F:=univ.filter (· < k);have sp:y k=m k*p k k+∑ j∈F,m j*p j k:=by have h1:=(congrFun hs k).symm;simp[Finset.sum_apply] at h1;have sb:∑ j,m j*p j k=∑ j∈univ.filter (·<=k),m j*p j k:=(sum_subset (filter_subset _ _) λ j _ hj=>by rw[hu j k (lt_of_not_ge (by simpa using hj)),mul_zero]).symm;rw[h1,sb,show univ.filter (·<=k)=insert k F by ext j;simp[F,le_iff_eq_or_lt],sum_insert (by simp[F])]
  have ml:|m k|<=|m k*p k k|:=by have:=hd k;rw[abs_mul,abs_of_nonneg (by omega:0<=p k k)];nlinarith[abs_nonneg (m k)]
  exact ml.trans (by rw[show m k*p k k=y k - ∑ j∈F,m j*p j k by linarith];exact (abs_sub _ _).trans (add_le_add le_rfl (abs_sum_le_sum_abs _ _)))
 let B:ℤ:=↑d*V+1;have st:∀ t (k:Fin d),k.1<=t->|m k|<=B^t*w k:=by
  intro t;induction t with
  | zero=>intro k hk;have h0:univ.filter (· < k)=∅:=filter_eq_empty_iff.mpr λ j _ h=>by have:j.1 < k.1:=h;omega
          have h1:=bd k;rw[h0,sum_empty,add_zero] at h1;simpa using h1.trans (hy k)
  | succ t ih=>
   intro k hk;let F:=univ.filter (· < k)
   have h1:∑ j∈F,|m j*p j k|<=∑ _j∈F,↑V*B^t*w k:=sum_le_sum λ j hj=>by have jk:=(mem_filter.mp hj).2;have mj:=ih j (by have:j.1 < k.1:=jk;omega);have pj:=ho j k;rw[abs_mul,abs_of_nonneg pj.1];have:=mul_le_mul (mj.trans (mul_le_mul_of_nonneg_left (m2K (hw (le_of_lt jk))) (by positivity))) pj.2 pj.1 (by positivity);linarith
   have sl:∑ j∈F,|m j*p j k|<=↑d*V*B^t*w k:=h1.trans (by rw[sum_const,nsmul_eq_mul];have:=mul_le_mul_of_nonneg_right (m2K (by simpa using card_le_univ F)) (show (0:ℤ)<=V*B^t*w k by positivity);linarith)
   have y1:|y k|<=B^t*w k:=(hy k).trans (le_mul_of_one_le_left (cast_nonneg _) (one_le_pow₀ (by dsimp[B];exact le_add_of_nonneg_left (by positivity))))
   have:=bd k;have:B^(t+1)*w k=B^t*w k+↑d*V*B^t*w k:=(by dsimp[B];ring);linarith
 exact λ k=>st k.1 k le_rfl
lemma m2F {d} (V:ℕ) (w:Fin d->ℕ) (hw:Monotone w) (p:Fin d->ZV d) (hu:∀ j i,i < j->p j i=0) (hb:∀ j i,0<=p j i/\p j i<=V) (R:ℝ) (hR:0<=R) (m:ZV d) (hm:∀ j,(|m j|:ℝ)<=R*w j):∀ k,(|(∑ j,m j•p j) k|:ℝ)<=d*V*R*w k:=λ k=>by
 simp[Finset.sum_apply]
 refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (g:=λ _=>↑V*R*w k) λ j _=>?_).trans_eq (by rw[sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul];ring))
 by_cases jk:j<=k
 . have pa:|(p j k:ℝ)|<=V:=(by rw[abs_of_nonneg (by exact_mod_cast (hb j k).1:(0:ℝ)<=p j k)];exact_mod_cast (hb j k).2);rw[abs_mul];have:=mul_le_mul ((hm j).trans (mul_le_mul_of_nonneg_left (m2R (hw jk)) hR)) pa (abs_nonneg _) (by positivity);linarith
 . rw[hu j k (lt_of_not_ge jk),Int.cast_zero,mul_zero,abs_zero];positivity
theorem lnr (d:ℕ) (hd:1<=d) {c:ℝ} (hc0:0 < c) (hc1:c<=1) :
 ∃ (κ:ℕ) (γ:ℝ) (L₀ W₀:ℕ),1<=κ/\0 < γ/\∀ (Q:ZB d) (A:Finset (ZV d)),
 (∀ i,W₀<=Q.width i)->A⊆Q.tF->(0:ZV d)∈A->c*(Q.vol:ℝ)<=(A.card:ℝ)->
 ∃ (P:GAP (ZV d) d),P.iC/\P.iS/\(∀ i,P.step i∈AddSubgroup.closure (A:Set (ZV d)))/\
 (∀ x∈AddSubgroup.closure (A:Set (ZV d)),∃! n:ZV d,∑ i,n i•P.step i=x)/\
 (∀ x∈Q.tF,x∈AddSubgroup.closure (A:Set (ZV d))->x∈P.tF)/\
 (∃ t:ZV d,∀ x∈P.tF,∀ i,(κ:ℤ)*Q.lo i<=(x - t) i/\(x - t) i<=(κ:ℤ)*Q.hi i)/\
 (∀ i,(P.width i:ℝ)<=(κ:ℝ)*(Q.width i:ℝ))/\
 (∀ ℓ:ℕ,L₀<=ℓ->∀ (hγℓ:0<=γ*(ℓ:ℝ)) (hcent:P.iC),
 ∃ x₀:ZV d,(P.rS (γ*(ℓ:ℝ)) hγℓ hcent).tF.image (·+x₀)⊆iSm ℓ A):=by
 classical
 have _:=hc1;let⟨cd,V,L2,W2,cp,vp,h2⟩:=m2x d hd hc0;let M:=V^d;let o:=L2+⌈1/cd⌉₊+1;have lp:1<=o:=by omega
 let C:=(d*V+1)^d;have c1:1<=C:=one_le_pow₀ (by omega);let B:=2*d*V*C;let K:=2*B+1;let g:ℝ:=1/(32*d*V*C*o)
 have dr:=m2E hd;have vr:=m2E vp;have cr:=m2E c1;have lr:=m2E lp;refine⟨K,g,4*M+16*M*o+32*o+4,W2+2,by omega,by positivity,?_⟩
 intro Q A hq as h0 ac;let w:=Q.width;let H:=m2C (A:Set (ZV d))
 let⟨v,t',hv,db⟩:=h2 Q (λ i=>by have:=hq i;omega) o (by omega) (λ _=>A.image (· - Q.lo)) (λ _=>(m2m Q as).1) (λ _=>by rw[(m2m Q as).2];exact ac);let t:=t'+o•Q.lo
 have du:∀ b:ZV d,(∀ i,0<=b i/\b i<=w i)->t+(λ i=>b i*v i)∈iSm o A:=λ b hb=>by
  have hm:=db (mem_image.mpr ⟨b,mem_piFinset.mpr λ i=>mem_Icc.mpr ⟨(hb i).1,(hb i).2.trans (Int.le_floor.mpr (by have:=m2L cp (b:=1) (by omega:⌈1/cd⌉₊<=o);push_cast;nlinarith[cast_nonneg (α:=ℝ) (w i)]))⟩,rfl⟩)
  rw[m2l,m2b] at hm;let⟨y,hA,hE⟩:=m2I hm;rwa[show t+(λ i=>b i*v i)=y by have h1:y=(y+-(o•Q.lo))+o•Q.lo:=(by abel);rw[h1,hE];dsimp[t];abel]
 have tg:t∈H:=by have h:=du 0 λ _=>⟨le_rfl,cast_nonneg _⟩;rw[show t+(λ i=>(0:ZV d) i*v i)=t by ext i;simp] at h;exact m2q A o h
 have vg:∀ i,single i ↑(v i)∈H:=λ i=>by
  have h:=du (single i 1) λ j=>by simp[Pi.single_apply];split_ifs <;> [exact⟨by omega,m2K (Q.wP j)⟩;exact⟨le_rfl,cast_nonneg _⟩]
  rw[show (λ j:Fin d=>((single i (1:ℤ):ZV d) j)*v j)=single i ↑(v i) by ext j;by_cases ji:j=i <;> simp[ji]] at h;simpa[add_sub_cancel_left] using H.sub_mem (m2q A o h) tg
 let s:=Tuple.sort w;have sm:=Tuple.monotone_sort w;let e:ZV d ≃+ ZV d:=⟨⟨λ x i=>x (s i),λ y i=>y (s.symm i),λ _=>by ext i;simp,λ _=>by ext i;simp⟩,λ _ _=>rfl⟩
 let⟨q,pm,pu,pd,po,pb⟩:=m2A d (H.map (e:ZV d →+ ZV d)) (λ i=>v (s i)) (λ i=>(hv (s i)).1) λ i=>⟨single (s i) ↑(v (s i)),vg (s i),by ext j;simp[e,Pi.single_apply]⟩
 have hV:∀ j i,0<=q j i/\q j i<=V:=λ j i=>⟨(po j i).1,(po j i).2.trans (m2K (hv (s i)).2)⟩
 let P:GAP (ZV d) d:=⟨0,λ i=>e.symm (q (s.symm i)),λ i=>-(↑C*w i),λ i=>↑C*w i,λ i=>by have:(0:ℤ)<=C*w i:=(by positivity);linarith⟩
 have pc:P.iC:=⟨rfl,λ i=>by have:(0:ℤ)<=C*w i:=(by positivity);exact⟨by dsimp[P];linarith,this⟩⟩
 have p1:∀ i,P.step i∈H:=λ i=>by let⟨u,hG,hE⟩:=pm (s.symm i);simpa[P,<- hE] using hG
 have e1:∀ n:ZV d,e (∑ i,n i•P.step i)=∑ j,n (s j)•q j:=λ n=>by rw[map_sum];exact (Equiv.sum_comp s _).symm.trans (sum_congr rfl λ j _=>by rw[map_zsmul];simp[P])
 have fw:∀ (R:ℝ),0<=R->∀ n:ZV d,(∀ i,(|n i|:ℝ)<=R*w i)->∀ i,(|(∑ j,n j•P.step j) i|:ℝ)<=d*V*R*w i:=λ R hR n hn i=>by have h1:=m2F V (λ j=>w (s j)) sm q pu hV R hR (λ j=>n (s j)) (λ j=>hn (s j)) (s.symm i);rw[<- e1 n] at h1;simpa[e] using h1
 have q0:=(ZB.mTF Q 0).mp (as h0);have qa:∀ x∈Q.tF,∀ i,|x i|<=w i:=λ x hx i=>by let⟨a1,a2⟩:=(ZB.mTF Q x).mp hx i;let⟨b1,b2⟩:=q0 i;rw[Pi.zero_apply] at b1 b2;have:↑(w i)=Q.hi i - Q.lo i+1:=(by unfold w ZB.width;omega);exact abs_le.mpr ⟨by omega,by omega⟩
 have:∀ i,NeZero (v i):=λ i=>⟨Nat.ne_of_gt (hv i).1⟩;let⟨p,_,g0,d0⟩:=m2n v hv;let U:=H.map p;let b:=Fintype.card ↥U
 have kc:b<=M:=(Fintype.card_le_of_injective Subtype.val Subtype.val_injective).trans g0;let W:=A.attach.image λ a=>(⟨p a.1,a.1,m2S a.2,rfl⟩:↥U)
 have kc1:iSm b W=univ:=by
  have y0:(0:↥U)∈W:=mem_image.mpr ⟨⟨0,h0⟩,mem_attach _ _,Subtype.ext (map_zero p)⟩;rw[<- m2b];refine m2p _ (λ _=>⟨0,y0⟩) λ _=>?_
  have gl:H<=((m2D W).map U.subtype).comap p:=(closure_le _).mpr λ a ha=>⟨⟨p a,a,AddSubgroup.subset_closure ha,rfl⟩,m2S (by simpa using sub_mem_sub (mem_image.mpr ⟨⟨a,mem_coe.mp ha⟩,mem_attach _ _,rfl⟩) y0),rfl⟩
  rw[eq_top_iff];intro y _;let⟨z,zg,hE⟩:=y.2;let⟨y',hS,hE'⟩:=gl zg;rwa[<- (Subtype.ext (hE'.trans hE):y'=y)]
 refine⟨P,pc,⟨rfl,λ _=>rfl⟩,p1,?_,?_,?_,?_,?_⟩
 . intro x hG;let⟨m,me,mu⟩:=pb (e x) ⟨x,hG,rfl⟩;exact⟨λ i=>m (s.symm i),e.injective (by rw[e1];simpa using me),λ n hn=>by have hm':(λ j=>n (s j))=m:=mu _ (by dsimp only;rw[<- e1 n,hn]);ext i;simpa using congrFun hm' (s.symm i)⟩
 . intro x hQ hG;let⟨m,me,_⟩:=pb (e x) ⟨x,hG,rfl⟩;have hb:=m2B V (λ j=>w (s j)) sm q pu pd hV m (e x) me λ k=>qa x hQ (s k)
   refine mem_image.mpr ⟨λ i=>m (s.symm i),(ZB.mTF _ _).mpr λ i=>abs_le.mp ((by simpa using hb (s.symm i):|m (s.symm i)|<=(↑d*V+1)^(s.symm i).1*w i).trans (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.pow_le_pow_right (by omega:1<=d*V+1) (le_of_lt (s.symm i).2)) (cast_nonneg _))),by simp only[GAP.eval,P,zero_add];exact e.injective (by rw[e1];simpa using me)⟩
 . let D:=λ i=>Q.hi i - Q.lo i;refine⟨λ i=>-(↑K*Q.lo i) - B*D i,λ _ hx i=>?_⟩;obtain⟨n,hn,rfl⟩:=m2I hx
   have xz:|(∑ j,n j•P.step j) i|<=↑d*V*C*w i:=(by exact_mod_cast fw C (cast_nonneg _) n (λ j=>by exact_mod_cast abs_le.mpr ((ZB.mTF P.cB n).mp hn j)) i)
   have de:↑(w i)=D i+1:=(by have:=Q.hle i;unfold w ZB.width;dsimp[D];omega)
   have xb:|(∑ j,n j•P.step j) i|<=B*D i:=xz.trans (by have h1:↑(w i)<=2*D i:=(by have:=hq i;dsimp[w] at de ⊢;omega);have h2:(0:ℤ)<=d*V*C:=(by positivity);dsimp[B];nlinarith only[h1,h2])
   have d0:0<=D i:=(by have:=Q.hle i;dsimp[D];omega);let⟨lx,hx⟩:=abs_le.mp xb;simp only[GAP.eval,P,zero_add,Pi.sub_apply];dsimp[K,D] at*;exact⟨by linarith,by linarith⟩
 . intro i;have h3:(C:ℤ)<=d*V*C:=(by exact_mod_cast (by simpa using Nat.mul_le_mul_right C (Nat.mul_pos hd vp):C<=d*V*C))
   have hw:(1:ℤ)<=w i:=(by exact_mod_cast Q.wP i);unfold GAP.width;exact_mod_cast Int.toNat_le.mpr (by dsimp[GAP.cB,P,K,B,w] at hw ⊢;nlinarith only[hw,h3,cast_nonneg (α:=ℤ) C])
 . intro l hl gl _;let k:=(l - M)/o;have k1:1<=k:=div_pos (by omega) lp;have km:k*o+b<=l:=(by have:k*o<=l - M:=Nat.div_mul_le_self (l - M) o;omega)
   have lk:l<=4*o*k:=(by have h1:l<=2*(l - M):=(by omega);have h2:l - M < k*o+o:=lt_div_mul_add (a:=l - M) lp;nlinarith only[h1,h2,k1])
   have hM:4*(M:ℝ)<=k:=(by exact_mod_cast show 4*M<=k by have:16*M*o<=l:=(by omega);nlinarith only[this,lk,lp])
   have h8:(8:ℝ)<=k:=(by exact_mod_cast show 8<=k by have:32*o<=l:=(by omega);nlinarith only[this,lk,lp])
   have hg:(d:ℝ)*V*(g*l*C)<=k/8:=(by have:(l:ℝ)<=4*o*k:=(by exact_mod_cast lk);dsimp[g];rw[show (d:ℝ)*V*(1/(32*d*V*C*o)*l*C)=l/(32*o) by field_simp[ne_of_gt dr,ne_of_gt vr,ne_of_gt cr,ne_of_gt lr],div_le_div_iff₀ (by positivity) (by positivity)];linarith)
   let f:=λ i=>((k:ℤ)*w i)/2;refine⟨(k:ℤ)•t+(λ i=>f i*v i),λ _ hy=>?_⟩;obtain⟨_,hz,rfl⟩:=m2I hy;obtain⟨n,hn,rfl⟩:=m2I hz;simp only[GAP.eval,GAP.rS,zero_add]
   let z:=∑ j,n j•P.step j;have zg:z∈H:=H.sum_mem λ j _=>H.zsmul_mem (p1 j) (n j)
   have h1:W.image U.subtype=A.image p:=(by ext y;simp only[W,mem_image,mem_attach,true_and];exact⟨λ⟨_,⟨⟨a,ha⟩,rfl⟩,h⟩=>⟨a,ha,h⟩,λ⟨a,ha,h⟩=>⟨⟨p a,a,m2S ha,rfl⟩,⟨⟨a,ha⟩,rfl⟩,h⟩⟩)
   have h2:(iSm b A).image p=(iSm b W).image U.subtype:=(by simp only[<- m2b,m2e,h1])
   let⟨r,rm,rp⟩:=m2I (h2.symm▸mem_image_of_mem U.subtype (kc1.symm▸mem_univ (⟨p z,z,zg,rfl⟩:↥U)));have db:=d0 r z rp;let a:=λ i=>(z i - r i)/v i
   have nb:∀ j,(|n j|:ℝ)<=g*l*C*w j:=λ j=>by let⟨hl',hh'⟩:=(ZB.mTF _ n).mp hn j;dsimp[GAP.cB,GAP.rS,P] at hl' hh';exact abs_le.mpr ⟨by simpa[mul_assoc] using (Int.le_ceil _).trans (Int.cast_le (R:=ℝ).mpr hl'),by simpa[mul_assoc] using (Int.cast_le (R:=ℝ).mpr hh').trans (Int.floor_le _)⟩
   have bm:∀ i,0<=f i+a i/\f i+a i<=k*w i:=λ i=>by
    have fz:(|z i|:ℝ)<=↑k/8*w i:=(fw (g*l*C) (by positivity) n nb i).trans (mul_le_mul_of_nonneg_right hg (cast_nonneg _))
    have ra:|r i|<=M*w i:=(m2z A w (λ a ha j=>qa a (as ha) j) b rm i).trans (mul_le_mul_of_nonneg_right (m2K kc) (cast_nonneg _))
    have al:(|a i|:ℝ)<=|z i|+M*w i:=(by exact_mod_cast (db i).2.trans (add_le_add le_rfl ra));have wp:(1:ℝ)<=w i:=(by exact_mod_cast Q.wP i)
    have bz:2*|a i|+2<=k*w i:=(by exact_mod_cast show ((2*|a i|+2:ℤ):ℝ)<=((k:ℤ)*w i:ℤ) by push_cast at al ⊢;nlinarith only[al,fz,hM,h8,wp])
    let⟨_,_⟩:=abs_le.mp (le_rfl:|a i|<=|a i|);exact⟨by dsimp[f];omega,by dsimp[f];omega⟩
   refine iSS h0 km ?_;rw[show z+((k:ℤ)•t+(λ i=>f i*v i))=((k:ℤ)•t+(λ i=>(f i+a i)*v i))+r by ext i;have:=(db i).1;simp only[Pi.add_apply];linarith[add_mul (f i) (a i) ↑(v i)],iSA]
   exact add_mem_add (m2y A o v w t du k _ bm) rm
end
end E186
namespace E186
def DJH (johnC:ℕ->ℕ):Prop:=(∀d,1<=johnC d)/\∀(d:ℕ) (G:AddSubgroup (ZV d)) (B:Set (RV d)),(0:RV d)∈B->Convex ℝ B->(∀x∈B,-x∈B)->Bornology.IsBounded B->∃(k:ℕ) (_:k<=d) (w:Fin k->ZV d) (N:Fin k->ℕ),(∀i,w i∈G)/\(∀i,1<=N i)/\LinearIndependent ℝ (λi=>zR (w i))/\(∀c:ZV k,(∀i,|c i|<(N i:ℤ))->zR (∑i,c i•w i)∈B)/\(∀x:ZV d,x∈G->zR x∈B->∃c:ZV k,(∀i,|c i|<(johnC d*N i:ℤ))/\∑i,c i•w i=x)
def QPH:Prop:=∀(D:ℕ) (c:ZV (D+1)),c≠0->∃(p:ZV (D+1) →+ ZV D) (c0:ZV (D+1)),c0≠0/\(∃m:ℤ,m≠0/\m•c0=c)/\Function.Surjective p/\(∀x:ZV (D+1),p x=0<->∃t:ℤ,t•c0=x)
section
open Function
open Fintype (piFinset card_piFinset card_coe)
open Real (cos)
open Nat (mul_le_mul_left mul_le_mul_right cast_pos cast_nonneg sub_le lt_succ_of_le mul_pos cast_le)
open ZMod (natCast_zmod_val)
open Int (toNat_of_nonneg)
open Complex (exp I)
open Pi (single single_apply)
open Fin (addCases)
open GAP (cB nS)
lemma m30 {a b} [AddCommMonoid b] {s:Finset a} {f g:a->b} (h:∀x∈s,f x=g x):∑x∈s,f x=∑x∈s,g x:=sum_congr rfl h
lemma m31 {a b} [DecidableEq b] {s:Finset a} {f:a->b} {y} (h:y∈s.image f):∃x∈s,f x=y:=mem_image.mp h
lemma m32 {a} {s:Finset a} {p:a->Prop} [DecidablePred p] {x} (h:x∈s.filter p):x∈s/\p x:=mem_filter.mp h
lemma m33 {a b} [DecidableEq b] {s:Finset a} {f:a->b} (h:Set.InjOn f s):#(s.image f)=#s:=card_image_of_injOn h
lemma m34 {a b} [DecidableEq b] (s:Finset a) {f:a->b} (h:Injective f):#(s.image f)=#s:=card_image_of_injective s h
lemma m35 {a} {s t:Finset a} (h:s⊆t):#s<=#t:=card_le_card h
lemma m36 {a b} [CommMonoid b] {s:Finset a} {f g:a->b} (h:∀x∈s,f x=g x):∏x∈s,f x=∏x∈s,g x:=prod_congr rfl h
lemma m37 {d} {B:ZB d} {x}:x∈B.tF<->∀i,B.lo i<=x i/\x i<=B.hi i:=ZB.mTF B x
lemma m38 {t} [Fintype t] [DecidableEq t] {a:t->Type*} {f:∀i,Finset (a i)} {x}:x∈piFinset f<->∀i,x i∈f i:=Fintype.mem_piFinset
lemma m3a (A:Finset ℤ):∀k,iSm k A=k•A
 | 0=>by simp[iSm];rfl
 | k+1=>by rw[iSm,m3a A k,succ_nsmul]
lemma m3b {A:Finset ℤ}:∀{s} (a:Fin s->ℤ),(∀i,a i∈A)->(∑i,a i)∈iSm s A
 | 0,_,_=>by simp[iSm]
 | _+1,a,h=>by rw[Fin.sum_univ_castSucc,iSm];exact add_mem_add (m3b (λi=>a i.castSucc) λi=>h _) (h _)
lemma m3c {A:Finset ℤ} (hA:A.Nonempty) {K:ℝ} (hK:(#(A+A):ℝ)<=K*#A) (m n:ℕ) :
 (#(iSm m A-iSm n A):ℝ)<=K^(m+n)*#A:=by
 have h1:(((#(m•A-n•A):ℚ≥0):ℝ))<=((((#(A+A):ℚ≥0)/#A)^(m+n)*#A:ℚ≥0):ℝ) :=
  NNRat.cast_le.mpr (pluennecke_ruzsa_inequality_nsmul_sub_nsmul_add hA A m n)
 rw[m3a,m3a];have:=(div_le_iff₀ (cast_pos.mpr hA.card_pos)).mpr hK;exact le_trans (by simpa[NNRat.cast_mul,NNRat.cast_pow,NNRat.cast_div]using h1) (by gcongr)
lemma m3d {d} (s:ℕ) (P:GAP ℤ d) :
 P.iSP s<->∀c:ZV d,(∀i,|c i|<=(s:ℤ)*(P.hi i-P.lo i))->(∑i,c i•P.step i)=0->c=0:=by
 constructor
 . intro hP c hc hs
   let a i:=if 0<=c i then (s:ℤ)*P.lo i+c i else (s:ℤ)*P.lo i;let b i:=if 0<=c i then (s:ℤ)*P.lo i else (s:ℤ)*P.lo i-c i;have h0 i:(0:ℤ)<=(s:ℤ)*(P.hi i-P.lo i):=mul_nonneg (cast_nonneg s) (sub_nonneg.mpr (P.hle i));have h1:a∈(P.nS s).cB.tF:=m37.mpr λi=>by have:=abs_le.mp (hc i);have:=h0 i;dsimp[a,cB,nS];split_ifs<;>constructor<;>linarith
   have h2:b∈(P.nS s).cB.tF:=m37.mpr λi=>by have:=abs_le.mp (hc i);have:=h0 i;dsimp[b,cB,nS];split_ifs<;>constructor<;>linarith
   have hd:a-b=c:=funext λi=>by dsimp[a,b];split_ifs<;>ring
   have he:(P.nS s).eval a=(P.nS s).eval b:=by
    dsimp only[GAP.eval,nS];rw[add_right_inj];apply sub_eq_zero.mp;rw[<-sum_sub_distrib];exact(m30 λi _=>by rw[<-sub_smul];exact congrArg (·•P.step i) (congrFun hd i)).trans hs
   rw[<-hd,hP h1 h2 he,sub_self]
 . intro h a ha b hb he;rw[mem_coe,m37]at ha hb;dsimp only[GAP.eval,nS]at he
   have h2:=sub_eq_zero.mpr (add_left_cancel he);rw[<-sum_sub_distrib]at h2;simp_rw[<-sub_smul]at h2;exact sub_eq_zero.mp (h (a-b) (λi=>by have x:=ha i;have y:=hb i;dsimp[cB,nS]at x y;rw[Pi.sub_apply,abs_le];constructor<;>linarith) h2)
lemma m3e {d s1 s2} {P:GAP ℤ d} (hs:s1<=s2) (hP:P.iSP s2):P.iSP s1 :=
 (m3d s1 P).mpr λc hc=>(m3d s2 P).mp hP c λi=>le_trans (hc i) (mul_le_mul_of_nonneg_right (by exact_mod_cast hs) (sub_nonneg.mpr (P.hle i)))
lemma m3f {d s} {P:GAP ℤ d} (hs:1<=s) (hP:P.iSP s):P.iP :=
 λ_ h1 _ h2 he=>m3e hs hP (by simpa[nS,cB]using h1) (by simpa[nS,cB]using h2) (by simpa[nS,GAP.eval]using he)
lemma m3g {d} {P:GAP ℤ d} (hP:P.iSP 2) {a b c e:ZV d}
 (h1:a∈P.cB.tF) (h2:b∈P.cB.tF) (h3:c∈P.cB.tF) (h4:e∈P.cB.tF)
 (he:P.eval a+P.eval b=P.eval c+P.eval e):a+b=c+e:=by
 rw[m37]at h1 h2 h3 h4;dsimp only[GAP.eval]at he;have hb:(∑i,a i•P.step i)+(∑i,b i•P.step i)-((∑i,c i•P.step i)+(∑i,e i•P.step i))=0:=by linarith
 simp only[<-sum_add_distrib,<-sum_sub_distrib]at hb;exact sub_eq_zero.mp ((m3d 2 P).mp hP _ (λi=>by have:=h1 i;have:=h2 i;have:=h3 i;have:=h4 i;dsimp[cB]at *;rw[abs_le];omega) ((m30 λi _=>by simp only[Pi.sub_apply,Pi.add_apply,sub_smul,add_smul]).trans hb))
def m3h {d} (P:GAP ℤ d):GAP ℤ d:=⟨P.base+∑i,P.lo i•P.step i,P.step,0,λi=>P.hi i-P.lo i,λi=>sub_nonneg.mpr (P.hle i)⟩
lemma m3i {d} (P:GAP ℤ d) (n:ZV d):(m3h P).eval n=P.eval (n+P.lo):=by
 dsimp[GAP.eval,m3h];rw[add_assoc,<-sum_add_distrib];congr 1;exact m30 λi _=>by ring
lemma m3j {d} (P:GAP ℤ d):(m3h P).tF=P.tF:=by
 ext x;simp only[GAP.tF,mem_image,m37,cB];constructor
 . rintro⟨n,hn,rfl⟩;exact⟨n+P.lo,λi=>by have:=hn i;dsimp[m3h]at this ⊢;omega,(m3i P n).symm⟩
 . rintro⟨n,hn,rfl⟩;exact⟨n-P.lo,λi=>by have:=hn i;dsimp[m3h]at *;omega,by rw[m3i,sub_add_cancel]⟩
lemma m3k {d} (P:GAP ℤ d):(m3h P).vol=P.vol:=by unfold GAP.vol ZB.vol;exact m36 λi _=>by simp[ZB.width,cB,m3h]
lemma m3l {d} (s:ℕ) (P:GAP ℤ d):(m3h P).iSP s<->P.iSP s:=by simp[m3d,m3h]
lemma m3m {a b c:ℕ} (hb:0<b) (h:a/b=c):(c:ℤ)*b<=a/\(a:ℤ)<(c+1:ℤ)*b:=by
 have h1:=Nat.div_mul_le_self a b;have h2:=Nat.lt_div_mul_add (a:=a) hb;rw[h]at h1 h2;exact⟨by exact_mod_cast h1,by exact_mod_cast (show a<(c+1)*b by rw[Nat.add_mul,one_mul];omega)⟩
lemma m3n {k C:ℕ} {M:Fin k->ℕ} (hM:∀i,1<=M i):(∏i,(2*(C*M i)-1))<=(2*C)^k*∏i,(2*M i-1) :=
 (prod_le_prod' (g:=λi=>(2*C)*(2*M i-1)) λi _=>by have:=hM i;exact le_trans (sub_le _ 1) (by rw[<-mul_assoc];exact mul_le_mul_left _ (by omega))).trans_eq (by rw[prod_mul_distrib,prod_const,card_univ,Fintype.card_fin])
lemma m3o {α β:Type*} [DecidableEq β] [Fintype β] (S:Finset α) (f:α->β) (hβ:Nonempty β) :
 ∃b,#S<=Fintype.card β*#(S.filter λx=>f x=b):=by
 by_contra h;push Not at h;have t:=sum_lt_sum_of_nonempty (univ_nonempty_iff.mpr hβ) λb _=>h b;rw[<-mul_sum,<-card_eq_sum_card_fiberwise (f:=f) (t:=univ) λ_ _=>mem_univ _,sum_const,card_univ,smul_eq_mul]at t;exact lt_irrefl _ t
lemma m3p (s:ℕ) (hs:1<=s) {A:Finset ℤ} (hA:A.Nonempty) {N:ℕ} (hNp:Nat.Prime N) (hN:#(iSm s A-iSm s A)<=N) :
 ∃(A':Finset ℤ) (f:ℤ->ZMod N),A'⊆A/\ #A<=s*#A'/\Set.InjOn f A' /\
  ∀(a b:Fin s->ℤ),(∀i,a i∈A')->(∀i,b i∈A')->((∑i,a i=∑i,b i)<->(∑i,f (a i)=∑i,f (b i))):=by
 classical
 let D:=iSm s A-iSm s A;let Z:=D.erase 0;have h0:(0:ℤ)∈D:=by have⟨a,ha⟩:=hA;have h:=m3b (λ_:Fin s=>a) λ_=>ha;simpa[D]using sub_mem_sub h h
 have h1:#Z<=N-1:=by rw[show #Z=#D-1 from card_erase_of_mem h0];exact Nat.sub_le_sub_right hN 1
 have h2:∀z∈Z,-z∈Z:=λz hz=>by rw[mem_erase]at hz ⊢;obtain⟨x,hx,y,hy,rfl⟩:=mem_sub.mp hz.2;exact⟨neg_ne_zero.mpr hz.1,by rw[show -(x-y)=y-x by ring];exact sub_mem_sub hy hx⟩
 have⟨q,hqg,hqp⟩:=Nat.exists_infinite_primes (max (D.sup λz=>z.natAbs) N+1);have hM:=lt_of_le_of_lt (le_max_left _ _) (Nat.lt_of_succ_le hqg);have hq:=lt_trans hNp.pos (lt_of_le_of_lt (le_max_right _ _) (Nat.lt_of_succ_le hqg));have:Fact q.Prime:=⟨hqp⟩;let Q:=(q-1)/N;let B:Finset (ZMod q):=(Z×ˢIcc 1 Q).image λp=>(((p.2*N:ℕ):ZMod q)*((p.1:ZMod q))⁻¹);have hB:#B<#(univ.erase (0:ZMod q)):=by
  rw[card_erase_of_mem (mem_univ _),card_univ,ZMod.card q];have:1<=Q:=(Nat.le_div_iff_mul_le hNp.pos).mpr (show 1*N<=q-1 by have:=lt_of_le_of_lt (le_max_right _ _) (Nat.lt_of_succ_le hqg);omega);have:N*Q<=q-1:=Nat.mul_div_le (q-1) N;have:#B<=#Z*Q:=le_trans card_image_le (by simp[card_product]);have:=mul_le_mul_right Q h1;have:(N-1)*Q+Q=N*Q:=by rw[<-add_one_mul,Nat.sub_add_cancel hNp.one_lt.le]
  omega
 have⟨m,hm,hb⟩:∃m∈univ.erase (0:ZMod q),m ∉ B:=by by_contra h;push Not at h;exact absurd (m35 λx hx=>h x hx) (not_le_of_gt hB)
 have hm0:=(mem_erase.mp hm).1;let l:=m.val;have hlc:=natCast_zmod_val m;have hz:∀z∈D,z≠0->(z:ZMod q)≠0:=λz h hn h0=>hn (Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd z q).mp h0) (by have:=lt_of_le_of_lt (le_sup (f:=λx:ℤ=>x.natAbs) h) hM;have:=Int.abs_eq_natAbs z;omega));have hgp:∀z∈Z,∀w:ℤ,0<w->w<q->(N:ℤ) ∣ w->((l:ℤ)*z:ZMod q)≠w:=by
  intro z h w hp hl ⟨ki,hk⟩ he;have hkp:0<ki:=by nlinarith
  let k:=ki.toNat;have hw:w=((k*N:ℕ):ℤ):=by push_cast;rw[toNat_of_nonneg hkp.le];linarith
  have hkn:k*N<=q-1:=by exact_mod_cast (show ((k*N:ℕ):ℤ)<=((q-1:ℕ):ℤ) by omega)
  have ht:m*(z:ZMod q)=((k*N:ℕ):ZMod q):=by rw[hw]at he;push_cast at he;rw[hlc]at he;simpa[Nat.cast_mul]using he
  apply hb;rw[show m=((k*N:ℕ):ZMod q)*((z:ZMod q))⁻¹ by rw[<-ht,mul_assoc,mul_inv_cancel₀ (hz z (mem_erase.mp h).2 (mem_erase.mp h).1),mul_one]];exact mem_image.mpr ⟨(z,k),mem_product.mpr ⟨h,mem_Icc.mpr ⟨by omega,(Nat.le_div_iff_mul_le hNp.pos).mpr hkn⟩⟩,rfl⟩
 have hg:∀z∈Z,∀w:ℤ,w≠0->|w|<q->(N:ℤ) ∣ w->((l:ℤ)*z:ZMod q)≠w:=by
  intro z h w hn ha hd he;rcases lt_or_gt_of_ne hn with t | t
  . apply hgp (-z) (h2 z h) (-w) (by omega) (by rw[abs_lt]at ha;omega) (dvd_neg.mpr hd);push_cast at he ⊢;rw[mul_neg,he]
  . exact hgp z h w t (by rw[abs_lt]at ha;omega) hd he
 let r (x:ℤ):=((l:ℤ)*x) % q;have hr x:0<=r x/\r x<q:=⟨Int.emod_nonneg _ (by omega),Int.emod_lt_of_pos _ (by omega)⟩;let bk (x:ℤ):Fin s:=⟨(s*(r x).toNat)/q,(Nat.div_lt_iff_lt_mul hq).mpr (Nat.mul_lt_mul_of_pos_left (by have:=hr x;omega) (by omega))⟩;have⟨j,hj⟩:=m3o A bk ⟨⟨0,hs⟩⟩;rw[Fintype.card_fin]at hj;let A':=A.filter λx=>bk x=j;let f (x:ℤ):ZMod N:=r x;have hf:∀(a b:Fin s->ℤ),(∀i,a i∈A')->(∀i,b i∈A')->((∑i,a i=∑i,b i)<->(∑i,f (a i)=∑i,f (b i))):=by
  intro a b ha hb;let w:=(∑i,r (a i))-∑i,r (b i);let z:=(∑i,a i)-∑i,b i;have hD:z∈D:=sub_mem_sub (m3b a λi=>(m32 (ha i)).1) (m3b b λi=>(m32 (hb i)).1);have hwq:(w:ZMod q)=((l:ℤ)*z:ZMod q):=by dsimp[w,z];push_cast;rw[mul_sub,mul_sum,mul_sum];simp_rw[show ∀x,(r x:ZMod q)=((l:ℤ)*x:ZMod q) from λx=>by simp[r,Int.cast_mul,ZMod.intCast_mod]];push_cast;rfl
  have hwl:|w|<q:=by
   have hw:|(s:ℤ)*w|<(s:ℤ)*q:=by
    rw[show (s:ℤ)*w=∑i,(s:ℤ)*(r (a i)-r (b i)) by dsimp[w];rw[<-sum_sub_distrib,mul_sum]]
    calc _<=∑i,|(s:ℤ)*(r (a i)-r (b i))|:=abs_sum_le_sum_abs _ _
     _ < ∑_:Fin s,(q:ℤ):=sum_lt_sum_of_nonempty (univ_nonempty_iff.mpr ⟨⟨0,hs⟩⟩) λi _=>by
      have t1:=m3m hq (congrArg Fin.val (m32 (ha i)).2);have t2:=m3m hq (congrArg Fin.val (m32 (hb i)).2);push_cast at t1 t2;rw[toNat_of_nonneg (hr (a i)).1]at t1;rw[toNat_of_nonneg (hr (b i)).1]at t2;rw[abs_lt];constructor<;>linarith
     _ = _:=by simp
   rw[abs_mul,abs_of_nonneg (cast_nonneg s)]at hw;exact lt_of_mul_lt_mul_left hw (by omega)
  constructor
  . intro he;simpa[f]using congrArg (λt:ℤ=>(t:ZMod N)) (sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd w q).mp (by rw[hwq];dsimp[z];rw[sub_eq_zero.mpr he];simp)) hwl))
  . intro he;have hd:=(ZMod.intCast_zmod_eq_zero_iff_dvd w N).mp (by dsimp[w];push_cast;exact sub_eq_zero.mpr he)
    by_contra hn;have hzn:=sub_ne_zero.mpr hn;by_cases hw0:w=0
    . have ht:=hwq.symm;rw[hw0]at ht;push_cast at ht;rw[hlc]at ht;exact absurd (mul_eq_zero.mp ht) (by push Not;exact⟨hm0,hz z hD hzn⟩)
    . exact hg z (mem_erase.mpr ⟨hzn,hD⟩) w hw0 hwl hd hwq.symm
 refine⟨A',f,filter_subset _ _,hj,λx hx y hy hxy=>?_,hf⟩;have ht:=(hf (λ_=>x) (λ_=>y) (λ_=>hx) (λ_=>hy)).mpr (by simp[hxy]);simp at ht;exact ht.resolve_right (by omega)
noncomputable def m3q (N:ℕ) (t:ZMod N):ℂ:=exp (((2*Real.pi*t.val/N:ℝ):ℂ)*I)
lemma m3s (N:ℕ) (t:ZMod N):(m3q N t).re=cos (2*Real.pi*t.val/N):=Complex.exp_ofReal_mul_I_re _
lemma m3t {N:ℕ} [NeZero N] (k:ℤ):m3q N k=exp (((2*Real.pi*k/N:ℝ):ℂ)*I):=by
 unfold m3q;have hN:(N:ℂ)≠0:=Nat.cast_ne_zero.mpr (NeZero.ne N);have⟨m,hm⟩:=(ZMod.intCast_zmod_eq_zero_iff_dvd (((k:ZMod N).val:ℤ)-k) N).mp (by push_cast;exact sub_eq_zero.mpr (natCast_zmod_val _));have hv:(((k:ZMod N).val:ℕ):ℂ)=k+m*N:=by have:=congrArg (λz:ℤ=>(z:ℂ)) (show (((k:ZMod N).val:ℕ):ℤ)=k+m*N by linarith);push_cast at this;exact this
 rw[show (((2*Real.pi*((k:ZMod N).val:ℝ)/N:ℝ):ℂ)*I)=(((2*Real.pi*k/N:ℝ):ℂ)*I)+(m:ℂ)*(2*Real.pi*I) by push_cast;rw[hv];field_simp[hN],
  Complex.exp_add,Complex.exp_int_mul_two_pi_mul_I,mul_one]
lemma m3u {N:ℕ} [NeZero N] (t u:ZMod N):m3q N (t+u)=m3q N t*m3q N u:=by
 let k:ℤ:=(t.val:ℤ)+u.val;rw[show t+u=k by dsimp[k];rw[Int.cast_add,Int.cast_natCast,Int.cast_natCast,natCast_zmod_val,natCast_zmod_val],m3t];unfold m3q;rw[<-Complex.exp_add];congr 1;dsimp[k];push_cast;ring
lemma m3v {N:ℕ} [NeZero N] (t:ZMod N):m3q N (-t)=starRingEnd ℂ (m3q N t):=by
 let k:ℤ:=-(t.val:ℤ);rw[show -t=k by dsimp[k];rw[Int.cast_neg,Int.cast_natCast,natCast_zmod_val],m3t];unfold m3q;rw[<-Complex.exp_conj];congr 1;dsimp[k];simp only[map_mul,Complex.conj_ofReal,Complex.conj_I];push_cast;ring
lemma m3w {N:ℕ} [NeZero N] (q:ZMod N):∑x,m3q N (q*x)=if q=0 then (N:ℂ) else 0:=by
 split_ifs with hq
 . subst hq;simp[m3q,ZMod.card]
 . have hn1:m3q N q≠1:=λh1=>by
    unfold m3q at h1;have⟨k,hk⟩:=Complex.exp_eq_one_iff.mp h1;have hN:(0:ℝ)<N:=cast_pos.mpr (NeZero.pos N);have h2:(((2*Real.pi*q.val/N:ℝ):ℂ))=((k:ℤ):ℂ)*(2*Real.pi):=mul_right_cancel₀ Complex.I_ne_zero (by simpa[mul_assoc]using hk);have h3:2*Real.pi*q.val/N=k*(2*Real.pi):=by exact_mod_cast h2
    have hr:(q.val:ℝ)/N=k:=mul_left_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero) (by linarith [show 2*Real.pi*((q.val:ℝ)/N)=2*Real.pi*q.val/N by ring]);have hp:0<q.val:=Nat.pos_of_ne_zero λh0=>hq (by rw[<-natCast_zmod_val q,h0];simp);have:0<k:=by exact_mod_cast (show (0:ℝ)<k by rw[<-hr];exact div_pos (cast_pos.mpr hp) hN)
    have:k<1:=by exact_mod_cast (show (k:ℝ)<1 by rw[<-hr,div_lt_one hN];exact_mod_cast ZMod.val_lt q)
    omega
   set S:ℂ:=∑x,m3q N (q*x);have hs:m3q N q*S=S:=by dsimp[S];rw[mul_sum];exact(m30 λx _=>by change m3q N q*m3q N (q*x)=m3q N (q*(x+1));rw[mul_add,mul_one,add_comm,m3u]).trans (Equiv.sum_comp (Equiv.addRight (1:ZMod N)) λx=>m3q N (q*x))
   exact(mul_eq_zero.mp (show (m3q N q-1)*S=0 by rw[sub_mul,one_mul,hs,sub_self])).resolve_left (sub_ne_zero.mpr hn1)
lemma m3x {N:ℕ} [NeZero N] {t:ZMod N} {y:ℤ} (hy:(y:ZMod N)=t) (hb:(|y|:ℝ)<(N:ℝ)/4):0<cos (2*Real.pi*t.val/N):=by
 rw[<-m3s,<-hy,m3t,Complex.exp_ofReal_mul_I_re];apply Real.cos_pos_of_mem_Ioo;have hN:(0:ℝ)<N:=cast_pos.mpr (NeZero.pos N);have:=Real.pi_pos;have ha:=abs_lt.mp (by exact_mod_cast hb:|(y:ℝ)|<N/4);constructor
 . rw[lt_div_iff₀ hN];have:=mul_lt_mul_of_pos_left (show -(N:ℝ)/4<y by linarith [ha.1]) (show (0:ℝ)<2*Real.pi by positivity);linarith
 . rw[div_lt_iff₀ hN];have:=mul_lt_mul_of_pos_left ha.2 (show (0:ℝ)<2*Real.pi by positivity);linarith
lemma m3y {N:ℕ} [NeZero N] (A:Finset (ZMod N)) {a:ℝ} (ha:0<a) (hA:a*N<=#A) :
 ∃R:Finset (ZMod N),(0:ZMod N) ∉ R/\ #R<=⌊4/a^2⌋₊ /\
  ∀x,(∀q∈R,0<=cos (2*Real.pi*(q*x).val/N))->x∈A+A-A-A:=by
 classical
 let e:=m3q N;let r:ℝ:=#A;let n:ℝ:=N;have hN:0<n:=cast_pos.mpr (NeZero.pos N);have hAp:=lt_of_lt_of_le (mul_pos ha hN) hA;let F (q:ZMod N):ℂ:=∑t∈A,e (q*t);have hs q:((‖F q‖^2:ℝ):ℂ)=F q*starRingEnd ℂ (F q):=by rw[Complex.mul_conj,Complex.normSq_eq_norm_sq]
 have hpC:∑q,F q*starRingEnd ℂ (F q)=(N:ℂ)*#A:=by
  calc _=∑q,∑t∈A,∑u∈A,e ((t-u)*q):=m30 λq _=>by dsimp[F];rw[map_sum,sum_mul];exact m30 λt _=>by rw[mul_sum];exact m30 λu _=>by dsimp[e];rw[<-m3v,<-m3u,sub_mul,sub_eq_add_neg,mul_comm t q,mul_comm u q]
   _ = ∑t∈A,∑u∈A,∑q,e ((t-u)*q):=by rw[sum_comm];exact m30 λ_ _=>sum_comm
   _ = ∑t∈A,∑u∈A,(if t-u=0 then (N:ℂ) else 0):=m30 λ_ _=>m30 λ_ _=>m3w _
   _ = ∑_∈A,(N:ℂ):=m30 λt ht=>by simp_rw[sub_eq_zero,eq_comm (a:=t)];simp[ht]
   _ = _:=by simp[mul_comm]
 have hp:∑q,‖F q‖^2=n*r:=by have h1:=congrArg Complex.re hpC;rw[show (∑q,F q*starRingEnd ℂ (F q)).re=∑q,‖F q‖^2 by rw[Complex.re_sum];exact m30 λq _=>by rw[<-hs q,Complex.ofReal_re]]at h1;simpa[n,r]using h1
 let T:=r^3/(2*n);have hT:0<T:=(by positivity);let R:=univ.filter λq:ZMod N=>q≠0/\T<‖F q‖^2;have hR:#R<=⌊4/a^2⌋₊:=Nat.le_floor<|by
  have h1:(#R:ℝ)*T<=n*r:=le_trans ((by simp:(#R:ℝ)*T=∑_∈R,T)▸sum_le_sum λq hq=>le_of_lt (m32 hq).2.2) (hp▸sum_le_sum_of_subset_of_nonneg (subset_univ R) λ_ _ _=>sq_nonneg _);have h2:(#R:ℝ)<=2*(n/r)^2:=(mul_le_mul_iff_left₀ hT).mp<|by rwa[show 2*(n/r)^2*T=n*r by dsimp[T];field_simp[ne_of_gt hAp,ne_of_gt hN]]
  have:(n/r)^2<=(1/a)^2:=pow_le_pow_left₀ (by positivity) ((div_le_div_iff₀ hAp ha).mpr (by linarith)) 2
  calc (#R:ℝ)<=2/a^2:=by linarith [show 2*(1/a)^2=2/a^2 by ring]
   _<=_:=div_le_div_of_nonneg_right (by norm_num) (sq_nonneg a)
 refine⟨R,by simp[R],hR,λx hc=>?_⟩;by_contra hx;have h4:∑q,((‖F q‖^4:ℝ):ℂ)*e (-(q*x))=0:=by
  have ht q:((‖F q‖^4:ℝ):ℂ)*e (-(q*x))=∑a1∈A,∑a2∈A,∑b1∈A,∑b2∈A,e ((a1+a2-b1-b2-x)*q):=by
   rw[show ((‖F q‖^4:ℝ):ℂ)=F q*F q*starRingEnd ℂ (F q)*starRingEnd ℂ (F q) by rw[show ((‖F q‖^4:ℝ):ℂ)=((‖F q‖^2:ℝ):ℂ)*((‖F q‖^2:ℝ):ℂ) by push_cast;ring,hs];ring];symm
   calc _=∑a1∈A,∑a2∈A,∑b1∈A,∑b2∈A,e (q*a1)*e (q*a2)*starRingEnd ℂ (e (q*b1))*starRingEnd ℂ (e (q*b2))*e (-(q*x)):=m30 λ_ _=>m30 λ_ _=>m30 λ_ _=>m30 λ_ _=>(by dsimp[e];rw[<-m3v,<-m3v,<-m3u,<-m3u,<-m3u,<-m3u];congr 1;ring)
    _ = _:=by dsimp[F];simp_rw[<-sum_mul,<-mul_sum,<-map_sum];congr 1;simp_rw[<-sum_mul,<-mul_sum,<-map_sum];simp_rw[<-sum_mul,<-mul_sum];simp_rw[<-sum_mul]
  simp_rw[ht]
  calc _=∑a1∈A,∑a2∈A,∑b1∈A,∑b2∈A,∑q,e ((a1+a2-b1-b2-x)*q):=by rw[sum_comm];refine m30 λ_ _=>?_;rw[sum_comm];refine m30 λ_ _=>?_;rw[sum_comm];exact m30 λ_ _=>sum_comm
   _ = 0:=sum_eq_zero λ_ h1=>sum_eq_zero λ_ h2=>sum_eq_zero λ_ h3=>sum_eq_zero λ_ h4=>by dsimp[e];rw[m3w,if_neg];intro h0;exact hx ((sub_eq_zero.mp h0)▸sub_mem_sub (sub_mem_sub (add_mem_add h1 h2) h3) h4)
 let g (q:ZMod N):=‖F q‖^4*(e (q*x)).re;let E:=univ.erase (0:ZMod N)\R;have hg0:∑q,g q=0:=by have h1:=congrArg Complex.re h4;rw[Complex.re_sum,Complex.zero_re]at h1;exact(m30 λq _=>by dsimp[g,e];rw[Complex.re_ofReal_mul,m3v,Complex.conj_re]).trans h1
 have hs1:∑q,g q=g 0+(∑q∈R,g q+∑q∈E,g q):=by rw[<-add_sum_erase _ _ (mem_univ (0:ZMod N)),add_comm (∑q∈R,g q),sum_sdiff λq hq=>mem_erase.mpr ⟨(m32 hq).2.1,mem_univ _⟩]
 have h0v:g 0=r^4:=by dsimp[g,F,e,r];simp[m3q]
 have hRn:0<=∑q∈R,g q:=sum_nonneg λq hq=>mul_nonneg (by positivity) (by rw[m3s];exact hc q hq);have hrm:-r^4/2<=∑q∈E,g q:=by
  have h1:∑q∈E,-(T*‖F q‖^2)<=∑q∈E,g q:=sum_le_sum λq hq=>by
   rw[Finset.mem_sdiff]at hq;have hT':‖F q‖^2<=T:=by by_contra hg;push Not at hg;exact hq.2 (mem_filter.mpr ⟨mem_univ _,(mem_erase.mp hq.1).1,hg⟩)
   have:=mul_le_mul_of_nonneg_right hT' (sq_nonneg (‖F q‖));have:=m3s N (q*x)▸Real.neg_one_le_cos (2*Real.pi*(q*x).val/N);dsimp[g,e];nlinarith [sq_nonneg (‖F q‖^2),show ‖F q‖^4=‖F q‖^2*‖F q‖^2 by ring]
  have:=hp▸sum_le_sum_of_subset_of_nonneg (subset_univ E) λ_ _ _=>sq_nonneg (‖F _‖);have:T*(n*r)=r^4/2:=by dsimp[T];field_simp[ne_of_gt hN]
  rw[sum_neg_distrib,<-mul_sum]at h1;nlinarith
 have:(0:ℝ)<r^4/2:=by positivity
 linarith
lemma m3z {N:ℕ} [NeZero N] (R:Finset (ZMod N)) {M:ℕ} (hM:1<=M) :
 ∃B:Finset (ZMod N),N<=M^#R*#B/\∀x∈B,∀q∈R,∃y:ℤ,(y:ZMod N)=q*x/\(M:ℤ)*|y|<N:=by
 classical
 have hN:=NeZero.pos N;let f (x:ZMod N):(q:R)->Fin M:=λq=>⟨(M*(q.1*x).val)/N,(Nat.div_lt_iff_lt_mul hN).mpr (Nat.mul_lt_mul_of_pos_left (ZMod.val_lt _) (by omega))⟩;have⟨v,hv⟩:=m3o (univ:Finset (ZMod N)) f ⟨λ_=>⟨0,hM⟩⟩;simp[ZMod.card]at hv;let F:=univ.filter λx:ZMod N=>f x=v;have hF:N<=M^#R*#F:=hv;obtain⟨x0,hx0⟩:F.Nonempty:=nonempty_iff_ne_empty.mpr λh0=>by rw[h0,card_empty,mul_zero]at hF;omega
 refine⟨F.image (·-x0),(m34 F sub_left_injective).symm▸hF,λd hd q hq=>?_⟩;obtain⟨x,hx,rfl⟩:=m31 hd;refine⟨((q*x).val:ℤ)-(q*x0).val,by push_cast;rw[natCast_zmod_val,natCast_zmod_val,mul_sub],?_⟩;have h1:=m3m hN (congrArg Fin.val (congrFun (m32 hx).2 ⟨q,hq⟩));have h2:=m3m hN (congrArg Fin.val (congrFun (m32 hx0).2 ⟨q,hq⟩));push_cast at h1 h2;rw[show (M:ℤ)*|((q*x).val:ℤ)-(q*x0).val|=|(M:ℤ)*(((q*x).val:ℤ)-(q*x0).val)| by rw[abs_mul,abs_of_nonneg (cast_nonneg M:(0:ℤ)<=M)],abs_lt];constructor<;>linarith
lemma m3A {k d} {w:Fin k->ZV d} (h:LinearIndependent ℝ λi=>zR (w i)):Injective λa:ZV k=>∑i,a i•w i:=λa b hab=>by
 have h1:∑i,(a i-b i)•w i=0:=by have:=sub_eq_zero.mpr hab;rw[<-sum_sub_distrib]at this;simpa[sub_smul]using this
 have h2:=congrArg zR h1;rw[zRu,zR0]at h2;simp_rw[zRm]at h2;ext i;exact sub_eq_zero.mp (by exact_mod_cast Fintype.linearIndependent_iff.mp h (λj=>((a j-b j:ℤ):ℝ)) h2 i)
lemma m3B {J:ℕ->ℕ} (hJ:DJH J) (hQ:QPH) (s:ℕ) (hs:1<=s) :
 ∀D,∃C,1<=C/\∀P:GAP ℤ D,∃(k:ℕ) (_:k<=D) (Q:GAP ℤ k),Q.iSP s/\P.tF⊆Q.tF/\Q.vol<=C*P.vol:=λD=>by
 induction D using Nat.strong_induction_on with
 | h D ih =>
  cases D with
  | zero=>exact⟨1,le_refl 1,λP=>⟨0,le_refl 0,P,(m3d s P).mpr λc _ _=>funext λi=>Fin.elim0 i,Subset.rfl,by simp⟩⟩
  | succ D =>
   choose Cs _ hCs using λj (hj:j<=D)=>ih j (lt_succ_of_le hj);let Cp:=(range (D+1)).sup λj=>if h:j<=D then Cs j h else 1;let JD:=J D;let sf:=(2*JD)^D*(2*s+2)^(D+1);refine⟨max 1 (Cp*sf),le_max_left _ _,λP=>?_⟩;let P':=m3h P;by_cases hp:P'.iSP s
   . exact⟨D+1,le_refl _,P',hp,(m3j P).symm▸Subset.rfl,(m3k P).symm▸Nat.le_mul_of_pos_left _ (lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _))⟩
   . have hn:=(m3d s P').not.mp hp;push Not at hn;have⟨c,hcb,hcs,hcn⟩:=hn
     let L i:=(P'.hi i).toNat;have hL i:(L i:ℤ)=P'.hi i:=toNat_of_nonneg (by simpa[P',m3h]using P'.hle i);obtain⟨p,c0,_,⟨m,hm0,hme⟩,hps,hpk⟩:=hQ D c hcn;let f:ZV (D+1) →+ ℤ:=⟨⟨λx=>∑i,x i•P'.step i,by simp⟩,λ_ _=>by simp[add_mul,sum_add_distrib]⟩;have hks x (hx:p x=0):f x=0:=by have h0:f c0=0:=(mul_eq_zero.mp (show m*f c0=0 by rw[<-smul_eq_mul,<-map_zsmul,hme];exact hcs)).resolve_left hm0;obtain⟨t,rfl⟩:=(hpk x).mp hx;rw[map_zsmul,h0,smul_zero]
     choose el hel using λj:Fin D=>hps (single j 1);let g:ZV D →+ ℤ:=⟨⟨λy=>∑j,y j•f (el j),by simp⟩,λ_ _=>by simp[add_mul,sum_add_distrib]⟩;have hgc x:g (p x)=f x:=by have h1:=hks (x-∑j,(p x j)•el j) (by rw[map_sub,map_sum];simp_rw[map_zsmul,hel];ext j;simp[Finset.sum_apply,single_apply]);rw[map_sub,map_sum,sub_eq_zero]at h1;simp_rw[map_zsmul]at h1;exact h1.symm
     let e1 (i:Fin (D+1)):ZV (D+1):=single i 1;let pR:RV (D+1) →ₗ[ℝ] RV D:=⟨⟨λv=>∑i,v i•zR (p (e1 i)),λ_ _=>by simp[add_smul,sum_add_distrib]⟩,λ_ _=>by simp[mul_smul,smul_sum]⟩;have hpR x:pR (zR x)=zR (p x):=by
      have h1:p x=∑i,x i•p (e1 i):=by conv_lhs=>rw[show x=∑i,x i•e1 i by ext j;simp[e1,single_apply]];rw[map_sum];exact m30 λi _=>map_zsmul p _ _
      rw[h1,zRu];dsimp only[pR,LinearMap.coe_mk,AddHom.coe_mk,zR];exact m30 λi _=>(zRm _ _).symm
     let B0:Set (RV (D+1)):={ v | ∀i,|v i|<=L i };let B:=pR '' B0;have hB0:Convex ℝ B0:=λu hu v hv a b ha hb hab i=>by
      dsimp;calc |a*u i+b*v i|<=a*|u i|+b*|v i|:=by simpa[abs_mul,abs_of_nonneg ha,abs_of_nonneg hb]using abs_add_le (a*u i) (b*v i)
       _<=L i:=by have:=hu i;have:=hv i;nlinarith
     have hBb:Bornology.IsBounded B:=(Metric.isBounded_closedBall (x:=(0:RV D)) (r:=∑i,(L i:ℝ)*‖zR (p (e1 i))‖)).subset<|by
      rintro y ⟨v,hv,rfl⟩;rw[Metric.mem_closedBall,dist_zero_right]
      calc _<=∑i,|v i| *‖zR (p (e1 i))‖:=(norm_sum_le _ _).trans_eq (m30 λi _=>by rw[norm_smul,Real.norm_eq_abs])
       _<=_:=sum_le_sum λi _=>mul_le_mul_of_nonneg_right (hv i) (norm_nonneg _)
     have⟨k1,hk1,w,N,_,hNp,wl,wi,wc⟩:=hJ.2 D ⊤ B ⟨0,λi=>by simp,map_zero pR⟩ (hB0.linear_image pR) (by rintro y ⟨v,hv,rfl⟩;exact⟨-v,λi=>by simpa using hv i,map_neg pR v⟩) hBb;have hJC:1<=JD:=hJ.1 D;let Q1:GAP ℤ k1:=⟨P'.base,λi=>g (w i),λi=>-((JD*N i:ℤ)-1),λi=>(JD*N i:ℤ)-1,λi=>by have:=mul_pos hJC (hNp i);omega⟩;have hb:P'.tF⊆Q1.tF:=λx hx=>by
      obtain⟨n,hn,rfl⟩:=m31 hx;rw[m37]at hn;have⟨a,ha,he⟩:=wc (p n) trivial ⟨zR n,λi=>by have hi:=hn i;dsimp[cB]at hi;rw[show P'.lo i=0 from rfl,<-hL i]at hi;dsimp[zR];rw[abs_of_nonneg (by exact_mod_cast hi.1)];exact_mod_cast hi.2,hpR n⟩;refine mem_image.mpr ⟨a,m37.mpr λi=>by have:=abs_lt.mp (ha i);dsimp[cB,Q1,JD];omega,?_⟩;dsimp only[GAP.eval,Q1];congr 1;rw[show ∑i,a i•g (w i)=g (∑i,a i•w i) by rw[map_sum];exact m30 λi _=>(map_zsmul g _ _).symm,he,hgc];rfl
     have hk v (hv:pR v=0):∃t:ℝ,t•zR c=v:=by
      have hs:Surjective pR:=λy=>⟨∑j,y j•zR (el j),by rw[map_sum];simp_rw[show ∀j,pR (y j•zR (el j))=y j•single j (1:ℝ) from λj=>by rw[map_smul,hpR,hel];congr 1;ext t;simp[zR,single_apply]];ext t;simp[single_apply]⟩;have hd:Module.finrank ℝ (LinearMap.ker pR)=1:=by have h:=LinearMap.finrank_range_add_finrank_ker pR;rw[LinearMap.range_eq_top.mpr hs,finrank_top,Module.finrank_fin_fun,Module.finrank_fin_fun]at h;omega
      let u:LinearMap.ker pR:=⟨zR c,by rw[LinearMap.mem_ker,hpR,(hpk c).mpr ⟨m,hme⟩,zR0]⟩;have ht:Submodule.span ℝ ({u}:Set (LinearMap.ker pR))=⊤:=Submodule.eq_top_of_finrank_eq (by rw[finrank_span_singleton (λh0=>hcn (zRi _ ((zR0 _).symm▸congrArg Subtype.val h0))),hd]);rcases Submodule.mem_span_singleton.mp (show (⟨v,hv⟩:LinearMap.ker pR)∈_ by rw[ht];trivial) with ⟨t,hl⟩;exact⟨t,congrArg Subtype.val hl⟩
     let S:=(ZB.mk (λi=>-((N i:ℤ)-1)) (λi=>(N i:ℤ)-1) λi=>by have:=hNp i;omega).tF;let Bg:=(ZB.symm λi=>(s+1)*L i).tF;have hl:∀a∈S,∃z∈Bg,p z=∑i,a i•w i:=λa ha=>by
      dsimp only[S]at ha;rw[m37]at ha;have⟨v,hvB,hve⟩:=wi a (λi=>by have:=ha i;dsimp at this;rw[abs_lt];omega);have⟨z0,hz0⟩:=hps (∑i,a i•w i);have⟨t,hl⟩:=hk (zR z0-v) (by rw[map_sub,hpR,hz0,hve,sub_self]);refine⟨z0-⌊t⌋•c,m37.mpr λi=>?_,by rw[map_sub,map_zsmul,(hpk c).mpr ⟨m,hme⟩,smul_zero,sub_zero,hz0]⟩;have h1:((z0-⌊t⌋•c) i:ℝ)=v i+(t-⌊t⌋)*c i:=by have:=congrFun hl.symm i;simp only[zR,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]at this ⊢;push_cast;linarith
      have h2:=sub_nonneg.mpr (Int.floor_le t);have h3:t-⌊t⌋<=1:=by linarith [Int.lt_floor_add_one t]
      have h4:|(c i:ℝ)|<=(s:ℝ)*L i:=by exact_mod_cast (show |c i|<=(s:ℤ)*L i by have:=hcb i;rwa[show P'.lo i=0 from rfl,sub_zero,<-hL i]at this)
      have h5:|((z0-⌊t⌋•c) i:ℝ)|<=(((s+1)*L i:ℕ):ℝ):=by
       rw[h1];calc _<=|v i|+(t-⌊t⌋)*|(c i:ℝ)|:=le_trans (abs_add_le _ _) (by rw[abs_mul,abs_of_nonneg h2])
        _<=L i+1*((s:ℝ)*L i):=by have:=hvB i;gcongr
        _ = _:=by push_cast;ring
      exact abs_le.mp (by exact_mod_cast h5)
     choose lf hlm hlp using hl;have hSB:#S<=#Bg:=by
      let fx (a:ZV k1):=if h:a∈S then lf a h else 0;exact(m33 (s:=S) (f:=fx) λa ha b hb he=>by rw[mem_coe]at ha hb;exact m3A wl (by dsimp only;rw[<-hlp a ha,<-hlp b hb];exact congrArg p (by dsimp only[fx]at he;rwa[dif_pos ha,dif_pos hb]at he))).symm▸m35 λz hz=>by obtain⟨a,ha,rfl⟩:=m31 hz;simpa[fx,dif_pos ha]using hlm a ha
     have hBl:#Bg<=(2*s+2)^(D+1)*P'.vol:=by
      rw[ZB.cTF];unfold ZB.vol GAP.vol ZB.vol;exact(prod_le_prod' (g:=λi=>(2*s+2)*P'.cB.width i) λi _=>by rw[show P'.cB.width i=L i+1 by dsimp only[ZB.width,cB,L];have h0:P'.lo i=0:=rfl;have:=P'.hle i;rw[h0]at *;omega];dsimp only[ZB.width,ZB.symm];rw[show ((((s+1)*L i:ℕ):ℤ)- -(((s+1)*L i:ℕ):ℤ)+1).toNat=2*((s+1)*L i)+1 by omega];nlinarith).trans_eq (by rw[prod_mul_distrib,prod_const,card_univ,Fintype.card_fin])
     have hQv:Q1.vol<=sf*P'.vol:=by
      have h1:Q1.vol<=(2*JD)^k1*#S:=by
       rw[show Q1.vol=∏i,(2*(JD*N i)-1) by unfold GAP.vol ZB.vol;exact m36 λi _=>by dsimp[ZB.width,cB,Q1];have:=mul_pos hJC (hNp i);omega,
        show #S=∏i,(2*N i-1) by rw[ZB.cTF];exact m36 λi _=>by dsimp[ZB.width];have:=hNp i;omega]
       exact m3n hNp
      exact le_trans (h1.trans (Nat.mul_le_mul (Nat.pow_le_pow_right (by omega) hk1) hSB)) ((show (2*JD)^D*((2*s+2)^(D+1)*P'.vol)=sf*P'.vol by dsimp[sf];ring)▸mul_le_mul_left _ hBl)
     have⟨k,hk',Q,hQp,hQs,hQv'⟩:=hCs k1 hk1 Q1;refine⟨k,hk'.trans (Nat.le_succ_of_le hk1),Q,hQp,(m3j P).symm▸Subset.trans hb hQs,?_⟩;rw[<-m3k P];exact le_trans (hQv'.trans (Nat.mul_le_mul (by simpa[hk1]using le_sup (f:=λj=>if h:j<=D then Cs j h else 1) (mem_range.mpr (lt_succ_of_le hk1))) hQv)) (by rw[<-mul_assoc];exact mul_le_mul_right _ (le_max_right _ _))
lemma m3C {N k} {A':Finset ℤ} (hA':A'.Nonempty) {f:ℤ->ZMod N}
 (hF:∀(a b:Fin 8->ℤ),(∀i,a i∈A')->(∀i,b i∈A')->((∑i,a i=∑i,b i)<->(∑i,f (a i)=∑i,f (b i))))
 {P:GAP (ZMod N) k} (hs:P.iS) (hp:P.iP) (hb:P.tF⊆A'.image f+A'.image f-A'.image f-A'.image f) :
 ∃U:GAP ℤ k,U.iS/\U.iP/\U.vol=P.vol/\U.tF⊆A'+A'-A'-A':=by
 classical
 have⟨a0,ha0⟩:=hA';let R (q:Fin 4->ℤ):=∀t,q t∈A';let E (q:Fin 4->ℤ):=q 0+q 1-q 2-q 3;let M (q:Fin 4->ℤ):=f (q 0)+f (q 1)-f (q 2)-f (q 3);have f6 a b c (ha:R a) (hb:R b) (hc:R c):E a+E b=E c<->M a+M b=M c:=by
  let u:Fin 8->ℤ:=![a 0,a 1,b 0,b 1,c 2,c 3,a 0,a 0];let v:Fin 8->ℤ:=![a 2,a 3,b 2,b 3,c 0,c 1,a 0,a 0];have hi:=hF u v (λi=>by fin_cases i<;>first | exact ha _ | exact hb _ | exact hc _) (λi=>by fin_cases i<;>first | exact ha _ | exact hb _ | exact hc _);simp[u,v,Fin.sum_univ_eight]at hi;exact⟨λh=>by have h2:=hi.mp (by dsimp[E]at h;linarith);dsimp[M];linear_combination h2,λh=>by have:=hi.mpr (by dsimp[M]at h;linear_combination h);dsimp[E];linarith⟩
 have hr:∀y∈A'.image f+A'.image f-A'.image f-A'.image f,∃q,R q/\y=M q:=λy hy=>by
  obtain⟨t1,ht1,y4,hy4,rfl⟩:=mem_sub.mp hy;obtain⟨t2,ht2,y3,hy3,rfl⟩:=mem_sub.mp ht1;obtain⟨y1,hy1,y2,hy2,rfl⟩:=mem_add.mp ht2;obtain⟨a1,h1,rfl⟩:=m31 hy1;obtain⟨a2,h2,rfl⟩:=m31 hy2;obtain⟨a3,h3,rfl⟩:=m31 hy3;obtain⟨a4,h4,rfl⟩:=m31 hy4;exact⟨![a1,a2,a3,a4],λt=>by fin_cases t<;>assumption,rfl⟩
 have hst i:∃q,R q/\(1<=P.hi i->P.step i=M q):=by
  by_cases hh:1<=P.hi i
  . have hm:P.step i∈P.tF:=mem_image.mpr ⟨single i (1:ℤ),m37.mpr λj=>by
     have:=hs.2 j;have:=P.hle j;dsimp[cB];exact if h:j=i then by subst h;simp;omega else by simp[h];omega,by dsimp only[GAP.eval];rw[hs.1,zero_add];simp[single_apply]⟩
    have⟨q,hq,he⟩:=hr _ (hb hm);exact⟨q,hq,λ_=>he⟩
  . exact⟨λ_=>a0,λ_=>ha0,λh=>absurd h hh⟩
 choose sq hsq hse using hst;let U:GAP ℤ k:=⟨0,λi=>E (sq i),P.lo,P.hi,P.hle⟩;have hl:∀m c,c∈P.cB.tF->(∑i,(c i).natAbs)=m->∃q,R q/\U.eval c=E q/\P.eval c=M q:=λm=>by
  induction m with
  | zero=>intro c _ hz;have h0:c=0:=funext λi=>Int.natAbs_eq_zero.mp ((sum_eq_zero_iff.mp hz) i (mem_univ i));exact⟨λ_=>a0,λ_=>ha0,by rw[h0];simp[GAP.eval,U,E],by rw[h0];simp[GAP.eval,hs.1,M]⟩
  | succ m ih =>
   intro c hc hm;have⟨i0,hi0⟩:∃i0,c i0≠0:=by by_contra h;push Not at h;have:∑i,(c i).natAbs=0:=sum_eq_zero (λi _=>by simp[h i]);omega
   rw[m37]at hc;have hhi:1<=P.hi i0:=by have:=hc i0;have:=hs.2 i0;dsimp[cB]at *;omega
   let c':ZV k:=update c i0 (if 0<c i0 then c i0-1 else c i0+1);have hcm:c'∈P.cB.tF:=m37.mpr λj=>by
    by_cases h:j=i0
    . subst h;have:=hc j;have:=hs.2 j;dsimp[cB,c']at *;rw[update_self];split_ifs<;>omega
    . dsimp[c'];rw[update_of_ne h];exact hc j
   have hcs:(∑i,(c' i).natAbs)=m:=by
    have:=add_sum_erase univ (λi=>(c i).natAbs) (mem_univ i0);have:=add_sum_erase univ (λi=>(c' i).natAbs) (mem_univ i0);have:∑i∈univ.erase i0,(c' i).natAbs=∑i∈univ.erase i0,(c i).natAbs:=m30 λj hj=>by dsimp[c'];rw[update_of_ne (mem_erase.mp hj).1]
    have:(c' i0).natAbs+1=(c i0).natAbs:=by dsimp[c'];rw[update_self];split_ifs<;>omega
    omega
   have⟨qa,hqa,h1',h0'⟩:=ih c' hcm hcs;have⟨qc,hqc,h0c⟩:=hr _ (hb (mem_image.mpr ⟨c,m37.mpr hc,rfl⟩));have hde (G:Type) [AddCommGroup G] (Q:GAP G k):Q.eval c=Q.eval c'+(if 0<c i0 then Q.step i0 else -Q.step i0):=by
    dsimp only[GAP.eval];rw[add_assoc];congr 1;rw[<-add_sum_erase _ _ (mem_univ i0),<-add_sum_erase _ _ (mem_univ i0),m30 (f:=λi=>c' i•Q.step i) (g:=λi=>c i•Q.step i) λj hj=>by dsimp[c'];rw[update_of_ne (mem_erase.mp hj).1]];dsimp[c'];rw[update_self];split_ifs<;>simp only[sub_smul,add_smul,one_smul]<;>abel
   refine⟨qc,hqc,?_,h0c⟩;have hU:=hde ℤ U;have hP:=hde (ZMod N) P;have hs0:=hse i0 hhi;split_ifs at hU hP with hpos
   . rw[hU,h1'];exact(f6 qa (sq i0) qc hqa (hsq i0) hqc).mpr (by rw[<-h0',<-hs0,<-h0c,hP])
   . have hi:=(f6 qc (sq i0) qa hqc (hsq i0) hqa).mpr (by rw[<-h0c,<-hs0,<-h0',hP];abel);rw[hU,h1'];dsimp only[U]at hi ⊢;linarith
 refine⟨U,⟨rfl,hs.2⟩,λc1 h1 c2 h2 he=>?_,rfl,λx hx=>?_⟩
 . rw[mem_coe]at h1 h2;have⟨q1,hq1,e1,e1'⟩:=hl _ c1 h1 rfl;have⟨q2,hq2,e2,e2'⟩:=hl _ c2 h2 rfl
   have hm:=(f6 q1 (λ_=>a0) q2 hq1 (λ_=>ha0) hq2).mp (by dsimp[E];linarith);exact hp h1 h2 (by rw[e1',e2'];dsimp[M]at hm;linear_combination hm)
 . obtain⟨c,hc,rfl⟩:=m31 hx;have⟨q,hq,e1,_⟩:=hl _ c hc rfl;rw[e1];exact sub_mem_sub (sub_mem_sub (add_mem_add (hq 0) (hq 1)) (hq 2)) (hq 3)
lemma m3D {J:ℕ->ℕ} (hJ:DJH J) (hQ:QPH) {K:ℝ} (hK1:1<=K) (s:ℕ) (hs:1<=s) :
 ∃(D:ℕ) (C:ℝ),1<=C/\∀A:Finset ℤ,A.Nonempty->(#(A+A):ℝ)<=K*#A ->
  ∃(k:ℕ) (_:k<=D) (P:GAP ℤ k),P.iSP s/\A⊆P.tF/\(P.vol:ℝ)<=C*#A:=by
 classical
 have hK:=lt_of_lt_of_le zero_lt_one hK1;let a:ℝ:=1/(16*K^16);have ha:0<a:=by positivity
 let rm:=⌊4/a^2⌋₊+1;let Jm:=(range (rm+1)).sup J;have hJg:∀r ≤ rm,J r<=Jm:=λr hr=>le_sup (f:=J) (mem_range.mpr (lt_succ_of_le hr));have hJp:=le_trans (hJ.1 0) (hJg 0 (Nat.zero_le _));let Cb:=(8*Jm)^rm;let D:=rm+⌊K^5*Cb⌋₊;choose Cr _ hCr using m3B hJ hQ s hs;let cm:=(range (D+1)).sup Cr;let C:ℝ:=max 1 (cm*2^D*K^4);refine⟨D,C,le_max_left _ _,λA hA hAA=>?_⟩;let W:=iSm 8 A-iSm 8 A;have hW:#A<=#W:=by
  have⟨a0,ha0⟩:=hA;exact(m34 A sub_left_injective).symm▸m35 λx hx=>by
   obtain⟨t,ht,rfl⟩:=m31 hx;rw[show t-a0=(∑i:Fin 8,if i=0 then t else a0)-∑_:Fin 8,a0 by simp[Fin.sum_univ_eight];ring];exact sub_mem_sub (m3b (λi:Fin 8=>if i=0 then t else a0) λi=>by split_ifs<;>assumption) (m3b (λ_:Fin 8=>a0) λ_=>ha0)
 have hW8:(#W:ℝ)<=K^16*#A:=by simpa[W]using m3c hA hAA 8 8
 have⟨N,hNp,hWN,hN2⟩:=Nat.exists_prime_lt_and_le_two_mul (#W) (Nat.ne_of_gt (lt_of_lt_of_le hA.card_pos hW));have:Fact N.Prime:=⟨hNp⟩;have⟨A',f,hAs,hAc,hfi,hF8⟩:=m3p 8 (by norm_num) hA hNp hWN.le;have hAn:A'.Nonempty:=nonempty_iff_ne_empty.mpr λh0=>by rw[h0,card_empty,mul_zero]at hAc;exact absurd hAc (not_le_of_gt hA.card_pos)
 let B1:=A'.image f;have hdn:a*N<=#B1:=by
  have:(N:ℝ)<=2*#W:=by exact_mod_cast hN2
  have h2:(#A:ℝ)<=8*#B1:=(m33 hfi)▸by exact_mod_cast hAc
  have:=mul_le_mul_of_nonneg_left h2 (show (0:ℝ)<=K^16 by positivity);dsimp[a];rw[one_div_mul_eq_div,div_le_iff₀ (by positivity)];linarith
 have⟨R0,h0R,hR0,hBg⟩:=m3y B1 ha hdn;let R:=insert (1:ZMod N) R0;have hRc:#R<=rm:=le_trans (card_insert_le _ _) (Nat.add_le_add_right hR0 1);set r:=#R;have hrp:0<r:=card_pos.mpr ⟨1,mem_insert_self _ R0⟩;let eR:R ≃ Fin r:=Fintype.equivFinOfCardEq (card_coe R);let q j:=(eR.symm j).1;have hqm j:q j∈R:=(eR.symm j).2;have hqn j:q j≠0:=λh0=>(by simp[R,h0R]:(0:ZMod N) ∉ R) (h0▸hqm j);let G:AddSubgroup (ZV r):=⟨⟨⟨{ y | ∃x:ZMod N,∀j,(y j:ZMod N)=q j*x },by rintro _ _ ⟨x1,h1⟩ ⟨x2,h2⟩;exact⟨x1+x2,λj=>by simp[h1 j,h2 j,mul_add]⟩⟩,⟨0,λ_=>by simp⟩⟩,by rintro _ ⟨x,hx⟩;exact⟨-x,λj=>by simp[hx j]⟩⟩;let B:Set (RV r):={ v | ∀j,|v j|<(N:ℝ)/4 };have hNR:(0:ℝ)<N:=cast_pos.mpr hNp.pos;have hBc:Convex ℝ B:=λu hu v hv s t hs ht hst j=>by
  dsimp;calc |s*u j+t*v j|<=s*|u j|+t*|v j|:=by simpa[abs_mul,abs_of_nonneg hs,abs_of_nonneg ht]using abs_add_le (s*u j) (t*v j)
   _ < N/4:=by
    rcases eq_or_lt_of_le hs with rfl | hs'
    . have:t=1:=by linarith
      subst this;simpa using hv j
    . have:=mul_lt_mul_of_pos_left (hu j) hs';have:=mul_le_mul_of_nonneg_left (hv j).le ht;nlinarith
 have hBb:Bornology.IsBounded B:=(Metric.isBounded_closedBall (x:=(0:RV r)) (r:=(N:ℝ)/4)).subset λv hv=>by rw[Metric.mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg (by positivity)];exact λj=>(Real.norm_eq_abs _).symm▸(hv j).le
 have⟨k,hk,w,M,hwm,hMp,wl,wi,wc⟩:=hJ.2 r G B (λ_=>by dsimp;rw[abs_zero];positivity) hBc (λv hv j=>by simpa using hv j) hBb;let j0:Fin r:=⟨0,hrp⟩;let fG:ZV r →+ ZMod N:=⟨⟨λy=>(q j0)⁻¹*(y j0:ZMod N),by simp⟩,λ_ _=>by simp[mul_add]⟩;have hfe y x (hx:∀j,(y j:ZMod N)=q j*x):fG y=x:=by dsimp[fG];rw[hx j0,<-mul_assoc,inv_mul_cancel₀ (hqn j0),one_mul]
 have hfm:∀y∈G,∀j,(y j:ZMod N)=q j*fG y:=λy ⟨x,hx⟩ j=>(hfe y x hx).symm▸hx j;let P:GAP (ZMod N) k:=⟨0,λi=>fG (w i),λi=>-((M i:ℤ)-1),λi=>(M i:ℤ)-1,λi=>by have:=hMp i;omega⟩;have hfv (c:ZV k):fG (∑i,c i•w i)=P.eval c:=by dsimp only[GAP.eval,P];rw[zero_add,map_sum];exact m30 λi _=>map_zsmul fG _ _
 have hcl:∀c∈P.cB.tF,∀i,|c i|<M i:=λc hc i=>by have:=m37.mp hc i;dsimp[cB,P]at this;rw[abs_lt];omega
 have hgy (c:ZV k):(∑i,c i•w i)∈G:=G.sum_mem λi _=>G.zsmul_mem (hwm i) _;have hPs:P.tF⊆B1+B1-B1-B1:=λx hx=>by
  obtain⟨c,hc,rfl⟩:=m31 hx;refine hBg (P.eval c) λq' hq'=>?_;let j:=eR ⟨q',mem_insert_of_mem hq'⟩;have heq:q j=q':=by dsimp[q,j];simp
  exact le_of_lt (m3x (y:=(∑i,c i•w i) j) (by rw[<-hfv c,<-heq];exact hfm _ (hgy c) j) (by simpa only[zR,Int.cast_abs]using wi c (hcl c hc) j))
 have hPp:P.iP:=λc1 h1 c2 h2 he=>by
  rw[mem_coe]at h1 h2;let y1:=∑i,c1 i•w i;let y2:=∑i,c2 i•w i;refine m3A wl (funext λj=>sub_eq_zero.mp (Int.eq_zero_of_abs_lt_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mp ?_) ?_))
  . push_cast;exact sub_eq_zero.mpr (by rw[hfm y1 (hgy c1) j,hfm y2 (hgy c2) j,hfv,hfv,he])
  . have a:|(y1 j:ℝ)|<N/4:=wi c1 (hcl c1 h1) j;have b:|(y2 j:ℝ)|<N/4:=wi c2 (hcl c2 h2) j
    exact_mod_cast (lt_of_le_of_lt (abs_sub (y1 j:ℝ) (y2 j:ℝ)) (by linarith):|(y1 j:ℝ)-y2 j|<N)
 have⟨Bb,hBc',hBs⟩:=m3z R (M:=4) (by norm_num);have hJC:=hJ.1 r;let CB:ZB k:=⟨λi=>-((J r*M i:ℤ)-1),λi=>(J r*M i:ℤ)-1,λi=>by have:=mul_pos hJC (hMp i);omega⟩;have hcv:Bb⊆CB.tF.image P.eval:=λx hx=>by
  choose y hym hyb using λj=>hBs x hx (q j) (hqm j);have⟨c,hl,he⟩:=wc y ⟨x,hym⟩ (λj=>by have:(4:ℝ)*|(y j:ℝ)|<N:=(by exact_mod_cast hyb j);dsimp[zR];linarith);exact mem_image.mpr ⟨c,m37.mpr λi=>by have:=abs_lt.mp (hl i);dsimp[CB];omega,by rw[<-hfv c,he,hfe y x hym]⟩
 have hNP:N<=Cb*#P.tF:=by
  rw[P.cEV hPp];have hCB:CB.vol<=(2*J r)^k*P.vol:=by
   rw[show CB.vol=∏i,(2*(J r*M i)-1) from m36 λi _=>by dsimp[ZB.width,CB];have:=mul_pos hJC (hMp i);omega,
    show P.vol=∏i,(2*M i-1) by unfold GAP.vol ZB.vol;exact m36 λi _=>by dsimp[ZB.width,cB,P];have:=hMp i;omega]
   exact m3n hMp
  calc N<=4^r*((2*J r)^k*P.vol):=hBc'.trans (mul_le_mul_left _ (le_trans (le_trans (m35 hcv) (card_image_le.trans CB.cTF.le)) hCB))
   _<=4^r*((2*J r)^r*P.vol):=by gcongr;omega
   _ = (8*J r)^r*P.vol:=by rw[<-mul_assoc,<-mul_pow];ring
   _<=Cb*P.vol:=mul_le_mul_right _ (le_trans (Nat.pow_le_pow_left (mul_le_mul_left 8 (hJg r hRc)) r) (Nat.pow_le_pow_right (by omega) hRc))
 have⟨U,u1,u2,u3,u4⟩:=m3C hAn hF8 ⟨rfl,λ_=>rfl⟩ hPp hPs;have uA:U.tF⊆iSm 2 A-iSm 2 A:=Subset.trans u4 λx hx=>by
  obtain⟨_,⟨_,⟨a1,h1,a2,h2,rfl⟩,b1,h3,rfl⟩,b2,h4,rfl⟩:=by simpa only[Finset.mem_sub,Finset.mem_add]using sub_subset_sub (sub_subset_sub (add_subset_add hAs hAs) hAs) hAs hx
  rw[show iSm 2 A=A+A by ext y;simp[iSm,Finset.mem_add]];exact mem_sub.mpr ⟨a1+a2,add_mem_add h1 h2,b1+b2,add_mem_add h3 h4,by ring⟩
 have hcb:(#(A+U.tF):ℝ)<=(K^5*Cb)*#U.tF:=by
  have hs3:A+U.tF⊆iSm 3 A-iSm 2 A:=λx hx=>by obtain⟨a,ha,p,hp,rfl⟩:=mem_add.mp hx;obtain⟨u,hu,v,hv,rfl⟩:=mem_sub.mp (uA hp);rw[show a+(u-v)=(u+a)-v by ring];exact sub_mem_sub (add_mem_add hu ha) hv
  have h1:(#(A+U.tF):ℝ)<=K^5*#A:=le_trans (cast_le.mpr (m35 hs3)) (by simpa using m3c hA hAA 3 2);have h2:(#A:ℝ)<=Cb*#U.tF:=(by rw[U.cEV u2,P.cEV hPp,u3]:#U.tF=#P.tF).symm▸by exact_mod_cast hW.trans (le_trans hWN.le hNP)
  exact h1.trans (by rw[mul_assoc];exact mul_le_mul_of_nonneg_left h2 (by positivity))
 have⟨F,_,hFR,hAc⟩:=ruzsa_covering_add ⟨0,U.zMC (U.sIC u1)⟩ hcb;obtain⟨f0,_⟩:F.Nonempty:=by have⟨a,ha⟩:=hA;have⟨x,hx,_,_,_⟩:=mem_add.mp (hAc ha);exact⟨x,hx⟩
 let eF:F ≃ Fin (#F):=Fintype.equivFinOfCardEq (card_coe F);let g j:=(eF.symm j).1;let V:GAP ℤ (k+#F):=⟨f0,addCases U.step λj=>g j-f0,addCases (λi=>2*U.lo i) λ_=>0,addCases (λi=>2*U.hi i) λ_=>1,addCases (λi=>by simp;have:=U.hle i;omega) λ_=>by simp⟩;have hV:A⊆V.tF:=λa ha=>by
  obtain⟨x,hxF,d,hd,rfl⟩:=mem_add.mp (hAc ha);obtain⟨p,hp,q,hq,rfl⟩:=mem_sub.mp hd;obtain⟨c1,h1,rfl⟩:=m31 hp;obtain⟨c2,h2,rfl⟩:=m31 hq;rw[m37]at h1 h2;let j0:=eF ⟨x,hxF⟩;let dt:ZV (#F):=single j0 1;refine mem_image.mpr ⟨addCases (c1-c2) dt,m37.mpr ?_,?_⟩
  . exact addCases (λi=>by dsimp[cB,V];simp only[Fin.addCases_left];have:=h1 i;have:=h2 i;have:=u1.2 i;dsimp[cB]at *;omega) (λj=>by dsimp[cB,V,dt];simp only[Fin.addCases_right];by_cases h:j=j0<;>simp[h])
  . dsimp only[GAP.eval,V];rw[Fin.sum_univ_add];simp only[Fin.addCases_left,Fin.addCases_right]
    rw[show ∑i,(c1-c2) i•U.step i=U.eval c1-U.eval c2 by dsimp only[GAP.eval];rw[u1.1,zero_add,zero_add,<-sum_sub_distrib];exact m30 λi _=>by rw[Pi.sub_apply,sub_smul],
     show ∑j,(dt j)•(g j-f0)=x-f0 by simp[dt,single_apply,g,j0]]
    dsimp only[GAP.eval];rw[u1.1,zero_add,zero_add];ring
 have hVv:V.vol<=2^(k+#F)*U.vol:=by
  unfold GAP.vol ZB.vol;rw[Fin.prod_univ_add,pow_add];have hp1:(∏i:Fin k,V.cB.width (Fin.castAdd (#F) i))<=2^k*U.vol:=(prod_le_prod' (g:=λi=>2*U.cB.width i) λi _=>by dsimp[ZB.width,cB,V];simp only[Fin.addCases_left];have:=U.hle i;omega).trans_eq (by rw[prod_mul_distrib,prod_const,card_univ,Fintype.card_fin];rfl);rw[show ∏j:Fin (#F),V.cB.width (Fin.natAdd k j)=2^#F by simp_rw[show ∀j,V.cB.width (Fin.natAdd k j)=2 from λj=>by dsimp[ZB.width,cB,V];simp];simp];exact le_trans (mul_le_mul_right _ hp1) (by ring_nf;rfl)
 have hDl:=add_le_add (hk.trans hRc) (Nat.le_floor hFR);have⟨k',hk',Q,hQp,hVQ,hQv⟩:=hCr (k+#F) V;refine⟨k',hk'.trans hDl,Q,hQp,Subset.trans hV hVQ,?_⟩;have hUR:(U.vol:ℝ)<=K^4*#A:=le_trans (cast_le.mpr (U.cEV u2▸m35 uA)) (by simpa using m3c hA hAA 2 2);have hQn:=hQv.trans (Nat.mul_le_mul (le_sup (f:=Cr) (mem_range.mpr (lt_succ_of_le hDl))) (hVv.trans (mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hDl))));have hQR:(Q.vol:ℝ)<=cm*2^D*U.vol:=by have:=(cast_le (α:=ℝ)).mpr hQn;push_cast at this;linarith
 exact hQR.trans ((mul_le_mul_of_nonneg_left hUR (by positivity)).trans (by rw[<-mul_assoc];exact mul_le_mul_of_nonneg_right (le_max_right _ _) (cast_nonneg _)))
abbrev m3E d:=Fin d->ℕ
abbrev m3Y d:=Finset (m3E d)
def m3F {d} (i:Fin d) (A:m3Y d):=∀x∈A,∀t ≤ x i,update x i t∈A
def m3G {d} (A:m3Y d):=∀i,m3F i A
lemma m3H {d} {A:m3Y d} (hA:m3G A) {x y:m3E d} (hx:x∈A) (hxy:∀i,y i<=x i):y∈A:=by
 have hs:∀k ≤ d,(λi:Fin d=>if (i:ℕ)<k then y i else x i)∈A:=λk=>by
  induction k with
  | zero=>intro _;simpa using hx
  | succ k ih =>
   intro hk;let j:Fin d:=⟨k,hk⟩;have hu:update (λi:Fin d=>if (i:ℕ)<k then y i else x i) j (y j)=λi:Fin d=>if (i:ℕ)<k+1 then y i else x i:=funext λi=>by
    by_cases h:i=j
    . subst h;simp[j]
    . rw[update_of_ne h];have:(i:ℕ)≠k:=λe=>h (Fin.ext e);split_ifs<;>first | rfl | omega
   rw[<-hu];exact hA j _ (ih (Nat.le_of_succ_le hk)) (y j) (by simp[j,hxy j])
 convert hs d (le_refl d) using 1;ext i;simp[i.isLt]
lemma m3I {d} {A B:m3Y d} (hA:m3G A) (hB:m3G B):m3G (A+B):=λi x hx t ht=>by
 obtain⟨a,ha,b,hb,rfl⟩:=mem_add.mp hx;let t1:=min t (a i);let t2:=t-t1;rw[show update (a+b) i t=update a i t1+update b i t2 by
  ext j;by_cases h:j=i<;>simp[h,t1,t2]]
 exact add_mem_add (hA i a ha t1 (min_le_right _ _)) (hB i b hb t2 (by have:t<=a i+b i:=ht;dsimp[t1,t2];omega))
def m3J {d} (I:Finset (Fin d)) (x:m3E d):m3E d:=λi=>if i∈I then x i else 0
lemma m3K {d} {X:m3Y d} (hX:m3G X):#(X+piFinset λ_:Fin d=>range 2)=∑I,#(X.image (m3J I)):=by
 classical
 let cb:m3Y d:=piFinset λ_=>range 2;let sp (z:m3E d):=univ.filter λi=>z i≠0;rw[card_eq_sum_card_fiberwise (f:=sp) (t:=univ) λ_ _=>mem_univ _];refine m30 λI _=>?_;let em (u:m3E d):m3E d:=λi=>if i∈I then u i+1 else 0;rw[show (X+cb).filter (λz=>sp z=I)=(X.image (m3J I)).image em by
  ext z;simp only[mem_filter,Finset.mem_add,mem_image];constructor
  . rintro⟨⟨x,hx,e,he,rfl⟩,hs⟩;let u:m3E d:=λi=>if i∈I then x i+e i-1 else 0
    refine⟨u,⟨u,m3H hX hx λi=>by have:=mem_range.mp (m38.mp he i);dsimp[u];split_ifs<;>omega,funext λi=>by dsimp[m3J,u];split_ifs<;>rfl⟩,funext λi=>?_⟩;have hm:i∈I<->(x+e) i≠0:=by rw[<-hs];simp[sp]
    dsimp[em,u]at *;split_ifs with hI
    . have:=hm.mp hI;omega
    . by_contra hn;exact hI (hm.mpr (Ne.symm hn))
  . rintro⟨_,⟨x,hx,rfl⟩,rfl⟩;let e:m3E d:=λi=>if i∈I then 1 else 0
    refine⟨⟨m3J I x,m3H hX hx λi=>by dsimp[m3J];split_ifs<;>omega,e,m38.mpr λi=>mem_range.mpr (by dsimp[e];split_ifs<;>omega),funext λi=>by dsimp[m3J,e,em];split_ifs<;>simp⟩,by ext i;simp[sp,em]⟩]
 exact m33 λu1 h1 u2 h2 he=>by obtain⟨_,_,rfl⟩:=m31 h1;obtain⟨_,_,rfl⟩:=m31 h2;ext i;have:=congrFun he i;dsimp[em,m3J]at this ⊢;split_ifs at this ⊢<;>omega
def m3L {d} (A:m3Y d) (i:Fin d) (x:m3E d):=A.filter λy=>update y i 0=update x i 0
lemma m3M {d} (A:m3Y d) (i:Fin d) (x:m3E d):Set.InjOn (λw:m3E d=>w i) (m3L A i x):=λw1 h1 w2 h2 he=>by
 rw[mem_coe,m3L,mem_filter]at h1 h2;ext j;by_cases h:j=i
 . subst h;exact he
 . have a:=congrFun h1.2 j;have b:=congrFun h2.2 j;simp[update_of_ne h]at a b;exact a.trans b.symm
def m3N {d} (i:Fin d) (A:m3Y d):=(A.image λx=>update x i 0).biUnion λb=>(range (#(m3L A i b))).image λt=>update b i t
lemma m3O {d} {i:Fin d} {A:m3Y d} {y:m3E d}:y∈m3N i A<->y i<#(m3L A i y):=by
 simp only[m3N,mem_biUnion,mem_image,mem_range];constructor
 . rintro⟨b,⟨x,_,rfl⟩,t,ht,rfl⟩;rw[update_self];rwa[show m3L A i (update (update x i 0) i t)=m3L A i (update x i 0) by unfold m3L;congr 1;ext z;simp]
 . intro hl;have⟨x,hx⟩:=card_pos.mp (Nat.lt_of_le_of_lt (Nat.zero_le _) hl);rw[m3L,mem_filter]at hx
   refine⟨update y i 0,⟨x,hx.1,hx.2⟩,y i,?_,by simp⟩;rwa[show m3L A i (update y i 0)=m3L A i y by unfold m3L;congr 1;ext z;simp]
lemma m3P {d} (i:Fin d) (A:m3Y d):#(m3N i A)=#A:=by
 unfold m3N;rw[card_biUnion]
 . rw[m30 λb _=>(m34 _ λ_ _ h=>by simpa using congrFun h i).trans (card_range _)]
   exact(m30 λb hb=>by obtain⟨_,_,rfl⟩:=m31 hb;unfold m3L;congr 1;ext z;simp).trans (card_eq_sum_card_fiberwise (f:=λx=>update x i 0) λx hx=>mem_image.mpr ⟨x,hx,rfl⟩).symm
 . intro b1 h1 b2 h2 hn;dsimp[onFun];rw[disjoint_left];intro z hz1 hz2;obtain⟨_,_,rfl⟩:=m31 hz1;have⟨_,_,h⟩:=m31 hz2
   obtain⟨_,_,rfl⟩:=m31 h1;obtain⟨_,_,rfl⟩:=m31 h2;have:=congrArg (λv=>update v i 0) h;simp at this;exact hn this.symm
lemma m3Q {d} {i:Fin d} {A X:m3Y d} (hAX:A⊆X) (hX:m3F i X):m3N i A⊆X:=λy hy=>by
 rw[m3O]at hy;by_contra hyX;have hs:(m3L X i y).image (· i)⊆range (y i):=λt ht=>by
  obtain⟨z,hz,rfl⟩:=m31 ht;rw[m3L,mem_filter]at hz;rw[mem_range];by_contra hg;push Not at hg;have he:update z i (y i)=y:=funext λj=>by
   by_cases h:j=i
   . subst h;simp
   . rw[update_of_ne h];simpa[update_of_ne h]using congrFun hz.2 j
  exact hyX (he▸hX z hz.1 (y i) hg)
 have h1:#(m3L A i y)<=#(m3L X i y):=m35 (filter_subset_filter _ hAX);have h2:#(m3L X i y)<=y i:=(m33 (m3M X i y)).symm▸le_trans (m35 hs) (card_range _).le;omega
lemma m3R {d} {i j:Fin d} (hji:j≠i) {A:m3Y d} (hA:m3F j A):m3F j (m3N i A):=λy hy t ht=>by
 rw[m3O]at hy ⊢;rw[update_of_ne hji.symm];have hs:(m3L A i y).image (λz=>update z j t)⊆m3L A i (update y j t):=λw hw=>by obtain⟨z,hz,rfl⟩:=m31 hw;rw[m3L,mem_filter]at hz ⊢;exact⟨hA z hz.1 t ((by simpa[update_of_ne hji]using congrFun hz.2 j:z j=y j)▸ht),by rw[update_comm hji,hz.2,update_comm hji.symm]⟩
 exact lt_of_lt_of_le hy ((m33 (s:=m3L A i y) (f:=λz=>update z j t) λz1 h1 z2 h2 he=>m3M A i y h1 h2 (by simpa[update_of_ne hji.symm]using congrFun he i)).symm▸m35 hs)
lemma m3S {d} (i:Fin d) (A B:m3Y d):#(m3N i A+m3N i B)<=#(A+B):=by
 let bs:=((m3N i A+m3N i B) ∪ (A+B)).image λx=>update x i 0;have hp:∀S⊆(m3N i A+m3N i B) ∪ (A+B),#S=∑c∈bs,#(m3L S i c):=λS hS=>by
  rw[card_eq_sum_card_fiberwise (f:=λx=>update x i 0) (t:=bs) λx hx=>mem_image.mpr ⟨x,hS hx,rfl⟩];exact m30 λc hc=>by obtain⟨_,_,rfl⟩:=m31 hc;unfold m3L;congr 1;ext z;simp
 rw[hp _ subset_union_left,hp _ subset_union_right];refine sum_le_sum λc hc=>?_;obtain⟨xc,_,rfl⟩:=m31 hc;set c0:=update xc i 0;let L:=m3L (m3N i A+m3N i B) i c0;by_cases hL:L=∅
 . simp[L,hL]
 . have hLn:=(nonempty_iff_ne_empty.mpr hL).image (· i)
   let m:=(L.image (· i)).max' hLn;have⟨z,hzL,hzm⟩:=m31 (max'_mem _ hLn);have hLl:#L<=m+1:=(m33 (m3M _ i c0)).symm▸le_trans (m35 λt ht=>mem_range.mpr (lt_succ_of_le (le_max' _ t ht))) (card_range _).le;dsimp only[L]at hzL;rw[m3L,mem_filter]at hzL;obtain⟨u,hu,v,hv,rfl⟩:=mem_add.mp hzL.1;rw[m3O]at hu hv;let S:=(m3L A i u).image (· i);let T:=(m3L B i v).image (· i);have hSc:#S=#(m3L A i u):=m33 (m3M A i u);have hTc:#T=#(m3L B i v):=m33 (m3M B i v);have hSn:S.Nonempty:=card_pos.mp (by omega);have hTn:T.Nonempty:=card_pos.mp (by omega);have h1d:#S+#T-1<=#(S+T):=by
    let t0:=T.min' hTn;let s1:=S.max' hSn;have ht0:=min'_mem T hTn;have hs1:=max'_mem S hSn;have hd:Disjoint (S.image (·+t0)) ((T.erase t0).image (s1+·)):=disjoint_left.mpr λx h1 h2=>by obtain⟨s,hs,rfl⟩:=m31 h1;have⟨t,ht,h⟩:=m31 h2;have:=le_max' S s hs;have:=lt_of_le_of_ne (min'_le T t (mem_erase.mp ht).2) (Ne.symm (mem_erase.mp ht).1);omega
    have hc:#(S.image (·+t0) ∪ (T.erase t0).image (s1+·))<=#(S+T):=m35 (union_subset (λx hx=>by obtain⟨s,hs,rfl⟩:=m31 hx;exact add_mem_add hs ht0) (λx hx=>by obtain⟨t,ht,rfl⟩:=m31 hx;exact add_mem_add hs1 (mem_erase.mp ht).2));rw[card_union_of_disjoint hd,m34 _ (add_left_injective t0),m34 _ (add_right_injective s1),card_erase_of_mem ht0]at hc;have:=hTn.card_pos;omega
   have hST:S+T⊆(m3L (A+B) i c0).image (· i):=λt ht=>by
    obtain⟨sa,hsa,tb,htb,rfl⟩:=mem_add.mp ht;obtain⟨a,ha,rfl⟩:=m31 hsa;obtain⟨b,hb,rfl⟩:=m31 htb;rw[m3L,mem_filter]at ha hb;refine mem_image.mpr ⟨a+b,mem_filter.mpr ⟨add_mem_add ha.1 hb.1,funext λj=>?_⟩,rfl⟩;by_cases h:j=i
    . subst h;simp[c0]
    . have a:=congrFun ha.2 j;have b:=congrFun hb.2 j;have c:=congrFun hzL.2 j;simp[update_of_ne h]at a b c ⊢;omega
   have:=h1d.trans (le_trans (m35 hST) card_image_le);have:(u+v) i=u i+v i:=rfl;change (#L)<=_;omega
def m3T {d}:(k:ℕ)->k<=d->m3Y d->m3Y d
 | 0,_,A=>A
 | k+1,hk,A=>m3N ⟨k,hk⟩ (m3T k (Nat.le_of_succ_le hk) A)
lemma m3U {d} (X:m3Y d) (hX:m3G X):∀k (hk:k<=d) A,A⊆X ->
 (∀i:Fin d,(i:ℕ)<k->m3F i (m3T k hk A))/\ #(m3T k hk A)=#A/\m3T k hk A⊆X/\ #(m3T k hk A+m3T k hk A)<=#(A+A):=λk=>by
 induction k with
 | zero=>intro _ A hA;exact⟨λ_ hi=>by omega,rfl,hA,le_refl _⟩
 | succ k ih =>
  intro hk A hA;have⟨h1,h2,h3,h4⟩:=ih (Nat.le_of_succ_le hk) A hA;refine⟨λi hi=>?_,by rw[m3T,m3P,h2],m3Q h3 (hX ⟨k,hk⟩),le_trans (m3S ⟨k,hk⟩ _ _) h4⟩;by_cases hik:(i:ℕ)=k
  . rw[show i=⟨k,hk⟩ from Fin.ext hik];intro y hy t ht;dsimp only[m3T]at hy ⊢;rw[m3O]at hy ⊢
    rw[update_self,show m3L _ ⟨k,hk⟩ (update y ⟨k,hk⟩ t)=m3L _ ⟨k,hk⟩ y by unfold m3L;congr 1;ext z;simp];exact lt_of_le_of_lt ht hy
  . exact m3R (λh=>hik (congrArg Fin.val h)) (h1 i (by omega))
def m3V {d} (L:Fin d->ℕ):m3Y d:=piFinset λi=>range (L i)
lemma m3W {d} {L:Fin d->ℕ} (hL:∀i,1<=L i) {A:m3Y d} (hA:A⊆m3V L) :
 2^d*#A+∏i,(2*L i-1)<=#(A+A)+∏i,(2*L i):=by
 have hDS:m3G (m3V L):=λi x hx t ht=>by
  simp[m3V]at hx ⊢;intro j;by_cases h:j=i
  . subst h;rw[update_self];exact lt_of_le_of_lt ht (hx j)
  . rw[update_of_ne h];exact hx j
 let A':=m3T d (le_refl d) A;have⟨hd,hc,hs,ha⟩:=m3U (m3V L) hDS d (le_refl d) A hA;let cb:m3Y d:=piFinset λ_=>range 2;let L2 i:=2*L i-1;let U:Finset (Finset (Fin d)):=univ;have hbm:2^d*#A<=#(A'+A'+cb):=by
  let f (p:m3E d × m3E d):=p.1+p.1+p.2;have hi:Set.InjOn f (A'×ˢcb:Finset _):=λp1 h1 p2 h2 he=>by rw[mem_coe,mem_product]at h1 h2;apply Prod.ext<;>(ext i;have:=congrFun he i;have:=mem_range.mp (m38.mp h1.2 i);have:=mem_range.mp (m38.mp h2.2 i);dsimp[f]at *;omega)
  exact(show 2^d*#A=#((A'×ˢcb).image f) by rw[m33 hi,card_product,hc,show #cb=2^d by simp[cb,card_piFinset],mul_comm])▸m35 λz hz=>by obtain⟨p,hp,rfl⟩:=m31 hz;rw[mem_product]at hp;exact add_mem_add (add_mem_add hp.1 hp.1) hp.2
 rw[m3K (m3I (λi=>hd i i.isLt) (λi=>hd i i.isLt))]at hbm;have hsp:=(add_sum_erase U (λI=>#((A'+A').image (m3J I))) (mem_univ univ)).symm;have hu:(A'+A').image (m3J univ)=A'+A':=by ext x;simp only[mem_image];exact⟨λ⟨y,hy,h⟩=>by convert hy using 1;rw[<-h];ext i;simp[m3J],λhx=>⟨x,hx,by ext i;simp[m3J]⟩⟩
 have hbx:A'+A'⊆m3V L2:=λz hz=>by obtain⟨x,hx,y,hy,rfl⟩:=mem_add.mp hz;exact m38.mpr λi=>mem_range.mpr (by have:=mem_range.mp (m38.mp (hs hx) i);have:=mem_range.mp (m38.mp (hs hy) i);have:=hL i;dsimp[L2];omega)
 have hrm:∑I∈U.erase univ,#((A'+A').image (m3J I))<=∑I∈U.erase univ,∏i∈I,L2 i:=sum_le_sum λI _=>by
  refine le_trans (m35 (image_subset_image hbx)) (le_trans (m35 (show (m3V L2).image (m3J I)⊆piFinset λi=>if i∈I then range (L2 i) else {0} from λz hz=>by
   obtain⟨x,hx,rfl⟩:=m31 hz;exact m38.mpr λi=>by
    dsimp[m3J];split_ifs with hI
    . exact m38.mp hx i
    . exact mem_singleton_self 0)) ?_)
  rw[card_piFinset,show ∏i,#(if i∈I then range (L2 i) else ({0}:Finset ℕ))=∏i,if i∈I then L2 i else 1 from m36 λi _=>by split_ifs<;>simp,prod_ite,prod_const_one,mul_one];exact le_of_eq (prod_congr (by ext i;simp) λ_ _=>rfl)
 have htot:∑I:Finset (Fin d),∏i∈I,L2 i=∏i,(2*L i):=by
  rw[show ∏i,(2*L i)=∏i,(L2 i+1) from m36 λi _=>by have:=hL i;dsimp[L2];omega,prod_add];simp_rw[show ∀I:Finset (Fin d),(∏i∈I,L2 i)*(∏_∈univ\I,(1:ℕ))=∏i∈I,L2 i from λI=>by simp];rw[powerset_univ]
 have hts:=(add_sum_erase U (λI=>∏i∈I,L2 i) (mem_univ univ)).symm;have ha':#(A'+A')<=#(A+A):=ha;dsimp only[L2,U]at htot hts hrm hsp;rw[hsp,hu]at hbm;omega
lemma m3X {k} {L:Fin k->ℕ} (hL:∀i,1<=L i) (ha:∀i j,i<=j->L j<=L i) (hk:0<k) :
 L ⟨k-1,Nat.sub_lt hk Nat.zero_lt_one⟩*(∏i,(2*L i)-∏i,(2*L i-1))<=k*2^k*∏i,L i:=by
 have h1:∀s:Finset (Fin k),∏i∈s,(2*L i)<=∏i∈s,(2*L i-1)+∑j∈s,∏i∈s.erase j,(2*L i):=λs=>by
  induction s using Finset.induction_on with
  | empty=>simp
  | insert x s hx ih =>
   rw[prod_insert hx,prod_insert hx,sum_insert hx,erase_insert hx,
    show ∑j∈s,∏i∈(insert x s).erase j,(2*L i)=(2*L x)*∑j∈s,∏i∈s.erase j,(2*L i) by rw[mul_sum];exact m30 λj hj=>by rw[erase_insert_of_ne (by rintro rfl;exact hx hj),prod_insert (by simp[hx])]]
   have h2:=hL x;calc 2*L x*∏i∈s,(2*L i)=(2*L x-1)*∏i∈s,(2*L i)+∏i∈s,(2*L i):=by rw[<-add_one_mul,Nat.sub_add_cancel (by omega)]
    _<=(2*L x-1)*(∏i∈s,(2*L i-1)+∑j∈s,∏i∈s.erase j,(2*L i))+∏i∈s,(2*L i):=by gcongr
    _<=_:=by rw[mul_add];have:=mul_le_mul_right (∑j∈s,∏i∈s.erase j,(2*L i)) (sub_le (2*L x) 1);omega
 let lt:Fin k:=⟨k-1,Nat.sub_lt hk Nat.zero_lt_one⟩
 calc _<=L lt*∑j,∏i∈univ.erase j,(2*L i):=mul_le_mul_left _ (by have:=h1 univ;omega)
  _ = ∑j,L lt*∏i∈univ.erase j,(2*L i):=mul_sum _ _ _
  _<=∑_:Fin k,(2^k*∏i,L i):=sum_le_sum λj _=>by
   have hpr:∏i∈univ.erase j,(2*L i)=2^(k-1)*∏i∈univ.erase j,L i:=by rw[prod_mul_distrib,prod_const,card_erase_of_mem (mem_univ j),card_univ,Fintype.card_fin]
   calc _<=L j*∏i∈univ.erase j,(2*L i):=mul_le_mul_right _ (ha j lt (show j.val<=k-1 by omega))
    _ = 2^(k-1)*∏i,L i:=by rw[hpr,<-mul_prod_erase univ _ (mem_univ j)];ring
    _<=_:=mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) (sub_le k 1))
  _ = _:=by rw[sum_const,card_univ,Fintype.card_fin,smul_eq_mul,mul_assoc]
theorem lbi {johnC:ℕ->ℕ} (hJ:DJH johnC) (hQ:QPH) (s d:ℕ) (hs:1<=s) (δ:ℝ) (hδ:0<δ):∃(C:ℝ) (D:ℕ),1<=C/\∀A:Finset ℤ,A.Nonempty->(#(A+A):ℝ)<=(2:ℝ)^((d:ℝ)+1-δ)*#A->∃(k:ℕ) (_:k<=D) (Q:GAP ℤ k),Q.iSP (max s 2)/\A+A⊆Q.tF/\(Q.vol:ℝ)<=C*#(A+A)/\(∏i:Fin k,if (i:ℕ)<d then (Q.width i:ℝ) else 1)>=C⁻¹*Q.vol:=by
 classical
 let K:ℝ:=2^((d:ℝ)+1-δ);let E:=max K 1;have⟨D,F,hF,hFr⟩:=m3D hJ hQ (one_le_pow₀ (n:=4) (le_max_right K 1)) (max s 2) (hs.trans (le_max_left s 2));have hdp:0<1-(2:ℝ)^(-δ):=sub_pos.mpr (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith));let M:=max 1 (((d+1:ℝ)*F*E)/(1-2^(-δ)));have hM:1<=M:=le_max_left _ _;let C:=max F (M^D);have hC:1<=C:=hF.trans (le_max_left _ _);have hCp:=lt_of_lt_of_le zero_lt_one hC;refine⟨C,D,hC,λA hA hAA=>?_⟩;have⟨a0,ha0⟩:=hA;have hA2:#A<=#(A+A):=(m34 A (add_left_injective a0)).symm▸m35 λx hx=>by obtain⟨a,ha,rfl⟩:=m31 hx;exact add_mem_add ha ha0
 have hAp:(0:ℝ)<#A:=cast_pos.mpr hA.card_pos;have hK1:1<=K:=by have:(#A:ℝ)<=K*#A:=le_trans (by exact_mod_cast hA2) hAA;nlinarith
 have hE:E=K:=max_eq_left hK1;have hA4:(#((A+A)+(A+A)):ℝ)<=E^4*#(A+A):=by
  rw[show (A+A)+(A+A)=iSm 4 A-iSm 0 A by rw[show (4:ℕ)=2+2 from rfl,iSA,show iSm 2 A=A+A by ext x;simp[iSm,Finset.mem_add]];ext x;simp[iSm],hE];exact le_trans (m3c hA hAA 4 0) (by simpa using mul_le_mul_of_nonneg_left (show (#A:ℝ)<=#(A+A) by exact_mod_cast hA2) (show (0:ℝ)<=K^4 by positivity))
 have⟨k,hk,U,hUp,hAs,hUv⟩:=hFr (A+A) ⟨a0+a0,add_mem_add ha0 ha0⟩ hA4;let V:=m3h U;let g:=Tuple.sort λi:Fin k=>OrderDual.toDual (V.width i);let Q:GAP ℤ k:=⟨V.base,V.step ∘ g,V.lo ∘ g,V.hi ∘ g,λi=>V.hle (g i)⟩;have hQe n:Q.eval n=V.eval (n ∘ g.symm):=by dsimp only[GAP.eval,Q];congr 1;rw[<-Equiv.sum_comp g λj=>(n ∘ g.symm) j•V.step j];exact m30 λi _=>by simp
 have hQp:Q.iSP (max s 2):=(m3d _ Q).mpr λc hc hs=>by
  have h1:=Equiv.sum_comp g λj=>c (g.symm j)•V.step j;simp at h1;have h0:=(m3d _ V).mp ((m3l _ U).mpr hUp) (c ∘ g.symm) (λj=>by simpa[Q]using hc (g.symm j)) (h1.symm.trans hs);ext i;simpa using congrFun h0 (g i)
 have hQF:Q.tF=U.tF:=by
  rw[<-m3j U];ext x;simp only[GAP.tF,mem_image,m37,cB];constructor
  . rintro⟨n,hn,rfl⟩;exact⟨n ∘ g.symm,λj=>by simpa[Q]using hn (g.symm j),(hQe n).symm⟩
  . rintro⟨n,hn,rfl⟩;exact⟨n ∘ g,λi=>hn (g i),by rw[hQe];congr 1;ext j;simp⟩
 have hQV:Q.vol=U.vol:=(Equiv.prod_comp g λj=>V.width j).trans (m3k U);have hQh i:Q.hi i=(Q.width i:ℤ)-1:=by dsimp[GAP.width,ZB.width,cB];have h0:Q.lo i=0:=rfl;have:=Q.hle i;rw[h0]at *;omega
 have hQa i j (hij:i<=j):Q.width j<=Q.width i:=Tuple.monotone_sort (λt:Fin k=>OrderDual.toDual (V.width t)) hij;refine⟨k,hk,Q,hQp,hQF▸hAs,hQV▸hUv.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (cast_nonneg _)),?_⟩;by_cases hkd:k<=d
 . rw[show (∏i:Fin k,if (i:ℕ)<d then (Q.width i:ℝ) else 1)=Q.vol by unfold GAP.vol ZB.vol;push_cast;exact m36 λi _=>by rw[if_pos (lt_of_lt_of_le i.isLt hkd)];rfl]
   exact mul_le_of_le_one_left (cast_nonneg _) (inv_le_one_of_one_le₀ hC)
 . push Not at hkd;let L:=Q.width;let B:=A.image (·+a0)
   have hBs:B⊆Q.tF:=λx hx=>by obtain⟨a,ha,rfl⟩:=m31 hx;exact hQF▸hAs (add_mem_add ha ha0)
   have hB2:#(B+B)=#(A+A):=by
    rw[show B+B=(A+A).image (·+(a0+a0)) by
     ext x;simp only[B,Finset.mem_add,mem_image];constructor
     . rintro⟨_,⟨a1,h1,rfl⟩,_,⟨a2,h2,rfl⟩,rfl⟩;exact⟨a1+a2,⟨a1,h1,a2,h2,rfl⟩,by ring⟩
     . rintro⟨_,⟨a1,h1,a2,h2,rfl⟩,rfl⟩;exact⟨a1+a0,⟨a1,h1,rfl⟩,a2+a0,⟨a2,h2,rfl⟩,by ring⟩]
    exact m34 _ (add_left_injective _)
   let nZ (v:m3E k):ZV k:=λi=>v i;have hni:Injective nZ:=λ_ _ h=>funext λi=>Nat.cast_injective (congrFun h i);let S:=(m3V L).filter λv=>Q.eval (nZ v)∈B;have hSb:∀v∈m3V L,nZ v∈Q.cB.tF:=λv hv=>m37.mpr λi=>by dsimp[cB,nZ];have h0:Q.lo i=0:=rfl;rw[h0,hQh i];have:v i<Q.width i:=mem_range.mp (m38.mp hv i);omega
   have hSi:S.image (λv=>Q.eval (nZ v))=B:=by
    ext x;simp only[S,mem_image,mem_filter];constructor
    . rintro⟨_,⟨_,h⟩,rfl⟩;exact h
    . intro hx;obtain⟨n,hn,rfl⟩:=m31 (hBs hx);rw[m37]at hn;let v:m3E k:=λi=>(n i).toNat
      have hv:nZ v=n:=funext λi=>by have h:=hn i;dsimp only[cB]at h;rw[show Q.lo i=0 from rfl]at h;exact toNat_of_nonneg h.1
      exact⟨v,⟨m38.mpr λi=>mem_range.mpr (by have h:=hn i;dsimp only[cB]at h;rw[show Q.lo i=0 from rfl,hQh i]at h;dsimp[v,L];omega),hv.symm▸hx⟩,hv▸rfl⟩
   have hQ2:=m3e (le_max_right s 2) hQp;have hSc:#S=#A:=by
    rw[<-m34 A (add_left_injective a0)];change (#S)=#B;rw[<-hSi];symm;exact m33 λv1 h1 v2 h2 he=>hni (m3f (by norm_num) hQ2 (hSb v1 (m32 h1).1) (hSb v2 (m32 h2).1) he)
   have hSS:#(S+S)<=#(A+A):=by
    rw[<-hB2];let w (u:m3E k):=(Q.base+Q.base)+∑i,(u i:ℤ)•Q.step i;have hwa u v:w (u+v)=Q.eval (nZ u)+Q.eval (nZ v):=by dsimp only[w,GAP.eval,nZ];simp only[Pi.add_apply,Nat.cast_add,add_smul,sum_add_distrib];ring
    exact(m33 (s:=S+S) (f:=w) λw1 h1 w2 h2 he=>by rw[mem_coe]at h1 h2;obtain⟨u1,hu1,v1,hv1,rfl⟩:=mem_add.mp h1;obtain⟨u2,hu2,v2,hv2,rfl⟩:=mem_add.mp h2;rw[hwa,hwa]at he;exact hni (funext λi=>by simpa[nZ]using congrFun (m3g hQ2 (hSb _ (m32 hu1).1) (hSb _ (m32 hv1).1) (hSb _ (m32 hu2).1) (hSb _ (m32 hv2).1) he) i)).symm▸m35 λz hz=>by obtain⟨t,ht,rfl⟩:=m31 hz;obtain⟨u,hu,v,hv,rfl⟩:=mem_add.mp ht;rw[hwa];exact add_mem_add (m32 hu).2 (m32 hv).2
   let H (j:Fin (d+1)):=L ⟨j.val,lt_of_lt_of_le j.isLt hkd⟩;let pH (u:m3E k):m3E (d+1):=λj=>u ⟨j.val,lt_of_lt_of_le j.isLt hkd⟩;let pT (u:m3E k):m3E k:=λi=>if (i:ℕ)<d+1 then 0 else u i;let mg (a:m3E (d+1)) (x:m3E k):m3E k:=λi=>if h:(i:ℕ)<d+1 then a ⟨i,h⟩ else x i;have hmq u:mg (pH u) (pT u)=u:=funext λi=>by dsimp[mg,pH,pT];split_ifs<;>rfl
   let T:m3Y k:=piFinset λi=>if (i:ℕ)<d+1 then {0} else range (L i);let Sx x:=(S.filter λu=>pT u=x).image pH;have hxc:∑x∈T,#(Sx x)=#S:=by
    rw[m30 λx _=>m33 λu1 h1 u2 h2 he=>by rw[mem_coe,mem_filter]at h1 h2;rw[<-hmq u1,<-hmq u2,he,h1.2,h2.2]];exact(card_eq_sum_card_fiberwise λu hu=>m38.mpr λi=>by
     dsimp[pT];split_ifs
     . exact mem_singleton_self 0
     . exact m38.mp (m32 hu).1 i).symm
   have hxa:∑x∈T,#(Sx x+Sx x)<=#(S+S):=by
    let pc x:=(Sx x+Sx x).image λa=>mg a (x+x);have hpd:Set.PairwiseDisjoint (T:Set _) pc:=λx1 h1 x2 h2 hn=>by
     dsimp[onFun];rw[disjoint_left];intro w hw1 hw2;obtain⟨_,_,rfl⟩:=m31 hw1;have⟨_,_,h⟩:=m31 hw2;apply hn;ext i;by_cases hi:(i:ℕ)<d+1
     . have a:=m38.mp h1 i;have b:=m38.mp h2 i;rw[if_pos hi,mem_singleton]at a b;rw[a,b]
     . have:=congrFun h i;dsimp[mg]at this;rw[dif_neg hi,dif_neg hi]at this;omega
    calc _=∑x∈T,#(pc x):=m30 λx _=>(m34 _ λa1 a2 he=>funext λj=>by have h:=congrFun he ⟨j.val,lt_of_lt_of_le j.isLt hkd⟩;dsimp only[mg]at h;rwa[dif_pos j.isLt,dif_pos j.isLt]at h).symm
     _ = #(T.biUnion pc):=(card_biUnion hpd).symm
     _<=#(S+S):=m35 λw hw=>by
      have⟨x,_,hx⟩:=mem_biUnion.mp hw;obtain⟨a,ha,rfl⟩:=m31 hx;obtain⟨a1,ha1,a2,ha2,rfl⟩:=mem_add.mp ha;obtain⟨u1,hu1,rfl⟩:=m31 ha1;obtain⟨u2,hu2,rfl⟩:=m31 ha2;rw[mem_filter]at hu1 hu2;rw[show mg (pH u1+pH u2) (x+x)=mg (pH u1) (pT u1)+mg (pH u2) (pT u2) by rw[hu1.2,hu2.2];ext i;dsimp[mg];split_ifs<;>rfl,hmq u1,hmq u2];exact add_mem_add hu1.1 hu2.1
   have hgs:2^(d+1)*#A+#T*∏j,(2*H j-1)<=#(A+A)+#T*∏j,(2*H j):=by
    have h1:=sum_le_sum λx (_:x∈T)=>m3W (L:=H) (A:=Sx x) (λj=>Q.cB.wP _) (λa ha=>by obtain⟨u,hu,rfl⟩:=m31 ha;exact m38.mpr λj=>m38.mp (m32 (m32 hu).1).1 _);simp[sum_add_distrib,<-mul_sum,hxc,hSc]at h1;omega
   have hvs:#T*∏j,H j=Q.vol:=by
    rw[show #T=∏i:Fin k,if (i:ℕ)<d+1 then 1 else L i by rw[card_piFinset];exact m36 λi _=>by split_ifs<;>simp,
     show ∏j,H j=∏i:Fin k,if (i:ℕ)<d+1 then L i else 1 by rw[prod_ite,prod_const_one,mul_one];exact prod_bij (λj _=>(⟨j.val,lt_of_lt_of_le j.isLt hkd⟩:Fin k)) (λj _=>mem_filter.mpr ⟨mem_univ _,j.isLt⟩) (λ_ _ _ _ h=>Fin.ext (congrArg (Fin.val:Fin k->ℕ) h)) (λi hi=>⟨⟨i.val,(m32 hi).2⟩,mem_univ _,Fin.ext rfl⟩) λ_ _=>rfl,
     <- prod_mul_distrib];unfold GAP.vol ZB.vol;exact m36 λi _=>by split_ifs<;>simp[L,GAP.width]
   let l:=L ⟨d,hkd⟩;have hmn:2^(d+1)*#A*l<=#(A+A)*l+(d+1)*2^(d+1)*Q.vol:=by
    have:=mul_le_mul_left (#T) (prod_le_prod' (s:=univ) λj _=>sub_le (2*H j) 1);have h1:=mul_le_mul_right l (show 2^(d+1)*#A<=#(A+A)+#T*(∏j,(2*H j)-∏j,(2*H j-1)) by rw[Nat.mul_sub_left_distrib];omega);rw[Nat.add_mul]at h1;have:#T*(∏j,(2*H j)-∏j,(2*H j-1))*l<=(d+1)*2^(d+1)*Q.vol:=le_trans ((show #T*(∏j,(2*H j)-∏j,(2*H j-1))*l=#T*(l*(∏j,(2*H j)-∏j,(2*H j-1))) by ring)▸mul_le_mul_left (#T) (m3X (L:=H) (λj=>Q.cB.wP _) (λi j hij=>hQa _ _ hij) (Nat.succ_pos d))) (by rw[<-hvs];ring_nf;rfl);omega
   have hLM:(l:ℝ)<=M:=by
    let p2:ℝ:=2^(d+1);let q2:ℝ:=2^(-δ);let aR:ℝ:=#A;have hR:p2*aR*l<=#(A+A)*l+(d+1:ℝ)*p2*Q.vol:=by have:=(cast_le (α:=ℝ)).mpr hmn;push_cast at this;linarith
    have hKs:K=p2*q2:=by dsimp[K,p2,q2];rw[sub_eq_add_neg,Real.rpow_add (by norm_num:(0:ℝ)<2),show ((d:ℝ)+1)=((d+1:ℕ):ℝ) by push_cast;ring,Real.rpow_natCast]
    have hQb:(Q.vol:ℝ)<=F*K*aR:=by rw[hQV];have:=mul_le_mul_of_nonneg_left hAA (by linarith:0<=F);linarith
    have hAA':(#(A+A):ℝ)<=p2*q2*aR:=by rw[<-hKs];exact hAA
    have:=mul_le_mul_of_nonneg_right hAA' (cast_nonneg l);have:=mul_le_mul_of_nonneg_left hQb (show (0:ℝ)<=(d+1:ℝ)*p2 by positivity);have h2:(1-q2)*l<=(d+1:ℝ)*F*K:=le_of_mul_le_mul_left (by linarith) (show (0:ℝ)<p2*aR by positivity);exact le_trans (by rw[hE,le_div_iff₀ hdp];linarith) (le_max_right _ _)
   let f1 (i:Fin k):ℝ:=if (i:ℕ)<d then Q.width i else 1;let f2 (i:Fin k):ℝ:=if (i:ℕ)<d then 1 else Q.width i;have htp:(∏i,f2 i)<=C:=by
    have hle:(∏i,f2 i)<=∏_:Fin k,M:=prod_le_prod (λi _=>by dsimp[f2];split_ifs<;>positivity) λi _=>by
     dsimp[f2];split_ifs with hi
     . exact hM
     . exact le_trans (by exact_mod_cast hQa ⟨d,hkd⟩ i (show d<=i.val by omega)) hLM
    exact le_trans (le_trans (by simpa using hle) (pow_le_pow_right₀ hM hk)) (le_max_right _ _)
   have hvf:(Q.vol:ℝ)=(∏i,f1 i)*∏i,f2 i:=by rw[<-prod_mul_distrib];unfold GAP.vol ZB.vol;push_cast;exact m36 λi _=>by dsimp[f1,f2];split_ifs<;>simp[GAP.width]
   rw[ge_iff_le,inv_mul_le_iff₀ hCp,hvf];exact le_trans (mul_le_mul_of_nonneg_left htp (prod_nonneg λi _=>by dsimp[f1];split_ifs<;>positivity)) (by rw[mul_comm])
end
end E186
namespace E186
def m4fs {G:Type*} [AddCommMonoid G] [DecidableEq G]:∀ {n:ℕ},(Fin n->Finset G)->Finset G
| 0,_=>{0}
| _+1,A=>m4fs (fun i=>A i.castSucc)+A (Fin.last _)
def LEH:Prop:=∀ (d:ℕ),1<=d->∀ (c:ℝ),0< c->c<=1->∃ (γ:ℝ) (L₀ W₀:ℕ),0< γ/\ ∀ (Q:ZB d),(∀ i,W₀<=Q.width i)->∀ (ℓ:ℕ),L₀<=ℓ->∀ (A:Fin ℓ->Finset (ZV d)),(∀ t,A t⊆Q.tF)->(∀ t,c*(Q.vol:ℝ)<=((A t).card:ℝ))->(∀ t,AddSubgroup.closure ((A t-A t:Finset (ZV d)):Set (ZV d))=⊤)->∃ x₀:ZV d,(ZB.symm (fun i=>⌊γ*(ℓ:ℝ)*(Q.width i:ℝ)⌋₊)).tF.image (·+x₀)⊆m4fs A
def LNH:Prop:=∀ (d:ℕ),1<=d->∀ (c:ℝ),0< c->c<=1->∃ (κ:ℕ) (γ:ℝ) (L₀ W₀:ℕ) (_:1<=κ) (hγ:0< γ),∀ (Q:ZB d) (A:Finset (ZV d)),(∀ i,W₀<=Q.width i)->A⊆Q.tF->(0:ZV d)∈A->c*(Q.vol:ℝ)<=(A.card:ℝ)->∃ (P:GAP (ZV d) d) (_hC:P.iC) (hS:P.iS),(∀ i,P.step i∈AddSubgroup.closure (A:Set (ZV d)))/\ (∀ x∈AddSubgroup.closure (A:Set (ZV d)),∃! n:ZV d,∑ i,n i•P.step i=x)/\ (∀ x∈Q.tF,x∈AddSubgroup.closure (A:Set (ZV d))->x∈P.tF)/\ (∃ t:ZV d,∀ x∈P.tF,∀ i,(κ:ℤ)*Q.lo i<=(x-t) i/\ (x-t) i<=(κ:ℤ)*Q.hi i)/\ (∀ i,(P.width i:ℝ)<=(κ:ℝ)*(Q.width i:ℝ))/\ (∀ ℓ:ℕ,L₀<=ℓ->∃ x₀:ZV d,(P.rS (γ*(ℓ:ℝ)) (mul_nonneg hγ.le (Nat.cast_nonneg ℓ)) (GAP.sIC hS)).tF.image (·+x₀)⊆iSm ℓ A)
def LBH:Prop:=∀ (s d:ℕ),1<=s->∀ (δ:ℝ),0< δ->∃ (C:ℝ) (D_max:ℕ),1<=C/\ ∀ (A:Finset ℤ),A.Nonempty->((A+A).card:ℝ)<=(2:ℝ) ^ ((d:ℝ)+1-δ)*(A.card:ℝ)->∃ (k:ℕ) (_:k<=D_max) (Qtilde:GAP ℤ k),Qtilde.iSP (max s 2)/\ (A+A)⊆Qtilde.tF/\ (Qtilde.vol:ℝ)<=C*((A+A).card:ℝ)/\ (∏ i:Fin k,if (i:ℕ)< d then (Qtilde.width i:ℝ) else 1)>=C⁻¹*(Qtilde.vol:ℝ)
def CSH:Prop:=∀ (ℓ:ℕ),1<=ℓ->∀ (β:ℝ),1< β->∃ (c:ℝ) (d_max m₀:ℕ) (hc:0< c),c<=1/\ 1<=d_max/\ 4<=m₀/\ ∀ (B:ZB ℓ) (A:Finset (ZV ℓ)),(0:ZV ℓ)∈B.tF->A⊆B.tF->m₀<=A.card->(B.vol:ℝ)<=(A.card:ℝ) ^ β->
 let m:ℕ:=A.card
 let s:ℕ:=⌊(m:ℝ) / (Real.log (m:ℝ)) ^ 2⌋₊
 ∃ (d':ℕ) (_:1<=d') (_:d'<=d_max) (hatA A':Finset (ZV ℓ)) (P:GAP (ZV ℓ) d') (q₀:ZV ℓ) (hS:P.iS),hatA⊆A/\ (m:ℝ)-c⁻¹*(m:ℝ) / Real.log (m:ℝ)<=(hatA.card:ℝ)/\ A'⊆hatA/\ A'.card<=s/\ (∀ i:Fin d',1<=P.hi i)/\ hatA⊆P.tF/\ q₀∈AddSubgroup.closure (Set.range P.step)/\ (P.rS (c*(s:ℝ)) (mul_nonneg hc.le (Nat.cast_nonneg s)) (GAP.sIC hS)).iP/\ ((P.rS (c*(s:ℝ)) (mul_nonneg hc.le (Nat.cast_nonneg s)) (GAP.sIC hS)).tF.image (·+q₀))⊆sS A'
namespace M4
abbrev Y:=ℝ
section
open scoped Classical
open Finset Real
open ZB (mTF cTF)
open AddSubgroup (closure closure_le subset_closure sum_mem closure_mono relIndex_mul_index relIndex_eq_one)
open Fintype (piFinset mem_piFinset card_piFinset)
open Pi (single single_eq_same single_eq_of_ne)
open Int (toNat_of_nonneg floor_le le_floor ceil_le sub_one_lt_floor ceil_lt_add_one ceil_mono floor_mono ceil_intCast floor_intCast ceil_neg one_le_abs natCast_natAbs cast_abs cast_natCast toNat_natCast card_Icc card_Ico card_Ioc le_of_dvd)
open Nat (le_ceil div_mul_le_self le_div_iff_mul_le mul_div_le div_pos cast_nonneg pow_le_pow_right one_le_pow le_pow_clog pow_log_le_self lt_pow_succ_log_self le_log_of_pow_le div_le_self add_sub_of_le lt_two_pow_self le_of_succ_le lt_floor_add_one div_le_of_le_mul div_add_mod mod_lt le_mul_of_pos_left le_mul_of_pos_right cast_mul cast_pow cast_sub cast_zero cast_one cast_ofNat cast_prod cast_sum find find_spec find_min find_min' strong_induction_on cast_injective clog_le_iff_le_pow)
open Classical (choose choose_spec)
open GAP (eval cB nS rS iP iC iS iSP cEV cLV zMC)
open Set (InjOn)
variable {G1 G2 U1 U2:Type*} [AddCommGroup G1] [AddCommGroup G2]
abbrev V:=Finset
abbrev F:=@iSm
abbrev z2:=@sS
abbrev zf {G:Type*} [AddGroup G] (s:Set G):=closure s
abbrev z8 [DecidableEq G2] (f:U1->G2) (A:V U1):=zf ((A.image f:V G2):Set G2)
abbrev zi (n:ℕ):=Icc (-(n:ℤ)) n
abbrev ze:=@GAP.sIC
abbrev W:=@nS
abbrev z5 {d:ℕ} (P:GAP G1 d):=P.cB.tF
noncomputable abbrev z3 {d:ℕ} (P:GAP G1 d) (c:Y) (h:P.iC) (hc:0<=c:=by positivity):=P.rS c hc h
noncomputable abbrev y0 (D:ℕ) (c:Y):=Nat.clog 2 (⌈64*(1+16*log ((4/3:Y)*(2:Y)^D/c))⌉₊+1)
noncomputable abbrev y5 (D:ℕ) (c:Y):=(3/8:Y)*c*(1/(2*(2:Y)^(y0 D c)))^D
noncomputable abbrev zt (n:ℕ) (b:Y):=Nat.clog 2 (⌈(n:Y)^(1/b)⌉₊+1)+1
abbrev yw [DecidableEq G1] (d s:ℕ) (c:Y) (hc:0< c) (b a:V G1) (P:GAP G1 d) (e:G1) (hS:P.iS):Prop:=
 a⊆b/\ #a<=s/\ (∀ i,1<=P.hi i)/\ b⊆P.tF/\ e∈zf (Set.range P.step) /\
 (z3 P (c*s) (ze hS)).iP/\ (z3 P (c*s) (ze hS)).tF.image (·+e)⊆z2 a
lemma za {a b c:Y} (h:a<=b) (hc:0<=c:=by positivity):c*a<=c*b:=mul_le_mul_of_nonneg_left h hc
lemma zj {a b c:Y} (h:a<=b) (hc:0<=c:=by positivity):a*c<=b*c:=mul_le_mul_of_nonneg_right h hc
lemma y6 {a b c d:Y} (e:a<=b) (f:c<=d) (hc:0<=c:=by positivity) (hb:0<=b:=by positivity):a*c<=b*d:=mul_le_mul e f hc hb
lemma ye {a b c:ℤ} (h:a<=b) (hc:0<=c:=by positivity):c*a<=c*b:=mul_le_mul_of_nonneg_left h hc
lemma y7 {a b c:ℤ} (h:a<=b) (hc:0<=c:=by positivity):a*c<=b*c:=mul_le_mul_of_nonneg_right h hc
lemma Z {a b:ℕ} (h:a<=b):(a:Y)<=b:=Nat.cast_le.mpr h
lemma zw {a b:ℕ} (h:a< b):(a:Y)< b:=Nat.cast_lt.mpr h
lemma zk {a:ℕ} (h:1<=a):(1:Y)<=a:=Nat.one_le_cast.mpr h
lemma zx (a:ℕ) (h:1<=a:=by omega):(1:Y)<=a:=Nat.one_le_cast.mpr h
lemma zy {a b:ℤ} (h:a<=b):(a:Y)<=b:=Int.cast_le.mpr h
lemma yx {a:ℤ} (h:0<=a):(0:Y)<=a:=by exact_mod_cast h
lemma zo {a:ℕ} (h:0< a):(0:Y)< a:=Nat.cast_pos.mpr h
lemma zl (a:ℕ) (h:0< a:=by omega):(0:Y)< a:=Nat.cast_pos.mpr h
lemma zr {a b:ℕ} (h:a<=b:=by omega):2^a<=2^b:=pow_le_pow_right (by omega) h
lemma y1 (k:ℕ):1<=2^k:=one_le_pow k 2 (by omega)
lemma zu {a b:ℕ} (c:ℕ) (h:a<=b):c*a<=c*b:=Nat.mul_le_mul_left c h
lemma y2 {a b:ℕ} (c:ℕ) (h:a<=b):a*c<=b*c:=Nat.mul_le_mul_right c h
abbrev zs:=Nat.log 2
abbrev xa:=Nat.clog 2
lemma z6 {s t:V U1} (h:s⊆t):#s<=#t:=card_le_card h
lemma z0 [DecidableEq U2] {s:V U1} {f:U1->U2} {y:U2}:y∈s.image f->∃ x∈s,f x=y:=mem_image.mp
lemma zg {s:V U1} {p:U1->Prop} [DecidablePred p] {x:U1}:x∈s.filter p->x∈s/\ p x:=mem_filter.mp
lemma y8 [DecidableEq G1] {A B:V G1} {x:G1}:x∈A+B->∃ a∈A,∃ b∈B,a+b=x:=Finset.mem_add.mp
lemma zz [DecidableEq U1] {A B:V U1} {x:U1}:x∈A\B->x∈A/\ x∉B:=mem_sdiff.mp
lemma y9 [DecidableEq U1] {A B:V U1} {x:U1}:x∈A/\ x∉B->x∈A\B:=mem_sdiff.mpr
lemma zd [DecidableEq U2] {s:V U1} (f:U1->U2) {a:U1}:a∈s->f a∈s.image f:=mem_image_of_mem f
lemma zh [DecidableEq U2] {s:V U1} {f:U1->U2} {b:U2}:(∃ a∈s,f a=b)->b∈s.image f:=mem_image.mpr
lemma zv {s:V U1} {p:U1->Prop} [DecidablePred p] {x:U1}:x∈s/\ p x->x∈s.filter p:=mem_filter.mpr
lemma yf {s t:V U1}:s∈t.powerset->s⊆t:=mem_powerset.mp
lemma xp {s t:V U1}:s⊆t->s∈t.powerset:=mem_powerset.mpr
lemma zb {d:ℕ} {B:ZB d} {x:ZV d}:x∈B.tF->∀ i,B.lo i<=x i/\ x i<=B.hi i:=(mTF B x).mp
lemma zc {d:ℕ} {B:ZB d} {x:ZV d}:(∀ i,B.lo i<=x i/\ x i<=B.hi i)->x∈B.tF:=(mTF B x).mpr
lemma yn [DecidableEq G1] (s:V G1) (a:G1):#(s.image (·+a))=#s:=card_image_of_injective s (add_left_injective a)
lemma ya [DecidableEq G2] {f:U1->G2} {A B:V U1} (h:A⊆B):z8 f A<=z8 f B:=closure_mono (coe_subset.mpr (image_subset_image h))
lemma xb [DecidableEq U1] {A B C:V U1} (h:B⊆A) (a:B⊆C):(#(A\C):Y)<=(#A:Y)-#B:=by have:=Z (z6 (sdiff_subset_sdiff (Subset.rfl:A⊆A) a));rwa[card_sdiff_of_subset h,cast_sub (z6 h)] at this
lemma yy [DecidableEq G1] {A:V G1} (a:0∈A) (k:ℕ):0< #(F k A):=Nonempty.card_pos ⟨0,zMI a k⟩
abbrev zp:=@le_max_left
abbrev zm:=@le_max_right
abbrev xq:=@min_le_left
abbrev xr:=@min_le_right
abbrev yb:=@zMI
abbrev xc:=@zMSu
abbrev yg:=@iSS
abbrev z7:=@cast_nonneg
lemma yz {a b:Y} (c:0< a) {n:ℕ} (h:⌈b/a⌉₊<=n):b<=a*n:=by linarith[(div_le_iff₀ c).mp ((le_ceil _).trans (Z h))]
lemma x3 {s k:ℕ} (h:1<=s/k):s<=2*k*(s/k):=by have a:0< k:=(by by_contra b;have:k=0:=(by omega);rw[this,Nat.div_zero] at h;omega);have:=div_add_mod s k;have:=mod_lt s a;have:s< k*(s/k+1):=(by rw[Nat.mul_add,mul_one];omega);nlinarith
lemma xs {m:ℕ} (h:4<=m):1<=log m:=(log_exp 1).symm.trans_le (log_le_log (exp_pos 1) ((exp_one_lt_d9.le.trans (by norm_num)).trans (Z h)))
lemma xd {H n h:ℕ} {a:Y} (c:1< a) (d:(H:Y)^a< n) (e:(n:Y)<=(h:Y)^a):H<=h:=le_of_not_gt λ b=>by linarith[rpow_lt_rpow (z7 h) (zw b) (by linarith:(0:Y)< a)]
lemma yo {a c:Y} (b:0< a):∀ᶠ m:ℕ in atTop,c< (m:Y)^a:=eventually_atTop.mpr ⟨⌈(max 0 c+1)^(1/a)⌉₊+1,λ m e=>by have d:=rpow_le_rpow (by positivity) ((le_ceil _).trans (Z (by omega:⌈(max 0 c+1)^(1/a)⌉₊<=m))) b.le;rw[<-rpow_mul (by positivity),one_div_mul_cancel b.ne',rpow_one] at d;linarith[zm (0:Y) c]⟩
lemma yc (D:ℕ) (f:∀ d,1<=d->d<=D->ℕ):∃ M,∀ d a b,f d a b<=M:=⟨(Icc 1 D).sup λ d=>if h:1<=d/\ d<=D then f d h.1 h.2 else 0,λ d a b=>by simpa[dif_pos (And.intro a b)] using le_sup (f:=λ x=>if h:1<=x/\ x<=D then f x h.1 h.2 else 0) (mem_Icc.mpr ⟨a,b⟩)⟩
lemma xt {D:ℕ} (i:1<=D) (f:∀ d,1<=d->d<=D->Y) (j:∀ d a b,0< f d a b):∃ m,0< m/\ ∀ d a b,m<=f d a b:=by
 let g d:=if h:1<=d/\ d<=D then f d h.1 h.2 else 1;have hS:(Icc 1 D).Nonempty:=⟨1,mem_Icc.mpr ⟨le_rfl,i⟩⟩
 obtain⟨k,e,l⟩:=exists_mem_eq_inf' hS g;have c:=mem_Icc.mp e
 exact ⟨(Icc 1 D).inf' hS g,by rw[l];simpa[g,dif_pos c] using j k c.1 c.2,λ d a b=>by have h:=inf'_le g (mem_Icc.mpr ⟨a,b⟩);simp only[g,dif_pos (And.intro a b)] at h;exact h⟩
section
variable [DecidableEq G1] [DecidableEq G2]
lemma xu (f:G1→+G2) (S T:V G1):(S+T).image f=S.image f+T.image f:=by
 ext y;simp only[mem_image,Finset.mem_add];exact ⟨by rintro⟨_,⟨a,c,b,d,rfl⟩,rfl⟩;exact ⟨f a,⟨a,c,rfl⟩,f b,⟨b,d,rfl⟩,(map_add f _ _).symm⟩,by rintro⟨_,⟨a,c,rfl⟩,_,⟨b,d,rfl⟩,rfl⟩;exact ⟨a+b,⟨a,c,b,d,rfl⟩,map_add f _ _⟩⟩
lemma xv (f:G1→+G2):∀{n} (A:Fin n->V G1),(m4fs A).image f=m4fs λ i=>(A i).image f
 | 0,_=>by simp[m4fs]
 | _+1,A=>by simp[m4fs,xu,xv]
lemma wo (f:G1→+G2) {A:V G1} (hi:InjOn f (A:Set G1)):(z2 A).image f=z2 (A.image f):=by
 ext y;simp only[z2,sS,mem_image,mem_powerset]
 exact ⟨by rintro⟨_,⟨S,hS,rfl⟩,rfl⟩;exact ⟨S.image f,image_subset_image hS,by rw[sum_image λ a c b d=>hi (hS c) (hS d),map_sum]⟩,by rintro⟨T,e,rfl⟩;obtain⟨S,hS,rfl⟩:=subset_image_iff.mp e;exact ⟨_,⟨S,hS,rfl⟩,by rw[sum_image λ a c b d=>hi (hS c) (hS d),map_sum]⟩⟩
lemma xw {A B:V G1} (h:A⊆B):z2 A⊆z2 B:=image_subset_image (powerset_mono.mpr h)
lemma x4 (f:G1→+G2) (A:V G1):∀ k,(F k A).image f=F k (A.image f)
 | 0=>by simp[F,iSm]
 | k+1=>by simp[F,iSm,xu,x4]
lemma xe (A:V G1):F 1 A=A:=by ext x;simp[F,iSm,Finset.mem_add]
lemma xf {A:V ℤ} (a:0∈A) (k:ℕ):A⊆F (2^k) A:=by have h:F 1 A⊆F (2^k) A:=yg a (y1 k);rwa[xe] at h
lemma xg (A:V G1) (m:ℕ):∀ k,F (k*m) A=F k (F m A)
 | 0=>by simp[F,iSm]
 | k+1=>by dsimp[F] at*;rw[Nat.add_mul,one_mul,iSA,iSm];exact congrArg (·+iSm m A) (xg A m k)
lemma xx (A:V G1) (t:G1):∀ k,F k (A.image (·+t))=(F k A).image (·+(k:ℤ)•t)
 | 0=>by simp[F,iSm]
 | k+1=>by simp only[F,iSm,xx A t k];ext y;simp only[Finset.mem_add,mem_image];exact ⟨by rintro⟨_,⟨a,ha,rfl⟩,_,⟨b,hb,rfl⟩,rfl⟩;exact ⟨a+b,⟨a,ha,b,hb,rfl⟩,by push_cast;rw[add_smul,one_zsmul];abel⟩,by rintro⟨_,⟨a,ha,b,hb,rfl⟩,rfl⟩;exact ⟨a+(k:ℤ)•t,⟨a,ha,rfl⟩,b+t,⟨b,hb,rfl⟩,by push_cast;rw[add_smul,one_zsmul];abel⟩⟩
lemma xy {A:V G1} (e:0∈A) {k:ℕ} (f:1<=k):zf (F k A:Set G1)=zf (A:Set G1):=le_antisymm
 ((closure_le _).mpr λ v d=>by have g:∀ m,∀ w∈F m A,w∈zf (A:Set G1):=λ m=>(by induction m with | zero=>intro w c;simp only[F,iSm,mem_singleton] at c;subst c;exact zero_mem _ | succ m ih=>intro w c;rcases y8 c with ⟨a,i,b,j,rfl⟩;exact add_mem (ih a i) (subset_closure j));exact g k v d)
 ((closure_le _).mpr λ v d=>subset_closure ((by have h:F 1 A⊆F k A:=yg e f;rwa[xe] at h:A⊆F k A) d))
lemma yh {d:ℕ} (P:GAP G1 d):∀ k,F k P.tF=(W P k).tF
 | 0=>by ext x;simp only[F,iSm,mem_singleton,GAP.tF,mem_image,cB,mTF,W,nS,eval];exact ⟨λ h=>⟨0,λ _=>by simp,by simp[h]⟩,by rintro⟨n,hn,h⟩;have h0:∀ i,n i=0:=λ i=>(by have:=hn i;omega);simp[h0] at h;exact h.symm⟩
 | k+1=>by
  dsimp[F];rw[iSm];change F k P.tF+P.tF=_;rw[yh P k];ext x;simp only[Finset.mem_add,GAP.tF,mem_image,cB,mTF,W,nS,eval];constructor
  . rintro⟨_,⟨u,b,rfl⟩,_,⟨v,hv,rfl⟩,rfl⟩;refine ⟨u+v,λ i=>by have:=b i;have:=hv i;simp only[Pi.add_apply];push_cast;constructor <;> nlinarith,by push_cast;simp_rw[Pi.add_apply,add_smul,sum_add_distrib,one_zsmul];abel⟩
  . rintro⟨w,a,rfl⟩;let v:ZV d:=λ i=>max (P.lo i) (w i-(k:ℤ)*P.hi i);let u:=w-v
    refine ⟨(k:ℤ)•P.base+∑ i,u i•P.step i,⟨u,λ i=>?_,rfl⟩,P.base+∑ i,v i•P.step i,⟨v,λ i=>?_,rfl⟩,?_⟩
    . have:=a i;have:=P.hle i;dsimp[u,v];push_cast at*;rcases max_cases (P.lo i) (w i-(k:ℤ)*P.hi i) with ⟨h,_⟩|⟨h,_⟩ <;> constructor <;> nlinarith
    . have:=a i;have:=P.hle i;dsimp[v];push_cast at*;rcases max_cases (P.lo i) (w i-(k:ℤ)*P.hi i) with ⟨h,_⟩|⟨h,_⟩ <;> constructor <;> nlinarith
    . push_cast;rw[add_smul,one_zsmul,show ∑ x,w x•P.step x=∑ i,u i•P.step i+∑ i,v i•P.step i by rw[<-sum_add_distrib];exact sum_congr rfl λ i _=>by simp[u,<-add_smul]];abel
end
lemma xh {A:V ℤ} {n:ℕ} (c:A⊆zi n):∀ k,F k A⊆zi (k*n)
 | 0=>λ x hx=>by simp only[F,iSm,mem_singleton] at hx;subst hx;simp
 | k+1=>λ x hx=>by rcases y8 hx with ⟨a,ha,b,hb,rfl⟩;have:=mem_Icc.mp (xh c k ha);have:=mem_Icc.mp (c hb);rw[mem_Icc];push_cast at*;constructor <;> nlinarith
lemma xi {A:V ℤ} {n:ℕ} (a:A⊆zi n) (k:ℕ):#(F k A)<=2*k*n+1:=
 (z6 (xh a k)).trans (by rw[card_Icc,show ((k*n:ℕ):ℤ)+1 - -(k*n:ℕ)=((2*k*n+1:ℕ):ℤ) by push_cast;ring,toNat_natCast])
lemma x5 {a b:ℤ} {k:ℕ} (h:a<=b) (c:1<=k):((k:ℤ)*b-k*a+1).toNat<=k*(b-a+1).toNat:=by
 rw[show (k:ℤ)*b-k*a+1=((k*(b-a).toNat+1:ℕ):ℤ) by push_cast;rw[toNat_of_nonneg (by omega)];ring,toNat_natCast,show (b-a+1).toNat=(b-a).toNat+1 by omega,Nat.mul_add,mul_one];omega
lemma xz {d:ℕ} {P:GAP ℤ d} (a:∀ j,2<=P.width j) (h:ℕ) (j:Fin d):h<=(W P h).width j:=by
 have b:=a j;dsimp[GAP.width,cB,W,nS,ZB.width] at b ⊢;have:=P.hle j;have:=le_mul_of_one_le_right (z7 h) (show (1:ℤ)<=P.hi j-P.lo j by omega);have:(h:ℤ)*P.hi j-h*P.lo j=(h:ℤ)*(P.hi j-P.lo j):=(by ring);omega
lemma yp {d:ℕ} {P Q:GAP G1 d} (c:Q.iP) (a:z5 P⊆z5 Q) (e:P.step=Q.step) (f:P.base=0) (b:Q.base=0):P.iP:=
 λ u g v i j=>c (a g) (a i) (by simpa[eval,f,b,e] using j)
lemma w0 {d:ℕ} {P:GAP G1 d} (a:P.base=0) (b:P.iP):(W P 1).iP:=
 yp b (λ w c=>by simpa[z5,mTF,cB,W,nS] using c) rfl (by simp[W,nS,a]) a
lemma wp {d:ℕ} (P:GAP ℤ d) (g:0∈P.tF) (j:(W P 2).iP):
 ∃ Q:GAP ℤ d,Q.iC/\ Q.tF=P.tF/\ (∀ i,Q.width i=P.width i)/\ Q.vol=P.vol/\ (W Q 2).iP:=by
 rcases z0 g with ⟨m,k,e⟩;have hm':=zb k;let Q:GAP ℤ d:=⟨0,P.step,λ i=>P.lo i-m i,λ i=>P.hi i-m i,λ i=>by have:=P.hle i;omega⟩
 have c:∀ n,Q.eval n=P.eval (n+m):=λ n=>by simp only[eval,Q,zero_add,Pi.add_apply,smul_eq_mul,add_mul,sum_add_distrib];simp only[eval,smul_eq_mul] at e;linarith
 have a:∀ i,Q.width i=P.width i:=λ i=>by dsimp[GAP.width,cB,ZB.width,Q];congr 1;omega
 refine ⟨Q,⟨rfl,λ i=>by have:=hm' i;dsimp[cB,Q] at*;omega⟩,by ext x;simp only[GAP.tF,mem_image,cB,mTF];exact ⟨by rintro⟨n,b,rfl⟩;exact ⟨n+m,λ i=>by have:=b i;dsimp[Q] at*;omega,(c n).symm⟩,by rintro⟨n,b,rfl⟩;exact ⟨n-m,λ i=>by have:=b i;dsimp[Q];omega,by rw[c,sub_add_cancel]⟩⟩,a,by unfold GAP.vol ZB.vol;exact prod_congr rfl λ i _=>a i,λ u l v o f=>?_⟩
 have h':∀ w∈z5 (W Q 2),w+(2:ℤ)•m∈z5 (W P 2):=λ w a=>zc λ i=>by have:=zb a i;dsimp[cB,W,nS,Q] at*;constructor <;> linarith
 exact add_left_injective ((2:ℤ)•m) (j (h' u l) (h' v o) (by simp only[eval,W,nS,Q,smul_eq_mul] at f ⊢;simp only[Pi.add_apply,Pi.smul_apply,smul_eq_mul,add_mul,sum_add_distrib];linarith))
def yi {d k:ℕ} (P:GAP G1 d) (e:Fin k↪Fin d):GAP G1 k:=⟨P.base,λ i=>P.step (e i),λ i=>P.lo (e i),λ i=>P.hi (e i),λ i=>P.hle (e i)⟩
lemma w1 {d k:ℕ} (P:GAP G1 d) (e:Fin k↪Fin d) (n:ZV k):(yi P e).eval n=P.eval λ j=>if h:∃ i,e i=j then n (choose h) else 0:=by
 simp only[eval,yi];congr 1;rw[<-sum_subset (subset_univ (univ.image e)),sum_image λ _ _ _ _ h=>e.injective h]
 exact sum_congr rfl λ i _=>by have a:∃ i',e i'=e i:=⟨i,rfl⟩;rw[dif_pos a,e.injective (choose_spec a)]
 intro j _ b;rw[dif_neg λ⟨i,hi⟩=>b (hi▸zd e (mem_univ i)),zero_smul]
lemma yq {d:ℕ} (P:GAP G1 d) (c:Y) (h:P.iC) (hc:0<=c:=by positivity):(z3 P c h hc).iC:=
 ⟨rfl,λ i=>⟨ceil_le.mpr (by simpa using mul_nonpos_of_nonneg_of_nonpos hc (by exact_mod_cast (h.2 i).1)),le_floor.mpr (by simpa using mul_nonneg hc (by exact_mod_cast (h.2 i).2))⟩⟩
lemma yr {d:ℕ} (P:GAP G1 d) (c:Y) (a:P.iS) (hc:0<=c:=by positivity):(z3 P c (ze a) hc).iS:=
 ⟨rfl,λ i=>by dsimp[z3,rS];rw[a.2 i];push_cast;rw[mul_neg,ceil_neg]⟩
lemma w2 {d:ℕ} (P:GAP G1 d) {a b:Y} (hle:a<=b) (hc:P.iC) (c:0<=a:=by positivity) (h2:0<=b:=by positivity):
 z5 (z3 P a hc c)⊆z5 (z3 P b hc h2):=λ n e=>zc λ i=>by
 have:=zb e i;dsimp[cB,z3,rS] at*;exact ⟨(ceil_mono (mul_le_mul_of_nonpos_right hle (by exact_mod_cast (hc.2 i).1))).trans this.1,this.2.trans (floor_mono (zj hle (yx (hc.2 i).2)))⟩
lemma x6 {d:ℕ} (P:GAP G1 d) (h:P.iC) (k:ℕ):z5 (z3 P k h (z7 k))=z5 (W P k):=by
 ext n;simp only[z5,mTF,cB,z3,rS,W,nS]
 exact forall_congr' λ i=>by rw[show (k:Y)*P.lo i=(((k:ℤ)*P.lo i:ℤ):Y) by push_cast;rfl,show (k:Y)*P.hi i=(((k:ℤ)*P.hi i:ℤ):Y) by push_cast;rfl,ceil_intCast,floor_intCast]
lemma xj {d:ℕ} (P:GAP G1 d) {c:Y} (h:P.iC) {k:ℕ} (a:(k:Y)<=c) (hc:0<=c:=by positivity):z5 (W P k)⊆z5 (z3 P c h hc):=by rw[<-x6 P h k];exact w2 P a h (z7 k) hc
lemma w3 {d:ℕ} {P Q:GAP G1 d} (e:P.iS) (f:Q.iS) {a b:Y} (h:∀ j,a*P.hi j<=b*Q.hi j) (i:0<=a:=by positivity) (hb:0<=b:=by positivity):
 z5 (z3 P a (ze e) i)⊆z5 (z3 Q b (ze f) hb):=λ w k=>zc λ j=>by
 have c:=zb k j;dsimp[cB,z3,rS] at c ⊢;have l:=(zy c.2).trans (floor_le _);have g:=(Int.le_ceil _).trans (zy c.1)
 rw[e.2 j] at g;rw[f.2 j];push_cast at g ⊢;have:=h j;exact ⟨ceil_le.mpr (by linarith),le_floor.mpr (by linarith)⟩
lemma x7 {d:ℕ} (P:GAP G1 d) {k:ℕ} (a:1<=k):(W P k).vol<=k^d*P.vol:=by
 rw[show k^d*P.vol=∏ i:Fin d,k*P.width i by simp[GAP.vol,GAP.width,ZB.vol,prod_mul_distrib]];unfold GAP.vol ZB.vol;exact prod_le_prod' λ i _=>x5 (P.hle i) a
noncomputable def z4 [DecidableEq G1] {d:ℕ} (P:GAP G1 d) (a:G1):ZV d:=if h:∃ v∈z5 P,P.eval v=a then choose h else 0
lemma ys [DecidableEq G1] {d:ℕ} (P:GAP G1 d) {a:G1} (b:a∈P.tF):z4 P a∈z5 P:=by have h:=z0 b;simp only[z4,dif_pos h];exact (choose_spec h).1
lemma y3 [DecidableEq G1] {d:ℕ} (P:GAP G1 d) {a:G1} (b:a∈P.tF):P.eval (z4 P a)=a:=by have h:=z0 b;simp only[z4,dif_pos h];exact (choose_spec h).2
lemma yt [DecidableEq G1] {d:ℕ} {P:GAP G1 d} (hc:P.iC) (a:P.iP):z4 P 0=0:=by
 have b:P.eval 0=0:=(by simp[eval,hc.1]);rw[<-b];exact a (ys P (zd _ (zc hc.2))) (zc hc.2) (y3 P (zd _ (zc hc.2)))
def zq {d:ℕ} (P:GAP G1 d) (a:P.base=0):ZV d→+G1:=⟨⟨P.eval,by simp[eval,a]⟩,λ u v=>by simp only[eval,a,zero_add,Pi.add_apply,add_smul,sum_add_distrib]⟩
lemma w4 [DecidableEq G1] {d:ℕ} (P:GAP G1 d) (b:P.base=0) {S:V G1} (hS:S⊆P.tF) (k:ℕ):(F k (S.image (z4 P))).image (zq P b)=F k S:=by
 rw[x4 (zq P b)];congr 1;ext a;simp only[mem_image];exact ⟨by rintro⟨_,⟨s,e,rfl⟩,rfl⟩;rwa[show zq P b (z4 P s)=s from y3 P (hS e)],λ c=>⟨z4 P a,⟨a,c,rfl⟩,y3 P (hS c)⟩⟩
lemma xk [DecidableEq G1] {d:ℕ} (P:GAP G1 d) {S:V G1} (hS:S⊆P.tF):∀ k,F k (S.image (z4 P))⊆(z5 (W P k)).filter (·∈z8 (z4 P) S)
 | 0=>λ v hv=>by simp only[F,iSm,mem_singleton] at hv;subst hv;exact zv ⟨zc λ _=>by simp[cB,W,nS],zero_mem _⟩
 | k+1=>λ v hv=>by rcases y8 hv with ⟨u,hu,w,hw,rfl⟩;have hu':=zg (xk P hS k hu);rcases z0 hw with ⟨s,a,rfl⟩;exact zv ⟨zc λ j=>by have:=zb hu'.1 j;have:=zb (ys P (hS a)) j;dsimp[cB,W,nS] at*;change _<=u j+z4 P s j/\ u j+z4 P s j<=_;constructor <;> linarith,add_mem hu'.2 (subset_closure (zd _ a))⟩
lemma w5 {d:ℕ} {S:V (ZV d)} {v:Fin d->ZV d} (f:∀ j,v j∈zf (S:Set (ZV d))) (g:∀ x∈zf (S:Set (ZV d)),∃! n:ZV d,∑ i,n i•v i=x) (j:Fin d):∃ x∈S,∃ n:ZV d,∑ i,n i•v i=x/\ n j≠0:=by
 by_contra l;push Not at l
 let o:AddSubgroup (ZV d):=⟨{carrier:={x|∃ n:ZV d,∑ i,n i•v i=x/\ n j=0},add_mem':=by rintro _ _ ⟨a,rfl,c⟩ ⟨b,rfl,h2⟩;exact ⟨a+b,by simp[add_smul,sum_add_distrib],by simp[c,h2]⟩,zero_mem':=⟨0,by simp,rfl⟩},by rintro _ ⟨a,rfl,c⟩;exact ⟨-a,by simp[neg_smul,sum_neg_distrib],by simp[c]⟩⟩
 rcases ((closure_le _).mpr λ x m=>by obtain⟨n,e,_⟩:=g x (subset_closure m);exact ⟨n,e,l x m n e⟩:zf (S:Set (ZV d))<=o) (f j) with ⟨n,e,p⟩
 obtain⟨_,_,k⟩:=g (v j) (f j);have c:=k n e|>.trans (k (single j 1) (by simp[Pi.single_apply])).symm;have:n j=1:=(by simp[c]);omega
lemma w6 {d:ℕ} {P:GAP (ZV d) d} (hS:P.iS) {Q:ZB d} {b:ℕ} (a:∃ t:ZV d,∀ x∈P.tF,∀ i,(b:ℤ)*Q.lo i<=(x-t) i/\ (x-t) i<=(b:ℤ)*Q.hi i):∀ x∈P.tF,∀ i,2*|x i| <=(b:ℤ)*(Q.hi i-Q.lo i):=by
 rcases a with ⟨t,a⟩;intro x e i
 have c:-x∈P.tF:=by rcases z0 e with ⟨n,c,rfl⟩;exact zh ⟨-n,zc λ j=>by have:=zb c j;have:=hS.2 j;dsimp[cB] at*;omega,by simp[eval,hS.1,neg_smul,sum_neg_distrib]⟩
 have f:=a x e i;have g:=a (-x) c i;simp only[Pi.sub_apply,Pi.neg_apply] at f g;rcases abs_cases (x i) with ⟨h,_⟩|⟨h,_⟩ <;> linarith
lemma w7 [DecidableEq G1] {d:ℕ} (P:GAP G1 d) {t k:ℕ} (R:1<=k) (f:¬(W P t).iP):#(W P k).tF<=t*d*k^(d-1)*P.vol:=by
 unfold iP InjOn at f;push Not at f;rcases f with ⟨u,S,v,T,U,Q⟩;let z:=u-v
 have A:∑ i,z i•P.step i=0:=by simp_rw[z,Pi.sub_apply,sub_smul,sum_sub_distrib,sub_eq_zero];exact add_left_cancel (a:=(t:ℤ)•P.base) (by simpa[eval,W,nS] using U)
 have C:∀ i,|z i| <=(t:ℤ)*(P.hi i-P.lo i):=λ i=>abs_le.mpr (by have:=zb S i;have:=zb T i;dsimp[cB,W,nS,z] at*;constructor <;> linarith)
 have ⟨i0,hi0⟩:∃ i0,z i0≠0:=by by_contra h;push Not at h;exact sub_ne_zero.mpr Q (funext h)
 let B:=z5 (W P k);let D:=B.filter λ b=>b-z∉B
 have s:(W P k).tF⊆D.image (W P k).eval:=λ x hx=>by
  rcases z0 hx with ⟨b,c,rfl⟩;let M:=k*(P.hi i0-P.lo i0).toNat+2
  have w:∃ m:ℕ,b-(m:ℤ)•z∉B:=⟨M,λ hm=>by have:=zb c i0;have:=zb hm i0;dsimp[cB,W,nS] at*;have h3:(M:ℤ)*|z i0| <=(k:ℤ)*(P.hi i0-P.lo i0):=(by simpa[abs_mul,abs_of_nonneg (z7 M:(0:ℤ)<=M)] using (abs_le.mpr ⟨by linarith,by linarith⟩:|(b i0-(M:ℤ)*z i0)-b i0| <=(k:ℤ)*(P.hi i0-P.lo i0)));have:=le_mul_of_one_le_right (z7 M) (one_le_abs hi0);have:(M:ℤ)=(k:ℤ)*(P.hi i0-P.lo i0)+2:=(by dsimp[M];rw[toNat_of_nonneg (sub_nonneg.mpr (P.hle i0))]);linarith⟩
  let l:=find w;have p:=find_spec w;have E:0< l:=Nat.pos_of_ne_zero λ h=>p (by change b-(l:ℤ)•z∈B;rw[h];simpa using c)
  refine zh ⟨b-((l-1:ℕ):ℤ)•z,zv ⟨not_not.mp (find_min w (Nat.sub_lt E zero_lt_one)),λ h=>p (by convert h using 1;ext j;dsimp;have e:((l-1:ℕ):ℤ)+1=l:=(by omega);rw[<-e];ring)⟩,?_⟩
  simp only[eval,W,nS,Pi.sub_apply,Pi.smul_apply,smul_eq_mul];congr 1;simp_rw[sub_smul,mul_smul];rw[sum_sub_distrib,<-smul_sum,A,smul_zero,sub_zero]
 let y j:=B.filter λ b=>¬((k:ℤ)*P.lo j<=b j-z j/\ b j-z j<=(k:ℤ)*P.hi j)
 have G:D⊆univ.biUnion y:=λ b c=>by have hb':=zg c;have I:¬∀ j,(k:ℤ)*P.lo j<=(b-z) j/\ (b-z) j<=(k:ℤ)*P.hi j:=λ ha=>hb'.2 (zc ha);push Not at I;rcases I with ⟨j,X⟩;exact mem_biUnion.mpr ⟨j,mem_univ j,zv ⟨hb'.1,λ h=>not_lt_of_ge h.2 (X h.1)⟩⟩
 have J:∀ j,#(y j)<=t*k^(d-1)*P.vol:=λ j=>by
  let n:=if 0<=z j then Ico ((k:ℤ)*P.lo j) ((k:ℤ)*P.lo j+z j) else Ioc ((k:ℤ)*P.hi j+z j) ((k:ℤ)*P.hi j)
  have K:y j⊆piFinset λ i=>if i=j then n else Icc ((k:ℤ)*P.lo i) ((k:ℤ)*P.hi i):=λ b c=>by
   have hb':=zg c;have L:=zb hb'.1;rw[mem_piFinset];intro i;by_cases r:i=j
   . subst r;rw[if_pos rfl];have hi:=L i;dsimp[cB,W,nS] at hi;by_cases o:0<=z i;simp only[n,if_pos o,mem_Ico];exact ⟨hi.1,by by_contra;exact hb'.2 (by omega)⟩;simp only[n,if_neg o,mem_Ioc];exact ⟨by by_contra;exact hb'.2 (by omega),hi.2⟩
   . rw[if_neg r];exact mem_Icc.mpr (L i)
  have N:#n<=t*P.width j:=by
   have O:=C j;have h2:=P.hle j;have hle:(P.hi j-P.lo j).toNat<=P.width j:=(by dsimp[GAP.width,cB,ZB.width];omega);have q:(t:ℤ)*(P.hi j-P.lo j)=((t*(P.hi j-P.lo j).toNat:ℕ):ℤ):=(by push_cast;rw[toNat_of_nonneg (by omega)])
   dsimp[n];split_ifs with o <;> [rw[card_Ico,add_sub_cancel_left];rw[card_Ioc,show (k:ℤ)*P.hi j-(k*P.hi j+z j)=-z j by ring]]
   . rw[abs_of_nonneg o,q] at O;exact (by omega:(z j).toNat<=t*(P.hi j-P.lo j).toNat).trans (zu t hle)
   . rw[abs_of_neg (not_le.mp o),q] at O;exact (by omega:(-z j).toNat<=t*(P.hi j-P.lo j).toNat).trans (zu t hle)
  exact (z6 K).trans ((card_piFinset _).trans_le ((prod_le_prod' (g:=λ i=>if i=j then t*P.width j else k*P.width i) λ i _=>by split_ifs;exact N;rw[card_Icc,show (k:ℤ)*P.hi i+1-k*P.lo i=k*P.hi i-k*P.lo i+1 by ring];exact x5 (P.hle i) R).trans_eq (by rw[<-mul_prod_erase univ _ (mem_univ j),if_pos rfl,prod_congr rfl λ i hi=>if_neg (ne_of_mem_erase hi),prod_mul_distrib,prod_const,card_erase_of_mem (mem_univ j),card_univ,Fintype.card_fin];unfold GAP.vol ZB.vol GAP.width;rw[<-mul_prod_erase univ (λ i=>P.cB.width i) (mem_univ j)];ring)))
 exact (z6 s).trans (card_image_le.trans ((z6 G).trans (card_biUnion_le.trans ((sum_le_sum λ j _=>J j).trans_eq (by simp;ring)))))
lemma xl [DecidableEq G1] {A:V G1} (a:0∈A) {x:G1} (b:x∈A):∀{t r:ℕ},t<=r->(t:ℤ)•x∈F r A
 | 0,r,_=>by simpa using yb a r
 | t+1,r,h=>by rw[show r=(r-1)+1 by omega,F,iSm];have h2:=add_mem_add (xl a b (by omega:t<=r-1)) b;rwa[show (t:ℤ)•x+x=((t+1:ℕ):ℤ)•x by push_cast;rw[add_smul,one_zsmul]] at h2
lemma w8 {d:ℕ} {Q:GAP ℤ d} (r:Q.iC) (s:Q.iP) {P:GAP (ZV d) d} (b:P.iS) (t:∀ n:ZV d,∑ i,n i•P.step i=0->n=0) {a:ℕ} (E:1<=a)
 (y:∀ x∈P.tF,∀ i,2*|x i| <=(a:ℤ)*(Q.hi i-Q.lo i)):(z3 (⟨0,λ i=>Q.eval (P.step i),P.lo,P.hi,P.hle⟩:GAP ℤ d) (1/(a:Y)) (ze ⟨rfl,b.2⟩)).iP:=by
 let Q':GAP ℤ d:=⟨0,λ i=>Q.eval (P.step i),P.lo,P.hi,P.hle⟩;let g:=zq Q r.1;have hS:Q'.iS:=⟨rfl,b.2⟩
 have e:∀ n,Q'.eval n=g (P.eval n):=λ n=>by simp only[eval,Q',b.1,zero_add,map_sum,map_zsmul];rfl
 let m:ZV d:=λ i=>Q.lo i+(Q.hi i-Q.lo i)/2
 have c:∀ w∈z5 (z3 Q' (1/(a:Y)) (ze hS)),m+P.eval w∈z5 Q:=λ w D=>by
  have k:(a:ℤ)•w∈z5 P:=zc λ j=>by have l:=zb D j;dsimp[cB,z3,rS,Q'] at l ⊢;have o:=zo (by omega:0< a);have A:=za ((Int.le_ceil _).trans (zy l.1)) o.le;have p:=za ((zy l.2).trans (floor_le _)) o.le;field_simp[o.ne'] at A p;exact ⟨by exact_mod_cast (by linarith:(P.lo j:Y)<=(a:Y)*w j),by exact_mod_cast (by linarith:(a:Y)*w j<=P.hi j)⟩
  have q:(a:ℤ)•P.eval w∈P.tF:=by rw[show (a:ℤ)•P.eval w=P.eval ((a:ℤ)•w) by simp[eval,b.1,smul_sum,mul_smul]];exact zd _ k
  exact zc λ i=>by have p:=y _ q i;simp only[Pi.smul_apply,smul_eq_mul,abs_mul,abs_of_nonneg (z7 a:(0:ℤ)<=a)] at p;have:(0:ℤ)< a:=(by omega);have:2*|(P.eval w) i| <=Q.hi i-Q.lo i:=(by nlinarith);have:=Q.hle i;dsimp[m,cB];rcases abs_cases ((P.eval w) i) with ⟨h,_⟩|⟨h,_⟩ <;> omega
 intro u B v C z
 have f:=add_left_cancel (s (c u B) (c v C) (by change g (m+P.eval u)=g (m+P.eval v);rw[map_add,map_add,<-e u,<-e v,show Q'.eval u=Q'.eval v by simpa[eval,z3,rS,Q'] using z]))
 simp only[eval,b.1,zero_add] at f;exact sub_eq_zero.mp (t (u-v) (by simp_rw[Pi.sub_apply,sub_smul,sum_sub_distrib,f,sub_self]))
lemma w9 {d:ℕ} (P:GAP G1 d) (c:P.base=0) (a b:ℕ):W (W P a) b=W P (b*a):=by
 cases P;simp only[W,nS] at c ⊢;subst c;simp only[smul_zero];congr 1 <;> funext j <;> push_cast <;> ring
lemma x8 {f:ℕ->Y} {c:Y} (hc:0<=c) {a:ℕ}:∀ m,(∀ k< m,c*f (a+k)<=f (a+k+1))->c^m*f a<=f (a+m)
 | 0,_=>by simp
 | m+1,h=>by rw[pow_succ',mul_assoc];exact (za (x8 hc m λ k hk=>h k (by omega)) hc).trans (by simpa[add_assoc] using h m (Nat.lt_succ_self m))
lemma wq {D T n h:ℕ} {e:Y} {A:V ℤ} (l:1<=T) (a4:e+1< D) (L:A⊆zi n) (B:0∈A) (M:2<=#A)
 (a5:(n:Y)<=(h:Y)^e) (C:4*T*2^(T+2)<=h) (a2:3*((2*T*2^T:ℕ):Y)^(D+1)< (h:Y)^(1/2:Y)):
 let d:=zs (h/T)
 ∃ d' y:ℕ,1<=d'/\ d'<=D/\ T<=y/\ y< d/\ ((#(F (2^(y+1)) A):Y)<=(2:Y)^((d':Y)+1/2)*#(F (2^y) A)) /\
  ∀ z∈Ico T d,(2:Y)^((d':Y)-1/2)*#(F (2^z) A)< #(F (2^(z+1)) A):=by
 intro d;have N:T<=h:=le_trans (le_mul_of_pos_left T (by omega:0< 4)) ((le_mul_of_pos_right _ (y1 _)).trans C)
 have O:=pow_log_le_self 2 (div_pos N l).ne';have P:=lt_pow_succ_log_self (by omega:1< 2) (h/T)
 have a6:T+2<=d:=le_log_of_pow_le (by omega) ((le_div_iff_mul_le l).mpr (by nlinarith))
 have p:∃ d':ℕ,∃ z∈Ico T d,(#(F (2^(z+1)) A):Y)<=(2:Y)^((d':Y)+1/2)*#(F (2^z) A):=
  ⟨#(F (2^(T+1)) A),T,mem_Ico.mpr ⟨le_rfl,by omega⟩,((Z lt_two_pow_self.le).trans (by push_cast;rw[<-rpow_natCast];exact rpow_le_rpow_of_exponent_le (by norm_num) (by linarith))).trans (le_mul_of_one_le_right (by positivity) (zk (yy B _)))⟩
 let d':=find p;have g:∃ z∈Ico T d,(#(F (2^(z+1)) A):Y)<=(2:Y)^((d':Y)+1/2)*#(F (2^z) A):=find_spec p
 have i:1<=d':=by
  by_contra h0';have Q:d'=0:=(by omega);rcases g with ⟨z,_,u⟩;rw[Q] at u
  let X:=F (2^z) A;have a7:2<=#X:=M.trans (z6 (xf B z));have q:X.Nonempty:=card_pos.mp (by omega)
  have R:2*#X-1<=#(X+X):=by
   let a:=X.min' q;let b:=X.max' q
   have hd:Disjoint (X.image (a+·)) ((X.erase a).image (b+·)):=disjoint_left.mpr λ y j o=>by rcases z0 j with ⟨x1,a0,rfl⟩;rcases z0 o with ⟨x2,w,he⟩;have:=(mem_erase.mp w).1;have:=le_max' X x1 a0;have:=min'_le X x2 (mem_erase.mp w).2;omega
   have:=z6 (union_subset (λ y K=>by rcases z0 K with ⟨x,J,rfl⟩;exact add_mem_add (min'_mem X q) J) (λ y K=>by rcases z0 K with ⟨x,J,rfl⟩;exact add_mem_add (max'_mem X q) (mem_of_mem_erase J)):X.image (a+·)∪(X.erase a).image (b+·)⊆X+X)
   rw[card_union_of_disjoint hd,card_image_of_injective _ (add_right_injective a),card_image_of_injective _ (add_right_injective b),card_erase_of_mem (min'_mem X q)] at this;omega
  rw[show X+X=F (2^(z+1)) A by dsimp[X,F];rw[<-iSA,<-mul_two,<-pow_succ]] at R
  have:((2:Y)^(1/2:Y))^2< (3/2:Y)^2:=(by rw[<-rpow_natCast,<-rpow_mul (by norm_num)];norm_num)
  have S:=Z (by omega:3*#X<=2*#(F (2^(z+1)) A));push_cast at S;simp only[cast_zero,zero_add] at u
  nlinarith[rpow_nonneg (by norm_num:(0:Y)<=2) (1/2:Y),zo (by omega:0< #X)]
 have r:∀ z∈Ico T d,(2:Y)^((d':Y)-1/2)*#(F (2^z) A)< #(F (2^(z+1)) A):=λ z u=>by
  have j:=find_min p (Nat.sub_lt i zero_lt_one);push Not at j;have:=j z u;rwa[show ((d'-1:ℕ):Y)+1/2=(d':Y)-1/2 by rw[cast_sub i];push_cast;ring] at this
 have E:d'<=D:=le_of_not_gt λ a1=>by
  have m:=zl h
  have v:=x8 (f:=λ z=>(#(F (2^z) A):Y)) (c:=(2:Y)^((D:Y)+1/2)) (by positivity) (a:=T) (d-T) λ k hk=>(zj (rpow_le_rpow_of_exponent_le (by norm_num) (by have:=Z a1;push_cast at this;linarith))).trans (r (T+k) (mem_Ico.mpr ⟨by omega,by omega⟩)).le
  rw[add_sub_of_le (by omega:T<=d),<-rpow_natCast,<-rpow_mul (by norm_num)] at v
  have G:=(le_mul_of_one_le_right (by positivity) (zk (yy B _))).trans v
  have I:(#(F (2^d) A):Y)<=3*(h:Y)^(1+e):=(by have o:=Z ((xi L (2^d)).trans (by have:=O.trans (div_le_self h T);nlinarith:2*2^d*n+1<=2*h*n+1));have h3:(h:Y)*n<=(h:Y)^(1+e):=(by rw[rpow_add m,rpow_one];gcongr);have:=one_le_mul_of_one_le_of_one_le (zx h) (zk (by have:=z6 L;rw[card_Icc] at this;omega:1<=n));push_cast at o;linarith)
  have a3:(h:Y)/((2*T*2^T:ℕ):Y)<=(2:Y)^(d-T):=(div_le_iff₀ (by positivity)).mpr (by have j:h< T*2^(d+1):=(show h< T*(h/T+1) by have:=div_add_mod h T;have:=mod_lt h l;nlinarith).trans_le (zu T P);have o:2^(d+1)=2*2^T*2^(d-T):=(by rw[pow_succ,mul_assoc,<-pow_add,add_sub_of_le (by omega:T<=d),mul_comm]);exact_mod_cast (by rw[o] at j;nlinarith:h<=2^(d-T)*(2*T*2^T)))
  have s:((h:Y)/((2*T*2^T:ℕ):Y))^((D:Y)+1/2)<=3*(h:Y)^(1+e):=le_trans (by rw[show (2:Y)^(((D:Y)+1/2)*((d-T:ℕ):Y))=((2:Y)^(d-T))^((D:Y)+1/2) by rw[<-rpow_natCast,<-rpow_mul (by norm_num),mul_comm]];gcongr) (G.trans I)
  rw[div_rpow m.le (by positivity),div_le_iff₀ (by positivity)] at s
  have U:(h:Y)^(1/2:Y)*(h:Y)^(1+e)<=(h:Y)^((D:Y)+1/2):=(by rw[<-rpow_add m];exact rpow_le_rpow_of_exponent_le (zk (by omega)) (by linarith))
  have j:=le_of_mul_le_mul_right (by linarith[U,s]:(h:Y)^(1/2:Y)*(h:Y)^(1+e)<=3*((2*T*2^T:ℕ):Y)^((D:Y)+1/2)*(h:Y)^(1+e)) (rpow_pos_of_pos m (1+e))
  have o:((2*T*2^T:ℕ):Y)^((D:Y)+1/2)<=((2*T*2^T:ℕ):Y)^(D+1):=(by rw[<-rpow_natCast];exact rpow_le_rpow_of_exponent_le (zk (Nat.mul_pos (Nat.mul_pos (by omega) l) (y1 _))) (by push_cast;linarith))
  linarith
 have t:=find_spec g;exact ⟨d',find g,i,E,(mem_Ico.mp t.1).1,(mem_Ico.mp t.1).2,t.2,r⟩
lemma wa {d C r y m:ℕ} {A:V ℤ} {b:GAP ℤ d} (a:b.iS) (o:0∈A) (q:1<=C)
 (f:∃ k:ℤ,b.tF.image (·+k)⊆F (C*2^(y+1)) A) (hle:(2^r/C+1)*(C*2^(y+1))<=m):
 #(W (z3 b (1/(C:Y)) (ze a)) (2^r)).tF<=#(F m A):=by
 obtain⟨k,n⟩:=f;let c:=2^r/C+1;let R:=z3 b (1/(C:Y)) (ze a);have e:=yr b (1/(C:Y)) a
 have g:(W R (2^r)).tF⊆(W b c).tF:=λ z p=>by
  rcases z0 p with ⟨v,l,rfl⟩;refine zh ⟨v,?_,by simp[eval,W,nS,R,rS,a.1]⟩
  change v∈z5 (W R (2^r)) at l;rw[<-x6 R (ze e)] at l;change v∈z5 (W b c);rw[<-x6 b (ze a)]
  exact w3 e a (λ j=>by
   have s:(R.hi j:Y)<=(b.hi j:Y)/C:=(by simpa[R,z3,rS,one_div,div_eq_inv_mul] using floor_le (1/(C:Y)*b.hi j))
   have t:((2^r:ℕ):Y)/C<=(c:Y):=(div_le_iff₀ (zo (by omega))).mpr (by have:=div_add_mod (2^r) C;have:=mod_lt (2^r) (by omega:0< C);exact_mod_cast (show 2^r<=c*C by dsimp[c];nlinarith))
   have:=yx ((ze a).2 j).2;calc ((2^r:ℕ):Y)*R.hi j<=((2^r:ℕ):Y)*((b.hi j:Y)/C):=by gcongr
    _=((2^r:ℕ):Y)/C*b.hi j:=by ring
    _<=(c:Y)*b.hi j:=by gcongr) (by positivity) (by positivity) l
 have i:(W b c).tF.image (·+(c:ℤ)•k)⊆F (c*(C*2^(y+1))) A:=(by rw[<-yh,<-xx,xg];exact iSM n c)
 exact (z6 g).trans ((yn _ _).symm.trans_le (z6 (i.trans (yg o hle))))
lemma wr {D C T b h n y d o:ℕ} {A:V ℤ} {g:GAP ℤ d} (c:g.iS) (h0:0∈A) (a0:1<=C) (a1:1<=T)
 (a2:2*C<=2^b) (a3:1<=d) (E:d<=n) (G:n<=D) (ai:T<=y)
 (N:∀ z∈Ico T (zs (h/T)),(2:Y)^((n:Y)-1/2)*#(F (2^z) A)< #(F (2^(z+1)) A))
 (J:∀ j,2<=(z3 g (1/(C:Y)) (ze c)).hi j/\ g.hi j< 2*(C:ℤ)*(z3 g (1/(C:Y)) (ze c)).hi j)
 (O:(z3 g (1/(C:Y)) (ze c)).iP) (P:∃ x0:ℤ,g.tF.image (·+x0)⊆F (C*2^(y+1)) A)
 (a4:∀ a∈A,∃ v:ZV d,g.eval v=a/\ ∀ j,|v j| *(2^(y+1):ℤ)<=g.hi j)
 (a5:2^o*(4*C*T*2^(2*(2*D+2*D*(2*b+3)+4)+2*b+4)*2^(y+1))<=h):(W (z3 g (1/(C:Y)) (ze c)) (2^o)).iP:=by
 let l:=zs (h/T);let i:=2*(2*D+2*D*(2*b+3)+4);let R:=z3 g (1/(C:Y)) (ze c);have w:=yr g (1/(C:Y)) c
 by_contra M;have x:∃ r:ℕ,¬(W R (2^r)).iP:=⟨o,M⟩;let p:=find x;have K:¬(W R (2^p)).iP:=find_spec x
 have Q:1<=p:=by by_contra h0';have h:p=0:=(by omega);rw[h,pow_zero] at K;exact K (w0 w.1 O)
 let r:=p-1;have a6:(W R (2^r)).iP:=not_not.mp (find_min x (Nat.sub_lt Q zero_lt_one))
 have a7:¬(W (W R (2^r)) 2).iP:=by rwa[w9 R w.1 (2^r) 2,show 2*2^r=2^p by rw[show p=r+1 by omega,pow_succ,mul_comm]]
 have S:r< o:=lt_of_lt_of_le (by omega:r< p) (find_min' x M);let u:=r+y+1
 have aj:u+i+2*b+2<=l:=by
  have q:2^(u+i+2*b+3)*T<=2^o*(4*C*T*2^(i+2*b+4)*2^(y+1)):=by rw[show u+i+2*b+3=r+(y+1)+(i+2*b+3) by omega,pow_add,pow_add];have:=zr S.le;have:=zr (by omega:i+2*b+3<=i+2*b+4);have:2^r*2^(y+1)*2^(i+2*b+3)*T<=2^o*2^(y+1)*2^(i+2*b+4)*T:=(by gcongr);have:=zu (2^o*2^(y+1)*2^(i+2*b+4)*T) (by omega:1<=4*C);linarith
  have:=le_log_of_pow_le (by omega:1< 2) ((le_div_iff_mul_le a1).mpr (q.trans a5));dsimp[l,zs];omega
 let u':=u+b+2;let e:=l-u+b
 have a8:(2:Y)^(((n:Y)-1/2)*((e-2*b-2:ℕ):Y))*#(F (2^u') A)<=#(F (2^l) A):=by
  have q:=x8 (f:=λ z=>(#(F (2^z) A):Y)) (by positivity) (a:=u') (e-2*b-2) λ k hk=>(N (u'+k) (mem_Ico.mpr ⟨by omega,by omega⟩)).le
  rwa[show u'+(e-2*b-2)=l by omega,<-rpow_natCast,<-rpow_mul (by norm_num)] at q
 have a9:F (2^l) A⊆(W R (2^(e+r))).tF:=by
  have hs:∀ m,∀ z∈F m A,∃ v:ZV d,g.eval v=z/\ ∀ j,|v j| *(2^(y+1):ℤ)<=(m:ℤ)*g.hi j:=λ m=>by
   induction m with | zero=>intro z B;simp only[F,iSm,mem_singleton] at B;subst B;exact ⟨0,by simp[eval,c.1],λ _=>by simp⟩ | succ m ih=>
    intro z B;rcases y8 B with ⟨z1,ac,a,ha,rfl⟩;obtain⟨v1,ad,ae⟩:=ih z1 ac;obtain⟨na,af,ag⟩:=a4 a ha;refine ⟨v1+na,by have:=map_add (zq g c.1) v1 na;simpa[zq,ad,af] using this,λ j=>?_⟩;have:=y7 (abs_add_le (v1 j) (na j)) (by positivity:(0:ℤ)<=2^(y+1));have:=ae j;have:=ag j;push_cast;simp only[Pi.add_apply];nlinarith
  intro z B;obtain⟨v,hv,hb⟩:=hs (2^l) z B;refine zh ⟨v,zc λ j=>?_,by simpa[eval,W,nS,R,z3,rS,c.1] using hv⟩
  have U:((2^l:ℕ):ℤ)*(2*C)<=((2^(e+r):ℕ):ℤ)*2^(y+1):=by exact_mod_cast ((zu _ a2).trans_eq (by rw[<-pow_add,show l+b=e+r+(y+1) by omega,pow_add]))
  have q:=(hb j).trans (ye (J j).2.le (z7 _));have h2:=y7 U (by have:=(J j).1;dsimp[R] at*;omega:(0:ℤ)<=R.hi j);have L:|v j| <=((2^(e+r):ℕ):ℤ)*R.hi j:=(by have:(0:ℤ)< 2^(y+1):=(by positivity);change |v j| *(2^(y+1):ℤ)<=((2^l:ℕ):ℤ)*(2*(C:ℤ)*R.hi j) at q;nlinarith)
  dsimp[cB,W,nS];rw[w.2 j];push_cast at L ⊢;rw[mul_neg];exact abs_le.mp L
 have I:=w7 (W R (2^r)) (t:=2) (k:=2^e) (y1 _) a7
 rw[w9 R w.1 (2^r) (2^e),<-pow_add,<-cEV a6] at I
 have X:=wa c h0 a0 P (m:=2^u') (by have:=div_mul_le_self (2^r) C;have:=zr (Nat.le_add_right r b);have:=zr (Nat.le_add_left b r);have h2:2^r+C<=2^(r+b+1):=(by rw[pow_succ];omega);have h3:=(y2 (2^(y+1)) ((show (2^r/C+1)*C<=2^r+C by rw[Nat.add_mul,one_mul];omega).trans h2)).trans ((pow_add 2 _ _).symm.trans_le (zr (by omega:r+b+1+(y+1)<=u')));nlinarith)
 have aa:(#(F (2^l) A):Y)<=((2*d*(2^e)^(d-1):ℕ):Y)*#(F (2^u') A):=by exact_mod_cast (z6 a9).trans (I.trans (zu _ X))
 have hc:(2:Y)^(((n:Y)-1/2)*((e-2*b-2:ℕ):Y))<=(2:Y)^((2*D+e*(d-1):ℕ):Y):=by
  have q:=le_of_mul_le_mul_right (a8.trans aa) (zo (yy h0 _));have ak:((2*d:ℕ):Y)<=(2:Y)^(2*D):=(by exact_mod_cast (zu 2 (E.trans G)).trans lt_two_pow_self.le)
  calc _<=((2*d:ℕ):Y)*(2:Y)^(e*(d-1)):=by simpa[cast_mul,<-pow_mul] using q
   _<=(2:Y)^(2*D)*(2:Y)^(e*(d-1)):=by gcongr
   _=_:=by rw[<-pow_add,<-rpow_natCast]
 have s:((n:Y)-1/2)*((e-2*b-2:ℕ):Y)<=((2*D+e*(d-1):ℕ):Y):=le_of_not_gt λ ah=>by linarith[rpow_lt_rpow_of_exponent_lt (by norm_num:(1:Y)< 2) ah,hc]
 rw[cast_sub (by omega),cast_sub (by omega)] at s;push_cast at s
 have ab:=za (by rw[cast_sub a3];have:=Z E;push_cast;linarith:((d-1:ℕ):Y)<=(n:Y)-1) (z7 e)
 nlinarith only[s,ab,Z G,Z (show i<=e by omega),show (i:Y)=4*D+4*D*(2*b+3)+8 by dsimp[i];push_cast;ring]
lemma wb (d:ℕ) (g:1<=d) (A:V ℤ):∃ P:GAP ℤ d,P.iC/\ A⊆P.tF/\ ∀ n:ℕ,A⊆zi n->P.vol<=2*n+1:=by
 let M:=A.sup Int.natAbs;let b:Fin d:=⟨0,by omega⟩;let P:GAP ℤ d:=⟨0,λ i=>if i=b then 1 else 0,λ i=>if i=b then -(M:ℤ) else 0,λ i=>if i=b then M else 0,λ i=>by split_ifs <;> omega⟩
 refine ⟨P,⟨rfl,λ i=>by dsimp[P];split_ifs <;> omega⟩,λ a c=>zh ⟨λ i=>if i=b then a else 0,zc λ i=>by dsimp[cB,P];split_ifs;exact abs_le.mp (by rw[Int.abs_eq_natAbs];exact_mod_cast le_sup (f:=Int.natAbs) c);exact ⟨le_rfl,le_rfl⟩,by simp only[eval,P,zero_add];rw[sum_eq_single_of_mem b (mem_univ b) λ i _ hi=>by simp[hi]];simp⟩,λ n e=>?_⟩
 have j:M<=n:=Finset.sup_le λ a c=>by have:=mem_Icc.mp (e c);omega
 have:P.vol=2*M+1:=(by unfold GAP.vol cB ZB.vol;rw[prod_eq_single_of_mem b (mem_univ b) λ i _ hi=>by dsimp[ZB.width,P];rw[if_neg hi];omega];dsimp[ZB.width,P];omega);omega
noncomputable def z9 (d:ℕ) (A:V ℤ):ℕ:=sInf {v|∃ P:GAP ℤ d,P.iC/\ A⊆P.tF/\ P.vol=v}
lemma yj {d:ℕ} (b:1<=d) (A:V ℤ):∃ P:GAP ℤ d,P.iC/\ A⊆P.tF/\ P.vol=z9 d A:=by obtain⟨a,c,e,_⟩:=wb d b A;exact Nat.sInf_mem (s:={v|∃ P:GAP ℤ d,P.iC/\ A⊆P.tF/\ P.vol=v}) ⟨a.vol,a,c,e,rfl⟩
lemma x9 {d:ℕ} {A:V ℤ} {P:GAP ℤ d} (hc:P.iC) (a:A⊆P.tF):z9 d A<=P.vol:=Nat.sInf_le ⟨P,hc,a,rfl⟩
lemma wc {d:ℕ} {A B:V ℤ} (a:1<=d) (h:A⊆B):z9 d A<=z9 d B:=by obtain⟨P,hc,b,c⟩:=yj a B;rw[<-c];exact x9 hc (h.trans b)
lemma xm {d:ℕ} (a:1<=d) (A:V ℤ):#A<=z9 d A:=by obtain⟨P,_,b,c⟩:=yj a A;rw[<-c];exact (z6 b).trans P.cLV
noncomputable def zn (d:ℕ) (a:1<=d) (A:V ℤ):GAP ℤ d:=choose (yj a A)
lemma yk {d:ℕ} (a:1<=d) (A:V ℤ):(zn d a A).iC:=(choose_spec (yj a A)).1
lemma yl {d:ℕ} (a:1<=d) (A:V ℤ):A⊆(zn d a A).tF:=(choose_spec (yj a A)).2.1
lemma ym {d:ℕ} (a:1<=d) (A:V ℤ):(zn d a A).vol=z9 d A:=(choose_spec (yj a A)).2.2
lemma xn {d h:ℕ} {A:V ℤ} (a:1<=d) (b:1<=h):#(F h A)<=h^d*z9 d A:=by rw[<-ym a A];exact (z6 (by rw[<-yh];exact iSM (yl a A) h)).trans (((W (zn d a A) h).cLV).trans (x7 _ b))
lemma we {d:ℕ} {P:GAP G1 d} (hS:P.iS) (j:Fin d):(P.width j:Y)=2*(P.hi j:Y)+1:=by
 dsimp[GAP.width,cB,ZB.width];rw[hS.2 j];have a:=(ze hS).2 j|>.2;exact_mod_cast (by rw[toNat_of_nonneg (by omega)];omega:((P.hi j - -P.hi j+1).toNat:ℤ)=2*P.hi j+1)
lemma ws {T J y k:ℕ} {K E:Y} {A:V ℤ} {G:GAP ℤ k}
 (au:K< T) (a0:1<=E) (N:E<=K) (X:0∈A) (b7:2<=#A) (b8:T<=y)
 (ab:G.iSP 2) (a1:F (2^(y+1)) A⊆G.tF)
 (ac:(G.vol:Y)<=E*#(F (2^(y+1)) A)) (ad:E⁻¹*G.vol<=∏ i:Fin k,if (i:ℕ)< J then (G.width i:Y) else 1):
 ∃ (d:ℕ) (_:1<=d) (_:d<=J) (c:GAP ℤ d) (o:ℤ->ZV d),
  c.iC/\ c.iP/\ (∀ j,T<=c.width j)/\ (∀ a∈A,c.eval (o a)=a)/\ o 0=0 /\
  (∀ a∈A,∀ j,c.lo j<=(2^(y+1):ℤ)*o a j/\ (2^(y+1):ℤ)*o a j<=c.hi j) /\
  F (2^(y+1)) (A.image o)⊆z5 c/\ (F (2^(y+1)) (A.image o)).image c.eval=F (2^(y+1)) A /\
  K⁻¹*c.vol<=#(F (2^(y+1)) (A.image o)):=by
 have ae:=zero_lt_one.trans_le (a0.trans N);have a2:=zero_lt_one.trans_le a0
 obtain⟨b,l,ar,as,a9,aa⟩:=wp G (a1 (yb X _)) (by simpa[iSP] using ab)
 have O:b.iP:=yp aa (λ w hw=>zc λ i=>by have:=zb hw i;have:=l.2 i;dsimp[cB,W,nS] at*;constructor <;> linarith) rfl l.1 (by dsimp[W,nS];rw[l.1,mul_zero])
 have s:F (2^(y+1)) A⊆b.tF:=by rwa[ar]
 have an:∀ i:Fin k,J<=(i:ℕ)->(b.width i:Y)<=K:=λ i hi=>by
  let P1:=∏ j:Fin k,if (j:ℕ)< J then (b.width j:Y) else 1;let P2:=∏ j:Fin k,if (j:ℕ)< J then 1 else (b.width j:Y)
  have av:(b.vol:Y)=P1*P2:=(by dsimp[P1,P2];rw[<-prod_mul_distrib];simp only[GAP.vol,GAP.width,ZB.vol,cast_prod];exact prod_congr rfl λ j _=>by split_ifs <;> ring)
  have B:E⁻¹*b.vol<=P1:=(by rw[a9];convert ad using 2 with j;rw[as j])
  have P:=za (le_of_mul_le_mul_right (by have:=zj B (prod_nonneg λ j _=>by split_ifs <;> positivity:0<=P2);linarith only[this,av]:E⁻¹*P2*b.vol<=1*b.vol) (zo b.vP)) a2.le
  rw[<-mul_assoc,mul_inv_cancel₀ a2.ne',one_mul,mul_one] at P
  exact ((by dsimp[P2];rw[<-mul_prod_erase univ _ (mem_univ i),if_neg (not_lt.mpr hi)];exact le_mul_of_one_le_right (z7 _) (one_le_prod λ j _=>by split_ifs;exact le_rfl;exact zk (b.cB.wP j)):(b.width i:Y)<=P2).trans (P.trans N))
 let D:=univ.filter λ i:Fin k=>(i:ℕ)< J/\ (2^(y+1):ℤ)<=max (-b.lo i) (b.hi i)
 have L:∀ x∈A,(∀ i,i∉D->z4 b x i=0)/\ (∀ i,b.lo i<=(2^(y+1):ℤ)*z4 b x i/\ (2^(y+1):ℤ)*z4 b x i<=b.hi i):=λ x C=>by
  let r:=2^(y+1);let Q (t:ℕ):=z4 b ((t:ℤ)•x);have I:∀ t ≤ r,Q t∈z5 b:=λ t ht=>ys b (s (xl X C ht));have a3:∀ t ≤ r,b.eval (Q t)=(t:ℤ)•x:=λ t ht=>y3 b (s (xl X C ht))
  have af:∀ t ≤ r,Q t=(t:ℤ)•Q 1:=λ t=>by
   induction t using strong_induction_on with | h t ih=>
    intro M;match t with
    | 0=>simpa[Q] using yt l O
    | 1=>simp
    | m+2=>
      have p:∀ u v,u∈z5 b->v∈z5 b->u+v∈z5 (W b 2):=λ u v hu q=>zc λ i=>by have:=zb hu i;have:=zb q i;dsimp[cB,W,nS] at*;constructor <;> linarith
      have ag:∀ u v,(W b 2).eval (u+v)=b.eval u+b.eval v:=λ u v=>by simp only[eval,W,nS,l.1,mul_zero,zero_add,Pi.add_apply,smul_eq_mul,add_mul,sum_add_distrib]
      have B:=aa (p _ _ (I (m+1) (by omega)) (I (m+1) (by omega))) (p _ _ (I m (by omega)) (I (m+2) M)) (by rw[ag,ag,a3 (m+1) (by omega),a3 m (by omega),a3 (m+2) M,<-add_smul,<-add_smul,show (m:ℤ)+((m+2:ℕ):ℤ)=((m+1:ℕ):ℤ)+((m+1:ℕ):ℤ) by push_cast;ring])
      rw[ih (m+1) (by omega) (by omega),ih m (by omega) (by omega)] at B;ext i;have P:=congrFun B i;simp only[Pi.add_apply,Pi.smul_apply,smul_eq_mul] at P ⊢;push_cast at P ⊢;linarith
  have ah:Q 1=z4 b x:=(by simp[Q])
  have ai:∀ i,b.lo i<=(2^(y+1):ℤ)*z4 b x i/\ (2^(y+1):ℤ)*z4 b x i<=b.hi i:=λ i=>by have:=zb (I r le_rfl) i;rw[af r le_rfl,ah] at this;simpa[cB,r,Pi.smul_apply,smul_eq_mul] using this
  refine ⟨λ i hi=>?_,ai⟩;simp only[D,mem_filter,mem_univ,true_and,not_and] at hi;by_contra al
  by_cases am:(i:ℕ)< J
  . have a4:=not_le.mp (hi am);have aw:=ai i;have ax:(0:ℤ)< 2^(y+1):=(by positivity);have ay:=one_le_abs al
    rcases abs_cases (z4 b x i) with ⟨h,_⟩|⟨h,_⟩ <;> nlinarith only[h,ay,ax,aw,a4,zp (-b.lo i) (b.hi i),zm (-b.lo i) (b.hi i)]
  . have az:(range (r+1)).image (λ t:ℕ=>(t:ℤ)*z4 b x i)⊆Icc (b.lo i) (b.hi i):=λ z hz=>by rcases z0 hz with ⟨t,ht,rfl⟩;have M:=Nat.lt_succ_iff.mp (mem_range.mp ht);have:=zb (I t M) i;rw[af t M,ah] at this;exact mem_Icc.mpr (by simpa[cB,Pi.smul_apply,smul_eq_mul] using this)
    have b0:r+1<=b.width i:=by have B:=z6 az;rw[card_image_of_injOn (λ _ _ _ _ b5=>cast_injective (mul_right_cancel₀ al b5)),card_range,card_Icc] at B;dsimp[GAP.width,cB,ZB.width] at*;have:=b.hle i;omega
    linarith only[zw ((show T< r+1 by have:=lt_two_pow_self (n:=y+1);dsimp[r];omega).trans_le b0),au,an i (not_lt.mp am)]
 let d:=#D;let e:Fin d↪Fin k:=(D.orderEmbOfFin rfl).toEmbedding;have aj:∀ j,e j∈D:=λ j=>D.orderEmbOfFin_mem rfl j
 have hdd':d<=J:=((card_image_of_injOn (f:=λ i:Fin k=>(i:ℕ)) (λ _ _ _ _ h=>Fin.ext h)).symm.trans_le (z6 λ m hm=>by rcases z0 hm with ⟨i,hi,rfl⟩;exact mem_range.mpr (zg hi).2.1)).trans_eq (card_range J)
 have b1:1<=d:=by
  rcases card_pos.mp (by rw[card_erase_of_mem X];omega:0< #(A.erase 0)) with ⟨x,C⟩;have ak:=(mem_erase.mp C).2
  have b2:z4 b x≠0:=λ hz=>(mem_erase.mp C).1 (by have:=y3 b (s (xf X _ ak));rw[hz] at this;simpa[eval,l.1] using this.symm)
  have ⟨i,hi⟩:∃ i,z4 b x i≠0:=(by by_contra p;push Not at p;exact b2 (funext p));exact Nonempty.card_pos ⟨i,by by_contra hn;exact hi ((L x ak).1 i hn)⟩
 let c:=yi b e;have R:c.iC:=⟨l.1,λ i=>l.2 (e i)⟩
 have a5:c.iP:=λ u hu v q b6=>by
  let U:ZV d->ZV k:=λ n j=>if h:∃ i,e i=j then n (choose h) else 0
  have hm:∀ n∈z5 c,U n∈z5 b:=λ n hn=>zc λ j=>by by_cases h:∃ i,e i=j;simp only[U,dif_pos h];simpa[c,cB,yi,choose_spec h] using zb hn (choose h);simp only[U,dif_neg h];exact l.2 j
  have hq:=O (hm u hu) (hm v q) (by rw[<-w1 b e u,<-w1 b e v,b6]);ext i;have:=congrFun hq (e i);have C:∃ i',e i'=e i:=⟨i,rfl⟩;simp only[U,dif_pos C] at this;rwa[e.injective (choose_spec C)] at this
 have ao:∀ j,T<=c.width j:=λ j=>by have a4:=(zg (aj j)).2.2;have hc:=R.2 j;dsimp[c,yi,GAP.width,cB,ZB.width] at hc ⊢;have b9:((2^(y+1):ℕ):ℤ)<=b.hi (e j)-b.lo (e j):=(by push_cast;rcases le_max_iff.mp a4 with B|P <;> omega);have:=lt_two_pow_self (n:=y+1);omega
 let o a j:=z4 b a (e j)
 have S:∀ a∈A,c.eval (o a)=a:=λ a p=>by
  have b3:univ.image e=D:=(by ext i;simp only[mem_image,mem_univ,true_and];exact ⟨λ⟨j,hj⟩=>hj▸aj j,λ hi=>by have h:i∈(D:Set _):=hi;rw[<-Finset.range_orderEmbOfFin D rfl] at h;exact h⟩)
  conv_rhs=>rw[<-y3 b (s (xf X _ p))]
  change b.base+∑ j,z4 b a (e j)•b.step (e j)=b.base+∑ i,z4 b a i•b.step i;rw[l.1,zero_add,zero_add,<-sum_image (f:=λ i=>z4 b a i•b.step i) (g:=e) (λ _ _ _ _ h=>e.injective h),b3];exact sum_subset (subset_univ D) λ i _ hi=>by rw[(L a p).1 i hi,zero_smul]
 have ap:o 0=0:=funext λ j=>by dsimp[o];rw[yt l O];rfl
 let Ab:=F (2^(y+1)) (A.image o);let a6:=zq c R.1
 have a7:Ab⊆z5 c:=by
  have b4:∀ t ≤ 2^(y+1),∀ v∈F t (A.image o),∀ j,(t:ℤ)*c.lo j<=(2^(y+1):ℤ)*v j/\ (2^(y+1):ℤ)*v j<=(t:ℤ)*c.hi j:=λ t=>by
   induction t with | zero=>intro _ v q j;simp only[F,iSm,mem_singleton] at q;subst q;simp | succ t ih=>intro ht v q j;rcases y8 q with ⟨u,hu,w,hw,rfl⟩;rcases z0 hw with ⟨a,p,rfl⟩;have B:=ih (by omega) u hu j;have P:=(L a p).2 (e j);dsimp[c,yi,o] at B ⊢;constructor <;> linarith
  intro v q;exact zc λ j=>by have:=b4 (2^(y+1)) le_rfl v q j;dsimp[cB];push_cast at this;have:(0:ℤ)< 2^(y+1):=(by positivity);constructor <;> nlinarith
 have a8:Ab.image c.eval=F (2^(y+1)) A:=by change Ab.image a6=_;dsimp[Ab];rw[x4 a6];congr 1;ext x;simp only[mem_image];exact ⟨by rintro⟨_,⟨a,p,rfl⟩,rfl⟩;change c.eval (o a)∈A;rwa[S a p],λ C=>⟨o x,⟨x,C,rfl⟩,S x C⟩⟩
 have aq:K⁻¹*c.vol<=#Ab:=by
  rw[show #Ab=#(F (2^(y+1)) A) by rw[<-a8];exact (card_image_of_injOn (a5.mono (by exact_mod_cast a7))).symm]
  have q:c.vol<=b.vol:=(by change ∏ i:Fin d,c.width i<=∏ i:Fin k,b.width i;rw[show ∏ i:Fin d,c.width i=∏ j∈univ.image e,b.width j by rw[prod_image λ _ _ _ _ h=>e.injective h];rfl,<-union_sdiff_of_subset (subset_univ (univ.image e)),prod_union disjoint_sdiff];exact le_mul_of_pos_right _ (prod_pos λ j _=>b.cB.wP j))
  have B:=za ((Z q).trans (show (b.vol:Y)<=K*#(F (2^(y+1)) A) by rw[a9];exact ac.trans (zj N))) (inv_nonneg.mpr ae.le);rwa[<-mul_assoc,inv_mul_cancel₀ ae.ne',one_mul] at B
 exact ⟨d,b1,hdd',c,o,R,a5,ao,S,ap,λ a p j=>(L a p).2 (e j),a7,a8,aq⟩
lemma wt {D p C T G h d' y d:ℕ} {A:V ℤ} {l:GAP ℤ d} {f:ℤ->ZV d} {c:GAP (ZV d) d} {xN:ZV d}
 (M:1<=C) (a6:p<=C) (as:1000*C+1<=T) (au:2*C<=2^G)
 (h0:0∈A) (av:1<=d) (af:d<=d') (ag:d'<=D) (aw:T<=y) (ax:y< zs (h/T)) (ay:T<=h)
 (ah:∀ z∈Ico T (zs (h/T)),(2:Y)^((d':Y)-1/2)*#(F (2^z) A)< #(F (2^(z+1)) A))
 (N:l.iC) (ai:l.iP) (O:∀ a∈A,l.eval (f a)=a) (aj:f 0=0)
 (ak:∀ a∈A,∀ j,l.lo j<=(2^(y+1):ℤ)*f a j/\ (2^(y+1):ℤ)*f a j<=l.hi j)
 (al:(F (2^(y+1)) (A.image f)).image l.eval=F (2^(y+1)) A)
 (e:c.iS) (K:∀ i,c.step i∈zf (F (2^(y+1)) (A.image f):Set (ZV d)))
 (g:∀ x∈zf (F (2^(y+1)) (A.image f):Set (ZV d)),∃! n:ZV d,∑ i,n i•c.step i=x)
 (a7:∀ x∈z5 l,x∈zf (F (2^(y+1)) (A.image f):Set (ZV d))->x∈c.tF)
 (S:∃ t:ZV d,∀ x∈c.tF,∀ i,(C:ℤ)*l.lo i<=(x-t) i/\ (x-t) i<=(C:ℤ)*l.hi i)
 (az:c.tF.image (·+xN)⊆F p (F (2^(y+1)) (A.image f))):
 (1/(6*(C:Y)*(4*C*T*2^(2*(2*D+2*D*(2*G+3)+4)+2*G+4):ℕ)))^d*(h:Y)^d*z9 d A<=#(F h A):=by
 let C':=4*C*T*2^(2*(2*D+2*D*(2*G+3)+4)+2*G+4);have a9:1<=T:=(by omega);let Ab:=F (2^(y+1)) (A.image f);let k:=zq l N.1
 have b0:1000*C*2^(y+1)< h:=(Nat.mul_lt_mul_of_pos_right (by omega:1000*C< T) (by positivity)).trans_le ((zu T ((zr ax).trans (pow_log_le_self 2 (div_pos ay a9).ne'))).trans (mul_div_le h T))
 have a8:∀ n:ZV d,∑ j,n j•c.step j=0->n=0:=λ n hn=>by obtain⟨_,_,E⟩:=g 0 (zero_mem _);rw[E n hn,<-E 0 (by simp)]
 have U:=xy (zh ⟨0,h0,aj⟩) (y1 (y+1))
 let b:GAP ℤ d:=⟨0,λ j=>l.eval (c.step j),c.lo,c.hi,c.hle⟩;have q:b.iS:=⟨rfl,e.2⟩;have I:=ze q
 have J:∀ n,b.eval n=k (c.eval n):=λ n=>by simp only[eval,b,e.1,zero_add,map_sum,map_zsmul];rfl
 have X:∀ a∈A,∃ n:ZV d,∑ j,n j•c.step j=f a/\ ∀ j,c.lo j<=(2^(y+1):ℤ)*n j/\ (2^(y+1):ℤ)*n j<=c.hi j:=λ a s=>by
  have a0:f a∈zf (Ab:Set (ZV d)):=(by rw[U];exact subset_closure (zd f s));obtain⟨n,o,_⟩:=g (f a) a0
  rcases z0 (a7 _ (zc λ j=>by dsimp[cB];simpa[Pi.smul_apply,smul_eq_mul] using ak a s j) (zsmul_mem a0 (2^(y+1):ℤ))) with ⟨m,ac,ad⟩
  simp only[eval,e.1,zero_add] at ad;obtain⟨_,_,E⟩:=g _ (zsmul_mem a0 (2^(y+1):ℤ))
  have am:m=(2^(y+1):ℤ)•n:=E m ad|>.trans (E ((2^(y+1):ℤ)•n) (by simp[<-o,smul_sum,mul_smul])).symm
  rw[am] at ac;exact ⟨n,o,λ j=>by simpa[cB] using zb ac j⟩
 have a1:∀ j,(2^(y+1):ℤ)<=b.hi j:=λ j=>by
  rw[U] at K g;obtain⟨_,hx,n,o,ae⟩:=w5 K g j;rcases z0 hx with ⟨a,s,rfl⟩
  obtain⟨n',ar,B⟩:=X a s;obtain⟨_,_,E⟩:=g (f a) (subset_closure (zd f s));rw[E n o,<-E n' ar] at ae
  have h1:=B j;have v:=e.2 j;have h3:=one_le_abs ae;have L:(0:ℤ)< 2^(y+1):=(by positivity)
  dsimp[b];rcases abs_cases (n' j) with ⟨h,_⟩|⟨h,_⟩ <;> nlinarith only[h,h1,v,h3,L]
 have a2:∃ x0:ℤ,b.tF.image (·+x0)⊆F (C*2^(y+1)) A:=⟨l.eval xN,λ z hz=>by
  rcases z0 hz with ⟨_,b8,rfl⟩;rcases z0 b8 with ⟨n,hn,rfl⟩
  have hi:k (c.eval n+xN)∈F p (F (2^(y+1)) A):=(by rw[<-al];change _∈F p (Ab.image k);rw[<-x4 k];exact zd _ (az (zd _ (zd _ hn))))
  rw[J];change k (c.eval n)+k xN∈_;rw[<-map_add k];rw[<-xg A (2^(y+1)) p] at hi;exact yg h0 (y2 _ a6) hi⟩
 let R:=z3 b (1/(C:Y)) I;have a3:=yr b (1/(C:Y)) q
 have bb:4<=C':=(by dsimp[C'];have:=one_le_pow (2*(2*D+2*D*(2*G+3)+4)+2*G+4) 2 (by omega);have:4<=4*C*T:=(by nlinarith);nlinarith)
 have w:=zl C;have an:=zl C'
 have aa:∀ j,2<=R.hi j/\ b.hi j< 2*(C:ℤ)*R.hi j:=λ j=>by
  have h1:=(show (10*C:ℤ)<=2^(y+1) by have:=lt_two_pow_self (n:=y+1);exact_mod_cast (by omega:10*C<=2^(y+1))).trans (a1 j)
  have hf:(b.hi j:Y)/C-1< R.hi j:=(by dsimp[R,z3,rS];linarith[sub_one_lt_floor (1/(C:Y)*b.hi j),show 1/(C:Y)*b.hi j=(b.hi j:Y)/C by ring])
  have v:(2:Y)<=R.hi j:=(by linarith[(le_div_iff₀ w).mpr (by exact_mod_cast h1:(10:Y)*C<=b.hi j)])
  have hm:(b.hi j:Y)< 2*C*R.hi j:=(by have:=mul_lt_mul_of_pos_left hf w;field_simp[w.ne'] at this;nlinarith)
  exact ⟨by exact_mod_cast v,by exact_mod_cast hm⟩
 have a4:=w8 N ai e a8 M (w6 (Q:=l.cB) e S)
 let r:=zs (h/(C'*2^(y+1)))
 have b1:h<=2*C'*2^(y+1)*2^r:=by
  have b2:=Nat.mul_pos (by omega:0< C') (by positivity:0< 2^(y+1))
  have b3:=lt_pow_succ_log_self (by omega:1< 2) (h/(C'*2^(y+1)));have:=div_add_mod h (C'*2^(y+1));have:=mod_lt h b2
  have v:=(show h< (C'*2^(y+1))*(h/(C'*2^(y+1))+1) by nlinarith).le.trans (zu _ b3);rw[pow_succ 2 r] at v;linarith
 have a5:r≠0->2^r*(C'*2^(y+1))<=h:=λ u=>(le_div_iff_mul_le (Nat.mul_pos (by omega) (by positivity))).mp (pow_log_le_self 2 λ hq=>u (by dsimp[r];rw[hq];rfl))
 have b4:(W R (2^r)).iP:=by
  by_cases u:r=0;rw[u,pow_zero];exact w0 a3.1 a4
  exact wr q h0 M a9 au av af ag aw ah aa a4 a2 (λ a s=>by obtain⟨na,o,B⟩:=X a s;refine ⟨na,by rw[J,show c.eval na=f a by simp only[eval,e.1,zero_add,o]];exact O a s,λ j=>?_⟩;have v:=B j;rw[e.2 j] at v;have:=abs_le.mpr v;rwa[abs_mul,abs_of_pos (by positivity:(0:ℤ)< 2^(y+1)),mul_comm] at this) (a5 u)
 have ao:=wa q h0 M a2 (r:=r) (m:=h) (by have:=div_mul_le_self (2^r) C;have bc:2*(2^r*2^(y+1))<=h:=(by by_cases u:r=0;rw[u,pow_zero,one_mul];nlinarith;have:=a5 u;nlinarith);have:=y2 (2^(y+1)) (show (2^r/C+1)*C<=2^r+C by rw[Nat.add_mul,one_mul];omega);nlinarith)
 let P:=z3 b (1/(2^(y+1):Y)) I;have ab:=yr b (1/(2^(y+1):Y)) q;have b5:=ze ab
 have b6:A⊆P.tF:=λ a s=>by obtain⟨n,o,B⟩:=X a s;have L:(0:Y)< 2^(y+1):=(by positivity);exact zh ⟨n,zc λ j=>by dsimp[cB,P,z3,rS,b];rw[ceil_le,le_floor,one_div,inv_mul_le_iff₀ L,le_inv_mul_iff₀ L];exact ⟨by exact_mod_cast (B j).1,by exact_mod_cast (B j).2⟩,by rw[show P.eval n=b.eval n from rfl,J,show c.eval n=f a by simp only[eval,e.1,zero_add,o]];exact O a s⟩
 have ap:((1/(6*(C:Y)*C'))^d)*(h:Y)^d*P.vol<=((W R (2^r)).vol:Y):=by
  change ((1/(6*(C:Y)*C'))^d)*(h:Y)^d*((∏ j:Fin d,P.width j:ℕ):Y)<=((∏ j:Fin d,(W R (2^r)).width j:ℕ):Y)
  rw[cast_prod,cast_prod,show ((1/(6*(C:Y)*C'))^d)*(h:Y)^d*∏ j:Fin d,(P.width j:Y)=∏ j:Fin d,((h:Y)/(6*(C:Y)*C')*P.width j) by rw[prod_mul_distrib,prod_const,card_univ,Fintype.card_fin,<-mul_pow,show (1/(6*(C:Y)*C'))*(h:Y)=(h:Y)/(6*(C:Y)*C') by ring]]
  have aq:(W R (2^r)).iS:=⟨by dsimp[W,nS];rw[a3.1,mul_zero],λ j=>by dsimp[W,nS];rw[a3.2 j];ring⟩
  have bd:(h:Y)/(2*(C':Y)*2^(y+1))<=((2^r:ℕ):Y):=(div_le_iff₀ (by positivity)).mpr (by have:=Z b1;push_cast at this ⊢;linarith)
  refine prod_le_prod (λ _ _=>by positivity) λ j _=>?_
  have b9:(1:Y)<=P.hi j:=(by dsimp[P,z3,rS];exact_mod_cast (le_floor.mpr (by rw[Int.cast_one,one_div,le_inv_mul_iff₀ (by positivity),mul_one];exact_mod_cast a1 j):(1:ℤ)<=⌊1/(2^(y+1):Y)*b.hi j⌋))
  have ba:(P.hi j:Y)<=(b.hi j:Y)/2^(y+1):=(by simpa[P,z3,rS,one_div,div_eq_inv_mul] using floor_le (1/(2^(y+1):Y)*b.hi j))
  have bf:(P.width j:Y)<=3*(b.hi j:Y)/2^(y+1):=(by rw[we ab j];change 2*(P.hi j:Y)+1<=_;linarith[show 3*(b.hi j:Y)/2^(y+1)=3*((b.hi j:Y)/2^(y+1)) by ring])
  have b7:((2^r:ℕ):Y)*(b.hi j:Y)/C<=((W R (2^r)).width j:Y):=(by rw[we aq j];dsimp[W,nS];rw[show ((2^r*R.hi j:ℤ):Y)=((2^r:ℕ):Y)*R.hi j by push_cast;rfl];have v:=za (by exact_mod_cast (aa j).2.le:(b.hi j:Y)<=2*C*R.hi j) (z7 (2^r));rw[div_le_iff₀ w];nlinarith only[v,w])
  have be:=yx ((I.2 j).2)
  calc (h:Y)/(6*(C:Y)*C')*P.width j<=(h:Y)/(6*(C:Y)*C')*(3*(b.hi j:Y)/2^(y+1)):=by gcongr
   _=(h:Y)/(2*(C':Y)*2^(y+1))*((b.hi j:Y)/C):=by field_simp[w.ne',an.ne'];ring
   _<=((2^r:ℕ):Y)*((b.hi j:Y)/C):=by gcongr
   _<=((W R (2^r)).width j:Y):=by rw[<-mul_div_assoc];exact b7
 exact (za (Z (x9 b5 b6))).trans (ap.trans (by rw[<-cEV b4];exact Z ao))
lemma wu (hNR:LNH) (hBilu:LBH) (m:Y) (aw:1< m):
 ∃ (j:Y) (o:ℕ),0< j/\ j<=1/\ 2<=o /\
  ∀ (n h:ℕ) (A:V ℤ),o<=n->A⊆zi n->0∈A->2<=#A->(n:Y)<=(h:Y)^m->
   ∃ (d:ℕ) (_:1<=d),d<=⌊m+2⌋₊/\ j*(h:Y)^d*z9 d A<=#(F h A):=by
 let D:=⌊m+2⌋₊;have bf:3<=D:=Nat.le_floor (by norm_num;linarith);have ax:m+1< D:=(by linarith[lt_floor_add_one (m+2)])
 choose Cb Db a6 av using λ e (_:e<=D)=>hBilu 2 e (by omega) (1/2) (by norm_num)
 let K:Y:=(range (D+1)).sup' ⟨0,mem_range.mpr (Nat.succ_pos D)⟩ λ e=>if h:e<=D then Cb e h else 1
 have a0:∀ e (s:e<=D),Cb e s<=K:=λ e s=>by simpa[dif_pos s] using le_sup' (λ x=>if h:x<=D then Cb x h else 1) (mem_range.mpr (Nat.lt_succ_of_le s))
 have a1:1<=K:=(a6 0 (Nat.zero_le D)).trans (a0 0 (Nat.zero_le D));have ay:=zero_lt_one.trans_le a1
 choose a7 ba bb bc _ M X using λ d (hd:1<=d) (_:d<=D)=>hNR d hd K⁻¹ (inv_pos.mpr ay) (inv_le_one_of_one_le₀ a1)
 obtain⟨a3,ah⟩:=yc D a7;obtain⟨q,P,ai⟩:=xt (by omega:1<=D) ba M;obtain⟨r,aj⟩:=yc D bb;obtain⟨a4,ak⟩:=yc D bc
 let b:=max r (⌈1/q⌉₊+1);let C:=max 1 (max b a3);let T:=max (1000*C+1) (max (⌈K⌉₊+1) a4)
 have ⟨hC1,hCℓ,hCκ⟩:1<=C/\ b<=C/\ a3<=C:=by simp only[C,le_max_iff,le_refl,true_or,or_true,and_self]
 have ⟨hT1000,hTK',hTW⟩:1000*C+1<=T/\ ⌈K⌉₊+1<=T/\ a4<=T:=by simp only[T,le_max_iff,le_refl,true_or,or_true,and_self]
 have a2:1<=T:=(by omega);have w:r<=b:=zp r (⌈1/q⌉₊+1);have az:K< T:=(le_ceil K).trans_lt (zw (by omega))
 let u:=xa (2*C)+1;have b0:2*C<=2^u:=(le_pow_clog (by omega) _).trans (zr (Nat.le_succ _))
 let C':=4*C*T*2^(2*(2*D+2*D*(2*u+3)+4)+2*u+4);have aa:C'=4*C*T*2^(2*(2*D+2*D*(2*u+3)+4)+2*u+4):=rfl
 have ab:1<=C':=Nat.mul_pos (Nat.mul_pos (by omega:0< 4*C) a2) (Nat.pow_pos (by omega:0< 2))
 obtain⟨Q,b6⟩:=eventually_atTop.mp ((eventually_ge_atTop (4*T*2^(T+2))).and (yo (a:=1/2) (c:=3*((2*T*2^T:ℕ):Y)^(D+1)) (by norm_num)))
 let o:=max 2 (⌈(Q:Y)^m⌉₊+1);have ac:2<=o:=zp 2 (⌈(Q:Y)^m⌉₊+1);have ad:(Q:Y)^m< o:=(le_ceil _).trans_lt (zw (by have:=zm 2 (⌈(Q:Y)^m⌉₊+1);omega))
 have z:1<=q*b:=yz P (by have:=zm r (⌈1/q⌉₊+1);omega)
 let j:Y:=min 1 ((1/(6*(C:Y)*C'))^D);have ae:0< j:=lt_min zero_lt_one (by positivity);have af:j<=1:=xq 1 ((1/(6*(C:Y)*C'))^D);have ag:j<=(1/(6*(C:Y)*C'))^D:=xr 1 ((1/(6*(C:Y)*C'))^D)
 clear_value K b C T u C' o j
 refine ⟨j,o,ae,af,ac,λ n h A hn hA N a8 a9=>?_⟩
 obtain⟨E,al⟩:=b6 h (xd aw (ad.trans_le (Z hn)) a9)
 obtain⟨e,y,be,l,a5,b7,bg,am⟩:=wq a2 ax hA N a8 a9 E al
 have b1:T<=h:=le_trans (le_mul_of_pos_left T (by omega:0< 4)) ((le_mul_of_pos_right _ (y1 _)).trans E)
 have B:F (2^y) A+F (2^y) A=F (2^(y+1)) A:=(by dsimp[F];rw[pow_succ,mul_two,iSA])
 obtain⟨k,_,bh,R,G,S,U⟩:=av e l (F (2^y) A) ⟨0,yb N _⟩ (by rw[B];rwa[show (e:Y)+1-1/2=e+1/2 by ring])
 obtain⟨d,g,I,Q0,c0,p,an,ao,ap,J,aq,ar,as,au⟩:=ws az (a6 e l) (a0 e l) N a8 a5 R (B▸G) (B▸S) U
 have f:=I.trans l
 obtain⟨L,_,hS,hm,hb,hc,⟨t,ht⟩,_,hs⟩:=X d g f Q0.cB (F (2^(y+1)) (A.image c0)) (λ i=>((ak d g f).trans hTW).trans (ao i)) ar (yb (zh ⟨0,N,J⟩) _) au
 obtain⟨x0,b8⟩:=hs b ((aj d g f).trans w)
 have b2:∃ t:ZV d,∀ x∈L.tF,∀ i,(C:ℤ)*Q0.lo i<=(x-t) i/\ (x-t) i<=(C:ℤ)*Q0.hi i:=⟨t,λ x hx i=>by have O:=ht x hx i;dsimp[cB] at O;simp only[Pi.sub_apply] at O ⊢;have h2:((a7 d g f:ℤ)<=C):=(by exact_mod_cast (ah d g f).trans hCκ);have b3:=(p.2 i).1;have b4:=(p.2 i).2;constructor <;> nlinarith only[O.1,O.2,h2,b3,b4]⟩
 have b5:L.tF.image (·+x0)⊆F b (F (2^(y+1)) (A.image c0)):=λ v hv=>b8 (by rcases z0 hv with ⟨_,b9,rfl⟩;rcases z0 b9 with ⟨n,hn,rfl⟩;exact zd _ (zh ⟨n,xj L (ze hS) (k:=1) (by simpa using z.trans (zj (ai d g f))) (mul_nonneg (M d g f).le (z7 b)) (by simpa[z5,mTF,cB,W,nS] using hn),by simp[eval,rS,hS.1]⟩))
 have bd:j<=(1/(6*(C:Y)*C'))^d:=ag.trans (pow_le_pow_of_le_one (by positivity) (div_le_one_of_le₀ (by have:=zk ab;have:=zk hC1;nlinarith only[this,‹(1:Y)<=C'›]) (by positivity)) f)
 exact ⟨d,g,f,(by gcongr:(j*(h:Y)^d*z9 d A)<=(1/(6*(C:Y)*C'))^d*(h:Y)^d*z9 d A).trans (aa▸wt hC1 hCℓ hT1000 b0 N g I l a5 b7 b1 am p an ap J aq as hS hm hb hc b2 b5)⟩
abbrev yu (a c b:Y) (e:ℕ) (f:0< b):Prop:=∀ (n h:ℕ) (A:V ℤ),e<=n->A⊆zi n->0∈A->2<=#A->(n:Y)<=(h:Y)^a->∃ (d:ℕ) (hd1:1<=d),d<=⌊1+a⌋₊/\ c*(h:Y)^d*z9 d A<=#(F h A)/\ (∀ j,2<=(zn d hd1 A).width j)/\ (zn d hd1 A).iP/\ (z3 (zn d hd1 A) (b*h) (yk hd1 A)).iP/\ (h<=n->∀ j,|(zn d hd1 A).step j| <=2*(n:ℤ)^2)
lemma wv (hNR:LNH) (hBilu:LBH) (m:Y) (P:1< m):∃ (f l:Y) (D:ℕ) (a5:0< l),0< f/\ f<=1/\ l<=1/\ 4<=D/\ yu m f l D a5:=by
 obtain⟨f,N0,r,a3,_,a4⟩:=wu hNR hBilu m P;let p:=⌊1+m⌋₊
 have a6:0< ((p+1:ℕ):Y)-(1+m):=(by have:=lt_floor_add_one (1+m);dsimp[p];push_cast;linarith)
 let l:=min 1 (f/(2*((p+1:ℕ):Y)));have E:0< l:=lt_min zero_lt_one (by positivity)
 obtain⟨H0,af⟩:=eventually_atTop.mp ((eventually_ge_atTop (max 2 (max (⌈2/f⌉₊+1) (⌈2/l⌉₊+1)))).and (yo (a:=((p+1:ℕ):Y)-(1+m)) (c:=3/f) a6))
 let D:=max 4 (max N0 (⌈(H0:Y)^m⌉₊+1));have T:(H0:Y)^m< D:=(le_ceil _).trans_lt (zw (by have:=(zm N0 (⌈(H0:Y)^m⌉₊+1)).trans (zm 4 _);omega))
 refine ⟨f,l,D,E,r,a3,xq _ _,zp _ _,λ n h A hn hA h0 aj L=>?_⟩
 obtain⟨K,aq⟩:=af h (xd P (T.trans_le (Z hn)) L)
 have y:1<=h:=(by have:=(zp _ _).trans K;omega)
 have U:(2:Y)<=f*h:=yz r (by have:=((zp (⌈2/f⌉₊+1) (⌈2/l⌉₊+1)).trans (zm 2 _)).trans K;omega)
 have an:(2:Y)<=l*h:=yz E (by have:=((zm (⌈2/f⌉₊+1) (⌈2/l⌉₊+1)).trans (zm 2 _)).trans K;omega)
 obtain⟨d,u,_,q⟩:=a4 n h A (((zp N0 _).trans (zm 4 _)).trans hn) hA h0 aj L
 have X:d<=p:=le_of_not_gt λ S=>by
  have B:=zl h;have G:=zk y
  have ao:f*(h:Y)^((p+1:ℕ):Y)<=#(F h A):=(by rw[rpow_natCast];exact (za (pow_le_pow_right₀ G S) r.le).trans ((le_mul_of_one_le_right (by positivity) (zk ((show 1<=#A by omega).trans (xm u A)))).trans q))
  have C:(#(F h A):Y)<=3*(h:Y)^(1+m):=(by have h1:=Z (xi hA h);have h2:(h:Y)*n<=(h:Y)^(1+m):=(by rw[rpow_add B,rpow_one];exact za L B.le);have:=one_le_mul_of_one_le_of_one_le G (zx n);push_cast at h1;linarith)
  linarith[(le_div_iff₀ r).mpr (le_of_mul_le_mul_right (by rw[mul_right_comm,<-rpow_add B,sub_add_cancel];linarith:(h:Y)^(((p+1:ℕ):Y)-(1+m))*f*(h:Y)^(1+m)<=3*(h:Y)^(1+m)) (rpow_pos_of_pos B (1+m)))]
 let e:=zn d u A;have o:=yk u A;have v:=yl u A;have x:=ym u A
 have Q:(h:Y)^d=h*(h:Y)^(d-1):=(by conv_lhs=>rw[show d=(d-1)+1 by omega,pow_succ,mul_comm])
 have hhp':(0:Y)< (h:Y)^(d-1)*z9 d A:=(by rw[<-x];have:=zo e.vP;positivity)
 have s:#(F h A)<=h^(d-1)*e.vol->False:=λ hle=>by have C:(#(F h A):Y)<=(h:Y)^(d-1)*z9 d A:=(by rw[<-x];exact_mod_cast hle);rw[Q] at q;nlinarith only[q,C,hhp',U]
 have O:∀ j,2<=e.width j:=λ j=>by
  by_contra ag;have R:e.width j=1:=(by have:=e.cB.wP j;dsimp[GAP.width] at ag ⊢;omega)
  apply s;refine (z6 (by rw[<-yh];exact iSM v h)).trans ((W e h).cLV.trans ?_)
  change ∏ i:Fin d,(W e h).width i<=h^(d-1)*∏ i:Fin d,e.width i;rw[<-mul_prod_erase univ _ (mem_univ j),show (W e h).width j=1 by dsimp[GAP.width,cB,W,nS,ZB.width] at R ⊢;have:=e.hle j;have:e.hi j=e.lo j:=(by omega);rw[this];omega,one_mul]
  exact (prod_le_prod' (g:=λ i=>h*e.width i) λ i _=>x5 (e.hle i) y).trans_eq (by rw[prod_mul_distrib,prod_const,card_erase_of_mem (mem_univ j),card_univ,Fintype.card_fin,<-mul_prod_erase univ (λ i=>e.width i) (mem_univ j),R,one_mul])
 have a0:(W e ⌈l*h⌉₊).iP:=by
  let t:=⌈l*h⌉₊;by_contra ah
  have C:(#(F h A):Y)<=(t:Y)*d*(h:Y)^(d-1)*z9 d A:=(by rw[<-x];exact_mod_cast (z6 (by rw[<-yh];exact iSM v h)).trans (w7 e y ah))
  have h1:f*h<=(t:Y)*d:=(by rw[Q] at q;nlinarith only[q,C,hhp'])
  have a1:(t:Y)<=(3/2:Y)*l*h:=(by linarith[(Nat.ceil_lt_add_one (by positivity:(0:Y)<=l*h)).le])
  have h3:(t:Y)*d<=(3/4:Y)*f*h:=calc (t:Y)*d<=((3/2:Y)*l*h)*((p+1:ℕ):Y):=y6 a1 (Z (by omega:d<=p+1)) (z7 d) (by positivity)
   _<=((3/2:Y)*(f/(2*((p+1:ℕ):Y)))*h)*((p+1:ℕ):Y):=by have:=xr (1:Y) (f/(2*((p+1:ℕ):Y)));gcongr
   _=(3/4:Y)*f*h:=by field_simp[(by positivity:(0:Y)< ((p+1:ℕ):Y)).ne'];ring
  linarith only[h1,h3,mul_pos r (zl h)]
 have I:(z3 e (l*h) o).iP:=yp a0 (by rw[<-x6 e o];exact w2 e (le_ceil _) o) rfl rfl (by dsimp[W,nS];rw[o.1,mul_zero])
 have a2:e.iP:=yp I (Subset.trans (λ w hw=>by simpa[z5,mTF,cB,W,nS] using hw) (xj e o (k:=1) (by simpa using (by linarith:(1:Y)<=l*h)))) rfl o.1 rfl
 refine ⟨d,u,X,q,O,a2,I,λ ak j=>le_of_not_gt λ S=>?_⟩
 have ap:2*(h:ℤ)*n< |e.step j| :=(by have:(h:ℤ)<=n:=(by exact_mod_cast ak);nlinarith)
 let Sg:=(z5 (W e h)).filter λ b=>(W e h).eval b∈zi (h*n);let J (b:ZV d) i:=if i=j then 0 else b i
 have a7:InjOn J (Sg:Set (ZV d)):=λ M al N am hp=>by
  have a8:=mem_Icc.mp (zg al).2;have a9:=mem_Icc.mp (zg am).2;have ho:∀ i,i≠j->M i=N i:=λ i hi=>by simpa[J,hi] using congrFun hp i
  have aa:(W e h).eval M-(W e h).eval N=(M j-N j)*e.step j:=(by dsimp[eval,W,nS];rw[o.1,mul_zero,zero_add,zero_add,<-sum_sub_distrib,sum_eq_single_of_mem j (mem_univ j) λ i _ hi=>by rw[ho i hi,sub_self]];ring)
  have ha:|M j-N j| *|e.step j| <=2*(h:ℤ)*n:=(by rw[<-abs_mul,<-aa,abs_le];push_cast at a8 a9;constructor <;> linarith)
  have ab:M j=N j:=(by by_contra ai;linarith[le_mul_of_one_le_left (abs_nonneg (e.step j)) (one_le_abs (sub_ne_zero.mpr ai))])
  ext i;by_cases hi:i=j;subst hi;exact ab;exact ho i hi
 have ac:Sg.image J⊆piFinset λ i:Fin d=>if i=j then ({0}:V ℤ) else Icc ((h:ℤ)*e.lo i) ((h:ℤ)*e.hi i):=λ w hw=>by rcases z0 hw with ⟨b,hb,rfl⟩;have ad:=zb (zg hb).1;rw[mem_piFinset];intro i;by_cases hi:i=j;subst hi;simp[J];simp only[J,if_neg hi];exact mem_Icc.mpr (ad i)
 have ae:F h A⊆Sg.image (W e h).eval:=λ z hz=>by rcases z0 ((by rw[<-yh];exact iSM v h:F h A⊆(W e h).tF) hz) with ⟨b,hb,rfl⟩;exact zd _ (zv ⟨hb,xh hA h hz⟩)
 apply s;refine (z6 ae).trans (card_image_le.trans ((card_image_of_injOn a7).symm.trans_le ((z6 ac).trans ?_)))
 rw[card_piFinset,<-mul_prod_erase univ _ (mem_univ j),if_pos rfl,card_singleton,one_mul]
 exact (prod_le_prod' (g:=λ i=>h*e.width i) λ i hi=>by rw[if_neg (ne_of_mem_erase hi),card_Icc,show (h:ℤ)*e.hi i+1-h*e.lo i=h*e.hi i-h*e.lo i+1 by ring];exact x5 (e.hle i) y).trans (by rw[prod_mul_distrib,prod_const,card_erase_of_mem (mem_univ j),card_univ,Fintype.card_fin];exact zu _ (by unfold GAP.vol ZB.vol;rw[<-mul_prod_erase univ (λ i=>e.cB.width i) (mem_univ j)];exact le_mul_of_pos_left _ (e.cB.wP j)))
lemma ww {d:ℕ} (H:AddSubgroup (ZV d)) (B:ZB d) {K:ℕ} (P:∀ j,2*K<=B.width j) (hS:(2:Y)^d*B.vol< ((K:Y)+1)*#(B.tF.filter (·∈H))):H.index≠0/\ H.index<=K:=by
 let E:V (ZV d):=insert 0 ((univ.image λ i:Fin d=>single i (1:ℤ))∪(univ.image λ i:Fin d=>single i (-1:ℤ)));have o:(0:ZV d)∈E:=mem_insert_self _ _
 have Q:∀ k,∀ t∈F k E,∀ j,|t j| <=(k:ℤ):=λ k=>by
  induction k with | zero=>intro t l j;simp only[F,iSm,mem_singleton] at l;subst l;simp | succ k f=>
   intro t l j;rcases y8 l with ⟨a,ha,b,m,rfl⟩;have:=f a ha j
   have a7:|b j| <=1:=(by rcases mem_insert.mp m with rfl|m;simp;rcases mem_union.mp m with m|m <;> (rcases z0 m with ⟨i,_,rfl⟩;by_cases I:j=i;subst I;simp;simp[single_eq_of_ne I]))
   have:=abs_add_le (a j) (b j);push_cast;simp only[Pi.add_apply];linarith
 let mk:=QuotientAddGroup.mk' H
 have J:∀ (U:V (ZV d⧸H)),(0:ZV d⧸H)∈U->(∀ q∈U,∀ e∈E,q+mk e∈U)->∀ q,q∈U:=λ U a2 w q=>by
  have hi:∀ (i:Fin d) (z:ℤ) (q:ZV d⧸H),q∈U->q+mk (z•single i 1)∈U:=λ i z=>Int.induction_on z (λ _ h=>by simpa using h) (λ n f q h=>by rw[add_zsmul,one_zsmul,map_add,<-add_assoc];exact w _ (f q h) _ (mem_insert_of_mem (mem_union_left _ (zd _ (mem_univ i))))) (λ n f q h=>by rw[sub_zsmul,one_zsmul,map_add,<-add_assoc];exact w _ (f q h) _ (mem_insert_of_mem (mem_union_right _ (zh ⟨i,mem_univ i,by ext j;by_cases e:j=i;subst e;simp;simp[single_eq_of_ne e]⟩))))
  have hs':∀ (s:V (Fin d)) (x:ZV d) (q:ZV d⧸H),q∈U->q+mk (∑ i∈s,x i•single i 1)∈U:=λ s x=>Finset.induction_on s (λ _ h=>by simpa using h) (λ i s a3 f q h=>by rw[sum_insert a3,map_add,<-add_assoc,add_right_comm];exact hi i (x i) _ (f q h))
  induction q using QuotientAddGroup.induction_on with | H x=>have p:=hs' univ x 0 a2;rwa[zero_add,show ∑ i:Fin d,x i•single i (1:ℤ)=x from funext λ j=>by simp[Finset.sum_apply,Pi.single_apply]] at p
 let G k:=(F k E).image mk;have D:∀ k,1<=#(G k):=λ k=>Nonempty.card_pos ⟨0,zh ⟨0,yb o k,map_zero mk⟩⟩
 have A:∀ k,G k=G (k+1)->H.index=#(G k):=λ k e=>@Nat.card_eq_fintype_card _ ⟨G k,J (G k) (zh ⟨0,yb o k,map_zero mk⟩) λ q u e' he=>by rcases z0 u with ⟨t,l,rfl⟩;rw[e];exact zh ⟨t+e',add_mem_add l he,map_add mk t e'⟩⟩
 by_contra N
 have L:∀ k ≤ K,k+1<=#(G k):=λ k=>by
  induction k with | zero=>intro _;exact D 0 | succ k f=>
   intro hk;by_cases g:G k=G (k+1);have:=A k g;have:=D k;by_cases a8:#(G k)<=K;exact absurd ⟨by omega,by omega⟩ N;rw[<-g];omega
   have:=card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨image_subset_image (yg o (Nat.le_succ k)),g⟩);have:=f (by omega);dsimp[G,F] at*;omega
 let c q:=if h:∃ v∈F K E,mk v=q then choose h else 0
 have r:∀ q∈G K,c q∈F K E/\ mk (c q)=q:=λ q u=>by have h:=z0 u;simp only[c,dif_pos h];exact choose_spec h
 let S:=B.tF.filter (·∈H);let C:ZB d:=⟨λ j=>B.lo j-K,λ j=>B.hi j+K,λ j=>by have:=B.hle j;omega⟩
 have R:Set.PairwiseDisjoint (G K:Set (ZV d⧸H)) (λ q=>S.image (·+c q)):=λ q1 a4 O a5 a6=>disjoint_left.mpr λ y p h2=>by
  rcases z0 p with ⟨s1,X,rfl⟩;rcases z0 h2 with ⟨s2,a0,g⟩;apply a6;rw[<-(r q1 a4).2,<-(r O a5).2];apply QuotientAddGroup.eq.mpr
  rw[show -(c q1)+c O=s1-s2 from eq_sub_iff_add_eq.mpr (by rw[add_assoc,add_comm (c O) s2,g];abel)];exact H.sub_mem (zg X).2 (zg a0).2
 have M:(G K).biUnion (λ q=>S.image (·+c q))⊆C.tF:=λ y hy=>by rcases mem_biUnion.mp hy with ⟨q,u,a1⟩;rcases z0 a1 with ⟨s,w,rfl⟩;exact zc λ j=>by have:=zb (zg w).1 j;have:=abs_le.mp (Q K _ (r q u).1 j);dsimp[C];change B.lo j-K<=s j+c q j/\ s j+c q j<=B.hi j+K;omega
 have T:C.vol<=2^d*B.vol:=(by rw[show 2^d*B.vol=∏ j:Fin d,2*B.width j by simp[ZB.vol,prod_mul_distrib]];exact prod_le_prod' λ j _=>by have p:=P j;have:=B.hle j;dsimp[ZB.width,C] at p ⊢;omega)
 have:((K:Y)+1)*#S<=(2:Y)^d*B.vol:=by exact_mod_cast (y2 _ (L K le_rfl)).trans ((by rw[sum_const,smul_eq_mul]:#(G K)*#S=∑ _∈G K,#S).trans_le (((sum_congr rfl λ _ _=>(yn _ _).symm).trans (card_biUnion R).symm).trans_le ((z6 M).trans (by rw[cTF];exact T))))
 linarith
lemma wf {d D h K k:ℕ} {b:Y} {P:GAP ℤ d} {H:AddSubgroup (ZV d)} (e:d<=D) (f:1<=h) (c:0< b) (g:(2:Y)^D/b< ((K:Y)+1))
 (i:2*K<=h) (p:K< 2^k) (l:∀ j,2<=P.width j) (m:b*(h:Y)^d*P.vol<=#((z5 (W P h)).filter (·∈H))):H.index≠0/\ H.index< 2^k:=by
 let a:=(W P h).cB
 have n:b*a.vol<=#(a.tF.filter (·∈H)):=((za (Z (x7 P f)|>.trans_eq (by push_cast;rfl):(a.vol:Y)<=(h:Y)^d*P.vol) c.le).trans_eq (by ring)).trans m
 have o:(2:Y)^d*a.vol< ((K:Y)+1)*#(a.tF.filter (·∈H)):=(mul_lt_mul_of_pos_right (lt_of_le_of_lt (pow_le_pow_right₀ (by norm_num) e) ((div_lt_iff₀ c).mp g)) (zo a.vP)).trans_le (by rw[mul_assoc];exact za n)
 have ⟨h1,h2⟩:=ww H a (λ j=>i.trans (xz l h j)) o;exact ⟨h1,h2.trans_lt p⟩
abbrev yv (D n:ℕ) (x:Y) (a b:V ℤ):Prop:=∀ d,1<=d->d<=D->∀ P:GAP ℤ d,P.iC->(∀ j,|P.step j| <=2*(n:ℤ)^2)->(P.vol:Y)<=(3/4:Y)*z9 d a->x< #(b\P.tF)
abbrev y4 (x a:Y) (n:ℕ) (A:V ℤ):Prop:=yv ⌊1+a⌋₊ n x A A
lemma wg {D n:ℕ} {x:Y} {a d:V ℤ} (e:1<=D) (c:2<=#a) (f:yv D n x a d):x< #(d\({0}:V ℤ)):=by
 let b:GAP ℤ 1:=⟨0,λ _=>0,λ _=>0,λ _=>0,λ _=>le_rfl⟩
 exact (f 1 le_rfl e b ⟨rfl,λ _=>⟨le_rfl,le_rfl⟩⟩ (λ _=>by simp[b]) (by have g:b.vol=1:=(by simp[GAP.vol,cB,ZB.vol,ZB.width,b]);have c:=Z (c.trans (xm le_rfl a));rw[g];push_cast at c ⊢;linarith)).trans_le (Z (z6 (sdiff_subset_sdiff Subset.rfl (by intro y i;rw[mem_singleton.mp i];exact zMC ⟨rfl,λ _=>⟨le_rfl,le_rfl⟩⟩))))
lemma wx (k x:Y) (hx:0< x) (n:ℕ) (A:V ℤ) (t:A⊆zi n) (u:0∈A):
 ∃ j:V ℤ,j⊆A/\ 0∈j/\ y4 x k n j/\ (#A:Y)-x*((⌊1+k⌋₊:Y)*log (2*(n:Y)+1)/log (4/3))<=#j:=by
 let D:=⌊1+k⌋₊;let a S:=∏ d∈Icc 1 D,z9 d S;have c:0< log (4/3:Y):=log_pos (by norm_num)
 have e:∀ U:V ℤ,0∈U->1<=a U:=λ U K=>one_le_prod' λ d s=>(Nonempty.card_pos ⟨0,K⟩).trans_le (xm (mem_Icc.mp s).1 U)
 have l:∀ M (S:V ℤ),a S=M->S⊆zi n->0∈S->∃ T:V ℤ,T⊆S/\ 0∈T/\ y4 x k n T/\ (#S:Y)-x*(log (a S:Y)/log (4/3))<=#T:=λ M=>by
  induction M using strong_induction_on with | h M ih=>
   intro S O B f;by_cases b:y4 x k n S
   . exact ⟨S,Subset.rfl,f,b,by have:=div_nonneg (log_nonneg (zk (e S f))) c.le;nlinarith⟩
   . unfold y4 yv at b;push Not at b;rcases b with ⟨d,C,E,P,g,m,G,z⟩;let S':=S∩P.tF;have h0S':0∈S':=mem_inter.mpr ⟨f,zMC g⟩
     have v:(a S':Y)<=(3/4:Y)*a S:=(by dsimp[a];have w:d∈Icc 1 D:=mem_Icc.mpr ⟨C,E⟩;rw[cast_prod,cast_prod,<-mul_prod_erase (Icc 1 D) _ w,<-mul_prod_erase (Icc 1 D) _ w];exact (y6 ((Z (x9 g inter_subset_right)).trans G) (prod_le_prod (λ _ _=>z7 _) λ i hi=>Z (wc (mem_Icc.mp (mem_of_mem_erase hi)).1 inter_subset_left)) (prod_nonneg λ _ _=>z7 _) (by positivity)).trans_eq (by ring))
     have o:=zo (by have:=e S f;omega:0< a S)
     obtain⟨T,p,I,q,X⟩:=ih (a S') (by rw[<-O];exact_mod_cast (by linarith:(a S':Y)< a S)) S' rfl (inter_subset_left.trans B) h0S'
     have L:(#S:Y)-x<=#S':=(by have:=congrArg ((↑):ℕ->Y) (card_inter_add_card_sdiff S P.tF);push_cast at this;linarith)
     have R:log (a S':Y)/log (4/3)<=log (a S:Y)/log (4/3)-1:=(by have N:=log_le_log (zo (by have:=e S' h0S';omega:0< a S')) v;rw[log_mul (by norm_num) o.ne',show log (3/4:Y)=-log (4/3:Y) by rw[<-log_inv];norm_num] at N;rw[div_le_iff₀ c,sub_mul,div_mul_cancel₀ _ c.ne',one_mul];linarith)
     exact ⟨T,p.trans inter_subset_left,I,q,by nlinarith⟩
 obtain⟨j,r,J,b,hc⟩:=l (a A) A rfl t u
 have y:(a A:Y)<=(2*(n:Y)+1)^D:=(by dsimp[a];rw[cast_prod];exact (prod_le_prod (λ _ _=>z7 _) λ d s=>by obtain⟨P,g,m,Q⟩:=wb d (mem_Icc.mp s).1 A;have:=Z ((x9 g m).trans (Q n t));push_cast at this;exact this).trans_eq (by rw[prod_const,Nat.card_Icc];simp))
 have z:=div_le_div_of_nonneg_right ((log_le_log (zo (by have:=e A u;omega:0< a A)) y).trans_eq (log_pow _ _)) c.le
 exact ⟨j,r,J,b,by nlinarith⟩
lemma wh {a b:AddSubgroup G1} (c:b< a) (d:b.index≠0):2*a.index<=b.index:=by
 have f:b.relIndex a≠1:=λ h=>not_le_of_gt c (relIndex_eq_one.mp h);have e:=relIndex_mul_index c.le
 have g:b.relIndex a≠0:=λ h=>d (by rw[h,zero_mul] at e;exact e.symm);rw[<-e];exact y2 a.index (by omega)
lemma wi {i c r x:Y} {s n h d:ℕ} {t:0< r} {A:V ℤ} (K:1< i) (L:0< c) (u:yu i c r s t) (I:s<=n) (v:A⊆zi n) (w:2<=#A)
 (j:(n:Y)<=(h:Y)^i) (z:h<=n) (k:y4 x i n A) (l:c*(h:Y)^d*z9 d A<=#(F h A)) {S:V ℤ} (f:S⊆A) (g:0∈S) (M:(#A:Y)-x<=#S):
 (3/4:Y)*c^2*(h:Y)^d*z9 d A<=#(F h S):=by
 have B:2<=#S:=(by by_contra N;have C:S={0}:=(by ext y;simp only[mem_singleton];exact ⟨λ J=>card_le_one.mp (by omega) y J 0 g,λ e=>e▸g⟩);linarith[wg (Nat.le_floor (by norm_num;linarith)) w k,xb f (by rw[C]:S⊆{0})])
 obtain⟨a,b,o,p,_,_,_,q⟩:=u n h S I (f.trans v) g B j
 have D:(3/4:Y)*z9 a A< z9 a S:=lt_of_not_ge λ hle=>by linarith[k a b o (zn a b S) (yk b S) (q z) (by rw[ym];exact hle),xb f (yl b S)]
 have E:1<=h:=by by_contra h0';have G:h=0:=(by omega);rw[G,cast_zero,zero_rpow (by linarith)] at j;linarith[zk (by have:=z6 v;rw[card_Icc] at this;omega:1<=n)]
 have m:(#(F h A):Y)<=(h:Y)^a*z9 a A:=(by exact_mod_cast xn (d:=a) b E (A:=A))
 calc (3/4:Y)*c^2*(h:Y)^d*z9 d A=(3/4:Y)*c*(c*(h:Y)^d*z9 d A):=by ring
  _<=(3/4:Y)*c*((h:Y)^a*z9 a A):=za (l.trans m)
  _=c*(h:Y)^a*((3/4:Y)*z9 a A):=by ring
  _<=#(F h S):=(za D.le).trans p
abbrev wy (a b:Y) (c e:ℕ):Prop:=∀ (n h:ℕ) (x:Y) (A:V ℤ),c<=n->0< x->A⊆zi n->0∈A->2<=#A->(n:Y)<=(h:Y)^a->h<=n->y4 x a n A->∀ {d} (hd1:1<=d),d<=⌊1+a⌋₊->b*(h:Y)^d*z9 d A<=#(F h A)->(∀ j,2<=(zn d hd1 A).width j)->∃ hA0:V ℤ,hA0⊆A/\ 0∈hA0/\ (#A:Y)-x/2<=#hA0/\ y4 (x/2) a n hA0/\ ∀ A'':V ℤ,A''⊆hA0->0∈A''->(#hA0:Y)-x/e<=#A''->z8 (z4 (zn d hd1 A)) A''=z8 (z4 (zn d hd1 A)) hA0
lemma wz (k z cp:Y) (B:ℕ) (E:1< k) (a3:0< z) (a4:0< cp) (a5:yu k z cp B a4):∃ b r:ℕ,2<=b/\ B<=r/\ wy k z r b:=by
 let D:=⌊1+k⌋₊;let L:Y:=(3/4:Y)*z^2;have a6:0< L:=(by positivity);let K:=⌊(2:Y)^D/L⌋₊;let c:=xa (K+2)+1;let b:=2*c+2;let M:=max 2 (2*K);let r:=max B (⌈(M:Y)^k⌉₊+1)
 have a7:K< 2^c:=lt_of_lt_of_le (by omega:K< K+2) ((le_pow_clog (by omega:1< 2) _).trans (zr (Nat.le_succ _)))
 have N:(M:Y)^k< r:=(le_ceil _).trans_lt (zw (by have:=zm B (⌈(M:Y)^k⌉₊+1);omega))
 refine ⟨b,r,by omega,zp _ _,λ n h x A hn hx hA h0 ad I ae J d q af a0 a1=>?_⟩
 have O:=xd E (N.trans_le (Z hn)) I;have a8:1<=h:=(by have:=zp 2 (2*K);omega)
 let C:=zn d q A;let s:=z4 C;have Q:=yk q A;have t:=yl q A;have R:=ym q A
 have l:∀ S:V ℤ,S⊆A->0∈S->(#A:Y)-x<=#S->(z8 s S).index≠0/\ (z8 s S).index< 2^c:=λ S e j v=>
  wf af a8 a6 (lt_floor_add_one _) ((zm 2 (2*K)).trans O) a7 a1 ((show L*(h:Y)^d*C.vol<=#(F h S) from by rw[R];exact wi E a3 a5 ((zp _ _).trans hn) hA ad I ae J a0 e j v).trans (Z (by rw[<-w4 C Q.1 (e.trans t) h];exact card_image_le.trans (z6 (xk C (e.trans t) h)))))
 let m (S:V ℤ):=∀ A'',A''⊆S->0∈A''->(#S:Y)-x/b<=#A''->z8 s A''=z8 s S
 have o:=zl b
 have a9:∃ S:V ℤ,S⊆A/\ 0∈S/\ (#A:Y)-(c:Y)*(x/b)<=#S/\ m S:=by
  by_contra ac
  have hb:∀ i ≤ c,∃ S:V ℤ,S⊆A/\ 0∈S/\ (#A:Y)-(i:Y)*(x/b)<=#S/\ 2^i<=(z8 s S).index:=λ i=>by
   induction i with | zero=>intro _;exact ⟨A,Subset.rfl,h0,by simp,Nat.pos_of_ne_zero (l A Subset.rfl h0 (by linarith)).1⟩ | succ i ih=>
    intro hi;obtain⟨S,e,j,v,G⟩:=ih (by omega)
    have u:¬m S:=λ hg=>ac ⟨S,e,j,by have:=Z (show i<=c by omega);nlinarith[show 0<=x/b by positivity],hg⟩
    unfold m at u;push Not at u;rcases u with ⟨X,p,w,aj,aa⟩
    have T:(#A:Y)-x<=#X:=(by have:=(div_le_one o).mpr (Z (by omega:i+1<=b));have:((i+1:ℕ):Y)*(x/b)=x*(((i+1:ℕ):Y)/b):=(by ring);push_cast at*;nlinarith)
    exact ⟨X,p.trans e,w,by push_cast;linarith,(by rw[pow_succ,mul_comm]:2^(i+1)=2*2^i).trans_le ((zu 2 G).trans (wh (lt_of_le_of_ne (ya p) aa) (l X (p.trans e) w T).1))⟩
  obtain⟨S,e,j,v,G⟩:=hb c le_rfl
  have:=(l S e j (by have:=(div_le_one o).mpr (Z (by omega:c<=b));have:(c:Y)*(x/b)=x*((c:Y)/b):=(by ring);nlinarith)).2;omega
 obtain⟨f,g,ab,al,hg⟩:=a9
 have U:(#A:Y)-x/2<=#f:=(by have:(c:Y)/b<=1/2:=(div_le_div_iff₀ o (by norm_num)).mpr (by rw[one_mul];exact_mod_cast (by omega:c*2<=b));have:(c:Y)*(x/b)=x*((c:Y)/b):=(by ring);nlinarith)
 refine ⟨f,g,ab,U,λ d' y a2 P ag ah ai=>?_,hg⟩
 have ak:=J d' y a2 P ag ah (ai.trans (za (Z (wc y g)) (by norm_num)))
 have hle:=(z6 (λ a ha=>by rcases zz ha with ⟨h1,h2⟩;by_cases h:a∈f;exact mem_union_right _ (y9 ⟨h,h2⟩);exact mem_union_left _ (y9 ⟨h1,h⟩):A\P.tF⊆(A\f)∪(f\P.tF))).trans (card_union_le _ _)
 have hAA':(#(A\f):Y)<=x/2:=(by rw[card_sdiff_of_subset g,cast_sub (z6 g)];linarith);have hR:=Z hle;push_cast at hR;linarith
lemma wj {d:ℕ} (B:ZB d) (j:Fin d):B.width j<=B.vol:=by unfold ZB.vol;rw[<-mul_prod_erase univ B.width (mem_univ j)];exact le_mul_of_pos_right _ (prod_pos λ i _=>B.wP i)
lemma wk [DecidableEq G1]:∀{n} (B:Fin n->V G1),(∀ i j,i≠j->Disjoint (B i) (B j))->z2 (univ.biUnion B)=m4fs λ i=>z2 (B i)
 | 0,_,_=>by simp[m4fs,z2,sS]
 | n+1,B,hd=>by
  have hu:univ.biUnion B=(univ.biUnion λ i:Fin n=>B i.castSucc)∪B (Fin.last n):=(by ext x;simp only[mem_union,mem_biUnion,mem_univ,true_and];exact ⟨by rintro⟨i,hi⟩;exact Fin.lastCases (motive:=λ k=>x∈B k->_) Or.inr (λ j h=>Or.inl ⟨j,h⟩) i hi,by rintro(⟨j,hj⟩|hl);exact ⟨j.castSucc,hj⟩;exact ⟨Fin.last n,hl⟩⟩)
  rw[hu,z2,sUD (by rw[disjoint_biUnion_left];exact λ i _=>hd i.castSucc (Fin.last n) (Fin.castSucc_ne_last i)),m4fs];congr 1;exact wk (λ i=>B i.castSucc) λ i j h=>hd i.castSucc j.castSucc λ e=>h (Fin.castSucc_injective n e)
lemma wl [DecidableEq G1] [DecidableEq G2] (f:G1→+G2) {B:V G2} {g:G2->G1} (d:∀ a∈B,f (g a)=a):(z2 (B.image g)).image f=z2 B:=by
 have hi:InjOn g (B:Set G2):=λ a c b k e=>by have:=congrArg f e;rwa[d a c,d b k] at this
 ext z;simp only[mem_image,z2,sS,mem_powerset];constructor
 . rintro⟨_,⟨T,j,rfl⟩,rfl⟩;let S:=B.filter λ a=>g a∈T
   have hS:S.image g=T:=(by ext v;simp only[mem_image,S,mem_filter];exact ⟨by rintro⟨a,⟨_,h⟩,rfl⟩;exact h,λ i=>by rcases z0 (j i) with ⟨a,c,rfl⟩;exact ⟨a,⟨c,i⟩,rfl⟩⟩)
   refine ⟨S,filter_subset _ _,?_⟩;rw[<-hS,sum_image (hi.mono (coe_subset.mpr (filter_subset _ _))),map_sum];exact sum_congr rfl λ a c=>(d a (filter_subset _ _ c)).symm
 . rintro⟨S,hS,rfl⟩;exact ⟨_,⟨S.image g,image_subset_image hS,rfl⟩,by rw[sum_image (hi.mono (coe_subset.mpr hS)),map_sum];exact sum_congr rfl λ a c=>d a (hS c)⟩
lemma wm {d:ℕ} (A:V (ZV d)) (w:Fin d->ℕ) (b:∀ v∈A,∀ j,|v j| <=w j):∀ u∈z2 A,∀ j,|u j| <=(#A:ℤ)*w j:=λ u c j=>by
 rcases z0 c with ⟨S,hS,rfl⟩;have a:=yf hS;rw[Finset.sum_apply]
 exact (abs_sum_le_sum_abs _ _).trans ((sum_le_sum λ v e=>b v (a e) j).trans ((by rw[sum_const,nsmul_eq_mul]:∑ _∈S,(w j:ℤ)=(#S:ℤ)*w j).trans_le (y7 (by exact_mod_cast z6 a))))
lemma wn {x a:Y} (b:0< x) (c:0< a):log x<=x^a/a:=by have d:=log_le_sub_one_of_pos (rpow_pos_of_pos b a);rw[log_rpow b a] at d;rw[le_div_iff₀ c];linarith
lemma v2 (S A:V ℤ) (hS:S.Nonempty) {k:ℕ} (L:1<=k) (hg:2*#S<=#(F k A)):∃ a∈A,(#S:Y)/(2*(k:Y))<=#(S.image (·+a)\S):=by
 have t:∀ k,1<=k->∀ M:Y,(∀ a∈A,(#(S.image (·+a)\S):Y)< M)->∀ b∈F k A,(#(S.image (·+b)\S):Y)< (k:Y)*M:=λ k=>by
  induction k with | zero=>omega | succ k ih=>
   rcases k with _|k;intro _ M i b g;rw[xe] at g;simpa using i b g
   intro _ M i b g;rcases y8 g with ⟨d,D,a,j,rfl⟩;have u:=ih (by omega) M i d D;have T:=i a j
   have l:S.image (·+(d+a))\S⊆(S.image (·+(d+a))\S.image (·+d))∪(S.image (·+d)\S):=λ x q=>by rcases zz q with ⟨c,f⟩;by_cases I:x∈S.image (·+d);exact mem_union_right _ (y9 ⟨I,f⟩);exact mem_union_left _ (y9 ⟨c,I⟩)
   have v:S.image (·+(d+a))\S.image (·+d)=(S.image (·+a)\S).image (·+d):=by ext x;simp only[Finset.mem_sdiff,mem_image];exact ⟨by rintro⟨⟨s,o,rfl⟩,hn⟩;refine ⟨s+a,⟨⟨s,o,rfl⟩,λ J=>hn ⟨s+a,J,?_⟩⟩,?_⟩ <;> ring,by rintro⟨y,⟨⟨s,o,rfl⟩,hn⟩,rfl⟩;refine ⟨⟨s,o,by ring⟩,?_⟩;rintro⟨Q,E,e⟩;exact hn ((by linarith:Q=s+a)▸E)⟩
   have N:=Z ((z6 l).trans ((card_union_le _ _).trans_eq (by rw[v,yn])));push_cast at N u ⊢;linarith
 by_contra j;push Not at j;have w:=zl k;let B:=F k A
 have O:∀ b∈B,(#(S.image (·+b)\S):Y)< (#S:Y)/2:=λ b g=>by have c:=t k L _ j b g;rwa[show (k:Y)*((#S:Y)/(2*(k:Y)))=(#S:Y)/2 by field_simp[w.ne']] at c
 have m:B.Nonempty:=card_pos.mp (by have:=hS.card_pos;dsimp[B];omega);let P b:=(S×ˢS).filter λ p=>p.2-p.1=b
 have z:∀ b∈B,(#S:Y)/2< #(P b):=λ b g=>by
  have n:#(P b)=#(S.image (·+b)∩S):=card_bij (λ p _=>p.2) (λ p r=>by rcases zg r with ⟨G,hd⟩;rcases mem_product.mp G with ⟨c,f⟩;exact mem_inter.mpr ⟨zh ⟨p.1,c,by linarith⟩,f⟩) (λ p1 c p2 f e=>by have:=(zg c).2;have:=(zg f).2;ext <;> linarith) (λ y R=>by rcases mem_inter.mp R with ⟨c,f⟩;rcases z0 c with ⟨x,q,rfl⟩;exact ⟨(x,x+b),zv ⟨mem_product.mpr ⟨q,f⟩,by ring⟩,rfl⟩)
  have:(#(P b):Y)+#(S.image (·+b)\S)=#S:=(by rw[n];exact_mod_cast (by rw[card_inter_add_card_sdiff,yn]:#(S.image (·+b)∩S)+#(S.image (·+b)\S)=#S));linarith[O b g]
 have C:Set.PairwiseDisjoint (B:Set ℤ) P:=λ _ _ _ _ K=>disjoint_left.mpr λ p c f=>K ((zg c).2.symm.trans (zg f).2)
 have U:=(by rw[sum_const,nsmul_eq_mul]:(#B:Y)*((#S:Y)/2)=∑ _∈B,(#S:Y)/2).trans_lt (sum_lt_sum_of_nonempty m z)
 have hle:∑ b∈B,(#(P b):Y)<=(#S:Y)*#S:=(by have:=Z (by rw[<-card_biUnion C];exact z6 λ p r=>by rcases mem_biUnion.mp r with ⟨_,_,h⟩;exact (zg h).1:∑ b∈B,#(P b)<=#(S×ˢS));rwa[card_product,cast_mul,cast_sum] at this)
 have X:=zo hS.card_pos;have:#B< 2*#S:=(by exact_mod_cast (by nlinarith:(#B:Y)< 2*#S));dsimp[B] at this;omega
lemma v3 {q v cp:Y} {N1 n s d:ℕ} {b7:0< cp} (c8:1< q) (ag:0< v) (c9:v<=1)
 (b8:N1<=n) (b9:yu q v cp N1 b7) {i l:V ℤ} (h0:0∈i) (ba:2<=#i) (ah:i⊆zi n) (a3:l⊆i.erase 0)
 (ai:yv ⌊1+q⌋₊ n ((s/(2*d):ℕ):Y) i l) (aj:s/d<=n) (bb:1<=s/(2*d))
 (a6:zt n q+y0 ⌊1+q⌋₊ v<=zs (s/d)) (bc:1+(2:Y)^(zt n q+2)*log (3*(n:Y)^2)< ((s/(2*d):ℕ):Y)/2):
 ∃ A':V ℤ,A'⊆l/\ #A'=s/(2*d)/\ y5 ⌊1+q⌋₊ v*#(F (s/d) i)<=#(z2 A'):=by
 let D:=⌊1+q⌋₊;have bd:1<=D:=Nat.le_floor (by norm_num;linarith)
 let J:=s/(2*d);let E:=y0 D v;let G:=1/(2*(2:Y)^E);let c:=zt n q;let N:=zs (s/d);let y:=(4/3:Y)*(2:Y)^D/v;let z:=N-E;have hrc':c+E<=N:=a6
 have Q:0< s/d:=(by by_contra h0';have e:s/d=0:=Nat.eq_zero_of_not_pos h0';dsimp[zs,zt] at a6;rw[e,Nat.log_zero_right] at a6;omega)
 have ca:(J:Y)< #l:=(wg bd ba ai).trans_le (Z (z6 sdiff_subset))
 let I (B:V ℤ) (x:ℤ):=#((z2 B).image (·+x)\z2 B)
 have a0:∀ B:V ℤ,B⊆l->#B< J->∃ a∈l\B,∀ b∈l\B,I B b<=I B a:=λ B hB an=>
  exists_max_image (l\B) _ (card_pos.mp (by rw[card_sdiff_of_subset hB];have:#B< #l:=(by exact_mod_cast (by linarith[zw an]:(#B:Y)< #l));omega))
 let nx B:=if h:B⊆l/\ #B< J then insert (choose (a0 B h.1 h.2)) B else B
 let sq j:=Nat.rec (motive:=λ _=>V ℤ) ∅ (λ _ p=>nx p) j
 have C:∀ j ≤ J,sq j⊆l/\ #(sq j)=j:=λ j=>by
  induction j with | zero=>intro _;exact ⟨empty_subset _,rfl⟩ | succ j ih=>
   intro M;obtain⟨hs,hc⟩:=ih (le_of_succ_le M);have hd:sq j⊆l/\ #(sq j)< J:=⟨hs,by omega⟩
   have a1:=choose_spec (a0 (sq j) hd.1 hd.2);change nx (sq j)⊆l/\ #(nx (sq j))=j+1;dsimp[nx];rw[dif_pos hd]
   exact ⟨insert_subset (zz a1.1).1 hs,by rw[card_insert_of_notMem (zz a1.1).2,hc]⟩
 have a7:∀ j< J,∃ a∈l\sq j,sq (j+1)=insert a (sq j)/\ ∀ b∈l\sq j,I (sq j) b<=I (sq j) a:=λ j M=>by
  have hd:sq j⊆l/\ #(sq j)< J:=⟨(C j M.le).1,by rw[(C j M.le).2];exact M⟩;have a1:=choose_spec (a0 (sq j) hd.1 hd.2);exact ⟨_,a1.1,by change nx (sq j)=_;dsimp[nx];rw[dif_pos hd],a1.2⟩
 clear_value nx sq
 let g j:Y:=#(z2 (sq j));have a8:∀ j,(1:Y)<=g j:=λ j=>zk (Nonempty.card_pos ⟨0,xc _⟩)
 have ak:∀ a b,a<=b->b<=J->g a<=g b:=λ a b ap hb=>by
  have m:∀ k,a+k<=J->g a<=g (a+k):=λ k=>by induction k with | zero=>intro _;exact le_rfl | succ k ih=>intro hk;exact (ih (by omega)).trans (by rcases a7 (a+k) (by omega) with ⟨x,_,e,_⟩;exact Z (by rw[<-Nat.add_assoc,e];exact z6 (xw (subset_insert x _))))
  simpa[add_sub_of_le ap] using m (b-a) (by omega)
 let GB:=l.powerset.filter λ B=>(#l:Y)-J<=#B;have a2:l∈GB:=zv ⟨mem_powerset_self l,by linarith[(z7 J:(0:Y)<=J)]⟩
 have a4:GB.Nonempty:=⟨l,a2⟩;let R r:=GB.inf' a4 λ B=>#(F (2^r) (insert 0 B));let t r:Y:=(R r:Y)/2
 have K:∀ r,(0:Y)< t r:=λ r=>by obtain⟨B,_,e⟩:=exists_mem_eq_inf' a4 (λ B=>#(F (2^r) (insert 0 B)));have:=zk (yy (mem_insert_self 0 B) (2^r));dsimp[t,R];rw[e];linarith
 have al:∀ r1 r2,r1<=r2->t r1<=t r2:=λ r1 r2 O=>by obtain⟨B,hB,e⟩:=exists_mem_eq_inf' a4 (λ B=>#(F (2^r2) (insert 0 B)));dsimp[t,R];rw[e];exact div_le_div_of_nonneg_right (Z ((inf'_le (λ B=>#(F (2^r1) (insert 0 B))) hB).trans (z6 (yg (mem_insert_self 0 B) (zr O))))) (by norm_num)
 have be:∀ j r,j< J->g j< t r->exp (1/(2:Y)^(r+2))*g j<=g (j+1):=λ j r M a5=>by
  have bf:l\sq j∈GB:=zv ⟨xp sdiff_subset,by rw[card_sdiff_of_subset (C j M.le).1,(C j M.le).2,cast_sub (by exact_mod_cast (by linarith[zw M]:(j:Y)<=#l))];linarith[Z M.le]⟩
  have bg:2*#(z2 (sq j))<=#(F (2^r) (insert 0 (l\sq j))):=(by exact_mod_cast (by dsimp[t,g] at a5;linarith:2*(#(z2 (sq j)):Y)<=R r):2*#(z2 (sq j))<=R r).trans (inf'_le _ bf)
  obtain⟨b,bw,bx⟩:=v2 (z2 (sq j)) (insert 0 (l\sq j)) ⟨0,xc _⟩ (y1 r) bg
  have as:b∈l\sq j:=(by rcases mem_insert.mp bw with rfl|h;exfalso;have bh:((z2 (sq j)).image (·+0)\z2 (sq j))=∅:=(by simp);rw[bh,card_empty,cast_zero] at bx;have:(0:Y)< #(z2 (sq j))/(2*((2^r:ℕ):Y)):=(by have:=a8 j;dsimp[g] at this;positivity);linarith;exact h)
  rcases a7 j M with ⟨a,bz,c0,c1⟩
  have bi:#(z2 (sq (j+1)))=#(z2 (sq j))+I (sq j) a:=by
   have bj:z2 (insert a (sq j))=z2 (sq j)∪(z2 (sq j)).image (·+a):=(by rw[<-singleton_union,z2,sUD (disjoint_singleton_left.mpr (zz bz).2)];ext x;simp only[sS,Finset.mem_add,mem_union,mem_image,mem_powerset];refine ⟨by rintro⟨_,⟨T,hT,rfl⟩,_,⟨S,hS,rfl⟩,rfl⟩;rcases subset_singleton_iff.mp hT with rfl|rfl;exact Or.inl ⟨S,hS,by simp⟩;exact Or.inr ⟨_,⟨S,hS,rfl⟩,by simp[add_comm]⟩,by rintro(⟨S,hS,rfl⟩|⟨_,⟨S,hS,rfl⟩,rfl⟩);exact ⟨0,⟨∅,empty_subset _,by simp⟩,_,⟨S,hS,rfl⟩,by simp⟩;exact ⟨a,⟨{a},Subset.rfl,by simp⟩,_,⟨S,hS,rfl⟩,by simp[add_comm]⟩⟩)
   rw[c0,bj,<-card_union_of_disjoint disjoint_sdiff];congr 1;ext x;simp only[mem_union,Finset.mem_sdiff];tauto
  have bk:(1+1/(2:Y)^(r+1))*g j<=g (j+1):=(by have hR:=congrArg ((↑):ℕ->Y) bi;have:=Z (c1 b as);have:g j/(2*((2^r:ℕ):Y))=(1/(2:Y)^(r+1))*g j:=(by push_cast;rw[pow_succ];ring);dsimp[g,I] at*;push_cast at hR;linarith)
  have bl:exp (1/(2:Y)^(r+2))<=1+1/(2:Y)^(r+1):=(by let x:=1/(2:Y)^(r+1);have cc:x<=1:=div_le_one_of_le₀ (one_le_pow₀ (by norm_num)) (by positivity);have u:(1:Y)<=exp (-(x/2))*(1+x):=(by nlinarith[show 0<=x by positivity]:(1:Y)<=(1-x/2)*(1+x)).trans (zj (by linarith[add_one_le_exp (-(x/2))]));have h4:=za u (exp_pos (x/2)).le;rw[mul_one,<-mul_assoc,<-exp_add,add_neg_cancel,exp_zero,one_mul] at h4;rwa[show 1/(2:Y)^(r+2)=x/2 by dsimp[x];rw[pow_succ];ring])
  exact (zj bl (by linarith[a8 j])).trans bk
 have am:∀ r,c-1<=r->r<=N->∃ (o:ℕ) (_:1<=o),o<=D/\ (3/8:Y)*v*((2^r:ℕ):Y)^o*z9 o i<=t r:=λ r af aq=>by
  obtain⟨B,ao,c2⟩:=exists_mem_eq_inf' a4 λ B=>#(F (2^r) (insert 0 B))
  have a9:=yf (zg ao).1;have an:=(zg ao).2;let X:=insert 0 B
  have au:X⊆i:=insert_subset h0 (a9.trans (a3.trans (erase_subset 0 i)))
  have av:2<=#X:=(by have cd:0< #B:=(by exact_mod_cast (by linarith:(0:Y)< #B));rw[card_insert_of_notMem λ c4=>notMem_erase 0 i (a3 (a9 c4))];omega)
  have aw:2^r<=n:=((zr aq).trans (pow_log_le_self 2 Q.ne')).trans aj
  have bm:(n:Y)<=((2^r:ℕ):Y)^q:=(by have m:=(le_ceil _).trans (Z (show ⌈(n:Y)^(1/q)⌉₊<=2^r by have:=le_pow_clog (by omega:1< 2) (⌈(n:Y)^(1/q)⌉₊+1);have:=zr af;dsimp[c,zt] at this;omega));have h3:=rpow_le_rpow (rpow_nonneg (z7 n) _) m (by linarith:0<=q);rwa[<-rpow_mul (z7 n),one_div_mul_cancel (by linarith:q≠0),rpow_one] at h3)
  obtain⟨o,w,P,c3,_,_,_,b5⟩:=b9 n (2^r) X b8 (au.trans ah) (mem_insert_self 0 B) av bm
  have bn:(3/4:Y)*z9 o i< z9 o X:=lt_of_not_ge λ hle=>by linarith[ai o w P (zn o w X) (yk w X) (b5 aw) (by rw[ym];exact hle),xb a9 ((subset_insert 0 B).trans (yl w X))]
  refine ⟨o,w,P,?_⟩;rw[show t r=(#(F (2^r) X):Y)/2 by dsimp[t,R,X];rw[c2]];linarith[(za bn.le).trans c3]
 have bo:∀ r,c<=r->r<=N->t r/t (r-1)<=y:=λ r af aq=>by
  obtain⟨o,w,P,cf⟩:=am (r-1) (by omega) (by omega)
  have bp:t r<=(1/2:Y)*((2^r:ℕ):Y)^o*z9 o i:=(by have m:=Z ((inf'_le (λ B=>#(F (2^r) (insert 0 B))) a2).trans ((z6 (iSM (insert_subset h0 (a3.trans (erase_subset 0 i))) _)).trans (xn w (y1 r))));rw[cast_mul,cast_pow] at m;dsimp[t,R];linarith)
  rw[div_le_iff₀ (K (r-1))]
  have bq:((2^r:ℕ):Y)^o=(2:Y)^o*((2^(r-1):ℕ):Y)^o:=(by have e:2^r=2*2^(r-1):=(by conv_lhs=>rw[<-Nat.sub_add_cancel (show 1<=r by dsimp[c,zt] at af;omega),pow_succ,mul_comm]);rw[e,cast_mul,mul_pow,cast_ofNat])
  calc t r<=(1/2:Y)*((2:Y)^o*((2^(r-1):ℕ):Y)^o)*z9 o i:=by rwa[bq] at bp
   _<=(1/2:Y)*((2:Y)^D*((2^(r-1):ℕ):Y)^o)*z9 o i:=by have:=pow_le_pow_right₀ (by norm_num:(1:Y)<=2) P;gcongr
   _=y*((3/8:Y)*v*((2^(r-1):ℕ):Y)^o*z9 o i):=by dsimp[y];field_simp[ag.ne'];ring
   _<=y*t (r-1):=by gcongr
 have ax:t c<=3*(n:Y)^2:=(by have cb:2^c<=n:=((zr (by omega:c<=N)).trans (pow_log_le_self 2 Q.ne')).trans aj;have m:=Z ((inf'_le (λ B=>#(F (2^c) (insert 0 B))) a2).trans ((xi ((insert_subset h0 (a3.trans (erase_subset 0 i))).trans ah) (2^c)).trans (by nlinarith:2*2^c*n+1<=2*n*n+1)));have:=zx n;push_cast at m;dsimp[t,R];nlinarith)
 let f r:=if h:∃ j< J,t r<=g j then find h else J
 have aa:∀ r,f r<=J:=λ r=>by dsimp[f];split_ifs with h;exact (find_spec h).1.le;rfl
 have br:∀ r1 r2,r1<=r2->f r1<=f r2:=λ r1 r2 O=>by dsimp[f];by_cases m:∃ j< J,t r1<=g j <;> by_cases u:∃ j< J,t r2<=g j;simp only[dif_pos m,dif_pos u];exact find_min' m ⟨(find_spec u).1,(al _ _ O).trans (find_spec u).2⟩;simp only[dif_pos m,dif_neg u];exact (find_spec m).1.le;exact absurd ⟨find u,(find_spec u).1,(al _ _ O).trans (find_spec u).2⟩ m;simp only[dif_neg m,dif_neg u];exact le_rfl
 have ab:∀ r,0< f r->g (f r-1)< t r:=λ r O=>by dsimp[f] at O ⊢;split_ifs at O ⊢ with h;exact not_le.mp λ hc=>find_min h (by omega:find h-1< find h) ⟨by have:=(find_spec h).1;omega,hc⟩;push Not at h;exact h (J-1) (by omega)
 have ac:∀ r,f r< J->t r<=g (f r):=λ r O=>by dsimp[f] at O ⊢;split_ifs at O ⊢ with h;exact (find_spec h).2;omega
 clear_value I GB R t f
 have ad:∀ (a b r:ℕ) (L U:Y),a< b->b<=J->0< L->L<=g a->g (b-1)< U->U<=t r->((b-a:ℕ):Y)<=1+(2:Y)^(r+2)*log (U/L):=λ a b r L U ap hb c5 c6 ar c7=>by
  have m:=x8 (f:=g) (exp_pos _).le (a:=a) (b-1-a) λ k hk=>be (a+k) r (by omega) ((ak (a+k) (b-1) (by omega) (by omega)).trans_lt (ar.trans_le c7))
  rw[add_sub_of_le (by omega:a<=b-1),<-exp_nat_mul] at m
  have u:=log_lt_log (exp_pos _) ((lt_div_iff₀ c5).mpr (((za c6 (exp_pos _).le).trans m).trans_lt ar))
  rw[log_exp,mul_one_div,div_lt_iff₀ (by positivity)] at u;have:((b-a:ℕ):Y)=((b-1-a:ℕ):Y)+1:=(by exact_mod_cast (by omega:b-a=(b-1-a)+1));linarith
 have bs:(f c:Y)< (J:Y)/2:=by
  by_cases h0':f c=0;rw[h0',cast_zero];linarith[zl J]
  have m:=ad 0 (f c) c 1 (t c) (by omega) (aa c) zero_lt_one (a8 0) (ab c (by omega)) le_rfl;rw[Nat.sub_zero,div_one] at m
  linarith[za (log_le_log (K c) ax) (by positivity:(0:Y)<=(2:Y)^(c+2)),bc]
 have ay:0< log y:=log_pos (by dsimp[y];rw[lt_div_iff₀ ag];have:(1:Y)<=(2:Y)^D:=one_le_pow₀ (by norm_num);nlinarith)
 have az:∀ k,c+k<=N->(f (c+k):Y)<=(f c:Y)+(2:Y)^(c+k)*(1+16*log y):=λ k=>by
  induction k with | zero=>intro _;have:(0:Y)<=(2:Y)^c*(1+16*log y):=(by positivity);linarith | succ k ih=>
   intro hk;have m:=ih (by omega);have bt:=br (c+k) (c+k+1) (by omega)
   have a0:(f (c+k+1):Y)-f (c+k)<=1+(2:Y)^(c+k+3)*log y:=by
    rw[<-cast_sub bt];by_cases he:f (c+k)=f (c+k+1);rw[he,Nat.sub_self,cast_zero];positivity
    have a5:f (c+k)< f (c+k+1):=(by omega)
    have u:=ad (f (c+k)) (f (c+k+1)) (c+k+1) (t (c+k)) (t (c+k+1)) a5 (aa _) (K _) (ac _ (a5.trans_le (aa _))) (ab _ (by omega)) le_rfl
    have h3:=log_le_log (div_pos (K _) (K _)) (bo (c+k+1) (by omega) (by omega))
    rw[Nat.add_sub_cancel] at h3;linarith[za h3 (by positivity:(0:Y)<=(2:Y)^(c+k+3))]
   rw[show c+(k+1)=c+k+1 by omega];nlinarith only[m,a0,show (2:Y)^(c+k+1)=2*(2:Y)^(c+k) by rw[pow_succ];ring,show (2:Y)^(c+k+3)=8*(2:Y)^(c+k) by rw[pow_add];ring,show (1:Y)<=(2:Y)^(c+k) from one_le_pow₀ (by norm_num),ay]
 have ae:f z< J:=by
  have m:=az (z-c) (by omega);rw[add_sub_of_le (by omega:c<=z)] at m
  have bu:64*(1+16*log y)<=(2:Y)^E:=(le_ceil _).trans ((Z ((by omega:⌈64*(1+16*log y)⌉₊<=⌈64*(1+16*log y)⌉₊+1).trans (le_pow_clog (by omega:1< 2) _))).trans_eq (by push_cast;rfl))
  have b0:(2:Y)^z*(2:Y)^E<=((s/d:ℕ):Y):=(by exact_mod_cast ((by rw[<-pow_add,Nat.sub_add_cancel (by omega:E<=N)]:2^z*2^E=2^N).trans_le (pow_log_le_self 2 Q.ne')))
  have bv:((s/d:ℕ):Y)<=4*(J:Y):=(by exact_mod_cast div_le_of_le_mul (by have hd:=x3 bb;have he:2*(2*d)*(s/(2*d))=d*(4*(s/(2*d))):=(by ring);dsimp[J];omega:s<=d*(4*J)))
  have b1:=za bu (by positivity:(0:Y)<=(2:Y)^z);exact_mod_cast (by linarith only[m,bs,b0,bv,b1]:(f z:Y)< J)
 have b2:=(ac z ae).trans (ak (f z) J ae.le le_rfl)
 have h2rt':G*((s/d:ℕ):Y)<=((2^z:ℕ):Y):=(by dsimp[G];rw[one_div,inv_mul_le_iff₀ (by positivity)];have m:=lt_pow_succ_log_self (by omega:1< 2) (s/d);have u:2^(N+1)=2*2^E*2^z:=(by rw[pow_succ,<-Nat.sub_add_cancel (by omega:E<=N),pow_add];ring);have h3:=zw (u▸m);rw[cast_mul,cast_mul,cast_pow,cast_ofNat] at h3;linarith)
 obtain⟨ds,w,P,b6⟩:=am z (by omega) (by omega);refine ⟨sq J,(C J le_rfl).1,(C J le_rfl).2,?_⟩
 have b3:0< G:=(by dsimp[G];positivity);have b4:G<=1:=(by dsimp[G];exact div_le_one_of_le₀ (by have:(1:Y)<=(2:Y)^E:=one_le_pow₀ (by norm_num);linarith) (by positivity))
 change ((3/8:Y)*v*G^D)*#(F (s/d) i)<=g J;clear_value G E y
 have ce:(#(F (s/d) i):Y)<=((s/d:ℕ):Y)^ds*z9 ds i:=(by exact_mod_cast xn w Q (A:=i))
 calc ((3/8:Y)*v*G^D)*#(F (s/d) i)<=((3/8:Y)*v*G^ds)*(((s/d:ℕ):Y)^ds*z9 ds i):=by have:=pow_le_pow_of_le_one b3.le b4 P;gcongr
  _=(3/8:Y)*v*(G*((s/d:ℕ):Y))^ds*z9 ds i:=by rw[mul_pow];ring
  _<=(3/8:Y)*v*((2^z:ℕ):Y)^ds*z9 ds i:=by gcongr
  _<=g J:=b6.trans b2
lemma v4 {d D h J N w:ℕ} {O:Y} (X:d<=D) (a0:1<=h) (a1:0< O) (a2:(2:Y)^D/O< ((N:Y)+1))
 (a3:2*N<=h) (a4:N< 2^w) (a5:J<=h) {b:GAP ℤ d} (o:b.iC) (P:∀ j,2<=b.width j)
 {m q n:V ℤ} (C:m⊆b.tF) (k:q⊆m) (g:n⊆q) (Q:#n=J)
 (a6:z8 (z4 b) q=z8 (z4 b) m) (a7:O*(h:Y)^d*b.vol<=#(z2 n)):
 ∃ Bi:V ℤ,n⊆Bi/\ Bi⊆q/\ #Bi<=J+w/\ z8 (z4 b) Bi=z8 (z4 b) m:=by
 let c:=z4 b;let L:=z8 c m;let r:=z8 c n
 have E:=wf X a0 a1 a2 a3 a4 P (a7.trans (Z (by rw[<-wl (zq b o.1) λ a s=>y3 b (C (k (g s)))];exact card_image_le.trans (z6 λ v B=>zv ⟨by rcases z0 B with ⟨S,hS,rfl⟩;have G:=yf hS;have x:(#S:ℤ)<=h:=(by exact_mod_cast (z6 G).trans (card_image_le.trans (by rw[Q];exact a5)));have I:∀ u∈S,u∈z5 b:=λ u p=>(by rcases z0 (G p) with ⟨a,s,rfl⟩;exact ys b (C (k (g s))));exact zc λ j=>by dsimp[cB,W,nS];rw[Finset.sum_apply];exact ⟨(mul_le_mul_of_nonpos_right x (o.2 j).1).trans ((by rw[sum_const,nsmul_eq_mul]:(#S:ℤ)*b.lo j=∑ _∈S,b.lo j).trans_le (sum_le_sum λ u p=>(zb (I u p) j).1)),(sum_le_sum λ u p=>(zb (I u p) j).2).trans ((by rw[sum_const,nsmul_eq_mul]:∑ _∈S,b.hi j=(#S:ℤ)*b.hi j).trans_le (y7 x (o.2 j).2))⟩,by rcases z0 B with ⟨S,hS,rfl⟩;exact sum_mem r λ u p=>subset_closure (yf hS p)⟩))))
 by_contra M
 have a8:∀ t ≤ w,∃ S:V ℤ,n⊆S/\ S⊆q/\ #S<=J+t/\ z8 c S< L/\ 2^t*(z8 c S).index<=r.index:=λ t=>by
  induction t with | zero=>intro _;exact ⟨n,Subset.rfl,g,by omega,lt_of_le_of_ne (ya (g.trans k)) (λ e=>M ⟨n,Subset.rfl,g,by omega,e⟩),by change 1*r.index<=r.index;omega⟩ | succ t ih=>
   intro ht;obtain⟨S,i,T,x,U,K⟩:=ih (le_of_succ_le ht)
   have ⟨a,haAi,hna⟩:∃ a∈q,c a∉z8 c S:=(by by_contra s;push Not at s;exact not_le_of_gt U (by dsimp[L];rw[<-a6];exact (closure_le _).mpr λ v B=>by rcases z0 B with ⟨a,aa,rfl⟩;exact s a aa))
   let S':=insert a S;have l:=insert_subset haAi T;have R:#S'<=J+(t+1):=(by dsimp[S'];have:=card_insert_le a S;omega)
   have a9:z8 c S< z8 c S':=lt_of_le_of_ne (ya (f:=c) (subset_insert a S)) (λ e=>hna (e▸subset_closure (zd c (mem_insert_self a S))))
   have y:(z8 c S).index≠0:=λ A=>by have z:=relIndex_mul_index (ya i:r<=z8 c S);rw[A,mul_zero] at z;exact E.1 z.symm
   exact ⟨S',i.trans (subset_insert a S),l,R,lt_of_le_of_ne (ya (l.trans k)) (λ e=>M ⟨S',i.trans (subset_insert a S),l,by omega,e⟩),((by rw[pow_succ];ring:2^(t+1)*(z8 c S').index=2^t*(2*(z8 c S').index)).trans_le (zu _ (wh a9 y))).trans K⟩
 obtain⟨S,i,_,_,_,K⟩:=a8 w le_rfl
 have y:(z8 c S).index≠0:=λ A=>by have z:=relIndex_mul_index (ya i:r<=z8 c S);rw[A,mul_zero] at z;exact E.1 z.symm
 have:=le_mul_of_pos_right (2^w) (Nat.pos_of_ne_zero y);omega
lemma v5 (e:Y) (v b o p i:ℕ) (I:1< e) (E:2<=b):
 let d:=8*e;∃ t:ℕ,4<=t/\ ∀ m n s:ℕ,t<=m->m<=2*n+1->(n:Y)<=(m:Y)^e->(m:Y)^(1/2:Y)<=s->
  v<=n/\ p<=s/b/\ 1<=s/(2*b)/\ s/(2*b)+o<=s/b/\ b*(s/(2*b)+o)<=s/\ (n:Y)<=((s/b:ℕ):Y)^d /\
  zt n d+i<=zs (s/b)/\ 1+(2:Y)^(zt n d+2)*log (3*(n:Y)^2)< ((s/(2*b):ℕ):Y)/2:=by
 intro d;let k:=max (b*(p+2)) (max (4*b) (2*b*o+2*b))
 obtain⟨t,a0⟩:=eventually_atTop.mp ((eventually_ge_atTop (max 4 (2*v+2))).and ((yo (a:=1/2) (c:=(k:Y)+1) (by norm_num)).and ((yo (a:=3*e) (c:=(2*(b:Y))^d) (by linarith)).and (yo (a:=1/4) (c:=24*(b:Y)*(1+384*(2*e+2)+(2:Y)^i)+1) (by norm_num)))))
 refine ⟨max 4 t,zp _ _,λ m n s hm ab u D=>?_⟩
 obtain⟨B,aa,a1,C⟩:=a0 m ((zm 4 t).trans hm)
 have J:=(zp _ _).trans B;have f:=zl m;have q:=zx m;have a4:=zl n;have a2:=zx n
 have K:v<=n:=(by have:=(zm 4 (2*v+2)).trans B;omega);have a5:k<=s:=(by exact_mod_cast (by linarith:(k:Y)<=s))
 have ⟨hSr1,hSr2,hSr3⟩:b*(p+2)<=k/\ 4*b<=k/\ 2*b*o+2*b<=k:=by simp only[k,le_max_iff,le_refl,true_or,or_true,and_self]
 have L:p<=s/b:=(by have:p+2<=s/b:=(le_div_iff_mul_le (by omega)).mpr (by nlinarith);omega)
 have x:1<=s/(2*b):=(le_div_iff_mul_le (by omega)).mpr (by omega)
 have y:b*(s/(2*b)+o)<=s:=(by rw[Nat.mul_add];have:=div_mul_le_self s (2*b);nlinarith)
 have M:s/(2*b)+o<=s/b:=(le_div_iff_mul_le (by omega)).mpr (by rw[mul_comm];exact y)
 have G:1<=s/b:=(by omega);have w:(s:Y)/(2*b)<=((s/b:ℕ):Y):=(div_le_iff₀ (by positivity)).mpr (by have:=Z (x3 G);push_cast at this;linarith)
 have N:(n:Y)<=((s/b:ℕ):Y)^d:=by
  have O:=rpow_le_rpow (by positivity) ((div_le_div_of_nonneg_right D (by positivity)).trans w) (by positivity:(0:Y)<=d)
  rw[div_rpow (by positivity) (by positivity),<-rpow_mul f.le,show (1/2:Y)*d=4*e by dsimp[d];ring] at O
  exact u.trans (((le_div_iff₀ (by positivity)).mpr ((za a1.le).trans_eq (by rw[<-rpow_add f];congr 1;ring))).trans O)
 let g:=zt n d
 have z:(2:Y)^(g+2)<=48*(m:Y)^(1/8:Y):=by
  have a6:2^(g-1)<=2*(⌈(n:Y)^(1/d)⌉₊+1):=(by dsimp[g,zt];generalize hc:Nat.clog 2 (⌈(n:Y)^(1/d)⌉₊+1)=c;cases c with | zero=>simp;omega | succ c'=>have P:¬Nat.clog 2 (⌈(n:Y)^(1/d)⌉₊+1)<=c':=(by omega);rw[clog_le_iff_le_pow (by omega)] at P;rw[pow_succ,mul_comm];omega)
  have a7:(2:Y)^(g+2)<=16*((⌈(n:Y)^(1/d)⌉₊:Y)+1):=(by exact_mod_cast (by rw[show g+2=(g-1)+3 from rfl,pow_add];linarith:2^(g+2)<=16*(⌈(n:Y)^(1/d)⌉₊+1)))
  have a8:(n:Y)^(1/d)<=(m:Y)^(1/8:Y):=(by have j:=rpow_le_rpow (z7 n) u (by positivity:(0:Y)<=1/d);rw[<-rpow_mul f.le,show e*(1/d)=1/8 by dsimp[d];field_simp[(by linarith:e≠0)]] at j;exact j)
  linarith[one_le_rpow q (by norm_num:(0:Y)<=1/8),(Nat.ceil_lt_add_one (rpow_nonneg (z7 n) (1/d))).le]
 have Q:(m:Y)^(1/8:Y)*(m:Y)^(1/8:Y)=(m:Y)^(1/4:Y):=(by rw[<-rpow_add f];norm_num)
 have A:(m:Y)^(1/4:Y)*(m:Y)^(1/4:Y)=(m:Y)^(1/2:Y):=(by rw[<-rpow_add f];norm_num)
 have l:(2:Y)<=b:=(by exact_mod_cast E)
 have R:1+(2:Y)^(g+2)*log (3*(n:Y)^2)< ((s/(2*b):ℕ):Y)/2:=by
  have S:log (3*(n:Y)^2)<=8*(2*e+2)*(m:Y)^(1/8:Y):=(by have a3:(4:Y)<=m:=(by exact_mod_cast J);have T:3*(n:Y)^2<=(m:Y)^(2*e+2):=(y6 (by rw[show (2:Y)=((2:ℕ):Y) by norm_num,rpow_natCast];nlinarith:(3:Y)<=(m:Y)^(2:Y)) ((pow_le_pow_left₀ (z7 n) u 2).trans_eq (by rw[<-rpow_natCast,<-rpow_mul f.le,cast_ofNat,mul_comm]))).trans_eq (by rw[<-rpow_add f];congr 1;ring);have a9:=(log_le_log (by positivity) T).trans_eq (log_rpow f _);have:=za (wn f (by norm_num:(0:Y)< 1/8)) (by linarith:0<=2*e+2);linarith)
  have U:(m:Y)^(1/2:Y)/(4*(b:Y))<=((s/(2*b):ℕ):Y):=(div_le_iff₀ (by positivity)).mpr (by have:=Z (x3 x);push_cast at this;linarith)
  have hL:1+(2:Y)^(g+2)*log (3*(n:Y)^2)<=(1+384*(2*e+2))*(m:Y)^(1/4:Y):=(by have j:=y6 z S (log_nonneg (by nlinarith)) (by positivity);have r:=one_le_rpow q (by norm_num:(0:Y)<=1/4);have w:48*(m:Y)^(1/8:Y)*(8*(2*e+2)*(m:Y)^(1/8:Y))=384*(2*e+2)*(m:Y)^(1/4:Y):=(by rw[<-Q];ring);linarith only[j,r,w])
  have hR:(1+384*(2*e+2))*(m:Y)^(1/4:Y)< (m:Y)^(1/2:Y)/(8*(b:Y)):=(lt_div_iff₀ (by positivity)).mpr (by have j:=mul_lt_mul_of_pos_right (by have:(0:Y)<=(2:Y)^i:=(by positivity);nlinarith only[C,l,I,this]:8*(b:Y)*(1+384*(2*e+2))< (m:Y)^(1/4:Y)) (rpow_pos_of_pos f (1/4));nlinarith only[j,A])
  linarith only[hL,hR,U,show (m:Y)^(1/2:Y)/(8*(b:Y))=((m:Y)^(1/2:Y)/(4*(b:Y)))/2 by ring]
 have X:g+i<=zs (s/b):=le_log_of_pow_le (by omega) (by
  have j:(2:Y)^(g+i)<=12*(2:Y)^i*(m:Y)^(1/4:Y):=(by rw[pow_add];have hle:=rpow_le_rpow_of_exponent_le q (by norm_num:(1/8:Y)<=1/4);have r:(2:Y)^(g+2)=4*(2:Y)^g:=(by rw[pow_add];ring);have:(0:Y)<=(2:Y)^i:=(by positivity);nlinarith only[z,hle,r,this])
  have r:12*(2:Y)^i*(m:Y)^(1/4:Y)< (m:Y)^(1/2:Y)/(2*(b:Y)):=(lt_div_iff₀ (by positivity)).mpr (by have hb:=mul_lt_mul_of_pos_right (by have:(0:Y)<=384*(2*e+2):=(by linarith);nlinarith only[C,l,this]:24*(b:Y)*(2:Y)^i< (m:Y)^(1/4:Y)) (rpow_pos_of_pos f (1/4));nlinarith only[hb,A])
  exact_mod_cast (j.trans_lt (r.trans_le ((div_le_div_of_nonneg_right D (by positivity)).trans w))).le)
 exact ⟨K,L,x,M,y,N,X,R⟩
lemma v6 {d s b K1 O D:ℕ} {M A al ce p:Y}
 (am:1<=s/b) (b7:K1<=s/b) (b8:b*K1<=s) (av:1<=D) (b9:4*(O:Y)/M<=D)
 (an:0< M) (ao:0< A) (br:A<=p/2) (aw:A<=1/(2*(b:Y)*D)) (bv:⌈16/M⌉₊+2<=s/b)
 {e:GAP ℤ d} (E:e.iC) (ax:∀ j,2<=e.width j) (ai:(z3 e (M*(s/b:ℕ)) E).iP)
 {m:V ℤ} (a4:m⊆e.tF) {c:GAP (ZV d) d} (f:c.iS) (ay:ce*(c.vol:Y)<=al*((s/b:ℕ):Y)^d*e.vol)
 (a5:∀ j,c.step j∈z8 (z4 e) m) (G:∀ x∈z8 (z4 e) m,∃! n:ZV d,∑ j,n j•c.step j=x)
 (az:∀ x∈z5 (W e (s/b)),x∈z8 (z4 e) m->x∈c.tF)
 (b0:∃ t:ZV d,∀ x∈c.tF,∀ j,(O:ℤ)*(W e (s/b)).lo j<=(x-t) j/\ (x-t) j<=(O:ℤ)*(W e (s/b)).hi j)
 (ba:(∀ i,s/b<=c.width i)->∀ S:Fin b->V (ZV d),(∀ t,S t⊆z5 c)->(∀ t,ce*c.vol<=#(S t))->(∀ t,zf ((S t-S t:V (ZV d)):Set (ZV d))=⊤)->∃ x0,((ZB.symm λ i=>⌊p*b*c.width i⌋₊).tF.image (·+x0))⊆m4fs S)
 {B:Fin b->V ℤ} (a3:∀ i,B i⊆m.erase 0) (b1:∀ i j,i≠j->Disjoint (B i) (B j))
 (P:∀ i,#(B i)<=K1/\ al*((s/b:ℕ):Y)^d*e.vol<=#(z2 (B i))/\ z8 (z4 e) (B i)=z8 (z4 e) m):
 ∃ (U:V ℤ) (o:GAP ℤ d) (q0:ℤ) (hS:o.iS),yw d s A ao (m.erase 0) U o q0 hS:=by
 let h:=s/b;let l:=z4 e;let L:=z8 l m;let hA:=m.erase 0;let g:=zq c f.1
 have a6:∀ v:ZV d,∑ j,v j•c.step j=0->v=0:=λ v N=>by obtain⟨_,_,u⟩:=G 0 (zero_mem L);rw[u v N,<-u 0 (by simp)]
 let q x:=if J:x∈L then choose (G x J) else 0
 have X:∀ x∈L,∑ j,q x j•c.step j=x:=λ x J=>by dsimp[q];rw[dif_pos J];exact (choose_spec (G x J)).1
 have a0:∀ x∈L,∀ v,∑ j,v j•c.step j=x->v=q x:=λ x J v N=>by dsimp[q];rw[dif_pos J];exact (choose_spec (G x J)).2 v N
 have ap:∀ a∈m,∀ j,(h:ℤ)*|q (l a) j| <=c.hi j:=λ a k j=>by
  have hL:l a∈L:=subset_closure (zd l k);have aq:=zb (ys e (a4 k))
  rcases z0 (az _ (zc λ i=>⟨ye (aq i).1 (z7 h),ye (aq i).2 (z7 h)⟩) (zsmul_mem hL (h:ℤ))) with ⟨v,N,he⟩
  simp only[eval,f.1,zero_add] at he
  have bb:v=(h:ℤ)•q (l a):=a0 _ (zsmul_mem hL _) v he|>.trans (a0 _ (zsmul_mem hL _) ((h:ℤ)•q (l a)) (by simp only[Pi.smul_apply,smul_eq_mul,mul_smul,<-smul_sum,X (l a) hL];rfl)).symm
  rw[bb] at N;have a7:=zb N j;dsimp[cB] at a7;rw[f.2 j] at a7;have:=abs_le.mpr a7;rwa[abs_mul,abs_of_nonneg (z7 h)] at this
 have I:∀ j,(h:ℤ)<=c.hi j:=λ j=>by obtain⟨_,J,n,bm,au⟩:=w5 a5 G j;rcases z0 J with ⟨a,k,rfl⟩;rw[a0 (l a) (subset_closure (zd l k)) n bm] at au;linarith[ap a k j,ye (one_le_abs au) (z7 h)]
 let r j:=(c.hi j).toNat/h;have b2:∀ j,1<=r j:=λ j=>div_pos (by have:=I j;omega) (by omega)
 have a1:∀ j,(h:ℤ)*r j<=c.hi j:=λ j=>by have:((r j:ℤ)*h)<=((c.hi j).toNat:ℤ):=(by exact_mod_cast div_mul_le_self (c.hi j).toNat h);have:=toNat_of_nonneg (by have:=I j;omega:(0:ℤ)<=c.hi j);linarith
 let o:GAP ℤ d:=⟨0,λ j=>e.eval (c.step j),λ j=>-(r j:ℤ),λ j=>(r j:ℤ),λ j=>by omega⟩;have a2:o.iS:=⟨rfl,λ _=>rfl⟩;have R:=ze a2
 let C:ZV d→+ℤ:=(zq e E.1).comp g
 have a8:∀ v,C v=o.eval v:=λ v=>by simp only[C,g,AddMonoidHom.comp_apply,zq,AddMonoidHom.coe_mk,ZeroHom.coe_mk,eval,f.1,zero_add,map_sum,map_zsmul,o]
 have a9:∀ a∈m,C (q (l a))=a:=λ a k=>by simp only[C,g,AddMonoidHom.comp_apply,zq,AddMonoidHom.coe_mk,ZeroHom.coe_mk,eval,f.1,zero_add,X (l a) (subset_closure (zd l k))];exact y3 e (a4 k)
 have ar:∀ a∈m,∀ j,|q (l a) j| <=r j:=λ a k j=>by have h1:(h:ℤ)*((q (l a) j).natAbs:ℤ)<=((c.hi j).toNat:ℤ):=(by rw[natCast_natAbs,toNat_of_nonneg (by have:=I j;omega)];exact ap a k j);have h3:((q (l a) j).natAbs:ℤ)<=r j:=(by exact_mod_cast (le_div_iff_mul_le (by omega)).mpr (by rw[mul_comm];exact_mod_cast h1));rwa[natCast_natAbs] at h3
 have aa:hA⊆o.tF:=λ a k=>zh ⟨q (l a),zc λ j=>abs_le.mp (ar a (erase_subset 0 m k) j),by rw[<-a8];exact a9 a (erase_subset 0 m k)⟩
 let ab:=erase_subset 0 m;let S i:=z2 ((B i).image λ a=>q (l a))
 have ac:∀ i,(S i).image C=z2 (B i):=λ i=>wl C λ a k=>a9 a (ab (a3 i k))
 have bc:∀ i,S i⊆z5 c:=λ i v N=>zc λ j=>by dsimp[cB];rw[f.2 j];exact abs_le.mp ((wm ((B i).image λ a=>q (l a)) r (λ u hu j=>by rcases z0 hu with ⟨a,k,rfl⟩;exact ar a (ab (a3 i k)) j) v N j).trans ((y7 (by exact_mod_cast card_image_le.trans ((P i).1.trans b7))).trans (a1 j)))
 have bd:∀ i,ce*c.vol<=#(S i):=λ i=>ay.trans ((P i).2.1.trans (by rw[<-ac i];exact Z card_image_le))
 have b3:∀ i,zf ((S i-S i:V (ZV d)):Set (ZV d))=⊤:=λ i=>by
  let K:=zf ((S i-S i:V (ZV d)):Set (ZV d));have ad:∀ v,g v=∑ j,v j•c.step j:=λ v=>by simp[g,zq,eval,f.1]
  have hL:L<=K.map g:=by dsimp[L,l];rw[<-(P i).2.2];refine (closure_le _).mpr λ y hy=>by rcases z0 hy with ⟨a,k,rfl⟩;refine ⟨q (l a),subset_closure ?_,by rw[ad,X _ (subset_closure (zd l (ab (a3 i k))))]⟩;exact mem_coe.mpr (sub_zero (q (l a))▸sub_mem_sub (zh ⟨{q (l a)},xp (singleton_subset_iff.mpr (zd (λ a=>q (l a)) k)),by simp⟩:q (l a)∈S i) (xc _:0∈S i))
  ext v;simp only[AddSubgroup.mem_top,iff_true];obtain⟨u,hu,bn⟩:=hL (x:=g v) (by rw[ad];exact sum_mem L λ j _=>zsmul_mem (a5 j) (v j))
  have h0:g (u-v)=0:=(by rw[map_sub,bn,sub_self]);rw[ad] at h0;rwa[sub_eq_zero.mp (a6 _ h0)] at hu
 obtain⟨v0,bo⟩:=ba (λ j=>by have:=I j;have:=f.2 j;dsimp[GAP.width,cB,ZB.width];omega) S bc bd b3
 let U:=univ.biUnion B;have ae:U⊆hA:=λ a k=>by rcases mem_biUnion.mp k with ⟨i,_,h⟩;exact a3 i h
 have b4:#U<=s:=card_biUnion_le.trans ((sum_le_sum λ i _=>(P i).1).trans ((by simp:∑ _∈univ,K1=b*K1).trans_le b8))
 have aj:(m4fs S).image C=z2 U:=(by rw[xv,show (λ i=>(S i).image C)=(λ i=>z2 (B i)) from funext ac,<-wk B b1])
 have be:(s:Y)<=2*(b:Y)*h:=(by have:=Z (x3 am);push_cast at this;linarith)
 have af:(z3 o (A*s) R).tF.image (·+C v0)⊆z2 U:=λ z hz=>by
  rcases z0 hz with ⟨_,bp,rfl⟩;rcases z0 bp with ⟨v,N,rfl⟩
  have bf:v∈(ZB.symm λ j=>⌊p*b*c.width j⌋₊).tF:=zc λ j=>by
   have hj:=zb N j;dsimp[cB,z3,rS,o,ZB.symm] at hj ⊢;have h1:=(zy hj.2).trans (floor_le _);have h2:-(A*s*r j)<=v j:=(by have hl:=(Int.le_ceil _).trans (zy hj.1);push_cast at hl;linarith)
   have bw:2*(h:Y)*r j<=c.width j:=(by exact_mod_cast (show 2*h*r j<=c.width j by dsimp[GAP.width,cB,ZB.width];have:((2*h*r j:ℕ):ℤ)<=c.hi j-c.lo j+1:=(by rw[f.2 j];push_cast;linarith[a1 j]);have:=I j;have:=f.2 j;omega))
   have bt:0<=p:=(by linarith)
   have bg:A*s*r j<=p*b*c.width j:=calc A*s*r j<=(p/2)*(2*(b:Y)*h)*r j:=by gcongr
    _=p*b/2*(2*(h:Y)*r j):=by ring
    _<=p*b/2*c.width j:=by gcongr
    _<=p*b*c.width j:=by have:0<=p*b*c.width j:=(by positivity);linarith
   exact abs_le.mp (by rw[<-natCast_natAbs];exact_mod_cast (Nat.le_floor_iff (by positivity)).mpr (by rw[<-cast_natCast,natCast_natAbs,cast_abs];exact (abs_le.mpr ⟨h2,h1⟩).trans bg))
  rw[show (z3 o (A*s) R).eval v=o.eval v by simp[eval,z3,rS,o],<-a8 v,<-map_add C v v0,<-aj];exact zd C (bo (zd _ bf))
 have bh:C v0∈zf (Set.range o.step):=by
  rcases z0 (by simpa using af (zd (·+C v0) (zMC (yq o _ R))):C v0∈z2 U) with ⟨T,hT,bq⟩
  rw[<-bq];exact sum_mem _ λ a k=>by rcases z0 (aa (ae (yf hT k))) with ⟨v,_,rfl⟩;simp only[eval,o,zero_add];exact sum_mem _ λ j _=>zsmul_mem (subset_closure (Set.mem_range_self j)) _
 have b5:(z3 o (A*s) R).iP:=by
  let w:=z3 e (M*h) E;have bs:=yz an (by omega:⌈16/M⌉₊<=h)
  have bi:∀ x∈c.tF,∀ j,2*|x j| <=(D:ℤ)*(w.hi j-w.lo j):=λ x J j=>by
   have h1:=w6 (Q:=(W e h).cB) f b0 x J j;dsimp[cB,W,nS] at h1;have bj:2*|(x j:Y)| <=O*(h:Y)*((e.hi j:Y)-e.lo j):=(by have h1':=zy h1;push_cast at h1';linarith)
   have bx:(1:Y)<=e.hi j-e.lo j:=(by exact_mod_cast (show (1:ℤ)<=e.hi j-e.lo j by have:=ax j;dsimp[GAP.width,cB,ZB.width] at this;have:=e.hle j;omega))
   have bk:(1/2:Y)*M*h*(e.hi j-e.lo j)<=(w.hi j:Y)-w.lo j:=(by dsimp[w,z3,rS];nlinarith[sub_one_lt_floor (M*h*e.hi j),ceil_lt_add_one (M*h*e.lo j)])
   have b6:4*(O:Y)<=M*D:=(by linarith[(div_le_iff₀ an).mp b9])
   have bl:2*|(x j:Y)| <=(D:Y)*((w.hi j:Y)-w.lo j):=(by have k:=za bk (z7 D);have hb:=zj b6 (by positivity:(0:Y)<=h*(e.hi j-e.lo j));have:0<=O*((h:Y)*((e.hi j:Y)-e.lo j)):=(by positivity);linarith only[bj,k,hb,this])
   exact_mod_cast (by rwa[<-cast_abs] at bl:(2*(|x j| :ℤ):Y)<=(D:ℤ)*(w.hi j-w.lo j))
  let Q':GAP ℤ d:=⟨0,λ j=>w.eval (c.step j),c.lo,c.hi,c.hle⟩;have ag:Q'.iS:=⟨rfl,f.2⟩
  have ah:=zl D;have as:=zl h;have ak:=zo (by by_contra h0;have:b=0:=(by omega);rw[this,Nat.div_zero] at am;omega:0< b)
  have bu:A*s*D<=h:=(zj (y6 aw be (z7 s)) (z7 D)).trans_eq (by field_simp[ah.ne',ak.ne'])
  refine yp (w8 (yq e _ E) ai f a6 av bi) (w3 a2 ag λ j=>?_) (by funext j;simp only[o,eval,z3,rS,E.1,zero_add]) rfl rfl
  have bz:(o.hi j:Y)<=(Q'.hi j:Y)/h:=(le_div_iff₀ as).mpr (by dsimp[o,Q'];have:=zy (a1 j);push_cast at this ⊢;linarith)
  have:=yx ((ze ag).2 j).2;calc A*s*o.hi j<=A*s*((Q'.hi j:Y)/h):=by gcongr
   _=(A*s/h)*Q'.hi j:=by ring
   _<=(1/(D:Y))*Q'.hi j:=by have:=(div_le_div_iff₀ as ah).mpr (by linarith:A*s*D<=1*h);gcongr
 exact ⟨U,o,C v0,a2,ae,b4,λ j=>by dsimp[o];exact_mod_cast b2 j,aa,bh,b5,af⟩
lemma v7 {f r cp u m:Y} {N1 o n s b d Ki p:ℕ} {al:0< cp}
 (a1:1< f) (am:0< r) (a2:r<=1) (an:2<=o) (ao:N1<=n)
 (ap:d<=⌊1+f⌋₊) (aq:1<=s/b) (ar:s/(2*b)+p<=s/b) (as:b*(s/(2*b)+p)<=s) (au:s/b<=n) (av:1<=s/(2*b))
 (O:0< m) (aw:(2:Y)^⌊1+f⌋₊/m< ((Ki:Y)+1)) (ax:2*Ki<=s/b) (ay:Ki< 2^p)
 (az:zt n f+y0 ⌊1+f⌋₊ r<=zs (s/b)) (b0:1+(2:Y)^(zt n f+2)*log (3*(n:Y)^2)< ((s/(2*b):ℕ):Y)/2)
 (Q:m=y5 ⌊1+f⌋₊ r*u)
 (b1:yu f r cp N1 al) {l:GAP ℤ d} (w:l.iC) (a3:∀ j,2<=l.width j) (a4:l.iP)
 {c:V ℤ} (U:0∈c) (a5:2<=#c) (a6:c⊆zi n) (a7:c⊆l.tF)
 (a8:y4 ((2*(o:Y)*s)/2) f n c)
 (a9:∀ A'',A''⊆c->0∈A''->(#c:Y)-(2*(o:Y)*s)/o<=#A''->z8 (z4 l) A''=z8 (z4 l) c)
 (aa:u*((s/b:ℕ):Y)^d*l.vol<=#(F (s/b) c)):
 ∃ B:Fin b->V ℤ,(∀ i,B i⊆c.erase 0)/\ (∀ i j,i≠j->Disjoint (B i) (B j)) /\
  ∀ i,#(B i)<=s/(2*b)+p/\ m*((s/b:ℕ):Y)^d*l.vol<=#(z2 (B i))/\ z8 (z4 l) (B i)=z8 (z4 l) c:=by
 let h:=s/b;let J:=s/(2*b);let y:=z4 l;let L:=z8 y c;let hA:=c.erase 0
 have b2:∀ t ≤ b,∃ B:Fin t->V ℤ,(∀ i,B i⊆hA)/\ (∀ i j,i≠j->Disjoint (B i) (B j))/\ ∀ i,#(B i)<=J+p/\ m*(h:Y)^d*l.vol<=#(z2 (B i))/\ z8 y (B i)=L:=λ t=>by
  induction t with | zero=>intro _;exact ⟨Fin.elim0,λ i=>i.elim0,λ i=>i.elim0,λ i=>i.elim0⟩ | succ t ih=>
   intro ht;obtain⟨B,b6,ae,E⟩:=ih (le_of_succ_le ht);let z:=univ.biUnion B;let R:=hA\z
   have A:#z<=s:=card_biUnion_le.trans ((sum_le_sum λ i _=>(E i).1).trans ((by simp:∑ _∈univ,(J+p)=t*(J+p)).trans_le ((y2 _ (by omega:t<=b)).trans as)))
   have ab:yv ⌊1+f⌋₊ n (J:Y) c R:=λ d' aj ak P a0 bb bc=>by
    have be:=a8 d' aj ak P a0 bb bc
    have ac:c\P.tF⊆(R\P.tF)∪z:=λ a C=>by rcases zz C with ⟨G,X⟩;have ha':a∈hA:=mem_erase.mpr ⟨λ e=>X (e▸zMC a0),G⟩;by_cases hU:a∈z;exact mem_union_right _ hU;exact mem_union_left _ (y9 ⟨y9 ⟨ha',hU⟩,X⟩)
    have hcl':=Z ((z6 ac).trans ((card_union_le _ _).trans (Nat.add_le_add_left A _)));push_cast at hcl'
    have bf:(2:Y)*s<=(2*(o:Y)*s)/2:=(by have:(2:Y)<=o:=(by exact_mod_cast an);nlinarith[(z7 s:(0:Y)<=s)])
    linarith[Z (div_le_self s (2*b))]
   have ad:z8 y R=L:=by
    have D:insert 0 R⊆c:=insert_subset U (sdiff_subset.trans (erase_subset 0 c))
    have b3:c\insert 0 R⊆z:=λ a C=>by rcases zz C with ⟨G,b7⟩;by_contra ba;exact b7 (if e:a=0 then e▸mem_insert_self 0 R else mem_insert_of_mem (y9 ⟨mem_erase.mpr ⟨e,G⟩,ba⟩))
    have b4:(#c:Y)-(2*(o:Y)*s)/o<=#(insert 0 R):=(by have h1:=z6 b3;rw[card_sdiff_of_subset D] at h1;have b5:=Z (h1.trans A);rw[cast_sub (z6 D)] at b5;rw[show 2*(o:Y)*s/o=2*s by field_simp[(zl o).ne']];linarith[(z7 s:(0:Y)<=s)])
    dsimp[L,y];rw[<-a9 (insert 0 R) D (mem_insert_self 0 R) b4];refine le_antisymm (ya (subset_insert 0 R)) ((closure_le _).mpr λ v hv=>?_)
    rcases z0 hv with ⟨a,C,rfl⟩;rcases mem_insert.mp C with rfl|haR;rw[yt w a4];exact zero_mem _;exact subset_closure (zd y haR)
   obtain⟨b8,af,ag,ah⟩:=v3 a1 am a2 ao b1 U a5 a6 sdiff_subset ab au av az b0
   have q:m*(h:Y)^d*l.vol<=#(z2 b8):=((by rw[Q];ring:m*(h:Y)^d*l.vol=y5 ⌊1+f⌋₊ r*(u*(h:Y)^d*l.vol)).trans_le (za aa)).trans ah
   obtain⟨Bt,ai,I,b9,S⟩:=v4 ap aq O aw ax ay ((Nat.le_add_right J p).trans ar) w a3 a7 (sdiff_subset.trans (erase_subset 0 c)) af ag ad q
   let g:Fin (t+1)->V ℤ:=Fin.snoc B Bt
   refine ⟨g,λ i=>Fin.lastCases (by simpa[g] using I.trans sdiff_subset) (λ j=>by simpa[g] using b6 j) i,λ i j bd=>?_,λ i=>Fin.lastCases ⟨by simpa[g] using b9,by simpa[g] using q.trans (Z (z6 (xw ai))),by simpa[g] using S⟩ (λ k=>by simpa[g] using E k) i⟩
   refine Fin.lastCases (motive:=λ i=>i≠j->Disjoint (g i) (g j)) ?_ (λ K=>?_) i bd
   . refine Fin.lastCases (motive:=λ j=>Fin.last t≠j->Disjoint (g (Fin.last t)) (g j)) (λ h=>absurd rfl h) (λ T _=>by simp only[g,Fin.snoc_last,Fin.snoc_castSucc];exact disjoint_left.mpr λ x M N=>(zz (I M)).2 (mem_biUnion.mpr ⟨T,mem_univ T,N⟩)) j
   . refine Fin.lastCases (motive:=λ j=>K.castSucc≠j->Disjoint (g K.castSucc) (g j)) (λ _=>by simp only[g,Fin.snoc_last,Fin.snoc_castSucc];exact disjoint_right.mpr λ x M N=>(zz (I M)).2 (mem_biUnion.mpr ⟨K,mem_univ K,N⟩)) (λ T h=>by simp only[g,Fin.snoc_castSucc];exact ae K T λ e=>h (congrArg Fin.castSucc e)) j
 exact b2 b le_rfl
lemma v8 (hNR:LNH) (D:ℕ) (c:Y) (i:0< c) (k:c<=1):
 ∃ κM b:ℕ,1<=κM/\ ∀ d,1<=d->d<=D->∃ e:ℕ,e<=κM/\ ∀ (Q:ZB d) (A:V (ZV d)),(∀ j,b<=Q.width j)->A⊆Q.tF->0∈A->c*Q.vol<=#A->
  ∃ P:GAP (ZV d) d,P.iS/\ (∀ j,P.step j∈zf (A:Set (ZV d)))/\ (∀ x∈zf (A:Set (ZV d)),∃! n:ZV d,∑ j,n j•P.step j=x) /\
   (∀ x∈Q.tF,x∈zf (A:Set (ZV d))->x∈P.tF)/\ (∃ t:ZV d,∀ x∈P.tF,∀ j,(e:ℤ)*Q.lo j<=(x-t) j/\ (x-t) j<=(e:ℤ)*Q.hi j)/\ (∀ j,(P.width j:Y)<=(e:Y)*Q.width j):=by
 choose g _ _ u _ _ w using λ d (a:1<=d) (_:d<=D)=>hNR d a c i k
 obtain⟨l,m⟩:=yc D g;obtain⟨b,v⟩:=yc D u
 exact ⟨max 1 l,b,zp _ _,λ d a f=>⟨g d a f,(m d a f).trans (zm _ _),λ Q A y z B C=>by obtain⟨P,_,hS,o,p,q,r,s,_⟩:=w d a f Q A (λ j=>(v d a f).trans (y j)) z B C;exact ⟨P,hS,o,p,q,r,s⟩⟩⟩
lemma v9 (hBox:LEH) {D:ℕ} (q:1<=D) (k:Y) (n:0< k) (o:k<=1):
 ∃ (c:Y) (e f:ℕ),0< c/\ 2<=e/\ ∀ d,1<=d->d<=D->∃ a:Y,c<=a/\ ∀ (Q:ZB d),(∀ j,f<=Q.width j)->
  ∀ S:Fin e->V (ZV d),(∀ t,S t⊆Q.tF)->(∀ t,k*Q.vol<=#(S t))->(∀ t,zf ((S t-S t:V (ZV d)):Set (ZV d))=⊤)->
   ∃ x0,((ZB.symm λ i=>⌊a*e*Q.width i⌋₊).tF.image (·+x0))⊆m4fs S:=by
 choose a u v hγ w using λ d (b:1<=d) (_:d<=D)=>hBox d b k n o
 obtain⟨c,l,m⟩:=xt q a hγ;obtain⟨p,r⟩:=yc D u;obtain⟨f,s⟩:=yc D v
 exact ⟨c,max 2 p,f,l,zp _ _,λ d b g=>⟨a d b g,m d b g,λ Q x=>w d b g Q (λ j=>(s d b g).trans (x j)) (max 2 p) ((r d b g).trans (zm _ _))⟩⟩
lemma va (hBox:LEH) (hNR:LNH) (hBilu:LBH) (u:Y) (c6:1< u):
 ∃ (c:Y) (dm M0:ℕ) (hc:0< c),c<=1/\ 1<=dm/\ 4<=M0 /\
  ∀ (n s:ℕ) (A:V ℤ),A⊆zi n->M0<=#A->(n:Y)<=(#A:Y)^u->(#A:Y)^(1/2:Y)<=s->(s:Y)<=c*#A/log #A->
   ∃ (d:ℕ) (_:1<=d) (_:d<=dm) (l A':V ℤ) (P:GAP ℤ d) (q0:ℤ) (hS:P.iS),
    l⊆A/\ (#A:Y)-c⁻¹*s*log #A<=#l/\ yw d s c hc l A' P q0 hS:=by
 let β':=8*u;have hβ':1< β':=(by dsimp[β'];linarith);let D:=⌊1+β'⌋₊;have ay:1<=D:=Nat.le_floor (by norm_num;linarith)
 obtain⟨N,cp,N1,af,ag,bt,_,cu,a8⟩:=wv hNR hBilu β' hβ'
 obtain⟨r,N2,cc,ce,cf⟩:=wz β' N cp N1 hβ' ag af a8
 let Kc:=y0 D N;let cd:=y5 D N;have bb:0< cd:=(by dsimp[cd,y5];positivity)
 have co:cd<=1:=(by dsimp[cd,y5];have v:(1/(2*(2:Y)^(y0 D N)))^D<=1:=pow_le_one₀ (by positivity) (div_le_one_of_le₀ (by have:(1:Y)<=(2:Y)^(y0 D N):=one_le_pow₀ (by norm_num);linarith) (by positivity));nlinarith)
 let g:=(3/4:Y)*N^2;have J:0< g:=(by dsimp[g];positivity);have ap:g<=1:=(by dsimp[g];nlinarith)
 let k:=cd*g;have a3:0< k:=mul_pos bb J;have aq:k<=1:=(by dsimp[k];nlinarith)
 let S:=⌊(2:Y)^D/k⌋₊;let ki:=xa (S+2)+1;have c7:(2:Y)^D/k< ((S:Y)+1):=lt_floor_add_one ((2:Y)^D/k)
 have c8:S< 2^ki:=lt_of_lt_of_le (by omega:S< S+2) ((le_pow_clog (by omega:1< 2) _).trans (zr (Nat.le_succ _)))
 obtain⟨f,b2,a9,au⟩:=v8 hNR D g J ap
 let X:=k/(f:Y)^D;have ab:0< X:=(by have:=zo (by omega:0< f);dsimp[X];positivity)
 have bc:X<=1:=(div_le_self a3.le (one_le_pow₀ (zk a9))).trans aq
 obtain⟨b3,e,b4,cm,av,bu⟩:=v9 hBox ay X ab bc
 let Mp:=⌈4*(f:Y)/cp⌉₊+1;have bd:1<=Mp:=(by omega);have c9:4*(f:Y)/cp<=Mp:=(le_ceil _).trans (Z (by omega))
 let b:=2*(r:Y)*((D:Y)*(u+2)/log (4/3))+(r:Y)+4;have K:0< b:=(by have:=log_pos (by norm_num:(1:Y)< 4/3);dsimp[b];positivity)
 let o:=min 1 (min (b3/2) (min (1/(2*(e:Y)*Mp)) (min (1/(4*b)) (1/(4*(e:Y))))))
 have a0:0< o:=lt_min zero_lt_one (lt_min (by positivity) (lt_min (by positivity) (lt_min (by positivity) (by positivity))))
 have ⟨hcf1,hcfγ,hcfp',hcfl,hcf4⟩:o<=1/\ o<=b3/2/\ o<=1/(2*(e:Y)*Mp)/\ o<=1/(4*b)/\ o<=1/(4*(e:Y)):=by simp only[o,min_le_iff,le_refl,true_or,or_true,and_self]
 let T:=max b2 (max b4 (max (⌈16/cp⌉₊+2) (max (2*S) 2)))
 have ⟨hHrW,hHrE,hHr16,hHrK,hHr2⟩:b2<=T/\ b4<=T/\ ⌈16/cp⌉₊+2<=T/\ 2*S<=T/\ 2<=T:=by simp only[T,le_max_iff,le_refl,true_or,or_true,and_self]
 obtain⟨M0,ah,bv⟩:=v5 u N2 e ki T Kc c6 av
 have a4:b=2*(r:Y)*((D:Y)*(u+2)/log (4/3))+(r:Y)+4:=rfl;have ar:g=(3/4:Y)*N^2:=rfl
 have be:Kc=y0 D N:=rfl;have as:k=y5 D N*g:=rfl;have bf:X=k/(f:Y)^D:=rfl
 clear_value Kc cd g k S ki X Mp b o T
 refine ⟨o,D,M0,a0,hcf1,ay,ah,λ n s A l hm b9 cl ba=>?_⟩
 let m:=#A;have a5:=ah.trans hm;have bg:m<=2*n+1:=(by have:=z6 l;rw[card_Icc] at this;dsimp[m];omega)
 obtain⟨b5,O,cg,b6,b7,ai,ch,ci⟩:=bv m n s hm bg b9 cl
 let h:=s/e;have w:1<=h:=(by omega);have ac:=ce.trans b5;have az:=zl m;have p:=xs a5
 have bh:=zl r;have ct:=zo (by have:=w.trans (div_le_self s e);omega:0< s)
 have ad:h<=n:=by
  have v:(s:Y)<=(m:Y)/(4*e):=(ba.trans (div_le_div_of_nonneg_left (by positivity) zero_lt_one p)).trans (by rw[div_one];exact (zj hcf4 (z7 m)).trans_eq (by ring))
  have h2:4*e*s<=m:=(by have:=zl e;exact_mod_cast (by linarith[(le_div_iff₀ (by positivity:(0:Y)< 4*e)).mp v]:(4*(e:Y))*s<=m))
  have:8*s<=m:=(y2 s (by omega:8<=4*e)).trans h2;have:=div_le_self s e;omega
 let A0:=insert 0 A;have x:A0⊆zi n:=insert_subset (mem_Icc.mpr ⟨by omega,by omega⟩) l
 obtain⟨Q,C,aj,ak,bw⟩:=wx β' (2*(r:Y)*s) (by positivity) n A0 x (mem_insert_self 0 A)
 have a6:(m:Y)-(2*(r:Y)*((D:Y)*(u+2)/log (4/3)))*s*log m<=#Q:=by
  have cq:=log_pos (by norm_num:(1:Y)< 4/3);have bi:=Z (z6 (subset_insert 0 A))
  have cr:log (2*(n:Y)+1)<=(u+2)*log m:=(by have:=zx n;have y:(4:Y)<=m:=(by exact_mod_cast a5);exact (log_le_log (by positivity) ((by linarith:2*(n:Y)+1<=3*n).trans ((y6 (by rw[show (2:Y)=((2:ℕ):Y) by norm_num,rpow_natCast];nlinarith only[y]:(3:Y)<=(m:Y)^(2:Y)) b9).trans_eq (by rw[<-rpow_add az];congr 1;ring)))).trans_eq (log_rpow az _))
  have h2:2*(r:Y)*s*((D:Y)*log (2*(n:Y)+1)/log (4/3))<=(2*(r:Y)*((D:Y)*(u+2)/log (4/3)))*s*log m:=calc _<=2*(r:Y)*s*((D:Y)*((u+2)*log m)/log (4/3)):=by gcongr
   _=_:=by ring
  linarith only[bw,bi,h2]
 have a7:b*s*log m<=(m:Y)/4:=by
  have v:b*s*log m<=(b*o)*m:=(zj (za ba K.le) (by linarith only[p])).trans_eq (by change b*(o*m/log m)*log m=(b*o)*m;rw[mul_assoc,div_mul_cancel₀ _ (by linarith only[p]:log m≠0),<-mul_assoc])
  have h2:b*o<=1/4:=(za hcfl K.le).trans_eq (by rw[mul_one_div,div_eq_div_iff (by positivity) (by norm_num)];ring);linarith only[v,zj h2 (z7 m)]
 have a1:2<=#Q:=(by have hle:2*(r:Y)*((D:Y)*(u+2)/log (4/3))<=b:=(by rw[a4];linarith only[bh]);have h3:=zj (zj hle (z7 s)) (by linarith only[p]);have y:(4:Y)<=m:=(by exact_mod_cast a5);exact_mod_cast (by linarith only[a6,a7,h3,y]:(2:Y)<=#Q))
 obtain⟨d,t,I,al,R,a2,aw,_⟩:=a8 n h Q ac (C.trans x) aj a1 ai
 let i:=zn d t Q;let φ:=z4 i;have z:=yk t Q;have M:=yl t Q;have bj:=ym t Q
 obtain⟨E,q,G,b8,bx,bz⟩:=cf n h (2*(r:Y)*s) Q b5 (by positivity) (C.trans x) aj a1 ai ad ak t I al R
 let l:=E.erase 0;have bk:l⊆A:=λ a ha=>by have b0:=mem_erase.mp ha;rcases mem_insert.mp (C (q b0.2)) with rfl|h;exact absurd rfl b0.1;exact h
 have b1:(m:Y)-b*s*log m<=#l:=(by have v:(#l:Y)=#E-1:=(by dsimp[l];rw[card_erase_of_mem G,cast_sub (Nonempty.card_pos ⟨0,G⟩),cast_one]);have ca:=zk (w.trans (div_le_self s e));have bl:=za (le_mul_of_one_le_right (z7 s) p) (z7 r);have bm:(1:Y)<=s*log m:=(by nlinarith only[ca,p]);rw[a4];nlinarith only[v,b8,a6,bl,bm])
 have bn:(m:Y)-o⁻¹*s*log m<=#l:=(by have:4*b<=o⁻¹:=(le_inv_comm₀ (by positivity) a0).mpr (by rw[<-one_div];exact hcfl);have h2:=zj (zj (by linarith only[this,K]:b<=o⁻¹) (z7 s)) (by linarith only[p]);linarith only[b1,h2])
 have bo:2<=#E:=(by have y:(4:Y)<=m:=(by exact_mod_cast a5);have v:1<=#l:=(by exact_mod_cast (by linarith only[b1,a7,y]:(1:Y)<=#l));dsimp[l] at v;rw[card_erase_of_mem G] at v;omega)
 let L:=z8 φ E;let Qx:ZB d:=(W i h).cB;let U:=F h (E.image φ)
 have ae:g*(h:Y)^d*i.vol<=#(F h E):=(by rw[bj,ar];exact wi hβ' ag a8 ac (C.trans x) a1 ai ad ak al q G (by have:(0:Y)<=(r:Y)*s:=(by positivity);linarith only[b8,this]))
 have bp:zf (U:Set (ZV d))=L:=xy (zh ⟨0,G,yt z a2⟩) w
 have bq:g*Qx.vol<=#U:=calc g*Qx.vol<=g*((h:Y)^d*i.vol):=za (by change ((W i h).vol:Y)<=(h:Y)^d*i.vol;exact (Z (x7 i w)).trans_eq (by push_cast;rfl)) J.le
  _<=#(F h E):=by rw[<-mul_assoc];exact ae
  _<=#U:=Z (by rw[<-w4 i z.1 (q.trans M) h];exact card_image_le)
 obtain⟨cv,aa,c0⟩:=au d t I
 obtain⟨Qb,c1,am,an,ao,c2,c3⟩:=c0 Qx U (λ j=>(hHrW.trans O).trans (xz R h j)) ((xk i (q.trans M) h).trans (filter_subset _ _)) (yb (zh ⟨0,G,yt z a2⟩) h) bq
 rw[bp] at am an ao
 obtain⟨B,cj,c4,ax⟩:=v7 hβ' ag bt cc ac I w b6 b7 ad cg a3 c7 (hHrK.trans O) c8 (be▸ch) ci as a8 z R a2 G bo ((q.trans C).trans x) (q.trans M) bx bz ae
 have br:X*(Qb.vol:Y)<=k*(h:Y)^d*i.vol:=by
  have bs:(0:Y)< (f:Y)^D:=(by have:=zo (by omega:0< f);positivity)
  have v:(Qb.vol:Y)<=(f:Y)^d*(W i h).vol:=(by change ((∏ j:Fin d,Qb.width j:ℕ):Y)<=(f:Y)^d*((∏ j:Fin d,(W i h).width j:ℕ):Y);rw[cast_prod,cast_prod,show (f:Y)^d*∏ j:Fin d,((W i h).width j:Y)=∏ j:Fin d,((f:Y)*(W i h).width j) by rw[prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]];exact prod_le_prod (λ _ _=>z7 _) λ j _=>(c3 j).trans (zj (Z aa)))
  have cb:(Qb.vol:Y)<=(f:Y)^D*((h:Y)^d*i.vol):=calc (Qb.vol:Y)<=(f:Y)^d*((h:Y)^d*i.vol):=v.trans (za (Z (x7 i w)|>.trans_eq (by push_cast;rfl)))
   _<=(f:Y)^D*((h:Y)^d*i.vol):=by have:=pow_le_pow_right₀ (zk a9) I;gcongr
  exact (za cb ab.le).trans_eq (by rw[bf,<-mul_assoc,div_mul_cancel₀ _ bs.ne',<-mul_assoc])
 obtain⟨cs,cn,ck⟩:=bu d t I
 obtain⟨A',Qf,q0,c5,ho⟩:=v6 w b6 b7 bd ((div_le_div_of_nonneg_right (by linarith[Z aa]) af.le).trans c9) af a0 (hcfγ.trans (by linarith)) hcfp' (hHr16.trans O) z R aw (q.trans M) c1 br am an ao c2 (λ hw=>ck Qb.cB (λ j=>(hHrE.trans O).trans (hw j))) cj c4 ax
 exact ⟨d,t,I,l,A',Qf,q0,c5,bk,bn,ho⟩
def yd (c H:ℕ):ZV c→+ℤ:=⟨⟨λ a=>∑ j:Fin c,(H:ℤ)^(j:ℕ)*a j,by change ∑ j:Fin c,(H:ℤ)^(j:ℕ)*(0:ℤ)=0;simp⟩,λ a b=>by dsimp;rw[<-sum_add_distrib];exact sum_congr rfl λ _ _=>by ring⟩
lemma xo {d H:ℕ} (z:2<=H) {a b:ZV d} (w:∀ j,2*|a j| < H) (x:∀ j,2*|b j| < H) (y:yd d H a=yd d H b):a=b:=by
 apply sub_eq_zero.mp;let c:=a-b;have hc:∀ j,|c j| < H:=λ j=>by simp only[c,Pi.sub_apply];linarith[abs_sub (a j) (b j),w j,x j]
 have m:yd d H c=0:=(by dsimp[c];rw[map_sub,y,sub_self]);by_contra u
 have i:∃ k,∃ hk:k< d,c ⟨k,hk⟩≠0:=(by by_contra ha';push Not at ha';exact u (funext λ j=>ha' j.1 j.2))
 let f:=find i;obtain⟨s,t⟩:(∃ hk:f< d,c ⟨f,hk⟩≠0):=find_spec i
 have n:∀ j:Fin d,(j:ℕ)< f->c j=0:=λ j l=>by have:=find_min i l;push Not at this;exact this j.2
 let g:Fin d:=⟨f,s⟩
 have o:(H:ℤ)^f*c g+∑ j∈univ.erase g,(H:ℤ)^(j:ℕ)*c j=0:=(by have:=add_sum_erase univ (λ j:Fin d=>(H:ℤ)^(j:ℕ)*c j) (mem_univ g);change ∑ j:Fin d,(H:ℤ)^(j:ℕ)*c j=0 at m;rwa[m] at this)
 have p:(H:ℤ)^(f+1)∣∑ j∈univ.erase g,(H:ℤ)^(j:ℕ)*c j:=dvd_sum λ j l=>by by_cases v:(j:ℕ)< f;rw[n j v,mul_zero];exact dvd_zero _;exact dvd_mul_of_dvd_left (pow_dvd_pow (H:ℤ) (by have:(j:ℕ)≠f:=λ e=>(mem_erase.mp l).1 (Fin.ext e);omega)) _
 have q:(H:ℤ)∣c g:=(mul_dvd_mul_iff_left (pow_ne_zero f (by omega:(H:ℤ)≠0))).mp (by rw[<-pow_succ,eq_neg_of_add_eq_zero_left o];exact dvd_neg.mpr p)
 have r:(H:ℤ)∣|c g| :=(by rcases abs_cases (c g) with ⟨h,_⟩|⟨h,_⟩;rwa[h];rw[h];exact dvd_neg.mpr q);linarith[le_of_dvd (abs_pos.mpr t) r,hc g]
lemma vb {b m s n H N:ℕ} {c:Y} (hc:0< c) (b3:(2:Y)<=c*s) (ah:2<=H) (b5:2*((N:ℤ)*((2*s*n+1:ℕ):ℤ)^b*(2*(s:ℤ)*n)+(s:ℤ)*n)< H)
 {B:ZB b} {A:V (ZV b)} (Q:A⊆B.tF) (as:∀ x∈B.tF,∀ j,|x j| <=n) (au:∀ x∈B.tF,∀ j,2*|x j| < H)
 (S:InjOn (yd b H) (B.tF:Set (ZV b))) (a4:0< log m) (av:(s:Y)<=(m:Y)/(log m)^2)
 {L M:V ℤ} {t:GAP ℤ N} {U:ℤ} (l:t.iS) (a5:L⊆A.image (yd b H)) (b4:(m:Y)-c⁻¹*s*log m<=#L)
 (ad:yw N s c hc L M t U l):
 ∃ (E f:V (ZV b)) (P:GAP (ZV b) N) (p:ZV b) (hS:P.iS),E⊆A/\ (m:Y)-c⁻¹*m/log m<=#E/\ yw N s c hc E f P p hS:=by
 rcases ad with ⟨a1,a2,ab,aq,_,ac,I⟩
 let o:=yd b H;let E:=A.filter (λ a=>o a∈L);let f:=A.filter (λ a=>o a∈M)
 have ak:E.image o=L:=(by ext z;simp only[mem_image,E,mem_filter];exact ⟨by rintro⟨_,⟨_,h⟩,rfl⟩;exact h,λ hz=>by rcases z0 (a5 hz) with ⟨a,D,rfl⟩;exact ⟨a,⟨D,hz⟩,rfl⟩⟩)
 have a6:f.image o=M:=(by ext z;simp only[mem_image,f,mem_filter];exact ⟨by rintro⟨_,⟨_,h⟩,rfl⟩;exact h,λ hz=>by rcases z0 (a5 (a1 hz)) with ⟨a,D,rfl⟩;exact ⟨a,⟨D,hz⟩,rfl⟩⟩)
 have C:E⊆A:=filter_subset _ _;have J:f⊆E:=λ a D=>zv ⟨(zg D).1,a1 (zg D).2⟩
 have al:#E=#L:=(by rw[<-ak];exact (card_image_of_injOn (S.mono (coe_subset.mpr (C.trans Q)))).symm)
 have a7:#f=#M:=(by rw[<-a6];exact (card_image_of_injOn (S.mono (coe_subset.mpr ((J.trans C).trans Q)))).symm)
 have ae:(m:Y)-c⁻¹*m/log m<=#E:=(by rw[al];have h2:(s:Y)*log m<=(m:Y)/log m:=(zj av a4.le).trans_eq (by field_simp[a4.ne']);have:=za h2 (inv_nonneg.mpr hc.le);linarith[show c⁻¹*((m:Y)/log m)=c⁻¹*m/log m by ring])
 have G:(z2 f).image o=z2 M:=(by rw[<-a6];exact wo o (S.mono (coe_subset.mpr ((J.trans C).trans Q))))
 have r:∀ u∈z2 f,∀ j,|u j| <=(s:ℤ)*n:=λ u hu j=>(wm f (λ _=>n) (λ a D=>as a (Q (C (J D)))) u hu j).trans (y7 (by exact_mod_cast (a7▸a2)) (z7 n))
 have O:=ze l;let d:=z3 t (c*s) O
 obtain⟨p,a0,a3⟩:=z0 (by rw[G];simpa using I (zd (·+U) (zMC (yq t (c*s) O))):U∈(z2 f).image o)
 have hsl':∀ i:Fin N,∃ u∈z2 f,o u=t.step i+U:=λ i=>by
  have aw:1<=d.hi i:=(by dsimp[d,z3,rS];rw[le_floor];have:=zy (ab i);push_cast at this ⊢;nlinarith)
  have ax:single i (1:ℤ)∈z5 d:=zc λ j=>by have hC:=(yq t (c*s) O).2 j;dsimp[cB];by_cases e:j=i;subst e;simp only[single_eq_same];exact ⟨by linarith[hC.1],aw⟩;simp only[single_eq_of_ne e];exact hC
  exact z0 (by rw[G];exact I (zd (·+U) (zh ⟨single i 1,ax,by simp only[eval,z3,rS,zero_add];rw[sum_eq_single_of_mem i (mem_univ i) λ j _ h=>by simp[single_eq_of_ne h]];simp⟩)))
 choose us b2 ag using hsl';let q i:=us i-p
 have am:∀ i,o (q i)=t.step i:=λ i=>by dsimp[q];rw[map_sub,ag i,a3,add_sub_cancel_right]
 have ay:∀ i j,|q i j| <=2*(s:ℤ)*n:=λ i j=>by dsimp[q];linarith[abs_sub (us i j) (p j),r (us i) (b2 i) j,r p a0 j]
 let P:GAP (ZV b) N:=⟨0,q,t.lo,t.hi,t.hle⟩;have ai:P.iS:=⟨rfl,l.2⟩;have aj:=ze ai;let R:=z3 P (c*s) aj
 have X:∀ v,o (P.eval v)=t.eval v:=λ v=>by simp only[eval,P,l.1,zero_add,map_sum];exact sum_congr rfl λ i _=>by rw[map_zsmul,am i]
 have af:∀ i,d.hi i<=((2*s*n+1:ℕ):ℤ)^b:=by
  have K:d.vol<=(2*s*n+1)^b:=by
   have h1:d.vol=#(d.tF.image (·+U)):=(by rw[yn,cEV ac])
   have h2:z2 f⊆(ZB.symm λ _=>s*n).tF:=λ u hu=>zc λ j=>abs_le.mp (r u hu j)
   have h3:#(ZB.symm (λ _:Fin b=>s*n)).tF=(2*s*n+1)^b:=(by rw[cTF];unfold ZB.vol ZB.symm ZB.width;simp only[prod_const,card_univ,Fintype.card_fin,show (((s*n:ℕ):ℤ) - -((s*n:ℕ):ℤ)+1).toNat=2*s*n+1 by have:2*s*n=2*(s*n):=(by ring);omega])
   rw[h1];exact (z6 I).trans ((by rw[<-G]:#(z2 M)=#((z2 f).image o)).trans_le (card_image_le.trans ((z6 h2).trans_eq h3)))
  intro i;have hw:=(wj d.cB i).trans K;have hC:=(yq t (c*s) O).2 i;change d.lo i<=0/\ 0<=d.hi i at hC;dsimp[GAP.width,cB,ZB.width] at hw;exact_mod_cast (by omega:d.hi i<=((2*s*n+1)^b:ℕ))
 have a8:∀ v∈z5 R,∀ j,|P.eval v j| <=(N:ℤ)*((2*s*n+1:ℕ):ℤ)^b*(2*(s:ℤ)*n):=λ v K j=>by
  have hS:=yr t (c*s) l;rw[show P.eval v j=∑ i,v i*q i j by simp only[eval,P,zero_add,Finset.sum_apply,Pi.smul_apply,smul_eq_mul]]
  exact (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (g:=λ _=>((2*s*n+1:ℕ):ℤ)^b*(2*(s:ℤ)*n)) λ i _=>by rw[abs_mul];have a9:=zb K i;dsimp[cB,R,z3,rS,P] at a9;have hs:=hS.2 i;dsimp[z3,rS] at hs;rw[hs] at a9;exact mul_le_mul ((abs_le.mpr a9).trans (af i)) (ay i j) (abs_nonneg _) (by positivity)).trans_eq (by simp;ring))
 have an:z5 P⊆z5 R:=Subset.trans (λ w hw=>by simpa[z5,mTF,cB,W,nS] using hw) (xj P aj (k:=1) (by simpa using (by linarith:(1:Y)<=c*s)))
 have aa:E⊆P.tF:=λ a D=>by rcases z0 (aq (zg D).2) with ⟨v,K,he⟩;exact zh ⟨v,K,xo ah (λ j=>by have:=a8 v (an K) j;have:(0:ℤ)<=(s:ℤ)*n:=(by positivity);linarith) (au a (Q (C D))) (by rw[X v,he])⟩
 have az:R.iP:=λ u hu v K e=>ac hu K (by have h1:=congrArg o e;have h':∀ w,o (R.eval w)=d.eval w:=λ w=>(by rw[show R.eval w=P.eval w from rfl,X w];dsimp[d,z3,rS,eval];rw[l.1]);rwa[h' u,h' v] at h1)
 have ao:R.tF.image (·+p)⊆z2 f:=λ y hy=>by
  rcases z0 hy with ⟨_,b0,rfl⟩;rcases z0 b0 with ⟨v,K,rfl⟩;rw[show R.eval v=P.eval v from rfl]
  obtain⟨z,hz,ar⟩:=z0 (by rw[G,map_add,X v,a3];exact I (zd (·+U) (zh ⟨v,K,by simp[eval,rS,l.1]⟩)):o (P.eval v+p)∈(z2 f).image o)
  rwa[xo ah (λ j=>by simp only[Pi.add_apply];linarith[abs_add_le (P.eval v j) (p j),a8 v K j,r p a0 j]) (λ j=>by have:(0:ℤ)<=(N:ℤ)*((2*s*n+1:ℕ):ℤ)^b*(2*(s:ℤ)*n):=(by positivity);linarith[r z hz j]) ar.symm]
 have ap:p∈zf (Set.range P.step):=by rcases z0 a0 with ⟨T,hT,b1⟩;rw[<-b1];exact sum_mem _ λ a D=>by rcases z0 (aa (J (yf hT D))) with ⟨v,_,rfl⟩;simp only[eval,P,zero_add];exact sum_mem _ λ i _=>zsmul_mem (subset_closure (Set.mem_range_self i)) _
 exact ⟨E,f,P,p,ai,C,ae,J,by rw[a7];exact a2,ab,aa,ap,az,ao⟩
theorem cst (hBox:LEH) (hNR:LNH) (hBilu:LBH):CSH:=by
 intro b I β b1;let f:=2*b+5;let o:=(β+1)*((f*b:ℕ):Y)+1
 have S:1< o:=(by have:=zk (Nat.mul_pos (show 0< f by dsimp[f];omega) I);dsimp[o];nlinarith)
 obtain⟨c,dm,M1,hc,am,a4,J,an⟩:=va hBox hNR hBilu o S
 let p:=max M1 (max (128^4) (max (⌈exp c⁻¹⌉₊+2) (max (⌈(2/c)^2⌉₊+2) (2*dm+4))))
 have ⟨hm0M,hm0128,hm0e,hm02c,hm0d⟩:M1<=p/\ 128^4<=p/\ ⌈exp c⁻¹⌉₊+2<=p/\ ⌈(2/c)^2⌉₊+2<=p/\ 2*dm+4<=p:=by simp only[p,le_max_iff,le_refl,true_or,or_true,and_self]
 clear_value p
 refine ⟨c,dm,p,hc,am,a4,J.trans hm0M,λ B A au u O av=>?_⟩
 let m:=#A;let s:=⌊(m:Y)/(log m)^2⌋₊;have v:=(J.trans hm0M).trans O;have d:=zl m
 have aw:=xs v;have l:0< log m:=(by linarith);have w:(s:Y)<=(m:Y)/(log m)^2:=Nat.floor_le (by positivity)
 have C:(m:Y)^(1/2:Y)<=s:=by
  have ae:(log m)^2<=64*(m:Y)^(1/4:Y):=(pow_le_pow_left₀ l.le ((wn d (by norm_num:(0:Y)< 1/8)).trans_eq (by ring:(m:Y)^(1/8:Y)/(1/8)=8*(m:Y)^(1/8:Y))) 2).trans_eq (by rw[mul_pow,<-rpow_natCast ((m:Y)^(1/8:Y)),<-rpow_mul d.le];norm_num)
  have af:(128:Y)<=(m:Y)^(1/4:Y):=(by have i:=rpow_le_rpow (by positivity) (by rw[show (4:Y)=((4:ℕ):Y) by norm_num,rpow_natCast];exact_mod_cast hm0128.trans O:(128:Y)^(4:Y)<=m) (by norm_num:(0:Y)<=1/4);rw[<-rpow_mul (by norm_num)] at i;norm_num at i;exact i)
  have hd:(m:Y)^(1/2:Y)+1<=(m:Y)/(log m)^2:=(by have i:=div_le_div_of_nonneg_left d.le (sq_pos_of_pos l) ae;have h2:(m:Y)/(64*(m:Y)^(1/4:Y))=(m:Y)^(1/4:Y)/64*(m:Y)^(1/2:Y):=(by rw[div_eq_iff (by positivity),show (m:Y)^(1/4:Y)/64*(m:Y)^(1/2:Y)*(64*(m:Y)^(1/4:Y))=(m:Y)^(1/4:Y)*(m:Y)^(1/4:Y)*(m:Y)^(1/2:Y) by ring,<-rpow_add d,<-rpow_add d,show (1/4:Y)+1/4+1/2=1 by norm_num,rpow_one]);have:=one_le_rpow (zx m) (by norm_num:(0:Y)<=1/2);nlinarith only[i,h2,af,this])
  linarith[lt_floor_add_one ((m:Y)/(log m)^2)]
 have T:(s:Y)<=c*m/log m:=(by have ag:c⁻¹<=log m:=(log_exp _).symm.trans_le (log_le_log (exp_pos _) ((le_ceil _).trans (Z (by omega))));have hi:1/log m<=c:=(div_le_iff₀ l).mpr (by have:=za ag hc.le;rwa[mul_inv_cancel₀ hc.ne'] at this);calc (s:Y)<=(m:Y)/(log m)^2:=w
  _=(1/log m)*(m/log m):=by ring
  _<=c*(m/log m):=by gcongr
  _=c*m/log m:=by ring)
 have U:(2:Y)<=c*s:=(by have i:=rpow_le_rpow (by positivity) ((le_ceil _).trans (Z (by omega)):(2/c)^2<=m) (by norm_num:(0:Y)<=1/2);rw[<-rpow_natCast (2/c),<-rpow_mul (by positivity)] at i;norm_num at i;linarith[(div_le_iff₀ hc).mp (i.trans C)])
 have ah:s<=m:=(by exact_mod_cast w.trans (div_le_self d.le (by nlinarith:(1:Y)<=(log m)^2)))
 let n:=B.vol;have Q:m<=n:=(by have:=z6 u;rwa[cTF] at this);have ai:=ah.trans Q;have ay:=v.trans Q
 have D:∀ x∈B.tF,∀ j,|x j| <=n:=λ x t j=>by have:=zb t j;have:=zb au j;have:=wj B j;dsimp[ZB.width] at*;rw[abs_le];omega
 let H:=(2*n+2)^f;have R:2<=H:=(by omega:2<=2*n+2).trans (Nat.le_self_pow (by dsimp[f];omega) _);let q:=H^b;let X:=yd b H
 have E:∀ x∈B.tF,∀ j,2*|x j| < H:=λ x t j=>by have:=D x t j;have:(2*(n:ℤ)+2)<=H:=(by exact_mod_cast Nat.le_self_pow (by dsimp[f];omega) (2*n+2));linarith
 have G:InjOn X (B.tF:Set (ZV b)):=λ x t y hy e=>xo R (E x t) (E y hy) e
 have a0:∀ x∈B.tF,X x∈zi q:=λ x t=>by
  rw[mem_Icc,<-abs_le];change |∑ j:Fin b,(H:ℤ)^(j:ℕ)*x j| <=q
  have K:(b:ℤ)*n<=H:=(by exact_mod_cast ((Nat.mul_le_mul (lt_two_pow_self.le.trans (Nat.pow_le_pow_left (by omega:2<=2*n+2) b)) (by rw[pow_one];omega:n<=(2*n+2)^1)).trans ((pow_add _ _ _).symm.trans_le (Nat.pow_le_pow_right (by omega:0< 2*n+2) (by dsimp[f];omega)))))
  have i:|∑ j:Fin b,(H:ℤ)^(j:ℕ)*x j| <=(H:ℤ)^(b-1)*((b:ℤ)*n):=((abs_sum_le_sum_abs _ _).trans (sum_le_sum λ j _=>by rw[abs_mul,abs_of_nonneg (pow_nonneg (z7 H) _)];exact ye (D x t j) (pow_nonneg (z7 H) _))).trans ((sum_le_sum (g:=λ _:Fin b=>(H:ℤ)^(b-1)*n) λ j _=>y7 (pow_le_pow_right₀ (by exact_mod_cast (by omega:1<=H)) (by have:=j.isLt;omega)) (z7 n)).trans_eq (by simp;ring))
  exact i.trans ((ye K (pow_nonneg (z7 H) _)).trans_eq (by dsimp[q];rw[<-pow_succ,Nat.sub_add_cancel I]))
 let A0:=A.image X;have k:#A0=m:=card_image_of_injOn (G.mono (coe_subset.mpr u))
 have a1:A0⊆zi q:=λ z hz=>by rcases z0 hz with ⟨a,ha,rfl⟩;exact a0 a (u ha)
 have a2:(q:Y)<=(m:Y)^o:=by
  have aj:2*(n:Y)+2<=(m:Y)^(β+1):=(by have:=zx n;have a3:(4:Y)<=m:=(by exact_mod_cast v);exact (by linarith:2*(n:Y)+2<=4*n).trans ((y6 a3 av).trans_eq (by dsimp[m];rw[rpow_add d,rpow_one,mul_comm])))
  rw[show (q:Y)=(2*(n:Y)+2)^(f*b) by dsimp[q,H];rw[<-pow_mul];push_cast;rfl]
  exact ((pow_le_pow_left₀ (by positivity) aj _).trans_eq (by rw[<-rpow_natCast,<-rpow_mul d.le])).trans (rpow_le_rpow_of_exponent_le (zx m) (by dsimp[o];linarith))
 obtain⟨r,ao,ap,b2,b3,P0,x0,a5,a6,a7,M⟩:=an q s A0 a1 (by rw[k];exact hm0M.trans O) (by rw[k];exact a2) (by rw[k];exact C) (by rw[k];exact T)
 have ak:2*((r:ℤ)*((2*s*n+1:ℕ):ℤ)^b*(2*(s:ℤ)*n)+(s:ℤ)*n)< H:=by
  have ax:=y2 n ai;have L:2*s*n+1<=(2*n+2)^2:=(by nlinarith)
  have az:r*(2*s*n+1)^b*(2*s*n)<=(2*n+2)^(2*b+3):=((Nat.mul_le_mul (Nat.mul_le_mul (by have:=hm0d.trans O;omega:r<=2*n+2) (Nat.pow_le_pow_left L b)) (by nlinarith:2*s*n<=(2*n+2)^2)).trans_eq (by rw[<-pow_mul];ring))
  have b0:s*n<=(2*n+2)^(2*b+3):=(by nlinarith:s*n<=(2*n+2)^2).trans (Nat.pow_le_pow_right (by omega:0< 2*n+2) (by omega))
  have al:4*(2*n+2)^(2*b+3)< (2*n+2)^f:=((Nat.mul_lt_mul_of_pos_right (by nlinarith:4< (2*n+2)^2) (Nat.pow_pos (by omega:0< 2*n+2))).trans_eq (by rw[<-pow_add,show 2+(2*b+3)=f by dsimp[f];omega]))
  have hle:2*(r*(2*s*n+1)^b*(2*s*n)+s*n)< H:=(by omega:2*(r*(2*s*n+1)^b*(2*s*n)+s*n)<=4*(2*n+2)^(2*b+3)).trans_lt al
  rw[show 2*((r:ℤ)*((2*s*n+1:ℕ):ℤ)^b*(2*(s:ℤ)*n)+(s:ℤ)*n)=((2*(r*(2*s*n+1)^b*(2*s*n)+s*n):ℕ):ℤ) by push_cast;ring];exact Int.ofNat_lt.mpr hle
 obtain⟨hA,A',P,q0,aq,a8,N,a9,aa,ar,ab,ac,as,ad⟩:=vb hc U R ak u D E G l w a5 a6 (by rwa[k] at a7) M
 exact ⟨r,ao,ap,hA,A',P,q0,aq,a8,N,a9,aa,ar,ab,ac,as,ad⟩
end
end M4
theorem cst (hBox:LEH) (hNR:LNH) (hBilu:LBH):CSH:=M4.cst hBox hNR hBilu
end E186
namespace E186
def DCPR {d : ℕ} (δ : ℝ) (A : Finset (RV d)) : Prop :=
  ∀ a ∈ A, ∃ u : RV d, u ≠ 0 ∧
    ((A.filter (fun x => (0 : ℝ) ≤ ∑ i : Fin d, u i * (x i - a i))).card : ℝ) ≤
      δ * (A.card : ℝ)
namespace m5
open Finset Matrix Real MeasureTheory
abbrev R:=ℝ
abbrev F:=Fin
abbrev V:=RV
abbrev S:=Finset
abbrev M:=Matrix
abbrev C:=ConvexOn
abbrev D:=ConcaveOn
abbrev Q:=@mul_le_mul_of_nonneg_left
abbrev T:=@mul_le_mul_of_nonneg_right
abbrev U:=@mem_filter
abbrev W:=@rpow_pos_of_pos
abbrev X:=@smul_eq_mul
abbrev Y:=@le_div_iff₀
abbrev Z:=@div_le_iff₀
abbrev Qh:=@Pi.smul_apply
abbrev Qi:=@two_pos
abbrev Qj:=@mul_pos
abbrev Qk:=@mul_nonneg
abbrev Ql:=@pow_le_pow_left₀
abbrev Qm:=@div_le_div_iff₀
abbrev Qn:=@rpow_le_rpow_of_exponent_ge
abbrev Qo:=@div_le_div_of_nonneg_right
abbrev Qp:=@rpow_natCast
abbrev Qq:=@div_nonneg
abbrev Qr:=@abs_le
abbrev Qs:=@lt_of_lt_of_le
abbrev Qt:=@Pi.add_apply
abbrev Qu:=@Pi.sub_apply
abbrev Qv:=@sum_le_sum
abbrev Qw:=@abs_of_pos
abbrev Qx:=@one_mul
abbrev Qy:=@Pi.single_apply
abbrev Qz:=@Nat.cast_nonneg
abbrev QA:=@add_sub_cancel_left
abbrev QB:=@mulVec_mulVec
abbrev QC:=@rpow_mul
abbrev QD:=@mul_le_mul
abbrev QE:=@pow_pos
abbrev QF:=@abs_of_nonneg
abbrev QG:=@div_pos
abbrev QH:=@mem_univ
abbrev QI:=@continuous_const
abbrev QJ:=@one_le_mul_of_one_le_of_one_le
abbrev QK:=@dotProduct_smul
abbrev QL:=@mul_pow
abbrev QM:=@pow_nonneg
abbrev QN:=@mul_assoc
abbrev QO:=@sqrt_le_sqrt
abbrev QP:=@card_le_card
abbrev QQ:=@rpow_add
abbrev QR:=@mul_one
abbrev QS:=@sum_add_distrib
abbrev QT:=@one_mulVec
abbrev QU:=@sq_nonneg
abbrev QV:=@mem_biUnion
abbrev QW:=@one_pos
abbrev QX:=@nsmul_eq_mul
abbrev QY:=@lt_of_le_of_ne
abbrev QZ:=@dotProduct_sub
abbrev xa:=@Pi.single_eq_same
abbrev xb:=@exists_max_image
abbrev xc:=@Finset.sum_apply
abbrev xd:=@lt_div_iff₀
abbrev xe:=@sqrt_pos
abbrev xf:=@sum_sub_distrib
abbrev xg:=@rpow_le_rpow_of_exponent_le
abbrev xh:=@sub_zero
abbrev xi:=@div_self
abbrev xj:=@Metric.eventually_nhds_iff
abbrev xk:=@eventually_nhdsWithin_iff
abbrev xl:=@abs_mul
abbrev xm:=@mul_div_cancel₀
abbrev xn:=@Fin.snoc_castSucc
abbrev xo:=@le_rfl
abbrev xp:=@one_le_pow₀
abbrev xq:=@mul_left_comm
abbrev xr:=@Fin.snoc_last
abbrev xs:=@one_div_le_one_div_of_le
abbrev xt:=@sum_const
abbrev xu:=@sum_congr
abbrev xv:=@continuous_apply
abbrev xw:=@mul_sum
abbrev xx:=@sub_nonneg
abbrev xy:=@nhdsWithin
abbrev xz:=@rpow_le_rpow
abbrev xA:=@zero_dotProduct
abbrev xB:=@pow_succ
abbrev xC:=@add_zero
abbrev xD:=@mulVec_smul
abbrev xE:=@div_eq_mul_inv
abbrev xF:=@Fin.castSucc_ne_last
abbrev xG:=@Nat.ceil_lt_add_one
abbrev xH:=@continuous_pi
abbrev xI:=@div_le_one
abbrev xJ:=@add_le_add
abbrev xK:=@abs_nonneg
abbrev xL:=@abs_add_le
abbrev xM:=@sub_pos
abbrev xN:=@sqrt_sq
abbrev xO:=@Set.ext
abbrev xP:=@Set.Ioi
abbrev xQ:=@rpow_one
abbrev xR:=@min_le_right
abbrev xS:=@Real.dist_eq
abbrev xT:=@Nat.floor_le
abbrev xU:=@not_le
abbrev xV:=@Fintype.card_fin
abbrev xW:=@sum_le_sum_of_subset_of_nonneg
abbrev xX:=@zero_le_one
abbrev xY:=@le_antisymm
abbrev xZ:=@le_abs_self
abbrev Xa:=@sum_filter_add_sum_filter_not
abbrev Xb:=@smul_dotProduct
abbrev Xc:=@div_pow
abbrev Xd:=@mul_rpow
abbrev Xe:=@mul_comm
abbrev Xf:=@Set.univ
abbrev Xg:=@div_lt_one
abbrev Xh:=@abs_of_neg
abbrev Xi:=@sub_eq_add_neg
abbrev Xj:=@mul_prod_erase
abbrev Xk:=@lt_of_le_of_lt
abbrev Xl:=@dotProduct_add
abbrev Xm:=@Fin.cases_succ
abbrev Xn:=@sum_eq_zero_iff_of_nonneg
abbrev Xo:=@div_le_div_of_nonneg_left
abbrev Xp:=@filter_subset
abbrev Xq:=@disjoint_left
abbrev Xr:=@add_sum_erase
abbrev Xs:=@Pi.zero_apply
abbrev Xt:=@Fin.cons_succ
abbrev Xu:=@zero_smul
abbrev Xv:=@mem_erase
abbrev Xw:=@mul_lt_mul_of_pos_right
abbrev Xx:=@div_lt_div_of_pos_right
abbrev Xy:=@Fin.exists_succAbove_eq
abbrev Xz:=@mem_coe
abbrev XA:=@abs_neg
abbrev XB:=@card_le_univ
abbrev XC:=@card_biUnion
abbrev XD:=@Nat.cast_pos
abbrev XE:=@mul_lt_mul_of_pos_left
abbrev XF:=@le_of_mul_le_mul_right
abbrev XG:=@Nat.one_le_iff_ne_zero
def E {n:ℕ}(i:F n):V n:=Pi.single i 1
def O {d:ℕ}(u:V d):R:=∑i,u i^2
noncomputable def G {d:ℕ}(u:V d):R:=√(O u)
lemma qj {d:ℕ}(u:V d):0<=G u:=sqrt_nonneg _
lemma qk {d:ℕ}(u:V d):G u^2=O u:=sq_sqrt (sum_nonneg λ_ _=>QU _)
lemma qz {d:ℕ}(u:V d):O u=0↔u=0:=⟨λh=>funext λi=>sq_eq_zero_iff.mp ((Xn λ_ _=>QU _).mp h i (QH i)),λh=>by simp[h,O]⟩
lemma qu {d:ℕ}{u:V d}(h:u≠0):0< O u:=QY (sum_nonneg λ_ _=>QU _) (Ne.symm (mt (qz u).mp h))
lemma qv {d:ℕ}(u v:V d):|u⬝ᵥv|<=G u*G v:=by
 have h:(u⬝ᵥv)^2<=(G u*G v)^2:=(by rw[QL,qk,qk];simpa[dotProduct,O] using sum_mul_sq_le_sq_mul_sq univ u v);have a:=sq_le_sq.mp h;rwa[QF (Qk (qj u) (qj v))] at a
lemma qA {d:ℕ}(u v:V d):G (u+v)<=G u+G v:=by
 have a:O (u+v)=O u+2*(u⬝ᵥv)+O v:=(by simp only[O,dotProduct,Qt];simp_rw[add_sq,QS,QN,<-xw]);have b:O (u+v)<=(G u+G v)^2:=(by rw[a,add_sq,qk,qk];linarith[(xZ _).trans (qv u v)]);exact (QO b).trans_eq (xN (add_nonneg (qj u) (qj v)))
lemma qr {d:ℕ}(c:R)(u:V d):G (c•u)=|c| *G u:=by
 have h:O (c•u)=c^2*O u:=(by simp only[O,Qh,X,QL,<-xw]);rw[G,h,sqrt_mul (QU c),sqrt_sq_eq_abs,G]
lemma qg {d:ℕ}(u:V d)(i:F d):|u i|<=G u:=by
 rw[<-sqrt_sq_eq_abs];exact QO (single_le_sum (f:=λj:F d=>u j^2) (λ_ _=>QU _) (QH i))
lemma qo {d:ℕ}{u:V d}{a:R}(b:0<=a)(h:∀i,|u i|<=a):G u<=√d*a:=by
 have c:O u<=(d:R)*a^2:=(Qv λi _=>sq_le_sq.mpr (by rw[QF b];exact h i)).trans_eq (by simp);exact (QO c).trans_eq (by rw[sqrt_mul (Qz d),xN b])
lemma qw {d:ℕ}{u:V d}(h:u≠0):O ((1/G u)•u)=1:=by
 have a:0< G u:=xe.mpr (qu h);rw[<-qk,qr,Qw (by positivity)];field_simp[a.ne']
lemma qF {d:ℕ}{g:M (F d) (F d) R}(a:gᵀ*g=1)(x y:V d):(g*ᵥx)⬝ᵥ(g*ᵥy)=x⬝ᵥy:=by
 rw[dotProduct_mulVec,<-mulVec_transpose,QB,a,QT]
lemma ql {d:ℕ}{g:M (F d) (F d) R}(a:gᵀ*g=1)(x:V d):O (g*ᵥx)=O x:=by
 simpa[O,dotProduct,sq] using qF a x x
lemma qG {d:ℕ}{g:M (F d) (F d) R}(a:gᵀ*g=1):|g.det|=1:=by
 have h:gᵀ.det*g.det=1:=(by rw[<-det_mul,a,det_one]);rw[det_transpose,<-sq] at h;rcases sq_eq_one_iff.mp h with h | h<;>simp[h]
lemma qx {d:ℕ}{g:M (F d) (F d) R}(a:gᵀ*g=1):g*gᵀ=1:=by
 have b:IsUnit g.det:=isUnit_iff_ne_zero.mpr λc=>(by have:=qG a;simp[c] at this);rw[<-inv_eq_left_inv a];exact mul_nonsing_inv g b
lemma qB {α d:Type*}[DecidableEq α][DecidableEq d][Fintype d](c:S α)(f:α->d):∑b,(c.filter λx=>f x=b).card=c.card:=by
 rw[<-XC (λa _ b _ h=>Xq.mpr λx e g=>h ((U.mp e).2.symm.trans (U.mp g).2))];congr 1;ext x;simp only[QV,QH,true_and,U];exact⟨λ⟨_,h,_⟩=>h,λh=>⟨f x,h,rfl⟩⟩
lemma qH {α c:Type*}[DecidableEq α][DecidableEq c][Fintype c][Nonempty c](a:S α)(f:α->c):∃b,a.card<=Fintype.card c*(a.filter λx=>f x=b).card:=by
 obtain⟨b,_,d⟩:=xb univ (λb=>(a.filter λx=>f x=b).card) univ_nonempty;exact⟨b,by rw[<-qB a f];exact (Qv λq e=>d q e).trans (by simp)⟩
lemma qI {n:ℕ}(v:V (n+1))(l:O v=1):∃g:M (F (n+1)) (F (n+1)) R,gᵀ*g=1/\g*ᵥv=E (Fin.last n):=by
 let e:V (n+1):=E (Fin.last n);have m:O e=1:=by simp[O,e,E,Qy]
 by_cases a:v=e
 · exact⟨1,by simp,by rw[a,QT]⟩
 · let w:=v-e;let s:=O w;have h:s≠0:=(qu (sub_ne_zero.mpr a)).ne';let g:M (F (n+1)) (F (n+1)) R:=of λi j=>(if i=j then (1:R) else 0)-2/s*w i*w j;have b:gᵀ=g:=(by ext i j;simp only[g,transpose_apply,of_apply,eq_comm];ring);have c:gᵀ*g=1:=by
    rw[b];ext i j;simp only[mul_apply,one_apply,g,of_apply];have d:∀k:F (n+1),((if i=k then (1:R) else 0)-2/s*w i*w k)*
        ((if k=j then (1:R) else 0)-2/s*w k*w j)=
        (if i=k then (if k=j then (1:R) else 0) else 0)-(if i=k then 2/s*w k*w j else 0) -
        (if k=j then 2/s*w i*w k else 0)+4/s^2*w i*w j*w k^2:=λk=>by split_ifs<;>ring
    simp_rw[d,QS,xf,<-xw];simp only[sum_ite_eq,sum_ite_eq',QH,↓reduceIte];change (if i=j then (1:R) else 0)-2/s*w i*w j-2/s*w i*w j+4/s^2*w i*w j*s=_;field_simp[h];ring
   have o:2*(w⬝ᵥv)=s:=(by have p:s=O v-2*(v⬝ᵥe)+O e:=(by simp only[s,O,dotProduct,w,Qu];simp_rw[sub_sq,QS,xf,QN,<-xw]);have q:w⬝ᵥv=O v-v⬝ᵥe:=(by rw[sub_dotProduct,dotProduct_comm e v];simp[O,dotProduct,sq]);rw[p,q,l,m];ring);have f:g*ᵥv=e:=by
    ext i;simp only[mulVec,dotProduct,g,of_apply];have d:∀j:F (n+1),((if i=j then (1:R) else 0)-2/s*w i*w j)*v j=
        (if i=j then v j else 0)-2/s*w i*(w j*v j):=λj=>by split_ifs<;>ring
    simp_rw[d,xf,<-xw];simp only[sum_ite_eq,QH,↓reduceIte];change v i-2/s*w i*(w⬝ᵥv)=e i;have r:2/s*(w⬝ᵥv)=1:=(by field_simp[h];linarith);rw[show v i-2/s*w i*(w⬝ᵥv)=v i-w i*(2/s*(w⬝ᵥv)) by ring,r];simp[w]
   exact⟨g,c,f⟩
lemma qU {d:ℕ}(a b:V d)(c:∀i,a i<=b i):volume {x:V d | ∀i,a i<=x i/\x i<=b i}=ENNReal.ofReal (∏i,(b i-a i)):=by
 rw[show {x:V d | ∀i,a i<=x i/\x i<=b i}=Xf.pi λi=>Set.Icc (a i) (b i) from xO λx=>⟨λh i _=>h i,λh i=>h i trivial⟩,volume_pi_pi];simp_rw[volume_Icc];rw[ENNReal.ofReal_prod_of_nonneg λi _=>xx.mpr (c i)]
lemma qs {x a:R}(h:0< x):x^a*x^(-a)=1:=by rw[<-QQ h,add_neg_cancel,rpow_zero]
lemma qJ {x a:R}(h:0< x):x*x^a=x^(1+a):=by rw[QQ h,xQ]
lemma qb {n:ℕ}(h:1<=n):(0:R)< n:=by exact_mod_cast (by omega:0< n)
lemma qC {n:ℕ}(h:1<=n):(1:R)<=n:=by exact_mod_cast h
lemma qK {d:ℕ}{x y a:V d}{s t:R}(h:s+t=1):s•x+t•y-a=s•(x-a)+t•(y-a):=funext λj=>by simp only[Qu,Qt,Qh,X];linear_combination a j*h
noncomputable def qd {n:ℕ}(u:R)(m:ℕ)(v:F n->F (2*m)):V n:=λj=>-u+(((v j:ℕ):R)+1/2)*(u/m)
open Classical in abbrev qD (n:ℕ)(b c a:R)(A:S (V (n+1))):Prop:=∃(η:R) (x₀:V (n+1)) (K₀:Set (V (n+1))),a<=η/\η<=a^c/\0∈K₀/\Convex R K₀/\(∀x∈K₀,-x∈K₀)/\Bornology.IsBounded K₀/\(∀x,(∀i,|x i|<=1*a^((1:R)/((n+1:ℕ):R)))->x∈K₀)/\volume K₀<=ENNReal.ofReal (η*2^(n+1))/\((A.filter λx=>x-x₀∈K₀).card:R)>=η^((n:R)/((n:R)+2)+b)*A.card
lemma qV {n:ℕ}{H:V n->R}(w:C R {x:V n | ∀i,-(1/2:R)< x i/\x i< 3/2} H){e:V n}(g:∀i,-(1/2:R)< e i/\e i< 3/2):∃u:V n,∀y:V n,(∀i,-(1/2:R)< y i/\y i< 3/2)->H e+u⬝ᵥ(y-e)<=H y:=by
 let c:={x:V n | ∀i,-(1/2:R)< x i/\x i< 3/2};let d:Set (V n×R):={p | p.1∈c/\H p.1< p.2};have A:Convex R d:=by
  rintro⟨P,a0⟩ ⟨m,g1⟩ ⟨a1,a2⟩ ⟨h2,g2⟩ a b J k v;refine⟨w.1 m h2 J k v,Xk (w.2 m h2 J k v) ?_⟩;simp only[Prod.snd_add,Prod.smul_snd,X]
  by_cases r:a=0
  · subst r;have:b=1:=(by linarith);subst this;simpa using g2
  · linarith[XE g1 (QY J (Ne.symm r)),Q g2.le k]
 have K:IsOpen c:=(show c=Xf.pi λ_=>Set.Ioo (-(1/2:R)) (3/2) from xO λ_=>by simp[c])▸isOpen_set_pi Set.finite_univ λ_ _=>isOpen_Ioo;have B:IsOpen d:=
  (show d=(Prod.fst ⁻¹'c)∩(λp:V n×R=>p.2-H p.1) ⁻¹'xP 0 from xO λ⟨_,_⟩=>by simp[d])▸
   (continuous_snd.continuousOn.sub ((w.continuousOn K).comp continuous_fst.continuousOn λ_ h=>h)).isOpen_inter_preimage (K.preimage continuous_fst) isOpen_Ioi
 obtain⟨f,N⟩:=geometric_hahn_banach_open_point A B (show (e,H e) ∉ d from λh=>lt_irrefl _ h.2);let l:=f (0,1);have o:l< 0:=(by have m:=N (e,H e+1) ⟨g,by linarith⟩;rw[show (e,H e+1)=(e,H e)+(0,1) by ext<;>simp,map_add] at m;linarith);let u:V n:=λi=>-f (E i,0)/l;refine⟨u,λy hy=>?_⟩;have L:∀z:V n,f (z,0)=(-l)*(u⬝ᵥz):=λz=>by
  have m:(z,(0:R))=∑i,z i•(E i,(0:R)):=
   Prod.ext (by rw[Prod.fst_sum];ext j;simp[E,Qy]) (by rw[Prod.snd_sum];simp)
  rw[m,map_sum];simp_rw[map_smul,X];simp only[dotProduct,xw];exact xu rfl λi _=>by simp only[u];field_simp[o.ne]
 apply le_of_forall_pos_le_add;intro s hs;have I:=N (y,H y+s) ⟨hy,by linarith⟩;have q:∀(z:V n) (t:R),f (z,t)=f (z,0)+t*l:=λz t=>(by rw[show (z,t)=(z,0)+t•((0:V n),(1:R)) by ext<;>simp,map_add,map_smul,X]);rw[q y,q e,L y,L e] at I;have hm:(-l)*(u⬝ᵥ(y-e))< (-l)*(H y+s-H e):=(by rw[QZ];linarith);linarith[lt_of_mul_lt_mul_left hm (neg_pos.mpr o).le]
lemma qL {n:ℕ}{a:Set (V n)}{H:V n->R}(m:C R a H){x:V n}{i:F n}{t₁ t₂ t₃:R}(d:t₁< t₂)(e:t₂< t₃)(f:x+t₁•E i∈a)(g:x+t₃•E i∈a):(H (x+t₂•E i)-H (x+t₁•E i))/(t₂ - t₁)<=(H (x+t₃•E i)-H (x+t₂•E i))/(t₃ - t₂):=by
 have k:0< t₂ - t₁:=xM.mpr d;have l:0< t₃ - t₂:=xM.mpr e;have c:0< t₃ - t₁:=(by linarith);have h:x+t₂•E i=((t₃ - t₂)/(t₃ - t₁))•(x+t₁•E i)+((t₂ - t₁)/(t₃ - t₁))•(x+t₃•E i):=(by ext j;simp only[Qt,Qh,X];field_simp[c.ne'];ring);have b:=m.2 f g (Qq l.le c.le) (Qq k.le c.le) (by field_simp[c.ne'];ring);rw[<-h] at b;simp only[X] at b;rw[Qm k l];have o:=Q b c.le
 rw[show (t₃ - t₁)*((t₃ - t₂)/(t₃ - t₁)*H (x+t₁•E i)+(t₂ - t₁)/(t₃ - t₁)*H (x+t₃•E i))=
   (t₃ - t₂)*H (x+t₁•E i)+(t₂ - t₁)*H (x+t₃•E i) by field_simp[c.ne']] at o
 nlinarith
lemma qW (k m:ℕ)(hm:4*(k+2)< m)(H:V (k+1)->R)(a5:C R {x:V (k+1) | ∀i,-(1/2:R)< x i/\x i< 3/2} H)(hb:∀x,(∀i,-(1/2:R)< x i/\x i< 3/2)->0<=H x/\H x<=1)(I:S (F (k+1)->F m))(hI:I.Nonempty):∃v∈I,∃(a:V (k+1)) (b:R),∀x:V (k+1),(∀i,((v i:ℕ):R)/m<=x i/\x i<=(((v i:ℕ)+1:ℕ):R)/m)->|H x-(b+a⬝ᵥx)|<=32*((k+2:ℕ):R)^4*(m:R)^k/(m*I.card):=by
 classical
 let c:={x:V (k+1) | ∀i,-(1/2:R)< x i/\x i< 3/2};let d:R:=(k+2:ℕ);let e:R:=m;have w:0< e:=qb (by omega);have b2:0< d:=qb (by omega);have f5:d/e< 1/4:=(by rw[div_lt_iff₀ w];have:4*d< e:=(by dsimp[d,e];exact_mod_cast hm);linarith);have d6:(0:R)< I.card:=(by exact_mod_cast hI.card_pos);let z:=32*d^4*e^k/(e*I.card);have b9:0< z:=(by positivity);by_contra d4;push Not at d4;let n:(F (k+1)->F m)->V (k+1):=λv j=>((v j:ℕ):R)/e;have a6:∀v j,0<=n v j/\n v j< 1:=λv j=>
  ⟨Qq (Qz _) w.le,(Xg w).mpr (by dsimp[e];exact_mod_cast (v j).isLt)⟩
 have hU:∀v,n v∈c:=λv j=>⟨by linarith[(a6 v j).1],by linarith[(a6 v j).2]⟩;have P:∀v i {t:R},-(1/4:R)<=t->t< 1/2->n v+t•E i∈c:=λv i t g2 g3 j=>by
  by_cases h:j=i
  · subst h;simp only[Qt,Qh,X,E,xa,QR];exact⟨by linarith[(a6 v j).1],by linarith[(a6 v j).2]⟩
  · simpa[E,Qy,h] using hU v j
 choose u b7 using λv=>qV a5 (hU v);have d7:∀v∈I,∃i:F (k+1),∃s:R,0< s/\s<=d/e/\u v i+z*e/d< (H (n v+s•E i)-H (n v))/s:=by
  intro v hv;obtain⟨y,a7,d1⟩:=d4 v hv (u v) (H (n v)-u v⬝ᵥn v);have d8:y∈c:=λj=>⟨by linarith[Qq (Qz (v j:ℕ)) w.le,(a7 j).1],by linarith[(xI w).mpr (by dsimp[e];exact_mod_cast (v j).isLt:(((v j:ℕ)+1:ℕ):R)<=e),(a7 j).2]⟩;have c0:H (n v)-u v⬝ᵥn v+u v⬝ᵥy=H (n v)+u v⬝ᵥ(y-n v):=(by rw[QZ];ring);have c1:H (n v)+u v⬝ᵥ(y-n v)+z< H y:=(by rw[QF (xx.mpr (c0▸b7 v y d8)),c0] at d1;linarith);let A:F (k+1)->R:=λj=>y j-n v j;have a0:∀j,0<=A j:=λj=>xx.mpr (a7 j).1;have c2:∀j,A j<=1/e:=λj=>(by have:=(a7 j).2;simp only[A,n];have:(((v j:ℕ)+1:ℕ):R)/e-((v j:ℕ):R)/e=1/e:=(by push_cast;ring);linarith);let s:=∑j,A j;have q:0< s:=(by by_contra d5;push Not at d5;have hy:y=n v:=funext λj=>(by linarith[(Xn λr _=>a0 r).mp (xY d5 (sum_nonneg λr _=>a0 r)) j (QH j)]);subst hy;simp only[sub_self,dotProduct_zero,xC] at c1;linarith);have L:s<=d/e:=(Qv λj _=>c2 j).trans (by simp only[xt,card_univ,xV,QX,mul_one_div];exact Qo (by dsimp[d];exact_mod_cast (by omega:k+1<=k+2)) w.le);have b3:∑j:F (k+1),A j/s=1:=(by rw[<-sum_div];exact xi q.ne');have d9:y=∑j,(A j/s)•(n v+s•E j):=funext λr=>by
   simp only[xc,Qh,Qt,X,E,Qy];have ht:∀j:F (k+1),A j/s*(n v r+s*if r=j then 1 else 0)=A j/s*n v r+if j=r then A j else 0:=λj=>by
    by_cases h:j=r
    · subst h;simp;field_simp[q.ne']
    · simp[h,Ne.symm h]
   simp_rw[ht,QS,<-sum_mul,b3,Qx];simp only[sum_ite_eq',QH,↓reduceIte,A];ring
  have e0:H y<=∑j,(A j/s)*H (n v+s•E j):=(by rw[d9];simpa[X] using a5.map_sum_le (λj _=>Qq (a0 j) q.le) b3 (λj _=>P v j (by linarith) (by linarith)));have e1:H (n v)+u v⬝ᵥA+z=∑j,(A j/s)*(H (n v)+s*u v j+z):=(by have ht:∀j,(A j/s)*(H (n v)+s*u v j+z)=(A j/s)*(H (n v)+z)+u v j*A j:=λj=>(by field_simp[q.ne'];ring);simp_rw[ht,QS,<-sum_mul,b3,Qx];simp[dotProduct];ring);obtain⟨i,hi⟩:∃i,H (n v)+s*u v i+z< H (n v+s•E i):=(by by_contra b1;push Not at b1;have h1:∑j:F (k+1),(A j/s)*H (n v+s•E j)<=∑j:F (k+1),(A j/s)*(H (n v)+s*u v j+z):=Qv λj _=>Q (b1 j) (Qq (a0 j) q.le);have c3:H (n v)+u v⬝ᵥA+z< H y:=c1;linarith only[e0,h1,e1,c3]);refine⟨i,s,q,L,?_⟩;have h1:u v i+z/s< (H (n v+s•E i)-H (n v))/s:=(by rw[xd q];have:(u v i+z/s)*s=s*u v i+z:=(by field_simp[q.ne']);linarith);have h2:z*e/d<=z/s:=(by rw[Qm b2 q];nlinarith[(Y w).mp L]);linarith
 choose b8 sv q L d2 using d7;let b4:(F (k+1)->F m)->F (k+1)×(F k->F m)×F (k+3):=λv=>
  if hv:v∈I then let i:=b8 v hv;(i,λj=>v (i.succAbove j),⟨(v i).val % (k+3),Nat.mod_lt _ (by omega)⟩) else (0,λ_=>⟨0,by omega⟩,0)
 have:Nonempty (F (k+1)×(F k->F m)×F (k+3)):=⟨(0,λ_=>⟨0,by omega⟩,0)⟩;obtain⟨p,hp⟩:=qH I b4;let f:=I.filter λv=>b4 v=p;have a8:I.card<=((k+2)^2*m^k)*f.card:=(by rw[show Fintype.card (F (k+1)×(F k->F m)×F (k+3))=(k+1)*(k+3)*m^k by simp[Fintype.card_prod];ring] at hp;exact hp.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by nlinarith))));have c4:0< f.card:=(by by_contra h0;have:f.card=0:=(by omega);rw[this,mul_zero] at a8;have:=hI.card_pos;omega);let i:=p.1;have N:∀v∈f,∃hv:v∈I,b8 v hv=i/\(∀j:F k,v (i.succAbove j)=p.2.1 j)/\(v i).val % (k+3)=p.2.2.val:=λv f0=>(by obtain⟨b6,hk⟩:=U.mp f0;simp only[b4,dif_pos b6] at hk;have h1:b8 v b6=i:=congrArg Prod.fst hk;have h2:=congrArg (λx=>x.2.1) hk;have h3:=congrArg (λx=>x.2.2.val) hk;rw[h1] at h2 h3;exact⟨b6,h1,λj=>congrFun h2 j,h3⟩);have a9:∀g∈f,∀l∈f,∀j,j≠i->g j=l j:=λg h1 l h2 j f1=>(by obtain⟨r,rfl⟩:=Xy f1;obtain⟨_,_,w1,_⟩:=N g h1;obtain⟨_,_,w2,_⟩:=N l h2;exact (w1 r).trans (w2 r).symm);let B:=f.image λv=>(v i).val;have c5:B.card=f.card:=card_image_of_injOn λg h1 l h2 f2=>funext λj=>if h:j=i then h▸Fin.ext f2 else a9 g h1 l h2 j h;choose a2 a4 d3 using λr:F f.card=>mem_image.mp (orderEmbOfFin_mem B c5 r);have c6:∀r:ℕ,(hr:r< f.card)->u (a2 ⟨0,c4⟩) i+(r:R)*(z*e/d)<=u (a2 ⟨r,hr⟩) i:=by
  intro r;induction r with
  | zero=>intro _;simp
  | succ r ih=>
    intro hr;have h1:=ih (by omega);let g:=a2 ⟨r,by omega⟩;let l:=a2 ⟨r+1,hr⟩;obtain⟨a1,e6,_,e7⟩:=N g (a4 ⟨r,by omega⟩);obtain⟨_,_,_,e8⟩:=N l (a4 ⟨r+1,hr⟩);have f6:(g i).val< (l i).val:=(by rw[d3 ⟨r,by omega⟩,d3 ⟨r+1,hr⟩];exact (B.orderEmbOfFin c5).strictMono (Fin.mk_lt_mk.mpr (Nat.lt_succ_self r)));have c7:(g i).val+(k+3)<=(l i).val:=(by have e2:=Nat.div_add_mod (g i).val (k+3);have e3:=Nat.div_add_mod (l i).val (k+3);rw[e7] at e2;rw[e8] at e3;have hq:(g i).val/(k+3)+1<=(l i).val/(k+3):=(by by_contra h;nlinarith);nlinarith);let s1:=sv g a1;let t:R:=(((l i).val:R)-((g i).val:R))/e;have c8:s1< t:=Xk (L g a1) (Xx (by have:((g i).val:R)+((k+3:ℕ):R)<=(l i).val:=(by exact_mod_cast c7);dsimp[d];push_cast at this ⊢;linarith) w);have b5:n g+t•E i=n l:=funext λj=>by
     by_cases h:j=i
     · subst h;simp only[n,Qt,Qh,X,E,xa,QR,t];ring
     · simp[n,E,h,a9 g (a4 _) l (a4 _) j h]
    have b0:=qL a5 (x:=n g) (i:=i) (t₁:=0) (t₂:=s1) (t₃:=t) (q g a1) c8 (by rw[Xu,xC];exact hU g) (b5▸hU l);simp only[Xu,xC,xh,b5] at b0;have f3:=b7 l (n g+s1•E i) (P g i (by linarith[q g a1]) (by linarith[L g a1]));have f7:u l⬝ᵥ(n g+s1•E i-n l)=-(t-s1)*u l i:=(by rw[show n g+s1•E i-n l=(-(t-s1))•E i by rw[<-b5];ext j;simp[E,Qy];split_ifs<;>ring,QK,X,show u l⬝ᵥE i=u l i by simp[E]]);have c9:(H (n l)-H (n g+s1•E i))/(t-s1)<=u l i:=(by rw[Z (xM.mpr c8)];linarith);have a3:=d2 g a1;rw[e6] at a3;dsimp[s1,g,l] at h1 b0 c9 a3;push_cast at h1 a3 ⊢;linarith
 let o:=a2 ⟨0,c4⟩;let J:=a2 ⟨f.card-1,by omega⟩;obtain⟨K,e9,_,_⟩:=N J (a4 ⟨f.card-1,by omega⟩);have f8:(-4:R)<=u o i:=(by have h1:=b7 o (n o+(-(1/4:R))•E i) (P o i xo (by norm_num));have h2:u o⬝ᵥ(n o+(-(1/4:R))•E i-n o)=-(1/4:R)*u o i:=(by rw[QA,QK,X,show u o⬝ᵥE i=u o i by simp[E]]);have:=hb (n o) (hU o);have:=hb (n o+(-(1/4:R))•E i) (P o i xo (by norm_num));linarith);let sl:=sv J K;have c9:(H (n J+sl•E i)-H (n J))/sl<=4:=(by have h1:=qL a5 (x:=n J) (i:=i) (t₁:=0) (t₂:=sl) (t₃:=sl+1/4) (q J K) (by linarith) (by rw[Xu,xC];exact hU J) (P J i (by linarith[q J K]) (by linarith[L J K]));simp only[Xu,xC,xh,QA] at h1;have:=hb (n J+sl•E i) (P J i (by linarith[q J K]) (by linarith[L J K]));have:=hb (n J+(sl+1/4)•E i) (P J i (by linarith[q J K]) (by linarith[L J K]));linarith);have f9:=c6 (f.card-1) (by omega);have d0:=d2 J K;rw[e9] at d0;have e4:((f.card-1:ℕ):R)+1=f.card:=(by exact_mod_cast (by omega:f.card-1+1=f.card));have f4:(f.card:R)*(z*e/d)< 8:=(by rw[<-e4,add_mul,Qx];linarith);have e5:(I.card:R)/(d^2*e^k)<=f.card:=(Z (by positivity)).mpr (by have:(I.card:R)<=d^2*e^k*f.card:=(by dsimp[d,e];exact_mod_cast a8);linarith);have g0:32*d<=(f.card:R)*(z*e/d):=(by have hc:(I.card:R)/(d^2*e^k)*(z*e/d)=32*d:=(by dsimp[z];rw[show (I.card:R)/(d^2*e^k)*(32*d^4*e^k/(e*I.card)*e/d)=32*d*(((I.card:R)/I.card)*(e^k/e^k)*(e/e)*(d^3/d^3)) by ring,xi d6.ne',xi (pow_ne_zero k w.ne'),xi w.ne',xi (pow_ne_zero 3 b2.ne')];ring);rw[<-hc];exact T e5 (QG (Qj b9 w) b2).le);have g1:(2:R)<=d:=(by dsimp[d];exact_mod_cast (by omega:2<=k+2));linarith
def qc {d:ℕ}(x:F (d+1)->V d):M (F (d+1)) (F (d+1)) R:=of λr k=>Fin.cases (1:R) (λi=>x k i) r
lemma qM {n:ℕ}(A:M (F n) (F n) R)(k:F n)(u v:F n->R):(A.updateCol k (u-v)).det=(A.updateCol k u).det-(A.updateCol k v).det:=by
 rw[Xi,det_updateCol_add,<-neg_one_smul R v,det_updateCol_smul];ring
lemma qX {d:ℕ}(hd:1<=d){P:Set (V d)}(c5:IsCompact P)(b1:Convex R P)(c6:P.Nonempty){w:R}(hw:0< w)(b2:∀u:V d,O u=1->∃x∈P,∃y∈P,w<=u⬝ᵥ(x-y)):∃c∈P,∀z:V d,O (z-c)<=(w/(2*((d:R)+1)))^2->z∈P:=by
 obtain⟨m,K⟩:=c6;let f:(F (d+1)->V d)->R:=λx=>|(qc x).det|
 have c7:Continuous f:=(Continuous.matrix_det (xH λr=>xH λk=>
  Fin.cases (by simp only[qc,of_apply];exact QI)
    (λi=>by simp only[qc,of_apply];exact (xv i).comp (xv k)) r)).abs
 obtain⟨x,e2,c2⟩:=(isCompact_univ_pi λ_:F (d+1)=>c5).exists_isMaxOn ⟨λ_=>m,λ_ _=>K⟩ c7.continuousOn;have a4:∀k,x k∈P:=λk=>e2 k (Set.mem_univ k);have a0:(qc x).det≠0:=by
  intro e6;have I:∀y:F (d+1)->V d,(∀k,y k∈P)->(qc y).det=0:=λy hy=>
   abs_eq_zero.mp (xY (by simpa[f,e6] using c2 λk _=>hy k) (xK _))
  let b:={v:V d | ∃p∈P,v=p-m};let e:=Submodule.span R b
  by_cases c4:e=⊤
  · obtain⟨B,e3,e4,a6⟩:=exists_linearIndependent R b;have:Finite B:=a6.finite;let _:Fintype B:=Fintype.ofFinite B;have c8:Fintype.card B=d:=(by simpa[Module.finrank_fin_fun] using (Module.finrank_eq_card_basis (Module.Basis.mk a6 (by rw[Subtype.range_coe,e4];exact le_of_eq c4.symm))).symm);let eB:=(Fintype.equivFinOfCardEq c8).symm;choose p L a1 using λj:F d=>e3 (eB j).2;obtain⟨v,a7,c3⟩:=exists_mulVec_eq_zero_iff.mpr (I (Fin.cons m p) (Fin.cases K L));have b3:v 0=-∑j:F d,v j.succ:=by
     have h0:=congrFun c3 0;simp only[mulVec,dotProduct,qc,of_apply,Fin.sum_univ_succ,Fin.cases_zero,Qx,Xs] at h0;linarith
    have c9:∑j:F d,v j.succ•(eB j:V d)=0:=funext λi=>(by have hi:=congrFun c3 i.succ;simp only[mulVec,dotProduct,qc,of_apply,Xm,Fin.sum_univ_succ,Fin.cons_zero,Xt,Xs,b3] at hi;simp only[xc,Qh,X,Xs,a1,Qu];have:∑j:F d,v j.succ*(p j i-m i)=(∑j:F d,p j i*v j.succ)-(∑j:F d,v j.succ)*m i:=(by rw[sum_mul,<-xf];exact xu rfl λ_ _=>by ring);linarith);have b4:∀j:F d,v j.succ=0:=Fintype.linearIndependent_iff.mp (a6.comp eB eB.injective) (λj=>v j.succ) c9;exact a7 (funext λr=>Fin.cases (by simp[b3,b4]) b4 r)
  · obtain⟨l,a2⟩:=Submodule.exists_isCompl e;obtain⟨v,e5,a7⟩:=Submodule.exists_mem_ne_zero_of_ne_bot (show l≠⊥ from λh=>c4 (by have:=a2.sup_eq_top;rwa[h,sup_bot_eq] at this));have⟨n,a8⟩:∃n,v n≠0:=(by by_contra h;push Not at h;exact a7 (funext h));let pr:V d→ₗ[R] R:=(LinearMap.proj n).comp (l.subtype.comp (Submodule.projectionOnto l e a2.symm));let H:V d:=λi=>pr (E i);have a1:∀z,pr z=H⬝ᵥz:=λz=>by
     conv_lhs=>rw[show z=∑i,z i•E i by ext j;simp[E,Qy]]
     rw[map_sum];simp_rw[map_smul,X];exact xu rfl λ_ _=>by ring
    have d0:H≠0:=λh0=>a8<| by
     have h1:pr v=v n:=congrArg (λw:l=>(w:V d) n) (Submodule.projectionOnto_apply_left a2.symm ⟨v,e5⟩);rw[a1,h0,xA] at h1;exact h1.symm
    obtain⟨p,L,q,a9,b0⟩:=b2 ((1/G H)•H) (qw d0);have b5:p-q∈e:=(by rw[show p-q=(p-m)-(q-m) by ext i;simp];exact e.sub_mem (Submodule.subset_span ⟨p,L,rfl⟩) (Submodule.subset_span ⟨q,a9,rfl⟩));have b6:pr (p-q)=0:=congrArg (λw:l=>(w:V d) n) (Submodule.projectionOnto_apply_right a2.symm ⟨p-q,b5⟩);rw[Xb,X,<-a1,b6,mul_zero] at b0;linarith
 have a5:(0:R)< (d:R)+1:=(by positivity);let N:R:=1/((d:R)+1);let c:V d:=N•∑k:F (d+1),x k;have d1:∑_k:F (d+1),N=1:=(by simp[N];field_simp[a5.ne']);have d2:c∈P:=(by rw[show c=∑k,N•x k by rw[<-smul_sum]];exact b1.sum_mem (λ_ _=>by positivity) d1 (λk _=>a4 k));refine⟨c,d2,λz hz=>?_⟩;let A:=qc x;let o:V d->V (d+1):=λv=>Fin.cons (1:R) v;let L0:V d->V (d+1):=λv=>Fin.cons (0:R) v;have b7:∀u v,o u-o v=L0 (u-v):=λu v=>funext λr=>Fin.cases (by simp[o,L0]) (λ_=>by simp[o,L0]) r
 let ψ:F (d+1)->V d->R:=λk v=>(A.updateCol k (L0 v)).det/A.det;have a3:∀k v,ψ k v=(λi=>ψ k (E i))⬝ᵥv:=λk v=>by
  have h1:L0 v=∑i,v i•L0 (E i):=funext λr=>Fin.cases (by simp[L0]) (λj=>by simp[L0,E,Qy]) r
  have b8:∀(s:S (F d)) (g:F d->V (d+1)),(A.updateCol k (∑i∈s,g i)).det=∑i∈s,(A.updateCol k (g i)).det:=λs g=>
   Finset.induction_on s (by simpa using det_eq_zero_of_column_eq_zero k λ_=>by simp) λa s ha ih=>by rw[sum_insert ha,det_updateCol_add,ih,sum_insert ha]
  simp only[ψ,h1,b8,det_updateCol_smul,sum_div,dotProduct];exact xu rfl λ_ _=>by ring
 have b9:∀k,∀p∈P,∀q∈P,|ψ k (p-q)|<=2:=λk p hp q hq=>by
  have J:∀u∈P,|(A.updateCol k (o u)).det|<=|A.det|:=λu e7=>by
   have d3:A.updateCol k (o u)=qc (Function.update x k u):=by
    ext r j;by_cases h:j=k
    · subst h;refine Fin.cases ?_ ?_ r<;>simp[A,qc,o]
    · simp[A,qc,h]
   rw[d3];exact c2 λj _=>by by_cases h:j=k<;>simp[h,e7,a4]
  simp only[ψ,<-b7,qM,abs_div];rw[Z (abs_pos.mpr a0)];exact (abs_sub _ _).trans (by linarith[J p hp,J q hq])
 have d4:∀k,G (λi=>ψ k (E i))<=2/w:=λk=>by
  let a:V d:=λi=>ψ k (E i);change G a<=2/w
  by_cases I:a=0
  · rw[I];simp[G,O];positivity
  · have hp:0< G a:=xe.mpr (qu I);obtain⟨p,L,q,a9,b0⟩:=b2 ((1/G a)•a) (qw I);rw[Xb,X,<-a3,one_div_mul_eq_div,Y hp] at b0;rw[Y hw];linarith[(xZ _).trans (b9 k p L q a9)]
 let t:F (d+1)->R:=λk=>(A.updateCol k (o z)).det/A.det;have c0:A*ᵥt=o z:=(by have ht:t=A.det⁻¹•cramer A (o z):=funext λk=>(by simp only[t,Qh,X,cramer_apply];ring);rw[ht,xD,mulVec_cramer,smul_smul,inv_mul_cancel₀ a0,one_smul]);have d5:A*ᵥ(λ_=>N)=o c:=funext λr=>
  Fin.cases (by simp[mulVec,dotProduct,A,qc,o,N];field_simp[a5.ne'])
    (λi=>by simp only[mulVec,dotProduct,A,qc,of_apply,Xm,o,Xt,c,Qh,xc,X];rw[xw];exact xu rfl λ_ _=>by ring) r
 have d6:∀k,0<=t k:=λk=>by
  have d7:(A.updateCol k (o c)).det/A.det=N:=(by have h1:=congrArg (A⁻¹*ᵥ·) ((mulVec_cramer A (o c)).trans (by rw[<-d5,<-xD]));rw[QB,QB,nonsing_inv_mul A (isUnit_iff_ne_zero.mpr a0),QT,QT] at h1;have hk:=congrFun h1 k;simp only[cramer_apply,Qh,X] at hk;rw[hk,mul_div_cancel_left₀ _ a0]);have d8:t k-N=ψ k (z-c):=(by rw[<-d7];simp only[t,ψ,<-sub_div,<-b7,qM]);have d9:G (z-c)<=w/(2*((d:R)+1)):=(QO hz).trans_eq (xN (by positivity));have J:|ψ k (z-c)|<=N:=(by rw[a3];exact (qv _ _).trans ((QD (d4 k) d9 (qj _) (by positivity)).trans_eq (by dsimp[N];field_simp[hw.ne',a5.ne'])))
  rw[<-d8] at J;linarith[(Qr.mp J).1]
 have e0:∑k,t k=1:=(by simpa[mulVec,dotProduct,A,qc,o] using congrFun c0 0);have e1:∑k,t k•x k=z:=funext λi=>(by have hi:=congrFun c0 i.succ;simp only[mulVec,dotProduct,A,qc,of_apply,Xm,o,Xt] at hi;simp only[xc,Qh,X];simpa[Xe] using hi);rw[<-e1];exact b1.sum_mem (λk _=>d6 k) e0 (λk _=>a4 k)
noncomputable def qh (a w:R)(N:ℕ)(b:1<=N)(x:R):F N:=⟨min (N-1) (Nat.floor ((x-a)/w)),by omega⟩
lemma qy {a w x:R}{N:ℕ}(e:1<=N)(b:0< w)(j:a<=x)(k:x<=a+N*w):a+((qh a w N e x:ℕ):R)*w<=x/\x<=a+(((qh a w N e x:ℕ)+1:ℕ):R)*w:=by
 let t:=(x-a)/w;have c:0<=t:=Qq (xx.mpr j) b.le;have f:t<=N:=(Z b).mpr (by linarith);have d:x=a+t*w:=by simp only[t];field_simp[b.ne'];ring
 by_cases i:Nat.floor t< N
 · have g:(qh a w N e x:ℕ)=Nat.floor t:=min_eq_right (Nat.le_sub_one_of_lt i);rw[g,d];push_cast;exact⟨by nlinarith only[xT c,b],by nlinarith only[Nat.lt_floor_add_one t,b]⟩
 · have g:(qh a w N e x:ℕ)=N-1:=min_eq_left (by change N-1<=Nat.floor t;omega);have h:t=N:=xY f (le_trans (by exact_mod_cast (by omega:N<=Nat.floor t)) (xT c));rw[g,d,h,show (((N-1:ℕ)+1:ℕ):R)=N by exact_mod_cast (by omega:N-1+1=N)];exact⟨by nlinarith only[show ((N-1:ℕ):R)<=N by exact_mod_cast Nat.sub_le N 1,b],xo⟩
lemma qN {n m:ℕ}{a:R}(c:0< a)(b:(0:R)< m)(v:F n->F (2*m))(j:F n):|-a+(((v j:ℕ):R)+1/2)*(a/m)|<=a:=by
 have e:(0:R)<=(v j:ℕ):=Qz _;have d:((v j:ℕ):R)+1<=2*m:=(by have f:(((v j:ℕ)+1:ℕ):R)<=((2*m:ℕ):R):=(by exact_mod_cast (v j).isLt);push_cast at f;linarith);rw[Qr];constructor<;>nlinarith only[e,d,QG c b,show (2*(m:R))*(a/m)=2*a by field_simp[b.ne']]
noncomputable def qe (n:ℕ):R:=1/(2*((n+1:ℕ):R)*(32*((n+1:ℕ):R)^2*√((n+1:ℕ):R))^n)
lemma qt (n:ℕ):0< qe n:=by unfold qe;positivity
lemma qY {n:ℕ}(hn:1<=n){u:R}(a3:0< u)(d5:u<=1){v:Type*}[Fintype v][DecidableEq v](x:v->V (n+1))(hx:∀i,0< O (x i)/\O (x i)<=4*((n+1:ℕ):R)):∃g:M (F (n+1)) (F (n+1)) R,gᵀ*g=1/\qe n*u^n*Fintype.card v<=((univ.filter λi:v=>(∀j:F n,|(g*ᵥx i) j.castSucc|<=u)/\0< (g*ᵥx i) (Fin.last n)).card:R):=by
 classical
 by_cases d3:Fintype.card v=0
 · exact⟨1,by simp,by simp[d3]⟩
 · let c:R:=(n+1:ℕ);have o:0< c:=(by positivity);have d6:(2:R)<=c:=(by dsimp[c];exact_mod_cast (by omega:2<=n+1));have a4:0< √c:=xe.mpr o;let m:=u/(2*√c);have y:0< m:=(by positivity);have a5:m<=1/2:=(Z (by positivity)).mpr (by have:(1:R)<=√c:=(by rw[le_sqrt (by norm_num) o.le];linarith);linarith);let d:=Nat.ceil (8*c^2/m);have B:1<=d:=XG.mpr (Nat.ceil_pos.mpr (by positivity)).ne';have a0:(0:R)< d:=qb B;have a6:8*c^2/m<=d:=Nat.le_ceil _;have a7:(d:R)<=16*c^2/m:=by
    linarith[xG (show 0<=8*c^2/m by positivity),(one_le_div y).mpr (by nlinarith:m<=8*c^2),show 16*c^2/m=2*(8*c^2/m) by ring]
   let w:R:=2/d;have J:0< w:=(by positivity);have a8:w<=m/(4*c^2):=(by rw[Qm a0 (by positivity)];have:=Q a6 y.le;rw[xm _ y.ne'] at this;linarith);let A:v->V (n+1):=λi=>(1/G (x i))•x i;have K:∀i,O (A i)=1:=λi=>qw (mt (qz _).mpr (hx i).1.ne');have a9:∀i,∃k:F (n+1),1/c<=|A i k|:=λi=>(by obtain⟨k,_,hk⟩:=xb univ (λk:F (n+1)=>A i k^2) univ_nonempty;have s:1<=c*A i k^2:=(by rw[<-K i];exact (Qv λj hj=>hk j hj).trans (by simp[c]));have t:(1/c)^2<=A i k^2:=(by rw[Xc,one_pow,Z (sq_pos_of_pos o)];nlinarith);exact⟨k,by have h3:=sq_le_sq.mp t;rwa[Qw (by positivity)] at h3⟩)
   choose ki c2 using a9;let H:v->F (n+1)×Bool×(F n->F d):=λi=>(ki i,decide (0<=A i (ki i)),λj=>qh (-1) w d B (A i ((ki i).succAbove j)));have:Nonempty (F (n+1)×Bool×(F n->F d)):=⟨(0,true,λ_=>⟨0,by omega⟩)⟩;obtain⟨p,hp⟩:=qH (univ:S v) H;let e:=univ.filter λi:v=>H i=p;have b0:Fintype.card v<=(2*(n+1)*d^n)*e.card:=(by simpa[e,Fintype.card_prod,xV,QN,Xe,xq] using hp);obtain⟨l,a2⟩:e.Nonempty:=card_pos.mp (by by_contra h0;have:e.card=0:=(by omega);rw[this,mul_zero] at b0;omega);obtain⟨g,c1,d2⟩:=qI (A l) (K l);refine⟨g,c1,?_⟩;have c3:e⊆univ.filter λi:v=>(∀j:F n,|(g*ᵥx i) j.castSucc|<=u)/\0< (g*ᵥx i) (Fin.last n):=λi d4=>by
    let a:=A i;let b:=A l;let f:=ki l;have hk:H i=H l:=(U.mp d4).2.trans (U.mp a2).2.symm;have a1:ki i=f:=congrArg Prod.fst hk;have b1:decide (0<=a f)=decide (0<=b f):=(by have:=congrArg (λq=>q.2.1) hk;dsimp[H] at this;rwa[a1] at this);have c4:∀j:F n,qh (-1) w d B (a (f.succAbove j))=qh (-1) w d B (b (f.succAbove j)):=λj=>(by have:=congrFun (congrArg (λq=>q.2.2) hk) j;dsimp[H] at this;rwa[a1] at this);have I:∀(z:v) (r:F (n+1)),|A z r|<=1:=λz r=>(qg (A z) r).trans (by rw[G,K z,sqrt_one])
    have P:∀r:F (n+1),r≠f->|a r-b r|<=w:=λr hr=>(by obtain⟨j,rfl⟩:=Xy hr;have b2:-1+(d:R)*w=1:=(by simp only[w];rw[xm _ a0.ne'];ring);have s:=qy (a:=-1) (w:=w) B J (Qr.mp (I i (f.succAbove j))).1 (by linarith only[(Qr.mp (I i (f.succAbove j))).2,b2]);have t:=qy (a:=-1) (w:=w) B J (Qr.mp (I l (f.succAbove j))).1 (by linarith only[(Qr.mp (I l (f.succAbove j))).2,b2]);rw[show A i=a from rfl,c4 j] at s;rw[Qr];push_cast at s t;constructor<;>linarith only[s.1,s.2,t.1,t.2])
    have b3:((univ.erase f).card:R)<=c:=(by dsimp[c];exact_mod_cast (card_erase_le.trans (by simp:(univ:S (F (n+1))).card<=n+1)));have b4:|a f^2-b f^2|<=m/(2*c):=by
     have c5:a f^2-b f^2=∑r∈univ.erase f,(b r^2-a r^2):=(by have s:=Xr univ (λr=>a r^2) (QH f);have t:=Xr univ (λr=>b r^2) (QH f);rw[show ∑r,a r^2=1 from K i] at s;rw[show ∑r,b r^2=1 from K l] at t;rw[xf];linarith only[s,t]);rw[c5];have c6:∑r∈univ.erase f,|b r^2-a r^2|<=∑_r∈univ.erase f,(2*w):=Qv λr hr=>(by rw[show b r^2-a r^2=-(a r-b r)*(a r+b r) by ring,xl,XA];linarith only[QD (P r (Xv.mp hr).1) ((xL _ _).trans (show |a r|+|b r|<=2 by linarith only[I i r,I l r])) (xK _) J.le])
     have c7:∑_r∈univ.erase f,(2*w)<=c*(2*(m/(4*c^2))):=(by rw[xt,QX];exact QD b3 (Q a8 Qi.le) (Qk Qi.le J.le) o.le);refine (abs_sum_le_sum_abs _ _).trans (c6.trans (c7.trans_eq ?_));rw[show c*(2*(m/(4*c^2)))=m/(2*c)*(c/c) by ring,xi o.ne',QR]
    have b5:2/c<=|a f+b f|:=by
     have ha:1/c<=|a f|:=by have:=c2 i;rwa[a1] at this
     have hb:1/c<=|b f|:=c2 l;have b6:2/c=1/c+1/c:=by ring
     by_cases s:0<=a f
     · have t:0<=b f:=of_decide_eq_true (b1.symm.trans (decide_eq_true s));rw[QF s] at ha;rw[QF t] at hb;rw[QF (add_nonneg s t)];linarith only[ha,hb,b6]
     · have t:¬ 0<=b f:=λh=>s (of_decide_eq_true (b1.trans (decide_eq_true h)));rw[Xh (xU.mp s)] at ha;rw[Xh (xU.mp t)] at hb;rw[Xh (add_neg (xU.mp s) (xU.mp t))];linarith only[ha,hb,b6]
    have c8:|a f-b f|<=m/4:=by
     have c9:|a f-b f| *(2/c)<=m/(2*c):=
      (Q b5 (xK _)).trans (by rw[<-xl,show (a f-b f)*(a f+b f)=a f^2-b f^2 by ring];exact b4)
     have hm:=T c9 o.le;rw[Y (by norm_num:(0:R)< 4)];rw[QN,div_mul_cancel₀ _ o.ne',div_mul_eq_div_div,div_mul_cancel₀ _ o.ne'] at hm;linarith only[hm]
    have b7:O (a-b)<=m^2:=by
     unfold O;rw[<-Xr _ _ (QH f)];have s:(a f-b f)^2<=m^2/16:=(by nlinarith only[Qr.mp c8]);have t:∑r∈univ.erase f,(a r-b r)^2<=c*w^2:=
      (Qv λr hr=>by nlinarith only[Qr.mp (P r (Xv.mp hr).1)]:_<=∑_r∈univ.erase f,w^2).trans (by rw[xt,QX];exact T b3 (QU w))
     have h3:c*w^2<=m^2/16:=((Q (Ql J.le a8 2) o.le).trans_eq (by field_simp[o.ne'];ring:c*(m/(4*c^2))^2=m^2/(16*c^3))).trans (Xo (QU m) (by norm_num) (by linarith only[xp (by linarith:(1:R)<=c) (n:=3)]));simp only[Qu];linarith only[s,t,h3,QU m]
    have b8:G (g*ᵥa-E (Fin.last n))<=m:=(by rw[<-d2,<-mulVec_sub,G,ql c1,<-xN y.le];exact QO b7);have L:0< G (x i):=xe.mpr (hx i).1;have b9:G (x i)<=2*√c:=(QO (hx i).2).trans_eq (by rw[sqrt_mul (by norm_num),show √(4:R)=2 by rw[show (4:R)=2^2 by norm_num,xN (by norm_num)]]);have c0:g*ᵥx i=G (x i)•(g*ᵥa):=(by rw[<-xD];congr 1;ext r;simp only[a,A,Qh,X,one_div];rw[<-QN,mul_inv_cancel₀ L.ne',Qx]);refine U.mpr ⟨QH i,λj=>?_,?_⟩
    · have N:=qg (g*ᵥa-E (Fin.last n)) j.castSucc;simp only[Qu,E,Qy,xF,↓reduceIte,xh] at N;rw[c0,Qh,X,xl,Qw L];exact (QD b9 (N.trans b8) (xK _) (Qk Qi.le a4.le)).trans_eq (xm u (Qj Qi a4).ne')
    · have N:=qg (g*ᵥa-E (Fin.last n)) (Fin.last n);simp only[Qu,E,xa] at N;rw[c0,Qh,X];exact Qj L (by linarith only[(Qr.mp ((N.trans b8).trans a5)).1])
   have d0:(2*c*(d:R)^n)*(qe n*u^n)<=1:=(by have d1:(d:R)<=32*c^2*√c/u:=a7.trans_eq (by simp only[m];rw[div_div_eq_mul_div];ring);have hp:(d:R)^n<=(32*c^2*√c)^n/u^n:=(by rw[<-Xc];exact Ql a0.le d1 n);exact (Y (Qj (qt n) (QE a3 n))).mp ((Q hp (Qk Qi.le o.le)).trans_eq (by simp only[qe,c,xE,Qx,mul_inv,inv_inv];ring)));have s:(Fintype.card v:R)<=(2*c*(d:R)^n)*e.card:=(by dsimp[c];exact_mod_cast b0);exact ((Q s (Qj (qt n) (QE a3 n)).le).trans_eq (by ring)).trans
    ((T d0 (Qz e.card)).trans (by simpa only[Qx] using Nat.cast_le (α:=R).mpr (QP c3)))
lemma qZ {a α:R}(n:0< a)(e:0< α)(k:ℕ):∃d0>0,∀c,0< c->c< d0->a*(log (1/c))^k*c^α<=1:=by
 by_cases q:k=0
 · subst q;refine⟨min (1/2) ((1/a)^(1/α)),lt_min (by norm_num) (W (by positivity) _),λc f h=>?_⟩;have d:=xz f.le (Qs h (xR _ _)).le e.le;rw[<-QC (by positivity),one_div_mul_cancel e.ne',xQ] at d;have o:=Q d n.le;rw[mul_one_div_cancel n.ne'] at o;simpa using o
 · have i:(0:R)< k:=(by exact_mod_cast Nat.pos_of_ne_zero q);let p:=α/(2*k);have j:0< p:=(by positivity);let b:=a/p^k;have g:0< b:=(by positivity);refine⟨min (1/2) ((1/b)^(2/α)),lt_min (by norm_num) (W (by positivity) _),λc f h=>?_⟩;have l:log (1/c)<=(1/c)^p/p:=by
    have d:=log_le_sub_one_of_pos (W (show 0< 1/c by positivity) p);rw[log_rpow (by positivity)] at d;rw[Y j];linarith
   have r:(log (1/c))^k<=c^(-(α/2))/p^k:=(by have d:=Ql (log_nonneg (by rw[Y f];linarith[Qs h (min_le_left _ _)])) l k;rwa[Xc,<-Qp ((1/c)^p) k,<-QC (by positivity),show (1/c)^(p*(k:R))=c^(-(α/2)) by rw[one_div,inv_rpow f.le,<-rpow_neg f.le];congr 1;simp only[p];field_simp[i.ne']] at d);have m:c^(α/2)<=1/b:=(by have d:=xz f.le (Qs h (xR _ _)).le (by positivity:0<=α/2);rwa[<-QC (by positivity),show 2/α*(α/2)=1 by field_simp[e.ne'],xQ] at d);exact ((by gcongr:a*(log (1/c))^k*c^α<=a*(c^(-(α/2))/p^k)*c^α).trans_eq (by simp only[b];linear_combination (a/p^k)*(by rw[<-QQ f];congr 1;ring:c^(-(α/2))*c^α=c^(α/2)))).trans ((Q m g.le).trans_eq (mul_one_div_cancel g.ne'))
lemma qp (e c:R)(f:0< c){a b:R}(i:b< a)(k:ℕ):∀ᶠ d in xy (0:R) (xP 0),e*(log (1/d))^k*d^a<=c*d^b:=by
 obtain⟨p,n,h⟩:=qZ (show 0< max (e/c) 1 by positivity) (xM.mpr i) k;refine xk.mpr (xj.mpr ⟨min p 1,lt_min n QW,λd q g=>?_⟩);have j:d< p:=Qs (by rwa[xS,xh,Qw g] at q) (min_le_left _ _);have o:d< 1:=Qs (by rwa[xS,xh,Qw g] at q) (xR _ _);have l:0<=log (1/d):=log_nonneg (by rw[Y g];linarith);have m:(e/c)*(log (1/d))^k*d^(a-b)<=1:=
  (T (T (le_max_left _ _) (QM l k)) (W g _).le).trans (h d g j)
 have r:=T m (Qj f (W g b)).le;rw[Qx] at r;have s:e*(log (1/d))^k*d^a=e/c*(log (1/d))^k*d^(a-b)*(c*d^b):=(by rw[show d^a=d^(a-b)*d^b by rw[<-QQ g];congr 1;ring];field_simp[f.ne']);linarith
lemma qm (d c:R)(e:0< c){a b:R}(f:b< a):∀ᶠ δ in xy (0:R) (xP 0),d*δ^a<=c*δ^b:=by simpa using qp d c e f 0
lemma qE (d c:R)(e:0< c){a b:R}(f:b< a):∀ᶠ δ in xy (0:R) (xP 0),d*log (1/δ)*δ^a<=c*δ^b:=by simpa using qp d c e f 1
lemma qO (c:R)(b:0< c):∀ᶠ a in xy (0:R) (xP 0),a< c:=xk.mpr (xj.mpr ⟨c,b,λa d e=>by rwa[xS,xh,Qw e] at d⟩)
def qi {n:ℕ}(g:M (F (n+1)) (F (n+1)) R)(a:V n)(u h:R):Set (V (n+1)):={w | (∀j:F n,|(g*ᵥw) j.castSucc|<=u)/\|(g*ᵥw) (Fin.last n)-a⬝ᵥFin.init (g*ᵥw)|<=h}
lemma qP {n:ℕ}{g:M (F (n+1)) (F (n+1)) R}(v:gᵀ*g=1)(a:V n){u h:R}(I:0<=u)(J:0<=h):(0:V (n+1))∈qi g a u h/\Convex R (qi g a u h)/\(∀w∈qi g a u h,-w∈qi g a u h)/\Bornology.IsBounded (qi g a u h)/\volume (qi g a u h)=ENNReal.ofReal ((2*u)^n*(2*h)):=by
 let b:M (F (n+1)) (F (n+1)) R:=of λi j=>if i=j then 1 else if i=Fin.last n then Fin.lastCases 0 a j else 0;have x:b.det=1:=(by have m:b.IsLowerTriangular:=λi j A=>(by have f:i< j:=A;simp[b,of_apply,ne_of_lt f,show i≠Fin.last n from λh=>not_lt_of_ge (Fin.le_last j) (h▸f)]);rw[det_of_isLowerTriangular b m];simp[b]);let d:V (n+1):=Fin.snoc (λ_:F n=>u) h;let o:Set (V (n+1)):={y | ∀k,-d k<=y k/\y k<=d k};have e:∀y:V (n+1),Fin.init (b*ᵥy)=Fin.init y/\(b*ᵥy) (Fin.last n)=y (Fin.last n)+a⬝ᵥFin.init y:=λy=>by
  refine⟨funext λj=>?_,?_⟩
  · simp only[Fin.init,mulVec,dotProduct,b,of_apply,xF,↓reduceIte];simp_rw[show ∀r:F (n+1),(if j.castSucc=r then (1:R) else 0)*y r=if r=j.castSucc then y r else 0 from λr=>by by_cases K:r=j.castSucc<;>simp[K,eq_comm]];simp
  · simp only[mulVec,dotProduct,Fin.sum_univ_castSucc,b,of_apply,↓reduceIte,Qx,Fin.lastCases_castSucc,Fin.init];rw[add_comm];congr 1;exact xu rfl λj _=>by simp[Ne.symm (xF j)]
 let c:V (n+1)→ₗ[R] V (n+1):=toLin' (gᵀ*b);have p:qi g a u h=c '' o:=by
  ext w;simp only[Set.mem_image,c,toLin'_apply];constructor
  · intro t;let y:V (n+1):=Fin.snoc (Fin.init (g*ᵥw)) ((g*ᵥw) (Fin.last n)-a⬝ᵥFin.init (g*ᵥw));refine⟨y,λk=>Fin.lastCases (by simpa[y,d] using Qr.mp t.2) (λj=>by simpa[y,d,Fin.init] using Qr.mp (t.1 j)) k,?_⟩;have z:b*ᵥy=g*ᵥw:=funext λk=>Fin.lastCases
     (by rw[(e y).2,Fin.init_snoc];simp[y]) (λj=>by have:=congrFun (e y).1 j;simpa[y,Fin.init] using this) k
    rw[<-QB,z,QB,v,QT]
  · rintro⟨y,s,rfl⟩;have q:g*ᵥ((gᵀ*b)*ᵥy)=b*ᵥy:=(by rw[QB,<-QN,qx v,Matrix.one_mul]);refine⟨λj=>?_,?_⟩
    · simp only[q];have B:=congrFun (e y).1 j;simp only[Fin.init] at B;rw[B];exact Qr.mpr (by simpa[d] using s j.castSucc)
    · simp only[q,(e y).2,(e y).1,add_sub_cancel_right];exact Qr.mpr (by simpa[d] using s (Fin.last n))
 have l:o=Xf.pi λk=>Set.Icc (-d k) (d k):=xO λ_=>⟨λh i _=>h i,λh i=>h i trivial⟩;rw[p]
 refine⟨⟨0,λk=>Fin.lastCases (by simp[d,J]) (λj=>by simp[d,I]) k,map_zero c⟩,
  (l▸convex_pi λ_ _=>convex_Icc _ _).linear_image c,
  λ_ ⟨y,H,t⟩=>⟨-y,λk=>by simp only[Pi.neg_apply];exact⟨by linarith[(H k).2],by linarith[(H k).1]⟩,by rw[map_neg,t]⟩,
  ((l▸isCompact_univ_pi λ_=>isCompact_Icc).image (LinearMap.continuous_of_finiteDimensional c)).isBounded,?_⟩
 rw[Measure.addHaar_image_linearMap,LinearMap.det_toLin',det_mul,det_transpose,x,QR,qG v,ENNReal.ofReal_one,Qx];rw[qU (λk=>-d k) d (λk=>Fin.lastCases (by simp[d];linarith) (λj=>by simp[d];linarith) k)];congr 1;rw[Fin.prod_univ_castSucc];simp[d];ring
lemma Qa {d:ℕ}(c e:V d)(g:∀j,c j<=e j):{y:V d | ∀j,c j<=y j/\y j<=e j}⊆convexHull R ((univ.image (λa:F d->Bool=>λj=>if a j then e j else c j):S (V d)):Set (V d)):=by
 intro y l;let t:F d->R:=λj=>if c j=e j then 0 else (y j-c j)/(e j-c j);have m:∀j,0<=t j:=λj=>by
  by_cases h:c j=e j<;>simp[t,h];exact Qq (xx.mpr (l j).1) (xM.mpr (QY (g j) h)).le
 have n:∀j,t j<=1:=λj=>by
  by_cases h:c j=e j<;>simp[t,h];rw[xI (xM.mpr (QY (g j) h))];linarith[(l j).2]
 have o:∀j,t j*e j+(1-t j)*c j=y j:=λj=>by
  by_cases h:c j=e j
  · simp only[t,h,↓reduceIte];linarith[(l j).1,(l j).2]
  · simp only[t,h,↓reduceIte];field_simp[sub_ne_zero.mpr (Ne.symm h)];ring
 let i:(F d->Bool)->R:=λa=>∏j,if a j then t j else 1-t j;have p:∑a,i a=1:=(by dsimp[i];rw[<-Fintype.prod_sum (λj (b:Bool)=>if b then t j else 1-t j)];simp);have q:∑a:F d->Bool,i a•(λj=>if a j then e j else c j)=y:=funext λk=>by
  simp only[xc,Qh,X];let f:F d->Bool->R:=λj b=>if j=k then (if b then t j*e j else (1-t j)*c j) else (if b then t j else 1-t j);have s:∀a,i a*(if a k then e k else c k)=∏j,f j (a j):=λa=>by
   simp only[i];rw[<-Xj _ _ (QH k),<-Xj univ (λj=>f j (a j)) (QH k)];rw[show ∏j∈univ.erase k,f j (a j)=∏j∈univ.erase k,(if a j then t j else 1-t j) from prod_congr rfl λj r=>by simp only[f,(Xv.mp r).1,↓reduceIte]]
   cases a k<;>simp[f]<;>ring
  simp_rw[s];rw[<-Fintype.prod_sum f,<-Xj _ _ (QH k)];rw[show ∑b:Bool,f k b=y k by simpa[f] using o k,prod_eq_one λj r=>by simp[f,(Xv.mp r).1],QR]
 rw[<-q];exact (convex_convexHull R _).sum_mem (λa _=>prod_nonneg λj _=>by cases a j<;>simp<;>linarith[m j,n j])
  p λa _=>subset_convexHull R _ (Xz.mpr (mem_image_of_mem _ (QH a)))
lemma qQ {n:ℕ}(a b:R):Convex R {y:V n | ∀j,a<=y j/\y j<=b}:=(show {y:V n | ∀j,a<=y j/\y j<=b}=Xf.pi λ_=>Set.Icc a b from xO λ_=>⟨λh i _=>h i,λh i=>h i trivial⟩)▸convex_pi λ_ _=>convex_Icc _ _
lemma Qb {n:ℕ}(a b:R):Convex R {y:V n | ∀j,a< y j/\y j< b}:=(show {y:V n | ∀j,a< y j/\y j< b}=Xf.pi λ_=>Set.Ioo a b from xO λ_=>⟨λh i _=>h i,λh i=>h i trivial⟩)▸convex_pi λ_ _=>convex_Ioo _ _
lemma qR {α:Type*}[DecidableEq α](c:S α)(f:α->R){e:R}{L:ℕ}(o:0< e)(P:1<=L)(u:∀x∈c,e<=f x/\f x< 2^L*e):∃k< L,(∑x∈c,f x)/L<=∑x∈c.filter (λx=>2^k*e<=f x/\f x< 2^(k+1)*e),f x:=by
 classical
 let n:ℕ->S α:=λk=>c.filter λx=>2^k*e<=f x/\f x< 2^(k+1)*e;have p:∀x∈c,∃k∈range L,x∈n k:=λx l=>(by have i:∃k,k<=L/\f x< 2^k*e:=⟨L,xo,(u x l).2⟩;let g:=Nat.find i;have q:g<=L/\f x< 2^g*e:=Nat.find_spec i;have H:0< g:=(by by_contra h;have I:g=0:=(by omega);have:=q.2;rw[I,pow_zero,Qx] at this;linarith[(u x l).1]);refine⟨g-1,mem_range.mpr (by omega),U.mpr ⟨l,?_,by rw[show g-1+1=g by omega];exact q.2⟩⟩;by_contra d;push Not at d;exact Nat.find_min i (m:=g-1) (by omega) ⟨by omega,d⟩);have v:Set.PairwiseDisjoint (range L:Set ℕ) n:=λA _ B _ z=>by
  have d:∀a b,a< b->∀x∈n a,x ∉ n b:=λa b K x s t=>(by have:=T (pow_le_pow_right₀ (by norm_num:(1:R)<=2) (by omega:a+1<=b)) o.le;linarith[(U.mp s).2.2,(U.mp t).2.1]);rw[Function.onFun,Xq];intro x s t
  rcases lt_or_gt_of_ne z with h | h;exact d _ _ h x s t;exact d _ _ h x t s
 have r:∑x∈c,f x<=∑k∈range L,∑x∈n k,f x:=by
  rw[<-sum_biUnion v];exact xW (λx l=>let⟨k,w,J⟩:=p x l;QV.mpr ⟨k,w,J⟩)
    (λx l _=>le_trans o.le (u x (U.mp (QV.mp l).choose_spec.2).1).1)
 obtain⟨k,w,y⟩:=xb (range L) (λk=>∑x∈n k,f x) (nonempty_range_iff.mpr (by omega));refine⟨k,mem_range.mp w,(Z (by exact_mod_cast (by omega:0< L))).mpr ?_⟩;exact r.trans ((Qv λj N=>y j N).trans_eq (by simp only[xt,card_range,QX];ring))
lemma qS {n:ℕ}{u a r:R}(J:0< u)(hr:1<=r){h:V n->R}(v:∀y,(∀j,|y j|<=2*u)->0<=h y/\h y<=a)(x:D R {y:V n | ∀j,|y j|<=2*u} h){p q:V n}(s:∀j,|p j|<=u)(z:∀j,|q j-p j|<=u/r):|h q-h p|<=a/r:=by
 have b:0< r:=(by linarith);have c:0< r+1:=(by linarith);let t:=p+r•(q-p);let d:=p-r•(q-p);have f:∀j,|r*(q j-p j)|<=u:=λj=>by rw[xl,Qw b];exact (Q (z j) b.le).trans_eq (xm u b.ne')
 have g:∀j,|p j|<=2*u:=λj=>(s j).trans (by linarith)
 have i:∀j,|t j|<=2*u:=λj=>((xL _ _).trans (xJ (s j) (f j))).trans_eq (by ring)
 have k:∀j,|d j|<=2*u:=λj=>((abs_sub _ _).trans (xJ (s j) (f j))).trans_eq (by ring)
 have w:∀j,|q j|<=2*u:=λj=>(by have A:=xL (p j) (q j-p j);rw[add_sub_cancel] at A;have:u/r<=u:=(Z b).mpr (by nlinarith);linarith[s j,z j])
 have l:=v p g;have m:=v t i;have o:=v d k;have B:h p-a/r<=h q:=(by have e:=x.2 g i (by linarith[(xI b).mpr hr]:0<=1-1/r) (Qq xX b.le) (by ring);rw[show (1-1/r)•p+(1/r)•t=q by ext j;simp[t];field_simp[b.ne'];ring] at e;simp only[X] at e;linarith[Qo l.2 b.le,Qk (Qq xX b.le) m.1,show (1-1/r)*h p=h p-h p/r by ring]);have H:h q<=h p+a/r:=(by have e:=x.2 k w (Qq xX c.le) (Qq b.le c.le) (by rw[<-add_div,add_comm,xi c.ne']);rw[show (1/(r+1))•d+(r/(r+1))•q=p by ext j;simp[d];field_simp[c.ne'];ring] at e;simp only[X] at e;have I:=Q e c.le;rw[show (r+1)*(1/(r+1)*h d+r/(r+1)*h q)=h d+r*h q by field_simp[c.ne']] at I;linarith[(Y b).mpr (by linarith[o.1,l.2]:(h q-h p)*r<=a)]);exact Qr.mpr ⟨by linarith,by linarith⟩
noncomputable def qa (n:ℕ):R:=(4*√((n+1:ℕ):R))^n*2/2^(n+1)
noncomputable def qf (n:ℕ):R:=1/(6*√((n+1:ℕ):R)*(((n+1:ℕ):R)+1)*qa n)
noncomputable def qn (k:ℕ):R:=64*2^k*√((k+2:ℕ):R)*((k+2:ℕ):R)^4
noncomputable def qq (k:ℕ):R:=2*qn k
lemma Qc {d:ℕ}(hd:2<=d){f:R}(g:0< f)(e8:f< 1/16)(h1:8*f^((1:R)/d)<=1)(A:S (V d))(b8:∀x∈A,∀i,-1<=x i/\x i<=1)(e9:DCPR f A)(f0:(2:R)/f<=A.card):∃(r:R) (L k:ℕ) (l:R) (Ab:F k->S (V d)) (P:Set (V d)) (xb:F k->V d),8*f^((1:R)/d)<=r/\r<=16*f^((1:R)/d)/\1<=L/\(L:R)<=4*log (1/f)/\4/f<=2^L/\1<=k/\0< l/\1/(4*L*l)<=k/\(k:R)<=1/f/\(∀i,Ab i⊆A)/\(∀i j,i≠j->Disjoint (Ab i) (Ab j))/\(∀i,l*A.card<=(Ab i).card)/\(A.card:R)/(2*L)<=∑i,((Ab i).card:R)/\IsCompact P/\Convex R P/\P.Nonempty/\(P⊆{y | ∀j,-1<=y j/\y j<=1})/\(∀i,∀a∈Ab i,a∈P)/\∀i,xb i∈P/\(∀a∈Ab i,G (a-xb i)<=2*√d*r)/\∀ ρ>0,∃z,G (z-xb i)< ρ/\z ∉ P:=by
 classical
 have f1:(0:R)< d:=qb (by omega);have o:(0:R)< A.card:=Qs (QG Qi g) f0;have j0:1< log (1/f):=(by have j1:(16:R)< 1/f:=(xd g).mpr (by linarith);have:=log_lt_log (exp_pos 1) (lt_trans exp_one_lt_d9 (by linarith:(2.7182818286:R)< 1/f));rwa[log_exp] at this);let q:=f^((1:R)/d);have b9:0< q:=W g _;let N:=Nat.floor (1/(4*q));have f2:2<=N:=Nat.le_floor ((Y (by positivity)).mpr (by dsimp[q];linarith));have w:(0:R)< N:=qb (by omega);let r:R:=2/N;have b3:0< r:=QG Qi w;have f3:8*q<=r:=(Y w).mpr (by linarith[Q (xT (by positivity:0<=1/(4*q))) (by positivity:0<=8*q),show 8*q*(1/(4*q))=2 by field_simp[b9.ne'];ring])
 have f4:r<=16*q:=(Z w).mpr (by
  have c0:1/(8*q)<=N:=by have:(2:R)<=N:=(by exact_mod_cast f2);linarith[Nat.lt_floor_add_one (1/(4*q)),show 1/(4*q)=2*(1/(8*q)) by ring]
  linarith[Q c0 (by positivity:0<=16*q),show 16*q*(1/(8*q))=2 by field_simp[b9.ne'];ring])
 let gi:V d->F d->F N:=λx j=>qh (-1) r N (by omega) (x j);let K:(F d->F N)->V d:=λi j=>-1+((i j:ℕ):R)*r;let H0:(F d->F N)->V d:=λi j=>-1+(((i j:ℕ)+1:ℕ):R)*r;have a4:∀i j,K i j<=H0 i j:=λi j=>(by simp only[K,H0];push_cast;linarith);have f5:(N:R)*r=2:=(by simp only[r];field_simp[w.ne']);have a5:∀i j,-1<=K i j/\H0 i j<=1:=λi j=>⟨by simp only[K];nlinarith[Qz (α:=R) (i j:ℕ)],by simp only[H0];have:(((i j:ℕ)+1:ℕ):R)<=N:=(by exact_mod_cast (i j).isLt);nlinarith⟩;have a6:∀x∈A,∀j,K (gi x) j<=x j/\x j<=H0 (gi x) j:=λx hx j=>qy (by omega) b3 (b8 x hx j).1 (by linarith[(b8 x hx j).2,f5]);let B:(F d->F N)->S (V d):=λi=>A.filter λx=>gi x=i;have f6:∀i j,i≠j->Disjoint (B i) (B j):=λi j h=>Xq.mpr λx h1 h2=>h ((U.mp h1).2.symm.trans (U.mp h2).2);have a0:∑i,((B i).card:R)=A.card:=(by exact_mod_cast qB A gi);let c:=N^d;have c1:(0:R)< c:=(by simpa[c] using QE w d);have f7:Fintype.card (F d->F N)=c:=(by simp[c]);have f8:(c:R)<=1/(16*f):=(by have b4:(c:R)<=(1/(4*q))^d:=(by simpa[c] using Ql w.le (xT (by positivity)) d);have c2:(1/(4*q))^d=1/((4:R)^d*f):=(by rw[Xc,one_pow,QL,<-Qp q d,<-QC g.le,one_div_mul_cancel f1.ne',xQ]);exact (b4.trans_eq c2).trans (xs (by positivity) (by have:(4:R)^2<=4^d:=pow_le_pow_right₀ (by norm_num) hd;nlinarith)));let J:R:=1/(2*c);have c3:8*f<=J:=(Y (Qj Qi c1)).mpr (by linarith[(Y (by positivity:0< 16*f)).mp f8]);have c4:0< J:=(by linarith);let H:=univ.filter λi=>J*A.card<=(B i).card;have f9:(A.card:R)/2<=∑i∈H,((B i).card:R):=(by let L1:=univ.filter λi=>¬ J*A.card<=(B i).card;have hL:∑i∈L1,((B i).card:R)<=A.card/2:=(Qv λi m=>(xU.mp (U.mp m).2).le).trans ((by simp only[xt,QX];exact T (by exact_mod_cast (f7▸XB L1)) (by positivity):_<=c*(J*A.card)).trans_eq (by simp only[J];field_simp[c1.ne']));linarith[Xa univ (λi=>J*A.card<=(B i).card) (λi=>((B i).card:R)),a0]);let L:=Nat.ceil (log (4/f)/log 2);have n:0< log 2:=log_pos (by norm_num);have c5:1<=L:=XG.mpr (Nat.ceil_pos.mpr (QG (log_pos (by rw[xd g];linarith)) n)).ne';have g0:(L:R)<=4*log (1/f):=(by have b4:=log_lt_log (by positivity) (show 4/f< (1/f)^2 by have:(4:R)< 1/f:=(xd g).mpr (by linarith);nlinarith[show 4/f=4*(1/f) by ring]);rw[log_pow,Nat.cast_ofNat] at b4;have c2:log (4/f)/log 2< 3*log (1/f):=(div_lt_iff₀ n).mpr (by nlinarith[log_two_gt_d9]);linarith[xG (Qq (log_nonneg (show 1<=4/f by rw[Y g];linarith)) n.le)]);have c6:4/f<=(2:R)^L:=(by rw[<-exp_log (QG (by norm_num) g),<-exp_log (QE Qi L),log_pow];exact exp_le_exp.mpr ((Z n).mp (Nat.le_ceil _)));have c7:1< (2:R)^L*J:=(by linarith[QD c6 c3 (by positivity) (QM Qi.le L),show 4/f*(8*f)=32 by field_simp[g.ne'];ring]);obtain⟨kd,_,h0⟩:=qR H (λi=>((B i).card:R)) (Qj c4 o) c5 λi m=>
  ⟨(U.mp m).2,by have:((B i).card:R)<=A.card:=(by exact_mod_cast QP (Xp _ A));linarith[Xw c7 o]⟩
 let I:=H.filter λi=>2^kd*(J*A.card)<=(B i).card/\((B i).card:R)< 2^(kd+1)*(J*A.card);let l:R:=2^kd*J;have a1:f< l:=(by have:(1:R)<=2^kd:=xp (by norm_num);nlinarith);have a9:0< l:=(by linarith);have c8:(0:R)< L:=(by exact_mod_cast (by omega:0< L));have c9:(A.card:R)/(2*L)<=∑i∈I,((B i).card:R):=(show (A.card:R)/(2*L)=(A.card/2)/L by ring).trans_le ((Qo f9 c8.le).trans h0);have a2:∀i∈I,l*A.card<=(B i).card/\((B i).card:R)< 2*l*A.card:=λi m=>
  let h:=(U.mp m).2;⟨by linarith[show 2^kd*(J*A.card)=l*A.card by ring],by linarith[show 2^(kd+1)*(J*A.card)=2*l*A.card by rw[xB];ring]⟩
 have d0:1/(4*L*l)<=I.card:=(Z (by positivity)).mpr (le_of_mul_le_mul_left (show (A.card:R)*1<=A.card*(I.card*(4*L*l)) by linarith[(Z (show 0< 2*(L:R) by positivity)).mp (c9.trans ((Qv λi m=>(a2 i m).2.le).trans (by simp:∑_i∈I,(2*l*A.card)<=I.card*(2*l*A.card))))]) o);have b0:I.Nonempty:=card_pos.mp (XD (α:=R).mp (Qs (by positivity) d0))
 have g1:(I.card:R)<=1/f:=(Y g).mpr (by
  have g2:(I.card:R)*(l*A.card)<=A.card:=(by simp:_=∑_i∈I,(l*A.card)).trans_le ((Qv λi m=>(a2 i m).1).trans (a0▸xW (subset_univ I) λ_ _ _=>Qz _))
  linarith only[XF (show (I.card:R)*l*A.card<=1*A.card by linarith only[g2]) o,Q a1.le (Qz (α:=R) I.card)])
 let cr:=I.biUnion λi=>univ.image fun σ:F d->Bool=>λj=>if σ j then H0 i j else K i j;let P:=convexHull R (cr:Set (V d));have d1:IsCompact P:=cr.finite_toSet.isCompact_convexHull R;have d2:∀i∈I,{y | ∀j,K i j<=y j/\y j<=H0 i j}⊆P:=λi m=>
  (Qa (K i) (H0 i) (a4 i)).trans (convexHull_mono λz hz=>Xz.mpr (QV.mpr ⟨i,m,Xz.mp hz⟩))
 have g3:P⊆{y | ∀j,-1<=y j/\y j<=1}:=convexHull_min (λz hz=>by
  obtain⟨i,_,hm⟩:=QV.mp (Xz.mp hz);obtain⟨σ,_,rfl⟩:=mem_image.mp hm;intro j
  cases h8:σ j<;>simp only[h8,Bool.false_eq_true,↓reduceIte]
  · exact⟨(a5 i j).1,(a4 i j).trans (a5 i j).2⟩
  · exact⟨(a5 i j).1.trans (a4 i j),(a5 i j).2⟩) (qQ (-1) 1)
 have d3:∀i∈I,∀a∈B i,a∈P:=λi m a ha=>d2 i m λj=>(U.mp ha).2▸a6 a (U.mp ha).1 j;have d4:∀i j,H0 i j-K i j=r:=λi j=>(by simp only[H0,K];push_cast;ring);have d5:∀i∈I,∃xb∈P,(∀a∈B i,G (a-xb)<=2*√d*r)/\∀ ρ>0,∃z,G (z-xb)< ρ/\z ∉ P:=λi m=>by
  obtain⟨a,ha⟩:=card_pos.mp (XD (α:=R).mp (Qs (Qj a9 o) (a2 i m).1));have d6:=(U.mp ha).1;have g4:=(U.mp ha).2;obtain⟨a3,e2,h3⟩:=e9 a d6;let u:=(1/G a3)•a3;have d7:O u=1:=qw e2;have b5:G u=1:=(by rw[G,d7,sqrt_one]);have d8:((A.filter λx=>(0:R)<=u⬝ᵥ(x-a)).card:R)<=f*A.card:=(by have hf:A.filter (λx=>(0:R)<=u⬝ᵥ(x-a))=A.filter λx=>(0:R)<=∑j,a3 j*(x j-a j):=(by ext x;simp only[U,u,Xb,X];exact and_congr_right λ_=>mul_nonneg_iff_of_pos_left (QG QW (xe.mpr (qu e2))));rw[hf];exact h3);have b1:∀y∈P,u⬝ᵥ(y-a)< √d*r:=by
   refine convexHull_min (λz hz=>?_) λe5 h1 e6 h2 s t hs ht b7=>by
    change u⬝ᵥ(s•e5+t•e6-a)< √d*r;rw[qK b7,Xl,QK,QK,X,X]
    by_cases e4:s=0
    · subst e4;have:t=1:=(by linarith only[b7]);subst this;simp only[zero_mul,zero_add,Qx];exact h2
    · linarith only[XE h1 (QY hs (Ne.symm e4)),Q (le_of_lt h2) ht,show s*(√d*r)+t*(√d*r)=√d*r by rw[<-add_mul,b7,Qx]]
   obtain⟨i',h4,hm⟩:=QV.mp (Xz.mp hz);obtain⟨σ,_,rfl⟩:=mem_image.mp hm;let v:V d:=λj=>if σ j then H0 i' j else K i' j;have⟨b,e3,h5⟩:∃b∈B i',u⬝ᵥ(b-a)< 0:=(by by_contra b2;push Not at b2;linarith only[Nat.cast_le (α:=R).mpr (QP (show B i'⊆A.filter λx=>(0:R)<=u⬝ᵥ(x-a) from λb hb=>U.mpr ⟨(U.mp hb).1,b2 b hb⟩)),d8,Qs (Xw a1 o) (a2 i' h4).1]);have g5:G (v-b)<=√d*r:=qo b3.le λj=>by
    have b6:=a6 b (U.mp e3).1 j;rw[(U.mp e3).2] at b6;simp only[Qu,v]
    cases σ j<;>simp only[Bool.false_eq_true,↓reduceIte]<;>rw[Qr]<;>constructor<;>linarith only[b6.1,b6.2,d4 i' j]
   have d9:=qv u (v-b);rw[b5,Qx] at d9;change u⬝ᵥ(v-a)< √d*r;rw[show v-a=(v-b)+(b-a) by ext j;simp,Xl];linarith only[(xZ _).trans d9,g5,h5]
  let e:={t:R | 0<=t/\a+t•u∈P};have e0:∀t:R,u⬝ᵥ(a+t•u-a)=t:=λt=>(by rw[QA,QK,X,show u⬝ᵥu=O u by simp[dotProduct,O,sq],d7,QR]);have e1:BddAbove e:=⟨√d*r,λt ht=>by linarith only[b1 _ ht.2,e0 t]⟩;have a7:sSup e∈e:=(isClosed_Ici.inter (d1.isClosed.preimage (QI.add (continuous_id.smul QI)))).csSup_mem ⟨0,⟨Set.mem_Ici.mpr xo,by simpa using d3 i m a ha⟩⟩ e1;have g6:sSup e<=√d*r:=(by linarith only[b1 _ a7.2,e0 (sSup e)]);let x:=a+sSup e•u;refine⟨x,a7.2,λa' e7=>?_,fun ρ a8=>⟨x+(ρ/2)•u,?_,λhm=>?_⟩⟩
  · have g7:G (a'-a)<=√d*r:=qo b3.le λj=>by
     have h1:=a6 a' (U.mp e7).1 j;have h2:=a6 a d6 j;rw[(U.mp e7).2] at h1;rw[g4] at h2;simp only[Qu];rw[Qr];constructor<;>linarith only[h1.1,h1.2,h2.1,h2.2,d4 i j]
    have g8:G (a-x)<=√d*r:=(by rw[show a-x=(-sSup e)•u by ext j;simp[x],qr,XA,QF a7.1,b5,QR];exact g6);rw[show a'-x=(a'-a)+(a-x) by ext j;simp only[Qu,Qt];ring];linarith only[qA (a'-a) (a-x),g7,g8]
  · rw[QA,qr,Qw (by linarith only[a8]),b5,QR];linarith only[a8]
  · have g9:sSup e+ρ/2∈e:=⟨by linarith only[a7.1,a8],by rwa[show a+(sSup e+ρ/2)•u=x+(ρ/2)•u by ext j;simp[x];ring]⟩;linarith only[le_csSup e1 g9,a8]
 choose h6 h7 using d5;let eI:F I.card≃{i //i∈I}:=(Fintype.equivFinOfCardEq (Fintype.card_coe I)).symm
 refine⟨r,L,I.card,l,λi=>B (eI i).1,P,λi=>h6 (eI i).1 (eI i).2,
  f3,f4,c5,g0,c6,b0.card_pos,a9,d0,g1,
  λ_=>Xp _ A,λi j h9=>f6 _ _ λh=>h9 (eI.injective (Subtype.ext h)),
  λi=>(a2 _ (eI i).2).1,?_,d1,convex_convexHull R _,
  let⟨i,m⟩:=b0;⟨K i,d2 i m λj=>⟨xo,a4 i j⟩⟩,g3,
  λi a ha=>d3 _ (eI i).2 a ha,λi=>h7 _ (eI i).2⟩
 rw[Equiv.sum_comp eI λp:{i //i∈I}=>((B p.1).card:R),sum_coe_sort I λi=>((B i).card:R)];exact c9
open Classical in lemma Qd {n:ℕ}{ε e m l:R}(d0:e<=ε)(K:0< m)(N:m< 1)(f:0< l)(r:l< 1)(v:8*l^((1:R)/((n+1:ℕ):R))<=1)(h2:√((n+1:ℕ):R)*l^((1:R)/((n+1:ℕ):R))<=l^m/qa n)(h3:8*log (1/l)*l^(m*((n:R)/((n:R)+2)+e))<=1){L k:ℕ}(d2:1<=L)(d3:(L:R)<=4*log (1/l))(A:S (V (n+1)))(b2:(0:R)< A.card)(I:F k->S (V (n+1)))(b3:∀i,I i⊆A)(b4:∀i j,i≠j->Disjoint (I i) (I j))(w:(A.card:R)/(2*L)<=∑i,((I i).card:R))(P:Set (V (n+1)))(a0:IsCompact P)(s:P.Nonempty)(b5:P⊆{y | ∀j,-1<=y j/\y j<=1})(b6:∀i,∀a∈I i,a∈P)(u:V (n+1))(B:O u=1)(b7:∀x∈P,∀y∈P,u⬝ᵥ(x-y)< l^m/qa n):qD n ε m l A:=by
 let b:R:=(n+1:ℕ);have b8:0< b:=(by positivity);have b9:0< √b:=xe.mpr b8;have d4:0< qa n:=(by unfold qa;positivity);let c:=l^m/qa n;have c0:0< c:=(by positivity);have a1:Continuous (λx:V (n+1)=>u⬝ᵥx):=continuous_finsetSum univ λi _=>QI.mul (xv i);obtain⟨pM,a9,hM⟩:=a0.exists_isMaxOn s a1.continuousOn;obtain⟨pm,b0,hm⟩:=a0.exists_isMinOn s a1.continuousOn;let J:=(u⬝ᵥpM+u⬝ᵥpm)/2;let d:=J•u;obtain⟨g,q,c9⟩:=qI u B;let o:=qi g 0 (2*√b) c;have p:=qP q 0 (show 0<=2*√b by positivity) c0.le;let t:=l^m;have a2:l<=t:=(by simpa[t] using Qn f r.le N.le);have a3:t< 1:=rpow_lt_one f.le r K;have H:∀z:V (n+1),(g*ᵥz) (Fin.last n)=u⬝ᵥz:=λz=>(by have v:=qF q u z;rw[c9] at v;simpa[dotProduct,E,Qy] using v);refine⟨t,d,o,a2,xo,p.1,p.2.1,p.2.2.1,p.2.2.2.1,?_,?_,?_⟩
 · intro z hz;have a4:G (g*ᵥz)<=√b*l^((1:R)/b):=(by rw[G,ql q];exact qo (W f _).le λi=>by simpa[Qx,b] using hz i);refine⟨λj=>(qg _ _).trans (a4.trans (by nlinarith only[v,b9])),?_⟩;simp only[xA,xh];exact (qg _ _).trans (a4.trans h2)
 · rw[p.2.2.2.2];apply le_of_eq;congr 1;simp only[c,qa,t,b];rw[show 2*(2*√((n+1:ℕ):R))=4*√((n+1:ℕ):R) by ring];field_simp[(by positivity:(4*√((n+1:ℕ):R))^n*2≠0)]
 · have a5:G u=1:=(by rw[G,B,sqrt_one]);have c1:∀x∈P,x-d∈o:=λx hx=>by
    have c2:u⬝ᵥ(x-d)=u⬝ᵥx-J:=(by rw[QZ,QK,X,show u⬝ᵥu=O u by simp[dotProduct,O,sq],B,QR]);have c3:u⬝ᵥpM-u⬝ᵥpm< c:=(by have:=b7 pM a9 pm b0;rwa[QZ] at this);have a6:∀y∈P,G y<=√b:=λy hy=>(by simpa[b] using qo xX λj=>Qr.mpr (b5 hy j));have d5:|J|<=√b:=by
     have v:∀y∈P,|u⬝ᵥy|<=√b:=λy hy=>by have:=qv u y;rw[a5,Qx] at this;exact this.trans (a6 y hy)
     dsimp[J];rw[Qr];have:=Qr.mp (v pM a9);have:=Qr.mp (v pm b0);constructor<;>linarith
    have c4:G (x-d)<=2*√b:=(by rw[Xi];exact (qA x (-d)).trans (by rw[show -d=(-J)•u by ext j;simp[d],qr,XA,a5,QR];linarith[a6 x hx]));refine⟨λj=>(qg _ _).trans (by rw[G,ql q,<-G];exact c4),?_⟩;simp only[xA,xh,H,c2,Qr];dsimp[J];have c5:u⬝ᵥx<=u⬝ᵥpM:=hM hx;have c6:u⬝ᵥpm<=u⬝ᵥx:=hm hx;constructor<;>linarith only[c5,c6,c3]
   have c7:∑i,((I i).card:R)<=((A.filter λx=>x-d∈o).card:R):=(by exact_mod_cast (by rw[<-XC (λi _ j _ h=>b4 i j h)];exact QP λx hx=>let⟨i,_,b1⟩:=QV.mp hx;U.mpr ⟨b3 i b1,c1 x (b6 i x b1)⟩));have d6:0< log (1/l):=log_pos (by rw[xd f];linarith);have d1:(0:R)< L:=(by exact_mod_cast (by omega:0< L));have a7:t^((n:R)/((n:R)+2)+ε)<=1/(2*L):=(by have a8:=Qn (W f m) a3.le (by linarith:(n:R)/((n:R)+2)+e<=(n:R)/((n:R)+2)+ε);rw[show t^((n:R)/((n:R)+2)+e)=l^(m*((n:R)/((n:R)+2)+e)) by simp only[t,<-QC f.le]] at a8;have c8:l^(m*((n:R)/((n:R)+2)+e))<=1/(8*log (1/l)):=(Y (by positivity)).mpr (by linarith);exact (a8.trans c8).trans (xs (by positivity) (by linarith)));exact ((T a7 b2.le).trans_eq (by ring)).trans (w.trans c7)
lemma Qe {n:ℕ}(hn:1<=n){τ δ:R}(c5:0< δ)(h4:qf n*δ^τ<=1){L k m:ℕ}(c6:1<=L)(e3:4/δ<=2^L)(e4:1<=k)(e5:(k:R)<=1/δ)(e6:1<=m)(P:Set (V (n+1)))(c7:IsCompact P)(c8:Convex R P)(c9:P.Nonempty)(a8:P⊆{y | ∀j,-1<=y j/\y j<=1})(e7:∀u:V (n+1),O u=1->∃x∈P,∃y∈P,δ^τ/qa n<=u⬝ᵥ(x-y))(xb:F k->V (n+1))(b6:∀i,xb i∈P)(b7:∀i,∀ ρ>0,∃z,G (z-xb i)< ρ/\z ∉ P):let d:=qf n*δ^τ;∃(cc:V (n+1)) (g:M (F (n+1)) (F (n+1)) R) (e:S (F k)) (h:V n->R) (ci:F k->F n->F (2*m)) (J:S (F n->F (2*m))) (K:R),gᵀ*g=1/\qe n*d^n*k<=e.card/\(∀y,(∀j,|y j|<=2*d)->0<=h y/\h y<=2*√((n+1:ℕ):R))/\D R {y:V n | ∀j,|y j|<=2*d} h/\(∀i∈e,(g*ᵥ(xb i-cc)) (Fin.last n)=h (Fin.init (g*ᵥ(xb i-cc))))/\(∀i∈e,∀j,|Fin.init (g*ᵥ(xb i-cc)) j-qd d m (ci i) j|<=d/(2*m))/\J.Nonempty/\0< K/\1/((2:R)^(n+1)*L)<=K/\(m:R)^n/(2*L*K)<=J.card/\∀v∈J,K*e.card/(m:R)^n<=((e.filter λi=>ci i=v).card:R):=by
 classical
 intro d;let b:R:=(n+1:ℕ);let c:R:=m;let H:R:=L;have c2:0< b:=(by positivity);have e8:0< b+1:=(by linarith);have e9:0< √b:=xe.mpr c2;have f0:0< qa n:=(by unfold qa;positivity);have h5:0< qf n:=(by unfold qf;positivity);have a9:0< d:=(by positivity);obtain⟨cc,c1,a6⟩:=qX (by omega:1<=n+1) c7 c8 c9 (by positivity:0< δ^τ/qa n) e7;let b0:=(δ^τ/qa n)/(2*(b+1));have f1:3*√b*d=b0:=(by simp only[d,qf,b0,b];field_simp[e9.ne',e8.ne',f0.ne'];ring);let B:F k->V (n+1):=λi=>xb i-cc;have f2:∀i,0< O (B i)/\O (B i)<=4*b:=λi=>by
  refine⟨?_,?_⟩
  · by_contra b3;push Not at b3;have h0:xb i=cc:=sub_eq_zero.mp ((qz _).mp (xY b3 (sum_nonneg λ_ _=>QU _)));obtain⟨z,hz,g7⟩:=b7 i b0 (by positivity);rw[h0] at hz;exact g7 (a6 z (by rw[<-qk];exact Ql (qj _) hz.le 2))
  · have f3:G (B i)<=√b*2:=qo (by norm_num:(0:R)<=2) λj=>by
     have:=a8 (b6 i) j;have:=a8 c1 j;simp only[B,Qu,Qr];constructor<;>linarith
    rw[<-qk];exact (Ql (qj (B i)) f3 2).trans_eq (by rw[QL,sq_sqrt c2.le];ring)
 obtain⟨g,a1,g8⟩:=qY hn a9 h4 B f2;let e:=univ.filter λi:F k=>(∀j:F n,|(g*ᵥB i) j.castSucc|<=d)/\0< (g*ᵥB i) (Fin.last n);have b8:qe n*d^n*k<=e.card:=(by simpa[e,xV] using g8);have d0:(0:R)< k:=qb e4;have a0:(0:R)< e.card:=Qs (Qj (Qj (qt n) (QE a9 n)) d0) b8;let Pg:=(λz=>g*ᵥ(z-cc)) '' P;have b9:Convex R Pg:=(by rintro _ ⟨x,hx,rfl⟩ _ ⟨y,hy,rfl⟩ s t hs ht b5;exact⟨s•x+t•y,c8 hx hy hs ht b5,by dsimp only;rw[qK b5,mulVec_add,xD,xD]⟩);have d1:IsCompact Pg:=c7.image (xH λi=>continuous_finsetSum univ λj _=>QI.mul ((xv j).sub QI));have d2:∀w:V (n+1),O w<=b0^2->w∈Pg:=λw hw=>
  ⟨cc+gᵀ*ᵥw,a6 _ (by rw[QA,ql (by rw[transpose_transpose];exact qx a1)];exact hw),by dsimp only;rw[QA,QB,qx a1,QT]⟩
 have d3:∀w∈Pg,G w<=2*√b:=(by rintro _ ⟨z,hz,rfl⟩;rw[G,ql a1,<-G];have I:G (z-cc)<=√b*2:=qo (by norm_num:(0:R)<=2) λj=>(by have:=a8 hz j;have:=a8 c1 j;simp only[Qu,Qr];constructor<;>linarith);linarith);let h:V n->R:=λy=>sSup {t:R | Fin.snoc y t∈Pg};have d4:∀y,(∀j,|y j|<=2*d)->∀w:V (n+1),G w<=√b*d->Fin.snoc y 0+w∈Pg:=λy hy w hw=>by
  have f4:G (Fin.snoc y 0)<=2*√b*d:=(QO (by
   simp only[O,Fin.sum_univ_castSucc,xn,xr,zero_pow (by norm_num:2≠0),xC];have I:∑j:F n,y j^2<=(n:R)*(2*d)^2:=(Qv λj _=>sq_le_sq.mpr (by rw[QF (Qk Qi.le a9.le)];exact hy j)).trans_eq (by simp);rw[show (2*√b*d)^2=b*(2*d)^2 by rw[QL,QL,sq_sqrt c2.le];ring]
   exact I.trans (T (by dsimp[b];exact_mod_cast Nat.le_succ n) (QU _)))).trans_eq (xN (by positivity))
  apply d2;rw[<-qk];exact Ql (qj _) ((qA _ _).trans (by linarith only[f4,hw,f1])) 2
 have c0:∀y t,Fin.snoc y t∈Pg->t<=2*√b:=λy t ht=>(by have I:=qg (Fin.snoc y t) (Fin.last n);simp only[xr] at I;exact (xZ t).trans (I.trans (d3 _ ht)));have b1:∀y,BddAbove {t:R | Fin.snoc y t∈Pg}:=λy=>⟨2*√b,c0 y⟩;have b2:∀y,(∀j,|y j|<=2*d)->Fin.snoc y (h y)∈Pg/\0<=h y/\h y<=2*√b:=λy hy=>(by have h0:(0:R)∈{t | Fin.snoc y t∈Pg}:=(by simpa using d4 y hy 0 (by simp[G,O];positivity));have f5:IsClosed {t:R | Fin.snoc y t∈Pg}:=d1.isClosed.preimage (xH λj=>Fin.lastCases (by simp only[xr];exact continuous_id) (λ_=>by simp only[xn];exact QI) j);exact⟨f5.csSup_mem ⟨0,h0⟩ (b1 y),le_csSup (b1 y) h0,csSup_le ⟨0,h0⟩ (c0 y)⟩);have f6:D R {y:V n | ∀j,|y j|<=2*d} h:=
  ⟨(show {y:V n | ∀j,|y j|<=2*d}={y:V n | ∀j,-(2*d)<=y j/\y j<=2*d} from xO λ_=>by simp only[Set.mem_ofPred_eq,Qr])▸qQ _ _,
   λl I o h2 s t hs ht b5=>by
    simp only[X];refine le_csSup (b1 _) ?_;change Fin.snoc (s•l+t•o) (s*h l+t*h o)∈Pg;rw[show Fin.snoc (s•l+t•o) (s*h l+t*h o)=s•Fin.snoc l (h l)+t•Fin.snoc o (h o) by ext r;refine Fin.lastCases ?_ ?_ r<;>simp]
    exact b9 (b2 l I).1 (b2 o h2).1 hs ht b5⟩
 have f7:∀i∈e,(g*ᵥB i) (Fin.last n)=h (Fin.init (g*ᵥB i)):=λi hi=>by
  let z:=g*ᵥB i;let y:=Fin.init z;let zl:=z (Fin.last n);have c3:=(U.mp hi).2;have d5:∀j,|y j|<=2*d:=λj=>(c3.1 j).trans (by linarith)
  have b3:zl<=h y:=le_csSup (b1 y) (by show Fin.snoc y zl∈Pg;dsimp[y,zl];rw[Fin.snoc_init_self];exact⟨xb i,b6 i,rfl⟩);by_contra h3;have d6:zl< h y:=QY b3 h3;have a2:0< h y:=lt_trans c3.2 d6;let p:=zl/h y;have a3:0< 1-p:=xM.mpr ((Xg a2).mpr d6);obtain⟨w0,g9,e0⟩:=b7 i ((1-p)*(√b*d)) (by positivity);let w:=g*ᵥ(w0-xb i);have d7:G ((1/(1-p))•w)<=√b*d:=(by rw[qr,Qw (QG QW a3),one_div_mul_eq_div,Z a3,G,ql a1,<-G];simpa[Xe] using g9.le);have f8:g*ᵥ(w0-cc)=(1-p)•(Fin.snoc y 0+(1/(1-p))•w)+p•Fin.snoc y (h y):=by
   rw[show g*ᵥ(w0-cc)=z+w by rw[show w0-cc=B i+(w0-xb i) by ext j;simp[B],mulVec_add],<-Fin.snoc_init_self z];ext r;refine Fin.lastCases ?_ (λj=>?_) r
   · simp only[Qt,Qh,X,xr];rw[show (1-p)*(0+1/(1-p)*w (Fin.last n))=w (Fin.last n) by field_simp[a3.ne'];ring,show p*h y=zl by dsimp[p];field_simp[a2.ne']];simp only[zl];ring
   · simp only[Qt,Qh,X,xn];field_simp[a3.ne'];ring
  obtain⟨z',e1,e2⟩:=f8▸b9 (d4 y d5 _ d7) (b2 y d5).1 a3.le (Qq c3.2.le a2.le) (by ring);have f9:z'=w0:=sub_left_inj.mp (by have I:=congrArg (mulVec gᵀ) e2;dsimp only at I;rwa[QB,QB,a1,QT,QT] at I);exact e0 (f9▸e1)
 have N:0< c:=qb e6;have q:0< H:=qb c6;let ci:F k->F n->F (2*m):=λi j=>qh (-d) (d/c) (2*m) (by omega) (Fin.init (g*ᵥB i) j);have g0:∀i∈e,∀j,|Fin.init (g*ᵥB i) j-qd d m (ci i) j|<=d/(2*c):=λi hi j=>(by have hb:=Qr.mp ((U.mp hi).2.1 j);have h6:((2*m:ℕ):R)*(d/c)=2*d:=(by dsimp[c];push_cast;field_simp[N.ne']);have I:=qy (a:=-d) (w:=d/c) (by omega:1<=2*m) (QG a9 N) hb.1 (by linarith);let t:R:=(ci i j:ℕ);have d8:-d+t*(d/c)<=Fin.init (g*ᵥB i) j/\Fin.init (g*ᵥB i) j<=-d+(t+1)*(d/c):=(by simpa[t,ci,Fin.init] using I);simp only[qd];rw[Qr];constructor<;>linarith only[d8.1,d8.2,show (t+1/2)*(d/c)-d/(2*c)=t*(d/c) by ring,show (t+1/2)*(d/c)+d/(2*c)=(t+1)*(d/c) by ring])
 let f:(F n->F (2*m))->ℕ:=λv=>(e.filter λi=>ci i=v).card;have g1:∑v,(f v:R)=e.card:=(by exact_mod_cast qB e ci);let a4:=univ.filter λv=>1<=f v;have g2:∑v∈a4,(f v:R)=e.card:=(by rw[<-g1,<-Xa univ (λv=>1<=f v)];have h0:∑v∈univ.filter (λv=>¬ 1<=f v),(f v:R)=0:=sum_eq_zero λv hv=>(by have:f v=0:=(by have:=(U.mp hv).2;omega);simp[this]);linarith only[h0]);obtain⟨A,_,a7⟩:=qR a4 (λv=>(f v:R)) QW c6 λv hv=>
  ⟨by exact_mod_cast (U.mp hv).2,by
   have I:(f v:R)<=e.card:=(by exact_mod_cast QP (Xp _ e));have h2:(e.card:R)<=k:=by exact_mod_cast (by simpa using XB e:e.card<=k)
   linarith only[I,h2,e5,Xx (by norm_num:(1:R)< 4) c5,e3,show (2:R)^L*1=2^L by ring]⟩
 rw[g2] at a7;let J:=a4.filter λv=>2^A*1<=(f v:R)/\(f v:R)< 2^(A+1)*1;let K:R:=2^A*c^n/e.card;have b4:0< K:=QG (Qj (QE Qi A) (QE N n)) a0;have a5:c^n≠0:=pow_ne_zero n N.ne';have g3:∀v∈J,K*e.card/c^n<=f v:=λv hv=>(by have h2:K*e.card/c^n=2^A:=(by simp only[K];field_simp[a0.ne',a5]);linarith only[(U.mp hv).2.1,h2]);have c4:c^n/(2*H*K)<=J.card:=by
  have g4:∑v∈J,(f v:R)<=J.card*(2*K*e.card/c^n):=
   (Qv λv hv=>by linarith only[(U.mp hv).2.2]:_<=∑_v∈J,(2:R)^(A+1)).trans_eq (by simp only[xt,QX,K,xB];congr 1;field_simp[a0.ne',a5])
  rw[Z (Qj (Qj Qi q) b4)];have hm:=Q (a7.trans g4) (Qk q.le (QM N.le n));have hl:H*c^n*((e.card:R)/H)=e.card*c^n:=(by rw[show H*c^n*((e.card:R)/H)=(e.card:R)*c^n*(H/H) by ring,xi q.ne',QR]);have hr:H*c^n*(J.card*(2*K*e.card/c^n))=e.card*(J.card*(2*H*K)):=(by rw[show H*c^n*(J.card*(2*K*e.card/c^n))=(e.card:R)*(J.card*(2*H*K))*(c^n/c^n) by ring,xi a5,QR]);exact le_of_mul_le_mul_left (by linarith only[hm,hl,hr]) a0
 have d9:J.Nonempty:=card_pos.mp (XD (α:=R).mp (Qs (QG (QE N n) (Qj (Qj Qi q) b4)) c4));have g5:1/((2:R)^(n+1)*H)<=K:=(by have g6:(J.card:R)<=2^n*c^n:=(by dsimp[c];rw[<-QL];exact_mod_cast (by rw[<-show Fintype.card (F n->F (2*m))=(2*m)^n by simp];exact XB J:J.card<=(2*m)^n));have I:=(Z (Qj (Qj Qi q) b4)).mp (c4.trans g6);rw[Z (Qj (QE Qi (n+1)) q)];exact XF (by rw[xB];linarith only[I,show (2:R)^n*c^n*(2*H*K)=((2:R)^n*2*H*K)*c^n by ring]:1*c^n<=K*((2:R)^(n+1)*H)*c^n) (QE N n));exact⟨cc,g,e,h,ci,J,K,a1,b8,λy hy=>(b2 y hy).2,f6,f7,g0,d9,b4,g5,c4,g3⟩
open Classical in lemma qT {n:ℕ}{ε τ δ o b err B hr η:R}{k m:ℕ}(a3:0< δ)(a4:0< o)(s:(0:R)< m)(a5:√((n+1:ℕ):R)*δ^((1:R)/((n+1:ℕ):R))<=b)(H:b<=o/(2*m))(b4:0<=B)(b5:(1+(n:R)*B)*b<=err)(a0:2*err<=hr)(a6:0<=err)(a7:(2*(o/m))^n*(2*hr)=η*2^(n+1))(a8:δ<=η)(a9:η<=δ^τ)(A:S (V (n+1)))(Ab:F k->S (V (n+1)))(b6:∀i,Ab i⊆A)(b7:∀i j,i≠j->Disjoint (Ab i) (Ab j))(t:V (n+1))(g:M (F (n+1)) (F (n+1)) R)(u:gᵀ*g=1)(I:F k->V (n+1))(b0:∀i,∀a∈Ab i,G (a-I i)<=b)(Ig:S (F k))(h:V n->R)(b8:∀i∈Ig,(g*ᵥ(I i-t)) (Fin.last n)=h (Fin.init (g*ᵥ(I i-t))))(ci:F k->F n->F (2*m))(b9:∀i∈Ig,∀j,|Fin.init (g*ᵥ(I i-t)) j-qd o m (ci i) j|<=o/(2*m))(v:F n->F (2*m))(c:V n)(d:R)(c0:∀y,(∀j,|y j-qd o m v j|<=o/(2*m))->|h y-(d+c⬝ᵥy)|<=err)(c1:∀j,|c j|<=B)(a1:η^((n:R)/((n:R)+2)+ε)*A.card<=∑i∈Ig.filter λi=>ci i=v,((Ab i).card:R)):qD n ε τ δ A:=by
 let q:=qd o m v;let e:V (n+1):=t+gᵀ*ᵥFin.snoc q (d+c⬝ᵥq);let J:=qi g c (o/m) hr;have l:=qP u c (Qq a4.le s.le) (show 0<=hr by linarith only[a0,a6]);have c2:∀z:V (n+1),g*ᵥ(z-e)=g*ᵥ(z-t)-Fin.snoc q (d+c⬝ᵥq):=λz=>(by rw[show z-e=(z-t)-gᵀ*ᵥFin.snoc q (d+c⬝ᵥq) by ext r;simp[e];ring,mulVec_sub,QB,qx u,QT]);have K:∀w:V (n+1),(∀j:F n,|w j.castSucc|<=b)->|w (Fin.last n)|<=b->|w (Fin.last n)-c⬝ᵥFin.init w|<=err:=λw c7 c8=>
  (abs_sub _ _).trans ((xJ c8 ((abs_sum_le_sum_abs _ _).trans ((Qv λj _=>by rw[xl];exact QD (c1 j) (c7 j) (xK _) b4:_<=∑_j:F n,(B*b)).trans_eq (by simp[QN]:_=(n:R)*B*b)))).trans (by linarith only[b5]))
 refine⟨η,e,J,a8,a9,l.1,l.2.1,l.2.2.1,l.2.2.2.1,?_,?_,?_⟩
 · intro z hz;have c3:G (g*ᵥz)<=b:=(by rw[G,ql u,<-G];exact qo (W a3 _).le λi=>by simpa[Qx] using hz i:G (g*ᵥz)<=_).trans a5;have hc:∀r,|(g*ᵥz) r|<=b:=λr=>(qg _ r).trans c3
   exact⟨λj=>(hc j.castSucc).trans (H.trans (by rw[Qm (Qj Qi s) s];nlinarith only[a4,s])),(K (g*ᵥz) (λj=>hc j.castSucc) (hc (Fin.last n))).trans (by linarith only[a0,a6])⟩
 · rw[l.2.2.2.2,a7]
 · have c4:∀i∈Ig.filter λi=>ci i=v,∀a∈Ab i,a-e∈J:=λi hi a ha=>by
    have L:=(U.mp hi).1;have b1:=(U.mp hi).2;let N:=g*ᵥ(I i-t);let q1:V (n+1):=Fin.snoc q (d+c⬝ᵥq);let f:=N-q1;let p:=g*ᵥ(a-I i);have b2:∀j,|Fin.init N j-q j|<=o/(2*m):=λj=>by have:=b9 i L j;rwa[b1] at this
    have a2:∀r,|p r|<=b:=λr=>(qg _ r).trans (by rw[G,ql u];exact b0 i a ha)
    have P:g*ᵥ(a-e)=f+p:=(by rw[c2,show a-t=(I i-t)+(a-I i) by ext r;simp,mulVec_add];ext r;simp[f,p,N,q1];ring);refine⟨λj=>?_,?_⟩
    · simp only[P,f,q1,Qt,Qu,xn];exact (xL _ _).trans ((xJ (b2 j) ((a2 j.castSucc).trans H)).trans_eq (by ring))
    · have c5:(f+p) (Fin.last n)-c⬝ᵥFin.init (f+p)=(f (Fin.last n)-c⬝ᵥFin.init f)+(p (Fin.last n)-c⬝ᵥFin.init p):=(by rw[show Fin.init (f+p)=Fin.init f+Fin.init p from rfl,Xl];simp only[Qt];ring);have c6:|f (Fin.last n)-c⬝ᵥFin.init f|<=err:=by
       rw[show f (Fin.last n)-c⬝ᵥFin.init f=h (Fin.init N)-(d+c⬝ᵥFin.init N) by
        simp only[f,q1,N,Qu,xr,b8 i L];rw[show Fin.init (N-q1)=Fin.init N-q by ext j;simp[q1,Fin.init],QZ];ring]
       exact c0 _ b2
      rw[P,c5];exact (xL _ _).trans ((xJ c6 (K p (λj=>a2 j.castSucc) (a2 (Fin.last n)))).trans (by linarith only[a0]))
   exact a1.trans (by exact_mod_cast (by rw[<-XC (λi _ j _ h=>b7 i j h)];exact QP λx hx=>let⟨i,hi,b3⟩:=QV.mp hx;U.mpr ⟨b6 i b3,c4 i hi x b3⟩))
lemma Qf {k L m:ℕ}{d K:R}(g:0< d)(c0:1<=L)(d2:2*(k+2)< m)(c1:0< K)(c2:2*(m:R)*(qn k*K*L/(m:R)^2)<=√((k+2:ℕ):R))(h:V (k+1)->R)(a4:∀y,(∀j,|y j|<=2*d)->0<=h y/\h y<=2*√((k+2:ℕ):R))(a5:D R {y:V (k+1) | ∀j,|y j|<=2*d} h)(J:S (F (k+1)->F (2*m)))(I:J.Nonempty)(c3:(m:R)^(k+1)/(2*L*K)<=J.card):let o:=qn k*K*L/(m:R)^2;∃v∈J,∃(c:V (k+1)) (i:R),(∀y,(∀j,|y j-qd d m v j|<=d/(2*m))->|h y-(i+c⬝ᵥy)|<=o)/\∀j,|c j|<=3*√((k+2:ℕ):R)/d:=by
 intro o;let a:R:=(k+2:ℕ);let b:R:=m;have c4:0< a:=qb (by omega);have p:0< √a:=xe.mpr c4;have e:0< b:=qb (by omega);have c5:(1:R)<=b:=qC (by omega);have a6:(0:R)< L:=qb c0;let f:V (k+1)->V (k+1):=λx j=>(2*x j-1)*d;let H:V (k+1)->R:=λx=>1-h (f x)/(2*√a);have N:∀x:V (k+1),(∀j,-(1/2:R)< x j/\x j< 3/2)->∀j,|f x j|<=2*d:=λx hx j=>(by rw[xl,Qw g];exact T (Qr.mpr ⟨by linarith only[(hx j).1],by linarith only[(hx j).2]⟩) g.le)
 have c6:C R {x:V (k+1) | ∀j,-(1/2:R)< x j/\x j< 3/2} H:=
  ⟨Qb _ _,λl h1 n h2 s t hs ht a3=>by
   have hl:f (s•l+t•n)=s•f l+t•f n:=funext λj=>(by simp only[f,Qt,Qh,X];linear_combination d*a3);have hc:=Qo (a5.2 (N l h1) (N n h2) hs ht a3) (Qk Qi.le p.le);simp only[H,X] at hc ⊢;rw[hl]
   linarith only[hc,show s*(1-h (f l)/(2*√a))+t*(1-h (f n)/(2*√a))=1-(s*h (f l)+t*h (f n))/(2*√a) by linear_combination a3]⟩
 have c7:∀x,(∀j,-(1/2:R)< x j/\x j< 3/2)->0<=H x/\H x<=1:=λx hx=>
  let hb:=a4 _ (N x hx);⟨by simp only[H];linarith only[(xI (Qj Qi p)).mpr hb.2],by simp only[H];linarith only[Qq hb.1 (Qk Qi.le p.le)]⟩
 obtain⟨v,d1,aH,bH,b9⟩:=qW k (2*m) (by omega) H c6 c7 J I;let q:=qd d m v;let c:V (k+1):=λj=>-(√a/d)*aH j;let i:R:=2*√a*(1-bH - ∑j,aH j/2);let u:V (k+1)->R:=λy=>i+c⬝ᵥy;have P:∀y,(∀j,|y j-q j|<=d/(2*b))->|h y-u y|<=o:=λy hy=>by
  let x:V (k+1):=λj=>(y j+d)/(2*d);have c8:∀j,((v j:ℕ):R)/((2*m:ℕ):R)<=x j/\x j<=(((v j:ℕ)+1:ℕ):R)/((2*m:ℕ):R):=λj=>by
   let t:R:=(v j:ℕ);have a0:=Qr.mp (hy j);simp only[q,qd] at a0;push_cast;have c9:-d+t*(d/b)<=y j:=(by linarith only[a0.1,show (t+1/2)*(d/b)-d/(2*b)=t*(d/b) by ring]);have d0:y j<=-d+(t+1)*(d/b):=(by linarith only[a0.2,show (t+1/2)*(d/b)+d/(2*b)=(t+1)*(d/b) by ring]);simp only[x];constructor
   · rw[Qm (Qj Qi e) (Qj Qi g)];nlinarith only[c9,e,show t*(2*d)=t*(d/b)*(2*b) by field_simp[e.ne']]
   · rw[Qm (Qj Qi g) (Qj Qi e)];nlinarith only[d0,e,show (t+1)*(2*d)=(t+1)*(d/b)*(2*b) by field_simp[e.ne']]
  have a7:f x=y:=funext λj=>(by simp only[f,x];field_simp[g.ne'];ring);have a8:h y-u y=-(2*√a)*(H x-(bH+aH⬝ᵥx)):=(by simp only[H,a7,u,i,c,x,dotProduct];have hs:∑j,-(√a/d)*aH j*y j=-(2*√a)*(∑j,aH j*((y j+d)/(2*d)))+2*√a*(∑j,aH j/2):=(by rw[xw,xw,<-QS];exact xu rfl λ_ _=>by field_simp[g.ne'];ring);rw[hs];field_simp[p.ne'];ring);rw[a8,xl,XA,Qw (Qj Qi p)];refine (Q (b9 x c8) (Qk Qi.le p.le)).trans ?_
  have a1:(J.card:R)≠0:=(by exact_mod_cast I.card_pos.ne');rw[show 2*√a*(32*a^4*((2*m:ℕ):R)^k/(((2*m:ℕ):R)*J.card))=32*2^k*√a*a^4*b^k/(b*J.card) by dsimp[b];push_cast;rw[QL];field_simp[e.ne',a1]];exact (Xo (by positivity) (by positivity) (Q c3 e.le)).trans_eq (by dsimp[o,qn,a,b] at e ⊢;rw[xB];field_simp[e.ne',a6.ne',c1.ne'];ring)
 refine⟨v,d1,c,i,P,λj=>?_⟩;let z:R:=if 0<=c j then 1 else -1;have A:|z|=1:=by simp only[z];split_ifs<;>norm_num
 have a9:z*c j=|c j|:=by simp only[z];split_ifs with h<;>[rw[Qx,QF h];rw[neg_one_mul,Xh (xU.mp h)]]
 let w:V (k+1):=λr=>if r=j then q j-z*(d/(2*b)) else q r;let B:V (k+1):=w+(z*(d/b))•E j;have b0:∀r,|w r-q r|<=d/(2*b):=λr=>by
  by_cases h:r=j
  · subst h;simp only[w,↓reduceIte,sub_sub_cancel_left,XA,xl,A,Qx,Qw (QG g (Qj Qi e))];exact xo
  · simp[w,h];positivity
 have b1:∀r,|B r-q r|<=d/(2*b):=λr=>by
  by_cases h:r=j
  · subst h;simp only[B,w,Qt,Qh,X,E,xa,QR,↓reduceIte];rw[show q r-z*(d/(2*b))+z*(d/b)-q r=z*(d/(2*b)) by ring,xl,A,Qx,Qw (QG g (Qj Qi e))]
  · simp[B,w,E,h];positivity
 have b2:∀r,|w r|<=d:=λr=>by
  by_cases h:r=j
  · subst h;simp only[w,↓reduceIte,q,qd,z];let t:R:=(v r:ℕ);have h0:0<=t:=Qz _;have b3:t+1<=2*b:=(by have h1:(((v r:ℕ)+1:ℕ):R)<=((2*m:ℕ):R):=(by exact_mod_cast (v r).isLt);dsimp[b,t];push_cast at h1 ⊢;linarith);have b4:(2*b)*(d/b)=2*d:=(by field_simp[e.ne']);split_ifs
    · rw[show -d+(t+1/2)*(d/b)-1*(d/(2*b))=-d+t*(d/b) by ring,Qr];constructor<;>nlinarith only[h0,b3,QG g e,b4]
    · rw[show -d+(t+1/2)*(d/b) - -1*(d/(2*b))=-d+(t+1)*(d/b) by ring,Qr];constructor<;>nlinarith only[h0,b3,QG g e,b4]
  · simpa[w,h,q,qd] using qN g e v r
 have b5:∀r,|B r-w r|<=d/b:=λr=>by
  by_cases h:r=j
  · subst h;simp only[B,Qt,Qh,X,E,xa,QR,QA,xl,A,Qx,Qw (QG g e)];exact xo
  · simp[B,E,h];positivity
 have b6:=(Qr.mp (qS g c5 a4 a5 b2 b5)).2;have b7:=Qr.mp (P w b0);have b8:=Qr.mp (P B b1);have a2:u B-u w=|c j| *(d/b):=(by simp only[u,add_sub_add_left_eq_sub,<-QZ,show B-w=(z*(d/b))•E j by ext r;simp[B]];rw[QK,X,show c⬝ᵥE j=c j by simp[E],<-a9];ring)
 have h1:=Q (show |c j| *(d/b)<=2*√a/b+2*o by linarith only[b6,b7.2,b8.1,a2]) e.le;have h2:b*(|c j| *(d/b))=|c j| *d:=by field_simp[e.ne']
 have h3:b*(2*√a/b+2*o)=2*√a+2*b*o:=(by field_simp[e.ne']);rw[Y g];linarith only[h1,h2,h3,c2]
lemma Qg (k:ℕ){ε e:R}(a5:0< e)(b8:e<=ε)(d0:e<=1/(((k+2:ℕ):R)+1)):let d:R:=(k+2:ℕ);let y:=e/20;let w:=((k+1:ℕ):R)/(((k+1:ℕ):R)+2);let i:=3/(10*(d+1));∀ᶠ f in xy (0:R) (xP 0),∀(K:R) (L m:ℕ),1<=L->(L:R)<=4*log (1/f)->f^(-i)<=m->(m:R)<=2*f^(-i)->1<=m->let l:=qf (k+1)*f^y;(0< K->1/((2:R)^(k+2)*L)<=K->K<=(m:R)^w->let v:=qq k*K*L*l^(k+1)/(m:R)^(k+3);f<=v/\v<=f^y/\v^(w+ε)<=(qe (k+1)/(4*L))*(K*l^(k+1)/(m:R)^(k+1)))/\((m:R)^w< K->let v:=2*√d*l^(k+1)/(m:R)^(k+2);f<=v/\v<=f^y/\v^(w+ε)<=(qe (k+1)/(4*L))*(K*l^(k+1)/(m:R)^(k+1))):=by
 intro d y w i;let n:R:=(k+1:ℕ);let j:=qf (k+1);let z:=qe (k+1);let o:=qq k;let p:=w+e;let q:=1-w-e;have b3:0< d:=(by positivity);have b9:(2:R)<=d:=(by dsimp[d];exact_mod_cast (by omega:2<=k+2));have r:0< d+1:=(by linarith);have c0:0< √d:=xe.mpr b3;have b4:0< y:=(by positivity);have a8:(1:R)<=√d:=(by rw[le_sqrt (by norm_num) b3.le];linarith);have b5:p< 1:=(by have:w+1/(d+1)=d/(d+1):=(by simp only[w,d];push_cast;field_simp[r.ne'];ring);linarith[(Xg r).mpr (by linarith:d< d+1)]);have e7:1-w=2/(d+1):=(by simp only[w,d];push_cast;field_simp[r.ne'];ring);have d1:0< q:=(by linarith[QG QW r,show 2/(d+1)-1/(d+1)=1/(d+1) by ring]);have f0:0< j:=(by unfold j qf qa;positivity);have N:0< o:=(by unfold o qq qn;positivity);have c1:1<=o:=(by have h2:=QJ (QJ (xp (by norm_num:(1:R)<=2) (n:=k)) a8) (xp (by linarith:(1:R)<=d) (n:=4));unfold o qq qn;linarith only[h2,show 2*(64*(2:R)^k*√d*d^4)=128*((2:R)^k*√d*d^4) by ring]);have f1:0< z:=qt (k+1);have e8:n*y<=1/20:=(by have c2:y<=1/(20*(d+1)):=(by simp only[y];rw[Qm (by norm_num) (by positivity)];linarith[(Y r).mp d0]);exact (Q c2 (by positivity)).trans (by rw[mul_one_div,Qm (by positivity) (by norm_num)];simp only[n,d];push_cast;linarith));have f2:d*i< 3/10:=by simp only[i];rw[mul_div_assoc',div_lt_div_iff₀ (by positivity) (by norm_num)];linarith
 filter_upwards [self_mem_nhdsWithin,qO (1/16) (by norm_num),
  qm j 1 QW b4,
  qp (2^(k+3)) (o*j^(k+1)/2^(k+2)) (by positivity) (by linarith:n*y< 7/10) 0,
  qE (4*o*j^(k+1)) 1 QW (by positivity:(0:R)< i),
  qp (256*o*2^(k+2)) (z*j^2) (by positivity) (by linarith:-(e/5)< 0) 3,
  qp (2^(k+2)) (2*√d*j^(k+1)) (by positivity) (by linarith:n*y< 1-d*i) 0,
  qm (2*√d*j^(k+1)) 1 QW (by positivity:(0:R)< d*i),
  qp (32*√d) (z*j^2) (by positivity) (by linarith:-(e/10)< 0) 1]
  with f (c:(0:R)< f) d9 e0 e1 e2 e3 e4 e5 e6
 intro K L m c6 a4 a7 c7 b2 l;let b:R:=m;let s:R:=L;let u:=l^(k+1);let g:=log (1/f);have P:f< 1:=(by linarith);have B:0< l:=(by positivity);have h:0< b:=qb b2;have d2:(1:R)<=b:=qC b2;have J:0< s:=qb c6;have c3:(1:R)<=s:=qC c6;have f3:0< g:=log_pos (by rw[xd c];linarith);have b6:u=j^(k+1)*f^(n*y):=(by simp only[u,l,j,n,QL];congr 1;rw[<-Qp,<-QC c.le];congr 1;ring);have a9:u<=j^(k+1)*f^y:=(by simp only[u,l,j,QL];gcongr;rw[<-Qp];simpa using Qn (W c y) (rpow_lt_one c.le P b4).le (by exact_mod_cast (by omega:1<=k+1):(1:R)<=((k+1:ℕ):R)));have b0:u=u^p*l^(n*q):=(by dsimp[u];rw[<-Qp l (k+1),<-QC B.le,<-QQ B];congr 1;simp only[n,p,q];ring);have e9:j^2*f^(e/10)<=l^(n*q):=(by have f4:n*(2/(d+1))<=2:=(by rw[mul_div_assoc',Z r];simp only[n,d];push_cast;linarith);have H:l^2<=l^(n*q):=(by simpa[rpow_two] using Qn B (by simpa[l,j] using e0) (by nlinarith:n*q<=2));rwa[show l^2=j^2*f^(e/10) by simp only[l,j,QL];congr 1;rw[<-Qp,<-QC c.le];congr 1;simp only[y];push_cast;ring] at H);have b1:∀ {x},0< x->x<=f^y->x^(w+ε)<=x^p:=λhx hl=>
  Qn hx (Xk hl (rpow_lt_one c.le P b4)).le (by linarith only[b8])
 constructor
 · intro c8 c9 d7 v;have a0:f<=v:=by
    have d3:1/(2:R)^(k+2)<=K*s:=(Z (by positivity)).mpr (by linarith[(Z (by positivity:0< (2:R)^(k+2)*s)).mp c9]);have a1:b^(k+3)<=(2:R)^(k+3)*f^(-(3:R)/10):=
     (Ql h.le c7 (k+3)).trans_eq (by rw[QL,<-Qp (f^(-i)),<-QC c.le];congr 2;simp only[i,d];push_cast;field_simp[r.ne'];ring)
    rw[Y (QE h _)];have H:f*b^(k+3)<=(2:R)^(k+3)*f^(7/10:R):=
     (Q a1 c.le).trans_eq (by rw[xq,qJ c];congr 2;norm_num)
    exact (H.trans (by simpa[b6,xE,QN,Xe,xq] using e1:_<=o*(1/2^(k+2))*u)).trans (by linarith only[T (Q d3 N.le) (QM B.le (k+1))])
   have A:v<=f^y:=(by have d4:K/b^(k+3)<=1/b:=(by have H:b^w<=b^(k+2):=(by rw[<-Qp b (k+2)];exact xg d2 (by linarith only[b5,a5,b9,show (k+2:R)=d by simp only[d];push_cast;ring]));rw[Qm (QE h _) h,Qx,xB];exact T (d7.trans H) h.le);have b7:1/b<=f^i:=(Z h).mpr (by linarith only[qs (a:=i) c,Q a7 (W c i).le]);have H:=QD (QD (Q a4 N.le) a9 (QM B.le _) (by positivity)) (d4.trans b7) (by positivity) (by positivity);have h2:=T (by simpa[g] using e2:4*o*j^(k+1)*g*f^i<=1) (W c y).le;linarith only[H,h2,show v=o*s*u*(K/b^(k+3)) by simp only[v,o,u,b,s];ring]);refine⟨a0,A,(b1 (by positivity) A).trans ?_⟩;have a2:v^p=(K^p*u^p/b^(k+1))*((o*s)^p/b^((d+1)*e)):=(by have I:(b^(k+3))^p=b^(k+1)*b^((d+1)*e):=(by rw[<-Qp b (k+3),<-QC h.le,<-Qp b (k+1),<-QQ h];congr 1;simp only[p,w,d];push_cast;field_simp[r.ne'];ring);simp only[v];rw[div_rpow (by positivity) (by positivity),Xd (by positivity) (QM B.le _),Xd (by positivity) J.le,Xd N.le c8.le,I,Xd N.le J.le];ring);have a3:(z/(4*s))*(K*u/b^(k+1))=(K^p*u^p/b^(k+1))*((z/(4*s))*K^q*l^(n*q)):=by
    conv_lhs=>rw[show K=K^p*K^q by rw[<-QQ c8,show p+q=1 by simp only[p,q];ring,xQ],b0]
    ring
   rw[a2,a3];gcongr;rw[Z (W h _)];let s1:R:=(2:R)^(k+2)*s;let t1:R:=4*2^(k+2)*g;have d5:0< t1:=(by positivity);have H:(o*s)^p*(4*s)<=64*o*g^2:=(by have d6:(o*s)^p<=o*s:=(by simpa using xg (QJ c1 c3) b5.le);linarith only[QD (d6.trans (Q a4 N.le)) (by linarith only[a4]:4*s<=16*g) (by positivity) (by positivity),show o*(4*g)*(16*g)=64*o*g^2 by ring]);have h2:1/t1<=K^q:=
    (xs (by positivity) (by linarith only[Q a4 (QM Qi.le (k+2))]:s1<=t1)).trans
     ((by simpa[s1] using Qn (show 0< 1/s1 by positivity) ((xI (by positivity)).mpr (QJ (xp (by norm_num)) c3)) (show q<=1 by linarith only[a5,show 0<=w by unfold w;positivity]):1/s1<=_).trans (xz (by positivity) c9 d1.le))
   have h4:f^(-(3:R)*e/10)<=b^((d+1)*e):=(by have a6:=xz (W c _).le a7 (by positivity:0<=(d+1)*e);rwa[<-QC c.le,show -i*((d+1)*e)=-(3:R)*e/10 by simp only[i];field_simp[r.ne']] at a6);have h5:(o*s)^p*(4*s)<=z*K^q*l^(n*q)*b^((d+1)*e):=(by have c4:64*o*g^2<=z*j^2*f^(-(e/5))/t1:=(Y d5).mpr (by linarith only[show 256*o*2^(k+2)*g^3<=z*j^2*f^(-(e/5)) by simpa[g] using e3,show 64*o*g^2*t1=256*o*2^(k+2)*g^3 by simp only[t1];ring]);have t:z*(1/t1)*(j^2*f^(e/10)*f^(-(3:R)*e/10))<=z*K^q*(l^(n*q)*b^((d+1)*e)):=(by gcongr);rw[QN (j^2),<-QQ c,show e/10+-(3:R)*e/10=-(e/5) by ring] at t;linarith only[H,c4,t,show z*(1/t1)*(j^2*f^(-(e/5)))=z*j^2*f^(-(e/5))/t1 by ring]);exact ((Y (Qj (by norm_num) J)).mpr h5).trans_eq (by ring)
 · intro d8 v;have a0:f<=v:=by
    have a1:b^(k+2)<=(2:R)^(k+2)*f^(-(d*i)):=(Ql h.le c7 (k+2)).trans_eq (by rw[QL,<-Qp (f^(-i)),<-QC c.le];congr 2;simp only[d];ring);rw[Y (QE h _)];exact ((Q a1 c.le).trans_eq (by rw[xq,qJ c,<-Xi])).trans (by dsimp[u] at b6;simpa[b6,QN,Xe,xq] using e4)
   have A:v<=f^y:=by
    have b7:1/b^(k+2)<=f^(d*i):=(Z (QE h _)).mpr (by
     have H:f^(-(d*i))<=b^(k+2):=by have:=Ql (W c _).le a7 (k+2);rwa[<-Qp (f^(-i)),<-QC c.le,show -i*((k+2:ℕ):R)=-(d*i) by simp only[d];ring] at this
     linarith only[qs (a:=d*i) c,Q H (W c (d*i)).le])
    have H:=QD (Q a9 (Qk Qi.le c0.le)) b7 (by positivity) (by positivity);have h2:=T (by simpa using e5:2*√d*j^(k+1)*f^(d*i)<=1) (W c y).le;linarith only[H,h2,show v=2*√d*u*(1/b^(k+2)) by simp only[v,u,b];ring]
   refine⟨a0,A,(b1 (by positivity) A).trans ?_⟩;have a2:v^p=(u^p/b^(k+1))*((2*√d)^p*b^w/b^(d*e)):=(by have I:(b^(k+2))^p*b^w=b^(k+1)*b^(d*e):=(by rw[<-Qp b (k+2),<-QC h.le,<-QQ h,<-Qp b (k+1),<-QQ h];congr 1;simp only[p,w,d];push_cast;field_simp[r.ne'];ring);simp only[v];rw[div_rpow (by positivity) (by positivity),Xd (Qk Qi.le c0.le) (QM B.le _),div_mul_div_comm,div_eq_div_iff (W (QE h (k+2)) _).ne' (Qj (QE h (k+1)) (W h _)).ne'];linear_combination -(2*√d)^p*u^p*I);have a3:(z/(4*s))*(K*u/b^(k+1))=(u^p/b^(k+1))*((z/(4*s))*K*l^(n*q)):=(by (conv_lhs=>rw[b0]);ring);rw[a2,a3];gcongr;rw[Z (W h _)];have H:(2*√d)^p*(4*s)<=32*√d*g:=(by have c5:(2*√d)^p<=2*√d:=(by simpa using xg (by linarith only[a8]:(1:R)<=2*√d) b5.le);linarith only[QD c5 (by linarith only[a4]:4*s<=16*g) (by positivity) (by positivity)]);have h3:f^(-(e/5))<=b^(d*e):=(by have a6:=xz (W c _).le a7 (Qk b3.le a5.le);rw[<-QC c.le] at a6;have hf:(2:R)/3<=d/(d+1):=(by rw[Qm (by norm_num) r];linarith only[b9]);exact (Qn c P.le (by rw[show -i*(d*e)=-(3/10)*(d/(d+1))*e by simp only[i,xE,mul_inv];ring];nlinarith only[hf,a5])).trans a6);have h4:(2*√d)^p*(4*s)<=z*l^(n*q)*b^(d*e):=(by have t:z*(j^2*f^(e/10)*f^(-(e/5)))<=z*(l^(n*q)*b^(d*e)):=(by gcongr);rw[QN (j^2),<-QQ c,show e/10+-(e/5)=-(e/10) by ring] at t;linarith only[H,show 32*√d*g<=z*j^2*f^(-(e/10)) by simpa[g] using e6,t]);have h5:(2*√d)^p<=(z/(4*s))*l^(n*q)*b^(d*e):=((Y (Qj (by norm_num) J)).mpr h4).trans_eq (by ring);exact (QD h5 d8.le (W h w).le (by positivity)).trans_eq (by ring)
end m5
section
open Finset Matrix Real MeasureTheory m5
theorem nd1 {δ : ℝ} (hδ : δ < 1 / 2) {A : Finset (ZV 1)} (hA : A.Nonempty) :
    ¬ DCP δ A := by
 intro J;let c:=A.filter λa=>A.card<=2*(A.filter λx=>x 0<=a 0).card;obtain⟨H,m,g⟩:=xb A (λx=>x 0) hA;obtain⟨a,n,h⟩:=exists_min_image c (λx=>x 0) ⟨H,U.mpr ⟨m,by rw[filter_true_of_mem λx d=>g x d];omega⟩⟩;obtain⟨o,p⟩:=U.mp n;have k:A.card<=2*(A.filter λx=>a 0<=x 0).card:=by
  let L:=A.filter λx=>x 0< a 0;have e:L.card+(A.filter λx=>a 0<=x 0).card=A.card:=by simpa[L,not_lt] using card_filter_add_card_filter_not (s:=A) (λx=>x 0< a 0)
  by_cases y:L.Nonempty
  · obtain⟨b,j,q⟩:=xb L (λx=>x 0) y;have l:b ∉ c:=λw=>xU.mpr (U.mp j).2 (h b w);simp only[c,U,(U.mp j).1,true_and,xU] at l;have:=QP (show L⊆A.filter λx=>x 0<=b 0 from λx d=>U.mpr ⟨(U.mp d).1,q x d⟩);omega
  · rw[not_nonempty_iff_eq_empty.mp y,card_empty] at e;omega
 obtain⟨u,r,I⟩:=J a o;have z:u 0≠0:=λK=>r (funext λi=>Subsingleton.elim i 0▸K);have B:(0:R)< A.card:=(by exact_mod_cast hA.card_pos);have f:∀(P:ZV 1->Prop) [DecidablePred P],A.card<=2*(A.filter P).card->(∀x∈A.filter P,(0:R)<=u 0*((x 0-a 0:ℤ):R))->False:=λP _ N hs=>(by have h1:(A.card:R)<=2*((A.filter P).card:R):=(by exact_mod_cast N);have h2:((A.filter P).card:R)<=((A.filter λx=>(0:R)<=∑i:F 1,u i*((x i-a i:ℤ):R)).card:R):=(by exact_mod_cast QP λx d=>U.mpr ⟨(U.mp d).1,by rw[Fin.sum_univ_one];exact hs x d⟩);nlinarith)
 rcases lt_or_gt_of_ne z with t | v
 · exact f _ p λx d=>mul_nonneg_of_nonpos_of_nonpos t.le (by exact_mod_cast sub_nonpos.mpr (U.mp d).2)
 · exact f _ k λx d=>Qk v.le (by exact_mod_cast xx.mpr (U.mp d).2)
open Classical in
theorem lc1 (d : ℕ) (hd : 2 ≤ d) (ε : ℝ) (hε : 0 < ε) :
    ∃ (τ δ₀ c_rad : ℝ), 0 < τ ∧ τ < 1 ∧ 0 < δ₀ ∧ 0 < c_rad ∧
      ∀ (δ : ℝ), 0 < δ → δ < δ₀ →
        ∀ (A : Finset (RV d)),
          (∀ x ∈ A, ∀ i : Fin d, -1 ≤ x i ∧ x i ≤ 1) →
          DCPR δ A →
          (2 : ℝ) / δ ≤ (A.card : ℝ) →
          ∃ (η : ℝ) (x₀ : RV d) (K₀ : Set (RV d)),
            δ ≤ η ∧ η ≤ δ ^ τ ∧
            (0 : RV d) ∈ K₀ ∧ Convex ℝ K₀ ∧ (∀ x ∈ K₀, -x ∈ K₀) ∧
            Bornology.IsBounded K₀ ∧
            (∀ x : RV d, (∀ i, |x i| ≤ c_rad * δ ^ ((1 : ℝ) / (d : ℝ))) → x ∈ K₀) ∧
            MeasureTheory.volume K₀ ≤ ENNReal.ofReal (η * (2 : ℝ) ^ d) ∧
            ((A.filter (fun x => x - x₀ ∈ K₀)).card : ℝ) ≥
              η ^ (((d : ℝ) - 1) / ((d : ℝ) + 1) + ε) * (A.card : ℝ) := by
 rcases d with _ | _ | k
 · omega
 · omega
 let d:R:=(k+2:ℕ);have c2:0< d:=(by positivity);have c3:(2:R)<=d:=(by dsimp[d];exact_mod_cast (by omega:2<=k+2));have z:0< d+1:=(by linarith);have a6:0< √d:=xe.mpr c2;let e:=min ε (1/(d+1));have f7:0< e:=lt_min hε (by positivity);have b5:e<=ε:=min_le_left _ _;have d7:e<=1/(d+1):=xR _ _;let τ:=e/20;have H:0< τ:=(by positivity);have d8:τ<=1/(20*(d+1)):=(by simp only[τ];rw[Qm (by norm_num) (by positivity)];have:=(Y z).mp d7;linarith);have b6:τ< 1:=(by linarith[d8,show 1/(20*(d+1))< 1 by rw[Xg (by positivity)];linarith]);let α:=((k+1:ℕ):R)/(((k+1:ℕ):R)+2);have c4:((↑(k+2):R)-1)/((↑(k+2):R)+1)=α:=(by simp only[α];push_cast;ring);let l:=3/(10*(d+1));have k9:0< l:=(by positivity);let cU:=qf (k+1);let q:=qn k;let cn:=qe (k+1);have l2:0< qa (k+1):=(by unfold qa;positivity);have c5:0< cU:=(by unfold cU qf;positivity);have c6:0< q:=(by unfold q qn;positivity);have f8:0< cn:=qt (k+1);have l0:1/(20*(d+1))+2*l< 1/d:=(by rw[show 1/(20*(d+1))+2*l=13/(20*(d+1)) by simp only[l];field_simp[z.ne'];ring,div_lt_div_iff₀ (by positivity) c2];linarith);have l3:0< 1/(20*(d+1)):=(by positivity);have f9:τ< 1/d:=(by linarith);have g0:τ+l< 1/d:=(by linarith);have g1:2*l< 1/d - τ:=(by linarith);have d9:l< 1/d:=(by linarith);have g2:∀ᶠ δ in xy (0:R) (xP 0),∀(A:S (V (k+2))),
     (∀x∈A,∀i,-1<=x i/\x i<=1)->DCPR δ A->(2:R)/δ<=A.card->qD (k+1) ε τ δ A:=by
  filter_upwards [self_mem_nhdsWithin,qO (1/16) (by norm_num),
   qm 8 1 QW (by positivity:(0:R)< 1/d),
   qm (√d) (1/qa (k+1)) (by positivity) f9,
   qE 8 1 QW (by positivity:(0:R)< τ*(α+e)),
   qm cU 1 QW H,
   qp (2*d+1) 1 QW (by linarith:-l< 0) 0,
   qE (8*q) (√d) a6 (by positivity:(0:R)< 6/(10*(d+1)^2)),
   qm (32*√d) (cU/4) (by positivity) g0,
   qm (128*d^2*√d/cU) (q/(4*2^(k+2))) (by positivity) g1,
   qm (32*√d) (√d/2) (by positivity) d9,
   Qg k f7 b5 d7]
   with δ (j:(0:R)< δ) d6 h1 h2 h3 h4 h5 h6 h7 h8 k8 f6
  intro A d4 d5 b4;have a7:(0:R)< A.card:=Qs (by positivity) b4;obtain⟨r,L,k',μ,Ab,P,xb,j2,j3,a1,b0,j4,j5,b9,j6,j7,c8,c9,e5,d0,e6,j8,c0,e7,j9,w⟩:=
   Qc (by omega:2<=k+2) j d6 (by simpa[d] using h1) A d4 d5 b4
  by_cases d3:∃u:V (k+2),O u=1/\∀x∈P,∀y∈P,u⬝ᵥ(x-y)< δ^τ/qa (k+1)
  · obtain⟨u,k0,k1⟩:=d3;exact Qd b5 H b6 j (by linarith) (by simpa[d,Nat.add_assoc] using h1) (by rw[show (((k+1)+1:ℕ):R)=d from rfl];simpa[div_eq_inv_mul] using h2) (by simpa[α] using h3) a1 b0 A a7 Ab c8 c9 d0 P e6 c0 e7 j9 u k0 k1
  · push Not at d3;let m:=Nat.ceil (δ^(-l));let b:R:=m;let LL:R:=L;have c7:δ^(-l)<=b:=Nat.le_ceil _;have a8:2*d+1<=δ^(-l):=(by simpa using h5);have e0:2*(k+2)< m:=(by exact_mod_cast (by dsimp[d] at a8;push_cast at a8 ⊢;linarith only[a8,c7]:((2*(k+2):ℕ):R)< m));have a9:b<=2*δ^(-l):=(by linarith only[a8,c3,xG (W j (-l)).le]);obtain⟨cc,g,Ig,h,ci,J,K,e8,e9,f0,f1,f2,f3,c1,b1,f4,k2,k3⟩:=
     Qe (by omega) j (by simpa[cU] using h4) a1 j4 j5 j7 (by omega:1<=m) P e6 j8 c0 e7 d3 xb (λi=>(w i).1) (λi=>(w i).2.2)
    let o:=cU*δ^τ;let c:=2*√d*r;have p:0< o:=Qj c5 (W j τ);have n:0< b:=qb (by omega);have b7:0< LL:=qb a1;have I:c<=32*√d*δ^((1:R)/d):=(by simp only[c,d];nlinarith only[j3,a6]);have N:√d*δ^((1:R)/d)<=c:=(by simp only[c,d];nlinarith only[j2,a6,W j ((1:R)/d)]);have e1:0<=c:=le_trans (Qk a6.le (W j _).le) N;have b8:c<=o/(2*b):=(by have g3:(cU/4)*δ^(τ+l)<=o/(2*b):=(Y (Qj Qi n)).mpr ((Q (by linarith only[a9]:2*b<=4*δ^(-l)) (Qk (Qq c5.le (by norm_num)) (W j _).le)).trans_eq (by rw[QQ j];simp only[o];linear_combination (cU*δ^τ)*qs (a:=l) j));linarith only[I,h7,g3]);have t:∀v∈J,(cn/(4*LL))*(K*o^(k+1)/b^(k+1))*A.card<=∑i∈Ig.filter λi=>ci i=v,((Ab i).card:R):=λv a2=>(by let f:=Ig.filter λi=>ci i=v;have s:(f.card:R)*(μ*A.card)<=∑i∈f,((Ab i).card:R):=(by rw[xt,QX]:_=∑_i∈f,(μ*A.card)).trans_le (Qv λi _=>e5 i);have g4:=(Qo (Q ((Q j6 (Qk f8.le (QM p.le _))).trans e9) b1.le) (QM n.le _)).trans (k3 v a2);exact (show (cn/(4*LL))*(K*o^(k+1)/b^(k+1))*A.card=_ by simp only[xE,Qx,mul_inv];linear_combination -(K*cn*o^(k+1)*(4:R)⁻¹*LL⁻¹*(b^(k+1))⁻¹*A.card)*inv_mul_cancel₀ b9.ne').trans_le ((T g4 (Qk b9.le a7.le)).trans s));obtain⟨k4,k5⟩:=f6 K L m a1 b0 c7 a9 (by omega)
    by_cases b3:K<=b^α
    · have g5:2*b*(q*K*LL/b^2)<=√d:=by
       have g6:K/b<=b^(-(2:R)/(d+1)):=(Qo b3 n.le).trans_eq (by (conv_lhs=>arg 2;rw[<-xQ b]);rw[<-rpow_sub n];congr 1;simp only[α,d];push_cast;field_simp[z.ne'];ring);have e2:b^(-(2:R)/(d+1))<=δ^(6/(10*(d+1)^2)):=(by have s:=rpow_le_rpow_of_nonpos (W j (-l)) c7 (show -(2:R)/(d+1)<=0 by rw[neg_div];linarith only[QG Qi z]);rwa[<-QC j.le,show -l*(-(2:R)/(d+1))=6/(10*(d+1)^2) by simp only[l];field_simp[z.ne'];ring] at s);have s:=QD (Q b0 (Qk Qi.le c6.le)) (g6.trans e2) (Qq b1.le n.le) (Qk (Qk Qi.le c6.le) (by linarith only[b0,b7]));linarith only[s,show 2*b*(q*K*LL/b^2)=2*q*LL*(K/b) by field_simp[n.ne'],show 8*q*log (1/δ)*δ^(6/(10*(d+1)^2))<=√d by simpa using h6]
      obtain⟨v,a2,d1,d2,k6,k7⟩:=Qf p a1 e0 b1 g5 h f0 f1 J c1 k2;let err:=q*K*LL/b^2;let η:=qq k*K*LL*o^(k+1)/b^(k+3);obtain⟨a3,a4,a5⟩:=k4 b1 f4 b3;have g7:(1+((k+1:ℕ):R)*(3*√d/o))*c<=err:=by
       have g8:1+((k+1:ℕ):R)*(3*√d/o)<=4*d^2/o:=by
        have e3:√d<=d:=(QO (by nlinarith only[c3])).trans_eq (xN c2.le);have s:1<=1/o:=(one_le_div p).mpr (by simpa[o,cU] using h4);exact (by linarith only[s,show 1/o+((k+1:ℕ):R)*(3*√d/o)=(((k+1:ℕ):R)*(3*√d)+1)/o by ring]:_<=(((k+1:ℕ):R)*(3*√d)+1)/o).trans
         (Qo (by have g9:((k+1:ℕ):R)<=d:=(by simp only[d];push_cast;linarith);nlinarith only[g9,e3,c3]) p.le)
       have h0:1/(2:R)^(k+2)<=K*LL:=(Z (QE Qi _)).mpr (by linarith only[(Z (Qj (QE Qi _) b7)).mp f4]);have h9:(q/(4*2^(k+2)))*δ^(2*l)<=err:=(by have j0:b^2<=4*δ^(-(2*l)):=(Ql n.le a9 2).trans_eq (by rw[QL,<-Qp (δ^(-l)),<-QC j.le];norm_num;congr 2;ring);rw[Y (QE n 2)];linarith only[Q j0 (by positivity:0<=q/(4*2^(k+2))*δ^(2*l)),show q/(4*2^(k+2))*δ^(2*l)*(4*δ^(-(2*l)))=q*(1/2^(k+2)) by linear_combination (q/2^(k+2))*qs (a:=2*l) j,Q h0 c6.le]);have j1:(4*d^2/o)*c<=(q/(4*2^(k+2)))*δ^(2*l):=
        ((Q I (by positivity)).trans_eq (by simp only[o];rw[rpow_sub j];field_simp[c5.ne',(W j τ).ne'];ring)).trans h8
       exact (T g8 e1).trans (j1.trans h9)
      have a0:(2*(o/b))^(k+1)*(2*(2*err))=η*2^(k+2):=(by simp only[η,qq,q,err,QL,Xc,xB];ring);exact qT j p n N b8 (by positivity) g7 xo (by positivity) a0 a3 a4 A Ab c8 c9 cc g e8 xb (λi=>(w i).2.1) Ig h f2 ci f3 v d1 d2 k6 k7 ((T a5 a7.le).trans (t v a2))
    · push Not at b3;obtain⟨v,a2⟩:=c1;let η:=2*√d*o^(k+1)/b^(k+2);obtain⟨a3,a4,a5⟩:=k5 b3;have e4:c<=√d/b:=(by linarith only[I,k8,(Y n).mpr ((Q a9 (by positivity)).trans_eq (by linear_combination √d*qs (a:=l) j):√d/2*δ^l*b<=√d)]);have a0:(2*(o/b))^(k+1)*(2*(2*√d/b))=η*2^(k+2):=by
       simp only[η,QL,Xc,xB];ring
      exact qT (B:=0) (err:=√d/b) (hr:=2*√d/b) j p n N b8 xo (by linarith only[e4]) (by ring_nf;exact xo) (by positivity) a0 a3 a4 A Ab c8 c9 cc g e8 xb (λi=>(w i).2.1) Ig h f2 ci f3 v 0 (h (qd o m v))
       (λy hy=>by
        rw[xA,xC]
        exact (qS p (by exact_mod_cast (by omega:1<=2*m):(1:R)<=((2*m:ℕ):R)) f0 f1 (qN p n v) (by simpa[Nat.cast_mul,qd] using hy)).trans_eq (by dsimp[b,d];push_cast;field_simp[n.ne'];rw[show (k:R)+1+1=(k:R)+2 by ring]))
       (λ_=>by simp) ((T a5 a7.le).trans (t v a2))
 obtain⟨δ₀,b2,f5⟩:=xj.mp (xk.mp g2);refine⟨τ,δ₀,1,H,b6,b2,QW,fun δ j l1 A d4 d5 b4=>?_⟩;rw[c4];exact f5 (by rwa[xS,xh,Qw j]) j A d4 d5 b4
end
end E186
namespace E186
noncomputable section
open scoped Classical
open Real MeasureTheory Finset
abbrev M6R := @DCPR
abbrev M6D := DJH
abbrev M6C := CSH
def M6L:Prop:=∀(d:ℕ),2<=d->∀(e:ℝ),0< e->∃(t o r:ℝ),0< t/\t<1/\0< o/\0< r/\∀(p:ℝ),0< p->p< o->∀(A:Finset (RV d)),(∀ x∈A,∀ i:Fin d,-1<=x i/\x i<=1)->M6R p A->(2:ℝ)/p<=#A->∃(n:ℝ) (z:RV d) (K:Set (RV d)),p<=n/\n<=p^t/\(0:RV d)∈K/\Convex ℝ K/\(∀ x∈K,-x∈K)/\Bornology.IsBounded K/\(∀ x:RV d,(∀ i,|x i|<=r*p^((1:ℝ)/(d:ℝ)))->x∈K)/\volume K<=ENNReal.ofReal (n*(2:ℝ)^d)/\(#(A.filter fun x=>x-z∈K):ℝ) ≥ n^(((d:ℝ)-1)/((d:ℝ)+1)+e)*#A
def M6O:Prop:=∀(p:ℝ),p<1/2->∀(A:Finset (ZV 1)),A.Nonempty->¬ DCP p A
abbrev m61 d:=Finset (ZV d)
lemma m62 {t} [Mul t] [Zero t] [Preorder t] [PosMulMono t] {a b c:t}:a<=b->0<=c->c*a<=c*b:=mul_le_mul_of_nonneg_left
lemma m63 {t} [Mul t] [Zero t] [Preorder t] [MulPosMono t] {a b c:t}:a<=b->0<=c->a*c<=b*c:=mul_le_mul_of_nonneg_right
lemma m64 {a b} [AddCommMonoid b] {s:Finset a} {f g:a->b}:(∀ x∈s,f x=g x)->∑ x∈s,f x=∑ x∈s,g x:=sum_congr rfl
lemma m65 {n:ℕ}:(0:ℝ)<=n:=Nat.cast_nonneg n
lemma m66 {a b:ℝ}:0<=a->0<=b->0<=a*b:=mul_nonneg
abbrev m67 {d} {B:ZB d} {x}:=ZB.mTF B x
lemma m68 {t} [Semigroup t] (a b c:t):a*b*c=a*(b*c):=mul_assoc a b c
lemma m6A {a:ℝ}:0<=a->∀ n:ℕ,0<=a^n:=pow_nonneg
abbrev m6C {x}:=@rpow_mul x
lemma m6D {a:ℕ}:0< a->(0:ℝ)< a:=Nat.cast_pos.mpr
lemma m6E {a b} [DecidableEq b] {s:Finset a} {f:a->b} {y}:y∈s.image f->∃ x∈s,f x=y:=mem_image.mp
lemma m6F {a b c:ℝ}:0< c->(a<=b/c↔a*c<=b):=le_div_iff₀
abbrev m6G {x}:=@rpow_neg x
lemma m6I {a b c:ℝ}:0< c->(a/c<=b↔a<=b*c):=div_le_iff₀
lemma m6K {a} {s t:Finset a}:s⊆t->#s<=#t:=card_le_card
abbrev m6L {x}:=@rpow_add x
lemma m6P {a} {p:a->Prop} [DecidablePred p] {s:Finset a} {x}:x∈s.filter p->x∈s/\p x:=mem_filter.mp
lemma m6Q {a b:ℝ}:0<=a->a<=b->∀ n:ℕ,a^n<=b^n:=pow_le_pow_left₀
lemma m6R {a b:ℝ}:0<=a->0<=b->0<=a/b:=div_nonneg
lemma m6T {a b} [DecidableEq b] (s:Finset a) {f:a->b}:Function.Injective f->#(s.image f)=#s:=card_image_of_injective s
lemma m6U {a} {s t:Finset a}:s∈t.powerset->s⊆t:=mem_powerset.mp
abbrev m6V {x}:=@rpow_pos_of_pos x
abbrev m6W:=ENNReal.ofReal
abbrev m6X:=DecidableEq
lemma m6Y {t} [LinearOrder t] (a b:t):b<=max a b:=le_max_right a b
abbrev m6Z {x}:=@rpow_nonneg x
lemma m6a {a:ℕ}:1<=a->(1:ℝ)<=a:=Nat.one_le_cast.mpr
lemma m6c {t} [Preorder t] {a b c:t}:a< b->b<=c->a< c:=lt_of_lt_of_le
lemma m6d (a:ℝ):0<=a^2:=sq_nonneg a
lemma m6e {a b} [AddCommMonoid b] {s:Finset a} {f g:a->b}:∑ x∈s,(f x+g x)=∑ x∈s,f x+∑ x∈s,g x:=sum_add_distrib
lemma m6h {a} {p:a->Prop} [DecidablePred p] {s:Finset a}:s.filter p⊆s:=filter_subset p s
abbrev m6i {x y z}:=@rpow_le_rpow_of_exponent_le x y z
lemma m6j {a b:ℕ}:a<=b->(a:ℝ)<=b:=Nat.cast_le.mpr
lemma m6l {a:ℝ} (h:1<=a) {m n:ℕ} (i:m<=n):a^m<=a^n:=pow_le_pow_right₀ h i
lemma m6m {t} [LinearOrder t] (a b:t):a<=max a b:=le_max_left a b
abbrev m6q:=M6D
abbrev m6r {x y}:=@mul_rpow x y
lemma m6w {a b c:ℝ}:0<=a->0< b->b<=c->a/c<=a/b:=div_le_div_of_nonneg_left
lemma m6x {a:ℝ} (h:1<=a) {n:ℕ}:1<=a^n:=one_le_pow₀ h
abbrev m6y:=rpow_natCast
lemma m6z {t} [AddGroup t] {a:t}:Function.Injective (·-a):=sub_left_injective
lemma m6a0 (a b:ℝ):min a b<=a:=min_le_left a b
abbrev m6a5 {g} [AddGroup g] (s:Set g):=AddSubgroup.closure s
abbrev m6a6 {i m} [AddCommGroup m] [Module ℝ m] (v:i->m):=LinearIndependent ℝ v
abbrev m6ac {g} [AddCommGroup g] {d} {P:GAP g d}:=@GAP.sIC g _ d P
abbrev m6ad {x y z}:=@rpow_le_rpow x y z
lemma m6ae (a b:ℝ):a/b=a*b⁻¹:=div_eq_mul_inv a b
lemma m6al (n:ℕ):(0:ℝ)<=n:=Nat.cast_nonneg n
lemma m6am {a b:ℝ}:0<=a->1<=b->a<=b*a:=le_mul_of_one_le_left
abbrev m6az {x y z}:=@rpow_le_rpow_of_exponent_ge x y z
lemma m6b0 {a b c:ℝ}:a<=b->0<=c->a/c<=b/c:=div_le_div_of_nonneg_right
lemma m6b1 {a b:ℝ}:0<=a->1<=b->a<=a*b:=le_mul_of_one_le_right
abbrev m6bs {p q}:=@ENNReal.ofReal_le_ofReal p q
variable {G H : Type*} [AddCommGroup G] [AddCommGroup H] {hC : M6C} {J : ℕ -> ℕ}
def m6N (n:ℕ):ℕ:=⌊(n:ℝ)/(log n)^2⌋₊
lemma m6S {d:ℕ} (B:ZB d):(1:ℝ)<=B.vol:=m6a B.vP
lemma m6af {d:ℕ} (B:ZB d):(0:ℝ)< B.vol:=m6D B.vP
lemma m6ag {d:ℕ} {B:ZB d} {A:m61 d} (h:A⊆B.tF):(#A:ℝ)<=B.vol:=m6j ((m6K h).trans_eq B.cTF)
lemma m6s {n:ℕ} (c:ℝ) (f:Fin n->ℝ):c^n*∏ i,f i=∏ i,(c*f i):=by rw[prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]
lemma m6an {n:ℕ} (c:ℕ) (f:Fin n->ℕ):c^n*∏ i,f i=∏ i,(c*f i):=by rw[prod_mul_distrib,prod_const,card_univ,Fintype.card_fin]
lemma m6ao {a b c:ℝ} (d:0<=a) (e:0< b) (h:a^b<=c):a<=c^(1/b):=by have:=m6ad (m6Z d _) h (one_div_pos.mpr e).le;rwa[←m6C d,mul_one_div_cancel e.ne',rpow_one] at this
lemma m6ap {a b c:ℝ} (d:0<=a) (e:0< b) (h:a^b< c):a< c^(1/b):=by have:=rpow_lt_rpow (m6Z d _) h (one_div_pos.mpr e);rwa[←m6C d,mul_one_div_cancel e.ne',rpow_one] at this
lemma m6t {a b:ℝ} (d:0<=a) (n:ℕ):(a^(-b))^n=a^(-((n:ℝ)*b)):=by rw[←m6y _ n,←m6C d];congr 1;ring
lemma m6b2 {k a:ℕ} (hJ:1<=a) (N:Fin k->ℕ) (b:∀ i,1<=N i):(ZB.symm fun i=>a*N i).vol<=(3*a)^k*∏ i,(2*N i-1):=by
 simp only[ZB.vol];rw[m6an];refine prod_le_prod' fun i _=>?_;have:=b i;dsimp[ZB.symm,ZB.width];rw[←Nat.cast_mul,show ((a*N i:ℕ):ℤ) - -↑(a*N i)+1=↑(2*(a*N i)+1) by push_cast;ring,Int.toNat_natCast];have:2*N i-1+1=2*N i:=by omega
 nlinarith
lemma m6aq {d:ℕ} (B:ZB d) (k:Fin d):(B.width k:ℝ)=((B.hi k-B.lo k:ℤ):ℝ)+1:=by exact_mod_cast (Int.toNat_of_nonneg (by have:=B.hle k;omega):((B.width k:ℕ):ℤ)=B.hi k-B.lo k+1)
lemma m6ah {c x y:ℝ} {d:ℕ} (a:0< c) (h:(c/3)^d*x<=y):x<=(3/c)^d*y:=by
 have hi:(3/c)^d*(c/3)^d=1:=by rw[←mul_pow,show 3/c*(c/3)=1 by field_simp,one_pow]
 exact(by linear_combination x*hi.symm:x=_).trans_le (m62 h (by positivity))
lemma m6ar {d:ℕ} {P:GAP G d} (a:P.iS) (h:∀ i,1<=P.hi i) (i:Fin d):(P.cB.width i:ℝ)=2*P.hi i+1:=by exact_mod_cast (show ((P.cB.width i:ℕ):ℤ)=2*P.hi i+1 by simp only[GAP.cB,ZB.width,a.2 i];rw[Int.toNat_of_nonneg (by have:=h i;omega)];omega)
lemma m6ai {d k:ℕ} (w:Fin k->ZV d):Module.finrank ℝ (Submodule.span ℝ (Set.range fun i=>zR (w i)))<=k:=
 (finrank_span_le_card _).trans (by rw[Set.toFinset_range];exact card_image_le.trans (by simp))
lemma m6b3 {d l:ℕ} {P:GAP (ZV l) d} (a:P.base=0) {x:ZV l} (b:x∈P.tF):zR x∈Submodule.span ℝ (Set.range fun i=>zR (P.step i)):=by obtain ⟨v,_,rfl⟩:=m6E b;rw[GAP.eval,a,zero_add,zRu];exact Submodule.sum_mem _ fun i _=>by rw[zRm];exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
def m6M {d:ℕ} (B:ZB d) (t:ZV d):ZB d:=⟨fun i=>B.lo i+t i,fun i=>B.hi i+t i,fun i=>by have:=B.hle i;omega⟩
lemma m6b4 {d:ℕ} (B:ZB d) (t:ZV d) (i:Fin d):(m6M B t).width i=B.width i:=by simp only[m6M,ZB.width];congr 1;omega
lemma m6a7 {d:ℕ} (B:ZB d) (t:ZV d):(m6M B t).vol=B.vol:=prod_congr rfl fun i _=>m6b4 B t i
lemma m6a1 {d:ℕ} {B:ZB d} {x:ZV d} (h:x∈B.tF):(0:ZV d)∈(m6M B (-x)).tF:=
 m67.mpr fun i=>by have:=m67.mp h i;simp[m6M];omega
lemma m6a8 {d:ℕ} {B:ZB d} {A:m61 d} (h:A⊆B.tF) (x:ZV d):A.image (· - x)⊆(m6M B (-x)).tF:=fun y b=>by obtain ⟨z,a,rfl⟩:=m6E b;exact m67.mpr fun i=>by have:=m67.mp (h a) i;simp[m6M,sub_eq_add_neg];omega
def m6a9 {d:ℕ} (B:ZB d):GAP (ZV d) d:=⟨0,fun i=>Pi.single i 1,B.lo,B.hi,B.hle⟩
lemma m6b5 {d:ℕ} (B:ZB d):(m6a9 B).tF=B.tF:=by
 have a:∀ n,(m6a9 B).eval n=n:=fun n=>by ext j;simp[m6a9,GAP.eval];rw[sum_eq_single j] <;> simp (config:={contextual:=true})
 ext x;simp only[GAP.tF,mem_image];exact ⟨fun ⟨n,hn,h⟩=>by rw[←h,a];exact hn,fun b=>⟨x,b,a x⟩⟩
def m6H {d:ℕ} (P:GAP G d) (c:ℝ) (hc:0<=c) (hs:P.iS):GAP G d:=P.rS c hc (m6ac hs)
lemma m6aj {d:ℕ} {P:GAP G d} (hs:P.iS) (c:ℝ) (hc:0<=c):(m6H P c hc hs).iS:=
 ⟨rfl,fun i=>by simp[m6H,GAP.rS,hs.2 i,Int.ceil_neg]⟩
lemma m6bt {d:ℕ} {P:GAP G d} (hs:P.iS) (a:∀ i,1<=P.hi i) {c:ℝ} (e:1<=c):(c/3)^d*↑P.vol<=↑(m6H P c (by linarith) hs).vol:=by
 let Q:=m6H P c (by linarith) hs;have b:Q.iS:=m6aj hs c (by linarith);rw[GAP.vol,ZB.vol,Nat.cast_prod,m6s];simp only[GAP.vol,ZB.vol,Nat.cast_prod];refine prod_le_prod (fun _ _=>by positivity) fun i _=>?_
 have:(1:ℝ)<=P.hi i:=by exact_mod_cast a i
 have:c*P.hi i-1< Q.hi i:=by change c*P.hi i-1<(⌊c*(P.hi i:ℝ)⌋:ℝ);linarith[Int.lt_floor_add_one (c*(P.hi i:ℝ))]
 rw[m6ar hs a i,m6ar b (fun j=>Int.le_floor.mpr (by simp;have:(1:ℝ)<=P.hi j:=(by exact_mod_cast a j);nlinarith)) i];nlinarith
lemma m6b6 {d:ℕ} {P:GAP G d} (hs:P.iS) {c:ℝ} (a:1<=c) (f:(m6H P c (by linarith) hs).iP):P.iP:=by
 let Q:=m6H P c (by linarith) hs;have b:Q.iS:=m6aj hs c (by linarith);rw[GAP.iP,show P.eval=Q.eval from funext fun n=>by simp[GAP.eval,Q,m6H,GAP.rS,hs.1]];refine f.mono fun n e=>m67.mpr fun i=>?_
 have:P.hi i<=Q.hi i:=Int.le_floor.mpr (m6am (by exact_mod_cast ((m6ac hs).2 i).2) a);have:P.lo i<=n i/\n i<=P.hi i:=m67.mp e i;have:=hs.2 i;have:=b.2 i;change Q.lo i<=n i/\n i<=Q.hi i;omega
lemma m6bu {d:ℕ} (P:GAP G d) {k:ℕ} (a:1<=k):(P.nS k).vol<=k^d*P.vol:=by
 simp only[GAP.vol,ZB.vol];rw[m6an];refine prod_le_prod' fun i _=>?_;simp only[GAP.cB,ZB.width,GAP.nS];have:=P.hle i;have:(1:ℤ)<=k:=by exact_mod_cast a
 have:((k:ℤ)*(P.hi i-P.lo i+1)).toNat=k*(P.hi i-P.lo i+1).toNat:=Nat.cast_injective (R:=ℤ) (by rw[Int.toNat_of_nonneg (by nlinarith),Nat.cast_mul,Int.toNat_of_nonneg (by omega)]);have:(k:ℤ)*P.hi i-k*P.lo i+1<=k*(P.hi i-P.lo i+1):=by nlinarith
 omega
lemma m6b7 [m6X G] {d:ℕ} (P:GAP G d):∀ k,iSm k P.tF⊆(P.nS k).tF | 0=>fun x a=>by rw[iSm,mem_singleton] at a;subst a;exact mem_image.mpr ⟨0,m67.mpr fun i=>by simp[GAP.cB,GAP.nS],by simp[GAP.eval,GAP.nS]⟩ | k+1=>fun x a=>by obtain ⟨y,b,z,e,rfl⟩:=mem_add.mp a;obtain ⟨n,f,rfl⟩:=m6E (m6b7 P k b);obtain ⟨m,g,rfl⟩:=m6E e;refine mem_image.mpr ⟨n+m,m67.mpr fun i=>?_,by simp[GAP.eval,GAP.nS,add_zsmul,m6e];abel⟩;have:=m67.mp f i;have:=m67.mp g i;simp only[GAP.cB,GAP.nS,Pi.add_apply,Nat.cast_add,Nat.cast_one] at*;constructor <;> nlinarith
lemma m6bv [m6X G] {A B:Finset G} (hAB:A⊆B) (i:0∈B) {k:ℕ} (j:#A<=k):sS A⊆iSm k B:=by
 have e:∀ T⊆B,(∑ y∈T,y)∈iSm #T B:=fun T=>Finset.induction_on T (fun _=>by simp[iSm])
  fun a s d g h=>by rw[sum_insert d,card_insert_of_notMem d,iSm];simpa[add_comm] using add_mem_add (g ((subset_insert a s).trans h)) (h (mem_insert_self a s))
 intro x f;obtain ⟨S,b,rfl⟩:=m6E f;exact iSS i ((m6K (m6U b)).trans j) (e S ((m6U b).trans hAB))
lemma m6b8 [m6X G] [m6X H] {A:Finset G} {f:G →+H} (hi:Set.InjOn f (A:Set G)) (j:NonAvg (A.image f)):NonAvg A:=by intro a k T l m g;have b:T⊆A:=fun x d=>(mem_erase.mp (l d)).2;apply j (f a) (mem_image_of_mem f k) (T.image f) (fun y i=>by obtain ⟨x,d,rfl⟩:=m6E i;have h:=mem_erase.mp (l d);exact mem_erase.mpr ⟨fun e=>h.1 (hi h.2 k e),mem_image_of_mem f h.2⟩) (by rw[card_image_of_injOn (hi.mono b)];omega);rw[sum_image fun x d y i h=>hi (b d) (b i) h,card_image_of_injOn (hi.mono b),←map_sum,g,map_zsmul]
def m6u [m6X G] {d:ℕ} (P:GAP G d) (A:Finset G):m61 d:=P.cB.tF.filter (fun n=>P.eval n∈A)
lemma m6as [m6X G] {d:ℕ} {P:GAP G d} {A:Finset G} (h:A⊆P.tF):(m6u P A).image P.eval=A:=by ext y;simp only[m6u,mem_image,mem_filter];exact ⟨fun ⟨_,⟨_,h2⟩,h3⟩=>h3 ▸ h2,fun a=>by obtain ⟨n,b,rfl⟩:=m6E (h a);exact ⟨n,⟨b,a⟩,rfl⟩⟩
lemma m6b9 [m6X G] {d:ℕ} {P:GAP G d} {A:Finset G} (h:A⊆P.tF) (a:P.iP):#(m6u P A)=#A:=by
 conv_rhs=>rw[←m6as h]
 exact(card_image_of_injOn (a.mono m6h)).symm
lemma m6bw [m6X G] {d:ℕ} {P:GAP G d} {A:Finset G} (hb:P.base=0) (h:A⊆P.tF) (hp:P.iP) (hNA:NonAvg A):NonAvg (m6u P A):=
 m6b8 (f:=AddMonoidHom.mk' P.eval fun u v=>by simp[GAP.eval,hb,add_zsmul,m6e]) (hp.mono m6h) (by change NonAvg ((m6u P A).image P.eval);rwa[m6as h])
lemma m6at [m6X G] {d h:ℕ} {P:GAP G d} (j:(0:G)∈P.tF) {k:Finset G} (e:k⊆P.tF) {s:ℕ} (hs:1<=s) (f:#k<=s) {c:ℝ} (p:0< c) (l:1<=c*s) {b:GAP G h} (a:b.iS) (m:∀ i,1<=b.hi i) {n:G} (o:(m6H b (c*s) (by positivity) a).iP) (g:((m6H b (c*s) (by positivity) a).tF.image (·+n))⊆sS k):(c/3)^h*(s:ℝ)^h*b.vol<=(s:ℝ)^d*P.vol:=by
 let Q:=m6H b (c*s) (by positivity) a;refine(show _<=(Q.vol:ℝ) by simpa[Q,mul_div_right_comm,mul_pow] using m6bt a m l).trans ?_
 exact_mod_cast (by rw[←GAP.cEV o,←m6T _ (add_left_injective n)];exact((m6K g).trans (m6K (m6bv e j f))).trans ((m6K (m6b7 P s)).trans ((P.nS s).cLV.trans (m6bu P hs))):Q.vol<=s^d*P.vol)
def m6k {d:ℕ} (w:Fin d->ℕ):Set (RV d):={x | ∀ i,|x i|<=↑(w i)}
lemma m6ba {d:ℕ} (w:Fin d->ℕ):(0:RV d)∈m6k w/\Convex ℝ (m6k w)/\(∀ x∈m6k w,-x∈m6k w)/\Bornology.IsBounded (m6k w):=
 ⟨fun _=>by simp,fun x e y f a b g h k i=>by change |a*x i+b*y i|<=_;exact(abs_add_le _ _).trans (by rw[abs_mul,abs_mul,abs_of_nonneg g,abs_of_nonneg h];nlinarith[e i,f i]),fun x e i=>by simpa using e i,
  (Metric.isBounded_iff_subset_closedBall 0).mpr ⟨∑ i:Fin d,↑(w i),fun x e=>by rw[Metric.mem_closedBall,dist_zero_right,pi_norm_le_iff_of_nonneg (by positivity)];exact fun i=>(e i).trans (single_le_sum (fun j _=>Nat.cast_nonneg (w j)) (mem_univ i))⟩⟩
lemma m6bb {d:ℕ} {B:ZB d} (e:(0:ZV d)∈B.tF) {x:ZV d} (f:x∈B.tF):zR x∈m6k B.width:=fun i=>by
 have a:=(ZB.mTF B 0).mp e i;have b:=(ZB.mTF B x).mp f i;simp only[Pi.zero_apply] at a;have:((B.width i:ℕ):ℤ)=B.hi i-B.lo i+1:=Int.toNat_of_nonneg (by omega)
 show |(x i:ℝ)|<=↑(B.width i);exact_mod_cast (abs_le.mpr ⟨by omega,by omega⟩:|x i|<=↑(B.width i))
lemma m6bc {d k:ℕ} {w:Fin k->ZV d} (f:m6a6 (fun i=>zR (w i))):Function.Injective (fun c:ZV k=>∑ i:Fin k,c i•w i):=fun a b e=>by
 have h:∑ i:Fin k,((a i-b i:ℤ):ℝ)•zR (w i)=0:=by
  have g:=congrArg zR (show ∑ i:Fin k,(a i-b i)•w i=0 by rw[show ∑ i,(a i-b i)•w i=(∑ i,a i•w i) - ∑ i,b i•w i by rw[←sum_sub_distrib];exact m64 fun _ _=>sub_zsmul _ _ _,sub_eq_zero];exact e);rw[zRu,zR0] at g;rw[←g];exact m64 fun i _=>(zRm _ _).symm
 ext i;have:a i-b i=0:=by exact_mod_cast Fintype.linearIndependent_iff.mp f _ h i
 omega
lemma m6au (hJ:m6q J) {d e a s:ℕ} {B:ZB d} (S:(0:ZV d)∈B.tF) {H:Submodule ℝ (RV d)} (T:Module.finrank ℝ H<=a) (U:a<=e) {z:m61 d} (r:z⊆B.tF) (t:∀ x∈z,zR x∈H) (hs:1<=s) (u:#z<=s) {c:ℝ} (Z:0< c) (V:1<=c*s) {h:GAP (ZV d) e} (l:h.iS) (W:∀ i,1<=h.hi i) {q0:ZV d} (hp:(m6H h (c*s) (by positivity) l).iP) (y:((m6H h (c*s) (by positivity) l).tF.image (·+q0))⊆sS z):(c/3)^e*(s:ℝ)^(e-a)*h.vol<=(9*↑(J d))^d*B.vol:=by
 let Γ:AddSubgroup (ZV d):={carrier:={x | zR x∈H},zero_mem':=by simp[zR0],add_mem':=fun b Y=>by change zR (_+_)∈H;rw[zRa];exact H.add_mem b Y,neg_mem':=fun b=>by change zR (-_)∈H;rw[zRn];exact H.neg_mem b};obtain ⟨X,L,M,O⟩:=m6ba B.width;obtain ⟨k,o,w,N,hwΓ,f,p,q,g⟩:=hJ.2 d Γ (m6k B.width) X L M O;have m:k<=a:=by have C:m6a6 (fun i=>(⟨zR (w i),hwΓ i⟩:H)):=LinearIndependent.of_comp H.subtype p;exact le_trans (by simpa[Fintype.card_fin] using C.fintype_card_le_finrank) T
 let n:ZB k:=⟨fun i=>-(↑(N i)-1),fun i=>↑(N i)-1,fun i=>by have:=f i;omega⟩;have D:∏ i:Fin k,(2*N i-1)<=3^d*B.vol:=by
  have E:#(n.tF.image (fun v=>∑ i,v i•w i))=∏ i:Fin k,(2*N i-1):=by rw[m6T _ (m6bc p),n.cTF];exact prod_congr rfl fun i _=>by simp only[ZB.width,n];have:=f i;omega
  have F:n.tF.image (fun v=>∑ i,v i•w i)⊆(ZB.symm B.width).tF:=fun x b=>by
   obtain ⟨v,R,rfl⟩:=m6E b;exact m67.mpr fun i=>abs_le.mp (by have:=q v (fun j=>by have:=m67.mp R j;simp only[n] at this;rw[abs_lt];omega) i;change |((∑ j,v j•w j) i:ℝ)|<=↑(B.width i) at this;exact_mod_cast this:|(∑ j,v j•w j) i|<=↑(B.width i))
  refine E ▸ ((m6K F).trans_eq (ZB.symm B.width).cTF).trans ?_
  simp only[ZB.vol];rw[m6an];exact prod_le_prod' fun i _=>by have:=B.wP i;change ((B.width i:ℤ) - -(B.width i:ℤ)+1).toNat<=3*B.width i;omega
 let Q:GAP (ZV d) k:=⟨0,w,fun i=>-↑(J d*N i),fun i=>↑(J d*N i),fun i=>by omega⟩;have G:(Q.vol:ℝ)<=(9*↑(J d))^d*B.vol:=by
  have C:Q.vol<=(3*J d)^d*(3^d*B.vol):=(m6b2 (hJ.1 d) N f).trans (Nat.mul_le_mul (Nat.pow_le_pow_right (by have:=hJ.1 d;omega) o) D);exact(by exact_mod_cast C:(Q.vol:ℝ)<=(3*↑(J d))^d*((3:ℝ)^d*B.vol)).trans_eq (by rw[←m68,←mul_pow];congr 2;ring)
 have K:=m6at (P:=Q) (GAP.zMC ⟨rfl,fun i=>⟨by simp[Q];positivity,by simp[Q];positivity⟩⟩) (fun x b=>by obtain ⟨v,R,rfl⟩:=g x (t x b) (m6bb S (r b));exact mem_image.mpr ⟨v,m67.mpr fun i=>by have:=abs_lt.mp (R i);simp only[GAP.cB,Q,Nat.cast_mul];omega,by simp[GAP.eval,Q]⟩) hs u Z V l W hp y;refine le_of_mul_le_mul_left ?_ (pow_pos (m6D (by omega):(0:ℝ)< s) a);rw[show (s:ℝ)^a*((c/3)^e*(s:ℝ)^(e-a)*h.vol)=(c/3)^e*((s:ℝ)^a*(s:ℝ)^(e-a))*h.vol by ring,←pow_add,Nat.add_sub_cancel' U];grw [K,m6l (m6a hs) m,G]
def m6a2 {l:ℕ} (c:ℝ) (dm m0:ℕ) (_B:ZB l) (A:m61 l) (d':ℕ) (hA A':m61 l) (P:GAP (ZV l) d') (q0:ZV l):Prop:=
 ∃(hc:0< c) (hS:P.iS),c<=1/\1<=d'/\d'<=dm/\m0<=#A/\
  let s:=m6N #A
  hA⊆A/\(#A:ℝ)-c⁻¹*#A/log #A<=#hA/\A'⊆hA/\#A'<=s/\
  (∀ i:Fin d',1<=P.hi i)/\hA⊆P.tF/\q0∈m6a5 (Set.range P.step)/\
  (m6H P (c*s) (m66 hc.le (Nat.cast_nonneg s)) hS).iP/\
  ((m6H P (c*s) (m66 hc.le (Nat.cast_nonneg s)) hS).tF.image (·+q0))⊆sS A'
structure m69 (hCor:M6C) where
 c:ℕ->ℝ
 dm:ℕ->ℕ
 m0:ℕ->ℕ
 ok:∀ l,1<=l->0< c l/\c l<=1/\1<=dm l/\4<=m0 l/\
  ∀(B:ZB l) (A:m61 l),(0:ZV l)∈B.tF->A⊆B.tF->m0 l<=#A->(B.vol:ℝ)<=(#A:ℝ)^(10:ℝ)->
   ∃ d' hA A' P q0,m6a2 (c l) (dm l) (m0 l) B A d' hA A' P q0
def m6bx (a:M6C):m69 a:=by
 have g:∀ l,∃(c:ℝ) (dm m0:ℕ),1<=l->0< c/\c<=1/\1<=dm/\4<=m0/\
   ∀(B:ZB l) (A:m61 l),(0:ZV l)∈B.tF->A⊆B.tF->m0<=#A->(B.vol:ℝ)<=(#A:ℝ)^(10:ℝ)->
    ∃ k n o P p,m6a2 c dm m0 B A k n o P p:=fun l=>by
  by_cases q:1<=l
  . obtain ⟨c,dm,m0,b,e,i,j,hs⟩:=a l q 10 (by norm_num)
    exact ⟨c,dm,m0,fun _=>⟨b,e,i,j,fun B A u hAB s v=>by obtain ⟨k,f,m,n,o,P,p,t,r⟩:=hs B A u hAB s v;exact ⟨k,n,o,P,p,b,t,e,f,m,s,r⟩⟩⟩
  . exact ⟨1,1,4,fun h=>absurd h q⟩
 choose c dm m0 hs using g;exact ⟨c,dm,m0,hs⟩
def m6a3 (sp:m69 hC) {d:ℕ} (de ga:ℝ) (B:ZB d) (A:m61 d):Prop:=
 ∀ A1⊆A,de*#A<=#A1->∀ x∈B.tF,∀ d1 hA1 A1' P1 q1,
  m6a2 (sp.c d) (sp.dm d) (sp.m0 d) (m6M B (-x)) (A1.image (· - x)) d1 hA1 A1' P1 q1->d1=d/\ga*B.vol<=P1.vol
lemma m6n (q:ℝ) (hq:0< q) (C:ℝ):∀ᶠ m:ℕ in atTop,C<=(m:ℝ)^q:=
 tendsto_natCast_atTop_atTop.eventually ((tendsto_rpow_atTop hq).eventually_ge_atTop C)
lemma m6b (p:ℝ) (hp:0< p) (C:ℝ):∀ᶠ m:ℕ in atTop,C<=(log m)^p:=
 ((tendsto_rpow_atTop hp).comp (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).eventually_ge_atTop C
lemma m6f (p q:ℝ) (f:0< p) (j:0< q) (C:ℝ):∀ᶠ m:ℕ in atTop,C*(log m)^p<=(m:ℝ)^q:=by
 let a:=q/(2*p);have g:0< a:=by positivity
 filter_upwards [eventually_ge_atTop 2,m6n (q/2) (half_pos j) (max C 0*a⁻¹^p)] with m hm2 hmC
 have b:(0:ℝ)< m:=m6D (by omega);have h:0< log m:=log_pos (Nat.one_lt_cast.mpr (by omega));have d:log m<=a⁻¹*(m:ℝ)^a:=by have i:=log_le_sub_one_of_pos (m6V b a);rw[log_rpow b] at i;rw[inv_mul_eq_div,le_div_iff₀' g];linarith
 have e:(log m)^p<=a⁻¹^p*(m:ℝ)^(q/2):=(m6ad h.le d f.le).trans_eq (by rw[m6r (by positivity) (by positivity),←m6C b.le];congr 2;dsimp[a];field_simp[f.ne'])
 calc C*(log m)^p<=max C 0*(a⁻¹^p*(m:ℝ)^(q/2)):=mul_le_mul (m6m C 0) e (by positivity) (m6Y C 0)
  _=(max C 0*a⁻¹^p)*(m:ℝ)^(q/2):=by ring
  _<=(m:ℝ)^(q/2)*(m:ℝ)^(q/2):=by gcongr
  _=(m:ℝ)^q:=by rw[←m6L b];congr 1;ring
def m6v (sp:m69 hC) (l:ℕ):ℝ:=(Icc 1 (l+8)).inf' ⟨1,mem_Icc.mpr ⟨le_rfl,by omega⟩⟩ sp.c
def m6aa (sp:m69 hC) (J:ℕ->ℕ) (l:ℕ):ℝ:=(3/m6v sp l)^((Icc 1 (l+8)).sup sp.dm)*(9*↑((Icc 1 (l+8)).sup J))^(l+8)
def m6a4 (sp:m69 hC) (J:ℕ->ℕ) (l:ℕ):ℝ:=(m6aa sp J l)^(l+18)
lemma m6bd (sp:m69 hC) (l:ℕ):0< m6v sp l/\m6v sp l<=1/\∀ r,1<=r->r<=l+8->m6v sp l<=sp.c r:=
 ⟨(lt_inf'_iff _).mpr fun r a=>(sp.ok r (mem_Icc.mp a).1).1,(inf'_le sp.c (mem_Icc.mpr ⟨le_rfl,by omega⟩)).trans (sp.ok 1 le_rfl).2.1,fun _ b d=>inf'_le sp.c (mem_Icc.mpr ⟨b,d⟩)⟩
lemma m6be (hJ:m6q J) (b:m69 hC) (l:ℕ):1<=m6aa b J l:=by obtain ⟨a,d,_⟩:=m6bd b l;have:(1:ℝ)<=↑((Icc 1 (l+8)).sup J):=m6a ((hJ.1 1).trans (le_sup (f:=J) (mem_Icc.mpr ⟨le_rfl,by omega⟩)));exact one_le_mul_of_one_le_of_one_le (m6x (by rw[m6F a];linarith)) (m6x (by linarith))
lemma m6av {l u j r U k m:ℕ} {e f b d:ℝ} (s:e<=1/6) (g:(1:ℝ)< m) (n:1<=b) (hg0:0< f) (h:f<=1) (o:0<=d) (t:d<=(m:ℝ)^(4:ℝ)) (i:b^2<=(m:ℝ)^((1:ℝ)/4)) (v:b^l<=m) (w:1<=k) (x:u+j<=l+2*U) (hi:(k:ℝ)*((m:ℝ)^(1-e))^U<=b^(u+j)*f^r*d):U<=8:=by
 have a:(0:ℝ)< m:=by linarith
 have p:b^(2*U)<=(m:ℝ)^((1/4:ℝ)*U):=by rw[pow_mul,m6C a.le,m6y];exact m6Q (by positivity) i U
 have q:(m:ℝ)^((1-e)*U)<=(m:ℝ)^((1/4:ℝ)*U+5):=by
  rw[m6C a.le,m6y];refine(m6am (by positivity) (m6a w)).trans (hi.trans ?_)
  calc _<=b^(l+2*U)*1*(m:ℝ)^(4:ℝ):=by gcongr;exact pow_le_one₀ hg0.le h
   _=b^l*b^(2*U)*(m:ℝ)^(4:ℝ):=by rw[pow_add,mul_one]
   _<=(m:ℝ)*(m:ℝ)^((1/4:ℝ)*U)*(m:ℝ)^(4:ℝ):=by gcongr
   _=_:=by rw[mul_comm (m:ℝ),←rpow_add_one a.ne',←m6L a];congr 1;ring
 have:=(rpow_le_rpow_left_iff g).mp q;exact Nat.lt_succ_iff.mp (by exact_mod_cast (show (U:ℝ)<9 by nlinarith))
lemma m6by (hJ:m6q J) (t:m69 hC) (l:ℕ) (hl:1<=l) (e:ℝ) (l1:0< e) (b9:e<=1/6) (K:ℕ) (l2:1<=K) (j6:(30:ℝ)<=K*e):∃ Mr:ℕ,4<=Mr/\∀(B:ZB l) (A:m61 l) (z C:ℝ),(0:ZV l)∈B.tF->A⊆B.tF->NonAvg A->Mr<=#A->(B.vol:ℝ)<=(#A:ℝ)^(4:ℝ)->0< z->z<=1/2->0< C->C<=z^(2*K)->(#A:ℝ)^(-(1:ℝ)/3)<=C->(#A:ℝ)^(-e/2)< z^(4*(l+18))->2*(log #A)^2*(#A:ℝ)^(-e/2)<=z->∃ dt M Z,1<=dt/\dt<=l+8/\(0:ZV dt)∈M.tF/\Z⊆M.tF/\NonAvg Z/\m6a3 t z C M Z/\(#A:ℝ)^(1-e/2)<=#Z/\(#Z:ℝ)<=#A/\(M.vol:ℝ)<=(#Z:ℝ)^(6:ℝ)/\(l< dt->(M.vol:ℝ)*(#A:ℝ)^((1-e)*((dt-l:ℕ):ℝ))<=m6a4 t J l*B.vol)/\(dt< l->(M.vol:ℝ)<=m6a4 t J l*B.vol)/\(dt=l->(M.vol:ℝ)<=m6a4 t J l*((#Z:ℝ)/#A)^K*B.vol):=by
 generalize b5:m6aa t J l=CS;have o:1<=CS:=b5 ▸ m6be hJ t l;obtain ⟨y,c7,g0⟩:=m6bd t l;obtain ⟨Mr,i4⟩:=eventually_atTop.mp (show ∀ᶠ m:ℕ in atTop,_/\_/\_/\_/\_/\_ by
  filter_upwards [eventually_ge_atTop 4,m6n (e/6) (by positivity) 2,m6n (1-e) (by linarith) (1/m6v t l),m6n (1/4) (by norm_num) (CS^2),tendsto_natCast_atTop_atTop.eventually (eventually_gt_atTop (CS^(l+18))),m6b 1 one_pos (4*(m6v t l)⁻¹)] with m a b c d f g
  exact ⟨a,b,c,d,f,g⟩)
 refine ⟨max 4 Mr,m6m _ _,fun B A z C j1 hAB j2 j3 a0 hd0 b8 hg0 e6 j4 j5 h8=>?_⟩
 obtain ⟨k5,i5,i6,e1,e2,g1⟩:=i4 #A ((m6Y 4 Mr).trans j3);rw[rpow_one] at g1;set m:=#A;have D:(1:ℝ)< m:=Nat.one_lt_cast.mpr (by omega);have q:(0:ℝ)< m:=by linarith
 let p:=(m:ℝ)^(1-e);have a1:1<=p:=one_le_rpow D.le (by linarith);have v:0< p:=by linarith
 have i0:C<=1/2:=e6.trans ((m6Q hd0.le b8 _).trans (by simpa using pow_le_pow_of_le_one (by norm_num:(0:ℝ)<=1/2) (by norm_num) (show 1<=2*K by omega)));have d5:=(m6l o (by omega:l<=l+18)).trans e2.le;have e7:(1:ℝ)<=log m:=by have:=(one_le_inv₀ y).mpr c7;linarith
 obtain ⟨Ns,k6⟩:∃ Ns:ℕ,CS^(l+18)*(m:ℝ)^(4:ℝ)<(2:ℝ)^Ns:=by obtain ⟨N,hN⟩:=exists_nat_gt (CS^(l+18)*(m:ℝ)^(4:ℝ));exact ⟨N,hN.trans_le (by exact_mod_cast (Nat.lt_two_pow_self (n:=N)).le)⟩
 let L:=l+18+Ns+1;let Iv:=fun (i u O Q U r:ℕ) (F:ZB r) (Ai:m61 r)=>
  1<=r/\r<=l+8/\(0:ZV r)∈F.tF/\Ai⊆F.tF/\NonAvg Ai/\i=u+O+Q/\
  r+O<=l+U/\u<=U/\(F.vol:ℝ)*p^U<=CS^(u+O)*C^Q*B.vol/\
  z^(2*i)*m<=#Ai/\(m:ℝ)^(1-e/2)<=#Ai/\(#Ai:ℝ)<=m
 have b4:∀ k i u O Q U r F Ai,L-i=k->Iv i u O Q U r F Ai->
   ∃ j u' d' s' U' dt M Z,Iv j u' d' s' U' dt M Z/\m6a3 t z C M Z:=fun k=>
  Nat.strong_induction_on k fun k ih i u O Q U r F Ai hk hI=>
   if hir:m6a3 t z C F Ai then ⟨i,u,O,Q,U,r,F,Ai,hI,hir⟩
   else by
    obtain ⟨b6,b7,_,g2,g3,k7,k8,g4,X,i7,i8,g5⟩:=hI;have k1:=m6av b9 D o hg0 (by linarith) (m65) a0 e1 d5 F.vP (by omega) X;have j7:Q< Ns:=by
     by_contra f9;push Not at f9;have h1:(1:ℝ)<=CS^(l+18)*(1/2:ℝ)^Ns*(m:ℝ)^(4:ℝ):=by
      calc (1:ℝ)<=F.vol*p^U:=one_le_mul_of_one_le_of_one_le (m6S F) (m6x a1)
       _<=CS^(u+O)*C^Q*B.vol:=X
       _<=CS^(l+18)*(1/2:ℝ)^Ns*(m:ℝ)^(4:ℝ):=mul_le_mul (mul_le_mul (m6l o (by omega)) ((m6Q hg0.le i0 _).trans (pow_le_pow_of_le_one (by norm_num) (by norm_num) f9)) (m6A hg0.le _) (m6A (by linarith only[o]) _)) a0 (m65) (m66 (m6A (by linarith only[o]) _) (m6A (by norm_num) _))
     have h2:=m62 h1 (m6A (by norm_num:(0:ℝ)<=2) Ns);rw[show (2:ℝ)^Ns*(CS^(l+18)*(1/2:ℝ)^Ns*↑m^(4:ℝ))=CS^(l+18)*((2:ℝ)*(1/2))^Ns*↑m^(4:ℝ) by rw[mul_pow];ring,show (2:ℝ)*(1/2)=1 by norm_num,one_pow,mul_one] at h2;linarith
    unfold m6a3 at hir;push Not at hir;obtain ⟨A1,e3,c8,x,g6,H,c9,k9,P1,q1,⟨_,Y,_,b2,g7,_,T,i9,d0,d2,g8,e4,_,V,b3⟩,hviol⟩:=hir;set G:=#(A1.image (· - x));have a2:G=#A1:=m6T A1 m6z;have c0:z*(m:ℝ)^(1-e/2)<=G:=by rw[a2];exact(m62 i8 hd0.le).trans c8
    have c1:(G:ℝ)<=m:=by rw[a2];exact(m6j (m6K e3)).trans g5
    have d6:=g0 r b6 b7;have w:=(t.ok r b6).1;have e8:(m:ℝ)^(-e/2)*(m:ℝ)^(1-e/2)=p:=by dsimp[p];rw[←m6L q];congr 1;ring
    have a3:p<=G:=(e8 ▸ m63 ((m6am (m6Z q.le _) (by nlinarith)).trans h8) (m6Z q.le _)).trans c0;have c2:=m6c v a3;have R:=log_pos (m6c (by linarith[i5.trans (m6i D.le (by linarith:e/6<=1-e))]) a3);set s1:=m6N G;have a4:p<=s1:=by
     have k2:2*p<=(G:ℝ)/(log G)^2:=by
      rw[m6F (sq_pos_of_pos R)];refine(m62 (m6Q R.le (log_le_log c2 c1) 2) (m66 two_pos.le v.le)).trans ?_
      calc 2*p*(log m)^2=(2*(log m)^2*↑m^(-e/2))*↑m^(1-e/2):=by linear_combination -2*(log m)^2*e8
       _<=(G:ℝ):=(m63 h8 (m6Z q.le _)).trans c0
     dsimp[s1,m6N];linarith[Nat.lt_floor_add_one ((G:ℝ)/(log G)^2)]
    have a5:1<=t.c r*s1:=((m6I y).mp i6).trans ((mul_comm _ _).trans_le (mul_le_mul d6 a4 v.le w.le));have i1:(G:ℝ)/2<=#c9:=by
     have e9:(1-e)*log m<=log G:=by rw[←log_rpow q];exact log_le_log v a3
     have:(t.c r)⁻¹/log G<=1/2:=(m6I R).mpr (by nlinarith only[inv_anti₀ y d6,g1,e9,b9,e7]);nlinarith only[this,i9,c2,show (G:ℝ)-(t.c r)⁻¹*G/log G=(1-(t.c r)⁻¹/log G)*G by ring]
    have f0:=m6b6 Y a5 V;let Bn:=P1.cB;let An:=m6u P1 c9;have c3:=m6b9 e4 f0;have W:z^(2*(i+1))*m<=#An:=by
     rw[show z^(2*(i+1))=z*z*z^(2*i) by rw[show 2*(i+1)=2*i+2 by omega,pow_add,pow_two];ring,m68,m68,c3];exact(m62 ((m62 i7 hd0.le).trans c8) hd0.le).trans ((m63 b8 (m65)).trans (by rw[←a2];linarith only[i1]))
    have a6:(m:ℝ)^(1-e/2)<=#An:=by
     by_contra e0;push Not at e0;have f1:z^(2*(i+1))<(m:ℝ)^(-e/2):=lt_of_mul_lt_mul_right ((W.trans_lt e0).trans_eq (by rw[←rpow_add_one q.ne'];congr 1;ring)) q.le;by_cases k4:i+1<=2*(l+18)
     . linarith only[j5,f1,pow_le_pow_of_le_one hd0.le (by linarith only[b8]) (show 2*(i+1)<=4*(l+18) by omega)]
     . have f2:C^Q<(m:ℝ)^(-(5:ℝ)):=
        (((m6Q hg0.le e6 Q).trans_eq (by rw[←pow_mul];congr 1;ring:(z^(2*K))^Q=z^(K*(2*Q)))).trans
         ((pow_le_pow_of_le_one hd0.le (by linarith only[b8]) (Nat.mul_le_mul_left K (by omega:i+1<=2*Q))).trans_eq
          (by rw[←m6y z (2*(i+1)),←m6C hd0.le,←m6y z];congr 1;push_cast;ring))).trans_lt
         ((rpow_lt_rpow (m6A hd0.le _) f1 (div_pos (m6D (by omega)) two_pos)).trans_le (by rw[←m6C q.le];exact m6i D.le (by linarith only[j6])))
       have i2:(1:ℝ)< CS^(l+18)/m:=
        (one_le_mul_of_one_le_of_one_le (m6S F) (m6x a1)).trans_lt
         ((X.trans (mul_le_mul (m63 (m6l o (by omega:u+O<=l+18)) (m6A hg0.le _)) a0 (m65) (m66 (m6A (by linarith only[o]) _) (m6A hg0.le _)))).trans_lt
          ((mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_left f2 (pow_pos (by linarith only[o]) _)) (m6V q _)).trans_eq
           (by rw[m68,←m6L q,show -(5:ℝ)+4= -1 by norm_num,rpow_neg_one,m6ae])))
       linarith only[e2,(one_lt_div q).mp i2]
    have a7:(0:ZV H)∈Bn.tF:=m67.mpr (m6ac Y).2;have S:=m6bw Y.1 e4 f0 ((by simpa only[sub_eq_add_neg] using (g3.subset e3).translate (-x):NonAvg _).subset T);have a8:(#An:ℝ)<=m:=by rw[c3];exact(m6j (m6K T)).trans c1
    have h3:(3/t.c r)^H<=(3/m6v t l)^((Icc 1 (l+8)).sup t.dm):=(m6Q (m6R (by norm_num) w.le) (m6w (by norm_num) y d6) H).trans (m6l (by rw[m6F y];linarith only[c7]) (g7.trans (le_sup (f:=t.dm) (mem_Icc.mpr ⟨b6,b7⟩))));have f3:(1:ℝ)<=9*↑((Icc 1 (l+8)).sup J):=by have:(1:ℝ)<=↑((Icc 1 (l+8)).sup J):=m6a ((hJ.1 1).trans (le_sup (f:=J) (mem_Icc.mpr ⟨le_rfl,by omega⟩)));linarith
    have E:1<=s1:=Nat.one_le_cast.mp (a1.trans a4);have a9:=(d0.trans T).trans (m6a8 (e3.trans g2) x);by_cases e0:H< r
    . have h9:((9:ℝ)*↑(J r))^r<=(9*↑((Icc 1 (l+8)).sup J))^(l+8):=(m6Q (m66 (by norm_num) (m65)) (m62 (m6j (le_sup (f:=J) (mem_Icc.mpr ⟨b6,b7⟩))) (by norm_num)) r).trans (m6l f3 b7)
      have c4:=m6au hJ (m6a1 g6) le_rfl (m6ai P1.step) a9 (fun _ h=>m6b3 Y.1 (d0.trans e4 <| h)) E d2 w a5 Y g8 V b3;rw[m6a7,mul_right_comm] at c4;have d7:(Bn.vol:ℝ)<=CS*F.vol:=(m6ah w ((m6b1 (m66 (m6A (m6R w.le (by norm_num)) H) (m65)) (m6x (m6a E))).trans c4)).trans (by rw[←b5,m6aa,←m68];exact m63 (mul_le_mul h3 h9 (m6A (m66 (by norm_num) (m65)) _) (m6A (m6R (by norm_num) y.le) _)) (m65));exact ih (L-(i+1)) (by omega) (i+1) u (O+1) Q U H Bn An rfl ⟨b2,by omega,a7,filter_subset _ _,S,by omega,by omega,g4,
       ((m63 d7 (m6A v.le _)).trans_eq (m68 _ _ _)).trans ((m62 X (by linarith only[o])).trans_eq (by rw[show u+(O+1)=(u+O)+1 by omega,pow_succ];ring)),W,a6,a8⟩
    . by_cases f8:r< H
      . have f4:=m6at (P:=m6a9 (m6M F (-x))) (by rw[m6b5];exact m6a1 g6) (by rw[m6b5];exact a9) E d2 w a5 Y g8 V b3
        rw[show (m6a9 (m6M F (-x))).vol=F.vol from m6a7 F (-x)] at f4;have f5:(t.c r/3)^H*(P1.vol*(s1:ℝ)^(H-r))<=F.vol:=le_of_mul_le_mul_left (by rw[show (s1:ℝ)^r*((t.c r/3)^H*(P1.vol*(s1:ℝ)^(H-r)))=(t.c r/3)^H*((s1:ℝ)^r*(s1:ℝ)^(H-r))*P1.vol by ring,←pow_add,Nat.add_sub_cancel' f8.le];exact f4) (pow_pos (m6D E) r);have d7:(Bn.vol:ℝ)*(s1:ℝ)^(H-r)<=CS*F.vol:=(m6ah w f5).trans (by rw[←b5,m6aa];exact m63 (h3.trans (m6b1 (m6A (m6R (by norm_num) y.le) _) (m6x f3))) (m65));have c5:(Bn.vol:ℝ)*p^(U+(H-r))<=CS^((u+1)+O)*C^Q*B.vol:=by
         rw[pow_add,mul_comm (p^U),←m68];exact((m63 ((m62 (m6Q v.le a4 _) (m65)).trans d7) (m6A v.le _)).trans_eq (m68 _ _ _)).trans ((m62 X (by linarith only[o])).trans_eq (by rw[show (u+1)+O=(u+O)+1 by omega,pow_succ];ring))
        have k3:=m6av b9 D o hg0 (by linarith) (m65) a0 e1 d5 Bn.vP (by omega) c5;exact ih (L-(i+1)) (by omega) (i+1) (u+1) O Q (U+(H-r)) H Bn An rfl ⟨b2,by omega,a7,filter_subset _ _,S,by omega,by omega,by omega,c5,W,a6,a8⟩
      . exact ih (L-(i+1)) (by omega) (i+1) u O (Q+1) U H Bn An rfl ⟨b2,by omega,a7,filter_subset _ _,S,by omega,by omega,g4,
         ((m63 (hviol (by omega)).le (m6A v.le _)).trans_eq (m68 _ _ _)).trans ((m62 X hg0.le).trans_eq (by rw[pow_succ];ring)),W,a6,a8⟩
 obtain ⟨j,u',d',s',U',dt,M,Z,⟨g9,h0,h4,h5,e5,j0,j9,k0,d3,h6,d4,h7⟩,hir⟩:=
  b4 L 0 0 0 0 0 l B A (Nat.sub_zero _) ⟨hl,by omega,j1,hAB,j2,rfl,le_rfl,le_rfl,by simp,by rw[mul_zero,pow_zero,one_mul],rpow_le_self_of_one_le D.le (by linarith),le_rfl⟩
 have d8:C<=1:=by linarith
 have j8:=m6av b9 D o hg0 d8 (m65) a0 e1 d5 M.vP (by omega) d3;have d9:m6a4 t J l=CS^(l+18):=by simp[m6a4,b5]
 have b0:(M.vol:ℝ)*p^U'<=CS^(l+18)*C^s'*B.vol:=d3.trans (m63 (m63 (m6l o (by omega:u'+d'<=l+18)) (m6A hg0.le _)) (m65));have c6:CS^(l+18)*C^s'*B.vol<=CS^(l+18)*B.vol:=(m63 (m62 (pow_le_one₀ hg0.le d8) (m6A (by linarith only[o]) _)) (m65)).trans_eq (by ring);have b1:=((m6b1 (m65) (m6x a1)).trans b0).trans c6;refine ⟨dt,M,Z,g9,h0,h4,h5,e5,hir,d4,h7,by
  calc (M.vol:ℝ)<=CS^(l+18)*B.vol:=b1
   _<=m*↑m^(4:ℝ):=mul_le_mul e2.le a0 (m65) q.le
   _=↑m^(5:ℝ):=by rw[mul_comm,←rpow_add_one q.ne'];norm_num
   _<=(↑m^(1-e/2))^(6:ℝ):=by rw[←m6C q.le];exact m6i D.le (by linarith)
   _<=↑(#Z)^(6:ℝ):=m6ad (m6Z q.le _) d4 (by norm_num),
  fun f8=>by rw[d9,m6C q.le,m6y];exact((m62 (m6l a1 (by omega:dt-l<=U')) (m65)).trans b0).trans c6,
  fun _=>d9 ▸ b1,fun l0=>by
   rw[d9];have i3:p⁻¹<=C^2:=(by dsimp[p];rw[←m6G q.le];exact m6i D.le (by linarith):p⁻¹<=↑m^(-(2/3:ℝ))).trans (by rw[show (m:ℝ)^(-(2/3:ℝ))=(↑m^(-(1:ℝ)/3))^2 by rw[←m6y,←m6C q.le];congr 1;norm_num];exact m6Q (m6Z q.le _) j4 2);have f6:p⁻¹^U'<=C^(u'+d'):=(m6Q (inv_nonneg.mpr v.le) i3 _).trans (by rw[←pow_mul];exact pow_le_pow_of_le_one hg0.le d8 (by omega));have f7:(M.vol:ℝ)<=CS^(l+18)*C^j*B.vol:=by
    rw[←mul_one (M.vol:ℝ),←one_pow U',←mul_inv_cancel₀ v.ne',mul_pow,←m68];refine(m63 b0 (m6A (inv_nonneg.mpr v.le) _)).trans ?_
    rw[show CS^(l+18)*C^s'*B.vol*p⁻¹^U'=CS^(l+18)*(C^s'*p⁻¹^U')*B.vol by ring];exact(m63 (m62 (m62 f6 (m6A hg0.le _)) (m6A (by linarith only[o]) _)) (m65)).trans_eq (by rw[←pow_add,add_comm s',←j0])
   exact f7.trans (m63 (m62 (((m6Q hg0.le e6 j).trans_eq (by rw[←pow_mul,←pow_mul];congr 1;ring)).trans (m6Q (m6A hd0.le _) ((m6F q).mpr h6) K)) (m6A (by linarith only[o]) _)) (m65))⟩
def m6O {d:ℕ} (u:RV d) (x a:ZV d):ℝ:=∑ k,u k*((x k-a k:ℤ):ℝ)
lemma m6bf {x:ℝ} (h:1<=x):x/2<=↑⌊x⌋:=by
 by_cases a:x<2
 . have:(1:ℝ)<=↑⌊x⌋:=by exact_mod_cast Int.le_floor.mpr (by simpa using h)
   linarith
 . linarith[Int.sub_one_lt_floor x]
lemma m6bg {α β:Type*} [m6X β] {S:Finset α} {V:Finset β} (f:α->β) (i:∀ x∈S,f x∈V) (a:V.Nonempty):∃ t∈V,(#S:ℝ)<=#V*#(S.filter fun x=>f x=t):=by
 obtain ⟨t,e,d⟩:=exists_max_image V (fun t=>#(S.filter fun x=>f x=t)) a;have hs:∑ v∈V,#(S.filter fun x=>f x=v)=#S:=by
  rw[←card_biUnion fun j _ k _ a=>disjoint_left.mpr fun x g h=>a ((m6P g).2.symm.trans (m6P h).2)];congr 1;ext x;simp only[mem_biUnion,mem_filter];exact ⟨fun ⟨_,_,b,_⟩=>b,fun b=>⟨f x,i x b,b,rfl⟩⟩
 exact ⟨t,e,by exact_mod_cast hs.symm.trans_le ((sum_le_sum d).trans_eq (by rw[sum_const,smul_eq_mul]))⟩
lemma m6bh {d:ℕ} {E:m61 d} {a:ZV d} {S:Set (E->ℝ)} (l:Convex ℝ S) (m:IsCompact S) {v:RV d} (n:v∉(fun f=>∑ x:E,f x•zR (x.1-a)) '' S):∃(u:RV d) (z:ℝ),z<∑ k,u k*v k/\∀ f∈S,∑ x:E,f x*m6O u x.1 a< z:=by
 let h:(E->ℝ) →ₗ[ℝ] RV d:=⟨⟨fun f=>∑ x:E,f x•zR (x.1-a),fun _ _=>by simp[add_smul,m6e]⟩,fun _ _=>by simp[smul_sum,mul_smul]⟩;obtain ⟨f,q,r,e⟩:=geometric_hahn_banach_point_closed (l.linear_image h) (m.image (continuous_finsetSum _ fun x _=>(continuous_apply x).smul continuous_const)).isClosed n;let u:RV d:=fun i=>-f (Pi.single i 1);have b:∀ w:RV d,∑ i:Fin d,u i*w i= -f w:=fun w=>by
  have o:w=∑ i:Fin d,w i•(Pi.single i (1:ℝ):RV d):=by ext j;simp only[Finset.sum_apply,Pi.smul_apply,smul_eq_mul];rw[sum_eq_single j] <;> simp (config:={contextual:=true})
  conv_rhs=>rw[o,map_sum]
  simp only[map_smul,smul_eq_mul,←sum_neg_distrib,u];exact m64 fun _ _=>by ring
 refine ⟨u,-q,by rw[b];linarith,fun g s=>?_⟩
 have p:∑ k,u k*(h g) k=∑ x:E,g x*m6O u x.1 a:=by
  change ∑ k,u k*(∑ x:E,g x•zR (x.1-a)) k=_;simp only[Finset.sum_apply,Pi.smul_apply,smul_eq_mul,zR,Pi.sub_apply,mul_sum,m6O];rw[sum_comm];exact m64 fun _ _=>m64 fun _ _=>by push_cast;ring
 rw[←p,b];linarith[e (h g) ⟨g,s,rfl⟩]
def m6aw (J:ℕ->ℕ) (sp:m69 hC) {d:ℕ} (de ga:ℝ) (B:ZB d) (A:m61 d):Prop:=
 ∀ T⊆A,de*#A<=#T->sp.m0 d<=#T/\(B.vol:ℝ)<=(#T:ℝ)^(10:ℝ)/\
  1<=sp.c d*m6N #T/\(27*↑(J d)/sp.c d)^d/ga< m6N #T
structure m6o (J:ℕ->ℕ) (sp:m69 hC) {d:ℕ} (de ga:ℝ) (B:ZB d) (A:m61 d):Prop where
 hJ:m6q J
 hd:1<=d
 hd0:0< de
 hg0:0< ga
 hAB:A⊆B.tF
 hir:m6a3 sp de ga B A
 hs:m6aw J sp de ga B A
lemma m6bi {d a:ℕ} {c s e b:ℝ} (g:0< c) (h:0< e) (i:0< a) (j:(c/3)^d*s*(e*a)<=(9*b)^d*a) (k:(27*b/c)^d/e< s):False:=by have f:=m6ah g (le_of_mul_le_mul_right (by linarith:(c/3)^d*(s*e)*a<=(9*b)^d*a) (m6D i));linarith[(m6F h).mpr (f.trans_eq (by rw[←mul_pow,show 3/c*(9*b)=27*b/c by ring]))]
lemma m6ax {d:ℕ} {w u:ℝ} {l:ZB d} {v:m61 d} {e:m69 hC} (C:m6o J e w u l v) {a:ZV d} (x:a∈l.tF) {T:m61 d} (f:T⊆v) (m:w*#v<=#T):let S:=T.image (· - a);let s:=m6N #S;∃(n o:m61 d) (P:GAP (ZV d) d) (q:ZV d),m6a2 (e.c d) (e.dm d) (e.m0 d) (m6M l (-a)) S d n o P q/\u*l.vol<=P.vol/\1<=s/\1<=e.c d*s/\(27*↑(J d)/e.c d)^d/u< s:=by
 intro S s;have b:#S=#T:=m6T T m6z;obtain ⟨p,h,r,i⟩:=C.hs T f m;obtain ⟨y,n,o,P,q,j⟩:=(e.ok d C.hd).2.2.2.2 (m6M l (-a)) S (m6a1 x) (m6a8 (f.trans C.hAB) a) (b ▸ p) (by rw[m6a7,b];exact h);obtain ⟨k,t⟩:=C.hir T f m a x y n o P q j;rcases k.symm with rfl
 have g:1<=e.c d*s:=by simpa[s,b] using r
 exact ⟨n,o,P,q,j,t,by exact_mod_cast (show (1:ℝ)<=s by nlinarith[(e.ok d C.hd).2.1,m6al s]),g,by simpa[s,b] using i⟩
def m6B {α:Type*} [m6X α] (A:Finset α) (p:α->ℝ) (S:Finset α):ℝ:=(∏ a∈S,p a)*(∏ a∈A \ S,(1-p a))
lemma m6ab {α:Type*} [m6X α] (A:Finset α) (p:α->ℝ):(∑ S∈A.powerset,m6B A p S=1)/\(∀ g:α->ℝ,∑ S∈A.powerset,m6B A p S*((∑ x∈S,g x) - ∑ x∈A,p x*g x)^2=∑ x∈A,p x*(1-p x)*g x^2):=by
 have k:∀{a:α} {T:Finset α},a∉T->∀ F:Finset α->ℝ,∑ S∈(insert a T).powerset,F S=(∑ S∈T.powerset,F S)+∑ S∈T.powerset,F (insert a S):=fun {a T} b F=>by
  rw[powerset_insert,sum_union (disjoint_left.mpr fun S f n=>by obtain ⟨U,_,rfl⟩:=m6E n;exact b (m6U f (mem_insert_self a U))),sum_image];intro s f t n e;simpa[erase_insert (fun h=>b (m6U f h)),erase_insert (fun h=>b (m6U n h))] using congrArg (·.erase a) e
 have i:∀{a:α} {T S:Finset α},a∉T->S⊆T->m6B (insert a T) p S=(1-p a)*m6B T p S/\m6B (insert a T) p (insert a S)=p a*m6B T p S:=fun {a T S} b d=>by
  have l:a∉S:=fun h=>b (d h);have m:a∉T \ S:=fun h=>b (mem_sdiff.mp h).1;have f:insert a T \ S=insert a (T \ S):=by ext x;simp only[Finset.mem_sdiff,mem_insert];exact ⟨fun ⟨h,hn⟩=>h.imp_right fun o=>⟨o,hn⟩,fun h=>h.elim (fun e=>⟨Or.inl e,e ▸ l⟩) fun ⟨o,hn⟩=>⟨Or.inr o,hn⟩⟩
  have n:insert a T \ insert a S=T \ S:=by ext x;simp only[Finset.mem_sdiff,mem_insert];exact ⟨fun ⟨h,hn⟩=>⟨h.elim (fun e=>absurd (Or.inl e) hn) id,fun hs=>hn (Or.inr hs)⟩,fun ⟨hT,j⟩=>⟨Or.inr hT,fun h=>h.elim (fun e=>b (e ▸ hT)) j⟩⟩
  exact ⟨by simp only[m6B,f,prod_insert m];ring,by simp only[m6B,n,prod_insert l];ring⟩
 have f:∀ T:Finset α,∑ S∈T.powerset,m6B T p S=1:=fun T=>Finset.induction_on T (by simp[m6B]) fun a T b q=>by
  rw[k b,m64 fun S j=>(i b (m6U j)).1,m64 fun S j=>(i b (m6U j)).2,←mul_sum,←mul_sum,q];ring
 refine ⟨f A,fun g=>Finset.induction_on A (by simp[m6B]) fun a T b q=>?_⟩
 rw[k b,sum_insert b];set u:=∑ x∈T,p x*g x;rw[show (∑ S∈T.powerset,m6B (insert a T) p S*((∑ x∈S,g x)-(p a*g a+u))^2)+(∑ S∈T.powerset,m6B (insert a T) p (insert a S)*((∑ x∈insert a S,g x)-(p a*g a+u))^2)=∑ S∈T.powerset,(m6B T p S*((∑ x∈S,g x)-u)^2+m6B T p S*(p a*(1-p a)*g a^2)) by
   rw[←m6e];exact m64 fun S j=>by have d:=m6U j;have r:=i b d;rw[r.1,r.2,sum_insert (fun h=>b (d h))];ring,
  m6e,←sum_mul,q,f T,sum_insert b];ring
lemma m6bj {α:Type*} [m6X α] {A:Finset α} {p:α->ℝ} (l:∀ a∈A,0<=p a/\p a<=1) {F:Finset α->ℝ} {M:ℝ} (h:∑ S∈A.powerset,m6B A p S*F S<=M):∃ S⊆A,F S<=M:=by
 by_contra b;push Not at b;have i:∀ S∈A.powerset,0<=m6B A p S:=fun S g=>m66 (prod_nonneg fun a j=>(l a (m6U g j)).1) (prod_nonneg fun a j=>by linarith[(l a (mem_sdiff.mp j).1).2]);obtain ⟨f,d,e⟩:∃ f∈A.powerset,0< m6B A p f:=by by_contra k;push Not at k;linarith[(m6ab A p).1,sum_nonpos k]
 have m:=sum_lt_sum (fun S g=>m62 (b S (m6U g)).le (i S g)) ⟨f,d,mul_lt_mul_of_pos_left (b f (m6U d)) e⟩;rw[←sum_mul,(m6ab A p).1,one_mul] at m;linarith
lemma m6bz {d:ℕ} (A:m61 d) (w:Fin d->ℝ) (s:∀ i,0<=w i) (n:∀ a∈A,∀ i,|(a i:ℝ)|<=w i) (p:ZV d->ℝ) (q:∀ a∈A,0<=p a/\p a<=1):∃ S⊆A,∀ i:Fin d,|(∑ a∈A,p a*(a i:ℝ))-((∑ a∈S,a) i:ℝ)|<=sqrt (↑d*#A)*w i:=by
 let g:=univ.filter fun i:Fin d=>0< w i;have h:∑ S∈A.powerset,m6B A p S*(∑ i∈g,(((∑ a∈S,(a i:ℝ)) - ∑ a∈A,p a*(a i:ℝ))/w i)^2)<=↑d*#A/4:=by
  trans ∑ i∈g,(1/w i^2)*∑ S∈A.powerset,m6B A p S*((∑ a∈S,(a i:ℝ)) - ∑ a∈A,p a*(a i:ℝ))^2
  . exact le_of_eq (by simp only[mul_sum];rw[sum_comm];exact m64 fun _ _=>m64 fun _ _=>by rw[div_pow];ring)
  refine(sum_le_sum fun i hi=>?_).trans ((by rw[sum_const,nsmul_eq_mul]:∑ _i∈g,((#A:ℝ)/4)=#g*((#A:ℝ)/4)).trans_le ((m63 (m6j ((m6K m6h).trans_eq (by rw[card_univ,Fintype.card_fin]))) (by positivity)).trans_eq (by ring)))
  have b:0< w i:=(m6P hi).2;rw[(m6ab A p).2];have hs:∑ a∈A,p a*(1-p a)*(a i:ℝ)^2<=#A*(w i^2/4):=(sum_le_sum fun a e=>by
   have:(a i:ℝ)^2<=w i^2:=by rw[←sq_abs];exact m6Q (abs_nonneg _) (n a e i) 2
   nlinarith[(q a e).1,(q a e).2,m6d (p a-1/2),m6d (w i)]:_<=∑ _a∈A,(w i^2/4)).trans_eq (by rw[sum_const,nsmul_eq_mul])
  exact(m62 hs (by positivity)).trans_eq (by field_simp)
 obtain ⟨S,m,r⟩:=m6bj q h;refine ⟨S,m,fun i=>?_⟩;rw[show ((∑ a∈S,a) i:ℝ)=∑ a∈S,(a i:ℝ) by simp];by_cases b:0< w i
 . have o:(((∑ a∈S,(a i:ℝ)) - ∑ a∈A,p a*(a i:ℝ))/w i)^2<=↑d*#A:=by
    have:=single_le_sum (f:=fun j=>(((∑ a∈S,(a j:ℝ)) - ∑ a∈A,p a*(a j:ℝ))/w j)^2) (fun _ _=>m6d _) (mem_filter.mpr ⟨mem_univ i,b⟩:i∈g);nlinarith[show (0:ℝ)<=↑d*#A by positivity]
   have e:=sqrt_le_sqrt o;rw[sqrt_sq_eq_abs,abs_div,abs_of_pos b,m6I b] at e;rwa[abs_sub_comm]
 . have k:w i=0:=le_antisymm (not_lt.mp b) (s i)
   have l:∀ a∈A,(a i:ℝ)=0:=fun a e=>abs_nonpos_iff.mp (k ▸ n a e i);rw[sum_eq_zero fun a e=>l a (m e),sum_eq_zero fun a e=>by rw[l a e,mul_zero],k];simp
lemma m6c0 {d:ℕ} {j:ℝ} {b:m61 d} (S:0< j) (T:j<=1/2) (U:2<=↑(#b)*j) (h:¬ DCP j b):∃ a∈b,∃ c:ZV d->ℝ,(∀ x∈b.erase a,0<=c x/\c x<=2/(j*#b))/\(∑ x∈b.erase a,c x=1)/\(∑ x∈b.erase a,c x•zR (x-a)=0):=by
 unfold DCP at h;push Not at h;obtain ⟨a,q,r⟩:=h;have k:4<=#b:=by exact_mod_cast (show (4:ℝ)<=#b by nlinarith)
 let E:=b.erase a;have L:(#E:ℝ)=#b-1:=by rw[card_erase_of_mem q,Nat.cast_sub (by omega)];simp
 have A:(0:ℝ)<#E:=by linarith[show (4:ℝ)<=#b by exact_mod_cast k]
 let M:ℝ:=2/(j*#b);let l:Set (E->ℝ):=(Set.univ.pi fun _=>Set.Icc 0 M) ∩ {f | ∑ x:E,f x=1};have m:l.Nonempty:=⟨fun _=>1/#E,⟨fun _ _=>⟨by positivity,by rw[div_le_div_iff₀ A (by positivity)];nlinarith[show (4:ℝ)<=#b by exact_mod_cast k]⟩,by simp;field_simp⟩⟩;have B:(0:RV d)∈(fun f=>∑ x:E,f x•zR (x.1-a)) '' l:=by
  by_contra J;have n:Convex ℝ l:=(convex_pi fun _ _=>convex_Icc 0 M).inter fun f O g P s t _ _ Q=>by
   change ∑ x:E,(s*f x+t*g x)=1;rw[m6e,←mul_sum,←mul_sum,O,P];linarith
  have o:IsCompact l:=(isCompact_univ_pi fun _=>isCompact_Icc).inter_right (isClosed_eq (continuous_finsetSum _ fun x _=>continuous_apply x) continuous_const);obtain ⟨u,z,K,v⟩:=m6bh n o J;simp only[Pi.zero_apply,mul_zero,sum_const_zero] at K;have C:u≠0:=fun R=>by obtain ⟨w,i⟩:=m;have:=v w i;simp[R,m6O] at this;linarith
  let G:=E.filter fun x=>(0:ℝ)<=m6O u x a;have D:j*#b/2<=#G:=by
   have hs:b.filter (fun x=>(0:ℝ)<=m6O u x a)⊆insert a G:=fun x e=>by
    rw[mem_filter] at e;by_cases p:x=a
    . exact p ▸ mem_insert_self _ _
    . exact mem_insert_of_mem (mem_filter.mpr ⟨mem_erase.mpr ⟨p,e.1⟩,e.2⟩)
   have:j*#b<#G+1:=m6c (r u C) (by exact_mod_cast (m6K hs).trans (card_insert_le _ _));nlinarith
  have F:(0:ℝ)<#G:=m6c (by positivity) D;let g:E->ℝ:=fun x=>if x.1∈G then 1/#G else 0;have H:g∈l:=⟨fun x _=>by
   dsimp[g];split_ifs
   . exact ⟨by positivity,by rw[div_le_div_iff₀ F (by positivity)];linarith⟩
   . exact ⟨le_rfl,by positivity⟩,by
   change ∑ x∈E.attach,(if x.1∈G then (1:ℝ)/#G else 0)=1;rw[sum_attach E (fun x=>if x∈G then (1:ℝ)/#G else 0),←sum_filter,show E.filter (·∈G)=G by ext x;simp[G],sum_const,nsmul_eq_mul];field_simp⟩
  have N:0<=∑ x:E,g x*m6O u x.1 a:=sum_nonneg fun x _=>by
   dsimp[g];split_ifs with e
   . exact m66 (by positivity) (m6P e).2
   . simp
  linarith[v g H]
 obtain ⟨w,i,y⟩:=B;refine ⟨a,q,fun x=>if e:x∈E then w ⟨x,e⟩ else 0,fun x e=>by dsimp only;rw[dif_pos e];exact i.1 ⟨x,e⟩ (Set.mem_univ _),?_,?_⟩
 . rw[←sum_attach E (fun x=>if e:x∈E then w ⟨x,e⟩ else 0),m64 fun x _=>dif_pos x.2];exact i.2
 . rw[←sum_attach E (fun x=>(if e:x∈E then w ⟨x,e⟩ else 0)•zR (x-a)),m64 fun x _=>by rw[dif_pos x.2]];exact y
lemma m6bk {d:ℕ} {w:Fin d->ZV d} (n:m6a6 (fun j=>zR (w j))):let A:=Matrix.of (fun k j=>w j k);A.det≠0/\∀ z:ZV d,(A.det.natAbs:ℤ)•z∈m6a5 (Set.range w):=by
 intro A;let a:=(Int.castRingHom ℝ).mapMatrix A;have b:Function.Injective (Matrix.toLin' a):=(injective_iff_map_eq_zero _).mpr fun v p=>by
  have g:Matrix.toLin' a v=∑ j,v j•zR (w j):=by ext k;simp[Matrix.mulVec,dotProduct,a,A,zR];exact m64 fun _ _=>mul_comm _ _
  rw[g] at p;ext j;exact Fintype.linearIndependent_iff.mp n v p j
 let e:=LinearEquiv.ofBijective (Matrix.toLin' a) ⟨b,LinearMap.injective_iff_surjective.mp b⟩;have i:a.det≠0:=fun m=>by
  have o:LinearMap.det (Matrix.toLin' a)*LinearMap.det e.symm.toLinearMap=1:=by rw[←LinearMap.det_comp,show (Matrix.toLin' a).comp e.symm.toLinearMap=LinearMap.id from LinearMap.ext e.apply_symm_apply,LinearMap.det_id]
  rw[LinearMap.det_toLin',m,zero_mul] at o;norm_num at o
 refine ⟨fun m=>i (by have:=RingHom.map_det (Int.castRingHom ℝ) A;change (A.det:ℝ)=a.det at this;rw[←this,m,Int.cast_zero]),fun z=>?_⟩
 have l:A.det•z=∑ j,(A.adjugate.mulVec z) j•w j:=by
  rw[←show A.mulVec (A.adjugate.mulVec z)=A.det•z by rw[Matrix.mulVec_mulVec,Matrix.mul_adjugate,Matrix.smul_mulVec,Matrix.one_mulVec]];ext k;simp[Matrix.mulVec,dotProduct,A];exact m64 fun _ _=>mul_comm _ _
 have f:A.det•z∈m6a5 (Set.range w):=l ▸ AddSubgroup.sum_mem _ fun j _=>AddSubgroup.zsmul_mem _ (AddSubgroup.subset_closure (Set.mem_range_self j)) _;rcases Int.natAbs_eq A.det with h | h
 . exact h ▸ f
 . exact(show (A.det.natAbs:ℤ)•z= -(A.det•z) by rw[←neg_zsmul];congr 1;omega) ▸ AddSubgroup.neg_mem _ f
lemma m6bl {d:ℕ} {de ga:ℝ} {e:ZB d} {A0:m61 d} {n:m69 hC} (C:m6o J n de ga e A0) {a:ZV d} (Q:a∈e.tF) {A1:m61 d} (F:A1⊆A0) (a5:de*#A0<=#A1):let S1:=A1.image (· - a);let f:=m6N #S1;∃(U u:m61 d) (b:GAP (ZV d) d) (M:ZV d) (_:b.iS),m6a2 (n.c d) (n.dm d) (n.m0 d) (m6M e (-a)) S1 d U u b M/\b.iP/\m6a6 (fun j=>zR (b.step j))/\(∀ k:Fin d,|(M k:ℝ)|<=↑f*e.width k)/\∃ G:ℕ,1<=G/\(G:ℝ)<=↑d.factorial*(3/n.c d)^d/ga/\∀ z:ZV d,(G:ℤ)•z∈m6a5 (Set.range b.step):=by
 intro S1 f;obtain ⟨U,u,b,M,N,a3,v,O,a4⟩:=m6ax C Q F a5;have V:=N;obtain ⟨w,g,_,_,_,_,A,_,B,P,D,b5,_,E,l⟩:=N;have o:=m6a1 Q;have p:=m6a8 (F.trans C.hAB) a;have W:m6a6 (fun j=>zR (b.step j)):=by
  by_contra a2;let H:=Submodule.span ℝ (Set.range (fun j:Fin d=>zR (b.step j)));have b8:Module.finrank ℝ H< d:=by have:Module.finrank ℝ H<=d:=m6ai b.step;by_contra c2;exact a2 (linearIndependent_iff_card_eq_finrank_span.mpr (by change Fintype.card (Fin d)=Module.finrank ℝ H;rw[Fintype.card_fin];omega))
  have X:=m6au C.hJ o le_rfl (m6ai b.step) ((B.trans A).trans p) (fun _ h=>m6b3 g.1 (B.trans b5 <| h)) v P w O g D E l;rw[m6a7] at X;have a6:(f:ℝ)<=(f:ℝ)^(d-Module.finrank ℝ H):=by simpa using m6l (m6a v) (show 1<=d-Module.finrank ℝ H by omega)
  exact m6bi w C.hg0 e.vP (by grw [a6,a3,X];exact m66 C.hg0.le (m65)) a4
 have R:∀ y∈sS u,∀ k:Fin d,(f:ℤ)*(e.lo k-a k)<=y k/\y k<=(f:ℤ)*(e.hi k-a k):=fun y hy k=>by
  obtain ⟨T,hT,rfl⟩:=m6E hy;have Y:=m6U hT;have b9:(#T:ℤ)<=f:=by exact_mod_cast (m6K Y).trans P
  have S:=m67.mp o k;simp only[m6M,Pi.zero_apply,Pi.neg_apply,←sub_eq_add_neg] at S;have Z:∀ x∈T,e.lo k-a k<=x k/\x k<=e.hi k-a k:=fun x hx=>by have:=m67.mp (p (A (B (Y hx)))) k;simp only[m6M,Pi.neg_apply,←sub_eq_add_neg] at this;exact this
  have a7:=sum_le_sum fun x hx=>(Z x hx).1;have a8:=sum_le_sum fun x hx=>(Z x hx).2;simp only[sum_const,nsmul_eq_mul,Finset.sum_apply] at a7 a8 ⊢;constructor <;> nlinarith
 have q:∀ k,(e.hi k-e.lo k:ℤ)<=e.width k:=fun k=>by have:=m6aq e k;exact_mod_cast (by linarith:((e.hi k-e.lo k:ℤ):ℝ)<=e.width k)
 let Q1:=m6H b (n.c d*f) (by positivity) g;have m:Q1.iS:=m6aj g _ (by positivity);have a9:∀ j k:Fin d,(b.hi j:ℝ)*|(b.step j k:ℝ)|<=(n.c d)⁻¹*e.width k:=fun j k=>by
  let L:=Q1.hi j;have r:0<=L:=((m6ac m).2 j).2;have c0:n.c d*f*b.hi j/2<=L:=m6bf (by nlinarith[show (1:ℝ)<=b.hi j by exact_mod_cast D j]:1<=n.c d*f*b.hi j);have K:∀ t:ℤ,|t|<=L->t•b.step j+M∈sS u:=fun t ht=>l (mem_image.mpr ⟨t•b.step j,mem_image.mpr ⟨Pi.single j t,m67.mpr fun i=>by
   change Q1.lo i<=(Pi.single j t:ZV d) i/\(Pi.single j t:ZV d) i<=Q1.hi i;by_cases a1:i=j
   . subst a1;simp[m.2 i];have:=abs_le.mp ht;omega
   . simp[Pi.single_eq_of_ne a1];exact(m6ac m).2 i,
   by simp only[GAP.eval,m6H,GAP.rS,zero_add];rw[sum_eq_single j] <;> simp (config:={contextual:=true})⟩,rfl⟩)
  have hp:=R _ (K L (by rw[abs_of_nonneg r])) k;have hn:=R _ (K (-L) (by rw[abs_neg,abs_of_nonneg r])) k;simp only[Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hp hn;have c1:2*(L:ℝ)*|(b.step j k:ℝ)|<=↑f*e.width k:=by
   have h1:(|2*L*b.step j k| :ℝ)<=((f:ℤ)*e.width k:ℤ):=by exact_mod_cast (abs_le.mpr ⟨by linarith,by linarith⟩:|2*L*b.step j k|<=(f:ℤ)*(e.hi k-e.lo k)).trans (m62 (q k) (Int.natCast_nonneg f))
   rw[abs_mul,abs_mul,abs_of_nonneg (by norm_num:(0:ℝ)<=2),abs_of_nonneg (by exact_mod_cast r:(0:ℝ)<=L)] at h1;push_cast at h1;exact h1
  rw[inv_mul_eq_div,le_div_iff₀' w];exact le_of_mul_le_mul_left (by nlinarith[abs_nonneg (b.step j k:ℝ)]:↑f*(n.c d*((b.hi j:ℝ)*|(b.step j k:ℝ)|))<=↑f*e.width k) (m6D v)
 have b0:∀ k:Fin d,|(M k:ℝ)|<=↑f*e.width k:=fun k=>by
  have hq:=R M (l (mem_image.mpr ⟨0,GAP.zMC (m6ac m),by simp⟩)) k;have S:=m67.mp o k;simp only[m6M,Pi.zero_apply,Pi.neg_apply,←sub_eq_add_neg] at S;exact_mod_cast (abs_le.mpr ⟨by nlinarith[q k,Int.natCast_nonneg f],by nlinarith[q k,Int.natCast_nonneg f]⟩:|M k|<=(f:ℤ)*e.width k)
 let Ai:=Matrix.of (fun k j=>b.step j k);obtain ⟨b6,b7⟩:=m6bk W;let G:=Ai.det.natAbs;have b1:(G:ℝ)<=↑d.factorial*(3/n.c d)^d/ga:=by
  have b2:(G:ℝ)*∏ j:Fin d,(b.hi j:ℝ)<=↑d.factorial*(n.c d)⁻¹^d*e.vol:=by
   rw[show (G:ℝ)=|(Ai.det:ℝ)| by change ((Ai.det.natAbs:ℕ):ℝ)=_;rw[←Int.cast_abs,Int.abs_eq_natAbs,Int.cast_natCast],Matrix.det_apply];simp only[Units.smul_def,zsmul_eq_mul,Int.cast_sum,Int.cast_mul,Int.cast_prod];have b3:|∑ s:Equiv.Perm (Fin d),((Equiv.Perm.sign s:ℤ):ℝ)*∏ j:Fin d,(Ai (s j) j:ℝ)|<=∑ s:Equiv.Perm (Fin d),∏ j:Fin d,|(b.step j (s j):ℝ)|:=
    (abs_sum_le_sum_abs _ _).trans_eq (m64 fun (s:Equiv.Perm (Fin d)) _=>by rw[abs_mul,abs_prod,show |((Equiv.Perm.sign s:ℤ):ℝ)| =1 by rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h <;> simp[h],one_mul];rfl)
   have a0:∀ j:Fin d,(0:ℝ)<=b.hi j:=fun j=>by exact_mod_cast (show (0:ℤ)<=b.hi j by have:=D j;omega)
   calc _<=(∑ s:Equiv.Perm (Fin d),∏ j:Fin d,|(b.step j (s j):ℝ)|)*∏ j,(b.hi j:ℝ):=m63 b3 (prod_nonneg fun j _=>a0 j)
    _=∑ s:Equiv.Perm (Fin d),∏ j,((b.hi j:ℝ)*|(b.step j (s j):ℝ)|):=by rw[sum_mul];exact m64 fun _ _=>by rw[←prod_mul_distrib];exact prod_congr rfl fun _ _=>mul_comm _ _
    _<=∑ s:Equiv.Perm (Fin d),∏ j,((n.c d)⁻¹*↑(e.width (s j))):=sum_le_sum fun s _=>prod_le_prod (fun j _=>m66 (a0 j) (abs_nonneg _)) fun j _=>a9 j (s j)
    _=∑ _s:Equiv.Perm (Fin d),((n.c d)⁻¹^d*↑e.vol):=m64 fun s _=>by rw[←m6s];congr 1;simp only[ZB.vol,Nat.cast_prod];exact Fintype.prod_equiv s _ (fun k=>(e.width k:ℝ)) fun _=>rfl
    _=_:=by rw[sum_const,card_univ,Fintype.card_perm,Fintype.card_fin,nsmul_eq_mul,m68]
  have b4:(b.vol:ℝ)<=3^d*∏ j:Fin d,(b.hi j:ℝ):=by
   rw[m6s];simp only[GAP.vol,ZB.vol,Nat.cast_prod];exact prod_le_prod (fun _ _=>m65) fun j _=>by rw[m6ar g D j];linarith[show (1:ℝ)<=b.hi j by exact_mod_cast D j]
  rw[m6F C.hg0];refine le_of_mul_le_mul_right ?_ (m6af e);rw[m68 (G:ℝ)];grw [a3,b4];rw[mul_left_comm (G:ℝ)];grw [b2];exact le_of_eq (by rw[m6ae,mul_pow];ring)
 exact ⟨U,u,b,M,g,V,m6b6 g O E,W,b0,G,Nat.one_le_iff_ne_zero.mpr (Int.natAbs_ne_zero.mpr b6),b1,b7⟩
lemma m6c1 {d:ℕ} (hd:1<=d) (W:Fin d->ℝ) (z:∀ i,0< W i) (u:RV d) {r:ℝ} (A:0< r) {a:Fin d} (p:u a≠0):volume {x:RV d | (∀ i,|x i|<=W i)/\ |∑ i,u i*x i|<=r}<=m6W ((2*r/|u a|)*∏ i∈univ.erase a,(2*W i)):=by
 cases d with
 | zero=>omega
 | succ n=>
   let K:Set (RV (n+1)):={x | (∀ i,|x i|<=W i)/\ |∑ i,u i*x i|<=r};have f:IsClosed K:=(show IsClosed {x:RV (n+1) | ∀ i,|x i|<=W i} by rw[show {x:RV (n+1) | ∀ i,|x i|<=W i}=⋂ i,{x | |x i|<=W i} by ext;simp];exact isClosed_iInter fun i=>isClosed_le (continuous_abs.comp (continuous_apply i)) continuous_const).inter
    (isClosed_le (continuous_abs.comp (continuous_finsetSum _ fun i _=>continuous_const.mul (continuous_apply i))) continuous_const)
   let e:=MeasurableEquiv.piFinSuccAbove (fun _:Fin (n+1)=>ℝ) a;rw[((volume_preserving_piFinSuccAbove (fun _:Fin (n+1)=>ℝ) a).symm.measure_preimage_emb e.symm.measurableEmbedding K).symm];change (volume.prod volume) (e.symm ⁻¹' K)<=_;rw[Measure.prod_apply_symm (f.measurableSet.preimage e.symm.measurable)];let g:Set (Fin n->ℝ):=Set.univ.pi fun j=>Set.Icc (-W (a.succAbove j)) (W (a.succAbove j));have k:∀ y:Fin n->ℝ,volume ((fun b:ℝ=>(b,y)) ⁻¹' (e.symm ⁻¹' K))<=g.indicator (fun _=>m6W (2*r/|u a|)) y:=fun y=>by
    by_cases m:y∈g
    . rw[Set.indicator_of_mem m];let S:=∑ j:Fin n,u (a.succAbove j)*y j
      refine(measure_mono (show _⊆Set.Icc (-S/u a-r/|u a|) (-S/u a+r/|u a|) from fun b o=>?_)).trans_eq (by rw[Real.volume_Icc];congr 1;ring)
      have l:∑ i:Fin (n+1),u i*(e.symm (b,y)) i=u a*b+S:=by
       rw[Fin.sum_univ_succAbove _ a];simp only[S];congr 1
       . congr 1;exact Fin.insertNth_apply_same (α:=fun _=>ℝ) a b y
       . exact m64 fun j _=>by congr 1;exact Fin.insertNth_apply_succAbove (α:=fun _=>ℝ) a b y j
      have q:|u a*(b-(-S/u a))|<=r:=by rw[show u a*(b-(-S/u a))=u a*b+S by field_simp;ring];exact l ▸ o.2
      rw[abs_mul] at q;have s:=abs_le.mp ((le_div_iff₀' (abs_pos.mpr p)).mpr q);exact ⟨by linarith,by linarith⟩
    . rw[Set.indicator_of_notMem m,show (fun b:ℝ=>(b,y)) ⁻¹' (e.symm ⁻¹' K)=∅ by
       ext b;simp only[Set.mem_preimage,Set.mem_empty_iff_false,iff_false];intro w;apply m;intro j _;have t:=w.1 (a.succAbove j);have s:(e.symm (b,y)) (a.succAbove j)=y j:=Fin.insertNth_apply_succAbove (α:=fun _=>ℝ) a b y j;rw[s,abs_le] at t;exact t,measure_empty]
   have v:volume g=m6W (∏ i∈univ.erase a,(2*W i)):=by
    rw[volume_pi,Measure.pi_pi,prod_congr rfl fun j _=>show volume (Set.Icc (-W (a.succAbove j)) (W (a.succAbove j)))=m6W (2*W (a.succAbove j)) by rw[Real.volume_Icc];congr 1;ring,←ENNReal.ofReal_prod_of_nonneg fun j _=>by linarith[z (a.succAbove j)]];congr 1;exact prod_bij (fun (j:Fin n) _=>a.succAbove j) (fun j _=>mem_erase.mpr ⟨Fin.succAbove_ne a j,mem_univ _⟩) (fun _ _ _ _ h=>Fin.succAbove_right_injective h) (fun i hi=>by obtain ⟨j,rfl⟩:=Fin.exists_succAbove_eq (mem_erase.mp hi).1;exact ⟨j,mem_univ j,rfl⟩) fun _ _=>rfl
   exact(lintegral_mono k).trans_eq (by rw[lintegral_indicator (MeasurableSet.univ_pi fun _=>measurableSet_Icc),setLIntegral_const,v,←ENNReal.ofReal_mul (by positivity)])
lemma m6ay {d:ℕ} {w z:ℝ} {n:ZB d} {o:m61 d} {A:m69 hC} (C:m6o J A w z n o) {p:ZV d} (j:p∈n.tF) {F:m61 d} (f:F⊆o) (q:w*#o<=#F) {H:Submodule ℝ (RV d)} (r:Module.finrank ℝ H<=d-1) (s:∀ x∈F,zR (x-p)∈H):False:=by
 obtain ⟨u,B,D,E,⟨b,k,_,_,_,_,a,_,e,g,l,_,_,h,i⟩,hvg,hsFp,hcs1,hsbg⟩:=m6ax C j f q;have t:=m6au C.hJ (m6a1 j) r (by omega:d-1<=d) ((e.trans a).trans (m6a8 (f.trans C.hAB) p))
  (fun v y=>by obtain ⟨x,m,rfl⟩:=m6E (a (e y));exact s x m) hsFp g b hcs1 k l h i
 rw[m6a7,show d-(d-1)=1 by omega,pow_one] at t;exact m6bi b C.hg0 n.vP (by grw [hvg,t]) hsbg
def m6J (J:ℕ->ℕ) (sp:m69 hC) (d:ℕ):ℝ:=1/(64*↑d*(18*↑d*↑(J d)/sp.c d)^d)
lemma m6ak (hJ:m6q J) (a:m69 hC) {d:ℕ} (hd:1<=d):0< m6J J a d:=by have:(0:ℝ)< d:=m6D (by omega);have:(0:ℝ)< J d:=m6D (by have:=hJ.1 d;omega);have:=(a.ok d hd).1;unfold m6J;positivity
lemma m6c2 {d:ℕ} {de ga:ℝ} {e:ZB d} {X:m61 d} {Y:m69 hC} (C:m6o J Y de ga e X) {a:ZV d} (q:a∈e.tF) {u:RV d} {r b:ℝ} (hr:0< r) (e0:0< b) {G:Fin d} (c0:r/(d*b)< |u G| *e.width G) (e1:2*(18*↑d*↑(J d)/Y.c d)^d*d*b<=ga) {S:m61 d} (l:S⊆X) (d8:∀ x∈S,|m6O u x a|<=r):(#S:ℝ)<4*↑(J d)*de*#X:=by
 by_contra d2;push Not at d2;have a0:=C.hJ.1 d;have L:(0:ℝ)< d:=m6D (by have:=C.hd;omega);have B:=(Y.ok d C.hd).1;have D:de*#X<=#S:=by nlinarith[m6a a0,m6al #X]
 let f:RV d →ₗ[ℝ] ℝ:=⟨⟨fun y=>∑ k,u k*y k,fun _ _=>by simp[mul_add,m6e]⟩,fun _ _=>by simp[mul_sum,mul_left_comm]⟩;let K:Set (RV d):=m6k e.width ∩ f ⁻¹' Set.Icc (-r) r;obtain ⟨d3,a8,a9,b0⟩:=m6ba e.width;have n:Convex ℝ K:=a8.inter ((convex_Icc (-r) r).linear_preimage f);have E:∀ y∈K,-y∈K:=fun y hy=>⟨a9 y hy.1,by simp only[Set.mem_preimage,Set.mem_Icc,f.map_neg];exact ⟨by linarith[hy.2.2],by linarith[hy.2.1]⟩⟩;obtain ⟨k,e5,w,N,_,b1,d4,b2,g⟩:=C.hJ.2 d ⊤ K ⟨d3,by simp[f,hr.le]⟩ n E (b0.subset fun _ hy=>hy.1);have s:∀ x∈S,zR (x-a)∈K:=fun x m=>⟨fun i=>by simpa only[m6b4] using m6bb (m6a1 q) (m6a8 (l.trans C.hAB) a (mem_image_of_mem _ m)) i,abs_le.mp (by simpa only[f,LinearMap.coe_mk,AddHom.coe_mk,m6O,zR,Pi.sub_apply,Int.cast_sub] using d8 x m)⟩;by_cases e4:k< d
 . let H:=Submodule.span ℝ (Set.range fun i:Fin k=>zR (w i))
   exact m6ay C q l D ((m6ai w).trans (by omega)) fun x m=>by
    obtain ⟨c,_,hc⟩:=g (x-a) trivial (s x m);rw[←hc,zRu];exact H.sum_mem fun i _=>by rw[zRm];exact H.smul_mem _ (Submodule.subset_span (Set.mem_range_self i))
 rcases (show k=d by omega) with rfl
 by_cases o:∃ z:Fin k,N z=1
 . obtain ⟨z,b3⟩:=o
   let M:ZV k->ZV k:=fun x=>if m:x∈S then (g (x-a) trivial (s x m)).choose else 0;have O:∀ x (m:x∈S),(∀ i,|M x i| <(J k*N i:ℤ))/\∑ i,M x i•w i=x-a:=fun x m=>by simpa only[M,dif_pos m] using (g (x-a) trivial (s x m)).choose_spec
   let vs:=Icc (-(J k:ℤ)) (J k:ℤ);obtain ⟨t0,_,d5⟩:=m6bg (S:=S) (V:=vs) (fun x=>M x z) (fun x m=>mem_Icc.mpr (by have:=abs_lt.mp ((O x m).1 z);rw[b3,Nat.cast_one,mul_one] at this;omega)) ⟨0,mem_Icc.mpr ⟨by omega,by omega⟩⟩;let F:=S.filter fun x=>M x z=t0;have R:F⊆X:=m6h.trans l;have a1:de*#X<=#F:=by
    change (#S:ℝ)<=#vs*#F at d5;have:(#vs:ℝ)<=4*↑(J k):=by exact_mod_cast (show #vs<=4*J k by rw[Int.card_Icc];omega)
    have:(0:ℝ)< J k:=m6D (by omega);nlinarith[m6al #F]
   obtain ⟨x0,p⟩:F.Nonempty:=card_pos.mp (by have:=(C.hs F R a1).1;have:=(Y.ok k C.hd).2.2.2.1;omega);let H:=Submodule.span ℝ ((fun i:Fin k=>zR (w i)) '' ((univ.erase z:Finset (Fin k)):Set (Fin k)));have c1:Module.finrank ℝ H<=k-1:=(finrank_span_le_card _).trans (by rw[Set.toFinset_image,toFinset_coe];exact card_image_le.trans_eq (by rw[card_erase_of_mem (mem_univ z),card_univ,Fintype.card_fin]));exact m6ay C (C.hAB (R p)) R a1 c1 fun x b9=>by
    have c2:x-x0=∑ i∈univ.erase z,(M x i-M x0 i)•w i:=by
     rw[show x-x0=(x-a)-(x0-a) by abel,←(O x (m6P b9).1).2,←(O x0 (m6P p).1).2,←sum_sub_distrib,←add_sum_erase _ _ (mem_univ z),(m6P b9).2.trans (m6P p).2.symm,sub_self,zero_add];exact m64 fun _ _=>(sub_zsmul _ _ _).symm
    rw[c2,zRu];exact H.sum_mem fun i hi=>by rw[zRm];exact H.smul_mem _ (Submodule.subset_span ⟨i,mem_coe.mpr hi,rfl⟩)
 push Not at o;have T:∀ i,2<=N i:=fun i=>by have:=b1 i;have:=o i;omega
 let Ai:=Matrix.of (fun r j=>w j r);let Z:=(Int.castRingHom ℝ).mapMatrix Ai;let Eb:Set (RV k):=Set.univ.pi fun i=>Set.Icc (-↑(N i-1)/k) (↑(N i-1)/k);have c3:Matrix.toLin' Z '' Eb⊆K:=by
  rintro _ ⟨t,ht,rfl⟩;rw[show Matrix.toLin' Z t=∑ i:Fin k,(1/(k:ℝ))•(((k:ℝ)*t i)•zR (w i)) by ext r;simp only[Matrix.toLin'_apply,Matrix.mulVec,dotProduct,Z,RingHom.mapMatrix_apply,Matrix.map_apply,Int.coe_castRingHom,Ai,Matrix.of_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,zR];exact m64 fun _ _=>by field_simp[L.ne']];refine n.sum_mem (fun _ _=>by positivity) (by rw[sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul];field_simp) fun i _=>?_
  have a2:=ht i (Set.mem_univ i);let h:ℤ:=↑(N i-1);have U:(0:ℝ)< h:=by exact_mod_cast (show (0:ℤ)< h by dsimp[h];have:=T i;omega)
  have c4:|(k:ℝ)*t i|<=h:=abs_le.mpr ⟨by have:=m62 a2.1 L.le;have:(k:ℝ)*(-↑(N i-1)/k)= -h:=(by simp[h];field_simp);linarith,by have:=m62 a2.2 L.le;have:(k:ℝ)*(↑(N i-1)/k)=h:=(by simp[h];field_simp);linarith⟩;set v:=(h:ℝ)•zR (w i);have a3:v∈K:=by
   have h1:=b2 (Pi.single i h) fun j=>by
    by_cases a7:j=i
    . subst a7;simp[h,abs_of_nonneg];have:=T j;omega
    . simp[Pi.single_eq_of_ne a7];have:=b1 j;omega
   rwa[show ∑ j:Fin k,(Pi.single i h:ZV k) j•w j=h•w i by rw[sum_eq_single i] <;> simp (config:={contextual:=true}),zRm] at h1
  let al:=((k:ℝ)*t i/h+1)/2;have a4:0<=al/\al<=1:=by
   have:|(k:ℝ)*t i/h|<=1:=by rw[abs_div,abs_of_pos U,div_le_one U];exact c4
   rw[abs_le] at this;constructor <;> dsimp[al] <;> linarith
  rw[show ((k:ℝ)*t i)•zR (w i)=al•v+(1-al)•(-v) by dsimp[v];rw[smul_neg,smul_smul,smul_smul,←sub_eq_add_neg,←sub_smul];congr 1;dsimp[al];field_simp[U.ne'];ring];exact n a3 (E _ a3) a4.1 (by linarith[a4.2]) (by ring)
 have c5:m6W ((2/(k:ℝ))^k*∏ i:Fin k,↑(N i-1))<=volume K:=by
  have c6:(1:ℝ)<= |LinearMap.det (Matrix.toLin' Z)|:=by rw[LinearMap.det_toLin',←show (Ai.det:ℝ)=Z.det from RingHom.map_det (Int.castRingHom ℝ) Ai];exact_mod_cast Int.one_le_abs (m6bk d4).1
  have c7:volume Eb=m6W ((2/(k:ℝ))^k*∏ i:Fin k,↑(N i-1)):=by
   rw[volume_pi,Measure.pi_pi,prod_congr rfl fun i _=>show volume (Set.Icc (-↑(N i-1)/(k:ℝ)) (↑(N i-1)/(k:ℝ)))=m6W ((2/(k:ℝ))*↑(N i-1)) by rw[Real.volume_Icc];congr 1;ring,←ENNReal.ofReal_prod_of_nonneg fun _ _=>by positivity,←m6s]
  exact(one_mul _).symm.trans_le (c7 ▸ (m63 (ENNReal.ofReal_one ▸ m6bs c6) zero_le).trans ((Measure.addHaar_image_linearMap volume (Matrix.toLin' Z) Eb).symm.trans_le (measure_mono c3)))
 have a5:u G≠0:=fun h0=>by rw[h0,abs_zero,zero_mul] at c0;linarith[show 0< r/((k:ℝ)*b) by positivity]
 have c8:volume K<=m6W ((k:ℝ)*b*2^k*e.vol):=by
  rw[show K={x:RV k | (∀ i,|x i|<=e.width i)/\ |∑ i,u i*x i|<=r} by ext y;simp[K,f,m6k,abs_le]];refine(m6c1 C.hd (fun i=>↑(e.width i)) (fun i=>m6D (e.wP i)) u hr a5).trans (m6bs ?_);have c9:2*r/|u G|<=2*k*b*e.width G:=(m6I (abs_pos.mpr a5)).mpr (by linarith[(div_lt_iff₀ (by positivity)).mp c0]);have d0:(2*(e.width G:ℝ))*∏ i∈univ.erase G,(2*(e.width i:ℝ))=(2:ℝ)^k*e.vol:=by rw[mul_prod_erase univ (fun i=>2*(e.width i:ℝ)) (mem_univ G),←m6s];simp[ZB.vol]
  exact(m63 c9 (prod_nonneg fun _ _=>by positivity)).trans_eq (by linear_combination (k:ℝ)*b*d0)
 let Q:GAP (ZV k) k:=⟨0,w,fun i=>-↑(J k*N i),fun i=>↑(J k*N i),fun i=>by omega⟩;have d1:(Q.vol:ℝ)<=(6*↑k*↑(J k))^k*k*b*e.vol:=by
  have hm:=m62 ((ENNReal.ofReal_le_ofReal_iff (by positivity)).mp (c5.trans c8)) (m6A (by positivity:(0:ℝ)<=3*k*J k) k);rw[←m68,←mul_pow,show 3*(k:ℝ)*J k*(2/k)=6*J k by field_simp;ring] at hm;have h1:(Q.vol:ℝ)<=(6*(J k:ℝ))^k*∏ i:Fin k,↑(N i-1):=by
   rw[m6s];simp only[GAP.vol,ZB.vol,Nat.cast_prod];exact prod_le_prod (fun _ _=>m65) fun i _=>by
    simp only[ZB.width,GAP.cB,Q];have:=T i;have:=a0;exact_mod_cast (show (((J k*N i:ℕ):ℤ) - -↑(J k*N i)+1).toNat<=6*J k*(N i-1) by rw[show ((J k*N i:ℕ):ℤ) - -↑(J k*N i)+1=↑(2*(J k*N i)+1) by push_cast;ring,Int.toNat_natCast];have:1<=N i-1/\N i-1+1=N i:=(by omega);nlinarith)
  exact(h1.trans hm).trans_eq (by rw[show (3*(k:ℝ)*J k)^k*(k*b*2^k*e.vol)=((3*k*J k)^k*2^k)*k*b*e.vol by ring,←mul_pow];congr 4;ring)
 obtain ⟨d9,S',PS,qS,⟨_,b4,_,_,_,_,W,_,b5,b6,b7,_,_,b8,A⟩,hvg,hsSp,hcsS,_⟩:=m6ax C q l D;have e2:=m6at (P:=Q) (GAP.zMC ⟨rfl,fun i=>⟨by simp[Q];positivity,by simp[Q];positivity⟩⟩) (fun v hv=>by obtain ⟨x,d6,rfl⟩:=m6E (W (b5 hv));obtain ⟨c,hc,d7⟩:=g (x-a) trivial (s x d6);exact mem_image.mpr ⟨c,m67.mpr fun i=>by have:=abs_lt.mp (hc i);simp[GAP.cB,Q];omega,by simpa[GAP.eval,Q] using d7⟩) hsSp b6 B hcsS b4 b7 b8 A;have a6:=m6ah B (le_of_mul_le_mul_right (by linarith:(Y.c k/3)^k*PS.vol*(m6N #(S.image (· - a)):ℝ)^k<=Q.vol*(m6N #(S.image (· - a)):ℝ)^k) (pow_pos (m6D hsSp) k));have e3:ga*e.vol<=(ga/2)*e.vol:=by
  grw [hvg,a6,d1];rw[←m68,←m68,←m68,←mul_pow,show 3/Y.c k*(6*↑k*↑(J k))=18*↑k*↑(J k)/Y.c k by ring];gcongr;linarith
 nlinarith[m6af e,C.hg0]
lemma m6c3 {d:ℕ} {l H K:ℝ} {p:ZB d} {g:m61 d} {q:m69 hC} (C:m6o J q H K p g) (z:0< l) {a:ZV d} (A:a∈p.tF) {b:m61 d} (B:b⊆g) {c:ZV d->ℝ} (E:∀ x∈b,0<=c x/\c x<=2/(l*#g)) (F:(1:ℝ)/4<=∑ x∈b,c x) (a8:64*↑(J d)*H<=l) (v:RV d) (hv:∀ k:Fin d,|v k|<=m6J J q d*l*K*#g*p.width k):∃ t:ZV d->ℝ,(∀ x∈b,|t x|<=(l*#g/4)*c x)/\v=∑ x∈b,t x•zR (x-a):=by
 let o:=m6J J q d*l*K;have Z:(0:ℝ)< d:=m6D (by have:=C.hd;omega);have a0:(0:ℝ)< J d:=m6D (by have:=C.hJ.1 d;omega);have U:=(q.ok d C.hd).1;have V:0< o:=mul_pos (mul_pos (m6ak C.hJ q C.hd) z) C.hg0;have a1:(0:ℝ)<#g:=by by_contra h;have:#g=0:=Nat.eq_zero_of_le_zero (by exact_mod_cast not_lt.mp h);have:b=∅:=card_eq_zero.mp (by have:=m6K B;omega);rw[this,sum_empty] at F;norm_num at F
 let D:=fun x=>(l*#g/4)*c x;have i:∀ x∈b,0<=D x:=fun x e=>m66 (by positivity) (E x e).1;let Tb:Set (b->ℝ):=Set.univ.pi fun x=>Set.Icc (-D x.1) (D x.1);have L:v∈(fun f=>∑ x:b,f x•zR (x.1-a)) '' Tb:=by
  by_contra O;obtain ⟨u,m,a7,n⟩:=m6bh (convex_pi fun _ _=>convex_Icc _ _) (isCompact_univ_pi fun _=>isCompact_Icc) O;have a2:0< m:=by have:=n 0 fun x _=>⟨by change -D x.1<=0;linarith[i x.1 x.2],i x.1 x.2⟩;simpa using this
  let G:b->ℝ:=fun x=>if (0:ℝ)<=m6O u x.1 a then D x.1 else -D x.1;have a3:∑ x∈b,D x*|m6O u x a| < m:=by
   have W:=n G fun x _=>by dsimp[G];split_ifs <;> exact ⟨by linarith[i x.1 x.2],by linarith[i x.1 x.2]⟩
   rw[show ∑ x:b,G x*m6O u x.1 a=∑ x∈b,D x*|m6O u x a| from (m64 fun x _=>by
    dsimp[G];split_ifs with P
    . rw[abs_of_nonneg P]
    . push Not at P;rw[abs_of_neg P];ring).trans (sum_coe_sort b _)] at W;exact W
  obtain ⟨Q,R⟩:∃ Q:Fin d,m/(d*o*#g)< |u Q| *p.width Q:=by
   by_contra X;push Not at X;have:∑ k,u k*v k<=m:=((sum_le_sum fun _ _=>le_abs_self _).trans (sum_le_sum fun k _=>by have a4:|v k|<=o*#g*p.width k:=hv k;rw[abs_mul];nlinarith[abs_nonneg (u k)]:_<=∑ k,(|u k| *p.width k)*(o*#g))).trans ((sum_le_sum fun k _=>m63 (X k) (by positivity)).trans_eq (by rw[sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul];field_simp));linarith
  let j:=K/(2*(18*↑d*↑(J d)/q.c d)^d*d);have s:0< j:=by dsimp[j];have:=C.hg0;positivity
  let r:=j*m/(o*#g);have M:0< r:=by dsimp[r];positivity
  let S:=b.filter fun x=>|m6O u x a|<=r;have N:=m6c2 C A M s (by rw[show r/(d*j)=m/(d*o*#g) by dsimp[r];field_simp];exact R) (by dsimp[j];rw[mul_div_cancel₀ _ (by positivity)]) (m6h.trans B) fun _ e=>(m6P e).2;have a5:∑ x∈S,c x<=1/8:=(((sum_le_sum fun x e=>(E x (m6P e).1).2).trans_eq (by rw[sum_const,nsmul_eq_mul])).trans ((m63 N.le (by positivity)).trans_eq (show (4*↑(J d)*H*#g)*(2/(l*#g))=8*↑(J d)*H/l by field_simp;ring))).trans ((m6I z).mpr (by linarith));have w:(1:ℝ)/8<=∑ x∈b \ S,c x:=by linarith[sum_sdiff (filter_subset (fun x=>|m6O u x a|<=r) b) (f:=c)]
  have a6:m<=∑ x∈b,D x*|m6O u x a|:=by
   rw[show m=r*((l*#g/4)*(1/8)) by dsimp[r,o,j,m6J];field_simp[C.hg0.ne'];ring];grw [w];rw[←m68,mul_sum];exact(sum_le_sum fun x e=>by
    rw[show r*(l*#g/4)*c x=D x*r by dsimp[D];ring];exact m62 (by by_contra h;exact(mem_sdiff.mp e).2 (mem_filter.mpr ⟨(mem_sdiff.mp e).1,le_of_not_ge h⟩)) (i x (mem_sdiff.mp e).1)).trans
     (sum_le_sum_of_subset_of_nonneg sdiff_subset fun x e _=>m66 (i x e) (abs_nonneg _))
  linarith
 obtain ⟨Y,T,y⟩:=L;refine ⟨fun x=>if e:x∈b then Y ⟨x,e⟩ else 0,fun x e=>by simp only[dif_pos e];exact abs_le.mpr (T ⟨x,e⟩ (Set.mem_univ _)),?_⟩;rw[←y,←sum_attach b (fun x=>(if e:x∈b then Y ⟨x,e⟩ else 0)•zR (x-a)),m64 fun x _=>by rw[dif_pos x.2]];rfl
lemma m6c4 {d:ℕ} {o M:m61 d} (U:Disjoint o M) {a:GAP (ZV d) d} (b:a.iS) (F:∀ i,1<=a.hi i) (t:a.iP) (G:o⊆a.tF) (V:m6a6 (fun j=>zR (a.step j))) {q:ZV d} (H:q∈m6a5 (Set.range a.step)) {c:ℝ} (a0:0< c) {J:ℕ} (K:((m6H a (c*J) (by positivity) b).tF.image (·+q))⊆sS M) (a1:sqrt (↑d*#o)<=c*J/2) (Y:1<=c*J) {y:ZV d} (L:y∈m6a5 (Set.range a.step)) {p:ZV d->ℝ} (hp:∀ x∈o,0<=p x/\p x<=1) (W:zR (y-q)=∑ x∈o,p x•zR x):y∈sS (o ∪ M):=by
 let w:=m6u a o;have N:=m6b9 G t;have r:=m6as G;have k:w⊆a.cB.tF:=filter_subset _ _;obtain ⟨m,D⟩:∃ m:ZV d,y-q=∑ j,m j•a.step j:=
  AddSubgroup.closure_induction (p:=fun z _=>∃ m:ZV d,z=∑ j,m j•a.step j)
   (fun _ hz=>by obtain ⟨X,rfl⟩:=hz;exact ⟨Pi.single X 1,by rw[sum_eq_single X] <;> simp (config:={contextual:=true})⟩) ⟨0,by simp⟩
   (fun _ _ _ _ ⟨m1,g⟩ ⟨m2,l⟩=>⟨m1+m2,by rw[g,l,←m6e];exact m64 fun _ _=>(add_zsmul _ _ _).symm⟩)
   (fun _ _ ⟨m,h⟩=>⟨-m,by rw[h,←sum_neg_distrib];exact m64 fun _ _=>(neg_zsmul _ _).symm⟩) (AddSubgroup.sub_mem _ L H)
 have O:∀ j:Fin d,(m j:ℝ)=∑ v∈w,p (a.eval v)*(v j:ℝ):=by
  have g:zR (y-q)=∑ j,(m j:ℝ)•zR (a.step j):=by rw[D,zRu];exact m64 fun _ _=>zRm _ _
  have l:zR (y-q)=∑ j,(∑ v∈w,p (a.eval v)*(v j:ℝ))•zR (a.step j):=by
   rw[W,←r,sum_image fun v1 g v2 l h=>t (k g) (k l) h,
    m64 fun v _=>show p (a.eval v)•zR (a.eval v)=∑ j,(p (a.eval v)*(v j:ℝ))•zR (a.step j) by
     generalize p (a.eval v)=pv;rw[GAP.eval,b.1,zero_add,zRu,smul_sum];exact m64 fun _ _=>by rw[zRm,smul_smul],sum_comm]
   exact m64 fun _ _=>sum_smul.symm
  exact fun j=>sub_eq_zero.mp (Fintype.linearIndependent_iff.mp V (fun j=>(m j:ℝ) - ∑ v∈w,p (a.eval v)*(v j:ℝ)) (by simp only[sub_smul,sum_sub_distrib];rw[←g,←l,sub_self]) j)
 obtain ⟨n,s,E⟩:=m6bz w (fun j=>(a.hi j:ℝ)) (fun j=>by exact_mod_cast (show (0:ℤ)<=a.hi j by have:=F j;omega))
  (fun v T j=>by have g:=m67.mp (k T) j;dsimp[GAP.cB] at g;have l:=b.2 j;exact_mod_cast (abs_le.mpr ⟨by omega,g.2⟩:|v j|<=a.hi j))
  (fun v=>p (a.eval v)) fun v T=>hp _ (r ▸ mem_image_of_mem _ T)
 let e:=m - ∑ v∈n,v;let Q:=m6H a (c*J) (by positivity) b;have P:Q.iS:=m6aj b _ (by positivity);have R:e∈Q.cB.tF:=m67.mpr fun j=>by
  have B:=E j;rw[←O j,N] at B;have:(1:ℝ)<=a.hi j:=by exact_mod_cast F j
  have S:|e j|<=Q.hi j:=by exact_mod_cast ((show |(e j:ℝ)|<=c*J*a.hi j/2 by rw[show (e j:ℝ)=(m j:ℝ)-((∑ v∈n,v) j:ℝ) by simp[e]];exact B.trans (by nlinarith)).trans (m6bf (by nlinarith)))
  have:=P.2 j;change Q.lo j<=e j/\e j<=Q.hi j;rw[abs_le] at S;omega
 have g:a.eval (∑ v∈n,v)∈sS o:=by
  rw[show a.eval (∑ v∈n,v)=∑ v∈n,a.eval v by simp only[GAP.eval,b.1,zero_add];rw[sum_comm];exact m64 fun j _=>by rw[Finset.sum_apply,sum_smul],←sum_image (f:=fun x:ZV d=>x) fun v1 g v2 l h=>t (k (s g)) (k (s l)) h];exact mem_image.mpr ⟨n.image a.eval,mem_powerset.mpr (r ▸ image_subset_image s),rfl⟩
 have l:a.eval e+q∈sS M:=K (mem_image.mpr ⟨a.eval e,mem_image.mpr ⟨e,R,by simp[GAP.eval,m6H,GAP.rS,b.1]⟩,rfl⟩);have Z:y=a.eval (∑ v∈n,v)+(a.eval e+q):=by
  have C:∀ u v,a.eval (u+v)=a.eval u+a.eval v:=fun u v=>by simp only[GAP.eval,b.1,zero_add,Pi.add_apply];rw[←m6e];exact m64 fun _ _=>add_zsmul _ _ _
  rw[←add_assoc,←C,show (∑ v∈n,v)+e=m by dsimp[e];abel,GAP.eval,b.1,zero_add,←D,sub_add_cancel]
 rw[sUD U,Z];exact add_mem_add g l
lemma m6c5 (g:m69 hC) {d:ℕ} (hd:1<=d) {h r:ℝ} {n:ZB d} {a:m61 d} (y:2<=#a) (o:(n.vol:ℝ)<=(#a:ℝ)^(6:ℝ)) (p:(#a:ℝ)^(-(1:ℝ)/4)<=h) (k:↑(g.m0 d)<=h*#a) (l:1<=g.c d*(h*#a/(log #a)^2-1)) (m:(27*↑(J d)/g.c d)^d/r< h*#a/(log #a)^2-1):m6aw J g h r n a:=fun T x f=>by
 have q:=(g.ok d hd).1;have i:(0:ℝ)<#a:=m6D (by omega);have s:(1:ℝ)<=#a:=m6a (by omega);have b:g.m0 d<=#T:=by exact_mod_cast k.trans f
 have t:4<=#T:=(g.ok d hd).2.2.2.1.trans b;have u:(0:ℝ)<#T:=m6D (by omega);have v:0< log #T:=log_pos (Nat.one_lt_cast.mpr (by omega));have j:(n.vol:ℝ)<=(#T:ℝ)^(10:ℝ):=by
  grw [o]
  calc (#a:ℝ)^(6:ℝ)<=((#a:ℝ)^((3:ℝ)/4))^(10:ℝ):=by rw[←m6C i.le];gcongr;norm_num
   _<=(#T:ℝ)^(10:ℝ):=by gcongr;rw[show (3:ℝ)/4= -(1:ℝ)/4+1 by norm_num,rpow_add_one i.ne'];grw [p,f]
 have e:h*#a/(log #a)^2-1<=m6N #T:=by
  have w:h*#a/(log #a)^2<=#T/(log #T)^2:=div_le_div₀ (by positivity) f (by positivity) (by gcongr);dsimp[m6N];linarith[Nat.lt_floor_add_one ((#T:ℝ)/(log #T)^2)]
 exact ⟨b,j,by grw [l,e],m.trans_le e⟩
lemma m6c6 {α:Type*} [m6X α] {d:Finset α} {a:α} (p:a∈d) {q:ℝ} (A:0< q) (n:16<=#d) (w:72<=(#d:ℝ)*q) {c:α->ℝ} (o:∀ x∈d.erase a,0<=c x/\c x<=2/(q*#d)) (h:∑ x∈d.erase a,c x=1):∃ b e:Finset α,Disjoint b e/\b ∪ e=d.erase a/\(#d:ℝ)/4<=#b/\(#d:ℝ)/4<=#e/\(1:ℝ)/3<=∑ x∈b,c x/\(1:ℝ)/3<=∑ x∈e,c x:=by
 let E:=d.erase a;have y:(16:ℝ)<=#d:=by exact_mod_cast n
 have z:(#E:ℝ)=#d-1:=by dsimp[E];rw[card_erase_of_mem p,Nat.cast_sub (by omega)];simp
 have i:(0:ℝ)<#E:=by linarith
 have j:∑ S∈E.powerset,m6B E (fun _=>(1/2:ℝ)) S*(((#S:ℝ)-#E/2)^2/#E+36*((∑ x∈S,c x)-1/2)^2)<=1/2:=by
  have k:=(m6ab E (fun _=>(1/2:ℝ))).2 (fun _=>1);simp only[sum_const,nsmul_eq_mul,mul_one] at k;have l:=(m6ab E (fun _=>(1/2:ℝ))).2 c;rw[←mul_sum,h,mul_one] at l;have r:∑ x∈E,(1/2:ℝ)*(1-1/2)*c x^2<=1/144:=
   ((sum_le_sum fun x v=>by have:c x<=1/36:=(o x v).2.trans ((m6I (by positivity)).mpr (by linarith));nlinarith[(o x v).1]:_<=∑ x∈E,(1/4:ℝ)*((1/36)*c x))).trans_eq (by rw[←mul_sum,←mul_sum,h];ring)
  trans ((1:ℝ)/#E)*(∑ S∈E.powerset,m6B E (fun _=>(1/2:ℝ)) S*((#S:ℝ)-#E*(1/2))^2)+36*(∑ S∈E.powerset,m6B E (fun _=>(1/2:ℝ)) S*((∑ x∈S,c x)-1/2)^2)
  . exact le_of_eq (by rw[mul_sum,mul_sum,←m6e];exact m64 fun _ _=>by ring)
  rw[k,l];have:((1:ℝ)/#E)*(#E*((1/2)*(1-1/2)))=1/4:=by field_simp;ring
  linarith
 obtain ⟨b,m,u⟩:=m6bj (fun _ _=>by norm_num:∀ x∈E,(0:ℝ)<=1/2/\(1/2:ℝ)<=1) j;let e:=E \ b;have f:Disjoint b e:=disjoint_sdiff;have g:b ∪ e=E:=union_sdiff_of_subset m;have s:((#b:ℝ)-#E/2)^2<=#E/2:=by have:=(m6I i).mp (by nlinarith[m6d ((∑ x∈b,c x)-1/2)]:((#b:ℝ)-#E/2)^2/#E<=1/2);linarith
 have t:(#b:ℝ)+#e=#E:=by exact_mod_cast (card_union_of_disjoint f).symm.trans (congrArg card g)
 have:((∑ x∈b,c x)-1/2)^2<=1/72:=by nlinarith[m6R (m6d ((#b:ℝ)-#E/2)) i.le]
 have:(∑ x∈b,c x)+(∑ x∈e,c x)=1:=by rw[←sum_union f,g];exact h
 exact ⟨b,e,f,g,by nlinarith,by nlinarith,by nlinarith,by nlinarith⟩
lemma m6bm {d:ℕ} {i Z H:ℝ} {r:ZB d} {z:m61 d} {g:m69 hC} (C:m6o J g Z H r z) (n:0< i) (d9:i<=1/2) (e0:Z<=1/4) (d1:64*↑(J d)*Z<=i) (b0:16<=#z) (d2:sqrt (↑d*#z)<=g.c d*(Z*#z/(log #z)^2-1)/2) (b1:48*(g.c d)⁻¹<=i*log (#z/4)) (b2:8*(g.c d)⁻¹/log (#z/4)<=m6J J g d*i*H) {a:ZV d} (b3:a∈r.tF) {c:ZV d->ℝ} {b M B:m61 d} {Pi:GAP (ZV d) d} {S y:ZV d} (w:b⊆z) (U:(#z:ℝ)/4<=#b) (t:∀ x∈b,0<=c x/\c x<=2/(i*#z)) (b4:(1:ℝ)/3<=∑ x∈b,c x) (b5:Pi.iS) (b6:Pi.iP) (d3:m6a6 (fun j=>zR (Pi.step j))) (d4:m6a2 (g.c d) (g.dm d) (g.m0 d) (m6M r (-a)) (b.image (· - a)) d M B Pi S) (d5:∀ k,|(S k:ℝ)|<=m6N #(b.image (· - a))*r.width k) (b7:y∈m6a5 (Set.range Pi.step)) (d6:∀ k,|(y k:ℝ)-(i*#z/4)*∑ x∈b,c x*((x k-a k:ℤ):ℝ)|<=(m6J J g d*i*H/2)*#z*r.width k):y∈sS (b.image (· - a)):=by
 set m:=#z;have l:(0:ℝ)< m:=m6D (by omega);have s:=(g.ok d C.hd).1;have N:1<=(g.c d)⁻¹:=(one_le_inv₀ s).mpr (g.ok d C.hd).2.1;have A:0< log ((m:ℝ)/4):=log_pos (by linarith[show (16:ℝ)<=m by exact_mod_cast b0]);have O:1<=log ((m:ℝ)/4):=by nlinarith
 let Si:=b.image (· - a);have o:#Si=#b:=m6T b m6z;have P:Z*m<=#b:=by nlinarith
 obtain ⟨_,_,_,_,_,_,q,a4,F,a5,a6,d0,a7,_,Y⟩:=d4;let p:=M \ B;let e:=b.filter fun x=>x-a∈p;have K:e.image (· - a)=p:=by ext v;simp only[mem_image,e,mem_filter];exact ⟨fun ⟨_,⟨_,h⟩,he⟩=>he ▸ h,fun hv=>by obtain ⟨x,G,rfl⟩:=m6E (q (mem_sdiff.mp hv).1);exact ⟨x,⟨G,hv⟩,rfl⟩⟩
 have D:(0:ℝ)<#b:=m6c (div_pos l (by norm_num)) U;have E:=log_le_log (div_pos l (by norm_num)) U;have Q:1<=log #b:=O.trans E;have L:0< log #b:=by linarith only[Q]
 have R:(#(b \ e):ℝ)<=2*(g.c d)⁻¹*m/log ((m:ℝ)/4):=by
  have b8:#e=#M-#B:=by rw[←m6T e m6z,K,card_sdiff_of_subset F]
  have a0:(#B:ℝ)<=(g.c d)⁻¹*#b/log #b:=
   (by exact_mod_cast (o ▸ a5):(#B:ℝ)<=m6N #b).trans ((Nat.floor_le (m6R (m65) (m6d _))).trans
    ((m6w D.le L (by nlinarith only[Q])).trans (by rw[mul_div_assoc];exact m6am (m6R D.le L.le) N)))
  rw[card_sdiff_of_subset m6h,b8,Nat.cast_sub ((Nat.sub_le _ _).trans (o ▸ m6K q)),Nat.cast_sub (m6K F)];rw[o] at a4
  calc (#b:ℝ)-(#M-#B)<=2*(g.c d)⁻¹*#b/log #b:=by linarith only[a4,a0,show 2*(g.c d)⁻¹*#b/log #b=(g.c d)⁻¹*#b/log #b+(g.c d)⁻¹*#b/log #b by ring]
   _<=2*(g.c d)⁻¹*m/log ((m:ℝ)/4):=div_le_div₀ (m66 (m66 two_pos.le (inv_nonneg.mpr s.le)) l.le) (m62 (m6j (m6K w)) (m66 two_pos.le (inv_nonneg.mpr s.le))) A E
 have V:(1:ℝ)/4<=∑ x∈e,c x:=by
  have hm:∑ x∈b \ e,c x<=1/12:=
   (((sum_le_sum fun x G=>(t x (mem_sdiff.mp G).1).2).trans_eq (by rw[sum_const,nsmul_eq_mul])).trans
    ((m63 R (m6R two_pos.le (m66 n.le l.le))).trans_eq
     (by rw[div_mul_div_comm,show 2*(g.c d)⁻¹*m*2=4*(g.c d)⁻¹*m by ring,show log ((m:ℝ)/4)*(i*m)=i*log ((m:ℝ)/4)*m by ring,mul_div_mul_right _ _ l.ne']))).trans
    ((m6I (mul_pos n A)).mpr (by linarith only[b1]))
  linarith only[b4,hm,sum_sdiff (filter_subset (fun x=>x-a∈p) b) (f:=c)]
 let bz:RV d:=(i*m/4)•∑ x∈e,c x•zR (x-a);let v:=zR (y-S)-bz;have b9:∀ k:Fin d,|v k|<=m6J J g d*i*H*m*r.width k:=fun k=>by
  have W:(0:ℝ)<=r.width k:=m65;have c0:|(i*m/4)*∑ x∈b \ e,c x*((x k-a k:ℤ):ℝ)|<=((g.c d)⁻¹*m/log ((m:ℝ)/4))*r.width k:=by
   rw[abs_mul,abs_of_nonneg (m6R (m66 n.le l.le) (by norm_num))];have c1:|∑ x∈b \ e,c x*((x k-a k:ℤ):ℝ)|<=#(b \ e)*(2/(i*m)*r.width k):=
    (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun x G=>by
     have X:=(mem_sdiff.mp G).1;have d7:=m67.mp (C.hAB (w X)) k;have d8:=m67.mp b3 k;have hw:((r.width k:ℕ):ℤ)=r.hi k-r.lo k+1:=Int.toNat_of_nonneg (by have:=r.hle k;omega);have c2:|((x k-a k:ℤ):ℝ)|<=r.width k:=by exact_mod_cast (abs_le.mpr ⟨by omega,by omega⟩:|x k-a k|<=r.width k)
     rw[abs_mul,abs_of_nonneg (t x X).1];exact mul_le_mul (t x X).2 c2 (abs_nonneg _) (m6R two_pos.le (m66 n.le l.le)):_<=∑ _x∈b \ e,(2/(i*m)*r.width k)).trans_eq (by rw[sum_const,nsmul_eq_mul]))
   exact(m62 c1 (m6R (m66 n.le l.le) (by norm_num))).trans (by
    rw[show (i*m/4)*(#(b \ e)*(2/(i*m)*r.width k))=((i*m)/(i*m))*(#(b \ e)/2*r.width k) by ring,div_self (mul_ne_zero n.ne' l.ne'),one_mul];exact(m63 (m6b0 R two_pos.le) W).trans_eq (by ring))
  have c3:|(S k:ℝ)|<=((g.c d)⁻¹*m/log ((m:ℝ)/4))*r.width k:=(o ▸ d5 k).trans (m63
   ((Nat.floor_le (m6R (m65) (m6d _))).trans
    ((div_le_div₀ (m65) (m6j (m6K w)) (sq_pos_of_pos A) (m6Q A.le E 2)).trans
     ((m6w l.le A (by nlinarith only[O])).trans (by rw[mul_div_assoc];exact m6am (m6R l.le A.le) N)))) W)
  have c4:v k=((y k:ℝ)-(i*m/4)*∑ x∈b,c x*((x k-a k:ℤ):ℝ))+((i*m/4)*∑ x∈b \ e,c x*((x k-a k:ℤ):ℝ))-S k:=by
   have:v k=(y k:ℝ)-S k-(i*m/4)*∑ x∈e,c x*((x k-a k:ℤ):ℝ):=by dsimp only [v,bz];simp only[_root_.Pi.sub_apply,_root_.Pi.smul_apply,Finset.sum_apply,smul_eq_mul,zR,Int.cast_sub]
   rw[this];linear_combination -(i*m/4)*sum_sdiff (filter_subset (fun x=>x-a∈p) b) (f:=fun x=>c x*((x k-a k:ℤ):ℝ))
  have c5:2*((g.c d)⁻¹*m/log ((m:ℝ)/4))<=(m6J J g d*i*H/2)*m:=by
   have:=m63 b2 (m6R l.le (by norm_num:(0:ℝ)<=4));have h0:0<=m6J J g d*i*H*m:=m66 (m66 (m66 (m6ak C.hJ g C.hd).le n.le) C.hg0.le) l.le;linarith only[this,h0,show 8*(g.c d)⁻¹/log ((m:ℝ)/4)*(m/4)=2*((g.c d)⁻¹*m/log ((m:ℝ)/4)) by ring,show m6J J g d*i*H*(m/4)=(m6J J g d*i*H*m)/4 by ring,show (m6J J g d*i*H/2)*m=(m6J J g d*i*H*m)/2 by ring]
  rw[c4];exact((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (by linarith only[d6 k,c0,c3,m63 c5 W])
 have a1:e⊆z:=m6h.trans w;obtain ⟨ti,a8,a9⟩:=m6c3 C n b3 a1 (fun x G=>t x (m6P G).1) V d1 v b9;let pi:ZV d->ℝ:=fun u=>(i*m/4)*c (u+a)+ti (u+a);have a2:∀ u∈p,0<=pi u/\pi u<=1:=fun u hu=>by
  obtain ⟨x,G,rfl⟩:=m6E (K.symm ▸ hu);have ht:=abs_le.mp (a8 x G);have hD:(i*m/4)*c x<=1/2:=(m62 (t x (m6P G).1).2 (m6R (m66 n.le l.le) (by norm_num))).trans_eq
   (by rw[div_mul_div_comm,show i*m*2=2*(i*m) by ring,mul_div_mul_right _ _ (mul_ne_zero n.ne' l.ne')];norm_num)
  dsimp[pi];rw[sub_add_cancel];exact ⟨by linarith only[ht.1],by linarith only[ht.2,hD]⟩
 have c6:zR (y-S)=∑ u∈p,pi u•zR u:=by
  rw[show zR (y-S)=bz+v by dsimp[v];abel,a9];conv_rhs=>rw[←K,sum_image fun _ _ _ _ h=>m6z h]
  dsimp only [bz];rw[smul_sum,←m6e];exact m64 fun _ _=>by simp only[pi,sub_add_cancel,add_smul,smul_smul]
 have a3:sqrt (↑d*#p)<=g.c d*m6N #Si/2:=by
  have c7:(#p:ℝ)<=m:=by exact_mod_cast (show #p<=m by rw[←K,m6T _ m6z];exact m6K (m6h.trans w))
  have c8:Z*m/(log m)^2-1<=m6N #Si:=by
   rw[o];have c9:Z*m/(log m)^2<=#b/(log #b)^2:=div_le_div₀ (m65) P (sq_pos_of_pos L) (m6Q L.le (log_le_log D (m6j (m6K w))) 2);dsimp[m6N];linarith only[c9,Nat.lt_floor_add_one ((#b:ℝ)/(log #b)^2)]
  exact(sqrt_le_sqrt (m62 c7 (Nat.cast_nonneg d))).trans (d2.trans (m6b0 (m62 c8 s.le) two_pos.le))
 obtain ⟨T,hT,rfl⟩:=m6E (m6c4 sdiff_disjoint b5 a6 b6 (sdiff_subset.trans d0) d3 a7 s Y a3 (o ▸ (C.hs b w P).2.2.1) b7 a2 c6);exact mem_image.mpr ⟨T,mem_powerset.mpr ((m6U hT).trans (union_subset (sdiff_subset.trans q) (F.trans q))),rfl⟩
lemma m6c7 {d:ℕ} {l de K:ℝ} {B0:ZB d} {i:m61 d} {o:m69 hC} (C:m6o J o de K B0 i) (p:0< l) (H:l<=1/2) (b5:de<=1/4) (b6:64*↑(J d)*de<=l) (c8:NonAvg i) (q:16<=#i) (b7:72<=↑(#i)*l) (b8:sqrt (↑d*#i)<=o.c d*(de*#i/(log #i)^2-1)/2) (w:48*(o.c d)⁻¹<=l*log (#i/4)) (z:8*(o.c d)⁻¹/log (#i/4)<=m6J J o d*l*K) (d7:4*(↑d.factorial*(3/o.c d)^d/K)^2<=m6J J o d*l*K*#i):DCP l i:=by
 by_contra R;set m:=#i;obtain ⟨a,B,c,D,c4,c5⟩:=m6c0 p H (by linarith) R;have r:=C.hAB B;obtain ⟨S,T,U,b,V,W,c6,c7⟩:=m6c6 B p q b7 D c4;have s:S⊆i:=(b ▸ subset_union_left).trans (erase_subset _ _);have t:T⊆i:=(b ▸ subset_union_right).trans (erase_subset _ _);obtain ⟨d3,d4,P1,q1,X,Y,Z,a0,a1,E,a2,d0,a3⟩:=m6bl C r s (by nlinarith);obtain ⟨d5,d6,P2,q2,a4,a5,a6,a7,a8,F,a9,d1,b0⟩:=m6bl C r t (by nlinarith);let xi:=m6J J o d*l*K;have c9:0< xi:=mul_pos (mul_pos (m6ak C.hJ o C.hd) p) C.hg0;let n:RV d:=fun k=>(l*m/4)*∑ x∈S,c x*((x k-a k:ℤ):ℝ);have L:∀ k,-n k=(l*m/4)*∑ x∈T,c x*((x k-a k:ℤ):ℝ):=fun k=>by
  have A:=congrFun c5 k;rw[←b,sum_union U] at A;simp only[Pi.add_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,zR,Pi.sub_apply,Int.cast_sub,Pi.zero_apply] at A;dsimp[n];linear_combination -(l*m/4)*(by simpa only[Int.cast_sub] using A:(∑ x∈S,c x*((x k-a k:ℤ):ℝ))+(∑ x∈T,c x*((x k-a k:ℤ):ℝ))=0)
 let M:=E*F;have j:(0:ℝ)< M:=m6D (Nat.mul_pos a2 a9);have d2:2*(M:ℝ)<=(xi/2)*m:=by
  have:(M:ℝ)<=(↑d.factorial*(3/o.c d)^d/K)^2:=by have:=(o.ok d C.hd).1;have:=C.hg0;rw[sq,show (M:ℝ)=E*F from Nat.cast_mul E F];gcongr
  linarith
 let kz:Fin d:=⟨0,by have:=C.hd;omega⟩;let u:ZV d:=fun k=>if k=kz/\⌊n k/M⌋=0 then 1 else ⌊n k/M⌋;let e:ZV d:=(M:ℤ)•u;have v:e≠0:=fun h0=>by
  have hk:=congrFun h0 kz;simp only[e,u,Pi.smul_apply,smul_eq_mul,Pi.zero_apply,true_and] at hk;have N:(M:ℤ)≠0:=by exact_mod_cast Nat.mul_ne_zero (by omega) (by omega)
  split_ifs at hk with h
  . exact N (by simpa using hk)
  . exact h ((mul_eq_zero.mp hk).resolve_left N)
 have O:∀ k,|(e k:ℝ)-n k|<=(xi/2)*m*B0.width k:=fun k=>by
  have h1:=Int.floor_le (n k/M);have h2:=Int.lt_floor_add_one (n k/M);have b9:|(e k:ℝ)-n k|<=M:=by
   rw[show (e k:ℝ)=(M:ℝ)*(u k:ℝ) by simp[e]];dsimp[u];split_ifs with h
   . rw[h.2,Int.cast_zero] at h1 h2;rw[Int.cast_one,mul_one,abs_le];exact ⟨by linarith only[(div_lt_iff₀ j).mp (by linarith only[h2]:n k/M<1),j],by linarith only[(m6F j).mp h1,j]⟩
   . rw[abs_le];exact ⟨by linarith[(div_lt_iff₀ j).mp h2],by linarith[(m6F j).mp h1]⟩
  exact(b9.trans (by linarith:(M:ℝ)<=(xi/2)*m)).trans (m6b1 (by positivity) (m6a (B0.wP k)))
 have c0:=m6bm C p H b5 b6 q b8 w z r (y:=e) s V (fun x G=>D x (b ▸ mem_union_left T G)) c6 X Z a0 Y a1
  (by rw[show e=(E:ℤ)•((F:ℤ)•u) by dsimp[e];rw[smul_smul];exact congrArg (·•u) (Nat.cast_mul E F)];exact a3 _) O
 have c1:=m6bm C p H b5 b6 q b8 w z r (y:=-e) t W (fun x G=>D x (b ▸ mem_union_right S G)) c7 a4 a6 a7 a5 a8
  (AddSubgroup.neg_mem _ (by rw[show e=(F:ℤ)•((E:ℤ)•u) by dsimp[e];rw[smul_smul];exact congrArg (·•u) ((Nat.cast_mul E F).trans (mul_comm _ _))];exact b0 _))
  fun k=>by rw[←L k];simp only[Pi.neg_apply,Int.cast_neg];rw[show -(e k:ℝ) - -n k= -((e k:ℝ)-n k) by ring,abs_neg];exact O k
 obtain ⟨U1,b1,f⟩:=m6E c0;obtain ⟨U2,b2,g⟩:=m6E c1;obtain ⟨T1,b3,rfl⟩:=subset_image_iff.mp (m6U b1);obtain ⟨T2,b4,rfl⟩:=subset_image_iff.mp (m6U b2);rw[sum_image fun _ _ _ _ h=>m6z h] at f g;have c2:T1.Nonempty:=by by_contra h;rw[not_nonempty_iff_eq_empty.mp h,sum_empty] at f;exact v f.symm
 have c3:T2.Nonempty:=by by_contra h;rw[not_nonempty_iff_eq_empty.mp h,sum_empty] at g;exact v (neg_eq_zero.mp g.symm)
 have P:=U.mono b3 b4;apply c8 a B (T1 ∪ T2) (union_subset (fun x G=>b ▸ mem_union_left T (b3 G)) (fun x G=>b ▸ mem_union_right S (b4 G))) (by rw[card_union_of_disjoint P];have:=card_pos.mpr c2;have:=card_pos.mpr c3;omega);have Q:(∑ x∈T1 ∪ T2,(x-a))=0:=by rw[sum_union P,f,g,add_neg_cancel]
 rw[sum_sub_distrib,sum_const,show (#(T1 ∪ T2):ℕ)•a=(#(T1 ∪ T2):ℤ)•a by simp] at Q;exact sub_eq_zero.mp Q
def m60 (d:ℕ):ℝ:=if d<=1 then 1/4 else (↑d-1)/(↑d+1)
lemma m6p {d:ℕ} (h:2<=d):m60 d=(↑d-1)/(↑d+1):=by simp[m60,show ¬ d<=1 by omega]
lemma m6g (d:ℕ):(1:ℝ)/4<=m60 d:=by
 by_cases h:d<=1
 . simp[m60,h]
 rw[m6p (by omega),m6F] <;> linarith[show (2:ℝ)<=d by exact_mod_cast (by omega:2<=d)]
lemma m6bn (d:ℕ):m60 d<1:=by
 by_cases h:d<=1
 . simp[m60,h];norm_num
 rw[m6p (by omega),div_lt_one] <;> linarith[show (2:ℝ)<=d by exact_mod_cast (by omega:2<=d)]
lemma m6bo {a b D:ℕ} (g:1<=a) (e:a< b) (f:b<=D):min ((1:ℝ)/12) (2/(↑D*(↑D+1)))<=m60 b-m60 a:=by
 have:(2:ℝ)<=b:=by exact_mod_cast (by omega:2<=b)
 by_cases d:a=1
 . subst d;rw[show m60 1=1/4 by simp[m60],m6p (by omega)]
   exact(m6a0 _ _).trans (by rw[le_sub_iff_add_le,m6F (by linarith)];linarith)
 . rw[m6p (by omega),m6p (by omega)]
   have:(2:ℝ)<=a:=by exact_mod_cast (by omega:2<=a)
   have:(a:ℝ)+1<=b:=by exact_mod_cast (by omega:a+1<=b)
   have:(b:ℝ)<=D:=m6j f;rw[show ((b:ℝ)-1)/(b+1)-(a-1)/(a+1)=2*(b-a)/((b+1)*(a+1)) by field_simp;ring];exact(min_le_right _ _).trans ((m6w (by norm_num) (by nlinarith) (by nlinarith)).trans (m6b0 (by linarith) (by nlinarith)))
lemma m6c8 {d g:ℕ} {z e:ℝ} (hd:1<=d) (s:d< g) (t:0< z) (u:m60 d+z<1) (A:e<=z/20):(m60 g+z)*(1/(m60 d+z)-(1-e)*((g-d:ℕ):ℝ))<=1-z/10:=by
 set a:=m60 d;set b:=m60 g;set k:=g-d;have v:=m6g d;have w:=m6g g;have o:=m6bn g;have h:0< a+z:=by linarith
 have l:z^3<=z^2:=by nlinarith[m6d z]
 rw[show (b+z)*(1/(a+z)-(1-e)*k)=(b+z)*(1-(1-e)*k*(a+z))/(a+z) by field_simp[h.ne'],m6I h];refine(m62 (by nlinarith[m66 (m6al k) h.le]:1-(1-e)*k*(a+z)<=1-(1-z/20)*k*(a+z)) (by linarith)).trans ?_
 have f:∀ m:ℝ,1<=(1-z/20)*m*(a+z)->(b+z)*(1-(1-z/20)*m*(a+z))<=(1-z/10)*(a+z):=fun m y=>
  (mul_nonpos_of_nonneg_of_nonpos (by linarith) (by linarith)).trans (m66 (by linarith) h.le)
 by_cases i:4<=k
 . have:(4:ℝ)<=k:=by exact_mod_cast i
   have:1+4*z<=(k:ℝ)*(a+z):=by nlinarith
   exact f k (by rw[m68];nlinarith[m6d z])
 by_cases r:d<=3
 . have n:g=d+k:=by omega
   have p:1<=k:=by omega
   have x:k<=3:=by omega
   dsimp[a,b];rw[n];interval_cases d <;> interval_cases k <;> (simp only[m60];norm_num;ring_nf;linarith[m6d z,l])
 . have q:(3:ℝ)/5<=a:=by dsimp[a];rw[m6p (by omega),m6F (by positivity)];linarith[show (4:ℝ)<=d by exact_mod_cast (by omega:4<=d)]
   by_cases j:2<=k
   . have:(2:ℝ)<=k:=by exact_mod_cast j
     have:6/5<=(k:ℝ)*(a+z):=by nlinarith
     exact f k (by rw[m68];nlinarith)
   . rw[show k=1 by omega];push_cast
     have n:(b+z)*(1-(1-z/20)*1*(a+z))<=(1+z)*(1-(1-z/20)*(a+z)):=by rw[mul_one];exact m63 (by linarith) (by nlinarith)
     have p:(2+17/20*z-z^2/20)*(3/5+z)<=(2+17/20*z-z^2/20)*(a+z):=m62 (by linarith) (by nlinarith[m6d z]);nlinarith[m6d z,l]
lemma m6bp {d K:ℕ} {z e E R B b o l:ℝ} (Q:0< z) (S:m60 d+z<1) (T:0< e) (U:e<=z/100) (V:100<=K) (j:0< E) (C:E<=1) (h:0< R) (m:R<=1) (G:1<=b) (H:1<=B) (J:1<=o) (n:B^(m60 d+z)< b) (L:o<=E^(1-e)*R^(K:ℝ)*B) (D:E^(m60 d+e)*R*b<=l) (hAB:l<=o):o^(m60 d+z)< l/\b^(z/2)<=l:=by
 set a:=m60 d;have W:=m6g d;have g:0< a+z:=by linarith
 have M:(100:ℝ)<=K:=by exact_mod_cast V
 refine ⟨((m6ad (by linarith) L g.le).trans_eq (by rw[m6r (by positivity) (by linarith),m6r (by positivity) (by positivity),←m6C j.le,←m6C h.le])).trans_lt ((mul_lt_mul_of_pos_left n (by positivity)).trans_le ((m63 (mul_le_mul (m6az j C (by nlinarith)) ((m6az h m (by nlinarith)).trans_eq (rpow_one R)) (by positivity) (by positivity)) (by linarith)).trans D)),?_⟩
 have p:=((D.trans hAB).trans L).trans_lt (mul_lt_mul_of_pos_left (m6ap (by linarith) g n) (by positivity));have f:0<1-a-2*e:=by linarith
 set i:=-((1-a-z)/(a+z));have q:b^i<=E^(1-a-2*e)*R^((K:ℝ)-1):=le_of_mul_le_mul_right (by
  have N:b^i*(E^(a+e)*R*b^(1/(a+z)))=E^(a+e)*R*b:=by rw[mul_left_comm,←m6L (by linarith),show i+1/(a+z)=1 by dsimp[i];field_simp;ring,rpow_one]
  have O:E^(1-a-2*e)*R^((K:ℝ)-1)*(E^(a+e)*R*b^(1/(a+z)))=E^(1-e)*R^(K:ℝ)*b^(1/(a+z)):=by rw[show ∀ u v w x y:ℝ,u*v*(w*x*y)=(u*w)*(v*x)*y by intros;ring,←m6L j,←rpow_add_one h.ne',show 1-a-2*e+(a+e)=1-e by ring,sub_add_cancel]
  rw[N,O];exact p.le) (by positivity)
 let k:=(a+e)/(1-a-2*e);have r:0< k:=div_pos (by linarith) f;have F:(1:ℝ)/4<=k:=(m6F f).mpr (by linarith);have s:b^(i*k)<=E^(a+e)*R:=
  ((m6C (by linarith) _ _).trans_le ((m6ad (by positivity) q r.le).trans_eq (by rw[m6r (by positivity) (by positivity),←m6C j.le,←m6C h.le,mul_div_cancel₀ _ f.ne']))).trans
   (m62 ((m6az h m (by nlinarith)).trans_eq (rpow_one R)) (by positivity))
 have P:z/2<=i*k+1:=by
  have t:i*k+1=(z-e*(1+a+z))/((1-a-2*e)*(a+z)):=by
   rw[eq_div_iff (mul_pos f g).ne'];dsimp[i,k];have A:(1-a-z)/(a+z)*((a+e)/(1-a-2*e))*((1-a-2*e)*(a+z))=(1-a-z)*(a+e):=by
    rw[show (1-a-z)/(a+z)*((a+e)/(1-a-2*e))*((1-a-2*e)*(a+z))=((1-a-z)/(a+z)*(a+z))*((a+e)/(1-a-2*e)*(1-a-2*e)) by ring,div_mul_cancel₀ _ g.ne',div_mul_cancel₀ _ f.ne']
   linear_combination -A
  rw[t,m6F (mul_pos f g)];nlinarith[show (1-a-2*e)*(a+z)<=1 by nlinarith]
 calc b^(z/2)<=b^(i*k+1):=by gcongr
  _=b^(i*k)*b:=rpow_add_one (by linarith) _
  _<=l:=by grw [s,D]
lemma m6c9 {d:ℕ} {n v:ℝ} {b:ZB d} {g:m61 d} {w:m69 hC} (C:m6o J w n v b g) (o:g.Nonempty):∀ i:Fin d,1/n< b.width i:=fun i=>by
 by_contra hle;push Not at hle;let h:=Icc (b.lo i) (b.hi i);have j:#h=b.width i:=by dsimp[h,ZB.width];rw[Int.card_Icc];have:=b.hle i;omega
 obtain ⟨a,q⟩:=o;obtain ⟨t,_,l⟩:=m6bg (S:=g) (V:=h) (fun x=>x i) (fun x m=>mem_Icc.mpr (m67.mp (C.hAB m) i)) ⟨a i,mem_Icc.mpr (m67.mp (C.hAB q) i)⟩;let F:=g.filter fun x=>x i=t;have e:n*#g<=#F:=by have:=m62 ((j ▸ l).trans (m63 hle (m65))) C.hd0.le;rwa[←m68,mul_one_div_cancel C.hd0.ne',one_mul] at this
 obtain ⟨u,f⟩:F.Nonempty:=card_pos.mp (Nat.cast_pos.mp ((mul_pos C.hd0 (m6D (card_pos.mpr ⟨a,q⟩))).trans_le e));let p:RV d →ₗ[ℝ] ℝ:=LinearMap.proj i;have k:Module.finrank ℝ (LinearMap.ker p)<=d-1:=by have s:=LinearMap.finrank_range_add_finrank_ker p;rw[Module.finrank_fin_fun,LinearMap.range_eq_top.mpr fun r=>⟨fun _=>r,rfl⟩,finrank_top,Module.finrank_self] at s;omega
 exact m6ay C (C.hAB (m6P f).1) m6h e k fun x m=>by change ((x i-u i:ℤ):ℝ)=0;rw[(m6P m).2,(m6P f).2,sub_self,Int.cast_zero]
lemma m6ca {d:ℕ} {a:Set (RV d)} (l:Convex ℝ a) (m:∀ v:RV d,(∀ j,|v j|<=1)->v∈a) {M:ℝ} (t:0<=M) (u:volume a<=m6W M) {T:m61 d} (w:∀ v∈T,zR v∈(2:ℝ)•a):(#T:ℝ)<=3^d*M:=by
 let U:ZV d->Set (RV d):=fun v=>Set.univ.pi fun j=>Set.Ioo ((v j:ℝ)-1/2) ((v j:ℝ)+1/2);have b:(T:Set (ZV d)).PairwiseDisjoint U:=fun n _ o _ k=>Set.disjoint_left.mpr fun x r s=>k (by
  ext j;obtain ⟨_,_⟩:=r j (Set.mem_univ j);obtain ⟨_,_⟩:=s j (Set.mem_univ j);have:|n j-o j| <1:=by exact_mod_cast (abs_lt.mpr ⟨by linarith,by linarith⟩:|(n j:ℝ)-o j| <1)
  rw[abs_lt] at this;omega)
 have e:(⋃ v∈T,U v)⊆(3:ℝ)•a:=fun x p=>by
  simp only[Set.mem_iUnion] at p;obtain ⟨v,f,g⟩:=p;obtain ⟨y,h,i⟩:=w v f;have q:x-zR v∈a:=m _ fun j=>by obtain ⟨_,_⟩:=g j (Set.mem_univ j);change |x j-↑(v j)|<=1;rw[abs_le];constructor <;> linarith
  exact ⟨(2/3:ℝ)•y+(1/3:ℝ)•(x-zR v),l h q (by norm_num) (by norm_num) (by norm_num),by ext j;have:=congrFun i j;simp only[Pi.smul_apply,Pi.add_apply,Pi.sub_apply,smul_eq_mul,zR] at this ⊢;linarith⟩
 refine(ENNReal.ofReal_le_ofReal_iff (by positivity)).mp ?_
 calc m6W ↑(#T)=(#T:ENNReal):=ENNReal.ofReal_natCast #T
  _=∑ _v∈T,(1:ENNReal):=by simp
  _=∑ v∈T,volume (U v):=m64 fun v _=>by dsimp[U];rw[volume_pi,Measure.pi_pi];simp only[Real.volume_Ioo,show ∀ j,(v j:ℝ)+1/2-((v j:ℝ)-1/2)=1 by intro j;ring,ENNReal.ofReal_one,prod_const_one]
  _=volume (⋃ v∈T,U v):=(measure_biUnion_finset b fun _ _=>MeasurableSet.univ_pi fun _=>measurableSet_Ioo).symm
  _<=m6W ((3:ℝ)^d)*volume a:=(measure_mono e).trans_eq (by rw[Measure.addHaar_smul,Module.finrank_fin_fun,abs_of_nonneg (by positivity)])
  _<=m6W (3^d*M):=(m62 u zero_le).trans_eq (ENNReal.ofReal_mul (by positivity)).symm
def m6bq (d:ℕ) (e ta cr mu:ℝ):Prop:=
 ∀ A:Finset (RV d),(∀ x∈A,∀ i,-1<=x i/\x i<=1)->M6R mu A->2/mu<=#A->
  ∃ et x0 K0,mu<=et/\et<=mu^ta/\(0:RV d)∈K0/\Convex ℝ K0/\(∀ x∈K0,-x∈K0)/\Bornology.IsBounded K0/\
   (∀ x:RV d,(∀ i,|x i|<=cr*mu^((1:ℝ)/d))->x∈K0)/\volume K0<=m6W (et*2^d)/\
   (#(A.filter fun x=>x-x0∈K0):ℝ) >= et^((↑d-1)/(↑d+1)+e)*#A
lemma m6cb (hJ:m6q J) {d:ℕ} (hd:2<=d) {e ta cr m:ℝ} (d5:m60 d+e<1) (d6:0< ta) (e4:0< cr) (a1:0< m) (d7:m<=1) (d8:m6bq d e ta cr m) {l:ZB d} {p:m61 d} (hAB:p⊆l.tF) (d9:NonAvg p) (e0:DCP m p) (c2:(2:ℝ)/m<=#p) (e1:∀ i:Fin d,2/(cr*m^((1:ℝ)/d))+1<=l.width i):∃(j:ℝ) (k:ℕ) (C:ZB k) (o:m61 k),m<=j/\j<=m^ta/\1<=k/\k<=d/\(0:ZV k)∈C.tF/\o⊆C.tF/\NonAvg o/\j^(m60 d+e)*#p<=#o/\(C.vol:ℝ)<=(9*↑(J d))^d*j*l.vol:=by
 let md:RV d:=fun i=>((l.lo i+l.hi i:ℤ):ℝ)/2;let g:RV d:=fun i=>((l.hi i-l.lo i:ℤ):ℝ)/2;have D:0< cr*m^((1:ℝ)/d):=by positivity
 have a2:∀ i,1/(cr*m^((1:ℝ)/d))<=g i:=fun i=>by have:=e1 i;have:=m6aq l i;dsimp[g];linarith[show 2/(cr*m^((1:ℝ)/d))=2*(1/(cr*m^((1:ℝ)/d))) by ring]
 have b:∀ i,0< g i:=fun i=>m6c (one_div_pos.mpr D) (a2 i);let n:ZV d->RV d:=fun x i=>((x i:ℝ)-md i)/g i;have S:Function.Injective n:=fun x1 x2 h=>by ext i;exact Int.cast_injective (α:=ℝ) (by linarith[(div_left_inj' (b i).ne').mp (congrFun h i)])
 let E:=p.image n;have q:#E=#p:=m6T p S;have a3:∀ y∈E,∀ i,-1<=y i/\y i<=1:=fun y hy i=>by
  obtain ⟨x,A,rfl⟩:=m6E hy;have a4:=m67.mp (hAB A) i;have:(l.lo i:ℝ)<=x i:=by exact_mod_cast a4.1
  have:(x i:ℝ)<=l.hi i:=by exact_mod_cast a4.2
  dsimp[n,md,g];rw[m6F (b i),m6I (b i)];dsimp[g];push_cast;constructor <;> linarith
 have T:M6R m E:=fun y hy=>by
  obtain ⟨a,ha,rfl⟩:=m6E hy;obtain ⟨u,d0,d1⟩:=e0 a ha;refine ⟨fun i=>u i*g i,fun h0=>d0 (by ext i;exact(mul_eq_zero.mp (congrFun h0 i)).resolve_right (b i).ne'),?_⟩;have c3:E.filter (fun z=>(0:ℝ)<=∑ i,(u i*g i)*(z i-n a i))=(p.filter fun x=>(0:ℝ)<=∑ i,u i*((x i-a i:ℤ):ℝ)).image n:=by
   ext z;simp only[mem_filter,mem_image,E];have a5:∀ x,∑ i,(u i*g i)*(n x i-n a i)=∑ i,u i*((x i-a i:ℤ):ℝ):=fun x=>m64 fun i _=>by dsimp[n];push_cast;field_simp[(b i).ne'];ring
   exact ⟨fun ⟨⟨x,A,hzx⟩,h⟩=>⟨x,⟨A,by subst hzx;rwa[a5 x] at h⟩,hzx⟩,fun ⟨x,⟨A,h⟩,hzx⟩=>⟨⟨x,A,hzx⟩,by subst hzx;rwa[a5 x]⟩⟩
  rw[c3,m6T _ S,q];exact d1
 obtain ⟨j,x0,K0,B,R,b2,b3,b4,b5,Y,b6,b7⟩:=d8 E a3 T (q ▸ c2);have F:=m6c a1 B;have a6:=R.trans (rpow_le_one a1.le d7 d6.le);let L:RV d →ₗ[ℝ] RV d:=Matrix.toLin' (Matrix.diagonal g);have U:∀ v i,L v i=g i*v i:=fun v i=>by simp[L,Matrix.mulVec_diagonal]
 let G:=L '' K0;let x1:=md+L x0;have r:=b3.linear_image L;have H:∀ v∈G,-v∈G:=by rintro _ ⟨y,hy,rfl⟩;exact ⟨-y,b4 y hy,L.map_neg y⟩
 have V:∀ v:RV d,(∀ i,|v i|<=1)->v∈G:=fun v hv=>⟨fun i=>v i/g i,Y _ fun i=>by rw[abs_div,abs_of_pos (b i),m6I (b i)];linarith[hv i,(m6I D).mp (a2 i)],by ext i;rw[U];exact mul_div_cancel₀ _ (b i).ne'⟩;have a7:volume G<=m6W (j*l.vol):=by
  have a8:0<=∏ i,g i:=prod_nonneg fun i _=>(b i).le;have c4:(∏ i,g i)*(j*2^d)<=j*l.vol:=by
   rw[show (∏ i,g i)*(j*2^d)=j*∏ i,(2*g i) by rw[←m6s];ring];gcongr;rw[ZB.vol,Nat.cast_prod];exact prod_le_prod (fun i _=>by linarith[b i]) fun i _=>by have:=m6aq l i;dsimp[g];linarith
  exact(by rw[Measure.addHaar_image_linearMap,LinearMap.det_toLin',Matrix.det_diagonal,abs_of_nonneg a8]:volume G=_).trans_le ((m62 b6 zero_le).trans (by rw[←ENNReal.ofReal_mul a8];exact m6bs c4))
 let s:=p.filter fun x=>zR x-x1∈G;have a9:s.image n=E.filter fun y=>y-x0∈K0:=by
  ext y;simp only[mem_image,mem_filter,s,E];have hL:∀ x,L (n x-x0)=zR x-x1:=fun x=>by ext i;simp only[U,Pi.sub_apply,Pi.add_apply,n,zR,x1];rw[mul_sub,mul_div_cancel₀ _ (b i).ne'];ring
  have c5:Function.Injective L:=fun u v h=>by ext i;exact mul_left_cancel₀ (b i).ne' (by simpa only[U] using congrFun h i)
  exact ⟨fun ⟨x,⟨A,⟨w,hw,hwe⟩⟩,hxy⟩=>⟨⟨x,A,hxy⟩,hxy ▸ (c5 (hwe.trans (hL x).symm) ▸ hw)⟩,fun ⟨⟨x,A,hxy⟩,h⟩=>⟨x,⟨A,⟨n x-x0,hxy ▸ h,hL x⟩⟩,hxy⟩⟩
 have K:j^(m60 d+e)*#p<=#s:=by rw[←m6T s S,a9,m6p hd,←q];exact b7
 have e2:(2:ℝ)<=#s:=by
  have h2:(2:ℝ)<=j*#p:=by have:=(m6I F).mp ((m6w (by norm_num) a1 B).trans c2);linarith
  exact(h2.trans (m63 ((rpow_one j).symm.trans_le (m6az F a6 d5.le)) (m65))).trans K
 obtain ⟨a0,d2⟩:s.Nonempty:=card_pos.mp (by exact_mod_cast (show (0:ℝ)<#s by linarith));let W:=s.image (· - a0);have M:#W=#s:=m6T s m6z;have b0:∀ v∈W,zR v∈(2:ℝ)•G:=fun v hv=>by
  obtain ⟨x,A,rfl⟩:=m6E hv;exact ⟨(1/2:ℝ)•(zR x-x1)+(1/2:ℝ)•(-(zR a0-x1)),r (m6P A).2 (H _ (m6P d2).2) (by norm_num) (by norm_num) (by norm_num),by ext i;simp[zR];ring⟩
 obtain ⟨k,b8,w,N,_,b9,d3,c0,Z⟩:=hJ.2 d ⊤ ((2:ℝ)•G) ⟨0,⟨0,b2,L.map_zero⟩,by simp⟩ (r.smul 2) (by rintro _ ⟨y,hy,rfl⟩;exact ⟨-y,H y hy,by simp⟩) ((LinearMap.lsmul ℝ (RV d) (2:ℝ)).toContinuousLinearMap.lipschitz.isBounded_image (L.toContinuousLinearMap.lipschitz.isBounded_image b5));let O:ZV k->ZV d:=fun c=>∑ i,c i•w i;have t:=m6bc d3;let C:=ZB.symm fun i=>J d*N i;let o:=C.tF.filter fun c=>O c∈W;have P:o.image O=W:=by
  ext v;simp only[mem_image,mem_filter,o];exact ⟨fun ⟨_,⟨_,h⟩,he⟩=>he ▸ h,fun hv=>by obtain ⟨c,d4,c1⟩:=Z v trivial (b0 v hv);exact ⟨c,⟨m67.mpr fun i=>abs_le.mp (d4 i).le,by change ∑ i,c i•w i∈W;rwa[c1]⟩,c1⟩⟩
 have Q:#o=#W:=by rw[←m6T o t,P]
 have X:=m6b8 (f:=AddMonoidHom.mk' O fun u v=>by dsimp[O];rw[←m6e];exact m64 fun _ _=>add_zsmul _ _ _) t.injOn (by change NonAvg (o.image O);rw[P];simpa[W,s,sub_eq_add_neg] using (d9.subset m6h).translate (-a0));have c6:1<=k:=by
  by_contra h;rcases (show k=0 by omega) with rfl
  have h1:#o<=1:=(m6K m6h).trans_eq (by rw[C.cTF];simp[ZB.vol]);have:(#o:ℝ)<=1:=by exact_mod_cast h1
  rw[Q,M] at this;linarith
 have b1:(C.vol:ℝ)<=(9*↑(J d))^d*j*l.vol:=by
  let Tb:=Fintype.piFinset fun i:Fin k=>Icc (-(N i:ℤ)+1) ((N i:ℤ)-1);have c7:(#(Tb.image O):ℝ)<=3^d*(j*l.vol):=m6ca r V (by positivity) a7 fun v hv=>by
   obtain ⟨c,hc,rfl⟩:=m6E hv;exact c0 c fun i=>by have:=mem_Icc.mp (Fintype.mem_piFinset.mp hc i);rw[abs_lt];omega
  have c8:#(Tb.image O)=∏ i:Fin k,(2*N i-1):=by rw[m6T _ t,Fintype.card_piFinset];exact prod_congr rfl fun i _=>by rw[Int.card_Icc];have:=b9 i;omega
  have c9:(C.vol:ℝ)<=(3*↑(J d))^k*#(Tb.image O):=by exact_mod_cast (c8 ▸ m6b2 (hJ.1 d) N b9)
  have e3:(1:ℝ)<=J d:=m6a (hJ.1 d);grw [c9,m6l (by linarith:(1:ℝ)<=3*↑(J d)) b8,c7];exact le_of_eq (by rw[←m68,←m68,←mul_pow];congr 3;ring)
 exact ⟨j,k,C,o,B,R,c6,b8,ZB.zMS _,filter_subset _ _,X,by rw[Q,M];exact K,b1⟩
lemma m6cc {d a:ℕ} {b z e A B j m f:ℝ} (hd:1<=d) (n:d< a) (o:0< b) (D:b<=z) (q:m60 d+z<1) (F:e<=b/100) (G:1<=A) (H:1<=B) (x:1<=j) (J:1<=f) (r:B^(m60 d+z)< A) (s:A^(1-e/2)<=m) (t:j*A^((1-e)*((a-d:ℕ):ℝ))<=f*B) (K:f^(2:ℝ)<=A^(b/40)):j^(m60 a+(z+b/100))< m:=by
 have L:=m6g d;have y:=m6g a;have u:=m6bn a;have g:=m6c o D;have h:0< m60 d+z:=by linarith
 let p:=m60 a+(z+b/100);have v:0< p:=by dsimp[p];linarith
 let E:=1/(m60 d+z)-(1-e)*((a-d:ℕ):ℝ);have i:j< f*A^E:=lt_of_mul_lt_mul_right (by rw[m68,←m6L (by linarith),show E+(1-e)*((a-d:ℕ):ℝ)=1/(m60 d+z) by dsimp[E];ring];exact t.trans_lt (mul_lt_mul_of_pos_left (m6ap (by linarith) h r) (by linarith))) (by positivity);have k:p*E+b/40<=1-e/2:=by
  by_cases l:E<=0
  . nlinarith[mul_nonpos_of_nonneg_of_nonpos v.le l]
  have C:E<=4:=by dsimp[E];linarith[(m6I h).mpr (by linarith:1<=4*(m60 d+z)),m66 (by linarith:0<=1-e) (m6al (a-d))]
  have w:(m60 a+z)*E<=1-z/10:=m6c8 hd n g q (by linarith);nlinarith[show p*E=(m60 a+z)*E+(b/100)*E by dsimp[p];ring]
 calc j^p<(f*A^E)^p:=rpow_lt_rpow (by linarith) i v
  _=f^p*A^(E*p):=by rw[m6r (by linarith) (by positivity),←m6C (by linarith)]
  _<=f^(2:ℝ)*A^(E*p):=by gcongr;dsimp[p];linarith
  _<=A^(b/40)*A^(E*p):=by gcongr
  _=A^(p*E+b/40):=by rw[←m6L (by linarith)];congr 1;ring
  _<=m:=by grw [k,s]
lemma m6cd {d g:ℕ} {z a h e A B i k f:ℝ} (u:0< z) (v:m60 d+z<1) (w:a<=m60 d-m60 g) (o:0< a) (q:0< h) (x:h<=a/4) (y:e<=a/8) (C:1<=A) (D:1<=B) (r:1<=i) (E:1<=f) (l:B^(m60 d+z)< A) (m:A^(1-e/2)<=k) (n:i<=f*B) (F:f<=A^(a/2)):i^(m60 g+(z+h))< k:=by
 have G:=m6g d;have s:=m6g g;have b:0< m60 d+z:=by linarith
 let p:=m60 g+(z+h);have t:0< p:=by dsimp[p];linarith
 have j:p/(m60 d+z)+a/2<=1-e/2:=by
  have:p/(m60 d+z)<=1-(3/4)*a/(m60 d+z):=(m6I b).mpr (by rw[sub_mul,one_mul,div_mul_cancel₀ _ b.ne'];dsimp[p];linarith);linarith[(m6F b).mpr (by nlinarith:(3/4)*a*(m60 d+z)<=(3/4)*a)]
 calc i^p<(f*A^(1/(m60 d+z)))^p:=rpow_lt_rpow (by linarith) (n.trans_lt (mul_lt_mul_of_pos_left (m6ap (by linarith) b l) (by linarith))) t
  _=f^p*A^(p/(m60 d+z)):=by rw[m6r (by linarith) (by positivity),←m6C (by linarith)];congr 2;ring
  _<=f^(1:ℝ)*A^(p/(m60 d+z)):=by gcongr;dsimp[p];linarith
  _<=A^(a/2)*A^(p/(m60 d+z)):=by rw[rpow_one];gcongr
  _=A^(p/(m60 d+z)+a/2):=by rw[←m6L (by linarith)];congr 1;ring
  _<=k:=by grw [j,m]
def m6br (d K:ℕ) (z0 th e z:ℝ) (B:ZB d) (A:m61 d):Prop:=
 (∃(d':ℕ) (B':ZB d') (A':m61 d'),d< d'/\d'<=d+8/\(0:ZV d')∈B'.tF/\A'⊆B'.tF/\NonAvg A'/\(#A:ℝ)^(1-e/2)<=#A'/\(B'.vol:ℝ)^(m60 d'+(z+z0/100))<#A')\/
 (∃(d':ℕ) (B':ZB d') (A':m61 d'),1<=d'/\d'< d/\(0:ZV d')∈B'.tF/\A'⊆B'.tF/\NonAvg A'/\(#A:ℝ)^(1-e/2)<=#A'/\(B'.vol:ℝ)^(m60 d'+(z+th))<#A')\/
 (∃(et rh:ℝ) (k:ℕ) (B':ZB k) (A':m61 k),0< et/\et<1/\0< rh/\rh<=1/\1<=k/\k<=d/\(0:ZV k)∈B'.tF/\A'⊆B'.tF/\NonAvg A'/\(B'.vol:ℝ)<=et^(1-e)*rh^(K:ℝ)*B.vol/\et^(m60 d+e)*rh*#A<=#A'/\B'.vol< B.vol)
lemma m6ce (k:M6L) (d:ℕ) {a e:ℝ} (t u:ℝ) (i:0< a) (v:0< e):∃ Me:ℕ,∀ m:ℕ,Me<=m->(2:ℝ)<=log m->2<=d->∃ g l f:ℝ,0< g/\g<1/\0< l/\0< f/\(log m)^(-a)< l/\2/(f*((log m)^(-a))^((1:ℝ)/d))+1<=1/((log m)^(-a))^2/\t*(9*u)^d*((log m)^(-a))^(g*e)<=1/\m6bq d e g f ((log m)^(-a)):=by
 by_cases j:2<=d
 . obtain ⟨g,l,f,p,q,hd0,r,s⟩:=k d j e v
   refine eventually_atTop.mp ?_
   filter_upwards [m6b a i (2*l⁻¹),m6b (3*a/2) (by positivity) (2/f+1),m6b (a*g*e) (by positivity) (t*(9*u)^d)] with m h1 h2 h3 hL2 _
   set L:=log m;have b:0< L:=by linarith
   have n:1<=L:=by linarith
   have o:L^(-a)< l:=by rw[m6G b.le,inv_lt_comm₀ (by positivity) hd0];linarith[inv_pos.mpr hd0]
   have w:2/(f*(L^(-a))^((1:ℝ)/d))+1<=1/(L^(-a))^2:=by
    rw[show 1/(L^(-a))^2=L^(2*a) by rw[one_div,m6t b.le 2,m6G b.le,inv_inv];push_cast;ring,
     show 2/(f*(L^(-a))^((1:ℝ)/d))=(2/f)*L^(a/↑d) by rw[div_mul_eq_div_div,m6ae (2/f),←m6C b.le,←m6G b.le];congr 2;ring]
    have x:=m6i n (m6w i.le (by norm_num) (by exact_mod_cast j:(2:ℝ)<=d));have y:1<=L^(a/2):=one_le_rpow n (by positivity);exact(by nlinarith[m6R (by norm_num:(0:ℝ)<=2) r.le]:_<=(2/f+1)*L^(a/2)).trans ((m63 h2 (by linarith)).trans_eq (by rw[←m6L b];congr 1;ring))
   have z:t*(9*u)^d*(L^(-a))^(g*e)<=1:=by rw[←m6C b.le,show -a*(g*e)= -(a*g*e) by ring,m6G b.le,mul_inv_le_iff₀ (by positivity)];linarith
   exact ⟨g,l,f,p,q,hd0,r,o,w,z,s (L^(-a)) (by positivity) o⟩
 . exact ⟨0,fun _ _ _ h=>absurd h j⟩
lemma m6cf (hJ:m6q J) (g:m69 hC) {d K:ℕ} (hd:1<=d) (hK:100<=K) {e:ℝ} (a3:e<=1/6):∃ M1:ℕ,∀ m:ℕ,M1<=m->∀(W:ZB d) (b:m61 d),b⊆W.tF->NonAvg b->(m:ℝ)^(1-e/2)<=#b->(#b:ℝ)<=m->(W.vol:ℝ)<=(#b:ℝ)^(6:ℝ)->let h:=(log m)^(-(1/(8*(K:ℝ)+2)));m6a3 g (h^2) ((h^2)^(2*K)) W b->m6aw J g (h^2) ((h^2)^(2*K)) W b/\DCP h b/\72<=(#b:ℝ)*h/\b.Nonempty:=by
 set f:ℝ:=1/(8*(K:ℝ)+2);set k:=m6J J g d;have Y:(100:ℝ)<=K:=by exact_mod_cast hK
 have r:0< f:=div_pos (by norm_num) (by linarith);have a4:f<=1/4:=(m6I (by linarith)).mpr (by linarith);have n:=(g.ok d hd).1;have w:0< k:=m6ak hJ g hd;let F:ℝ:=↑d.factorial*(3/g.c d)^d;refine eventually_atTop.mp ?_
 filter_upwards [eventually_ge_atTop 16,m6b 1 one_pos 2,m6b f r 3,m6b f r (64*↑(J d)),
  m6b (1-f) (by linarith) (96*(g.c d)⁻¹),m6b (1/2) (by norm_num) (16*(g.c d)⁻¹/k),
  m6n (1-e/2) (by linarith) 16,m6n (1/4) (by norm_num) 4,
  m6f f (1/2) r (by norm_num) 72,m6f (2*f) (1/8) (by positivity) (by norm_num) 1,
  m6f (2*f) (1/2) (by positivity) (by norm_num) ↑(g.m0 d),
  m6f (2+2*f) (3/4) (by positivity) (by norm_num) (1+(g.c d)⁻¹),
  m6f (2+2*f+4*(K:ℝ)*f) (3/4) (by positivity) (by norm_num) (2+(27*↑(J d)/g.c d)^d),
  m6f (2+2*f) (1/4) (by positivity) (by norm_num) (1+2*(g.c d)⁻¹*sqrt ↑d),
  m6f (8*(K:ℝ)*f+1/2) (1/2) (by positivity) (by norm_num) (4*F^2/k)]
  with m hm16n hL2 hk3 hkJ hlgc hlgx hm16 hmq h72 hdr hm0b hb1 hb2 hb3 hM W b hAtBt hAtNA hAtlo hAthi hBt6 _
 intro hir;rw[rpow_one] at hL2;set L:=log m;set h:=L^(-f);set l:=h^2;set q:=l^(2*K);have C:(1:ℝ)<=m:=m6a (by omega);have i:(0:ℝ)< m:=by linarith
 have a:0< L:=by linarith
 have Z:1<=L:=by linarith
 have j:=m6V a (-f);have x:=pow_pos j 2;have G:=pow_pos x (2*K);have H:h<1/2:=by dsimp[h];rw[m6G a.le,inv_lt_comm₀ (by positivity) (by norm_num)];norm_num;linarith only[hk3]
 have o:l=L^(-(2*f)):=by simpa[l,h] using m6t a.le 2
 have s:q=L^(-(4*(K:ℝ)*f)):=by dsimp[q];rw[o,m6t a.le (2*K)];congr 2;push_cast;ring
 have M:16<=#b:=by exact_mod_cast hm16.trans hAtlo
 have y:(0:ℝ)<#b:=m6D (by omega);have t:=(m6i C (by linarith only[a3]:(3:ℝ)/4<=1-e/2)).trans hAtlo;have p:=(m6i C (by norm_num:(1:ℝ)/2<=3/4)).trans t;have a0:64*↑(J d)*l<=h:=by
  have:64*↑(J d)*h<=1:=by dsimp[h];rw[m6G a.le,mul_inv_le_iff₀ (by positivity)];linarith only[hkJ]
  dsimp[l];nlinarith only[this,j]
 have z:72<=(#b:ℝ)*h:=by dsimp[h];rw[m6G a.le,←m6ae,m6F (by positivity)];linarith only[h72,p]
 have N:(#b:ℝ)^(-(1:ℝ)/4)<=l:=by
  rw[o,m6G a.le,show -(1:ℝ)/4= -((1:ℝ)/4) by ring,m6G y.le,inv_le_inv₀ (by positivity) (by positivity)];exact(by rw[←m6C i.le,show ((1:ℝ)/2)*((1:ℝ)/4)=1/8 by norm_num];linarith only[hdr]:L^(2*f)<=(↑m^((1:ℝ)/2))^((1:ℝ)/4)).trans (m6ad (m6Z i.le _) p (by norm_num))
 have O:↑(g.m0 d)<=l*#b:=by rw[o,m6G a.le,inv_mul_eq_div,m6F (by positivity)];linarith only[hm0b,p]
 have A:0< log #b:=log_pos (Nat.one_lt_cast.mpr (by omega));have u:↑m^((3:ℝ)/4)/L^(2+2*f)<=l*#b/(log #b)^2:=by
  rw[m6L a,rpow_two,o,m6G a.le,←div_div,inv_mul_eq_div,div_right_comm];exact div_le_div₀ (by positivity) (m6b0 t (by positivity)) (sq_pos_of_pos A) (m6Q A.le (log_le_log y hAthi) 2)
 have P:1<=g.c d*(l*#b/(log #b)^2-1):=by
  have v:=((m6F (m6V a _)).mpr hb1).trans u;have:=m62 (by linarith only[v]:(g.c d)⁻¹<=l*#b/(log #b)^2-1) n.le;rwa[mul_inv_cancel₀ n.ne'] at this
 have Q:(27*↑(J d)/g.c d)^d/q< l*#b/(log #b)^2-1:=by
  rw[m6ae,s,←m6G a.le,neg_neg];have v:(2+(27*↑(J d)/g.c d)^d)*L^(4*(K:ℝ)*f)<=l*#b/(log #b)^2:=
   ((m6F (m6V a _)).mpr (by rw[m68,←m6L a,show 4*(K:ℝ)*f+(2+2*f)=2+2*f+4*(K:ℝ)*f by ring];exact hb2)).trans u
  have a1:1<=L^(4*(K:ℝ)*f):=one_le_rpow Z (by positivity);linarith only[v,a1]
 have a2:sqrt (↑d*#b)<=g.c d*(l*#b/(log #b)^2-1)/2:=by
  have v:(1+2*(g.c d)⁻¹*sqrt ↑d)*↑m^((1:ℝ)/2)<=l*#b/(log #b)^2:=
   ((m6F (m6V a _)).mpr (by rw[mul_right_comm];exact(m63 hb3 (m6Z i.le _)).trans_eq (by rw[←m6L i];norm_num))).trans u
  have X:sqrt (↑d*#b)<=sqrt ↑d*↑m^((1:ℝ)/2):=by rw[sqrt_mul (Nat.cast_nonneg d),←sqrt_eq_rpow];grw [hAthi]
  have h3:2*(g.c d)⁻¹*sqrt (↑d*#b)<=l*#b/(log #b)^2-1:=
   (m62 X (by positivity)).trans (by linarith only[v,one_le_rpow C (by norm_num:(0:ℝ)<=1/2),show (1+2*(g.c d)⁻¹*sqrt ↑d)*↑m^((1:ℝ)/2)=↑m^((1:ℝ)/2)+2*(g.c d)⁻¹*(sqrt ↑d*↑m^((1:ℝ)/2)) by ring])
  have:=m62 h3 n.le;rw[show g.c d*(2*(g.c d)⁻¹*sqrt (↑d*#b))=2*sqrt (↑d*#b) by field_simp[n.ne']] at this;linarith only[this]
 have R:L/2<=log (#b/4):=by
  have v:(m:ℝ)^((1:ℝ)/2)<=#b/4:=(m6F (by norm_num:(0:ℝ)<4)).mpr ((m62 hmq (m6Z i.le _)).trans (by rw[←m6L i,show (1:ℝ)/2+1/4=3/4 by norm_num];exact t));have:=log_le_log (m6V i _) v;rw[log_rpow i] at this;dsimp[L];linarith only[this]
 have D:48*(g.c d)⁻¹<=h*log (#b/4):=by
  have v:h*(L/2)=L^(1-f)/2:=by dsimp[h];rw[←mul_div_assoc,←rpow_add_one a.ne'];congr 2;ring
  linarith only[hlgc,v,m62 R j.le]
 have S:h*q=L^(-(1:ℝ)/2):=by rw[show h=L^(-f) from rfl,s,←m6L a];congr 1;dsimp[f];field_simp[show 8*(K:ℝ)+2≠0 by linarith only[Y]];ring
 have E:8*(g.c d)⁻¹/log (#b/4)<=k*h*q:=by
  have v:=(m6w (by positivity) (half_pos a) R).trans_eq (by rw[rpow_neg_one];field_simp[a.ne'];ring:8*(g.c d)⁻¹/(L/2)=16*(g.c d)⁻¹*L^(-(1:ℝ)));have X:=m63 ((m6I w).mp hlgx) (m6Z a.le (-(1:ℝ)));rw[mul_comm _ k,m68 k,←m6L a,show (1:ℝ)/2+ -(1:ℝ)= -(1:ℝ)/2 by norm_num] at X;rw[m68,S];linarith only[v,X]
 have T:4*(F/q)^2<=k*h*q*#b:=by
  have U:q^2=L^(-(8*(K:ℝ)*f)):=by rw[s,m6t a.le 2];congr 2;push_cast;ring
  have V:4*(F/q)^2=k*L^(-(1:ℝ)/2)*(4*F^2/k*L^(8*(K:ℝ)*f+1/2)):=by
   rw[show k*L^(-(1:ℝ)/2)*(4*F^2/k*L^(8*(K:ℝ)*f+1/2))=(k*(4*F^2/k))*(L^(-(1:ℝ)/2)*L^(8*(K:ℝ)*f+1/2)) by ring,
    mul_div_cancel₀ _ w.ne',←m6L a,show -(1:ℝ)/2+(8*(K:ℝ)*f+1/2)=8*(K:ℝ)*f by ring,div_pow F q 2,m6ae _ (q^2),U,m6G a.le,inv_inv];ring
  rw[V,show k*h*q*#b=k*L^(-(1:ℝ)/2)*#b by rw[m68 k,S]];grw [hM,p]
 have B:=m6c5 g hd (by omega) hBt6 N O P Q;exact ⟨B,m6c7 ⟨hJ,hd,x,G,hAtBt,hir,B⟩ j H.le (by nlinarith only[j,H]) a0 hAtNA M z a2 D E T,z,card_pos.mp (by omega)⟩
lemma m6cg (hJ:m6q J) (sp:m69 hC) (a6:M6L) (c5:M6O) {W d K:ℕ} (hd:1<=d) (c6:d<=W) {z0 gm th e:ℝ} (c7:0< z0) (E:gm=min ((1:ℝ)/12) (2/(↑W*(↑W+1)))) (c8:0< th) (c9:th<=gm/4) (F:0< e) (f6:e<=z0/100) (f7:e<=gm/8) (hK:100<=K) (f8:(30:ℝ)<=K*e):∃ Md:ℕ,16<=Md/\∀(z:ℝ) (B:ZB d) (A:m61 d),z0<=z->m60 d+z<1->(0:ZV d)∈B.tF->A⊆B.tF->NonAvg A->Md<=#A->(B.vol:ℝ)^(m60 d+z)<#A->m6br d K z0 th e z B A:=by
 have G:0< gm:=by rw[E];exact lt_min (by norm_num) (div_pos (by norm_num) (mul_pos (m6D (by omega)) (by positivity)))
 have X:e<=1/6:=by have:gm<=1/12:=E ▸ m6a0 _ _;linarith
 have d6:m60 d+e<1:=by
  by_cases h:d<=1
  . simp[m60,h];linarith
  . rw[m6p (by omega)];have:(2:ℝ)<=d:=by exact_mod_cast (by omega:2<=d)
    have:(d:ℝ)<=W:=m6j c6;have:1-((d:ℝ)-1)/((d:ℝ)+1)=2/((d:ℝ)+1):=by field_simp;ring
    have:gm<=2/((W:ℝ)*((W:ℝ)+1)):=E ▸ min_le_right _ _;linarith[m6w (by norm_num:(0:ℝ)<=2) (by linarith:(0:ℝ)< d+1) (by nlinarith:(d:ℝ)+1<=W*(W+1))]
 obtain ⟨Mr,_,e1⟩:=m6by hJ sp d hd e F X K (by omega) f8;let q:ℝ:=1/(8*(K:ℝ)+2);have f9:(100:ℝ)<=K:=by exact_mod_cast hK
 have H:0< q:=div_pos (by norm_num) (by linarith);let M:=m6a4 sp J d;have N:(1:ℝ)<=M:=m6x (m6be hJ sp d);obtain ⟨Me,e2⟩:=m6ce a6 d M ↑(J d) H F;obtain ⟨M1,e3⟩:=m6cf hJ sp hd hK X;obtain ⟨Md,e4⟩:=eventually_atTop.mp (show ∀ᶠ m:ℕ in atTop,_/\_/\_/\_/\_/\_/\_/\_ by
  filter_upwards [eventually_ge_atTop (max 16 (max Mr (max Me M1))),m6b 1 one_pos 2,m6b q H 3,
   m6f (4*(K:ℝ)*q) (1/3) (by positivity) (by norm_num) 1,
   m6f (8*((d+18:ℕ):ℝ)*q) (e/2) (by positivity) (half_pos F) 2,
   m6f (2+2*q) (e/2) (by positivity) (half_pos F) 2,
   m6n (z0/40) (by positivity) (M^(2:ℝ)),m6n (gm/2) (half_pos G) M] with m a b c d1 d2 d3 d4 d5
  exact ⟨a,b,c,d1,d2,d3,d4,d5⟩)
 refine ⟨max 16 Md,m6m _ _,fun z B A hz c4 f4 hAB f5 hm a5=>?_⟩
 set m:=#A;obtain ⟨Z,b0,e5,b1,e6,e7,e8,e9⟩:=e4 m ((m6Y 16 Md).trans hm);rw[rpow_one] at b0;set L:=log m;have a7:(1:ℝ)<=m:=m6a (by omega);have n:(0:ℝ)< m:=by linarith
 have f:0< L:=by linarith
 have d7:(B.vol:ℝ)<=↑m^(4:ℝ):=by simpa[show (1:ℝ)/(1/4)=4 by norm_num] using m6ao (m6af B).le (by norm_num:(0:ℝ)<1/4) ((m6i (m6S B) (by linarith[m6g d])).trans a5.le)
 set mu:=L^(-q);set O:=mu^2;set ga:=O^(2*K);have g:=m6V f (-q);have s:=pow_pos g 2;have P:=pow_pos s (2*K);have x:mu<1/2:=by dsimp[mu];rw[m6G f.le,inv_lt_comm₀ (by positivity) (by norm_num)];norm_num;linarith only[e5]
 have t:O=L^(-(2*q)):=by simpa[O,mu] using m6t f.le 2
 have a8:ga=L^(-(4*(K:ℝ)*q)):=by dsimp[ga];rw[t,m6t f.le (2*K)];congr 2;push_cast;ring
 have y:↑m^(-(1:ℝ)/3)<=ga:=by rw[a8,m6G f.le,show -(1:ℝ)/3= -((1:ℝ)/3) by ring,m6G n.le,inv_le_inv₀ (m6V n _) (m6V f _)];linarith only[b1]
 have C:↑m^(-e/2)< O^(4*(d+18)):=by
  rw[show O^(4*(d+18))=(L^(8*((d+18:ℕ):ℝ)*q))⁻¹ by rw[t,m6t f.le (4*(d+18)),show ((4*(d+18):ℕ):ℝ)*(2*q)=8*((d+18:ℕ):ℝ)*q by push_cast;ring,m6G f.le],show -e/2= -(e/2) by ring,m6G n.le,inv_lt_inv₀ (m6V n _) (m6V f _)];linarith only[e6,m6V f (8*((d+18:ℕ):ℝ)*q)]
 have D:2*L^2*↑m^(-e/2)<=O:=by
  rw[t,m6G f.le,show -e/2= -(e/2) by ring,m6G n.le,mul_inv_le_iff₀ (m6V n _),inv_mul_eq_div,m6F (m6V f _),show 2*L^2*L^(2*q)=2*L^(2+2*q) by rw[←rpow_two L,m68,←m6L f]];exact e7
 obtain ⟨dt,Bt,At,S,b2,T,j,o,hir,l,v,b3,b4,b5,b6⟩:=
  e1 B A O ga f4 hAB f5 ((m6m _ _).trans ((m6Y 16 _).trans Z)) d7 s (by dsimp[O];nlinarith only[g,x]) P le_rfl y C D
 rcases lt_trichotomy d dt with hlt | rfl | hgt
 . exact Or.inl ⟨dt,Bt,At,hlt,b2,T,j,o,l,m6cc hd hlt c7 hz c4 f6 a7 (m6S B) (m6S Bt) N a5 l (b4 hlt) e8⟩
 . obtain ⟨b7,b8,b9,a0⟩:=e3 m ((m6Y _ _).trans ((m6Y _ _).trans ((m6Y 16 _).trans Z))) Bt At j o l v b3 hir
   by_cases e0:d=1
   . rcases e0 with rfl;exact absurd b8 (c5 mu x At a0)
   . have a9:2<=d:=by omega
     obtain ⟨ta,d0,cr,U,_,_,f0,_,a1,a2,f1⟩:=e2 m ((m6m _ _).trans ((m6Y _ _).trans ((m6Y 16 _).trans Z))) b0 a9;obtain ⟨w,k,Bn,An,c0,V,f2,f3,c1,a3,a4,c2,c3⟩:=m6cb hJ a9 d6 U f0 g (by linarith only[x]) f1 j o b8 ((m6I g).mpr (by linarith only[b9])) (fun i=>a1.trans (m6c9 ⟨hJ,hd,s,P,j,hir,b7⟩ a0 i).le);have p:=m6c g c0;have Q:=V.trans_lt (rpow_lt_one g.le (by linarith only[x]) U);let rh:=(#At:ℝ)/m;have u:=div_pos (m6D (card_pos.mpr a0)) n;have R:=(div_le_one n).mpr v;have r:(Bn.vol:ℝ)<=w^(1-e)*rh^(K:ℝ)*B.vol:=by
      have d8:M*(9*↑(J d))^d*w^e<=1:=by grw [V,←m6C g.le,a2]
      have d9:w=w^e*w^(1-e):=by rw[←m6L p,show e+(1-e)=1 by ring,rpow_one]
      grw [c3,b6 rfl];rw[m6y,show (9*↑(J d))^d*w*(M*rh^K*B.vol)=(M*(9*↑(J d))^d*w^e)*(w^(1-e)*rh^K*B.vol) by linear_combination (M*(9*↑(J d))^d*rh^K*B.vol)*d9];exact(m63 d8 (m66 (m66 (m6Z p.le _) (m6A u.le _)) (m65))).trans_eq (one_mul _)
     have Y:Bn.vol< B.vol:=by
      have h1:w^(1-e)*rh^(K:ℝ)<1:=(m62 (rpow_le_one u.le R (Nat.cast_nonneg K)) (m6Z p.le _)).trans_lt (by rw[mul_one];exact rpow_lt_one p.le Q (by linarith only[X]));exact Nat.cast_lt.mp (r.trans_lt (by simpa only[one_mul] using mul_lt_mul_of_pos_right h1 (m6af B)))
     exact Or.inr (Or.inr ⟨w,rh,k,Bn,An,p,Q,u,R,f2,f3,c1,a3,a4,r,by rw[m68,div_mul_cancel₀ _ n.ne'];exact c2,Y⟩)
 . exact Or.inr (Or.inl ⟨dt,Bt,At,S,hgt,T,j,o,l,m6cd (m6c c7 hz) c4 (E ▸ m6bo S hgt c6) G c8 c9 f7 a7 (m6S B) (m6S Bt) N a5 l (b5 hgt) e9⟩)
lemma m6ch (hJ:m6q J) (sp:m69 hC) (a3:M6L) (b6:M6O) (V:ℕ) (hd0:1<=V) (b:ℝ) (C:0< b):∃ M:ℕ,∀(B:ZB V) (A:m61 V),(0:ZV V)∈B.tF->A⊆B.tF->NonAvg A->M<=#A->¬ ((B.vol:ℝ)^(m60 V+b)<#A):=by
 let p:=⌈100/b⌉₊;let q:=V+8*p;let s:=min ((1:ℝ)/12) (2/(↑q*(↑q+1)));have c7:0< s:=lt_min (by norm_num) (div_pos (by norm_num) (mul_pos (m6D (by omega)) (by positivity)));let i:=b/100;let W:=min i (s/4);let e:=min (b/100) (s/8);have D:0< i:=by positivity
 have F:0< W:=lt_min D (by positivity);have t:0< e:=lt_min (by positivity) (by positivity);have c8:e<=1/6:=by have:s<=1/12:=m6a0 _ _;linarith[min_le_right (b/100) (s/8)]
 let K:=max 100 (⌈30/e⌉₊+1);have b7:(30:ℝ)<=K*e:=(m6I t).mp ((Nat.le_ceil _).trans (by exact_mod_cast (Nat.le_succ _).trans (m6Y 100 _)));have g:∀ d∈Icc 1 q,∃ Md:ℕ,16<=Md/\∀(z:ℝ) (B:ZB d) (A:m61 d),b<=z->m60 d+z<1->(0:ZV d)∈B.tF->A⊆B.tF->NonAvg A->Md<=#A->(B.vol:ℝ)^(m60 d+z)<#A->m6br d K b W e z B A:=
  fun d hd=>m6cg hJ sp a3 b6 (mem_Icc.mp hd).1 (mem_Icc.mp hd).2 C rfl F (min_le_right _ _) t (m6a0 _ _) (min_le_right _ _) (m6m _ _) b7
 let Ms:=max 16 ((Icc 1 q).sup fun d=>if h:d∈Icc 1 q then (g d h).choose else 16);have a4:∀ d (hd:d∈Icc 1 q),(g d hd).choose<=Ms:=fun d hd=>by simpa only[dif_pos hd] using (le_sup (f:=fun d=>if h:d∈Icc 1 q then (g d h).choose else 16) hd).trans (m6Y 16 _)
 let Mr:ℕ->ℝ:=Nat.rec 2 fun _ b2=>max 2 (max ((Ms:ℝ)^(2/b)) (b2^(4/b)));have G:∀ r,(2:ℝ)<=Mr r:=fun r=>by cases r <;> [exact le_rfl;exact m6m 2 _]
 have a5:∀(r u d:ℕ) (z:ℝ) (B:ZB d) (A:m61 d),u<=p->1<=d->d<=V+8*(p-u)->
   b<=z->1-z<=r*W->1-z<=u*i->(0:ZV d)∈B.tF->A⊆B.tF->NonAvg A->Mr r<=#A->(B.vol:ℝ)^(m60 d+z)<#A->False:=by
  intro r;induction r with
  | zero=>intro u d z B A _ _ _ _ hr _ _ hAB _ _ l;linarith[(rpow_one (B.vol:ℝ)).symm.trans_le (m6i (m6S B) (show (1:ℝ)<=m60 d+z by simp at hr;linarith[m6g d])),m6ag hAB]
  | succ r ih=>
    intro u d z Q S b0 c1 c9 hz hr c2 b1 m Y T l;by_cases j:1<=m60 d+z
    . linarith[(rpow_one (Q.vol:ℝ)).symm.trans_le (m6i (m6S Q) j),m6ag m]
    push Not at j;have w:d∈Icc 1 q:=mem_Icc.mpr ⟨c1,by omega⟩;have H:(1:ℝ)<=#S:=by linarith[G (r+1)]
    have a6:(Ms:ℝ)<=(#S:ℝ)^(b/2):=by simpa[one_div_div] using m6ao (Nat.cast_nonneg Ms) (by positivity:0<2/b) ((m6m _ _).trans ((m6Y 2 _).trans T))
    have L:Mr r<=(#S:ℝ)^(b/4):=by simpa[one_div_div] using m6ao (by linarith[G r]) (by positivity:0<4/b) ((m6Y _ _).trans ((m6Y 2 _).trans T))
    have b8:∀ v (Z:ZB d) (U:m61 d) (E R:ℝ),Z.vol=v->0< E->E<=1->0< R->R<=1->
      (0:ZV d)∈Z.tF->U⊆Z.tF->NonAvg U->(Z.vol:ℝ)<=E^(1-e)*R^(K:ℝ)*Q.vol->E^(m60 d+e)*R*#S<=#U->False:=fun v=>Nat.strong_induction_on v fun v c3 Z U E R hv n a0 y a1 b3 o a2 b4 b5=>by
     obtain ⟨a9,P⟩:=m6bp (m6c C hz) j t (by linarith[m6a0 (b/100) (s/8)]) (m6m 100 _) n a0 y a1 H (m6S Q) (m6S Z) l b4 b5 (m6ag o);have a7:(g d w).choose<=#U:=by exact_mod_cast (by grw [a4 d w,a6,show b/2<=z/2 by linarith,P]:((g d w).choose:ℝ)<=#U)
     have a8:∀{x:ℝ},(#U:ℝ)^(1-e/2)<=x->Mr r<=x:=fun hx=>by grw [L,show b/4<=(z/2)*(1-e/2) by nlinarith,m6C (by linarith),P,hx];linarith
     rcases (g d w).choose_spec.2 z Z U hz j b3 o a2 a7 a9 with
      ⟨d',B',A',hdd',hd'8,h0B',hA'B',hA'NA,hA'lo,a⟩ | ⟨d',B',A',hd'1,hd'lt,h0B',hA'B',hA'NA,hA'lo,a⟩ |
      ⟨et,rh,k,B',A',het0,het1,hrh0,hrh1,hk1,hkd,h0B',hA'B',hA'NA,hB'b,hA'b,hB'lt⟩
     . have b9:1<=u:=by by_contra h;rcases (show u=0 by omega) with rfl;simp at c2;linarith[m6g d]
       exact ih (u-1) d' (z+i) B' A' (by omega) (by omega) (by omega) (by linarith) (by push_cast at hr;linarith[m6a0 i (s/4)]) (by rw[Nat.cast_sub b9,Nat.cast_one];linarith) h0B' hA'B' hA'NA (a8 hA'lo) a
     . exact ih u d' (z+W) B' A' b0 hd'1 (by omega) (by linarith) (by push_cast at hr;linarith) (by linarith) h0B' hA'B' hA'NA (a8 hA'lo) a
     . have N:(B'.vol:ℝ)<=(E*et)^(1-e)*(R*rh)^(K:ℝ)*Q.vol:=by grw [hB'b,b4];exact le_of_eq (by rw[m6r n.le het0.le,m6r y.le hrh0.le];ring)
       have O:(E*et)^(m60 d+e)*(R*rh)*#S<=#A':=by rw[m6r n.le het0.le,show E^(m60 d+e)*et^(m60 d+e)*(R*rh)*#S=et^(m60 d+e)*rh*(E^(m60 d+e)*R*#S) by ring];grw [b5,hA'b]
       by_cases c0:k=d
       . subst c0;exact c3 B'.vol (hv ▸ hB'lt) B' A' (E*et) (R*rh) rfl (mul_pos n het0) (mul_le_one₀ a0 het0.le het1.le) (mul_pos y hrh0) (mul_le_one₀ a1 hrh0.le hrh1) h0B' hA'B' hA'NA N O
       . obtain ⟨a,X⟩:=m6bp (m6c C hz) j t (by linarith[m6a0 (b/100) (s/8)]) (m6m 100 _) (mul_pos n het0) (mul_le_one₀ a0 het0.le het1.le) (mul_pos y hrh0) (mul_le_one₀ a1 hrh0.le hrh1) H (m6S Q) (m6S B') l N O (m6ag hA'B')
         exact ih u k (z+W) B' A' b0 hk1 (by omega) (by linarith) (by push_cast at hr;linarith) (by linarith) h0B' hA'B' hA'NA (by grw [L,show b/4<=z/2 by linarith,X]) ((m6i (m6S B') (by linarith[m6bo hk1 (by omega:k< d) (by omega:d<=q),min_le_right i (s/4)])).trans_lt a)
    exact b8 Q.vol Q S 1 1 rfl one_pos le_rfl one_pos le_rfl b1 m Y (by simp) (by simp)
 let Rm:=⌈1/W⌉₊;refine ⟨⌈Mr Rm⌉₊,fun B A c4 hAB c5 c6 l=>a5 Rm p V b B A le_rfl hd0 (by omega) le_rfl (by linarith[(m6I F).mp (Nat.le_ceil (1/W))]) (by have:=m63 (Nat.le_ceil (100/b)) D.le;rw[show 100/b*i=1 by dsimp[i];field_simp[C.ne']] at this;linarith) c4 hAB c5 ((Nat.le_ceil _).trans (m6j c6)) l⟩
theorem h2h {johnC : ℕ → ℕ}
 (hJohn : M6D johnC) (hCor : M6C) (hConv : M6L) (hOne : M6O) :
 OMA.R_Erdos186_erdos_186_R1.H2 :=by
 intro e J;let C:=min e (1/2);obtain ⟨M,F⟩:=m6ch hJohn (m6bx hCor) hConv hOne 1 le_rfl C (lt_min J (by norm_num));rw[Filter.eventually_atTop];refine ⟨M,fun j K D p P g _ _ _ y=>?_⟩;by_contra o;push Not at o;let k:ℕ->ZV 1:=fun n _=>(n:ℤ);have f:Function.Injective k:=fun a b h=>Int.ofNat.inj (congrFun h ⟨0,Nat.zero_lt_one⟩);let B:ZB 1:=⟨fun _=>0,fun _=>↑D,fun _=>Nat.cast_nonneg D⟩;let A:=P.image k;have s:(0:ZV 1)∈B.tF:=m67.mpr fun _=>⟨le_rfl,Nat.cast_nonneg D⟩;have hAB:A⊆B.tF:=fun v L=>by obtain ⟨n,G,rfl⟩:=m6E L;exact m67.mpr fun _=>⟨Nat.cast_nonneg n,by change (n:ℤ)<=↑D;exact_mod_cast (mem_Icc.mp (g G)).2⟩
 have t:NonAvg A:=fun N z O q d i=>by
  obtain ⟨a,H,rfl⟩:=m6E z;obtain ⟨T,w,rfl⟩:=subset_image_iff.mp (fun x r=>(mem_erase.mp (q r)).2);rw[m6T T f] at d i;rw[sum_image fun _ _ _ _ h=>f h] at i;have E:=congrFun i ⟨0,Nat.zero_lt_one⟩;simp only[Finset.sum_apply,Pi.smul_apply,smul_eq_mul,k] at E;exact o a H T (fun x r=>by have h:=mem_erase.mp (q (mem_image_of_mem k r));exact mem_erase.mpr ⟨fun e=>h.1 (congrArg k e),w r⟩) d (Nat.cast_injective (R:=ℤ) (by push_cast;exact E))
 have l:#A=2^j:=by rw[m6T P f,y]
 have u:B.vol=D+1:=by dsimp[ZB.vol,ZB.width,B];rw[Fin.prod_univ_one];omega
 apply F B A s hAB t (l ▸ K.trans (Nat.lt_two_pow_self (n:=j)).le)
 rw[show m60 1=1/4 by simp[m60],u,l];have m:=exp_lt_exp.mpr ((m63 (show 1/4+C<=1/4+e by linarith[m6a0 e (1/2)]) (log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le D)))).trans_lt p);rw[exp_log (by exact_mod_cast pow_pos (by norm_num:0<2) j)] at m;rw[rpow_def_of_pos (by exact_mod_cast Nat.succ_pos D),mul_comm];simpa only[Nat.cast_pow,Nat.cast_ofNat] using m
end
end E186
namespace E186
lemma g_fsum {G : Type*} [AddCommMonoid G] [DecidableEq G] :
 ∀ {n : ℕ} (A : Fin n → Finset G), m4fs A = fSm A
 | 0, _ => rfl
 | _ + 1, A => by simp [m4fs, fSm, g_fsum]
lemma g_dj : DJH jC :=
 ⟨johnConst_pos, fun _ Γ B h0 hc hs hb => djs Γ B h0 hc hs hb⟩
lemma g_qp : QPH := fun _ c hc => qpe c hc
lemma g_box : LEH := by
 intro d hd c hc0 hc1
 obtain ⟨γ, L₀, W₀, hγ, h⟩ := leb d hd hc0 hc1
 refine ⟨γ, L₀, W₀, hγ, fun Q hQ ℓ hℓ A h1 h2 h3 => ?_⟩
 simpa [g_fsum] using h Q hQ ℓ hℓ A h1 h2 h3
lemma g_nr : LNH := by
 intro d hd c hc0 hc1
 obtain ⟨κ, γ, L₀, W₀, hκ, hγ, h⟩ := lnr d hd hc0 hc1
 refine ⟨κ, γ, L₀, W₀, hκ, hγ, fun Q A hQ hA h0 hc => ?_⟩
 obtain ⟨P, hC, hS, h1, h2, h3, h4, h5, h6⟩ := h Q A hQ hA h0 hc
 exact ⟨P, hC, hS, h1, h2, h3, h4, h5, fun ℓ hℓ => h6 ℓ hℓ (mul_nonneg hγ.le (Nat.cast_nonneg ℓ)) (GAP.sIC hS)⟩
lemma g_bilu : LBH := fun s d hs δ hδ => lbi g_dj g_qp s d hs δ hδ
lemma g_m6_conv : M6L := by
 intro d hd ε hε
 obtain ⟨τ, δ₀, c_rad, hτ, hτ1, hδ₀, hcr, h⟩ := lc1 d hd ε hε
 refine ⟨τ, δ₀, c_rad, hτ, hτ1, hδ₀, hcr, fun δ hδ hδlt A hA hdc hcard => ?_⟩
 obtain ⟨η, x₀, K₀, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h δ hδ hδlt A hA hdc hcard
 refine ⟨η, x₀, K₀, h1, h2, h3, h4, h5, h6, h7, h8, ?_⟩
 convert h9 using 3
lemma g_m6_one : M6O := fun _ hδ _ hA => nd1 hδ hA
end E186
theorem OMA.solution : OMA.R_Erdos186_erdos_186_R1.H2 :=
 E186.h2h E186.g_dj (E186.cst E186.g_box E186.g_nr E186.g_bilu) E186.g_m6_conv E186.g_m6_one
