import OMAReductions.R_Kourovka_1_40_kourovka_1_40_R2

/-!
# Kourovka 1.40 for locally nilpotent intersections and a three-generator reduction

Credit: @witeg4. The homomorphism lemma for Engel commutators comes from the parent reduction.
The two factors act by commuting conjugations on each lower central layer of their intersection.
An elementwise binomial argument proves termination on each layer. Any remaining counterexample
can be tested on three generators, with the initial test element belonging to both factors.
An Engel generator lift across a cyclic quotient preserves finite generation of the kernel.
Applied twice, this makes both factors and their intersection finitely generated in the test group.
-/

open Kourovka.«1.40» Subgroup OMA.R_Kourovka_1_40_kourovka_1_40_R2
open scoped commutatorElement

namespace OMA.MixedEngel

variable {G : Type*} [Group G]

private theorem iterate_add (x y : G) (m n : ℕ) :
    engelCommutator x y (m+n) = engelCommutator (engelCommutator x y m) y n := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg (fun z => ⁅z,y⁆) ih

/-- Normality puts the first commutator in K, where the Engel condition applies. -/
private theorem ambient_engel (K : Subgroup G) [K.Normal] (hK : IsEngelGroup K)
    {k : G} (hk : k ∈ K) : IsEngelElement k := by
  intro x
  have hx : ⁅x,k⁆ ∈ K := commutator_le_right (⊤ : Subgroup G) K
    (commutator_mem_commutator (mem_top x) hk)
  obtain ⟨n,hn⟩ := hK ⟨k,hk⟩ ⟨⁅x,k⁆,hx⟩
  refine ⟨1+n, ?_⟩
  rw [iterate_add]
  exact (engel_map K.subtype ⟨⁅x,k⁆,hx⟩ ⟨k,hk⟩ n).symm.trans
    (by rw [hn, map_one])

private theorem iterate_mem (D : Subgroup G) [D.Normal] {z : G} (hz : z ∈ D) (k : G) :
    ∀ n, engelCommutator z k n ∈ D
  | 0 => hz
  | n+1 => commutator_le_left D (⊤ : Subgroup G)
      (commutator_mem_commutator (iterate_mem D hz k n) (mem_top k))

/-- Modulo N, h centralizes D, so on D iterating with k*h agrees with iterating with k. -/
private theorem descend (D N H : Subgroup G) [D.Normal] [N.Normal] (hDN : ⁅D,H⁆ ≤ N)
    {z k h : G} (hz : z ∈ D) (hh : h ∈ H) (hk : IsEngelElement k) :
    ∃ n, engelCommutator z (k*h) n ∈ N := by
  let q := QuotientGroup.mk' N
  have eqmod (n : ℕ) :
      q (engelCommutator z (k*h) n) = q (engelCommutator z k n) := by
    induction n with
    | zero => rfl
    | succ n ih =>
      let w := engelCommutator z k n
      have comm : q ⁅w,h⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr
        (hDN (commutator_mem_commutator (iterate_mem D hz k n) hh))
      simp only [engelCommutator, map_commutatorElement, ih, map_mul]
      change ⁅q w, q k*q h⁆ = ⁅q w,q k⁆
      rw [map_commutatorElement] at comm
      rw [commutatorElement_mul_right_eq_mul_conj, comm]
      simp [mul_assoc]
  obtain ⟨n,hn⟩ := hk z
  refine ⟨n,(QuotientGroup.eq_one_iff _).mp ?_⟩
  exact (eqmod n).trans (by rw [hn,map_one])

end OMA.MixedEngel

namespace OMA.EngelAction

variable {M : Type*} [AddCommGroup M]

/-- Elementwise binomial bound. Neither operator needs a global nilpotence bound. -/
theorem add_kills (A B : Module.End ℤ M) (hc : Commute A B) (x : M) (m n : ℕ)
    (ha : (A^m) x = 0) (hb : (B^n) x = 0) : ((A+B)^(m+n)) x = 0 := by
  rw [hc.add_pow', LinearMap.sum_apply]
  apply Finset.sum_eq_zero
  rintro ⟨i,j⟩ hij
  have hs : i+j=m+n := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  have hz : ((A^i)*(B^j)) x=0 := by
    by_cases h : n ≤ j
    · rw [Module.End.mul_apply, Module.End.pow_map_zero_of_le h hb, map_zero]
    · rw [((hc.pow_left i).pow_right j).eq, Module.End.mul_apply,
        Module.End.pow_map_zero_of_le (by omega : m ≤ i) ha, map_zero]
  simp only [LinearMap.smul_apply, hz, smul_zero]

theorem product_unipotent (S T : Module.End ℤ M) (hc : Commute S T) (x : M) (m n : ℕ)
    (hs : ((1-S)^m) x = 0) (ht : ((1-T)^n) x = 0) :
    ((1-S*T)^(m+n)) x = 0 := by
  have hst : Commute S (1-T) := (Commute.one_right _).sub_right hc
  have h₁ : Commute (1-S) S := (Commute.one_left _).sub_left (Commute.refl _)
  have h₂ : Commute (1-S) (1-T) := (Commute.one_left _).sub_left hst
  have hkill : ((S*(1-T))^n) x = 0 := by
    rw [hst.mul_pow, Module.End.mul_apply, ht, map_zero]
  have e : 1-S*T = (1-S)+S*(1-T) := by noncomm_ring
  rw [e]
  exact add_kills _ _ (h₁.mul_right h₂) _ _ _ hs hkill

end OMA.EngelAction

namespace OMA.EngelCentralLayer

open Kourovka.«1.40» Subgroup
open scoped commutatorElement IsMulCommutative

variable {G : Type*} [Group G] (A : Subgroup G) [A.Normal] [IsMulCommutative A]

/-- On an abelian normal layer centralized by [h,k], ambient Engel elements h and k
have an Engel product on every element of the layer. -/
theorem kills_on_layer {h k : G} (hh : IsEngelElement h) (hk : IsEngelElement k)
    (hc : ⁅h,k⁆ ∈ centralizer (A : Set G)) (x : A) :
    ∃ n, engelCommutator (x:G) (h*k) n = 1 := by
  let conjOp (y : G) : Module.End ℤ (Additive A) :=
    ((MulAut.conjNormal (H := A) y).toMonoidHom.toAdditive).toIntLinearMap
  have act_mul (h k : G) : conjOp (h*k) = conjOp h * conjOp k := by
    apply LinearMap.ext
    intro x
    change MulAut.conjNormal (H := A) (h*k) x.toMul = _
    rw [map_mul]
    rfl

  have iteration (y : G) (x : Additive A) (n : ℕ) :
      (((((1-conjOp y)^n) x).toMul : A) : G) = engelCommutator (x.toMul:G) y n := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Module.End.mul_apply]
      let z := ((1-conjOp y)^n) x
      change (z.toMul : G) / (y * (z.toMul : G) * y⁻¹) = _
      change (z.toMul : G) = _ at ih
      rw [ih]
      simp [engelCommutator, commutatorElement_def, div_eq_mul_inv, mul_assoc]

  have act_commute {h k : G} (hc : ⁅h,k⁆ ∈ centralizer (A : Set G)) :
      Commute (conjOp h) (conjOp k) := by
    have tr : MulAut.conjNormal (H := A) ⁅h,k⁆ = 1 := by
      apply MulEquiv.ext
      intro a
      apply Subtype.ext
      change ⁅h,k⁆ * (a:G) * ⁅h,k⁆⁻¹ = a
      rw [← mem_centralizer_iff.mp hc a a.property]
      simp only [mul_assoc,mul_inv_cancel,mul_one]
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at tr
    change conjOp h * conjOp k = conjOp k * conjOp h
    apply LinearMap.ext
    intro x
    exact congrArg (fun f : MulAut A => f x.toMul) tr

  let z : Additive A := Additive.ofMul x
  have lift (y : G) (hy : IsEngelElement y) : ∃ n : ℕ, ((1-conjOp y)^n) z = 0 := by
    obtain ⟨n,hn⟩ := hy x
    refine ⟨n, ?_⟩
    apply Additive.toMul.injective
    apply Subtype.ext
    exact (iteration y z n).trans hn
  obtain ⟨m,hm⟩ := lift h hh
  obtain ⟨n,hn⟩ := lift k hk
  have kill := OMA.EngelAction.product_unipotent _ _ (act_commute hc) z m n hm hn
  rw [← act_mul] at kill
  refine ⟨m+n, (iteration (h*k) z (m+n)).symm.trans ?_⟩
  rw [kill]
  rfl
end OMA.EngelCentralLayer

namespace OMA.EngelIntersection
open Kourovka.«1.40» Subgroup
open scoped commutatorElement IsMulCommutative

variable {G : Type*} [Group G]

private theorem quotient_engel {y : G} (hy : IsEngelElement y) (N : Subgroup G) [N.Normal] :
    IsEngelElement (QuotientGroup.mk' N y) := by
  intro x
  obtain ⟨z,rfl⟩ := QuotientGroup.mk'_surjective N x
  obtain ⟨n,hn⟩ := hy z
  exact ⟨n, (engel_map (QuotientGroup.mk' N) z y n).symm.trans (by rw [hn,map_one])⟩

private theorem layer_drop (I : Subgroup G) [I.Normal] {h k z : G} (i : ℕ)
    (hz : z ∈ I.lowerCentralSeries i) (hc : ⁅h,k⁆ ∈ I)
    (hh : IsEngelElement h) (hk : IsEngelElement k) :
    ∃ n, engelCommutator z (h*k) n ∈ I.lowerCentralSeries (i+1) := by
  let D := I.lowerCentralSeries i
  let N := I.lowerCentralSeries (i+1)
  let q := QuotientGroup.mk' N
  let A := D.map q
  have cent {v w : G} (hv : v ∈ D) (hw : w ∈ I) : q v * q w = q w * q v := by
    apply commutatorElement_eq_one_iff_mul_comm.mp
    rw [← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr (commutator_mem_commutator hv hw)
  let : A.Normal := Subgroup.Normal.map (inferInstance : D.Normal) q (QuotientGroup.mk'_surjective N)
  let : IsMulCommutative A := by
    apply IsMulCommutative.of_setLike_mul_comm
    rintro _ ⟨v,hv,rfl⟩ _ ⟨w,hw,rfl⟩
    exact cent hv (I.lowerCentralSeries_le_self i hw)
  have central : ⁅q h,q k⁆ ∈ centralizer (A : Set (G ⧸ N)) := by
    apply mem_centralizer_iff.mpr
    rintro _ ⟨v,hv,rfl⟩
    rw [← map_commutatorElement]
    exact cent hv hc
  obtain ⟨n,hn⟩ := OMA.EngelCentralLayer.kills_on_layer A
    (quotient_engel hh N) (quotient_engel hk N) central ⟨q z,⟨z,hz,rfl⟩⟩
  refine ⟨n,(QuotientGroup.eq_one_iff _).mp ?_⟩
  change q (engelCommutator z (h*k) n) = 1
  rw [engel_map, map_mul]
  exact hn

theorem enter_intersection (H K : Subgroup G) [H.Normal] [K.Normal]
    (eH : IsEngelGroup H) (eK : IsEngelGroup K) (hsup : H ⊔ K = ⊤)
    (y x : G) : ∃ n, engelCommutator x y n ∈ H ⊓ K := by
  obtain ⟨h,hh,k,hk,hy⟩ := mem_sup_of_normal_right.mp
    (show y ∈ H ⊔ K by rw [hsup]; exact mem_top _)
  obtain ⟨k',hk',h',hh',hy'⟩ := mem_sup_of_normal_right.mp
    (show y ∈ K ⊔ H by rw [sup_comm,hsup]; exact mem_top _)
  have he := OMA.MixedEngel.ambient_engel H eH hh
  have ke := OMA.MixedEngel.ambient_engel K eK hk
  obtain ⟨m,hm⟩ := OMA.MixedEngel.descend ⊤ K K (commutator_le_right _ _) (mem_top x) hk he
  obtain ⟨l,hl⟩ := OMA.MixedEngel.descend ⊤ H H (commutator_le_right _ _) (mem_top x) hh'
    (OMA.MixedEngel.ambient_engel K eK hk')
  rw [hy'] at hl
  rw [hy] at hm
  refine ⟨m+l, ?_, ?_⟩
  · rw [Nat.add_comm, OMA.MixedEngel.iterate_add]
    exact OMA.MixedEngel.iterate_mem H hl y m
  · rw [OMA.MixedEngel.iterate_add]
    exact OMA.MixedEngel.iterate_mem K hm y l

theorem nilpotent_intersection (H K : Subgroup G) [H.Normal] [K.Normal]
    (eH : IsEngelGroup H) (eK : IsEngelGroup K) (hsup : H ⊔ K = ⊤)
    (nilI : Group.IsNilpotent (H ⊓ K : Subgroup G)) : IsEngelGroup G := by
  intro y x
  obtain ⟨h,hh,k,hk,hy⟩ := mem_sup_of_normal_right.mp
    (show y ∈ H ⊔ K by rw [hsup]; exact mem_top _)
  have he := OMA.MixedEngel.ambient_engel H eH hh
  have ke := OMA.MixedEngel.ambient_engel K eK hk
  let I := H ⊓ K
  have hc : ⁅h,k⁆ ∈ I := ⟨commutator_le_left H K (commutator_mem_commutator hh hk),
    commutator_le_right H K (commutator_mem_commutator hh hk)⟩
  have reach (i : ℕ) : ∃ n, engelCommutator x y n ∈ I.lowerCentralSeries i := by
    induction i with
    | zero => exact enter_intersection H K eH eK hsup y x
    | succ i ih =>
      obtain ⟨u,hu⟩ := ih
      obtain ⟨v,hv⟩ := layer_drop I i hu hc he ke
      exact ⟨u+v,by rw [OMA.MixedEngel.iterate_add,← hy]; rw [← hy] at hv; exact hv⟩
  obtain ⟨i,hi⟩ := (isNilpotent_iff_lowerCentralSeries I).mp nilI
  obtain ⟨n,hn⟩ := reach i
  exact ⟨n,by simpa [hi] using hn⟩

end OMA.EngelIntersection

namespace OMA.EngelOrbit
open Subgroup Kourovka.«1.40»
open scoped commutatorElement
variable {G : Type*} [Group G]

private theorem cyclic_fg (x : G) : (zpowers x).FG := by
  classical
  exact ⟨{x},by simp [zpowers_eq_closure]⟩

/-- The conjugates of one element by all integral powers of an Engel element lie
in a finitely generated invariant subgroup of the chosen normal subgroup. -/
theorem one_orbit (N : Subgroup G) [N.Normal] (t : G) {x : G} (hx : x ∈ N) (n : ℕ)
    (hn : engelCommutator x t n = 1) :
    ∃ B : Subgroup G, B.FG ∧ B ≤ N ∧ x ∈ B ∧ B.map (MulAut.conj t) = B := by
  induction n generalizing x with
  | zero =>
    change x=1 at hn
    exact ⟨⊥,Subgroup.FG.bot,bot_le,by simp [hn],by simp⟩
  | succ n ih =>
    let w := ⁅x,t⁆
    have hw : w ∈ N := commutator_le_left N (⊤ : Subgroup G)
      (commutator_mem_commutator hx (mem_top t))
    have hn' : engelCommutator w t n = 1 := by
      change engelCommutator (engelCommutator x t 1) t n = 1
      rw [← OMA.MixedEngel.iterate_add x t 1 n, Nat.add_comm]; exact hn
    obtain ⟨B,hB,hBN,hwB,hinv⟩ := ih hw hn'
    let c := (MulAut.conj t).toMonoidHom
    change B.map c = B at hinv
    let D := zpowers x ⊔ B
    have hxD : x ∈ D := mem_sup_left (mem_zpowers x)
    have hwD : w ∈ D := mem_sup_right hwB
    have iden : w * c x = x := by
      change ⁅x,t⁆ * (t*x*t⁻¹) = x
      simp [commutatorElement_def,mul_assoc]
    have hcD : c x ∈ D := by
      rw [(eq_inv_mul_iff_mul_eq).mpr iden]
      exact D.mul_mem (D.inv_mem hwD) hxD
    have hBm : B ≤ D.map c := by
      calc B = B.map c := hinv.symm
           _ ≤ D.map c := map_mono (show B ≤ D from le_sup_right)
    refine ⟨D,(cyclic_fg x).sup hB,sup_le (zpowers_le.mpr hx) hBN,hxD,le_antisymm ?_ ?_⟩
    · change (zpowers x ⊔ B).map c ≤ D
      rw [Subgroup.map_sup,MonoidHom.map_zpowers,hinv]
      exact sup_le (zpowers_le.mpr hcD) le_sup_right
    · apply sup_le _ hBm
      apply zpowers_le.mpr
      rw [← iden]
      exact (D.map c).mul_mem (hBm hwB) ⟨x,hxD,rfl⟩


/-- Finitely generated groups with cyclic quotient and an Engel generator lift have
finitely generated kernel, even when that quotient is infinite. -/
theorem cyclic_kernel_fg [Group.FG G] (N : Subgroup G) [N.Normal] (t : G)
    (ht : IsEngelElement t) (hgen : N ⊔ zpowers t = ⊤) : N.FG := by
  classical
  obtain ⟨s,hs⟩ := (Group.FG.out : (⊤ : Subgroup G).FG)
  have rep (j : s) : ∃ w ∈ N, ∃ p ∈ zpowers t, w*p = j.val :=
    mem_sup_of_normal_left.mp (by rw [hgen]; exact mem_top _)
  choose w hw p hp he using rep
  have orbit (j : s) : ∃ B : Subgroup G, B.FG ∧ B ≤ N ∧ w j ∈ B ∧ B.map (MulAut.conj t) = B := by
    obtain ⟨n,hn⟩ := ht (w j)
    exact one_orbit N t (hw j) n hn
  choose C fg sub mem stab using orbit
  let B := ⨆ i, C i
  have hBN : B ≤ N := iSup_le sub
  have hBfg : B.FG := Subgroup.FG.iSup _ fg
  have full : B ⊔ zpowers t = ⊤ := by
    apply top_unique
    rw [← hs, closure_le]
    intro x hx
    let j : s := ⟨x,hx⟩
    change j.val ∈ B ⊔ zpowers t
    rw [← he j]
    exact mul_mem_sup (le_iSup C j (mem j)) (hp j)
  have normaliz : t ∈ normalizer (B : Set G) := by
    apply mem_normalizer_iff_map_conj_eq.mpr
    change (⨆ i,C i).map _ = ⨆ i,C i
    rw [Subgroup.map_iSup]
    simp_rw [stab]
  let : B.Normal := normalizer_eq_top_iff.mp (by
    apply top_unique
    rw [← full]
    exact sup_le B.le_normalizer (zpowers_le.mpr normaliz))
  let V := N ⊓ zpowers t
  obtain ⟨d,hd⟩ := (le_zpowers_iff t V).mp inf_le_right
  have split : N = B ⊔ V := by
    apply le_antisymm _ (sup_le hBN inf_le_left)
    intro x hx
    obtain ⟨u,hu,v,hv,rfl⟩ := mem_sup_of_normal_left.mp
      (show x ∈ B ⊔ zpowers t by rw [full]; exact mem_top _)
    exact mul_mem_sup hu ⟨(N.mul_mem_cancel_left (hBN hu)).mp hx,hv⟩
  rw [split,hd]
  exact hBfg.sup (cyclic_fg _)

end OMA.EngelOrbit
namespace OMA.EngelOrbit
open Kourovka.«1.40» Subgroup
variable {G : Type*} [Group G]

/-- In the three-generator test, both factors and their intersection are finitely generated. -/
theorem three_fg (H K : Subgroup G) [H.Normal] [K.Normal] (eH : IsEngelGroup H)
    (eK : IsEngelGroup K) {h k z : G} (hh : h ∈ H) (hk : k ∈ K) (hz : z ∈ H ⊓ K)
    (hg : closure ({h,k,z} : Set G) = ⊤) : H.FG ∧ K.FG ∧ (H ⊓ K : Subgroup G).FG := by
  classical
  let : Group.FG G := Group.fg_iff.mpr ⟨_,hg,by simp⟩
  have fullH : H ⊔ zpowers k = ⊤ := by
    apply top_unique
    rw [← hg,closure_le]
    intro x hx
    rcases (show x=h ∨ x=k ∨ x=z from hx) with rfl|rfl|rfl
    · exact mem_sup_left hh
    · exact mem_sup_right (mem_zpowers _)
    · exact mem_sup_left hz.1
  have fullK : K ⊔ zpowers h = ⊤ := by
    apply top_unique
    rw [← hg,closure_le]
    intro x hx
    rcases (show x=h ∨ x=k ∨ x=z from hx) with rfl|rfl|rfl
    · exact mem_sup_right (mem_zpowers _)
    · exact mem_sup_left hk
    · exact mem_sup_left hz.2
  have fgH := cyclic_kernel_fg H k (OMA.MixedEngel.ambient_engel K eK hk) fullH
  have fgK := cyclic_kernel_fg K h (OMA.MixedEngel.ambient_engel H eH hh) fullK
  refine ⟨fgH,fgK,?_⟩
  let : Group.FG H := (Group.fg_iff_subgroup_fg H).mpr fgH
  let u : H := ⟨h,hh⟩
  let J := K.comap H.subtype
  have full : J ⊔ zpowers u = ⊤ := by
    apply top_unique
    intro a _
    obtain ⟨v,hv,p,hp,he⟩ := mem_sup_of_normal_left.mp
      (show (a:G) ∈ K ⊔ zpowers h by rw [fullK]; exact mem_top _)
    obtain ⟨j,rfl⟩ := mem_zpowers_iff.mp hp
    have hvH : v ∈ H := by
      apply (H.mul_mem_cancel_right (H.zpow_mem hh j)).mp
      rw [he]
      exact a.property
    have eqH : (⟨v,hvH⟩ : H)*u^j=a := Subtype.ext he
    rw [← eqH]
    exact mul_mem_sup (show (⟨v,hvH⟩ : H) ∈ J from hv) (zpow_mem_zpowers _ _)
  have fj := cyclic_kernel_fg J u (eH u) full
  obtain ⟨S,hs,hfin⟩ := (Subgroup.fg_iff J).mp fj
  apply (Subgroup.fg_iff _).mpr
  refine ⟨H.subtype '' S,?_,hfin.image _⟩
  rw [← MonoidHom.map_closure,hs]
  ext v
  constructor
  · rintro ⟨u,hu,rfl⟩
    exact ⟨u.property,hu⟩
  · intro hv
    exact ⟨⟨v,hv.1⟩,hv.2,rfl⟩

end OMA.EngelOrbit
namespace OMA.R_Kourovka_1_40_kourovka_1_40_R2_H1_R1

open Kourovka.«1.40» Subgroup
open scoped commutatorElement

/-- The remaining three-generator test when the intersection is torsion. -/
def H1 : Prop :=
  ∀ (G : Type) [Group G] (H K : Subgroup G) [H.Normal] [K.Normal],
    IsEngelGroup H → IsEngelGroup K → ∀ h ∈ H, ∀ k ∈ K, ∀ z ∈ H ⊓ K,
    closure ({h,k,z} : Set G) = ⊤ → H.FG → K.FG → (H ⊓ K : Subgroup G).FG →
    ¬ Group.IsNilpotent (H ⊓ K : Subgroup G) →
    (∀ v : (H ⊓ K : Subgroup G), IsOfFinOrder v) → ∃ n, engelCommutator z (h*k) n = 1

/-- The remaining three-generator test when the intersection has an element of infinite order. -/
def H2 : Prop :=
  ∀ (G : Type) [Group G] (H K : Subgroup G) [H.Normal] [K.Normal],
    IsEngelGroup H → IsEngelGroup K → ∀ h ∈ H, ∀ k ∈ K, ∀ z ∈ H ⊓ K,
    closure ({h,k,z} : Set G) = ⊤ → H.FG → K.FG → (H ⊓ K : Subgroup G).FG →
    ¬ Group.IsNilpotent (H ⊓ K : Subgroup G) →
    (∃ v : (H ⊓ K : Subgroup G), ¬ IsOfFinOrder v) → ∃ n, engelCommutator z (h*k) n = 1

theorem restrict_engel {G : Type*} [Group G] (H T : Subgroup G) (eH : IsEngelGroup H) :
    IsEngelGroup (H.comap T.subtype) := by
  let f : H.comap T.subtype →* H :=
    (T.subtype.comp (H.comap T.subtype).subtype).codRestrict H (fun x => x.property)
  intro y x
  obtain ⟨n,hn⟩ := eH (f y) (f x)
  have he : f (engelCommutator x y n) = f 1 := by
    rw [engel_map,hn,map_one]
  exact ⟨n,Subtype.ext (Subtype.ext (congrArg (fun v : H => (v:G)) he))⟩

private theorem triple {G : Type} [Group G]
    (H K : Subgroup G) [H.Normal] [K.Normal] (eH : IsEngelGroup H) (eK : IsEngelGroup K)
    (cases : (H1 ∧ H2) ∨ ∀ J : Subgroup (H ⊓ K : Subgroup G), J.FG → Group.IsNilpotent J)
    {h k z : G} (hh : h ∈ H) (hk : k ∈ K) (hz : z ∈ H ⊓ K) :
    ∃ n, engelCommutator z (h*k) n = 1 := by
  let s : Set G := {h,k,z}
  let T := closure s
  let u : T := ⟨h,subset_closure (by simp [s])⟩
  let v : T := ⟨k,subset_closure (by simp [s])⟩
  let w : T := ⟨z,subset_closure (by simp [s])⟩
  let A := H.comap T.subtype
  let B := K.comap T.subtype
  have gen : closure ({u,v,w} : Set T) = ⊤ := by
    convert! closure_preimage_eq_top s using 2
    ext x
    simp only [s,Set.mem_preimage,Set.mem_insert_iff,Set.mem_singleton_iff,Subtype.ext_iff]
    rfl
  have hu : u ∈ A := hh
  have hv : v ∈ B := hk
  have hw : w ∈ A ⊓ B := hz
  have full : A ⊔ B = ⊤ := by
    apply top_unique
    rw [← gen, closure_le]
    intro t ht
    rcases (show t = u ∨ t = v ∨ t = w from ht) with rfl|rfl|rfl
    · exact mem_sup_left hu
    · exact mem_sup_right hv
    · exact mem_sup_left hw.1
  have ea := restrict_engel H T eH
  have eb := restrict_engel K T eK
  have inside : ∃ n, engelCommutator w (u*v) n = 1 := by
    by_cases nil : Group.IsNilpotent (A ⊓ B : Subgroup T)
    · exact OMA.EngelIntersection.nilpotent_intersection A B ea eb full nil (u*v) w
    obtain ⟨fa,fb,fi⟩ := OMA.EngelOrbit.three_fg A B ea eb hu hv hw gen
    rcases cases with ⟨a,b⟩ | locally
    · by_cases tor : ∀ q : (A ⊓ B : Subgroup T), IsOfFinOrder q
      · exact a T A B ea eb u hu v hv w hw gen fa fb fi nil tor
      · push Not at tor
        exact b T A B ea eb u hu v hv w hw gen fa fb fi nil tor
    · let I := (A ⊓ B : Subgroup T)
      let emb : I →* (H ⊓ K : Subgroup G) :=
        (T.subtype.comp I.subtype).codRestrict _ (fun v => v.property)
      have inj : Function.Injective emb := by
        intro x y he
        exact Subtype.ext (Subtype.ext (congrArg (fun v : (H ⊓ K : Subgroup G) => (v:G)) he))
      let : Group.FG I := (Group.fg_iff_subgroup_fg I).mpr fi
      let : Group.IsNilpotent emb.range :=
        locally _ ((Group.fg_iff_subgroup_fg _).mp (Group.fg_range emb))
      exact (nil (Group.nilpotent_of_mulEquiv (MonoidHom.ofInjective inj).symm)).elim
  obtain ⟨n,hn⟩ := inside
  exact ⟨n, (engel_map T.subtype w (u*v) n).symm.trans (by rw [hn,map_one])⟩


/-- Local nilpotence of the intersection suffices for arbitrary normal Engel factors. -/
theorem locally_nilpotent_intersection {G : Type} [Group G] (H K : Subgroup G) [H.Normal] [K.Normal]
    (eH : IsEngelGroup H) (eK : IsEngelGroup K) (hs : H ⊔ K = ⊤)
    (locally : ∀ J : Subgroup (H ⊓ K : Subgroup G), J.FG → Group.IsNilpotent J) : IsEngelGroup G := by
  intro y x
  obtain ⟨m,hm⟩ := OMA.EngelIntersection.enter_intersection H K eH eK hs y x
  obtain ⟨h,hh,k,hk,rfl⟩ := mem_sup_of_normal_right.mp
    (show y ∈ H ⊔ K by rw [hs]; exact mem_top _)
  obtain ⟨n,hn⟩ := triple H K eH eK (.inr locally) hh hk hm
  exact ⟨m+n,by rw [OMA.MixedEngel.iterate_add]; exact hn⟩

theorem main : H1 → H2 → OMA.R_Kourovka_1_40_kourovka_1_40_R2.H1 := by
  intro a b G _ H K hH hK eH eK hs _ _ _ y x
  obtain ⟨m,hm⟩ := OMA.EngelIntersection.enter_intersection H K eH eK hs y x
  obtain ⟨h,hh,k,hk,rfl⟩ := mem_sup_of_normal_right.mp
    (show y ∈ H ⊔ K by rw [hs]; exact mem_top _)
  obtain ⟨n,hn⟩ := triple H K eH eK (.inl ⟨a,b⟩) hh hk hm
  exact ⟨m+n,by rw [OMA.MixedEngel.iterate_add]; exact hn⟩

end OMA.R_Kourovka_1_40_kourovka_1_40_R2_H1_R1
